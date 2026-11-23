import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_984_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def HasMonoSize (n : ℕ) (f : BFn n) (s : ℕ) : Prop :=
  ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x

theorem nat_beq_true {a b : ℕ} : Nat.beq a b = true ↔ a = b := by
  exact ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem nat_beq_false {a b : ℕ} : Nat.beq a b = false ↔ a ≠ b := by
  constructor
  · intro h heq; subst heq; rw [Nat.beq_refl] at h; exact Bool.noConfusion h
  · intro hne
    cases hb : Nat.beq a b with
    | false => rfl
    | true => exact absurd (nat_beq_true.1 hb) hne

/-! ## Section 1: Monotone circuit simplification, relabeling, and gate elimination -/

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

def MOk (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

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
  by_cases hj : j < n
  · simp [inputSupps, hj]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hm : L.length ∈ W
  · set W' := W.erase L.length
    have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W' ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      obtain ⟨j, hjW, hij⟩ := Finset.mem_biUnion.1 hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact Finset.mem_biUnion.2 ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact Finset.mem_biUnion.2 ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 := Finset.card_le_card hsub
    have hc2 := h (W' ∪ g.inputs.toFinset)
    have hc3 : (W' ∪ g.inputs.toFinset).card ≤ W'.card + g.inputs.toFinset.card :=
      Finset.card_union_le _ _
    have hc4 : g.inputs.toFinset.card ≤ 2 := le_trans (List.toFinset_card_le _) hg
    have hc5 : W'.card + 1 = W.card := Finset.card_erase_add_one hm
    omega
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ (W.biUnion fun j => L.getD j ∅) := by
      intro i hi
      obtain ⟨j, hjW, hij⟩ := Finset.mem_biUnion.1 hi
      have hjl : j ≠ L.length := fun e => hm (e ▸ hjW)
      rw [getD_snoc_ne _ _ _ _ hjl] at hij
      exact Finset.mem_biUnion.2 ⟨j, hjW, hij⟩
    have := le_trans (Finset.card_le_card hsub) (h W)
    omega

theorem cnt_suppsFrom {n : ℕ} (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, g.inputs.length ≤ 2) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; simpa [suppsFrom] using h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g])
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self) h)
    simpa [suppsFrom, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

theorem dep_lower_set (n : ℕ) (f : BFn n) (D : Finset (Fin n))
    (hD : ∀ i ∈ D, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasMonoSize n f s) : D.card ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hcnt := cnt_suppsFrom C.gates 0 (inputSupps n) (fun g hg => (ok g hg).2) cnt_inputs
  have hcard : ((suppsFrom C.gates (inputSupps n)).getD C.output ∅).card ≤ C.gates.length + 1 := by
    have := hcnt {C.output}
    simpa using this
  have hsub : D ⊆ (suppsFrom C.gates (inputSupps n)).getD C.output ∅ := by
    intro i hi
    by_contra hni
    obtain ⟨x, hx⟩ := hD i hi
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro j hj
        have hji : j ≠ i := fun e => hni (e ▸ hj)
        simp [Function.update_of_ne hji])
    rw [← hev, ← hev]
    exact hag
  have := le_trans (Finset.card_le_card hsub) hcard
  have hsz' : C.gates.length ≤ s := hsz
  omega

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

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

def simplifyM (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | _ => (none, Sum.inl false)

def CleanMG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k]

def CleanML (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanMG (n + p) g

theorem simplifyM_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplifyM op m ins).1, MOk g := by
  intro g hg
  cases op <;> simp only [simplifyM] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; exact ⟨Or.inl rfl, by simp⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; exact ⟨Or.inr rfl, by simp⟩
  · simp at hg
  · simp at hg
  · simp at hg

theorem simplifyM_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplifyM op m ins).1, CleanMG m g := by
  intro g hg
  cases op <;> simp only [simplifyM] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact ⟨Or.inl rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact ⟨Or.inr rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · simp at hg
  · simp at hg
  · simp at hg

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hs => lt_of_lt_of_le hs h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

theorem simplifyM_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    let r := simplifyM op w.length ins
    statValid (w.length + r.1.toList.length) r.2 ∧
      statVal (wiresFrom r.1.toList w) r.2 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · exact ⟨trivial, rfl⟩
    · cases a with
      | inl c => exact ⟨trivial, by simp [simplifyM, simpAnd, statVal, GateOp.eval]⟩
      | inr j =>
        exact ⟨by simpa [simplifyM, simpAnd, statValid] using hv (Sum.inr j) (by simp),
          by simp [simplifyM, simpAnd, statVal, wiresFrom, GateOp.eval]⟩
    · cases a with
      | inl c =>
        cases b with
        | inl d => exact ⟨trivial, by simp [simplifyM, simpAnd, statVal, GateOp.eval]⟩
        | inr j =>
          cases c
          · exact ⟨trivial, by simp [simplifyM, simpAnd, statVal, GateOp.eval]⟩
          · exact ⟨by simpa [simplifyM, simpAnd, statValid] using hv (Sum.inr j) (by simp),
              by simp [simplifyM, simpAnd, statVal, wiresFrom, GateOp.eval]⟩
      | inr j =>
        cases b with
        | inl d =>
          cases d
          · exact ⟨trivial, by simp [simplifyM, simpAnd, statVal, GateOp.eval]⟩
          · exact ⟨by simpa [simplifyM, simpAnd, statValid] using hv (Sum.inr j) (by simp),
              by simp [simplifyM, simpAnd, statVal, wiresFrom, GateOp.eval]⟩
        | inr k =>
          refine ⟨by simp [simplifyM, simpAnd, statValid], ?_⟩
          simp [simplifyM, simpAnd, statVal, wiresFrom, GateOp.eval]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · exact ⟨trivial, rfl⟩
    · cases a with
      | inl c => exact ⟨trivial, by simp [simplifyM, simpOr, statVal, GateOp.eval]⟩
      | inr j =>
        exact ⟨by simpa [simplifyM, simpOr, statValid] using hv (Sum.inr j) (by simp),
          by simp [simplifyM, simpOr, statVal, wiresFrom, GateOp.eval]⟩
    · cases a with
      | inl c =>
        cases b with
        | inl d => exact ⟨trivial, by simp [simplifyM, simpOr, statVal, GateOp.eval]⟩
        | inr j =>
          cases c
          · exact ⟨by simpa [simplifyM, simpOr, statValid] using hv (Sum.inr j) (by simp),
              by simp [simplifyM, simpOr, statVal, wiresFrom, GateOp.eval]⟩
          · exact ⟨trivial, by simp [simplifyM, simpOr, statVal, GateOp.eval]⟩
      | inr j =>
        cases b with
        | inl d =>
          cases d
          · exact ⟨by simpa [simplifyM, simpOr, statValid] using hv (Sum.inr j) (by simp),
              by simp [simplifyM, simpOr, statVal, wiresFrom, GateOp.eval]⟩
          · exact ⟨trivial, by simp [simplifyM, simpOr, statVal, GateOp.eval]⟩
        | inr k =>
          refine ⟨by simp [simplifyM, simpOr, statValid], ?_⟩
          simp [simplifyM, simpOr, statVal, wiresFrom, GateOp.eval]
    · simp at hlen

theorem simplifyM_none (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : ins.length ≤ 2)
    (hc : ∃ c, Sum.inl c ∈ ins) : (simplifyM op m ins).1 = none := by
  rcases hop with rfl | rfl <;> rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp at hc
  · cases a <;> rfl
  · cases a <;> cases b <;> first | rfl | simp at hc
  · simp at hlen
  · simp at hc
  · cases a <;> rfl
  · cases a <;> cases b <;> first | rfl | simp at hc
  · simp at hlen

theorem simplifyM_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : ins.length ≤ 2)
    (b : Bool) (h1 : op = GateOp.and → b = false) (h2 : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplifyM op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl
  · have hb : b = false := h1 rfl; subst hb
    rcases ins with _ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩
    · simp at hc
    · cases x <;> simp [simplifyM, simpAnd] at hc ⊢
    · cases x <;> cases y <;> simp [simplifyM, simpAnd] at hc ⊢ <;>
        rcases hc with rfl | rfl <;> simp
    · simp at hlen
  · have hb : b = true := h2 rfl; subst hb
    rcases ins with _ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩
    · simp at hc
    · cases x <;> simp [simplifyM, simpOr] at hc ⊢
    · cases x <;> cases y <;> simp [simplifyM, simpOr] at hc ⊢ <;>
        rcases hc with rfl | rfl <;> simp
    · simp at hlen

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  let ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false)
  let r := simplifyM g.op (n + acc.2.length) ins
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_nil (n : ℕ) (acc : List Stat × List Gate) : elim n [] acc = acc := rfl

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (gs gs' : List Gate) (acc : List Stat × List Gate) :
    elim n (gs ++ gs') acc = elim n gs' (elim n gs acc) := by
  simp [elim, List.foldl_append]

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      cases (simplifyM g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 <;>
        simp
    simp only [elim_cons, List.length_cons] at h1 ⊢
    omega

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem elim_getD (n i : ℕ) (acc : List Stat × List Gate) (gs : List Gate)
    (hi : i < acc.1.length) :
    (elim n gs acc).1.getD i (Sum.inl false) = acc.1.getD i (Sum.inl false) := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [elim_cons, ih _ (by simp [elimStep]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, MOk g) → ∀ g ∈ (elim n gs acc).2, MOk g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h2
    · exact h g' h1
    · exact simplifyM_ok _ _ _ g' (Option.mem_toList.1 h2)

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧
    ∀ i : ℕ, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
      statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate),
    (∀ g ∈ gs, MOk g) → Inv n y w acc → Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    obtain ⟨hl, hi⟩ := h
    have hgok := hok g List.mem_cons_self
    apply ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hs := simplifyM_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplifyM g.op (n + acc.2.length) ins with hr
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
    (∀ g ∈ gs, MOk g) → (∀ i, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false))) →
    CleanML n acc.2 → CleanML n (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ _ hc; exact hc
  | cons g gs ih =>
    intro acc hok hv hc
    apply ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    · intro i
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplifyM_sound g.op hgok.1 (List.replicate (n + acc.2.length) false) ins
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
        set r := simplifyM g.op (n + acc.2.length)
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
          exact simplifyM_clean g.op (n + acc.2.length) _ (by
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
  rw [List.ofFn_succ']; simp

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

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, MOk g) → k < acc.1.length →
    (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) →
    (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ ⟨g, hg, _⟩; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hread
    have hgok := hok g List.mem_cons_self
    have hgsok : ∀ g' ∈ gs, MOk g' := fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')
    by_cases hg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnone : (simplifyM g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none :=
        simplifyM_none _ _ _ hgok.1 (by simpa using hgok.2) ⟨c, List.mem_map.2 ⟨k, hg, hc⟩⟩
      have h1 := elim_len n gs (elimStep n acc g)
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplifyM g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      simp only [elim_cons, List.length_cons] at h1 ⊢
      omega
    · have hread' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hkg'⟩ := hread
        rcases List.mem_cons.1 hg' with rfl | hmem
        · exact absurd hkg' hg
        · exact ⟨g', hmem, hkg'⟩
      have hstep := ih (elimStep n acc g) hgsok (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          show (acc.1 ++ [_]).getD k (Sum.inl false) = Sum.inl c
          rw [List.getD_append _ _ _ _ hk]; exact hc) hread'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        cases (simplifyM g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 <;>
          simp
      simp only [elim_cons, List.length_cons] at hstep ⊢
      omega

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : MOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplifyM g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none :=
    simplifyM_none _ _ _ hg.1 (by simpa using hg.2) ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplifyM g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : MOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplifyM g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
  rw [e]
  exact simplifyM_const _ _ _ hg.1 (by simpa using hg.2) (fixBit g)
    (fun h => by simp [fixBit, h]) (fun h => by simp [fixBit, h])
    (List.mem_map.2 ⟨k, hk, hc⟩)

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

theorem gate_elim_one (n : ℕ) (f : BFn (n + 1)) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasMonoSize (n + 1) f s) :
    ∃ s', s' + 1 ≤ s ∧ HasMonoSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hmok : ∀ g ∈ C.gates, MOk g := ok
  set acc := elim n C.gates (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) C.gates _ _ hmok (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2]
    exact hev (Fin.snoc y b)
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hread : ∃ g ∈ C.gates, n ∈ g.inputs := by
      by_contra hnr
      push Not at hnr
      have hon : C.output ≠ n := by
        intro e
        have := elim_getD n n (initStats n b, []) C.gates (by simp [initStats])
        rw [initStats_last] at this
        rw [hacc, e, this] at hst
        cases hst
      obtain ⟨x, hx⟩ := hdep
      apply hx
      have hno := supp_noread n C.gates (inputSupps (n + 1)) hnr (inputSupps_noread n) C.output hon
      have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x
        C.gates _ _ _ (agree_inputs _ _)).2.2 C.output (by
          intro k hk
          have hkn : k ≠ Fin.last n := fun e => hno (e ▸ hk)
          simp [Function.update_of_ne hkn])
      rw [← hev, ← hev]
      exact hag
    have hlt := elim_len_lt n n C.gates (initStats n b, []) hmok (by simp [initStats])
      ⟨b, initStats_last n b⟩ hread
    have hlt' : acc.2.length + 1 ≤ C.gates.length := by
      simpa [hacc] using hlt
    refine ⟨acc.2.length, by omega,
      ⟨acc.2, j⟩, elim_ok n C.gates _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

theorem two_saved (n : ℕ) (gs : List Gate) (hmok : ∀ g ∈ gs, MOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Sum.inl false) ≠ Sum.inl c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n (initStats n false, []) gs (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : MOk g := hmok g hg
  have hpren : ∀ g' ∈ pre, MOk g' := fun g' h => hmok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, MOk g' :=
    fun g' h => hmok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Sum.inl false) = Sum.inl b := by
    intro b
    rw [elim_getD n n (initStats n b, []) pre (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]; simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b; simp [elimStep, hAl b]
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
    have := hF false; have := hB2 false
    rw [hsplit, hlen]; omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false; have := hB2 false
    rw [hsplit, hlen]; omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g); have := hB2 (fixBit g)
    rw [hsplit, hlen]; omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n (n + 1 + pre.length) _ post (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]; simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length :=
        ⟨fun e => hj (Or.inl e), fun e => hj (Or.inr e)⟩
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

theorem gate_elim_two (n : ℕ) (f : BFn (n + 1)) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasMonoSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasMonoSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n C.gates (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) C.gates _ _ ok (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      statVal (wiresFrom (elim n C.gates (initStats n b, [])).2 (List.ofFn y))
        ((elim n C.gates (initStats n b, [])).1.getD C.output (Sum.inl false)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2]
    exact hev (Fin.snoc y b)
  have hout : ∀ b c,
      (elim n C.gates (initStats n b, [])).1.getD C.output (Sum.inl false) ≠ Sum.inl c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom C.gates (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n C.gates ok C.output hsupp hout
  cases hst : (elim n C.gates (initStats n b, [])).1.getD C.output (Sum.inl false) with
  | inl c => exact absurd hst (hout b c)
  | inr j =>
    refine ⟨b, (elim n C.gates (initStats n b, [])).2.length, by omega,
      ⟨(elim n C.gates (initStats n b, [])).2, j⟩, elim_ok n C.gates _ (by simp), le_refl _, ?_⟩
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
      unfold wmap; split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by unfold wmap; split <;> omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by unfold wmap; split <;> omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih => intro W W' h; exact ih _ _ (rel_step n m π W W' g h)

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

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : BFn n) (s : ℕ)
    (hc : HasMonoSize n h s) : HasMonoSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    exact (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output

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
      intro e; apply hj
      have := congrArg (Equiv.swap p (Fin.last n)) e
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    obtain ⟨t, ht⟩ := Fin.exists_castSucc_eq.2 hl
    rw [← ht, Fin.snoc_castSucc, ht, Equiv.swap_apply_self, Function.update_of_ne hj]

theorem one_gate_at (n : ℕ) (f : BFn (n + 1)) (p : Fin (n + 1)) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasMonoSize (n + 1) f s) :
    ∃ s' : ℕ, s' + 1 ≤ s ∧ HasMonoSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasMonoSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
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
    simpa [hσ, Equiv.swap_apply_right] using hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap n p x b, snoc_swap n p y b]
    exact hxy
  obtain ⟨s', hs', h'⟩ := gate_elim_one n (fun x => f (x ∘ σ)) b s hdep' hnc' hg
  refine ⟨s', hs', ?_⟩
  have hrel := relabel_size (fun j : Fin n => σ j.castSucc)
    (fun y : Fin n → Bool => f (Fin.snoc y b ∘ σ)) s' h'
  have heq : (fun x : Fin (n + 1) → Bool => f (Fin.snoc (x ∘ fun j : Fin n => σ j.castSucc) b ∘ σ))
      = fun x => f (Function.update x p b) := by
    funext x
    show f (Fin.snoc (fun j : Fin n => x (σ j.castSucc)) b ∘ σ) = _
    rw [snoc_swap n p x b]
  rwa [heq] at hrel

theorem gate_elim_at (n : ℕ) (f : BFn (n + 1)) (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasMonoSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasMonoSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasMonoSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
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
    simpa [hσ, Equiv.swap_apply_right] using hx0
  have hnc' : ∀ b : Bool, ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    intro b
    obtain ⟨x, y, hxy⟩ := hnc b
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap n p x b, snoc_swap n p y b]
    exact hxy
  obtain ⟨b, s', hs', h'⟩ := gate_elim_two n (fun x => f (x ∘ σ)) s hdep' hnc' hg
  refine ⟨b, s', hs', ?_⟩
  have hrel := relabel_size (fun j : Fin n => σ j.castSucc)
    (fun y : Fin n → Bool => f (Fin.snoc y b ∘ σ)) s' h'
  have heq : (fun x : Fin (n + 1) → Bool => f (Fin.snoc (x ∘ fun j : Fin n => σ j.castSucc) b ∘ σ))
      = fun x => f (Function.update x p b) := by
    funext x
    show f (Fin.snoc (fun j : Fin n => x (σ j.castSucc)) b ∘ σ) = _
    rw [snoc_swap n p x b]
  rwa [heq] at hrel

/-! ## Section 1b: Graph-function (`gfn`) monotone reductions -/

def gfn {n : ℕ} (A : List (Fin n)) (E : List (Fin n × Fin n)) (x : Fin n → Bool) : Bool :=
  A.any (fun a => x a) || E.any (fun e => x e.1 && x e.2)

def dedup {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: t => if a ∈ t then dedup t else a :: dedup t

theorem mem_dedup {α : Type} [DecidableEq α] (l : List α) (x : α) : x ∈ dedup l ↔ x ∈ l := by
  induction l with
  | nil => simp [dedup]
  | cons a t ih =>
    simp only [dedup]
    split_ifs with h
    · rw [ih]; constructor
      · intro hx; exact List.mem_cons_of_mem _ hx
      · intro hx; rcases List.mem_cons.1 hx with rfl | hx <;> assumption
    · simp [ih]

def fix0A {n : ℕ} (A : List (Fin n)) (p : Fin n) : List (Fin n) := A.filter (· != p)
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
    (h : ∀ s, HasMonoSize n f s → val2 ≤ s) : ∀ s, HasMonoSize n f s → val1 ≤ s :=
  fun s hs => le_trans hle (h s hs)

theorem gfn_empty {n : ℕ} (A : List (Fin n)) (hnd : A.Nodup) :
    ∀ s : ℕ, HasMonoSize n (gfn A []) s → A.length - 1 ≤ s := by
  intro s h
  have hd := dep_lower_set n (gfn A []) A.toFinset (by
    intro i hi
    have hiA : i ∈ A := List.mem_toFinset.1 hi
    refine ⟨fun _ => false, ?_⟩
    have h0 : gfn A [] (fun _ => false) = false := by simp [gfn]
    have h1 : gfn A [] (Function.update (fun _ => false) i true) = true := by
      simp only [gfn, List.any_nil, Bool.or_false, List.any_eq_true]
      exact ⟨i, hiA, by simp⟩
    simp [h0, h1]) s h
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
    simp [h0, h1]
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
    · exact ⟨e, he, by simp [h1, h2]⟩
    · exact ⟨e, he, by have hqp : q ≠ p := h3 ▸ h1; simp [h2, h3, hqp]⟩

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
    (ih : ∀ s, HasMonoSize (n + 1) (gfn A' E') s → k ≤ s) :
    ∀ s, HasMonoSize (n + 1) (gfn A E) s → k + 1 ≤ s := by
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
    (ih : ∀ s, HasMonoSize (n + 1) (gfn A' E') s → k ≤ s) :
    ∀ s, HasMonoSize (n + 1) (gfn A E) s → k + 1 ≤ s := by
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
    (ih0 : ∀ s, HasMonoSize (n + 1) (gfn A0 E0) s → k ≤ s)
    (ih1 : ∀ s, HasMonoSize (n + 1) (gfn A1 E1) s → k ≤ s) :
    ∀ s, HasMonoSize (n + 1) (gfn A E) s → k + 2 ≤ s := by
  intro s h
  have hres0 : (fun x => gfn A E (Function.update x p false)) = gfn A0 E0 := by
    rw [hA0, hE0]; exact gfn_restrict_false A E p
  have hres1 : (fun x => gfn A E (Function.update x p true)) = gfn A1 E1 := by
    rw [hA1, hE1]; exact gfn_restrict_true A E p hpA hloop
  have hnc : ∀ b, ∃ x y, gfn A E (Function.update x p b) ≠ gfn A E (Function.update y p b) := by
    intro b
    cases b
    · obtain ⟨x, y, hxy⟩ := gfn_nc A0 E0 hnc0
      exact ⟨x, y, by simpa [congrFun hres0] using hxy⟩
    · obtain ⟨x, y, hxy⟩ := gfn_nc A1 E1 hnc1
      exact ⟨x, y, by simpa [congrFun hres1] using hxy⟩
  obtain ⟨b, s', hs', h'⟩ := gate_elim_at n (gfn A E) p s (gfn_dep A E p hdep) hnc h
  cases b
  · rw [hres0] at h'; have := ih0 s' h'; omega
  · rw [hres1] at h'; have := ih1 s' h'; omega

theorem gfn_base {n k val : ℕ} (E : List (Fin n × Fin n)) (Eb : List (Fin k × Fin k))
    (π : Fin n → Fin k) (f : BFn k)
    (hiso : isoCheck E Eb π = true)
    (hf : ∀ x : Fin k → Bool, gfn [] Eb x = f x)
    (hbase : ∀ s, HasMonoSize k f s → val ≤ s) :
    ∀ s, HasMonoSize n (gfn [] E) s → val ≤ s := by
  intro s hs
  have hcomp : ∀ x : Fin k → Bool, gfn [] E (x ∘ π) = f x := by
    intro x
    rw [← hf x]
    apply Bool.eq_iff_iff.2
    simp only [isoCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
      Bool.or_eq_true, beq_iff_eq] at hiso
    simp only [gfn, List.any_nil, Bool.false_or, List.any_eq_true, Bool.and_eq_true,
      Function.comp_apply]
    constructor
    · rintro ⟨e, he, h1, h2⟩
      obtain ⟨e', he', ⟨ha, hb⟩ | ⟨ha, hb⟩⟩ := hiso.1 e he
      · exact ⟨e', he', ha ▸ h1, hb ▸ h2⟩
      · exact ⟨e', he', hb ▸ h2, ha ▸ h1⟩
    · rintro ⟨e', he', h1, h2⟩
      obtain ⟨e, he, ⟨ha, hb⟩ | ⟨ha, hb⟩⟩ := hiso.2 e' he'
      · exact ⟨e, he, ha.symm ▸ h1, hb.symm ▸ h2⟩
      · exact ⟨e, he, ha.symm ▸ h2, hb.symm ▸ h1⟩
  have hrel := relabel_size π (gfn [] E) s hs
  have heq : (fun x => gfn [] E (x ∘ π)) = f := funext hcomp
  rw [heq] at hrel
  exact hbase s hrel

theorem finish_conj {n val : ℕ} (E : List (Fin n × Fin n)) (f : BFn n)
    (heq : ∀ x, gfn [] E x = f x)
    (h : ∀ s, HasMonoSize n (gfn [] E) s → val ≤ s) :
    ∀ C : Circuit, Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) → val ≤ C.size := by
  intro C hM hev
  exact h C.size ⟨C, hM, le_refl _, fun x => (hev x).trans (heq x).symm⟩

/-! ## Section 2: MBuild, DBuild, DLive, bit-parallel v6, and verified barrier engine -/

def pt (n : ℕ) (v : ℕ) : Fin n → Bool := fun i => v.testBit i

def encL {n : ℕ} (a : BFn n) : List ℕ → ℕ
  | [] => 0
  | v :: t => Nat.bit (a (pt n v)) (encL a t)

theorem encL_testBit {n : ℕ} (a : BFn n) : ∀ (l : List ℕ) (j : ℕ),
    (encL a l).testBit j = (l.map fun v => a (pt n v)).getD j false
  | [], _ => by simp [encL]
  | _ :: _, 0 => by simp [encL]
  | _ :: t, j + 1 => by simp [encL, Nat.testBit_bit_succ, encL_testBit a t j]

theorem encL_lt {n : ℕ} (a : BFn n) : ∀ l : List ℕ, encL a l < 2 ^ l.length
  | [] => by simp [encL]
  | v :: t => by
    have ih := encL_lt a t
    simp only [encL, List.length_cons, pow_succ']
    cases a (pt n v) <;> simp [Nat.bit] <;> omega

theorem encL_and {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (fun x => a x && b x) l = encL a l &&& encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]; rfl

theorem encL_or {n : ℕ} (a b : BFn n) (l : List ℕ) :
    encL (fun x => a x || b x) l = encL a l ||| encL b l := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, encL_testBit, encL_testBit, encL_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]; rfl

def goalME (M E : ℕ) : ℕ := ((1 <<< E) - 1) <<< M

theorem testBit_goalME (M E j : ℕ) :
    (goalME M E).testBit j = decide (M ≤ j ∧ j < M + E) := by
  unfold goalME
  rw [Nat.testBit_shiftLeft]
  have h1 : (1 <<< E) - 1 = 2 ^ E - 1 := by simp [Nat.shiftLeft_eq]
  rw [h1, Nat.testBit_two_pow_sub_one]
  by_cases hM : M ≤ j
  · simp only [decide_eq_true hM, Bool.true_and]
    by_cases hE : j - M < E <;> simp [hM, hE] <;> omega
  · simp only [decide_eq_false hM, Bool.false_and]
    have : ¬ (M ≤ j ∧ j < M + E) := fun h => hM h.1
    simp [this]

theorem goalME_lt (M E : ℕ) : goalME M E < 2 ^ (M + E) := by
  unfold goalME
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, one_mul, pow_add, Nat.mul_comm (2 ^ M)]
  have h1 : 1 ≤ 2 ^ E := Nat.one_le_two_pow
  have h2 : 0 < 2 ^ M := Nat.two_pow_pos M
  exact Nat.mul_lt_mul_of_pos_right (by omega) h2

theorem lt_two_pow_of_testBit_false : ∀ (x k : ℕ), (∀ j, k ≤ j → x.testBit j = false) → x < 2 ^ k := by
  intro x
  induction x using Nat.strong_induction_on with
  | ind x ih =>
    intro k h
    by_cases hx0 : x = 0
    · subst hx0; exact Nat.two_pow_pos k
    · cases k with
      | zero =>
        exfalso
        have h0 : x = 0 := Nat.eq_of_testBit_eq fun j => by simpa using h j (Nat.zero_le j)
        exact hx0 h0
      | succ k =>
        have hdiv : x / 2 < 2 ^ k := ih (x / 2) (Nat.div_lt_self (by omega) (by omega)) k (fun j hj => by
          have := h (j + 1) (by omega)
          rwa [Nat.testBit_succ] at this)
        rw [pow_succ']
        omega

def goodME (M w : ℕ) : Bool :=
  let mMask := (1 <<< M) - 1
  !(Nat.beq (w >>> M) 0) && !(Nat.beq (w &&& mMask) mMask)

def domME (M x y : ℕ) : Bool :=
  let mMask := (1 <<< M) - 1
  let gx := x ^^^ mMask
  Nat.beq (gx &&& (y ^^^ mMask)) gx

theorem testBit_mMask (M j : ℕ) : (((1 <<< M) - 1).testBit j) = decide (j < M) := by
  have : (1 <<< M) - 1 = 2 ^ M - 1 := by simp [Nat.shiftLeft_eq]
  rw [this, Nat.testBit_two_pow_sub_one]

theorem domME_iff (M x y : ℕ) :
    domME M x y = true ↔
      (∀ i < M, y.testBit i ≤ x.testBit i) ∧ (∀ j, M ≤ j → x.testBit j ≤ y.testBit j) := by
  unfold domME
  rw [nat_beq_true, Nat.eq_iff_testBit_eq]
  constructor
  · intro h
    constructor
    · intro i hi
      have h' := h i
      rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_xor, testBit_mMask, decide_eq_true hi] at h'
      cases hx : x.testBit i <;> cases hy : y.testBit i <;> simp_all
    · intro j hj
      have h' := h j
      have hlt : ¬ j < M := by omega
      rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_xor, testBit_mMask, decide_eq_false hlt] at h'
      cases hx : x.testBit j <;> cases hy : y.testBit j <;> simp_all
  · rintro ⟨h1, h2⟩ j
    rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_xor, testBit_mMask]
    by_cases hj : j < M
    · simp only [decide_eq_true hj]
      have := h1 j hj
      cases hx : x.testBit j <;> cases hy : y.testBit j <;> simp_all <;> exact absurd this (by decide)
    · simp only [decide_eq_false hj]
      have := h2 j (by omega)
      cases hx : x.testBit j <;> cases hy : y.testBit j <;> simp_all <;> exact absurd this (by decide)

theorem domME_refl (M x : ℕ) : domME M x x = true :=
  (domME_iff M x x).2 ⟨fun _ _ => le_refl _, fun _ _ => le_refl _⟩

theorem domME_trans {M x y z : ℕ} (h1 : domME M x y = true) (h2 : domME M y z = true) :
    domME M x z = true := by
  rw [domME_iff] at h1 h2 ⊢
  exact ⟨fun i hi => le_trans (h2.1 i hi) (h1.1 i hi), fun j hj => le_trans (h1.2 j hj) (h2.2 j hj)⟩

theorem domME_and {M x1 y1 x2 y2 : ℕ} (h1 : domME M x1 y1 = true) (h2 : domME M x2 y2 = true) :
    domME M (x1 &&& x2) (y1 &&& y2) = true := by
  rw [domME_iff] at h1 h2 ⊢
  refine ⟨fun i hi => ?_, fun j hj => ?_⟩
  · simp only [Nat.testBit_and]
    have a := h1.1 i hi; have b := h2.1 i hi
    cases hx1 : x1.testBit i <;> cases hy1 : y1.testBit i <;>
      cases hx2 : x2.testBit i <;> cases hy2 : y2.testBit i <;> simp_all
  · simp only [Nat.testBit_and]
    have a := h1.2 j hj; have b := h2.2 j hj
    cases hx1 : x1.testBit j <;> cases hy1 : y1.testBit j <;>
      cases hx2 : x2.testBit j <;> cases hy2 : y2.testBit j <;> simp_all

theorem domME_or {M x1 y1 x2 y2 : ℕ} (h1 : domME M x1 y1 = true) (h2 : domME M x2 y2 = true) :
    domME M (x1 ||| x2) (y1 ||| y2) = true := by
  rw [domME_iff] at h1 h2 ⊢
  refine ⟨fun i hi => ?_, fun j hj => ?_⟩
  · simp only [Nat.testBit_or]
    have a := h1.1 i hi; have b := h2.1 i hi
    cases hx1 : x1.testBit i <;> cases hy1 : y1.testBit i <;>
      cases hx2 : x2.testBit i <;> cases hy2 : y2.testBit i <;> simp_all
  · simp only [Nat.testBit_or]
    have a := h1.2 j hj; have b := h2.2 j hj
    cases hx1 : x1.testBit j <;> cases hy1 : y1.testBit j <;>
      cases hx2 : x2.testBit j <;> cases hy2 : y2.testBit j <;> simp_all

theorem domME_goal {M E y : ℕ} (hy : y < 2 ^ (M + E)) (h : domME M (goalME M E) y = true) :
    y = goalME M E := by
  rw [domME_iff] at h
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_goalME]
  by_cases hj : j < M
  · have h1 := h.1 j hj
    rw [testBit_goalME] at h1
    have hfalse : decide (M ≤ j ∧ j < M + E) = false := decide_eq_false (by omega)
    rw [hfalse] at h1 ⊢
    cases hyj : y.testBit j <;> simp_all
    exact absurd h1 (by decide)
  · by_cases hj2 : j < M + E
    · have h2 := h.2 j (by omega)
      rw [testBit_goalME] at h2
      have htrue : decide (M ≤ j ∧ j < M + E) = true := decide_eq_true ⟨by omega, hj2⟩
      rw [htrue] at h2 ⊢
      cases hyj : y.testBit j <;> simp_all
      exact absurd h2 (by decide)
    · have hfalse : decide (M ≤ j ∧ j < M + E) = false := decide_eq_false (by omega)
      rw [hfalse]
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) (by omega)))

theorem goodME_iff (M w : ℕ) :
    goodME M w = true ↔ (∃ j, M ≤ j ∧ w.testBit j = true) ∧ (∃ i < M, w.testBit i = false) := by
  unfold goodME
  simp only [Bool.and_eq_true, Bool.not_eq_true', nat_beq_false]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · by_contra hall
      push Not at hall
      apply h1
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_shiftRight, Nat.zero_testBit]
      exact Bool.eq_false_iff.2 (hall (M + k) (by omega))
    · by_contra hall
      push Not at hall
      apply h2
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_and, testBit_mMask]
      by_cases hk : k < M
      · have : w.testBit k = true := Bool.eq_true_of_not_eq_false (hall k hk)
        simp [hk, this]
      · simp [hk]
  · rintro ⟨⟨j, hj, hjt⟩, ⟨i, hi, hif⟩⟩
    constructor
    · intro h0
      have := congrArg (fun x => x.testBit (j - M)) h0
      rw [Nat.testBit_shiftRight, Nat.zero_testBit, show M + (j - M) = j by omega, hjt] at this
      exact Bool.noConfusion this
    · intro hm
      have := congrArg (fun x => x.testBit i) hm
      rw [Nat.testBit_and, testBit_mMask, decide_eq_true hi, hif] at this
      exact Bool.noConfusion this

theorem goodME_goal {M E : ℕ} (hM : 0 < M) (hE : 0 < E) : goodME M (goalME M E) = true := by
  rw [goodME_iff]
  refine ⟨⟨M, le_refl M, ?_⟩, ⟨0, hM, ?_⟩⟩
  · rw [testBit_goalME]; simp [hE]
  · rw [testBit_goalME]; simp [show ¬ M ≤ 0 by omega]

theorem goodME_mono {M x y : ℕ} (hx : goodME M x = true) (hd : domME M x y = true) :
    goodME M y = true := by
  rw [goodME_iff] at hx ⊢
  rw [domME_iff] at hd
  obtain ⟨⟨j, hj, hjt⟩, ⟨i, hi, hif⟩⟩ := hx
  refine ⟨⟨j, hj, ?_⟩, ⟨i, hi, ?_⟩⟩
  · have := hd.2 j hj; rw [hjt] at this; cases hy : y.testBit j <;> simp_all; exact absurd this (by decide)
  · have := hd.1 i hi; rw [hif] at this; cases hy : y.testBit i <;> simp_all; exact absurd this (by decide)

theorem and_lt_pow {a b k : ℕ} (ha : a < 2 ^ k) : (a &&& b) < 2 ^ k :=
  lt_of_le_of_lt Nat.and_le_left ha

theorem or_lt_pow {a b k : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) : (a ||| b) < 2 ^ k :=
  Nat.or_lt_two_pow ha hb

def MBuild (M E : ℕ) : ℕ → Finset ℕ → Prop
  | 0, A => goalME M E ∈ A
  | k + 1, A => MBuild M E k A ∨
      ∃ a ∈ A, ∃ b ∈ A, ∃ conj : Bool, MBuild M E k (insert (if conj then a &&& b else a ||| b) A)

def DBuild (M E : ℕ) : ℕ → Finset ℕ → Prop
  | 0, A => goalME M E ∈ A
  | k + 1, A => DBuild M E k A ∨
      ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ ∃ conj : Bool,
        let z := if conj then a &&& b else a ||| b
        goodME M z = true ∧ (∀ w ∈ A, domME M z w = false) ∧
        DBuild M E k (insert z (A.filter (fun w => domME M w z = false)))

def DLive (M E : ℕ) : ℕ → Finset ℕ → Prop
  | 0, s => s = {goalME M E}
  | k + 1, s => DLive M E k s ∨
      ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ conj : Bool,
        let z := if conj then a &&& b else a ||| b
        goodME M z = true ∧ (∀ w ∈ s, domME M z w = false) ∧
        ∃ rest : Finset ℕ, s = insert a (insert b rest) ∧
          (∀ w ∈ rest, domME M w z = false) ∧ DLive M E k (insert z rest)

theorem mbuild_mono {M E k : ℕ} {A B : Finset ℕ} (hsub : A ⊆ B) (h : MBuild M E k A) :
    MBuild M E k B := by
  induction k generalizing A B with
  | zero => exact hsub h
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, conj, tail⟩
    · exact Or.inl (ih hsub skip)
    · exact Or.inr ⟨a, hsub ha, b, hsub hb, conj, ih (Finset.insert_subset_insert _ hsub) tail⟩

theorem mbuild_to_dbuild {M E : ℕ} (hM : 0 < M) (hE : 0 < E) :
    ∀ (k : ℕ) (A B : Finset ℕ),
      (∀ x ∈ A, x < 2 ^ (M + E)) → (∀ y ∈ B, y < 2 ^ (M + E)) →
      (∀ x ∈ A, goodME M x = true → ∃ y ∈ B, domME M x y = true) →
      MBuild M E k A → DBuild M E k B := by
  intro k
  induction k with
  | zero =>
    intro A B _ hBlt hcov h0
    obtain ⟨y, hyB, hdy⟩ := hcov (goalME M E) h0 (goodME_goal hM hE)
    have hyeq : y = goalME M E := domME_goal (hBlt y hyB) hdy
    show goalME M E ∈ B
    rwa [← hyeq]
  | succ k ih =>
    intro A B hAlt hBlt hcov hstep
    rcases hstep with skip | ⟨a, ha, b, hb, conj, tail⟩
    · exact Or.inl (ih A B hAlt hBlt hcov skip)
    · set z := if conj then a &&& b else a ||| b
      have hzlt : z < 2 ^ (M + E) := by
        cases conj
        · exact or_lt_pow (hAlt a ha) (hAlt b hb)
        · exact and_lt_pow (hAlt a ha)
      have hAlt' : ∀ x ∈ insert z A, x < 2 ^ (M + E) := by
        intro x hx; rcases Finset.mem_insert.1 hx with rfl | hx
        · exact hzlt
        · exact hAlt x hx
      by_cases hgood_a : goodME M a = true
      swap
      · have hkeep : ∀ x ∈ insert z A, goodME M x = true → ∃ y ∈ B, domME M x y = true := by
          intro x hx hgx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · have hnot : ¬ ((∃ j, M ≤ j ∧ a.testBit j = true) ∧ (∃ i < M, a.testBit i = false)) := by
              rwa [← goodME_iff]
            have hza : goodME M z = true := hgx
            by_cases hae : ∃ j, M ≤ j ∧ a.testBit j = true
            · have ham : ∀ i < M, a.testBit i = true := by
                intro i hi; by_contra hf
                exact hnot ⟨hae, ⟨i, hi, Bool.eq_false_iff.2 hf⟩⟩
              cases conj
              · exfalso
                obtain ⟨_, ⟨i, hi, hif⟩⟩ := (goodME_iff M z).1 hza
                simp only [z, Bool.false_eq_true, ↓reduceIte, Nat.testBit_or, ham i hi, Bool.true_or] at hif
                exact Bool.noConfusion hif
              · have hzb : domME M z b = true := by
                  rw [domME_iff]
                  refine ⟨fun i hi => ?_, fun j _ => ?_⟩
                  · simp [z, Nat.testBit_and, ham i hi]
                  · simp only [z, ↓reduceIte, Nat.testBit_and]
                    cases a.testBit j <;> cases b.testBit j <;> decide
                have hgb : goodME M b = true := goodME_mono hza hzb
                obtain ⟨y, hyB, hdy⟩ := hcov b hb hgb
                exact ⟨y, hyB, domME_trans hzb hdy⟩
            · push Not at hae
              have hae0 : ∀ j, M ≤ j → a.testBit j = false := fun j hj => Bool.eq_false_iff.2 (hae j hj)
              cases conj
              · have hzb : domME M z b = true := by
                  rw [domME_iff]
                  refine ⟨fun i _ => ?_, fun j hj => ?_⟩
                  · simp only [z, Bool.false_eq_true, ↓reduceIte, Nat.testBit_or]
                    cases a.testBit i <;> cases b.testBit i <;> decide
                  · simp [z, Nat.testBit_or, hae0 j hj]
                have hgb : goodME M b = true := goodME_mono hza hzb
                obtain ⟨y, hyB, hdy⟩ := hcov b hb hgb
                exact ⟨y, hyB, domME_trans hzb hdy⟩
              · exfalso
                obtain ⟨⟨j, hj, hjt⟩, _⟩ := (goodME_iff M z).1 hza
                simp only [z, ↓reduceIte, Nat.testBit_and, hae0 j hj, Bool.false_and] at hjt
                exact Bool.noConfusion hjt
          · exact hcov x hx hgx
        exact Or.inl (ih _ B hAlt' hBlt hkeep tail)
      by_cases hgood_b : goodME M b = true
      swap
      · have hkeep : ∀ x ∈ insert z A, goodME M x = true → ∃ y ∈ B, domME M x y = true := by
          intro x hx hgx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · have hnot : ¬ ((∃ j, M ≤ j ∧ b.testBit j = true) ∧ (∃ i < M, b.testBit i = false)) := by
              rwa [← goodME_iff]
            have hza : goodME M z = true := hgx
            by_cases hbe : ∃ j, M ≤ j ∧ b.testBit j = true
            · have hbm : ∀ i < M, b.testBit i = true := by
                intro i hi; by_contra hf
                exact hnot ⟨hbe, ⟨i, hi, Bool.eq_false_iff.2 hf⟩⟩
              cases conj
              · exfalso
                obtain ⟨_, ⟨i, hi, hif⟩⟩ := (goodME_iff M z).1 hza
                simp only [z, Bool.false_eq_true, ↓reduceIte, Nat.testBit_or, hbm i hi, Bool.or_true] at hif
                exact Bool.noConfusion hif
              · have hzb : domME M z a = true := by
                  rw [domME_iff]
                  refine ⟨fun i hi => ?_, fun j _ => ?_⟩
                  · simp [z, Nat.testBit_and, hbm i hi]
                  · simp only [z, ↓reduceIte, Nat.testBit_and]
                    cases a.testBit j <;> cases b.testBit j <;> decide
                obtain ⟨y, hyB, hdy⟩ := hcov a ha hgood_a
                exact ⟨y, hyB, domME_trans hzb hdy⟩
            · push Not at hbe
              have hbe0 : ∀ j, M ≤ j → b.testBit j = false := fun j hj => Bool.eq_false_iff.2 (hbe j hj)
              cases conj
              · have hzb : domME M z a = true := by
                  rw [domME_iff]
                  refine ⟨fun i _ => ?_, fun j hj => ?_⟩
                  · simp only [z, Bool.false_eq_true, ↓reduceIte, Nat.testBit_or]
                    cases a.testBit i <;> cases b.testBit i <;> decide
                  · simp [z, Nat.testBit_or, hbe0 j hj]
                obtain ⟨y, hyB, hdy⟩ := hcov a ha hgood_a
                exact ⟨y, hyB, domME_trans hzb hdy⟩
              · exfalso
                obtain ⟨⟨j, hj, hjt⟩, _⟩ := (goodME_iff M z).1 hza
                simp only [z, ↓reduceIte, Nat.testBit_and, hbe0 j hj, Bool.and_false] at hjt
                exact Bool.noConfusion hjt
          · exact hcov x hx hgx
        exact Or.inl (ih _ B hAlt' hBlt hkeep tail)
      obtain ⟨a', ha'B, hda⟩ := hcov a ha hgood_a
      obtain ⟨b', hb'B, hdb⟩ := hcov b hb hgood_b
      set z' := if conj then a' &&& b' else a' ||| b'
      have hzz' : domME M z z' = true := by
        cases conj
        · exact domME_or hda hdb
        · exact domME_and hda hdb
      have hz'lt : z' < 2 ^ (M + E) := by
        cases conj
        · exact or_lt_pow (hBlt a' ha'B) (hBlt b' hb'B)
        · exact and_lt_pow (hBlt a' ha'B)
      by_cases hgz' : goodME M z' = true
      swap
      · have hkeep : ∀ x ∈ insert z A, goodME M x = true → ∃ y ∈ B, domME M x y = true := by
          intro x hx hgx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact absurd (goodME_mono hgx hzz') hgz'
          · exact hcov x hx hgx
        exact Or.inl (ih _ B hAlt' hBlt hkeep tail)
      by_cases hdomB : ∃ w ∈ B, domME M z' w = true
      · obtain ⟨w, hwB, hdw⟩ := hdomB
        have hkeep : ∀ x ∈ insert z A, goodME M x = true → ∃ y ∈ B, domME M x y = true := by
          intro x hx hgx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact ⟨w, hwB, domME_trans hzz' hdw⟩
          · exact hcov x hx hgx
        exact Or.inl (ih _ B hAlt' hBlt hkeep tail)
      · have hne : a' ≠ b' := by
          intro heq; subst heq
          apply hdomB
          refine ⟨a', ha'B, ?_⟩
          have hz'eq : z' = a' := by cases conj <;> simp [z']
          rw [hz'eq]; exact domME_refl M a'
        have hndom : ∀ w ∈ B, domME M z' w = false := by
          intro w hw; exact Bool.eq_false_iff.2 (fun h => hdomB ⟨w, hw, h⟩)
        set B' := insert z' (B.filter (fun w => domME M w z' = false))
        have hB'lt : ∀ y ∈ B', y < 2 ^ (M + E) := by
          intro y hy
          rcases Finset.mem_insert.1 hy with rfl | hy
          · exact hz'lt
          · exact hBlt y (Finset.mem_filter.1 hy).1
        have hcov' : ∀ x ∈ insert z A, goodME M x = true → ∃ y ∈ B', domME M x y = true := by
          intro x hx hgx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact ⟨z', Finset.mem_insert_self _ _, hzz'⟩
          · obtain ⟨y, hyB, hdy⟩ := hcov x hx hgx
            cases hdz : domME M y z' with
            | true => exact ⟨z', Finset.mem_insert_self _ _, domME_trans hdy hdz⟩
            | false => exact ⟨y, Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hyB, hdz⟩), hdy⟩
        exact Or.inr ⟨a', ha'B, b', hb'B, hne, conj, hgz', hndom, ih _ B' hAlt' hB'lt hcov' tail⟩

theorem dbuild_to_dlive {M E : ℕ} : ∀ {k : ℕ} {A : Finset ℕ},
    DBuild M E k A → ∃ s ⊆ A, DLive M E k s := by
  intro k
  induction k with
  | zero =>
    intro A h
    exact ⟨{goalME M E}, Finset.singleton_subset_iff.2 h, rfl⟩
  | succ k ih =>
    intro A h
    rcases h with skip | ⟨a, ha, b, hb, hab, conj, hgz, hndom, tail⟩
    · obtain ⟨s, hs, hl⟩ := ih skip
      exact ⟨s, hs, Or.inl hl⟩
    · set z := if conj then a &&& b else a ||| b
      obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases hzt : z ∈ t
      · set rest := t.erase z
        have hrest_sub : rest ⊆ A.filter (fun w => domME M w z = false) := by
          intro u hu
          have hu' := Finset.mem_erase.1 hu
          exact (Finset.mem_insert.1 (ht hu'.2)).resolve_left hu'.1
        have hrestA : rest ⊆ A := Finset.Subset.trans hrest_sub (Finset.filter_subset _ _)
        have hrest_ndom : ∀ w ∈ rest, domME M w z = false := fun w hw => (Finset.mem_filter.1 (hrest_sub hw)).2
        set s := insert a (insert b rest)
        have hsA : s ⊆ A := Finset.insert_subset ha (Finset.insert_subset hb hrestA)
        refine ⟨s, hsA, Or.inr ⟨a, by simp [s], b, by simp [s], hab, conj, hgz,
          fun w hw => hndom w (hsA hw), rest, rfl, hrest_ndom, ?_⟩⟩
        simpa [z, rest, Finset.insert_erase hzt] using hrun
      · have htA : t ⊆ A := by
          intro u hu
          have hu' := (Finset.mem_insert.1 (ht hu)).resolve_left (fun e => hzt (e ▸ hu))
          exact (Finset.mem_filter.1 hu').1
        exact ⟨t, htA, Or.inl hrun⟩

theorem dlive_card {M E : ℕ} : ∀ {k : ℕ} {s : Finset ℕ}, DLive M E k s → s.card ≤ k + 1
  | 0, _, h => by simp [DLive] at h; simp [h]
  | k + 1, _, h => by
    rcases h with skip | ⟨a, ha, b, hb, _, conj, _, hndom, rest, rfl, _, tail⟩
    · exact le_trans (dlive_card skip) (by omega)
    · have hzrest : (if conj then a &&& b else a ||| b) ∉ rest := by
        intro hm
        have := hndom _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
        rw [domME_refl] at this; cases this
      have htail := dlive_card tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h1 := Finset.card_insert_le a (insert b rest)
      have h2 := Finset.card_insert_le b rest
      omega

theorem first_dlive {M E : ℕ} : ∀ {k : ℕ} {s : Finset ℕ}, DLive M E (k + 1) s →
    s = {goalME M E} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ conj : Bool,
      let z := if conj then a &&& b else a ||| b
      goodME M z = true ∧ (∀ w ∈ s, domME M z w = false) ∧
      ∃ rest : Finset ℕ, s = insert a (insert b rest) ∧
        (∀ w ∈ rest, domME M w z = false) ∧ DLive M E k (insert z rest)
  | 0, _, h => h
  | k + 1, _, h => by
    rcases h with skip | step
    · rcases first_dlive skip with done | ⟨a, ha, b, hb, hab, conj, hgz, hnd, r, hs, hrnd, tail⟩
      · exact Or.inl done
      · exact Or.inr ⟨a, ha, b, hb, hab, conj, hgz, hnd, r, hs, hrnd, Or.inl tail⟩
    · exact Or.inr step

theorem dlive_bits_le {M E : ℕ} : ∀ {k : ℕ} {s : Finset ℕ}, DLive M E k s →
    ∀ i j : ℕ, (∀ w ∈ s, w.testBit i ≤ w.testBit j) → (goalME M E).testBit i ≤ (goalME M E).testBit j
  | 0, _, h, i, j, hw => by simp [DLive] at h; subst h; exact hw _ (by simp)
  | k + 1, _, h, i, j, hw => by
    rcases h with skip | ⟨a, ha, b, hb, _, conj, _, _, rest, rfl, _, tail⟩
    · exact dlive_bits_le skip i j hw
    · apply dlive_bits_le tail i j
      intro w hw'
      rcases Finset.mem_insert.1 hw' with rfl | hwr
      · have hwa := hw a (by simp)
        have hwb := hw b (by simp)
        cases conj <;> simp only [Nat.testBit_and, Nat.testBit_or, ↓reduceIte, Bool.false_eq_true]
        · cases hai : a.testBit i <;> cases haj : a.testBit j <;>
            cases hbi : b.testBit i <;> cases hbj : b.testBit j <;> simp_all
        · cases hai : a.testBit i <;> cases haj : a.testBit j <;>
            cases hbi : b.testBit i <;> cases hbj : b.testBit j <;> simp_all
      · exact hw w (by simp [hwr])

/-! ## Section 2b: Subadditive score bound (`value6` / `eval6_bound`) on `DLive` at `slack = 0` -/

def value6 (a b c d e f : Bool) : ℕ :=
  let x := b.toNat + c.toNat
  let y := (!e).toNat + (!f).toNat
  if a then (if d then y else max x (max y (x + y - 1))) else (if d then 0 else x)

theorem value6_and : ∀ a b c d e f g h i j l m : Bool,
    value6 (a && g) (b && h) (c && i) (d && j) (e && l) (f && m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem value6_or : ∀ a b c d e f g h i j l m : Bool,
    value6 (a || g) (b || h) (c || i) (d || j) (e || l) (f || m)
      ≤ value6 a b c d e f + value6 g h i j l m := by decide +kernel

theorem dlive_score_bound {M E : ℕ} (v : ℕ → ℕ)
    (hand : ∀ a b, v (a &&& b) ≤ v a + v b) (hor : ∀ a b, v (a ||| b) ≤ v a + v b) :
    ∀ {k : ℕ} {s : Finset ℕ}, DLive M E k s → s.card = k + 1 → v (goalME M E) ≤ ∑ w ∈ s, v w
  | 0, _, h, _ => by simp [DLive] at h; subst h; simp
  | k + 1, _, h, hcard => by
    rcases h with skip | ⟨a, ha, b, hb, hab, conj, _, hndom, rest, rfl, _, tail⟩
    · have := dlive_card skip; omega
    · set z := if conj then a &&& b else a ||| b
      have hzrest : z ∉ rest := by
        intro hm
        have := hndom z (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
        rw [domME_refl] at this; cases this
      have htail_card := dlive_card tail
      rw [Finset.card_insert_of_notMem hzrest] at htail_card
      have ha_nr : a ∉ rest := by
        intro ham
        have h1 : insert a (insert b rest) = insert b rest := Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ham)
        rw [h1] at hcard
        have h2 := Finset.card_insert_le b rest
        omega
      have hb_nr : b ∉ rest := by
        intro hbm
        have h1 : insert b rest = rest := Finset.insert_eq_of_mem hbm
        rw [h1] at hcard
        have h2 := Finset.card_insert_le a rest
        omega
      have hrcard : rest.card = k := by
        rw [Finset.card_insert_of_notMem (by simp [hab, ha_nr]), Finset.card_insert_of_notMem hb_nr] at hcard
        omega
      have ih := dlive_score_bound v hand hor tail (by rw [Finset.card_insert_of_notMem hzrest, hrcard])
      rw [Finset.sum_insert hzrest] at ih
      rw [Finset.sum_insert (by simp [hab, ha_nr]), Finset.sum_insert hb_nr]
      have hzle : v z ≤ v a + v b := by cases conj <;> simp [z, hand, hor]
      omega

def eval6 (a b c d e f w : ℕ) : ℕ :=
  value6 (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)

theorem eval6_bound {M E k : ℕ} {s : Finset ℕ} (h : DLive M E k s) (hc : s.card = k + 1)
    (a b c d e f : ℕ) : eval6 a b c d e f (goalME M E) ≤ ∑ w ∈ s, eval6 a b c d e f w := by
  apply dlive_score_bound (eval6 a b c d e f) _ _ h hc
  · intro x y
    simpa only [eval6, Nat.testBit_and] using value6_and
      (x.testBit a) (x.testBit b) (x.testBit c) (x.testBit d) (x.testBit e) (x.testBit f)
      (y.testBit a) (y.testBit b) (y.testBit c) (y.testBit d) (y.testBit e) (y.testBit f)
  · intro x y
    simpa only [eval6, Nat.testBit_or] using value6_or
      (x.testBit a) (x.testBit b) (x.testBit c) (x.testBit d) (x.testBit e) (x.testBit f)
      (y.testBit a) (y.testBit b) (y.testBit c) (y.testBit d) (y.testBit e) (y.testBit f)

/-! ## Section 2c: Bit-permutation symmetries (`ValidPerm`) on `DLive` -/

structure ValidPerm (M E : ℕ) (f : ℕ → ℕ) : Prop where
  lt : ∀ w, w < 2 ^ (M + E) → f w < 2 ^ (M + E)
  and_eq : ∀ a b, a < 2 ^ (M + E) → b < 2 ^ (M + E) → f (a &&& b) = f a &&& f b
  or_eq : ∀ a b, a < 2 ^ (M + E) → b < 2 ^ (M + E) → f (a ||| b) = f a ||| f b
  goal_eq : f (goalME M E) = goalME M E
  good_eq : ∀ w, w < 2 ^ (M + E) → goodME M (f w) = goodME M w
  dom_eq : ∀ a b, a < 2 ^ (M + E) → b < 2 ^ (M + E) → domME M (f a) (f b) = domME M a b
  inj : ∀ a b, a < 2 ^ (M + E) → b < 2 ^ (M + E) → f a = f b → a = b

theorem validPerm_id (M E : ℕ) : ValidPerm M E id :=
  ⟨fun _ h => h, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, rfl, fun _ _ => rfl,
   fun _ _ _ _ => rfl, fun _ _ _ _ h => h⟩

theorem validPerm_comp {M E : ℕ} {f g : ℕ → ℕ} (hf : ValidPerm M E f) (hg : ValidPerm M E g) :
    ValidPerm M E (fun w => f (g w)) where
  lt w hw := hf.lt _ (hg.lt w hw)
  and_eq a b ha hb := by rw [hg.and_eq a b ha hb, hf.and_eq _ _ (hg.lt a ha) (hg.lt b hb)]
  or_eq a b ha hb := by rw [hg.or_eq a b ha hb, hf.or_eq _ _ (hg.lt a ha) (hg.lt b hb)]
  goal_eq := by rw [hg.goal_eq, hf.goal_eq]
  good_eq w hw := by rw [hf.good_eq _ (hg.lt w hw), hg.good_eq w hw]
  dom_eq a b ha hb := by rw [hf.dom_eq _ _ (hg.lt a ha) (hg.lt b hb), hg.dom_eq a b ha hb]
  inj a b ha hb h := hg.inj a b ha hb (hf.inj _ _ (hg.lt a ha) (hg.lt b hb) h)

theorem dlive_image {M E : ℕ} {f : ℕ → ℕ} (hf : ValidPerm M E f) :
    ∀ {k : ℕ} {s : Finset ℕ}, (∀ w ∈ s, w < 2 ^ (M + E)) → DLive M E k s → DLive M E k (s.image f)
  | 0, _, _, h => by simp [DLive] at h; subst h; simp [DLive, hf.goal_eq]
  | k + 1, _, hlt, h => by
    rcases h with skip | ⟨a, ha, b, hb, hab, conj, hgz, hnd, rest, rfl, hrnd, tail⟩
    · exact Or.inl (dlive_image hf hlt skip)
    · have halt : a < 2 ^ (M + E) := hlt a (by simp)
      have hblt : b < 2 ^ (M + E) := hlt b (by simp)
      set z := if conj then a &&& b else a ||| b
      have hzlt : z < 2 ^ (M + E) := by
        cases conj
        · exact or_lt_pow halt hblt
        · exact and_lt_pow halt
      have hfz : f z = if conj then f a &&& f b else f a ||| f b := by
        cases conj
        · exact hf.or_eq a b halt hblt
        · exact hf.and_eq a b halt hblt
      have hne : f a ≠ f b := fun e => hab (hf.inj a b halt hblt e)
      have hgz' : goodME M (if conj then f a &&& f b else f a ||| f b) = true := by
        rw [← hfz, hf.good_eq z hzlt]; exact hgz
      have hnd' : ∀ w ∈ (insert a (insert b rest)).image f,
          domME M (if conj then f a &&& f b else f a ||| f b) w = false := by
        intro w hw
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hw
        rw [← hfz, hf.dom_eq z u hzlt (hlt u hu)]
        exact hnd u hu
      have hrnd' : ∀ w ∈ rest.image f,
          domME M w (if conj then f a &&& f b else f a ||| f b) = false := by
        intro w hw
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hw
        rw [← hfz, hf.dom_eq u z (hlt u (by simp [hu])) hzlt]
        exact hrnd u hu
      have htail_lt : ∀ w ∈ insert z rest, w < 2 ^ (M + E) := by
        intro w hw
        rcases Finset.mem_insert.1 hw with rfl | hwr
        · exact hzlt
        · exact hlt w (by simp [hwr])
      have htail' := dlive_image hf htail_lt tail
      rw [Finset.image_insert, hfz] at htail'
      refine Or.inr ⟨f a, Finset.mem_image_of_mem f (by simp), f b, Finset.mem_image_of_mem f (by simp),
        hne, conj, hgz', hnd', rest.image f, ?_, hrnd', htail'⟩
      simp [Finset.image_insert]

def invBpOK (M E : ℕ) (invBp : List ℕ) : Bool :=
  let tot := M + E
  invBp.length == tot &&
  (List.range tot).all (fun i => invBp.contains i) &&
  (List.range M).all (fun i => invBp.getD i tot < M) &&
  (List.range E).all (fun j => M ≤ invBp.getD (M + j) tot && invBp.getD (M + j) tot < tot)

def evalPiece (p : ℕ × ℕ × ℕ) (w : ℕ) : ℕ :=
  match p.2.1 with
  | 0 => w &&& p.1
  | 1 => (w &&& p.1) <<< p.2.2
  | _ => (w &&& p.1) >>> p.2.2

def applySpec : List (ℕ × ℕ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | [p], w => evalPiece p w
  | p :: ps, w => evalPiece p w ||| applySpec ps w

def pieceOK (M E : ℕ) (invBp : List ℕ) (p : ℕ × ℕ × ℕ) : Bool :=
  let tot := M + E
  let m := p.1
  let dir := p.2.1
  let d := p.2.2
  m < 2 ^ tot &&
  (List.range tot).all (fun b =>
    if m.testBit b then
      match dir with
      | 0 => invBp.getD b tot == b
      | 1 => b + d < tot && invBp.getD (b + d) tot == b
      | _ => d ≤ b && invBp.getD (b - d) tot == b
    else true)

def specOK (M E : ℕ) (spec : List (ℕ × ℕ × ℕ)) (invBp : List ℕ) : Bool :=
  let tot := M + E
  invBpOK M E invBp &&
  spec.all (pieceOK M E invBp) &&
  (List.range tot).all (fun b => spec.any (fun p => p.1.testBit b))

theorem testBit_lt_of_lt {x k j : ℕ} (hx : x < 2 ^ k) (hj : k ≤ j) : x.testBit j = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hj))

theorem piece_testBit_true {M E : ℕ} {invBp : List ℕ} {p : ℕ × ℕ × ℕ} {w j : ℕ}
    (hp : pieceOK M E invBp p = true) (ht : (evalPiece p w).testBit j = true) :
    j < M + E ∧ w.testBit (invBp.getD j (M + E)) = true := by
  simp only [pieceOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hp
  obtain ⟨hm, hall⟩ := hp
  rcases p with ⟨m, dir, d⟩
  cases dir with
  | zero =>
    simp only [evalPiece, Nat.testBit_and, Bool.and_eq_true] at ht
    have hj : j < M + E := by
      by_contra hge
      rw [testBit_lt_of_lt hm (by omega)] at ht; exact Bool.noConfusion ht.2
    have hjb := hall j hj
    simp only [ht.2, ↓reduceIte, beq_iff_eq] at hjb
    exact ⟨hj, hjb.symm ▸ ht.1⟩
  | succ dir' =>
    cases dir' with
    | zero =>
      simp only [evalPiece, Nat.testBit_shiftLeft, Nat.testBit_and, Bool.and_eq_true,
        decide_eq_true_eq] at ht
      obtain ⟨hdj, hwb, hmb⟩ := ht
      have hblt : j - d < M + E := by
        by_contra hge
        rw [testBit_lt_of_lt hm (by omega)] at hmb; exact Bool.noConfusion hmb
      have hjb := hall (j - d) hblt
      simp only [hmb, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hjb
      have heq : j - d + d = j := by omega
      rw [heq] at hjb
      exact ⟨hjb.1, hjb.2.symm ▸ hwb⟩
    | succ _ =>
      simp only [evalPiece, Nat.testBit_shiftRight, Nat.testBit_and, Bool.and_eq_true] at ht
      obtain ⟨hwb, hmb⟩ := ht
      have hblt : d + j < M + E := by
        by_contra hge
        rw [testBit_lt_of_lt hm (by omega)] at hmb; exact Bool.noConfusion hmb
      have hjb := hall (d + j) hblt
      simp only [hmb, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hjb
      have heq : d + j - d = j := by omega
      rw [heq] at hjb
      have hj : j < M + E := by omega
      exact ⟨hj, hjb.2.symm ▸ hwb⟩

theorem nodup_of_length_eq_toFinset_card {α : Type} [DecidableEq α] :
    ∀ {l : List α}, l.toFinset.card = l.length → l.Nodup
  | [], _ => List.nodup_nil
  | a :: t, h => by
    by_cases ha : a ∈ t
    · have h1 : (a :: t).toFinset = t.toFinset := by
        ext x; simp only [List.mem_toFinset, List.mem_cons]
        exact ⟨fun hx => hx.elim (fun e => e ▸ ha) id, Or.inr⟩
      rw [h1] at h
      have hle := List.toFinset_card_le t
      simp only [List.length_cons] at h
      omega
    · have h1 : (a :: t).toFinset = insert a t.toFinset := by ext x; simp
      rw [h1, Finset.card_insert_of_notMem (by simpa using ha)] at h
      simp only [List.length_cons] at h
      exact List.nodup_cons.2 ⟨ha, nodup_of_length_eq_toFinset_card (by omega)⟩

theorem applySpec_testBit_iff {M E : ℕ} {spec : List (ℕ × ℕ × ℕ)} {invBp : List ℕ}
    (hok : specOK M E spec invBp = true) (w j : ℕ) :
    (applySpec spec w).testBit j = if j < M + E then w.testBit (invBp.getD j (M + E)) else false := by
  have hspec := hok
  simp only [specOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.any_eq_true] at hspec
  obtain ⟨⟨hinv, hpieces⟩, hcov⟩ := hspec
  have hinv' := hinv
  simp only [invBpOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    List.contains_eq_mem, decide_eq_true_eq] at hinv'
  obtain ⟨⟨⟨hlen, hsurj⟩, hMpart⟩, hEpart⟩ := hinv'
  have hlt_inv : ∀ k < M + E, invBp.getD k (M + E) < M + E := by
    intro k hk
    by_cases hkM : k < M
    · have := hMpart k hkM; omega
    · have := (hEpart (k - M) (by omega)).2
      rwa [show M + (k - M) = k by omega] at this
  have hnodup : invBp.Nodup := by
    have hnd := List.nodup_range (n := M + E)
    have hcard : (List.range (M + E)).toFinset.card ≤ invBp.toFinset.card :=
      Finset.card_le_card (fun x hx => List.mem_toFinset.2 (hsurj x (List.mem_range.1 (List.mem_toFinset.1 hx))))
    rw [List.toFinset_card_of_nodup hnd, List.length_range] at hcard
    have hle2 := List.toFinset_card_le invBp
    exact nodup_of_length_eq_toFinset_card (by omega)
  have hinj_inv : ∀ k1 < M + E, ∀ k2 < M + E,
      invBp.getD k1 (M + E) = invBp.getD k2 (M + E) → k1 = k2 := by
    intro k1 hk1 k2 hk2 heq
    have h1 : k1 < invBp.length := by omega
    have h2 : k2 < invBp.length := by omega
    rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at heq
    exact (List.Nodup.getElem_inj_iff hnodup).1 heq
  have happ : ∀ l : List (ℕ × ℕ × ℕ),
      (applySpec l w).testBit j = true ↔ ∃ p ∈ l, (evalPiece p w).testBit j = true := by
    intro l
    induction l with
    | nil => simp [applySpec]
    | cons p ps ih =>
      cases ps with
      | nil => simp [applySpec]
      | cons p2 ps2 =>
        simp only [applySpec, Nat.testBit_or, Bool.or_eq_true, ih, List.mem_cons]
        constructor
        · rintro (h | ⟨q, hq, hqt⟩)
          · exact ⟨p, Or.inl rfl, h⟩
          · exact ⟨q, Or.inr hq, hqt⟩
        · rintro ⟨q, rfl | hq, hqt⟩
          · exact Or.inl hqt
          · exact Or.inr ⟨q, hq, hqt⟩
  apply Bool.eq_iff_iff.2
  rw [happ]
  split_ifs with hj
  · constructor
    · rintro ⟨p, hp, hpt⟩
      exact (piece_testBit_true (hpieces p hp) hpt).2
    · intro hwt
      set b := invBp.getD j (M + E)
      have hblt : b < M + E := hlt_inv j hj
      obtain ⟨p, hp, hmb⟩ := hcov b hblt
      refine ⟨p, hp, ?_⟩
      have hp' := hpieces p hp
      simp only [pieceOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hp'
      have hpb := hp'.2 b hblt
      simp only [hmb, ↓reduceIte] at hpb
      rcases p with ⟨m, dir, d⟩
      cases dir with
      | zero =>
        simp only [beq_iff_eq] at hpb
        have hjeq : j = b := hinj_inv j hj b hblt hpb.symm
        rw [hjeq]; simp [evalPiece, Nat.testBit_and, hwt, hmb]
      | succ dir' =>
        cases dir' with
        | zero =>
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hpb
          have hjeq : j = b + d := hinj_inv j hj (b + d) hpb.1 hpb.2.symm
          rw [hjeq]
          simp only [evalPiece, Nat.testBit_shiftLeft, Nat.testBit_and, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨by omega, by simpa [show b + d - d = b by omega] using hwt,
            by simpa [show b + d - d = b by omega] using hmb⟩
        | succ _ =>
          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hpb
          have hjeq : j = b - d := hinj_inv j hj (b - d) (by omega) hpb.2.symm
          rw [hjeq]
          simp only [evalPiece, Nat.testBit_shiftRight, Nat.testBit_and, Bool.and_eq_true]
          exact ⟨by simpa [show d + (b - d) = b by omega] using hwt,
            by simpa [show d + (b - d) = b by omega] using hmb⟩
  · simp only [iff_false, not_exists, not_and]
    intro p hp hpt
    exact hj (piece_testBit_true (hpieces p hp) hpt).1

theorem validPerm_of_spec (M E : ℕ) (f : ℕ → ℕ) (spec : List (ℕ × ℕ × ℕ)) (invBp : List ℕ)
    (hdef : ∀ w, f w = applySpec spec w) (hok : specOK M E spec invBp = true) :
    ValidPerm M E f := by
  have hbit : ∀ w j, (f w).testBit j = if j < M + E then w.testBit (invBp.getD j (M + E)) else false :=
    fun w j => by rw [hdef]; exact applySpec_testBit_iff hok w j
  have hinv := hok
  simp only [specOK, invBpOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    List.contains_eq_mem, decide_eq_true_eq] at hinv
  obtain ⟨⟨⟨⟨⟨hlen, hsurj⟩, hMpart⟩, hEpart⟩, _⟩, _⟩ := hinv
  have hsurj_get : ∀ i < M + E, ∃ j < M + E, invBp.getD j (M + E) = i := by
    intro i hi
    obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.1 (hsurj i hi)
    exact ⟨j, by omega, by rw [List.getD_eq_getElem _ _ hj, hje]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w _
    exact lt_two_pow_of_testBit_false (f w) (M + E) (fun j hj => by
      rw [hbit]; simp [show ¬ j < M + E by omega])
  · intro a b _ _
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_and, hbit, hbit, hbit]
    split_ifs <;> simp [Nat.testBit_and]
  · intro a b _ _
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_or, hbit, hbit, hbit]
    split_ifs <;> simp [Nat.testBit_or]
  · apply Nat.eq_of_testBit_eq; intro j
    rw [hbit]
    by_cases hj : j < M + E
    · simp only [hj, ↓reduceIte, testBit_goalME]
      by_cases hjM : j < M
      · have h1 := hMpart j hjM
        rw [decide_eq_false (by omega), decide_eq_false (by omega)]
      · have h2 := hEpart (j - M) (by omega)
        rw [show M + (j - M) = j by omega] at h2
        rw [decide_eq_true h2, decide_eq_true ⟨by omega, trivial⟩]
    · simp only [hj, ↓reduceIte, testBit_goalME]
      simp
  · intro w hw
    apply Bool.eq_iff_iff.2
    rw [goodME_iff, goodME_iff]
    constructor
    · rintro ⟨⟨j, hjM, hjt⟩, ⟨i, hiM, hif⟩⟩
      rw [hbit] at hjt hif
      by_cases hjlt : j < M + E
      swap; · simp [hjlt] at hjt
      simp only [hjlt, ↓reduceIte] at hjt
      have hif' : w.testBit (invBp.getD i (M + E)) = false := by
        simpa [show i < M + E by omega] using hif
      have h1 := hEpart (j - M) (by omega); rw [show M + (j - M) = j by omega] at h1
      exact ⟨⟨invBp.getD j (M + E), h1.1, hjt⟩, ⟨invBp.getD i (M + E), hMpart i hiM, hif'⟩⟩
    · rintro ⟨⟨j, hjM, hjt⟩, ⟨i, hiM, hif⟩⟩
      have hjlt : j < M + E := by
        by_contra hge; rw [testBit_lt_of_lt hw (by omega)] at hjt; exact Bool.noConfusion hjt
      obtain ⟨j', hj'lt, hj'eq⟩ := hsurj_get j hjlt
      obtain ⟨i', hi'lt, hi'eq⟩ := hsurj_get i (by omega)
      have hj'M : M ≤ j' := by
        by_contra hlt; have := hMpart j' (by omega); omega
      have hi'M : i' < M := by
        by_contra hge; have := (hEpart (i' - M) (by omega)).1
        rw [show M + (i' - M) = i' by omega] at this; omega
      refine ⟨⟨j', hj'M, ?_⟩, ⟨i', hi'M, ?_⟩⟩
      · rw [hbit]; simp only [hj'lt, ↓reduceIte, hj'eq]; exact hjt
      · rw [hbit]; simp only [hi'lt, ↓reduceIte, hi'eq]; exact hif
  · intro a b ha hb
    apply Bool.eq_iff_iff.2
    rw [domME_iff, domME_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i hi => ?_, fun j hj => ?_⟩
      · obtain ⟨i', hi'lt, hi'eq⟩ := hsurj_get i (by omega)
        have hi'M : i' < M := by
          by_contra hge; have := (hEpart (i' - M) (by omega)).1
          rw [show M + (i' - M) = i' by omega] at this; omega
        have := h1 i' hi'M
        rw [hbit, hbit] at this; simp only [hi'lt, ↓reduceIte, hi'eq] at this
        exact this
      · by_cases hjlt : j < M + E
        · obtain ⟨j', hj'lt, hj'eq⟩ := hsurj_get j hjlt
          have hj'M : M ≤ j' := by
            by_contra hlt; have := hMpart j' (by omega); omega
          have := h2 j' hj'M
          rw [hbit, hbit] at this; simp only [hj'lt, ↓reduceIte, hj'eq] at this
          exact this
        · rw [testBit_lt_of_lt ha (by omega), testBit_lt_of_lt hb (by omega)]
    · rintro ⟨h1, h2⟩
      refine ⟨fun i hi => ?_, fun j hj => ?_⟩
      · rw [hbit, hbit]; simp only [show i < M + E by omega, ↓reduceIte]
        exact h1 _ (hMpart i hi)
      · rw [hbit, hbit]
        split_ifs with hjlt
        · have hE := hEpart (j - M) (by omega); rw [show M + (j - M) = j by omega] at hE
          exact h2 _ hE.1
        · exact le_refl false
  · intro a b ha hb hfab
    apply Nat.eq_of_testBit_eq; intro i
    by_cases hilt : i < M + E
    · obtain ⟨j, hjlt, hjeq⟩ := hsurj_get i hilt
      have := congrArg (fun x => x.testBit j) hfab
      rw [hbit, hbit] at this; simp only [hjlt, ↓reduceIte, hjeq] at this
      exact this
    · rw [testBit_lt_of_lt ha (by omega), testBit_lt_of_lt hb (by omega)]

/-! ## Section 2d: TURBO V4 evaluator & soundness proofs -/

def fldB (T : ℕ → ℕ) (w i : ℕ) : ℕ :=
  (T (i >>> 6) >>> (w * (i &&& 63))) &&& ((1 <<< w) - 1)

def bsrB (T : ℕ → ℕ) (w h : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    match Nat.blt (lo + 1) hi with
    | true =>
      let mid := (lo + hi) >>> 1
      match Nat.ble (fldB T w mid) h with
      | true => bsrB T w h f mid hi
      | false => bsrB T w h f lo mid
    | false => lo

def hw24 (w : ℕ) : ℕ :=
  let x := w + 145
  let x2 := (x * x) % 1048573
  (x2 * x) % 1048573

def hz24 : List ℕ → ℕ
  | [] => 0
  | w :: t => hw24 w + hz24 t

def hk24 (zs : List ℕ) : ℕ := hz24 zs % 1048573

def oriKeyFast : List ℕ → ℕ
  | [] => 0
  | w :: t => w * (w + 17) + oriKeyFast t

def mapPerm (f : ℕ → ℕ) : List ℕ → List ℕ
  | [] => []
  | w :: t => f w :: mapPerm f t

theorem mapPerm_eq_map (f : ℕ → ℕ) (ws : List ℕ) : mapPerm f ws = ws.map f := by
  induction ws with
  | nil => rfl
  | cons w t ih => simp [mapPerm, ih]

def oriStageGo (perm : ℕ → ℕ → ℕ) (ws : List ℕ) : List ℕ → ℕ → List ℕ → List ℕ
  | [], _, best => best
  | pi :: rest, bestK, best =>
    let cur := mapPerm (perm pi) ws
    let ck := oriKeyFast cur
    match Nat.blt ck bestK with
    | true => oriStageGo perm ws rest ck cur
    | false => oriStageGo perm ws rest bestK best

def oriStage (perm : ℕ → ℕ → ℕ) (pis : List ℕ) (ws : List ℕ) : List ℕ :=
  oriStageGo perm ws pis (oriKeyFast ws) ws

def oriStages (perm : ℕ → ℕ → ℕ) : List (List ℕ) → List ℕ → List ℕ
  | [], ws => ws
  | st :: rest, ws => oriStages perm rest (oriStage perm st ws)

theorem oriStageGo_mem {M E : ℕ} {perm : ℕ → ℕ → ℕ}
    (hp : ∀ pi, ValidPerm M E (perm pi)) (ws : List ℕ) :
    ∀ (pis : List ℕ) (bestK : ℕ) (best : List ℕ),
      (∃ f, ValidPerm M E f ∧ best = ws.map f) →
      ∃ f, ValidPerm M E f ∧ oriStageGo perm ws pis bestK best = ws.map f
  | [], _, _, h => h
  | pi :: rest, bestK, best, h => by
    simp only [oriStageGo]
    split
    · exact oriStageGo_mem hp ws rest _ _ ⟨perm pi, hp pi, mapPerm_eq_map _ _⟩
    · exact oriStageGo_mem hp ws rest _ _ h

theorem oriStages_valid {M E : ℕ} {perm : ℕ → ℕ → ℕ}
    (hp : ∀ pi, ValidPerm M E (perm pi)) :
    ∀ (stages : List (List ℕ)) (ws : List ℕ),
      ∃ f, ValidPerm M E f ∧ oriStages perm stages ws = ws.map f
  | [], ws => ⟨id, validPerm_id M E, by simp [oriStages]⟩
  | st :: rest, ws => by
    simp only [oriStages]
    obtain ⟨f1, hf1, h1⟩ := oriStageGo_mem hp ws st (oriKeyFast ws) ws ⟨id, validPerm_id M E, by simp⟩
    obtain ⟨f2, hf2, h2⟩ := oriStages_valid hp rest (oriStage perm st ws)
    refine ⟨fun w => f2 (f1 w), validPerm_comp hf2 hf1, ?_⟩
    rw [h2, oriStage, h1, List.map_map]; rfl

theorem toFinset_map_eq_image (f : ℕ → ℕ) (ws : List ℕ) :
    (ws.map f).toFinset = ws.toFinset.image f := by
  ext x; simp

theorem oriStages_dlive {M E k : ℕ} {perm : ℕ → ℕ → ℕ} {stages : List (List ℕ)} {ws : List ℕ}
    (hp : ∀ pi, ValidPerm M E (perm pi))
    (hlt : ∀ w ∈ ws, w < 2 ^ (M + E)) (h : DLive M E k ws.toFinset) :
    DLive M E k (oriStages perm stages ws).toFinset := by
  obtain ⟨f, hf, hmap⟩ := oriStages_valid hp stages ws
  rw [hmap, toFinset_map_eq_image]
  exact dlive_image hf (fun w hw => hlt w (List.mem_toFinset.1 hw)) h

def idxGenB (NN : ℕ → ℕ) (HT : ℕ → ℕ → ℕ) (s : ℕ) (zs : List ℕ) : ℕ :=
  bsrB (HT s) 20 (hk24 zs) 11 0 (NN s)

def popAt : ℕ → List ℕ → ℕ × List ℕ
  | _, [] => (0, [])
  | 0, a :: t => (a, t)
  | k + 1, a :: t =>
    let (v, r) := popAt k t
    (v, a :: r)

def mvDL (ori : List ℕ → List ℕ) (c : ℕ) (ws : List ℕ) : List ℕ :=
  let i := c &&& 15
  let j := (c >>> 4) &&& 15
  let op := (c >>> 8) &&& 1
  let ka := (c >>> 9) &&& 1
  let kb := (c >>> 10) &&& 1
  let (b, r0) := popAt j ws
  let (a, r) := popAt i r0
  let w := match Nat.beq op 0 with | true => a &&& b | false => a ||| b
  let r1 := match Nat.beq kb 1 with | true => b :: r | false => r
  let r2 := match Nat.beq ka 1 with | true => a :: r1 | false => r1
  ori (w :: r2)

def StGenB (xs : List ℕ) (ori : List ℕ → List ℕ) (PT : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => xs
  | d + 1, s, j =>
    let e := fldB (PT s) 22 j
    mvDL ori (e &&& 0x7FF) (StGenB xs ori PT d (s + 1) (e >>> 11))

def SgenB (cap : ℕ) (xs : List ℕ) (ori : List ℕ → List ℕ) (PT : ℕ → ℕ → ℕ) (s j : ℕ) : List ℕ :=
  StGenB xs ori PT (cap - s) s j

def eraseNat (x : ℕ) : List ℕ → Option (List ℕ)
  | [] => none
  | a :: t =>
    match Nat.beq a x with
    | true => some t
    | false => match eraseNat x t with
      | none => none
      | some t' => some (a :: t')

def isPermNat : List ℕ → List ℕ → Bool
  | [], [] => true
  | [], _ :: _ => false
  | a :: t, ys =>
    match eraseNat a ys with
    | none => false
    | some ys' => isPermNat t ys'

theorem eraseNat_perm {x : ℕ} : ∀ {ys ys' : List ℕ},
    eraseNat x ys = some ys' → ys.Perm (x :: ys')
  | [], _, h => by simp [eraseNat] at h
  | a :: t, ys', h => by
    simp only [eraseNat] at h
    cases hax : Nat.beq a x with
    | true =>
      rw [hax] at h
      have heq : a = x := nat_beq_true.1 hax
      subst heq; cases h; exact List.Perm.refl _
    | false =>
      rw [hax] at h
      cases he : eraseNat x t with
      | none => rw [he] at h; cases h
      | some t' =>
        rw [he] at h; cases h
        exact (List.Perm.cons a (eraseNat_perm he)).trans (List.Perm.swap x a t')

theorem isPermNat_sound : ∀ {xs ys : List ℕ}, isPermNat xs ys = true → xs.Perm ys
  | [], [], _ => List.Perm.refl []
  | [], _ :: _, h => by simp [isPermNat] at h
  | a :: t, ys, h => by
    simp only [isPermNat] at h
    cases he : eraseNat a ys with
    | none => rw [he] at h; cases h
    | some ys' =>
      rw [he] at h
      exact (List.Perm.cons a (isPermNat_sound h)).trans (eraseNat_perm he).symm

def allLt (bound : ℕ) : List ℕ → Bool
  | [] => true
  | w :: t => Nat.blt w bound && allLt bound t

theorem allLt_sound {bound : ℕ} : ∀ {ws : List ℕ}, allLt bound ws = true → ∀ w ∈ ws, w < bound
  | [], _ => fun _ h => by simp at h
  | a :: t, h => by
    simp only [allLt, Bool.and_eq_true, Nat.blt_eq] at h
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hwt
    · exact h.1
    · exact allLt_sound h.2 w hwt

def memNat (x : ℕ) : List ℕ → Bool
  | [] => false
  | a :: t => Nat.beq a x || memNat x t

theorem memNat_iff (x : ℕ) : ∀ ws : List ℕ, memNat x ws = true ↔ x ∈ ws
  | [] => by simp [memNat]
  | a :: t => by
    simp only [memNat, Bool.or_eq_true, nat_beq_true, memNat_iff x t, List.mem_cons]
    constructor
    · rintro (rfl | h)
      · exact Or.inl rfl
      · exact Or.inr h
    · rintro (rfl | h)
      · exact Or.inl rfl
      · exact Or.inr h

def nodupNat : List ℕ → Bool
  | [] => true
  | a :: t => !(memNat a t) && nodupNat t

theorem nodupNat_sound : ∀ {ws : List ℕ}, nodupNat ws = true → ws.Nodup
  | [], _ => List.nodup_nil
  | a :: t, h => by
    simp only [nodupNat, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.2 ⟨?_, nodupNat_sound h.2⟩
    intro ham
    have := (memNat_iff a t).2 ham
    rw [this] at h; exact Bool.noConfusion h.1

def validME (M E : ℕ) : Bool :=
  1 ≤ M && M ≤ 9 && (E == 3 || E == 5 || E == 6 || E == 7 || E == 8 || E == 9)

theorem validME_props {M E : ℕ} (h : validME M E = true) :
    1 ≤ M ∧ M ≤ 9 ∧ 2 ≤ E ∧ E < 10 ∧ (E == 3 || E == 5 || E == 6 || E == 7 || E == 8 || E == 9) = true := by
  simp only [validME, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1.1, h.1.2, ?_, ?_, h.2⟩
  · have hE := h.2
    simp only [Bool.or_eq_true, beq_iff_eq] at hE
    rcases hE with ((((rfl | rfl) | rfl) | rfl) | rfl) | rfl <;> omega
  · have hE := h.2
    simp only [Bool.or_eq_true, beq_iff_eq] at hE
    rcases hE with ((((rfl | rfl) | rfl) | rfl) | rfl) | rfl <;> omega

def expTab (E : ℕ) : ℕ :=
  match E with
  | 3 => 0x249248241240209208201200049048041040009008001000
  | 5 => 0x8421084200840108400080210802008001080000042100420004010040000021000200000100000
  | 6 => 0x41041041040041001041000040041040040040001040000001041001040001001001000000041000040000001000000
  | 7 => 0x204081020408002040010204000020008102000800200001020000000040810004080000400100040000000081000008000000010000000
  | 8 => 0x1010101010101000101000101010000010001010100010001000001010000000001010100010100000100010001000000000101000001000000000100000000
  | 9 => 0x8040201008040200008040001008040000008000201008000200008000001008000000000040201000040200000040001000040000000000201000000200000000001000000000
  | _ => 0

def sepFast (M E mMask tab e4 mask4 : ℕ) (w : ℕ) : ℕ :=
  let inv := mMask ^^^ (w &&& mMask)
  let lo := (tab >>> (e4 * (inv &&& 15))) &&& mask4
  let hi := (tab >>> (e4 * ((inv >>> 4) &&& 15))) &&& mask4
  let top := match Nat.ble 256 inv with | true => 1 <<< (8 * E) | false => 0
  (lo ||| (hi <<< e4) ||| top) * (w >>> M)

def expSpec (E x : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => expSpec E x m ||| (if x.testBit m then 1 <<< (m * E) else 0)

theorem expSpec_lt {E : ℕ} (hE : 0 < E) (x : ℕ) : ∀ m, expSpec E x m < 2 ^ (m * E)
  | 0 => by simp [expSpec]
  | m + 1 => by
    have ih := expSpec_lt hE x m
    simp only [expSpec]
    apply Nat.or_lt_two_pow
      (lt_of_lt_of_le ih (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right E (Nat.le_succ m))))
    split_ifs
    · rw [Nat.shiftLeft_eq, one_mul]
      exact Nat.pow_lt_pow_right (by omega) (by rw [Nat.succ_mul]; omega)
    · exact Nat.two_pow_pos _

theorem expSpec_testBit {E : ℕ} (hE : 0 < E) (x : ℕ) : ∀ m p,
    (expSpec E x m).testBit p = decide (p / E < m ∧ p % E = 0 ∧ x.testBit (p / E) = true)
  | 0, p => by simp [expSpec]
  | m + 1, p => by
    simp only [expSpec, Nat.testBit_or, expSpec_testBit hE x m p]
    by_cases hlt : p / E < m
    · have hne : p ≠ m * E := by intro e; subst e; rw [Nat.mul_div_cancel _ hE] at hlt; omega
      have hbit : (if x.testBit m then 1 <<< (m * E) else 0).testBit p = false := by
        split_ifs
        · rw [Nat.testBit_shiftLeft]
          by_cases hge : m * E ≤ p
          · have hpos : p - m * E ≠ 0 := by omega
            simp only [decide_eq_true hge, Bool.true_and]
            cases hk : p - m * E with
            | zero => omega
            | succ k => simp [Nat.testBit_succ]
          · simp [hge]
        · simp
      rw [hbit, Bool.or_false]
      have h1 : p / E < m + 1 := by omega
      simp [hlt, h1]
    · by_cases heq : p / E = m
      · have hf : decide (p / E < m ∧ p % E = 0 ∧ x.testBit (p / E) = true) = false :=
          decide_eq_false (by omega)
        rw [hf, Bool.false_or]
        have hlt1 : p / E < m + 1 := by omega
        by_cases hmod : p % E = 0
        · have hp : p = m * E := by
            have := Nat.div_add_mod p E; rw [heq, hmod, Nat.mul_comm] at this; omega
          subst hp
          have hdiv : m * E / E = m := Nat.mul_div_cancel m hE
          have hmod0 : m * E % E = 0 := Nat.mul_mod_left m E
          cases hx : x.testBit m <;> simp [hdiv, hmod0, hx, Nat.testBit_shiftLeft]
        · have hne : p ≠ m * E := by intro e; subst e; exact hmod (Nat.mul_mod_left m E)
          have hbit : (if x.testBit m then 1 <<< (m * E) else 0).testBit p = false := by
            split_ifs
            · rw [Nat.testBit_shiftLeft]
              by_cases hge : m * E ≤ p
              · cases hk : p - m * E with
                | zero => omega
                | succ k => simp [Nat.testBit_succ]
              · simp [hge]
            · simp
          rw [hbit]
          simp [hmod]
      · have hf1 : decide (p / E < m ∧ p % E = 0 ∧ x.testBit (p / E) = true) = false :=
          decide_eq_false (by omega)
        have hf2 : decide (p / E < m + 1 ∧ p % E = 0 ∧ x.testBit (p / E) = true) = false :=
          decide_eq_false (by omega)
        rw [hf1, hf2, Bool.false_or]
        have hgt : m * E < p := by
          have hge : m + 1 ≤ p / E := by omega
          have := Nat.mul_le_mul_right E hge
          have hdiv := Nat.div_mul_le_self p E
          rw [Nat.succ_mul] at this
          omega
        split_ifs
        · rw [Nat.testBit_shiftLeft]
          cases hk : p - m * E with
          | zero => omega
          | succ k => simp [Nat.testBit_succ]
        · simp

theorem testBit_add_mul_two_pow : ∀ (k a b j : ℕ), a < 2 ^ k →
    (a + b * 2 ^ k).testBit j = if j < k then a.testBit j else b.testBit (j - k)
  | 0, a, b, j, ha => by have ha0 : a = 0 := by omega
                         subst ha0; simp
  | k + 1, a, b, 0, ha => by
    simp only [Nat.testBit_zero, Nat.zero_lt_succ, ↓reduceIte, pow_succ']
    have : (a + b * (2 * 2 ^ k)) % 2 = a % 2 := by
      rw [show a + b * (2 * 2 ^ k) = a + 2 * (b * 2 ^ k) by ring, Nat.add_mul_mod_self_left]
    rw [this]
  | k + 1, a, b, j + 1, ha => by
    have ha2 : a / 2 < 2 ^ k := by rw [pow_succ'] at ha; omega
    have hdiv : (a + b * 2 ^ (k + 1)) / 2 = a / 2 + b * 2 ^ k := by
      rw [pow_succ', show a + b * (2 * 2 ^ k) = a + 2 * (b * 2 ^ k) by ring, Nat.add_mul_div_left _ _ (by omega)]
    rw [Nat.testBit_succ, hdiv, testBit_add_mul_two_pow k (a / 2) b j ha2]
    by_cases hj : j < k
    · simp [hj, show j + 1 < k + 1 by omega, Nat.testBit_succ]
    · simp [hj, show ¬ j + 1 < k + 1 by omega, show j + 1 - (k + 1) = j - k by omega]

theorem or_eq_add_of_lt {a b k : ℕ} (ha : a < 2 ^ k) : (a ||| (b <<< k)) = a + b * 2 ^ k := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, testBit_add_mul_two_pow k a b j ha]
  by_cases hj : j < k
  · simp [hj, show ¬ k ≤ j by omega]
  · rw [testBit_lt_of_lt ha (by omega)]; simp [hj, show k ≤ j by omega]

theorem expSpec_mul_lt {E : ℕ} (hE : 0 < E) (x eb : ℕ) (heb : eb < 2 ^ E) (m : ℕ) :
    expSpec E x m * eb < 2 ^ (m * E) := by
  have hbound : expSpec E x m * (2 ^ E - 1) < 2 ^ (m * E) := by
    induction m with
    | zero => simp [expSpec]
    | succ m' ih' =>
      simp only [expSpec]
      have hlt' := expSpec_lt hE x m'
      cases hx : x.testBit m' with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.or_zero]
        exact lt_of_lt_of_le ih' (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right E (Nat.le_succ m')))
      | true =>
        simp only [↓reduceIte]
        rw [or_eq_add_of_lt hlt', one_mul, Nat.add_mul, Nat.succ_mul, pow_add]
        have hpow : 1 ≤ 2 ^ E := Nat.one_le_two_pow
        have hmul : 2 ^ (m' * E) * (2 ^ E - 1) + 2 ^ (m' * E) = 2 ^ (m' * E) * 2 ^ E := by
          have : (2 ^ E - 1) + 1 = 2 ^ E := by omega
          calc 2 ^ (m' * E) * (2 ^ E - 1) + 2 ^ (m' * E)
              = 2 ^ (m' * E) * ((2 ^ E - 1) + 1) := by ring
            _ = 2 ^ (m' * E) * 2 ^ E := by rw [this]
        omega
  exact lt_of_le_of_lt (Nat.mul_le_mul_left _ (by omega)) hbound

theorem expSpec_mul_testBit {E : ℕ} (hE : 0 < E) (x eb : ℕ) (heb : eb < 2 ^ E) :
    ∀ m d e, d < m → e < E →
      (expSpec E x m * eb).testBit (d * E + e) = (x.testBit d && eb.testBit e) := by
  intro m
  induction m with
  | zero => intro d _ hd; omega
  | succ m ih =>
    have hlt_mul : expSpec E x m * eb < 2 ^ (m * E) := expSpec_mul_lt hE x eb heb m
    intro d e hd he
    simp only [expSpec]
    have hlt_exp := expSpec_lt hE x m
    cases hx : x.testBit m with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.or_zero]
      by_cases hdm : d < m
      · exact ih d e hdm he
      · have hdeq : d = m := by omega
        subst hdeq
        rw [hx, Bool.false_and]
        exact testBit_lt_of_lt hlt_mul (by omega)
    | true =>
      simp only [↓reduceIte]
      rw [or_eq_add_of_lt hlt_exp, one_mul, Nat.add_mul, Nat.mul_comm (2 ^ (m * E)) eb,
        ← or_eq_add_of_lt hlt_mul, Nat.testBit_or, Nat.testBit_shiftLeft]
      by_cases hdm : d < m
      · have hlt_pos : d * E + e < m * E := by
          have : (d + 1) * E ≤ m * E := Nat.mul_le_mul_right E (by omega)
          rw [Nat.succ_mul] at this; omega
        rw [ih d e hdm he, decide_eq_false (by omega), Bool.false_and, Bool.or_false]
      · have hdeq : d = m := by omega
        subst d
        rw [testBit_lt_of_lt hlt_mul (by omega), Bool.false_or, decide_eq_true (by omega),
          Bool.true_and, show m * E + e - m * E = e by omega, hx, Bool.true_and]

def sepSpec (M E w : ℕ) : ℕ :=
  let mMask := (1 <<< M) - 1
  expSpec E (mMask ^^^ (w &&& mMask)) M * (w >>> M)

theorem sepSpec_lt {M E w : ℕ} (hE : 0 < E) (hw : w < 2 ^ (M + E)) :
    sepSpec M E w < 2 ^ (M * E) := by
  unfold sepSpec
  apply expSpec_mul_lt hE
  rw [Nat.shiftRight_eq_div_pow]
  rw [pow_add] at hw
  exact Nat.div_lt_of_lt_mul hw

theorem sepSpec_testBit {M E w : ℕ} (hE : 0 < E) (hw : w < 2 ^ (M + E)) (d e : ℕ)
    (hd : d < M) (he : e < E) :
    (sepSpec M E w).testBit (d * E + e) = (!w.testBit d && w.testBit (M + e)) := by
  unfold sepSpec
  have heb : w >>> M < 2 ^ E := by
    rw [Nat.shiftRight_eq_div_pow]; rw [pow_add] at hw
    exact Nat.div_lt_of_lt_mul hw
  rw [expSpec_mul_testBit hE _ _ heb M d e hd he]
  rw [Nat.testBit_xor, Nat.testBit_and, testBit_mMask, decide_eq_true hd,
    Nat.testBit_shiftRight, Bool.and_true]
  cases w.testBit d <;> simp

-- Checked by decide +kernel over all 54 valid (M, E) pairs and 16 nibbles!
theorem expTab_ok : ∀ E < 10, (E == 3 || E == 5 || E == 6 || E == 7 || E == 8 || E == 9) = true →
    ∀ k < 16, ((expTab E >>> (4 * E * k)) &&& ((1 <<< (4 * E)) - 1)) = expSpec E k 4 := by
  decide +kernel

theorem loCol_ok : ∀ M < 10, ∀ E < 10, validME M E = true →
    ((1 <<< (M * E)) - 1) / ((1 <<< E) - 1) = expSpec E ((1 <<< M) - 1) M := by
  decide +kernel

theorem sepFast_eq_sepSpec {M E w : ℕ} (hME : validME M E = true) :
    sepFast M E ((1 <<< M) - 1) (expTab E) (4 * E) ((1 <<< (4 * E)) - 1) w = sepSpec M E w := by
  have hME' := hME
  simp only [validME, Bool.and_eq_true, decide_eq_true_eq] at hME'
  obtain ⟨⟨hM1, hM9⟩, hEvalid⟩ := hME'
  have hEpos : 0 < E := by
    simp only [Bool.or_eq_true, beq_iff_eq] at hEvalid
    rcases hEvalid with ((((rfl | rfl) | rfl) | rfl) | rfl) | rfl <;> omega
  have hE10 : E < 10 := by
    simp only [Bool.or_eq_true, beq_iff_eq] at hEvalid
    rcases hEvalid with ((((rfl | rfl) | rfl) | rfl) | rfl) | rfl <;> omega
  unfold sepFast sepSpec
  dsimp only
  congr 1
  set inv := ((1 <<< M) - 1) ^^^ (w &&& ((1 <<< M) - 1))
  have hinv_lt : inv < 2 ^ M := by
    apply lt_two_pow_of_testBit_false
    intro j hj
    simp only [inv, Nat.testBit_xor, Nat.testBit_and, testBit_mMask, decide_eq_false (by omega : ¬ j < M)]
    simp
  have hlo : (expTab E >>> (4 * E * (inv &&& 15))) &&& ((1 <<< (4 * E)) - 1) = expSpec E (inv &&& 15) 4 :=
    expTab_ok E hE10 hEvalid (inv &&& 15) (lt_of_le_of_lt Nat.and_le_right (by omega))
  have hhi : (expTab E >>> (4 * E * ((inv >>> 4) &&& 15))) &&& ((1 <<< (4 * E)) - 1) =
      expSpec E ((inv >>> 4) &&& 15) 4 :=
    expTab_ok E hE10 hEvalid ((inv >>> 4) &&& 15) (lt_of_le_of_lt Nat.and_le_right (by omega))
  rw [hlo, hhi]
  apply Nat.eq_of_testBit_eq
  intro p
  rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_shiftLeft, expSpec_testBit hEpos, expSpec_testBit hEpos,
    expSpec_testBit hEpos]
  have hinv_ge : ∀ j, M ≤ j → inv.testBit j = false := fun j hj => testBit_lt_of_lt hinv_lt hj
  have h15 : ∀ k, (15 : ℕ).testBit k = decide (k < 4) := by
    intro k; have : (15 : ℕ) = 2 ^ 4 - 1 := rfl; rw [this, Nat.testBit_two_pow_sub_one]
  by_cases hmod : p % E = 0
  · set q := p / E
    have hp : p = q * E := by
      have := Nat.div_add_mod p E; rw [hmod, Nat.add_zero, Nat.mul_comm] at this; exact this.symm
    have hq4 : (p - 4 * E) / E = q - 4 := by
      by_cases h4 : 4 * E ≤ p
      · have : p - 4 * E = (q - 4) * E := by rw [hp, Nat.sub_mul]
        rw [this, Nat.mul_div_cancel _ hEpos]
      · have hqlt : q < 4 := by
          by_contra hge
          exact h4 (by rw [hp]; exact Nat.mul_le_mul_right E (by omega))
        rw [Nat.sub_eq_zero_of_le (by omega), Nat.sub_eq_zero_of_le (by omega), Nat.zero_div]
    have hmod4 : 4 * E ≤ p → (p - 4 * E) % E = 0 := by
      intro h4; rw [hp, ← Nat.sub_mul]; exact Nat.mul_mod_left _ _
    by_cases hq_lt4 : q < 4
    · have h4p : ¬ 4 * E ≤ p := by rw [hp]; exact Nat.not_le.2 (Nat.mul_lt_mul_of_pos_right hq_lt4 hEpos)
      have h8p : ¬ 8 * E ≤ p := by rw [hp]; exact Nat.not_le.2 (Nat.mul_lt_mul_of_pos_right (by omega) hEpos)
      have htop : (match Nat.ble 256 inv with | true => 1 <<< (8 * E) | false => 0).testBit p = false := by
        cases Nat.ble 256 inv <;> simp [Nat.testBit_shiftLeft, h8p]
      rw [htop, Bool.or_false, decide_eq_false h4p, Bool.false_and, Bool.or_false]
      simp only [q, hmod, hq_lt4, Nat.testBit_and, h15, true_and, decide_true, Bool.and_true]
      by_cases hqM : p / E < M
      · simp [hqM]
      · simp [hqM, hinv_ge (p / E) (by omega)]
    · by_cases hq_lt8 : q < 8
      · have h4p : 4 * E ≤ p := by rw [hp]; exact Nat.mul_le_mul_right E (by omega)
        have h8p : ¬ 8 * E ≤ p := by rw [hp]; exact Nat.not_le.2 (Nat.mul_lt_mul_of_pos_right (by omega) hEpos)
        have htop : (match Nat.ble 256 inv with | true => 1 <<< (8 * E) | false => 0).testBit p = false := by
          cases Nat.ble 256 inv <;> simp [Nat.testBit_shiftLeft, h8p]
        have h1f : decide (p / E < 4 ∧ p % E = 0 ∧ (inv &&& 15).testBit (p / E) = true) = false :=
          decide_eq_false (by omega)
        rw [htop, Bool.or_false, h1f, Bool.false_or,
          decide_eq_true h4p, Bool.true_and, hq4, hmod4 h4p]
        simp only [Nat.testBit_and, Nat.testBit_shiftRight, h15,
          show q - 4 < 4 by omega, show 4 + (q - 4) = q by omega, true_and, decide_true, Bool.and_true]
        by_cases hqM : q < M
        · simp [q, hmod, hqM]
        · simp [q, hmod, hqM, hinv_ge q (by omega)]
      · by_cases hq8 : q = 8
        · have h4p : 4 * E ≤ p := by rw [hp]; exact Nat.mul_le_mul_right E (by omega)
          have h8p : p = 8 * E := by rw [hp, hq8]
          have h1 : decide (p / E < 4 ∧ p % E = 0 ∧ (inv &&& 15).testBit (p / E) = true) = false :=
            decide_eq_false (by omega)
          have h2 : decide ((p - 4 * E) / E < 4 ∧ (p - 4 * E) % E = 0 ∧
              ((inv >>> 4) &&& 15).testBit ((p - 4 * E) / E) = true) = false :=
            decide_eq_false (by omega)
          rw [h1, h2, Bool.and_false, Bool.or_false, Bool.false_or]
          have h256 : Nat.ble 256 inv = inv.testBit 8 := by
            have hinv512 : inv < 512 := lt_of_lt_of_le hinv_lt (Nat.pow_le_pow_right (by omega) hM9)
            have hall : ∀ x < 512, Nat.ble 256 x = x.testBit 8 := by decide +kernel
            exact hall inv hinv512
          rw [h256]
          by_cases h8M : 8 < M
          · cases h8 : inv.testBit 8 <;> simp [h8p, hq8, q, h8M, h8, Nat.testBit_shiftLeft]
          · have h8f : inv.testBit 8 = false := hinv_ge 8 (by omega)
            simp [h8f, q, hq8, h8M]
        · have hgt8 : 8 < q := by omega
          have h1 : decide (p / E < 4 ∧ p % E = 0 ∧ (inv &&& 15).testBit (p / E) = true) = false :=
            decide_eq_false (by omega)
          have h2 : decide ((p - 4 * E) / E < 4 ∧ (p - 4 * E) % E = 0 ∧
              ((inv >>> 4) &&& 15).testBit ((p - 4 * E) / E) = true) = false :=
            decide_eq_false (by omega)
          have h3 : decide (p / E < M ∧ p % E = 0 ∧ inv.testBit (p / E) = true) = false :=
            decide_eq_false (by omega)
          have htop : (match Nat.ble 256 inv with | true => 1 <<< (8 * E) | false => 0).testBit p = false := by
            have hgt : 8 * E < p := by rw [hp]; exact Nat.mul_lt_mul_of_pos_right hgt8 hEpos
            cases Nat.ble 256 inv with
            | false => exact Nat.zero_testBit p
            | true =>
              rw [Nat.testBit_shiftLeft]
              cases hk : p - 8 * E with
              | zero => omega
              | succ k => simp [Nat.testBit_succ]
          rw [h1, h2, h3, htop]; simp
  · have hmod4 : 4 * E ≤ p → (p - 4 * E) % E ≠ 0 := by
      intro h4 h0
      have : p % E = 0 := by
        have hmul : (p - 4 * E + 4 * E) % E = (p - 4 * E) % E := by
          have := Nat.add_mul_mod_self_right (p - 4 * E) 4 E
          simp [Nat.mul_comm]
        rw [Nat.sub_add_cancel h4] at hmul; omega
      exact hmod this
    have htop : (match Nat.ble 256 inv with | true => 1 <<< (8 * E) | false => 0).testBit p = false := by
      have hne : p ≠ 8 * E := by intro e; subst e; exact hmod (Nat.mul_mod_left 8 E)
      cases Nat.ble 256 inv with
      | false => exact Nat.zero_testBit p
      | true =>
        rw [Nat.testBit_shiftLeft]
        by_cases hge : 8 * E ≤ p
        · cases hk : p - 8 * E with
          | zero => omega
          | succ k => simp [Nat.testBit_succ]
        · simp [hge]
    rw [htop, Bool.or_false]
    have h1 : decide (p / E < 4 ∧ p % E = 0 ∧ (inv &&& 15).testBit (p / E) = true) = false :=
      decide_eq_false (fun h => hmod h.2.1)
    have h3 : decide (p / E < M ∧ p % E = 0 ∧ inv.testBit (p / E) = true) = false :=
      decide_eq_false (fun h => hmod h.2.1)
    rw [h1, h3, Bool.false_or]
    by_cases h4 : 4 * E ≤ p
    · rw [decide_eq_true h4, Bool.true_and, decide_eq_false (fun h => hmod4 h4 h.2.1)]
    · rw [decide_eq_false h4, Bool.false_and]

theorem scand_eq_sepSpec {M E a b : ℕ} (hME : validME M E = true)
    (ha : a < 2 ^ (M + E)) (hb : b < 2 ^ (M + E)) :
    let loCol := ((1 <<< (M * E)) - 1) / ((1 <<< E) - 1)
    ((sepSpec M E a ||| sepSpec M E b) &&& (((a &&& b) >>> M) * loCol)) = sepSpec M E (a &&& b) := by
  have hME' := hME
  simp only [validME, Bool.and_eq_true, decide_eq_true_eq] at hME'
  obtain ⟨⟨hM1, hM9⟩, hEvalid⟩ := hME'
  have hEpos : 0 < E := by
    simp only [Bool.or_eq_true, beq_iff_eq] at hEvalid
    rcases hEvalid with ((((rfl | rfl) | rfl) | rfl) | rfl) | rfl <;> omega
  have hE10 : E < 10 := by
    simp only [Bool.or_eq_true, beq_iff_eq] at hEvalid
    rcases hEvalid with ((((rfl | rfl) | rfl) | rfl) | rfl) | rfl <;> omega
  dsimp only
  rw [loCol_ok M (by omega) E hE10 hME]
  have hab : a &&& b < 2 ^ (M + E) := and_lt_pow ha
  have heb : (a &&& b) >>> M < 2 ^ E := by
    rw [Nat.shiftRight_eq_div_pow]; rw [pow_add] at hab
    exact Nat.div_lt_of_lt_mul hab
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < M * E
  · set d := p / E
    set e := p % E
    have hd : d < M := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    have he : e < E := Nat.mod_lt p hEpos
    have hpeq : p = d * E + e := by have := Nat.div_add_mod p E; rw [Nat.mul_comm] at this; exact this.symm
    rw [hpeq, Nat.testBit_and, Nat.testBit_or, sepSpec_testBit hEpos ha d e hd he,
      sepSpec_testBit hEpos hb d e hd he, sepSpec_testBit hEpos hab d e hd he,
      Nat.mul_comm _ (expSpec _ _ _), expSpec_mul_testBit hEpos _ _ heb M d e hd he,
      testBit_mMask, decide_eq_true hd, Bool.true_and, Nat.testBit_shiftRight, Nat.testBit_and,
      Nat.testBit_and]
    cases a.testBit d <;> cases b.testBit d <;> cases a.testBit (M + e) <;> cases b.testBit (M + e) <;> rfl
  · have hlt1 := sepSpec_lt hEpos ha
    have hlt2 := sepSpec_lt hEpos hb
    have hlt3 := sepSpec_lt hEpos hab
    rw [Nat.testBit_and, Nat.testBit_or, testBit_lt_of_lt hlt1 (by omega),
      testBit_lt_of_lt hlt2 (by omega), testBit_lt_of_lt hlt3 (by omega)]; rfl

/-! ## Section 2e: listC1 / listC2, rowSm / colSm, and v6 soundness -/

def listC1 : List ℕ → ℕ
  | [] => 0
  | x :: t => x ||| listC1 t

def listC2 : List ℕ → ℕ
  | [] => 0
  | x :: t => listC2 t ||| (x &&& listC1 t)

theorem listC1_append (l1 l2 : List ℕ) : listC1 (l1 ++ l2) = listC1 l1 ||| listC1 l2 := by
  induction l1 with
  | nil => simp [listC1]
  | cons a t ih => simp [listC1, ih, Nat.or_assoc]

theorem listC2_append (l1 l2 : List ℕ) :
    listC2 (l1 ++ l2) = listC2 l1 ||| listC2 l2 ||| (listC1 l1 &&& listC1 l2) := by
  induction l1 with
  | nil => simp [listC1, listC2]
  | cons a t ih =>
    apply Nat.eq_of_testBit_eq; intro p
    simp only [List.cons_append, listC1, listC2, ih, listC1_append, Nat.testBit_or, Nat.testBit_and]
    cases a.testBit p <;> cases (listC1 t).testBit p <;> cases (listC1 l2).testBit p <;>
      cases (listC2 t).testBit p <;> cases (listC2 l2).testBit p <;> rfl

theorem listC1_perm {l1 l2 : List ℕ} (h : l1.Perm l2) : listC1 l1 = listC1 l2 := by
  induction h with
  | nil => rfl
  | cons a _ ih => simp [listC1, ih]
  | swap a b t =>
    apply Nat.eq_of_testBit_eq; intro p
    simp only [listC1, Nat.testBit_or]; cases a.testBit p <;> cases b.testBit p <;> cases (listC1 t).testBit p <;> rfl
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem listC2_perm {l1 l2 : List ℕ} (h : l1.Perm l2) : listC2 l1 = listC2 l2 := by
  induction h with
  | nil => rfl
  | cons a hp ih => simp [listC2, ih, listC1_perm hp]
  | swap a b t =>
    apply Nat.eq_of_testBit_eq; intro p
    simp only [listC1, listC2, Nat.testBit_or, Nat.testBit_and]
    cases a.testBit p <;> cases b.testBit p <;> cases (listC1 t).testBit p <;> cases (listC2 t).testBit p <;> rfl
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem listC1_testBit (l : List ℕ) (p : ℕ) :
    (listC1 l).testBit p = true ↔ ∃ x ∈ l, x.testBit p = true := by
  induction l with
  | nil => simp [listC1]
  | cons a t ih => simp [listC1, ih]

theorem listC2_testBit_false : ∀ (l : List ℕ) (p : ℕ),
    (listC2 l).testBit p = false →
    ∀ i j (hi : i < l.length) (hj : j < l.length),
      l[i].testBit p = true → l[j].testBit p = true → i = j
  | [], _, _, _, _, hi, _, _, _ => by simp at hi
  | a :: t, p, h, i, j, hi, hj, hti, htj => by
    simp only [listC2, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at h
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j' =>
        simp only [List.getElem_cons_zero] at hti
        simp only [List.getElem_cons_succ] at htj
        have hj' : j' < t.length := by simp at hj; omega
        have hmem : (listC1 t).testBit p = true :=
          (listC1_testBit t p).2 ⟨t[j'], List.getElem_mem hj', htj⟩
        rcases h.2 with ha | ht
        · rw [hti] at ha; exact Bool.noConfusion ha
        · rw [hmem] at ht; exact Bool.noConfusion ht
    | succ i' =>
      cases j with
      | zero =>
        simp only [List.getElem_cons_succ] at hti
        simp only [List.getElem_cons_zero] at htj
        have hi' : i' < t.length := by simp at hi; omega
        have hmem : (listC1 t).testBit p = true :=
          (listC1_testBit t p).2 ⟨t[i'], List.getElem_mem hi', hti⟩
        rcases h.2 with ha | ht
        · rw [htj] at ha; exact Bool.noConfusion ha
        · rw [hmem] at ht; exact Bool.noConfusion ht
      | succ j' =>
        simp only [List.getElem_cons_succ] at hti htj
        congr 1
        exact listC2_testBit_false t p h.1 i' j' (by simp at hi; omega) (by simp at hj; omega) hti htj

theorem dlive_listC1_full {M E k : ℕ} {ws : List ℕ} (hME : validME M E = true)
    (hlt : ∀ w ∈ ws, w < 2 ^ (M + E)) (h : DLive M E k ws.toFinset) :
    listC1 (ws.map (sepSpec M E)) = (1 <<< (M * E)) - 1 := by
  obtain ⟨hM1, hM9, hE2, hE10, _⟩ := validME_props hME
  have hEpos : 0 < E := by omega
  apply Nat.eq_of_testBit_eq
  intro p
  rw [testBit_mMask]
  by_cases hp : p < M * E
  · rw [decide_eq_true hp]
    apply (listC1_testBit _ p).2
    set d := p / E
    set e := p % E
    have hd : d < M := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    have he : e < E := Nat.mod_lt p hEpos
    have hpeq : p = d * E + e := by have := Nat.div_add_mod p E; rw [Nat.mul_comm] at this; exact this.symm
    have hne : ¬ (goalME M E).testBit (M + e) ≤ (goalME M E).testBit d := by
      rw [testBit_goalME, testBit_goalME]
      simp [show M ≤ M + e by omega, show M + e < M + E by omega, show ¬ M ≤ d by omega]
    have hex : ∃ w ∈ ws, w.testBit d = false ∧ w.testBit (M + e) = true := by
      by_contra hall
      push Not at hall
      apply hne
      apply dlive_bits_le h (M + e) d
      intro w hw
      have hw' := hall w (List.mem_toFinset.1 hw)
      cases hwd : w.testBit d <;> cases hwe : w.testBit (M + e) <;> simp_all
    obtain ⟨w, hw, hwd, hwe⟩ := hex
    refine ⟨sepSpec M E w, List.mem_map.2 ⟨w, hw, rfl⟩, ?_⟩
    rw [hpeq, sepSpec_testBit hEpos (hlt w hw) d e hd he, hwd, hwe]; rfl
  · rw [decide_eq_false hp]
    apply Bool.eq_false_iff.2
    intro ht
    obtain ⟨_, hw, hpt⟩ := (listC1_testBit _ p).1 ht
    obtain ⟨w, hwm, rfl⟩ := List.mem_map.1 hw
    rw [testBit_lt_of_lt (sepSpec_lt hEpos (hlt w hwm)) (by omega)] at hpt
    exact Bool.noConfusion hpt

-- Carry-trick row-smear soundness (one direction: bit (d*E + a) true -> exists b < E with u.testBit (d*E + b) = true)
theorem rHi_spec {E : ℕ} (hE : 2 ≤ E) :
    ∀ (m u : ℕ), u < 2 ^ (m * E) →
      let full := (1 <<< (m * E)) - 1
      let loCol := expSpec E ((1 <<< m) - 1) m
      let hiCol := loCol <<< (E - 1)
      let loK := full ^^^ hiCol
      let rHi := (((u &&& loK) + loK) ||| u) &&& hiCol
      ∀ d < m, rHi.testBit (d * E + (E - 1)) = true → ∃ b < E, u.testBit (d * E + b) = true := by
  intro m
  induction m with
  | zero => intro _ _ d hd; omega
  | succ m ih =>
    intro u hu
    dsimp only
    set E1 := E - 1
    set K0 := 2 ^ E1 - 1
    -- Split u = u0 + 2^E * u1 with u0 < 2^E, u1 < 2^(m * E)
    set u0 := u % 2 ^ E
    set u1 := u / 2 ^ E
    have hu0_lt : u0 < 2 ^ E := Nat.mod_lt u (Nat.two_pow_pos E)
    have hu1_lt : u1 < 2 ^ (m * E) := by
      have : (m + 1) * E = E + m * E := by rw [Nat.succ_mul, Nat.add_comm]
      rw [this, pow_add] at hu
      exact Nat.div_lt_of_lt_mul hu
    have hu_split : u = u0 + u1 * 2 ^ E := by
      have hdm := Nat.div_add_mod u (2 ^ E); simp only [u0, u1]; rw [Nat.mul_comm]; omega
    -- Express hiCol(m+1) and loK(m+1) in terms of low E bits and shifted hiCol(m), loK(m)!
    set loCol_m := expSpec E ((1 <<< m) - 1) m
    set hiCol_m := loCol_m <<< E1
    set full_m := (1 <<< (m * E)) - 1
    set loK_m := full_m ^^^ hiCol_m
    set loCol_s := expSpec E ((1 <<< (m + 1)) - 1) (m + 1)
    set hiCol_s := loCol_s <<< E1
    set full_s := (1 <<< ((m + 1) * E)) - 1
    set loK_s := full_s ^^^ hiCol_s
    have hEpos : 0 < E := by omega
    have hhi_shift : hiCol_s = 2 ^ E1 + hiCol_m * 2 ^ E := by
      rw [← or_eq_add_of_lt (Nat.pow_lt_pow_right (by omega) (show E1 < E by omega))]
      apply Nat.eq_of_testBit_eq; intro p
      rw [Nat.testBit_or, Nat.testBit_shiftLeft]
      simp only [hiCol_s, hiCol_m, loCol_s, loCol_m, Nat.testBit_shiftLeft,
        expSpec_testBit hEpos]
      by_cases hpE : p < E
      · have hnot : ¬ E ≤ p := by omega
        rw [decide_eq_false hnot, Bool.false_and, Bool.or_false]
        by_cases hpe1 : p = E1
        · subst hpe1
          have h0 : ((1 <<< (m + 1)) - 1).testBit 0 = true := by rw [testBit_mMask]; simp
          simp [E1, h0, Nat.testBit_two_pow_self]
        · have hne : (2 ^ E1).testBit p = false := by
            rw [Nat.testBit_two_pow]; exact decide_eq_false (Ne.symm hpe1)
          rw [hne]
          by_cases hge : E1 ≤ p
          · have hlt_sub : p - E1 < E := by omega
            have hmod : (p - E1) % E ≠ 0 := by
              rw [Nat.mod_eq_of_lt hlt_sub]; omega
            simp [hge, hmod]
          · simp [hge]
      · have hge : E ≤ p := by omega
        have hlt2 : (2 ^ E1).testBit p = false :=
          testBit_lt_of_lt (Nat.pow_lt_pow_right (by omega) (show E1 < E by omega)) hge
        rw [hlt2, Bool.false_or, decide_eq_true hge, Bool.true_and]
        have hge1 : E1 ≤ p := by omega
        rw [decide_eq_true hge1, Bool.true_and]
        by_cases hge2 : E1 ≤ p - E
        · rw [decide_eq_true hge2, Bool.true_and]
          have hsub : p - E - E1 = (p - E1) - E := by omega
          rw [hsub]
          have hadd : (p - E1 - E) + E = p - E1 := by omega
          have hdiv1 : (p - E1) / E = (p - E1 - E) / E + 1 := by
            have h1 := Nat.add_div_right (p - E1 - E) hEpos
            rwa [hadd] at h1
          have hdiv : (p - E1 - E) / E = (p - E1) / E - 1 := by rw [hdiv1, Nat.add_sub_cancel]
          have hmod : (p - E1 - E) % E = (p - E1) % E := by
            have h1 := Nat.add_mod_right (p - E1 - E) E
            rw [hadd] at h1; exact h1.symm
          have hpos_q : 1 ≤ (p - E1) / E := by rw [hdiv1]; omega
          rw [hdiv, hmod, testBit_mMask, testBit_mMask]
          by_cases hltm : (p - E1) / E - 1 < m <;>
            simp [hltm, show (p - E1) / E < m + 1 ↔ (p - E1) / E - 1 < m by omega]
        · rw [decide_eq_false hge2, Bool.false_and]
          have hlt_sub : p - E1 < E := by omega
          have hpos_sub : 0 < p - E1 := by omega
          have hmod : (p - E1) % E ≠ 0 := by rw [Nat.mod_eq_of_lt hlt_sub]; omega
          simp [hmod]
    have hloK_shift : loK_s = K0 + loK_m * 2 ^ E := by
      have hK0_lt : K0 < 2 ^ E := by
        have : 2 ^ E1 < 2 ^ E := Nat.pow_lt_pow_right (by omega) (by omega); omega
      rw [← or_eq_add_of_lt hK0_lt]
      apply Nat.eq_of_testBit_eq; intro p
      simp only [loK_s, loK_m, full_s, full_m, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft,
        testBit_mMask, hhi_shift, ← or_eq_add_of_lt (Nat.pow_lt_pow_right (by omega) (show E1 < E by omega))]
      by_cases hpE : p < E
      · have hnot : ¬ E ≤ p := by omega
        have hK0_bit : K0.testBit p = decide (p < E1) := Nat.testBit_two_pow_sub_one E1 p
        have h2e1 : (2 ^ E1).testBit p = decide (E1 = p) := Nat.testBit_two_pow
        have hp_lt_s : p < (m + 1) * E := by rw [Nat.succ_mul]; omega
        simp only [decide_eq_false hnot, Bool.false_and, Bool.or_false, decide_eq_true hp_lt_s,
          hK0_bit, h2e1]
        by_cases hpe1 : p < E1
        · simp [hpe1, show E1 ≠ p by omega]
        · have : E1 = p := by omega
          simp [hpe1, this]
      · have hge : E ≤ p := by omega
        have hK0_f : K0.testBit p = false := testBit_lt_of_lt hK0_lt hge
        have h2e1_f : (2 ^ E1).testBit p = false :=
          testBit_lt_of_lt (Nat.pow_lt_pow_right (by omega) (show E1 < E by omega)) hge
        rw [hK0_f, h2e1_f, Bool.false_or, Bool.false_or, decide_eq_true hge, Bool.true_and]
        have hlt_iff : p < (m + 1) * E ↔ p - E < m * E := by rw [Nat.succ_mul]; omega
        simp [hlt_iff]
    -- Now split (u &&& loK_s) + loK_s with ZERO carry across bit E!
    have hand_split : u &&& loK_s = (u0 &&& K0) + (u1 &&& loK_m) * 2 ^ E := by
      have hK0_lt : K0 < 2 ^ E := by
        have : 2 ^ E1 < 2 ^ E := Nat.pow_lt_pow_right (by omega) (by omega); omega
      have h1 : u0 &&& K0 < 2 ^ E := lt_of_le_of_lt Nat.and_le_left hu0_lt
      rw [hu_split, hloK_shift, ← or_eq_add_of_lt hu0_lt, ← or_eq_add_of_lt hK0_lt, ← or_eq_add_of_lt h1]
      apply Nat.eq_of_testBit_eq; intro p
      simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft]
      by_cases hpE : p < E
      · simp [show ¬ E ≤ p by omega]
      · have hge : E ≤ p := by omega
        have hb1 : u0.testBit p = false := testBit_lt_of_lt hu0_lt hge
        have hb2 : K0.testBit p = false := testBit_lt_of_lt hK0_lt hge
        have hb3 : (u0 &&& K0).testBit p = false := testBit_lt_of_lt h1 hge
        simp [hb1, hb2, hb3, hge]
    have hlow_noc : (u0 &&& K0) + K0 < 2 ^ E := by
      have h1 : u0 &&& K0 ≤ K0 := Nat.and_le_right
      have h2 : 2 ^ E = 2 * 2 ^ E1 := by
        rw [show E = E1 + 1 by omega, pow_succ']
      have h3 : 1 ≤ 2 ^ E1 := Nat.one_le_two_pow
      omega
    have hsum_split : (u &&& loK_s) + loK_s = ((u0 &&& K0) + K0) + ((u1 &&& loK_m) + loK_m) * 2 ^ E := by
      rw [hand_split, hloK_shift]; ring
    have hrHi_split : (((u &&& loK_s) + loK_s) ||| u) &&& hiCol_s =
        ((((u0 &&& K0) + K0) ||| u0) &&& 2 ^ E1) +
        ((((u1 &&& loK_m) + loK_m) ||| u1) &&& hiCol_m) * 2 ^ E := by
      have hlow_lt : (((u0 &&& K0) + K0) ||| u0) &&& 2 ^ E1 < 2 ^ E :=
        lt_of_le_of_lt Nat.and_le_right (Nat.pow_lt_pow_right (by omega) (by omega))
      rw [hsum_split, hu_split, hhi_shift,
        ← or_eq_add_of_lt hlow_noc, ← or_eq_add_of_lt hu0_lt,
        ← or_eq_add_of_lt (Nat.pow_lt_pow_right (by omega) (show E1 < E by omega)),
        ← or_eq_add_of_lt hlow_lt]
      apply Nat.eq_of_testBit_eq; intro p
      simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft]
      by_cases hpE : p < E
      · simp [show ¬ E ≤ p by omega]
      · have hge : E ≤ p := by omega
        have hb1 : ((u0 &&& K0) + K0).testBit p = false := testBit_lt_of_lt hlow_noc hge
        have hb2 : u0.testBit p = false := testBit_lt_of_lt hu0_lt hge
        have hb3 : (2 ^ E1).testBit p = false :=
          testBit_lt_of_lt (Nat.pow_lt_pow_right (by omega) (show E1 < E by omega)) hge
        have hb4 : ((((u0 &&& K0) + K0) ||| u0) &&& 2 ^ E1).testBit p = false := testBit_lt_of_lt hlow_lt hge
        simp [hb1, hb2, hb3, hb4, hge]
    intro d hd hbit
    rw [hrHi_split, ← or_eq_add_of_lt (lt_of_le_of_lt Nat.and_le_right (Nat.pow_lt_pow_right (by omega) (show E1 < E by omega)))] at hbit
    cases d with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, Nat.testBit_or, Nat.testBit_shiftLeft,
        show ¬ E ≤ E1 by omega, decide_false, Bool.false_and, Bool.or_false] at hbit
      have hu0_ne : u0 ≠ 0 := by
        intro h0
        rw [h0] at hbit
        simp only [K0, Nat.zero_and, Nat.zero_add, Nat.or_zero, Nat.testBit_and,
          Nat.testBit_two_pow_sub_one, lt_irrefl, decide_false, Bool.false_and] at hbit
        exact Bool.noConfusion hbit
      have hex : ∃ b < E, u0.testBit b = true := by
        by_contra hall; push Not at hall
        apply hu0_ne
        apply Nat.eq_of_testBit_eq; intro k
        rw [Nat.zero_testBit]
        by_cases hk : k < E
        · exact Bool.eq_false_iff.2 (hall k hk)
        · exact testBit_lt_of_lt hu0_lt (by omega)
      obtain ⟨b, hb, hbt⟩ := hex
      refine ⟨b, hb, ?_⟩
      rw [Nat.zero_mul, Nat.zero_add, hu_split, ← or_eq_add_of_lt hu0_lt, Nat.testBit_or, hbt]; rfl
    | succ d' =>
      have hgeE : E ≤ (d' + 1) * E + E1 := by rw [Nat.succ_mul]; omega
      have hlow_f : ((((u0 &&& K0) + K0) ||| u0) &&& 2 ^ E1).testBit ((d' + 1) * E + E1) = false :=
        testBit_lt_of_lt (lt_of_le_of_lt Nat.and_le_right (Nat.pow_lt_pow_right (by omega) (show E1 < E by omega))) hgeE
      rw [Nat.testBit_or, hlow_f, Bool.false_or, Nat.testBit_shiftLeft, decide_eq_true hgeE,
        Bool.true_and, show (d' + 1) * E + E1 - E = d' * E + E1 by rw [Nat.succ_mul]; omega] at hbit
      obtain ⟨b, hb, hbt⟩ := ih u1 hu1_lt d' (by omega) hbit
      refine ⟨b, hb, ?_⟩
      rw [hu_split, ← or_eq_add_of_lt hu0_lt, Nat.testBit_or, Nat.testBit_shiftLeft,
        decide_eq_true (by rw [Nat.succ_mul]; omega), Bool.true_and,
        show (d' + 1) * E + b - E = d' * E + b by rw [Nat.succ_mul]; omega, hbt, Bool.or_true]

theorem rowSm_sound {M E u d a : ℕ} (hME : validME M E = true) (hu : u < 2 ^ (M * E))
    (hd : d < M) (ha : a < E) :
    let full := (1 <<< (M * E)) - 1
    let eMask := (1 <<< E) - 1
    let loCol := full / eMask
    let hiCol := loCol <<< (E - 1)
    let loK := full ^^^ hiCol
    let rHi := (((u &&& loK) + loK) ||| u) &&& hiCol
    let rowSm := (rHi >>> (E - 1)) * eMask
    rowSm.testBit (d * E + a) = true → ∃ b < E, u.testBit (d * E + b) = true := by
  obtain ⟨hM1, hM9, hE2, hE10, _⟩ := validME_props hME
  dsimp only
  rw [loCol_ok M (by omega) E hE10 hME]
  intro hrow
  -- Express (rHi >>> (E - 1)) as expSpec E rBits M!
  set loCol := expSpec E ((1 <<< M) - 1) M
  set hiCol := loCol <<< (E - 1)
  set loK := ((1 <<< (M * E)) - 1) ^^^ hiCol
  set rHi := (((u &&& loK) + loK) ||| u) &&& hiCol
  -- Define rBits via testBit: bit k of rBits = rHi.testBit (k * E + (E - 1))
  -- Actually (rHi >>> (E - 1)) = expSpec E (Nat.ofFn ...) M; even simpler, prove directly by induction on M or expSpec!
  -- Notice rHi &&& hiCol = rHi, so every 1-bit of rHi >>> (E - 1) is at a multiple of E (< M * E)!
  -- Define rBits by recursing:
  let rBits : ℕ := (List.range M).foldl (fun acc k => if rHi.testBit (k * E + (E - 1)) then acc ||| (1 <<< k) else acc) 0
  have hrBits_bit : ∀ k < M, rBits.testBit k = rHi.testBit (k * E + (E - 1)) := by
    have hfold : ∀ (l : List ℕ) (acc k : ℕ),
        ((l.foldl (fun a j => if rHi.testBit (j * E + (E - 1)) then a ||| (1 <<< j) else a) acc).testBit k = true) ↔
        (acc.testBit k = true ∨ (k ∈ l ∧ rHi.testBit (k * E + (E - 1)) = true)) := by
      intro l
      induction l with
      | nil => intro acc k; simp
      | cons j rest ih =>
        intro acc k
        simp only [List.foldl_cons, ih, List.mem_cons]
        by_cases hj : rHi.testBit (j * E + (E - 1)) = true
        · simp only [hj, ↓reduceIte, Nat.testBit_or, Bool.or_eq_true]
          have h1 : (1 <<< j).testBit k = true ↔ j = k := by
            rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow, decide_eq_true_eq]
          rw [h1]
          constructor
          · rintro ((ha | rfl) | ⟨hk, hrt⟩)
            · exact Or.inl ha
            · exact Or.inr ⟨Or.inl rfl, hj⟩
            · exact Or.inr ⟨Or.inr hk, hrt⟩
          · rintro (ha | ⟨rfl | hk, hrt⟩)
            · exact Or.inl (Or.inl ha)
            · exact Or.inl (Or.inr rfl)
            · exact Or.inr ⟨hk, hrt⟩
        · simp only [hj, ↓reduceIte]
          constructor
          · rintro (ha | ⟨hk, hrt⟩)
            · exact Or.inl ha
            · exact Or.inr ⟨Or.inr hk, hrt⟩
          · rintro (ha | ⟨rfl | hk, hrt⟩)
            · exact Or.inl ha
            · exact absurd hrt hj
            · exact Or.inr ⟨hk, hrt⟩
    intro k hk
    apply Bool.eq_iff_iff.2
    rw [hfold (List.range M) 0 k]
    simp [List.mem_range, hk]
  have hrHi_eq : rHi >>> (E - 1) = expSpec E rBits M := by
    apply Nat.eq_of_testBit_eq; intro p
    rw [Nat.testBit_shiftRight, expSpec_testBit (by omega)]
    have hle_hi : rHi.testBit ((E - 1) + p) = true → hiCol.testBit ((E - 1) + p) = true := by
      intro ht
      have h1 : (rHi &&& hiCol).testBit ((E - 1) + p) = true := by
        have : rHi &&& hiCol = rHi := by simp [rHi, Nat.and_assoc]
        rwa [this]
      rw [Nat.testBit_and, Bool.and_eq_true] at h1; exact h1.2
    apply Bool.eq_iff_iff.2
    constructor
    · intro ht
      have hhi := hle_hi ht
      have hEpos : 0 < E := by omega
      simp only [hiCol, loCol, Nat.testBit_shiftLeft,
        show E - 1 ≤ E - 1 + p by omega, decide_true, Bool.true_and,
        show E - 1 + p - (E - 1) = p by omega] at hhi
      rw [expSpec_testBit hEpos, decide_eq_true_eq] at hhi
      refine decide_eq_true ⟨hhi.1, hhi.2.1, ?_⟩
      rw [hrBits_bit (p / E) hhi.1]
      have hp : p = p / E * E := by
        have := Nat.div_add_mod p E; rw [hhi.2.1, Nat.mul_comm] at this; omega
      rwa [show p / E * E + (E - 1) = E - 1 + p by omega]
    · intro hdec
      simp only [decide_eq_true_eq] at hdec
      obtain ⟨hdiv, hmod, hrb⟩ := hdec
      rw [hrBits_bit (p / E) hdiv] at hrb
      have hp : p = p / E * E := by
        have := Nat.div_add_mod p E; rw [hmod, Nat.mul_comm] at this; omega
      rwa [show E - 1 + p = p / E * E + (E - 1) by omega]
  rw [hrHi_eq] at hrow
  have hem : (1 <<< E) - 1 < 2 ^ E := by rw [Nat.shiftLeft_eq, one_mul]; have := Nat.two_pow_pos E; omega
  rw [expSpec_mul_testBit (by omega) rBits ((1 <<< E) - 1) hem M d a hd ha,
    hrBits_bit d hd, testBit_mMask, decide_eq_true ha, Bool.and_true] at hrow
  exact rHi_spec hE2 M u hu d hd hrow

theorem colSm_sound {M E u d a : ℕ} (hME : validME M E = true) (hu : u < 2 ^ (M * E))
    (hd : d < M) (ha : a < E) :
    let eMask := (1 <<< E) - 1
    let full := (1 <<< (M * E)) - 1
    let loCol := full / eMask
    let v0 := match Nat.blt 8 M with | true => u ||| (u >>> (8 * E)) | false => u
    let v1 := v0 ||| (v0 >>> (4 * E))
    let v2 := v1 ||| (v1 >>> (2 * E))
    let v3 := (v2 ||| (v2 >>> E)) &&& eMask
    let colSm := v3 * loCol
    colSm.testBit (d * E + a) = true → ∃ f < M, u.testBit (f * E + a) = true := by
  obtain ⟨hM1, hM9, hE2, hE10, _⟩ := validME_props hME
  have hEpos : 0 < E := by omega
  dsimp only
  rw [loCol_ok M (by omega) E hE10 hME]
  intro hcol
  set v0 := match Nat.blt 8 M with | true => u ||| (u >>> (8 * E)) | false => u
  set v1 := v0 ||| (v0 >>> (4 * E))
  set v2 := v1 ||| (v1 >>> (2 * E))
  set v3 := (v2 ||| (v2 >>> E)) &&& ((1 <<< E) - 1)
  have hv3_lt : v3 < 2 ^ E := by
    apply lt_of_le_of_lt Nat.and_le_right
    rw [Nat.shiftLeft_eq, one_mul]; have := Nat.two_pow_pos E; omega
  rw [Nat.mul_comm v3 _, expSpec_mul_testBit hEpos _ v3 hv3_lt M d a hd ha,
    testBit_mMask, decide_eq_true hd, Bool.true_and] at hcol
  simp only [v3, v2, v1, Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight,
    testBit_mMask, decide_eq_true ha, Bool.and_true, Bool.or_eq_true] at hcol
  have hv0_ex : ∀ p, v0.testBit p = true → ∃ k, u.testBit (k * E + p) = true := by
    intro p hp
    cases h8 : Nat.blt 8 M with
    | false =>
      simp only [v0, h8] at hp
      exact ⟨0, by simpa using hp⟩
    | true =>
      simp only [v0, h8, Nat.testBit_or, Nat.testBit_shiftRight, Bool.or_eq_true] at hp
      rcases hp with h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨8, h⟩
  have hex_k : ∃ k, u.testBit (k * E + a) = true := by
    rcases hcol with (((h | h) | (h | h)) | ((h | h) | (h | h)))
    · obtain ⟨k, hk⟩ := hv0_ex a h; exact ⟨k, hk⟩
    · obtain ⟨k, hk⟩ := hv0_ex (4 * E + a) h; exact ⟨k + 4, by rwa [Nat.add_mul, Nat.add_assoc]⟩
    · obtain ⟨k, hk⟩ := hv0_ex (2 * E + a) h; exact ⟨k + 2, by rwa [Nat.add_mul, Nat.add_assoc]⟩
    · obtain ⟨k, hk⟩ := hv0_ex (4 * E + (2 * E + a)) h
      exact ⟨k + 6, by convert hk using 2; ring⟩
    · obtain ⟨k, hk⟩ := hv0_ex (E + a) h; exact ⟨k + 1, by convert hk using 2; ring⟩
    · obtain ⟨k, hk⟩ := hv0_ex (4 * E + (E + a)) h; exact ⟨k + 5, by convert hk using 2; ring⟩
    · obtain ⟨k, hk⟩ := hv0_ex (2 * E + (E + a)) h; exact ⟨k + 3, by convert hk using 2; ring⟩
    · obtain ⟨k, hk⟩ := hv0_ex (4 * E + (2 * E + (E + a))) h; exact ⟨k + 7, by convert hk using 2; ring⟩
  obtain ⟨k, hk⟩ := hex_k
  have hkM : k < M := by
    by_contra hge
    have h1 : M * E ≤ k * E + a := by
      have := Nat.mul_le_mul_right E (show M ≤ k by omega); omega
    rw [testBit_lt_of_lt hu h1] at hk
    exact Bool.noConfusion hk
  exact ⟨k, hkM, hk⟩

structure GCtx where
  M : ℕ
  E : ℕ
  e1 : ℕ
  e2 : ℕ
  e4 : ℕ
  e8 : ℕ
  mMask : ℕ
  eMask : ℕ
  full : ℕ
  loCol : ℕ
  hiCol : ℕ
  loK : ℕ
  tab : ℕ
  mask4 : ℕ
  bigM : Bool

def mkGCtx (M E : ℕ) : GCtx :=
  let mMask := (1 <<< M) - 1
  let eMask := (1 <<< E) - 1
  let full := (1 <<< (M * E)) - 1
  let loCol := full / eMask
  let hiCol := loCol <<< (E - 1)
  let e4 := 4 * E
  ⟨M, E, E - 1, 2 * E, e4, 8 * E, mMask, eMask, full, loCol, hiCol, full ^^^ hiCol, expTab E, (1 <<< e4) - 1, Nat.blt 8 M⟩

structure WNode where
  w : ℕ
  gw : ℕ
  sw : ℕ
  tc1 : ℕ
  tc2 : ℕ

def buildNodes (ctx : GCtx) : List ℕ → List WNode
  | [] => []
  | w :: t =>
    let rest := buildNodes ctx t
    let sw := sepFast ctx.M ctx.E ctx.mMask ctx.tab ctx.e4 ctx.mask4 w
    match rest with
    | [] => [⟨w, w ^^^ ctx.mMask, sw, 0, 0⟩]
    | h :: _ =>
      let tc1 := h.sw ||| h.tc1
      let tc2 := h.tc2 ||| (h.sw &&& h.tc1)
      ⟨w, w ^^^ ctx.mMask, sw, tc1, tc2⟩ :: rest

def anyDomBoth (gc : ℕ) : List WNode → Bool
  | [] => false
  | p :: t =>
    let m := gc &&& p.gw
    Nat.beq m gc || Nat.beq m p.gw || anyDomBoth gc t

def collectW (acc : List ℕ) : List WNode → List ℕ
  | [] => acc
  | p :: t => collectW (p.w :: acc) t

def wireQual (ctx : GCtx) (uniq sw : ℕ) : ℕ :=
  let u := sw &&& uniq
  match Nat.beq u 0 with
  | true => 0
  | false =>
    let rHi := (((u &&& ctx.loK) + ctx.loK) ||| u) &&& ctx.hiCol
    let rowSm := (rHi >>> ctx.e1) * ctx.eMask
    let v0 := match ctx.bigM with | true => u ||| (u >>> ctx.e8) | false => u
    let v1 := v0 ||| (v0 >>> ctx.e4)
    let v2 := v1 ||| (v1 >>> ctx.e2)
    let v3 := (v2 ||| (v2 >>> ctx.E)) &&& ctx.eMask
    sw &&& rowSm &&& (v3 * ctx.loCol)

theorem wireQual_bit_sound {M E uniq w p : ℕ} (hME : validME M E = true) (hw : w < 2 ^ (M + E))
    (hbit : (wireQual (mkGCtx M E) uniq (sepSpec M E w)).testBit p = true) :
    p < M * E ∧
      let d := p / E
      let a := p % E
      w.testBit d = false ∧ w.testBit (M + a) = true ∧
      (∃ b < E, (sepSpec M E w &&& uniq).testBit (d * E + b) = true) ∧
      (∃ f < M, (sepSpec M E w &&& uniq).testBit (f * E + a) = true) := by
  obtain ⟨hM1, hM9, hE2, hE10, _⟩ := validME_props hME
  have hEpos : 0 < E := by omega
  unfold wireQual at hbit
  dsimp only at hbit
  cases hu0 : Nat.beq (sepSpec M E w &&& uniq) 0 with
  | true => rw [hu0] at hbit; simp at hbit
  | false =>
    rw [hu0] at hbit
    simp only [mkGCtx, Nat.testBit_and, Bool.and_eq_true] at hbit
    obtain ⟨⟨hsw, hrow⟩, hcol⟩ := hbit
    have hp : p < M * E := by
      by_contra hge
      rw [testBit_lt_of_lt (sepSpec_lt hEpos hw) (by omega)] at hsw
      exact Bool.noConfusion hsw
    set d := p / E
    set a := p % E
    have hd : d < M := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
    have ha : a < E := Nat.mod_lt p hEpos
    have hpeq : p = d * E + a := by have := Nat.div_add_mod p E; rw [Nat.mul_comm] at this; exact this.symm
    rw [hpeq] at hsw hrow hcol
    have hlt_u : sepSpec M E w &&& uniq < 2 ^ (M * E) := and_lt_pow (sepSpec_lt hEpos hw)
    have hsw' := hsw
    rw [sepSpec_testBit hEpos hw d a hd ha, Bool.and_eq_true, Bool.not_eq_true'] at hsw'
    refine ⟨hp, hsw'.1, hsw'.2,
      rowSm_sound hME hlt_u hd ha hrow,
      colSm_sound hME hlt_u hd ha hcol⟩

-- Core v6 refutation theorem: if two distinct wires in ws share a bit in wireQual, DLive at slack=0 is impossible!
theorem v6_refute {M E k : ℕ} {ws : List ℕ} (hME : validME M E = true)
    (hnd : ws.Nodup) (hlt : ∀ w ∈ ws, w < 2 ^ (M + E))
    (hlen : ws.length = k + 1)
    (i1 i2 : ℕ) (hi1 : i1 < ws.length) (hi2 : i2 < ws.length) (hne : i1 ≠ i2)
    (p : ℕ)
    (hq1 : (wireQual (mkGCtx M E) (((1 <<< (M * E)) - 1) ^^^ listC2 (ws.map (sepSpec M E)))
              (sepSpec M E ws[i1])).testBit p = true)
    (hq2 : (wireQual (mkGCtx M E) (((1 <<< (M * E)) - 1) ^^^ listC2 (ws.map (sepSpec M E)))
              (sepSpec M E ws[i2])).testBit p = true) :
    ¬ DLive M E k ws.toFinset := by
  intro hdl
  obtain ⟨hM1, hM9, hE2, hE10, _⟩ := validME_props hME
  have hEpos : 0 < E := by omega
  set uniq := ((1 <<< (M * E)) - 1) ^^^ listC2 (ws.map (sepSpec M E))
  obtain ⟨hp, hd1, ha1, ⟨b1, hb1, hub1⟩, ⟨f1, hf1, huf1⟩⟩ :=
    wireQual_bit_sound hME (hlt _ (List.getElem_mem hi1)) hq1
  obtain ⟨_, hd2, ha2, ⟨b2, hb2, hub2⟩, ⟨f2, hf2, huf2⟩⟩ :=
    wireQual_bit_sound hME (hlt _ (List.getElem_mem hi2)) hq2
  set d := p / E
  set a := p % E
  have hdM : d < M := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
  have haE : a < E := Nat.mod_lt p hEpos
  -- Uniqueness helper: if (sepSpec M E ws[idx] &&& uniq).testBit (r*E + c) = true,
  -- then NO other index j != idx has (sepSpec M E ws[j]).testBit (r*E + c) = true!
  have huniq_idx : ∀ (idx : ℕ) (hidx : idx < ws.length) (r c : ℕ) (hr : r < M) (hc : c < E),
      (sepSpec M E ws[idx] &&& uniq).testBit (r * E + c) = true →
      ∀ (j : ℕ) (hj : j < ws.length), j ≠ idx →
        (!ws[j].testBit r) = false ∨ ws[j].testBit (M + c) = false := by
    intro idx hidx r c hr hc hbit j hj hji
    simp only [uniq, Nat.testBit_and, Nat.testBit_xor, testBit_mMask, Bool.and_eq_true] at hbit
    have hpos_lt : r * E + c < M * E := by
      have : (r + 1) * E ≤ M * E := Nat.mul_le_mul_right E (by omega)
      rw [Nat.succ_mul] at this; omega
    rw [decide_eq_true hpos_lt] at hbit
    have hc2f : (listC2 (ws.map (sepSpec M E))).testBit (r * E + c) = false := by
      cases h : (listC2 (ws.map (sepSpec M E))).testBit (r * E + c) with
      | false => rfl
      | true => rw [h] at hbit; exact Bool.noConfusion hbit.2
    have hnot : (sepSpec M E ws[j]).testBit (r * E + c) = false := by
      cases h : (sepSpec M E ws[j]).testBit (r * E + c) with
      | false => rfl
      | true =>
        exfalso
        have heq := listC2_testBit_false (ws.map (sepSpec M E)) (r * E + c) hc2f
          j idx (by simpa using hj) (by simpa using hidx) (by simpa using h) (by simpa using hbit.1)
        exact hji heq
    rw [sepSpec_testBit hEpos (hlt _ (List.getElem_mem hj)) r c hr hc, Bool.and_eq_false_iff] at hnot
    exact hnot
  -- Deduce exact bits on ws[i1] and ws[i2]
  have hb1_i1 : ws[i1].testBit (M + b1) = true := by
    rw [Nat.testBit_and, sepSpec_testBit hEpos (hlt _ (List.getElem_mem hi1)) d b1 hdM hb1,
      Bool.and_eq_true, Bool.and_eq_true] at hub1
    exact hub1.1.2
  have hb2_i2 : ws[i2].testBit (M + b2) = true := by
    rw [Nat.testBit_and, sepSpec_testBit hEpos (hlt _ (List.getElem_mem hi2)) d b2 hdM hb2,
      Bool.and_eq_true, Bool.and_eq_true] at hub2
    exact hub2.1.2
  have hf1_i1 : ws[i1].testBit f1 = false := by
    rw [Nat.testBit_and, sepSpec_testBit hEpos (hlt _ (List.getElem_mem hi1)) f1 a hf1 haE,
      Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at huf1
    exact huf1.1.1
  have hf2_i2 : ws[i2].testBit f2 = false := by
    rw [Nat.testBit_and, sepSpec_testBit hEpos (hlt _ (List.getElem_mem hi2)) f2 a hf2 haE,
      Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at huf2
    exact huf2.1.1
  have hb1_i2 : ws[i2].testBit (M + b1) = false := by
    rcases huniq_idx i1 hi1 d b1 hdM hb1 hub1 i2 hi2 hne.symm with h | h
    · rw [hd2] at h; exact Bool.noConfusion h
    · exact h
  have hb2_i1 : ws[i1].testBit (M + b2) = false := by
    rcases huniq_idx i2 hi2 d b2 hdM hb2 hub2 i1 hi1 hne with h | h
    · rw [hd1] at h; exact Bool.noConfusion h
    · exact h
  have hf1_i2 : ws[i2].testBit f1 = true := by
    rcases huniq_idx i1 hi1 f1 a hf1 haE huf1 i2 hi2 hne.symm with h | h
    · cases hx : ws[i2].testBit f1 <;> simp_all
    · rw [ha2] at h; exact Bool.noConfusion h
  have hf2_i1 : ws[i1].testBit f2 = true := by
    rcases huniq_idx i2 hi2 f2 a hf2 haE huf2 i1 hi1 hne with h | h
    · cases hx : ws[i1].testBit f2 <;> simp_all
    · rw [ha1] at h; exact Bool.noConfusion h
  -- Apply eval6_bound with (M+a, M+b1, M+b2, d, f1, f2)
  have hcard : ws.toFinset.card = k + 1 := by rw [List.toFinset_card_of_nodup hnd, hlen]
  have hbd := eval6_bound hdl hcard (M + a) (M + b1) (M + b2) d f1 f2
  have hgoal3 : eval6 (M + a) (M + b1) (M + b2) d f1 f2 (goalME M E) = 3 := by
    simp [eval6, value6, testBit_goalME, show M ≤ M + a by omega, show M + a < M + E by omega,
      show M ≤ M + b1 by omega, show M + b1 < M + E by omega,
      show M ≤ M + b2 by omega, show M + b2 < M + E by omega,
      show ¬ M ≤ d by omega, show ¬ M ≤ f1 by omega, show ¬ M ≤ f2 by omega]
  set ev := eval6 (M + a) (M + b1) (M + b2) d f1 f2
  have hev1 : ev ws[i1] = 1 := by
    simp [ev, eval6, value6, ha1, hb1_i1, hb2_i1, hd1, hf1_i1, hf2_i1]
  have hev2 : ev ws[i2] = 1 := by
    simp [ev, eval6, value6, ha2, hb1_i2, hb2_i2, hd2, hf1_i2, hf2_i2]
  have hev_other : ∀ w ∈ ws.toFinset, w ≠ ws[i1] → w ≠ ws[i2] → ev w = 0 := by
    intro w hw hne1 hne2
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 (List.mem_toFinset.1 hw)
    have hji1 : j ≠ i1 := fun e => hne1 (by subst e; rfl)
    have hji2 : j ≠ i2 := fun e => hne2 (by subst e; rfl)
    have hdb1 := huniq_idx i1 hi1 d b1 hdM hb1 hub1 j hj hji1
    have hdb2 := huniq_idx i2 hi2 d b2 hdM hb2 hub2 j hj hji2
    have haf1 := huniq_idx i1 hi1 f1 a hf1 haE huf1 j hj hji1
    have haf2 := huniq_idx i2 hi2 f2 a hf2 haE huf2 j hj hji2
    simp only [ev, eval6, value6]
    cases hwa : ws[j].testBit (M + a) <;> cases hwd : ws[j].testBit d
    · -- a=false, d=false -> b1=false, b2=false
      have hb1f : ws[j].testBit (M + b1) = false := hdb1.elim (by rw [hwd]; simp) id
      have hb2f : ws[j].testBit (M + b2) = false := hdb2.elim (by rw [hwd]; simp) id
      simp [hb1f, hb2f]
    · simp
    · -- a=true, d=false -> b1=false, b2=false, f1=true, f2=true
      have hb1f : ws[j].testBit (M + b1) = false := hdb1.elim (by rw [hwd]; simp) id
      have hb2f : ws[j].testBit (M + b2) = false := hdb2.elim (by rw [hwd]; simp) id
      have hf1t : ws[j].testBit f1 = true := haf1.elim (by cases ws[j].testBit f1 <;> simp) (by rw [hwa]; simp)
      have hf2t : ws[j].testBit f2 = true := haf2.elim (by cases ws[j].testBit f2 <;> simp) (by rw [hwa]; simp)
      simp [hb1f, hb2f, hf1t, hf2t]
    · -- a=true, d=true -> f1=true, f2=true
      have hf1t : ws[j].testBit f1 = true := haf1.elim (by cases ws[j].testBit f1 <;> simp) (by rw [hwa]; simp)
      have hf2t : ws[j].testBit f2 = true := haf2.elim (by cases ws[j].testBit f2 <;> simp) (by rw [hwa]; simp)
      simp [hf1t, hf2t]
  have hw1_ne_w2 : ws[i1] ≠ ws[i2] := fun e => hne ((List.Nodup.getElem_inj_iff hnd).1 e)
  have hsub : ({ws[i1], ws[i2]} : Finset ℕ) ⊆ ws.toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact List.mem_toFinset.2 (List.getElem_mem _)
  have hsum2 : ∑ w ∈ ws.toFinset, ev w = ∑ w ∈ ({ws[i1], ws[i2]} : Finset ℕ), ev w := by
    symm
    apply Finset.sum_subset hsub
    intro w hw hnot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    exact hev_other w hw hnot.1 hnot.2
  rw [hsum2, Finset.sum_pair hw1_ne_w2, hev1, hev2] at hbd
  rw [hgoal3] at hbd
  omega

/-! ## Section 2f: TURBO V4 evaluator, soundness, and circuit-to-barrier bridge -/

def scanNodes (ctx : GCtx) (uniq : ℕ) : List WNode → ℕ → Option ℕ
  | [], seen1 => some seen1
  | p :: t, seen1 =>
    let q := wireQual ctx uniq p.sw
    match Nat.beq q 0 with
    | true => scanNodes ctx uniq t seen1
    | false =>
      match Nat.beq (seen1 &&& q) 0 with
      | false => none
      | true => scanNodes ctx uniq t (seen1 ||| q)

def v6Step (ctx : GCtx) (uniq sw seen1 : ℕ) : Option ℕ :=
  let q := wireQual ctx uniq sw
  match Nat.beq (seen1 &&& q) 0 with
  | false => none
  | true => some (seen1 ||| q)

def v6Check0 (ctx : GCtx) (base1 base2 sc : ℕ) (pref tail : List WNode) : Bool :=
  let uniq := ctx.full ^^^ (base2 ||| (base1 &&& sc))
  match Nat.beq uniq 0 with
  | true => false
  | false =>
    let q0 := wireQual ctx uniq sc
    match scanNodes ctx uniq pref q0 with
    | none => true
    | some s1 =>
      match scanNodes ctx uniq tail s1 with
      | none => true
      | some _ => false

def v6Check1 (ctx : GCtx) (base1 base2 sc sx : ℕ) (pref tail : List WNode) : Bool :=
  let c1x := base1 ||| sx
  let c2x := base2 ||| (base1 &&& sx)
  let uniq := ctx.full ^^^ (c2x ||| (c1x &&& sc))
  match Nat.beq uniq 0 with
  | true => false
  | false =>
    let q0 := wireQual ctx uniq sc
    match v6Step ctx uniq sx q0 with
    | none => true
    | some s1 =>
      match scanNodes ctx uniq pref s1 with
      | none => true
      | some s2 =>
        match scanNodes ctx uniq tail s2 with
        | none => true
        | some _ => false

def v6Check2 (ctx : GCtx) (base1 base2 sc sa sb : ℕ) (pref tail : List WNode) : Bool :=
  let c1a := base1 ||| sa
  let c2a := base2 ||| (base1 &&& sa)
  let c1ab := c1a ||| sb
  let c2ab := c2a ||| (c1a &&& sb)
  let uniq := ctx.full ^^^ (c2ab ||| (c1ab &&& sc))
  match Nat.beq uniq 0 with
  | true => false
  | false =>
    let q0 := wireQual ctx uniq sc
    match v6Step ctx uniq sa q0 with
    | none => true
    | some s1 =>
      match v6Step ctx uniq sb s1 with
      | none => true
      | some s2 =>
        match scanNodes ctx uniq pref s2 with
        | none => true
        | some s3 =>
          match scanNodes ctx uniq tail s3 with
          | none => true
          | some _ => false

def checkHT (S : ℕ → ℕ → List ℕ) (N : ℕ → ℕ)
    (idx : ℕ → List ℕ → ℕ) (ori : List ℕ → List ℕ) (s : ℕ) (ns : List ℕ) : Bool :=
  let c := ori ns
  let j := idx s c
  !(Nat.blt j (N s) && isPermNat c (S s j))

def tryOpV4 (ctx : GCtx) (maxKeep : ℕ)
    (S : ℕ → ℕ → List ℕ) (N : ℕ → ℕ)
    (idx : ℕ → List ℕ → ℕ) (ori : List ℕ → List ℕ) (s : ℕ)
    (pref tail : List WNode) (a ga sa b gb sb base1 base2 c sc : ℕ) : Bool :=
  let c0 := base1 ||| sc
  let canReach :=
    match maxKeep with
    | 0 => Nat.beq c0 ctx.full
    | 1 => Nat.beq (c0 ||| sa) ctx.full || Nat.beq (c0 ||| sb) ctx.full
    | _ => true
  match canReach with
  | false => false
  | true =>
    let gc := c ^^^ ctx.mMask
    match Nat.beq (gc &&& ga) gc || Nat.beq (gc &&& gb) gc || anyDomBoth gc pref || anyDomBoth gc tail with
    | true => false
    | false =>
      (Nat.beq c0 ctx.full &&
        (match Nat.beq maxKeep 0 && v6Check0 ctx base1 base2 sc pref tail with
         | true => false
         | false => checkHT S N idx ori s (c :: collectW (collectW [] tail) pref))) ||
      (Nat.ble 1 maxKeep &&
        (let canA := !(Nat.beq (ga &&& gc) ga)
         let canB := !(Nat.beq (gb &&& gc) gb)
         (canA && Nat.beq (c0 ||| sa) ctx.full &&
           (match Nat.beq maxKeep 1 && v6Check1 ctx base1 base2 sc sa pref tail with
            | true => false
            | false => checkHT S N idx ori s (c :: a :: collectW (collectW [] tail) pref))) ||
         (canB && Nat.beq (c0 ||| sb) ctx.full &&
           (match Nat.beq maxKeep 1 && v6Check1 ctx base1 base2 sc sb pref tail with
            | true => false
            | false => checkHT S N idx ori s (c :: b :: collectW (collectW [] tail) pref))) ||
         (Nat.ble 2 maxKeep && canA && canB && Nat.beq (c0 ||| sa ||| sb) ctx.full &&
           (match Nat.beq maxKeep 2 && v6Check2 ctx base1 base2 sc sa sb pref tail with
            | true => false
            | false => checkHT S N idx ori s (c :: a :: b :: collectW (collectW [] tail) pref)))))

def loopPairBV4 (ctx : GCtx) (maxKeep : ℕ)
    (S : ℕ → ℕ → List ℕ) (N : ℕ → ℕ)
    (idx : ℕ → List ℕ → ℕ) (ori : List ℕ → List ℕ) (s : ℕ)
    (a ga sa : ℕ) (pref : List WNode) (p1 p2 : ℕ) : List WNode → Bool
  | [] => false
  | nb :: tail =>
    let base1 := p1 ||| nb.tc1
    let base2 := p2 ||| nb.tc2 ||| (p1 &&& nb.tc1)
    let cand := a &&& nb.w
    let candE := cand >>> ctx.M
    let okAnd :=
      !(Nat.beq candE 0) && !(Nat.beq (cand &&& ctx.mMask) ctx.mMask) &&
      (let scand := (sa ||| nb.sw) &&& (candE * ctx.loCol)
       tryOpV4 ctx maxKeep S N idx ori s pref tail a ga sa nb.w nb.gw nb.sw base1 base2 cand scand)
    okAnd ||
    (let cor := a ||| nb.w
     let okOr :=
       !(Nat.beq (cor &&& ctx.mMask) ctx.mMask) && !(Nat.beq (cor >>> ctx.M) 0) &&
       (let scor := sepFast ctx.M ctx.E ctx.mMask ctx.tab ctx.e4 ctx.mask4 cor
        tryOpV4 ctx maxKeep S N idx ori s pref tail a ga sa nb.w nb.gw nb.sw base1 base2 cor scor)
     okOr ||
     loopPairBV4 ctx maxKeep S N idx ori s a ga sa (nb :: pref) (p1 ||| nb.sw) (p2 ||| (p1 &&& nb.sw)) tail)

def loopPairAV4 (ctx : GCtx) (maxKeep : ℕ)
    (S : ℕ → ℕ → List ℕ) (N : ℕ → ℕ)
    (idx : ℕ → List ℕ → ℕ) (ori : List ℕ → List ℕ) (s : ℕ)
    (pref : List WNode) (p1 p2 : ℕ) : List WNode → Bool
  | [] => false
  | na :: tail =>
    loopPairBV4 ctx maxKeep S N idx ori s na.w na.gw na.sw pref p1 p2 tail ||
    loopPairAV4 ctx maxKeep S N idx ori s (na :: pref) (p1 ||| na.sw) (p2 ||| (p1 &&& na.sw)) tail

def barV3 (M E : ℕ) (S : ℕ → ℕ → List ℕ) (N : ℕ → ℕ)
    (idx : ℕ → List ℕ → ℕ) (ori : List ℕ → List ℕ) : ℕ → ℕ → Bool
  | 0, i =>
    let ws := S 0 i
    nodupNat ws && !(ws == [((1 <<< E) - 1) <<< M])
  | s + 1, i =>
    let ws := S (s + 1) i
    allLt (1 <<< (M + E)) ws && nodupNat ws && !(ws == [((1 <<< E) - 1) <<< M]) &&
    let ctx := mkGCtx M E
    let nodes := buildNodes ctx ws
    !(loopPairAV4 ctx (s + 2 - ws.length) S N idx ori s [] 0 0 nodes)

def span (f : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, _ => true
  | n + 1, i => f i && span f n (i + 1)

theorem span_ok {f : ℕ → Bool} : ∀ {n off : ℕ}, span f n off = true →
    ∀ j, off ≤ j → j < off + n → f j = true
  | 0, _, _, _, h1, h2 => by omega
  | n + 1, off, h, j, h1, h2 => by
    simp only [span, Bool.and_eq_true] at h
    by_cases heq : j = off
    · subst heq; exact h.1
    · exact span_ok h.2 j (by omega) (by omega)

theorem span_step {f : ℕ → Bool} (n off : ℕ) {m : ℕ}
    (h1 : span f n off = true)
    (h2 : ∀ i, off + n ≤ i → i < m → f i = true) :
    ∀ i, off ≤ i → i < m → f i = true := by
  intro i hlo hhi
  by_cases h : i < off + n
  · exact span_ok h1 i hlo h
  · exact h2 i (by omega) hhi

theorem span_end {f : ℕ → Bool} (n off : ℕ) {m : ℕ}
    (h1 : span f n off = true) (hle : m ≤ off + n) :
    ∀ i, off ≤ i → i < m → f i = true :=
  fun i hlo hhi => span_ok h1 i hlo (by omega)

theorem lvl_empty {f : ℕ → Bool} : ∀ i, 0 ≤ i → i < 0 → f i = true :=
  fun _ _ h => by omega

theorem all_step {Z : ℕ → ℕ → Bool} {N : ℕ → ℕ} {s : ℕ}
    (h1 : ∀ i, 0 ≤ i → i < N (s + 1) → Z (s + 1) i = true)
    (h2 : ∀ t ≤ s, ∀ i < N t, Z t i = true) :
    ∀ t ≤ s + 1, ∀ i < N t, Z t i = true := by
  intro t ht i hi
  by_cases he : t = s + 1
  · subst he; exact h1 i (Nat.zero_le _) hi
  · exact h2 t (by omega) i hi

theorem all_zero {Z : ℕ → ℕ → Bool} {N : ℕ → ℕ}
    (h0 : ∀ i, 0 ≤ i → i < N 0 → Z 0 i = true) :
    ∀ t ≤ 0, ∀ i < N t, Z t i = true := by
  intro t ht i hi
  have h0' : t = 0 := by omega
  subst h0'; exact h0 i (Nat.zero_le _) hi

-- Helper lemmas for scanNodes, v6Check0/1/2

theorem perm_toFinset_eq {l1 l2 : List ℕ} (h : l1.Perm l2) : l1.toFinset = l2.toFinset := by
  ext x; simp [h.mem_iff]

theorem or_full_of_lt {K x y : ℕ} (hx : x = (1 <<< K) - 1) (hy : y < 2 ^ K) :
    x ||| y = (1 <<< K) - 1 := by
  apply Nat.eq_of_testBit_eq; intro p
  rw [Nat.testBit_or, hx, testBit_mMask]
  by_cases hp : p < K
  · simp [hp]
  · rw [decide_eq_false hp, testBit_lt_of_lt hy (by omega)]; rfl

theorem exists_testBit_of_ne_zero {x : ℕ} (h : x ≠ 0) : ∃ p, x.testBit p = true := by
  by_contra hall; push Not at hall
  apply h
  apply Nat.eq_of_testBit_eq; intro p
  rw [Nat.zero_testBit]
  exact Bool.eq_false_iff.2 (hall p)

theorem scanNodes_none (ctx : GCtx) (uniq : ℕ) :
    ∀ (ns : List WNode) (seen1 : ℕ), scanNodes ctx uniq ns seen1 = none →
      (∃ i, ∃ hi : i < ns.length, ∃ p, seen1.testBit p = true ∧ (wireQual ctx uniq ns[i].sw).testBit p = true) ∨
      (∃ i, ∃ hi : i < ns.length, ∃ j, ∃ hj : j < ns.length, i ≠ j ∧
        ∃ p, (wireQual ctx uniq ns[i].sw).testBit p = true ∧ (wireQual ctx uniq ns[j].sw).testBit p = true)
  | [], _, h => by simp [scanNodes] at h
  | a :: t, seen1, h => by
    simp only [scanNodes] at h
    cases hq0 : Nat.beq (wireQual ctx uniq a.sw) 0 with
    | true =>
      rw [hq0] at h
      rcases scanNodes_none ctx uniq t seen1 h with ⟨i, hi, p, hs, hq⟩ | ⟨i, hi, j, hj, hne, p, h1, h2⟩
      · exact Or.inl ⟨i + 1, by simp; omega, p, hs, hq⟩
      · exact Or.inr ⟨i + 1, by simp; omega, j + 1, by simp; omega, by omega, p, h1, h2⟩
    | false =>
      rw [hq0] at h
      cases hsq : Nat.beq (seen1 &&& wireQual ctx uniq a.sw) 0 with
      | false =>
        obtain ⟨p, hp⟩ := exists_testBit_of_ne_zero (nat_beq_false.1 hsq)
        rw [Nat.testBit_and, Bool.and_eq_true] at hp
        exact Or.inl ⟨0, by simp, p, hp.1, hp.2⟩
      | true =>
        rw [hsq] at h
        rcases scanNodes_none ctx uniq t (seen1 ||| wireQual ctx uniq a.sw) h with
          ⟨i, hi, p, hs, hq⟩ | ⟨i, hi, j, hj, hne, p, h1, h2⟩
        · rw [Nat.testBit_or, Bool.or_eq_true] at hs
          rcases hs with hs1 | hqa
          · exact Or.inl ⟨i + 1, by simp; omega, p, hs1, hq⟩
          · exact Or.inr ⟨0, by simp, i + 1, by simp; omega, by omega, p, hqa, hq⟩
        · exact Or.inr ⟨i + 1, by simp; omega, j + 1, by simp; omega, by omega, p, h1, h2⟩

theorem scanNodes_some (ctx : GCtx) (uniq : ℕ) :
    ∀ (ns : List WNode) (seen1 s' : ℕ), scanNodes ctx uniq ns seen1 = some s' →
      ∀ p, s'.testBit p = true ↔
        seen1.testBit p = true ∨ ∃ i, ∃ hi : i < ns.length, (wireQual ctx uniq ns[i].sw).testBit p = true
  | [], seen1, s', h, p => by
    simp only [scanNodes, Option.some.injEq] at h
    subst h; simp
  | a :: t, seen1, s', h, p => by
    simp only [scanNodes] at h
    cases hq0 : Nat.beq (wireQual ctx uniq a.sw) 0 with
    | true =>
      rw [hq0] at h
      have hqzero : wireQual ctx uniq a.sw = 0 := nat_beq_true.1 hq0
      rw [scanNodes_some ctx uniq t seen1 s' h p]
      constructor
      · rintro (hs | ⟨i, hi, hq⟩)
        · exact Or.inl hs
        · exact Or.inr ⟨i + 1, by simp; omega, hq⟩
      · rintro (hs | ⟨i, hi, hq⟩)
        · exact Or.inl hs
        · cases i with
          | zero => simp [hqzero] at hq
          | succ i' => exact Or.inr ⟨i', by simp at hi; omega, hq⟩
    | false =>
      rw [hq0] at h
      cases hsq : Nat.beq (seen1 &&& wireQual ctx uniq a.sw) 0 with
      | false => rw [hsq] at h; cases h
      | true =>
        rw [hsq] at h
        rw [scanNodes_some ctx uniq t (seen1 ||| wireQual ctx uniq a.sw) s' h p,
          Nat.testBit_or, Bool.or_eq_true]
        constructor
        · rintro ((hs | hqa) | ⟨i, hi, hq⟩)
          · exact Or.inl hs
          · exact Or.inr ⟨0, by simp, hqa⟩
          · exact Or.inr ⟨i + 1, by simp; omega, hq⟩
        · rintro (hs | ⟨i, hi, hq⟩)
          · exact Or.inl (Or.inl hs)
          · cases i with
            | zero => exact Or.inl (Or.inr hq)
            | succ i' => exact Or.inr ⟨i', by simp at hi; omega, hq⟩

theorem v6Step_none {ctx : GCtx} {uniq sw seen1 : ℕ} (h : v6Step ctx uniq sw seen1 = none) :
    ∃ p, seen1.testBit p = true ∧ (wireQual ctx uniq sw).testBit p = true := by
  unfold v6Step at h; dsimp only at h
  cases hsq : Nat.beq (seen1 &&& wireQual ctx uniq sw) 0 with
  | true => rw [hsq] at h; cases h
  | false =>
    obtain ⟨p, hp⟩ := exists_testBit_of_ne_zero (nat_beq_false.1 hsq)
    rw [Nat.testBit_and, Bool.and_eq_true] at hp
    exact ⟨p, hp.1, hp.2⟩

theorem v6Step_some {ctx : GCtx} {uniq sw seen1 s' : ℕ} (h : v6Step ctx uniq sw seen1 = some s') :
    ∀ p, s'.testBit p = true ↔ seen1.testBit p = true ∨ (wireQual ctx uniq sw).testBit p = true := by
  unfold v6Step at h; dsimp only at h
  cases hsq : Nat.beq (seen1 &&& wireQual ctx uniq sw) 0 with
  | false => rw [hsq] at h; cases h
  | true =>
    rw [hsq] at h; cases h
    intro p; rw [Nat.testBit_or, Bool.or_eq_true]

def PrefOK (M E : ℕ) (ns : List WNode) : Prop :=
  ∀ p ∈ ns, p.gw = p.w ^^^ ((1 <<< M) - 1) ∧ p.sw = sepSpec M E p.w

def NodesOK (M E : ℕ) : List WNode → Prop
  | [] => True
  | h :: t =>
    h.gw = h.w ^^^ ((1 <<< M) - 1) ∧
    h.sw = sepSpec M E h.w ∧
    h.tc1 = listC1 (t.map (·.sw)) ∧
    h.tc2 = listC2 (t.map (·.sw)) ∧
    NodesOK M E t

theorem NodesOK.toPrefOK {M E : ℕ} : ∀ {ns : List WNode}, NodesOK M E ns → PrefOK M E ns
  | [], _ => fun _ h => by simp at h
  | h :: t, ⟨hgw, hsw, _, _, ht⟩ => fun p hp => by
    rcases List.mem_cons.1 hp with rfl | hpt
    · exact ⟨hgw, hsw⟩
    · exact NodesOK.toPrefOK ht p hpt

theorem buildNodes_map_w (ctx : GCtx) : ∀ ws : List ℕ, (buildNodes ctx ws).map (·.w) = ws
  | [] => rfl
  | w :: t => by
    simp only [buildNodes]
    cases h : buildNodes ctx t with
    | nil =>
      have := buildNodes_map_w ctx t; rw [h] at this; simp at this; subst this; rfl
    | cons x xs =>
      have := buildNodes_map_w ctx t; rw [h] at this; simp [this]

theorem buildNodes_ok {M E : ℕ} (hME : validME M E = true) :
    ∀ ws : List ℕ, NodesOK M E (buildNodes (mkGCtx M E) ws)
  | [] => trivial
  | w :: t => by
    have ih := buildNodes_ok hME t
    simp only [buildNodes]
    cases h : buildNodes (mkGCtx M E) t with
    | nil =>
      refine ⟨rfl, ?_, rfl, rfl, trivial⟩
      exact sepFast_eq_sepSpec hME
    | cons x xs =>
      rw [h] at ih
      refine ⟨rfl, sepFast_eq_sepSpec hME, ?_, ?_, ih⟩
      · simp [listC1, ih.2.2.1]
      · simp [listC2, ih.2.2.1, ih.2.2.2.1]

theorem PrefOK.map_sw {M E : ℕ} : ∀ {ns : List WNode}, PrefOK M E ns →
    ns.map (·.sw) = (ns.map (·.w)).map (sepSpec M E)
  | [], _ => rfl
  | h :: t, hp => by
    simp [(hp h List.mem_cons_self).2, PrefOK.map_sw (fun p hpt => hp p (List.mem_cons_of_mem _ hpt))]

theorem PrefOK.getElem_sw {M E : ℕ} {ns : List WNode} (h : PrefOK M E ns) (i : ℕ) (hi : i < ns.length) :
    ns[i].sw = sepSpec M E ns[i].w :=
  (h ns[i] (List.getElem_mem hi)).2

theorem anyDomBoth_false {M E c : ℕ} : ∀ {ns : List WNode}, PrefOK M E ns →
    (∀ p ∈ ns, domME M c p.w = false ∧ domME M p.w c = false) →
    anyDomBoth (c ^^^ ((1 <<< M) - 1)) ns = false
  | [], _, _ => rfl
  | h :: t, hpok, hall => by
    simp only [anyDomBoth, Bool.or_eq_false_iff]
    have hgw := (hpok h List.mem_cons_self).1
    have hh := hall h List.mem_cons_self
    have h1 : Nat.beq ((c ^^^ ((1 <<< M) - 1)) &&& h.gw) (c ^^^ ((1 <<< M) - 1)) = false := by
      rw [hgw]; exact hh.1
    have h2 : Nat.beq ((c ^^^ ((1 <<< M) - 1)) &&& h.gw) h.gw = false := by
      rw [hgw, Nat.and_comm]; exact hh.2
    exact ⟨⟨h1, h2⟩, anyDomBoth_false (fun p hp => hpok p (List.mem_cons_of_mem _ hp))
      (fun p hp => hall p (List.mem_cons_of_mem _ hp))⟩

theorem collectW_eq (acc : List ℕ) : ∀ l : List WNode, collectW acc l = l.reverse.map (·.w) ++ acc
  | [] => rfl
  | p :: t => by simp [collectW, collectW_eq (p.w :: acc) t]

theorem collectW_toFinset (pref tail : List WNode) :
    (collectW (collectW [] tail) pref).toFinset = (pref.map (·.w) ++ tail.map (·.w)).toFinset := by
  rw [collectW_eq, collectW_eq]
  ext x
  simp

-- Helper to pull a shared bit from scanNodes on (pref, tail) into a list (lead ++ pref.map .w ++ tail.map .w)
theorem scanNodes_pair_hit {M E : ℕ} {uniq : ℕ} {lead : List ℕ} {pref tail : List WNode}
    (hpref : PrefOK M E pref) (htail : PrefOK M E tail)
    {s0 : ℕ}
    (hs0 : ∀ p, s0.testBit p = true →
      ∃ i, ∃ hi : i < lead.length, (wireQual (mkGCtx M E) uniq (sepSpec M E lead[i])).testBit p = true)
    (hhit : (match scanNodes (mkGCtx M E) uniq pref s0 with
            | none => true
            | some s1 => match scanNodes (mkGCtx M E) uniq tail s1 with | none => true | some _ => false) = true) :
    let ws := lead ++ (pref.map (·.w) ++ tail.map (·.w))
    ∃ i1, ∃ hi1 : i1 < ws.length, ∃ i2, ∃ hi2 : i2 < ws.length, i1 ≠ i2 ∧
      ∃ p, (wireQual (mkGCtx M E) uniq (sepSpec M E ws[i1])).testBit p = true ∧
           (wireQual (mkGCtx M E) uniq (sepSpec M E ws[i2])).testBit p = true := by
  intro ws
  have hget_lead : ∀ i (hi : i < lead.length),
      ws[i]'(by simp [ws]; omega) = lead[i] := fun i hi => by
    simp [ws, List.getElem_append_left hi]
  have hget_pref : ∀ i (hi : i < pref.length),
      ws[lead.length + i]'(by simp [ws]; omega) = pref[i].w := fun i hi => by
    simp only [ws, List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    rw [List.getElem_append_left (by simp; omega)]; simp
  have hget_tail : ∀ i (hi : i < tail.length),
      ws[lead.length + pref.length + i]'(by simp [ws]; omega) = tail[i].w := fun i hi => by
    simp only [ws, List.getElem_append_right (show lead.length ≤ lead.length + pref.length + i by omega),
      show lead.length + pref.length + i - lead.length = pref.length + i by omega]
    rw [List.getElem_append_right (by simp)]; simp
  cases hp : scanNodes (mkGCtx M E) uniq pref s0 with
  | none =>
    rcases scanNodes_none (mkGCtx M E) uniq pref s0 hp with ⟨i, hi, p, h1, h2⟩ | ⟨i, hi, j, hj, hne, p, h1, h2⟩
    · obtain ⟨k, hk, hkq⟩ := hs0 p h1
      rw [hpref.getElem_sw i hi] at h2
      refine ⟨k, by simp [ws]; omega, lead.length + i, by simp [ws]; omega, by omega, p, ?_, ?_⟩
      · rwa [hget_lead k hk]
      · rwa [hget_pref i hi]
    · rw [hpref.getElem_sw i hi] at h1
      rw [hpref.getElem_sw j hj] at h2
      refine ⟨lead.length + i, by simp [ws]; omega, lead.length + j, by simp [ws]; omega, by omega, p, ?_, ?_⟩
      · rwa [hget_pref i hi]
      · rwa [hget_pref j hj]
  | some s1 =>
    rw [hp] at hhit; dsimp only at hhit
    cases ht : scanNodes (mkGCtx M E) uniq tail s1 with
    | some _ => rw [ht] at hhit; exact Bool.noConfusion hhit
    | none =>
      have hs1 := scanNodes_some (mkGCtx M E) uniq pref s0 s1 hp
      rcases scanNodes_none (mkGCtx M E) uniq tail s1 ht with ⟨j, hj, p, h1, h2⟩ | ⟨i, hi, j, hj, hne, p, h1, h2⟩
      · rw [htail.getElem_sw j hj] at h2
        rcases (hs1 p).1 h1 with h1' | ⟨i, hi, h1'⟩
        · obtain ⟨k, hk, hkq⟩ := hs0 p h1'
          refine ⟨k, by simp [ws]; omega, lead.length + pref.length + j, by simp [ws]; omega, by omega, p, ?_, ?_⟩
          · rwa [hget_lead k hk]
          · rwa [hget_tail j hj]
        · rw [hpref.getElem_sw i hi] at h1'
          refine ⟨lead.length + i, by simp [ws]; omega, lead.length + pref.length + j, by simp [ws]; omega, by omega, p, ?_, ?_⟩
          · rwa [hget_pref i hi]
          · rwa [hget_tail j hj]
      · rw [htail.getElem_sw i hi] at h1
        rw [htail.getElem_sw j hj] at h2
        refine ⟨lead.length + pref.length + i, by simp [ws]; omega,
          lead.length + pref.length + j, by simp [ws]; omega, by omega, p, ?_, ?_⟩
        · rwa [hget_tail i hi]
        · rwa [hget_tail j hj]

theorem v6Check0_no {M E k c sc base1 base2 : ℕ} {pref tail : List WNode}
    (hME : validME M E = true)
    (hpref : PrefOK M E pref) (htail : PrefOK M E tail)
    (hsc : sc = sepSpec M E c)
    (hb1 : base1 = listC1 ((pref ++ tail).map (·.sw)))
    (hb2 : base2 = listC2 ((pref ++ tail).map (·.sw)))
    (hnd : (c :: (pref.map (·.w) ++ tail.map (·.w))).Nodup)
    (hlt : ∀ w ∈ (c :: (pref.map (·.w) ++ tail.map (·.w))), w < 2 ^ (M + E))
    (hlen : (c :: (pref.map (·.w) ++ tail.map (·.w))).length = k + 1)
    (hv6 : v6Check0 (mkGCtx M E) base1 base2 sc pref tail = true) :
    ¬ DLive M E k (c :: (pref.map (·.w) ++ tail.map (·.w))).toFinset := by
  unfold v6Check0 at hv6
  dsimp only at hv6
  set ws := c :: (pref.map (·.w) ++ tail.map (·.w))
  have huniq : ((1 <<< (M * E)) - 1) ^^^ (base2 ||| (base1 &&& sc)) =
      ((1 <<< (M * E)) - 1) ^^^ listC2 (ws.map (sepSpec M E)) := by
    congr 1
    have hsws : (pref ++ tail).map (·.sw) = (pref.map (·.w) ++ tail.map (·.w)).map (sepSpec M E) := by
      rw [List.map_append, List.map_append, hpref.map_sw, htail.map_sw]
    rw [hb1, hb2, hsws, hsc]
    simp only [ws, List.map_cons, listC2, Nat.and_comm]
  cases hu0 : Nat.beq ((mkGCtx M E).full ^^^ (base2 ||| (base1 &&& sc))) 0 with
  | true => rw [hu0] at hv6; exact Bool.noConfusion hv6
  | false =>
    rw [hu0] at hv6; dsimp only at hv6
    have hs0 : ∀ p, (wireQual (mkGCtx M E) ((mkGCtx M E).full ^^^ (base2 ||| (base1 &&& sc))) sc).testBit p = true →
        ∃ i, ∃ hi : i < [c].length,
          (wireQual (mkGCtx M E) ((mkGCtx M E).full ^^^ (base2 ||| (base1 &&& sc))) (sepSpec M E [c][i])).testBit p = true := by
      intro p hp; exact ⟨0, by simp, by simpa [hsc] using hp⟩
    obtain ⟨i1, hi1, i2, hi2, hne, p, hq1, hq2⟩ := scanNodes_pair_hit hpref htail hs0 hv6
    rw [show (mkGCtx M E).full = (1 <<< (M * E)) - 1 from rfl, huniq] at hq1 hq2
    exact v6_refute hME hnd hlt hlen i1 i2 hi1 hi2 hne p hq1 hq2

theorem v6Check1_no {M E k c sc x sx base1 base2 : ℕ} {pref tail : List WNode}
    (hME : validME M E = true)
    (hpref : PrefOK M E pref) (htail : PrefOK M E tail)
    (hsc : sc = sepSpec M E c) (hsx : sx = sepSpec M E x)
    (hb1 : base1 = listC1 ((pref ++ tail).map (·.sw)))
    (hb2 : base2 = listC2 ((pref ++ tail).map (·.sw)))
    (hnd : (c :: x :: (pref.map (·.w) ++ tail.map (·.w))).Nodup)
    (hlt : ∀ w ∈ (c :: x :: (pref.map (·.w) ++ tail.map (·.w))), w < 2 ^ (M + E))
    (hlen : (c :: x :: (pref.map (·.w) ++ tail.map (·.w))).length = k + 1)
    (hv6 : v6Check1 (mkGCtx M E) base1 base2 sc sx pref tail = true) :
    ¬ DLive M E k (c :: x :: (pref.map (·.w) ++ tail.map (·.w))).toFinset := by
  unfold v6Check1 at hv6
  dsimp only at hv6
  set ws := c :: x :: (pref.map (·.w) ++ tail.map (·.w))
  set uniq := (mkGCtx M E).full ^^^ ((base2 ||| (base1 &&& sx)) ||| ((base1 ||| sx) &&& sc))
  have huniq : uniq = ((1 <<< (M * E)) - 1) ^^^ listC2 (ws.map (sepSpec M E)) := by
    show ((1 <<< (M * E)) - 1) ^^^ _ = _
    congr 1
    have hsws : (pref ++ tail).map (·.sw) = (pref.map (·.w) ++ tail.map (·.w)).map (sepSpec M E) := by
      rw [List.map_append, List.map_append, hpref.map_sw, htail.map_sw]
    rw [hb1, hb2, hsws, hsc, hsx]
    simp only [ws, List.map_cons, listC2, listC1, Nat.and_comm, Nat.or_comm]
  cases hu0 : Nat.beq uniq 0 with
  | true => rw [hu0] at hv6; exact Bool.noConfusion hv6
  | false =>
    rw [hu0] at hv6; dsimp only at hv6
    cases hs1 : v6Step (mkGCtx M E) uniq sx (wireQual (mkGCtx M E) uniq sc) with
    | none =>
      obtain ⟨p, h1, h2⟩ := v6Step_none hs1
      rw [huniq, hsc] at h1
      rw [huniq, hsx] at h2
      exact v6_refute hME hnd hlt hlen 0 1 (by simp [ws]) (by simp [ws]) (by omega) p h1 h2
    | some s1 =>
      rw [hs1] at hv6; dsimp only at hv6
      have hspec1 := v6Step_some hs1
      have hlead : ∀ p, s1.testBit p = true →
          ∃ i, ∃ hi : i < [c, x].length, (wireQual (mkGCtx M E) uniq (sepSpec M E [c, x][i])).testBit p = true := by
        intro p hp
        rcases (hspec1 p).1 hp with h1 | h2
        · exact ⟨0, by simp, by simpa [hsc] using h1⟩
        · exact ⟨1, by simp, by simpa [hsx] using h2⟩
      obtain ⟨i1, hi1, i2, hi2, hne, p, hq1, hq2⟩ := scanNodes_pair_hit hpref htail hlead hv6
      rw [huniq] at hq1 hq2
      exact v6_refute hME hnd hlt hlen i1 i2 hi1 hi2 hne p hq1 hq2

theorem v6Check2_no {M E k c sc a sa b sb base1 base2 : ℕ} {pref tail : List WNode}
    (hME : validME M E = true)
    (hpref : PrefOK M E pref) (htail : PrefOK M E tail)
    (hsc : sc = sepSpec M E c) (hsa : sa = sepSpec M E a) (hsb : sb = sepSpec M E b)
    (hb1 : base1 = listC1 ((pref ++ tail).map (·.sw)))
    (hb2 : base2 = listC2 ((pref ++ tail).map (·.sw)))
    (hnd : (c :: a :: b :: (pref.map (·.w) ++ tail.map (·.w))).Nodup)
    (hlt : ∀ w ∈ (c :: a :: b :: (pref.map (·.w) ++ tail.map (·.w))), w < 2 ^ (M + E))
    (hlen : (c :: a :: b :: (pref.map (·.w) ++ tail.map (·.w))).length = k + 1)
    (hv6 : v6Check2 (mkGCtx M E) base1 base2 sc sa sb pref tail = true) :
    ¬ DLive M E k (c :: a :: b :: (pref.map (·.w) ++ tail.map (·.w))).toFinset := by
  unfold v6Check2 at hv6
  dsimp only at hv6
  set ws := c :: a :: b :: (pref.map (·.w) ++ tail.map (·.w))
  set uniq := (mkGCtx M E).full ^^^
    (((base2 ||| (base1 &&& sa)) ||| ((base1 ||| sa) &&& sb)) ||| (((base1 ||| sa) ||| sb) &&& sc))
  have huniq : uniq = ((1 <<< (M * E)) - 1) ^^^ listC2 (ws.map (sepSpec M E)) := by
    show ((1 <<< (M * E)) - 1) ^^^ _ = _
    congr 1
    have hsws : (pref ++ tail).map (·.sw) = (pref.map (·.w) ++ tail.map (·.w)).map (sepSpec M E) := by
      rw [List.map_append, List.map_append, hpref.map_sw, htail.map_sw]
    have hperm : (c :: b :: a :: (pref.map (·.w) ++ tail.map (·.w))).map (sepSpec M E) |>.Perm
        (ws.map (sepSpec M E)) := List.Perm.cons _ (List.Perm.swap _ _ _)
    rw [← listC2_perm hperm, hb1, hb2, hsws, hsc, hsa, hsb]
    simp only [List.map_cons, listC2, listC1, Nat.and_comm, Nat.or_comm]
  cases hu0 : Nat.beq uniq 0 with
  | true => rw [hu0] at hv6; exact Bool.noConfusion hv6
  | false =>
    rw [hu0] at hv6; dsimp only at hv6
    cases hs1 : v6Step (mkGCtx M E) uniq sa (wireQual (mkGCtx M E) uniq sc) with
    | none =>
      obtain ⟨p, h1, h2⟩ := v6Step_none hs1
      rw [huniq, hsc] at h1; rw [huniq, hsa] at h2
      exact v6_refute hME hnd hlt hlen 0 1 (by simp [ws]) (by simp [ws]) (by omega) p h1 h2
    | some s1 =>
      rw [hs1] at hv6; dsimp only at hv6
      have hspec1 := v6Step_some hs1
      cases hs2 : v6Step (mkGCtx M E) uniq sb s1 with
      | none =>
        obtain ⟨p, h1, h2⟩ := v6Step_none hs2
        rw [huniq, hsb] at h2
        rcases (hspec1 p).1 h1 with hc | ha
        · rw [huniq, hsc] at hc
          exact v6_refute hME hnd hlt hlen 0 2 (by simp [ws]) (by simp [ws]) (by omega) p hc h2
        · rw [huniq, hsa] at ha
          exact v6_refute hME hnd hlt hlen 1 2 (by simp [ws]) (by simp [ws]) (by omega) p ha h2
      | some s2 =>
        rw [hs2] at hv6; dsimp only at hv6
        have hspec2 := v6Step_some hs2
        have hlead : ∀ p, s2.testBit p = true →
            ∃ i, ∃ hi : i < [c, a, b].length, (wireQual (mkGCtx M E) uniq (sepSpec M E [c, a, b][i])).testBit p = true := by
          intro p hp
          rcases (hspec2 p).1 hp with h1 | hb
          · rcases (hspec1 p).1 h1 with hc | ha
            · exact ⟨0, by simp, by simpa [hsc] using hc⟩
            · exact ⟨1, by simp, by simpa [hsa] using ha⟩
          · exact ⟨2, by simp, by simpa [hsb] using hb⟩
        obtain ⟨i1, hi1, i2, hi2, hne, p, hq1, hq2⟩ := scanNodes_pair_hit hpref htail hlead hv6
        rw [huniq] at hq1 hq2
        exact v6_refute hME hnd hlt hlen i1 i2 hi1 hi2 hne p hq1 hq2

theorem checkHT_false {M E s : ℕ} {S : ℕ → ℕ → List ℕ} {N : ℕ → ℕ}
    {idx : ℕ → List ℕ → ℕ} {ori : List ℕ → List ℕ} {ns : List ℕ}
    (hori : ∀ k l, (∀ w ∈ l, w < 2 ^ (M + E)) → DLive M E k l.toFinset → DLive M E k (ori l).toFinset)
    (hS : ∀ j < N s, ¬ DLive M E s (S s j).toFinset)
    (hlt : ∀ w ∈ ns, w < 2 ^ (M + E))
    (hchk : checkHT S N idx ori s ns = false) :
    ¬ DLive M E s ns.toFinset := by
  unfold checkHT at hchk
  simp only [Bool.not_eq_false', Bool.and_eq_true, Nat.blt_eq] at hchk
  intro hdl
  have hdl' := hori s ns hlt hdl
  have hperm := isPermNat_sound hchk.2
  rw [perm_toFinset_eq hperm] at hdl'
  exact hS _ hchk.1 hdl'

theorem canReach_eq_true_of_ge2 {m c0 sa sb full : ℕ} :
    2 ≤ m →
    (match m with
     | 0 => Nat.beq c0 full
     | 1 => Nat.beq (c0 ||| sa) full || Nat.beq (c0 ||| sb) full
     | _ => true) = true := by
  cases m with | zero => omega | succ k => cases k with | zero => omega | succ _ => intro _; rfl

theorem canReach_eq_true_of_ge1_a {m c0 sa sb full : ℕ} :
    1 ≤ m → c0 ||| sa = full →
    (match m with
     | 0 => Nat.beq c0 full
     | 1 => Nat.beq (c0 ||| sa) full || Nat.beq (c0 ||| sb) full
     | _ => true) = true := by
  cases m with | zero => omega | succ k => cases k with | zero => intro _ h; simp [nat_beq_true.2 h] | succ _ => intro _ _; rfl

theorem canReach_eq_true_of_ge1_b {m c0 sa sb full : ℕ} :
    1 ≤ m → c0 ||| sb = full →
    (match m with
     | 0 => Nat.beq c0 full
     | 1 => Nat.beq (c0 ||| sa) full || Nat.beq (c0 ||| sb) full
     | _ => true) = true := by
  cases m with | zero => omega | succ k => cases k with | zero => intro _ h; simp [nat_beq_true.2 h] | succ _ => intro _ _; rfl

theorem canReach_eq_true_of_0 {m c0 sa sb full : ℕ} :
    c0 = full → c0 ||| sa = full →
    (match m with
     | 0 => Nat.beq c0 full
     | 1 => Nat.beq (c0 ||| sa) full || Nat.beq (c0 ||| sb) full
     | _ => true) = true := by
  cases m with
  | zero => intro h0 _; exact nat_beq_true.2 h0
  | succ k => cases k with | zero => intro _ h1; simp [nat_beq_true.2 h1] | succ _ => intro _ _; rfl

theorem tryOpV4_false {M E s maxKeep : ℕ} {S : ℕ → ℕ → List ℕ} {N : ℕ → ℕ}
    {idx : ℕ → List ℕ → ℕ} {ori : List ℕ → List ℕ}
    {pref tail : List WNode} {a ga sa b gb sb base1 base2 c sc : ℕ}
    (hME : validME M E = true)
    (hori : ∀ k l, (∀ w ∈ l, w < 2 ^ (M + E)) → DLive M E k l.toFinset → DLive M E k (ori l).toFinset)
    (hS : ∀ j < N s, ¬ DLive M E s (S s j).toFinset)
    (hpref : PrefOK M E pref) (htail : PrefOK M E tail)
    (hnd : (a :: b :: (pref.map (·.w) ++ tail.map (·.w))).Nodup)
    (hlt : ∀ w ∈ (a :: b :: (pref.map (·.w) ++ tail.map (·.w))), w < 2 ^ (M + E))
    (hlen_le : 2 + pref.length + tail.length ≤ s + 2)
    (hmax : maxKeep = s + 2 - (2 + pref.length + tail.length))
    (hga : ga = a ^^^ ((1 <<< M) - 1)) (hsa : sa = sepSpec M E a)
    (hgb : gb = b ^^^ ((1 <<< M) - 1)) (hsb : sb = sepSpec M E b)
    (hb1 : base1 = listC1 ((pref ++ tail).map (·.sw)))
    (hb2 : base2 = listC2 ((pref ++ tail).map (·.sw)))
    (hc_lt : c < 2 ^ (M + E)) (hsc : sc = sepSpec M E c)
    (htry : tryOpV4 (mkGCtx M E) maxKeep S N idx ori s pref tail a ga sa b gb sb base1 base2 c sc = false)
    (hdom_s : ∀ w ∈ (a :: b :: (pref.map (·.w) ++ tail.map (·.w))), domME M c w = false)
    (rest : Finset ℕ)
    (hs_eq : (a :: b :: (pref.map (·.w) ++ tail.map (·.w))).toFinset = insert a (insert b rest))
    (hrnd : ∀ w ∈ rest, domME M w c = false)
    (hdl : DLive M E s (insert c rest)) : False := by
  obtain ⟨hM1, hM9, hE2, hE10, _⟩ := validME_props hME
  have hEpos : 0 < E := by omega
  set ptW := pref.map (·.w) ++ tail.map (·.w)
  have hpt_sub_rest : ∀ w ∈ ptW, w ∈ rest := by
    intro w hw
    have hw_in : w ∈ insert a (insert b rest) := by
      rw [← hs_eq]; exact List.mem_toFinset.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
    have hnd_a := (List.nodup_cons.1 hnd).1
    have hnd_b := (List.nodup_cons.1 (List.nodup_cons.1 hnd).2).1
    have hwa : w ≠ a := fun e => hnd_a (e ▸ List.mem_cons_of_mem _ hw)
    have hwb : w ≠ b := fun e => hnd_b (e ▸ hw)
    rcases Finset.mem_insert.1 hw_in with rfl | hw_in'
    · exact absurd rfl hwa
    · rcases Finset.mem_insert.1 hw_in' with rfl | hwr
      · exact absurd rfl hwb
      · exact hwr
  have hrest_sub : ∀ w ∈ rest, w = a ∨ w = b ∨ w ∈ ptW := by
    intro w hw
    have hw_in : w ∈ (a :: b :: ptW).toFinset := by
      rw [hs_eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw)
    simpa using hw_in
  have hc_not_in : ∀ w ∈ (a :: b :: ptW), c ≠ w := by
    intro w hw heq; subst heq
    have := hdom_s c hw; rw [domME_refl] at this; exact Bool.noConfusion this
  have hnd_pt : ptW.Nodup := (List.nodup_cons.1 (List.nodup_cons.1 hnd).2).2
  have hlt_pt : ∀ w ∈ ptW, w < 2 ^ (M + E) := fun w hw => hlt w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
  have hlt_a : a < 2 ^ (M + E) := hlt a List.mem_cons_self
  have hlt_b : b < 2 ^ (M + E) := hlt b (List.mem_cons_of_mem _ List.mem_cons_self)
  have hbase1_eq : base1 = listC1 (ptW.map (sepSpec M E)) := by
    rw [hb1, List.map_append, hpref.map_sw, htail.map_sw, ← List.map_append]
  -- Establish dominance check is false!
  have hdom_false : (Nat.beq ((c ^^^ (mkGCtx M E).mMask) &&& ga) (c ^^^ (mkGCtx M E).mMask) ||
      Nat.beq ((c ^^^ (mkGCtx M E).mMask) &&& gb) (c ^^^ (mkGCtx M E).mMask) ||
      anyDomBoth (c ^^^ (mkGCtx M E).mMask) pref || anyDomBoth (c ^^^ (mkGCtx M E).mMask) tail) = false := by
    have hca : Nat.beq ((c ^^^ ((1 <<< M) - 1)) &&& ga) (c ^^^ ((1 <<< M) - 1)) = false := by
      rw [hga]; exact hdom_s a List.mem_cons_self
    have hcb : Nat.beq ((c ^^^ ((1 <<< M) - 1)) &&& gb) (c ^^^ ((1 <<< M) - 1)) = false := by
      rw [hgb]; exact hdom_s b (List.mem_cons_of_mem _ List.mem_cons_self)
    have hdp : anyDomBoth (c ^^^ ((1 <<< M) - 1)) pref = false := by
      apply anyDomBoth_false hpref
      intro p hp
      have hpw : p.w ∈ ptW := List.mem_append_left _ (List.mem_map.2 ⟨p, hp, rfl⟩)
      exact ⟨hdom_s p.w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hpw)), hrnd p.w (hpt_sub_rest p.w hpw)⟩
    have hdt : anyDomBoth (c ^^^ ((1 <<< M) - 1)) tail = false := by
      apply anyDomBoth_false htail
      intro p hp
      have hpw : p.w ∈ ptW := List.mem_append_right _ (List.mem_map.2 ⟨p, hp, rfl⟩)
      exact ⟨hdom_s p.w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hpw)), hrnd p.w (hpt_sub_rest p.w hpw)⟩
    simp [mkGCtx, hca, hcb, hdp, hdt]
  -- Helper: split into 4 cases of (a ∈ rest, b ∈ rest)
  have hptW_len : ptW.length = pref.length + tail.length := by simp [ptW]
  have hcol_fin : (collectW (collectW [] tail) pref).toFinset = ptW.toFinset := collectW_toFinset pref tail
  by_cases ha_r : a ∈ rest <;> by_cases hb_r : b ∈ rest
  · -- Case (true, true): insert c rest = (c :: a :: b :: ptW).toFinset
    have hfin : insert c rest = (c :: a :: b :: ptW).toFinset := by
      ext w; simp only [Finset.mem_insert, List.mem_toFinset, List.mem_cons]
      constructor
      · rintro (rfl | hw)
        · exact Or.inl rfl
        · exact Or.inr (hrest_sub w hw)
      · rintro (rfl | rfl | rfl | hw)
        · exact Or.inl rfl
        · exact Or.inr ha_r
        · exact Or.inr hb_r
        · exact Or.inr (hpt_sub_rest w hw)
    have hnd2 : (c :: a :: b :: ptW).Nodup := List.nodup_cons.2 ⟨fun h => hc_not_in c h rfl, hnd⟩
    have hlt2 : ∀ w ∈ (c :: a :: b :: ptW), w < 2 ^ (M + E) := fun w hw => by
      rcases List.mem_cons.1 hw with rfl | hw'
      · exact hc_lt
      · exact hlt w hw'
    rw [hfin] at hdl
    have hcard := dlive_card hdl
    rw [List.toFinset_card_of_nodup hnd2] at hcard
    have hmk2 : 2 ≤ maxKeep := by simp [hptW_len] at hcard; omega
    have hfull2 : base1 ||| sc ||| sa ||| sb = (mkGCtx M E).full := by
      have hf := dlive_listC1_full hME hlt2 hdl
      simp only [List.map_cons, listC1, ← hsc, ← hsa, ← hsb, ← hbase1_eq] at hf
      show base1 ||| sc ||| sa ||| sb = (1 <<< (M * E)) - 1
      rw [← hf]
      apply Nat.eq_of_testBit_eq; intro p; simp only [Nat.testBit_or]
      cases base1.testBit p <;> cases sc.testBit p <;> cases sa.testBit p <;> cases sb.testBit p <;> rfl
    have hcanA : Nat.beq (ga &&& (c ^^^ (mkGCtx M E).mMask)) ga = false := by
      rw [hga]; exact hrnd a ha_r
    have hcanB : Nat.beq (gb &&& (c ^^^ (mkGCtx M E).mMask)) gb = false := by
      rw [hgb]; exact hrnd b hb_r
    unfold tryOpV4 at htry
    have hreach := canReach_eq_true_of_ge2 (c0 := base1 ||| sc) (sa := sa) (sb := sb) (full := (mkGCtx M E).full) hmk2
    dsimp only at htry
    rw [hreach, hdom_false] at htry; dsimp only at htry
    have hble1 : Nat.ble 1 maxKeep = true := by rw [Nat.ble_eq]; omega
    have hble2 : Nat.ble 2 maxKeep = true := by rw [Nat.ble_eq]; omega
    have hbr2 : (match Nat.beq maxKeep 2 && v6Check2 (mkGCtx M E) base1 base2 sc sa sb pref tail with
        | true => false
        | false => checkHT S N idx ori s (c :: a :: b :: collectW (collectW [] tail) pref)) = false := by
      simp only [hble1, hble2, hcanA, hcanB, nat_beq_true.2 hfull2, Bool.not_false, Bool.true_and, Bool.and_true, Bool.or_eq_false_iff] at htry
      exact htry.2.2
    cases hv6 : (Nat.beq maxKeep 2 && v6Check2 (mkGCtx M E) base1 base2 sc sa sb pref tail) with
    | true =>
      simp only [Bool.and_eq_true, nat_beq_true] at hv6
      exact v6Check2_no hME hpref htail hsc hsa hsb hb1 hb2 hnd2 hlt2 (by simp [hptW_len]; omega) hv6.2 hdl
    | false =>
      rw [hv6] at hbr2; dsimp only at hbr2
      have hdl' : DLive M E s (c :: a :: b :: collectW (collectW [] tail) pref).toFinset := by
        simpa [List.toFinset_cons, hcol_fin] using hdl
      have hlt_col : ∀ w ∈ (c :: a :: b :: collectW (collectW [] tail) pref), w < 2 ^ (M + E) := fun w hw => by
        have hw' : w ∈ (c :: a :: b :: ptW).toFinset := by
          have := List.mem_toFinset.2 hw; simpa [List.toFinset_cons, hcol_fin] using this
        exact hlt2 w (List.mem_toFinset.1 hw')
      exact checkHT_false hori hS hlt_col hbr2 hdl'
  · -- Case (true, false): insert c rest = (c :: a :: ptW).toFinset
    have hfin : insert c rest = (c :: a :: ptW).toFinset := by
      ext w; simp only [Finset.mem_insert, List.mem_toFinset, List.mem_cons]
      constructor
      · rintro (rfl | hw)
        · exact Or.inl rfl
        · rcases hrest_sub w hw with rfl | rfl | hw'
          · exact Or.inr (Or.inl rfl)
          · exact absurd hw hb_r
          · exact Or.inr (Or.inr hw')
      · rintro (rfl | rfl | hw)
        · exact Or.inl rfl
        · exact Or.inr ha_r
        · exact Or.inr (hpt_sub_rest w hw)
    have hnd1a : (c :: a :: ptW).Nodup :=
      List.nodup_cons.2 ⟨fun h => by
        rcases List.mem_cons.1 h with rfl | h'
        · exact hc_not_in c List.mem_cons_self rfl
        · exact hc_not_in c (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h')) rfl,
        List.nodup_cons.2 ⟨fun h => (List.nodup_cons.1 hnd).1 (List.mem_cons_of_mem _ h), hnd_pt⟩⟩
    have hlt1a : ∀ w ∈ (c :: a :: ptW), w < 2 ^ (M + E) := fun w hw => by
      rcases List.mem_cons.1 hw with rfl | hw'
      · exact hc_lt
      · rcases List.mem_cons.1 hw' with rfl | hw''
        · exact hlt_a
        · exact hlt_pt w hw''
    rw [hfin] at hdl
    have hcard := dlive_card hdl
    rw [List.toFinset_card_of_nodup hnd1a] at hcard
    have hmk1 : 1 ≤ maxKeep := by simp [hptW_len] at hcard; omega
    have hfull1a : base1 ||| sc ||| sa = (mkGCtx M E).full := by
      have hf := dlive_listC1_full hME hlt1a hdl
      simp only [List.map_cons, listC1, ← hsc, ← hsa, ← hbase1_eq] at hf
      show base1 ||| sc ||| sa = (1 <<< (M * E)) - 1
      rw [← hf]
      apply Nat.eq_of_testBit_eq; intro p; simp only [Nat.testBit_or]
      cases base1.testBit p <;> cases sc.testBit p <;> cases sa.testBit p <;> rfl
    have hcanA : Nat.beq (ga &&& (c ^^^ (mkGCtx M E).mMask)) ga = false := by
      rw [hga]; exact hrnd a ha_r
    unfold tryOpV4 at htry
    have hreach := canReach_eq_true_of_ge1_a (sb := sb) hmk1 hfull1a
    dsimp only at htry
    rw [hreach, hdom_false] at htry; dsimp only at htry
    have hble1 : Nat.ble 1 maxKeep = true := by rw [Nat.ble_eq]; omega
    have hbr1a : (match Nat.beq maxKeep 1 && v6Check1 (mkGCtx M E) base1 base2 sc sa pref tail with
        | true => false
        | false => checkHT S N idx ori s (c :: a :: collectW (collectW [] tail) pref)) = false := by
      simp only [hble1, hcanA, nat_beq_true.2 hfull1a, Bool.not_false, Bool.true_and, Bool.and_true, Bool.or_eq_false_iff] at htry
      exact htry.2.1.1
    cases hv6 : (Nat.beq maxKeep 1 && v6Check1 (mkGCtx M E) base1 base2 sc sa pref tail) with
    | true =>
      simp only [Bool.and_eq_true, nat_beq_true] at hv6
      exact v6Check1_no hME hpref htail hsc hsa hb1 hb2 hnd1a hlt1a (by simp [hptW_len]; omega) hv6.2 hdl
    | false =>
      rw [hv6] at hbr1a; dsimp only at hbr1a
      have hdl' : DLive M E s (c :: a :: collectW (collectW [] tail) pref).toFinset := by
        simpa [List.toFinset_cons, hcol_fin] using hdl
      have hlt_col : ∀ w ∈ (c :: a :: collectW (collectW [] tail) pref), w < 2 ^ (M + E) := fun w hw => by
        have hw' : w ∈ (c :: a :: ptW).toFinset := by
          have := List.mem_toFinset.2 hw; simpa [List.toFinset_cons, hcol_fin] using this
        exact hlt1a w (List.mem_toFinset.1 hw')
      exact checkHT_false hori hS hlt_col hbr1a hdl'
  · -- Case (false, true): insert c rest = (c :: b :: ptW).toFinset
    have hfin : insert c rest = (c :: b :: ptW).toFinset := by
      ext w; simp only [Finset.mem_insert, List.mem_toFinset, List.mem_cons]
      constructor
      · rintro (rfl | hw)
        · exact Or.inl rfl
        · rcases hrest_sub w hw with rfl | rfl | hw'
          · exact absurd hw ha_r
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr hw')
      · rintro (rfl | rfl | hw)
        · exact Or.inl rfl
        · exact Or.inr hb_r
        · exact Or.inr (hpt_sub_rest w hw)
    have hnd1b : (c :: b :: ptW).Nodup :=
      List.nodup_cons.2 ⟨fun h => hc_not_in c (List.mem_cons_of_mem _ h) rfl, (List.nodup_cons.1 hnd).2⟩
    have hlt1b : ∀ w ∈ (c :: b :: ptW), w < 2 ^ (M + E) := fun w hw => by
      rcases List.mem_cons.1 hw with rfl | hw'
      · exact hc_lt
      · exact hlt w (List.mem_cons_of_mem _ hw')
    rw [hfin] at hdl
    have hcard := dlive_card hdl
    rw [List.toFinset_card_of_nodup hnd1b] at hcard
    have hmk1 : 1 ≤ maxKeep := by simp [hptW_len] at hcard; omega
    have hfull1b : base1 ||| sc ||| sb = (mkGCtx M E).full := by
      have hf := dlive_listC1_full hME hlt1b hdl
      simp only [List.map_cons, listC1, ← hsc, ← hsb, ← hbase1_eq] at hf
      show base1 ||| sc ||| sb = (1 <<< (M * E)) - 1
      rw [← hf]
      apply Nat.eq_of_testBit_eq; intro p; simp only [Nat.testBit_or]
      cases base1.testBit p <;> cases sc.testBit p <;> cases sb.testBit p <;> rfl
    have hcanB : Nat.beq (gb &&& (c ^^^ (mkGCtx M E).mMask)) gb = false := by
      rw [hgb]; exact hrnd b hb_r
    unfold tryOpV4 at htry
    have hreach := canReach_eq_true_of_ge1_b (sa := sa) hmk1 hfull1b
    dsimp only at htry
    rw [hreach, hdom_false] at htry; dsimp only at htry
    have hble1 : Nat.ble 1 maxKeep = true := by rw [Nat.ble_eq]; omega
    have hbr1b : (match Nat.beq maxKeep 1 && v6Check1 (mkGCtx M E) base1 base2 sc sb pref tail with
        | true => false
        | false => checkHT S N idx ori s (c :: b :: collectW (collectW [] tail) pref)) = false := by
      simp only [hble1, hcanB, nat_beq_true.2 hfull1b, Bool.not_false, Bool.true_and, Bool.and_true, Bool.or_eq_false_iff] at htry
      exact htry.2.1.2
    cases hv6 : (Nat.beq maxKeep 1 && v6Check1 (mkGCtx M E) base1 base2 sc sb pref tail) with
    | true =>
      simp only [Bool.and_eq_true, nat_beq_true] at hv6
      exact v6Check1_no hME hpref htail hsc hsb hb1 hb2 hnd1b hlt1b (by simp [hptW_len]; omega) hv6.2 hdl
    | false =>
      rw [hv6] at hbr1b; dsimp only at hbr1b
      have hdl' : DLive M E s (c :: b :: collectW (collectW [] tail) pref).toFinset := by
        simpa [List.toFinset_cons, hcol_fin] using hdl
      have hlt_col : ∀ w ∈ (c :: b :: collectW (collectW [] tail) pref), w < 2 ^ (M + E) := fun w hw => by
        have hw' : w ∈ (c :: b :: ptW).toFinset := by
          have := List.mem_toFinset.2 hw; simpa [List.toFinset_cons, hcol_fin] using this
        exact hlt1b w (List.mem_toFinset.1 hw')
      exact checkHT_false hori hS hlt_col hbr1b hdl'
  · -- Case (false, false): insert c rest = (c :: ptW).toFinset
    have hfin : insert c rest = (c :: ptW).toFinset := by
      ext w; simp only [Finset.mem_insert, List.mem_toFinset, List.mem_cons]
      constructor
      · rintro (rfl | hw)
        · exact Or.inl rfl
        · rcases hrest_sub w hw with rfl | rfl | hw'
          · exact absurd hw ha_r
          · exact absurd hw hb_r
          · exact Or.inr hw'
      · rintro (rfl | hw)
        · exact Or.inl rfl
        · exact Or.inr (hpt_sub_rest w hw)
    have hnd0 : (c :: ptW).Nodup :=
      List.nodup_cons.2 ⟨fun h => hc_not_in c (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)) rfl, hnd_pt⟩
    have hlt0 : ∀ w ∈ (c :: ptW), w < 2 ^ (M + E) := fun w hw => by
      rcases List.mem_cons.1 hw with rfl | hw'
      · exact hc_lt
      · exact hlt_pt w hw'
    rw [hfin] at hdl
    have hfull0 : base1 ||| sc = (mkGCtx M E).full := by
      have hf := dlive_listC1_full hME hlt0 hdl
      simp only [List.map_cons, listC1, ← hsc, ← hbase1_eq] at hf
      show base1 ||| sc = (1 <<< (M * E)) - 1
      rw [Nat.or_comm]; exact hf
    unfold tryOpV4 at htry
    have hfull1a : base1 ||| sc ||| sa = (mkGCtx M E).full :=
      or_full_of_lt hfull0 (hsa ▸ sepSpec_lt hEpos hlt_a)
    have hreach := canReach_eq_true_of_0 (m := maxKeep) (sb := sb) hfull0 hfull1a
    dsimp only at htry
    rw [hreach, hdom_false] at htry; dsimp only at htry
    simp only [Bool.or_eq_false_iff] at htry
    have hbr0 := htry.1
    rw [nat_beq_true.2 hfull0, Bool.true_and] at hbr0
    cases hv6 : (Nat.beq maxKeep 0 && v6Check0 (mkGCtx M E) base1 base2 sc pref tail) with
    | true =>
      simp only [Bool.and_eq_true, nat_beq_true] at hv6
      exact v6Check0_no hME hpref htail hsc hb1 hb2 hnd0 hlt0 (by simp [hptW_len]; omega) hv6.2 hdl
    | false =>
      rw [hv6] at hbr0; dsimp only at hbr0
      have hdl' : DLive M E s (c :: collectW (collectW [] tail) pref).toFinset := by
        simpa [List.toFinset_cons, hcol_fin] using hdl
      have hlt_col : ∀ w ∈ (c :: collectW (collectW [] tail) pref), w < 2 ^ (M + E) := fun w hw => by
        have hw' : w ∈ (c :: ptW).toFinset := by
          have := List.mem_toFinset.2 hw; simpa [List.toFinset_cons, hcol_fin] using this
        exact hlt0 w (List.mem_toFinset.1 hw')
      exact checkHT_false hori hS hlt_col hbr0 hdl'

theorem loopPairBV4_false {M E s maxKeep : ℕ} {S : ℕ → ℕ → List ℕ} {N : ℕ → ℕ}
    {idx : ℕ → List ℕ → ℕ} {ori : List ℕ → List ℕ}
    (hME : validME M E = true)
    (hori : ∀ k l, (∀ w ∈ l, w < 2 ^ (M + E)) → DLive M E k l.toFinset → DLive M E k (ori l).toFinset)
    (hS : ∀ j < N s, ¬ DLive M E s (S s j).toFinset)
    {a ga sa : ℕ} (hga : ga = a ^^^ ((1 <<< M) - 1)) (hsa : sa = sepSpec M E a) :
    ∀ (pref tail : List WNode) (p1 p2 : ℕ),
      PrefOK M E pref → NodesOK M E tail →
      p1 = listC1 (pref.map (·.sw)) → p2 = listC2 (pref.map (·.sw)) →
      (a :: (pref.map (·.w) ++ tail.map (·.w))).Nodup →
      (∀ w ∈ (a :: (pref.map (·.w) ++ tail.map (·.w))), w < 2 ^ (M + E)) →
      1 + pref.length + tail.length ≤ s + 2 →
      maxKeep = s + 2 - (1 + pref.length + tail.length) →
      loopPairBV4 (mkGCtx M E) maxKeep S N idx ori s a ga sa pref p1 p2 tail = false →
      ∀ b ∈ tail.map (·.w), ∀ conj : Bool,
        let z := if conj then a &&& b else a ||| b
        goodME M z = true →
        (∀ w ∈ (a :: (pref.map (·.w) ++ tail.map (·.w))), domME M z w = false) →
        ∀ rest : Finset ℕ,
          (a :: (pref.map (·.w) ++ tail.map (·.w))).toFinset = insert a (insert b rest) →
          (∀ w ∈ rest, domME M w z = false) →
          DLive M E s (insert z rest) → False := by
  intro pref tail
  induction tail generalizing pref with
  | nil => intro _ _ _ _ _ _ _ _ _ _ _ b hb; simp at hb
  | cons nb tail' ih =>
    intro p1 p2 hpref htail hp1 hp2 hnd hlt hlen hmax hloop b hb conj z hgz hdom rest hs_eq hrnd hdl
    obtain ⟨hnb_gw, hnb_sw, hnb_tc1, hnb_tc2, htail'⟩ := htail
    simp only [loopPairBV4, Bool.or_eq_false_iff] at hloop
    obtain ⟨hokAnd, hokOr, hrec⟩ := hloop
    have hperm_ab : (a :: nb.w :: (pref.map (·.w) ++ tail'.map (·.w))).Perm
        (a :: (pref.map (·.w) ++ (nb :: tail').map (·.w))) := by
      simp only [List.map_cons]
      exact List.Perm.cons a (List.perm_middle.symm)
    rcases List.mem_cons.1 hb with rfl | hb'
    · -- b = nb.w
      have hnd_ab : (a :: nb.w :: (pref.map (·.w) ++ tail'.map (·.w))).Nodup :=
        (List.Perm.nodup_iff hperm_ab).2 hnd
      have hlt_ab : ∀ w ∈ (a :: nb.w :: (pref.map (·.w) ++ tail'.map (·.w))), w < 2 ^ (M + E) :=
        fun w hw => hlt w (hperm_ab.subset hw)
      have hdom_ab : ∀ w ∈ (a :: nb.w :: (pref.map (·.w) ++ tail'.map (·.w))), domME M z w = false :=
        fun w hw => hdom w (hperm_ab.subset hw)
      have hs_ab : (a :: nb.w :: (pref.map (·.w) ++ tail'.map (·.w))).toFinset = insert a (insert nb.w rest) := by
        rw [perm_toFinset_eq hperm_ab]; exact hs_eq
      have hbase1 : p1 ||| nb.tc1 = listC1 ((pref ++ tail').map (·.sw)) := by
        rw [hp1, hnb_tc1, List.map_append, listC1_append]
      have hbase2 : p2 ||| nb.tc2 ||| (p1 &&& nb.tc1) = listC2 ((pref ++ tail').map (·.sw)) := by
        rw [hp2, hnb_tc2, hp1, hnb_tc1, List.map_append, listC2_append]
      have hlt_a : a < 2 ^ (M + E) := hlt a List.mem_cons_self
      have hlt_b : nb.w < 2 ^ (M + E) := hlt_ab nb.w (List.mem_cons_of_mem _ List.mem_cons_self)
      cases conj with
      | true =>
        have hgood_and : (!(Nat.beq ((a &&& nb.w) >>> (mkGCtx M E).M) 0) &&
            !(Nat.beq ((a &&& nb.w) &&& (mkGCtx M E).mMask) (mkGCtx M E).mMask)) = true := hgz
        rw [hgood_and, Bool.true_and] at hokAnd
        have hsc : (sa ||| nb.sw) &&& (((a &&& nb.w) >>> (mkGCtx M E).M) * (mkGCtx M E).loCol) =
            sepSpec M E (a &&& nb.w) := by
          rw [hsa, hnb_sw]; exact scand_eq_sepSpec hME hlt_a hlt_b
        exact tryOpV4_false hME hori hS hpref htail'.toPrefOK hnd_ab hlt_ab (by simp at hlen; omega)
          (by simp at hmax; omega) hga hsa hnb_gw hnb_sw hbase1 hbase2 (and_lt_pow hlt_a) hsc
          hokAnd hdom_ab rest hs_ab hrnd hdl
      | false =>
        have hgz' : (!(Nat.beq ((a ||| nb.w) >>> (mkGCtx M E).M) 0) &&
            !(Nat.beq ((a ||| nb.w) &&& (mkGCtx M E).mMask) (mkGCtx M E).mMask)) = true := hgz
        have hgood_or : (!(Nat.beq ((a ||| nb.w) &&& (mkGCtx M E).mMask) (mkGCtx M E).mMask) &&
            !(Nat.beq ((a ||| nb.w) >>> (mkGCtx M E).M) 0)) = true := by
          rw [Bool.and_comm]; exact hgz'
        rw [hgood_or, Bool.true_and] at hokOr
        have hsc : sepFast (mkGCtx M E).M (mkGCtx M E).E (mkGCtx M E).mMask (mkGCtx M E).tab
            (mkGCtx M E).e4 (mkGCtx M E).mask4 (a ||| nb.w) =
            sepSpec M E (a ||| nb.w) := sepFast_eq_sepSpec hME
        exact tryOpV4_false hME hori hS hpref htail'.toPrefOK hnd_ab hlt_ab (by simp at hlen; omega)
          (by simp at hmax; omega) hga hsa hnb_gw hnb_sw hbase1 hbase2 (or_lt_pow hlt_a hlt_b) hsc
          hokOr hdom_ab rest hs_ab hrnd hdl
    · -- b ∈ tail'.map (·.w)
      have hpref' : PrefOK M E (nb :: pref) := fun p hp => by
        rcases List.mem_cons.1 hp with rfl | hp'
        · exact ⟨hnb_gw, hnb_sw⟩
        · exact hpref p hp'
      have hp1' : p1 ||| nb.sw = listC1 ((nb :: pref).map (·.sw)) := by
        simp [listC1, hp1, Nat.or_comm]
      have hp2' : p2 ||| (p1 &&& nb.sw) = listC2 ((nb :: pref).map (·.sw)) := by
        simp [listC2, hp1, hp2, Nat.and_comm]
      have hnd' : (a :: ((nb :: pref).map (·.w) ++ tail'.map (·.w))).Nodup :=
        (List.Perm.nodup_iff hperm_ab).2 hnd
      have hlt' : ∀ w ∈ (a :: ((nb :: pref).map (·.w) ++ tail'.map (·.w))), w < 2 ^ (M + E) :=
        fun w hw => hlt w (hperm_ab.subset hw)
      have hdom' : ∀ w ∈ (a :: ((nb :: pref).map (·.w) ++ tail'.map (·.w))), domME M z w = false :=
        fun w hw => hdom w (hperm_ab.subset hw)
      have hs' : (a :: ((nb :: pref).map (·.w) ++ tail'.map (·.w))).toFinset = insert a (insert b rest) := by
        simp only [List.map_cons, List.cons_append]; rw [perm_toFinset_eq hperm_ab]; exact hs_eq
      exact ih (nb :: pref) (p1 ||| nb.sw) (p2 ||| (p1 &&& nb.sw)) hpref' htail' hp1' hp2'
        hnd' hlt' (by simp at hlen ⊢; omega) (by simp at hmax ⊢; omega) hrec b hb' conj hgz hdom' rest hs' hrnd hdl

theorem loopPairAV4_false {M E s maxKeep : ℕ} {S : ℕ → ℕ → List ℕ} {N : ℕ → ℕ}
    {idx : ℕ → List ℕ → ℕ} {ori : List ℕ → List ℕ}
    (hME : validME M E = true)
    (hori : ∀ k l, (∀ w ∈ l, w < 2 ^ (M + E)) → DLive M E k l.toFinset → DLive M E k (ori l).toFinset)
    (hS : ∀ j < N s, ¬ DLive M E s (S s j).toFinset) :
    ∀ (pref nodes : List WNode) (p1 p2 : ℕ),
      PrefOK M E pref → NodesOK M E nodes →
      p1 = listC1 (pref.map (·.sw)) → p2 = listC2 (pref.map (·.sw)) →
      (pref.map (·.w) ++ nodes.map (·.w)).Nodup →
      (∀ w ∈ (pref.map (·.w) ++ nodes.map (·.w)), w < 2 ^ (M + E)) →
      pref.length + nodes.length ≤ s + 2 →
      maxKeep = s + 2 - (pref.length + nodes.length) →
      loopPairAV4 (mkGCtx M E) maxKeep S N idx ori s pref p1 p2 nodes = false →
      ∀ a ∈ nodes.map (·.w), ∀ b ∈ nodes.map (·.w), a ≠ b → ∀ conj : Bool,
        let z := if conj then a &&& b else a ||| b
        goodME M z = true →
        (∀ w ∈ (pref.map (·.w) ++ nodes.map (·.w)), domME M z w = false) →
        ∀ rest : Finset ℕ,
          (pref.map (·.w) ++ nodes.map (·.w)).toFinset = insert a (insert b rest) →
          (∀ w ∈ rest, domME M w z = false) →
          DLive M E s (insert z rest) → False := by
  intro pref nodes
  induction nodes generalizing pref with
  | nil => intro _ _ _ _ _ _ _ _ _ _ _ a ha; simp at ha
  | cons na tail ih =>
    intro p1 p2 hpref hnodes hp1 hp2 hnd hlt hlen hmax hloop a ha b hb hab conj z hgz hdom rest hs_eq hrnd hdl
    obtain ⟨hna_gw, hna_sw, _, _, htail⟩ := hnodes
    simp only [loopPairAV4, Bool.or_eq_false_iff] at hloop
    obtain ⟨hB, hA⟩ := hloop
    have hperm_a : (na.w :: (pref.map (·.w) ++ tail.map (·.w))).Perm
        (pref.map (·.w) ++ (na :: tail).map (·.w)) := by
      simp only [List.map_cons]
      exact List.perm_middle.symm
    rcases List.mem_cons.1 ha with rfl | ha'
    · -- a = na.w, so b ∈ tail.map (·.w)
      have hb' : b ∈ tail.map (·.w) := (List.mem_cons.1 hb).resolve_left (Ne.symm hab)
      have hnd_a := (List.Perm.nodup_iff hperm_a).2 hnd
      have hlt_a : ∀ w ∈ (na.w :: (pref.map (·.w) ++ tail.map (·.w))), w < 2 ^ (M + E) :=
        fun w hw => hlt w (hperm_a.subset hw)
      have hdom_a : ∀ w ∈ (na.w :: (pref.map (·.w) ++ tail.map (·.w))), domME M z w = false :=
        fun w hw => hdom w (hperm_a.subset hw)
      have hs_a : (na.w :: (pref.map (·.w) ++ tail.map (·.w))).toFinset = insert na.w (insert b rest) := by
        rw [perm_toFinset_eq hperm_a]; exact hs_eq
      exact loopPairBV4_false hME hori hS hna_gw hna_sw pref tail p1 p2 hpref htail hp1 hp2
        hnd_a hlt_a (by simp at hlen; omega) (by simp at hmax; omega) hB b hb' conj hgz hdom_a rest hs_a hrnd hdl
    · rcases List.mem_cons.1 hb with rfl | hb'
      · -- b = na.w, a ∈ tail.map (·.w): swap a and b using commutativity!
        have hz_swap : z = if conj then na.w &&& a else na.w ||| a := by
          cases conj <;> simp [z, Nat.and_comm, Nat.or_comm]
        have hnd_b := (List.Perm.nodup_iff hperm_a).2 hnd
        have hlt_b : ∀ w ∈ (na.w :: (pref.map (·.w) ++ tail.map (·.w))), w < 2 ^ (M + E) :=
          fun w hw => hlt w (hperm_a.subset hw)
        have hdom_b : ∀ w ∈ (na.w :: (pref.map (·.w) ++ tail.map (·.w))), domME M z w = false :=
          fun w hw => hdom w (hperm_a.subset hw)
        have hs_b : (na.w :: (pref.map (·.w) ++ tail.map (·.w))).toFinset = insert na.w (insert a rest) := by
          rw [perm_toFinset_eq hperm_a, Finset.insert_comm]; exact hs_eq
        rw [hz_swap] at hgz hdom_b hrnd hdl
        exact loopPairBV4_false hME hori hS hna_gw hna_sw pref tail p1 p2 hpref htail hp1 hp2
          hnd_b hlt_b (by simp at hlen; omega) (by simp at hmax; omega) hB a ha' conj hgz hdom_b rest hs_b hrnd hdl
      · -- Both a, b ∈ tail.map (·.w)
        have hpref' : PrefOK M E (na :: pref) := fun p hp => by
          rcases List.mem_cons.1 hp with rfl | hp'
          · exact ⟨hna_gw, hna_sw⟩
          · exact hpref p hp'
        have hp1' : p1 ||| na.sw = listC1 ((na :: pref).map (·.sw)) := by
          simp [listC1, hp1, Nat.or_comm]
        have hp2' : p2 ||| (p1 &&& na.sw) = listC2 ((na :: pref).map (·.sw)) := by
          simp [listC2, hp1, hp2, Nat.and_comm]
        have hnd' := (List.Perm.nodup_iff hperm_a).2 hnd
        have hlt' : ∀ w ∈ ((na :: pref).map (·.w) ++ tail.map (·.w)), w < 2 ^ (M + E) :=
          fun w hw => hlt w (hperm_a.subset hw)
        have hdom' : ∀ w ∈ ((na :: pref).map (·.w) ++ tail.map (·.w)), domME M z w = false :=
          fun w hw => hdom w (hperm_a.subset hw)
        have hs' : ((na :: pref).map (·.w) ++ tail.map (·.w)).toFinset = insert a (insert b rest) := by
          simp only [List.map_cons, List.cons_append]; rw [perm_toFinset_eq hperm_a]; exact hs_eq
        exact ih (na :: pref) (p1 ||| na.sw) (p2 ||| (p1 &&& na.sw)) hpref' htail hp1' hp2'
          hnd' hlt' (by simp at hlen ⊢; omega) (by simp at hmax ⊢; omega) hA a ha' b hb' hab conj hgz hdom' rest hs' hrnd hdl

theorem nodup_toFinset_eq_singleton {ws : List ℕ} {g : ℕ} (hnd : ws.Nodup) (h : ws.toFinset = {g}) :
    ws = [g] := by
  have hlen : ws.length = 1 := by
    have := congrArg Finset.card h
    rw [List.toFinset_card_of_nodup hnd, Finset.card_singleton] at this
    exact this
  cases ws with
  | nil => simp at hlen
  | cons x t =>
    cases t with
    | cons _ _ => simp at hlen
    | nil =>
      have hx : x ∈ ({g} : Finset ℕ) := by rw [← h]; simp
      simp only [Finset.mem_singleton] at hx
      subst hx; rfl

theorem barV3_all {M E : ℕ} (hME : validME M E = true)
    (S : ℕ → ℕ → List ℕ) (N : ℕ → ℕ)
    (idx : ℕ → List ℕ → ℕ) (ori : List ℕ → List ℕ)
    (hori : ∀ k l, (∀ w ∈ l, w < 2 ^ (M + E)) → DLive M E k l.toFinset → DLive M E k (ori l).toFinset)
    (cap : ℕ)
    (hbar : ∀ s ≤ cap, ∀ i < N s, barV3 M E S N idx ori s i = true) :
    ∀ s ≤ cap, ∀ i < N s, ¬ DLive M E s (S s i).toFinset := by
  intro s
  induction s with
  | zero =>
    intro _ i hi hdl
    have hb := hbar 0 (Nat.zero_le _) i hi
    simp only [barV3, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at hb
    have hnd := nodupNat_sound hb.1
    have hws := nodup_toFinset_eq_singleton hnd hdl
    exact hb.2 hws
  | succ s ih =>
    intro hs i hi hdl
    have hb := hbar (s + 1) hs i hi
    simp only [barV3, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at hb
    obtain ⟨⟨⟨halt, hndb⟩, hneq⟩, hloop⟩ := hb
    have hnd := nodupNat_sound hndb
    have hlt_shift : ∀ w ∈ S (s + 1) i, w < 1 <<< (M + E) := allLt_sound halt
    have hlt : ∀ w ∈ S (s + 1) i, w < 2 ^ (M + E) := fun w hw => by
      have := hlt_shift w hw; rwa [Nat.shiftLeft_eq, one_mul] at this
    have hcard := dlive_card hdl
    rw [List.toFinset_card_of_nodup hnd] at hcard
    rcases first_dlive hdl with hdone | ⟨a, ha, b, hb', hab, conj, hgz, hdom, rest, hs_eq, hrnd, htail_dl⟩
    · exact hneq (nodup_toFinset_eq_singleton hnd hdone)
    · set nodes := buildNodes (mkGCtx M E) (S (s + 1) i)
      have hmap : nodes.map (·.w) = S (s + 1) i := buildNodes_map_w (mkGCtx M E) (S (s + 1) i)
      have hlen_nodes : nodes.length = (S (s + 1) i).length := by
        rw [← hmap, List.length_map]
      have hS_ih : ∀ j < N s, ¬ DLive M E s (S s j).toFinset := ih (by omega)
      have hpref0 : PrefOK M E [] := fun _ h => by simp at h
      have hnodes_ok : NodesOK M E nodes := buildNodes_ok hME (S (s + 1) i)
      exact loopPairAV4_false hME hori hS_ih [] nodes 0 0 hpref0 hnodes_ok rfl rfl
        (by simpa [hmap] using hnd)
        (by simpa [hmap] using hlt)
        (by simp [hlen_nodes]; omega)
        (by simp [hlen_nodes])
        hloop a (by rw [hmap]; exact List.mem_toFinset.1 ha) b (by rw [hmap]; exact List.mem_toFinset.1 hb')
        hab conj hgz
        (by simpa [hmap] using fun w hw => hdom w (List.mem_toFinset.2 hw))
        rest (by simpa [hmap] using hs_eq) hrnd htail_dl

-- Section 2g: Circuit -> CleanML -> MBuild -> DBuild -> DLive -> Barrier!

def initIdStats (n : ℕ) : List Stat := List.ofFn fun i : Fin n => Sum.inr i.val

theorem inv_initId (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (initIdStats n, []) := by
  refine ⟨by simp [initIdStats], ?_⟩
  intro i
  by_cases hi : i < n
  · simp [initIdStats, hi, statValid, statVal, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [initIdStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

theorem mbuild_add {M E : ℕ} : ∀ {k s : ℕ} {A : Finset ℕ}, MBuild M E k A → k ≤ s → MBuild M E s A
  | 0, 0, _, h, _ => h
  | 0, s + 1, _, h, _ => Or.inl (mbuild_add h (Nat.zero_le _))
  | k + 1, s + 1, _, h, hle => by
    by_cases heq : k = s
    · subst heq; exact h
    · exact Or.inl (mbuild_add h (by omega))

def wireFn (n : ℕ) (gs : List Gate) (j : ℕ) : BFn n :=
  fun x => (wiresFrom gs (List.ofFn x)).getD j false

theorem cleanML_to_mbuild {n M E : ℕ} (rows : List ℕ) :
    ∀ (gs pref : List Gate),
      CleanML n (pref ++ gs) →
      (∃ j < n + (pref ++ gs).length, encL (wireFn n (pref ++ gs) j) rows = goalME M E) →
      MBuild M E gs.length
        ((Finset.range (n + pref.length)).image (fun j => encL (wireFn n pref j) rows))
  | [], pref, _, ⟨j, hj, hgoal⟩ => by
    simp only [List.append_nil] at hj hgoal
    exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, hgoal⟩
  | g :: rest, pref, hclean, hex => by
    have hg : CleanMG (n + pref.length) g := hclean pref.length g (by simp)
    obtain ⟨hop, a, b, ha, hb, hgin⟩ := hg
    set pref' := pref ++ [g]
    have hpeq : pref ++ g :: rest = pref' ++ rest := by simp [pref']
    rw [hpeq] at hclean hex
    have ih := cleanML_to_mbuild rows rest pref' hclean hex
    set A := (Finset.range (n + pref.length)).image (fun j => encL (wireFn n pref j) rows)
    set ea := encL (wireFn n pref a) rows
    set eb := encL (wireFn n pref b) rows
    have hea : ea ∈ A := Finset.mem_image.2 ⟨a, Finset.mem_range.2 ha, rfl⟩
    have heb : eb ∈ A := Finset.mem_image.2 ⟨b, Finset.mem_range.2 hb, rfl⟩
    have hwire_lt : ∀ i < n + pref.length, wireFn n pref' i = wireFn n pref i := by
      intro i hi
      funext x
      simp only [wireFn, pref', wiresFrom_append]
      exact getD_wiresFrom [g] _ i (by rw [length_wiresFrom, List.length_ofFn]; exact hi)
    have hwire_new : ∀ conj : Bool, g.op = (if conj then GateOp.and else GateOp.or) →
        encL (wireFn n pref' (n + pref.length)) rows = if conj then ea &&& eb else ea ||| eb := by
      intro conj hcop
      have hfn : wireFn n pref' (n + pref.length) =
          fun x => if conj then wireFn n pref a x && wireFn n pref b x else wireFn n pref a x || wireFn n pref b x := by
        funext x
        simp only [wireFn, pref']
        rw [wiresFrom_append]
        have hlen_w : (wiresFrom pref (List.ofFn x)).length = n + pref.length := by
          rw [length_wiresFrom, List.length_ofFn]
        have h1 : wiresFrom [g] (wiresFrom pref (List.ofFn x)) =
            wiresFrom pref (List.ofFn x) ++ [g.op.eval (g.inputs.map fun i => (wiresFrom pref (List.ofFn x)).getD i false)] := rfl
        rw [h1, getD_snoc_len _ _ _ _ hlen_w, hgin, hcop]
        cases conj <;> simp [GateOp.eval]
      rw [hfn]
      cases conj <;> simp [ea, eb, encL_and, encL_or]
    rcases hop with hand | hor
    · refine Or.inr ⟨ea, hea, eb, heb, true, ?_⟩
      have hsub : ((Finset.range (n + pref'.length)).image (fun j => encL (wireFn n pref' j) rows)) ⊆
          insert (ea &&& eb) A := by
        intro w hw
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
        rw [Finset.mem_range] at hj
        have hlen' : pref'.length = pref.length + 1 := by simp [pref']
        by_cases hlt : j < n + pref.length
        · rw [hwire_lt j hlt]
          exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨j, Finset.mem_range.2 hlt, rfl⟩)
        · have heq : j = n + pref.length := by omega
          subst heq
          rw [hwire_new true hand]
          exact Finset.mem_insert_self _ _
      exact mbuild_mono hsub ih
    · refine Or.inr ⟨ea, hea, eb, heb, false, ?_⟩
      have hsub : ((Finset.range (n + pref'.length)).image (fun j => encL (wireFn n pref' j) rows)) ⊆
          insert (ea ||| eb) A := by
        intro w hw
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
        rw [Finset.mem_range] at hj
        have hlen' : pref'.length = pref.length + 1 := by simp [pref']
        by_cases hlt : j < n + pref.length
        · rw [hwire_lt j hlt]
          exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨j, Finset.mem_range.2 hlt, rfl⟩)
        · have heq : j = n + pref.length := by omega
          subst heq
          rw [hwire_new false hor]
          exact Finset.mem_insert_self _ _
      exact mbuild_mono hsub ih

theorem hasMonoSize_to_mbuild {n M E s : ℕ} (rows xs : List ℕ) (f : BFn n)
    (hM1 : 1 ≤ M) (hE1 : 1 ≤ E)
    (hrows_len : rows.length = M + E)
    (hf_goal : encL f rows = goalME M E)
    (hxs : xs = (List.finRange n).map (fun i => encL (fun x => x i) rows))
    (hs : HasMonoSize n f s) :
    MBuild M E s xs.toFinset := by
  obtain ⟨C, ok, hsz, hev⟩ := hs
  have hsz' : C.gates.length ≤ s := hsz
  have hmok : ∀ g ∈ C.gates, MOk g := ok
  set acc := elim n C.gates (initIdStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n (List.ofFn y) (by simp) C.gates _ _ hmok (inv_initId n y)
  have hclean : CleanML n acc.2 := by
    apply elim_clean n C.gates (initIdStats n, []) hmok
    · intro i
      by_cases hi : i < n
      · simp [initIdStats, hi, statValid]
      · rw [List.getD_eq_default _ _ (by simp [initIdStats]; omega)]; trivial
    · intro p g hg; simp at hg
  have hlen_acc : acc.2.length ≤ s := le_trans (by simpa [hacc] using elim_len n C.gates (initIdStats n, [])) hsz'
  have hval : ∀ y : Fin n → Bool,
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2]
    exact hev y
  have hf_nc : ∃ y1 y2 : Fin n → Bool, f y1 ≠ f y2 := by
    have h0 : (encL f rows).testBit 0 = false := by
      rw [hf_goal, testBit_goalME]; exact decide_eq_false (by omega)
    have hM : (encL f rows).testBit M = true := by
      rw [hf_goal, testBit_goalME]; exact decide_eq_true ⟨le_refl _, by omega⟩
    rw [encL_testBit] at h0 hM
    refine ⟨pt n (rows.getD 0 0), pt n (rows.getD M 0), ?_⟩
    have h0' : f (pt n (rows.getD 0 0)) = false := by
      have : 0 < rows.length := by omega
      simpa [List.getD_eq_getElem?_getD, this] using h0
    have hM' : f (pt n (rows.getD M 0)) = true := by
      have : M < rows.length := by omega
      simpa [List.getD_eq_getElem?_getD, this] using hM
    rw [h0', hM']; decide
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y1, y2, hne⟩ := hf_nc
    apply hne
    rw [← hval y1, ← hval y2, hst]; rfl
  | inr outIdx =>
    have hout_lt : outIdx < n + acc.2.length := by
      have hv := ((hinv (fun _ => false)).2 C.output).1
      rw [hst] at hv; exact hv
    have hout_eq : wireFn n acc.2 outIdx = f := by
      funext y
      have := hval y
      rw [hst] at this
      exact this
    have hmb := cleanML_to_mbuild (M := M) (E := E) rows acc.2 [] (by simpa using hclean)
      ⟨outIdx, by simpa using hout_lt, by simpa [hout_eq] using hf_goal⟩
    have hA_eq : ((Finset.range (n + ([] : List Gate).length)).image (fun j => encL (wireFn n [] j) rows)) =
        xs.toFinset := by
      ext w
      simp only [List.length_nil, Nat.add_zero, Finset.mem_image, Finset.mem_range,
        hxs, List.mem_toFinset, List.mem_map, List.mem_finRange, true_and]
      constructor
      · rintro ⟨j, hj, rfl⟩
        refine ⟨⟨j, hj⟩, ?_⟩
        congr 1; funext x; simp [wireFn, wiresFrom, hj]
      · rintro ⟨i, rfl⟩
        refine ⟨i.val, i.isLt, ?_⟩
        congr 1; funext x; simp [wireFn, wiresFrom, i.isLt]
    rw [hA_eq] at hmb
    exact mbuild_add hmb hlen_acc

def allProperSubNotFull (M E : ℕ) (xs : List ℕ) : Bool :=
  let full := (1 <<< (M * E)) - 1
  xs.all (fun x => !(Nat.beq (listC1 ((xs.erase x).map (sepSpec M E))) full))

theorem listC1_subset_full {K : ℕ} {l1 l2 : List ℕ}
    (hsub : ∀ y ∈ l1, y ∈ l2)
    (hlt2 : ∀ y ∈ l2, y < 2 ^ K)
    (hf1 : listC1 l1 = (1 <<< K) - 1) :
    listC1 l2 = (1 <<< K) - 1 := by
  apply Nat.eq_of_testBit_eq; intro p
  rw [testBit_mMask]
  by_cases hp : p < K
  · rw [decide_eq_true hp]
    have h1 : (listC1 l1).testBit p = true := by rw [hf1, testBit_mMask, decide_eq_true hp]
    obtain ⟨y, hy1, hyp⟩ := (listC1_testBit l1 p).1 h1
    exact (listC1_testBit l2 p).2 ⟨y, hsub y hy1, hyp⟩
  · rw [decide_eq_false hp]
    apply Bool.eq_false_iff.2
    intro h2
    obtain ⟨y, hy2, hyp⟩ := (listC1_testBit l2 p).1 h2
    rw [testBit_lt_of_lt (hlt2 y hy2) (by omega)] at hyp
    exact Bool.noConfusion hyp

theorem prove_base_mono {n M E cap : ℕ}
    (rows xs : List ℕ)
    (f : BFn n)
    (S : ℕ → ℕ → List ℕ) (N : ℕ → ℕ)
    (idx : ℕ → List ℕ → ℕ) (ori : List ℕ → List ℕ)
    (hME : validME M E = true)
    (hori : ∀ k l, (∀ w ∈ l, w < 2 ^ (M + E)) → DLive M E k l.toFinset → DLive M E k (ori l).toFinset)
    (hrows_len : rows.length = M + E)
    (hf_goal : encL f rows = goalME M E)
    (hxs : xs = (List.finRange n).map (fun i => encL (fun x => x i) rows))
    (hsub : allProperSubNotFull M E xs = true)
    (hcap0 : Nat.blt 0 (N cap) = true)
    (hperm0 : isPermNat xs (S cap 0) = true)
    (hbar : ∀ s ≤ cap, ∀ i < N s, barV3 M E S N idx ori s i = true) :
    ∀ s, HasMonoSize n f s → cap + 1 ≤ s := by
  intro s hs
  by_contra hlt_s
  have hle : s ≤ cap := by omega
  obtain ⟨hM1, _, hE2, _, _⟩ := validME_props hME
  have hEpos : 0 < E := by omega
  have hmb : MBuild M E cap xs.toFinset :=
    mbuild_add (hasMonoSize_to_mbuild rows xs f hM1 (by omega) hrows_len hf_goal hxs hs) hle
  have hxs_lt : ∀ w ∈ xs, w < 2 ^ (M + E) := by
    intro w hw
    rw [hxs] at hw
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hw
    rw [← hrows_len]; exact encL_lt _ rows
  have hdb : DBuild M E cap xs.toFinset :=
    mbuild_to_dbuild (by omega) hEpos cap xs.toFinset xs.toFinset
      (fun w hw => hxs_lt w (List.mem_toFinset.1 hw))
      (fun w hw => hxs_lt w (List.mem_toFinset.1 hw))
      (fun w hw _ => ⟨w, hw, domME_refl M w⟩) hmb
  obtain ⟨sub, hsub_xs, hdl⟩ := dbuild_to_dlive hdb
  have hsub_eq : sub = xs.toFinset := by
    by_contra hne
    have hex : ∃ x ∈ xs, x ∉ sub := by
      by_contra hall; push Not at hall
      apply hne
      exact Finset.Subset.antisymm hsub_xs (fun x hx => hall x (List.mem_toFinset.1 hx))
    obtain ⟨x, hx_in, hx_not⟩ := hex
    have hfull_sub : listC1 (sub.toList.map (sepSpec M E)) = (1 <<< (M * E)) - 1 := by
      apply dlive_listC1_full hME
      · intro w hw; exact hxs_lt w (List.mem_toFinset.1 (hsub_xs (Finset.mem_toList.1 hw)))
      · simpa using hdl
    have hfull_er : listC1 ((xs.erase x).map (sepSpec M E)) = (1 <<< (M * E)) - 1 := by
      apply listC1_subset_full (K := M * E) _ _ hfull_sub
      · intro y hy
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hy
        have hw_sub : w ∈ sub := Finset.mem_toList.1 hw
        have hw_xs : w ∈ xs := List.mem_toFinset.1 (hsub_xs hw_sub)
        have hwx : w ≠ x := fun e => hx_not (e ▸ hw_sub)
        exact List.mem_map.2 ⟨w, (List.mem_erase_of_ne hwx).2 hw_xs, rfl⟩
      · intro y hy
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hy
        exact sepSpec_lt hEpos (hxs_lt w (List.mem_of_mem_erase hw))
    simp only [allProperSubNotFull, List.all_eq_true, Bool.not_eq_true', nat_beq_false] at hsub
    exact hsub x hx_in hfull_er
  rw [hsub_eq] at hdl
  have hno := barV3_all hME S N idx ori hori cap hbar cap (le_refl _) 0 (by rwa [Nat.blt_eq] at hcap0)
  rw [perm_toFinset_eq (isPermNat_sound hperm0)] at hdl
  exact hno hdl

/-! ## Section 3: Verified barrier certificates for base graphs -/

def edges_K3 : List (Fin 3 × Fin 3) := [(0,1),(0,2),(1,2)]
def r0 : List ℕ := [1,2,4,3,5,6]
def x0 : List ℕ := [25,42,52]
def o0 (ws : List ℕ) : List ℕ := ws
theorem ho0 : ∀ k l, (∀ w ∈ l, w < 2 ^ (3 + 3)) → DLive 3 3 k l.toFinset → DLive 3 3 k (o0 l).toFinset := fun _ _ _ h => h
def N0 : ℕ → ℕ | 3 => 1 | _ => 0
def H0 : ℕ → ℕ → ℕ | _ => fun _ => 0
def P0 : ℕ → ℕ → ℕ | _ => fun _ => 0
def Z0 (s i : ℕ) : Bool := barV3 3 3 (SgenB 3 x0 o0 P0) N0 (idxGenB N0 H0) o0 s i
theorem l0_3 : ∀ i, 0 ≤ i → i < N0 3 → Z0 3 i = true := span_end 1 0 (by decide +kernel) (le_refl _)
theorem base_K3 : ∀ s, HasMonoSize 3 (gfn [] edges_K3) s → 4 ≤ s :=
  prove_base_mono (M := 3) (E := 3) (cap := 3) r0 x0 (gfn [] edges_K3)
    (SgenB 3 x0 o0 P0) N0 (idxGenB N0 H0) o0
    (by decide) ho0 rfl (by decide) rfl (by decide +kernel) rfl (by decide +kernel) (
    all_step l0_3 <| all_step lvl_empty <| all_step lvl_empty <| all_zero lvl_empty)

def edges_C5 : List (Fin 5 × Fin 5) := [(0,1),(0,2),(1,3),(2,4),(3,4)]
def r1 : List ℕ := [6,9,12,17,18,3,5,10,20,24]
def x1 : List ℕ := [106,177,325,646,792]
def o1 (ws : List ℕ) : List ℕ := ws
theorem ho1 : ∀ k l, (∀ w ∈ l, w < 2 ^ (5 + 5)) → DLive 5 5 k l.toFinset → DLive 5 5 k (o1 l).toFinset := fun _ _ _ h => h
def N1 : ℕ → ℕ | 6 => 1 | _ => 0
def H1 : ℕ → ℕ → ℕ | _ => fun _ => 0
def P1 : ℕ → ℕ → ℕ | _ => fun _ => 0
def Z1 (s i : ℕ) : Bool := barV3 5 5 (SgenB 6 x1 o1 P1) N1 (idxGenB N1 H1) o1 s i
theorem l1_6 : ∀ i, 0 ≤ i → i < N1 6 → Z1 6 i = true := span_end 1 0 (by decide +kernel) (le_refl _)
theorem base_C5 : ∀ s, HasMonoSize 5 (gfn [] edges_C5) s → 7 ≤ s :=
  prove_base_mono (M := 5) (E := 5) (cap := 6) r1 x1 (gfn [] edges_C5)
    (SgenB 6 x1 o1 P1) N1 (idxGenB N1 H1) o1
    (by decide) ho1 rfl (by decide) rfl (by decide +kernel) rfl (by decide +kernel) (
    all_step l1_6 <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_zero lvl_empty)

def edges_BOWTIE : List (Fin 5 × Fin 5) := [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)]
def r2 : List ℕ := [1,10,12,18,20,3,5,9,17,6,24]
def x2 : List ℕ := [481,554,596,1158,1304]
def p2 (pi w : ℕ) : ℕ := match pi with
  | 0 => ((w &&& 0x54) >>> 1) ||| ((w &&& 0x781) ||| ((w &&& 0x2a) <<< 1))
  | 1 => ((w &&& 0x18) >>> 2) ||| (((w &&& 0x100) >>> 1) ||| ((w &&& 0x661) ||| (((w &&& 0x80) <<< 1) ||| ((w &&& 0x6) <<< 2))))
  | 2 => ((w &&& 0x180) >>> 2) ||| (((w &&& 0x408) >>> 1) ||| ((w &&& 0x13) ||| (((w &&& 0x204) <<< 1) ||| ((w &&& 0x60) <<< 2))))
  | _ => w
theorem vp2 : ∀ pi, ValidPerm 5 6 (p2 pi)
  | 0 => validPerm_of_spec 5 6 (p2 0) [(0x54,2,1),(0x781,0,0),(0x2a,1,1)] [0,2,1,4,3,6,5,7,8,9,10] (fun _ => rfl) (by decide +kernel)
  | 1 => validPerm_of_spec 5 6 (p2 1) [(0x18,2,2),(0x100,2,1),(0x661,0,0),(0x80,1,1),(0x6,1,2)] [0,3,4,1,2,5,6,8,7,9,10] (fun _ => rfl) (by decide +kernel)
  | 2 => validPerm_of_spec 5 6 (p2 2) [(0x180,2,2),(0x408,2,1),(0x13,0,0),(0x204,1,1),(0x60,1,2)] [0,1,3,2,4,7,8,5,6,10,9] (fun _ => rfl) (by decide +kernel)
  | _ + 3 => validPerm_id 5 6
def o2 : List ℕ → List ℕ := oriStages p2 [[0],[1],[2]]
theorem ho2 : ∀ k l, (∀ w ∈ l, w < 2 ^ (5 + 6)) → DLive 5 6 k l.toFinset → DLive 5 6 k (o2 l).toFinset := fun _ _ hlt h => oriStages_dlive vp2 hlt h
def N2 : ℕ → ℕ | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 1 | _ => 0
def H2_4 : ℕ → ℕ
  | 0 => 0x76645
  | _ => 0
def H2_5 : ℕ → ℕ
  | 0 => 0x624f660e6750d3921b7a20f550cb8b
  | _ => 0
def H2_6 : ℕ → ℕ
  | 0 => 0xb67e3a7ac74cd1842c5121c5d
  | _ => 0
def H2 : ℕ → ℕ → ℕ | 4 => H2_4 | 5 => H2_5 | 6 => H2_6 | _ => fun _ => 0
def P2_4 : ℕ → ℕ
  | 0 => 0x2121
  | _ => 0
def P2_5 : ℕ → ℕ
  | 0 => 0x44c0011210004c00014000450002030
  | _ => 0
def P2_6 : ℕ → ℕ
  | 0 => 0x710001c8400621001cc400610
  | _ => 0
def P2 : ℕ → ℕ → ℕ | 4 => P2_4 | 5 => P2_5 | 6 => P2_6 | _ => fun _ => 0
def Z2 (s i : ℕ) : Bool := barV3 5 6 (SgenB 7 x2 o2 P2) N2 (idxGenB N2 H2) o2 s i
theorem l2_4 : ∀ i, 0 ≤ i → i < N2 4 → Z2 4 i = true := span_end 1 0 (by decide +kernel) (le_refl _)
theorem l2_5 : ∀ i, 0 ≤ i → i < N2 5 → Z2 5 i = true := span_end 6 0 (by decide +kernel) (le_refl _)
theorem l2_6 : ∀ i, 0 ≤ i → i < N2 6 → Z2 6 i = true := span_end 5 0 (by decide +kernel) (le_refl _)
theorem l2_7 : ∀ i, 0 ≤ i → i < N2 7 → Z2 7 i = true := span_end 1 0 (by decide +kernel) (le_refl _)
theorem base_BOWTIE : ∀ s, HasMonoSize 5 (gfn [] edges_BOWTIE) s → 8 ≤ s :=
  prove_base_mono (M := 5) (E := 6) (cap := 7) r2 x2 (gfn [] edges_BOWTIE)
    (SgenB 7 x2 o2 P2) N2 (idxGenB N2 H2) o2
    (by decide) ho2 rfl (by decide) rfl (by decide +kernel) rfl (by decide +kernel) (
    all_step l2_7 <| all_step l2_6 <| all_step l2_5 <| all_step l2_4 <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_zero lvl_empty)

def edges_TwoK3 : List (Fin 6 × Fin 6) := [(0,1),(0,2),(1,2),(3,4),(3,5),(4,5)]
def r3 : List ℕ := [9,10,12,17,18,20,33,34,36,3,5,6,24,40,48]
def x3 : List ℕ := [1609,2706,3364,12295,20536,25024]
def p3 (pi w : ℕ) : ℕ := match pi with
  | 0 => ((w &&& 0x524) >>> 1) ||| ((w &&& 0x7849) ||| ((w &&& 0x292) <<< 1))
  | 1 => ((w &&& 0x1c0) >>> 3) ||| (((w &&& 0x2000) >>> 1) ||| ((w &&& 0x4e07) ||| (((w &&& 0x1000) <<< 1) ||| ((w &&& 0x38) <<< 3))))
  | 2 => ((w &&& 0x40) >>> 4) ||| (((w &&& 0x7000) >>> 3) ||| (((w &&& 0x88) >>> 2) ||| ((w &&& 0x111) ||| (((w &&& 0x22) <<< 2) ||| (((w &&& 0xe00) <<< 3) ||| ((w &&& 0x4) <<< 4))))))
  | _ => w
theorem vp3 : ∀ pi, ValidPerm 9 6 (p3 pi)
  | 0 => validPerm_of_spec 9 6 (p3 0) [(0x524,2,1),(0x7849,0,0),(0x292,1,1)] [0,2,1,3,5,4,6,8,7,10,9,11,12,13,14] (fun _ => rfl) (by decide +kernel)
  | 1 => validPerm_of_spec 9 6 (p3 1) [(0x1c0,2,3),(0x2000,2,1),(0x4e07,0,0),(0x1000,1,1),(0x38,1,3)] [0,1,2,6,7,8,3,4,5,9,10,11,13,12,14] (fun _ => rfl) (by decide +kernel)
  | 2 => validPerm_of_spec 9 6 (p3 2) [(0x40,2,4),(0x7000,2,3),(0x88,2,2),(0x111,0,0),(0x22,1,2),(0xe00,1,3),(0x4,1,4)] [0,3,6,1,4,7,2,5,8,12,13,14,9,10,11] (fun _ => rfl) (by decide +kernel)
  | _ + 3 => validPerm_id 9 6
def o3 : List ℕ → List ℕ := oriStages p3 [[0],[1],[2]]
theorem ho3 : ∀ k l, (∀ w ∈ l, w < 2 ^ (9 + 6)) → DLive 9 6 k l.toFinset → DLive 9 6 k (o3 l).toFinset := fun _ _ hlt h => oriStages_dlive vp3 hlt h
def N3 : ℕ → ℕ | 4 => 1 | 5 => 4 | 6 => 10 | 7 => 7 | 8 => 1 | _ => 0
def H3_4 : ℕ → ℕ
  | 0 => 0x5409d
  | _ => 0
def H3_5 : ℕ → ℕ
  | 0 => 0x81f477659f1fec81e245
  | _ => 0
def H3_6 : ℕ → ℕ
  | 0 => 0xe9bd5db554d8a05b7677af3eda6aeba33bb9b9638218572487
  | _ => 0
def H3_7 : ℕ → ℕ
  | 0 => 0xdf135da27ecab01b38bf8b7e24437537c96
  | _ => 0
def H3 : ℕ → ℕ → ℕ | 4 => H3_4 | 5 => H3_5 | 6 => H3_6 | 7 => H3_7 | _ => fun _ => 0
def P3_4 : ℕ → ℕ
  | 0 => 0x10
  | _ => 0
def P3_5 : ℕ → ℕ
  | 0 => 0x80800002000048402121
  | _ => 0
def P3_6 : ℕ → ℕ
  | 0 => 0x60c00115000a0c0001500004c0001210044c00114000050001121
  | _ => 0
def P3_7 : ℕ → ℕ
  | 0 => 0x730001c4000741001c8400610001d0000621
  | _ => 0
def P3 : ℕ → ℕ → ℕ | 4 => P3_4 | 5 => P3_5 | 6 => P3_6 | 7 => P3_7 | _ => fun _ => 0
def Z3 (s i : ℕ) : Bool := barV3 9 6 (SgenB 8 x3 o3 P3) N3 (idxGenB N3 H3) o3 s i
theorem l3_4 : ∀ i, 0 ≤ i → i < N3 4 → Z3 4 i = true := span_end 1 0 (by decide +kernel) (le_refl _)
theorem l3_5 : ∀ i, 0 ≤ i → i < N3 5 → Z3 5 i = true := span_end 4 0 (by decide +kernel) (le_refl _)
theorem l3_6 : ∀ i, 0 ≤ i → i < N3 6 → Z3 6 i = true := span_end 10 0 (by decide +kernel) (le_refl _)
theorem l3_7 : ∀ i, 0 ≤ i → i < N3 7 → Z3 7 i = true := span_end 7 0 (by decide +kernel) (le_refl _)
theorem l3_8 : ∀ i, 0 ≤ i → i < N3 8 → Z3 8 i = true := span_end 1 0 (by decide +kernel) (le_refl _)
theorem base_TwoK3 : ∀ s, HasMonoSize 6 (gfn [] edges_TwoK3) s → 9 ≤ s :=
  prove_base_mono (M := 9) (E := 6) (cap := 8) r3 x3 (gfn [] edges_TwoK3)
    (SgenB 8 x3 o3 P3) N3 (idxGenB N3 H3) o3
    (by decide) ho3 rfl (by decide) rfl (by decide +kernel) rfl (by decide +kernel) (
    all_step l3_8 <| all_step l3_7 <| all_step l3_6 <| all_step l3_5 <| all_step l3_4 <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_zero lvl_empty)

def edges_K3C5 : List (Fin 6 × Fin 6) := [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(4,5)]
def r4 : List ℕ := [10,17,28,33,34,36,3,5,9,6,18,40,48]
def x4 : List ℕ := [458,1617,676,2309,5126,6200]
def p4 (pi w : ℕ) : ℕ := match pi with
  | 0 => ((w &&& 0x600) >>> 2) ||| (((w &&& 0x1012) >>> 1) ||| ((w &&& 0x64) ||| (((w &&& 0x809) <<< 1) ||| ((w &&& 0x180) <<< 2))))
  | _ => w
theorem vp4 : ∀ pi, ValidPerm 6 7 (p4 pi)
  | 0 => validPerm_of_spec 6 7 (p4 0) [(0x600,2,2),(0x1012,2,1),(0x64,0,0),(0x809,1,1),(0x180,1,2)] [1,0,2,4,3,5,6,9,10,7,8,12,11] (fun _ => rfl) (by decide +kernel)
  | _ + 1 => validPerm_id 6 7
def o4 : List ℕ → List ℕ := oriStages p4 [[0]]
theorem ho4 : ∀ k l, (∀ w ∈ l, w < 2 ^ (6 + 7)) → DLive 6 7 k l.toFinset → DLive 6 7 k (o4 l).toFinset := fun _ _ hlt h => oriStages_dlive vp4 hlt h
def N4 : ℕ → ℕ | 6 => 18 | 7 => 13 | 8 => 1 | _ => 0
def H4_6 : ℕ → ℕ
  | 0 => 0x968a1892808571c731a06f4ee673b666c166649d6132a60f85598963cbd03b011319871eb2a1e98f1a2dd18fd5
  | _ => 0
def H4_7 : ℕ → ℕ
  | 0 => 0xf5167eaba8b0b549a45d9907888c646c9dd6679a61679527433b5453903f09d64
  | _ => 0
def H4 : ℕ → ℕ → ℕ | 6 => H4_6 | 7 => H4_7 | _ => fun _ => 0
def P4_6 : ℕ → ℕ
  | 0 => 0x45800115000e5000194000c14002830006540061300044c004060018540061400045000196000e4c00193000e58006160
  | _ => 0
def P4_7 : ℕ → ℕ
  | 0 => 0x653001d0000732001d4c0074300184000750001c40007520018c000620001cc000720
  | _ => 0
def P4 : ℕ → ℕ → ℕ | 6 => P4_6 | 7 => P4_7 | _ => fun _ => 0
def Z4 (s i : ℕ) : Bool := barV3 6 7 (SgenB 8 x4 o4 P4) N4 (idxGenB N4 H4) o4 s i
theorem l4_6 : ∀ i, 0 ≤ i → i < N4 6 → Z4 6 i = true := span_end 18 0 (by decide +kernel) (le_refl _)
theorem l4_7 : ∀ i, 0 ≤ i → i < N4 7 → Z4 7 i = true := span_end 13 0 (by decide +kernel) (le_refl _)
theorem l4_8 : ∀ i, 0 ≤ i → i < N4 8 → Z4 8 i = true := span_end 1 0 (by decide +kernel) (le_refl _)
theorem base_K3C5 : ∀ s, HasMonoSize 6 (gfn [] edges_K3C5) s → 9 ≤ s :=
  prove_base_mono (M := 6) (E := 7) (cap := 8) r4 x4 (gfn [] edges_K3C5)
    (SgenB 8 x4 o4 P4) N4 (idxGenB N4 H4) o4
    (by decide) ho4 rfl (by decide) rfl (by decide +kernel) rfl (by decide +kernel) (
    all_step l4_8 <| all_step l4_7 <| all_step l4_6 <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_zero lvl_empty)

def edges_n6_025 : List (Fin 6 × Fin 6) := [(0,1),(0,2),(0,3),(1,2),(3,4),(3,5),(4,5)]
def r5 : List ℕ := [10,12,17,18,20,33,34,36,3,5,9,6,24,40,48]
def x5 : List ℕ := [1828,2377,2706,13315,20508,24800]
def p5 (pi w : ℕ) : ℕ := match pi with
  | 0 => ((w &&& 0x292) >>> 1) ||| ((w &&& 0x7c24) ||| ((w &&& 0x149) <<< 1))
  | 1 => ((w &&& 0xe0) >>> 3) ||| (((w &&& 0x2000) >>> 1) ||| ((w &&& 0x4f03) ||| (((w &&& 0x1000) <<< 1) ||| ((w &&& 0x1c) <<< 3))))
  | 2 => ((w &&& 0x3020) >>> 4) ||| (((w &&& 0x4000) >>> 3) ||| (((w &&& 0x44) >>> 2) ||| ((w &&& 0x488) ||| (((w &&& 0x11) <<< 2) ||| (((w &&& 0x800) <<< 3) ||| ((w &&& 0x302) <<< 4))))))
  | _ => w
theorem vp5 : ∀ pi, ValidPerm 8 7 (p5 pi)
  | 0 => validPerm_of_spec 8 7 (p5 0) [(0x292,2,1),(0x7c24,0,0),(0x149,1,1)] [1,0,2,4,3,5,7,6,9,8,10,11,12,13,14] (fun _ => rfl) (by decide +kernel)
  | 1 => validPerm_of_spec 8 7 (p5 1) [(0xe0,2,3),(0x2000,2,1),(0x4f03,0,0),(0x1000,1,1),(0x1c,1,3)] [0,1,5,6,7,2,3,4,8,9,10,11,13,12,14] (fun _ => rfl) (by decide +kernel)
  | 2 => validPerm_of_spec 8 7 (p5 2) [(0x3020,2,4),(0x4000,2,3),(0x44,2,2),(0x488,0,0),(0x11,1,2),(0x800,1,3),(0x302,1,4)] [2,5,0,3,6,1,4,7,12,13,10,14,8,9,11] (fun _ => rfl) (by decide +kernel)
  | _ + 3 => validPerm_id 8 7
def o5 : List ℕ → List ℕ := oriStages p5 [[0],[1],[2]]
theorem ho5 : ∀ k l, (∀ w ∈ l, w < 2 ^ (8 + 7)) → DLive 8 7 k l.toFinset → DLive 8 7 k (o5 l).toFinset := fun _ _ hlt h => oriStages_dlive vp5 hlt h
def N5 : ℕ → ℕ | 4 => 2 | 5 => 22 | 6 => 50 | 7 => 40 | 8 => 8 | 9 => 1 | _ => 0
def H5_4 : ℕ → ℕ
  | 0 => 0xb8862657ea
  | _ => 0
def H5_5 : ℕ → ℕ
  | 0 => 0xfa0efc53629ddee9a750985f097a2593e6391902846a07464071ae670c40545d54d4c0313373106d2da792b4761f1b51a4dc154540f023
  | _ => 0
def H5_6 : ℕ → ℕ
  | 0 => 0xeda97e95dce38d9def3ade50bdb877db42cd1926cde4ec7194c0e81bf7acbe7c6bd481bc8afbbee9b8d69b4fbfb3e04b3b2faf1c1a8d05a38609fbc29c1e38e37f7df987db787d8ae75b007461070be068ab7653db5b86458a27525c6428253dfa53a9f13510a32fd5313372ee46287e61f4321deac129f310f8b08164
  | _ => 0
def H5_7 : ℕ → ℕ
  | 0 => 0xfb86af96bfcc166c1e1ec0e51bc8afba993ba823b9259af1c1a5268a38609fd059fbc29ee0790e098e37f7db7868bd864cec602dd5f23454c3b5341846dff461f5455893dfa53db023a9f139fb634d073144e2f5a42b8ec2841c220cb1f4021495b0cbea
  | _ => 0
def H5_8 : ℕ → ℕ
  | 0 => 0xe2543deb219c1919032d853b8815482e2dd04bba
  | _ => 0
def H5 : ℕ → ℕ → ℕ | 4 => H5_4 | 5 => H5_5 | 6 => H5_6 | 7 => H5_7 | 8 => H5_8 | _ => fun _ => 0
def P5_4 : ℕ → ℕ
  | 0 => 0x1648006810
  | _ => 0
def P5_5 : ℕ → ℕ
  | 0 => 0x241440e0500420c81813100a4c011151002484080200245400995100e840069410004c00313101c084011410125040093103e4c4019210280c801131
  | _ => 0
def P5_6 : ℕ → ℕ
  | 0 => 0x4c580081210148800196100e50402950042100001510480c009860046584028320205000c9510204801134002a5000c06002a0c81314000c080009210280800582000c180048200065040e82002454402940010d0003021000504053210245040e931010c800713000808002920044cc0009400104800093102c840039510204c0043300025800bc32
  | _ => 0
def P5_7 : ℕ → ℕ
  | 0 => 0x71000045000b10000d31004d40028300014c001c3000ccc00393000b4c4031500010c001150004cc00056000c5000113000a88400532001540013400090c00143100a8c000c2100118001140007584031300015440082100ecc0005520030c00056100cd4000d5000118803340
  | _ => 0
def P5_8 : ℕ → ℕ
  | 0 => 0x18c000610001c4000730001d0400621001c8400740
  | _ => 0
def P5 : ℕ → ℕ → ℕ | 4 => P5_4 | 5 => P5_5 | 6 => P5_6 | 7 => P5_7 | 8 => P5_8 | _ => fun _ => 0
def Z5 (s i : ℕ) : Bool := barV3 8 7 (SgenB 9 x5 o5 P5) N5 (idxGenB N5 H5) o5 s i
theorem l5_4 : ∀ i, 0 ≤ i → i < N5 4 → Z5 4 i = true := span_end 2 0 (by decide +kernel) (le_refl _)
theorem l5_5 : ∀ i, 0 ≤ i → i < N5 5 → Z5 5 i = true := span_end 22 0 (by decide +kernel) (le_refl _)
theorem l5_6 : ∀ i, 0 ≤ i → i < N5 6 → Z5 6 i = true := span_end 50 0 (by decide +kernel) (le_refl _)
theorem l5_7 : ∀ i, 0 ≤ i → i < N5 7 → Z5 7 i = true := span_end 40 0 (by decide +kernel) (le_refl _)
theorem l5_8 : ∀ i, 0 ≤ i → i < N5 8 → Z5 8 i = true := span_end 8 0 (by decide +kernel) (le_refl _)
theorem l5_9 : ∀ i, 0 ≤ i → i < N5 9 → Z5 9 i = true := span_end 1 0 (by decide +kernel) (le_refl _)
theorem base_n6_025 : ∀ s, HasMonoSize 6 (gfn [] edges_n6_025) s → 10 ≤ s :=
  prove_base_mono (M := 8) (E := 7) (cap := 9) r5 x5 (gfn [] edges_n6_025)
    (SgenB 9 x5 o5 P5) N5 (idxGenB N5 H5) o5
    (by decide) ho5 rfl (by decide) rfl (by decide +kernel) rfl (by decide +kernel) (
    all_step l5_9 <| all_step l5_8 <| all_step l5_7 <| all_step l5_6 <| all_step l5_5 <| all_step l5_4 <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_zero lvl_empty)

def edges_n7_050 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(1,3),(2,4),(3,5),(4,6),(5,6)]
def r6 : List ℕ := [25,38,49,50,70,73,76,3,5,10,20,40,80,96]
def x6 : List ℕ := [421,666,1362,2657,5133,10254,12400]
def p6 (pi w : ℕ) : ℕ := match pi with
  | 0 => ((w &&& 0x70) >>> 3) ||| (((w &&& 0x1500) >>> 1) ||| ((w &&& 0x2001) ||| (((w &&& 0xa80) <<< 1) ||| ((w &&& 0xe) <<< 3))))
  | _ => w
theorem vp6 : ∀ pi, ValidPerm 7 7 (p6 pi)
  | 0 => validPerm_of_spec 7 7 (p6 0) [(0x70,2,3),(0x1500,2,1),(0x2001,0,0),(0xa80,1,1),(0xe,1,3)] [0,4,5,6,1,2,3,8,7,10,9,12,11,13] (fun _ => rfl) (by decide +kernel)
  | _ + 1 => validPerm_id 7 7
def o6 : List ℕ → List ℕ := oriStages p6 [[0]]
theorem ho6 : ∀ k l, (∀ w ∈ l, w < 2 ^ (7 + 7)) → DLive 7 7 k l.toFinset → DLive 7 7 k (o6 l).toFinset := fun _ _ hlt h => oriStages_dlive vp6 hlt h
def N6 : ℕ → ℕ | 7 => 22 | 8 => 16 | 9 => 1 | _ => 0
def H6_7 : ℕ → ℕ
  | 0 => 0xfb663e82aee81e7e8001d644fc70adc4de8c1c18bd786b702dadcfca8b0f9f273936518699f7a1cc5ae9056dd34829245b573f5a4213d9
  | _ => 0
def H6_8 : ℕ → ℕ
  | 0 => 0xffd04fc100f4d16dc3c1d7b5ad299fb5d25a8c299d77888a976da014b1c1487ac3fc853863209874
  | _ => 0
def H6 : ℕ → ℕ → ℕ | 7 => H6_7 | 8 => H6_8 | _ => fun _ => 0
def P6_7 : ℕ → ℕ
  | 0 => 0x1c5c00713001c580059400180c0001500005c005930016580049300125c00715001254000140012580049400004c00016000c1c00105000e0c007140
  | _ => 0
def P6_8 : ℕ → ℕ
  | 0 => 0x1d8400610001d04007210019940071000194c00743001cc000763001cc400765001d4000751001d4c00631
  | _ => 0
def P6 : ℕ → ℕ → ℕ | 7 => P6_7 | 8 => P6_8 | _ => fun _ => 0
def Z6 (s i : ℕ) : Bool := barV3 7 7 (SgenB 9 x6 o6 P6) N6 (idxGenB N6 H6) o6 s i
theorem l6_7 : ∀ i, 0 ≤ i → i < N6 7 → Z6 7 i = true := span_end 22 0 (by decide +kernel) (le_refl _)
theorem l6_8 : ∀ i, 0 ≤ i → i < N6 8 → Z6 8 i = true := span_end 16 0 (by decide +kernel) (le_refl _)
theorem l6_9 : ∀ i, 0 ≤ i → i < N6 9 → Z6 9 i = true := span_end 1 0 (by decide +kernel) (le_refl _)
theorem base_n7_050 : ∀ s, HasMonoSize 7 (gfn [] edges_n7_050) s → 10 ≤ s :=
  prove_base_mono (M := 7) (E := 7) (cap := 9) r6 x6 (gfn [] edges_n7_050)
    (SgenB 9 x6 o6 P6) N6 (idxGenB N6 H6) o6
    (by decide) ho6 rfl (by decide) rfl (by decide +kernel) rfl (by decide +kernel) (
    all_step l6_9 <| all_step l6_8 <| all_step l6_7 <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_zero lvl_empty)

def edges_n7_055 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(2,6),(3,4)]
def r7 : List ℕ := [44,52,74,82,97,104,112,3,5,9,17,6,34,68,24]
def x7 : List ℕ := [1936,6284,10499,16933,17482,4211,8316]
def p7 (pi w : ℕ) : ℕ := match pi with
  | 0 => ((w &&& 0x44a) >>> 1) ||| ((w &&& 0x7990) ||| ((w &&& 0x225) <<< 1))
  | 1 => ((w &&& 0xc) >>> 2) ||| (((w &&& 0x2100) >>> 1) ||| ((w &&& 0x4e70) ||| (((w &&& 0x1080) <<< 1) ||| ((w &&& 0x3) <<< 2))))
  | 2 => ((w &&& 0x8) >>> 3) ||| (((w &&& 0x2544) >>> 1) ||| ((w &&& 0x4810) ||| (((w &&& 0x12a2) <<< 1) ||| ((w &&& 0x1) <<< 3))))
  | _ => w
theorem vp7 : ∀ pi, ValidPerm 7 8 (p7 pi)
  | 0 => validPerm_of_spec 7 8 (p7 0) [(0x44a,2,1),(0x7990,0,0),(0x225,1,1)] [1,0,3,2,4,6,5,7,8,10,9,11,12,13,14] (fun _ => rfl) (by decide +kernel)
  | 1 => validPerm_of_spec 7 8 (p7 1) [(0xc,2,2),(0x2100,2,1),(0x4e70,0,0),(0x1080,1,1),(0x3,1,2)] [2,3,0,1,4,5,6,8,7,9,10,11,13,12,14] (fun _ => rfl) (by decide +kernel)
  | 2 => validPerm_of_spec 7 8 (p7 2) [(0x8,2,3),(0x2544,2,1),(0x4810,0,0),(0x12a2,1,1),(0x1,1,3)] [3,2,1,0,4,6,5,8,7,10,9,11,13,12,14] (fun _ => rfl) (by decide +kernel)
  | _ + 3 => validPerm_id 7 8
def o7 : List ℕ → List ℕ := oriStages p7 [[0,1,2]]
theorem ho7 : ∀ k l, (∀ w ∈ l, w < 2 ^ (7 + 8)) → DLive 7 8 k l.toFinset → DLive 7 8 k (o7 l).toFinset := fun _ _ hlt h => oriStages_dlive vp7 hlt h
def N7 : ℕ → ℕ | 4 => 3 | 5 => 46 | 6 => 208 | 7 => 321 | 8 => 138 | 9 => 13 | 10 => 1 | _ => 0
def H7_4 : ℕ → ℕ
  | 0 => 0xd030d5dcd1201bf
  | _ => 0
def H7_5 : ℕ → ℕ
  | 0 => 0xfcdf4fcc3bf72c7edb3eeacc8e98d2dd182dcb59d9cc8d85d1d08e8cbca0c2addbe439be2a7af8d6ad1b2a3c469e7e1988df8ce697655175a7e72e725e1ba5c5b959fd155d4a530845212c4f0884c01046815426ff404c0359c933d2e32ddd32b88275a925540241b71a36719e6519cc40839c
  | _ => 0
def H7_6 : ℕ → ℕ
  | 0 => 0x4ab8a474df46e4c426ff42564424964237540c3d4098b3f42a3dd9a3dc3b3bc7c3bbc83762333d2e32bef30af1302862f9ca2c55e2adb82ac812a46b2819027fb027b9e2778624b8b2457c23b3922c9f210d11f6771c1dc1ba9a1b7d01a8f31a65c19a711633d162501581715805154291492513e3013bdc1369011baa103170f4090ee9a0ee5a0e8fc0d80b0c0460b19d08f1a0863e03828035df01e3e01b7b
  | 1 => 0xa691ca3c85a29959d9629d3799c8059a51294ebd932af8f0438adbc86ab483738836a4834fa82b5c826188221c81ea481b30812df7d9e67b24579968797187886977bf6703f26db746d8d86d78b6c8f16c6496c6056ac9767dcf67aaa6535e6529a64d22648ae63e4863385630c96259c617ec5ff905fc1e5c5b95b4285a31d594c25745b56cda55765554ec54d9d53de35196c500e74d9a74d76e4d4494cd6d
  | 2 => 0xf20a6f1873f0e7af06bcedb3eed4b1ec268ec224ebeffe80a2e766be5ef2e5c41e4e7ce3d5de3303e2474e1a8ade53ddde97dc6f1dc6addb7c6daae9da176d8d9bd77edd70e9d6cc7d68d9d41ddd3aa3d1dfcd17c7c9909c935ac4a8fc302bc21f1c20b5c09f1c059abe850bd9b9bd855bc533bc251ba853b8f19b8dd8b8654b8265b7affb465ab43a5b3838b2b69acff9acf36ac6c1aab61a8897a73a5a6acd
  | 3 => 0xff1cafdd62fd74cfd39dfd12cfad9efa8cef79b6f72c7f47f6f478ff37f3f371df2576f22c4f21b0
  | _ => 0
def H7_7 : ℕ → ℕ
  | 0 => 0x28dc128b0028aec27e7127c3027a232728f25ea4259d125356240b2235fc22f6c21c1c20a12204511f0c51edbc1eac61e1f71c7901c5aa1c39f1a01419b4519a7119151186a6185e1175bb16f3416aff155671509013bde131ee12d2e1204110c5110a6a0ee240da290d9e50d4fa0d1520c03f0abb80a8d30a6c709cd8085e0073e30711d07085059e5052da0508304de202c1802b92029e301e3e00a4f00a24
  | 1 => 0x629686175a610465fd705fc1e5f2c85e2345dce25d6a85c0135add25a5b859e8059cdd5797e5794f56d1e56c9456b7d5576553f88538d55385d5272b5196c50d42508f74fc014e6eb4d7b24cd4b4c0474bbb44b07748fe84890a45e3a443504392441c8640e354098b3f44b3dc2a3d7803c24038c55376233602435722330ec3302732e1932c953261d2f7f02f6fc2e77d2dbcc2ca242adb82ac6129ab129878
  | 2 => 0x9863d96edd96c1f965e394089932af9242291bca912f08e3058d2388c2b38c0a58bfe08bf9c8b25288b6b88a3587d9b879f986f998579985606853f285342847ec83c1c82a6a8276a824ae814bb80bd180a117f39a7f0037c15e7b01b7a48378c95785b878307771d37686375cd7752ed736f772014718c57170f714696d6416cd8c6cb536c6496c2fb6aad367e5a67e1367c766773d66570652da644c263835
  | 3 => 0xd0126cfa4ccec90ce2a6ce0decdcbfcd4b9cce97cbd83ca87ec9f4fc8384c7e79c7495c5d01c5853c416dc3f72c3339c2b14c244dc2145c1457c12b7c037abfb46bb50dba232ba215b68cbb664db4a6db2bd4b15a6b12f5b082bb025caf668aed1cad8efaceb2ac408ab6a0aac9aaa1e2a9620a7f1ca77e1a70f4a6960a66b2a58f5a3c85a23aca20c2a1c78a1bb3a14559fb939e0a19d4b09d2be9b9579b149
  | 4 => 0xfeec7fec30fe770fb6dff9de3f9922f835ff75c1f5859f476ff4102f374df34edf28b2f1721f167ef1303f120cf11f8f11e1efb5deded4ede82ec322ec268ec224ebeffeba12eb591eb14eea9b8e9ba7e873fe7dd1e7278e5e22e5c41e4e81e49aee4863e3e79e19eee17b5e1129e054ae0451dc6f1dc1cddb918db0e2daae9da5bcda1ced860ad8309d764ad64b0d57c1d3fd4d3f90d304ed2678d1dfcd08bc
  | 5 => 0xff260
  | _ => 0
def H7_8 : ℕ → ℕ
  | 0 => 0x70f166e4bf6e3c86e0496cb976b2b46493b63e1c5fd705cb65571ca56b9e567cc56370546af51fe04f2334b8f94a6044734c43a6e4227c3feea3beef3b3d53a553395de35a3431eeb310752e77d2d2ce2c5d42adb829878259d123f4422fe222957220bd204511ea071e2af1bd1b17e5915323131ee1228e10def0ee240dcab0da290aaa008df0086240703305733050290501004b1d048b7031d80252800361
  | 1 => 0xec268e271ee19eee0ec8e0adae014eddd90dd588db739d80b9d6b27d525bd4392d3fd4d29a8cfe43cf79dcec90ce2a6ca87eca537c6452c5d45c3f6ec3c6fc2011bfa58be73fb64c9b15a6afe78ad334ad26fab6e4aa01da7c61a45c0a3cf99f11c9a9409a5e296ba495de79267191c0e914e38e9a98d03b8c0a58bfe08a8a7880e187fc98475882a6a8105380e1a7e4fe7d57c7a7d87a7a575004736a9715c2
  | 2 => 0xff930f86def4595f4102f17c9f11e1f01e1efb19ed042ec64e
  | _ => 0
def H7_9 : ℕ → ℕ
  | 0 => 0xf80d5efb5dca57bbcdd59d4b08e9ed7b9106b2475dad6588ec176fb0c03f08e34
  | _ => 0
def H7 : ℕ → ℕ → ℕ | 4 => H7_4 | 5 => H7_5 | 6 => H7_6 | 7 => H7_7 | 8 => H7_8 | 9 => H7_9 | _ => fun _ => 0
def P7_4 : ℕ → ℕ
  | 0 => 0x1392001048000020
  | _ => 0
def P7_5 : ℕ → ℕ
  | 0 => 0x5041e94102a44006131026500031201768805f1510985481b02103c50c481520dc4c44712003a4c40414103a544001310105441d9300244c44794107e4c0041310805480c0210bc0c83d83004e4c01f132068548408100244c80092104a4800c9410024c80912112a4c4031300281486093000a548120300124c027d20
  | _ => 0
def P7_6 : ℕ → ℕ
  | 0 => 0x1750806b83024acc00112114a4805f1410fc500241620869483084017c5842413007e4c007143170084011320684801341013408069130090580091200d24c46f96101c4c00512121b040453500b84c0351412064401d1511164842a950004d08901530d4584088610445480b93109c4c42795302018008932034180071210065883f932114d445016108e50c65b500024c00e9531464c42b3400ea50c452100905001d1410fc5406295001c48001332
  | 1 => 0x1aa5440392014a5000c961196d442f9411944c48b93011a4c0101301ee0c01415012650002932112540134200c4d40071400285040f14113250443251196c80039622105440a1310acc80039210b4500081610a14c037a540c04c06e1301301044335321e4c4159310e24c0111401ea544318320c4944511300e04c81c9611b255021b5004c0407b9620e44c02f13021b48037b530444801a1500881441704102e080161400d054c459311d04c46b151
  | 2 => 0xae4c892b401104c42a9430d84c029121024500068320f84803d1630aa4800413212e48427930168184051320285843643201a0c07f1410324c07514219cd441f1100025004493009c50c331210f41880c0600664c830160086d44239530200c01c9410fa5440152100a4c4101400c05006294022e4c4101600d8d006725311e1846b141196cc03c8610184c81c95101a5002b3300765042c1610e65446106101c4c42d1300925009c83001050c86b41
  | 3 => 0x324c837b520cf4c02843107e5406d8600364c4040400ac4800e9430564402f1620fa4403633022294033d21
  | _ => 0
def P7_7 : ℕ → ℕ
  | 0 => 0x22990010300f6c8010b5102ed40033410bcd040742004e5c0189510965c4062640c64842f9510f44c42b920038d840a1520ad0800c8710100c818971018d800185202ed44049620fad802d1410b4584020710ec1c03fe100e81801c121076d882e1700195040f73209a5003ff300f15001a020018d8c101320be5c408c300a85000f72000a18042440012d8c2c141018d4c2b9300ac8c003d3001e0c01c1300825c01194110e5001b9300a688008b61
  | 1 => 0xe65440625008e54c0344003cd400b1400f7500281510105801695003bcc02182005e4c40e2620320c02a1700d2544090500840802b0300801c02694302ec402f36201c0800a04002c4c00414007c58c1d9310a6d840f621078d40008300f74c00ba2102418010a6302ec80355300e65040f25203a94c2a15003dc40379400a6d880392101a1802394009ed8427361016180081520500c40f61002a5c413930020480069310a60402c161092d843a820
  | 2 => 0x40500433300aa544170710085c83fb5109a4c8009710e24c01486003dd0c312300ba0803b96001e5c8169600265c0081210044c41286007a5c807952078cc004d320725483f15007894c0992006ecc010a520844c4033510740840635400d4c0079210705c024b5002ecc0340710f8d80199410ae508081620ad0c03f1600640800214201304010b610321c834b6200ed08431300680c4209320c05441d9410f94c01804300ccc4338200c21c816970
  | 3 => 0x5858c36b6000408026930076cc44395003dcc0140300ffc800993010cd001c96203e1800bb6300ed48433600345481a9420fc5003d0700c648036b620465841bb4002a54c210720ae4840817205650404a600d01001c1400e258c0512008c5c02b44203dc8404b6203bd0c3c53001d50036b4000f4840097205a5000f62005e58003d4100c5042f1410134c00bf430c40c02a071028484101500405c01e32003d8c02093003948004a2009458807430
  | 4 => 0x2a50c1b1400665840d9600465c4110700d8d402395003ad401e9420404c00a1200544841997103d90c3126010e5c02c17103b4c4035200234400695301e480239300120400394206e480159610b05440a1720794c438970076d040bd3203b4840996000c4c42d96302c4802396000f100160200261c436b300bcd80209400da4c02907006ed401c94203a484050720d61c804a6102650034b5103dd4c0215207e5c03197202c1c80d94003cd440eb63
  | 5 => 0xd132
  | _ => 0
def P7_8 : ℕ → ℕ
  | 0 => 0x1514000f54008dc401821002cc00075400ad840465400298c00262008d840555100acc003d41008d8001b630014c4032600150c00054200ad400365400f4c0047430190c005e40017d0003b74008cc003d5000850000e310014c0009200124c00217000d0c002b2100cdc40625001814000273003d04023630010c00054000a58002b73004d8c04363003d0804940001d040037100c5c401c30002d8800b6000d50002372015d5001d31000d8403d52
  | 1 => 0x24c003c4200a4c00006001418000f43007d50042600151000474001954401d40012d0004960003950002600019500295001708002130014dcc03060002d0000370014d8c03d620154c801371012d8c00170000dc801340004d8000b2001550800440003d9001330011d0804b6000b14804362008d000463000058400f3100edcc023700045000116000388403d3200ad8004d410044c00526000390803c4000dd0c01c21000d8c033630038c804741
  | 2 => 0x6dd00053201788004430017d0400b61012cc005b6100858003c60
  | _ => 0
def P7_9 : ℕ → ℕ
  | 0 => 0x730000d400073100190c00361001d4c007210018c000610001d0c0062100094400710
  | _ => 0
def P7 : ℕ → ℕ → ℕ | 4 => P7_4 | 5 => P7_5 | 6 => P7_6 | 7 => P7_7 | 8 => P7_8 | 9 => P7_9 | _ => fun _ => 0
def Z7 (s i : ℕ) : Bool := barV3 7 8 (SgenB 10 x7 o7 P7) N7 (idxGenB N7 H7) o7 s i
theorem l7_4 : ∀ i, 0 ≤ i → i < N7 4 → Z7 4 i = true := span_end 3 0 (by decide +kernel) (le_refl _)
theorem l7_5 : ∀ i, 0 ≤ i → i < N7 5 → Z7 5 i = true := span_end 46 0 (by decide +kernel) (le_refl _)
theorem c7_6_0 : span (Z7 6) 128 0 = true := by decide +kernel
theorem c7_6_1 : span (Z7 6) 80 128 = true := by decide +kernel
theorem l7_6 : ∀ i, 0 ≤ i → i < N7 6 → Z7 6 i = true :=
  span_step 128 0 c7_6_0 <| span_end 80 128 c7_6_1 (le_refl _)
theorem c7_7_0 : span (Z7 7) 128 0 = true := by decide +kernel
theorem c7_7_1 : span (Z7 7) 128 128 = true := by decide +kernel
theorem c7_7_2 : span (Z7 7) 65 256 = true := by decide +kernel
theorem l7_7 : ∀ i, 0 ≤ i → i < N7 7 → Z7 7 i = true :=
  span_step 128 0 c7_7_0 <| span_step 128 128 c7_7_1 <| span_end 65 256 c7_7_2 (le_refl _)
theorem c7_8_0 : span (Z7 8) 96 0 = true := by decide +kernel
theorem c7_8_1 : span (Z7 8) 42 96 = true := by decide +kernel
theorem l7_8 : ∀ i, 0 ≤ i → i < N7 8 → Z7 8 i = true :=
  span_step 96 0 c7_8_0 <| span_end 42 96 c7_8_1 (le_refl _)
theorem l7_9 : ∀ i, 0 ≤ i → i < N7 9 → Z7 9 i = true := span_end 13 0 (by decide +kernel) (le_refl _)
theorem l7_10 : ∀ i, 0 ≤ i → i < N7 10 → Z7 10 i = true := span_end 1 0 (by decide +kernel) (le_refl _)
theorem base_n7_055 : ∀ s, HasMonoSize 7 (gfn [] edges_n7_055) s → 11 ≤ s :=
  prove_base_mono (M := 7) (E := 8) (cap := 10) r7 x7 (gfn [] edges_n7_055)
    (SgenB 10 x7 o7 P7) N7 (idxGenB N7 H7) o7
    (by decide) ho7 rfl (by decide) rfl (by decide +kernel) rfl (by decide +kernel) (
    all_step l7_10 <| all_step l7_9 <| all_step l7_8 <| all_step l7_7 <| all_step l7_6 <| all_step l7_5 <| all_step l7_4 <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_zero lvl_empty)

def edges_n7_060 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(1,2),(3,5),(4,6),(5,6)]
def r8 : List ℕ := [26,28,33,50,52,65,74,76,3,5,9,17,6,40,80,96]
def x8 : List ℕ := [3876,4425,4754,9411,18459,40988,49376]
def p8 (pi w : ℕ) : ℕ := match pi with
  | 0 => ((w &&& 0xe0) >>> 3) ||| (((w &&& 0x4800) >>> 1) ||| ((w &&& 0x9303) ||| (((w &&& 0x2400) <<< 1) ||| ((w &&& 0x1c) <<< 3))))
  | 1 => ((w &&& 0x292) >>> 1) ||| ((w &&& 0xfc24) ||| ((w &&& 0x149) <<< 1))
  | 2 => ((w &&& 0x80) >>> 4) ||| (((w &&& 0x20) >>> 3) ||| (((w &&& 0x40) >>> 2) ||| (((w &&& 0x4a02) >>> 1) ||| ((w &&& 0x9000) ||| (((w &&& 0x2501) <<< 1) ||| (((w &&& 0x10) <<< 2) ||| (((w &&& 0x4) <<< 3) ||| ((w &&& 0x8) <<< 4))))))))
  | _ => w
theorem vp8 : ∀ pi, ValidPerm 8 8 (p8 pi)
  | 0 => validPerm_of_spec 8 8 (p8 0) [(0xe0,2,3),(0x4800,2,1),(0x9303,0,0),(0x2400,1,1),(0x1c,1,3)] [0,1,5,6,7,2,3,4,8,9,11,10,12,14,13,15] (fun _ => rfl) (by decide +kernel)
  | 1 => validPerm_of_spec 8 8 (p8 1) [(0x292,2,1),(0xfc24,0,0),(0x149,1,1)] [1,0,2,4,3,5,7,6,9,8,10,11,12,13,14,15] (fun _ => rfl) (by decide +kernel)
  | 2 => validPerm_of_spec 8 8 (p8 2) [(0x80,2,4),(0x20,2,3),(0x40,2,2),(0x4a02,2,1),(0x9000,0,0),(0x2501,1,1),(0x10,1,2),(0x4,1,3),(0x8,1,4)] [1,0,5,7,6,2,4,3,9,8,11,10,12,14,13,15] (fun _ => rfl) (by decide +kernel)
  | _ + 3 => validPerm_id 8 8
def o8 : List ℕ → List ℕ := oriStages p8 [[0,1,2]]
theorem ho8 : ∀ k l, (∀ w ∈ l, w < 2 ^ (8 + 8)) → DLive 8 8 k l.toFinset → DLive 8 8 k (o8 l).toFinset := fun _ _ hlt h => oriStages_dlive vp8 hlt h
def N8 : ℕ → ℕ | 5 => 4 | 6 => 43 | 7 => 128 | 8 => 103 | 9 => 15 | 10 => 1 | _ => 0
def H8_5 : ℕ → ℕ
  | 0 => 0x996217762140cad26af7
  | _ => 0
def H8_6 : ℕ → ℕ
  | 0 => 0xfe787e85a8e4c66e1272d0cb8cede7bf4e4b558bae039a7f439dee29d75d99b7c93ee191b53910b08c74478e8c76418717b16efa06d6dc679eb5da1e543cb517e648e85484df3bebe2fedf2b820267e51f4f11f0c61b26419e511252a125110e9b70e0660c36f0908f05e7d
  | _ => 0
def H8_7 : ℕ → ℕ
  | 0 => 0x7ffae7fdb97d5d27d3d57c9f078170760e67455d6ca7c6bf816bdd76bb56675446559963ca562914614e860bff5fcd45f8bc5efba5c0aa5b33a578b95477550f154f7164e8564e5f74cc5647c7c4441943e50438b9430c741fb43cf403acb5392e038f80347f533ddc3307932f31300492b3ff282bd2586e23e461ee5c1e3ae1c19e1bff01a4a0186c711a5f116030fe690c0840ac5e09d0705de600cef008e3
  | 1 => 0xfff5cfd1cafb721fa957f6a0cf2104f1072efdb6ee8a1ed215eae50ea908ea14ce8e20e8545e3be1e05bdddf74dc5d8db46fdaafed70efd60f3d3f96d2adad2a3cd2684cffebcede7cadbcc68a2bfe36beea4be3e8bcbbdbc1d4b912cb85a4b6dc9b3305aea74ad5dcaad3ba925ea845ca5481a458ba2d47a0f99a047a9f8a19b972982ab92f0d8fea78f2678eb4e8da3c8a018897c8847538360a80ff680334
  | _ => 0
def H8_8 : ℕ → ℕ
  | 0 => 0x9f8a19f7209e4289a3f199df8982ab941b09348a92f0d92dd785a10847537ba357b93d74edd7394172be86d46f6c7266b1586919c6742866f30655996376d624d061f426170b5b33a571a95491152caf4d8ee4cc564441943dd543db3430c73e18039d8e379ac36bdf3437c304132e6702d79d2b66a2b3072999a278af201d01c4dd1c19e1a5381a442149d9145581383c133b9108210de8309d070621b00cef
  | 1 => 0xfd1cafd167fc167fa957f90daf87b6f06a0ef8abe9650e405de3be1e1b53dc95adb12fdaad4d5544d2684ccfcdcc849cb4becadbcc66a3c3a52c192fbc242ba23eb7b54ad68fad5dcabfc5aad3baab31a8abfa85fea4611a3430a1bfaa1882a0f99
  | _ => 0
def H8_9 : ℕ → ℕ
  | 0 => 0xfb68ef89eef784fece5fe1f5ee0600de53cd3284a7dcaa2d9883ac57c0573fe513a49008d0a
  | _ => 0
def H8 : ℕ → ℕ → ℕ | 5 => H8_5 | 6 => H8_6 | 7 => H8_7 | 8 => H8_8 | 9 => H8_9 | _ => fun _ => 0
def P8_5 : ℕ → ℕ
  | 0 => 0x4e4800813100a48407110
  | _ => 0
def P8_6 : ℕ → ℕ
  | 0 => 0x1e1320bc4c00d9310c684006921088084199610c24c4058200b4504189610ae4c41f8600f25041b9310604c82013006e504109310904c80b9610285802d16103e1881894102e4841086003c4c40d06107a4c82d9410545440c14000e4c43f95104a54803860060440129320984c0351410704c005020
  | _ => 0
def P8_7 : ℕ → ℕ
  | 0 => 0x17588219510194c40c9720145c4069710621c0064210b8d800046200650409031018d40090200a05c8120720a65c4219410620800b850052188063300084801d8600145842f07000c4c8311500365841f1300015480c020054500149400204800d941004c400c06201e58011c620c6d40219710c45801d22009e5842f860042504015320ba544311400b448407920034c8411d310065c4199710474c831170006544051410b44800794005e4801e971
  | 1 => 0xb8d00049300b61c8281200101c0005310c6cc0292200ba584151700840c406961066584081600761c01a920066504031610171482a15108a1002e33004e5081c95000c5040133000a080121700184800e020091504081400b45080122104a0c01c9700c6d80013500425c40055106f4c40096002c0800b84001a544013200665440c07000248028140040580002100704c00f8200324c42d1300425441bd210965040f93106c080089710541c811a10
  | _ => 0
def P8_8 : ℕ → ℕ
  | 0 => 0x1250001430014d40014600055800516000318805c300124c006d7100b1c803140010d0000d500035c80243000718000d3200918006c50019100024310051c803130010c8403d6000f4c40246200c58000460014cc006c400194c4041600145c00057100acc00413000b584015620054c006d420035000147000754801571012d8003c3001d0c002571012d0003821014540053600070c000d7000358404b300034c405c7000adc00603000318002930
  | 1 => 0x414000310000c4100414000c3001d18002b600014c00256000ad00020700095840443200f084012500015000513000358003340010d8002970014dc002c31010cc006c7001b0c00153200ccc00296000554804960005544022700034c001c5000cd8000d420188c002940
  | _ => 0
def P8_9 : ℕ → ℕ
  | 0 => 0x743001d4400710001d4c0063000188400610001c840066500194c00763001cc000750001cc400765
  | _ => 0
def P8 : ℕ → ℕ → ℕ | 5 => P8_5 | 6 => P8_6 | 7 => P8_7 | 8 => P8_8 | 9 => P8_9 | _ => fun _ => 0
def Z8 (s i : ℕ) : Bool := barV3 8 8 (SgenB 10 x8 o8 P8) N8 (idxGenB N8 H8) o8 s i
theorem l8_5 : ∀ i, 0 ≤ i → i < N8 5 → Z8 5 i = true := span_end 4 0 (by decide +kernel) (le_refl _)
theorem l8_6 : ∀ i, 0 ≤ i → i < N8 6 → Z8 6 i = true := span_end 43 0 (by decide +kernel) (le_refl _)
theorem l8_7 : ∀ i, 0 ≤ i → i < N8 7 → Z8 7 i = true := span_end 128 0 (by decide +kernel) (le_refl _)
theorem l8_8 : ∀ i, 0 ≤ i → i < N8 8 → Z8 8 i = true := span_end 103 0 (by decide +kernel) (le_refl _)
theorem l8_9 : ∀ i, 0 ≤ i → i < N8 9 → Z8 9 i = true := span_end 15 0 (by decide +kernel) (le_refl _)
theorem l8_10 : ∀ i, 0 ≤ i → i < N8 10 → Z8 10 i = true := span_end 1 0 (by decide +kernel) (le_refl _)
theorem base_n7_060 : ∀ s, HasMonoSize 7 (gfn [] edges_n7_060) s → 11 ≤ s :=
  prove_base_mono (M := 8) (E := 8) (cap := 10) r8 x8 (gfn [] edges_n7_060)
    (SgenB 10 x8 o8 P8) N8 (idxGenB N8 H8) o8
    (by decide) ho8 rfl (by decide) rfl (by decide +kernel) rfl (by decide +kernel) (
    all_step l8_10 <| all_step l8_9 <| all_step l8_8 <| all_step l8_7 <| all_step l8_6 <| all_step l8_5 <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_zero lvl_empty)

def edges_n7_061 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,2),(1,4),(2,5),(3,6),(4,6)]
def r9 : List ℕ := [28,42,49,56,68,97,98,3,5,9,6,18,36,72,80]
def x9 : List ℕ := [932,3266,5393,8715,18445,4206,24688]
def p9 (pi w : ℕ) : ℕ := match pi with
  | 0 => ((w &&& 0xc00) >>> 2) ||| (((w &&& 0x4044) >>> 1) ||| ((w &&& 0x1099) ||| (((w &&& 0x2022) <<< 1) ||| ((w &&& 0x300) <<< 2))))
  | _ => w
theorem vp9 : ∀ pi, ValidPerm 7 8 (p9 pi)
  | 0 => validPerm_of_spec 7 8 (p9 0) [(0xc00,2,2),(0x4044,2,1),(0x1099,0,0),(0x2022,1,1),(0x300,1,2)] [0,2,1,3,4,6,5,7,10,11,8,9,12,14,13] (fun _ => rfl) (by decide +kernel)
  | _ + 1 => validPerm_id 7 8
def o9 : List ℕ → List ℕ := oriStages p9 [[0]]
theorem ho9 : ∀ k l, (∀ w ∈ l, w < 2 ^ (7 + 8)) → DLive 7 8 k l.toFinset → DLive 7 8 k (o9 l).toFinset := fun _ _ hlt h => oriStages_dlive vp9 hlt h
def N9 : ℕ → ℕ | 5 => 4 | 6 => 86 | 7 => 266 | 8 => 167 | 9 => 17 | 10 => 1 | _ => 0
def H9_5 : ℕ → ℕ
  | 0 => 0xf2110a6ab29120158c16
  | _ => 0
def H9_6 : ℕ → ℕ
  | 0 => 0xcfd68cb9f3c6300c61a5bfd09bebf8bad0fb7679ab414aa1bea453c96b22955a68fc5c8eec08da968da7f8d8ac8d1c68ad1e847c7823838118e811397c17a7a8ce79cbb78c257878e74fee71ef5706556f11b6afa06756d6745d669376303c5eb0d5cae75b69159b9253e255303a517984e74747bef446bc444d3424ae401a33fd023a84436c78356f326a9924ccb1ecdb1d0311abbc09a5d099e8076ce00214
  | 1 => 0xfe59afe232fd6d6fbd5af92fcf8338f82f2f6a27f56b9f3a48ede5bec37be6f06e50dde0aecdc6e4dc64ddaa73d7d2ad70d1d5375d3f7a
  | _ => 0
def H9_7 : ℕ → ℕ
  | 0 => 0x438fd430003d1093bb2d39ddd39d8d38fee37b7d36fad367af365b135e2535778353cb33d6733aa32faf92ef102e6682e51d2de6a2ce122b2cd2a9bb28fa126f31256fa24c0023c0023aa322733216c21f7141f0b91f0ae1dceb1ccd71cabf193fd18a32180751679515b2115a63144e613df21383d123d5122f81226110e1310ac80ff620cce50cbdf0c8ab0b4b908b310652e02ab501b74013a7012e600fb2
  | 1 => 0x74c9373b8672cf670ba8702696ec8d6eacc6e5ed6e4e86d6696d2866ca896b1356add86a8986a71c67db9679e8670df6531d6227e5e8da5cae75c18f5c0155bc835ba885b5ac5aeb85ad635aabb5a1625933c579695792b56dde5666f5608b548ec53a01526a3520e15142b50ecd50bc2509d6507cd501024f8f14f8314ed114d6a14ce894b1cc4a9da4a37549f934918f4853347eba46331441f543cba43c39
  | 2 => 0xbb0edb8435b7f94b6d9fb66c7b43e6b3e00b331fb2941af8ccae9cdabe19a9dd0a8612a7b06a6aaea6026a4076a3f86a32d1a27e3a0bb1a05c2a01269fa9b9f1dc9e4bf9dd1d9d7199b67a9a51f99bb89933998f43972b7965899638f9636a9471e92828927e191bcf919c9914a39044c9022f8bcdf89f35882528568b84a9784697841998156c80a6a805637e65c7cb817a2cd77a677641f75b2b7591374fee
  | 3 => 0xf6c76f4809f3050f0bf7f0920f076cefbb9ef0e8eee75eee6feeca1ed1feecf5cecbd5ea085e9c14e7569e637fe407ae14b4e1025e0b4adfc05df94cdca2bdc64ddb4abdb2dbdb17ddad24d9a9ad78d2d6694d62c9d4250d3ca2d305bd2b45d255bcf49bce806cd22acc79bcbb88cba03cb01dc90bac89dac7caec6940c40c8c3dc2c3690c2ae4c26b7c2522c2083c1ff2bf20cbdf3bbde0dbce6dbb921bb16e
  | 4 => 0xffceafdfc0fd8dcfd65cfd2e1fccdcfc052fbbb4f9bc2f7abc
  | _ => 0
def H9_8 : ℕ → ℕ
  | 0 => 0x663b363a7b5f3b55cf7c5b30b5b2965aea15a9fe57ab556ddd55325552c85067b4fcb74f8f14f7ac4f52c4ba924b6744a0f749ad1469f3441f5434ac4300040fb840d3f409ad4041d3f30c3e7423e0aa3d6383bb2d3b68d37ee6378c836e6135ad73577833d67322572f7d62d0d12ce12265962563824cfc24a83227db1e6411dceb193fd17de11404613ec211362102f10b7a80a5ba08e180652e060ea01b74
  | 1 => 0xcd64ecd22acbf97c7f2cc78bfc6eb5c5a53c59dcc566fc423ec2fefc2083c1868bb16eb9c37b8fd0b748eb6924b640fb2941b0dc7b07a7ad3a1acd85aa57faa553a9797a8b42a32f8a1beda13d99fa9b9d0949cb879c8a798f4397c659769e95b8792e41929b5920cc90ac98e9718d63d8cb788a0e18807a8703c83ce180a6a805eb7fd377ebf17cb81798cb788437841673ac6715e16dce46d28669af2679e8
  | 2 => 0xfe0e1fb3e9f8a29f7c03f7919f2657f10a9ef579ec9e3ebed0ebb0deba85e9577e942de80d4e4a15e37a1e2b5fe2a6ee1f09e0b4ae08f0e0877df61cdca2bdc64ddc007dae21d9950d7a8ad7394d4dedd48f0d3507cfbf3cf7c9cf052cf00fce105
  | _ => 0
def H9_9 : ℕ → ℕ
  | 0 => 0xefcd9e1583d6355ca9a0bba34b0f5ab0ce183e646104e5ba2a359f82e51d1cd2a1329d122610c84c05b2c
  | _ => 0
def H9 : ℕ → ℕ → ℕ | 5 => H9_5 | 6 => H9_6 | 7 => H9_7 | 8 => H9_8 | 9 => H9_9 | _ => fun _ => 0
def P9_5 : ℕ → ℕ
  | 0 => 0x1a4801612004650406940
  | _ => 0
def P9_6 : ℕ → ℕ
  | 0 => 0x9818031161080180209521ea0c0209620c65847f830082508299610004c428943076480409200c85080414003e504591420340c4228500c24c42a9410c65442813206854c2993103e54431141100d400e0300aa4c41585110a4802a951160544131610f20c4771311325042c9300c25040895309a4c4051630a6504259310864c44295007e4c0081510d28404095013a504351611444401695004c5442c9320485402893204c484511411105041a131
  | 1 => 0x12450858131100cc02694105c4845d1400765001d15201e5441496116250011961154540351510604c40794101c480079610a6544051530224c013141
  | _ => 0
def P9_7 : ℕ → ℕ
  | 0 => 0x5c0c80182009450435920001148069310055444804004ed4c411510945842797000a580459400644c0003100885002412105318805d1007c4c40293005ad44238700885c0003400764c40bc62078cc40175307e1003997106a54c1d141036184501300141804d9410085c047b20084d483f54010654c1693105854c1696106a5405094005ad040c44013e1c026b610f4c801a970092d841a0311425c0109530be4803d5300f0480062300734c001310
  | 1 => 0x381c0329400fe1c0341420c0d80221300d4484049500825c02187008a4c034152026d4c0795000c5440e050034504229600050c446f500ca5802a9430d84c04d8300825405095007a5842f9500aa4c8013500d8d000c5300345c41d16103454443151022508003200aa50047d300365803197209e4c42b9410d8d800d1610aa540179400da48043171000d4014d420a85002c9420984c02b9611045c418b640014c80c8500a8580158200904c00bd42
  | 2 => 0x745c41812105294c13a520174c02793003cd803e9600170800f26402ed4c47d4007c54c3504002e94036330076cc446f3010e4c01e13105e58009a5402c548509600f6480439310dc0804286001c5c41a963118504419430c0d8c28120004cc00136305acc42412005ad843e9700b8d900036305a504003600584c40b13104c0c00714111bd001e95104258c071611321801d1510480801793200c5840213000499408830092d8c0a94300099006030
  | 3 => 0x124d40241720825803e0600929880b142036500081430501800794011bc80079700945443e950004d800b16203e08036350052d401a93008494c0682008618018b630440801c9100cc504065310680c0408400c85042d12005e54035152052d444086004ed44311410125003e94000c5040e82005e5c00f36301258032161005d0c2094000c5c4261500c45840bb51062980015410c45440036100e08046f4307a5c42d9610b90c409b510605c809020
  | 4 => 0x125c00033009e54c36320084d4418d410365c03a55202a4c82d971
  | _ => 0
def P9_8 : ℕ → ℕ
  | 0 => 0xbd0801762008cc001320004d800234001818002f6401d1400554000599002f5300bd400644001e54001b6300b8c002f31004d0001752011544047540064c00353000854002f630154c80853201350400d42005d9000d6000d5480794000d58405d300110c001b700115c00196000650007d42005c8402e400065400653200bcc801761015148003300114c402d200085800453000f1c802f5401b4c807b700130c005c3000f50804870002d8c08050
  | 1 => 0x13580079700190c000d400031c00587000d4c401c7202110002f6501714001970008d40001300034c801b3001d1c003d5200f1c002c30021180023630210c00236101550801b6000d14401b40006d8401b50013d4c0793001f18803a60002d8407960008d8005450000d8400c4001ed40034500058840747201110006c300135c406c60005908082500005c000a6400bd8407b400085c00026300f5c0062600030c002e6400f5400014000f0c000160
  | 2 => 0xd71008dc003c40005d5005d3201d0c002f2100354003d310129c002d3100bd0c02f6201b5000037000754803d6201ecc00757100f5c4021300151c00436000e1800214000448007b6000b99405a7000d18000d30005cc80034000bd8002f51005d040036000f50002f40
  | _ => 0
def P9_9 : ℕ → ℕ
  | 0 => 0x76000198c00740001d8c00720001d8800753001d0c00710001cc800765000d40006200018c000252001cc000610
  | _ => 0
def P9 : ℕ → ℕ → ℕ | 5 => P9_5 | 6 => P9_6 | 7 => P9_7 | 8 => P9_8 | 9 => P9_9 | _ => fun _ => 0
def Z9 (s i : ℕ) : Bool := barV3 7 8 (SgenB 10 x9 o9 P9) N9 (idxGenB N9 H9) o9 s i
theorem l9_5 : ∀ i, 0 ≤ i → i < N9 5 → Z9 5 i = true := span_end 4 0 (by decide +kernel) (le_refl _)
theorem l9_6 : ∀ i, 0 ≤ i → i < N9 6 → Z9 6 i = true := span_end 86 0 (by decide +kernel) (le_refl _)
theorem c9_7_0 : span (Z9 7) 128 0 = true := by decide +kernel
theorem c9_7_1 : span (Z9 7) 128 128 = true := by decide +kernel
theorem c9_7_2 : span (Z9 7) 10 256 = true := by decide +kernel
theorem l9_7 : ∀ i, 0 ≤ i → i < N9 7 → Z9 7 i = true :=
  span_step 128 0 c9_7_0 <| span_step 128 128 c9_7_1 <| span_end 10 256 c9_7_2 (le_refl _)
theorem c9_8_0 : span (Z9 8) 96 0 = true := by decide +kernel
theorem c9_8_1 : span (Z9 8) 71 96 = true := by decide +kernel
theorem l9_8 : ∀ i, 0 ≤ i → i < N9 8 → Z9 8 i = true :=
  span_step 96 0 c9_8_0 <| span_end 71 96 c9_8_1 (le_refl _)
theorem l9_9 : ∀ i, 0 ≤ i → i < N9 9 → Z9 9 i = true := span_end 17 0 (by decide +kernel) (le_refl _)
theorem l9_10 : ∀ i, 0 ≤ i → i < N9 10 → Z9 10 i = true := span_end 1 0 (by decide +kernel) (le_refl _)
theorem base_n7_061 : ∀ s, HasMonoSize 7 (gfn [] edges_n7_061) s → 11 ≤ s :=
  prove_base_mono (M := 7) (E := 8) (cap := 10) r9 x9 (gfn [] edges_n7_061)
    (SgenB 10 x9 o9 P9) N9 (idxGenB N9 H9) o9
    (by decide) ho9 rfl (by decide) rfl (by decide +kernel) rfl (by decide +kernel) (
    all_step l9_10 <| all_step l9_9 <| all_step l9_8 <| all_step l9_7 <| all_step l9_6 <| all_step l9_5 <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_zero lvl_empty)

def edges_n7_062 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(3,6),(4,5)]
def r10 : List ℕ := [10,28,81,84,97,98,100,3,5,9,6,18,40,72,48]
def x10 : List ℕ := [916,3233,1354,12803,18446,20592,8316]
def o10 (ws : List ℕ) : List ℕ := ws
theorem ho10 : ∀ k l, (∀ w ∈ l, w < 2 ^ (7 + 8)) → DLive 7 8 k l.toFinset → DLive 7 8 k (o10 l).toFinset := fun _ _ _ h => h
def N10 : ℕ → ℕ | 4 => 1 | 5 => 21 | 6 => 187 | 7 => 516 | 8 => 306 | 9 => 28 | 10 => 1 | _ => 0
def H10_4 : ℕ → ℕ
  | 0 => 0x55b61
  | _ => 0
def H10_5 : ℕ → ℕ
  | 0 => 0xf6389f3993e9129e3e81bfc56b449fb0ad2aa8849c8089bc8391dd36e1895df72595954d8c9481213d6db3bf1634c45279c2198fd
  | _ => 0
def H10_6 : ℕ → ℕ
  | 0 => 0x5c5f15ac99594b759431593b0591a158d215873d57a5956dcb54e4152be351c965113150e144f0304e8604e66b4da2b4d62e4c3ab48a154879b4087c3cef33c4543c19f387833576034c6733d8a33d10333c93146d314512ef4b2eecf2ecbb2ebeb2e91f2bb182b5ae269b9266ef23e9722a1b212f1203e61c1c31af09191c31916e0f2ca0f1030ea5d0d6c30b0fd0ab900aa650877e0804904ba900991003c2
  | 1 => 0xb2a81b253eb2330af647adc1aab59ba9a99a629ea3f1fa0b2e9c3789b621991e69900e98b7697a3797a17979c2961379504e92cb991b208fd4f8e6c68d2b18bc278a54d898f887d93871e08608185bf085160824437f7247ec887ec167ea6c7e4ac7dd7d7dc2c7c80e7a63c72bd97221271a3f70dd16da3e6c31f6b7d56ae3a6a81e6913268580664f765b6464fa862da561e9e616b95f31c5dc525d7805cdcb
  | 2 => 0xff1adfdf78fd86efd2c0fcd00fab2ff6ccbf62abf3649f23d4f0bb4f0293e993ee968ee89e2e7986e7058e4a8ee0e35e0ac5df486def29de499de47bddd9add1e8dccb8dc442dbfa8db61fda4cad9ee6d9a17d7c04d7a61d7854d7820d39acd1437d0a31cf985cc317cbfe6cbe82cba33ca4bdca1beca10cc73f6c3109c2adfc2693c231fbe4b7bb747b9f2cb54b9b3bbdb2c16
  | _ => 0
def H10_7 : ℕ → ℕ
  | 0 => 0x2856b2807a2776c273fe273ba266112597f256112532f2445823c35236282298b221832215d220c521fcc21e6621c55215991f8cd1f5c41e6801d27c1cc021af091a7931a4ab191df189bd174da14d10143d71432d141ba1313112a67116cf10f390f7ec0f1850df450dca20d54e0c8910ae380a86f0a1a009b0109ab108bf908bb608b8307ca007ba3072ea06bc5063fb04b2e03c5c027c90204701b1101551
  | 1 => 0x426e4415c740e7e40e67405f5403a0402d93e11f3e0733dff23cfd13cca93c4d73c1b93be8c3baab3b8693b8573b6593b4603b3483b1e03a85b3a18439aff399f0389d138797387833855e383e7383a0382c2382ae37cb537b4c3769037494371b836db83630f35f4735e9335cbb3507c3421332c1d3270b326ec318163173930f5a303662f7f12f7ad2effa2ed0a2de1d2af832ab692a8b72a402291fb28aab
  | 2 => 0x60e3f60ae05ffa55fab75f4e75f0a15e2295d99c5d56f5cf8b5cabc5c5ad5bd2a5af9a59b1a59a12595e9591a1590b357aeb5723356d1c56a515696355f7753bba535b651f5051b22508ea50776501fd4fabe4f9ea4f7ab4f4fe4f2a34e15e4df974d2634c3fb4c1f24bd664ba964b38c4b26c4b07649ebe49a8f49914495244951d479f14754d473b845f9345ca9453c4452db4463643f7743ef942bfc42a91
  | 3 => 0x83e4d83464833b482bda8288581f8481bca81442808988079b7fce67e7047e3137df347dd8e7d22d7d1dc7c70e7c5157bf2c7b9607b1727abd97a4fc794b17948c7908e78dd876dcc7671973e927313e725d8710be70dd170b6d708776f7ab6ee8a6e7a96e5316e03a6cfbe6cdd46cc0a6c7b76c0086ba946ad5f6aa4e684a466d27666ec659476524e6519164c846409f63b6a6339462998622ae61fce6119a
  | 4 => 0xa0faba02299fded9fbcc9d6d59c5389c2109b9029b4c59b2109b15e9ad3f9ab819a49e9a49699114988e397a37975a7966859636e9605a94d2c947ae944b9933719310892c2b91efd91aff9165f91366910879107890af7905ce904f18fd4f8fad58edb98ed108ec388ea308dc218d5958c5e18ba598b2aa8af7e8a93c8a32c8981a8876f87e858787886c918663d8650b861a285b3e851a484abd8485584009
  | 5 => 0xc00b2bff95bff4fbfdd7bf27cbee49bec64beb1abe837be600bda04bad10bac6bbaafdbaa0dba376b9f2cb9dc4b9c14b90afb6febb6bf4b6b7eb69ecb695bb3e95b3447b333bb2b13b22c8b1b17b1733b13dbb123db018eaffdfaff7baef48aedecae6dcae6cdadc5dad55ead494ad3b6acb71acafbac375ac312abe85aaf38aabd9aa3c2a9fe6a890ca856da805fa71d3a6f39a629ea49fea4706a3a4ea1e7c
  | 6 => 0xe02ffdfe6ddfafadfaacdef0ede2a0dcf6fdcccfdc452dc017dbd49dba57db6b2db332db1bbdad69da1afd9886d8309d7907d765dd6d33d6601d5c85d56a5d4c3ed41d3d3883d2f3fd23a0d230bd19e0d1524d1193d06d0d01ffcf51ccf033cefeaceb88ceac9cdf54cc317cb984caa83ca29ac9a63c83e5c7d71c7b44c7739c7412c687fc66ddc5cebc5720c56a2c4418c3e8dc3decc2610c1fedc1450c131f
  | 7 => 0xfcdfffc65afa46ff99e3f97fff8e0bf87a2f82c3f8074f78e2f6c5df67cef59a6f5933f4ee6f4ae1f3fb5f3839f2ef9f29f6f219cf2092f1689f114df068deff52efdd2ef625ef297eed6eededced891ed23ded230ece70ecbf3ec1d4ebf3bebdc0eb97beadc7ea1bdea062e98e4e8d95e80c9e75b9e5e94e5848e53d0e4f40e4b41e475be431be40c0e3f20e332ce2ca2e2287e1872e1670e0bf9e0974e06fc
  | 8 => 0xff0ecfeef0fe985fdab7
  | _ => 0
def H10_8 : ℕ → ℕ
  | 0 => 0x319072f7f12f3b72f1292e7412e58f2d3b52c3a42b39a2acf12a10526ebf263bc25d0c253a42330d22cce22c502298b2216a2143b205dd1fbbe1f8161f79a1f5bd1b00b1a793189bd184b2168801657c1520e12a8411c9511bd8116470fc920e6480e3ff0e34f0df490d3d10d20b0cb820c6ce0b8ad0afa20a58f0a42a098c0097e9093f20695c03ce603bfd0393d034520281101fc10188a017820110f00eff
  | 1 => 0x61b79619d160d195e2605d2275c2fc5bf335b37e5af9a5adab5a5965933356c6956963551cc54ed65423853cec518ea516584f70b4e5ae4df974d5004d0934c3fb4c0de4bf2e4b26c4ab4d4a7eb4a0e049eb249a8f4991448deb488c7487c548747473b846f32456b54463643b8842df640e7e3ef2f3ecca3daa03d0a23baab3ba223b06b3ab6d39d0638de23878338769386c3382c237690363fe362e035f8a
  | 2 => 0x9747996772966f495d429594b954f494edf94807946e493662932ab92f98928039210f9136690f359019f8ff748f5678d9b18ce1f8c2b58ab648a38c8994c867288663d85a15857a083f1d8331a81a2a81968815dd8079b7eb447ea3a7df967d3647bf2c7b8477b59678a2377f167729372ff771c7771982710be702e27000c6e9a76e4826e3556da506c3676bc2e6aba368c18688ed673c76489562bb66210d
  | 3 => 0xd3a78d2f3fcf9d7ceb88cc7ffcc5bfcb828ca8fbca5aaca29ac97fcc9642c77e4c7518c687fc56ffc3697c1255c0fa4c00b2bfe38bf25bbe837be600be28fbdfcdbda04bd8fdbcbc1bb839bb442baafdb9f2cb9d83b9addb689ab665eb61fab5ef8b3a65b22e7b1dacb1d57b1a7bb0049ad09dac20dab0fbaa7dfaa3c2a856da7372a66caa463ba21e5a11f3a0fab9fa339f1f99dba09cf6d9976497e0697baf
  | 4 => 0xffd59ff058fe022fdfa4fd585fcff0fc858fc130f73e4f6d17f5576f4ed1f3e73f3cd6f3348f2a2ef25e8f2165f10c1f0533edd29ecbf3ebf3beb97be9be1e8e8fe8855e84f7e7b0ee78d7e5426e2287df7a3df2abdef0edde43dc155dc0a1dab45dab00da7b0d8bf3d8339d8309d765dd763bd6639d6601d6260d56a5
  | _ => 0
def H10_9 : ℕ → ℕ
  | 0 => 0xf8779f77fbedd67e655dc6582adac4a9688a7d2aa5c66a586f9c1d98ea688af7e818a6747b96be575d4245a70f52d1a4868d3e6653cfd132bf232b743135f2fae2197e4174da
  | _ => 0
def H10 : ℕ → ℕ → ℕ | 4 => H10_4 | 5 => H10_5 | 6 => H10_6 | 7 => H10_7 | 8 => H10_8 | 9 => H10_9 | _ => fun _ => 0
def P10_4 : ℕ → ℕ
  | 0 => 0x4120
  | _ => 0
def P10_5 : ℕ → ℕ
  | 0 => 0xa15200a5403314005e480149410164c40395203e5040585007a5080b1510784c41405007a4c80394203e4c4131520244801314211a5045c130
  | _ => 0
def P10_6 : ℕ → ℕ
  | 0 => 0x17e54c5815021858c573303625042b11009e5445b15001c4c46b16214c548c38621485803496101c5840d9312351446e1301905881616114c5084c13015cd40561600d254453161214504111200b85046a1402225003113015cd00091513504400b9312145445ed411aa544e0941096540573100f05841d1210d24c4488300ba5002e1511c24c8271211020c09c96125d4c8321300d25044a1510d858c559610d84c46714110c4805492001c5047f161
  | 1 => 0x2e5442b8302d24c0279611284c40b9410a85440816114e5085294103a4c0135423224c44a1410904c0479303020c02204201a1480a1310a65049593014c484d81612445005745127244086121024584d21611b45808b9510b25088415000658c39130024504009630004c8c89410745448c8600ee4c4bd9620405442394135e584691520161840e9610e4500699621ee4c47a96114e4c4bc1511a4508641520de5847b94118a4805e9211824c016141
  | 2 => 0x71510064c8a22200024c8001531565445732007458c5594122c140671212aa4c4828502e25009e9603b650c5886213e100361510c85000c1630585448d9410aa0805f93202858c8b9411765806a92127a4c05b9610e45801345016050040040236584161101525804106015d4c4b61600445801d14127a540135301da508321601a6548259203980800b961190508391500204c4b61500ea5803116004c8842a161
  | _ => 0
def P10_7 : ℕ → ℕ
  | 0 => 0x3a5848f960086d840d0201844c0763300e754c4b1502305402c54217a1c8659610d8080089702280c01d8300ea5848517004c5406517318450034d421c0d943bd320e25c43196201c5c06594111ed80224200894408497217e5cc0e9511d8d802895105ad848f5601641c00e151046cc00896008050031d3107d4c84bb41048d8c3bb1002e54c2f32004c5000816102a50c3b0400f00c0541730a05c41886001850023f401ac580185301ac54003970
  | 1 => 0xae5001b1610b848023f531bfd087d141248100459710d2d8445173061080261510ccd846fe430285802993012ed842f9601bc1c0763500c6d8c909401c84c83697018ed802315020ad806fe4204648016a630505c46ff2116e5c0371610c7148519310f64c02c3630bd5444095113ad802f87104c58065b510e05c4261411905443694012ecc43f97112c500231400489945702007cd80548211ac5cc7b36506e1c41e9301121c0689721a010085140
  | 2 => 0xe58094b2023e500125520ba990381701b254416151196d042c2640f0504911400781808492004c5c023e4214e5c4268501bfd0c76532046c80459600a49901c1700bd5045117114ad80340300be5c02ad30238d9404040236d9423f311a85443696011650047d421664c021a6403c0800e97108410052b40062100190200eed8c4b1701c84c04f1301905047d1611ea584911500080803f1610041c01f2630fa5843597008fd0c23f521bfc8087b65
  | 3 => 0xe25447d341146540421302305006b97305a8806094000e4c82f9301a65c4293601a24847513017458498070140500294520bd188018201b05c4975601824c01f9611a8584289711704c02e1501a01c00684023a4c01d9421265802593024a5840a87013ad8411c6105ac8423f2109b1845196014acc0039301865cc51160130d8c471400585848e92102054426d51196d842f94006c5c45d17308c4c0421310d2980401410b85802e1700cc98c47b63
  | 4 => 0x1e4c08886008f88094d300e05401414107a1482617100a984061702081c026a50186584609600d2c846f0601a65802f13019b5804b16013a98834c320bd0c40c9322445c00a15017454423f420d05084c2611a45c4129201785c07a1610925802f9500bcd000286100b54404d430bcd402ed4207c8800f13125cc407d3610b10c80b93200a8401236002a5cc763400e55803bb5019208047a6423a480061500a5508541310bb1484186008fcc038160
  | 5 => 0x144480672610184c0428310475447793121c5003bb6001e5c0278200000c02b9501bfd002a02008f8c84e1500605802714109858423e5108f8c023f1018e9900c02008c58092b6104888002d300e05006ff500185803e95125d4c01416105c1c0531700ccd945f0210c6d88609700c4dd8699501ac4c82eb650741c07586004c1880c95207a5c08f9700285c04e160026080059310160c00713014058081830162984729600a4d94371510dc5044b951
  | 6 => 0x100544651400585040895012c48025020089580551600f8500551502014c0871600ef548389410f85cc11b50060c40201600c408023f320704c03bb301144802c8721d61c00a1401c85c011b400965c020150178484851500065cc37973194580851600284c0651301545003592009c5845015004658031d4110c5c44b1300eed006115012e504141510665c08c170012080813632445802d1700b2500240700ae5c058c520ac5004017108fd4002c50
  | 7 => 0xfa5c4281410385847113007e5c41e07012e5843a9511f8d8023f5123e54023f2000b588768200225006b14005b508081710e25840e1410eec80980400b85003bc421bfcc03a1700dc5c44b93107e504600211d45005617211c5c0651702305801013000e5001015002050400820046d804c8520585c42017010c5443e1300bccc00e9411084c82715112ed4458b6000e5409894011c54031a10060d8031d3204a5c00e17314ad40820600bcd803a941
  | 8 => 0xe54c1b1511405c03f171
  | _ => 0
def P10_8 : ℕ → ℕ
  | 0 => 0x20d000a9300029d006d50001d0c025700055c0024300349800a35001fd0c04d600018800256100358005870001d4c007620264c0083500074c802450001d8c09b600155c00245202518004160001100074400074c006c5000e9c00b532028cc00cb4001fd0802d5102ac8401d5100dd940553000dd4407e430055440d44001f9440cb7001310005440001c8407e4201fd480073001754800d7000d994006300085c802d420095440155000558407e60
  | 1 => 0x1d18008b50022d000365301b10007f610194c807f6503418000d5002ad0005a700035440817002adc00bc3000dd0408b3001f98400d3201318001430026500007420191800813000b5000645003250003d420154c807f5101314007c5001050006c3000750802a750089d40a950007148012750325c006d32001d8404130028d800836003558809b700015800436000510005d7100714003d3000c480006520051800897002654002d300130c000640
  | 2 => 0xdd4c02b76008dc800631001d040cb300075c80c2700350c00137200f10003d3202510007f300284c007f4001358400d31007580045520315840064100f4c40375201b18003c410020c0005410131880446201fd800645200b0c00bc500225800062101710004d52002dd80a14000cc8005c300028c002d5200b0c4037310155080075202a580054620095880927000b1880c460013540074300031400434000bd5003762012dc000751028dc004330
  | 3 => 0x171400a9700195c80c930026d000334000898005c600094c808140010dc00ab500349c0015320105400943000dd0804d51016dd802060009540036430265c00a1600155c80837001f184036610054c00364200dc840815000c58005d5001b54804b72001cc807d51026d4008330032d40036210174c80ab3001b18808b70010dd800d40017d4c0a1500105c00154200cd400363200edd809b300265800556100514000731032d800063200199002d41
  | 4 => 0x1f94803d40001d400387000558003360028d00037610341c003c60022d8002d3200ccc00072002ad8003c3001f8c809b2100b100090700270c8089500225000c950003d500b430001d9400d42010d400075401cdd80a17000550002c600224c00066500dd0c064400310c007e5002918800c4001add80a94002058002d50001d900c9600091000c070
  | _ => 0
def P10_9 : ℕ → ℕ
  | 0 => 0x1d500074300195000753001c840072000188400653001880007300018c000610000d9400741001d0000761001cc400764001d4000641001cc800263001d0800751001d8800752001c4000360
  | _ => 0
def P10 : ℕ → ℕ → ℕ | 4 => P10_4 | 5 => P10_5 | 6 => P10_6 | 7 => P10_7 | 8 => P10_8 | 9 => P10_9 | _ => fun _ => 0
def Z10 (s i : ℕ) : Bool := barV3 7 8 (SgenB 10 x10 o10 P10) N10 (idxGenB N10 H10) o10 s i
theorem l10_4 : ∀ i, 0 ≤ i → i < N10 4 → Z10 4 i = true := span_end 1 0 (by decide +kernel) (le_refl _)
theorem l10_5 : ∀ i, 0 ≤ i → i < N10 5 → Z10 5 i = true := span_end 21 0 (by decide +kernel) (le_refl _)
theorem c10_6_0 : span (Z10 6) 128 0 = true := by decide +kernel
theorem c10_6_1 : span (Z10 6) 59 128 = true := by decide +kernel
theorem l10_6 : ∀ i, 0 ≤ i → i < N10 6 → Z10 6 i = true :=
  span_step 128 0 c10_6_0 <| span_end 59 128 c10_6_1 (le_refl _)
theorem c10_7_0 : span (Z10 7) 128 0 = true := by decide +kernel
theorem c10_7_1 : span (Z10 7) 128 128 = true := by decide +kernel
theorem c10_7_2 : span (Z10 7) 128 256 = true := by decide +kernel
theorem c10_7_3 : span (Z10 7) 128 384 = true := by decide +kernel
theorem c10_7_4 : span (Z10 7) 4 512 = true := by decide +kernel
theorem l10_7 : ∀ i, 0 ≤ i → i < N10 7 → Z10 7 i = true :=
  span_step 128 0 c10_7_0 <| span_step 128 128 c10_7_1 <| span_step 128 256 c10_7_2 <| span_step 128 384 c10_7_3 <| span_end 4 512 c10_7_4 (le_refl _)
theorem c10_8_0 : span (Z10 8) 96 0 = true := by decide +kernel
theorem c10_8_1 : span (Z10 8) 96 96 = true := by decide +kernel
theorem c10_8_2 : span (Z10 8) 96 192 = true := by decide +kernel
theorem c10_8_3 : span (Z10 8) 18 288 = true := by decide +kernel
theorem l10_8 : ∀ i, 0 ≤ i → i < N10 8 → Z10 8 i = true :=
  span_step 96 0 c10_8_0 <| span_step 96 96 c10_8_1 <| span_step 96 192 c10_8_2 <| span_end 18 288 c10_8_3 (le_refl _)
theorem l10_9 : ∀ i, 0 ≤ i → i < N10 9 → Z10 9 i = true := span_end 28 0 (by decide +kernel) (le_refl _)
theorem l10_10 : ∀ i, 0 ≤ i → i < N10 10 → Z10 10 i = true := span_end 1 0 (by decide +kernel) (le_refl _)
theorem base_n7_062 : ∀ s, HasMonoSize 7 (gfn [] edges_n7_062) s → 11 ≤ s :=
  prove_base_mono (M := 7) (E := 8) (cap := 10) r10 x10 (gfn [] edges_n7_062)
    (SgenB 10 x10 o10 P10) N10 (idxGenB N10 H10) o10
    (by decide) ho10 rfl (by decide) rfl (by decide +kernel) rfl (by decide +kernel) (
    all_step l10_10 <| all_step l10_9 <| all_step l10_8 <| all_step l10_7 <| all_step l10_6 <| all_step l10_5 <| all_step l10_4 <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_zero lvl_empty)

def edges_n7_065 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(4,6),(5,6)]
def r11 : List ℕ := [28,34,49,52,65,74,76,3,5,9,6,18,40,80,96]
def x11 : List ℕ := [916,3234,1353,4705,10253,20494,24688]
def p11 (pi w : ℕ) : ℕ := match pi with
  | 0 => ((w &&& 0x70) >>> 3) ||| (((w &&& 0xc00) >>> 2) ||| (((w &&& 0x2000) >>> 1) ||| ((w &&& 0x4081) ||| (((w &&& 0x1000) <<< 1) ||| (((w &&& 0x300) <<< 2) ||| ((w &&& 0xe) <<< 3))))))
  | _ => w
theorem vp11 : ∀ pi, ValidPerm 7 8 (p11 pi)
  | 0 => validPerm_of_spec 7 8 (p11 0) [(0x70,2,3),(0xc00,2,2),(0x2000,2,1),(0x4081,0,0),(0x1000,1,1),(0x300,1,2),(0xe,1,3)] [0,4,5,6,1,2,3,7,10,11,8,9,13,12,14] (fun _ => rfl) (by decide +kernel)
  | _ + 1 => validPerm_id 7 8
def o11 : List ℕ → List ℕ := oriStages p11 [[0]]
theorem ho11 : ∀ k l, (∀ w ∈ l, w < 2 ^ (7 + 8)) → DLive 7 8 k l.toFinset → DLive 7 8 k (o11 l).toFinset := fun _ _ hlt h => oriStages_dlive vp11 hlt h
def N11 : ℕ → ℕ | 5 => 1 | 6 => 33 | 7 => 144 | 8 => 127 | 9 => 17 | 10 => 1 | _ => 0
def H11_5 : ℕ → ℕ
  | 0 => 0x1e889
  | _ => 0
def H11_6 : ℕ → ℕ
  | 0 => 0xf1a10e85a2e2b28e1ebadb782db241cc76ec84a8c6c74c31f0c11f1be477b99d59fd639808a93b4e847e47ed477ce0f708e56aca069c1564fe264fe1398a934e103396622d160ea310dc640d5d20bb4c03bd3
  | _ => 0
def H11_7 : ℕ → ℕ
  | 0 => 0x6dae9676286748f64bfa6351e613f25c6805bc075b7a05a7175831157e67551ab539e94ce5a4b992452984521e4486d434914099f3f95a3d3ae3cddf3c72c3b08b3b06638128371673597e3597234ecc328c9322bf30c9f2f01c2ead42c42f2bdb42b3ff290a0277c926dce2561123e1823a82214741e4df1e3e51c4e91a02a18348173e815a231402c135c31247611dae0e1c20b3e208ebd04ce7019e601470
  | 1 => 0xe3b3be34bce1c03e0688dec28dda9edd5e0dd566d8780d803ed7a51d7872d6917d43c5d2916d11a0ce3e5c8f7ec6de2c4448c2c7dc1de1c0862bfb11bdf4fb6e42b58fbb44f4b447ab4013b2adcb0fd8aa83ea8bafa87e3a49d4a3c28a36e0a20909fea89e5e59d28b9bff394b3893d8d92de792b3c8a80f88cb187469865388524a844a383624822b0811d280ff4801497dd3878d6f77def7235c71ed16e30a
  | 2 => 0xfd524fbf53fbaecfb2ecf8730f6c1cf4d64efd23eedd7eeb14ec27cebbd5eba49ead86e9b22e7ca0
  | _ => 0
def H11_8 : ℕ → ℕ
  | 0 => 0x975339326c92b3c8ed1c8d08c89a8186b8986538801497faad7de537dd387a97f7777e75cfe70a7d6ebe86e58e6dae967bc465c725c45e5bc075946758eb55797a56feb55dcd551ab53943511814ce1c465884638445f7e4521e451ed44bd33f95a3c50f3812836165350183178f2dd9c2c2782a3fb23b0022573217631e3e51d0041c4e91bb611891a1834811dae113a7103840f0f70e9e70c01b0861504da3
  | 1 => 0xfe664fe039fd524fbf53fb3f8fb3d1fa4fff93e3f747bf3ec6efd23ef6fae99fde7835e72cfe72b0e64d7e6437e3609e3296e2fc9e2510e1f52e1063dd566dc787db62ad8780d803ed754fd5c94d2916d26dad11a0d059ac9f86c28bfc190ebe310bd366bc1a5b8a54b7e4fb66f9b4735b44f4b4013b3685b304fad659ac927ac888ac760ac5d2aa28fa7455a3077a2b339fa659ed119965f98c749760b
  | _ => 0
def H11_9 : ℕ → ℕ
  | 0 => 0xf7c0de65d2e6402e3018e0ed8b7e077ade66c036513354b9b334da932ce529a0c292581bae70cf8404ca4
  | _ => 0
def H11 : ℕ → ℕ → ℕ | 5 => H11_5 | 6 => H11_6 | 7 => H11_7 | 8 => H11_8 | 9 => H11_9 | _ => fun _ => 0
def P11_5 : ℕ → ℕ
  | 0 => 0x920
  | _ => 0
def P11_6 : ℕ → ℕ
  | 0 => 0x19420265840b94101a544131400a64842996108e484211210a058413130098580239610e65440b92101a4c4239410ca544021510a44800f1610ca50405860004188021100065480994103c5041b13101a5042712106018000060
  | _ => 0
def P11_7 : ℕ → ℕ
  | 0 => 0xda4801406006a504001710405841a96103a5840f82001e58405b1006c58011c520540800a85007150805d42014504009300125401a54102f548071600d41001997101e5041c4320921c00912007e4c82a13104050405d5109450816b500641000496003a5040095005b1882415006ecc00d1610f41c005d4106ed40341400025800984003048027120016d801d92001b5480094004a5842b06000854800920042584048720da5c0241700aa58403d62
  | 1 => 0x1b4c4241600825842915100f148045410145841d1300065801102001a84002172016cc0150300ce0800282000c5c416b6006a5c414d320f05c8001610125c00d17102018803161016d002a0200200800892007250403141000544350500d058000141016c80079510865040097006ec401c9510825440797105ad0005c6200408016b200d81c03893002c4c006c6206c5c02b0700825041a95105acc038920030580101510d05401b14003a5440d151
  | 2 => 0x4c5c02c9200665841ed520085081095103a5c4019300965440d97009c5c034170016d401c32106c54021961
  | _ => 0
def P11_8 : ℕ → ℕ
  | 0 => 0xac8405d6000a5c004d4000914000430006cc0029400100c00843000cdc003160014d8006d4001f1800455101b10002b6000014000c3001b140075420144c00057000150805c6000ad400254000650000d3200acc001b700015c404d42006d80011400031880136000654004c6000c50004c4000150004d3201150006c700191c000562014cc00643000c4c0042300021c0013300030c4031500064c002b70001548035510090c00254201b0c002b40
  | 1 => 0x33600215440317001454000d300011c0035410130c0025710011000296001b54803c6000b0c800d510014c80255000718800d6001f54000530017140074300114c4011600171c00244000a5400197001758400d6100a4c000d4100658000d71006d00053500091c00025001b5080056000cd000753201354001b500044c0051600029c00347200318000551004d0002d5200354000472021180074400111000255100ccc000d7200cd4005c40
  | _ => 0
def P11_9 : ℕ → ℕ
  | 0 => 0x732001d0c00720001d0000753001d8000665001cc000710001d9400653001880007520018c000610001d8c00750
  | _ => 0
def P11 : ℕ → ℕ → ℕ | 5 => P11_5 | 6 => P11_6 | 7 => P11_7 | 8 => P11_8 | 9 => P11_9 | _ => fun _ => 0
def Z11 (s i : ℕ) : Bool := barV3 7 8 (SgenB 10 x11 o11 P11) N11 (idxGenB N11 H11) o11 s i
theorem l11_5 : ∀ i, 0 ≤ i → i < N11 5 → Z11 5 i = true := span_end 1 0 (by decide +kernel) (le_refl _)
theorem l11_6 : ∀ i, 0 ≤ i → i < N11 6 → Z11 6 i = true := span_end 33 0 (by decide +kernel) (le_refl _)
theorem c11_7_0 : span (Z11 7) 128 0 = true := by decide +kernel
theorem c11_7_1 : span (Z11 7) 16 128 = true := by decide +kernel
theorem l11_7 : ∀ i, 0 ≤ i → i < N11 7 → Z11 7 i = true :=
  span_step 128 0 c11_7_0 <| span_end 16 128 c11_7_1 (le_refl _)
theorem l11_8 : ∀ i, 0 ≤ i → i < N11 8 → Z11 8 i = true := span_end 127 0 (by decide +kernel) (le_refl _)
theorem l11_9 : ∀ i, 0 ≤ i → i < N11 9 → Z11 9 i = true := span_end 17 0 (by decide +kernel) (le_refl _)
theorem l11_10 : ∀ i, 0 ≤ i → i < N11 10 → Z11 10 i = true := span_end 1 0 (by decide +kernel) (le_refl _)
theorem base_n7_065 : ∀ s, HasMonoSize 7 (gfn [] edges_n7_065) s → 11 ≤ s :=
  prove_base_mono (M := 7) (E := 8) (cap := 10) r11 x11 (gfn [] edges_n7_065)
    (SgenB 10 x11 o11 P11) N11 (idxGenB N11 H11) o11
    (by decide) ho11 rfl (by decide) rfl (by decide +kernel) rfl (by decide +kernel) (
    all_step l11_10 <| all_step l11_9 <| all_step l11_8 <| all_step l11_7 <| all_step l11_6 <| all_step l11_5 <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_zero lvl_empty)

def edges_n7_066 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,2),(3,4),(4,5),(4,6),(5,6)]
def r12 : List ℕ := [17,18,20,33,42,44,65,74,76,3,5,9,6,24,48,80,96]
def x12 : List ℕ := [3657,4754,5412,10672,57351,81976,98752]
def p12 (pi w : ℕ) : ℕ := match pi with
  | 0 => ((w &&& 0x524) >>> 1) ||| ((w &&& 0x1f849) ||| ((w &&& 0x292) <<< 1))
  | 1 => ((w &&& 0x1c0) >>> 3) ||| (((w &&& 0x8000) >>> 1) ||| ((w &&& 0x13e07) ||| (((w &&& 0x4000) <<< 1) ||| ((w &&& 0x38) <<< 3))))
  | 2 => ((w &&& 0xc000) >>> 5) ||| (((w &&& 0x10040) >>> 4) ||| (((w &&& 0x2088) >>> 2) ||| ((w &&& 0x111) ||| (((w &&& 0x822) <<< 2) ||| (((w &&& 0x1004) <<< 4) ||| ((w &&& 0x600) <<< 5))))))
  | _ => w
theorem vp12 : ∀ pi, ValidPerm 9 8 (p12 pi)
  | 0 => validPerm_of_spec 9 8 (p12 0) [(0x524,2,1),(0x1f849,0,0),(0x292,1,1)] [0,2,1,3,5,4,6,8,7,10,9,11,12,13,14,15,16] (fun _ => rfl) (by decide +kernel)
  | 1 => validPerm_of_spec 9 8 (p12 1) [(0x1c0,2,3),(0x8000,2,1),(0x13e07,0,0),(0x4000,1,1),(0x38,1,3)] [0,1,2,6,7,8,3,4,5,9,10,11,12,13,15,14,16] (fun _ => rfl) (by decide +kernel)
  | 2 => validPerm_of_spec 9 8 (p12 2) [(0xc000,2,5),(0x10040,2,4),(0x2088,2,2),(0x111,0,0),(0x822,1,2),(0x1004,1,4),(0x600,1,5)] [0,3,6,1,4,7,2,5,8,14,15,13,16,11,9,10,12] (fun _ => rfl) (by decide +kernel)
  | _ + 3 => validPerm_id 9 8
def o12 : List ℕ → List ℕ := oriStages p12 [[0],[1],[2]]
theorem ho12 : ∀ k l, (∀ w ∈ l, w < 2 ^ (9 + 8)) → DLive 9 8 k l.toFinset → DLive 9 8 k (o12 l).toFinset := fun _ _ hlt h => oriStages_dlive vp12 hlt h
def N12 : ℕ → ℕ | 5 => 2 | 6 => 29 | 7 => 77 | 8 => 67 | 9 => 10 | 10 => 1 | _ => 0
def H12_5 : ℕ → ℕ
  | 0 => 0x2931f01b72
  | _ => 0
def H12_6 : ℕ → ℕ
  | 0 => 0xfeffdfb6c1f4061f3c47e9eeadb0e7d64c9d2889cc995cb5b3c86fbbafc4b4123b3709a19f49dbdf987fa7af22717b064dfa614a343c0c419732b42f28afd22f7217f3413cfa06b84
  | _ => 0
def H12_7 : ℕ → ℕ
  | 0 => 0xcc79fcbe11cbd94c4517c0193bfcb9bf944bc644b590bb5270b1c5ca8f41a8b48a69769e43a9d6ec98b7f987fa94d6892acf9235f91a68916798dea17c58b79b03771a66d8056ad90659ef6577c64e566172a5bb1c56de353e8a4ec414d9724af92474b6424513feab3c6973b1cc382fd3463e32a61304202e3202b4682ad3121beb1ec56191291783816e90144861127e052820421b02f7802d8d011e50094c
  | 1 => 0xfd3d4fc76bfb3f5f8b39f7c07f0594eed3becaa2e9956e76bde321dd451ad1179
  | _ => 0
def H12_8 : ℕ → ℕ
  | 0 => 0xf4de9f059cefc53e9956e98b3e76bde640ce25e0dc95bd1179ceb43c1126bfcb9bf9a1baf12b2908b1064ad7caa67c49fb0c9e43a9a8169808497d979759691d05916798b2377fd797f4de7d58c7934677f79771a675b2573fe871bc36d8056a285699c667fec6734866f8564616624f55654f55f4251aa84ec414af9243b92416f340d684064b3cf473b39c34a97331dd32a6131d902d1152ad3121beb13218
  | 1 => 0xfb5f0fb564f7ad2
  | _ => 0
def H12_9 : ℕ → ℕ
  | 0 => 0xf8d7bed0237ff5467695658515f0da4c6c340b723bc8d0da0e
  | _ => 0
def H12 : ℕ → ℕ → ℕ | 5 => H12_5 | 6 => H12_6 | 7 => H12_7 | 8 => H12_8 | 9 => H12_9 | _ => fun _ => 0
def P12_5 : ℕ → ℕ
  | 0 => 0x44800d120
  | _ => 0
def P12_6 : ℕ → ℕ
  | 0 => 0x151320304c4174100724c409131042540250310504c00e12101248402131076584029320385440a9210004c818110038504021320904c800941014508041420005480095100e0841c0300005880c110
  | _ => 0
def P12_7 : ℕ → ℕ
  | 0 => 0x585040484005a08013171002d4002020002c4000d3203a58419c3200a8800d32100c58020132042480120300721801e1210325440b9510005440a9520104c000a210205841b96001a480120200465400315004b1080817100e5040e94100b548073300240801b9400684801b83206050400141046500161710465801e9420280801314107a4840a9300164c01e92000e5840c932002c800b93204e1000e13202e5040a9420721c01b950002d0008132
  | 1 => 0x1610401000d942002cc01e9300184c40814102054406020014080119210140c417020
  | _ => 0
def P12_8 : ℕ → ℕ
  | 0 => 0x358400c500050c8019300010c0019400035800133000d0c0019600091000445200450002c400130c00433000114002d7100958801360004540025310034c800d71009500043600104c0035310090c000c300031800053001294001950010d4001d21004c8401130006cc002560006d0002450007504005510035c000d5200e8c001b60010580048500031c003d3100b0c0025420034c003c40004d00024520105400053200b5000116000e0c001350
  | 1 => 0x56000648401b50
  | _ => 0
def P12_9 : ℕ → ℕ
  | 0 => 0x1d0000630001c4000721001d440073100188400610001d4000730
  | _ => 0
def P12 : ℕ → ℕ → ℕ | 5 => P12_5 | 6 => P12_6 | 7 => P12_7 | 8 => P12_8 | 9 => P12_9 | _ => fun _ => 0
def Z12 (s i : ℕ) : Bool := barV3 9 8 (SgenB 10 x12 o12 P12) N12 (idxGenB N12 H12) o12 s i
theorem l12_5 : ∀ i, 0 ≤ i → i < N12 5 → Z12 5 i = true := span_end 2 0 (by decide +kernel) (le_refl _)
theorem l12_6 : ∀ i, 0 ≤ i → i < N12 6 → Z12 6 i = true := span_end 29 0 (by decide +kernel) (le_refl _)
theorem l12_7 : ∀ i, 0 ≤ i → i < N12 7 → Z12 7 i = true := span_end 77 0 (by decide +kernel) (le_refl _)
theorem l12_8 : ∀ i, 0 ≤ i → i < N12 8 → Z12 8 i = true := span_end 67 0 (by decide +kernel) (le_refl _)
theorem l12_9 : ∀ i, 0 ≤ i → i < N12 9 → Z12 9 i = true := span_end 10 0 (by decide +kernel) (le_refl _)
theorem l12_10 : ∀ i, 0 ≤ i → i < N12 10 → Z12 10 i = true := span_end 1 0 (by decide +kernel) (le_refl _)
theorem base_n7_066 : ∀ s, HasMonoSize 7 (gfn [] edges_n7_066) s → 11 ≤ s :=
  prove_base_mono (M := 9) (E := 8) (cap := 10) r12 x12 (gfn [] edges_n7_066)
    (SgenB 10 x12 o12 P12) N12 (idxGenB N12 H12) o12
    (by decide) ho12 rfl (by decide) rfl (by decide +kernel) rfl (by decide +kernel) (
    all_step l12_10 <| all_step l12_9 <| all_step l12_8 <| all_step l12_7 <| all_step l12_6 <| all_step l12_5 <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_zero lvl_empty)

def edges_n7_067 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,4),(2,5),(3,6),(4,5),(4,6)]
def r13 : List ℕ := [14,17,28,42,70,97,98,3,5,9,18,36,72,48,80]
def x13 : List ℕ := [930,1241,2325,4621,25606,10344,20592]
def p13 (pi w : ℕ) : ℕ := match pi with
  | 0 => ((w &&& 0x5210) >>> 1) ||| ((w &&& 0x4e7) ||| ((w &&& 0x2908) <<< 1))
  | 1 => ((w &&& 0x40) >>> 6) ||| (((w &&& 0x6000) >>> 5) ||| (((w &&& 0x420) >>> 3) ||| (((w &&& 0x10) >>> 1) ||| ((w &&& 0x1802) ||| (((w &&& 0x8) <<< 1) ||| (((w &&& 0x84) <<< 3) ||| (((w &&& 0x300) <<< 5) ||| ((w &&& 0x1) <<< 6))))))))
  | 2 => ((w &&& 0x4040) >>> 6) ||| (((w &&& 0x2000) >>> 4) ||| (((w &&& 0x420) >>> 3) ||| (((w &&& 0x1000) >>> 1) ||| ((w &&& 0x1a) ||| (((w &&& 0x800) <<< 1) ||| (((w &&& 0x84) <<< 3) ||| (((w &&& 0x200) <<< 4) ||| ((w &&& 0x101) <<< 6))))))))
  | _ => w
theorem vp13 : ∀ pi, ValidPerm 7 8 (p13 pi)
  | 0 => validPerm_of_spec 7 8 (p13 0) [(0x5210,2,1),(0x4e7,0,0),(0x2908,1,1)] [0,1,2,4,3,5,6,7,9,8,10,12,11,14,13] (fun _ => rfl) (by decide +kernel)
  | 1 => validPerm_of_spec 7 8 (p13 1) [(0x40,2,6),(0x6000,2,5),(0x420,2,3),(0x10,2,1),(0x1802,0,0),(0x8,1,1),(0x84,1,3),(0x300,1,5),(0x1,1,6)] [6,1,5,4,3,2,0,10,13,14,7,11,12,8,9] (fun _ => rfl) (by decide +kernel)
  | 2 => validPerm_of_spec 7 8 (p13 2) [(0x4040,2,6),(0x2000,2,4),(0x420,2,3),(0x1000,2,1),(0x1a,0,0),(0x800,1,1),(0x84,1,3),(0x200,1,4),(0x101,1,6)] [6,1,5,3,4,2,0,10,14,13,7,12,11,9,8] (fun _ => rfl) (by decide +kernel)
  | _ + 3 => validPerm_id 7 8
def o13 : List ℕ → List ℕ := oriStages p13 [[0,1,2]]
theorem ho13 : ∀ k l, (∀ w ∈ l, w < 2 ^ (7 + 8)) → DLive 7 8 k l.toFinset → DLive 7 8 k (o13 l).toFinset := fun _ _ hlt h => oriStages_dlive vp13 hlt h
def N13 : ℕ → ℕ | 6 => 19 | 7 => 79 | 8 => 73 | 9 => 11 | 10 => 1 | _ => 0
def H13_6 : ℕ → ℕ
  | 0 => 0xfd303eeec3d4abec82b9a646d8b5bd7ba577b1cb77b9076e9c70f026cf7b6ba2e640af4ecc04ec76179f203a3003231
  | _ => 0
def H13_7 : ℕ → ℕ
  | 0 => 0xd9759d5b55d5627c8eeac6225c3eb0bf6b1be91ebdc92b9033b85fcb786cb5712af0b3adb36ad17dad142a45249ddf7912bb8964284e6083cd0835d0824407c0dd76e9475523743a07321e6e4276e0836c1db6bf8167a7163e6d625a75fc895b2bd5a9c7592c05788054e6053bc9533095106c4f0fa4e6524e4714d2a74ce704b98d4a3e049c1c38ad3326a22d0b12b294282492229d1b13b12aff0731e0092b
  | 1 => 0xfd87dfcb2ef966ef86adf6692f59e6f380bf1dd0e7fd4e7217e53d3e3fa8e3dc5dcac1d9836
  | _ => 0
def H13_8 : ℕ → ℕ
  | 0 => 0xeb50ee9aaae6db7de4f1de23ad9759d63c1d5b55d410ed1506c8500c31a2b7c4bb786cb4284b195cb17a8af7f5af337ad20eaae80aa4d3a6de4a6af1a50e5993159562f92bb284e608244080ce27f18c7c54c7c0e877ed9743a07392e6e87b6e4276dded60b635fc895f4fa5b2bd592d757fc456928533f14f3034c3814ac2f42f9e3ed483ebb8370852a92a282492081c1f2841b13b19e7c0ba7f0a6cc0a6c3
  | 1 => 0xfd87df966ef6de4f1197f06e2efdc8ef0d5ecc8fec4ca
  | _ => 0
def H13_9 : ℕ → ℕ
  | 0 => 0xeb33ae7d21dfad5dab64b5e28a4f5f84a227e760739680253b010a2
  | _ => 0
def H13 : ℕ → ℕ → ℕ | 6 => H13_6 | 7 => H13_7 | 8 => H13_8 | 9 => H13_9 | _ => fun _ => 0
def P13_6 : ℕ → ℕ
  | 0 => 0xbd4101450420952040544051610304c40e13103e58405131014544039600585480392000e5000f92103c5840f95103850420942
  | _ => 0
def P13_7 : ℕ → ℕ
  | 0 => 0x420800302003a5040f96104a50409161008c40148500125481f840016180049200245041936001e5801b96203e5040d9400475880496005e580080200000801f1410484c0050310515842316100a5400e97105008004942008cc019340064c801931001c1800413000a4c00d93101e5002014107c5440d0400245c41b9520245440f97105a5881b97202d5080f9510785441935001e5401f17106514817940026480179500184800a56208810016942
  | 1 => 0x159300475480792000f5481516107e180179700654c80f16103658015141064cc00e9510185800f141
  | _ => 0
def P13_8 : ℕ → ℕ
  | 0 => 0x9540053600090c000b300131000096000714402930003548005320091800356100550004040007584047650070c00254200b54404430011140053500095c0045610015440345000ad0001c500144c00516000558404a3000ad4000b70002d0002940007188005600025400424000d544009300071800295000114000b6000910001d3200f0c003d510095000545200f54003f53003188004300145400256100f1800483000dd8c015500075c001d71
  | 1 => 0x97000250002b3000754801d400050c004460002d4005330
  | _ => 0
def P13_9 : ℕ → ℕ
  | 0 => 0x610001d0000750001cc80076200194800720001c840075200188000710
  | _ => 0
def P13 : ℕ → ℕ → ℕ | 6 => P13_6 | 7 => P13_7 | 8 => P13_8 | 9 => P13_9 | _ => fun _ => 0
def Z13 (s i : ℕ) : Bool := barV3 7 8 (SgenB 10 x13 o13 P13) N13 (idxGenB N13 H13) o13 s i
theorem l13_6 : ∀ i, 0 ≤ i → i < N13 6 → Z13 6 i = true := span_end 19 0 (by decide +kernel) (le_refl _)
theorem l13_7 : ∀ i, 0 ≤ i → i < N13 7 → Z13 7 i = true := span_end 79 0 (by decide +kernel) (le_refl _)
theorem l13_8 : ∀ i, 0 ≤ i → i < N13 8 → Z13 8 i = true := span_end 73 0 (by decide +kernel) (le_refl _)
theorem l13_9 : ∀ i, 0 ≤ i → i < N13 9 → Z13 9 i = true := span_end 11 0 (by decide +kernel) (le_refl _)
theorem l13_10 : ∀ i, 0 ≤ i → i < N13 10 → Z13 10 i = true := span_end 1 0 (by decide +kernel) (le_refl _)
theorem base_n7_067 : ∀ s, HasMonoSize 7 (gfn [] edges_n7_067) s → 11 ≤ s :=
  prove_base_mono (M := 7) (E := 8) (cap := 10) r13 x13 (gfn [] edges_n7_067)
    (SgenB 10 x13 o13 P13) N13 (idxGenB N13 H13) o13
    (by decide) ho13 rfl (by decide) rfl (by decide +kernel) rfl (by decide +kernel) (
    all_step l13_10 <| all_step l13_9 <| all_step l13_8 <| all_step l13_7 <| all_step l13_6 <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_zero lvl_empty)

def edges_n7_068 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(3,4),(5,6)]
def r14 : List ℕ := [1,42,44,50,52,74,76,82,84,3,5,9,17,33,65,6,24,96]
def x14 : List ℕ := [32257,33450,34132,67686,70040,139294,147936]
def p14 (pi w : ℕ) : ℕ := match pi with
  | 0 => ((w &&& 0x554) >>> 1) ||| ((w &&& 0x3f801) ||| ((w &&& 0x2aa) <<< 1))
  | 1 => ((w &&& 0x198) >>> 2) ||| (((w &&& 0x1000) >>> 1) ||| ((w &&& 0x3e601) ||| (((w &&& 0x800) <<< 1) ||| ((w &&& 0x66) <<< 2))))
  | 2 => ((w &&& 0x1e0) >>> 4) ||| (((w &&& 0x4000) >>> 1) ||| ((w &&& 0x39e01) ||| (((w &&& 0x2000) <<< 1) ||| ((w &&& 0x1e) <<< 4))))
  | 3 => ((w &&& 0x6060) >>> 2) ||| (((w &&& 0x20000) >>> 1) ||| ((w &&& 0x8787) ||| (((w &&& 0x10000) <<< 1) ||| ((w &&& 0x1818) <<< 2))))
  | 4 => ((w &&& 0x1800) >>> 2) ||| (((w &&& 0x10088) >>> 1) ||| ((w &&& 0x26133) ||| (((w &&& 0x8044) <<< 1) ||| ((w &&& 0x600) <<< 2))))
  | 5 => ((w &&& 0x6000) >>> 4) ||| (((w &&& 0x20) >>> 3) ||| (((w &&& 0x20040) >>> 2) ||| (((w &&& 0x80) >>> 1) ||| ((w &&& 0x103) ||| (((w &&& 0x18004) <<< 1) ||| (((w &&& 0x1e08) <<< 2) ||| ((w &&& 0x10) <<< 3)))))))
  | 6 => ((w &&& 0x80) >>> 3) ||| (((w &&& 0x7820) >>> 2) ||| (((w &&& 0x30008) >>> 1) ||| ((w &&& 0x103) ||| (((w &&& 0x40) <<< 1) ||| (((w &&& 0x8010) <<< 2) ||| (((w &&& 0x4) <<< 3) ||| ((w &&& 0x600) <<< 4)))))))
  | 7 => ((w &&& 0x6000) >>> 4) ||| (((w &&& 0xa0) >>> 3) ||| (((w &&& 0x20000) >>> 2) ||| ((w &&& 0x1194b) ||| (((w &&& 0x8000) <<< 2) ||| (((w &&& 0x14) <<< 3) ||| ((w &&& 0x600) <<< 4))))))
  | _ => w
theorem vp14 : ∀ pi, ValidPerm 9 9 (p14 pi)
  | 0 => validPerm_of_spec 9 9 (p14 0) [(0x554,2,1),(0x3f801,0,0),(0x2aa,1,1)] [0,2,1,4,3,6,5,8,7,10,9,11,12,13,14,15,16,17] (fun _ => rfl) (by decide +kernel)
  | 1 => validPerm_of_spec 9 9 (p14 1) [(0x198,2,2),(0x1000,2,1),(0x3e601,0,0),(0x800,1,1),(0x66,1,2)] [0,3,4,1,2,7,8,5,6,9,10,12,11,13,14,15,16,17] (fun _ => rfl) (by decide +kernel)
  | 2 => validPerm_of_spec 9 9 (p14 2) [(0x1e0,2,4),(0x4000,2,1),(0x39e01,0,0),(0x2000,1,1),(0x1e,1,4)] [0,5,6,7,8,1,2,3,4,9,10,11,12,14,13,15,16,17] (fun _ => rfl) (by decide +kernel)
  | 3 => validPerm_of_spec 9 9 (p14 3) [(0x6060,2,2),(0x20000,2,1),(0x8787,0,0),(0x10000,1,1),(0x1818,1,2)] [0,1,2,5,6,3,4,7,8,9,10,13,14,11,12,15,17,16] (fun _ => rfl) (by decide +kernel)
  | 4 => validPerm_of_spec 9 9 (p14 4) [(0x1800,2,2),(0x10088,2,1),(0x26133,0,0),(0x8044,1,1),(0x600,1,2)] [0,1,3,2,4,5,7,6,8,11,12,9,10,13,14,16,15,17] (fun _ => rfl) (by decide +kernel)
  | 5 => validPerm_of_spec 9 9 (p14 5) [(0x6000,2,4),(0x20,2,3),(0x20040,2,2),(0x80,2,1),(0x103,0,0),(0x18004,1,1),(0x1e08,1,2),(0x10,1,3)] [0,1,5,2,6,3,7,4,8,13,14,9,10,11,12,17,15,16] (fun _ => rfl) (by decide +kernel)
  | 6 => validPerm_of_spec 9 9 (p14 6) [(0x80,2,3),(0x7820,2,2),(0x30008,2,1),(0x103,0,0),(0x40,1,1),(0x8010,1,2),(0x4,1,3),(0x600,1,4)] [0,1,3,5,7,2,4,6,8,11,12,13,14,9,10,16,17,15] (fun _ => rfl) (by decide +kernel)
  | 7 => validPerm_of_spec 9 9 (p14 7) [(0x6000,2,4),(0xa0,2,3),(0x20000,2,2),(0x1194b,0,0),(0x8000,1,2),(0x14,1,3),(0x600,1,4)] [0,1,5,3,7,2,6,4,8,13,14,11,12,9,10,17,16,15] (fun _ => rfl) (by decide +kernel)
  | _ + 8 => validPerm_id 9 9
def o14 : List ℕ → List ℕ := oriStages p14 [[0],[1],[2],[3,4,5,6,7]]
theorem ho14 : ∀ k l, (∀ w ∈ l, w < 2 ^ (9 + 9)) → DLive 9 9 k l.toFinset → DLive 9 9 k (o14 l).toFinset := fun _ _ hlt h => oriStages_dlive vp14 hlt h
def N14 : ℕ → ℕ | 4 => 1 | 5 => 28 | 6 => 145 | 7 => 295 | 8 => 245 | 9 => 67 | 10 => 5 | 11 => 1 | _ => 0
def H14_4 : ℕ → ℕ
  | 0 => 0xaa62a
  | _ => 0
def H14_5 : ℕ → ℕ
  | 0 => 0xfb43df30e0eb582c0f3dbfce6b091eb066ba347fa2d4396d1e882948322d81a997c77d73c0d6c9716a8195a00d59ae258c5945c3f3619832c8c2425b2266d220351d8720b766
  | _ => 0
def H14_6 : ℕ → ℕ
  | 0 => 0x6e9976e8206e4aa6db746a7036754765ab8620696035e5ab8159082532b1531335115850512483e8465504620945d474555a4374b4029738df3384e536b18365623518b3312c326e5321932d9f22d93228f9127b4d2751525f4325e3d250aa249862334320e4d1f1421d3db1cd451cd211b3e11b2921ab8f1a9e618f6f1878b17ad115f8b13e39115e2113110e4e30d19607e0906fb6066b304d8002ac3029fe
  | 1 => 0xe5b20e4e60e4a49e3e9be2a8bdffeadfeabddfbcdd3b1dd28bdc12bd7e27d6ddbd43d6d03d3d0375cf97eccd27cbb0cc5a30c4f14c42cbc3d8dc0f3dc0dacc09cdbcd94bb21dba557b8138b7f7db7a93b68e1b644ab26ecb1560af6bbaeddeac5b4ab357aaf38aa8f5a9218a13ad9d8429d008963df8f6a48d2238c5038a0a08820f81b8b7e8b67c9b97c5ed7b9467ad2279759793db7536d720cd71c416fc63
  | 2 => 0xfe411fe1e7f8a7cf729ff6452f5d51f3b56f353ef271bef620ef58eee5caed9d0e9c48e87a8e8068e6267
  | _ => 0
def H14_7 : ℕ → ℕ
  | 0 => 0x3cb7e3b05b39f5d395f7384193448133d0b3300e32e213219330bb230746303a82f54f2f23f2e0222dd6e2d8a42a6dc2a31d29a482881128678262fc249a22293d2264c21e12208c5200d71f9bd1f0691e7901cdd91aab3189ca159371484e126ef11de611bdb0eb840e58b0dd510d89e0d5340a0e009727087ae07e0907b060739205ee6056bd056ac051d505004044c4026bc01cc501cc00168e012e100750
  | 1 => 0x709af6e8206a70369c6a69944698c168d5b68c1b68ba068af5681a36803967fb167235667c16581d64f6064df462d306209560f355ff395f4c85ba7658db156b8b561a255833553a2552705517f54f6d54ebd527485132c5100b50646501e7500824fcf34fbbf4ef1d4e5cd4de7b4d84c4b29c4aa6249c4c48d9b48b97478bb4650a45e3f4530b426ef423bd41dc441602413ca3f6ce3eaf33e5ea3d85c3d6ff
  | 2 => 0xa1bbc9ed319e55f9d8429d0089cfe89c1d59c0249be6e9b0b39ad929ad4297d9797ccd95df994092936ae928229263b91c1f91a599191690f7790cf48ebdf8dc758c5038be2f8b1898ace58ab8c8a42688ee987c24879fe84ff9820708201c8143a8069e804e2804397ff4d7f8227ead57db037c9367bd427ad227a88f7a28979ec3789607796d773c076fcf76b2e75c667572a74e3773efe73d3d727da71c60
  | 3 => 0xd45f9d43d6d2d8dd2859d205ed19bdd1636d05aad03d3cf34ccde52cb357ca778c97cbc8ce9c89f5c86f5c8552c5a30c545dc51bbc4cf6c4336c42cbc2e18c0b31c08babf83fbe99ebe297bd2ecbcb13bc075bb369bb33dba63aba2e9b80efb743bb7246b6916b6362b5727b5527b4a8ab4921b3f33b3143b2c91b27f9af936af350adbcfadb77abf56ab71fa9824a8b67a814aa74e5a4c9fa447fa3914a2251
  | 4 => 0xffb29fe411fd842fbe7ef8ca0f5d51f51def40b9f3660f2f2ef1b0ff1661f0e03f0aaaedfcded925ecc85eb24beb0c3ea5d6e9963e87a8e8068e7c8ee7297e50fee4640e4575e41f6e2f80e2b27dfbeadded5dd27fdac2cd992ad7602d6c78d6219
  | _ => 0
def H14_8 : ℕ → ℕ
  | 0 => 0x409093eaba3d83f3d66c3aaf23972b38d3d35cbc3415a329d9318f12fb6e2d19a2cc992bfec2ba4a2aad4296ff292b32824327d2225275249a2241c1235562164c200c71ead41e8641e3121d86e1d0341b6d61abe91972f18fd2189ca182a1178aa1744516c761686315afe15711156de1505a14b881498f13d97124130ffa60fe810dcf30d5340acc90a84a09c570972706e1b0586f056bd02d9b021fc0168e
  | 1 => 0x7ead57e1717a8c87a52f782c677d387796d775327646975aa47525773d3d72620700556fb516f3e06d6796ca986c0a16ad316a33a69fe269f2268d7f67a6666410642506419c6364c6343162d30614055f64d5f19e5deb45cdd85c33158f2f57d5e56ac55562a548675376b52f84510a74fc7b4f0164e5cd4cff84c86e4be614b9654b29c4aa62478bb469de4593b4412a43cbf43bd4430a142bae423bd413ca
  | 2 => 0xc4647c33a8c2c4bc1985c1304c0c9fbf33fbdcfcbd709bcb13bb1b9ba6c5b9bd6b80efb7d94b7c28b7246b7198b5ec1b4921b4760b2ac4b26abb1827b0944af337acaa1ab151a9824a77c7a75dfa6fb0a5617a559ea490ca2f09a1586a02bba00979fbea9e5489d0089c2239a5869977d982e396bed948a19263b8f6698e5128ab8c8a97f8a4b38853487ab1854cd84ff98201c81e8f7fd127facf7f8227eb4e
  | 3 => 0xffb29ff369fd842fca17fbdd6facb0fa5f6fa228f9ddbf98b9f4946f45fdf1141f0707f05dbf01a9ee910ee74bed42aecc85eb5c8eb414e951ce9484e830ee673ce560fe50fee2f80e1a6dde073dc5cbda731d815ed6219d5bb0d3871d2c82d1636cfe87cfe14cf34ccf112cd0b5cc004cb587cac60ca112c9c63c97cbc9538c9217c53b2
  | _ => 0
def H14_9 : ℕ → ℕ
  | 0 => 0xfb53dfa5f6f9ddbf8e2ff1feaf01e6edef5e869ae830ee0919cf34cccb4cc97e5bff08bc336b90e0b7503b7198b4921ae506ac79fa5617a2f098f6518d8ea8a61f89ebb8769f870d57faba75cd9726206ede56e3266c5bf69fe267a89671be609945a9ba59d0f58c53564405051f4858b47487423bd40ded3ae5a3742b3502b2d02a2b2c3249a22264e21e121c81719b2f19b2d174450682c061c304300021fc
  | 1 => 0xfdeb5fd842fca17
  | _ => 0
def H14_10 : ℕ → ℕ
  | 0 => 0xe4f31664104755b3972b379c4
  | _ => 0
def H14 : ℕ → ℕ → ℕ | 4 => H14_4 | 5 => H14_5 | 6 => H14_6 | 7 => H14_7 | 8 => H14_8 | 9 => H14_9 | 10 => H14_10 | _ => fun _ => 0
def P14_4 : ℕ → ℕ
  | 0 => 0x921
  | _ => 0
def P14_5 : ℕ → ℕ
  | 0 => 0x944c80413001c4c402920066500169310ba4c8019420164c02d1310064c8119300845043f9400fe4c0199300504c42113103c4842a1410904c8009320345080d1320605002e9420164841c130
  | _ => 0
def P14_6 : ℕ → ℕ
  | 0 => 0x544c0269301725083f541134484339511e250815131062440589501885403c9321ef080409531885003ec30110500341321724805c9311ae544471400ce5046504101e0402a14305c440771530004800e13009450c5e5420f04840013109c54c209430924806693206e4c462932080500330431464c41e13202a54455150178c8418941062544169300c05084615005c4c83c15114e4c010943002504159400164804d94305454c3994103a4c030152
  | 1 => 0x11f0403e143070108001400185083713101e4c0118300f854c009310984c81f141246544229300684c4078410b04c45a9200d6504010201724843f83009c50c071200424c87d9311745842d9420284c4061522465045c95209e1083d9200164c0259200ee4c076b2022150c0a9411d0c80179320304c82813204a4c4121301625002313004a5040913203a5083904300e4c81794110650815143000508569210e84c0541210fd4840732000254446140
  | 2 => 0x91210184801f121086108151210144c440042180108131420100845d12102a4c4409430545040e1400a450413132
  | _ => 0
def P14_7 : ℕ → ℕ
  | 0 => 0x1050451b300984c430d300010401e8210b2544329601604c40d930032184279400b6500219300ac10c220411344c40285404c0c857d42062144203301801402114300e0c01c930092c80140210f2c84231410dc4c04c9430c65402795003414009031150544071100ce5001713219414403940096c842531006a5044c82003e0c40392004a50c4b21001c5041a8421868800083205c4c4361500e04c4168520a21843693207e58c13120014cc422843
  | 1 => 0x1044c82493010a4c8059411a554c1d83009858401b3100d10c088500ac5803a442094cc04495101050c4d1600b2584391500280c4261410c2cc8240400ba0403c031096d04411531654c47595305e0c8121630ba1445293000a4c42b15008c544071610445080601007e5cc219600380c8119310e6500679511604c814b30122480052200ca5400b1401e51082b93200c88062951038108009200fec842c1430528847114006a5442914118a5840b831
  | 2 => 0x16e5441b9530fc54c2592106808451b50006cc025b3112e4c01a53014e084203321525802c03112d8c8029210985440717103050024d2102c54c24c31000c800a9400f30c857b300144c4159511285002823003058024d5101654c5414114a5884a12009750c0c15001658c05321062140711600564c4399500200c00883213a1001213211e4c840c43036cc06942011a10800940142540694411b110c4496112654c3fd501545401682002c50446950
  | 3 => 0xae5082013201a54c24b500154c82d14309c4805f15112d4841d13004c50038141096d4414b10096cc0033210a8504391600000400f0511ae58c3414104a0c05b0311a850c1714104850c24b4000ccc4219310dc5080883002a4c06794301e0841095110458c119420954c82e030092cc0159711c45402a13108c5841d1400444c41f95301210c62943006c800e94106c4c8129320ba4c00a9500534c825d5306c50047a201ae5cc470510164c41a961
  | 4 => 0x9821014484331300ca108441500064c40b1630f050806940010508121530165004d1500984c85a032094884279310ae50451b100e054c0d0400365002594104a140369311de0844d1210b04c8391300e6580381630ec0842404105e108391531b4540529210a458434020
  | _ => 0
def P14_8 : ℕ → ℕ
  | 0 => 0x485c010830083d000573206bcc006c20008c8008f210094c80462100ed080913103914018970083d4c06d31066540161320075881d560054d801413207648006d210121441784005bcc01214001b5441bb4207ad001b2300069000313202acc0199600680c4057310045cc1ae210364c00256202390c0584104454018142006cc408f10023d0c0c173011d4c011630095481d92103a4c01415300a0c01514003a58020f500000c8141730704c003932
  | 1 => 0x14c8012150015d4c1316001b5000ad410005000d95100ecc801d4306bd40151600838840244206bd500f14003a500030600305c00574302c5c00813006bd0001d410158841d420006884059420238c4011320764c006d5007e5400093000c550031300248c003a30040d840313107748414c400070800032007acc00c16300c5cc10141032108058400075081db40014cc01b0300830c808f500585401615303a4c4159500118c81bb3000048003830
  | 2 => 0x705001034101854c0ad4200454c16f5302c4c009950054d00039420304c0199400360c01ad410755400c14007c10008e2102c5000902001acc00284001190c15320011d0c21130055108003210061001f46000714c118400484c01d330083cc00c9300845cc0f13000f4c4179420010c8041200701080304000418008f3202b0c4121630085041f2400361040216104110c16140000d000e4710075481d9400085441d54004c5001c15004054400840
  | 3 => 0x213203a5c00182005b8840f1410445000793005058c0572100c58c1c850040d440b9530721440c1320665c01984200210406c410114c4141420604840f160023cc01803001c0c00e440010c801016103c5c0211310281400234100754016d310304c419930008d840a9300020c00d15301a4c01c86004c4c006d5201b5801db30008d441f970014c4018960023d4c0e540
  | _ => 0
def P14_9 : ℕ → ℕ
  | 0 => 0x58c0015300088c0017400030c402440009d0001e31003504005310025000155100590c017600058c401640009cc401b300024c000e310018c40143000150000f41001d0401663001d5001e41009d0400621005d8c01b40001d9000e5400195001560005d5001f31005d4400e43007c8400643001084017300018c0025310064c001761005cc40074300510000f31001cc40203000990000021006c8400f43005d0c00b400054c401f41005d9000430
  | 1 => 0xf6400650000b30
  | _ => 0
def P14_10 : ℕ → ℕ
  | 0 => 0x7100018400073100188400721
  | _ => 0
def P14 : ℕ → ℕ → ℕ | 4 => P14_4 | 5 => P14_5 | 6 => P14_6 | 7 => P14_7 | 8 => P14_8 | 9 => P14_9 | 10 => P14_10 | _ => fun _ => 0
def Z14 (s i : ℕ) : Bool := barV3 9 9 (SgenB 11 x14 o14 P14) N14 (idxGenB N14 H14) o14 s i
theorem l14_4 : ∀ i, 0 ≤ i → i < N14 4 → Z14 4 i = true := span_end 1 0 (by decide +kernel) (le_refl _)
theorem l14_5 : ∀ i, 0 ≤ i → i < N14 5 → Z14 5 i = true := span_end 28 0 (by decide +kernel) (le_refl _)
theorem c14_6_0 : span (Z14 6) 128 0 = true := by decide +kernel
theorem c14_6_1 : span (Z14 6) 17 128 = true := by decide +kernel
theorem l14_6 : ∀ i, 0 ≤ i → i < N14 6 → Z14 6 i = true :=
  span_step 128 0 c14_6_0 <| span_end 17 128 c14_6_1 (le_refl _)
theorem c14_7_0 : span (Z14 7) 128 0 = true := by decide +kernel
theorem c14_7_1 : span (Z14 7) 128 128 = true := by decide +kernel
theorem c14_7_2 : span (Z14 7) 39 256 = true := by decide +kernel
theorem l14_7 : ∀ i, 0 ≤ i → i < N14 7 → Z14 7 i = true :=
  span_step 128 0 c14_7_0 <| span_step 128 128 c14_7_1 <| span_end 39 256 c14_7_2 (le_refl _)
theorem c14_8_0 : span (Z14 8) 96 0 = true := by decide +kernel
theorem c14_8_1 : span (Z14 8) 96 96 = true := by decide +kernel
theorem c14_8_2 : span (Z14 8) 53 192 = true := by decide +kernel
theorem l14_8 : ∀ i, 0 ≤ i → i < N14 8 → Z14 8 i = true :=
  span_step 96 0 c14_8_0 <| span_step 96 96 c14_8_1 <| span_end 53 192 c14_8_2 (le_refl _)
theorem l14_9 : ∀ i, 0 ≤ i → i < N14 9 → Z14 9 i = true := span_end 67 0 (by decide +kernel) (le_refl _)
theorem l14_10 : ∀ i, 0 ≤ i → i < N14 10 → Z14 10 i = true := span_end 5 0 (by decide +kernel) (le_refl _)
theorem l14_11 : ∀ i, 0 ≤ i → i < N14 11 → Z14 11 i = true := span_end 1 0 (by decide +kernel) (le_refl _)
theorem base_n7_068 : ∀ s, HasMonoSize 7 (gfn [] edges_n7_068) s → 12 ≤ s :=
  prove_base_mono (M := 9) (E := 9) (cap := 11) r14 x14 (gfn [] edges_n7_068)
    (SgenB 11 x14 o14 P14) N14 (idxGenB N14 H14) o14
    (by decide) ho14 rfl (by decide) rfl (by decide +kernel) rfl (by decide +kernel) (
    all_step l14_11 <| all_step l14_10 <| all_step l14_9 <| all_step l14_8 <| all_step l14_7 <| all_step l14_6 <| all_step l14_5 <| all_step l14_4 <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_zero lvl_empty)

def edges_n7_069 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(1,6),(3,4),(5,6)]
def r15 : List ℕ := [10,18,33,44,52,65,76,84,3,5,9,17,6,34,66,24,96]
def x15 : List ℕ := [3876,28931,4824,33865,34962,73756,82144]
def p15 (pi w : ℕ) : ℕ := match pi with
  | 0 => ((w &&& 0x892) >>> 1) ||| ((w &&& 0x1f324) ||| ((w &&& 0x449) <<< 1))
  | 1 => ((w &&& 0xe0) >>> 3) ||| (((w &&& 0x4000) >>> 1) ||| ((w &&& 0x19f03) ||| (((w &&& 0x2000) <<< 1) ||| ((w &&& 0x1c) <<< 3))))
  | 2 => ((w &&& 0x20) >>> 4) ||| (((w &&& 0x7000) >>> 3) ||| (((w &&& 0x44) >>> 2) ||| (((w &&& 0x10000) >>> 1) ||| ((w &&& 0x188) ||| (((w &&& 0x8000) <<< 1) ||| (((w &&& 0x11) <<< 2) ||| (((w &&& 0xe00) <<< 3) ||| ((w &&& 0x2) <<< 4))))))))
  | _ => w
theorem vp15 : ∀ pi, ValidPerm 8 9 (p15 pi)
  | 0 => validPerm_of_spec 8 9 (p15 0) [(0x892,2,1),(0x1f324,0,0),(0x449,1,1)] [1,0,2,4,3,5,7,6,8,9,11,10,12,13,14,15,16] (fun _ => rfl) (by decide +kernel)
  | 1 => validPerm_of_spec 8 9 (p15 1) [(0xe0,2,3),(0x4000,2,1),(0x19f03,0,0),(0x2000,1,1),(0x1c,1,3)] [0,1,5,6,7,2,3,4,8,9,10,11,12,14,13,15,16] (fun _ => rfl) (by decide +kernel)
  | 2 => validPerm_of_spec 8 9 (p15 2) [(0x20,2,4),(0x7000,2,3),(0x44,2,2),(0x10000,2,1),(0x188,0,0),(0x8000,1,1),(0x11,1,2),(0xe00,1,3),(0x2,1,4)] [2,5,0,3,6,1,4,7,8,12,13,14,9,10,11,16,15] (fun _ => rfl) (by decide +kernel)
  | _ + 3 => validPerm_id 8 9
def o15 : List ℕ → List ℕ := oriStages p15 [[0],[1],[2]]
theorem ho15 : ∀ k l, (∀ w ∈ l, w < 2 ^ (8 + 9)) → DLive 8 9 k l.toFinset → DLive 8 9 k (o15 l).toFinset := fun _ _ hlt h => oriStages_dlive vp15 hlt h
def N15 : ℕ → ℕ | 4 => 1 | 5 => 42 | 6 => 312 | 7 => 834 | 8 => 836 | 9 => 215 | 10 => 11 | 11 => 1 | _ => 0
def H15_4 : ℕ → ℕ
  | 0 => 0x40b07
  | _ => 0
def H15_5 : ℕ → ℕ
  | 0 => 0xfee7afead9f214feee98e9b0fe5512e424ad843bd77d5ccb9bc82c0c1767baee8b8280b5623a628ea259a98a6a97ff87f7336e29b57e875062a4d65b47d963c18e39921359d3302072aa1a26936255eb23fda1cd4a1c32b1ba69195d7189af159630ea810e65b04a50
  | _ => 0
def H15_6 : ℕ → ℕ
  | 0 => 0x31cc3318542f7932e7e32e62a2d2502c23e2c2352adb12843c2835f28326278b22651125ffe25ec42489e245ef22b77224f622474221b621fd121d9f20fbd1eedc1ed2a1e5db1de3f1dd351ca561c9ed1c8e41c8c11b74d1ac7f1a2c619ec919c2617a921619715f0d15ef214a44142e013622135781350c13309108d20f0770acee0a115096790808f0677b048500479e041cc032c9024da019ae009bf004c5
  | 1 => 0x69d876907f669d9660d364ef964d776455d634fd62e4d6157d5edd95dce75c6f05c5195bb2d5af095a53659514591ea584d95832a5731e56ef956c5e5518954bae50e9f4de954dc184d1cd4c02f4adc54adbe4a4c648101464424637544b3342d9f4268041be0416984073b3d1183c8b63bcca3ada23aafd3a4663a0a637cd8375d736f4336ef7362c536185359d3354dd34efd349b2349833489f33eef32b15
  | 2 => 0x9f8dd9e1129bdc59b1a69ad919a588994b5986fb97f1a95ab09580c94f1292655903ca8f7c18eab28e5ff8e5d58b57b8b11e89b8588f108890e8859887d9186bba8550884a388414283c14835e983220826d6815e88027a7e9bf7e9b17e34f7d8997d2227ce4b7ce247aeee7a18b793dc78afd785987795d776c676b2c74d2e7394a73946733c570bd0706036fa706f5ff6eb8d6ccd56cb8a6cac36b8c06b4ef
  | 3 => 0xd9a3cd83a6d7f28d7a99d6ffed6981d60ead2a4bd06f4d0601ce950ce34fcd0b8cb648cad46ca215c9dbfc9c2ac90e3c877bc6a6dc66acc5edbc5808c2209c1ab5c16b3be845bc149bc0bcbb9c7bb650b9bbdb76eab75efb75a2b70b7b6dd6b6c17b6212b5ed3b45fcb1013b0de0b0810ad6bdad679acce7ab664aaeaeaa259a9fcea7422a68bfa6188a46a2a3a55a3778a24dfa202aa17b7a17b0a1600a0a85
  | 4 => 0xffad3ff2e5fe5e3fb97efa6adfa5c3f8197f7104f6a11f63a3f6321f6077f5233f4a27f381ef2f70f218cf214ff1cb5f1856f0adeefe6aef622ee951ee359ededeecec4eccd5ebed6eb5f9ead0dea2f0e9d9fe98bce8799e853ce7b17e662ae60dbe5fbee5ea0e55d9e4928e44dee3a59e3776e2910e19fbe0d6be0816e0334dfec5dc037db4a6db162dac41
  | _ => 0
def H15_7 : ℕ → ℕ
  | 0 => 0x133ed132881323a12e7e12ab112a66127151240811f7d11ac91177410f5310b96109b8108d21082e10589102ea0fadc0f8ec0ec700e0dd0d5b90d0db0ce070cb0d0c45e0c2d10b9e20b68e0b3290b1f70b0920a4350a18e0982f07fb5070630632b05d830586a04a7a048500461d044cc042390419b03d0b039a8036450351a0325602e9d02c8d02bca0290b024da0227601c03016f0013f80107900a9700337
  | 1 => 0x27b5a26d1226511263bb25faa25ad42553f2518f24a372420522d3a22b7722a012224521c7921c562181b2131f20fc420c3b20bbf207172068720445200f41fc7a1fc551e1f21cd941c8c11c2701bdd91ba9c1b7411b5061aefc19cfb19aa21922518cf21891e187f81784217728176bc173331718516cc016af1161b415e7115d9015d121595915435154051527f14ac214ac11424a1405013819136bc13622
  | 2 => 0x3a46639fb839c7d398cf39625390d3388b4387f1386df37d7e37d2437479366b23660e362c5362593610d360db360d6357a4353dd3537d33c3e3382f3364132dbb32cc232b433269e31d6b30c6a308482ff422fb182f6f82f1d52f0052ef832ee132ea5d2e9202e70a2e62a2de2e2dd6f2d9592d84e2d27e2c8052b81e2b55d2b4f02b1a42add62acb52a7902a2fe29ce129af42954229203290ae2879f28211
  | 3 => 0x50a9850659503e34f0084ef9f4edf64e8e94e3cd4d14d4c9464c36a4bfbf4ba054aec84ad6f4a8c04a8454981b496da4857e483b347d234759546f3345df545970454aa44d0b44a1543f56436bf42ff542f0c42ddc42cf642a18426804211d41b194193b40f14409fe400ab3fce93fb493f5f03ef4c3eb9b3e9ae3e8c73e5393df4a3dc5f3db043d9353d6f73d6823cee13c0763b5d13b4363b1393aafd3a745
  | 4 => 0x6180a6178060d1560a29607b65ff1e5fd8e5fbd45fb0f5f9be5f1545f0f25f08a5ed6e5e4f35e0215de075cf1a5caf75c76a5c6fa5bf495bf455be8e5b9315b8625b4f75b13b5ad1e5ac335a4b25a3c85a2fc5a2375a04159f5c59696595f45951459217591ea58e4e5854257b50575cc5755456ef95647355d3d557805564c5552054bed54ad85469754072534fb52eb352b0e5244651d0750fc850f9050f5f
  | 5 => 0x72fc672e5572c2071dc871bd671b9a7119c710b8710146f3ed6f39b6f1256ef5e6ede46e6ce6e6076e02b6dbbf6da8b6cf9b6ccf36ccd56cb4e6c5066bcce6b8c06b4426ac6d6a87e6a3376a14969942695a9691d668e4068d4268aec6873c6865b678f0670cf6704566c4166baa668ed6676565e2465b4664d7764bcd649b76470e645d063dab637ee6375f634fd6349f6332f62370622516210861c8361acb
  | 6 => 0x82e2682bf38278f81fa28111d80e6680dd880845804437fe6f7f7a77f71e7f0577efc27eabe7e3bb7e34f7e1be7e1547e0f77e0b27dd727d32e7d2fa7d1b87d0797ce247cc4d7c9137b8a47b5b37b49b7b3b77ade47ac917ac2a7aa1e7a2f77a20379ec779c6079471791da789b6786e3781fd780a977ca87782b768967649776358760b67601175de1751f97515474faa74d2e74abc7493e742ab7383a73053
  | 7 => 0x9541d94c869480d93d8e93195918e6915dd9100290de890c20909c0908269063b9062a8fb588f9308f7c18f7a68f17e8ecd18e76f8e4978e45b8de8e8ddbd8d9b08d9ac8d8158d7d08d4e08d3d98d20c8c3df8bcb78bb148baf48ba458b1728a9328a5cf8a31f89e178960a8928388f1088ba6883fd8820987e2687bf487b598787a8769a8690686764863a38570d84e5e84a38846ed83ec983e4383a24832da
  | 8 => 0xa9b1da935ba9358a8f2aa8904a7c72a7b77a7705a7390a6d8ea66f9a6651a65baa604aa5f4fa5d2ea5c23a58eda4883a43d5a4351a3ed1a27bda2607a2365a1ddfa1ad5a1a21a160aa0eeba0e389fdfa9fbc99fb3f9f24e9efef9e35e9dd3a9d88c9d5d19d0789cccc9c9af9c4b99c1659c15c9b16b9af869a97b9a19699fbd99df4999d79972a98f0b98d1a979ba977e29657e964b0964a395aaa95a3495804
  | 9 => 0xc156dc141fc0e07c0d8ac0c92c0b79c0affc0960bece7bebb9be1e7bd322bc9bcbc412bc049bbcf1bb650baab7ba474b8fb3b832cb7f6bb7bc8b75a2b742db7130b6b9cb63cbb5bf6b58f4b5547b5505b51deb4c8eb45fcb3d37b2e34b22a1b20b3b1dc7b17ddb1683b1664b13beb020bb01bbafdc1af9d7af572af3bbaf1f6af044aee42aec20ae97dadadead831acf4bac6a6ab9c4ab799ab708aaeaea9fd5
  | 10 => 0xd80edd808cd7e4ad78b9d78b7d7825d7730d6e11d6b57d683cd671dd5761d4f2fd484ad2f2fd2bfbd2841d24dcd20b2d1ff2d12e3d12d2d1233d0e0dd0d05d0a32cfa7ecef1cce611cdb71cda60cd408cd36bcce4dcc963cc4c2cc21dcc0b1cbec1cbe19cbcd4cb440cb235ca907c93ebc92f5c90e3c85e1c7fedc7314c6a6dc6973c68e8c6445c57aac5431c4b7bc447ec3e19c342ec295dc2842c237ac203d
  | 11 => 0xed209ece8eeccc8ec391ec283ec1ecebe30eb37aeb33eea6f2e93cae8fb5e8c5ee684be676be64c2e5751e52f1e50efe504be4d94e44e5e42dce42c3e3b0de2f75e2bd1e2572e22b7e210ee1a70e19fbe15a0e1592e1521e0a48e07ade069bdfd02df82adf56adecc3dea88dea05de6dede411ddd54dda12dd9d7dd9b2dd6b4dcbcedb137dae74dac41daa6cd9e91d9d96d9ca5d9b52d9393d9183d9167d8831
  | 12 => 0xff8b9ff6f9ff698fe997fe320fdc69fd5a6fce5efca19fc893fc6f2fb225fb1cbfae68fae28fa86dfa66afa573f9dd3f9547f90aaf8818f8455f81c2f80c5f7fbcf7b88f7561f7481f6ebcf6e2df6747f663df63ddf5c05f5563f54bbf5334f4ef4f4e7ef4bf1f4b54f4626f4548f3de3f396df35d6f2fa4f2acef2a91f2660f1df2f19b7f11baf0c64f0adeefeeeef28feebc8ee6b9ede95edd7eed9ffed25b
  | 13 => 0xffbe7ff92f
  | _ => 0
def H15_8 : ℕ → ℕ
  | 0 => 0x15b591563b1548114ac113a6713968135391324611f7d10f5310e941086d105731042a0f26c0eb5d0e9c70e5080e0dd0dce70d82c0d5b90cc390c8080bfd60bbd90bb5d0b9e20b68e0b4540ad070a7100a2b009ab7090a1084ae07e46076a90707206d6f06cb2069fd0636c05f4805d3c059ef0579e03c530387f0335f02e9d02bca02b52025760224801c8001948016f00148c0136e00d0800c2200b1c00a78
  | 1 => 0x2c8052c7342c70f2be3d2bbc02b7e92b7d92b6592aa6929ffc29fd329ce129c84298e9292032911e2844f280e127f5927b6027b25279232553f254b42518724b6024b1b24a7524767246a423ae323915231c02314922dca22d5a228f12205121d0121c512080320552201e61fc7a1f4461d0941c7a11b9b71b5591b1e31a8c01a05919aa21982e1923d191fa18b3c17f951714316cc016b19167f51631416104
  | 2 => 0x3e2723e0623dbe63d65c3d4243c9763c7f03c29e3c0763bf523bc9a3b5eb3b2aa3b1393b04c3a40c3a34f3a2ad3a1a63a12c398cf398a83910d38f4b3862a37c993746b37388362ed361a1358ad35302350a034647345fa33f4133d6333c3e33997338bc3382f336e5330743265a32439313fc3115d30cf8308483074d304ff3042b301832f4fc2ec672e9242e5782e0d22dd912d81e2d27e2d2222d1b02cd73
  | 3 => 0x5487554608545a8542985378452b44528495260751d075189f50c78508c74f8a84f6734f6384f1f94e7524e4aa4d14d4cecb4cc3d4cba94cb134ca6d4c9634a30e4a23749b9c49a15497e6496da4906748b5c48a4f48979483a047b6d47b3c478674746a46ebb4612b4608d45a87454aa454a044e0a44cd443f5643f21438f143742433ef42fd142e4941f6541c7541c3e4193b40e46401ac3f4e83e7193e28b
  | 4 => 0x60192601595fd4d5fb965f8685f4c75f4145f3f85f1545f0f25eed05e5aa5e4105e0955dd375da3c5da2d5cd6d5c5a85c25c5bf455bb1d5bab25ba565b9395afaf5a7545a37a5a2d15a2a15a07359f8259b6459ac0599bd597fa594e4592175904958a1c5854258399580bc57fc257ce157c26578815740e5729c56ef956d8656958565a2565515607155d3d55780556af552f6551d6550af54bed54b1f5498b
  | 5 => 0x72bc472a317271872644725b872392718e971393712f97119c707c06ff026f4966f14d6ef5e6ee296e32e6debf6dd216db386d9d56d6356d0886c89d6bcf36ba746b45c6b42d6b41b6b2606aac06a9696a4d46a3416a2c86a1ac69c3b68d426837a67d7066c4166aaf66765663e46638f658cb648866429f63eb363b55633f062d3e6262362251620c161fe761bd561ab76178060fca60e9460d15606456045b
  | 6 => 0x87106867648603d85fa785922856308518684e54849ff8416c839ce8394b831c682fdb821e9820878199c8188e81121804697ffb17f2c87edd97e5177e4bd7e46d7e3137e0bc7dfbf7d32e7d2017c7e97c1e87bd817bd347b7d27b1b27aac47a4a67a2037940978212780a977e0d777f0770f276b81766f1765367646f7635875e9275e7c7597b755fc753747510574e777493e7416773e5a73dce7383a72eb6
  | 7 => 0x9c4b99c3c09c15c9b39a9b1959b0cd99dfd98d2898cbc97cb197b419772996dd496b6a96b089639495bea95bdf94a559498093daf935f292e8d9281c926b491ba3918e6917d090acf909c09038f903678ff7b8fb588e7f08e1088d9188d5a08cdef8c93b8c79e8c04c8bfba8ba9b8ba458b6de8b4c48b3358afb18aefe8a8e78a8458a17489ef689a318997c897ea8943e885de8856e883a388251880bd87622
  | 8 => 0xb1496b1113b0f26b0e51b085cb050dafd9daf508af460aed37adadead3ecad39fad303ad080acdbcac846abae6ab215aa7f1aa24caa121a9cada9a86a9681a84c3a7feea7f21a73fea736aa7340a6c91a5a1ca532aa42fca403ba3e37a3a8aa3628a3412a2d09a28c8a265aa2365a2059a1f04a169ba145da0b41a0638a05a69fdfa9f7ca9f2a89f03d9efef9e4e29db899d74a9cce39cbf99c6fa9c6a99c59a
  | 9 => 0xc4e54c4899c40bec3d12c3bc5c37f5c3129c304dc292dc25d4c22f9c2267c224ac209ac2088c1ed9c1b74c1923c116bc0b79c0746c01a3c009dbf9e9bf33abf229bebb9bea46be903be851be4b5be36abe300bdbb4bd960bcb1abca34bbb59bb331ba8deba79fba285b9b70b8fb3b883cb8217b7ce7b7bc8b7a2ab7a02b73a5b7199b6df8b6716b643eb5a49b5451b51deb3112b20a8b2097b1d36b1816b1683
  | 10 => 0xd7fcfd7f6ad7f59d7730d770ad7696d7566d6e77d6946d5af0d5519d547cd522cd44acd3f91d39f7d3455d33bbd2e60d21afd1ff2d1ccbd161cd1536d0eacd0d20d09ccd0667d056fd0522d00d7d0001cfc98cfa7eced6dce736ce611ce132cda60cd408cce72ccb50cc80fcc4c2cc4b2cc21dcb9b5cb964cb440cb0a3ca3fbca006c99c8c9137c8111c7f42c7c7fc7734c6ccec67b8c6109c5dd6c56bcc56b7
  | 11 => 0xebe30ebcdeeacfcea9bcea035e9ee9e9e0ee9719e8e3ae8c5ee8b54e7cb7e7b4ee7ad6e7356e6ca9e5579e5195e4d85e4c53e44dbe4284e3dc3e3d75e3d39e3194e2cf9e231ee1fe1e1a7fe0bbfe040be03a2e016edfe48dfa8cdf82adf72bdf4a9df1efdf0c6de85ede3c3de28dde1cfddfcfdded9dcc16dc871dc7eedbd37db850db796db5bcdb407db279da7adda4d9d9ca5d9272d8f03d8974d87b6d80ed
  | 12 => 0xfe11ffdc32fd5a6fc74dfc728fc2e0fa822fa333f9dd3f9af7f8a32f88aef81c2f7c99f6e2df6bc8f68e3f66a0f663df5e9df5563f5490f534bf526af4e36f49d1f47a5f4548f44dcf3e95f3701f31a6f30b8f2d1df25caf1f76f1f16f1d14f1ac8f199ef1888f1539f13c4f136df11aef0e0ff0d19f06d8ef77cef28feecd3ee8ffee760ee3a4ee001edf59ede00edcb0ed9ffed64ded5dced4c2ed209ecbfd
  | 13 => 0xff4b5ff417fe37dfe320
  | _ => 0
def H15_9 : ℕ → ℕ
  | 0 => 0x43f21437474361f42f1041c3e4193b40e463fe453f6653ec2f3cb6b3c9763c7f03c5383ad323a40c39b99393d43731036f5a33531330de31780309f82f6bc2d8832d27e2c3b8275f326ce12495d2450c22fce219121fc7a1e4901e12719f3e16cf61622b161ab1249e111f91052c0ece60e8190e3620ca5d0b68e0871f076a9063f905d3c055fe04a9b04a0c03e6903b5202d30029d7013c700f8300dfd00b9e
  | 1 => 0x89a3188fc08875f8763b872e4871068290d8276b80faf7f8b27eeeb7e4bd7e46d7d7617d0b27b1c37a912777f07646f75e3475e1c7545e7493e7397872a8f6f82c6d0b66c0e76ba346a22567d706429f63f0461fe75bf4558cac55bb85551c551d654bed54608540d25378452fe951d0750dd250a7f506b0503bf4ef264ea614e8774cc3d4ca6d4c99d4b2134ab64496da487794706b46c23454aa4527c449ec
  | 2 => 0xe283cdf82adf58fdecf9de3b1dddd4dd260da905da7add80edd6e77d547cd5314d4973d3015d1601d158ed0f51d0f47d01dbcf7c7cf118cbc85cb964ca26fc949cc74c4c7311c7230c4f83c17cfc0435bebb9be14dbddadbca34bbf74baa43ba285b8d67b5a11b5612b4320abae6ab3f2a935ca8e92a8382a7f23a6bc7a270ca0a1c9ab769a7df99a899972a985e496452957ad9395c92fd29273f8c4728b1fa
  | 3 => 0xfbb69f938ef8f47f7be6f7038f66a0f635bf5563f4bd7f3279f30d4f11b5f0d19efbd0ef3c1ef37ced6a0ed209e84b8e7728e6abce47a5e3d75
  | _ => 0
def H15_10 : ℕ → ℕ
  | 0 => 0xd1e45ce132be300ba8deb8aa5b0e518416c7294d526e93f54500683
  | _ => 0
def H15 : ℕ → ℕ → ℕ | 4 => H15_4 | 5 => H15_5 | 6 => H15_6 | 7 => H15_7 | 8 => H15_8 | 9 => H15_9 | 10 => H15_10 | _ => fun _ => 0
def P15_4 : ℕ → ℕ
  | 0 => 0x2121
  | _ => 0
def P15_5 : ℕ → ℕ
  | 0 => 0x1285007d12106a4800213105c5041493104a5045d9300a44c47e9510025045c130130544009311205444c1410c64c84c93101e4c41b9310044c04f9310bc0c81713104a4c413941190508021210524400114007e5442c9511244c4599310aa440251301a04c07d1300a64c01c15107e50407930
  | _ => 0
def P15_6 : ℕ → ℕ
  | 0 => 0x51ad00180201744c02c9431845444912131c5046db404264801e1431bc040c694225854c1a1216044c09715116e48148b200524844d95112acc4c38301fa108a594029254c0814234ac800195214e484b61420484c0869312d85880213102650c57930032548959311964808d9501f44c4b09430e654468042126508019210664843a9521e6501629612584c80f1411ec508ac9311e04c4b21622b85047d1612ba5486db10184484f7c201e654c60d20
  | 1 => 0x90505198533404849f93133e508510101f64c8429201b6cc02b1541dc50c3a4301fa4c0029401564c0581302ac54471121034480b612001e508121501b04c81f86117c508691210665446893217a508a3d3206350ce09313985002994114850c461211164c81996122ed04658313d85080f1313761803f94307c0c86db204945003c921016545221411441840ac311e64c003a2007608005132522480721514a6480c393222f440b61521ac54473140
  | 2 => 0x3ae5508bb214945408e130593080db8400e45083ec1028e8840d13001454912151274500314313324842a9411744c4a8950234580dd96106a4c4431413fe540011314b24c4731302c45001c021310501451422b4550519622d4cc43595113a588a49404564807f9102c44c548b404c2508000102ba5089e0211745005d1434740c0d2b401be5843d96210c5445394105e10c9794351c540359312424c84b921032508a98302264c89d9411720c005142
  | 3 => 0xc24c8399412d4d043c131272508314200ae480239301e64c418d532b24844aa320584c05594001e4c80ab101f45041292117a484269401100c58984231a4c87403000f4c83d9520be14c0114325c504069311ac4c41b932146509099215344809f12109a4800993202050c561210345000213210a5088f1402505043012125a58860c102244c4061310184c04d9414b24c03a5402485005d1201804847d1511628803c143034484f213222818130920
  | 4 => 0xc55046c9213dc5043152118c4c4529404fe5841994140c5444d93100ec8458d326164846d1321ae4c4561522c854948930442500671321845040c93217a5053993112b50c6d15313a5086b9530fb4c05693116c4c91a1600e64c4a715003c5843a5502d250418a3223850058b214a8584131101345083f1300560c03d94212454430131522cc0721411f0484069400a4500d2b302204842e910
  | _ => 0
def P15_7 : ℕ → ℕ
  | 0 => 0x280509319400001448315116a4849f13234854cfd9410380c918951530cc47d94037cd442a95158a5854a331332504a004011ec40448420a64c4c99604b65c0b31410d34c9858730c848196a31062080a792001e14d5895009a5014cb510895487f94035e1409b43007e584b99612645c4639602b45093d1715125041d96329e5401c9613facc0401400985041b3211eec40569323265412e0401644840f03229514c579303364c090940428cc021132
  | 1 => 0x1485846a84206c4c87503046c508501602b050135940486544ed96133a4c8151323bccc0b4150122588c61630ce5c0180533de544b795129a4c0569514dc144b61323a850c608301184c4fa1414f85840313002e5045713109c504dc1610285044f13046a9089a1402504c4ed95114c084ee9540d3508a3171414484035403165c01983002a4c46a84042910cb79611de5c0339503044c81e35013a10cd61400440808c16127c4c17216204a0c006921
  | 2 => 0x1a4c47116137cc81319205308c059232376509021635288c0ea96114a5443517042650c5f15009648467b2100c8c8abb3101ac842a93200d080420300640c96396037ccc42793228b080c41311be508d49521944c0f894207c4416603034050c33150164d04593305d2580601401804841c9421645445e1630de540c0b424625840d130094100589633944c4b69602d64c45a83206a548211532985c07bb3007e548651500240c8ed1403184c42d941
  | 3 => 0x381010294216c0848a1503c84c962b6117c5c09a15045c5005214341a584db9702b50c0501303b44c01715222f5488c9610a44412e93204950c4c95318e540063324705801b2201d648025d2041950c7d960228501749501fe484421430d64c93995120e0c84297105c484a79104d65c0593210b21007d15040e504fc9303aa4c82d1502984c0ea95106a5c85396333810ce294002a50483b210105cc171620ba0406393038e141603300d24c833921
  | 4 => 0x4384c4148210fc0848775413c4c5318322d0580041313e8584211630e0480081311b6100fa9402da4c1431612d458406b311be58842951096d08b216129e4c047b20388584eb97306f4c4429312ea508921414084c86892111f4c95e4531804c034a202e30c19221019e4c80d9523ca504688312b0581363311a214d4cb3112c084ba14146c4c80994028ad04579413604c141173146100779600225c5069512124c016b320bc0c0901712c84c41bd41
  | 5 => 0xb41087b0401a25046596127210141153038080d713108c5859eb20134cc49f16316c0c80623114a5c48c94347658c249510ec0804604306ecc4df131164d44cc542336588a113209a5c08314322a1412694210a5055a9635104c83e87051254c7d921088c4026161078c40877402684c0a2b2130b5049a121078cc409960088880c41634a8508bd0211c450830020070084381304765082706331a5004e17303e5844c9631c85047f9703ce0c0bb961
  | 6 => 0x240544b51434764c0f21630cc5048a1606761402d931144480299611965440e14108450cee9321664c01f94251e4c50002137a5409e850224140ed1602b0484b793102850825d431560800f9515184c4761511665c0f2b506085442e8431fa100f7971284d4816a313925806b8210380c02314151054c569412d850c409611885400d8601c65081e3305b84c01f92121dd0cb21514625c40344121dc853e1510e854557932360481319500c858135931
  | 7 => 0xe30854003043858c4b41028ad44098322485c4b21415a24c48e9611fc50083c320e40c0321310a04c59e1403304c8269212cc584579502a458433930002504e215109e4c086971135484f894332c484f505333214c31840102544539323d65088765458e5400815008c544ca06036e580b01602c4180761410e85049b5312854853595356a4c41a9624a948047c310645040353108408025a311dc5442d9712ae4c5579634ba504c31313bcd000c850
  | 8 => 0x2445806f9214a65844684208c4408774149a58c140734a10c8281512bc54cf123009c544035511a84c0c0d202af504849605fc544c317111f1092e95102e54c67c421fc5c02693026ecc0c6b402b4d49279311350800d1601845cd28321134cc0e492113c501771512de5c4eb93207e5051d9733960c82914037cd01603400564c81d9312505cce693121d9080895111ed406e020248440a316126cd483a35101058c8611017658c17951350100d7860
  | 9 => 0x3bcd40033314ba4c43f1400ce5801581009e5cc47d52244500de93023550527160446484cab320e05802a97106e4c48494034850c38142078c8025b30026540a29210645002d1602504c026960344d48569310a610c051525705c04703000c4c50f15029a504281613450c0d81430788842e02007e54425b521421485414217650c4a1410764c8fc9214060801c9310d4580cc22100ccc0da8320fed400a1400ce5003a34108a584869511344c520832
  | 10 => 0x140c02695001c1041e340410d48261541885800704216254c849501185c4231424085cc8283145e100261301b05051e8404145412d9212425042995107654c5015006d508991411a84c40b9304ac540feb514560c01f140055588c11630985442d120188500d704317a140d217305c4c011d411d8441269306085086685021d0412a3621324c9202202341081d9422780c01c9431805808d24217850c0b93229a5843515021dcc85296105c4818d840
  | 11 => 0x34480a31410e3544a91413cac812a5211720843fb303ec4c8041534f450438d411fc5404c14230454c6115324858434b210d4500279631dc5842d951480cc4caa302d0508941323ae4c0c6a21118584028210c04c4c09210aa4406a1521d85849014100d48442932100508de92031ad407d1401764c88d963316540b31311b0584110326445081387048d18c8316132050806b511344c09115015708060170580d40429534465002813217854d4cb21
  | 12 => 0x555489915107e4c8af1320be4805696111a08105160048c40c41321c450cc79602f014447b401784c8b994104e551520514720802717112d5001b5320cc5c00d140536cc83a87013c5409416302e58cc81520d64c050832290500351300104c8099205124c49f153190508155322e848052151164cc4631402c054003543566140ce942140500551702da4846113137cd4083171248544591410620847d95000d4c05d9535c0504ac85006a50857942
  | 13 => 0x14e5cc15442
  | _ => 0
def P15_8 : ℕ → ℕ
  | 0 => 0x574842403012d580200700125004b94007ed485f76003b5042a94109758832b300d65080dd411955403e15013c18c130210dc584237320584c84e1711190843d940075d4c5916003bcc0300500200800f15007c5c00d13216ed44351500b1d0c0bd510654841393008dd5034f500185400c1730b2c801d73117a4c00dd310aed040f84214a540641310a6c403715116dd085f76317dcc8019400a05cc1d54108dd94269531755802c7650255041c060
  | 1 => 0x60180358210255006716001fd000c1410655803357011ecc0095620bbd4829b300cd58007f300754844b4410568c40b5401344c05047207f4845f6540c25040f17013f9946044007c600098310675044b930186500099210611000ef430c44c41bd4206c4c819c4001fcc432d70021500204200f620c0b820016d002e03011f500061410065c020b600b198004954056500661300f4d402c73206f544021540aedc45c13002a4c45e94000c1405f721
  | 2 => 0x3e100270310404c00614006a500031300e24c03d9500ce0800b5310d0540189500d39905b3300ab4c8431300900c84d031056d40217500825400e03002f1402297000660047d5016adc42ab5103bcc41fd5303c58062e430322001fc400f05801dd310691401d5310545403b95016e5840d931025540220610ac60c0c14001acc42193002c14812f2103c4c005b600bbd080d1411904c0145501785c00ba30042d801d74001a4c0589300b2d0021751
  | 3 => 0x3b9945f62118bcc02493001f8840da300a04c01c05104248067f5009e54c1433010a5c0388320c34c86b14001f9401cb41128504588630544c023731124cc0261301984c8029300bbcc8193501605041fb420645401f160056d8858960085cc41713113fd00429300b1d001516302c9483786008dd002ab2002c08012f300f8500038310aa5843804004bcc45e150132d4443c4117550007f4317d98c520300360804fe2103bd001b14002f58007e65
  | 4 => 0x1ac4c01495008dc841d7300266005e1600bbc8443d500681001f93015e4c436c420cb5401397308a4842bb5109a4c8429801924c0131730504c00b4200f51440217013fd5021754060980428730f84c0236100c35485a34007f5404ff65072d841454000a504209400aad04528630c2584110500b1cc44fe100c09404ff430774c043d4007858c1d1210f4d80570630585404d150085840335400165004e37106e90029f21064cc00902010620c2b153
  | 5 => 0x1fd94288700bbd40341400808801d7650785cc2a0610c6cc81d9720b41400f05205454c0a963084c8428871076d485b7520d39801494007f50430b4108dcc0390501765081393212558006b400bcd042c72103460c2364113c0c015160085d000387304c58c2a9320a7cc40ee210d3504390300165800b5501161805a37002a4c8041300084c012f100f010c0ee540701405416103b84062e2102f5001517316cc804b98004c4c01093002550c62f50
  | 6 => 0x16dc842085206c4c00b441162500010801125403735107594c3a43006ecc41713006f080219630bbd04519300224c005b500db4c407e430465001e153085d4c67f300951c00f93001c0c02bb3209a60c309321410841fb6210ed80217210dad0019d4201a8c802983082d003f9610809c04d14007254434f4319f884649400b1d8c25b21075994120400748401b1800b19443d9210864c80216009c0c01db4210e4c02ef300611c01a9600565400ef54
  | 7 => 0x965803044016cd00254400255c4237530a790c039300de184019500e91045a3500250803203205754c0a02106a5cc1002103b8c0219830385443f0400611402ef31075d4034f600160c8061601126002b94105a5c0373610ee500460211466000105001854c216400264c0655400065802ab610124c42f33216e544649500b1d042b1730d3cc432d3110f5444b54003c500021320758843a550085d0c095600d60c81b1630b18400297300054c27963
  | 8 => 0x829480a9300b1d4032c200125c03b9800c74c412e310b854436b600824c007e10075d0c09470096d806a130085cc012e210d3d4c099700835444475004bd0c2c75411f58007f5018c4c039d411119943f0630f80c4495400925cc400300c6d88021400d4580335500208c0351300d3d902604018c4c42b97104e5000616307c54007f5112008430b610124c80694017554039c40085cc83f93200858c2d03201fd04061700f84845b75100058c63830
  | 9 => 0x1085c0161410b40c4139530184c806b6019fd9412f53112580560700fed8404963096d001857006e880131311a01801a2701085405a140077100021310064c0084310924c405b2006e0802162015610019540054500001430650802cc41056d805f7300d388420b5012e5401442001fd4c216210f26001096001ac803d34000a4c80595001250834e4001258068c4000e5441d64003c0c80d17306f1cc5a9711600c00ef5016ed840bc200d450025940
  | 10 => 0x2d0c02ef510d3d001c96103454c2a06002c8802c6210e950010b3006c5801a93013fc845f7400a78c40c15306a5c00082100e0c03c150110d442c7510625c01dd210d38401395008e1002d8320a78840856115a1004474201fc4008031072cc829f4313254433c20056484259500b84c4236650215445a1700265001c941128d042362101f5043a5600689001b1500545c00bc31042d001a95005a4c0151320b40c0237410625801497013fcc034f30
  | 11 => 0x660c4171631304c0051400444c0161520580c034e5310a5402b95113fd40088300bbd0029f530655c0279730d3d94171731194c44b550150d840ef411600c417930132cc83c17012a5c006d43162540008420cb10415b400d3d502a05013f90405c320ca4c00198308dd48495500fc0c83d3300808842c73006a4c825b5002d54c6613104e5c044653111d942174108dc802d8600e954c219310bb8844683016cd400ef651904c81694002a5cc15920
  | 12 => 0x2d544249630681c06142102d5085ac63085d481cb510564c02375014258006b3001a5801456002e0c4061730b1d802f9300bc504529700164804ff310bb840049731660c00854107a0c01d9420440c015b5210a5000217300a58c5906302a60c1715019fd0028131076dc832d4004bd441b13100a55000173028108510700671804a9400670c42a9511360c0029310222003d9300924c80493006a58c05b2107654815b42056cc05503201a4801b183
  | 13 => 0x265401bd4308d8805a150
  | _ => 0
def P15_9 : ℕ → ℕ
  | 0 => 0x954400651001d9402f4200b58802130010cc000f400014c402e6300f904005300015c00045000d8c400550007d8802f7600d90c007430090c402e4100b8c80143000b8c402f5400e4c00067000790004f6500b0c801f76013d44006730085400577600554402761001cc80275101354401542011d9004f5000199400552005d8c0057100850001f640070c00263100d0c00563000995001f42005d9000731009d940264301198c00730001dc002721
  | 1 => 0x8cc001741013d8000e540059d8012500018c80363000190404f610018c404c5000d54000773001dc804e50005d00043500011c804f40003cc40064300858001651013584054300011000074100948403765008d4001540013d8802b3000e50000754003d04007740028c00416000ad8004762008d00017300020c005660005d8003f64011d080176500bd88037610130c00356000fd0c0175400dd44041400019c80163000bd900294000488400532
  | 2 => 0x15d800296001194404e30007cc800470001d4401a2100ed0001050010d8000430003d900162100590c00f430074c801631001dc405730005d4401752005900043400019000376000590404e4000999000750003904005420104c00174300388402360003d5001e5400ad000267600798c014400038c403b3000390004c400155c40074000310000650001dd401552007d00016520018c0021210151800075200598c01e30005dd800742015d4000753
  | 3 => 0x366400ddd8026530075080577101358004f3001054001e410078c8047650078c401c400079d804754007d500277600a4c00176200788400d31005d0800540
  | _ => 0
def P15_10 : ℕ → ℕ
  | 0 => 0x753001cc8006300018400074300188000643001c8000730001c4000750
  | _ => 0
def P15 : ℕ → ℕ → ℕ | 4 => P15_4 | 5 => P15_5 | 6 => P15_6 | 7 => P15_7 | 8 => P15_8 | 9 => P15_9 | 10 => P15_10 | _ => fun _ => 0
def Z15 (s i : ℕ) : Bool := barV3 8 9 (SgenB 11 x15 o15 P15) N15 (idxGenB N15 H15) o15 s i
theorem l15_4 : ∀ i, 0 ≤ i → i < N15 4 → Z15 4 i = true := span_end 1 0 (by decide +kernel) (le_refl _)
theorem l15_5 : ∀ i, 0 ≤ i → i < N15 5 → Z15 5 i = true := span_end 42 0 (by decide +kernel) (le_refl _)
theorem c15_6_0 : span (Z15 6) 128 0 = true := by decide +kernel
theorem c15_6_1 : span (Z15 6) 128 128 = true := by decide +kernel
theorem c15_6_2 : span (Z15 6) 56 256 = true := by decide +kernel
theorem l15_6 : ∀ i, 0 ≤ i → i < N15 6 → Z15 6 i = true :=
  span_step 128 0 c15_6_0 <| span_step 128 128 c15_6_1 <| span_end 56 256 c15_6_2 (le_refl _)
theorem c15_7_0 : span (Z15 7) 128 0 = true := by decide +kernel
theorem c15_7_1 : span (Z15 7) 128 128 = true := by decide +kernel
theorem c15_7_2 : span (Z15 7) 128 256 = true := by decide +kernel
theorem c15_7_3 : span (Z15 7) 128 384 = true := by decide +kernel
theorem c15_7_4 : span (Z15 7) 128 512 = true := by decide +kernel
theorem c15_7_5 : span (Z15 7) 128 640 = true := by decide +kernel
theorem c15_7_6 : span (Z15 7) 66 768 = true := by decide +kernel
theorem l15_7 : ∀ i, 0 ≤ i → i < N15 7 → Z15 7 i = true :=
  span_step 128 0 c15_7_0 <| span_step 128 128 c15_7_1 <| span_step 128 256 c15_7_2 <| span_step 128 384 c15_7_3 <| span_step 128 512 c15_7_4 <| span_step 128 640 c15_7_5 <| span_end 66 768 c15_7_6 (le_refl _)
theorem c15_8_0 : span (Z15 8) 96 0 = true := by decide +kernel
theorem c15_8_1 : span (Z15 8) 96 96 = true := by decide +kernel
theorem c15_8_2 : span (Z15 8) 96 192 = true := by decide +kernel
theorem c15_8_3 : span (Z15 8) 96 288 = true := by decide +kernel
theorem c15_8_4 : span (Z15 8) 96 384 = true := by decide +kernel
theorem c15_8_5 : span (Z15 8) 96 480 = true := by decide +kernel
theorem c15_8_6 : span (Z15 8) 96 576 = true := by decide +kernel
theorem c15_8_7 : span (Z15 8) 96 672 = true := by decide +kernel
theorem c15_8_8 : span (Z15 8) 68 768 = true := by decide +kernel
theorem l15_8 : ∀ i, 0 ≤ i → i < N15 8 → Z15 8 i = true :=
  span_step 96 0 c15_8_0 <| span_step 96 96 c15_8_1 <| span_step 96 192 c15_8_2 <| span_step 96 288 c15_8_3 <| span_step 96 384 c15_8_4 <| span_step 96 480 c15_8_5 <| span_step 96 576 c15_8_6 <| span_step 96 672 c15_8_7 <| span_end 68 768 c15_8_8 (le_refl _)
theorem c15_9_0 : span (Z15 9) 96 0 = true := by decide +kernel
theorem c15_9_1 : span (Z15 9) 96 96 = true := by decide +kernel
theorem c15_9_2 : span (Z15 9) 23 192 = true := by decide +kernel
theorem l15_9 : ∀ i, 0 ≤ i → i < N15 9 → Z15 9 i = true :=
  span_step 96 0 c15_9_0 <| span_step 96 96 c15_9_1 <| span_end 23 192 c15_9_2 (le_refl _)
theorem l15_10 : ∀ i, 0 ≤ i → i < N15 10 → Z15 10 i = true := span_end 11 0 (by decide +kernel) (le_refl _)
theorem l15_11 : ∀ i, 0 ≤ i → i < N15 11 → Z15 11 i = true := span_end 1 0 (by decide +kernel) (le_refl _)
theorem base_n7_069 : ∀ s, HasMonoSize 7 (gfn [] edges_n7_069) s → 12 ≤ s :=
  prove_base_mono (M := 8) (E := 9) (cap := 11) r15 x15 (gfn [] edges_n7_069)
    (SgenB 11 x15 o15 P15) N15 (idxGenB N15 H15) o15
    (by decide) ho15 rfl (by decide) rfl (by decide +kernel) rfl (by decide +kernel) (
    all_step l15_11 <| all_step l15_10 <| all_step l15_9 <| all_step l15_8 <| all_step l15_7 <| all_step l15_6 <| all_step l15_5 <| all_step l15_4 <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_zero lvl_empty)

def edges_n7_070 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(3,6),(5,6)]
def r16 : List ℕ := [10,33,44,52,65,82,84,3,5,9,17,6,34,24,72,96]
def x16 : List ℕ := [1938,6305,2380,25093,9320,36878,49264]
def p16 (pi w : ℕ) : ℕ := match pi with
  | 0 => ((w &&& 0x70) >>> 3) ||| (((w &&& 0x6600) >>> 2) ||| ((w &&& 0x8001) ||| (((w &&& 0x1980) <<< 2) ||| ((w &&& 0xe) <<< 3))))
  | _ => w
theorem vp16 : ∀ pi, ValidPerm 7 9 (p16 pi)
  | 0 => validPerm_of_spec 7 9 (p16 0) [(0x70,2,3),(0x6600,2,2),(0x8001,0,0),(0x1980,1,2),(0xe,1,3)] [0,4,5,6,1,2,3,9,10,7,8,13,14,11,12,15] (fun _ => rfl) (by decide +kernel)
  | _ + 1 => validPerm_id 7 9
def o16 : List ℕ → List ℕ := oriStages p16 [[0]]
theorem ho16 : ∀ k l, (∀ w ∈ l, w < 2 ^ (7 + 9)) → DLive 7 9 k l.toFinset → DLive 7 9 k (o16 l).toFinset := fun _ _ hlt h => oriStages_dlive vp16 hlt h
def N16 : ℕ → ℕ | 5 => 25 | 6 => 339 | 7 => 1503 | 8 => 1773 | 9 => 440 | 10 => 17 | 11 => 1 | _ => 0
def H16_5 : ℕ → ℕ
  | 0 => 0xdbc2ccd1cdbe969ae3cb9e73099ded969d9859ca792ff681bb638a7627415afd356e3d5394b51f6750ea33b4b02a10e262ac1b17d12bd911dea1042904b29
  | _ => 0
def H16_6 : ℕ → ℕ
  | 0 => 0x306c630681300932fbcc2fa262f94c2f7522f3dc2e7332e63c2e54f2d3732c9bd2a6b82999e291fe291bd27e2d27cb2262b626244257fa24756212da2121c1f8e51ea281e3b71e3891d10c1be931b55f1af7f1a3bc1a3461a07c1974a184fd16d86169ce14eed14d39135c61319b12909112f40e0170d4070d1a40cf690cf100adad09faf081c107be406b5c064ea05e870463903fea03a7d0254d01a9500ecb
  | 1 => 0x621ff61e58614fe613005e94e5de735b61c5b1db5a4dd59baf59b8358eef58bb05782b56b7a565585619a55f9e53a48533435330252cdc527535268751e474fd254e7184d9274caad4c90f4c5654be4b4b26d4adbd49d7d48b914789d47127470e64600a4585d44aa44448b4311b3fc273fafb3f2513e8de3e89d3e7c33e6df3e5dc3da983be463bc253b0ed3952f37c9e37a2c3759c36628362d935c1f31c24
  | 2 => 0x931a592f7991c08905ad8ff5e8f1f28eb5f8e6d38d8fb8cc708bfed8b6f28aeaa8a9038a0dd8915e887ad8876c870fb86ac28638184f9684b818449e82be6818d7818967fbec7fbdc7f7c57f34c7ea847e4407c24e7b18b7ab5278b9e78b1a787ca76c0c7580d75246744b773ae673ab77376e7114b7094b6c2c16c0316a2e669c0d6962068e0d67f946661965d876550d651db647a362c8f628bf625c9624fb
  | 3 => 0xc0145bf842bf608beeedbeb94be2dcbca9ebc811bb72dbb244bb1b6b8d33b7c21b593bb52d6b4f5bb3b19b19a1b0034afa26af03baef70ae637ad5afac3cdabe0dabd26ab05daa4a8a9b35a886ca81fda8133a7338a6d80a57a6a5705a4871a43c4a3f45a3c84a3344a31a3a1327a0dcaa04179e5529c3459c28d9c1e79b5c99a25e97fd597cdf976dd976249673995ef595239951f8950ce944cd9417d937f5
  | 4 => 0xeea0aee61cec91fec42debb03ebae2eb4caea22ae89c5e77dee5582e4bd8e49cae45f4e41cde2fe6e1fdddfb93deb70de983de2f6ddaa8dd3aedc3c0daf95d9967d91f5d8e72d79a6d791cd7076d68bfd687ed5b53d4cbfd47c8d427ad3fc4d3f2cd322bd2256d2106d1c1dd0ea3cfd59cf4afcdd6acc53dcc0bccaeb2cae4fcad47c9ffbc8e83c8a7cc7a07c5cadc3e49c1ac5c18abc145bc103ec0b31c043f
  | 5 => 0xffd2eff098fd96afc498fc45afbcebfa97af98cbf97bef894ef7808f524bf4966f4248f3044f06aeefe2eefc79eec35
  | _ => 0
def H16_7 : ℕ → ℕ
  | 0 => 0xbbc10baa10ba950b3510b3100b2200b1eb0b08b0b04e0aeee0aeb10ada50a97109f1f09cfb086b0080e607c4b079c90772707683075e90740d0739f072b407180070a40700206ce906bc00664e0654c05e92057dc056d9054e10503804f7404cd604cac04c1f04bd303fd403c84039c6034f402faf0293902188017d401765016ca01224010ad0101500e4300e2500e02007a70063f00320001a40010b000ad
  | 1 => 0x1554f154b6152ea1500114ed714d3914ba914ab91469414653142c2140f8140e5140851406e1398d13833137711372113695132bf1319b1295f126a512680124711243011d15117b011540111dc1112110b0310a3e101c41009b0fe4e0fcdd0fc9c0f75a0f47a0f2b80ecfd0e6190e5d80e5410e3b60e2b30db080d8910d7640d7030d6d50d57d0d3730d2fc0d2690d0410cd360cbb10cad40c6990c4d50bef1
  | 2 => 0x23a7f238bf236962342422e5c22c0522ba322b7022867227392237421b472186a212ea212e82121c210b62109820c692069e20658200201fbe11f1e11ef111e3281dfcc1d9391d7971d2b71ce2e1cc001c8261c2b81c0bd1bed01be741bcbf1bb2d1b23d1af3a1ab831a9771a34619b871974a1956118ea51879f18572184ff1762816f9e16f5d16b0316ac21684016757166ad165bb1653b15932158fa15682
  | 3 => 0x2edcc2ec872e9192e8fb2e8062e7c52e6ea2e5dd2e3132e3032e28c2e1cb2e0a22ddf22d9172d80c2d71c2d62a2d4ac2d2ae2d1e62d15a2d0e32cf862c9bd2c7a92bf7e2bc012b8e32b4032b3922b0e02af7a2acde2aa452a9bb2a6b829fe529bcf2998e290e828f2b28ea828d9e28c3228bdc28826281b3279da277a72770026dbd26552264c82645425f7025ac6258c2257bd2550424d0424b9b2470723d26
  | 4 => 0x3bdfd3bcd33bc083ba633b77e3b1273b0ed3ad373ac323a6b73a5df3a54d3a3023a0cc39f7739bff38b09386c5386be384d0378ed378533760f37302371aa36eea36cbb36c1636bd5364a1362ad3626c35e1035b2635821357e335684355ba34f2b33407332db32a34323c432325322ac31f7031f2331cd331b6b30f6e30b8930b0b309513073d304f3300932f8382f7472f10c2efae2ef332ef0e2eee52ee11
  | 5 => 0x45ecd4584d4575b455fa455644546b4512444d9b44974444ab4445943e7943b3a43af843910431414307042fa742d8c42d8442ce442bce4265442602424ab4243c422ea4227e42223421ea41ee141dac417914152c4125a4119c4114340f2a40ea940c35408f1403cd4023d4009d3f37c3ee3f3ee343ea9d3e8ab3e8253e37e3ddc43db0a3d6793d63c3d27b3d1193cda23c9653c7343c5bc3c56c3c11f3c02a
  | 6 => 0x50ec350c8c509d0501a64fede4fe654fd244fa7d4f9394efa04ef374ef174e3dc4e2614e1e94e15a4df984db534d8734d8034d7164d49f4d3db4d1ca4cf934ce9a4c9e84c7d64c6a04c64b4c1804c1344c0b34bfd14bf904be6d4bbe64b4834b3ab4aee24aea14adaf4a95149f5649a26491ba491794916548c9d487924844e48235481e8481e047e0a4763a46a81469a94661c464d54630a462f44606546016
  | 7 => 0x5a5b45a49d59baf59b5159a1d5985f5951c594db59264590b958eef58aa958a905899e58615581fb5819a57f8757ed057ddd57cd157b6157b14578a6575be572c556efb56ed556e9956aca56ac456a195679756666564f9561f856113560e3560af55d5d55795555e05508a54f7354bc254a4d5462853ccd53a90529b1526d551fc551d3f51cee51c4751bfb51b9251a45516cb5136351322510835106e50ed8
  | 8 => 0x63f8963ea9638e16331e6322a631556314962ff462fae625f962398622ef621ff6216f617d7615306144360d8260d4260ae160583605426051c603545ff0a5fddb5fb655f9905f81e5f0225edbb5e8195e6495e3fe5e1605df655dddd5dd315dc845daca5d89b5d7885d5025d0835c9565c86c5c7d45c6465c6105c58c5c10f5c0e45bf065bdd75bd4d5bb125b9bf5b70b5b3195b2915b1db5aaf95a7d85a656
  | 9 => 0x6e99a6e7506e1886da606d2756cd646cd2c6cc346c6f26c51c6c32f6c1126bfef6ba846afaa6ae386ac7a6aa7a6aa1a6a43f6a3116a2ba6a2446a1c769ff269f076971669685694f968ed8686466839367f7567e1367c1567b2267ad567a5867a1e675636750f675026723a671386701166fe266dfa66b8966b8066a7e6698b6684f6664e66646666196621665b236520264dd46453d64347643446410a63fba
  | 10 => 0x7937d7906778f1d78d9a788f97829f77878776f37752a772e477137771307708676d8176bea767b17664076635765da76592763d475e70757cd75507754c275482753457527d74f837433f741ec74111739ec739b7737c3736f8735087325672eb872d8f729c572631720947196f711fa70f3270dc3709697073670563702846fe556fdcd6fd146f8846f8516f8166f5986f3616f19a6f0dc6ecd76ebeb6eaff
  | 11 => 0x837838365383379832aa83210831e382f1982d7e82c048261f825b082500823f78182b815708140380cde808b68087b80312800867fc0d7f8637f7747f6ca7ecff7eb2d7e8567e68d7e1c27db117d93b7d8597d78f7d4197d30d7d2747d0f87cfd77c8b27c56a7c3717c1ed7c0437c0317bed67bd3d7bbac7b90e7b6da7ab527ab517a9797a6db7a2f47a23b79ca1799c07996a798c3798917979f7979779569
  | 12 => 0x8c0eb8c0df8bd768ba4c8b6188b5298b46f8ab8c8a7ce8a67b8a5ae8a2768a21c8a13c8a0898a02c89d7989b1d8970d8958b89286891c88915e88c0088aac88a58889808877b8873a886e98833288210880938806587fb387a92875528712986b3d868b2866be864dc864538642185db185c5b85bba85a9f858018523784f0b84e0f84d9c84c9584845847d48461e843bf8437e842da83cfd83bcf838f083878
  | 13 => 0x98591983259803a97ff897fd597ec097dc996e1896daf9692b964e8960d395ffe9531694ff3946c9942b393cc693c7f93bd993b1493a98938e0938ad930999303c92dc39294a9250b924ca921289203391ea991e8b91cd591b5c9144f90e2190dba90ce090b0190602905bd900988fde38fb1b8f6828f44d8f4058ece68ec508eba58e6158e26e8defa8d9e58d9a48d9918d75a8d5708d15c8d0ab8cbf38c3b5
  | 14 => 0xa190aa1763a1638a1099a0fc2a0f38a0f37a0d9ba0812a0801a0502a01179fb6e9fa849f8509f2be9ee2c9ed109eced9e7099e5529e3059e1ab9dff49dc529d7fd9d68b9cdb29cd919cd719cb949ca9f9ca549c7359c28d9c0a69bb919b9cd9b8299b6809b1849b15c9b10e9b0979ae219ac4c9aa379a9309a4d39a3e59a3199a3069a21899f0c99dda99933998af998209960398ee498ea398e099892698776
  | 15 => 0xaa538aa4f7aa3edaa25daa1c5aa18da9d84a96d3a96c9a95fba9499a9197a9070a8cfca8972a87eba8734a850ea84bba847aa8467a802aa7c44a7b07a77aaa769ea7695a762ea75eda74eea7111a7085a6e6fa6c32a6b14a6adfa5de3a5bc3a59cda581fa5805a57a6a57a2a5368a4efba4c96a4b56a4546a445ba43c4a3ef9a39eaa37d4a32d1a2fa0a2f21a2cbca2b2fa298ba27cba25c3a2521a1ed1a1a74
  | 16 => 0xb495fb4930b4885b4844b46b9b4412b4090b3fecb3bb4b3a91b371ab348eb33feb33bdb3046b2ff5b2b44b29b0b23edb1d4eb18ccb1476b1237b11dcb11aeb0f04b0dffb0b68b0abdb0373afdf9afa0aaf910af7a2af56faf089af05faefa7aee2aae9c8ae8fbae6b2ae47eae42bae174adb4cad9b5ad850ad3d2ad040acd83acad6ac91bac4c3ac159abcbeab6f6ab1b8aaf80aaf3aaaeddaad9caac26aa9e5
  | 17 => 0xbfa90bf81dbeea5be91ebe19abdd76bdce2bd5bdbd529bc811bc1bfbbfa8bb903bb880bb5f7bb4dfbaf17bab39ba9efba5b6ba315b9e04b9de8b9d54b9d3cb9b9ab9264b917bb8ed6b882ab8740b84c3b8293b7e6cb7b6eb787bb782ab77e9b77c0b7387b712bb7128b705ab6f36b6e59b6e51b6d83b6c98b6aacb6839b6755b648bb6378b6272b609cb6064b5a13b593bb58feb580fb5574b52d6b4f51b4ddc
  | 18 => 0xcc47bcc04ccbb6bcb6bfcb468cb386cb100cb0accaa19ca7f6ca77aca4feca2f4ca2bfca231ca218ca1ebc9d50c9788c8bb5c8a52c8a11c8227c80bdc7dc0c79f1c79e7c79d5c7272c7071c69a4c5deec5cadc5c3bc5bfac565bc52f8c507ec5070c4abbc4a3ec414bc4002c3c75c39c1c3702c352dc3450c3353c3092c2acac2660c24abc1f8bc13f5c0d4cc0946c08fac08d8c08bcc0798c04f3c01f3bfd1f
  | 19 => 0xd9c31d9a53d98c5d9759d94d2d93b0d92c0d9203d847ad81efd813ed7d5bd77a8d7793d7671d735ed731dd7076d6fe7d6ae8d6a55d65bad5b4fd5b21d585cd581bd5581d49acd471cd4586d44b8d3fc4d343fd31e2d2ee6d2c79d2917d26f4d2216d2187d197dd15f9d12a8d0ffbd0cf0d0cdad09ccd042dd02fccf985cf742cf682cf058ced19cea81ce7f5ce2dfce14cce0d0cdbe4cdb23ccddcccc3fcc993
  | 20 => 0xe3b45e3abae36e2e332ce32b9e326ce2fa6e2ef9e2da3e2d26e2cf0e2a13e285de283ce25e5e2424e1b22e1a53e1764e10b0e0eb5e0b74e0a39e090be08dce0781e06d9e044fe0399e01e1e0111dffb4dfeabdfe18dfb93df9ecdf802df40ddf132df048de8bbde53ade4f9ddbd1ddb90dd507dd1cedd0dbdd004dcfc3dca98dca57dc8d8dc22adc00cdbbfddb5f2dae9edad8bdaca2dac89da5e9da320da2df
  | 21 => 0xf0cf1f0c18f0b31f019ff010bef8b0ef753ef646ef482eeb39eea0aee7d5ee6baee679ee61cee58cee2bdedb4eed743ed3b7ecc36ecaebec5d3ebfc5ebc23ebad1eb937eb90feb814ea52dea4f2ea4e1ea3bbea172ea158e9dcfe9d4ee9b41e9b00e94fae9348e89ace8939e877de8371e7ed6e776be7715e73b6e6f16e6c41e6b85e6a02e69bbe64b8e63b6e631ce628ae5632e4da9e4a8ee43f8e3d79e3c7f
  | 22 => 0xfb265fb0a5fb064fafdbfae15fa3c5f9845f9611f9273f8f56f8be8f84fff843af83dcf83b2f8371f8300f7cb7f73d3f7088f6dd9f6dcbf6bb9f6a84f6a14f685ff6802f6462f5ee1f5d64f5c02f5bd0f5861f550cf4fa4f4d67f4c77f4624f452ef443ef4437f420bf41caf3e19f3b8ef3b52f393bf3752f3518f33d4f3326f326bf2f03f2e9bf2db8f2bb6f28f1f27daf1f88f16f4f16b3f14fff14eaf0f5c
  | 23 => 0xffe83ffbd9ff788ff75eff64aff5f5ff23afef8afe9a5fe7f1fe2b7fe23bfe12ffe015fdf2cfdebcfde7bfd3ccfd348fcf3cfc81afc5c3fc531fc496fc337fc23afc075fbfc3fbc7efb84cfb284
  | _ => 0
def H16_8 : ℕ → ℕ
  | 0 => 0x80a307fd307a5807964076b0076460700d06501061020605f0600005f6005e9205d0f05ccf05bff05a0105994055ae054e1053a60530d050f604ef404e1e04cf804bfd0483d04522044d8043ce0409c03eff03c320383d0382803609034f40306b02edf02eb802d2b02d21026330248101e3501ca30180501765012cb011e50101500ff600f9900f1c00e4300e1b00e0200df400b3500a870063f0055b000fc
  | 1 => 0x1246912325122ae120d911f7011de011c0a1185311750113b81100410a76105ff105f50fdef0fa490f9c90f68c0f4f20f36b0f09f0efad0ee170e6f20e68d0e10b0ce5d0cdc50cbdd0ca350c9c20c3fa0c11b0c0110bf950bb860b7840b58e0b5490b3c30b2c90b0650aedd0aa920a5260a31809fc309ee709d9109c1c09b4409a100981c09514093b60916208f8e08e6408a9d089ce089c3087ab08427082e0
  | 2 => 0x1bb3c1b2d51af311adb41a8861a6961a6941a3af1a3921a2811a26b1a1de1a1bb19fdb19c5919c5819b40190dd18eb618d9718849184be184621811a1808b17fe017ba117955179141707716fe016ef716e2016e1216c4016bdc16844167c8166181661416181158fa1587e14e9f14bc214aaf144c3142b21425e1421d13ce213c871399b139481378c1378b137711321a130ae12c1112adc127d912611124a3
  | 3 => 0x2397323567232542311422ece22e5c22b7022a8e22404223c32237422239220e8220d22209121c4921825216632152a214a920f7920c9820c5720ba720b7f208872051e1fd971fbcc1fa391f9181f5e11f4751f3ff1f2721ef731ef111ee9e1ed0d1ec0a1eb121e9961e5df1e5611e41b1e3281e30c1dfd41dfba1dd7a1d9a41d6d81d6d21d6971d4dc1d27d1ce3e1ce2e1cd5d1cb4d1c96d1c5881bef61be63
  | 4 => 0x2b37a2af7a2ae8b2ab0f2a6292a6252a3452a18d29a1b2933e2931229112290f7290ad28fbe28ea828e2c28dab28751287072865628138280d927f2927e1c27daf27bcf27b46279b4279162776427700274312734226cb926c4e26b6726a552687f2664b264542601525d9f25cca25c8925b8625ada258f025601251dc24fa224b9b247e824794246c52455b245142434d24276240bb23d8523d2923bf22398d
  | 5 => 0x35821357ca3573d3569c35684353f33510e3499c3446733fcc33c8e33aff33a3033a043364733637332bf325eb32169320f331c9731b85312343108c30ce230c3730bf13087330629303392ff342fe9e2f8d62f8872f7dc2f7202f4e32f33c2effb2ef3b2eeeb2ed592e8df2e5dd2e2972e2752e24b2ddda2d8122d3b92d2092cea22cc5e2c6dc2c2202c2072c16c2c0b32bf962bc012bae22b6d92b5e12b392
  | 6 => 0x40278401c74009d3fa803f8b83f85c3f37c3f35b3efab3ee3f3ea3e3e94e3e5643e0c23e0bd3dc273db0a3d9eb3d63c3d3de3ccb93c86f3c39b3bf813baad3b5c63b3df3b0243afe33ae4e3aa933a2b239d7139782396e73903438f8738d11386c53817e37ec437daf37a6f379803755137505374e536fea36f1d36eea36ec936ddb36bac368513673936386362ad3626c360c435fda35e8835e6235ac235961
  | 7 => 0x47ff147fe447f4d47e9f47d4647ce047c8947ba14794547845476e347621475434754047320473034727d4601645f7f45e2a45add45aae45a314563e455fa45564453dd4523e451fd451a34518a4512444e6244ddb44c8b44bdb44a8244a5f4477c43e5543af743a6f4316742fd542fa742c0e429c9427394255c4252c42479421ea41c7341c104176b416b44125a40f2a40e8c40dec40da140cde40aad40306
  | 8 => 0x5212a51f9451f7d51ecc51e8951d7d51b5f51b0751a3151766516525120d50fa650d745039b5035b4fad74f6484f1e84f0754efd84efaf4ea6f4e5394e2ef4e26b4df884db884db514dab74da954da144d5ee4d5d74d5844d4f24d3db4d24a4d0de4cf6d4ceac4ce9a4c6ae4c2094bfdb4be6d4bccf4ba524b6984b34c4b0374add74abe34aadb4a93449dd649be74977b4910b48f5c48b89488f448735485dc
  | 9 => 0x5c0b55be1e5be125bb4a5b75a5b65a5b5275b2255af6b5ae435ad9a5a64a5973f5969f5966c5904058ee358ea358e6a58cb458c17588825848e584355819a57f1957e0957c1d57c04578745778d5753c574fb56ed556c8f56baf56ab056a195689a55de555c4b55bf155a4155796550ae54dce54c4254a3b542e45402c5377e53776534b853318532c1532905314052be2529af5296e526a5525f55243a5234a
  | 10 => 0x657f0654386538864f2464f0e64cfb64ad96494d647ff6427d64236638e163843634466322a6314962fd562fae62d2362ca162ac5629c26262e625ed625b862349621b961f0d61d1d61b01619876160461443613b46132c6125260da460bae605b5601d55fff25fef25fe8e5fe5e5fe1d5f5e75f5485f2d05f2535f2125efd25e91c5e5005e4bf5e1605e09c5dd385db2f5d2395cea65cade5c9565c43c5c3fb
  | 11 => 0x6ef4f6ee666ebeb6e9706e5836e54a6e36b6e15b6d5586d3fe6d1d56d0fc6d0786cc916ca5d6c9176c77f6c32f6c2f66c2f46bf9e6bf6e6beab6bb746b8c46b6d46b33c6ae216ac7a6a58f69ff269fba69f07698dc6964668fa868e0568d6068d5d68ae668a736863a685316823d67fdd67c5f674256716467138670a866fef66b7066ae866ac56664e663b36606165edd65dcb65ccf65c7f65b4765b2365b06
  | 12 => 0x7855178537784997848a77d65779e0778e4776f3775b7775b476eed76cc276b5776640765e97637675ea775e6675d0e75c9675507751287506574ccd74a9d74a7374939748b67484f74805747ea741f17419474111740cc73f15739ec73805737c4737187307072d8f72d7472c92724687225771d8771ab171787715287102270f6670ef070a41709847095f70725706f06ffaf6fdcd6fac36f5a26f5986efd8
  | 13 => 0x825b082500824f781feb8182b8175b811ca809be808b6806ea802c28024f80126800818003e7ffcd7fe3a7fc877fb4d7f9397f6ca7f54d7f2927ecce7eb8c7ea7a7e8f77e7247e63a7e1c97de9e7de8e7de777dde07d9177d8597d30e7d0987cd287ca957c98a7c8db7c69d7c5887c56a7c32d7c0437bed67b77c7b0787af3d7acf47acab7a27e7a12b7a10479f80798917982879631795827911078c8d788e5
  | 14 => 0x8befa8be478bcef8b3da8b09d8afe68aedf8a6e88a5ae8a01a89b1d8941d8902088e0d88cc788c32889cd88956883ca87fec87f8f87ac6871298707586e3a86db2869238681b86570864538644c864338629d861f585db185dad85da385d3985d2785bee85bba85ba4857328552284bd684b7184498843bf8437e8429483e2783dfc8397e838a48373582ffb82f1982ed082be9827c882750826f282656825b6
  | 15 => 0x963bc9601c95e2095031949119487f94759943e4941629401e93fd993f6393e1c93b14939c69383d934cc933899305492c7192b05925e49249791f7591e8b91d8f91c09919f99105c90e4990e2190dba904d290361900988fa148f55a8f5268ef318eda38e6ac8e5558e31a8e2118deaa8dc498dabe8d9dd8d9bd8d8428d7528d5418d4e68d4c98d39b8d36a8d02a8cddb8c91f8c9168c61f8c5808c3b58c205
  | 16 => 0xa0ed4a0d51a0d12a0b10a0907a0801a03f79fe699fd559fc719f9f99f64a9f4939f36f9f0b89efc99ee2c9ec549e7e19e4ad9e47d9e37a9e2ae9d75a9d68b9d5019d4199d1cd9ce8b9ce209cb619c9759c7359c5ec9c2d59b8299b6969b5939b4a89b2509b22f9ab849a19499e2c999ec99976998b4998af9982099634990f4985cc9802d97f52978cf9764f97466970599703496d9196d029692b968c396796
  | 17 => 0xa965ca9614a95f5a95efa948ea9419a92bda915da8d69a8932a8801a8594a83b8a80eda804ca7ad3a77aaa72bda7205a7085a6f82a6e25a6e04a6d80a6b1fa6457a621aa5f14a57a2a564ea560da55ffa558aa54c7a53cfa52c4a4fb9a4ecea4da1a4cbca4955a468da44fca44c4a4118a3c33a383fa3750a3403a298ba247ba21d0a20c3a1f3ba1ebba1e81a1d83a1b16a190aa18c2a1888a16c4a1304a0f38
  | 18 => 0xb18f1b12c6b1253b0d2ab0ce3b0c8bb0bd4b07a0b04cfb03c1b0088afceeafba2afa0aaf9d4af56faefa7aeb10aea87ae9c8ae98bae8b1ae870ae3c7adc19adb4cadb20ad9bbad9b5ad6e9ad633ad210ad204aced7ace10acc2dacb10acb0eac886ac5f9ac581ac3e6ac3acac0e7aba0bab8a6ab795ab44bab3f2ab1b9ab1b8aaeddaaeaeaa744aa611aa5fcaa2d1aa25da9f19a9d84a9b75a9b4ea992fa97e2
  | 19 => 0xba27bba036b9f1ab9d54b9d44b9d3cb99cdb98c6b97cab971fb95a3b9065b8c3ab8a87b7ec3b7d9cb7d82b7bbab7aabb7876b7432b72e1b7130b6ee7b6ea0b6e1bb6ce1b6c73b6c29b63dcb614db610cb5fb0b5d0fb5d05b5b25b5882b5752b5729b5310b5101b4ddcb4da3b4d7bb4a60b495db462eb4549b4505b4325b4089b3cceb3ba1b3532b34d7b2f71b2eedb2e91b2a5fb28f3b26cdb2604b227fb20b0
  | 20 => 0xc25f0c25a9c2307c2231c1c5cc1bcfc1856c180fc12a1c1119c0fc3c0eaac0c48c0babc0ba9c0a52c07edc067ac0607c0246bfca8bfba0bfadfbf792bf415bef76be91abe736be727be4eabe451be06cbd9febd7b3bd794bd497bd407bd2f8bd1f5bd157bd0d0bce6ebcb66bcb15bc873bc832bc7b5bc331bc13ebc085bbfb3bb6b5bb388bb1fbbb1d2baf6dbaf17badf9bab3eba97eba937ba8beba7ccba5b6
  | 21 => 0xca6d5ca6a6ca1edc9ff0c9fdcc9867c9194c8fb4c8f56c8e9dc8a72c8a39c897fc884ac87c3c836cc8314c7d47c7a01c77c0c7584c74abc7272c7071c6be3c6a72c6a31c61c2c60d3c5f26c5984c5974c5481c5231c504cc5048c503ec4d59c4ac7c48efc4755c4626c432ac42a0c420ec41dfc40b9c4002c3ee4c3e76c3c5bc3c1ac38d3c372fc3450c33a2c324dc31b4c3028c2ea1c2a46c2a3fc2a05c2925
  | 22 => 0xd1927d165cd10f5d105bd0c99d0bd2d0bc5d09fdd07fed05a3d03b5d031ad02d3d0236d01dfd0085cff39cfba8cf682cf672cf51dcf367cf263cf21fced19ceb01ceae7ce7f5ce549ce38fce273ce0f7ce0d0ce03ecdc20cdbe4cdbbdcdaf4cd86dcd7d0cd4eccd389cd21dccdabccccfcc799cc607cc16ccc0f0cbd1bcbc73cbb6bcba63cb732cb71bcb702cb5dacb452cb41bcaf1acacd4cabfbcaba2ca7d8
  | 23 => 0xdc810dbf89dbf31dbdbedbacddb77bdb6d1db4bedb27adb056db024dafe3daf21dab89da3f9da330da2f8da127d9ce9d9759d95fad93b0d91fdd8f17d8c90d8bd8d86d3d84e3d820cd81efd7e7dd7a6fd7671d7437d740cd72aad707dd6b5bd6a02d65bad5dddd5b34d54c8d5436d5267d5202d4be7d4b5dd4a70d43f9d3ee5d3de0d3d9cd3d15d3bb3d3b11d3ab3d39f4d3630d2e7ed2c28d2a05d21c1d1acb
  | 24 => 0xe6094e5ecae5bf9e59b0e5781e5632e5631e52f6e4ba8e487be4579e4140e3d78e3b37e3797e3795e3540e32d5e3201e30ede2f2ce2f25e2d43e2cf0e2b63e2a13e29b6e2149e1a9ee19a5e152be0e06e0c0ee0a26e06d9e0245dffb4dfe18dfa00df8b5df874df5e5df132df03bde98cde96ade6c4de63cde191dde34ddcaaddbd1ddb90dda31dd835dd792dd70fdd282dd1cedd01adca0fdc994dc977dc973
  | 25 => 0xef36aef2dbef17bef132ef0bfef0abeeda4eed02eebf7eea55ee842ee793ee635ee271ee1b0ee0d4edc52edb0beda33ed4c9ec99dec980ec628ec382ec1e0ec1d6ebba5eb937eb936eb8baeb504eae68eab97ea54fea541ea4f2ea278e9dcfe9d80e9c1ae98d9e978fe978be94d9e92f0e8d28e87c6e8765e8724e86dce8501e80dce7f2fe7e1ae7bc8e7b6ae75b3e73e8e6f7ae6f6de6886e67a4e64cde6153
  | 26 => 0xf848bf83ddf80f9f7d40f7cbff7b00f78d5f7849f77e9f7666f7665f738bf7131f70c1f709df7010f6f6cf6d53f6cfff6962f6587f6462f623ef60b5f5b39f5878f5861f5644f5114f5019f4fd2f4ea8f4827f440ef407df3891f36bbf2fa7f2e90f2acef22a5f20d2f206bf2057f1f88f1ec7f1d7ff1950f15f7f144cf0c18f0b3df09a9f0706f06f9f061deffa8efe43efd99ef9c1ef8a0ef745ef6beef5e8
  | 27 => 0xffe89ffe57ff5f5fef1cfee60fee1ffec9ffe796fe5b3fdccbfdc32fd8fcfd7d4fd027fcfd4fce95fc9c0fc808fc800fc554fc18afbfaffbf04fbca8fbc57fbacdfb942fb41cfb210faed8fad02fac5bfab77faadbfaa1cfa95ffa3c5fa1eaf964af940df938cf915bf8edbf89f7f88ff
  | _ => 0
def H16_9 : ℕ → ℕ
  | 0 => 0x25da32519f24c3024b9b24ac823bf2234e4230c7227f521aa8215ce20537202b01f8451f5e11f2721ce2e1c32c1bc4e1bb8919b5c19b401986918f5118223181fe17a2e16bdc16b571613a14bbe149441433712b2c11750105fa1015b0fa490f36b0ef320ee170e6f20df580dc8c0d8140c6ad0c1eb0c11b0b3fb0a7b60a1dc0a11d0916208e0f07a5806fc80612404cf8036c80355c02321018b800e1b0029a
  | 1 => 0x4a86d4900448b894886e486974754346d7f466ac45ff54543644fa0444724319342fa7428fe41dd041c7341c104167a40f2a40d793fdb83f0653ee6d3ec903e0bd3cfa13b0fd3a1573a03339d4c3833737ec43767936f6035821352d034e1e34cff34c4033110328bc3277b3264e31a433172730cf0307b72fba52ef572ec2c2e43d2e34c2d8122d5f92d5032ceea2c1952b5352af7a26b67265f02645425fc2
  | 2 => 0x71bb46fdcd6f81f6bd666bd4a6a7d569c86696c46961b68d8568d5d685af681f667f646777b6716466b7065c20656cb62aae62707625b862349608e85f32c5e5d95e4c25d9735d82d5d1995c5155ba065b9105a27c597d15966c58e7f589a8585d4584ed57f1957bf657a0d56fc656a0c55f7455d1d5511254edd54a3b543bf5436a537f9536c35314652a8852a1d522fb5199c4f3384d92b4bfd94be6d4bc47
  | 3 => 0x90cce8ff958f4168f2428f2258f0638e5a38e4fe8e31a8d8f38d5418d17e8cba08c1e58b96c8b8968aadc8a3e48819f8712985522843be83010825b0810a18104f80840800907fc357eee27da697d9aa7d9177cea27ce1e7cd3a7c7447c71c7bca37b9c97b5e67b0787aa0e7a85579905791f97906078a38785ee7713576d2d765717652a7643a75f80757d77484f73f1573a93738de736367339172d8f71e55
  | 4 => 0xb6b1fb551bb5212b4484b2732b2725b20a5afa0aaf56faefa7aef65aea6dae9aeae98aae739ad633acba3ac91eaa611aa59fa9b75a97e2a785da77aaa7554a7085a67c6a54c7a4ecea4770a4547a4118a35aba339ca2375a1ccaa0ffaa0ed4a099aa07779f17f9f0609e59a9e5799dfb99d7f09d68b9d3d89c2d59a3fc998af995b3983a69802d969a89688995d5b95236941e79372a9337091b3f910c890e21
  | 5 => 0xdd73fdd255dcf51dcb34dbde1dacebda993d9d3cd9d1dd9a88d84c8d7e7dd7699d756cd6961d672fd5c0ed5774d4ef1d4960d3f52d3b4ad2bddd2baed1df7d1ba6d177bd1650d0baad031ad0290cf293ced19cdf59cdaf5cc799cbe02cbd7acbc9eca7d8ca0bdc95aac899fc879bc7c4cc7272c5b88c4f1fc3bcbc36d0c2b1fc0ba9c0937c041abf792bd8d8bc94cbc0fbbb3e8bae70bae4dbab3eb8905b80c8
  | 6 => 0xff769fef39fee60fee1ffe6d2fd4f2fd436fcd7efbeb1fa6dbfa5aef99a3f938cf8c50f89f7f87dff84b7f7b00f6b8cf4dc0f4d1ff3788f3485f10e6f06f9f05c7effa8efd8eef530ee43bee1f3ed5cced5b5ed0ffeaf13ea991ea4f2e8dcfe87e3e80dce7746e7526e73e8e6d07e6a4be5f1de3428e1a45dff0fdfe8cdf9c5df98edf5f3de7baddbd1ddb90
  | _ => 0
def H16_10 : ℕ → ℕ
  | 0 => 0xfe5b3fb09af7cbff6f6cf4ea8ddcaad3a90be736b03c1accca978cf783245b4b5552e2473200e9160c274
  | _ => 0
def H16 : ℕ → ℕ → ℕ | 5 => H16_5 | 6 => H16_6 | 7 => H16_7 | 8 => H16_8 | 9 => H16_9 | 10 => H16_10 | _ => fun _ => 0
def P16_5 : ℕ → ℕ
  | 0 => 0x1e1420d2508099510404408e9300264c40794307c50c189510205007c92023a500021521da440131500504c0081200f65441e121008508461410ac5084394111648002120
  | _ => 0
def P16_6 : ℕ → ℕ
  | 0 => 0xb545408d1410925400a92003c504999416b64c41e9410ec58e1d160168584899503345805f9205c05002d1310b24c4ec8402144c58e93146754d6094010e480140200064803d2313facc46e1315d64c5c78606c2481c08626d44c46b96100e4c6931600344810f1520f4cc20b1425624c4d494111a5452a1411ced40551545144c55d820138540a89416a450d7d1521dc5085c91017e5001e9611224ca3713021e484f7140080508c69626b84c94e921
  | 1 => 0x3525443414204e500101423dc548759407944800f9610245860914116c4c86f1213a85048115224a1887915018c1481915005a5082314208c5482894160e50c4c12054e504353303204c6c39408b20801096311a5055f921378540091213e854cb40402ca4c40394100e544bd1214c45042f16008c4c89a93007e5401e9510725003b9320ec4c8c89510f554cd59500424c84693132a54039130064480b4942026545059326fc4c59a1401d25046b951
  | 2 => 0x13a5881e93124650001940232545d5b400e6584b495231054c8f8103dc581eb3500264c473b40704500278302484c0919303585408c94100e5842414320e58e3c1305384c0921402465408c9611bc588bf95052e5885f930026584c594120a548ae9611250413a1611465000f1616044816595018650d3894113a481b815025458226140526540101621dc4c9d5b300d510d4e9422045081c9200bc5482e9521c65803555386e540439524ac5800f131
  | 3 => 0xe65453915151850d299317f45019a1600bc5005b130125541519520a25469b02007e501379510360c48a0620c84c57015002a54c0994171c040f7162b80500658605464c8f09605ec5809d1322f44c4981421e4580d414121e585c81611b050c5782013850c3e1313525844394213a548f31621344c8c11514f4504cf94115c040019302ba504939310e64c44606110a0c50403019c50819140134588358600b45842c96105a4c8c69520525445f143
  | 4 => 0x4e58014010390500ab1403584c1681323504c56494328a5049d9313eb4c57b1303cc508c11312fe4818e9414044c4059300bc509048610ba508b613163c5848d1300f84c073b305c4500e41503fe50c2f1205a8504c9141322504951303ea880e386148450c0f9410180c08c9318544800a950562505551402d2484ae021450584879511984c00a9300244c5451512d85057115090e540999311ba504a293105a5494514129c184c51425545417f921
  | 5 => 0x16d06102a4c4211512344c45a1211564c93d942224500101528985803e553546480ef1313164c6069517fa5440915116854469862
  | _ => 0
def P16_7 : ℕ → ℕ
  | 0 => 0x188c80653194cd045214314650d799520048824f9707e854ca38316985c442963024544f04430525c2e017113c500c41511f04c8c116143a586e01512c84c6039322cc14660971b6a4c4be9614d41c4751320ea544051314ac0c03d15265c509ae97079250b642300dc54e351503c85821b95094d18d89851436cc498352b805073283077654d8e9510be5425c9400080c824953464042829507bacc28296089658436140918880aa9717664ca0b941
  | 1 => 0xb8058443d63cc24c1ae54188150d0d941698585ed9731d4508749527ea0c8b5941436d442c93147c5c7610400f04c88503043e544b49731a4cc56794130850b08150016548c3b3230ccc815171d940c0609515c8440dd15138058019a3044a4c5cd832be0545eeb407bad411a1509105c65c9603c6540f21403c6500239318564c933b3112d4c63a1700b654e6195114e54d691401760c8b9961a1a0c1b61423c154c89960a605c4d99519105054a950
  | 2 => 0x6f6840a916152c540a81510945049a9619d814c3694200d54d6b16108e10019b5129250d751303c0cc9c392126154436972ba25849893247c5856fd4339214c411600965022f140be45c2bb07002e4c1cf96026e480611738245814a17144a549ae46317c4870ab307e85ce680212205066e95088c501a89214204c50d931344549fb13019854129153a00cc436952228500899303c8540f19601f058e9c9704a458df19735025858b9705e64ca5c843
  | 3 => 0x33c546db16147c545d20502285808995053254507120052541878503164c98e9716261c6470418505c59a0701f29851f132910585ec930bd50801213233a509669329081860f151b405400d1200ea4c5691602a0442609318565011714235ed400655378248401542434500b59615bed88121630c40820d94167c54c8897128950cfa9302ba5034793021c481418504cf54d491200420c179170a66500c49705834c93c0502e6544d911092450032142
  | 4 => 0x15c581cbd4341254c17173260d88b7131a924c4749731805ce9c94081f18d3f93102e4c47d33182e5454a9600aa544381600a8545f297118e100c7231850505369315b0580039709f0508c3a3130c8c60f161d0e503439601be5ca6387137c5002c95107a582efb4038ed851997181ecc12a17123814d2e9422408c2d08408e05802496390cd019e0503025c40c1517ca5460fb420760862713106758c151317f84827095070c5017e040d0854406961
  | 5 => 0x3cc880aa5630dc5cec91400484c16c1501ec506240401eb4c59815117e505c897028e1069997068810cc49600f04c0cd820794103541213261002d9325884c0a05539aa4c8249314585814997133a5402f97047c4c53d11099a5409994222ed81601423805c03812062a5463416012e5028e840102500d89600ee5408b110066cc42216143c585831530a4540b59102820823c070646580b217306254e751314b4d02a59401044c0b99314e80843d140
  | 6 => 0x7765cc72910064544f3a31bb64c07a161010cc30915181ecc59d83202e5829c1404685c07d3321505c453973722541521417225010b23118e109c585362cd40e3b31478580039502b81c5be8534a85046c13135ecc0429316d4484189630625cc5794019e5442b0400fc544751311d24c5781316a7186de942b724c40b95302e5cc905520f04c57a1410ea4c870951260ccade95116858635940b3a5063a96186e5c0319609c25c0e3b514b558400820
  | 7 => 0x2d65c51097094c504b49326b45013802010c544431611c2587081706a64c1048504b65c0709412685055b9420be5810da301eb5040c1711cc544fc9700f058c191313bc0c43a973562cc0420107a25448317300514c66031280cc4e3b4143e5c55e13043c5440697136d54dc89608365c49195113c5824336017e4c4221414584c648131a965c0d18417b25cc60971670c836716000558e7e43224c4c42d96316c50ea6942a9850a3a93125a50281840
  | 8 => 0x43e584a817129e5c06403032c0813f9710fe4c14b1701684410794226a504a49734365456716120a0ca0fc4108e10adc951064506f417316c54c5b1733125020fd214da5842a9716f21002a1714d81c13f9410ec14eb45319de5c03f1320124c0b1161b3a585789311f0504b016123a5c2a59502be5443a96107a5c21194123a5410f9410ca50cc502001f50c8b17179c58536941014548f3d532205c43716301f10aad0600665450db61ac858015161
  | 9 => 0x36410a1197199a4c15e1500fc58c985212ce1013103005e085f68703444caefb42524580ea9525bf485ba03222ed40181312b21c4d9160500440b496336ccc5e715104c5c01b9621945843983140a505a9b5003650478961182585d7040152508411700605cf1b9539205450db211025c1412300924c98b340312148d6d63ad14847313109a4c005172846585ceb100ee5c071051a004c4049701b05035b9508ea5445515283f544a915114e58c07b21
  | 10 => 0x90cd409693002458423142086548a4953442500500204260c03f9321e85c4298415661410dd635c6cc60a1512a20c26316339e580e715144454595a303f0584d89406a6d034213157e4808a1306d85483f9739d45c4349700d05c1781613aa5823d0700ce5063d05019e5c41a87094ccc22a96122c544881515928c04293221e040d11428cc1043397172ed81ca95169c4c171b515e0504cf171480104f613051350ea40401685c407b306ba5403d130
  | 11 => 0x6a6cc10a1324b4d81911700f45c02c94322ec819817101950043c43810440838710741006e9404c2500611321804c81e9400b01c85f1315c6d0421850a521c2f89300684c59f0713ea5029485074e141ae22013e0876703245c441e71312ad545e89103d854c931632525c4919712340c05114112d0c88bb403a05804e1700304c4f59411305cc5411038e584ed9718fe4c5951312a45c49a9513f40c85f96185a100e693129e581cd9525fa88009953
  | 12 => 0x3d84c90db415305802d930644541d99301024c19016001450c7c1610ee501b5a3036c8c875173b38cc1199318284c4ec12013c4c1b51604f4584611537e44c48196306058db6971019484e695339a58e481719d45454c150222545308526a2cc68f05361644057930444504c8871216504065610d8541cd04006a1007097106e4823a97133c584b11316485c0411402c05c4171306d2504af971bbecc0d89503625c10f9319401c0050700a8506df870
  | 13 => 0x1d8505c3b318e44c422940874549af17023a580679310f05cc5f0406da5842215104e1c43f95310a4c1daa309d4505a9c329b0540aa9411540c167b61588480d99710305845a1519b85c4fc96042854d0a1730da1c1ec93256c4c45e1400d6104f59716a2d04398304005082d9733b6585d514102e500e34424b4c80b595157c4c5150403a4141359710825c5b69413124c00133113c5404e8503ea5c2be9631ca5085a8700a61c43203253c5c08bb30
  | 14 => 0x7a5409d16073ad419c5512d05095a930252505081712465052902059ec87001405965416b13281e881161505b25c06015349c5403a941ad00804e8402a450e0b961abc5812f95153c4c08a15003050489940296548fc1415b1584d991038e5052f320d0a100560411804c0c4171054504c117159c54406951b1a1002a1612fa5c419b41372cc09317383c441698436d8486769509981c0e3b212364c02f94043a5452315348c58d6a84233614043171
  | 15 => 0x3c85c0f197087548459810d9c5c160a10014508b7132c0410060941af6100b11411d85c4b01413ae4c580d512be4c43d8405025454016135b509af1603aa481598302744c116121216584791711e25c4d01420544c20593014650481953ba45c53f1501cc5c4551213ae5c4541415de54c7c86142e581eb1610485cd359613745c5171711de1c50d9619c81c045030be25c112962b504c0d81713f25408a170444580409503dccc007c63b9654936050
  | 16 => 0x4b4cc14917048a5c5221710fc504f3443168505151429468814f15022c505b51505165c5451711be548881313a454b1434201918133c4298c4c9ae2105f44c19c9710fe58e2a9512ad4c9eb141a1a101098503344c4df1307f84c2769702745000644149c5002c020466584118305ac58db29300195461a03119e5858b3604fc480899700ce544fd9716ca485309703e85c41813244a4843e07150e1c04c1302808c92b1710c64806515186610093070
  | 17 => 0x5c4c9009512415471804083f4c49852052858567c536ca581719317c150819d43cca10283a31059508a814100e5815f9504cec842903107e5094c170670d819e920d74581c1941874d495b1718025050114259f58db48302525846794124658407b3148a4c5221413c25c52014201950e5a9601d24c1c31504725cd3f1406d84c5cbb206b9545b6931004c867d2300a4503111706e05c5bbc633d64c9719515324c45f9713d0504d69320ce5856c950
  | 18 => 0x7e4d45b8161246441981617ec58cf61730ea5c4859510125416a153d9410020961012502789737ee5c5691502c4544b01510dc4c8f6870010cc4033314ac505578323c21c95f1517cf484e697353c441095423ae545859715c65040444300d10d1a16064450167b4144a5c56a1632f00c1481536464c90993245a1042d0302165c46c1705c6c84831530885c7671500f4580949512d4508b895135b104049603345cc339108ce100b117140a5c572171
  | 19 => 0x57e4c6701414ba1c4b011089e5c09a020a805c419b617625083414048c5ccfc171b1918c6517110410545951514505a8941b9a4c8209511444c41316044a5864f94048a545221610f4542128536a2c84ec1304f450419941054544f5951644582dd9706725449d17015058453931a80504e655309e1003f1318e0541381313444c6565434025c60132088c580158310604c09d1109b8504131505a45c20194104c500700705b04c5421513ea58342141
  | 20 => 0x5d2504209321d8585369718105c2e01313988c1b61202a444164d535e20806e95055d544eb94190ccc172953302544fc1511ce0c83f161216440511610564c8411508d64c70d2300d2540511516bc541fb95113054c341508d4500e59507ba4c04c13245c586ba96162ccc1eb151c205804784111c1049d12037c442038301325015b151010cc8033324c05c52f97157e5cd761324b6502e816170ec844f17078c1804404043a4c6ad0705ce1c53d871
  | 21 => 0x4a85846e1422dc5cebe932be0504471428d658cdf17089e580c3b307ba541659305165854516159e484e71412aa4c66e9602e25855f9537ac5c55e17064a4c62096150a542a31321524c1641710925ccea9213804c3111603ae5867016162e5023e031616505409415005051714181a5c1981411445c5610712a45044c16310ecc552973802546533219a41c08105190d50ad715081a5417b94129258d779735f45c020941782c84749325e458172141
  | 22 => 0xd444c26a9419aa5841716309a5822f1708aa5c6a013148a58533c631bc5080b950684104aa96151650420931398cc4aa95106e5c1379624fe547552310da5898717388c5c1669429d45840394024c54cc4161bfc1015e1600cc5804297380258498342cd4101789730085093797256c50405162594485600104da545a61514a854409943aec1416212160c1c21d5205ca5ce209417a258625941d268c234130a0a50122941488545e01707b258efc850
  | 23 => 0xc41413d64c6433203104c46f87005a5c0be951261580b21538244c14817334a1455b1610884c51e15030f50cc355372a50d6fd206745cc2c9712005081215308a50a209515de4c97e1426d45c2341708245c201210
  | _ => 0
def P16_8 : ℕ → ℕ
  | 0 => 0x17dd04c45601d98848ed400101401e7601a658c2e71016f1c40d9401ba4c03cb70042588983200cd58c5d97017dcc4641700f60c86f97111488010b6000e100099410da5cc88e210c858067160099500321502255009b7501cc58065953079d4887b3001f5441d44021bd80641310cd10c21d211cc4c0ab16018ecc4d336105fcc87c130020540cb130012d049c5622a5d8c8d55321b8c4a11511d1884a116107b4848a14005fd000c9410875007f030
  | 1 => 0x11060058b50134200611731d1d80afe430d9d481596020188427180162dc06f150031540b9160089c8467130136200641501ad54ca96211c460c6bd702518849362102458c2262005854c339600e2100871500c85c0019402740c04e5501805c06c1830445409c76018edc84bd61083d0460f5103ad045d9731ba4c4dba300bf50039730223cc02276516d1cc1e74331b100b1b701a454060f2128754c881602bfd045c932183d9467932234cc05ed70
  | 2 => 0x564c81c5430504c84bc501e85008f9500285009b61014e4c033332201d08131732f64c0ce1320464c8397640f518021021366d407116312dd9419d3108e0c81116300358c8b940079d00b21632c85cc1f9320b9d8833930183d04afe65303cc09be2126fd00bf9503531005097000e0c0199401b058cb283021bd402a1800b9d84369302bc54caf17303d4c43976316f5c05f7301af580937500de500a13411a45c0d213010854040e500e590067931
  | 3 => 0x87540405700f35803a7650d9d902515111c50858b40288cc0a236005f50804b511564c4a1351284d84397650645cc767500b9840c8350251d90bc9402f26008a13008a540183620b20c0731502d45004ba701725cc4a9302155c4767512da1008ed530de5c05b54314e5cc2647205fd84019211160c44ed4013f5c09214105c60c88f6514c4c81e61028a5800f23012c8805ab713355c02e74017dd801e9301d9d0440f420e5d00441401425cc44160
  | 4 => 0x41580078202b618040f62054c80091300a858005d511c60c0cb83017254c8e5711f8580105702ea54060d3214e58c2fd500871045393105a6001a87014c58c807540e5cc404d63303d8021d3114c54c3975418d1808d1702ac54040f540311002716031b1801cc20079c8426531162480509530d9c84c0e65301980d9d70060d485093215c60c3d4500b9c805e92007e5cc1c5400584c84f05130c1404415009a5804eb501726009605111e4c05e152
  | 5 => 0xf25c02e76000cd04cd54001258407c20251d04807300e654c5598317e5c05615018ed486993116ad44d69401885c032970223d442b0300ca5cc2796019c60035173103d0c1198314e4c80ec731965cc34932055580531731904c82f531017144571630905808b95015c54c947630965402f13107e4c490170101540329630315805096326d884b456005c4c036620089d8c8f930002cc8559733464c493880223d8c8514015658cc62301e84c090150
  | 6 => 0x17e580c29300cc5843a4200fb1000b34103a5446495024dd9090140079d40b1d60028148a413005f8840336118c1000995018e588621500bd0807f8300144c0d6030103d942275118c900c0f533464c80d32121f5c02c94127a20000b61014148807531e55480cd52034580489801ef18091d400285c03c1321d1cc02e74115c5cc859801ba60c0097113b5c054d402ea5c018d7317d990db13233a504ce96128c4c08d52114758003351016dc064970
  | 7 => 0xb25002e7520e58401eb6002ed44499401c01003495310c5806496008390c0b3512304c018d50031080119301e85c01d05016f584131600ca4c41033005a5c0461402b85040d1400680c0c0e313018c46216011d484da15117dd0c3a2400e5d8877970020cc0b1b3005fd90500300244c460f620670c86f1601ae4c03675305fd403823007110805b20056540081701724c04c1301865008e573082d800d12000e5403097004658c9a83017dcc815930
  | 8 => 0x898408d37032c500b00500e5880155501425402276012a200397501fa5c07bc400564c40115105054c2fd70055500131530f054c5b452223d90aff3017dd485f9502d24c05f740042d8877140103c847a0321d999448970214d006fb710444c860150182d401ca300629c0ab9401fc0c4009512475c011180271cc00f0200e650c870320ce5c0a70301d75c0937402d15001d25018f54021b3026fd8071932320d800514002a4c035163032d044fd53
  | 9 => 0x240dc0810402ce200599700da4c8691830e8cc41e7310a8540a31400a40c0b85732780c00f5422c51801cd430df5ccc0750240d409c753066d807c85123b484d6950020580069301d9d088f970183d8c27150201990ceb4133ad844b87006454c17f510b990040a2028020089570083d50339422bfcc837b300c60c0185412f650068840147084452302991001716305fcc475d4026fcc07475224dd04159400244c8091730becc04b56105fd50ce131
  | 10 => 0x33108183720f354017e601f6140227530fb540241402f24c0311310e58c8251712a5cc03a5611ea100ac1600286008d1600e5d8072932017504a315005c5cc171312571803ec70044580020812285401ca201555002273111c5881f9300ccd84747540e158457d3005a0c87683120f08417e542fc140159630565cc05c631265805c94005058c1417303d5c81e75104c58c131322145404613026dd00480301780c046160083cc40497104454c11173
  | 11 => 0x1a65cc4b5711be5440832102460020e6526454091d60042cc0960500bccc4131800decc41e66218f5049034019c5401995019a540238301d9d0c05c610b9d0c659630da4c42a14005850864163082d405a17000c5c4947300425400c55319a4c02d15026fd8c91c413278840c4520ce50058b3021c5001855009c5001e6501d1c8402930182d0005b4009e540bd03021f1040854303a5c4da351183d0c87d611d9c800844206a0c01916318e50819183
  | 12 => 0x1985007296302a1009475326450015970260dc0a60702c75402296012f5c8265520e5d440c0200d44c03497309e500279700ec148bd9500cc5044554324754000b4103154460f5201f5ccb003010e1005f6101f22002f4302581800b971254d843a93002c5c4241500905c042130089980109200280c8403301ba58c0194207b5005f72103150809140327d8007d531a458c3b0402ae5407c1800041400ed5324dd8c6b120201d482e76423454075420
  | 13 => 0xe008088f310926001e73206050828030103d80984510125047e960028540991701de540d39501865800835016d5049b720214d4058b521be584d5c4014754483d5121bd9084d500351086d9600d9d84700300315880a94212e9000c4610b98848d1402a5d001cc3004a600a25700b9d4c4e36001f5c487d500720c0a3950082d00121710d9d80531301a81409237109a54017f631ea9005bb3021bd00251611555c40f98010850011931083d482e665
  | 14 => 0xbc8809bf64153484a646007e5401ed50271d505ed5003a5041f1401ac5c0a25400ca600767210ec0c81c5411260c436730089d849373021c4c0881420544801f180301d0c4583006c5002393019e4c00c951251d5007d623440c07474312e1006f1802286001cd4024dd502898031a1c01055018ed8895c5013b4846bd4005f8c4331510cc5c4d2940201d005bb5006c60020f6119a5c04b541082c80000401264c07a15015f4841ed51271d4840f52
  | 15 => 0x1564c036750089d00254433120c08f960301d809bf31066d00368800ce6003494026dc845892132c5406f1703464c02595217dd0816163201c84226310f354c1c4511ac540b437002460c75d5004c5404b55307208057952089d081f1300d90c83cd400245802fd600c4600489502205c06b3700f64c0a3940261584b515006c14c4737200a1008d3600e950c061301dc54017f301945084e540004500227413060c045551251cc418521082cc01e631
  | 16 => 0x4c4c08075017dd5066940017588589400c8600584400899046503016854046170327cc02642005660c9483016a5c492341103d00141830ca4c03675115558013183098080795501865406993007e58c239423355407683018358831163299140ac14004460c8617005fc804e57003e10ca39301551448d35013f5801e63029e1401e9600205003b0301764c05c03036c4c07e95007b08064130271d007674024210005d4318ad40579421acd4033341
  | 17 => 0x42d0010540079d8838841251d4860f53103cc83675424dd486b4410ded803663104c5c08d34007c540258310404c06fb20031d942f0200611001e6531d9d8c20e6321bcc01d930079d508815015e588333510ccdc4738300735481e6210e9548169500275d04bc6005fc4020e4106c58087d400c460c771801424c0369630445001618307990c58962064200439321accc00f5530f2c802e750115588366640125440656405c4c825351260d8085170
  | 18 => 0x1085803395026fd4820f42089d40d2950018100cd4711e20c05b2201d18400c47316f5003c9201a64c8379302464c007d521015008516027c0c05a16016850020f5318ed0860b600585cc661600664c03e150083c8407d42089944084730e958c1e620183d501e7611a0200227521eb1c0510300d9d008f94026dd94226633360c037b500245405014224058062930083d943e1800e58841f98303d54495840079cc04715208c4c0289503384c022621
  | 19 => 0xb9c8495c7011e508629602025c0d316126dd88729311864c02f542260cc0c074208a500050300d25406fd730e590457b420b998c2c08034a4c0ac36023b5c0701500d44c47c1501bed449475021bd080f4520b990405b60012d84d69300d990437b200995cc00b710c05080983005fd045a951163484405602255c8c9f501dc5c04ed600875c0340800b98c088f4001e88086f431038c4091701ba4c83116005fc841cd51260d40b14401a44c413140
  | 20 => 0x2165801c22033c0c0083312989c088f500d994c396311d1d908d4730c25802894010394c227320384c00837006c540ca0501a44c007c7203ad449b751075580366210614c4338322238c83cc30083cc8a29501d6cc0269301af540249700b9d08c4570223d8005d6112d5082fc710ec5441e710180600c9f401985c06615017dd402694024410020f43271d40806100731085ed602a2580300800025840103021b88431930089cc0a2930079d0460b10
  | 21 => 0x10390c329600c45401ed611d1d00854612d45801693029454036763214cc0946321865c0840322285801b17036c500c45501564c86fb611f05002495020808040d5220254057b5215ed883113030c200ae3410d9d9481830032c80396511470c40c54305fd4c1a9301e00c01834214a144397530751c01cc710c26001e76301c2006393107c58038542162d0858b620e5988459510b94c874750089d0c6714022e4c04fb201b6540983401b65c085370
  | 22 => 0x1d9d48033710434841c552271900ab1301764c48615026f8c86b340214d80201302474841117001a2001ed7021bcc4aca30082c4063c400bc884bb9501d1d88349801140805c96315354003151032d4457c510b9d4440e6300c504c6c5017660c1887023b5402e75433558042180103d901c55011a5001e75314750040e2126158862b302351043b0501d9d806b14007c5c0b51300f85c000b5116d5084615005f8800214004350c1ec410a258044130
  | 23 => 0x20f584aff400b9d940a1600b98800bb711e04c0a1d700e5d080b37118ad0062b60251d802583018394c0d3200465cc7383120c0c06b1600735049c5410d9d0c34960240d80397321eb1804fd501844c40b1411b24c018c4011c1c05314004a5c05205008990036732020d80031610221409b76028a600747411844c837b40066dc0903300c2540060530c45c00f220042dc80f97013c1407673026fd4017f6014708005d731f2140b454334e4c00d360
  | 24 => 0x3485407314003e5801185007e500a294008a5c01d54117650010b5211a5c040f510dd10005d7105f90080760048dc4795620d01c04fd40031504731802644c01094024a0c01815211250825371103d0486e6504a5801295021f580c0f4002e54421d5102c5443795010c54086160218500b4950182cc04b563016cc00d340089d90500501acd800f9500410804b02021e4c02e763246cc095a4003e50004b710de5806113026dd9040f50251d0086e40
  | 25 => 0x54dc0ba96007e5803594013954805b500761441e72017658c5ed402ae4c05317017d8c04695004318c265710fb58017f622fc0c04b5701dc580aff6003d5882275411d4c4c9f532bfd402e5312255402e7300799803a541066d408e5500dedc03792005a5005893005a580509403115006016034e5004734204a500269700e14c4c0f50301d00b29512a590ccc0400131ccb1d7117d880570800d65801b93003adc4ba98026154cd9d4024dd803c163
  | 26 => 0x14c5405f980094d845f7610308809c621083948895601d2100bb03007e6005c960083d90029420ca500795430550c08ed6021bd4cc6a7005fd080094118458c62c320614c01e74225458470151103d4c60e4312d5444ec2017dd8860f64103d8c131411839488eb2005fd0c9c6651d1d8c05d530566005f650284504ab1400a04c86613018398c5f7532a550494d751e25088532017d884948322bf8842b82126dcc0ac34007e5c0807630e95c08d551
  | 27 => 0x3676205f84018162083d88c0e21301884265422c0508b82202620c0085533485003117303158c2fd510f3504b4940014504771300141402e65211e1005d9600b40c02276205fd94946101585c0cc8300645042c8501d510855550098880c07302165409217115358072930063580299302c714440f301284c00a130
  | _ => 0
def P16_9 : ℕ → ℕ
  | 0 => 0x1390c046530211000695000f9800254000158802552005d4403e4100bd4c02774008884037710015c00354200c5c0037760079d004f3100d94c01c50005d0003752005dc0036610118c405b5000ddcc0363201310403c4000f88407d6101ad0000f6100994007430012cc001561016d0005b30001d8401675011d8c03643003cc0014310074c804770015d4803f610209c00177601ad8005740007d0c05b60009d440863001590001775018cc002f71
  | 1 => 0xbd000174200158005651003d440157000b1c004f61001d4401773003cc400d31013c8405970001cc4005310110c00557000dd900615001594004f750139040575000b9d40337001394c05631007d8c036740018c00477100118000532001dd404950015d8004776021dd403f72011d0002f75011d8004632011d0803f7601198401f6400390403e5101190c02d3200fd4c0636000f98800621007dcc0173100f8c40617001110000f4000e0c001762
  | 2 => 0x59000693002114000f630179d002e700179440076301118001551018d00016410079000077400d0c80255000d54805f72001dc800e30017dd8024500071c004640017d4c05e6200f90004730011508027630178c40577301114003f5001518001c40003d8008760009d080577200f5c000d51007d0801f520039d803f4101598405764009d0406d520158c80067600bd500253100390005e410159c00564101dd800065400b8c00275001a5c002c30
  | 3 => 0x1dd800f540059c800e6100bcc001f5100fdc0006530015000075200b4c000e4300198405552007d4c047540018c80166500fd0c069600091000254201fd8406130005d9000643019d900277001ddd006f71005d4801743012d4002630019dcc03f710098c807776009dc406f720210c00543001dd0001730019dd80667402194001f4001bd90066510119d401e65019d4802f730038c4066630134c400d300008840063100f9d005f640201c004630
  | 4 => 0x7cc000743001dc000753007cc80163000bd840494001654006160011dcc02f5200bcc401643007dd803a3002190001e30016dc003f400054c00637000fd9005940021d0005930009d9006b5001510001732001d04004300099d8046600151c001542005d8001440007dc0017710099d00577001f9000265400b90001c3001658001e7200b1000567500c54002e410079040243000398000f710035c402753001dc405571003dd80273101d8c006940
  | 5 => 0x994401f75001d880275200998c0764000d95001f72009884047650158c001d30007d4001e31007d840155200794802f320119400475001598001e630019d001470021d4005771007dd00375100f140015600099040177400c4c00373100198006b70009d000177200f58400c3000790c01663005d8402640005908049300058c406f5200fd80007730098c400d6000f94002e72018d4006e7500794c0165300b99400c4000754403350009d8401750
  | 6 => 0xb5c40363100cd000336000318001f310054c802f72001d5002f6000b98c02f6400154002e2100754001e500119d804b4000b90c03e7600dd8c00f4300dd080073201acc00175300ccc003743005d8c03c60001d9001670003dd002e53001d940573001850001e7001dcc001472001d0801d420055400157100fd4803d52009dcc01430009dd80873000d9d802e31003d900076000c50003160
  | _ => 0
def P16_10 : ℕ → ℕ
  | 0 => 0x761001d9400742001944006200018400075000199400741001c4000621001d4400720001d8800752001cc400721
  | _ => 0
def P16 : ℕ → ℕ → ℕ | 5 => P16_5 | 6 => P16_6 | 7 => P16_7 | 8 => P16_8 | 9 => P16_9 | 10 => P16_10 | _ => fun _ => 0
def Z16 (s i : ℕ) : Bool := barV3 7 9 (SgenB 11 x16 o16 P16) N16 (idxGenB N16 H16) o16 s i
theorem l16_5 : ∀ i, 0 ≤ i → i < N16 5 → Z16 5 i = true := span_end 25 0 (by decide +kernel) (le_refl _)
theorem c16_6_0 : span (Z16 6) 128 0 = true := by decide +kernel
theorem c16_6_1 : span (Z16 6) 128 128 = true := by decide +kernel
theorem c16_6_2 : span (Z16 6) 83 256 = true := by decide +kernel
theorem l16_6 : ∀ i, 0 ≤ i → i < N16 6 → Z16 6 i = true :=
  span_step 128 0 c16_6_0 <| span_step 128 128 c16_6_1 <| span_end 83 256 c16_6_2 (le_refl _)
theorem c16_7_0 : span (Z16 7) 128 0 = true := by decide +kernel
theorem c16_7_1 : span (Z16 7) 128 128 = true := by decide +kernel
theorem c16_7_2 : span (Z16 7) 128 256 = true := by decide +kernel
theorem c16_7_3 : span (Z16 7) 128 384 = true := by decide +kernel
theorem c16_7_4 : span (Z16 7) 128 512 = true := by decide +kernel
theorem c16_7_5 : span (Z16 7) 128 640 = true := by decide +kernel
theorem c16_7_6 : span (Z16 7) 128 768 = true := by decide +kernel
theorem c16_7_7 : span (Z16 7) 128 896 = true := by decide +kernel
theorem c16_7_8 : span (Z16 7) 128 1024 = true := by decide +kernel
theorem c16_7_9 : span (Z16 7) 128 1152 = true := by decide +kernel
theorem c16_7_10 : span (Z16 7) 128 1280 = true := by decide +kernel
theorem c16_7_11 : span (Z16 7) 95 1408 = true := by decide +kernel
theorem l16_7 : ∀ i, 0 ≤ i → i < N16 7 → Z16 7 i = true :=
  span_step 128 0 c16_7_0 <| span_step 128 128 c16_7_1 <| span_step 128 256 c16_7_2 <| span_step 128 384 c16_7_3 <| span_step 128 512 c16_7_4 <| span_step 128 640 c16_7_5 <| span_step 128 768 c16_7_6 <| span_step 128 896 c16_7_7 <| span_step 128 1024 c16_7_8 <| span_step 128 1152 c16_7_9 <| span_step 128 1280 c16_7_10 <| span_end 95 1408 c16_7_11 (le_refl _)
theorem c16_8_0 : span (Z16 8) 96 0 = true := by decide +kernel
theorem c16_8_1 : span (Z16 8) 96 96 = true := by decide +kernel
theorem c16_8_2 : span (Z16 8) 96 192 = true := by decide +kernel
theorem c16_8_3 : span (Z16 8) 96 288 = true := by decide +kernel
theorem c16_8_4 : span (Z16 8) 96 384 = true := by decide +kernel
theorem c16_8_5 : span (Z16 8) 96 480 = true := by decide +kernel
theorem c16_8_6 : span (Z16 8) 96 576 = true := by decide +kernel
theorem c16_8_7 : span (Z16 8) 96 672 = true := by decide +kernel
theorem c16_8_8 : span (Z16 8) 96 768 = true := by decide +kernel
theorem c16_8_9 : span (Z16 8) 96 864 = true := by decide +kernel
theorem c16_8_10 : span (Z16 8) 96 960 = true := by decide +kernel
theorem c16_8_11 : span (Z16 8) 96 1056 = true := by decide +kernel
theorem c16_8_12 : span (Z16 8) 96 1152 = true := by decide +kernel
theorem c16_8_13 : span (Z16 8) 96 1248 = true := by decide +kernel
theorem c16_8_14 : span (Z16 8) 96 1344 = true := by decide +kernel
theorem c16_8_15 : span (Z16 8) 96 1440 = true := by decide +kernel
theorem c16_8_16 : span (Z16 8) 96 1536 = true := by decide +kernel
theorem c16_8_17 : span (Z16 8) 96 1632 = true := by decide +kernel
theorem c16_8_18 : span (Z16 8) 45 1728 = true := by decide +kernel
theorem l16_8 : ∀ i, 0 ≤ i → i < N16 8 → Z16 8 i = true :=
  span_step 96 0 c16_8_0 <| span_step 96 96 c16_8_1 <| span_step 96 192 c16_8_2 <| span_step 96 288 c16_8_3 <| span_step 96 384 c16_8_4 <| span_step 96 480 c16_8_5 <| span_step 96 576 c16_8_6 <| span_step 96 672 c16_8_7 <| span_step 96 768 c16_8_8 <| span_step 96 864 c16_8_9 <| span_step 96 960 c16_8_10 <| span_step 96 1056 c16_8_11 <| span_step 96 1152 c16_8_12 <| span_step 96 1248 c16_8_13 <| span_step 96 1344 c16_8_14 <| span_step 96 1440 c16_8_15 <| span_step 96 1536 c16_8_16 <| span_step 96 1632 c16_8_17 <| span_end 45 1728 c16_8_18 (le_refl _)
theorem c16_9_0 : span (Z16 9) 96 0 = true := by decide +kernel
theorem c16_9_1 : span (Z16 9) 96 96 = true := by decide +kernel
theorem c16_9_2 : span (Z16 9) 96 192 = true := by decide +kernel
theorem c16_9_3 : span (Z16 9) 96 288 = true := by decide +kernel
theorem c16_9_4 : span (Z16 9) 56 384 = true := by decide +kernel
theorem l16_9 : ∀ i, 0 ≤ i → i < N16 9 → Z16 9 i = true :=
  span_step 96 0 c16_9_0 <| span_step 96 96 c16_9_1 <| span_step 96 192 c16_9_2 <| span_step 96 288 c16_9_3 <| span_end 56 384 c16_9_4 (le_refl _)
theorem l16_10 : ∀ i, 0 ≤ i → i < N16 10 → Z16 10 i = true := span_end 17 0 (by decide +kernel) (le_refl _)
theorem l16_11 : ∀ i, 0 ≤ i → i < N16 11 → Z16 11 i = true := span_end 1 0 (by decide +kernel) (le_refl _)
theorem base_n7_070 : ∀ s, HasMonoSize 7 (gfn [] edges_n7_070) s → 12 ≤ s :=
  prove_base_mono (M := 7) (E := 9) (cap := 11) r16 x16 (gfn [] edges_n7_070)
    (SgenB 11 x16 o16 P16) N16 (idxGenB N16 H16) o16
    (by decide) ho16 rfl (by decide) rfl (by decide +kernel) rfl (by decide +kernel) (
    all_step l16_11 <| all_step l16_10 <| all_step l16_9 <| all_step l16_8 <| all_step l16_7 <| all_step l16_6 <| all_step l16_5 <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_zero lvl_empty)

def edges_n7_071 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,2),(1,4),(2,5),(3,6),(4,6),(5,6)]
def r17 : List ℕ := [28,42,49,56,65,66,68,3,5,9,6,18,36,72,80,96]
def x17 : List ℕ := [916,3234,5441,8715,18445,36878,57456]
def p17 (pi w : ℕ) : ℕ := match pi with
  | 0 => ((w &&& 0x9142) >>> 1) ||| ((w &&& 0x261c) ||| ((w &&& 0x48a1) <<< 1))
  | 1 => ((w &&& 0xc00) >>> 2) ||| (((w &&& 0x4024) >>> 1) ||| ((w &&& 0x90c9) ||| (((w &&& 0x2012) <<< 1) ||| ((w &&& 0x300) <<< 2))))
  | 2 => ((w &&& 0x1000) >>> 3) ||| (((w &&& 0x8440) >>> 2) ||| (((w &&& 0x106) >>> 1) ||| ((w &&& 0x8) ||| (((w &&& 0x6830) <<< 1) ||| (((w &&& 0x201) <<< 2) ||| ((w &&& 0x80) <<< 3))))))
  | 3 => ((w &&& 0x400) >>> 3) ||| (((w &&& 0x804) >>> 2) ||| (((w &&& 0xd060) >>> 1) ||| ((w &&& 0x8) ||| (((w &&& 0x83) <<< 1) ||| (((w &&& 0x2110) <<< 2) ||| ((w &&& 0x200) <<< 3))))))
  | 4 => ((w &&& 0x1400) >>> 3) ||| (((w &&& 0x8044) >>> 2) ||| ((w &&& 0x492a) ||| (((w &&& 0x2011) <<< 2) ||| ((w &&& 0x280) <<< 3))))
  | _ => w
theorem vp17 : ∀ pi, ValidPerm 7 9 (p17 pi)
  | 0 => validPerm_of_spec 7 9 (p17 0) [(0x9142,2,1),(0x261c,0,0),(0x48a1,1,1)] [1,0,2,3,4,6,5,8,7,9,10,12,11,13,15,14] (fun _ => rfl) (by decide +kernel)
  | 1 => validPerm_of_spec 7 9 (p17 1) [(0xc00,2,2),(0x4024,2,1),(0x90c9,0,0),(0x2012,1,1),(0x300,1,2)] [0,2,1,3,5,4,6,7,10,11,8,9,12,14,13,15] (fun _ => rfl) (by decide +kernel)
  | 2 => validPerm_of_spec 7 9 (p17 2) [(0x1000,2,3),(0x8440,2,2),(0x106,2,1),(0x8,0,0),(0x6830,1,1),(0x201,1,2),(0x80,1,3)] [1,2,0,3,6,4,5,8,10,12,7,9,11,15,13,14] (fun _ => rfl) (by decide +kernel)
  | 3 => validPerm_of_spec 7 9 (p17 3) [(0x400,2,3),(0x804,2,2),(0xd060,2,1),(0x8,0,0),(0x83,1,1),(0x2110,1,2),(0x200,1,3)] [2,0,1,3,5,6,4,10,7,11,8,12,9,14,15,13] (fun _ => rfl) (by decide +kernel)
  | 4 => validPerm_of_spec 7 9 (p17 4) [(0x1400,2,3),(0x8044,2,2),(0x492a,0,0),(0x2011,1,2),(0x280,1,3)] [2,1,0,3,6,5,4,10,8,12,7,11,9,15,14,13] (fun _ => rfl) (by decide +kernel)
  | _ + 5 => validPerm_id 7 9
def o17 : List ℕ → List ℕ := oriStages p17 [[0,1,2,3,4]]
theorem ho17 : ∀ k l, (∀ w ∈ l, w < 2 ^ (7 + 9)) → DLive 7 9 k l.toFinset → DLive 7 9 k (o17 l).toFinset := fun _ _ hlt h => oriStages_dlive vp17 hlt h
def N17 : ℕ → ℕ | 6 => 74 | 7 => 471 | 8 => 640 | 9 => 177 | 10 => 9 | 11 => 1 | _ => 0
def H17_6 : ℕ → ℕ
  | 0 => 0xeb268e91c4e827de581bd7f20d2154c9189c8d6bc678bc2647be1ddb137dac43ba46fba11689f10c9ebae9abda8f5b78da158b1b88a91387eb184395829357f36975331733d46b727683e765e85609635ee465831757cd95457c50a734bb7546128440bf3882f3797336f7c35f1335eda319b82f98e2ecad2be6b2967822f541ebda1cb711afc61946316a711563f147f513eae109010fbb90e7e4048720078f
  | 1 => 0xfad72f769af7661f313ff17d7ee175edb8aed16becae6eca1b
  | _ => 0
def H17_7 : ℕ → ℕ
  | 0 => 0x2197d212d120bc420b24209a12004d1ffe71decd1d7d51d22c1ce4e1c58a1c0041a2e519f6519463183e217f1117a3c1750316114159a5153f7143f512a69129951268b11bf21197510d370fdcf0f3100ef930ee790ecb20e6fe0db500d5320ca860bc250bb140b3950a67709ffc09b6208be208b2d083da082d9062c805d93048f0046180405f03eb6035320328d026e301c6301a690175f00d4c006e600386
  | 1 => 0x494d74933e482a1478f94735c469e84615745c3643ed641b7841498410223f3bf3f1ef3ef5c3e8063e0873dfaf3cf533c3f53b66f3b3fd3af2c37f13379383756d375183750936fcc36db236a69361d535c7233c1e3375c31a50319553176531687301672fc322f5a42e5d72de5e2dbe62d1d02cec62c21d2ba822ba592b5722a6b628b1327fa127e9c27db127c54272c1262292585024d2123de122abd21c13
  | 2 => 0x68124680eb6806d67feb6740a6669d65e8565c236544265346651b1650da650c364fe664ebe6358e632736221161d0f613a0608db6045b600805e5955e0175be2458d8d58b5b588c257feb57dca5766c5758b561b755eaa554f45542c550d054ffa54b2953f9053c6d5338452cd9524795200c50f5450a4c4fba84fb224fa174f8d24eeec4ec1a4eb4c4d6244d3454cfa04cbdd4aef84a9764a17b4a11f49fb3
  | 3 => 0x89eea89d1f89c2689a838922488ecd88d85883eb8816887fd287eb187843874a6864d08648785d2384935843bb83cf883b5a839658368d82e898295f826a181a6b8142e7f9327f4617f07c7ef427e1c07d2aa7cf0f7bf157b8a97b1847ae207a8bb799ab793f478eb878595772ed76d3f7665f75b9a7584274a57730f672b9770a7b703de6e4a86d4156cfe86ca086c5e56bf4c6a81b69e3069b086979369508
  | 4 => 0xad1a6acb95acacbabf16a845fa83faa830ca6e5da699aa6961a6953a6861a6834a6557a5a2ea5904a5224a4c03a4b9ea3c0aa38afa2ee3a2214a1bb3a1b7ca1a1da11b8a0f36a0bb1a0952a05859ff869fc169f5e09f29a9f1519dfb89dafd9c2409a67e98ba197c599757a971ee96e5c969bc960e49360a934989347f92eb9929c59235a91fb79169490dde8f3608f0368e33b8c6ff8c1188b3078b0068abfa
  | 5 => 0xd40e3d3e1bd370ed2d47d1f53cff0acfc00cf4aace5b0cd14ecba1ecb145cafd1c9ffbc88f0c8760c8587c7ffec6febc68fbc591cc4f3ec4a14c4386c3af8c300bc2c13c2483c22b5c20fdc1fb2c11d5c0599c00c1bf498becd1be496be0eabdaf8bd71ebd5eebd027bca36bb2abbb01dbabcdb9002b8d1ab8849b86dfb63abb422db300bb2047b1b16b1356b0f3cb0852b04a1afb30aee9fae139adf2ead239
  | 6 => 0xf53a5f5207f4d46f478df3f4cf313ff2e89f2a77f2a45f2844f25b8f17d7f1575efdf0efde8efd55efcf0ef908ef7beeefc5ee957edb9cecda1ebc96ea069e93dbe77d4e76a1e75e4e6cd5e6b55e43bfe4334e4244e25bbe1e87e0fbee0215dfcbfdecc8dec74dea35de5fbdcbacdc50fdbeb2dbb0adb5dadab12da7e8d9cd3d9af1d970dd8bb5d84afd7d29d7c32d793cd7271d6cabd5858d575ad4ba1d411c
  | 7 => 0xff727fee0ffd9ecfd98dfccc5fbff0fbb57fb167fad72f9d55f9744f9503f8fe6f8f77f8a33f7bdbf7661f73e7f7137f6d4af5ee2f58abf55af
  | _ => 0
def H17_8 : ℕ → ℕ
  | 0 => 0x17f1117d5a1782b1770e171e316c77165da15be0153f71524214aea14446143f512eb0129951276e11fc311e7211e1d11bbc1118c108b7101bf0feff0fbe90facc0f1750e1e70dfe20de1f0db500c1f20bdc80b3f70aa540a6770a2dc09f2408d7708c6b08a9d08a1b0879807adb071730711106c5306472062c8062b70581105218052060507904ea6036600353b02c23024b70151601262006e60036500318
  | 1 => 0x3120230ed830a852fe612fc322f4a12e54f2d8332d5892d1d02cdba2c6832c4c42c4a22bb9b2b69a2a6ec2988928fa82840827db127c6727c06277b52730b26cca262292614a251ef2517324f1124b52245f723bf223b48235a1234a6226f221c002197d215e12034f1ff4e1fd4c1fbf11e77c1ddbd1d4211d23d1c9711c8201c75f1bd511bacc1b1ae1b0941acd21a3061a2e519c1c197e318d9318b07183e2
  | 2 => 0x4b8b14afa14adff48efa475fa4715846fe646d4546ccf46b4e4698146464461c245fc34531a453084414444061437aa4319242c0c415c2414f5412784123540ee840e5b40d4f40d05404513ffcc3f77a3ee043ed5a3d5393d4163d2053b7893aaf73aaca3a6fa39671391a038e96383173814f37fce374e436fcc36b1736a8c361df358b5353773523235097347913419933aaf3244031cb331a1e316de3131d
  | 3 => 0x6566c6564b64fbf64e3c64cee64ace643cd63b7e63735635b76326362bad62aaf6282161ef7613a0609fd608db607fe6045b5f23b5df415d6c25d4545d3a95c8095b2d05afd55abba5937759022584bb583f05825b573dc568695656f563a9560eb55fc455a5955889554f454a4b5426553fcf5393252fba52c4c5298750f8c50cda4f4bf4efe94ec514eb4c4e9c94e4764d9904d79a4ca5d4c7534c5624bddb
  | 4 => 0x810ff810e7805407fe4d7f6a57f57b7ef4e7e2747e1c07ddf27da667d7a97d27b7cd207bf8c7ad317a09079d097918f785957814f77b5c776637703975abd75737754c1754207502374d187435a73edf73c0d72cf67258a71e70718997178870fd770be4702946fc4d6f2866e55a6e5586e3f76de776d2f76d1c26d02d6bb186b0df69fe569911690e1680eb67feb67d5067cc56790d675ac6724c671e066981
  | 5 => 0x97c01979ec9757a971ee970b396e5c9663a964719631d9604495fdf95f9495eec95ac195120949ef92db692c8e91fb791e9291bf5916949123a906448f3608f0528e7978de048db098d7478d67d8ccec8bdee8b8128b5a08b5948b1648ad518aafa89fb489eea89db5898d88927a8922488f8b88aea88157876af87392872bc8716f8716d871418582e852e5851e584cda83caf8368d82fcc827838262f82170
  | 6 => 0xb4dc9b4abfb369db2d25b2a8fb2047b12f5af69caf398aeebaaec9faeb1fae9ccae7c1ae3a4ae16dad66fad113acd1dac3adabf16abda7ab0afa9a98a9828a96b7a9288a8e70a8d9ba8ac2a845fa826ca5f3ea5903a574ba49c6a4464a399fa2d37a236ba21eca20a5a16dda140ea11b89f5979f4689f29a9e9ac9e9a29e6369d59e9cd4e9cb379c70b9c42c9b68c9b4669b0049a19b9a14899e549808c97c04
  | 7 => 0xd1424d1100cf655cf4aaceebaceb7ece028cdc68cd172ccf91ccf81cc422cb9a8c9c92c9be9c975dc8a54c8a0ac8625c8587c8141c7c4dc7ac5c7857c7597c6fcdc6b06c6800c63a7c61e0c591cc4e59c4a14c3ee9c3253c1fb2c13a4c1284c0bdcc072ac0599c0529bf03dbecd1bdd70bdcd7bd821bd3cdbd0fcbd097bd027bcd07ba4a5b9f61b9ac1b9256b8b65b86dfb8357b7a3bb72acb694bb5971b5834
  | 8 => 0xe727ce6b9ee6853e61cae60eae6088e50c5e43bfe4244e422ce3c2fe362ae2eabe1c77e198be17d2e12dce0dd7e091ce04d0e04bbdfeabdfbffdf840df694df544df4e6ded5dde9c2de87ade150dd977dd4d9dd3bcdcfabdcdc6dc034dbabfdb997db4f9da6dfda689d9f8fd9e8fd9c05d9698d8e7bd8d1ed6c36d617bd5cead5c3cd5b7bd52d1d4cbdd4758d42fcd411cd3e84d3443d3244d31f5d311bd2cba
  | 9 => 0xff910fe897fe37ffe258fd8b3fd5a9fc5f7fbd8efacedfa5eff9d97f9685f9621f8fe6f8cfef8c4cf8c09f8468f8450f7d3cf79a4f71b7f69caf6683f65bff5dbff53abf53a5f5207f50e5f4ec4f485ef3ebef335ef2cc9f2252efcf0ee957ee2f5ee1fbee071ede3ded024ecfb2ebeefebe77ebc6aebc17eba04eb523eb383eaff4ea7b1ea275ea25fe93dbe8d18e8917e8863e8695e85a3e83a5e7ff8e75e4
  | _ => 0
def H17_9 : ℕ → ℕ
  | 0 => 0x55831549e3531d652fba51cab51aac512ab4e4d84c5624b7fc4adaa4a47a49cf14838247272469814564a4544b41b763fb0f3f96c3f86a3d9ee3d8a83ac113a0b0375e736fcc33e1b31f0731a1e30ee42f4762d8332c3262bb9b2bb8b27c06266aa2544e2339b22ccc1fbf11da7a1cd081c30617f11171e31666b1475411eab115400facc0f95c0e2a60cade080f30717307136059ee02a9b0210400e97006e6
  | 1 => 0xb2ba9b12f5aec9fabda7ab09fa845fa6571a31faa0b3f9e9e99d67f9bc499a9a394c8292c8e916949153a904718eb138e8028e6038cde28ca4f8ae9089ca9898d8873e186cee863ba853fd83dc982fc280eb5809e28028a8008b7fe4d7cac07a09477dc07739d758517384c7045f6f7056f27d6c7ce6ab2368ee367feb67d50666a3656d16237f61e92613a05bef85b1745afd55abbf5a4215a04258fad559ff
  | 2 => 0xfe1c8fd5a9fad83f8cfef7b55f6e7ff5ab5f4dbbf4833f3b89f15e8efe72ee957eb32ee8d18e8726e83f7e5e41e4244e422ce30c8df544de63eddbbddcdc6d9b3bd9b11d62a4d617bd4b50d411cd1fdad0700cdc68cd7c9c6800c55aac3253c0599c031abf56dbd5e2b9617b8f49b726bb5db1b5ae0b520cb4999
  | _ => 0
def H17_10 : ℕ → ℕ
  | 0 => 0xdfc05d35a4bf03d765534e4764b53f40d051c75f0e1e7
  | _ => 0
def H17 : ℕ → ℕ → ℕ | 6 => H17_6 | 7 => H17_7 | 8 => H17_8 | 9 => H17_9 | 10 => H17_10 | _ => fun _ => 0
def P17_6 : ℕ → ℕ
  | 0 => 0x1204c82815016a58c2a152286580321312c050013930392544139632605804a1600ba58477931048544061420d0584091310664c49216024e54c189100584849d14026e500159410944c42494036e5807e12017c5441614106c5803b8300d04c41f0501285404a9310a85885f9400e04c49d1500245049b9500564c412131242500139310485841993006658c1a95310654c1b15017c5842e93106a4c413953056544281600bc4c4769601660406e960
  | 1 => 0x18e5804193017c5040516003010857121048504059510f84403c962
  | _ => 0
def P17_7 : ℕ → ℕ
  | 0 => 0xa65405994118e4c4489400c65403d1410205804514110c54ca9a300345c08c8411f65c01d97009654c841610a6500261400ac5c025931210d04569500065c02e9301f65801d94019c504abb3104e584711320ac540d39701e85045c9511ac4c4901420680806a14101c5cc699601101807d1710265407b97103e58019d5104e504139510e80c46096009e4c4a09300085cc1284028c0c02e97001454c420513380c0071310cc5805c9611464c111170
  | 1 => 0x3e64c8c85321145c46c8633d25450f1612ca58c7091034a4c47096115a4c0969511b84c04915115a500dd5621185c07595306754ca193128a4c84b15112a580843612fb5442c3200cb18cbed530f04c0279511725041416018e4c0d5b20190d005e1512a8580cb95012850027971104540391711404c0581421a85444114021e504bec63128540b495204e4c4391611244c4a9d630344c0099400e454407163086504548701d65cca89520ce54c07130
  | 2 => 0x84c11bb301f654c1002016c0c4279412105452614127c200819600965404f96321454c811610b454007d523440c86431008c0c0631700580801317019c54432b3024a5005e1411245846b9711185810f1411405c00d9431c458cbb85104e5c4099701e44c47915112c4c44a94015c1006b961034540ea2301a65400c9313d65006f13023e500041301a64c0081501145444a160280480429611381003315018e4c848970008580639631a8440f4961
  | 3 => 0x46ed4035d612021c0520700204c0559611e65cc929700ee14133850210484205620a85844917111458521150210d44a09604b68c44b9511e4585051612121c02593032e5c06f14012254032d5312a5c0179404081003d0201ee58442951320840ef1320401406f17021e544111411d650d349510d25c07d93129a5447b94102858c9794039c4c93f8301c25c4c89501b85408b951252185140301fa0c80e56104a1804a1303225c0ee5211b85c10a951
  | 4 => 0x925047b9510c24c41fa1002c50019a2010c4c420551062880843211b0504b01611485c82796103a14020461272580aa1400815086b1711b45444d14105e5801bb203a21c0774420b8080dd210067548489603b9080cb9602c04c42a1510a65c0051732825407a13108e1c470941326d80c89300f05000b1200f0540209513bc54c4a17015a580ed1311724c4c9b10178584131501465c02c56204c50092960200140259201345450a9712a854079171
  | 5 => 0x1024c05f93000854c190211bc5809d1400505401316022a5c4a89420b14c85f9311f64c0141702825c0abb212761008a0503bc5cc331403545411797331250822d520924c4fd0402aed84205321565c4ef16307f4c43b220026480530300285ccd51700675088c1411424c46c1314445807b04101458c8a95101058cfd83011c5844b17112a5408317011c5446397317e58c609704165006f15005e4c037940100184141400b1184b614210a5c4cf030
  | 6 => 0x3e084d514000e144ad9510205c0ab93122c5800d1400d6840911320105cd1c150124504843311885047a17141c580644631785c4081400984c0461500c2544e39600085401d9500c04c0c21500d25809d1302b65c447c621184c00a8300b458010b3012e584431204aa1400c9710c25c44f9324305cc319600c058c7317124a5400d8102a7584509420284c44317043058cb095001c4c90a961138508a51710144c50c1430104c87914135c5c026160
  | 7 => 0x21630104c44d8401e85440213110c4c0379601345c51c1600a25049bc420ce58cb30203d8d0111150190d80841410c64c0501500c04c41182023810069970
  | _ => 0
def P17_8 : ℕ → ℕ
  | 0 => 0x5a08001b200d55002d142125884007100dc5404d5400205845855009184038d7006e5001b573020504141300e198c2496301e50c1b57107e4c0260301504c4386310524c43d621091cc01b4200255c820d41144180095520b1084218610795c00314001a5cc0ac410aa1c41c970108600048300615c010d521104c01e440001d043864106e5803097007e5cc2335100460c22d4209dcc430960086500009630e1cc408442149840398200d558001173
  | 1 => 0x3e580127620364c008e20042544095710e1c84411300124c0109410764c83494000a4c4083511184c045d700f58c827742049d5039d4100c5800f9501158840093001a1c03d6310f8584126200019805356006edc03b1600540c401d600400c05854004a4c0100310250840a95209d880094420a018026b7103a0c038730136c803ed601044c8119530024c801c300431083f4700e95040073111c4c83d7610205c4007600d0d802308005660c0a942
  | 2 => 0x11c20014183025080379730da5400097306ec80119830ae0c03497013b100499300d85cc359730f5c8457521039100277600019902383102ad4801d700255802dc40049d0049730125d401bd610fb0802c9600360c0126651105003a542049c8424750125d8c3097309dd9447c400f8d440ab4202394c3d6531265c0033400f59082207003c48005b610f5d001266412650041153001d443d762049cc44c4730f8dc43f953117500526210b80c016061
  | 3 => 0xd15c0535400a25001a8300f91cc4a36109dcc0141320de54c431830fb5000f3400fe1800f3600645cc2c0200d84c4469700d654c0597101a508551310ec4c045721020dc40ad2106150008e210664c0149400a21cc083610a24c012640115d80456500b71c03b1731061c030932020d040336000c5c0149830e91cc0076311c4c4021301504c0309830835c83d75007258047130034d843f0400ec5c01842002488020d51023cc4349501384c04dd43
  | 4 => 0x10e18c1c57000260c0713000a4c008e300018c40957311a580431630f58803d76304658c220710fc9003c1630499883c98306ed800d171049d0c38d3111e9400c983001cc00f970001904457500e1d002515006d4c4541320740c810b51001d841276009e1c01d83010c5cc3b131042d04238300525cc1276307c58c16b31008508390500c258c24930049c80334700f8d043614000d5c44f330024080006210324c01f18305c0c84db3003958017930
  | 5 => 0x6260c1118003c5000f1600fb5c00f1500e18401b57200a58c2784010850006983091cc83c1830b750c051301175803f450016544369400965c04d130091d8c431300165040ad7115ccc00c9310395c82c5400a64c0379320f5d804313204e4c82f03003cc8001d501355c008f4313cd4008f2012a4c02763003c5c04213003d48427763149d803c93106ed001c0300d84c00ab620835843c97301a58c08f500526004c16100cdc00695309194c0f441
  | 6 => 0x10c4c43d7310391c00074309dd901b9700304c04215009260c3d7320391400f9800624c83093010e0c01503003954c0ac700d15000ad510228401262109d988159300251c00d94102550c127610581c00495203c4c02305003258c5273009dd0c127300de5000856207e4c8139310b81403903004c0c03c17311e14038d400018c00a972023d483c93210450000721049d402773200754c527400cf1c00f4730f8d8408e430d2600051701085804d550
  | 7 => 0x23d8c38d5009d8c405961023cc04976001e5cc419301355803455012654012732094580094310be20c189630120c42463103d58c4e8700e31c405150016dc4149300146000285006254c128400255042b1800f85444974011a5404e1501451c008d310d24c0085520828c008f5300c4800ab7206c8803e17109460045b2002b5803c93004e5cc1495004e4c02b85004e58c1a0300044c81263004994c2697101254002973001d002774012658012631
  | 8 => 0x1175400493209d9044966211f1c0007540685081246215c480041300700c42464309dd40439500c510001d401385c0559300e1d801b5431564c425132034dc445730149d404f7210a80c016d430a20c808e521221cc3718005058c0f3700945002762107e4c410b2007e58c4e14003a5c00b173136d002776113dcc41b02013e1401b470069588246210018400954005b084183301449803095000458c1b920049c4024743091c402f83013a9c010151
  | 9 => 0xf5cc02f1310da4c02473100454c1413103ccc04db600945c00076404454000931016d44494310e18845837000d1844c3610564c42b1600505cc51440016d0445c51049d9420d530524c8242200f85042b15002c54c211420281c020d4001a4c834471128584019200dc5c01606000cc8027753049d9020a600e1980289500445c016d4102e140309400726000f3500681cc276431204c00815100e4c02765401e54c2493208c0c03a8300924c40d161
  | _ => 0
def P17_9 : ℕ → ℕ
  | 0 => 0x5dd80272100dd9402d3000bd8c01f510019c802f6400d1c000562001d9001f6300f98002772005d040343000bdd801f5200754401f30009d940076500399001764005dd0047530019c002130009d4803670002d0001f650019440043000d8c000550001d4c01330005d500074200bd8000f310095480077000bd00005520024c000b60003c8400732003d0803730004d0002e30001d8c03761001dc802c30003dd802f310011c000f61009d4c01160
  | 1 => 0x5dc40054000110002330001cc401140003d9000f62001d8000e54001d0c0053100150800775001140011700038c40064100199000f54003cc803c3000190c02c400014c80056000194003e30011cc00357100390c00632007dd803776001d04007730014c002f4100190001d52001dd80063100798002f7400994c0375000798c02f70001dc402150004d8003f6400b90000630005d8c0217000bd5000774002cc001f600078c003f620015c400750
  | 2 => 0x1c60001d4400c31004dc004670009d0c02d31005cc402775001d480447000bcc000940009cc4005700074c801f31001d000185000d58000e6200694001c30005c8402350001d8403f31001d88023700019d400960007d88016630074c0017730011c80373100f1800113000794401631007d0c00f4300ddc400676007cc8016410118c000730
  | _ => 0
def P17_10 : ℕ → ℕ
  | 0 => 0x730001d8c00743001c4000630001d800061000198c00740
  | _ => 0
def P17 : ℕ → ℕ → ℕ | 6 => P17_6 | 7 => P17_7 | 8 => P17_8 | 9 => P17_9 | 10 => P17_10 | _ => fun _ => 0
def Z17 (s i : ℕ) : Bool := barV3 7 9 (SgenB 11 x17 o17 P17) N17 (idxGenB N17 H17) o17 s i
theorem l17_6 : ∀ i, 0 ≤ i → i < N17 6 → Z17 6 i = true := span_end 74 0 (by decide +kernel) (le_refl _)
theorem c17_7_0 : span (Z17 7) 128 0 = true := by decide +kernel
theorem c17_7_1 : span (Z17 7) 128 128 = true := by decide +kernel
theorem c17_7_2 : span (Z17 7) 128 256 = true := by decide +kernel
theorem c17_7_3 : span (Z17 7) 87 384 = true := by decide +kernel
theorem l17_7 : ∀ i, 0 ≤ i → i < N17 7 → Z17 7 i = true :=
  span_step 128 0 c17_7_0 <| span_step 128 128 c17_7_1 <| span_step 128 256 c17_7_2 <| span_end 87 384 c17_7_3 (le_refl _)
theorem c17_8_0 : span (Z17 8) 96 0 = true := by decide +kernel
theorem c17_8_1 : span (Z17 8) 96 96 = true := by decide +kernel
theorem c17_8_2 : span (Z17 8) 96 192 = true := by decide +kernel
theorem c17_8_3 : span (Z17 8) 96 288 = true := by decide +kernel
theorem c17_8_4 : span (Z17 8) 96 384 = true := by decide +kernel
theorem c17_8_5 : span (Z17 8) 96 480 = true := by decide +kernel
theorem c17_8_6 : span (Z17 8) 64 576 = true := by decide +kernel
theorem l17_8 : ∀ i, 0 ≤ i → i < N17 8 → Z17 8 i = true :=
  span_step 96 0 c17_8_0 <| span_step 96 96 c17_8_1 <| span_step 96 192 c17_8_2 <| span_step 96 288 c17_8_3 <| span_step 96 384 c17_8_4 <| span_step 96 480 c17_8_5 <| span_end 64 576 c17_8_6 (le_refl _)
theorem c17_9_0 : span (Z17 9) 96 0 = true := by decide +kernel
theorem c17_9_1 : span (Z17 9) 81 96 = true := by decide +kernel
theorem l17_9 : ∀ i, 0 ≤ i → i < N17 9 → Z17 9 i = true :=
  span_step 96 0 c17_9_0 <| span_end 81 96 c17_9_1 (le_refl _)
theorem l17_10 : ∀ i, 0 ≤ i → i < N17 10 → Z17 10 i = true := span_end 9 0 (by decide +kernel) (le_refl _)
theorem l17_11 : ∀ i, 0 ≤ i → i < N17 11 → Z17 11 i = true := span_end 1 0 (by decide +kernel) (le_refl _)
theorem base_n7_071 : ∀ s, HasMonoSize 7 (gfn [] edges_n7_071) s → 12 ≤ s :=
  prove_base_mono (M := 7) (E := 9) (cap := 11) r17 x17 (gfn [] edges_n7_071)
    (SgenB 11 x17 o17 P17) N17 (idxGenB N17 H17) o17
    (by decide) ho17 rfl (by decide) rfl (by decide +kernel) rfl (by decide +kernel) (
    all_step l17_11 <| all_step l17_10 <| all_step l17_9 <| all_step l17_8 <| all_step l17_7 <| all_step l17_6 <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_zero lvl_empty)

def edges_n7_072 : List (Fin 7 × Fin 7) := [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(3,6),(4,5),(5,6)]
def r18 : List ℕ := [10,28,33,34,36,66,81,84,3,5,9,6,18,40,72,48,96]
def x18 : List ℕ := [1860,6441,2706,25603,37058,106524,82144]
def p18 (pi w : ℕ) : ℕ := match pi with
  | 0 => ((w &&& 0x16040) >>> 5) ||| (((w &&& 0x8000) >>> 3) ||| (((w &&& 0x4) >>> 2) ||| (((w &&& 0x20) >>> 1) ||| ((w &&& 0x488) ||| (((w &&& 0x10) <<< 1) ||| (((w &&& 0x1) <<< 2) ||| (((w &&& 0x1000) <<< 3) ||| ((w &&& 0xb02) <<< 5))))))))
  | _ => w
theorem vp18 : ∀ pi, ValidPerm 8 9 (p18 pi)
  | 0 => validPerm_of_spec 8 9 (p18 0) [(0x16040,2,5),(0x8000,2,3),(0x4,2,2),(0x20,2,1),(0x488,0,0),(0x10,1,1),(0x1,1,2),(0x1000,1,3),(0xb02,1,5)] [2,6,0,3,5,4,1,7,13,14,10,16,15,8,9,12,11] (fun _ => rfl) (by decide +kernel)
  | _ + 1 => validPerm_id 8 9
def o18 : List ℕ → List ℕ := oriStages p18 [[0]]
theorem ho18 : ∀ k l, (∀ w ∈ l, w < 2 ^ (8 + 9)) → DLive 8 9 k l.toFinset → DLive 8 9 k (o18 l).toFinset := fun _ _ hlt h => oriStages_dlive vp18 hlt h
def N18 : ℕ → ℕ | 5 => 6 | 6 => 222 | 7 => 1304 | 8 => 1694 | 9 => 441 | 10 => 17 | 11 => 1 | _ => 0
def H18_5 : ℕ → ℕ
  | 0 => 0xf9fabda3d0c89fbc5ce3bf6702c18e
  | _ => 0
def H18_6 : ℕ → ℕ
  | 0 => 0x53e23517e151089502954ebe04e8924e7204d86b4d4f84be784baf54b3654aae946e67465b745fee45b91427343e9c13d85b3d6e53add1375c4368ea35eb03414131838310ed30a4c3093b306d12f8942e6f22d0f22cf7729a1027c2c276c726a6124ceb2339d22bfb2222120ad3208a11f9161bfdc1ab46175d9126871142c107480ef510d37a0d07107c2c071d906d0b06bef05ccc04af803f560202e00910
  | 1 => 0x91fdb91ba8908098eca68ea938d2a38bf5e8a58c883d986a918594084f3e8402b8353b831c88305681db2816537e9797e93c7c7027a98c7a5637997d78c4077a9e76aed753197522d73d21719d47142b708fc707df6f56d6eaee6e9136e8a06a16c69c4d696a067afa679f866e15668b065e5365d8464b38635da62fd562dc2615d25f4515dbfb5d04d5ccd95a7995a4fb5a3705853f5832c567595559253e88
  | 2 => 0xddc73dcad1dba2ddb4ffda78fd6f47d4cf7d383fd2023d12d3cf554cf2ddcee9ccd9dacccd6cc758cb6abcb325ca9e2c6ba6c54cfc43c4c20d4c1e37bfa9dbf722bde81bda80baed2b79f8b3fe6b39a5b1fa2b1e30b1c4cb1840b14bab0c0faee99aea26ae37fadc2fad683accf2acb26ac6d7ac364aad40aa961a75bca564ea5551a4fbfa35bca3249a0fce9f0f09e122999fe9721c9622a94cba939b9924d2
  | 3 => 0xffe2afd15cfb7c5fb401f9385f658af64fff5cfbf5152f2146ef747ecb5eeb882eb32feb15be9350e8721e870fe85e0e7d87e7a36e5c48e58d5e3ed2e2168e2126e1c13e11ffe071ade318
  | _ => 0
def H18_7 : ℕ → ℕ
  | 0 => 0xb68a0b5670b4fb0aff70ace40a6ea0a6910a39109f4d09e9a09c9709c050982a09792090f50908d0907c08d8908b2a08786084970795c06f10069de0657f064570642906251061c8059c3057150568a056640565d04dbb04bb8049d7047ca0466a045ab03af703a840378a033bb03306028c50259002391022bf0225a01a17019b801631015e5014dd013f0012a3010c800e4200c68009080081a0070a006cd
  | 1 => 0x18f75187aa183a41823a18027177ea1732416a9a168371665e163ac15b9d158af150b114db2147d31476113c4813b20135bc134d712f2012a58129a61291a128261261b125a0123ae122a0121001207911e3a11cb6118be1120c1118710d9f10aa510a23109731062a0f8720f3890ed0f0ec270e9ff0e9f80e99b0e9660e6150e5b70e51e0dd8b0db740db700da3f0d4fe0cdc70cd140c35a0c0e00b8110b6b4
  | 2 => 0x276b6274502730826d56268842670a2630425f3425d5d25aa4257c22523a251c024bdd24b8523fcd23c7723753235a22306322c2b22bfb2224821f8e21c7721a9c21a4b218942163521367212bb212ab20d042091a208a920612204b2201ff1fba01f9661f10d1efc81e9661e67f1e67e1e0381d7691d0631cabc1ca321c7681bb811b91c1b76c1b42c1b2af1b1ab1ad461a6911a2071a158195ea1933719248
  | 3 => 0x366673642d3611435b0d35a61356bc35637350d034cad3480b34635342d433d0b33424330a032eee32bd7329a632680321953211031fba31e0e318fc318c430a9c3043c303742fa652fa172f89c2f4a72f0d62ebe22ea6c2e9612e2752cfba2c4f02c11e2c0ef2be682bd942bba62ba902b7492b6c42b54e2a6ef2a5a32a5252a08d29f3329be929a5f299e6298aa293f829289291d528a5b288062828727b5a
  | 4 => 0x40f0e40e8e409ea4098d40664404f0402a94001c3f9743f4043f0493ec6e3e3843e06c3df363dcdb3d6b93d1c43ccfd3cb3d3c80e3c75b3c4733c34a3c08c3bf153bb723b9023b6b53b02e3afac3ade63adc73a73c3a63a3a2bf3a1a33a00739e993995a398e13959a3953438fb338f2338d8138c7438bb0389b83889d38729385973842d383eb3837f383253802337c4b3780b376fb371ad3707036f07369a5
  | 5 => 0x4bd3b4bac14b6684b2bb4ac994a54b4a03d49dd949c4049b9d491dd48e9e48d7348b294884d4858d483e84831d480a74805647b734797d47954478564739d4715c470164701446b4d469ce46879466ee465934608c45fee45e534591a4575945619455944544e44fb044eb344b7b44701446af4447b4420343ef043ee243d1b43951437b9430434303142e5c42cfe4292b4207d41f9c41b33416f8413af41188
  | 6 => 0x592b458fa458ea458e7f58e6758c31583bd582ad57edb57b335798b5763a574415722e56bb556ba656a8d56a3a569e9569c4565255644b5620d55c8d55a3e556a75543e554275532c551ee54fad54e2d5460c5444553e1e53c1753b1552e115273c51c3851aec51acd51a98517e0516f4512c95106550e9450bb050b19506fb506284ff7c4ff044fe6b4f8ea4f3654e4684d4f84d2b14d0174cf454c2a14c232
  | 7 => 0x68968687c867be0678d3674e7674476720766b5466b13669a9666146635765ecc65de765641653ff64dab64af2648816441a6408063b32639ac638d0638bf635da6317d62fc662d6e62bbe6294862640624ed61eb96108e60f4c60c2b60aad60a7f609fa606f8606c2603496020f5fde65f7c25f4f25f4515f02e5f0255dd075da4c5d58b5c5ce5c3485c1085c0b65bbaa5b2945adda5a86a5a7d75a08c59f7b
  | 8 => 0x764a67649a75fb975f3675ea875e6275e35758fe75844751c774bf274976741cb73e4173c8c7389a7367d734027333d730867301a72c357299f7239c71cb571afa70f5070c0e70afe700f76ffba6fbe46fb056faa06fa726f72b6f5766f4ea6f30e6f1296f0cb6ea8f6e9916e92d6e59d6dde96dcee6d8936d88c6d1996c9a96c5c56bcb46b82c6b63c6ac476a5de6a44369c4d69b13695e368d7468b6068a40
  | 9 => 0x82fea82f0182cdd82bc88292b827f18227d8216c8184b81579811bf810cc80842805cb8059a803ca7fc017f94b7f84a7f5017f1b57eeef7ed187ec457eb9f7ea267e53f7e1d47da357d7ab7d4537d0da7cb127c8457c74e7c14b7c0c67a07e79f9279da279b5779b47796f97968d7945d793aa791a078c407887c78694782c378294781f97803277e9d779a77782d7779b7763477434770ac76d9976ba076630
  | 10 => 0x8f4438f2be8efe88eca68ec828e9cf8e92d8df428deab8da948cdaf8cda18c9f08c6758c3cd8c0818bf708b9ec8b8388b7368b3d48b13e8b0c28b0748aee08ab178a79e8a6968a56d8a38e8a05189d3289ce589ab489a9a896c8895f8893ba88aa588a16886fb883d987f888785687702874af86f0b86e8886a5485b6a859bb85706852dd84f3e84e5a84dd5846dc841da84170836958359083473831c883056
  | 11 => 0x9af1b9ae0d99f5c99e8899cd999a93998ba998a09980d9978d9977f9968998f459892d98814983bd9824a980909801d97e6b97b379763c9754296fb396dbc96c01969c2969ad9697095af19588294f3394690944cf9434b9426293e7f93e4d938e9937c593705935f59353b92afa925da921dc921da91971918dd91766915e9915a5914769118a9108d9105790f0490cc19010c8fa8c8f8fc8f6208f5018f4f3
  | 12 => 0xa4820a461ea45e0a45d0a44e7a42e5a4117a3e23a3a01a36d3a33dfa32c1a3249a2e49a2918a2914a2879a2833a26a6a25afa1ffea1f8da1c4ea1585a13c5a1130a0e44a0b43a0a7fa08d4a0841a07eda07d0a078da06309fc429f8789f4329f4169f2e79f0749eec99edcd9ed559e5d29e24a9df0d9dd359dbd29d61e9d1f59cdda9cc909c8459c7659c7449c4919c19c9c0339b8e49b8819b4109b1f79b0e1
  | 13 => 0xae805ae425adfc3aded9ad6cdad5c5ad552ad52fad392ad23dac7d3ac730ac6a1ac5c0ac364ac163abdf2ab907ab841ab5c7ab338ab26baadd0aa833aa7aea9ea0a9525a91d3a8b01a8843a87f5a80b9a800aa7ef8a7e11a7cf1a7cd9a7b45a774da7110a70fea6c77a6ae9a6a64a6862a6762a66b6a666ea6505a640ea5e5aa5d0da5bf4a5baea5920a5628a553ca53a1a52d8a5073a504fa4fbfa4f1aa4b8e
  | 14 => 0xbae1bbae0dbad4aba624ba483ba3a9ba392b9eccb9e99b9c13b9a61b993bb9826b95a3b92bcb8ea7b8647b859bb843db8210b7eccb7df3b7db3b7aa2b6e57b6952b67eab6186b6033b5adcb5329b4e94b4a50b493ab444cb4445b40e1b4023b3fe6b3d58b341fb3185b2d60b27cdb22fdb1d43b1c4cb1959b17fbb1725b1699b14f0b11bdb0c8fb045caff35afd67afba2af1bdaeebdaeeb6aee99ae9edae813
  | 15 => 0xc7186c6e6ac6ca7c6a79c6974c66f8c6639c62cec5ef3c5edbc5e6ec5ddec5cfac5b13c596ac5179c4bccc474fc465cc450ac44d8c423ec3dd2c3bf4c3b1cc392dc3205c317bc2f1dc1e21c1c83c18cfc1844c172dc1351c1264c11adc0831c024ec00d2bffd7bfdb7bfad0bfa9bbf879bf4f0bf39ebeb58be889be06bbdd19bdc10bdad5bd572bd396bd386bd019bcb13bc8efbbe14bb8bfbb48fbb422bb295
  | 16 => 0xd4f1cd4f04d4ee6d4cf8d4bf9d4b61d4aded4626d4216d4000d3a6ed3825d3297d3162d30a2d2f08d29b4d2818d2810d27dbd22e1d20ebd1f54d1e22d19c1d198ad0e8fd06d8d0128cf910cf636cf4e0cef2bcee77ceb3ecea82ce9fdce73cce6fbce3c9cdb82cd8c0ccfd8cca85cc9c6cbd94cb5dccaf45ca871ca7ecca29cc9b7dc9a69c9805c92f5c8dddc8bfbc8b89c886dc7f88c7b83c7b07c7a64c7542
  | 17 => 0xe0624e0484e02c5e02c4e0026dff50dfdf7dfc50dfc01dead4de4e5dde6addadfdda75dda6bdd769dd30ddcd9ddc48fdc314dc21adbfcbdbe9fdbda4dbc8bdbb1ddb5addb130daf3ddae02dad72dab7bda817da78fda75cda6d0da612da24cda0bbda0b4d9d41d9c2ed9baad9864d8fdad8d59d8b4ed889cd86d5d833ed7b7ad7ae0d78dbd704ad703bd6e2fd68f4d66fbd6351d5f4cd5e35d5713d5561d5358
  | 18 => 0xee5c8ee385edbe0ed59bed308ecd9becd90ecb5eecae3ec693ec40aec1d7ebee2eb589eb53ceb1e1eb0eaeb082eaf84ead5feaacbea88aea579e9ec9e9da3e988ee985ce97f9e966ae9634e95c8e8f5de8d36e89ede834be7fc6e7fa2e63a5e626ae5b76e59ebe58d5e5073e4ed1e479ee3f06e3901e38cde3648e31d3e2fb2e2f2de2c2be2979e2136e1fb9e1fa1e19d0e1920e189de17c2e173de168de0cf3
  | 19 => 0xfa084f956cf94f9f9385f91ebf8f65f8f1ef8dd5f816af7e31f79e8f79d4f75f4f733ef72e3f7157f706ef6f95f6ed5f6ea9f68d6f6757f6694f62f0f60aef5e73f5b62f5794f5754f54def4d54f4cb5f4b5bf45ddf4406f43d1f40a8f3c66f3599f2f46f2a1ef2a03f29cef26bcf259df1fa5f1dc7f1b46f1174f0facf0b35f07b5f0489f0221ef8a4ef57cef331ef228ef0a8eec02eeb7deeaf8eea50eea31
  | 20 => 0xfef17fecc7fe1edfe09bfdd26fdbf5fd8fffd8ebfd713fd47cfd1a3fd0eafcbd9fcad2fc9a8fc505fbe71fbd10fb7a0faf65faad6faa38fa8fcfa4c1
  | _ => 0
def H18_8 : ℕ → ℕ
  | 0 => 0x9f4d09e9a09d9509c9709c7409916098c10987f0967809624093b708d7c089f7089e80855108392082fd082950810c0808f075700749107025062510601505ce205bc10565205235051ae050f304ecc04c65047ca046ca045b5045ab043bd0401a03cbf039600394f038db035d9035b5033bb032db02f5a02e24026b0026a70264d022ce01fc101ac6019e601732015c40116100cbb00c72006cd004310027a
  | 1 => 0x129ea129a61295312804123ae122cb11c8911ad411a141196b118331120c10f2810d6010c5c10bcf10bb51087d107b41062a105d2104b3104161030d0fd130fa8d0f76f0f4a60f3430f1b20ee270ea6d0e9090e8710e76d0e6640e5eb0e2dd0e2610df8b0df490de020dcd40daf40dac80d7cd0d3c20d0450cf0e0c9c90c8b20c25d0bfd30bf100bd270b7400b71e0b4cd0a8180a7e30a6600a59b0a39b09f7d
  | 2 => 0x1c7771c16a1bd201b9ac1b2361aec21ae3d1abba1ab3b1a7b71a3c21a1dd1a0ec19921197c0194d1193fc1925018ee518a551865d18403183e918393182fe182b41823a181d417ec117c0c17b0f179e9179511786317857174d116af1167d71677b166d016522161b115ef615b9d159271569815663154cf1536d1521d14cad14c7814abf145a4140ed13f3a13f0f13cf213834134ff132c41319112b8312a58
  | 3 => 0x267d9267892670a263b025dca25a08257cb25515254362504c24e9524b77247c12464a245c52445a24327242c32429a2396a23791234ac2320e22da1226e522504222c921e6621dec21da821d8a21ae421a4b2195c215b1210b520bd020bcf20423201ff1fb451fa6f1f4651f3e01f3ba1f2e11f14f1f0de1ef141ed621eb931e9a51e9661e7951e4351e06c1df4e1d9ba1d8df1d2db1d2101ceeb1cb961ca32
  | 4 => 0x2fc702fa652ef622edb92ec8b2ea602e9f12e8f22e7162e4a82e4582dc4f2d8f92d4002d3fc2d1262d1022cb762c82e2c8172c6d42c5212c4bc2c3982c0352be0a2bc9e2bb572bb452ba902b9be2b9112b7492b6af2b2742b1292b03e2ad8e2ab9a2a7262a5132a08d29eb529e9729abd298aa2980b2943028a82287bd285822847c282d42828228131280ef27cfa274182736c2706326dd426d5626a08269a6
  | 5 => 0x38bb038b243897f3889d38617385413847e384663842d383fb383d63834e37fb637dff37d8e37ad6377ce376e037680374cd3702a366673659d3642d3640b3630d362da361693600635f4c35a613588635675350d03504734f0b349ad3490e33c8b33971336ca3363d33534334bb333bd3335c32ac432a22329a63294f321523212231da131cc731934318b93161130a9c309a73036a3025030190300a92fef6
  | 6 => 0x4206d41fd441d9f41b18417a44171f4151b40c82407da4067f4026a3fb6c3f9753f7a43f12f3ecaa3ebf73e7ab3e52e3e0de3dfb43ddf73dd4e3da9b3d9d93d9d13d9923d7143d5843d55b3cc043cbba3c9273c2f43c1b03bf523bea03be9e3bb4a3b9dd3b6b53b50f3b0333b02e3af1a3acb93aa103a73c3a5423a4443a2e23a09939f9539ec939b2d39ada3989a3981e396a839696394c93935638f6038d92
  | 7 => 0x4cd1f4cc344c9474bb864b4b14b3f44b31c4b2314b2174aeda4ada24aa67494ef48ab548a5448a2a489b648953487944862447e4547dfb47b6847b3a478564776d4770147653475c64739d4715c46fc946e59466284661f464c44647f45efb45c9745b41459b14529c44de244b4844b3d443a14435143f4d43e8643baa43a8f437e64379143597431a743045430434303142d6742ae34292b4264d423884207d
  | 8 => 0x55a6255864556a755568554725532c5520e54d5254c5554684546065459b53f6b5379b536ee536715331e52f5752c9752b5c52991521f9520f75201351d5f51ad651791510de50ff850de750c83506565041050076500014ff7c4fe6e4fe6b4fcc24fc4c4fb584f9984f8c54f7ec4f7854f5eb4ef854ef5e4ecf84ec534eb8c4eb7a4e9f14e75c4e3474e1254ded44dd2b4dc4f4d8cb4d3a94d2f54d0b04ceb7
  | 9 => 0x5f73d5f56f5f35d5f0945ecd45ec745ec635e9a35e6705e4a75e4005e3585e0b05dd075db795d00a5cd995cd345cb495c2a05c0ee5bf865be5a5bcca5bbaa5ba585b6b25b2295b1285acb55aa855a9bd5a86a5a76a5a60e5a4a45a3865a36a5a2d85a2c35a1e35a04d598dc59707596bc5966d58fcf58e5058cf758c3158a5f589d5583e257cc957cc157b1557af057870571df56bd45663c5620d561cb56051
  | 10 => 0x68e1468dbc68b4c68ae56886c686b968634685dc683eb6833267f3f67972677d26751b67459673fa66e4166c6066b2a6655865eff65a28659cb6564f65225650dd64e06646c46454463ff363f8563c5263900638d6635fc63206630c3630be62fd262eda62a14627986275c624a46249262303621ad6203e61d8e61c6961b9061b4f61b4b60d1460bab6068b60501603ff602665ff9d5fdcb5fc795fabc5f83f
  | 11 => 0x7413473d9873b86734a97313f72d8072c71724f17209f71f8171e1d71de271c7471afa718bf71527712f671140710fa70afe705cb70462700226fc136fc006f46d6eb546e7f16e76c6e4d46e46a6e0526deca6dd326dc676dc5c6dbc86da9f6d9fb6d0d36c6e66c1e66bf3d6bf156bee36bb036b85f6b5356b4f36b18a6b0db6af926acd96ab946a9f96a9e86a4436a2436a22e69b88695e3695ca69523691e4
  | 12 => 0x7ed287eb9f7ea727e6087e5d57e4eb7e3967e2437e0427dcbc7db0c7dad27d8ec7d7e47d6ef7d5aa7cf657cd297cd1e7c74e7c74a7c5b07c0ba7bf7e7baf97ba607ba0e7b4d47b2d17b2317b1b67aea17a3ca7a3c47a33779b3a79a18795f6795dc793aa79157789e47875978196781117810077e9d776ac776347708676693762f475de975a4675928758c375844754a874fc274d3574cf674b047492f741ff
  | 13 => 0x8a8728a2208a1df89e9989601891b388b37889ab887a2881eb87f3887a5c87781873498718986d9f86a738698186723864ed8618d8614885feb85e0e85d6e85d1985cab85be7857068568d856458540585305851be84ed784c6183ce783c6283c48839d883960837d18343d82f62829578277f826e8825a781f4a81e3781c238160c814d781135810ea80ff980c3d8057f7f9d07f9a07f94b7f4307f10b7ef35
  | 14 => 0x92b05928b4927e4927049238291eab91b3891b0c919bf918ee9180d91615914a99149f913339131590f5690f0490dbc90d8e90cc190c1690b3e900c58fc0a8fa8c8f8fc8f8b38f8ab8f82f8f2eb8f2528eef48ee928edbd8e9cf8e9848e9468e79b8e2d58e1498dba48dac18d9b78d8ee8d8c18d6748d6438d5388d3d08d34b8d0f48cdaf8c4b38c0f38bf848bf708bf468bca18b6d28ae9c8ae838a9d88a978
  | 15 => 0x99df399c5799ad399a93999fc9980d99517994a89912c98f4598d03989c99892d98248980909808f97fb797f5097b94979c597639975599753996ff796ec696bc496b0096ad3969ad968fd968539675a963e0962cd9608f95e4b95e2795b1495ade958eb95882958539559d952e795291950e194f3394d2194b9994b3594b14948129463893cbb93bf093bbc939fb938e99360b933849333292f2f92d8992cda
  | 16 => 0xa4180a406ba3d83a3b8ca3a01a388ba3798a310fa30eea30d5a30bda2d8aa2b86a2a15a2836a2727a2377a1e08a1dc0a1865a184fa17f0a143ca0f1da0dd8a0c69a0b2ba0b20a086ba07d0a06df9fe1d9fb559f8789f60c9f2989f12e9efbc9eb059e7559e2aa9e2139e09f9dd359dbf99d1249cc909be709bb879bb319b8819b60a9b2f49afee9af369aeb19ada69abaf9aab89a4bf9a3ee9a03899f5c99e88
  | 17 => 0xacc3dacbfaacb54acaffaca73ac7d3ac45aac3bcac163ac080ac075ac058abdf2abb36abaf8ab724ab507ab208aaf96aadd0aa9cbaa587aa35faa2f8aa1d6a9f29a98f7a954aa9455a9450a90a6a8d91a8befa8b01a8a90a8a0ba89e9a8623a8596a8296a81b7a81a5a80b9a7cf1a7b45a79b4a7781a76ffa6ae9a6a7ca6773a60a1a5f54a5b9fa59cea4f72a4e48a4bd0a4acda4990a4840a45e0a4551a4508
  | 18 => 0xb7aa2b79f0b7728b7467b6e58b6dc8b6b11b67bdb6287b61ffb5c33b5b3db5adcb5693b55b6b5513b54dab5404b5169b50adb4eecb4ecfb4bbeb4b8bb3e05b3901b30ecb2d26b2c8cb2592b22eeb2193b1f50b1a9cb192cb159ab155ab1508b10e7b10a2b0f3fb0c39b0c0fb0a9bb0490b002aafcffafc5caf348af2e9aef93aee2dae7cbae568ae3b4adfc3adfabadd51add1aad56fad389ad1ffacfaeacd78
  | 19 => 0xc3efbc3bf4c3b0fc360bc317bc300dc2e09c2567c24bdc1b10c1561c129bc1193c112ac0fdbc0ee2c0df2c0d8dc0d5cc0c1fc0c0cc0608c019bbf93abf8e7bf5b6bf575bef4dbeb58beacfbe4ebbd58fbd26ebd151bd0c3bc8f4bc8c9bc631bc588bc2fdbbf37bbc68bba30bb2a1bb068bad22ba543ba392ba1b8b9c13b9be4b9a61b94bab931fb91c9b8de5b8d84b8908b88fcb88b8b8797b8783b868bb7c4a
  | 20 => 0xcc5f1cc548cc342cc267cc1aacc126cc05fcbfd3cbe79cbe37cbcf2cb778cb3adcb02ccae63cab55ca885ca7daca6bbca06dc9dadc9d90c9d24c9b0cc9ae0c93e6c9074c8fbec8f41c8bfbc8b89c887dc886dc86a0c8295c7e65c7d25c7cc9c7abbc7a88c73a0c6fe0c6f10c6974c6538c60bec6073c5edbc5cfcc5af4c5acac59c4c58fcc561dc4fe5c4e9cc4d2ec4c90c4c46c4bccc4babc4ad1c450ac42da
  | 21 => 0xd5eb6d5cbdd5879d5324d51f0d4ef3d4d2ed4a19d45ebd4489d3fc8d38a7d29b5d282fd247ad230ed22c7d20f5d1fe9d1cbfd171ad143fd10fdd0797d072bcff5bcfb1ecf7b4cf741cf553cf406cf252cf1f5cf05dced1dceb3ecea46ce96ece8e1ce7e4ce6d3ce68ece59dce559ce4e9ce3c9ce340ce259ce21cce1c0cdea2cdd8dcdcdbcda62cd97dcd77acd3f2cd3b3cd1ebccf6bccd7acca87cc9c6cc600
  | 22 => 0xdf364df26bdf21edf09ddf01ddef90decd7debc6deaa3de761de4e5de3bede335dda9add901dd74fdd0b6dcf30dcf1adce99dcd56dcccfdcb57dc82adc7bfdc21adbde6db9dfdb5addb299db0cfdaea2dae02dab42daa94da811da75cda560da3d1d9f4ed9d41d9034d8ff2d8f48d8d17d8affd8aedd8946d893ad83fad810ad80ddd7ff8d7818d75ead7597d7577d741dd7067d6df8d69ded6686d6163d6092
  | 23 => 0xe9afce9a66e98f5e98dce945ce938ae9234e91dee8cabe8b06e8a70e8968e87a5e8028e7efae7e75e7e4be7b73e79e6e6fe4e6d14e68d5e6886e6614e6227e5cb7e58d9e520ce509ce5023e4e83e47afe44cde446de42f5e41a5e40ace3ca5e3aade38c8e35c0e2fd5e23dee2255e2052e1f08e1ce5e1cc7e1c7fe1b89e1a68e1649e13cee1056e0dbae0c7ae095ee06a5e01cfdff91dfc02dfc01dfb2ddf3d1
  | 24 => 0xf4928f48c9f4406f43d1f40acf3d84f3d21f3c66f3a40f384df2ddef2426f23f9f2159f1da6f1529f14b0f113bf1087f0e7df0bf7f07acf0554f03faf0362efe8bef8d6ef897ef6dcef658ef3d8ef381ef331ef2e9eed9eedc55eda0fed33ded26ded0c5ece79eca6dec7bdec6cdebee8ebeccebe47ebbc5ebb45eba8aeb86deb844eb7ddeb36deb273eb0f9ead6fead5feaadfea61fea473e9f4be9f0fe9b87
  | 25 => 0xfc9a8fc83cfc33afbf74fbdf1fbc96fbc21fb7a0faebffaea1fae2afadc1fad32fad15fac38fab80fa8fcfa8cafa4c1fa2f6fa231f9f7af9cdcf9b10f9963f94f9f913bf8cd3f8c5df89dbf8822f82c4f82abf82a2f7acef7a2bf7a12f789ff7157f6fcaf6eedf6cfcf6757f64b5f6368f6202f6170f60b9f5f06f5e73f5a5cf5a53f5983f5686f543ef53e1f534cf52cef5169f504cf4fb0f4d5af4af7f49ab
  | 26 => 0xffdc3ff8d5ff557ff4d0ff3cdfee95fed91fece7febbffea75fe904fe35afdfdbfde76fdd26fdcb8fdbcffdaf2fd91ffd865fd764fd748fd713fd61ffd4a9fd1e5fd1a3fd0e1fccd7fcc8a
  | _ => 0
def H18_9 : ℕ → ℕ
  | 0 => 0x25a082511c24b77245172425622da122564223162141d1e4351e3781e3441e1121c7681c1de19f8318ee5183de1820c17b0f16d1b16a67163b215e281566414a9b149b81440c12e6712799123ae11e5611c8911a3510bb5109651062a103b00f47c0e7c70de420de180ccb10b95f0b7050b5940b48509b1309916078c0071620668105ce20356c033bb027c2026af022ce01f7d019f9019c601502006cd0016e
  | 1 => 0x478564715c46831461c745d2f44e1b446ec443b84374c4331142d6741ab24178c3fb6c3f3473edfc3d6e03cdec3b9013b6b23ac3b3a4c43a27939da739c1739b8b399223916a384ae37cde3780c37751376e03586335748356743519833c6f3383a330d43271f3256c3177630cd42fba62e9f12e2ea2dfc92dd332d8b92d53a2c8b32c7152bcbb2ba902a8f82a8b42a22a28f9728936280ef27ce92736c26516
  | 2 => 0x6c7006c3936ada26ad2b6a4436997d695e368ff968cde682c56815d67c1f677d2675cc667ff664ec6625b66067653ab64e066473b6443663c4d637bd61e5f6097d6014f5fd9b5f2515e3955e1f15df5e5cb495ba695b8945acae5aa9159bb958f405876a56dd85630e55ed3558ac549595378a5130950bfb4fe6b4f7744f29d4ea5b4e5a34d1d94cd1f4c9694c4f64b1d14af144aa894a847493be486be48524
  | 3 => 0x952da950bb94bc8947a5932db92cda929489273b9261291dbc90f048fcf88ef838ee928edbd8deb68d3ed8ae838ab218a88788fa3887a2871d68626b85b5983ce782e6b8251081ff181b13818f880e397f9a07f10b7ef357da4e7d8497c8c67bc547b84a7b7c07aa467987779426790ae780d777878776b17708676c357678e7584474d4c73f7d72d8072d1172c7171afa718e5718c96ff876e3fd6e0526dec3
  | 4 => 0xb7467b71e6b6355b5fc4b5954b56e8b3ff6b3fc5b3c3eb3699b34b0b2654b2222b1f32b15fdb155ab13f5b0ddfaf34bae8efae5ddae03dadfc3ac83cac7d3abf0fab507aa83daa5b1a9804a9720a900ba8b01a84eda84a5a7ca0a4e6aa3d83a30bda2c6ea1cb4a18499fdf79fb1b9f12e9eb009ea609e4999dce59c3d59bee09ba1f9b4259ad009ab4299a93999fc98ad89874a96ff796dee9655c9609c95882
  | 5 => 0xd5eb2d5c4ed4985d419ad2f87d2c08d1df4d137dd0ffcd0f82d06aed023ccefb5ceebecee18cedf5ce9e4ce639ce4e9cda62cd560cc9c6cb60ecb245cafe0caa12ca044c9dadc9061c8ce0c7bcbc75b1c75a8c7445c6072c5884c5431c4ea8c4e8fc4c46c3d61c3ad3c2d4bc1a0fc1800c13a4c10a8c0c0cbeaf2bd547bbf37bbcc1bba8cbb463bad22babc4babb2ba46fba12eb9c13b806ab7cefb7a0cb7482
  | 6 => 0xfefd3fe16cfd713fd5dafd1a3fb55dfb001fa033f9fa1f9b10f9037f8c5df8034f7725f67c8f6757f62b9f5fcff4406f40bbf40acf3524f2426efdb6efbfdef3d8eecbdedc55ebad8eb86deb03feaa18e9dcbe9a6ee81d1e7b06e68bee6886e6873e6475e5e7ce5a9ce47afe4409e1e34e1ad5e1650e04d6dfd46df7b0df535def90de412dc21adad22d816cd7818
  | _ => 0
def H18_10 : ℕ → ℕ
  | 0 => 0xef658ea473e5ed0e1530ce96eb6eddb2f0b65f475fbaa506564ecf84cc34431a739802336ca29c851db6d
  | _ => 0
def H18 : ℕ → ℕ → ℕ | 5 => H18_5 | 6 => H18_6 | 7 => H18_7 | 8 => H18_8 | 9 => H18_9 | 10 => H18_10 | _ => fun _ => 0
def P18_5 : ℕ → ℕ
  | 0 => 0x1ac540579300140400e14202e50814131
  | _ => 0
def P18_6 : ℕ → ℕ
  | 0 => 0x4a24840b16176e4c0a99401c254ca394059854c0496163e585391510124c52f9304e45048d95240214923120530548bc1301a8041169305e8540641103be1498c9400364c5169503624c8569633d45445795156454438951548540049413540c8e895115e5057a1608b85403d951378545339512aa484111300e2584d89520f6504c6141104480111403185440b151288180a4141012545dc1613ca5444916204c4c8df1612d4548d91612aa54456931
  | 1 => 0x200584781602a2500039310f64c43b9430fc544369410dc4c0141513a14c84b1614fc4408194105a0403e1214725403b9324144c8369311c85805d93002e50509140040440141615ea5045a160124548b995115e5844e9535505841116053e584e844202e4c40b1411045802b920538544451506b0504b9921248545391610f65843f1410d2580d99400fc4c4d3940282480a404004e5499a94161c5840995061a54d1c9602fa4c80e91053e50409960
  | 2 => 0x64c4411302e65849013034650478150926100141413f24c9889402305041394209850456953112504df1513a0841a8160364545319600fc5848c8611685408e16123a4c48e1412865040195312450a481303465840193069c500b21320504c5a99600e44c00b1310c008049120538584d71500525881396235a5408995122054401963206544d71601bc508d6121022084d9141004084801511e85044c9201bc4841d1412384c58c9319f05805f921
  | 3 => 0x8504c0d69403a2508449510c4484f416172e500aec10378508e85522304c529151144504f9951490545521600aa508a21623ca505269415f658489961220584819611445440e9400e25041393215a50c8e151
  | _ => 0
def P18_7 : ℕ → ℕ
  | 0 => 0x8465013b1613d65419a17319758e641705ca4c26d1705640c8ff95001a5872797022ccc8da9302345c106040af210061850060508eb1732385454f9603bc5086fb303b25086d1702d1484e29408d050200c514b24c011850040508028502880c9963321a25c0df12066c085369701fc4c452b4088a5c456920c7114d5516096c5414f9705105cd309730b8584791410cc5cc98951844d862394122854c1f3314065442b0326f8540751307b054cff150
  | 1 => 0xc4e500bfb311445088a1202ef485cc9310865804d1323065066313008a500581202f45c0050700124c00313269e5416b15155c548ce9400684c48f141025148131703ea5482f1638801002d9511504400f360038584e05316be5064904180c1c1369501a458d019710205c57e940225140639202f058cef16158c180a4140c0e4c0ec9513f6541a7970086540a19704c258c299325e01c5581403b65c0a11602745cf009407b04c4f81618fa5c150173
  | 2 => 0x3da480040604b8540741509fd0817c9506325c0549711c45c18b161bf44c04a4533be5c642960146585ee1602eecc9869519845009d9710b84c59f151118586891507f4cc8110600f714462953c040c06d13222ccc4ef131046544ec9315ac5c6039420a21013694006a0c8be4500cc4ca71b206904c0870524600c0049530b8505291610e65451d97006e141191614464c176230c3ec802d96141250431141225544cd971c7150c1fc536184c42e171
  | 3 => 0x5f25c0229205ca5c1c2150334501a41503964c0cf13017a58d7e9300ea5807f1735cc4c19704006a18e662303c558c9c95036e4c8791711e25823e9501dc5853e0707e84c45095007f50db1a301d0581941325ac5846f1704dc501521301c4540691731ba58d071731985c44116074054445930126440b79727e05018715030c58cc295110c180629631505c0ff94088a54438961706140e6843025509821513ea5caab13160a58efb9307a604043050
  | 4 => 0x14e58c29973038544631315b05c89907133c5834803065058ca41703de1002e931430440e0430381544a11503705c05a96311254c399414ec5c44a33033a581a70406ec50aab17321e100ca33027258005840cdec408fc630c44c58714047ac851d3210ba4809497305a5c17a1428f0581ae9612d84c04b1402fed05cd1402385c563b3060a5cc3dd41126504b914255c485821410ca580ed9603b65404613150c5803a5532fec857e9607c25c06fb40
  | 5 => 0x6024c5cd1508665467705046a1017d96089c1c4c846317a4c04d173286540c3173328d022296164618dae95107f58ce6940a1e5c11f8404645c4c9161010100718606b650024020476540c19712d85cc639705cc4c46c5536ca508bd1506c64c45f063990504dd95369a580e59402e6540a5932308481758701fc4c1a41407f48c446151a525c0ba1512345406c9429f45c00f82026c5806d1317e28c1a01603ae480aa1400ba58d9b931b9a084ab170
  | 6 => 0x7084c1273412e658017972180544c91210865c0819312b654d2313268c4c588b323064c5273217bc508c21612b258cf14530ae0c0ca31033a4c3259502544800c0718d88c04782125a544541603ced01dc9514464c8cd95175458d18960140584c79304fe5c0b61312f04c430163b66580491511224c573173270540578323a458e4b8408fa580e3b102664c06893120a540979533925c0da9326c74c4dd963844586c99701c44c0631617405c488150
  | 7 => 0x8905c60b94041c54cca563496505da8504a65c67c131cb8540fb14218e54248040474d844f9311165cde8c310b45851d96044a1002d1416cc5c51eb316c25c0ca35053a5cc40160474cc5259712d84c87f1532a6541ee1410ec5c1fe9702f25405e9310c054c869701e4544789401dc505431502fed446403017054671b6005e589e89307bc585571306885c018040b7a4c02f1730b65c4031317405048d13074058466141192540691312e44c966840
  | 8 => 0x5f054dfb9511665455b9705805cc32142cfe8c01f44318e440bd13048c54cbd14014e4c8fc1532744c4a596345e5057d95070f08473170197485179517965c2a89610508c0541207bc4c51f15004c5010115311250ced0321c4580869602ac5423a95133a541681321ba5cc2e15162354d7a150b205803f5635024c27da20290540e70733c550d601634964c4a114011658cbc1320ca500f594065a18034850100540ca542150501321500ec580d8863
  | 9 => 0x5024c43b052146504a11301c8501499411f854583160276585441631dc4402194048c4c5e8b50a400c92735147c4c13696015e0c4e35515f058c6c5635d0505769703cecc2bb9312824c4de9310368c65a9505e25452c9504ce8411604004c5418a1406265801686186658c819304361804e0411cc5802f13260c54163b4083cd806f9500e958ea814068a108fb0715a05cec60409a458187b417e2ccb0c8404a64c53b1513c85083f83240018cfe873
  | 10 => 0x5a8509f8d43012504529405e84c050960146546119307fa5006915326e501fa17147ad451d3411ba4c90c1514ae5c06d951518100d3971aa05c1b8940381085e8b407ea140b115230c4c43a2318d8cc8b79621045c1a79607a2cc14186007e8830fb402a8549b01603da4c4c917118a4c91d1212505415a9504625c0ca3202364c97f0504b2581fa15100c5cc219300bc54cbf941628581899400e658574131424509309326065800f3102fe48452930
  | 11 => 0x71c5443f3320f75858716014ad41f71302fed85bf1501d0502898510985886c2311bc4c11c1511c4501a116370f546691401ba54ec29606085846d96145e4c6cc8405b0180e203032f10c2c140640549299411504c02612071c4426e96318a50c4795041c4c5b89600255894314045e585e19329884c4b9940974545590302cc5458b151150542bb94151a5087f14022e4c4c5932170584af553368501168201ee101821101c6081869613765cdd2b30
  | 12 => 0x56e541929630ca4c017941346508c1932b5254c631415e65c04b160a7054d4c1612ee484499619f6c86c2950526585731323f6581e11408d950c10962234582c29403dc5c29496066e4c98c3510ea4c19a163416181d355358ed42a01312284c6215610b448303970b84881a29507101050497161ed443a9706c25408953178d1443c84060a4caa49211fc5406b8400200c0339323b2584a68703ac58c9d1303f65c1a99514985c232970b84cc446141
  | 13 => 0xec5401187039250145950d20101e5940a4e4c176950020584be5314d85007b0323a81c4dd9322fe544318324355440dd6377c580331317e41011d351a94501a694039658152120012544761413fc5008fb3134e5445e1208085ce980406f84c0411300005c5a015087258ca19603f04c9fb9716424c5ad1407c7081ab9305264c5b1a105f65033c230822c826d13044c0c00316327458c4a563412584cc14245e5c6e71730684c92714157858594153
  | 14 => 0x1a44c8a7b329045cc9796305e4827dd42254580bbb52342100e495016a4c1273612a64c0bc153c36545259515cc58c4d13017c484dd94327cccb0fb50c7c5cdcf160c4858c88160c160c0049713ee4c9e01501185c54c1710b45c4001615265c4d39619525c21dc40474585d79602d1083081633365865d1311f25084035047a4c445931250500c91414b8580208400ba502665528725ccc1953370582ee961204cca6d840320cc4bb9320384c6ee951
  | 15 => 0x6a84c4601716fe5409d94128a501e1931a1a1052fc430ea54075021626540d99411c01450716363254004961142500861326844c47d9204a64ca1494196e5008184232ecc8001510ca540ab1309ba54c5017112950e84830050cc40e1415b0548639602b24caa4170104500081517c7485a29601245c4489730fd10d4f9501cc4c01e820616104631710e25444b17011e50081820a485c4499513dc4c1588400685049c1601125ccf81421a25062b040
  | 16 => 0x6a85c4299300ea5008b2305fe5045014167cd441a161a924c0969712a65c0db03006854432970381585f21512e64c017950124584489638e7546471320425ca3bc202048c5a29702205c1741514a650c26142828c41521213de0c05b16120a5c05a9321e25406e9301dc546cd02016658464040042549471536ee4c053953328d802192112c541a996100c4c01a1717760c1c714183a18c5e9329ae580188201925c0b61631124c95587031e580c8932
  | 17 => 0x1d454287950020504969413665c46896007ecc0bc97038a5406f1501404405b1511665c45a9533965c2631702865017b1325b0588db97318e500109421820c0da931bf8140661511925804a442a8e5c48294014ad811a83040458d1d1411244409f231cded42329506345058c36158ed80aa1721805844b1301265c5b817107ec862084051c58d87b6188a4c44496364a4c8331630b4544c597325258e611302705c0f815136e58edad5215258499950
  | 18 => 0x8465c0e81621344c41fb312845c0ef1716325818c151220501191313b25c4de9415041c519151100c80839511b4542b71600124c48296020c5468c1501bed82d99501f85859e95154450a1d0401a25401f3320985002d13171754d7b1532b254d869716624c6ce1403820842e95305150cbf9612e85c429931128c84403601fc58e668607b05ce460712705018997033a5c0bd1603ac4c49997031e5c06d1600385c4a59311e44c478970326540b4551
  | 19 => 0x17a5cc6fb502685411d151128cc5763321705c5a1a3126850052b30100cc0b7870732584ac943aae580ff960276545989539fa4c4299630cc4c00b13037c5c1a117376a180509700bc4c19f9531525459e961140545be140036cc0a59733fc5c0ad0427b854088130ad0582429307a35884914112254e5b9306e65449c1300ba4c2308312b25cc99960286504979433e0504969613d6581441311ca48118940174508c79506264c1809632685808d963
  | 20 => 0x37a5c46f1406e65848a9422da440c7940b32508ca2211f44c014553a90480f817133c4870fb604c24c0f59702f258066131192500bbb629cc4c23296001c080bc930
  | _ => 0
def P18_8 : ℕ → ℕ
  | 0 => 0x226500449510104c0059611ebd001e13014e60c8895018dcc4d81321f2580d6b70093d500c03001f50cb57300eb148d70302e80844297014860c47040199cc43a94029d5807ae212764c0d3765043d5007d70344cc04d9501835c08d0601ebd403013213e5c48f1401a20c02613111a4c467030003d840f17311f8801182018dd0c041522304c01cd400e4cc0b256011c4c05df53144d0094f500d2cc01d970173cc4784201144c84a8200006004fb61
  | 1 => 0x18450005971043d0c5e98321e4800df651084c0499402a5540034631eb94c4f95103ad4024e10058d840df43177c845415324b5800b130093d045b9832124c0041800225402b9701eb8c47f9530a6cc40eb201ad50067d6325f5405517029b10c83b50074d04c2b301624c88146205754c991401f8600c49300205c060d40199c8435550253d0c24f6516c600308212b20c012a20037d4015d7211654034d70356100931302018c484750353d8071521
  | 2 => 0x3d043815018a5c03c8302db14004f61003d4c6fb5108a5cc67b611865c06a93018ed84847600e85803e840256540099801591c0089701ae5800df10112d84bb1301805c060d3124f0c800f62226cc04d9802018846198302f5cc225700fdd843218317550008160014540d8130013d0c8064032a4c08995004e60c6018306d54c8896021b0845a96301a500cfb400c060024f212e45008ff3211fd402a130003c402d98323a5407ae4103e90004c52
  | 3 => 0x804c8a4c4318e5446eb5127f140034502f45c053931043d40959402bf5c05293005f50061932003994051600c84c02b9830fd8804ad41037d044602107f5c094e211ebc8411c631671c438c301f24c00de641bd1808d26004314800e321545800f132226d8089031043d804f9411ebcc009930013cc8269310295447b1501351482693223a58050170342cc06293233e54070950369884b57401ec4c0cfb602a850093f50209504b08300475801b341
  | 4 => 0x9458c1d16112058c3f752166cc06296028988494e402a110064c400224c004e100379407822011fd94d3930186500261832a84c880764037d4407c50112cc803832093c803b5700844c8908701c85803b02021b0804598019e544018711c05c044b511805808fe311a00c01815002f54c44941043d842105014e4c004d421405808fe421ebcc40355305f1845015000a4c042950037d883c1300ead407335123f884807310a750c1d15125054c67050
  | 5 => 0x176cc00ed430945cc10d4208a60c3f6652898c4139402b84c007d5125f5800eb600139944d970003d80919801674c4411302e20c07a16002d500639710d954094b211f4d447936129cd405a93030c5c004f6330a580a826030c540c2940174c80db7400845cc37d432065006c84002908010e31000500c2d61043840971320b64c0a60300a454480751003d407af6007654049950289d400de321d25c016151057188060732538c494e6513d54c24f40
  | 6 => 0x1c55c087c610ae4c807c40154500aad702725c04d4602e46008ff210ae58021c4033ed4094f212125c0637620105400df6403f504400301c0580cc83019a600d893029ad84a84701c55408d2400dc54486b31253d802698302f544806621999909a8302b64c89fc400875c83d0300a45843e83011a4c003040091100ae5210225806794128990c0a5410605000d0710545485b13036dd8099d500605807b1602640c8610322b8d4011d5309a4c07e170
  | 7 => 0x938840b4200e060004f52013948a2721112d04601400845489513220f5c45f9832331407283016c54013932253cc00ec511f20c86b940201950198830500c809960144480db8300ee58ca29502331c07314105608024541058d04c2b603385005a9320139508818030ad00094201901003017018dd4c9013223860ca6b321d258044b301b4540871801c61005018000394006960073080201302a01808395026810004f301ba584ca940343500a2321
  | 8 => 0xfdcc03e4410fec40d37400439503fb402c95001fb301b65cc25d43289cc01fd603461c059b60037900db7301d4d003306304b5c404f512ab50010f520c858c919502ab54010f30289cc40fd502ac5c0243311aa5cc1fc200ee5cc0b33008950020951003d480b82023c54062983013d940115107f5000813029d50019951177d502255005f080629401845c06673003b584709800ead002d9320138800ed7105f5405d560082dc4619502b0cc88a960
  | 9 => 0x1e1084b6a700b820c8075221f540919400fdd8c669303220c0bb1730a24c02e9630146006f97110814c4e1302bf580a9830307884890301165c000f6302d5c0395501665c09c9800504c03b43124fd80438302d65c02a07306c544ba0700c258c10e520aa4c81817018d9483f7410700c8d0d7008060c991802b8cc020b4124c5006b370201d885db2002a5006661020ed803e5210eacc029d4113d5c0081502a554c21d620b258c59950043d9401142
  | 10 => 0x34dd80959302966003807325f50004f20003d904d9600fd8c8669500e288447f632e44c009551093cc04bc302441407523200048442142093d4075451003d0c0bd7111fd800ed520704c089c420a688040142057540819600ce0c878c500a510c15a200fdd403957011fd047533027650087d60057508499801d4d4004f420975040df30199d4005d6328a58010f511180c84303004b1c01d9600d4cc08466425c4c012d53037c802613202554ca1960
  | 11 => 0x20ecc0c1f310939504bd3124f9901113034d884ad94011a4c8551800d614083a320d00c83e12003adc095131043d0893f5211f8c80594123fd4c71540013d0083b701321c07418009394004f41003d440e540199d448cc60003d0003221043d8c15131199d0010f40307d0c755611fe58c5133006060047f51037d8c00f2003f180ab1801b64c08e131307cc05783018d8400de102f45405df612b84808075023058c4817303808020b611931c0aa180
  | 12 => 0x7554c3fb30016d8425d60211d441cd610c84c49b5402ec5801a8501b64c86198021188010f410a01405df31087140847301364c80595115058cd89500d5580b915006cd440df421806005b14021260024f510f8dc0951830f95002d9310005406a98309460c83b201600c45db4003b504bb1832f60c004e300039801637129258410f32176c40d4e212e460c0bd6311458c21183037d4c7217020408000e312d6600b59830040c08e13202060094f64
  | 13 => 0x17390c3f6543384c01b4431625cc24f642db100521631804c09713131260c96830016dc424f620438c0753201fc0c03f760144d405df430895807093004b58066940158980ad94130c600c218330a5c00e42001390c0de3103950410f5313edc45393201388400e5425058c25d5319994099d4008a4c0753602e44c815a310005c08472108e0c48ff400138c46118012b5c81513016a5cc00e420975840814012f108db62113e5846298005a4c000e21
  | 14 => 0x844c40de410341c04d56123fcc000f3113ed44d39320180c8089400664c02e9320ee60c17d702705c093f100379481c93005f5c424f42211508b5940177d88b5765189540cf9702341006256000a4c8ae830093d4c1393112f0800de210c64c0161611c060010e650140c82f180016cc85e96323fd400b55011fd006b5501835402a9530f60c09e1731565cc7218020e58005c432d5d50c718324ec846d1800e55005de6500d5401013011650029553
  | 15 => 0x296580623200038404f0202a84c01d14107b50456440292d847514000d5c059b401be54400f21292504629300224c83013005f5803b5630d958c919300d95803ff21093c407156026d580601633075483f753199880db750182cc0c2b70353cc01393012060c032403604c4741500d24c03b55113088093f2132c54c5df41046084749803124c8753702304c4667640439009d9800d3540261300254c404d62199d80513702785c047e4018658c10e21
  | 16 => 0x2480c04b1831d64c0c493124f50847f302b66003ff640a04c0c78301b84c08a93004e5803f7620ce50825153144d800df311a41c412d400d5500611301ec60c3e551173d001308013ed04774400938c85db5008058c4ba30211d004b8301f2540245512360c06b5602a5500211630620c89fc601a80c00f84003b10415f652890c8dc13117c0c01d35118e584b4d31072d80bd160013cc4901311a254466754039540a4b322384c08474204358867961
  | 17 => 0x1aa4c8041701ca0c87af621780c06b17005708024e412d4c842fd6219ed442d97311f54808980369d4047f6207b1c01d3320044c0b61410734844ab310304c024e311cd54c10f100291c08603223fd80198321144c4a262014a100388200805cc4e13215050c4c4521755c0c316024f8800df211d4540c29501ba5447e1500a4d44991301cc544261630fdd00a78300144c025a6218dd8063b51208c807e130208d408d470074d84839702d5d80c1f50
  | 18 => 0x1e45844f571135540271300a4cc80403218a4c4b6c601eb9800942110e100099701f45447e14022c0c08d4502d5c8460d6011fd48afd400a80c063b7118d94097d703541401518307b100163510ffd443f7432304c85518329354c0346017e54c069801e3180b574134dd407af54307d0093f401b64c4cfb700a4d8432173091580b5750353d40bb1802329002617304e5443b95300d50c090200df544849600938c00df6116a4c4b633214660c93f42
  | 19 => 0x7b180b553227854024f3135a500b383016c5c00983118dd949c16023fd94637511bad844b15326a0c44ad51369d0011d500b25cc1fb500184c05595331860c04160353d00ac4432544c011b312da1c09856018dd488ff54093cc83632004e5400ed51253d003fe430ae4c0b10300fd8845215321250047f4319ed04846210d9500599600ee4c8a7130177d48d6960025500a4b411f554c4a030173d4c666540e4d80c2b5007354044c4324060c45130
  | 20 => 0x660c004f60013d8893f652675800b5602d8d044e0500244c4dc1320975083b5610571800bd500a04c8637500ca200a261024b5c05195301f1c060132013990951510ff94c3f641037d5059b50184540a69611d45800995006c5c447f6132a540d4f620a04c47334112054c3f6302ca0c0bd180164140d4d5232c60c3fe3121edc0ae1212a610083b401384c43f6310500c04d443199d485cf640c25ccb655311f8841614116e54c2293235a54006970
  | 21 => 0x8e0c051963177d446b461024cc44f272369cc05cf510c04c49b5701d060c73942043d8845930013d4c15d6300d50447e41369d80c505013858ca2764199d8c47e5303ad003703000a5400bd40177d90b78400ac5cc551322a4c803d03223c4c0209710045402422027654020b5111f8c41d9400bf1004d5511104c00a020208d000de60029184d0b601e84c025d63173cc093e2130b1cc1d9302e0cc06376418dcc0b573212c4c8320400a608009832
  | 22 => 0x145c030983098200d185016a60cad9300fdcc492d4013f58c6374035a5c05ce412d0100715612bf54087d510735c0637100ba60c355703011c0211300ae5406254011a5cc86820037d003ab7006c5842c98301808455153082504991501895c029a301d45c003573307d8015173176d803ff4303c54c2a9830439900a5501c2500806520fdc8411a2109388004f500ed5882313000a0c0983700005803657024f8406374209154cc044000a5481a821
  | 23 => 0x6cdc4338300f8c800356011410047e6000650000f3217794c3e5600265000a54018a5ccb2550013c8400f541738c4d393111fcc4c88500575046364326e1003b4210c84c8c0980016d0400f42072cc08a940326d8015d6101a5405df3235ad8047f542675c0368702ab5801513217e5cc721501285442d9630ead80985502f860010e2002f5083014000d50847f210766008bc21289d80667420395847af6325ecc06fb7102e8803a9500105003ff31
  | 24 => 0x32e0c03015004a080c99501998846363016260ccf9401aa58c07d500d3580636210939809e13029014005b510a05cc807631d058cab1301ec58c0eb3008a4c424f5218d8c42445215a1c02b980093d805d4302d64c0539731581807e16035ad40b562135ad00a95700e35009b5501d04c0139731310805de3115914002140003d947a180199d9472942173884a9560201cc02785004b5080a571177950209610568c06663113488000f301738c08bc31
  | 25 => 0x33e5801b3611ebd0c381701aa4c47c041177d8c1b141043cc4bf0500a060c5cf41132140ca9700c060c8074323210037d6020e500d8940047084807400ae58ca384017790803552037cc837d531864c045960013d905e9730ce4c4871501999040e4601b658c5de2111258457050043c84469831824c011d431e158c7af522d64c8139632d00c0161712615002b132047100849503704c0af03010a6000df60037d4800e20166dc0d373009a58c45183
  | 26 => 0xfdd943685001450034d400ac60c10f641265c0ce150013d50cfc6304b5cc3ab31289d0093f301665004813206ccc85d5500804c40bd611f2500d016007e4c0807601865cc901300de0804f5731d04c458030
  | _ => 0
def P18_9 : ℕ → ℕ
  | 0 => 0x1110006750011500047620219d80233001910001f7201dd400837001fd0001f62001dcc01750005d040463001714004776005d0803b300054c80377301fdc005f54009994077700194c80476500550400f4100c4c00575201354002f710128c007d5200a5800074001598000f6400750801c300039000157201f90c04d3201f8c0026740075000764001d90400741008dc00664300c50006e43001d840153001dd8c05e500019000675400a50001e41
  | 1 => 0x18002150005d4c01c60003d8c07765011d4c01772009d0801d7100518807e50003dc400c300114c8006410035c400f53013d8007450013dc00643001310001f71001d8c04f76007d4003f43005d8806f4000dd040367601b54004e5000bcc80077100fd4c0175100dc8400f3000b9d80375200bd48007530114c40234001d9c00376401fcc00676100bd50027640015440273202050001551013d8c00f5100bd8c004300035800275300acc002774
  | 2 => 0xfd4401f5400dcc804f650120c00747000e5400477000bd440167600fdcc05f500071400173000ddc404f43005dcc04f40019dc001d7000bdc802632015d0003f2100dd4c07650011d0802f41009d44034620199000164000cd8000571017dc0027730079c801552007cc000d510115080274100754401f6500590407f50007d0803f710085800173200dd5004f3201f9d802f43020d0001f51007d0c0177400390404f5201bd4007f52011cc801f63
  | 3 => 0x9dc400f73005dd404676019cc80333000190c04771005d4802e650085c002e64003d8402b6000558001d52005dc001d60017dd807740001d44044300138c80266401d98003340001d9005e30013d4401c4000798c0463200ed000154000ad0004f72009dd801e31011d4405f6200598801c70009d9400774013d0400630015d900477300cdc00176500599402950007d0001e400035000474100adc00315000f90c0146000d90401e4301d18002e32
  | 4 => 0x554004640011d000267600594c00731005908076720199c006470015d5001660001100016430079800543000310002754001d0c056400079d4037650084c00276202054000e5301f1000777400399004f50017d8002f6400a4c000e430058c4037750058c0005300135c002f7400758404f6400194c067400050c4017540038c40066101314000631001584057410038c001f410139d8081600170c004f71007d840026000d988055320158c003930
  | 5 => 0x1b8c006730009c8405641017d4c01e5001390001f52011d800365301b90001f70015cc802e41007d4c05a21017dc400f400075400835000b94808130008c8401743007dd405771017d0c0544001d8c001763005dd807e4001f18004764015d4c0243200990401731013d500236001dd800265301b0c002631003d0c05460011dd000540011d5006c40008d400577600794400f31020d800773001f98004d510079880214000794805762019d8005f42
  | 6 => 0x3776007dcc0394001bd4408170007cc4037620059d402f7600d54806f7300510001761011cc40573000c5c001f6000bd9402970005d8002b50001cc00335001d1000667201f0c001561020cc005e7600ed4006551019d9407f60017dcc03f310159d8066300191c803731019dd001e70015dcc02f21005d0003f41019d4406f3000dd0c01e300055080665001914002f3100c5800273101788400d30
  | _ => 0
def P18_10 : ℕ → ℕ
  | 0 => 0x621001d0000761001cc000760001c8400741001c40007200018c00064100184000620001d4000742001d8800751
  | _ => 0
def P18 : ℕ → ℕ → ℕ | 5 => P18_5 | 6 => P18_6 | 7 => P18_7 | 8 => P18_8 | 9 => P18_9 | 10 => P18_10 | _ => fun _ => 0
def Z18 (s i : ℕ) : Bool := barV3 8 9 (SgenB 11 x18 o18 P18) N18 (idxGenB N18 H18) o18 s i
theorem l18_5 : ∀ i, 0 ≤ i → i < N18 5 → Z18 5 i = true := span_end 6 0 (by decide +kernel) (le_refl _)
theorem c18_6_0 : span (Z18 6) 128 0 = true := by decide +kernel
theorem c18_6_1 : span (Z18 6) 94 128 = true := by decide +kernel
theorem l18_6 : ∀ i, 0 ≤ i → i < N18 6 → Z18 6 i = true :=
  span_step 128 0 c18_6_0 <| span_end 94 128 c18_6_1 (le_refl _)
theorem c18_7_0 : span (Z18 7) 128 0 = true := by decide +kernel
theorem c18_7_1 : span (Z18 7) 128 128 = true := by decide +kernel
theorem c18_7_2 : span (Z18 7) 128 256 = true := by decide +kernel
theorem c18_7_3 : span (Z18 7) 128 384 = true := by decide +kernel
theorem c18_7_4 : span (Z18 7) 128 512 = true := by decide +kernel
theorem c18_7_5 : span (Z18 7) 128 640 = true := by decide +kernel
theorem c18_7_6 : span (Z18 7) 128 768 = true := by decide +kernel
theorem c18_7_7 : span (Z18 7) 128 896 = true := by decide +kernel
theorem c18_7_8 : span (Z18 7) 128 1024 = true := by decide +kernel
theorem c18_7_9 : span (Z18 7) 128 1152 = true := by decide +kernel
theorem c18_7_10 : span (Z18 7) 24 1280 = true := by decide +kernel
theorem l18_7 : ∀ i, 0 ≤ i → i < N18 7 → Z18 7 i = true :=
  span_step 128 0 c18_7_0 <| span_step 128 128 c18_7_1 <| span_step 128 256 c18_7_2 <| span_step 128 384 c18_7_3 <| span_step 128 512 c18_7_4 <| span_step 128 640 c18_7_5 <| span_step 128 768 c18_7_6 <| span_step 128 896 c18_7_7 <| span_step 128 1024 c18_7_8 <| span_step 128 1152 c18_7_9 <| span_end 24 1280 c18_7_10 (le_refl _)
theorem c18_8_0 : span (Z18 8) 96 0 = true := by decide +kernel
theorem c18_8_1 : span (Z18 8) 96 96 = true := by decide +kernel
theorem c18_8_2 : span (Z18 8) 96 192 = true := by decide +kernel
theorem c18_8_3 : span (Z18 8) 96 288 = true := by decide +kernel
theorem c18_8_4 : span (Z18 8) 96 384 = true := by decide +kernel
theorem c18_8_5 : span (Z18 8) 96 480 = true := by decide +kernel
theorem c18_8_6 : span (Z18 8) 96 576 = true := by decide +kernel
theorem c18_8_7 : span (Z18 8) 96 672 = true := by decide +kernel
theorem c18_8_8 : span (Z18 8) 96 768 = true := by decide +kernel
theorem c18_8_9 : span (Z18 8) 96 864 = true := by decide +kernel
theorem c18_8_10 : span (Z18 8) 96 960 = true := by decide +kernel
theorem c18_8_11 : span (Z18 8) 96 1056 = true := by decide +kernel
theorem c18_8_12 : span (Z18 8) 96 1152 = true := by decide +kernel
theorem c18_8_13 : span (Z18 8) 96 1248 = true := by decide +kernel
theorem c18_8_14 : span (Z18 8) 96 1344 = true := by decide +kernel
theorem c18_8_15 : span (Z18 8) 96 1440 = true := by decide +kernel
theorem c18_8_16 : span (Z18 8) 96 1536 = true := by decide +kernel
theorem c18_8_17 : span (Z18 8) 62 1632 = true := by decide +kernel
theorem l18_8 : ∀ i, 0 ≤ i → i < N18 8 → Z18 8 i = true :=
  span_step 96 0 c18_8_0 <| span_step 96 96 c18_8_1 <| span_step 96 192 c18_8_2 <| span_step 96 288 c18_8_3 <| span_step 96 384 c18_8_4 <| span_step 96 480 c18_8_5 <| span_step 96 576 c18_8_6 <| span_step 96 672 c18_8_7 <| span_step 96 768 c18_8_8 <| span_step 96 864 c18_8_9 <| span_step 96 960 c18_8_10 <| span_step 96 1056 c18_8_11 <| span_step 96 1152 c18_8_12 <| span_step 96 1248 c18_8_13 <| span_step 96 1344 c18_8_14 <| span_step 96 1440 c18_8_15 <| span_step 96 1536 c18_8_16 <| span_end 62 1632 c18_8_17 (le_refl _)
theorem c18_9_0 : span (Z18 9) 96 0 = true := by decide +kernel
theorem c18_9_1 : span (Z18 9) 96 96 = true := by decide +kernel
theorem c18_9_2 : span (Z18 9) 96 192 = true := by decide +kernel
theorem c18_9_3 : span (Z18 9) 96 288 = true := by decide +kernel
theorem c18_9_4 : span (Z18 9) 57 384 = true := by decide +kernel
theorem l18_9 : ∀ i, 0 ≤ i → i < N18 9 → Z18 9 i = true :=
  span_step 96 0 c18_9_0 <| span_step 96 96 c18_9_1 <| span_step 96 192 c18_9_2 <| span_step 96 288 c18_9_3 <| span_end 57 384 c18_9_4 (le_refl _)
theorem l18_10 : ∀ i, 0 ≤ i → i < N18 10 → Z18 10 i = true := span_end 17 0 (by decide +kernel) (le_refl _)
theorem l18_11 : ∀ i, 0 ≤ i → i < N18 11 → Z18 11 i = true := span_end 1 0 (by decide +kernel) (le_refl _)
theorem base_n7_072 : ∀ s, HasMonoSize 7 (gfn [] edges_n7_072) s → 12 ≤ s :=
  prove_base_mono (M := 8) (E := 9) (cap := 11) r18 x18 (gfn [] edges_n7_072)
    (SgenB 11 x18 o18 P18) N18 (idxGenB N18 H18) o18
    (by decide) ho18 rfl (by decide) rfl (by decide +kernel) rfl (by decide +kernel) (
    all_step l18_11 <| all_step l18_10 <| all_step l18_9 <| all_step l18_8 <| all_step l18_7 <| all_step l18_6 <| all_step l18_5 <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_step lvl_empty <| all_zero lvl_empty)


/-! ## Section 4: Proofs of all 31 conjuncts -/

theorem cj1 : ∀ s, HasMonoSize 7 (gfn [] [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4),(5,6)]) s → 10 ≤ s :=
  (gfn_fix1 [] [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4),(5,6)] 5 [6] [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)] 9 (by decide) (by decide) (by decide) rfl rfl (by decide) (gfn_fix0 [6] [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)] 6 [] [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)] 8 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)] edges_BOWTIE (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 3 | ⟨4,_⟩ => 4 | ⟨5,_⟩ => 0 | _ => 0) (gfn [] edges_BOWTIE) (by decide) (fun _ => rfl) base_BOWTIE)))

theorem cj2 : ∀ s, HasMonoSize 7 (gfn [] [(0,1),(0,2),(0,3),(0,4),(1,2),(3,5),(4,6)]) s → 10 ≤ s :=
  (gfn_branch2 [] [(0,1),(0,2),(0,3),(0,4),(1,2),(3,5),(4,6)] 5 [] [(0,1),(0,2),(0,3),(0,4),(1,2),(4,6)] [3] [(0,1),(0,2),(0,4),(1,2),(4,6)] 8 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (gfn_fix0 [] [(0,1),(0,2),(0,3),(0,4),(1,2),(4,6)] 3 [] [(0,1),(0,2),(0,4),(1,2),(4,6)] 7 (by decide) rfl rfl (by decide) (gfn_branch2 [] [(0,1),(0,2),(0,4),(1,2),(4,6)] 6 [] [(0,1),(0,2),(0,4),(1,2)] [4] [(0,1),(0,2),(1,2)] 5 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (gfn_fix0 [] [(0,1),(0,2),(0,4),(1,2)] 4 [] [(0,1),(0,2),(1,2)] 4 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(1,2)] edges_K3 (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 0 | ⟨4,_⟩ => 0 | ⟨5,_⟩ => 0 | _ => 0) (gfn [] edges_K3) (by decide) (fun _ => rfl) base_K3)) (gfn_fix0 [4] [(0,1),(0,2),(1,2)] 4 [] [(0,1),(0,2),(1,2)] 4 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(1,2)] edges_K3 (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 0 | ⟨4,_⟩ => 0 | ⟨5,_⟩ => 0 | _ => 0) (gfn [] edges_K3) (by decide) (fun _ => rfl) base_K3)))) (gfn_fix0 [3] [(0,1),(0,2),(0,4),(1,2),(4,6)] 3 [] [(0,1),(0,2),(0,4),(1,2),(4,6)] 7 (by decide) rfl rfl (by decide) (gfn_branch2 [] [(0,1),(0,2),(0,4),(1,2),(4,6)] 6 [] [(0,1),(0,2),(0,4),(1,2)] [4] [(0,1),(0,2),(1,2)] 5 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (gfn_fix0 [] [(0,1),(0,2),(0,4),(1,2)] 4 [] [(0,1),(0,2),(1,2)] 4 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(1,2)] edges_K3 (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 0 | ⟨4,_⟩ => 0 | ⟨5,_⟩ => 0 | _ => 0) (gfn [] edges_K3) (by decide) (fun _ => rfl) base_K3)) (gfn_fix0 [4] [(0,1),(0,2),(1,2)] 4 [] [(0,1),(0,2),(1,2)] 4 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(1,2)] edges_K3 (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 0 | ⟨4,_⟩ => 0 | ⟨5,_⟩ => 0 | _ => 0) (gfn [] edges_K3) (by decide) (fun _ => rfl) base_K3)))))

theorem cj3 : ∀ s, HasMonoSize 7 (gfn [] [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(4,6)]) s → 10 ≤ s :=
  (gfn_branch2 [] [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(4,6)] 5 [] [(0,1),(0,2),(0,3),(1,2),(1,4),(4,6)] [3] [(0,1),(0,2),(1,2),(1,4),(4,6)] 8 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (gfn_fix0 [] [(0,1),(0,2),(0,3),(1,2),(1,4),(4,6)] 3 [] [(0,1),(0,2),(1,2),(1,4),(4,6)] 7 (by decide) rfl rfl (by decide) (gfn_branch2 [] [(0,1),(0,2),(1,2),(1,4),(4,6)] 6 [] [(0,1),(0,2),(1,2),(1,4)] [4] [(0,1),(0,2),(1,2)] 5 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (gfn_fix0 [] [(0,1),(0,2),(1,2),(1,4)] 4 [] [(0,1),(0,2),(1,2)] 4 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(1,2)] edges_K3 (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 0 | ⟨4,_⟩ => 0 | ⟨5,_⟩ => 0 | _ => 0) (gfn [] edges_K3) (by decide) (fun _ => rfl) base_K3)) (gfn_fix0 [4] [(0,1),(0,2),(1,2)] 4 [] [(0,1),(0,2),(1,2)] 4 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(1,2)] edges_K3 (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 0 | ⟨4,_⟩ => 0 | ⟨5,_⟩ => 0 | _ => 0) (gfn [] edges_K3) (by decide) (fun _ => rfl) base_K3)))) (gfn_fix0 [3] [(0,1),(0,2),(1,2),(1,4),(4,6)] 3 [] [(0,1),(0,2),(1,2),(1,4),(4,6)] 7 (by decide) rfl rfl (by decide) (gfn_branch2 [] [(0,1),(0,2),(1,2),(1,4),(4,6)] 6 [] [(0,1),(0,2),(1,2),(1,4)] [4] [(0,1),(0,2),(1,2)] 5 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (gfn_fix0 [] [(0,1),(0,2),(1,2),(1,4)] 4 [] [(0,1),(0,2),(1,2)] 4 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(1,2)] edges_K3 (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 0 | ⟨4,_⟩ => 0 | ⟨5,_⟩ => 0 | _ => 0) (gfn [] edges_K3) (by decide) (fun _ => rfl) base_K3)) (gfn_fix0 [4] [(0,1),(0,2),(1,2)] 4 [] [(0,1),(0,2),(1,2)] 4 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(1,2)] edges_K3 (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 0 | ⟨4,_⟩ => 0 | ⟨5,_⟩ => 0 | _ => 0) (gfn [] edges_K3) (by decide) (fun _ => rfl) base_K3)))))

theorem cj4 : ∀ s, HasMonoSize 7 (gfn [] [(0,1),(0,2),(0,3),(1,2),(3,4),(3,5),(4,6)]) s → 10 ≤ s :=
  (gfn_branch2 [] [(0,1),(0,2),(0,3),(1,2),(3,4),(3,5),(4,6)] 6 [] [(0,1),(0,2),(0,3),(1,2),(3,4),(3,5)] [4] [(0,1),(0,2),(0,3),(1,2),(3,5)] 8 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (gfn_fix0 [] [(0,1),(0,2),(0,3),(1,2),(3,4),(3,5)] 4 [] [(0,1),(0,2),(0,3),(1,2),(3,5)] 7 (by decide) rfl rfl (by decide) (gfn_branch2 [] [(0,1),(0,2),(0,3),(1,2),(3,5)] 5 [] [(0,1),(0,2),(0,3),(1,2)] [3] [(0,1),(0,2),(1,2)] 5 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (gfn_fix0 [] [(0,1),(0,2),(0,3),(1,2)] 3 [] [(0,1),(0,2),(1,2)] 4 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(1,2)] edges_K3 (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 0 | ⟨4,_⟩ => 0 | ⟨5,_⟩ => 0 | _ => 0) (gfn [] edges_K3) (by decide) (fun _ => rfl) base_K3)) (gfn_fix0 [3] [(0,1),(0,2),(1,2)] 3 [] [(0,1),(0,2),(1,2)] 4 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(1,2)] edges_K3 (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 0 | ⟨4,_⟩ => 0 | ⟨5,_⟩ => 0 | _ => 0) (gfn [] edges_K3) (by decide) (fun _ => rfl) base_K3)))) (gfn_fix0 [4] [(0,1),(0,2),(0,3),(1,2),(3,5)] 4 [] [(0,1),(0,2),(0,3),(1,2),(3,5)] 7 (by decide) rfl rfl (by decide) (gfn_branch2 [] [(0,1),(0,2),(0,3),(1,2),(3,5)] 5 [] [(0,1),(0,2),(0,3),(1,2)] [3] [(0,1),(0,2),(1,2)] 5 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (gfn_fix0 [] [(0,1),(0,2),(0,3),(1,2)] 3 [] [(0,1),(0,2),(1,2)] 4 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(1,2)] edges_K3 (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 0 | ⟨4,_⟩ => 0 | ⟨5,_⟩ => 0 | _ => 0) (gfn [] edges_K3) (by decide) (fun _ => rfl) base_K3)) (gfn_fix0 [3] [(0,1),(0,2),(1,2)] 3 [] [(0,1),(0,2),(1,2)] 4 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(1,2)] edges_K3 (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 0 | ⟨4,_⟩ => 0 | ⟨5,_⟩ => 0 | _ => 0) (gfn [] edges_K3) (by decide) (fun _ => rfl) base_K3)))))

theorem cj5 : ∀ s, HasMonoSize 7 (gfn [] [(0,1),(0,2),(0,3),(1,2),(3,4),(4,5),(5,6)]) s → 10 ≤ s :=
  (gfn_branch2 [] [(0,1),(0,2),(0,3),(1,2),(3,4),(4,5),(5,6)] 6 [] [(0,1),(0,2),(0,3),(1,2),(3,4),(4,5)] [5] [(0,1),(0,2),(0,3),(1,2),(3,4)] 8 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (gfn_fix0 [] [(0,1),(0,2),(0,3),(1,2),(3,4),(4,5)] 5 [] [(0,1),(0,2),(0,3),(1,2),(3,4)] 7 (by decide) rfl rfl (by decide) (gfn_branch2 [] [(0,1),(0,2),(0,3),(1,2),(3,4)] 4 [] [(0,1),(0,2),(0,3),(1,2)] [3] [(0,1),(0,2),(1,2)] 5 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (gfn_fix0 [] [(0,1),(0,2),(0,3),(1,2)] 3 [] [(0,1),(0,2),(1,2)] 4 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(1,2)] edges_K3 (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 0 | ⟨4,_⟩ => 0 | ⟨5,_⟩ => 0 | _ => 0) (gfn [] edges_K3) (by decide) (fun _ => rfl) base_K3)) (gfn_fix0 [3] [(0,1),(0,2),(1,2)] 3 [] [(0,1),(0,2),(1,2)] 4 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(1,2)] edges_K3 (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 0 | ⟨4,_⟩ => 0 | ⟨5,_⟩ => 0 | _ => 0) (gfn [] edges_K3) (by decide) (fun _ => rfl) base_K3)))) (gfn_branch2 [5] [(0,1),(0,2),(0,3),(1,2),(3,4)] 4 [5] [(0,1),(0,2),(0,3),(1,2)] [5,3] [(0,1),(0,2),(1,2)] 6 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (gfn_fix0 [5] [(0,1),(0,2),(0,3),(1,2)] 3 [5] [(0,1),(0,2),(1,2)] 5 (by decide) rfl rfl (by decide) (gfn_fix0 [5] [(0,1),(0,2),(1,2)] 5 [] [(0,1),(0,2),(1,2)] 4 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(1,2)] edges_K3 (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 0 | ⟨4,_⟩ => 0 | ⟨5,_⟩ => 0 | _ => 0) (gfn [] edges_K3) (by decide) (fun _ => rfl) base_K3))) (gfn_fix0 [5,3] [(0,1),(0,2),(1,2)] 3 [5] [(0,1),(0,2),(1,2)] 5 (by decide) rfl rfl (by decide) (gfn_fix0 [5] [(0,1),(0,2),(1,2)] 5 [] [(0,1),(0,2),(1,2)] 4 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(1,2)] edges_K3 (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 0 | ⟨4,_⟩ => 0 | ⟨5,_⟩ => 0 | _ => 0) (gfn [] edges_K3) (by decide) (fun _ => rfl) base_K3)))))

theorem cj6 : ∀ s, HasMonoSize 7 (gfn [] [(0,1),(0,2),(0,3),(1,2),(4,5),(4,6),(5,6)]) s → 10 ≤ s :=
  (gfn_fix0 [] [(0,1),(0,2),(0,3),(1,2),(4,5),(4,6),(5,6)] 3 [] [(0,1),(0,2),(1,2),(4,5),(4,6),(5,6)] 9 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(1,2),(4,5),(4,6),(5,6)] edges_TwoK3 (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 0 | ⟨4,_⟩ => 3 | ⟨5,_⟩ => 4 | _ => 5) (gfn [] edges_TwoK3) (by decide) (fun _ => rfl) base_TwoK3))

theorem cj7 : ∀ s, HasMonoSize 7 (gfn [] [(0,1),(0,2),(0,3),(1,4),(2,5),(3,6),(4,5)]) s → 10 ≤ s :=
  (gfn_branch2 [] [(0,1),(0,2),(0,3),(1,4),(2,5),(3,6),(4,5)] 6 [] [(0,1),(0,2),(0,3),(1,4),(2,5),(4,5)] [3] [(0,1),(0,2),(1,4),(2,5),(4,5)] 8 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (gfn_fix0 [] [(0,1),(0,2),(0,3),(1,4),(2,5),(4,5)] 3 [] [(0,1),(0,2),(1,4),(2,5),(4,5)] 7 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(1,4),(2,5),(4,5)] edges_C5 (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 0 | ⟨4,_⟩ => 3 | ⟨5,_⟩ => 4 | _ => 0) (gfn [] edges_C5) (by decide) (fun _ => rfl) base_C5)) (gfn_fix0 [3] [(0,1),(0,2),(1,4),(2,5),(4,5)] 3 [] [(0,1),(0,2),(1,4),(2,5),(4,5)] 7 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(1,4),(2,5),(4,5)] edges_C5 (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 0 | ⟨4,_⟩ => 3 | ⟨5,_⟩ => 4 | _ => 0) (gfn [] edges_C5) (by decide) (fun _ => rfl) base_C5)))

theorem cj9 : ∀ s, HasMonoSize 7 (gfn [] [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(3,4)]) s → 10 ≤ s :=
  (gfn_fix0 [] [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(3,4)] 5 [] [(0,1),(0,2),(0,3),(0,4),(0,6),(1,2),(3,4)] 9 (by decide) rfl rfl (by decide) (gfn_fix0 [] [(0,1),(0,2),(0,3),(0,4),(0,6),(1,2),(3,4)] 6 [] [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)] 8 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)] edges_BOWTIE (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 3 | ⟨4,_⟩ => 4 | ⟨5,_⟩ => 0 | _ => 0) (gfn [] edges_BOWTIE) (by decide) (fun _ => rfl) base_BOWTIE)))

theorem cj10 : ∀ s, HasMonoSize 7 (gfn [] [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,6),(3,4)]) s → 10 ≤ s :=
  (gfn_fix0 [] [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,6),(3,4)] 5 [] [(0,1),(0,2),(0,3),(0,4),(1,2),(1,6),(3,4)] 9 (by decide) rfl rfl (by decide) (gfn_fix0 [] [(0,1),(0,2),(0,3),(0,4),(1,2),(1,6),(3,4)] 6 [] [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)] 8 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)] edges_BOWTIE (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 3 | ⟨4,_⟩ => 4 | ⟨5,_⟩ => 0 | _ => 0) (gfn [] edges_BOWTIE) (by decide) (fun _ => rfl) base_BOWTIE)))

theorem cj11 : ∀ s, HasMonoSize 7 (gfn [] [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(3,4),(5,6)]) s → 11 ≤ s :=
  (gfn_branch2 [] [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(3,4),(5,6)] 6 [] [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(3,4)] [5] [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)] 9 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (gfn_fix0 [] [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(3,4)] 5 [] [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)] 8 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)] edges_BOWTIE (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 3 | ⟨4,_⟩ => 4 | ⟨5,_⟩ => 0 | _ => 0) (gfn [] edges_BOWTIE) (by decide) (fun _ => rfl) base_BOWTIE)) (gfn_fix0 [5] [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)] 5 [] [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)] 8 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)] edges_BOWTIE (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 3 | ⟨4,_⟩ => 4 | ⟨5,_⟩ => 0 | _ => 0) (gfn [] edges_BOWTIE) (by decide) (fun _ => rfl) base_BOWTIE)))

theorem cj12 : ∀ s, HasMonoSize 7 (gfn [] [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(1,6),(3,4)]) s → 10 ≤ s :=
  (gfn_fix0 [] [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(1,6),(3,4)] 5 [] [(0,1),(0,2),(0,3),(0,4),(1,2),(1,6),(3,4)] 9 (by decide) rfl rfl (by decide) (gfn_fix0 [] [(0,1),(0,2),(0,3),(0,4),(1,2),(1,6),(3,4)] 6 [] [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)] 8 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)] edges_BOWTIE (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 3 | ⟨4,_⟩ => 4 | ⟨5,_⟩ => 0 | _ => 0) (gfn [] edges_BOWTIE) (by decide) (fun _ => rfl) base_BOWTIE)))

theorem cj14 : ∀ s, HasMonoSize 7 (gfn [] [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(3,6)]) s → 10 ≤ s :=
  (gfn_fix0 [] [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(3,6)] 5 [] [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4),(3,6)] 9 (by decide) rfl rfl (by decide) (gfn_fix0 [] [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4),(3,6)] 6 [] [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)] 8 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)] edges_BOWTIE (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 3 | ⟨4,_⟩ => 4 | ⟨5,_⟩ => 0 | _ => 0) (gfn [] edges_BOWTIE) (by decide) (fun _ => rfl) base_BOWTIE)))

theorem cj15 : ∀ s, HasMonoSize 7 (gfn [] [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(5,6)]) s → 11 ≤ s :=
  (gfn_branch2 [] [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(5,6)] 6 [] [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4)] [5] [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)] 9 (by decide) (by decide) (by decide) rfl rfl rfl rfl (by decide) (by decide) (gfn_fix0 [] [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4)] 5 [] [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)] 8 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)] edges_BOWTIE (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 3 | ⟨4,_⟩ => 4 | ⟨5,_⟩ => 0 | _ => 0) (gfn [] edges_BOWTIE) (by decide) (fun _ => rfl) base_BOWTIE)) (gfn_fix0 [5] [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)] 5 [] [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)] 8 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)] edges_BOWTIE (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 3 | ⟨4,_⟩ => 4 | ⟨5,_⟩ => 0 | _ => 0) (gfn [] edges_BOWTIE) (by decide) (fun _ => rfl) base_BOWTIE)))

theorem cj16 : ∀ s, HasMonoSize 7 (gfn [] [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,6),(5,6)]) s → 10 ≤ s :=
  (gfn_fix0 [] [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,6),(5,6)] 4 [] [(0,1),(0,2),(0,3),(1,2),(1,5),(3,6),(5,6)] 9 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(0,3),(1,2),(1,5),(3,6),(5,6)] edges_K3C5 (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 3 | ⟨4,_⟩ => 0 | ⟨5,_⟩ => 4 | _ => 5) (gfn [] edges_K3C5) (by decide) (fun _ => rfl) base_K3C5))

theorem cj17 : ∀ s, HasMonoSize 7 (gfn [] [(0,1),(0,2),(0,3),(0,4),(1,2),(3,5),(3,6),(5,6)]) s → 11 ≤ s :=
  (gfn_fix0 [] [(0,1),(0,2),(0,3),(0,4),(1,2),(3,5),(3,6),(5,6)] 4 [] [(0,1),(0,2),(0,3),(1,2),(3,5),(3,6),(5,6)] 10 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(0,3),(1,2),(3,5),(3,6),(5,6)] edges_n6_025 (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 3 | ⟨4,_⟩ => 0 | ⟨5,_⟩ => 4 | _ => 5) (gfn [] edges_n6_025) (by decide) (fun _ => rfl) base_n6_025))

theorem cj21 : ∀ s, HasMonoSize 7 (gfn [] [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(3,6),(5,6)]) s → 11 ≤ s :=
  (gfn_fix0 [] [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(3,6),(5,6)] 4 [] [(0,1),(0,2),(0,3),(1,2),(3,5),(3,6),(5,6)] 10 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(0,3),(1,2),(3,5),(3,6),(5,6)] edges_n6_025 (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 3 | ⟨4,_⟩ => 0 | ⟨5,_⟩ => 4 | _ => 5) (gfn [] edges_n6_025) (by decide) (fun _ => rfl) base_n6_025))

theorem cj22 : ∀ s, HasMonoSize 7 (gfn [] [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(4,5),(5,6)]) s → 10 ≤ s :=
  (gfn_fix0 [] [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(4,5),(5,6)] 6 [] [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(4,5)] 9 (by decide) rfl rfl (by decide) (gfn_base [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(4,5)] edges_K3C5 (fun i : Fin 7 => match i with | ⟨0,_⟩ => 0 | ⟨1,_⟩ => 1 | ⟨2,_⟩ => 2 | ⟨3,_⟩ => 3 | ⟨4,_⟩ => 4 | ⟨5,_⟩ => 5 | _ => 0) (gfn [] edges_K3C5) (by decide) (fun _ => rfl) base_K3C5))

end PEqualNP.Outside.L_meta_984_aux

open PEqualNP.Outside.L_meta_984_aux in
theorem PEqualNP.Outside.L_meta_984 :
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)) x) → 10 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)) x) → 11 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)) x) → 12 ≤ C.size) ∧ (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)) x) → 12 ≤ C.size) :=
  ⟨finish_conj edges_n6_025 _ (fun x => by simp [gfn, edges_n6_025, Bool.or_assoc]) base_n6_025,
   finish_conj _ _ (fun x => by simp [gfn, Bool.or_assoc]) cj1,
   finish_conj _ _ (fun x => by simp [gfn, Bool.or_assoc]) cj2,
   finish_conj _ _ (fun x => by simp [gfn, Bool.or_assoc]) cj3,
   finish_conj _ _ (fun x => by simp [gfn, Bool.or_assoc]) cj4,
   finish_conj _ _ (fun x => by simp [gfn, Bool.or_assoc]) cj5,
   finish_conj _ _ (fun x => by simp [gfn, Bool.or_assoc]) cj6,
   finish_conj _ _ (fun x => by simp [gfn, Bool.or_assoc]) cj7,
   finish_conj edges_n7_050 _ (fun x => by simp [gfn, edges_n7_050, Bool.or_assoc]) base_n7_050,
   finish_conj _ _ (fun x => by simp [gfn, Bool.or_assoc]) cj9,
   finish_conj _ _ (fun x => by simp [gfn, Bool.or_assoc]) cj10,
   finish_conj _ _ (fun x => by simp [gfn, Bool.or_assoc]) cj11,
   finish_conj _ _ (fun x => by simp [gfn, Bool.or_assoc]) cj12,
   finish_conj edges_n7_055 _ (fun x => by simp [gfn, edges_n7_055, Bool.or_assoc]) base_n7_055,
   finish_conj _ _ (fun x => by simp [gfn, Bool.or_assoc]) cj14,
   finish_conj _ _ (fun x => by simp [gfn, Bool.or_assoc]) cj15,
   finish_conj _ _ (fun x => by simp [gfn, Bool.or_assoc]) cj16,
   finish_conj _ _ (fun x => by simp [gfn, Bool.or_assoc]) cj17,
   finish_conj edges_n7_060 _ (fun x => by simp [gfn, edges_n7_060, Bool.or_assoc]) base_n7_060,
   finish_conj edges_n7_061 _ (fun x => by simp [gfn, edges_n7_061, Bool.or_assoc]) base_n7_061,
   finish_conj edges_n7_062 _ (fun x => by simp [gfn, edges_n7_062, Bool.or_assoc]) base_n7_062,
   finish_conj _ _ (fun x => by simp [gfn, Bool.or_assoc]) cj21,
   finish_conj _ _ (fun x => by simp [gfn, Bool.or_assoc]) cj22,
   finish_conj edges_n7_065 _ (fun x => by simp [gfn, edges_n7_065, Bool.or_assoc]) base_n7_065,
   finish_conj edges_n7_066 _ (fun x => by simp [gfn, edges_n7_066, Bool.or_assoc]) base_n7_066,
   finish_conj edges_n7_067 _ (fun x => by simp [gfn, edges_n7_067, Bool.or_assoc]) base_n7_067,
   finish_conj edges_n7_068 _ (fun x => by simp [gfn, edges_n7_068, Bool.or_assoc]) base_n7_068,
   finish_conj edges_n7_069 _ (fun x => by simp [gfn, edges_n7_069, Bool.or_assoc]) base_n7_069,
   finish_conj edges_n7_070 _ (fun x => by simp [gfn, edges_n7_070, Bool.or_assoc]) base_n7_070,
   finish_conj edges_n7_071 _ (fun x => by simp [gfn, edges_n7_071, Bool.or_assoc]) base_n7_071,
   finish_conj edges_n7_072 _ (fun x => by simp [gfn, edges_n7_072, Bool.or_assoc]) base_n7_072⟩

