import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1612
open PEqualNP.CircuitLowerBounds
open Relation

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

theorem val_mono {n : ℕ} (gs : List Gate)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) (w : ℕ) :
    val gs w x = true → val gs w y = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · simpa only [val_input gs _ w hw] using hxy ⟨w,hw⟩
    by_cases hg : w < n + gs.length
    · have hi : w - n < gs.length := by omega
      have he : n + (w-n) = w := by omega
      rcases (legal gs[w-n] (List.getElem_mem hi)).1 with ha | ho
      · intro h
        have hs := (val_and gs x (w-n) hi ha).mp (by simpa only [he] using h)
        rw [← he]
        apply (val_and gs y (w-n) hi ha).mpr
        intro r hr
        obtain ⟨hlt,hit⟩ := hs r hr
        exact ⟨hlt, ih r (by omega) hit⟩
      · intro h
        obtain ⟨r,hr,hlt,hit⟩ := (val_or gs x (w-n) hi ho).mp (by simpa only [he] using h)
        rw [← he]
        exact (val_or gs y (w-n) hi ho).mpr ⟨r,hr,hlt,ih r (by omega) hit⟩
    · simp [val_big gs x w (by omega)]

def lines (t : Fin 13) : Finset (Fin 13) := {t,t+1,t+3,t+9}

abbrev neg (A : Finset (Fin 13)) : Fin 13 → Bool := fun v => decide (v ∉ A)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma geometry : (∀ t : Fin 13, (lines t).card = 4) ∧
    (0 : Fin 13) ∈ lines 4 ∧ (0 : Fin 13) ∈ lines 10 ∧ (0 : Fin 13) ∈ lines 12 ∧
    (1 : Fin 13) ∈ lines 1 ∧ (1 : Fin 13) ∈ lines 5 ∧ (1 : Fin 13) ∈ lines 11 ∧
    (∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), (0 : Fin 13) ∉ lines m) ∧
    (∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), (1 : Fin 13) ∉ lines l) := by
  decide +kernel


noncomputable def mset (L : Fin 13 → Finset (Fin 13)) (T : Fin 13 → Fin 13 → Fin 13 → Bool)
    (gates : List Gate) (l : Fin 13) (i : Fin gates.length) : Finset (Fin 13) := by
  classical
  exact (L l).filter (fun y => ∃ a b : ℕ, (gates.get i).inputs = [a, b] ∧
    (val gates a (T l y) = true ∨ val gates b (T l y) = true))

abbrev rel (L : Fin 13 → Finset (Fin 13)) (T : Fin 13 → Fin 13 → Fin 13 → Bool)
    (gates : List Gate) (l : Fin 13) (k : ℕ) : Fin 13 → Fin 13 → Prop :=
  EqvGen (fun p q => ∃ i : Fin gates.length, (i : ℕ) < k ∧
    (gates.get i).op = GateOp.or ∧ val gates (13 + (i : ℕ)) (neg (L l)) = false ∧
    p ∈ mset L T gates l i ∧ q ∈ mset L T gates l i)

theorem rel_step {L T gates l k} {i : Fin gates.length} {p q : Fin 13}
    (hi : (i : ℕ) < k) (hop : (gates.get i).op = GateOp.or)
    (hfa : val gates (13 + (i : ℕ)) (neg (L l)) = false)
    (hp : p ∈ mset L T gates l i) (hq : q ∈ mset L T gates l i) :
    rel L T gates l k p q :=
  EqvGen.rel p q ⟨i, hi, hop, hfa, hp, hq⟩

theorem rel_mono {L T gates l k k'} (h : k ≤ k') {p q : Fin 13}
    (hr : rel L T gates l k p q) : rel L T gates l k' p q := by
  induction hr with
  | rel a b hab =>
    obtain ⟨i, hi, hop, hfa, hp, hq⟩ := hab
    exact EqvGen.rel a b ⟨i, by omega, hop, hfa, hp, hq⟩
  | refl => exact EqvGen.refl _
  | symm a b _ ih => exact EqvGen.symm _ _ ih
  | trans a b c _ _ ih1 ih2 => exact EqvGen.trans _ _ _ ih1 ih2

theorem rel_const {L T gates l k} (X : Finset (Fin 13))
    (hX : ∀ i : Fin gates.length, (i : ℕ) < k → (gates.get i).op = GateOp.or →
      val gates (13 + (i : ℕ)) (neg (L l)) = false →
      ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L l, ∀ y' ∈ L l,
      (val gates a (T l y) = true ∨ val gates b (T l y) = true) →
      (val gates a (T l y') = true ∨ val gates b (T l y') = true) → (y ∈ X ↔ y' ∈ X))
    {p q : Fin 13} (hr : rel L T gates l k p q) : (p ∈ X ↔ q ∈ X) := by
  classical
  induction hr with
  | rel p q hpq =>
    obtain ⟨i, hi, hop, hfa, hp, hq⟩ := hpq
    obtain ⟨hpL, a, b, hinp, halp⟩ := Finset.mem_filter.mp hp
    obtain ⟨hqL, a', b', hinq, halq⟩ := Finset.mem_filter.mp hq
    have hab : a = a' ∧ b = b' := by
      have hh := hinp.symm.trans hinq
      simp at hh
      exact hh
    obtain ⟨rfl, rfl⟩ := hab
    exact hX i hi hop hfa a b hinp p hpL q hqL halp halq
  | refl => exact Iff.rfl
  | symm p q _ ih => exact ih.symm
  | trans p q r _ _ ih1 ih2 => exact ih1.trans ih2

theorem card_le_two_iff' {α : Type*} (s : Finset α) :
    s.card ≤ 2 ↔ ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a ≠ b → a ≠ c → b ≠ c → False := by
  constructor
  · intro h a ha b hb c hc hab hac hbc
    have := Finset.two_lt_card.2 ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩
    omega
  · intro h
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 hcon
    exact h a ha b hb c hc hab hac hbc

theorem exists_ordered_triple {α : Type*} [LinearOrder α] [DecidableEq α] (J : Finset α)
    (hJ : J.card = 3) : ∃ x ∈ J, ∃ y ∈ J, ∃ z ∈ J, x < y ∧ y < z := by
  classical
  have hne : J.Nonempty := Finset.card_pos.mp (by omega)
  set x := J.min' hne with hxdef
  set z := J.max' hne with hzdef
  have hxJ : x ∈ J := J.min'_mem hne
  have hzJ : z ∈ J := J.max'_mem hne
  have hxz : x ≠ z := by
    intro h
    have hsub : J ⊆ {x} := by
      intro w hw
      rw [Finset.mem_singleton]
      have h1 : x ≤ w := Finset.min'_le J w hw
      have h2 : w ≤ z := Finset.le_max' J w hw
      rw [← h] at h2
      exact le_antisymm h2 h1
    have hle := Finset.card_le_card hsub
    rw [Finset.card_singleton] at hle
    omega
  have hsub : ({x, z} : Finset α) ⊆ J := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hxJ
    · rw [Finset.mem_singleton] at hw; subst hw; exact hzJ
  have hcard2 : ({x, z} : Finset α).card = 2 := by
    rw [Finset.card_pair_eq_two_iff]; exact hxz
  have hc1 : (J \ {x, z}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hcard2]; omega
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hc1
  have hyJ : y ∈ J := by
    have h1 : y ∈ J \ {x, z} := hy ▸ Finset.mem_singleton_self y
    exact (Finset.mem_sdiff.mp h1).1
  have hnyx : y ≠ x := by
    have h1 : y ∈ J \ {x, z} := hy ▸ Finset.mem_singleton_self y
    have h2 := (Finset.mem_sdiff.mp h1).2
    intro h
    apply h2
    rw [h]
    exact Finset.mem_insert_self x ({z} : Finset α)
  have hnyz : y ≠ z := by
    have h1 : y ∈ J \ {x, z} := hy ▸ Finset.mem_singleton_self y
    have h2 := (Finset.mem_sdiff.mp h1).2
    intro h
    apply h2
    rw [h]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self z)
  exact ⟨x, hxJ, y, hyJ, z, hzJ,
    lt_of_le_of_ne (Finset.min'_le J y hyJ) (Ne.symm hnyx),
    lt_of_le_of_ne (Finset.le_max' J y hyJ) hnyz⟩

theorem merge_unifies {α : Type*} [DecidableEq α] (U : Finset α) (hU : U.card = 3)
    (R : α → α → Prop) (hR : Equivalence R)
    {a b p q : α} (ha : a ∈ U) (hb : b ∈ U) (hp : p ∈ U) (hq : q ∈ U)
    (hab : a ≠ b) (hRab : R a b) (hpq : ¬ R p q) :
    ∀ x ∈ U, EqvGen (fun s t => R s t ∨ (s = p ∧ t = q) ∨ (s = q ∧ t = p)) x a := by
  classical
  have hpq' : p ≠ q := fun h => hpq (h ▸ hR.refl q)
  have hsub_ab : ({a, b} : Finset α) ⊆ U := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact ha
    · exact hb
  have hsub_pq : ({p, q} : Finset α) ⊆ U := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hp
    · exact hq
  have hcab : ({a, b} : Finset α).card = 2 := by
    rw [Finset.card_pair_eq_two_iff]; exact hab
  have hcpq : ({p, q} : Finset α).card = 2 := by
    rw [Finset.card_pair_eq_two_iff]; exact hpq'
  have hne : ({a, b} : Finset α) ≠ {p, q} := by
    intro h
    apply hpq
    have h1 : p ∈ ({a, b} : Finset α) := by
      rw [h]; exact Finset.mem_insert_self p ({q} : Finset α)
    have h2 : q ∈ ({a, b} : Finset α) := by
      rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
    · exact absurd rfl hpq'
    · exact hRab
    · exact hR.symm hRab
    · exact absurd rfl hpq'
  have hsubU : ({a, b} : Finset α) ∪ {p, q} ⊆ U := Finset.union_subset hsub_ab hsub_pq
  have hcardU : (({a, b} : Finset α) ∪ {p, q}).card ≤ 3 := by
    have := Finset.card_le_card hsubU; omega
  have hinter : (({a, b} : Finset α) ∩ {p, q}).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hdisj : Disjoint ({a, b} : Finset α) {p, q} :=
      Finset.disjoint_iff_inter_eq_empty.mpr hemp
    rw [Finset.card_union_of_disjoint hdisj, hcab, hcpq] at hcardU
    omega
  have hinterle : (({a, b} : Finset α) ∩ {p, q}).card ≤ 1 := by
    by_contra hlt
    have h2 : 2 ≤ (({a, b} : Finset α) ∩ {p, q}).card := by omega
    have hsub : ({a, b} : Finset α) ⊆ {p, q} := by
      have heq : ({a, b} : Finset α) ∩ {p, q} = {a, b} :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
      rw [← heq]; exact Finset.inter_subset_right
    exact hne (Finset.eq_of_subset_of_card_le hsub (by omega))
  have hunion : ({a, b} : Finset α) ∪ {p, q} = U := by
    have hsum := Finset.card_union_add_card_inter ({a, b} : Finset α) ({p, q} : Finset α)
    have hinterpos : 0 < (({a, b} : Finset α) ∩ {p, q}).card := Finset.card_pos.mpr hinter
    have hc3 : (({a, b} : Finset α) ∪ {p, q}).card = 3 := by omega
    exact Finset.eq_of_subset_of_card_le hsubU (by omega)
  obtain ⟨w, hw⟩ := hinter
  obtain ⟨hws, hwt⟩ := Finset.mem_inter.mp hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hws hwt
  have hwa : EqvGen (fun s t => R s t ∨ (s = p ∧ t = q) ∨ (s = q ∧ t = p)) w a := by
    rcases hws with rfl | rfl
    · exact EqvGen.refl _
    · exact EqvGen.rel _ _ (Or.inl (hR.symm hRab))
  have hwp : EqvGen (fun s t => R s t ∨ (s = p ∧ t = q) ∨ (s = q ∧ t = p)) w p := by
    rcases hwt with rfl | rfl
    · exact EqvGen.refl _
    · exact EqvGen.rel _ _ (Or.inr (Or.inr ⟨rfl, rfl⟩))
  have hwq : EqvGen (fun s t => R s t ∨ (s = p ∧ t = q) ∨ (s = q ∧ t = p)) w q := by
    rcases hwt with rfl | rfl
    · exact EqvGen.rel _ _ (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact EqvGen.refl _
  intro x hx
  rw [← hunion] at hx
  rcases Finset.mem_union.mp hx with hxab | hxpq
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hxab
    rcases hxab with h | h
    · rw [h]; exact EqvGen.refl _
    · rw [h]; exact EqvGen.rel _ _ (Or.inl (hR.symm hRab))
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hxpq
    rcases hxpq with h | h
    · rw [h]; exact EqvGen.symm _ _ (EqvGen.trans _ _ _ (EqvGen.symm _ _ hwa) hwp)
    · rw [h]; exact EqvGen.symm _ _ (EqvGen.trans _ _ _ (EqvGen.symm _ _ hwa) hwq)
theorem key (L : Fin 13 → Finset (Fin 13)) (l c : Fin 13) (M : Finset (Fin 13))
    (hcard : (L l).card = 4) (hc : c ∈ L l)
    (T : Fin 13 → Fin 13 → Fin 13 → Bool) (gates : List Gate)
    (hlegal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hwf : ∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < 13 + (i : ℕ))
    (hTc : T l c = fun v => decide (v = c))
    (hMc : ∀ m ∈ M, c ∉ L m)
    (I : Finset (Fin gates.length))
    (hI : ∀ g ∈ I, ((gates.get g).op = GateOp.or ∧
        val gates (13 + (g : ℕ)) (fun v : Fin 13 => decide (v ∉ L l)) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L l, ∃ r' ∈ L l,
          val gates w1 (T l r) = true ∧ val gates w2 (T l r') = true ∧
          ∃ X : Finset (Fin 13), r ∈ X ∧ r' ∉ X ∧
            (∀ i : Fin gates.length, i < g → (gates.get i).op = GateOp.or →
              val gates (13 + (i : ℕ)) (fun v : Fin 13 => decide (v ∉ L l)) = false →
              ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L l, ∀ y' ∈ L l,
              (val gates a (T l y) = true ∨ val gates b (T l y) = true) →
              (val gates a (T l y') = true ∨ val gates b (T l y') = true) → (y ∈ X ↔ y' ∈ X))) ∧
        ∃ m ∈ M, val gates (13 + (g : ℕ)) (fun v : Fin 13 => decide (v ∉ L m)) = false) :
    I.card ≤ 2 := by
  classical
  have notc : ∀ g ∈ I, c ∉ mset L T gates l g := by
    intro g hg hcm
    obtain ⟨⟨hop, hfa, w1, w2, hin, r, hrL, r', hr'L, h1, h2, X, hrX, hr'X, hX⟩, m, hmM, hfm⟩ := hI g hg
    have hcm' : c ∉ L m := hMc m hmM
    obtain ⟨-, a, b, hinab, halive⟩ := Finset.mem_filter.mp hcm
    have hab : a = w1 ∧ b = w2 := by
      have hh := hinab.symm.trans hin
      simp at hh
      exact hh
    rw [hab.1, hab.2] at halive
    have hnotex : ¬ (∃ i ∈ (gates.get g).inputs, i < 13 + (g:ℕ) ∧
        val gates i (neg (L m)) = true) := by
      intro hcon
      have hv := (val_or gates (neg (L m)) (g:ℕ) g.isLt hop).2 hcon
      rw [hfm] at hv
      exact Bool.false_ne_true hv
    have hpoint : ∀ v : Fin 13, (T l c) v = true → (neg (L m)) v = true := by
      intro v hv
      have hvc : v = c := by
        rw [hTc] at hv
        simpa using hv
      subst hvc
      simp [neg, hcm']
    have hw1lt : w1 < 13 + (g:ℕ) := hwf g w1 (by rw [hin]; simp)
    have hw2lt : w2 < 13 + (g:ℕ) := hwf g w2 (by rw [hin]; simp)
    rcases halive with hlv | hlv
    · have hm := val_mono gates hlegal (T l c) (neg (L m)) hpoint w1 hlv
      exact hnotex ⟨w1, by rw [hin]; simp, hw1lt, hm⟩
    · have hm := val_mono gates hlegal (T l c) (neg (L m)) hpoint w2 hlv
      exact hnotex ⟨w2, by rw [hin]; simp, hw2lt, hm⟩
  have ess : ∀ g ∈ I, ∃ r, ∃ r', r ∈ mset L T gates l g ∧ r' ∈ mset L T gates l g ∧
      ¬ rel L T gates l (g:ℕ) r r' := by
    intro g hg
    obtain ⟨⟨hop, hfa, w1, w2, hin, r, hrL, r', hr'L, h1, h2, X, hrX, hr'X, hX⟩, m, hmM, hfm⟩ := hI g hg
    have hrm : r ∈ mset L T gates l g := by
      rw [mset, Finset.mem_filter]
      exact ⟨hrL, w1, w2, hin, Or.inl h1⟩
    have hr'm : r' ∈ mset L T gates l g := by
      rw [mset, Finset.mem_filter]
      exact ⟨hr'L, w1, w2, hin, Or.inr h2⟩
    refine ⟨r, r', hrm, hr'm, ?_⟩
    intro hrel
    have hrc := rel_const X (fun i hi hop' hfa' a b hin' y hy y' hy' al1 al2 =>
      hX i hi hop' hfa' a b hin' y hy y' hy' al1 al2) hrel
    exact hr'X (hrc.mp hrX)
  have claim : ∀ x ∈ I, ∀ y ∈ I, ∀ z ∈ I, x < y → y < z → False := by
    intro x hx y hy z hz hxy hyz
    obtain ⟨rx, rx', hrxm, hrx'm, hnx⟩ := ess x hx
    obtain ⟨ry, ry', hrym, hry'm, hny⟩ := ess y hy
    obtain ⟨rz, rz', hrzm, hr'zm, hnz⟩ := ess z hz
    have hrxU : rx ∈ (L l).erase c := by
      rw [Finset.mem_erase]
      exact ⟨fun h => notc x hx (h ▸ hrxm), (Finset.mem_filter.mp hrxm).1⟩
    have hrx'U : rx' ∈ (L l).erase c := by
      rw [Finset.mem_erase]
      exact ⟨fun h => notc x hx (h ▸ hrx'm), (Finset.mem_filter.mp hrx'm).1⟩
    have hryU : ry ∈ (L l).erase c := by
      rw [Finset.mem_erase]
      exact ⟨fun h => notc y hy (h ▸ hrym), (Finset.mem_filter.mp hrym).1⟩
    have hry'U : ry' ∈ (L l).erase c := by
      rw [Finset.mem_erase]
      exact ⟨fun h => notc y hy (h ▸ hry'm), (Finset.mem_filter.mp hry'm).1⟩
    have hrzU : rz ∈ (L l).erase c := by
      rw [Finset.mem_erase]
      exact ⟨fun h => notc z hz (h ▸ hrzm), (Finset.mem_filter.mp hrzm).1⟩
    have hrz'U : rz' ∈ (L l).erase c := by
      rw [Finset.mem_erase]
      exact ⟨fun h => notc z hz (h ▸ hr'zm), (Finset.mem_filter.mp hr'zm).1⟩
    have hU3 : ((L l).erase c).card = 3 := by
      have hh := Finset.card_erase_of_mem hc
      omega
    have hxop : (gates.get x).op = GateOp.or := (hI x hx).1.1
    have hxfa : val gates (13 + (x:ℕ)) (neg (L l)) = false := (hI x hx).1.2.1
    have hyop : (gates.get y).op = GateOp.or := (hI y hy).1.1
    have hyfa : val gates (13 + (y:ℕ)) (neg (L l)) = false := (hI y hy).1.2.1
    have hrelxx' : rel L T gates l (y:ℕ) rx rx' :=
      rel_step (by exact hxy) hxop hxfa hrxm hrx'm
    have hrxne : rx ≠ rx' := by
      intro h
      apply hnx
      rw [h]
      exact EqvGen.refl rx'
    have hR : Equivalence (rel L T gates l (y:ℕ)) :=
      { refl := fun _ => EqvGen.refl _
        symm := fun h => EqvGen.symm _ _ h
        trans := fun h1 h2 => EqvGen.trans _ _ _ h1 h2 }
    have huniv := merge_unifies ((L l).erase c) hU3 (rel L T gates l (y:ℕ)) hR
      hrxU hrx'U hryU hry'U hrxne hrelxx' hny
    have h1 := huniv rz hrzU
    have h2 := huniv rz' hrz'U
    have hgen : ∀ s t, (rel L T gates l (y:ℕ) s t ∨ (s = ry ∧ t = ry') ∨ (s = ry' ∧ t = ry)) →
        rel L T gates l (z:ℕ) s t := by
      intro s t hst
      rcases hst with hst | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact rel_mono (Nat.le_of_lt hyz) hst
      · exact rel_step hyz hyop hyfa hrym hry'm
      · exact EqvGen.symm _ _ (rel_step hyz hyop hyfa hrym hry'm)
    have hcontra : rel L T gates l (z:ℕ) rz rz' :=
      EqvGen.eqvGen_le hgen rz rz' (EqvGen.trans _ _ _ h1 (EqvGen.symm _ _ h2))
    exact hnz hcontra
  rw [card_le_two_iff']
  intro g1 hg1 g2 hg2 g3 hg3 h12 h13 h23
  have hJsub : ({g1, g2, g3} : Finset (Fin gates.length)) ⊆ I := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hg1
    · exact hg2
    · exact hg3
  have hJ3 : ({g1, g2, g3} : Finset (Fin gates.length)).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨g1, g2, g3, h12, h13, h23, rfl⟩
  obtain ⟨x, hxJ, y, hyJ, z, hzJ, hxyz⟩ := exists_ordered_triple _ hJ3
  exact claim x (hJsub hxJ) y (hJsub hyJ) z (hJsub hzJ) hxyz.1 hxyz.2

theorem eval_ofFn (gates : List Gate) {n : ℕ} (o : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨gates, o⟩ (List.ofFn x) = val gates o x := rfl

end PEqualNP.Outside.L_meta_1612

theorem PEqualNP.Outside.L_meta_1612 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (T : Fin 13 → Fin 13 → Fin 13 → Bool) (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ t : Fin 13, ∀ p ∈ L t, ∀ v ∈ L t, T t p v = true ↔ v = p) → (∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), T l 0 = (fun v : Fin 13 => decide (v = 0))) → (∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), T m 1 = (fun v : Fin 13 => decide (v = 1))) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < 13 + (i : ℕ)) →
    (∀ l ∈ ({4, 10, 12} : Finset (Fin 13)), (∀ X : Finset (Fin 13), (∀ i : Fin gates.length, True → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L l, ∀ y' ∈ L l,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y)) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y')) = true) → (y ∈ X ↔ y' ∈ X)) → ∀ y ∈ L l, ∀ y' ∈ L l, (y ∈ X ↔ y' ∈ X)) →
      ∀ I : Finset (Fin gates.length), (∀ g ∈ I, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L l, ∃ r' ∈ L l, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (T l r)) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (T l r')) = true ∧
        ∃ X : Finset (Fin 13), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L l, ∀ y' ∈ L l,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y)) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T l y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T l y')) = true) → (y ∈ X ↔ y' ∈ X))) ∧
        ∃ m ∈ ({1, 5, 11} : Finset (Fin 13)), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false) → I.card ≤ 2) ∧
    (∀ m ∈ ({1, 5, 11} : Finset (Fin 13)), (∀ X : Finset (Fin 13), (∀ i : Fin gates.length, True → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L m, ∀ y' ∈ L m,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T m y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T m y)) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T m y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T m y')) = true) → (y ∈ X ↔ y' ∈ X)) → ∀ y ∈ L m, ∀ y' ∈ L m, (y ∈ X ↔ y' ∈ X)) →
      ∀ I : Finset (Fin gates.length), (∀ g ∈ I, ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L m, ∃ r' ∈ L m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w1⟩ (List.ofFn (T m r)) = true ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w2⟩ (List.ofFn (T m r')) = true ∧
        ∃ X : Finset (Fin 13), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (i : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L m))) = false →
          ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ L m, ∀ y' ∈ L m,
          (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T m y)) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T m y)) = true) → (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, a⟩ (List.ofFn (T m y')) = true ∨ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, b⟩ (List.ofFn (T m y')) = true) → (y ∈ X ↔ y' ∈ X))) ∧
        ∃ l ∈ ({4, 10, 12} : Finset (Fin 13)), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, 13 + (g : ℕ)⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L l))) = false) → I.card ≤ 2) := by
  intro L hL T gates hleg hT0 hT1 hgates hwf
  have hLeq : L = PEqualNP.Outside.L_meta_1612.lines := funext hL
  subst hLeq
  obtain ⟨hcard, h04, h010, h012, h11, h15, h111, h0not, h1not⟩ :=
    PEqualNP.Outside.L_meta_1612.geometry
  constructor
  · intro l hl huni I hI
    have hTc : T l 0 = fun v => decide (v = 0) := hT0 l hl
    have hc : (0 : Fin 13) ∈ PEqualNP.Outside.L_meta_1612.lines l := by
      have hl' : l = 4 ∨ l = 10 ∨ l = 12 := by simpa using hl
      rcases hl' with rfl | rfl | rfl
      · exact h04
      · exact h010
      · exact h012
    exact PEqualNP.Outside.L_meta_1612.key PEqualNP.Outside.L_meta_1612.lines l 0
      ({1, 5, 11} : Finset (Fin 13)) (hcard l) hc T gates hgates hwf hTc h0not I
      (by simpa only [PEqualNP.Outside.L_meta_1612.eval_ofFn, PEqualNP.Outside.L_meta_1612.neg] using hI)
  · intro m hm huni I hI
    have hTc : T m 1 = fun v => decide (v = 1) := hT1 m hm
    have hc : (1 : Fin 13) ∈ PEqualNP.Outside.L_meta_1612.lines m := by
      have hm' : m = 1 ∨ m = 5 ∨ m = 11 := by simpa using hm
      rcases hm' with rfl | rfl | rfl
      · exact h11
      · exact h15
      · exact h111
    exact PEqualNP.Outside.L_meta_1612.key PEqualNP.Outside.L_meta_1612.lines m 1
      ({4, 10, 12} : Finset (Fin 13)) (hcard m) hc T gates hgates hwf hTc h1not I
      (by simpa only [PEqualNP.Outside.L_meta_1612.eval_ofFn, PEqualNP.Outside.L_meta_1612.neg] using hI)
