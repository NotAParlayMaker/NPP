import Mathlib
import PEqualNP.Defs

private def l275Good (g : PEqualNP.CircuitLowerBounds.Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2

private def l275Step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

private def l275Wires (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) : List Bool :=
  gs.foldl l275Step x

private def l275Val (gs : List PEqualNP.CircuitLowerBounds.Gate) (x : Fin 7 → Bool)
    (j : ℕ) : Bool :=
  (l275Wires gs (List.ofFn x)).getD j false

private lemma l275_wires_append (gs hs : List PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) :
    l275Wires (gs ++ hs) x = l275Wires hs (l275Wires gs x) := by
  simp [l275Wires, List.foldl_append]

private lemma l275_wires_prefix (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
    ∃ t : List Bool, l275Wires gs w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [l275Wires], rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hlen⟩ := ih (l275Step w g)
    refine ⟨g.op.eval (g.inputs.map fun j => w.getD j false) :: t, ?_, by simp [hlen]⟩
    change l275Wires gs (l275Step w g) = _
    rw [ht]
    simp [l275Step]

private lemma l275_wires_length (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
    (l275Wires gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hlen⟩ := l275_wires_prefix gs w
  simp [ht, hlen]

private lemma l275_wires_getD (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool)
    (j : ℕ) (hj : j < w.length) :
    (l275Wires gs w).getD j false = w.getD j false := by
  obtain ⟨t, ht, _⟩ := l275_wires_prefix gs w
  rw [ht, List.getD_append _ _ _ _ hj]

private lemma l275_val_append (gs hs : List PEqualNP.CircuitLowerBounds.Gate)
    (x : Fin 7 → Bool) (j : ℕ) (hj : j < 7 + gs.length) :
    l275Val (gs ++ hs) x j = l275Val gs x j := by
  unfold l275Val
  rw [l275_wires_append, l275_wires_getD]
  simpa [l275_wires_length] using hj

private lemma l275_gate_val (pre post : List PEqualNP.CircuitLowerBounds.Gate)
    (g : PEqualNP.CircuitLowerBounds.Gate) (x : Fin 7 → Bool) :
    l275Val (pre ++ g :: post) x (7 + pre.length) =
      g.op.eval (g.inputs.map fun j => l275Val pre x j) := by
  let w := l275Wires pre (List.ofFn x)
  have hw : w.length = 7 + pre.length := by simp [w, l275_wires_length]
  unfold l275Val
  rw [l275_wires_append]
  change (l275Wires post (l275Step w g)).getD (7 + pre.length) false = _
  rw [l275_wires_getD _ _ _ (by simp [l275Step, hw])]
  simp [l275Step, List.getD_eq_getElem?_getD, ← hw, w]

private lemma l275_wires_mono (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hgs : ∀ g ∈ gs, l275Good g) (w v : List Bool) (hlen : w.length = v.length)
    (h : ∀ j, w.getD j false = true → v.getD j false = true) :
    ∀ j, (l275Wires gs w).getD j false = true → (l275Wires gs v).getD j false = true := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    change ∀ j, (l275Wires gs (l275Step w g)).getD j false = true →
      (l275Wires gs (l275Step v g)).getD j false = true
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [l275Step, hlen]
    · obtain ⟨hop, hinputs⟩ := hgs g (by simp)
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hinputs
      intro j
      by_cases hj : j < w.length
      · have hj' : j < v.length := by rwa [← hlen]
        simpa only [l275Step, List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ hj'] using h j
      unfold l275Step
      by_cases hj' : j = w.length
      · subst j
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _),
          List.getElem?_append_right hlen.ge, Nat.sub_self, Nat.sub_eq_zero_of_le hlen.le,
          List.getElem?_cons_zero, Option.getD_some, hab, List.map_cons, List.map_nil]
        rcases hop with hop | hop
        · simp [hop, PEqualNP.CircuitLowerBounds.GateOp.eval, Bool.and_eq_true]
          exact fun hwa hwb => ⟨h a hwa, h b hwb⟩
        · simp [hop, PEqualNP.CircuitLowerBounds.GateOp.eval, Bool.or_eq_true]
          exact fun hw => hw.imp (h a) (h b)
      · rw [List.getD_eq_default _ _ (by simp only [List.length_append, List.length_singleton]; omega)]
        simp

private lemma l275_val_mono (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hgs : ∀ g ∈ gs, l275Good g) (x y : Fin 7 → Bool)
    (h : ∀ p, x p = true → y p = true) (j : ℕ) :
    l275Val gs x j = true → l275Val gs y j = true := by
  apply l275_wires_mono gs hgs _ _ (by simp)
  intro k hk
  by_cases hlt : k < 7
  · have hx : k < (List.ofFn x).length := by simpa
    have hy : k < (List.ofFn y).length := by simpa
    rw [List.getD_eq_getElem _ _ hx, List.getElem_ofFn] at hk
    rw [List.getD_eq_getElem _ _ hy, List.getElem_ofFn]
    exact h ⟨k, hlt⟩ hk
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hlt)] at hk
    contradiction

private def l275Single (p : Fin 7) : Fin 7 → Bool := fun q => decide (q = p)

private def l275Pair (p q : Fin 7) : Fin 7 → Bool := fun r => decide (r = p ∨ r = q)

private def l275Support (gs : List PEqualNP.CircuitLowerBounds.Gate) (j : ℕ) : Finset (Fin 7) :=
  Finset.univ.filter fun p => l275Val gs (l275Single p) j = true

private lemma l275_mem_support (gs : List PEqualNP.CircuitLowerBounds.Gate) (j : ℕ) (p : Fin 7) :
    p ∈ l275Support gs j ↔ l275Val gs (l275Single p) j = true := by
  simp [l275Support]

private lemma l275_support_is_gate (gs : List PEqualNP.CircuitLowerBounds.Gate) (j : ℕ)
    (hc : 2 ≤ (l275Support gs j).card) : 7 ≤ j ∧ j < 7 + gs.length := by
  constructor
  · by_contra! hj
    have hsub : l275Support gs j ⊆ {⟨j, hj⟩} := by
      intro p hp
      rw [l275_mem_support, l275Val, l275_wires_getD _ _ _ (by simpa using hj),
        List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn] at hp
      have he : (⟨j, hj⟩ : Fin 7) = p := by simpa only [l275Single, decide_eq_true_eq] using hp
      simpa only [Finset.mem_singleton] using he.symm
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hcard
    omega
  · by_contra! hj
    have hzero : l275Support gs j = ∅ := by
      ext p
      rw [l275_mem_support, l275Val,
        List.getD_eq_default _ _ (by simpa [l275_wires_length] using hj)]
      simp
    simp [hzero] at hc

private def l275Line (i : Fin 4) : Finset (Fin 7) :=
  (![ {0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5} ] : Fin 4 → Finset (Fin 7)) i

private lemma l275_line_card : ∀ i, (l275Line i).card = 3 := by decide

private lemma l275_line_inter : ∀ i j, i ≠ j → ((l275Line i) ∩ (l275Line j)).card ≤ 1 := by
  decide

private lemma l275_support_out (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ) (i : Fin 4)
    (hone : ∀ p, l275Val gs (l275Single p) o = true ↔ p ∈ l275Line i) :
    l275Support gs o = l275Line i := by
  ext p
  rw [l275_mem_support, hone]

private lemma l275_helper (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hgs : ∀ g ∈ gs, l275Good g) (o : ℕ) (i : Fin 4)
    (hone : ∀ p, l275Val gs (l275Single p) o = true ↔ p ∈ l275Line i)
    (hpair : ∀ x : Fin 7 → Bool, (Finset.univ.filter (fun q => x q = true)).card ≤ 2 →
      (∀ q ∈ l275Line i, x q = false) → l275Val gs x o = false) :
    ∃ j, 7 ≤ j ∧ j < o ∧ 2 ≤ (l275Support gs j).card ∧ l275Support gs j ⊆ l275Line i := by
  have hpos := l275_support_is_gate gs o (by rw [l275_support_out gs o i hone, l275_line_card]; decide)
  let d := o - 7
  have hd : d < gs.length := by dsimp [d]; omega
  let pre := gs.take d
  let g := gs[d]
  let post := gs.drop (d + 1)
  have hsplit : gs = pre ++ g :: post := by
    dsimp [pre, g, post]
    rw [← List.drop_eq_getElem_cons hd, List.take_append_drop]
  have ho : o = 7 + pre.length := by
    rw [show pre.length = d by simp [pre, Nat.min_eq_left (Nat.le_of_lt hd)]]
    dsimp [d]
    omega
  have hpre : ∀ k ∈ pre, l275Good k := fun k hk => hgs k (List.mem_of_mem_take hk)
  obtain ⟨hop, hinputs⟩ := hgs g (List.getElem_mem hd)
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hinputs
  have hgate (x : Fin 7 → Bool) :
      l275Val gs x o = g.op.eval [l275Val pre x a, l275Val pre x b] := by
    calc
      l275Val gs x o = l275Val (pre ++ g :: post) x (7 + pre.length) := by
        rw [← hsplit, ← ho]
      _ = _ := by rw [l275_gate_val, hab]; rfl
  have promote (j : ℕ) (hc : 2 ≤ (l275Support pre j).card)
      (hs : l275Support pre j ⊆ l275Line i) :
      7 ≤ j ∧ j < o ∧ 2 ≤ (l275Support gs j).card ∧ l275Support gs j ⊆ l275Line i := by
    obtain ⟨hj, hj'⟩ := l275_support_is_gate pre j hc
    have he : l275Support gs j = l275Support pre j := by
      ext p
      simp only [l275_mem_support]
      rw [hsplit, l275_val_append pre (g :: post) _ j hj']
    exact ⟨hj, ho ▸ hj', he ▸ hc, he ▸ hs⟩
  rcases hop with hand | hor
  · have hinter : l275Support pre a ∩ l275Support pre b = l275Line i := by
      ext p
      rw [← hone p, hgate, hand]
      simp [l275_mem_support, PEqualNP.CircuitLowerBounds.GateOp.eval, Bool.and_eq_true]
    have ha : l275Line i ⊆ l275Support pre a := hinter ▸ Finset.inter_subset_left
    have hb : l275Line i ⊆ l275Support pre b := hinter ▸ Finset.inter_subset_right
    have hca := Finset.card_le_card ha
    have hcb := Finset.card_le_card hb
    rw [l275_line_card] at hca hcb
    by_cases hsa : l275Support pre a ⊆ l275Line i
    · exact ⟨a, promote a (by omega) hsa⟩
    by_cases hsb : l275Support pre b ⊆ l275Line i
    · exact ⟨b, promote b (by omega) hsb⟩
    -- If each input sees an outside point, their pair turns the output on.
    obtain ⟨p, hp, hpout⟩ := Finset.not_subset.mp hsa
    obtain ⟨q, hq, hqout⟩ := Finset.not_subset.mp hsb
    have hpa : l275Val pre (l275Pair p q) a = true :=
      l275_val_mono pre hpre _ _ (by intro r hr; simp [l275Single, l275Pair] at hr ⊢; simp [hr])
        a ((l275_mem_support pre a p).mp hp)
    have hqb : l275Val pre (l275Pair p q) b = true :=
      l275_val_mono pre hpre _ _ (by intro r hr; simp [l275Single, l275Pair] at hr ⊢; simp [hr])
        b ((l275_mem_support pre b q).mp hq)
    have htrue : l275Val gs (l275Pair p q) o = true := by
      simp [hgate, hand, PEqualNP.CircuitLowerBounds.GateOp.eval, hpa, hqb]
    have hcard : (Finset.univ.filter (fun r => l275Pair p q r = true)).card ≤ 2 := by
      have he : Finset.univ.filter (fun r => l275Pair p q r = true) = {p, q} := by
        ext r
        simp [l275Pair]
      rw [he]
      by_cases hpq : p = q <;> simp [hpq]
    have hfalse := hpair (l275Pair p q) hcard (by
      intro r hr
      have hrp : r ≠ p := fun e => hpout (e ▸ hr)
      have hrq : r ≠ q := fun e => hqout (e ▸ hr)
      simp [l275Pair, hrp, hrq])
    rw [htrue] at hfalse
    contradiction
  · have hunion : l275Support pre a ∪ l275Support pre b = l275Line i := by
      ext p
      rw [← hone p, hgate, hor]
      simp [l275_mem_support, PEqualNP.CircuitLowerBounds.GateOp.eval, Bool.or_eq_true]
    by_cases ha : 2 ≤ (l275Support pre a).card
    · exact ⟨a, promote a ha (hunion ▸ Finset.subset_union_left)⟩
    have hb : 2 ≤ (l275Support pre b).card := by
      have he := Finset.card_union_add_card_inter (l275Support pre a) (l275Support pre b)
      rw [hunion, l275_line_card] at he
      omega
    exact ⟨b, promote b hb (hunion ▸ Finset.subset_union_right)⟩

theorem PEqualNP.Outside.L_meta_275 : ¬ ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin 4 → ℕ), C.size ≤ 7 ∧ (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ ∀ i : Fin 4, (∀ p : Fin 7, (C.wires (List.ofFn (fun q : Fin 7 => decide (q = p)))).getD (o i) false = true ↔ p ∈ (![{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}] : Fin 4 → Finset (Fin 7)) i) ∧ ∀ x : Fin 7 → Bool, (Finset.univ.filter (fun q : Fin 7 => x q = true)).card ≤ 2 → (∀ q ∈ (![{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}] : Fin 4 → Finset (Fin 7)) i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false := by
  rintro ⟨C, o, hsize, hgs, houtputs⟩
  change C.gates.length ≤ 7 at hsize
  have hone (i : Fin 4) (p : Fin 7) :
      l275Val C.gates (l275Single p) (o i) = true ↔ p ∈ l275Line i :=
    (houtputs i).1 p
  have hpair (i : Fin 4) (x : Fin 7 → Bool)
      (hx : (Finset.univ.filter (fun q => x q = true)).card ≤ 2)
      (hzero : ∀ q ∈ l275Line i, x q = false) :
      l275Val C.gates x (o i) = false :=
    (houtputs i).2 x hx hzero
  have hhelper (i : Fin 4) := l275_helper C.gates hgs (o i) i (hone i) (hpair i)
  choose a ha using hhelper
  have hout (i : Fin 4) : l275Support C.gates (o i) = l275Line i :=
    l275_support_out C.gates (o i) i (hone i)
  have houtcard (i : Fin 4) : 2 ≤ (l275Support C.gates (o i)).card := by
    rw [hout, l275_line_card]
    decide
  have houtpos (i : Fin 4) := l275_support_is_gate C.gates (o i) (houtcard i)
  let wire (i : Fin 4) (b : Bool) := if b then o i else a i
  have hw (i : Fin 4) (b : Bool) : 7 ≤ wire i b ∧ wire i b < 7 + C.gates.length ∧
      2 ≤ (l275Support C.gates (wire i b)).card ∧
      l275Support C.gates (wire i b) ⊆ l275Line i := by
    cases b
    · obtain ⟨hlo, hlt, hcard, hsub⟩ := ha i
      exact ⟨hlo, hlt.trans (houtpos i).2, hcard, hsub⟩
    · exact ⟨(houtpos i).1, (houtpos i).2, houtcard i, by simp [wire, hout]⟩
  have hline (i j : Fin 4) (b c : Bool) (he : wire i b = wire j c) : i = j := by
    by_contra hij
    have hsub : l275Support C.gates (wire i b) ⊆ l275Line i ∩ l275Line j :=
      Finset.subset_inter (hw i b).2.2.2 (he.symm ▸ (hw j c).2.2.2)
    have hcard := Finset.card_le_card hsub
    have hsmall := l275_line_inter i j hij
    have hbig := (hw i b).2.2.1
    omega
  let f : Fin 4 × Bool → Fin C.gates.length := fun q =>
    ⟨wire q.1 q.2 - 7, by
      have hlo := (hw q.1 q.2).1
      have hhi := (hw q.1 q.2).2.1
      omega⟩
  have hinj : Function.Injective f := by
    rintro ⟨i, b⟩ ⟨j, c⟩ he
    have he' := congrArg Fin.val he
    change wire i b - 7 = wire j c - 7 at he'
    have hwEq : wire i b = wire j c := by
      have hi := (hw i b).1
      have hj := (hw j c).1
      omega
    have hij := hline i j b c hwEq
    subst j
    have hbc : b = c := by
      have hlt := (ha i).2.1
      cases b <;> cases c <;> simp [wire] at hwEq ⊢ <;> omega
    subst c
    rfl
  have hcard := Fintype.card_le_of_injective f hinj
  simp at hcard
  omega
