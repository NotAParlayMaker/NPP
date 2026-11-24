import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3999

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Circuit builders (copied from PEqualNP.MetaComplexity.Helpers.Shannon and EdgeUpper).

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

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

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD (i : ℕ) false = x i := by simp

def Bld (n : ℕ) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length ≤ s ∧
    out < m + gs.length ∧ ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

theorem bld_mono {n : ℕ} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n F s) (hs : s ≤ s') :
    Bld n F s' := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, le_trans len hs, ho, ev⟩

theorem bld_congr {n : ℕ} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s)
    (e : ∀ x, F x = H x) : Bld n H s := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, len, ho, fun w hw => by rw [ev w hw, e]⟩

theorem bld_var {n : ℕ} (i : Fin n) : Bld n (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, by simp, le_rfl, by simp; omega, ?_⟩
  intro w _
  simp [wiresFrom]

theorem bld_bin {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
    {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1) (h2 : Bld n H s2) :
    Bld n (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
  intro m hm
  obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ := h1 m hm
  obtain ⟨gs2, o2, ok2, len2, ho2, ev2⟩ := h2 (m + gs1.length) (by omega)
  refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact ok1 g hg
    · exact ok2 g hg
    · subst hg; rcases hop with h | h <;> simp [Ok, h]
  · simp; omega
  · simp; omega
  · intro w hw
    rw [wiresFrom_append, wiresFrom_append]
    set v := wiresFrom gs1 w with hv
    have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
    set u := wiresFrom gs2 v with hu
    have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
    have step : wiresFrom [⟨op, [o1, o2]⟩] u
        = u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
    rw [step, ← lu, getD_snoc_eq]
    simp only [List.map_cons, List.map_nil, hc]
    have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
      rw [hu, getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
    have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
      rw [hu, ev2 v lv]
      congr 1
      funext i
      rw [hv, getD_wiresFrom _ _ _ (by have := i.2; omega)]
    rw [e1, e2]

theorem bld_or {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x || H x) (s1 + s2 + 1) :=
  bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_and {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x && H x) (s1 + s2 + 1) :=
  bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_hasCircuitSize {n : ℕ} {F : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s) :
    HasCircuitSize n F s := by
  obtain ⟨gs, out, ok, len, _, ev⟩ := h n le_rfl
  refine ⟨⟨gs, out⟩, ok, len, ?_⟩
  intro x
  have e := ev (List.ofFn x) (by simp)
  simp only [Circuit.eval, wires_eq, e]
  congr 1
  funext i
  exact getD_ofFn x i

theorem bld_anyList {n : ℕ} (vs : List (Fin n)) : ∀ v : Fin n,
    Bld n (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have := bld_or (bld_var v) (ih w)
    refine bld_congr (bld_mono this (by simp)) ?_
    intro x
    simp

theorem bld_anyFinset {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    Bld n (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
  obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
    cases h : S.toList with
    | nil => simp at h; exact absurd h hS.ne_empty
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
  refine bld_congr (bld_mono (bld_anyList vs v) (by omega)) ?_
  intro x
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
  simp

open Classical in
theorem bld_edges (n : ℕ) (T : Finset (Fin n)) : ∀ E : Finset (Sym2 (Fin n)), E.Nonempty →
    (∀ e ∈ E, ∃ t ∈ T, t ∈ e) →
    Bld n (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (E.card + T.card - 1) := by
  induction T using Finset.induction_on with
  | empty =>
    intro E hE hc
    obtain ⟨e, he⟩ := hE
    obtain ⟨t, ht, _⟩ := hc e he
    simp at ht
  | @insert t T0 htT ih =>
    intro E hE hc
    set E1 := E.filter (fun e => t ∈ e) with hE1
    set E2 := E.filter (fun e => t ∉ e) with hE2
    have hsplit : E1.card + E2.card = E.card := Finset.card_filter_add_card_filter_not _
    have hcard : (insert t T0).card = T0.card + 1 := Finset.card_insert_of_notMem htT
    have c2 : ∀ e ∈ E2, ∃ t' ∈ T0, t' ∈ e := by
      intro e he
      rw [hE2, Finset.mem_filter] at he
      obtain ⟨t', ht', hte⟩ := hc e he.1
      rcases Finset.mem_insert.1 ht' with h | h
      · subst h; exact absurd hte he.2
      · exact ⟨t', h, hte⟩
    -- the star at `t`
    set S := Finset.univ.filter (fun v : Fin n => s(t, v) ∈ E1) with hS
    have hSc : S.card ≤ E1.card := by
      refine Finset.card_le_card_of_injOn (fun v => s(t, v)) ?_ ?_
      · intro v hv
        simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
        exact hv
      · intro a _ b _ hab
        exact Sym2.congr_right.1 hab
    have star : E1.Nonempty → Bld n (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
        E1.card := by
      intro h1
      have hSne : S.Nonempty := by
        obtain ⟨e, he⟩ := h1
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        exact ⟨b, by simp [hS, ← hb, he]⟩
      have := bld_and (bld_var t) (bld_anyFinset S hSne)
      have hpos := hSne.card_pos
      refine bld_congr (bld_mono this (by omega)) ?_
      intro x
      rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
      constructor
      · rintro ⟨ht, v, hv, hxv⟩
        refine ⟨s(t, v), (Finset.mem_filter.1 hv).2, ?_⟩
        intro u hu
        rcases Sym2.mem_iff.1 hu with rfl | rfl <;> assumption
      · rintro ⟨e, he, hall⟩
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        subst hb
        exact ⟨hall t (Sym2.mem_mk_left _ _), b, by simp [hS, he],
          hall b (Sym2.mem_mk_right _ _)⟩
    have key : ∀ x : Fin n → Bool, decide (∃ e ∈ E, ∀ v ∈ e, x v = true)
        = (decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) || decide (∃ e ∈ E2, ∀ v ∈ e, x v = true)) := by
      intro x
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_iff, hE1, hE2, Finset.mem_filter]
      constructor
      · rintro ⟨e, he, h⟩
        by_cases hte : t ∈ e
        · exact Or.inl ⟨e, ⟨he, hte⟩, h⟩
        · exact Or.inr ⟨e, ⟨he, hte⟩, h⟩
      · rintro (⟨e, ⟨he, _⟩, h⟩ | ⟨e, ⟨he, _⟩, h⟩) <;> exact ⟨e, he, h⟩
    rw [hcard]
    by_cases h1 : E1.Nonempty
    · by_cases h2 : E2.Nonempty
      · have := bld_or (star h1) (ih E2 h2 c2)
        have hp := h2.card_pos
        refine bld_congr (bld_mono this (by omega)) ?_
        intro x
        rw [key]
      · rw [Finset.not_nonempty_iff_eq_empty] at h2
        refine bld_congr (bld_mono (star h1) (by omega)) ?_
        intro x
        rw [key, h2]
        simp
    · rw [Finset.not_nonempty_iff_eq_empty] at h1
      have h2 : E2.Nonempty := by
        by_contra h2
        rw [Finset.not_nonempty_iff_eq_empty] at h2
        have := hE.card_pos
        rw [h1, h2] at hsplit
        simp at hsplit
        omega
      refine bld_congr (bld_mono (ih E2 h2 c2) (by omega)) ?_
      intro x
      rw [key, h1]
      simp

theorem edge_upper : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)), (∃ i j : Fin n, G.Adj i j) → (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) (G.edgeFinset.card + T.card - 1) := by
  intro n G _ T hE hc
  obtain ⟨i0, j0, h0⟩ := hE
  have hne : G.edgeFinset.Nonempty := ⟨s(i0, j0), by simpa using h0⟩
  have cov : ∀ e ∈ G.edgeFinset, ∃ t ∈ T, t ∈ e := by
    intro e
    refine Sym2.ind (fun a b => ?_) e
    intro he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    rcases hc a b he with h | h
    · exact ⟨a, h, Sym2.mem_mk_left _ _⟩
    · exact ⟨b, h, Sym2.mem_mk_right _ _⟩
  apply bld_hasCircuitSize
  refine bld_congr (bld_edges n T G.edgeFinset hne cov) ?_
  intro x
  rw [decide_eq_decide]
  constructor
  · rintro ⟨e, he, h⟩
    revert he h
    refine Sym2.ind (fun a b => ?_) e
    intro he h
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact ⟨a, b, he, h a (Sym2.mem_mk_left _ _), h b (Sym2.mem_mk_right _ _)⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    refine ⟨s(i, j), by simpa using hij, ?_⟩
    intro v hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl <;> assumption


-- Graph part.

theorem fin2_odd : ∀ a b c d : Fin 2, a ≠ b → b ≠ c → c ≠ d → a ≠ d := by decide

theorem fin2_other : ∀ a b k : Fin 2, a ≠ b → a ≠ k → b = k := by decide

theorem walk_parity {n : ℕ} {G : SimpleGraph (Fin n)} (c : G.Coloring (Fin 2)) {x y : Fin n}
    (p : G.Walk x y) : ((c x).val + p.length) % 2 = (c y).val % 2 := by
  induction p with
  | nil => simp
  | @cons a b d h p ih =>
    have hv := c.valid h
    have hne : (c a).val ≠ (c b).val := fun e => hv (Fin.ext e)
    have h1 := (c a).isLt
    have h2 := (c b).isLt
    simp only [SimpleGraph.Walk.length_cons]
    omega

theorem cycle_of_two_paths {n : ℕ} {G : SimpleGraph (Fin n)} {x y : Fin n} (p q : G.Walk x y)
    (hp : p.IsPath) (hq : q.IsPath) (hpq : p ≠ q) :
    ∃ (v : Fin n) (c : G.Walk v v), c.IsCycle ∧ c.length ≤ p.length + q.length := by
  classical
  let s : Finset (Sym2 (Fin n)) := (p.edges ++ q.edges).toFinset
  let H : SimpleGraph (Fin n) := SimpleGraph.fromEdgeSet (s : Set (Sym2 (Fin n)))
  have hHs : ∀ e ∈ H.edgeSet, e ∈ s := by
    intro e he
    rw [SimpleGraph.edgeSet_fromEdgeSet] at he
    exact he.1
  have hHG : ∀ e ∈ H.edgeSet, e ∈ G.edgeSet := by
    intro e he
    have h1 := hHs e he
    simp only [s, List.mem_toFinset, List.mem_append] at h1
    rcases h1 with h1 | h1
    · exact p.edges_subset_edgeSet h1
    · exact q.edges_subset_edgeSet h1
  have hsH : ∀ e ∈ s, e ∈ G.edgeSet → e ∈ H.edgeSet := by
    intro e he hG
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨he, G.not_isDiag_of_mem_edgeSet hG⟩
  have hpH : ∀ e ∈ p.edges, e ∈ H.edgeSet := fun e he =>
    hsH e (by simp [s, he]) (p.edges_subset_edgeSet he)
  have hqH : ∀ e ∈ q.edges, e ∈ H.edgeSet := fun e he =>
    hsH e (by simp [s, he]) (q.edges_subset_edgeSet he)
  have back : ∀ {u w : Fin n} (r : H.Walk u w), ∀ e ∈ r.edges, e ∈ G.edgeSet :=
    fun r e he => hHG e (r.edges_subset_edgeSet he)
  have hnot : ¬ H.IsAcyclic := by
    intro hA
    have e1 := (SimpleGraph.isAcyclic_iff_subsingleton_path.1 hA x y).elim
      ⟨p.transfer H hpH, hp.transfer hpH⟩ ⟨q.transfer H hqH, hq.transfer hqH⟩
    have e2 := congrArg (fun r : H.Path x y => r.1.transfer G (back r.1)) e1
    simp only [SimpleGraph.Walk.transfer_transfer, SimpleGraph.Walk.transfer_self] at e2
    exact hpq e2
  simp only [SimpleGraph.IsAcyclic, not_forall, not_not] at hnot
  obtain ⟨v, c, hc⟩ := hnot
  refine ⟨v, c.transfer G (back c), hc.transfer (back c), ?_⟩
  rw [SimpleGraph.Walk.length_transfer, ← SimpleGraph.Walk.length_edges,
    ← List.toFinset_card_of_nodup hc.edges_nodup]
  calc c.edges.toFinset.card ≤ s.card := by
        apply Finset.card_le_card
        intro e he
        rw [List.mem_toFinset] at he
        exact hHs e (c.edges_subset_edgeSet he)
    _ ≤ (p.edges ++ q.edges).length := List.toFinset_card_le _
    _ = p.length + q.length := by simp

theorem path1 {n : ℕ} {G : SimpleGraph (Fin n)} {a b : Fin n} (h1 : G.Adj a b) :
    (SimpleGraph.Walk.cons h1 SimpleGraph.Walk.nil).IsPath := by
  rw [SimpleGraph.Walk.isPath_def]
  simp [G.ne_of_adj h1]

theorem path2 {n : ℕ} {G : SimpleGraph (Fin n)} {a b c : Fin n} (h1 : G.Adj a b)
    (h2 : G.Adj b c) (hac : a ≠ c) :
    (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil)).IsPath := by
  rw [SimpleGraph.Walk.isPath_def]
  simp [G.ne_of_adj h1, G.ne_of_adj h2, hac]

theorem path3 {n : ℕ} {G : SimpleGraph (Fin n)} {a b c d : Fin n} (h1 : G.Adj a b)
    (h2 : G.Adj b c) (h3 : G.Adj c d) (hac : a ≠ c) (hbd : b ≠ d) (had : a ≠ d) :
    (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2
      (SimpleGraph.Walk.cons h3 SimpleGraph.Walk.nil))).IsPath := by
  rw [SimpleGraph.Walk.isPath_def]
  simp [G.ne_of_adj h1, G.ne_of_adj h2, G.ne_of_adj h3, hac, hbd, had]

theorem key8 {n : ℕ} {G : SimpleGraph (Fin n)} (col : G.Coloring (Fin 2))
    (hcyc : ∀ (x6 : Fin n) (x7 : G.Walk x6 x6), x7.IsCycle → 7 ≤ x7.length) {x y : Fin n}
    (p q : G.Walk x y) (hp : p.IsPath) (hq : q.IsPath) (hpq : p ≠ q) :
    8 ≤ p.length + q.length := by
  obtain ⟨v, c, hc, hl⟩ := cycle_of_two_paths p q hp hq hpq
  have h7 := hcyc v c hc
  have hpar := walk_parity col c
  omega

theorem ball15 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (col : G.Coloring (Fin 2))
    (key : ∀ {x y : Fin n} (p q : G.Walk x y), p.IsPath → q.IsPath → p ≠ q →
      8 ≤ p.length + q.length)
    (hdeg : ∀ v, (G.neighborFinset v).card = 3) (w : Fin n) :
    ∃ S : Finset (Fin n), 15 ≤ S.card ∧ ∀ z ∈ S, col z ≠ col w := by
  classical
  let inner : Fin n → Finset (Fin n) := fun x =>
    ((G.neighborFinset x).erase w).biUnion (fun y => (G.neighborFinset y).erase x)
  have memi : ∀ x z, z ∈ inner x ↔ ∃ y, (y ≠ w ∧ G.Adj x y) ∧ z ≠ x ∧ G.Adj y z := by
    intro x z
    simp [inner]
  let S3 := (G.neighborFinset w).biUnion inner
  have cardi : ∀ x, G.Adj w x → (inner x).card = 4 := by
    intro x hx
    rw [Finset.card_biUnion]
    · rw [Finset.sum_congr rfl (g := fun _ => 2)]
      · rw [Finset.sum_const, Finset.card_erase_of_mem (by simpa using hx.symm), hdeg]
        rfl
      · intro y hy
        have hy' : G.Adj x y := by simpa using (Finset.mem_erase.1 hy).2
        rw [Finset.card_erase_of_mem (by simpa using hy'.symm), hdeg]
    · intro y1 hy1 y2 hy2 hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, SimpleGraph.mem_neighborFinset,
        Set.mem_singleton_iff] at hy1 hy2
      simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hz1 hz2
      have := key (SimpleGraph.Walk.cons hy1.1 (SimpleGraph.Walk.cons hz1.2 SimpleGraph.Walk.nil))
        (SimpleGraph.Walk.cons hy2.1 (SimpleGraph.Walk.cons hz2.2 SimpleGraph.Walk.nil))
        (path2 _ _ (Ne.symm hz1.1)) (path2 _ _ (Ne.symm hz2.1)) (by
          intro h
          have h' := congrArg SimpleGraph.Walk.support h
          simp at h'
          exact hne h')
      simp at this
  have hdisj3 : ∀ x1, G.Adj w x1 → ∀ x2, G.Adj w x2 → x1 ≠ x2 → ∀ z, z ∈ inner x1 → z ∉ inner x2 := by
    intro x1 hx1 x2 hx2 hne z hz1 hz2
    obtain ⟨y1, hy1, hz1⟩ := (memi x1 z).1 hz1
    obtain ⟨y2, hy2, hz2⟩ := (memi x2 z).1 hz2
    have hwz : w ≠ z := fin2_odd _ _ _ _ (col.valid hx1) (col.valid hy1.2) (col.valid hz1.2) ∘
      congrArg col
    have := key (SimpleGraph.Walk.cons hx1 (SimpleGraph.Walk.cons hy1.2
        (SimpleGraph.Walk.cons hz1.2 SimpleGraph.Walk.nil)))
      (SimpleGraph.Walk.cons hx2 (SimpleGraph.Walk.cons hy2.2
        (SimpleGraph.Walk.cons hz2.2 SimpleGraph.Walk.nil)))
      (path3 _ _ _ (Ne.symm hy1.1) (Ne.symm hz1.1) hwz)
      (path3 _ _ _ (Ne.symm hy2.1) (Ne.symm hz2.1) hwz) (by
        intro h
        have h' := congrArg SimpleGraph.Walk.support h
        simp at h'
        exact hne h'.1)
    simp at this
  have card3 : S3.card = 12 := by
    rw [Finset.card_biUnion]
    · rw [Finset.sum_congr rfl (g := fun _ => 4)]
      · rw [Finset.sum_const, hdeg]
        rfl
      · intro x hx
        exact cardi x (by simpa using hx)
    · intro x1 hx1 x2 hx2 hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      exact hdisj3 x1 (by simpa using hx1) x2 (by simpa using hx2) hne z hz1 hz2
  have hd : Disjoint (G.neighborFinset w) S3 := by
    rw [Finset.disjoint_left]
    intro z hz hz3
    rw [SimpleGraph.mem_neighborFinset] at hz
    obtain ⟨x, hx, hzx⟩ := Finset.mem_biUnion.1 hz3
    rw [SimpleGraph.mem_neighborFinset] at hx
    obtain ⟨y, hy, hz1⟩ := (memi x z).1 hzx
    have hwz : w ≠ z := fin2_odd _ _ _ _ (col.valid hx) (col.valid hy.2) (col.valid hz1.2) ∘
      congrArg col
    have := key (SimpleGraph.Walk.cons hz SimpleGraph.Walk.nil)
      (SimpleGraph.Walk.cons hx (SimpleGraph.Walk.cons hy.2
        (SimpleGraph.Walk.cons hz1.2 SimpleGraph.Walk.nil)))
      (path1 _) (path3 _ _ _ (Ne.symm hy.1) (Ne.symm hz1.1) hwz) (by
        intro h
        have h' := congrArg SimpleGraph.Walk.length h
        simp at h')
    simp at this
  refine ⟨G.neighborFinset w ∪ S3, by rw [Finset.card_union_of_disjoint hd, card3, hdeg], ?_⟩
  intro z hz
  rcases Finset.mem_union.1 hz with hz | hz
  · rw [SimpleGraph.mem_neighborFinset] at hz
    exact (col.valid hz).symm
  · obtain ⟨x, hx, hzx⟩ := Finset.mem_biUnion.1 hz
    rw [SimpleGraph.mem_neighborFinset] at hx
    obtain ⟨y, hy, hz1⟩ := (memi x z).1 hzx
    exact Ne.symm (fin2_odd _ _ _ _ (col.valid hx) (col.valid hy.2) (col.valid hz1.2))

theorem upd2 {n : ℕ} (x : Fin n → Bool) (a b i : Fin n) :
    Function.update (Function.update x a false) b false i = true ↔
      i ≠ a ∧ i ≠ b ∧ x i = true := by
  by_cases hb : i = b <;> by_cases ha : i = a <;> simp [Function.update_apply, ha, hb]

theorem main : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool), x2.Colorable (2 : ℕ) → (∀ (x5 : Fin x1), (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → (∀ (x8 : Fin x1 → Bool), x3 x8 = Bool.true ↔ ∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) → (30 : ℕ) ≤ x1 ∧ Even x1 ∧ ∃ (x9 : Fin x1) (x10 : Fin x1), x9 ≠ x10 ∧ ¬x2.Adj x9 x10 ∧ ∃ (x11 : ℕ), x11 + (9 : ℕ) ≤ (2 : ℕ) * x1 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x12 : Fin x1 → Bool) => x3 (Function.update (Function.update x12 x9 Bool.false) x10 Bool.false)) x11 := by
  intro n G f hcol hdeg0 hcyc hE hf
  classical
  obtain ⟨col⟩ := hcol
  have hdeg : ∀ v, (G.neighborFinset v).card = 3 := by
    intro v
    rw [← hdeg0 v, Set.ncard_eq_toFinset_card']
    rfl
  have hdeg' : ∀ v, G.degree v = 3 := fun v => by
    rw [← G.card_neighborFinset_eq_degree]; exact hdeg v
  have key : ∀ {x y : Fin n} (p q : G.Walk x y), p.IsPath → q.IsPath → p ≠ q →
      8 ≤ p.length + q.length := fun p q hp hq hpq => key8 col hcyc p q hp hq hpq
  obtain ⟨u, v, huv⟩ := hE
  have h30 : 30 ≤ n := by
    obtain ⟨Su, hSu, cSu⟩ := ball15 col key hdeg u
    obtain ⟨Sv, hSv, cSv⟩ := ball15 col key hdeg v
    have hd : Disjoint Su Sv := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      exact cSv z hz2 (fin2_other _ _ _ (col.valid huv) (Ne.symm (cSu z hz1))).symm
    have := Finset.card_le_univ (Su ∪ Sv)
    rw [Finset.card_union_of_disjoint hd, Fintype.card_fin] at this
    omega
  have hsum := G.sum_degrees_eq_twice_card_edges
  simp only [hdeg', Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  refine ⟨h30, ⟨G.edgeFinset.card - n, by omega⟩, ?_⟩
  obtain ⟨k, hk⟩ : ∃ k : Fin 2, 2 * (Finset.univ.filter (fun x => col x = k)).card ≤ n := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun x => col x = 0)
    have e : Finset.univ.filter (fun x => ¬ col x = 0) = Finset.univ.filter (fun x => col x = 1) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      generalize col x = c
      revert c
      decide
    rw [e, Finset.card_univ, Fintype.card_fin] at h
    by_cases h0 : 2 * (Finset.univ.filter (fun x => col x = 0)).card ≤ n
    · exact ⟨0, h0⟩
    · exact ⟨1, by omega⟩
  set A := Finset.univ.filter (fun x => col x = k) with hA
  obtain ⟨w, hw⟩ : ∃ w, col w ≠ k := by
    by_cases h : col u = k
    · exact ⟨v, fun h' => col.valid huv (h.trans h'.symm)⟩
    · exact ⟨u, h⟩
  have hNA : G.neighborFinset w ⊆ A := by
    intro z hz
    rw [SimpleGraph.mem_neighborFinset] at hz
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fin2_other (col w) (col z) k (col.valid hz) hw
  have hA3 : 3 ≤ A.card := hdeg w ▸ Finset.card_le_card hNA
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1
    (by rw [hdeg w]; norm_num : 1 < (G.neighborFinset w).card)
  have haA := hNA ha
  have hbA := hNA hb
  have hca : col a = k := by simpa [hA] using haA
  have hcb : col b = k := by simpa [hA] using hbA
  have hnadj : ¬ G.Adj a b := fun h => col.valid h (hca.trans hcb.symm)
  refine ⟨a, b, hab, hnadj, ?_⟩
  let G' : SimpleGraph (Fin n) :=
    { Adj := fun i j => G.Adj i j ∧ i ≠ a ∧ i ≠ b ∧ j ≠ a ∧ j ≠ b
      symm := ⟨fun i j h => ⟨h.1.symm, h.2.2.2.1, h.2.2.2.2, h.2.1, h.2.2.1⟩⟩
      loopless := ⟨fun i h => G.ne_of_adj h.1 rfl⟩ }
  let T := (A.erase a).erase b
  have hT : T.card + 2 = A.card := by
    have e1 := Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨Ne.symm hab, hbA⟩)
    have e2 := Finset.card_erase_of_mem haA
    simp only [T]
    omega
  have hIa : (G.incidenceFinset a).card = 3 := by
    rw [G.card_incidenceFinset_eq_degree, hdeg']
  have hIb : (G.incidenceFinset b).card = 3 := by
    rw [G.card_incidenceFinset_eq_degree, hdeg']
  have hmemI : ∀ (c : Fin n) (e : Sym2 (Fin n)), e ∈ G.incidenceFinset c ↔
      e ∈ G.edgeFinset ∧ c ∈ e := by
    intro c e
    rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.mem_edgeFinset]
    rfl
  have hd2 : Disjoint (G.incidenceFinset a) (G.incidenceFinset b) := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    rw [hmemI] at h1 h2
    have := (Sym2.mem_and_mem_iff hab).1 ⟨h1.2, h2.2⟩
    rw [this, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at h1
    exact hnadj h1.1
  have hd1 : Disjoint G'.edgeFinset (G.incidenceFinset a ∪ G.incidenceFinset b) := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    rw [Finset.mem_union, hmemI, hmemI] at h2
    revert h1 h2
    refine Sym2.ind (fun i j => ?_) e
    intro h1 h2
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at h1
    obtain ⟨_, h1a, h1b, h2a, h2b⟩ := h1
    rcases h2 with ⟨_, h⟩ | ⟨_, h⟩ <;> rcases Sym2.mem_iff.1 h with h | h <;> simp_all
  have hsub : G'.edgeFinset ⊆ G.edgeFinset := by
    intro e
    refine Sym2.ind (fun i j => ?_) e
    intro h
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at h ⊢
    exact h.1
  have hcard1 : G'.edgeFinset.card + 6 ≤ G.edgeFinset.card := by
    have := Finset.card_le_card (Finset.union_subset hsub (Finset.union_subset
      (G.incidenceFinset_subset a) (G.incidenceFinset_subset b)))
    rw [Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2, hIa, hIb] at this
    omega
  have hcard2 : G.edgeFinset.card ≤ G'.edgeFinset.card + 6 := by
    have hs : G.edgeFinset ⊆ G'.edgeFinset ∪ (G.incidenceFinset a ∪ G.incidenceFinset b) := by
      intro e
      refine Sym2.ind (fun i j => ?_) e
      intro h
      rw [Finset.mem_union, Finset.mem_union, hmemI, hmemI, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet]
      have h' := h
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at h'
      by_cases hia : i = a
      · subst hia; exact Or.inr (Or.inl ⟨h, Sym2.mem_mk_left _ _⟩)
      by_cases hja : j = a
      · subst hja; exact Or.inr (Or.inl ⟨h, Sym2.mem_mk_right _ _⟩)
      by_cases hib : i = b
      · subst hib; exact Or.inr (Or.inr ⟨h, Sym2.mem_mk_left _ _⟩)
      by_cases hjb : j = b
      · subst hjb; exact Or.inr (Or.inr ⟨h, Sym2.mem_mk_right _ _⟩)
      exact Or.inl ⟨h', hia, hib, hja, hjb⟩
    have h1 := Finset.card_le_card hs
    have h2 := Finset.card_union_le G'.edgeFinset (G.incidenceFinset a ∪ G.incidenceFinset b)
    have h3 := Finset.card_union_le (G.incidenceFinset a) (G.incidenceFinset b)
    omega
  have hEdge : ∃ i j : Fin n, G'.Adj i j := by
    obtain ⟨e, he⟩ := Finset.card_pos.1 (by omega : 0 < G'.edgeFinset.card)
    revert he
    refine Sym2.ind (fun i j => ?_) e
    intro he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact ⟨i, j, he⟩
  have hcov : ∀ i j : Fin n, G'.Adj i j → i ∈ T ∨ j ∈ T := by
    intro i j h
    obtain ⟨hij, hia, hib, hja, hjb⟩ := h
    by_cases hi : col i = k
    · left
      simp only [T, Finset.mem_erase, hA, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hib, hia, hi⟩
    · right
      simp only [T, Finset.mem_erase, hA, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hjb, hja, fin2_other _ _ _ (col.valid hij) hi⟩
  have hc := edge_upper n G' T hEdge hcov
  refine ⟨G'.edgeFinset.card + T.card - 1, by omega, ?_⟩
  have hfun : (fun x : Fin n → Bool => f (Function.update (Function.update x a false) b false))
      = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G'.Adj i j ∧ x i = true ∧ x j = true)) := by
    funext x
    rw [Bool.eq_iff_iff, hf, decide_eq_true_iff]
    simp only [upd2]
    constructor
    · rintro ⟨i, j, h, ⟨hia, hib, hi⟩, ⟨hja, hjb, hj⟩⟩
      exact ⟨i, j, ⟨h, hia, hib, hja, hjb⟩, hi, hj⟩
    · rintro ⟨i, j, ⟨h, hia, hib, hja, hjb⟩, hi, hj⟩
      exact ⟨i, j, h, ⟨hia, hib, hi⟩, ⟨hja, hjb, hj⟩⟩
  rw [hfun]
  convert hc

end PEqualNP.Outside.L_meta_3999

theorem PEqualNP.Outside.L_meta_3999 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool), x2.Colorable (2 : ℕ) → (∀ (x5 : Fin x1), (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → (∀ (x8 : Fin x1 → Bool), x3 x8 = Bool.true ↔ ∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) → (30 : ℕ) ≤ x1 ∧ Even x1 ∧ ∃ (x9 : Fin x1) (x10 : Fin x1), x9 ≠ x10 ∧ ¬x2.Adj x9 x10 ∧ ∃ (x11 : ℕ), x11 + (9 : ℕ) ≤ (2 : ℕ) * x1 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x12 : Fin x1 → Bool) => x3 (Function.update (Function.update x12 x9 Bool.false) x10 Bool.false)) x11 :=
  PEqualNP.Outside.L_meta_3999.main
