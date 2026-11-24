import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1975

-- Builder for AND/OR circuits adapted from the accepted proof L-meta-1003.

open PEqualNP PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds

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

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

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

theorem edge_bld (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (hE : ∃ i j : Fin n, G.Adj i j) (hc : ∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) :
    Bld n (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true))
      (G.edgeFinset.card + T.card - 1) := by
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

theorem upper (n : ℕ) (G : SimpleGraph (Fin n)) (S T : Finset (Fin n))
    (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hne : S.Nonempty ∨ ∃ (i : Fin n) (j : Fin n), G.Adj i j)
    (hc : ∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T)
    (hs : s + 1 = S.card + G.edgeSet.ncard + T.card)
    (hf : ∀ x : Fin n → Bool, f x = true ↔ (∃ v ∈ S, x v = true) ∨
      ∃ (i : Fin n) (j : Fin n), G.Adj i j ∧ x i = true ∧ x j = true) :
    HasCircuitSize n f s := by
  classical
  have hcard : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [hcard] at hs
  have key : ∀ x : Fin n → Bool, f x = (decide (∃ v ∈ S, x v = true) ||
      decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) := by
    intro x
    rw [Bool.eq_iff_iff, hf x]
    simp only [Bool.or_eq_true, decide_eq_true_iff]
  apply bld_hasCircuitSize
  by_cases hE : ∃ i j : Fin n, G.Adj i j
  · have hEc : 0 < G.edgeFinset.card := by
      obtain ⟨i0, j0, h0⟩ := hE
      exact Finset.card_pos.2 ⟨s(i0, j0), by simpa using h0⟩
    by_cases hS : S.Nonempty
    · have hSc := hS.card_pos
      have := bld_or (bld_anyFinset S hS) (edge_bld n G T hE hc)
      refine bld_congr (bld_mono this (by omega)) ?_
      intro x
      rw [key x]
    · rw [Finset.not_nonempty_iff_eq_empty] at hS
      subst hS
      simp only [Finset.card_empty, zero_add] at hs
      refine bld_congr (bld_mono (edge_bld n G T hE hc) (by omega)) ?_
      intro x
      rw [key x]
      simp
  · have hS : S.Nonempty := by
      rcases hne with h | h
      · exact h
      · exact absurd h hE
    have hSc := hS.card_pos
    refine bld_congr (bld_mono (bld_anyFinset S hS) (by omega)) ?_
    intro x
    rw [key x]
    have : ¬ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true := by
      rintro ⟨i, j, h, -, -⟩
      exact hE ⟨i, j, h⟩
    simp [this]


-- Lower bound side: in a least circuit every gate but the output is read by some gate,
-- and every input the function depends on is read by some gate.

theorem wiresFrom_cons (g : Gate) (L : List Gate) (W : List Bool) :
    wiresFrom (g :: L) W
      = wiresFrom L (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]) := rfl

def sh (K i : ℕ) : ℕ := if i < K then i else i - 1

theorem getD_sh (W : List Bool) (K i : ℕ) (h : i ≠ K) :
    (W.eraseIdx K).getD (sh K i) false = W.getD i false := by
  unfold sh
  by_cases hi : i < K
  · simp only [hi, ite_true, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eraseIdx_of_lt hi]
  · simp only [hi, ite_false, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eraseIdx_of_ge (by omega)]
    have : i - 1 + 1 = i := by omega
    rw [this]

def shG (K : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sh K)⟩

theorem wiresFrom_erase (K : ℕ) : ∀ (L : List Gate) (W : List Bool), K < W.length →
    (∀ g ∈ L, K ∉ g.inputs) →
    wiresFrom (L.map (shG K)) (W.eraseIdx K) = (wiresFrom L W).eraseIdx K := by
  intro L
  induction L with
  | nil => intro W _ _; rfl
  | cons g L ih =>
    intro W hK hL
    have hg : K ∉ g.inputs := hL g List.mem_cons_self
    have hval : (g.inputs.map (sh K)).map (fun i => (W.eraseIdx K).getD i false)
        = g.inputs.map (fun i => W.getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i hi
      exact getD_sh W K i (by rintro rfl; exact hg hi)
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons]
    have e1 : (shG K g).op = g.op := rfl
    have e2 : (shG K g).inputs = g.inputs.map (sh K) := rfl
    rw [e1, e2, hval, ← List.eraseIdx_append_of_lt_length hK]
    exact ih _ (by simp; omega) (fun g' hg' => hL g' (List.mem_cons_of_mem _ hg'))

theorem delete_unread (N : ℕ) (C : Circuit) (p : ℕ) (hp : p < C.gates.length)
    (ho : C.output ≠ N + p) (hu : ∀ g ∈ C.gates, N + p ∉ g.inputs) (hfan : FanInTwo C) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 1 = C.size ∧ circuitFun N D = circuitFun N C := by
  refine ⟨⟨C.gates.take p ++ (C.gates.drop (p + 1)).map (shG (N + p)), sh (N + p) C.output⟩,
    ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · exact hfan g (List.mem_of_mem_take h)
    · obtain ⟨g', hg', rfl⟩ := List.mem_map.1 h
      have := hfan g' (List.mem_of_mem_drop hg')
      exact ⟨this.1, by simpa [shG] using this.2⟩
  · simp only [Circuit.size, List.length_append, List.length_map, List.length_take,
      List.length_drop]
    omega
  · funext x
    have hsplit : C.gates = C.gates.take p ++ C.gates[p] :: C.gates.drop (p + 1) := by
      simp only [List.cons_getElem_drop_succ, List.take_append_drop]
    have hW0 : (wiresFrom (C.gates.take p) (List.ofFn x)).length = N + p := by
      rw [length_wiresFrom]; simp; omega
    simp only [circuitFun, Circuit.eval, wires_eq]
    rw [wiresFrom_append]
    conv => rhs; rw [hsplit, wiresFrom_append, wiresFrom_cons]
    set W0 := wiresFrom (C.gates.take p) (List.ofFn x)
    set b := C.gates[p].op.eval (C.gates[p].inputs.map fun i => W0.getD i false)
    have hW : W0 = (W0 ++ [b]).eraseIdx (N + p) := by
      rw [List.eraseIdx_append_of_length_le (by omega)]; simp [hW0]
    have key : wiresFrom ((C.gates.drop (p + 1)).map (shG (N + p))) W0
        = (wiresFrom (C.gates.drop (p + 1)) (W0 ++ [b])).eraseIdx (N + p) := by
      have := wiresFrom_erase (N + p) (C.gates.drop (p + 1)) (W0 ++ [b]) (by simp; omega)
        (fun g hg => hu g (List.mem_of_mem_drop hg))
      rwa [← hW] at this
    rw [key]
    exact getD_sh _ _ _ ho

theorem wiresFrom_agree (a : ℕ) : ∀ (L : List Gate) (W W' : List Bool), W.length = W'.length →
    (∀ i, i ≠ a → W.getD i false = W'.getD i false) → (∀ g ∈ L, a ∉ g.inputs) →
    ∀ i, i ≠ a → (wiresFrom L W).getD i false = (wiresFrom L W').getD i false := by
  intro L
  induction L with
  | nil => intro W W' _ h _; exact h
  | cons g L ih =>
    intro W W' hl h hL
    rw [wiresFrom_cons, wiresFrom_cons]
    have hg : a ∉ g.inputs := hL g List.mem_cons_self
    have hv : g.inputs.map (fun i => W.getD i false) = g.inputs.map (fun i => W'.getD i false) :=
      List.map_congr_left (fun i hi => h i (by rintro rfl; exact hg hi))
    rw [hv]
    apply ih _ _ (by simp [hl])
    · intro i hi
      by_cases hiW : i < W.length
      · rw [List.getD_append _ _ _ _ hiW, List.getD_append _ _ _ _ (hl ▸ hiW)]
        exact h i hi
      · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega),
          hl]
    · exact fun g' hg' => hL g' (List.mem_cons_of_mem _ hg')

theorem unread_var (N : ℕ) (C : Circuit) (a : Fin N) (hu : ∀ g ∈ C.gates, (a : ℕ) ∉ g.inputs)
    (ho : C.output ≠ a) (x : Fin N → Bool) (b : Bool) :
    circuitFun N C (Function.update x a b) = circuitFun N C x := by
  simp only [circuitFun, Circuit.eval, wires_eq]
  apply wiresFrom_agree a C.gates _ _ (by simp) _ hu _ ho
  intro i hi
  by_cases hiN : i < N
  · have h1 := getD_ofFn (Function.update x a b) ⟨i, hiN⟩
    have h2 := getD_ofFn x ⟨i, hiN⟩
    simp only at h1 h2
    rw [h1, h2, Function.update_of_ne]
    intro he
    exact hi (by rw [← he])
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem output_var (N : ℕ) (C : Circuit) (a : Fin N) (ho : C.output = a) (x : Fin N → Bool) :
    circuitFun N C x = x a := by
  simp only [circuitFun, Circuit.eval, wires_eq]
  rw [ho, getD_wiresFrom _ _ _ (by simp), getD_ofFn]

def cnt (gs : List Gate) (i : ℕ) : ℕ := gs.countP (fun g => decide (i ∈ g.inputs))

theorem sum_cnt_le (I : Finset ℕ) : ∀ gs : List Gate, (∀ g ∈ gs, g.inputs.length ≤ 2) →
    ∑ i ∈ I, cnt gs i ≤ 2 * gs.length := by
  intro gs
  induction gs with
  | nil => intro _; simp [cnt]
  | cons g gs ih =>
    intro h
    have h1 := ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
    have h2 : ∑ i ∈ I, (if i ∈ g.inputs then 1 else 0) ≤ 2 := by
      rw [Finset.sum_boole]
      calc ((I.filter (fun i => i ∈ g.inputs)).card : ℕ) ≤ g.inputs.toFinset.card := by
            apply Finset.card_le_card
            intro i hi
            simp only [Finset.mem_filter] at hi
            simpa using hi.2
        _ ≤ g.inputs.length := List.toFinset_card_le _
        _ ≤ 2 := h g List.mem_cons_self
    have e : ∀ i, cnt (g :: gs) i = cnt gs i + (if i ∈ g.inputs then 1 else 0) := by
      intro i
      simp only [cnt, List.countP_cons, decide_eq_true_eq]
    simp only [e, Finset.sum_add_distrib, List.length_cons]
    omega

theorem vac (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1))
    (x4 : (Fin x1 → Bool) → Bool) (x5 : Circuit)
    (hDeg : ∀ x6 ∉ x3, (x2.neighborSet x6).ncard = 3)
    (hDisj : ∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3)
    (hEdge : ∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10)
    (hF : ∀ (x10 : Fin x1 → Bool), x4 x10 = true ↔ (∃ x11 ∈ x3, x10 x11 = true) ∨
      ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = true ∧ x10 x12 = true)
    (hFan : FanInTwo x5) (hFun : circuitFun x1 x5 = x4)
    (hMin : ∀ (x13 : ℕ), HasCircuitSize x1 x4 x13 → x5.size ≤ x13)
    (hRead : ∀ v ∉ x3, 3 ≤ cnt x5.gates v) : False := by
  classical
  set T : Finset (Fin x1) := Finset.univ.filter (fun v => v ∉ x3) with hT
  set S := x5.gates.length with hS
  obtain ⟨u0, w0, huw⟩ := hEdge
  have hu0 : u0 ∉ x3 := hDisj _ _ huw
  have hw0 : w0 ∉ x3 := hDisj _ _ huw.symm
  have hm : 1 ≤ T.card := Finset.card_pos.2 ⟨u0, by simp [hT, hu0]⟩
  -- handshake: twice the edges is three times the cubic vertices
  have hdeg : ∀ v, x2.degree v = if v ∈ x3 then 0 else 3 := by
    intro v
    split_ifs with hv
    · rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero]
      apply Finset.eq_empty_of_forall_notMem
      intro w hw
      rw [SimpleGraph.mem_neighborFinset] at hw
      exact hDisj _ _ hw hv
    · rw [← SimpleGraph.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]
      exact hDeg v hv
  have hhand : 2 * x2.edgeSet.ncard = 3 * T.card := by
    have h := SimpleGraph.sum_degrees_eq_twice_card_edges x2
    have hc : x2.edgeSet.ncard = x2.edgeFinset.card := by
      rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    rw [hc, ← h]
    simp only [hdeg]
    rw [Finset.sum_ite]
    simp [hT, mul_comm]
  -- upper bound
  have hup : HasCircuitSize x1 x4 (x3.card + x2.edgeSet.ncard + T.card - 1) := by
    apply upper x1 x2 x3 T x4 _ (Or.inr ⟨u0, w0, huw⟩)
    · intro i j hij
      left
      simp [hT, hDisj _ _ hij]
    · omega
    · exact hF
  have hSup := hMin _ hup
  simp only [Circuit.size] at hSup
  -- lower bound by counting reads
  have hsum := sum_cnt_le (Finset.range (x1 + S)) x5.gates (fun g hg => (hFan g hg).2)
  rw [Finset.sum_range_add, ← Fin.sum_univ_eq_sum_range] at hsum
  have hA : ∀ a ∈ x3, 1 ≤ cnt x5.gates a := by
    intro a ha
    by_contra hc
    have h0 : cnt x5.gates a = 0 := by omega
    have hu : ∀ g ∈ x5.gates, (a : ℕ) ∉ g.inputs := by
      intro g hg hm'
      have := (List.countP_eq_zero.1 h0) g hg
      simp [hm'] at this
    by_cases ho : x5.output = a
    · have h1 := output_var x1 x5 a ho (fun i => decide (i = u0 ∨ i = w0))
      rw [hFun] at h1
      have h2 : x4 (fun i => decide (i = u0 ∨ i = w0)) = true :=
        (hF _).2 (Or.inr ⟨u0, w0, huw, by simp, by simp⟩)
      rw [h1] at h2
      have hau : a ≠ u0 := by rintro rfl; exact hu0 ha
      have haw : a ≠ w0 := by rintro rfl; exact hw0 ha
      simp [hau, haw] at h2
    · have h1 := unread_var x1 x5 a hu ho (fun _ => false) true
      rw [hFun] at h1
      have h2 : x4 (Function.update (fun _ => false) a true) = true :=
        (hF _).2 (Or.inl ⟨a, ha, by simp⟩)
      rw [h1] at h2
      rcases (hF _).1 h2 with ⟨_, _, h⟩ | ⟨_, _, _, h, _⟩ <;> simp at h
  have hG : ∀ p ∈ Finset.range S,
      1 ≤ cnt x5.gates (x1 + p) + (if x1 + p = x5.output then 1 else 0) := by
    intro p hp
    rw [Finset.mem_range] at hp
    by_cases ho : x1 + p = x5.output
    · simp [ho]
    · by_contra hc
      have h0 : cnt x5.gates (x1 + p) = 0 := by simp [ho] at hc; omega
      have hu : ∀ g ∈ x5.gates, x1 + p ∉ g.inputs := by
        intro g hg hm'
        have := (List.countP_eq_zero.1 h0) g hg
        simp [hm'] at this
      obtain ⟨D, hD, hDs, hDf⟩ := delete_unread x1 x5 p hp (Ne.symm ho) hu hFan
      have : HasCircuitSize x1 x4 (S - 1) := by
        refine ⟨D, hD, ?_, ?_⟩
        · simp only [Circuit.size] at hDs ⊢; omega
        · intro x
          rw [← hFun]
          exact congrFun hDf x
      have := hMin _ this
      simp only [Circuit.size] at this
      omega
  have hG2 := Finset.sum_le_sum hG
  rw [Finset.sum_add_distrib] at hG2
  have hone : ∑ p ∈ Finset.range S, (if x1 + p = x5.output then 1 else 0) ≤ 1 := by
    rw [Finset.sum_boole]
    simp only [Nat.cast_id]
    apply Finset.card_le_one.2
    intro p hp q hq
    simp only [Finset.mem_filter] at hp hq
    omega
  have hV : ∑ v : Fin x1, (if v ∈ x3 then 1 else 3) ≤ ∑ v : Fin x1, cnt x5.gates v := by
    apply Finset.sum_le_sum
    intro v _
    split_ifs with hv
    · exact hA v hv
    · exact hRead v hv
  have hV2 : ∑ v : Fin x1, (if v ∈ x3 then 1 else 3) = x3.card + 3 * T.card := by
    rw [Finset.sum_ite]
    simp [hT, mul_comm]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at hG2
  omega

end PEqualNP.Outside.L_meta_1975

theorem PEqualNP.Outside.L_meta_1975 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       x16.length = (3 : ℕ) ∧ ∀ x17 ∈ x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.or) →                     ∃ x15 ∉ x3, ∃ (x16 : ℕ), x16 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x4 (Function.update x17 x15 Bool.false)) x16 := by
  intro x1 x2 x3 x4 x5 hDeg _ hDisj hEdge hF hFan hFun hMin hRead
  apply False.elim
  apply PEqualNP.Outside.L_meta_1975.vac x1 x2 x3 x4 x5 hDeg hDisj hEdge hF hFan hFun hMin
  intro v hv
  have h3 := (hRead v hv).1
  unfold PEqualNP.Outside.L_meta_1975.cnt
  rw [← h3, ← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro g _ hg
  simp only [List.contains_iff_mem, decide_eq_true_eq] at hg ⊢
  exact List.mem_of_mem_take hg
