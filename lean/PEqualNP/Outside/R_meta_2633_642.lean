import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

-- The cover construction and effective port counting build on L-meta-4861, L-meta-4863
-- and R-meta-2629-318. Here the shared gate outputs are charged to their at most two raw inputs.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 12000 in
theorem PEqualNP.Outside.R_meta_2633_642
  (portBound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
    let rd := fun (g : Gate) => g.inputs.take (bif g.op.eval [false] then 1 else 2)
    let count := fun j : ℕ => (C.output :: C.gates.flatMap rd).count (n+j)
    let shared : Finset (Fin C.gates.length) := Finset.univ.filter (fun j => 1 < count j.val)
    FanInTwo C → circuitFun n C = NestedCover.graphFun G A →
    (∀ s, HasCircuitSize n (NestedCover.graphFun G A) s → C.size ≤ s) →
    A.card + (∑ a ∈ Aᶜ, (C.gates.filter (fun g => (rd g).contains a.val)).length) +
      shared.card +
      (C.gates.filter fun g => g.op.eval [false]).length ≤ C.size + 1)
  (privateCycle : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
    let rd := fun (g : Gate) => g.inputs.take (bif g.op.eval [false] then 1 else 2)
    let reads := fun v : Fin n => C.gates.filter (fun g => (rd g).contains v.val)
    let use := fun j : ℕ => (C.output :: C.gates.flatMap rd).count (n+j)
    let S := {v : Fin n | v ∉ A ∧ (reads v).length = 2 ∧ ∀ j : Fin C.gates.length,
      v.val ∈ rd (C.gates.get j) → use j.val ≤ 1}
    (∀ v ∉ A, (G.neighborSet v).ncard = 3) → (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
    (∀ u v, G.Adj u v → u ∉ A) → IsMinimalCircuit n C →
    circuitFun n C = NestedCover.graphFun G A →
    (∀ v ∉ A, 2 ≤ (reads v).length ∧ (reads v).length ≤ 3 ∧ ∀ g ∈ reads v, g.op = .or) →
    (∀ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) →
      C.size+1 < A.card + G.edgeFinset.card + T.card) →
    (∀ Z : Finset (Fin n), Z.card ≤ (Aᶜ.filter fun v => (reads v).length = 3).card +
      2*(C.gates.filter fun g => g.op.eval [false]).length → ¬(G.induce (S \ ↑Z)).Colorable 2) →
    ∃ v ∉ A, ∃ s, s+4 ≤ C.size ∧ HasCircuitSize n (fun x => NestedCover.graphFun G A (Function.update x v false)) s) : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [_x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∀ x16 ∉ x4, ∀ x18 ∈ x7 x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∃ x17 ∉ x4, (x7 x17).length = (2 : ℕ)) → ∃ x18 ∉ x4, ∃ (x19 : ℕ), x19 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x20 : Fin x1 → Bool) => x6 (Function.update x20 x18 Bool.false)) x19 := by
  let portRD (g : Gate) := g.inputs.take (bif g.op.eval [false] then 1 else 2)
  have budgetBranch {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit)
      (deg : ∀ v ∉ A, (G.neighborSet v).ncard = 3) (unmarked : ∀ v w, G.Adj v w → v ∉ A)
      (edge : ∃ v w, G.Adj v w) (fan : FanInTwo C) (computes : circuitFun n C = NestedCover.graphFun G A)
      (minimal : ∀ s, HasCircuitSize n (NestedCover.graphFun G A) s → C.size ≤ s)
      (reads : Fin n → ℕ)
      (hr : reads = fun a => (C.gates.filter fun g => (portRD g).contains a.val).length)
      (hread : ∀ a ∉ A, 2 ≤ reads a ∧ reads a ≤ 3)
      (I : Finset (Fin n)) (hsub : I ⊆ Aᶜ) (hind : ∀ u ∈ I, ∀ v ∈ I, ¬G.Adj u v)
      (budget : Aᶜ.card ≤ 2*(I.card + (Aᶜ.filter (fun v => reads v = 3)).card +
        (Finset.univ.filter (fun j : Fin C.gates.length =>
          1 < (C.output :: C.gates.flatMap portRD).count (n+j.val))).card + (C.gates.filter fun g => g.op.eval [false]).length)
        ∨ A.card + G.edgeFinset.card + (Aᶜ \ I).card ≤ C.size+1) :
      ∃ v ∉ A, ∃ s, s+4 ≤ C.size ∧ HasCircuitSize n (fun x => NestedCover.graphFun G A (Function.update x v false)) s := by
    classical
    have evAnd (l : List Bool) : GateOp.and.eval l = l.all id := rfl
    have evOr (l : List Bool) : GateOp.or.eval l = l.any id := rfl
    have evNot (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl
    have evSize (K : Circuit) : K.size = K.gates.length := rfl
    have evCirc (K : Circuit) (w : List Bool) : K.eval w = (K.wires w).getD K.output false := rfl
    have evGraph {m : ℕ} (K : SimpleGraph (Fin m)) [DecidableRel K.Adj] (M : Finset (Fin m))
        (x : Fin m → Bool) : NestedCover.graphFun K M x =
          (decide (∃ a ∈ M, x a = true) || decide (∃ a b, K.Adj a b ∧ x a = true ∧ x b = true)) := rfl
    let F (w : List Bool) (g : Gate) : List Bool := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

    have buildWiresEq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

    have wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
        wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
      simp [wiresFrom, List.foldl_append]

    have wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
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

    have length_wiresFrom (gs : List Gate) (w : List Bool) :
        (wiresFrom gs w).length = w.length + gs.length := by
      obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
      rw [ht]; simp [hl]

    have getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
        (wiresFrom gs w).getD i false = w.getD i false := by
      obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
      rw [ht, List.getD_append _ _ _ _ h]

    let Ok (g : Gate) : Prop :=
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2


    have getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
      simp


    have getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
        (List.ofFn x).getD (i : ℕ) false = x i := by simp


    let Bld (n : ℕ) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
      ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length ≤ s ∧
        out < m + gs.length ∧ ∀ w : List Bool, w.length = m →
          (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

    have bld_mono {n : ℕ} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n F s) (hs : s ≤ s') :
        Bld n F s' := by
      intro m hm
      obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
      exact ⟨gs, out, ok, le_trans len hs, ho, ev⟩

    have bld_congr {n : ℕ} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s)
        (e : ∀ x, F x = H x) : Bld n H s := by
      intro m hm
      obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
      exact ⟨gs, out, ok, len, ho, fun w hw => by rw [ev w hw, e]⟩

    have bld_var {n : ℕ} (i : Fin n) : Bld n (fun x => x i) 0 := by
      intro m hm
      refine ⟨[], i, by simp, le_rfl, by simp; omega, ?_⟩
      intro w _
      simp [wiresFrom]

    have bld_bin {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
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

    have bld_or {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
        (h2 : Bld n H s2) : Bld n (fun x => F x || H x) (s1 + s2 + 1) :=
      bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [evOr]) h1 h2

    have bld_and {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
        (h2 : Bld n H s2) : Bld n (fun x => F x && H x) (s1 + s2 + 1) :=
      bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [evAnd]) h1 h2

    have bld_hasCircuitSize {n : ℕ} {F : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s) :
        HasCircuitSize n F s := by
      obtain ⟨gs, out, ok, len, _, ev⟩ := h n le_rfl
      refine ⟨⟨gs, out⟩, ok, len, ?_⟩
      intro x
      have e := ev (List.ofFn x) (by simp)
      simp only [evCirc, buildWiresEq, e]
      congr 1
      funext i
      exact getD_ofFn x i

    clear_value Bld

    have bld_anyList {n : ℕ} (vs : List (Fin n)) : ∀ v : Fin n,
        Bld n (fun x => (v :: vs).any fun j => x j) vs.length := by
      induction vs with
      | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
      | cons w ws ih =>
        intro v
        have := bld_or (bld_var v) (ih w)
        refine bld_congr (bld_mono this (by simp)) ?_
        intro x
        simp

    have bld_anyFinset {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
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



    have bld_edges (n : ℕ) (T : Finset (Fin n)) : ∀ E : Finset (Sym2 (Fin n)), E.Nonempty →
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

    have edgeBuilder : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)), (∃ i j : Fin n, G.Adj i j) → (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → Bld n (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) (G.edgeFinset.card + T.card - 1) := by
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




    have markedUpper {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (A T : Finset (Fin n)) (f : (Fin n → Bool) → Bool)
        (hE : ∃ i j, G.Adj i j) (cover : ∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T)
        (hf : ∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) :
        HasCircuitSize n f (A.card + G.edgeFinset.card + T.card - 1) := by
      classical
      have b := edgeBuilder n G T hE cover
      obtain ⟨i,j,hij⟩ := hE
      have epos : 0 < G.edgeFinset.card := Finset.card_pos.mpr ⟨s(i,j),by simpa using hij⟩
      apply bld_hasCircuitSize
      by_cases ha : A.Nonempty
      · have ap := ha.card_pos
        apply bld_congr (bld_mono (bld_or (bld_anyFinset A ha) b) (by omega))
        intro x
        rw [Bool.eq_iff_iff, hf]
        simp
      · have he := Finset.not_nonempty_iff_eq_empty.mp ha
        apply bld_congr (bld_mono b (by simp [he]))
        intro x
        rw [Bool.eq_iff_iff, hf]
        simp [he]





    have dropLemma : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [_x3 : DecidableRel x2.Adj] (x4 x5 : Finset (Fin x1)) (x6 : Fin x1), (∀ x7 ∉ x4, (x2.neighborSet x7).ncard = (3 : ℕ)) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x4) → x5 ⊆ x4ᶜ → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∈ x5 ∨ x11 ∈ x5) → x6 ∈ x5 → ∃ (x12 : ℕ), x12 + (5 : ℕ) ≤ x4.card + x2.edgeFinset.card + x5.card ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x13 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 (Function.update x13 x6 Bool.false)) x12 := by
      classical
      intro n G inst A T v deg unmarked sub cover hv
      let H := G.deleteIncidenceSet v
      have huv : v ∉ A := Finset.mem_compl.mp (sub hv)
      have hd : G.degree v = 3 := by rw [← G.ncard_neighborSet]; exact deg v huv
      have hedge : ∃ i j, H.Adj i j := by
        have hpos : 0 < (G.neighborFinset v).card := by simpa using hd ▸ (show 0 < 3 by decide)
        obtain ⟨w,hw⟩ := Finset.card_pos.mp hpos
        have hvw := (G.mem_neighborFinset v w).mp hw
        have hwv := hvw.symm
        have hdw : G.degree w = 3 := by rw [← G.ncard_neighborSet]; exact deg w (unmarked w v hwv)
        by_contra! h
        have hsub : G.neighborFinset w ⊆ {v} := by
          intro t ht
          obtain hwt := (G.mem_neighborFinset w t).mp ht
          by_contra hn
          have hne : t ≠ v := by simpa using hn
          exact h w t (SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hwt,hwv.ne,hne⟩)
        have hb := Finset.card_le_card hsub
        simp [hdw] at hb
      have cov (i j : Fin n) (h : H.Adj i j) : i ∈ T.erase v ∨ j ∈ T.erase v := by
        obtain ⟨h',hi,hj⟩ := SimpleGraph.deleteIncidenceSet_adj.mp h
        exact (cover i j h').imp (fun h => Finset.mem_erase.mpr ⟨hi,h⟩)
          (fun h => Finset.mem_erase.mpr ⟨hj,h⟩)
      let f := fun x : Fin n → Bool => NestedCover.graphFun G A (Function.update x v false)
      have spec (x : Fin n → Bool) :
          f x = true ↔ (∃ a ∈ A, x a = true) ∨ ∃ i j, H.Adj i j ∧ x i = true ∧ x j = true := by
        change NestedCover.graphFun G A (Function.update x v false) = true ↔ _
        rw [evGraph]
        simp only [Bool.or_eq_true,decide_eq_true_eq]
        constructor
        · rintro (⟨a,ha,hx⟩|⟨i,j,hij,hi,hj⟩)
          · exact Or.inl ⟨a,ha,by simpa [Function.update_of_ne (show a ≠ v from fun he => huv (he ▸ ha))] using hx⟩
          · have hiv : i ≠ v := by rintro rfl; simp at hi
            have hjv : j ≠ v := by rintro rfl; simp at hj
            exact Or.inr ⟨i,j,SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hij,hiv,hjv⟩,
              by simpa [Function.update_of_ne hiv] using hi,by simpa [Function.update_of_ne hjv] using hj⟩
        · rintro (⟨a,ha,hx⟩|⟨i,j,hij,hi,hj⟩)
          · exact Or.inl ⟨a,ha,by simpa [Function.update_of_ne (show a ≠ v from fun he => huv (he ▸ ha))] using hx⟩
          · obtain ⟨hed,hiv,hjv⟩ := SimpleGraph.deleteIncidenceSet_adj.mp hij
            exact Or.inr ⟨i,j,hed,by simpa [Function.update_of_ne hiv] using hi,
              by simpa [Function.update_of_ne hjv] using hj⟩
      have hbuild := markedUpper H A (T.erase v) f hedge cov spec
      have hcard : H.edgeFinset.card = G.edgeFinset.card - 3 := by
        simp only [H,SimpleGraph.card_edgeFinset_deleteIncidenceSet,hd]
      obtain ⟨i,j,hij⟩ := hedge
      have pos := (Finset.card_pos.mpr (show H.edgeFinset.Nonempty from ⟨s(i,j),by simpa using hij⟩))
      have hT := Finset.card_erase_add_one hv
      exact ⟨_,by omega,hbuild⟩
    classical
    let T := Aᶜ \ I
    have ts : T ⊆ Aᶜ := Finset.sdiff_subset
    have cov (u v : Fin n) (h : G.Adj u v) : u ∈ T ∨ v ∈ T := by
      by_cases hu : u ∈ I
      · exact Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr (unmarked _ _ h.symm),
          fun hv => hind u hu v hv h⟩)
      · exact Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr (unmarked _ _ h),hu⟩)
    obtain ⟨a,b,hab⟩ := edge
    obtain ⟨v,hv⟩ : T.Nonempty := (cov a b hab).elim (fun h => ⟨a,h⟩) (fun h => ⟨b,h⟩)
    obtain ⟨s,hs,hbuild⟩ := dropLemma n G A T v deg unmarked ts cov hv
    refine ⟨v,Finset.mem_compl.mp (ts hv),s,?_,hbuild⟩
    have ports := portBound n G A C fan computes minimal
    change A.card + (∑ a ∈ Aᶜ, (C.gates.filter fun g => (portRD g).contains a.val).length) + (Finset.univ.filter (fun j : Fin C.gates.length => 1 < (C.output :: C.gates.flatMap portRD).count (n+j.val))).card + (C.gates.filter fun g => g.op.eval [false]).length ≤ C.size + 1 at ports
    rw [← hr] at ports
    have dA (a : Fin n) (ha : a ∈ A) : G.degree a = 0 :=
      (G.degree_eq_zero a).mpr (fun j h => unmarked a j h ha)
    have dU (a : Fin n) (ha : a ∈ Aᶜ) : G.degree a = 3 := by
      rw [← G.ncard_neighborSet]
      exact deg a (Finset.mem_compl.mp ha)
    have degreeSum := G.sum_degrees_eq_twice_card_edges
    rw [← A.sum_add_sum_compl,Finset.sum_congr rfl dA,Finset.sum_congr rfl dU] at degreeSum
    simp only [Finset.sum_const_zero,zero_add,Finset.sum_const,smul_eq_mul] at degreeSum
    have hR (a : Fin n) (ha : a ∈ Aᶜ) : reads a = 2 + (if reads a = 3 then 1 else 0) := by
      obtain ⟨lo,hi⟩ := hread a (Finset.mem_compl.mp ha)
      split_ifs <;> omega
    have sumR := Finset.sum_congr rfl hR
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.sum_boole,smul_eq_mul,Nat.cast_id] at sumR
    have hT : T.card = Aᶜ.card-I.card := Finset.card_sdiff_of_subset hsub
    have hI := Finset.card_le_card hsub
    rcases budget with budget | budget
    · omega
    · change A.card + G.edgeFinset.card + T.card ≤ C.size+1 at budget
      omega
  classical
  intro n G inst A C f readers deg girth unmarked edge fan computes minimal readBounds allOr _
  let uses := fun j : ℕ => (C.output :: C.gates.flatMap portRD).count (n+j)
  let J := Finset.univ.filter fun j : Fin C.gates.length => 1 < uses j.val
  let S := {v : Fin n | v ∉ A ∧ (readers v).length = 2 ∧ ∀ j : Fin C.gates.length,
    v.val ∈ portRD (C.gates.get j) → uses j.val ≤ 1}
  let Q := Aᶜ.filter (fun v => (readers v).length = 3)
  let t := (C.gates.filter fun g => g.op.eval [false]).length
  have hread := fun v hv => And.intro (readBounds v hv).1 (readBounds v hv).2.1
  by_cases tight : ∀ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) →
      C.size+1 < A.card + G.edgeFinset.card + T.card
  case neg =>
    push Not at tight
    obtain ⟨T,cov,price⟩ := tight
    let I := Aᶜ \ T
    have sub : I ⊆ Aᶜ := Finset.sdiff_subset
    have hind (u) (hu : u ∈ I) (v) (hv : v ∈ I) (e : G.Adj u v) : False := by
      exact (cov u v e).elim (Finset.mem_sdiff.mp hu).2 (Finset.mem_sdiff.mp hv).2
    have subPrice : Aᶜ \ I ⊆ T := by
      intro z hz
      by_contra hn
      exact (Finset.mem_sdiff.mp hz).2 (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hz).1,hn⟩)
    apply budgetBranch G A C deg unmarked edge fan computes minimal _ rfl hread I sub hind (Or.inr ?_)
    have hh := Finset.card_le_card subPrice
    omega
  by_cases colorable : ∃ Z : Finset (Fin n), Z.card ≤ Q.card + 2*t ∧ (G.induce (S \ ↑Z)).Colorable 2
  · obtain ⟨Z,hZ,⟨c⟩⟩ := colorable
    let S' : Set (Fin n) := S \ ↑Z
    let color (v : Fin n) : Fin 2 := if h : v ∈ S' then c ⟨v,h⟩ else 0
    let part (i : Fin 2) := Finset.univ.filter (fun v : Fin n => v ∈ S' ∧ color v = i)
    have part_sub (i) : part i ⊆ Aᶜ := by
      intro v hv
      exact Finset.mem_compl.mpr (Finset.mem_filter.mp hv).2.1.1.1
    have ind (i) (u) (hu : u ∈ part i) (v) (hv : v ∈ part i) : ¬G.Adj u v := by
      intro e
      obtain ⟨huS,hi⟩ := (Finset.mem_filter.mp hu).2
      obtain ⟨hvS,hj⟩ := (Finset.mem_filter.mp hv).2
      exact c.valid (v := ⟨u,huS⟩) (w := ⟨v,hvS⟩) e (by simpa [color,huS,hvS] using hi.trans hj.symm)
    let inputs := J.biUnion fun j => (portRD (C.gates.get j)).toFinset
    let X := Aᶜ.filter (fun v => v.val ∈ inputs)
    have rawBound (j : Fin C.gates.length) (_ : j ∈ J) : (portRD (C.gates.get j)).toFinset.card ≤ 2 :=
      (List.toFinset_card_le _).trans (by
        simp only [portRD,List.length_take]
        exact (Nat.min_le_right ..).trans (fan _ (List.get_mem _ _)).2)
    have boundX : X.card ≤ J.card * 2 := by
      have hs : X.image Fin.val ⊆ inputs := by
        intro t ht
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ht
        exact (Finset.mem_filter.mp hv).2
      have h := Finset.card_le_card hs
      rw [Finset.card_image_of_injective _ Fin.val_injective] at h
      exact h.trans (Finset.card_biUnion_le_card_mul J _ 2 rawBound)
    have cover : Aᶜ ⊆ (((part 0 ∪ part 1) ∪ Q) ∪ X) ∪ Z := by
      intro v hv
      by_cases hz : v ∈ Z
      · exact Finset.mem_union_right _ hz
      apply Finset.mem_union_left
      by_cases hx : v ∈ X
      · exact Finset.mem_union_right _ hx
      apply Finset.mem_union_left
      by_cases hq : v ∈ Q
      · exact Finset.mem_union_right _ hq
      apply Finset.mem_union_left
      have hvA := Finset.mem_compl.mp hv
      obtain ⟨hlo,hhi,_⟩ := readBounds v hvA
      have h2 : (readers v).length = 2 := by
        have h3 : (readers v).length ≠ 3 := fun hh => hq (Finset.mem_filter.mpr ⟨hv,hh⟩)
        omega
      have hvS : v ∈ S := by
        refine ⟨hvA,h2,?_⟩
        intro j hj
        by_contra! large
        exact hx (Finset.mem_filter.mpr ⟨hv,Finset.mem_biUnion.mpr
          ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,large⟩,List.mem_toFinset.mpr hj⟩⟩)
      have hc : color v = 0 ∨ color v = 1 := by have := (color v).isLt; omega
      rcases hc with hc|hc
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨hvS,hz⟩,hc⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨hvS,hz⟩,hc⟩)
    have lower := Finset.card_le_card cover
    have h1 := Finset.card_union_le (part 0) (part 1)
    have h2 := Finset.card_union_le (part 0 ∪ part 1) Q
    have h3 := Finset.card_union_le ((part 0 ∪ part 1) ∪ Q) X
    have h4 := Finset.card_union_le (((part 0 ∪ part 1) ∪ Q) ∪ X) Z
    have solve (i : Fin 2) (hi : Aᶜ.card ≤ 2*((part i).card + Q.card + J.card + t)) :=
      budgetBranch G A C deg unmarked edge fan computes minimal _ rfl hread (part i)
        (part_sub i) (ind i) (Or.inl hi)
    by_cases h : (part 0).card ≤ (part 1).card
    · exact solve 1 (by omega)
    · exact solve 0 (by omega)
  · apply privateCycle n G A C deg girth unmarked _ computes _ tight (fun Z h col => colorable ⟨Z,h,col⟩)
    · exact ⟨fan,fun D ok h => minimal D.size ⟨D,ok,le_rfl,fun x => congrFun (h.trans computes) x⟩⟩
    · exact fun v hv => ⟨(readBounds v hv).1,(readBounds v hv).2.1,allOr v hv⟩
