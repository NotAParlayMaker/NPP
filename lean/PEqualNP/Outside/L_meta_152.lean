import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_152

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def orFun (m : Fin 4 → Bool) (x : Fin 4 → Bool) : Bool :=
  (m 0 && x 0) || (m 1 && x 1) || (m 2 && x 2) || (m 3 && x 3)

def genFun (c0 : Bool) (mL : Fin 4 → Bool) (c1 : Bool) (mR : Fin 4 → Bool)
    (d : Fin 4 → Bool) (u : Bool) (x : Fin 4 → Bool) : Bool :=
  orFun d x || (u && ((c0 || orFun mL x) && (c1 || orFun mR x)))

lemma bool_or_distrib4 (a1 a2 b1 b2 c1 c2 d1 d2 x0 x1 x2 x3 : Bool) :
    (((a1 && x0) || (b1 && x1) || (c1 && x2) || (d1 && x3)) ||
     ((a2 && x0) || (b2 && x1) || (c2 && x2) || (d2 && x3))) =
    (((a1 || a2) && x0) || ((b1 || b2) && x1) || ((c1 || c2) && x2) || ((d1 || d2) && x3)) := by
  revert a1 a2 b1 b2 c1 c2 d1 d2 x0 x1 x2 x3
  decide

lemma orFun_or (m1 m2 : Fin 4 → Bool) (x : Fin 4 → Bool) :
    (orFun m1 x || orFun m2 x) = orFun (fun i => m1 i || m2 i) x :=
  bool_or_distrib4 (m1 0) (m2 0) (m1 1) (m2 1) (m1 2) (m2 2) (m1 3) (m2 3)
    (x 0) (x 1) (x 2) (x 3)

lemma bool_gen_or (o1 o2 u1 u2 A : Bool) :
    ((o1 || (u1 && A)) || (o2 || (u2 && A))) = ((o1 || o2) || ((u1 || u2) && A)) := by
  cases o1 <;> cases o2 <;> cases u1 <;> cases u2 <;> cases A <;> rfl

lemma genFun_or (c0 : Bool) (mL : Fin 4 → Bool) (c1 : Bool) (mR : Fin 4 → Bool)
    (d1 d2 : Fin 4 → Bool) (u1 u2 : Bool) (x : Fin 4 → Bool) :
    (genFun c0 mL c1 mR d1 u1 x || genFun c0 mL c1 mR d2 u2 x) =
      genFun c0 mL c1 mR (fun i => d1 i || d2 i) (u1 || u2) x := by
  dsimp [genFun]
  rw [bool_gen_or, orFun_or]

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma getD_append_singleton (w : List Bool) (b : Bool) (k : ℕ) :
    (w ++ [b]).getD k false =
      if k < w.length then w.getD k false
      else if k = w.length then b
      else false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : k < w.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1]
    by_cases h2 : k = w.length
    · subst h2
      rw [if_pos rfl, List.getElem?_append_right (le_refl _)]
      simp
    · rw [if_neg h2, List.getElem?_eq_none]
      · rfl
      · simp only [List.length_append, List.length_singleton]
        omega

def AllPure (w : (Fin 4 → Bool) → List Bool) : Prop :=
  ∀ k : ℕ, ∃ m : Fin 4 → Bool, ∀ x : Fin 4 → Bool, (w x).getD k false = orFun m x

def AllGenWith (c0 : Bool) (mL : Fin 4 → Bool) (c1 : Bool) (mR : Fin 4 → Bool)
    (w : (Fin 4 → Bool) → List Bool) : Prop :=
  ∀ k : ℕ, ∃ (d : Fin 4 → Bool) (u : Bool),
    ∀ x : Fin 4 → Bool, (w x).getD k false = genFun c0 mL c1 mR d u x

def AllGen (w : (Fin 4 → Bool) → List Bool) : Prop :=
  ∃ (c0 : Bool) (mL : Fin 4 → Bool) (c1 : Bool) (mR : Fin 4 → Bool), AllGenWith c0 mL c1 mR w

lemma allPure_to_allGen {w : (Fin 4 → Bool) → List Bool} (h : AllPure w) : AllGen w := by
  refine ⟨false, fun _ => false, false, fun _ => false, fun k => ?_⟩
  obtain ⟨m, hm⟩ := h k
  refine ⟨m, false, fun x => ?_⟩
  rw [hm x]
  simp [genFun]

lemma orFun_single (x : Fin 4 → Bool) (idx : Fin 4) :
    x idx = orFun (fun i => decide (i = idx)) x := by
  fin_cases idx <;> simp [orFun]

lemma allPure_init : AllPure (fun x : Fin 4 → Bool => List.ofFn x) := by
  intro k
  by_cases hk : k < 4
  · refine ⟨fun i => decide (i = ⟨k, hk⟩), fun x => ?_⟩
    have hget : (List.ofFn x).getD k false = x ⟨k, hk⟩ := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [hk]
    rw [hget]
    exact orFun_single x ⟨k, hk⟩
  · refine ⟨fun _ => false, fun x => ?_⟩
    have hget : (List.ofFn x).getD k false = false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [hk]
    rw [hget]
    rfl

lemma step_or_allPure {w : (Fin 4 → Bool) → List Bool} {len : ℕ}
    (hlen : ∀ x, (w x).length = len) (hw : AllPure w) (g : Gate)
    (hop : g.op = GateOp.or) (hfan : g.inputs.length ≤ 2) :
    AllPure (fun x => stepWire (w x) g) := by
  have hnew : ∃ m : Fin 4 → Bool, ∀ x : Fin 4 → Bool,
      g.op.eval (g.inputs.map fun i => (w x).getD i false) = orFun m x := by
    rw [hop]
    rcases hli : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
    · refine ⟨fun _ => false, fun x => rfl⟩
    · obtain ⟨ma, hma⟩ := hw a
      refine ⟨ma, fun x => ?_⟩
      change ((w x).getD a false || false) = orFun ma x
      rw [Bool.or_false, hma x]
    · obtain ⟨ma, hma⟩ := hw a
      obtain ⟨mb, hmb⟩ := hw b
      refine ⟨fun i => ma i || mb i, fun x => ?_⟩
      change ((w x).getD a false || ((w x).getD b false || false)) = _
      rw [Bool.or_false, hma x, hmb x, orFun_or]
    · rw [hli] at hfan; simp at hfan
  obtain ⟨mnew, hmnew⟩ := hnew
  intro k
  by_cases hk1 : k < len
  · obtain ⟨mk, hmk⟩ := hw k
    refine ⟨mk, fun x => ?_⟩
    change (stepWire (w x) g).getD k false = _
    rw [stepWire, getD_append_singleton, hlen x, if_pos hk1, hmk x]
  · by_cases hk2 : k = len
    · refine ⟨mnew, fun x => ?_⟩
      change (stepWire (w x) g).getD k false = _
      rw [stepWire, getD_append_singleton, hlen x, if_neg hk1, if_pos hk2, hmnew x]
    · refine ⟨fun _ => false, fun x => ?_⟩
      change (stepWire (w x) g).getD k false = _
      rw [stepWire, getD_append_singleton, hlen x, if_neg hk1, if_neg hk2]
      rfl

lemma step_or_allGenWith {c0 : Bool} {mL : Fin 4 → Bool} {c1 : Bool} {mR : Fin 4 → Bool}
    {w : (Fin 4 → Bool) → List Bool} {len : ℕ} (hlen : ∀ x, (w x).length = len)
    (hw : AllGenWith c0 mL c1 mR w) (g : Gate) (hop : g.op = GateOp.or)
    (hfan : g.inputs.length ≤ 2) :
    AllGenWith c0 mL c1 mR (fun x => stepWire (w x) g) := by
  have hnew : ∃ (d : Fin 4 → Bool) (u : Bool), ∀ x : Fin 4 → Bool,
      g.op.eval (g.inputs.map fun i => (w x).getD i false) = genFun c0 mL c1 mR d u x := by
    rw [hop]
    rcases hli : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
    · refine ⟨fun _ => false, false, fun x => rfl⟩
    · obtain ⟨da, ua, hma⟩ := hw a
      refine ⟨da, ua, fun x => ?_⟩
      change ((w x).getD a false || false) = _
      rw [Bool.or_false, hma x]
    · obtain ⟨da, ua, hma⟩ := hw a
      obtain ⟨db, ub, hmb⟩ := hw b
      refine ⟨fun i => da i || db i, ua || ub, fun x => ?_⟩
      change ((w x).getD a false || ((w x).getD b false || false)) = _
      rw [Bool.or_false, hma x, hmb x, genFun_or]
    · rw [hli] at hfan; simp at hfan
  obtain ⟨dnew, unew, hmnew⟩ := hnew
  intro k
  by_cases hk1 : k < len
  · obtain ⟨dk, uk, hmk⟩ := hw k
    refine ⟨dk, uk, fun x => ?_⟩
    change (stepWire (w x) g).getD k false = _
    rw [stepWire, getD_append_singleton, hlen x, if_pos hk1, hmk x]
  · by_cases hk2 : k = len
    · refine ⟨dnew, unew, fun x => ?_⟩
      change (stepWire (w x) g).getD k false = _
      rw [stepWire, getD_append_singleton, hlen x, if_neg hk1, if_pos hk2, hmnew x]
    · refine ⟨fun _ => false, false, fun x => ?_⟩
      change (stepWire (w x) g).getD k false = _
      rw [stepWire, getD_append_singleton, hlen x, if_neg hk1, if_neg hk2]
      rfl

lemma step_and_allGen {w : (Fin 4 → Bool) → List Bool} {len : ℕ}
    (hlen : ∀ x, (w x).length = len) (hw : AllPure w) (g : Gate)
    (hop : g.op = GateOp.and) (hfan : g.inputs.length ≤ 2) :
    AllGen (fun x => stepWire (w x) g) := by
  have hnew : ∃ (c0 : Bool) (mL : Fin 4 → Bool) (c1 : Bool) (mR : Fin 4 → Bool),
      ∀ x : Fin 4 → Bool,
        g.op.eval (g.inputs.map fun i => (w x).getD i false) =
          genFun c0 mL c1 mR (fun _ => false) true x := by
    rw [hop]
    rcases hli : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
    · refine ⟨true, fun _ => false, true, fun _ => false, fun x => rfl⟩
    · obtain ⟨ma, hma⟩ := hw a
      refine ⟨false, ma, true, fun _ => false, fun x => ?_⟩
      change ((w x).getD a false && true) = _
      rw [Bool.and_true, hma x]
      simp [genFun, orFun]
    · obtain ⟨ma, hma⟩ := hw a
      obtain ⟨mb, hmb⟩ := hw b
      refine ⟨false, ma, false, mb, fun x => ?_⟩
      change ((w x).getD a false && ((w x).getD b false && true)) = _
      rw [Bool.and_true, hma x, hmb x]
      simp [genFun, orFun]
    · rw [hli] at hfan; simp at hfan
  obtain ⟨c0, mL, c1, mR, hmnew⟩ := hnew
  refine ⟨c0, mL, c1, mR, fun k => ?_⟩
  by_cases hk1 : k < len
  · obtain ⟨mk, hmk⟩ := hw k
    refine ⟨mk, false, fun x => ?_⟩
    change (stepWire (w x) g).getD k false = _
    rw [stepWire, getD_append_singleton, hlen x, if_pos hk1, hmk x]
    simp [genFun]
  · by_cases hk2 : k = len
    · refine ⟨fun _ => false, true, fun x => ?_⟩
      change (stepWire (w x) g).getD k false = _
      rw [stepWire, getD_append_singleton, hlen x, if_neg hk1, if_pos hk2, hmnew x]
    · refine ⟨fun _ => false, false, fun x => ?_⟩
      change (stepWire (w x) g).getD k false = _
      rw [stepWire, getD_append_singleton, hlen x, if_neg hk1, if_neg hk2]
      rfl

lemma foldl_or_allGen (gs : List Gate)
    (hor : ∀ g ∈ gs, g.op = GateOp.or ∧ g.inputs.length ≤ 2) :
    ∀ (w : (Fin 4 → Bool) → List Bool) (len : ℕ),
      (∀ x, (w x).length = len) → AllGen w → AllGen (fun x => gs.foldl stepWire (w x)) := by
  induction gs with
  | nil =>
    intro w _ _ hw
    exact hw
  | cons g gs ih =>
    intro w len hlen ⟨c0, mL, c1, mR, hw⟩
    have hg := hor g List.mem_cons_self
    have hw' := step_or_allGenWith hlen hw g hg.1 hg.2
    have hlen' : ∀ x, (stepWire (w x) g).length = len + 1 := by
      intro x; simp [stepWire, hlen x]
    exact ih (fun g' hg' => hor g' (List.mem_cons_of_mem g hg'))
      (fun x => stepWire (w x) g) (len + 1) hlen' ⟨c0, mL, c1, mR, hw'⟩

lemma foldl_atMostOneAnd_allGen (gs : List Gate)
    (hM : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (huniq : ∀ (j1 j2 : ℕ) (g1 g2 : Gate),
      gs[j1]? = some g1 → gs[j2]? = some g2 → g1.op = GateOp.and → g2.op = GateOp.and → j1 = j2) :
    ∀ (w : (Fin 4 → Bool) → List Bool) (len : ℕ),
      (∀ x, (w x).length = len) → AllPure w → AllGen (fun x => gs.foldl stepWire (w x)) := by
  induction gs with
  | nil =>
    intro w _ _ hw
    exact allPure_to_allGen hw
  | cons g gs ih =>
    intro w len hlen hw
    have hg := hM g List.mem_cons_self
    have hlen' : ∀ x, (stepWire (w x) g).length = len + 1 := by
      intro x; simp [stepWire, hlen x]
    rcases hg.1 with hand | hor
    · have hw' := step_and_allGen hlen hw g hand hg.2
      have hallOr : ∀ g' ∈ gs, g'.op = GateOp.or ∧ g'.inputs.length ≤ 2 := by
        intro g' hg'
        have hm' := hM g' (List.mem_cons_of_mem g hg')
        refine ⟨?_, hm'.2⟩
        rcases hm'.1 with hand' | hor'
        · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg'
          have h0 : (g :: gs)[0]? = some g := rfl
          have hj1 : (g :: gs)[j + 1]? = some gs[j] := by simp [hj]
          have heq := huniq 0 (j + 1) g gs[j] h0 hj1 hand hand'
          omega
        · exact hor'
      exact foldl_or_allGen gs hallOr (fun x => stepWire (w x) g) (len + 1) hlen' hw'
    · have hw' := step_or_allPure hlen hw g hor hg.2
      have hM' : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
        fun g' hg' => hM g' (List.mem_cons_of_mem g hg')
      have huniq' : ∀ (j1 j2 : ℕ) (g1 g2 : Gate),
          gs[j1]? = some g1 → gs[j2]? = some g2 →
          g1.op = GateOp.and → g2.op = GateOp.and → j1 = j2 := by
        intro j1 j2 g1 g2 h1 h2 ha1 ha2
        have h1' : (g :: gs)[j1 + 1]? = some g1 := h1
        have h2' : (g :: gs)[j2 + 1]? = some g2 := h2
        have heq := huniq (j1 + 1) (j2 + 1) g1 g2 h1' h2' ha1 ha2
        omega
      exact ih hM' huniq' (fun x => stepWire (w x) g) (len + 1) hlen' hw'

lemma no_11_bools (c0 c1 u l0 l1 l2 l3 r0 r1 r2 r3 : Bool) :
    ¬ ((u && ((c0 || l0) && (c1 || r0))) = false ∧
       (u && ((c0 || l1) && (c1 || r1))) = false ∧
       (u && ((c0 || l2) && (c1 || r2))) = false ∧
       (u && ((c0 || l3) && (c1 || r3))) = false ∧
       (u && ((c0 || (l0 || l1)) && (c1 || (r0 || r1)))) = true ∧
       (u && ((c0 || (l2 || l3)) && (c1 || (r2 || r3)))) = true ∧
       (u && ((c0 || (l0 || l2)) && (c1 || (r0 || r2)))) = false ∧
       (u && ((c0 || (l0 || l3)) && (c1 || (r0 || r3)))) = false ∧
       (u && ((c0 || (l1 || l3)) && (c1 || (r1 || r3)))) = false) := by
  revert c0 c1 u l0 l1 l2 l3 r0 r1 r2 r3
  decide

end PEqualNP.Outside.L_meta_152

open PEqualNP.Outside.L_meta_152 in
theorem PEqualNP.Outside.L_meta_152 : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ 1 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) ∧ ∀ x : Fin 4 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 4, u.val + 1 = v.val ∧ x u = true ∧ x v = true) := by
  rintro ⟨C, hM, ⟨A, hAcard, hA⟩, hEval⟩
  have hM' : ∀ g ∈ C.gates,
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
       g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hM g hg
    exact ⟨by simpa using hop, hlen⟩
  have huniq : ∀ (j1 j2 : ℕ) (g1 g2 : PEqualNP.CircuitLowerBounds.Gate),
      C.gates[j1]? = some g1 → C.gates[j2]? = some g2 →
      g1.op = PEqualNP.CircuitLowerBounds.GateOp.and →
      g2.op = PEqualNP.CircuitLowerBounds.GateOp.and → j1 = j2 := by
    intro j1 j2 g1 g2 h1 h2 ha1 ha2
    exact Finset.card_le_one.mp hAcard j1 (hA j1 g1 h1 ha1) j2 (hA j2 g2 h2 ha2)
  obtain ⟨c0, mL, c1, mR, hgen⟩ :=
    foldl_atMostOneAnd_allGen C.gates hM' huniq (fun x => List.ofFn x) 4 (fun x => by simp) allPure_init
  obtain ⟨d, u, hout⟩ := hgen C.output
  have hval : ∀ x : Fin 4 → Bool,
      genFun c0 mL c1 mR d u x = decide (∃ a b : Fin 4, a.val + 1 = b.val ∧ x a = true ∧ x b = true) := by
    intro x
    have h1 : C.eval (List.ofFn x) = genFun c0 mL c1 mR d u x := hout x
    rw [← h1]
    by_cases hc : C.eval (List.ofFn x) = true
    · rw [hc, eq_comm, decide_eq_true_iff]
      exact (hEval x).mp hc
    · have hf : C.eval (List.ofFn x) = false := Bool.eq_false_iff.mpr hc
      rw [hf, eq_comm, decide_eq_false_iff_not]
      exact fun hp => hc ((hEval x).mpr hp)
  have hs0 := hval ![true, false, false, false]
  have hs1 := hval ![false, true, false, false]
  have hs2 := hval ![false, false, true, false]
  have hs3 := hval ![false, false, false, true]
  have he01 := hval ![true, true, false, false]
  have he23 := hval ![false, false, true, true]
  have hn02 := hval ![true, false, true, false]
  have hn03 := hval ![true, false, false, true]
  have hn13 := hval ![false, true, false, true]
  simp only [genFun, orFun, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Bool.and_true, Bool.and_false, Bool.or_false, Bool.false_or] at hs0 hs1 hs2 hs3 he01 he23 hn02 hn03 hn13
  have h0_val : decide (∃ a b : Fin 4, a.val + 1 = b.val ∧ (![true, false, false, false] : Fin 4 → Bool) a = true ∧ (![true, false, false, false] : Fin 4 → Bool) b = true) = false := by decide
  have h1_val : decide (∃ a b : Fin 4, a.val + 1 = b.val ∧ (![false, true, false, false] : Fin 4 → Bool) a = true ∧ (![false, true, false, false] : Fin 4 → Bool) b = true) = false := by decide
  have h2_val : decide (∃ a b : Fin 4, a.val + 1 = b.val ∧ (![false, false, true, false] : Fin 4 → Bool) a = true ∧ (![false, false, true, false] : Fin 4 → Bool) b = true) = false := by decide
  have h3_val : decide (∃ a b : Fin 4, a.val + 1 = b.val ∧ (![false, false, false, true] : Fin 4 → Bool) a = true ∧ (![false, false, false, true] : Fin 4 → Bool) b = true) = false := by decide
  have he01_val : decide (∃ a b : Fin 4, a.val + 1 = b.val ∧ (![true, true, false, false] : Fin 4 → Bool) a = true ∧ (![true, true, false, false] : Fin 4 → Bool) b = true) = true := by decide
  have he23_val : decide (∃ a b : Fin 4, a.val + 1 = b.val ∧ (![false, false, true, true] : Fin 4 → Bool) a = true ∧ (![false, false, true, true] : Fin 4 → Bool) b = true) = true := by decide
  have hn02_val : decide (∃ a b : Fin 4, a.val + 1 = b.val ∧ (![true, false, true, false] : Fin 4 → Bool) a = true ∧ (![true, false, true, false] : Fin 4 → Bool) b = true) = false := by decide
  have hn03_val : decide (∃ a b : Fin 4, a.val + 1 = b.val ∧ (![true, false, false, true] : Fin 4 → Bool) a = true ∧ (![true, false, false, true] : Fin 4 → Bool) b = true) = false := by decide
  have hn13_val : decide (∃ a b : Fin 4, a.val + 1 = b.val ∧ (![false, true, false, true] : Fin 4 → Bool) a = true ∧ (![false, true, false, true] : Fin 4 → Bool) b = true) = false := by decide
  rw [h0_val] at hs0
  rw [h1_val] at hs1
  rw [h2_val] at hs2
  rw [h3_val] at hs3
  rw [he01_val] at he01
  rw [he23_val] at he23
  rw [hn02_val] at hn02
  rw [hn03_val] at hn03
  rw [hn13_val] at hn13
  have hd0 : d 0 = false := by
    cases h : d 0
    · rfl
    · rw [h, Bool.true_or] at hs0; cases hs0
  have hd1 : d 1 = false := by
    cases h : d 1
    · rfl
    · rw [h, Bool.true_or] at hs1; cases hs1
  have hd2 : d 2 = false := by
    cases h : d 2
    · rfl
    · rw [h, Bool.true_or] at hs2; cases hs2
  have hd3 : d 3 = false := by
    cases h : d 3
    · rfl
    · rw [h, Bool.true_or] at hs3; cases hs3
  rw [hd0, Bool.false_or] at hs0
  rw [hd1, Bool.false_or] at hs1
  rw [hd2, Bool.false_or] at hs2
  rw [hd3, Bool.false_or] at hs3
  rw [hd0, hd1, Bool.or_self, Bool.false_or] at he01
  rw [hd2, hd3, Bool.or_self, Bool.false_or] at he23
  rw [hd0, hd2, Bool.or_self, Bool.false_or] at hn02
  rw [hd0, hd3, Bool.or_self, Bool.false_or] at hn03
  rw [hd1, hd3, Bool.or_self, Bool.false_or] at hn13
  exact no_11_bools c0 c1 u (mL 0) (mL 1) (mL 2) (mL 3) (mR 0) (mR 1) (mR 2) (mR 3)
    ⟨hs0, hs1, hs2, hs3, he01, he23, hn02, hn03, hn13⟩
