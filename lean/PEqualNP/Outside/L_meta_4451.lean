import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4451

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem len_fold : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length
  | [], _ => rfl
  | g :: gs, w => by
    simp only [List.foldl_cons]
    rw [len_fold gs]
    simp [step]
    omega

theorem step_getD_lt (w : List Bool) (g : Gate) (k : ℕ) (hk : k < w.length) :
    (step w g).getD k false = w.getD k false := by
  unfold step
  exact List.getD_append _ _ _ _ hk

theorem step_getD_last (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  unfold step
  simp

theorem fold_prefix : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl step w).getD i false = w.getD i false
  | [], _, _, _ => rfl
  | g :: gs, w, i, hi => by
    simp only [List.foldl_cons]
    rw [fold_prefix gs _ i (by simp [step]; omega)]
    unfold step
    exact List.getD_append _ _ _ _ hi

theorem getD_snoc {α : Type} (w : List α) (a d : α) (i : ℕ) :
    (w ++ [a]).getD i d = if i < w.length then w.getD i d else if i = w.length then a else d := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; simp
  · rw [List.getD_eq_default]; simp; omega

-- the simplification of a circuit under one input set to false
def sstep (n : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate) : List Gate × List (Option ℕ) :=
  match g.op, s.2.getD (g.inputs.getD 0 0) none, s.2.getD (g.inputs.getD 1 0) none with
  | GateOp.and, some ka, some kb =>
      (s.1 ++ [⟨GateOp.and, [ka, kb]⟩], s.2 ++ [some (n + s.1.length)])
  | GateOp.or, none, vb => (s.1, s.2 ++ [vb])
  | GateOp.or, some ka, none => (s.1, s.2 ++ [some ka])
  | GateOp.or, some ka, some kb =>
      (s.1 ++ [⟨GateOp.or, [ka, kb]⟩], s.2 ++ [some (n + s.1.length)])
  | _, _, _ => (s.1, s.2 ++ [none])

-- facts about one gate of the old circuit
def OkGate (len : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b, g.inputs = [a, b] ∧ a < len ∧ b < len

-- shape of the state, independent of the input
def WF (n : ℕ) (s : List Gate × List (Option ℕ)) : Prop :=
  (∀ j (hj : j < s.1.length), (s.1[j].op = GateOp.and ∨ s.1[j].op = GateOp.or) ∧
      ∃ a b, s.1[j].inputs = [a, b] ∧ a < n + j ∧ b < n + j) ∧
    ∀ i k, s.2.getD i none = some k → k < n + s.1.length

theorem sstep_cases (n : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate) (a b : ℕ)
    (hin : g.inputs = [a, b]) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    (g.op = GateOp.and ∧ ∃ ka kb, s.2.getD a none = some ka ∧ s.2.getD b none = some kb ∧
        sstep n s g = (s.1 ++ [⟨GateOp.and, [ka, kb]⟩], s.2 ++ [some (n + s.1.length)])) ∨
    (g.op = GateOp.and ∧ (s.2.getD a none = none ∨ s.2.getD b none = none) ∧
        sstep n s g = (s.1, s.2 ++ [none])) ∨
    (g.op = GateOp.or ∧ s.2.getD a none = none ∧ sstep n s g = (s.1, s.2 ++ [s.2.getD b none])) ∨
    (g.op = GateOp.or ∧ ∃ ka, s.2.getD a none = some ka ∧ s.2.getD b none = none ∧
        sstep n s g = (s.1, s.2 ++ [some ka])) ∨
    (g.op = GateOp.or ∧ ∃ ka kb, s.2.getD a none = some ka ∧ s.2.getD b none = some kb ∧
        sstep n s g = (s.1 ++ [⟨GateOp.or, [ka, kb]⟩], s.2 ++ [some (n + s.1.length)])) := by
  unfold sstep
  rw [hin]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  rcases hop with hop | hop <;> rw [hop] <;>
    rcases ha : s.2.getD a none with _ | ka <;> rcases hb : s.2.getD b none with _ | kb <;> simp

theorem wf_step (n : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate) (hw : WF n s)
    (hg : OkGate s.2.length g) : WF n (sstep n s g) := by
  obtain ⟨hop, a, b, hin, ha, hb⟩ := hg
  obtain ⟨hw1, hw2⟩ := hw
  have hm : ∀ i k, (s.2 ++ [some (n + s.1.length)]).getD i none = some k → k < n + s.1.length + 1 := by
    intro i k h
    rw [getD_snoc] at h
    split_ifs at h with h1 h2
    · have := hw2 i k h; omega
    · simp at h; omega
  have emit : ∀ (o : GateOp) (ka kb : ℕ), (o = GateOp.and ∨ o = GateOp.or) →
      s.2.getD a none = some ka → s.2.getD b none = some kb →
      WF n (s.1 ++ [⟨o, [ka, kb]⟩], s.2 ++ [some (n + s.1.length)]) := by
    intro o ka kb ho hka hkb
    refine ⟨?_, ?_⟩
    · intro j hj
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hjl : j < s.1.length
      · simp only [List.getElem_append_left hjl]
        exact hw1 j hjl
      · have hje : j = s.1.length := by omega
        subst hje
        simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
        exact ⟨ho, ka, kb, rfl, hw2 _ _ hka, hw2 _ _ hkb⟩
    · intro i k h
      have := hm i k h
      simp only [List.length_append, List.length_singleton]
      omega
  have keep : ∀ v : Option ℕ, (∀ k, v = some k → k < n + s.1.length) →
      WF n (s.1, s.2 ++ [v]) := by
    intro v hv
    refine ⟨hw1, ?_⟩
    intro i k h
    simp only at h ⊢
    rw [getD_snoc] at h
    split_ifs at h with h1 h2
    · exact hw2 i k h
    · exact hv k h
  rcases sstep_cases n s g a b hin hop with
    ⟨ho, ka, kb, hka, hkb, he⟩ | ⟨ho, _, he⟩ | ⟨ho, _, he⟩ | ⟨ho, ka, hka, _, he⟩ |
      ⟨ho, ka, kb, hka, hkb, he⟩ <;> rw [he]
  · exact emit _ ka kb (Or.inl rfl) hka hkb
  · exact keep none (by simp)
  · exact keep _ (fun k h => hw2 b k h)
  · exact keep _ (fun k h => by cases h; exact hw2 a ka hka)
  · exact emit _ ka kb (Or.inr rfl) hka hkb

-- the semantic invariant for one input x
def Inv {n : ℕ} (t : Fin n) (x : Fin n → Bool) (s : List Gate × List (Option ℕ))
    (ow : List Bool) : Prop :=
  s.2.length = ow.length ∧
    ∀ i, i < ow.length →
      (s.2.getD i none = none → x t = false → ow.getD i false = false) ∧
      ∀ k, s.2.getD i none = some k →
        ((s.1.foldl step (List.ofFn x)).getD k false = true → ow.getD i false = true) ∧
        (x t = false → (s.1.foldl step (List.ofFn x)).getD k false = ow.getD i false)

theorem inv_snoc {n : ℕ} (t : Fin n) (x : Fin n → Bool) (ng ng' : List Gate)
    (m : List (Option ℕ)) (v : Option ℕ) (ow : List Bool) (val : Bool)
    (hpre : ∀ k, k < n + ng.length →
      (ng'.foldl step (List.ofFn x)).getD k false = (ng.foldl step (List.ofFn x)).getD k false)
    (hwf : ∀ i k, m.getD i none = some k → k < n + ng.length)
    (hi : Inv t x (ng, m) ow)
    (hN : v = none → x t = false → val = false)
    (hS : ∀ k, v = some k →
      ((ng'.foldl step (List.ofFn x)).getD k false = true → val = true) ∧
      (x t = false → (ng'.foldl step (List.ofFn x)).getD k false = val)) :
    Inv t x (ng', m ++ [v]) (ow ++ [val]) := by
  obtain ⟨hl, hinv⟩ := hi
  simp only at hl hinv
  refine ⟨by simp [hl], ?_⟩
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_or_ge i ow.length with h1 | h1
  · have h1' : i < m.length := by omega
    simp only [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h1']
    obtain ⟨hn0, hs0⟩ := hinv i h1
    refine ⟨hn0, ?_⟩
    intro k hk
    rw [hpre k (hwf i k hk)]
    exact hs0 k hk
  · have hie : i = ow.length := by omega
    subst hie
    have e1 : (m ++ [v]).getD ow.length none = v := by rw [← hl]; simp
    have e2 : (ow ++ [val]).getD ow.length false = val := by simp
    simp only [e1, e2]
    exact ⟨hN, hS⟩

theorem inv_step {n : ℕ} (t : Fin n) (x : Fin n → Bool) (s : List Gate × List (Option ℕ))
    (ow : List Bool) (g : Gate) (hw : WF n s) (hg : OkGate ow.length g) (hi : Inv t x s ow) :
    Inv t x (sstep n s g) (step ow g) := by
  obtain ⟨hop, a, b, hin, ha, hb⟩ := hg
  obtain ⟨hw1, hw2⟩ := hw
  have hnwl : (s.1.foldl step (List.ofFn x)).length = n + s.1.length := by
    rw [len_fold]; simp
  have hstep : step ow g = ow ++ [g.op.eval [ow.getD a false, ow.getD b false]] := by
    simp [step, hin]
  have hA := hi.2 a ha
  have hB := hi.2 b hb
  have hpre_same : ∀ k, k < n + s.1.length →
      (s.1.foldl step (List.ofFn x)).getD k false = (s.1.foldl step (List.ofFn x)).getD k false :=
    fun _ _ => rfl
  have hpre_app : ∀ (h : Gate) k, k < n + s.1.length →
      ((s.1 ++ [h]).foldl step (List.ofFn x)).getD k false =
        (s.1.foldl step (List.ofFn x)).getD k false := by
    intro h k hk
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    exact step_getD_lt _ _ _ (by omega)
  have hnew : ∀ (h : Gate), ((s.1 ++ [h]).foldl step (List.ofFn x)).getD (n + s.1.length) false =
      h.op.eval (h.inputs.map fun i => (s.1.foldl step (List.ofFn x)).getD i false) := by
    intro h
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [← hnwl]
    exact step_getD_last _ _
  have hi' : Inv t x (s.1, s.2) ow := hi
  rw [hstep]
  rcases sstep_cases n s g a b hin hop with
    ⟨ho, ka, kb, hka, hkb, he⟩ | ⟨ho, hn, he⟩ | ⟨ho, hn, he⟩ | ⟨ho, ka, hka, hnb, he⟩ |
      ⟨ho, ka, kb, hka, hkb, he⟩ <;> rw [he, ho]
  · refine inv_snoc t x s.1 _ s.2 _ ow _ (hpre_app _) hw2 hi' (by simp) ?_
    intro k hk
    simp only [Option.some.injEq] at hk
    subst hk
    rw [hnew]
    obtain ⟨ma, ea⟩ := hA.2 ka hka
    obtain ⟨mb, eb⟩ := hB.2 kb hkb
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
      Bool.and_true]
    refine ⟨?_, ?_⟩
    · intro h
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨ma h.1, mb h.2⟩
    · intro ht
      rw [ea ht, eb ht]
  · refine inv_snoc t x s.1 s.1 s.2 none ow _ hpre_same hw2 hi' ?_ (by simp)
    intro _ ht
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
      Bool.and_true]
    rcases hn with hn | hn
    · rw [hA.1 hn ht]; simp
    · rw [hB.1 hn ht]; simp
  · refine inv_snoc t x s.1 s.1 s.2 _ ow _ hpre_same hw2 hi' ?_ ?_
    · intro hbn ht
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
        Bool.or_false]
      rw [hA.1 hn ht, hB.1 hbn ht]
      rfl
    · intro k hk
      obtain ⟨mb, eb⟩ := hB.2 k hk
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
        Bool.or_false]
      refine ⟨?_, ?_⟩
      · intro h
        rw [mb h]
        simp
      · intro ht
        rw [eb ht, hA.1 hn ht]
        simp
  · refine inv_snoc t x s.1 s.1 s.2 _ ow _ hpre_same hw2 hi' (by simp) ?_
    intro k hk
    simp only [Option.some.injEq] at hk
    subst hk
    obtain ⟨ma, ea⟩ := hA.2 ka hka
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
      Bool.or_false]
    refine ⟨?_, ?_⟩
    · intro h
      rw [ma h]
      simp
    · intro ht
      rw [ea ht, hB.1 hnb ht]
      simp
  · refine inv_snoc t x s.1 _ s.2 _ ow _ (hpre_app _) hw2 hi' (by simp) ?_
    intro k hk
    simp only [Option.some.injEq] at hk
    subst hk
    rw [hnew]
    obtain ⟨ma, ea⟩ := hA.2 ka hka
    obtain ⟨mb, eb⟩ := hB.2 kb hkb
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
      Bool.or_false]
    refine ⟨?_, ?_⟩
    · intro h
      simp only [Bool.or_eq_true] at h ⊢
      rcases h with h | h
      · exact Or.inl (ma h)
      · exact Or.inr (mb h)
    · intro ht
      rw [ea ht, eb ht]

theorem fold_all {n : ℕ} (t : Fin n) (x : Fin n → Bool) : ∀ (gs : List Gate)
    (s : List Gate × List (Option ℕ)) (ow : List Bool),
    (∀ j (hj : j < gs.length), OkGate (ow.length + j) gs[j]) → WF n s → Inv t x s ow →
    WF n (gs.foldl (sstep n) s) ∧ Inv t x (gs.foldl (sstep n) s) (gs.foldl step ow)
  | [], _, _, _, hw, hi => ⟨hw, hi⟩
  | g :: gs, s, ow, hg, hw, hi => by
    simp only [List.foldl_cons]
    have hg0 : OkGate ow.length g := by
      have := hg 0 (by simp)
      rwa [List.getElem_cons_zero, Nat.add_zero] at this
    have hl : (s.2).length = ow.length := hi.1
    refine fold_all t x gs _ _ ?_ (wf_step n s g hw (by rw [hl]; exact hg0))
      (inv_step t x s ow g hw hg0 hi)
    intro j hj
    have := hg (j + 1) (by simp; omega)
    simp only [List.getElem_cons_succ] at this
    have hlen : (step ow g).length = ow.length + 1 := by simp [step]
    rw [hlen, show ow.length + 1 + j = ow.length + (j + 1) by omega]
    exact this

theorem sstep_len (n : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate) (a b : ℕ)
    (hin : g.inputs = [a, b]) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (tv : ℕ)
    (ht : s.2.getD tv none = none) (htl : tv < s.2.length) :
    (sstep n s g).2.getD tv none = none ∧ tv < (sstep n s g).2.length ∧
      (sstep n s g).1.length + (if tv ∈ g.inputs then 1 else 0) ≤ s.1.length + 1 := by
  have key : ∀ v : Option ℕ, (s.2 ++ [v]).getD tv none = none ∧ tv < (s.2 ++ [v]).length := by
    intro v
    refine ⟨?_, by simp; omega⟩
    rw [List.getD_append _ _ _ _ htl]
    exact ht
  rcases sstep_cases n s g a b hin hop with
    ⟨ho, ka, kb, hka, hkb, he⟩ | ⟨ho, hn, he⟩ | ⟨ho, hn, he⟩ | ⟨ho, ka, hka, hnb, he⟩ |
      ⟨ho, ka, kb, hka, hkb, he⟩ <;> rw [he] <;> refine ⟨(key _).1, (key _).2, ?_⟩
  · have : tv ∉ g.inputs := by
      rw [hin]
      intro hm
      simp at hm
      rcases hm with hm | hm
      · subst hm; rw [ht] at hka; cases hka
      · subst hm; rw [ht] at hkb; cases hkb
    simp [this]
  · split_ifs <;> simp
  · split_ifs <;> simp
  · split_ifs <;> simp
  · have : tv ∉ g.inputs := by
      rw [hin]
      intro hm
      simp at hm
      rcases hm with hm | hm
      · subst hm; rw [ht] at hka; cases hka
      · subst hm; rw [ht] at hkb; cases hkb
    simp [this]

theorem fold_len (n : ℕ) (tv : ℕ) : ∀ (gs : List Gate) (s : List Gate × List (Option ℕ)),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b, g.inputs = [a, b]) →
    s.2.getD tv none = none → tv < s.2.length →
    (gs.foldl (sstep n) s).1.length + gs.countP (fun g => decide (tv ∈ g.inputs)) ≤
      s.1.length + gs.length
  | [], _, _, _, _ => by simp
  | g :: gs, s, hg, ht, htl => by
    simp only [List.foldl_cons, List.countP_cons, List.length_cons]
    obtain ⟨hop, a, b, hin⟩ := hg g (by simp)
    obtain ⟨ht', htl', hle⟩ := sstep_len n s g a b hin hop tv ht htl
    have ih := fold_len n tv gs (sstep n s g) (fun g' hg' => hg g' (by simp [hg'])) ht' htl'
    by_cases hm : tv ∈ g.inputs
    · simp [hm] at hle ⊢
      omega
    · simp [hm] at hle ⊢
      omega

theorem indep (tv : ℕ) : ∀ (gs : List Gate) (w w' : List Bool), w.length = w'.length →
    (∀ i, i ≠ tv → w.getD i false = w'.getD i false) → (∀ g ∈ gs, tv ∉ g.inputs) →
    ∀ i, i ≠ tv → (gs.foldl step w).getD i false = (gs.foldl step w').getD i false
  | [], _, _, _, h, _ => h
  | g :: gs, w, w', hl, h, hg => by
    simp only [List.foldl_cons]
    have hv : g.op.eval (g.inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => w'.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro i hi
      exact h i (fun e => hg g (by simp) (e ▸ hi))
    refine indep tv gs _ _ (by simp [step, hl]) ?_ (fun g' hg' => hg g' (by simp [hg']))
    intro i hi
    unfold step
    rw [hv, getD_snoc, getD_snoc, hl, h i hi]

theorem getD_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (i : ℕ) (d : α) :
    (List.ofFn f).getD i d = if h : i < n then f ⟨i, h⟩ else d := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [List.getD_eq_default _ _ (by simpa using h)]

end PEqualNP.Outside.L_meta_4451

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_4451

theorem PEqualNP.Outside.L_meta_4451 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin x1), PEqualNP.TopForm.IsAO2 x1 x2 → x3 ≠ x4 → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x7 : Fin x1) => Decidable.decide (x7 = x3)) = Bool.false → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x8 : Fin x1) => Decidable.decide (x8 = x4)) = Bool.false → (PEqualNP.MetaComplexity.circuitFun x1 x2 fun (x9 : Fin x1) => Decidable.decide (x9 = x3 ∨ x9 = x4)) = Bool.true → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x10 ∧ x10.size < x2.size ∧ (∀ (x11 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x10 x11 = Bool.true → PEqualNP.MetaComplexity.circuitFun x1 x2 x11 = Bool.true) ∧ ∀ (x11 : Fin x1 → Bool), x11 x3 = Bool.false → PEqualNP.MetaComplexity.circuitFun x1 x10 x11 = PEqualNP.MetaComplexity.circuitFun x1 x2 x11 := by
  intro n C t u hC htu h1 h2 h3
  obtain ⟨hAO, hRB, h2in⟩ := hC
  have hok : ∀ j (hj : j < C.gates.length), OkGate (n + j) C.gates[j] := by
    intro j hj
    have hm := List.getElem_mem hj
    obtain ⟨a, b, hab⟩ := List.length_eq_two.1 (h2in _ hm)
    have hrb := hRB j hj
    have hga : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      exact List.getD_eq_getElem _ _ hj
    rw [hga, hab] at hrb
    exact ⟨hAO _ hm, a, b, hab, hrb a (by simp), hrb b (by simp)⟩
  let m0 : List (Option ℕ) := List.ofFn (fun i : Fin n => if i = t then none else some i.val)
  let s0 : List Gate × List (Option ℕ) := ([], m0)
  have hm0 : ∀ i, m0.getD i none = if h : i < n then (if (⟨i, h⟩ : Fin n) = t then none else some i)
      else none := fun i => getD_ofFn _ i none
  have hwf0 : WF n s0 := by
    refine ⟨fun j hj => by simp [s0] at hj, ?_⟩
    intro i k hk
    simp only [s0, hm0] at hk
    split_ifs at hk with h hh
    · simp at hk
      simp [s0]; omega
  have hinv0 : ∀ x : Fin n → Bool, Inv t x s0 (List.ofFn x) := by
    intro x
    refine ⟨by simp [s0, m0], ?_⟩
    intro i hi
    simp only [List.length_ofFn] at hi
    simp only [s0, hm0, dif_pos hi, List.foldl_nil, getD_ofFn]
    split_ifs with hh
    · constructor
      · intro _ ht; rw [hh]; exact ht
      · intro k hk; simp at hk
    · constructor
      · intro hk; simp at hk
      intro k hk
      simp only [Option.some.injEq] at hk
      subst hk
      simp [dif_pos hi]
  let S := C.gates.foldl (sstep n) s0
  have hall : ∀ x : Fin n → Bool, WF n S ∧ Inv t x S (C.gates.foldl step (List.ofFn x)) := by
    intro x
    refine fold_all t x C.gates s0 (List.ofFn x) ?_ hwf0 (hinv0 x)
    intro j hj
    simpa using hok j hj
  have hwfS : WF n S := (hall (fun _ => false)).1
  let D : Circuit := ⟨S.1, (S.2.getD C.output none).getD (n + S.1.length)⟩
  refine ⟨D, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- only AND and OR gates
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
    exact (hwfS.1 j hj).1
  · -- every gate reads earlier wires
    intro j hj i hi
    have hga : PEqualNP.MetaComplexity.NestedCover.gateAt D j = S.1[j] := by
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt
      exact List.getD_eq_getElem _ _ hj
    rw [hga] at hi
    obtain ⟨_, a, b, hab, ha, hb⟩ := hwfS.1 j hj
    rw [hab] at hi
    simp at hi
    rcases hi with rfl | rfl <;> assumption
  · -- exactly two inputs
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
    obtain ⟨_, a, b, hab, _, _⟩ := hwfS.1 j hj
    rw [hab]; rfl
  · -- fewer gates
    have hcnt : 1 ≤ C.gates.countP (fun g => decide (t.val ∈ g.inputs)) := by
      by_contra hc
      have h0 : ∀ g ∈ C.gates, t.val ∉ g.inputs := by
        intro g hg hm
        apply hc
        exact List.countP_pos_iff.2 ⟨g, hg, by simpa using hm⟩
      by_cases hout : C.output = t.val
      · apply absurd h1
        unfold PEqualNP.MetaComplexity.circuitFun Circuit.eval
        rw [wires_eq, hout, fold_prefix _ _ _ (by simp), getD_ofFn, dif_pos t.isLt]
        simp
      · apply absurd h3
        have e := indep t.val C.gates (List.ofFn fun x8 : Fin n => decide (x8 = u))
          (List.ofFn fun x9 : Fin n => decide (x9 = t ∨ x9 = u)) (by simp) ?_ h0 C.output hout
        · unfold PEqualNP.MetaComplexity.circuitFun Circuit.eval
          rw [wires_eq, ← e, ← wires_eq]
          unfold PEqualNP.MetaComplexity.circuitFun Circuit.eval at h2
          rw [h2]
          simp
        · intro i hi
          rw [getD_ofFn, getD_ofFn]
          split_ifs with h
          · have : (⟨i, h⟩ : Fin n) ≠ t := fun e => hi (by rw [← e])
            simp [this]
          · rfl
    have hlen := fold_len n t.val C.gates s0
      (fun g hg => by
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
        obtain ⟨hop, a, b, hab, _, _⟩ := hok j hj
        exact ⟨hop, a, b, hab⟩)
      (by simp only [s0, hm0, dif_pos t.isLt]; simp)
      (by simp [s0, m0])
    show S.1.length < C.gates.length
    have hS1 : S.1.length = (List.foldl (sstep n) ([], m0) C.gates).1.length := rfl
    simp only [s0, List.length_nil] at hlen
    omega
  · -- below the old circuit
    intro x hD
    obtain ⟨_, hl, hinv⟩ := hall x
    unfold PEqualNP.MetaComplexity.circuitFun Circuit.eval at hD ⊢
    rw [wires_eq] at hD ⊢
    simp only [D] at hD
    rcases hS : S.2.getD C.output none with _ | k
    · rw [hS] at hD
      simp only [Option.getD_none] at hD
      rw [List.getD_eq_default _ _ (by rw [len_fold]; simp)] at hD
      cases hD
    · rw [hS] at hD
      simp only [Option.getD_some] at hD
      by_cases ho : C.output < (C.gates.foldl step (List.ofFn x)).length
      · exact ((hinv C.output ho).2 k hS).1 hD
      · rw [List.getD_eq_default _ _ (by rw [hl]; omega)] at hS
        cases hS
  · -- equal where x3 is false
    intro x ht
    obtain ⟨_, hl, hinv⟩ := hall x
    unfold PEqualNP.MetaComplexity.circuitFun Circuit.eval
    rw [wires_eq, wires_eq]
    simp only [D]
    rcases hS : S.2.getD C.output none with _ | k
    · simp only [Option.getD_none]
      rw [List.getD_eq_default _ _ (by rw [len_fold]; simp)]
      by_cases ho : C.output < (C.gates.foldl step (List.ofFn x)).length
      · exact ((hinv C.output ho).1 hS ht).symm
      · rw [List.getD_eq_default _ _ (by omega)]
    · simp only [Option.getD_some]
      by_cases ho : C.output < (C.gates.foldl step (List.ofFn x)).length
      · exact ((hinv C.output ho).2 k hS).2 ht
      · rw [List.getD_eq_default _ _ (by rw [hl]; omega)] at hS
        cases hS
