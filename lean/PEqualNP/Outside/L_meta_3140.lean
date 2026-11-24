import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_3140

namespace Elim

def run (gs : List Gate) (w : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires w

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) :=
  rfl

theorem run_append_one (gs : List Gate) (g : Gate) (w : List Bool) :
    run (gs ++ [g]) w
      = run gs w ++ [g.op.eval (g.inputs.map fun i => (run gs w).getD i false)] := by
  simp [run, Circuit.wires, List.foldl_append]

theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run, Circuit.wires]
  | cons g gs ih =>
    rw [run_cons, ih]
    simp <;> omega

def val (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl b => b
  | Sum.inr k => w.getD k false

def act : GateOp → List (Bool ⊕ ℕ) → Option (Bool ⊕ ℕ)
  | GateOp.not, [] => some (Sum.inl true)
  | GateOp.not, Sum.inl b :: _ => some (Sum.inl (!b))
  | GateOp.and, [] => some (Sum.inl true)
  | GateOp.and, [s] => some s
  | GateOp.and, [Sum.inl b, s] => some (if b then s else Sum.inl false)
  | GateOp.and, [Sum.inr k, Sum.inl b] => some (if b then Sum.inr k else Sum.inl false)
  | GateOp.or, [] => some (Sum.inl false)
  | GateOp.or, [s] => some s
  | GateOp.or, [Sum.inl b, s] => some (if b then Sum.inl true else s)
  | GateOp.or, [Sum.inr k, Sum.inl b] => some (if b then Sum.inl true else Sum.inr k)
  | _, _ => none

def ins (a : List (Bool ⊕ ℕ)) : List ℕ := a.filterMap Sum.getRight?

theorem act_some (w : List Bool) (op : GateOp) (a : List (Bool ⊕ ℕ)) (s : Bool ⊕ ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hl : a.length ≤ 2)
    (h : act op a = some s) : val w s = op.eval (a.map (val w)) := by
  rcases hop with rfl | rfl | rfl <;>
  rcases a with _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, r⟩⟩⟩ <;>
  first
  | (simp only [List.length_cons] at hl; omega)
  | (simp [act] at h; subst h; simp [val, GateOp.eval])
  | (rcases s1 with (_ | _) | k1 <;> rcases s2 with (_ | _) | k2 <;>
      simp [act] at h <;> subst h <;> simp [val, GateOp.eval])
  | (rcases s1 with (_ | _) | k1 <;> simp [act] at h <;> subst h <;> simp [val, GateOp.eval])

theorem act_none (w : List Bool) (op : GateOp) (a : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hl : a.length ≤ 2)
    (h : act op a = none) :
    op.eval ((ins a).map fun k => w.getD k false) = op.eval (a.map (val w)) := by
  rcases hop with rfl | rfl | rfl <;>
  rcases a with _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, r⟩⟩⟩ <;>
  first
  | (simp only [List.length_cons] at hl; omega)
  | (simp [act] at h; done)
  | (rcases s1 with (_ | _) | k1 <;> rcases s2 with (_ | _) | k2 <;>
      simp [act] at h <;> simp [val, GateOp.eval, ins])
  | (rcases s1 with (_ | _) | k1 <;> simp [act] at h <;> simp [val, GateOp.eval, ins])

theorem act_mem (op : GateOp) (a : List (Bool ⊕ ℕ)) (k : ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hl : a.length ≤ 2)
    (h : act op a = some (Sum.inr k)) : Sum.inr k ∈ a := by
  rcases hop with rfl | rfl | rfl <;>
  rcases a with _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, r⟩⟩⟩ <;>
  first
  | (simp only [List.length_cons] at hl; omega)
  | (simp [act] at h; done)
  | (simp [act] at h; subst h; simp; done)
  | (rcases s1 with (_ | _) | k1 <;> rcases s2 with (_ | _) | k2 <;>
      simp [act] at h <;> simp [h])
  | (rcases s1 with (_ | _) | k1 <;> simp [act] at h <;> simp [h])

def Good (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

def step (n2 : ℕ) (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  match act g.op (g.inputs.map fun i => st.1.getD i (Sum.inl false)) with
  | some s => (st.1 ++ [s], st.2)
  | none => (st.1 ++ [Sum.inr (n2 + st.2.length)],
      st.2 ++ [⟨g.op, ins (g.inputs.map fun i => st.1.getD i (Sum.inl false))⟩])

theorem val_append (w e : List Bool) (s : Bool ⊕ ℕ)
    (h : ∀ k, s = Sum.inr k → k < w.length) : val (w ++ e) s = val w s := by
  rcases s with b | k
  · rfl
  · have hk := h k rfl
    simp [val, List.getElem?_append_left hk]

theorem val_getD (w : List Bool) (m : List (Bool ⊕ ℕ)) (i : ℕ) :
    val w (m.getD i (Sum.inl false)) = (m.map (val w)).getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases m[i]? <;> simp [val]

theorem getD_mem (m : List (Bool ⊕ ℕ)) (i k : ℕ)
    (h : m.getD i (Sum.inl false) = Sum.inr k) : Sum.inr k ∈ m := by
  simp only [List.getD_eq_getElem?_getD] at h
  cases hm : m[i]? with
  | none => simp [hm] at h
  | some s =>
    simp [hm] at h
    subst h
    exact List.mem_of_getElem? hm

theorem step_inv (y : List Bool) (n2 : ℕ) (hn : y.length = n2) (g : Gate) (W : List Bool)
    (st : List (Bool ⊕ ℕ) × List Gate) (hg : Good g)
    (h1 : st.1.map (val (run st.2 y)) = W)
    (h3 : ∀ k, Sum.inr k ∈ st.1 → k < n2 + st.2.length)
    (h4 : ∀ g' ∈ st.2, Good g') :
    (step n2 st g).1.map (val (run (step n2 st g).2 y))
        = W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)] ∧
      (∀ k, Sum.inr k ∈ (step n2 st g).1 → k < n2 + (step n2 st g).2.length) ∧
      (∀ g' ∈ (step n2 st g).2, Good g') := by
  obtain ⟨m, gs⟩ := st
  simp only at h1 h3 h4
  have hlen : (run gs y).length = n2 + gs.length := by rw [run_length, hn]
  have ha : (g.inputs.map fun i => m.getD i (Sum.inl false)).map (val (run gs y))
      = g.inputs.map fun i => W.getD i false := by
    rw [← h1, List.map_map]
    apply List.map_congr_left
    intro i _
    exact val_getD _ _ _
  have hal : (g.inputs.map fun i => m.getD i (Sum.inl false)).length ≤ 2 := by
    simpa using hg.2
  have hmem : ∀ k, Sum.inr k ∈ (g.inputs.map fun i => m.getD i (Sum.inl false)) →
      k < n2 + gs.length := by
    intro k hk
    obtain ⟨i, _, hi⟩ := List.mem_map.1 hk
    exact h3 k (getD_mem m i k hi)
  unfold step
  cases hact : act g.op (g.inputs.map fun i => m.getD i (Sum.inl false)) with
  | some s =>
    simp only
    refine ⟨?_, ?_, h4⟩
    · rw [List.map_append, h1, List.map_singleton, act_some _ _ _ _ hg.1 hal hact, ha]
    · intro k hk
      rcases List.mem_append.1 hk with hk | hk
      · exact h3 k hk
      · have hs : Sum.inr k = s := by simpa using hk
        subst hs
        exact hmem k (act_mem _ _ _ hg.1 hal hact)
  | none =>
    simp only
    refine ⟨?_, ?_, ?_⟩
    · rw [List.map_append, run_append_one, List.map_singleton]
      congr 1
      · rw [← h1]
        apply List.map_congr_left
        intro s hs
        apply val_append
        intro k hk
        subst hk
        rw [hlen]
        exact h3 k hs
      · simp only [val]
        rw [← hlen, List.getD_append_right _ _ _ _ (le_refl _)]
        simp only [Nat.sub_self, List.getD_cons_zero]
        rw [act_none _ _ _ hg.1 hal hact, ha]
    · intro k hk
      rcases List.mem_append.1 hk with hk | hk
      · have := h3 k hk
        simp only [List.length_append, List.length_singleton]
        omega
      · have hs : k = n2 + gs.length := by simpa using hk
        simp only [List.length_append, List.length_singleton]
        omega
    · intro g' hg'
      rcases List.mem_append.1 hg' with hg' | hg'
      · exact h4 g' hg'
      · have hs : g' = ⟨g.op, ins (g.inputs.map fun i => m.getD i (Sum.inl false))⟩ := by
          simpa using hg'
        subst hs
        refine ⟨hg.1, le_trans (List.length_filterMap_le _ _) hal⟩

theorem main (y : List Bool) (n2 : ℕ) (hn : y.length = n2) :
    ∀ (L : List Gate) (W : List Bool) (st : List (Bool ⊕ ℕ) × List Gate),
      (∀ g ∈ L, Good g) → st.1.map (val (run st.2 y)) = W →
      (∀ k, Sum.inr k ∈ st.1 → k < n2 + st.2.length) → (∀ g' ∈ st.2, Good g') →
      (L.foldl (step n2) st).1.map (val (run (L.foldl (step n2) st).2 y)) = run L W ∧
      (∀ g' ∈ (L.foldl (step n2) st).2, Good g') := by
  intro L
  induction L with
  | nil =>
    intro W st _ h1 _ h4
    exact ⟨h1, h4⟩
  | cons g L ih =>
    intro W st hL h1 h3 h4
    obtain ⟨a, b, c⟩ := step_inv y n2 hn g W st (hL g (by simp)) h1 h3 h4
    rw [List.foldl_cons, run_cons]
    exact ih _ _ (fun g' hg' => hL g' (by simp [hg'])) a b c

def Reads (v : ℕ) (g : Gate) : Prop :=
  v ∈ g.inputs ∧ (g.op = GateOp.not → g.inputs.head? = Option.some v)

theorem reads_act (v : ℕ) (m : List (Bool ⊕ ℕ)) (g : Gate) (hg : Good g)
    (hm : m.getD v (Sum.inl false) = Sum.inl false) (hr : Reads v g) :
    ∃ s, act g.op (g.inputs.map fun i => m.getD i (Sum.inl false)) = some s := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hl⟩ := hg
  obtain ⟨hr1, hr2⟩ := hr
  simp only at hop hl hr1 hr2 ⊢
  rcases hop with rfl | rfl | rfl
  · rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
    · simp at hr1
    · simp at hr1
      subst hr1
      simp [act]
    · simp at hr1
      rcases hr1 with rfl | rfl
      · simp only [List.map_cons, List.map_nil, hm]
        simp [act]
      · simp only [List.map_cons, List.map_nil, hm]
        rcases m.getD a (Sum.inl false) with (_ | _) | k <;> simp [act]
    · simp only [List.length_cons] at hl
      omega
  · rcases inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
    · simp at hr1
    · simp at hr1
      subst hr1
      simp [act]
    · simp at hr1
      rcases hr1 with rfl | rfl
      · simp only [List.map_cons, List.map_nil, hm]
        simp [act]
      · simp only [List.map_cons, List.map_nil, hm]
        rcases m.getD a (Sum.inl false) with (_ | _) | k <;> simp [act]
    · simp only [List.length_cons] at hl
      omega
  · have h := hr2 rfl
    rcases inputs with _ | ⟨a, r⟩
    · simp at h
    · simp at h
      subst h
      simp only [List.map_cons, hm]
      simp [act]

theorem step_fst (n2 : ℕ) (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    ∃ s, (step n2 st g).1 = st.1 ++ [s] := by
  unfold step
  cases act g.op (g.inputs.map fun i => st.1.getD i (Sum.inl false)) with
  | some s => exact ⟨s, rfl⟩
  | none => exact ⟨_, rfl⟩

theorem step_snd_le (n2 : ℕ) (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    (step n2 st g).2.length ≤ st.2.length + 1 := by
  unfold step
  cases act g.op (g.inputs.map fun i => st.1.getD i (Sum.inl false)) with
  | some s => simp
  | none => simp

theorem step_snd_eq (n2 v : ℕ) (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hg : Good g)
    (hm : st.1.getD v (Sum.inl false) = Sum.inl false) (hr : Reads v g) :
    (step n2 st g).2 = st.2 := by
  obtain ⟨s, hs⟩ := reads_act v st.1 g hg hm hr
  unfold step
  rw [hs]

theorem step_keep (n2 v : ℕ) (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate)
    (hv : v < st.1.length) (hm : st.1.getD v (Sum.inl false) = Sum.inl false) :
    v < (step n2 st g).1.length ∧ (step n2 st g).1.getD v (Sum.inl false) = Sum.inl false := by
  obtain ⟨s, hs⟩ := step_fst n2 st g
  rw [hs]
  refine ⟨by simp; omega, ?_⟩
  rw [List.getD_append _ _ _ _ hv]
  exact hm


def pred (P : List ℕ) (g : Gate) : Bool :=
  P.any fun v => (if g.op.eval [false] = true then List.take 1 g.inputs else g.inputs).contains v

theorem pred_reads (P : List ℕ) (g : Gate) (hg : Good g) (h : pred P g = true) :
    ∃ v ∈ P, Reads v g := by
  obtain ⟨v, hv, hc⟩ := List.any_eq_true.1 h
  refine ⟨v, hv, ?_⟩
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, _⟩ := hg
  simp only at hop
  rcases hop with rfl | rfl | rfl
  · simp [GateOp.eval] at hc
    exact ⟨hc, by simp⟩
  · simp [GateOp.eval] at hc
    exact ⟨hc, by simp⟩
  · simp [GateOp.eval] at hc
    rcases inputs with _ | ⟨a, r⟩
    · simp at hc
    · simp at hc
      subst hc
      exact ⟨by simp, fun _ => rfl⟩

theorem cntP (n2 : ℕ) (P : List ℕ) : ∀ (L : List Gate) (st : List (Bool ⊕ ℕ) × List Gate),
    (∀ g ∈ L, Good g) →
    (∀ v ∈ P, v < st.1.length ∧ st.1.getD v (Sum.inl false) = Sum.inl false) →
    (L.foldl (step n2) st).2.length + (L.filter (pred P)).length ≤ st.2.length + L.length := by
  intro L
  induction L with
  | nil => intro st _ _; simp
  | cons g L ih =>
    intro st hL hV
    have hV' : ∀ v ∈ P, v < (step n2 st g).1.length ∧
        (step n2 st g).1.getD v (Sum.inl false) = Sum.inl false :=
      fun v hv => step_keep n2 v st g (hV v hv).1 (hV v hv).2
    have hL' : ∀ g' ∈ L, Good g' := fun g' hg' => hL g' (by simp [hg'])
    have h1 := ih (step n2 st g) hL' hV'
    simp only [List.foldl_cons, List.length_cons]
    by_cases hp : pred P g = true
    · rw [List.filter_cons_of_pos hp, List.length_cons]
      obtain ⟨v, hv, hr⟩ := pred_reads P g (hL g (by simp)) hp
      rw [step_snd_eq n2 v st g (hL g (by simp)) (hV v hv).2 hr] at h1
      omega
    · rw [List.filter_cons_of_neg hp]
      have h2 := step_snd_le n2 st g
      omega


def Good2 (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def RB (n2 : ℕ) (gs : List Gate) : Prop :=
  ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n2 + j

theorem good_of_good2 (g : Gate) (h : Good2 g) : Good g :=
  ⟨by rcases h.1 with h | h <;> simp [h], by rw [h.2]⟩

theorem act_none_len (op : GateOp) (a : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or) (hl : a.length = 2)
    (h : act op a = none) : (ins a).length = 2 := by
  rcases a with _ | ⟨s1, _ | ⟨s2, _ | ⟨s3, r⟩⟩⟩
  · simp at hl
  · simp at hl
  · rcases hop with rfl | rfl <;>
    rcases s1 with (_ | _) | k1 <;> rcases s2 with (_ | _) | k2 <;> simp [act] at h <;> simp [ins]
  · simp at hl

theorem step_good2 (n2 : ℕ) (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hg : Good2 g)
    (h3 : ∀ k, Sum.inr k ∈ st.1 → k < n2 + st.2.length)
    (h4 : ∀ g' ∈ st.2, Good2 g') (h5 : RB n2 st.2) :
    (∀ g' ∈ (step n2 st g).2, Good2 g') ∧ RB n2 (step n2 st g).2 := by
  obtain ⟨m, gs⟩ := st
  simp only at h3 h4 h5
  unfold step
  cases hact : act g.op (g.inputs.map fun i => m.getD i (Sum.inl false)) with
  | some s => exact ⟨h4, h5⟩
  | none =>
    simp only
    refine ⟨?_, ?_⟩
    · intro g' hg'
      rcases List.mem_append.1 hg' with hg' | hg'
      · exact h4 g' hg'
      · have hs : g' = ⟨g.op, ins (g.inputs.map fun i => m.getD i (Sum.inl false))⟩ := by
          simpa using hg'
        subst hs
        refine ⟨hg.1, ?_⟩
        exact act_none_len _ _ hg.1 (by simpa using hg.2) hact
    · intro j hj i hi
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hjl : j < gs.length
      · rw [List.getD_append _ _ _ _ hjl] at hi
        exact h5 j hjl i hi
      · have hje : j = gs.length := by omega
        subst hje
        rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
        simp only [Nat.sub_self, List.getD_cons_zero] at hi
        simp only [ins, List.mem_filterMap] at hi
        obtain ⟨s, hs, hsi⟩ := hi
        rcases s with b | k
        · simp at hsi
        · simp at hsi
          subst hsi
          obtain ⟨i', _, hi'⟩ := List.mem_map.1 hs
          exact h3 k (getD_mem m i' k hi')

theorem main2 (n2 : ℕ) :
    ∀ (L : List Gate) (st : List (Bool ⊕ ℕ) × List Gate),
      (∀ g ∈ L, Good2 g) →
      (∀ k, Sum.inr k ∈ st.1 → k < n2 + st.2.length) → (∀ g' ∈ st.2, Good2 g') →
      RB n2 st.2 →
      (∀ k, Sum.inr k ∈ (L.foldl (step n2) st).1 → k < n2 + (L.foldl (step n2) st).2.length) ∧
      (∀ g' ∈ (L.foldl (step n2) st).2, Good2 g') ∧ RB n2 (L.foldl (step n2) st).2 := by
  intro L
  induction L with
  | nil =>
    intro st _ h3 h4 h5
    exact ⟨h3, h4, h5⟩
  | cons g L ih =>
    intro st hL h3 h4 h5
    have hg := hL g (by simp)
    obtain ⟨_, b, _⟩ := step_inv (List.replicate n2 false) n2 (by simp) g _ st
      (good_of_good2 g hg) rfl h3 (fun g' hg' => good_of_good2 g' (h4 g' hg'))
    obtain ⟨c, d⟩ := step_good2 n2 st g hg h3 h4 h5
    rw [List.foldl_cons]
    exact ih _ (fun g' hg' => hL g' (by simp [hg'])) b c d

theorem engine (n : ℕ) (C : Circuit) (ρ : List (Option (Fin n))) (P : List ℕ)
    (hG2 : ∀ g ∈ C.gates, Good2 g) (hP : ∀ v ∈ P, ρ[v]? = some none) :
    ∃ D : Circuit, (∀ g ∈ D.gates, Good2 g) ∧ RB n D.gates ∧
      D.gates.length + (C.gates.filter (pred P)).length ≤ C.gates.length ∧
      ((D.output < n + D.gates.length ∧
        ∀ y : Fin n → Bool, D.eval (List.ofFn y) = C.eval (ρ.map fun o => o.elim false y)) ∨
       ∃ b : Bool, ∀ y : Fin n → Bool, C.eval (ρ.map fun o => o.elim false y) = b) := by
  have hG : ∀ g ∈ C.gates, Good g := fun g hg => good_of_good2 g (hG2 g hg)
  obtain ⟨st0, hst0⟩ : ∃ st0 : List (Bool ⊕ ℕ) × List Gate,
      st0 = (ρ.map (fun o => o.elim (Sum.inl false) (fun j => Sum.inr j.val)), []) := ⟨_, rfl⟩
  obtain ⟨st, hst⟩ : ∃ st : List (Bool ⊕ ℕ) × List Gate,
      st = C.gates.foldl (step n) st0 := ⟨_, rfl⟩
  have h30 : ∀ k, Sum.inr k ∈ st0.1 → k < n + st0.2.length := by
    intro k hk
    rw [hst0] at hk
    obtain ⟨o, _, ho⟩ := List.mem_map.1 hk
    cases o with
    | none => cases ho
    | some j =>
      have hj : j.val = k := Sum.inr.inj ho
      have := j.isLt
      rw [hst0]
      simp only [List.length_nil]
      omega
  have h40 : ∀ g' ∈ st0.2, Good g' := by
    intro g' hg'
    rw [hst0] at hg'
    cases hg'
  have hmain : ∀ y : Fin n → Bool,
      st.1.map (val (run st.2 (List.ofFn y)))
        = run C.gates (ρ.map fun o => o.elim false y) ∧
      (∀ g' ∈ st.2, Good g') := by
    intro y
    rw [hst]
    apply main (List.ofFn y) n (by simp) C.gates _ st0 hG
    · rw [hst0, List.map_map]
      apply List.map_congr_left
      intro o _
      cases o with
      | none => rfl
      | some j => simp [run, Circuit.wires, val]
    · exact h30
    · exact h40
  have hm2 := main2 n C.gates st0 hG2 h30 (by intro g' hg'; rw [hst0] at hg'; cases hg')
    (by intro j hj; rw [hst0] at hj; simp at hj)
  rw [← hst] at hm2
  have hval : ∀ y : Fin n → Bool,
      C.eval (ρ.map fun o => o.elim false y) = val (run st.2 (List.ofFn y))
        (st.1.getD C.output (Sum.inl false)) := by
    intro y
    rw [val_getD, (hmain y).1]
    rfl
  have hcnt : st.2.length + (C.gates.filter (pred P)).length ≤ C.gates.length := by
    have := cntP n P C.gates st0 hG (by
      intro v hv
      have h := hP v hv
      have hlt : v < ρ.length := by
        by_contra hc
        rw [List.getElem?_eq_none (by omega)] at h
        cases h
      refine ⟨by rw [hst0]; simpa using hlt, ?_⟩
      rw [hst0]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, h]
      rfl)
    have h0 : st0.2.length = 0 := by rw [hst0]; rfl
    rw [hst]
    omega
  cases hout : st.1.getD C.output (Sum.inl false) with
  | inl b =>
    refine ⟨⟨[], 0⟩, by simp, by intro j hj; simp at hj, by simp only [List.length_nil]; omega, Or.inr ⟨b, ?_⟩⟩
    intro y
    rw [hval y, hout]
    rfl
  | inr k =>
    refine ⟨⟨st.2, k⟩, hm2.2.1, hm2.2.2, by simpa using hcnt, Or.inl ⟨?_, ?_⟩⟩
    · exact hm2.1 k (getD_mem _ _ _ hout)
    · intro y
      rw [hval y, hout]
      rfl


open PEqualNP.MetaComplexity.NestedCover

def AO2 (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def C0 (C : Circuit) (j : ℕ) : Circuit :=
  Circuit.mk (C.gates.set j (Gate.mk GateOp.or [])) C.output

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

theorem wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

theorem getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

theorem getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

theorem getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

theorem getD_wiresFrom_ge (gs : List Gate) (w : List Bool) (i : ℕ)
    (h : w.length + gs.length ≤ i) : (wiresFrom gs w).getD i false = false := by
  rw [List.getD_eq_default]
  rw [length_wiresFrom]; exact h

def sig (n : ℕ) (K : Finset ℕ) (w : ℕ) : ℕ :=
  if w < n then w else if w - n ∈ K then n else w + 1

def FF (n : ℕ) (C : Circuit) (K : Finset ℕ) (i : ℕ) : Gate :=
  if i ∈ K then ⟨GateOp.and, [n, n]⟩ else ⟨(gateAt C i).op, (gateAt C i).inputs.map (sig n K)⟩

def G2 (n : ℕ) (C : Circuit) (K : Finset ℕ) : List Gate :=
  (List.range C.gates.length).map (FF n C K)

def rho (n : ℕ) : List (Option (Fin n)) :=
  (List.ofFn fun i : Fin n => some i) ++ [none]

theorem rho_map (n : ℕ) (x : Fin n → Bool) :
    (rho n).map (fun o => o.elim false x) = List.ofFn x ++ [false] := by
  simp [rho, List.map_ofFn, Function.comp_def]

theorem gateAt_eq (C : Circuit) (i : ℕ) (hi : i < C.gates.length) :
    gateAt C i = C.gates[i] := by
  unfold gateAt
  exact List.getD_eq_getElem _ _ hi

theorem sim (n : ℕ) (C : Circuit) (j : ℕ) (K : Finset ℕ) (hRB : ReadsBack n C)
    (hjK : j ∈ K)
    (hout : ∀ k < C.gates.length, k ∉ K → ∀ w ∈ (gateAt C k).inputs, n ≤ w → w - n ∈ K → w = n + j)
    (x : Fin n → Bool) :
    ∀ i, i < C.gates.length → i ∉ K →
      (wiresFrom (G2 n C K) (List.ofFn x ++ [false])).getD (n + 1 + i) false
        = (wiresFrom (C0 C j).gates (List.ofFn x)).getD (n + i) false := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hi hiK
  have hij : i ≠ j := fun h => hiK (h ▸ hjK)
  have hl2 : (List.ofFn x ++ [false]).length = n + 1 := by simp
  have hl0 : (List.ofFn x).length = n := by simp
  have hG2l : (G2 n C K).length = C.gates.length := by simp [G2]
  have hC0l : (C0 C j).gates.length = C.gates.length := by simp [C0]
  have e2 := getD_wiresFrom_gate (G2 n C K) (List.ofFn x ++ [false]) i (by omega)
  have e0 := getD_wiresFrom_gate (C0 C j).gates (List.ofFn x) i (by omega)
  rw [hl2] at e2
  rw [hl0] at e0
  rw [e2, e0]
  have hF : (G2 n C K)[i]'(by omega) = ⟨(gateAt C i).op, (gateAt C i).inputs.map (sig n K)⟩ := by
    simp [G2, FF, hiK]
  have hC : (C0 C j).gates[i]'(by omega) = gateAt C i := by
    rw [gateAt_eq C i hi]
    simp [C0, List.getElem_set_ne (Ne.symm hij)]
  rw [hF, hC]
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro w hw
  have hwlt : w < n + i := hRB i hi w hw
  simp only [Function.comp_apply]
  rw [if_pos hwlt]
  unfold sig
  by_cases h1 : w < n
  · rw [if_pos h1, if_pos (by omega), getD_wiresFrom_lt _ _ _ (by omega),
      getD_wiresFrom_lt _ _ _ (by omega)]
    rw [List.getD_append _ _ _ _ (by simpa using h1)]
  · rw [if_neg h1]
    by_cases h2 : w - n ∈ K
    · rw [if_pos h2, if_pos (by omega)]
      have hw' : w = n + j := hout i hi hiK w hw (by omega) h2
      rw [getD_wiresFrom_lt _ _ _ (by simp)]
      have : (List.ofFn x ++ [false]).getD n false = false := by
        have := getD_snoc_eq (List.ofFn x) false
        rwa [hl0] at this
      rw [this]
      have hjl : j < C.gates.length := by omega
      have e0' := getD_wiresFrom_gate (C0 C j).gates (List.ofFn x) j (by omega)
      rw [hl0] at e0'
      rw [hw', e0']
      simp [C0, GateOp.eval]
    · rw [if_neg h2, if_pos (by omega)]
      have := ih (w - n) (by omega) (by omega) h2
      have e1 : n + 1 + (w - n) = w + 1 := by omega
      have e3 : n + (w - n) = w := by omega
      rw [e1, e3] at this
      exact this


theorem wiresFrom_false (gs : List Gate) (hg : ∀ g ∈ gs, Good2 g) :
    ∀ w : List Bool, (∀ i, w.getD i false = false) → ∀ i, (wiresFrom gs w).getD i false = false := by
  induction gs with
  | nil => intro w hw i; exact hw i
  | cons g gs ih =>
    intro w hw
    have hstep : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [hstep]
    apply ih (fun g' hg' => hg g' (by simp [hg']))
    intro i
    have hgg := hg g (by simp)
    have hv : g.op.eval (g.inputs.map fun i => w.getD i false) = false := by
      obtain ⟨hop, hl⟩ := hgg
      rcases g with ⟨op, inputs⟩
      simp only at hop hl ⊢
      rcases inputs with _ | ⟨u, _ | ⟨v, _ | ⟨t, r⟩⟩⟩
      · simp at hl
      · simp at hl
      · rcases hop with rfl | rfl <;> simp only [GateOp.eval, List.map_cons, List.map_nil, hw] <;> rfl
      · simp at hl
    by_cases hi : i < w.length
    · rw [List.getD_append _ _ _ _ hi]; exact hw i
    · by_cases he : i = w.length
      · subst he; rw [getD_snoc_eq]; exact hv
      · rw [List.getD_eq_default]; simp; omega

theorem elim (n : ℕ) (C : Circuit) (j k k' : ℕ) (K : Finset ℕ) (hA : AO2 C) (hRB : ReadsBack n C)
    (hjK : j ∈ K) (hle : ∀ i ∈ K, i ≤ j) (hkk : k ≠ k') (hk : k < C.gates.length)
    (hk' : k' < C.gates.length) (hrk : n + j ∈ (gateAt C k).inputs)
    (hrk' : n + j ∈ (gateAt C k').inputs)
    (hout : ∀ k < C.gates.length, k ∉ K → ∀ w ∈ (gateAt C k).inputs, n ≤ w → w - n ∈ K → w = n + j)
    (hO : ¬ (n ≤ C.output ∧ C.output - n ∈ K)) :
    ∃ (E : Circuit) (o : Option ℕ), AO2 E ∧ ReadsBack n E ∧ E.gates.length + K.card + 2 ≤ C.gates.length ∧
      (∀ w ∈ o, w < n + E.gates.length) ∧
      ∀ x : Fin n → Bool, o.elim false (fun w => (E.wires (List.ofFn x)).getD w false) = circuitFun n (C0 C j) x := by
  have hjk : j < k := by have := hRB k hk (n + j) hrk; omega
  have hjk' : j < k' := by have := hRB k' hk' (n + j) hrk'; omega
  have hkK : k ∉ K := fun h => by have := hle k h; omega
  have hkK' : k' ∉ K := fun h => by have := hle k' h; omega
  have hG2l : (G2 n C K).length = C.gates.length := by simp [G2]
  have hgood : ∀ g ∈ G2 n C K, Good2 g := by
    intro g hg
    simp only [G2, List.mem_map, List.mem_range] at hg
    obtain ⟨i, hi, rfl⟩ := hg
    unfold FF
    split_ifs with hiK
    · exact ⟨Or.inl rfl, rfl⟩
    · have h := hA (gateAt C i) (by rw [gateAt_eq C i hi]; exact List.getElem_mem hi)
      exact ⟨h.1, by simpa using h.2⟩
  have hP : ∀ v ∈ [n], (rho n)[v]? = some none := by
    intro v hv
    simp at hv
    subst hv
    simp [rho, List.getElem?_append_right]
  obtain ⟨D, hDg, hDrb, hDcnt, hcase⟩ := engine n ⟨G2 n C K, sig n K C.output⟩ (rho n) [n] hgood hP
  have hfun : ∀ x : Fin n → Bool,
      (Circuit.mk (G2 n C K) (sig n K C.output)).eval ((rho n).map fun o => o.elim false x)
        = circuitFun n (C0 C j) x := by
    intro x
    rw [rho_map]
    show (wiresFrom (G2 n C K) (List.ofFn x ++ [false])).getD (sig n K C.output) false
      = (wiresFrom (C0 C j).gates (List.ofFn x)).getD C.output false
    have hC0l : (C0 C j).gates.length = C.gates.length := by simp [C0]
    unfold sig
    by_cases h1 : C.output < n
    · rw [if_pos h1, getD_wiresFrom_lt _ _ _ (by simp; omega), getD_wiresFrom_lt _ _ _ (by simp; omega)]
      rw [List.getD_append _ _ _ _ (by simpa using h1)]
    · rw [if_neg h1]
      have h2 : C.output - n ∉ K := fun h => hO ⟨by omega, h⟩
      rw [if_neg h2]
      by_cases h3 : C.output - n < C.gates.length
      · have := sim n C j K hRB hjK hout x (C.output - n) h3 h2
        have e1 : n + 1 + (C.output - n) = C.output + 1 := by omega
        have e3 : n + (C.output - n) = C.output := by omega
        rw [e1, e3] at this
        exact this
      · rw [getD_wiresFrom_ge _ _ _ (by simp; omega), getD_wiresFrom_ge _ _ _ (by simp; omega)]
  have hcount : K.card + 2 ≤ ((G2 n C K).filter (pred [n])).length := by
    have hfm : (G2 n C K).filter (pred [n])
        = ((List.range C.gates.length).filter (fun i => pred [n] (FF n C K i))).map (FF n C K) := by
      unfold G2
      rw [List.filter_map]
      rfl
    rw [hfm, List.length_map]
    have hsub : insert k (insert k' K) ⊆
        ((List.range C.gates.length).filter (fun i => pred [n] (FF n C K i))).toFinset := by
      intro i hi
      rw [List.mem_toFinset, List.mem_filter, List.mem_range]
      simp only [Finset.mem_insert] at hi
      have hsig : sig n K (n + j) = n := by
        unfold sig
        rw [if_neg (by omega), if_pos (by simpa using hjK)]
      rcases hi with rfl | rfl | hiK
      · refine ⟨hk, ?_⟩
        have hop := (hA (gateAt C i) (by rw [gateAt_eq C i hk]; exact List.getElem_mem hk)).1
        have hmem : n ∈ (gateAt C i).inputs.map (sig n K) := List.mem_map.2 ⟨n + j, hrk, hsig⟩
        unfold FF pred
        rw [if_neg hkK]
        rcases hop with hop | hop <;> simp [hop, GateOp.eval] <;> exact ⟨n + j, by assumption, hsig⟩
      · refine ⟨hk', ?_⟩
        have hop := (hA (gateAt C i) (by rw [gateAt_eq C i hk']; exact List.getElem_mem hk')).1
        have hmem : n ∈ (gateAt C i).inputs.map (sig n K) := List.mem_map.2 ⟨n + j, hrk', hsig⟩
        unfold FF pred
        rw [if_neg hkK']
        rcases hop with hop | hop <;> simp [hop, GateOp.eval] <;> exact ⟨n + j, by assumption, hsig⟩
      · refine ⟨by have := hle i hiK; omega, ?_⟩
        unfold FF pred
        rw [if_pos hiK]
        simp [GateOp.eval]
    have hc1 := Finset.card_le_card hsub
    have hc2 := List.toFinset_card_le ((List.range C.gates.length).filter (fun i => pred [n] (FF n C K i)))
    have hc3 : (insert k (insert k' K)).card = K.card + 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hkk, hkK]), Finset.card_insert_of_notMem hkK']
    omega
  have hDle : D.gates.length + K.card + 2 ≤ C.gates.length := by
    have : D.gates.length + ((G2 n C K).filter (pred [n])).length ≤ (G2 n C K).length := hDcnt
    omega
  rcases hcase with ⟨hDo, hDf⟩ | ⟨bb, hb⟩
  · refine ⟨D, some D.output, hDg, hDrb, hDle, ?_, ?_⟩
    · intro w hw
      simp at hw
      subst hw
      exact hDo
    · intro x
      rw [← hfun x, ← hDf x]
      rfl
  · have hbf : bb = false := by
      rw [← hb (fun _ => false), rho_map]
      exact wiresFrom_false _ hgood _ (by
        intro i
        by_cases hi : i < n
        · rw [List.getD_append _ _ _ _ (by simpa using hi)]; simp [hi]
        · by_cases he : i = n
          · subst he
            have := getD_snoc_eq (List.ofFn (fun _ : Fin i => false)) false
            simpa using this
          · rw [List.getD_eq_default]; simp; omega) _
    refine ⟨⟨[], 0⟩, none, by intro g hg; simp at hg, by intro i hi; simp at hi, by simp; omega,
      by intro w hw; simp at hw, ?_⟩
    intro x
    rw [← hfun x, hb x, hbf]
    rfl

end Elim

-- wire lemmas, count, cone_reads from w1-p-sprint/cone3.lean
def w_step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem w_wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl w_step x := rfl

theorem w_foldl_length (G : List Gate) (w : List Bool) :
    (G.foldl w_step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [w_step]; omega

theorem w_getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem w_getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem w_foldl_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl w_step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [w_step]; omega)]
    exact w_getD_append_lt _ _ _ hi

theorem w_foldl_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl w_step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i =>
        ((G.take t).foldl w_step w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [w_foldl_getD _ _ _ (by simp only [w_step, List.length_append, List.length_singleton, w_foldl_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [w_step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [w_foldl_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [w_foldl_length, Nat.min_eq_left ht.le]

theorem w_foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl w_step w).length) :
    (G.foldl w_step w).getD i false =
      ((G.take t).foldl w_step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact w_foldl_getD _ _ _ hi

theorem w_gate_value (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl w_step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i =>
        if i < w.length + t then (G.foldl w_step w).getD i false else false) := by
  rw [w_foldl_getD_gate G w t ht]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : ((G.take t).foldl w_step w).length = w.length + t := by
    rw [w_foldl_length, List.length_take, Nat.min_eq_left ht.le]
  split_ifs with h
  · exact (w_foldl_take_getD G w t i (by rw [hlen]; exact h)).symm
  · exact w_getD_of_length_le _ _ (by rw [hlen]; omega)

theorem w_wire_gate {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
  have hg : gateAt C j = C.gates[j] := by
    simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rw [w_wires_eq, ← hx, w_gate_value C.gates x j hj, hg]
  congr 1
  apply List.map_congr_left
  intro i hi
  have := hRB j hj i (by rw [hg]; exact hi)
  rw [if_pos (by omega)]
def AO2 (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def RK (n : ℕ) (C : Circuit) (K : Finset ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun w => ∃ i ∈ K, w ∈ (gateAt C i).inputs)

theorem gateAt_len (C : Circuit) (hA : AO2 C) (i : ℕ) (hi : i < C.gates.length) :
    (gateAt C i).inputs.length = 2 := by
  have : gateAt C i = C.gates[i] := by
    simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rw [this]
  exact (hA _ (List.getElem_mem hi)).2

theorem count (n : ℕ) (C : Circuit) (j : ℕ) (K : Finset ℕ) (hA : AO2 C)
    (hK : ∀ i ∈ K, i < C.gates.length)
    (hread : ∀ i ∈ K, i ≠ j → ∃ k ∈ K, n + i ∈ (gateAt C k).inputs) :
    (RK n C K).card ≤ K.card + 1 := by
  classical
  let D : Finset ℕ := RK n C K ∪ (K.erase j).image (fun i => n + i)
  have hdisj : Disjoint (RK n C K) ((K.erase j).image (fun i => n + i)) := by
    rw [Finset.disjoint_left]
    intro w hw hw2
    simp only [RK, Finset.mem_filter, Finset.mem_range] at hw
    simp only [Finset.mem_image] at hw2
    obtain ⟨i, _, rfl⟩ := hw2
    omega
  have hD : D.card = (RK n C K).card + (K.erase j).card := by
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ (fun x y h => by simpa using h)]
  have hex : ∀ w ∈ D, ∃ s ∈ K ×ˢ Finset.range 2, (gateAt C s.1).inputs[s.2]? = some w := by
    intro w hw
    have hmem : ∃ i ∈ K, w ∈ (gateAt C i).inputs := by
      rcases Finset.mem_union.mp hw with h | h
      · simp only [RK, Finset.mem_filter] at h
        exact h.2
      · simp only [Finset.mem_image, Finset.mem_erase] at h
        obtain ⟨i, ⟨hij, hi⟩, rfl⟩ := h
        exact hread i hi hij
    obtain ⟨i, hi, hw⟩ := hmem
    obtain ⟨pos, hpos, hget⟩ := List.getElem_of_mem hw
    refine ⟨(i, pos), ?_, ?_⟩
    · have := gateAt_len C hA i (hK i hi)
      simp only [Finset.mem_product, Finset.mem_range]
      exact ⟨hi, by omega⟩
    · simp [List.getElem?_eq_getElem hpos, hget]
  let g : ℕ → ℕ × ℕ := fun w =>
    if h : ∃ s ∈ K ×ˢ Finset.range 2, (gateAt C s.1).inputs[s.2]? = some w then Classical.choose h
    else (0, 0)
  have hg : ∀ w ∈ D, g w ∈ K ×ˢ Finset.range 2 ∧ (gateAt C (g w).1).inputs[(g w).2]? = some w := by
    intro w hw
    have h := hex w hw
    simp only [g, dite_eq_left_iff, h]
    exact Classical.choose_spec h
  have hle : D.card ≤ (K ×ˢ Finset.range 2).card := by
    apply Finset.card_le_card_of_injOn g
    · intro w hw
      exact (hg w hw).1
    · intro w hw w' hw' he
      have h1 := (hg w hw).2
      have h2 := (hg w' hw').2
      rw [he] at h1
      rw [h1] at h2
      exact Option.some_injective _ h2
  rw [Finset.card_product, Finset.card_range] at hle
  have hj : (K.erase j).card + 1 ≥ K.card := by
    have := Finset.pred_card_le_card_erase (s := K) (a := j)
    omega
  omega

theorem input_getD (C : Circuit) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (C.wires x).getD w false = x.getD w false := by
  rw [w_wires_eq]; exact w_foldl_getD _ _ _ hw

theorem cone_agree (n : ℕ) (C : Circuit) (K : Finset ℕ) (hRB : ReadsBack n C)
    (hK : ∀ i ∈ K, i < C.gates.length)
    (hcl : ∀ i ∈ K, ∀ w ∈ (gateAt C i).inputs, n ≤ w → w - n ∈ K)
    (x x' : List Bool) (hx : x.length = n) (hx' : x'.length = n)
    (hag : ∀ w ∈ RK n C K, x.getD w false = x'.getD w false) :
    ∀ i ∈ K, (C.wires x).getD (n + i) false = (C.wires x').getD (n + i) false := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rw [w_wire_gate hRB x hx i (hK i hi), w_wire_gate hRB x' hx' i (hK i hi)]
    congr 1
    apply List.map_congr_left
    intro w hw
    by_cases hwn : w < n
    · rw [input_getD C x w (by omega), input_getD C x' w (by omega)]
      apply hag
      simp only [RK, Finset.mem_filter, Finset.mem_range]
      exact ⟨hwn, i, hi, hw⟩
    · have h1 := hcl i hi w hw (by omega)
      have h2 := hRB i (hK i hi) w hw
      have := ih (w - n) (by omega) h1
      have he : n + (w - n) = w := by omega
      rw [he] at this
      exact this

def C0 (C : Circuit) (j : ℕ) : Circuit :=
  Circuit.mk (C.gates.set j (Gate.mk GateOp.or [])) C.output

theorem gateAt_C0 (C : Circuit) (j i : ℕ) (hi : i < C.gates.length) :
    gateAt (C0 C j) i = if i = j then Gate.mk GateOp.or [] else gateAt C i := by
  by_cases h : i = j
  · subst h
    simp [gateAt, C0, List.getD_eq_getElem?_getD, hi]
  · have h' : j ≠ i := Ne.symm h
    simp [gateAt, C0, List.getD_eq_getElem?_getD, h, List.getElem?_set_ne h']

theorem rb_C0 (n : ℕ) (C : Circuit) (j : ℕ) (hRB : ReadsBack n C) : ReadsBack n (C0 C j) := by
  intro i hi w hw
  have hi' : i < C.gates.length := by simpa [C0] using hi
  rw [gateAt_C0 C j i hi'] at hw
  split_ifs at hw with h
  · simp at hw
  · exact hRB i hi' w hw

theorem wires_len (C : Circuit) (x : List Bool) : (C.wires x).length = x.length + C.gates.length := by
  rw [w_wires_eq]; exact w_foldl_length _ _

theorem c0_agree (n : ℕ) (C : Circuit) (j : ℕ) (hRB : ReadsBack n C) (x : List Bool)
    (hx : x.length = n) (hj0 : (C.wires x).getD (n + j) false = false) :
    ∀ w, ((C0 C j).wires x).getD w false = (C.wires x).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    have hlen : (C0 C j).gates.length = C.gates.length := by simp [C0]
    by_cases hwn : w < n
    · rw [input_getD _ x w (by omega), input_getD _ x w (by omega)]
    · by_cases hwl : w < n + C.gates.length
      · have hi : w - n < C.gates.length := by omega
        have he : w = n + (w - n) := by omega
        rw [he, w_wire_gate (rb_C0 n C j hRB) x hx (w - n) (by omega), gateAt_C0 C j _ hi]
        split_ifs with h
        · rw [h, hj0]; simp [GateOp.eval]
        · rw [w_wire_gate hRB x hx (w - n) hi]
          congr 1
          apply List.map_congr_left
          intro u hu
          exact ih u (by have := hRB (w - n) hi u hu; omega)
      · rw [w_getD_of_length_le _ _ (by rw [wires_len, hlen]; omega),
          w_getD_of_length_le _ _ (by rw [wires_len]; omega)]

theorem not_read (n : ℕ) (C : Circuit) (j : ℕ) (K : Finset ℕ) (hRB : ReadsBack n C)
    (hj : j < C.gates.length) (hjK : j ∈ K) (hle : ∀ i ∈ K, i ≤ j)
    (hcl : ∀ i ∈ K, ∀ w ∈ (gateAt C i).inputs, n ≤ w → w - n ∈ K)
    (hone : ∀ v : Fin n, (C.wires (List.ofFn (fun u : Fin n => decide (u = v)))).getD (n + j) false = false)
    (u v : Fin n) (z : Fin n → Bool) (hz : ∀ e, e ≠ u → z e = decide (e = v))
    (hlost : circuitFun n (C0 C j) z = false) (htrue : circuitFun n C z = true) :
    u.val ∈ RK n C K := by
  by_contra hu
  have hK : ∀ i ∈ K, i < C.gates.length := fun i hi => by have := hle i hi; omega
  have hag : ∀ w ∈ RK n C K, (List.ofFn z).getD w false
      = (List.ofFn (fun e : Fin n => decide (e = v))).getD w false := by
    intro w hw
    have hwn : w < n := by
      simp only [RK, Finset.mem_filter, Finset.mem_range] at hw; exact hw.1
    have hne : (⟨w, hwn⟩ : Fin n) ≠ u := by
      intro h; apply hu; rw [← h]; exact hw
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hwn, hz _ hne]
  have h1 := cone_agree n C K hRB hK hcl (List.ofFn z) _ (by simp) (by simp) hag j hjK
  rw [hone v] at h1
  have h2 := c0_agree n C j hRB (List.ofFn z) (by simp) h1 C.output
  have e1 : circuitFun n (C0 C j) z = ((C0 C j).wires (List.ofFn z)).getD C.output false := rfl
  have e2 : circuitFun n C z = (C.wires (List.ofFn z)).getD C.output false := rfl
  rw [e1, h2, ← e2, htrue] at hlost
  exact absurd hlost (by decide)

theorem cone_reads (a b : ℕ) (C : Circuit) (j : ℕ) (K : Finset ℕ)
    (hRB : ReadsBack (a + b) C) (hj : j < C.gates.length)
    (hone : ∀ v : Fin (a + b), (C.wires (List.ofFn (fun u : Fin (a + b) => decide (u = v)))).getD (a + b + j) false = false)
    (hjK : j ∈ K) (hle : ∀ i ∈ K, i ≤ j)
    (hcl : ∀ i ∈ K, ∀ w ∈ (gateAt C i).inputs, a + b ≤ w → w - (a + b) ∈ K)
    (p : Fin a) (l : Fin b)
    (hlost : circuitFun (a + b) (C0 C j) (fun e => decide (e = Fin.castAdd b p ∨ e = Fin.natAdd a l)) = false)
    (htrue : circuitFun (a + b) C (fun e => decide (e = Fin.castAdd b p ∨ e = Fin.natAdd a l)) = true) :
    p.val ∈ RK (a + b) C K ∧ a + l.val ∈ RK (a + b) C K := by
  constructor
  · have := not_read (a + b) C j K hRB hj hjK hle hcl hone (Fin.castAdd b p) (Fin.natAdd a l) _
      (fun e he => by simp [he]) hlost htrue
    simpa using this
  · have := not_read (a + b) C j K hRB hj hjK hle hcl hone (Fin.natAdd a l) (Fin.castAdd b p) _
      (fun e he => by simp [he]) hlost htrue
    simpa using this


theorem elim (n : ℕ) (C : Circuit) (j k k' : ℕ) (K : Finset ℕ) (hA : AO2 C) (hRB : ReadsBack n C)
    (hjK : j ∈ K) (hle : ∀ i ∈ K, i ≤ j) (hkk : k ≠ k') (hk : k < C.gates.length)
    (hk' : k' < C.gates.length) (hrk : n + j ∈ (gateAt C k).inputs)
    (hrk' : n + j ∈ (gateAt C k').inputs)
    (hout : ∀ k < C.gates.length, k ∉ K → ∀ w ∈ (gateAt C k).inputs, n ≤ w → w - n ∈ K → w = n + j)
    (hO : ¬ (n ≤ C.output ∧ C.output - n ∈ K)) :
    ∃ (E : Circuit) (o : Option ℕ), AO2 E ∧ ReadsBack n E ∧ E.gates.length + K.card + 2 ≤ C.gates.length ∧
      (∀ w ∈ o, w < n + E.gates.length) ∧
      ∀ x : Fin n → Bool, o.elim false (fun w => (E.wires (List.ofFn x)).getD w false) = circuitFun n (C0 C j) x := by
  exact Elim.elim n C j k k' K hA hRB hjK hle hkk hk hk' hrk hrk' hout hO

-- star forest circuits from w1-p-structured/stars.lean
namespace Stars

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (G : List Gate) (x : List Bool) : List Bool := G.foldl step x

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

lemma W_length (G : List Gate) (x : List Bool) : (W G x).length = x.length + G.length := by
  induction G generalizing x with
  | nil => simp [W]
  | cons g G ih =>
    simp only [W, List.foldl_cons] at ih ⊢
    rw [ih]; simp [step]; omega

lemma getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma W_prefix (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (W G w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    simp only [W, List.foldl_cons] at ih ⊢
    rw [ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

lemma W_append (G H : List Gate) (x : List Bool) : W (G ++ H) x = W H (W G x) := by
  simp [W, List.foldl_append]

lemma W_append_lt (G H : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + G.length) :
    (W (G ++ H) x).getD i false = (W G x).getD i false := by
  rw [W_append]; exact W_prefix _ _ _ (by rw [W_length]; exact hi)

lemma W_snoc_eq (G : List Gate) (g : Gate) (x : List Bool) :
    (W (G ++ [g]) x).getD (x.length + G.length) false =
      g.op.eval (g.inputs.map fun i => (W G x).getD i false) := by
  rw [W_append]
  simp only [W, List.foldl_cons, List.foldl_nil, step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by
    have := W_length G x; simp only [W] at this; omega)]
  have := W_length G x; simp only [W] at this
  simp [this]

lemma W_input {n : ℕ} (G : List Gate) (z : Fin n → Bool) (s : Fin n) :
    (W G (List.ofFn z)).getD s.val false = z s := by
  rw [W_prefix _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

lemma W_ge {n : ℕ} (G : List Gate) (z : Fin n → Bool) (i : ℕ) (hi : n + G.length ≤ i) :
    (W G (List.ofFn z)).getD i false = false :=
  getD_of_length_le _ _ (by rw [W_length]; simp; omega)

def Good (n : ℕ) (G : List Gate) : Prop :=
  (∀ g ∈ G, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
    ReadsBack n ⟨G, 0⟩

lemma Good_snoc {n : ℕ} (G : List Gate) (hG : Good n G) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (u v : ℕ) (hu : u < n + G.length)
    (hv : v < n + G.length) : Good n (G ++ [⟨op, [u, v]⟩]) := by
  refine ⟨?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with h | h
    · exact hG.1 g h
    · rw [List.mem_singleton] at h; subst h; exact ⟨hop, rfl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    unfold gateAt at hi
    simp only at hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
    · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left h] at hi
      have := hG.2 j h i
      unfold gateAt at this
      simp only at this
      rw [List.getD_eq_getElem _ _ h] at this
      exact this hi
    · subst h
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp)] at hi
      simp at hi
      rcases hi with h | h <;> omega

lemma W_snoc_val {n : ℕ} (G : List Gate) (g : Gate) (z : Fin n → Bool) :
    (W (G ++ [g]) (List.ofFn z)).getD (n + G.length) false =
      g.op.eval (g.inputs.map fun i => (W G (List.ofFn z)).getD i false) := by
  have := W_snoc_eq G g (List.ofFn z)
  simp only [List.length_ofFn] at this
  exact this

lemma or_chain {n : ℕ} (N : Finset (Fin n)) (hN : N.Nonempty) (G : List Gate) (hG : Good n G) :
    ∃ G1 : List Gate, ∃ w : ℕ, Good n G1 ∧ G1.length + 1 ≤ G.length + N.card ∧
      G.length ≤ G1.length ∧ w < n + G1.length ∧
      (∀ z : Fin n → Bool, ∀ i < n + G.length,
        (W G1 (List.ofFn z)).getD i false = (W G (List.ofFn z)).getD i false) ∧
      ∀ z : Fin n → Bool, ((W G1 (List.ofFn z)).getD w false = true ↔ ∃ s ∈ N, z s = true) := by
  induction hN using Finset.Nonempty.cons_induction with
  | singleton s =>
    refine ⟨G, s.val, hG, by simp, le_rfl, by have := s.isLt; omega, fun z i hi => rfl, fun z => ?_⟩
    rw [W_input]; simp
  | cons s N hs hN ih =>
    obtain ⟨G1, w, hG1, hlen, hle, hw, hpre, hval⟩ := ih
    refine ⟨G1 ++ [Gate.mk GateOp.or [w, s.val]], n + G1.length,
      Good_snoc G1 hG1 _ (Or.inr rfl) _ _ hw (by have := s.isLt; omega), ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton, Finset.card_cons]; omega
    · simp; omega
    · simp
    · intro z i hi
      rw [W_append_lt _ _ _ _ (by simp; omega)]
      exact hpre z i hi
    · intro z
      rw [W_snoc_val]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id, W_input, Bool.or_eq_true, hval, Finset.mem_cons]
      constructor
      · rintro (⟨t, ht, hz⟩ | h)
        · exact ⟨t, Or.inr ht, hz⟩
        · exact ⟨s, Or.inl rfl, h⟩
      · rintro ⟨t, (rfl | ht), hz⟩
        · exact Or.inr hz
        · exact Or.inl ⟨t, ht, hz⟩

lemma star_step {n : ℕ} (G : List Gate) (hG : Good n G) (acc : ℕ) (c : Fin n)
    (N : Finset (Fin n)) (hN : N.Nonempty) :
    ∃ G1 : List Gate, ∃ acc1 : ℕ, Good n G1 ∧ G1.length ≤ G.length + N.card + 1 ∧
      ∀ z : Fin n → Bool, ((W G1 (List.ofFn z)).getD acc1 false = true ↔
        ((W G (List.ofFn z)).getD acc false = true ∨ (z c = true ∧ ∃ s ∈ N, z s = true))) := by
  obtain ⟨G1, w, hG1, hlen, hle, hw, hpre, hval⟩ := or_chain N hN G hG
  have hG2 : Good n (G1 ++ [Gate.mk GateOp.and [c.val, w]]) :=
    Good_snoc G1 hG1 _ (Or.inl rfl) _ _ (by have := c.isLt; omega) hw
  have ht : ∀ z : Fin n → Bool,
      (W (G1 ++ [Gate.mk GateOp.and [c.val, w]]) (List.ofFn z)).getD (n + G1.length) false = true ↔
        (z c = true ∧ ∃ s ∈ N, z s = true) := by
    intro z
    rw [W_snoc_val]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      Bool.and_true, id, W_input, Bool.and_eq_true, hval]
  by_cases hacc : acc < n + G.length
  · refine ⟨(G1 ++ [Gate.mk GateOp.and [c.val, w]]) ++ [Gate.mk GateOp.or [acc, n + G1.length]],
      n + (G1 ++ [Gate.mk GateOp.and [c.val, w]]).length,
      Good_snoc _ hG2 _ (Or.inr rfl) _ _ (by simp; omega) (by simp), ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton]; omega
    · intro z
      rw [W_snoc_val]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id, Bool.or_eq_true]
      rw [ht z, W_append_lt _ _ _ _ (by simp; omega), hpre z acc hacc]
  · refine ⟨G1 ++ [Gate.mk GateOp.and [c.val, w]], n + G1.length, hG2, by simp; omega, ?_⟩
    intro z
    rw [ht z, W_ge G z acc (by omega)]
    simp

lemma castAdd_ne_natAdd {a b : ℕ} (p : Fin a) (l : Fin b) : Fin.castAdd b p ≠ Fin.natAdd a l := by
  intro h
  have := congrArg Fin.val h
  simp at this
  have := p.isLt
  omega

lemma stars_main (a b : ℕ) (m : ℕ) : ∀ (R : Finset (Fin (a + b))), R.card ≤ m →
    ∀ (S : Fin a → Fin b → Prop),
    (∀ (p p' : Fin a) (l l' : Fin b), S p l → S p' l → S p l' → p' = p ∨ l' = l) →
    (∀ p l, S p l → Fin.castAdd b p ∈ R ∧ Fin.natAdd a l ∈ R) →
    ∀ (G : List Gate), Good (a + b) G → ∀ acc : ℕ,
    ∃ G' : List Gate, ∃ acc' : ℕ, Good (a + b) G' ∧ G'.length ≤ G.length + R.card ∧
      ∀ z : Fin (a + b) → Bool, ((W G' (List.ofFn z)).getD acc' false = true ↔
        ((W G (List.ofFn z)).getD acc false = true ∨
          ∃ (p : Fin a) (l : Fin b), S p l ∧ z (Fin.castAdd b p) = true ∧
            z (Fin.natAdd a l) = true)) := by
  classical
  induction m with
  | zero =>
    intro R hR S _ hSR G hG acc
    refine ⟨G, acc, hG, by omega, fun z => ?_⟩
    have hR0 : R = ∅ := Finset.card_eq_zero.1 (by omega)
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨p, l, hpl, _⟩)
      · exact h
      · exact absurd (hSR p l hpl).1 (by simp [hR0])
  | succ m ih =>
    intro R hR S hP3 hSR G hG acc
    by_cases hE : ∃ p l, S p l
    · by_cases hRt : ∃ (l : Fin b) (p p' : Fin a), p ≠ p' ∧ S p l ∧ S p' l
      · obtain ⟨l, p, p', hpp', hpl, hp'l⟩ := hRt
        have hdeg : ∀ q l1, S q l → S q l1 → l1 = l := by
          intro q l1 hq hq1
          by_cases hqp : q = p
          · subst hqp
            rcases hP3 q p' l l1 hq hp'l hq1 with h | h
            · exact absurd h.symm hpp'
            · exact h
          · rcases hP3 q p l l1 hq hpl hq1 with h | h
            · exact absurd h.symm hqp
            · exact h
        set N : Finset (Fin (a + b)) := (Finset.univ.filter (fun q => S q l)).image (Fin.castAdd b)
          with hNdef
        set c : Fin (a + b) := Fin.natAdd a l with hcdef
        have hNne : N.Nonempty := ⟨Fin.castAdd b p, by
          simp only [hNdef, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨p, hpl, rfl⟩⟩
        obtain ⟨G1, acc1, hG1, hlen1, hval1⟩ := star_step G hG acc c N hNne
        have hcN : c ∉ N := by
          simp only [hNdef, hcdef, Finset.mem_image, not_exists, not_and]
          intro q _ h
          exact castAdd_ne_natAdd q l h
        have hsub : insert c N ⊆ R := by
          intro v hv
          rcases Finset.mem_insert.1 hv with h | h
          · rw [h]; exact (hSR p l hpl).2
          · simp only [hNdef, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at h
            obtain ⟨q, hq, rfl⟩ := h
            exact (hSR q l hq).1
        have hcard : (R \ insert c N).card + N.card + 1 = R.card := by
          rw [Finset.card_sdiff_of_subset hsub, Finset.card_insert_of_notMem hcN]
          have := Finset.card_le_card hsub
          rw [Finset.card_insert_of_notMem hcN] at this
          omega
        obtain ⟨G', acc', hG', hlen', hval'⟩ := ih (R \ insert c N) (by omega)
          (fun q l1 => S q l1 ∧ l1 ≠ l)
          (fun q q' l1 l1' h1 h2 h3 => hP3 q q' l1 l1' h1.1 h2.1 h3.1)
          (by
            intro q l1 hq
            have hq1 := hSR q l1 hq.1
            refine ⟨Finset.mem_sdiff.2 ⟨hq1.1, ?_⟩, Finset.mem_sdiff.2 ⟨hq1.2, ?_⟩⟩
            · intro hm
              rcases Finset.mem_insert.1 hm with h | h
              · exact castAdd_ne_natAdd q l h
              · simp only [hNdef, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
                  true_and] at h
                obtain ⟨q2, hq2, hq2e⟩ := h
                have : q2 = q := Fin.castAdd_injective _ _ hq2e
                subst this
                exact hq.2 (hdeg q2 l1 hq2 hq.1)
            · intro hm
              rcases Finset.mem_insert.1 hm with h | h
              · exact hq.2 (Fin.natAdd_injective _ _ h)
              · simp only [hNdef, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
                  true_and] at h
                obtain ⟨q2, _, hq2e⟩ := h
                exact castAdd_ne_natAdd q2 l1 hq2e)
          G1 hG1 acc1
        refine ⟨G', acc', hG', by omega, fun z => ?_⟩
        rw [hval', hval1]
        constructor
        · rintro ((h | ⟨hc, s, hs, hzs⟩) | ⟨q, l1, hq, hz1, hz2⟩)
          · exact Or.inl h
          · simp only [hNdef, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
              true_and] at hs
            obtain ⟨q, hq, rfl⟩ := hs
            exact Or.inr ⟨q, l, hq, hzs, hc⟩
          · exact Or.inr ⟨q, l1, hq.1, hz1, hz2⟩
        · rintro (h | ⟨q, l1, hq, hz1, hz2⟩)
          · exact Or.inl (Or.inl h)
          · by_cases hl1 : l1 = l
            · subst hl1
              refine Or.inl (Or.inr ⟨hz2, Fin.castAdd b q, ?_, hz1⟩)
              simp only [hNdef, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨q, hq, rfl⟩
            · exact Or.inr ⟨q, l1, ⟨hq, hl1⟩, hz1, hz2⟩
      · push Not at hRt
        obtain ⟨p, l, hpl⟩ := hE
        set N : Finset (Fin (a + b)) := (Finset.univ.filter (fun l1 => S p l1)).image (Fin.natAdd a)
          with hNdef
        set c : Fin (a + b) := Fin.castAdd b p with hcdef
        have hNne : N.Nonempty := ⟨Fin.natAdd a l, by
          simp only [hNdef, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨l, hpl, rfl⟩⟩
        obtain ⟨G1, acc1, hG1, hlen1, hval1⟩ := star_step G hG acc c N hNne
        have hcN : c ∉ N := by
          simp only [hNdef, hcdef, Finset.mem_image, not_exists, not_and]
          intro q _ h
          exact castAdd_ne_natAdd p q h.symm
        have hsub : insert c N ⊆ R := by
          intro v hv
          rcases Finset.mem_insert.1 hv with h | h
          · rw [h]; exact (hSR p l hpl).1
          · simp only [hNdef, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at h
            obtain ⟨q, hq, rfl⟩ := h
            exact (hSR p q hq).2
        have hcard : (R \ insert c N).card + N.card + 1 = R.card := by
          rw [Finset.card_sdiff_of_subset hsub, Finset.card_insert_of_notMem hcN]
          have := Finset.card_le_card hsub
          rw [Finset.card_insert_of_notMem hcN] at this
          omega
        obtain ⟨G', acc', hG', hlen', hval'⟩ := ih (R \ insert c N) (by omega)
          (fun q l1 => S q l1 ∧ q ≠ p)
          (fun q q' l1 l1' h1 h2 h3 => hP3 q q' l1 l1' h1.1 h2.1 h3.1)
          (by
            intro q l1 hq
            have hq1 := hSR q l1 hq.1
            refine ⟨Finset.mem_sdiff.2 ⟨hq1.1, ?_⟩, Finset.mem_sdiff.2 ⟨hq1.2, ?_⟩⟩
            · intro hm
              rcases Finset.mem_insert.1 hm with h | h
              · exact hq.2 (Fin.castAdd_injective _ _ h)
              · simp only [hNdef, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
                  true_and] at h
                obtain ⟨q2, _, hq2e⟩ := h
                exact castAdd_ne_natAdd q q2 hq2e.symm
            · intro hm
              rcases Finset.mem_insert.1 hm with h | h
              · exact castAdd_ne_natAdd p l1 h.symm
              · simp only [hNdef, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
                  true_and] at h
                obtain ⟨q2, hq2, hq2e⟩ := h
                have : q2 = l1 := Fin.natAdd_injective _ _ hq2e
                subst this
                exact hRt q2 p q (Ne.symm hq.2) hq2 hq.1)
          G1 hG1 acc1
        refine ⟨G', acc', hG', by omega, fun z => ?_⟩
        rw [hval', hval1]
        constructor
        · rintro ((h | ⟨hc, s, hs, hzs⟩) | ⟨q, l1, hq, hz1, hz2⟩)
          · exact Or.inl h
          · simp only [hNdef, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
              true_and] at hs
            obtain ⟨q, hq, rfl⟩ := hs
            exact Or.inr ⟨p, q, hq, hc, hzs⟩
          · exact Or.inr ⟨q, l1, hq.1, hz1, hz2⟩
        · rintro (h | ⟨q, l1, hq, hz1, hz2⟩)
          · exact Or.inl (Or.inl h)
          · by_cases hqp : q = p
            · subst hqp
              refine Or.inl (Or.inr ⟨hz1, Fin.natAdd a l1, ?_, hz2⟩)
              simp only [hNdef, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨l1, hq, rfl⟩
            · exact Or.inr ⟨q, l1, ⟨hq, hqp⟩, hz1, hz2⟩
    · refine ⟨G, acc, hG, by omega, fun z => ?_⟩
      constructor
      · intro h; exact Or.inl h
      · rintro (h | ⟨p, l, hpl, _⟩)
        · exact h
        · exact absurd ⟨p, l, hpl⟩ hE

theorem stars (a b : ℕ) (S : Fin a → Fin b → Prop)
    (hP3 : ∀ (p p' : Fin a) (l l' : Fin b), S p l → S p' l → S p l' → p' = p ∨ l' = l)
    (E : Circuit)
    (hE : ∀ g ∈ E.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hRB : ReadsBack (a + b) E) (R : Finset (Fin (a + b)))
    (hR : ∀ p l, S p l → Fin.castAdd b p ∈ R ∧ Fin.natAdd a l ∈ R) :
    ∃ F : Circuit, (∀ g ∈ F.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        g.inputs.length = 2) ∧ ReadsBack (a + b) F ∧ F.size ≤ E.size + R.card ∧
      ∀ z : Fin (a + b) → Bool, (circuitFun (a + b) F z = true ↔
        (circuitFun (a + b) E z = true ∨ ∃ (p : Fin a) (l : Fin b), S p l ∧
          z (Fin.castAdd b p) = true ∧ z (Fin.natAdd a l) = true)) := by
  obtain ⟨G', acc', hG', hlen, hval⟩ :=
    stars_main a b R.card R le_rfl S hP3 hR E.gates ⟨hE, hRB⟩ E.output
  exact ⟨⟨G', acc'⟩, hG'.1, hG'.2, hlen, fun z => hval z⟩

theorem stars_nat (a b : ℕ) (S : Fin a → Fin b → Prop)
    (hP3 : ∀ (p p' : Fin a) (l l' : Fin b), S p l → S p' l → S p l' → p' = p ∨ l' = l)
    (E : Circuit)
    (hE : ∀ g ∈ E.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hRB : ReadsBack (a + b) E) (R : Finset ℕ)
    (hR : ∀ p l, S p l → (Fin.castAdd b p).val ∈ R ∧ (Fin.natAdd a l).val ∈ R) :
    ∃ F : Circuit, (∀ g ∈ F.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        g.inputs.length = 2) ∧ ReadsBack (a + b) F ∧ F.size ≤ E.size + R.card ∧
      ∀ z : Fin (a + b) → Bool, (circuitFun (a + b) F z = true ↔
        (circuitFun (a + b) E z = true ∨ ∃ (p : Fin a) (l : Fin b), S p l ∧
          z (Fin.castAdd b p) = true ∧ z (Fin.natAdd a l) = true)) := by
  classical
  obtain ⟨F, h1, h2, h3, h4⟩ := stars a b S hP3 E hE hRB
    (Finset.univ.filter (fun v : Fin (a + b) => v.val ∈ R))
    (fun p l h => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hR p l h)
  refine ⟨F, h1, h2, le_trans h3 ?_, h4⟩
  have : (Finset.univ.filter (fun v : Fin (a + b) => v.val ∈ R)).card ≤ R.card := by
    apply Finset.card_le_card_of_injOn (fun v => v.val)
    · intro v hv
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
      exact hv
    · intro v _ w _ h
      exact Fin.ext h
  omega


end Stars

theorem stars (a b : ℕ) (S : Fin a → Fin b → Prop)
    (hS : ∀ (p p' : Fin a) (l l' : Fin b), S p l → S p' l → S p l' → p' = p ∨ l' = l)
    (E : Circuit) (hEA : AO2 E) (hERB : ReadsBack (a + b) E) (R : Finset (Fin (a + b)))
    (hR : ∀ p l, S p l → Fin.castAdd b p ∈ R ∧ Fin.natAdd a l ∈ R) :
    ∃ F : Circuit, AO2 F ∧ ReadsBack (a + b) F ∧ F.size ≤ E.size + R.card ∧
      ∀ z : Fin (a + b) → Bool, circuitFun (a + b) F z = true ↔
        (circuitFun (a + b) E z = true ∨
          ∃ (p : Fin a) (l : Fin b), S p l ∧ z (Fin.castAdd b p) = true ∧ z (Fin.natAdd a l) = true) :=
  Stars.stars a b S hS E hEA hERB R hR

-- monotone lemmas from w1-p-automation/mono.lean
namespace Mono

def Le (g g' : Gate) : Prop :=
  g = Gate.mk GateOp.or [] ∨ (g = g' ∧ (g.op = GateOp.and ∨ g.op = GateOp.or))

def Imp (v v' : List Bool) : Prop :=
  v.length = v'.length ∧ ∀ i, v.getD i false = true → v'.getD i false = true

theorem eval_le (g g' : Gate) (h : Le g g') (v v' : List Bool) (hv : Imp v v') :
    g.op.eval (g.inputs.map fun i => v.getD i false) = true →
      g'.op.eval (g'.inputs.map fun i => v'.getD i false) = true := by
  rcases h with h | ⟨rfl, hop⟩
  · subst h
    simp [GateOp.eval]
  · rcases hop with hop | hop
    · rw [hop]
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
      intro H x hx
      obtain ⟨i, hi, rfl⟩ := hx
      exact hv.2 i (H _ ⟨i, hi, rfl⟩)
    · rw [hop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
      rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
      exact ⟨_, ⟨i, hi, rfl⟩, hv.2 i hx⟩

theorem imp_snoc (v v' : List Bool) (b b' : Bool) (hv : Imp v v') (hb : b = true → b' = true) :
    Imp (v ++ [b]) (v' ++ [b']) := by
  refine ⟨by simp [hv.1], ?_⟩
  intro i hi
  rcases lt_trichotomy i v.length with h | h | h
  · rw [List.getD_append _ _ _ _ h] at hi
    rw [List.getD_append _ _ _ _ (by rw [← hv.1]; exact h)]
    exact hv.2 i hi
  · subst h
    rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
    rw [hv.1, List.getD_append_right _ _ _ _ (le_refl _)]
    simp only [Nat.sub_self, List.getD_cons_zero] at hi ⊢
    exact hb hi
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
    simp at hi

theorem fold_le : ∀ (G G' : List Gate), List.Forall₂ Le G G' → ∀ (v v' : List Bool), Imp v v' →
    Imp (G.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) v)
      (G'.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) v') := by
  intro G G' h
  induction h with
  | nil => intro v v' hv; exact hv
  | cons hg _ ih =>
    intro v v' hv
    simp only [List.foldl_cons]
    exact ih _ _ (imp_snoc _ _ _ _ hv (eval_le _ _ hg v v' hv))

theorem forall₂_set (G : List Gate) (j : ℕ)
    (hG : ∀ g ∈ G, g.op = GateOp.and ∨ g.op = GateOp.or) :
    List.Forall₂ Le (G.set j (Gate.mk GateOp.or [])) G := by
  induction G generalizing j with
  | nil => simp
  | cons g G ih =>
    cases j with
    | zero =>
      simp only [List.set_cons_zero]
      refine List.Forall₂.cons (Or.inl rfl) ?_
      clear ih
      induction G with
      | nil => exact List.Forall₂.nil
      | cons g' G ih' =>
        exact List.Forall₂.cons (Or.inr ⟨rfl, hG g' (by simp)⟩)
          (ih' (fun g'' hg'' => hG g'' (by
            simp only [List.mem_cons] at hg'' ⊢
            tauto)))
    | succ j =>
      simp only [List.set_cons_succ]
      exact List.Forall₂.cons (Or.inr ⟨rfl, hG g (by simp)⟩)
        (ih j (fun g' hg' => hG g' (List.mem_cons_of_mem _ hg')))

theorem forall₂_self (G : List Gate) (hG : ∀ g ∈ G, Le g g) : List.Forall₂ Le G G := by
  induction G with
  | nil => exact List.Forall₂.nil
  | cons g G ih =>
    exact List.Forall₂.cons (hG g (by simp)) (ih (fun g' hg' => hG g' (List.mem_cons_of_mem _ hg')))

theorem le_C0 {n : ℕ} (C : Circuit) (j : ℕ) (hA : AO2 C) (z : Fin n → Bool) :
    circuitFun n (C0 C j) z = true → circuitFun n C z = true := by
  have h := fold_le _ _ (forall₂_set C.gates j (fun g hg => (hA g hg).1))
    (List.ofFn z) (List.ofFn z) ⟨rfl, fun _ h => h⟩
  exact h.2 C.output

theorem in_C0 {n : ℕ} (C : Circuit) (j : ℕ) (hA : AO2 C) (z z' : Fin n → Bool)
    (hz : ∀ e, z e = true → z' e = true) :
    circuitFun n (C0 C j) z = true → circuitFun n (C0 C j) z' = true := by
  have hself : ∀ g ∈ C.gates.set j (Gate.mk GateOp.or []), Le g g := by
    intro g hg
    rcases List.mem_or_eq_of_mem_set hg with hg | hg
    · exact Or.inr ⟨rfl, (hA g hg).1⟩
    · exact Or.inl hg
  have hx : Imp (List.ofFn z) (List.ofFn z') := by
    refine ⟨by simp, ?_⟩
    intro i hi
    by_cases h : i < n
    · rw [List.getD_eq_getElem _ _ (by simp; exact h), List.getElem_ofFn] at hi ⊢
      exact hz _ hi
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at hi
      simp at hi
  have h := fold_le _ _ (forall₂_self _ hself) _ _ hx
  exact h.2 C.output

end Mono

theorem wires_length (C : Circuit) (x : List Bool) : (C.wires x).length = x.length + C.gates.length := by
  unfold Circuit.wires
  generalize C.gates = gs
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp
    omega

theorem c0_ops (C : Circuit) (j : ℕ) (hD : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ g ∈ (C0 C j).gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
  intro g hg
  have := List.mem_or_eq_of_mem_set hg
  rcases this with h | h
  · exact hD g h
  · subst h; exact Or.inr rfl

theorem decomp (a b : ℕ) (I : Fin a → Fin b → Prop) (C : Circuit) (j : ℕ)
    (hA : AO2 C)
    (hF : ∀ z : Fin (a + b) → Bool, circuitFun (a + b) C z = true ↔
      ∃ (p : Fin a) (l : Fin b), I p l ∧ z (Fin.castAdd b p) = true ∧ z (Fin.natAdd a l) = true)
    (z : Fin (a + b) → Bool) :
    (∃ (p : Fin a) (l : Fin b), I p l ∧ z (Fin.castAdd b p) = true ∧ z (Fin.natAdd a l) = true) ↔
      (circuitFun (a + b) (C0 C j) z = true ∨
        ∃ (p : Fin a) (l : Fin b), (I p l ∧ circuitFun (a + b) (C0 C j)
          (fun e => decide (e = Fin.castAdd b p ∨ e = Fin.natAdd a l)) = false) ∧
          z (Fin.castAdd b p) = true ∧ z (Fin.natAdd a l) = true) := by
  constructor
  · rintro ⟨p, l, hI, hp, hl⟩
    by_cases h : circuitFun (a + b) (C0 C j) (fun e => decide (e = Fin.castAdd b p ∨ e = Fin.natAdd a l)) = true
    · left
      refine Mono.in_C0 C j hA _ z ?_ h
      intro i hi
      simp only [decide_eq_true_eq] at hi
      rcases hi with rfl | rfl
      · exact hp
      · exact hl
    · right
      exact ⟨p, l, ⟨hI, by simpa using h⟩, hp, hl⟩
  · rintro (h | ⟨p, l, ⟨hI, _⟩, hp, hl⟩)
    · exact (hF z).1 (Mono.le_C0 C j hA z h)
    · exact ⟨p, l, hI, hp, hl⟩

end PEqualNP.Outside.L_meta_3140

theorem PEqualNP.Outside.L_meta_3140 : ∀ (a b : ℕ) (I : Fin a → Fin b → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ) (K : Finset ℕ), (∀ (p p' : Fin a) (l l' : Fin b), p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (a + b) C → (∀ z : Fin (a + b) → Bool, PEqualNP.MetaComplexity.circuitFun (a + b) C z = true ↔ ∃ (p : Fin a) (l : Fin b), I p l ∧ z (Fin.castAdd b p) = true ∧ z (Fin.natAdd a l) = true) → j < C.gates.length → (∀ v : Fin (a + b), (C.wires (List.ofFn (fun u : Fin (a + b) => decide (u = v)))).getD (a + b + j) false = false) → (∃ k k' : ℕ, k ≠ k' ∧ k < C.gates.length ∧ k' < C.gates.length ∧ a + b + j ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs ∧ a + b + j ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k').inputs) → j ∈ K → (∀ i ∈ K, i ≤ j) → (∀ i ∈ K, ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).inputs, a + b ≤ w → w - (a + b) ∈ K) → (∀ i ∈ K, i ≠ j → ∃ k ∈ K, a + b + i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) → (∀ k < C.gates.length, k ∉ K → ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, a + b ≤ w → w - (a + b) ∈ K → w = a + b + j) → ¬ (a + b ≤ C.output ∧ C.output - (a + b) ∈ K) → (∀ (p p' : Fin a) (l l' : Fin b), (I p l ∧ PEqualNP.MetaComplexity.circuitFun (a + b) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set j (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun e1 : Fin (a + b) => decide (e1 = Fin.castAdd b p ∨ e1 = Fin.natAdd a l)) = false) → (I p' l ∧ PEqualNP.MetaComplexity.circuitFun (a + b) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set j (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun e2 : Fin (a + b) => decide (e2 = Fin.castAdd b p' ∨ e2 = Fin.natAdd a l)) = false) → (I p l' ∧ PEqualNP.MetaComplexity.circuitFun (a + b) (PEqualNP.CircuitLowerBounds.Circuit.mk (C.gates.set j (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [])) C.output) (fun e3 : Fin (a + b) => decide (e3 = Fin.castAdd b p ∨ e3 = Fin.natAdd a l')) = false) → p' = p ∨ l' = l) → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C'.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (a + b) C' ∧ C'.size < C.size ∧ (∀ z : Fin (a + b) → Bool, PEqualNP.MetaComplexity.circuitFun (a + b) C' z = true ↔ ∃ (p : Fin a) (l : Fin b), I p l ∧ z (Fin.castAdd b p) = true ∧ z (Fin.natAdd a l) = true) := by
  intro a b I C j K _hC4 hA hRB hF hj hone hrd hjK hle hcl hread hout hO hstar
  obtain ⟨k, k', hkk, hk, hk', hrk, hrk'⟩ := hrd
  have hA' : PEqualNP.Outside.L_meta_3140.AO2 C := hA
  have hD : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := fun g hg => (hA g hg).1
  obtain ⟨E0, o, hEA, hERB, hElen, ho, hEval⟩ :=
    PEqualNP.Outside.L_meta_3140.elim (a + b) C j k k' K hA' hRB hjK hle hkk hk hk' hrk hrk' hout hO
  let E : PEqualNP.CircuitLowerBounds.Circuit :=
    PEqualNP.CircuitLowerBounds.Circuit.mk E0.gates (o.getD (a + b + E0.gates.length))
  have hEfun : ∀ z : Fin (a + b) → Bool, PEqualNP.MetaComplexity.circuitFun (a + b) E z =
      PEqualNP.MetaComplexity.circuitFun (a + b) (PEqualNP.Outside.L_meta_3140.C0 C j) z := by
    intro z
    rw [← hEval z]
    cases o with
    | some w => rfl
    | none =>
      show (E0.wires (List.ofFn z)).getD (a + b + E0.gates.length) false = false
      have hlen := PEqualNP.Outside.L_meta_3140.wires_length E0 (List.ofFn z)
      rw [List.length_ofFn] at hlen
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
  have hEA' : PEqualNP.Outside.L_meta_3140.AO2 E := hEA
  have hERB' : PEqualNP.MetaComplexity.NestedCover.ReadsBack (a + b) E := hERB
  let S : Fin a → Fin b → Prop := fun p l => I p l ∧ PEqualNP.MetaComplexity.circuitFun (a + b)
    (PEqualNP.Outside.L_meta_3140.C0 C j) (fun e => decide (e = Fin.castAdd b p ∨ e = Fin.natAdd a l)) = false
  have hS : ∀ (p p' : Fin a) (l l' : Fin b), S p l → S p' l → S p l' → p' = p ∨ l' = l :=
    fun p p' l l' h1 h2 h3 => hstar p p' l l' h1 h2 h3
  let R : Finset (Fin (a + b)) :=
    Finset.univ.filter (fun v : Fin (a + b) => v.val ∈ PEqualNP.Outside.L_meta_3140.RK (a + b) C K)
  have hRcard : R.card ≤ K.card + 1 := by
    have h1 : R.card ≤ (PEqualNP.Outside.L_meta_3140.RK (a + b) C K).card := by
      have : R.map Fin.valEmbedding ⊆ PEqualNP.Outside.L_meta_3140.RK (a + b) C K := by
        intro w hw
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, R] at hw
        obtain ⟨v, hv, rfl⟩ := hw
        exact hv
      have := Finset.card_le_card this
      rwa [Finset.card_map] at this
    have hK : ∀ i ∈ K, i < C.gates.length := fun i hi => lt_of_le_of_lt (hle i hi) hj
    have h2 := PEqualNP.Outside.L_meta_3140.count (a + b) C j K hA' hK hread
    omega
  have hR : ∀ p l, S p l → Fin.castAdd b p ∈ R ∧ Fin.natAdd a l ∈ R := by
    intro p l hpl
    have htrue : PEqualNP.MetaComplexity.circuitFun (a + b) C
        (fun e => decide (e = Fin.castAdd b p ∨ e = Fin.natAdd a l)) = true := by
      rw [hF]
      exact ⟨p, l, hpl.1, by simp, by simp⟩
    have hc := PEqualNP.Outside.L_meta_3140.cone_reads a b C j K hRB hj hone hjK hle hcl p l hpl.2 htrue
    constructor
    · simp only [R, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castAdd]
      exact hc.1
    · simp only [R, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_natAdd]
      exact hc.2
  obtain ⟨F, hFA, hFRB, hFsize, hFfun⟩ :=
    PEqualNP.Outside.L_meta_3140.stars a b S hS E hEA' hERB' R hR
  refine ⟨F, hFA, hFRB, ?_, ?_⟩
  · have h1 : E.size = E0.gates.length := rfl
    have h2 : C.size = C.gates.length := rfl
    omega
  · intro z
    rw [hFfun z, hEfun z]
    exact (PEqualNP.Outside.L_meta_3140.decomp a b I C j hA' hF z).symm
