import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2305

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def interp (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl b => b
  | Sum.inr k => w.getD k false

def lk (vals : List (Bool ⊕ ℕ)) (i : ℕ) : Bool ⊕ ℕ := vals.getD i (Sum.inl false)

def idx : Bool ⊕ ℕ → ℕ
  | Sum.inl _ => 0
  | Sum.inr k => k

def andV : Bool ⊕ ℕ → Bool ⊕ ℕ → Bool ⊕ ℕ
  | Sum.inl true, b => b
  | Sum.inl false, _ => Sum.inl false
  | Sum.inr a, Sum.inl true => Sum.inr a
  | Sum.inr _, Sum.inl false => Sum.inl false
  | Sum.inr a, Sum.inr _ => Sum.inr a

def orV : Bool ⊕ ℕ → Bool ⊕ ℕ → Bool ⊕ ℕ
  | Sum.inl true, _ => Sum.inl true
  | Sum.inl false, b => b
  | Sum.inr _, Sum.inl true => Sum.inl true
  | Sum.inr a, Sum.inl false => Sum.inr a
  | Sum.inr a, Sum.inr _ => Sum.inr a

def notV : Bool ⊕ ℕ → Bool ⊕ ℕ
  | Sum.inl b => Sum.inl (!b)
  | Sum.inr a => Sum.inr a

def simV : GateOp → List (Bool ⊕ ℕ) → Bool ⊕ ℕ
  | GateOp.and, [a] => a
  | GateOp.and, [a, b] => andV a b
  | GateOp.or, [a] => a
  | GateOp.or, [a, b] => orV a b
  | GateOp.not, a :: _ => notV a
  | _, _ => Sum.inl true

def Ok (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 ∧
    (g.op = GateOp.not → g.inputs.length ≤ 1)

def sim : List (Bool ⊕ ℕ) → ℕ → List Gate → List Gate
  | _, _, [] => []
  | vals, m, g :: gs =>
    if (g.inputs.map (lk vals)).all Sum.isRight then
      ⟨g.op, (g.inputs.map (lk vals)).map idx⟩ :: sim (vals ++ [Sum.inr m]) (m + 1) gs
    else sim (vals ++ [simV g.op (g.inputs.map (lk vals))]) m gs

def fv : List (Bool ⊕ ℕ) → ℕ → List Gate → List (Bool ⊕ ℕ)
  | vals, _, [] => vals
  | vals, m, g :: gs =>
    if (g.inputs.map (lk vals)).all Sum.isRight then
      fv (vals ++ [Sum.inr m]) (m + 1) gs
    else fv (vals ++ [simV g.op (g.inputs.map (lk vals))]) m gs

theorem simV_ok (w : List Bool) (op : GateOp) (vs : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hl : vs.length ≤ 2)
    (hn : op = GateOp.not → vs.length ≤ 1) (hc : vs.all Sum.isRight = false) :
    interp w (simV op vs) = op.eval (vs.map (interp w)) := by
  rcases hop with rfl | rfl | rfl <;>
  rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> simp at hl hc hn <;>
  rcases a with (_ | _) | a <;> (try rcases b with (_ | _) | b) <;>
  simp_all [simV, andV, orV, notV, interp, GateOp.eval]

theorem simV_mem (op : GateOp) (vs : List (Bool ⊕ ℕ)) (k : ℕ)
    (h : simV op vs = Sum.inr k) : Sum.inr k ∈ vs := by
  rcases op with _ | _ | _ | m | _ <;>
  rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
  (try rcases a with (_ | _) | a) <;> (try rcases b with (_ | _) | b) <;>
  simp_all [simV, andV, orV, notV]

theorem lk_app_lt (vals l : List (Bool ⊕ ℕ)) (i : ℕ) (h : i < vals.length) :
    lk (vals ++ l) i = lk vals i := List.getD_append _ _ _ _ h

theorem lk_app_cases (vals : List (Bool ⊕ ℕ)) (v : Bool ⊕ ℕ) (i : ℕ) :
    lk (vals ++ [v]) i = lk vals i ∨ lk (vals ++ [v]) i = v := by
  rcases lt_trichotomy i vals.length with h | h | h
  · exact Or.inl (lk_app_lt _ _ _ h)
  · right
    subst h
    unfold lk
    rw [List.getD_append_right _ _ _ _ (le_refl _)]
    simp
  · left
    unfold lk
    rw [List.getD_eq_default (hn := by simp; omega), List.getD_eq_default (hn := by omega)]

theorem interp_app (w l : List Bool) (v : Bool ⊕ ℕ) (h : ∀ k, v = Sum.inr k → k < w.length) :
    interp (w ++ l) v = interp w v := by
  rcases v with b | k
  · rfl
  · exact List.getD_append _ _ _ _ (h k rfl)

theorem ext_step (oldW newW newW' : List Bool) (vals : List (Bool ⊕ ℕ)) (b : Bool)
    (v : Bool ⊕ ℕ) (hlen : oldW.length = vals.length)
    (hinv : ∀ i, oldW.getD i false = interp newW (lk vals i))
    (hb : ∀ i k, lk vals i = Sum.inr k → k < newW.length)
    (hmono : ∀ u, (∀ k, u = Sum.inr k → k < newW.length) → interp newW' u = interp newW u)
    (hv : interp newW' v = b) :
    ∀ i, (oldW ++ [b]).getD i false = interp newW' (lk (vals ++ [v]) i) := by
  intro i
  rcases lt_trichotomy i vals.length with h | h | h
  · rw [List.getD_append _ _ _ _ (by omega), lk_app_lt _ _ _ h, hinv, hmono _ (hb i)]
  · subst h
    rw [List.getD_append_right _ _ _ _ (by omega)]
    unfold lk
    rw [List.getD_append_right _ _ _ _ (le_refl _)]
    simp [hlen, hv]
  · rw [List.getD_eq_default (hn := by simp; omega)]
    unfold lk
    rw [List.getD_eq_default (hn := by simp; omega)]
    rfl

theorem sim_correct (gs : List Gate) : ∀ (oldW newW : List Bool) (vals : List (Bool ⊕ ℕ)),
    (∀ g ∈ gs, Ok g) → oldW.length = vals.length →
    (∀ i, oldW.getD i false = interp newW (lk vals i)) →
    (∀ i k, lk vals i = Sum.inr k → k < newW.length) →
    ∀ i, (gs.foldl stp oldW).getD i false =
      interp ((sim vals newW.length gs).foldl stp newW) (lk (fv vals newW.length gs) i) := by
  induction gs with
  | nil =>
    intro oldW newW vals _ _ hinv _ i
    simpa [sim, fv] using hinv i
  | cons g gs ih =>
    intro oldW newW vals hok hlen hinv hb
    have hg := hok g (by simp)
    have hok' : ∀ g ∈ gs, Ok g := fun g' h' => hok g' (by simp [h'])
    have heval : g.op.eval (g.inputs.map fun i => oldW.getD i false) =
        g.op.eval ((g.inputs.map (lk vals)).map (interp newW)) := by
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact hinv i
    by_cases hc : (g.inputs.map (lk vals)).all Sum.isRight = true
    · simp only [sim, fv, hc, if_true, List.foldl_cons]
      have hl' : (stp newW ⟨g.op, (g.inputs.map (lk vals)).map idx⟩).length =
          newW.length + 1 := by simp [stp]
      rw [← hl']
      apply ih
      · exact hok'
      · simp [stp, hlen]
      · apply ext_step oldW newW _ vals _ _ hlen hinv hb
        · intro u hu
          exact interp_app _ _ _ hu
        · simp only [interp, stp]
          rw [List.getD_append_right _ _ _ _ (le_refl _)]
          simp only [Nat.sub_self, List.getD_cons_zero]
          rw [heval]
          congr 1
          rw [List.map_map]
          apply List.map_congr_left
          intro u hu
          have := List.all_eq_true.mp hc u hu
          rcases u with b | k
          · simp at this
          · rfl
      · intro i k h
        rw [hl']
        rcases lk_app_cases vals (Sum.inr newW.length) i with h' | h' <;> rw [h'] at h
        · have := hb _ _ h
          omega
        · cases h
          omega
    · simp only [sim, fv, hc, if_false, List.foldl_cons, Bool.false_eq_true]
      apply ih
      · exact hok'
      · simp [stp, hlen]
      · apply ext_step oldW newW newW vals _ _ hlen hinv hb
        · intro u _
          rfl
        · rw [simV_ok newW g.op _ hg.1 (by simpa using hg.2.1) (by simpa using hg.2.2)
            (by simpa using hc), heval]
      · intro i k h
        rcases lk_app_cases vals (simV g.op (g.inputs.map (lk vals))) i with h' | h' <;>
          rw [h'] at h
        · exact hb _ _ h
        · have hm := simV_mem _ _ _ h
          rw [List.mem_map] at hm
          obtain ⟨j, _, hj⟩ := hm
          exact hb _ _ hj

def trunc (g : Gate) : Gate :=
  { op := g.op, inputs := if g.op.eval [false] = true then List.take 1 g.inputs else g.inputs }

def P (g : Gate) : Bool := [(0 : ℕ), 9].any fun j => g.inputs.contains j

def Good (vals : List (Bool ⊕ ℕ)) : Prop :=
  lk vals 0 = Sum.inl false ∧ lk vals 9 = Sum.inl true ∧ 10 ≤ vals.length

def V0 : List (Bool ⊕ ℕ) := [Sum.inl false, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3,
  Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inr 7, Sum.inl true]

theorem fv_len (gs : List Gate) : ∀ vals m, (fv vals m gs).length = vals.length + gs.length := by
  induction gs with
  | nil => intro vals m; simp [fv]
  | cons g gs ih =>
    intro vals m
    simp only [fv]
    split <;> rw [ih] <;> simp <;> omega

theorem fv_lk (gs : List Gate) : ∀ vals m i, i < vals.length → lk (fv vals m gs) i = lk vals i := by
  induction gs with
  | nil => intro vals m i _; simp [fv]
  | cons g gs ih =>
    intro vals m i h
    simp only [fv]
    split <;> rw [ih _ _ _ (by simp; omega), lk_app_lt _ _ _ h]

theorem good_app (vals : List (Bool ⊕ ℕ)) (v : Bool ⊕ ℕ) (h : Good vals) : Good (vals ++ [v]) := by
  obtain ⟨h0, h9, hl⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [lk_app_lt _ _ _ (by omega), h0]
  · rw [lk_app_lt _ _ _ (by omega), h9]
  · simp; omega

theorem good_fv (vals : List (Bool ⊕ ℕ)) (m : ℕ) (gs : List Gate) (h : Good vals) :
    Good (fv vals m gs) := by
  obtain ⟨h0, h9, hl⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [fv_lk _ _ _ _ (by omega), h0]
  · rw [fv_lk _ _ _ _ (by omega), h9]
  · rw [fv_len]; omega

theorem sim_app (a b : List Gate) : ∀ vals m, ∃ m', (sim vals m (a ++ b)).length =
    (sim vals m a).length + (sim (fv vals m a) m' b).length := by
  induction a with
  | nil => intro vals m; exact ⟨m, by simp [sim, fv]⟩
  | cons g a ih =>
    intro vals m
    by_cases hc : (g.inputs.map (lk vals)).all Sum.isRight = true
    · obtain ⟨m', h⟩ := ih (vals ++ [Sum.inr m]) (m + 1)
      refine ⟨m', ?_⟩
      simp only [List.cons_append, sim, fv, hc, if_true, List.length_cons]
      rw [h]
      omega
    · obtain ⟨m', h⟩ := ih (vals ++ [simV g.op (g.inputs.map (lk vals))]) m
      refine ⟨m', ?_⟩
      simp only [List.cons_append, sim, fv, hc, if_false, Bool.false_eq_true]
      exact h

theorem sim_count (gs : List Gate) : ∀ (vals : List (Bool ⊕ ℕ)) (m : ℕ), Good vals →
    (sim vals m gs).length + (gs.filter P).length ≤ gs.length := by
  induction gs with
  | nil => intros; simp [sim]
  | cons g gs ih =>
    intro vals m hv
    obtain ⟨h0, h9, hl⟩ := hv
    by_cases hx : P g = true
    · have hc : (g.inputs.map (lk vals)).all Sum.isRight = false := by
        have hx' : 0 ∈ g.inputs ∨ 9 ∈ g.inputs := by simpa [P] using hx
        cases hcc : (g.inputs.map (lk vals)).all Sum.isRight
        · rfl
        · rcases hx' with h | h
          · have := List.all_eq_true.mp hcc _ (List.mem_map.mpr ⟨_, h, rfl⟩)
            rw [h0] at this
            simp at this
          · have := List.all_eq_true.mp hcc _ (List.mem_map.mpr ⟨_, h, rfl⟩)
            rw [h9] at this
            simp at this
      have := ih _ m (good_app _ (simV g.op (g.inputs.map (lk vals))) ⟨h0, h9, hl⟩)
      simp only [sim, hc, List.filter_cons, hx, List.length_cons, if_true, Bool.false_eq_true,
        if_false]
      omega
    · have hx2 : P g = false := by simpa using hx
      simp only [List.filter_cons, hx2, Bool.false_eq_true, if_false, List.length_cons]
      by_cases hc : (g.inputs.map (lk vals)).all Sum.isRight = true
      · have := ih _ (m + 1) (good_app _ (Sum.inr m) ⟨h0, h9, hl⟩)
        simp only [sim, hc, if_true, List.length_cons]
        omega
      · have := ih _ m (good_app _ (simV g.op (g.inputs.map (lk vals))) ⟨h0, h9, hl⟩)
        simp only [sim, hc, if_false, Bool.false_eq_true]
        omega

theorem simV_left (op : GateOp) (vs : List (Bool ⊕ ℕ))
    (h : op = GateOp.and ∧ Sum.inl false ∈ vs ∨ op = GateOp.or ∧ Sum.inl true ∈ vs)
    (hl : vs.length ≤ 2) : (simV op vs).isLeft = true := by
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
  rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try simp at hl h ⊢) <;>
  rcases a with (_ | _) | a <;> (try rcases b with (_ | _) | b) <;>
  simp_all [simV, andV, orV]

theorem case2 (vals : List (Bool ⊕ ℕ)) (m : ℕ) (hv : Good vals) (hlv : vals.length = 10)
    (x5 y1 y2 : List Gate) (x6 x8 : Gate) (hok6 : Ok x6)
    (hop6 : x6.op = GateOp.and ∧ 0 ∈ x6.inputs ∨ x6.op = GateOp.or ∧ 9 ∈ x6.inputs)
    (hP8 : P x8 = false) (hin : 10 + x5.length ∈ x8.inputs) :
    (sim vals m (x5 ++ x6 :: (y1 ++ x8 :: y2))).length + 1 +
      ((x5 ++ x6 :: (y1 ++ x8 :: y2)).filter P).length ≤
      (x5 ++ x6 :: (y1 ++ x8 :: y2)).length := by
  obtain ⟨m1, hA⟩ := sim_app x5 (x6 :: (y1 ++ x8 :: y2)) vals m
  have hg1 : Good (fv vals m x5) := good_fv _ _ _ hv
  have hl1 : (fv vals m x5).length = 10 + x5.length := by rw [fv_len, hlv]
  have hmem : Sum.inl false ∈ x6.inputs.map (lk (fv vals m x5)) ∨
      Sum.inl true ∈ x6.inputs.map (lk (fv vals m x5)) := by
    rcases hop6 with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl (List.mem_map.mpr ⟨_, h, hg1.1⟩)
    · exact Or.inr (List.mem_map.mpr ⟨_, h, hg1.2.1⟩)
  have hc6 : (x6.inputs.map (lk (fv vals m x5))).all Sum.isRight = false := by
    cases hcc : (x6.inputs.map (lk (fv vals m x5))).all Sum.isRight
    · rfl
    · rcases hmem with h | h
      · have := List.all_eq_true.mp hcc _ h
        simp at this
      · have := List.all_eq_true.mp hcc _ h
        simp at this
  have hleft : (simV x6.op (x6.inputs.map (lk (fv vals m x5)))).isLeft = true := by
    have hl : (x6.inputs.map (lk (fv vals m x5))).length ≤ 2 := by simpa using hok6.2.1
    rcases hop6 with ⟨h, h0⟩ | ⟨h, h9⟩
    · exact simV_left _ _ (Or.inl ⟨h, List.mem_map.mpr ⟨_, h0, hg1.1⟩⟩) hl
    · exact simV_left _ _ (Or.inr ⟨h, List.mem_map.mpr ⟨_, h9, hg1.2.1⟩⟩) hl
  have hs6 : sim (fv vals m x5) m1 (x6 :: (y1 ++ x8 :: y2)) =
      sim (fv vals m x5 ++ [simV x6.op (x6.inputs.map (lk (fv vals m x5)))]) m1
        (y1 ++ x8 :: y2) := by
    simp only [sim, hc6, Bool.false_eq_true, if_false]
  obtain ⟨m2, hB⟩ := sim_app y1 (x8 :: y2)
    (fv vals m x5 ++ [simV x6.op (x6.inputs.map (lk (fv vals m x5)))]) m1
  have hc3 : lk (fv (fv vals m x5 ++ [simV x6.op (x6.inputs.map (lk (fv vals m x5)))]) m1 y1)
      (10 + x5.length) = simV x6.op (x6.inputs.map (lk (fv vals m x5))) := by
    rw [fv_lk _ _ _ _ (by simp; omega)]
    unfold lk
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hl1]
  have hc8 : (x8.inputs.map (lk (fv (fv vals m x5 ++
      [simV x6.op (x6.inputs.map (lk (fv vals m x5)))]) m1 y1))).all Sum.isRight = false := by
    cases hcc : (x8.inputs.map (lk (fv (fv vals m x5 ++
      [simV x6.op (x6.inputs.map (lk (fv vals m x5)))]) m1 y1))).all Sum.isRight
    · rfl
    · have := List.all_eq_true.mp hcc _ (List.mem_map.mpr ⟨_, hin, rfl⟩)
      rw [hc3] at this
      revert hleft this
      cases simV x6.op (x6.inputs.map (lk (fv vals m x5))) <;> simp
  have hs8 := fun (V : List (Bool ⊕ ℕ)) (hV : (x8.inputs.map (lk V)).all Sum.isRight = false) =>
    (show sim V m2 (x8 :: y2) = sim (V ++ [simV x8.op (x8.inputs.map (lk V))]) m2 y2 by
      simp only [sim, hV, Bool.false_eq_true, if_false])
  have hg3 := good_fv _ m1 y1 (good_app _ (simV x6.op (x6.inputs.map (lk (fv vals m x5)))) hg1)
  have k5 := sim_count x5 vals m hv
  have k1 := sim_count y1 _ m1 (good_app _ (simV x6.op (x6.inputs.map (lk (fv vals m x5)))) hg1)
  have k2 := sim_count y2 _ m2 (good_app _ (simV x8.op (x8.inputs.map (lk (fv (fv vals m x5 ++
      [simV x6.op (x6.inputs.map (lk (fv vals m x5)))]) m1 y1)))) hg3)
  have hP6 : P x6 = true := by
    rcases hop6 with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [P, h]
  rw [hA, hs6, hB, hs8 _ hc8]
  simp only [List.filter_append, List.filter_cons, hP6, hP8, List.length_append,
    List.length_cons, if_true, Bool.false_eq_true, if_false]
  omega

theorem sim_gates (gs : List Gate) : ∀ vals m, ∀ g' ∈ sim vals m gs,
    ∃ g ∈ gs, g'.op = g.op ∧ g'.inputs.length = g.inputs.length := by
  induction gs with
  | nil => intro vals m g' h; simp [sim] at h
  | cons g gs ih =>
    intro vals m g' h
    simp only [sim] at h
    split at h
    · rcases List.mem_cons.mp h with rfl | h
      · exact ⟨g, by simp, rfl, by simp⟩
      · obtain ⟨g'', h1, h2⟩ := ih _ _ g' h
        exact ⟨g'', by simp [h1], h2⟩
    · obtain ⟨g'', h1, h2⟩ := ih _ _ g' h
      exact ⟨g'', by simp [h1], h2⟩

theorem ok_trunc (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    Ok (trunc g) := by
  obtain ⟨hop, hl⟩ := h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h <;> simp [Ok, trunc, h, GateOp.eval] <;> omega

theorem stp_trunc (W : List Bool) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    stp W (trunc g) = stp W g := by
  rcases g with ⟨op, l⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h <;> subst h <;> simp [stp, trunc, GateOp.eval] <;> cases l <;> simp

theorem foldl_trunc (gs : List Gate)
    (h : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    ∀ W, (gs.map trunc).foldl stp W = gs.foldl stp W := by
  induction gs with
  | nil => intro W; rfl
  | cons g gs ih =>
    intro W
    simp only [List.map_cons, List.foldl_cons]
    rw [stp_trunc W g (h g (by simp))]
    exact ih (fun g' hg' => h g' (by simp [hg'])) _

theorem foldl_prefix (gs : List Gate) : ∀ W i, i < W.length →
    (gs.foldl stp W).getD i false = W.getD i false := by
  induction gs with
  | nil => intro W i _; rfl
  | cons g gs ih =>
    intro W i h
    simp only [List.foldl_cons]
    rw [ih _ _ (by simp [stp]; omega)]
    exact List.getD_append _ _ _ _ h

theorem inv_V0 (x : Fin 8 → Bool) : ∀ i,
    (List.ofFn (Fin.cons false x : Fin 9 → Bool) ++ [true]).getD i false =
      interp (List.ofFn x) (lk V0 i) := by
  intro i
  simp only [List.ofFn_succ, List.ofFn_zero, Fin.cons_zero, Fin.cons_succ]
  rcases Nat.lt_or_ge i 10 with h | h
  · interval_cases i <;> simp [lk, V0, interp]
  · rw [List.getD_eq_default (hn := by simp; omega)]
    unfold lk
    rw [List.getD_eq_default (hn := by simp [V0]; omega)]
    rfl

theorem bound_V0 (x : Fin 8 → Bool) : ∀ i k, lk V0 i = Sum.inr k → k < (List.ofFn x).length := by
  intro i k h
  rw [List.length_ofFn]
  rcases Nat.lt_or_ge i 10 with hi | hi
  · interval_cases i <;> simp [lk, V0] at h <;> omega
  · unfold lk at h
    rw [List.getD_eq_default (hn := by simp [V0]; omega)] at h
    cases h

theorem good_V0 : Good V0 := ⟨rfl, rfl, by simp [V0]⟩

theorem main (x1 : Circuit) (hfan : FanInTwo x1)
    (h9 : ∀ y : Fin 9 → Bool, (x1.wires (List.ofFn y)).getD 9 false = !y 0)
    (hnc : ∃ a c : Fin 8 → Bool,
      circuitFun 9 x1 (Fin.cons false a) ≠ circuitFun 9 x1 (Fin.cons false c))
    (hcnt : (sim V0 8 ((x1.gates.drop 1).map trunc)).length ≤ 11) :
    HasCircuitSize 8 (fun x : Fin 8 → Bool => circuitFun 9 x1 (Fin.cons false x)) 11 := by
  rcases hg : x1.gates with _ | ⟨g0, rest⟩
  · exfalso
    have := h9 (fun _ => false)
    rw [Circuit.wires, hg, List.foldl_nil, List.getD_eq_default (hn := by simp)] at this
    simp at this
  rw [hg, List.drop_one, List.tail_cons] at hcnt
  have hrest : ∀ g ∈ rest, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2 := fun g h => hfan g (by rw [hg]; simp [h])
  have hok : ∀ g ∈ rest.map trunc, Ok g := by
    intro g h
    rw [List.mem_map] at h
    obtain ⟨g', h', rfl⟩ := h
    exact ok_trunc g' (hrest g' h')
  have hw : ∀ y, x1.wires y = rest.foldl stp (stp y g0) := by
    intro y
    rw [Circuit.wires, hg]
    rfl
  have hP : ∀ x : Fin 8 → Bool, circuitFun 9 x1 (Fin.cons false x) =
      interp ((sim V0 8 (rest.map trunc)).foldl stp (List.ofFn x))
        (lk (fv V0 8 (rest.map trunc)) x1.output) := by
    intro x
    have hW0 : stp (List.ofFn (Fin.cons false x : Fin 9 → Bool)) g0 =
        List.ofFn (Fin.cons false x : Fin 9 → Bool) ++ [true] := by
      have := h9 (Fin.cons false x)
      rw [hw, foldl_prefix _ _ _ (by simp [stp])] at this
      simp only [stp] at this ⊢
      rw [List.getD_append_right _ _ _ _ (by simp)] at this
      simp only [List.length_ofFn, Nat.sub_self, List.getD_cons_zero, Fin.cons_zero,
        Bool.not_false] at this
      rw [this]
    have key := sim_correct (rest.map trunc) (stp (List.ofFn (Fin.cons false x : Fin 9 → Bool)) g0)
      (List.ofFn x) V0 hok (by rw [hW0]; simp [V0]) (by rw [hW0]; exact inv_V0 x) (bound_V0 x)
      x1.output
    rw [List.length_ofFn, foldl_trunc rest (fun g h => (hrest g h).1)] at key
    unfold circuitFun Circuit.eval
    rw [hw]
    exact key
  rcases hout : lk (fv V0 8 (rest.map trunc)) x1.output with b | k
  · exfalso
    obtain ⟨a, c, hne⟩ := hnc
    rw [hP a, hP c, hout] at hne
    exact hne rfl
  · refine ⟨⟨sim V0 8 (rest.map trunc), k⟩, ?_, hcnt, ?_⟩
    · intro g hgm
      obtain ⟨g', hg', hop, hlen⟩ := sim_gates _ _ _ g hgm
      have h' := hok g' hg'
      refine ⟨?_, by rw [hlen]; exact h'.2.1⟩
      rw [hop]
      rcases h'.1 with h | h | h <;> simp [h]
    · intro x
      change _ = circuitFun 9 x1 (Fin.cons false x)
      rw [hP x, hout]
      rfl

theorem count_main (x1 : Circuit) (hfan : FanInTwo x1) (hsize : x1.size ≤ 15)
    (hcase : 3 ≤ (((x1.gates.drop 1).map trunc).filter P).length ∨
      2 ≤ (((x1.gates.drop 1).map trunc).filter P).length ∧
      ∃ (x5 : List Gate) (x6 : Gate) (x7 : List Gate),
        (x1.gates.drop 1).map trunc = x5 ++ x6 :: x7 ∧
        (x6.op = GateOp.and ∧ 0 ∈ x6.inputs ∨ x6.op = GateOp.or ∧ 9 ∈ x6.inputs) ∧
        ∃ x8 ∈ x7, P x8 = false ∧ 10 + x5.length ∈ x8.inputs) :
    (sim V0 8 ((x1.gates.drop 1).map trunc)).length ≤ 11 := by
  have hl : ((x1.gates.drop 1).map trunc).length ≤ 14 := by
    simp [Circuit.size] at hsize ⊢
    omega
  have hok : ∀ g ∈ (x1.gates.drop 1).map trunc, Ok g := by
    intro g h
    rw [List.mem_map] at h
    obtain ⟨g', h', rfl⟩ := h
    exact ok_trunc g' (hfan g' (List.mem_of_mem_drop h'))
  generalize (x1.gates.drop 1).map trunc = gs at hl hok hcase ⊢
  rcases hcase with h3 | ⟨h2, x5, x6, x7, heq, hop6, x8, hx8, hP8, hin⟩
  · have := sim_count gs V0 8 good_V0
    omega
  · obtain ⟨y1, y2, rfl⟩ := List.append_of_mem hx8
    subst heq
    have := case2 V0 8 good_V0 rfl x5 y1 y2 x6 x8 (hok x6 (by simp)) hop6 hP8 hin
    omega

end PEqualNP.Outside.L_meta_2305

theorem PEqualNP.Outside.L_meta_2305 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : List PEqualNP.CircuitLowerBounds.Gate := List.map (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => { op := x2.op, inputs := if x2.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x2.inputs else x2.inputs : PEqualNP.CircuitLowerBounds.Gate }) (List.drop (1 : ℕ) x1.gates);   have x3 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x4 : ℕ) => x3.inputs.contains x4;   have x4 : ℕ := (List.filter x3 x2).length;   have x5 : Prop := ∃ (x5 : List PEqualNP.CircuitLowerBounds.Gate) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 : List PEqualNP.CircuitLowerBounds.Gate), x2 = x5 ++ x6 :: x7 ∧ (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (0 : ℕ) ∈ x6.inputs ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (9 : ℕ) ∈ x6.inputs) ∧ ∃ x8 ∈ x7, x3 x8 = Bool.false ∧ (10 : ℕ) + x5.length ∈ x8.inputs;   PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x7 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x7)).getD (9 : ℕ) Bool.false = !x7 (0 : Fin (9 : ℕ))) → x1.size ≤ (15 : ℕ) → (3 : ℕ) ≤ x4 ∨ (2 : ℕ) ≤ x4 ∧ x5 → (∃ (x10 : Fin (8 : ℕ) → Bool) (x11 : Fin (8 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 (Fin.cons Bool.false x10) ≠ PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 (Fin.cons Bool.false x11)) → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x11 : Fin (8 : ℕ) → Bool) => PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 (Fin.cons Bool.false x11)) (11 : ℕ) := by
  intro x1 x2 x3 x4 x5 hfan h9 hsize hcase hnc
  exact PEqualNP.Outside.L_meta_2305.main x1 hfan h9 hnc
    (PEqualNP.Outside.L_meta_2305.count_main x1 hfan hsize hcase)
