import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2305_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

private lemma run_nil (w : List Bool) : run [] w = w := rfl

private lemma run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma run_append (gs1 gs2 : List Gate) (w : List Bool) :
    run (gs1 ++ gs2) w = run gs2 (run gs1 w) := by
  simp [run, List.foldl_append]

private lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

private lemma run_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

private def normGate (g : Gate) : Gate :=
  ⟨g.op, if g.op.eval [false] = true then g.inputs.take 1 else g.inputs⟩

private def GoodGate (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
  g.inputs.length ≤ 2 ∧
  (g.op = GateOp.not → g.inputs.length ≤ 1)

private lemma goodGate_of_norm (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) : GoodGate (normGate g) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · refine ⟨Or.inl h, ?_, fun hc => by simp [normGate, h] at hc⟩
    simp [normGate, h, GateOp.eval, hlen]
  · refine ⟨Or.inr (Or.inl h), ?_, fun hc => by simp [normGate, h] at hc⟩
    simp [normGate, h, GateOp.eval, hlen]
  · refine ⟨Or.inr (Or.inr h), ?_, fun _ => by simp [normGate, h, GateOp.eval]⟩
    have : (g.inputs.take 1).length ≤ 1 := by simp
    simp only [normGate, h, GateOp.eval, List.headD_cons, Bool.not_false, ↓reduceIte]
    omega

private lemma normGate_eval (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (w : List Bool) :
    (normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · simp [normGate, h, GateOp.eval]
  · simp [normGate, h, GateOp.eval]
  · simp only [normGate, h, GateOp.eval, List.headD_cons, Bool.not_false, ↓reduceIte]
    cases g.inputs with
    | nil => rfl
    | cons a _ => rfl

private lemma run_map_normGate (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (w : List Bool) :
    run (gs.map normGate) w = run gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, run_cons]
    rw [normGate_eval g (hgs g List.mem_cons_self) w]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _

private inductive Ref where
  | const (b : Bool)
  | wire (u : ℕ)
  deriving DecidableEq

private def Ref.eval (dw : List Bool) : Ref → Bool
  | .const b => b
  | .wire u => dw.getD u false

private def Ref.ok (bound : ℕ) : Ref → Prop
  | .const _ => True
  | .wire u => u < bound

private structure St where
  env : List Ref
  gs : List Gate

private def initSt : St :=
  ⟨[.const false, .wire 0, .wire 1, .wire 2, .wire 3, .wire 4, .wire 5, .wire 6, .wire 7,
    .const true], []⟩

private def stepAnd2 (nextW : ℕ) (r1 r2 : Ref) : Ref × List Gate :=
  match r1, r2 with
  | .const false, _ => (.const false, [])
  | .const true, r2 => (r2, [])
  | .wire _, .const false => (.const false, [])
  | .wire u, .const true => (.wire u, [])
  | .wire u, .wire v => (.wire nextW, [⟨.and, [u, v]⟩])

private def stepOr2 (nextW : ℕ) (r1 r2 : Ref) : Ref × List Gate :=
  match r1, r2 with
  | .const true, _ => (.const true, [])
  | .const false, r2 => (r2, [])
  | .wire _, .const true => (.const true, [])
  | .wire u, .const false => (.wire u, [])
  | .wire u, .wire v => (.wire nextW, [⟨.or, [u, v]⟩])

private def stepNot1 (nextW : ℕ) (r1 : Ref) : Ref × List Gate :=
  match r1 with
  | .const b => (.const (!b), [])
  | .wire u => (.wire nextW, [⟨.not, [u]⟩])

private def stepOut (st : St) (g : Gate) : Ref × List Gate :=
  match g.op with
  | .and =>
    match g.inputs with
    | [] => (.const true, [])
    | [a] => (st.env.getD a (.const false), [])
    | [a, b] => stepAnd2 (8 + st.gs.length) (st.env.getD a (.const false)) (st.env.getD b (.const false))
    | _ => (.const false, [])
  | .or =>
    match g.inputs with
    | [] => (.const false, [])
    | [a] => (st.env.getD a (.const false), [])
    | [a, b] => stepOr2 (8 + st.gs.length) (st.env.getD a (.const false)) (st.env.getD b (.const false))
    | _ => (.const false, [])
  | .not =>
    match g.inputs with
    | [] => (.const true, [])
    | a :: _ => stepNot1 (8 + st.gs.length) (st.env.getD a (.const false))
  | _ => (.const false, [])

private def step (st : St) (g : Gate) : St :=
  let p := stepOut st g
  ⟨st.env ++ [p.1], st.gs ++ p.2⟩

private def runPass (gs : List Gate) (st : St) : St :=
  gs.foldl step st

private lemma runPass_nil (st : St) : runPass [] st = st := rfl

private lemma runPass_cons (g : Gate) (gs : List Gate) (st : St) :
    runPass (g :: gs) st = runPass gs (step st g) := rfl

private lemma runPass_append (gs1 gs2 : List Gate) (st : St) :
    runPass (gs1 ++ gs2) st = runPass gs2 (runPass gs1 st) := by
  simp [runPass, List.foldl_append]

private lemma step_env_length (st : St) (g : Gate) :
    (step st g).env.length = st.env.length + 1 := by
  simp [step]

private lemma step_env_getD_lt (st : St) (g : Gate) (i : ℕ) (hi : i < st.env.length) :
    (step st g).env.getD i (.const false) = st.env.getD i (.const false) := by
  simp only [step]
  exact List.getD_append _ _ _ _ hi

private lemma runPass_env_length (gs : List Gate) (st : St) :
    (runPass gs st).env.length = st.env.length + gs.length := by
  induction gs generalizing st with
  | nil => simp [runPass]
  | cons g gs ih =>
    rw [runPass_cons, ih, step_env_length]; simp; omega

private lemma runPass_env_getD_lt (gs : List Gate) (st : St) (i : ℕ) (hi : i < st.env.length) :
    (runPass gs st).env.getD i (.const false) = st.env.getD i (.const false) := by
  induction gs generalizing st with
  | nil => rfl
  | cons g gs ih =>
    rw [runPass_cons, ih _ (by rw [step_env_length]; omega), step_env_getD_lt st g i hi]

private lemma stepAnd2_len (nextW : ℕ) (r1 r2 : Ref) : (stepAnd2 nextW r1 r2).2.length ≤ 1 := by
  cases r1 with
  | const b1 => cases b1 <;> simp [stepAnd2]
  | wire u => cases r2 with
    | const b2 => cases b2 <;> simp [stepAnd2]
    | wire v => simp [stepAnd2]

private lemma stepOr2_len (nextW : ℕ) (r1 r2 : Ref) : (stepOr2 nextW r1 r2).2.length ≤ 1 := by
  cases r1 with
  | const b1 => cases b1 <;> simp [stepOr2]
  | wire u => cases r2 with
    | const b2 => cases b2 <;> simp [stepOr2]
    | wire v => simp [stepOr2]

private lemma stepNot1_len (nextW : ℕ) (r1 : Ref) : (stepNot1 nextW r1).2.length ≤ 1 := by
  cases r1 <;> simp [stepNot1]

private lemma step_gs_le (st : St) (g : Gate) :
    (step st g).gs.length ≤ st.gs.length + 1 := by
  have h2 : (stepOut st g).2.length ≤ 1 := by
    unfold stepOut
    cases g.op <;> simp only []
    · cases g.inputs with
      | nil => simp
      | cons a rest =>
        cases rest with
        | nil => simp
        | cons b rest2 =>
          cases rest2 with
          | nil => exact stepAnd2_len _ _ _
          | cons _ _ => simp
    · cases g.inputs with
      | nil => simp
      | cons a rest =>
        cases rest with
        | nil => simp
        | cons b rest2 =>
          cases rest2 with
          | nil => exact stepOr2_len _ _ _
          | cons _ _ => simp
    · cases g.inputs with
      | nil => simp
      | cons a _ => exact stepNot1_len _ _
    · simp
    · simp
  simp only [step, List.length_append]
  omega

private lemma step_no_emit_of_const (st : St) (g : Gate) (hg : GoodGate g)
    (hconst : ∃ i ∈ g.inputs, ∃ b : Bool, st.env.getD i (.const false) = .const b) :
    (step st g).gs.length = st.gs.length := by
  obtain ⟨hop, hlen, hnot⟩ := hg
  obtain ⟨i, hi, b, hbi⟩ := hconst
  have h0 : (stepOut st g).2.length = 0 := by
    rcases hop with h | h | h
    · cases hin : g.inputs with
      | nil => simp [hin] at hi
      | cons a rest =>
        cases rest with
        | nil => simp only [stepOut, h, hin, List.length_nil]
        | cons c rest2 =>
          cases rest2 with
          | nil =>
            simp only [hin, List.mem_cons, List.not_mem_nil, or_false] at hi
            simp only [stepOut, h, hin]
            rcases hi with rfl | rfl
            · rw [hbi]; cases b <;> simp [stepAnd2]
            · rw [hbi]; cases st.env.getD a (.const false) with
              | const b1 => cases b1 <;> simp [stepAnd2]
              | wire u => cases b <;> simp [stepAnd2]
          | cons _ _ => simp [hin] at hlen
    · cases hin : g.inputs with
      | nil => simp [hin] at hi
      | cons a rest =>
        cases rest with
        | nil => simp only [stepOut, h, hin, List.length_nil]
        | cons c rest2 =>
          cases rest2 with
          | nil =>
            simp only [hin, List.mem_cons, List.not_mem_nil, or_false] at hi
            simp only [stepOut, h, hin]
            rcases hi with rfl | rfl
            · rw [hbi]; cases b <;> simp [stepOr2]
            · rw [hbi]; cases st.env.getD a (.const false) with
              | const b1 => cases b1 <;> simp [stepOr2]
              | wire u => cases b <;> simp [stepOr2]
          | cons _ _ => simp [hin] at hlen
    · have h1 := hnot h
      cases hin : g.inputs with
      | nil => simp [hin] at hi
      | cons a rest =>
        cases rest with
        | nil =>
          simp only [hin, List.mem_cons, List.not_mem_nil, or_false] at hi
          subst hi
          simp only [stepOut, h, hin, hbi, stepNot1, List.length_nil]
        | cons _ _ => simp [hin] at h1
  simp only [step, List.length_append, h0, add_zero]

private lemma step_const_of_kill (st : St) (g : Gate) (hg : GoodGate g)
    (h0 : st.env.getD 0 (.const false) = .const false)
    (h9 : st.env.getD 9 (.const false) = .const true)
    (hkill : (g.op = GateOp.and ∧ 0 ∈ g.inputs) ∨ (g.op = GateOp.or ∧ 9 ∈ g.inputs)) :
    ∃ b : Bool, (step st g).env.getD st.env.length (.const false) = .const b := by
  obtain ⟨_, hlen, _⟩ := hg
  have hres : (step st g).env.getD st.env.length (.const false) = (stepOut st g).1 := by
    simp [step]
  rw [hres]
  rcases hkill with ⟨hop, hmem⟩ | ⟨hop, hmem⟩
  · refine ⟨false, ?_⟩
    cases hin : g.inputs with
    | nil => simp [hin] at hmem
    | cons a rest =>
      cases rest with
      | nil =>
        simp only [hin, List.mem_cons, List.not_mem_nil, or_false] at hmem
        subst hmem; simp only [stepOut, hop, hin, h0]
      | cons c rest2 =>
        cases rest2 with
        | nil =>
          simp only [hin, List.mem_cons, List.not_mem_nil, or_false] at hmem
          simp only [stepOut, hop, hin]
          rcases hmem with rfl | rfl
          · rw [h0]; rfl
          · rw [h0]; cases st.env.getD a (.const false) with
            | const b1 => cases b1 <;> rfl
            | wire u => rfl
        | cons _ _ => simp [hin] at hlen
  · refine ⟨true, ?_⟩
    cases hin : g.inputs with
    | nil => simp [hin] at hmem
    | cons a rest =>
      cases rest with
      | nil =>
        simp only [hin, List.mem_cons, List.not_mem_nil, or_false] at hmem
        subst hmem; simp only [stepOut, hop, hin, h9]
      | cons c rest2 =>
        cases rest2 with
        | nil =>
          simp only [hin, List.mem_cons, List.not_mem_nil, or_false] at hmem
          simp only [stepOut, hop, hin]
          rcases hmem with rfl | rfl
          · rw [h9]; rfl
          · rw [h9]; cases st.env.getD a (.const false) with
            | const b1 => cases b1 <;> rfl
            | wire u => rfl
        | cons _ _ => simp [hin] at hlen

private def StValid (st : St) (w_of : (Fin 8 → Bool) → List Bool) : Prop :=
  FanInTwo ⟨st.gs, 0⟩ ∧
  (∀ i, Ref.ok (8 + st.gs.length) (st.env.getD i (.const false))) ∧
  ∀ y : Fin 8 → Bool,
    (w_of y).length = st.env.length ∧
    ∀ i < st.env.length,
      (st.env.getD i (.const false)).eval (run st.gs (List.ofFn y)) = (w_of y).getD i false

private lemma ref_ok_mono {m1 m2 : ℕ} (h : m1 ≤ m2) {r : Ref} (hr : Ref.ok m1 r) :
    Ref.ok m2 r := by
  cases r with
  | const _ => trivial
  | wire u => exact Nat.lt_of_lt_of_le hr h

private lemma ref_eval_append (gs1 gs2 : List Gate) (y : Fin 8 → Bool) (r : Ref)
    (hr : Ref.ok (8 + gs1.length) r) :
    r.eval (run (gs1 ++ gs2) (List.ofFn y)) = r.eval (run gs1 (List.ofFn y)) := by
  cases r with
  | const _ => rfl
  | wire u =>
    simp only [Ref.eval, run_append]
    have hlt : u < (run gs1 (List.ofFn y)).length := by
      rw [run_length]; simp; exact hr
    exact run_getD_lt gs2 _ u hlt

private lemma lk_eval (st : St) (w_of : (Fin 8 → Bool) → List Bool) (hv : StValid st w_of)
    (y : Fin 8 → Bool) (i : ℕ) :
    (st.env.getD i (.const false)).eval (run st.gs (List.ofFn y)) = (w_of y).getD i false := by
  obtain ⟨_, _, hev⟩ := hv
  obtain ⟨hlen, hget⟩ := hev y
  by_cases hi : i < st.env.length
  · exact hget i hi
  · have h1 : st.env.getD i (.const false) = .const false :=
      List.getD_eq_default _ _ (Nat.not_lt.mp hi)
    have h2 : (w_of y).getD i false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [h1, h2]; rfl

private lemma step_valid (st : St) (w_of : (Fin 8 → Bool) → List Bool)
    (hv : StValid st w_of) (g : Gate) (hg : GoodGate g) :
    StValid (step st g) (fun y => run [g] (w_of y)) := by
  obtain ⟨hFan, hOk, hEv⟩ := hv
  obtain ⟨hop, hlen, hnot⟩ := hg
  have hlk := fun y i => lk_eval st w_of ⟨hFan, hOk, hEv⟩ y i
  have no_emit (r : Ref) (hr_ok : Ref.ok (8 + st.gs.length) r)
      (hstep_eq : stepOut st g = (r, []))
      (hr_ev : ∀ y, r.eval (run st.gs (List.ofFn y)) =
        g.op.eval (g.inputs.map fun i => (w_of y).getD i false)) :
      StValid (step st g) (fun y => run [g] (w_of y)) := by
    simp only [step, hstep_eq, List.append_nil]
    refine ⟨hFan, ?_, ?_⟩
    · intro i
      by_cases hi : i < st.env.length
      · rw [List.getD_append _ _ _ _ hi]; exact hOk i
      · by_cases hi2 : i = st.env.length
        · subst hi2; simp [hr_ok]
        · rw [List.getD_eq_default _ _ (by simp; omega)]; trivial
    · intro y
      obtain ⟨hwlen, hwget⟩ := hEv y
      refine ⟨by simp [run, hwlen], ?_⟩
      intro i hi
      simp only [List.length_append, List.length_singleton] at hi
      by_cases hilt : i < st.env.length
      · rw [List.getD_append _ _ _ _ hilt, hwget i hilt]
        exact (List.getD_append _ _ _ _ (by omega)).symm
      · have hieq : i = st.env.length := by omega
        subst hieq
        simp only [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
        rw [hr_ev y, run_cons, run_nil, List.getD_append_right _ _ _ _ (by omega)]
        simp [hwlen]
  have one_emit (g' : Gate)
      (hg'_fan : g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2)
      (hstep_eq : stepOut st g = (.wire (8 + st.gs.length), [g']))
      (hg'_ev : ∀ y, g'.op.eval (g'.inputs.map fun j => (run st.gs (List.ofFn y)).getD j false) =
        g.op.eval (g.inputs.map fun i => (w_of y).getD i false)) :
      StValid (step st g) (fun y => run [g] (w_of y)) := by
    simp only [step, hstep_eq]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hFan x hx
      · exact hg'_fan
    · intro i
      by_cases hi : i < st.env.length
      · rw [List.getD_append _ _ _ _ hi]
        exact ref_ok_mono (by simp) (hOk i)
      · by_cases hi2 : i = st.env.length
        · subst hi2; simp [Ref.ok]
        · rw [List.getD_eq_default _ _ (by simp; omega)]; trivial
    · intro y
      obtain ⟨hwlen, hwget⟩ := hEv y
      refine ⟨by simp [run, hwlen], ?_⟩
      intro i hi
      simp only [List.length_append, List.length_singleton] at hi
      by_cases hilt : i < st.env.length
      · rw [List.getD_append _ _ _ _ hilt, ref_eval_append st.gs [g'] y _ (hOk i), hwget i hilt]
        exact (List.getD_append _ _ _ _ (by omega)).symm
      · have hieq : i = st.env.length := by omega
        subst hieq
        simp only [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero,
          Ref.eval]
        rw [run_append, run_cons, run_nil, List.getD_append_right _ _ _ _ (by rw [run_length]; simp)]
        have hrl : (run st.gs (List.ofFn y)).length = 8 + st.gs.length := by
          rw [run_length]; simp
        simp only [hrl, Nat.sub_self, List.getD_cons_zero]
        rw [hg'_ev y, run_cons, run_nil, List.getD_append_right _ _ _ _ (by omega)]
        simp [hwlen]
  rcases hop with hop | hop | hop
  · -- AND
    cases hin : g.inputs with
    | nil =>
      exact no_emit (.const true) trivial (by simp only [stepOut, hop, hin])
        (fun y => by simp only [hop, hin, GateOp.eval, List.map_nil, List.all_nil, Ref.eval])
    | cons a rest =>
      cases rest with
      | nil =>
        exact no_emit (st.env.getD a (.const false)) (hOk a) (by simp only [stepOut, hop, hin])
          (fun y => by simp only [hop, hin, GateOp.eval, List.map_cons, List.map_nil,
            List.all_cons, List.all_nil, id_eq, Bool.and_true, hlk y a])
      | cons c rest2 =>
        cases rest2 with
        | nil =>
          cases ha : st.env.getD a (.const false) with
          | const b1 =>
            cases b1 with
            | false =>
              exact no_emit (.const false) trivial (by simp only [stepOut, hop, hin, ha, stepAnd2])
                (fun y => by
                  have h1 := hlk y a; rw [ha] at h1
                  simp only [hop, hin, GateOp.eval, List.map_cons, List.map_nil,
                    List.all_cons, List.all_nil, id_eq, Bool.and_true, ← h1, Ref.eval, Bool.false_and])
            | true =>
              exact no_emit (st.env.getD c (.const false)) (hOk c)
                (by simp only [stepOut, hop, hin, ha, stepAnd2])
                (fun y => by
                  have h1 := hlk y a; rw [ha] at h1
                  have h2 := hlk y c
                  simp only [hop, hin, GateOp.eval, List.map_cons, List.map_nil,
                    List.all_cons, List.all_nil, id_eq, Bool.and_true, ← h1, ← h2, Ref.eval, Bool.true_and])
          | wire u =>
            cases hc : st.env.getD c (.const false) with
            | const b2 =>
              cases b2 with
              | false =>
                exact no_emit (.const false) trivial (by simp only [stepOut, hop, hin, ha, hc, stepAnd2])
                  (fun y => by
                    have h2 := hlk y c; rw [hc] at h2
                    simp only [hop, hin, GateOp.eval, List.map_cons, List.map_nil,
                      List.all_cons, List.all_nil, id_eq, Bool.and_true, ← h2, Ref.eval, Bool.and_false])
              | true =>
                exact no_emit (.wire u) (ha ▸ hOk a)
                  (by simp only [stepOut, hop, hin, ha, hc, stepAnd2])
                  (fun y => by
                    have h1 := hlk y a; rw [ha] at h1
                    have h2 := hlk y c; rw [hc] at h2
                    simp only [hop, hin, GateOp.eval, List.map_cons, List.map_nil,
                      List.all_cons, List.all_nil, id_eq, Bool.and_true, ← h1, ← h2, Ref.eval])
            | wire v =>
              exact one_emit ⟨.and, [u, v]⟩ (by simp) (by simp only [stepOut, hop, hin, ha, hc, stepAnd2])
                (fun y => by
                  have h1 := hlk y a; rw [ha] at h1
                  have h2 := hlk y c; rw [hc] at h2
                  simp only [hop, hin, GateOp.eval, List.map_cons, List.map_nil,
                    List.all_cons, List.all_nil, id_eq, Bool.and_true, ← h1, ← h2, Ref.eval])
        | cons _ _ => simp [hin] at hlen
  · -- OR
    cases hin : g.inputs with
    | nil =>
      exact no_emit (.const false) trivial (by simp only [stepOut, hop, hin])
        (fun y => by simp only [hop, hin, GateOp.eval, List.map_nil, List.any_nil, Ref.eval])
    | cons a rest =>
      cases rest with
      | nil =>
        exact no_emit (st.env.getD a (.const false)) (hOk a) (by simp only [stepOut, hop, hin])
          (fun y => by simp only [hop, hin, GateOp.eval, List.map_cons, List.map_nil,
            List.any_cons, List.any_nil, id_eq, Bool.or_false, hlk y a])
      | cons c rest2 =>
        cases rest2 with
        | nil =>
          cases ha : st.env.getD a (.const false) with
          | const b1 =>
            cases b1 with
            | true =>
              exact no_emit (.const true) trivial (by simp only [stepOut, hop, hin, ha, stepOr2])
                (fun y => by
                  have h1 := hlk y a; rw [ha] at h1
                  simp only [hop, hin, GateOp.eval, List.map_cons, List.map_nil,
                    List.any_cons, List.any_nil, id_eq, Bool.or_false, ← h1, Ref.eval, Bool.true_or])
            | false =>
              exact no_emit (st.env.getD c (.const false)) (hOk c)
                (by simp only [stepOut, hop, hin, ha, stepOr2])
                (fun y => by
                  have h1 := hlk y a; rw [ha] at h1
                  have h2 := hlk y c
                  simp only [hop, hin, GateOp.eval, List.map_cons, List.map_nil,
                    List.any_cons, List.any_nil, id_eq, Bool.or_false, ← h1, ← h2, Ref.eval, Bool.false_or])
          | wire u =>
            cases hc : st.env.getD c (.const false) with
            | const b2 =>
              cases b2 with
              | true =>
                exact no_emit (.const true) trivial (by simp only [stepOut, hop, hin, ha, hc, stepOr2])
                  (fun y => by
                    have h2 := hlk y c; rw [hc] at h2
                    simp only [hop, hin, GateOp.eval, List.map_cons, List.map_nil,
                      List.any_cons, List.any_nil, id_eq, Bool.or_false, ← h2, Ref.eval, Bool.or_true])
              | false =>
                exact no_emit (.wire u) (ha ▸ hOk a)
                  (by simp only [stepOut, hop, hin, ha, hc, stepOr2])
                  (fun y => by
                    have h1 := hlk y a; rw [ha] at h1
                    have h2 := hlk y c; rw [hc] at h2
                    simp only [hop, hin, GateOp.eval, List.map_cons, List.map_nil,
                      List.any_cons, List.any_nil, id_eq, Bool.or_false, ← h1, ← h2, Ref.eval])
            | wire v =>
              exact one_emit ⟨.or, [u, v]⟩ (by simp) (by simp only [stepOut, hop, hin, ha, hc, stepOr2])
                (fun y => by
                  have h1 := hlk y a; rw [ha] at h1
                  have h2 := hlk y c; rw [hc] at h2
                  simp only [hop, hin, GateOp.eval, List.map_cons, List.map_nil,
                    List.any_cons, List.any_nil, id_eq, Bool.or_false, ← h1, ← h2, Ref.eval])
        | cons _ _ => simp [hin] at hlen
  · -- NOT
    have h1 := hnot hop
    cases hin : g.inputs with
    | nil =>
      exact no_emit (.const true) trivial (by simp only [stepOut, hop, hin])
        (fun y => by simp only [hop, hin, GateOp.eval, List.map_nil, List.headD_nil,
          Bool.not_false, Ref.eval])
    | cons a rest =>
      cases rest with
      | nil =>
        cases ha : st.env.getD a (.const false) with
        | const b1 =>
          exact no_emit (.const (!b1)) trivial (by simp only [stepOut, hop, hin, ha, stepNot1])
            (fun y => by
              have h1' := hlk y a; rw [ha] at h1'
              simp only [hop, hin, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons,
                ← h1', Ref.eval])
        | wire u =>
          exact one_emit ⟨.not, [u]⟩ (by simp) (by simp only [stepOut, hop, hin, ha, stepNot1])
            (fun y => by
              have h1' := hlk y a; rw [ha] at h1'
              simp only [hop, hin, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons,
                ← h1', Ref.eval])
      | cons _ _ => simp [hin] at h1

private lemma runPass_valid (gs : List Gate) (hgs : ∀ g ∈ gs, GoodGate g)
    (st : St) (w_of : (Fin 8 → Bool) → List Bool) (hv : StValid st w_of) :
    StValid (runPass gs st) (fun y => run gs (w_of y)) := by
  induction gs generalizing st w_of with
  | nil => exact hv
  | cons g gs ih =>
    rw [runPass_cons]
    have h1 := step_valid st w_of hv g (hgs g List.mem_cons_self)
    have h2 := ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) (step st g)
      (fun y => run [g] (w_of y)) h1
    exact h2

private def reads09 (g : Gate) : Bool :=
  [(0 : ℕ), 9].any fun i => g.inputs.contains i

private lemma reads09_iff (g : Gate) :
    reads09 g = true ↔ 0 ∈ g.inputs ∨ 9 ∈ g.inputs := by
  simp [reads09]

private lemma runPass_count_base (gs : List Gate) (hgs : ∀ g ∈ gs, GoodGate g) (st : St)
    (hlen : 10 ≤ st.env.length)
    (h0 : st.env.getD 0 (.const false) = .const false)
    (h9 : st.env.getD 9 (.const false) = .const true) :
    (runPass gs st).gs.length + (gs.filter reads09).length ≤ st.gs.length + gs.length := by
  induction gs generalizing st with
  | nil => simp [runPass]
  | cons g gs ih =>
    rw [runPass_cons, List.filter_cons, List.length_cons]
    have hg := hgs g List.mem_cons_self
    have hst'len : 10 ≤ (step st g).env.length := by rw [step_env_length]; omega
    have hst'0 : (step st g).env.getD 0 (.const false) = .const false := by
      rw [step_env_getD_lt st g 0 (by omega), h0]
    have hst'9 : (step st g).env.getD 9 (.const false) = .const true := by
      rw [step_env_getD_lt st g 9 (by omega), h9]
    have hrec := ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) (step st g)
      hst'len hst'0 hst'9
    cases hr : reads09 g with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hstep := step_gs_le st g
      omega
    | true =>
      simp only [↓reduceIte, List.length_cons]
      have hmem := (reads09_iff g).mp hr
      have hconst : ∃ i ∈ g.inputs, ∃ b : Bool, st.env.getD i (.const false) = .const b := by
        rcases hmem with hm | hm
        · exact ⟨0, hm, false, h0⟩
        · exact ⟨9, hm, true, h9⟩
      have hstep := step_no_emit_of_const st g hg hconst
      omega

private lemma runPass_count_extra (gs : List Gate) (hgs : ∀ g ∈ gs, GoodGate g) (st : St)
    (w0 : ℕ) (b0 : Bool) (hlen : 10 ≤ st.env.length) (hw0 : w0 < st.env.length)
    (h0 : st.env.getD 0 (.const false) = .const false)
    (h9 : st.env.getD 9 (.const false) = .const true)
    (hwc : st.env.getD w0 (.const false) = .const b0)
    (hex : ∃ g ∈ gs, reads09 g = false ∧ w0 ∈ g.inputs) :
    (runPass gs st).gs.length + (gs.filter reads09).length + 1 ≤ st.gs.length + gs.length := by
  induction gs generalizing st with
  | nil => obtain ⟨_, h, _⟩ := hex; cases h
  | cons g gs ih =>
    rw [runPass_cons, List.filter_cons, List.length_cons]
    have hg := hgs g List.mem_cons_self
    have hrest := fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
    have hst'len : 10 ≤ (step st g).env.length := by rw [step_env_length]; omega
    have hst'w0 : w0 < (step st g).env.length := by rw [step_env_length]; omega
    have hst'0 : (step st g).env.getD 0 (.const false) = .const false := by
      rw [step_env_getD_lt st g 0 (by omega), h0]
    have hst'9 : (step st g).env.getD 9 (.const false) = .const true := by
      rw [step_env_getD_lt st g 9 (by omega), h9]
    have hst'wc : (step st g).env.getD w0 (.const false) = .const b0 := by
      rw [step_env_getD_lt st g w0 hw0, hwc]
    by_cases hhit : reads09 g = false ∧ w0 ∈ g.inputs
    · have hstep := step_no_emit_of_const st g hg ⟨w0, hhit.2, b0, hwc⟩
      have hbase := runPass_count_base gs hrest (step st g) hst'len hst'0 hst'9
      simp only [hhit.1, Bool.false_eq_true, ↓reduceIte]
      omega
    · have hex' : ∃ g' ∈ gs, reads09 g' = false ∧ w0 ∈ g'.inputs := by
        obtain ⟨g', hg', h1, h2⟩ := hex
        simp only [List.mem_cons] at hg'
        rcases hg' with rfl | hg'
        · exact absurd ⟨h1, h2⟩ hhit
        · exact ⟨g', hg', h1, h2⟩
      have hrec := ih hrest (step st g) hst'len hst'w0 hst'0 hst'9 hst'wc hex'
      cases hr : reads09 g with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hstep := step_gs_le st g
        omega
      | true =>
        simp only [↓reduceIte, List.length_cons]
        have hmem := (reads09_iff g).mp hr
        have hconst : ∃ i ∈ g.inputs, ∃ b : Bool, st.env.getD i (.const false) = .const b := by
          rcases hmem with hm | hm
          · exact ⟨0, hm, false, h0⟩
          · exact ⟨9, hm, true, h9⟩
        have hstep := step_no_emit_of_const st g hg hconst
        omega

end PEqualNP.Outside.L_meta_2305_aux

open PEqualNP.Outside.L_meta_2305_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_2305 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : List PEqualNP.CircuitLowerBounds.Gate := List.map (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => { op := x2.op, inputs := if x2.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x2.inputs else x2.inputs : PEqualNP.CircuitLowerBounds.Gate }) (List.drop (1 : ℕ) x1.gates);   have x3 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x4 : ℕ) => x3.inputs.contains x4;   have x4 : ℕ := (List.filter x3 x2).length;   have x5 : Prop := ∃ (x5 : List PEqualNP.CircuitLowerBounds.Gate) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 : List PEqualNP.CircuitLowerBounds.Gate), x2 = x5 ++ x6 :: x7 ∧ (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (0 : ℕ) ∈ x6.inputs ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (9 : ℕ) ∈ x6.inputs) ∧ ∃ x8 ∈ x7, x3 x8 = Bool.false ∧ (10 : ℕ) + x5.length ∈ x8.inputs;   PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x7 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x7)).getD (9 : ℕ) Bool.false = !x7 (0 : Fin (9 : ℕ))) → x1.size ≤ (15 : ℕ) → (3 : ℕ) ≤ x4 ∨ (2 : ℕ) ≤ x4 ∧ x5 → (∃ (x10 : Fin (8 : ℕ) → Bool) (x11 : Fin (8 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 (Fin.cons Bool.false x10) ≠ PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 (Fin.cons Bool.false x11)) → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x11 : Fin (8 : ℕ) → Bool) => PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 (Fin.cons Bool.false x11)) (11 : ℕ) := by
  intro C
  dsimp only
  intro hFan hFirst hSize hCases hNonConst
  have hne : C.gates ≠ [] := by
    intro hnil
    have h0 := hFirst (fun _ => false)
    have hlen : (C.wires (List.ofFn (fun _ : Fin 9 => false))).length = 9 := by
      simp [Circuit.wires, hnil]
    have hd : (C.wires (List.ofFn (fun _ : Fin 9 => false))).getD 9 false = false :=
      List.getD_eq_default _ _ (by omega)
    rw [hd] at h0
    exact Bool.false_ne_true h0
  obtain ⟨g0, rest, hgates⟩ := List.exists_cons_of_ne_nil hne
  let x2 : List Gate := rest.map normGate
  have hx2_eq_drop : List.map normGate (C.gates.drop 1) = x2 := by
    simp [hgates, x2]
  have hx2_len : x2.length ≤ 14 := by
    have : C.gates.length ≤ 15 := hSize
    rw [hgates, List.length_cons] at this
    simp [x2]; omega
  have hrest_fan : ∀ g ∈ rest, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2 := fun g hg => hFan g (by rw [hgates]; exact List.mem_cons_of_mem _ hg)
  have hx2_good : ∀ g ∈ x2, GoodGate g := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    exact goodGate_of_norm g' (hrest_fan g' hg').1 (hrest_fan g' hg').2
  have hInit : StValid initSt (fun y => run [g0] (List.ofFn (Fin.cons false y))) := by
    refine ⟨(by intro g hg; cases hg), ?_, ?_⟩
    · intro i
      by_cases hi : i < 10
      · interval_cases i <;> simp [initSt, Ref.ok]
      · rw [List.getD_eq_default _ _ (by simp [initSt]; omega)]; trivial
    · intro y
      refine ⟨by simp [initSt, run], ?_⟩
      intro i hi
      simp only [initSt, List.length_cons, List.length_nil] at hi
      have hw9 : (run [g0] (List.ofFn (Fin.cons false y))).getD 9 false = true := by
        have hf := hFirst (Fin.cons false y)
        have hw : C.wires (List.ofFn (Fin.cons false y)) =
            run rest (run [g0] (List.ofFn (Fin.cons false y))) := by
          change run C.gates _ = _
          rw [hgates, show g0 :: rest = [g0] ++ rest from rfl, run_append]
        rw [hw, run_getD_lt rest _ 9 (by simp [run])] at hf
        simpa using hf
      have hwi (k : Fin 9) : (run [g0] (List.ofFn (Fin.cons false y))).getD k.val false =
          Fin.cons (α := fun _ => Bool) false y k := by
        rw [run_cons, run_nil, List.getD_append _ _ _ _ (by simp)]
        rw [List.getD_eq_getElem _ _ (by simp)]
        simp only [List.getElem_ofFn]
      have hdy (j : Fin 8) : (List.ofFn y).getD j.val false = y j := by
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      have hrun0 : run [] (List.ofFn y) = List.ofFn y := rfl
      rw [show initSt.gs = [] from rfl, hrun0]
      interval_cases i
      · exact (hwi 0).symm
      · exact (hdy 0).trans (hwi 1).symm
      · exact (hdy 1).trans (hwi 2).symm
      · exact (hdy 2).trans (hwi 3).symm
      · exact (hdy 3).trans (hwi 4).symm
      · exact (hdy 4).trans (hwi 5).symm
      · exact (hdy 5).trans (hwi 6).symm
      · exact (hdy 6).trans (hwi 7).symm
      · exact (hdy 7).trans (hwi 8).symm
      · exact hw9.symm
  let finSt := runPass x2 initSt
  have hFinValid : StValid finSt (fun y => run x2 (run [g0] (List.ofFn (Fin.cons false y)))) :=
    runPass_valid x2 hx2_good initSt _ hInit
  have hwires_eq (y : Fin 8 → Bool) :
      run x2 (run [g0] (List.ofFn (Fin.cons false y))) = C.wires (List.ofFn (Fin.cons false y)) := by
    rw [run_map_normGate rest (fun g hg => (hrest_fan g hg).1)]
    change run rest (run [g0] _) = run C.gates _
    rw [hgates, show g0 :: rest = [g0] ++ rest from rfl, run_append]
  have hCount : finSt.gs.length ≤ 11 := by
    change (3 ≤ ((List.map normGate (C.gates.drop 1)).filter reads09).length) ∨
      (2 ≤ ((List.map normGate (C.gates.drop 1)).filter reads09).length ∧
        ∃ (p : List Gate) (g6 : Gate) (q : List Gate),
          List.map normGate (C.gates.drop 1) = p ++ g6 :: q ∧
          ((g6.op = GateOp.and ∧ 0 ∈ g6.inputs) ∨ (g6.op = GateOp.or ∧ 9 ∈ g6.inputs)) ∧
          ∃ g8 ∈ q, reads09 g8 = false ∧ 10 + p.length ∈ g8.inputs) at hCases
    rw [hx2_eq_drop] at hCases
    rcases hCases with h3 | ⟨h2, p, g6, q, hx2eq, hkill, g8, hg8q, hg8nr, hg8in⟩
    · have hb := runPass_count_base x2 hx2_good initSt (by simp [initSt]) rfl rfl
      change finSt.gs.length + (x2.filter reads09).length ≤ 0 + x2.length at hb
      omega
    · have hp_good : ∀ g ∈ p, GoodGate g := fun g hg =>
        hx2_good g (by rw [hx2eq]; exact List.mem_append_left _ hg)
      have hg6_good : GoodGate g6 :=
        hx2_good g6 (by rw [hx2eq]; exact List.mem_append_right _ List.mem_cons_self)
      have hq_good : ∀ g ∈ q, GoodGate g := fun g hg =>
        hx2_good g (by rw [hx2eq]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg))
      let stP := runPass p initSt
      let stG := step stP g6
      have hfin_eq : finSt = runPass q stG := by
        change runPass x2 initSt = _
        rw [hx2eq, runPass_append, runPass_cons]
      have hstP_len : stP.env.length = 10 + p.length := by
        simpa [stP, initSt] using runPass_env_length p initSt
      have hstP_0 : stP.env.getD 0 (.const false) = .const false := by
        rw [runPass_env_getD_lt p initSt 0 (by simp [initSt])]; rfl
      have hstP_9 : stP.env.getD 9 (.const false) = .const true := by
        rw [runPass_env_getD_lt p initSt 9 (by simp [initSt])]; rfl
      have hbp := runPass_count_base p hp_good initSt (by simp [initSt]) rfl rfl
      have hg6_const : ∃ i ∈ g6.inputs, ∃ b : Bool, stP.env.getD i (.const false) = .const b := by
        rcases hkill with ⟨_, hm⟩ | ⟨_, hm⟩
        · exact ⟨0, hm, false, hstP_0⟩
        · exact ⟨9, hm, true, hstP_9⟩
      have hstG_gs : stG.gs.length = stP.gs.length :=
        step_no_emit_of_const stP g6 hg6_good hg6_const
      obtain ⟨b0, hb0⟩ := step_const_of_kill stP g6 hg6_good hstP_0 hstP_9 hkill
      have hstG_len : stG.env.length = 10 + p.length + 1 := by
        rw [step_env_length, hstP_len]
      have hstG_0 : stG.env.getD 0 (.const false) = .const false := by
        rw [step_env_getD_lt stP g6 0 (by omega), hstP_0]
      have hstG_9 : stG.env.getD 9 (.const false) = .const true := by
        rw [step_env_getD_lt stP g6 9 (by omega), hstP_9]
      have hstG_w0 : stG.env.getD (10 + p.length) (.const false) = .const b0 := by
        simpa [hstP_len] using hb0
      have hbq := runPass_count_extra q hq_good stG (10 + p.length) b0
        (by omega) (by omega) hstG_0 hstG_9 hstG_w0 ⟨g8, hg8q, hg8nr, hg8in⟩
      have hfilt_split : (x2.filter reads09).length =
          (p.filter reads09).length + 1 + (q.filter reads09).length := by
        have hg6r : reads09 g6 = true := by
          rw [reads09_iff]
          rcases hkill with ⟨_, hm⟩ | ⟨_, hm⟩
          · exact Or.inl hm
          · exact Or.inr hm
        rw [hx2eq, List.filter_append, List.filter_cons, hg6r]
        simp; omega
      have hlen_split : x2.length = p.length + 1 + q.length := by
        rw [hx2eq]; simp; omega
      rw [hfin_eq]
      change stP.gs.length + (p.filter reads09).length ≤ 0 + p.length at hbp
      omega
  have hout_eval (y : Fin 8 → Bool) :
      (finSt.env.getD C.output (.const false)).eval (run finSt.gs (List.ofFn y)) =
        circuitFun 9 C (Fin.cons false y) := by
    have h1 := lk_eval finSt _ hFinValid y C.output
    rw [hwires_eq y] at h1
    exact h1
  cases hr : finSt.env.getD C.output (.const false) with
  | const b =>
    obtain ⟨y1, y2, hne'⟩ := hNonConst
    have h1 := hout_eval y1; rw [hr] at h1
    have h2 := hout_eval y2; rw [hr] at h2
    simp only [Ref.eval] at h1 h2
    exact absurd (h1.symm.trans h2) hne'
  | wire outW =>
    refine ⟨⟨finSt.gs, outW⟩, hFinValid.1, hCount, ?_⟩
    intro y
    have h1 := hout_eval y
    rw [hr] at h1
    exact h1
