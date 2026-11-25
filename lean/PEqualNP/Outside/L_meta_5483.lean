import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5483

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge {α : Type} (w : List α) (d : α) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma getD_append_left {α : Type} (l₁ l₂ : List α) (d : α) (i : ℕ) (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right_self {α : Type} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  simp [List.getD_eq_getElem?_getD]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w false i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def evalSym (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl b => b
  | Sum.inr i => w.getD i false

def StrictGate (n j : ℕ) (g : Gate) : Prop :=
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    ∃ u v : ℕ, g.inputs = [u, v] ∧ u < n + j ∧ v < n + j) ∨
  (g.op = GateOp.not ∧ ∃ u : ℕ, g.inputs = [u] ∧ u < n + j)

def StrictCircuit (n : ℕ) (gs : List Gate) : Prop :=
  ∀ (j : ℕ) (hj : j < gs.length), StrictGate n j gs[j]

lemma strictGate_fanInTwo {n j : ℕ} {g : Gate} (h : StrictGate n j g) :
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  rcases h with ⟨hop, u, v, hin, _, _⟩ | ⟨hop, u, hin, _⟩
  · rcases hop with hop | hop <;> simp [hop, hin]
  · simp [hop, hin]

lemma strictCircuit_fanInTwo {n : ℕ} {C : Circuit} (h : StrictCircuit n C.gates) :
    FanInTwo C := by
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
  exact strictGate_fanInTwo (h j hj)

lemma strictCircuit_append {n : ℕ} {gs : List Gate} {g : Gate}
    (hgs : StrictCircuit n gs) (hg : StrictGate n gs.length g) :
    StrictCircuit n (gs ++ [g]) := by
  intro j hj
  simp only [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < gs.length
  · rw [List.getElem_append_left hlt]
    exact hgs j hlt
  · have hjeq : j = gs.length := by omega
    subst hjeq
    simpa using hg

def simpGate (n : ℕ) (gs : List Gate) (env : List (Bool ⊕ ℕ)) (g : Gate) :
    List Gate × (Bool ⊕ ℕ) :=
  match g.op, g.inputs with
  | GateOp.and, [] => (gs, Sum.inl true)
  | GateOp.and, [a] => (gs, env.getD a (Sum.inl false))
  | GateOp.and, [a, b] =>
    match env.getD a (Sum.inl false), env.getD b (Sum.inl false) with
    | Sum.inl false, _ => (gs, Sum.inl false)
    | _, Sum.inl false => (gs, Sum.inl false)
    | Sum.inl true, s => (gs, s)
    | s, Sum.inl true => (gs, s)
    | Sum.inr u, Sum.inr v => (gs ++ [⟨GateOp.and, [u, v]⟩], Sum.inr (n + gs.length))
  | GateOp.or, [] => (gs, Sum.inl false)
  | GateOp.or, [a] => (gs, env.getD a (Sum.inl false))
  | GateOp.or, [a, b] =>
    match env.getD a (Sum.inl false), env.getD b (Sum.inl false) with
    | Sum.inl true, _ => (gs, Sum.inl true)
    | _, Sum.inl true => (gs, Sum.inl true)
    | Sum.inl false, s => (gs, s)
    | s, Sum.inl false => (gs, s)
    | Sum.inr u, Sum.inr v => (gs ++ [⟨GateOp.or, [u, v]⟩], Sum.inr (n + gs.length))
  | GateOp.not, [] => (gs, Sum.inl true)
  | GateOp.not, a :: _ =>
    match env.getD a (Sum.inl false) with
    | Sum.inl b => (gs, Sum.inl (!b))
    | Sum.inr u => (gs ++ [⟨GateOp.not, [u]⟩], Sum.inr (n + gs.length))
  | _, _ => (gs, Sum.inl false)

def simpFold (n : ℕ) : List Gate → List Gate × List (Bool ⊕ ℕ) → List Gate × List (Bool ⊕ ℕ)
  | [], st => st
  | g :: rest, (gs, env) =>
    let res := simpGate n gs env g
    simpFold n rest (res.1, env ++ [res.2])

lemma simpGate_len_le (n : ℕ) (gs : List Gate) (env : List (Bool ⊕ ℕ)) (g : Gate) :
    gs.length ≤ (simpGate n gs env g).1.length ∧
      (simpGate n gs env g).1.length ≤ gs.length + 1 := by
  rcases g with ⟨op, ins⟩
  unfold simpGate
  cases op with
  | and =>
    cases ins with
    | nil => simp
    | cons a tl =>
      cases tl with
      | nil => simp
      | cons b tl2 =>
        cases tl2 with
        | nil =>
          dsimp only
          cases env.getD a (Sum.inl false) with
          | inl ba =>
            cases ba with
            | false => simp
            | true =>
              cases env.getD b (Sum.inl false) with
              | inl bb => cases bb <;> simp
              | inr ub => simp
          | inr ua =>
            cases env.getD b (Sum.inl false) with
            | inl bb => cases bb <;> simp
            | inr ub => simp
        | cons c tl3 => simp
  | or =>
    cases ins with
    | nil => simp
    | cons a tl =>
      cases tl with
      | nil => simp
      | cons b tl2 =>
        cases tl2 with
        | nil =>
          dsimp only
          cases env.getD a (Sum.inl false) with
          | inl ba =>
            cases ba with
            | false =>
              cases env.getD b (Sum.inl false) with
              | inl bb => cases bb <;> simp
              | inr ub => simp
            | true => simp
          | inr ua =>
            cases env.getD b (Sum.inl false) with
            | inl bb => cases bb <;> simp
            | inr ub => simp
        | cons c tl3 => simp
  | not =>
    cases ins with
    | nil => simp
    | cons a tl =>
      dsimp only
      cases env.getD a (Sum.inl false) <;> simp
  | mod m => simp
  | maj => simp

lemma simpFold_len_le (n : ℕ) (gates : List Gate) (gs : List Gate) (env : List (Bool ⊕ ℕ)) :
    (simpFold n gates (gs, env)).1.length ≤ gs.length + gates.length := by
  induction gates generalizing gs env with
  | nil => simp [simpFold]
  | cons g rest ih =>
    simp only [simpFold]
    have h1 := ih (simpGate n gs env g).1 (env ++ [(simpGate n gs env g).2])
    have h2 := (simpGate_len_le n gs env g).2
    simp only [List.length_cons]
    omega

lemma simpFold_env_len (n : ℕ) (gates : List Gate) (gs : List Gate) (env : List (Bool ⊕ ℕ)) :
    (simpFold n gates (gs, env)).2.length = env.length + gates.length := by
  induction gates generalizing gs env with
  | nil => simp [simpFold]
  | cons g rest ih =>
    simp only [simpFold]
    rw [ih]
    simp
    omega

lemma simpGate_spec (n : ℕ) (gs : List Gate) (env : List (Bool ⊕ ℕ)) (g : Gate)
    (hgOp : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hgLen : g.inputs.length ≤ 2)
    (hStrict : StrictCircuit n gs)
    (hEnvBnd : ∀ s ∈ env, ∀ u, s = Sum.inr u → u < n + gs.length) :
    let res := simpGate n gs env g
    StrictCircuit n res.1 ∧
    (∀ u, res.2 = Sum.inr u → u < n + res.1.length) ∧
    (∀ (w₀ w' : List Bool), w'.length = n → w₀.length = env.length →
      (∀ i < env.length, evalSym (gs.foldl stepWire w') (env.getD i (Sum.inl false)) = w₀.getD i false) →
      (∀ i < env.length, evalSym (res.1.foldl stepWire w') (env.getD i (Sum.inl false)) = w₀.getD i false) ∧
      evalSym (res.1.foldl stepWire w') res.2 = g.op.eval (g.inputs.map fun i => w₀.getD i false)) := by
  have hEnvGet : ∀ i u, env.getD i (Sum.inl false) = Sum.inr u → u < n + gs.length := by
    intro i u hu
    by_cases hi : i < env.length
    · apply hEnvBnd (env.getD i (Sum.inl false)) _ u hu
      simp [List.getD_eq_getElem?_getD, hi]
    · rw [getD_ge env (Sum.inl false) i (by omega)] at hu
      cases hu
  have hEvalGet : ∀ (w₀ w' : List Bool), w₀.length = env.length →
      (∀ i < env.length, evalSym (gs.foldl stepWire w') (env.getD i (Sum.inl false)) = w₀.getD i false) →
      ∀ i, evalSym (gs.foldl stepWire w') (env.getD i (Sum.inl false)) = w₀.getD i false := by
    intro w₀ w' hlen hEq i
    by_cases hi : i < env.length
    · exact hEq i hi
    · rw [getD_ge env (Sum.inl false) i (by omega), getD_ge w₀ false i (by omega)]
      rfl
  have hAppendStay : ∀ (newG : Gate) (w₀ w' : List Bool), w'.length = n → w₀.length = env.length →
      (∀ i < env.length, evalSym (gs.foldl stepWire w') (env.getD i (Sum.inl false)) = w₀.getD i false) →
      ∀ i < env.length, evalSym ((gs ++ [newG]).foldl stepWire w') (env.getD i (Sum.inl false)) = w₀.getD i false := by
    intro newG w₀ w' hw' hlen hEq i hi
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    cases hs : env.getD i (Sum.inl false) with
    | inl b =>
      have := hEq i hi; rw [hs] at this; exact this
    | inr u =>
      have hu : u < n + gs.length := hEnvGet i u hs
      have hlenW : (gs.foldl stepWire w').length = n + gs.length := by rw [foldl_length, hw']
      have := hEq i hi; rw [hs] at this
      simp only [evalSym, stepWire] at this ⊢
      rw [getD_append_left _ _ false u (by omega)]
      exact this
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgOp
  rcases hgOp with hop | hop | hop
  · cases hin : g.inputs with
    | nil =>
      simp only [simpGate, hop, hin]
      refine ⟨hStrict, by simp, fun w₀ w' _ _ hEq => ⟨hEq, by simp [evalSym, GateOp.eval]⟩⟩
    | cons a tl =>
      cases tl with
      | nil =>
        simp only [simpGate, hop, hin]
        refine ⟨hStrict, fun u hu => hEnvGet a u hu, fun w₀ w' _ hlen hEq => ⟨hEq, ?_⟩⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
        exact hEvalGet w₀ w' hlen hEq a
      | cons b tl2 =>
        cases tl2 with
        | nil =>
          cases ha : env.getD a (Sum.inl false) with
          | inl ba =>
            cases ba with
            | false =>
              simp only [simpGate, hop, hin, ha]
              refine ⟨hStrict, by simp, fun w₀ w' _ hlen hEq => ⟨hEq, ?_⟩⟩
              have hEa := hEvalGet w₀ w' hlen hEq a; rw [ha] at hEa
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
              rw [← hEa]; rfl
            | true =>
              cases hb : env.getD b (Sum.inl false) with
              | inl bb =>
                cases bb with
                | false =>
                  simp only [simpGate, hop, hin, ha, hb]
                  refine ⟨hStrict, by simp, fun w₀ w' _ hlen hEq => ⟨hEq, ?_⟩⟩
                  have hEb := hEvalGet w₀ w' hlen hEq b; rw [hb] at hEb
                  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                  rw [← hEb]; simp [evalSym]
                | true =>
                  simp only [simpGate, hop, hin, ha, hb]
                  refine ⟨hStrict, by simp, fun w₀ w' _ hlen hEq => ⟨hEq, ?_⟩⟩
                  have hEa := hEvalGet w₀ w' hlen hEq a; rw [ha] at hEa
                  have hEb := hEvalGet w₀ w' hlen hEq b; rw [hb] at hEb
                  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                  rw [← hEa, ← hEb]; rfl
              | inr ub =>
                simp only [simpGate, hop, hin, ha, hb]
                refine ⟨hStrict, fun u hu => by cases hu; exact hEnvGet b ub hb, fun w₀ w' _ hlen hEq => ⟨hEq, ?_⟩⟩
                have hEa := hEvalGet w₀ w' hlen hEq a; rw [ha] at hEa
                have hEb := hEvalGet w₀ w' hlen hEq b; rw [hb] at hEb
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                rw [← hEa, ← hEb]; simp [evalSym]
          | inr ua =>
            cases hb : env.getD b (Sum.inl false) with
            | inl bb =>
              cases bb with
              | false =>
                simp only [simpGate, hop, hin, ha, hb]
                refine ⟨hStrict, by simp, fun w₀ w' _ hlen hEq => ⟨hEq, ?_⟩⟩
                have hEb := hEvalGet w₀ w' hlen hEq b; rw [hb] at hEb
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                rw [← hEb]; simp [evalSym]
              | true =>
                simp only [simpGate, hop, hin, ha, hb]
                refine ⟨hStrict, fun u hu => by cases hu; exact hEnvGet a ua ha, fun w₀ w' _ hlen hEq => ⟨hEq, ?_⟩⟩
                have hEa := hEvalGet w₀ w' hlen hEq a; rw [ha] at hEa
                have hEb := hEvalGet w₀ w' hlen hEq b; rw [hb] at hEb
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                rw [← hEa, ← hEb]; simp [evalSym]
            | inr ub =>
              have hua := hEnvGet a ua ha
              have hub := hEnvGet b ub hb
              have hnew : StrictGate n gs.length ⟨GateOp.and, [ua, ub]⟩ :=
                Or.inl ⟨Or.inl rfl, ua, ub, rfl, hua, hub⟩
              simp only [simpGate, hop, hin, ha, hb]
              refine ⟨strictCircuit_append hStrict hnew, ?_, ?_⟩
              · intro u hu; cases hu; simp only [List.length_append, List.length_singleton]; omega
              · intro w₀ w' hw' hlen hEq
                refine ⟨hAppendStay _ w₀ w' hw' hlen hEq, ?_⟩
                rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
                have hlenW : (gs.foldl stepWire w').length = n + gs.length := by rw [foldl_length, hw']
                have hEa := hEvalGet w₀ w' hlen hEq a; rw [ha] at hEa
                have hEb := hEvalGet w₀ w' hlen hEq b; rw [hb] at hEb
                simp only [evalSym, stepWire, ← hlenW, getD_append_right_self]
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
                rw [← hEa, ← hEb]; rfl
        | cons _ _ => simp [hin] at hgLen
  · cases hin : g.inputs with
    | nil =>
      simp only [simpGate, hop, hin]
      refine ⟨hStrict, by simp, fun w₀ w' _ _ hEq => ⟨hEq, by simp [evalSym, GateOp.eval]⟩⟩
    | cons a tl =>
      cases tl with
      | nil =>
        simp only [simpGate, hop, hin]
        refine ⟨hStrict, fun u hu => hEnvGet a u hu, fun w₀ w' _ hlen hEq => ⟨hEq, ?_⟩⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
        exact hEvalGet w₀ w' hlen hEq a
      | cons b tl2 =>
        cases tl2 with
        | nil =>
          cases ha : env.getD a (Sum.inl false) with
          | inl ba =>
            cases ba with
            | true =>
              simp only [simpGate, hop, hin, ha]
              refine ⟨hStrict, by simp, fun w₀ w' _ hlen hEq => ⟨hEq, ?_⟩⟩
              have hEa := hEvalGet w₀ w' hlen hEq a; rw [ha] at hEa
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
              rw [← hEa]; rfl
            | false =>
              cases hb : env.getD b (Sum.inl false) with
              | inl bb =>
                cases bb with
                | true =>
                  simp only [simpGate, hop, hin, ha, hb]
                  refine ⟨hStrict, by simp, fun w₀ w' _ hlen hEq => ⟨hEq, ?_⟩⟩
                  have hEb := hEvalGet w₀ w' hlen hEq b; rw [hb] at hEb
                  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                  rw [← hEb]; simp [evalSym]
                | false =>
                  simp only [simpGate, hop, hin, ha, hb]
                  refine ⟨hStrict, by simp, fun w₀ w' _ hlen hEq => ⟨hEq, ?_⟩⟩
                  have hEa := hEvalGet w₀ w' hlen hEq a; rw [ha] at hEa
                  have hEb := hEvalGet w₀ w' hlen hEq b; rw [hb] at hEb
                  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                  rw [← hEa, ← hEb]; rfl
              | inr ub =>
                simp only [simpGate, hop, hin, ha, hb]
                refine ⟨hStrict, fun u hu => by cases hu; exact hEnvGet b ub hb, fun w₀ w' _ hlen hEq => ⟨hEq, ?_⟩⟩
                have hEa := hEvalGet w₀ w' hlen hEq a; rw [ha] at hEa
                have hEb := hEvalGet w₀ w' hlen hEq b; rw [hb] at hEb
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                rw [← hEa, ← hEb]; simp [evalSym]
          | inr ua =>
            cases hb : env.getD b (Sum.inl false) with
            | inl bb =>
              cases bb with
              | true =>
                simp only [simpGate, hop, hin, ha, hb]
                refine ⟨hStrict, by simp, fun w₀ w' _ hlen hEq => ⟨hEq, ?_⟩⟩
                have hEb := hEvalGet w₀ w' hlen hEq b; rw [hb] at hEb
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                rw [← hEb]; simp [evalSym]
              | false =>
                simp only [simpGate, hop, hin, ha, hb]
                refine ⟨hStrict, fun u hu => by cases hu; exact hEnvGet a ua ha, fun w₀ w' _ hlen hEq => ⟨hEq, ?_⟩⟩
                have hEa := hEvalGet w₀ w' hlen hEq a; rw [ha] at hEa
                have hEb := hEvalGet w₀ w' hlen hEq b; rw [hb] at hEb
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                rw [← hEa, ← hEb]; simp [evalSym]
            | inr ub =>
              have hua := hEnvGet a ua ha
              have hub := hEnvGet b ub hb
              have hnew : StrictGate n gs.length ⟨GateOp.or, [ua, ub]⟩ :=
                Or.inl ⟨Or.inr rfl, ua, ub, rfl, hua, hub⟩
              simp only [simpGate, hop, hin, ha, hb]
              refine ⟨strictCircuit_append hStrict hnew, ?_, ?_⟩
              · intro u hu; cases hu; simp only [List.length_append, List.length_singleton]; omega
              · intro w₀ w' hw' hlen hEq
                refine ⟨hAppendStay _ w₀ w' hw' hlen hEq, ?_⟩
                rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
                have hlenW : (gs.foldl stepWire w').length = n + gs.length := by rw [foldl_length, hw']
                have hEa := hEvalGet w₀ w' hlen hEq a; rw [ha] at hEa
                have hEb := hEvalGet w₀ w' hlen hEq b; rw [hb] at hEb
                simp only [evalSym, stepWire, ← hlenW, getD_append_right_self]
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
                rw [← hEa, ← hEb]; rfl
        | cons _ _ => simp [hin] at hgLen
  · cases hin : g.inputs with
    | nil =>
      simp only [simpGate, hop, hin]
      refine ⟨hStrict, by simp, fun w₀ w' _ _ hEq => ⟨hEq, by simp [evalSym, GateOp.eval]⟩⟩
    | cons a tl =>
      cases ha : env.getD a (Sum.inl false) with
      | inl ba =>
        simp only [simpGate, hop, hin, ha]
        refine ⟨hStrict, by simp, fun w₀ w' _ hlen hEq => ⟨hEq, ?_⟩⟩
        have hEa := hEvalGet w₀ w' hlen hEq a; rw [ha] at hEa
        simp only [GateOp.eval, List.map_cons, List.headD_cons]
        rw [← hEa]; rfl
      | inr ua =>
        have hua := hEnvGet a ua ha
        have hnew : StrictGate n gs.length ⟨GateOp.not, [ua]⟩ :=
          Or.inr ⟨rfl, ua, rfl, hua⟩
        simp only [simpGate, hop, hin, ha]
        refine ⟨strictCircuit_append hStrict hnew, ?_, ?_⟩
        · intro u hu; cases hu; simp only [List.length_append, List.length_singleton]; omega
        · intro w₀ w' hw' hlen hEq
          refine ⟨hAppendStay _ w₀ w' hw' hlen hEq, ?_⟩
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
          have hlenW : (gs.foldl stepWire w').length = n + gs.length := by rw [foldl_length, hw']
          have hEa := hEvalGet w₀ w' hlen hEq a; rw [ha] at hEa
          simp only [evalSym, stepWire, ← hlenW, getD_append_right_self]
          simp only [GateOp.eval, List.map_cons, List.headD_cons]
          rw [← hEa]; rfl

lemma simpFold_spec (n : ℕ) (gates : List Gate) (gs : List Gate) (env : List (Bool ⊕ ℕ))
    (hGates : ∀ g ∈ gates,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hStrict : StrictCircuit n gs)
    (hEnvBnd : ∀ s ∈ env, ∀ u, s = Sum.inr u → u < n + gs.length) :
    let res := simpFold n gates (gs, env)
    StrictCircuit n res.1 ∧
    (∀ s ∈ res.2, ∀ u, s = Sum.inr u → u < n + res.1.length) ∧
    (∀ (w₀ w' : List Bool), w'.length = n → w₀.length = env.length →
      (∀ i < env.length, evalSym (gs.foldl stepWire w') (env.getD i (Sum.inl false)) = w₀.getD i false) →
      ∀ i < res.2.length,
        evalSym (res.1.foldl stepWire w') (res.2.getD i (Sum.inl false)) =
          (gates.foldl stepWire w₀).getD i false) := by
  induction gates generalizing gs env with
  | nil =>
    refine ⟨hStrict, hEnvBnd, ?_⟩
    intro w₀ w' _ _ hEq i hi
    exact hEq i hi
  | cons g rest ih =>
    simp only [simpFold]
    have hg := hGates g (by simp)
    have hrest : ∀ g' ∈ rest,
        g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hGates g' (by simp [hg'])
    have hstep := simpGate_spec n gs env g hg.1 hg.2 hStrict hEnvBnd
    have hlen_ge := (simpGate_len_le n gs env g).1
    have hEnvBnd' : ∀ s ∈ env ++ [(simpGate n gs env g).2], ∀ u,
        s = Sum.inr u → u < n + (simpGate n gs env g).1.length := by
      intro s hs u hu
      rcases List.mem_append.mp hs with hs | hs
      · have := hEnvBnd s hs u hu; omega
      · simp only [List.mem_singleton] at hs; subst hs; exact hstep.2.1 u hu
    have hIH := ih (simpGate n gs env g).1 (env ++ [(simpGate n gs env g).2]) hrest hstep.1 hEnvBnd'
    refine ⟨hIH.1, hIH.2.1, ?_⟩
    intro w₀ w' hw' hlen hEq i hi
    rw [List.foldl_cons]
    apply hIH.2.2 (stepWire w₀ g) w' hw' (by simp [stepWire, hlen])
    · intro k hk
      simp only [List.length_append, List.length_singleton] at hk
      by_cases hlt : k < env.length
      · rw [getD_append_left _ _ _ k hlt]
        have := (hstep.2.2 w₀ w' hw' hlen hEq).1 k hlt
        simp only [stepWire]
        rw [getD_append_left _ _ _ k (by omega)]
        exact this
      · have hkeq : k = env.length := by omega
        rw [hkeq]
        rw [getD_append_right_self]
        simp only [stepWire, ← hlen, getD_append_right_self]
        exact (hstep.2.2 w₀ w' hw' hlen hEq).2
    · exact hi

lemma simpGate_eq_len_agree (n : ℕ) (gs : List Gate) (env : List (Bool ⊕ ℕ)) (g : Gate)
    (hgOp : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hgLen : g.inputs.length ≤ 2)
    (hEmit : (simpGate n gs env g).1.length = gs.length + 1)
    (w₁ w₂ : List Bool) (hw₁ : w₁.length = env.length) (hw₂ : w₂.length = env.length)
    (hAgree : ∀ i < env.length, (∃ u, env.getD i (Sum.inl false) = Sum.inr u) →
      w₁.getD i false = w₂.getD i false) :
    g.op.eval (g.inputs.map fun i => w₁.getD i false) =
      g.op.eval (g.inputs.map fun i => w₂.getD i false) := by
  have hAg : ∀ i u, env.getD i (Sum.inl false) = Sum.inr u → w₁.getD i false = w₂.getD i false := by
    intro i u hu
    by_cases hi : i < env.length
    · exact hAgree i hi ⟨u, hu⟩
    · rw [getD_ge env (Sum.inl false) i (by omega)] at hu; cases hu
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgOp
  rcases hgOp with hop | hop | hop
  · cases hin : g.inputs with
    | nil => simp only [simpGate, hop, hin] at hEmit; omega
    | cons a tl =>
      cases tl with
      | nil => simp only [simpGate, hop, hin] at hEmit; omega
      | cons b tl2 =>
        cases tl2 with
        | nil =>
          cases ha : env.getD a (Sum.inl false) with
          | inl ba =>
            cases ba with
            | false => simp only [simpGate, hop, hin, ha] at hEmit; omega
            | true =>
              cases hb : env.getD b (Sum.inl false) with
              | inl bb => cases bb <;> (simp only [simpGate, hop, hin, ha, hb] at hEmit; omega)
              | inr ub => simp only [simpGate, hop, hin, ha, hb] at hEmit; omega
          | inr ua =>
            cases hb : env.getD b (Sum.inl false) with
            | inl bb => cases bb <;> (simp only [simpGate, hop, hin, ha, hb] at hEmit; omega)
            | inr ub =>
              simp only [hop, GateOp.eval, List.map_cons, List.map_nil]
              rw [hAg a ua ha, hAg b ub hb]
        | cons _ _ => simp [hin] at hgLen
  · cases hin : g.inputs with
    | nil => simp only [simpGate, hop, hin] at hEmit; omega
    | cons a tl =>
      cases tl with
      | nil => simp only [simpGate, hop, hin] at hEmit; omega
      | cons b tl2 =>
        cases tl2 with
        | nil =>
          cases ha : env.getD a (Sum.inl false) with
          | inl ba =>
            cases ba with
            | true => simp only [simpGate, hop, hin, ha] at hEmit; omega
            | false =>
              cases hb : env.getD b (Sum.inl false) with
              | inl bb => cases bb <;> (simp only [simpGate, hop, hin, ha, hb] at hEmit; omega)
              | inr ub => simp only [simpGate, hop, hin, ha, hb] at hEmit; omega
          | inr ua =>
            cases hb : env.getD b (Sum.inl false) with
            | inl bb => cases bb <;> (simp only [simpGate, hop, hin, ha, hb] at hEmit; omega)
            | inr ub =>
              simp only [hop, GateOp.eval, List.map_cons, List.map_nil]
              rw [hAg a ua ha, hAg b ub hb]
        | cons _ _ => simp [hin] at hgLen
  · cases hin : g.inputs with
    | nil => simp only [simpGate, hop, hin] at hEmit; omega
    | cons a tl =>
      cases ha : env.getD a (Sum.inl false) with
      | inl ba => simp only [simpGate, hop, hin, ha] at hEmit; omega
      | inr ua =>
        simp only [hop, GateOp.eval, List.map_cons, List.headD_cons]
        rw [hAg a ua ha]

lemma simpFold_eq_len_agree (n : ℕ) (gates : List Gate) (gs : List Gate) (env : List (Bool ⊕ ℕ))
    (hGates : ∀ g ∈ gates,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hFull : (simpFold n gates (gs, env)).1.length = gs.length + gates.length)
    (w₁ w₂ : List Bool) (hw₁ : w₁.length = env.length) (hw₂ : w₂.length = env.length)
    (hAgree : ∀ i < env.length, (∃ u, env.getD i (Sum.inl false) = Sum.inr u) →
      w₁.getD i false = w₂.getD i false) :
    ∀ i < (simpFold n gates (gs, env)).2.length,
      (∃ u, (simpFold n gates (gs, env)).2.getD i (Sum.inl false) = Sum.inr u) →
      (gates.foldl stepWire w₁).getD i false = (gates.foldl stepWire w₂).getD i false := by
  induction gates generalizing gs env w₁ w₂ with
  | nil =>
    intro i hi hu
    exact hAgree i hi hu
  | cons g rest ih =>
    simp only [simpFold] at hFull ⊢
    rw [List.foldl_cons, List.foldl_cons]
    have hg := hGates g (by simp)
    have hrest : ∀ g' ∈ rest,
        g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hGates g' (by simp [hg'])
    have hle1 := (simpGate_len_le n gs env g).2
    have hle2 := simpFold_len_le n rest (simpGate n gs env g).1 (env ++ [(simpGate n gs env g).2])
    simp only [List.length_cons] at hFull
    have hEmit : (simpGate n gs env g).1.length = gs.length + 1 := by omega
    have hRestFull : (simpFold n rest ((simpGate n gs env g).1, env ++ [(simpGate n gs env g).2])).1.length =
        (simpGate n gs env g).1.length + rest.length := by omega
    have hValEq := simpGate_eq_len_agree n gs env g hg.1 hg.2 hEmit w₁ w₂ hw₁ hw₂ hAgree
    apply ih (simpGate n gs env g).1 (env ++ [(simpGate n gs env g).2]) hrest hRestFull
      (stepWire w₁ g) (stepWire w₂ g) (by simp [stepWire, hw₁]) (by simp [stepWire, hw₂])
    intro k hk hku
    simp only [List.length_append, List.length_singleton] at hk
    by_cases hlt : k < env.length
    · rw [getD_append_left _ _ _ k hlt] at hku
      simp only [stepWire]
      rw [getD_append_left _ _ _ k (by omega), getD_append_left _ _ _ k (by omega)]
      exact hAgree k hlt hku
    · have hkeq : k = env.length := by omega
      rw [hkeq]
      simp only [stepWire, ← hw₁, ← hw₂]
      rw [getD_append_right_self, hw₁, ← hw₂, getD_append_right_self]
      exact hValEq

def initEnv (n : ℕ) : List (Bool ⊕ ℕ) :=
  (List.finRange n).map fun i => Sum.inr i.val

lemma initEnv_length (n : ℕ) : (initEnv n).length = n := by
  simp [initEnv]

lemma initEnv_getD_lt (n i : ℕ) (hi : i < n) :
    (initEnv n).getD i (Sum.inl false) = Sum.inr i := by
  simp [initEnv, List.getD_eq_getElem?_getD, hi]

lemma initEnv_snoc_getD_last (n : ℕ) (x d : Bool ⊕ ℕ) :
    (initEnv n ++ [x]).getD n d = x := by
  have h := getD_append_right_self (initEnv n) x d
  rwa [initEnv_length] at h

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

lemma restrict_size_lt {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {t : ℕ}
    (hC : HasCircuitSize (n + 1) f t)
    (hEss : ∃ x y : Fin (n + 1) → Bool,
      (∀ i : Fin n, x i.castSucc = y i.castSucc) ∧ f x ≠ f y)
    (hNonConst : ∃ z₀ z₁ : Fin n → Bool,
      f (Fin.snoc z₀ false) = false ∧ f (Fin.snoc z₁ false) = true) :
    HasCircuitSize n (fun z : Fin n → Bool => f (Fin.snoc z false)) (t - 1) := by
  obtain ⟨C, hFan, hSz, hEval⟩ := hC
  let e0 : List (Bool ⊕ ℕ) := initEnv n ++ [Sum.inl false]
  have he0_len : e0.length = n + 1 := by simp [e0, initEnv_length]
  have hEnvBnd : ∀ s ∈ e0, ∀ u, s = Sum.inr u → u < n + ([] : List Gate).length := by
    intro s hs u hu
    simp only [e0, initEnv, List.mem_append, List.mem_map, List.mem_finRange, List.mem_singleton] at hs
    rcases hs with ⟨i, _, hi⟩ | hs
    · rw [← hi] at hu; cases hu; simpa using i.isLt
    · rw [hs] at hu; cases hu
  have hSpec := simpFold_spec n C.gates [] e0 hFan (by intro j hj; simp at hj) hEnvBnd
  set res := simpFold n C.gates ([], e0)
  have hres_env_len : res.2.length = n + 1 + C.gates.length := by
    rw [simpFold_env_len, he0_len]
  have hEvalLink : ∀ z : Fin n → Bool,
      evalSym (res.1.foldl stepWire (List.ofFn z)) (res.2.getD C.output (Sum.inl false)) =
        f (Fin.snoc z false) := by
    intro z
    rw [← hEval (Fin.snoc z false), Circuit.eval, wires_eq_foldl]
    by_cases hout : C.output < res.2.length
    · apply hSpec.2.2 (List.ofFn (Fin.snoc z false)) (List.ofFn z) (by simp) (by simp [he0_len])
      · intro i hi
        rw [he0_len] at hi
        by_cases hin : i < n
        · simp only [e0]
          rw [getD_append_left _ _ _ i (by rw [initEnv_length]; exact hin), initEnv_getD_lt n i hin]
          simp only [evalSym, List.foldl_nil]
          rw [ofFn_getD z i hin, ofFn_getD (Fin.snoc z false) i hi]
          exact (Fin.snoc_castSucc (α := fun _ => Bool) false z ⟨i, hin⟩).symm
        · have hieq : i = n := by omega
          rw [hieq]
          simp only [e0, initEnv_snoc_getD_last, evalSym]
          rw [ofFn_getD (Fin.snoc z false) n (Nat.lt_succ_self n)]
          exact (Fin.snoc_last (α := fun _ => Bool) false z).symm
      · exact hout
    · rw [getD_ge res.2 (Sum.inl false) C.output (by omega)]
      rw [getD_ge (C.gates.foldl stepWire (List.ofFn (Fin.snoc z false))) false C.output
        (by rw [foldl_length, List.length_ofFn]; omega)]
      rfl
  cases houtSym : res.2.getD C.output (Sum.inl false) with
  | inl b =>
    obtain ⟨z₀, z₁, hz₀, hz₁⟩ := hNonConst
    have h0 := hEvalLink z₀; rw [houtSym] at h0
    have h1 := hEvalLink z₁; rw [houtSym] at h1
    simp only [evalSym] at h0 h1
    rw [hz₀] at h0; rw [hz₁] at h1
    rw [h0] at h1; cases h1
  | inr outW =>
    have hlen_le : res.1.length ≤ C.gates.length := by
      have := simpFold_len_le n C.gates [] e0
      simp only [List.length_nil, zero_add] at this
      exact this
    have hlen_lt : res.1.length < C.gates.length := by
      by_contra hge
      have hFull : res.1.length = ([] : List Gate).length + C.gates.length := by
        simp; omega
      obtain ⟨x, y, hxy, hne⟩ := hEss
      have houtLt : C.output < res.2.length := by
        by_contra hge2
        rw [getD_ge res.2 (Sum.inl false) C.output (by omega)] at houtSym
        cases houtSym
      have hAg := simpFold_eq_len_agree n C.gates [] e0 hFan hFull
        (List.ofFn x) (List.ofFn y) (by simp [he0_len]) (by simp [he0_len]) (by
          intro i hi hiu
          rw [he0_len] at hi
          by_cases hin : i < n
          · rw [ofFn_getD x i hi, ofFn_getD y i hi]
            exact hxy ⟨i, hin⟩
          · have hieq : i = n := by omega
            rw [hieq] at hiu
            simp only [e0, initEnv_snoc_getD_last] at hiu
            obtain ⟨u, hu⟩ := hiu; cases hu)
        C.output houtLt ⟨outW, houtSym⟩
      have hfx : f x = (C.gates.foldl stepWire (List.ofFn x)).getD C.output false :=
        (hEval x).symm
      have hfy : f y = (C.gates.foldl stepWire (List.ofFn y)).getD C.output false :=
        (hEval y).symm
      exact hne (by rw [hfx, hfy]; exact hAg)
    refine ⟨⟨res.1, outW⟩, strictCircuit_fanInTwo hSpec.1, ?_, ?_⟩
    · change res.1.length ≤ t - 1
      change C.gates.length ≤ t at hSz
      omega
    · intro z
      have hz := hEvalLink z
      rw [houtSym] at hz
      exact hz

lemma to_strict_circuit {n : ℕ} {f : (Fin n → Bool) → Bool} {t : ℕ}
    (hC : HasCircuitSize n f t)
    (hNonConst : ∃ z₀ z₁ : Fin n → Bool, f z₀ = false ∧ f z₁ = true) :
    ∃ D : Circuit, StrictCircuit n D.gates ∧ D.output < n + D.gates.length ∧
      D.gates.length ≤ t ∧ ∀ x : Fin n → Bool, D.eval (List.ofFn x) = f x := by
  obtain ⟨C, hFan, hSz, hEval⟩ := hC
  let e0 := initEnv n
  have he0_len : e0.length = n := initEnv_length n
  have hEnvBnd : ∀ s ∈ e0, ∀ u, s = Sum.inr u → u < n + ([] : List Gate).length := by
    intro s hs u hu
    simp only [e0, initEnv, List.mem_map, List.mem_finRange] at hs
    obtain ⟨i, _, hi⟩ := hs
    rw [← hi] at hu; cases hu; simpa using i.isLt
  have hSpec := simpFold_spec n C.gates [] e0 hFan (by intro j hj; simp at hj) hEnvBnd
  set res := simpFold n C.gates ([], e0)
  have hres_env_len : res.2.length = n + C.gates.length := by
    rw [simpFold_env_len, he0_len]
  have hEvalLink : ∀ x : Fin n → Bool,
      evalSym (res.1.foldl stepWire (List.ofFn x)) (res.2.getD C.output (Sum.inl false)) = f x := by
    intro x
    rw [← hEval x, Circuit.eval, wires_eq_foldl]
    by_cases hout : C.output < res.2.length
    · apply hSpec.2.2 (List.ofFn x) (List.ofFn x) (by simp) (by simp [he0_len])
      · intro i hi
        rw [he0_len] at hi
        rw [initEnv_getD_lt n i hi]
        rfl
      · exact hout
    · rw [getD_ge res.2 (Sum.inl false) C.output (by omega)]
      rw [getD_ge (C.gates.foldl stepWire (List.ofFn x)) false C.output
        (by rw [foldl_length, List.length_ofFn]; omega)]
      rfl
  cases houtSym : res.2.getD C.output (Sum.inl false) with
  | inl b =>
    obtain ⟨z₀, z₁, hz₀, hz₁⟩ := hNonConst
    have h0 := hEvalLink z₀; rw [houtSym] at h0
    have h1 := hEvalLink z₁; rw [houtSym] at h1
    simp only [evalSym] at h0 h1
    rw [hz₀] at h0; rw [hz₁] at h1
    rw [h0] at h1; cases h1
  | inr outW =>
    have houtLt : C.output < res.2.length := by
      by_contra hge
      rw [getD_ge res.2 (Sum.inl false) C.output (by omega)] at houtSym
      cases houtSym
    have houtMem : Sum.inr outW ∈ res.2 := by
      rw [← houtSym]
      simp [List.getD_eq_getElem?_getD, houtLt]
    have houtBnd : outW < n + res.1.length := hSpec.2.1 _ houtMem outW rfl
    have hlen_le : res.1.length ≤ t := by
      have h1 : res.1.length ≤ ([] : List Gate).length + C.gates.length :=
        simpFold_len_le n C.gates [] e0
      simp only [List.length_nil, zero_add] at h1
      change C.gates.length ≤ t at hSz
      omega
    exact ⟨⟨res.1, outW⟩, hSpec.1, houtBnd, hlen_le, fun x => by
      have hx := hEvalLink x; rw [houtSym] at hx; exact hx⟩

def wval {n : ℕ} (D : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (D.wires (List.ofFn x)).getD w false

lemma wval_input {n : ℕ} (D : Circuit) (i : Fin n) (x : Fin n → Bool) :
    wval D i.val x = x i := by
  unfold wval
  rw [wires_eq_foldl, foldl_getD_lt _ _ i.val (by simp)]
  exact ofFn_getD x i.val i.isLt

lemma wval_gate_and {n : ℕ} (D : Circuit) (j u v : ℕ) (hj : j < D.gates.length)
    (h : D.gates[j] = ⟨GateOp.and, [u, v]⟩) (hu : u < n + j) (hv : v < n + j) (x : Fin n → Bool) :
    wval D (n + j) x = (wval D u x && wval D v x) := by
  unfold wval
  have hl : (List.ofFn x).length = n := by simp
  have key := foldl_getD_gate D.gates (List.ofFn x) j hj
  rw [hl] at key
  rw [wires_eq_foldl, key, h]
  simp [GateOp.eval, hu, hv]

lemma wval_gate_or {n : ℕ} (D : Circuit) (j u v : ℕ) (hj : j < D.gates.length)
    (h : D.gates[j] = ⟨GateOp.or, [u, v]⟩) (hu : u < n + j) (hv : v < n + j) (x : Fin n → Bool) :
    wval D (n + j) x = (wval D u x || wval D v x) := by
  unfold wval
  have hl : (List.ofFn x).length = n := by simp
  have key := foldl_getD_gate D.gates (List.ofFn x) j hj
  rw [hl] at key
  rw [wires_eq_foldl, key, h]
  simp [GateOp.eval, hu, hv]

lemma wval_gate_not {n : ℕ} (D : Circuit) (j u : ℕ) (hj : j < D.gates.length)
    (h : D.gates[j] = ⟨GateOp.not, [u]⟩) (hu : u < n + j) (x : Fin n → Bool) :
    wval D (n + j) x = !(wval D u x) := by
  unfold wval
  have hl : (List.ofFn x).length = n := by simp
  have key := foldl_getD_gate D.gates (List.ofFn x) j hj
  rw [hl] at key
  rw [wires_eq_foldl, key, h]
  simp [GateOp.eval, hu]

def isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def maj3 (x : Fin 3 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)

lemma maj3_not_indep (f : (Fin 3 → Bool) → Bool)
    (hf : (∀ x, f x = maj3 x) ∨ (∀ x, f x = !(maj3 x)))
    (c : Fin 3) (hInd : ∀ x y : Fin 3 → Bool, (∀ i, i ≠ c → x i = y i) → f x = f y) :
    False := by
  have hcheck : ∀ c : Fin 3, ∃ x y : Fin 3 → Bool,
      (∀ i, i ≠ c → x i = y i) ∧ maj3 x ≠ maj3 y := by decide
  obtain ⟨x, y, hxy, hne⟩ := hcheck c
  have heq := hInd x y hxy
  rcases hf with h | h
  · rw [h x, h y] at heq; exact hne heq
  · rw [h x, h y] at heq; exact hne (Bool.not_inj heq)

lemma maj3_not_fixed_lit (f : (Fin 3 → Bool) → Bool)
    (hf : (∀ x, f x = maj3 x) ∨ (∀ x, f x = !(maj3 x)))
    (v : Fin 3) (b : Bool) (hFix : ∃ c : Bool, ∀ x : Fin 3 → Bool, x v = b → f x = c) :
    False := by
  have hcheck : ∀ (v : Fin 3) (b : Bool), ∃ x y : Fin 3 → Bool,
      x v = b ∧ y v = b ∧ maj3 x ≠ maj3 y := by decide
  obtain ⟨x, y, hx, hy, hne⟩ := hcheck v b
  obtain ⟨c, hc⟩ := hFix
  have heq : f x = f y := by rw [hc x hx, hc y hy]
  rcases hf with h | h
  · rw [h x, h y] at heq; exact hne heq
  · rw [h x, h y] at heq; exact hne (Bool.not_inj heq)

lemma strict_gate0_indep (D : Circuit) (h0 : 0 < D.gates.length) (hs0 : StrictGate 3 0 D.gates[0]) :
    ∃ c : Fin 3, ∀ x y : Fin 3 → Bool, (∀ i, i ≠ c → x i = y i) →
      wval D 3 x = wval D 3 y := by
  rcases hs0 with ⟨hop, u, v, hin, hu, hv⟩ | ⟨hop, u, hin, hu⟩
  · have hc : ∃ c : Fin 3, c.val ≠ u ∧ c.val ≠ v := by
      have : ∀ u < 3, ∀ v < 3, ∃ c : Fin 3, c.val ≠ u ∧ c.val ≠ v := by decide
      exact this u hu v hv
    obtain ⟨c, hcu, hcv⟩ := hc
    refine ⟨c, fun x y hxy => ?_⟩
    have hux : wval D u x = x ⟨u, hu⟩ := wval_input D ⟨u, hu⟩ x
    have huy : wval D u y = y ⟨u, hu⟩ := wval_input D ⟨u, hu⟩ y
    have hvx : wval D v x = x ⟨v, hv⟩ := wval_input D ⟨v, hv⟩ x
    have hvy : wval D v y = y ⟨v, hv⟩ := wval_input D ⟨v, hv⟩ y
    have h1 : x ⟨u, hu⟩ = y ⟨u, hu⟩ := hxy ⟨u, hu⟩ (fun h => hcu (congrArg Fin.val h).symm)
    have h2 : x ⟨v, hv⟩ = y ⟨v, hv⟩ := hxy ⟨v, hv⟩ (fun h => hcv (congrArg Fin.val h).symm)
    rcases hop with hop | hop
    · have hg : D.gates[0] = ⟨GateOp.and, [u, v]⟩ := by cases h : D.gates[0]; simp_all
      rw [wval_gate_and D 0 u v h0 hg hu hv x, wval_gate_and D 0 u v h0 hg hu hv y]
      rw [hux, huy, hvx, hvy, h1, h2]
    · have hg : D.gates[0] = ⟨GateOp.or, [u, v]⟩ := by cases h : D.gates[0]; simp_all
      rw [wval_gate_or D 0 u v h0 hg hu hv x, wval_gate_or D 0 u v h0 hg hu hv y]
      rw [hux, huy, hvx, hvy, h1, h2]
  · have hc : ∃ c : Fin 3, c.val ≠ u := by
      have : ∀ u < 3, ∃ c : Fin 3, c.val ≠ u := by decide
      exact this u hu
    obtain ⟨c, hcu⟩ := hc
    refine ⟨c, fun x y hxy => ?_⟩
    have hg : D.gates[0] = ⟨GateOp.not, [u]⟩ := by cases h : D.gates[0]; simp_all
    rw [wval_gate_not D 0 u h0 hg hu x, wval_gate_not D 0 u h0 hg hu y]
    rw [wval_input D ⟨u, hu⟩ x, wval_input D ⟨u, hu⟩ y]
    rw [hxy ⟨u, hu⟩ (fun h => hcu (congrArg Fin.val h).symm)]

lemma strict_not_wire_lt5_maj (D : Circuit) (hS : StrictCircuit 3 D.gates)
    (w : ℕ) (hw : w < 5) (hwBnd : w < 3 + D.gates.length)
    (hf : (∀ x, wval D w x = maj3 x) ∨ (∀ x, wval D w x = !(maj3 x))) : False := by
  by_cases hw3 : w < 3
  · have hEq : ∀ x, wval D w x = x ⟨w, hw3⟩ := fun x => wval_input D ⟨w, hw3⟩ x
    exact maj3_not_fixed_lit (wval D w) hf ⟨w, hw3⟩ false ⟨false, fun x hx => by rw [hEq, hx]⟩
  · by_cases hw3eq : w = 3
    · subst hw3eq
      have h0 : 0 < D.gates.length := by omega
      obtain ⟨c, hc⟩ := strict_gate0_indep D h0 (hS 0 h0)
      exact maj3_not_indep (wval D 3) hf c hc
    · have hw4 : w = 4 := by omega
      subst hw4
      have h1 : 1 < D.gates.length := by omega
      have h0 : 0 < D.gates.length := by omega
      rcases hS 1 h1 with ⟨hop, u, v, hin, hu, hv⟩ | ⟨hop, u, hin, hu⟩
      · have hgate : ∀ x : Fin 3 → Bool, wval D 4 x =
            if isAnd D.gates[1].op then wval D u x && wval D v x else wval D u x || wval D v x := by
          intro x
          rcases hop with hop | hop
          · have hg : D.gates[1] = ⟨GateOp.and, [u, v]⟩ := by cases h : D.gates[1]; simp_all
            simp [hop, isAnd, wval_gate_and D 1 u v h1 hg hu hv x]
          · have hg : D.gates[1] = ⟨GateOp.or, [u, v]⟩ := by cases h : D.gates[1]; simp_all
            simp [hop, isAnd, wval_gate_or D 1 u v h1 hg hu hv x]
        by_cases hu3 : u < 3
        · rcases hop with hop | hop
          · exact maj3_not_fixed_lit (wval D 4) hf ⟨u, hu3⟩ false ⟨false, fun x hx => by
              rw [hgate x]; simp [hop, isAnd, wval_input D ⟨u, hu3⟩ x, hx]⟩
          · exact maj3_not_fixed_lit (wval D 4) hf ⟨u, hu3⟩ true ⟨true, fun x hx => by
              rw [hgate x]; simp [hop, isAnd, wval_input D ⟨u, hu3⟩ x, hx]⟩
        · by_cases hv3 : v < 3
          · rcases hop with hop | hop
            · exact maj3_not_fixed_lit (wval D 4) hf ⟨v, hv3⟩ false ⟨false, fun x hx => by
                rw [hgate x]; simp [hop, isAnd, wval_input D ⟨v, hv3⟩ x, hx]⟩
            · exact maj3_not_fixed_lit (wval D 4) hf ⟨v, hv3⟩ true ⟨true, fun x hx => by
                rw [hgate x]; simp [hop, isAnd, wval_input D ⟨v, hv3⟩ x, hx]⟩
          · have hueq : u = 3 := by omega
            have hveq : v = 3 := by omega
            subst hueq; subst hveq
            obtain ⟨c, hc⟩ := strict_gate0_indep D h0 (hS 0 h0)
            exact maj3_not_indep (wval D 4) hf c (fun x y hxy => by
              rw [hgate x, hgate y, hc x y hxy])
      · have hg : D.gates[1] = ⟨GateOp.not, [u]⟩ := by cases h : D.gates[1]; simp_all
        by_cases hu3 : u < 3
        · exact maj3_not_fixed_lit (wval D 4) hf ⟨u, hu3⟩ false ⟨true, fun x hx => by
            rw [wval_gate_not D 1 u h1 hg hu x, wval_input D ⟨u, hu3⟩ x, hx]; rfl⟩
        · have hueq : u = 3 := by omega
          subst hueq
          obtain ⟨c, hc⟩ := strict_gate0_indep D h0 (hS 0 h0)
          exact maj3_not_indep (wval D 4) hf c (fun x y hxy => by
            rw [wval_gate_not D 1 3 h1 hg hu x, wval_gate_not D 1 3 h1 hg hu y, hc x y hxy])

lemma maj3_no_factor_g0 (c : Fin 3) (g0 : (Fin 3 → Bool) → Bool)
    (hInd0 : ∀ x y : Fin 3 → Bool, (∀ i, i ≠ c → x i = y i) → g0 x = g0 y)
    (F : Bool → Bool → Bool)
    (hF : ∀ x : Fin 3 → Bool, maj3 x = F (g0 x) (x c)) : False := by
  let x0 : Fin 3 → Bool := fun _ => false
  let x2 : Fin 3 → Bool := fun i => decide (i ≠ c)
  let x1 : Fin 3 → Bool := fun i => decide (i = c + 1)
  have hsame : g0 x0 = g0 x1 ∨ g0 x0 = g0 x2 ∨ g0 x1 = g0 x2 := by
    cases g0 x0 <;> cases g0 x1 <;> cases g0 x2 <;> simp
  have hmaj_0 : ∀ b : Bool, maj3 (Function.update x0 c b) = false := by
    intro b
    have : ∀ (c : Fin 3) (b : Bool), maj3 (Function.update (fun _ : Fin 3 => false) c b) = false := by
      decide
    exact this c b
  have hmaj_2 : ∀ b : Bool, maj3 (Function.update x2 c b) = true := by
    intro b
    have : ∀ (c : Fin 3) (b : Bool), maj3 (Function.update (fun i : Fin 3 => decide (i ≠ c)) c b) = true := by
      decide
    exact this c b
  have hmaj_1 : ∀ b : Bool, maj3 (Function.update x1 c b) = b := by
    intro b
    have : ∀ (c : Fin 3) (b : Bool), maj3 (Function.update (fun i : Fin 3 => decide (i = c + 1)) c b) = b := by
      decide
    exact this c b
  have hg0_upd : ∀ x b, g0 (Function.update x c b) = g0 x := fun x b =>
    hInd0 _ _ (fun i hi => by simp [Function.update, hi])
  rcases hsame with h01 | h02 | h12
  · have e1 := hF (Function.update x0 c true)
    have e2 := hF (Function.update x1 c true)
    rw [hmaj_0 true, hg0_upd, Function.update_self] at e1
    rw [hmaj_1 true, hg0_upd, Function.update_self, ← h01] at e2
    rw [← e1] at e2; cases e2
  · have e1 := hF (Function.update x0 c false)
    have e2 := hF (Function.update x2 c false)
    rw [hmaj_0 false, hg0_upd, Function.update_self] at e1
    rw [hmaj_2 false, hg0_upd, Function.update_self, ← h02] at e2
    rw [← e1] at e2; cases e2
  · have e1 := hF (Function.update x1 c false)
    have e2 := hF (Function.update x2 c false)
    rw [hmaj_1 false, hg0_upd, Function.update_self] at e1
    rw [hmaj_2 false, hg0_upd, Function.update_self, ← h12] at e2
    rw [← e1] at e2; cases e2

lemma maj3_no_disjoint_op (a c : Fin 3) (hac : a ≠ c)
    (g0 g1 : (Fin 3 → Bool) → Bool)
    (hInd0 : ∀ x y : Fin 3 → Bool, (∀ i, i ≠ c → x i = y i) → g0 x = g0 y)
    (hInd1 : ∀ x y : Fin 3 → Bool, (∀ i, i ≠ a → x i = y i) → g1 x = g1 y)
    (hOp : (∀ x, maj3 x = (g0 x || g1 x)) ∨ (∀ x, maj3 x = (g0 x && g1 x))) : False := by
  rcases hOp with hOr | hAnd
  · have hex : ∃ x1 : Fin 3 → Bool, maj3 x1 = true ∧
        maj3 (Function.update x1 c false) = false ∧ maj3 (Function.update x1 a false) = false := by
      have : ∀ a c : Fin 3, a ≠ c → ∃ x1 : Fin 3 → Bool, maj3 x1 = true ∧
          maj3 (Function.update x1 c false) = false ∧ maj3 (Function.update x1 a false) = false := by
        decide
      exact this a c hac
    obtain ⟨x1, hx1, hxc, hxa⟩ := hex
    have hor1 := hOr x1; rw [hx1] at hor1
    cases hg0 : g0 x1 with
    | true =>
      have h0c : g0 (Function.update x1 c false) = true := by
        rw [hInd0 _ x1 (fun i hi => by simp [Function.update, hi])]; exact hg0
      have e := hOr (Function.update x1 c false)
      rw [hxc, h0c] at e; simp at e
    | false =>
      rw [hg0] at hor1; simp at hor1
      have h1a : g1 (Function.update x1 a false) = true := by
        rw [hInd1 _ x1 (fun i hi => by simp [Function.update, hi])]; exact hor1
      have e := hOr (Function.update x1 a false)
      rw [hxa, h1a] at e; simp at e
  · have hex : ∃ x1 : Fin 3 → Bool, maj3 x1 = false ∧
        maj3 (Function.update x1 c true) = true ∧ maj3 (Function.update x1 a true) = true := by
      have : ∀ a c : Fin 3, a ≠ c → ∃ x1 : Fin 3 → Bool, maj3 x1 = false ∧
          maj3 (Function.update x1 c true) = true ∧ maj3 (Function.update x1 a true) = true := by
        decide
      exact this a c hac
    obtain ⟨x1, hx1, hxc, hxa⟩ := hex
    have hand1 := hAnd x1; rw [hx1] at hand1
    cases hg0 : g0 x1 with
    | false =>
      have h0c : g0 (Function.update x1 c true) = false := by
        rw [hInd0 _ x1 (fun i hi => by simp [Function.update, hi])]; exact hg0
      have e := hAnd (Function.update x1 c true)
      rw [hxc, h0c] at e; simp at e
    | true =>
      rw [hg0] at hand1; simp at hand1
      have h1a : g1 (Function.update x1 a true) = false := by
        rw [hInd1 _ x1 (fun i hi => by simp [Function.update, hi])]; exact hand1
      have e := hAnd (Function.update x1 a true)
      rw [hxa, h1a] at e; simp at e

lemma not_hasCircuitSize_maj3_3 : ¬ HasCircuitSize 3 maj3 3 := by
  intro hC
  have hNonConst : ∃ z₀ z₁ : Fin 3 → Bool, maj3 z₀ = false ∧ maj3 z₁ = true := by decide
  obtain ⟨D, hS, houtBnd, hLen, hEval⟩ := to_strict_circuit hC hNonConst
  by_cases hout5 : D.output < 5
  · exact strict_not_wire_lt5_maj D hS D.output hout5 houtBnd (Or.inl hEval)
  · have houtEq : D.output = 5 := by omega
    have hLen3 : D.gates.length = 3 := by omega
    have h0 : 0 < D.gates.length := by omega
    have h1 : 1 < D.gates.length := by omega
    have h2 : 2 < D.gates.length := by omega
    have hEval5 : ∀ x, wval D 5 x = maj3 x := fun x => by
      have := hEval x; rw [Circuit.eval, houtEq] at this; exact this
    rcases hS 2 h2 with ⟨hop2, u2, v2, hin2, hu2, hv2⟩ | ⟨hop2, u2, hin2, hu2⟩
    · have hgate2 : ∀ x, maj3 x =
          if isAnd D.gates[2].op then wval D u2 x && wval D v2 x else wval D u2 x || wval D v2 x := by
        intro x
        rw [← hEval5 x]
        rcases hop2 with hop2 | hop2
        · have hg : D.gates[2] = ⟨GateOp.and, [u2, v2]⟩ := by cases h : D.gates[2]; simp_all
          simp [hop2, isAnd, wval_gate_and D 2 u2 v2 h2 hg hu2 hv2 x]
        · have hg : D.gates[2] = ⟨GateOp.or, [u2, v2]⟩ := by cases h : D.gates[2]; simp_all
          simp [hop2, isAnd, wval_gate_or D 2 u2 v2 h2 hg hu2 hv2 x]
      by_cases hu2lt : u2 < 3
      · rcases hop2 with hop2 | hop2
        · exact maj3_not_fixed_lit maj3 (Or.inl fun _ => rfl) ⟨u2, hu2lt⟩ false
            ⟨false, fun x hx => by rw [hgate2 x]; simp [hop2, isAnd, wval_input D ⟨u2, hu2lt⟩ x, hx]⟩
        · exact maj3_not_fixed_lit maj3 (Or.inl fun _ => rfl) ⟨u2, hu2lt⟩ true
            ⟨true, fun x hx => by rw [hgate2 x]; simp [hop2, isAnd, wval_input D ⟨u2, hu2lt⟩ x, hx]⟩
      · by_cases hv2lt : v2 < 3
        · rcases hop2 with hop2 | hop2
          · exact maj3_not_fixed_lit maj3 (Or.inl fun _ => rfl) ⟨v2, hv2lt⟩ false
              ⟨false, fun x hx => by rw [hgate2 x]; simp [hop2, isAnd, wval_input D ⟨v2, hv2lt⟩ x, hx]⟩
          · exact maj3_not_fixed_lit maj3 (Or.inl fun _ => rfl) ⟨v2, hv2lt⟩ true
              ⟨true, fun x hx => by rw [hgate2 x]; simp [hop2, isAnd, wval_input D ⟨v2, hv2lt⟩ x, hx]⟩
        · by_cases huvEq : u2 = v2
          · subst huvEq
            have hsame : ∀ x, wval D u2 x = maj3 x := fun x => by
              rw [hgate2 x]; rcases hop2 with hop2 | hop2 <;> simp [hop2, isAnd]
            exact strict_not_wire_lt5_maj D hS u2 hu2 (by omega) (Or.inl hsame)
          · have hpair : (∀ x, maj3 x = (wval D 3 x || wval D 4 x)) ∨
                (∀ x, maj3 x = (wval D 3 x && wval D 4 x)) := by
              have hcases : (u2 = 3 ∧ v2 = 4) ∨ (u2 = 4 ∧ v2 = 3) := by omega
              rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hop2 with hop2 | hop2
              · right; intro x; have := hgate2 x; simp [hop2, isAnd] at this; exact this
              · left; intro x; have := hgate2 x; simp [hop2, isAnd] at this; exact this
              · right; intro x; have := hgate2 x; simp [hop2, isAnd] at this; rw [Bool.and_comm] at this; exact this
              · left; intro x; have := hgate2 x; simp [hop2, isAnd] at this; rw [Bool.or_comm] at this; exact this
            obtain ⟨c, hc0⟩ := strict_gate0_indep D h0 (hS 0 h0)
            rcases hS 1 h1 with ⟨hop1, u1, v1, hin1, hu1, hv1⟩ | ⟨hop1, u1, hin1, hu1⟩
            · have hgate1 : ∀ x : Fin 3 → Bool, wval D 4 x =
                  if isAnd D.gates[1].op then wval D u1 x && wval D v1 x else wval D u1 x || wval D v1 x := by
                intro x
                rcases hop1 with hop1 | hop1
                · have hg : D.gates[1] = ⟨GateOp.and, [u1, v1]⟩ := by cases h : D.gates[1]; simp_all
                  simp [hop1, isAnd, wval_gate_and D 1 u1 v1 h1 hg hu1 hv1 x]
                · have hg : D.gates[1] = ⟨GateOp.or, [u1, v1]⟩ := by cases h : D.gates[1]; simp_all
                  simp [hop1, isAnd, wval_gate_or D 1 u1 v1 h1 hg hu1 hv1 x]
              by_cases hcMem : u1 = c.val ∨ v1 = c.val
              · have hother : ∃ w, w < 4 ∧ ∀ x, wval D 4 x =
                    if isAnd D.gates[1].op then wval D w x && x c else wval D w x || x c := by
                  rcases hcMem with rfl | rfl
                  · refine ⟨v1, hv1, fun x => ?_⟩
                    rw [hgate1 x, wval_input D c x]
                    rcases hop1 with hop1 | hop1 <;> simp [hop1, isAnd, Bool.and_comm, Bool.or_comm]
                  · refine ⟨u1, hu1, fun x => ?_⟩
                    rw [hgate1 x, wval_input D c x]
                obtain ⟨w, hw4, hwEq⟩ := hother
                by_cases hw3 : w = 3
                · subst hw3
                  let f1 : Bool → Bool → Bool :=
                    if isAnd D.gates[1].op then (fun p q => p && q) else (fun p q => p || q)
                  rcases hpair with hOr | hAnd
                  · exact maj3_no_factor_g0 c (wval D 3) hc0 (fun p q => p || f1 p q) (fun x => by
                      rw [hOr x, hwEq x]; rcases hop1 with hop1 | hop1 <;> simp [f1, hop1, isAnd])
                  · exact maj3_no_factor_g0 c (wval D 3) hc0 (fun p q => p && f1 p q) (fun x => by
                      rw [hAnd x, hwEq x]; rcases hop1 with hop1 | hop1 <;> simp [f1, hop1, isAnd])
                · have hwlt3 : w < 3 := by omega
                  have ha : ∃ a : Fin 3, a ≠ c ∧ a.val ≠ w := by
                    have : ∀ c : Fin 3, ∀ w < 3, ∃ a : Fin 3, a ≠ c ∧ a.val ≠ w := by decide
                    exact this c w hwlt3
                  obtain ⟨a, hac, haw⟩ := ha
                  have hInd1 : ∀ x y : Fin 3 → Bool, (∀ i, i ≠ a → x i = y i) →
                      wval D 4 x = wval D 4 y := by
                    intro x y hxy
                    rw [hwEq x, hwEq y, wval_input D ⟨w, hwlt3⟩ x, wval_input D ⟨w, hwlt3⟩ y]
                    rw [hxy c hac.symm, hxy ⟨w, hwlt3⟩ (fun h => haw (congrArg Fin.val h).symm)]
                  exact maj3_no_disjoint_op a c hac (wval D 3) (wval D 4) hc0 hInd1 hpair
              · push_neg at hcMem
                have hInd1 : ∀ x y : Fin 3 → Bool, (∀ i, i ≠ c → x i = y i) →
                    wval D 4 x = wval D 4 y := by
                  intro x y hxy
                  have hW : ∀ w < 4, w ≠ c.val → wval D w x = wval D w y := by
                    intro w hw4 hwc
                    by_cases hw3 : w < 3
                    · rw [wval_input D ⟨w, hw3⟩ x, wval_input D ⟨w, hw3⟩ y]
                      exact hxy ⟨w, hw3⟩ (fun h => hwc (congrArg Fin.val h))
                    · have : w = 3 := by omega
                      subst this; exact hc0 x y hxy
                  rw [hgate1 x, hgate1 y, hW u1 hu1 hcMem.1, hW v1 hv1 hcMem.2]
                exact maj3_not_indep maj3 (Or.inl fun _ => rfl) c (fun x y hxy => by
                  rcases hpair with hOr | hAnd
                  · rw [hOr x, hOr y, hc0 x y hxy, hInd1 x y hxy]
                  · rw [hAnd x, hAnd y, hc0 x y hxy, hInd1 x y hxy])
            · have hg1 : D.gates[1] = ⟨GateOp.not, [u1]⟩ := by cases h : D.gates[1]; simp_all
              by_cases hu1lt : u1 < 3
              · rcases hpair with hOr | hAnd
                · exact maj3_not_fixed_lit maj3 (Or.inl fun _ => rfl) ⟨u1, hu1lt⟩ false
                    ⟨true, fun x hx => by
                      rw [hOr x, wval_gate_not D 1 u1 h1 hg1 hu1 x, wval_input D ⟨u1, hu1lt⟩ x, hx]; simp⟩
                · exact maj3_not_fixed_lit maj3 (Or.inl fun _ => rfl) ⟨u1, hu1lt⟩ true
                    ⟨false, fun x hx => by
                      rw [hAnd x, wval_gate_not D 1 u1 h1 hg1 hu1 x, wval_input D ⟨u1, hu1lt⟩ x, hx]; simp⟩
              · have hu1eq : u1 = 3 := by omega
                subst hu1eq
                exact maj3_not_indep maj3 (Or.inl fun _ => rfl) c (fun x y hxy => by
                  rcases hpair with hOr | hAnd
                  · rw [hOr x, hOr y, wval_gate_not D 1 3 h1 hg1 hu1 x, wval_gate_not D 1 3 h1 hg1 hu1 y, hc0 x y hxy]
                  · rw [hAnd x, hAnd y, wval_gate_not D 1 3 h1 hg1 hu1 x, wval_gate_not D 1 3 h1 hg1 hu1 y, hc0 x y hxy])
    · have hg2 : D.gates[2] = ⟨GateOp.not, [u2]⟩ := by cases h : D.gates[2]; simp_all
      have hNeg : ∀ x, wval D u2 x = !(maj3 x) := fun x => by
        have h := hEval5 x
        rw [wval_gate_not D 2 u2 h2 hg2 hu2 x] at h
        rw [← h, Bool.not_not]
      exact strict_not_wire_lt5_maj D hS u2 hu2 (by omega) (Or.inr hNeg)

def targetF6 (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) ||
  (x 1 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5)

def f5 (x : Fin 5 → Bool) : Bool := targetF6 (Fin.snoc x false)
def f4 (x : Fin 4 → Bool) : Bool := f5 (Fin.snoc x false)
def f3 (x : Fin 3 → Bool) : Bool := f4 (Fin.snoc x false)

lemma f3_eq_maj3 : f3 = maj3 := by
  funext x
  revert x
  decide

lemma f6_ess : ∃ x y : Fin 6 → Bool,
    (∀ i : Fin 5, x i.castSucc = y i.castSucc) ∧ targetF6 x ≠ targetF6 y := by
  decide

lemma f6_nonconst : ∃ z₀ z₁ : Fin 5 → Bool,
    targetF6 (Fin.snoc z₀ false) = false ∧ targetF6 (Fin.snoc z₁ false) = true := by
  decide

lemma f5_ess : ∃ x y : Fin 5 → Bool,
    (∀ i : Fin 4, x i.castSucc = y i.castSucc) ∧ f5 x ≠ f5 y := by
  decide

lemma f5_nonconst : ∃ z₀ z₁ : Fin 4 → Bool,
    f5 (Fin.snoc z₀ false) = false ∧ f5 (Fin.snoc z₁ false) = true := by
  decide

lemma f4_ess : ∃ x y : Fin 4 → Bool,
    (∀ i : Fin 3, x i.castSucc = y i.castSucc) ∧ f4 x ≠ f4 y := by
  decide

lemma f4_nonconst : ∃ z₀ z₁ : Fin 3 → Bool,
    f4 (Fin.snoc z₀ false) = false ∧ f4 (Fin.snoc z₁ false) = true := by
  decide

lemma main_proof : ∀ t : ℕ, HasCircuitSize 6 targetF6 t → 7 ≤ t := by
  intro t h6
  by_contra hlt
  have h5 : HasCircuitSize 5 f5 (t - 1) := restrict_size_lt h6 f6_ess f6_nonconst
  have h4 : HasCircuitSize 4 f4 (t - 1 - 1) := restrict_size_lt h5 f5_ess f5_nonconst
  have h3 : HasCircuitSize 3 f3 (t - 1 - 1 - 1) := restrict_size_lt h4 f4_ess f4_nonconst
  rw [f3_eq_maj3] at h3
  obtain ⟨C, hFan, hSz, hEval⟩ := h3
  exact not_hasCircuitSize_maj3_3 ⟨C, hFan, by omega, hEval⟩

end PEqualNP.Outside.L_meta_5483

theorem PEqualNP.Outside.L_meta_5483 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5)) t → 7 ≤ t :=
  PEqualNP.Outside.L_meta_5483.main_proof
