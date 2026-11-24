import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2305

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def normGate (g : Gate) : Gate :=
  { op := g.op, inputs := if g.op.eval [false] = true then g.inputs.take 1 else g.inputs }

def reads09 (g : Gate) : Bool :=
  [(0 : ℕ), 9].any fun i => g.inputs.contains i

def okGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def normOkGate (g : Gate) : Prop :=
  okGate g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

lemma okGate_normGate (g : Gate) (hg : okGate g) : normOkGate (normGate g) := by
  rcases hg with ⟨hop, hlen⟩
  refine ⟨⟨hop, ?_⟩, ?_⟩
  · unfold normGate
    split_ifs
    · simp
    · exact hlen
  · intro hnot
    unfold normGate at hnot ⊢
    have hev : g.op.eval [false] = true := by rw [hnot]; rfl
    simp only [hev, ↓reduceIte]
    simp

lemma stepW_normGate (w : List Bool) (g : Gate) (hg : okGate g) :
    stepW w (normGate g) = stepW w g := by
  rcases hg with ⟨hop, _⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with h | h | h
  · have hev : g.op.eval [false] = false := by rw [h]; rfl
    simp [stepW, normGate, hev]
  · have hev : g.op.eval [false] = false := by rw [h]; rfl
    simp [stepW, normGate, hev]
  · have hev : g.op.eval [false] = true := by rw [h]; rfl
    simp only [stepW, normGate, hev, ↓reduceIte, h, GateOp.eval]
    cases g.inputs with
    | nil => rfl
    | cons a as => rfl

lemma foldl_stepW_map_norm (gs : List Gate) (w : List Bool) (hgs : ∀ g ∈ gs, okGate g) :
    (gs.map normGate).foldl stepW w = gs.foldl stepW w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [stepW_normGate w g (hgs g (List.mem_cons_self ..))]
    exact ih _ (fun a ha => hgs a (List.mem_cons_of_mem g ha))

lemma getD_stepW_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (stepW w g).getD i false = w.getD i false := by
  simp only [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma length_stepW (w : List Bool) (g : Gate) : (stepW w g).length = w.length + 1 := by
  simp [stepW]

lemma length_foldl_stepW (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons, ih, length_stepW]
    omega

lemma getD_foldl_stepW_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (stepW w g) (by rw [length_stepW]; omega), getD_stepW_lt w g i hi]

def evalVal (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl b => b
  | Sum.inr j => w.getD j false

def evalConstOrSimp (nextWire : ℕ) (op : GateOp) (vals : List (Bool ⊕ ℕ)) :
    (Bool ⊕ ℕ) × Option Gate :=
  match op with
  | GateOp.not =>
    match vals with
    | [] => (Sum.inl true, none)
    | Sum.inl b :: _ => (Sum.inl (!b), none)
    | Sum.inr j :: _ => (Sum.inr nextWire, some { op := GateOp.not, inputs := [j] })
  | GateOp.and =>
    match vals with
    | [] => (Sum.inl true, none)
    | [v] => (v, none)
    | [Sum.inl false, _] => (Sum.inl false, none)
    | [_, Sum.inl false] => (Sum.inl false, none)
    | [Sum.inl true, v] => (v, none)
    | [v, Sum.inl true] => (v, none)
    | [Sum.inr j1, Sum.inr j2] => (Sum.inr nextWire, some { op := GateOp.and, inputs := [j1, j2] })
    | _ => (Sum.inl false, none)
  | GateOp.or =>
    match vals with
    | [] => (Sum.inl false, none)
    | [v] => (v, none)
    | [Sum.inl true, _] => (Sum.inl true, none)
    | [_, Sum.inl true] => (Sum.inl true, none)
    | [Sum.inl false, v] => (v, none)
    | [v, Sum.inl false] => (v, none)
    | [Sum.inr j1, Sum.inr j2] => (Sum.inr nextWire, some { op := GateOp.or, inputs := [j1, j2] })
    | _ => (Sum.inl false, none)
  | _ => (Sum.inl false, none)

lemma evalConstOrSimp_none_of_mem_inl (nextWire : ℕ) (op : GateOp) (vals : List (Bool ⊕ ℕ))
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : vals.length ≤ 2) (hnot : op = GateOp.not → vals.length ≤ 1)
    (hinl : ∃ b, Sum.inl b ∈ vals) :
    (evalConstOrSimp nextWire op vals).2 = none := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hinl with ⟨b0, hb0⟩
  rcases hop with rfl | rfl | rfl
  · rcases vals with _ | ⟨x, _ | ⟨y, _ | z⟩⟩
    · cases hb0
    · rfl
    · cases x with
      | inl bx => cases bx <;> cases y with
        | inl by_ => cases by_ <;> rfl
        | inr _ => rfl
      | inr _ => cases y with
        | inl by_ => cases by_ <;> rfl
        | inr _ => simp at hb0
    · simp at hlen
  · rcases vals with _ | ⟨x, _ | ⟨y, _ | z⟩⟩
    · cases hb0
    · rfl
    · cases x with
      | inl bx => cases bx <;> cases y with
        | inl by_ => cases by_ <;> rfl
        | inr _ => rfl
      | inr _ => cases y with
        | inl by_ => cases by_ <;> rfl
        | inr _ => simp at hb0
    · simp at hlen
  · have h1 := hnot rfl
    rcases vals with _ | ⟨x, _ | y⟩
    · cases hb0
    · cases x <;> simp_all [evalConstOrSimp]
    · simp at h1

lemma evalConstOrSimp_and_false (nextWire : ℕ) (vals : List (Bool ⊕ ℕ))
    (hlen : vals.length ≤ 2) (hmem : Sum.inl false ∈ vals) :
    (evalConstOrSimp nextWire GateOp.and vals).1 = Sum.inl false := by
  rcases vals with _ | ⟨x, _ | ⟨y, _ | z⟩⟩
  · cases hmem
  · simp only [List.mem_singleton] at hmem; subst hmem; rfl
  · cases x with
    | inl bx => cases bx <;> cases y with
      | inl by_ => cases by_ <;> simp_all [evalConstOrSimp]
      | inr jy => simp_all [evalConstOrSimp]
    | inr jx => cases y with
      | inl by_ => cases by_ <;> simp_all [evalConstOrSimp]
      | inr jy => simp_all [evalConstOrSimp]
  · simp at hlen

lemma evalConstOrSimp_or_true (nextWire : ℕ) (vals : List (Bool ⊕ ℕ))
    (hlen : vals.length ≤ 2) (hmem : Sum.inl true ∈ vals) :
    (evalConstOrSimp nextWire GateOp.or vals).1 = Sum.inl true := by
  rcases vals with _ | ⟨x, _ | ⟨y, _ | z⟩⟩
  · cases hmem
  · simp only [List.mem_singleton] at hmem; subst hmem; rfl
  · cases x with
    | inl bx => cases bx <;> cases y with
      | inl by_ => cases by_ <;> simp_all [evalConstOrSimp]
      | inr jy => simp_all [evalConstOrSimp]
    | inr jx => cases y with
      | inl by_ => cases by_ <;> simp_all [evalConstOrSimp]
      | inr jy => simp_all [evalConstOrSimp]
  · simp at hlen

lemma evalConstOrSimp_correct (outWires : List Bool) (op : GateOp) (vals : List (Bool ⊕ ℕ))
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : vals.length ≤ 2) (hnot : op = GateOp.not → vals.length ≤ 1)
    (hbound : ∀ j, Sum.inr j ∈ vals → j < outWires.length) :
    match (evalConstOrSimp outWires.length op vals).2 with
    | none =>
      evalVal outWires (evalConstOrSimp outWires.length op vals).1 =
        op.eval (vals.map (evalVal outWires)) ∧
      ∀ j, (evalConstOrSimp outWires.length op vals).1 = Sum.inr j → j < outWires.length
    | some g' =>
      okGate g' ∧
      (evalConstOrSimp outWires.length op vals).1 = Sum.inr outWires.length ∧
      g'.op.eval (g'.inputs.map fun j => outWires.getD j false) =
        op.eval (vals.map (evalVal outWires)) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · rcases vals with _ | ⟨x, _ | ⟨y, _ | z⟩⟩
    · simp [evalConstOrSimp, evalVal, GateOp.eval]
    · simp only [evalConstOrSimp]
      refine ⟨by cases x <;> simp [evalVal, GateOp.eval], ?_⟩
      intro j hj; cases hj
      exact hbound j (List.mem_singleton_self ..)
    · cases x with
      | inl bx => cases bx <;> cases y with
        | inl by_ => cases by_ <;> simp [evalConstOrSimp, evalVal, GateOp.eval]
        | inr jy =>
          simp only [evalConstOrSimp]
          refine ⟨by simp [evalVal, GateOp.eval], ?_⟩
          intro j hj; cases hj <;> exact hbound _ (by simp)
      | inr jx => cases y with
        | inl by_ => cases by_ with
          | false => simp [evalConstOrSimp, evalVal, GateOp.eval]
          | true =>
            simp only [evalConstOrSimp]
            refine ⟨by simp [evalVal, GateOp.eval], ?_⟩
            intro j hj; cases hj <;> exact hbound _ (by simp)
        | inr jy =>
          simp only [evalConstOrSimp]
          refine ⟨⟨by simp, by simp⟩, by trivial, ?_⟩
          simp [evalVal, GateOp.eval]
    · simp at hlen
  · rcases vals with _ | ⟨x, _ | ⟨y, _ | z⟩⟩
    · simp [evalConstOrSimp, evalVal, GateOp.eval]
    · simp only [evalConstOrSimp]
      refine ⟨by cases x <;> simp [evalVal, GateOp.eval], ?_⟩
      intro j hj; cases hj
      exact hbound j (List.mem_singleton_self ..)
    · cases x with
      | inl bx => cases bx <;> cases y with
        | inl by_ => cases by_ <;> simp [evalConstOrSimp, evalVal, GateOp.eval]
        | inr jy =>
          simp only [evalConstOrSimp]
          refine ⟨by simp [evalVal, GateOp.eval], ?_⟩
          intro j hj; cases hj <;> exact hbound _ (by simp)
      | inr jx => cases y with
        | inl by_ => cases by_ with
          | false =>
            simp only [evalConstOrSimp]
            refine ⟨by simp [evalVal, GateOp.eval], ?_⟩
            intro j hj; cases hj <;> exact hbound _ (by simp)
          | true => simp [evalConstOrSimp, evalVal, GateOp.eval]
        | inr jy =>
          simp only [evalConstOrSimp]
          refine ⟨⟨by simp, by simp⟩, by trivial, ?_⟩
          simp [evalVal, GateOp.eval]
    · simp at hlen
  · have h1 := hnot rfl
    rcases vals with _ | ⟨x, _ | y⟩
    · simp [evalConstOrSimp, evalVal, GateOp.eval]
    · cases x with
      | inl bx => simp [evalConstOrSimp, evalVal, GateOp.eval]
      | inr jx =>
        simp only [evalConstOrSimp]
        refine ⟨⟨by simp, by simp⟩, by trivial, ?_⟩
        simp [evalVal, GateOp.eval]
    · simp at h1

def compileStep (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  let vals := g.inputs.map fun i => st.1.getD i (Sum.inl false)
  let p := evalConstOrSimp (8 + st.2.length) g.op vals
  (st.1 ++ [p.1], match p.2 with | none => st.2 | some g' => st.2 ++ [g'])

def initEnv : List (Bool ⊕ ℕ) :=
  [Sum.inl false, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3,
   Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inr 7, Sum.inl true]

def GoodState (y : Fin 8 → Bool) (origWires : List Bool)
    (env : List (Bool ⊕ ℕ)) (out : List Gate) : Prop :=
  (∀ g ∈ out, okGate g) ∧
  env.length = origWires.length ∧
  ∀ i : ℕ, match env.getD i (Sum.inl false) with
    | Sum.inl b => origWires.getD i false = b
    | Sum.inr j => j < (out.foldl stepW (List.ofFn y)).length ∧
        (out.foldl stepW (List.ofFn y)).getD j false = origWires.getD i false

lemma goodState_compileStep (y : Fin 8 → Bool) (origWires : List Bool)
    (env : List (Bool ⊕ ℕ)) (out : List Gate) (g : Gate)
    (hgood : GoodState y origWires env out) (hg : normOkGate g) :
    GoodState y (stepW origWires g) (compileStep (env, out) g).1 (compileStep (env, out) g).2 := by
  rcases hgood with ⟨houtOk, hlen, hmatch⟩
  rcases hg with ⟨⟨hop, hglen⟩, hnot⟩
  set outWires := out.foldl stepW (List.ofFn y)
  have houtLen : outWires.length = 8 + out.length := by
    simp [outWires, length_foldl_stepW]
  set vals := g.inputs.map fun i => env.getD i (Sum.inl false)
  have hvalsLen : vals.length ≤ 2 := by simpa [vals] using hglen
  have hvalsNot : g.op = GateOp.not → vals.length ≤ 1 := fun h => by
    simpa [vals] using hnot h
  have hbound : ∀ j, Sum.inr j ∈ vals → j < outWires.length := by
    intro j hj
    simp only [vals, List.mem_map] at hj
    rcases hj with ⟨i, _, hi⟩
    have hm := hmatch i
    rw [hi] at hm
    exact hm.1
  have hmapEq : g.inputs.map (fun i => origWires.getD i false) = vals.map (evalVal outWires) := by
    simp only [vals, List.map_map]
    apply List.map_congr_left
    intro i _
    change origWires.getD i false = evalVal outWires (env.getD i (Sum.inl false))
    have hm := hmatch i
    cases hdi : env.getD i (Sum.inl false) with
    | inl b =>
      rw [hdi] at hm
      simpa [evalVal] using hm
    | inr j =>
      rw [hdi] at hm
      simpa [evalVal] using hm.2.symm
  have hcorr := evalConstOrSimp_correct outWires g.op vals hop hvalsLen hvalsNot hbound
  simp only [compileStep]
  rw [← houtLen]
  cases hp2 : (evalConstOrSimp outWires.length g.op vals).2 with
  | none =>
    rw [hp2] at hcorr
    rcases hcorr with ⟨heval, hjbound⟩
    refine ⟨houtOk, by simp [hlen, length_stepW], ?_⟩
    intro i
    by_cases hi : i < env.length
    · have hid : (env ++ [(evalConstOrSimp outWires.length g.op vals).1]).getD i (Sum.inl false) =
          env.getD i (Sum.inl false) := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      rw [hid, getD_stepW_lt origWires g i (hlen ▸ hi)]
      exact hmatch i
    · by_cases hieq : i = env.length
      · subst hieq
        have hid : (env ++ [(evalConstOrSimp outWires.length g.op vals).1]).getD env.length (Sum.inl false) =
            (evalConstOrSimp outWires.length g.op vals).1 := by
          simp [List.getD_eq_getElem?_getD]
        have hoid : (stepW origWires g).getD env.length false =
            g.op.eval (g.inputs.map fun i => origWires.getD i false) := by
          simp [stepW, hlen, List.getD_eq_getElem?_getD]
        rw [hid, hoid, hmapEq, ← heval]
        cases hres : (evalConstOrSimp outWires.length g.op vals).1 with
        | inl b => simp [evalVal]
        | inr j => exact ⟨hjbound j hres, by change outWires.getD j false = evalVal outWires (Sum.inr j); rfl⟩
      · have hgt : env.length + 1 ≤ i := by omega
        have hid : (env ++ [(evalConstOrSimp outWires.length g.op vals).1]).getD i (Sum.inl false) =
            Sum.inl false := by
          rw [List.getD_eq_default]
          simp; omega
        have hoid : (stepW origWires g).getD i false = false := by
          rw [List.getD_eq_default]
          simp [length_stepW]; omega
        rw [hid, hoid]
  | some g' =>
    rw [hp2] at hcorr
    rcases hcorr with ⟨hg'ok, hres, heval⟩
    refine ⟨?_, by simp [hlen, length_stepW], ?_⟩
    · intro a ha
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact houtOk a ha
      · exact hg'ok
    · intro i
      have houtWires' : (out ++ [g']).foldl stepW (List.ofFn y) = stepW outWires g' := by
        simp [outWires, List.foldl_append]
      rw [houtWires']
      by_cases hi : i < env.length
      · have hid : (env ++ [(evalConstOrSimp outWires.length g.op vals).1]).getD i (Sum.inl false) =
            env.getD i (Sum.inl false) := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        rw [hid, getD_stepW_lt origWires g i (hlen ▸ hi)]
        have hm := hmatch i
        cases hdi : env.getD i (Sum.inl false) with
        | inl b => rw [hdi] at hm; exact hm
        | inr j =>
          rw [hdi] at hm
          refine ⟨by rw [length_stepW]; omega, ?_⟩
          rw [getD_stepW_lt outWires g' j hm.1]
          exact hm.2
      · by_cases hieq : i = env.length
        · subst hieq
          have hid : (env ++ [(evalConstOrSimp outWires.length g.op vals).1]).getD env.length (Sum.inl false) =
              Sum.inr outWires.length := by
            simp [List.getD_eq_getElem?_getD, hres]
          have hoid : (stepW origWires g).getD env.length false =
              g.op.eval (g.inputs.map fun i => origWires.getD i false) := by
            simp [stepW, hlen, List.getD_eq_getElem?_getD]
          rw [hid]
          refine ⟨by rw [length_stepW]; omega, ?_⟩
          rw [hoid, hmapEq, ← heval]
          simp [stepW, List.getD_eq_getElem?_getD]
        · have hgt : env.length + 1 ≤ i := by omega
          have hid : (env ++ [(evalConstOrSimp outWires.length g.op vals).1]).getD i (Sum.inl false) =
              Sum.inl false := by
            rw [List.getD_eq_default]
            simp; omega
          have hoid : (stepW origWires g).getD i false = false := by
            rw [List.getD_eq_default]
            simp [length_stepW]; omega
          rw [hid, hoid]

lemma goodState_foldl (y : Fin 8 → Bool) (gs : List Gate) (origWires : List Bool)
    (env : List (Bool ⊕ ℕ)) (out : List Gate)
    (hgood : GoodState y origWires env out) (hgs : ∀ g ∈ gs, normOkGate g) :
    GoodState y (gs.foldl stepW origWires)
      (gs.foldl compileStep (env, out)).1 (gs.foldl compileStep (env, out)).2 := by
  induction gs generalizing origWires env out with
  | nil => exact hgood
  | cons g gs ih =>
    simp only [List.foldl_cons]
    exact ih _ _ _
      (goodState_compileStep y origWires env out g hgood (hgs g (List.mem_cons_self ..)))
      (fun a ha => hgs a (List.mem_cons_of_mem g ha))

lemma compileStep_length_le (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    (compileStep st g).2.length ≤ st.2.length + 1 := by
  simp only [compileStep]
  cases (evalConstOrSimp (8 + st.2.length) g.op (g.inputs.map fun i => st.1.getD i (Sum.inl false))).2 with
  | none => simp
  | some _ => simp

lemma compileStep_length_eq_of_mem_inl (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate)
    (hg : normOkGate g) (hinl : ∃ i ∈ g.inputs, ∃ b, st.1.getD i (Sum.inl false) = Sum.inl b) :
    (compileStep st g).2.length = st.2.length := by
  rcases hg with ⟨⟨hop, hglen⟩, hnot⟩
  rcases hinl with ⟨i, hi, b, hb⟩
  have hmem : Sum.inl b ∈ g.inputs.map (fun k => st.1.getD k (Sum.inl false)) :=
    List.mem_map.2 ⟨i, hi, hb⟩
  have hnone := evalConstOrSimp_none_of_mem_inl (8 + st.2.length) g.op
    (g.inputs.map fun k => st.1.getD k (Sum.inl false)) hop
    (by simp [hglen]) (fun h => by simp [hnot h]) ⟨b, hmem⟩
  simp only [compileStep]
  rw [hnone]

lemma compileStep_fst_length (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    (compileStep st g).1.length = st.1.length + 1 := by
  simp [compileStep]

lemma compileStep_fst_getD_lt (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (i : ℕ)
    (hi : i < st.1.length) :
    (compileStep st g).1.getD i (Sum.inl false) = st.1.getD i (Sum.inl false) := by
  simp only [compileStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma compileStep_fst_getD_eq (st : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    (compileStep st g).1.getD st.1.length (Sum.inl false) =
      (evalConstOrSimp (8 + st.2.length) g.op
        (g.inputs.map fun i => st.1.getD i (Sum.inl false))).1 := by
  simp [compileStep, List.getD_eq_getElem?_getD]

lemma foldl_compileStep_fst_length (gs : List Gate) (st : List (Bool ⊕ ℕ) × List Gate) :
    (gs.foldl compileStep st).1.length = st.1.length + gs.length := by
  induction gs generalizing st with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons, ih, compileStep_fst_length]
    omega

lemma foldl_compileStep_fst_getD_lt (gs : List Gate) (st : List (Bool ⊕ ℕ) × List Gate) (i : ℕ)
    (hi : i < st.1.length) :
    (gs.foldl compileStep st).1.getD i (Sum.inl false) = st.1.getD i (Sum.inl false) := by
  induction gs generalizing st with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (compileStep st g) (by rw [compileStep_fst_length]; omega), compileStep_fst_getD_lt st g i hi]

lemma mem_reads09_iff (g : Gate) :
    reads09 g = true ↔ (0 ∈ g.inputs ∨ 9 ∈ g.inputs) := by
  simp [reads09]

lemma foldl_compileStep_length_le (gs : List Gate) (st : List (Bool ⊕ ℕ) × List Gate)
    (hgs : ∀ g ∈ gs, normOkGate g)
    (h0 : st.1.getD 0 (Sum.inl false) = Sum.inl false)
    (h9 : st.1.getD 9 (Sum.inl false) = Sum.inl true)
    (h10 : 10 ≤ st.1.length) :
    (gs.foldl compileStep st).2.length ≤
      st.2.length + (gs.filter fun g => !reads09 g).length := by
  induction gs generalizing st with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.filter_cons]
    have hg := hgs g (List.mem_cons_self ..)
    have hgs' : ∀ a ∈ gs, normOkGate a := fun a ha => hgs a (List.mem_cons_of_mem g ha)
    have h0' : (compileStep st g).1.getD 0 (Sum.inl false) = Sum.inl false := by
      rw [compileStep_fst_getD_lt st g 0 (by omega), h0]
    have h9' : (compileStep st g).1.getD 9 (Sum.inl false) = Sum.inl true := by
      rw [compileStep_fst_getD_lt st g 9 (by omega), h9]
    have h10' : 10 ≤ (compileStep st g).1.length := by
      rw [compileStep_fst_length]; omega
    have hih := ih (compileStep st g) hgs' h0' h9' h10'
    cases hr : reads09 g with
    | true =>
      have hor : 0 ∈ g.inputs ∨ 9 ∈ g.inputs := (mem_reads09_iff g).1 hr
      have hinl : ∃ i ∈ g.inputs, ∃ b, st.1.getD i (Sum.inl false) = Sum.inl b := by
        rcases hor with hi0 | hi9
        · exact ⟨0, hi0, false, h0⟩
        · exact ⟨9, hi9, true, h9⟩
      have heq := compileStep_length_eq_of_mem_inl st g hg hinl
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, heq] at hih ⊢
      exact hih
    | false =>
      have hle := compileStep_length_le st g
      simp only [Bool.not_false, ↓reduceIte, List.length_cons] at hih ⊢
      omega

lemma foldl_compileStep_length_cascade (gs : List Gate) (st : List (Bool ⊕ ℕ) × List Gate)
    (hgs : ∀ g ∈ gs, normOkGate g)
    (h0 : st.1.getD 0 (Sum.inl false) = Sum.inl false)
    (h9 : st.1.getD 9 (Sum.inl false) = Sum.inl true)
    (h10 : 10 ≤ st.1.length)
    (idx : ℕ) (hidxLen : idx < st.1.length) (b : Bool)
    (hidxVal : st.1.getD idx (Sum.inl false) = Sum.inl b)
    (hh : ∃ h ∈ gs, reads09 h = false ∧ idx ∈ h.inputs) :
    (gs.foldl compileStep st).2.length + 1 ≤
      st.2.length + (gs.filter fun g => !reads09 g).length := by
  induction gs generalizing st with
  | nil =>
    rcases hh with ⟨h, hmem, _⟩
    cases hmem
  | cons g gs ih =>
    simp only [List.foldl_cons, List.filter_cons]
    have hg := hgs g (List.mem_cons_self ..)
    have hgs' : ∀ a ∈ gs, normOkGate a := fun a ha => hgs a (List.mem_cons_of_mem g ha)
    have h0' : (compileStep st g).1.getD 0 (Sum.inl false) = Sum.inl false := by
      rw [compileStep_fst_getD_lt st g 0 (by omega), h0]
    have h9' : (compileStep st g).1.getD 9 (Sum.inl false) = Sum.inl true := by
      rw [compileStep_fst_getD_lt st g 9 (by omega), h9]
    have h10' : 10 ≤ (compileStep st g).1.length := by
      rw [compileStep_fst_length]; omega
    have hidxLen' : idx < (compileStep st g).1.length := by
      rw [compileStep_fst_length]; omega
    have hidxVal' : (compileStep st g).1.getD idx (Sum.inl false) = Sum.inl b := by
      rw [compileStep_fst_getD_lt st g idx hidxLen, hidxVal]
    rcases hh with ⟨h, hmem, hnr, hidx⟩
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem_gs
    · have heq := compileStep_length_eq_of_mem_inl st h hg ⟨idx, hidx, b, hidxVal⟩
      have hle := foldl_compileStep_length_le gs (compileStep st h) hgs' h0' h9' h10'
      simp only [hnr, Bool.not_false, ↓reduceIte, List.length_cons, heq] at hle ⊢
      omega
    · cases hr : reads09 g with
      | true =>
        have hor : 0 ∈ g.inputs ∨ 9 ∈ g.inputs := (mem_reads09_iff g).1 hr
        have hinl : ∃ i ∈ g.inputs, ∃ b', st.1.getD i (Sum.inl false) = Sum.inl b' := by
          rcases hor with hi0 | hi9
          · exact ⟨0, hi0, false, h0⟩
          · exact ⟨9, hi9, true, h9⟩
        have heq := compileStep_length_eq_of_mem_inl st g hg hinl
        have hih := ih (compileStep st g) hgs' h0' h9' h10' hidxLen' hidxVal' ⟨h, hmem_gs, hnr, hidx⟩
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, heq] at hih ⊢
        exact hih
      | false =>
        have hle := compileStep_length_le st g
        have hih := ih (compileStep st g) hgs' h0' h9' h10' hidxLen' hidxVal' ⟨h, hmem_gs, hnr, hidx⟩
        simp only [Bool.not_false, ↓reduceIte, List.length_cons] at hih ⊢
        omega

lemma list_ofFn_cons (y : Fin 8 → Bool) :
    List.ofFn (Fin.cons false y) = false :: List.ofFn y := by
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    cases i with
    | zero => simp
    | succ k => simp

lemma goodState_init (y : Fin 8 → Bool) (g0 : Gate)
    (hHead : (stepW (List.ofFn (Fin.cons false y)) g0).getD 9 false = true) :
    GoodState y (stepW (List.ofFn (Fin.cons false y)) g0) initEnv [] := by
  refine ⟨(by simp), (by simp [initEnv, length_stepW]), ?_⟩
  intro i
  have hstep : stepW (List.ofFn (Fin.cons false y)) g0 = false :: List.ofFn y ++ [true] := by
    have hlen : (List.ofFn (Fin.cons false y)).length = 9 := by simp
    simp only [stepW] at hHead ⊢
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.sub_self] at hHead
    simp only [List.getElem?_cons_zero, Option.getD_some] at hHead
    rw [hHead, list_ofFn_cons]
  rw [hstep]
  match i with
  | 0 => simp [initEnv]
  | 1 => simp [initEnv]
  | 2 => simp [initEnv]
  | 3 => simp [initEnv]
  | 4 => simp [initEnv]
  | 5 => simp [initEnv]
  | 6 => simp [initEnv]
  | 7 => simp [initEnv]
  | 8 => simp [initEnv]
  | 9 => simp [initEnv]
  | k + 10 =>
    have hdef1 : initEnv.getD (k + 10) (Sum.inl false) = Sum.inl false := by
      rw [List.getD_eq_default]; simp [initEnv]
    have hdef2 : (false :: List.ofFn y ++ [true]).getD (k + 10) false = false := by
      rw [List.getD_eq_default]; simp
    rw [hdef1, hdef2]

lemma filter_length_add_not (gs : List Gate) :
    (gs.filter reads09).length + (gs.filter fun g => !reads09 g).length = gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.filter_cons, List.length_cons]
    cases reads09 g <;> simp <;> omega

end PEqualNP.Outside.L_meta_2305

theorem PEqualNP.Outside.L_meta_2305 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : List PEqualNP.CircuitLowerBounds.Gate := List.map (fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => { op := x2.op, inputs := if x2.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x2.inputs else x2.inputs : PEqualNP.CircuitLowerBounds.Gate }) (List.drop (1 : ℕ) x1.gates);   have x3 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x4 : ℕ) => x3.inputs.contains x4;   have x4 : ℕ := (List.filter x3 x2).length;   have x5 : Prop := ∃ (x5 : List PEqualNP.CircuitLowerBounds.Gate) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 : List PEqualNP.CircuitLowerBounds.Gate), x2 = x5 ++ x6 :: x7 ∧ (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (0 : ℕ) ∈ x6.inputs ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (9 : ℕ) ∈ x6.inputs) ∧ ∃ x8 ∈ x7, x3 x8 = Bool.false ∧ (10 : ℕ) + x5.length ∈ x8.inputs;   PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x7 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x7)).getD (9 : ℕ) Bool.false = !x7 (0 : Fin (9 : ℕ))) → x1.size ≤ (15 : ℕ) → (3 : ℕ) ≤ x4 ∨ (2 : ℕ) ≤ x4 ∧ x5 → (∃ (x10 : Fin (8 : ℕ) → Bool) (x11 : Fin (8 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 (Fin.cons Bool.false x10) ≠ PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 (Fin.cons Bool.false x11)) → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x11 : Fin (8 : ℕ) → Bool) => PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 (Fin.cons Bool.false x11)) (11 : ℕ) := by
  intro x1
  dsimp only
  intro hFan hHead hSize hCond hNonConst
  let x2 : List PEqualNP.CircuitLowerBounds.Gate :=
    List.map (fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
      { op := g.op, inputs := if g.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) g.inputs else g.inputs : PEqualNP.CircuitLowerBounds.Gate })
      (List.drop (1 : ℕ) x1.gates)
  cases hgates : x1.gates with
  | nil =>
    have hbad := hHead (fun _ => false)
    simp [PEqualNP.CircuitLowerBounds.Circuit.wires, hgates] at hbad
  | cons g0 tail0 =>
    have htail0_norm : tail0.map PEqualNP.Outside.L_meta_2305.normGate = x2 := by
      simp [x2, PEqualNP.Outside.L_meta_2305.normGate, hgates]
    have htail0_ok : ∀ g ∈ tail0, PEqualNP.Outside.L_meta_2305.okGate g := by
      intro g hg
      exact hFan g (by simp [hgates, hg])
    have hx2_ok : ∀ g ∈ x2, PEqualNP.Outside.L_meta_2305.normOkGate g := by
      intro g hg
      rw [← htail0_norm, List.mem_map] at hg
      rcases hg with ⟨g1, hg1, rfl⟩
      exact PEqualNP.Outside.L_meta_2305.okGate_normGate g1 (htail0_ok g1 hg1)
    have hx2_len : x2.length ≤ 14 := by
      have hs : x1.gates.length ≤ 15 := hSize
      rw [hgates, List.length_cons] at hs
      rw [← htail0_norm, List.length_map]
      omega
    set res := x2.foldl PEqualNP.Outside.L_meta_2305.compileStep (PEqualNP.Outside.L_meta_2305.initEnv, [])
    have hres_len : res.2.length ≤ 11 := by
      have h0 : PEqualNP.Outside.L_meta_2305.initEnv.getD 0 (Sum.inl false) = Sum.inl false := rfl
      have h9 : PEqualNP.Outside.L_meta_2305.initEnv.getD 9 (Sum.inl false) = Sum.inl true := rfl
      have hinitLen : PEqualNP.Outside.L_meta_2305.initEnv.length = 10 := rfl
      have hnilLen : ([] : List PEqualNP.CircuitLowerBounds.Gate).length = 0 := rfl
      have h10 : 10 ≤ PEqualNP.Outside.L_meta_2305.initEnv.length := by omega
      have hsum := PEqualNP.Outside.L_meta_2305.filter_length_add_not x2
      rcases hCond with h3 | ⟨h2, hx5⟩
      · have hle := PEqualNP.Outside.L_meta_2305.foldl_compileStep_length_le x2
          (PEqualNP.Outside.L_meta_2305.initEnv, []) hx2_ok h0 h9 h10
        have h3b : 3 ≤ (x2.filter PEqualNP.Outside.L_meta_2305.reads09).length := h3
        change res.2.length ≤ 0 + (x2.filter fun g => !PEqualNP.Outside.L_meta_2305.reads09 g).length at hle
        omega
      · rcases hx5 with ⟨pre, gc, post, hsplit, hgc, h, hhpost, hhnr, hhidx⟩
        have hx2_split : x2 = pre ++ gc :: post := hsplit
        have hpre_ok : ∀ g ∈ pre, PEqualNP.Outside.L_meta_2305.normOkGate g := fun g hg =>
          hx2_ok g (by rw [hx2_split]; simp [hg])
        have hgc_ok : PEqualNP.Outside.L_meta_2305.normOkGate gc :=
          hx2_ok gc (by rw [hx2_split]; simp)
        have hpost_ok : ∀ g ∈ post, PEqualNP.Outside.L_meta_2305.normOkGate g := fun g hg =>
          hx2_ok g (by rw [hx2_split]; simp [hg])
        set stPre := pre.foldl PEqualNP.Outside.L_meta_2305.compileStep (PEqualNP.Outside.L_meta_2305.initEnv, [])
        have hstPre_0 : stPre.1.getD 0 (Sum.inl false) = Sum.inl false := by
          rw [PEqualNP.Outside.L_meta_2305.foldl_compileStep_fst_getD_lt pre _ 0 (by dsimp; rw [hinitLen]; omega), h0]
        have hstPre_9 : stPre.1.getD 9 (Sum.inl false) = Sum.inl true := by
          rw [PEqualNP.Outside.L_meta_2305.foldl_compileStep_fst_getD_lt pre _ 9 (by dsimp; rw [hinitLen]; omega), h9]
        have hstPre_len : stPre.1.length = 10 + pre.length := by
          simp [stPre, PEqualNP.Outside.L_meta_2305.foldl_compileStep_fst_length, hinitLen]
        have hpre_gates := PEqualNP.Outside.L_meta_2305.foldl_compileStep_length_le pre
          (PEqualNP.Outside.L_meta_2305.initEnv, []) hpre_ok h0 h9 h10
        change stPre.2.length ≤ 0 + (pre.filter fun g => !PEqualNP.Outside.L_meta_2305.reads09 g).length at hpre_gates
        have hgc_reads : PEqualNP.Outside.L_meta_2305.reads09 gc = true := by
          rw [PEqualNP.Outside.L_meta_2305.mem_reads09_iff]
          rcases hgc with ⟨_, hi⟩ | ⟨_, hi⟩
          · exact Or.inl hi
          · exact Or.inr hi
        set stGc := PEqualNP.Outside.L_meta_2305.compileStep stPre gc
        have hgc_gates : stGc.2.length = stPre.2.length := by
          apply PEqualNP.Outside.L_meta_2305.compileStep_length_eq_of_mem_inl stPre gc hgc_ok
          rcases hgc with ⟨_, hi⟩ | ⟨_, hi⟩
          · exact ⟨0, hi, false, hstPre_0⟩
          · exact ⟨9, hi, true, hstPre_9⟩
        have hstGc_0 : stGc.1.getD 0 (Sum.inl false) = Sum.inl false := by
          rw [PEqualNP.Outside.L_meta_2305.compileStep_fst_getD_lt stPre gc 0 (by omega), hstPre_0]
        have hstGc_9 : stGc.1.getD 9 (Sum.inl false) = Sum.inl true := by
          rw [PEqualNP.Outside.L_meta_2305.compileStep_fst_getD_lt stPre gc 9 (by omega), hstPre_9]
        have hstGc_len : stGc.1.length = 10 + pre.length + 1 := by
          rw [PEqualNP.Outside.L_meta_2305.compileStep_fst_length, hstPre_len]
        have hgc_res : ∃ b : Bool, stGc.1.getD (10 + pre.length) (Sum.inl false) = Sum.inl b := by
          have heq := PEqualNP.Outside.L_meta_2305.compileStep_fst_getD_eq stPre gc
          rw [hstPre_len] at heq
          rw [heq]
          rcases hgc with ⟨hop, hi0⟩ | ⟨hop, hi9⟩
          · refine ⟨false, ?_⟩
            rw [hop]
            apply PEqualNP.Outside.L_meta_2305.evalConstOrSimp_and_false
            · simp [hgc_ok.1.2]
            · exact List.mem_map.2 ⟨0, hi0, hstPre_0⟩
          · refine ⟨true, ?_⟩
            rw [hop]
            apply PEqualNP.Outside.L_meta_2305.evalConstOrSimp_or_true
            · simp [hgc_ok.1.2]
            · exact List.mem_map.2 ⟨9, hi9, hstPre_9⟩
        rcases hgc_res with ⟨bc, hbc⟩
        have hpost_gates := PEqualNP.Outside.L_meta_2305.foldl_compileStep_length_cascade post stGc
          hpost_ok hstGc_0 hstGc_9 (by omega) (10 + pre.length) (by omega) bc hbc
          ⟨h, hhpost, hhnr, hhidx⟩
        have hres_eq : res = post.foldl PEqualNP.Outside.L_meta_2305.compileStep stGc := by
          simp [res, hx2_split, List.foldl_append, List.foldl_cons, stGc, stPre]
        rw [← hres_eq] at hpost_gates
        have hfilt_split : (x2.filter fun g => !PEqualNP.Outside.L_meta_2305.reads09 g).length =
            (pre.filter fun g => !PEqualNP.Outside.L_meta_2305.reads09 g).length +
            (post.filter fun g => !PEqualNP.Outside.L_meta_2305.reads09 g).length := by
          rw [hx2_split, List.filter_append, List.filter_cons]
          simp [hgc_reads]
        have h2b : 2 ≤ (x2.filter PEqualNP.Outside.L_meta_2305.reads09).length := h2
        omega
    have hgood_final : ∀ y : Fin 8 → Bool,
        PEqualNP.Outside.L_meta_2305.GoodState y
          (x1.wires (List.ofFn (Fin.cons false y))) res.1 res.2 := by
      intro y
      have hw : x1.wires (List.ofFn (Fin.cons false y)) =
          tail0.foldl PEqualNP.Outside.L_meta_2305.stepW
            (PEqualNP.Outside.L_meta_2305.stepW (List.ofFn (Fin.cons false y)) g0) := by
        change x1.gates.foldl PEqualNP.Outside.L_meta_2305.stepW (List.ofFn (Fin.cons false y)) = _
        rw [hgates, List.foldl_cons]
      have hHeadY : (PEqualNP.Outside.L_meta_2305.stepW (List.ofFn (Fin.cons false y)) g0).getD 9 false = true := by
        have hhy := hHead (Fin.cons false y)
        have hlen : (PEqualNP.Outside.L_meta_2305.stepW (List.ofFn (Fin.cons false y)) g0).length = 10 := by
          simp [PEqualNP.Outside.L_meta_2305.length_stepW]
        rw [hw, PEqualNP.Outside.L_meta_2305.getD_foldl_stepW_lt tail0 _ 9 (by omega)] at hhy
        simpa using hhy
      have hw_eq : x1.wires (List.ofFn (Fin.cons false y)) =
          x2.foldl PEqualNP.Outside.L_meta_2305.stepW
            (PEqualNP.Outside.L_meta_2305.stepW (List.ofFn (Fin.cons false y)) g0) := by
        rw [hw, ← htail0_norm, PEqualNP.Outside.L_meta_2305.foldl_stepW_map_norm tail0 _ htail0_ok]
      rw [hw_eq]
      exact PEqualNP.Outside.L_meta_2305.goodState_foldl y x2 _
        PEqualNP.Outside.L_meta_2305.initEnv []
        (PEqualNP.Outside.L_meta_2305.goodState_init y g0 hHeadY) hx2_ok
    cases hout : res.1.getD x1.output (Sum.inl false) with
    | inl b =>
      exfalso
      rcases hNonConst with ⟨y1, y2, hne⟩
      have h1 := (hgood_final y1).2.2 x1.output
      have h2 := (hgood_final y2).2.2 x1.output
      rw [hout] at h1 h2
      apply hne
      change (x1.wires (List.ofFn (Fin.cons false y1))).getD x1.output false =
        (x1.wires (List.ofFn (Fin.cons false y2))).getD x1.output false
      rw [h1, h2]
    | inr j =>
      refine ⟨{ gates := res.2, output := j }, ?_, hres_len, ?_⟩
      · intro g hg
        exact (hgood_final (fun _ => false)).1 g hg
      · intro y
        have hm := (hgood_final y).2.2 x1.output
        rw [hout] at hm
        exact hm.2
