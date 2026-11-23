import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_669_aux

open PEqualNP.CircuitLowerBounds

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wiresOf (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl stepWire x

lemma eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wiresOf gs x).getD o false := rfl

lemma wiresOf_nil (x : List Bool) : wiresOf [] x = x := rfl

lemma wiresOf_append_singleton (gs : List Gate) (g : Gate) (x : List Bool) :
    wiresOf (gs ++ [g]) x = stepWire (wiresOf gs x) g := by
  simp [wiresOf, List.foldl_append]

lemma wiresOf_length (gs : List Gate) (x : List Bool) :
    (wiresOf gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wiresOf]
  | append_singleton gs g ih =>
    rw [wiresOf_append_singleton, stepWire, List.length_append, List.length_singleton, ih,
      List.length_append, List.length_singleton, Nat.add_assoc]

lemma getD_append_lt {α : Type} (l : List α) (v d : α) {i : ℕ} (h : i < l.length) :
    (l ++ [v]).getD i d = l.getD i d := by
  have h1 : i < (l ++ [v]).length := by
    rw [List.length_append, List.length_singleton]
    omega
  rw [List.getD_eq_getElem l d h, List.getD_eq_getElem (l ++ [v]) d h1,
    List.getElem_append_left h]

lemma getD_append_eq {α : Type} (l : List α) (v d : α) :
    (l ++ [v]).getD l.length d = v := by
  have h1 : l.length < (l ++ [v]).length := by
    rw [List.length_append, List.length_singleton]
    omega
  rw [List.getD_eq_getElem (l ++ [v]) d h1, List.getElem_append_right (Nat.le_refl _)]
  simp

lemma getD_append_gt {α : Type} (l : List α) (v d : α) {i : ℕ} (h : l.length < i) :
    (l ++ [v]).getD i d = d := by
  have h1 : (l ++ [v]).length ≤ i := by
    rw [List.length_append, List.length_singleton]
    omega
  exact List.getD_eq_default (l ++ [v]) d h1

lemma getD_ofFn_lt {n : ℕ} (f : Fin n → Bool) {i : ℕ} (h : i < n) :
    (List.ofFn f).getD i false = f ⟨i, h⟩ := by
  have h1 : i < (List.ofFn f).length := by
    rw [List.length_ofFn]
    exact h
  rw [List.getD_eq_getElem (List.ofFn f) false h1, List.getElem_ofFn]

lemma getD_ofFn_ge {n : ℕ} (f : Fin n → Bool) {i : ℕ} (h : n ≤ i) :
    (List.ofFn f).getD i false = false := by
  have h1 : (List.ofFn f).length ≤ i := by
    rw [List.length_ofFn]
    exact h
  exact List.getD_eq_default (List.ofFn f) false h1

lemma eval_and_nil : GateOp.and.eval [] = true := rfl
lemma eval_or_nil : GateOp.or.eval [] = false := rfl
lemma eval_and_one (a : Bool) : GateOp.and.eval [a] = a := by cases a <;> rfl
lemma eval_or_one (a : Bool) : GateOp.or.eval [a] = a := by cases a <;> rfl
lemma eval_and_two (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by cases a <;> cases b <;> rfl
lemma eval_or_two (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by cases a <;> cases b <;> rfl

def fixInput (n : ℕ) (T Z : Finset (Fin n)) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => if i ∈ T then true else if i ∈ Z then false else x i

def ValidGate (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def WireRel (n : ℕ) (T Z : Finset (Fin n)) (gs gs' : List Gate) (m : ℕ → Bool ⊕ ℕ) : Prop :=
  (∀ g ∈ gs', ValidGate g) ∧
  gs'.length ≤ gs.length ∧
  (∀ i : ℕ, n + gs.length ≤ i → m i = Sum.inl false) ∧
  (∀ i : ℕ, match m i with
    | Sum.inl b =>
        ∀ x : Fin n → Bool, (wiresOf gs (List.ofFn (fixInput n T Z x))).getD i false = b
    | Sum.inr j =>
        j < n + gs'.length ∧
        ∀ x : Fin n → Bool,
          (wiresOf gs (List.ofFn (fixInput n T Z x))).getD i false =
          (wiresOf gs' (List.ofFn x)).getD j false)

lemma base_wireRel (n : ℕ) (T Z : Finset (Fin n)) :
    ∃ m : ℕ → Bool ⊕ ℕ, WireRel n T Z [] [] m := by
  let m : ℕ → Bool ⊕ ℕ := fun i =>
    if h : i < n then
      if ⟨i, h⟩ ∈ T then Sum.inl true
      else if ⟨i, h⟩ ∈ Z then Sum.inl false
      else Sum.inr i
    else Sum.inl false
  refine ⟨m, ?_, ?_, ?_, ?_⟩
  · intro g hg
    cases hg
  · exact Nat.le_refl 0
  · intro i hi
    have hn : ¬ i < n := by omega
    simp [m, hn]
  · intro i
    by_cases h : i < n
    · by_cases hT : (⟨i, h⟩ : Fin n) ∈ T
      · simp only [m, h, hT, ↓reduceDIte, ↓reduceIte]
        intro x
        rw [wiresOf_nil, getD_ofFn_lt _ h]
        simp [fixInput, hT]
      · by_cases hZ : (⟨i, h⟩ : Fin n) ∈ Z
        · simp only [m, h, hT, hZ, ↓reduceDIte, ↓reduceIte]
          intro x
          rw [wiresOf_nil, getD_ofFn_lt _ h]
          simp [fixInput, hT, hZ]
        · simp only [m, h, hT, hZ, ↓reduceDIte, ↓reduceIte]
          refine ⟨by omega, ?_⟩
          intro x
          rw [wiresOf_nil, wiresOf_nil, getD_ofFn_lt _ h, getD_ofFn_lt _ h]
          simp [fixInput, hT, hZ]
    · simp only [m, h, ↓reduceDIte]
      intro x
      rw [wiresOf_nil, getD_ofFn_ge _ (by omega)]

lemma extend_same (n : ℕ) (T Z : Finset (Fin n)) (gs gs' : List Gate) (g : Gate)
    (m : ℕ → Bool ⊕ ℕ) (hrel : WireRel n T Z gs gs' m) (res : Bool ⊕ ℕ)
    (hres : match res with
      | Sum.inl b =>
          ∀ x : Fin n → Bool,
            g.op.eval (g.inputs.map fun k =>
              (wiresOf gs (List.ofFn (fixInput n T Z x))).getD k false) = b
      | Sum.inr j =>
          j < n + gs'.length ∧
          ∀ x : Fin n → Bool,
            g.op.eval (g.inputs.map fun k =>
              (wiresOf gs (List.ofFn (fixInput n T Z x))).getD k false) =
            (wiresOf gs' (List.ofFn x)).getD j false) :
    WireRel n T Z (gs ++ [g]) gs' (fun i => if i = n + gs.length then res else m i) := by
  rcases hrel with ⟨hvalid, hlen, hoob, hsem⟩
  refine ⟨hvalid, ?_, ?_, ?_⟩
  · rw [List.length_append, List.length_singleton]
    omega
  · intro i hi
    rw [List.length_append, List.length_singleton] at hi
    have hne : i ≠ n + gs.length := by omega
    simp only [hne, ↓reduceIte]
    exact hoob i (by omega)
  · intro i
    rcases Nat.lt_trichotomy i (n + gs.length) with hlt | heq | hgt
    · have hne : i ≠ n + gs.length := by omega
      simp only [hne, ↓reduceIte]
      have hi := hsem i
      cases hm : m i with
      | inl b =>
        rw [hm] at hi
        intro x
        rw [wiresOf_append_singleton, stepWire, getD_append_lt]
        · exact hi x
        · rw [wiresOf_length, List.length_ofFn]
          exact hlt
      | inr j =>
        rw [hm] at hi
        refine ⟨hi.1, ?_⟩
        intro x
        rw [wiresOf_append_singleton, stepWire, getD_append_lt]
        · exact hi.2 x
        · rw [wiresOf_length, List.length_ofFn]
          exact hlt
    · rw [heq]
      simp only [↓reduceIte]
      cases hres_eq : res with
      | inl b =>
        rw [hres_eq] at hres
        intro x
        rw [wiresOf_append_singleton, stepWire]
        have hlenw : (wiresOf gs (List.ofFn (fixInput n T Z x))).length = n + gs.length := by
          rw [wiresOf_length, List.length_ofFn]
        rw [← hlenw, getD_append_eq]
        exact hres x
      | inr j =>
        rw [hres_eq] at hres
        refine ⟨hres.1, ?_⟩
        intro x
        rw [wiresOf_append_singleton, stepWire]
        have hlenw : (wiresOf gs (List.ofFn (fixInput n T Z x))).length = n + gs.length := by
          rw [wiresOf_length, List.length_ofFn]
        rw [← hlenw, getD_append_eq]
        exact hres.2 x
    · have hne : i ≠ n + gs.length := by omega
      simp only [hne, ↓reduceIte]
      rw [hoob i (by omega)]
      intro x
      rw [wiresOf_append_singleton, stepWire, getD_append_gt]
      rw [wiresOf_length, List.length_ofFn]
      exact hgt

lemma extend_new (n : ℕ) (T Z : Finset (Fin n)) (gs gs' : List Gate) (g g' : Gate)
    (m : ℕ → Bool ⊕ ℕ) (hrel : WireRel n T Z gs gs' m) (hg' : ValidGate g')
    (hval : ∀ x : Fin n → Bool,
      g.op.eval (g.inputs.map fun k =>
        (wiresOf gs (List.ofFn (fixInput n T Z x))).getD k false) =
      g'.op.eval (g'.inputs.map fun k =>
        (wiresOf gs' (List.ofFn x)).getD k false)) :
    WireRel n T Z (gs ++ [g]) (gs' ++ [g'])
      (fun i => if i = n + gs.length then Sum.inr (n + gs'.length) else m i) := by
  rcases hrel with ⟨hvalid, hlen, hoob, hsem⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h hh
    rcases List.mem_append.mp hh with hh1 | hh2
    · exact hvalid h hh1
    · rw [List.mem_singleton] at hh2
      rw [hh2]
      exact hg'
  · rw [List.length_append, List.length_singleton, List.length_append, List.length_singleton]
    omega
  · intro i hi
    rw [List.length_append, List.length_singleton] at hi
    have hne : i ≠ n + gs.length := by omega
    simp only [hne, ↓reduceIte]
    exact hoob i (by omega)
  · intro i
    rcases Nat.lt_trichotomy i (n + gs.length) with hlt | heq | hgt
    · have hne : i ≠ n + gs.length := by omega
      simp only [hne, ↓reduceIte]
      have hi := hsem i
      cases hm : m i with
      | inl b =>
        rw [hm] at hi
        intro x
        rw [wiresOf_append_singleton, stepWire, getD_append_lt]
        · exact hi x
        · rw [wiresOf_length, List.length_ofFn]
          exact hlt
      | inr j =>
        rw [hm] at hi
        refine ⟨?_, ?_⟩
        · rw [List.length_append, List.length_singleton]
          omega
        · intro x
          rw [wiresOf_append_singleton, stepWire, getD_append_lt]
          · rw [wiresOf_append_singleton, stepWire, getD_append_lt]
            · exact hi.2 x
            · rw [wiresOf_length, List.length_ofFn]
              exact hi.1
          · rw [wiresOf_length, List.length_ofFn]
            exact hlt
    · rw [heq]
      simp only [↓reduceIte]
      refine ⟨?_, ?_⟩
      · rw [List.length_append, List.length_singleton]
        omega
      · intro x
        rw [wiresOf_append_singleton, stepWire, wiresOf_append_singleton, stepWire]
        have hlen1 : (wiresOf gs (List.ofFn (fixInput n T Z x))).length = n + gs.length := by
          rw [wiresOf_length, List.length_ofFn]
        have hlen2 : (wiresOf gs' (List.ofFn x)).length = n + gs'.length := by
          rw [wiresOf_length, List.length_ofFn]
        rw [← hlen1, getD_append_eq, ← hlen2, getD_append_eq]
        exact hval x
    · have hne : i ≠ n + gs.length := by omega
      simp only [hne, ↓reduceIte]
      rw [hoob i (by omega)]
      intro x
      rw [wiresOf_append_singleton, stepWire, getD_append_gt]
      rw [wiresOf_length, List.length_ofFn]
      exact hgt

lemma step_wireRel (n : ℕ) (T Z : Finset (Fin n)) (gs gs' : List Gate) (g : Gate)
    (m : ℕ → Bool ⊕ ℕ) (hrel : WireRel n T Z gs gs' m)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ (gs'' : List Gate) (m' : ℕ → Bool ⊕ ℕ), WireRel n T Z (gs ++ [g]) gs'' m' := by
  rcases g with ⟨op, inputs⟩
  rcases hg with ⟨hop, hlen⟩
  dsimp only at hop hlen
  match inputs with
  | [] =>
    rcases hop with rfl | rfl
    · refine ⟨gs', _, extend_same n T Z gs gs' ⟨GateOp.and, []⟩ m hrel (Sum.inl true) ?_⟩
      intro x
      rfl
    · refine ⟨gs', _, extend_same n T Z gs gs' ⟨GateOp.or, []⟩ m hrel (Sum.inl false) ?_⟩
      intro x
      rfl
  | [a] =>
    have ha := hrel.2.2.2 a
    rcases hop with rfl | rfl
    · refine ⟨gs', _, extend_same n T Z gs gs' ⟨GateOp.and, [a]⟩ m hrel (m a) ?_⟩
      cases hma : m a with
      | inl b =>
        rw [hma] at ha
        intro x
        simp only [List.map, eval_and_one, ha x]
      | inr j =>
        rw [hma] at ha
        refine ⟨ha.1, ?_⟩
        intro x
        simp only [List.map, eval_and_one, ha.2 x]
    · refine ⟨gs', _, extend_same n T Z gs gs' ⟨GateOp.or, [a]⟩ m hrel (m a) ?_⟩
      cases hma : m a with
      | inl b =>
        rw [hma] at ha
        intro x
        simp only [List.map, eval_or_one, ha x]
      | inr j =>
        rw [hma] at ha
        refine ⟨ha.1, ?_⟩
        intro x
        simp only [List.map, eval_or_one, ha.2 x]
  | [a, b] =>
    have ha := hrel.2.2.2 a
    have hb := hrel.2.2.2 b
    rcases hop with rfl | rfl
    · cases hma : m a with
      | inl ba =>
        rw [hma] at ha
        cases ba
        · refine ⟨gs', _, extend_same n T Z gs gs' ⟨GateOp.and, [a, b]⟩ m hrel (Sum.inl false) ?_⟩
          intro x
          simp only [List.map, eval_and_two, ha x, Bool.false_and]
        · refine ⟨gs', _, extend_same n T Z gs gs' ⟨GateOp.and, [a, b]⟩ m hrel (m b) ?_⟩
          cases hmb : m b with
          | inl bb =>
            rw [hmb] at hb
            intro x
            simp only [List.map, eval_and_two, ha x, hb x, Bool.true_and]
          | inr jb =>
            rw [hmb] at hb
            refine ⟨hb.1, ?_⟩
            intro x
            simp only [List.map, eval_and_two, ha x, hb.2 x, Bool.true_and]
      | inr ja =>
        rw [hma] at ha
        cases hmb : m b with
        | inl bb =>
          rw [hmb] at hb
          cases bb
          · refine ⟨gs', _, extend_same n T Z gs gs' ⟨GateOp.and, [a, b]⟩ m hrel (Sum.inl false) ?_⟩
            intro x
            simp only [List.map, eval_and_two, hb x, Bool.and_false]
          · refine ⟨gs', _, extend_same n T Z gs gs' ⟨GateOp.and, [a, b]⟩ m hrel (Sum.inr ja) ?_⟩
            refine ⟨ha.1, ?_⟩
            intro x
            simp only [List.map, eval_and_two, ha.2 x, hb x, Bool.and_true]
        | inr jb =>
          rw [hmb] at hb
          refine ⟨gs' ++ [⟨GateOp.and, [ja, jb]⟩], _,
            extend_new n T Z gs gs' ⟨GateOp.and, [a, b]⟩ ⟨GateOp.and, [ja, jb]⟩ m hrel
              ⟨Or.inl rfl, rfl⟩ ?_⟩
          intro x
          simp only [List.map, eval_and_two, ha.2 x, hb.2 x]
    · cases hma : m a with
      | inl ba =>
        rw [hma] at ha
        cases ba
        · refine ⟨gs', _, extend_same n T Z gs gs' ⟨GateOp.or, [a, b]⟩ m hrel (m b) ?_⟩
          cases hmb : m b with
          | inl bb =>
            rw [hmb] at hb
            intro x
            simp only [List.map, eval_or_two, ha x, hb x, Bool.false_or]
          | inr jb =>
            rw [hmb] at hb
            refine ⟨hb.1, ?_⟩
            intro x
            simp only [List.map, eval_or_two, ha x, hb.2 x, Bool.false_or]
        · refine ⟨gs', _, extend_same n T Z gs gs' ⟨GateOp.or, [a, b]⟩ m hrel (Sum.inl true) ?_⟩
          intro x
          simp only [List.map, eval_or_two, ha x, Bool.true_or]
      | inr ja =>
        rw [hma] at ha
        cases hmb : m b with
        | inl bb =>
          rw [hmb] at hb
          cases bb
          · refine ⟨gs', _, extend_same n T Z gs gs' ⟨GateOp.or, [a, b]⟩ m hrel (Sum.inr ja) ?_⟩
            refine ⟨ha.1, ?_⟩
            intro x
            simp only [List.map, eval_or_two, ha.2 x, hb x, Bool.or_false]
          · refine ⟨gs', _, extend_same n T Z gs gs' ⟨GateOp.or, [a, b]⟩ m hrel (Sum.inl true) ?_⟩
            intro x
            simp only [List.map, eval_or_two, hb x, Bool.or_true]
        | inr jb =>
          rw [hmb] at hb
          refine ⟨gs' ++ [⟨GateOp.or, [ja, jb]⟩], _,
            extend_new n T Z gs gs' ⟨GateOp.or, [a, b]⟩ ⟨GateOp.or, [ja, jb]⟩ m hrel
              ⟨Or.inr rfl, rfl⟩ ?_⟩
          intro x
          simp only [List.map, eval_or_two, ha.2 x, hb.2 x]
  | _ :: _ :: _ :: _ =>
    simp at hlen

lemma build_wireRel (n : ℕ) (T Z : Finset (Fin n)) (gates : List Gate)
    (hgates : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ (gates' : List Gate) (m : ℕ → Bool ⊕ ℕ), WireRel n T Z gates gates' m := by
  induction gates using List.reverseRecOn with
  | nil =>
    rcases base_wireRel n T Z with ⟨m, hm⟩
    exact ⟨[], m, hm⟩
  | append_singleton gs g ih =>
    have hgs : ∀ h ∈ gs, (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2 :=
      fun h hh => hgates h (List.mem_append_left [g] hh)
    have hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
      hgates g (List.mem_append_right gs (List.mem_singleton.mpr rfl))
    rcases ih hgs with ⟨gs', m, hrel⟩
    exact step_wireRel n T Z gs gs' g m hrel hg

lemma main :
    ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)),
      (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
      ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ),
        (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧
        gates'.length ≤ gates.length ∧
        ∀ o : ℕ,
          (∃ x y : Fin n → Bool,
            PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠
            PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) →
          ∀ x : Fin n → Bool,
            PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) =
            PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) := by
  intro n gates T Z hgates
  rcases build_wireRel n T Z gates hgates with ⟨gates', m, hvalid, hlen, _, hsem⟩
  let r : ℕ → ℕ := fun o => match m o with | Sum.inl _ => 0 | Sum.inr j => j
  refine ⟨gates', r, hvalid, hlen, ?_⟩
  intro o hnc x
  have ho := hsem o
  cases hmo : m o with
  | inl b =>
    rw [hmo] at ho
    rcases hnc with ⟨x1, x2, hne⟩
    exfalso
    apply hne
    rw [eval_eq, eval_eq]
    have h1 := ho x1
    have h2 := ho x2
    exact h1.trans h2.symm
  | inr j =>
    rw [hmo] at ho
    have hro : r o = j := by simp [r, hmo]
    rw [hro, eval_eq, eval_eq]
    exact (ho.2 x).symm

end PEqualNP.Outside.L_meta_669_aux

theorem PEqualNP.Outside.L_meta_669 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) := by
  exact PEqualNP.Outside.L_meta_669_aux.main
