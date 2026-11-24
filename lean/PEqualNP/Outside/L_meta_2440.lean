import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2440

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wire {n : ℕ} (σ : Fin n → Fin n) (i : ℕ) : ℕ :=
  if hi : i < n then (σ ⟨i, hi⟩).val else i

def gate {n : ℕ} (σ : Fin n → Fin n) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wire σ)⟩

def circuit {n : ℕ} (σ : Fin n → Fin n) (C : Circuit) : Circuit :=
  ⟨C.gates.map (gate σ), wire σ C.output⟩

lemma mono {n : ℕ} (σ : Fin n → Fin n) {C : Circuit} (hC : FanInTwo C) :
    FanInTwo (circuit σ C) := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  rcases hC g' hg' with ⟨ho, hn⟩
  exact ⟨ho, by simpa [gate] using hn⟩

lemma size {n : ℕ} (σ : Fin n → Fin n) (C : Circuit) :
    (circuit σ C).size = C.size := by simp [circuit, Circuit.size]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma read_append {n : ℕ} (σ : Fin n → Fin n) {u v : List Bool}
    (he : u.length = v.length) (hn : n ≤ u.length)
    (hr : ∀ i, u.getD (wire σ i) false = v.getD i false)
    (b : Bool) : ∀ i, (u ++ [b]).getD (wire σ i) false = (v ++ [b]).getD i false := by
  intro i
  by_cases hi : i < n
  · have hw : wire σ i < u.length := lt_of_lt_of_le (by simp [wire, hi]) hn
    have hv : i < v.length := by omega
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left hw,
      List.getElem?_append_left hv] using hr i
  · rw [show wire σ i = i by simp [wire, hi]]
    by_cases hlt : i < u.length
    · have hlt' : i < v.length := by omega
      have hh := hr i
      rw [show wire σ i = i by simp [wire, hi]] at hh
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
        List.getElem?_append_left hlt'] using hh
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : u.length ≤ i),
        List.getElem?_append_right (by omega : v.length ≤ i), he]

lemma fold_read {n : ℕ} (σ : Fin n → Fin n) (gs : List Gate) (u v : List Bool)
    (he : u.length = v.length) (hn : n ≤ u.length)
    (hr : ∀ i, u.getD (wire σ i) false = v.getD i false) :
    ∀ i, ((gs.map (gate σ)).foldl step u).getD (wire σ i) false =
      (gs.foldl step v).getD i false := by
  induction gs generalizing u v with
  | nil => exact hr
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hx : (g.inputs.map (wire σ)).map (fun i => u.getD i false) =
        g.inputs.map (fun i => v.getD i false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => hr i)
    apply ih
    · simp [step, he]
    · simp [step]
      omega
    · unfold step gate
      simp only
      rw [hx]
      exact read_append σ he hn hr _

lemma wires_read {n : ℕ} (σ : Fin n → Fin n) (C : Circuit) (x : Fin n → Bool)
    (i : ℕ) : ((circuit σ C).wires (List.ofFn x)).getD (wire σ i) false =
      (C.wires (List.ofFn (x ∘ σ))).getD i false := by
  have hr : ∀ i, (List.ofFn x).getD (wire σ i) false = (List.ofFn (x ∘ σ)).getD i false := by
    intro i
    by_cases h : i < n <;> simp [wire, h, List.getD_eq_getElem?_getD]
  exact fold_read σ C.gates _ _ (by simp) (by simp) hr i

def target (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
  (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def a : Fin 9 → Fin 9 := ![0, 5, 8, 3, 4, 1, 7, 6, 2]
def b : Fin 9 → Fin 9 := ![1, 2, 3, 8, 6, 0, 7, 4, 5]

lemma a_invariant (x : Fin 9 → Bool) : target (x ∘ a) = target x := by
  dsimp [target, a, Function.comp_def]
  ac_rfl

lemma b_invariant (x : Fin 9 → Bool) : target (x ∘ b) = target x := by
  dsimp [target, b, Function.comp_def]
  ac_rfl

def move (word : List Bool) (i : Fin 9) : Fin 9 :=
  word.foldl (fun j bit => if bit then b j else a j) i

lemma move_invariant (word : List Bool) (x : Fin 9 → Bool) : target (x ∘ move word) = target x := by
  induction word generalizing x with
  | nil => rfl
  | cons bit rest ih =>
    cases bit with
    | false => exact (a_invariant (x ∘ move rest)).trans (ih x)
    | true => exact (b_invariant (x ∘ move rest)).trans (ih x)

def routes : List (List Bool) :=
  (List.range 5).flatMap fun n => (List.range (2 ^ n)).map fun m => (List.range n).map m.testBit

def representatives : List (Fin 9 × Fin 9) := [(0,1), (0,2), (0,3), (0,4), (0,6), (4,6)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 8000000 in
lemma vertexRoutes :
    ∀ u : Fin 9, routes.any (fun w => decide (move w u ∈ ([0,4] : List (Fin 9)))) = true := by
  decide

set_option maxRecDepth 24000 in
set_option maxHeartbeats 8000000 in
lemma pairRoutes :
    ∀ u v : Fin 9, u = v ∨ routes.any (fun w =>
      decide ((move w u, move w v) ∈ representatives ∨
        (move w v, move w u) ∈ representatives)) = true := by
  decide

lemma movedEval (D : Circuit) (hD : circuitFun 9 D = target) (word : List Bool) :
    circuitFun 9 (circuit (move word) D) = target := by
  funext x
  have he := wires_read (move word) D x D.output
  change circuitFun 9 (circuit (move word) D) x = circuitFun 9 D (x ∘ move word) at he
  rw [he, hD]
  exact move_invariant word x

lemma movedFirst (D : Circuit) (word : List Bool) (x : Fin 9 → Bool) :
    ((circuit (move word) D).wires (List.ofFn x)).getD 9 false =
      (D.wires (List.ofFn (x ∘ move word))).getD 9 false := by
  simpa [wire] using wires_read (move word) D x 9

theorem orbitNormalize (D : Circuit) (valid : FanInTwo D) (computes : circuitFun 9 D = target)
    (first : (∃ u : Fin 9, ∀ x : Fin 9 → Bool,
      (D.wires (List.ofFn x)).getD 9 false = !x u) ∨
      ∃ (u v : Fin 9) (op : Bool), u ≠ v ∧ ∀ x : Fin 9 → Bool,
        (D.wires (List.ofFn x)).getD 9 false = if op = true then x u && x v else x u || x v) :
    ∃ E : Circuit, FanInTwo E ∧ E.size = D.size ∧ circuitFun 9 E = target ∧
      ((∃ u ∈ ([0,4] : List (Fin 9)), ∀ x : Fin 9 → Bool,
        (E.wires (List.ofFn x)).getD 9 false = !x u) ∨
        ∃ p ∈ representatives, ∃ op : Bool, ∀ x : Fin 9 → Bool,
          (E.wires (List.ofFn x)).getD 9 false =
            if op = true then x p.1 && x p.2 else x p.1 || x p.2) := by
  rcases first with ⟨u, hu⟩ | ⟨u, v, op, hne, huv⟩
  · obtain ⟨word, _, hw⟩ := List.any_eq_true.mp (vertexRoutes u)
    refine ⟨_, mono (move word) valid, size (move word) D, movedEval D computes word, ?_⟩
    refine Or.inl ⟨move word u, of_decide_eq_true hw, fun x => ?_⟩
    rw [movedFirst D word x, hu]
    rfl
  · rcases pairRoutes u v with he | h
    · exact (hne he).elim
    obtain ⟨word, _, hw⟩ := List.any_eq_true.mp h
    refine ⟨_, mono (move word) valid, size (move word) D, movedEval D computes word, Or.inr ?_⟩
    rcases of_decide_eq_true hw with hw | hw
    · refine ⟨(move word u, move word v), hw, op, fun x => ?_⟩
      rw [movedFirst D word x, huv (x ∘ move word)]
      rfl
    · refine ⟨(move word v, move word u), hw, op, fun x => ?_⟩
      rw [movedFirst D word x, huv (x ∘ move word)]
      simp only [Function.comp_apply]
      rw [Bool.and_comm (x (move word u)), Bool.or_comm (x (move word u))]


lemma notConstant (z : Bool) : target ≠ (fun _ => z) := by
  intro h
  cases z with
  | false =>
      let x : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1)
      have hx : target x = true := by decide
      have hw : target x = false := congrFun h x
      rw [hx] at hw
      exact Bool.noConfusion hw
  | true =>
      let x : Fin 9 → Bool := fun _ => false
      have hx : target x = false := by decide
      have hw : target x = true := congrFun h x
      rw [hx] at hw
      exact Bool.noConfusion hw

lemma notProjection : ∀ u : Fin 9, target ≠ (fun x => x u) := by
  intro u h
  have hz : ∀ i : Fin 9, target (fun j => decide (j = i)) = false := by decide
  have hw := congrFun h (fun j => decide (j = u))
  rw [hz u] at hw
  simp at hw

end PEqualNP.Outside.L_meta_2440


namespace PEqualNP.Outside.L_meta_2440.SingleGate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def firstValue (n : ℕ) (g : Gate) (x : Fin n → Bool) : Bool :=
  g.op.eval (g.inputs.map fun w => (List.ofFn x).getD w false)

lemma firstWires (n : ℕ) (g : Gate) (x : Fin n → Bool) :
    (Circuit.mk [g] 0).wires (List.ofFn x) = List.ofFn x ++ [firstValue n g x] := rfl

lemma unaryCases (f : Bool → Bool) : (f = (fun _ => false) ∨ f = (fun _ => true)) ∨
    (f = id ∨ f = fun b => !b) := by
  cases hf : f false <;> cases ht : f true
  · exact Or.inl (Or.inl (funext fun b => by cases b <;> assumption))
  · exact Or.inr (Or.inl (funext fun b => by cases b <;> assumption))
  · exact Or.inr (Or.inr (funext fun b => by cases b <;> assumption))
  · exact Or.inl (Or.inr (funext fun b => by cases b <;> assumption))

lemma firstLoose (n : ℕ) (g : Gate) (hf : FanInTwo (Circuit.mk [g] 0)) :
    (∃ c : Bool, ∀ x, firstValue n g x = c) ∨
    (∃ (i : Fin n) (f : Bool → Bool), ∀ x, firstValue n g x = f (x i)) ∨
    ∃ (i j : Fin n), i ≠ j ∧ ∃ b : Bool,
      ∀ x, firstValue n g x = if b then x i && x j else x i || x j := by
  have ⟨op,bound⟩ := hf g (by simp)
  change g.inputs.length ≤ 2 at bound
  have readValid (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
      (List.ofFn x).getD w false = x ⟨w,hw⟩ := by
    rw [List.getD_eq_getElem _ _ (by simpa)]
    simp only [List.getElem_ofFn]
  have readMissing (x : Fin n → Bool) (w : ℕ) (hw : ¬ w < n) :
      (List.ofFn x).getD w false = false := List.getD_eq_default _ _ (by simpa using hw)
  rcases he : g.inputs with _ | ⟨u,tail⟩
  · exact Or.inl ⟨g.op.eval [], by intro x; simp [firstValue,he]⟩
  rcases ht : tail with _ | ⟨v,tail'⟩
  · by_cases hu : u < n
    · exact Or.inr (Or.inl ⟨⟨u,hu⟩,fun b => g.op.eval [b], by
        intro x; simp only [firstValue,he,ht,List.map_cons,List.map_nil,readValid _ _ hu]⟩)
    · exact Or.inl ⟨g.op.eval [false], by
        intro x; simp only [firstValue,he,ht,List.map_cons,List.map_nil,readMissing _ _ hu]⟩
  have empty : tail' = [] := by simpa [he,ht] using bound
  subst tail'
  by_cases hu : u < n
  · by_cases hv : v < n
    · by_cases huv : u = v
      · subst v
        exact Or.inr (Or.inl ⟨⟨u,hu⟩,fun z => g.op.eval [z,z], by
          intro x; simp only [firstValue,he,ht,List.map_cons,List.map_nil,readValid _ _ hu]⟩)
      · have hne : (⟨u,hu⟩ : Fin n) ≠ ⟨v,hv⟩ := fun h => huv (congrArg Fin.val h)
        have op' : g.op = .and ∨ g.op = .or ∨ g.op = .not := op
        rcases op' with hop | hop | hop
        · refine Or.inr (Or.inr ⟨⟨u,hu⟩,⟨v,hv⟩,hne,true,?_⟩)
          intro x
          simp only [firstValue,he,ht,List.map_cons,List.map_nil,hop,readValid _ _ hu,readValid _ _ hv]
          simp [GateOp.eval]
        · refine Or.inr (Or.inr ⟨⟨u,hu⟩,⟨v,hv⟩,hne,false,?_⟩)
          intro x
          simp only [firstValue,he,ht,List.map_cons,List.map_nil,hop,readValid _ _ hu,readValid _ _ hv]
          simp [GateOp.eval]
        · refine Or.inr (Or.inl ⟨⟨u,hu⟩,(fun b => !b),?_⟩)
          intro x
          simp only [firstValue,he,ht,List.map_cons,List.map_nil,hop,
            readValid _ _ hu,readValid _ _ hv]
          rfl
    · exact Or.inr (Or.inl ⟨⟨u,hu⟩, (fun z => g.op.eval [z,false]), by
        intro x
        simp only [firstValue,he,ht,List.map_cons,List.map_nil,readValid _ _ hu,readMissing _ _ hv]⟩)
  · by_cases hv : v < n
    · exact Or.inr (Or.inl ⟨⟨v,hv⟩,(fun z => g.op.eval [false,z]), by
        intro x
        simp only [firstValue,he,ht,List.map_cons,List.map_nil,readMissing _ _ hu,readValid _ _ hv]⟩)
    · exact Or.inl ⟨g.op.eval [false,false], by
        intro x
        simp only [firstValue,he,ht,List.map_cons,List.map_nil,readMissing _ _ hu,readMissing _ _ hv]⟩

lemma firstKinds (n : ℕ) (g : Gate) (hf : FanInTwo (Circuit.mk [g] 0)) :
    (∃ c : Bool, ∀ x, firstValue n g x = c) ∨
    (∃ i : Fin n, ∀ x, firstValue n g x = x i) ∨
    (∃ i : Fin n, ∀ x, firstValue n g x = !x i) ∨
    ∃ (i j : Fin n), i ≠ j ∧ ∃ b : Bool,
      ∀ x, firstValue n g x = if b then x i && x j else x i || x j := by
  rcases firstLoose n g hf with h | ⟨i,f,h⟩ | h
  · exact Or.inl h
  · rcases unaryCases f with (rfl | rfl) | (rfl | rfl)
    · exact Or.inl ⟨false,h⟩
    · exact Or.inl ⟨true,h⟩
    · exact Or.inr (Or.inl ⟨i,h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨i,h⟩))
  · exact Or.inr (Or.inr (Or.inr h))

lemma firstWiresKinds (n : ℕ) (g : Gate) (hf : FanInTwo (Circuit.mk [g] 0)) :
    let V := fun x : Fin n → Bool => g.op.eval (g.inputs.map fun w => (List.ofFn x).getD w false)
    (∃ c : Bool, ∀ x, V x = c) ∨ (∃ i : Fin n, ∀ x, V x = x i) ∨
    (∃ i : Fin n, ∀ x, V x = !x i) ∨ ∃ (i j : Fin n), i ≠ j ∧ ∃ b : Bool,
      ∀ x, V x = if b then x i && x j else x i || x j := firstKinds n g hf

end PEqualNP.Outside.L_meta_2440.SingleGate

namespace PEqualNP.Outside.L_meta_2440.FirstProper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_2440.SingleGate

private def shift (n p w : ℕ) : ℕ :=
  if w < n then w else if w = n then p else w - 1

private def trueGate (n : ℕ) (g : Gate) : Gate :=
  match g.op with
  | .and => ⟨.and, g.inputs.filter fun w => w != n⟩
  | .or => if n ∈ g.inputs then ⟨.and, []⟩ else g
  | .not => if g.inputs.head? = some n then ⟨.or, []⟩ else ⟨.not, g.inputs.take 1⟩
  | _ => g

private def replaceGate (n : ℕ) (r : Option ℕ) (g : Gate) : Gate :=
  let h := if r.isNone then trueGate n g else g
  ⟨h.op, h.inputs.map (shift n (r.getD n))⟩

private theorem read_ne (a b : List Bool) (c : Bool) (p w : ℕ) (hw : w ≠ a.length) :
    (a ++ b).getD (shift a.length p w) false = (a ++ c :: b).getD w false := by
  by_cases hlt : w < a.length
  · simp [shift, hlt, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
  · have h1 : a.length ≤ w - 1 := by omega
    have h2 : a.length ≤ w := by omega
    have h3 : w - a.length = (w - 1 - a.length) + 1 := by omega
    simp only [shift, hlt, hw, ite_false, List.getD_eq_getElem?_getD,
      List.getElem?_append_right h1, List.getElem?_append_right h2]
    rw [h3]
    rfl

private theorem read_eq (a b : List Bool) (c : Bool) :
    (a ++ c :: b).getD a.length false = c := by
  simp [List.getD_eq_getElem?_getD]

private theorem eval_replace (n : ℕ) (r : Option ℕ) (g : Gate)
    (hOp : g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (old fresh : ℕ → Bool)
    (hRead : ∀ w, w ≠ n → fresh (shift n (r.getD n) w) = old w)
    (hReplace : old n = (r.map fresh).getD true) :
    (replaceGate n r g).op.eval ((replaceGate n r g).inputs.map fresh) =
      g.op.eval (g.inputs.map old) := by
  cases r with
  | some p =>
      simp only [replaceGate, Option.isNone_some, Bool.false_eq_true, ite_false,
        Option.getD_some, List.map_map, Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro w _
      by_cases hw : w = n
      · subst w
        simpa [shift] using hReplace.symm
      · exact hRead w hw
  | none =>
      have hTrue : old n = true := hReplace
      simp only [Option.getD_none] at hRead
      simp only [replaceGate, Option.isNone_none, ite_true, Option.getD_none,
        List.map_map, Function.comp_def]
      rcases hOp with ho | ho | ho
      · simp only [trueGate, ho, GateOp.eval, List.all_map, Function.comp_def]
        generalize g.inputs = xs
        induction xs with
        | nil => rfl
        | cons w ws ih =>
            by_cases hw : w = n
            · subst w
              rw [List.filter_cons, ite_eq_right (by simp)]
              simpa only [List.all_cons, id_eq, hTrue, Bool.true_and] using ih
            · rw [List.filter_cons, ite_eq_left (by simpa using hw)]
              simp only [id_eq] at ih
              simp only [List.all_cons, id_eq, hRead w hw, ih]
      · by_cases hm : n ∈ g.inputs
        · simp [trueGate, ho, hm, GateOp.eval, List.any_map, List.any_eq_true]
          exact ⟨n, hm, hTrue⟩
        · simp only [trueGate, ho, hm, ite_false]
          congr 1
          apply List.map_congr_left
          intro w hw
          exact hRead w (fun e => hm (e ▸ hw))
      · simp only [trueGate, ho]
        cases he : g.inputs with
        | nil => simp [GateOp.eval]
        | cons w ws =>
            by_cases hw : w = n
            · subst w
              simp [GateOp.eval, hTrue]
            · simp [hw, GateOp.eval, hRead w hw]

private theorem model_replace (n : ℕ) (r : Option ℕ) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (replaceGate n r g).op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      (replaceGate n r g).inputs.length ≤ 2 := by
  rcases h with ⟨hop, hlen⟩
  cases r with
  | some p => simpa [replaceGate] using ⟨hop, hlen⟩
  | none =>
      have hop' : g.op = .and ∨ g.op = .or ∨ g.op = .not := hop
      rcases hop' with ho | ho | ho
      · simp [replaceGate, trueGate, ho]
        exact List.length_filter_le _ _ |>.trans hlen
      · by_cases hm : n ∈ g.inputs <;> simp [replaceGate, trueGate, ho, hm, hlen]
      · by_cases hm : g.inputs.head? = some n <;>
          simp [replaceGate, trueGate, ho, hm, List.length_take]

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem fold_replace (a : List Bool) (c : Bool) (r : Option ℕ) (gs : List Gate)
    (hOps : ∀ g ∈ gs, g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (b : List Bool)
    (hR : ∀ z : List Bool, z.length ≤ b.length + gs.length →
      c = (r.map (fun p => (a ++ z).getD p false)).getD true) :
    ∃ t : List Bool, t.length = b.length + gs.length ∧
      (gs.map (replaceGate a.length r)).foldl step (a ++ b) = a ++ t ∧
      gs.foldl step (a ++ c :: b) = a ++ c :: t := by
  induction gs generalizing b with
  | nil => exact ⟨b, by simp⟩
  | cons g gs ih =>
      have h := eval_replace a.length r g (hOps g (by simp))
        (fun p => (a ++ c :: b).getD p false) (fun p => (a ++ b).getD p false)
        (read_ne a b c (r.getD a.length)) (by rw [read_eq]; exact hR b (by simp))
      let v := g.op.eval (g.inputs.map fun p => (a ++ c :: b).getD p false)
      have hr' : ∀ z : List Bool, z.length ≤ (b ++ [v]).length + gs.length →
          c = (r.map (fun p => (a ++ z).getD p false)).getD true := by
        intro z hz
        apply hR z
        simp only [List.length_append, List.length_singleton] at hz
        simp only [List.length_cons]
        omega
      obtain ⟨t, ht, hFresh, hOld⟩ := ih
        (fun q hq => hOps q (List.mem_cons_of_mem _ hq)) (b ++ [v]) hr'
      refine ⟨t, by simp at ht ⊢; omega, ?_, ?_⟩
      · simp only [List.map_cons, List.foldl_cons]
        have he : step (a ++ b) (replaceGate a.length r g) = a ++ (b ++ [v]) := by
          unfold step
          rw [h, List.append_assoc]
        rw [he]
        exact hFresh
      · simpa [List.foldl_cons, step, v, List.append_assoc] using hOld

private theorem erase_first (n : ℕ) (g : Gate) (gs : List Gate) (o : ℕ)
    (hC : FanInTwo ⟨g :: gs, o⟩) (r : Option ℕ)
    (hR : ∀ (x : Fin n → Bool) (z : List Bool), z.length ≤ gs.length →
      firstValue n g x = (r.map (fun p => (List.ofFn x ++ z).getD p false)).getD true)
    (hOut : o ≠ n) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = gs.length ∧
      circuitFun n D = circuitFun n ⟨g :: gs, o⟩ := by
  let D : Circuit := ⟨gs.map (replaceGate n r), shift n (r.getD n) o⟩
  refine ⟨D, ?_, by simp [D, Circuit.size], ?_⟩
  · intro w hw
    change w ∈ gs.map (replaceGate n r) at hw
    obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hw
    exact model_replace n r w' (hC w' (List.mem_cons_of_mem _ hw'))
  · funext x
    let a := List.ofFn x
    let c := firstValue n g x
    have hn : a.length = n := by simp [a]
    obtain ⟨t, ht, hNew, hOld⟩ := fold_replace a c r gs
      (fun w hw => (hC w (List.mem_cons_of_mem _ hw)).1) [] (by simpa [a, c] using hR x)
    have hRead := read_ne a t c (r.getD n) o (by simpa [hn] using hOut)
    change ((gs.map (replaceGate n r)).foldl step a).getD (shift n (r.getD n) o) false =
      (gs.foldl step (a ++ [c])).getD o false
    simp only [hn, List.append_nil] at hNew
    rw [hNew, hOld]
    simpa only [hn] using hRead

private theorem fold_read (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
    (gs.foldl step w).getD j false = w.getD j false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g rest ih =>
      simp only [List.foldl_cons]
      have hj' : j < (step w g).length := by simp [step]; omega
      rw [ih _ hj']
      exact List.getD_append _ _ _ _ hj

private theorem first_wire (n : ℕ) (g : Gate) (gs : List Gate) (o : ℕ) (x : Fin n → Bool) :
    ((Circuit.mk (g :: gs) o).wires (List.ofFn x)).getD n false = firstValue n g x := by
  change (gs.foldl step (List.ofFn x ++ [firstValue n g x])).getD n false = _
  rw [fold_read _ _ _ (by simp)]
  simp

theorem first_proper (n : ℕ) (C : Circuit) (hC : FanInTwo C)
    (hConst : ∀ b, circuitFun n C ≠ fun _ => b)
    (hInput : ∀ i, circuitFun n C ≠ fun x => x i) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size ∧ circuitFun n D = circuitFun n C ∧
      ((∃ i : Fin n, ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD n false = !x i) ∨
      ∃ i j : Fin n, i ≠ j ∧ ∃ b : Bool, ∀ x : Fin n → Bool,
        (D.wires (List.ofFn x)).getD n false = if b then x i && x j else x i || x j) := by
  generalize hBudget : C.size = m
  induction m using Nat.strong_induction_on generalizing C with
  | ind m ih =>
    rcases C with ⟨gates, out⟩
    cases gates with
    | nil =>
        by_cases ho : out < n
        · refine (hInput ⟨out, ho⟩ (funext fun x => ?_)).elim
          change (List.ofFn x).getD out false = x ⟨out, ho⟩
          rw [List.getD_eq_getElem _ _ (by simpa using ho)]
          simp only [List.getElem_ofFn]
        · refine (hConst false (funext fun x => ?_)).elim
          change (List.ofFn x).getD out false = false
          exact List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ho)
    | cons g gs =>
        have hHead : FanInTwo ⟨[g], 0⟩ := by
          intro q hq
          have hq' : q = g := by simpa using hq
          subst q
          exact hC g (by simp)
        rcases firstKinds n g hHead with ⟨b, hb⟩ | ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, j, hne, b, hb⟩
        · have ho : out ≠ n := by
            intro h
            subst out
            exact hConst b (funext fun x => (first_wire n g gs n x).trans (hb x))
          let r := if b then none else some (n + gs.length)
          have hR : ∀ (x : Fin n → Bool) (z : List Bool), z.length ≤ gs.length →
              firstValue n g x = (r.map (fun p => (List.ofFn x ++ z).getD p false)).getD true := by
            intro x z hz
            rw [hb]
            cases b with
            | false =>
                have h : (List.ofFn x ++ z).length ≤ n + gs.length := by simpa using hz
                change false = (List.ofFn x ++ z).getD (n + gs.length) false
                exact (List.getD_eq_default _ _ h).symm
            | true => rfl
          obtain ⟨D, hD, hSize, hEval⟩ := erase_first n g gs out hC r hR ho
          have hdConst : ∀ b, circuitFun n D ≠ fun _ => b := by rwa [hEval]
          have hdInput : ∀ i, circuitFun n D ≠ fun x => x i := by rwa [hEval]
          have hLT : D.size < m := by
            rw [hSize, ← hBudget]
            simp [Circuit.size]
          obtain ⟨E, hE, hESize, hEEval, hProper⟩ := ih D.size hLT D hD hdConst hdInput rfl
          exact ⟨E, hE, hESize.trans hLT.le, hEEval.trans hEval, hProper⟩
        · have ho : out ≠ n := by
            intro h
            subst out
            exact hInput i (funext fun x => (first_wire n g gs n x).trans (hi x))
          have hR : ∀ (x : Fin n → Bool) (z : List Bool), z.length ≤ gs.length →
              firstValue n g x =
                ((some i.val).map (fun p => (List.ofFn x ++ z).getD p false)).getD true := by
            intro x z _
            rw [hi]
            simp only [Option.map_some, Option.getD_some]
            rw [List.getD_append _ _ _ _ (by simp)]
            rw [List.getD_eq_getElem _ _ (by simp)]
            simp only [List.getElem_ofFn]
          obtain ⟨D, hD, hSize, hEval⟩ := erase_first n g gs out hC (some i.val) hR ho
          have hdConst : ∀ b, circuitFun n D ≠ fun _ => b := by rwa [hEval]
          have hdInput : ∀ i, circuitFun n D ≠ fun x => x i := by rwa [hEval]
          have hLT : D.size < m := by
            rw [hSize, ← hBudget]
            simp [Circuit.size]
          obtain ⟨E, hE, hESize, hEEval, hProper⟩ := ih D.size hLT D hD hdConst hdInput rfl
          exact ⟨E, hE, hESize.trans hLT.le, hEEval.trans hEval, hProper⟩
        · exact ⟨_, hC, hBudget.le, rfl, Or.inl ⟨i, fun x =>
            (first_wire n g gs out x).trans (hi x)⟩⟩
        · exact ⟨_, hC, hBudget.le, rfl, Or.inr ⟨i, j, hne, b, fun x =>
            (first_wire n g gs out x).trans (hb x)⟩⟩

end PEqualNP.Outside.L_meta_2440.FirstProper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2440

theorem PEqualNP.Outside.L_meta_2440 :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x3 : Fin (9 : ℕ) → Bool) => x3 (0 : Fin (9 : ℕ)) && x3 (1 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (3 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (4 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)) && x3 (0 : Fin (9 : ℕ)) || x3 (0 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ)) || x3 (1 : Fin (9 : ℕ)) && x3 (6 : Fin (9 : ℕ)) || x3 (2 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (3 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (5 : Fin (9 : ℕ)) && x3 (7 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)) && x3 (8 : Fin (9 : ℕ)) || x3 (8 : Fin (9 : ℕ)) && x3 (5 : Fin (9 : ℕ))) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 ∧ x4.size ≤ x1.size ∧ PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x4 = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ∧ ((∃ x5 ∈ [(0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))], ∀ (x6 : Fin (9 : ℕ) → Bool), (x4.wires (List.ofFn x6)).getD (9 : ℕ) Bool.false = !x6 x5) ∨ ∃ x5 ∈ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)))], ∃ (x6 : Bool), ∀ (x7 : Fin (9 : ℕ) → Bool), (x4.wires (List.ofFn x7)).getD (9 : ℕ) Bool.false = if x6 = Bool.true then x7 x5.1 && x7 x5.2 else x7 x5.1 || x7 x5.2) := by
  intro C valid hC
  have computes : circuitFun 9 C = target := hC
  have hConst : ∀ b, circuitFun 9 C ≠ fun _ => b := by
    rw [computes]
    exact notConstant
  have hInput : ∀ i, circuitFun 9 C ≠ fun x => x i := by
    rw [computes]
    exact notProjection
  obtain ⟨D, hD, small, same, first⟩ := FirstProper.first_proper 9 C valid hConst hInput
  have first' : (∃ u : Fin 9, ∀ x : Fin 9 → Bool,
      (D.wires (List.ofFn x)).getD 9 false = !x u) ∨
      ∃ (u v : Fin 9) (op : Bool), u ≠ v ∧ ∀ x : Fin 9 → Bool,
        (D.wires (List.ofFn x)).getD 9 false = if op = true then x u && x v else x u || x v := by
    rcases first with h | ⟨a, b, ne, op, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, b, op, ne, h⟩
  obtain ⟨E, hE, esize, efun, efirst⟩ := orbitNormalize D hD (same.trans computes) first'
  refine ⟨E, hE, esize.le.trans small, efun.trans computes.symm, efirst⟩
