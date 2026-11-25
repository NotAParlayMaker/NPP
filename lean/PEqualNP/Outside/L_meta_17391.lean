import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17391

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Terms (n : ℕ) := List (List (Fin n))

def observe (x : Fin n → Bool) (p : Terms n) : Bool := p.any (fun l => l.all x)

def product (p q : Terms n) : Terms n := p.flatMap fun a => q.map fun b => a ++ b

theorem observeAppend (x : Fin n → Bool) (p q : Terms n) :
    observe x (p ++ q) = (observe x p || observe x q) := by
  simp only [observe, List.any_append]

theorem observeRowProduct (x : Fin n → Bool) (a : List (Fin n)) (q : Terms n) :
    observe x (q.map fun b => a ++ b) = (a.all x && observe x q) := by
  induction q with
  | nil => simp [observe]
  | cons b q ih =>
    have step :
        ((a.all x && b.all x) || (a.all x && observe x q)) =
          (a.all x && (b.all x || observe x q)) := by
      cases h : a.all x <;> simp [h]
    calc
      observe x ((b :: q).map fun b => a ++ b) =
          ((a.all x && b.all x) || observe x (q.map fun b => a ++ b)) := by
        simp only [List.map_cons, observe, List.any_cons, List.all_append]
      _ = (a.all x && (b.all x || observe x q)) := by rw [ih]; exact step
      _ = (a.all x && observe x (b :: q)) := rfl

theorem observeProduct (x : Fin n → Bool) (p q : Terms n) :
    observe x (product p q) = (observe x p && observe x q) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change observe x ((q.map fun b => a ++ b) ++ product p q) =
      ((a.all x || observe x p) && observe x q)
    rw [observeAppend, observeRowProduct, ih]
    cases h : observe x q <;> simp [h]

def pureFamily (p : Terms n) : Finset (Finset (Fin n)) := (p.map List.toFinset).toFinset

theorem observe_of_subset (x : Fin n → Bool) (p q : Terms n) (sub : pureFamily p ⊆ pureFamily q)
    (yes : observe x p = true) : observe x q = true := by
  obtain ⟨a, ma, ok⟩ := List.any_eq_true.mp yes
  have ha : a.toFinset ∈ pureFamily p :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, ma, rfl⟩)
  obtain ⟨b, mb, eq⟩ := List.mem_map.mp (List.mem_toFinset.mp (sub ha))
  apply List.any_eq_true.mpr
  refine ⟨b, mb, List.all_eq_true.mpr ?_⟩
  intro i mi
  have h : i ∈ b.toFinset := List.mem_toFinset.mpr mi
  rw [eq] at h
  exact List.all_eq_true.mp ok i (List.mem_toFinset.mp h)

theorem observe_same (x : Fin n → Bool) (p q : Terms n) (eq : pureFamily p = pureFamily q) :
    observe x p = observe x q := by
  cases hp : observe x p <;> cases hq : observe x q
  · rfl
  · have hn := observe_of_subset x q p (by rw [eq]) hq
    simp [hp] at hn
  · have hn := observe_of_subset x p q (by rw [eq]) hp
    simp [hq] at hn
  · rfl

def allTerms (xs : List (Terms n)) : Terms n := xs.foldr product [[]]
def anyTerms (xs : List (Terms n)) : Terms n := xs.foldr List.append []

theorem allMatches (x : Fin n → Bool) (xs : List (Terms n)) :
    observe x (allTerms xs) = (xs.map (observe x)).all id := by
  induction xs with
  | nil => rfl
  | cons p tail ih =>
    change observe x (product p (allTerms tail)) =
      (observe x p && (tail.map (observe x)).all id)
    rw [observeProduct, ih]

theorem anyMatches (x : Fin n → Bool) (xs : List (Terms n)) :
    observe x (anyTerms xs) = (xs.map (observe x)).any id := by
  induction xs with
  | nil => rfl
  | cons p tail ih =>
    change observe x (p ++ anyTerms tail) =
      (observe x p || (tail.map (observe x)).any id)
    rw [observeAppend, ih]

theorem observedRead (x : Fin n → Bool) (xs : List (Terms n)) (i : ℕ) :
    observe x (xs.getD i []) = (xs.map (observe x)).getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : xs[i]? <;> simp [observe, h]


def termGate {n : ℕ} (op : GateOp) (xs : List (Terms n)) : Terms n :=
  match op with
  | .and => allTerms xs
  | .or => anyTerms xs
  | _ => []

theorem gateMatches (x : Fin n → Bool) (g : Gate) (ws : List (Terms n))
    (ops : g.op = .and ∨ g.op = .or) :
    observe x (termGate g.op (g.inputs.map (fun i => ws.getD i []))) =
      g.op.eval (g.inputs.map (fun i => (ws.map (observe x)).getD i false)) := by
  have reads : (g.inputs.map (fun i => ws.getD i [])).map (observe x) =
      g.inputs.map (fun i => (ws.map (observe x)).getD i false) := by
    rw [List.map_map]
    congr 1
    funext i
    exact observedRead x ws i
  rcases ops with h | h
  · rw [h]
    change observe x (allTerms _) = _
    rw [allMatches, reads]
    rfl
  · rw [h]
    change observe x (anyTerms _) = _
    rw [anyMatches, reads]
    rfl

def symbolicRun {n : ℕ} : List Gate → List (Terms n) → List (Terms n)
  | [], ws => ws
  | g :: gs, ws => symbolicRun gs (ws ++ [termGate g.op (g.inputs.map (fun i => ws.getD i []))])

theorem runMatches (x : Fin n → Bool) (gs : List Gate) (ws : List (Terms n))
    (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    (symbolicRun gs ws).map (observe x) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))])
        (ws.map (observe x)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simp only [symbolicRun, List.foldl_cons]
    rw [ih _ (fun g' hg' => ops g' (List.mem_cons_of_mem _ hg'))]
    simp only [List.map_append, List.map_singleton]
    rw [gateMatches x g ws (ops g (by simp))]

def termInput {n : ℕ} (i : Fin n) : Terms n := [[i]]

theorem termInputMatches (x : Fin n → Bool) (i : Fin n) :
    observe x (termInput i) = x i := by
  simp [observe, termInput]

def circuitTerms (n : ℕ) (C : Circuit) : Terms n :=
  (symbolicRun C.gates (List.ofFn termInput)).getD C.output []

theorem circuitMatches (C : Circuit) (x : Fin n → Bool)
    (ops : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or) :
    observe x (circuitTerms n C) = C.eval (List.ofFn x) := by
  have inputs : (List.ofFn termInput).map (observe x) = List.ofFn x := by
    rw [List.map_ofFn]
    exact congrArg (fun f : Fin n → Bool => List.ofFn f) (funext (termInputMatches x))
  unfold circuitTerms Circuit.eval Circuit.wires
  rw [observedRead, runMatches x C.gates _ ops, inputs]



def termCode (s : List (Fin n)) : ℕ := s.foldr (fun i r => 2^i.val ||| r) 0

theorem termCodeBit (s : List (Fin n)) (i : Fin n) :
    (termCode s).testBit i.val = decide (i ∈ s) := by
  induction s with
  | nil => simp [termCode]
  | cons j rest ih =>
    change (2^j.val ||| termCode rest).testBit i.val = decide (i ∈ j :: rest)
    rw [Nat.testBit_or, Nat.testBit_two_pow, ih]
    simp [Fin.val_inj, eq_comm]

theorem termCodeInject {a b : List (Fin n)} (same : termCode a = termCode b) :
    a.toFinset = b.toFinset := by
  ext i
  have d := congrArg (fun k : ℕ => k.testBit i.val) same
  rw [termCodeBit, termCodeBit] at d
  simp only [List.mem_toFinset]
  constructor
  · intro h
    have b := decide_eq_true h
    rw [d] at b
    exact of_decide_eq_true b
  · intro h
    have a := decide_eq_true h
    rw [← d] at a
    exact of_decide_eq_true a

def coversCodes (p q : List ℕ) : Bool :=
  p.all (fun i => q.contains i)

theorem codeSub {p q : Terms n}
    (h : coversCodes (p.map termCode) (q.map termCode) = true) :
    pureFamily p ⊆ pureFamily q := by
  intro s hs
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hs)
  have seen : termCode u ∈ p.map termCode := List.mem_map.mpr ⟨u, hu, rfl⟩
  have hv := List.all_eq_true.mp h _ seen
  obtain ⟨v, hv, equal⟩ := List.mem_map.mp ((by simpa using hv : termCode u ∈ q.map termCode))
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨v, hv, termCodeInject equal⟩)


def witness : Circuit :=
  ⟨[
    ⟨.and, [1, 4]⟩,
    ⟨.and, [2, 5]⟩,
    ⟨.and, [3, 6]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [13, 12]⟩,
    ⟨.and, [0, 14]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.and, [4, 5]⟩,
    ⟨.and, [8, 9]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.or, [19, 18]⟩,
    ⟨.and, [7, 20]⟩,
    ⟨.and, [1, 3]⟩,
    ⟨.and, [4, 6]⟩,
    ⟨.or, [22, 23]⟩,
    ⟨.and, [8, 24]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.or, [26, 27]⟩,
    ⟨.and, [9, 28]⟩,
    ⟨.or, [15, 21]⟩,
    ⟨.or, [30, 25]⟩,
    ⟨.or, [31, 29]⟩
  ], 32⟩

def expected : Terms 10 := [[0,1,4],[0,2,5],[0,3,6],[1,2,7],[1,3,8],[2,3,9],[4,5,7],[4,6,8],[5,6,9],[7,8,9]]

def binaryAO (g : Gate) : Bool :=
  match g.op with
  | .and | .or => true
  | _ => false

theorem binaryAOSound (g : Gate) (h : binaryAO g = true) :
    g.op = .and ∨ g.op = .or := by
  cases eq : g.op <;> simp [binaryAO, eq] at h ⊢

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2400000 in
theorem gateChecklist : witness.gates.all (fun g => binaryAO g && decide (g.inputs.length ≤ 2)) = true := by
  decide +kernel

theorem permitted : ∀ g ∈ witness.gates, g.op = .and ∨ g.op = .or := by
  intro g hg
  have yes := List.all_eq_true.mp gateChecklist g hg
  simp only [Bool.and_eq_true] at yes
  exact binaryAOSound g yes.1

theorem fit : FanInTwo witness := by
  intro g hg
  have yes := List.all_eq_true.mp gateChecklist g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at yes
  rcases binaryAOSound g yes.1 with h | h
  · exact ⟨by simp [h], yes.2⟩
  · exact ⟨by simp [h], yes.2⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem codesMatch :
    coversCodes ((circuitTerms 10 witness).map termCode) (expected.map termCode) = true ∧
    coversCodes (expected.map termCode) ((circuitTerms 10 witness).map termCode) = true := by
  decide +kernel

theorem correctness (x : Fin 10 → Bool) :
    witness.eval (List.ofFn x) = observe x expected :=
  (circuitMatches witness x permitted).symm.trans
    (observe_same x (circuitTerms 10 witness) expected
      (Finset.Subset.antisymm (codeSub codesMatch.1) (codeSub codesMatch.2)))

end PEqualNP.Outside.L_meta_17391

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_17391 in
theorem PEqualNP.Outside.L_meta_17391 : PEqualNP.MetaComplexity.HasCircuitSize 10 (fun x : Fin 10 → Bool => (x 0 && x 1 && x 4) || (x 0 && x 2 && x 5) || (x 0 && x 3 && x 6) || (x 1 && x 2 && x 7) || (x 1 && x 3 && x 8) || (x 2 && x 3 && x 9) || (x 4 && x 5 && x 7) || (x 4 && x 6 && x 8) || (x 5 && x 6 && x 9) || (x 7 && x 8 && x 9)) 24 := by
  refine ⟨witness, fit, by decide, ?_⟩
  intro x
  rw [correctness]
  simp only [observe, expected, List.any_cons, List.any_nil, List.all_cons, List.all_nil,
    Bool.and_true, Bool.or_false, Bool.and_assoc, Bool.or_assoc]

