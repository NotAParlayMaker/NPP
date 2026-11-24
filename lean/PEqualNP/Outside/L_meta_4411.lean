import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4411_aux

-- L-meta-4411
--
-- Reading table for a circuit whose first two gates are supplied from outside, plus the fact
-- that a wire no gate reads can never influence the output.
--
-- The wire table is the fold behind `Circuit.wires`; these lemmas are adapted from the merged
-- files `L_meta_2038` and `L_meta_2507` (same fold, different statements).

-- The wire table of a gate list, starting from an arbitrary initial list of bits.
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_eq_wires (C : Circuit) (w : List Bool) : C.wires w = wiresFrom C.gates w := rfl

lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

-- The wires of a gate that actually influence its value: all of them, except that a `not`
-- gate ignores every input after the first (and `not` on no inputs is constantly `true`).
def liveInputs (g : Gate) : List ℕ :=
  if g.op.eval [Bool.false, Bool.false] = Bool.true then g.inputs.take 1 else g.inputs

-- The input `i` is read by the gate `g` in a position where it influences `g`'s value.
def ReadsLive (g : Gate) (i : ℕ) : Prop := i ∈ liveInputs g

-- The value of a gate of the AND/OR/NOT basis depends only on the wires it reads live.
lemma eval_map_agree (g : Gate) (w w' : List Bool) (i : ℕ)
    (hfan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hno : i ∉ liveInputs g)
    (hagree : ∀ j, j ≠ i → w.getD j false = w'.getD j false) :
    g.op.eval (g.inputs.map fun k => w.getD k false)
      = g.op.eval (g.inputs.map fun k => w'.getD k false) := by
  obtain ⟨op, ins⟩ := g
  rcases hfan with rfl | rfl | rfl
  · -- AND reads every input
    have hins : i ∉ ins := by simpa [liveInputs, GateOp.eval] using hno
    have hmap : (ins.map fun k => w.getD k false) = (ins.map fun k => w'.getD k false) :=
      List.map_congr_left fun k hk => hagree k fun h => hins (h ▸ hk)
    simp only [hmap]
  · -- OR reads every input
    have hins : i ∉ ins := by simpa [liveInputs, GateOp.eval] using hno
    have hmap : (ins.map fun k => w.getD k false) = (ins.map fun k => w'.getD k false) :=
      List.map_congr_left fun k hk => hagree k fun h => hins (h ▸ hk)
    simp only [hmap]
  · -- NOT reads only its first input
    have hlive : liveInputs (⟨GateOp.not, ins⟩ : Gate) = ins.take 1 := by
      simp [liveInputs, GateOp.eval]
    rw [hlive] at hno
    cases ins with
    | nil => simp
    | cons k ks =>
      have hk : k ∈ (k :: ks).take 1 := by simp
      have hki : k ≠ i := fun h => hno (h ▸ hk)
      simp [GateOp.eval]
      exact hagree k hki

-- Two wire tables that agree away from the wire `i` still agree away from `i`, as long as no
-- gate of the list reads `i` live.
lemma wiresFrom_agree (gs : List Gate) (i : ℕ)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hno : ∀ g ∈ gs, i ∉ liveInputs g) :
    ∀ (w w' : List Bool), w.length = w'.length →
      (∀ j, j ≠ i → w.getD j false = w'.getD j false) →
      ∀ j, j ≠ i → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil =>
    intro w w' _ ha j hj
    exact ha j hj
  | cons g gs ih =>
    intro w w' hl ha j hj
    have hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) :=
      hfan g (List.mem_cons_self ..)
    have hng : i ∉ liveInputs g := hno g (List.mem_cons_self ..)
    have hv := eval_map_agree g w w' i hg hng ha
    rw [wiresFrom_cons, wiresFrom_cons]
    refine ih (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) _ _ ?_ ?_ j hj
    · simp
      omega
    · intro j' hj'
      by_cases hlt : j' < w.length
      · rw [getD_snoc_lt _ _ _ _ hlt, getD_snoc_lt _ _ _ _ (by omega)]
        exact ha j' hj'
      · by_cases heq : j' = w.length
        · rw [getD_snoc_eq _ _ _ _ heq, getD_snoc_eq _ _ _ _ (by omega)]
          exact hv
        · rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
          exact ha j' hj'

-- The graph: the Petersen graph minus one vertex

-- The twelve edges of the Petersen graph on `9` vertices.
def edges : List (Fin 9 × Fin 9) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5),
   (1, 6), (2, 7), (3, 8), (5, 7), (6, 8), (8, 5)]

-- Adjacency of the twelve edges, as a computable predicate.
def adj (u v : Fin 9) : Bool :=
  edges.any fun e => (e.1 == u && e.2 == v) || (e.1 == v && e.2 == u)

-- The edge function: some edge has both ends set.
def edgeFun (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)

-- Reading a bit of `List.ofFn g` as `g` applied to a `Fin`.
lemma ofFn_getD {α : Type*} {n : ℕ} (g : Fin n → α) (k : ℕ) (d : α) (hk : k < n) :
    (List.ofFn g).getD k d = g ⟨k, hk⟩ := by
  simp only [List.getD, List.getElem?_ofFn, dite_eq_left hk, Option.getD_some]

-- The initial wire list of the reduced problem: the nine inputs, then the two OR gates the
-- desk supplies. Two such lists agree away from `i` once the inputs agree away from `i` and the
-- two supplied OR gates have the same values.
lemma agree_ofFn (p q : Fin 9 → Bool) (u v u' v' : Bool) (i : ℕ)
    (hpq : ∀ j : Fin 9, (j : ℕ) ≠ i → p j = q j)
    (hu : u = u') (hv : v = v') :
    ∀ j, j ≠ i →
      (List.ofFn p ++ [u, v]).getD j false = (List.ofFn q ++ [u', v']).getD j false := by
  intro j hj
  have hp : (List.ofFn p).length = 9 := by simp
  have hq : (List.ofFn q).length = 9 := by simp
  by_cases h9 : j < 9
  · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega),
      ofFn_getD p j false h9, ofFn_getD q j false h9]
    exact hpq ⟨j, h9⟩ hj
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
    by_cases h9' : j = 9
    · subst h9'
      simpa using hu
    · by_cases h10 : j = 10
      · subst h10
        simpa using hv
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

-- Finite facts about the graph, all checked by `decide`

-- Every vertex has a neighbour.
lemma exists_adj : ∀ i : Fin 9, ∃ d : Fin 9, adj i d = true := by decide

-- A vertex `d` adjacent to `a` but to neither `b` nor `a` itself serves as the escape vertex
-- for the case where the unread input is the first supplied OR gate's left end.
lemma escape : ∀ a b : Fin 9, a ≠ b → a ≠ 0 → a ≠ 4 → b ≠ 0 → b ≠ 4 →
    ∃ d : Fin 9, adj a d = true ∧ adj b d = false ∧ d ≠ b := by decide

-- The generic case: the input `i` is one of the nine, but not one of the four that the two
-- supplied OR gates see. Setting only a neighbour `d` gives `false`, setting `d` and `i` gives
-- `true`, and resetting `i` changes no other wire.
lemma witness_generic : ∀ (i d a b : Fin 9), adj i d = true →
    i ≠ 0 → i ≠ 4 → i ≠ a → i ≠ b →
    (∀ j : Fin 9, j ≠ i → (j == d) = (j == d || j == i)) ∧
    (((fun j : Fin 9 => j == d) 0 || (fun j : Fin 9 => j == d) 4)
      = ((fun j : Fin 9 => j == d || j == i) 0
          || (fun j : Fin 9 => j == d || j == i) 4)) ∧
    (((fun j : Fin 9 => j == d) a || (fun j : Fin 9 => j == d) b)
      = ((fun j : Fin 9 => j == d || j == i) a
          || (fun j : Fin 9 => j == d || j == i) b)) ∧
    edgeFun (fun j : Fin 9 => j == d) = false ∧
    edgeFun (fun j : Fin 9 => j == d || j == i) = true := by
  decide

-- The case `i = 0`: the second supplied OR gate makes `x_4` visible, so `x_0` is the only
-- hidden input; setting only `4` gives `false`, setting `0` and `4` gives `true`.
lemma witness_zero : ∀ (a b : Fin 9), a ≠ 0 → b ≠ 0 →
    (∀ j : Fin 9, j ≠ (0 : Fin 9) →
      (j == (4 : Fin 9)) = (j == (4 : Fin 9) || j == (0 : Fin 9))) ∧
    (((fun j : Fin 9 => j == (4 : Fin 9)) 0 || (fun j : Fin 9 => j == (4 : Fin 9)) 4)
      = ((fun j : Fin 9 => j == (4 : Fin 9) || j == (0 : Fin 9)) 0
          || (fun j : Fin 9 => j == (4 : Fin 9) || j == (0 : Fin 9)) 4)) ∧
    (((fun j : Fin 9 => j == (4 : Fin 9)) a || (fun j : Fin 9 => j == (4 : Fin 9)) b)
      = ((fun j : Fin 9 => j == (4 : Fin 9) || j == (0 : Fin 9)) a
          || (fun j : Fin 9 => j == (4 : Fin 9) || j == (0 : Fin 9)) b)) ∧
    edgeFun (fun j : Fin 9 => j == (4 : Fin 9)) = false ∧
    edgeFun (fun j : Fin 9 => j == (4 : Fin 9) || j == (0 : Fin 9)) = true := by
  decide

-- The case `i = 4`, symmetric to `i = 0` with the roles of `0` and `4` exchanged.
lemma witness_four : ∀ (a b : Fin 9), a ≠ 4 → b ≠ 4 →
    (∀ j : Fin 9, j ≠ (4 : Fin 9) →
      (j == (0 : Fin 9)) = (j == (0 : Fin 9) || j == (4 : Fin 9))) ∧
    (((fun j : Fin 9 => j == (0 : Fin 9)) 0 || (fun j : Fin 9 => j == (0 : Fin 9)) 4)
      = ((fun j : Fin 9 => j == (0 : Fin 9) || j == (4 : Fin 9)) 0
          || (fun j : Fin 9 => j == (0 : Fin 9) || j == (4 : Fin 9)) 4)) ∧
    (((fun j : Fin 9 => j == (0 : Fin 9)) a || (fun j : Fin 9 => j == (0 : Fin 9)) b)
      = ((fun j : Fin 9 => j == (0 : Fin 9) || j == (4 : Fin 9)) a
          || (fun j : Fin 9 => j == (0 : Fin 9) || j == (4 : Fin 9)) b)) ∧
    edgeFun (fun j : Fin 9 => j == (0 : Fin 9)) = false ∧
    edgeFun (fun j : Fin 9 => j == (0 : Fin 9) || j == (4 : Fin 9)) = true := by
  decide

-- The case `i` is the first supplied OR gate's left end `a`: the second gate sees `b`, so `b`
-- stays set and `a` is toggled.
lemma witness_first : ∀ (a b d : Fin 9), a ≠ b → adj a d = true →
    adj b d = false → d ≠ b → a ≠ 0 → a ≠ 4 →
    (∀ j : Fin 9, j ≠ a → (j == b || j == d) = (j == b || j == d || j == a)) ∧
    (((fun j : Fin 9 => j == b || j == d) 0 || (fun j : Fin 9 => j == b || j == d) 4)
      = ((fun j : Fin 9 => j == b || j == d || j == a) 0
          || (fun j : Fin 9 => j == b || j == d || j == a) 4)) ∧
    (((fun j : Fin 9 => j == b || j == d) a || (fun j : Fin 9 => j == b || j == d) b)
      = ((fun j : Fin 9 => j == b || j == d || j == a) a
          || (fun j : Fin 9 => j == b || j == d || j == a) b)) ∧
    edgeFun (fun j : Fin 9 => j == b || j == d) = false ∧
    edgeFun (fun j : Fin 9 => j == b || j == d || j == a) = true := by
  decide

-- The case `i` is the first supplied OR gate's right end; symmetric in `a` and `b`.
lemma witness_second : ∀ (a b d : Fin 9), a ≠ b → adj b d = true →
    adj a d = false → d ≠ a → b ≠ 0 → b ≠ 4 →
    (∀ j : Fin 9, j ≠ b → (j == a || j == d) = (j == a || j == d || j == b)) ∧
    (((fun j : Fin 9 => j == a || j == d) 0 || (fun j : Fin 9 => j == a || j == d) 4)
      = ((fun j : Fin 9 => j == a || j == d || j == b) 0
          || (fun j : Fin 9 => j == a || j == d || j == b) 4)) ∧
    (((fun j : Fin 9 => j == a || j == d) a || (fun j : Fin 9 => j == a || j == d) b)
      = ((fun j : Fin 9 => j == a || j == d || j == b) a
          || (fun j : Fin 9 => j == a || j == d || j == b) b)) ∧
    edgeFun (fun j : Fin 9 => j == a || j == d) = false ∧
    edgeFun (fun j : Fin 9 => j == a || j == d || j == b) = true := by
  decide

-- On the initial wire list, a wire among the nine inputs carries exactly that input bit.
lemma eval_input_wire (C : Circuit) (x : Fin 9 → Bool) (u v : Bool) (i : ℕ) (hi : i < 9) :
    (C.wires (List.ofFn x ++ [u, v])).getD i false = x ⟨i, hi⟩ := by
  rw [wiresFrom_eq_wires, wiresFrom_getD_lt _ _ _ (by simp; omega)]
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  exact ofFn_getD x i false hi


-- Setting only the wire `i` (and nothing else) makes the edge function false.
lemma edgeFun_single : ∀ i : Fin 9, edgeFun (fun j : Fin 9 => j == i) = false := by decide

end PEqualNP.Outside.L_meta_4411_aux

open PEqualNP.Outside.L_meta_4411_aux

-- Read completeness of a small circuit for the edge function of the Petersen graph minus a
-- vertex, in the normal form where the first two gates are handed in from outside.
--
-- If no gate reads the input `i` in a live position, then changing `x_i` can change no wire
-- value except the wire `i` itself. But the edge function does depend on `x_i`: there are two
-- inputs, differing only in `x_i`, on which the two supplied `OR` gates have the same values and
-- the edge function differs. Unless the output wire *is* the input wire `i` — and it cannot be,
-- because then the circuit would compute the projection `x_i`, which is false at the input where
-- only `i` is set while the edge function is true. So the output would change as well: a
-- contradiction.
theorem PEqualNP.Outside.L_meta_4411 :
  ∀ (x1 x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), x1 ≠ (0 : Fin (9 : ℕ)) → x1 ≠ (4 : Fin (9 : ℕ)) → x2 ≠ (0 : Fin (9 : ℕ)) → x2 ≠ (4 : Fin (9 : ℕ)) → x1 ≠ x2 → PEqualNP.MetaComplexity.FanInTwo x3 → (∀ (x10 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn x10 ++ [x10 (0 : Fin (9 : ℕ)) || x10 (4 : Fin (9 : ℕ)), x10 x1 || x10 x2]) = (x10 (0 : Fin (9 : ℕ)) && x10 (1 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (2 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (3 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (4 : Fin (9 : ℕ)) || x10 (4 : Fin (9 : ℕ)) && x10 (0 : Fin (9 : ℕ)) || x10 (0 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ)) || x10 (1 : Fin (9 : ℕ)) && x10 (6 : Fin (9 : ℕ)) || x10 (2 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (3 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (5 : Fin (9 : ℕ)) && x10 (7 : Fin (9 : ℕ)) || x10 (6 : Fin (9 : ℕ)) && x10 (8 : Fin (9 : ℕ)) || x10 (8 : Fin (9 : ℕ)) && x10 (5 : Fin (9 : ℕ)))) → ∀ (x11 : Fin (9 : ℕ)), ∃ x12 ∈ x3.gates, ↑x11 ∈ if x12.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x12.inputs else x12.inputs := by
  intro x1 x2 x3 h1n0 h1n4 h2n0 h2n4 h12 hfan hcomp x11
  have hfun : ∀ x : Fin 9 → Bool,
      x3.eval (List.ofFn x ++ [x 0 || x 4, x x1 || x x2]) = edgeFun x := by
    intro x
    simpa [edgeFun] using hcomp x
  by_contra hcon
  have hnolive : ∀ g ∈ x3.gates, (x11 : ℕ) ∉ liveInputs g := by
    intro g hg hmem
    exact hcon ⟨g, hg, hmem⟩
  have hfan' : ∀ g ∈ x3.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) := by
    intro g hg
    exact (hfan g hg).1
  -- the output wire is not the unread input
  have hout : x3.output ≠ (x11 : ℕ) := by
    intro hout
    have hr : (x3.wires (List.ofFn (fun j : Fin 9 => j == x11)
        ++ [(fun j : Fin 9 => j == x11) 0 || (fun j : Fin 9 => j == x11) 4,
            (fun j : Fin 9 => j == x11) x1 || (fun j : Fin 9 => j == x11) x2])).getD
          x3.output false = edgeFun (fun j : Fin 9 => j == x11) := by
      simpa [Circuit.eval] using hfun (fun j : Fin 9 => j == x11)
    rw [hout] at hr
    have hleft : (x3.wires (List.ofFn (fun j : Fin 9 => j == x11)
        ++ [(fun j : Fin 9 => j == x11) 0 || (fun j : Fin 9 => j == x11) 4,
            (fun j : Fin 9 => j == x11) x1 || (fun j : Fin 9 => j == x11) x2])).getD
          (x11 : ℕ) false = true := by
      rw [eval_input_wire x3 (fun j : Fin 9 => j == x11) _ _ (x11 : ℕ) x11.isLt]
      simp
    rw [hleft, edgeFun_single x11] at hr
    exact Bool.noConfusion hr
  -- the witness pair: same wire values except at `i`, different edge function
  have key : ∃ p q : Fin 9 → Bool,
      (∀ j : Fin 9, (j : ℕ) ≠ (x11 : ℕ) → p j = q j) ∧
      (p 0 || p 4) = (q 0 || q 4) ∧
      (p x1 || p x2) = (q x1 || q x2) ∧
      edgeFun p ≠ edgeFun q := by
    by_cases h0 : x11 = (0 : Fin 9)
    · refine ⟨fun j => j == (4 : Fin 9), fun j => j == (4 : Fin 9) || j == (0 : Fin 9),
        ?_, ?_, ?_, ?_⟩
      · intro j hj
        have hj' : j ≠ (0 : Fin 9) := by
          intro h
          exact hj (by simp [h, h0])
        exact (witness_zero x1 x2 h1n0 h2n0).1 j hj'
      · exact (witness_zero x1 x2 h1n0 h2n0).2.1
      · exact (witness_zero x1 x2 h1n0 h2n0).2.2.1
      · intro heq
        rw [(witness_zero x1 x2 h1n0 h2n0).2.2.2.1,
          (witness_zero x1 x2 h1n0 h2n0).2.2.2.2] at heq
        exact Bool.noConfusion heq
    · by_cases h4 : x11 = (4 : Fin 9)
      · refine ⟨fun j => j == (0 : Fin 9), fun j => j == (0 : Fin 9) || j == (4 : Fin 9),
          ?_, ?_, ?_, ?_⟩
        · intro j hj
          have hj' : j ≠ (4 : Fin 9) := by
            intro h
            exact hj (by simp [h, h4])
          exact (witness_four x1 x2 h1n4 h2n4).1 j hj'
        · exact (witness_four x1 x2 h1n4 h2n4).2.1
        · exact (witness_four x1 x2 h1n4 h2n4).2.2.1
        · intro heq
          rw [(witness_four x1 x2 h1n4 h2n4).2.2.2.1,
            (witness_four x1 x2 h1n4 h2n4).2.2.2.2] at heq
          exact Bool.noConfusion heq
      · by_cases hA : x11 = x1
        · obtain ⟨d, had, hbd, hdb⟩ := escape x1 x2 h12 h1n0 h1n4 h2n0 h2n4
          refine ⟨fun j => j == x2 || j == d, fun j => j == x2 || j == d || j == x1,
            ?_, ?_, ?_, ?_⟩
          · intro j hj
            have hj' : j ≠ x1 := by
              intro h
              exact hj (by simp [h, hA])
            exact (witness_first x1 x2 d h12 had hbd hdb h1n0 h1n4).1 j hj'
          · exact (witness_first x1 x2 d h12 had hbd hdb h1n0 h1n4).2.1
          · exact (witness_first x1 x2 d h12 had hbd hdb h1n0 h1n4).2.2.1
          · intro heq
            rw [(witness_first x1 x2 d h12 had hbd hdb h1n0 h1n4).2.2.2.1,
              (witness_first x1 x2 d h12 had hbd hdb h1n0 h1n4).2.2.2.2] at heq
            exact Bool.noConfusion heq
        · by_cases hB : x11 = x2
          · obtain ⟨d, hbd, had, hda⟩ := escape x2 x1 h12.symm h2n0 h2n4 h1n0 h1n4
            refine ⟨fun j => j == x1 || j == d, fun j => j == x1 || j == d || j == x2,
              ?_, ?_, ?_, ?_⟩
            · intro j hj
              have hj' : j ≠ x2 := by
                intro h
                exact hj (by simp [h, hB])
              exact (witness_second x1 x2 d h12 hbd had hda h2n0 h2n4).1 j hj'
            · exact (witness_second x1 x2 d h12 hbd had hda h2n0 h2n4).2.1
            · exact (witness_second x1 x2 d h12 hbd had hda h2n0 h2n4).2.2.1
            · intro heq
              rw [(witness_second x1 x2 d h12 hbd had hda h2n0 h2n4).2.2.2.1,
                (witness_second x1 x2 d h12 hbd had hda h2n0 h2n4).2.2.2.2] at heq
              exact Bool.noConfusion heq
          · obtain ⟨d, had⟩ := exists_adj x11
            refine ⟨fun j => j == d, fun j => j == d || j == x11, ?_, ?_, ?_, ?_⟩
            · intro j hj
              have hj' : j ≠ x11 := by
                intro h
                exact hj (by simp [h])
              exact (witness_generic x11 d x1 x2 had h0 h4 hA hB).1 j hj'
            · exact (witness_generic x11 d x1 x2 had h0 h4 hA hB).2.1
            · exact (witness_generic x11 d x1 x2 had h0 h4 hA hB).2.2.1
            · intro heq
              rw [(witness_generic x11 d x1 x2 had h0 h4 hA hB).2.2.2.1,
                (witness_generic x11 d x1 x2 had h0 h4 hA hB).2.2.2.2] at heq
              exact Bool.noConfusion heq
  obtain ⟨p, q, hpq, hf9, hf10, hne⟩ := key
  have hlen : (List.ofFn p ++ [p 0 || p 4, p x1 || p x2]).length
      = (List.ofFn q ++ [q 0 || q 4, q x1 || q x2]).length := by simp
  have hind := wiresFrom_agree x3.gates (x11 : ℕ) hfan' hnolive
    (List.ofFn p ++ [p 0 || p 4, p x1 || p x2])
    (List.ofFn q ++ [q 0 || q 4, q x1 || q x2]) hlen
    (agree_ofFn p q (p 0 || p 4) (p x1 || p x2) (q 0 || q 4) (q x1 || q x2)
      (x11 : ℕ) hpq hf9 hf10) x3.output hout
  have hpe : edgeFun p
      = (wiresFrom x3.gates (List.ofFn p ++ [p 0 || p 4, p x1 || p x2])).getD
          x3.output false := by
    simpa [Circuit.eval, wiresFrom_eq_wires] using (hfun p).symm
  have hqe : edgeFun q
      = (wiresFrom x3.gates (List.ofFn q ++ [q 0 || q 4, q x1 || q x2])).getD
          x3.output false := by
    simpa [Circuit.eval, wiresFrom_eq_wires] using (hfun q).symm
  exact hne (by rw [hpe, hqe]; exact hind)
