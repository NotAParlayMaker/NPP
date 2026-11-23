import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.BigOperators
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_152_aux

open PEqualNP.CircuitLowerBounds

-- Basic wire identities from L-meta-717.
def stepWires (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]

def runWires (m : ℕ) (gs : List Gate) (x : Fin m → Bool) : List Bool :=
  gs.foldl stepWires (List.ofFn x)

def wireVal (m : ℕ) (gs : List Gate) (x : Fin m → Bool) (i : ℕ) : Bool :=
  (runWires m gs x).getD i false

def wireAt (m : ℕ) (gs : List Gate) (bound i : ℕ) (x : Fin m → Bool) : Bool :=
  if i < bound then wireVal m gs x i else false

lemma foldl_stepWires_length (gs : List Gate) (ws : List Bool) :
    (gs.foldl stepWires ws).length = ws.length + gs.length := by
  induction gs generalizing ws with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons, ih, stepWires, List.length_append]
    simp only [List.length_nil]
    omega

lemma runWires_length (m : ℕ) (gs : List Gate) (x : Fin m → Bool) :
    (runWires m gs x).length = m + gs.length := by
  unfold runWires
  rw [foldl_stepWires_length, List.length_ofFn]

lemma foldl_stepWires_getD_lt (gs : List Gate) (ws : List Bool) {i : ℕ} (hi : i < ws.length) :
    (gs.foldl stepWires ws).getD i false = ws.getD i false := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWires ws g).length := by
      simp only [stepWires, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (stepWires ws g) hlt, List.getD_eq_getElem _ _ hlt, List.getD_eq_getElem _ _ hi]
    simp only [stepWires, List.getElem_append_left hi]

lemma wireVal_input (m : ℕ) (gs : List Gate) (x : Fin m → Bool) (v : Fin m) :
    wireVal m gs x v.val = x v := by
  unfold wireVal runWires
  have hv : v.val < (List.ofFn x).length := by simp
  rw [foldl_stepWires_getD_lt gs (List.ofFn x) hv, List.getD_eq_getElem _ _ hv, List.getElem_ofFn]

lemma wireVal_of_ge (m : ℕ) (gs : List Gate) (x : Fin m → Bool) {i : ℕ} (hi : m + gs.length ≤ i) :
    wireVal m gs x i = false := by
  unfold wireVal
  rw [List.getD_eq_default]
  rw [runWires_length]
  exact hi

lemma wireVal_gate (m : ℕ) (gs : List Gate) (x : Fin m → Bool) {k : ℕ} (hk : k < gs.length) :
    wireVal m gs x (m + k) =
      (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i => wireAt m gs (m + k) i x) := by
  unfold wireVal runWires
  have hsplit : gs = gs.take k ++ (gs[k]'hk) :: gs.drop (k + 1) := by
    simp
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  set ws := (gs.take k).foldl stepWires (List.ofFn x)
  have hws_len : ws.length = m + k := by
    rw [foldl_stepWires_length, List.length_ofFn, List.length_take]
    omega
  have hstep_len : (stepWires ws (gs[k]'hk)).length = m + k + 1 := by
    simp [stepWires, hws_len]
  have hlt : m + k < (stepWires ws (gs[k]'hk)).length := by omega
  rw [foldl_stepWires_getD_lt (gs.drop (k + 1)) (stepWires ws (gs[k]'hk)) hlt]
  have hlast : (stepWires ws (gs[k]'hk)).getD (m + k) false =
      (gs[k]'hk).op.eval ((gs[k]'hk).inputs.map fun i => ws.getD i false) := by
    rw [List.getD_eq_getElem _ _ hlt]
    simp [stepWires, hws_len]
  rw [hlast]
  congr 1
  apply List.map_congr_left
  intro i _
  unfold wireAt
  split_ifs with hi
  · have hi_ws : i < ws.length := by omega
    have hsplit2 : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    symm
    unfold wireVal runWires
    rw [hsplit2, List.foldl_append]
    exact foldl_stepWires_getD_lt (gs.drop k) ws hi_ws
  · rw [List.getD_eq_default]
    omega

-- At each AND gate, record the value of its first operand.
def gateChoice {n : ℕ} (C : Circuit) (A : Finset ℕ) (x : Fin n → Bool) (j : A) : Bool :=
  match ((C.gates[j.val]?).map Gate.inputs).getD [] with
  | a :: _ => wireAt n C.gates (n+j.val) a x
  | [] => false

-- Inputs with the same recorded bits have a rejected union whenever both are rejected.
theorem union_comparison {n : ℕ} (C : Circuit) (A : Finset ℕ)
    (mono : PEqualNP.MetaComplexity.Monotone2 C)
    (cover : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A)
    (x y : Fin n → Bool) (same : gateChoice C A x = gateChoice C A y) (w : ℕ) :
    wireVal n C.gates (fun i => x i || y i) w = true →
      wireVal n C.gates x w = true ∨ wireVal n C.gates y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · let i : Fin n := ⟨w,hw⟩
      change wireVal n C.gates _ i.val = true →
        wireVal n C.gates x i.val = true ∨ wireVal n C.gates y i.val = true
      simp only [wireVal_input, Bool.or_eq_true]
      exact fun h => h
    by_cases ht : n + C.gates.length ≤ w
    · simp [wireVal_of_ge n C.gates _ ht]
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hw)
    have hj : j < C.gates.length := by omega
    have hs := mono C.gates[j] (List.getElem_mem hj)
    have op : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or := hs.1
    have inputs := hs.2
    have transfer (a : ℕ) :
        wireAt n C.gates (n+j) a (fun i => x i || y i) = true →
        wireAt n C.gates (n+j) a x = true ∨ wireAt n C.gates (n+j) a y = true := by
      by_cases ha : a < n+j
      · simpa only [wireAt,ite_eq_left ha] using ih a ha
      · simp [wireAt,ha]
    rw [wireVal_gate n C.gates _ hj,wireVal_gate n C.gates x hj,wireVal_gate n C.gates y hj]
    cases hab : C.gates[j].inputs with
    | nil => rcases op with h|h <;> simp [h,GateOp.eval]
    | cons a rest =>
      cases hrest : rest with
      | nil =>
        rcases op with h|h <;> simp [h, GateOp.eval] <;> exact transfer a
      | cons b tail =>
        have empty : tail = [] := by
          rw [hab,hrest] at inputs
          simpa using inputs
        subst tail
        rcases op with h|h
        · have ja := cover j _ (List.getElem?_eq_getElem hj) h
          have equal := congrFun same ⟨j,ja⟩
          simp only [gateChoice,List.getElem?_eq_getElem hj,Option.map_some,Option.getD_some,
            hab,hrest] at equal
          simp only [h,List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,
            id,Bool.and_true,Bool.and_eq_true]
          intro ⟨ha,hb⟩
          have both : wireAt n C.gates (n+j) a x = true ∧ wireAt n C.gates (n+j) a y = true := by
            rcases transfer a ha with t|t
            · exact ⟨t,equal ▸ t⟩
            · exact ⟨equal.symm ▸ t,t⟩
          exact (transfer b hb).elim (fun t => Or.inl ⟨both.1,t⟩) (fun t => Or.inr ⟨both.2,t⟩)
        · simp only [h,List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,
            id,Bool.or_false,Bool.or_eq_true]
          intro hh
          rcases hh with ha|hb
          · exact (transfer a ha).elim (fun t => Or.inl (Or.inl t)) (fun t => Or.inr (Or.inl t))
          · exact (transfer b hb).elim (fun t => Or.inl (Or.inr t)) (fun t => Or.inr (Or.inr t))

-- The three maximal independent sets of the four-vertex path.
def pattern (i : Fin 3) (p : Fin 4) : Bool :=
  decide (p ∈ (![({0,2} : Finset (Fin 4)),{0,3},{1,3}] i))

def hasEdge (x : Fin 4 → Bool) : Prop :=
  ∃ u v : Fin 4, u.val + 1 = v.val ∧ x u = true ∧ x v = true

end PEqualNP.Outside.L_meta_152_aux

open PEqualNP.Outside.L_meta_152_aux

theorem PEqualNP.Outside.L_meta_152 : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ 1 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) ∧ ∀ x : Fin 4 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 4, u.val + 1 = v.val ∧ x u = true ∧ x v = true) := by
  rintro ⟨C, hm, ⟨A, hcard, cover⟩, correct⟩
  have quiet : ∀ i, ¬hasEdge (pattern i) := by unfold hasEdge; decide
  have loud : ∀ i j, i ≠ j → hasEdge (fun p => pattern i p || pattern j p) := by
    unfold hasEdge
    decide
  have inj : Function.Injective (fun i => gateChoice C A (pattern i)) := by
    intro i j same
    by_contra h
    have positive := (correct _).2 (loud i j h)
    have one := union_comparison C A hm cover (pattern i) (pattern j) same C.output positive
    exact one.elim (fun t => quiet i ((correct _).1 t)) (fun t => quiet j ((correct _).1 t))
  have count : 3 ≤ 2 ^ A.card := by simpa using Fintype.card_le_of_injective _ inj
  have limit : 2 ^ A.card ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) hcard
  omega
