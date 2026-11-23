import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_245

open PEqualNP.CircuitLowerBounds

def idx (a b c d : Bool) : ℕ := a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat

def fP (a b c d : Bool) : Bool := (a && b) || (b && c) || (c && d)

def base : List ℕ := [43690, 52428, 61680, 65280]

def opT : GateOp → List ℕ → ℕ
  | GateOp.and, l => l.foldr (fun a acc => a &&& acc) 65535
  | GateOp.or, l => l.foldr (fun a acc => a ||| acc) 0
  | GateOp.not, l => 65535 ^^^ (l.headD 0)
  | _, _ => 0

def newT (T : List ℕ) (g : Gate) : ℕ := opT g.op (g.inputs.map fun i => T.getD i 0)

def snoc (T : List ℕ) (t : ℕ) : List ℕ := T ++ [t]

def stepT (T : List ℕ) (g : Gate) : List ℕ := snoc T (newT T g)

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Inv (m : ℕ) (w : List Bool) (T : List ℕ) : Prop :=
  w.length = T.length ∧ ∀ i, w.getD i false = (T.getD i 0).testBit m

def Allowed (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

lemma idx_lt (a b c d : Bool) : idx a b c d < 16 := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

lemma inv_base (a b c d : Bool) : Inv (idx a b c d) [a, b, c, d] base := by
  refine ⟨rfl, ?_⟩
  intro i
  rcases i with _ | _ | _ | _ | i
  · cases a <;> cases b <;> cases c <;> cases d <;> decide
  · cases a <;> cases b <;> cases c <;> cases d <;> decide
  · cases a <;> cases b <;> cases c <;> cases d <;> decide
  · cases a <;> cases b <;> cases c <;> cases d <;> decide
  · simp [base]

lemma full_bit (m : ℕ) (hm : m < 16) : (65535 : ℕ).testBit m = true := by
  interval_cases m <;> decide

lemma and_corr (m : ℕ) (hm : m < 16) (w : List Bool) (T : List ℕ) (hI : Inv m w T)
    (l : List ℕ) :
    (l.map fun i => w.getD i false).all id =
      ((l.map fun i => T.getD i 0).foldr (fun a acc => a &&& acc) 65535).testBit m := by
  induction l with
  | nil => simp [full_bit m hm]
  | cons i l ih =>
    simp only [List.map_cons, List.all_cons, List.foldr_cons, Nat.testBit_and, id]
    rw [ih, hI.2 i]

lemma or_corr (m : ℕ) (w : List Bool) (T : List ℕ) (hI : Inv m w T) (l : List ℕ) :
    (l.map fun i => w.getD i false).any id =
      ((l.map fun i => T.getD i 0).foldr (fun a acc => a ||| acc) 0).testBit m := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.any_cons, List.foldr_cons, Nat.testBit_or, id]
    rw [ih, hI.2 i]

lemma op_corr (m : ℕ) (hm : m < 16) (w : List Bool) (T : List ℕ) (hI : Inv m w T)
    (g : Gate) (hg : Allowed g) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = (newT T g).testBit m := by
  unfold newT
  rcases hg.1 with h | h | h
  · rw [h]
    exact and_corr m hm w T hI g.inputs
  · rw [h]
    exact or_corr m w T hI g.inputs
  · rw [h]
    simp only [GateOp.eval, opT]
    rcases g.inputs with _ | ⟨i, l⟩
    · simp [full_bit m hm]
    · simp only [List.map_cons, List.headD_cons, Nat.testBit_xor, full_bit m hm, Bool.true_xor]
      rw [hI.2 i]

lemma inv_step (m : ℕ) (hm : m < 16) (w : List Bool) (T : List ℕ) (hI : Inv m w T)
    (g : Gate) (hg : Allowed g) : Inv m (stepW w g) (stepT T g) := by
  refine ⟨by simp [stepW, stepT, snoc, hI.1], ?_⟩
  intro i
  have hc := op_corr m hm w T hI g hg
  have hl := hI.1
  show (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD i false =
    ((T ++ [newT T g]).getD i 0).testBit m
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rcases Nat.lt_trichotomy i w.length with h | h | h
  · have h' : i < T.length := by omega
    rw [List.getElem?_append_left h, List.getElem?_append_left h']
    have h3 := hI.2 i
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at h3
    exact h3
  · have e1 : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])[i]? =
        some (g.op.eval (g.inputs.map fun i => w.getD i false)) := by
      rw [h]
      exact List.getElem?_concat_length
    have e2 : (T ++ [newT T g])[i]? = some (newT T g) := by
      rw [h, hl]
      exact List.getElem?_concat_length
    rw [e1, e2]
    exact hc
  · have e1 : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])[i]? = none :=
      List.getElem?_eq_none (by simp; omega)
    have e2 : (T ++ [newT T g])[i]? = none := List.getElem?_eq_none (by simp; omega)
    rw [e1, e2]
    simp

lemma inv_fold (m : ℕ) (hm : m < 16) (gs : List Gate) (hgs : ∀ g ∈ gs, Allowed g)
    (w : List Bool) (T : List ℕ) (hI : Inv m w T) :
    Inv m (gs.foldl stepW w) (gs.foldl stepT T) := by
  induction gs generalizing w T with
  | nil => exact hI
  | cons g gs ih =>
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _
      (inv_step m hm w T hI g (hgs g (List.mem_cons_self)))

def cands (T : List ℕ) : List (List ℕ) :=
  [] :: (((0 :: T).map fun a => [a]) ++ ((0 :: T).flatMap fun a => (0 :: T).map fun b => [a, b]))

def next (T : List ℕ) : List ℕ :=
  ([GateOp.and, GateOp.or, GateOp.not].flatMap fun op => (cands T).map (opT op)).dedup

lemma getD_mem (T : List ℕ) (i : ℕ) : T.getD i 0 ∈ 0 :: T := by
  by_cases h : i < T.length
  · have : T.getD i 0 = T[i] := by simp [List.getD_eq_getElem?_getD, h]
    rw [this]
    exact List.mem_cons_of_mem _ (List.getElem_mem h)
  · have : T.getD i 0 = 0 := List.getD_eq_default _ _ (by omega)
    rw [this]
    exact List.mem_cons_self

lemma mem_next (T : List ℕ) (g : Gate) (hg : Allowed g) : newT T g ∈ next T := by
  unfold next newT
  rw [List.mem_dedup, List.mem_flatMap]
  refine ⟨g.op, ?_, ?_⟩
  · rcases hg.1 with h | h | h <;> rw [h] <;> simp
  · apply List.mem_map_of_mem
    have hlen := hg.2
    unfold cands
    rcases hin : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k, l⟩⟩⟩
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_left _
        (List.mem_map_of_mem (f := fun a => [a]) (getD_mem T i)))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨T.getD i 0, getD_mem T i,
          List.mem_map_of_mem (f := fun b => [T.getD i 0, b]) (getD_mem T j)⟩))
    · rw [hin] at hlen
      simp at hlen

lemma mem_snoc (x t : ℕ) (T : List ℕ) (h : x ∈ 0 :: snoc T t) : x ∈ 0 :: T ∨ x = t := by
  simp only [snoc, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h ⊢
  tauto

def all16 : List (Bool × Bool × Bool × Bool) :=
  [false, true].flatMap fun a => [false, true].flatMap fun b =>
    [false, true].flatMap fun c => [false, true].map fun d => (a, b, c, d)

def sig (t : ℕ) : List Bool := all16.map fun q => t.testBit (idx q.1 q.2.1 q.2.2.1 q.2.2.2)

def sigF : List Bool := all16.map fun q => fP q.1 q.2.1 q.2.2.1 q.2.2.2

def bad (t : ℕ) : Bool := decide (sig t = sigF)

def chk : Bool :=
  ((0 :: base).all fun t => !(bad t)) &&
  (next base).all fun t1 => !(bad t1) &&
    (next (snoc base t1)).all fun t2 => !(bad t2) &&
      (next (snoc (snoc base t1) t2)).all fun t3 => !(bad t3)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma chk_true : chk = true := by
  decide +kernel

lemma bad_of (t : ℕ) (H : ∀ a b c d : Bool, fP a b c d = t.testBit (idx a b c d)) :
    bad t = true := by
  unfold bad
  rw [decide_eq_true_eq]
  unfold sig sigF
  apply List.map_congr_left
  intro q _
  exact (H q.1 q.2.1 q.2.2.1 q.2.2.2).symm

lemma no_small (D : Circuit) (hD : ∀ g ∈ D.gates, Allowed g) (hs : D.gates.length ≤ 3)
    (H : ∀ a b c d : Bool, D.eval [a, b, c, d] = fP a b c d) : False := by
  have hb : bad ((D.gates.foldl stepT base).getD D.output 0) = true := by
    apply bad_of
    intro a b c d
    rw [← H a b c d]
    exact (inv_fold (idx a b c d) (idx_lt a b c d) D.gates hD _ _ (inv_base a b c d)).2 D.output
  have hmem := getD_mem (D.gates.foldl stepT base) D.output
  have hc := chk_true
  simp only [chk, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨h0, h1⟩ := hc
  have fin : ∀ t : ℕ, bad t = true → bad t = false → False := by
    intro t p q
    rw [q] at p
    exact absurd p (by simp)
  rcases hgs : D.gates with _ | ⟨g1, _ | ⟨g2, _ | ⟨g3, _ | ⟨g4, rest⟩⟩⟩⟩
  · rw [hgs] at hmem hb
    simp only [List.foldl_nil] at hmem hb
    exact fin _ hb (h0 _ hmem)
  · rw [hgs] at hmem hb hD
    have a1 := mem_next base g1 (hD g1 (by simp))
    obtain ⟨b1, _⟩ := h1 _ a1
    simp only [List.foldl_cons, List.foldl_nil, stepT] at hmem hb
    rcases mem_snoc _ _ _ hmem with e | e
    · exact fin _ hb (h0 _ e)
    · rw [e] at hb
      exact fin _ hb b1
  · rw [hgs] at hmem hb hD
    have a1 := mem_next base g1 (hD g1 (by simp))
    obtain ⟨b1, h2⟩ := h1 _ a1
    have a2 := mem_next (snoc base (newT base g1)) g2 (hD g2 (by simp))
    obtain ⟨b2, _⟩ := h2 _ a2
    simp only [List.foldl_cons, List.foldl_nil, stepT] at hmem hb
    rcases mem_snoc _ _ _ hmem with e | e
    · rcases mem_snoc _ _ _ e with e | e
      · exact fin _ hb (h0 _ e)
      · rw [e] at hb
        exact fin _ hb b1
    · rw [e] at hb
      exact fin _ hb b2
  · rw [hgs] at hmem hb hD
    have a1 := mem_next base g1 (hD g1 (by simp))
    obtain ⟨b1, h2⟩ := h1 _ a1
    have a2 := mem_next (snoc base (newT base g1)) g2 (hD g2 (by simp))
    obtain ⟨b2, h3⟩ := h2 _ a2
    have a3 := mem_next (snoc (snoc base (newT base g1)) (newT (snoc base (newT base g1)) g2)) g3
      (hD g3 (by simp))
    have b3 := h3 _ a3
    simp only [List.foldl_cons, List.foldl_nil, stepT] at hmem hb
    rcases mem_snoc _ _ _ hmem with e | e
    · rcases mem_snoc _ _ _ e with e | e
      · rcases mem_snoc _ _ _ e with e | e
        · exact fin _ hb (h0 _ e)
        · rw [e] at hb
          exact fin _ hb b1
      · rw [e] at hb
        exact fin _ hb b2
    · rw [e] at hb
      exact fin _ hb b3
  · rw [hgs] at hs
    simp at hs
    omega

def circ : Circuit :=
  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [4, 2]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [5, 6]⟩], 7⟩

lemma ofFn4 (x : Fin 4 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3] := by
  rfl

lemma circ_eval : ∀ a b c d : Bool, circ.eval [a, b, c, d] = fP a b c d := by
  decide

lemma circ_fan : PEqualNP.MetaComplexity.FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_245

theorem PEqualNP.Outside.L_meta_245 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩], 7⟩ → PEqualNP.MetaComplexity.IsMinimalCircuit 4 C ∧ PEqualNP.MetaComplexity.circuitFun 4 C = (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)) ∧ C.gates[3]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩ := by
  intro C hC
  subst hC
  refine ⟨⟨PEqualNP.Outside.L_meta_245.circ_fan, fun D hD hfun => ?_⟩, ?_, rfl⟩
  · by_contra hlt
    have hs : D.gates.length ≤ 3 := by
      simp only [PEqualNP.CircuitLowerBounds.Circuit.size, List.length_cons, List.length_nil,
        not_le] at hlt
      omega
    apply PEqualNP.Outside.L_meta_245.no_small D _ hs
    · intro a b c d
      have h1 := congrFun hfun (fun i : Fin 4 => [a, b, c, d].getD i.val false)
      exact (show D.eval [a, b, c, d] = PEqualNP.Outside.L_meta_245.circ.eval [a, b, c, d] from h1).trans
        (PEqualNP.Outside.L_meta_245.circ_eval a b c d)
    · intro g hg
      obtain ⟨h1, h2⟩ := hD g hg
      exact ⟨by simpa using h1, h2⟩
  · funext x
    show PEqualNP.Outside.L_meta_245.circ.eval (List.ofFn x) = _
    rw [PEqualNP.Outside.L_meta_245.ofFn4 x]
    exact PEqualNP.Outside.L_meta_245.circ_eval (x 0) (x 1) (x 2) (x 3)
