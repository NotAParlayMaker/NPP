import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9019

open PEqualNP.CircuitLowerBounds

/-! ## Composition

The definitions and lemmas up to `compose` are copied from the merged step L-meta-9018
(author Bastian Milan): a prefix of gates computing given wires, followed by a circuit reading
those wires. -/

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len_foldl (G : List Gate) (s : List Bool) :
    (G.foldl step s).length = s.length + G.length := by
  induction G generalizing s with
  | nil => simp
  | cons g G ih => simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons,
      List.length_nil]; omega

def remap (L M K : ℕ) (w : Fin L → ℕ) (i : ℕ) : ℕ :=
  if h : i < L then (if w ⟨i, h⟩ < M then w ⟨i, h⟩ else M + K) else M + (i - L)

def mapGate (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

theorem main (W y : List Bool) (r : ℕ → ℕ) (K : ℕ)
    (hr : ∀ E : List Bool, E.length ≤ K → ∀ i, (W ++ E).getD (r i) false = (y ++ E).getD i false) :
    ∀ (G : List Gate) (E : List Bool), E.length + G.length ≤ K →
      ∃ E' : List Bool, E'.length = E.length + G.length ∧
        (G.map (mapGate r)).foldl step (W ++ E) = W ++ E' ∧ G.foldl step (y ++ E) = y ++ E' := by
  intro G
  induction G with
  | nil => intro E _; exact ⟨E, by simp, by simp, by simp⟩
  | cons g G ih =>
    intro E hE
    simp only [List.length_cons] at hE
    have hv : (g.inputs.map r).map (fun i => (W ++ E).getD i false)
        = g.inputs.map (fun i => (y ++ E).getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      exact hr E (by omega) i
    obtain ⟨E', h1, h2, h3⟩ :=
      ih (E ++ [g.op.eval (g.inputs.map fun i => (y ++ E).getD i false)])
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    refine ⟨E', ?_, ?_, ?_⟩
    · rw [h1]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · simp only [List.map_cons, List.foldl_cons]
      have : step (W ++ E) (mapGate r g)
          = W ++ (E ++ [g.op.eval (g.inputs.map fun i => (y ++ E).getD i false)]) := by
        simp only [step, mapGate]
        rw [hv, List.append_assoc]
      rw [this, h2]
    · simp only [List.foldl_cons]
      have : step (y ++ E) g
          = y ++ (E ++ [g.op.eval (g.inputs.map fun i => (y ++ E).getD i false)]) := by
        simp only [step, List.append_assoc]
      rw [this, h3]

theorem getD_left (l l' : List Bool) (n : ℕ) (h : n < l.length) :
    (l ++ l').getD n false = l.getD n false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_right (l l' : List Bool) (n : ℕ) (h : l.length ≤ n) :
    (l ++ l').getD n false = l'.getD (n - l.length) false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_big (l : List Bool) (n : ℕ) (h : l.length ≤ n) : l.getD n false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

theorem hr_of (L M K : ℕ) (w : Fin L → ℕ) (W : List Bool) (v : Fin L → Bool)
    (hW : W.length = M) (hw : ∀ j, W.getD (w j) false = v j) :
    ∀ E : List Bool, E.length ≤ K → ∀ i,
      (W ++ E).getD (remap L M K w i) false = (List.ofFn v ++ E).getD i false := by
  intro E hE i
  unfold remap
  by_cases h : i < L
  · rw [dif_pos h, getD_left (List.ofFn v) E i (by simp [h])]
    have hy : (List.ofFn v).getD i false = v ⟨i, h⟩ := by
      simp [List.getD_eq_getElem?_getD, h]
    rw [hy]
    by_cases h2 : w ⟨i, h⟩ < M
    · rw [if_pos h2, getD_left _ _ _ (by omega), hw]
    · rw [if_neg h2, ← hw, getD_big _ _ (by simp; omega), getD_big W _ (by omega)]
  · rw [dif_neg h, getD_right _ _ _ (by omega), getD_right _ _ _ (by simp; omega)]
    simp only [List.length_ofFn]
    congr 1
    omega

theorem compose : ∀ (N L : ℕ) (D : Set (List Bool)) (P : List PEqualNP.CircuitLowerBounds.Gate) (w : Fin L → ℕ) (g : Fin L → List Bool → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ x ∈ D, x.length = N) → PEqualNP.MetaComplexity.Monotone2 (⟨P, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x ∈ D, ∀ j, ((⟨P, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires x).getD (w j) false = g j x) → ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C' ∧ C'.size ≤ P.length + C.size ∧ ∀ x ∈ D, C'.eval x = C.eval (List.ofFn fun j => g j x) := by
  intro N L D P w g C hD hP hC hw
  let M := N + P.length
  let K := C.gates.length
  let r := remap L M K w
  refine ⟨⟨P ++ C.gates.map (mapGate r), r C.output⟩, ?_, ?_, ?_⟩
  · intro gt hgt
    rw [List.mem_append] at hgt
    rcases hgt with hgt | hgt
    · exact hP gt hgt
    · rw [List.mem_map] at hgt
      obtain ⟨g0, hg0, rfl⟩ := hgt
      obtain ⟨h1, h2⟩ := hC g0 hg0
      exact ⟨h1, by simp only [mapGate, List.length_map]; exact h2⟩
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x hx
    have hWlen : ((⟨P, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires x).length = M := by
      show (P.foldl step x).length = M
      rw [len_foldl, hD x hx]
    have hr := hr_of L M K w ((⟨P, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires x)
      (fun j => g j x) hWlen (hw x hx)
    obtain ⟨E', h1, h2, h3⟩ := main _ _ r K hr C.gates [] (by simp [K])
    simp only [List.append_nil] at h2 h3
    show ((P ++ C.gates.map (mapGate r)).foldl step x).getD (r C.output) false
      = (C.gates.foldl step (List.ofFn fun j => g j x)).getD C.output false
    rw [List.foldl_append]
    have hPw : P.foldl step x = (⟨P, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires x := rfl
    rw [hPw, h2, h3]
    exact hr E' (by simp at h1; omega) C.output

/-! ## Gate lists over known wires -/

theorem getD_snoc (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem foldl_getD_lt (G : List Gate) : ∀ (W : List Bool) (i : ℕ), i < W.length →
    (G.foldl step W).getD i false = W.getD i false := by
  induction G with
  | nil => intro W i _; rfl
  | cons g G ih =>
    intro W i hi
    rw [List.foldl_cons, ih _ i (by simp only [step, List.length_append, List.length_singleton]; omega)]
    exact getD_left W _ i hi

/-- Gates reading only the given wires all see the same wires. -/
theorem foldl_par (G : List Gate) : ∀ W : List Bool, (∀ g ∈ G, ∀ i ∈ g.inputs, i < W.length) →
    G.foldl step W = W ++ G.map (fun g => g.op.eval (g.inputs.map fun i => W.getD i false)) := by
  induction G with
  | nil => intro W _; simp
  | cons g G ih =>
    intro W h
    rw [List.foldl_cons]
    have h1 : step W g = W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)] := rfl
    rw [ih _ (fun g' hg' i hi => by
      have := h g' (List.mem_cons_of_mem _ hg') i hi
      rw [h1, List.length_append, List.length_singleton]; omega)]
    rw [h1, List.append_assoc, List.map_cons, List.singleton_append]
    congr 2
    apply List.map_congr_left
    intro g' hg'
    congr 1
    apply List.map_congr_left
    intro i hi
    exact getD_left _ _ _ (h g' (List.mem_cons_of_mem _ hg') i hi)

/-! ## A chain of OR gates -/

/-- OR gates folding the wires of `r` into the accumulator wire `acc`, the first new wire being
`next`. -/
def chainFrom : ℕ → List ℕ → ℕ → List Gate
  | _, [], _ => []
  | acc, a :: r, next => ⟨GateOp.or, [acc, a]⟩ :: chainFrom next r (next + 1)

/-- The output wire of `chainFrom`. -/
def outFrom : ℕ → List ℕ → ℕ → ℕ
  | acc, [], _ => acc
  | _, _ :: r, next => outFrom next r (next + 1)

theorem chainFrom_len : ∀ (r : List ℕ) (acc next : ℕ), (chainFrom acc r next).length = r.length := by
  intro r
  induction r with
  | nil => intro acc next; rfl
  | cons a r ih => intro acc next; simp only [chainFrom, List.length_cons, ih]

theorem chainFrom_ops : ∀ (r : List ℕ) (acc next : ℕ), ∀ g ∈ chainFrom acc r next,
    g.op = GateOp.or ∧ g.inputs.length ≤ 2 := by
  intro r
  induction r with
  | nil => intro acc next g hg; simp [chainFrom] at hg
  | cons a r ih =>
    intro acc next g hg
    simp only [chainFrom, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨rfl, by simp⟩
    · exact ih _ _ g hg

theorem chainFrom_spec : ∀ (r : List ℕ) (acc next : ℕ) (W : List Bool), W.length = next →
    acc < next → (∀ a ∈ r, a < next) →
    outFrom acc r next < next + r.length ∧
    ((chainFrom acc r next).foldl step W).getD (outFrom acc r next) false
      = (W.getD acc false || (r.map fun a => W.getD a false).any id) := by
  intro r
  induction r with
  | nil =>
    intro acc next W _ hacc _
    refine ⟨by simp only [outFrom, List.length_nil]; omega, ?_⟩
    simp [outFrom, chainFrom]
  | cons a r ih =>
    intro acc next W hW hacc hr
    have hs : step W ⟨GateOp.or, [acc, a]⟩ = W ++ [W.getD acc false || W.getD a false] := by
      simp [step, GateOp.eval]
    have h := ih next (next + 1) (W ++ [W.getD acc false || W.getD a false]) (by simp [hW])
      (by omega) (fun b hb => by have := hr b (List.mem_cons_of_mem _ hb); omega)
    simp only [chainFrom, outFrom, List.foldl_cons, hs, List.length_cons]
    refine ⟨by omega, ?_⟩
    rw [h.2]
    have e1 : (W ++ [W.getD acc false || W.getD a false]).getD next false
        = (W.getD acc false || W.getD a false) := by
      rw [← hW]; exact getD_snoc _ _
    have e2 : (r.map fun b => (W ++ [W.getD acc false || W.getD a false]).getD b false)
        = r.map fun b => W.getD b false := by
      apply List.map_congr_left
      intro b hb
      exact getD_left _ _ _ (by rw [hW]; exact hr b (List.mem_cons_of_mem _ hb))
    rw [e1, e2]
    simp only [List.map_cons, List.any_cons, id, Bool.or_assoc]

/-! ## Literals of a one-hot vector

`ws q` (for `q < 2 ^ m`) are wires holding a one-hot vector, on at position `c`. One level folds
the pairs `2 q, 2 q + 1` with `2 ^ m` OR gates (a one-hot vector at `c / 2`) and reads bit `0` of
`c` as the OR of the odd positions and its negation as the OR of the even positions, two chains
of `2 ^ m - 1` gates. The rest is the same on the folded vector. -/

def rest (ws : ℕ → ℕ) (d n : ℕ) : List ℕ := (List.range n).map fun q => ws (2 * q + d)

def layer (ws : ℕ → ℕ) (n : ℕ) : List Gate :=
  (List.range n).map fun q => ⟨GateOp.or, [ws (2 * q), ws (2 * q + 1)]⟩

def buildG : ℕ → (ℕ → ℕ) → ℕ → List Gate
  | 0, _, _ => []
  | m + 1, ws, next =>
    layer ws (2 ^ m) ++ (chainFrom (ws 1) (rest ws 3 (2 ^ m - 1)) (next + 2 ^ m) ++
      (chainFrom (ws 0) (rest ws 2 (2 ^ m - 1)) (next + 2 ^ m + (2 ^ m - 1)) ++
        buildG m (fun q => next + q) (next + 2 ^ m + (2 ^ m - 1) + (2 ^ m - 1))))

/-- The wire holding bit `j`. -/
def posW : ℕ → (ℕ → ℕ) → ℕ → ℕ → ℕ
  | 0, _, _, _ => 0
  | m + 1, ws, next, 0 => outFrom (ws 1) (rest ws 3 (2 ^ m - 1)) (next + 2 ^ m)
  | m + 1, _, next, j + 1 => posW m (fun q => next + q) (next + 2 ^ m + (2 ^ m - 1) + (2 ^ m - 1)) j

/-- The wire holding the negation of bit `j`. -/
def negW : ℕ → (ℕ → ℕ) → ℕ → ℕ → ℕ
  | 0, _, _, _ => 0
  | m + 1, ws, next, 0 => outFrom (ws 0) (rest ws 2 (2 ^ m - 1)) (next + 2 ^ m + (2 ^ m - 1))
  | m + 1, _, next, j + 1 => negW m (fun q => next + q) (next + 2 ^ m + (2 ^ m - 1) + (2 ^ m - 1)) j

theorem rest_len (ws : ℕ → ℕ) (d n : ℕ) : (rest ws d n).length = n := by simp [rest]

theorem rest_in (ws : ℕ → ℕ) (N next d : ℕ) (hd : d ≤ 3) (h : ∀ q < 2 * N, ws q < next) :
    ∀ a ∈ rest ws d (N - 1), a < next := by
  intro a ha
  simp only [rest, List.mem_map, List.mem_range] at ha
  obtain ⟨q, hq, rfl⟩ := ha
  exact h _ (by omega)

theorem layer_in (ws : ℕ → ℕ) (N next : ℕ) (h : ∀ q < 2 * N, ws q < next) :
    ∀ g ∈ layer ws N, ∀ i ∈ g.inputs, i < next := by
  intro g hg i hi
  simp only [layer, List.mem_map, List.mem_range] at hg
  obtain ⟨q, hq, rfl⟩ := hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact h _ (by omega)
  · exact h _ (by omega)

theorem layer_getD (ws : ℕ → ℕ) (n q : ℕ) (hq : q < n) (f : Gate → Bool) :
    ((layer ws n).map f).getD q false = f ⟨GateOp.or, [ws (2 * q), ws (2 * q + 1)]⟩ := by
  simp [layer, List.getD_eq_getElem?_getD, hq]

theorem any_range (n : ℕ) (f : ℕ → Bool) :
    ((List.range n).map f).any id = true ↔ ∃ q < n, f q = true := by
  simp [List.any_eq_true, List.mem_range]

theorem pos_val (N c : ℕ) (ws : ℕ → ℕ) (V : List Bool) (hN : 1 ≤ N) (hc : c < 2 * N)
    (hV : ∀ q < 2 * N, V.getD (ws q) false = decide (q = c)) :
    (V.getD (ws 1) false || ((rest ws 3 (N - 1)).map fun a => V.getD a false).any id)
      = decide (c % 2 = 1) := by
  rw [Bool.eq_iff_iff, Bool.or_eq_true, rest, List.map_map, any_range, decide_eq_true_iff]
  constructor
  · rintro (h | ⟨q, hq, h⟩)
    · rw [hV 1 (by omega)] at h; simp at h; omega
    · simp only [Function.comp_apply] at h
      rw [hV (2 * q + 3) (by omega)] at h; simp at h; omega
  · intro h
    by_cases h1 : c = 1
    · left; rw [hV 1 (by omega)]; simp [h1]
    · right
      refine ⟨(c - 3) / 2, by omega, ?_⟩
      simp only [Function.comp_apply]
      rw [hV _ (by omega)]; simp; omega

theorem neg_val (N c : ℕ) (ws : ℕ → ℕ) (V : List Bool) (hN : 1 ≤ N) (hc : c < 2 * N)
    (hV : ∀ q < 2 * N, V.getD (ws q) false = decide (q = c)) :
    (V.getD (ws 0) false || ((rest ws 2 (N - 1)).map fun a => V.getD a false).any id)
      = !decide (c % 2 = 1) := by
  have e : (!decide (c % 2 = 1)) = decide (c % 2 = 0) := by
    rcases Nat.mod_two_eq_zero_or_one c with h | h <;> simp [h]
  rw [e, Bool.eq_iff_iff, Bool.or_eq_true, rest, List.map_map, any_range, decide_eq_true_iff]
  constructor
  · rintro (h | ⟨q, hq, h⟩)
    · rw [hV 0 (by omega)] at h; simp at h; omega
    · simp only [Function.comp_apply] at h
      rw [hV (2 * q + 2) (by omega)] at h; simp at h; omega
  · intro h
    by_cases h1 : c = 0
    · left; rw [hV 0 (by omega)]; simp [h1]
    · right
      refine ⟨(c - 2) / 2, by omega, ?_⟩
      simp only [Function.comp_apply]
      rw [hV _ (by omega)]; simp; omega

theorem build_len : ∀ (m : ℕ) (ws : ℕ → ℕ) (next : ℕ),
    (buildG m ws next).length + 2 * m + 3 = 3 * 2 ^ m := by
  intro m
  induction m with
  | zero => intro ws next; simp [buildG]
  | succ m ih =>
    intro ws next
    have := ih (fun q => next + q) (next + 2 ^ m + (2 ^ m - 1) + (2 ^ m - 1))
    have hN : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    simp only [buildG, List.length_append, layer, List.length_map, List.length_range,
      chainFrom_len, rest_len, pow_succ]
    omega

theorem build_ops : ∀ (m : ℕ) (ws : ℕ → ℕ) (next : ℕ), ∀ g ∈ buildG m ws next,
    g.op = GateOp.or ∧ g.inputs.length ≤ 2 := by
  intro m
  induction m with
  | zero => intro ws next g hg; simp [buildG] at hg
  | succ m ih =>
    intro ws next g hg
    simp only [buildG, List.mem_append] at hg
    rcases hg with hg | hg | hg | hg
    · simp only [layer, List.mem_map, List.mem_range] at hg
      obtain ⟨q, _, rfl⟩ := hg
      exact ⟨rfl, by simp⟩
    · exact chainFrom_ops _ _ _ g hg
    · exact chainFrom_ops _ _ _ g hg
    · exact ih _ _ g hg

theorem build_spec : ∀ (m : ℕ) (ws : ℕ → ℕ) (next : ℕ) (W : List Bool) (c : ℕ), W.length = next →
    (∀ q < 2 ^ m, ws q < next) → c < 2 ^ m →
    (∀ q < 2 ^ m, W.getD (ws q) false = decide (q = c)) → ∀ j < m,
    posW m ws next j < next + (buildG m ws next).length ∧
    negW m ws next j < next + (buildG m ws next).length ∧
    ((buildG m ws next).foldl step W).getD (posW m ws next j) false
      = decide (c / 2 ^ j % 2 = 1) ∧
    ((buildG m ws next).foldl step W).getD (negW m ws next j) false
      = !decide (c / 2 ^ j % 2 = 1) := by
  intro m
  induction m with
  | zero => intro _ _ _ _ _ _ _ _ j hj; omega
  | succ m ih =>
    intro ws next W c hW hws hc hV j hj
    have hN : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
    rw [h2] at hws hc hV
    have hG : buildG (m + 1) ws next = layer ws (2 ^ m) ++
        (chainFrom (ws 1) (rest ws 3 (2 ^ m - 1)) (next + 2 ^ m) ++
        (chainFrom (ws 0) (rest ws 2 (2 ^ m - 1)) (next + 2 ^ m + (2 ^ m - 1)) ++
        buildG m (fun q => next + q) (next + 2 ^ m + (2 ^ m - 1) + (2 ^ m - 1)))) := rfl
    have hlen : (buildG (m + 1) ws next).length = 2 ^ m + (2 ^ m - 1) + (2 ^ m - 1) +
        (buildG m (fun q => next + q) (next + 2 ^ m + (2 ^ m - 1) + (2 ^ m - 1))).length := by
      rw [hG]
      simp only [List.length_append, layer, List.length_map, List.length_range, chainFrom_len,
        rest_len]
      omega
    -- the folding layer
    obtain ⟨W1, hW1⟩ : ∃ W1, W1 = (layer ws (2 ^ m)).foldl step W := ⟨_, rfl⟩
    have hW1e : W1 = W ++ (layer ws (2 ^ m)).map
        (fun g => g.op.eval (g.inputs.map fun i => W.getD i false)) := by
      rw [hW1]; exact foldl_par _ _ (by rw [hW]; exact layer_in ws _ next hws)
    have hW1l : W1.length = next + 2 ^ m := by
      rw [hW1e]; simp [layer, hW]
    have hV1 : ∀ q < 2 * 2 ^ m, W1.getD (ws q) false = decide (q = c) := fun q hq => by
      rw [hW1, foldl_getD_lt _ _ _ (by rw [hW]; exact hws q hq)]; exact hV q hq
    have hF1 : ∀ q < 2 ^ m, W1.getD (next + q) false = decide (q = c / 2) := by
      intro q hq
      rw [hW1e, getD_right _ _ _ (by omega), hW, Nat.add_sub_cancel_left, layer_getD ws _ q hq]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
        Bool.or_false]
      rw [hV _ (by omega), hV _ (by omega), Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_iff]
      constructor
      · intro h; omega
      · intro h; omega
    -- the chain for bit 0
    have hc1 := chainFrom_spec (rest ws 3 (2 ^ m - 1)) (ws 1) (next + 2 ^ m) W1 hW1l
      (by have := hws 1 (by omega); omega)
      (fun a ha => by have := rest_in ws (2 ^ m) next 3 (by omega) hws a ha; omega)
    rw [rest_len] at hc1
    obtain ⟨W2, hW2⟩ : ∃ W2, W2 =
        (chainFrom (ws 1) (rest ws 3 (2 ^ m - 1)) (next + 2 ^ m)).foldl step W1 := ⟨_, rfl⟩
    have hW2l : W2.length = next + 2 ^ m + (2 ^ m - 1) := by
      rw [hW2, len_foldl, hW1l, chainFrom_len, rest_len]
    have hV2 : ∀ q < 2 * 2 ^ m, W2.getD (ws q) false = decide (q = c) := fun q hq => by
      rw [hW2, foldl_getD_lt _ _ _ (by rw [hW1l]; have := hws q hq; omega)]; exact hV1 q hq
    have hF2 : ∀ q < 2 ^ m, W2.getD (next + q) false = decide (q = c / 2) := fun q hq => by
      rw [hW2, foldl_getD_lt _ _ _ (by rw [hW1l]; omega)]; exact hF1 q hq
    have hP2 : W2.getD (outFrom (ws 1) (rest ws 3 (2 ^ m - 1)) (next + 2 ^ m)) false
        = decide (c % 2 = 1) := by
      rw [hW2, hc1.2]; exact pos_val (2 ^ m) c ws W1 hN hc hV1
    -- the chain for the negation of bit 0
    have hc2 := chainFrom_spec (rest ws 2 (2 ^ m - 1)) (ws 0) (next + 2 ^ m + (2 ^ m - 1)) W2 hW2l
      (by have := hws 0 (by omega); omega)
      (fun a ha => by have := rest_in ws (2 ^ m) next 2 (by omega) hws a ha; omega)
    rw [rest_len] at hc2
    obtain ⟨W3, hW3⟩ : ∃ W3, W3 =
        (chainFrom (ws 0) (rest ws 2 (2 ^ m - 1)) (next + 2 ^ m + (2 ^ m - 1))).foldl step W2 :=
      ⟨_, rfl⟩
    have hW3l : W3.length = next + 2 ^ m + (2 ^ m - 1) + (2 ^ m - 1) := by
      rw [hW3, len_foldl, hW2l, chainFrom_len, rest_len]
    have hF3 : ∀ q < 2 ^ m, W3.getD (next + q) false = decide (q = c / 2) := fun q hq => by
      rw [hW3, foldl_getD_lt _ _ _ (by rw [hW2l]; omega)]; exact hF2 q hq
    have hP3 : W3.getD (outFrom (ws 1) (rest ws 3 (2 ^ m - 1)) (next + 2 ^ m)) false
        = decide (c % 2 = 1) := by
      rw [hW3, foldl_getD_lt _ _ _ (by rw [hW2l]; omega)]; exact hP2
    have hN3 : W3.getD (outFrom (ws 0) (rest ws 2 (2 ^ m - 1)) (next + 2 ^ m + (2 ^ m - 1))) false
        = !decide (c % 2 = 1) := by
      rw [hW3, hc2.2]; exact neg_val (2 ^ m) c ws W2 hN hc hV2
    have b1 := hc1.1
    have b2 := hc2.1
    rcases j with _ | j
    · have e1 : posW (m + 1) ws next 0 = outFrom (ws 1) (rest ws 3 (2 ^ m - 1)) (next + 2 ^ m) :=
        rfl
      have e2 : negW (m + 1) ws next 0
          = outFrom (ws 0) (rest ws 2 (2 ^ m - 1)) (next + 2 ^ m + (2 ^ m - 1)) := rfl
      rw [hlen, e1, e2, hG, List.foldl_append, List.foldl_append, List.foldl_append, ← hW1, ← hW2,
        ← hW3]
      refine ⟨by omega, by omega, ?_, ?_⟩
      · rw [foldl_getD_lt _ _ _ (by rw [hW3l]; omega), hP3]; simp
      · rw [foldl_getD_lt _ _ _ (by rw [hW3l]; omega), hN3]; simp
    · have hj' : j < m := by omega
      have e1 : posW (m + 1) ws next (j + 1)
          = posW m (fun q => next + q) (next + 2 ^ m + (2 ^ m - 1) + (2 ^ m - 1)) j := rfl
      have e2 : negW (m + 1) ws next (j + 1)
          = negW m (fun q => next + q) (next + 2 ^ m + (2 ^ m - 1) + (2 ^ m - 1)) j := rfl
      have H := ih (fun q => next + q) (next + 2 ^ m + (2 ^ m - 1) + (2 ^ m - 1)) W3 (c / 2) hW3l
        (fun q hq => by show next + q < _; omega) (by omega) hF3 j hj'
      rw [hlen, e1, e2, hG, List.foldl_append, List.foldl_append, List.foldl_append, ← hW1, ← hW2,
        ← hW3]
      have hdiv : c / 2 / 2 ^ j = c / 2 ^ (j + 1) := by
        rw [Nat.div_div_eq_div_mul, ← pow_succ']
      rw [hdiv] at H
      exact ⟨by omega, by omega, H.2.2.1, H.2.2.2⟩

/-! ## Binary digits and the inputs `oneEach` -/

theorem tableIndex_bits : ∀ (n a : ℕ), a < 2 ^ n →
    PEqualNP.MetaComplexity.tableIndex (fun i : Fin n => decide (a / 2 ^ (i : ℕ) % 2 = 1)) = a := by
  intro n
  induction n with
  | zero => intro a ha; simp at ha; simp [PEqualNP.MetaComplexity.tableIndex]; omega
  | succ n ih =>
    intro a ha
    have h2 : a / 2 < 2 ^ n := by rw [pow_succ] at ha; omega
    have hih := ih (a / 2) h2
    unfold PEqualNP.MetaComplexity.tableIndex at hih ⊢
    rw [Fin.sum_univ_succ]
    have key : ∀ i : Fin n,
        (if decide (a / 2 ^ ((i.succ : Fin (n + 1)) : ℕ) % 2 = 1) = true
          then 2 ^ ((i.succ : Fin (n + 1)) : ℕ) else 0)
        = 2 * (if decide (a / 2 / 2 ^ (i : ℕ) % 2 = 1) = true then 2 ^ (i : ℕ) else 0) := by
      intro i
      rw [Fin.val_succ, Nat.div_div_eq_div_mul, ← pow_succ']
      split_ifs <;> simp [pow_succ']
    rw [Finset.sum_congr rfl (fun i _ => key i), ← Finset.mul_sum, hih]
    simp only [Fin.val_zero, pow_zero, Nat.div_one]
    split_ifs with h <;> simp at h <;> omega

theorem oneEach_left {n m : ℕ} (u : Fin n) (v : Fin m) (q : ℕ) (hq : q < n) :
    (PEqualNP.Represents.oneEach u v).getD q false = decide (q = u.val) := by
  unfold PEqualNP.Represents.oneEach
  rw [getD_left _ _ _ (by simp [hq])]
  simp [List.getD_eq_getElem?_getD, hq, Fin.ext_iff]

theorem oneEach_right {n m : ℕ} (u : Fin n) (v : Fin m) (q : ℕ) (hq : q < m) :
    (PEqualNP.Represents.oneEach u v).getD (n + q) false = decide (q = v.val) := by
  unfold PEqualNP.Represents.oneEach
  rw [getD_right _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, hq, Fin.ext_iff]

end PEqualNP.Outside.L_meta_9019

open PEqualNP.Outside.L_meta_9019 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_9019 : ∀ (k l s : ℕ) (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool), PEqualNP.Represents.HasLitSize (k + l) (PEqualNP.Represents.adjFun A) s → PEqualNP.Represents.RepSizeAtMost A (s + 3 * 2 ^ k + 3 * 2 ^ l) := by
  intro k l s A ⟨C, hCm, hCs, hC⟩
  obtain ⟨G1, hG1⟩ : ∃ G1, G1 = buildG k (fun q => q) (2 ^ k + 2 ^ l) := ⟨_, rfl⟩
  obtain ⟨G2, hG2⟩ : ∃ G2, G2 = buildG l (fun q => 2 ^ k + q) (2 ^ k + 2 ^ l + G1.length) :=
    ⟨_, rfl⟩
  obtain ⟨wire, hwire⟩ : ∃ wire : ℕ → ℕ, wire = fun i =>
      if i < k then posW k (fun q => q) (2 ^ k + 2 ^ l) i
      else if i < k + l then posW l (fun q => 2 ^ k + q) (2 ^ k + 2 ^ l + G1.length) (i - k)
      else if i < k + l + k then negW k (fun q => q) (2 ^ k + 2 ^ l) (i - (k + l))
      else negW l (fun q => 2 ^ k + q) (2 ^ k + 2 ^ l + G1.length) (i - (k + l) - k) := ⟨_, rfl⟩
  have hP : PEqualNP.MetaComplexity.Monotone2 (⟨G1 ++ G2, 0⟩ : Circuit) := by
    intro g hg
    have hg' : g ∈ G1 ++ G2 := hg
    have : g.op = GateOp.or ∧ g.inputs.length ≤ 2 := by
      rw [List.mem_append] at hg'
      rcases hg' with hg' | hg'
      · rw [hG1] at hg'; exact build_ops _ _ _ g hg'
      · rw [hG2] at hg'; exact build_ops _ _ _ g hg'
    exact ⟨by rw [this.1]; simp, this.2⟩
  obtain ⟨C', hm', hs', he'⟩ := compose (2 ^ k + 2 ^ l) ((k + l) + (k + l))
    {x | x.length = 2 ^ k + 2 ^ l} (G1 ++ G2) (fun j => wire j)
    (fun j x => ((⟨G1 ++ G2, 0⟩ : Circuit).wires x).getD (wire j) false) C
    (fun x hx => hx) hP hCm (fun x _ j => rfl)
  refine ⟨C', hm', ?_, ?_⟩
  · have h1 := build_len k (fun q => q) (2 ^ k + 2 ^ l)
    have h2 := build_len l (fun q => 2 ^ k + q) (2 ^ k + 2 ^ l + G1.length)
    rw [← hG1] at h1
    rw [← hG2] at h2
    have : C.size ≤ s := hCs
    simp only [List.length_append] at hs'
    omega
  · intro u v
    have hx : (PEqualNP.Represents.oneEach u v).length = 2 ^ k + 2 ^ l := by
      simp [PEqualNP.Represents.oneEach]
    have hX1 : ∀ q < 2 ^ k, (PEqualNP.Represents.oneEach u v).getD ((fun q => q) q) false
        = decide (q = u.val) := fun q hq => oneEach_left u v q hq
    have hX2 : ∀ q < 2 ^ l, (PEqualNP.Represents.oneEach u v).getD (2 ^ k + q) false
        = decide (q = v.val) := fun q hq => oneEach_right u v q hq
    rw [he' _ hx]
    generalize PEqualNP.Represents.oneEach u v = X at hx hX1 hX2 ⊢
    have hS1 := build_spec k (fun q => q) (2 ^ k + 2 ^ l) X u.val hx
      (fun q hq => Nat.lt_of_lt_of_le hq (Nat.le_add_right _ _)) u.isLt hX1
    rw [← hG1] at hS1
    obtain ⟨Y, hY⟩ : ∃ Y, Y = G1.foldl step X := ⟨_, rfl⟩
    rw [← hY] at hS1
    have hYl : Y.length = 2 ^ k + 2 ^ l + G1.length := by rw [hY, len_foldl, hx]
    have hY2 : ∀ q < 2 ^ l, Y.getD ((fun q => 2 ^ k + q) q) false = decide (q = v.val) := by
      intro q hq
      show Y.getD (2 ^ k + q) false = _
      rw [hY, foldl_getD_lt _ _ _ (by rw [hx]; omega)]
      exact hX2 q hq
    have hS2 := build_spec l (fun q => 2 ^ k + q) _ Y v.val hYl
      (fun q hq => by show 2 ^ k + q < _; omega) v.isLt hY2
    rw [← hG2] at hS2
    have hW : ∀ j, ((⟨G1 ++ G2, 0⟩ : Circuit).wires X).getD j false
        = (G2.foldl step Y).getD j false := by
      intro j
      show ((G1 ++ G2).foldl step X).getD j false = _
      rw [List.foldl_append, ← hY]
    let xb : Fin (k + l) → Bool := fun i => if (i : ℕ) < k then decide (u.val / 2 ^ (i : ℕ) % 2 = 1)
      else decide (v.val / 2 ^ ((i : ℕ) - k) % 2 = 1)
    have hleft : ∀ i : Fin (k + l), (G2.foldl step Y).getD (wire i) false = xb i := by
      intro i
      by_cases hi : (i : ℕ) < k
      · have H := hS1 i hi
        rw [hwire]
        simp only [xb, if_pos hi]
        rw [foldl_getD_lt _ _ _ (by rw [hYl]; omega)]
        exact H.2.2.1
      · have hi2 : (i : ℕ) - k < l := by omega
        have H := hS2 _ hi2
        rw [hwire]
        simp only [xb, if_neg hi, if_pos i.isLt]
        exact H.2.2.1
    have hright : ∀ i : Fin (k + l), (G2.foldl step Y).getD (wire (k + l + i)) false = !xb i := by
      intro i
      by_cases hi : (i : ℕ) < k
      · have H := hS1 i hi
        rw [hwire]
        simp only [xb, if_pos hi]
        rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
          show k + l + (i : ℕ) - (k + l) = i by omega,
          foldl_getD_lt _ _ _ (by rw [hYl]; omega)]
        exact H.2.2.2
      · have hi2 : (i : ℕ) - k < l := by omega
        have H := hS2 _ hi2
        rw [hwire]
        simp only [xb, if_neg hi]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
          show k + l + (i : ℕ) - (k + l) - k = i - k by omega]
        exact H.2.2.2
    have hlist : (List.ofFn fun j : Fin ((k + l) + (k + l)) =>
        ((⟨G1 ++ G2, 0⟩ : Circuit).wires X).getD (wire j) false)
        = List.ofFn xb ++ List.ofFn fun i => !xb i := by
      rw [List.ofFn_add]
      congr 1
      · congr 1
        funext i
        rw [hW]
        exact hleft i
      · congr 1
        funext i
        rw [hW]
        exact hright i
    show C.eval (List.ofFn fun j : Fin ((k + l) + (k + l)) =>
        ((⟨G1 ++ G2, 0⟩ : Circuit).wires X).getD (wire j) false) = A u v
    rw [hlist, hC xb]
    unfold PEqualNP.Represents.adjFun
    have e1 : (fun i : Fin k => xb (Fin.castAdd l i))
        = fun i : Fin k => decide (u.val / 2 ^ (i : ℕ) % 2 = 1) := by
      funext i
      have : ((Fin.castAdd l i : Fin (k + l)) : ℕ) = i := rfl
      simp only [xb, this, if_pos i.isLt]
    have e2 : (fun j : Fin l => xb (Fin.natAdd k j))
        = fun j : Fin l => decide (v.val / 2 ^ (j : ℕ) % 2 = 1) := by
      funext j
      have : ((Fin.natAdd k j : Fin (k + l)) : ℕ) = k + j := rfl
      simp only [xb, this, if_neg (show ¬ (k + (j : ℕ) < k) by omega), Nat.add_sub_cancel_left]
    rw [e1, e2, tableIndex_bits k u.val u.isLt, tableIndex_bits l v.val v.isLt]
    congr 1
    · exact Fin.ext (by simp [Nat.mod_eq_of_lt u.isLt])
    · exact Fin.ext (by simp [Nat.mod_eq_of_lt v.isLt])
