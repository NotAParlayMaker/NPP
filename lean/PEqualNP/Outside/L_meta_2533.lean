import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2533_aux

open PEqualNP.CircuitLowerBounds

def stepW (acc : List Bool) (g : Gate) : List Bool :=
  acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]

def reGate (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma fold_len (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma gO (l : List Bool) (j : ℕ) (h : l.length ≤ j) : l.getD j false = false :=
  List.getD_eq_default _ _ h

lemma gA (l : List Bool) (v : Bool) (j : ℕ) :
    (l ++ [v]).getD j false = if j < l.length then l.getD j false else if j = l.length then v else false := by
  rcases Nat.lt_trichotomy j l.length with h | h | h
  · rw [if_pos h]; exact List.getD_append _ _ _ _ h
  · subst h; simp
  · rw [if_neg (show ¬ j < l.length by omega), if_neg (show ¬ j = l.length by omega), gO]
    simp; omega

lemma fold_sim (ρ : ℕ → ℕ) (gs : List Gate) : ∀ (W W' : List Bool),
    (∀ i, W'.getD (ρ i) false = W.getD i false) →
    (∀ k < gs.length, ∀ i, (i = W.length + k ↔ ρ i = W'.length + k) ∧
      (W.length + k < i → W'.length + k < ρ i)) →
    ∀ i, ((gs.map (reGate ρ)).foldl stepW W').getD (ρ i) false = (gs.foldl stepW W).getD i false := by
  induction gs with
  | nil => intro W W' h _ i; simpa using h i
  | cons g gs ih =>
    intro W W' hinv hc
    have hv : g.op.eval ((g.inputs.map ρ).map fun i => W'.getD i false)
        = g.op.eval (g.inputs.map fun i => W.getD i false) := by
      rw [List.map_map]; congr 1; exact List.map_congr_left (fun i _ => hinv i)
    have h0 := hc 0 (by simp)
    simp only [Nat.add_zero] at h0
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · intro i
      show (W' ++ [g.op.eval ((g.inputs.map ρ).map fun i => W'.getD i false)]).getD (ρ i) false
        = (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]).getD i false
      rw [hv, gA, gA]
      obtain ⟨h1, h2⟩ := h0 i
      rcases Nat.lt_trichotomy i W.length with hi | hi | hi
      · have hr : ρ i ≠ W'.length := fun e => by have := h1.2 e; omega
        rw [if_pos hi]
        by_cases hr2 : ρ i < W'.length
        · rw [if_pos hr2]; exact hinv i
        · rw [if_neg hr2, if_neg hr, ← hinv i, gO _ _ (by omega)]
      · have hr : ρ i = W'.length := h1.1 hi
        rw [if_neg (show ¬ ρ i < W'.length by omega), if_pos hi, if_neg (show ¬ i < W.length by omega), if_pos hr]
      · have hr := h2 hi
        rw [if_neg (show ¬ ρ i < W'.length by omega), if_neg (show ¬ ρ i = W'.length by omega), if_neg (show ¬ i < W.length by omega), if_neg (show ¬ i = W.length by omega)]
    · intro k hk i
      have := hc (k + 1) (by simp; omega) i
      simp only [stepW, List.length_append, List.length_singleton]
      rw [show W.length + 1 + k = W.length + (k + 1) by omega,
        show W'.length + 1 + k = W'.length + (k + 1) by omega]
      exact this

def rA (n a K i : ℕ) : ℕ :=
  if i < n then i else if i = n then K else if i < n + 1 + a then i - 1
  else if i = n + 1 + a then K else i - 2

def rB (n a K t i : ℕ) : ℕ := if i = n + 1 + a then t else rA n a K i

def tB (n a K b : ℕ) : ℕ := if b < n + 1 + a then rA n a K b else K

lemma tB_range (n a c b : ℕ) : tB n a (n + a + c) b < n + a ∨ tB n a (n + a + c) b = n + a + c := by
  unfold tB rA; split_ifs <;> omega

lemma tB_val (n a c b : ℕ) (W1 W1' : List Bool) (h1 : W1.length = n + 1 + a) (h1' : W1'.length = n + a)
    (inv : ∀ i, W1'.getD (rA n a (n + a + c) i) false = W1.getD i false) :
    W1'.getD (tB n a (n + a + c) b) false = W1.getD b false := by
  unfold tB
  split_ifs with h
  · exact inv b
  · rw [gO _ _ (by omega), gO _ _ (by omega)]

lemma core (n : ℕ) (A B : List Gate) (ins : List ℕ) (out t : ℕ)
    (hF : PEqualNP.MetaComplexity.FanInTwo ⟨A ++ ⟨GateOp.or, ins⟩ :: B, out⟩)
    (ht : t < n + A.length ∨ t = n + A.length + B.length)
    (hv : ∀ W1 W1' : List Bool, W1.length = n + 1 + A.length → W1'.length = n + A.length →
      (∀ i, W1'.getD (rA n A.length (n + A.length + B.length) i) false = W1.getD i false) →
      W1'.getD t false = GateOp.or.eval (ins.map fun i => W1.getD i false)) :
    PEqualNP.MetaComplexity.HasCircuitSize n
      (fun x => Circuit.eval ⟨A ++ ⟨GateOp.or, ins⟩ :: B, out⟩ (List.ofFn x ++ [false]))
      (A.length + B.length) := by
  refine ⟨⟨A.map (reGate (rA n A.length (n + A.length + B.length))) ++
    B.map (reGate (rB n A.length (n + A.length + B.length) t)),
    rB n A.length (n + A.length + B.length) t out⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_map] at hg
    rcases hg with ⟨g', hg', rfl⟩ | ⟨g', hg', rfl⟩
    · have := hF g' (by simp [hg'])
      simpa [reGate] using this
    · have := hF g' (by simp [hg'])
      simpa [reGate] using this
  · simp [Circuit.size]
  · intro x
    show List.getD (List.foldl stepW (List.ofFn x)
      (A.map (reGate (rA n A.length (n + A.length + B.length))) ++
        B.map (reGate (rB n A.length (n + A.length + B.length) t))))
      (rB n A.length (n + A.length + B.length) t out) false
      = List.getD (List.foldl stepW (List.ofFn x ++ [false]) (A ++ ⟨GateOp.or, ins⟩ :: B)) out false
    simp only [List.foldl_append, List.foldl_cons]
    have inv0 : ∀ i, (List.ofFn x).getD (rA n A.length (n + A.length + B.length) i) false
        = (List.ofFn x ++ [false]).getD i false := by
      intro i
      rw [gA]
      simp only [List.length_ofFn]
      unfold rA
      split_ifs <;> first | rfl | omega | (rw [gO]; simp only [List.length_ofFn]; omega)
    have cond0 : ∀ k < A.length, ∀ i, (i = (List.ofFn x ++ [false]).length + k ↔
        rA n A.length (n + A.length + B.length) i = (List.ofFn x).length + k) ∧
        ((List.ofFn x ++ [false]).length + k < i →
          (List.ofFn x).length + k < rA n A.length (n + A.length + B.length) i) := by
      simp only [List.length_append, List.length_ofFn, List.length_singleton]
      intro k hk i
      unfold rA
      split_ifs <;> exact ⟨⟨fun h => by omega, fun h => by omega⟩, fun h => by omega⟩
    have inv1 := fold_sim _ A _ _ inv0 cond0
    have hl1 : (A.foldl stepW (List.ofFn x ++ [false])).length = n + 1 + A.length := by
      rw [fold_len]; simp
    have hl1' : ((A.map (reGate (rA n A.length (n + A.length + B.length)))).foldl stepW
        (List.ofFn x)).length = n + A.length := by
      rw [fold_len]; simp
    have inv2 : ∀ i, ((A.map (reGate (rA n A.length (n + A.length + B.length)))).foldl stepW
        (List.ofFn x)).getD (rB n A.length (n + A.length + B.length) t i) false
        = (stepW (A.foldl stepW (List.ofFn x ++ [false])) ⟨GateOp.or, ins⟩).getD i false := by
      intro i
      rw [stepW, gA, hl1]
      unfold rB
      by_cases hp : i = n + 1 + A.length
      · rw [if_pos hp, if_neg (show ¬ i < n + 1 + A.length by omega), if_pos hp]
        exact hv _ _ hl1 hl1' inv1
      · rw [if_neg hp, inv1, if_neg hp]
        split_ifs with h
        · rfl
        · rw [gO _ _ (by omega)]
    have cond2 : ∀ k < B.length, ∀ i,
        (i = (stepW (A.foldl stepW (List.ofFn x ++ [false])) ⟨GateOp.or, ins⟩).length + k ↔
        rB n A.length (n + A.length + B.length) t i =
          ((A.map (reGate (rA n A.length (n + A.length + B.length)))).foldl stepW
            (List.ofFn x)).length + k) ∧
        ((stepW (A.foldl stepW (List.ofFn x ++ [false])) ⟨GateOp.or, ins⟩).length + k < i →
          ((A.map (reGate (rA n A.length (n + A.length + B.length)))).foldl stepW
            (List.ofFn x)).length + k < rB n A.length (n + A.length + B.length) t i) := by
      intro k hk i
      rw [stepW]
      simp only [List.length_append, List.length_singleton, hl1, hl1']
      unfold rB rA
      rcases ht with ht | ht <;>
      split_ifs <;> exact ⟨⟨fun h => by omega, fun h => by omega⟩, fun h => by omega⟩
    exact fold_sim _ B _ _ inv2 cond2 out

end PEqualNP.Outside.L_meta_2533_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2533_aux in
theorem PEqualNP.Outside.L_meta_2533 : ∀ (x1 : ℕ) (x2 x3 : List PEqualNP.CircuitLowerBounds.Gate) (x4 : List ℕ) (x5 : ℕ),   x1 ∈ x4 →     have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x2 ++ { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := x4 : PEqualNP.CircuitLowerBounds.Gate } :: x3, output := x5 : PEqualNP.CircuitLowerBounds.Circuit };     PEqualNP.MetaComplexity.FanInTwo x7 → PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x9 : Fin x1 → Bool) => x7.eval (List.ofFn x9 ++ [Bool.false])) (x2.length + x3.length) := by
  intro n A B ins out hn
  dsimp only
  intro hF
  have hlen := (hF ⟨GateOp.or, ins⟩ (by simp)).2
  have hn0 : ∀ W1 W1' : List Bool, W1.length = n + 1 + A.length → W1'.length = n + A.length →
      (∀ i, W1'.getD (rA n A.length (n + A.length + B.length) i) false = W1.getD i false) →
      W1.getD n false = false := by
    intro W1 W1' h1 h1' inv
    rw [← inv n]
    unfold rA
    rw [if_neg (show ¬ n < n by omega), if_pos rfl, gO _ _ (by omega)]
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp at hn
  · simp at hn
    subst hn
    refine core n A B [n] out (tB n A.length (n + A.length + B.length) n) hF (tB_range _ _ _ _) ?_
    intro W1 W1' h1 h1' inv
    rw [tB_val _ _ _ _ W1 W1' h1 h1' inv]
    simp [GateOp.eval]
  · simp at hn
    rcases hn with rfl | rfl
    · refine core n A B [n, b] out (tB n A.length (n + A.length + B.length) b) hF (tB_range _ _ _ _) ?_
      intro W1 W1' h1 h1' inv
      rw [tB_val _ _ _ _ W1 W1' h1 h1' inv]
      have h0 := hn0 W1 W1' h1 h1' inv
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, h0, id, Bool.false_or, Bool.or_false]
    · refine core n A B [a, n] out (tB n A.length (n + A.length + B.length) a) hF (tB_range _ _ _ _) ?_
      intro W1 W1' h1 h1' inv
      rw [tB_val _ _ _ _ W1 W1' h1 h1' inv]
      have h0 := hn0 W1 W1' h1 h1' inv
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, h0, id, Bool.false_or, Bool.or_false]
  · simp at hlen
