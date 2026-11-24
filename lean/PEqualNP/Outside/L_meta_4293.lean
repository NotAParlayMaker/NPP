import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4293

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.MetaComplexity.NestedCover

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def mapE (n m p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

theorem len_fold (gs : List Gate) : ∀ a, (gs.foldl stepW a).length = a.length + gs.length := by
  induction gs with
  | nil => intro a; simp
  | cons g gs ih => intro a; simp [ih, stepW]; omega

theorem getD_snoc (l : List Bool) (x : Bool) (i : ℕ) :
    (l ++ [x]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then x else false := by
  split_ifs with h1 h2
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ h1,
      List.getElem_append_left h1]
  · subst h2
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem prefix_fold (gs : List Gate) :
    ∀ a i, i < a.length → (gs.foldl stepW a).getD i false = a.getD i false := by
  induction gs with
  | nil => intro a i _; rfl
  | cons g gs ih =>
    intro a i hi
    rw [List.foldl_cons, ih _ i (by simp [stepW]; omega)]
    simp only [stepW]
    rw [getD_snoc, if_pos hi]

theorem rho_prop (n m p k i : ℕ) (hp : p < n + m) (hk : n + m < k) :
    (eraseRedirect n m p i < k - 1 ↔ i < k) ∧ (eraseRedirect n m p i = k - 1 ↔ i = k) := by
  unfold eraseRedirect
  split_ifs <;> constructor <;> constructor <;> intro h <;> omega

theorem run (n m p : ℕ) (hp : p < n + m) (gs : List Gate) :
    ∀ a b : List Bool, n + m < a.length → b.length + 1 = a.length →
      (∀ i, b.getD (eraseRedirect n m p i) false = a.getD i false) →
      ∀ i, ((gs.map (mapE n m p)).foldl stepW b).getD (eraseRedirect n m p i) false
        = (gs.foldl stepW a).getD i false := by
  induction gs with
  | nil => intro a b _ _ h i; exact h i
  | cons g gs ih =>
    intro a b ha hlen h
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    have hval : (mapE n m p g).op.eval ((mapE n m p g).inputs.map fun i => b.getD i false)
        = g.op.eval (g.inputs.map fun i => a.getD i false) := by
      simp only [mapE, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact h j
    apply ih
    · simp [stepW]; omega
    · simp [stepW]; omega
    · intro i
      simp only [stepW]
      rw [getD_snoc, getD_snoc, hval]
      obtain ⟨hA, hB⟩ := rho_prop n m p a.length i hp ha
      have hbl : b.length = a.length - 1 := by omega
      rw [hbl]
      by_cases h1 : i < a.length
      · rw [if_pos (hA.2 h1), if_pos h1]
        exact h i
      · rw [if_neg (fun h' => h1 (hA.1 h')), if_neg h1]
        by_cases h2 : i = a.length
        · rw [if_pos (hB.2 h2), if_pos h2]
        · rw [if_neg (fun h' => h2 (hB.1 h')), if_neg h2]

end PEqualNP.Outside.L_meta_4293

theorem PEqualNP.Outside.L_meta_4293 : ∀ (x1 : ℕ) (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → x2.output < x1 + x2.gates.length → PEqualNP.CircuitMoves.Lift x1 x2 x3 → PEqualNP.TopForm.IsAO2 x1 x3 ∧ x3.output < x1 + x3.gates.length ∧ x3.size = x2.size ∧ PEqualNP.MetaComplexity.circuitFun x1 x3 = PEqualNP.MetaComplexity.circuitFun x1 x2 := by
  open PEqualNP.Outside.L_meta_4293 PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves
    PEqualNP.MetaComplexity.NestedCover in
  intro n C C' hAO hout hL
  obtain ⟨hAnd, hRB, hTwo⟩ := hAO
  obtain ⟨m, hm, p, hp, h, hh, hnh, hgate, hbelow, rfl⟩ := hL
  have hE : eraseGate n C m p = ⟨C.gates.take m ++ (C.gates.drop (m + 1)).map (mapE n m p),
      eraseRedirect n m p C.output⟩ := by
    unfold eraseGate
    rw [if_pos hm]
    rfl
  have hRB' : ∀ j (hj : j < C.gates.length), ∀ i ∈ C.gates[j].inputs, i < n + j := by
    intro j hj i hi
    apply hRB j hj
    simp only [gateAt]
    rw [List.getD_eq_getElem _ _ hj]
    exact hi
  have hgm : C.gates[m] = ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m] = ⟨GateOp.or, [h, p]⟩ := by
    rw [List.getElem?_eq_getElem hm] at hgate
    simpa using hgate
  have hdec : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
    rw [← List.drop_eq_getElem_cons hm, List.take_append_drop]
  have hlt : m < C.gates.length := hm
  unfold liftAt
  rw [hE]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton, List.mem_map] at hg
    rcases hg with (hg | ⟨g0, hg0, rfl⟩) | rfl
    · exact hAnd g (List.mem_of_mem_take hg)
    · exact hAnd g0 (List.mem_of_mem_drop hg0)
    · exact Or.inr rfl
  · intro j hj i hi
    simp only [gateAt] at hi
    rw [List.getD_eq_getElem _ _ hj] at hi
    simp only [List.length_append, List.length_take, List.length_map, List.length_drop,
      List.length_singleton] at hj
    rw [List.getElem_append] at hi
    split_ifs at hi with h1
    · rw [List.getElem_append] at hi
      split_ifs at hi with h2
      · rw [List.getElem_take] at hi
        simp only [List.length_take] at h2
        exact hRB' j (by omega) i hi
      · simp only [List.getElem_map, List.getElem_drop, mapE, List.length_take] at hi h1 h2
        rw [List.mem_map] at hi
        obtain ⟨i0, hi0, rfl⟩ := hi
        have := hRB' _ _ i0 hi0
        unfold eraseRedirect
        split_ifs <;> omega
    · simp only [List.length_append, List.length_take, List.length_map, List.length_drop] at h1
      simp at hi
      rcases hi with rfl | rfl
      · unfold eraseRedirect
        split_ifs <;> omega
      · omega
  · intro g hg
    simp only [List.mem_append, List.mem_singleton, List.mem_map] at hg
    rcases hg with (hg | ⟨g0, hg0, rfl⟩) | rfl
    · exact hTwo g (List.mem_of_mem_take hg)
    · simpa [mapE] using hTwo g0 (List.mem_of_mem_drop hg0)
    · rfl
  · simp
  · simp [Circuit.size]
    omega
  · funext x
    have hb := hbelow x
    simp only [PEqualNP.MetaComplexity.circuitFun, Circuit.eval, wires_eq] at hb ⊢
    rw [hdec] at hb
    conv_rhs => rw [hdec]
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at hb ⊢
    have hv : stepW ((C.gates.take m).foldl stepW (List.ofFn x)) C.gates[m] =
        (C.gates.take m).foldl stepW (List.ofFn x) ++
          [((C.gates.take m).foldl stepW (List.ofFn x)).getD p false ||
            ((C.gates.take m).foldl stepW (List.ofFn x)).getD h false] := by
      rcases hgm with hg | hg <;> rw [hg] <;> simp [stepW, GateOp.eval, Bool.or_comm]
    rw [hv] at hb ⊢
    generalize hA : (C.gates.take m).foldl stepW (List.ofFn x) = A at hb ⊢
    have hAl : A.length = n + m := by
      rw [← hA, len_fold]
      simp
      omega
    have hWE : (((C.gates.drop (m + 1)).map (mapE n m p)).foldl stepW A).getD h false =
        A.getD h false := prefix_fold _ _ _ (by omega)
    have hWC : ((C.gates.drop (m + 1)).foldl stepW (A ++ [A.getD p false || A.getD h false])).getD
        h false = A.getD h false := by
      rw [prefix_fold _ _ _ (by simp; omega), getD_snoc, if_pos (by omega)]
    have hlenE : (((C.gates.drop (m + 1)).map (mapE n m p)).foldl stepW A).length =
        n + (C.gates.take m ++ (C.gates.drop (m + 1)).map (mapE n m p)).length := by
      rw [len_fold, hAl]
      simp
      omega
    simp only [stepW]
    rw [getD_snoc, if_neg (by omega), if_pos hlenE.symm]
    simp only [List.map_cons, List.map_nil]
    rw [hWE]
    cases hhv : A.getD h false
    · have hrun := run n m p hp (C.gates.drop (m + 1)) (A ++ [A.getD p false || false]) A
        (by simp; omega) (by simp)
        (by
          intro i
          rw [getD_snoc]
          unfold eraseRedirect
          split_ifs <;> first
            | omega
            | (rw [List.getD_eq_default _ _ (by omega)])
            | (simp; done))
        C.output
      rw [hrun]
      simp [GateOp.eval]
    · rw [hhv] at hWC hb
      rw [hb hWC]
      simp [GateOp.eval]
