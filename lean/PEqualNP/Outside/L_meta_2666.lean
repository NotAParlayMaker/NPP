import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2666_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def gs (n : ℕ) : List (Fin n × Fin n) → List Gate
  | [] => [⟨GateOp.or, []⟩]
  | p :: L => gs n L ++ [⟨GateOp.and, [p.1.val, p.2.val]⟩,
      ⟨GateOp.or, [n + 2 * L.length, n + 2 * L.length + 1]⟩]

lemma gs_len (n : ℕ) (L : List (Fin n × Fin n)) : (gs n L).length = 2 * L.length + 1 := by
  induction L with
  | nil => simp [gs]
  | cons p L ih => simp [gs, ih]; ring

lemma fold_pre (l : List Gate) (w : List Bool) :
    ∃ t, l.foldl stepW w = w ++ t ∧ t.length = l.length := by
  induction l generalizing w with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g l ih =>
    obtain ⟨t, ht, hl⟩ := ih (stepW w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]
    simp [stepW]

lemma stepW_last (w : List Bool) (g : Gate) :
    (stepW w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [stepW]

lemma stepW_last' (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length + 1 - 1) :
    (stepW w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; simp [stepW]

lemma stepW_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (stepW w g).getD i false = w.getD i false := by
  simp [stepW, List.getD, List.getElem?_append_left hi]

lemma key (n : ℕ) (x : Fin n → Bool) (L : List (Fin n × Fin n)) :
    ((gs n L).foldl stepW (List.ofFn x)).getD (n + 2 * L.length) false =
      decide (∃ p ∈ L, x p.1 = true ∧ x p.2 = true) := by
  induction L with
  | nil => simp [gs, stepW, GateOp.eval]
  | cons p L ih =>
    obtain ⟨t, ht, hl⟩ := fold_pre (gs n L) (List.ofFn x)
    rw [gs_len] at hl
    have hx : ∀ i : Fin n, ((gs n L).foldl stepW (List.ofFn x)).getD i.val false = x i := by
      intro i
      rw [ht, List.getD_append _ _ _ _ (by simp)]
      simp
    have hlen : ((gs n L).foldl stepW (List.ofFn x)).length = n + 2 * L.length + 1 := by
      rw [ht]; simp [hl]; omega
    set w := (gs n L).foldl stepW (List.ofFn x) with hw
    have e : (gs n (p :: L)).foldl stepW (List.ofFn x) = stepW (stepW w ⟨GateOp.and, [p.1.val, p.2.val]⟩)
        ⟨GateOp.or, [n + 2 * L.length, n + 2 * L.length + 1]⟩ := by
      simp [gs, List.foldl_append, w]
    rw [e]
    have hi : n + 2 * (p :: L).length = (stepW w ⟨GateOp.and, [p.1.val, p.2.val]⟩).length := by
      simp [stepW, hlen]; ring
    rw [hi, stepW_last]
    simp only [List.map_cons, List.map_nil, GateOp.eval]
    rw [stepW_lt _ _ _ (by rw [hlen]; omega), stepW_last' _ _ _ hlen.symm, ih]
    simp only [List.map_cons, List.map_nil, GateOp.eval, hx]
    simp
    rw [Bool.or_comm]

lemma gs_mono (n : ℕ) (L : List (Fin n × Fin n)) : Monotone2 ⟨gs n L, n + 2 * L.length⟩ := by
  intro g hg
  induction L with
  | nil =>
    have hg' : g = ⟨GateOp.or, []⟩ := by simpa [gs] using hg
    subst hg'; simp
  | cons p L ih =>
    simp only [gs, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact ih hg
    · simp
    · simp

lemma exists_mono (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ C : Circuit, Monotone2 C ∧ circuitFun n C = NestedCover.graphFun G ∅ := by
  classical
  let L := (Finset.univ.filter (fun p : Fin n × Fin n => G.Adj p.1 p.2)).toList
  refine ⟨⟨gs n L, n + 2 * L.length⟩, ?_, ?_⟩
  · exact gs_mono n L
  · funext x
    have h := key n x L
    show ((gs n L).foldl stepW (List.ofFn x)).getD _ false = _
    rw [h]
    simp [NestedCover.graphFun, L]

end PEqualNP.Outside.L_meta_2666_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_2666 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x4 ∧ PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ := by
  intro n G _
  classical
  have hex : ∃ k, ∃ C : Circuit, Monotone2 C ∧ circuitFun n C = NestedCover.graphFun G ∅ ∧ C.size = k := by
    obtain ⟨C, h1, h2⟩ := PEqualNP.Outside.L_meta_2666_aux.exists_mono n G
    exact ⟨_, C, h1, h2, rfl⟩
  obtain ⟨C, h1, h2, h3⟩ := Nat.find_spec hex
  refine ⟨C, ⟨h1, fun D hD hf => ?_⟩, h2⟩
  rw [h3]
  exact Nat.find_min' hex ⟨D, hD, hf.trans h2, rfl⟩
