import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9308
open PEqualNP.CircuitLowerBounds



def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem len : ∀ (gs : List Gate) (w : List Bool), (gs.foldl stp w).length = w.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih => intro w; rw [List.foldl_cons, ih]; simp [stp]; omega

theorem pre : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl stp w).getD i false = w.getD i false := by
  intro gs
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih _ i (by simp [stp]; omega)]
    unfold stp
    exact List.getD_append _ _ _ _ hi

theorem ev_or (p q : Bool) : GateOp.or.eval [p, q] = (p || q) := by cases p <;> cases q <;> rfl
theorem ev_and (p q : Bool) : GateOp.and.eval [p, q] = (p && q) := by cases p <;> cases q <;> rfl

theorem ext2 (gs : List Gate) (o : ℕ) (x : List Bool) (a b : ℕ) (ha : a < x.length) (hb : b < x.length) :
    Circuit.eval ⟨gs ++ [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [o, x.length + gs.length]⟩], x.length + gs.length + 1⟩ x
      = (Circuit.eval ⟨gs, o⟩ x || (x.getD a false && x.getD b false)) := by
  have hl := len gs x
  have pa := pre gs x a ha
  have pb := pre gs x b hb
  show ((gs ++ [(⟨GateOp.and, [a, b]⟩ : Gate), ⟨GateOp.or, [o, x.length + gs.length]⟩]).foldl stp x).getD
      (x.length + gs.length + 1) false = ((gs.foldl stp x).getD o false || (x.getD a false && x.getD b false))
  rw [List.foldl_append, ← pa, ← pb, ← hl]
  generalize gs.foldl stp x = W
  have e1 : ∀ (L : List Bool) (v : Bool), (L ++ [v]).getD L.length false = v := by intro L v; simp
  have e2 : ∀ (L : List Bool) (v : Bool) (i : ℕ), i < L.length → (L ++ [v]).getD i false = L.getD i false :=
    fun L v i h => List.getD_append _ _ _ _ h
  have e3 : ∀ (L : List Bool) (i : ℕ), L.length ≤ i → L.getD i false = false :=
    fun L i h => List.getD_eq_default _ _ h
  have hs1 : ∀ v : Bool, (W ++ [v]).length = W.length + 1 := by intro v; simp
  simp only [List.foldl_cons, List.foldl_nil, stp, List.map_cons, List.map_nil]
  rw [← hs1, e1, ev_or, ev_and, e1]
  rcases Nat.lt_trichotomy o W.length with h | h | h
  · rw [e2 _ _ _ h]
  · rw [h, e1, e3 W W.length (le_refl _)]
    cases (W.getD a false && W.getD b false) <;> rfl
  · rw [e3 _ o (by rw [hs1]; omega), e3 W o (by omega)]

theorem main (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) :
    ∀ l : List (Fin n × Fin n), ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      D.size = C.size + 2 * l.length ∧ ∀ (x6 x7 : Fin n → Bool),
        D.eval (List.ofFn x6 ++ List.ofFn x7) =
          (C.eval (List.ofFn x6 ++ List.ofFn x7) || l.any fun p => x6 p.1 && x7 p.2) := by
  intro l
  induction l with
  | nil => exact ⟨C, hC, by simp, by simp⟩
  | cons p l ih =>
    obtain ⟨D, hD, hs, he⟩ := ih
    refine ⟨⟨D.gates ++ [⟨GateOp.and, [p.1.val, n + p.2.val]⟩, ⟨GateOp.or, [D.output, (n + n) + D.gates.length]⟩],
      (n + n) + D.gates.length + 1⟩, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.1 hg with h | h
      · exact hD g h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl <;> simp
    · simp only [Circuit.size, List.length_append, List.length_cons, List.length_nil] at hs ⊢
      omega
    · intro x6 x7
      have hlen : (List.ofFn x6 ++ List.ofFn x7).length = n + n := by simp
      have key := ext2 D.gates D.output (List.ofFn x6 ++ List.ofFn x7) p.1.val (n + p.2.val)
        (by rw [hlen]; omega) (by rw [hlen]; omega)
      rw [hlen] at key
      have hD' : Circuit.eval ⟨D.gates, D.output⟩ = D.eval := rfl
      have g1 : (List.ofFn x6 ++ List.ofFn x7).getD p.1.val false = x6 p.1 := by
        rw [List.getD_append _ _ _ _ (by simp)]; simp
      have g2 : (List.ofFn x6 ++ List.ofFn x7).getD (n + p.2.val) false = x7 p.2 := by
        rw [List.getD_append_right _ _ _ _ (by simp)]; simp
      rw [key, hD', he, g1, g2, List.any_cons]
      cases C.eval (List.ofFn x6 ++ List.ofFn x7) <;> cases (x6 p.1 && x7 p.2) <;> simp

end PEqualNP.Outside.L_meta_9308

open PEqualNP.Outside.L_meta_9308 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_9308 : ∀ (x1 : ℕ) (x2 : List (Fin x1 × Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size = x3.size + (2 : ℕ) * x2.length ∧ ∀ (x6 x7 : Fin x1 → Bool), x5.eval (List.ofFn x6 ++ List.ofFn x7) = (x3.eval (List.ofFn x6 ++ List.ofFn x7) || x2.any fun (x8 : Fin x1 × Fin x1) => x6 x8.1 && x7 x8.2) := by
  intro x1 x2 x3 h3
  exact main x1 x3 h3 x2
