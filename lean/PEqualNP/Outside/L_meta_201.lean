import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.LMeta201C

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def sep (Fu Fv : List Bool) (a b : ℕ) : Prop :=
  (Fu.getD a false = true ∧ Fv.getD a false = false ∧ Fv.getD b false = true ∧
    Fu.getD b false = false) ∨
  (Fv.getD a false = true ∧ Fu.getD a false = false ∧ Fu.getD b false = true ∧
    Fv.getD b false = false)

theorem core (au av bu bv : Bool)
    (h : ¬((au = true ∧ av = false ∧ bv = true ∧ bu = false) ∨
      (av = true ∧ au = false ∧ bu = true ∧ bv = false))) :
    ((au || av) && (bu || bv)) = ((au && bu) || (av && bv)) := by
  cases au <;> cases av <;> cases bu <;> cases bv <;> simp_all

theorem snoc_or (wu wv wuv : List Bool) (x y z : Bool) (h1 : wv.length = wu.length)
    (h2 : wuv.length = wu.length)
    (hor : ∀ k, wuv.getD k false = (wu.getD k false || wv.getD k false))
    (hz : z = (x || y)) :
    ∀ k, (wuv ++ [z]).getD k false = ((wu ++ [x]).getD k false || (wv ++ [y]).getD k false) := by
  intro k
  rcases lt_trichotomy k wu.length with h | h | h
  · rw [List.getD_append wuv [z] false k (by omega), List.getD_append wu [x] false k (by omega),
      List.getD_append wv [y] false k (by omega)]
    exact hor k
  · subst h
    rw [List.getD_append_right wuv [z] false wu.length (by omega),
      List.getD_append_right wu [x] false wu.length (by omega),
      List.getD_append_right wv [y] false wu.length (by omega)]
    simp [h1, h2, hz]
  · rw [List.getD_eq_default (wuv ++ [z]) false (by simp; omega),
      List.getD_eq_default (wu ++ [x]) false (by simp; omega),
      List.getD_eq_default (wv ++ [y]) false (by simp; omega)]
    rfl

theorem val_or (op : GateOp) (ins : List ℕ) (hop : op = GateOp.and ∨ op = GateOp.or)
    (hlen : ins.length ≤ 2) (wu wv wuv : List Bool) (h1 : wv.length = wu.length)
    (h2 : wuv.length = wu.length)
    (hor : ∀ k, wuv.getD k false = (wu.getD k false || wv.getD k false))
    (hns : ∀ a b, op = GateOp.and → ins = [a, b] → a < wu.length → b < wu.length →
      ¬ sep wu wv a b) :
    op.eval (ins.map fun i => wuv.getD i false) =
      (op.eval (ins.map fun i => wu.getD i false) ||
        op.eval (ins.map fun i => wv.getD i false)) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rcases hop with rfl | rfl <;> rfl
  · rcases hop with rfl | rfl <;>
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false, hor a]
  · simp only [List.map_cons, List.map_nil]
    rw [hor a, hor b]
    rcases hop with rfl | rfl
    · simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
      by_cases ha : a < wu.length
      · by_cases hb : b < wu.length
        · exact core _ _ _ _ (hns a b rfl rfl ha hb)
        · rw [List.getD_eq_default wu false (n := b) (by omega),
            List.getD_eq_default wv false (n := b) (by omega)]
          simp
      · rw [List.getD_eq_default wu false (n := a) (by omega),
          List.getD_eq_default wv false (n := a) (by omega)]
        simp
    · simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      cases wu.getD a false <;> cases wv.getD a false <;> cases wu.getD b false <;>
        cases wv.getD b false <;> rfl
  · simp at hlen

theorem pre (gs : List Gate) (w : List Bool) : ∃ t, gs.foldl stp w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (stp w g)
    exact ⟨_ :: t, by rw [List.foldl_cons, ht, stp, List.append_assoc]; rfl⟩

theorem pre_getD (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (gs.foldl stp w).getD k false = w.getD k false := by
  obtain ⟨t, ht⟩ := pre gs w
  rw [ht, List.getD_append w t false k hk]

theorem inv (gs : List Gate) :
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    ∀ (wu wv wuv : List Bool), wv.length = wu.length → wuv.length = wu.length →
      (∀ k, wuv.getD k false = (wu.getD k false || wv.getD k false)) →
      (∀ (j : ℕ) (g : Gate) (a b : ℕ), gs[j]? = some g → g.op = GateOp.and →
        g.inputs = [a, b] → a < wu.length + j → b < wu.length + j →
        ¬ sep (gs.foldl stp wu) (gs.foldl stp wv) a b) →
      ∀ k, (gs.foldl stp wuv).getD k false =
        ((gs.foldl stp wu).getD k false || (gs.foldl stp wv).getD k false) := by
  induction gs with
  | nil => intro _ wu wv wuv _ _ hor _ k; exact hor k
  | cons g gs ih =>
    intro hgs wu wv wuv h1 h2 hor hno
    have hg := hgs g (by simp)
    have hval := val_or g.op g.inputs hg.1 hg.2 wu wv wuv h1 h2 hor (by
      intro a b hand hin ha hb hs
      apply hno 0 g a b rfl hand hin (by omega) (by omega)
      unfold sep at hs ⊢
      rw [pre_getD (g :: gs) wu a ha, pre_getD (g :: gs) wv a (by omega),
        pre_getD (g :: gs) wu b hb, pre_getD (g :: gs) wv b (by omega)]
      exact hs)
    exact ih (fun g' hg' => hgs g' (by simp [hg'])) (stp wu g) (stp wv g) (stp wuv g)
      (by simp [stp, h1]) (by simp [stp, h2])
      (snoc_or wu wv wuv _ _ _ h1 h2 hor hval)
      (fun j g' a b hj hand hin ha hb => hno (j + 1) g' a b
        (by rw [List.getElem?_cons_succ]; exact hj) hand hin
        (by simp [stp] at ha; omega) (by simp [stp] at hb; omega))

end PEqualNP.Outside.LMeta201C

open PEqualNP.Outside.LMeta201C

theorem PEqualNP.Outside.L_meta_201 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo C → (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → PEqualNP.MetaComplexity.circuitFun n C = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → ∀ u v : Fin n, G.Adj u v → ∃ j : ℕ, (∃ (g : PEqualNP.CircuitLowerBounds.Gate) (a b : ℕ), C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ g.inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧ (((C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD a false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD a false = false ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD b false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD b false = false) ∨ ((C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD a false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD a false = false ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = u)))).getD b false = true ∧ (C.wires (List.ofFn (fun i : Fin n => decide (i = v)))).getD b false = false))) := by
  intro n G _ C hfan hnot hfun u v huv
  by_contra hcon
  have hgs : ∀ g ∈ C.gates,
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hfan g hg
    have h3 := hnot g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h h3
  have key := inv C.gates hgs
    (List.ofFn (fun i : Fin n => decide (i = u)))
    (List.ofFn (fun i : Fin n => decide (i = v)))
    (List.ofFn (fun i : Fin n => decide (i = u) || decide (i = v)))
    (by simp) (by simp)
    (by
      intro k
      by_cases h : k < n <;> simp [h])
    (by
      intro j g a b hj hand hin ha hb hs
      apply hcon
      simp only [List.length_ofFn] at ha hb
      exact ⟨j, g, a, b, hj, hand, hin, ha, hb, hs⟩)
    C.output
  have e1 : PEqualNP.MetaComplexity.circuitFun n C (fun i : Fin n => decide (i = u)) = false := by
    rw [hfun]
    simp
  have e2 : PEqualNP.MetaComplexity.circuitFun n C (fun i : Fin n => decide (i = v)) = false := by
    rw [hfun]
    simp
  have e3 : PEqualNP.MetaComplexity.circuitFun n C
      (fun i : Fin n => decide (i = u) || decide (i = v)) = true := by
    rw [hfun]
    exact decide_eq_true ⟨u, v, huv, by simp, by simp⟩
  change PEqualNP.MetaComplexity.circuitFun n C
      (fun i : Fin n => decide (i = u) || decide (i = v)) =
    (PEqualNP.MetaComplexity.circuitFun n C (fun i : Fin n => decide (i = u)) ||
      PEqualNP.MetaComplexity.circuitFun n C (fun i : Fin n => decide (i = v))) at key
  rw [e1, e2, e3] at key
  simp at key
