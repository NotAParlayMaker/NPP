import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7585
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

theorem eff_eval (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (f : ℕ → Bool) :
    g.op.eval (g.inputs.map f)
      = g.op.eval ((List.take (bif g.op.eval [false] then 1 else 2) g.inputs).map f) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change ins.length ≤ 2 at hlen
  have h2 : List.take 2 ins = ins := List.take_of_length_le hlen
  rcases hop with rfl | rfl | rfl
  · simp [GateOp.eval, h2]
  · simp [GateOp.eval, h2]
  · cases ins with
    | nil => rfl
    | cons a t => simp [GateOp.eval]

theorem noreadE (i : ℕ) : ∀ (gs : List Gate) (U U' : List Bool), U.length = U'.length →
    i < U.length →
    (∀ g ∈ gs, (g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
      i ∉ List.take (bif g.op.eval [false] then 1 else 2) g.inputs) →
    (∀ t, t ≠ i → U.getD t false = U'.getD t false) →
    ∀ t, t ≠ i → (wf gs U).getD t false = (wf gs U').getD t false := by
  intro gs
  induction gs with
  | nil => intro U U' _ _ _ h t ht; exact h t ht
  | cons g gs ih =>
    intro U U' hlen hi hg h t ht
    rw [wf_cons, wf_cons]
    have hgg := hg g List.mem_cons_self
    have hv : g.op.eval (g.inputs.map fun j => U.getD j false)
        = g.op.eval (g.inputs.map fun j => U'.getD j false) := by
      rw [eff_eval g hgg.1 (fun j => U.getD j false), eff_eval g hgg.1 (fun j => U'.getD j false)]
      congr 1
      apply List.map_congr_left
      intro j hj
      exact h j (fun e => hgg.2 (e ▸ hj))
    rw [hv]
    refine ih _ _ (by simp [hlen]) (by simp; omega)
      (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) ?_ t ht
    intro s hs
    rcases Nat.lt_trichotomy s U.length with h1 | h1 | h1
    · rw [getD_snoc_lt _ _ _ h1, getD_snoc_lt _ _ _ (by omega)]
      exact h s hs
    · rw [h1, getD_snoc_eq, hlen, getD_snoc_eq]
    · rw [getD_snoc_gt _ _ _ h1, getD_snoc_gt _ _ _ (by omega)]

end PEqualNP.Outside.L_meta_7585

open PEqualNP.Outside.L_meta_7585 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_7585 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin x1), x2.Adj x5 x6 → PEqualNP.MetaComplexity.FanInTwo x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → ∃ x10 ∈ x4.gates, ↑x5 ∈ List.take (bif x10.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x10.inputs := by
  intro n G _ C a b hab hC hfun
  by_contra hno
  have hno' : ∀ g ∈ C.gates, (a : ℕ) ∉ List.take (bif g.op.eval [false] then 1 else 2) g.inputs :=
    fun g hg hin => hno ⟨g, hg, hin⟩
  have hne : a ≠ b := G.ne_of_adj hab
  have hagree : ∀ t, t ≠ (a : ℕ) →
      (List.ofFn fun v : Fin n => decide (v = a ∨ v = b)).getD t false
        = (List.ofFn fun v : Fin n => decide (v = b)).getD t false := by
    intro t ht
    by_cases htn : t < n
    · have e1 := getD_ofFn (fun v : Fin n => decide (v = a ∨ v = b)) ⟨t, htn⟩
      have e2 := getD_ofFn (fun v : Fin n => decide (v = b)) ⟨t, htn⟩
      simp only at e1 e2
      rw [e1, e2]
      have hta : (⟨t, htn⟩ : Fin n) ≠ a := fun e => ht (by rw [← e])
      simp [hta]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  have hw := noreadE (a : ℕ) C.gates _ _ (by simp) (by simp) (fun g hg => ⟨hC g hg, hno' g hg⟩) hagree
  have hA : PEqualNP.MetaComplexity.circuitFun n C (fun v : Fin n => decide (v = a ∨ v = b)) = true := by
    rw [hfun]
    unfold PEqualNP.MetaComplexity.NestedCover.graphFun
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inr ⟨a, b, hab, Or.inl rfl, Or.inr rfl⟩
  have hB : PEqualNP.MetaComplexity.circuitFun n C (fun v : Fin n => decide (v = b)) = false := by
    rw [hfun]
    unfold PEqualNP.MetaComplexity.NestedCover.graphFun
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq]
    refine ⟨fun ⟨_, h, _⟩ => by simp at h, ?_⟩
    rintro ⟨u, v, huv, hu, hv⟩
    rw [hu, hv] at huv
    exact G.irrefl huv
  by_cases ho : C.output = (a : ℕ)
  · have hC1 : PEqualNP.MetaComplexity.circuitFun n C (fun v : Fin n => decide (v = a)) = true := by
      show (wf C.gates (List.ofFn fun v : Fin n => decide (v = a))).getD C.output false = true
      rw [ho, wf_keep _ _ _ (by simp)]
      have e := getD_ofFn (fun v : Fin n => decide (v = a)) a
      simp only at e
      rw [e]
      simp
    rw [hfun] at hC1
    unfold PEqualNP.MetaComplexity.NestedCover.graphFun at hC1
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hC1
    rcases hC1 with ⟨_, h, _⟩ | ⟨u, v, huv, hu, hv⟩
    · simp at h
    · rw [hu, hv] at huv
      exact G.irrefl huv
  · have e : PEqualNP.MetaComplexity.circuitFun n C (fun v : Fin n => decide (v = a ∨ v = b))
        = PEqualNP.MetaComplexity.circuitFun n C (fun v : Fin n => decide (v = b)) := hw C.output ho
    rw [hA, hB] at e
    exact absurd e (by simp)
