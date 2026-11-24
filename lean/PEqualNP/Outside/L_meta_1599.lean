import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_1599

def value (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def wires {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  (Circuit.mk gs 0).wires (List.ofFn x)

lemma snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    wires (gs ++ [g]) x = wires gs x ++ [value g (wires gs x)] := by
  simp [wires, Circuit.wires, List.foldl_append, value]

lemma length_w {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (wires gs x).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wires, Circuit.wires]
  | append_singleton gs g ih => simp [snoc, ih, Nat.add_assoc]

lemma getSnoc {α : Type} (l : List α) (a d : α) (i : Nat) :
    (l ++ [a]).getD i d = if i = l.length then a else l.getD i d := by
  by_cases h : i < l.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, Nat.ne_of_lt h]
  · have k : l.length ≤ i := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right k]
    by_cases e : i = l.length
    · simp [e]
    · have t : 1 ≤ i-l.length := by omega
      simp [e, List.getElem?_eq_none (by simpa using t : [a].length ≤ i-l.length),
        List.getD_eq_getElem?_getD, List.getElem?_eq_none k]

def single {n : ℕ} (v : Fin n) (w : Fin n) : Bool := decide (w = v)

lemma pass {n : ℕ} (u v : Fin n) (gs : List Gate)
    (legal : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (dark : ∀ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and →
      (wires gs (pairInput u v)).getD (n+j) false = false) :
    ∀ i, (wires gs (pairInput u v)).getD i false = true →
      (wires gs (single u)).getD i false = true ∨ (wires gs (single v)).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi
    by_cases h : i < n
    · simpa [wires, Circuit.wires, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
        h, pairInput, single] using hi
    · simp [wires, Circuit.wires, List.getD_eq_getElem?_getD, List.getElem?_ofFn, h] at hi
  | append_singleton gs g ih =>
    have sub : ∀ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and →
        (wires gs (pairInput u v)).getD (n+j) false = false := by
      intro j hj hop
      have h := dark j (by simp; omega) (by rw [getSnoc, if_neg (Nat.ne_of_lt hj)]; exact hop)
      rw [snoc, getSnoc, length_w, if_neg (by omega)] at h
      exact h
    have old := ih (fun a ha => legal a (List.mem_append_left _ ha)) sub
    intro i hi
    by_cases h : i = n + gs.length
    · subst i
      simp only [snoc, getSnoc, length_w, if_true] at hi ⊢
      rcases legal g (by simp) with hand | hor
      · have e := dark gs.length (by simp) (by rw [getSnoc, if_pos rfl]; exact hand)
        simp only [snoc, getSnoc, length_w, if_true] at e
        simp [hi] at e
      · simp only [value, hor, GateOp.eval, List.any_eq_true, List.mem_map] at hi ⊢
        obtain ⟨_, ⟨j, hj, rfl⟩, yes⟩ := hi
        rcases old j yes with h | h
        · exact Or.inl ⟨_, ⟨j, hj, rfl⟩, h⟩
        · exact Or.inr ⟨_, ⟨j, hj, rfl⟩, h⟩
    · simp only [snoc, getSnoc, length_w, if_neg h] at hi ⊢
      exact old i hi

lemma singleton_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    graphFun G ∅ (single v) = false := by
  simp [graphFun, single, SimpleGraph.irrefl]

end PEqualNP.Outside.L_meta_1599

theorem PEqualNP.Outside.L_meta_1599 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.EdgeOwnership.AndOrOnly C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.EdgeOwnership.EveryEdgeOwned n G C := by
  classical
  intro n G inst C legal eqn u v hadj
  have existsLit : ∃ j, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      gateVal n C j (pairInput u v) = true := by
    by_contra no
    have dark : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        gateVal n C j (pairInput u v) = false := by
      intro j hj hg
      cases e : gateVal n C j (pairInput u v) with
      | false => rfl
      | true => exact False.elim (no ⟨j, hj, hg, e⟩)
    have yes : circuitFun n C (pairInput u v) = true := by
      rw [eqn]
      simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inr ⟨u,v,hadj,by simp [pairInput],by simp [pairInput]⟩
    have h := PEqualNP.Outside.L_meta_1599.pass u v C.gates legal dark C.output yes
    change circuitFun n C _ = true ∨ circuitFun n C _ = true at h
    simp [eqn, PEqualNP.Outside.L_meta_1599.singleton_false] at h
  have h := Nat.find_spec existsLit
  refine ⟨Nat.find existsLit, h.1, h.1, h.2.1, h.2.2, ?_⟩
  intro i hi _ hop
  cases e : gateVal n C i (pairInput u v) with
  | false => rfl
  | true => exact False.elim (Nat.find_min existsLit hi ⟨lt_trans hi h.1, hop, e⟩)
