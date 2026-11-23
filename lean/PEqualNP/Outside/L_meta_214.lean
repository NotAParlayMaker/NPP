import Mathlib
import PEqualNP.Defs
namespace LMeta214
open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp


private abbrev Sig (n : ℕ) := (Fin n → Bool) → Prop
private def wire {n : ℕ} (gs : List Gate) (f : Sig n) :=
  ∃ i < n + gs.length, ∀ x, ((gs.foldl step (List.ofFn x)).getD i false = true ↔ f x)
private def good (gs : List Gate) (k : ℕ) :=
  (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
  ∃ A : Finset ℕ, A.card ≤ k ∧ ∀ j g, gs[j]? = some g → g.op = .and → j ∈ A

private lemma keep {n gs} {f : Sig n} (h : wire gs f) (ss : List Gate) : wire (gs ++ ss) f := by
  obtain ⟨i,hi,he⟩ := h
  refine ⟨i, by simp; omega, fun x => ?_⟩
  induction ss using List.reverseRecOn with
  | nil => simpa using he x
  | append_singleton ss g ih =>
    simp only [← List.append_assoc, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    rw [step, getD_append_left_lt _ _ _ (by simp [foldl_step_len]; omega)]
    exact ih

private lemma inp (n : ℕ) (v : Fin n) (gs : List Gate) : wire gs (fun x => x v = true) := by
  have h : wire [] (fun x : Fin n → Bool => x v = true) := by
    exact ⟨v.val, by simp, fun x => by simp [List.getD_eq_getElem?_getD, v.isLt]⟩
  simpa using keep h gs

private def fee : GateOp → ℕ
  | .and => 1
  | _ => 0

private lemma addgood {gs k} (hg : good gs k) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hl : g.inputs.length ≤ 2) :
    good (gs ++ [g]) (k + fee g.op) := by
  obtain ⟨hg,A,hc,ha⟩ := hg
  constructor
  · intro t ht; simp only [List.mem_append, List.mem_singleton] at ht; rcases ht with ht | rfl; exact hg _ ht; exact ⟨hop,hl⟩
  · classical
    by_cases h : g.op = .and
    · refine ⟨insert gs.length A, ?_, ?_⟩
      · exact (Finset.card_insert_le _ _).trans (by simp [h,fee]; omega)
      · intro j t hj ht
        by_cases hj' : j < gs.length
        · exact Finset.mem_insert_of_mem (ha _ _ (by simpa [List.getElem?_append_left hj'] using hj) ht)
        · have hjlt := List.getElem?_eq_some_iff.mp hj
          have : j = gs.length := by have := hjlt.choose; simp at this; omega
          simp [this]
    · refine ⟨A, by omega, ?_⟩
      intro j t hj ht
      by_cases hj' : j < gs.length
      · exact ha _ _ (by simpa [List.getElem?_append_left hj'] using hj) ht
      · rw [List.getElem?_append_right (by omega)] at hj
        cases he : j - gs.length with
        | zero => simp [he] at hj; subst t; contradiction
        | succ z => simp [he] at hj

private lemma make {n : ℕ} (gs : List Gate) (g : Gate) (f : Sig n)
    (he : ∀ x, g.op.eval (g.inputs.map fun i => (gs.foldl step (List.ofFn x)).getD i false) = true ↔ f x) :
    wire (gs ++ [g]) f := by
  refine ⟨n + gs.length, by simp, fun x => ?_⟩
  have hh : (gs.foldl step (List.ofFn x)).length = n + gs.length := by simp [foldl_step_len]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, step]
  rw [← hh, getD_append_self]
  exact he x

private lemma emptyWire {n gs k} (hg : good gs k) :
    ∃ ss, good (gs ++ ss) k ∧ wire (gs ++ ss) (fun _ : Fin n → Bool => False) := by
  let g : Gate := ⟨.or, []⟩
  exact ⟨[g], addgood hg g (by simp [g]) (by decide), make gs g _ (by simp [g, GateOp.eval])⟩

private lemma combine {n gs k} {a b : Sig n} (hg : good gs k) (ha : wire gs a) (hb : wire gs b)
    (meet : Bool) : ∃ ss, good (gs ++ ss) (k + meet.toNat) ∧
    wire (gs ++ ss) (fun x => if meet then a x ∧ b x else a x ∨ b x) := by
  obtain ⟨i,_,hi⟩ := ha
  obtain ⟨j,_,hj⟩ := hb
  simp only [List.getD_eq_getElem?_getD] at hi hj
  cases meet with
  | false =>
    let g : Gate := ⟨.or,[i,j]⟩
    exact ⟨[g], addgood hg g (by simp [g]) (by simp [g]), make gs g _ (by simp [g, GateOp.eval,hi,hj])⟩
  | true =>
    let g : Gate := ⟨.and,[i,j]⟩
    exact ⟨[g], addgood hg g (by simp [g]) (by simp [g]), make gs g _ (by simp [g, GateOp.eval,hi,hj])⟩

private lemma neighbors {n gs k} (hg : good gs k) (V : Finset (Fin n)) :
    ∃ ss, good (gs ++ ss) k ∧ wire (gs ++ ss) (fun x => ∃ v ∈ V, x v = true) := by
  classical
  induction V using Finset.induction_on with
  | empty => simpa using (emptyWire (n := n) hg)
  | @insert v V hv ih =>
    obtain ⟨s,hs,hw⟩ := ih
    obtain ⟨t,ht,hw'⟩ := combine hs (inp n v _) hw false
    refine ⟨s ++ t, by simpa [List.append_assoc] using ht, ?_⟩
    simpa [List.append_assoc] using hw'

private def hasStar {n} (G : SimpleGraph (Fin n)) (v : Fin n) : Sig n :=
  fun x => x v = true ∧ ∃ w, G.Adj v w ∧ x w = true

private theorem stars {n} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) :
    ∃ gs, good gs T.card ∧ wire gs (fun x => ∃ v ∈ T, hasStar G v x) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have hg : good [] 0 := ⟨by simp, ∅, by simp, by simp⟩
    simpa using (emptyWire (n := n) hg)
  | @insert v T hv ih =>
    obtain ⟨gs,hg,hw⟩ := ih
    obtain ⟨s,hs,hn⟩ := neighbors hg (Finset.univ.filter (G.Adj v))
    obtain ⟨t,ht,ha⟩ := combine hs (inp n v _) hn true
    have ha' : wire ((gs ++ s) ++ t) (hasStar G v) := by unfold hasStar; simpa using ha
    obtain ⟨u,hu,hr⟩ := combine ht ha' (keep (keep hw s) t) false
    exact ⟨_, by simpa [hv] using hu, by simpa using hr⟩

end LMeta214
open LMeta214 PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_214 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (T : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ T.card ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) ∧ ∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) := by
  intro n G T cover
  obtain ⟨gs,⟨hg,A,hA,ha⟩,j,hj,he⟩ := stars G T
  refine ⟨⟨gs,j⟩,hg,⟨A,hA,ha⟩,fun x => (he x).trans ?_⟩
  constructor
  · rintro ⟨u,_,hx,v,hv,hy⟩
    exact ⟨u,v,hv,hx,hy⟩
  · rintro ⟨u,v,huv,hu,hv⟩
    rcases cover u v huv with h | h
    · exact ⟨u,h,hu,v,huv,hv⟩
    · exact ⟨v,h,hv,u,huv.symm,hu⟩
