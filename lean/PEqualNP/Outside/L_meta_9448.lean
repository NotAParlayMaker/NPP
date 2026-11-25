import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9448
open PEqualNP.CircuitLowerBounds



def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def opOf (b : Bool) : GateOp := if b = true then GateOp.or else GateOp.and

def f (b : Bool) (p q : Bool) : Bool := if b = true then (p || q) else (p && q)

theorem ev (b p q : Bool) : (opOf b).eval [p, q] = f b p q := by
  cases b <;> cases p <;> cases q <;> rfl

def chain (b : Bool) (n : ℕ) : ℕ → ℕ → List (Fin n) → List Gate
  | _, _, [] => []
  | w, k, a :: l => ⟨opOf b, [w, a.val]⟩ :: chain b n (n + k) (k + 1) l

theorem chain_len (b : Bool) (n : ℕ) : ∀ (l : List (Fin n)) (w k : ℕ), (chain b n w k l).length = l.length := by
  intro l
  induction l with
  | nil => intro w k; rfl
  | cons a l ih => intro w k; simp [chain, ih]

theorem chain_mem (b : Bool) (n : ℕ) : ∀ (l : List (Fin n)) (w k : ℕ), (∀ a ∈ l, w ≠ a.val) →
    ∀ g ∈ chain b n w k l, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup := by
  intro l
  induction l with
  | nil => intro w k _ g hg; simp [chain] at hg
  | cons a l ih =>
    intro w k hw g hg
    simp only [chain, List.mem_cons] at hg
    rcases hg with rfl | hg
    · refine ⟨?_, rfl, ?_⟩
      · cases b
        · exact Or.inl rfl
        · exact Or.inr rfl
      · have := hw a (List.mem_cons_self ..)
        simp [this]
    · exact ih (n + k) (k + 1) (fun c _ => by have := c.isLt; omega) g hg

theorem chain_rb (b : Bool) (n : ℕ) : ∀ (l : List (Fin n)) (w k : ℕ), w < n + k →
    ∀ j, j < (chain b n w k l).length → ∀ i ∈ ((chain b n w k l).getD j ⟨GateOp.or, []⟩).inputs, i < n + k + j := by
  intro l
  induction l with
  | nil => intro w k _ j hj; simp [chain] at hj
  | cons a l ih =>
    intro w k hw j hj i hi
    cases j with
    | zero =>
      simp only [chain, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
      have := a.isLt
      rcases hi with rfl | rfl <;> omega
    | succ j =>
      simp only [chain, List.getD_cons_succ] at hi
      simp only [chain, List.length_cons] at hj
      have := ih (n + k) (k + 1) (by omega) j (by omega) i hi
      omega

theorem chain_val (b : Bool) (n : ℕ) (xv : Fin n → Bool) : ∀ (l : List (Fin n)) (W : List Bool) (w k : ℕ),
    W.length = n + k → (∀ a : Fin n, W.getD a.val false = xv a) → l ≠ [] →
    ((chain b n w k l).foldl stp W).getD (n + k + l.length - 1) false
      = l.foldl (fun acc a => f b acc (xv a)) (W.getD w false) := by
  intro l
  induction l with
  | nil => intro W w k _ _ h; exact absurd rfl h
  | cons a l ih =>
    intro W w k hW hx _
    have e1 : ∀ (L : List Bool) (v : Bool), (L ++ [v]).getD L.length false = v := by intro L v; simp
    have hstp : stp W ⟨opOf b, [w, a.val]⟩ = W ++ [f b (W.getD w false) (xv a)] := by
      unfold stp
      simp only [List.map_cons, List.map_nil]
      rw [ev, hx]
    simp only [chain, List.foldl_cons]
    rw [hstp]
    by_cases hl : l = []
    · subst hl
      simp only [chain, List.foldl_nil, List.length_cons, List.length_nil]
      have : n + k + (0 + 1) - 1 = W.length := by omega
      rw [this, e1]
    · have h := ih (W ++ [f b (W.getD w false) (xv a)]) (n + k) (k + 1) (by simp; omega)
        (fun c => by
          rw [List.getD_append _ _ _ _ (by have := c.isLt; omega)]
          exact hx c) hl
      have e : n + k + (l.length + 1) - 1 = n + (k + 1) + l.length - 1 := by omega
      rw [List.length_cons, e, h, ← hW, e1]

theorem fold_any (b : Bool) (n : ℕ) (xv : Fin n → Bool) : ∀ (l : List (Fin n)) (v : Bool),
    l.foldl (fun acc a => f b acc (xv a)) v
      = if b = true then (v || l.any xv) else (v && l.all xv) := by
  intro l
  induction l with
  | nil => intro v; cases b <;> simp
  | cons a l ih =>
    intro v
    rw [List.foldl_cons, ih]
    cases b <;> simp [f, Bool.or_assoc, Bool.and_assoc]

theorem main (n : ℕ) (b : Bool) (x3 : Fin n) (x4 : List (Fin n)) (hne : x4 ≠ [])
    (hnd : (x3 :: x4).Nodup) :
    ∃ C : Circuit, C.size = x4.length ∧ C.output = n + C.size - 1 ∧ PEqualNP.TopForm.IsAO2 n C ∧
      (∀ g ∈ C.gates, g.inputs.Nodup) ∧ ∀ x : List Bool, x.length = n →
        C.eval x = if b = true then (x3 :: x4).any fun a => x.getD a.val false
          else (x3 :: x4).all fun a => x.getD a.val false := by
  have hw : ∀ a ∈ x4, x3.val ≠ a.val := by
    intro a ha h
    exact (List.nodup_cons.1 hnd).1 (Fin.ext h ▸ ha)
  have hm := chain_mem b n x4 x3.val 0 hw
  have hlen := chain_len b n x4 x3.val 0
  refine ⟨⟨chain b n x3.val 0 x4, n + x4.length - 1⟩, hlen, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · show n + x4.length - 1 = n + (chain b n x3.val 0 x4).length - 1
    rw [hlen]
  · intro g hg
    exact (hm g hg).1
  · intro j hj i hi
    have := chain_rb b n x4 x3.val 0 (by have := x3.isLt; omega) j hj i hi
    omega
  · intro g hg
    exact (hm g hg).2.1
  · intro g hg
    exact (hm g hg).2.2
  · intro x hx
    show ((chain b n x3.val 0 x4).foldl stp x).getD (n + x4.length - 1) false = _
    have h := chain_val b n (fun a => x.getD a.val false) x4 x x3.val 0 (by omega) (fun _ => rfl) hne
    rw [Nat.add_zero] at h
    rw [h, fold_any, List.any_cons, List.all_cons]

end PEqualNP.Outside.L_meta_9448

open PEqualNP.Outside.L_meta_9448 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_9448 : ∀ (x1 : ℕ) (x2 : Bool) (x3 : Fin x1) (x4 : List (Fin x1)), x4 ≠ [] → (x3 :: x4).Nodup → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), x7.size = x4.length ∧ x7.output = x1 + x7.size - (1 : ℕ) ∧ PEqualNP.TopForm.IsAO2 x1 x7 ∧ (∀ x8 ∈ x7.gates, x8.inputs.Nodup) ∧ ∀ (x8 : List Bool), x8.length = x1 → x7.eval x8 = if x2 = Bool.true then (x3 :: x4).any fun (x10 : Fin x1) => x8.getD (↑x10) Bool.false else (x3 :: x4).all fun (x10 : Fin x1) => x8.getD (↑x10) Bool.false := by
  intro x1 x2 x3 x4 hne hnd
  exact main x1 x2 x3 x4 hne hnd
