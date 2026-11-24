import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3789

open PEqualNP.CircuitLowerBounds PEqualNP.CleanedNonEdge

def stepW (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]

def Inv (n : ℕ) (ws : List Bool) (cs : List (List ℕ)) : Prop :=
  ws.length = n + cs.length ∧
  (∀ k < cs.length, ∀ j ∈ cs.getD k [], j < cs.length) ∧
  (∀ k < cs.length, ∀ j ∈ cs.getD k [],
    ws.getD (n + j) false = true → ws.getD (n + k) false = true)

lemma getD_append_left_lt {α : Type*} (l₁ l₂ : List α) (d : α) (i : ℕ) (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_singleton_eq {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

lemma inv_step (n : ℕ) (ws : List Bool) (cs : List (List ℕ)) (gate : Gate)
    (h : Inv n ws cs) : Inv n (stepW ws gate) (orStep n cs gate) := by
  rcases h with ⟨hlen, hlt, himp⟩
  have hclen : (orStep n cs gate).length = cs.length + 1 := by
    simp [orStep]
  refine ⟨?_, ?_, ?_⟩
  · simp [stepW, hlen, hclen]
    omega
  · intro k hk j hj
    rw [hclen] at hk ⊢
    by_cases hklt : k < cs.length
    · have hget : (orStep n cs gate).getD k [] = cs.getD k [] := by
        unfold orStep
        exact getD_append_left_lt cs _ [] k hklt
      rw [hget] at hj
      exact Nat.lt_trans (hlt k hklt j hj) (Nat.lt_succ_self _)
    · have hkeq : k = cs.length := by omega
      subst hkeq
      unfold orStep at hj
      rw [getD_append_singleton_eq, List.mem_cons] at hj
      rcases hj with rfl | hj
      · exact Nat.lt_succ_self _
      · split_ifs at hj with hop
        · rw [List.mem_flatMap] at hj
          rcases hj with ⟨u, hu, hju⟩
          rw [List.mem_filter, decide_eq_true_eq] at hu
          have hun : u - n < cs.length := by omega
          exact Nat.lt_trans (hlt (u - n) hun j hju) (Nat.lt_succ_self _)
        · simp at hj
  · intro k hk j hj htrue
    rw [hclen] at hk
    by_cases hklt : k < cs.length
    · have hget : (orStep n cs gate).getD k [] = cs.getD k [] := by
        unfold orStep
        exact getD_append_left_lt cs _ [] k hklt
      rw [hget] at hj
      have hjlt : j < cs.length := hlt k hklt j hj
      have hnj : n + j < ws.length := by omega
      have hnk : n + k < ws.length := by omega
      have htrue' : ws.getD (n + j) false = true := by
        unfold stepW at htrue
        rw [getD_append_left_lt ws _ false (n + j) hnj] at htrue
        exact htrue
      have hktrue : ws.getD (n + k) false = true := himp k hklt j hj htrue'
      unfold stepW
      rw [getD_append_left_lt ws _ false (n + k) hnk]
      exact hktrue
    · have hkeq : k = cs.length := by omega
      subst hkeq
      unfold orStep at hj
      rw [getD_append_singleton_eq, List.mem_cons] at hj
      rcases hj with rfl | hj
      · exact htrue
      · split_ifs at hj with hop
        · rw [List.mem_flatMap] at hj
          rcases hj with ⟨u, hu, hju⟩
          rw [List.mem_filter, decide_eq_true_eq] at hu
          have hun : u - n < cs.length := by omega
          have hjlt : j < cs.length := hlt (u - n) hun j hju
          have hnj : n + j < ws.length := by omega
          have htrue' : ws.getD (n + j) false = true := by
            unfold stepW at htrue
            rw [getD_append_left_lt ws _ false (n + j) hnj] at htrue
            exact htrue
          have hutrue : ws.getD (n + (u - n)) false = true := himp (u - n) hun j hju htrue'
          have huadd : n + (u - n) = u := by omega
          rw [huadd] at hutrue
          unfold stepW
          rw [← hlen, getD_append_singleton_eq]
          rw [hop]
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
          exact ⟨true, ⟨u, hu.1, hutrue⟩, rfl⟩
        · simp at hj

lemma inv_foldl (n : ℕ) (gs : List Gate) :
    ∀ (ws : List Bool) (cs : List (List ℕ)),
      Inv n ws cs → Inv n (gs.foldl stepW ws) (gs.foldl (orStep n) cs) := by
  induction gs with
  | nil => intro ws cs h; exact h
  | cons g gs ih =>
    intro ws cs h
    exact ih (stepW ws g) (orStep n cs g) (inv_step n ws cs g h)

lemma main (n : ℕ) (C : Circuit) (g w : ℕ) (x : List Bool)
    (hx : x.length = n) (hr : OrReaches n C w g)
    (ht : (C.wires x).getD (n + g) false = true) :
    (C.wires x).getD w false = true := by
  have hbase : Inv n x [] := by
    refine ⟨by simp [hx], ?_, ?_⟩
    · intro k hk; simp at hk
    · intro k hk; simp at hk
  have hfold : Inv n (C.wires x) (orSets n C) := inv_foldl n C.gates x [] hbase
  rcases hr with ⟨hnw, hmem⟩
  have hlt : w - n < (orSets n C).length := by
    by_contra hge
    have hle : (orSets n C).length ≤ w - n := by omega
    have hnil : (orSets n C).getD (w - n) [] = [] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr hle]
    rw [hnil] at hmem
    simp at hmem
  have hres := hfold.2.2 (w - n) hlt g hmem ht
  have heq : n + (w - n) = w := by omega
  rw [heq] at hres
  exact hres

end PEqualNP.Outside.L_meta_3789

theorem PEqualNP.Outside.L_meta_3789 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ) (x5 : List Bool), x5.length = x1 → PEqualNP.CleanedNonEdge.OrReaches x1 x2 x4 x3 → (x2.wires x5).getD (x1 + x3) Bool.false = Bool.true → (x2.wires x5).getD x4 Bool.false = Bool.true := by
  intro x1 x2 x3 x4 x5 hx hr ht
  exact PEqualNP.Outside.L_meta_3789.main x1 x2 x3 x4 x5 hx hr ht
