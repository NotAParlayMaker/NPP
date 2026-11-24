import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3266_aux

open PEqualNP.CircuitLowerBounds

def stepF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepF x := rfl

theorem len (gs : List Gate) : ∀ w : List Bool, (gs.foldl stepF w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih]
    simp [stepF]
    omega

theorem snoc_ne (l : List Bool) (v : Bool) (w : ℕ) (h : w ≠ l.length) :
    (l ++ [v]).getD w false = l.getD w false := by
  rcases Nat.lt_or_gt_of_ne h with h1 | h1
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem snoc_eq (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD_eq_getElem?_getD]

theorem supp (n : ℕ) (gs : List Gate) :
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
    ∀ W : Finset ℕ, ∃ S : Finset ℕ,
      S.card ≤ W.card + List.countP (fun g : Gate => !g.op.eval [false]) gs ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) →
        ∀ w ∈ W, (gs.foldl stepF x).getD w false = (gs.foldl stepF y).getD w false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ W
    exact ⟨W, by simp, fun x y _ _ h w hw => by simpa using h w hw⟩
  | append_singleton gs g ih =>
    intro hf W
    have ih' := ih (fun g hg => hf g (List.mem_append_left _ hg))
    obtain ⟨hop, hlen⟩ := hf g (by simp)
    haveI := Classical.dec (g.op = GateOp.not)
    by_cases hm : n + gs.length ∈ W
    · obtain ⟨R, hRdef⟩ : ∃ R : List ℕ, R = if g.op = GateOp.not then g.inputs.take 1 else g.inputs :=
        ⟨_, rfl⟩
      obtain ⟨S, hSc, hSa⟩ := ih' (W.erase (n + gs.length) ∪ R.toFinset)
      refine ⟨S, ?_, ?_⟩
      · have c1 := Finset.card_union_le (W.erase (n + gs.length)) R.toFinset
        have c2 := Finset.card_erase_of_mem hm
        have c3 := List.toFinset_card_le R
        have c4 : 0 < W.card := Finset.card_pos.mpr ⟨_, hm⟩
        have c5 : R.length ≤ 1 + List.countP (fun g : Gate => !g.op.eval [false]) [g] := by
          rcases hop with h | h | h <;> simp [hRdef, h, GateOp.eval, List.countP_cons] <;> omega
        rw [List.countP_append]
        omega
      · intro x y hx hy hS w hw
        rw [List.foldl_append, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil, stepF]
        by_cases hwm : w = n + gs.length
        · subst hwm
          have ex : ∀ v, (gs.foldl stepF x ++ [v]).getD (n + gs.length) false = v := by
            intro v
            have := snoc_eq (gs.foldl stepF x) v
            rwa [len, hx] at this
          have ey : ∀ v, (gs.foldl stepF y ++ [v]).getD (n + gs.length) false = v := by
            intro v
            have := snoc_eq (gs.foldl stepF y) v
            rwa [len, hy] at this
          rw [ex, ey]
          have hR : ∀ i ∈ R, (gs.foldl stepF x).getD i false = (gs.foldl stepF y).getD i false :=
            fun i hi => hSa x y hx hy hS i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi))
          rcases hop with h | h | h
          · have e : (g.inputs.map fun i => (gs.foldl stepF x).getD i false) =
                (g.inputs.map fun i => (gs.foldl stepF y).getD i false) :=
              List.map_congr_left (fun i hi => hR i (by simp [hRdef, h, hi]))
            rw [e]
          · have e : (g.inputs.map fun i => (gs.foldl stepF x).getD i false) =
                (g.inputs.map fun i => (gs.foldl stepF y).getD i false) :=
              List.map_congr_left (fun i hi => hR i (by simp [hRdef, h, hi]))
            rw [e]
          · rw [h]
            cases hin : g.inputs with
            | nil => simp [GateOp.eval]
            | cons a t =>
              simp only [GateOp.eval, List.map_cons, List.headD_cons]
              rw [hR a (by simp [hRdef, h, hin])]
        · rw [snoc_ne _ _ _ (by rw [len, hx]; exact hwm), snoc_ne _ _ _ (by rw [len, hy]; exact hwm)]
          exact hSa x y hx hy hS w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwm, hw⟩))
    · obtain ⟨S, hSc, hSa⟩ := ih' W
      refine ⟨S, by rw [List.countP_append]; omega, ?_⟩
      intro x y hx hy hS w hw
      have hwm : w ≠ n + gs.length := fun e => hm (e ▸ hw)
      rw [List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, stepF]
      rw [snoc_ne _ _ _ (by rw [len, hx]; exact hwm), snoc_ne _ _ _ (by rw [len, hy]; exact hwm)]
      exact hSa x y hx hy hS w hw

end PEqualNP.Outside.L_meta_3266_aux

theorem PEqualNP.Outside.L_meta_3266 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → ∃ (x4 : Finset ℕ), x4.card ≤ List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => !x5.op.eval [Bool.false]) x2.gates + (1 : ℕ) ∧ ∀ (x5 x6 : List Bool), x5.length = x1 → x6.length = x1 → (∀ x9 ∈ x4, x5.getD x9 Bool.false = x6.getD x9 Bool.false) → x2.eval x5 = x2.eval x6 := by
  intro x1 x2 hF
  obtain ⟨S, hSc, hSa⟩ := PEqualNP.Outside.L_meta_3266_aux.supp x1 x2.gates
    (fun g hg => by
      have := hF g hg
      simpa using this) {x2.output}
  refine ⟨S, by rw [Finset.card_singleton] at hSc; omega, ?_⟩
  intro x y hx hy h
  exact hSa x y hx hy h x2.output (Finset.mem_singleton_self _)
