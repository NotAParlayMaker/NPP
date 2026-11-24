import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3266
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def effective (g : Gate) : List ℕ := if g.op.eval [false] then g.inputs.take 1 else g.inputs
def cost (g : Gate) : ℕ := if !g.op.eval [false] then 1 else 0
lemma append_lookup (x : List Bool) (v : Bool) (i : ℕ) :
    (x ++ [v]).getD i false = if i = x.length then v else x.getD i false := by
  by_cases hi : i < x.length
  · rw [List.getD_append _ _ _ _ hi, ite_eq_right (by omega)]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    by_cases he : i = x.length
    · simp [he]
    · have hx : x.getD i false = false := List.getD_eq_default _ _ (by omega)
      have hn : i - x.length ≠ 0 := by omega
      rw [ite_eq_right he]
      calc
        [v].getD (i-x.length) false = false := List.getD_eq_default _ _ (by simp only [List.length_singleton];omega)
        _ = x.getD i false := hx.symm
lemma effective_length (g : Gate) (h : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    (effective g).length ≤ cost g + 1 := by
  rcases h with ⟨h,hsize⟩
  rcases h with h | h | h
  · simpa [effective,cost,h,GateOp.eval] using hsize
  · simpa [effective,cost,h,GateOp.eval] using hsize
  · simp [effective,cost,h,GateOp.eval]
lemma eval_agrees (g : Gate) (h : g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (x y : List Bool) (same : ∀ i ∈ effective g, x.getD i false = y.getD i false) :
    g.op.eval (g.inputs.map fun i => x.getD i false) =
      g.op.eval (g.inputs.map fun i => y.getD i false) := by
  rcases h with h | h | h
  · have same' : ∀ i ∈ g.inputs, x.getD i false = y.getD i false := by simpa [effective,h,GateOp.eval] using same
    rw [List.map_congr_left same']
  · have same' : ∀ i ∈ g.inputs, x.getD i false = y.getD i false := by simpa [effective,h,GateOp.eval] using same
    rw [List.map_congr_left same']
  · cases hi : g.inputs with
    | nil => rfl
    | cons i rest =>
      have hh := same i (by simp [effective,h,hi,GateOp.eval])
      simpa [h,hi,GateOp.eval] using congrArg Bool.not hh
lemma support (gs : List Gate) (legal : ∀ g ∈ gs,
    (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (n : ℕ) (F : Finset ℕ) :
    ∃ S : Finset ℕ, S.card ≤ (gs.map cost).sum + F.card ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) →
        ∀ i ∈ F, ({gates := gs, output := i} : Circuit).eval x =
          ({gates := gs, output := i} : Circuit).eval y := by
  induction gs generalizing n F with
  | nil => exact ⟨F, by simp, fun x y _ _ h i hi => h i hi⟩
  | cons g gs ih =>
    obtain ⟨S,hcard,hS⟩ := ih (fun k hk => legal k (by simp [hk])) (n+1) F
    let T : Finset ℕ := if n ∈ S then S.erase n ∪ (effective g).toFinset else S
    have ht : T.card ≤ S.card + cost g := by
      by_cases hn : n ∈ S
      · have h1 := Finset.card_union_le (S.erase n) (effective g).toFinset
        have h2 := List.toFinset_card_le (l := effective g)
        have h3 := effective_length g (legal g (by simp))
        have h4 := Finset.card_erase_add_one hn
        dsimp only [T];rw [ite_eq_left hn];omega
      · simp [T,hn]
    refine ⟨T, by simp only [List.map_cons,List.sum_cons];omega, ?_⟩
    intro x y hx hy same i hi
    have next : ∀ j ∈ S,
        (x ++ [g.op.eval (g.inputs.map fun k => x.getD k false)]).getD j false =
        (y ++ [g.op.eval (g.inputs.map fun k => y.getD k false)]).getD j false := by
      intro j hj
      rw [append_lookup,append_lookup,hx,hy]
      by_cases hjn : j = n
      · rw [ite_eq_left hjn,ite_eq_left hjn]
        apply eval_agrees g (legal g (by simp)).1 x y
        intro k hk
        apply same k
        have hn : n ∈ S := hjn ▸ hj
        simp only [T,ite_eq_left hn,Finset.mem_union,List.mem_toFinset]
        exact Or.inr hk
      · rw [ite_eq_right hjn,ite_eq_right hjn]
        apply same j
        by_cases hn : n ∈ S
        · simp [T,hn,Finset.mem_union,Finset.mem_erase,hjn,hj]
        · simpa [T,hn] using hj
    have answer := hS (x ++ [g.op.eval (g.inputs.map fun k => x.getD k false)])
      (y ++ [g.op.eval (g.inputs.map fun k => y.getD k false)])
      (by simp [hx]) (by simp [hy]) next i hi
    exact answer
lemma sum_cost (gs : List Gate) :
    (gs.map cost).sum = gs.countP (fun g => !g.op.eval [false]) := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [cost,List.countP_cons,ih,Nat.add_comm]
end PEqualNP.Outside.L_meta_3266

theorem PEqualNP.Outside.L_meta_3266 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → ∃ (x4 : Finset ℕ), x4.card ≤ List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => !x5.op.eval [Bool.false]) x2.gates + (1 : ℕ) ∧ ∀ (x5 x6 : List Bool), x5.length = x1 → x6.length = x1 → (∀ x9 ∈ x4, x5.getD x9 Bool.false = x6.getD x9 Bool.false) → x2.eval x5 = x2.eval x6 := by
  intro n C fan
  obtain ⟨S,hs,he⟩ := PEqualNP.Outside.L_meta_3266.support C.gates
    (fun g hg => fan g hg) n {C.output}
  refine ⟨S, ?_, ?_⟩
  · simpa only [PEqualNP.Outside.L_meta_3266.sum_cost, Finset.card_singleton] using hs
  · intro x y hx hy same
    exact he x y hx hy same C.output (by simp)
