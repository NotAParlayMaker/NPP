import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2666_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

lemma eval_nil (W : List Bool) (out : ℕ) :
    Circuit.eval ⟨[], out⟩ W = W.getD out false := rfl

lemma eval_cons (g : Gate) (gs : List Gate) (out : ℕ) (W : List Bool) :
    Circuit.eval ⟨g :: gs, out⟩ W =
      Circuit.eval ⟨gs, out⟩
        (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]) := rfl

lemma getD_snoc_len (l : List Bool) (v d : Bool) :
    (l ++ [v]).getD l.length d = v := by
  rw [List.getD_append_right l [v] d l.length (le_refl l.length)]
  simp

lemma getD_snoc_lt (l : List Bool) (v d : Bool) {i : ℕ} (h : i < l.length) :
    (l ++ [v]).getD i d = l.getD i d :=
  List.getD_append l [v] d i h

lemma any_congr_mem {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ a ∈ l, p a = q a) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.any_cons, List.any_cons, h a (by simp)]
      congr 1
      exact ih (fun b hb => h b (by simp [hb]))

/-- The AND/OR gate layer for the DNF of the edge function: for each edge `p` in turn, an AND
gate on its two endpoints followed by an OR gate that folds the AND value into the accumulator.
`start` is the wire index of the next AND gate and `acc` the wire index of the accumulator. -/
def dnfGates (n : ℕ) : ℕ → ℕ → List (Fin n × Fin n) → List Gate × ℕ
  | start, acc, [] => ([], acc)
  | start, acc, p :: ps =>
      let g₁ : Gate := { op := GateOp.and, inputs := [p.1.val, p.2.val] }
      let g₂ : Gate := { op := GateOp.or, inputs := [acc, start] }
      let r := dnfGates n (start + 2) (start + 1) ps
      (g₁ :: g₂ :: r.1, r.2)

noncomputable def edgeList (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    List (Fin n × Fin n) :=
  (Finset.univ.filter (fun p : Fin n × Fin n => G.Adj p.1 p.2 ∧ p.1 < p.2)).toList

noncomputable def dnfCircuit (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Circuit :=
  let L := edgeList n G
  let r := dnfGates n (n + 1) n L
  { gates := { op := GateOp.or, inputs := [] } :: r.1, output := r.2 }

lemma dnfGates_mono (n : ℕ) (start acc : ℕ) (L : List (Fin n × Fin n)) :
    ∀ g ∈ (dnfGates n start acc L).1,
      g.op = GateOp.and ∨ g.op = GateOp.or := by
  induction L generalizing start acc with
  | nil => intro g hg; simp [dnfGates] at hg
  | cons p ps ih =>
      intro g hg
      simp only [dnfGates, List.mem_cons] at hg
      rcases hg with rfl | rfl | hg
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact ih (start + 2) (start + 1) g hg

lemma dnfGates_inputs_le (n : ℕ) (start acc : ℕ) (L : List (Fin n × Fin n)) :
    ∀ g ∈ (dnfGates n start acc L).1, g.inputs.length ≤ 2 := by
  induction L generalizing start acc with
  | nil => intro g hg; simp [dnfGates] at hg
  | cons p ps ih =>
      intro g hg
      simp only [dnfGates, List.mem_cons] at hg
      rcases hg with rfl | rfl | hg
      · simp
      · simp
      · exact ih (start + 2) (start + 1) g hg

lemma dnf_mono (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Monotone2 (dnfCircuit n G) := by
  intro g hg
  simp only [dnfCircuit, List.mem_cons] at hg
  rcases hg with rfl | hg
  · exact ⟨Or.inr rfl, by simp⟩
  · exact ⟨dnfGates_mono n (n + 1) n (edgeList n G) g hg,
      dnfGates_inputs_le n (n + 1) n (edgeList n G) g hg⟩

lemma dnfGates_eval (n : ℕ) (L : List (Fin n × Fin n)) :
    ∀ (W : List Bool) (start acc : ℕ), start = W.length → acc < start →
      (∀ p ∈ L, p.1.val < start ∧ p.2.val < start) →
      Circuit.eval ⟨(dnfGates n start acc L).1, (dnfGates n start acc L).2⟩ W =
        (W.getD acc false ||
          L.any (fun p => W.getD p.1.val false && W.getD p.2.val false)) := by
  induction L with
  | nil =>
      intro W start acc hstart hacc h
      simp [dnfGates, eval_nil]
  | cons p ps ih =>
      intro W start acc hstart hacc h
      have hp1 : p.1.val < start := (h p (by simp)).1
      have hp2 : p.2.val < start := (h p (by simp)).2
      have hps : ∀ q ∈ ps, q.1.val < start + 2 ∧ q.2.val < start + 2 := by
        intro q hq
        have hq' := h q (by simp [hq])
        omega
      have hstart' : start = W.length := hstart
      dsimp only [dnfGates]
      rw [eval_cons]
      dsimp only
      rw [eval_cons]
      dsimp only
      simp only [List.map_cons, List.map_nil]
      set v₁ : Bool :=
        GateOp.and.eval [W.getD p.1.val false, W.getD p.2.val false] with hv₁
      set v₂ : Bool :=
        GateOp.or.eval [(W ++ [v₁]).getD acc false, (W ++ [v₁]).getD start false] with hv₂
      have hW₁len : (W ++ [v₁]).length = start + 1 := by simp [hstart']
      have hW₂len : ((W ++ [v₁]) ++ [v₂]).length = start + 2 := by
        rw [List.length_append, List.length_singleton, hW₁len]
      have hrec := ih ((W ++ [v₁]) ++ [v₂]) (start + 2) (start + 1)
        hW₂len.symm (by omega) hps
      rw [hrec]
      have hv₁val : v₁ = (W.getD p.1.val false && W.getD p.2.val false) := by
        rw [hv₁]
        simp [GateOp.eval]
      have hacc' : (W ++ [v₁]).getD acc false = W.getD acc false := by
        rw [getD_snoc_lt _ _ _ (by omega)]
      have hstart'' : (W ++ [v₁]).getD start false = v₁ := by
        rw [hstart']
        exact getD_snoc_len W v₁ false
      have hv₂val : v₂ = (W.getD acc false ||
          (W.getD p.1.val false && W.getD p.2.val false)) := by
        rw [hv₂, hacc', hstart'', hv₁val]
        simp [GateOp.eval]
      have hlast : ((W ++ [v₁]) ++ [v₂]).getD (start + 1) false = v₂ := by
        rw [show start + 1 = (W ++ [v₁]).length by omega]
        exact getD_snoc_len (W ++ [v₁]) v₂ false
      have hps' : ∀ q ∈ ps,
          ((W ++ [v₁]) ++ [v₂]).getD q.1.val false = W.getD q.1.val false ∧
          ((W ++ [v₁]) ++ [v₂]).getD q.2.val false = W.getD q.2.val false := by
        intro q hq
        have hq' := h q (by simp [hq])
        have hq1W : q.1.val < W.length := by rw [← hstart']; exact hq'.1
        have hq2W : q.2.val < W.length := by rw [← hstart']; exact hq'.2
        have hq1V : q.1.val < (W ++ [v₁]).length := by rw [hW₁len]; omega
        have hq2V : q.2.val < (W ++ [v₁]).length := by rw [hW₁len]; omega
        constructor
        · rw [getD_snoc_lt (W ++ [v₁]) v₂ false hq1V,
              getD_snoc_lt W v₁ false hq1W]
        · rw [getD_snoc_lt (W ++ [v₁]) v₂ false hq2V,
              getD_snoc_lt W v₁ false hq2W]
      rw [any_congr_mem (l := ps) (p := fun q =>
            ((W ++ [v₁]) ++ [v₂]).getD q.1.val false &&
              ((W ++ [v₁]) ++ [v₂]).getD q.2.val false)
          (q := fun q => W.getD q.1.val false && W.getD q.2.val false) (by
        intro q hq
        rw [(hps' q hq).1, (hps' q hq).2])]
      rw [hlast, hv₂val]
      rw [List.any_cons]
      simp [Bool.or_assoc]

lemma edgeList_mem (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : Fin n × Fin n) :
    p ∈ edgeList n G ↔ G.Adj p.1 p.2 ∧ p.1 < p.2 := by
  unfold edgeList
  rw [Finset.mem_toList, Finset.mem_filter]
  simp

lemma edgeList_any (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    (edgeList n G).any (fun p => x p.1 && x p.2) =
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff]
  constructor
  · intro hany
    rw [List.any_eq_true] at hany
    obtain ⟨p, hp, hptrue⟩ := hany
    rw [Bool.and_eq_true] at hptrue
    exact ⟨p.1, p.2, (edgeList_mem n G p).mp hp |>.1, hptrue.1, hptrue.2⟩
  · rintro ⟨u, v, hadj, hu, hv⟩
    rw [List.any_eq_true]
    rcases lt_trichotomy u v with huv | huv | hvu
    · refine ⟨(u, v), ?_, ?_⟩
      · rw [edgeList_mem]
        exact ⟨hadj, huv⟩
      · rw [Bool.and_eq_true]
        exact ⟨hu, hv⟩
    · subst huv
      exact absurd hadj (G.irrefl)
    · refine ⟨(v, u), ?_, ?_⟩
      · rw [edgeList_mem]
        exact ⟨hadj.symm, hvu⟩
      · rw [Bool.and_eq_true]
        exact ⟨hv, hu⟩

lemma dnf_eval (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    Circuit.eval (dnfCircuit n G) (List.ofFn x) = graphFun G ∅ x := by
  let W := List.ofFn x
  have hWlen : W.length = n := List.length_ofFn
  let L := edgeList n G
  have hconst : Circuit.eval (dnfCircuit n G) W =
      Circuit.eval ⟨(dnfGates n (n + 1) n L).1, (dnfGates n (n + 1) n L).2⟩
        (W ++ [false]) := by
    simp only [dnfCircuit, L]
    rw [eval_cons]
    simp [GateOp.eval]
  rw [hconst]
  have hgates := dnfGates_eval n L (W ++ [false]) (n + 1) n
    (by simp [hWlen]) (by omega)
    (by
      intro p hp
      exact ⟨by omega, by omega⟩)
  rw [hgates]
  have hfalse : (W ++ [false]).getD n false = false := by
    rw [← hWlen]
    exact getD_snoc_len W false false
  rw [hfalse, Bool.false_or]
  have hx : ∀ p ∈ L,
      (W ++ [false]).getD p.1.val false = x p.1 ∧
      (W ++ [false]).getD p.2.val false = x p.2 := by
    intro p hp
    have h1 : p.1.val < W.length := by rw [hWlen]; exact p.1.isLt
    have h2 : p.2.val < W.length := by rw [hWlen]; exact p.2.isLt
    constructor
    · rw [getD_snoc_lt _ _ _ h1, List.getD_eq_getElem W false h1]
      simp [W]
    · rw [getD_snoc_lt _ _ _ h2, List.getD_eq_getElem W false h2]
      simp [W]
  rw [any_congr_mem (l := L) (p := fun p =>
        (W ++ [false]).getD p.1.val false && (W ++ [false]).getD p.2.val false)
      (q := fun p => x p.1 && x p.2) (by
    intro p hp
    rw [(hx p hp).1, (hx p hp).2])]
  rw [edgeList_any, graphFun]
  simp

end PEqualNP.Outside.L_meta_2666_aux

open PEqualNP.Outside.L_meta_2666_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.L_meta_2666 :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj],
      ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x4 ∧
          PEqualNP.MetaComplexity.circuitFun x1 x4 =
            PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ := by
  classical
  intro n G hdec
  letI : DecidableRel G.Adj := hdec
  let C₀ : Circuit := dnfCircuit n G
  have hmono₀ : Monotone2 C₀ := dnf_mono n G
  have heval₀ : circuitFun n C₀ = graphFun G ∅ := by
    funext x
    exact dnf_eval n G x
  let P : ℕ → Prop := fun s =>
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ circuitFun n C = graphFun G ∅
  have hex : ∃ s, P s := ⟨C₀.size, C₀, hmono₀, le_rfl, heval₀⟩
  obtain ⟨C, hCmono, hCle, hCfun⟩ := Nat.find_spec hex
  have hPsize : P C.size := ⟨C, hCmono, le_rfl, hCfun⟩
  have hsize : C.size = Nat.find hex :=
    le_antisymm hCle (Nat.find_min' hex hPsize)
  refine ⟨C, ⟨hCmono, ?_⟩, hCfun⟩
  intro D hDmono hDfun
  rw [hsize]
  apply Nat.find_min' hex
  exact ⟨D, hDmono, le_rfl, hDfun.trans hCfun⟩
