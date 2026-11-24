import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_4680

def sw : GateOp → GateOp
  | GateOp.and => GateOp.or
  | GateOp.or => GateOp.and
  | o => o

def sg (k i : ℕ) : ℕ := if i < k then i + 1 else 0

def dg : ℕ → List Gate → List Gate
  | _, [] => []
  | k, g :: gs => ⟨sw g.op, g.inputs.map (sg k)⟩ :: dg (k + 1) gs

theorem dg_length : ∀ (k : ℕ) (gs : List Gate), (dg k gs).length = gs.length
  | _, [] => rfl
  | k, g :: gs => by simp [dg, dg_length (k + 1) gs]

theorem dg_get : ∀ (k : ℕ) (gs : List Gate) (j : ℕ) (h : j < gs.length),
    ((dg k gs)[j]'(by rw [dg_length]; exact h)).op = sw (gs[j]'h).op
  | _, [], _, h => by simp at h
  | k, g :: gs, 0, _ => rfl
  | k, g :: gs, j + 1, h => by
    simp only [dg, List.getElem_cons_succ]; exact dg_get (k + 1) gs j (by simpa using h)

def Inv (k : ℕ) (WC WD : List Bool) : Prop :=
  WC.length = k ∧ WD.length = k + 1 ∧ WD.getD 0 false = true ∧
    ∀ i < k, WD.getD (i + 1) false = !(WC.getD i false)

theorem inv_read (k : ℕ) (WC WD : List Bool) (h : Inv k WC WD) (i : ℕ) :
    WD.getD (sg k i) false = !(WC.getD i false) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold sg
  split_ifs with hi
  · exact h4 i hi
  · rw [h3, List.getD_eq_default _ _ (by omega)]; rfl

theorem sw_eval (o : GateOp) (ho : o = GateOp.and ∨ o = GateOp.or) (l : List Bool) :
    (sw o).eval (l.map (fun b => !b)) = !(o.eval l) := by
  rcases ho with rfl | rfl <;> simp only [sw, GateOp.eval] <;>
    induction l with
    | nil => rfl
    | cons b l ih => cases b <;> simp_all

theorem fold_inv : ∀ (gs : List Gate) (k : ℕ) (WC WD : List Bool),
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) → Inv k WC WD →
    Inv (k + gs.length)
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) WC)
      ((dg k gs).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) WD)
  | [], k, WC, WD, _, h => h
  | g :: gs, k, WC, WD, hm, h => by
    simp only [dg, List.foldl_cons, List.length_cons]
    have e : (sw g.op).eval ((g.inputs.map (sg k)).map fun i => WD.getD i false) =
        !(g.op.eval (g.inputs.map fun i => WC.getD i false)) := by
      rw [List.map_map, ← sw_eval g.op (hm g (by simp))]
      congr 1; rw [List.map_map]; apply List.map_congr_left; intro i _
      exact inv_read k WC WD h i
    rw [e, show k + (gs.length + 1) = (k + 1) + gs.length by omega]
    apply fold_inv gs (k + 1) _ _ (fun g' hg' => hm g' (by simp [hg']))
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨by simp [h1], by simp [h2], by rw [List.getD_append _ _ _ _ (by omega)]; exact h3, ?_⟩
    intro i hi
    rcases Nat.lt_or_ge i k with hik | hik
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]; exact h4 i hik
    · have : i = k := by omega
      subst this
      rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp [h1, h2]

def dual (C : Circuit) : Circuit :=
  ⟨dg 26 C.gates, if C.output < 26 + C.gates.length then C.output + 1 else 0⟩

theorem dual_mono (C : Circuit) (hm : Monotone2 C) : Monotone2 (dual C) := by
  have : ∀ (k : ℕ) (gs : List Gate), (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
      g.inputs.length ≤ 2) → ∀ g ∈ dg k gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
      g.inputs.length ≤ 2 := by
    intro k gs
    induction gs generalizing k with
    | nil => intro _ g hg; simp [dg] at hg
    | cons g gs ih =>
      intro h g' hg'
      simp only [dg, List.mem_cons] at hg'
      rcases hg' with rfl | hg'
      · obtain ⟨h1, h2⟩ := h g (by simp)
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 ⊢
        refine ⟨?_, by simpa using h2⟩
        rcases h1 with h1 | h1 <;> simp [h1, sw]
      · exact ih (k + 1) (fun g'' hg'' => h g'' (by simp [hg''])) g' hg'
  exact this 26 C.gates hm

theorem dual_eval (C : Circuit) (hm : Monotone2 C) (x : Fin 26 → Bool) :
    (circuitFun 27 (dual C) fun x5 => Fin.cases true (fun x6 => !x x6) x5) = !circuitFun 26 C x := by
  have hb : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => by
    have := (hm g hg).1; simpa using this
  have h0 : Inv 26 (List.ofFn x) (List.ofFn fun x5 : Fin 27 => Fin.cases true (fun x6 => !x x6) x5) := by
    refine ⟨by simp, by simp, by simp [List.ofFn_succ], ?_⟩
    intro i hi
    rw [List.ofFn_succ, List.getD_cons_succ]
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi),
      List.getElem_ofFn, List.getElem_ofFn]
    rfl
  have hf := fold_inv C.gates 26 _ _ hb h0
  simp only [circuitFun, Circuit.eval, Circuit.wires, dual]
  have := inv_read _ _ _ hf C.output
  simp only [sg] at this
  exact this

theorem dual_count (C : Circuit) :
    Nat.card { x4 : Fin (dual C).gates.length // ((dual C).gates.get x4).op = GateOp.and } ≤
      {x4 : Fin C.gates.length | (C.gates.get x4).op = GateOp.or}.ncard := by
  have hl : (dual C).gates.length = C.gates.length := dg_length 26 C.gates
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_le_card_of_injective
    (fun y => ⟨Fin.cast hl y.1, ?_⟩) ?_
  · have h := y.2
    simp only [List.get_eq_getElem, dual] at h
    simp only [Set.mem_setOf_eq, List.get_eq_getElem, Fin.val_cast]
    rw [dg_get 26 C.gates y.1.val (by rw [← hl]; exact y.1.isLt)] at h
    revert h; cases (C.gates[y.1.val]'_).op <;> simp [sw]
  · intro a b h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext (by ext; have := congrArg Fin.val h; simpa using this)

end PEqualNP.Outside.L_meta_4680

theorem PEqualNP.Outside.L_meta_4680 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 ∧ Nat.card { x4 : Fin x3.gates.length // (x3.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and } ≤ {x4 : Fin x1.gates.length | (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard ∧ ∀ (x4 : Fin (26 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x3 fun (x5 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.cases Bool.true (fun (x6 : Fin (26 : ℕ)) => !x4 x6) x5) = !PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 x4 := by
  intro C hm
  exact ⟨PEqualNP.Outside.L_meta_4680.dual C, PEqualNP.Outside.L_meta_4680.dual_mono C hm,
    PEqualNP.Outside.L_meta_4680.dual_count C, PEqualNP.Outside.L_meta_4680.dual_eval C hm⟩
