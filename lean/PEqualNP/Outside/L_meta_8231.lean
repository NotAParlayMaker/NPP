import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_8231_aux

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

theorem getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

theorem gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

theorem wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj

theorem eval_mono (C : Circuit) (hC : Monotone2 C) (x y : Fin 11 → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  intro h
  have hm : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have h1 := (hC g hg).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h1
  have hin : ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
    intro i hi
    by_cases hlt : i < 11
    · rw [List.getD_eq_getElem _ _ (by simpa using hlt)] at hi ⊢
      simp only [List.getElem_ofFn] at hi ⊢
      exact hxy _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
      exact Bool.noConfusion hi
  exact wiresFrom_mono C.gates hm (List.ofFn x) (List.ofFn y) (by simp) hin C.output h

end PEqualNP.Outside.L_meta_8231_aux

open PEqualNP.Outside.L_meta_8231_aux

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_8231 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 : Fin (40 : ℕ)), x1.eval (List.map (fun (x4 : ℕ) => x4.testBit ↑x3) [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)]) = Nat.testBit (65535 : ℕ) ↑x3) → ∀ (x4 : Fin (11 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (11 : ℕ)) (x6 : Fin (11 : ℕ)), (↑x5, ↑x6) ∈ [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true := by
  intro C hC htest x
  let P : List ℕ := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768]
  let Q : List ℕ := [15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]
  let E : List (ℕ × ℕ) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
    (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  let row (r : ℕ) (i : Fin 11) := r.testBit i.val
  let pt (j : ℕ) : ℕ := (P ++ Q).getD j 0
  let edge (x : Fin 11 → Bool) :=
    E.any fun e => x (Fin.ofNat 11 e.1) && x (Fin.ofNat 11 e.2)
  let leRow (x y : Fin 11 → Bool) :=
    (List.finRange 11).all (fun i => !x i || y i)
  have leRow_imp (x y : Fin 11 → Bool) (h : leRow x y = true) :
      ∀ i, x i = true → y i = true := by
    intro i hxi
    have hi := List.all_eq_true.mp h i (List.mem_finRange i)
    simpa [hxi] using hi
  have bridge : ∀ j : Fin 40,
      List.map (fun (x4 : ℕ) => x4.testBit ↑j) [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)]
        = List.ofFn (row (pt j.val)) ∧ Nat.testBit (65535 : ℕ) j.val = decide (j.val < 16) := by
    decide +kernel
  have cover : ∀ x : Fin 11 → Bool,
      ((List.finRange 40).any (fun j => decide (j.val < 16) && leRow (row (pt j.val)) x) = edge x) ∧
      ((List.finRange 40).any (fun j => decide (16 ≤ j.val) && leRow x (row (pt j.val))) = !edge x) := by
    decide +kernel
  have edge_spec (x : Fin 11 → Bool) :
      edge x = true ↔ ∃ u v : Fin 11, (u.val, v.val) ∈ E ∧ x u = true ∧ x v = true := by
    dsimp only [edge]
    simp only [List.any_eq_true, Bool.and_eq_true]
    constructor
    · rintro ⟨⟨a,b⟩, hab, ha, hb⟩
      have bounds : ∀ e ∈ E, e.1 < 11 ∧ e.2 < 11 := by decide
      obtain ⟨ba,bb⟩ := bounds (a,b) hab
      refine ⟨Fin.ofNat 11 a, Fin.ofNat 11 b, ?_, ha, hb⟩
      change (a % 11,b % 11) ∈ E
      rwa [Nat.mod_eq_of_lt ba, Nat.mod_eq_of_lt bb]
    · rintro ⟨u,v,hm,hu,hv⟩
      refine ⟨(u.val,v.val), hm, ?_, ?_⟩
      · convert hu using 2
        exact Fin.ext (Nat.mod_eq_of_lt u.isLt)
      · convert hv using 2
        exact Fin.ext (Nat.mod_eq_of_lt v.isLt)
  have exact_test (j : Fin 40) :
      C.eval (List.ofFn (row (pt j.val))) = decide (j.val < 16) := by
    rw [← (bridge j).1, htest j, (bridge j).2]
  change C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 11, (u.val,v.val) ∈ E ∧ x u = true ∧ x v = true
  rw [← edge_spec]
  constructor
  · intro hx
    by_cases he : edge x = true
    · exact he
    · have he0 : edge x = false := Bool.eq_false_of_not_eq_true he
      have nq : (List.finRange 40).any
          (fun j => decide (16 ≤ j.val) && leRow x (row (pt j.val))) = true := by
        rw [(cover x).2, he0]; rfl
      obtain ⟨j, _, hj⟩ := List.any_eq_true.mp nq
      rw [Bool.and_eq_true] at hj
      obtain ⟨hj16, hle⟩ := hj
      have neg : C.eval (List.ofFn (row (pt j.val))) = false := by
        rw [exact_test j]
        have : ¬ j.val < 16 := by simpa using hj16
        simp [this]
      exact (Bool.false_ne_true (neg.symm.trans
        (eval_mono C hC x (row (pt j.val)) (leRow_imp _ _ hle) hx))).elim
  · intro hx
    have np : (List.finRange 40).any
        (fun j => decide (j.val < 16) && leRow (row (pt j.val)) x) = true := (cover x).1.trans hx
    obtain ⟨j, _, hj⟩ := List.any_eq_true.mp np
    rw [Bool.and_eq_true] at hj
    obtain ⟨hj16, hle⟩ := hj
    have pos : C.eval (List.ofFn (row (pt j.val))) = true := by
      rw [exact_test j]; exact hj16
    exact eval_mono C hC (row (pt j.val)) x (leRow_imp _ _ hle) pos
