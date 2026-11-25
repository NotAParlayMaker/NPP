import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7338_aux

open PEqualNP.CircuitLowerBounds

/-- an input map `Fin n1 → Fin n2` as a map on wire numbers -/
def sh_lift {n1 n2 : ℕ} (s : Fin n1 → Fin n2) : ℕ → ℕ := fun i => if h : i < n1 then ((s ⟨i, h⟩ : Fin n2) : ℕ) else 0

/-- wire `i` of the old circuit (on `n1` inputs) is wire `sh_rho i` of the relabelled one (on `n2` inputs) -/
def sh_rho (n1 n2 : ℕ) (σ : ℕ → ℕ) (i : ℕ) : ℕ := if i < n1 then σ i else i - n1 + n2

def sh_gmap (n1 n2 : ℕ) (σ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sh_rho n1 n2 σ)⟩

def sh_relabel (n1 n2 : ℕ) (σ : ℕ → ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (sh_gmap n1 n2 σ), sh_rho n1 n2 σ C.output⟩

/-- the relabelled circuit for an input map `s : Fin n1 → Fin n2` -/
def sh_rel {n1 n2 : ℕ} (s : Fin n1 → Fin n2) (C : Circuit) : Circuit := sh_relabel n1 n2 (sh_lift s) C

theorem sh_fold_rel (n1 n2 : ℕ) (σ : ℕ → ℕ) (hσ : ∀ i < n1, σ i < n2) (gs : List Gate) :
    ∀ w1 w2 : List Bool, n1 ≤ w1.length → n2 ≤ w2.length → w1.length - n1 = w2.length - n2 →
      (∀ i, w1.getD i false = w2.getD (sh_rho n1 n2 σ i) false) →
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1).getD i false =
        ((gs.map (sh_gmap n1 n2 σ)).foldl
          (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2).getD (sh_rho n1 n2 σ i) false := by
  induction gs with
  | nil => intro w1 w2 _ _ _ h; simpa using h
  | cons g gs ih =>
    intro w1 w2 h1 h2 hl h
    simp only [List.foldl_cons, List.map_cons]
    apply ih
    · simp; omega
    · simp; omega
    · simp; omega
    · have hv : g.op.eval (g.inputs.map fun i => w1.getD i false) =
          (sh_gmap n1 n2 σ g).op.eval ((sh_gmap n1 n2 σ g).inputs.map fun i => w2.getD i false) := by
        simp only [sh_gmap, List.map_map]
        congr 1
        apply List.map_congr_left
        intro a _
        exact h a
      intro i
      rcases Nat.lt_trichotomy i w1.length with hlt | heq | hgt
      · have hr : sh_rho n1 n2 σ i < w2.length := by
          unfold sh_rho; split_ifs with hi
          · have := hσ i hi; omega
          · omega
        rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hr]
        exact h i
      · have hr : sh_rho n1 n2 σ i = w2.length := by
          unfold sh_rho; split_ifs <;> omega
        rw [hr]
        subst heq
        rw [List.getD_append_right _ _ _ _ (le_refl _), List.getD_append_right _ _ _ _ (le_refl _)]
        simp only [Nat.sub_self, List.getD_cons_zero]
        exact hv
      · have hr : w2.length < sh_rho n1 n2 σ i := by
          unfold sh_rho; split_ifs <;> omega
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem sh_relabel_eval (n1 n2 : ℕ) (σ : ℕ → ℕ) (hσ : ∀ i < n1, σ i < n2) (C : Circuit)
    (w1 w2 : List Bool) (h1 : n1 ≤ w1.length) (h2 : n2 ≤ w2.length) (hl : w1.length - n1 = w2.length - n2)
    (h : ∀ i, w1.getD i false = w2.getD (sh_rho n1 n2 σ i) false) :
    C.eval w1 = (sh_relabel n1 n2 σ C).eval w2 := by
  unfold Circuit.eval Circuit.wires sh_relabel
  exact sh_fold_rel n1 n2 σ hσ C.gates w1 w2 h1 h2 hl h C.output

theorem sh_getD_ofFn_append {n : ℕ} (x : Fin n → Bool) (e : List Bool) (i : ℕ) :
    (List.ofFn x ++ e).getD i false = if h : i < n then x ⟨i, h⟩ else e.getD (i - n) false := by
  by_cases h : i < n
  · rw [List.getD_append _ _ _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h), dif_pos h]
    simp
  · rw [List.getD_append_right _ _ _ _ (by simp; omega), dif_neg h]
    simp

theorem sh_lift_lt {n1 n2 : ℕ} (s : Fin n1 → Fin n2) : ∀ i < n1, sh_lift s i < n2 := by
  intro i hi
  unfold sh_lift
  rw [dif_pos hi]
  exact (s ⟨i, hi⟩).isLt

theorem sh_relabel_eval_gen {n1 n2 : ℕ} (s : Fin n1 → Fin n2) (C : Circuit) (y : Fin n2 → Bool) (e : List Bool) :
    (sh_relabel n1 n2 (sh_lift s) C).eval (List.ofFn y ++ e) = C.eval (List.ofFn (fun i => y (s i)) ++ e) := by
  symm
  apply sh_relabel_eval n1 n2 (sh_lift s) (sh_lift_lt s)
  · simp
  · simp
  · simp
  · intro i
    rw [sh_getD_ofFn_append, sh_getD_ofFn_append]
    by_cases hi : i < n1
    · have hr : sh_rho n1 n2 (sh_lift s) i = ((s ⟨i, hi⟩ : Fin n2) : ℕ) := by
        unfold sh_rho sh_lift; rw [if_pos hi, dif_pos hi]
      rw [dif_pos hi, hr, dif_pos (s ⟨i, hi⟩).isLt]
    · have hr : sh_rho n1 n2 (sh_lift s) i = i - n1 + n2 := by
        unfold sh_rho; rw [if_neg hi]
      rw [dif_neg hi, hr, dif_neg (by omega), show i - n1 + n2 - n2 = i - n1 by omega]

theorem sh_relabel_eval_app {n1 n2 : ℕ} (s : Fin n1 → Fin n2) (C : Circuit) (y : Fin n2 → Bool) (e : List Bool) :
    (sh_rel s C).eval (List.ofFn y ++ e) = C.eval (List.ofFn (fun i => y (s i)) ++ e) :=
  sh_relabel_eval_gen s C y e

theorem sh_relabel_eval_nil {n1 n2 : ℕ} (s : Fin n1 → Fin n2) (C : Circuit) (y : Fin n2 → Bool) :
    (sh_rel s C).eval (List.ofFn y) = C.eval (List.ofFn (fun i => y (s i))) := by
  simpa [sh_rel] using sh_relabel_eval_gen s C y []

theorem sh_relabel_size (n1 n2 : ℕ) (σ : ℕ → ℕ) (C : Circuit) : (sh_relabel n1 n2 σ C).size = C.size := by
  simp [sh_relabel, Circuit.size]

theorem sh_relabel_fanInTwo (n1 n2 : ℕ) (σ : ℕ → ℕ) (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (sh_relabel n1 n2 σ C) := by
  intro g hg
  simp only [sh_relabel, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  simpa [sh_gmap] using h g0 hg0

theorem sh_relabel_monotone2 (n1 n2 : ℕ) (σ : ℕ → ℕ) (C : Circuit) (h : PEqualNP.MetaComplexity.Monotone2 C) :
    PEqualNP.MetaComplexity.Monotone2 (sh_relabel n1 n2 σ C) := by
  intro g hg
  simp only [sh_relabel, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  simpa [sh_gmap] using h g0 hg0

end PEqualNP.Outside.L_meta_7338_aux

theorem PEqualNP.Outside.L_meta_7338 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1 → Fin x1), PEqualNP.MetaComplexity.FanInTwo x2 → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = x2.size ∧ ∀ (x6 : Fin x1 → Bool) (x7 : List Bool), x5.eval (List.ofFn x6 ++ x7) = x2.eval (List.ofFn (x6 ∘ x3) ++ x7) := by
  intro x1 x2 x3
  intros
  refine ⟨PEqualNP.Outside.L_meta_7338_aux.sh_rel (fun i => x3 i) x2, ?_⟩
  repeat' apply And.intro
  all_goals first
    | exact PEqualNP.Outside.L_meta_7338_aux.sh_relabel_size _ _ _ _
    | exact PEqualNP.Outside.L_meta_7338_aux.sh_relabel_fanInTwo _ _ _ _ ‹_›
    | exact PEqualNP.Outside.L_meta_7338_aux.sh_relabel_monotone2 _ _ _ _ ‹_›
    | (intros; first | exact PEqualNP.Outside.L_meta_7338_aux.sh_relabel_eval_app _ _ _ _ | exact PEqualNP.Outside.L_meta_7338_aux.sh_relabel_eval_nil _ _ _ | simpa using PEqualNP.Outside.L_meta_7338_aux.sh_relabel_eval_app _ _ _ _ | simpa [Function.comp] using PEqualNP.Outside.L_meta_7338_aux.sh_relabel_eval_nil _ _ _)
    | (intros; simp only [PEqualNP.MetaComplexity.circuitFun]; first | exact PEqualNP.Outside.L_meta_7338_aux.sh_relabel_eval_app _ _ _ _ | exact PEqualNP.Outside.L_meta_7338_aux.sh_relabel_eval_nil _ _ _ | simpa using PEqualNP.Outside.L_meta_7338_aux.sh_relabel_eval_app _ _ _ _ | simpa [Function.comp] using PEqualNP.Outside.L_meta_7338_aux.sh_relabel_eval_nil _ _ _)
