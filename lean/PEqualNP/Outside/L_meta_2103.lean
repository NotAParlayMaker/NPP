import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_2103_aux

private def value (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map (fun i => w.getD i false))

private def run (gs : List Gate) (w : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires w

private theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [value g w]) := rfl

private theorem run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, Circuit.wires, List.foldl_append]

private theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run, Circuit.wires]
  | cons g gs ih =>
    rw [run_cons, ih]
    simp <;> omega

private theorem run_preserves (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) : (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

private def rename (f : ℕ → ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map f⟩

private theorem rename_mono (f : ℕ → ℕ) (gs : List Gate)
    (h : Monotone2 ⟨gs, 0⟩) : Monotone2 ⟨gs.map (rename f), 0⟩ := by
  intro a ha
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp ha
  exact ⟨(h g hg).1, by simpa [rename] using (h g hg).2⟩

private theorem run_rename (f : ℕ → ℕ) (gs : List Gate) (w v : List Bool)
    (hprefix : ∀ i < w.length, f i < v.length)
    (hsuffix : ∀ i, w.length ≤ i → f i = v.length + (i - w.length))
    (hval : ∀ i, w.getD i false = v.getD (f i) false) :
    ∀ i, (run gs w).getD i false = (run (gs.map (rename f)) v).getD (f i) false := by
  induction gs generalizing w v with
  | nil => exact hval
  | cons g gs ih =>
    have hg : value (rename f g) v = value g w := by
      simp only [value, rename, List.map_map, Function.comp_apply]
      congr 1
      apply List.map_congr_left
      intro i _
      exact (hval i).symm
    simp only [List.map_cons, run_cons, hg]
    have hw : (w ++ [value g w]).length = w.length + 1 := by simp
    have hv : (v ++ [value g w]).length = v.length + 1 := by simp
    apply ih
    · intro i hi
      rw [hw] at hi
      rw [hv]
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | rfl
      · exact (hprefix i hlt).trans (Nat.lt_succ_self _)
      · rw [hsuffix _ le_rfl, Nat.sub_self, Nat.add_zero]
        omega
    · intro i hi
      rw [hw] at hi
      rw [hw, hv, hsuffix i (by omega)]
      omega
    · intro i
      by_cases hi : i < w.length
      · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hprefix i hi)]
        exact hval i
      · rcases eq_or_lt_of_le (Nat.le_of_not_lt hi) with rfl | hi'
        · rw [hsuffix _ le_rfl, Nat.sub_self, Nat.add_zero]
          simp
        · rw [List.getD_eq_default _ _ (by omega),
            List.getD_eq_default _ _ (by rw [hsuffix _ (by omega)]; omega)]

private def reindex {n m : ℕ} (f : Fin n → Fin m) (k : ℕ) (i : ℕ) : ℕ :=
  if h : i < n then (f ⟨i,h⟩).val else k + (i - n)

private theorem get_input {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

private theorem reindex_run {n m : ℕ} (f : Fin n → Fin m) (x : Fin m → Bool)
    (gs : List Gate) (v : List Bool) (hv : m ≤ v.length)
    (hval : ∀ i : Fin m, v.getD i.val false = x i) :
    ∀ i, (run gs (List.ofFn (fun j => x (f j)))).getD i false =
      (run (gs.map (rename (reindex f v.length))) v).getD (reindex f v.length i) false := by
  apply run_rename
  · intro i hi
    have h : i < n := by simpa using hi
    rw [reindex, dif_pos h]
    exact (f ⟨i,h⟩).isLt.trans_le hv
  · intro i hi
    have h : n ≤ i := by simpa using hi
    rw [List.length_ofFn, reindex, dif_neg (Nat.not_lt.mpr h)]
  · intro i
    by_cases hi : i < n
    · rw [reindex, dif_pos hi, hval]
      exact get_input _ ⟨i,hi⟩
    · rw [reindex, dif_neg hi, List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hi)]
      exact (List.getD_eq_default _ _ (by omega)).symm

private theorem or_combine {n m : ℕ} (f : Fin n → Fin m) (A B : Circuit)
    (ha : Monotone2 A) (hb : Monotone2 B) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ A.size + B.size + 1 ∧
      ∀ x : Fin m → Bool, circuitFun m D x =
        (circuitFun n A (fun i => x (f i)) || circuitFun m B x) := by
  let fa := reindex f m
  let ga := A.gates.map (rename fa)
  let k := m + A.gates.length
  let fb := reindex (id : Fin m → Fin m) k
  let gb := B.gates.map (rename fb)
  let top := k + B.gates.length
  let oa := if A.output < n + A.gates.length then fa A.output else top
  let ob := fb B.output
  let last : Gate := ⟨.or, [oa,ob]⟩
  refine ⟨⟨(ga ++ gb) ++ [last], top⟩, ?_, ?_, ?_⟩
  · have hga := rename_mono fa A.gates ha
    have hgb := rename_mono fb B.gates hb
    intro g hg
    change g ∈ (ga ++ gb) ++ [last] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact (List.mem_append.mp hg).elim (hga g) (hgb g)
    · have he : g = last := by simpa using hg
      subst g
      simp [last]
  · simp [Circuit.size, ga, gb, Nat.add_assoc]
  · intro x
    let base := List.ofFn x
    let wa := run ga base
    let wb := run gb wa
    have hbase : base.length = m := List.length_ofFn
    have hwa : wa.length = k := by simp [wa, run_length, hbase, ga, k]
    have hwb : wb.length = top := by simp [wb, run_length, hwa, gb, top]
    have hread (i : Fin m) : wa.getD i.val false = x i := by
      rw [show wa = run ga base from rfl, run_preserves _ _ _ (by simpa [hbase] using i.isLt)]
      exact get_input x i
    have hea := reindex_run f x A.gates base (by omega) (get_input x) A.output
    rw [hbase] at hea
    have heb := reindex_run (id : Fin m → Fin m) x B.gates wa
      (by rw [hwa]; dsimp [k]; omega) hread B.output
    rw [hwa] at heb
    have hao : wb.getD oa false = A.eval (List.ofFn (fun i => x (f i))) := by
      by_cases ho : A.output < n + A.gates.length
      · simp only [oa, ho, ↓reduceIte]
        have hf : fa A.output < wa.length := by
          rw [hwa]
          change reindex f m A.output < k
          by_cases h : A.output < n
          · rw [reindex, dif_pos h]
            exact (f ⟨_, h⟩).isLt.trans_le (by dsimp [k]; omega)
          · rw [reindex, dif_neg h]
            dsimp [k]
            omega
        change (run gb wa).getD (fa A.output) false = _
        rw [run_preserves _ _ _ hf]
        exact hea.symm
      · simp only [oa, ho, ↓reduceIte]
        change wb.getD top false = (run A.gates (List.ofFn (fun i => x (f i)))).getD A.output false
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by rw [run_length]; simpa using Nat.le_of_not_lt ho)]
    have hbo : wb.getD ob false = B.eval (List.ofFn x) := heb.symm
    change (run ((ga ++ gb) ++ [last]) base).getD top false = _
    rw [run_append, run_append]
    change (run [last] wb).getD top false = _
    rw [run_cons]
    change (wb ++ [value last wb]).getD top false = _
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hwb, value, last, GateOp.eval, circuitFun, hao, hbo, -List.getD_eq_getElem?_getD]
    rfl

end PEqualNP.Outside.L_meta_2103_aux

theorem PEqualNP.Outside.L_meta_2103 :
    ∀ (n m : ℕ) (f : Fin n → Fin m) (A B : Circuit),
      Monotone2 A → ReadsBack n A → Monotone2 B → ReadsBack m B →
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ A.size + B.size + 1 ∧
        ∀ x : Fin m → Bool, circuitFun m D x =
          (circuitFun n A (fun i => x (f i)) || circuitFun m B x) := by
  intro n m f A B ha _ hb _
  exact L_meta_2103_aux.or_combine f A B ha hb
