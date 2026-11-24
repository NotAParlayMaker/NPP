import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_4871

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_fold (C : Circuit) (x : List Bool) : C.wires x = List.foldl stp x C.gates := rfl

lemma stp_len (w : List Bool) (g : Gate) : (stp w g).length = w.length + 1 := by
  simp only [stp, List.length_append, List.length_singleton]

lemma getD_snoc_lt {L : List Bool} {a : Bool} {i : ℕ} (h : i < L.length) :
    (L ++ [a]).getD i false = L.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_len {L : List Bool} {a : Bool} : (L ++ [a]).getD L.length false = a := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl L.length)]
  simp

lemma getD_snoc_gt {L : List Bool} {a : Bool} {i : ℕ} (h : L.length < i) :
    (L ++ [a]).getD i false = false := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega : L.length ≤ i)]
  simp [show i - L.length ≠ 0 by omega]

lemma ble_iff (a b : Bool) : (a ≤ b) ↔ (a = true → b = true) := by
  revert a b
  decide

lemma true_le (b : Bool) : (true ≤ b) ↔ b = true := by
  revert b
  decide

lemma gate_mono {X Y : List Bool} (hXY : ∀ i, X.getD i false ≤ Y.getD i false) {g : Gate}
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or) :
    g.op.eval (g.inputs.map fun i => X.getD i false) ≤
      g.op.eval (g.inputs.map fun i => Y.getD i false) := by
  rw [ble_iff]
  intro hval
  rcases hg with hg | hg
  · rw [hg] at hval ⊢
    simp only [GateOp.eval] at hval ⊢
    rw [List.all_eq_true] at hval ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    have h1 : X.getD i false = true :=
      hval _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
    have h2 := hXY i
    rw [h1] at h2
    exact (true_le _).mp h2
  · rw [hg] at hval ⊢
    simp only [GateOp.eval] at hval ⊢
    rw [List.any_eq_true] at hval ⊢
    obtain ⟨b, hb, hbt⟩ := hval
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    refine ⟨Y.getD i false, List.mem_map.mpr ⟨i, hi, rfl⟩, ?_⟩
    have h1 : X.getD i false = true := hbt
    have h2 := hXY i
    rw [h1] at h2
    exact (true_le _).mp h2

lemma fold_mono (gs : List Gate) (hAO : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (X Y : List Bool), X.length = Y.length → (∀ i, X.getD i false ≤ Y.getD i false) →
      ∀ i, (List.foldl stp X gs).getD i false ≤ (List.foldl stp Y gs).getD i false := by
  induction gs with
  | nil => intro X Y _ h i; exact h i
  | cons g gs ih =>
    intro X Y hlen h i
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hAO g' (by simp [hg']))
    · rw [stp_len, stp_len, hlen]
    · intro j
      by_cases hj : j < X.length
      · rw [stp, getD_snoc_lt hj, stp, getD_snoc_lt (by omega)]
        exact h j
      · by_cases hje : j = X.length
        · subst hje
          rw [stp, getD_snoc_len, stp, hlen, getD_snoc_len]
          exact gate_mono h (hAO g (by simp))
        · have hjlt : X.length < j := by omega
          rw [stp, getD_snoc_gt hjlt, stp, getD_snoc_gt (by omega)]

end PEqualNP.Outside.L_meta_4871

open PEqualNP.Outside.L_meta_4871 in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_4871 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → Monotone fun (x3 : Fin (14 : ℕ) → Bool) => x1.eval (List.ofFn x3) := by
  intro C hAO
  obtain ⟨honly, -, -⟩ := hAO
  intro x y hxy
  have hXY : ∀ i, (List.ofFn x).getD i false ≤ (List.ofFn y).getD i false := by
    intro i
    by_cases hi : i < 14
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi),
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi)]
      simp only [Option.getD_some, List.getElem_ofFn]
      exact hxy ⟨i, hi⟩
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      simp only [Option.getD_none]
      exact Bool.false_le _
  have hlen : (List.ofFn x).length = (List.ofFn y).length := by simp
  have := fold_mono C.gates honly (List.ofFn x) (List.ofFn y) hlen hXY C.output
  simpa only [Circuit.eval, wires_fold] using this
