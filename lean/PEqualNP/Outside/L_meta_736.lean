import Mathlib.Data.List.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_736

open PEqualNP.CircuitLowerBounds

private def extend (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def reindex (phi : ℕ → ℕ) (g : Gate) : Gate :=
  { op := g.op, inputs := g.inputs.map phi }

private lemma getD_snoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  by_cases lt : i < w.length
  · simp [List.getD, List.getElem?_append_left lt, Nat.ne_of_lt lt]
  · rw [List.getD, List.getElem?_append_right (by omega)]
    by_cases eq : i = w.length
    · simp [eq]
    · have a : w.length ≤ i := by omega
      have b : [b].length ≤ i - w.length := by simp; omega
      simp [eq, List.getD, List.getElem?_eq_none a, List.getElem?_eq_none b]

private lemma fold_preserves (phi : ℕ → ℕ) (n n' m : ℕ)
    (pin : ∀ t : ℕ, t < m → ∀ i : ℕ, phi i = n' + t ↔ i = n + t)
    (gs : List Gate) (t : ℕ) (w w' : List Bool)
    (ht : t + gs.length ≤ m) (hw : w.length = n + t) (hw' : w'.length = n' + t)
    (same : ∀ i, w'.getD (phi i) false = w.getD i false) :
    ∀ i, ((gs.map (reindex phi)).foldl extend w').getD (phi i) false =
      (gs.foldl extend w).getD i false := by
  induction gs generalizing t w w' with
  | nil => exact same
  | cons g rest ih =>
    have htm : t < m := by simp at ht; omega
    have hin :
        (g.inputs.map phi).map (fun j => w'.getD j false) =
          g.inputs.map (fun j => w.getD j false) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => same i)
    apply ih (t + 1) (extend w g) (extend w' (reindex phi g))
    · simp at ht
      omega
    · simp [extend, hw]; omega
    · simp [extend, hw']; omega
    · intro i
      simp only [extend, reindex, getD_snoc, hw, hw', hin, pin t htm i, same i]

end PEqualNP.Outside.L_meta_736

theorem PEqualNP.Outside.L_meta_736 : ∀ (n n' : ℕ) (O : Finset (Fin n)) (e : Fin n' → Fin n), StrictMono e →
  (∀ k : Fin n, k ∉ O ↔ ∃ j : Fin n', e j = k) → n' + O.card = n →
  ∀ gates : List PEqualNP.CircuitLowerBounds.Gate,
  ∃ psi : ℕ → ℕ, ∀ x x' : List Bool, x.length = n → x'.length = n' →
    (∀ k ∈ O, x.getD (k : ℕ) false = true) →
    (∀ j : Fin n', x.getD (e j : ℕ) false = x'.getD (j : ℕ) false) →
    (∀ i : ℕ, (PEqualNP.CircuitLowerBounds.Circuit.wires
        { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } ::
            gates.map (fun g => { op := g.op, inputs := g.inputs.map psi }), output := 0 } x').getD (psi i) false
      = (PEqualNP.CircuitLowerBounds.Circuit.wires { gates := gates, output := 0 } x).getD i false) ∧
    (∀ o : ℕ, PEqualNP.CircuitLowerBounds.Circuit.eval
        { gates := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } ::
            gates.map (fun g => { op := g.op, inputs := g.inputs.map psi }), output := psi o } x'
      = PEqualNP.CircuitLowerBounds.Circuit.eval { gates := gates, output := o } x) := by
  classical
  open PEqualNP.Outside.L_meta_736 in
  open PEqualNP.CircuitLowerBounds in
  intro n n' O e _ image _ gates
  let onInput (i : ℕ) := ∃ j : Fin n', (e j).val = i
  let psi (i : ℕ) : ℕ :=
    if h : onInput i then h.choose.val
    else if i < n then n' else (n' + 1) + (i - n)
  have pin (t : ℕ) (_ : t < gates.length) (i : ℕ) :
      psi i = (n' + 1) + t ↔ i = n + t := by
    unfold psi
    split
    next he =>
      have hj := he.choose.isLt
      have hi : i < n := he.choose_spec ▸ (e he.choose).isLt
      omega
    next _ => split <;> omega
  refine ⟨psi, ?_⟩
  intro x x' hx hx' hO he
  have base (i : ℕ) : (x' ++ [true]).getD (psi i) false = x.getD i false := by
    rw [getD_snoc, hx']
    by_cases himage : onInput i
    · rw [show psi i = himage.choose.val by exact dite_eq_left himage,
          if_neg (Nat.ne_of_lt himage.choose.isLt)]
      simpa only [himage.choose_spec] using (he himage.choose).symm
    · by_cases hi : i < n
      · have fixed : (⟨i, hi⟩ : Fin n) ∈ O := by
          by_contra hn
          obtain ⟨j, hj⟩ := (image ⟨i, hi⟩).mp hn
          exact himage ⟨j, congrArg Fin.val hj⟩
        simpa [psi, himage, hi] using (hO ⟨i, hi⟩ fixed).symm
      · have hpsi : n' < psi i := by
          simp only [psi, dif_neg himage, if_neg hi]
          omega
        rw [if_neg (Ne.symm (Nat.ne_of_lt hpsi))]
        simp [List.getD, List.getElem?_eq_none (show x'.length ≤ psi i by omega),
          List.getElem?_eq_none (show x.length ≤ i by omega)]
  have output := fold_preserves psi n (n' + 1) gates.length pin gates 0 x (x' ++ [true])
    (by simp) (by simpa using hx) (by simp [hx']) base
  exact ⟨output, output⟩
