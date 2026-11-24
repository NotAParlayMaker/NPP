import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3358

open PEqualNP.CircuitLowerBounds

-- A gate that is not a NOT gate. Such a gate reads at most two wires; a NOT gate reads one.
def isBin (g : Gate) : Bool :=
  match g.op with
  | .not => false
  | _ => true

-- The wires whose values the gate depends on.
def reads (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma gate_dep (g : Gate) (w w' : List Bool)
    (h : ∀ i ∈ reads g, w.getD i false = w'.getD i false) :
    g.op.eval (g.inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w'.getD i false) := by
  obtain ⟨op, inputs⟩ := g
  cases op with
  | not =>
    cases inputs with
    | nil => rfl
    | cons a l =>
      have ha := h a (by simp [reads])
      simpa [GateOp.eval, List.getD_eq_getElem?_getD] using ha
  | and =>
    have hm : (inputs.map fun i => w.getD i false) = (inputs.map fun i => w'.getD i false) :=
      List.map_congr_left (fun i hi => h i (by simpa [reads] using hi))
    simp only [hm]
  | or =>
    have hm : (inputs.map fun i => w.getD i false) = (inputs.map fun i => w'.getD i false) :=
      List.map_congr_left (fun i hi => h i (by simpa [reads] using hi))
    simp only [hm]
  | mod m =>
    have hm : (inputs.map fun i => w.getD i false) = (inputs.map fun i => w'.getD i false) :=
      List.map_congr_left (fun i hi => h i (by simpa [reads] using hi))
    simp only [hm]
  | maj =>
    have hm : (inputs.map fun i => w.getD i false) = (inputs.map fun i => w'.getD i false) :=
      List.map_congr_left (fun i hi => h i (by simpa [reads] using hi))
    simp only [hm]

lemma reads_len (g : Gate) (hl : g.inputs.length ≤ 2) :
    (reads g).length ≤ 1 + (if isBin g = true then 1 else 0) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp [reads, isBin] <;> omega

-- Read backwards from a set of wires: every non-NOT gate adds at most one wire to the set
-- of wires the values depend on, a NOT gate adds none.
lemma dep (gs : List Gate) (hl : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ (n : ℕ) (R : Finset ℕ), ∃ R' : Finset ℕ, R' ⊆ Finset.range n ∧
      R'.card ≤ R.card + gs.countP isBin ∧
      ∀ w w' : List Bool, w.length = n → w'.length = n →
        (∀ i ∈ R', w.getD i false = w'.getD i false) →
        ∀ i ∈ R, (gs.foldl step w).getD i false = (gs.foldl step w').getD i false := by
  induction gs with
  | nil =>
    intro n R
    refine ⟨R.filter (· < n), ?_, ?_, ?_⟩
    · intro i hi
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
    · simpa using Finset.card_filter_le R (· < n)
    · intro w w' hw hw' h i hi
      simp only [List.foldl_nil]
      by_cases hin : i < n
      · exact h i (Finset.mem_filter.mpr ⟨hi, hin⟩)
      · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | cons g gs ih =>
    intro n R
    obtain ⟨R1, hsub1, hcard1, hdep1⟩ :=
      ih (fun g' hg' => hl g' (List.mem_cons_of_mem _ hg')) (n + 1) R
    have hcount : (g :: gs).countP isBin = gs.countP isBin + (if isBin g = true then 1 else 0) :=
      List.countP_cons
    have hlt : ∀ j ∈ R1, j ≠ n → j < n := by
      intro j hj hne
      have := Finset.mem_range.mp (hsub1 hj)
      omega
    by_cases hn : n ∈ R1
    · refine ⟨R1.erase n ∪ (reads g).toFinset.filter (· < n), ?_, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_union.mp hi with hi | hi
        · obtain ⟨hne, hi⟩ := Finset.mem_erase.mp hi
          exact Finset.mem_range.mpr (hlt i hi hne)
        · exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
      · have h1 : (R1.erase n).card + 1 = R1.card := Finset.card_erase_add_one hn
        have h2 : ((reads g).toFinset.filter (· < n)).card ≤ (reads g).length :=
          (Finset.card_filter_le _ _).trans (List.toFinset_card_le _)
        have h3 := reads_len g (hl g List.mem_cons_self)
        have h4 := Finset.card_union_le (R1.erase n) ((reads g).toFinset.filter (· < n))
        omega
      · intro w w' hw hw' h i hi
        have hv : g.op.eval (g.inputs.map fun i => w.getD i false) =
            g.op.eval (g.inputs.map fun i => w'.getD i false) := by
          apply gate_dep
          intro j hj
          by_cases hjn : j < n
          · exact h j (Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hj, hjn⟩))
          · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        refine hdep1 (step w g) (step w' g) (by simp [step, hw]) (by simp [step, hw']) ?_ i hi
        intro j hj
        by_cases hjn : j = n
        · subst hjn
          simp only [step]
          rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega),
            hw, hw', Nat.sub_self, List.getD_cons_zero, List.getD_cons_zero]
          exact hv
        · have hj' := hlt j hj hjn
          simp only [step]
          rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
          exact h j (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hjn, hj⟩))
    · refine ⟨R1, ?_, ?_, ?_⟩
      · intro i hi
        exact Finset.mem_range.mpr (hlt i hi (fun e => hn (e ▸ hi)))
      · omega
      · intro w w' hw hw' h i hi
        refine hdep1 (step w g) (step w' g) (by simp [step, hw]) (by simp [step, hw']) ?_ i hi
        intro j hj
        have hj' := hlt j hj (fun e => hn (e ▸ hj))
        simp only [step]
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact h j hj

lemma one_not (l : List Gate) (j : ℕ) (hj : j < l.length) (h : isBin l[j] = false) :
    l.countP isBin + 1 ≤ l.length := by
  have hle := List.countP_le_length (p := isBin) (l := l)
  have hne : l.countP isBin ≠ l.length := by
    intro he
    have := (List.countP_eq_length.mp he) l[j] (List.getElem_mem hj)
    rw [h] at this
    exact Bool.false_ne_true this
  omega

lemma two_nots (l : List Gate) : ∀ (i j : ℕ) (hij : i < j) (hj : j < l.length),
    isBin (l[i]'(by omega)) = false → isBin l[j] = false → l.countP isBin + 2 ≤ l.length := by
  induction l with
  | nil => intro i j hij hj; simp at hj
  | cons a t ih =>
    intro i j hij hj hi' hj'
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hjt : j' < t.length := by simpa using hj
    have hj2 : isBin t[j'] = false := by simpa using hj'
    cases i with
    | zero =>
      have ha : isBin a = false := by simpa using hi'
      have h1 := one_not t j' hjt hj2
      have hc : (a :: t).countP isBin = t.countP isBin := by simp [ha]
      have hlen : (a :: t).length = t.length + 1 := rfl
      omega
    | succ i' =>
      have hi2 : isBin (t[i']'(by omega)) = false := by simpa using hi'
      have h1 := ih i' j' (by omega) hjt hi2 hj2
      have hc : (a :: t).countP isBin ≤ t.countP isBin + 1 := by
        rw [List.countP_cons]
        split <;> omega
      have hlen : (a :: t).length = t.length + 1 := rfl
      omega

lemma main (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C) (hs : C.size ≤ 7)
    (a b : Fin C.gates.length) (hab : a < b)
    (ha : (C.gates.get a).op = GateOp.not) (hb : (C.gates.get b).op = GateOp.not) :
    ∃ S ⊆ Finset.range 17, S.card ≤ 6 ∧ ∀ (w w' : List Bool), w.length = 17 → w'.length = 17 →
      (∀ i ∈ S, w.getD i false = w'.getD i false) → C.eval w = C.eval w' := by
  obtain ⟨R', hsub, hcard, hdep⟩ := dep C.gates (fun g hg => (hf g hg).2) 17 {C.output}
  have hnots := two_nots C.gates a.val b.val hab b.isLt
    (by have h : C.gates[a.val].op = GateOp.not := ha
        unfold isBin; rw [h])
    (by have h : C.gates[b.val].op = GateOp.not := hb
        unfold isBin; rw [h])
  have hsz : C.gates.length ≤ 7 := hs
  refine ⟨R', hsub, ?_, ?_⟩
  · rw [Finset.card_singleton] at hcard
    omega
  · intro w w' hw hw' h
    exact hdep w w' hw hw' h C.output (Finset.mem_singleton_self _)

end PEqualNP.Outside.L_meta_3358

theorem PEqualNP.Outside.L_meta_3358 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (7 : ℕ) → ∀ (x4 x5 : Fin x1.gates.length), x4 < x5 → (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ x9 ⊆ Finset.range (17 : ℕ), x9.card ≤ (6 : ℕ) ∧ ∀ (x10 x11 : List Bool), x10.length = (17 : ℕ) → x11.length = (17 : ℕ) → (∀ x14 ∈ x9, x10.getD x14 Bool.false = x11.getD x14 Bool.false) → x1.eval x10 = x1.eval x11 :=
  fun C hf hs a b hab ha hb => PEqualNP.Outside.L_meta_3358.main C hf hs a b hab ha hb
