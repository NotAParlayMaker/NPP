import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18193

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem and_mono (a a' b b' : Bool) (h1 : a ≤ a') (h2 : b ≤ b') : (a && b) ≤ (a' && b') := by
  revert h1 h2
  cases a <;> cases a' <;> cases b <;> cases b' <;> decide

theorem or_mono (a a' b b' : Bool) (h1 : a ≤ a') (h2 : b ≤ b') : (a || b) ≤ (a' || b') := by
  revert h1 h2
  cases a <;> cases a' <;> cases b <;> cases b' <;> decide

theorem all_mono (l : List ℕ) (f f' : ℕ → Bool) (h : ∀ i, f i ≤ f' i) :
    (l.map f).all id ≤ (l.map f').all id := by
  induction l with
  | nil => exact le_refl _
  | cons a l ih =>
    simp only [List.map_cons, List.all_cons, id]
    exact and_mono _ _ _ _ (h a) ih

theorem any_mono (l : List ℕ) (f f' : ℕ → Bool) (h : ∀ i, f i ≤ f' i) :
    (l.map f).any id ≤ (l.map f').any id := by
  induction l with
  | nil => exact le_refl _
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, id]
    exact or_mono _ _ _ _ (h a) ih

theorem getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i < W.length then W.getD i false else if i = W.length then v else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    simp
  · rw [List.getD_eq_default]
    simp
    omega

def R (W W' : List Bool) : Prop :=
  W.length = W'.length ∧ ∀ i, W.getD i false ≤ W'.getD i false

theorem step_R (W W' : List Bool) (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : R W W') : R (step W g) (step W' g) := by
  obtain ⟨hl, hle⟩ := h
  have hv : g.op.eval (g.inputs.map fun i => W.getD i false) ≤
      g.op.eval (g.inputs.map fun i => W'.getD i false) := by
    rcases hg with hg | hg <;> rw [hg] <;> simp only [GateOp.eval]
    · exact all_mono _ _ _ hle
    · exact any_mono _ _ _ hle
  refine ⟨by simp [step, hl], fun i => ?_⟩
  simp only [step, getD_snoc, hl]
  split_ifs
  · exact hle i
  · exact hv
  · exact le_refl _

theorem fold_R (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ W W' : List Bool, R W W' → R (gs.foldl step W) (gs.foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _
      (step_R W W' g (hgs g List.mem_cons_self) h)

theorem R_append {l1 l1' l2 l2' : List Bool} (h1 : R l1 l1') (h2 : R l2 l2') :
    R (l1 ++ l2) (l1' ++ l2') := by
  obtain ⟨hl1, h1⟩ := h1
  obtain ⟨hl2, h2⟩ := h2
  refine ⟨by simp [hl1, hl2], fun i => ?_⟩
  by_cases hi : i < l1.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hl1 ▸ hi)]
    exact h1 i
  · have hi' : l1.length ≤ i := by omega
    rw [List.getD_append_right _ _ _ _ hi', List.getD_append_right _ _ _ _ (hl1 ▸ hi'), hl1]
    exact h2 _

theorem R_ofFn {n : ℕ} (f g : Fin n → Bool) (h : ∀ i, f i ≤ g i) :
    R (List.ofFn f) (List.ofFn g) := by
  refine ⟨by simp, fun i => ?_⟩
  by_cases hi : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_ofFn]
    exact h ⟨i, hi⟩
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem eval_mono (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C) (l l' : List Bool)
    (h : R l l') : C.eval l ≤ C.eval l' := by
  have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hm g hg).1
    simpa using this
  show (C.wires l).getD C.output false ≤ (C.wires l').getD C.output false
  rw [wires_eq, wires_eq]
  exact (fold_R C.gates hops _ _ h).2 C.output

def mergeIndex (n i : ℕ) : ℕ :=
  if i < n then i else i - n

def mergeGate (n : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (mergeIndex n)⟩

def mergeCircuit (n : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (mergeGate n), mergeIndex n C.output⟩

def Related (n : ℕ) (full short : List Bool) : Prop :=
  n ≤ short.length ∧ full.length = n + short.length ∧
    ∀ i, full.getD i false = short.getD (mergeIndex n i) false

theorem initial {n : ℕ} (x : List Bool) (hx : x.length = n) :
    Related n (x ++ x) x := by
  refine ⟨by omega, by simp [hx], fun i => ?_⟩
  by_cases hi : i < n
  · rw [List.getD_append _ _ _ _ (by omega), mergeIndex, ite_eq_left hi]
  · rw [List.getD_append_right _ _ _ _ (by omega), mergeIndex, ite_eq_right hi, hx]

theorem relatedStep {n : ℕ} {full short : List Bool} (h : Related n full short) (g : Gate) :
    Related n (step full g) (step short (mergeGate n g)) := by
  obtain ⟨hn, hlen, hval⟩ := h
  have hvalues : (g.inputs.map fun i => full.getD i false) =
      (mergeGate n g).inputs.map (fun i => short.getD i false) := by
    simp only [mergeGate, List.map_map, Function.comp_def, hval]
  refine ⟨by simp [step]; omega, by simp [step, hlen]; omega, fun i => ?_⟩
  have lt : mergeIndex n i < short.length ↔ i < full.length := by
    unfold mergeIndex
    split <;> omega
  have eq : mergeIndex n i = short.length ↔ i = full.length := by
    unfold mergeIndex
    split <;> omega
  simp only [step, getD_snoc, lt, eq, hvalues]
  by_cases hi : i < full.length
  · simp only [ite_eq_left hi, hval]
  · simp only [ite_eq_right hi, mergeGate]

theorem relatedFold (n : ℕ) (gs : List Gate) (full short : List Bool)
    (h : Related n full short) :
    Related n (gs.foldl step full) ((gs.map (mergeGate n)).foldl step short) := by
  induction gs generalizing full short with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    exact ih _ _ (relatedStep h g)

theorem mergeEval {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    (mergeCircuit n C).eval (List.ofFn x) = C.eval (List.ofFn x ++ List.ofFn x) := by
  let w := List.ofFn x
  exact ((relatedFold n C.gates (w ++ w) w (initial w (by simp [w]))).2.2 C.output).symm

theorem mergeMonotone (n : ℕ) (C : Circuit) (h : Monotone2 C) :
    Monotone2 (mergeCircuit n C) := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  simpa [mergeGate] using h a ha

theorem supportCount {n : ℕ} (x : Fin n → Bool) :
    (List.ofFn x).count true = (Finset.univ.filter fun i => x i = true).card := by
  rw [List.ofFn_eq_map, List.count, List.countP_map, List.countP_eq_length_filter]
  let l := (List.finRange n).filter (fun i => x i == true)
  have hl : l.Nodup := (List.nodup_finRange n).filter _
  change l.length = _
  rw [← List.toFinset_card_of_nodup hl]
  congr 1
  ext i
  simp [l]

theorem crownEval {n : ℕ} (hn : 0 < n) (C : Circuit) (hC : Monotone2 C)
    (hRep : Represents (fun u v : Fin n => decide (u ≠ v)) C)
    (x : Fin n → Bool) :
    C.eval (List.ofFn x ++ List.ofFn x) = decide (2 ≤ (List.ofFn x).count true) := by
  let T := Finset.univ.filter fun i : Fin n => x i = true
  have hT (i : Fin n) : i ∈ T ↔ x i = true := by simp [T]
  rw [supportCount]
  change C.eval (List.ofFn x ++ List.ofFn x) = decide (2 ≤ T.card)
  by_cases many : 2 ≤ T.card
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < T.card)
    have below (a : Fin n) (ha : a ∈ T) (i : Fin n) : decide (i = a) ≤ x i := by
      by_cases e : i = a
      · subst i
        simp [(hT a).mp ha]
      · simp [e]
    have hmon := eval_mono C hC _ _ (R_append (R_ofFn _ _ (below a ha)) (R_ofFn _ _ (below b hb)))
    change C.eval (oneEach a b) ≤ _ at hmon
    rw [hRep a b] at hmon
    have ordered : true ≤ C.eval (List.ofFn x ++ List.ofFn x) := by simpa [hab] using hmon
    have value : C.eval (List.ofFn x ++ List.ofFn x) = true := by
      cases e : C.eval (List.ofFn x ++ List.ofFn x)
      · exact False.elim ((by decide : ¬ true ≤ false) (e ▸ ordered))
      · rfl
    simp [many, value]
  · have hex : ∃ a : Fin n, ∀ i ∈ T, i = a := by
      by_cases hne : T.Nonempty
      · obtain ⟨a, ha⟩ := hne
        refine ⟨a, fun i hi => ?_⟩
        by_contra h
        have hc := Finset.one_lt_card.mpr ⟨i, hi, a, ha, h⟩
        omega
      · refine ⟨⟨0, hn⟩, fun i hi => ?_⟩
        exact False.elim (hne ⟨i, hi⟩)
    obtain ⟨a, ha⟩ := hex
    have above (i : Fin n) : x i ≤ decide (i = a) := by
      cases h : x i
      · simp
      · simp [ha i ((hT i).mpr h)]
    have hmon := eval_mono C hC _ _ (R_append (R_ofFn _ _ above) (R_ofFn _ _ above))
    change _ ≤ C.eval (oneEach a a) at hmon
    rw [hRep a a] at hmon
    have ordered : C.eval (List.ofFn x ++ List.ofFn x) ≤ false := by simpa using hmon
    have value : C.eval (List.ofFn x ++ List.ofFn x) = false := by
      cases e : C.eval (List.ofFn x ++ List.ofFn x)
      · rfl
      · exact False.elim ((by decide : ¬ true ≤ false) (e ▸ ordered))
    simp [many, value]

end PEqualNP.Outside.L_meta_18193

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_18193 in
theorem PEqualNP.Outside.L_meta_18193 : (∀ n s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (2 ≤ (List.ofFn x).count true)) := by
  intro n s h
  by_cases hn : n = 0
  · subst n
    refine ⟨⟨[], 0⟩, ?_, ?_, ?_⟩
    · simp [Monotone2]
    · simp [Circuit.size]
    · intro x
      simp [Circuit.eval, Circuit.wires]
  · obtain ⟨C, hm, hs, hrep⟩ := h
    refine ⟨mergeCircuit n C, mergeMonotone n C hm, ?_, fun x => ?_⟩
    · simpa [Circuit.size, mergeCircuit] using hs
    · rw [mergeEval]
      exact crownEval (by omega) C hm hrep x
