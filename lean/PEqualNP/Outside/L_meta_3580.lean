import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3580

private def kept (g : Gate) : List ℕ :=
  g.inputs.take (bif g.op.eval [false] then 1 else 2)

private def Normal (C : Circuit) : Prop := ∀ g ∈ C.gates, kept g = g.inputs

private def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w =
      run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma run_len (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

private lemma normal_exists (C : Circuit) (h : FanInTwo C) :
    ∃ D : Circuit, D.size = C.size ∧ FanInTwo D ∧ Normal D ∧
      ∀ w : List Bool, D.eval w = C.eval w := by
  let f (g : Gate) : Gate := ⟨g.op, kept g⟩
  have he (g : Gate) (hg : g ∈ C.gates) (v : List Bool) :
      (f g).op.eval ((f g).inputs.map fun i => v.getD i false) =
        g.op.eval (g.inputs.map fun i => v.getD i false) := by
    obtain ⟨hop, hle⟩ := h g hg
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at hop
    rcases hop with hop | hop | hop
    · simp [f, kept, hop, GateOp.eval, List.take_of_length_le hle]
    · simp [f, kept, hop, GateOp.eval, List.take_of_length_le hle]
    · cases hI : g.inputs <;> simp [f, kept, hop, GateOp.eval, hI]
  refine ⟨⟨C.gates.map f, C.output⟩, List.length_map f, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hg
    have hb : (kept a).length ≤ a.inputs.length := by simp [kept, List.length_take]
    exact ⟨(h a ha).1, hb.trans (h a ha).2⟩
  · intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hg
    show (kept a).take (bif a.op.eval [false] then 1 else 2) = kept a
    apply List.take_of_length_le
    exact List.length_take_le _ _
  · intro w
    have hRun (gs : List Gate) (hmem : ∀ g ∈ gs, g ∈ C.gates) (x : List Bool) :
        run (gs.map f) x = run gs x := by
      induction gs generalizing x with
      | nil => rfl
      | cons g gs ih =>
        rw [List.map_cons, run_cons, run_cons, he g (hmem g List.mem_cons_self), ih]
        exact fun a ha => hmem a (List.mem_cons_of_mem _ ha)
    change (run (C.gates.map f) w).getD C.output false = (run C.gates w).getD C.output false
    rw [hRun C.gates (fun _ h => h)]

private def through (k w : ℕ) : ℕ := if k < w then w - 1 else w

-- Compare the wire arrays after skipping a gate whose value has no reader.
-- The index shift follows the checked wire renumbering in L-meta-1351.
private lemma skip_fold (k : ℕ) (gs : List Gate)
    (hunread : ∀ g ∈ gs, k ∉ g.inputs)
    (W S : List Bool) (hk : k ≤ S.length) (hlen : W.length = S.length + 1)
    (hall : ∀ w, w ≠ k → S.getD (through k w) false = W.getD w false) :
    ∀ w, w ≠ k →
      (run (gs.map fun g => ⟨g.op, g.inputs.map (through k)⟩) S).getD (through k w) false =
        (run gs W).getD w false := by
  induction gs generalizing W S with
  | nil => exact hall
  | cons g gs ih =>
    rw [List.map_cons, run_cons, run_cons]
    have hmaps : ((g.inputs.map (through k)).map fun i => S.getD i false) =
        (g.inputs.map fun i => W.getD i false) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i hi
      exact hall i (fun e => hunread g List.mem_cons_self (e ▸ hi))
    simp only [hmaps]
    apply ih (fun a ha => hunread a (List.mem_cons_of_mem _ ha)) _ _ (by simp; omega)
      (by simp; omega)
    intro w hw
    rcases Nat.lt_trichotomy w W.length with hlt | he | hgt
    · have hsm : through k w < S.length := by
        by_cases h : k < w
        · simp [through, h]; omega
        · simp [through, h]; omega
      rw [List.getD_append _ _ _ _ hsm, List.getD_append _ _ _ _ hlt]
      exact hall w hw
    · have hi : through k w = S.length := by simp [through, show k < w by omega]; omega
      rw [hi, he]
      simp
    · have hi : S.length + 1 ≤ through k w := by
        simp [through, show k < w by omega]
        omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma remove_unused (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.size)
    (hn : FanInTwo C) (hN : Normal C)
    (ho : C.output ≠ n + j) (hu : ∀ g ∈ C.gates, n + j ∉ g.inputs) :
    ∃ D : Circuit, D.size < C.size ∧ FanInTwo D ∧ Normal D ∧
      circuitFun n D = circuitFun n C := by
  let k := n + j
  let pre := C.gates.take j
  let post := C.gates.drop (j + 1)
  let g := C.gates[j]'(show j < C.gates.length from hj)
  let remap (a : Gate) : Gate := ⟨a.op, a.inputs.map (through k)⟩
  let D : Circuit := ⟨pre ++ post.map remap, through k C.output⟩
  have hsplit : C.gates = pre ++ g :: post := by
    rw [← List.drop_eq_getElem_cons (show j < C.gates.length from hj)]
    exact (List.take_append_drop j C.gates).symm
  have hp (a : Gate) (ha : a ∈ pre) : a ∈ C.gates :=
    List.mem_of_mem_take ha
  have hq (a : Gate) (ha : a ∈ post) : a ∈ C.gates :=
    List.mem_of_mem_drop ha
  have hn' : FanInTwo D := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hn a (hp a ha)
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
      exact ⟨(hn b (hq b hb)).1, by simpa [remap] using (hn b (hq b hb)).2⟩
  have hN' : Normal D := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hN a (hp a ha)
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
      change (b.inputs.map (through k)).take (bif b.op.eval [false] then 1 else 2) = _
      rw [← List.map_take]
      exact congrArg (List.map (through k)) (hN b (hq b hb))
  have hj' : j < C.gates.length := hj
  have hpre : pre.length = j := List.length_take_of_le hj'.le
  refine ⟨D, ?_, hn', hN', ?_⟩
  · change (pre ++ post.map remap).length < C.gates.length
    simp [hpre, post]
    omega
  · funext x
    let S := run pre (List.ofFn x)
    let b := g.op.eval (g.inputs.map fun i => S.getD i false)
    have hs : S.length = k := by
      simp [S, run_len, hpre, k]
    change (run (pre ++ post.map remap) (List.ofFn x)).getD (through k C.output) false =
      (run C.gates (List.ofFn x)).getD C.output false
    have hApp (gs ts : List Gate) (w : List Bool) : run (gs ++ ts) w = run ts (run gs w) := by
      simp [run, List.foldl_append]
    rw [hsplit, hApp, hApp, run_cons]
    change (run (post.map remap) S).getD (through k C.output) false =
      (run post (S ++ [b])).getD C.output false
    apply skip_fold k post (fun a ha => hu a (hq a ha)) _ _ (by omega) (by simp) _ C.output ho
    intro w hw
    by_cases h : w < k
    · rw [show through k w = w by simp [through, show ¬ k < w by omega],
        List.getD_append _ _ _ _ (by omega)]
    · have hlt : k < w := by omega
      have hb : S.length ≤ through k w := by simp [through, hlt]; omega
      rw [List.getD_eq_default _ _ hb, List.getD_eq_default _ _ (by simp; omega)]

private lemma input_irrelevant (gs : List Gate) (k : ℕ) (hu : ∀ g ∈ gs, k ∉ g.inputs)
    (W S : List Bool) (hlen : W.length = S.length) (hk : k < W.length)
    (he : ∀ w, w ≠ k → W.getD w false = S.getD w false) :
    ∀ w, w ≠ k → (run gs W).getD w false = (run gs S).getD w false := by
  induction gs generalizing W S with
  | nil => exact he
  | cons g gs ih =>
    rw [run_cons, run_cons]
    have eg : (g.inputs.map fun i => W.getD i false) =
        (g.inputs.map fun i => S.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact he i (fun e => hu g List.mem_cons_self (e ▸ hi))
    rw [eg]
    apply ih (fun a ha => hu a (List.mem_cons_of_mem _ ha)) _ _ (by simp [hlen]) (by simp; omega)
    intro w hw
    rcases Nat.lt_trichotomy w W.length with hlt | heq | hgt
    · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
      exact he w hw
    · have last (w' : List Bool) (b : Bool) (h : w = w'.length) :
          (w' ++ [b]).getD w false = b := by rw [h]; simp
      rw [last W _ heq, last S _ (by omega)]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma slot_budget (gs : List Gate) :
    (gs.filter (fun g => g.op.eval [false])).length + (gs.flatMap kept).length ≤
      2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    cases he : g.op.eval [false]
    · simp only [List.filter_cons, he, Bool.false_eq_true, ite_false, List.flatMap_cons,
        List.length_append, List.length_cons]
      have h : (kept g).length ≤ 2 := by simp [kept, he]
      omega
    · simp only [List.filter_cons, he, ite_true, List.flatMap_cons,
        List.length_append, List.length_cons]
      have h : (kept g).length ≤ 1 := by simp [kept, he]
      omega

end PEqualNP.Outside.L_meta_3580


open PEqualNP.Outside.L_meta_3580 in
theorem PEqualNP.Outside.L_meta_3580 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   (2 : ℕ) ≤ x1 →     PEqualNP.MetaComplexity.FanInTwo x2 →       (∀ (x5 : Fin x1), ∃ (x6 : Fin x1 → Bool) (x7 : Fin x1 → Bool), (∀ (x8 : Fin x1), x8 ≠ x5 → x6 x8 = x7 x8) ∧ PEqualNP.MetaComplexity.circuitFun x1 x2 x6 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x7) →         ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit),           x6.size ≤ x2.size ∧             PEqualNP.MetaComplexity.FanInTwo x6 ∧               PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.circuitFun x1 x2 ∧                 have x7 : List ℕ := List.flatMap (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => List.take (bif x7.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x7.inputs) x6.gates;                 (∀ x8 < x1 + x6.size, x8 ≠ x6.output → x8 ∈ x7) ∧ (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.op.eval [Bool.false]) x6.gates).length + (x7.length - x7.toFinset.card) ≤ x6.size + (1 : ℕ) - x1 := by
  intro n C hn hC hdep
  classical
  let F := circuitFun n C
  let P (s : ℕ) := ∃ D : Circuit, D.size ≤ s ∧ FanInTwo D ∧ Normal D ∧ circuitFun n D = F
  have hP : P C.size := by
    obtain ⟨D, hsz, hD, hN, hEq⟩ := normal_exists C hC
    exact ⟨D, hsz.le, hD, hN, funext (fun x => hEq (List.ofFn x))⟩
  have hex : ∃ s, P s := ⟨C.size, hP⟩
  obtain ⟨D, hs, hD, hN, hEq⟩ := Nat.find_spec hex
  have hmin (D' : Circuit) (hD' : FanInTwo D') (hn' : Normal D')
      (he : circuitFun n D' = F) : D.size ≤ D'.size :=
    hs.trans (Nat.find_min' hex ⟨D', le_rfl, hD', hn', he⟩)
  let R := D.gates.flatMap kept
  have live (w : ℕ) (hw : w < n + D.size) (ho : w ≠ D.output) : w ∈ R := by
    by_contra hno
    have hu : ∀ g ∈ D.gates, w ∉ g.inputs := by
      intro a ha hr
      apply hno
      change w ∈ D.gates.flatMap kept
      exact List.mem_flatMap.2 ⟨a, ha, (hN a ha).symm ▸ hr⟩
    by_cases hi : w < n
    · let i : Fin n := ⟨w, hi⟩
      obtain ⟨x, y, hxy, hne⟩ := hdep i
      have hv : ∀ j : ℕ, j ≠ w → (List.ofFn x).getD j false = (List.ofFn y).getD j false := by
        intro j hj
        by_cases h : j < n
        · rw [List.getD_eq_getElem _ _ (by simpa using h),
              List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn, List.getElem_ofFn]
          exact hxy _ (fun e => hj (congrArg Fin.val e))
        · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h),
              List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)]
      have hh := input_irrelevant D.gates w hu (List.ofFn x) (List.ofFn y)
        (by simp) (by simpa using hi) hv D.output (Ne.symm ho)
      apply hne
      change F x = F y
      rw [← hEq]
      exact hh
    · let j := w - n
      have hEqw : w = n + j := by dsimp [j]; omega
      obtain ⟨D', hs', hD', hn', he⟩ := remove_unused n D j (by omega) hD hN
        (by simpa [← hEqw] using (Ne.symm ho)) (by simpa [← hEqw] using hu)
      exact (Nat.not_lt_of_ge (hmin D' hD' hn' (he.trans hEq))) hs'
  refine ⟨D, hs.trans (Nat.find_min' hex hP), hD, hEq, live, ?_⟩
  have hsub : ((Finset.range (n + D.size)).erase D.output) ⊆ R.toFinset := by
    intro w hw
    exact List.mem_toFinset.2 (live w (Finset.mem_range.1 (Finset.mem_erase.1 hw).2)
      (Finset.mem_erase.1 hw).1)
  have hc := Finset.card_le_card hsub
  have low : n + D.size ≤ R.toFinset.card + 1 := by
    by_cases h : D.output ∈ Finset.range (n + D.size)
    · have hh := Finset.card_erase_add_one h
      rw [Finset.card_range] at hh
      omega
    · rw [Finset.erase_eq_of_notMem h, Finset.card_range] at hc
      omega
  have up := slot_budget D.gates
  have le := List.toFinset_card_le R
  change (D.gates.filter fun g => g.op.eval [false]).length + (R.length - R.toFinset.card) ≤
    D.size + 1 - n
  change _ + R.length ≤ 2 * D.size at up
  omega
