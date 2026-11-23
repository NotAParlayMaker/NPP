import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1332

open PEqualNP.CircuitLowerBounds

private def redirect (p z i : ℕ) : ℕ := if i = p then z else i

private def specializeGate (p z : ℕ) (g : Gate) : Gate :=
  match g.op with
  | .and => if p ∈ g.inputs then ⟨.or, []⟩ else g
  | .or => ⟨.or, g.inputs.filter fun i => i != p⟩
  | _ => ⟨g.op, g.inputs.map (redirect p z)⟩

private def good (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

private def binary (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2

private theorem specialize_good {p z : ℕ} {g : Gate} (h : good g) :
    good (specializeGate p z g) := by
  rcases g with ⟨op, ins⟩
  obtain ⟨ha | ho | hn, hl⟩ := h
  · cases ha
    by_cases hi : p ∈ ins <;> simp [good, specializeGate, hi, hl]
  · cases ho
    have hle := List.length_filter_le (fun i => i != p) ins
    simp [good, specializeGate, hle.trans hl]
  · cases hn
    simp [good, specializeGate, hl]

private theorem not_preserved {p z : ℕ} {g : Gate} (h : good g)
    (hn : (specializeGate p z g).op = .not) : g.op = .not := by
  rcases g with ⟨op, ins⟩
  obtain ⟨ha | ho | hg, _⟩ := h
  · cases ha
    by_cases hi : p ∈ ins <;> simp [specializeGate, hi] at hn
  · cases ho
    simp [specializeGate] at hn
  · exact hg

private theorem binary_preserved {p z : ℕ} {g : Gate} (h : good g)
    (hb : binary (specializeGate p z g)) : binary g ∧ p ∉ g.inputs := by
  rcases g with ⟨op, ins⟩
  obtain ⟨ha | ho | hn, hlen⟩ := h
  · cases ha
    by_cases hm : p ∈ ins
    · simp [specializeGate, binary, hm] at hb
    · exact ⟨by simpa [specializeGate, hm] using hb, hm⟩
  · cases ho
    have he : (ins.filter fun i => i != p).length = 2 := by
      simpa [specializeGate, binary] using hb
    have old : ins.length = 2 := by
      have := List.length_filter_le (fun i => i != p) ins
      change ins.length ≤ 2 at hlen
      omega
    refine ⟨⟨Or.inr rfl, old⟩, ?_⟩
    intro hmem
    have shorter : (ins.filter fun i => i != p).length < ins.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨p, hmem, by simp⟩
    omega
  · cases hn
    simp [specializeGate, binary] at hb

private def gv (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private def step (w : List Bool) (g : Gate) : List Bool := w ++ [gv w g]

private theorem read_set (w : List Bool) {p : ℕ} (hp : p < w.length) (i : ℕ) :
    (w.set p false).getD i false = if i = p then false else w.getD i false := by
  by_cases h : i = p
  · subst i
    simp [List.getD_eq_getElem?_getD, hp]
  · have ne : p ≠ i := fun e => h e.symm
    simp [List.getD_eq_getElem?_getD, h, ne]

private theorem read_redirect (w : List Bool) {p z : ℕ} (hp : p < w.length)
    (hz : w.length ≤ z) (i : ℕ) :
    w.getD (redirect p z i) false = (w.set p false).getD i false := by
  rw [read_set w hp i]
  by_cases h : i = p
  · simp [redirect, h, List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr hz]
  · simp [redirect, h]

private theorem gv_specialize (w : List Bool) {p z : ℕ} (hp : p < w.length)
    (hz : w.length ≤ z) (g : Gate) :
    gv w (specializeGate p z g) = gv (w.set p false) g := by
  cases g with
  | mk op ins =>
    cases op with
    | and =>
      by_cases hm : p ∈ ins
      · simp only [specializeGate, if_pos hm, gv, GateOp.eval, List.map_nil, List.any_nil]
        symm
        apply Bool.eq_false_of_not_eq_true
        intro h
        simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at h
        have bad := h p hm
        change (w.set p false).getD p false = true at bad
        rw [read_set w hp p] at bad
        simp at bad
      · simp only [specializeGate, if_neg hm, gv]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hip : i ≠ p := fun h => hm (h ▸ hi)
        simp only [read_set w hp i, if_neg hip]
    | or =>
      simp only [specializeGate, gv, GateOp.eval, List.any_map, List.any_filter, Function.comp_apply, id_eq]
      congr 1
      funext i
      change ((i != p) && w.getD i false) = (w.set p false).getD i false
      rw [read_set w hp i]
      by_cases h : i = p <;> simp [h]
    | not | mod | maj =>
      simp only [specializeGate, gv, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact read_redirect w hp hz i

private theorem fold_specialize (gs : List Gate) (w : List Bool) {p z : ℕ}
    (hp : p < w.length) (hz : w.length + gs.length ≤ z) :
    gs.foldl step (w.set p false) = ((gs.map (specializeGate p z)).foldl step w).set p false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    let w' := step w (specializeGate p z g)
    have hv := gv_specialize w (z := z) hp (by simp at hz; omega) g
    have e : step (w.set p false) g = w'.set p false := by
      simp only [w', step, List.set_append_left p false hp, hv]
    have newLen : w'.length = w.length + 1 := by simp [w', step]
    simp only [List.map_cons, List.foldl_cons]
    rw [e]
    exact ih w' (by omega) (by simp at hz; omega)

private theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

private theorem set_inputs {n : ℕ} (x : Fin n → Bool) (p : Fin n) :
    List.ofFn (fun i => if i = p then false else x i) = (List.ofFn x).set p.val false := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  rw [List.getElem_ofFn, List.getElem_set]
  have hin : i < n := by simpa using hi
  by_cases h : i = p.val
  · have hp : (⟨i, hin⟩ : Fin n) = p := Fin.ext h
    simp [h]
  · have hp : (⟨i, hin⟩ : Fin n) ≠ p := fun eq => h (congrArg Fin.val eq)
    have hrev : p.val ≠ i := fun e => h e.symm
    simp [hp, hrev]

end PEqualNP.Outside.L_meta_1332

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1332
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.L_meta_1332 :
    ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → ∀ p : Fin n, (∃ i0 : Fin m, p ∈ S i0 ∧ ∃ v0 ∈ S i0, v0 ≠ p) → ∀ a b : Fin gates.length, a ≠ b → ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (gates.get a).inputs.length = 2 → p.val ∈ (gates.get a).inputs → ((gates.get b).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get b).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (gates.get b).inputs.length = 2 → p.val ∈ (gates.get b).inputs → ∀ (t : ℕ) (ι : Fin t → Fin gates.length), (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r : Fin t, ι r = q) → ∀ I : Finset (Fin gates.length), (∀ q2 : Fin gates.length, ((gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gates.get q2).inputs.length = 2 → q2 ∈ I) → ∃ (gl : List PEqualNP.CircuitLowerBounds.Gate) (ol : Fin m → ℕ) (κ : Fin t → Fin gl.length) (J : Finset (Fin gl.length)), (∀ h ∈ gl, (h.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ h.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ h.inputs.length ≤ 2) ∧ (∀ q3 : Fin gl.length, (gl.get q3).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ r2 : Fin t, κ r2 = q3) ∧ (∀ q4 : Fin gl.length, ((gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ (gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (gl.get q4).inputs.length = 2 → q4 ∈ J) ∧ J.card + 2 ≤ I.card ∧ ∀ (o2 : Fin m) (x2 : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol o2⟩ (List.ofFn x2) = decide (∃ v2 ∈ S o2, v2 ≠ p ∧ x2 v2 = true) := by
  intro n m S _ gates out goodGates computes p _ a b distinct aOp aLen aRead bOp bLen bRead
    t iota coversNot I coversBinary
  let z := n + gates.length
  let sg := specializeGate p.val z
  let gl := gates.map sg
  let e : Fin gl.length ≃ Fin gates.length := finCongr (by simp [gl])
  let J := ((I.erase a).erase b).map e.symm.toEmbedding
  have atGate (q : Fin gl.length) : gl.get q = sg (gates.get (e q)) := by
    change (gates.map sg)[q.val] = sg (gates[(e q).val])
    rw [List.getElem_map] <;> rfl
  have goodOrig (q : Fin gates.length) : good (gates.get q) :=
    goodGates _ (List.get_mem gates q)
  refine ⟨gl, fun i => redirect p.val z (out i), fun r => e.symm (iota r), J, ?_, ?_, ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hh
    exact specialize_good (goodGates _ hg)
  · intro q hn
    rw [atGate] at hn
    obtain ⟨r, hr⟩ := coversNot (e q) (not_preserved (goodOrig (e q)) hn)
    exact ⟨r, by simpa only [Equiv.symm_apply_apply] using congrArg e.symm hr⟩
  · intro q hq
    change binary (gl.get q) at hq
    rw [atGate] at hq
    obtain ⟨old, noP⟩ := binary_preserved (goodOrig (e q)) hq
    have notA : e q ≠ a := fun he => noP (he.symm ▸ aRead)
    have notB : e q ≠ b := fun he => noP (he.symm ▸ bRead)
    apply Finset.mem_map.mpr
    exact ⟨e q, Finset.mem_erase.mpr ⟨notB, Finset.mem_erase.mpr ⟨notA, coversBinary (e q) old⟩⟩,
      e.symm_apply_apply q⟩
  · have aIn : a ∈ I := coversBinary a ⟨aOp, aLen⟩
    have bIn : b ∈ I.erase a := Finset.mem_erase.mpr ⟨distinct.symm, coversBinary b ⟨bOp, bLen⟩⟩
    have aCard := Finset.card_erase_add_one aIn
    have bCard := Finset.card_erase_add_one bIn
    simp only [J, Finset.card_map]
    omega
  · intro o x
    let fix (i : Fin n) := if i = p then false else x i
    have hp : p.val < (List.ofFn x).length := by simpa using p.isLt
    have hz : (List.ofFn x).length + gates.length ≤ z := by simp [z]
    have runEq : Circuit.eval ⟨gl, redirect p.val z (out o)⟩ (List.ofFn x) =
        Circuit.eval ⟨gates, out o⟩ (List.ofFn fix) := by
      change (gl.foldl step (List.ofFn x)).getD (redirect p.val z (out o)) false =
        (gates.foldl step (List.ofFn fix)).getD (out o) false
      change (gl.foldl step (List.ofFn x)).getD (redirect p.val z (out o)) false =
        (gates.foldl step (List.ofFn (fun i => if i = p then false else x i))).getD (out o) false
      rw [set_inputs x p, fold_specialize gates (List.ofFn x) hp hz]
      apply read_redirect
      · rw [fold_length]; simp only [List.length_ofFn]; omega
      · rw [fold_length]
        simp [gl, z]
    rw [runEq, computes]
    apply decide_eq_decide.mpr
    constructor
    · rintro ⟨v, hv, htrue⟩
      have hne : v ≠ p := by
        rintro rfl
        simp [fix] at htrue
      exact ⟨v, hv, hne, by simpa [fix, hne] using htrue⟩
    · rintro ⟨v, hv, hne, htrue⟩
      exact ⟨v, hv, by simpa [fix, hne] using htrue⟩
