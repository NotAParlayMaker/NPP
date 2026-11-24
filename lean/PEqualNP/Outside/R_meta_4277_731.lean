import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Delete the last gate outside the output-closed set.
-- If the complemented input is unused, remove the precomputed inverter instead.
theorem PEqualNP.Outside.R_meta_4277_731
    (short : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) x1 (14 : ℕ))
    (used : ∀ C : Circuit, FanInTwo C → C.size = 14 →
      10 ≤ C.output → C.output < 24 →
      let mark (g : Gate) := ([0, 9] : List ℕ).any g.inputs.contains
      (C.gates.filter mark).length = 2 →
      (C.gates.filter (fun g => !mark g && g.inputs.contains 4)).length ≤ 1 →
      (∀ g ∈ C.gates, mark g = true → ∃ w : ℕ, w ≠ 0 ∧ w ≠ 9 ∧
        ((g.op = .or ∧ (g.inputs = [0, w] ∨ g.inputs = [w, 0])) ∨
         (g.op = .and ∧ (g.inputs = [9, w] ∨ g.inputs = [w, 9])))) →
      (∃ g ∈ C.gates, 9 ∈ g.inputs) →
      ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!x 0]) ≠
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Set ℕ), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size = (14 : ℕ) → (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any x5.inputs.contains) x1.gates).length = (2 : ℕ) → (List.filter (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => ! [(0 : ℕ), (9 : ℕ)].any x6.inputs.contains && x6.inputs.contains (4 : ℕ)) x1.gates).length ≤ (1 : ℕ) → (x1.output ∈ x2 ∧ (0 : ℕ) ∉ x2 ∧ (9 : ℕ) ∉ x2 ∧ ∀ (x7 : List PEqualNP.CircuitLowerBounds.Gate) (x8 : PEqualNP.CircuitLowerBounds.Gate) (x9 : List PEqualNP.CircuitLowerBounds.Gate), x1.gates = x7 ++ x8 :: x9 → if [(0 : ℕ), (9 : ℕ)].any x8.inputs.contains = Bool.true then (10 : ℕ) + x7.length ∈ x2 → ∃ x12 ∈ x2, x8.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (x8.inputs = [(0 : ℕ), x12] ∨ x8.inputs = [x12, (0 : ℕ)]) ∨ x8.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x8.inputs = [(9 : ℕ), x12] ∨ x8.inputs = [x12, (9 : ℕ)]) else (10 : ℕ) + x7.length ∈ x2 ∧ ∀ x11 ∈ x8.inputs, x11 ∈ x2) → ∃ (x8 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))]) ≠ (fun (x9 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x10 : ℕ) => x9 (Fin.ofNat (9 : ℕ) (x10 / (10 : ℕ))) && x9 (Fin.ofNat (9 : ℕ) (x10 % (10 : ℕ)))) x8 := by
  intro C X hFan hLen hCount hFour hX
  classical
  let mark (g : Gate) := ([0, 9] : List ℕ).any g.inputs.contains
  let seed (x : Fin 9 → Bool) := List.ofFn x ++ [!x 0]
  let F (x : Fin 9 → Bool) :=
    ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  let step (ws : List Bool) (g : Gate) :=
    ws ++ [g.op.eval (g.inputs.map (fun i => ws.getD i false))]
  let index (q i : ℕ) := if i < q then i else i - 1
  let rename (q : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (index q)⟩
  have hSize : C.gates.length = 14 := hLen
  have seedLen (x : Fin 9 → Bool) : (seed x).length = 10 := by simp [seed]
  have len (L : List Gate) (w : List Bool) : (L.foldl step w).length = w.length + L.length := by
    induction L generalizing w with
    | nil => simp
    | cons g L ih =>
      rw [List.foldl_cons, ih]
      simp only [step, List.length_append, List.length_singleton, List.length_cons, List.length_nil]
      omega
  have old (L : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
      (L.foldl step w).getD j false = w.getD j false := by
    induction L generalizing w with
    | nil => rfl
    | cons g L ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      exact List.getD_append w _ false j hj
  have fanRename (q : ℕ) (L : List Gate) (h : ∀ g ∈ L, g ∈ C.gates) (o : ℕ) :
      FanInTwo ⟨L.map (rename q), o⟩ := by
    intro g hg
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
    have hgood := hFan f (h f hf)
    exact ⟨hgood.1, by simpa only [rename, List.length_map] using hgood.2⟩
  have readSkip (q : ℕ) (w : List Bool) (hLen : w.length = q) (b : Bool)
      (ys : List Bool) (i : ℕ) (hi : i ≠ q) :
      (w ++ [b] ++ ys).getD i false = (w ++ ys).getD (index q i) false := by
    by_cases h : i < q
    · rw [show index q i = i from ite_eq_left h, List.append_assoc]
      rw [List.getD_append w ([b] ++ ys) false i (by omega),
        List.getD_append w ys false i (by omega)]
    · rw [show index q i = i - 1 from ite_eq_right h]
      have hq : q + 1 ≤ i := by omega
      rw [List.getD_append_right (w ++ [b]) ys false i (by simp only [List.length_append, List.length_singleton, hLen]; omega),
        List.getD_append_right w ys false (i - 1) (by omega)]
      simp only [List.length_append, List.length_singleton, hLen]
      rw [show i - (q + 1) = i - 1 - q by omega]
  have runShort (q : ℕ) (w : List Bool) (hq : w.length = q) (b : Bool)
      (L : List Gate) (avoid : ∀ g ∈ L, q ∉ g.inputs) (ys : List Bool) :
      ∃ zs, L.foldl step (w ++ [b] ++ ys) = w ++ [b] ++ zs ∧
        (L.map (rename q)).foldl step (w ++ ys) = w ++ zs := by
    induction L generalizing ys with
    | nil => exact ⟨ys, rfl, rfl⟩
    | cons g L ih =>
      have hg := avoid g List.mem_cons_self
      let v := g.op.eval (g.inputs.map (fun i => (w ++ [b] ++ ys).getD i false))
      have hMap : g.inputs.map (fun i => (w ++ [b] ++ ys).getD i false) =
          g.inputs.map (fun i => (w ++ ys).getD (index q i) false) :=
        List.map_congr_left (fun i hi => readSkip q w hq b ys i (fun e => hg (e ▸ hi)))
      have hOld : step (w ++ [b] ++ ys) g = w ++ [b] ++ (ys ++ [v]) := by
        exact List.append_assoc _ _ _
      have hNew : step (w ++ ys) (rename q g) = w ++ (ys ++ [v]) := by
        change ((w ++ ys) ++ [g.op.eval ((g.inputs.map (index q)).map
          (fun i => (w ++ ys).getD i false))]) = _
        rw [List.map_map, Function.comp_def, ← hMap]
        exact List.append_assoc _ _ _
      rw [List.foldl_cons, List.map_cons, List.foldl_cons, hOld, hNew]
      exact ih (fun g hg => avoid g (List.mem_cons_of_mem _ hg)) (ys ++ [v])
  have sameBefore (q : ℕ) (L : List Gate) (w : List Bool) (h : w.length + L.length ≤ q) :
      (L.map (rename q)).foldl step w = L.foldl step w := by
    induction L generalizing w with
    | nil => rfl
    | cons g L ih =>
      have hw : w.length < q := by simp at h; omega
      have hMap : g.inputs.map (fun i => w.getD (index q i) false) =
          g.inputs.map (fun i => w.getD i false) := by
        apply List.map_congr_left
        intro i _
        by_cases hi : i < q
        · rw [show index q i = i from ite_eq_left hi]
        · rw [show index q i = i - 1 from ite_eq_right hi, List.getD_eq_default w false (by omega),
            List.getD_eq_default w false (by omega)]
      have eqStep : step w (rename q g) = step w g := by
        change w ++ [g.op.eval ((g.inputs.map (index q)).map (fun i => w.getD i false))] =
          w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
        rw [List.map_map, Function.comp_def, hMap]
      rw [List.map_cons, List.foldl_cons, List.foldl_cons, eqStep]
      apply ih
      simp only [step, List.length_append, List.length_singleton]
      simp only [List.length_cons] at h
      omega
  have splitAt (L : List Gate) (i : ℕ) (hi : i < L.length) :
      ∃ before g after, L = before ++ g :: after ∧ before.length = i := by
    induction L generalizing i with
    | nil => simp at hi
    | cons g L ih =>
      cases i with
      | zero => exact ⟨[], g, L, rfl, rfl⟩
      | succ i =>
        obtain ⟨b, d, a, e, hn⟩ := ih i (by simpa using hi)
        exact ⟨g :: b, d, a, by simp only [List.cons_append, ← e], by simp [hn]⟩
  have bitsX (pre : List Gate) (g : Gate) (post : List Gate)
      (eq : C.gates = pre ++ g :: post) (live : 10 + pre.length ∈ X) :
      ∀ i ∈ g.inputs, i ∈ X ∨ i = 0 ∨ i = 9 := by
    have h := hX.2.2.2 pre g post eq
    change (if mark g = true then 10 + pre.length ∈ X → _ else _) at h
    by_cases hm : mark g = true
    · rw [ite_eq_left hm] at h
      obtain ⟨w, hw, hForm⟩ := h live
      rcases hForm with ⟨_, e | e⟩ | ⟨_, e | e⟩ <;> rw [e] <;> simp [hw]
    · rw [ite_eq_right hm] at h
      intro i hi
      exact Or.inl (h.2 i hi)
  by_contra! hAgrees
  change ∀ x : Fin 9 → Bool, C.eval (seed x) = F x at hAgrees
  let dropped := (Finset.range C.gates.length).filter (fun i => 10 + i ∉ X)
  by_cases hDrop : dropped.Nonempty
  · let a := dropped.max' hDrop
    have hMem : a ∈ dropped := Finset.max'_mem _ _
    have ha : a < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hMem).1
    have hdead : 10 + a ∉ X := (Finset.mem_filter.mp hMem).2
    obtain ⟨before, g, after, eqGate, beforeLen⟩ := splitAt C.gates a ha
    let q := 10 + a
    have hAfter : ∀ p ∈ after, q ∉ p.inputs := by
      intro p hp hread
      obtain ⟨pre, post, ep⟩ := List.mem_iff_append.mp hp
      let i := (before ++ [g] ++ pre).length
      have e : C.gates = (before ++ [g] ++ pre) ++ p :: post := by
        simp only [eqGate, ep, List.append_assoc, List.singleton_append]
        rfl
      have hi : i < C.gates.length := by
        rw [e]
        simp only [i, List.length_append, List.length_cons, List.length_singleton]
        omega
      have hgt : a < i := by simp [i, beforeLen]; omega
      have hLive : 10 + i ∈ X := by
        by_contra hn
        have hiMem : i ∈ dropped :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hn⟩
        exact hgt.not_ge (Finset.le_max' _ _ hiMem)
      have hAllowed := bitsX (before ++ [g] ++ pre) p post e hLive q hread
      change (10 + a) ∈ X ∨ 10 + a = 0 ∨ 10 + a = 9 at hAllowed
      rcases hAllowed with hh | hh | hh
      · exact hdead hh
      · omega
      · omega
    let inverter : Gate := ⟨.not, [0]⟩
    let L := before ++ after
    let D : Circuit := ⟨inverter :: L.map (rename q), index q C.output⟩
    apply short
    refine ⟨D, ?_, ?_, ?_⟩
    · have hTail := fanRename q L (fun p hp => by
        change p ∈ before ++ after at hp
        rw [eqGate]
        rcases List.mem_append.mp hp with hp | hp
        · exact List.mem_append_left _ hp
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ hp)) (index q C.output)
      intro p hp
      change p ∈ inverter :: L.map (rename q) at hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨by simp [inverter], by simp [inverter]⟩
      · exact hTail p hp
    · change (inverter :: L.map (rename q)).length ≤ 14
      have h := congrArg List.length eqGate
      simp only [hSize, List.length_append, List.length_cons] at h
      simp only [List.length_cons, List.length_map, L, List.length_append]
      omega
    · intro x
      have first : step (List.ofFn x) inverter = seed x := by
        have hx0 : (List.ofFn x).getD 0 false = x 0 := by
          rw [List.getD_eq_getElem _ false (n := 0) (by simp), List.getElem_ofFn]
          rfl
        change List.ofFn x ++ [!(List.ofFn x).getD 0 false] = seed x
        rw [hx0]
      let w := before.foldl step (seed x)
      have hw : w.length = q := by rw [show w.length = _ from len before (seed x), seedLen, beforeLen]
      let b := g.op.eval (g.inputs.map (fun i => w.getD i false))
      obtain ⟨ys, hOld, hNew⟩ := runShort q w hw b after hAfter []
      simp only [List.append_nil] at hOld hNew
      have oldVal : C.eval (seed x) = (w ++ [b] ++ ys).getD C.output false := by
        change (C.gates.foldl step (seed x)).getD C.output false = _
        rw [eqGate, List.foldl_append, List.foldl_cons]
        change (after.foldl step (w ++ [b])).getD C.output false = _
        rw [hOld]
      have outNe : C.output ≠ q := by
        intro e
        apply hdead
        change q ∈ X
        rw [← e]
        exact hX.1
      change ((inverter :: L.map (rename q)).foldl step (List.ofFn x)).getD (index q C.output) false = _
      rw [List.foldl_cons, first, show L = before ++ after from rfl, List.map_append, List.foldl_append,
        sameBefore q before (seed x) (by rw [seedLen, beforeLen]), hNew, ← readSkip q w hw b ys C.output outNe,
        ← oldVal, hAgrees x]
  · have hAll (i : ℕ) (hi : i < C.gates.length) : 10 + i ∈ X := by
      by_contra h
      exact hDrop ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, h⟩⟩
    by_cases hInverter : ∃ p ∈ C.gates, 9 ∈ p.inputs
    · have loops : ∀ g ∈ C.gates, mark g = true → ∃ w : ℕ, w ≠ 0 ∧ w ≠ 9 ∧
          ((g.op = .or ∧ (g.inputs = [0, w] ∨ g.inputs = [w, 0])) ∨
           (g.op = .and ∧ (g.inputs = [9, w] ∨ g.inputs = [w, 9]))) := by
        intro g hg hm
        obtain ⟨pr, su, e⟩ := List.mem_iff_append.mp hg
        have hp : pr.length < C.gates.length := by simp [e]
        have props := hX.2.2.2 pr g su e
        change (if mark g = true then _ else _) at props
        rw [ite_eq_left hm] at props
        obtain ⟨w, hw, hh⟩ := props (hAll _ hp)
        exact ⟨w, fun e => hX.2.1 (e ▸ hw), fun e => hX.2.2.1 (e ▸ hw), hh⟩
      have hEval (x : Fin 9 → Bool) :
          (C.gates.foldl step (seed x)).getD C.output false = F x := hAgrees x
      have hOutMin : 10 ≤ C.output := by
        by_contra! ho
        have ho9 : C.output ≠ 9 := fun e => hX.2.2.1 (e ▸ hX.1)
        let v : Fin 9 := ⟨C.output, by omega⟩
        let x : Fin 9 → Bool := fun i => decide (i = v)
        have hx : F x = false := by
          have h : ∀ v : Fin 9, F (fun i => decide (i = v)) = false := by decide +kernel
          exact h v
        have key := hEval x
        rw [old _ _ _ (by rw [seedLen]; omega), hx] at key
        have hv : (seed x).getD C.output false = true := by
          change (List.ofFn x ++ [!x 0]).getD v.val false = true
          rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ false (n := v.val) (by simp),
            List.getElem_ofFn]
          simp [x]
        exact Bool.noConfusion (hv.symm.trans key)
      have hOutMax : C.output < 24 := by
        by_contra! ho
        let x : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1)
        have ht : F x = true := by decide
        have hm := hEval x
        rw [List.getD_eq_default _ false (by rw [len, seedLen, hSize]; exact ho), ht] at hm
        exact Bool.noConfusion hm
      obtain ⟨x, hx⟩ := used C hFan hLen hOutMin hOutMax hCount hFour loops hInverter
      exact hx (hAgrees x)
    · have avoid : ∀ p ∈ C.gates, 9 ∉ p.inputs := by
        intro p hp hn
        exact hInverter ⟨p, hp, hn⟩
      let D : Circuit := ⟨C.gates.map (rename 9), index 9 C.output⟩
      have outNe : C.output ≠ 9 := fun e => hX.2.2.1 (e ▸ hX.1)
      apply short
      refine ⟨D, fanRename 9 C.gates (fun _ h => h) _, ?_, ?_⟩
      · change (C.gates.map (rename 9)).length ≤ 14
        rw [List.length_map, hSize]
      · intro x
        let w := List.ofFn x
        have hw : w.length = 9 := List.length_ofFn
        obtain ⟨ys, hOld, hNew⟩ := runShort 9 w hw (!x 0) C.gates avoid []
        simp only [List.append_nil] at hOld hNew
        change ((C.gates.map (rename 9)).foldl step w).getD (index 9 C.output) false = _
        rw [hNew, ← readSkip 9 w hw (!x 0) ys C.output outNe, ← hOld]
        exact hAgrees x
