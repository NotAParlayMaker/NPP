import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_907

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

private lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

private lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

private def val (C : Circuit) (x : Fin 9 → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma input_val (C : Circuit) (x : Fin 9 → Bool) (p : Fin 9) :
    val C x p.val = x p := by
  change (run C.gates (List.ofFn x)).getD p.val false = x p
  have hp : p.val < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp, List.getElem_ofFn]

private lemma missing_val (C : Circuit) (x : Fin 9 → Bool) (w : ℕ)
    (hw : 9 + C.gates.length ≤ w) : val C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length] using hw)

private lemma gate_val (C : Circuit) (x : Fin 9 → Bool) (j : ℕ) (hj : j < C.gates.length) :
    val C x (9 + j) =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun r => if r < 9 + j then val C x r else false) := by
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = 9 + j := by
    simp [earlier, run_length, Nat.min_eq_left hj.le]
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < 9 + j then val C x r else false := by
    by_cases hr : r < 9 + j
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD (9 + j) false =
    g.op.eval (g.inputs.map fun r => if r < 9 + j then val C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

private lemma op_and_or_of_ne_not (C : Circuit) (hfan : FanInTwo C) (j : ℕ)
    (hj : j < C.gates.length) (hne : (C.gates[j]).op ≠ GateOp.not) :
    (C.gates[j]).op = GateOp.and ∨ (C.gates[j]).op = GateOp.or := by
  have hmem := (hfan _ (List.getElem_mem hj)).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h hne

private lemma eval_and_or_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f g : ℕ → Bool) (hfg : ∀ r ∈ l, f r = true → g r = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro h b hb
    obtain ⟨r, hr, rfl⟩ := hb
    exact hfg r hr (h _ ⟨r, hr, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨b, ⟨r, hr, rfl⟩, h⟩
    exact ⟨g r, ⟨r, hr, rfl⟩, hfg r hr h⟩

private lemma val_mono_before (C : Circuit) (hfan : FanInTwo C) (k : ℕ)
    (hno : ∀ j : ℕ, (hj : j < C.gates.length) → j < k → (C.gates[j]).op ≠ GateOp.not)
    (x y : Fin 9 → Bool) (hxy : ∀ q, x q = true → y q = true) :
    ∀ w : ℕ, w < 9 + k → val C x w = true → val C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hx
    by_cases h9 : w < 9
    · have h1 := input_val C x ⟨w, h9⟩
      have h2 := input_val C y ⟨w, h9⟩
      exact h2 ▸ hxy ⟨w, h9⟩ (h1 ▸ hx)
    · by_cases hlen : w < 9 + C.gates.length
      · have hj : w - 9 < C.gates.length := by omega
        have heq : 9 + (w - 9) = w := by omega
        rw [← heq] at hx ⊢
        rw [gate_val C x (w - 9) hj] at hx
        rw [gate_val C y (w - 9) hj]
        have hop := op_and_or_of_ne_not C hfan (w - 9) hj (hno (w - 9) hj (by omega))
        apply eval_and_or_mono _ hop _ _ _ _ hx
        intro r _ hr
        by_cases hlt : r < 9 + (w - 9)
        · rw [ite_eq_left hlt] at hr ⊢
          exact ih r (by omega) (by omega) hr
        · rw [ite_eq_right hlt] at hr
          exact Bool.noConfusion hr
      · rw [missing_val C x w (by omega)] at hx
        exact Bool.noConfusion hx

private lemma exists_H (C : Circuit) (hfan : FanInTwo C)
    (huniq : ∀ i j : Fin C.gates.length, (C.gates.get i).op = GateOp.not →
      (C.gates.get j).op = GateOp.not → i = j) :
    ∃ H : (Fin 9 → Bool) → Bool,
      (∀ x y : Fin 9 → Bool, (∀ q, x q = true → y q = true) → H x = true → H y = true) ∧
      (∀ x y : Fin 9 → Bool, (∀ q, x q = true → y q = true) → H x = H y →
        ∀ w : ℕ, val C x w = true → val C y w = true) ∧
      (∀ j : Fin C.gates.length, (C.gates.get j).op = GateOp.not →
        ∀ x : Fin 9 → Bool, val C x (9 + j.val) = !(H x)) := by
  by_cases hex : ∃ p : Fin C.gates.length, (C.gates.get p).op = GateOp.not
  · obtain ⟨p, hp⟩ := hex
    let H : (Fin 9 → Bool) → Bool := fun x =>
      ((C.gates[p.val]).inputs.map fun r => if r < 9 + p.val then val C x r else false).headD false
    have hne_other : ∀ j : ℕ, (hj : j < C.gates.length) → j ≠ p.val → (C.gates[j]).op ≠ GateOp.not := by
      intro j hj hne hop
      have := huniq ⟨j, hj⟩ p (by simpa using hop) hp
      exact hne (congrArg Fin.val this)
    have hnot_eval : ∀ x : Fin 9 → Bool, val C x (9 + p.val) = !(H x) := by
      intro x
      rw [gate_val C x p.val p.isLt]
      have hp' : (C.gates[p.val]).op = GateOp.not := by simpa using hp
      rw [hp']
      rfl
    refine ⟨H, ?_, ?_, ?_⟩
    · intro x y hxy hx
      have hmb := val_mono_before C hfan p.val (fun j hj hlt => hne_other j hj (by omega)) x y hxy
      dsimp only [H] at hx ⊢
      cases hins : (C.gates[p.val]).inputs with
      | nil => simp [hins] at hx
      | cons r _ =>
        simp only [hins, List.map_cons, List.headD_cons] at hx ⊢
        by_cases hr : r < 9 + p.val
        · rw [ite_eq_left hr] at hx ⊢
          exact hmb r hr hx
        · rw [ite_eq_right hr] at hx
          exact Bool.noConfusion hx
    · intro x y hxy hHeq w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hx
        by_cases h9 : w < 9
        · have h1 := input_val C x ⟨w, h9⟩
          have h2 := input_val C y ⟨w, h9⟩
          exact h2 ▸ hxy ⟨w, h9⟩ (h1 ▸ hx)
        · by_cases hlen : w < 9 + C.gates.length
          · have hj : w - 9 < C.gates.length := by omega
            have heq : 9 + (w - 9) = w := by omega
            by_cases hwp : w - 9 = p.val
            · rw [← heq, hwp, hnot_eval x] at hx
              rw [← heq, hwp, hnot_eval y, ← hHeq]
              exact hx
            · rw [← heq] at hx ⊢
              rw [gate_val C x (w - 9) hj] at hx
              rw [gate_val C y (w - 9) hj]
              have hop := op_and_or_of_ne_not C hfan (w - 9) hj (hne_other (w - 9) hj hwp)
              apply eval_and_or_mono _ hop _ _ _ _ hx
              intro r _ hr
              by_cases hlt : r < 9 + (w - 9)
              · rw [ite_eq_left hlt] at hr ⊢
                exact ih r (by omega) hr
              · rw [ite_eq_right hlt] at hr
                exact Bool.noConfusion hr
          · rw [missing_val C x w (by omega)] at hx
            exact Bool.noConfusion hx
    · intro j hj x
      have hjp : j = p := huniq j p hj hp
      subst hjp
      exact hnot_eval x
  · refine ⟨fun _ => false, ?_, ?_, ?_⟩
    · intro _ _ _ h
      exact h
    · intro x y hxy _ w
      by_cases hlen : w < 9 + C.gates.length
      · exact val_mono_before C hfan C.gates.length
          (fun j hj _ hop => hex ⟨⟨j, hj⟩, by simpa using hop⟩) x y hxy w hlen
      · intro hx
        rw [missing_val C x w (by omega)] at hx
        exact Bool.noConfusion hx
    · intro j hj
      exact absurd ⟨j, hj⟩ hex

private def linePt (a b c : Fin 3) : Fin 9 :=
  ⟨3 * c.val + (a * c + b).val, by omega⟩

private def lineSet (p : Fin 3 × Fin 3) : Finset (Fin 9) :=
  Finset.univ.image (linePt p.1 p.2)

private lemma lineSet_card (p : Fin 3 × Fin 3) : (lineSet p).card = 3 := by
  revert p
  decide

private lemma lineSet_inter (p q : Fin 3 × Fin 3) (h : p ≠ q) :
    (lineSet p ∩ lineSet q).card ≤ 1 := by
  revert p q h
  decide

private lemma lineSet_sdiff (p q : Fin 3 × Fin 3) (h : p ≠ q) :
    ∃ k : Fin 9, k ∈ lineSet q ∧ k ∉ lineSet p := by
  revert p q h
  decide

private lemma lineSet_spec (x : Fin 9 → Bool) (a b : Fin 3) :
    (∃ c : Fin 3, ∃ k : Fin 9, (k : ℕ) = 3 * (c : ℕ) + ((a * c + b : Fin 3) : ℕ) ∧ x k = true) ↔
      ∃ k ∈ lineSet (a, b), x k = true := by
  constructor
  · rintro ⟨c, k, hk, hxk⟩
    refine ⟨k, ?_, hxk⟩
    rw [lineSet, Finset.mem_image]
    exact ⟨c, Finset.mem_univ c, Fin.ext hk.symm⟩
  · rintro ⟨k, hk, hxk⟩
    rw [lineSet, Finset.mem_image] at hk
    obtain ⟨c, _, rfl⟩ := hk
    exact ⟨c, linePt a b c, rfl, hxk⟩

private def targetFun (S : Finset (Fin 9)) (x : Fin 9 → Bool) : Bool :=
  decide (∃ k ∈ S, x k = true)

private def single (q : Fin 9) : Fin 9 → Bool :=
  fun r => decide (r = q)

private def outsideVec (S : Finset (Fin 9)) : Fin 9 → Bool :=
  fun r => decide (r ∉ S)

private def supp (C : Circuit) (w : ℕ) : Finset (Fin 9) :=
  Finset.univ.filter fun q => val C (single q) w = true

private lemma mem_supp (C : Circuit) (w : ℕ) (q : Fin 9) :
    q ∈ supp C w ↔ val C (single q) w = true := by
  simp [supp]

private lemma ge_nine_of_supp_card (C : Circuit) (w : ℕ) (h : 2 ≤ (supp C w).card) : 9 ≤ w := by
  by_contra hw
  have hw' : w < 9 := by omega
  let p : Fin 9 := ⟨w, hw'⟩
  have hsub : supp C w ⊆ {p} := by
    intro q hq
    have hv := (mem_supp C w q).mp hq
    change val C (single q) p.val = true at hv
    rw [input_val] at hv
    simp only [single, decide_eq_true_eq] at hv
    simp [p, hv]
  have hle := Finset.card_le_card hsub
  simp at hle
  omega

private lemma targetFun_false (S : Finset (Fin 9)) : targetFun S (fun _ => false) = false := by
  simp [targetFun]

private lemma targetFun_true (S : Finset (Fin 9)) (hS : S.Nonempty) :
    targetFun S (fun _ => true) = true := by
  obtain ⟨k, hk⟩ := hS
  simp only [targetFun, decide_eq_true_eq]
  exact ⟨k, hk, trivial⟩

private lemma targetFun_single (S : Finset (Fin 9)) (q : Fin 9) :
    targetFun S (single q) = decide (q ∈ S) := by
  simp [targetFun, single]

private lemma targetFun_outside (S : Finset (Fin 9)) : targetFun S (outsideVec S) = false := by
  simp [targetFun, outsideVec]

private lemma earliest_gate_and_helper (C : Circuit) (hfan : FanInTwo C)
    (H : (Fin 9 → Bool) → Bool)
    (hHmono : ∀ x y : Fin 9 → Bool, (∀ q, x q = true → y q = true) → H x = true → H y = true)
    (hHval : ∀ x y : Fin 9 → Bool, (∀ q, x q = true → y q = true) → H x = H y →
      ∀ w : ℕ, val C x w = true → val C y w = true)
    (hHnot : ∀ j : Fin C.gates.length, (C.gates.get j).op = GateOp.not →
      ∀ x : Fin 9 → Bool, val C x (9 + j.val) = !(H x))
    (S : Finset (Fin 9)) (hScard : S.card = 3)
    (w : ℕ) (hw : ∀ x : Fin 9 → Bool, val C x w = targetFun S x)
    (hmin : ∀ w' : ℕ, w' < w → ¬ (∀ x : Fin 9 → Bool, val C x w' = targetFun S x)) :
    ∃ (go gu : Fin C.gates.length),
      w = 9 + go.val ∧
      (C.gates.get go).op ≠ GateOp.not ∧
      (C.gates.get gu).op ≠ GateOp.not ∧
      gu.val < go.val ∧
      ((supp C (9 + gu.val) ⊆ S ∧ 2 ≤ (supp C (9 + gu.val)).card) ∨
        (val C (outsideVec S) (9 + gu.val) = false ∧
          ∀ x : Fin 9 → Bool, targetFun S x = true → val C x (9 + gu.val) = true)) := by
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hsupp_w : supp C w = S := by
    ext q
    rw [mem_supp, hw, targetFun_single, decide_eq_true_eq]
  have hw_ge : 9 ≤ w := ge_nine_of_supp_card C w (by rw [hsupp_w]; omega)
  have hw_lt : w < 9 + C.gates.length := by
    by_contra hge
    have h1 := hw (fun _ => true)
    rw [missing_val C _ w (by omega), targetFun_true S hSne] at h1
    exact Bool.noConfusion h1
  let go : Fin C.gates.length := ⟨w - 9, by omega⟩
  have hwo : w = 9 + go.val := by dsimp [go]; omega
  have hgo_ne_not : (C.gates.get go).op ≠ GateOp.not := by
    intro hnot
    have h0 := hw (fun _ => false)
    rw [hwo, hHnot go hnot, targetFun_false] at h0
    have hH0 : H (fun _ => false) = true := by
      cases hh : H (fun _ => false)
      · rw [hh] at h0; exact Bool.noConfusion h0
      · rfl
    have hH1 : H (fun _ => true) = true := hHmono _ _ (fun _ _ => rfl) hH0
    have h1 := hw (fun _ => true)
    rw [hwo, hHnot go hnot, hH1, targetFun_true S hSne] at h1
    exact Bool.noConfusion h1
  have hgo_op : (C.gates[go.val]).op = GateOp.and ∨ (C.gates[go.val]).op = GateOp.or :=
    op_and_or_of_ne_not C hfan go.val go.isLt (by simpa using hgo_ne_not)
  have hgo_len : (C.gates[go.val]).inputs.length ≤ 2 := (hfan _ (List.getElem_mem go.isLt)).2
  have hinputs2 : ∃ a b : ℕ, (C.gates[go.val]).inputs = [a, b] ∧ a < w ∧ b < w := by
    rcases hl : (C.gates[go.val]).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · rcases hgo_op with hop | hop
      · have h0 := hw (fun _ => false)
        rw [hwo, gate_val C _ go.val go.isLt, hop, hl] at h0
        rw [targetFun_false] at h0
        simp [GateOp.eval] at h0
      · have h1 := hw (fun _ => true)
        rw [hwo, gate_val C _ go.val go.isLt, hop, hl] at h1
        rw [targetFun_true S hSne] at h1
        simp [GateOp.eval] at h1
    · by_cases ha : a < w
      · exfalso
        apply hmin a ha
        intro x
        have hx := hw x
        rw [hwo, gate_val C x go.val go.isLt, hl] at hx
        rw [← hwo] at hx
        rcases hgo_op with hop | hop <;> simp [hop, GateOp.eval, ha] at hx <;> exact hx
      · exfalso
        have h1 := hw (fun _ => true)
        rw [hwo, gate_val C _ go.val go.isLt, hl] at h1
        rw [← hwo, targetFun_true S hSne] at h1
        rcases hgo_op with hop | hop <;> simp [hop, GateOp.eval, ha] at h1
    · refine ⟨a, b, rfl, ?_, ?_⟩
      · by_contra ha
        rcases hgo_op with hop | hop
        · have h1 := hw (fun _ => true)
          rw [hwo, gate_val C _ go.val go.isLt, hl] at h1
          rw [← hwo, targetFun_true S hSne] at h1
          simp [hop, GateOp.eval, ha] at h1
        · by_cases hb : b < w
          · apply hmin b hb
            intro x
            have hx := hw x
            rw [hwo, gate_val C x go.val go.isLt, hl] at hx
            rw [← hwo] at hx
            simp [hop, GateOp.eval, ha, hb] at hx
            exact hx
          · have h1 := hw (fun _ => true)
            rw [hwo, gate_val C _ go.val go.isLt, hl] at h1
            rw [← hwo, targetFun_true S hSne] at h1
            simp [hop, GateOp.eval, ha, hb] at h1
      · by_contra hb
        rcases hgo_op with hop | hop
        · have h1 := hw (fun _ => true)
          rw [hwo, gate_val C _ go.val go.isLt, hl] at h1
          rw [← hwo, targetFun_true S hSne] at h1
          simp [hop, GateOp.eval, hb] at h1
        · by_cases ha : a < w
          · apply hmin a ha
            intro x
            have hx := hw x
            rw [hwo, gate_val C x go.val go.isLt, hl] at hx
            rw [← hwo] at hx
            simp [hop, GateOp.eval, ha, hb] at hx
            exact hx
          · have h1 := hw (fun _ => true)
            rw [hwo, gate_val C _ go.val go.isLt, hl] at h1
            rw [← hwo, targetFun_true S hSne] at h1
            simp [hop, GateOp.eval, ha, hb] at h1
    · rw [hl] at hgo_len
      simp at hgo_len
  obtain ⟨a, b, hab, haw, hbw⟩ := hinputs2
  rcases hgo_op with hop | hop
  · have hand : ∀ x : Fin 9 → Bool, targetFun S x = (val C x a && val C x b) := by
      intro x
      have hx := hw x
      rw [hwo, gate_val C x go.val go.isLt, hop, hab] at hx
      rw [← hwo] at hx
      simp only [List.map_cons, List.map_nil, ite_eq_left haw, ite_eq_left hbw, GateOp.eval,
        List.all_cons, List.all_nil, id_eq, Bool.and_true] at hx
      exact hx.symm
    have hzero : val C (outsideVec S) a = false ∨ val C (outsideVec S) b = false := by
      have hz := hand (outsideVec S)
      rw [targetFun_outside] at hz
      cases ha0 : val C (outsideVec S) a <;> cases hb0 : val C (outsideVec S) b <;> simp [ha0, hb0] at hz ⊢
    have hpick : ∃ u : ℕ, u < w ∧ val C (outsideVec S) u = false ∧
        ∀ x : Fin 9 → Bool, targetFun S x = true → val C x u = true := by
      rcases hzero with ha0 | hb0
      · refine ⟨a, haw, ha0, fun x hx => ?_⟩
        rw [hand x] at hx
        exact (Bool.and_eq_true _ _ |>.mp hx).1
      · refine ⟨b, hbw, hb0, fun x hx => ?_⟩
        rw [hand x] at hx
        exact (Bool.and_eq_true _ _ |>.mp hx).2
    obtain ⟨u, huw, huz, hut⟩ := hpick
    have hSsub : S ⊆ supp C u := by
      intro q hq
      rw [mem_supp]
      apply hut (single q)
      rw [targetFun_single, decide_eq_true_eq]
      exact hq
    have huge : 9 ≤ u := ge_nine_of_supp_card C u (by
      have := Finset.card_le_card hSsub
      omega)
    let gu : Fin C.gates.length := ⟨u - 9, by omega⟩
    have hgu_eq : 9 + gu.val = u := by dsimp [gu]; omega
    have hHz : H (outsideVec S) = true := by
      by_contra hHzf
      have hHz0 : H (outsideVec S) = false := by
        cases hh : H (outsideVec S)
        · rfl
        · exact absurd hh hHzf
      apply hmin u huw
      intro x
      cases htx : targetFun S x with
      | true => exact hut x htx
      | false =>
        have hxz : ∀ q, x q = true → outsideVec S q = true := by
          intro q hxq
          simp only [outsideVec, decide_eq_true_eq]
          intro hqS
          have : targetFun S x = true := by
            simp only [targetFun, decide_eq_true_eq]
            exact ⟨q, hqS, hxq⟩
          rw [htx] at this
          exact Bool.noConfusion this
        have hHx0 : H x = false := by
          cases hh : H x
          · rfl
          · have := hHmono x (outsideVec S) hxz hh
            rw [hHz0] at this
            exact Bool.noConfusion this
        cases huv : val C x u with
        | false => rfl
        | true =>
          have := hHval x (outsideVec S) hxz (by rw [hHx0, hHz0]) u huv
          rw [huz] at this
          exact Bool.noConfusion this
    have hgu_ne_not : (C.gates.get gu).op ≠ GateOp.not := by
      intro hnot
      have hH1 : H (fun _ => true) = true := hHmono (outsideVec S) (fun _ => true) (fun _ _ => rfl) hHz
      have hv1 : val C (fun _ => true) u = true := hut (fun _ => true) (targetFun_true S hSne)
      rw [← hgu_eq, hHnot gu hnot, hH1] at hv1
      exact Bool.noConfusion hv1
    exact ⟨go, gu, hwo, hgo_ne_not, hgu_ne_not, by omega, Or.inr ⟨by rwa [hgu_eq], fun x hx => by rw [hgu_eq]; exact hut x hx⟩⟩
  · have hor : ∀ x : Fin 9 → Bool, targetFun S x = (val C x a || val C x b) := by
      intro x
      have hx := hw x
      rw [hwo, gate_val C x go.val go.isLt, hop, hab] at hx
      rw [← hwo] at hx
      simp only [List.map_cons, List.map_nil, ite_eq_left haw, ite_eq_left hbw, GateOp.eval,
        List.any_cons, List.any_nil, id_eq, Bool.or_false] at hx
      exact hx.symm
    have hsub_a : supp C a ⊆ S := by
      intro q hq
      rw [mem_supp] at hq
      have := hor (single q)
      rw [hq, Bool.true_or, targetFun_single] at this
      exact of_decide_eq_true this
    have hsub_b : supp C b ⊆ S := by
      intro q hq
      rw [mem_supp] at hq
      have := hor (single q)
      rw [hq, Bool.or_true, targetFun_single] at this
      exact of_decide_eq_true this
    have hcov : S ⊆ supp C a ∪ supp C b := by
      intro q hq
      have h1 := hor (single q)
      rw [targetFun_single, decide_eq_true_eq.mpr hq] at h1
      rcases Bool.or_eq_true _ _ |>.mp h1.symm with ha1 | hb1
      · exact Finset.mem_union_left _ ((mem_supp C a q).mpr ha1)
      · exact Finset.mem_union_right _ ((mem_supp C b q).mpr hb1)
    have hsum : 3 ≤ (supp C a).card + (supp C b).card := by
      calc 3 = S.card := hScard.symm
        _ ≤ (supp C a ∪ supp C b).card := Finset.card_le_card hcov
        _ ≤ (supp C a).card + (supp C b).card := Finset.card_union_le _ _
    have h0_ab : val C (fun _ => false) a = false ∧ val C (fun _ => false) b = false := by
      have h0 := hor (fun _ => false)
      rw [targetFun_false] at h0
      cases ha0 : val C (fun _ => false) a <;> cases hb0 : val C (fun _ => false) b <;> simp [ha0, hb0] at h0 ⊢
    have hpick : ∃ u : ℕ, u < w ∧ supp C u ⊆ S ∧ 2 ≤ (supp C u).card ∧ val C (fun _ => false) u = false := by
      by_cases hca : 2 ≤ (supp C a).card
      · exact ⟨a, haw, hsub_a, hca, h0_ab.1⟩
      · exact ⟨b, hbw, hsub_b, by omega, h0_ab.2⟩
    obtain ⟨u, huw, husub, hucard, hu0⟩ := hpick
    have huge : 9 ≤ u := ge_nine_of_supp_card C u hucard
    let gu : Fin C.gates.length := ⟨u - 9, by omega⟩
    have hgu_eq : 9 + gu.val = u := by dsimp [gu]; omega
    have hgu_ne_not : (C.gates.get gu).op ≠ GateOp.not := by
      intro hnot
      rw [← hgu_eq, hHnot gu hnot] at hu0
      have hH0 : H (fun _ => false) = true := by
        cases hh : H (fun _ => false)
        · rw [hh] at hu0; exact Bool.noConfusion hu0
        · rfl
      have hempty : supp C u = ∅ := by
        ext q
        simp only [mem_supp, Finset.notMem_empty, iff_false]
        have hHq : H (single q) = true := hHmono _ _ (fun _ h => Bool.noConfusion h) hH0
        rw [← hgu_eq, hHnot gu hnot, hHq]
        decide
      rw [hempty] at hucard
      simp at hucard
    exact ⟨go, gu, hwo, hgo_ne_not, hgu_ne_not, by omega, Or.inl ⟨by rwa [hgu_eq], by rwa [hgu_eq]⟩⟩

private theorem main : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, ∃ o : Fin 3 → Fin 3 → ℕ,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    (∀ i j : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not →
      (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) ∧
    C.size ≤ 18 ∧
    (C.size = 18 → ∃ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
    ∀ x : Fin 9 → Bool, ∀ a b : Fin 3,
      ((C.wires (List.ofFn x)).getD (o a b) false = true ↔
        ∃ c : Fin 3, ∃ k : Fin 9, (k : ℕ) = 3 * (c : ℕ) + ((a * c + b : Fin 3) : ℕ) ∧ x k = true)) := by
  classical
  rintro ⟨C, o, hfan, huniq, hsz, h18, hcomp⟩
  obtain ⟨H, hHmono, hHval, hHnot⟩ := exists_H C hfan huniq
  have hex_w : ∀ p : Fin 3 × Fin 3, ∃ w : ℕ, ∀ x : Fin 9 → Bool, val C x w = targetFun (lineSet p) x := by
    intro p
    refine ⟨o p.1 p.2, fun x => ?_⟩
    apply Bool.eq_iff_iff.mpr
    rw [targetFun, decide_eq_true_eq, ← lineSet_spec]
    exact hcomp x p.1 p.2
  have hdata : ∀ p : Fin 3 × Fin 3,
      ∃ (go gu : Fin C.gates.length),
        (∀ x : Fin 9 → Bool, val C x (9 + go.val) = targetFun (lineSet p) x) ∧
        (C.gates.get go).op ≠ GateOp.not ∧
        (C.gates.get gu).op ≠ GateOp.not ∧
        gu.val < go.val ∧
        ((supp C (9 + gu.val) ⊆ lineSet p ∧ 2 ≤ (supp C (9 + gu.val)).card) ∨
          (val C (outsideVec (lineSet p)) (9 + gu.val) = false ∧
            ∀ x : Fin 9 → Bool, targetFun (lineSet p) x = true → val C x (9 + gu.val) = true)) := by
    intro p
    let w := Nat.find (hex_w p)
    have hw : ∀ x : Fin 9 → Bool, val C x w = targetFun (lineSet p) x := Nat.find_spec (hex_w p)
    have hmin : ∀ w' : ℕ, w' < w → ¬ (∀ x : Fin 9 → Bool, val C x w' = targetFun (lineSet p) x) :=
      fun w' hlt => Nat.find_min (hex_w p) hlt
    obtain ⟨go, gu, hwo, hgo_ne, hgu_ne, hlt, hprop⟩ :=
      earliest_gate_and_helper C hfan H hHmono hHval hHnot (lineSet p) (lineSet_card p) w hw hmin
    exact ⟨go, gu, fun x => by rw [← hwo]; exact hw x, hgo_ne, hgu_ne, hlt, hprop⟩
  choose go gu hgo_ev hgo_ne hgu_ne hgu_lt hgu_prop using hdata
  let φ : (Fin 3 × Fin 3) ⊕ (Fin 3 × Fin 3) → Fin C.gates.length := Sum.elim go gu
  have hφ_ne : ∀ z, (C.gates.get (φ z)).op ≠ GateOp.not := by
    rintro (p | p)
    · exact hgo_ne p
    · exact hgu_ne p
  have hgo_inj : Function.Injective go := by
    intro p q hpq
    by_contra hne
    obtain ⟨k, hkq, hkp⟩ := lineSet_sdiff p q hne
    have h1 := hgo_ev p (single k)
    have h2 := hgo_ev q (single k)
    rw [hpq, h2, targetFun_single, targetFun_single] at h1
    simp [hkq, hkp] at h1
  have hgu_ne_go : ∀ p q : Fin 3 × Fin 3, gu p ≠ go q := by
    intro p q heq
    by_cases hpq : p = q
    · subst hpq
      have := hgu_lt p
      rw [heq] at this
      exact lt_irrefl _ this
    · rcases hgu_prop p with ⟨hsub, hcard⟩ | ⟨hout, _⟩
      · have hsq : supp C (9 + (go q).val) = lineSet q := by
          ext k
          rw [mem_supp, hgo_ev q, targetFun_single, decide_eq_true_eq]
        rw [heq, hsq] at hsub
        have hinter : lineSet q ⊆ lineSet p ∩ lineSet q :=
          Finset.subset_inter hsub (Finset.Subset.refl _)
        have h1 := Finset.card_le_card hinter
        have h2 := lineSet_inter p q hpq
        have h3 := lineSet_card q
        omega
      · obtain ⟨k, hkq, hkp⟩ := lineSet_sdiff p q hpq
        have h1 := hgo_ev q (outsideVec (lineSet p))
        rw [← heq, hout] at h1
        have h2 : targetFun (lineSet q) (outsideVec (lineSet p)) = true := by
          simp only [targetFun, outsideVec, decide_eq_true_eq]
          exact ⟨k, hkq, hkp⟩
        rw [h2] at h1
        exact Bool.noConfusion h1
  have hgu_inj : Function.Injective gu := by
    intro p q hpq
    by_contra hne
    rcases hgu_prop p with ⟨hsubp, hcardp⟩ | ⟨houtp, htruep⟩
    · rcases hgu_prop q with ⟨hsubq, _⟩ | ⟨_, htrueq⟩
      · have hinter : supp C (9 + (gu p).val) ⊆ lineSet p ∩ lineSet q :=
          Finset.subset_inter hsubp (hpq ▸ hsubq)
        have h1 := Finset.card_le_card hinter
        have h2 := lineSet_inter p q hne
        omega
      · have hsq : lineSet q ⊆ supp C (9 + (gu q).val) := by
          intro k hk
          rw [mem_supp]
          apply htrueq (single k)
          rw [targetFun_single, decide_eq_true_eq]
          exact hk
        have hinter : lineSet q ⊆ lineSet p ∩ lineSet q :=
          Finset.subset_inter (hsq.trans (hpq ▸ hsubp)) (Finset.Subset.refl _)
        have h1 := Finset.card_le_card hinter
        have h2 := lineSet_inter p q hne
        have h3 := lineSet_card q
        omega
    · rcases hgu_prop q with ⟨hsubq, _⟩ | ⟨_, htrueq⟩
      · have hsp : lineSet p ⊆ supp C (9 + (gu p).val) := by
          intro k hk
          rw [mem_supp]
          apply htruep (single k)
          rw [targetFun_single, decide_eq_true_eq]
          exact hk
        have hinter : lineSet p ⊆ lineSet p ∩ lineSet q :=
          Finset.subset_inter (Finset.Subset.refl _) (hsp.trans (hpq ▸ hsubq))
        have h1 := Finset.card_le_card hinter
        have h2 := lineSet_inter p q hne
        have h3 := lineSet_card p
        omega
      · obtain ⟨k, hkq, hkp⟩ := lineSet_sdiff p q hne
        have ht : targetFun (lineSet q) (outsideVec (lineSet p)) = true := by
          simp only [targetFun, outsideVec, decide_eq_true_eq]
          exact ⟨k, hkq, hkp⟩
        have h1 := htrueq (outsideVec (lineSet p)) ht
        rw [← hpq, houtp] at h1
        exact Bool.noConfusion h1
  have hφ_inj : Function.Injective φ := by
    rintro (p | p) (q | q) heq
    · exact congrArg Sum.inl (hgo_inj heq)
    · exact absurd heq.symm (hgu_ne_go q p)
    · exact absurd heq (hgu_ne_go p q)
    · exact congrArg Sum.inr (hgu_inj heq)
  let good : Finset (Fin C.gates.length) :=
    Finset.univ.filter fun j => (C.gates.get j).op ≠ GateOp.not
  have hcard_good : 18 ≤ good.card := by
    have himg : (Finset.univ : Finset ((Fin 3 × Fin 3) ⊕ (Fin 3 × Fin 3))).image φ ⊆ good := by
      intro j hj
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hφ_ne z⟩
    have hle := Finset.card_le_card himg
    rw [Finset.card_image_of_injective _ hφ_inj, Finset.card_univ] at hle
    simpa using hle
  have hgood_le : good.card ≤ C.size := by
    calc good.card ≤ (Finset.univ : Finset (Fin C.gates.length)).card := Finset.card_filter_le _ _
      _ = C.size := by simp [Circuit.size]
  have hsz18 : C.size = 18 := by omega
  obtain ⟨jnot, hjnot⟩ := h18 hsz18
  have hnot_mem : jnot ∉ good := by
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    exact hjnot
  have hlt : good.card < (Finset.univ : Finset (Fin C.gates.length)).card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ _, fun h => hnot_mem (h.symm ▸ Finset.mem_univ jnot)⟩)
  simp only [Finset.card_univ, Fintype.card_fin] at hlt
  change good.card < C.size at hlt
  omega

end PEqualNP.Outside.L_meta_907

theorem PEqualNP.Outside.L_meta_907 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, ∃ o : Fin 3 → Fin 3 → ℕ,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    (∀ i j : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not →
      (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) ∧
    C.size ≤ 18 ∧
    (C.size = 18 → ∃ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
    ∀ x : Fin 9 → Bool, ∀ a b : Fin 3,
      ((C.wires (List.ofFn x)).getD (o a b) false = true ↔
        ∃ c : Fin 3, ∃ k : Fin 9, (k : ℕ) = 3 * (c : ℕ) + ((a * c + b : Fin 3) : ℕ) ∧ x k = true)) := by
  exact PEqualNP.Outside.L_meta_907.main
