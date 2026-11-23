import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_738_aux

open PEqualNP.CircuitLowerBounds

private def isAndOp : GateOp → Bool
  | GateOp.and => true
  | _ => false

private lemma isAndOp_eq_true (op : GateOp) : isAndOp op = true ↔ op = GateOp.and := by
  cases op <;> simp [isAndOp]

private lemma isAndOp_eq_false (op : GateOp) : isAndOp op = false ↔ op ≠ GateOp.and := by
  cases op <;> simp [isAndOp]

private def runWires (gs : List Gate) (inp : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) inp

private lemma runWires_eq (C : Circuit) (inp : List Bool) :
    C.wires inp = runWires C.gates inp := rfl

private lemma runWires_length (gs : List Gate) (inp : List Bool) :
    (runWires gs inp).length = inp.length + gs.length := by
  unfold runWires
  induction gs generalizing inp with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

private lemma runWires_append (gs1 gs2 : List Gate) (inp : List Bool) :
    runWires (gs1 ++ gs2) inp = runWires gs2 (runWires gs1 inp) := by
  simp [runWires, List.foldl_append]

private lemma runWires_getD_lt (gs : List Gate) (inp : List Bool) {i : ℕ} (hi : i < inp.length) :
    (runWires gs inp).getD i false = inp.getD i false := by
  unfold runWires
  induction gs generalizing inp with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (inp ++ [g.op.eval (g.inputs.map fun k => inp.getD k false)]).length := by
      simp; omega
    rw [ih _ hi', List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hi,
      List.getElem_append_left hi]

private lemma runWires_getD_ge (gs : List Gate) (inp : List Bool) {i : ℕ}
    (hi : inp.length + gs.length ≤ i) :
    (runWires gs inp).getD i false = false := by
  rw [List.getD_eq_default]
  rw [runWires_length]
  exact hi

private lemma runWires_snoc_last (gs : List Gate) (g : Gate) (inp : List Bool) :
    (runWires (gs ++ [g]) inp).getD (inp.length + gs.length) false =
      g.op.eval (g.inputs.map fun a => (runWires gs inp).getD a false) := by
  rw [runWires_append]
  set w := runWires gs inp
  have hw : w.length = inp.length + gs.length := runWires_length gs inp
  have hstep : runWires [g] w = w ++ [g.op.eval (g.inputs.map fun a => w.getD a false)] := rfl
  rw [hstep, ← hw, List.getD_eq_getElem _ _ (by simp)]
  simp

private lemma runWires_getD_gate (gs : List Gate) (inp : List Bool) (j : Fin gs.length) :
    (runWires gs inp).getD (inp.length + j.val) false =
      (gs.get j).op.eval
        ((gs.get j).inputs.map fun a =>
          if a < inp.length + j.val then (runWires gs inp).getD a false else false) := by
  have hj := j.isLt
  have hsplit : gs = (gs.take j.val ++ [gs.get j]) ++ gs.drop (j.val + 1) := by
    conv_lhs => rw [← List.take_append_drop j.val gs]
    rw [List.drop_eq_getElem_cons hj, List.append_assoc]
    simp
  have htake_len : (gs.take j.val).length = j.val := by rw [List.length_take]; omega
  have hlt : inp.length + j.val < (runWires (gs.take j.val ++ [gs.get j]) inp).length := by
    rw [runWires_length, List.length_append, htake_len]; simp
  have hres : (runWires gs inp).getD (inp.length + j.val) false =
      (runWires (gs.take j.val ++ [gs.get j]) inp).getD (inp.length + j.val) false := by
    have h1 := congrArg (fun l => (runWires l inp).getD (inp.length + j.val) false) hsplit
    rw [h1, runWires_append]
    exact runWires_getD_lt _ _ hlt
  rw [hres]
  have hsnoc := runWires_snoc_last (gs.take j.val) (gs.get j) inp
  rw [htake_len] at hsnoc
  rw [hsnoc]
  congr 1
  apply List.map_congr_left
  intro a _
  by_cases ha : a < inp.length + j.val
  · simp only [ha, ite_true]
    have ha_w : a < (runWires (gs.take j.val) inp).length := by
      rw [runWires_length, htake_len]; exact ha
    have hsplit2 : gs = gs.take j.val ++ gs.drop j.val := (List.take_append_drop j.val gs).symm
    have h2 := congrArg (fun l => (runWires l inp).getD a false) hsplit2
    rw [h2, runWires_append, runWires_getD_lt _ _ ha_w]
  · simp only [ha, ite_false]
    exact List.getD_eq_default _ _ (by rw [runWires_length, htake_len]; omega)

private def runDegs (gs : List Gate) (d0 : List ℕ) : List ℕ :=
  gs.foldl (fun d g => d ++ [g.lineDegree d]) d0

private lemma runDegs_length (gs : List Gate) (d0 : List ℕ) :
    (runDegs gs d0).length = d0.length + gs.length := by
  unfold runDegs
  induction gs generalizing d0 with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

private lemma runDegs_append (gs1 gs2 : List Gate) (d0 : List ℕ) :
    runDegs (gs1 ++ gs2) d0 = runDegs gs2 (runDegs gs1 d0) := by
  simp [runDegs, List.foldl_append]

private lemma runDegs_getD_lt (gs : List Gate) (d0 : List ℕ) {i : ℕ} (hi : i < d0.length) :
    (runDegs gs d0).getD i 0 = d0.getD i 0 := by
  unfold runDegs
  induction gs generalizing d0 with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (d0 ++ [g.lineDegree d0]).length := by simp; omega
    rw [ih _ hi', List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hi,
      List.getElem_append_left hi]

private lemma runDegs_getD_ge (gs : List Gate) (d0 : List ℕ) {i : ℕ}
    (hi : d0.length + gs.length ≤ i) :
    (runDegs gs d0).getD i 0 = 0 := by
  rw [List.getD_eq_default]
  rw [runDegs_length]
  exact hi

private lemma gate_lineDegree_eq (g : Gate) (d : List ℕ) :
    g.lineDegree d =
      if isAndOp g.op then (g.inputs.map fun i => d.getD i 0).sum
      else (g.inputs.map fun i => d.getD i 0).foldr max 0 := by
  unfold Gate.lineDegree
  cases h : g.op <;> simp [isAndOp]

private lemma runDegs_snoc_last (gs : List Gate) (g : Gate) (d0 : List ℕ) :
    (runDegs (gs ++ [g]) d0).getD (d0.length + gs.length) 0 =
      g.lineDegree (runDegs gs d0) := by
  rw [runDegs_append]
  set d := runDegs gs d0
  have hd : d.length = d0.length + gs.length := runDegs_length gs d0
  have hstep : runDegs [g] d = d ++ [g.lineDegree d] := rfl
  rw [hstep, ← hd, List.getD_eq_getElem _ _ (by simp)]
  simp

private lemma runDegs_getD_gate (gs : List Gate) (d0 : List ℕ) (j : Fin gs.length) :
    (runDegs gs d0).getD (d0.length + j.val) 0 =
      if isAndOp (gs.get j).op then
        ((gs.get j).inputs.map fun a =>
          if a < d0.length + j.val then (runDegs gs d0).getD a 0 else 0).sum
      else
        ((gs.get j).inputs.map fun a =>
          if a < d0.length + j.val then (runDegs gs d0).getD a 0 else 0).foldr max 0 := by
  have hj := j.isLt
  have hsplit : gs = (gs.take j.val ++ [gs.get j]) ++ gs.drop (j.val + 1) := by
    conv_lhs => rw [← List.take_append_drop j.val gs]
    rw [List.drop_eq_getElem_cons hj, List.append_assoc]
    simp
  have htake_len : (gs.take j.val).length = j.val := by rw [List.length_take]; omega
  have hlt : d0.length + j.val < (runDegs (gs.take j.val ++ [gs.get j]) d0).length := by
    rw [runDegs_length, List.length_append, htake_len]; simp
  have hres : (runDegs gs d0).getD (d0.length + j.val) 0 =
      (runDegs (gs.take j.val ++ [gs.get j]) d0).getD (d0.length + j.val) 0 := by
    have h1 := congrArg (fun l => (runDegs l d0).getD (d0.length + j.val) 0) hsplit
    rw [h1, runDegs_append]
    exact runDegs_getD_lt _ _ hlt
  rw [hres]
  have hsnoc := runDegs_snoc_last (gs.take j.val) (gs.get j) d0
  rw [htake_len] at hsnoc
  rw [hsnoc, gate_lineDegree_eq]
  have hmap : ((gs.get j).inputs.map fun a => (runDegs (gs.take j.val) d0).getD a 0) =
      ((gs.get j).inputs.map fun a =>
        if a < d0.length + j.val then (runDegs gs d0).getD a 0 else 0) := by
    apply List.map_congr_left
    intro a _
    by_cases ha : a < d0.length + j.val
    · simp only [ha, ite_true]
      have ha_d : a < (runDegs (gs.take j.val) d0).length := by
        rw [runDegs_length, htake_len]; exact ha
      have hsplit2 : gs = gs.take j.val ++ gs.drop j.val := (List.take_append_drop j.val gs).symm
      have h2 := congrArg (fun l => (runDegs l d0).getD a 0) hsplit2
      rw [h2, runDegs_append, runDegs_getD_lt _ _ ha_d]
    · simp only [ha, ite_false]
      exact List.getD_eq_default _ _ (by rw [runDegs_length, htake_len]; omega)
  rw [hmap]

private lemma mem_le_foldr_max {l : List ℕ} {a : ℕ} (ha : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp ha with rfl | hxs
    · exact le_max_left _ _
    · exact le_trans (ih hxs) (le_max_right _ _)

private lemma mem_le_sum {l : List ℕ} {a : ℕ} (ha : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.mp ha with rfl | hxs
    · omega
    · have := ih hxs; omega

private def deg (P L : ℕ) (C : Circuit) (v : ℕ) : ℕ :=
  (C.lineDegrees (P + L) (Finset.Ico P (P + L))).getD v 0

private def degInit (P L : ℕ) : List ℕ :=
  (List.range (P + L)).map fun i => if i ∈ Finset.Ico P (P + L) then 1 else 0

private lemma deg_eq_runDegs (P L : ℕ) (C : Circuit) (v : ℕ) :
    deg P L C v = (runDegs C.gates (degInit P L)).getD v 0 := rfl

private lemma degInit_length (P L : ℕ) : (degInit P L).length = P + L := by
  simp [degInit]

private lemma deg_lt_P (P L : ℕ) (C : Circuit) {v : ℕ} (hv : v < P) :
    deg P L C v = 0 := by
  rw [deg_eq_runDegs, runDegs_getD_lt C.gates (degInit P L) (by rw [degInit_length]; omega)]
  have hlt : v < (degInit P L).length := by rw [degInit_length]; omega
  rw [List.getD_eq_getElem _ _ hlt]
  simp [degInit, hv]

private lemma deg_line (P L : ℕ) (C : Circuit) (w : Fin L) :
    deg P L C (P + w.val) = 1 := by
  have hw := w.isLt
  rw [deg_eq_runDegs, runDegs_getD_lt C.gates (degInit P L) (by rw [degInit_length]; omega)]
  have hlt : P + w.val < (degInit P L).length := by rw [degInit_length]; omega
  rw [List.getD_eq_getElem _ _ hlt]
  simp [degInit, hw]

private lemma deg_ge (P L : ℕ) (C : Circuit) {v : ℕ} (hv : P + L + C.gates.length ≤ v) :
    deg P L C v = 0 := by
  rw [deg_eq_runDegs]
  exact runDegs_getD_ge C.gates (degInit P L) (by rw [degInit_length]; exact hv)

private lemma deg_gate (P L : ℕ) (C : Circuit) (j : Fin C.gates.length) :
    deg P L C (P + L + j.val) =
      if isAndOp (C.gates.get j).op then
        ((C.gates.get j).inputs.map fun a =>
          if a < P + L + j.val then deg P L C a else 0).sum
      else
        ((C.gates.get j).inputs.map fun a =>
          if a < P + L + j.val then deg P L C a else 0).foldr max 0 := by
  have h := runDegs_getD_gate C.gates (degInit P L) j
  rw [degInit_length] at h
  exact h

private def Step (P L : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ ∃ i : Fin C.gates.length, b = P + L + i.val ∧ a ∈ (C.gates.get i).inputs

private def Reach (P L : ℕ) (C : Circuit) : ℕ → ℕ → Prop :=
  Relation.ReflTransGen (Step P L C)

private lemma le_of_reach {P L : ℕ} {C : Circuit} {a b : ℕ} (h : Reach P L C a b) : a ≤ b := by
  induction h with
  | refl => exact le_refl _
  | tail _ hstep ih => exact le_trans ih (le_of_lt hstep.1)

private lemma deg_mono_step {P L : ℕ} {C : Circuit} {a b : ℕ} (h : Step P L C a b) :
    deg P L C a ≤ deg P L C b := by
  rcases h with ⟨hlt, i, rfl, hmem⟩
  rw [deg_gate]
  have ha : deg P L C a ∈ (C.gates.get i).inputs.map
      (fun x => if x < P + L + i.val then deg P L C x else 0) := by
    refine List.mem_map.mpr ⟨a, hmem, by simp [hlt]⟩
  split_ifs
  · exact mem_le_sum ha
  · exact mem_le_foldr_max ha

private lemma deg_mono_reach {P L : ℕ} {C : Circuit} {a b : ℕ} (h : Reach P L C a b) :
    deg P L C a ≤ deg P L C b := by
  induction h with
  | refl => exact le_refl _
  | tail _ hstep ih => exact le_trans ih (deg_mono_step hstep)

private lemma deg_wire_le_one {P L : ℕ} {C : Circuit}
    (hDeg : HasLineDegree (P + L) (Finset.Ico P (P + L)) C 1)
    (hAllReach : ∀ j : Fin C.gates.length, Reach P L C (P + L + j.val) C.output)
    (v : ℕ) : deg P L C v ≤ 1 := by
  by_cases h1 : v < P
  · rw [deg_lt_P P L C h1]; omega
  · by_cases h2 : v < P + L
    · have hw : v = P + (v - P) := by omega
      rw [hw, deg_line P L C ⟨v - P, by omega⟩]
    · by_cases h3 : v < P + L + C.gates.length
      · have hj : v = P + L + (v - (P + L)) := by omega
        rw [hj]
        exact le_trans (deg_mono_reach (hAllReach ⟨v - (P + L), by omega⟩)) hDeg
      · rw [deg_ge P L C (by omega)]; omega

private def val (C : Circuit) {P L : ℕ} (x : Fin P → Bool) (y : Fin L → Bool) (v : ℕ) : Bool :=
  (C.wires (List.ofFn x ++ List.ofFn y)).getD v false

private def val0 (C : Circuit) (L : ℕ) {P : ℕ} (x : Fin P → Bool) (v : ℕ) : Bool :=
  val C x (fun _ : Fin L => false) v

private lemma val_lt_P (C : Circuit) {P L : ℕ} (x : Fin P → Bool) (y : Fin L → Bool)
    (u : Fin P) : val C x y u.val = x u := by
  have hu := u.isLt
  unfold val
  rw [runWires_eq, runWires_getD_lt C.gates _ (by simp; omega)]
  have hlt : u.val < (List.ofFn x ++ List.ofFn y).length := by simp; omega
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_append_left (by simp)]
  simp

private lemma val_line (C : Circuit) {P L : ℕ} (x : Fin P → Bool) (y : Fin L → Bool)
    (w : Fin L) : val C x y (P + w.val) = y w := by
  have hw := w.isLt
  unfold val
  rw [runWires_eq, runWires_getD_lt C.gates _ (by simp)]
  have hlt : P + w.val < (List.ofFn x ++ List.ofFn y).length := by simp
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_append_right (by simp)]
  simp

private lemma val_gate (C : Circuit) {P L : ℕ} (x : Fin P → Bool) (y : Fin L → Bool)
    (j : Fin C.gates.length) :
    val C x y (P + L + j.val) =
      (C.gates.get j).op.eval
        ((C.gates.get j).inputs.map fun a =>
          if a < P + L + j.val then val C x y a else false) := by
  unfold val
  have hlen : (List.ofFn x ++ List.ofFn y).length = P + L := by simp
  have h := runWires_getD_gate C.gates (List.ofFn x ++ List.ofFn y) j
  rw [hlen] at h
  exact h

private lemma val_ge (C : Circuit) {P L : ℕ} (x : Fin P → Bool) (y : Fin L → Bool)
    {v : ℕ} (hv : P + L + C.gates.length ≤ v) : val C x y v = false := by
  unfold val
  rw [runWires_eq]
  exact runWires_getD_ge C.gates _ (by simp; exact hv)

private lemma val_mono {P L : ℕ} {C : Circuit} (hMono : IsMonotoneCircuit C)
    (x : Fin P → Bool) (y : Fin L → Bool) :
    ∀ v : ℕ, val0 C L x v = true → val C x y v = true := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro h0
    by_cases h1 : v < P
    · have hu : v = (⟨v, h1⟩ : Fin P).val := rfl
      rw [hu, val0, val_lt_P] at h0
      rw [hu, val_lt_P]
      exact h0
    · by_cases h2 : v < P + L
      · let w : Fin L := ⟨v - P, by omega⟩
        have hw : v = P + w.val := by dsimp [w]; omega
        rw [hw] at h0
        simp [val0, val_line] at h0
      · by_cases h3 : v < P + L + C.gates.length
        · let j : Fin C.gates.length := ⟨v - (P + L), by omega⟩
          have hj : v = P + L + j.val := by simp [j]; omega
          rw [hj] at h0 ⊢
          rw [val0, val_gate] at h0
          rw [val_gate]
          rcases hMono (C.gates.get j) (List.get_mem _ _) with hop | hop
          · rw [hop] at h0 ⊢
            simp only [GateOp.eval, List.all_eq_true, id_eq, List.mem_map] at h0 ⊢
            rintro _ ⟨a, ha, rfl⟩
            have ha0 := h0 _ ⟨a, ha, rfl⟩
            by_cases hlt : a < P + L + j.val
            · simp only [hlt, ite_true] at ha0 ⊢
              exact ih a (by omega) ha0
            · simp only [hlt, ite_false] at ha0
              simp at ha0
          · rw [hop] at h0 ⊢
            simp only [GateOp.eval, List.any_eq_true, id_eq, List.mem_map] at h0 ⊢
            obtain ⟨_, ⟨a, ha, rfl⟩, ha0⟩ := h0
            by_cases hlt : a < P + L + j.val
            · simp only [hlt, ite_true] at ha0
              exact ⟨true, ⟨a, ha, by simp only [hlt, ite_true]; exact ih a (by omega) ha0⟩, rfl⟩
            · simp only [hlt, ite_false] at ha0
              simp at ha0
        · rw [val0, val_ge C _ _ (by omega)] at h0
          simp at h0

private lemma val_indep_of_deg_zero {P L : ℕ} {C : Circuit}
    (x : Fin P → Bool) (y : Fin L → Bool) :
    ∀ v : ℕ, deg P L C v = 0 → val C x y v = val0 C L x v := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hdeg
    by_cases h1 : v < P
    · have hu : v = (⟨v, h1⟩ : Fin P).val := rfl
      rw [hu, val0, val_lt_P, val_lt_P]
    · by_cases h2 : v < P + L
      · let w : Fin L := ⟨v - P, by omega⟩
        have hw : v = P + w.val := by dsimp [w]; omega
        rw [hw, deg_line] at hdeg
        omega
      · by_cases h3 : v < P + L + C.gates.length
        · let j : Fin C.gates.length := ⟨v - (P + L), by omega⟩
          have hj : v = P + L + j.val := by simp [j]; omega
          rw [hj] at hdeg ⊢
          rw [val0, val_gate, val_gate]
          congr 1
          apply List.map_congr_left
          intro a ha
          by_cases hlt : a < P + L + j.val
          · simp only [hlt, ite_true]
            have hstep : Step P L C a (P + L + j.val) := ⟨hlt, j, rfl, ha⟩
            have hda : deg P L C a = 0 := by
              have := deg_mono_step hstep
              omega
            exact ih a (by omega) hda
          · simp only [hlt, ite_false]
        · rw [val0, val_ge C _ _ (by omega), val_ge C _ _ (by omega)]

private lemma val_indep_of_no_line_reach {P L : ℕ} {C : Circuit}
    (x : Fin P → Bool) (y : Fin L → Bool) :
    ∀ v : ℕ, (∀ w : Fin L, ¬ Reach P L C (P + w.val) v) → val C x y v = val0 C L x v := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hno
    by_cases h1 : v < P
    · have hu : v = (⟨v, h1⟩ : Fin P).val := rfl
      rw [hu, val0, val_lt_P, val_lt_P]
    · by_cases h2 : v < P + L
      · exfalso
        exact hno ⟨v - P, by omega⟩ (by
          have : P + (v - P) = v := by omega
          rw [this]; exact Relation.ReflTransGen.refl)
      · by_cases h3 : v < P + L + C.gates.length
        · let j : Fin C.gates.length := ⟨v - (P + L), by omega⟩
          have hj : v = P + L + j.val := by simp [j]; omega
          rw [hj] at hno ⊢
          rw [val0, val_gate, val_gate]
          congr 1
          apply List.map_congr_left
          intro a ha
          by_cases hlt : a < P + L + j.val
          · simp only [hlt, ite_true]
            refine ih a (by omega) (fun w hreach => hno w ?_)
            exact Relation.ReflTransGen.tail hreach ⟨hlt, j, rfl, ha⟩
          · simp only [hlt, ite_false]
        · rw [val0, val_ge C _ _ (by omega), val_ge C _ _ (by omega)]

private def isYGate (P L : ℕ) (C : Circuit) (j : Fin C.gates.length) : Bool :=
  decide (deg P L C (P + L + j.val) = 1)

private def ych (P L : ℕ) (C : Circuit) (j : Fin C.gates.length) : List ℕ :=
  ((C.gates.get j).inputs.filter fun a => decide (a < P + L + j.val ∧ deg P L C a = 1)).dedup

private lemma mem_ych_iff {P L : ℕ} {C : Circuit} {j : Fin C.gates.length} {a : ℕ} :
    a ∈ ych P L C j ↔ a ∈ (C.gates.get j).inputs ∧ a < P + L + j.val ∧ deg P L C a = 1 := by
  simp [ych]

private lemma ych_nodup (P L : ℕ) (C : Circuit) (j : Fin C.gates.length) :
    (ych P L C j).Nodup :=
  List.nodup_dedup _

private lemma ych_length_le_two {P L : ℕ} {C : Circuit}
    (hFan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (j : Fin C.gates.length) :
    (ych P L C j).length ≤ 2 := by
  calc (ych P L C j).length
      ≤ ((C.gates.get j).inputs.filter _).length := List.Sublist.length_le (List.dedup_sublist _)
    _ ≤ (C.gates.get j).inputs.length := List.length_filter_le _ _
    _ ≤ 2 := hFan _ (List.get_mem _ _)

private def yAndOther (P L : ℕ) (C : Circuit) (j : Fin C.gates.length) : Option ℕ :=
  match (C.gates.get j).inputs with
  | [a, b] => if a < P + L + j.val ∧ deg P L C a = 1 then some b else some a
  | _ => none

private lemma yAnd_shape {P L : ℕ} {C : Circuit}
    (hFan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hDeg : HasLineDegree (P + L) (Finset.Ico P (P + L)) C 1)
    (hAllReach : ∀ j : Fin C.gates.length, Reach P L C (P + L + j.val) C.output)
    (j : Fin C.gates.length) (hy : isYGate P L C j = true)
    (hand : (C.gates.get j).op = GateOp.and) :
    (∃ a, (C.gates.get j).inputs = [a] ∧ a < P + L + j.val ∧ deg P L C a = 1 ∧
      ych P L C j = [a] ∧ yAndOther P L C j = none) ∨
    (∃ a b, ((C.gates.get j).inputs = [a, b] ∨ (C.gates.get j).inputs = [b, a]) ∧
      a < P + L + j.val ∧ deg P L C a = 1 ∧
      (b < P + L + j.val → deg P L C b = 0) ∧
      ych P L C j = [a] ∧ yAndOther P L C j = some b) := by
  have hd : deg P L C (P + L + j.val) = 1 := by simpa [isYGate] using hy
  rw [deg_gate, show isAndOp (C.gates.get j).op = true from (isAndOp_eq_true _).mpr hand] at hd
  simp only [ite_true] at hd
  have hlen : (C.gates.get j).inputs.length ≤ 2 := hFan _ (List.get_mem _ _)
  rcases h_ins : (C.gates.get j).inputs with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
  · rw [h_ins] at hd; simp at hd
  · left
    rw [h_ins] at hd
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hd
    by_cases hx : x < P + L + j.val
    · simp only [hx, ite_true] at hd
      refine ⟨x, rfl, hx, hd, ?_, ?_⟩
      · unfold ych; rw [h_ins]; simp [hx, hd]
      · unfold yAndOther; rw [h_ins]
    · simp only [hx, ite_false] at hd; omega
  · right
    rw [h_ins] at hd
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hd
    have hdx_le : deg P L C x ≤ 1 := deg_wire_le_one hDeg hAllReach x
    have hdy_le : deg P L C y ≤ 1 := deg_wire_le_one hDeg hAllReach y
    by_cases hx : x < P + L + j.val ∧ deg P L C x = 1
    · have hby : ¬ (y < P + L + j.val ∧ deg P L C y = 1) := by
        intro hy1
        simp only [hx.1, hy1.1, ite_true, hx.2, hy1.2] at hd
        omega
      have hdy0 : y < P + L + j.val → deg P L C y = 0 := by
        intro hylt
        simp only [hx.1, hylt, ite_true, hx.2] at hd
        omega
      refine ⟨x, y, Or.inl rfl, hx.1, hx.2, hdy0, ?_, ?_⟩
      · unfold ych; rw [h_ins]; simp [hx.1, hx.2, hby]
      · unfold yAndOther; rw [h_ins]; simp [hx.1, hx.2]
    · have hdx0 : (if x < P + L + j.val then deg P L C x else 0) = 0 := by
        by_cases hxl : x < P + L + j.val
        · simp only [hxl, ite_true]
          have : deg P L C x ≠ 1 := fun h => hx ⟨hxl, h⟩
          omega
        · simp only [hxl, ite_false]
      rw [hdx0, zero_add] at hd
      by_cases hyl : y < P + L + j.val
      · simp only [hyl, ite_true] at hd
        have hdx0' : x < P + L + j.val → deg P L C x = 0 := by
          intro hxl; simp only [hxl, ite_true] at hdx0; exact hdx0
        refine ⟨y, x, Or.inr rfl, hyl, hd, hdx0', ?_, ?_⟩
        · unfold ych; rw [h_ins]; simp [hx, hyl, hd]
        · unfold yAndOther; rw [h_ins]; simp [hx]
      · simp only [hyl, ite_false] at hd; omega
  · rw [h_ins] at hlen; simp at hlen

private lemma ych_length_eq_one_of_and {P L : ℕ} {C : Circuit}
    (hFan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hDeg : HasLineDegree (P + L) (Finset.Ico P (P + L)) C 1)
    (hAllReach : ∀ j : Fin C.gates.length, Reach P L C (P + L + j.val) C.output)
    (j : Fin C.gates.length) (hy : isYGate P L C j = true)
    (hand : (C.gates.get j).op = GateOp.and) :
    (ych P L C j).length = 1 := by
  rcases yAnd_shape hFan hDeg hAllReach j hy hand with
    ⟨a, _, _, _, hych, _⟩ | ⟨a, b, _, _, _, _, hych, _⟩
  · simp [hych]
  · simp [hych]

private def edgeSem (P L : ℕ) (C : Circuit) (x : Fin P → Bool) (j : Fin C.gates.length) : Bool :=
  if isAndOp (C.gates.get j).op then
    match yAndOther P L C j with
    | none => true
    | some f => if f < P + L + j.val then val0 C L x f else false
  else true

private def ctxSem (P L : ℕ) (C : Circuit) (x : Fin P → Bool) (v : ℕ) : Bool :=
  if v = C.output then true
  else
    (List.finRange C.gates.length).any fun j =>
      if h : v < P + L + j.val ∧ P + L + j.val ≤ C.output then
        isYGate P L C j && (ych P L C j).contains v && edgeSem P L C x j &&
          ctxSem P L C x (P + L + j.val)
      else false
termination_by C.output - v
decreasing_by omega

private lemma ctxSem_output (P L : ℕ) (C : Circuit) (x : Fin P → Bool) :
    ctxSem P L C x C.output = true := by
  rw [ctxSem]; simp

private lemma ctxSem_of_lt {P L : ℕ} {C : Circuit} {x : Fin P → Bool} {v : ℕ}
    (hAllReach : ∀ j : Fin C.gates.length, Reach P L C (P + L + j.val) C.output)
    (hne : v ≠ C.output) :
    ctxSem P L C x v =
      (List.finRange C.gates.length).any fun j =>
        isYGate P L C j && (ych P L C j).contains v && edgeSem P L C x j &&
          ctxSem P L C x (P + L + j.val) := by
  conv_lhs => rw [ctxSem]
  simp only [hne, ite_false]
  congr 1
  funext j
  by_cases hlt : v < P + L + j.val
  · have hle : P + L + j.val ≤ C.output := le_of_reach (hAllReach j)
    rw [dif_pos ⟨hlt, hle⟩]
  · rw [dif_neg (fun h => hlt h.1)]
    have hnot : (ych P L C j).contains v = false := by
      rw [Bool.eq_false_iff]
      intro hmem
      exact hlt (mem_ych_iff.mp (List.contains_iff_mem.mp hmem)).2.1
    rw [hnot]
    simp

private lemma ctxSem_sound {P L : ℕ} {C : Circuit}
    (hMono : IsMonotoneCircuit C)
    (hFan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hDeg : HasLineDegree (P + L) (Finset.Ico P (P + L)) C 1)
    (hAllReach : ∀ j : Fin C.gates.length, Reach P L C (P + L + j.val) C.output)
    (x : Fin P → Bool) (y : Fin L → Bool) :
    ∀ d v : ℕ, C.output - v = d → v ≤ C.output →
      val C x y v = true → ctxSem P L C x v = true → val C x y C.output = true := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro v hd hle hval hctx
    by_cases heq : v = C.output
    · rwa [← heq]
    · rw [ctxSem_of_lt hAllReach heq, List.any_eq_true] at hctx
      obtain ⟨j, _, hj⟩ := hctx
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hj
      obtain ⟨⟨⟨hy, hych⟩, hedge⟩, hctxj⟩ := hj
      obtain ⟨hmem, hlt, _⟩ := mem_ych_iff.mp hych
      have hjle : P + L + j.val ≤ C.output := le_of_reach (hAllReach j)
      have hvalj : val C x y (P + L + j.val) = true := by
        rw [val_gate]
        rcases hMono (C.gates.get j) (List.get_mem _ _) with hop | hop
        · rw [hop]
          unfold edgeSem at hedge
          rw [show isAndOp (C.gates.get j).op = true from (isAndOp_eq_true _).mpr hop] at hedge
          simp only [ite_true] at hedge
          rcases yAnd_shape hFan hDeg hAllReach j hy hop with
            ⟨a, hins, halt, _, hych_eq, _⟩ | ⟨a, b, hins, halt, _, _, hych_eq, hoth⟩
          · rw [hych_eq, List.mem_singleton] at hych
            subst hych
            rw [hins]
            simp [GateOp.eval, halt, hval]
          · rw [hych_eq, List.mem_singleton] at hych
            subst hych
            rw [hoth] at hedge
            by_cases hblt : b < P + L + j.val
            · simp only [hblt, ite_true] at hedge
              have hvb : val C x y b = true := val_mono hMono x y b hedge
              rcases hins with hins | hins <;> rw [hins] <;>
                simp [GateOp.eval, halt, hblt, hval, hvb]
            · simp only [hblt, ite_false] at hedge; simp at hedge
        · rw [hop]
          simp only [GateOp.eval, List.any_eq_true, id_eq, List.mem_map]
          exact ⟨true, ⟨v, hmem, by simp [hlt, hval]⟩, rfl⟩
      exact ih (C.output - (P + L + j.val)) (by omega) (P + L + j.val) rfl hjle hvalj hctxj

private lemma ctxSem_complete {P L : ℕ} {C : Circuit} {N : Finset (Fin L)}
    (hMono : IsMonotoneCircuit C)
    (hFan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hDeg : HasLineDegree (P + L) (Finset.Ico P (P + L)) C 1)
    (hAllReach : ∀ j : Fin C.gates.length, Reach P L C (P + L + j.val) C.output)
    (hN : ∀ w : Fin L, w ∈ N ↔ Reach P L C (P + w.val) C.output)
    (x : Fin P → Bool) (y : Fin L → Bool) :
    ∀ v : ℕ, v ≤ C.output → deg P L C v = 1 → Reach P L C v C.output →
      val C x y v = true → val0 C L x v = false → ctxSem P L C x v = true →
      ∃ u : Fin L, u ∈ N ∧ y u = true ∧ ctxSem P L C x (P + u.val) = true := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hle hdv hreach hval hval0 hctx
    by_cases h1 : v < P
    · rw [deg_lt_P P L C h1] at hdv; omega
    · by_cases h2 : v < P + L
      · let u : Fin L := ⟨v - P, by omega⟩
        have hu : v = P + u.val := by simp [u]; omega
        rw [hu] at hreach hval hctx
        refine ⟨u, (hN u).mpr hreach, ?_, hctx⟩
        simpa [val_line] using hval
      · by_cases h3 : v < P + L + C.gates.length
        · let j : Fin C.gates.length := ⟨v - (P + L), by omega⟩
          have hj : v = P + L + j.val := by simp [j]; omega
          rw [hj] at hle hdv hval hval0 hctx
          have hy : isYGate P L C j = true := by simp [isYGate, hdv]
          rcases hMono (C.gates.get j) (List.get_mem _ _) with hop | hop
          · rcases yAnd_shape hFan hDeg hAllReach j hy hop with
              ⟨a, hins, halt, hadeg, hych_eq, hoth⟩ |
              ⟨a, b, hins, halt, hadeg, hbdeg, hych_eq, hoth⟩
            · rw [val_gate, hop, hins] at hval
              rw [val0, val_gate, hop, hins] at hval0
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                id_eq, Bool.and_true, halt, ite_true] at hval hval0
              have hne_a : a ≠ C.output := by omega
              have hreach_a : Reach P L C a C.output :=
                Relation.ReflTransGen.head ⟨halt, j, rfl, by rw [hins]; simp⟩ (hAllReach j)
              have hctx_a : ctxSem P L C x a = true := by
                rw [ctxSem_of_lt hAllReach hne_a, List.any_eq_true]
                refine ⟨j, List.mem_finRange j, ?_⟩
                simp [hy, hych_eq, edgeSem, hop, isAndOp, hoth, hctx]
              exact ih a (by omega) (by omega) hadeg hreach_a hval hval0 hctx_a
            · rw [val_gate, hop] at hval
              rw [val0, val_gate, hop] at hval0
              have hval_ab : (if a < P + L + j.val then val C x y a else false) = true ∧
                  (if b < P + L + j.val then val C x y b else false) = true := by
                rcases hins with hins | hins
                · rw [hins] at hval; simpa [GateOp.eval, Bool.and_eq_true] using hval
                · rw [hins] at hval
                  have h := (by simpa [GateOp.eval, Bool.and_eq_true] using hval :
                    (if b < P + L + j.val then val C x y b else false) = true ∧
                    (if a < P + L + j.val then val C x y a else false) = true)
                  exact ⟨h.2, h.1⟩
              have hblt : b < P + L + j.val := by
                by_contra hnb
                simp only [hnb, ite_false] at hval_ab
                simp at hval_ab
              have hvb : val C x y b = true := by simpa [hblt] using hval_ab.2
              have hvb0 : val0 C L x b = true := by
                rw [← val_indep_of_deg_zero x y b (hbdeg hblt)]
                exact hvb
              have hva : val C x y a = true := by simpa [halt] using hval_ab.1
              have hva0 : val0 C L x a = false := by
                rcases hins with hins | hins
                · rw [hins] at hval0
                  simp only [val0, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
                    List.all_nil, id_eq, Bool.and_true, halt, hblt, ite_true] at hval0
                  change (val0 C L x a && val0 C L x b) = false at hval0
                  rw [hvb0, Bool.and_true] at hval0
                  exact hval0
                · rw [hins] at hval0
                  simp only [val0, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
                    List.all_nil, id_eq, Bool.and_true, halt, hblt, ite_true] at hval0
                  change (val0 C L x b && val0 C L x a) = false at hval0
                  rw [hvb0, Bool.true_and] at hval0
                  exact hval0
              have hne_a : a ≠ C.output := by omega
              have ha_mem : a ∈ (C.gates.get j).inputs := by
                rcases hins with hins | hins <;> rw [hins] <;> simp
              have hreach_a : Reach P L C a C.output :=
                Relation.ReflTransGen.head ⟨halt, j, rfl, ha_mem⟩ (hAllReach j)
              have hedge : edgeSem P L C x j = true := by
                simp [edgeSem, hop, isAndOp, hoth, hblt, hvb0]
              have hctx_a : ctxSem P L C x a = true := by
                rw [ctxSem_of_lt hAllReach hne_a, List.any_eq_true]
                refine ⟨j, List.mem_finRange j, ?_⟩
                simp [hy, hych_eq, hedge, hctx]
              exact ih a (by omega) (by omega) hadeg hreach_a hva hva0 hctx_a
          · rw [val_gate, hop] at hval
            rw [val0, val_gate, hop] at hval0
            simp only [GateOp.eval, List.any_eq_true, id_eq, List.mem_map] at hval
            obtain ⟨_, ⟨a, hamem, ha_eq⟩, ha_true⟩ := hval
            rw [ha_true] at ha_eq
            by_cases halt : a < P + L + j.val
            · simp only [halt, ite_true] at ha_eq
              have hva0 : val0 C L x a = false := by
                by_contra hne0
                have ht : val0 C L x a = true := by cases h : val0 C L x a <;> simp_all
                have : (GateOp.or.eval ((C.gates.get j).inputs.map fun z =>
                    if z < P + L + j.val then val0 C L x z else false)) = true := by
                  simp only [GateOp.eval, List.any_eq_true, id_eq, List.mem_map]
                  exact ⟨true, ⟨a, hamem, by simp [halt, ht]⟩, rfl⟩
                change GateOp.or.eval ((C.gates.get j).inputs.map fun z =>
                    if z < P + L + j.val then val0 C L x z else false) = false at hval0
                rw [this] at hval0
                simp at hval0
              have hadeg : deg P L C a = 1 := by
                have hle1 : deg P L C a ≤ 1 := deg_wire_le_one hDeg hAllReach a
                have hne0 : deg P L C a ≠ 0 := by
                  intro h0
                  have := val_indep_of_deg_zero x y a h0
                  rw [ha_eq, hva0] at this
                  simp at this
                omega
              have hne_a : a ≠ C.output := by
                have := le_of_reach (hAllReach j); omega
              have hreach_a : Reach P L C a C.output :=
                Relation.ReflTransGen.head ⟨halt, j, rfl, hamem⟩ (hAllReach j)
              have haych : a ∈ ych P L C j := mem_ych_iff.mpr ⟨hamem, halt, hadeg⟩
              have hedge : edgeSem P L C x j = true := by
                unfold edgeSem
                rw [hop]
                rfl
              have hctx_a : ctxSem P L C x a = true := by
                rw [ctxSem_of_lt hAllReach hne_a, List.any_eq_true]
                refine ⟨j, List.mem_finRange j, ?_⟩
                rw [hy, List.contains_iff_mem.mpr haych, hedge, hctx]
                rfl
              exact ih a (by omega) (by have := le_of_reach (hAllReach j); omega) hadeg hreach_a ha_eq hva0 hctx_a
            · simp only [halt, ite_false] at ha_eq; simp at ha_eq
        · rw [deg_ge P L C (by omega)] at hdv; omega

private lemma eval_eq_ctxSem {P L : ℕ} {C : Circuit} {N : Finset (Fin L)}
    (hMono : IsMonotoneCircuit C)
    (hFan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hDeg : HasLineDegree (P + L) (Finset.Ico P (P + L)) C 1)
    (hAllReach : ∀ j : Fin C.gates.length, Reach P L C (P + L + j.val) C.output)
    (hN : ∀ w : Fin L, w ∈ N ↔ Reach P L C (P + w.val) C.output)
    (hDegOut : deg P L C C.output = 1)
    (x : Fin P → Bool) (y : Fin L → Bool) :
    C.eval (List.ofFn x ++ List.ofFn y) =
      (C.eval (List.ofFn x ++ List.ofFn (fun _ : Fin L => false)) ||
        decide (∃ u : Fin L, y u = true ∧ (u ∈ N ∧ ctxSem P L C x (P + u.val) = true))) := by
  change val C x y C.output = (val0 C L x C.output || _)
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · intro hval
    cases h0 : val0 C L x C.output
    · right
      obtain ⟨u, huN, hyu, hctx⟩ := ctxSem_complete hMono hFan hDeg hAllReach hN x y
        C.output (le_refl _) hDegOut Relation.ReflTransGen.refl hval h0 (ctxSem_output P L C x)
      exact ⟨u, hyu, huN, hctx⟩
    · left; rfl
  · rintro (h0 | ⟨u, hyu, huN, hctx⟩)
    · exact val_mono hMono x y C.output h0
    · have hreach : Reach P L C (P + u.val) C.output := (hN u).mp huN
      have hvu : val C x y (P + u.val) = true := by rw [val_line]; exact hyu
      exact ctxSem_sound hMono hFan hDeg hAllReach x y
        (C.output - (P + u.val)) (P + u.val) rfl (le_of_reach hreach) hvu hctx

private def deadIdx (P : ℕ) (C : Circuit) : ℕ := P + C.gates.length + 1

private def evalOpt (gs : List Gate) {P : ℕ} (x : Fin P → Bool) : Option ℕ → Bool
  | none => true
  | some w => (runWires gs (List.ofFn x)).getD w false

private def ValidOpt (P : ℕ) (C : Circuit) (len : ℕ) : Option ℕ → Prop
  | none => True
  | some w => w < P + len ∨ w = deadIdx P C

private lemma validOpt_mono {P : ℕ} {C : Circuit} {len1 len2 : ℕ} (h : len1 ≤ len2)
    {o : Option ℕ} (hv : ValidOpt P C len1 o) : ValidOpt P C len2 o := by
  cases o with
  | none => trivial
  | some w =>
    rcases hv with hlt | heq
    · left; omega
    · right; exact heq

private lemma evalOpt_append {P : ℕ} {C : Circuit} (gs1 gs2 : List Gate) (x : Fin P → Bool)
    {o : Option ℕ} (hv : ValidOpt P C gs1.length o)
    (hbound : (gs1 ++ gs2).length ≤ C.gates.length) :
    evalOpt (gs1 ++ gs2) x o = evalOpt gs1 x o := by
  cases o with
  | none => rfl
  | some w =>
    simp only [evalOpt]
    rcases hv with hlt | rfl
    · rw [runWires_append]
      exact runWires_getD_lt gs2 (runWires gs1 (List.ofFn x)) (by rw [runWires_length, List.length_ofFn]; exact hlt)
    · have h1 : (List.ofFn x).length + gs1.length ≤ deadIdx P C := by
        simp only [List.length_ofFn, deadIdx]
        rw [List.length_append] at hbound; omega
      have h2 : (List.ofFn x).length + (gs1 ++ gs2).length ≤ deadIdx P C := by
        simp only [List.length_ofFn, deadIdx]; omega
      rw [runWires_getD_ge gs1 _ h1, runWires_getD_ge (gs1 ++ gs2) _ h2]

private lemma evalOpt_dead {P : ℕ} {C : Circuit} (gs : List Gate) (x : Fin P → Bool)
    (hbound : gs.length ≤ C.gates.length) :
    evalOpt gs x (some (deadIdx P C)) = false := by
  simp only [evalOpt]
  exact runWires_getD_ge gs (List.ofFn x) (by simp [deadIdx]; omega)

private def isMonoFan2 (gs : List Gate) : Prop :=
  (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) ∧ (∀ g ∈ gs, g.inputs.length ≤ 2)

private lemma isMonoFan2_nil : isMonoFan2 [] :=
  ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩

private lemma isMonoFan2_append {gs1 gs2 : List Gate}
    (h1 : isMonoFan2 gs1) (h2 : isMonoFan2 gs2) : isMonoFan2 (gs1 ++ gs2) := by
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩
  · rcases List.mem_append.mp hg with hg | hg
    · exact h1.1 g hg
    · exact h2.1 g hg
  · rcases List.mem_append.mp hg with hg | hg
    · exact h1.2 g hg
    · exact h2.2 g hg

private def buildPStep (P L : ℕ) (C : Circuit) (k : ℕ) (st : List Gate × (ℕ → ℕ)) :
    List Gate × (ℕ → ℕ) :=
  if hk : k < C.gates.length then
    if deg P L C (P + L + k) = 0 then
      let g := C.gates.get ⟨k, hk⟩
      let g' : Gate := ⟨g.op, g.inputs.map fun a => if a < P + L + k then st.2 a else deadIdx P C⟩
      let idx := P + st.1.length
      (st.1 ++ [g'], fun v => if v = P + L + k then idx else st.2 v)
    else st
  else st

private def buildP (P L : ℕ) (C : Circuit) : ℕ → List Gate × (ℕ → ℕ)
  | 0 => ([], fun v => if v < P then v else deadIdx P C)
  | k + 1 => buildPStep P L C k (buildP P L C k)

private lemma buildP_mono_len (P L : ℕ) (C : Circuit) (k : ℕ) :
    (buildP P L C k).1.length ≤ k := by
  induction k with
  | zero => simp [buildP]
  | succ k ih =>
    simp only [buildP, buildPStep]
    by_cases hk : k < C.gates.length
    · rw [dif_pos hk]
      by_cases hd : deg P L C (P + L + k) = 0
      · simp only [hd, ite_true, List.length_append, List.length_cons, List.length_nil]
        omega
      · simp only [hd, ite_false]; omega
    · rw [dif_neg hk]; omega

private lemma buildP_len_exact (P L : ℕ) (C : Circuit) (k : ℕ) (hk : k ≤ C.gates.length) :
    (buildP P L C k).1.length =
      ((Finset.univ : Finset (Fin C.gates.length)).filter
        (fun j => j.val < k ∧ deg P L C (P + L + j.val) = 0)).card := by
  induction k with
  | zero => simp [buildP]
  | succ k ih =>
    have hklt : k < C.gates.length := by omega
    have ih' := ih (by omega)
    let j0 : Fin C.gates.length := ⟨k, hklt⟩
    simp only [buildP, buildPStep, dif_pos hklt]
    by_cases hdeg0 : deg P L C (P + L + k) = 0
    · simp only [hdeg0, ite_true, List.length_append, List.length_cons, List.length_nil, ih']
      have hset : (Finset.univ.filter fun j : Fin C.gates.length =>
            j.val < k + 1 ∧ deg P L C (P + L + j.val) = 0) =
          insert j0 (Finset.univ.filter fun j : Fin C.gates.length =>
            j.val < k ∧ deg P L C (P + L + j.val) = 0) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, j0]
        constructor
        · rintro ⟨h1, h2⟩
          by_cases heq : j.val = k
          · left; exact heq
          · right; exact ⟨by omega, h2⟩
        · rintro (heq | ⟨h1, h2⟩)
          · exact ⟨by omega, by rw [heq]; exact hdeg0⟩
          · exact ⟨by omega, h2⟩
      rw [hset, Finset.card_insert_of_notMem (by simp [j0])]
    · rw [if_neg hdeg0, ih']
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        have hne : j.val ≠ k := by intro heq; rw [heq] at h2; exact hdeg0 h2
        exact ⟨by omega, h2⟩

private lemma buildP_isMonoFan2 {P L : ℕ} {C : Circuit}
    (hMono : IsMonotoneCircuit C) (hFan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (k : ℕ) :
    isMonoFan2 (buildP P L C k).1 := by
  induction k with
  | zero => exact isMonoFan2_nil
  | succ k ih =>
    simp only [buildP, buildPStep]
    by_cases hk : k < C.gates.length
    · rw [dif_pos hk]
      by_cases hdeg0 : deg P L C (P + L + k) = 0
      · simp only [hdeg0, ite_true]
        apply isMonoFan2_append ih
        refine ⟨fun g hg => ?_, fun g hg => ?_⟩
        · simp only [List.mem_singleton] at hg; subst hg
          exact hMono (C.gates.get ⟨k, hk⟩) (List.get_mem _ _)
        · simp only [List.mem_singleton] at hg; subst hg
          simp only [List.length_map]
          exact hFan (C.gates.get ⟨k, hk⟩) (List.get_mem _ _)
      · simp only [hdeg0, ite_false]; exact ih
    · rw [dif_neg hk]; exact ih

private lemma buildP_spec {P L : ℕ} {C : Circuit} (k : ℕ) (hk : k ≤ C.gates.length) :
    ∀ v < P + L + k, deg P L C v = 0 →
      (buildP P L C k).2 v < P + (buildP P L C k).1.length ∧
      ∀ (x : Fin P → Bool),
        (runWires (buildP P L C k).1 (List.ofFn x)).getD ((buildP P L C k).2 v) false =
          val0 C L x v := by
  induction k with
  | zero =>
    intro v hv hdv
    by_cases hvp : v < P
    · refine ⟨by simp [buildP, hvp], fun x => ?_⟩
      simp only [buildP, hvp, ite_true, runWires, List.foldl_nil]
      let u : Fin P := ⟨v, hvp⟩
      have hu : v = u.val := rfl
      rw [hu, val0, val_lt_P, List.getD_eq_getElem _ _ (by simp [u, hvp])]
      simp [u]
    · let w : Fin L := ⟨v - P, by omega⟩
      have hw : v = P + w.val := by dsimp [w]; omega
      rw [hw, deg_line] at hdv; omega
  | succ k ih =>
    have hklt : k < C.gates.length := by omega
    have ih' := ih (by omega)
    intro v hv hdv
    simp only [buildP, buildPStep, dif_pos hklt]
    by_cases hdeg0 : deg P L C (P + L + k) = 0
    · simp only [hdeg0, ite_true]
      set gs := (buildP P L C k).1
      set mp := (buildP P L C k).2
      let j : Fin C.gates.length := ⟨k, hklt⟩
      let g' : Gate := ⟨(C.gates.get j).op, (C.gates.get j).inputs.map fun a =>
        if a < P + L + k then mp a else deadIdx P C⟩
      by_cases hveq : v = P + L + k
      · subst hveq
        refine ⟨by simp, fun x => ?_⟩
        simp only [ite_true]
        have hsnoc := runWires_snoc_last gs g' (List.ofFn x)
        rw [List.length_ofFn] at hsnoc
        rw [hsnoc, val0, val_gate C x _ j]
        dsimp only [g', j]
        congr 1
        rw [List.map_map]
        apply List.map_congr_left
        intro a ha
        simp only [Function.comp_apply]
        by_cases halt : a < P + L + k
        · simp only [halt, ite_true]
          have hda : deg P L C a = 0 := by
            have h1 := deg_mono_step (⟨halt, j, rfl, ha⟩ : Step P L C a (P + L + j.val))
            dsimp [j] at h1
            omega
          exact (ih' a halt hda).2 x
        · simp only [halt, ite_false]
          have hglen : gs.length ≤ C.gates.length := le_trans (buildP_mono_len P L C k) (by omega)
          exact runWires_getD_ge gs (List.ofFn x) (by simp [deadIdx]; omega)
      · have hvlt : v < P + L + k := by omega
        obtain ⟨hmp, heval⟩ := ih' v hvlt hdv
        refine ⟨by simp [hveq]; omega, fun x => ?_⟩
        simp only [hveq, ite_false]
        rw [runWires_append,
          runWires_getD_lt [g'] (runWires gs (List.ofFn x)) (by rw [runWires_length, List.length_ofFn]; exact hmp)]
        exact heval x
    · simp only [hdeg0, ite_false]
      have hvlt : v < P + L + k := by
        by_contra hge
        have : v = P + L + k := by omega
        rw [this] at hdv; exact hdeg0 hdv
      exact ih' v hvlt hdv

private def addAndOpt (P : ℕ) (C : Circuit) (gs : List Gate)
    (c : Option ℕ) (fOpt : Option ℕ) : List Gate × Option ℕ :=
  match fOpt with
  | none => (gs, c)
  | some f =>
    if f = deadIdx P C then (gs, some (deadIdx P C))
    else match c with
      | none => (gs, some f)
      | some w => (gs ++ [⟨GateOp.and, [w, f]⟩], some (P + gs.length))

private lemma addAndOpt_ext (P : ℕ) (C : Circuit) (gs : List Gate) (c fOpt : Option ℕ) :
    ∃ extra, (addAndOpt P C gs c fOpt).1 = gs ++ extra ∧ extra.length ≤ 1 ∧ isMonoFan2 extra := by
  cases fOpt with
  | none => exact ⟨[], by simp [addAndOpt], by simp, isMonoFan2_nil⟩
  | some f =>
    simp only [addAndOpt]
    by_cases hf : f = deadIdx P C
    · simp only [hf, ite_true]
      exact ⟨[], by simp, by simp, isMonoFan2_nil⟩
    · simp only [hf, ite_false]
      cases c with
      | none => exact ⟨[], by simp, by simp, isMonoFan2_nil⟩
      | some w =>
        exact ⟨[⟨GateOp.and, [w, f]⟩], rfl, by simp,
          ⟨fun g hg => by simp at hg; subst hg; left; rfl,
           fun g hg => by simp at hg; subst hg; simp⟩⟩

private lemma addAndOpt_valid {P : ℕ} {C : Circuit} (gs : List Gate) {c fOpt : Option ℕ}
    (hc : ValidOpt P C gs.length c) (hf : ValidOpt P C gs.length fOpt) :
    ValidOpt P C (addAndOpt P C gs c fOpt).1.length (addAndOpt P C gs c fOpt).2 := by
  cases fOpt with
  | none => exact hc
  | some f =>
    simp only [addAndOpt]
    by_cases hfd : f = deadIdx P C
    · simp only [hfd, ite_true]; right; rfl
    · simp only [hfd, ite_false]
      cases c with
      | none => exact hf
      | some w => left; simp

private lemma addAndOpt_eval {P : ℕ} {C : Circuit} (gs : List Gate) (x : Fin P → Bool)
    {c fOpt : Option ℕ}
    (hc : ValidOpt P C gs.length c) (hf : ValidOpt P C gs.length fOpt)
    (hbound : (addAndOpt P C gs c fOpt).1.length ≤ C.gates.length) :
    evalOpt (addAndOpt P C gs c fOpt).1 x (addAndOpt P C gs c fOpt).2 =
      (evalOpt gs x c && evalOpt gs x fOpt) := by
  cases fOpt with
  | none => simp [addAndOpt, evalOpt]
  | some f =>
    simp only [addAndOpt] at hbound ⊢
    by_cases hfd : f = deadIdx P C
    · simp only [hfd, ite_true] at hbound ⊢
      rw [evalOpt_dead gs x hbound, Bool.and_false]
    · simp only [hfd, ite_false] at hbound ⊢
      cases c with
      | none => simp [evalOpt]
      | some w =>
        simp only [evalOpt]
        have hsnoc := runWires_snoc_last gs ⟨GateOp.and, [w, f]⟩ (List.ofFn x)
        rw [List.length_ofFn] at hsnoc
        rw [hsnoc]
        simp [GateOp.eval]

private def addOrChain (P : ℕ) (gs : List Gate) (acc : ℕ) : List ℕ → List Gate × ℕ
  | [] => (gs, acc)
  | w :: ws =>
    let idx := P + gs.length
    addOrChain P (gs ++ [⟨GateOp.or, [acc, w]⟩]) idx ws

private lemma addOrChain_ext (P : ℕ) (gs : List Gate) (acc : ℕ) (ws : List ℕ) :
    ∃ extra, (addOrChain P gs acc ws).1 = gs ++ extra ∧
      extra.length = ws.length ∧ isMonoFan2 extra := by
  induction ws generalizing gs acc with
  | nil => exact ⟨[], by simp [addOrChain], rfl, isMonoFan2_nil⟩
  | cons w ws ih =>
    obtain ⟨extra, heq, hlen, hmf⟩ := ih (gs ++ [⟨GateOp.or, [acc, w]⟩]) (P + gs.length)
    refine ⟨⟨GateOp.or, [acc, w]⟩ :: extra, ?_, by simp [hlen], ?_⟩
    · simp only [addOrChain, heq, List.append_assoc, List.singleton_append]
    · refine ⟨fun g hg => ?_, fun g hg => ?_⟩
      · rcases List.mem_cons.mp hg with rfl | hg
        · right; rfl
        · exact hmf.1 g hg
      · rcases List.mem_cons.mp hg with rfl | hg
        · simp
        · exact hmf.2 g hg

private lemma addOrChain_valid {P : ℕ} {C : Circuit} (gs : List Gate) (acc : ℕ) (ws : List ℕ)
    (hacc : ValidOpt P C gs.length (some acc)) :
    ValidOpt P C (addOrChain P gs acc ws).1.length (some (addOrChain P gs acc ws).2) := by
  induction ws generalizing gs acc with
  | nil => exact hacc
  | cons w ws ih =>
    simp only [addOrChain]
    exact ih (gs ++ [⟨GateOp.or, [acc, w]⟩]) (P + gs.length) (Or.inl (by simp))

private lemma addOrChain_eval {P : ℕ} {C : Circuit} (gs : List Gate) (x : Fin P → Bool)
    (acc : ℕ) (ws : List ℕ)
    (hacc : ValidOpt P C gs.length (some acc))
    (hws : ∀ w ∈ ws, ValidOpt P C gs.length (some w))
    (hbound : (addOrChain P gs acc ws).1.length ≤ C.gates.length) :
    evalOpt (addOrChain P gs acc ws).1 x (some (addOrChain P gs acc ws).2) =
      (evalOpt gs x (some acc) || ws.any (fun w => evalOpt gs x (some w))) := by
  induction ws generalizing gs acc with
  | nil => simp [addOrChain]
  | cons w ws ih =>
    simp only [addOrChain] at hbound ⊢
    set gs1 := gs ++ [⟨GateOp.or, [acc, w]⟩]
    have hgs1_len : gs1.length ≤ C.gates.length := by
      obtain ⟨extra, heq, _, _⟩ := addOrChain_ext P gs1 (P + gs.length) ws
      rw [heq, List.length_append] at hbound; omega
    have hws1 : ∀ u ∈ ws, ValidOpt P C gs1.length (some u) :=
      fun u hu => validOpt_mono (by simp [gs1]) (hws u (List.mem_cons_of_mem _ hu))
    rw [ih gs1 (P + gs.length) (Or.inl (by simp [gs1])) hws1 hbound]
    have hstep_eval : evalOpt gs1 x (some (P + gs.length)) =
        (evalOpt gs x (some acc) || evalOpt gs x (some w)) := by
      simp only [evalOpt, gs1]
      have hsnoc := runWires_snoc_last gs ⟨GateOp.or, [acc, w]⟩ (List.ofFn x)
      rw [List.length_ofFn] at hsnoc
      rw [hsnoc]
      simp [GateOp.eval]
    rw [hstep_eval]
    have hany : ws.any (fun u => evalOpt gs1 x (some u)) = ws.any (fun u => evalOpt gs x (some u)) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨u, hu, hev⟩
        refine ⟨u, hu, ?_⟩
        rwa [evalOpt_append gs [⟨GateOp.or, [acc, w]⟩] x (hws u (List.mem_cons_of_mem _ hu)) hgs1_len] at hev
      · rintro ⟨u, hu, hev⟩
        refine ⟨u, hu, ?_⟩
        rwa [evalOpt_append gs [⟨GateOp.or, [acc, w]⟩] x (hws u (List.mem_cons_of_mem _ hu)) hgs1_len]
    rw [hany]
    simp [Bool.or_assoc]

private def addOrList (P : ℕ) (C : Circuit) (gs : List Gate) (cs : List (Option ℕ)) :
    List Gate × Option ℕ :=
  if cs.any Option.isNone then (gs, none)
  else
    match cs.filterMap id with
    | [] => (gs, some (deadIdx P C))
    | w :: ws =>
      let res := addOrChain P gs w ws
      (res.1, some res.2)

private lemma addOrList_ext (P : ℕ) (C : Circuit) (gs : List Gate) (cs : List (Option ℕ)) :
    ∃ extra, (addOrList P C gs cs).1 = gs ++ extra ∧
      extra.length ≤ cs.length - 1 ∧ isMonoFan2 extra := by
  unfold addOrList
  by_cases hnone : cs.any Option.isNone = true
  · simp only [hnone, ite_true]
    exact ⟨[], by simp, by simp, isMonoFan2_nil⟩
  · simp only [hnone, ite_false]
    cases hfm : cs.filterMap id with
    | nil => exact ⟨[], by simp, by simp, isMonoFan2_nil⟩
    | cons w ws =>
      obtain ⟨extra, heq, hlen, hmf⟩ := addOrChain_ext P gs w ws
      have hfmlen : (cs.filterMap id).length ≤ cs.length := List.length_filterMap_le id cs
      rw [hfm, List.length_cons] at hfmlen
      exact ⟨extra, heq, by omega, hmf⟩

private lemma addOrList_valid {P : ℕ} {C : Circuit} (gs : List Gate) (cs : List (Option ℕ))
    (hcs : ∀ c ∈ cs, ValidOpt P C gs.length c) :
    ValidOpt P C (addOrList P C gs cs).1.length (addOrList P C gs cs).2 := by
  unfold addOrList
  by_cases hnone : cs.any Option.isNone = true
  · simp only [hnone, ite_true]; trivial
  · simp only [hnone, ite_false]
    cases hfm : cs.filterMap id with
    | nil => right; rfl
    | cons w ws =>
      have hw : some w ∈ cs := by
        have hmem : w ∈ cs.filterMap id := by rw [hfm]; simp
        obtain ⟨o, ho, hoid⟩ := List.mem_filterMap.mp hmem
        cases o with
        | none => simp at hoid
        | some u => simp at hoid; subst hoid; exact ho
      exact addOrChain_valid gs w ws (hcs _ hw)

private lemma addOrList_eval {P : ℕ} {C : Circuit} (gs : List Gate) (x : Fin P → Bool)
    (cs : List (Option ℕ))
    (hcs : ∀ c ∈ cs, ValidOpt P C gs.length c)
    (hbound : (addOrList P C gs cs).1.length ≤ C.gates.length) :
    evalOpt (addOrList P C gs cs).1 x (addOrList P C gs cs).2 =
      cs.any (evalOpt gs x) := by
  unfold addOrList at hbound ⊢
  by_cases hnone : cs.any Option.isNone = true
  · simp only [hnone, ite_true, evalOpt]
    symm
    rw [List.any_eq_true]
    obtain ⟨c, hc, hcn⟩ := List.any_eq_true.mp hnone
    cases c with
    | none => exact ⟨none, hc, rfl⟩
    | some _ => simp at hcn
  · rw [if_neg hnone] at hbound ⊢
    have hall_some : ∀ c ∈ cs, ∃ w, c = some w := by
      intro c hc
      cases c with
      | none =>
        exfalso
        exact hnone (List.any_eq_true.mpr ⟨none, hc, rfl⟩)
      | some w => exact ⟨w, rfl⟩
    cases hfm : cs.filterMap id with
    | nil =>
      rw [hfm] at hbound
      dsimp only at hbound ⊢
      rw [evalOpt_dead gs x hbound]
      symm
      rw [Bool.eq_false_iff]
      intro hany
      obtain ⟨c, hc, _⟩ := List.any_eq_true.mp hany
      obtain ⟨w, rfl⟩ := hall_some c hc
      have : w ∈ cs.filterMap id := List.mem_filterMap.mpr ⟨some w, hc, rfl⟩
      rw [hfm] at this; simp at this
    | cons w ws =>
      rw [hfm] at hbound
      dsimp only at hbound ⊢
      have hmem_all : ∀ u ∈ w :: ws, some u ∈ cs := by
        intro u hu
        have : u ∈ cs.filterMap id := by rw [hfm]; exact hu
        obtain ⟨o, ho, hoid⟩ := List.mem_filterMap.mp this
        cases o with
        | none => simp at hoid
        | some z => simp at hoid; subst hoid; exact ho
      have hwv := hcs _ (hmem_all w (by simp))
      have hwsv : ∀ u ∈ ws, ValidOpt P C gs.length (some u) :=
        fun u hu => hcs _ (hmem_all u (List.mem_cons_of_mem _ hu))
      rw [addOrChain_eval gs x w ws hwv hwsv hbound]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, List.any_eq_true]
      constructor
      · rintro (hw | ⟨u, hu, hev⟩)
        · exact ⟨some w, hmem_all w (by simp), hw⟩
        · exact ⟨some u, hmem_all u (List.mem_cons_of_mem _ hu), hev⟩
      · rintro ⟨c, hc, hev⟩
        obtain ⟨u, rfl⟩ := hall_some c hc
        have hu : u ∈ w :: ws := by
          rw [← hfm]
          exact List.mem_filterMap.mpr ⟨some u, hc, rfl⟩
        rcases List.mem_cons.mp hu with rfl | hws_mem
        · left; exact hev
        · right; exact ⟨u, hws_mem, hev⟩

private def yParents (P L : ℕ) (C : Circuit) (v : ℕ) : List (Fin C.gates.length) :=
  (List.finRange C.gates.length).filter fun j => isYGate P L C j && (ych P L C j).contains v

private def yStep (P L : ℕ) (C : Circuit) (pMap : ℕ → ℕ) (v : ℕ)
    (st : List Gate × (ℕ → Option ℕ) × (ℕ → Option ℕ)) :
    List Gate × (ℕ → Option ℕ) × (ℕ → Option ℕ) :=
  let gs := st.1
  let ctxMap := st.2.1
  let contribMap := st.2.2
  if hv : v < P + L + C.gates.length ∧ deg P L C v = 1 ∧
      (v = C.output ∨ (yParents P L C v).length > 0) then
    let p1 :=
      if v = C.output then (gs, (none : Option ℕ))
      else addOrList P C gs ((yParents P L C v).map fun j => contribMap j.val)
    let gs1 := p1.1
    let cv := p1.2
    let ctxMap1 := fun w => if w = v then cv else ctxMap w
    if hge : P + L ≤ v then
      let j : Fin C.gates.length := ⟨v - (P + L), by omega⟩
      if isAndOp (C.gates.get j).op then
        let fOpt : Option ℕ :=
          match yAndOther P L C j with
          | none => none
          | some f => some (if f < P + L + j.val then pMap f else deadIdx P C)
        let p2 := addAndOpt P C gs1 cv fOpt
        (p2.1, ctxMap1, fun k => if k = j.val then p2.2 else contribMap k)
      else
        (gs1, ctxMap1, fun k => if k = j.val then cv else contribMap k)
    else
      (gs1, ctxMap1, contribMap)
  else st

private def buildY (P L : ℕ) (C : Circuit) (gsP : List Gate) (pMap : ℕ → ℕ) :
    ℕ → List Gate × (ℕ → Option ℕ) × (ℕ → Option ℕ)
  | 0 => (gsP, fun _ => some (deadIdx P C), fun _ => some (deadIdx P C))
  | step + 1 =>
    yStep P L C pMap (C.output - step) (buildY P L C gsP pMap step)

private def yNodeCost (P L : ℕ) (C : Circuit) (v : ℕ) : ℕ :=
  if v < P + L + C.gates.length ∧ deg P L C v = 1 ∧
      (v = C.output ∨ (yParents P L C v).length > 0) then
    (if v = C.output then 0 else (yParents P L C v).length - 1) +
    (if h : P + L ≤ v ∧ v < P + L + C.gates.length then
      if isAndOp (C.gates.get ⟨v - (P + L), by omega⟩).op then 1 else 0
    else 0)
  else 0

private lemma yStep_ext (P L : ℕ) (C : Circuit) (pMap : ℕ → ℕ) (v : ℕ)
    (st : List Gate × (ℕ → Option ℕ) × (ℕ → Option ℕ)) :
    ∃ extra, (yStep P L C pMap v st).1 = st.1 ++ extra ∧ isMonoFan2 extra ∧
      extra.length ≤ yNodeCost P L C v := by
  unfold yStep yNodeCost
  dsimp only
  by_cases hv : v < P + L + C.gates.length ∧ deg P L C v = 1 ∧
      (v = C.output ∨ (yParents P L C v).length > 0)
  · rw [dif_pos hv, if_pos hv]
    have hp1 : ∃ e1, (if v = C.output then (st.1, (none : Option ℕ))
          else addOrList P C st.1 ((yParents P L C v).map fun j => st.2.2 j.val)).1 = st.1 ++ e1 ∧
        isMonoFan2 e1 ∧ e1.length ≤ (if v = C.output then 0 else (yParents P L C v).length - 1) := by
      by_cases hveq : v = C.output
      · rw [if_pos hveq, if_pos hveq]
        exact ⟨[], by simp, isMonoFan2_nil, by simp⟩
      · rw [if_neg hveq, if_neg hveq]
        obtain ⟨e1, heq, hlen, hmf⟩ := addOrList_ext P C st.1
          ((yParents P L C v).map fun j => st.2.2 j.val)
        rw [List.length_map] at hlen
        exact ⟨e1, heq, hmf, hlen⟩
    obtain ⟨e1, he1_eq, he1_mf, he1_len⟩ := hp1
    set p1 := if v = C.output then (st.1, (none : Option ℕ))
      else addOrList P C st.1 ((yParents P L C v).map fun j => st.2.2 j.val)
    by_cases hge : P + L ≤ v
    · rw [dif_pos hge, dif_pos ⟨hge, hv.1⟩]
      let j : Fin C.gates.length := ⟨v - (P + L), by omega⟩
      by_cases hand : isAndOp (C.gates.get j).op = true
      · rw [if_pos hand, if_pos hand]
        let fOpt : Option ℕ :=
          match yAndOther P L C j with
          | none => none
          | some f => some (if f < P + L + j.val then pMap f else deadIdx P C)
        obtain ⟨e2, he2_eq, he2_len, he2_mf⟩ := addAndOpt_ext P C p1.1 p1.2 fOpt
        refine ⟨e1 ++ e2, ?_, isMonoFan2_append he1_mf he2_mf, ?_⟩
        · rw [he2_eq, he1_eq, List.append_assoc]
        · rw [List.length_append]; omega
      · rw [if_neg hand, if_neg hand]
        exact ⟨e1, he1_eq, he1_mf, by omega⟩
    · rw [dif_neg hge, dif_neg (fun h => hge h.1)]
      exact ⟨e1, he1_eq, he1_mf, by omega⟩
  · rw [dif_neg hv, if_neg hv]
    exact ⟨[], by simp, isMonoFan2_nil, by simp⟩

private lemma buildY_step_ext (P L : ℕ) (C : Circuit) (gsP : List Gate) (pMap : ℕ → ℕ)
    (step : ℕ) :
    ∃ extra, (buildY P L C gsP pMap (step + 1)).1 = (buildY P L C gsP pMap step).1 ++ extra ∧
      isMonoFan2 extra ∧ extra.length ≤ yNodeCost P L C (C.output - step) :=
  yStep_ext P L C pMap (C.output - step) (buildY P L C gsP pMap step)

private lemma buildY_isMonoFan2 {P L : ℕ} {C : Circuit} {gsP : List Gate}
    (hP : isMonoFan2 gsP) (pMap : ℕ → ℕ) (step : ℕ) :
    isMonoFan2 (buildY P L C gsP pMap step).1 := by
  induction step with
  | zero => exact hP
  | succ step ih =>
    obtain ⟨extra, heq, hmf, _⟩ := buildY_step_ext P L C gsP pMap step
    rw [heq]
    exact isMonoFan2_append ih hmf

private lemma buildY_len_mono (P L : ℕ) (C : Circuit) (gsP : List Gate) (pMap : ℕ → ℕ)
    {s1 s2 : ℕ} (h : s1 ≤ s2) :
    (buildY P L C gsP pMap s1).1.length ≤ (buildY P L C gsP pMap s2).1.length := by
  induction h with
  | refl => exact le_refl _
  | @step m _ ih =>
    obtain ⟨extra, heq, _, _⟩ := buildY_step_ext P L C gsP pMap m
    rw [heq, List.length_append]; omega

private lemma buildY_len_le_sum (P L : ℕ) (C : Circuit) (gsP : List Gate) (pMap : ℕ → ℕ)
    (step : ℕ) :
    (buildY P L C gsP pMap step).1.length ≤
      gsP.length + ∑ s ∈ Finset.range step, yNodeCost P L C (C.output - s) := by
  induction step with
  | zero => simp [buildY]
  | succ step ih =>
    obtain ⟨extra, heq, _, hlen⟩ := buildY_step_ext P L C gsP pMap step
    rw [heq, List.length_append, Finset.sum_range_succ]
    omega

private lemma mem_yParents_iff {P L : ℕ} {C : Circuit} {v : ℕ} {j : Fin C.gates.length} :
    j ∈ yParents P L C v ↔ isYGate P L C j = true ∧ v ∈ ych P L C j := by
  simp [yParents]

private lemma yParents_nodup (P L : ℕ) (C : Circuit) (v : ℕ) :
    (yParents P L C v).Nodup :=
  (List.nodup_finRange C.gates.length).filter _

private lemma reach_iff_yNode {P L : ℕ} {C : Circuit}
    (hDeg : HasLineDegree (P + L) (Finset.Ico P (P + L)) C 1)
    (hAllReach : ∀ j : Fin C.gates.length, Reach P L C (P + L + j.val) C.output)
    {v : ℕ} (hdv : deg P L C v = 1) :
    Reach P L C v C.output ↔ (v = C.output ∨ (yParents P L C v).length > 0) := by
  constructor
  · intro hreach
    rcases Relation.ReflTransGen.cases_head hreach with rfl | ⟨b, hstep, _⟩
    · left; rfl
    · right
      rcases hstep with ⟨hlt, j, rfl, hmem⟩
      have hdj : deg P L C (P + L + j.val) = 1 := by
        have h1 : deg P L C v ≤ deg P L C (P + L + j.val) :=
          deg_mono_step ⟨hlt, j, rfl, hmem⟩
        have h2 : deg P L C (P + L + j.val) ≤ 1 := deg_wire_le_one hDeg hAllReach _
        omega
      have hjmem : j ∈ yParents P L C v := by
        rw [mem_yParents_iff]
        exact ⟨by simp [isYGate, hdj], mem_ych_iff.mpr ⟨hmem, hlt, hdv⟩⟩
      exact List.length_pos_of_mem hjmem
  · rintro (rfl | hpos)
    · exact Relation.ReflTransGen.refl
    · obtain ⟨j, hjmem⟩ := List.exists_mem_of_length_pos hpos
      rw [mem_yParents_iff] at hjmem
      obtain ⟨hmem, hlt, _⟩ := mem_ych_iff.mp hjmem.2
      exact Relation.ReflTransGen.head ⟨hlt, j, rfl, hmem⟩ (hAllReach j)

private lemma yParents_output_nil {P L : ℕ} {C : Circuit}
    (hAllReach : ∀ j : Fin C.gates.length, Reach P L C (P + L + j.val) C.output) :
    yParents P L C C.output = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro j hj
  rw [mem_yParents_iff] at hj
  have h1 : C.output < P + L + j.val := (mem_ych_iff.mp hj.2).2.1
  have h2 : P + L + j.val ≤ C.output := le_of_reach (hAllReach j)
  omega

private lemma buildY_final_size {P L : ℕ} {C : Circuit} {N : Finset (Fin L)}
    (hMono : IsMonotoneCircuit C)
    (hFan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hDeg : HasLineDegree (P + L) (Finset.Ico P (P + L)) C 1)
    (hAllReach : ∀ j : Fin C.gates.length, Reach P L C (P + L + j.val) C.output)
    (hN : ∀ w : Fin L, w ∈ N ↔ Reach P L C (P + w.val) C.output)
    (hOutLt : C.output < P + L + C.gates.length)
    (hOutDeg : deg P L C C.output = 1)
    (hOutGe : P + L ≤ C.output) :
    (buildY P L C (buildP P L C C.gates.length).1 (buildP P L C C.gates.length).2
      (C.output - P + 1)).1.length + N.card ≤ C.gates.length + 1 := by
  classical
  set gsP := (buildP P L C C.gates.length).1
  set pMap := (buildP P L C C.gates.length).2
  set totalSteps := C.output - P + 1
  have hlen_sum := buildY_len_le_sum P L C gsP pMap totalSteps
  let GP := (Finset.univ : Finset (Fin C.gates.length)).filter (fun j => deg P L C (P + L + j.val) = 0)
  let GY := (Finset.univ : Finset (Fin C.gates.length)).filter (fun j => deg P L C (P + L + j.val) = 1)
  let GYa := GY.filter (fun j => isAndOp (C.gates.get j).op = true)
  let GYo := GY.filter (fun j => isAndOp (C.gates.get j).op = false)
  have hgsP_len : gsP.length = GP.card := by
    have h := buildP_len_exact P L C C.gates.length (le_refl _)
    simpa [gsP, GP] using h
  have hGP_GY : GP.card + GY.card = C.gates.length := by
    have hdisj : Disjoint GP GY := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      simp only [GP, GY, Finset.mem_filter] at hj1 hj2
      omega
    have hunion : GP ∪ GY = Finset.univ := by
      ext j
      simp only [GP, GY, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      have hle := deg_wire_le_one hDeg hAllReach (P + L + j.val)
      omega
    have := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ, Fintype.card_fin] at this
    omega
  have hGY_disj : Disjoint GYa GYo := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [GYa, GYo, Finset.mem_filter] at hj1 hj2
    rw [hj1.2] at hj2; simp at hj2
  have hGY_union : GYa ∪ GYo = GY := by
    ext j
    simp only [GYa, GYo, Finset.mem_union, Finset.mem_filter]
    cases isAndOp (C.gates.get j).op <;> simp
  have hGYa_GYo : GYa.card + GYo.card = GY.card := by
    have := Finset.card_union_of_disjoint hGY_disj
    rw [hGY_union] at this
    omega
  have hsum_reindex :
      (∑ s ∈ Finset.range totalSteps, yNodeCost P L C (C.output - s)) =
      ∑ v ∈ Finset.Icc P C.output, yNodeCost P L C v := by
    refine Finset.sum_bij (fun s _ => C.output - s) ?_ ?_ ?_ ?_
    · intro s hs
      simp only [Finset.mem_range, totalSteps] at hs
      simp only [Finset.mem_Icc]
      omega
    · intro s1 hs1 s2 hs2 heq
      simp only [Finset.mem_range, totalSteps] at hs1 hs2
      omega
    · intro v hv
      simp only [Finset.mem_Icc] at hv
      exact ⟨C.output - v, by simp [totalSteps]; omega, by omega⟩
    · intro s _; rfl
  let VY : Finset ℕ := (Finset.Icc P C.output).filter fun v =>
    v < P + L + C.gates.length ∧ deg P L C v = 1 ∧ (v = C.output ∨ (yParents P L C v).length > 0)
  have hOutMemVY : C.output ∈ VY := by
    simp only [VY, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, le_refl _⟩, hOutLt, hOutDeg, Or.inl trivial⟩
  have hVY_card : VY.card = N.card + GY.card := by
    let VYN := N.image (fun w : Fin L => P + w.val)
    let VYG := GY.image (fun j : Fin C.gates.length => P + L + j.val)
    have hVYN_card : VYN.card = N.card :=
      Finset.card_image_of_injective N (fun a b h => Fin.ext (by omega))
    have hVYG_card : VYG.card = GY.card :=
      Finset.card_image_of_injective GY (fun a b h => Fin.ext (by omega))
    have hdisj : Disjoint VYN VYG := by
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      simp only [VYN, VYG, Finset.mem_image] at hv1 hv2
      obtain ⟨w, _, rfl⟩ := hv1
      obtain ⟨j, _, hj⟩ := hv2
      have := w.isLt
      omega
    have hunion : VY = VYN ∪ VYG := by
      ext v
      simp only [VY, VYN, VYG, Finset.mem_filter, Finset.mem_Icc, Finset.mem_union,
        Finset.mem_image, GY, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨hv1, hv2⟩, hvlt, hdv, hpar⟩
        have hreach : Reach P L C v C.output := (reach_iff_yNode hDeg hAllReach hdv).mpr hpar
        by_cases hltPL : v < P + L
        · left
          refine ⟨⟨v - P, by omega⟩, (hN _).mpr ?_, by dsimp; omega⟩
          have : P + (⟨v - P, by omega⟩ : Fin L).val = v := by dsimp; omega
          rwa [this]
        · right
          refine ⟨⟨v - (P + L), by omega⟩, ?_, by dsimp; omega⟩
          have : P + L + (⟨v - (P + L), by omega⟩ : Fin C.gates.length).val = v := by dsimp; omega
          rwa [this]
      · rintro (⟨w, hwN, rfl⟩ | ⟨j, hjdeg, rfl⟩)
        · have hw := w.isLt
          have hreach : Reach P L C (P + w.val) C.output := (hN w).mp hwN
          have hle : P + w.val ≤ C.output := le_of_reach hreach
          have hdw : deg P L C (P + w.val) = 1 := deg_line P L C w
          exact ⟨⟨by omega, hle⟩, by omega, hdw, (reach_iff_yNode hDeg hAllReach hdw).mp hreach⟩
        · have hj := j.isLt
          have hreach : Reach P L C (P + L + j.val) C.output := hAllReach j
          have hle : P + L + j.val ≤ C.output := le_of_reach hreach
          exact ⟨⟨by omega, hle⟩, by omega, hjdeg, (reach_iff_yNode hDeg hAllReach hjdeg).mp hreach⟩
    rw [hunion, Finset.card_union_of_disjoint hdisj, hVYN_card, hVYG_card]
  have hsum_VY :
      (∑ v ∈ Finset.Icc P C.output, yNodeCost P L C v) =
      (∑ v ∈ VY.erase C.output, ((yParents P L C v).length - 1)) + GYa.card := by
    have hsplit : (∑ v ∈ Finset.Icc P C.output, yNodeCost P L C v) =
        ∑ v ∈ VY, ((if v = C.output then 0 else (yParents P L C v).length - 1) +
          (if h : P + L ≤ v ∧ v < P + L + C.gates.length then
            if isAndOp (C.gates.get ⟨v - (P + L), by omega⟩).op then 1 else 0
          else 0)) := by
      simp only [yNodeCost]
      rw [← Finset.sum_filter]
    rw [hsplit, Finset.sum_add_distrib]
    congr 1
    · rw [← Finset.add_sum_erase _ _ hOutMemVY]
      simp only [ite_true, zero_add]
      refine Finset.sum_congr rfl fun v hv => ?_
      have hne := Finset.ne_of_mem_erase hv
      simp only [hne, ite_false]
    · have hGYa_eq : GYa.card = ∑ _j ∈ GYa, (1 : ℕ) := by simp
      rw [hGYa_eq]
      symm
      refine Finset.sum_bij_ne_zero (fun j _ _ => P + L + j.val) ?_ ?_ ?_ ?_
      · intro j hj _
        have hjlt := j.isLt
        simp only [GYa, GY, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp only [VY, Finset.mem_filter, Finset.mem_Icc]
        have hreach := hAllReach j
        exact ⟨⟨by omega, le_of_reach hreach⟩, by omega, hj.1,
          (reach_iff_yNode hDeg hAllReach hj.1).mp hreach⟩
      · intro j1 _ _ j2 _ _ heq
        exact Fin.ext (by omega)
      · intro v hv hne
        simp only [VY, Finset.mem_filter] at hv
        by_cases hcond : P + L ≤ v ∧ v < P + L + C.gates.length
        · rw [dif_pos hcond] at hne
          let j : Fin C.gates.length := ⟨v - (P + L), by omega⟩
          have hand : isAndOp (C.gates.get j).op = true := by
            by_contra hna; rw [if_neg hna] at hne; exact hne rfl
          have hjmem : j ∈ GYa := by
            simp only [GYa, GY, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨?_, hand⟩
            have hjeq : P + L + j.val = v := by dsimp [j]; omega
            rw [hjeq]
            exact hv.2.2.1
          exact ⟨j, hjmem, by simp, by dsimp [j]; omega⟩
        · rw [dif_neg hcond] at hne; exact absurd rfl hne
      · intro j hj _
        have hjlt := j.isLt
        simp only [GYa, GY, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have hcond : P + L ≤ P + L + j.val ∧ P + L + j.val < P + L + C.gates.length := by omega
        rw [dif_pos hcond]
        have heq : (⟨P + L + j.val - (P + L), by omega⟩ : Fin C.gates.length) = j :=
          Fin.ext (by dsimp; omega)
        rw [heq, if_pos hj.2]
  have hpar_pos : ∀ v ∈ VY.erase C.output, 1 ≤ (yParents P L C v).length := by
    intro v hv
    have hne : v ≠ C.output := Finset.ne_of_mem_erase hv
    have hmem : v ∈ VY := Finset.mem_of_mem_erase hv
    simp only [VY, Finset.mem_filter] at hmem
    rcases hmem.2.2.2 with rfl | hpos
    · exact absurd rfl hne
    · omega
  have hsub_sum :
      (∑ v ∈ VY.erase C.output, ((yParents P L C v).length - 1)) + (VY.card - 1) =
      ∑ v ∈ VY, (yParents P L C v).length := by
    have h1 : (∑ v ∈ VY.erase C.output, ((yParents P L C v).length - 1)) + (VY.erase C.output).card =
        ∑ v ∈ VY.erase C.output, (yParents P L C v).length := by
      have hc : (VY.erase C.output).card = ∑ _v ∈ VY.erase C.output, (1 : ℕ) := by simp
      rw [hc, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v hv => ?_
      have := hpar_pos v hv; omega
    have h2 : (VY.erase C.output).card = VY.card - 1 := Finset.card_erase_of_mem hOutMemVY
    have h3 : (∑ v ∈ VY, (yParents P L C v).length) =
        (yParents P L C C.output).length + ∑ v ∈ VY.erase C.output, (yParents P L C v).length :=
      (Finset.add_sum_erase _ _ hOutMemVY).symm
    rw [h3, yParents_output_nil hAllReach, List.length_nil, zero_add, ← h2]
    exact h1
  have hdouble :
      (∑ v ∈ VY, (yParents P L C v).length) = ∑ j ∈ GY, (ych P L C j).length := by
    have hL : ∀ v ∈ VY, (yParents P L C v).length =
        (GY.filter fun j => v ∈ ych P L C j).card := by
      intro v _
      rw [← List.toFinset_card_of_nodup (yParents_nodup P L C v)]
      congr 1
      ext j
      simp [mem_yParents_iff, GY, isYGate]
    have hR : ∀ j ∈ GY, (ych P L C j).length =
        (VY.filter fun v => v ∈ ych P L C j).card := by
      intro j hj
      have hjlt := j.isLt
      rw [← List.toFinset_card_of_nodup (ych_nodup P L C j)]
      congr 1
      ext v
      simp only [List.mem_toFinset, Finset.mem_filter, VY, Finset.mem_Icc]
      constructor
      · intro hvych
        obtain ⟨hmem, hlt, hdv⟩ := mem_ych_iff.mp hvych
        have hreach : Reach P L C v C.output :=
          Relation.ReflTransGen.head ⟨hlt, j, rfl, hmem⟩ (hAllReach j)
        have hgeP : P ≤ v := by
          by_contra hltP
          rw [deg_lt_P P L C (by omega)] at hdv; omega
        exact ⟨⟨⟨hgeP, le_of_reach hreach⟩, by omega, hdv,
          (reach_iff_yNode hDeg hAllReach hdv).mp hreach⟩, hvych⟩
      · exact fun h => h.2
    rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR]
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hych_bound : (∑ j ∈ GY, (ych P L C j).length) ≤ GYa.card + 2 * GYo.card := by
    rw [← hGY_union, Finset.sum_union hGY_disj]
    have h1 : (∑ j ∈ GYa, (ych P L C j).length) ≤ GYa.card := by
      have heq : (∑ j ∈ GYa, (ych P L C j).length) = ∑ _j ∈ GYa, (1 : ℕ) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        simp only [GYa, GY, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact ych_length_eq_one_of_and hFan hDeg hAllReach j
          (by simp [isYGate, hj.1]) ((isAndOp_eq_true _).mp hj.2)
      rw [heq]; simp
    have h2 : (∑ j ∈ GYo, (ych P L C j).length) ≤ 2 * GYo.card := by
      calc (∑ j ∈ GYo, (ych P L C j).length)
          ≤ ∑ _j ∈ GYo, (2 : ℕ) := Finset.sum_le_sum fun j _ => ych_length_le_two hFan j
        _ = 2 * GYo.card := by simp [mul_comm]
    omega
  have hVY_pos : 1 ≤ VY.card := Finset.card_pos.mpr ⟨C.output, hOutMemVY⟩
  rw [hsum_reindex, hsum_VY] at hlen_sum
  change (buildY P L C gsP pMap totalSteps).1.length + N.card ≤ C.gates.length + 1
  omega

private lemma buildY_from_gsP (P L : ℕ) (C : Circuit) (gsP : List Gate) (pMap : ℕ → ℕ)
    (step : ℕ) :
    ∃ e0, (buildY P L C gsP pMap step).1 = gsP ++ e0 := by
  induction step with
  | zero => exact ⟨[], by simp [buildY]⟩
  | succ s ihs =>
    obtain ⟨e0, he0⟩ := ihs
    obtain ⟨ea, hea, _, _⟩ := buildY_step_ext P L C gsP pMap s
    exact ⟨e0 ++ ea, by rw [hea, he0, List.append_assoc]⟩

private lemma buildY_sem {P L : ℕ} {C : Circuit}
    (hMono : IsMonotoneCircuit C)
    (hFan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hDeg : HasLineDegree (P + L) (Finset.Ico P (P + L)) C 1)
    (hAllReach : ∀ j : Fin C.gates.length, Reach P L C (P + L + j.val) C.output)
    (hOutLt : C.output < P + L + C.gates.length)
    (hFinalBound :
      (buildY P L C (buildP P L C C.gates.length).1 (buildP P L C C.gates.length).2
        (C.output - P + 1)).1.length ≤ C.gates.length)
    (x : Fin P → Bool) :
    ∀ step ≤ C.output - P + 1,
      let st := buildY P L C (buildP P L C C.gates.length).1 (buildP P L C C.gates.length).2 step
      (∀ v, C.output + 1 - step ≤ v → v ≤ C.output →
        v < P + L + C.gates.length → deg P L C v = 1 →
        (v = C.output ∨ (yParents P L C v).length > 0) →
        ValidOpt P C st.1.length (st.2.1 v) ∧
        evalOpt st.1 x (st.2.1 v) = ctxSem P L C x v) ∧
      (∀ j : Fin C.gates.length, C.output + 1 - step ≤ P + L + j.val →
        isYGate P L C j = true →
        ValidOpt P C st.1.length (st.2.2 j.val) ∧
        evalOpt st.1 x (st.2.2 j.val) = (ctxSem P L C x (P + L + j.val) && edgeSem P L C x j)) := by
  set gsP := (buildP P L C C.gates.length).1
  set pMap := (buildP P L C C.gates.length).2
  have hpSpec := buildP_spec (P := P) (L := L) (C := C) C.gates.length (le_refl _)
  intro step
  induction step with
  | zero =>
    intro _
    refine ⟨fun v h1 h2 _ _ _ => by omega, fun j h1 _ => ?_⟩
    have hjle : P + L + j.val ≤ C.output := le_of_reach (hAllReach j)
    omega
  | succ step ih =>
    intro hstep_le
    obtain ⟨ihCtx, ihContrib⟩ := ih (by omega)
    set st := buildY P L C gsP pMap step
    set v0 := C.output - step
    have hnext_bound : (buildY P L C gsP pMap (step + 1)).1.length ≤ C.gates.length :=
      le_trans (buildY_len_mono P L C gsP pMap hstep_le) hFinalBound
    obtain ⟨extra, hextra_eq, _, _⟩ := buildY_step_ext P L C gsP pMap step
    have hlen_le : st.1.length ≤ (buildY P L C gsP pMap (step + 1)).1.length := by
      change (buildY P L C gsP pMap step).1.length ≤ (buildY P L C gsP pMap (step + 1)).1.length
      rw [hextra_eq, List.length_append]; omega
    change (∀ v, C.output + 1 - (step + 1) ≤ v → v ≤ C.output →
        v < P + L + C.gates.length → deg P L C v = 1 →
        (v = C.output ∨ (yParents P L C v).length > 0) →
        ValidOpt P C (yStep P L C pMap v0 st).1.length ((yStep P L C pMap v0 st).2.1 v) ∧
        evalOpt (yStep P L C pMap v0 st).1 x ((yStep P L C pMap v0 st).2.1 v) = ctxSem P L C x v) ∧
      (∀ j : Fin C.gates.length, C.output + 1 - (step + 1) ≤ P + L + j.val →
        isYGate P L C j = true →
        ValidOpt P C (yStep P L C pMap v0 st).1.length ((yStep P L C pMap v0 st).2.2 j.val) ∧
        evalOpt (yStep P L C pMap v0 st).1 x ((yStep P L C pMap v0 st).2.2 j.val) =
          (ctxSem P L C x (P + L + j.val) && edgeSem P L C x j))
    by_cases hv0 : v0 < P + L + C.gates.length ∧ deg P L C v0 = 1 ∧
        (v0 = C.output ∨ (yParents P L C v0).length > 0)
    · have hyStep_unfold : yStep P L C pMap v0 st =
        let p1 :=
          if v0 = C.output then (st.1, (none : Option ℕ))
          else addOrList P C st.1 ((yParents P L C v0).map fun j => st.2.2 j.val)
        let gs1 := p1.1
        let cv := p1.2
        let ctxMap1 := fun w => if w = v0 then cv else st.2.1 w
        if hge : P + L ≤ v0 then
          let j : Fin C.gates.length := ⟨v0 - (P + L), by omega⟩
          if isAndOp (C.gates.get j).op then
            let fOpt : Option ℕ :=
              match yAndOther P L C j with
              | none => none
              | some f => some (if f < P + L + j.val then pMap f else deadIdx P C)
            let p2 := addAndOpt P C gs1 cv fOpt
            (p2.1, ctxMap1, fun k => if k = j.val then p2.2 else st.2.2 k)
          else
            (gs1, ctxMap1, fun k => if k = j.val then cv else st.2.2 k)
        else
          (gs1, ctxMap1, st.2.2) := by
        unfold yStep; rw [dif_pos hv0]
      set p1 :=
        if v0 = C.output then (st.1, (none : Option ℕ))
        else addOrList P C st.1 ((yParents P L C v0).map fun j => st.2.2 j.val)
      have hp1_ext : ∃ e1, p1.1 = st.1 ++ e1 := by
        by_cases heq : v0 = C.output
        · exact ⟨[], by simp [p1, heq]⟩
        · obtain ⟨e1, he1, _, _⟩ := addOrList_ext P C st.1
            ((yParents P L C v0).map fun j => st.2.2 j.val)
          exact ⟨e1, by simp [p1, heq, he1]⟩
      have hp1_to_next : ∃ e2, (yStep P L C pMap v0 st).1 = p1.1 ++ e2 := by
        rw [hyStep_unfold]
        dsimp only
        by_cases hge : P + L ≤ v0
        · rw [dif_pos hge]
          let j : Fin C.gates.length := ⟨v0 - (P + L), by omega⟩
          by_cases hand : isAndOp (C.gates.get j).op = true
          · simp only [j, hand, ite_true]
            obtain ⟨e2, he2, _, _⟩ := addAndOpt_ext P C p1.1 p1.2 _
            exact ⟨e2, he2⟩
          · simp only [j, hand, ite_false]; exact ⟨[], by simp⟩
        · rw [dif_neg hge]; exact ⟨[], by simp⟩
      obtain ⟨e2, he2_eq⟩ := hp1_to_next
      have hp1_bound : p1.1.length ≤ C.gates.length := by
        have h' : (yStep P L C pMap v0 st).1.length ≤ C.gates.length := hnext_bound
        rw [he2_eq, List.length_append] at h'; omega
      have hcv_spec : ValidOpt P C p1.1.length p1.2 ∧ evalOpt p1.1 x p1.2 = ctxSem P L C x v0 := by
        by_cases heq : v0 = C.output
        · simp only [p1, heq, ite_true]
          exact ⟨trivial, (ctxSem_output P L C x).symm⟩
        · simp only [p1, heq, ite_false]
          have hpar_spec : ∀ j ∈ yParents P L C v0,
              ValidOpt P C st.1.length (st.2.2 j.val) ∧
              evalOpt st.1 x (st.2.2 j.val) = (ctxSem P L C x (P + L + j.val) && edgeSem P L C x j) := by
            intro j hj
            rw [mem_yParents_iff] at hj
            have hlt : v0 < P + L + j.val := (mem_ych_iff.mp hj.2).2.1
            have hstep_gt : C.output + 1 - step ≤ P + L + j.val := by omega
            exact ihContrib j hstep_gt hj.1
          have hcs_valid : ∀ c ∈ (yParents P L C v0).map (fun j => st.2.2 j.val),
              ValidOpt P C st.1.length c := by
            intro c hc
            obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
            exact (hpar_spec j hj).1
          have hval := addOrList_valid st.1 _ hcs_valid
          have hev := addOrList_eval st.1 x _ hcs_valid (by simpa [p1, heq] using hp1_bound)
          refine ⟨hval, ?_⟩
          rw [hev, ctxSem_of_lt hAllReach heq, List.any_map]
          apply Bool.eq_iff_iff.mpr
          simp only [List.any_eq_true, Function.comp_apply]
          constructor
          · rintro ⟨j, hj, hjv⟩
            rw [(hpar_spec j hj).2] at hjv
            rw [mem_yParents_iff] at hj
            refine ⟨j, List.mem_finRange j, ?_⟩
            simp only [Bool.and_eq_true] at hjv ⊢
            exact ⟨⟨⟨hj.1, List.contains_iff_mem.mpr hj.2⟩, hjv.2⟩, hjv.1⟩
          · rintro ⟨j, _, hjv⟩
            simp only [Bool.and_eq_true, List.contains_iff_mem] at hjv
            obtain ⟨⟨⟨hyj, hych⟩, hedge⟩, hctxj⟩ := hjv
            have hjmem : j ∈ yParents P L C v0 := mem_yParents_iff.mpr ⟨hyj, hych⟩
            refine ⟨j, hjmem, ?_⟩
            rw [(hpar_spec j hjmem).2]
            simp [hctxj, hedge]
      have hcv_final : ValidOpt P C (yStep P L C pMap v0 st).1.length p1.2 ∧
          evalOpt (yStep P L C pMap v0 st).1 x p1.2 = ctxSem P L C x v0 := by
        refine ⟨validOpt_mono (by rw [he2_eq, List.length_append]; omega) hcv_spec.1, ?_⟩
        rw [he2_eq, evalOpt_append p1.1 e2 x hcv_spec.1 (by rw [← he2_eq]; exact hnext_bound)]
        exact hcv_spec.2
      have hctxMap_eq : (yStep P L C pMap v0 st).2.1 = fun w => if w = v0 then p1.2 else st.2.1 w := by
        rw [hyStep_unfold]
        dsimp only
        by_cases hge : P + L ≤ v0
        · rw [dif_pos hge]
          by_cases hand : isAndOp (C.gates.get ⟨v0 - (P + L), by omega⟩).op = true
          · rw [if_pos hand]
          · rw [if_neg hand]
        · rw [dif_neg hge]
      constructor
      · intro v hv1 hv2 hvlt hdv hpar
        rw [hctxMap_eq]
        by_cases hveq : v = v0
        · subst hveq; simpa using hcv_final
        · simp only [hveq, ite_false]
          have hv_old : C.output + 1 - step ≤ v := by omega
          obtain ⟨hval_old, hev_old⟩ := ihCtx v hv_old hv2 hvlt hdv hpar
          refine ⟨validOpt_mono hlen_le hval_old, ?_⟩
          have hex : (yStep P L C pMap v0 st).1 = st.1 ++ extra := hextra_eq
          rw [hex, evalOpt_append st.1 extra x hval_old (by rw [← hex]; exact hnext_bound)]
          exact hev_old
      · intro j hj1 hyj
        have hjlt := j.isLt
        by_cases hjeq : P + L + j.val = v0
        · have hge : P + L ≤ v0 := by omega
          let j' : Fin C.gates.length := ⟨v0 - (P + L), by omega⟩
          have hj_eq : j' = j := Fin.ext (by dsimp [j']; omega)
          have hsub : v0 - (P + L) = j.val := by omega
          rw [hyStep_unfold]
          dsimp only
          rw [dif_pos hge]
          change ValidOpt P C _ _ ∧ evalOpt _ x _ = (ctxSem P L C x (P + L + j.val) && edgeSem P L C x j)
          have h_j' : (⟨v0 - (P + L), by omega⟩ : Fin C.gates.length) = j := hj_eq
          have hgoal_rw :
              (if isAndOp (C.gates.get ⟨v0 - (P + L), by omega⟩).op = true then
                let fOpt : Option ℕ :=
                  match yAndOther P L C ⟨v0 - (P + L), by omega⟩ with
                  | none => none
                  | some f => some (if f < P + L + (v0 - (P + L)) then pMap f else deadIdx P C)
                let p2 := addAndOpt P C p1.1 p1.2 fOpt
                (p2.1, fun w => if w = v0 then p1.2 else st.2.1 w,
                  fun k => if k = v0 - (P + L) then p2.2 else st.2.2 k)
              else
                (p1.1, fun w => if w = v0 then p1.2 else st.2.1 w,
                  fun k => if k = v0 - (P + L) then p1.2 else st.2.2 k)) =
              (if isAndOp (C.gates.get j).op = true then
                let fOpt : Option ℕ :=
                  match yAndOther P L C j with
                  | none => none
                  | some f => some (if f < P + L + j.val then pMap f else deadIdx P C)
                let p2 := addAndOpt P C p1.1 p1.2 fOpt
                (p2.1, fun w => if w = v0 then p1.2 else st.2.1 w,
                  fun k => if k = j.val then p2.2 else st.2.2 k)
              else
                (p1.1, fun w => if w = v0 then p1.2 else st.2.1 w,
                  fun k => if k = j.val then p1.2 else st.2.2 k)) :=
            congrArg (fun jj : Fin C.gates.length =>
              if isAndOp (C.gates.get jj).op = true then
                let fOpt : Option ℕ :=
                  match yAndOther P L C jj with
                  | none => none
                  | some f => some (if f < P + L + jj.val then pMap f else deadIdx P C)
                let p2 := addAndOpt P C p1.1 p1.2 fOpt
                (p2.1, fun w => if w = v0 then p1.2 else st.2.1 w,
                  fun k => if k = jj.val then p2.2 else st.2.2 k)
              else
                (p1.1, fun w => if w = v0 then p1.2 else st.2.1 w,
                  fun k => if k = jj.val then p1.2 else st.2.2 k)) h_j'
          rw [hgoal_rw]
          by_cases hand : isAndOp (C.gates.get j).op = true
          · rw [if_pos hand]
            dsimp only
            simp only [ite_true]
            let fOpt : Option ℕ :=
              match yAndOther P L C j with
              | none => none
              | some f => some (if f < P + L + j.val then pMap f else deadIdx P C)
            have hfOpt_spec : ValidOpt P C p1.1.length fOpt ∧ evalOpt p1.1 x fOpt = edgeSem P L C x j := by
              obtain ⟨e1, he1⟩ := hp1_ext
              obtain ⟨e0, he0⟩ := buildY_from_gsP P L C gsP pMap step
              have heP : p1.1 = gsP ++ (e0 ++ e1) := by rw [he1, he0, List.append_assoc]
              have hp1_ge_P : gsP.length ≤ p1.1.length := by rw [heP, List.length_append]; omega
              unfold edgeSem
              rw [if_pos hand]
              have hand_eq : (C.gates.get j).op = GateOp.and := (isAndOp_eq_true _).mp hand
              rcases yAnd_shape hFan hDeg hAllReach j hyj hand_eq with
                ⟨a, _, _, _, _, hoth⟩ | ⟨a, b, _, _, _, hbdeg, _, hoth⟩
              · simp [fOpt, hoth, ValidOpt, evalOpt]
              · simp only [fOpt, hoth]
                by_cases hblt : b < P + L + j.val
                · rw [if_pos hblt, if_pos hblt]
                  have hdb : deg P L C b = 0 := hbdeg hblt
                  obtain ⟨hmp_lt, hmp_eval⟩ := hpSpec b (by omega) hdb
                  change pMap b < P + gsP.length at hmp_lt
                  change ∀ x : Fin P → Bool, (runWires gsP (List.ofFn x)).getD (pMap b) false = val0 C L x b at hmp_eval
                  refine ⟨Or.inl (by omega), ?_⟩
                  have hval_b : ValidOpt P C gsP.length (some (pMap b)) := Or.inl hmp_lt
                  rw [heP, evalOpt_append gsP (e0 ++ e1) x hval_b (by rw [← heP]; exact hp1_bound)]
                  exact hmp_eval x
                · rw [if_neg hblt, if_neg hblt]
                  exact ⟨Or.inr rfl, evalOpt_dead p1.1 x hp1_bound⟩
            have hbound_and : (addAndOpt P C p1.1 p1.2 fOpt).1.length ≤ C.gates.length := by
              have h' := hnext_bound
              change (yStep P L C pMap v0 st).1.length ≤ C.gates.length at h'
              rw [hyStep_unfold] at h'
              dsimp only at h'
              rw [dif_pos hge, hgoal_rw, if_pos hand] at h'
              exact h'
            refine ⟨addAndOpt_valid p1.1 hcv_spec.1 hfOpt_spec.1, ?_⟩
            rw [addAndOpt_eval p1.1 x hcv_spec.1 hfOpt_spec.1 hbound_and,
              hcv_spec.2, hfOpt_spec.2, hjeq]
          · rw [if_neg hand]
            dsimp only
            simp only [ite_true]
            have hedge_true : edgeSem P L C x j = true := by unfold edgeSem; rw [if_neg hand]
            rw [hedge_true, Bool.and_true, hjeq]
            exact hcv_spec
        · have hcontrib_unch : (yStep P L C pMap v0 st).2.2 j.val = st.2.2 j.val := by
            rw [hyStep_unfold]
            dsimp only
            by_cases hge : P + L ≤ v0
            · rw [dif_pos hge]
              have hne_val : j.val ≠ v0 - (P + L) := by omega
              by_cases hand : isAndOp (C.gates.get ⟨v0 - (P + L), by omega⟩).op = true
              · rw [if_pos hand]; dsimp only; rw [if_neg hne_val]
              · rw [if_neg hand]; dsimp only; rw [if_neg hne_val]
            · rw [dif_neg hge]
          rw [hcontrib_unch]
          have hj_old : C.output + 1 - step ≤ P + L + j.val := by omega
          obtain ⟨hval_old, hev_old⟩ := ihContrib j hj_old hyj
          refine ⟨validOpt_mono hlen_le hval_old, ?_⟩
          have hex : (yStep P L C pMap v0 st).1 = st.1 ++ extra := hextra_eq
          rw [hex, evalOpt_append st.1 extra x hval_old (by rw [← hex]; exact hnext_bound)]
          exact hev_old
    · have hid : yStep P L C pMap v0 st = st := by unfold yStep; rw [dif_neg hv0]
      rw [hid]
      constructor
      · intro v hv1 hv2 hvlt hdv hpar
        have hne : v ≠ v0 := by intro h; subst h; exact hv0 ⟨hvlt, hdv, hpar⟩
        exact ihCtx v (by omega) hv2 hvlt hdv hpar
      · intro j hj1 hyj
        have hjlt := j.isLt
        have hne : P + L + j.val ≠ v0 := by
          intro h
          have hdg : deg P L C v0 = 1 := by rw [← h]; simpa [isYGate] using hyj
          have hpar := (reach_iff_yNode hDeg hAllReach hdg).mp (h ▸ hAllReach j)
          exact hv0 ⟨by omega, hdg, hpar⟩
        exact ihContrib j (by omega) hyj

private lemma main_proof :
    ∀ (P1 L1 : ℕ) (C1 : PEqualNP.CircuitLowerBounds.Circuit) (N1 : Finset (Fin L1)),
      PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C1 →
      (∀ g1 ∈ C1.gates, g1.inputs.length ≤ 2) →
      PEqualNP.CircuitLowerBounds.HasLineDegree (P1 + L1) (Finset.Ico P1 (P1 + L1)) C1 1 →
      (∀ j1 : Fin C1.gates.length,
        Relation.ReflTransGen
          (fun a1 b1 : ℕ => a1 < b1 ∧ ∃ i1 : Fin C1.gates.length,
            b1 = P1 + L1 + i1.val ∧ a1 ∈ (C1.gates.get i1).inputs)
          (P1 + L1 + j1.val) C1.output) →
      (∀ w1 : Fin L1, w1 ∈ N1 ↔
        Relation.ReflTransGen
          (fun r1 s1 : ℕ => r1 < s1 ∧ ∃ k1 : Fin C1.gates.length,
            s1 = P1 + L1 + k1.val ∧ r1 ∈ (C1.gates.get k1).inputs)
          (P1 + w1.val) C1.output) →
      ∃ (D1 : PEqualNP.CircuitLowerBounds.Circuit) (T1 : Finset (Fin L1)) (o1 : Fin L1 → ℕ),
        PEqualNP.CircuitLowerBounds.IsMonotoneCircuit D1 ∧
        (∀ h1 ∈ D1.gates, h1.inputs.length ≤ 2) ∧
        D1.size + N1.card ≤ C1.size + 1 ∧
        ∀ (x1 : Fin P1 → Bool) (y1 : Fin L1 → Bool),
          C1.eval (List.ofFn x1 ++ List.ofFn y1) =
            (C1.eval (List.ofFn x1 ++ List.ofFn (fun _ : Fin L1 => false)) ||
              decide (∃ u1 : Fin L1, y1 u1 = true ∧
                (u1 ∈ T1 ∨ (D1.wires (List.ofFn x1)).getD (o1 u1) false = true))) := by
  intro P L C N hMono hFan hDeg hAllReach hN
  change ∀ j : Fin C.gates.length, Reach P L C (P + L + j.val) C.output at hAllReach
  change ∀ w : Fin L, w ∈ N ↔ Reach P L C (P + w.val) C.output at hN
  by_cases hNempty : N = ∅
  · refine ⟨⟨[], 0⟩, ∅, fun _ => P, ?_, ?_, ?_, ?_⟩
    · intro g hg; simp at hg
    · intro g hg; simp at hg
    · simp [Circuit.size, hNempty]
    · intro x y
      have hno : ∀ w : Fin L, ¬ Reach P L C (P + w.val) C.output := by
        intro w hreach
        have : w ∈ N := (hN w).mpr hreach
        rw [hNempty] at this; exact Finset.notMem_empty w this
      have hind := val_indep_of_no_line_reach x y C.output hno
      change val C x y C.output = (val0 C L x C.output || _)
      rw [hind]
      have hg : (({ gates := [], output := 0 } : Circuit).wires (List.ofFn x)).getD P false = false := by
        rw [runWires_eq]
        exact runWires_getD_ge [] (List.ofFn x) (by simp)
      have hdec : decide (∃ u : Fin L, y u = true ∧
          (u ∈ (∅ : Finset (Fin L)) ∨
            (({ gates := [], output := 0 } : Circuit).wires (List.ofFn x)).getD P false = true)) = false := by
        rw [decide_eq_false_iff_not]
        rintro ⟨u, _, hu | hw⟩
        · exact Finset.notMem_empty u hu
        · rw [hg] at hw; simp at hw
      rw [hdec, Bool.or_false]
  · obtain ⟨w0, hw0N⟩ := Finset.nonempty_iff_ne_empty.mpr hNempty
    have hw0Reach : Reach P L C (P + w0.val) C.output := (hN w0).mp hw0N
    have hOutDeg : deg P L C C.output = 1 := by
      have h1 : 1 ≤ deg P L C C.output := by
        have := deg_mono_reach hw0Reach
        rw [deg_line] at this
        exact this
      have h2 : deg P L C C.output ≤ 1 := hDeg
      omega
    have hOutGeP : P ≤ C.output := by
      have := le_of_reach hw0Reach; omega
    have hOutLt : C.output < P + L + C.gates.length := by
      by_contra hge
      rw [deg_ge P L C (by omega)] at hOutDeg; omega
    by_cases hOutGePL : P + L ≤ C.output
    · set bp := buildP P L C C.gates.length
      set stFinal := buildY P L C bp.1 bp.2 (C.output - P + 1)
      have hSize : stFinal.1.length + N.card ≤ C.gates.length + 1 :=
        buildY_final_size hMono hFan hDeg hAllReach hN hOutLt hOutDeg hOutGePL
      have hNpos : 1 ≤ N.card := Finset.card_pos.mpr ⟨w0, hw0N⟩
      have hFinalBound : stFinal.1.length ≤ C.gates.length := by omega
      have hmf : isMonoFan2 stFinal.1 :=
        buildY_isMonoFan2 (buildP_isMonoFan2 hMono hFan C.gates.length) bp.2 (C.output - P + 1)
      let D : Circuit := ⟨stFinal.1, 0⟩
      let T : Finset (Fin L) := N.filter fun u => (stFinal.2.1 (P + u.val)).isNone
      let o : Fin L → ℕ := fun u =>
        if u ∈ N then (stFinal.2.1 (P + u.val)).getD (deadIdx P C) else deadIdx P C
      refine ⟨D, T, o, hmf.1, hmf.2, hSize, ?_⟩
      intro x y
      rw [eval_eq_ctxSem hMono hFan hDeg hAllReach hN hOutDeg x y]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      have hSem := (buildY_sem hMono hFan hDeg hAllReach hOutLt hFinalBound x
        (C.output - P + 1) (le_refl _)).1
      constructor
      · rintro ⟨u, hyu, huN, hctx⟩
        have hult := u.isLt
        refine ⟨u, hyu, ?_⟩
        have hureach : Reach P L C (P + u.val) C.output := (hN u).mp huN
        have hu_spec := hSem (P + u.val) (by omega) (le_of_reach hureach) (by omega)
          (deg_line P L C u) ((reach_iff_yNode hDeg hAllReach (deg_line P L C u)).mp hureach)
        cases hopt : stFinal.2.1 (P + u.val) with
        | none =>
          left
          simp [T, huN, hopt]
        | some w =>
          right
          have hev := hu_spec.2
          rw [hopt] at hev
          simp only [evalOpt] at hev
          simp only [o, huN, ite_true, hopt, Option.getD_some, D, runWires_eq]
          rw [hev, hctx]
      · rintro ⟨u, hyu, hTo⟩
        have hult := u.isLt
        by_cases huN : u ∈ N
        · have hureach : Reach P L C (P + u.val) C.output := (hN u).mp huN
          have hu_spec := hSem (P + u.val) (by omega) (le_of_reach hureach) (by omega)
            (deg_line P L C u) ((reach_iff_yNode hDeg hAllReach (deg_line P L C u)).mp hureach)
          refine ⟨u, hyu, huN, ?_⟩
          rcases hTo with huT | huWire
          · simp only [T, Finset.mem_filter] at huT
            cases hopt : stFinal.2.1 (P + u.val) with
            | none =>
              have hev := hu_spec.2
              rw [hopt] at hev
              exact hev.symm
            | some w => rw [hopt] at huT; simp at huT
          · cases hopt : stFinal.2.1 (P + u.val) with
            | none =>
              have hev := hu_spec.2
              rw [hopt] at hev
              exact hev.symm
            | some w =>
              have hev := hu_spec.2
              rw [hopt] at hev
              simp only [o, huN, ite_true, hopt, Option.getD_some, D, runWires_eq] at huWire
              rw [← hev]; exact huWire
        · exfalso
          rcases hTo with huT | huWire
          · simp only [T, Finset.mem_filter] at huT; exact huN huT.1
          · simp only [o, huN, ite_false, D, runWires_eq] at huWire
            have hdead := evalOpt_dead stFinal.1 x hFinalBound
            simp only [evalOpt] at hdead
            rw [hdead] at huWire; simp at huWire
    · let u0 : Fin L := ⟨C.output - P, by omega⟩
      have hu0_eq : C.output = P + u0.val := by simp [u0]; omega
      have hreach_eq : ∀ a b, Reach P L C a b → b = C.output → a = C.output := by
        intro a b hr
        induction hr with
        | refl => intro h; exact h
        | tail _ hstep _ =>
          intro h
          rcases hstep with ⟨_, i, heq, _⟩
          omega
      have hN_eq : N = {u0} := by
        ext w
        simp only [Finset.mem_singleton, hN]
        constructor
        · intro hr
          have := hreach_eq _ _ hr rfl
          exact Fin.ext (by omega)
        · rintro rfl
          rw [← hu0_eq]; exact Relation.ReflTransGen.refl
      refine ⟨⟨[], 0⟩, {u0}, fun _ => P, ?_, ?_, ?_, ?_⟩
      · intro g hg; simp at hg
      · intro g hg; simp at hg
      · simp [Circuit.size, hN_eq]
      · intro x y
        change val C x y C.output = (val0 C L x C.output || _)
        rw [hu0_eq, val_line, val0, val_line, Bool.false_or]
        have hfalse : (({ gates := [], output := 0 } : Circuit).wires (List.ofFn x)).getD P false = false := by
          rw [runWires_eq]
          exact runWires_getD_ge [] (List.ofFn x) (by simp)
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, Finset.mem_singleton]
        constructor
        · intro hy
          exact ⟨u0, hy, Or.inl rfl⟩
        · rintro ⟨u, hyu, rfl | hw⟩
          · exact hyu
          · rw [hfalse] at hw; simp at hw

end PEqualNP.Outside.L_meta_738_aux

theorem PEqualNP.Outside.L_meta_738 :
    ∀ (P1 L1 : ℕ) (C1 : PEqualNP.CircuitLowerBounds.Circuit) (N1 : Finset (Fin L1)), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C1 → (∀ g1 ∈ C1.gates, g1.inputs.length ≤ 2) → PEqualNP.CircuitLowerBounds.HasLineDegree (P1 + L1) (Finset.Ico P1 (P1 + L1)) C1 1 → (∀ j1 : Fin C1.gates.length, Relation.ReflTransGen (fun a1 b1 : ℕ => a1 < b1 ∧ ∃ i1 : Fin C1.gates.length, b1 = P1 + L1 + i1.val ∧ a1 ∈ (C1.gates.get i1).inputs) (P1 + L1 + j1.val) C1.output) → (∀ w1 : Fin L1, w1 ∈ N1 ↔ Relation.ReflTransGen (fun r1 s1 : ℕ => r1 < s1 ∧ ∃ k1 : Fin C1.gates.length, s1 = P1 + L1 + k1.val ∧ r1 ∈ (C1.gates.get k1).inputs) (P1 + w1.val) C1.output) → ∃ (D1 : PEqualNP.CircuitLowerBounds.Circuit) (T1 : Finset (Fin L1)) (o1 : Fin L1 → ℕ), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit D1 ∧ (∀ h1 ∈ D1.gates, h1.inputs.length ≤ 2) ∧ D1.size + N1.card ≤ C1.size + 1 ∧ ∀ (x1 : Fin P1 → Bool) (y1 : Fin L1 → Bool), C1.eval (List.ofFn x1 ++ List.ofFn y1) = (C1.eval (List.ofFn x1 ++ List.ofFn (fun v1 : Fin L1 => false)) || decide (∃ u1 : Fin L1, y1 u1 = true ∧ (u1 ∈ T1 ∨ (D1.wires (List.ofFn x1)).getD (o1 u1) false = true))) :=
  PEqualNP.Outside.L_meta_738_aux.main_proof
