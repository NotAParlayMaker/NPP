import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1577

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_prefix (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, step_length, List.length_cons]
    omega

lemma fold_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by rw [step_length]; omega)]
    exact step_prefix w g i hi

lemma fold_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl step w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      rw [fold_prefix gs (step w g) (w.length + 0) (by rw [step_length]; omega)]
      have h0 : (step w g).getD (w.length + 0) false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [step, List.getD_eq_getElem?_getD]
      rw [h0]
      simp only [List.getElem_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases h : i < w.length
      · have h' : i < w.length + 0 := by omega
        simp only [h', ite_true]
        rw [fold_prefix gs (step w g) i (by rw [step_length]; omega)]
        exact (step_prefix w g i h).symm
      · have h' : ¬ i < w.length + 0 := by omega
        simp only [h', ite_false]
        exact List.getD_eq_default _ _ (by omega)
    | succ j =>
      have h := ih (step w g) j (by simpa using hj)
      rw [step_length] at h
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact h

def val (gs : List Gate) (n : ℕ) (x : Fin n → Bool) (t : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD t false

def ins (gs : List Gate) (n : ℕ) (t : ℕ) : Finset ℕ :=
  match gs[t - n]? with
  | some g => g.inputs.toFinset.filter (fun i => i < t)
  | none => ∅

def ind {n : ℕ} (Z : Finset (Fin n)) : Fin n → Bool := fun p => decide (p ∈ Z)

lemma ind_true {n : ℕ} (Z : Finset (Fin n)) (p : Fin n) : ind Z p = true ↔ p ∈ Z := by
  simp [ind]

lemma ind_weight {n : ℕ} (Z : Finset (Fin n)) :
    (Finset.univ.filter (fun i : Fin n => ind Z i = true)).card = Z.card := by
  congr 1
  ext p
  simp [ind]

lemma val_in (gs : List Gate) (n : ℕ) (t : ℕ) (h : t < n) (x : Fin n → Bool) :
    val gs n x t = x ⟨t, h⟩ := by
  unfold val
  rw [fold_prefix _ _ t (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

lemma val_out (gs : List Gate) (n : ℕ) (t : ℕ) (h : n + gs.length ≤ t) (x : Fin n → Bool) :
    val gs n x t = false := by
  unfold val
  apply List.getD_eq_default
  rw [fold_length, List.length_ofFn]
  exact h

lemma ins_lt (gs : List Gate) (n : ℕ) (t : ℕ) : ∀ i ∈ ins gs n t, i < t := by
  intro i hi
  unfold ins at hi
  split at hi
  · exact (Finset.mem_filter.mp hi).2
  · simp at hi

lemma val_key (gs : List Gate) (n : ℕ) (j : ℕ) (hj : j < gs.length) (z : Fin n → Bool) :
    val gs n z (n + j) =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < n + j then val gs n z i else false) := by
  have h := fold_gate gs (List.ofFn z) j hj
  rw [List.length_ofFn] at h
  exact h

lemma ite_val (b : Prop) [Decidable b] (u : Bool) :
    (if b then u else false) = true ↔ b ∧ u = true := by
  by_cases h : b <;> simp [h]

lemma val_dep (gs : List Gate) (n : ℕ)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (t : ℕ) (h1 : n ≤ t) (h2 : t < n + gs.length) (x y : Fin n → Bool)
    (H : ∀ i ∈ ins gs n t, val gs n y i = true → val gs n x i = true)
    (hy : val gs n y t = true) : val gs n x t = true := by
  obtain ⟨j, rfl⟩ : ∃ j, t = n + j := ⟨t - n, by omega⟩
  have hj : j < gs.length := by omega
  have hgt : gs[n + j - n]? = some gs[j] := by
    rw [show n + j - n = j by omega]
    exact List.getElem?_eq_getElem hj
  have hmem : ∀ i ∈ (gs[j]).inputs, i < n + j → i ∈ ins gs n (n + j) := by
    intro i hi hlt
    unfold ins
    rw [hgt]
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hi, hlt⟩
  have hstep : ∀ i ∈ (gs[j]).inputs,
      (if i < n + j then val gs n y i else false) = true →
      (if i < n + j then val gs n x i else false) = true := by
    intro i hi hh
    rw [ite_val] at hh ⊢
    exact ⟨hh.1, H i (hmem i hi hh.1) hh.2⟩
  rw [val_key gs n j hj] at hy ⊢
  rcases hg _ (List.getElem_mem hj) with hop | hop
  · rw [hop] at hy ⊢
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at hy ⊢
    rintro b ⟨i, hi, rfl⟩
    exact hstep i hi (hy _ ⟨i, hi, rfl⟩)
  · rw [hop] at hy ⊢
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hy ⊢
    obtain ⟨b, ⟨i, hi, rfl⟩, hb⟩ := hy
    exact ⟨_, ⟨i, hi, rfl⟩, hstep i hi hb⟩

lemma mono (gs : List Gate) (n : ℕ)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ p, y p = true → x p = true) :
    ∀ t, val gs n y t = true → val gs n x t = true := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro h
    by_cases h1 : t < n
    · rw [val_in gs n t h1] at h ⊢
      exact hxy _ h
    · by_cases h2 : t < n + gs.length
      · exact val_dep gs n hg t (by omega) h2 x y
          (fun i hi => ih i (ins_lt gs n t i hi)) h
      · rw [val_out gs n t (by omega)] at h
        exact absurd h (by simp)

def Closed (gs : List Gate) (S : Set ℕ) : Prop :=
  ∀ i : Fin gs.length, 13 + (i : ℕ) ∈ S → (gs.get i).op = GateOp.or →
    ∀ a ∈ (gs.get i).inputs, a ∈ S

def Cone (gs : List Gate) (h u : ℕ) : Prop :=
  ∀ S : Set ℕ, h ∈ S → Closed gs S → u ∈ S

def IsAnd (gs : List Gate) (A : ℕ) : Prop :=
  ∃ i : Fin gs.length, A = 13 + (i : ℕ) ∧ (gs.get i).op = GateOp.and

lemma or_val (gs : List Gate) (i : Fin gs.length) (hop : (gs.get i).op = GateOp.or)
    (hin : ∀ a ∈ (gs.get i).inputs, a < 13 + (i : ℕ)) (x : Fin 13 → Bool) :
    val gs 13 x (13 + (i : ℕ)) = true ↔ ∃ a ∈ (gs.get i).inputs, val gs 13 x a = true := by
  rw [val_key gs 13 i i.2]
  have e : gs[(i : ℕ)] = gs.get i := rfl
  rw [e, hop]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
  constructor
  · rintro ⟨b, ⟨a, ha, rfl⟩, hb⟩
    exact ⟨a, ha, ((ite_val _ _).mp hb).2⟩
  · rintro ⟨a, ha, hv⟩
    exact ⟨_, ⟨a, ha, rfl⟩, (ite_val _ _).mpr ⟨hin a ha, hv⟩⟩

lemma and_val (gs : List Gate) (i : Fin gs.length) (hop : (gs.get i).op = GateOp.and)
    (hin : ∀ a ∈ (gs.get i).inputs, a < 13 + (i : ℕ)) (x : Fin 13 → Bool) :
    val gs 13 x (13 + (i : ℕ)) = true ↔ ∀ a ∈ (gs.get i).inputs, val gs 13 x a = true := by
  rw [val_key gs 13 i i.2]
  have e : gs[(i : ℕ)] = gs.get i := rfl
  rw [e, hop]
  simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
  constructor
  · intro h a ha
    exact ((ite_val _ _).mp (h _ ⟨a, ha, rfl⟩)).2
  · rintro h b ⟨a, ha, rfl⟩
    exact (ite_val _ _).mpr ⟨hin a ha, h a ha⟩

lemma descend (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gs.length, 1 ≤ (gs.get i).inputs.length ∧
      ∀ a ∈ (gs.get i).inputs, a < 13 + (i : ℕ))
    (x z1 z2 : Fin 13 → Bool) :
    ∀ w, w < 13 + gs.length → val gs 13 x w = true → val gs 13 z1 w = false →
      val gs 13 z2 w = false →
      ∃ u, u ≤ w ∧ Cone gs w u ∧ val gs 13 x u = true ∧ val gs 13 z1 u = false ∧
        val gs 13 z2 u = false ∧ (u < 13 ∨ IsAnd gs u) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hx h1 h2
    by_cases hlt : w < 13
    · exact ⟨w, le_rfl, fun S hS _ => hS, hx, h1, h2, Or.inl hlt⟩
    · obtain ⟨j, rfl⟩ : ∃ j, w = 13 + j := ⟨w - 13, by omega⟩
      have hj : j < gs.length := by omega
      rcases (hg _ (List.get_mem gs ⟨j, hj⟩)).1 with hop | hop
      · exact ⟨13 + j, le_rfl, fun S hS _ => hS, hx, h1, h2, Or.inr ⟨⟨j, hj⟩, rfl, hop⟩⟩
      · have hi : ∀ a ∈ (gs.get ⟨j, hj⟩).inputs, a < 13 + j := (hin ⟨j, hj⟩).2
        obtain ⟨a, ha, hax⟩ := (or_val gs ⟨j, hj⟩ hop hi x).mp hx
        have f1 : val gs 13 z1 a = false := by
          by_contra hc
          rw [Bool.not_eq_false] at hc
          have := (or_val gs ⟨j, hj⟩ hop hi z1).mpr ⟨a, ha, hc⟩
          exact Bool.noConfusion (this.symm.trans h1)
        have f2 : val gs 13 z2 a = false := by
          by_contra hc
          rw [Bool.not_eq_false] at hc
          have := (or_val gs ⟨j, hj⟩ hop hi z2).mpr ⟨a, ha, hc⟩
          exact Bool.noConfusion (this.symm.trans h2)
        have hal := hi a ha
        obtain ⟨u, hu, hc, r1, r2, r3, r4⟩ := ih a hal (by omega) hax f1 f2
        exact ⟨u, by omega, fun S hS hcl => hc S (hcl ⟨j, hj⟩ hS hop a ha) hcl, r1, r2, r3, r4⟩

def Lc (t : Fin 13) : Finset (Fin 13) := {t, t + 1, t + 3, t + 9}

lemma comb : ∀ t p q : Fin 13, t ≠ 0 → p ∈ Lc 0 → q ∈ Lc 0 → p ≠ q → p ∈ Lc t → q ∈ Lc t → False := by
  unfold Lc
  decide

lemma ev (gs : List Gate) (w : ℕ) (x : Fin 13 → Bool) :
    Circuit.eval ⟨gs, w⟩ (List.ofFn x) = val gs 13 x w := rfl

end PEqualNP.Outside.L_meta_1577

theorem PEqualNP.Outside.L_meta_1577 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : ℕ) (t : Fin 13),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length ∧ ∀ a ∈ (gates.get i).inputs, a < 13 + (i : ℕ)) → t ≠ 0 →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false →
    2 ≤ ((L 0).filter (fun p => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, g⟩ (List.ofFn (fun v : Fin 13 => decide (v = p ∨ ((p = 3 ∨ p = 9) ∧ v ∉ L 0)))) = true)).card →
    ∃ Y : ℕ, (∀ S : Set ℕ, g ∈ S → (∀ i : Fin gates.length, 13 + (i : ℕ) ∈ S → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ a ∈ (gates.get i).inputs, a ∈ S) → Y ∈ S) ∧ (∃ i : Fin gates.length, Y = 13 + (i : ℕ) ∧ (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L 0))) = false ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v ∉ L t))) = false ∧
      ∃ s : Fin 13, (s = 3 ∨ s = 9) ∧ s ∉ L t ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, Y⟩ (List.ofFn (fun v : Fin 13 => decide (v = s ∨ ((s = 3 ∨ s = 9) ∧ v ∉ L 0)))) = true := by
  intro L hL gates g t hg hin ht e0 et hcard
  have hLc : L = PEqualNP.Outside.L_meta_1577.Lc := funext hL
  subst hLc
  simp only [PEqualNP.Outside.L_meta_1577.ev] at e0 et ⊢
  have hg' : ∀ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or := fun g h => (hg g h).1
  have key1 : ∀ p : Fin 13, PEqualNP.Outside.L_meta_1577.val gates 13 (fun v : Fin 13 => decide (v = p ∨ ((p = 3 ∨ p = 9) ∧ v ∉ PEqualNP.Outside.L_meta_1577.Lc 0))) g = true →
      p ∉ PEqualNP.Outside.L_meta_1577.Lc t → (p = 3 ∨ p = 9) := by
    intro p hp hpt
    by_contra hne
    have := PEqualNP.Outside.L_meta_1577.mono gates 13 hg' (fun v : Fin 13 => decide (v ∉ PEqualNP.Outside.L_meta_1577.Lc t)) _ (by
      intro v hv
      simp only [decide_eq_true_eq] at hv ⊢
      rcases hv with rfl | ⟨h, _⟩
      · exact hpt
      · exact absurd h hne) g hp
    rw [et] at this
    exact Bool.noConfusion this
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hcard
  rw [Finset.mem_filter] at hp hq
  simp only [PEqualNP.Outside.L_meta_1577.ev] at hp hq
  have ex : ∃ s : Fin 13, s ∉ PEqualNP.Outside.L_meta_1577.Lc t ∧ PEqualNP.Outside.L_meta_1577.val gates 13 (fun v : Fin 13 => decide (v = s ∨ ((s = 3 ∨ s = 9) ∧ v ∉ PEqualNP.Outside.L_meta_1577.Lc 0))) g = true := by
    by_cases h1 : p ∈ PEqualNP.Outside.L_meta_1577.Lc t
    · exact ⟨q, fun h2 => PEqualNP.Outside.L_meta_1577.comb t p q ht hp.1 hq.1 hpq h1 h2, hq.2⟩
    · exact ⟨p, h1, hp.2⟩
  obtain ⟨s, hst, hsv⟩ := ex
  have hs39 := key1 s hsv hst
  have hglt : g < 13 + gates.length := by
    by_contra hc
    rw [PEqualNP.Outside.L_meta_1577.val_out gates 13 g (by omega)] at hsv
    exact Bool.noConfusion hsv
  obtain ⟨u, _, hcone, r1, r2, r3, r4⟩ := PEqualNP.Outside.L_meta_1577.descend gates hg hin _ _ _ g hglt hsv e0 et
  rcases r4 with hu | hand
  · exfalso
    rw [PEqualNP.Outside.L_meta_1577.val_in gates 13 u hu] at r1 r2 r3
    simp only [decide_eq_true_eq, decide_eq_false_iff_not, not_not] at r1 r2 r3
    rcases r1 with h | ⟨_, h⟩
    · exact hst (h ▸ r3)
    · exact h r2
  · exact ⟨u, hcone, hand, r2, r3, s, hs39, hst, r1⟩
