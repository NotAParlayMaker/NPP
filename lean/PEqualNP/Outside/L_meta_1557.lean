import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1557

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


lemma main (gs : List Gate) (n : ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (j : ℕ) (hj : j < gs.length) :
    (∃ a : Fin gs.length, (gs.get a).op = GateOp.and ∧
      ∀ T : Finset (Fin gs.length), (⟨j, hj⟩ : Fin gs.length) ∈ T →
        (∀ i ∈ T, ∀ g' : Fin gs.length, n + (g' : ℕ) ∈ (gs.get i).inputs → g' < i → g' ∈ T) → a ∈ T) ∨
    (∀ x : Fin n → Bool, val gs n x (n + j) = true →
      ∃ v : Fin n, x v = true ∧ ∀ y : Fin n → Bool, y v = true → val gs n y (n + j) = true) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rcases (hg _ (List.getElem_mem hj)).1 with hop | hop
    · left
      exact ⟨⟨j, hj⟩, hop, fun T hT _ => hT⟩
    · by_cases hex : ∃ k, ∃ hk : k < j, n + k ∈ (gs[j]).inputs ∧
          ∃ a : Fin gs.length, (gs.get a).op = GateOp.and ∧
          ∀ T : Finset (Fin gs.length), (⟨k, hk.trans hj⟩ : Fin gs.length) ∈ T →
          (∀ i ∈ T, ∀ g' : Fin gs.length, n + (g' : ℕ) ∈ (gs.get i).inputs → g' < i → g' ∈ T) → a ∈ T
      · obtain ⟨k, hk, hin, a, ha, haT⟩ := hex
        left
        refine ⟨a, ha, fun T hT hcl => haT T ?_ hcl⟩
        exact hcl ⟨j, hj⟩ hT ⟨k, hk.trans hj⟩ hin hk
      · right
        intro x hx
        rw [val_key gs n j hj, hop] at hx
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hx
        obtain ⟨b, ⟨i, hi, rfl⟩, hb⟩ := hx
        obtain ⟨hlt, hv⟩ := (ite_val _ _).mp hb
        have up : ∀ y : Fin n → Bool, val gs n y i = true → val gs n y (n + j) = true := by
          intro y hy
          rw [val_key gs n j hj, hop]
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
          exact ⟨_, ⟨i, hi, rfl⟩, (ite_val _ _).mpr ⟨hlt, hy⟩⟩
        by_cases hin : i < n
        · refine ⟨⟨i, hin⟩, ?_, fun y hy => up y ?_⟩
          · rw [val_in gs n i hin] at hv; exact hv
          · rw [val_in gs n i hin]; exact hy
        · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
          have hk : k < j := by omega
          rcases ih k hk (hk.trans hj) with h | h
          · exact absurd ⟨k, hk, hi, h⟩ hex
          · obtain ⟨v, hxv, hv'⟩ := h x hv
            exact ⟨v, hxv, fun y hy => up y (hv' y hy)⟩

lemma pin (n : ℕ) (L M : Finset (Fin n)) (m : Fin n) (B : Fin n → Finset (Fin n))
    (f : (Fin n → Bool) → Bool) (q : Fin n)
    (hLM : L ∩ M = {m}) (hB : ∀ r ∈ L, B r ∩ L = ∅) (hq : q ∈ L)
    (h1 : f (fun v : Fin n => decide (v ∉ L)) = false)
    (h2 : f (fun v : Fin n => decide (v ∉ M)) = false)
    (h : ∃ v : Fin n, (fun v : Fin n => decide (v = q ∨ v ∈ B q)) v = true ∧
      ∀ y : Fin n → Bool, y v = true → f y = true) : q = m := by
  obtain ⟨v, hv, hy⟩ := h
  have hvL : v ∈ L := by
    by_contra hc
    have := hy (fun v : Fin n => decide (v ∉ L)) (by simpa using hc)
    rw [h1] at this
    exact absurd this (by simp)
  have hvM : v ∈ M := by
    by_contra hc
    have := hy (fun v : Fin n => decide (v ∉ M)) (by simpa using hc)
    rw [h2] at this
    exact absurd this (by simp)
  have hvq : v = q := by
    simp only [decide_eq_true_eq] at hv
    rcases hv with hv | hv
    · exact hv
    · have : v ∈ B q ∩ L := Finset.mem_inter.mpr ⟨hv, hvL⟩
      rw [hB q hq] at this
      exact absurd this (Finset.notMem_empty _)
    
  subst hvq
  have : v ∈ L ∩ M := Finset.mem_inter.mpr ⟨hvL, hvM⟩
  rw [hLM] at this
  exact Finset.mem_singleton.mp this

end PEqualNP.Outside.L_meta_1557

theorem PEqualNP.Outside.L_meta_1557 : ∀ (n : ℕ) (L M : Finset (Fin n)) (m : Fin n) (B : Fin n → Finset (Fin n))
    (gates : List PEqualNP.CircuitLowerBounds.Gate) (g : Fin gates.length) (q q' : Fin n),
    L ∩ M = {m} → (∀ r ∈ L, B r ∩ L = ∅) →
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    q ∈ L → q' ∈ L → q ≠ q' →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ L))) = false →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ M))) = false →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v = q ∨ v ∈ B q))) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v = q' ∨ v ∈ B q'))) = true →
    ∃ a : Fin gates.length, (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      ∀ T : Finset (Fin gates.length), g ∈ T →
        (∀ i ∈ T, ∀ g' : Fin gates.length, n + (g' : ℕ) ∈ (gates.get i).inputs → g' < i → g' ∈ T) → a ∈ T := by
  intro n L M m B gates g q q' hLM hB hg hq hq' hne h1 h2 h3 h4
  have e : ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn x)
      = PEqualNP.Outside.L_meta_1557.val gates n x (n + (g : ℕ)) := fun x => rfl
  rw [e] at h1 h2 h3 h4
  rcases PEqualNP.Outside.L_meta_1557.main gates n hg g.1 g.2 with h | h
  · exact h
  · exfalso
    apply hne
    rw [PEqualNP.Outside.L_meta_1557.pin n L M m B (fun x => PEqualNP.Outside.L_meta_1557.val gates n x (n + (g : ℕ))) q hLM hB hq h1 h2 (h _ h3),
      PEqualNP.Outside.L_meta_1557.pin n L M m B (fun x => PEqualNP.Outside.L_meta_1557.val gates n x (n + (g : ℕ))) q' hLM hB hq' h1 h2 (h _ h4)]
