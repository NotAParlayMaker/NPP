import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3010

def remap (σ : Equiv.Perm (Fin 14)) (w : ℕ) : ℕ :=
  if h : w < 14 then (σ ⟨w, h⟩).val else w

def remapGate (σ : Equiv.Perm (Fin 14)) (g : PEqualNP.CircuitLowerBounds.Gate) : PEqualNP.CircuitLowerBounds.Gate :=
  ⟨g.op, g.inputs.map (remap σ)⟩

lemma remap_lt14 (σ : Equiv.Perm (Fin 14)) (w : ℕ) (h : w < 14) : remap σ w < 14 := by
  unfold remap
  rw [dite_eq_left h]
  exact (σ ⟨w, h⟩).isLt

lemma remap_lt15 (σ : Equiv.Perm (Fin 14)) (w : ℕ) (h : w < 15) : remap σ w < 15 := by
  unfold remap
  by_cases h14 : w < 14
  · rw [dite_eq_left h14]
    have := (σ ⟨w, h14⟩).isLt
    omega
  · rw [dite_eq_right h14]
    exact h

lemma remap_inj (σ : Equiv.Perm (Fin 14)) {u v : ℕ} (h : remap σ u = remap σ v) : u = v := by
  unfold remap at h
  by_cases hu : u < 14 <;> by_cases hv : v < 14
  · rw [dite_eq_left hu, dite_eq_left hv] at h
    have hfin : σ ⟨u, hu⟩ = σ ⟨v, hv⟩ := Fin.ext h
    have hinj := σ.injective hfin
    exact congrArg Fin.val hinj
  · rw [dite_eq_left hu, dite_eq_right hv] at h
    have := (σ ⟨u, hu⟩).isLt
    omega
  · rw [dite_eq_right hu, dite_eq_left hv] at h
    have := (σ ⟨v, hv⟩).isLt
    omega
  · rw [dite_eq_right hu, dite_eq_right hv] at h
    exact h

lemma remap_mul (τ σ : Equiv.Perm (Fin 14)) (w : ℕ) : remap τ (remap σ w) = remap (τ * σ) w := by
  unfold remap
  by_cases hw : w < 14
  · rw [dite_eq_left hw, dite_eq_left hw]
    have hlt : (σ ⟨w, hw⟩).val < 14 := (σ ⟨w, hw⟩).isLt
    rw [dite_eq_left hlt]
    rfl
  · rw [dite_eq_right hw, dite_eq_right hw, dite_eq_right hw]

lemma remap_fin15 (σ : Equiv.Perm (Fin 14)) (i : Fin 15) :
    (if i.val < 14 then (σ (Fin.ofNat 14 i.val)).val else 14) = remap σ i.val := by
  unfold remap
  by_cases h : i.val < 14
  · rw [ite_eq_left h, dite_eq_left h]
    congr 2
    apply Fin.ext
    simp [Nat.mod_eq_of_lt h]
  · rw [ite_eq_right h, dite_eq_right h]
    omega

lemma eval_comm (op : PEqualNP.CircuitLowerBounds.GateOp)
    (hop : op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or)
    (a b : Bool) : op.eval [a, b] = op.eval [b, a] := by
  rcases hop with rfl | rfl
  · simp [PEqualNP.CircuitLowerBounds.GateOp.eval, Bool.and_comm]
  · simp [PEqualNP.CircuitLowerBounds.GateOp.eval, Bool.or_comm]

lemma foldl_wires_remap (σ : Equiv.Perm (Fin 14)) (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (w1 w2 : List Bool) (hlen : w1.length = w2.length) (h14 : 14 ≤ w1.length)
    (heq : ∀ k, w1.getD k false = w2.getD (remap σ k) false) :
    ∀ k, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w1).getD k false =
      ((gs.map (remapGate σ)).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w2).getD (remap σ k) false := by
  induction gs generalizing w1 w2 with
  | nil => exact heq
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hmap : (g.inputs.map fun i => w1.getD i false) =
        ((remapGate σ g).inputs.map fun i => w2.getD i false) := by
      simp only [remapGate, List.map_map]
      apply List.map_congr_left
      intro i _
      exact heq i
    have hv : g.op.eval (g.inputs.map fun i => w1.getD i false) =
        (remapGate σ g).op.eval ((remapGate σ g).inputs.map fun i => w2.getD i false) := by
      simp only [remapGate, hmap]
    apply ih
    · simp [hlen]
    · simp only [List.length_append, List.length_singleton]; omega
    · intro k
      rw [hv]
      by_cases hlt : k < w1.length
      · have hlt2 : remap σ k < w2.length := by
          by_cases hk14 : k < 14
          · have := remap_lt14 σ k hk14; omega
          · unfold remap; rw [dite_eq_right hk14]; omega
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_left hlt, List.getElem?_append_left hlt2]
        have := heq k
        rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at this
      · have hk14 : ¬ k < 14 := by omega
        have hrm : remap σ k = k := by unfold remap; rw [dite_eq_right hk14]
        have hle1 : w1.length ≤ k := by omega
        have hle2 : w2.length ≤ remap σ k := by omega
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_append_right hle1, List.getElem?_append_right hle2, hrm, hlen]

end PEqualNP.Outside.L_meta_3010

theorem PEqualNP.Outside.L_meta_3010 :
    ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       (2 : ℕ) ≤ x2.size →         x2.size ≤ (26 : ℕ) →           (∀ (x7 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7) →             have x8 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x8 x9 x10 x11 : ℕ) => ((15 : ℕ) * Min.min x8 x9 + Max.max x8 x9) * (225 : ℕ) + ((15 : ℕ) * Min.min x10 x11 + Max.max x10 x11);             have x9 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x9 : Equiv.Perm (Fin (14 : ℕ))) (x10 : Fin (15 : ℕ)) => if ↑x10 < (14 : ℕ) then ↑(x9 (Fin.ofNat (14 : ℕ) ↑x10)) else (14 : ℕ);             ∃ (x10 : Fin (14 : ℕ)) (x11 : Fin (14 : ℕ)) (x12 : Fin (15 : ℕ)) (x13 : Fin (15 : ℕ)) (x14 : PEqualNP.CircuitLowerBounds.GateOp) (x15 : PEqualNP.CircuitLowerBounds.GateOp) (x16 : PEqualNP.CircuitLowerBounds.Circuit),               x10 < x11 ∧                 x12 < x13 ∧                   (x14 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                     (x15 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                       (∀ (x17 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x18 : Fin (14 : ℕ) → Bool), x1 (x18 ∘ ⇑x17) = x1 x18) → x8 ↑x10 ↑x11 ↑x12 ↑x13 ≤ x8 (↑(x17 x10)) (↑(x17 x11)) (x9 x17 x12) (x9 x17 x13)) ∧                         PEqualNP.MetaComplexity.Monotone2 x16 ∧                           x16.size ≤ (24 : ℕ) ∧                             ∀ (x17 : Fin (14 : ℕ) → Bool),                               have x18 : List Bool := List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]];                               x16.eval (x18 ++ [x15.eval [x18.getD (↑x12) Bool.false, x18.getD (↑x13) Bool.false]]) = x1 x17 := by
  classical
  intro x1 x2 hao hnodup hge2 hle26 heval x8 x9
  rcases hao with ⟨handor, hrb, hlen2⟩
  match hgates : x2.gates with
  | [] => simp [PEqualNP.CircuitLowerBounds.Circuit.size, hgates] at hge2
  | [_] => simp [PEqualNP.CircuitLowerBounds.Circuit.size, hgates] at hge2
  | g0 :: g1 :: rest =>
    have hg0_mem : g0 ∈ x2.gates := by rw [hgates]; simp
    have hg1_mem : g1 ∈ x2.gates := by rw [hgates]; simp
    have hg0_len : g0.inputs.length = 2 := hlen2 g0 hg0_mem
    have hg1_len : g1.inputs.length = 2 := hlen2 g1 hg1_mem
    obtain ⟨u0, v0, hg0_in⟩ : ∃ u0 v0, g0.inputs = [u0, v0] := by
      match h : g0.inputs with
      | [a, b] => exact ⟨a, b, rfl⟩
      | [] => simp [h] at hg0_len
      | [_] => simp [h] at hg0_len
      | _ :: _ :: _ :: _ => simp [h] at hg0_len
    obtain ⟨u1, v1, hg1_in⟩ : ∃ u1 v1, g1.inputs = [u1, v1] := by
      match h : g1.inputs with
      | [a, b] => exact ⟨a, b, rfl⟩
      | [] => simp [h] at hg1_len
      | [_] => simp [h] at hg1_len
      | _ :: _ :: _ :: _ => simp [h] at hg1_len
    have hu0v0 : u0 ≠ v0 := by
      have hnd := hnodup g0 hg0_mem
      rw [hg0_in] at hnd
      simpa using hnd
    have hu1v1 : u1 ≠ v1 := by
      have hnd := hnodup g1 hg1_mem
      rw [hg1_in] at hnd
      simpa using hnd
    have hrb0 := hrb 0 (by rw [hgates]; simp)
    have hrb1 := hrb 1 (by rw [hgates]; simp)
    have hg0_at : PEqualNP.MetaComplexity.NestedCover.gateAt x2 0 = g0 := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hgates]
    have hg1_at : PEqualNP.MetaComplexity.NestedCover.gateAt x2 1 = g1 := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hgates]
    have hu0_lt : u0 < 14 := hrb0 u0 (by rw [hg0_at, hg0_in]; simp)
    have hv0_lt : v0 < 14 := hrb0 v0 (by rw [hg0_at, hg0_in]; simp)
    have hu1_lt : u1 < 15 := hrb1 u1 (by rw [hg1_at, hg1_in]; simp)
    have hv1_lt : v1 < 15 := hrb1 v1 (by rw [hg1_at, hg1_in]; simp)
    let G : Finset (Equiv.Perm (Fin 14)) :=
      Finset.univ.filter fun σ => ∀ z : Fin 14 → Bool, x1 (z ∘ σ) = x1 z
    have h1G : (1 : Equiv.Perm (Fin 14)) ∈ G := by
      simp [G]
    let score : Equiv.Perm (Fin 14) → ℕ :=
      fun σ => x8 (PEqualNP.Outside.L_meta_3010.remap σ u0) (PEqualNP.Outside.L_meta_3010.remap σ v0)
        (PEqualNP.Outside.L_meta_3010.remap σ u1) (PEqualNP.Outside.L_meta_3010.remap σ v1)
    obtain ⟨σ, hσG, hσmin⟩ := Finset.exists_min_image G score ⟨1, h1G⟩
    have hσ_sym : ∀ z : Fin 14 → Bool, x1 (z ∘ σ) = x1 z := (Finset.mem_filter.mp hσG).2
    let a : Fin 14 := ⟨min (PEqualNP.Outside.L_meta_3010.remap σ u0) (PEqualNP.Outside.L_meta_3010.remap σ v0),
      lt_of_le_of_lt (min_le_left _ _) (PEqualNP.Outside.L_meta_3010.remap_lt14 σ u0 hu0_lt)⟩
    let b : Fin 14 := ⟨max (PEqualNP.Outside.L_meta_3010.remap σ u0) (PEqualNP.Outside.L_meta_3010.remap σ v0),
      max_lt (PEqualNP.Outside.L_meta_3010.remap_lt14 σ u0 hu0_lt) (PEqualNP.Outside.L_meta_3010.remap_lt14 σ v0 hv0_lt)⟩
    let c : Fin 15 := ⟨min (PEqualNP.Outside.L_meta_3010.remap σ u1) (PEqualNP.Outside.L_meta_3010.remap σ v1),
      lt_of_le_of_lt (min_le_left _ _) (PEqualNP.Outside.L_meta_3010.remap_lt15 σ u1 hu1_lt)⟩
    let d : Fin 15 := ⟨max (PEqualNP.Outside.L_meta_3010.remap σ u1) (PEqualNP.Outside.L_meta_3010.remap σ v1),
      max_lt (PEqualNP.Outside.L_meta_3010.remap_lt15 σ u1 hu1_lt) (PEqualNP.Outside.L_meta_3010.remap_lt15 σ v1 hv1_lt)⟩
    let C' : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨rest.map (PEqualNP.Outside.L_meta_3010.remapGate σ), PEqualNP.Outside.L_meta_3010.remap σ x2.output⟩
    refine ⟨a, b, c, d, g0.op, g1.op, C', ?_, ?_, handor g0 hg0_mem, handor g1 hg1_mem, ?_, ?_, ?_, ?_⟩
    · show a.val < b.val
      dsimp only [a, b]
      have hne : PEqualNP.Outside.L_meta_3010.remap σ u0 ≠ PEqualNP.Outside.L_meta_3010.remap σ v0 :=
        fun h => hu0v0 (PEqualNP.Outside.L_meta_3010.remap_inj σ h)
      omega
    · show c.val < d.val
      dsimp only [c, d]
      have hne : PEqualNP.Outside.L_meta_3010.remap σ u1 ≠ PEqualNP.Outside.L_meta_3010.remap σ v1 :=
        fun h => hu1v1 (PEqualNP.Outside.L_meta_3010.remap_inj σ h)
      omega
    · intro τ hτ_sym
      have hτσG : τ * σ ∈ G := by
        simp only [G, Finset.mem_filter, Finset.mem_univ, true_and]
        intro z
        change x1 ((z ∘ τ) ∘ σ) = x1 z
        rw [hσ_sym (z ∘ τ), hτ_sym z]
      have hle := hσmin (τ * σ) hτσG
      have hab_eq : (15 * min a.val b.val + max a.val b.val) =
          (15 * min (PEqualNP.Outside.L_meta_3010.remap σ u0) (PEqualNP.Outside.L_meta_3010.remap σ v0) +
           max (PEqualNP.Outside.L_meta_3010.remap σ u0) (PEqualNP.Outside.L_meta_3010.remap σ v0)) := by
        simp only [a, b]
        omega
      have hcd_eq : (15 * min c.val d.val + max c.val d.val) =
          (15 * min (PEqualNP.Outside.L_meta_3010.remap σ u1) (PEqualNP.Outside.L_meta_3010.remap σ v1) +
           max (PEqualNP.Outside.L_meta_3010.remap σ u1) (PEqualNP.Outside.L_meta_3010.remap σ v1)) := by
        simp only [c, d]
        omega
      have hτab : (15 * min (τ a).val (τ b).val + max (τ a).val (τ b).val) =
          (15 * min (PEqualNP.Outside.L_meta_3010.remap (τ * σ) u0) (PEqualNP.Outside.L_meta_3010.remap (τ * σ) v0) +
           max (PEqualNP.Outside.L_meta_3010.remap (τ * σ) u0) (PEqualNP.Outside.L_meta_3010.remap (τ * σ) v0)) := by
        have hτa : (τ a).val = PEqualNP.Outside.L_meta_3010.remap τ a.val := by
          unfold PEqualNP.Outside.L_meta_3010.remap
          rw [dite_eq_left a.isLt]
        have hτb : (τ b).val = PEqualNP.Outside.L_meta_3010.remap τ b.val := by
          unfold PEqualNP.Outside.L_meta_3010.remap
          rw [dite_eq_left b.isLt]
        rw [hτa, hτb]
        rcases le_total (PEqualNP.Outside.L_meta_3010.remap σ u0) (PEqualNP.Outside.L_meta_3010.remap σ v0) with h | h
        · have ha' : a.val = PEqualNP.Outside.L_meta_3010.remap σ u0 := min_eq_left h
          have hb' : b.val = PEqualNP.Outside.L_meta_3010.remap σ v0 := max_eq_right h
          rw [ha', hb', PEqualNP.Outside.L_meta_3010.remap_mul, PEqualNP.Outside.L_meta_3010.remap_mul]
        · have ha' : a.val = PEqualNP.Outside.L_meta_3010.remap σ v0 := min_eq_right h
          have hb' : b.val = PEqualNP.Outside.L_meta_3010.remap σ u0 := max_eq_left h
          rw [ha', hb', PEqualNP.Outside.L_meta_3010.remap_mul, PEqualNP.Outside.L_meta_3010.remap_mul, min_comm, max_comm]
      have hτcd : (15 * min (x9 τ c) (x9 τ d) + max (x9 τ c) (x9 τ d)) =
          (15 * min (PEqualNP.Outside.L_meta_3010.remap (τ * σ) u1) (PEqualNP.Outside.L_meta_3010.remap (τ * σ) v1) +
           max (PEqualNP.Outside.L_meta_3010.remap (τ * σ) u1) (PEqualNP.Outside.L_meta_3010.remap (τ * σ) v1)) := by
        have hτc : x9 τ c = PEqualNP.Outside.L_meta_3010.remap τ c.val := PEqualNP.Outside.L_meta_3010.remap_fin15 τ c
        have hτd : x9 τ d = PEqualNP.Outside.L_meta_3010.remap τ d.val := PEqualNP.Outside.L_meta_3010.remap_fin15 τ d
        rw [hτc, hτd]
        rcases le_total (PEqualNP.Outside.L_meta_3010.remap σ u1) (PEqualNP.Outside.L_meta_3010.remap σ v1) with h | h
        · have hc' : c.val = PEqualNP.Outside.L_meta_3010.remap σ u1 := min_eq_left h
          have hd' : d.val = PEqualNP.Outside.L_meta_3010.remap σ v1 := max_eq_right h
          rw [hc', hd', PEqualNP.Outside.L_meta_3010.remap_mul, PEqualNP.Outside.L_meta_3010.remap_mul]
        · have hc' : c.val = PEqualNP.Outside.L_meta_3010.remap σ v1 := min_eq_right h
          have hd' : d.val = PEqualNP.Outside.L_meta_3010.remap σ u1 := max_eq_left h
          rw [hc', hd', PEqualNP.Outside.L_meta_3010.remap_mul, PEqualNP.Outside.L_meta_3010.remap_mul, min_comm, max_comm]
      dsimp only [x8, score] at hle ⊢
      rw [hab_eq, hcd_eq, hτab, hτcd]
      exact hle
    · intro g hg
      rcases List.mem_map.mp hg with ⟨g', hg', rfl⟩
      have hg'mem : g' ∈ x2.gates := by rw [hgates]; simp [hg']
      refine ⟨?_, ?_⟩
      · rcases handor g' hg'mem with h | h
        · exact Or.inl h
        · exact Or.inr (Set.mem_singleton_iff.mpr h)
      · simp only [PEqualNP.Outside.L_meta_3010.remapGate, List.length_map, hlen2 g' hg'mem]
        omega
    · simp only [C', PEqualNP.CircuitLowerBounds.Circuit.size, List.length_map]
      simp only [PEqualNP.CircuitLowerBounds.Circuit.size, hgates, List.length_cons] at hle26
      omega
    · intro z w1
      have h0eq : g0.op.eval [z a, z b] =
          (PEqualNP.Outside.L_meta_3010.remapGate σ g0).op.eval
            ((PEqualNP.Outside.L_meta_3010.remapGate σ g0).inputs.map fun i => (List.ofFn z).getD i false) := by
        simp only [PEqualNP.Outside.L_meta_3010.remapGate, hg0_in, List.map]
        have hgetu : (List.ofFn z).getD (PEqualNP.Outside.L_meta_3010.remap σ u0) false =
            z ⟨PEqualNP.Outside.L_meta_3010.remap σ u0, PEqualNP.Outside.L_meta_3010.remap_lt14 σ u0 hu0_lt⟩ := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          simp [PEqualNP.Outside.L_meta_3010.remap_lt14 σ u0 hu0_lt]
        have hgetv : (List.ofFn z).getD (PEqualNP.Outside.L_meta_3010.remap σ v0) false =
            z ⟨PEqualNP.Outside.L_meta_3010.remap σ v0, PEqualNP.Outside.L_meta_3010.remap_lt14 σ v0 hv0_lt⟩ := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          simp [PEqualNP.Outside.L_meta_3010.remap_lt14 σ v0 hv0_lt]
        rw [hgetu, hgetv]
        rcases le_total (PEqualNP.Outside.L_meta_3010.remap σ u0) (PEqualNP.Outside.L_meta_3010.remap σ v0) with h | h
        · have ha' : a = ⟨PEqualNP.Outside.L_meta_3010.remap σ u0, PEqualNP.Outside.L_meta_3010.remap_lt14 σ u0 hu0_lt⟩ :=
            Fin.ext (min_eq_left h)
          have hb' : b = ⟨PEqualNP.Outside.L_meta_3010.remap σ v0, PEqualNP.Outside.L_meta_3010.remap_lt14 σ v0 hv0_lt⟩ :=
            Fin.ext (max_eq_right h)
          rw [ha', hb']
        · have ha' : a = ⟨PEqualNP.Outside.L_meta_3010.remap σ v0, PEqualNP.Outside.L_meta_3010.remap_lt14 σ v0 hv0_lt⟩ :=
            Fin.ext (min_eq_right h)
          have hb' : b = ⟨PEqualNP.Outside.L_meta_3010.remap σ u0, PEqualNP.Outside.L_meta_3010.remap_lt14 σ u0 hu0_lt⟩ :=
            Fin.ext (max_eq_left h)
          rw [ha', hb', PEqualNP.Outside.L_meta_3010.eval_comm g0.op (handor g0 hg0_mem)]
      have h1eq : g1.op.eval [w1.getD c.val false, w1.getD d.val false] =
          (PEqualNP.Outside.L_meta_3010.remapGate σ g1).op.eval
            ((PEqualNP.Outside.L_meta_3010.remapGate σ g1).inputs.map fun i => w1.getD i false) := by
        simp only [PEqualNP.Outside.L_meta_3010.remapGate, hg1_in, List.map]
        rcases le_total (PEqualNP.Outside.L_meta_3010.remap σ u1) (PEqualNP.Outside.L_meta_3010.remap σ v1) with h | h
        · have hc' : c.val = PEqualNP.Outside.L_meta_3010.remap σ u1 := min_eq_left h
          have hd' : d.val = PEqualNP.Outside.L_meta_3010.remap σ v1 := max_eq_right h
          rw [hc', hd']
        · have hc' : c.val = PEqualNP.Outside.L_meta_3010.remap σ v1 := min_eq_right h
          have hd' : d.val = PEqualNP.Outside.L_meta_3010.remap σ u1 := max_eq_left h
          rw [hc', hd', PEqualNP.Outside.L_meta_3010.eval_comm g1.op (handor g1 hg1_mem)]
      have hstep : C'.eval (w1 ++ [g1.op.eval [w1.getD c.val false, w1.getD d.val false]]) =
          ((x2.gates.map (PEqualNP.Outside.L_meta_3010.remapGate σ)).foldl
            (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn z)).getD
            (PEqualNP.Outside.L_meta_3010.remap σ x2.output) false := by
        simp only [C', PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
          hgates, List.map_cons, List.foldl_cons]
        rw [h1eq]
        have hw1 : w1 = List.ofFn z ++ [(PEqualNP.Outside.L_meta_3010.remapGate σ g0).op.eval
            ((PEqualNP.Outside.L_meta_3010.remapGate σ g0).inputs.map fun i => (List.ofFn z).getD i false)] := by
          dsimp only [w1]
          rw [h0eq]
        rw [hw1]
      rw [hstep]
      have hbase : ∀ k, (List.ofFn (z ∘ σ)).getD k false =
          (List.ofFn z).getD (PEqualNP.Outside.L_meta_3010.remap σ k) false := by
        intro k
        by_cases hk : k < 14
        · have hrm : PEqualNP.Outside.L_meta_3010.remap σ k = (σ ⟨k, hk⟩).val := by
            unfold PEqualNP.Outside.L_meta_3010.remap; rw [dite_eq_left hk]
          rw [hrm, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_ofFn, List.getElem?_ofFn]
          simp [hk]
        · have hrm : PEqualNP.Outside.L_meta_3010.remap σ k = k := by
            unfold PEqualNP.Outside.L_meta_3010.remap; rw [dite_eq_right hk]
          rw [hrm, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
              List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
      have hmain := PEqualNP.Outside.L_meta_3010.foldl_wires_remap σ x2.gates
        (List.ofFn (z ∘ σ)) (List.ofFn z) (by simp) (by simp) hbase x2.output
      rw [← hmain]
      change x2.eval (List.ofFn (z ∘ σ)) = x1 z
      rw [heval (z ∘ σ), hσ_sym z]
