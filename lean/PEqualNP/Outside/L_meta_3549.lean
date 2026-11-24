import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3549

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge

/-! The cone computation as a plain fold of the gate list. -/

lemma getD_append_left_gen {α : Type} (l l' : List α) (d : α) (j : ℕ) (hj : j < l.length) :
    (l ++ l').getD j d = l.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

lemma getD_append_right_gen {α : Type} (l l' : List α) (d : α) (j : ℕ) (hj : l.length ≤ j) :
    (l ++ l').getD j d = l'.getD (j - l.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hj, List.getD_eq_getElem?_getD]

/-- The cone that one `coneStep` appends for the gate `g`. -/
def coneNew (n : ℕ) (cs : List (List ℕ)) (g : Gate) : List ℕ :=
  (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
    (fun w => (w - n) :: cs.getD (w - n) [])

lemma coneStep_eq (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    coneStep n cs g = cs ++ [coneNew n cs g] := rfl

/-- `cones` of a bare gate list, starting from the empty accumulator. -/
def conesOf (n : ℕ) (gs : List Gate) : List (List ℕ) := gs.foldl (coneStep n) []

lemma cones_eq_conesOf (n : ℕ) (C : Circuit) : cones n C = conesOf n C.gates := rfl

lemma conesOf_append (n : ℕ) (gs : List Gate) (g : Gate) :
    conesOf n (gs ++ [g]) = conesOf n gs ++ [coneNew n (conesOf n gs) g] := by
  change conesOf n (gs ++ [g]) = coneStep n (conesOf n gs) g
  simp [conesOf, List.foldl_append]

/-- One `coneStep` appends exactly one cone. -/
lemma conesOf_length (n : ℕ) (gs : List Gate) : (conesOf n gs).length = gs.length := by
  refine List.reverseRecOn gs (motive := fun l => (conesOf n l).length = l.length) ?_ ?_
  · rfl
  · intro as a ih
    rw [conesOf_append]
    simp [ih]

lemma conesOf_take_length (n : ℕ) (gs : List Gate) (j : ℕ) (hj : j ≤ gs.length) :
    (conesOf n (gs.take j)).length = j := by
  rw [conesOf_length, List.length_take, Nat.min_eq_left hj]

lemma getD_coneStep_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (j : ℕ)
    (hj : j < cs.length) : (cs ++ [coneNew n cs g]).getD j [] = cs.getD j [] :=
  getD_append_left_gen cs _ ([] : List ℕ) j hj

/-- Membership in the cone appended by one `coneStep`. -/
lemma mem_coneNew (n : ℕ) (cs : List (List ℕ)) (g : Gate) (i : ℕ) :
    i ∈ coneNew n cs g ↔
      ∃ w, w ∈ g.inputs ∧ n ≤ w ∧ w < n + cs.length ∧
        (i = w - n ∨ i ∈ cs.getD (w - n) []) := by
  unfold coneNew
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨w, hw, hi⟩
    rw [List.mem_filter] at hw
    obtain ⟨hw1, hw2⟩ := hw
    obtain ⟨h2, h3⟩ := of_decide_eq_true hw2
    exact ⟨w, hw1, h2, h3, List.mem_cons.1 hi⟩
  · rintro ⟨w, hw1, h2, h3, hi⟩
    exact ⟨w, by rw [List.mem_filter]; exact ⟨hw1, by simp [h2, h3]⟩, List.mem_cons.2 hi⟩

lemma getD_append_self_new (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (cs ++ [coneNew n cs g]).getD cs.length [] = coneNew n cs g := by
  rw [getD_append_right_gen cs _ ([] : List ℕ) cs.length (Nat.le_refl _), Nat.sub_self]
  rfl

lemma getD_append_self_of_le (n : ℕ) (cs : List (List ℕ)) (g : Gate) (j : ℕ)
    (hj : cs.length ≤ j) (hjl : j < cs.length + 1) :
    (cs ++ [coneNew n cs g]).getD j [] = coneNew n cs g := by
  have h : j = cs.length := by omega
  subst h
  exact getD_append_self_new n cs g

/-- Every gate in the cone of gate `j` has a smaller index. -/
lemma conesOf_bound (n : ℕ) (gs : List Gate) (j i : ℕ)
    (hj : j < (conesOf n gs).length) (hi : i ∈ (conesOf n gs).getD j []) : i < j := by
  revert j i
  refine List.reverseRecOn gs (motive := fun l => ∀ j i : ℕ,
    j < (conesOf n l).length → i ∈ (conesOf n l).getD j [] → i < j) ?_ ?_
  · intro j i hj
    simp [conesOf] at hj
  · intro as a ih j i hj hi
    rw [conesOf_append] at hj hi
    have hlen : (conesOf n as ++ [coneNew n (conesOf n as) a]).length
        = (conesOf n as).length + 1 := by simp
    rw [hlen] at hj
    by_cases hjc : j < (conesOf n as).length
    · rw [getD_append_left_gen _ _ ([] : List ℕ) j hjc] at hi
      exact ih j i hjc hi
    · have hje : j = (conesOf n as).length := by omega
      subst hje
      rw [getD_append_self_new, mem_coneNew] at hi
      obtain ⟨w, _, _, hw, h | h⟩ := hi
      · omega
      · have := ih (w - n) i (by omega) h
        omega

/-- The cone relation is transitive inside the prefix. -/
lemma conesOf_trans (n : ℕ) (gs : List Gate) (j i i' : ℕ)
    (hi : i ∈ (conesOf n gs).getD j []) (hi' : i' ∈ (conesOf n gs).getD i []) :
    i' ∈ (conesOf n gs).getD j [] := by
  revert j i i'
  refine List.reverseRecOn gs (motive := fun l => ∀ j i i' : ℕ,
    i ∈ (conesOf n l).getD j [] → i' ∈ (conesOf n l).getD i [] →
    i' ∈ (conesOf n l).getD j []) ?_ ?_
  · intro j i i' hi
    simp [conesOf] at hi
  · intro as a ih j i i' hi hi'
    rw [conesOf_append] at hi hi' ⊢
    by_cases hjc : j < (conesOf n as).length
    · rw [getD_append_left_gen _ _ ([] : List ℕ) j hjc] at hi ⊢
      have hib : i < (conesOf n as).length := by
        have := conesOf_bound n as j i hjc hi
        omega
      rw [getD_append_left_gen _ _ ([] : List ℕ) i hib] at hi'
      exact ih j i i' hi hi'
    · by_cases hje : j = (conesOf n as).length
      · subst hje
        rw [getD_append_self_new, mem_coneNew] at hi
        rw [getD_append_self_new]
        obtain ⟨w, hw, hn, hwlt, h | h⟩ := hi
        · have hib : i < (conesOf n as).length := by omega
          rw [getD_append_left_gen _ _ ([] : List ℕ) i hib] at hi'
          rw [mem_coneNew]
          exact ⟨w, hw, hn, hwlt, Or.inr (h ▸ hi')⟩
        · have hib : i < (conesOf n as).length := by
            have := conesOf_bound n as (w - n) i (by omega) h
            omega
          rw [getD_append_left_gen _ _ ([] : List ℕ) i hib] at hi'
          rw [mem_coneNew]
          exact ⟨w, hw, hn, hwlt, Or.inr (ih (w - n) i i' h hi')⟩
      · have hge : (conesOf n as ++ [coneNew n (conesOf n as) a]).length ≤ j := by
          simp only [List.length_append, List.length_singleton]
          omega
        rw [List.getD_eq_default _ _ hge] at hi
        exact absurd hi (by simp)

lemma conesOf_sublist (n : ℕ) (l l' : List Gate) :
    ∃ t, conesOf n (l ++ l') = conesOf n l ++ t := by
  refine List.reverseRecOn l' (motive := fun l' => ∃ t, conesOf n (l ++ l') = conesOf n l ++ t) ?_ ?_
  · exact ⟨[], by simp⟩
  · intro as a ih
    obtain ⟨t, ht⟩ := ih
    refine ⟨t ++ [coneNew n (conesOf n (l ++ as)) a], ?_⟩
    rw [← List.append_assoc, conesOf_append, ht, List.append_assoc]

lemma conesOf_getD_prefix (n : ℕ) (l l' : List Gate) (j : ℕ)
    (hj : j < (conesOf n l).length) :
    (conesOf n (l ++ l')).getD j [] = (conesOf n l).getD j [] := by
  obtain ⟨t, ht⟩ := conesOf_sublist n l l'
  rw [ht, getD_append_left_gen _ _ ([] : List ℕ) j hj]

/-- The cone of gate `j` is exactly the cone computed by one `coneStep` at the gate `j`. -/
lemma conesOf_getD_take (n : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    (conesOf n gs).getD j [] =
      coneNew n (conesOf n (gs.take j)) (gs.getD j ⟨GateOp.or, []⟩) := by
  have hsplit : gs = gs.take j ++ [gs.getD j ⟨GateOp.or, []⟩] ++ gs.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j gs]
    have hd : gs.drop j = gs.getD j ⟨GateOp.or, []⟩ :: gs.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons hj, List.getD_eq_getElem]
    rw [hd]
    simp
  conv_lhs => rw [hsplit]
  rw [conesOf_getD_prefix n (gs.take j ++ [gs.getD j ⟨GateOp.or, []⟩]) (gs.drop (j + 1)) j
    (by rw [conesOf_length, List.length_append, List.length_singleton, List.length_take,
          Nat.min_eq_left (by omega)]; omega)]
  rw [conesOf_append]
  exact getD_append_self_of_le n (conesOf n (gs.take j)) (gs.getD j ⟨GateOp.or, []⟩) j
    (by rw [conesOf_take_length n gs j (by omega)])
    (by rw [conesOf_take_length n gs j (by omega)]; omega)

/-- A gate reading the wire `n + i` of an earlier gate `i` has `i` in its strict cone. -/
lemma InCone_reads {n : ℕ} {C : Circuit} {i j : ℕ}
    (hj : j < C.gates.length) (hi : i < j) (hread : n + i ∈ (gateAt C j).inputs) :
    InCone n C i j := by
  have hgate : gateAt C j = C.gates.getD j ⟨GateOp.or, []⟩ := rfl
  rw [hgate] at hread
  rw [InCone, cones_eq_conesOf, conesOf_getD_take n C.gates j hj, mem_coneNew]
  refine ⟨n + i, hread, by omega, ?_, Or.inl (by omega)⟩
  rw [conesOf_take_length n C.gates j (by omega)]
  omega

/-- The strict cone is transitive. -/
lemma InCone_trans {n : ℕ} {C : Circuit} {i j k : ℕ}
    (h1 : InCone n C i j) (h2 : InCone n C j k) : InCone n C i k := by
  unfold InCone at *
  rw [cones_eq_conesOf] at *
  exact conesOf_trans n C.gates k j i h2 h1

/-- Reading a gate of `C.gates.mapIdx f` at index `j` gives `f j` of the gate of `C`. -/
lemma mapIdx_getD_lt (f : ℕ → Gate → Gate) (gs : List Gate) (j : ℕ) (d : Gate)
    (hj : j < gs.length) : (gs.mapIdx f).getD j d = f j (gs.getD j d) := by
  revert j d
  refine List.reverseRecOn gs (motive := fun l => ∀ (j : ℕ) (d : Gate), j < l.length →
    (l.mapIdx f).getD j d = f j (l.getD j d)) ?_ ?_
  · intro j d hj
    simp at hj
  · intro as a ih j d hj
    rw [List.mapIdx_append_one]
    by_cases hjc : j < as.length
    · rw [getD_append_left_gen _ _ d j (by simpa using hjc)]
      rw [getD_append_left_gen as [a] d j hjc]
      exact ih j d hjc
    · have hje : j = as.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst hje
      rw [getD_append_right_gen (as.mapIdx f) [f as.length a] d as.length (by simp)]
      rw [getD_append_right_gen as [a] d as.length (Nat.le_refl _), Nat.sub_self]
      simp

/-- The read relation of the narrowing move. -/
def GRel (n m : ℕ) (C : Circuit) (u : ℕ → ℕ) (NR : ℕ → ℕ → Prop)
    (G0 : List Gate) (rho : ℕ → ℕ → ℕ) (a b : ℕ) : Prop :=
  a < b ∧ b < C.gates.length ∧
    ((n + a ∈ (gateAt C b).inputs ∧ ¬ ∃ k, k < m ∧ a = u k ∧ NR k b) ∨
     ∃ k, k < m ∧ NR k b ∧ rho b (n + u k) = n + G0.length + a)

end PEqualNP.Outside.L_meta_3549

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge PEqualNP.Outside.L_meta_3549

theorem PEqualNP.Outside.L_meta_3549 :
  ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (qH : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (m : ℕ) (u T W z : ℕ → ℕ) (NR : ℕ → ℕ → Prop) (P : ℕ → (Fin n → Bool) → Bool) (G0 : List PEqualNP.CircuitLowerBounds.Gate) (rho : ℕ → ℕ → ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit), (∀ y0 : Fin n → Bool, qH y0 = true ↔ ∃ a0 b0 : Fin n, H.Adj a0 b0 ∧ y0 a0 = true ∧ y0 b0 = true) → PEqualNP.TopForm.IsAO2 n C → (∀ y1 : Fin n → Bool, C.eval (List.ofFn y1) = qH y1) → (∀ k0 r0 : ℕ, NR k0 r0 ↔ r0 < C.gates.length ∧ n + u k0 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).inputs ∧ (r0 = T k0 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k0) r0 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).op = PEqualNP.CircuitLowerBounds.GateOp.or))) → (∀ (k1 : ℕ) (y2 : Fin n → Bool), P k1 y2 = decide (∃ w1 : Fin n, y2 w1 = true ∧ PEqualNP.CleanedNonEdge.wireVal n C (n + u k1) (fun j1 : Fin n => decide (j1 = w1 ∨ (j1 : ℕ) = z k1)) = true)) → (∀ k2 < m, u k2 < C.gates.length ∧ T k2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ z k2 < n ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [W k2, z k2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [z k2, W k2]) ∧ (∀ y3 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + T k2) y3 = true → qH y3 = true) ∧ ∀ g2 < C.gates.length, PEqualNP.EdgeOwnership.InCone n C (T k2) g2 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ k3 < m, ∀ g3 < C.gates.length, PEqualNP.CleanedNonEdge.OrReaches n C (W k3) g3 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g3).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.EdgeOwnership.InCone n C (u k3) g3 → C.output ≠ n + g3 ∧ ∀ r3 < C.gates.length, n + g3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).inputs → r3 = T k3 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k3) r3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∀ k4 < m, ∀ k5 < m, ∀ r4 : ℕ, NR k5 r4 → r4 ≠ u k4 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r4 (u k4)) → (∀ i6 < G0.length, ∀ w6 ∈ (G0.getD i6 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, w6 < n + i6) → D = ⟨G0 ++ C.gates.mapIdx (fun r7 g7 => ({ op := g7.op, inputs := g7.inputs.map (fun i7 => rho r7 i7) } : PEqualNP.CircuitLowerBounds.Gate)), if C.output < n then C.output else C.output + G0.length⟩ → (∀ r8 < C.gates.length, ∀ i8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r8).inputs, (∀ k8 < m, ¬ (NR k8 r8 ∧ i8 = n + u k8)) → rho r8 i8 = if i8 < n then i8 else i8 + G0.length) → (∀ r9 : ℕ, ∀ k9 < m, NR k9 r9 → (rho r9 (n + u k9) < n + G0.length ∧ ∀ y9 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n (⟨G0, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) (rho r9 (n + u k9)) y9 = P k9 y9) ∨ (∃ g9 < r9, rho r9 (n + u k9) = n + G0.length + g9 ∧ (∀ y10 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + g9) y10 = P k9 y10) ∧ ∀ k10 < m, ∀ r10 : ℕ, NR k10 r10 → r10 ≠ g9 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r10 g9) ∨ ((∀ y11 : Fin n → Bool, P k9 y11 = false) ∧ n + G0.length + r9 ≤ rho r9 (n + u k9))) → ∀ g15 o15 : ℕ, C.output = n + o15 → g15 < C.gates.length → Relation.ReflTransGen (fun a13 b13 : ℕ => a13 < b13 ∧ b13 < C.gates.length ∧ ((n + a13 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C b13).inputs ∧ ¬ ∃ k13 < m, a13 = u k13 ∧ NR k13 b13) ∨ ∃ k14 < m, NR k14 b13 ∧ rho b13 (n + u k14) = n + G0.length + a13)) g15 o15 → G0.length + g15 ∈ PEqualNP.FactorSubst.liveGates n D
  := by
  intro n H qH C m u T W z NR P G0 rho D hqH hAO2 hCfun hNRiff hP hm hnonarrow hcong hleft hD
    hrho hinj g15 o15 hout hg15 hpath
  let f : ℕ → Gate → Gate :=
    fun r7 g7 => ({ op := g7.op, inputs := g7.inputs.map (fun i7 => rho r7 i7) } : Gate)
  have hD' : D = ⟨G0 ++ C.gates.mapIdx f,
      if C.output < n then C.output else C.output + G0.length⟩ := hD
  have hDout : D.output = if C.output < n then C.output else C.output + G0.length := by
    rw [hD']
  have hClen : D.gates.length = G0.length + C.gates.length := by
    rw [hD']
    simp
  have hout' : D.output = n + (o15 + G0.length) := by
    rw [hDout, if_neg (by omega)]
    omega
  have hinputs : ∀ b, b < C.gates.length →
      (gateAt D (G0.length + b)).inputs = (gateAt C b).inputs.map (rho b) := by
    intro b hb
    unfold gateAt
    rw [hD',
      List.getD_append_right G0 (C.gates.mapIdx f) (⟨GateOp.or, []⟩ : Gate) (G0.length + b)
        (by omega),
      Nat.add_sub_cancel_left,
      mapIdx_getD_lt f C.gates b (⟨GateOp.or, []⟩ : Gate) hb]
  have hstep : ∀ a b, GRel n m C u NR G0 rho a b →
      InCone n D (G0.length + a) (G0.length + b) := by
    rintro a b ⟨hab, hb, hcase | hcase⟩
    · obtain ⟨hread, hnn⟩ := hcase
      have hnn' : ∀ k, k < m → ¬ (NR k b ∧ n + a = n + u k) := by
        rintro k hk ⟨hNR, heq⟩
        exact hnn ⟨k, hk, by omega, hNR⟩
      have hrhoa : rho b (n + a) = n + a + G0.length := by
        rw [hrho b hb (n + a) hread hnn', if_neg (by omega)]
      refine InCone_reads (C := D) ?_ ?_ ?_
      · rw [hClen]; omega
      · omega
      · rw [hinputs b hb]
        have h2 : rho b (n + a) ∈ (gateAt C b).inputs.map (rho b) :=
          List.mem_map_of_mem (f := rho b) hread
        rw [hrhoa] at h2
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h2
    · obtain ⟨k, hk, hNR, hrhoeq⟩ := hcase
      have hread : n + u k ∈ (gateAt C b).inputs := ((hNRiff k b).1 hNR).2.1
      refine InCone_reads (C := D) ?_ ?_ ?_
      · rw [hClen]; omega
      · omega
      · rw [hinputs b hb]
        have h2 : rho b (n + u k) ∈ (gateAt C b).inputs.map (rho b) :=
          List.mem_map_of_mem (f := rho b) hread
        rw [hrhoeq] at h2
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h2
  have key : ∀ a b, Relation.ReflTransGen (GRel n m C u NR G0 rho) a b →
      a = b ∨ InCone n D (G0.length + a) (G0.length + b) := by
    intro a b hab
    induction hab with
    | refl => exact Or.inl rfl
    | tail hab hbc ih =>
      rcases ih with heq | hic
      · subst heq
        exact Or.inr (hstep _ _ hbc)
      · exact Or.inr (InCone_trans hic (hstep _ _ hbc))
  rw [show PEqualNP.FactorSubst.liveGates n D
      = (Finset.range D.gates.length).filter (fun j =>
          n ≤ D.output ∧ (j = D.output - n ∨ InCone n D j (D.output - n))) from rfl]
  simp only [Finset.mem_filter, Finset.mem_range]
  refine ⟨?_, ?_, ?_⟩
  · rw [hClen]; omega
  · rw [hout']; omega
  · rcases key g15 o15 hpath with heq | hic
    · exact Or.inl (by omega)
    · have hsub : D.output - n = G0.length + o15 := by
        rw [hout']
        omega
      exact Or.inr (by rwa [hsub])
