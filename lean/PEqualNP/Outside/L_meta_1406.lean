import Mathlib
import PEqualNP.Defs

namespace PEqualNP.MetaComplexity.L1406

open PEqualNP.CircuitLowerBounds

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

private theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

private theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

private theorem foldl_step_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl step w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton, foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_step_length, Nat.min_eq_left ht.le]

private theorem foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl step w).length) :
    (G.foldl step w).getD i false = ((G.take t).foldl step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact foldl_step_getD _ _ _ hi

private theorem gate_value (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i =>
        if i < w.length + t then (G.foldl step w).getD i false else false) := by
  rw [foldl_step_getD_gate G w t ht]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : ((G.take t).foldl step w).length = w.length + t := by
    rw [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]
  split_ifs with h
  · exact (foldl_take_getD G w t i (by rw [hlen]; exact h)).symm
  · exact getD_of_length_le _ _ (by rw [hlen]; omega)

private def val (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private theorem val_input (C : Circuit) (n : ℕ) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val C n x w = x ⟨w, hw⟩ := by
  unfold val
  rw [wires_eq, foldl_step_getD _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

private theorem val_none (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ)
    (hg : C.gates[j]? = none) : val C n x (n + j) = false := by
  unfold val
  apply getD_of_length_le
  rw [wires_eq, foldl_step_length]
  have hlen := List.getElem?_eq_none_iff.mp hg
  simp only [List.length_ofFn]
  omega

private theorem val_gate (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) :
    val C n x (n + j) =
      h.op.eval (h.inputs.map fun i => if i < n + j then val C n x i else false) := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hg
  have := gate_value C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at this
  exact this

private theorem val_or (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) (hop : h.op = GateOp.or) :
    val C n x (n + j) = true ↔ ∃ w ∈ h.inputs, w < n + j ∧ val C n x w = true := by
  rw [val_gate C n x j h hg, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  constructor
  · rintro ⟨w, hw, hv⟩
    by_cases hlt : w < n + j
    · exact ⟨w, hw, hlt, by simpa [hlt] using hv⟩
    · simp [hlt] at hv
  · rintro ⟨w, hw, hlt, hv⟩
    exact ⟨w, hw, by simpa [hlt] using hv⟩

private theorem val_and (C : Circuit) (n : ℕ) (x : Fin n → Bool) (j : ℕ) (h : Gate)
    (hg : C.gates[j]? = some h) (hop : h.op = GateOp.and) :
    val C n x (n + j) = true ↔ ∀ w ∈ h.inputs, w < n + j ∧ val C n x w = true := by
  rw [val_gate C n x j h hg, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
  constructor
  · intro hall w hw
    have hv := hall w hw
    by_cases hlt : w < n + j
    · exact ⟨hlt, by simpa [hlt] using hv⟩
    · simp [hlt] at hv
  · intro hall w hw
    obtain ⟨hlt, hv⟩ := hall w hw
    simpa [hlt] using hv

private def e1 {n : ℕ} (t : Fin n) : Fin n → Bool := fun i => decide (i = t)

private def e2 {n : ℕ} (c t : Fin n) : Fin n → Bool := fun i => decide (i = c ∨ i = t)

private theorem no_edge_e1 {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n) :
    ¬ ∃ u v : Fin n, G.Adj u v ∧ e1 c u = true ∧ e1 c v = true := by
  rintro ⟨u, v, hadj, hu, hv⟩
  have hu' : u = c := by simpa [e1] using hu
  have hv' : v = c := by simpa [e1] using hv
  exact hadj.ne (hu'.trans hv'.symm)

private theorem edge_e2 {n : ℕ} (G : SimpleGraph (Fin n)) (c t : Fin n)
    (h : ∃ u v : Fin n, G.Adj u v ∧ e2 c t u = true ∧ e2 c t v = true) : G.Adj c t := by
  obtain ⟨u, v, hadj, hu, hv⟩ := h
  have hu' : u = c ∨ u = t := by simpa [e2] using hu
  have hv' : v = c ∨ v = t := by simpa [e2] using hv
  rcases hu' with hu' | hu' <;> rcases hv' with hv' | hv'
  · exact absurd (hu'.trans hv'.symm) hadj.ne
  · rw [hu', hv'] at hadj; exact hadj
  · rw [hu', hv'] at hadj; exact hadj.symm
  · exact absurd (hu'.trans hv'.symm) hadj.ne

private theorem val_mono (C : Circuit) (n : ℕ)
    (hfan : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ w : ℕ, ∀ x y : Fin n → Bool, (∀ i : Fin n, x i = true → y i = true) →
      val C n x w = true → val C n y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro x y hxy hwv
    by_cases hwn : w < n
    · have hx : x ⟨w, hwn⟩ = true := by
        simpa [val_input C n x w hwn] using hwv
      rw [val_input C n y w hwn]
      exact hxy ⟨w, hwn⟩ hx
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      cases hg : C.gates[j]? with
      | none =>
        rw [val_none C n x j hg] at hwv
        cases hwv
      | some g =>
        have hop := (hfan g (List.mem_of_getElem? hg)).1
        rcases hop with hop | hop
        · have hall := (val_and C n x j g hg hop).mp hwv
          refine (val_and C n y j g hg hop).mpr ?_
          intro w' hw'
          obtain ⟨hlt, hv⟩ := hall w' hw'
          exact ⟨hlt, ih w' (by omega) x y hxy hv⟩
        · obtain ⟨w', hw', hlt, hv⟩ := (val_or C n x j g hg hop).mp hwv
          refine (val_or C n y j g hg hop).mpr ⟨w', hw', hlt, ?_⟩
          exact ih w' (by omega) x y hxy hv

private theorem mono_e1_e2 {n : ℕ} (t s : Fin n) :
    ∀ i : Fin n, e1 t i = true → e2 t s i = true := by
  intro i hi
  have hit : i = t := by simpa [e1] using hi
  simp [e2, hit]

private theorem gate_get_eq {C : Circuit} {j : Fin C.gates.length} {g : Gate}
    (hg : C.gates[(j : ℕ)]? = some g) : C.gates.get j = g := by
  have hsome : C.gates[(j : ℕ)]? = some (C.gates.get j) := by
    simpa using List.getElem?_eq_getElem j.isLt
  rw [hsome] at hg
  exact Option.some.inj hg

private theorem no_single_and (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n))
    (hclean : ∀ (i : Fin C.gates.length) (x : Fin n → Bool),
      (C.gates.get i).op = GateOp.and → val C n x (n + (i : ℕ)) = true →
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)
    (j : Fin C.gates.length) (hopj : (C.gates.get j).op = GateOp.and) (t : Fin n) :
    val C n (e1 t) (n + (j : ℕ)) ≠ true := by
  intro hv
  obtain ⟨u, v, hadj, hu, hv'⟩ := hclean j (e1 t) hopj hv
  exact no_edge_e1 G t ⟨u, v, hadj, hu, hv'⟩

private theorem fire_wire_single (C : Circuit) (n : ℕ)
    (hfan : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ j : ℕ, j < C.gates.length →
    ∀ (u v : Fin n)
      (hmin : ∀ k : ℕ, k < j → ∀ g : Gate, C.gates[k]? = some g →
        g.op = GateOp.and → val C n (e2 u v) (n + k) ≠ true)
      (w : ℕ) (hwlt : w < n + j) (hfw : val C n (e2 u v) w = true),
      ∃ t : Fin n, (t = u ∨ t = v) ∧ val C n (e1 t) w = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjlen u v hmin w hwlt hfw
    by_cases hwn : w < n
    · let t : Fin n := ⟨w, hwn⟩
      have ht : (e2 u v) t = true := by
        rw [← val_input C n (e2 u v) w hwn]
        exact hfw
      refine ⟨t, ?_, ?_⟩
      · simpa [e2] using ht
      · rw [val_input C n (e1 t) w hwn]
        simp [e1, t]
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hkj : k < j := by omega
      have hklen : k < C.gates.length := by omega
      cases hg : C.gates[k]? with
      | none =>
        rw [val_none C n (e2 u v) k hg] at hfw
        cases hfw
      | some g =>
        have hop := (hfan g (List.mem_of_getElem? hg)).1
        rcases hop with hop | hop
        · exact False.elim ((hmin k hkj g hg hop) hfw)
        · obtain ⟨w', hw', hlt, hv⟩ := (val_or C n (e2 u v) k g hg hop).mp hfw
          obtain ⟨t, htuv, hvt⟩ := ih k hkj hklen u v
            (fun k' hk' g' hg' hop' => hmin k' (by omega) g' hg' hop') w' (by omega) hv
          exact ⟨t, htuv, (val_or C n (e1 t) k g hg hop).mpr ⟨w', hw', hlt, hvt⟩⟩

private theorem exists_and_nosing (C : Circuit) (n : ℕ)
    (hfan : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ w : ℕ, (∀ t : Fin n, val C n (e1 t) w ≠ true) →
      ∀ x : Fin n → Bool, val C n x w = true →
        ∃ j : ℕ, (∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.and) ∧
          val C n x (n + j) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hnos x hxw
    by_cases hwn : w < n
    · let t : Fin n := ⟨w, hwn⟩
      have ht : val C n (e1 t) w = true := by
        rw [val_input C n (e1 t) w hwn]
        simp [e1, t]
      exact False.elim (hnos t ht)
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      cases hg : C.gates[j]? with
      | none =>
        rw [val_none C n x j hg] at hxw
        cases hxw
      | some g =>
        have hop := (hfan g (List.mem_of_getElem? hg)).1
        rcases hop with hop | hop
        · exact ⟨j, ⟨g, hg, hop⟩, hxw⟩
        · obtain ⟨w', hw', hlt, hv⟩ := (val_or C n x j g hg hop).mp hxw
          have hnos' : ∀ t : Fin n, val C n (e1 t) w' ≠ true := by
            intro t ht
            apply hnos t
            exact (val_or C n (e1 t) j g hg hop).mpr ⟨w', hw', hlt, ht⟩
          exact ih w' (by omega) hnos' x hv

private theorem center_exists (C : Circuit) (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfan : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hclean : ∀ (i : Fin C.gates.length) (x : Fin n → Bool),
      (C.gates.get i).op = GateOp.and → val C n x (n + (i : ℕ)) = true →
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)
    (j : Fin C.gates.length) (g : Gate) (hg : C.gates[(j : ℕ)]? = some g)
    (hop : g.op = GateOp.and)
    (u v : Fin n) (hadj : G.Adj u v) (hfire : val C n (e2 u v) (n + (j : ℕ)) = true)
    (hmin : ∀ k : ℕ, k < (j : ℕ) → ∀ g' : Gate, C.gates[k]? = some g' →
      g'.op = GateOp.and → val C n (e2 u v) (n + k) ≠ true) :
    ∃ c : Fin n, ∀ u' v' : Fin n, G.Adj u' v' →
      val C n (e2 u' v') (n + (j : ℕ)) = true →
      (∀ k : ℕ, k < (j : ℕ) → ∀ g' : Gate, C.gates[k]? = some g' →
        g'.op = GateOp.and → val C n (e2 u' v') (n + k) ≠ true) →
      c = u' ∨ c = v' := by
  have hall := (val_and C n (e2 u v) (j : ℕ) g hg hop).mp hfire
  have hlen : g.inputs.length ≤ 2 := (hfan g (List.mem_of_getElem? hg)).2
  have hjl : (j : ℕ) < C.gates.length := j.isLt
  have hopj : (C.gates.get j).op = GateOp.and := by
    rw [gate_get_eq hg]
    exact hop
  cases hins : g.inputs with
  | nil =>
    exfalso
    have hxall : val C n (fun _ : Fin n => false) (n + (j : ℕ)) = true := by
      rw [val_gate C n (fun _ : Fin n => false) (j : ℕ) g hg, hop]
      simp [GateOp.eval, hins]
    obtain ⟨a, b, hab, ha, hb⟩ := hclean j (fun _ : Fin n => false) hopj hxall
    simp at ha
  | cons w1 l =>
    cases hins2 : l with
    | nil =>
      have hw1mem : w1 ∈ g.inputs := by simp [hins]
      have hw1lt : w1 < n + (j : ℕ) := (hall w1 hw1mem).1
      have hw1fv : val C n (e2 u v) w1 = true := (hall w1 hw1mem).2
      obtain ⟨t, _, hvt⟩ := fire_wire_single C n hfan (j : ℕ) hjl u v hmin w1 hw1lt hw1fv
      have hsingle : val C n (e1 t) (n + (j : ℕ)) = true := by
        refine (val_and C n (e1 t) (j : ℕ) g hg hop).mpr ?_
        intro w hw
        rw [hins, hins2] at hw
        simp at hw
        subst w
        exact ⟨hw1lt, hvt⟩
      exact False.elim (no_single_and C n G hclean j hopj t hsingle)
    | cons w2 l2 =>
      have hnil : l2 = [] := by
        have hlen' : (w1 :: w2 :: l2).length ≤ 2 := by simpa [hins, hins2] using hlen
        simp at hlen'
        omega
      have hw1mem : w1 ∈ g.inputs := by simp [hins]
      have hw2mem : w2 ∈ g.inputs := by simp [hins, hins2]
      have hw1lt : w1 < n + (j : ℕ) := (hall w1 hw1mem).1
      have hw2lt : w2 < n + (j : ℕ) := (hall w2 hw2mem).1
      have hw1fv : val C n (e2 u v) w1 = true := (hall w1 hw1mem).2
      have hw2fv : val C n (e2 u v) w2 = true := (hall w2 hw2mem).2
      let V1 : Finset (Fin n) := Finset.univ.filter (fun t => val C n (e1 t) w1 = true)
      let V2 : Finset (Fin n) := Finset.univ.filter (fun t => val C n (e1 t) w2 = true)
      have hV1ne : V1.Nonempty := by
        obtain ⟨t, _, ht⟩ := fire_wire_single C n hfan (j : ℕ) hjl u v hmin w1 hw1lt hw1fv
        exact ⟨t, by simp [V1, ht]⟩
      have hV2ne : V2.Nonempty := by
        obtain ⟨t, _, ht⟩ := fire_wire_single C n hfan (j : ℕ) hjl u v hmin w2 hw2lt hw2fv
        exact ⟨t, by simp [V2, ht]⟩
      have hdisj : Disjoint V1 V2 := by
        rw [Finset.disjoint_left]
        intro t ht1 ht2
        have hv1 : val C n (e1 t) w1 = true := (Finset.mem_filter.mp ht1).2
        have hv2 : val C n (e1 t) w2 = true := (Finset.mem_filter.mp ht2).2
        have hs : val C n (e1 t) (n + (j : ℕ)) = true := by
          refine (val_and C n (e1 t) (j : ℕ) g hg hop).mpr ?_
          intro w hw
          have hw' : w = w1 ∨ w = w2 := by simpa [hins, hins2, hnil] using hw
          rcases hw' with rfl | rfl
          · exact ⟨hw1lt, hv1⟩
          · exact ⟨hw2lt, hv2⟩
        exact no_single_and C n G hclean j hopj t hs
      have hcross : ∀ t1 ∈ V1, ∀ t2 ∈ V2, G.Adj t1 t2 := by
        intro t1 ht1 t2 ht2
        have hv1 : val C n (e1 t1) w1 = true := (Finset.mem_filter.mp ht1).2
        have hv2 : val C n (e1 t2) w2 = true := (Finset.mem_filter.mp ht2).2
        have hgt : val C n (e2 t1 t2) (n + (j : ℕ)) = true := by
          refine (val_and C n (e2 t1 t2) (j : ℕ) g hg hop).mpr ?_
          intro w hw
          have hw' : w = w1 ∨ w = w2 := by simpa [hins, hins2, hnil] using hw
          rcases hw' with hw | hw
          · subst w
            exact ⟨hw1lt, val_mono C n hfan w1 (e1 t1) (e2 t1 t2) (mono_e1_e2 t1 t2) hv1⟩
          · subst w
            have hmono2 : ∀ i : Fin n, e1 t2 i = true → e2 t1 t2 i = true := by
              intro i hi
              have hit : i = t2 := by simpa [e1] using hi
              simp [e2, hit]
            exact ⟨hw2lt, val_mono C n hfan w2 (e1 t2) (e2 t1 t2) hmono2 hv2⟩
        obtain ⟨a, b, hab, ha, hb⟩ := hclean j (e2 t1 t2) hopj hgt
        exact edge_e2 G t1 t2 ⟨a, b, hab, ha, hb⟩
      have hsmall : V1.card ≤ 1 ∨ V2.card ≤ 1 := by
        by_contra h
        have hc1 : ¬ V1.card ≤ 1 := by omega
        have hc2 : ¬ V2.card ≤ 1 := by omega
        have hpair1 : ∃ a ∈ V1, ∃ b ∈ V1, a ≠ b := by
          by_contra hnone
          apply hc1
          exact Finset.card_le_one.mpr (by
            intro a ha b hb
            by_contra hab
            exact hnone ⟨a, ha, b, hb, hab⟩)
        have hpair2 : ∃ a ∈ V2, ∃ b ∈ V2, a ≠ b := by
          by_contra hnone
          apply hc2
          exact Finset.card_le_one.mpr (by
            intro a ha b hb
            by_contra hab
            exact hnone ⟨a, ha, b, hb, hab⟩)
        obtain ⟨a1, ha1, a2, ha2, hane⟩ := hpair1
        obtain ⟨b1, hb1, b2, hb2, hbne⟩ := hpair2
        have hab1 : G.Adj a1 b1 := hcross a1 ha1 b1 hb1
        have hab2 : G.Adj b1 a2 := (hcross a2 ha2 b1 hb1).symm
        have hab3 : G.Adj a2 b2 := hcross a2 ha2 b2 hb2
        have hab4 : G.Adj b2 a1 := (hcross a1 ha1 b2 hb2).symm
        exact h4 a1 b1 a2 b2 hane hbne ⟨hab1, hab2, hab3, hab4⟩
      rcases hsmall with hc1 | hc2
      · obtain ⟨c, hcV⟩ := hV1ne
        refine ⟨c, ?_⟩
        intro u' v' hadj' hfire' hmin'
        have hall' := (val_and C n (e2 u' v') (j : ℕ) g hg hop).mp hfire'
        have hw1lt' : w1 < n + (j : ℕ) := (hall' w1 hw1mem).1
        have hw1fv' : val C n (e2 u' v') w1 = true := (hall' w1 hw1mem).2
        obtain ⟨t, htuv, hvt⟩ := fire_wire_single C n hfan (j : ℕ) hjl u' v' hmin' w1 hw1lt' hw1fv'
        have htV : t ∈ V1 := by simp [V1, hvt]
        have htc : t = c := (Finset.card_le_one.mp hc1) t htV c hcV
        simpa [htc] using htuv
      · obtain ⟨c, hcV⟩ := hV2ne
        refine ⟨c, ?_⟩
        intro u' v' hadj' hfire' hmin'
        have hall' := (val_and C n (e2 u' v') (j : ℕ) g hg hop).mp hfire'
        have hw2lt' : w2 < n + (j : ℕ) := (hall' w2 hw2mem).1
        have hw2fv' : val C n (e2 u' v') w2 = true := (hall' w2 hw2mem).2
        obtain ⟨t, htuv, hvt⟩ := fire_wire_single C n hfan (j : ℕ) hjl u' v' hmin' w2 hw2lt' hw2fv'
        have htV : t ∈ V2 := by simp [V2, hvt]
        have htc : t = c := (Finset.card_le_one.mp hc2) t htV c hcV
        simpa [htc] using htuv

end PEqualNP.MetaComplexity.L1406

theorem PEqualNP.Outside.L_meta_1406 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∀ I : Finset (Fin gates.length), (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → i ∈ I) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ T.card ≤ I.card := by
  classical
  intro n G inst h4no gates out hfan hf hclean I hI
  by_cases hn : n = 0
  · subst n
    refine ⟨∅, ?_, by simp⟩
    intro u
    exact Fin.elim0 u
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates, out⟩
    have hfanC : ∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
      simpa [C] using hfan
    have hcleanC : ∀ (i : Fin C.gates.length) (x : Fin n → Bool),
        (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          PEqualNP.MetaComplexity.L1406.val C n x (n + (i : ℕ)) = true →
            ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
      intro i x hi hv
      exact hclean i x (by simpa [C] using hi) (by
        simpa [C, PEqualNP.MetaComplexity.L1406.val, PEqualNP.CircuitLowerBounds.Circuit.wires] using hv)
    let dflt : Fin n := ⟨0, hnpos⟩
    let Good : Fin C.gates.length → Prop := fun j =>
      ∃ u v : Fin n, G.Adj u v ∧
        PEqualNP.MetaComplexity.L1406.val C n (PEqualNP.MetaComplexity.L1406.e2 u v) (n + (j : ℕ)) = true ∧
        (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ∀ k : ℕ, k < (j : ℕ) → ∀ g : PEqualNP.CircuitLowerBounds.Gate,
          C.gates[k]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
            PEqualNP.MetaComplexity.L1406.val C n (PEqualNP.MetaComplexity.L1406.e2 u v) (n + k) ≠ true
    have center_spec : ∀ j : Fin C.gates.length, Good j →
        ∃ c : Fin n, ∀ u' v' : Fin n, G.Adj u' v' →
          PEqualNP.MetaComplexity.L1406.val C n (PEqualNP.MetaComplexity.L1406.e2 u' v') (n + (j : ℕ)) = true →
          (∀ k : ℕ, k < (j : ℕ) → ∀ g : PEqualNP.CircuitLowerBounds.Gate,
            C.gates[k]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
              PEqualNP.MetaComplexity.L1406.val C n (PEqualNP.MetaComplexity.L1406.e2 u' v') (n + k) ≠ true) →
          c = u' ∨ c = v' := by
      intro j hj
      rcases hj with ⟨u, v, hu, hfv, hopj, hmin⟩
      have hgj : C.gates[(j : ℕ)]? = some (C.gates.get j) := by
        simpa using List.getElem?_eq_getElem j.isLt
      exact PEqualNP.MetaComplexity.L1406.center_exists C n G hfanC h4no hcleanC j
        (C.gates.get j) hgj hopj u v hu hfv hmin
    let cen : Fin C.gates.length → Fin n := fun j =>
      if h : Good j then Classical.choose (center_spec j h) else dflt
    let T : Finset (Fin n) := I.image cen
    refine ⟨T, ?_, ?_⟩
    · intro u v hadj
      have hxe : PEqualNP.MetaComplexity.L1406.val C n (PEqualNP.MetaComplexity.L1406.e2 u v) C.output = true := by
        have heval : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (PEqualNP.MetaComplexity.L1406.e2 u v)) = true := by
          rw [hf]
          rw [decide_eq_true_eq]
          exact ⟨u, v, hadj, by simp [PEqualNP.MetaComplexity.L1406.e2], by simp [PEqualNP.MetaComplexity.L1406.e2]⟩
        simpa [C, PEqualNP.MetaComplexity.L1406.val, PEqualNP.CircuitLowerBounds.Circuit.eval] using heval
      have hout_input : ¬ C.output < n := by
        intro hlt
        let t : Fin n := ⟨C.output, hlt⟩
        have hvt : PEqualNP.MetaComplexity.L1406.val C n (PEqualNP.MetaComplexity.L1406.e1 t) C.output = true := by
          rw [PEqualNP.MetaComplexity.L1406.val_input C n _ C.output hlt]
          simp [PEqualNP.MetaComplexity.L1406.e1, t]
        have heval : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (PEqualNP.MetaComplexity.L1406.e1 t)) = true := by
          simpa [C, PEqualNP.MetaComplexity.L1406.val, PEqualNP.CircuitLowerBounds.Circuit.eval] using hvt
        have hf' := hf (PEqualNP.MetaComplexity.L1406.e1 t)
        rw [heval] at hf'
        have hex : ∃ a b : Fin n, G.Adj a b ∧ PEqualNP.MetaComplexity.L1406.e1 t a = true ∧ PEqualNP.MetaComplexity.L1406.e1 t b = true := by
          simpa using hf'.symm
        exact PEqualNP.MetaComplexity.L1406.no_edge_e1 G t hex
      have hnos : ∀ t : Fin n, PEqualNP.MetaComplexity.L1406.val C n (PEqualNP.MetaComplexity.L1406.e1 t) C.output ≠ true := by
        intro t ht
        have heval : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn (PEqualNP.MetaComplexity.L1406.e1 t)) = true := by
          simpa [C, PEqualNP.MetaComplexity.L1406.val, PEqualNP.CircuitLowerBounds.Circuit.eval] using ht
        have hf' := hf (PEqualNP.MetaComplexity.L1406.e1 t)
        rw [heval] at hf'
        have hex : ∃ a b : Fin n, G.Adj a b ∧ PEqualNP.MetaComplexity.L1406.e1 t a = true ∧ PEqualNP.MetaComplexity.L1406.e1 t b = true := by
          simpa using hf'.symm
        exact PEqualNP.MetaComplexity.L1406.no_edge_e1 G t hex
      have hout_lt : C.output < n + C.gates.length := by
        by_contra hge
        have hnone : C.gates[C.output - n]? = none := by
          apply List.getElem?_eq_none_iff.mpr
          omega
        have hz := PEqualNP.MetaComplexity.L1406.val_none C n (PEqualNP.MetaComplexity.L1406.e2 u v) (C.output - n) hnone
        have ho : C.output = n + (C.output - n) := by omega
        rw [ho, hz] at hxe
        cases hxe
      let o := C.output - n
      have ho : C.output = n + o := by omega
      have holen : o < C.gates.length := by omega
      have hxo : PEqualNP.MetaComplexity.L1406.val C n (PEqualNP.MetaComplexity.L1406.e2 u v) (n + o) = true := by
        simpa [ho] using hxe
      obtain ⟨j, hjand, hjfire⟩ := PEqualNP.MetaComplexity.L1406.exists_and_nosing C n hfanC (n + o) (by
        intro t ht
        apply hnos t
        simpa [ho] using ht) (PEqualNP.MetaComplexity.L1406.e2 u v) hxo
      have hexAnd : ∃ k : ℕ,
          (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[k]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧
          PEqualNP.MetaComplexity.L1406.val C n (PEqualNP.MetaComplexity.L1406.e2 u v) (n + k) = true := ⟨j, hjand, hjfire⟩
      let k0 := Nat.find hexAnd
      have hk0spec := Nat.find_spec hexAnd
      obtain ⟨g0, hg0, hop0⟩ := hk0spec.1
      have hk0len : k0 < C.gates.length := (List.getElem?_eq_some_iff.mp hg0).1
      have hfire0 : PEqualNP.MetaComplexity.L1406.val C n (PEqualNP.MetaComplexity.L1406.e2 u v) (n + k0) = true := hk0spec.2
      have hmin0 : ∀ k : ℕ, k < k0 → ∀ g : PEqualNP.CircuitLowerBounds.Gate,
          C.gates[k]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
            PEqualNP.MetaComplexity.L1406.val C n (PEqualNP.MetaComplexity.L1406.e2 u v) (n + k) ≠ true := by
        intro k hk g hg hop hv
        exact (Nat.find_min hexAnd hk) ⟨⟨g, hg, hop⟩, hv⟩
      let j0 : Fin C.gates.length := ⟨k0, hk0len⟩
      have hgood : Good j0 := by
        refine ⟨u, v, hadj, hfire0, ?_, hmin0⟩
        have hget : C.gates.get j0 = g0 := by
          have hsome : C.gates[k0]? = some (C.gates.get j0) := by simpa [j0] using List.getElem?_eq_getElem hk0len
          rw [hsome] at hg0
          exact Option.some.inj hg0
        rw [hget]
        exact hop0
      have hmemI : j0 ∈ I := by
        apply hI
        have hget : C.gates.get j0 = g0 := by
          have hsome : C.gates[k0]? = some (C.gates.get j0) := by simpa [j0] using List.getElem?_eq_getElem hk0len
          rw [hsome] at hg0
          exact Option.some.inj hg0
        rw [hget]
        exact hop0
      have hcspec := Classical.choose_spec (center_spec j0 hgood) u v hadj hfire0 hmin0
      have hcuv : cen j0 = u ∨ cen j0 = v := by
        simpa [cen, hgood] using hcspec
      rcases hcuv with hcu | hcv
      · left
        exact Finset.mem_image.mpr ⟨j0, hmemI, hcu⟩
      · right
        exact Finset.mem_image.mpr ⟨j0, hmemI, hcv⟩
    · simpa [T] using (Finset.card_image_le : (I.image cen).card ≤ I.card)
