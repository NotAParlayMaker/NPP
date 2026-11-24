import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1602

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

lemma pair_le {n : ℕ} (u v : Fin n) (p : Fin n)
    (h : PEqualNP.EdgeOwnership.pairInput u u p = true) :
    PEqualNP.EdgeOwnership.pairInput u v p = true := by
  simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at h ⊢
  tauto

lemma pair_le' {n : ℕ} (u v : Fin n) (p : Fin n)
    (h : PEqualNP.EdgeOwnership.pairInput v v p = true) :
    PEqualNP.EdgeOwnership.pairInput u v p = true := by
  simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at h ⊢
  tauto

lemma single (gs : List Gate) (n : ℕ) (e0 : Fin n) (G : SimpleGraph (Fin n))
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hand : ∀ j (hj : j < gs.length), (gs[j]).op = GateOp.and → ∀ e w : Fin n, ¬ G.Adj e w →
      val gs n (PEqualNP.EdgeOwnership.pairInput e w) (n + j) = false)
    (x : Fin n → Bool) (hx : ∀ u v, x u = true → x v = true → ¬ G.Adj u v) :
    ∀ t, val gs n x t = true →
      ∃ u, x u = true ∧ val gs n (PEqualNP.EdgeOwnership.pairInput u u) t = true := by
  have hg' : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := fun g h => (hg g h).1
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro h
    by_cases h1 : t < n
    · rw [val_in gs n t h1] at h
      refine ⟨⟨t, h1⟩, h, ?_⟩
      rw [val_in gs n t h1]
      simp [PEqualNP.EdgeOwnership.pairInput]
    · by_cases h2 : t < n + gs.length
      · obtain ⟨j, rfl⟩ : ∃ j, t = n + j := ⟨t - n, by omega⟩
        have hj : j < gs.length := by omega
        have hk := val_key gs n j hj x
        rcases hg' _ (List.getElem_mem hj) with hop | hop
        · exfalso
          have contra : ∀ a b : ℕ, a < n + j → b < n + j → val gs n x a = true →
              val gs n x b = true → (∀ i ∈ (gs[j]).inputs, i = a ∨ i = b) → False := by
            intro a b ha hb hva hvb hall
            obtain ⟨u, hu, hua⟩ := ih a ha hva
            obtain ⟨v, hv, hvb'⟩ := ih b hb hvb
            have h1 := mono gs n hg' (PEqualNP.EdgeOwnership.pairInput u v) _ (pair_le u v) a hua
            have h2 := mono gs n hg' (PEqualNP.EdgeOwnership.pairInput u v) _ (pair_le' u v) b hvb'
            have hf := hand j hj hop u v (hx u v hu hv)
            rw [val_key gs n j hj, hop] at hf
            have ht : GateOp.and.eval ((gs[j]).inputs.map fun i =>
                if i < n + j then val gs n (PEqualNP.EdgeOwnership.pairInput u v) i else false)
                = true := by
              simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
              rintro _ ⟨i, hi, rfl⟩
              rcases hall i hi with rfl | rfl
              · simp [ha, h1]
              · simp [hb, h2]
            rw [ht] at hf
            exact absurd hf (by simp)
          rw [h, hop] at hk
          have hk' := hk.symm
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at hk'
          have hlen := (hg _ (List.getElem_mem hj)).2
          have hin : ∀ i ∈ (gs[j]).inputs, i < n + j ∧ val gs n x i = true := by
            intro i hi
            exact (ite_val _ _).mp (hk' _ ⟨i, hi, rfl⟩)
          rcases hI : (gs[j]).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
          · have hf := hand j hj hop e0 e0 (G.irrefl)
            rw [val_key gs n j hj, hop, hI] at hf
            simp [GateOp.eval] at hf
          · rw [hI] at hin
            have ha := hin a (by simp)
            exact contra a a ha.1 ha.1 ha.2 ha.2 (by rw [hI]; simp)
          · rw [hI] at hin
            have ha := hin a (by simp)
            have hb := hin b (by simp)
            exact contra a b ha.1 hb.1 ha.2 hb.2 (by rw [hI]; simp)
          · rw [hI] at hlen
            simp at hlen
        · rw [h, hop] at hk
          have hk' := hk.symm
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hk'
          obtain ⟨_, ⟨i, hi, rfl⟩, hb⟩ := hk'
          obtain ⟨hlt, hv⟩ := (ite_val _ _).mp hb
          obtain ⟨u, hu, hui⟩ := ih i hlt hv
          refine ⟨u, hu, ?_⟩
          rw [val_key gs n j hj, hop]
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
          exact ⟨_, ⟨i, hi, rfl⟩, (ite_val _ _).mpr ⟨hlt, hui⟩⟩
      · rw [val_out gs n t (by omega)] at h
        exact absurd h (by simp)

end PEqualNP.Outside.L_meta_1602

theorem PEqualNP.Outside.L_meta_1602 : (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1) → ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj], (∀ p q r s : Fin m, p ≠ r → q ≠ s → ¬ (H.Adj p q ∧ H.Adj q r ∧ H.Adj r s ∧ H.Adj s p)) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.circuitFun m D = PEqualNP.MetaComplexity.NestedCover.graphFun H ∅ → (∀ k : ℕ, k < D.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt D k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ e w : Fin m, ¬ H.Adj e w → PEqualNP.EdgeOwnership.gateVal m D k (PEqualNP.EdgeOwnership.pairInput e w) = false) → ∃ S : Finset (Fin m), (∀ y z : Fin m, H.Adj y z → y ∈ S ∨ z ∈ S) ∧ H.edgeFinset.card + S.card ≤ D.size + 1 := by
  intro hprem m H _ h4 D hmono hfun hand
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine ⟨∅, fun y => y.elim0, ?_⟩
    have : H.edgeFinset = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro e
      induction e using Sym2.ind with
      | _ a b => exact a.elim0
    rw [this]
    simp
  · have hg : ∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hgm
      have := hmono g hgm
      simpa using this
    have hand' : ∀ j (hj : j < D.gates.length),
        (D.gates[j]).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ e w : Fin m, ¬ H.Adj e w →
        PEqualNP.Outside.L_meta_1602.val D.gates m (PEqualNP.EdgeOwnership.pairInput e w) (m + j)
          = false := by
      intro j hj hop e w hew
      have hga : PEqualNP.MetaComplexity.NestedCover.gateAt D j = D.gates[j] := by
        simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj]
      exact hand j hj (by rw [hga]; exact hop) e w hew
    have res := hprem m H h4 D.gates D.output hg ?_ ?_
    · exact res
    · intro x
      have := congrFun hfun x
      simpa [PEqualNP.MetaComplexity.circuitFun, PEqualNP.MetaComplexity.NestedCover.graphFun]
        using this
    · intro i x hop hw
      by_contra hne
      have hx : ∀ u v, x u = true → x v = true → ¬ H.Adj u v := by
        intro u v hu hv hadj
        exact hne ⟨u, v, hadj, hu, hv⟩
      obtain ⟨u, _, hu⟩ := PEqualNP.Outside.L_meta_1602.single D.gates m ⟨0, hm⟩ H hg hand' x hx
        (m + i) hw
      have hf := hand' i i.2 (by simpa using hop) u u H.irrefl
      rw [hu] at hf
      exact absurd hf (by simp)
