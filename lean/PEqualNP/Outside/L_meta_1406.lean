import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1406

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

lemma gate_cases (gs : List Gate) (n : ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (j : ℕ) (hj : j < gs.length) :
    ∃ J : Finset ℕ, J.card ≤ 2 ∧ (∀ i ∈ J, i < n + j) ∧
      ((∀ x : Fin n → Bool, val gs n x (n + j) = true ↔ ∃ i ∈ J, val gs n x i = true) ∨
       ((gs[j]).op = GateOp.and ∧
        ∀ x : Fin n → Bool, val gs n x (n + j) = true ↔ ∀ i ∈ J, val gs n x i = true)) := by
  classical
  have hlen := (hg _ (List.getElem_mem hj)).2
  rcases (hg _ (List.getElem_mem hj)).1 with hop | hop
  · by_cases hall : ∀ i ∈ (gs[j]).inputs, i < n + j
    · refine ⟨(gs[j]).inputs.toFinset, (List.toFinset_card_le _).trans hlen,
        fun i hi => hall i (List.mem_toFinset.mp hi), Or.inr ⟨hop, fun x => ?_⟩⟩
      rw [val_key gs n j hj, hop]
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id, List.mem_toFinset]
      constructor
      · intro h i hi
        exact ((ite_val _ _).mp (h _ ⟨i, hi, rfl⟩)).2
      · rintro h b ⟨i, hi, rfl⟩
        exact (ite_val _ _).mpr ⟨hall i hi, h i hi⟩
    · refine ⟨∅, by simp, by simp, Or.inl fun x => ?_⟩
      rw [val_key gs n j hj, hop]
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id, Finset.notMem_empty,
        false_and, exists_false, iff_false, not_forall]
      rw [not_forall] at hall
      obtain ⟨i, hi⟩ := hall
      rw [Classical.not_imp] at hi
      refine ⟨_, ⟨i, hi.1, rfl⟩, ?_⟩
      simp [hi.2]
  · refine ⟨(gs[j]).inputs.toFinset.filter (fun i => i < n + j),
      (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen),
      fun i hi => (Finset.mem_filter.mp hi).2, Or.inl fun x => ?_⟩
    rw [val_key gs n j hj, hop]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id, Finset.mem_filter,
      List.mem_toFinset]
    constructor
    · rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
      have := (ite_val _ _).mp hb
      exact ⟨i, ⟨hi, this.1⟩, this.2⟩
    · rintro ⟨i, ⟨hi, hlt⟩, hv⟩
      exact ⟨_, ⟨i, hi, rfl⟩, (ite_val _ _).mpr ⟨hlt, hv⟩⟩

def sing {n : ℕ} (u : Fin n) : Fin n → Bool := fun p => decide (p = u)

def pair {n : ℕ} (u v : Fin n) : Fin n → Bool := fun p => decide (p = u ∨ p = v)

def Ch (gs : List Gate) (n : ℕ) (j : ℕ) (u v : Fin n) : Prop :=
  val gs n (pair u v) (n + j) = true ∧ val gs n (sing u) (n + j) = false ∧
  val gs n (sing v) (n + j) = false ∧
  ∀ t < n + j, val gs n (pair u v) t = true →
    val gs n (sing u) t = true ∨ val gs n (sing v) t = true

lemma star {n : ℕ} (G : SimpleGraph (Fin n))
    (hC4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (j : ℕ) (hj : j < gs.length)
    (hs : (gs[j]).op = GateOp.and → ∀ x : Fin n → Bool, val gs n x (n + j) = true →
      ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true) :
    ∃ S : Finset (Fin n), S.card ≤ 1 ∧
      ∀ u v : Fin n, Ch gs n j u v → (gs[j]).op = GateOp.and ∧ (u ∈ S ∨ v ∈ S) := by
  classical
  have hgop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := fun g h => (hg g h).1
  obtain ⟨J, hJc, hJlt, hcase⟩ := gate_cases gs n hg j hj
  rcases hcase with hor | ⟨hop, hand⟩
  · refine ⟨∅, by simp, ?_⟩
    rintro u v ⟨h1, h2, h3, h4⟩
    exfalso
    obtain ⟨i, hi, hv⟩ := (hor _).mp h1
    rcases h4 i (hJlt i hi) hv with h | h
    · have h' := (hor _).mpr ⟨i, hi, h⟩
      rw [h2] at h'
      exact Bool.false_ne_true h'
    · have h' := (hor _).mpr ⟨i, hi, h⟩
      rw [h3] at h'
      exact Bool.false_ne_true h'
  · by_cases hex : ∃ i ∈ J,
        (Finset.univ.filter (fun w : Fin n => val gs n (sing w) i = true)).card ≤ 1
    · obtain ⟨i0, hi0, hc⟩ := hex
      refine ⟨_, hc, ?_⟩
      rintro u v ⟨h1, h2, h3, h4⟩
      refine ⟨hop, ?_⟩
      have hv := (hand _).mp h1 i0 hi0
      rcases h4 i0 (hJlt i0 hi0) hv with h | h
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    · refine ⟨∅, by simp, ?_⟩
      rintro u v ⟨h1, h2, h3, h4⟩
      exfalso
      have hb : ∃ b ∈ J, val gs n (sing u) b = false := by
        by_contra hne
        have h' : val gs n (sing u) (n + j) = true := (hand _).mpr (fun i hi => by
          by_contra hf
          exact hne ⟨i, hi, by simpa using hf⟩)
        rw [h2] at h'
        exact Bool.false_ne_true h'
      have ha : ∃ a ∈ J, val gs n (sing v) a = false := by
        by_contra hne
        have h' : val gs n (sing v) (n + j) = true := (hand _).mpr (fun i hi => by
          by_contra hf
          exact hne ⟨i, hi, by simpa using hf⟩)
        rw [h3] at h'
        exact Bool.false_ne_true h'
      obtain ⟨b, hbJ, hbu⟩ := hb
      obtain ⟨a, haJ, hav⟩ := ha
      have hbv : val gs n (sing v) b = true := by
        rcases h4 b (hJlt b hbJ) ((hand _).mp h1 b hbJ) with h | h
        · rw [hbu] at h
          exact absurd h Bool.false_ne_true
        · exact h
      have hau : val gs n (sing u) a = true := by
        rcases h4 a (hJlt a haJ) ((hand _).mp h1 a haJ) with h | h
        · exact h
        · rw [hav] at h
          exact absurd h Bool.false_ne_true
      have hab : a ≠ b := by
        intro e
        rw [e, hbu] at hau
        exact Bool.false_ne_true hau
      have hJ : ∀ i ∈ J, i = a ∨ i = b := by
        intro i hi
        have hsub : ({a, b} : Finset ℕ) ⊆ J := by
          intro t ht
          rcases Finset.mem_insert.mp ht with e | e
          · rw [e]
            exact haJ
          · rw [Finset.mem_singleton.mp e]
            exact hbJ
        have heq := Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hab]; exact hJc)
        rw [← heq] at hi
        rcases Finset.mem_insert.mp hi with e | e
        · exact Or.inl e
        · exact Or.inr (Finset.mem_singleton.mp e)
      have hbip : ∀ w w' : Fin n, val gs n (sing w) a = true → val gs n (sing w') b = true →
          G.Adj w w' := by
        intro w w' hw hw'
        have hx : val gs n (pair w w') (n + j) = true := by
          apply (hand _).mpr
          intro i hi
          rcases hJ i hi with e | e
          · rw [e]
            refine mono gs n hgop (pair w w') (sing w) (fun p hp => ?_) _ hw
            simp only [sing, pair, decide_eq_true_eq] at hp ⊢
            exact Or.inl hp
          · rw [e]
            refine mono gs n hgop (pair w w') (sing w') (fun p hp => ?_) _ hw'
            simp only [sing, pair, decide_eq_true_eq] at hp ⊢
            exact Or.inr hp
        obtain ⟨p, q, hpq, hp, hq⟩ := hs hop _ hx
        simp only [pair, decide_eq_true_eq] at hp hq
        have hne := G.ne_of_adj hpq
        rcases hp with e1 | e1 <;> rcases hq with e2 | e2
        · exact absurd (e1.trans e2.symm) hne
        · rw [e1, e2] at hpq
          exact hpq
        · rw [e1, e2] at hpq
          exact hpq.symm
        · exact absurd (e1.trans e2.symm) hne
      have hA : 1 < (Finset.univ.filter (fun w : Fin n => val gs n (sing w) a = true)).card := by
        by_contra h
        exact hex ⟨a, haJ, by omega⟩
      have hB : 1 < (Finset.univ.filter (fun w : Fin n => val gs n (sing w) b = true)).card := by
        by_contra h
        exact hex ⟨b, hbJ, by omega⟩
      obtain ⟨w1, hw1, w2, hw2, hne⟩ := Finset.one_lt_card.mp hA
      obtain ⟨z1, hz1, z2, hz2, hne'⟩ := Finset.one_lt_card.mp hB
      have a1 := (Finset.mem_filter.mp hw1).2
      have a2 := (Finset.mem_filter.mp hw2).2
      have c1 := (Finset.mem_filter.mp hz1).2
      have c2 := (Finset.mem_filter.mp hz2).2
      exact hC4 w1 z1 w2 z2 hne hne'
        ⟨hbip w1 z1 a1 c1, (hbip w2 z1 a2 c1).symm, hbip w2 z2 a2 c2, (hbip w1 z2 a1 c2).symm⟩

lemma exists_charge {n : ℕ} (gs : List Gate) (u v : Fin n) (out : ℕ)
    (h1 : val gs n (pair u v) out = true) (h2 : val gs n (sing u) out = false)
    (h3 : val gs n (sing v) out = false) :
    ∃ j, ∃ _ : j < gs.length, Ch gs n j u v := by
  classical
  have hQ : ∃ t, val gs n (pair u v) t = true ∧ val gs n (sing u) t = false ∧
      val gs n (sing v) t = false := ⟨out, h1, h2, h3⟩
  obtain ⟨hm1, hm2, hm3⟩ := Nat.find_spec hQ
  have hmin : ∀ t < Nat.find hQ, ¬ (val gs n (pair u v) t = true ∧
      val gs n (sing u) t = false ∧ val gs n (sing v) t = false) :=
    fun t ht => Nat.find_min hQ ht
  have hge : n ≤ Nat.find hQ := by
    by_contra hlt
    have hlt' : Nat.find hQ < n := by omega
    rw [val_in gs n _ hlt'] at hm1 hm2 hm3
    simp only [pair, sing, decide_eq_true_eq, decide_eq_false_iff_not] at hm1 hm2 hm3
    rcases hm1 with h | h
    · exact hm2 h
    · exact hm3 h
  have hlt : Nat.find hQ < n + gs.length := by
    by_contra hge'
    rw [val_out gs n _ (by omega)] at hm1
    exact Bool.false_ne_true hm1
  refine ⟨Nat.find hQ - n, by omega, ?_⟩
  have e : n + (Nat.find hQ - n) = Nat.find hQ := by omega
  unfold Ch
  rw [e]
  refine ⟨hm1, hm2, hm3, fun t ht hp => ?_⟩
  by_contra hno
  apply hmin t ht
  refine ⟨hp, ?_, ?_⟩
  · by_contra hh
    exact hno (Or.inl (by simpa using hh))
  · by_contra hh
    exact hno (Or.inr (by simpa using hh))

end PEqualNP.Outside.L_meta_1406

theorem PEqualNP.Outside.L_meta_1406 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∀ I : Finset (Fin gates.length), (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → i ∈ I) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ T.card ≤ I.card := by
  intro n G _ hC4 gates out hg heval hsound I hI
  classical
  have hstar : ∀ i : Fin gates.length, ∃ S : Finset (Fin n), S.card ≤ 1 ∧
      ∀ u v : Fin n, PEqualNP.Outside.L_meta_1406.Ch gates n i.val u v →
        (gates[i.val]).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (u ∈ S ∨ v ∈ S) := by
    intro i
    apply PEqualNP.Outside.L_meta_1406.star G hC4 gates hg i.val i.isLt
    intro hop x hx
    exact hsound i x hop hx
  choose S hS1 hS2 using hstar
  refine ⟨I.biUnion S, ?_, ?_⟩
  · intro u v huv
    have hp : PEqualNP.Outside.L_meta_1406.val gates n (PEqualNP.Outside.L_meta_1406.pair u v) out = true := by
      have h := heval (PEqualNP.Outside.L_meta_1406.pair u v)
      change PEqualNP.Outside.L_meta_1406.val gates n (PEqualNP.Outside.L_meta_1406.pair u v) out = _ at h
      rw [h]
      simp only [decide_eq_true_eq]
      exact ⟨u, v, huv, by simp [PEqualNP.Outside.L_meta_1406.pair], by simp [PEqualNP.Outside.L_meta_1406.pair]⟩
    have hsing : ∀ w : Fin n, PEqualNP.Outside.L_meta_1406.val gates n (PEqualNP.Outside.L_meta_1406.sing w) out = false := by
      intro w
      have h := heval (PEqualNP.Outside.L_meta_1406.sing w)
      change PEqualNP.Outside.L_meta_1406.val gates n (PEqualNP.Outside.L_meta_1406.sing w) out = _ at h
      rw [h]
      simp only [decide_eq_false_iff_not]
      rintro ⟨a, b, hab, ha, hb⟩
      simp only [PEqualNP.Outside.L_meta_1406.sing, decide_eq_true_eq] at ha hb
      rw [ha, hb] at hab
      exact G.irrefl hab
    obtain ⟨j, hj, hch⟩ := PEqualNP.Outside.L_meta_1406.exists_charge gates u v out hp (hsing u) (hsing v)
    obtain ⟨hop, hmem⟩ := hS2 ⟨j, hj⟩ u v hch
    have hjI := hI ⟨j, hj⟩ hop
    rcases hmem with h | h
    · exact Or.inl (Finset.mem_biUnion.mpr ⟨_, hjI, h⟩)
    · exact Or.inr (Finset.mem_biUnion.mpr ⟨_, hjI, h⟩)
  · calc (I.biUnion S).card ≤ ∑ i ∈ I, (S i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ I, 1 := Finset.sum_le_sum (fun i _ => hS1 i)
      _ = I.card := by simp
