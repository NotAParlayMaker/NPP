import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_988

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma foldl_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨(g.op.eval (g.inputs.map fun i => w.getD i false)) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht, step, List.append_assoc, List.singleton_append]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl step w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun c =>
        if c < w.length + j then (gs.foldl step w).getD c false else false) := by
  obtain ⟨t0, ht0, hl0⟩ := foldl_prefix (gs.take j) w
  have hAlen : ((gs.take j).foldl step w).length = w.length + j := by
    rw [ht0, List.length_append, hl0, List.length_take]
    omega
  have hfold : gs.foldl step w =
      (gs.drop (j+1)).foldl step (step ((gs.take j).foldl step w) gs[j]) := by
    have h1 : gs.foldl step w = (gs.drop j).foldl step ((gs.take j).foldl step w) := by
      rw [← List.foldl_append, List.take_append_drop]
    rw [h1, List.drop_eq_getElem_cons hj, List.foldl_cons]
  obtain ⟨t, ht, _⟩ := foldl_prefix (gs.drop (j+1)) (step ((gs.take j).foldl step w) gs[j])
  have key : ∀ c, c < w.length + j →
      (gs.foldl step w).getD c false = ((gs.take j).foldl step w).getD c false := by
    intro c hc
    rw [hfold, ht, step, List.append_assoc, List.getD_append _ _ _ _ (by omega)]
  have hmap : ((gs[j]).inputs.map fun c =>
        if c < w.length + j then (gs.foldl step w).getD c false else false) =
      (gs[j]).inputs.map fun i => ((gs.take j).foldl step w).getD i false := by
    apply List.map_congr_left
    intro c _
    split_ifs with hc
    · exact key c hc
    · exact (List.getD_eq_default _ _ (by omega)).symm
  rw [hmap, hfold, ht, step, List.append_assoc, List.getD_append_right _ _ _ _ (by omega), hAlen,
    Nat.sub_self, List.singleton_append, List.getD_cons_zero]

def val (C : Circuit) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma val_input (C : Circuit) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (h : w < n) :
    val C x w = x ⟨w, h⟩ := by
  obtain ⟨t, ht, _⟩ := foldl_prefix C.gates (List.ofFn x)
  unfold val
  rw [wires_eq, ht, List.getD_append _ _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

lemma val_out (C : Circuit) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (h : n + C.gates.length ≤ w) :
    val C x w = false := by
  obtain ⟨t, ht, hl⟩ := foldl_prefix C.gates (List.ofFn x)
  unfold val
  rw [wires_eq, ht]
  apply List.getD_eq_default
  simp only [List.length_append, List.length_ofFn, hl]
  omega

lemma val_gate (C : Circuit) {n : ℕ} (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    val C x (n + j) = (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun c =>
      if c < n + j then val C x c else false) := by
  have h := foldl_getD_gate C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold val
  rw [wires_eq]
  exact h

lemma all_map_iff (l : List ℕ) (f : ℕ → Bool) : (l.map f).all id = true ↔ ∀ c ∈ l, f c = true := by
  simp

lemma any_map_iff (l : List ℕ) (f : ℕ → Bool) : (l.map f).any id = true ↔ ∃ c ∈ l, f c = true := by
  simp

lemma val_mono (C : Circuit) (n : ℕ)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ w (x x' : Fin n → Bool), (∀ v, x v = true → x' v = true) →
      val C x w = true → val C x' w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro x x' hxx' hw
  by_cases h1 : w < n
  · rw [val_input C x w h1] at hw
    rw [val_input C x' w h1]
    exact hxx' _ hw
  by_cases h2 : w < n + C.gates.length
  · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    rw [val_gate C x j hj] at hw
    rw [val_gate C x' j hj]
    have hrd : ∀ c, (if c < n + j then val C x c else false) = true →
        (if c < n + j then val C x' c else false) = true := by
      intro c hc
      split_ifs at hc ⊢ with hcj
      · exact ih c hcj x x' hxx' hc
    rcases hC _ (List.getElem_mem hj) with hop | hop
    · rw [hop] at hw ⊢
      simp only [GateOp.eval] at hw ⊢
      rw [all_map_iff] at hw ⊢
      intro c hc
      exact hrd c (hw c hc)
    · rw [hop] at hw ⊢
      simp only [GateOp.eval] at hw ⊢
      rw [any_map_iff] at hw ⊢
      obtain ⟨c, hc, hc'⟩ := hw
      exact ⟨c, hc, hrd c hc'⟩
  · rw [val_out C x w (by omega)] at hw
    exact absurd hw (by simp)

def Below (C : Circuit) {n : ℕ} (S : Finset (Fin n)) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, val C x w = true → ∃ p ∈ S, x p = true

lemma child (C : Circuit) (n : ℕ)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S : Finset (Fin n)) (j : ℕ) (hj : j < C.gates.length) (hB : Below C S (n + j))
    (z : Fin n → Bool) (hz : val C z (n + j) = true) :
    ∃ c ∈ (C.gates[j]).inputs, c < n + j ∧ Below C S c ∧ val C z c = true := by
  have hmono := val_mono C n (fun g hg => (hC g hg).1)
  have hval := fun x : Fin n → Bool => val_gate C x j hj
  obtain ⟨hop, hlen⟩ := hC _ (List.getElem_mem hj)
  rcases hop with hop | hop
  · rw [hval, hop] at hz
    simp only [GateOp.eval] at hz
    rw [all_map_iff] at hz
    have hall : ∀ c ∈ (C.gates[j]).inputs, c < n + j ∧ val C z c = true := by
      intro c hc
      have := hz c hc
      split_ifs at this with hcj
      · exact ⟨hcj, this⟩
    have hup : ∀ x : Fin n → Bool, (∀ c ∈ (C.gates[j]).inputs, val C x c = true) → val C x (n + j) = true := by
      intro x hx
      rw [hval, hop]
      simp only [GateOp.eval]
      rw [all_map_iff]
      intro c hc
      simp only [(hall c hc).1, ↓reduceIte]
      exact hx c hc
    generalize hl : (C.gates[j]).inputs = l at hall hup hlen
    match l, hlen with
    | [], _ =>
      exfalso
      obtain ⟨p, _, hp⟩ := hB (fun _ => false) (hup _ (by simp))
      exact absurd hp (by simp)
    | [a], _ =>
      refine ⟨a, by simp, (hall a (by simp)).1, ?_, (hall a (by simp)).2⟩
      intro x hx
      exact hB x (hup x (by simpa using hx))
    | [a, b], _ =>
      by_cases ha : Below C S a
      · exact ⟨a, by simp, (hall a (by simp)).1, ha, (hall a (by simp)).2⟩
      by_cases hb : Below C S b
      · exact ⟨b, by simp, (hall b (by simp)).1, hb, (hall b (by simp)).2⟩
      exfalso
      obtain ⟨xa, hxa⟩ := not_forall.mp ha
      obtain ⟨xb, hxb⟩ := not_forall.mp hb
      obtain ⟨hxa1, hxa2⟩ := not_imp.mp hxa
      obtain ⟨hxb1, hxb2⟩ := not_imp.mp hxb
      have hxa3 : val C (fun v => xa v || xb v) a = true :=
        hmono a xa _ (fun v hv => by simp [hv]) hxa1
      have hxb3 : val C (fun v => xa v || xb v) b = true :=
        hmono b xb _ (fun v hv => by simp [hv]) hxb1
      have hfire : val C (fun v => xa v || xb v) (n + j) = true := by
        apply hup
        intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact hxa3
        · exact hxb3
      obtain ⟨p, hp, hp'⟩ := hB _ hfire
      have h1 : xa p = false := by
        by_contra h
        exact hxa2 ⟨p, hp, by simpa using h⟩
      have h2 : xb p = false := by
        by_contra h
        exact hxb2 ⟨p, hp, by simpa using h⟩
      simp [h1, h2] at hp'
    | _ :: _ :: _ :: _, h => simp at h
  · rw [hval, hop] at hz
    simp only [GateOp.eval] at hz
    rw [any_map_iff] at hz
    obtain ⟨c, hc, hc'⟩ := hz
    split_ifs at hc' with hcj
    refine ⟨c, hc, hcj, ?_, hc'⟩
    intro x hx
    apply hB x
    rw [hval, hop]
    simp only [GateOp.eval]
    rw [any_map_iff]
    exact ⟨c, hc, by simp only [hcj, ↓reduceIte]; exact hx⟩

noncomputable def T (C : Circuit) {n : ℕ} (S : Finset (Fin n)) (e : Fin n → Fin n → Bool)
    (w : ℕ) : Finset (Fin n) :=
  @Finset.filter _ (fun p => Below C S w ∧ val C (e p) w = true) (Classical.decPred _) S

lemma mem_T (C : Circuit) {n : ℕ} (S : Finset (Fin n)) (e : Fin n → Fin n → Bool) (w : ℕ)
    (p : Fin n) : p ∈ T C S e w ↔ p ∈ S ∧ Below C S w ∧ val C (e p) w = true := by
  unfold T
  exact @Finset.mem_filter _ (fun p => Below C S w ∧ val C (e p) w = true) (Classical.decPred _) S p

lemma T_input (C : Circuit) {n : ℕ} (S Y : Finset (Fin n)) (hYS : Disjoint Y S)
    (e : Fin n → Fin n → Bool) (he : ∀ p v, e p v = true ↔ (v ∈ Y ∨ v = p))
    (w : ℕ) (h : w < n) : (T C S e w).card ≤ 1 := by
  rw [Finset.card_le_one]
  have key : ∀ p ∈ T C S e w, p = ⟨w, h⟩ := by
    intro p hp
    rw [mem_T] at hp
    obtain ⟨_, hB, hv⟩ := hp
    rw [val_input C _ w h, he] at hv
    obtain ⟨q, hq, hq'⟩ := hB (fun v => decide (v = ⟨w, h⟩)) (by rw [val_input C _ w h]; simp)
    have hqw : q = ⟨w, h⟩ := by simpa using hq'
    rcases hv with hv | hv
    · exact absurd (hqw ▸ hq) (Finset.disjoint_left.mp hYS hv)
    · exact hv.symm
  intro a ha b hb
  rw [key a ha, key b hb]

lemma T_out (C : Circuit) {n : ℕ} (S : Finset (Fin n)) (e : Fin n → Fin n → Bool)
    (w : ℕ) (h : n + C.gates.length ≤ w) : T C S e w = ∅ := by
  ext p
  rw [mem_T, val_out C _ w h]
  simp

lemma T_gate (C : Circuit) (n : ℕ)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S : Finset (Fin n)) (e : Fin n → Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    ∃ R : Finset ℕ, R.card ≤ 2 ∧ (∀ c ∈ R, c < n + j) ∧
      T C S e (n + j) ⊆ R.biUnion (T C S e) := by
  refine ⟨((C.gates[j]).inputs.toFinset).filter (fun c => c < n + j), ?_, ?_, ?_⟩
  · calc _ ≤ ((C.gates[j]).inputs.toFinset).card := Finset.card_filter_le _ _
      _ ≤ (C.gates[j]).inputs.length := List.toFinset_card_le _
      _ ≤ 2 := (hC _ (List.getElem_mem hj)).2
  · intro c hc
    exact (Finset.mem_filter.mp hc).2
  · intro p hp
    rw [mem_T] at hp
    obtain ⟨hpS, hB, hv⟩ := hp
    obtain ⟨c, hc, hcj, hBc, hvc⟩ := child C n hC S j hj hB (e p) hv
    rw [Finset.mem_biUnion]
    refine ⟨c, ?_, ?_⟩
    · rw [Finset.mem_filter, List.mem_toFinset]
      exact ⟨hc, hcj⟩
    · rw [mem_T]
      exact ⟨hpS, hBc, hvc⟩

theorem frontier {α : Type} [DecidableEq α] (T : ℕ → Finset α)
    (hT : ∀ w, 2 ≤ (T w).card →
      ∃ R : Finset ℕ, R.card ≤ 2 ∧ (∀ c ∈ R, c < w) ∧ T w ⊆ R.biUnion T) :
    ∀ k (F : Finset ℕ), (∀ w ∈ F, w < k) →
      (F.biUnion T).card ≤ F.card + ((Finset.range k).filter (fun w => 2 ≤ (T w).card)).card := by
  intro k
  induction k with
  | zero =>
    intro F hF
    have hF0 : F = ∅ := by
      ext w
      simp only [Finset.notMem_empty, iff_false]
      intro hw
      exact absurd (hF w hw) (Nat.not_lt_zero _)
    subst hF0
    simp
  | succ k ih =>
    intro F hF
    have hcount : ((Finset.range (k+1)).filter (fun w => 2 ≤ (T w).card)).card =
        ((Finset.range k).filter (fun w => 2 ≤ (T w).card)).card +
          (if 2 ≤ (T k).card then 1 else 0) := by
      rw [Finset.range_add_one, Finset.filter_insert]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem]
        simp
      · simp
    by_cases hk : k ∈ F
    · have hF0 : ∀ w ∈ F.erase k, w < k := by
        intro w hw
        have hw' := Finset.mem_erase.mp hw
        have := hF w hw'.2
        omega
      have hFeq : F = insert k (F.erase k) := (Finset.insert_erase hk).symm
      have hcardF : F.card = (F.erase k).card + 1 := by
        rw [Finset.card_erase_of_mem hk]
        have : 0 < F.card := Finset.card_pos.mpr ⟨k, hk⟩
        omega
      have hbu : F.biUnion T = T k ∪ (F.erase k).biUnion T := by
        conv_lhs => rw [hFeq]
        rw [Finset.biUnion_insert]
      by_cases h2 : 2 ≤ (T k).card
      · obtain ⟨R, hR, hRlt, hsub⟩ := hT k h2
        have hF1 : ∀ w ∈ F.erase k ∪ R, w < k := by
          intro w hw
          rcases Finset.mem_union.mp hw with h | h
          · exact hF0 w h
          · exact hRlt w h
        have hih := ih (F.erase k ∪ R) hF1
        have hsub2 : F.biUnion T ⊆ (F.erase k ∪ R).biUnion T := by
          rw [hbu, Finset.union_biUnion]
          intro p hp
          rcases Finset.mem_union.mp hp with h | h
          · exact Finset.mem_union_right _ (hsub h)
          · exact Finset.mem_union_left _ h
        have hu := Finset.card_union_le (F.erase k) R
        have hc1 := Finset.card_le_card hsub2
        simp only [hcount, h2, ↓reduceIte]
        omega
      · have hih := ih (F.erase k) hF0
        have hu := Finset.card_union_le (T k) ((F.erase k).biUnion T)
        rw [hbu, hcount]
        simp only [h2, ↓reduceIte]
        omega
    · have hF' : ∀ w ∈ F, w < k := by
        intro w hw
        have := hF w hw
        have hne : w ≠ k := fun h => hk (h ▸ hw)
        omega
      have := ih F hF'
      rw [hcount]
      split_ifs
      · omega
      · omega

lemma per_set (C : Circuit) (n : ℕ)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S Y : Finset (Fin n)) (hYS : Disjoint Y S)
    (e : Fin n → Fin n → Bool) (he : ∀ p v, e p v = true ↔ (v ∈ Y ∨ v = p))
    (o : ℕ) (hB : Below C S o) (hfire : ∀ p ∈ S, val C (e p) o = true) :
    S.card ≤ 1 + ((Finset.Ico n (n + C.gates.length)).filter
      (fun w => 2 ≤ (T C S e w).card)).card := by
  have hTo : T C S e o = S := by
    ext p
    rw [mem_T]
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, hB, hfire p h⟩
  have hT : ∀ w, 2 ≤ (T C S e w).card →
      ∃ R : Finset ℕ, R.card ≤ 2 ∧ (∀ c ∈ R, c < w) ∧ T C S e w ⊆ R.biUnion (T C S e) := by
    intro w hw
    by_cases h1 : w < n
    · have := T_input C S Y hYS e he w h1
      omega
    by_cases h2 : w < n + C.gates.length
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      exact T_gate C n hC S e j (by omega)
    · rw [T_out C S e w (by omega)] at hw
      simp at hw
  have hf := frontier (T C S e) hT (o + 1) {o} (by simp)
  rw [Finset.singleton_biUnion, hTo, Finset.card_singleton] at hf
  have hsub : (Finset.range (o + 1)).filter (fun w => 2 ≤ (T C S e w).card) ⊆
      (Finset.Ico n (n + C.gates.length)).filter (fun w => 2 ≤ (T C S e w).card) := by
    intro w hw
    rw [Finset.mem_filter] at hw ⊢
    refine ⟨?_, hw.2⟩
    rw [Finset.mem_Ico]
    constructor
    · by_contra h1
      have := T_input C S Y hYS e he w (by omega)
      omega
    · by_contra h2
      have h3 := hw.2
      rw [T_out C S e w (by omega)] at h3
      simp at h3
  have := Finset.card_le_card hsub
  omega

lemma double_count {m : ℕ} (s : Finset ℕ) (P : Fin m → ℕ → Prop) [∀ i w, Decidable (P i w)]
    (D : ℕ) (h : ∀ w ∈ s, (Finset.univ.filter (fun i => P i w)).card ≤ D) :
    ∑ i, (s.filter (fun w => P i w)).card ≤ D * s.card := by
  calc ∑ i, (s.filter (fun w => P i w)).card = ∑ i, ∑ w ∈ s, if P i w then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.card_filter]
    _ = ∑ w ∈ s, ∑ i, if P i w then 1 else 0 := Finset.sum_comm
    _ = ∑ w ∈ s, (Finset.univ.filter (fun i => P i w)).card := by
        apply Finset.sum_congr rfl
        intro w _
        rw [Finset.card_filter]
    _ ≤ ∑ w ∈ s, D := Finset.sum_le_sum h
    _ = D * s.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

lemma share (C : Circuit) {n m : ℕ} (S y : Fin m → Finset (Fin n))
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) (w : ℕ) (i i' : Fin m) (hne : i ≠ i')
    (hi : 2 ≤ (T C (S i) (fun p v => decide (v ∈ y i ∨ v = p)) w).card)
    (hi' : 2 ≤ (T C (S i') (fun p v => decide (v ∈ y i' ∨ v = p)) w).card) :
    ¬ Disjoint (y i) (S i') := by
  intro hdisj
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < (T C (S i)
    (fun p v => decide (v ∈ y i ∨ v = p)) w).card)
  obtain ⟨r, hr⟩ := Finset.card_pos.mp (by omega : 0 < (T C (S i')
    (fun p v => decide (v ∈ y i' ∨ v = p)) w).card)
  rw [mem_T] at hp hq hr
  have hB' := hr.2.1
  have hin : ∀ t ∈ S i, val C (fun v => decide (v ∈ y i ∨ v = t)) w = true → t ∈ S i' := by
    intro t _ ht
    obtain ⟨s, hs, hs'⟩ := hB' _ ht
    simp only [decide_eq_true_eq] at hs'
    rcases hs' with hs' | hs'
    · exact absurd hs (Finset.disjoint_left.mp hdisj hs')
    · exact hs' ▸ hs
  have hp' := hin p hp.1 hp.2.2
  have hq' := hin q hq.1 hq.2.2
  have := Finset.card_le_one.mp (hS i i' hne) p (Finset.mem_inter.mpr ⟨hp.1, hp'⟩) q
    (Finset.mem_inter.mpr ⟨hq.1, hq'⟩)
  exact hpq this

end PEqualNP.Outside.L_meta_988

theorem PEqualNP.Outside.L_meta_988 : ∀ (n m D : ℕ) (S y : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, Disjoint (y i) (S i)) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = true → ∃ p ∈ S i, x p = true) → (∀ i : Fin m, ∀ p ∈ S i, (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y i ∨ v = p)))).getD (o i) false = true) → (∀ J : Finset (Fin m), (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ Disjoint (y i) (S j)) → J.card ≤ D) → ∑ i : Fin m, (S i).card ≤ D * C.gates.length + m := by
  intro n m D S y C o hS hyS hC hbelow hfire hD
  have hper : ∀ i : Fin m, (S i).card ≤ 1 + ((Finset.Ico n (n + C.gates.length)).filter
      (fun w => 2 ≤ (PEqualNP.Outside.L_meta_988.T C (S i)
        (fun p v => decide (v ∈ y i ∨ v = p)) w).card)).card := by
    intro i
    exact PEqualNP.Outside.L_meta_988.per_set C n hC (S i) (y i) (hyS i)
      (fun p v => decide (v ∈ y i ∨ v = p)) (fun p v => by simp) (o i) (hbelow i) (hfire i)
  have hdc := PEqualNP.Outside.L_meta_988.double_count (Finset.Ico n (n + C.gates.length))
    (fun i w => 2 ≤ (PEqualNP.Outside.L_meta_988.T C (S i)
        (fun p v => decide (v ∈ y i ∨ v = p)) w).card) D (by
      intro w _
      apply hD
      intro i hi i' hi' hne
      rw [Finset.mem_filter] at hi hi'
      exact PEqualNP.Outside.L_meta_988.share C S y hS w i i' hne hi.2 hi'.2)
  rw [Nat.card_Ico, Nat.add_sub_cancel_left] at hdc
  calc ∑ i : Fin m, (S i).card ≤ ∑ i : Fin m, (1 + ((Finset.Ico n (n + C.gates.length)).filter
      (fun w => 2 ≤ (PEqualNP.Outside.L_meta_988.T C (S i)
        (fun p v => decide (v ∈ y i ∨ v = p)) w).card)).card) :=
        Finset.sum_le_sum (fun i _ => hper i)
    _ = m + ∑ i : Fin m, ((Finset.Ico n (n + C.gates.length)).filter
      (fun w => 2 ≤ (PEqualNP.Outside.L_meta_988.T C (S i)
        (fun p v => decide (v ∈ y i ∨ v = p)) w).card)).card := by
        rw [Finset.sum_add_distrib]
        simp
    _ ≤ D * C.gates.length + m := by omega
