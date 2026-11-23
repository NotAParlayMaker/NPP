import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L925

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) :=
  rfl

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  unfold wiresFrom
  rw [List.foldl_append]

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

lemma wiresFrom_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : w.length + gs.length ≤ i) : (wiresFrom gs w).getD i false = false := by
  apply List.getD_eq_default
  rw [wiresFrom_length]
  exact hi

lemma wiresFrom_take_getD (gs : List Gate) (w : List Bool) (j i : ℕ) (hj : j ≤ gs.length)
    (hi : i < w.length + j) :
    (wiresFrom (gs.take j) w).getD i false = (wiresFrom gs w).getD i false := by
  conv_rhs => rw [← List.take_append_drop j gs, wiresFrom_append]
  rw [wiresFrom_getD_lt (gs.drop j) (wiresFrom (gs.take j) w) i
    (by rw [wiresFrom_length, List.length_take]; omega)]

lemma wiresFrom_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (wiresFrom gs w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (wiresFrom (gs.take j) w).getD i false) := by
  have hd : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
  have hlen : (wiresFrom (gs.take j) w).length = w.length + j := by
    rw [wiresFrom_length, List.length_take]
    omega
  calc (wiresFrom gs w).getD (w.length + j) false
      = (wiresFrom (gs.take j ++ gs.drop j) w).getD (w.length + j) false := by
        rw [List.take_append_drop]
    _ = gs[j].op.eval (gs[j].inputs.map fun i => (wiresFrom (gs.take j) w).getD i false) := by
        rw [wiresFrom_append, hd, wiresFrom_cons,
          wiresFrom_getD_lt _ _ _ (by rw [List.length_append, hlen]; simp)]
        rw [← hlen, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
        simp

def val {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (k : ℕ) : Bool :=
  (wiresFrom gates (List.ofFn x)).getD k false

lemma val_input {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (k : ℕ) (hk : k < n) :
    val gates x k = x ⟨k, hk⟩ := by
  unfold val
  rw [wiresFrom_getD_lt _ _ _ (by simpa using hk)]
  simp [List.getD_eq_getElem?_getD, hk]

lemma val_out {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (k : ℕ)
    (hk : n + gates.length ≤ k) : val gates x k = false := by
  unfold val
  apply wiresFrom_getD_ge
  simpa using hk

lemma val_gate {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (j : ℕ) (hj : j < gates.length) :
    val gates x (n + j) = gates[j].op.eval (gates[j].inputs.map fun i =>
      if i < n + j then val gates x i else false) := by
  unfold val
  have h := wiresFrom_getD_gate gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  rw [h]
  congr 1
  apply List.map_congr_left
  intro i _
  split_ifs with hlt
  · exact wiresFrom_take_getD gates (List.ofFn x) j i (le_of_lt hj) (by simpa using hlt)
  · apply List.getD_eq_default
    rw [wiresFrom_length, List.length_take, List.length_ofFn]
    omega

lemma eval_and (l : List ℕ) (f : ℕ → Bool) :
    GateOp.and.eval (l.map f) = true ↔ ∀ i ∈ l, f i = true := by
  simp [GateOp.eval]

lemma eval_or (l : List ℕ) (f : ℕ → Bool) :
    GateOp.or.eval (l.map f) = true ↔ ∃ i ∈ l, f i = true := by
  simp [GateOp.eval]

lemma val_mono {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    ∀ k, val gates x k = true → val gates y k = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases h1 : k < n
    · rw [val_input _ _ _ h1] at hk ⊢
      exact hxy _ hk
    · by_cases h2 : k < n + gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, k = n + j := ⟨k - n, by omega⟩
        have hj : j < gates.length := by omega
        rw [val_gate _ _ _ hj] at hk ⊢
        rcases hg _ (List.getElem_mem hj) with hop | hop
        · rw [hop, eval_and] at hk ⊢
          intro i hi
          have hx := hk i hi
          by_cases hlt : i < n + j
          · rw [if_pos hlt] at hx ⊢
            exact ih i (by omega) hx
          · rw [if_neg hlt] at hx
            exact absurd hx (by simp)
        · rw [hop, eval_or] at hk ⊢
          obtain ⟨i, hi, hx⟩ := hk
          refine ⟨i, hi, ?_⟩
          by_cases hlt : i < n + j
          · rw [if_pos hlt] at hx ⊢
            exact ih i (by omega) hx
          · rw [if_neg hlt] at hx
            exact absurd hx (by simp)
      · rw [val_out _ _ _ (by omega)] at hk
        exact absurd hk (by simp)

def ind {n : ℕ} (X : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ X)

def weight {n : ℕ} (x : Fin n → Bool) : ℕ := (Finset.univ.filter (fun i : Fin n => x i = true)).card

lemma weight_ind {n : ℕ} (X : Finset (Fin n)) : weight (ind X) = X.card := by
  unfold weight ind
  congr 1
  ext i
  simp

def IsSpec {n m : ℕ} (gates : List Gate) (S : Fin m → Finset (Fin n)) (w : Fin m) (j : ℕ) : Prop :=
  val gates (ind (S w)) (n + j) = true ∧ ∀ v, v ≠ w → val gates (ind (S v)) (n + j) = false

open Classical in
noncomputable def specSet {n m : ℕ} (gates : List Gate) (S : Fin m → Finset (Fin n)) (w : Fin m)
    (N : ℕ) : Finset ℕ :=
  (Finset.range gates.length).filter (fun j => n + j < N ∧ IsSpec gates S w j)

lemma mem_specSet {n m : ℕ} (gates : List Gate) (S : Fin m → Finset (Fin n)) (w : Fin m)
    (N j : ℕ) : j ∈ specSet gates S w N ↔ j < gates.length ∧ n + j < N ∧ IsSpec gates S w j := by
  classical
  unfold specSet
  simp

lemma acc_set {n m : ℕ} (q : ℕ) (S : Fin m → Finset (Fin n)) (w v : Fin m) (hvw : v ≠ w)
    (hcard : ∀ i, (S i).card = q + 1) (hint : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (P : Finset (Fin n)) (d : ℕ) (hP1 : P.card ≤ d * q + 1)
    (hP2 : (∃ u, S u ⊆ P) ∨ P.card ≤ d * q) (hPw : (P ∩ S w).card ≤ d) :
    (P ∪ S v).card ≤ (d + 1) * q + 1 ∧ ((∃ u, S u ⊆ P ∪ S v) ∨ (P ∪ S v).card ≤ (d + 1) * q) ∧
      ((P ∪ S v) ∩ S w).card ≤ d + 1 := by
  have e : (d + 1) * q = d * q + q := by ring
  refine ⟨?_, Or.inl ⟨v, Finset.subset_union_right⟩, ?_⟩
  · rcases hP2 with ⟨u, hu⟩ | hP2
    · have hsd : (S v \ S u).card ≤ q := by
        by_cases huv : u = v
        · subst huv
          simp
        · have h := Finset.card_sdiff_add_card_inter (S v) (S u)
          rw [hint v u (Ne.symm huv), hcard v] at h
          omega
      have h1 : (P ∪ S v).card ≤ P.card + (S v \ P).card := by
        rw [← Finset.union_sdiff_self_eq_union]
        exact Finset.card_union_le _ _
      have h2 : (S v \ P).card ≤ (S v \ S u).card :=
        Finset.card_le_card (Finset.sdiff_subset_sdiff (subset_refl _) hu)
      omega
    · have h1 := Finset.card_union_le P (S v)
      rw [hcard v] at h1
      omega
  · rw [Finset.union_inter_distrib_right]
    have h1 := Finset.card_union_le (P ∩ S w) (S v ∩ S w)
    rw [hint v w hvw] at h1
    omega

lemma acc_point {n m : ℕ} (q : ℕ) (hq : 1 ≤ q) (S : Fin m → Finset (Fin n)) (w : Fin m)
    (i : Fin n) (P : Finset (Fin n)) (d : ℕ) (hP1 : P.card ≤ d * q + 1)
    (hP2 : (∃ u, S u ⊆ P) ∨ P.card ≤ d * q) (hPw : (P ∩ S w).card ≤ d) :
    (P ∪ {i}).card ≤ (d + 1) * q + 1 ∧ ((∃ u, S u ⊆ P ∪ {i}) ∨ (P ∪ {i}).card ≤ (d + 1) * q) ∧
      ((P ∪ {i}) ∩ S w).card ≤ d + 1 := by
  have e : (d + 1) * q = d * q + q := by ring
  have h1 : (P ∪ {i}).card ≤ P.card + 1 := by
    have := Finset.card_union_le P {i}
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · omega
  · rcases hP2 with ⟨u, hu⟩ | hP2
    · exact Or.inl ⟨u, hu.trans Finset.subset_union_left⟩
    · right
      omega
  · rw [Finset.union_inter_distrib_right]
    have h2 := Finset.card_union_le (P ∩ S w) ({i} ∩ S w)
    have h3 : ({i} ∩ S w).card ≤ 1 := by
      calc ({i} ∩ S w).card ≤ ({i} : Finset (Fin n)).card := Finset.card_le_card Finset.inter_subset_left
        _ = 1 := Finset.card_singleton i
    omega

lemma descent {n m : ℕ} (q K c : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (w : Fin m)
    (hq : 1 ≤ q) (hcard : ∀ i, (S i).card = q + 1) (hint : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcK : c * q < K) (hcq : c ≤ q) :
    ∀ (N : ℕ) (F : Finset ℕ) (P : Finset (Fin n)) (d : ℕ),
      (∀ k ∈ F, k < N) →
      (∀ k ∈ F, val gates (ind (S w)) k = true) →
      (∀ x : Fin n → Bool, weight x ≤ K → (∀ i ∈ P, x i = true) → ¬ (∀ v ∈ S w, x v = true) →
        ∃ k ∈ F, val gates x k = false) →
      P.card ≤ d * q + 1 →
      ((∃ u, S u ⊆ P) ∨ P.card ≤ d * q) →
      (P ∩ S w).card ≤ d →
      c + 1 ≤ d + F.card + (specSet gates S w N).card := by
  have hgop : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg' => (hg g hg').1
  intro N
  induction N with
  | zero =>
    intro F P d hlt _ hinv hP1 _ hPw
    have hF : F = ∅ := by
      rcases F.eq_empty_or_nonempty with h | ⟨k, hk⟩
      · exact h
      · exact absurd (hlt k hk) (Nat.not_lt_zero _)
    subst hF
    by_cases hcov : S w ⊆ P
    · have h1 : (S w).card ≤ d := by
        calc (S w).card = (P ∩ S w).card := by rw [Finset.inter_eq_right.2 hcov]
          _ ≤ d := hPw
      rw [hcard] at h1
      omega
    · by_cases hPK : P.card ≤ K
      · exfalso
        obtain ⟨k, hk, _⟩ := hinv (ind P) (by rw [weight_ind]; exact hPK)
          (by intro i hi; simp [ind, hi])
          (by
            intro hall
            apply hcov
            intro v hv
            simpa [ind] using hall v hv)
        simp at hk
      · have h1 : c * q < d * q := by omega
        have h2 : c < d := Nat.lt_of_mul_lt_mul_right h1
        omega
  | succ N ih =>
    intro F P d hlt htrue hinv hP1 hP2 hPw
    have hmono : (specSet gates S w N).card ≤ (specSet gates S w (N + 1)).card := by
      apply Finset.card_le_card
      intro j hj
      rw [mem_specSet] at hj ⊢
      exact ⟨hj.1, by omega, hj.2.2⟩
    by_cases hN : N ∈ F
    · have dropGen : ∀ X : Finset (Fin n), val gates (ind X) N = true →
          (P ∪ X).card ≤ (d + 1) * q + 1 →
          ((∃ u, S u ⊆ P ∪ X) ∨ (P ∪ X).card ≤ (d + 1) * q) →
          ((P ∪ X) ∩ S w).card ≤ d + 1 →
          c + 1 ≤ d + F.card + (specSet gates S w (N + 1)).card := by
        intro X hX h1 h2 h3
        have hlt' : ∀ k ∈ F.erase N, k < N := by
          intro k hk
          have hk' := Finset.mem_erase.1 hk
          have := hlt k hk'.2
          omega
        have htrue' : ∀ k ∈ F.erase N, val gates (ind (S w)) k = true :=
          fun k hk => htrue k (Finset.mem_of_mem_erase hk)
        have hinv' : ∀ x : Fin n → Bool, weight x ≤ K → (∀ i ∈ P ∪ X, x i = true) →
            ¬ (∀ v ∈ S w, x v = true) → ∃ k ∈ F.erase N, val gates x k = false := by
          intro x hw hP hnot
          obtain ⟨k, hk, hkf⟩ := hinv x hw (fun i hi => hP i (Finset.mem_union_left _ hi)) hnot
          refine ⟨k, Finset.mem_erase.2 ⟨?_, hk⟩, hkf⟩
          rintro rfl
          have hm := val_mono gates hgop (ind X) x
            (fun i hi => hP i (Finset.mem_union_right _ (by simpa [ind] using hi))) k hX
          rw [hkf] at hm
          exact Bool.false_ne_true hm
        have h := ih (F.erase N) (P ∪ X) (d + 1) hlt' htrue' hinv' h1 h2 h3
        have hc := Finset.card_erase_add_one hN
        omega
      by_cases hNn : N < n
      · have hi := htrue N hN
        rw [val_input _ _ _ hNn] at hi
        have hiS : (⟨N, hNn⟩ : Fin n) ∈ S w := by simpa [ind] using hi
        by_cases hex : ∃ v, v ≠ w ∧ (⟨N, hNn⟩ : Fin n) ∈ S v
        · obtain ⟨v, hvw, hv⟩ := hex
          obtain ⟨a1, a2, a3⟩ := acc_set q S w v hvw hcard hint P d hP1 hP2 hPw
          exact dropGen (S v) (by rw [val_input _ _ _ hNn]; simpa [ind] using hv) a1 a2 a3
        · obtain ⟨a1, a2, a3⟩ := acc_point q hq S w ⟨N, hNn⟩ P d hP1 hP2 hPw
          exact dropGen {⟨N, hNn⟩} (by rw [val_input _ _ _ hNn]; simp [ind]) a1 a2 a3
      · by_cases hNg : N < n + gates.length
        · obtain ⟨j, rfl⟩ : ∃ j, N = n + j := ⟨N - n, by omega⟩
          have hj : j < gates.length := by omega
          by_cases hsp : ∀ v, v ≠ w → val gates (ind (S v)) (n + j) = false
          · have hjS : j ∈ specSet gates S w (n + j + 1) := by
              rw [mem_specSet]
              exact ⟨hj, by omega, htrue _ hN, hsp⟩
            have hjN : j ∉ specSet gates S w (n + j) := by
              rw [mem_specSet]
              omega
            have hcardS : (specSet gates S w (n + j)).card + 1 ≤
                (specSet gates S w (n + j + 1)).card := by
              have hsub : insert j (specSet gates S w (n + j)) ⊆ specSet gates S w (n + j + 1) := by
                intro k hk
                rcases Finset.mem_insert.1 hk with rfl | hk
                · exact hjS
                · rw [mem_specSet] at hk ⊢
                  exact ⟨hk.1, by omega, hk.2.2⟩
              calc (specSet gates S w (n + j)).card + 1
                  = (insert j (specSet gates S w (n + j))).card :=
                    (Finset.card_insert_of_notMem hjN).symm
                _ ≤ _ := Finset.card_le_card hsub
            have hw := htrue _ hN
            rw [val_gate _ _ _ hj] at hw
            have hlen2 := (hg _ (List.getElem_mem hj)).2
            rcases (hg _ (List.getElem_mem hj)).1 with hop | hop
            · rw [hop, eval_and] at hw
              have hall : ∀ i ∈ gates[j].inputs, i < n + j ∧ val gates (ind (S w)) i = true := by
                intro i hi
                have h := hw i hi
                by_cases hlt' : i < n + j
                · rw [if_pos hlt'] at h
                  exact ⟨hlt', h⟩
                · rw [if_neg hlt'] at h
                  exact absurd h (by simp)
              let F' := F.erase (n + j) ∪ gates[j].inputs.toFinset
              have hlt' : ∀ k ∈ F', k < n + j := by
                intro k hk
                rcases Finset.mem_union.1 hk with hk | hk
                · have hk' := Finset.mem_erase.1 hk
                  have := hlt k hk'.2
                  omega
                · exact (hall k (List.mem_toFinset.1 hk)).1
              have htrue' : ∀ k ∈ F', val gates (ind (S w)) k = true := by
                intro k hk
                rcases Finset.mem_union.1 hk with hk | hk
                · exact htrue k (Finset.mem_of_mem_erase hk)
                · exact (hall k (List.mem_toFinset.1 hk)).2
              have hinv' : ∀ x : Fin n → Bool, weight x ≤ K → (∀ i ∈ P, x i = true) →
                  ¬ (∀ v ∈ S w, x v = true) → ∃ k ∈ F', val gates x k = false := by
                intro x hwx hP hnot
                obtain ⟨k, hk, hkf⟩ := hinv x hwx hP hnot
                by_cases hkN : k = n + j
                · subst hkN
                  rw [val_gate _ _ _ hj, hop] at hkf
                  have hnall : ¬ ∀ i ∈ gates[j].inputs,
                      (if i < n + j then val gates x i else false) = true := by
                    intro h
                    rw [← eval_and] at h
                    rw [h] at hkf
                    exact Bool.noConfusion hkf
                  push_neg at hnall
                  obtain ⟨i, hi, hif⟩ := hnall
                  have hilt := (hall i hi).1
                  rw [if_pos hilt] at hif
                  refine ⟨i, Finset.mem_union_right _ (List.mem_toFinset.2 hi), ?_⟩
                  simpa using hif
                · exact ⟨k, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hkN, hk⟩), hkf⟩
              have hF' : F'.card ≤ F.card + 1 := by
                show (F.erase (n + j) ∪ gates[j].inputs.toFinset).card ≤ F.card + 1
                have h1 := Finset.card_union_le (F.erase (n + j)) gates[j].inputs.toFinset
                have h2 := Finset.card_erase_add_one hN
                have h3 : gates[j].inputs.toFinset.card ≤ gates[j].inputs.length :=
                  List.toFinset_card_le _
                omega
              have h := ih F' P d hlt' htrue' hinv' hP1 hP2 hPw
              omega
            · rw [hop, eval_or] at hw
              obtain ⟨i, hi, hif⟩ := hw
              have hilt : i < n + j := by
                by_contra hc
                rw [if_neg hc] at hif
                exact Bool.noConfusion hif
              rw [if_pos hilt] at hif
              let F' := insert i (F.erase (n + j))
              have hlt' : ∀ k ∈ F', k < n + j := by
                intro k hk
                rcases Finset.mem_insert.1 hk with rfl | hk
                · exact hilt
                · have hk' := Finset.mem_erase.1 hk
                  have := hlt k hk'.2
                  omega
              have htrue' : ∀ k ∈ F', val gates (ind (S w)) k = true := by
                intro k hk
                rcases Finset.mem_insert.1 hk with rfl | hk
                · exact hif
                · exact htrue k (Finset.mem_of_mem_erase hk)
              have hinv' : ∀ x : Fin n → Bool, weight x ≤ K → (∀ i ∈ P, x i = true) →
                  ¬ (∀ v ∈ S w, x v = true) → ∃ k ∈ F', val gates x k = false := by
                intro x hwx hP hnot
                obtain ⟨k, hk, hkf⟩ := hinv x hwx hP hnot
                by_cases hkN : k = n + j
                · subst hkN
                  rw [val_gate _ _ _ hj, hop] at hkf
                  refine ⟨i, Finset.mem_insert_self _ _, ?_⟩
                  by_contra hne
                  have hti : val gates x i = true := by simpa using hne
                  have hev : GateOp.or.eval (gates[j].inputs.map fun i =>
                      if i < n + j then val gates x i else false) = true := by
                    rw [eval_or]
                    exact ⟨i, hi, by rw [if_pos hilt]; exact hti⟩
                  rw [hev] at hkf
                  exact Bool.noConfusion hkf
                · exact ⟨k, Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hkN, hk⟩), hkf⟩
              have hF' : F'.card ≤ F.card := by
                show (insert i (F.erase (n + j))).card ≤ F.card
                have h1 := Finset.card_insert_le i (F.erase (n + j))
                have h2 := Finset.card_erase_add_one hN
                omega
              have h := ih F' P d hlt' htrue' hinv' hP1 hP2 hPw
              omega
          · push_neg at hsp
            obtain ⟨v, hvw, hv⟩ := hsp
            have hv' : val gates (ind (S v)) (n + j) = true := by simpa using hv
            obtain ⟨a1, a2, a3⟩ := acc_set q S w v hvw hcard hint P d hP1 hP2 hPw
            exact dropGen (S v) hv' a1 a2 a3
        · have h := htrue N hN
          rw [val_out _ _ _ (by omega)] at h
          exact absurd h (by simp)
    · have hlt' : ∀ k ∈ F, k < N := by
        intro k hk
        have h1 := hlt k hk
        have h2 : k ≠ N := fun h => hN (h ▸ hk)
        omega
      have h := ih F P d hlt' htrue hinv hP1 hP2 hPw
      omega

end PEqualNP.Outside.L925

namespace PEqualNP.Outside.L925

open PEqualNP.CircuitLowerBounds

lemma main :∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  intro q n m K S hq hcard hint gates out hgates heval c hcq hcK
  classical
  rcases Nat.eq_zero_or_pos c with hc0 | hcpos
  · subst hc0
    simp
  have hqc : q ≤ c * q := Nat.le_mul_of_pos_left q hcpos
  have heval' : ∀ (w : Fin m) (x : Fin n → Bool), weight x ≤ K →
      val gates x (out w) = decide (∀ v ∈ S w, x v = true) := fun w x hx => heval w x hx
  have hper : ∀ w, c ≤ (specSet gates S w (n + gates.length)).card := by
    intro w
    have hSw : val gates (ind (S w)) (out w) = true := by
      rw [heval' w _ (by rw [weight_ind, hcard]; omega)]
      simp [ind]
    have hout : out w < n + gates.length := by
      by_contra h
      rw [val_out _ _ _ (by omega)] at hSw
      exact Bool.false_ne_true hSw
    have h := descent q K c S gates w (by omega) hcard hint hgates hcK hcq (n + gates.length)
      {out w} ∅ 0 (by simpa using hout) (by simpa using hSw)
      (by
        intro x hx _ hnot
        refine ⟨out w, by simp, ?_⟩
        rw [heval' w x hx]
        simpa using hnot)
      (by simp) (Or.inr (by simp)) (by simp)
    simp at h
    omega
  have hdisj : ∀ w ∈ (Finset.univ : Finset (Fin m)), ∀ w' ∈ (Finset.univ : Finset (Fin m)), w ≠ w' →
      Disjoint (specSet gates S w (n + gates.length)) (specSet gates S w' (n + gates.length)) := by
    intro w _ w' _ hne
    rw [Finset.disjoint_left]
    intro j hj hj'
    rw [mem_specSet] at hj hj'
    have h1 := hj.2.2.1
    have h2 := hj'.2.2.2 w hne
    rw [h1] at h2
    exact Bool.noConfusion h2
  have hsub : (Finset.univ.biUnion fun w => specSet gates S w (n + gates.length)) ⊆
      Finset.range gates.length := by
    intro j hj
    rw [Finset.mem_biUnion] at hj
    obtain ⟨w, _, hj⟩ := hj
    rw [mem_specSet] at hj
    exact Finset.mem_range.2 hj.1
  calc m * c = ∑ _w : Fin m, c := by simp
    _ ≤ ∑ w : Fin m, (specSet gates S w (n + gates.length)).card :=
        Finset.sum_le_sum (fun w _ => hper w)
    _ = (Finset.univ.biUnion fun w => specSet gates S w (n + gates.length)).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.range gates.length).card := Finset.card_le_card hsub
    _ = gates.length := Finset.card_range _

end PEqualNP.Outside.L925

theorem PEqualNP.Outside.L_meta_925 : ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length :=
  PEqualNP.Outside.L925.main
