import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_925

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

lemma val_split (gs : List Gate) (n : ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (t : ℕ) (h1 : n ≤ t) (h2 : t < n + gs.length) (x0 : Fin n → Bool)
    (h0 : val gs n x0 t = true) :
    ∃ J : Finset ℕ, J.card ≤ 2 ∧ (∀ i ∈ J, i < t ∧ val gs n x0 i = true) ∧
      ∀ x : Fin n → Bool, (∀ i ∈ J, val gs n x i = true) → val gs n x t = true := by
  obtain ⟨j, rfl⟩ : ∃ j, t = n + j := ⟨t - n, by omega⟩
  have hj : j < gs.length := by omega
  rw [val_key gs n j hj] at h0
  rcases (hg _ (List.getElem_mem hj)).1 with hop | hop
  · rw [hop] at h0
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at h0
    refine ⟨(gs[j]).inputs.toFinset, ?_, ?_, ?_⟩
    · exact (List.toFinset_card_le _).trans (hg _ (List.getElem_mem hj)).2
    · intro i hi
      exact (ite_val _ _).mp (h0 _ ⟨i, List.mem_toFinset.mp hi, rfl⟩)
    · intro x hx
      rw [val_key gs n j hj, hop]
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
      rintro b ⟨i, hi, rfl⟩
      exact (ite_val _ _).mpr
        ⟨((ite_val _ _).mp (h0 _ ⟨i, hi, rfl⟩)).1, hx i (List.mem_toFinset.mpr hi)⟩
  · rw [hop] at h0
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at h0
    obtain ⟨b, ⟨i, hi, rfl⟩, hb⟩ := h0
    refine ⟨{i}, by simp, ?_, ?_⟩
    · intro i' hi'
      rw [Finset.mem_singleton.mp hi']
      exact (ite_val _ _).mp hb
    · intro x hx
      rw [val_key gs n j hj, hop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
      exact ⟨_, ⟨i, hi, rfl⟩,
        (ite_val _ _).mpr ⟨((ite_val _ _).mp hb).1, hx i (Finset.mem_singleton_self i)⟩⟩

def Spec {n m : ℕ} (gs : List Gate) (S : Fin m → Finset (Fin n)) (w : Fin m) (t : ℕ) : Prop :=
  val gs n (ind (S w)) t = true ∧ ∀ v : Fin m, v ≠ w → val gs n (ind (S v)) t = false

lemma descent {n m : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (q K : ℕ) (hq : 1 ≤ q) (S : Fin m → Finset (Fin n))
    (hcS : ∀ i : Fin m, (S i).card = q + 1)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) (w : Fin m) (r : ℕ)
    (hr1 : val gs n (ind (S w)) r = true)
    (hr2 : ∀ x : Fin n → Bool, (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K →
      ¬ (∀ p ∈ S w, x p = true) → val gs n x r = false) :
    ∀ d T, T + d = n + gs.length → ∃ (F X : Finset ℕ) (P : Finset (Fin n)) (D : ℕ),
      (∀ t ∈ F, val gs n (ind (S w)) t = true) ∧
      (∀ x : Fin n → Bool, (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K →
        (∀ p ∈ P, x p = true) → ¬ (∀ p ∈ S w, x p = true) →
        ∃ t ∈ F, val gs n x t = false) ∧
      (∀ t ∈ X, Spec gs S w t ∧ n ≤ t ∧ t < n + gs.length ∧ T ≤ t) ∧
      F.card + D ≤ X.card + 1 ∧
      P.card ≤ D * q + 1 ∧ (P.card ≤ D * q ∨ ∃ v : Fin m, v ≠ w ∧ S v ⊆ P) ∧
      (P ∩ S w).card ≤ D ∧
      (∀ t ∈ F, t < T) := by
  classical
  have hgop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := fun g h => (hg g h).1
  intro d
  induction d with
  | zero =>
    intro T hT
    refine ⟨{r}, ∅, ∅, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      rw [Finset.mem_singleton.mp ht]
      exact hr1
    · intro x hx _ hxS
      exact ⟨r, Finset.mem_singleton_self r, hr2 x hx hxS⟩
    · simp
    · simp
    · simp
    · left
      simp
    · simp
    · intro t ht
      rw [Finset.mem_singleton.mp ht]
      by_contra hh
      rw [val_out gs n r (by omega)] at hr1
      exact absurd hr1 (by simp)
  | succ d ih =>
    intro T hT
    obtain ⟨F, X, P, D, i1, i2, i3, i4, i5, i5', i6, i7⟩ := ih (T + 1) (by omega)
    have i3' : ∀ t ∈ X, Spec gs S w t ∧ n ≤ t ∧ t < n + gs.length ∧ T ≤ t := by
      intro t ht
      obtain ⟨a, b, c, e⟩ := i3 t ht
      exact ⟨a, b, c, by omega⟩
    by_cases hTF : T ∈ F
    · have hT1 := i1 T hTF
      have hTN : T < n + gs.length := by
        by_contra hh
        rw [val_out gs n T (by omega)] at hT1
        exact absurd hT1 (by simp)
      have hFpos : 0 < F.card := Finset.card_pos.mpr ⟨T, hTF⟩
      have hFer : (F.erase T).card = F.card - 1 := Finset.card_erase_of_mem hTF
      have i1e : ∀ t ∈ F.erase T, val gs n (ind (S w)) t = true :=
        fun t ht => i1 t (Finset.mem_of_mem_erase ht)
      have i7e : ∀ t ∈ F.erase T, t < T := by
        intro t ht
        have h5 := i7 t (Finset.mem_of_mem_erase ht)
        have h6 := Finset.ne_of_mem_erase ht
        omega
      have hmul : (D + 1) * q = D * q + q := by ring
      by_cases hsp : Spec gs S w T ∧ n ≤ T
      · obtain ⟨hspec, hn⟩ := hsp
        obtain ⟨J, hJc, hJ1, hJ2⟩ := val_split gs n hg T hn hTN (ind (S w)) hT1
        refine ⟨F.erase T ∪ J, insert T X, P, D, ?_, ?_, ?_, ?_, i5, i5', i6, ?_⟩
        · intro t ht
          rcases Finset.mem_union.mp ht with ht | ht
          · exact i1e t ht
          · exact (hJ1 t ht).2
        · intro x hx hxP hxS
          obtain ⟨t, ht, hf⟩ := i2 x hx hxP hxS
          by_cases htT : t = T
          · rw [htT] at hf
            by_contra hcon
            have hall : ∀ i ∈ J, val gs n x i = true := by
              intro i hi
              by_contra hne
              exact hcon ⟨i, Finset.mem_union_right _ hi, by simpa using hne⟩
            rw [hJ2 x hall] at hf
            exact absurd hf (by simp)
          · exact ⟨t, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨htT, ht⟩), hf⟩
        · intro t ht
          rcases Finset.mem_insert.mp ht with ht | ht
          · rw [ht]
            exact ⟨hspec, hn, hTN, le_refl _⟩
          · exact i3' t ht
        · have hTX : T ∉ X := by
            intro hh
            have := (i3 T hh).2.2.2
            omega
          rw [Finset.card_insert_of_notMem hTX]
          have h1 : (F.erase T ∪ J).card ≤ (F.erase T).card + J.card :=
            Finset.card_union_le _ _
          omega
        · intro t ht
          rcases Finset.mem_union.mp ht with ht | ht
          · exact i7e t ht
          · exact (hJ1 t ht).1
      · by_cases hv : ∃ v : Fin m, v ≠ w ∧ val gs n (ind (S v)) T = true
        · obtain ⟨v, hvw, hvT⟩ := hv
          refine ⟨F.erase T, X, P ∪ S v, D + 1, i1e, ?_, i3', ?_, ?_, ?_, ?_, i7e⟩
          · intro x hx hxP hxS
            obtain ⟨t, ht, hf⟩ :=
              i2 x hx (fun p hp => hxP p (Finset.mem_union_left _ hp)) hxS
            refine ⟨t, Finset.mem_erase.mpr ⟨?_, ht⟩, hf⟩
            intro e
            rw [e] at hf
            have h8 := mono gs n hgop x (ind (S v))
              (fun p hp => hxP p (Finset.mem_union_right _ ((ind_true _ _).mp hp))) T hvT
            rw [hf] at h8
            exact absurd h8 (by simp)
          · omega
          · have hun : (P ∪ S v).card ≤ P.card + (S v \ P).card := by
              rw [← Finset.union_sdiff_self_eq_union]
              exact Finset.card_union_le _ _
            have hfull : (S v \ P).card ≤ q + 1 :=
              (Finset.card_le_card Finset.sdiff_subset).trans (hcS v).le
            rcases i5' with h | ⟨v', _, hsub⟩
            · omega
            · by_cases hvv : v' = v
              · rw [hvv] at hsub
                have h0 : (S v \ P).card = 0 := by
                  rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub]
                  simp
                omega
              · have h9 : (S v \ P).card ≤ (S v \ S v').card :=
                  Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hsub)
                have h10 := Finset.card_sdiff_add_card_inter (S v) (S v')
                have h11 := hS v v' (fun e => hvv e.symm)
                have h12 := hcS v
                omega
          · right
            exact ⟨v, hvw, Finset.subset_union_right⟩
          · have h13 : (P ∪ S v) ∩ S w = (P ∩ S w) ∪ (S v ∩ S w) :=
              Finset.union_inter_distrib_right _ _ _
            rw [h13]
            have h14 := Finset.card_union_le (P ∩ S w) (S v ∩ S w)
            have h15 := hS v w hvw
            omega
        · have hspec : Spec gs S w T := by
            refine ⟨hT1, ?_⟩
            intro v hvw
            by_contra hne
            exact hv ⟨v, hvw, by simpa using hne⟩
          have hTn : T < n := by
            by_contra hh
            exact hsp ⟨hspec, by omega⟩
          have hp : (⟨T, hTn⟩ : Fin n) ∈ S w := by
            rw [val_in gs n T hTn] at hT1
            exact (ind_true _ _).mp hT1
          refine ⟨F.erase T, X, insert (⟨T, hTn⟩ : Fin n) P, D + 1, i1e, ?_, i3', ?_, ?_, ?_, ?_,
            i7e⟩
          · intro x hx hxP hxS
            obtain ⟨t, ht, hf⟩ :=
              i2 x hx (fun p' hp' => hxP p' (Finset.mem_insert_of_mem hp')) hxS
            refine ⟨t, Finset.mem_erase.mpr ⟨?_, ht⟩, hf⟩
            intro e
            rw [e, val_in gs n T hTn, hxP _ (Finset.mem_insert_self _ _)] at hf
            exact absurd hf (by simp)
          · omega
          · have := Finset.card_insert_le (⟨T, hTn⟩ : Fin n) P
            omega
          · have := Finset.card_insert_le (⟨T, hTn⟩ : Fin n) P
            rcases i5' with h | ⟨v', hv'w, hsub⟩
            · left
              omega
            · right
              exact ⟨v', hv'w, hsub.trans (Finset.subset_insert _ _)⟩
          · rw [Finset.insert_inter_of_mem hp]
            have := Finset.card_insert_le (⟨T, hTn⟩ : Fin n) (P ∩ S w)
            omega
    · refine ⟨F, X, P, D, i1, i2, i3', i4, i5, i5', i6, ?_⟩
      intro t ht
      have h5 := i7 t ht
      have h6 : t ≠ T := by
        intro e
        rw [e] at ht
        exact hTF ht
      omega

lemma core {n m : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (q K : ℕ) (hq : 2 ≤ q) (S : Fin m → Finset (Fin n))
    (hcS : ∀ i : Fin m, (S i).card = q + 1)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) (w : Fin m) (r : ℕ)
    (hcorr : ∀ x : Fin n → Bool, (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K →
      val gs n x r = decide (∀ v ∈ S w, x v = true))
    (c : ℕ) (hc : c ≤ q) (hcK : c * q < K) :
    ∃ X : Finset ℕ, (∀ t ∈ X, Spec gs S w t ∧ n ≤ t ∧ t < n + gs.length) ∧ c ≤ X.card := by
  classical
  by_cases hc0 : c = 0
  · exact ⟨∅, by simp, by omega⟩
  have hqc : q ≤ c * q := Nat.le_mul_of_pos_left q (by omega)
  have hr1 : val gs n (ind (S w)) r = true := by
    rw [hcorr (ind (S w)) (by rw [ind_weight, hcS w]; omega)]
    simp [ind]
  have hr2 : ∀ x : Fin n → Bool, (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K →
      ¬ (∀ p ∈ S w, x p = true) → val gs n x r = false := by
    intro x hx hxS
    rw [hcorr x hx]
    simpa using hxS
  obtain ⟨F, X, P, D, _, i2, i3, i4, i5, _, i6, i7⟩ :=
    descent gs hg q K (by omega) S hcS hS w r hr1 hr2 (n + gs.length) 0 (by omega)
  refine ⟨X, fun t ht => ⟨(i3 t ht).1, (i3 t ht).2.1, (i3 t ht).2.2.1⟩, ?_⟩
  have hF : F = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro t ht
    have := i7 t ht
    omega
  by_cases hsub : S w ⊆ P
  · rw [Finset.inter_eq_right.mpr hsub, hcS w] at i6
    rw [hF] at i4
    simp at i4
    omega
  · have hK : K < P.card := by
      by_contra hle
      obtain ⟨t, ht, _⟩ := i2 (ind P) (by rw [ind_weight]; omega)
        (fun p hp => (ind_true _ _).mpr hp)
        (fun h => hsub (fun p hp => (ind_true _ _).mp (h p hp)))
      rw [hF] at ht
      simp at ht
    rw [hF] at i4
    simp at i4
    have h1 : c * q < D * q := by omega
    have h2 : c < D := Nat.lt_of_mul_lt_mul_right h1
    omega

end PEqualNP.Outside.L_meta_925

theorem PEqualNP.Outside.L_meta_925 : ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun i : Fin n => x i = true)).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → c * q < K → m * c ≤ gates.length := by
  intro q n m K S hq hcS hS gates out hg hcorr c hc hcK
  classical
  have hcore : ∀ w : Fin m, ∃ X : Finset ℕ,
      (∀ t ∈ X, PEqualNP.Outside.L_meta_925.Spec gates S w t ∧ n ≤ t ∧ t < n + gates.length) ∧ c ≤ X.card := by
    intro w
    exact PEqualNP.Outside.L_meta_925.core gates hg q K hq S hcS hS w (out w) (hcorr w) c hc hcK
  choose X hX1 hX2 using hcore
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ (Finset.univ : Finset (Fin m)),
      i ≠ j → Disjoint (X i) (X j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro t hti htj
    have h1 := (hX1 i t hti).1.1
    have h2 := (hX1 j t htj).1.2 i hij
    rw [h1] at h2
    exact absurd h2 (by simp)
  calc m * c = ∑ _i : Fin m, c := by simp
    _ ≤ ∑ i : Fin m, (X i).card := Finset.sum_le_sum (fun i _ => hX2 i)
    _ = (Finset.univ.biUnion X).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.Ico n (n + gates.length)).card := by
      apply Finset.card_le_card
      intro t ht
      obtain ⟨i, _, hti⟩ := Finset.mem_biUnion.mp ht
      exact Finset.mem_Ico.mpr (hX1 i t hti).2
    _ = gates.length := by simp
