import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1353

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

lemma val_dep (gs : List Gate) (n : ℕ) (j : ℕ) (hj : j < gs.length)
    (hop : (gs[j]).op = GateOp.and ∨ (gs[j]).op = GateOp.or) (x y : Fin n → Bool)
    (H : ∀ i ∈ ins gs n (n + j), val gs n y i = true → val gs n x i = true)
    (hy : val gs n y (n + j) = true) : val gs n x (n + j) = true := by
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
  rcases hop with hop | hop
  · rw [hop] at hy ⊢
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at hy ⊢
    rintro b ⟨i, hi, rfl⟩
    exact hstep i hi (hy _ ⟨i, hi, rfl⟩)
  · rw [hop] at hy ⊢
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hy ⊢
    obtain ⟨b, ⟨i, hi, rfl⟩, hb⟩ := hy
    exact ⟨_, ⟨i, hi, rfl⟩, hstep i hi hb⟩

lemma mono (gs : List Gate) (n z : ℕ)
    (hop : ∀ j (hj : j < gs.length), n + j ≠ z →
      (gs[j]).op = GateOp.and ∨ (gs[j]).op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ p, y p = true → x p = true)
    (hz : val gs n y z = true → val gs n x z = true) :
    ∀ t, val gs n y t = true → val gs n x t = true := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro h
    by_cases h0 : t = z
    · rw [h0] at h ⊢
      exact hz h
    · by_cases h1 : t < n
      · rw [val_in gs n t h1] at h ⊢
        exact hxy _ h
      · by_cases h2 : t < n + gs.length
        · obtain ⟨j, rfl⟩ : ∃ j, t = n + j := ⟨t - n, by omega⟩
          exact val_dep gs n j (by omega) (hop j (by omega) h0) x y
            (fun i hi => ih i (ins_lt gs n (n + j) i hi)) h
        · rw [val_out gs n t (by omega)] at h
          exact absurd h (by simp)

lemma split_false (gs : List Gate) (n z : ℕ)
    (j : ℕ) (hj : j < gs.length)
    (hop : (gs[j]).op = GateOp.and ∨ (gs[j]).op = GateOp.or)
    (x0 : Fin n → Bool) (h0 : val gs n x0 (n + j) = false) :
    ∃ J : Finset ℕ, J ⊆ (gs[j]).inputs.toFinset.erase z ∧
      (∀ i ∈ J, i < n + j ∧ val gs n x0 i = false) ∧
      ∀ x : Fin n → Bool, val gs n x z = false → (∀ i ∈ J, val gs n x i = false) →
        val gs n x (n + j) = false := by
  classical
  rw [val_key gs n j hj] at h0
  rcases hop with hop | hop
  · rw [hop] at h0
    simp only [GateOp.eval] at h0
    rw [List.all_eq_false] at h0
    obtain ⟨b, hb, hbf⟩ := h0
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    have hall : ∀ x : Fin n → Bool, (if i < n + j then val gs n x i else false) = false →
        val gs n x (n + j) = false := by
      intro x hx
      rw [val_key gs n j hj, hop]
      simp only [GateOp.eval]
      rw [List.all_eq_false]
      exact ⟨_, List.mem_map.mpr ⟨i, hi, rfl⟩, by simpa using hx⟩
    by_cases hlt : i < n + j
    · by_cases hiz : i = z
      · refine ⟨∅, by simp, by simp, fun x hxz _ => hall x ?_⟩
        simp only [hlt, ↓reduceIte]
        rw [hiz]
        exact hxz
      · have hv : val gs n x0 i = false := by simpa [hlt] using hbf
        refine ⟨{i}, ?_, ?_, fun x _ hx => hall x ?_⟩
        · intro a ha
          rw [Finset.mem_singleton.mp ha]
          exact Finset.mem_erase.mpr ⟨hiz, List.mem_toFinset.mpr hi⟩
        · intro a ha
          rw [Finset.mem_singleton.mp ha]
          exact ⟨hlt, hv⟩
        · simp only [hlt, ↓reduceIte]
          exact hx i (Finset.mem_singleton_self i)
    · refine ⟨∅, by simp, by simp, fun x _ _ => hall x ?_⟩
      simp only [hlt, ↓reduceIte]
  · rw [hop] at h0
    simp only [GateOp.eval] at h0
    rw [List.any_eq_false] at h0
    refine ⟨((gs[j]).inputs.toFinset.erase z).filter (fun i => i < n + j),
      Finset.filter_subset _ _, ?_, ?_⟩
    · intro i hi
      obtain ⟨hi1, hi2⟩ := Finset.mem_filter.mp hi
      have hmem := List.mem_toFinset.mp (Finset.mem_of_mem_erase hi1)
      have := h0 _ (List.mem_map.mpr ⟨i, hmem, rfl⟩)
      refine ⟨hi2, ?_⟩
      simpa [hi2] using this
    · intro x hxz hx
      rw [val_key gs n j hj, hop]
      simp only [GateOp.eval]
      rw [List.any_eq_false]
      intro b hb
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
      by_cases hlt : i < n + j
      · simp only [hlt, ↓reduceIte, id, Bool.not_eq_true]
        by_cases hiz : i = z
        · rw [hiz]
          exact hxz
        · exact hx i (Finset.mem_filter.mpr
            ⟨Finset.mem_erase.mpr ⟨hiz, List.mem_toFinset.mpr hi⟩, hlt⟩)
      · simp [hlt]

def co {n : ℕ} (A : Finset (Fin n)) : Fin n → Bool := fun p => decide (p ∉ A)

lemma co_false {n : ℕ} (A : Finset (Fin n)) (p : Fin n) : co A p = false ↔ p ∈ A := by
  simp [co]

lemma co_true {n : ℕ} (A : Finset (Fin n)) (p : Fin n) : co A p = true ↔ p ∉ A := by
  simp [co]

def Spec {n m : ℕ} (gs : List Gate) (S : Fin m → Finset (Fin n)) (w : Fin m) (t : ℕ) : Prop :=
  val gs n (co (S w)) t = false ∧ ∀ v : Fin m, v ≠ w → val gs n (co (S v)) t = true

def Clean (gs : List Gate) (n z t : ℕ) : Prop :=
  n ≤ t ∧ t < n + gs.length ∧ t ≠ z ∧ ∀ g : Gate, gs[t - n]? = some g → z ∉ g.inputs

lemma descent {n m : ℕ} (gs : List Gate) (z s : ℕ)
    (hlen : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hop : ∀ j (hj : j < gs.length), n + j ≠ z →
      (gs[j]).op = GateOp.and ∨ (gs[j]).op = GateOp.or)
    (hwin : ∀ A : Finset (Fin n), s + 1 + A.card ≤ n → val gs n (co A) z = false)
    (q : ℕ) (hq : 1 ≤ q) (S : Fin m → Finset (Fin n))
    (hcS : ∀ i : Fin m, (S i).card = q + 1)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) (w : Fin m) (r : ℕ)
    (hr1 : val gs n (co (S w)) r = false)
    (hr2 : ∀ A : Finset (Fin n), ¬ S w ⊆ A → val gs n (co A) r = true) :
    ∀ d T, T + d = n + gs.length → ∃ (F X : Finset ℕ) (P : Finset (Fin n)) (D : ℕ),
      (∀ t ∈ F, val gs n (co (S w)) t = false) ∧
      (∀ A : Finset (Fin n), s + 1 + A.card ≤ n → P ⊆ A → ¬ S w ⊆ A →
        ∃ t ∈ F, val gs n (co A) t = true) ∧
      (∀ t ∈ X, Spec gs S w t ∧ Clean gs n z t ∧ T ≤ t) ∧
      F.card + D ≤ X.card + 1 ∧
      P.card ≤ D * q + 1 ∧ (P.card ≤ D * q ∨ ∃ v : Fin m, v ≠ w ∧ S v ⊆ P) ∧
      (P ∩ S w).card ≤ D ∧
      (∀ t ∈ F, t < T) := by
  classical
  intro d
  induction d with
  | zero =>
    intro T hT
    refine ⟨{r}, ∅, ∅, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      rw [Finset.mem_singleton.mp ht]
      exact hr1
    · intro A _ _ hA
      exact ⟨r, Finset.mem_singleton_self r, hr2 A hA⟩
    · simp
    · simp
    · simp
    · left
      simp
    · simp
    · intro t ht
      rw [Finset.mem_singleton.mp ht]
      by_contra hh
      have h1 := hr2 ∅ (by
        intro hsub
        have := Finset.card_le_card hsub
        rw [hcS w] at this
        simp at this)
      rw [val_out gs n r (by omega)] at h1
      exact absurd h1 (by simp)
  | succ d ih =>
    intro T hT
    obtain ⟨F, X, P, D, i1, i2, i3, i4, i5, i5', i6, i7⟩ := ih (T + 1) (by omega)
    have i3' : ∀ t ∈ X, Spec gs S w t ∧ Clean gs n z t ∧ T ≤ t := by
      intro t ht
      obtain ⟨a, b, e⟩ := i3 t ht
      exact ⟨a, b, by omega⟩
    by_cases hTF : T ∈ F
    · have hT1 := i1 T hTF
      have hFpos : 0 < F.card := Finset.card_pos.mpr ⟨T, hTF⟩
      have hFer : (F.erase T).card = F.card - 1 := Finset.card_erase_of_mem hTF
      have i1e : ∀ t ∈ F.erase T, val gs n (co (S w)) t = false :=
        fun t ht => i1 t (Finset.mem_of_mem_erase ht)
      have i7e : ∀ t ∈ F.erase T, t < T := by
        intro t ht
        have h5 := i7 t (Finset.mem_of_mem_erase ht)
        have h6 := Finset.ne_of_mem_erase ht
        omega
      have hmul : (D + 1) * q = D * q + q := by ring
      have hTX : T ∉ X := by
        intro hh
        have := (i3 T hh).2.2
        omega
      have dropkeep : (∀ A : Finset (Fin n), s + 1 + A.card ≤ n →
          val gs n (co A) T = false) →
          ∃ (F X : Finset ℕ) (P : Finset (Fin n)) (D : ℕ),
          (∀ t ∈ F, val gs n (co (S w)) t = false) ∧
          (∀ A : Finset (Fin n), s + 1 + A.card ≤ n → P ⊆ A → ¬ S w ⊆ A →
            ∃ t ∈ F, val gs n (co A) t = true) ∧
          (∀ t ∈ X, Spec gs S w t ∧ Clean gs n z t ∧ T ≤ t) ∧
          F.card + D ≤ X.card + 1 ∧
          P.card ≤ D * q + 1 ∧ (P.card ≤ D * q ∨ ∃ v : Fin m, v ≠ w ∧ S v ⊆ P) ∧
          (P ∩ S w).card ≤ D ∧
          (∀ t ∈ F, t < T) := by
        intro hconst
        refine ⟨F.erase T, X, P, D + 1, i1e, ?_, i3', ?_, ?_, ?_, ?_, i7e⟩
        · intro A hA hPA hSA
          obtain ⟨t, ht, hf⟩ := i2 A hA hPA hSA
          refine ⟨t, Finset.mem_erase.mpr ⟨?_, ht⟩, hf⟩
          intro e
          rw [e, hconst A hA] at hf
          exact absurd hf (by simp)
        · omega
        · omega
        · rcases i5' with h | h
          · left
            omega
          · right
            exact h
        · omega
      by_cases hsp : Spec gs S w T ∧ n ≤ T ∧ T < n + gs.length ∧ T ≠ z
      · obtain ⟨hspec, hn, hN, hTz⟩ := hsp
        obtain ⟨j, hjT⟩ : ∃ j, T = n + j := ⟨T - n, by omega⟩
        have hj : j < gs.length := by omega
        have hopj := hop j hj (by rw [← hjT]; exact hTz)
        have hT1' : val gs n (co (S w)) (n + j) = false := by
          rw [← hjT]
          exact hT1
        obtain ⟨J, hJsub, hJ1, hJ2⟩ := split_false gs n z j hj hopj (co (S w)) hT1'
        have hJcard : J.card ≤ 2 := by
          have h1 := Finset.card_le_card hJsub
          have h2 : ((gs[j]).inputs.toFinset.erase z).card ≤ (gs[j]).inputs.toFinset.card :=
            Finset.card_le_card (Finset.erase_subset _ _)
          have h3 := List.toFinset_card_le (gs[j]).inputs
          have h4 := hlen _ (List.getElem_mem hj)
          omega
        have hF1 : ∀ t ∈ F.erase T ∪ J, val gs n (co (S w)) t = false := by
          intro t ht
          rcases Finset.mem_union.mp ht with ht | ht
          · exact i1e t ht
          · exact (hJ1 t ht).2
        have hF2 : ∀ A : Finset (Fin n), s + 1 + A.card ≤ n → P ⊆ A → ¬ S w ⊆ A →
            ∃ t ∈ F.erase T ∪ J, val gs n (co A) t = true := by
          intro A hA hPA hSA
          obtain ⟨t, ht, hf⟩ := i2 A hA hPA hSA
          by_cases htT : t = T
          · rw [htT, hjT] at hf
            by_contra hcon
            have hall : ∀ i ∈ J, val gs n (co A) i = false := by
              intro i hi
              by_contra hne
              exact hcon ⟨i, Finset.mem_union_right _ hi, by simpa using hne⟩
            rw [hJ2 (co A) (hwin A hA) hall] at hf
            exact absurd hf (by simp)
          · exact ⟨t, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨htT, ht⟩), hf⟩
        have hF7 : ∀ t ∈ F.erase T ∪ J, t < T := by
          intro t ht
          rcases Finset.mem_union.mp ht with ht | ht
          · exact i7e t ht
          · rw [hjT]
            exact (hJ1 t ht).1
        have hun : (F.erase T ∪ J).card ≤ (F.erase T).card + J.card :=
          Finset.card_union_le _ _
        by_cases hJ2c : J.card = 2
        · refine ⟨F.erase T ∪ J, insert T X, P, D, hF1, hF2, ?_, ?_, i5, i5', i6, hF7⟩
          · intro t ht
            rcases Finset.mem_insert.mp ht with ht | ht
            · rw [ht]
              refine ⟨hspec, ⟨hn, hN, hTz, ?_⟩, le_refl _⟩
              intro g hg hzg
              have hgj : g = gs[j] := by
                have h1 : gs[T - n]? = some gs[j] := by
                  rw [hjT, show n + j - n = j by omega]
                  exact List.getElem?_eq_getElem hj
                rw [h1] at hg
                exact (Option.some.inj hg).symm
              rw [hgj] at hzg
              have h1 := Finset.card_le_card hJsub
              have h2 : ((gs[j]).inputs.toFinset.erase z).card =
                  (gs[j]).inputs.toFinset.card - 1 :=
                Finset.card_erase_of_mem (List.mem_toFinset.mpr hzg)
              have h3 := List.toFinset_card_le (gs[j]).inputs
              have h4 := hlen _ (List.getElem_mem hj)
              omega
            · exact i3' t ht
          · rw [Finset.card_insert_of_notMem hTX]
            omega
        · refine ⟨F.erase T ∪ J, X, P, D, hF1, hF2, i3', ?_, i5, i5', i6, hF7⟩
          omega
      · by_cases hv : ∃ v : Fin m, v ≠ w ∧ val gs n (co (S v)) T = false
        · obtain ⟨v, hvw, hvT⟩ := hv
          refine ⟨F.erase T, X, P ∪ S v, D + 1, i1e, ?_, i3', ?_, ?_, ?_, ?_, i7e⟩
          · intro A hA hPA hSA
            obtain ⟨t, ht, hf⟩ := i2 A hA (Finset.union_subset_left hPA) hSA
            refine ⟨t, Finset.mem_erase.mpr ⟨?_, ht⟩, hf⟩
            intro e
            rw [e] at hf
            have h8 := mono gs n z hop (co (S v)) (co A) (fun p hp => by
              rw [co_true] at hp ⊢
              exact fun hpv => hp (Finset.union_subset_right hPA hpv))
              (fun hzz => by
                rw [hwin A hA] at hzz
                exact absurd hzz (by simp)) T hf
            rw [hvT] at h8
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
          by_cases hTn : T < n
          · have hp : (⟨T, hTn⟩ : Fin n) ∈ S w := by
              rw [val_in gs n T hTn] at hT1
              exact (co_false _ _).mp hT1
            refine ⟨F.erase T, X, insert (⟨T, hTn⟩ : Fin n) P, D + 1, i1e, ?_, i3', ?_, ?_, ?_,
              ?_, i7e⟩
            · intro A hA hPA hSA
              obtain ⟨t, ht, hf⟩ := i2 A hA ((Finset.subset_insert _ _).trans hPA) hSA
              refine ⟨t, Finset.mem_erase.mpr ⟨?_, ht⟩, hf⟩
              intro e
              rw [e, val_in gs n T hTn,
                (co_false A _).mpr (hPA (Finset.mem_insert_self _ _))] at hf
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
          · apply dropkeep
            intro A hA
            by_cases hTz : T = z
            · rw [hTz]
              exact hwin A hA
            · have hTN : ¬ T < n + gs.length := fun hlt => hsp ⟨hspec, by omega, hlt, hTz⟩
              exact val_out gs n T (by omega) _
    · refine ⟨F, X, P, D, i1, i2, i3', i4, i5, i5', i6, ?_⟩
      intro t ht
      have h5 := i7 t ht
      have h6 : t ≠ T := by
        intro e
        rw [e] at ht
        exact hTF ht
      omega

lemma core {n m : ℕ} (gs : List Gate) (z s : ℕ)
    (hlen : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hop : ∀ j (hj : j < gs.length), n + j ≠ z →
      (gs[j]).op = GateOp.and ∨ (gs[j]).op = GateOp.or)
    (hwin : ∀ A : Finset (Fin n), s + 1 + A.card ≤ n → val gs n (co A) z = false)
    (q : ℕ) (hq : 2 ≤ q) (S : Fin m → Finset (Fin n))
    (hcS : ∀ i : Fin m, (S i).card = q + 1)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) (w : Fin m) (r : ℕ)
    (hcorr : ∀ x : Fin n → Bool, val gs n x r = decide (∃ v ∈ S w, x v = true))
    (c : ℕ) (hc : c ≤ q) (hcK : c = 0 ∨ c * q + (s + 1) < n) :
    ∃ X : Finset ℕ, (∀ t ∈ X, Spec gs S w t ∧ Clean gs n z t) ∧ c ≤ X.card := by
  classical
  by_cases hc0 : c = 0
  · exact ⟨∅, by simp, by omega⟩
  have hcK' : c * q + (s + 1) < n := by
    rcases hcK with h | h
    · exact absurd h hc0
    · exact h
  have hr1 : val gs n (co (S w)) r = false := by
    rw [hcorr]
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro v hv hco
    exact (co_true _ _).mp hco hv
  have hr2 : ∀ A : Finset (Fin n), ¬ S w ⊆ A → val gs n (co A) r = true := by
    intro A hA
    rw [hcorr]
    simp only [decide_eq_true_eq]
    rw [Finset.not_subset] at hA
    obtain ⟨v, hv, hvA⟩ := hA
    exact ⟨v, hv, (co_true _ _).mpr hvA⟩
  obtain ⟨F, X, P, D, _, i2, i3, i4, i5, _, i6, i7⟩ :=
    descent gs z s hlen hop hwin q (by omega) S hcS hS w r hr1 hr2 (n + gs.length) 0 (by omega)
  refine ⟨X, fun t ht => ⟨(i3 t ht).1, (i3 t ht).2.1⟩, ?_⟩
  have hF : F = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro t ht
    have := i7 t ht
    omega
  rw [hF] at i4
  simp only [Finset.card_empty, zero_add] at i4
  by_cases hsub : S w ⊆ P
  · rw [Finset.inter_eq_right.mpr hsub, hcS w] at i6
    omega
  · have hP : n < s + 1 + P.card := by
      by_contra hle
      obtain ⟨t, ht, _⟩ := i2 P (by omega) (Finset.Subset.refl _) hsub
      rw [hF] at ht
      simp at ht
    have h1 : c * q < D * q := by omega
    have h2 : c < D := Nat.lt_of_mul_lt_mul_right h1
    omega

end PEqualNP.Outside.L_meta_1353

theorem PEqualNP.Outside.L_meta_1353 : ∀ (q n m s : ℕ) (S : Fin m → Finset (Fin n)),
    2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
        decide (∃ v ∈ S w, x v = true)) →
    (∀ x : Fin n → Bool, s + 1 ≤ (Finset.univ.filter (fun v : Fin n => x v = true)).card →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn x) = false) →
    m * min q ((n - (s + 1) + q - 1) / q - 1) +
        (Finset.univ.filter (fun i : Fin gates.length =>
          j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 1 ≤ gates.length := by
  intro q n m s S hq hcS hS gates out j hg hjnot honly hcorr hheavy
  classical
  have hjlt : (j : ℕ) < gates.length := j.isLt
  have hlen : ∀ g ∈ gates, g.inputs.length ≤ 2 := fun g h => (hg g h).2
  have hop : ∀ j' (hj' : j' < gates.length), n + j' ≠ n + (j : ℕ) →
      (gates[j']).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      (gates[j']).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro j' hj' hne
    rcases (hg _ (List.getElem_mem hj')).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have := honly ⟨j', hj'⟩ h
      apply hne
      rw [← this]
  have hwin : ∀ A : Finset (Fin n), s + 1 + A.card ≤ n →
      PEqualNP.Outside.L_meta_1353.val gates n (PEqualNP.Outside.L_meta_1353.co A) (n + (j : ℕ)) = false := by
    intro A hA
    apply hheavy
    have h1 : Finset.univ.filter (fun v : Fin n => PEqualNP.Outside.L_meta_1353.co A v = true) = Aᶜ := by
      ext p
      simp [PEqualNP.Outside.L_meta_1353.co]
    rw [h1, Finset.card_compl, Fintype.card_fin]
    omega
  have hcle : min q ((n - (s + 1) + q - 1) / q - 1) ≤ q := Nat.min_le_left _ _
  have hcK : min q ((n - (s + 1) + q - 1) / q - 1) = 0 ∨
      min q ((n - (s + 1) + q - 1) / q - 1) * q + (s + 1) < n := by
    by_cases h0 : min q ((n - (s + 1) + q - 1) / q - 1) = 0
    · exact Or.inl h0
    · right
      have h1 : min q ((n - (s + 1) + q - 1) / q - 1) ≤ (n - (s + 1) + q - 1) / q - 1 :=
        Nat.min_le_right _ _
      have h2 : min q ((n - (s + 1) + q - 1) / q - 1) * q ≤
          ((n - (s + 1) + q - 1) / q - 1) * q := Nat.mul_le_mul_right q h1
      have h3 : ((n - (s + 1) + q - 1) / q - 1) * q =
          (n - (s + 1) + q - 1) / q * q - q := by
        rw [Nat.sub_mul, one_mul]
      have h4 : (n - (s + 1) + q - 1) / q * q ≤ n - (s + 1) + q - 1 := Nat.div_mul_le_self _ _
      have h5 : 1 ≤ (n - (s + 1) + q - 1) / q - 1 := by omega
      have h6 : 2 * q ≤ (n - (s + 1) + q - 1) / q * q := by
        have : 2 ≤ (n - (s + 1) + q - 1) / q := by omega
        exact Nat.mul_le_mul_right q this
      omega
  have hcore : ∀ w : Fin m, ∃ X : Finset ℕ,
      (∀ t ∈ X, PEqualNP.Outside.L_meta_1353.Spec gates S w t ∧ PEqualNP.Outside.L_meta_1353.Clean gates n (n + (j : ℕ)) t) ∧
        min q ((n - (s + 1) + q - 1) / q - 1) ≤ X.card := by
    intro w
    exact PEqualNP.Outside.L_meta_1353.core gates (n + (j : ℕ)) s hlen hop hwin q hq S hcS hS w (out w)
      (fun x => hcorr w x) _ hcle hcK
  choose X hX1 hX2 using hcore
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ i' ∈ (Finset.univ : Finset (Fin m)),
      i ≠ i' → Disjoint (X i) (X i') := by
    intro i _ i' _ hii
    rw [Finset.disjoint_left]
    intro t hti hti'
    have h1 := (hX1 i t hti).1.1
    have h2 := (hX1 i' t hti').1.2 i hii
    rw [h1] at h2
    exact absurd h2 (by simp)
  have hinj : Set.InjOn (fun i : Fin gates.length => n + i.val)
      (↑(Finset.univ.filter (fun i : Fin gates.length =>
        j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)) : Set (Fin gates.length)) := by
    intro a _ b _ hab
    apply Fin.ext
    simp only [] at hab
    omega
  have hznot : n + (j : ℕ) ∉ (Finset.univ.filter (fun i : Fin gates.length =>
      j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).image (fun i : Fin gates.length => n + i.val) := by
    intro hmem
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hmem
    have := (Finset.mem_filter.mp hi).2.1
    have h2 : (j : ℕ) < (i : ℕ) := this
    omega
  have hRcard : (insert (n + (j : ℕ)) ((Finset.univ.filter (fun i : Fin gates.length =>
      j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).image (fun i : Fin gates.length => n + i.val))).card =
      (Finset.univ.filter (fun i : Fin gates.length =>
        j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 1 := by
    rw [Finset.card_insert_of_notMem hznot, Finset.card_image_of_injOn hinj]
  have hdis2 : Disjoint (Finset.univ.biUnion X)
      (insert (n + (j : ℕ)) ((Finset.univ.filter (fun i : Fin gates.length =>
        j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).image (fun i : Fin gates.length => n + i.val))) := by
    rw [Finset.disjoint_left]
    intro t ht htR
    obtain ⟨w, _, htw⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨_, ⟨_, _, htz, hclean⟩⟩ := hX1 w t htw
    rcases Finset.mem_insert.mp htR with e | hR
    · exact htz e
    · obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hR
      have hzin := (Finset.mem_filter.mp hi).2.2
      apply hclean (gates.get i) _ hzin
      rw [← he, show n + (i : ℕ) - n = (i : ℕ) by omega]
      exact List.getElem?_eq_getElem i.isLt
  have hsubI : Finset.univ.biUnion X ∪
      (insert (n + (j : ℕ)) ((Finset.univ.filter (fun i : Fin gates.length =>
        j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).image (fun i : Fin gates.length => n + i.val))) ⊆
      Finset.Ico n (n + gates.length) := by
    intro t ht
    rcases Finset.mem_union.mp ht with h | h
    · obtain ⟨w, _, htw⟩ := Finset.mem_biUnion.mp h
      obtain ⟨_, ⟨h1, h2, _, _⟩⟩ := hX1 w t htw
      exact Finset.mem_Ico.mpr ⟨h1, h2⟩
    · rcases Finset.mem_insert.mp h with e | hR
      · rw [e]
        exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      · obtain ⟨i, _, he⟩ := Finset.mem_image.mp hR
        rw [← he]
        have := i.isLt
        exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hfin := Finset.card_le_card hsubI
  rw [Finset.card_union_of_disjoint hdis2, hRcard, Finset.card_biUnion hdisj, Nat.card_Ico] at hfin
  have hsum : m * min q ((n - (s + 1) + q - 1) / q - 1) ≤ ∑ w : Fin m, (X w).card := by
    calc m * min q ((n - (s + 1) + q - 1) / q - 1)
        = ∑ _w : Fin m, min q ((n - (s + 1) + q - 1) / q - 1) := by simp
      _ ≤ ∑ w : Fin m, (X w).card := Finset.sum_le_sum (fun w _ => hX2 w)
  omega
