import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1032

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

def Al {n : ℕ} (K : ℕ) (y : Finset (Fin n)) (x : Fin n → Bool) : Prop :=
  (∀ v ∈ y, x v = true) ∧ ((Finset.univ.filter (fun i : Fin n => x i = true)) \ y).card ≤ K

def Spec {n m : ℕ} (gs : List Gate) (S : Fin m → Finset (Fin n)) (y : Finset (Fin n))
    (w : Fin m) (t : ℕ) : Prop :=
  val gs n (ind (y ∪ S w)) t = true ∧
    ∀ v : Fin m, v ≠ w → 2 ≤ (S v \ y).card → val gs n (ind (y ∪ S v)) t = false

lemma ind_filter {n : ℕ} (Z : Finset (Fin n)) :
    Finset.univ.filter (fun i : Fin n => ind Z i = true) = Z := by
  ext p
  simp [ind]

lemma descent {n m : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (q K : ℕ) (hq : 1 ≤ q) (S : Fin m → Finset (Fin n)) (y : Finset (Fin n))
    (hcS : ∀ i : Fin m, (S i).card = q + 1)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) (w : Fin m) (r : ℕ)
    (hr1 : val gs n (ind (y ∪ S w)) r = true)
    (hr2 : ∀ x : Fin n → Bool, Al K y x → ¬ (∀ p ∈ S w, x p = true) → val gs n x r = false) :
    ∀ d T, T + d = n + gs.length → ∃ (F X : Finset ℕ) (P : Finset (Fin n)) (D : ℕ),
      (∀ t ∈ F, val gs n (ind (y ∪ S w)) t = true) ∧
      (∀ x : Fin n → Bool, Al K y x → (∀ p ∈ P, x p = true) → ¬ (∀ p ∈ S w, x p = true) →
        ∃ t ∈ F, val gs n x t = false) ∧
      (∀ t ∈ X, Spec gs S y w t ∧ n ≤ t ∧ t < n + gs.length ∧ T ≤ t) ∧
      F.card + D ≤ X.card + 1 ∧
      P.card ≤ D * q + 1 ∧ (P.card ≤ D * q ∨ ∃ v : Fin m, v ≠ w ∧ S v \ y ⊆ P) ∧
      (P ∩ (S w \ y)).card ≤ D ∧
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
    have i3' : ∀ t ∈ X, Spec gs S y w t ∧ n ≤ t ∧ t < n + gs.length ∧ T ≤ t := by
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
      have i1e : ∀ t ∈ F.erase T, val gs n (ind (y ∪ S w)) t = true :=
        fun t ht => i1 t (Finset.mem_of_mem_erase ht)
      have i7e : ∀ t ∈ F.erase T, t < T := by
        intro t ht
        have h5 := i7 t (Finset.mem_of_mem_erase ht)
        have h6 := Finset.ne_of_mem_erase ht
        omega
      have hmul : (D + 1) * q = D * q + q := by ring
      by_cases hsp : Spec gs S y w T ∧ n ≤ T
      · obtain ⟨hspec, hn⟩ := hsp
        obtain ⟨J, hJc, hJ1, hJ2⟩ := val_split gs n hg T hn hTN (ind (y ∪ S w)) hT1
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
      · by_cases hv : ∃ v : Fin m, v ≠ w ∧ 2 ≤ (S v \ y).card ∧
            val gs n (ind (y ∪ S v)) T = true
        · obtain ⟨v, hvw, _, hvT⟩ := hv
          refine ⟨F.erase T, X, P ∪ (S v \ y), D + 1, i1e, ?_, i3', ?_, ?_, ?_, ?_, i7e⟩
          · intro x hx hxP hxS
            obtain ⟨t, ht, hf⟩ :=
              i2 x hx (fun p hp => hxP p (Finset.mem_union_left _ hp)) hxS
            refine ⟨t, Finset.mem_erase.mpr ⟨?_, ht⟩, hf⟩
            intro e
            rw [e] at hf
            have h8 := mono gs n hgop x (ind (y ∪ S v)) (fun p hp => by
              have hp' := (ind_true _ _).mp hp
              by_cases hpy : p ∈ y
              · exact hx.1 p hpy
              · rcases Finset.mem_union.mp hp' with h | h
                · exact absurd h hpy
                · exact hxP p (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h, hpy⟩))) T hvT
            rw [hf] at h8
            exact absurd h8 (by simp)
          · omega
          · have hun : (P ∪ (S v \ y)).card ≤ P.card + ((S v \ y) \ P).card := by
              rw [← Finset.union_sdiff_self_eq_union]
              exact Finset.card_union_le _ _
            have hfull : ((S v \ y) \ P).card ≤ q + 1 :=
              (Finset.card_le_card (Finset.sdiff_subset.trans Finset.sdiff_subset)).trans
                (hcS v).le
            rcases i5' with h | ⟨v', _, hsub⟩
            · omega
            · by_cases hvv : v' = v
              · rw [hvv] at hsub
                have h0 : ((S v \ y) \ P).card = 0 := by
                  rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub]
                  simp
                omega
              · have h9 : ((S v \ y) \ P).card ≤ (S v \ S v').card := by
                  apply Finset.card_le_card
                  intro a ha
                  obtain ⟨ha1, ha2⟩ := Finset.mem_sdiff.mp ha
                  obtain ⟨ha3, ha4⟩ := Finset.mem_sdiff.mp ha1
                  refine Finset.mem_sdiff.mpr ⟨ha3, fun ha5 => ?_⟩
                  exact ha2 (hsub (Finset.mem_sdiff.mpr ⟨ha5, ha4⟩))
                have h10 := Finset.card_sdiff_add_card_inter (S v) (S v')
                have h11 := hS v v' (fun e => hvv e.symm)
                have h12 := hcS v
                omega
          · right
            exact ⟨v, hvw, Finset.subset_union_right⟩
          · have h13 : (P ∪ (S v \ y)) ∩ (S w \ y) ⊆ (P ∩ (S w \ y)) ∪ (S v ∩ S w) := by
              intro a ha
              obtain ⟨ha1, ha2⟩ := Finset.mem_inter.mp ha
              rcases Finset.mem_union.mp ha1 with h | h
              · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨h, ha2⟩)
              · exact Finset.mem_union_right _ (Finset.mem_inter.mpr
                  ⟨(Finset.mem_sdiff.mp h).1, (Finset.mem_sdiff.mp ha2).1⟩)
            have h13' := Finset.card_le_card h13
            have h14 := Finset.card_union_le (P ∩ (S w \ y)) (S v ∩ S w)
            have h15 := hS v w hvw
            omega
        · have hTn : T < n := by
            by_contra hh
            apply hsp
            refine ⟨⟨hT1, ?_⟩, by omega⟩
            intro v hvw hv2
            by_contra hne
            exact hv ⟨v, hvw, hv2, by simpa using hne⟩
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
          · have h13 : (insert (⟨T, hTn⟩ : Fin n) P) ∩ (S w \ y) ⊆
                insert (⟨T, hTn⟩ : Fin n) (P ∩ (S w \ y)) := by
              intro a ha
              obtain ⟨ha1, ha2⟩ := Finset.mem_inter.mp ha
              rcases Finset.mem_insert.mp ha1 with h | h
              · rw [h]
                exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨h, ha2⟩)
            have h13' := Finset.card_le_card h13
            have := Finset.card_insert_le (⟨T, hTn⟩ : Fin n) (P ∩ (S w \ y))
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
    (q K : ℕ) (hq : 2 ≤ q) (S : Fin m → Finset (Fin n)) (y : Finset (Fin n))
    (hcS : ∀ i : Fin m, (S i).card = q + 1)
    (hS : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) (w : Fin m) (r : ℕ)
    (hcorr : ∀ x : Fin n → Bool, Al K y x →
      val gs n x r = decide (∀ v ∈ S w, x v = true))
    (c : ℕ) (_ : c ≤ q) (hK : c * q < K ∨ n ≤ y.card + K) :
    ∃ X : Finset ℕ, (∀ t ∈ X, Spec gs S y w t ∧ n ≤ t ∧ t < n + gs.length) ∧
      min (c + 1) (S w \ y).card ≤ X.card + 1 := by
  classical
  by_cases hc0 : c = 0
  · refine ⟨∅, by simp, ?_⟩
    have := Nat.min_le_left (c + 1) (S w \ y).card
    simp only [Finset.card_empty]
    omega
  have hqc : q ≤ c * q := Nat.le_mul_of_pos_left q (by omega)
  have hall : ∀ Z : Finset (Fin n), y ⊆ Z → ((Z \ y).card ≤ K ∨ n ≤ y.card + K) →
      Al K y (ind Z) := by
    intro Z hyZ hZ
    refine ⟨fun v hv => (ind_true _ _).mpr (hyZ hv), ?_⟩
    rw [ind_filter]
    rcases hZ with h | h
    · exact h
    · have h1 := Finset.card_sdiff_add_card_eq_card hyZ
      have h2 : Z.card ≤ n := by
        have := Finset.card_le_univ Z
        simpa using this
      omega
  have hSw : ((y ∪ S w) \ y).card ≤ q + 1 := by
    rw [Finset.union_sdiff_left]
    exact (Finset.card_le_card Finset.sdiff_subset).trans (hcS w).le
  have hr1 : val gs n (ind (y ∪ S w)) r = true := by
    rw [hcorr _ (hall _ Finset.subset_union_left (by
      rcases hK with h | h
      · left
        omega
      · right
        exact h))]
    simp only [decide_eq_true_eq]
    intro v hv
    exact (ind_true _ _).mpr (Finset.mem_union_right _ hv)
  have hr2 : ∀ x : Fin n → Bool, Al K y x → ¬ (∀ p ∈ S w, x p = true) →
      val gs n x r = false := by
    intro x hx hxS
    rw [hcorr x hx]
    simpa using hxS
  obtain ⟨F, X, P, D, _, i2, i3, i4, i5, _, i6, i7⟩ :=
    descent gs hg q K (by omega) S y hcS hS w r hr1 hr2 (n + gs.length) 0 (by omega)
  refine ⟨X, fun t ht => ⟨(i3 t ht).1, (i3 t ht).2.1, (i3 t ht).2.2.1⟩, ?_⟩
  have hF : F = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro t ht
    have := i7 t ht
    omega
  rw [hF] at i4
  simp only [Finset.card_empty, zero_add] at i4
  have hmin1 := Nat.min_le_left (c + 1) (S w \ y).card
  have hmin2 := Nat.min_le_right (c + 1) (S w \ y).card
  by_cases hsub : S w \ y ⊆ P
  · rw [Finset.inter_eq_right.mpr hsub] at i6
    omega
  · have hnot : ¬ Al K y (ind (y ∪ P)) := by
      intro hal
      obtain ⟨t, ht, _⟩ := i2 (ind (y ∪ P)) hal
        (fun p hp => (ind_true _ _).mpr (Finset.mem_union_right _ hp))
        (fun h => hsub (fun p hp => by
          obtain ⟨hp1, hp2⟩ := Finset.mem_sdiff.mp hp
          rcases Finset.mem_union.mp ((ind_true _ _).mp (h p hp1)) with h' | h'
          · exact absurd h' hp2
          · exact h'))
      rw [hF] at ht
      simp at ht
    have hPy : ((y ∪ P) \ y).card ≤ P.card := by
      rw [Finset.union_sdiff_left]
      exact Finset.card_le_card Finset.sdiff_subset
    rcases hK with h | h
    · have hK2 : K < ((y ∪ P) \ y).card := by
        by_contra hle
        exact hnot (hall _ Finset.subset_union_left (Or.inl (by omega)))
      have h1 : c * q < D * q := by omega
      have h2 : c < D := Nat.lt_of_mul_lt_mul_right h1
      omega
    · exact absurd (hall _ Finset.subset_union_left (Or.inr h)) hnot

end PEqualNP.Outside.L_meta_1032

theorem PEqualNP.Outside.L_meta_1032 : ∀ (q n m K : ℕ) (S : Fin m → Finset (Fin n)) (y : Finset (Fin n)), 2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (∀ v ∈ y, x v = true) → ((Finset.univ.filter (fun i : Fin n => x i = true)) \ y).card ≤ K → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∀ v ∈ S w, x v = true)) → ∀ c : ℕ, c ≤ q → (c * q < K ∨ n ≤ y.card + K) → ∑ i ∈ Finset.univ.filter (fun i : Fin m => 2 ≤ (S i \ y).card), min (c + 1) (S i \ y).card ≤ gates.length + (Finset.univ.filter (fun i : Fin m => 2 ≤ (S i \ y).card)).card := by
  intro q n m K S y hq hcS hS gates out hg hcorr c hc hcK
  classical
  have hcore : ∀ w : Fin m, ∃ X : Finset ℕ, 2 ≤ (S w \ y).card →
      (∀ t ∈ X, PEqualNP.Outside.L_meta_1032.Spec gates S y w t ∧ n ≤ t ∧ t < n + gates.length) ∧
        min (c + 1) (S w \ y).card ≤ X.card + 1 := by
    intro w
    obtain ⟨X, h1, h2⟩ := PEqualNP.Outside.L_meta_1032.core gates hg q K hq S y hcS hS w (out w)
      (fun x hx => hcorr w x hx.1 hx.2) c hc hcK
    exact ⟨X, fun _ => ⟨h1, h2⟩⟩
  choose X hX using hcore
  have hdisj : ∀ i ∈ Finset.univ.filter (fun i : Fin m => 2 ≤ (S i \ y).card),
      ∀ j ∈ Finset.univ.filter (fun i : Fin m => 2 ≤ (S i \ y).card),
      i ≠ j → Disjoint (X i) (X j) := by
    intro i hi j hj hij
    have hi2 := (Finset.mem_filter.mp hi).2
    have hj2 := (Finset.mem_filter.mp hj).2
    rw [Finset.disjoint_left]
    intro t hti htj
    have h1 := ((hX i hi2).1 t hti).1.1
    have h2 := ((hX j hj2).1 t htj).1.2 i hij hi2
    rw [h1] at h2
    exact absurd h2 (by simp)
  have hsum : ∑ i ∈ Finset.univ.filter (fun i : Fin m => 2 ≤ (S i \ y).card), (X i).card ≤
      gates.length := by
    rw [← Finset.card_biUnion hdisj]
    have hsub : (Finset.univ.filter (fun i : Fin m => 2 ≤ (S i \ y).card)).biUnion X ⊆
        Finset.Ico n (n + gates.length) := by
      intro t ht
      obtain ⟨i, hi, hti⟩ := Finset.mem_biUnion.mp ht
      have hi2 := (Finset.mem_filter.mp hi).2
      exact Finset.mem_Ico.mpr ((hX i hi2).1 t hti).2
    have := Finset.card_le_card hsub
    simpa using this
  calc ∑ i ∈ Finset.univ.filter (fun i : Fin m => 2 ≤ (S i \ y).card),
        min (c + 1) (S i \ y).card
      ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin m => 2 ≤ (S i \ y).card), ((X i).card + 1) :=
        Finset.sum_le_sum (fun i hi => (hX i (Finset.mem_filter.mp hi).2).2)
    _ = ∑ i ∈ Finset.univ.filter (fun i : Fin m => 2 ≤ (S i \ y).card), (X i).card +
          (Finset.univ.filter (fun i : Fin m => 2 ≤ (S i \ y).card)).card := by
        rw [Finset.sum_add_distrib]
        simp
    _ ≤ gates.length + (Finset.univ.filter (fun i : Fin m => 2 ≤ (S i \ y).card)).card := by
        omega
