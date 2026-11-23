import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_988

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
    (t : ℕ) (h1 : n ≤ t) (h2 : t < n + gs.length) :
    ∃ J : Finset ℕ, J.card ≤ 2 ∧ (∀ i ∈ J, i < t) ∧
      ((∀ x : Fin n → Bool, val gs n x t = true ↔ ∃ i ∈ J, val gs n x i = true) ∨
       (∀ x : Fin n → Bool, val gs n x t = true ↔ ∀ i ∈ J, val gs n x i = true)) := by
  classical
  obtain ⟨j, rfl⟩ : ∃ j, t = n + j := ⟨t - n, by omega⟩
  have hj : j < gs.length := by omega
  have hlen := (hg _ (List.getElem_mem hj)).2
  rcases (hg _ (List.getElem_mem hj)).1 with hop | hop
  · by_cases hall : ∀ i ∈ (gs[j]).inputs, i < n + j
    · refine ⟨(gs[j]).inputs.toFinset, (List.toFinset_card_le _).trans hlen,
        fun i hi => hall i (List.mem_toFinset.mp hi), Or.inr fun x => ?_⟩
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

def zp {n : ℕ} (y : Finset (Fin n)) (p : Fin n) : Fin n → Bool :=
  fun v => decide (v ∈ y ∨ v = p)

def Below {n : ℕ} (gs : List Gate) (S y : Finset (Fin n)) (t : ℕ) : Prop :=
  ∀ x : Fin n → Bool, (∀ v ∈ y, x v = true) → val gs n x t = true → ∃ p ∈ S, x p = true

def Good {n : ℕ} (gs : List Gate) (S y : Finset (Fin n)) (t : ℕ) : Prop :=
  Below gs S y t ∧ 2 ≤ (S.filter (fun p => val gs n (zp y p) t = true)).card

lemma good_range {n : ℕ} (gs : List Gate) (S y : Finset (Fin n)) (hd : Disjoint y S) (t : ℕ)
    (h : Good gs S y t) : n ≤ t ∧ t < n + gs.length := by
  obtain ⟨hb, h2⟩ := h
  constructor
  · by_contra hlt
    have h1 : t < n := by omega
    have hty : (⟨t, h1⟩ : Fin n) ∉ y := by
      intro hy
      obtain ⟨p, hp, hxp⟩ := hb (fun v => decide (v ∈ y)) (fun v hv => by simp [hv])
        (by rw [val_in gs n t h1]; simp [hy])
      simp only [decide_eq_true_eq] at hxp
      exact Finset.disjoint_left.mp hd hxp hp
    have h3 : (S.filter (fun p => val gs n (zp y p) t = true)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb'
      have ha' := (Finset.mem_filter.mp ha).2
      have hb'' := (Finset.mem_filter.mp hb').2
      rw [val_in gs n t h1] at ha' hb''
      simp only [zp, decide_eq_true_eq] at ha' hb''
      rcases ha' with e | e
      · exact absurd e hty
      · rcases hb'' with e' | e'
        · exact absurd e' hty
        · rw [← e, ← e']
    omega
  · by_contra hge
    have h3 : S.filter (fun p => val gs n (zp y p) t = true) = ∅ := by
      ext a
      simp [val_out gs n t (by omega)]
    rw [h3] at h2
    simp at h2

lemma descent {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S y : Finset (Fin n)) (hd : Disjoint y S) (r : ℕ)
    (hr1 : Below gs S y r) (hr2 : ∀ p ∈ S, val gs n (zp y p) r = true) :
    ∀ d T, T + d = n + gs.length → ∃ F X : Finset ℕ,
      (∀ w ∈ F, Below gs S y w) ∧
      (∀ p ∈ S, ∃ w ∈ F, val gs n (zp y p) w = true) ∧
      (∀ t ∈ X, Good gs S y t ∧ T ≤ t) ∧ F.card ≤ X.card + 1 ∧
      (∀ t ∈ F, Good gs S y t → t < T) := by
  classical
  have hgop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := fun g h => (hg g h).1
  intro d
  induction d with
  | zero =>
    intro T hT
    refine ⟨{r}, ∅, ?_, ?_, ?_, ?_, ?_⟩
    · intro w hw
      rw [Finset.mem_singleton.mp hw]
      exact hr1
    · intro p hp
      exact ⟨r, Finset.mem_singleton_self r, hr2 p hp⟩
    · simp
    · simp
    · intro t _ hgood
      have := (good_range gs S y hd t hgood).2
      omega
  | succ d ih =>
    intro T hT
    obtain ⟨F, X, hF1, hF2, hX, hc, hP⟩ := ih (T + 1) (by omega)
    have hX' : ∀ t ∈ X, Good gs S y t ∧ T ≤ t := by
      intro t ht
      have := (hX t ht).2
      exact ⟨(hX t ht).1, by omega⟩
    by_cases h : T ∈ F ∧ Good gs S y T
    · obtain ⟨hTF, hTG⟩ := h
      obtain ⟨hn, hN⟩ := good_range gs S y hd T hTG
      have hTX : T ∉ X := by
        intro hh
        have := (hX T hh).2
        omega
      have hFer : (F.erase T).card = F.card - 1 := Finset.card_erase_of_mem hTF
      have hFpos : 0 < F.card := Finset.card_pos.mpr ⟨T, hTF⟩
      have hlow : ∀ t ∈ F.erase T, Good gs S y t → t < T := by
        intro t ht hgood
        have h5 := hP t (Finset.mem_of_mem_erase ht) hgood
        have h6 := Finset.ne_of_mem_erase ht
        omega
      obtain ⟨J, hJc, hJlt, hJ⟩ := gate_cases gs n hg T hn hN
      rcases hJ with hor | hand
      · refine ⟨F.erase T ∪ J, insert T X, ?_, ?_, ?_, ?_, ?_⟩
        · intro w hw
          rcases Finset.mem_union.mp hw with hw | hw
          · exact hF1 w (Finset.mem_of_mem_erase hw)
          · intro x hx hv
            exact hTG.1 x hx ((hor x).mpr ⟨w, hw, hv⟩)
        · intro p hp
          obtain ⟨w, hw, hv⟩ := hF2 p hp
          by_cases hwT : w = T
          · rw [hwT] at hv
            obtain ⟨i, hi, hvi⟩ := (hor _).mp hv
            exact ⟨i, Finset.mem_union_right _ hi, hvi⟩
          · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwT, hw⟩), hv⟩
        · intro t ht
          rcases Finset.mem_insert.mp ht with ht | ht
          · rw [ht]
            exact ⟨hTG, le_refl _⟩
          · exact hX' t ht
        · rw [Finset.card_insert_of_notMem hTX]
          have h1 : (F.erase T ∪ J).card ≤ (F.erase T).card + J.card :=
            Finset.card_union_le _ _
          omega
        · intro t ht hgood
          rcases Finset.mem_union.mp ht with ht | ht
          · exact hlow t ht hgood
          · exact hJlt t ht
      · have hex : ∃ a ∈ J, Below gs S y a := by
          by_contra hcon
          have hnb : ∀ a ∈ J, ∃ x : Fin n → Bool, (∀ v ∈ y, x v = true) ∧
              val gs n x a = true ∧ ∀ p ∈ S, x p = false := by
            intro a ha
            by_contra hna
            apply hcon
            refine ⟨a, ha, fun x hx hv => ?_⟩
            by_contra hno
            apply hna
            refine ⟨x, hx, hv, fun p hp => ?_⟩
            by_contra hxp
            exact hno ⟨p, hp, by simpa using hxp⟩
          choose xs hxs using hnb
          have hbig : val gs n (fun q => decide (q ∈ y ∨ ∃ a, ∃ ha : a ∈ J, xs a ha q = true)) T
              = true := by
            rw [hand]
            intro a ha
            refine mono gs n hgop _ (xs a ha) (fun q hq => ?_) a (hxs a ha).2.1
            simp only [decide_eq_true_eq]
            exact Or.inr ⟨a, ha, hq⟩
          obtain ⟨p, hp, hxp⟩ := hTG.1 _ (fun v hv => by simp [hv]) hbig
          simp only [decide_eq_true_eq] at hxp
          rcases hxp with hpy | ⟨a, ha, hq⟩
          · exact Finset.disjoint_left.mp hd hpy hp
          · rw [(hxs a ha).2.2 p hp] at hq
            exact absurd hq (by simp)
        obtain ⟨a, haJ, haB⟩ := hex
        refine ⟨F.erase T ∪ {a}, insert T X, ?_, ?_, ?_, ?_, ?_⟩
        · intro w hw
          rcases Finset.mem_union.mp hw with hw | hw
          · exact hF1 w (Finset.mem_of_mem_erase hw)
          · rw [Finset.mem_singleton.mp hw]
            exact haB
        · intro p hp
          obtain ⟨w, hw, hv⟩ := hF2 p hp
          by_cases hwT : w = T
          · rw [hwT] at hv
            exact ⟨a, Finset.mem_union_right _ (Finset.mem_singleton_self a),
              (hand _).mp hv a haJ⟩
          · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwT, hw⟩), hv⟩
        · intro t ht
          rcases Finset.mem_insert.mp ht with ht | ht
          · rw [ht]
            exact ⟨hTG, le_refl _⟩
          · exact hX' t ht
        · rw [Finset.card_insert_of_notMem hTX]
          have h1 : (F.erase T ∪ {a}).card ≤ (F.erase T).card + ({a} : Finset ℕ).card :=
            Finset.card_union_le _ _
          rw [Finset.card_singleton] at h1
          omega
        · intro t ht hgood
          rcases Finset.mem_union.mp ht with ht | ht
          · exact hlow t ht hgood
          · rw [Finset.mem_singleton.mp ht]
            exact hJlt a haJ
    · refine ⟨F, X, hF1, hF2, hX', hc, ?_⟩
      intro t ht hgood
      have h5 := hP t ht hgood
      have h6 : t ≠ T := by
        intro e
        rw [e] at ht hgood
        exact h ⟨ht, hgood⟩
      omega

lemma core {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S y : Finset (Fin n)) (hd : Disjoint y S) (r : ℕ)
    (hr1 : Below gs S y r) (hr2 : ∀ p ∈ S, val gs n (zp y p) r = true) :
    ∃ X : Finset ℕ, (∀ t ∈ X, Good gs S y t) ∧ S.card ≤ X.card + 1 := by
  classical
  obtain ⟨F, X, hF1, hF2, hX, hc, hP⟩ :=
    descent gs hg S y hd r hr1 hr2 (n + gs.length) 0 (by omega)
  refine ⟨X, fun t ht => (hX t ht).1, ?_⟩
  have hle : S.card ≤ F.card := by
    apply Finset.card_le_card_of_forall_subsingleton
      (fun p w => val gs n (zp y p) w = true)
    · intro p hp
      obtain ⟨w, hw, hv⟩ := hF2 p hp
      exact ⟨w, hw, hv⟩
    · intro w hw a ha b hb
      have hcard : (S.filter (fun p => val gs n (zp y p) w = true)).card ≤ 1 := by
        by_contra h2
        have := hP w hw ⟨hF1 w hw, by omega⟩
        omega
      exact Finset.card_le_one.mp hcard a (Finset.mem_filter.mpr ⟨ha.1, ha.2⟩) b
        (Finset.mem_filter.mpr ⟨hb.1, hb.2⟩)
  omega

end PEqualNP.Outside.L_meta_988

theorem PEqualNP.Outside.L_meta_988 : ∀ (n m D : ℕ) (S y : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, Disjoint (y i) (S i)) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = true → ∃ p ∈ S i, x p = true) → (∀ i : Fin m, ∀ p ∈ S i, (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y i ∨ v = p)))).getD (o i) false = true) → (∀ J : Finset (Fin m), (∀ i ∈ J, ∀ j ∈ J, i ≠ j → ¬ Disjoint (y i) (S j)) → J.card ≤ D) → ∑ i : Fin m, (S i).card ≤ D * C.gates.length + m := by
  intro n m D S y C o hS hdis hg hbelow hfire hJ
  classical
  have hgop : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or := fun g h => (hg g h).1
  have hcore : ∀ i : Fin m, ∃ X : Finset ℕ,
      (∀ t ∈ X, PEqualNP.Outside.L_meta_988.Good C.gates (S i) (y i) t) ∧ (S i).card ≤ X.card + 1 := by
    intro i
    apply PEqualNP.Outside.L_meta_988.core C.gates hg (S i) (y i) (hdis i) (o i)
    · intro x _ hv
      exact hbelow i x hv
    · intro p hp
      exact hfire i p hp
  choose X hX1 hX2 using hcore
  have hrange : ∀ i : Fin m, X i ⊆ Finset.Ico n (n + C.gates.length) := by
    intro i t ht
    exact Finset.mem_Ico.mpr (PEqualNP.Outside.L_meta_988.good_range C.gates (S i) (y i) (hdis i) t (hX1 i t ht))
  have hshare : ∀ t : ℕ, (Finset.univ.filter (fun i : Fin m => t ∈ X i)).card ≤ D := by
    intro t
    apply hJ
    intro i hi j hj hij hdisj
    have hti := (Finset.mem_filter.mp hi).2
    have htj := (Finset.mem_filter.mp hj).2
    obtain ⟨_, hi2⟩ := hX1 i t hti
    obtain ⟨hjb, _⟩ := hX1 j t htj
    obtain ⟨p, hp, p', hp', hne⟩ := Finset.one_lt_card.mp (Nat.lt_of_lt_of_le Nat.one_lt_two hi2)
    have hpS := (Finset.mem_filter.mp hp).1
    have hp'S := (Finset.mem_filter.mp hp').1
    have hpv := (Finset.mem_filter.mp hp).2
    have hp'v := (Finset.mem_filter.mp hp').2
    have hone : ∃ a ∈ S i, a ∉ S j ∧ PEqualNP.Outside.L_meta_988.val C.gates n (PEqualNP.Outside.L_meta_988.zp (y i) a) t = true := by
      by_cases hpj : p ∈ S j
      · by_cases hp'j : p' ∈ S j
        · exfalso
          have h1 : ({p, p'} : Finset (Fin n)) ⊆ S i ∩ S j := by
            intro a ha
            rcases Finset.mem_insert.mp ha with e | e
            · rw [e]
              exact Finset.mem_inter.mpr ⟨hpS, hpj⟩
            · rw [Finset.mem_singleton.mp e]
              exact Finset.mem_inter.mpr ⟨hp'S, hp'j⟩
          have h2 := Finset.card_le_card h1
          rw [Finset.card_pair hne] at h2
          have := hS i j hij
          omega
        · exact ⟨p', hp'S, hp'j, hp'v⟩
      · exact ⟨p, hpS, hpj, hpv⟩
    obtain ⟨a, haS, haj, hav⟩ := hone
    have hbig : PEqualNP.Outside.L_meta_988.val C.gates n (fun v => decide (v ∈ y j ∨ v ∈ y i ∨ v = a)) t = true := by
      refine PEqualNP.Outside.L_meta_988.mono C.gates n hgop _ (PEqualNP.Outside.L_meta_988.zp (y i) a) (fun q hq => ?_) t hav
      simp only [PEqualNP.Outside.L_meta_988.zp, decide_eq_true_eq] at hq ⊢
      exact Or.inr hq
    obtain ⟨r, hr, hxr⟩ := hjb _ (fun v hv => by simp [hv]) hbig
    simp only [decide_eq_true_eq] at hxr
    rcases hxr with h | h | h
    · exact Finset.disjoint_left.mp (hdis j) h hr
    · exact Finset.disjoint_left.mp hdisj h hr
    · rw [h] at hr
      exact haj hr
  have hcount : ∑ i : Fin m, (X i).card ≤ D * C.gates.length := by
    have e1 : ∀ i : Fin m, (X i).card =
        ∑ t ∈ Finset.Ico n (n + C.gates.length), (if t ∈ X i then 1 else 0) := by
      intro i
      rw [← Finset.card_filter, Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.mpr (hrange i)]
    have e2 : ∀ t : ℕ, (Finset.univ.filter (fun i : Fin m => t ∈ X i)).card =
        ∑ i : Fin m, (if t ∈ X i then 1 else 0) := by
      intro t
      rw [Finset.card_filter]
    calc ∑ i : Fin m, (X i).card
        = ∑ i : Fin m, ∑ t ∈ Finset.Ico n (n + C.gates.length), (if t ∈ X i then 1 else 0) :=
          Finset.sum_congr rfl (fun i _ => e1 i)
      _ = ∑ t ∈ Finset.Ico n (n + C.gates.length), ∑ i : Fin m, (if t ∈ X i then 1 else 0) :=
          Finset.sum_comm
      _ ≤ ∑ _t ∈ Finset.Ico n (n + C.gates.length), D :=
          Finset.sum_le_sum (fun t _ => by rw [← e2 t]; exact hshare t)
      _ = D * C.gates.length := by
          simp [mul_comm]
  calc ∑ i : Fin m, (S i).card ≤ ∑ i : Fin m, ((X i).card + 1) :=
        Finset.sum_le_sum (fun i _ => hX2 i)
    _ = ∑ i : Fin m, (X i).card + m := by
        rw [Finset.sum_add_distrib]
        simp
    _ ≤ D * C.gates.length + m := by omega
