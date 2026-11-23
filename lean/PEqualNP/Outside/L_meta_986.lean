import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_986

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

lemma ins_card (gs : List Gate) (n : ℕ) (t : ℕ)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) : (ins gs n t).card ≤ 2 := by
  unfold ins
  split
  · next g hgt =>
    have h1 := hg g (List.mem_of_getElem? hgt)
    calc (g.inputs.toFinset.filter (fun i => i < t)).card
        ≤ g.inputs.toFinset.card := Finset.card_filter_le _ _
      _ ≤ g.inputs.length := List.toFinset_card_le _
      _ ≤ 2 := h1
  · simp

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

def AD {n : ℕ} (v : (Fin n → Bool) → ℕ → Bool) (Dom : Finset (Fin n)) (t : ℕ) :
    Finset (Fin n) :=
  Dom.filter (fun a : Fin n => v (fun b : Fin n => decide (b = a)) t = true)

def Priv {n : ℕ} (v : (Fin n → Bool) → ℕ → Bool) (Dom S : Finset (Fin n)) (z t : ℕ) : Prop :=
  AD v Dom t ⊆ S ∧ 2 ≤ (AD v Dom t).card ∧ t ≠ z

lemma mem_AD {n : ℕ} (v : (Fin n → Bool) → ℕ → Bool) (Dom : Finset (Fin n)) (t : ℕ)
    (a : Fin n) : a ∈ AD v Dom t ↔ a ∈ Dom ∧ v (fun b : Fin n => decide (b = a)) t = true := by
  simp [AD]

lemma AD_mono {n : ℕ} (v : (Fin n → Bool) → ℕ → Bool) (D1 D2 : Finset (Fin n)) (t : ℕ)
    (h : D1 ⊆ D2) : AD v D1 t ⊆ AD v D2 t := by
  intro a ha
  rw [mem_AD] at ha ⊢
  exact ⟨h ha.1, ha.2⟩

lemma mono {n : ℕ} (v : (Fin n → Bool) → ℕ → Bool) (N : ℕ) (ins : ℕ → Finset ℕ) (z : ℕ)
    (hin : ∀ t (h : t < n) (x : Fin n → Bool), v x t = x ⟨t, h⟩)
    (hout : ∀ t, N ≤ t → ∀ x : Fin n → Bool, v x t = false)
    (hlt : ∀ t, ∀ i ∈ ins t, i < t)
    (hdep : ∀ t, n ≤ t → t < N → t ≠ z → ∀ x y : Fin n → Bool,
      (∀ i ∈ ins t, v y i = true → v x i = true) → v y t = true → v x t = true)
    (x y : Fin n → Bool) (hxy : ∀ q, y q = true → x q = true)
    (hz : v y z = true → v x z = true) :
    ∀ t, v y t = true → v x t = true := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro h
    by_cases h0 : t = z
    · rw [h0] at h ⊢
      exact hz h
    · by_cases h1 : t < n
      · rw [hin t h1] at h ⊢
        exact hxy _ h
      · by_cases h2 : t < N
        · exact hdep t (by omega) h2 h0 x y (fun i hi => ih i (hlt t i hi)) h
        · rw [hout t (by omega)] at h
          exact absurd h (by simp)

lemma priv_range {n : ℕ} (v : (Fin n → Bool) → ℕ → Bool) (N : ℕ)
    (hin : ∀ t (h : t < n) (x : Fin n → Bool), v x t = x ⟨t, h⟩)
    (hout : ∀ t, N ≤ t → ∀ x : Fin n → Bool, v x t = false)
    {Dom S : Finset (Fin n)} {z t : ℕ} (hp : Priv v Dom S z t) : n ≤ t ∧ t < N := by
  obtain ⟨_, h2, _⟩ := hp
  constructor
  · by_contra h
    have h1 : t < n := by omega
    have h3 : (AD v Dom t).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [mem_AD, hin t h1] at ha hb
      have ha' := ha.2
      have hb' := hb.2
      simp only [decide_eq_true_eq] at ha' hb'
      rw [← ha', ← hb']
    omega
  · by_contra h
    have h3 : AD v Dom t = ∅ := by
      ext a
      simp [AD, hout t (by omega)]
    rw [h3] at h2
    simp at h2

lemma descent {n : ℕ} (v : (Fin n → Bool) → ℕ → Bool) (N : ℕ) (ins : ℕ → Finset ℕ) (z : ℕ)
    (hin : ∀ t (h : t < n) (x : Fin n → Bool), v x t = x ⟨t, h⟩)
    (hout : ∀ t, N ≤ t → ∀ x : Fin n → Bool, v x t = false)
    (hlt : ∀ t, ∀ i ∈ ins t, i < t)
    (hcard : ∀ t, (ins t).card ≤ 2)
    (hdep : ∀ t, n ≤ t → t < N → t ≠ z → ∀ x y : Fin n → Bool,
      (∀ i ∈ ins t, v y i = true → v x i = true) → v y t = true → v x t = true)
    (Dom S : Finset (Fin n)) (r : ℕ) :
    ∀ d T, T + d = N → ∃ F X : Finset ℕ,
      (∀ x y : Fin n → Bool, (∀ w ∈ F, v y w = true → v x w = true) →
        v y r = true → v x r = true) ∧
      (∀ t ∈ X, Priv v Dom S z t ∧ T ≤ t) ∧ F.card ≤ X.card + 1 ∧
      (∀ t ∈ F, Priv v Dom S z t → t < T) := by
  intro d
  induction d with
  | zero =>
    intro T hT
    refine ⟨{r}, ∅, ?_, ?_, ?_, ?_⟩
    · intro x y h hy
      exact h r (by simp) hy
    · simp
    · simp
    · intro t _ hp
      have := (priv_range v N hin hout hp).2
      omega
  | succ d ih =>
    intro T hT
    obtain ⟨F, X, hF, hX, hc, hP⟩ := ih (T + 1) (by omega)
    by_cases h : T ∈ F ∧ Priv v Dom S z T
    · obtain ⟨hTF, hTP⟩ := h
      obtain ⟨hn, hN⟩ := priv_range v N hin hout hTP
      refine ⟨F.erase T ∪ ins T, insert T X, ?_, ?_, ?_, ?_⟩
      · intro x y h hy
        apply hF x y _ hy
        intro w hw
        by_cases hwT : w = T
        · rw [hwT]
          exact hdep T hn hN hTP.2.2 x y (fun i hi => h i (Finset.mem_union_right _ hi))
        · exact h w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwT, hw⟩))
      · intro t ht
        rcases Finset.mem_insert.mp ht with ht | ht
        · rw [ht]
          exact ⟨hTP, le_refl _⟩
        · have := (hX t ht).2
          exact ⟨(hX t ht).1, by omega⟩
      · have hTX : T ∉ X := by
          intro hh
          have := (hX T hh).2
          omega
        rw [Finset.card_insert_of_notMem hTX]
        have h1 : (F.erase T ∪ ins T).card ≤ (F.erase T).card + (ins T).card :=
          Finset.card_union_le _ _
        have h2 : (F.erase T).card = F.card - 1 := Finset.card_erase_of_mem hTF
        have h3 := hcard T
        have h4 : 0 < F.card := Finset.card_pos.mpr ⟨T, hTF⟩
        omega
      · intro t ht hp
        rcases Finset.mem_union.mp ht with ht | ht
        · have h5 := hP t (Finset.mem_of_mem_erase ht) hp
          have h6 := Finset.ne_of_mem_erase ht
          omega
        · exact hlt T t ht
    · refine ⟨F, X, hF, ?_, hc, ?_⟩
      · intro t ht
        have := (hX t ht).2
        exact ⟨(hX t ht).1, by omega⟩
      · intro t ht hp
        have h5 := hP t ht hp
        have h6 : t ≠ T := by
          intro e
          rw [e] at ht hp
          exact h ⟨ht, hp⟩
        omega

lemma pick {n : ℕ} (v : (Fin n → Bool) → ℕ → Bool) (Dom S : Finset (Fin n)) (L : Finset ℕ)
    (hL : ∀ t ∈ L, ∃ a, a ∈ AD v Dom t ∧ a ∉ S) :
    ∃ Y : Finset (Fin n), (∀ a ∈ Y, a ∈ Dom ∧ a ∉ S) ∧
      ∀ t ∈ L, ∃ a ∈ Y, a ∈ AD v Dom t := by
  classical
  induction L using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | insert t L ht ih =>
    obtain ⟨Y, h2, h3⟩ := ih (fun u hu => hL u (Finset.mem_insert_of_mem hu))
    obtain ⟨a, ha, haS⟩ := hL t (Finset.mem_insert_self t L)
    refine ⟨insert a Y, ?_, ?_⟩
    · intro b hb
      rcases Finset.mem_insert.mp hb with hb | hb
      · rw [hb]
        exact ⟨((mem_AD v Dom t a).mp ha).1, haS⟩
      · exact h2 b hb
    · intro u hu
      rcases Finset.mem_insert.mp hu with hu | hu
      · rw [hu]
        exact ⟨a, Finset.mem_insert_self _ _, ha⟩
      · obtain ⟨b, hb, hb'⟩ := h3 u hu
        exact ⟨b, Finset.mem_insert_of_mem hb, hb'⟩

lemma core {n : ℕ} (v : (Fin n → Bool) → ℕ → Bool) (N : ℕ) (ins : ℕ → Finset ℕ) (z : ℕ)
    (hin : ∀ t (h : t < n) (x : Fin n → Bool), v x t = x ⟨t, h⟩)
    (hout : ∀ t, N ≤ t → ∀ x : Fin n → Bool, v x t = false)
    (hlt : ∀ t, ∀ i ∈ ins t, i < t)
    (hcard : ∀ t, (ins t).card ≤ 2)
    (hdep : ∀ t, n ≤ t → t < N → t ≠ z → ∀ x y : Fin n → Bool,
      (∀ i ∈ ins t, v y i = true → v x i = true) → v y t = true → v x t = true)
    (Dom S : Finset (Fin n)) (r : ℕ)
    (hY : ∀ Y : Finset (Fin n), (∀ a ∈ Y, a ∈ Dom ∧ a ∉ S) →
      v (fun q : Fin n => decide (q ∈ Y)) z = true ∧
        v (fun q : Fin n => decide (q ∈ Y)) r = false)
    (R : Finset (Fin n))
    (hR : ∀ a ∈ R, a ∈ Dom ∧ v (fun b : Fin n => decide (b = a)) r = true) :
    ∃ X : Finset ℕ, (∀ t ∈ X, Priv v Dom S z t ∧ n ≤ t ∧ t < N) ∧ R.card ≤ X.card + 1 := by
  classical
  obtain ⟨F, X, hF, hX, hFX, hP⟩ :=
    descent v N ins z hin hout hlt hcard hdep Dom S r N 0 (by omega)
  refine ⟨X, fun t ht => ⟨(hX t ht).1, priv_range v N hin hout (hX t ht).1⟩, ?_⟩
  obtain ⟨Y, hY1, hY3⟩ := pick v Dom S (F.filter (fun t => ¬ AD v Dom t ⊆ S)) (by
    intro t ht
    have h1 := (Finset.mem_filter.mp ht).2
    rw [Finset.not_subset] at h1
    obtain ⟨a, ha, haS⟩ := h1
    exact ⟨a, ha, haS⟩)
  obtain ⟨hz, hr⟩ := hY Y hY1
  have hLvx : ∀ t ∈ F.filter (fun t => ¬ AD v Dom t ⊆ S),
      v (fun q : Fin n => decide (q ∈ Y)) t = true := by
    intro t ht
    obtain ⟨a, ha, hat⟩ := hY3 t ht
    refine mono v N ins z hin hout hlt hdep (fun q : Fin n => decide (q ∈ Y))
      (fun b : Fin n => decide (b = a)) ?_ (fun _ => hz) t ((mem_AD v Dom t a).mp hat).2
    intro q hq
    simp only [decide_eq_true_eq] at hq ⊢
    rw [hq]
    exact ha
  have hle : R.card ≤ F.card := by
    apply Finset.card_le_card_of_forall_subsingleton
      (fun a w => a ∈ AD v Dom w ∧ (AD v Dom w).card ≤ 1)
    · intro a ha
      by_contra hcon
      have h1 : v (fun q : Fin n => decide (q ∈ Y)) r = true := by
        apply hF (fun q : Fin n => decide (q ∈ Y)) (fun b : Fin n => decide (b = a)) _ (hR a ha).2
        intro w hw hwa
        by_contra hxw
        have hwz : w ≠ z := by
          intro e
          rw [e] at hxw
          exact hxw hz
        have haw : a ∈ AD v Dom w := (mem_AD v Dom w a).mpr ⟨(hR a ha).1, hwa⟩
        have hnl : w ∉ F.filter (fun t => ¬ AD v Dom t ⊆ S) := fun h => hxw (hLvx w h)
        have hsub : AD v Dom w ⊆ S := by
          by_contra hs
          exact hnl (Finset.mem_filter.mpr ⟨hw, hs⟩)
        have hcd : (AD v Dom w).card ≤ 1 := by
          by_contra h2
          have := hP w hw ⟨hsub, by omega, hwz⟩
          omega
        exact hcon ⟨w, hw, haw, hcd⟩
      rw [hr] at h1
      exact absurd h1 (by simp)
    · intro w _ a ha b hb
      exact Finset.card_le_one.mp ha.2.2 a ha.2.1 b hb.2.1
  omega

end PEqualNP.Outside.L_meta_986

theorem PEqualNP.Outside.L_meta_986 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (i0 : Fin gates.length) (hw : ℕ) (T : Finset (Fin n)) (t0 : Fin n), (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → q = i0) → (gates.get i0).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get i0).inputs.head? = some hw → hw < n + i0.val → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → (∀ y : Fin n → Bool, (∀ t ∈ T, y t = false) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, hw⟩ (List.ofFn y) = false) → t0 ∈ T → (∀ t ∈ T, (Finset.univ.filter (fun a : Fin m => t ∈ S a)).card ≤ (Finset.univ.filter (fun b : Fin m => t0 ∈ S b)).card) → 1 + ∑ s : Fin m, ((S s).card - 1) ≤ gates.length + ∑ u ∈ T.erase t0, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
  intro n m S gates out i0 hw T t0 _ hS hg hnot hi0 hhead hhw hcorr hT ht0 _
  classical
  have hi0lt : i0.val < gates.length := i0.isLt
  have hgi0 : gates[i0.val] = gates.get i0 := rfl
  have hin := PEqualNP.Outside.L_meta_986.val_in gates n
  have hout : ∀ t, n + gates.length ≤ t → ∀ x : Fin n → Bool, PEqualNP.Outside.L_meta_986.val gates n x t = false :=
    fun t h x => PEqualNP.Outside.L_meta_986.val_out gates n t h x
  have hlt := PEqualNP.Outside.L_meta_986.ins_lt gates n
  have hcard : ∀ t, (PEqualNP.Outside.L_meta_986.ins gates n t).card ≤ 2 :=
    fun t => PEqualNP.Outside.L_meta_986.ins_card gates n t (fun g h => (hg g h).2)
  have hdep : ∀ t, n ≤ t → t < n + gates.length → t ≠ n + i0.val → ∀ x y : Fin n → Bool,
      (∀ i ∈ PEqualNP.Outside.L_meta_986.ins gates n t, PEqualNP.Outside.L_meta_986.val gates n y i = true → PEqualNP.Outside.L_meta_986.val gates n x i = true) →
      PEqualNP.Outside.L_meta_986.val gates n y t = true → PEqualNP.Outside.L_meta_986.val gates n x t = true := by
    intro t h1 h2 h3 x y H hy
    obtain ⟨j, rfl⟩ : ∃ j, t = n + j := ⟨t - n, by omega⟩
    have hj : j < gates.length := by omega
    have hop : (gates[j]).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        (gates[j]).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
      rcases (hg _ (List.getElem_mem hj)).1 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso
        have := hnot ⟨j, hj⟩ h
        apply h3
        rw [← this]
    exact PEqualNP.Outside.L_meta_986.val_dep gates n j hj hop x y H hy
  have hNtrue : ∀ y : Fin n → Bool, (∀ t ∈ T, y t = false) →
      PEqualNP.Outside.L_meta_986.val gates n y (n + i0.val) = true := by
    intro y hy
    have h1 : PEqualNP.Outside.L_meta_986.val gates n y hw = false := hT y hy
    rw [PEqualNP.Outside.L_meta_986.val_key gates n i0.val hi0lt, hgi0, hi0]
    obtain ⟨l, hl⟩ := List.head?_eq_some_iff.mp hhead
    rw [hl]
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval, hhw, h1]
  have hper : ∀ o : Fin m, ∃ X : Finset ℕ,
      (∀ t ∈ X, PEqualNP.Outside.L_meta_986.Priv (PEqualNP.Outside.L_meta_986.val gates n)
        (if t0 ∈ S o then Finset.univ \ T.erase t0 else Finset.univ \ T) (S o) (n + i0.val) t ∧
        n ≤ t ∧ t < n + gates.length) ∧ (S o \ T.erase t0).card ≤ X.card + 1 := by
    intro o
    apply PEqualNP.Outside.L_meta_986.core (PEqualNP.Outside.L_meta_986.val gates n) (n + gates.length) (PEqualNP.Outside.L_meta_986.ins gates n) (n + i0.val)
      hin hout hlt hcard hdep
    · intro Y hY
      have hYT : ∀ t ∈ T, (fun q : Fin n => decide (q ∈ Y)) t = false := by
        intro t ht
        simp only [decide_eq_false_iff_not]
        intro htY
        obtain ⟨hd, hs⟩ := hY t htY
        by_cases h0 : t0 ∈ S o
        · simp only [h0, ↓reduceIte, Finset.mem_sdiff, Finset.mem_univ, true_and,
            Finset.mem_erase, not_and] at hd
          have : t = t0 := by
            by_contra hne
            exact hd hne ht
          rw [this] at hs
          exact hs h0
        · simp only [h0, ↓reduceIte, Finset.mem_sdiff, Finset.mem_univ, true_and] at hd
          exact hd ht
      refine ⟨hNtrue _ hYT, ?_⟩
      have h2 := hcorr o (fun q : Fin n => decide (q ∈ Y))
      have h3 : PEqualNP.Outside.L_meta_986.val gates n (fun q : Fin n => decide (q ∈ Y)) (out o) =
          decide (∃ v ∈ S o, (fun q : Fin n => decide (q ∈ Y)) v = true) := h2
      rw [h3]
      simp only [decide_eq_true_eq, decide_eq_false_iff_not, not_exists, not_and]
      intro v hv hvY
      exact (hY v hvY).2 hv
    · intro a ha
      obtain ⟨haS, haU⟩ := Finset.mem_sdiff.mp ha
      constructor
      · by_cases h0 : t0 ∈ S o
        · simp only [h0, ↓reduceIte, Finset.mem_sdiff, Finset.mem_univ, true_and]
          exact haU
        · simp only [h0, ↓reduceIte, Finset.mem_sdiff, Finset.mem_univ, true_and]
          intro haT
          apply haU
          refine Finset.mem_erase.mpr ⟨?_, haT⟩
          intro e
          rw [e] at haS
          exact h0 haS
      · have h2 := hcorr o (fun b : Fin n => decide (b = a))
        have h3 : PEqualNP.Outside.L_meta_986.val gates n (fun b : Fin n => decide (b = a)) (out o) =
            decide (∃ v ∈ S o, (fun b : Fin n => decide (b = a)) v = true) := h2
        rw [h3]
        simp only [decide_eq_true_eq]
        exact ⟨a, haS, rfl⟩
  choose X hX1 hX2 using hper
  have hsubT : ∀ o : Fin m, Finset.univ \ T ⊆
      (if t0 ∈ S o then Finset.univ \ T.erase t0 else Finset.univ \ T) := by
    intro o
    by_cases h0 : t0 ∈ S o
    · simp only [h0, ↓reduceIte]
      intro a ha
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_erase, not_and] at ha ⊢
      exact fun _ h => ha h
    · simp only [h0, ↓reduceIte]
      exact Finset.Subset.refl _
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ (Finset.univ : Finset (Fin m)),
      i ≠ j → Disjoint (X i) (X j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro t hti htj
    obtain ⟨pi1, pi2, _⟩ := (hX1 i t hti).1
    obtain ⟨pj1, pj2, _⟩ := (hX1 j t htj).1
    have h5 := hS i j hij
    by_cases hi : t0 ∈ S i
    · by_cases hj : t0 ∈ S j
      · simp only [hi, hj, ↓reduceIte] at pi1 pi2 pj1 pj2
        have h4 := Finset.card_le_card (Finset.subset_inter pi1 pj1)
        omega
      · simp only [hj, ↓reduceIte] at pj1 pj2
        have h3 := PEqualNP.Outside.L_meta_986.AD_mono (PEqualNP.Outside.L_meta_986.val gates n) _ _ t (hsubT i)
        have h4 := Finset.card_le_card (Finset.subset_inter (h3.trans pi1) pj1)
        omega
    · simp only [hi, ↓reduceIte] at pi1 pi2
      have h3 := PEqualNP.Outside.L_meta_986.AD_mono (PEqualNP.Outside.L_meta_986.val gates n) _ _ t (hsubT j)
      have h4 := Finset.card_le_card (Finset.subset_inter pi1 (h3.trans pj1))
      omega
  have hXsum : ∑ s : Fin m, (X s).card + 1 ≤ gates.length := by
    rw [← Finset.card_biUnion hdisj]
    have hsub : Finset.univ.biUnion X ⊆ (Finset.Ico n (n + gates.length)).erase (n + i0.val) := by
      intro t ht
      obtain ⟨i, _, hti⟩ := Finset.mem_biUnion.mp ht
      obtain ⟨hp, h1, h2⟩ := hX1 i t hti
      exact Finset.mem_erase.mpr ⟨hp.2.2, Finset.mem_Ico.mpr ⟨h1, h2⟩⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)] at h1
    simp only [Nat.card_Ico] at h1
    omega
  have hper2 : ∀ s : Fin m, (S s).card - 1 ≤ (X s).card + (S s ∩ T.erase t0).card := by
    intro s
    have h1 := hX2 s
    have h2 := Finset.card_sdiff_add_card_inter (S s) (T.erase t0)
    omega
  have hsum1 : ∑ s : Fin m, ((S s).card - 1) ≤
      ∑ s : Fin m, (X s).card + ∑ s : Fin m, (S s ∩ T.erase t0).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun s _ => hper2 s)
  have hsum2 : ∑ s : Fin m, (S s ∩ T.erase t0).card =
      ∑ u ∈ T.erase t0, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
    have e1 : ∀ s : Fin m, (S s ∩ T.erase t0).card =
        ∑ u ∈ T.erase t0, (if u ∈ S s then 1 else 0) := by
      intro s
      rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]
    have e2 : ∀ u : Fin n, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card =
        ∑ s : Fin m, (if u ∈ S s then 1 else 0) := by
      intro u
      rw [Finset.card_filter]
    simp only [e1, e2]
    exact Finset.sum_comm
  omega
