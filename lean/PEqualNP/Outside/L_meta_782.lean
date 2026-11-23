import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_782

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

def val (C : Circuit) (n : ℕ) (x : Fin n → Bool) (t : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD t false

def ins (C : Circuit) (n : ℕ) (t : ℕ) : Finset ℕ :=
  match C.gates[t - n]? with
  | some g => g.inputs.toFinset.filter (fun i => i < t)
  | none => ∅

lemma val_in (C : Circuit) (n : ℕ) (t : ℕ) (h : t < n) (x : Fin n → Bool) :
    val C n x t = x ⟨t, h⟩ := by
  unfold val
  rw [wires_eq, fold_prefix _ _ t (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

lemma val_out (C : Circuit) (n : ℕ) (t : ℕ) (h : n + C.size ≤ t) (x : Fin n → Bool) :
    val C n x t = false := by
  unfold val
  apply List.getD_eq_default
  rw [wires_eq, fold_length, List.length_ofFn]
  exact h

lemma ins_lt (C : Circuit) (n : ℕ) (t : ℕ) : ∀ i ∈ ins C n t, i < t := by
  intro i hi
  unfold ins at hi
  split at hi
  · exact (Finset.mem_filter.mp hi).2
  · simp at hi

lemma ins_card (C : Circuit) (n : ℕ) (t : ℕ)
    (hg : ∀ g ∈ C.gates, g.inputs.length = 2) : (ins C n t).card ≤ 2 := by
  unfold ins
  split
  · next g hgt =>
    have h1 := hg g (List.mem_of_getElem? hgt)
    calc (g.inputs.toFinset.filter (fun i => i < t)).card
        ≤ g.inputs.toFinset.card := Finset.card_filter_le _ _
      _ ≤ g.inputs.length := List.toFinset_card_le _
      _ = 2 := h1
  · simp

lemma val_dep (C : Circuit) (n : ℕ)
    (hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (t : ℕ) (h1 : n ≤ t) (h2 : t < n + C.size) (x y : Fin n → Bool)
    (H : ∀ i ∈ ins C n t, val C n y i = true → val C n x i = true)
    (hy : val C n y t = true) : val C n x t = true := by
  obtain ⟨j, rfl⟩ : ∃ j, t = n + j := ⟨t - n, by omega⟩
  have hj : j < C.gates.length := by
    unfold Circuit.size at h2
    omega
  have hgt : C.gates[n + j - n]? = some C.gates[j] := by
    rw [show n + j - n = j by omega]
    exact List.getElem?_eq_getElem hj
  have key : ∀ z : Fin n → Bool, val C n z (n + j) =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
        if i < n + j then val C n z i else false) := by
    intro z
    have h := fold_gate C.gates (List.ofFn z) j hj
    rw [List.length_ofFn] at h
    exact h
  have hmem : ∀ i ∈ (C.gates[j]).inputs, i < n + j → i ∈ ins C n (n + j) := by
    intro i hi hlt
    unfold ins
    rw [hgt]
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hi, hlt⟩
  have hstep : ∀ i ∈ (C.gates[j]).inputs,
      (if i < n + j then val C n y i else false) = true →
      (if i < n + j then val C n x i else false) = true := by
    intro i hi
    by_cases hlt : i < n + j
    · simp only [hlt, ite_true]
      exact H i (hmem i hi hlt)
    · simp only [hlt, ite_false]
      intro hf
      exact absurd hf (by simp)
  rw [key] at hy ⊢
  rcases hg _ (List.getElem_mem hj) with hop | hop
  · rw [hop] at hy ⊢
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at hy ⊢
    rintro b ⟨i, hi, rfl⟩
    exact hstep i hi (hy _ ⟨i, hi, rfl⟩)
  · rw [hop] at hy ⊢
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hy ⊢
    obtain ⟨b, ⟨i, hi, rfl⟩, hb⟩ := hy
    exact ⟨_, ⟨i, hi, rfl⟩, hstep i hi hb⟩

def A {n : ℕ} (v : (Fin n → Bool) → ℕ → Bool) (t : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun a : Fin n => v (fun b : Fin n => decide (b = a)) t = true)

def Priv {n : ℕ} (v : (Fin n → Bool) → ℕ → Bool) (S : Finset (Fin n)) (t : ℕ) : Prop :=
  A v t ⊆ S ∧ 2 ≤ (A v t).card

lemma mem_A {n : ℕ} (v : (Fin n → Bool) → ℕ → Bool) (t : ℕ) (a : Fin n) :
    a ∈ A v t ↔ v (fun b : Fin n => decide (b = a)) t = true := by
  simp [A]

lemma mono {n : ℕ} (v : (Fin n → Bool) → ℕ → Bool) (N : ℕ) (ins : ℕ → Finset ℕ)
    (hin : ∀ t (h : t < n) (x : Fin n → Bool), v x t = x ⟨t, h⟩)
    (hout : ∀ t, N ≤ t → ∀ x : Fin n → Bool, v x t = false)
    (hlt : ∀ t, ∀ i ∈ ins t, i < t)
    (hdep : ∀ t, n ≤ t → t < N → ∀ x y : Fin n → Bool,
      (∀ i ∈ ins t, v y i = true → v x i = true) → v y t = true → v x t = true)
    (x y : Fin n → Bool) (hxy : ∀ q, y q = true → x q = true) :
    ∀ t, v y t = true → v x t = true := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro h
    by_cases h1 : t < n
    · rw [hin t h1] at h ⊢
      exact hxy _ h
    · by_cases h2 : t < N
      · exact hdep t (by omega) h2 x y (fun i hi => ih i (hlt t i hi)) h
      · rw [hout t (by omega)] at h
        exact absurd h (by simp)

lemma priv_range {n : ℕ} (v : (Fin n → Bool) → ℕ → Bool) (N : ℕ)
    (hin : ∀ t (h : t < n) (x : Fin n → Bool), v x t = x ⟨t, h⟩)
    (hout : ∀ t, N ≤ t → ∀ x : Fin n → Bool, v x t = false)
    {S : Finset (Fin n)} {t : ℕ} (hp : Priv v S t) : n ≤ t ∧ t < N := by
  obtain ⟨_, h2⟩ := hp
  constructor
  · by_contra h
    have h1 : t < n := by omega
    have h3 : (A v t).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [mem_A, hin t h1] at ha hb
      simp only [decide_eq_true_eq] at ha hb
      rw [← ha, ← hb]
    omega
  · by_contra h
    have h3 : A v t = ∅ := by
      ext a
      simp [A, hout t (by omega)]
    rw [h3] at h2
    simp at h2

lemma descent {n : ℕ} (v : (Fin n → Bool) → ℕ → Bool) (N : ℕ) (ins : ℕ → Finset ℕ)
    (hin : ∀ t (h : t < n) (x : Fin n → Bool), v x t = x ⟨t, h⟩)
    (hout : ∀ t, N ≤ t → ∀ x : Fin n → Bool, v x t = false)
    (hlt : ∀ t, ∀ i ∈ ins t, i < t)
    (hcard : ∀ t, (ins t).card ≤ 2)
    (hdep : ∀ t, n ≤ t → t < N → ∀ x y : Fin n → Bool,
      (∀ i ∈ ins t, v y i = true → v x i = true) → v y t = true → v x t = true)
    (S : Finset (Fin n)) (r : ℕ) :
    ∀ d T, T + d = N → ∃ F X : Finset ℕ,
      (∀ x y : Fin n → Bool, (∀ w ∈ F, v y w = true → v x w = true) →
        v y r = true → v x r = true) ∧
      (∀ t ∈ X, Priv v S t ∧ T ≤ t) ∧ F.card ≤ X.card + 1 ∧
      (∀ t ∈ F, Priv v S t → t < T) := by
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
    by_cases h : T ∈ F ∧ Priv v S T
    · obtain ⟨hTF, hTP⟩ := h
      obtain ⟨hn, hN⟩ := priv_range v N hin hout hTP
      refine ⟨F.erase T ∪ ins T, insert T X, ?_, ?_, ?_, ?_⟩
      · intro x y h hy
        apply hF x y _ hy
        intro w hw
        by_cases hwT : w = T
        · rw [hwT]
          exact hdep T hn hN x y (fun i hi => h i (Finset.mem_union_right _ hi))
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

lemma pick {n : ℕ} (v : (Fin n → Bool) → ℕ → Bool) (S : Finset (Fin n)) (L : Finset ℕ)
    (hL : ∀ t ∈ L, ∃ a, a ∈ A v t ∧ a ∉ S) :
    ∃ Y : Finset (Fin n), Y.card ≤ L.card ∧ (∀ a ∈ Y, a ∉ S) ∧
      ∀ t ∈ L, ∃ a ∈ Y, a ∈ A v t := by
  classical
  induction L using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp, by simp⟩
  | insert t L ht ih =>
    obtain ⟨Y, h1, h2, h3⟩ := ih (fun u hu => hL u (Finset.mem_insert_of_mem hu))
    obtain ⟨a, ha, haS⟩ := hL t (Finset.mem_insert_self t L)
    refine ⟨insert a Y, ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem ht]
      have := Finset.card_insert_le a Y
      omega
    · intro b hb
      rcases Finset.mem_insert.mp hb with hb | hb
      · rw [hb]
        exact haS
      · exact h2 b hb
    · intro u hu
      rcases Finset.mem_insert.mp hu with hu | hu
      · rw [hu]
        exact ⟨a, Finset.mem_insert_self _ _, ha⟩
      · obtain ⟨b, hb, hb'⟩ := h3 u hu
        exact ⟨b, Finset.mem_insert_of_mem hb, hb'⟩

lemma core {n : ℕ} (v : (Fin n → Bool) → ℕ → Bool) (N : ℕ) (ins : ℕ → Finset ℕ)
    (hin : ∀ t (h : t < n) (x : Fin n → Bool), v x t = x ⟨t, h⟩)
    (hout : ∀ t, N ≤ t → ∀ x : Fin n → Bool, v x t = false)
    (hlt : ∀ t, ∀ i ∈ ins t, i < t)
    (hcard : ∀ t, (ins t).card ≤ 2)
    (hdep : ∀ t, n ≤ t → t < N → ∀ x y : Fin n → Bool,
      (∀ i ∈ ins t, v y i = true → v x i = true) → v y t = true → v x t = true)
    (S : Finset (Fin n)) (r k c : ℕ)
    (hprom : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
      (∀ q ∈ S, x q = false) → v x r = false)
    (hck : c ≤ k) (hc : c + 1 ≤ (A v r).card) :
    ∃ X : Finset ℕ, (∀ t ∈ X, Priv v S t ∧ n ≤ t ∧ t < N) ∧ c ≤ X.card := by
  classical
  obtain ⟨F, X, hF, hX, hFX, hP⟩ :=
    descent v N ins hin hout hlt hcard hdep S r N 0 (by omega)
  refine ⟨X, fun t ht => ⟨(hX t ht).1, priv_range v N hin hout (hX t ht).1⟩, ?_⟩
  obtain ⟨Y, hY1, hY2, hY3⟩ := pick v S (F.filter (fun t => ¬ A v t ⊆ S)) (by
    intro t ht
    have h1 := (Finset.mem_filter.mp ht).2
    rw [Finset.not_subset] at h1
    obtain ⟨a, ha, haS⟩ := h1
    exact ⟨a, ha, haS⟩)
  have hLF : (F.filter (fun t => ¬ A v t ⊆ S)).card ≤ F.card := Finset.card_filter_le _ _
  by_cases hk : k < (F.filter (fun t => ¬ A v t ⊆ S)).card
  · omega
  · have hx1 : (Finset.univ.filter (fun q : Fin n => (fun q : Fin n => decide (q ∈ Y)) q = true)).card
        ≤ k := by
      have h1 : Finset.univ.filter (fun q : Fin n => (fun q : Fin n => decide (q ∈ Y)) q = true)
          = Y := by
        ext q
        simp
      rw [h1]
      omega
    have hx2 : ∀ q ∈ S, (fun q : Fin n => decide (q ∈ Y)) q = false := by
      intro q hq
      simp only [decide_eq_false_iff_not]
      exact fun h => hY2 q h hq
    have hr := hprom (fun q : Fin n => decide (q ∈ Y)) hx1 hx2
    have hLvx : ∀ t ∈ F.filter (fun t => ¬ A v t ⊆ S),
        v (fun q : Fin n => decide (q ∈ Y)) t = true := by
      intro t ht
      obtain ⟨a, ha, hat⟩ := hY3 t ht
      refine mono v N ins hin hout hlt hdep (fun q : Fin n => decide (q ∈ Y))
        (fun b : Fin n => decide (b = a)) ?_ t ((mem_A v t a).mp hat)
      intro q hq
      simp only [decide_eq_true_eq] at hq ⊢
      rw [hq]
      exact ha
    have hle : (A v r).card ≤ F.card := by
      apply Finset.card_le_card_of_forall_subsingleton
        (fun a w => a ∈ A v w ∧ (A v w).card ≤ 1)
      · intro a ha
        by_contra hcon
        have h1 : v (fun q : Fin n => decide (q ∈ Y)) r = true := by
          apply hF (fun q : Fin n => decide (q ∈ Y)) (fun b : Fin n => decide (b = a)) _
            ((mem_A v r a).mp ha)
          intro w hw hwa
          by_contra hxw
          have haw : a ∈ A v w := (mem_A v w a).mpr hwa
          have hnl : w ∉ F.filter (fun t => ¬ A v t ⊆ S) := fun h => hxw (hLvx w h)
          have hsub : A v w ⊆ S := by
            by_contra hs
            exact hnl (Finset.mem_filter.mpr ⟨hw, hs⟩)
          have hcd : (A v w).card ≤ 1 := by
            by_contra h2
            have := hP w hw ⟨hsub, by omega⟩
            omega
          exact hcon ⟨w, hw, haw, hcd⟩
        rw [hr] at h1
        exact absurd h1 (by simp)
      · intro w _ a ha b hb
        exact Finset.card_le_one.mp ha.2.2 a ha.2.1 b hb.2.1
    omega

end PEqualNP.Outside.L_meta_782

theorem PEqualNP.Outside.L_meta_782 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c hS _ hg _ hprom hck hc
  classical
  have hcore : ∀ i : Fin m, ∃ X : Finset ℕ,
      (∀ t ∈ X, PEqualNP.Outside.L_meta_782.Priv (PEqualNP.Outside.L_meta_782.val C n) (S i) t ∧
        n ≤ t ∧ t < n + C.size) ∧ c i ≤ X.card := by
    intro i
    exact PEqualNP.Outside.L_meta_782.core (PEqualNP.Outside.L_meta_782.val C n) (n + C.size)
      (PEqualNP.Outside.L_meta_782.ins C n)
      (PEqualNP.Outside.L_meta_782.val_in C n)
      (fun t h x => PEqualNP.Outside.L_meta_782.val_out C n t h x)
      (PEqualNP.Outside.L_meta_782.ins_lt C n)
      (fun t => PEqualNP.Outside.L_meta_782.ins_card C n t (fun g h => (hg g h).2))
      (PEqualNP.Outside.L_meta_782.val_dep C n (fun g h => (hg g h).1))
      (S i) (o i) k (c i) (hprom i) (hck i) (hc i)
  choose X hX1 hX2 using hcore
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ (Finset.univ : Finset (Fin m)),
      i ≠ j → Disjoint (X i) (X j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro t hti htj
    have h1 := (hX1 i t hti).1
    have h2 := (hX1 j t htj).1
    have h3 : PEqualNP.Outside.L_meta_782.A (PEqualNP.Outside.L_meta_782.val C n) t ⊆ S i ∩ S j :=
      Finset.subset_inter h1.1 h2.1
    have h4 := Finset.card_le_card h3
    have h5 := hS i j hij
    have h6 := h1.2
    omega
  calc ∑ i : Fin m, c i ≤ ∑ i : Fin m, (X i).card := Finset.sum_le_sum (fun i _ => hX2 i)
    _ = (Finset.univ.biUnion X).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.Ico n (n + C.size)).card := by
      apply Finset.card_le_card
      intro t ht
      obtain ⟨i, _, hti⟩ := Finset.mem_biUnion.mp ht
      exact Finset.mem_Ico.mpr (hX1 i t hti).2
    _ = C.size := by simp
