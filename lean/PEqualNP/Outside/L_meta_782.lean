import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_782

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [step, List.getD]

lemma fold_len (gs : List Gate) :
    ∀ w : List Bool, (gs.foldl step w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih =>
    intro w
    rw [List.foldl_cons, ih, step_len, List.length_cons]
    omega

lemma fold_lt (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (gs.foldl step w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih _ i (by rw [step_len]; omega)]
    exact step_lt w g i hi

lemma getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD, List.getElem?_eq_none h]

lemma fold_gate (gs : List Gate) : ∀ (w : List Bool) (j : ℕ) (hj : j < gs.length),
    (gs.foldl step w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i =>
        if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs with
  | nil => intro w j hj; simp at hj
  | cons g gs ih =>
    intro w j hj
    cases j with
    | zero =>
      simp only [List.foldl_cons, Nat.add_zero, List.getElem_cons_zero]
      rw [fold_lt gs _ _ (by rw [step_len]; omega), step_last]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with h
      · rw [fold_lt gs _ _ (by rw [step_len]; omega), step_lt w g i h]
      · exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simp at hj; omega
      have e : w.length + (j + 1) = (step w g).length + j := by rw [step_len]; omega
      simp only [List.foldl_cons, List.getElem_cons_succ]
      rw [e, ih (step w g) j hj']

def V (C : Circuit) {n : ℕ} (y : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn y)).getD w false

def cv (C : Circuit) {n : ℕ} (y : Fin n → Bool) (w i : ℕ) : Bool :=
  if i < w then V C y i else false

def gateAt (C : Circuit) (n w : ℕ) : Gate := C.gates.getD (w - n) ⟨GateOp.and, []⟩

lemma V_input (C : Circuit) {n : ℕ} (y : Fin n → Bool) (w : ℕ) (h : w < n) :
    V C y w = y ⟨w, h⟩ := by
  unfold V
  rw [wires_eq, fold_lt _ _ _ (by simpa using h)]
  simp [List.getD, h]

lemma V_ge (C : Circuit) {n : ℕ} (y : Fin n → Bool) (w : ℕ) (h : n + C.gates.length ≤ w) :
    V C y w = false := by
  unfold V
  rw [wires_eq]
  apply getD_ge
  rw [fold_len]
  simpa using h

lemma V_gate (C : Circuit) {n : ℕ} (y : Fin n → Bool) (w : ℕ) (h1 : n ≤ w)
    (h2 : w < n + C.gates.length) :
    V C y w = (gateAt C n w).op.eval ((gateAt C n w).inputs.map (cv C y w)) := by
  have hj : w - n < C.gates.length := by omega
  have := fold_gate C.gates (List.ofFn y) (w - n) hj
  simp only [List.length_ofFn] at this
  have e : n + (w - n) = w := by omega
  rw [e] at this
  unfold V cv gateAt
  rw [wires_eq, this, List.getD_eq_getElem _ _ hj]
  rfl

lemma gateAt_mem (C : Circuit) (n w : ℕ) (h1 : n ≤ w) (h2 : w < n + C.gates.length) :
    gateAt C n w ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_mem _

lemma shape (C : Circuit) (n : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (w : ℕ) (h1 : n ≤ w) (h2 : w < n + C.gates.length) :
    ∃ i1 i2 : ℕ, (gateAt C n w).inputs = [i1, i2] ∧
      ((∀ y : Fin n → Bool, V C y w = (cv C y w i1 && cv C y w i2)) ∨
        (∀ y : Fin n → Bool, V C y w = (cv C y w i1 || cv C y w i2))) := by
  obtain ⟨hop, hlen⟩ := hG _ (gateAt_mem C n w h1 h2)
  obtain ⟨i1, i2, he⟩ : ∃ a b : ℕ, (gateAt C n w).inputs = [a, b] := by
    rcases h : (gateAt C n w).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp_all
  refine ⟨i1, i2, he, ?_⟩
  rcases hop with hop | hop
  · left
    intro y
    rw [V_gate C y w h1 h2, he, hop]
    simp [GateOp.eval]
  · right
    intro y
    rw [V_gate C y w h1 h2, he, hop]
    simp [GateOp.eval]

lemma mono (C : Circuit) {n : ℕ}
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (y y' : Fin n → Bool) (hy : ∀ q, y q = true → y' q = true) :
    ∀ w, V C y w = true → V C y' w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw
  by_cases h1 : w < n
  · rw [V_input C y w h1] at hw
    rw [V_input C y' w h1]
    exact hy _ hw
  by_cases h2 : w < n + C.gates.length
  · obtain ⟨i1, i2, -, hop⟩ := shape C n hG w (by omega) h2
    have hc : ∀ i, cv C y w i = true → cv C y' w i = true := by
      intro i
      unfold cv
      split_ifs with hi
      · exact ih i hi
      · simp
    rcases hop with hop | hop
    · rw [hop] at hw ⊢
      simp only [Bool.and_eq_true] at hw ⊢
      exact ⟨hc _ hw.1, hc _ hw.2⟩
    · rw [hop] at hw ⊢
      simp only [Bool.or_eq_true] at hw ⊢
      exact hw.imp (hc _) (hc _)
  · rw [V_ge C y w (by omega)] at hw
    exact absurd hw (by simp)

def ev {n : ℕ} (a : Fin n) : Fin n → Bool := fun b => decide (b = a)

def U (C : Circuit) (n w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun a : Fin n => V C (ev a) w = true)

lemma U_input (C : Circuit) (n w : ℕ) (h : w < n) : (U C n w).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨⟨w, h⟩, ?_⟩
  ext a
  simp [U, V_input C _ w h, ev, eq_comm]

lemma U_ge (C : Circuit) (n w : ℕ) (h : n + C.gates.length ≤ w) : U C n w = ∅ := by
  ext a
  simp [U, V_ge C _ w h]

def kids (C : Circuit) (n w : ℕ) : Finset ℕ :=
  ((gateAt C n w).inputs.filter (fun i => decide (i < w))).toFinset

lemma kids_lt (C : Circuit) (n w c : ℕ) (h : c ∈ kids C n w) : c < w := by
  simp [kids] at h
  exact h.2

lemma kids_card (C : Circuit) (n : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (w : ℕ) : (kids C n w).card ≤ 2 := by
  unfold kids
  refine (List.toFinset_card_le _).trans ((List.length_filter_le _ _).trans ?_)
  by_cases h : w - n < C.gates.length
  · have hm : gateAt C n w ∈ C.gates := by
      unfold gateAt
      rw [List.getD_eq_getElem _ _ h]
      exact List.getElem_mem _
    rw [(hG _ hm).2]
  · unfold gateAt
    rw [List.getD_eq_default _ _ (by omega)]
    simp

def priv (C : Circuit) (n : ℕ) (T : Finset (Fin n)) (w : ℕ) : Prop :=
  n ≤ w ∧ w < n + C.gates.length ∧ U C n w ⊆ T ∧ 2 ≤ (U C n w).card

lemma kid_of_cv (C : Circuit) {n : ℕ} (y : Fin n → Bool) (w i1 i2 : ℕ)
    (he : (gateAt C n w).inputs = [i1, i2]) (i : ℕ) (hi : i = i1 ∨ i = i2)
    (h : cv C y w i = true) : i ∈ kids C n w ∧ V C y i = true := by
  unfold cv at h
  split_ifs at h with hlt
  · refine ⟨?_, h⟩
    simp only [kids, he, List.mem_toFinset, List.mem_filter, List.mem_cons,
      List.not_mem_nil, decide_eq_true_eq]
    exact ⟨by tauto, hlt⟩

lemma per_out (C : Circuit) (n k : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (T : Finset (Fin n)) (o : ℕ) (hT2 : 2 ≤ (U C n o).card)
    (hsub : ∀ p : Fin n, V C (ev p) o = true → p ∈ T)
    (hprom : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
      (∀ q ∈ T, x q = false) → V C x o = false) :
    ∃ Cl : Finset ℕ, (∀ w ∈ Cl, priv C n T w) ∧
      (k ≤ Cl.card ∨ (U C n o).card ≤ Cl.card + 1) := by
  classical
  have hpo : priv C n T o := by
    refine ⟨?_, ?_, ?_, hT2⟩
    · by_contra h
      have := U_input C n o (by omega)
      omega
    · by_contra h
      rw [U_ge C n o (by omega)] at hT2
      simp at hT2
    · intro p hp
      exact hsub p (by simpa [U] using hp)
  let R : ℕ → ℕ → Prop := fun a b => priv C n T a ∧ b ∈ kids C n a ∧ priv C n T b
  let Cl : Finset ℕ := (Finset.range (n + C.gates.length)).filter
    (fun w => priv C n T w ∧ Relation.ReflTransGen R o w)
  let X : Finset ℕ := (Cl.biUnion (kids C n)).filter (fun w => ¬ priv C n T w)
  have hcl_priv : ∀ w ∈ Cl, priv C n T w := fun w hw => (Finset.mem_filter.mp hw).2.1
  have hoCl : o ∈ Cl := by
    simp only [Cl, Finset.mem_filter, Finset.mem_range]
    exact ⟨hpo.2.1, hpo, Relation.ReflTransGen.refl⟩
  have hcl_step : ∀ g ∈ Cl, ∀ c ∈ kids C n g, priv C n T c → c ∈ Cl := by
    intro g hg c hc hpc
    simp only [Cl, Finset.mem_filter, Finset.mem_range] at hg ⊢
    exact ⟨hpc.2.1, hpc, hg.2.2.tail ⟨hg.2.1, hc, hpc⟩⟩
  have hcl_par : ∀ w ∈ Cl, w ≠ o → ∃ g ∈ Cl, w ∈ kids C n g := by
    intro w hw hne
    simp only [Cl, Finset.mem_filter, Finset.mem_range] at hw
    rcases Relation.ReflTransGen.cases_tail hw.2.2 with h | ⟨g, hg, hr⟩
    · exact absurd h hne
    · refine ⟨g, ?_, hr.2.1⟩
      simp only [Cl, Finset.mem_filter, Finset.mem_range]
      exact ⟨hr.1.2.1, hr.1, hg⟩
  have hcount : X.card ≤ Cl.card + 1 := by
    have hdis : Disjoint (Cl.erase o) X := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      exact (Finset.mem_filter.mp h2).2 (hcl_priv w (Finset.mem_of_mem_erase h1))
    have hsubD : Cl.erase o ∪ X ⊆ Cl.biUnion (kids C n) := by
      intro w hw
      rcases Finset.mem_union.mp hw with h | h
      · obtain ⟨g, hg, hk⟩ := hcl_par w (Finset.mem_of_mem_erase h) (Finset.ne_of_mem_erase h)
        exact Finset.mem_biUnion.mpr ⟨g, hg, hk⟩
      · exact (Finset.mem_filter.mp h).1
    have h1 := Finset.card_le_card hsubD
    rw [Finset.card_union_of_disjoint hdis, Finset.card_erase_of_mem hoCl] at h1
    have h2 : (Cl.biUnion (kids C n)).card ≤ ∑ g ∈ Cl, (kids C n g).card :=
      Finset.card_biUnion_le
    have h3 : ∑ g ∈ Cl, (kids C n g).card ≤ ∑ _g ∈ Cl, 2 :=
      Finset.sum_le_sum (fun g _ => kids_card C n hG g)
    rw [Finset.sum_const, smul_eq_mul] at h3
    have h4 : 1 ≤ Cl.card := Finset.card_pos.mpr ⟨o, hoCl⟩
    omega
  let B : Finset ℕ := X.filter (fun c => ¬ U C n c ⊆ T)
  have hB : ∀ c ∈ B, ∃ a, a ∈ U C n c ∧ a ∉ T := by
    intro c hc
    obtain ⟨a, ha, hna⟩ := Finset.not_subset.mp (Finset.mem_filter.mp hc).2
    exact ⟨a, ha, hna⟩
  let pick : B → Fin n := fun c => (hB c.1 c.2).choose
  let Ts : Finset (Fin n) := B.attach.image pick
  let x : Fin n → Bool := fun q => decide (q ∈ Ts)
  have hxw : (Finset.univ.filter (fun q : Fin n => x q = true)).card = Ts.card := by
    congr 1
    ext q
    simp [x]
  have hTsX : Ts.card ≤ X.card := by
    refine (Finset.card_image_le).trans ?_
    rw [Finset.card_attach]
    exact Finset.card_filter_le _ _
  have hxT : ∀ q ∈ T, x q = false := by
    intro q hq
    simp only [x, decide_eq_false_iff_not]
    intro hm
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hm
    exact (hB c.1 c.2).choose_spec.2 hq
  have hbig : ∀ c ∈ X, ¬ U C n c ⊆ T → V C x c = true := by
    intro c hc hn
    have hcB : c ∈ B := Finset.mem_filter.mpr ⟨hc, hn⟩
    have hspec := (hB c hcB).choose_spec
    have hmem : pick ⟨c, hcB⟩ ∈ Ts := Finset.mem_image_of_mem _ (Finset.mem_attach _ _)
    have hv : V C (ev (pick ⟨c, hcB⟩)) c = true := (Finset.mem_filter.mp hspec.1).2
    refine mono C hG _ x ?_ c hv
    intro q hq
    simp only [ev, decide_eq_true_eq] at hq
    subst hq
    simpa [x] using hmem
  refine ⟨Cl, hcl_priv, ?_⟩
  by_cases hxo : V C x o = true
  · left
    by_contra hlt
    have := hprom x (by rw [hxw]; omega) hxT
    rw [this] at hxo
    exact absurd hxo (by simp)
  · right
    have hxo' : V C x o = false := by simpa using hxo
    have walk : ∀ w, w ∈ Cl → V C x w = false → ∀ a : Fin n, V C (ev a) w = true →
        ∃ c ∈ X, a ∈ U C n c ∧ (U C n c).card ≤ 1 := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
      intro hw hxw0 a haw
      have hpw := hcl_priv w hw
      obtain ⟨i1, i2, he, hop⟩ := shape C n hG w hpw.1 hpw.2.1
      have hchild : ∃ c ∈ kids C n w, V C x c = false ∧ V C (ev a) c = true := by
        rcases hop with hop | hop
        · rw [hop] at haw hxw0
          simp only [Bool.and_eq_true] at haw
          obtain ⟨k1, v1⟩ := kid_of_cv C _ w i1 i2 he i1 (Or.inl rfl) haw.1
          obtain ⟨k2, v2⟩ := kid_of_cv C _ w i1 i2 he i2 (Or.inr rfl) haw.2
          have l1 := kids_lt C n w i1 k1
          have l2 := kids_lt C n w i2 k2
          simp only [cv, l1, l2, ite_true, Bool.and_eq_false_iff] at hxw0
          rcases hxw0 with h | h
          · exact ⟨i1, k1, h, v1⟩
          · exact ⟨i2, k2, h, v2⟩
        · rw [hop] at haw hxw0
          simp only [Bool.or_eq_true] at haw
          simp only [Bool.or_eq_false_iff] at hxw0
          rcases haw with h | h
          · obtain ⟨k1, v1⟩ := kid_of_cv C _ w i1 i2 he i1 (Or.inl rfl) h
            have l1 := kids_lt C n w i1 k1
            have := hxw0.1
            simp only [cv, l1, ite_true] at this
            exact ⟨i1, k1, this, v1⟩
          · obtain ⟨k2, v2⟩ := kid_of_cv C _ w i1 i2 he i2 (Or.inr rfl) h
            have l2 := kids_lt C n w i2 k2
            have := hxw0.2
            simp only [cv, l2, ite_true] at this
            exact ⟨i2, k2, this, v2⟩
      obtain ⟨c, hck, hxc, hac⟩ := hchild
      have hcw := kids_lt C n w c hck
      by_cases hpc : priv C n T c
      · exact ih c hcw (hcl_step w hw c hck hpc) hxc a hac
      · refine ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨w, hw, hck⟩, hpc⟩, ?_, ?_⟩
        · simpa [U] using hac
        · by_contra hc2'
          have hc2 : 2 ≤ (U C n c).card := by omega
          have hcX : c ∈ X := Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨w, hw, hck⟩, hpc⟩
          have hsubc : U C n c ⊆ T := by
            by_contra hn
            rw [hbig c hcX hn] at hxc
            exact absurd hxc (by simp)
          apply hpc
          refine ⟨?_, by have := hpw.2.1; omega, hsubc, hc2⟩
          by_contra hlt
          have := U_input C n c (by omega)
          omega
    let Y : Finset ℕ := X.filter (fun c => (U C n c).card ≤ 1)
    have hcov : U C n o ⊆ Y.biUnion (U C n) := by
      intro a ha
      have hv : V C (ev a) o = true := (Finset.mem_filter.mp ha).2
      obtain ⟨c, hcX, hac, hc1⟩ := walk o hoCl hxo' a hv
      exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_filter.mpr ⟨hcX, hc1⟩, hac⟩
    have e1 := Finset.card_le_card hcov
    have e2 : (Y.biUnion (U C n)).card ≤ ∑ c ∈ Y, (U C n c).card := Finset.card_biUnion_le
    have e3 : ∑ c ∈ Y, (U C n c).card ≤ ∑ _c ∈ Y, 1 :=
      Finset.sum_le_sum (fun c hc => (Finset.mem_filter.mp hc).2)
    rw [Finset.sum_const, smul_eq_mul, mul_one] at e3
    have e4 : Y.card ≤ X.card := Finset.card_filter_le _ _
    omega

end PEqualNP.Outside.L_meta_782

theorem PEqualNP.Outside.L_meta_782 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c hS hA2 hG hsub hprom hck hcA
  classical
  have key := fun i : Fin m => PEqualNP.Outside.L_meta_782.per_out C n k hG (S i) (o i)
    (hA2 i) (fun p hp => hsub i p hp) (fun x hx hz => hprom i x hx hz)
  choose Cl hCl using key
  have hci : ∀ i, c i ≤ (Cl i).card := by
    intro i
    have h1 := hck i
    have h2 := hcA i
    rcases (hCl i).2 with h | h
    · omega
    · have : (PEqualNP.Outside.L_meta_782.U C n (o i)).card = (Finset.univ.filter (fun a : Fin n =>
          (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card :=
        rfl
      omega
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ (Finset.univ : Finset (Fin m)),
      i ≠ j → Disjoint (Cl i) (Cl j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro w hwi hwj
    have pi := (hCl i).1 w hwi
    have pj := (hCl j).1 w hwj
    have h1 := Finset.card_le_card (Finset.subset_inter pi.2.2.1 pj.2.2.1)
    have h2 := hS i j hij
    have h3 := pi.2.2.2
    omega
  have hsubI : (Finset.univ.biUnion Cl) ⊆ Finset.Ico n (n + C.gates.length) := by
    intro w hw
    obtain ⟨i, -, hwi⟩ := Finset.mem_biUnion.mp hw
    have p := (hCl i).1 w hwi
    exact Finset.mem_Ico.mpr ⟨p.1, p.2.1⟩
  have hsum : ∑ i : Fin m, c i ≤ ∑ i : Fin m, (Cl i).card := Finset.sum_le_sum (fun i _ => hci i)
  rw [← Finset.card_biUnion hdisj] at hsum
  have := Finset.card_le_card hsubI
  simp only [Nat.card_Ico] at this
  unfold PEqualNP.CircuitLowerBounds.Circuit.size
  omega
