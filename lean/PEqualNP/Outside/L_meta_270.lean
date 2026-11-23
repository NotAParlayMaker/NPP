import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L270

def gateEval (isAnd : Bool) (u v : Bool) : Bool := if isAnd then u && v else u || v

theorem gateEval_mono (isAnd : Bool) {u v u' v' : Bool} (hu : u = true → u' = true)
    (hv : v = true → v' = true) : gateEval isAnd u v = true → gateEval isAnd u' v' = true := by
  unfold gateEval
  cases isAnd <;> cases u <;> cases v <;> simp_all

theorem gateEval_and_true {u v : Bool} (h : gateEval true u v = true) : u = true ∧ v = true := by
  unfold gateEval at h
  cases u <;> cases v <;> simp_all

theorem gateEval_or_true {u v : Bool} (h : gateEval false u v = true) : u = true ∨ v = true := by
  unfold gateEval at h
  cases u <;> cases v <;> simp_all

theorem gateEval_or_false {u v : Bool} (h : gateEval false u v = false) : u = false ∧ v = false := by
  unfold gateEval at h
  cases u <;> cases v <;> simp_all

theorem gateEval_and_false {u v : Bool} (h : gateEval true u v = false) : u = false ∨ v = false := by
  unfold gateEval at h
  cases u <;> cases v <;> simp_all

theorem gateEval_true_of_and {u v : Bool} (hu : u = true) (hv : v = true) :
    gateEval true u v = true := by
  subst hu hv
  rfl

theorem gateEval_true_of_or_left {u v : Bool} (hu : u = true) : gateEval false u v = true := by
  subst hu
  rfl

theorem gateEval_true_of_or_right {u v : Bool} (hv : v = true) : gateEval false u v = true := by
  subst hv
  unfold gateEval
  simp

def e {n : ℕ} (p : Fin n) : Fin n → Bool := fun q => decide (q = p)

def rd {n : ℕ} (val : (Fin n → Bool) → ℕ → Bool) (x : Fin n → Bool) (w a : ℕ) : Bool :=
  if a < w then val x a else false

def Model {n : ℕ} (m : ℕ) (g : ℕ → Bool × ℕ × ℕ) (val : (Fin n → Bool) → ℕ → Bool) : Prop :=
  (∀ (x : Fin n → Bool) (p : Fin n), val x p.val = x p) ∧
  (∀ (x : Fin n → Bool) (w : ℕ), n ≤ w → w < n + m →
    val x w = gateEval (g w).1 (rd val x w (g w).2.1) (rd val x w (g w).2.2)) ∧
  (∀ (x : Fin n → Bool) (w : ℕ), n + m ≤ w → val x w = false)

section Abstract

variable {n m : ℕ} {g : ℕ → Bool × ℕ × ℕ} {val : (Fin n → Bool) → ℕ → Bool}

theorem rd_true {x : Fin n → Bool} {w a : ℕ} (h : rd val x w a = true) : a < w ∧ val x a = true := by
  unfold rd at h
  by_cases ha : a < w
  · simp only [ha, ↓reduceIte] at h
    exact ⟨ha, h⟩
  · simp only [ha, ↓reduceIte] at h
    exact absurd h Bool.false_ne_true

theorem rd_of_lt {x : Fin n → Bool} {w a : ℕ} (h : a < w) : rd val x w a = val x a := by
  unfold rd
  simp only [h, ↓reduceIte]

theorem rd_of_ge {x : Fin n → Bool} {w a : ℕ} (h : ¬ a < w) : rd val x w a = false := by
  unfold rd
  simp only [h, ↓reduceIte]

theorem val_mono (hM : Model m g val) {x y : Fin n → Bool}
    (hxy : ∀ p, x p = true → y p = true) : ∀ w, val x w = true → val y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hx
  rcases Nat.lt_or_ge w n with hw | hw
  · have h1 := hM.1 x ⟨w, hw⟩
    have h2 := hM.1 y ⟨w, hw⟩
    simp only at h1 h2
    rw [h2]
    exact hxy _ (h1 ▸ hx)
  · rcases Nat.lt_or_ge w (n + m) with hw2 | hw2
    · rw [hM.2.1 x w hw hw2] at hx
      rw [hM.2.1 y w hw hw2]
      refine gateEval_mono _ ?_ ?_ hx
      · intro ha
        obtain ⟨hlt, hv⟩ := rd_true ha
        rw [rd_of_lt hlt]
        exact ih _ hlt hv
      · intro hb
        obtain ⟨hlt, hv⟩ := rd_true hb
        rw [rd_of_lt hlt]
        exact ih _ hlt hv
    · rw [hM.2.2 x w hw2] at hx
      exact absurd hx Bool.false_ne_true

def pt (val : (Fin n → Bool) → ℕ → Bool) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => val (e p) w = true)

theorem mem_pt {w : ℕ} {p : Fin n} : p ∈ pt val w ↔ val (e p) w = true := by
  simp [pt]

theorem pt_input (hM : Model m g val) (p : Fin n) : pt val p.val = {p} := by
  ext q
  rw [mem_pt, hM.1, Finset.mem_singleton]
  simp [e, eq_comm]

theorem pt_out (hM : Model m g val) {w : ℕ} (hw : n + m ≤ w) : pt val w = ∅ := by
  ext q
  rw [mem_pt, hM.2.2 _ _ hw]
  simp

def ptr (val : (Fin n → Bool) → ℕ → Bool) (w a : ℕ) : Finset (Fin n) :=
  if a < w then pt val a else ∅

theorem mem_ptr {w a : ℕ} {p : Fin n} : p ∈ ptr val w a ↔ rd val (e p) w a = true := by
  unfold ptr rd
  split_ifs
  · exact mem_pt
  · simp

theorem pt_gate_and (hM : Model m g val) {w : ℕ} (hw : n ≤ w) (hw2 : w < n + m)
    (ha : (g w).1 = true) : pt val w = ptr val w (g w).2.1 ∩ ptr val w (g w).2.2 := by
  ext q
  rw [mem_pt, Finset.mem_inter, mem_ptr, mem_ptr, hM.2.1 _ _ hw hw2, ha]
  unfold gateEval
  simp

theorem pt_gate_or (hM : Model m g val) {w : ℕ} (hw : n ≤ w) (hw2 : w < n + m)
    (ha : (g w).1 = false) : pt val w = ptr val w (g w).2.1 ∪ ptr val w (g w).2.2 := by
  ext q
  rw [mem_pt, Finset.mem_union, mem_ptr, mem_ptr, hM.2.1 _ _ hw hw2, ha]
  unfold gateEval
  simp

theorem ptr_subset {w a : ℕ} (h : a < w) : ptr val w a = pt val a := by
  unfold ptr
  simp only [h, ↓reduceIte]

theorem ptr_empty {w a : ℕ} (h : ¬ a < w) : ptr val w a = ∅ := by
  unfold ptr
  simp only [h, ↓reduceIte]

theorem count_dag (Z : Finset ℕ) (o : ℕ) (ch : ℕ → Finset ℕ) (ho : o ∈ Z)
    (hpar : ∀ w ∈ Z, w ≠ o → ∃ v ∈ Z, w ∈ ch v) :
    Z.card ≤ (∑ v ∈ Z, (ch v).card) + 1 := by
  have h1 : Z.erase o ⊆ Z.biUnion ch := by
    intro w hw
    rw [Finset.mem_erase] at hw
    obtain ⟨v, hv, hwv⟩ := hpar w hw.2 hw.1
    exact Finset.mem_biUnion.2 ⟨v, hv, hwv⟩
  have h2 := Finset.card_le_card h1
  have h3 := Finset.card_biUnion_le (s := Z) (t := ch)
  rw [Finset.card_erase_of_mem ho] at h2
  omega

end Abstract

section PerOutput

variable {n : ℕ} (m : ℕ) (g : ℕ → Bool × ℕ × ℕ) (val : (Fin n → Bool) → ℕ → Bool)
  (S : Finset (Fin n))

def privB (w : ℕ) : Bool := decide (pt val w ⊆ S) && decide (2 ≤ (pt val w).card)

def rho : ℕ → Bool
  | w =>
    if w < n then false
    else if n + m ≤ w then false
    else if ¬ (pt val w ⊆ S) then true
    else if (pt val w).card ≤ 1 then false
    else gateEval (g w).1 (if h : (g w).2.1 < w then rho (g w).2.1 else false)
      (if h : (g w).2.2 < w then rho (g w).2.2 else false)
termination_by w => w

def rr (w a : ℕ) : Bool := if a < w then rho m g val S a else false

theorem rho_input {w : ℕ} (hw : w < n) : rho m g val S w = false := by
  rw [rho]
  simp [hw]

theorem rho_out {w : ℕ} (hw : n + m ≤ w) : rho m g val S w = false := by
  rw [rho]
  have : ¬ w < n := by omega
  simp [this, hw]

theorem rho_leaving {w : ℕ} (hw : n ≤ w) (hw2 : w < n + m) (hl : ¬ (pt val w ⊆ S)) :
    rho m g val S w = true := by
  rw [rho]
  have h1 : ¬ w < n := by omega
  have h2 : ¬ n + m ≤ w := by omega
  simp [h1, h2, hl]

theorem rho_small {w : ℕ} (hw : n ≤ w) (hw2 : w < n + m) (hs : pt val w ⊆ S)
    (hc : (pt val w).card ≤ 1) : rho m g val S w = false := by
  rw [rho]
  have h1 : ¬ w < n := by omega
  have h2 : ¬ n + m ≤ w := by omega
  simp [h1, h2, hs, hc]

theorem rho_priv {w : ℕ} (hw : n ≤ w) (hw2 : w < n + m) (hs : pt val w ⊆ S)
    (hc : 2 ≤ (pt val w).card) :
    rho m g val S w = gateEval (g w).1 (rr m g val S w (g w).2.1) (rr m g val S w (g w).2.2) := by
  rw [rho]
  have h1 : ¬ w < n := by omega
  have h2 : ¬ n + m ≤ w := by omega
  have h3 : ¬ (pt val w).card ≤ 1 := by omega
  simp only [h1, h2, hs, h3, not_true_eq_false, not_false_eq_true, ↓reduceIte, ↓reduceDIte]
  unfold rr
  rfl

theorem rr_true {w a : ℕ} (h : rr m g val S w a = true) : a < w ∧ rho m g val S a = true := by
  unfold rr at h
  by_cases ha : a < w
  · simp only [ha, ↓reduceIte] at h
    exact ⟨ha, h⟩
  · simp only [ha, ↓reduceIte] at h
    exact absurd h Bool.false_ne_true

theorem rr_of_lt {w a : ℕ} (h : a < w) : rr m g val S w a = rho m g val S a := by
  unfold rr
  simp only [h, ↓reduceIte]

theorem privB_true {w : ℕ} : privB val S w = true ↔ pt val w ⊆ S ∧ 2 ≤ (pt val w).card := by
  simp [privB]

theorem rho_true_cases {w : ℕ} (h : rho m g val S w = true) :
    n ≤ w ∧ w < n + m ∧ (¬ (pt val w ⊆ S) ∨ privB val S w = true) := by
  rcases Nat.lt_or_ge w n with hw | hw
  · rw [rho_input m g val S hw] at h
    exact absurd h Bool.false_ne_true
  rcases Nat.lt_or_ge w (n + m) with hw2 | hw2
  · refine ⟨hw, hw2, ?_⟩
    by_cases hs : pt val w ⊆ S
    · right
      rw [privB_true]
      refine ⟨hs, ?_⟩
      by_contra hc
      rw [rho_small m g val S hw hw2 hs (by omega)] at h
      exact absurd h Bool.false_ne_true
    · left
      exact hs
  · rw [rho_out m g val S hw2] at h
    exact absurd h Bool.false_ne_true

theorem privB_gate (hM : Model m g val) {w : ℕ} (h : privB val S w = true) : n ≤ w ∧ w < n + m := by
  rw [privB_true] at h
  rcases Nat.lt_or_ge w n with hw | hw
  · have := pt_input hM ⟨w, hw⟩
    simp only at this
    rw [this, Finset.card_singleton] at h
    omega
  rcases Nat.lt_or_ge w (n + m) with hw2 | hw2
  · exact ⟨hw, hw2⟩
  · rw [pt_out hM hw2, Finset.card_empty] at h
    omega

end PerOutput

section Reach

variable (ch : ℕ → Finset ℕ) (o : ℕ)

def reach (w : ℕ) : Prop := Relation.ReflTransGen (fun u v => v ∈ ch u) o w

noncomputable def R : Finset ℕ :=
  @Finset.filter ℕ (reach ch o) (fun _ => Classical.propDecidable _) (Finset.range (o + 1))

theorem reach_le (hch : ∀ u v, v ∈ ch u → v < u) {w : ℕ} (h : reach ch o w) : w ≤ o := by
  unfold reach at h
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact le_trans (le_of_lt (hch _ _ hstep)) ih

theorem mem_R (hch : ∀ u v, v ∈ ch u → v < u) {w : ℕ} : w ∈ R ch o ↔ reach ch o w := by
  unfold R
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨Nat.lt_succ_of_le (reach_le ch o hch h), h⟩

theorem R_root (hch : ∀ u v, v ∈ ch u → v < u) : o ∈ R ch o := by
  rw [mem_R ch o hch]
  exact Relation.ReflTransGen.refl

theorem R_closed (hch : ∀ u v, v ∈ ch u → v < u) {w u : ℕ} (hw : w ∈ R ch o) (hu : u ∈ ch w) :
    u ∈ R ch o := by
  rw [mem_R ch o hch] at hw ⊢
  exact Relation.ReflTransGen.tail hw hu

theorem R_parent (hch : ∀ u v, v ∈ ch u → v < u) {w : ℕ} (hw : w ∈ R ch o) (hne : w ≠ o) :
    ∃ v ∈ R ch o, w ∈ ch v := by
  rw [mem_R ch o hch] at hw
  rcases Relation.ReflTransGen.cases_tail hw with h | ⟨v, hv, hstep⟩
  · exact absurd h hne
  · exact ⟨v, (mem_R ch o hch).2 hv, hstep⟩

theorem R_ind (hch : ∀ u v, v ∈ ch u → v < u) (P : ℕ → Prop) (h0 : P o)
    (hstep : ∀ w, P w → ∀ u ∈ ch w, P u) : ∀ w ∈ R ch o, P w := by
  intro w hw
  rw [mem_R ch o hch] at hw
  unfold reach at hw
  induction hw with
  | refl => exact h0
  | tail _ hs ih => exact hstep _ ih _ hs

end Reach

section CaseOne

variable {n : ℕ} (m : ℕ) (g : ℕ → Bool × ℕ × ℕ) (val : (Fin n → Bool) → ℕ → Bool)
  (S : Finset (Fin n))

def ch1 (w : ℕ) : Finset ℕ :=
  if privB val S w = true ∧ rho m g val S w = true then
    (if (g w).1 = true then {(g w).2.1, (g w).2.2}
      else if rr m g val S w (g w).2.1 = true then {(g w).2.1} else {(g w).2.2})
  else ∅

theorem ch1_mem (hM : Model m g val) {w u : ℕ} (hu : u ∈ ch1 m g val S w) :
    u < w ∧ rho m g val S u = true := by
  unfold ch1 at hu
  split_ifs at hu with hpr hand hra
  · obtain ⟨hw, hw2⟩ := privB_gate m g val S hM hpr.1
    have hp := (privB_true val S).1 hpr.1
    have hr := hpr.2
    rw [rho_priv m g val S hw hw2 hp.1 hp.2, hand] at hr
    obtain ⟨h1, h2⟩ := gateEval_and_true hr
    rw [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact rr_true m g val S h1
    · exact rr_true m g val S h2
  · rw [Finset.mem_singleton] at hu
    subst hu
    exact rr_true m g val S hra
  · obtain ⟨hw, hw2⟩ := privB_gate m g val S hM hpr.1
    have hp := (privB_true val S).1 hpr.1
    have hr := hpr.2
    rw [rho_priv m g val S hw hw2 hp.1 hp.2] at hr
    have hand' : (g w).1 = false := Bool.eq_false_iff.2 hand
    rw [hand'] at hr
    rcases gateEval_or_true hr with h1 | h1
    · exact absurd h1 hra
    · rw [Finset.mem_singleton] at hu
      subst hu
      exact rr_true m g val S h1
  · exact absurd hu (Finset.notMem_empty u)

theorem ch1_card (w : ℕ) : (ch1 m g val S w).card ≤
    2 * (if privB val S w = true ∧ (g w).1 = true then 1 else 0) +
      (if privB val S w = true ∧ (g w).1 = false then 1 else 0) := by
  unfold ch1
  split_ifs with hpr hand h1 h2 h3 <;> simp_all [Finset.card_le_two]

def qOf (d : Fin n) (w : ℕ) : Fin n :=
  if h : (pt val w \ S).Nonempty then (pt val w \ S).min' h else d

theorem qOf_mem (d : Fin n) {w : ℕ} (h : ¬ (pt val w ⊆ S)) : qOf val S d w ∈ pt val w \ S := by
  unfold qOf
  have hne : (pt val w \ S).Nonempty := Finset.sdiff_nonempty.2 h
  simp only [hne, ↓reduceDIte]
  exact Finset.min'_mem _ _

theorem case_one (hM : Model m g val) (k o : ℕ) (d : Fin n) (ho : rho m g val S o = true)
    (hB : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
      (∀ q ∈ S, x q = false) → val x o = false) :
    k ≤ ((Finset.Ico n (n + m)).filter (fun w => privB val S w = true)).card := by
  have hch : ∀ u v, v ∈ ch1 m g val S u → v < u := fun u v h => (ch1_mem m g val S hM h).1
  set Rs := R (ch1 m g val S) o with hRs
  have hR_rho : ∀ w ∈ Rs, rho m g val S w = true :=
    R_ind (ch1 m g val S) o hch _ ho (fun w _ u hu => (ch1_mem m g val S hM hu).2)
  set Rsrc := Rs.filter (fun w => privB val S w = false) with hRsrc
  set Rp := Rs.filter (fun w => privB val S w = true) with hRp
  set Rand := Rp.filter (fun w => (g w).1 = true) with hRand
  set Ror := Rp.filter (fun w => (g w).1 = false) with hRor
  have hsplit1 : Rsrc.card + Rp.card = Rs.card := by
    rw [hRsrc, hRp]
    have := Finset.card_filter_add_card_filter_not (s := Rs) (p := fun w => privB val S w = false)
    simp only [Bool.not_eq_false] at this
    exact this
  have hsplit2 : Rand.card + Ror.card = Rp.card := by
    rw [hRand, hRor]
    have := Finset.card_filter_add_card_filter_not (s := Rp) (p := fun w => (g w).1 = true)
    simp only [Bool.not_eq_true] at this
    exact this
  have hcount := count_dag Rs o (ch1 m g val S) (R_root _ _ hch) (fun w hw hne => R_parent _ _ hch hw hne)
  have hsum : (∑ v ∈ Rs, (ch1 m g val S v).card) ≤ 2 * Rand.card + Ror.card := by
    calc (∑ v ∈ Rs, (ch1 m g val S v).card)
        ≤ ∑ v ∈ Rs, (2 * (if privB val S v = true ∧ (g v).1 = true then 1 else 0) +
            (if privB val S v = true ∧ (g v).1 = false then 1 else 0)) :=
          Finset.sum_le_sum (fun v _ => ch1_card m g val S v)
      _ = 2 * Rand.card + Ror.card := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_boole]
          simp only [Nat.cast_id, hRand, hRor, hRp, Finset.filter_filter]
  have hsrc : Rsrc.card ≤ Rand.card + 1 := by omega
  let Q : Finset (Fin n) := Rsrc.image (qOf val S d)
  have hQmem : ∀ q ∈ Q, ∃ w ∈ Rsrc, qOf val S d w = q := fun q hq => Finset.mem_image.1 hq
  have hsrc_leaving : ∀ w ∈ Rsrc, ¬ (pt val w ⊆ S) := by
    intro w hw
    rw [hRsrc, Finset.mem_filter] at hw
    have hr := hR_rho w hw.1
    rcases (rho_true_cases m g val S hr).2.2 with h | h
    · exact h
    · rw [h] at hw
      exact absurd hw.2 (by decide)
  have hQavoid : ∀ q ∈ S, decide (q ∈ Q) = false := by
    intro q hq
    rw [decide_eq_false_iff_not]
    intro hqQ
    obtain ⟨w, hw, hwq⟩ := hQmem q hqQ
    have := qOf_mem val S d (hsrc_leaving w hw)
    rw [hwq, Finset.mem_sdiff] at this
    exact this.2 hq
  have hQcard : (Finset.univ.filter (fun q : Fin n => decide (q ∈ Q) = true)).card = Q.card := by
    congr 1
    ext q
    simp
  have hdom : ∀ w ∈ Rs, val (fun q => decide (q ∈ Q)) w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
    intro hw
    have hr := hR_rho w hw
    by_cases hpr : privB val S w = true
    · obtain ⟨hwn, hwm⟩ := privB_gate m g val S hM hpr
      have hp := (privB_true val S).1 hpr
      have hr' := hr
      rw [rho_priv m g val S hwn hwm hp.1 hp.2] at hr'
      rw [hM.2.1 _ _ hwn hwm]
      have hchw : ch1 m g val S w = (if (g w).1 = true then {(g w).2.1, (g w).2.2}
          else if rr m g val S w (g w).2.1 = true then {(g w).2.1} else {(g w).2.2}) := by
        unfold ch1
        simp only [hpr, hr, and_self, ↓reduceIte]
      by_cases hand : (g w).1 = true
      · rw [hand] at hr' ⊢
        obtain ⟨h1, h2⟩ := gateEval_and_true hr'
        obtain ⟨ha, _⟩ := rr_true m g val S h1
        obtain ⟨hb, _⟩ := rr_true m g val S h2
        have hainR : (g w).2.1 ∈ Rs := R_closed _ _ hch hw (by rw [hchw, hand]; simp)
        have hbinR : (g w).2.2 ∈ Rs := R_closed _ _ hch hw (by rw [hchw, hand]; simp)
        apply gateEval_true_of_and
        · rw [rd_of_lt ha]
          exact ih _ ha hainR
        · rw [rd_of_lt hb]
          exact ih _ hb hbinR
      · have hand' : (g w).1 = false := Bool.eq_false_iff.2 hand
        rw [hand'] at hr' ⊢
        by_cases hra : rr m g val S w (g w).2.1 = true
        · obtain ⟨ha, _⟩ := rr_true m g val S hra
          have hainR : (g w).2.1 ∈ Rs := R_closed _ _ hch hw (by rw [hchw, hand', hra]; simp)
          apply gateEval_true_of_or_left
          rw [rd_of_lt ha]
          exact ih _ ha hainR
        · rcases gateEval_or_true hr' with h1 | h1
          · exact absurd h1 hra
          · obtain ⟨hb, _⟩ := rr_true m g val S h1
            have hra' : rr m g val S w (g w).2.1 = false := Bool.eq_false_iff.2 hra
            have hbinR : (g w).2.2 ∈ Rs := R_closed _ _ hch hw (by rw [hchw, hand', hra']; simp)
            apply gateEval_true_of_or_right
            rw [rd_of_lt hb]
            exact ih _ hb hbinR
    · have hpr' : privB val S w = false := Bool.eq_false_iff.2 hpr
      have hwsrc : w ∈ Rsrc := by
        rw [hRsrc, Finset.mem_filter]
        exact ⟨hw, hpr'⟩
      have hl := hsrc_leaving w hwsrc
      have hq := qOf_mem val S d hl
      rw [Finset.mem_sdiff] at hq
      have hv : val (e (qOf val S d w)) w = true := mem_pt.1 hq.1
      refine val_mono hM ?_ w hv
      intro p hp
      unfold e at hp
      rw [decide_eq_true_iff] at hp
      subst hp
      rw [decide_eq_true_iff]
      exact Finset.mem_image.2 ⟨w, hwsrc, rfl⟩
  have hvo : val (fun q => decide (q ∈ Q)) o = true := hdom o (R_root _ _ hch)
  have hk : k < Q.card := by
    by_contra hle
    rw [not_lt] at hle
    have := hB (fun q => decide (q ∈ Q)) (by rw [hQcard]; exact hle) hQavoid
    rw [hvo] at this
    exact absurd this (by decide)
  have hQle : Q.card ≤ Rsrc.card := Finset.card_image_le
  have hRand_sub : Rand ⊆ (Finset.Ico n (n + m)).filter (fun w => privB val S w = true) := by
    intro w hw
    rw [hRand, Finset.mem_filter, hRp, Finset.mem_filter] at hw
    obtain ⟨hwn, hwm⟩ := privB_gate m g val S hM hw.1.2
    rw [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨hwn, hwm⟩, hw.1.2⟩
  have := Finset.card_le_card hRand_sub
  omega

end CaseOne

section CaseTwo

variable {n : ℕ} (m : ℕ) (g : ℕ → Bool × ℕ × ℕ) (val : (Fin n → Bool) → ℕ → Bool)
  (S : Finset (Fin n))

def ch0 (w : ℕ) : Finset ℕ :=
  if privB val S w = true ∧ rho m g val S w = false then
    Finset.filter (fun u => u < w) ((if (g w).1 = true then
        (if rr m g val S w (g w).2.1 = false then {(g w).2.1} else {(g w).2.2})
      else {(g w).2.1, (g w).2.2} : Finset ℕ))
  else ∅

theorem ch0_mem (hM : Model m g val) {w u : ℕ} (hu : u ∈ ch0 m g val S w) :
    u < w ∧ rho m g val S u = false := by
  unfold ch0 at hu
  split_ifs at hu with hpr hand hra
  · rw [Finset.mem_filter, Finset.mem_singleton] at hu
    obtain ⟨rfl, hlt⟩ := hu
    refine ⟨hlt, ?_⟩
    rw [rr_of_lt m g val S hlt] at hra
    exact hra
  · rw [Finset.mem_filter, Finset.mem_singleton] at hu
    obtain ⟨rfl, hlt⟩ := hu
    refine ⟨hlt, ?_⟩
    obtain ⟨hw, hw2⟩ := privB_gate m g val S hM hpr.1
    have hp := (privB_true val S).1 hpr.1
    have hr := hpr.2
    rw [rho_priv m g val S hw hw2 hp.1 hp.2, hand] at hr
    rcases gateEval_and_false hr with h1 | h1
    · exact absurd h1 hra
    · rw [rr_of_lt m g val S hlt] at h1
      exact h1
  · rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hu
    obtain ⟨hu, hlt⟩ := hu
    refine ⟨hlt, ?_⟩
    obtain ⟨hw, hw2⟩ := privB_gate m g val S hM hpr.1
    have hp := (privB_true val S).1 hpr.1
    have hr := hpr.2
    have hand' : (g w).1 = false := Bool.eq_false_iff.2 hand
    rw [rho_priv m g val S hw hw2 hp.1 hp.2, hand'] at hr
    obtain ⟨h1, h2⟩ := gateEval_or_false hr
    rcases hu with rfl | rfl
    · rw [rr_of_lt m g val S hlt] at h1
      exact h1
    · rw [rr_of_lt m g val S hlt] at h2
      exact h2
  · exact absurd hu (Finset.notMem_empty u)

theorem ch0_card (w : ℕ) : (ch0 m g val S w).card ≤
    2 * (if privB val S w = true ∧ (g w).1 = false then 1 else 0) +
      (if privB val S w = true ∧ (g w).1 = true then 1 else 0) := by
  unfold ch0
  split_ifs with hpr hand h1 h2 h3 <;> simp_all
  all_goals first
    | exact le_trans (Finset.card_filter_le _ _) (by simp)
    | exact le_trans (Finset.card_filter_le _ _) Finset.card_le_two

theorem ch0_pt (hM : Model m g val) {w : ℕ} (hpr : privB val S w = true)
    (hr : rho m g val S w = false) : pt val w ⊆ (ch0 m g val S w).biUnion (pt val) := by
  obtain ⟨hw, hw2⟩ := privB_gate m g val S hM hpr
  have hchw : ch0 m g val S w = Finset.filter (fun u => u < w) ((if (g w).1 = true then
        (if rr m g val S w (g w).2.1 = false then {(g w).2.1} else {(g w).2.2})
      else {(g w).2.1, (g w).2.2} : Finset ℕ)) := by
    unfold ch0
    simp only [hpr, hr, and_self, ↓reduceIte]
  have hsub : ∀ a : ℕ, ∀ T : Finset ℕ, a ∈ T →
      ptr val w a ⊆ (T.filter (fun u => u < w)).biUnion (pt val) := by
    intro a T ha
    by_cases hlt : a < w
    · rw [ptr_subset hlt]
      exact Finset.subset_biUnion_of_mem (pt val) (Finset.mem_filter.2 ⟨ha, hlt⟩)
    · rw [ptr_empty hlt]
      exact Finset.empty_subset _
  rw [hchw]
  by_cases hand : (g w).1 = true
  · rw [pt_gate_and hM hw hw2 hand, hand]
    by_cases hra : rr m g val S w (g w).2.1 = false
    · simp only [hra, ↓reduceIte]
      exact le_trans Finset.inter_subset_left (hsub _ _ (Finset.mem_singleton_self _))
    · simp only [hra, ↓reduceIte]
      exact le_trans Finset.inter_subset_right (hsub _ _ (Finset.mem_singleton_self _))
  · have hand' : (g w).1 = false := Bool.eq_false_iff.2 hand
    rw [pt_gate_or hM hw hw2 hand', hand']
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply Finset.union_subset
    · exact hsub _ _ (Finset.mem_insert_self _ _)
    · exact hsub _ _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

theorem leaf_card (hM : Model m g val) {w : ℕ} (hr : rho m g val S w = false)
    (hpr : privB val S w = false) : (pt val w).card ≤ 1 := by
  rcases Nat.lt_or_ge w n with hw | hw
  · have := pt_input hM ⟨w, hw⟩
    simp only at this
    rw [this, Finset.card_singleton]
  rcases Nat.lt_or_ge w (n + m) with hw2 | hw2
  · by_cases hs : pt val w ⊆ S
    · by_contra hc
      have : privB val S w = true := (privB_true val S).2 ⟨hs, by omega⟩
      rw [this] at hpr
      exact absurd hpr (by decide)
    · rw [rho_leaving m g val S hw hw2 hs] at hr
      exact absurd hr (by decide)
  · rw [pt_out hM hw2, Finset.card_empty]
    exact Nat.zero_le _

theorem case_two (hM : Model m g val) (o : ℕ) (ho : rho m g val S o = false)
    (hA : pt val o = S) :
    S.card ≤ ((Finset.Ico n (n + m)).filter (fun w => privB val S w = true)).card + 1 := by
  have hch : ∀ u v, v ∈ ch0 m g val S u → v < u := fun u v h => (ch0_mem m g val S hM h).1
  set Zs := R (ch0 m g val S) o with hZs
  have hZ_rho : ∀ w ∈ Zs, rho m g val S w = false :=
    R_ind (ch0 m g val S) o hch _ ho (fun w _ u hu => (ch0_mem m g val S hM hu).2)
  set Zleaf := Zs.filter (fun w => privB val S w = false) with hZleaf
  set Zp := Zs.filter (fun w => privB val S w = true) with hZp
  set Zor := Zp.filter (fun w => (g w).1 = false) with hZor
  set Zand := Zp.filter (fun w => (g w).1 = true) with hZand
  have hsplit1 : Zleaf.card + Zp.card = Zs.card := by
    rw [hZleaf, hZp]
    have := Finset.card_filter_add_card_filter_not (s := Zs) (p := fun w => privB val S w = false)
    simp only [Bool.not_eq_false] at this
    exact this
  have hsplit2 : Zor.card + Zand.card = Zp.card := by
    rw [hZor, hZand]
    have := Finset.card_filter_add_card_filter_not (s := Zp) (p := fun w => (g w).1 = false)
    simp only [Bool.not_eq_false] at this
    exact this
  have hcount := count_dag Zs o (ch0 m g val S) (R_root _ _ hch) (fun w hw hne => R_parent _ _ hch hw hne)
  have hsum : (∑ v ∈ Zs, (ch0 m g val S v).card) ≤ 2 * Zor.card + Zand.card := by
    calc (∑ v ∈ Zs, (ch0 m g val S v).card)
        ≤ ∑ v ∈ Zs, (2 * (if privB val S v = true ∧ (g v).1 = false then 1 else 0) +
            (if privB val S v = true ∧ (g v).1 = true then 1 else 0)) :=
          Finset.sum_le_sum (fun v _ => ch0_card m g val S v)
      _ = 2 * Zor.card + Zand.card := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_boole]
          simp only [Nat.cast_id, hZor, hZand, hZp, Finset.filter_filter]
  have hleaf : Zleaf.card ≤ Zor.card + 1 := by omega
  have hptsub : ∀ w ∈ Zs, pt val w ⊆ Zleaf.biUnion (pt val) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
    intro hw
    by_cases hpr : privB val S w = true
    · have hr := hZ_rho w hw
      refine le_trans (ch0_pt m g val S hM hpr hr) ?_
      apply Finset.biUnion_subset.2
      intro u hu
      exact ih u (ch0_mem m g val S hM hu).1 (R_closed _ _ hch hw hu)
    · have hpr' : privB val S w = false := Bool.eq_false_iff.2 hpr
      exact Finset.subset_biUnion_of_mem (pt val) (Finset.mem_filter.2 ⟨hw, hpr'⟩)
  have hS : S.card ≤ Zleaf.card := by
    calc S.card = (pt val o).card := by rw [hA]
      _ ≤ (Zleaf.biUnion (pt val)).card := Finset.card_le_card (hptsub o (R_root _ _ hch))
      _ ≤ ∑ w ∈ Zleaf, (pt val w).card := Finset.card_biUnion_le
      _ ≤ ∑ w ∈ Zleaf, 1 := by
          apply Finset.sum_le_sum
          intro w hw
          rw [hZleaf, Finset.mem_filter] at hw
          exact leaf_card m g val S hM (hZ_rho w hw.1) hw.2
      _ = Zleaf.card := by simp
  have hZor_sub : Zor ⊆ (Finset.Ico n (n + m)).filter (fun w => privB val S w = true) := by
    intro w hw
    rw [hZor, Finset.mem_filter, hZp, Finset.mem_filter] at hw
    obtain ⟨hwn, hwm⟩ := privB_gate m g val S hM hw.1.2
    rw [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨hwn, hwm⟩, hw.1.2⟩
  have := Finset.card_le_card hZor_sub
  omega

end CaseTwo

section Combine

variable {n : ℕ} (m : ℕ) (g : ℕ → Bool × ℕ × ℕ) (val : (Fin n → Bool) → ℕ → Bool)

theorem per_output (hM : Model m g val) (S : Finset (Fin n)) (k o c : ℕ) (d : Fin n)
    (hA : pt val o = S)
    (hB : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
      (∀ q ∈ S, x q = false) → val x o = false)
    (hck : c ≤ k) (hcs : c + 1 ≤ S.card) :
    c ≤ ((Finset.Ico n (n + m)).filter (fun w => privB val S w = true)).card := by
  by_cases ho : rho m g val S o = true
  · exact le_trans hck (case_one m g val S hM k o d ho hB)
  · have ho' : rho m g val S o = false := Bool.eq_false_iff.2 ho
    have := case_two m g val S hM o ho' hA
    omega

theorem priv_disjoint (S T : Finset (Fin n)) (hST : (S ∩ T).card ≤ 1) :
    Disjoint ((Finset.Ico n (n + m)).filter (fun w => privB val S w = true))
      ((Finset.Ico n (n + m)).filter (fun w => privB val T w = true)) := by
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  rw [Finset.mem_filter, privB_true] at hw1 hw2
  have hsub : pt val w ⊆ S ∩ T := Finset.subset_inter hw1.2.1 hw2.2.1
  have := Finset.card_le_card hsub
  omega

theorem total_bound (hM : Model m g val) {mm : ℕ} (S : Fin mm → Finset (Fin n))
    (o : Fin mm → ℕ) (c : Fin mm → ℕ) (k : ℕ) (d : Fin n)
    (hpair : ∀ i j : Fin mm, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hA : ∀ i, pt val (o i) = S i)
    (hB : ∀ (i : Fin mm) (x : Fin n → Bool),
      (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
      (∀ q ∈ S i, x q = false) → val x (o i) = false)
    (hck : ∀ i, c i ≤ k) (hcs : ∀ i, c i + 1 ≤ (S i).card) :
    ∑ i : Fin mm, c i ≤ m := by
  calc ∑ i : Fin mm, c i
      ≤ ∑ i : Fin mm, ((Finset.Ico n (n + m)).filter (fun w => privB val (S i) w = true)).card :=
        Finset.sum_le_sum (fun i _ => per_output m g val hM (S i) k (o i) (c i) d (hA i) (hB i) (hck i) (hcs i))
    _ = (Finset.univ.biUnion (fun i : Fin mm =>
          (Finset.Ico n (n + m)).filter (fun w => privB val (S i) w = true))).card := by
        rw [Finset.card_biUnion]
        intro i _ j _ hij
        exact priv_disjoint m val (S i) (S j) (hpair i j hij)
    _ ≤ (Finset.Ico n (n + m)).card := by
        apply Finset.card_le_card
        apply Finset.biUnion_subset.2
        intro i _
        exact Finset.filter_subset _ _
    _ = m := by simp

end Combine

section Bridge

def wiresFrom (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool) :
    C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_cons (g : PEqualNP.CircuitLowerBounds.Gate)
    (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
    wiresFrom (g :: gs) w = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem wiresFrom_start (gs : List PEqualNP.CircuitLowerBounds.Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [wiresFrom_cons, ht]
    simp

theorem length_wiresFrom (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]
  simp [hl]

theorem getD_wiresFrom (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (i : ℕ)
    (h : i < w.length) : (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc_eq (L : List Bool) (S : Bool) : (L ++ [S]).getD L.length false = S := by
  simp

def isAndOp : PEqualNP.CircuitLowerBounds.GateOp → Bool
  | PEqualNP.CircuitLowerBounds.GateOp.and => true
  | _ => false

def gdesc (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : ℕ) : Bool × ℕ × ℕ :=
  (isAndOp (gs.getD (w - n) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).op,
    (gs.getD (w - n) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs.getD 0 0,
    (gs.getD (w - n) ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs.getD 1 0)

def cval {n : ℕ} (C : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

theorem eval_two (op : PEqualNP.CircuitLowerBounds.GateOp)
    (hop : op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ op = PEqualNP.CircuitLowerBounds.GateOp.or)
    (u v : Bool) : op.eval [u, v] = gateEval (isAndOp op) u v := by
  rcases hop with rfl | rfl
  · simp [PEqualNP.CircuitLowerBounds.GateOp.eval, isAndOp, gateEval]
  · simp [PEqualNP.CircuitLowerBounds.GateOp.eval, isAndOp, gateEval]

theorem take_succ_eq (gs : List PEqualNP.CircuitLowerBounds.Gate) (j : ℕ) (hj : j < gs.length) :
    gs.take (j + 1) = gs.take j ++ [gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, List.getD_eq_getElem _ _ hj]
  rfl

theorem model_of_circuit {n : ℕ} (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) :
    Model C.gates.length (gdesc n C.gates) (cval (n := n) C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x p
    unfold cval
    rw [wires_eq, getD_wiresFrom _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp),
      List.getElem_ofFn]
  · intro x w hw hw2
    set j := w - n with hj
    have hjl : j < C.gates.length := by omega
    have hwj : w = n + j := by omega
    set gt := C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩ with hgt
    have hmem : gt ∈ C.gates := by
      rw [hgt, List.getD_eq_getElem _ _ hjl]
      exact List.getElem_mem hjl
    obtain ⟨hop, hlen⟩ := hC gt hmem
    obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hlen
    have hsplit : C.gates = C.gates.take j ++ [gt] ++ C.gates.drop (j + 1) := by
      rw [← take_succ_eq C.gates j hjl, List.take_append_drop]
    set L := List.ofFn x with hL
    set P := wiresFrom (C.gates.take j) L with hP
    have hPlen : P.length = n + j := by
      rw [hP, length_wiresFrom]
      simp [hL, List.length_take, Nat.min_eq_left (le_of_lt hjl)]
    have h1 : wiresFrom [gt] P = P ++ [gt.op.eval (gt.inputs.map fun i => P.getD i false)] := rfl
    have hval_w : cval C x w = gt.op.eval (gt.inputs.map fun i => P.getD i false) := by
      unfold cval
      rw [wires_eq, hsplit, wiresFrom_append, wiresFrom_append]
      rw [h1, getD_wiresFrom _ _ _ (by simp [hPlen]; omega), hwj, ← hPlen, getD_snoc_eq]
    have hrd : ∀ a : ℕ, P.getD a false = rd (cval C) x w a := by
      intro a
      unfold rd
      by_cases ha : a < w
      · simp only [ha, ↓reduceIte]
        have hca : cval C x a = P.getD a false := by
          unfold cval
          rw [wires_eq, hsplit, wiresFrom_append, wiresFrom_append, h1,
            getD_wiresFrom _ _ _ (by simp [hPlen]; omega), List.getD_append _ _ _ _ (by omega)]
        rw [hca]
      · simp only [ha, ↓reduceIte]
        rw [List.getD_eq_default _ _ (by omega)]
    rw [hval_w, hab]
    simp only [List.map_cons, List.map_nil]
    rw [eval_two gt.op hop, hrd, hrd]
    unfold gdesc
    rw [← hj, ← hgt, hab]
    simp
  · intro x w hw
    unfold cval
    rw [wires_eq, List.getD_eq_default]
    rw [length_wiresFrom]
    simp
    omega

end Bridge

end PEqualNP.Outside.L270

theorem PEqualNP.Outside.L_meta_270 :
    ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c hpair hS2 hC hA hB hck hcs
  have hM := PEqualNP.Outside.L270.model_of_circuit (n := n) C hC
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  · have hpos : 0 < n := by
      have h2 := hS2 ⟨0, hm⟩
      by_contra hn
      have hn0 : n = 0 := by omega
      subst hn0
      have : (S ⟨0, hm⟩).card ≤ 0 := by
        have := Finset.card_le_univ (S ⟨0, hm⟩)
        simpa using this
      omega
    have hA' : ∀ i, PEqualNP.Outside.L270.pt (PEqualNP.Outside.L270.cval C) (o i) = S i := by
      intro i
      ext p
      rw [PEqualNP.Outside.L270.mem_pt]
      exact hA i p
    have := PEqualNP.Outside.L270.total_bound C.gates.length (PEqualNP.Outside.L270.gdesc n C.gates)
      (PEqualNP.Outside.L270.cval C) hM S o c k ⟨0, hpos⟩ hpair hA' (fun i x hx hq => hB i x hx hq) hck hcs
    exact this
