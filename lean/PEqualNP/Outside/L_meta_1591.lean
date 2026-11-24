import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1591

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

def vl {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (w : ℕ) : Bool :=
  value (⟨gates, 0⟩ : Circuit) x w

lemma vl_input {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (w : ℕ) (h : w < N) :
    vl gates x w = x ⟨w, h⟩ :=
  input_value (⟨gates, 0⟩ : Circuit) x ⟨w, h⟩

lemma vl_missing {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (w : ℕ)
    (hw : N + gates.length ≤ w) : vl gates x w = false :=
  missing_value (⟨gates, 0⟩ : Circuit) x w hw

lemma vl_and {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (w : ℕ) (h13 : N ≤ w)
    (hw : w < N + gates.length) (hop : (gates[w - N]'(by omega)).op = GateOp.and) :
    vl gates x w = true ↔
      ∀ r ∈ (gates[w - N]'(by omega)).inputs, r < w ∧ vl gates x r = true := by
  have h := gate_value (⟨gates, 0⟩ : Circuit) x w h13 hw
  simp only at h
  unfold vl
  rw [h, hop]
  simp only [GateOp.eval, List.all_eq_true, id_eq, List.mem_map]
  constructor
  · intro hall r hr
    have := hall _ ⟨r, hr, rfl⟩
    by_cases hrw : r < w
    · simpa [hrw] using this
    · simp [hrw] at this
  · rintro hall b ⟨r, hr, rfl⟩
    have := hall r hr
    simp [this.1, this.2]

lemma vl_or {N : ℕ} (gates : List Gate) (x : Fin N → Bool) (w : ℕ) (h13 : N ≤ w)
    (hw : w < N + gates.length) (hop : (gates[w - N]'(by omega)).op = GateOp.or) :
    vl gates x w = true ↔
      ∃ r ∈ (gates[w - N]'(by omega)).inputs, r < w ∧ vl gates x r = true := by
  have h := gate_value (⟨gates, 0⟩ : Circuit) x w h13 hw
  simp only at h
  unfold vl
  rw [h, hop]
  simp only [GateOp.eval, List.any_eq_true, id_eq, List.mem_map]
  constructor
  · rintro ⟨b, ⟨r, hr, rfl⟩, hb⟩
    by_cases hrw : r < w
    · exact ⟨r, hr, hrw, by simpa [hrw] using hb⟩
    · simp [hrw] at hb
  · rintro ⟨r, hr, hrw, hv⟩
    exact ⟨_, ⟨r, hr, rfl⟩, by simp [hrw, hv]⟩

lemma vl_mono {N : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin N → Bool) (hxy : ∀ v, x v = true → y v = true) :
    ∀ w, vl gates x w = true → vl gates y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hx
    by_cases h13 : w < N
    · rw [vl_input gates x w h13] at hx
      rw [vl_input gates y w h13]
      exact hxy _ hx
    · by_cases hw : w < N + gates.length
      · have hk : w - N < gates.length := by omega
        rcases hg (gates[w - N]) (List.getElem_mem hk) with hop | hop
        · rw [vl_and gates x w (by omega) hw hop] at hx
          rw [vl_and gates y w (by omega) hw hop]
          intro r hr
          exact ⟨(hx r hr).1, ih r (hx r hr).1 (hx r hr).2⟩
        · rw [vl_or gates x w (by omega) hw hop] at hx
          rw [vl_or gates y w (by omega) hw hop]
          obtain ⟨r, hr, hlt, hv⟩ := hx
          exact ⟨r, hr, hlt, ih r hlt hv⟩
      · rw [vl_missing gates x w (by omega)] at hx
        exact Bool.noConfusion hx

lemma core {α : Type*} [DecidableEq α] (S : ℕ → Finset α) (U : Finset ℕ)
    (h : ∀ w, (S w).card ≤ 1 ∨ (∃ r, r < w ∧ S w ⊆ S r) ∨
      (w ∈ U ∧ ∃ R : Finset ℕ, R.card ≤ 2 ∧ (∀ r ∈ R, r < w) ∧ S w ⊆ R.biUnion S)) :
    ∀ (m : ℕ) (T : Finset ℕ), (∀ w ∈ T, w < m) →
      (T.biUnion S).card ≤ T.card + (U.filter (fun u => u < m)).card := by
  intro m
  induction m with
  | zero =>
    intro T hT
    have hTe : T = ∅ :=
      Finset.eq_empty_of_forall_notMem (fun w hw => absurd (hT w hw) (by omega))
    subst hTe
    simp
  | succ m ih =>
    intro T hT
    have hmono : (U.filter (fun u => u < m)).card ≤ (U.filter (fun u => u < m + 1)).card := by
      apply Finset.card_le_card
      intro u hu
      have hu' := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨hu'.1, by omega⟩
    by_cases hm : m ∈ T
    · have hT0 : ∀ w ∈ T.erase m, w < m := by
        intro w hw
        have h1 := hT w (Finset.mem_of_mem_erase hw)
        have h2 := Finset.ne_of_mem_erase hw
        omega
      have hTc : (T.erase m).card + 1 = T.card := Finset.card_erase_add_one hm
      have hTu : T.biUnion S = S m ∪ (T.erase m).biUnion S := by
        conv_lhs => rw [← Finset.insert_erase hm]
        rw [Finset.biUnion_insert]
      rcases h m with h1 | ⟨r, hr, hsub⟩ | ⟨hmU, R, hRc, hRlt, hsub⟩
      · have h2 := ih (T.erase m) hT0
        have h3 := Finset.card_union_le (S m) ((T.erase m).biUnion S)
        rw [hTu]
        omega
      · have h2 := ih (insert r (T.erase m)) (by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact hr
          · exact hT0 w hw)
        have h3 : T.biUnion S ⊆ (insert r (T.erase m)).biUnion S := by
          rw [hTu]
          intro a ha
          rcases Finset.mem_union.mp ha with ha | ha
          · exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_insert_self _ _, hsub ha⟩
          · obtain ⟨c, hc, hac⟩ := Finset.mem_biUnion.mp ha
            exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_insert_of_mem hc, hac⟩
        have h4 := Finset.card_le_card h3
        have h5 := Finset.card_insert_le r (T.erase m)
        omega
      · have h2 := ih (R ∪ T.erase m) (by
          intro w hw
          rcases Finset.mem_union.mp hw with hw | hw
          · exact hRlt w hw
          · exact hT0 w hw)
        have h3 : T.biUnion S ⊆ (R ∪ T.erase m).biUnion S := by
          rw [hTu]
          intro a ha
          rcases Finset.mem_union.mp ha with ha | ha
          · obtain ⟨c, hc, hac⟩ := Finset.mem_biUnion.mp (hsub ha)
            exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_union_left _ hc, hac⟩
          · obtain ⟨c, hc, hac⟩ := Finset.mem_biUnion.mp ha
            exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_union_right _ hc, hac⟩
        have h4 := Finset.card_le_card h3
        have h5 := Finset.card_union_le R (T.erase m)
        have h6 : (U.filter (fun u => u < m)).card + 1 ≤
            (U.filter (fun u => u < m + 1)).card := by
          have hins : insert m (U.filter (fun u => u < m)) ⊆ U.filter (fun u => u < m + 1) := by
            intro u hu
            rcases Finset.mem_insert.mp hu with rfl | hu
            · exact Finset.mem_filter.mpr ⟨hmU, by omega⟩
            · have hu' := Finset.mem_filter.mp hu
              exact Finset.mem_filter.mpr ⟨hu'.1, by omega⟩
          have h7 := Finset.card_le_card hins
          rw [Finset.card_insert_of_notMem (by simp)] at h7
          exact h7
        omega
    · have h2 := ih T (fun w hw => by
        have h1 := hT w hw
        have h3 : w ≠ m := fun e => hm (e ▸ hw)
        omega)
      omega

def S {N : ℕ} (gates : List Gate) (z : Fin N → Bool) (ws : Fin N → Fin N → Bool)
    (M : Finset (Fin N)) (w : ℕ) : Finset (Fin N) :=
  M.filter (fun p => vl gates z w = false ∧ vl gates (ws p) w = true)

def isOr : GateOp → Bool
  | GateOp.or => true
  | _ => false

lemma isOr_iff (op : GateOp) : isOr op = true ↔ op = GateOp.or := by
  cases op <;> simp [isOr]

def U {N : ℕ} (gates : List Gate) (z : Fin N → Bool) (ws : Fin N → Fin N → Bool)
    (M : Finset (Fin N)) : Finset ℕ :=
  (Finset.Ico N (N + gates.length)).filter (fun w =>
    isOr (gates.getD (w - N) ⟨GateOp.and, []⟩).op = true ∧ 2 ≤ (S gates z ws M w).card)

lemma mem_U {N : ℕ} (gates : List Gate) (z : Fin N → Bool) (ws : Fin N → Fin N → Bool)
    (M : Finset (Fin N)) (w : ℕ) :
    w ∈ U gates z ws M ↔ (N ≤ w ∧ w < N + gates.length) ∧
      (gates.getD (w - N) ⟨GateOp.and, []⟩).op = GateOp.or ∧ 2 ≤ (S gates z ws M w).card := by
  unfold U
  rw [Finset.mem_filter, Finset.mem_Ico, isOr_iff]

lemma local_prop {N : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (z : Fin N → Bool) (ws : Fin N → Fin N → Bool) (M : Finset (Fin N))
    (hin : ∀ v p, z v = false → p ∈ M → ws p v = true → p = v) (w : ℕ) :
    (S gates z ws M w).card ≤ 1 ∨ (∃ r, r < w ∧ S gates z ws M w ⊆ S gates z ws M r) ∨
      (w ∈ U gates z ws M ∧ ∃ R : Finset ℕ, R.card ≤ 2 ∧ (∀ r ∈ R, r < w) ∧
        S gates z ws M w ⊆ R.biUnion (S gates z ws M)) := by
  by_cases hz : vl gates z w = true
  · left
    have he : S gates z ws M w = ∅ := by
      unfold S
      apply Finset.filter_eq_empty_iff.mpr
      intro p _ hp
      rw [hz] at hp
      exact Bool.noConfusion hp.1
    rw [he]
    simp
  · have hz' : vl gates z w = false := by simpa using hz
    by_cases h13 : w < N
    · left
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have ha' := Finset.mem_filter.mp ha
      have hb' := Finset.mem_filter.mp hb
      have hzv : z ⟨w, h13⟩ = false := by
        rw [← vl_input gates z w h13]
        exact hz'
      have e1 := hin ⟨w, h13⟩ a hzv ha'.1 (by
        rw [← vl_input gates (ws a) w h13]
        exact ha'.2.2)
      have e2 := hin ⟨w, h13⟩ b hzv hb'.1 (by
        rw [← vl_input gates (ws b) w h13]
        exact hb'.2.2)
      exact e1.trans e2.symm
    · by_cases hw : w < N + gates.length
      · have hk : w - N < gates.length := by omega
        have hmem : gates[w - N] ∈ gates := List.getElem_mem hk
        rcases (hg _ hmem).1 with hop | hop
        · have hnot : ¬ (∀ r ∈ (gates[w - N]).inputs, r < w ∧ vl gates z r = true) := by
            rw [← vl_and gates z w (by omega) hw hop]
            simp [hz']
          push Not at hnot
          obtain ⟨r, hr, hrn⟩ := hnot
          by_cases hrw : r < w
          · right
            left
            refine ⟨r, hrw, ?_⟩
            intro p hp
            have hp' := Finset.mem_filter.mp hp
            refine Finset.mem_filter.mpr ⟨hp'.1, ?_, ?_⟩
            · have h1 := hrn hrw
              simpa using h1
            · exact ((vl_and gates (ws p) w (by omega) hw hop).mp hp'.2.2 r hr).2
          · left
            have he : S gates z ws M w = ∅ := by
              unfold S
              apply Finset.filter_eq_empty_iff.mpr
              intro p _ hp
              exact hrw ((vl_and gates (ws p) w (by omega) hw hop).mp hp.2 r hr).1
            rw [he]
            simp
        · by_cases hc : (S gates z ws M w).card ≤ 1
          · left
            exact hc
          · right
            right
            refine ⟨?_, ((gates[w - N]).inputs.filter (fun r => r < w)).toFinset, ?_, ?_, ?_⟩
            · rw [mem_U]
              refine ⟨⟨by omega, hw⟩, ?_, by omega⟩
              rw [List.getD_eq_getElem _ _ hk]
              exact hop
            · exact le_trans (List.toFinset_card_le _)
                (le_trans (List.length_filter_le _ _) (hg _ hmem).2)
            · intro r hr
              have h1 := (List.mem_filter.mp (List.mem_toFinset.mp hr)).2
              simpa using h1
            · intro p hp
              have hp' := Finset.mem_filter.mp hp
              obtain ⟨r, hr, hrw, hv⟩ := (vl_or gates (ws p) w (by omega) hw hop).mp hp'.2.2
              refine Finset.mem_biUnion.mpr ⟨r, List.mem_toFinset.mpr
                (List.mem_filter.mpr ⟨hr, by simpa using hrw⟩),
                Finset.mem_filter.mpr ⟨hp'.1, ?_, hv⟩⟩
              by_contra hne
              have ht : vl gates z r = true := by simpa using hne
              have h1 := (vl_or gates z w (by omega) hw hop).mpr ⟨r, hr, hrw, ht⟩
              rw [hz'] at h1
              exact Bool.noConfusion h1
      · left
        have he : S gates z ws M w = ∅ := by
          unfold S
          apply Finset.filter_eq_empty_iff.mpr
          intro p _ hp
          rw [vl_missing gates (ws p) w (by omega)] at hp
          exact Bool.noConfusion hp.2
        rw [he]
        simp

lemma three_le {N : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (z : Fin N → Bool) (ws : Fin N → Fin N → Bool) (M : Finset (Fin N))
    (hin : ∀ v p, z v = false → p ∈ M → ws p v = true → p = v)
    (q : ℕ) (hM : M.card = q + 1) (o : ℕ) (hz : vl gates z o = false)
    (ho : ∀ p ∈ M, vl gates (ws p) o = true) : q ≤ (U gates z ws M).card := by
  have h := core (S gates z ws M) (U gates z ws M) (local_prop gates hg z ws M hin)
    (o + 1) {o} (by simp)
  have hS : S gates z ws M o = M := Finset.filter_true_of_mem (fun p hp => ⟨hz, ho p hp⟩)
  have h2 : ((U gates z ws M).filter (fun u => u < o + 1)).card ≤ (U gates z ws M).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  rw [Finset.singleton_biUnion, hS, hM, Finset.card_singleton] at h
  omega

lemma disj_one {N : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (z : Fin N → Bool) (ws : Fin N → Fin N → Bool) (M M' : Finset (Fin N))
    (z' : Fin N → Bool) (hc : (M ∩ M').card ≤ 1)
    (h : ∀ p ∈ M, p ∉ M' → ∀ v, ws p v = true → z' v = true) (w : ℕ)
    (h2 : 2 ≤ (S gates z ws M w).card) : vl gates z' w = true := by
  have hex : ∃ p ∈ S gates z ws M w, p ∉ M' := by
    by_contra hcon
    push Not at hcon
    have hsub : S gates z ws M w ⊆ M ∩ M' := fun p hp =>
      Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hp).1, hcon p hp⟩
    have h3 := Finset.card_le_card hsub
    omega
  obtain ⟨p, hp, hpM'⟩ := hex
  have hp' := Finset.mem_filter.mp hp
  exact vl_mono gates hg (ws p) z' (h p hp'.1 hpM') w hp'.2.2

def zf {N : ℕ} (M : Finset (Fin N)) : Fin N → Bool := fun v => decide (v ∉ M)

def wf {N : ℕ} (Bp : Fin N → Finset (Fin N)) : Fin N → Fin N → Bool :=
  fun p v => decide (v = p ∨ v ∈ Bp p)

theorem rot_exists (k : ℕ) :
    ∃ r : Fin (k + 3) → Fin (k + 3), Function.Injective r ∧ ∀ a, r a ≠ a ∧ r (r a) ≠ a := by
  have h1 : ((1 : Fin (k + 3)) : ℕ) = 1 := Fin.val_one (k + 1)
  refine ⟨fun a => a + 1, add_left_injective 1, ?_⟩
  intro a
  constructor
  · intro h
    have h2 : a + 1 = a + 0 := h.trans (add_zero a).symm
    have h3 : (1 : Fin (k + 3)) = 0 := add_left_cancel h2
    have h4 := congrArg Fin.val h3
    rw [h1] at h4
    simp at h4
  · intro h
    have h2 : a + (1 + 1) = a + 0 := by
      rw [← add_assoc, add_zero]
      exact h
    have h3 : (1 + 1 : Fin (k + 3)) = 0 := add_left_cancel h2
    have h4 := congrArg Fin.val h3
    rw [Fin.val_add, h1, Nat.mod_eq_of_lt (by omega)] at h4
    simp at h4

theorem sigma_exists {N : ℕ} (T0 : Finset (Fin N)) (k : ℕ) (hc : T0.card = k + 3) :
    ∃ sigma : Fin N → Fin N, (∀ x ∈ T0, sigma x ∈ T0) ∧ Set.InjOn sigma ↑T0 ∧
      (∀ x ∈ T0, sigma x ≠ x ∧ sigma (sigma x) ≠ x) := by
  obtain ⟨r, hri, hr⟩ := rot_exists k
  have e : T0 ≃ Fin (k + 3) := T0.equivFinOfCardEq hc
  have hex : ∃ sigma : Fin N → Fin N, ∀ x (h : x ∈ T0), sigma x = (e.symm (r (e ⟨x, h⟩))).1 :=
    ⟨fun x => if h : x ∈ T0 then (e.symm (r (e ⟨x, h⟩))).1 else x, fun x h => dif_pos h⟩
  obtain ⟨sigma, hs⟩ := hex
  refine ⟨sigma, ?_, ?_, ?_⟩
  · intro x hx
    rw [hs x hx]
    exact (e.symm _).2
  · intro x hx y hy hxy
    have hx' : x ∈ T0 := Finset.mem_coe.mp hx
    have hy' : y ∈ T0 := Finset.mem_coe.mp hy
    rw [hs x hx', hs y hy'] at hxy
    have h1 := hri (e.symm.injective (Subtype.ext hxy))
    have h2 := e.injective h1
    exact congrArg Subtype.val h2
  · intro x hx
    have hsx : sigma x ∈ T0 := by
      rw [hs x hx]
      exact (e.symm _).2
    have e1 : e ⟨sigma x, hsx⟩ = r (e ⟨x, hx⟩) := by
      have h0 : (⟨sigma x, hsx⟩ : T0) = e.symm (r (e ⟨x, hx⟩)) := Subtype.ext (hs x hx)
      rw [h0, Equiv.apply_symm_apply]
    constructor
    · intro h
      have h0 : (⟨sigma x, hsx⟩ : T0) = ⟨x, hx⟩ := Subtype.ext h
      rw [h0] at e1
      exact (hr _).1 e1.symm
    · intro h
      have e2 : sigma (sigma x) = (e.symm (r (e ⟨sigma x, hsx⟩))).1 := hs _ hsx
      rw [e1] at e2
      have h0 : e.symm (r (r (e ⟨x, hx⟩))) = ⟨x, hx⟩ := Subtype.ext (e2.symm.trans h)
      have h1 := congrArg e h0
      rw [Equiv.apply_symm_apply] at h1
      exact (hr _).2 h1

lemma main2 (q N : ℕ) (L : Fin N → Finset (Fin N))
    (hL4 : ∀ t : Fin N, (L t).card = q + 1)
    (hL1 : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (D : (Fin N → Bool) → Prop)
    (hzD : ∀ t : Fin N, D (zf (L t)))
    (gates : List Gate) (o : Fin N → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hev : ∀ (t : Fin N) (x : Fin N → Bool), D x →
      vl gates x (o t) = decide (∃ v ∈ L t, x v = true))
    (Lam : Finset (Fin N)) (B : Fin N → Fin N → Finset (Fin N))
    (hB : ∀ t ∈ Lam, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧ D (wf (B t) p))
    (hcross : ∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' → ¬ ((∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty) ∧
      (∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty)))
    (J : Finset ℕ) (hJ1 : J ⊆ Finset.Ico N (N + gates.length))
    (hJ2 : ∀ w ∈ J, ∀ t ∈ Lam, w ∉ U gates (zf (L t)) (wf (B t)) (L t)) :
    q * Lam.card + J.card ≤ gates.length := by
  classical
  have hgm : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g h => (hg g h).1
  have hLi : ∀ t t', t ≠ t' → (L t ∩ L t').card ≤ 1 := fun t t' h => le_of_eq (hL1 t t' h)
  have hz0 : ∀ t, vl gates (zf (L t)) (o t) = false := by
    intro t
    rw [hev t _ (hzD t)]
    simp [zf]
  have hw1 : ∀ t ∈ Lam, ∀ p ∈ L t, vl gates (wf (B t) p) (o t) = true := by
    intro t ht p hp
    rw [hev t _ (hB t ht p hp).2]
    simp only [decide_eq_true_eq]
    exact ⟨p, hp, by simp [wf]⟩
  have hin : ∀ t ∈ Lam, ∀ v p, zf (L t) v = false → p ∈ L t → wf (B t) p v = true → p = v := by
    intro t ht v p hzv hp hwv
    have hv : v ∈ L t := by simpa [zf] using hzv
    have hwv' : v = p ∨ v ∈ B t p := by simpa [wf] using hwv
    rcases hwv' with h | h
    · exact h.symm
    · exfalso
      have he := (hB t ht p hp).1
      have hmem : v ∈ B t p ∩ L t := Finset.mem_inter.mpr ⟨h, hv⟩
      rw [he] at hmem
      exact absurd hmem (Finset.notMem_empty v)
  have h3 : ∀ t ∈ Lam, q ≤ (U gates (zf (L t)) (wf (B t)) (L t)).card := fun t ht =>
    three_le gates hg _ _ _ (hin t ht) q (hL4 t) (o t) (hz0 t) (hw1 t ht)
  have hone : ∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' → (∀ p ∈ L t \ L t', B t p ∩ L t' = ∅) →
      Disjoint (U gates (zf (L t)) (wf (B t)) (L t))
        (U gates (zf (L t')) (wf (B t')) (L t')) := by
    intro t ht t' ht' hne hb
    rw [Finset.disjoint_left]
    intro w hw hw'
    have h2 := ((mem_U _ _ _ _ _).mp hw).2.2
    have h2' := ((mem_U _ _ _ _ _).mp hw').2.2
    have htrue : vl gates (zf (L t')) w = true := by
      refine disj_one gates hgm (zf (L t)) (wf (B t)) (L t) (L t') (zf (L t'))
        (hLi t t' hne) ?_ w h2
      intro p hp hp' v hv
      have hv' : v = p ∨ v ∈ B t p := by simpa [wf] using hv
      have hvn : v ∉ L t' := by
        rcases hv' with rfl | h
        · exact hp'
        · intro hvl
          have he := hb p (Finset.mem_sdiff.mpr ⟨hp, hp'⟩)
          have hmem : v ∈ B t p ∩ L t' := Finset.mem_inter.mpr ⟨h, hvl⟩
          rw [he] at hmem
          exact absurd hmem (Finset.notMem_empty v)
      simp [zf, hvn]
    obtain ⟨pp, hpp⟩ := Finset.card_pos.mp
      (by omega : 0 < (S gates (zf (L t')) (wf (B t')) (L t') w).card)
    have hf := (Finset.mem_filter.mp hpp).2.1
    rw [htrue] at hf
    exact Bool.noConfusion hf
  have hdisj : ∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' →
      Disjoint (U gates (zf (L t)) (wf (B t)) (L t))
        (U gates (zf (L t')) (wf (B t')) (L t')) := by
    intro t ht t' ht' hne
    by_cases h1 : ∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty
    · have h2 : ¬ ∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty :=
        fun h2 => hcross t ht t' ht' hne ⟨h1, h2⟩
      exact (hone t' ht' t ht hne.symm (fun p hp =>
        Finset.not_nonempty_iff_eq_empty.mp (fun hne' => h2 ⟨p, hp, hne'⟩))).symm
    · exact hone t ht t' ht' hne (fun p hp =>
        Finset.not_nonempty_iff_eq_empty.mp (fun hne' => h1 ⟨p, hp, hne'⟩))
  have hAcard : q * Lam.card ≤
      (Lam.biUnion (fun t => U gates (zf (L t)) (wf (B t)) (L t))).card := by
    rw [Finset.card_biUnion (fun t ht t' ht' hne => hdisj t ht t' ht' hne)]
    have h4 := Finset.card_nsmul_le_sum Lam
      (fun t => (U gates (zf (L t)) (wf (B t)) (L t)).card) q h3
    rw [smul_eq_mul] at h4
    exact le_of_eq_of_le (Nat.mul_comm _ _) h4
  have hAsub : Lam.biUnion (fun t => U gates (zf (L t)) (wf (B t)) (L t)) ⊆
      Finset.Ico N (N + gates.length) := by
    intro w hw
    obtain ⟨t, _, hwt⟩ := Finset.mem_biUnion.mp hw
    exact Finset.mem_Ico.mpr ((mem_U _ _ _ _ _).mp hwt).1
  have hd : Disjoint (Lam.biUnion (fun t => U gates (zf (L t)) (wf (B t)) (L t))) J := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    obtain ⟨t, ht, hwt⟩ := Finset.mem_biUnion.mp hw
    exact hJ2 w hw' t ht hwt
  have hsub : Lam.biUnion (fun t => U gates (zf (L t)) (wf (B t)) (L t)) ∪ J ⊆
      Finset.Ico N (N + gates.length) := Finset.union_subset hAsub hJ1
  have h5 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd, Nat.card_Ico] at h5
  omega

def sg {N : ℕ} : Fin N → Fin N → Bool := fun p v => decide (v = p)

def zr {N : ℕ} (M : Finset (Fin N)) : Fin N → Fin N → Bool := fun r v => decide (v ∉ M ∨ v = r)

def K {N : ℕ} (gates : List Gate) (M : Finset (Fin N)) : Finset ℕ :=
  (Finset.Ico N (N + gates.length)).filter (fun w =>
    isOr (gates.getD (w - N) ⟨GateOp.and, []⟩).op = false ∧ vl gates (zf M) w = false ∧
      ∃ r ∈ M, vl gates (zr M r) w = true)

lemma mem_K {N : ℕ} (gates : List Gate) (M : Finset (Fin N)) (w : ℕ) :
    w ∈ K gates M ↔ (N ≤ w ∧ w < N + gates.length) ∧
      isOr (gates.getD (w - N) ⟨GateOp.and, []⟩).op = false ∧ vl gates (zf M) w = false ∧
      ∃ r ∈ M, vl gates (zr M r) w = true := by
  unfold K
  rw [Finset.mem_filter, Finset.mem_Ico]

lemma child {N : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (M : Finset (Fin N)) (a : ℕ) :
    ∃ c : ℕ, a ∈ K gates M → (c < a ∧ vl gates (zf M) c = false ∧
      ∀ x : Fin N → Bool, vl gates x a = true → vl gates x c = true) := by
  by_cases ha : a ∈ K gates M
  · obtain ⟨⟨h1, h2⟩, hop, hz, r0, hr0, hv⟩ := (mem_K gates M a).mp ha
    have hk : a - N < gates.length := by omega
    have hand : (gates[a - N]).op = GateOp.and := by
      rcases (hg _ (List.getElem_mem hk)).1 with h | h
      · exact h
      · rw [List.getD_eq_getElem _ _ hk, h] at hop
        simp [isOr] at hop
    have hall := (vl_and gates (zr M r0) a h1 h2 hand).mp hv
    have hnot : ¬ (∀ r ∈ (gates[a - N]).inputs, r < a ∧ vl gates (zf M) r = true) := by
      rw [← vl_and gates (zf M) a h1 h2 hand]
      simp [hz]
    push Not at hnot
    obtain ⟨r, hr, hrn⟩ := hnot
    refine ⟨r, fun _ => ⟨(hall r hr).1, ?_, ?_⟩⟩
    · simpa using hrn (hall r hr).1
    · intro x hx
      exact ((vl_and gates x a h1 h2 hand).mp hx r hr).2
  · exact ⟨0, fun h => absurd h ha⟩

lemma rim {N : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (M : Finset (Fin N)) (c : ℕ → ℕ)
    (hc : ∀ a, a ∈ K gates M → (c a < a ∧ vl gates (zf M) (c a) = false ∧
      ∀ x : Fin N → Bool, vl gates x a = true → vl gates x (c a) = true))
    (r : Fin N) (hr : r ∈ M) :
    ∀ w, vl gates (zf M) w = false → vl gates (zr M r) w = true →
      vl gates (sg r) w = true ∨ ∃ a ∈ K gates M, vl gates (sg r) (c a) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hz hv
    by_cases h13 : w < N
    · left
      rw [vl_input gates (zf M) w h13] at hz
      rw [vl_input gates (zr M r) w h13] at hv
      rw [vl_input gates (sg r) w h13]
      have hz' : (⟨w, h13⟩ : Fin N) ∈ M := by simpa [zf] using hz
      have hv' : (⟨w, h13⟩ : Fin N) ∉ M ∨ (⟨w, h13⟩ : Fin N) = r := by simpa [zr] using hv
      rcases hv' with h | h
      · exact absurd hz' h
      · simp [sg, h]
    · by_cases hw : w < N + gates.length
      · have hk : w - N < gates.length := by omega
        rcases (hg _ (List.getElem_mem hk)).1 with hop | hop
        · have hK : w ∈ K gates M := by
            rw [mem_K]
            refine ⟨⟨by omega, hw⟩, ?_, hz, r, hr, hv⟩
            rw [List.getD_eq_getElem _ _ hk, hop]
            rfl
          obtain ⟨h1, h2, h3⟩ := hc w hK
          rcases ih (c w) h1 h2 (h3 _ hv) with h | h
          · right
            exact ⟨w, hK, h⟩
          · right
            exact h
        · obtain ⟨r', hr', hlt, hv'⟩ := (vl_or gates (zr M r) w (by omega) hw hop).mp hv
          have hz' : vl gates (zf M) r' = false := by
            by_contra hne
            have ht : vl gates (zf M) r' = true := by simpa using hne
            have h1 := (vl_or gates (zf M) w (by omega) hw hop).mpr ⟨r', hr', hlt, ht⟩
            rw [hz] at h1
            exact Bool.noConfusion h1
          rcases ih r' hlt hz' hv' with h | h
          · left
            exact (vl_or gates (sg r) w (by omega) hw hop).mpr ⟨r', hr', hlt, h⟩
          · right
            exact h
      · rw [vl_missing gates _ w (by omega)] at hv
        exact Bool.noConfusion hv

lemma m0count {N : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (M : Finset (Fin N)) (q : ℕ) (hM : M.card = q + 1) (o : ℕ)
    (hz : vl gates (zf M) o = false) (ho : ∀ r ∈ M, vl gates (zr M r) o = true) :
    q ≤ (K gates M).card + (U gates (zf M) sg M).card := by
  classical
  have hch := fun a => child gates hg M a
  choose c hc using hch
  have hin : ∀ v p : Fin N, zf M v = false → p ∈ M → sg p v = true → p = v := by
    intro v p _ _ h
    have h1 : v = p := by simpa [sg] using h
    exact h1.symm
  have hRt : ∀ w ∈ insert o ((K gates M).image c), w < N + gates.length + o + 1 := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · omega
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
      have h1 := (hc a ha).1
      have h2 := ((mem_K gates M a).mp ha).1.2
      omega
  have hcore := core (S gates (zf M) sg M) (U gates (zf M) sg M)
    (local_prop gates hg (zf M) sg M hin) (N + gates.length + o + 1)
    (insert o ((K gates M).image c)) hRt
  have hsub : M ⊆ (insert o ((K gates M).image c)).biUnion (S gates (zf M) sg M) := by
    intro r hr
    rcases rim gates hg M c hc r hr o hz (ho r hr) with h | ⟨a, ha, h⟩
    · exact Finset.mem_biUnion.mpr ⟨o, Finset.mem_insert_self _ _,
        Finset.mem_filter.mpr ⟨hr, hz, h⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨c a,
        Finset.mem_insert_of_mem (Finset.mem_image_of_mem c ha),
        Finset.mem_filter.mpr ⟨hr, (hc a ha).2.1, h⟩⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_insert_le o ((K gates M).image c)
  have h3 : ((K gates M).image c).card ≤ (K gates M).card := Finset.card_image_le
  have h4 : ((U gates (zf M) sg M).filter (fun u => u < N + gates.length + o + 1)).card ≤
      (U gates (zf M) sg M).card := Finset.card_le_card (Finset.filter_subset _ _)
  omega

def Bz {N : ℕ} (L : Fin N → Finset (Fin N)) (T0 : Finset (Fin N)) (sigma : Fin N → Fin N)
    (x0 : Fin N) : Fin N → Fin N → Finset (Fin N) :=
  fun s p => if p ∈ T0 then ∅ else if (L s ∩ T0).Nonempty then (L s ∩ T0).image sigma else {x0}

lemma Bz_mem {N : ℕ} (L : Fin N → Finset (Fin N)) (T0 : Finset (Fin N)) (sigma : Fin N → Fin N)
    (x0 : Fin N) (s p v : Fin N) (h : v ∈ Bz L T0 sigma x0 s p) :
    (∃ y ∈ L s ∩ T0, sigma y = v) ∨ (¬ (L s ∩ T0).Nonempty ∧ v = x0) := by
  unfold Bz at h
  by_cases h1 : p ∈ T0
  · rw [if_pos h1] at h
    exact absurd h (Finset.notMem_empty v)
  · rw [if_neg h1] at h
    by_cases h2 : (L s ∩ T0).Nonempty
    · rw [if_pos h2] at h
      left
      exact Finset.mem_image.mp h
    · rw [if_neg h2] at h
      right
      exact ⟨h2, Finset.mem_singleton.mp h⟩

lemma Bz_ne {N : ℕ} (L : Fin N → Finset (Fin N)) (T0 : Finset (Fin N)) (sigma : Fin N → Fin N)
    (x0 : Fin N) (s p : Fin N) (h : p ∉ T0) : (Bz L T0 sigma x0 s p).Nonempty := by
  unfold Bz
  rw [if_neg h]
  by_cases h2 : (L s ∩ T0).Nonempty
  · rw [if_pos h2]
    exact h2.image sigma
  · rw [if_neg h2]
    exact Finset.singleton_nonempty x0

lemma final (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N))
    (hm : 3 ≤ m) (hL : ∀ i : Fin N, (L i).card = q + 1)
    (hI : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (hT : T0 ⊆ L i0) (hc : T0.card = m)
    (gates : List Gate) (o : Fin N → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hev : ∀ (t : Fin N) (x : Fin N → Bool),
      ((∃ v ∈ T0, x v = true) ∨ ∀ v : Fin N, v ∉ L i0 → x v = true) →
      vl gates x (o t) = decide (∃ v ∈ L t, x v = true)) :
    N * q ≤ gates.length := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  rw [hk] at hc
  obtain ⟨sigma, hs1, hs2, hs3⟩ := sigma_exists T0 k hc
  obtain ⟨x0, hx0⟩ : ∃ x0, x0 ∈ T0 := Finset.card_pos.mp (by omega)
  have hgm : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g h => (hg g h).1
  have uniq : ∀ s : Fin N, s ≠ i0 → ∀ a b : Fin N, a ∈ L i0 → a ∈ L s → b ∈ L i0 → b ∈ L s →
      a = b := by
    intro s hs a b ha ha' hb hb'
    exact Finset.card_le_one.mp (hI s i0 hs).le a (Finset.mem_inter.mpr ⟨ha', ha⟩) b
      (Finset.mem_inter.mpr ⟨hb', hb⟩)
  have hzD : ∀ t : Fin N, (fun x : Fin N → Bool =>
      (∃ v ∈ T0, x v = true) ∨ ∀ v : Fin N, v ∉ L i0 → x v = true) (zf (L t)) := by
    intro t
    by_cases ht : t = i0
    · right
      intro v hv
      simp [zf, ht, hv]
    · left
      by_contra hcon
      push Not at hcon
      have hsub : T0 ⊆ L t ∩ L i0 := by
        intro v hv
        have h1 := hcon v hv
        have h2 : v ∈ L t := by simpa [zf] using h1
        exact Finset.mem_inter.mpr ⟨h2, hT hv⟩
      have h3 := Finset.card_le_card hsub
      rw [hI t i0 ht, hc] at h3
      omega
  have base : ∀ t : Fin N, t ≠ i0 → ∀ p v : Fin N, v ∈ Bz L T0 sigma x0 t p →
      v ∈ T0 ∧ v ∉ L t ∧ ∀ y ∈ T0, y ∈ L t → sigma y = v := by
    intro t ht p v hv
    rcases Bz_mem L T0 sigma x0 t p v hv with ⟨y0, hy0, hy0v⟩ | ⟨hne, hvx⟩
    · have hy0' := Finset.mem_inter.mp hy0
      have hvT : v ∈ T0 := hy0v ▸ hs1 y0 hy0'.2
      refine ⟨hvT, ?_, ?_⟩
      · intro hvl
        have e := uniq t ht v y0 (hT hvT) hvl (hT hy0'.2) hy0'.1
        rw [e] at hy0v
        exact (hs3 y0 hy0'.2).1 hy0v
      · intro y hy hyl
        have e := uniq t ht y y0 (hT hy) hyl (hT hy0'.2) hy0'.1
        rw [e]
        exact hy0v
    · rw [hvx]
      refine ⟨hx0, ?_, ?_⟩
      · intro hvl
        exact hne ⟨x0, Finset.mem_inter.mpr ⟨hvl, hx0⟩⟩
      · intro y hy hyl
        exact absurd ⟨y, Finset.mem_inter.mpr ⟨hyl, hy⟩⟩ hne
  have hB : ∀ t ∈ Finset.univ.erase i0, ∀ p ∈ L t, Bz L T0 sigma x0 t p ∩ L t = ∅ ∧
      (fun x : Fin N → Bool => (∃ v ∈ T0, x v = true) ∨ ∀ v : Fin N, v ∉ L i0 → x v = true)
        (wf (Bz L T0 sigma x0 t) p) := by
    intro t ht p hp
    have hti : t ≠ i0 := Finset.ne_of_mem_erase ht
    constructor
    · apply Finset.eq_empty_of_forall_notMem
      intro v hv
      have hv' := Finset.mem_inter.mp hv
      exact (base t hti p v hv'.1).2.1 hv'.2
    · left
      by_cases hpT : p ∈ T0
      · exact ⟨p, hpT, by simp [wf]⟩
      · obtain ⟨v, hv⟩ := Bz_ne L T0 sigma x0 t p hpT
        exact ⟨v, (base t hti p v hv).1, by simp [wf, hv]⟩
  have hcross : ∀ t ∈ Finset.univ.erase i0, ∀ t' ∈ Finset.univ.erase i0, t ≠ t' →
      ¬ ((∃ p ∈ L t \ L t', (Bz L T0 sigma x0 t p ∩ L t').Nonempty) ∧
      (∃ p ∈ L t' \ L t, (Bz L T0 sigma x0 t' p ∩ L t).Nonempty)) := by
    rintro t ht t' ht' hne ⟨⟨p, hp, v, hv⟩, ⟨p', hp', v', hv'⟩⟩
    have hti : t ≠ i0 := Finset.ne_of_mem_erase ht
    have hti' : t' ≠ i0 := Finset.ne_of_mem_erase ht'
    rw [Finset.mem_inter] at hv hv'
    obtain ⟨hvT, _, hvs⟩ := base t hti p v hv.1
    obtain ⟨hvT', _, hvs'⟩ := base t' hti' p' v' hv'.1
    have e1 : sigma v = v' := hvs' v hvT hv.2
    have e2 : sigma v' = v := hvs v' hvT' hv'.2
    exact (hs3 v hvT).2 (by rw [e1, e2])
  have hz : vl gates (zf (L i0)) (o i0) = false := by
    rw [hev i0 _ (hzD i0)]
    simp [zf]
  have ho : ∀ r ∈ L i0, vl gates (zr (L i0) r) (o i0) = true := by
    intro r hr
    rw [hev i0 _ (Or.inr (fun v hv => by simp [zr, hv]))]
    simp only [decide_eq_true_eq]
    exact ⟨r, hr, by simp [zr]⟩
  have hcnt := m0count gates hg (L i0) q (hL i0) (o i0) hz ho
  have hKU : Disjoint (K gates (L i0)) (U gates (zf (L i0)) sg (L i0)) := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    have h1 := ((mem_K gates (L i0) w).mp hw).2.1
    have h2 := ((mem_U _ _ _ _ _).mp hw').2.1
    rw [h2] at h1
    simp [isOr] at h1
  have hJ1 : K gates (L i0) ∪ U gates (zf (L i0)) sg (L i0) ⊆
      Finset.Ico N (N + gates.length) := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · exact Finset.mem_Ico.mpr ((mem_K gates (L i0) w).mp h).1
    · exact Finset.mem_Ico.mpr ((mem_U _ _ _ _ _).mp h).1
  have hJ2 : ∀ w ∈ K gates (L i0) ∪ U gates (zf (L i0)) sg (L i0),
      ∀ t ∈ Finset.univ.erase i0,
      w ∉ U gates (zf (L t)) (wf (Bz L T0 sigma x0 t)) (L t) := by
    intro w hw t ht hwt
    have hti : t ≠ i0 := Finset.ne_of_mem_erase ht
    have hU := (mem_U _ _ _ _ _).mp hwt
    rcases Finset.mem_union.mp hw with h | h
    · have h1 := ((mem_K gates (L i0) w).mp h).2.1
      rw [hU.2.1] at h1
      simp [isOr] at h1
    · have h2 := ((mem_U _ _ _ _ _).mp h).2.2
      have htrue : vl gates (zf (L t)) w = true := by
        refine disj_one gates hgm (zf (L i0)) sg (L i0) (L t) (zf (L t))
          (le_of_eq (hI i0 t (Ne.symm hti))) ?_ w h2
        intro p _ hp v hv
        have e : v = p := by simpa [sg] using hv
        simp [zf, e, hp]
      obtain ⟨pp, hpp⟩ := Finset.card_pos.mp
        (by omega : 0 < (S gates (zf (L t)) (wf (Bz L T0 sigma x0 t)) (L t) w).card)
      have hf := (Finset.mem_filter.mp hpp).2.1
      rw [htrue] at hf
      exact Bool.noConfusion hf
  have hmain := main2 q N L hL hI
    (fun x : Fin N → Bool => (∃ v ∈ T0, x v = true) ∨ ∀ v : Fin N, v ∉ L i0 → x v = true)
    hzD gates o hg hev (Finset.univ.erase i0) (Bz L T0 sigma x0) hB hcross
    (K gates (L i0) ∪ U gates (zf (L i0)) sg (L i0)) hJ1 hJ2
  rw [Finset.card_union_of_disjoint hKU, Finset.card_erase_of_mem (Finset.mem_univ i0),
    Finset.card_univ, Fintype.card_fin] at hmain
  have hN1 : 1 ≤ N := by
    have := i0.isLt
    omega
  have e : N * q = q * (N - 1) + q := by
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    ring
  omega


def brun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma bruncons (g : Gate) (gs : List Gate) (x : List Bool) :
    brun (g :: gs) x = brun gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma brunlength (gs : List Gate) (x : List Bool) :
    (brun gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [brun]
  | cons g gs ih => rw [bruncons, ih]; simp; omega

lemma brungetD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (brun gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [bruncons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma brunsplit (gs : List Gate) (x : List Bool) (j : ℕ) :
    brun gs x = brun (gs.drop j) (brun (gs.take j) x) := by
  simpa only [brun, List.foldl_append] using
    congrArg (fun l : List Gate => brun l x) (List.take_append_drop j gs).symm

def bvalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma binputvalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    bvalue C x p = x p := by
  change (brun C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [brungetD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma bmissingvalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : bvalue C x w = false := by
  change (brun C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [brunlength, Circuit.size] using hw)

lemma bgatevalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    bvalue C x w = g.op.eval (g.inputs.map fun r => if r < w then bvalue C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := brun (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, brunlength, Nat.min_eq_left hj.le, j]; omega
  have split : brun C.gates (List.ofFn x) = brun (g :: C.gates.drop (j + 1)) earlier := by
    rw [brunsplit C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then bvalue C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (brun C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (brungetD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (brun C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then bvalue C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [bruncons]
  rw [brungetD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma bgatemono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → bvalue C x r = true → bvalue C y r = true) :
    bvalue C x (n + k) = true → bvalue C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := bgatevalue C x (n + k) (by omega) hw
  have hy := bgatevalue C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then bvalue C x r else false) = true →
      (if r < n + k then bvalue C y r else false) = true := by
    by_cases h' : r < n + k
    · simpa [h'] using h r hm h'
    · simp [h']
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq]
    intro hx b hb
    obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
    exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
  · simp only [hop, GateOp.eval, List.any_eq_true, id_eq]
    intro hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
    exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

lemma borvalue {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.or) (x : Fin n → Bool) :
    bvalue C x (n + k) = true ↔ ∃ r ∈ C.gates[k].inputs, r < n + k ∧ bvalue C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := bgatevalue C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma bandvalue {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and) (x : Fin n → Bool) :
    bvalue C x (n + k) = true ↔ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ bvalue C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := bgatevalue C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma bmono {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (h : ∀ v, x v = true → y v = true) (w : ℕ) :
    bvalue C x w = true → bvalue C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change bvalue C x p = true → bvalue C y p = true
      simpa only [binputvalue] using h p
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      exact bgatemono C (w - n) hk (hC _ (List.getElem_mem hk)).1 x y fun r _ hlt => ih r (by omega)
    · simp [bmissingvalue C x w (by unfold Circuit.size; omega)]

lemma hmono (N : ℕ) (gates : List Gate) (j : Fin gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hone : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (x y : Fin N → Bool) (hxy : ∀ v, x v = true → y v = true) (w : ℕ) (hw : w < N + (j : ℕ)) :
    bvalue ⟨gates, 0⟩ x w = true → bvalue ⟨gates, 0⟩ y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < N
    · let p : Fin N := ⟨w, hn⟩
      change bvalue ⟨gates, 0⟩ x p = true → bvalue ⟨gates, 0⟩ y p = true
      simpa only [binputvalue] using hxy p
    · have hk : w - N < gates.length := by
        have := j.isLt
        omega
      have hwk : w = N + (w - N) := by omega
      rw [hwk]
      have hop : gates[w - N].op = GateOp.and ∨ gates[w - N].op = GateOp.or := by
        rcases (hg _ (List.getElem_mem hk)).1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · have h1 := hone ⟨w - N, hk⟩ h
          have h2 : w - N = (j : ℕ) := congrArg Fin.val h1
          omega
      exact bgatemono (n := N) ⟨gates, 0⟩ (w - N) hk hop x y fun r _ hlt => ih r (by omega) (by omega)

def drun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma druncons (g : Gate) (gs : List Gate) (x : List Bool) :
    drun (g :: gs) x = drun gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma drunappend (A B : List Gate) (x : List Bool) : drun (A ++ B) x = drun B (drun A x) := by
  simp [drun, List.foldl_append]

lemma drunlength (gs : List Gate) (x : List Bool) :
    (drun gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [drun]
  | cons g gs ih => rw [druncons, ih]; simp; omega

lemma drungetD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (drun gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [druncons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma drunsplit (gs : List Gate) (x : List Bool) (j : ℕ) :
    drun gs x = drun (gs.drop j) (drun (gs.take j) x) := by
  simpa only [drun, List.foldl_append] using
    congrArg (fun l : List Gate => drun l x) (List.take_append_drop j gs).symm

def dvalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma dmissingvalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : dvalue C x w = false := by
  change (drun C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [drunlength, Circuit.size] using hw)

lemma dgatevalue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    dvalue C x w = g.op.eval (g.inputs.map fun r => if r < w then dvalue C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := drun (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, drunlength, Nat.min_eq_left hj.le, j]; omega
  have split : drun C.gates (List.ofFn x) = drun (g :: C.gates.drop (j + 1)) earlier := by
    rw [drunsplit C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then dvalue C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (drun C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (drungetD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (drun C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then dvalue C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [druncons]
  rw [drungetD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma dgatevalueP {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) (hk : k < gs.length) :
    dvalue ⟨gs, 0⟩ x (n + k) =
      gs[k].op.eval (gs[k].inputs.map fun r => if r < n + k then dvalue ⟨gs, 0⟩ x r else false) := by
  have h := dgatevalue ⟨gs, 0⟩ x (n + k) (by omega) (by change n + k < n + gs.length; omega)
  simpa only [Nat.add_sub_cancel_left] using h

def isOrD : GateOp → Bool
  | GateOp.or => true
  | _ => false

def isNot : GateOp → Bool
  | GateOp.not => true
  | _ => false

lemma eval_ao (op : GateOp) (l : List Bool) (h : op = GateOp.and ∨ op = GateOp.or) :
    op.eval l = if isOrD op ∈ l then isOrD op else !isOrD op := by
  rcases h with rfl | rfl
  · simp only [GateOp.eval, isOrD]
    induction l with
    | nil => rfl
    | cons b t ih => cases b <;> simp_all
  · simp only [GateOp.eval, isOrD]
    induction l with
    | nil => rfl
    | cons b t ih => cases b <;> simp_all

def fin3 (a : Bool) (op : GateOp) (N : ℕ) : List ℕ → (Bool ⊕ ℕ) × List Gate
  | [] => (Sum.inl (!a), [])
  | [w] => (Sum.inr w, [])
  | w :: w2 :: t => (Sum.inr N, [⟨op, w :: w2 :: t⟩])

def gen (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate) : (Bool ⊕ ℕ) × List Gate :=
  if Sum.inl (isOrD g.op) ∈ g.inputs.map (fun r => ρ.getD r (Sum.inl false)) then
    (Sum.inl (isOrD g.op), [])
  else fin3 (isOrD g.op) g.op N
    ((g.inputs.map (fun r => ρ.getD r (Sum.inl false))).filterMap Sum.getRight?)

def stp (n h k : ℕ) (g : Gate) (s : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  if k < h then (s.1 ++ [Sum.inr (n + s.2.length)], s.2 ++ [g])
  else if k = h then (s.1 ++ [Sum.inl true], s.2)
  else if isNot g.op = true then (s.1 ++ [Sum.inl false], s.2)
  else (s.1 ++ [(gen s.1 (n + s.2.length) g).1], s.2 ++ (gen s.1 (n + s.2.length) g).2)

def SD (n h : ℕ) (gs : List Gate) : ℕ → List (Bool ⊕ ℕ) × List Gate
  | 0 => ((List.range n).map Sum.inr, [])
  | k + 1 => match gs[k]? with
    | none => SD n h gs k
    | some g => stp n h k g (SD n h gs k)

lemma SD_succ (n h : ℕ) (gs : List Gate) (k : ℕ) (hk : k < gs.length) :
    SD n h gs (k + 1) = stp n h k gs[k] (SD n h gs k) := by
  rw [SD]
  simp [hk]

lemma fin3_len (a : Bool) (op : GateOp) (N : ℕ) (l : List ℕ) : (fin3 a op N l).2.length ≤ 1 := by
  rcases l with _ | ⟨w, _ | ⟨w2, t⟩⟩ <;> simp [fin3]

lemma fin3_mem (a : Bool) (op : GateOp) (N : ℕ) (l : List ℕ) :
    ∀ g' ∈ (fin3 a op N l).2, g'.op = op ∧ g'.inputs = l := by
  rcases l with _ | ⟨w, _ | ⟨w2, t⟩⟩ <;> simp [fin3]

lemma fin3_short (a : Bool) (op : GateOp) (N : ℕ) (l : List ℕ) (h : l.length ≤ 1) :
    (fin3 a op N l).2 = [] := by
  rcases l with _ | ⟨w, _ | ⟨w2, t⟩⟩
  · rfl
  · rfl
  · simp at h

lemma gen_len (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate) : (gen ρ N g).2.length ≤ 1 := by
  unfold gen
  split_ifs
  · simp
  · exact fin3_len _ _ _ _

lemma gen_mem (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate) :
    ∀ g' ∈ (gen ρ N g).2, g'.op = g.op ∧ g'.inputs.length ≤ g.inputs.length := by
  unfold gen
  split_ifs
  · simp
  · intro g' hg'
    obtain ⟨h1, h2⟩ := fin3_mem _ _ _ _ g' hg'
    refine ⟨h1, ?_⟩
    rw [h2]
    exact (List.length_filterMap_le _ _).trans (by simp)

lemma filterMap_lt (l : List (Bool ⊕ ℕ)) (b : Bool) (h : Sum.inl b ∈ l) :
    (l.filterMap Sum.getRight?).length + 1 ≤ l.length := by
  induction l with
  | nil => simp at h
  | cons c t ih =>
    rcases List.mem_cons.mp h with h | h
    · subst h
      have := List.length_filterMap_le Sum.getRight? t
      change (t.filterMap Sum.getRight?).length + 1 ≤ t.length + 1
      omega
    · have := ih h
      rcases c with c | c
      · change (t.filterMap Sum.getRight?).length + 1 ≤ t.length + 1
        omega
      · change (t.filterMap Sum.getRight?).length + 1 + 1 ≤ t.length + 1
        omega

lemma gen_reader (ρ : List (Bool ⊕ ℕ)) (N : ℕ) (g : Gate) (hlen : g.inputs.length ≤ 2)
    (r : ℕ) (hr : r ∈ g.inputs) (hρ : ρ.getD r (Sum.inl false) = Sum.inl false) :
    (gen ρ N g).2 = [] := by
  unfold gen
  split_ifs
  · rfl
  · apply fin3_short
    have hm : Sum.inl false ∈ g.inputs.map (fun r => ρ.getD r (Sum.inl false)) :=
      List.mem_map.mpr ⟨r, hr, hρ⟩
    have := filterMap_lt _ false hm
    simp only [List.length_map] at this
    omega

lemma stp_fst (n h k : ℕ) (g : Gate) (s : List (Bool ⊕ ℕ) × List Gate) :
    ∃ d, (stp n h k g s).1 = s.1 ++ [d] := by
  unfold stp
  split_ifs <;> exact ⟨_, rfl⟩

lemma stp_snd (n h k : ℕ) (g : Gate) (s : List (Bool ⊕ ℕ) × List Gate) :
    ∃ e, (stp n h k g s).2 = s.2 ++ e ∧ e.length ≤ 1 := by
  unfold stp
  split_ifs
  · exact ⟨[g], rfl, by simp⟩
  · exact ⟨[], by simp, by simp⟩
  · exact ⟨[], by simp, by simp⟩
  · exact ⟨_, rfl, gen_len _ _ _⟩

lemma SD_len (n h : ℕ) (gs : List Gate) : ∀ k, k ≤ gs.length → (SD n h gs k).1.length = n + k := by
  intro k
  induction k with
  | zero => intro _; simp [SD]
  | succ k ih =>
    intro hk
    rw [SD_succ n h gs k (by omega)]
    obtain ⟨d, hd⟩ := stp_fst n h k gs[k] (SD n h gs k)
    rw [hd, List.length_append, ih (by omega)]
    simp
    omega

lemma SD_low (n h : ℕ) (gs : List Gate) : ∀ k, k ≤ gs.length → k ≤ h →
    (SD n h gs k).2 = gs.take k ∧ (SD n h gs k).1 = (List.range (n + k)).map Sum.inr := by
  intro k
  induction k with
  | zero => intro _ _; simp [SD]
  | succ k ih =>
    intro hk hkh
    obtain ⟨h1, h2⟩ := ih (by omega) (by omega)
    rw [SD_succ n h gs k (by omega)]
    have hlt : k < h := by omega
    unfold stp
    simp only [hlt, ↓reduceIte]
    rw [h1, h2]
    refine ⟨(List.take_succ_eq_append_getElem (by omega)).symm, ?_⟩
    have : (List.take k gs).length = k := by simp; omega
    rw [this, ← Nat.add_assoc, List.range_succ, List.map_append]
    rfl

lemma SD_prefix (n h : ℕ) (gs : List Gate) : ∀ k, k ≤ gs.length → h ≤ k →
    gs.take h <+: (SD n h gs k).2 := by
  intro k
  induction k with
  | zero =>
    intro _ hh
    have : h = 0 := by omega
    subst this
    simp
  | succ k ih =>
    intro hk hh
    by_cases he : h = k + 1
    · rw [he, (SD_low n (k + 1) gs (k + 1) hk le_rfl).1]
    · rw [SD_succ n h gs k (by omega)]
      obtain ⟨e, he2, _⟩ := stp_snd n h k gs[k] (SD n h gs k)
      rw [he2]
      exact (ih (by omega) (by omega)).trans (List.prefix_append _ _)

lemma SD_ops (n h j : ℕ) (gs : List Gate) (hhj : h < j)
    (hops : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (huniq : ∀ i (hi : i < gs.length), gs[i].op = GateOp.not → i = j) :
    ∀ k, k ≤ gs.length → ∀ g' ∈ (SD n h gs k).2,
      (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 := by
  intro k
  induction k with
  | zero => intro _ g' hg'; simp [SD] at hg'
  | succ k ih =>
    intro hk g' hg'
    have hkl : k < gs.length := by omega
    rw [SD_succ n h gs k hkl] at hg'
    have hg := hops gs[k] (List.getElem_mem hkl)
    unfold stp at hg'
    split_ifs at hg' with h1 h2 h3
    · rcases List.mem_append.mp hg' with hm | hm
      · exact ih (by omega) g' hm
      · rw [List.mem_singleton.mp hm]
        refine ⟨?_, hg.2⟩
        rcases hg.1 with ho | ho | ho
        · exact Or.inl ho
        · exact Or.inr ho
        · have := huniq k hkl ho
          omega
    · exact ih (by omega) g' hg'
    · exact ih (by omega) g' hg'
    · rcases List.mem_append.mp hg' with hm | hm
      · exact ih (by omega) g' hm
      · obtain ⟨e1, e2⟩ := gen_mem _ _ _ g' hm
        refine ⟨?_, e2.trans hg.2⟩
        rw [e1]
        rcases hg.1 with ho | ho | ho
        · exact Or.inl ho
        · exact Or.inr ho
        · rw [ho] at h3
          exact absurd rfl h3

lemma SD_j (n h j : ℕ) (gs : List Gate) (hhj : h < j) (hj : j < gs.length)
    (hjn : gs[j].op = GateOp.not) :
    ∀ k, k ≤ gs.length → j < k → (SD n h gs k).1.getD (n + j) (Sum.inl false) = Sum.inl false := by
  intro k
  induction k with
  | zero => intro _ h0; omega
  | succ k ih =>
    intro hk hjk
    have hkl : k < gs.length := by omega
    have hl := SD_len n h gs k (by omega)
    by_cases he : k = j
    · subst he
      rw [SD_succ n h gs k hkl]
      unfold stp
      have h1 : ¬ k < h := by omega
      have h2 : ¬ k = h := by omega
      have h3 : isNot gs[k].op = true := by rw [hjn]; rfl
      simp only [h1, h2, h3, ↓reduceIte]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp [hl]
    · rw [SD_succ n h gs k hkl]
      obtain ⟨d, hd⟩ := stp_fst n h k gs[k] (SD n h gs k)
      rw [hd, List.getD_append _ _ _ _ (by omega)]
      exact ih (by omega) (by omega)

def bad (n h j : ℕ) (gs : List Gate) (i : ℕ) : Bool :=
  decide (i = h ∨ i = j ∨ (j < i ∧ n + j ∈ (gs.getD i ⟨GateOp.and, []⟩).inputs))

lemma SD_bad (n h j : ℕ) (gs : List Gate) (hhj : h < j) (hj : j < gs.length)
    (hjn : gs[j].op = GateOp.not) (hlen : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (k : ℕ) (hk : k < gs.length) (hb : bad n h j gs k = true) :
    (SD n h gs (k + 1)).2 = (SD n h gs k).2 := by
  rw [SD_succ n h gs k hk]
  unfold bad at hb
  simp only [decide_eq_true_eq] at hb
  unfold stp
  rcases hb with hb | hb | ⟨hb1, hb2⟩
  · subst hb
    simp only [lt_irrefl, ↓reduceIte]
  · have h1 : ¬ k < h := by omega
    have h2 : ¬ k = h := by omega
    have h3 : isNot gs[k].op = true := by subst hb; rw [hjn]; rfl
    simp only [h1, h2, h3, ↓reduceIte]
  · have h1 : ¬ k < h := by omega
    have h2 : ¬ k = h := by omega
    simp only [h1, h2, ↓reduceIte]
    split_ifs
    · rfl
    · rw [List.getD_eq_getElem _ _ hk] at hb2
      rw [gen_reader _ _ gs[k] (hlen _ (List.getElem_mem hk)) (n + j) hb2
        (SD_j n h j gs hhj hj hjn k (by omega) hb1)]
      simp

lemma SD_count (n h j : ℕ) (gs : List Gate) (hhj : h < j) (hj : j < gs.length)
    (hjn : gs[j].op = GateOp.not) (hlen : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ k, k ≤ gs.length →
      (SD n h gs k).2.length + ((Finset.range k).filter (fun i => bad n h j gs i = true)).card ≤ k := by
  intro k
  induction k with
  | zero => intro _; simp [SD]
  | succ k ih =>
    intro hk
    have hkl : k < gs.length := by omega
    have ih' := ih (by omega)
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hb : bad n h j gs k = true
    · rw [SD_bad n h j gs hhj hj hjn hlen k hkl hb]
      simp only [hb, ↓reduceIte]
      rw [Finset.card_insert_of_notMem (by simp)]
      omega
    · simp only [hb]
      rw [SD_succ n h gs k hkl]
      obtain ⟨e, he, hel⟩ := stp_snd n h k gs[k] (SD n h gs k)
      rw [he, List.length_append]
      have : (false = true) = False := by simp
      simp only [this, ↓reduceIte]
      omega

def Rp (W' : List Bool) (v : Bool) : Bool ⊕ ℕ → Prop
  | Sum.inl b => v = b
  | Sum.inr w => w < W'.length ∧ W'.getD w false = v

lemma Rp_mono (W' : List Bool) (e : List Gate) (v : Bool) (r : Bool ⊕ ℕ) (hr : Rp W' v r) :
    Rp (drun e W') v r := by
  rcases r with b | w
  · exact hr
  · exact ⟨by rw [drunlength]; exact Nat.lt_add_right _ hr.1, by rw [drungetD _ _ _ hr.1]; exact hr.2⟩

lemma ext (ρ : List (Bool ⊕ ℕ)) (W' : List Bool) (e : List Gate) (d : Bool ⊕ ℕ) (V : ℕ → Bool)
    (N : ℕ) (hlen : ρ.length = N)
    (ih : ∀ i, Rp W' (if i < N then V i else false) (ρ.getD i (Sum.inl false)))
    (hd : Rp (drun e W') (V N) d) (i : ℕ) :
    Rp (drun e W') (if i < N + 1 then V i else false) ((ρ ++ [d]).getD i (Sum.inl false)) := by
  rcases lt_trichotomy i N with hi | hi | hi
  · rw [List.getD_append _ _ _ _ (by omega)]
    have := Rp_mono W' e _ _ (ih i)
    have h1 : i < N + 1 := by omega
    simpa only [hi, h1, ↓reduceIte] using this
  · subst hi
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simpa [hlen] using hd
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    have h1 : ¬ i < N + 1 := by omega
    simp only [h1, ↓reduceIte]
    exact rfl

lemma gen_sem (ρ : List (Bool ⊕ ℕ)) (W' : List Bool) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (vals : ℕ → Bool)
    (hr : ∀ r ∈ g.inputs, Rp W' (vals r) (ρ.getD r (Sum.inl false))) :
    Rp (drun (gen ρ W'.length g).2 W') (g.op.eval (g.inputs.map vals)) (gen ρ W'.length g).1 := by
  rw [eval_ao g.op _ hop]
  unfold gen
  by_cases hin : Sum.inl (isOrD g.op) ∈ g.inputs.map (fun r => ρ.getD r (Sum.inl false))
  · simp only [hin, ↓reduceIte]
    obtain ⟨r, hrm, hre⟩ := List.mem_map.mp hin
    have h1 := hr r hrm
    rw [hre] at h1
    have h2 : vals r = isOrD g.op := h1
    have hmem : isOrD g.op ∈ g.inputs.map vals := List.mem_map.mpr ⟨r, hrm, h2⟩
    simp only [hmem, ↓reduceIte]
    exact rfl
  · simp only [hin, ↓reduceIte]
    have key1 : ∀ w ∈ (g.inputs.map (fun r => ρ.getD r (Sum.inl false))).filterMap Sum.getRight?,
        w < W'.length ∧ ∃ r ∈ g.inputs, W'.getD w false = vals r := by
      intro w hw
      obtain ⟨c, hc, hcw⟩ := List.mem_filterMap.mp hw
      obtain ⟨r, hrm, hre⟩ := List.mem_map.mp hc
      have hc' : c = Sum.inr w := Sum.getRight?_eq_some_iff.mp hcw
      have h1 := hr r hrm
      rw [hre, hc'] at h1
      exact ⟨h1.1, r, hrm, h1.2⟩
    have key2 : isOrD g.op ∈ g.inputs.map vals ↔ isOrD g.op ∈
        ((g.inputs.map (fun r => ρ.getD r (Sum.inl false))).filterMap Sum.getRight?).map
          (fun w => W'.getD w false) := by
      constructor
      · intro hm
        obtain ⟨r, hrm, hre⟩ := List.mem_map.mp hm
        have h1 := hr r hrm
        rcases hc : ρ.getD r (Sum.inl false) with b | w
        · rw [hc] at h1
          have h2 : vals r = b := h1
          exact absurd (List.mem_map.mpr ⟨r, hrm, by rw [hc, ← h2, hre]⟩) hin
        · rw [hc] at h1
          refine List.mem_map.mpr ⟨w, List.mem_filterMap.mpr ⟨Sum.inr w, List.mem_map.mpr ⟨r, hrm, hc⟩, rfl⟩, ?_⟩
          rw [h1.2, hre]
      · intro hm
        obtain ⟨w, hw, hwe⟩ := List.mem_map.mp hm
        obtain ⟨_, r, hrm, hre⟩ := key1 w hw
        exact List.mem_map.mpr ⟨r, hrm, by rw [← hre, hwe]⟩
    simp only [key2]
    generalize (g.inputs.map (fun r => ρ.getD r (Sum.inl false))).filterMap Sum.getRight? = l at key1
    rcases l with _ | ⟨w, _ | ⟨w2, t⟩⟩
    · simp [fin3, Rp]
    · have hw := (key1 w (by simp)).1
      refine ⟨hw, ?_⟩
      change W'.getD w false = _
      simp only [List.map_cons, List.map_nil, List.mem_singleton]
      generalize W'.getD w false = c
      cases isOrD g.op <;> cases c <;> simp
    · refine ⟨by simp [fin3, drun], ?_⟩
      simp only [fin3, drun, List.foldl_cons, List.foldl_nil]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp only [Nat.sub_self, List.getD_cons_zero]
      exact eval_ao g.op _ hop

lemma sem (n h j : ℕ) (gs : List Gate) (x : Fin n → Bool)
    (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (huniq : ∀ i (hi : i < gs.length), gs[i].op = GateOp.not → i = j)
    (hh : dvalue ⟨gs, 0⟩ x (n + h) = true) (hjv : dvalue ⟨gs, 0⟩ x (n + j) = false) :
    ∀ k, k ≤ gs.length → ∀ i, Rp (drun (SD n h gs k).2 (List.ofFn x))
      (if i < n + k then dvalue ⟨gs, 0⟩ x i else false)
      ((SD n h gs k).1.getD i (Sum.inl false)) := by
  intro k
  induction k with
  | zero =>
    intro _ i
    change Rp (List.ofFn x) (if i < n + 0 then dvalue ⟨gs, 0⟩ x i else false)
      (((List.range n).map Sum.inr).getD i (Sum.inl false))
    by_cases hi : i < n
    · have e1 : ((List.range n).map (Sum.inr : ℕ → Bool ⊕ ℕ)).getD i (Sum.inl false) = Sum.inr i := by
        rw [List.getD_eq_getElem _ _ (by simpa using hi)]
        simp
      rw [e1]
      simp only [Nat.add_zero, hi, ↓reduceIte]
      refine ⟨by simpa using hi, ?_⟩
      exact (drungetD gs _ i (by simpa using hi)).symm
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      simp only [Nat.add_zero, hi, ↓reduceIte]
      exact rfl
  | succ k ih =>
    intro hk
    have hkl : k < gs.length := by omega
    have ih' := ih (by omega)
    have hl := SD_len n h gs k (by omega)
    have hWl : (drun (SD n h gs k).2 (List.ofFn x)).length = n + (SD n h gs k).2.length := by
      rw [drunlength]; simp
    have hgv := dgatevalueP gs x k hkl
    rw [SD_succ n h gs k hkl]
    unfold stp
    split_ifs with h1 h2 h3
    · simp only [drunappend, ← Nat.add_assoc]
      apply ext _ _ _ _ (fun i => dvalue ⟨gs, 0⟩ x i) (n + k) hl ih'
      obtain ⟨l1, l2⟩ := SD_low n h gs k (by omega) (by omega)
      have hk2 : (SD n h gs k).2.length = k := by rw [l1]; simp; omega
      refine ⟨by rw [drunlength, hWl]; simp, ?_⟩
      change ((drun (SD n h gs k).2 (List.ofFn x)) ++ [_]).getD _ false = _
      rw [List.getD_append_right _ _ _ _ (by omega), hWl, Nat.sub_self, List.getD_cons_zero, hgv]
      congr 1
      apply List.map_congr_left
      intro r _
      by_cases hr : r < n + k
      · have h4 := ih' r
        have e1 : (SD n h gs k).1.getD r (Sum.inl false) = Sum.inr r := by
          rw [l2, List.getD_eq_getElem _ _ (by simpa using hr)]
          simp
        rw [e1] at h4
        simp only [hr, ↓reduceIte] at h4 ⊢
        exact h4.2
      · simp only [hr, ↓reduceIte]
        exact List.getD_eq_default _ _ (by omega)
    · simp only [← Nat.add_assoc]
      have := ext _ _ [] (Sum.inl true) (fun i => dvalue ⟨gs, 0⟩ x i) (n + k) hl ih'
        (by subst h2; exact hh)
      exact this
    · simp only [← Nat.add_assoc]
      have hkj : k = j := by
        apply huniq k hkl
        rcases hops gs[k] (List.getElem_mem hkl) with ho | ho | ho
        · rw [ho] at h3; exact absurd h3 (by simp [isNot])
        · rw [ho] at h3; exact absurd h3 (by simp [isNot])
        · exact ho
      have := ext _ _ [] (Sum.inl false) (fun i => dvalue ⟨gs, 0⟩ x i) (n + k) hl ih'
        (by subst hkj; exact hjv)
      exact this
    · simp only [drunappend, ← Nat.add_assoc]
      apply ext _ _ _ _ (fun i => dvalue ⟨gs, 0⟩ x i) (n + k) hl ih'
      have hop : gs[k].op = GateOp.and ∨ gs[k].op = GateOp.or := by
        rcases hops gs[k] (List.getElem_mem hkl) with ho | ho | ho
        · exact Or.inl ho
        · exact Or.inr ho
        · rw [ho] at h3; exact absurd rfl h3
      change Rp _ (dvalue ⟨gs, 0⟩ x (n + k)) _
      rw [hgv, ← hWl]
      exact gen_sem _ _ gs[k] hop _ (fun r _ => ih' r)

lemma dmain : ∀ (n m : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (n + (h : ℕ)) :: r) →
    (∀ w : Fin m, ∃ x y : Fin n → Bool,
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn x) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn y) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn y) = false) →
    ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (out' : Fin m → ℕ),
      (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates.take (h : ℕ) <+: gates' ∧
      gates'.length + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 2
        ≤ gates.length ∧
      ∀ (w : Fin m) (x : Fin n → Bool),
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn x) = true →
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', out' w⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) := by
  intro n m gates out j h hops hj huniq hhj hin hsep
  have hjl : (j : ℕ) < gates.length := j.2
  have hhj' : (h : ℕ) < (j : ℕ) := hhj
  have hjn : gates[(j : ℕ)].op = GateOp.not := hj
  have huniq' : ∀ i (hi : i < gates.length), gates[i].op = GateOp.not → i = (j : ℕ) :=
    fun i hi ho => congrArg Fin.val (huniq ⟨i, hi⟩ ho)
  have hops1 : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not :=
    fun g hg => (hops g hg).1
  have hlen : ∀ g ∈ gates, g.inputs.length ≤ 2 := fun g hg => (hops g hg).2
  have hjv : ∀ x : Fin n → Bool, dvalue ⟨gates, 0⟩ x (n + (h : ℕ)) = true →
      dvalue ⟨gates, 0⟩ x (n + (j : ℕ)) = false := by
    intro x hx
    obtain ⟨r, hr⟩ := hin
    have hr' : gates[(j : ℕ)].inputs = (n + (h : ℕ)) :: r := hr
    rw [dgatevalueP gates x j hjl, hjn, hr']
    have : n + (h : ℕ) < n + (j : ℕ) := by omega
    simp [GateOp.eval, this, hx]
  have hsem := fun (x : Fin n → Bool) (hx : dvalue ⟨gates, 0⟩ x (n + (h : ℕ)) = true) =>
    sem n h j gates x hops1 huniq' hx (hjv x hx) gates.length le_rfl
  have hSl := SD_len n h gates gates.length le_rfl
  refine ⟨(SD n h gates gates.length).2,
    fun w => ((SD n h gates gates.length).1.getD (out w) (Sum.inl false)).elim (fun _ => 0) id,
    SD_ops n h j gates hhj' hops huniq' gates.length le_rfl,
    SD_prefix n h gates gates.length le_rfl (by omega), ?_, ?_⟩
  · have hc := SD_count n h j gates hhj' hjl hjn hlen gates.length le_rfl
    have hsub : insert (h : ℕ) (insert (j : ℕ)
        ((Finset.univ.filter (fun i : Fin gates.length =>
          j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).image (fun i : Fin gates.length => (i : ℕ)))) ⊆
        (Finset.range gates.length).filter (fun i => bad n h j gates i = true) := by
      intro i hi
      rw [Finset.mem_filter, Finset.mem_range]
      unfold bad
      simp only [decide_eq_true_eq]
      rcases Finset.mem_insert.mp hi with hi | hi
      · exact ⟨by omega, Or.inl hi⟩
      rcases Finset.mem_insert.mp hi with hi | hi
      · exact ⟨by omega, Or.inr (Or.inl hi)⟩
      obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨_, a, b⟩ := Finset.mem_filter.mp hi'
      refine ⟨i'.2, Or.inr (Or.inr ⟨a, ?_⟩)⟩
      rw [List.getD_eq_getElem _ _ i'.2]
      exact b
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_image_of_injective _ Fin.val_injective] at hcard
    · omega
    · intro hm
      obtain ⟨i', hi', he⟩ := Finset.mem_image.mp hm
      have := (Finset.mem_filter.mp hi').2.1
      have : (j : ℕ) < (i' : ℕ) := this
      omega
    · intro hm
      rcases Finset.mem_insert.mp hm with hm | hm
      · omega
      · obtain ⟨i', hi', he⟩ := Finset.mem_image.mp hm
        have := (Finset.mem_filter.mp hi').2.1
        have : (j : ℕ) < (i' : ℕ) := this
        omega
  · intro w x hx
    have hx' : dvalue ⟨gates, 0⟩ x (n + (h : ℕ)) = true := hx
    obtain ⟨x0, y0, hx0, hy0, ox, oy⟩ := hsep w
    have ox' : dvalue ⟨gates, 0⟩ x0 (out w) = true := ox
    have oy' : dvalue ⟨gates, 0⟩ y0 (out w) = false := oy
    have a1 := hsem x0 hx0 (out w)
    have a2 := hsem y0 hy0 (out w)
    have a3 := hsem x hx' (out w)
    change (drun (SD n h gates gates.length).2 (List.ofFn x)).getD (Sum.elim (fun _ => 0) id ((SD n h gates gates.length).1.getD (out w) (Sum.inl false))) false = dvalue ⟨gates, 0⟩ x (out w)
    rcases hc : (SD n h gates gates.length).1.getD (out w) (Sum.inl false) with b | w'
    · rw [hc] at a1 a2
      exfalso
      by_cases hlt : out w < n + gates.length
      · simp only [hlt, ↓reduceIte] at a1 a2
        have e1 : dvalue ⟨gates, 0⟩ x0 (out w) = b := a1
        have e2 : dvalue ⟨gates, 0⟩ y0 (out w) = b := a2
        rw [ox'] at e1
        rw [oy'] at e2
        rw [← e1] at e2
        exact Bool.noConfusion e2
      · rw [dmissingvalue _ x0 (out w) (by change n + gates.length ≤ _; omega)] at ox'
        exact Bool.noConfusion ox'
    · rw [hc] at a3
      by_cases hlt : out w < n + gates.length
      · simp only [hlt, ↓reduceIte] at a3
        exact a3.2
      · simp only [hlt, ↓reduceIte] at a3
        rw [dmissingvalue _ x (out w) (by change n + gates.length ≤ _; omega)]
        exact a3.2


lemma core3 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = 3 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (t : Fin N) (x : Fin N → Bool), ((∃ v ∈ T0, x v = true) ∨ ∀ v : Fin N, v ∉ L i0 → x v = true) →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    N * q ≤ gates.length := by
  intro q N L i0 T0 _ _ hL hI _ hT hc gates o hg hev
  exact PEqualNP.Outside.L_meta_1591.final q 3 N L i0 T0 le_rfl hL hI hT hc gates o hg hev

lemma m91 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = 3 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = true →
    (∀ a ∈ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v = a))) = true) →
    N * q + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ N + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length := by
  intro q N L i0 T0 hq3 hN hcard hint hjoin hT0 hT0c gates o j h hg hjop hone hhj hjin hout hco hpts
  classical
  have hoff : ∀ t : Fin N, t ≠ i0 → ∃ a ∈ T0, a ∉ L t := by
    intro t ht
    by_contra hc
    have hsub : T0 ⊆ L t ∩ L i0 := fun a ha =>
      Finset.mem_inter.mpr ⟨by_contra (fun hn => hc ⟨a, ha, hn⟩), hT0 ha⟩
    have hle := Finset.card_le_card hsub
    rw [hint t i0 ht, hT0c] at hle
    omega
  have hlt : N + (h : ℕ) < N + (j : ℕ) := by
    have : (h : ℕ) < (j : ℕ) := hhj
    omega
  obtain ⟨a0, ha0⟩ : T0.Nonempty := Finset.card_pos.mp (by omega)
  have htrue : PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun _ : Fin N => true)) = true :=
    hmono N gates j hg hone (fun v : Fin N => decide (v = a0)) (fun _ : Fin N => true) (fun v _ => rfl) _ hlt (hpts a0 ha0)
  have hy : ∀ t : Fin N, ∃ y : Fin N → Bool,
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn y) = true ∧ ∀ v ∈ L t, y v = false := by
    intro t
    by_cases ht : t = i0
    · refine ⟨fun v : Fin N => decide (v ∉ L i0), hco, fun v hv => decide_eq_false (not_not.mpr ?_)⟩
      rw [← ht]
      exact hv
    · obtain ⟨a, ha, hat⟩ := hoff t ht
      refine ⟨fun v : Fin N => decide (v = a), hpts a ha, fun v hv => decide_eq_false (fun e => hat ?_)⟩
      rw [← e]
      exact hv
  obtain ⟨gates', out', hg', hpre, hlen, hagree⟩ := dmain N N gates o j h hg hjop hone hhj hjin (by
    intro w
    obtain ⟨y, hy1, hy2⟩ := hy w
    refine ⟨fun _ : Fin N => true, y, htrue, hy1, ?_, ?_⟩
    · rw [hout]
      obtain ⟨u, hu⟩ : (L w).Nonempty := Finset.card_pos.mp (by
        rw [hcard]
        omega)
      exact decide_eq_true ⟨u, hu, rfl⟩
    · rw [hout]
      refine decide_eq_false ?_
      rintro ⟨v, hv, hh⟩
      rw [hy2 v hv] at hh
      exact Bool.false_ne_true hh)
  have key := core3 q N L i0 T0 hq3 hN hcard hint hjoin hT0 hT0c gates' out' hg' (fun t x hx => (hagree t x (by
    rcases hx with ⟨a, ha, hxa⟩ | hs
    · refine hmono N gates j hg hone (fun v : Fin N => decide (v = a)) x (fun v hv => ?_) _ hlt (hpts a ha)
      rw [of_decide_eq_true hv]
      exact hxa
    · exact hmono N gates j hg hone (fun v : Fin N => decide (v ∉ L i0)) x
        (fun v hv => hs v (of_decide_eq_true hv)) _ hlt hco)).trans (hout t x))
  omega

end PEqualNP.Outside.L_meta_1591

theorem PEqualNP.Outside.L_meta_1591 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = 3 →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = true →
    (∀ a ∈ T0, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v = a))) = true) →
    N * q + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ N + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length :=
  PEqualNP.Outside.L_meta_1591.m91
