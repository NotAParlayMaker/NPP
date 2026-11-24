import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1544

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

lemma main (q N : ℕ) (L : Fin N → Finset (Fin N)) (hq : 2 ≤ q)
    (hL4 : ∀ t : Fin N, (L t).card = q + 1)
    (hL1 : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (D : (Fin N → Bool) → Prop)
    (hup : ∀ x y : Fin N → Bool, D x → (∀ v : Fin N, x v = true → y v = true) → D y)
    (hzD : ∀ t : Fin N, D (zf (L t)))
    (gates : List Gate) (o : Fin N → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hev : ∀ (t : Fin N) (x : Fin N → Bool), D x →
      vl gates x (o t) = decide (∃ v ∈ L t, x v = true))
    (Lam : Finset (Fin N)) (B : Fin N → Fin N → Finset (Fin N))
    (hB : ∀ t ∈ Lam, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧ D (wf (B t) p))
    (hcross : ∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' → ¬ ((∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty) ∧
      (∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty)))
    (I : Finset (Fin gates.length)) (hI : ∀ g ∈ I, (gates.get g).op = GateOp.and) :
    q * Lam.card + max (N - Lam.card) I.card ≤ gates.length := by
  classical
  have hgm : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g h => (hg g h).1
  have hLi : ∀ t t', t ≠ t' → (L t ∩ L t').card ≤ 1 := fun t t' h => le_of_eq (hL1 t t' h)
  have hz0 : ∀ t, vl gates (zf (L t)) (o t) = false := by
    intro t
    rw [hev t _ (hzD t)]
    simp [zf]
  have hz1 : ∀ t s, t ≠ s → vl gates (zf (L s)) (o t) = true := by
    intro t s hts
    rw [hev t _ (hzD s)]
    have hex : ∃ v ∈ L t, v ∉ L s := by
      by_contra hcon
      push Not at hcon
      have hsub : L t ⊆ L t ∩ L s := fun v hv => Finset.mem_inter.mpr ⟨hv, hcon v hv⟩
      have h1 := Finset.card_le_card hsub
      have h2 := hL4 t
      have h3 := hLi t s hts
      omega
    obtain ⟨v, hv, hvs⟩ := hex
    simp only [decide_eq_true_eq]
    exact ⟨v, hv, by simp [zf, hvs]⟩
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
  have hIpart : (Lam.biUnion (fun t => U gates (zf (L t)) (wf (B t)) (L t))).card + I.card ≤
      gates.length := by
    have hinj : Function.Injective (fun g : Fin gates.length => N + g.val) := by
      intro a b hab
      apply Fin.ext
      have hab' : N + a.val = N + b.val := hab
      omega
    have hIc : (I.image (fun g : Fin gates.length => N + g.val)).card = I.card :=
      Finset.card_image_of_injective _ hinj
    have hd : Disjoint (Lam.biUnion (fun t => U gates (zf (L t)) (wf (B t)) (L t)))
        (I.image (fun g : Fin gates.length => N + g.val)) := by
      rw [Finset.disjoint_left]
      intro w hw hw'
      obtain ⟨g, hgI, rfl⟩ := Finset.mem_image.mp hw'
      obtain ⟨t, _, hwt⟩ := Finset.mem_biUnion.mp hw
      have hor := ((mem_U _ _ _ _ _).mp hwt).2.1
      have hand := hI g hgI
      rw [Nat.add_sub_cancel_left, List.getD_eq_getElem _ _ g.isLt] at hor
      rw [List.get_eq_getElem] at hand
      rw [hand] at hor
      exact GateOp.noConfusion hor
    have hsub : Lam.biUnion (fun t => U gates (zf (L t)) (wf (B t)) (L t)) ∪
        I.image (fun g : Fin gates.length => N + g.val) ⊆
        Finset.Ico N (N + gates.length) := by
      apply Finset.union_subset hAsub
      intro w hw
      obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hw
      have hlt := g.isLt
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    have h5 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd, hIc, Nat.card_Ico] at h5
    omega
  have hrange : ∀ t, N ≤ o t ∧ o t < N + gates.length := by
    intro t
    constructor
    · by_contra hlt
      have h13 : o t < N := by omega
      have hzv := hz0 t
      rw [vl_input gates _ (o t) h13] at hzv
      have hmem : (⟨o t, h13⟩ : Fin N) ∈ L t := by simpa [zf] using hzv
      have hxD : D (fun v : Fin N => decide (v ≠ ⟨o t, h13⟩)) := by
        refine hup (zf (L t)) _ (hzD t) ?_
        intro v hv
        have hvn : v ∉ L t := by simpa [zf] using hv
        simp only [decide_eq_true_eq]
        intro e
        exact hvn (e ▸ hmem)
      have hxv := hev t _ hxD
      rw [vl_input gates _ (o t) h13] at hxv
      have hex : ∃ v ∈ L t, v ≠ (⟨o t, h13⟩ : Fin N) := by
        by_contra hcon
        push Not at hcon
        have hsub : L t ⊆ {(⟨o t, h13⟩ : Fin N)} := fun v hv =>
          Finset.mem_singleton.mpr (hcon v hv)
        have h1 := Finset.card_le_card hsub
        have h2 := hL4 t
        rw [Finset.card_singleton] at h1
        omega
      obtain ⟨v, hv, hvne⟩ := hex
      have hT : decide (∃ v ∈ L t, (fun v : Fin N => decide (v ≠ ⟨o t, h13⟩)) v = true) = true := by
        simp only [decide_eq_true_eq]
        exact ⟨v, hv, hvne⟩
      rw [hT] at hxv
      simp at hxv
    · by_contra hge
      have hxD : D (fun _ : Fin N => true) := hup (zf (L t)) _ (hzD t) (fun v _ => rfl)
      have hxv := hev t _ hxD
      rw [vl_missing gates _ (o t) (by omega)] at hxv
      obtain ⟨v, hv⟩ := Finset.card_pos.mp (by rw [hL4 t]; omega : 0 < (L t).card)
      have hT : decide (∃ v ∈ L t, (fun _ : Fin N => true) v = true) = true := by
        simp only [decide_eq_true_eq]
        exact ⟨v, hv, by simp⟩
      rw [hT] at hxv
      exact Bool.noConfusion hxv
  have hoinj : Function.Injective o := by
    intro t s hts
    by_contra hne
    have h1 := hz1 t s hne
    have h0 := hz0 s
    rw [hts, h0] at h1
    exact Bool.noConfusion h1
  have hOpart : (Lam.biUnion (fun t => U gates (zf (L t)) (wf (B t)) (L t))).card +
      (N - Lam.card) ≤ gates.length := by
    have hOc : (Lamᶜ.image o).card = N - Lam.card := by
      rw [Finset.card_image_of_injective _ hoinj, Finset.card_compl, Fintype.card_fin]
    have hd : Disjoint (Lam.biUnion (fun t => U gates (zf (L t)) (wf (B t)) (L t)))
        (Lamᶜ.image o) := by
      rw [Finset.disjoint_left]
      intro w hw hw'
      obtain ⟨t, htc, rfl⟩ := Finset.mem_image.mp hw'
      obtain ⟨s, hs, hws⟩ := Finset.mem_biUnion.mp hw
      have hts : t ≠ s := fun e => (Finset.mem_compl.mp htc) (e ▸ hs)
      have h2 := ((mem_U _ _ _ _ _).mp hws).2.2
      obtain ⟨pp, hpp⟩ := Finset.card_pos.mp
        (by omega : 0 < (S gates (zf (L s)) (wf (B s)) (L s) (o t)).card)
      have hf := (Finset.mem_filter.mp hpp).2.1
      rw [hz1 t s hts] at hf
      exact Bool.noConfusion hf
    have hsub : Lam.biUnion (fun t => U gates (zf (L t)) (wf (B t)) (L t)) ∪ Lamᶜ.image o ⊆
        Finset.Ico N (N + gates.length) := by
      apply Finset.union_subset hAsub
      intro w hw
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_Ico.mpr (hrange t)
    have h5 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd, hOc, Nat.card_Ico] at h5
    omega
  rcases le_total (N - Lam.card) I.card with h | h
  · rw [max_eq_right h]
    omega
  · rw [max_eq_left h]
    omega

end PEqualNP.Outside.L_meta_1544

theorem PEqualNP.Outside.L_meta_1544 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    ∀ D : (Fin N → Bool) → Prop,
    (∀ x y : Fin N → Bool, D x → (∀ v : Fin N, x v = true → y v = true) → D y) →
    (∀ t : Fin N, D (fun v : Fin N => decide (v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (t : Fin N) (x : Fin N → Bool), D x → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    ∀ (Lam : Finset (Fin N)) (B : Fin N → Fin N → Finset (Fin N)),
    (∀ t ∈ Lam, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧ D (fun v : Fin N => decide (v = p ∨ v ∈ B t p))) →
    (∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' → ¬ ((∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty) ∧ (∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty))) →
    ∀ I : Finset (Fin gates.length), (∀ g ∈ I, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      q * Lam.card + max (N - Lam.card) I.card ≤ gates.length := by
  intro q N L hq _ hL4 hL1 _ D hup hco gates o hg hcorr Lam B hB hcross I hI
  exact PEqualNP.Outside.L_meta_1544.main q N L hq hL4 hL1 D hup hco gates o hg hcorr Lam B hB hcross I hI
