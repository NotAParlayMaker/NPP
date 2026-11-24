import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1535

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

def vl {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  value (⟨gates, 0⟩ : Circuit) x w

lemma vl_input {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (w : ℕ) (h : w < n) :
    vl gates x w = x ⟨w, h⟩ :=
  input_value (⟨gates, 0⟩ : Circuit) x ⟨w, h⟩

lemma vl_missing {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : vl gates x w = false :=
  missing_value (⟨gates, 0⟩ : Circuit) x w hw

lemma vl_gate {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (k : ℕ) (g : Gate)
    (hk : gates[k]? = some g) :
    vl gates x (n + k) =
      g.op.eval (g.inputs.map fun r => if r < n + k then vl gates x r else false) := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hk
  have h := gate_value (⟨gates, 0⟩ : Circuit) x (n + k) (by omega)
    (by show n + k < n + gates.length; omega)
  simp only [Nat.add_sub_cancel_left] at h
  exact h

lemma vl_and {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (k : ℕ) (g : Gate)
    (hk : gates[k]? = some g) (hop : g.op = GateOp.and) :
    vl gates x (n + k) = true ↔ ∀ r ∈ g.inputs, r < n + k ∧ vl gates x r = true := by
  rw [vl_gate gates x k g hk, hop]
  simp only [GateOp.eval, List.all_eq_true, id_eq, List.mem_map]
  constructor
  · intro hall r hr
    have := hall _ ⟨r, hr, rfl⟩
    by_cases hrw : r < n + k
    · simpa [hrw] using this
    · simp [hrw] at this
  · rintro hall b ⟨r, hr, rfl⟩
    have := hall r hr
    simp [this.1, this.2]

lemma vl_or {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (k : ℕ) (g : Gate)
    (hk : gates[k]? = some g) (hop : g.op = GateOp.or) :
    vl gates x (n + k) = true ↔ ∃ r ∈ g.inputs, r < n + k ∧ vl gates x r = true := by
  rw [vl_gate gates x k g hk, hop]
  simp only [GateOp.eval, List.any_eq_true, id_eq, List.mem_map]
  constructor
  · rintro ⟨b, ⟨r, hr, rfl⟩, hb⟩
    by_cases hrw : r < n + k
    · exact ⟨r, hr, hrw, by simpa [hrw] using hb⟩
    · simp [hrw] at hb
  · rintro ⟨r, hr, hrw, hv⟩
    exact ⟨_, ⟨r, hr, rfl⟩, by simp [hrw, hv]⟩

lemma vl_mono {n : ℕ} (gates : List Gate)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) :
    ∀ w, vl gates x w = true → vl gates y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hx
    by_cases hn : w < n
    · rw [vl_input gates x w hn] at hx
      rw [vl_input gates y w hn]
      exact hxy _ hx
    · by_cases hw : w < n + gates.length
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < gates.length := by omega
        have hgk : gates[k]? = some gates[k] := List.getElem?_eq_getElem hk
        rcases hg (gates[k]) (List.getElem_mem hk) with hop | hop
        · rw [vl_and gates x k _ hgk hop] at hx
          rw [vl_and gates y k _ hgk hop]
          intro r hr
          exact ⟨(hx r hr).1, ih r (hx r hr).1 (hx r hr).2⟩
        · rw [vl_or gates x k _ hgk hop] at hx
          rw [vl_or gates y k _ hgk hop]
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

def E {n : ℕ} (u : Fin n) : Fin n → Bool := fun v => decide (v = u)

def Yu {n : ℕ} (y : Fin n → Bool) (u : Fin n) : Fin n → Bool := fun v => y v || decide (v = u)

def Good (n : ℕ) (K : ℕ → Prop) (i : ℕ) : Prop := i < n ∨ ∃ k, i = n + k ∧ K k

open Classical in
noncomputable def D {n : ℕ} (gates : List Gate) (G : ℕ → Prop) (T : Finset (Fin n))
    (y : Fin n → Bool) (i : ℕ) : Finset (Fin n) :=
  if G i then Finset.univ.filter
    (fun u => u ∈ T ∧ vl gates y i = false ∧ vl gates (Yu y u) i = true) else ∅

lemma mem_D {n : ℕ} (gates : List Gate) (G : ℕ → Prop) (T : Finset (Fin n))
    (y : Fin n → Bool) (i : ℕ) (u : Fin n) :
    u ∈ D gates G T y i ↔
      G i ∧ u ∈ T ∧ vl gates y i = false ∧ vl gates (Yu y u) i = true := by
  unfold D
  split_ifs with h
  · simp [h]
  · simp [h]

def Core {n m : ℕ} (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ)
    (w0 : Fin m) (bk : ℕ) : Prop :=
  ∀ bK : Set ℕ, (∀ bk0 : ℕ, bk0 < gates.length → out w0 = n + bk0 → (∀ bu0 : Fin n, vl gates (E bu0) (n + bk0) = true → bu0 ∈ S w0) → bk0 ∈ bK) → (∀ bk1 ∈ bK, ∀ (bg1 : Gate) (bk2 : ℕ), gates[bk1]? = some bg1 → n + bk2 ∈ bg1.inputs → bk2 < bk1 → (∀ bu1 : Fin n, vl gates (E bu1) (n + bk2) = true → bu1 ∈ S w0) → bk2 ∈ bK) → bk ∈ bK

lemma per {n : ℕ} (gates : List Gate) (T : Finset (Fin n)) (o : ℕ) (K : ℕ → Prop)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hnorm : ∀ k, k < gates.length →
      (∀ a b : Fin n, vl gates (E a) (n + k) = true → vl gates (E b) (n + k) = true → a = b) →
      ∀ x : Fin n → Bool, vl gates x (n + k) = true →
        ∃ v, vl gates (E v) (n + k) = true ∧ x v = true)
    (hout : ∀ u, vl gates (E u) o = true ↔ u ∈ T)
    (hKsub : ∀ k, K k → ∀ u, vl gates (E u) (n + k) = true → u ∈ T)
    (hKstep : ∀ k1 k2 g, K k1 → gates[k1]? = some g → n + k2 ∈ g.inputs → k2 < k1 →
      (∀ u, vl gates (E u) (n + k2) = true → u ∈ T) → K k2)
    (hKout : ∀ k0, k0 < gates.length → o = n + k0 → K k0)
    (y : Fin n → Bool) (_hy0 : ∀ u ∈ T, y u = false) (hyo : vl gates y o = false)
    (hhit : ∀ bw k g, K k → gates[k]? = some g → g.op = GateOp.and → bw ∈ g.inputs →
      bw < n + k → ¬ (∀ u, vl gates (E u) bw = true → u ∈ T) →
      ∃ u4, vl gates (E u4) bw = true ∧ y u4 = true) :
    ∃ U : Finset ℕ, (∀ i ∈ U, n ≤ i ∧ i < n + gates.length ∧
      (∀ u, vl gates (E u) i = true → u ∈ T) ∧
      ∃ u v : Fin n, u ≠ v ∧ vl gates (E u) i = true ∧ vl gates (E v) i = true) ∧
      T.card ≤ U.card + 1 := by
  classical
  have hmono := vl_mono (n := n) gates (fun g h => (hg g h).1)
  have hEy : ∀ v, y v = true → ∀ t, E v t = true → y t = true := by
    intro v hv t ht
    simp only [E, decide_eq_true_eq] at ht
    rw [ht]; exact hv
  obtain ⟨U, hU⟩ : ∃ U : Finset ℕ, ∀ i, i ∈ U ↔ (i < n + gates.length ∧ n ≤ i ∧ K (i - n) ∧
      ∃ u v : Fin n, u ≠ v ∧ vl gates (E u) i = true ∧ vl gates (E v) i = true) :=
    ⟨(Finset.range (n + gates.length)).filter (fun i => n ≤ i ∧ K (i - n) ∧
      ∃ u v : Fin n, u ≠ v ∧ vl gates (E u) i = true ∧ vl gates (E v) i = true), by
      intro i; rw [Finset.mem_filter, Finset.mem_range]⟩
  have key : ∀ i, (D gates (Good n K) T y i).card ≤ 1 ∨
      (∃ r, r < i ∧ D gates (Good n K) T y i ⊆ D gates (Good n K) T y r) ∨
      (i ∈ U ∧ ∃ R : Finset ℕ, R.card ≤ 2 ∧ (∀ r ∈ R, r < i) ∧
        D gates (Good n K) T y i ⊆ R.biUnion (D gates (Good n K) T y)) := by
    intro i
    by_cases hG : Good n K i
    swap
    · left
      have he : D gates (Good n K) T y i = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro u hu
        exact hG ((mem_D gates (Good n K) T y i u).mp hu).1
      rw [he]; simp
    by_cases hin : i < n
    · left
      rw [Finset.card_le_one]
      intro a ha b hb
      obtain ⟨_, _, ha1, ha2⟩ := (mem_D gates (Good n K) T y i a).mp ha
      obtain ⟨_, _, hb1, hb2⟩ := (mem_D gates (Good n K) T y i b).mp hb
      rw [vl_input gates _ i hin] at ha1 ha2 hb2
      simp only [Yu, ha1, Bool.false_or, decide_eq_true_eq] at ha2 hb2
      exact ha2.symm.trans hb2
    rcases hG with hG | ⟨k, rfl, hK⟩
    · exact absurd hG hin
    by_cases hk : k < gates.length
    swap
    · left
      have he : D gates (Good n K) T y (n + k) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro u hu
        have h := ((mem_D gates (Good n K) T y (n + k) u).mp hu).2.2.2
        rw [vl_missing gates _ _ (by omega)] at h
        exact Bool.noConfusion h
      rw [he]; simp
    by_cases hbig : ∃ u v : Fin n, u ≠ v ∧ vl gates (E u) (n + k) = true ∧ vl gates (E v) (n + k) = true
    swap
    · left
      rw [Finset.card_le_one]
      have huniq : ∀ a b : Fin n, vl gates (E a) (n + k) = true → vl gates (E b) (n + k) = true →
          a = b := by
        intro a b ha hb
        by_contra hne
        exact hbig ⟨a, b, hne, ha, hb⟩
      have hsupp : ∀ a, a ∈ D gates (Good n K) T y (n + k) →
          vl gates (E a) (n + k) = true := by
        intro a ha
        obtain ⟨_, _, ha1, ha2⟩ := (mem_D gates (Good n K) T y (n + k) a).mp ha
        obtain ⟨v, hv1, hv2⟩ := hnorm k hk huniq _ ha2
        have hyv : y v = false := by
          cases hyv : y v with
          | false => rfl
          | true =>
            have h := hmono (E v) y (hEy v hyv) (n + k) hv1
            rw [h] at ha1
            exact Bool.noConfusion ha1
        simp only [Yu, hyv, Bool.false_or, decide_eq_true_eq] at hv2
        rw [← hv2]
        exact hv1
      intro a ha b hb
      exact huniq a b (hsupp a ha) (hsupp b hb)
    right; right
    have hgk : gates[k]? = some gates[k] := List.getElem?_eq_getElem hk
    refine ⟨(hU _).mpr ⟨by omega, by omega, by rwa [Nat.add_sub_cancel_left], hbig⟩, ?_⟩
    refine ⟨(gates[k].inputs.toFinset).filter (fun r => r < n + k), ?_, ?_, ?_⟩
    · calc ((gates[k].inputs.toFinset).filter (fun r => r < n + k)).card
          ≤ gates[k].inputs.toFinset.card := Finset.card_filter_le _ _
        _ ≤ gates[k].inputs.length := List.toFinset_card_le _
        _ ≤ 2 := (hg _ (List.getElem_mem hk)).2
    · intro r hr
      exact (Finset.mem_filter.mp hr).2
    · intro u hu
      obtain ⟨_, huT, hu1, hu2⟩ := (mem_D gates (Good n K) T y (n + k) u).mp hu
      have hex : ∃ r ∈ gates[k].inputs, r < n + k ∧ vl gates y r = false ∧
          vl gates (Yu y u) r = true ∧ (∀ t, vl gates (E t) r = true → t ∈ T) := by
        rcases (hg _ (List.getElem_mem hk)).1 with hop | hop
        · have hall := (vl_and gates (Yu y u) k _ hgk hop).mp hu2
          have hne : ¬ ∀ r ∈ gates[k].inputs, r < n + k ∧ vl gates y r = true := by
            intro h
            rw [(vl_and gates y k _ hgk hop).mpr h] at hu1
            exact Bool.noConfusion hu1
          obtain ⟨r, hr, hrn⟩ : ∃ r ∈ gates[k].inputs, ¬ (r < n + k ∧ vl gates y r = true) := by
            by_contra hcon
            exact hne (fun r hr => by
              by_contra h2
              exact hcon ⟨r, hr, h2⟩)
          have hr1 := (hall r hr).1
          have hyr : vl gates y r = false := by
            cases h : vl gates y r with
            | false => rfl
            | true => exact absurd ⟨hr1, h⟩ hrn
          refine ⟨r, hr, hr1, hyr, (hall r hr).2, ?_⟩
          by_contra hns
          obtain ⟨u4, h41, h42⟩ := hhit r k _ hK hgk hop hr hr1 hns
          have h := hmono (E u4) y (hEy u4 h42) r h41
          rw [h] at hyr
          exact Bool.noConfusion hyr
        · obtain ⟨r, hr, hr1, hr2⟩ := (vl_or gates (Yu y u) k _ hgk hop).mp hu2
          refine ⟨r, hr, hr1, ?_, hr2, ?_⟩
          · cases h : vl gates y r with
            | false => rfl
            | true =>
              rw [(vl_or gates y k _ hgk hop).mpr ⟨r, hr, hr1, h⟩] at hu1
              exact Bool.noConfusion hu1
          · intro t ht
            exact hKsub k hK t ((vl_or gates (E t) k _ hgk hop).mpr ⟨r, hr, hr1, ht⟩)
      obtain ⟨r, hr, hr1, hyr, hur, hsub⟩ := hex
      refine Finset.mem_biUnion.mpr ⟨r, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, hr1⟩,
        (mem_D gates (Good n K) T y r u).mpr ⟨?_, huT, hyr, hur⟩⟩
      by_cases hrn : r < n
      · exact Or.inl hrn
      · have e : n + (r - n) = r := by omega
        refine Or.inr ⟨r - n, e.symm, ?_⟩
        exact hKstep k (r - n) _ hK hgk (by rw [e]; exact hr) (by omega)
          (by rw [e]; exact hsub)
  have hcore := core (D gates (Good n K) T y) U key (n + gates.length)
  refine ⟨U, ?_, ?_⟩
  · intro i hi
    obtain ⟨c1, c2, c3, c4⟩ := (hU i).mp hi
    refine ⟨c2, c1, ?_, c4⟩
    intro u hu
    exact hKsub (i - n) c3 u (by rw [show n + (i - n) = i by omega]; exact hu)
  · by_cases ho : o < n
    · have hc : T.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        have ha' := (hout a).mpr ha
        have hb' := (hout b).mpr hb
        rw [vl_input gates _ o ho] at ha' hb'
        simp only [E, decide_eq_true_eq] at ha' hb'
        exact ha'.symm.trans hb'
      omega
    by_cases ho2 : o < n + gates.length
    swap
    · have he : T = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro u hu
        have h := (hout u).mpr hu
        rw [vl_missing gates _ _ (by omega)] at h
        exact Bool.noConfusion h
      rw [he]; simp
    have hKo : K (o - n) := hKout (o - n) (by omega) (by omega)
    have hsub : T ⊆ ({o} : Finset ℕ).biUnion (D gates (Good n K) T y) := by
      intro u hu
      rw [Finset.singleton_biUnion]
      refine (mem_D gates (Good n K) T y o u).mpr
        ⟨Or.inr ⟨o - n, by omega, hKo⟩, hu, hyo, ?_⟩
      refine hmono (E u) (Yu y u) ?_ o ((hout u).mpr hu)
      intro t ht
      simp only [E, decide_eq_true_eq] at ht
      simp [Yu, ht]
    have b1 := hcore {o} (by
      intro w hw
      rw [Finset.mem_singleton] at hw
      omega)
    have b2 := Finset.card_le_card hsub
    have b3 : (U.filter (fun u => u < n + gates.length)).card ≤ U.card :=
      Finset.card_filter_le _ _
    simp only [Finset.card_singleton] at b1
    omega

end PEqualNP.Outside.L_meta_1535

theorem PEqualNP.Outside.L_meta_1535 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ ak : ℕ, ak < gates.length → (Finset.univ.filter (fun au : Fin n => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun auk : Fin n => decide (auk = au)))).getD (n + ak) false = true)).card ≤ 1 → ∀ ax : Fin n → Bool, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn ax)).getD (n + ak) false = decide (∃ av : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun avk : Fin n => decide (avk = av)))).getD (n + ak) false = true ∧ ax av = true)) → (∀ (w : Fin m) (u : Fin n), (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun uk : Fin n => decide (uk = u)))).getD (out w) false = true ↔ u ∈ S w) → (∀ w0 : Fin m, ∃ y : Fin n → Bool, (∀ u3 ∈ S w0, y u3 = false) ∧ (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn y)).getD (out w0) false = false ∧ ∀ bw : ℕ, (∃ (bk : ℕ) (bg : PEqualNP.CircuitLowerBounds.Gate), (∀ bK : Set ℕ, (∀ bk0 : ℕ, bk0 < gates.length → out w0 = n + bk0 → (∀ bu0 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun bu0k : Fin n => decide (bu0k = bu0)))).getD (n + bk0) false = true → bu0 ∈ S w0) → bk0 ∈ bK) → (∀ bk1 ∈ bK, ∀ (bg1 : PEqualNP.CircuitLowerBounds.Gate) (bk2 : ℕ), gates[bk1]? = some bg1 → n + bk2 ∈ bg1.inputs → bk2 < bk1 → (∀ bu1 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun bu1k : Fin n => decide (bu1k = bu1)))).getD (n + bk2) false = true → bu1 ∈ S w0) → bk2 ∈ bK) → bk ∈ bK) ∧ gates[bk]? = some bg ∧ bg.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ bw ∈ bg.inputs ∧ bw < n + bk ∧ ¬ (∀ bu2 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun bu2k : Fin n => decide (bu2k = bu2)))).getD (bw) false = true → bu2 ∈ S w0)) → ∃ u4 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u4k : Fin n => decide (u4k = u4)))).getD (bw) false = true ∧ y u4 = true) → ∑ w1 : Fin m, (S w1).card ≤ gates.length + (Finset.univ.filter (fun w5 : Fin m => (S w5).Nonempty)).card := by
  intro n m S gates out h1 h2 h3 h4 h5
  have hper : ∀ w : Fin m, ∃ U : Finset ℕ, (∀ i ∈ U, n ≤ i ∧ i < n + gates.length ∧
      (∀ u, PEqualNP.Outside.L_meta_1535.vl gates (PEqualNP.Outside.L_meta_1535.E u) i = true →
        u ∈ S w) ∧
      ∃ u v : Fin n, u ≠ v ∧
        PEqualNP.Outside.L_meta_1535.vl gates (PEqualNP.Outside.L_meta_1535.E u) i = true ∧
        PEqualNP.Outside.L_meta_1535.vl gates (PEqualNP.Outside.L_meta_1535.E v) i = true) ∧
      (S w).card ≤ U.card + 1 := by
    intro w
    obtain ⟨y, hy0, hyo, hhit⟩ := h5 w
    refine PEqualNP.Outside.L_meta_1535.per gates (S w) (out w)
      (PEqualNP.Outside.L_meta_1535.Core S gates out w)
      (fun g hg => h2 g hg) ?_ (h4 w) ?_ ?_ ?_ y hy0 hyo ?_
    · intro k hk huniq x hx
      have h := h3 k hk (Finset.card_le_one.mpr (fun a ha b hb =>
        huniq a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2)) x
      rw [show PEqualNP.Outside.L_meta_1535.vl gates x (n + k) = _ from h] at hx
      exact of_decide_eq_true hx
    · intro k hK
      exact hK {k | ∀ u, PEqualNP.Outside.L_meta_1535.vl gates
        (PEqualNP.Outside.L_meta_1535.E u) (n + k) = true → u ∈ S w}
        (fun bk0 _ _ h => h) (fun bk1 _ bg1 bk2 _ _ _ h => h)
    · intro k1 k2 g hK hg hin hlt hsub bK a b
      exact b k1 (hK bK a b) g k2 hg hin hlt hsub
    · intro k0 hk0 ho bK a _
      exact a k0 hk0 ho (fun u hu => (h4 w u).mp (by rw [ho]; exact hu))
    · intro bw k g hK hg hop hin hlt hns
      exact hhit bw ⟨k, g, hK, hg, hop, hin, hlt, hns⟩
  choose U hU1 hU2 using hper
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
      a ≠ b → Disjoint (U a) (U b) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro i hia hib
    obtain ⟨_, _, hsa, u, v, huv, hu, hv⟩ := hU1 a i hia
    obtain ⟨_, _, hsb, _⟩ := hU1 b i hib
    have hle := h1 a b hab
    rw [Finset.card_le_one] at hle
    exact huv (hle u (Finset.mem_inter.mpr ⟨hsa u hu, hsb u hu⟩) v
      (Finset.mem_inter.mpr ⟨hsa v hv, hsb v hv⟩))
  have hsub : (Finset.univ : Finset (Fin m)).biUnion U ⊆ Finset.Ico n (n + gates.length) := by
    intro i hi
    obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨ha, hb, _⟩ := hU1 w i hw
    exact Finset.mem_Ico.mpr ⟨ha, hb⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj, Nat.card_Ico, Nat.add_sub_cancel_left] at hcard
  have hpt : ∀ w : Fin m, (S w).card ≤ (U w).card + (if (S w).Nonempty then 1 else 0) := by
    intro w
    by_cases hne : (S w).Nonempty
    · rw [if_pos hne]
      exact hU2 w
    · rw [if_neg hne, Finset.not_nonempty_iff_eq_empty.mp hne]
      simp
  calc ∑ w1 : Fin m, (S w1).card
      ≤ ∑ w : Fin m, ((U w).card + (if (S w).Nonempty then 1 else 0)) :=
        Finset.sum_le_sum (fun w _ => hpt w)
    _ = ∑ w : Fin m, (U w).card +
        (Finset.univ.filter (fun w5 : Fin m => (S w5).Nonempty)).card := by
        rw [Finset.sum_add_distrib, Finset.card_filter]
    _ ≤ gates.length + (Finset.univ.filter (fun w5 : Fin m => (S w5).Nonempty)).card :=
        Nat.add_le_add_right hcard _
