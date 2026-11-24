import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1624

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

lemma gate_mono {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or)
    (x y : Fin n → Bool)
    (h : ∀ r ∈ C.gates[k].inputs, r < n + k → value C x r = true → value C y r = true) :
    value C x (n + k) = true → value C y (n + k) = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  have hy := gate_value C y (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx hy
  rw [hx, hy]
  have hr (r : ℕ) (hm : r ∈ C.gates[k].inputs) :
      (if r < n + k then value C x r else false) = true →
      (if r < n + k then value C y r else false) = true := by
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

lemma or_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.or) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma and_value {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  have hw : n + k < n + C.size := by unfold Circuit.size; omega
  have hx := gate_value C x (n + k) (by omega) hw
  simp only [Nat.add_sub_cancel_left] at hx
  rw [hx, hop]
  simp [GateOp.eval]

lemma mono {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (h : ∀ v, x v = true → y v = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using h p
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      exact gate_mono C (w - n) hk (hC _ (List.getElem_mem hk)).1 x y fun r _ hlt => ih r (by omega)
    · simp [missing_value C x w (by unfold Circuit.size; omega)]


def S {n : ℕ} (C : Circuit) (A : Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  A.filter (fun p => value C (fun i : Fin n => decide (i = p)) w = true)

lemma mem_S {n : ℕ} (C : Circuit) (A : Finset (Fin n)) (w : ℕ) (p : Fin n) :
    p ∈ S C A w ↔ p ∈ A ∧ value C (fun i : Fin n => decide (i = p)) w = true := by
  simp [S]

lemma input_S {n : ℕ} (C : Circuit) (A : Finset (Fin n)) (w : ℕ) (hw : w < n)
    (p q : Fin n) (hp : p ∈ S C A w) (hq : q ∈ S C A w) : p = q := by
  rw [mem_S] at hp hq
  have e1 := input_value C (fun i : Fin n => decide (i = p)) ⟨w, hw⟩
  have e2 := input_value C (fun i : Fin n => decide (i = q)) ⟨w, hw⟩
  have f1 : (⟨w, hw⟩ : Fin n) = p := by
    have := e1.symm.trans hp.2
    simpa using this
  have f2 : (⟨w, hw⟩ : Fin n) = q := by
    have := e2.symm.trans hq.2
    simpa using this
  rw [← f1, ← f2]

lemma cover {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (A : Finset (Fin n)) (y : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hZ : value C y (n + k) = false) :
    ∃ R : Finset ℕ, R.card ≤ 2 ∧ (∀ r ∈ R, r < n + k ∧ value C y r = false) ∧
      ∀ p ∈ S C A (n + k), ∃ r ∈ R, p ∈ S C A r := by
  classical
  rcases (hC _ (List.getElem_mem hk)).1 with hop | hop
  · by_cases hne : (S C A (n + k)).Nonempty
    · obtain ⟨p0, hp0⟩ := hne
      have hp0' := (mem_S C A _ p0).mp hp0
      have hall := (and_value C k hk hop _).mp hp0'.2
      have hnot : ¬ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C y r = true := by
        intro h
        have := (and_value C k hk hop y).mpr h
        rw [hZ] at this
        exact Bool.noConfusion this
      push Not at hnot
      obtain ⟨r, hr, hr2⟩ := hnot
      have hrlt := (hall r hr).1
      refine ⟨{r}, by simp, ?_, ?_⟩
      · intro r' hr'
        rw [Finset.mem_singleton] at hr'
        subst hr'
        exact ⟨hrlt, by simpa using hr2 hrlt⟩
      · intro p hp
        have hp' := (mem_S C A _ p).mp hp
        exact ⟨r, Finset.mem_singleton_self r,
          (mem_S C A r p).mpr ⟨hp'.1, ((and_value C k hk hop _).mp hp'.2 r hr).2⟩⟩
    · refine ⟨∅, by simp, by simp, ?_⟩
      intro p hp
      exact absurd ⟨p, hp⟩ hne
  · refine ⟨(C.gates[k].inputs.filter (fun r => decide (r < n + k))).toFinset, ?_, ?_, ?_⟩
    · calc _ ≤ (C.gates[k].inputs.filter (fun r => decide (r < n + k))).length :=
            List.toFinset_card_le _
        _ ≤ C.gates[k].inputs.length := List.length_filter_le _ _
        _ ≤ 2 := (hC _ (List.getElem_mem hk)).2
    · intro r hr
      rw [List.mem_toFinset, List.mem_filter] at hr
      have hlt : r < n + k := by simpa using hr.2
      refine ⟨hlt, ?_⟩
      by_contra hv
      have := (or_value C k hk hop y).mpr ⟨r, hr.1, hlt, by simpa using hv⟩
      rw [hZ] at this
      exact Bool.noConfusion this
    · intro p hp
      have hp' := (mem_S C A _ p).mp hp
      obtain ⟨r, hr, hlt, hv⟩ := (or_value C k hk hop _).mp hp'.2
      exact ⟨r, by rw [List.mem_toFinset, List.mem_filter]; exact ⟨hr, by simpa using hlt⟩,
        (mem_S C A r p).mpr ⟨hp'.1, hv⟩⟩

lemma img_le_two {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (A : Finset (Fin n)) (y : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hZ : value C y (n + k) = false) (lbl : Fin n → ℕ)
    (hinv : ∀ w < n + k, value C y w = false → ∀ p ∈ S C A w, ∀ q ∈ S C A w, lbl p = lbl q) :
    ((S C A (n + k)).image lbl).card ≤ 2 := by
  classical
  obtain ⟨R, hR, hRz, hcov⟩ := cover C hC A y k hk hZ
  have hsub : (S C A (n + k)).image lbl ⊆ R.biUnion (fun r => (S C A r).image lbl) := by
    intro l hl
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨r, hr, hpr⟩ := hcov p hp
    exact Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_image_of_mem lbl hpr⟩
  have hone : ∀ r ∈ R, ((S C A r).image lbl).card ≤ 1 := by
    intro r hr
    rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
    exact hinv r (hRz r hr).1 (hRz r hr).2 p hp q hq
  calc _ ≤ (R.biUnion (fun r => (S C A r).image lbl)).card := Finset.card_le_card hsub
    _ ≤ ∑ r ∈ R, ((S C A r).image lbl).card := Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ R, 1 := Finset.sum_le_sum hone
    _ = R.card := by simp
    _ ≤ 2 := hR

lemma merge {n : ℕ} (T U : Finset (Fin n)) (hU : U ⊆ T) (lbl : Fin n → ℕ) (p0 : Fin n)
    (hp0 : p0 ∈ U) (hM : (U.image lbl).card ≤ 2) :
    (T.image lbl).card ≤
      (T.image (fun p => if lbl p ∈ U.image lbl then lbl p0 else lbl p)).card + 1 := by
  classical
  have h1 : insert (lbl p0) (T.image lbl \ U.image lbl) ⊆
      T.image (fun p => if lbl p ∈ U.image lbl then lbl p0 else lbl p) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · refine Finset.mem_image.mpr ⟨p0, hU hp0, ?_⟩
      simp
    · obtain ⟨hxI, hxM⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hxI
      exact Finset.mem_image.mpr ⟨p, hp, by simp only [hxM, ite_false]⟩
  have h2 : lbl p0 ∉ T.image lbl \ U.image lbl :=
    fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_image_of_mem lbl hp0)
  have h3 := Finset.card_le_card h1
  rw [Finset.card_insert_of_notMem h2] at h3
  have h4 : (T.image lbl).card ≤ (T.image lbl \ U.image lbl).card + (U.image lbl).card :=
    Finset.card_le_card_sdiff_add_card
  omega

abbrev act {n : ℕ} (C : Circuit) (A : Finset (Fin n)) (y : Fin n → Bool) (k : ℕ) : Prop :=
  value C y (n + k) = false ∧ 2 ≤ (S C A (n + k)).card

lemma induct {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (A : Finset (Fin n)) (y : Fin n → Bool) :
    ∀ k, k ≤ C.gates.length → ∃ lbl : Fin n → ℕ,
      A.card ≤ (A.image lbl).card + ((Finset.range k).filter (fun i => act C A y i)).card ∧
      ∀ w < n + k, value C y w = false → ∀ p ∈ S C A w, ∀ q ∈ S C A w, lbl p = lbl q := by
  classical
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun p => (p : ℕ), ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ Fin.val_injective]
      omega
    · intro w hw _ p hp q hq
      rw [input_S C A w (by omega) p q hp hq]
  | succ k ih =>
    intro hk
    obtain ⟨lbl, hcnt, hinv⟩ := ih (by omega)
    have hk' : k < C.gates.length := by omega
    have hnot : k ∉ (Finset.range k).filter (fun i => act C A y i) := by simp
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases ha : act C A y k
    · rw [ite_eq_left ha, Finset.card_insert_of_notMem hnot]
      obtain ⟨hZ, h2⟩ := ha
      obtain ⟨p0, hp0⟩ : (S C A (n + k)).Nonempty := Finset.card_pos.mp (by omega)
      have hM := img_le_two C hC A y k hk' hZ lbl hinv
      have hU : S C A (n + k) ⊆ A := Finset.filter_subset _ _
      have hm := merge A (S C A (n + k)) hU lbl p0 hp0 hM
      refine ⟨fun p => if lbl p ∈ (S C A (n + k)).image lbl then lbl p0 else lbl p,
        by omega, ?_⟩
      intro w hw hZw p hp q hq
      by_cases hwk : w < n + k
      · have := hinv w hwk hZw p hp q hq
        simp only [this]
      · have hw' : w = n + k := by omega
        subst hw'
        have hpm : lbl p ∈ (S C A (n + k)).image lbl := Finset.mem_image_of_mem lbl hp
        have hqm : lbl q ∈ (S C A (n + k)).image lbl := Finset.mem_image_of_mem lbl hq
        simp only [hpm, hqm, ite_true]
    · rw [ite_eq_right ha]
      refine ⟨lbl, hcnt, ?_⟩
      intro w hw hZw p hp q hq
      by_cases hwk : w < n + k
      · exact hinv w hwk hZw p hp q hq
      · have hw' : w = n + k := by omega
        subst hw'
        have hc : (S C A (n + k)).card ≤ 1 := by
          by_contra hc
          exact ha ⟨hZw, by omega⟩
        rw [Finset.card_le_one.mp hc p hp q hq]

lemma per_line {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (A : Finset (Fin n)) (y : Fin n → Bool) (o : ℕ)
    (hA : ∀ p ∈ A, value C (fun i : Fin n => decide (i = p)) o = true)
    (hy : value C y o = false) :
    A.card - 1 ≤ ((Finset.range C.gates.length).filter (fun i => act C A y i)).card := by
  classical
  obtain ⟨lbl, hcnt, hinv⟩ := induct C hC A y C.gates.length le_rfl
  by_cases ho : o < n + C.gates.length
  · have h1 : (A.image lbl).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
      exact hinv o ho hy p ((mem_S C A o p).mpr ⟨hp, hA p hp⟩) q
        ((mem_S C A o q).mpr ⟨hq, hA q hq⟩)
    omega
  · have hA0 : A = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      have := hA p hp
      rw [missing_value C _ o (by unfold Circuit.size; omega)] at this
      exact Bool.noConfusion this
    simp [hA0]

lemma disj {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (L1 L2 A1 : Finset (Fin n)) (hA1 : A1 ⊆ L1) (hI : (L1 ∩ L2).card ≤ 1) (k : ℕ)
    (h1 : act C A1 (fun i => decide (i ∉ L1)) k)
    (h2 : value C (fun i : Fin n => decide (i ∉ L2)) (n + k) = false) : False := by
  classical
  have hsub : S C A1 (n + k) ⊆ L1 ∩ L2 := by
    intro p hp
    rw [mem_S] at hp
    refine Finset.mem_inter.mpr ⟨hA1 hp.1, ?_⟩
    by_contra hpL
    have := mono C hC (fun i : Fin n => decide (i = p)) (fun i => decide (i ∉ L2)) (by
      intro v hv
      have hvp : v = p := of_decide_eq_true hv
      rw [hvp]
      exact decide_eq_true hpL) (n + k) hp.2
    rw [h2] at this
    exact Bool.noConfusion this
  have h3 := Finset.card_le_card hsub
  have h4 := h1.2
  omega

theorem bound (n m : ℕ) (L A : Fin m → Finset (Fin n)) (D : Circuit) (o : Fin m → ℕ)
    (hL : ∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1)
    (hD : PEqualNP.MetaComplexity.Monotone2 D)
    (hAL : ∀ j, A j ⊆ L j)
    (hpt : ∀ (j : Fin m) (p : Fin n), p ∈ A j →
      value D (fun i : Fin n => decide (i = p)) (o j) = true)
    (hco : ∀ j : Fin m, value D (fun i : Fin n => decide (i ∉ L j)) (o j) = false) :
    ∑ j : Fin m, ((A j).card - 1) ≤ D.size := by
  classical
  have hC : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have := hD g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  have hdisj : ∀ i j : Fin m, i ≠ j →
      Disjoint ((Finset.range D.gates.length).filter
        (fun k => act D (A i) (fun v => decide (v ∉ L i)) k))
      ((Finset.range D.gates.length).filter
        (fun k => act D (A j) (fun v => decide (v ∉ L j)) k)) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro k hki hkj
    rw [Finset.mem_filter] at hki hkj
    exact disj D hC (L i) (L j) (A i) (hAL i) (hL i j hij) k hki.2 hkj.2.1
  calc ∑ j : Fin m, ((A j).card - 1)
      ≤ ∑ j : Fin m, ((Finset.range D.gates.length).filter
          (fun k => act D (A j) (fun v => decide (v ∉ L j)) k)).card :=
        Finset.sum_le_sum fun j _ => per_line D hC (A j) _ (o j) (hpt j) (hco j)
    _ = (Finset.univ.biUnion (fun j : Fin m => (Finset.range D.gates.length).filter
          (fun k => act D (A j) (fun v => decide (v ∉ L j)) k))).card :=
        (Finset.card_biUnion (fun i _ j _ hij => hdisj i j hij)).symm
    _ ≤ (Finset.range D.gates.length).card := Finset.card_le_card (by
        intro k hk
        obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hk
        exact (Finset.mem_filter.mp hj).1)
    _ = D.size := by simp [Circuit.size]

end PEqualNP.Outside.L_meta_1624

theorem PEqualNP.Outside.L_meta_1624 : ∀ (n m : ℕ) (L A : Fin m → Finset (Fin n)) (D : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1) → PEqualNP.MetaComplexity.Monotone2 D → PEqualNP.MetaComplexity.NestedCover.ReadsBack n D → (∀ j : Fin m, A j ⊆ L j) → (∀ (j : Fin m) (p : Fin n), p ∈ A j → (D.wires (List.ofFn (fun i : Fin n => decide (i = p)))).getD (o j) false = true) → (∀ j : Fin m, (D.wires (List.ofFn (fun i : Fin n => decide (i ∉ L j)))).getD (o j) false = false) → ∑ j : Fin m, ((A j).card - 1) ≤ D.size := by
  intro n m L A D o hL hD _ hAL hpt hco
  exact PEqualNP.Outside.L_meta_1624.bound n m L A D o hL hD hAL hpt hco
