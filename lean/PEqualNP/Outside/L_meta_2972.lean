import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2972

open PEqualNP.CircuitLowerBounds

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

lemma merge_count {τ : Type*} [DecidableEq τ] (f : ℕ → Finset τ) (B : Finset ℕ)
    (h : ∀ w, 2 ≤ (f w).card → (∃ a < w, f w ⊆ f a) ∨
      (w ∈ B ∧ ∃ a < w, ∃ b < w, f w ⊆ f a ∪ f b))
    (R : Finset ℕ) : (R.biUnion f).card ≤ R.card + B.card := by
  have key : ∀ n : ℕ, ∀ R : Finset ℕ, (∀ w ∈ R, w < n) →
      (R.biUnion f).card ≤ R.card + (B.filter (· < n)).card := by
    intro n
    induction n with
    | zero =>
      intro R hR
      have : R = ∅ := Finset.eq_empty_of_forall_notMem fun w hw => by
        have := hR w hw; omega
      simp [this]
    | succ n ih =>
      intro R hR
      have hmonoB : (B.filter (· < n)).card ≤ (B.filter (· < n + 1)).card :=
        Finset.card_le_card fun w hw => by
          simp only [Finset.mem_filter] at hw ⊢
          exact ⟨hw.1, by omega⟩
      by_cases hn : n ∈ R
      · have herase : ∀ w ∈ R.erase n, w < n := fun w hw => by
          have h1 := hR w (Finset.mem_of_mem_erase hw)
          have h2 := Finset.ne_of_mem_erase hw
          omega
        have hcardR : (R.erase n).card + 1 = R.card := Finset.card_erase_add_one hn
        have hsplit : R.biUnion f ⊆ f n ∪ (R.erase n).biUnion f := by
          intro t ht
          rw [Finset.mem_biUnion] at ht
          obtain ⟨w, hw, htw⟩ := ht
          rw [Finset.mem_union]
          by_cases hwn : w = n
          · exact Or.inl (hwn ▸ htw)
          · exact Or.inr (Finset.mem_biUnion.2 ⟨w, Finset.mem_erase.2 ⟨hwn, hw⟩, htw⟩)
        by_cases h2 : 2 ≤ (f n).card
        · rcases h n h2 with ⟨a, ha, hsub⟩ | ⟨hB, a, ha, b, hb, hsub⟩
          · have h3 := ih (insert a (R.erase n)) (fun w hw => by
              rcases Finset.mem_insert.1 hw with rfl | hw
              · exact ha
              · exact herase w hw)
            have h4 : R.biUnion f ⊆ (insert a (R.erase n)).biUnion f := by
              rw [Finset.biUnion_insert]
              exact hsplit.trans (Finset.union_subset_union hsub (Finset.Subset.refl _))
            have h5 := Finset.card_le_card h4
            have h6 := Finset.card_insert_le a (R.erase n)
            omega
          · have h3 := ih (insert a (insert b (R.erase n))) (fun w hw => by
              rcases Finset.mem_insert.1 hw with rfl | hw
              · exact ha
              rcases Finset.mem_insert.1 hw with rfl | hw
              · exact hb
              · exact herase w hw)
            have h4 : R.biUnion f ⊆ (insert a (insert b (R.erase n))).biUnion f := by
              rw [Finset.biUnion_insert, Finset.biUnion_insert, ← Finset.union_assoc]
              exact hsplit.trans (Finset.union_subset_union hsub (Finset.Subset.refl _))
            have h5 := Finset.card_le_card h4
            have h6 := Finset.card_insert_le a (insert b (R.erase n))
            have h7 := Finset.card_insert_le b (R.erase n)
            have h8 : (B.filter (· < n)).card + 1 ≤ (B.filter (· < n + 1)).card := by
              have hnot : n ∉ B.filter (· < n) := by simp
              rw [← Finset.card_insert_of_notMem hnot]
              refine Finset.card_le_card fun w hw => ?_
              rcases Finset.mem_insert.1 hw with rfl | hw
              · exact Finset.mem_filter.2 ⟨hB, by omega⟩
              · rw [Finset.mem_filter] at hw ⊢
                exact ⟨hw.1, by omega⟩
            omega
        · have h3 := ih (R.erase n) herase
          have h4 := Finset.card_le_card hsplit
          have h5 := Finset.card_union_le (f n) ((R.erase n).biUnion f)
          omega
      · have h3 := ih R (fun w hw => by
          have h1 := hR w hw
          have h2 : w ≠ n := fun e => hn (e ▸ hw)
          omega)
        omega
  have h1 := key (R.sup id + 1) R (fun w hw => by
    have := Finset.le_sup (f := id) hw
    simp only [id] at this
    omega)
  have h2 : (B.filter (· < R.sup id + 1)).card ≤ B.card := Finset.card_filter_le _ _
  omega

lemma gate_op {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length) (x : Fin n → Bool) :
    value C x (n + k) = C.gates[k].op.eval
      (C.gates[k].inputs.map fun r => if r < n + k then value C x r else false) := by
  have h := gate_value C x (n + k) (by omega) (by unfold Circuit.size; omega)
  simpa only [Nat.add_sub_cancel_left] using h

lemma and_val {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (ho : C.gates[k].op = GateOp.and) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  rw [gate_op C k hk x, ho]
  simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  refine forall₂_congr fun r _ => ?_
  by_cases h : r < n + k <;> simp [h]

lemma or_val {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (ho : C.gates[k].op = GateOp.or) (x : Fin n → Bool) :
    value C x (n + k) = true ↔ ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C x r = true := by
  rw [gate_op C k hk x, ho]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
  refine exists_congr fun r => and_congr_right fun _ => ?_
  by_cases h : r < n + k <;> simp [h]

lemma two_kids (L : List ℕ) (hL : L.length ≤ 2) (w : ℕ) (hw : 0 < w) :
    ∃ a < w, ∃ b < w, ∀ r ∈ L, r < w → r = a ∨ r = b := by
  match L, hL with
  | [], _ => exact ⟨0, hw, 0, hw, by simp⟩
  | [a], _ =>
    by_cases ha : a < w
    · exact ⟨a, ha, a, ha, by simp⟩
    · exact ⟨0, hw, 0, hw, by simp; omega⟩
  | [a, b], _ =>
    by_cases ha : a < w <;> by_cases hb : b < w
    · exact ⟨a, ha, b, hb, by simp⟩
    · exact ⟨a, ha, a, ha, by simp; omega⟩
    · exact ⟨b, hb, b, hb, by simp; omega⟩
    · exact ⟨0, hw, 0, hw, by simp; omega⟩
  | _ :: _ :: _ :: _, h => simp at h

def Serves {n : ℕ} (C : Circuit) (l y : Fin n → Bool) (w : ℕ) : Prop :=
  value C l w = true ∧ value C y w = false

def Counted {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l y : ι → Fin n → Bool)
    (w : ℕ) : Prop :=
  ∃ p ∈ T, ∃ p' ∈ T, p ≠ p' ∧ Serves C (l p) (y p) w ∧ Serves C (l p') (y p') w

lemma gate_sep {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or) (l y : Fin n → Bool)
    (h : Serves C l y (n + k)) : ∃ r ∈ C.gates[k].inputs, r < n + k ∧ Serves C l y r := by
  by_contra hcon
  have hy : value C y (n + k) = true := gate_mono C k hk hop l y (fun r hr hlt hv => by
    by_contra hne
    exact hcon ⟨r, hr, hlt, hv, by simpa using hne⟩) h.1
  rw [h.2] at hy
  exact Bool.noConfusion hy

theorem ledger {n : ℕ} {ι : Type*} (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (T : Finset ι) (l y : ι → Fin n → Bool)
    (K : Finset ℕ) (R : Finset ℕ)
    (hR : ∀ t ∈ T, ∃ w ∈ R, Serves C (l t) (y t) w)
    (hin : ∀ v : Fin n, ∀ s ∈ T, ∀ t ∈ T, l s v = true → y s v = false → l t v = true →
      y t v = false → s = t)
    (hK : ∀ k, ∀ hk : k < C.gates.length, Counted C T l y (n + k) →
      (C.gates[k].op = GateOp.and ∧ ∀ s ∈ T, ∀ t ∈ T, y s = y t) ∨
      (C.gates[k].op = GateOp.or ∧ ∀ s ∈ T, ∀ t ∈ T, l s = l t) ∨
      (k ∈ K ∧ (C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or))) :
    T.card ≤ R.card + K.card := by
  classical
  let f : ℕ → Finset ι := fun w => T.filter fun t => Serves C (l t) (y t) w
  have hmem : ∀ w t, t ∈ f w ↔ t ∈ T ∧ Serves C (l t) (y t) w := fun w t => Finset.mem_filter
  have key := merge_count f (K.image (n + ·)) (by
    intro w hw
    obtain ⟨p, hp, p', hp', hne⟩ := Finset.one_lt_card.mp hw
    rw [hmem] at hp hp'
    have hwn : n ≤ w := by
      by_contra hlt
      have hlt : w < n := by omega
      have e : ∀ x : Fin n → Bool, value C x w = x ⟨w, hlt⟩ := fun x =>
        input_value C x ⟨w, hlt⟩
      have h1 := hp.2
      have h2 := hp'.2
      unfold Serves at h1 h2
      rw [e, e] at h1 h2
      exact hne (hin ⟨w, hlt⟩ p hp.1 p' hp'.1 h1.1 h1.2 h2.1 h2.2)
    have hwl : w < n + C.gates.length := by
      by_contra hge
      have h1 := hp.2.1
      rw [missing_value C (l p) w (by unfold Circuit.size; omega)] at h1
      exact Bool.noConfusion h1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    have hc : Counted C T l y (n + k) := ⟨p, hp.1, p', hp'.1, hne, hp.2, hp'.2⟩
    rcases hK k hk hc with ⟨ho, hy⟩ | ⟨ho, hl⟩ | ⟨hkK, hop⟩
    · left
      have h1 := hp.2.2
      have h2 : ¬ ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C (y p) r = true := fun h => by
        rw [(and_val C k hk ho (y p)).mpr h] at h1
        exact Bool.noConfusion h1
      push Not at h2
      obtain ⟨r, hr, hrv⟩ := h2
      have hlt := ((and_val C k hk ho (l p)).mp hp.2.1 r hr).1
      refine ⟨r, hlt, fun t ht => ?_⟩
      rw [hmem] at ht ⊢
      refine ⟨ht.1, ((and_val C k hk ho (l t)).mp ht.2.1 r hr).2, ?_⟩
      rw [hy t ht.1 p hp.1]
      simpa using hrv hlt
    · left
      obtain ⟨r, hr, hlt, hrv⟩ := (or_val C k hk ho (l p)).mp hp.2.1
      refine ⟨r, hlt, fun t ht => ?_⟩
      rw [hmem] at ht ⊢
      refine ⟨ht.1, by rw [hl t ht.1 p hp.1]; exact hrv, ?_⟩
      by_contra hne
      have := (or_val C k hk ho (y t)).mpr ⟨r, hr, hlt, by simpa using hne⟩
      rw [ht.2.2] at this
      exact Bool.noConfusion this
    · right
      refine ⟨Finset.mem_image.mpr ⟨k, hkK, rfl⟩, ?_⟩
      obtain ⟨r0, _, hr0, _⟩ := gate_sep C k hk hop _ _ hp.2
      obtain ⟨a, ha, b, hb, hab⟩ := two_kids _ (hfan _ (List.getElem_mem hk)) (n + k) (by omega)
      refine ⟨a, ha, b, hb, fun t ht => ?_⟩
      rw [hmem] at ht
      obtain ⟨r, hr, hlt, hs⟩ := gate_sep C k hk hop _ _ ht.2
      rw [Finset.mem_union, hmem, hmem]
      rcases hab r hr hlt with rfl | rfl
      · exact Or.inl ⟨ht.1, hs⟩
      · exact Or.inr ⟨ht.1, hs⟩) R
  have hT : T ⊆ R.biUnion f := fun t ht => by
    obtain ⟨w, hw, hs⟩ := hR t ht
    exact Finset.mem_biUnion.mpr ⟨w, hw, (hmem w t).mpr ⟨ht, hs⟩⟩
  have h1 := Finset.card_le_card hT
  have h2 : (K.image (n + ·)).card ≤ K.card := Finset.card_image_le
  omega

-- Lemma R, general form. x is below y for the list: pointwise below on the inputs, and every
-- gate that is not AND/OR and is true at x is true at y.
def Below {n : ℕ} (C : Circuit) (x y : Fin n → Bool) : Prop :=
  (∀ v, x v = true → y v = true) ∧
  ∀ k, ∀ hk : k < C.gates.length,
    ¬ (C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or) →
    value C x (n + k) = true → value C y (n + k) = true

theorem below_mono {n : ℕ} (C : Circuit) (x y : Fin n → Bool) (h : Below C x y) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using h.1 p
    by_cases hw : w < n + C.gates.length
    · have hk : w - n < C.gates.length := by omega
      have hwk : w = n + (w - n) := by omega
      rw [hwk]
      by_cases hop : C.gates[w - n].op = GateOp.and ∨ C.gates[w - n].op = GateOp.or
      · exact gate_mono C (w - n) hk hop x y fun r _ hlt => ih r (by omega)
      · exact h.2 (w - n) hk hop
    · simp [missing_value C x w (by unfold Circuit.size; omega)]

open Classical in
theorem pencils {n : ℕ} {κ ι : Type*} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (I : Finset κ) (S : κ → Finset ι) (u : ι → Fin n) (hu : Function.Injective u)
    (hS : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ s ∈ S i, ∀ t ∈ S i, s ∈ S j → t ∈ S j → s = t)
    (E : κ → Finset ι) (hE : ∀ i ∈ I, E i ⊆ S i) (R : κ → Finset ℕ)
    (hR : ∀ i ∈ I, ∀ t ∈ E i, ∃ w ∈ R i, Serves C (fun v => decide (v = u t))
      (fun v => decide (∃ s, s ∉ S i ∧ v = u s)) w) :
    ∑ i ∈ I, (E i).card ≤ ∑ i ∈ I, (R i).card + ((Finset.range C.gates.length).filter
      fun k => ∃ hk : k < C.gates.length, C.gates[k].op = GateOp.or).card := by
  let l : ι → Fin n → Bool := fun t v => decide (v = u t)
  let y : κ → ι → Fin n → Bool := fun i _ v => decide (∃ s, s ∉ S i ∧ v = u s)
  let K : κ → Finset ℕ := fun i => ((Finset.range C.gates.length).filter
      fun k => ∃ hk : k < C.gates.length, C.gates[k].op = GateOp.or).filter
      fun k => Counted C (E i) l (y i) (n + k)
  have hcard : ∀ i ∈ I, (E i).card ≤ (R i).card + (K i).card := fun i hi =>
    ledger C (fun g hg => (hC g hg).2) (E i) l (y i) (K i) (R i) (hR i hi)
      (fun v s _ t _ h1 _ h3 _ => by
        simp only [l, decide_eq_true_eq] at h1 h3
        exact hu (h1.symm.trans h3))
      (fun k hk hc => by
        rcases (hC _ (List.getElem_mem hk)).1 with ho | ho
        · exact Or.inl ⟨ho, fun _ _ _ _ => rfl⟩
        · refine Or.inr (Or.inr ⟨?_, Or.inr ho⟩)
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr hk, hk, ho⟩, hc⟩)
  have hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (K i) (K j) := by
    intro i hi j hj hij
    refine Finset.disjoint_left.mpr fun k hki hkj => ?_
    obtain ⟨s, hs, t, ht, hst, hs1, ht1⟩ := (Finset.mem_filter.mp hki).2
    obtain ⟨r, _, _, _, _, hr1, _⟩ := (Finset.mem_filter.mp hkj).2
    have hin : ∀ e, Serves C (l e) (y i e) (n + k) → e ∈ S j := by
      intro e he
      by_contra hne
      have hb : Below C (l e) (y j r) := by
        refine ⟨fun v hv => ?_, fun m hm hno => absurd (hC _ (List.getElem_mem hm)).1 hno⟩
        simp only [l, decide_eq_true_eq] at hv
        simp only [y, decide_eq_true_eq]
        exact ⟨e, hne, hv⟩
      have := below_mono C _ _ hb (n + k) he.1
      rw [hr1.2] at this
      exact Bool.noConfusion this
    exact hst (hS i hi j hj hij s (hE i hi hs) t (hE i hi ht) (hin s hs1) (hin t ht1))
  have h1 : (I.biUnion K).card ≤ ((Finset.range C.gates.length).filter
      fun k => ∃ hk : k < C.gates.length, C.gates[k].op = GateOp.or).card :=
    Finset.card_le_card fun k hk => by
      obtain ⟨i, _, hki⟩ := Finset.mem_biUnion.mp hk
      exact (Finset.mem_filter.mp hki).1
  rw [Finset.card_biUnion hdisj] at h1
  have h2 := Finset.sum_le_sum hcard
  rw [Finset.sum_add_distrib] at h2
  omega

section starblock
open PEqualNP.MetaComplexity.NestedCover

lemma value_mono {n : ℕ} (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (h : ∀ v, x v = true → y v = true) (w : ℕ)
    (hw : value C x w = true) : value C y w = true :=
  below_mono C x y ⟨h, fun _ hk hno => absurd (hC _ (List.getElem_mem hk)).1 hno⟩ w hw

def pt {N : ℕ} (p : Fin N) : Fin (N + N) → Bool := fun k => decide (k = Fin.castAdd N p)

def ln {N : ℕ} (l : Fin N) : Fin (N + N) → Bool := fun k => decide (k = Fin.natAdd N l)

lemma cast_ne {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

lemma pt_cast {N : ℕ} (p p' : Fin N) : pt p (Fin.castAdd N p') = true ↔ p' = p := by
  simp only [pt, decide_eq_true_eq]
  exact (Fin.castAdd_injective N N).eq_iff

lemma pt_nat {N : ℕ} (p l : Fin N) : pt p (Fin.natAdd N l) = true ↔ False := by
  simp only [pt, decide_eq_true_eq, iff_false]
  exact (cast_ne p l).symm

lemma ln_nat {N : ℕ} (l l' : Fin N) : ln l (Fin.natAdd N l') = true ↔ l' = l := by
  simp only [ln, decide_eq_true_eq]
  exact (Fin.natAdd_injective N N).eq_iff

lemma ln_cast {N : ℕ} (l p : Fin N) : ln l (Fin.castAdd N p) = true ↔ False := by
  simp only [ln, decide_eq_true_eq, iff_false]
  exact cast_ne p l

-- gate j is an AND with inputs a and c, sound, with a on at p and c on at l
def Wit {N : ℕ} (I : Fin N → Fin N → Prop) (C : Circuit) (j a c : ℕ) (p l : Fin N) : Prop :=
  (∃ hj : j < C.gates.length, C.gates[j].op = GateOp.and) ∧ a ∈ (gateAt C j).inputs ∧
  c ∈ (gateAt C j).inputs ∧ (∀ r ∈ (gateAt C j).inputs, r = a ∨ r = c) ∧
  (∀ x x' : Fin (N + N) → Bool, value C x a = true → value C x' c = true →
    ∃ p0 l0 : Fin N, I p0 l0 ∧ (x (Fin.castAdd N p0) = true ∨ x' (Fin.castAdd N p0) = true) ∧
      (x (Fin.natAdd N l0) = true ∨ x' (Fin.natAdd N l0) = true)) ∧
  value C (pt p) a = true ∧ value C (ln l) c = true

-- the points (lines) at which some input wire of gate j is on
def PA {N : ℕ} (C : Circuit) (j : ℕ) : Set (Fin N) :=
  {p | ∃ r ∈ (gateAt C j).inputs, value C (pt p) r = true}

def LB {N : ℕ} (C : Circuit) (j : ℕ) : Set (Fin N) :=
  {l | ∃ r ∈ (gateAt C j).inputs, value C (ln l) r = true}

lemma wit_pa {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit} {j a c : ℕ} {p l : Fin N}
    (h : Wit I C j a c p l) (p' : Fin N) (hp : p' ∈ PA C j) : value C (pt p') a = true := by
  obtain ⟨-, -, -, hall, hs, hpa, -⟩ := h
  obtain ⟨r, hr, hv⟩ := hp
  rcases hall r hr with rfl | rfl
  · exact hv
  · obtain ⟨p0, l0, -, -, h2⟩ := hs (pt p) (pt p') hpa hv
    simp only [pt_nat, or_self] at h2

lemma wit_lb {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit} {j a c : ℕ} {p l : Fin N}
    (h : Wit I C j a c p l) (l' : Fin N) (hl : l' ∈ LB C j) : value C (ln l') c = true := by
  obtain ⟨-, -, -, hall, hs, -, hlc⟩ := h
  obtain ⟨r, hr, hv⟩ := hl
  rcases hall r hr with rfl | rfl
  · obtain ⟨p0, l0, -, h1, -⟩ := hs (ln l') (ln l) hv hlc
    simp only [ln_cast, or_self] at h1
  · exact hv

lemma wit_inc {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit} {j a c : ℕ} {p l : Fin N}
    (h : Wit I C j a c p l) (p' l' : Fin N) (hp : p' ∈ PA C j) (hl : l' ∈ LB C j) : I p' l' := by
  obtain ⟨p0, l0, hI, h1, h2⟩ := h.2.2.2.2.1 _ _ (wit_pa h p' hp) (wit_lb h l' hl)
  simp only [pt_cast, pt_nat, ln_cast, ln_nat, or_false, false_or] at h1 h2
  subst h1; subst h2
  exact hI

open Classical in
theorem stars (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hI : ∀ p p' l l', p ≠ p' → I p l → I p' l → I p l' → I p' l' → l = l') :
    {e : Fin N × Fin N | I e.1 e.2 ∧ ∃ j a c, Wit I C j a c e.1 e.2}.ncard ≤
      2 * C.gates.length := by
  let A : Finset ℕ := (Finset.range C.gates.length).filter
    fun k => ∃ hk : k < C.gates.length, C.gates[k].op = GateOp.and
  let O : Finset ℕ := (Finset.range C.gates.length).filter
    fun k => ∃ hk : k < C.gates.length, C.gates[k].op = GateOp.or
  have hAO : A.card + O.card ≤ C.gates.length := by
    rw [← Finset.card_union_of_disjoint]
    · calc (A ∪ O).card ≤ (Finset.range C.gates.length).card :=
          Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _)
            (Finset.filter_subset _ _))
        _ = _ := Finset.card_range _
    · refine Finset.disjoint_left.mpr fun k h1 h2 => ?_
      obtain ⟨_, e1⟩ := (Finset.mem_filter.mp h1).2
      obtain ⟨_, e2⟩ := (Finset.mem_filter.mp h2).2
      rw [e1] at e2
      exact GateOp.noConfusion e2
  let J1 : Fin N → Finset ℕ := fun p => A.filter fun j => PA C j = {p}
  let J2 : Fin N → Finset ℕ := fun l => A.filter fun j =>
    LB C j = {l} ∧ ¬ ∃ p : Fin N, PA C j = {p}
  let R1 : Fin N → Finset ℕ := fun p => (J1 p).biUnion fun j => (gateAt C j).inputs.toFinset
  let R2 : Fin N → Finset ℕ := fun l => (J2 l).biUnion fun j => (gateAt C j).inputs.toFinset
  let E1 : Fin N → Finset (Fin N) := fun p => Finset.univ.filter fun l =>
    I p l ∧ ∃ j a c, Wit I C j a c p l ∧ PA C j = {p}
  let E2 : Fin N → Finset (Fin N) := fun l => Finset.univ.filter fun p =>
    I p l ∧ ∃ j a c, Wit I C j a c p l ∧ LB C j = {l} ∧ ¬ ∃ p' : Fin N, PA C j = {p'}
  have hfan : ∀ j, (gateAt C j).inputs.toFinset.card ≤ 2 := by
    intro j
    refine (List.toFinset_card_le _).trans ?_
    by_cases hj : j < C.gates.length
    · have : gateAt C j = C.gates[j] := by simp [gateAt, hj]
      rw [this]
      exact (hC _ (List.getElem_mem hj)).2
    · simp [gateAt, hj]
  have hR1 : ∀ p, (R1 p).card ≤ 2 * (J1 p).card := fun p => by
    rw [mul_comm]
    exact Finset.card_biUnion_le_card_mul _ _ _ fun j _ => hfan j
  have hR2 : ∀ l, (R2 l).card ≤ 2 * (J2 l).card := fun l => by
    rw [mul_comm]
    exact Finset.card_biUnion_le_card_mul _ _ _ fun j _ => hfan j
  have hA : ∀ {j a c p l}, Wit I C j a c p l → j ∈ A := fun h => by
    obtain ⟨hj, ho⟩ := h.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hj, ho⟩
  have b1 := pencils C hC Finset.univ (fun p : Fin N => Finset.univ.filter fun l => I p l)
    (fun l : Fin N => Fin.natAdd N l) (Fin.natAdd_injective N N)
    (by
      intro p _ p' _ hp s hs t ht hs' ht'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ht hs' ht'
      exact hI p p' s t hp hs hs' ht ht')
    E1
    (fun p _ l hl => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl).2.1⟩)
    R1 (by
      intro p _ l hl
      obtain ⟨-, -, j, a, c, hw, hP⟩ := Finset.mem_filter.mp hl
      refine ⟨c, Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hA hw, hP⟩,
        List.mem_toFinset.mpr hw.2.2.1⟩, hw.2.2.2.2.2.2, ?_⟩
      by_contra hne
      obtain ⟨p0, l0, h0, h1, h2⟩ := hw.2.2.2.2.1 (pt p) _ hw.2.2.2.2.2.1
        (Bool.not_eq_false _ ▸ hne)
      simp only [pt_cast, pt_nat, decide_eq_true_eq, false_or, Finset.mem_filter,
        Finset.mem_univ, true_and] at h1 h2
      obtain ⟨s, hs, he⟩ := h2
      rw [← (Fin.natAdd_injective N N) he] at hs
      rcases h1 with rfl | ⟨t, _, ht⟩
      · exact hs h0
      · exact cast_ne _ _ ht)
  have b2 := pencils C hC Finset.univ (fun l : Fin N => Finset.univ.filter fun p => I p l)
    (fun p : Fin N => Fin.castAdd N p) (Fin.castAdd_injective N N)
    (by
      intro l _ l' _ hl s hs t ht hs' ht'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ht hs' ht'
      by_contra hst
      exact hl (hI s t l l' hst hs ht hs' ht'))
    E2
    (fun p _ l hl => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl).2.1⟩)
    R2 (by
      intro l _ p hp
      obtain ⟨-, -, j, a, c, hw, hP⟩ := Finset.mem_filter.mp hp
      refine ⟨a, Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hA hw, hP⟩,
        List.mem_toFinset.mpr hw.2.1⟩, hw.2.2.2.2.2.1, ?_⟩
      by_contra hne
      obtain ⟨p0, l0, h0, h1, h2⟩ := hw.2.2.2.2.1 _ (ln l) (Bool.not_eq_false _ ▸ hne)
        hw.2.2.2.2.2.2
      simp only [ln_cast, ln_nat, decide_eq_true_eq, or_false, Finset.mem_filter,
        Finset.mem_univ, true_and] at h1 h2
      obtain ⟨s, hs, he⟩ := h1
      rw [← (Fin.castAdd_injective N N) he] at hs
      rcases h2 with ⟨t, _, ht⟩ | rfl
      · exact cast_ne _ _ ht.symm
      · exact hs h0)
  have hJ : ∑ p, (J1 p).card + ∑ l, (J2 l).card ≤ A.card := by
    rw [← Finset.card_biUnion, ← Finset.card_biUnion, ← Finset.card_union_of_disjoint]
    · refine Finset.card_le_card (Finset.union_subset ?_ ?_) <;>
      · refine Finset.biUnion_subset.mpr fun _ _ => Finset.filter_subset _ _
    · refine Finset.disjoint_left.mpr fun j h1 h2 => ?_
      obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.mp h1
      obtain ⟨l, -, hl⟩ := Finset.mem_biUnion.mp h2
      exact (Finset.mem_filter.mp hl).2.2 ⟨p, (Finset.mem_filter.mp hp).2⟩
    · intro l _ l' _ hne
      refine Finset.disjoint_left.mpr fun j h1 h2 => hne ?_
      exact Set.singleton_injective
        ((Finset.mem_filter.mp h1).2.1.symm.trans (Finset.mem_filter.mp h2).2.1)
    · intro p _ p' _ hne
      refine Finset.disjoint_left.mpr fun j h1 h2 => hne ?_
      exact Set.singleton_injective
        ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  have hsub : {e : Fin N × Fin N | I e.1 e.2 ∧ ∃ j a c, Wit I C j a c e.1 e.2} ⊆
      (((Finset.univ.biUnion fun p => (E1 p).image fun l => (p, l)) ∪
        (Finset.univ.biUnion fun l => (E2 l).image fun p => (p, l)) :
          Finset (Fin N × Fin N)) : Set (Fin N × Fin N)) := by
    rintro ⟨p, l⟩ ⟨he, j, a, c, hw⟩
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_biUnion,
      Finset.mem_univ, true_and, Finset.mem_image]
    have hp : p ∈ PA C j := ⟨a, hw.2.1, hw.2.2.2.2.2.1⟩
    have hl : l ∈ LB C j := ⟨c, hw.2.2.1, hw.2.2.2.2.2.2⟩
    by_cases h1 : ∃ p' : Fin N, PA C j = {p'}
    · obtain ⟨p', hp'⟩ := h1
      have : p = p' := by rw [hp'] at hp; exact hp
      subst this
      exact Or.inl ⟨p, l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he, j, a, c, hw, hp'⟩, rfl⟩
    · refine Or.inr ⟨l, p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he, j, a, c, hw, ?_, h1⟩, rfl⟩
      obtain ⟨p', hp', hne⟩ : ∃ p', p' ∈ PA C j ∧ p' ≠ p := by
        by_contra hcon
        push Not at hcon
        exact h1 ⟨p, Set.eq_singleton_iff_unique_mem.mpr ⟨hp, hcon⟩⟩
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨hl, fun l' hl' => ?_⟩
      exact hI p' p l' l hne (wit_inc hw p' l' hp' hl') (wit_inc hw p l' hp hl')
        (wit_inc hw p' l hp' hl) (wit_inc hw p l hp hl)
  have hle := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at hle
  have c1 : (Finset.univ.biUnion fun p => (E1 p).image fun l => (p, l)).card ≤
      ∑ p, (E1 p).card :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun p _ => Finset.card_image_le)
  have c2 : (Finset.univ.biUnion fun l => (E2 l).image fun p => (p, l)).card ≤
      ∑ l, (E2 l).card :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun p _ => Finset.card_image_le)
  have c3 := Finset.card_union_le (Finset.univ.biUnion fun p => (E1 p).image fun l => (p, l))
    (Finset.univ.biUnion fun l => (E2 l).image fun p => (p, l))
  have d1 : ∑ p, (R1 p).card ≤ 2 * ∑ p, (J1 p).card := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p _ => hR1 p
  have d2 : ∑ l, (R2 l).card ≤ 2 * ∑ l, (J2 l).card := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p _ => hR2 p
  change ∑ p, (E1 p).card ≤ ∑ p, (R1 p).card + O.card at b1
  change ∑ p, (E2 p).card ≤ ∑ p, (R2 p).card + O.card at b2
  omega

lemma wit_of {N : ℕ} (I : Fin N → Fin N → Prop) (C : Circuit)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hb : ReadsBack (N + N) C) (j a c : ℕ) (p l : Fin N) (hj : j < C.gates.length)
    (ho : (gateAt C j).op = GateOp.and)
    (hi : (gateAt C j).inputs = [a, c] ∨ (gateAt C j).inputs = [c, a])
    (hs : ∀ z : Fin (N + N) → Bool, value C z (N + N + j) = true →
      ∃ p0 l0 : Fin N, I p0 l0 ∧ z (Fin.castAdd N p0) = true ∧ z (Fin.natAdd N l0) = true)
    (hp : value C (pt p) a = true) (hl : value C (ln l) c = true) : Wit I C j a c p l := by
  have hg : gateAt C j = C.gates[j] := by simp [gateAt, hj]
  have hmem : ∀ r, r ∈ (gateAt C j).inputs ↔ r = a ∨ r = c := by
    intro r
    rcases hi with h | h <;> rw [h] <;> simp [or_comm]
  refine ⟨⟨hj, hg ▸ ho⟩, (hmem a).mpr (Or.inl rfl), (hmem c).mpr (Or.inr rfl),
    fun r hr => (hmem r).mp hr, fun x x' hx hx' => ?_, hp, hl⟩
  have hv : value C (fun k => x k || x' k) (N + N + j) = true := by
    rw [and_val C j hj (hg ▸ ho)]
    intro r hr
    rw [← hg] at hr
    refine ⟨hb j hj r hr, ?_⟩
    rcases (hmem r).mp hr with rfl | rfl
    · exact value_mono C hC x _ (fun v h => by simp [h]) _ hx
    · exact value_mono C hC x' _ (fun v h => by simp [h]) _ hx'
  obtain ⟨p0, l0, h0, h1, h2⟩ := hs _ hv
  exact ⟨p0, l0, h0, by simpa using h1, by simpa using h2⟩

end starblock

section debtblock
open Classical

lemma merge_rank {ι τ : Type*} (r : ι → ℕ) (f : ι → Finset τ) (B : Finset ι) (c : ι → ℕ)
    (h : ∀ i, 2 ≤ (f i).card → ∃ J : Finset ι, (∀ a ∈ J, r a < r i) ∧ f i ⊆ J.biUnion f ∧
      J.card ≤ 1 + (if i ∈ B then c i else 0)) (R : Finset ι) :
    (R.biUnion f).card ≤ R.card + ∑ i ∈ B, c i := by
  have key : ∀ n : ℕ, ∀ R : Finset ι, (∀ i ∈ R, r i < n) →
      (R.biUnion f).card ≤ R.card + ∑ i ∈ B.filter (fun i => r i < n), c i := by
    intro n
    induction n with
    | zero =>
      intro R hR
      have : R = ∅ := Finset.eq_empty_of_forall_notMem fun w hw => by
        have := hR w hw
        omega
      simp [this]
    | succ n ih =>
      intro R hR
      let L := R.filter fun i => r i < n
      let K := R.filter fun i => ¬ r i < n ∧ 2 ≤ (f i).card
      let Z := R.filter fun i => ¬ r i < n ∧ ¬ 2 ≤ (f i).card
      have hJ : ∀ i, ∃ J : Finset ι, i ∈ K → (∀ a ∈ J, r a < r i) ∧ f i ⊆ J.biUnion f ∧
          J.card ≤ 1 + (if i ∈ B then c i else 0) := by
        intro i
        by_cases hi : i ∈ K
        · obtain ⟨J, hJ⟩ := h i (Finset.mem_filter.mp hi).2.2
          exact ⟨J, fun _ => hJ⟩
        · exact ⟨∅, fun h => absurd h hi⟩
      choose J hJ using hJ
      have hsub : R.biUnion f ⊆ (L ∪ K.biUnion J).biUnion f ∪ Z.biUnion f := by
        intro t ht
        obtain ⟨i, hi, hti⟩ := Finset.mem_biUnion.mp ht
        by_cases h1 : r i < n
        · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
            ⟨i, Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, h1⟩), hti⟩)
        by_cases h2 : 2 ≤ (f i).card
        · have hiK : i ∈ K := Finset.mem_filter.mpr ⟨hi, h1, h2⟩
          obtain ⟨a, ha, hta⟩ := Finset.mem_biUnion.mp ((hJ i hiK).2.1 hti)
          exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
            ⟨a, Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hiK, ha⟩), hta⟩)
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨i, Finset.mem_filter.mpr ⟨hi, h1, h2⟩, hti⟩)
      have h1 := ih (L ∪ K.biUnion J) (fun i hi => by
        rcases Finset.mem_union.mp hi with hi | hi
        · exact (Finset.mem_filter.mp hi).2
        · obtain ⟨k, hk, hik⟩ := Finset.mem_biUnion.mp hi
          have := (hJ k hk).1 i hik
          have := hR k (Finset.mem_filter.mp hk).1
          omega)
      have h2 : (K.biUnion J).card ≤ K.card + ∑ i ∈ K, (if i ∈ B then c i else 0) := by
        refine Finset.card_biUnion_le.trans ?_
        refine (Finset.sum_le_sum fun i hi => (hJ i hi).2.2).trans ?_
        rw [Finset.sum_add_distrib]
        simp
      have h3 : (Z.biUnion f).card ≤ Z.card := by
        refine Finset.card_biUnion_le.trans ?_
        refine (Finset.sum_le_sum (g := fun _ => 1) fun i hi => ?_).trans (by simp)
        have := (Finset.mem_filter.mp hi).2.2
        omega
      have h4 : ∑ i ∈ K, (if i ∈ B then c i else 0) +
          ∑ i ∈ B.filter (fun i => r i < n), c i ≤ ∑ i ∈ B.filter (fun i => r i < n + 1), c i := by
        rw [← Finset.sum_filter, ← Finset.sum_union]
        · refine Finset.sum_le_sum_of_subset fun i hi => ?_
          rcases Finset.mem_union.mp hi with hi | hi
          · obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hi
            exact Finset.mem_filter.mpr ⟨h2, hR i (Finset.mem_filter.mp h1).1⟩
          · obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hi
            exact Finset.mem_filter.mpr ⟨h1, by omega⟩
        · refine Finset.disjoint_left.mpr fun i hi hi' => ?_
          have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2.1
          exact h1 (Finset.mem_filter.mp hi').2
      have h5 : L.card + (K.card + Z.card) = R.card := by
        have e1 := Finset.card_filter_add_card_filter_not (s := R) (fun i => r i < n)
        have e2 := Finset.card_filter_add_card_filter_not
          (s := R.filter fun i => ¬ r i < n) (fun i => 2 ≤ (f i).card)
        rw [Finset.filter_filter, Finset.filter_filter] at e2
        have e3 : L.card = (R.filter fun i => r i < n).card := rfl
        have e4 : K.card = (R.filter fun i => ¬ r i < n ∧ 2 ≤ (f i).card).card := rfl
        have e5 : Z.card = (R.filter fun i => ¬ r i < n ∧ ¬ 2 ≤ (f i).card).card := rfl
        omega
      have h6 := Finset.card_le_card hsub
      have h7 := Finset.card_union_le ((L ∪ K.biUnion J).biUnion f) (Z.biUnion f)
      have h8 := Finset.card_union_le L (K.biUnion J)
      omega
  refine (key (R.sup r + 1) R fun i hi => ?_).trans ?_
  · have := Finset.le_sup (f := r) hi
    omega
  · have := Finset.sum_le_sum_of_subset (f := c) (Finset.filter_subset
      (fun i => r i < R.sup r + 1) B)
    omega

-- the items at which a node is true when that item alone is on
noncomputable def Sing {ι τ : Type*} [Fintype τ] (T : Finset τ → ι → Prop) (i : ι) : Finset τ :=
  Finset.univ.filter fun t => T {t} i

def Own {ι τ : Type*} [Fintype τ] (T : Finset τ → ι → Prop) (I : Finset τ) (i : ι) : Prop :=
  Sing T i ⊆ I ∧ 2 ≤ (Sing T i).card

def Nodes {ι τ : Type*} [Fintype τ] (T : Finset τ → ι → Prop) (r : ι → ℕ) (A B : Finset ι)
    (c : ι → ℕ) (ch : ι → Bool → ι) : Prop :=
  ∀ i, 2 ≤ (Sing T i).card → (∀ X, T X i) ∨
    (i ∈ A ∧ (∀ b, r (ch i b) < r i) ∧ ∀ X, T X i ↔ T X (ch i false) ∧ T X (ch i true)) ∨
    ∃ J : Finset ι, (∀ a ∈ J, r a < r i) ∧ J.card ≤ 1 + (if i ∈ B then c i else 0) ∧
      ∀ X, T X i ↔ ∃ a ∈ J, T X a

lemma one_owner {ι τ : Type*} [Fintype τ] (T : Finset τ → ι → Prop)
    (hT : ∀ X Y i, X ⊆ Y → T X i → T Y i) (r : ι → ℕ) (A B : Finset ι) (c : ι → ℕ)
    (ch : ι → Bool → ι) (hN : Nodes T r A B c ch) (q : ℕ) (I : Finset τ) (w : ι)
    (hw : ∀ X : Finset τ, X.card ≤ q → T X w → ∃ t ∈ X, t ∈ I) (hq : 1 ≤ q)
    (E : Finset τ) (hE : E ⊆ Sing T w) (hEq : E.card ≤ q + 1) :
    E.card ≤ 1 + ∑ i ∈ B.filter (Own T I), c i + 2 * (A.filter (Own T I)).card := by
  by_cases hA : q < 2 * (A.filter (Own T I)).card
  · omega
  let P := (A.filter (Own T I)) ×ˢ (Finset.univ : Finset Bool)
  let g : ι × Bool → Finset τ := fun e =>
    if h : ∃ t, t ∈ Sing T (ch e.1 e.2) ∧ t ∉ I then {h.choose} else ∅
  let X := P.biUnion g
  have hXc : X.card ≤ q := by
    refine Finset.card_biUnion_le.trans ((Finset.sum_le_sum (g := fun _ => 1) fun e _ => ?_).trans ?_)
    · dsimp only [g]
      split <;> simp
    · simp only [P, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_product,
        Finset.card_univ, Fintype.card_bool]
      omega
  have hXI : ∀ t ∈ X, t ∉ I := by
    intro t ht
    obtain ⟨e, _, hte⟩ := Finset.mem_biUnion.mp ht
    dsimp only [g] at hte
    split at hte
    · rename_i h
      rw [Finset.mem_singleton.mp hte]
      exact h.choose_spec.2
    · simp at hte
  have hdebt : ∀ i ∈ A.filter (Own T I), ∀ b, ¬ T X (ch i b) → Sing T (ch i b) ⊆ I := by
    intro i hi b hX t ht
    by_contra hI
    apply hX
    have h : ∃ t, t ∈ Sing T (ch i b) ∧ t ∉ I := ⟨t, ht, hI⟩
    have hmem : h.choose ∈ X := by
      refine Finset.mem_biUnion.mpr ⟨(i, b), Finset.mem_product.mpr ⟨hi, Finset.mem_univ _⟩, ?_⟩
      dsimp only [g]
      rw [dite_eq_left h]
      exact Finset.mem_singleton_self _
    exact hT _ _ _ (Finset.singleton_subset_iff.mpr hmem)
      (Finset.mem_filter.mp h.choose_spec.1).2
  let f : ι → Finset τ := fun i => if ¬ T X i ∧ Sing T i ⊆ I then Sing T i else ∅
  have hf : ∀ i, ¬ T X i → Sing T i ⊆ I → f i = Sing T i := fun i h1 h2 => by
    dsimp only [f]
    rw [ite_eq_left ⟨h1, h2⟩]
  have hwX : ¬ T X w := fun h => by
    obtain ⟨t, h1, h2⟩ := hw X hXc h
    exact hXI t h1 h2
  have hwI : Sing T w ⊆ I := by
    intro t ht
    obtain ⟨s, h1, h2⟩ := hw {t} (by simpa using hq) (Finset.mem_filter.mp ht).2
    rwa [Finset.mem_singleton.mp h1] at h2
  have key := merge_rank r f (B.filter (Own T I)) c (fun i hi => by
    by_cases hg : ¬ T X i ∧ Sing T i ⊆ I
    · rw [hf i hg.1 hg.2] at hi ⊢
      have hown : Own T I i := ⟨hg.2, hi⟩
      rcases hN i hi with h | ⟨hiA, hr, h⟩ | ⟨J, hr, hc, h⟩
      · exact absurd (h X) hg.1
      · have hiA' : i ∈ A.filter (Own T I) := Finset.mem_filter.mpr ⟨hiA, hown⟩
        obtain ⟨b, hb⟩ : ∃ b, ¬ T X (ch i b) := by
          by_contra hno
          push Not at hno
          exact hg.1 ((h X).mpr ⟨hno false, hno true⟩)
        refine ⟨{ch i b}, fun a ha => by rw [Finset.mem_singleton.mp ha]; exact hr b, ?_, by simp⟩
        rw [Finset.singleton_biUnion, hf _ hb (hdebt i hiA' b hb)]
        intro t ht
        have := (h {t}).mp (Finset.mem_filter.mp ht).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        cases b
        · exact this.1
        · exact this.2
      · refine ⟨J, hr, fun t ht => ?_, ?_⟩
        · obtain ⟨a, ha, hta⟩ := (h {t}).mp (Finset.mem_filter.mp ht).2
          refine Finset.mem_biUnion.mpr ⟨a, ha, ?_⟩
          rw [hf a (fun hX => hg.1 ((h X).mpr ⟨a, ha, hX⟩)) (fun s hs => hg.2
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              (h {s}).mpr ⟨a, ha, (Finset.mem_filter.mp hs).2⟩⟩))]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hta⟩
        · by_cases hB : i ∈ B
          · rw [ite_eq_left (Finset.mem_filter.mpr ⟨hB, hown⟩)]
            rwa [ite_eq_left hB] at hc
          · rw [ite_eq_right hB] at hc
            omega
    · have : f i = ∅ := by
        dsimp only [f]
        rw [ite_eq_right hg]
      rw [this] at hi
      simp at hi) {w}
  rw [Finset.singleton_biUnion, hf w hwX hwI, Finset.card_singleton] at key
  have := Finset.card_le_card hE
  omega

lemma sum_own {ι κ : Type*} [Fintype κ] (B : Finset ι) (c : ι → ℕ) (Rg : κ → ι → Prop)
    (h : ∀ i k k', Rg k i → Rg k' i → k = k') :
    ∑ k, ∑ i ∈ B.filter (Rg k), c i ≤ ∑ i ∈ B, c i := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  have : (Finset.univ.filter fun k => Rg k i).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    exact h i a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  calc _ ≤ 1 * c i := Nat.mul_le_mul_right _ this
    _ = c i := one_mul _

-- owners k with item sets I k that share at most one item, promise up to q items on
theorem promise_ledger {ι τ κ : Type*} [Fintype τ] [Fintype κ] (T : Finset τ → ι → Prop)
    (hT : ∀ X Y i, X ⊆ Y → T X i → T Y i) (r : ι → ℕ) (A B : Finset ι) (c : ι → ℕ)
    (ch : ι → Bool → ι) (hN : Nodes T r A B c ch) (q : ℕ) (hq : 1 ≤ q) (I : κ → Finset τ)
    (hI : ∀ k k', k ≠ k' → ∀ s ∈ I k, ∀ t ∈ I k, s ∈ I k' → t ∈ I k' → s = t) (w : κ → ι)
    (hw : ∀ k, ∀ X : Finset τ, X.card ≤ q → T X (w k) → ∃ t ∈ X, t ∈ I k)
    (E : κ → Finset τ) (hE : ∀ k, E k ⊆ Sing T (w k)) (hEq : ∀ k, (E k).card ≤ q + 1) :
    ∑ k, (E k).card ≤ (Finset.univ.filter fun k => (E k).Nonempty).card + ∑ i ∈ B, c i +
      2 * A.card := by
  have h1 : ∀ k, (E k).card ≤ (if (E k).Nonempty then 1 else 0) +
      ∑ i ∈ B.filter (Own T (I k)), c i + 2 * ∑ i ∈ A.filter (Own T (I k)), 1 := by
    intro k
    by_cases hk : (E k).Nonempty
    · rw [ite_eq_left hk, ← Finset.card_eq_sum_ones]
      exact one_owner T hT r A B c ch hN q (I k) (w k) (hw k) hq (E k) (hE k) (hEq k)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hk]
      simp
  have hd : ∀ i k k', Own T (I k) i → Own T (I k') i → k = k' := by
    intro i k k' h h'
    by_contra hne
    obtain ⟨s, hs, t, ht, hst⟩ := Finset.one_lt_card.mp h.2
    exact hst (hI k k' hne s (h.1 hs) t (h.1 ht) (h'.1 hs) (h'.1 ht))
  have h2 := sum_own B c (fun k => Own T (I k)) hd
  have h3 := sum_own A (fun _ => 1) (fun k => Own T (I k)) hd
  refine (Finset.sum_le_sum fun k _ => h1 k).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.card_filter]
  rw [← Finset.card_eq_sum_ones] at h3
  omega

end debtblock

section inst
open PEqualNP.ReadK PEqualNP.MetaComplexity PEqualNP.TopForm
open Classical

-- points P on, lines X on
noncomputable def io {N : ℕ} (P X : Finset (Fin N)) : Fin (N + N) → Bool :=
  Fin.append (fun p => decide (p ∈ P)) (fun l => decide (l ∈ X))

lemma io_p {N : ℕ} (P X : Finset (Fin N)) (p : Fin N) :
    io P X (Fin.castAdd N p) = decide (p ∈ P) := Fin.append_left _ _ p

lemma io_l {N : ℕ} (P X : Finset (Fin N)) (l : Fin N) :
    io P X (Fin.natAdd N l) = decide (l ∈ X) := Fin.append_right _ _ l

noncomputable def V {N : ℕ} (C : Circuit) (P X : Finset (Fin N)) (w : ℕ) : Prop :=
  value C (io P X) w = true

def lt (C : Circuit) (j : ℕ) : ℕ := (C.gates.getD j ⟨GateOp.and, []⟩).inputs.getD 0 0
def rt (C : Circuit) (j : ℕ) : ℕ := (C.gates.getD j ⟨GateOp.and, []⟩).inputs.getD 1 0
def isA (C : Circuit) (j : ℕ) : Prop := j < C.gates.length ∧
  (C.gates.getD j ⟨GateOp.and, []⟩).op = GateOp.and
def isO (C : Circuit) (j : ℕ) : Prop := j < C.gates.length ∧
  (C.gates.getD j ⟨GateOp.and, []⟩).op = GateOp.or

-- w reaches the output through gates whose other inputs are on with the lines X alone
def K {N : ℕ} (C : Circuit) (X : Finset (Fin N)) (w : ℕ) : Prop :=
  ∀ Q : ℕ → Prop, Q C.output →
    (∀ j, isO C j → Q (N + N + j) → Q (lt C j) ∧ Q (rt C j)) →
    (∀ j, isA C j → Q (N + N + j) → (V C ∅ X (rt C j) → Q (lt C j)) ∧
      (V C ∅ X (lt C j) → Q (rt C j))) → Q w

section
variable {N : ℕ} {C : Circuit} (H : IsAO2 (N + N) C)
include H

lemma ao : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
  fun g hg => ⟨H.1 g hg, (H.2.2 g hg).le⟩

lemma isAO (j : ℕ) (hj : j < C.gates.length) : isA C j ∨ isO C j := by
  have he : C.gates.getD j ⟨GateOp.and, []⟩ = C.gates[j] := List.getD_eq_getElem _ _ hj
  rcases H.1 _ (List.getElem_mem hj) with h | h
  · exact Or.inl ⟨hj, by rw [he, h]⟩
  · exact Or.inr ⟨hj, by rw [he, h]⟩

lemma ins (j : ℕ) (hj : j < C.gates.length) : C.gates[j].inputs = [lt C j, rt C j] := by
  have he : C.gates.getD j ⟨GateOp.and, []⟩ = C.gates[j] := List.getD_eq_getElem _ _ hj
  have h2 := H.2.2 _ (List.getElem_mem hj)
  unfold lt rt
  rw [he]
  match hL : C.gates[j].inputs, h2 with
  | [a, b], _ => rfl

lemma back (j : ℕ) (hj : j < C.gates.length) : lt C j < N + N + j ∧ rt C j < N + N + j := by
  have hb := H.2.1
  have hi := ins H j hj
  have hg : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hj]
  have h2 := hb j hj
  rw [hg, hi] at h2
  exact ⟨h2 _ (by simp), h2 _ (by simp)⟩

lemma V_and (j : ℕ) (h : isA C j) (P X : Finset (Fin N)) :
    V C P X (N + N + j) ↔ V C P X (lt C j) ∧ V C P X (rt C j) := by
  obtain ⟨hj, ho⟩ := h
  rw [List.getD_eq_getElem _ _ hj] at ho
  obtain ⟨hb1, hb2⟩ := back H j hj
  unfold V
  rw [and_val C j hj ho, ins H j hj]
  simp [hb1, hb2]

lemma V_or (j : ℕ) (h : isO C j) (P X : Finset (Fin N)) :
    V C P X (N + N + j) ↔ V C P X (lt C j) ∨ V C P X (rt C j) := by
  obtain ⟨hj, ho⟩ := h
  rw [List.getD_eq_getElem _ _ hj] at ho
  obtain ⟨hb1, hb2⟩ := back H j hj
  unfold V
  rw [or_val C j hj ho, ins H j hj]
  simp [hb1, hb2]

lemma V_mono {P P' X X' : Finset (Fin N)} (hP : P ⊆ P') (hX : X ⊆ X') (w : ℕ)
    (h : V C P X w) : V C P' X' w := by
  refine value_mono C (ao H) _ _ (fun v => ?_) w h
  refine Fin.addCases (fun p => ?_) (fun l => ?_) v
  · rw [io_p, io_p, decide_eq_true_eq, decide_eq_true_eq]
    exact fun h => hP h
  · rw [io_l, io_l, decide_eq_true_eq, decide_eq_true_eq]
    exact fun h => hX h

lemma K_mono {X Y : Finset (Fin N)} (hX : X ⊆ Y) (w : ℕ) (h : K C X w) : K C Y w := by
  intro Q h0 h1 h2
  exact h Q h0 h1 fun j hj hQ => ⟨fun hv => (h2 j hj hQ).1 (V_mono H (subset_refl _) hX _ hv),
    fun hv => (h2 j hj hQ).2 (V_mono H (subset_refl _) hX _ hv)⟩

lemma K_out {P X : Finset (Fin N)} (w : ℕ) (h : K C X w) : V C P X w → V C P X C.output := by
  refine h (fun w => V C P X w → V C P X C.output) (fun h => h) (fun j hj hQ => ?_)
    (fun j hj hQ => ?_)
  · exact ⟨fun h => hQ ((V_or H j hj P X).mpr (Or.inl h)),
      fun h => hQ ((V_or H j hj P X).mpr (Or.inr h))⟩
  · exact ⟨fun h1 h2 => hQ ((V_and H j hj P X).mpr
        ⟨h2, V_mono H (Finset.empty_subset _) (subset_refl _) _ h1⟩),
      fun h1 h2 => hQ ((V_and H j hj P X).mpr
        ⟨V_mono H (Finset.empty_subset _) (subset_refl _) _ h1, h2⟩)⟩

omit H in
lemma K_or {X : Finset (Fin N)} (j : ℕ) (hj : isO C j) (h : K C X (N + N + j)) :
    K C X (lt C j) ∧ K C X (rt C j) :=
  ⟨fun Q h0 h1 h2 => (h1 j hj (h Q h0 h1 h2)).1, fun Q h0 h1 h2 => (h1 j hj (h Q h0 h1 h2)).2⟩

omit H in
lemma K_and {X : Finset (Fin N)} (j : ℕ) (hj : isA C j) (h : K C X (N + N + j)) :
    (V C ∅ X (rt C j) → K C X (lt C j)) ∧ (V C ∅ X (lt C j) → K C X (rt C j)) :=
  ⟨fun hv Q h0 h1 h2 => (h2 j hj (h Q h0 h1 h2)).1 hv,
    fun hv Q h0 h1 h2 => (h2 j hj (h Q h0 h1 h2)).2 hv⟩

omit H in
lemma K_base (X : Finset (Fin N)) : K C X C.output := fun _ h0 _ _ => h0

-- the input read on side b, and the other one
def tg (C : Circuit) (e : ℕ × Bool) : ℕ := if e.2 then rt C e.1 else lt C e.1
def ot (C : Circuit) (e : ℕ × Bool) : ℕ := if e.2 then lt C e.1 else rt C e.1

omit H in
lemma K_inv {X : Finset (Fin N)} (w : ℕ) (h : K C X w) : w = C.output ∨
    ∃ e : ℕ × Bool, tg C e = w ∧ K C X (N + N + e.1) ∧
      (isO C e.1 ∨ (isA C e.1 ∧ V C ∅ X (ot C e))) := by
  have := h (fun w => K C X w ∧ (w = C.output ∨ ∃ e : ℕ × Bool, tg C e = w ∧ K C X (N + N + e.1) ∧
      (isO C e.1 ∨ (isA C e.1 ∧ V C ∅ X (ot C e))))) ⟨K_base X, Or.inl rfl⟩
    (fun j hj hQ => ⟨⟨(K_or j hj hQ.1).1, Or.inr ⟨(j, false), rfl, hQ.1, Or.inl hj⟩⟩,
      (K_or j hj hQ.1).2, Or.inr ⟨(j, true), rfl, hQ.1, Or.inl hj⟩⟩)
    (fun j hj hQ => ⟨fun hv => ⟨(K_and j hj hQ.1).1 hv,
        Or.inr ⟨(j, false), rfl, hQ.1, Or.inr ⟨hj, hv⟩⟩⟩,
      fun hv => ⟨(K_and j hj hQ.1).2 hv, Or.inr ⟨(j, true), rfl, hQ.1, Or.inr ⟨hj, hv⟩⟩⟩⟩)
  exact this.2

-- nodes: a wire, a context of a wire, a contribution to a context through an AND gate
def T {N : ℕ} (C : Circuit) (X : Finset (Fin N)) : ℕ ⊕ ℕ ⊕ (ℕ × Bool) → Prop
  | Sum.inl w => V C ∅ X w
  | Sum.inr (Sum.inl w) => K C X w
  | Sum.inr (Sum.inr e) => isA C e.1 ∧ K C X (N + N + e.1) ∧ V C ∅ X (ot C e)

def rk (N : ℕ) (C : Circuit) : ℕ ⊕ ℕ ⊕ (ℕ × Bool) → ℕ
  | Sum.inl w => w
  | Sum.inr (Sum.inl w) => N + N + C.gates.length + 2 * (N + N + C.gates.length - w)
  | Sum.inr (Sum.inr e) => N + N + C.gates.length + 2 * (N + N + C.gates.length - (N + N + e.1)) + 1

def kid (N : ℕ) (C : Circuit) : ℕ ⊕ ℕ ⊕ (ℕ × Bool) → Bool → ℕ ⊕ ℕ ⊕ (ℕ × Bool)
  | Sum.inl w, b => Sum.inl (tg C (w - (N + N), b))
  | Sum.inr (Sum.inl w), _ => Sum.inl w
  | Sum.inr (Sum.inr e), false => Sum.inr (Sum.inl (N + N + e.1))
  | Sum.inr (Sum.inr e), true => Sum.inl (ot C e)

noncomputable def Ai (C : Circuit) : Finset ℕ := (Finset.range C.gates.length).filter (isA C)
noncomputable def Oi (C : Circuit) : Finset ℕ := (Finset.range C.gates.length).filter (isO C)
def edg (C : Circuit) : Finset (ℕ × Bool) := (Finset.range C.gates.length) ×ˢ Finset.univ

noncomputable def AA (N : ℕ) (C : Circuit) : Finset (ℕ ⊕ ℕ ⊕ (ℕ × Bool)) :=
  (Ai C).image (fun j => Sum.inl (N + N + j)) ∪
    (Ai C ×ˢ (Finset.univ : Finset Bool)).image (fun e => Sum.inr (Sum.inr e))

noncomputable def B1 (N : ℕ) (C : Circuit) : Finset (ℕ ⊕ ℕ ⊕ (ℕ × Bool)) :=
  (Oi C).image (fun j => Sum.inl (N + N + j))

noncomputable def B2 (N : ℕ) (C : Circuit) : Finset (ℕ ⊕ ℕ ⊕ (ℕ × Bool)) :=
  (Finset.range (N + N + C.gates.length)).image (fun w => Sum.inr (Sum.inl w))

noncomputable def cc (C : Circuit) : ℕ ⊕ ℕ ⊕ (ℕ × Bool) → ℕ
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl w) => ((edg C).filter fun e => tg C e = w).card
  | Sum.inr (Sum.inr _) => 0

omit H in
lemma mem_edg (e : ℕ × Bool) (h : isO C e.1 ∨ isA C e.1) : e ∈ edg C := by
  refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_univ _⟩
  rcases h with h | h <;> exact h.1

lemma tg_lt (e : ℕ × Bool) (h : e.1 < C.gates.length) :
    tg C e < N + N + e.1 ∧ ot C e < N + N + e.1 := by
  obtain ⟨h1, h2⟩ := back H e.1 h
  obtain ⟨j, b⟩ := e
  cases b
  · exact ⟨h1, h2⟩
  · exact ⟨h2, h1⟩

lemma T_mono (X Y : Finset (Fin N)) (i : ℕ ⊕ ℕ ⊕ (ℕ × Bool)) (h : X ⊆ Y) (hi : T C X i) :
    T C Y i := by
  rcases i with w | w | e
  · exact V_mono H (subset_refl _) h w hi
  · exact K_mono H h w hi
  · exact ⟨hi.1, K_mono H h _ hi.2.1, V_mono H (subset_refl _) h _ hi.2.2⟩

lemma nodes : Nodes (T (N := N) C) (rk N C) (AA N C) (B1 N C ∪ B2 N C) (cc C) (kid N C) := by
  intro i hi
  rcases i with w | w | e
  · by_cases hn : w < N + N
    · exfalso
      obtain ⟨s, hs, t, ht, hst⟩ := Finset.one_lt_card.mp hi
      have key : ∀ l : Fin N, l ∈ Sing (T (N := N) C) (Sum.inl w) → w = N + l := by
        intro l hl
        have hv : value C (io ∅ {l}) w = true := (Finset.mem_filter.mp hl).2
        rw [input_value C _ ⟨w, hn⟩] at hv
        have gen : ∀ v : Fin (N + N), io ∅ {l} v = true → (v : ℕ) = N + l := by
          intro v
          refine Fin.addCases (fun p => ?_) (fun l' => ?_) v
          · rw [io_p]
            simp
          · rw [io_l]
            intro h
            simp only [Finset.mem_singleton, decide_eq_true_eq] at h
            rw [h]
            rfl
        exact gen _ hv
      have h1 := key s hs
      have h2 := key t ht
      exact hst (Fin.ext (by omega))
    by_cases hw : w < N + N + C.gates.length
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
      have hj : j < C.gates.length := by omega
      obtain ⟨b1, b2⟩ := back H j hj
      rcases isAO H j hj with h | h
      · refine Or.inr (Or.inl ⟨?_, fun b => ?_, fun X => ?_⟩)
        · exact Finset.mem_union_left _ (Finset.mem_image.mpr
            ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, h⟩, rfl⟩)
        · simp only [kid, rk, Nat.add_sub_cancel_left]
          exact (tg_lt H (j, b) hj).1
        · simp only [kid, T, Nat.add_sub_cancel_left]
          exact V_and H j h ∅ X
      · refine Or.inr (Or.inr ⟨{Sum.inl (lt C j), Sum.inl (rt C j)}, fun a ha => ?_, ?_, fun X => ?_⟩)
        · rcases Finset.mem_insert.mp ha with rfl | ha
          · exact b1
          · rw [Finset.mem_singleton.mp ha]
            exact b2
        · have hm : (Sum.inl (N + N + j) : ℕ ⊕ ℕ ⊕ (ℕ × Bool)) ∈ B1 N C ∪ B2 N C :=
            Finset.mem_union_left _ (Finset.mem_image.mpr
              ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, h⟩, rfl⟩)
          rw [ite_eq_left hm]
          exact Finset.card_le_two
        · simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left, T]
          exact V_or H j h ∅ X
    · exfalso
      have : Sing (T (N := N) C) (Sum.inl w) = ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun l _ hl => ?_
        have hv : value C (io ∅ {l}) w = true := hl
        rw [missing_value C _ w (by unfold Circuit.size; omega)] at hv
        exact Bool.noConfusion hv
      rw [this] at hi
      simp at hi
  · by_cases ho : w = C.output
    · refine Or.inl fun X => ?_
      rw [ho]
      exact K_base X
    refine Or.inr (Or.inr ⟨((edg C).filter fun e => tg C e = w).image fun e =>
      if isA C e.1 then Sum.inr (Sum.inr e) else Sum.inr (Sum.inl (N + N + e.1)),
      fun a ha => ?_, ?_, fun X => ⟨fun hK => ?_, ?_⟩⟩)
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp he
      have hj := Finset.mem_range.mp (Finset.mem_product.mp h1).1
      have hlt := (tg_lt H e hj).1
      rw [h2] at hlt
      split
      · simp only [rk]
        omega
      · simp only [rk]
        omega
    · have hc := Finset.card_image_le (s := (edg C).filter fun e => tg C e = w)
        (f := fun e => if isA C e.1 then (Sum.inr (Sum.inr e) : ℕ ⊕ ℕ ⊕ (ℕ × Bool)) else
          Sum.inr (Sum.inl (N + N + e.1)))
      by_cases hw : w < N + N + C.gates.length
      · have hm : (Sum.inr (Sum.inl w) : ℕ ⊕ ℕ ⊕ (ℕ × Bool)) ∈ B1 N C ∪ B2 N C :=
          Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w, Finset.mem_range.mpr hw, rfl⟩)
        rw [ite_eq_left hm]
        simp only [cc]
        omega
      · have : (edg C).filter (fun e => tg C e = w) = ∅ := by
          refine Finset.filter_eq_empty_iff.mpr fun e he h => ?_
          have hj := Finset.mem_range.mp (Finset.mem_product.mp he).1
          have := (tg_lt H e hj).1
          omega
        rw [this]
        simp
    · rcases K_inv w hK with h | ⟨e, h1, h2, h3⟩
      · exact absurd h ho
      · have hmem : e ∈ (edg C).filter fun e => tg C e = w :=
          Finset.mem_filter.mpr ⟨mem_edg e (h3.imp id And.left), h1⟩
        refine ⟨_, Finset.mem_image_of_mem _ hmem, ?_⟩
        by_cases hA : isA C e.1
        · rw [ite_eq_left hA]
          refine ⟨hA, h2, ?_⟩
          rcases h3 with h3 | h3
          · exact GateOp.noConfusion (hA.2.symm.trans h3.2)
          · exact h3.2
        · rw [ite_eq_right hA]
          exact h2
    · rintro ⟨a, ha, hTa⟩
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp he
      have hj := Finset.mem_range.mp (Finset.mem_product.mp h1).1
      obtain ⟨j, b⟩ := e
      by_cases hA : isA C j
      · rw [ite_eq_left hA] at hTa
        change K C X w
        rw [← h2]
        cases b
        · exact (K_and j hA hTa.2.1).1 hTa.2.2
        · exact (K_and j hA hTa.2.1).2 hTa.2.2
      · rw [ite_eq_right hA] at hTa
        have hO : isO C j := (isAO H j hj).resolve_left hA
        change K C X w
        rw [← h2]
        cases b
        · exact (K_or j hO hTa).1
        · exact (K_or j hO hTa).2
  · by_cases hA : isA C e.1
    · refine Or.inr (Or.inl ⟨?_, fun b => ?_, fun X => ?_⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_product.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hA.1, hA⟩, Finset.mem_univ _⟩))
      · cases b
        · simp only [kid, rk]
          omega
        · simp only [kid, rk]
          have := (tg_lt H e hA.1).2
          have := hA.1
          omega
      · simp only [kid, T]
        exact ⟨fun h => h.2, fun h => ⟨hA, h⟩⟩
    · exfalso
      have : Sing (T (N := N) C) (Sum.inr (Sum.inr e)) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun l _ hl => hA hl.1
      rw [this] at hi
      simp at hi

omit H in
lemma counts : (Ai C).card + (Oi C).card ≤ C.gates.length := by
  rw [← Finset.card_union_of_disjoint]
  · refine (Finset.card_le_card (t := Finset.range C.gates.length) ?_).trans (by simp)
    exact Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  · refine Finset.disjoint_left.mpr fun j h1 h2 => ?_
    have e1 := (Finset.mem_filter.mp h1).2.2
    have e2 := (Finset.mem_filter.mp h2).2.2
    exact GateOp.noConfusion (e1.symm.trans e2)

omit H in
lemma edg_card : (edg C).card = 2 * C.gates.length := by
  simp [edg, Finset.card_product, Nat.mul_comm]

omit H in
lemma AA_card : (AA N C).card ≤ 3 * (Ai C).card := by
  refine (Finset.card_union_le _ _).trans ?_
  have h1 := Finset.card_image_le (s := Ai C)
    (f := fun j => (Sum.inl (N + N + j) : ℕ ⊕ ℕ ⊕ (ℕ × Bool)))
  have h2 := Finset.card_image_le (s := Ai C ×ˢ (Finset.univ : Finset Bool))
    (f := fun e => (Sum.inr (Sum.inr e) : ℕ ⊕ ℕ ⊕ (ℕ × Bool)))
  rw [Finset.card_product, Finset.card_univ, Fintype.card_bool] at h2
  omega

lemma BB_sum : ∑ i ∈ B1 N C ∪ B2 N C, cc C i ≤ (Oi C).card + 2 * C.gates.length := by
  have h0 := Finset.sum_union_inter (s₁ := B1 N C) (s₂ := B2 N C) (f := cc C)
  have h1 : ∑ i ∈ B1 N C, cc C i = (Oi C).card := by
    unfold B1
    rw [Finset.sum_image fun a _ b _ h => by
      have := Sum.inl.inj h
      omega]
    simp [cc]
  have h2 : ∑ i ∈ B2 N C, cc C i = 2 * C.gates.length := by
    unfold B2
    rw [Finset.sum_image fun a _ b _ h => Sum.inl.inj (Sum.inr.inj h), ← edg_card (C := C)]
    refine (Finset.card_eq_sum_card_fiberwise fun e he => ?_).symm
    have hj := Finset.mem_range.mp (Finset.mem_product.mp (Finset.mem_coe.mp he)).1
    have := (tg_lt H e hj).1
    exact Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))
  omega

end
end inst

section lin
open PEqualNP.ReadK PEqualNP.MetaComplexity PEqualNP.TopForm
open Classical

def gr {β : Type} (F : List β → Gate → β) (gs : List Gate) (w : List β) : List β :=
  gs.foldl (fun w g => w ++ [F w g]) w

lemma gr_pre {β : Type} (F : List β → Gate → β) (gs : List Gate) (w : List β) :
    ∃ t, gr F gs w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [gr], rfl⟩
  | cons g gs ih =>
    obtain ⟨t, h1, h2⟩ := ih (w ++ [F w g])
    refine ⟨F w g :: t, ?_, by simp [h2]⟩
    change gr F gs (w ++ [F w g]) = _
    rw [h1]
    simp

lemma gr_gate {β : Type} (F : List β → Gate → β) (d : β) (gs : List Gate) (w : List β) (j : ℕ)
    (hj : j < gs.length) : ∃ e : List β, e.length = w.length + j ∧
      (∀ i < w.length + j, (gr F gs w).getD i d = e.getD i d) ∧
      (gr F gs w).getD (w.length + j) d = F e gs[j] := by
  obtain ⟨t, h1, h2⟩ := gr_pre F (gs.take j) w
  have hlen : (gr F (gs.take j) w).length = w.length + j := by
    rw [h1, List.length_append, h2, List.length_take, Nat.min_eq_left hj.le]
  have hs : gr F gs w = gr F (gs.drop (j + 1)) (gr F (gs.take j) w ++
      [F (gr F (gs.take j) w) gs[j]]) := by
    have he : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
    conv_lhs => rw [he]
    simp only [gr, List.foldl_append, List.foldl_cons]
  obtain ⟨t', h3, _⟩ := gr_pre F (gs.drop (j + 1)) (gr F (gs.take j) w ++
      [F (gr F (gs.take j) w) gs[j]])
  rw [h3, List.append_assoc] at hs
  refine ⟨gr F (gs.take j) w, hlen, fun i hi => ?_, ?_⟩
  · rw [hs, List.getD_append _ _ _ _ (by omega)]
  · rw [hs, List.getD_append_right _ _ _ _ (by omega), hlen]
    simp

lemma gr_old {β : Type} (F : List β → Gate → β) (d : β) (gs : List Gate) (w : List β) (i : ℕ)
    (hi : i < w.length) : (gr F gs w).getD i d = w.getD i d := by
  obtain ⟨t, h1, _⟩ := gr_pre F gs w
  rw [h1, List.getD_append _ _ _ _ hi]

lemma gr_out {β : Type} (F : List β → Gate → β) (d : β) (gs : List Gate) (w : List β) (i : ℕ)
    (hi : w.length + gs.length ≤ i) : (gr F gs w).getD i d = d := by
  obtain ⟨t, h1, h2⟩ := gr_pre F gs w
  exact List.getD_eq_default _ _ (by rw [h1, List.length_append, h2]; exact hi)

def bits (N : ℕ) (p l : ℕ) : List Bool := (List.range (N + N)).map fun i => i == p || i == l

def LP (N : ℕ) (C : Circuit) (p l : ℕ) : List (Bool × Bool) :=
  linearParts C (fun w => decide (w < N)) (bits N p l)

def FF (w : List (Bool × Bool)) (g : Gate) : Bool × Bool :=
  let ins := g.inputs.map fun i => w.getD i (false, false)
  match g.op with
        | GateOp.or  => (ins.any (·.1), ins.any (·.2))
        | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
              (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
        | _ => (false, false)

def i0 (N p l : ℕ) : List (Bool × Bool) :=
  ((bits N p l).zipIdx).map fun (b, i) => if decide (i < N) then (false, b) else (b, false)

lemma LP_gr (N : ℕ) (C : Circuit) (p l : ℕ) : LP N C p l = gr FF C.gates (i0 N p l) := rfl

lemma i0_len (N p l : ℕ) : (i0 N p l).length = N + N := by simp [i0, bits]

lemma i0_get (N p l i : ℕ) (hi : i < N + N) : (i0 N p l).getD i (false, false) =
    if i < N then (false, i == p || i == l) else (i == p || i == l, false) := by
  rw [List.getD_eq_getElem _ _ (by rw [i0_len]; exact hi)]
  simp [i0, bits]

section
variable {N : ℕ} {C : Circuit} (H : IsAO2 (N + N) C)
include H

lemma LP_and (p l j : ℕ) (h : isA C j) : (LP N C p l).getD (N + N + j) (false, false) =
    (((LP N C p l).getD (lt C j) (false, false)).1 && ((LP N C p l).getD (rt C j) (false, false)).1,
     (((LP N C p l).getD (lt C j) (false, false)).1 && ((LP N C p l).getD (rt C j) (false, false)).2) ||
     (((LP N C p l).getD (lt C j) (false, false)).2 &&
       ((LP N C p l).getD (rt C j) (false, false)).1)) := by
  obtain ⟨hj, ho⟩ := h
  rw [List.getD_eq_getElem _ _ hj] at ho
  obtain ⟨b1, b2⟩ := back H j hj
  obtain ⟨e, h1, h2, h3⟩ := gr_gate FF (false, false) C.gates (i0 N p l) j hj
  rw [i0_len] at h2 h3
  rw [LP_gr, h3, h2 _ b1, h2 _ b2]
  unfold FF
  rw [ho, ins H j hj]
  simp

lemma LP_or (p l j : ℕ) (h : isO C j) : (LP N C p l).getD (N + N + j) (false, false) =
    (((LP N C p l).getD (lt C j) (false, false)).1 || ((LP N C p l).getD (rt C j) (false, false)).1,
     ((LP N C p l).getD (lt C j) (false, false)).2 ||
       ((LP N C p l).getD (rt C j) (false, false)).2) := by
  obtain ⟨hj, ho⟩ := h
  rw [List.getD_eq_getElem _ _ hj] at ho
  obtain ⟨b1, b2⟩ := back H j hj
  obtain ⟨e, h1, h2, h3⟩ := gr_gate FF (false, false) C.gates (i0 N p l) j hj
  rw [i0_len] at h2 h3
  rw [LP_gr, h3, h2 _ b1, h2 _ b2]
  unfold FF
  rw [ho, ins H j hj]
  simp

lemma part0 (p l : Fin N) (w : ℕ) (h : ((LP N C p (N + l)).getD w (false, false)).1 = true) :
    V C ∅ {l} w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < N + N
    · rw [LP_gr, gr_old _ _ _ _ _ (by rw [i0_len]; exact hn), i0_get _ _ _ _ hn] at h
      by_cases hw : w < N
      · rw [ite_eq_left hw] at h
        exact Bool.noConfusion h
      · rw [ite_eq_right hw] at h
        have hp := p.isLt
        have hwl : w = N + l := by
          simp only [Bool.or_eq_true, beq_iff_eq] at h
          omega
        have := input_value C (io ∅ {l}) (Fin.natAdd N l)
        rw [io_l] at this
        unfold V
        rw [hwl]
        refine Eq.trans ?_ (this.trans (by simp))
        rfl
    by_cases hw : w < N + N + C.gates.length
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
      have hj : j < C.gates.length := by omega
      obtain ⟨b1, b2⟩ := back H j hj
      rcases isAO H j hj with hA | hO
      · rw [LP_and H _ _ j hA, Bool.and_eq_true] at h
        exact (V_and H j hA _ _).mpr ⟨ih _ b1 h.1, ih _ b2 h.2⟩
      · rw [LP_or H _ _ j hO, Bool.or_eq_true] at h
        exact (V_or H j hO _ _).mpr (h.imp (ih _ b1) (ih _ b2))
    · rw [LP_gr, gr_out _ _ _ _ _ (by rw [i0_len]; omega)] at h
      exact Bool.noConfusion h

lemma part1 (p l : Fin N) (w : ℕ) (h : ((LP N C p (N + l)).getD w (false, false)).2 = true)
    (hK : K C ({l} : Finset (Fin N)) w) : K C ({l} : Finset (Fin N)) p := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < N + N
    · rw [LP_gr, gr_old _ _ _ _ _ (by rw [i0_len]; exact hn), i0_get _ _ _ _ hn] at h
      by_cases hw : w < N
      · rw [ite_eq_left hw] at h
        have hwp : w = p := by
          simp only [Bool.or_eq_true, beq_iff_eq] at h
          omega
        rwa [hwp] at hK
      · rw [ite_eq_right hw] at h
        exact Bool.noConfusion h
    by_cases hw : w < N + N + C.gates.length
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
      have hj : j < C.gates.length := by omega
      obtain ⟨b1, b2⟩ := back H j hj
      rcases isAO H j hj with hA | hO
      · rw [LP_and H _ _ j hA, Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
        rcases h with h | h
        · exact ih _ b2 h.2 ((K_and j hA hK).2 (part0 H p l _ h.1))
        · exact ih _ b1 h.1 ((K_and j hA hK).1 (part0 H p l _ h.2))
      · rw [LP_or H _ _ j hO, Bool.or_eq_true] at h
        rcases h with h | h
        · exact ih _ b1 h (K_or j hO hK).1
        · exact ih _ b2 h (K_or j hO hK).2
    · rw [LP_gr, gr_out _ _ _ _ _ (by rw [i0_len]; omega)] at h
      exact Bool.noConfusion h

end

lemma degree (N q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 1 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcard : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (hI : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) (p : Fin N) :
    (Finset.univ.filter fun l => I p l).card ≤ q + 1 := by
  let D := Finset.univ.filter fun l => I p l
  let G : Fin N → Finset (Fin N) := fun l => (Finset.univ.filter fun p' => I p' l).erase p
  have h1 : (D.biUnion G).card = ∑ l ∈ D, (G l).card := by
    refine Finset.card_biUnion fun l hl l' hl' hne => ?_
    refine Finset.disjoint_left.mpr fun p' hp hp' => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_erase.mp hp
    obtain ⟨_, h3⟩ := Finset.mem_erase.mp hp'
    exact hne ((hI p p' (Ne.symm h1)).unique
      ⟨(Finset.mem_filter.mp hl).2, (Finset.mem_filter.mp h2).2⟩
      ⟨(Finset.mem_filter.mp hl').2, (Finset.mem_filter.mp h3).2⟩)
  have h2 : ∑ l ∈ D, (G l).card = D.card * q := by
    rw [Finset.sum_congr rfl (g := fun _ => q) fun l hl => ?_]
    · simp
    · have hm : p ∈ Finset.univ.filter fun p' => I p' l :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl).2⟩
      dsimp only [G]
      rw [Finset.card_erase_of_mem hm, hcard]
      rfl
  have h3 : (D.biUnion G).card ≤ (Finset.univ.erase p : Finset (Fin N)).card := by
    refine Finset.card_le_card fun x hx => ?_
    obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hl).1, Finset.mem_univ _⟩
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h3
  have h4 : D.card * q ≤ (q + 1) * q := by
    calc D.card * q ≤ N - 1 := by omega
      _ = (q + 1) * q := by rw [hN, Nat.add_sub_cancel]; ring
  exact Nat.le_of_mul_le_mul_right h4 hq

theorem final (N q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hcard : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1)
    (hI : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) (H : IsAO2 (N + N) C)
    (hrej : ∀ z : Fin (N + N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      circuitFun (N + N) C z = false) :
    Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧ lineSingle C (N + N)
      (fun w : ℕ => decide (w < N)) e.1 (N + e.2) = true} ≤ 10 * C.size := by
  have hrej' : ∀ P X : Finset (Fin N), X.card ≤ q → V C P X C.output →
      ∃ p ∈ P, ∃ l ∈ X, I p l := by
    intro P X hX hV
    by_contra hno
    have h := hrej (io P X) (by
      rw [Fintype.card_subtype]
      refine (le_of_eq (congrArg Finset.card ?_)).trans hX
      ext l
      rw [Finset.mem_filter, io_l, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩) (by
      rintro ⟨p, l, h1, h2, h3⟩
      rw [io_p, decide_eq_true_eq] at h2
      rw [io_l, decide_eq_true_eq] at h3
      exact hno ⟨p, h2, l, h3, h1⟩)
    have hV' : circuitFun (N + N) C (io P X) = true := hV
    rw [h] at hV'
    exact Bool.noConfusion hV'
  have hinp : ∀ (p : Fin N) (X : Finset (Fin N)), V C {p} X p := by
    intro p X
    have := input_value C (io {p} X) (Fin.castAdd N p)
    rw [io_p] at this
    exact this.trans (by simp)
  let w : Fin N → ℕ ⊕ ℕ ⊕ (ℕ × Bool) := fun p => Sum.inr (Sum.inl p)
  let E : Fin N → Finset (Fin N) := fun p => Finset.univ.filter fun l => I p l ∧
    lineSingle C (N + N) (fun w : ℕ => decide (w < N)) p (N + l) = true
  have hEK : ∀ p, ∀ l ∈ E p, K C ({l} : Finset (Fin N)) p := by
    intro p l hl
    exact part1 H p l C.output (Finset.mem_filter.mp hl).2.2 (K_base _)
  have hcard' : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1 := by
    intro l
    rw [← hcard l, Fintype.card_subtype]
  have key := promise_ledger (T (N := N) C) (T_mono H) (rk N C) (AA N C) (B1 N C ∪ B2 N C) (cc C)
    (kid N C) (nodes H) q (by omega) (fun p => Finset.univ.filter fun l => I p l)
    (fun p p' hne s hs t ht hs' ht' => (hI p p' hne).unique
      ⟨(Finset.mem_filter.mp hs).2, (Finset.mem_filter.mp hs').2⟩
      ⟨(Finset.mem_filter.mp ht).2, (Finset.mem_filter.mp ht').2⟩) w
    (fun p X hX hK => by
      obtain ⟨p', hp', l, hl, hi⟩ := hrej' {p} X hX (K_out H (p : ℕ) hK (hinp p X))
      rw [Finset.mem_singleton.mp hp'] at hi
      exact ⟨l, hl, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩) E
    (fun p l hl => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hEK p l hl⟩)
    (fun p => (Finset.card_le_card fun l hl => Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl).2.1⟩).trans
      (degree N q I (by omega) hN hcard' hI p))
  have hne : (Finset.univ.filter fun p => (E p).Nonempty).card ≤ 2 * C.gates.length := by
    rw [← edg_card (C := C)]
    refine le_trans ?_ (Finset.card_image_le (s := edg C) (f := tg C))
    refine Finset.card_le_card_of_injOn (fun p : Fin N => (p : ℕ)) (fun p hp => ?_)
      (fun a _ b _ h => Fin.ext h)
    obtain ⟨l, hl⟩ := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2
    rcases K_inv (p : ℕ) (hEK p l hl) with ho | ⟨e, h1, h2, h3⟩
    · exfalso
      have hv := hinp p ∅
      rw [ho] at hv
      obtain ⟨_, _, l, hl, _⟩ := hrej' {p} ∅ (by simp) hv
      simp at hl
    · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨e, mem_edg e (h3.imp id And.left), h1⟩)
  have hsum : Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧ lineSingle C (N + N)
      (fun w : ℕ => decide (w < N)) e.1 (N + e.2) = true} = ∑ p, (E p).card := by
    rw [Fintype.card_subtype]
    simp only [E, Finset.card_filter]
    rw [Fintype.sum_prod_type]
  have h1 := BB_sum H
  have h2 := AA_card (N := N) (C := C)
  have h3 := counts (C := C)
  rw [hsum]
  unfold Circuit.size
  omega

end lin

end PEqualNP.Outside.L_meta_2972

theorem PEqualNP.Outside.L_meta_2972 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ PEqualNP.ReadK.lineSingle x5 (x2 + x2) (fun (x13 : ℕ) => Decidable.decide (x13 < x2)) (↑x12.1) (x2 + ↑x12.2) = Bool.true } ≤ (10 : ℕ) * x5.size := by
  intro q N I _ C hq hN hcard hI H hrej
  exact PEqualNP.Outside.L_meta_2972.final N q I C hq hN hcard hI H hrej
