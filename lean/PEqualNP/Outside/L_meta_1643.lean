import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1643

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

def Sv {n : ℕ} {ι : Type*} (C : Circuit) (l : ι → Fin n → Bool) (y : Fin n → Bool)
    (p : ι) (w : ℕ) : Prop :=
  value C (l p) w = true ∧ value C y w = false

def Multi {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (y : Fin n → Bool) (w : ℕ) : Prop :=
  ∃ p ∈ T, ∃ p' ∈ T, p ≠ p' ∧ Sv C l y p w ∧ Sv C l y p' w

lemma count {N m q : ℕ} (K : Fin m → Finset (Fin N)) (hq : ∀ i, q ≤ (K i).card)
    (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j)) : m * q ≤ (Finset.univ.biUnion K).card := by
  rw [Finset.card_biUnion (fun i _ j _ hij => hd i j hij)]
  have h2 : ∑ _i : Fin m, q ≤ ∑ i : Fin m, (K i).card := Finset.sum_le_sum fun i _ => hq i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  exact h2

lemma and_false {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : C.gates[k].op = GateOp.and) (htopo : ∀ w ∈ C.gates[k].inputs, w < n + k)
    (x : Fin n → Bool) (h : value C x (n + k) = false) :
    ∃ r ∈ C.gates[k].inputs, value C x r = false := by
  by_contra hcon
  have h2 : value C x (n + k) = true := (and_value C k hk hop x).mpr fun r hr =>
    ⟨htopo r hr, by
      by_contra hne
      exact hcon ⟨r, hr, by simpa using hne⟩⟩
  rw [h] at h2
  exact Bool.noConfusion h2

lemma multi_lt {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (y : Fin n → Bool) (w : ℕ) (h : Multi C T l y w) : w < n + C.gates.length := by
  by_contra hge
  obtain ⟨p, _, _, _, _, hsv, _⟩ := h
  have hm := missing_value C (l p) w (by unfold Circuit.size; omega)
  have h1 := hsv.1
  rw [hm] at h1
  exact Bool.noConfusion h1

lemma filter_step (W : Finset ℕ) (t : ℕ) (h : t ∈ W) :
    (W.filter (· < t + 1)).card = (W.filter (· < t)).card + 1 := by
  have e : W.filter (· < t + 1) = insert t (W.filter (· < t)) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hg, hlt⟩
      by_cases hw : w = t
      · exact Or.inl hw
      · exact Or.inr ⟨hg, by omega⟩
    · rintro (hw | ⟨hg, hlt⟩)
      · rw [hw]
        exact ⟨h, by omega⟩
      · exact ⟨hg, by omega⟩
  rw [e, Finset.card_insert_of_notMem (by simp)]

lemma filter_le (W : Finset ℕ) (t : ℕ) :
    (W.filter (· < t)).card ≤ (W.filter (· < t + 1)).card :=
  Finset.card_le_card fun w hw =>
    Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, by
      have := (Finset.mem_filter.mp hw).2
      omega⟩

lemma frontier2 {n : ℕ} {ι κ : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (y : Fin n → Bool) (Z : Finset κ) (yy : κ → Fin n → Bool)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (W A : Finset ℕ)
    (hW : ∀ k, ∀ hk : k < C.gates.length, C.gates[k].op = GateOp.or → Multi C T l y (n + k) →
      (∀ s ∈ Z, value C (yy s) (n + k) = true) → n + k ∈ W)
    (hA : ∀ k, ∀ hk : k < C.gates.length, C.gates[k].op = GateOp.and →
      value C y (n + k) = false → (∃ p ∈ T, value C (l p) (n + k) = true) →
      (∃ s ∈ Z, value C (yy s) (n + k) = false ∧
        ∀ r ∈ C.gates[k].inputs, ¬ (value C y r = false ∧ value C (yy s) r = false)) → n + k ∈ A)
    (hin : ∀ w, w < n → ¬ Multi C T l y w)
    (hbase : ∀ s ∈ Z, ∀ p ∈ T, ∀ p' ∈ T, ∀ w w' : ℕ, w < n → w' < n → Sv C l y p w →
      Sv C l y p' w' → value C (yy s) w = false → value C (yy s) w' = false → p = p')
    (T' : Finset ι) (hT' : T' ⊆ T) :
    ∀ d : ℕ, d ≤ C.gates.length → ∀ (F : Finset ℕ) (M : Finset κ), M ⊆ Z →
    (∀ w ∈ F, Multi C T l y w → w < n + d) →
    (∀ p ∈ T', (∃ w ∈ F, Sv C l y p w) ∨
      ∃ s ∈ M, ∃ w, w < n + d ∧ Sv C l y p w ∧ value C (yy s) w = false) →
    T'.card ≤ F.card + M.card + (W.filter (· < n + d)).card + (A.filter (· < n + d)).card := by
  classical
  intro d
  induction d with
  | zero =>
    intro _ F M hM hF hs
    have h1 : (T'.filter fun p => ∃ w ∈ F, Sv C l y p w).card ≤ F.card := by
      refine Finset.card_le_card_of_forall_subsingleton (fun p w => Sv C l y p w)
        (fun p hp => ?_) (fun w hw => ?_)
      · obtain ⟨w, hw, h⟩ := (Finset.mem_filter.mp hp).2
        exact ⟨w, hw, h⟩
      · intro p hp p' hp'
        by_contra hne
        have hm : Multi C T l y w :=
          ⟨p, hT' (Finset.mem_filter.mp hp.1).1, p', hT' (Finset.mem_filter.mp hp'.1).1, hne,
            hp.2, hp'.2⟩
        have hlt := hF w hw hm
        exact hin w (by omega) hm
    have h2 : (T'.filter fun p => ∃ s ∈ M, ∃ w, w < n ∧ Sv C l y p w ∧
        value C (yy s) w = false).card ≤ M.card := by
      refine Finset.card_le_card_of_forall_subsingleton
        (fun p s => ∃ w, w < n ∧ Sv C l y p w ∧ value C (yy s) w = false)
        (fun p hp => ?_) (fun s hsM => ?_)
      · obtain ⟨s, hsM, h⟩ := (Finset.mem_filter.mp hp).2
        exact ⟨s, hsM, h⟩
      · intro p hp p' hp'
        obtain ⟨w, hw, hsv, hyw⟩ := hp.2
        obtain ⟨w', hw', hsv', hyw'⟩ := hp'.2
        exact hbase s (hM hsM) p (hT' (Finset.mem_filter.mp hp.1).1) p'
          (hT' (Finset.mem_filter.mp hp'.1).1) w w' hw hw' hsv hsv' hyw hyw'
    have hsub : T' ⊆ (T'.filter fun p => ∃ w ∈ F, Sv C l y p w) ∪
        (T'.filter fun p => ∃ s ∈ M, ∃ w, w < n ∧ Sv C l y p w ∧
          value C (yy s) w = false) := by
      intro p hp
      rcases hs p hp with h | ⟨s, hsM, w, hw, h3, h4⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, h⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hp, s, hsM, w, by omega, h3, h4⟩)
    have h3 := Finset.card_le_card hsub
    have h4 := Finset.card_union_le (T'.filter fun p => ∃ w ∈ F, Sv C l y p w)
      (T'.filter fun p => ∃ s ∈ M, ∃ w, w < n ∧ Sv C l y p w ∧ value C (yy s) w = false)
    omega
  | succ d ih =>
    intro hd F M hM hF hs
    have hk : d < C.gates.length := by omega
    have hdl : d ≤ C.gates.length := by omega
    have hWle : (W.filter (· < n + d)).card ≤ (W.filter (· < n + (d + 1))).card :=
      filter_le W (n + d)
    have hAle : (A.filter (· < n + d)).card ≤ (A.filter (· < n + (d + 1))).card :=
      filter_le A (n + d)
    have hWs : n + d ∈ W →
        (W.filter (· < n + (d + 1))).card = (W.filter (· < n + d)).card + 1 :=
      fun h => filter_step W (n + d) h
    have hAs : n + d ∈ A →
        (A.filter (· < n + (d + 1))).card = (A.filter (· < n + d)).card + 1 :=
      fun h => filter_step A (n + d) h
    have keep : (∀ w ∈ F, Multi C T l y w → w ≠ n + d) →
        (∀ p ∈ T', ∀ s ∈ M, Sv C l y p (n + d) → value C (yy s) (n + d) = false →
          ∃ w, w < n + d ∧ Sv C l y p w ∧ value C (yy s) w = false) →
        T'.card ≤ F.card + M.card + (W.filter (· < n + (d + 1))).card +
          (A.filter (· < n + (d + 1))).card := by
      intro hne hpush
      have hF' : ∀ w ∈ F, Multi C T l y w → w < n + d := by
        intro w hw hm
        have h1 := hF w hw hm
        have h2 := hne w hw hm
        omega
      have hs' : ∀ p ∈ T', (∃ w ∈ F, Sv C l y p w) ∨
          ∃ s ∈ M, ∃ w, w < n + d ∧ Sv C l y p w ∧ value C (yy s) w = false := by
        intro p hp
        rcases hs p hp with h | ⟨s, hsM, w, hw, hsv, hyy⟩
        · exact Or.inl h
        · by_cases h : w = n + d
          · rw [h] at hsv hyy
            exact Or.inr ⟨s, hsM, hpush p hp s hsM hsv hyy⟩
          · exact Or.inr ⟨s, hsM, w, by omega, hsv, hyy⟩
      have hi := ih hdl F M hM hF' hs'
      omega
    by_cases huse : ∃ p ∈ T, Sv C l y p (n + d)
    swap
    · refine keep (fun w _ hm hw => ?_) (fun p hp s _ hsv _ => absurd ⟨p, hT' hp, hsv⟩ huse)
      rw [hw] at hm
      obtain ⟨p, hp, _, _, _, hsv, _⟩ := hm
      exact huse ⟨p, hp, hsv⟩
    obtain ⟨pu, hpu, hsvu⟩ := huse
    have hy : value C y (n + d) = false := hsvu.2
    rcases (hC _ (List.getElem_mem hk)).1 with hop | hop
    · have hall : ∀ p, Sv C l y p (n + d) →
          ∀ r ∈ C.gates[d].inputs, r < n + d ∧ value C (l p) r = true :=
        fun p hsv => (and_value C d hk hop (l p)).mp hsv.1
      obtain ⟨r0, hr0m, hr0y⟩ := and_false C d hk hop (fun w hw => (hall pu hsvu w hw).1) y hy
      have hr0lt : r0 < n + d := (hall pu hsvu r0 hr0m).1
      have hsv0 : ∀ p, Sv C l y p (n + d) → Sv C l y p r0 :=
        fun p hsv => ⟨(hall p hsv r0 hr0m).2, hr0y⟩
      have hF' : ∀ w ∈ insert r0 (F.erase (n + d)), Multi C T l y w → w < n + d := by
        intro w hw hm
        rcases Finset.mem_insert.mp hw with h | h
        · rw [h]
          exact hr0lt
        · have h1 := hF w (Finset.mem_erase.mp h).2 hm
          have h2 := (Finset.mem_erase.mp h).1
          omega
      by_cases hsp : ∃ s ∈ Z, value C (yy s) (n + d) = false ∧
          ∀ r ∈ C.gates[d].inputs, ¬ (value C y r = false ∧ value C (yy s) r = false)
      · have hAmem : n + d ∈ A := hA d hk hop hy ⟨pu, hpu, hsvu.1⟩ hsp
        have hs' : ∀ p ∈ T', (∃ w ∈ insert r0 (F.erase (n + d)), Sv C l y p w) ∨
            ∃ s ∈ M, ∃ w, w < n + d ∧ Sv C l y p w ∧ value C (yy s) w = false := by
          intro p hp
          rcases hs p hp with ⟨w, hw, hsv⟩ | ⟨s, hsM, w, hw, hsv, hyy⟩
          · by_cases h : w = n + d
            · rw [h] at hsv
              exact Or.inl ⟨r0, Finset.mem_insert_self _ _, hsv0 p hsv⟩
            · exact Or.inl ⟨w, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h, hw⟩), hsv⟩
          · by_cases h : w = n + d
            · rw [h] at hsv
              exact Or.inl ⟨r0, Finset.mem_insert_self _ _, hsv0 p hsv⟩
            · exact Or.inr ⟨s, hsM, w, by omega, hsv, hyy⟩
        have hi := ih hdl (insert r0 (F.erase (n + d))) M hM hF' hs'
        have c1 := Finset.card_insert_le r0 (F.erase (n + d))
        have c2 := Finset.card_erase_le (s := F) (a := n + d)
        have c3 := hAs hAmem
        omega
      · have hsp' : ∀ s ∈ Z, value C (yy s) (n + d) = false →
            ∃ r ∈ C.gates[d].inputs, value C y r = false ∧ value C (yy s) r = false := by
          intro s hsZ hv
          by_contra hcon
          exact hsp ⟨s, hsZ, hv, fun r hr hb => hcon ⟨r, hr, hb⟩⟩
        have hpush : ∀ p ∈ T', ∀ s ∈ M, Sv C l y p (n + d) → value C (yy s) (n + d) = false →
            ∃ w, w < n + d ∧ Sv C l y p w ∧ value C (yy s) w = false := by
          intro p _ s hsM hsv hyy
          obtain ⟨r, hr, hry, hryy⟩ := hsp' s (hM hsM) hyy
          exact ⟨r, (hall p hsv r hr).1, ⟨(hall p hsv r hr).2, hry⟩, hryy⟩
        by_cases hmem : n + d ∈ F
        · have hs' : ∀ p ∈ T', (∃ w ∈ insert r0 (F.erase (n + d)), Sv C l y p w) ∨
              ∃ s ∈ M, ∃ w, w < n + d ∧ Sv C l y p w ∧ value C (yy s) w = false := by
            intro p hp
            rcases hs p hp with ⟨w, hw, hsv⟩ | ⟨s, hsM, w, hw, hsv, hyy⟩
            · by_cases h : w = n + d
              · rw [h] at hsv
                exact Or.inl ⟨r0, Finset.mem_insert_self _ _, hsv0 p hsv⟩
              · exact Or.inl ⟨w, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h, hw⟩), hsv⟩
            · by_cases h : w = n + d
              · rw [h] at hsv hyy
                exact Or.inr ⟨s, hsM, hpush p hp s hsM hsv hyy⟩
              · exact Or.inr ⟨s, hsM, w, by omega, hsv, hyy⟩
          have hi := ih hdl (insert r0 (F.erase (n + d))) M hM hF' hs'
          have c1 := Finset.card_insert_le r0 (F.erase (n + d))
          have c2 := Finset.card_erase_add_one hmem
          omega
        · exact keep (fun w hw _ h => hmem (h ▸ hw)) hpush
    · have hyall : ∀ x : Fin n → Bool, value C x (n + d) = false →
          ∀ r ∈ C.gates[d].inputs, r < n + d → value C x r = false := by
        intro x hx r hr hlt
        by_contra h
        have h2 : value C x (n + d) = true :=
          (or_value C d hk hop x).mpr ⟨r, hr, hlt, by simpa using h⟩
        rw [hx] at h2
        exact Bool.noConfusion h2
      have hdown : ∀ p, Sv C l y p (n + d) →
          ∃ r ∈ C.gates[d].inputs, r < n + d ∧ Sv C l y p r := by
        intro p hsv
        obtain ⟨r, hr, hlt, hv⟩ := (or_value C d hk hop (l p)).mp hsv.1
        exact ⟨r, hr, hlt, hv, hyall y hsv.2 r hr hlt⟩
      have hpush : ∀ p ∈ T', ∀ s ∈ M, Sv C l y p (n + d) → value C (yy s) (n + d) = false →
          ∃ w, w < n + d ∧ Sv C l y p w ∧ value C (yy s) w = false := by
        intro p _ s _ hsv hyy
        obtain ⟨r, hr, hlt, hsr⟩ := hdown p hsv
        exact ⟨r, hlt, hsr, hyall (yy s) hyy r hr hlt⟩
      by_cases hmem : n + d ∈ F
      swap
      · exact keep (fun w hw _ h => hmem (h ▸ hw)) hpush
      by_cases hlow : ∃ s ∈ Z, value C (yy s) (n + d) = false
      · obtain ⟨s0, hs0Z, hs0⟩ := hlow
        have hM' : insert s0 M ⊆ Z := Finset.insert_subset hs0Z hM
        have hF' : ∀ w ∈ F.erase (n + d), Multi C T l y w → w < n + d := by
          intro w hw hm
          have h1 := hF w (Finset.mem_erase.mp hw).2 hm
          have h2 := (Finset.mem_erase.mp hw).1
          omega
        have hs' : ∀ p ∈ T', (∃ w ∈ F.erase (n + d), Sv C l y p w) ∨
            ∃ s ∈ insert s0 M, ∃ w, w < n + d ∧ Sv C l y p w ∧ value C (yy s) w = false := by
          intro p hp
          rcases hs p hp with ⟨w, hw, hsv⟩ | ⟨s, hsM, w, hw, hsv, hyy⟩
          · by_cases h : w = n + d
            · rw [h] at hsv
              obtain ⟨r, hr, hlt, hsr⟩ := hdown p hsv
              exact Or.inr ⟨s0, Finset.mem_insert_self _ _, r, hlt, hsr,
                hyall (yy s0) hs0 r hr hlt⟩
            · exact Or.inl ⟨w, Finset.mem_erase.mpr ⟨h, hw⟩, hsv⟩
          · by_cases h : w = n + d
            · rw [h] at hsv hyy
              exact Or.inr ⟨s, Finset.mem_insert_of_mem hsM, hpush p hp s hsM hsv hyy⟩
            · exact Or.inr ⟨s, Finset.mem_insert_of_mem hsM, w, by omega, hsv, hyy⟩
        have hi := ih hdl (F.erase (n + d)) (insert s0 M) hM' hF' hs'
        have c1 := Finset.card_erase_add_one hmem
        have c2 := Finset.card_insert_le s0 M
        omega
      · have hhigh : ∀ s ∈ Z, value C (yy s) (n + d) = true := by
          intro s hsZ
          by_contra h
          exact hlow ⟨s, hsZ, by simpa using h⟩
        by_cases hmu : Multi C T l y (n + d)
        swap
        · exact keep (fun w _ hm h => hmu (h ▸ hm)) hpush
        have hWmem : n + d ∈ W := hW d hk hop hmu hhigh
        have hPcard : ((C.gates[d].inputs.filter (· < n + d)).toFinset).card ≤ 2 := by
          have h1 := List.toFinset_card_le (C.gates[d].inputs.filter (· < n + d))
          have h2 := List.length_filter_le (fun r => decide (r < n + d)) C.gates[d].inputs
          have h3 := (hC _ (List.getElem_mem hk)).2
          omega
        have hF' : ∀ w ∈ F.erase (n + d) ∪ (C.gates[d].inputs.filter (· < n + d)).toFinset,
            Multi C T l y w → w < n + d := by
          intro w hw hm
          rcases Finset.mem_union.mp hw with hw | hw
          · have h1 := hF w (Finset.mem_erase.mp hw).2 hm
            have h2 := (Finset.mem_erase.mp hw).1
            omega
          · have := (List.mem_filter.mp (List.mem_toFinset.mp hw)).2
            simpa using this
        have hs' : ∀ p ∈ T',
            (∃ w ∈ F.erase (n + d) ∪ (C.gates[d].inputs.filter (· < n + d)).toFinset,
              Sv C l y p w) ∨
            ∃ s ∈ M, ∃ w, w < n + d ∧ Sv C l y p w ∧ value C (yy s) w = false := by
          intro p hp
          rcases hs p hp with ⟨w, hw, hsv⟩ | ⟨s, hsM, w, hw, hsv, hyy⟩
          · by_cases h : w = n + d
            · rw [h] at hsv
              obtain ⟨r, hr, hlt, hsr⟩ := hdown p hsv
              exact Or.inl ⟨r, Finset.mem_union_right _ (List.mem_toFinset.mpr
                (List.mem_filter.mpr ⟨hr, by simpa using hlt⟩)), hsr⟩
            · exact Or.inl ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩), hsv⟩
          · by_cases h : w = n + d
            · rw [h] at hsv hyy
              exact Or.inr ⟨s, hsM, hpush p hp s hsM hsv hyy⟩
            · exact Or.inr ⟨s, hsM, w, by omega, hsv, hyy⟩
        have hi := ih hdl (F.erase (n + d) ∪ (C.gates[d].inputs.filter (· < n + d)).toFinset)
          M hM hF' hs'
        have c1 := Finset.card_union_le (F.erase (n + d))
          ((C.gates[d].inputs.filter (· < n + d)).toFinset)
        have c2 := Finset.card_erase_add_one hmem
        have c3 := hWs hWmem
        omega

noncomputable def cfilter {α : Type*} [Fintype α] (P : α → Prop) : Finset α :=
  @Finset.filter α P (Classical.decPred P) Finset.univ

lemma mem_cfilter {α : Type*} [Fintype α] (P : α → Prop) (a : α) : a ∈ cfilter P ↔ P a := by
  unfold cfilter
  simp

def cy {N : ℕ} (L : Fin N → Finset (Fin N)) (t : Fin N) : Fin N → Bool :=
  fun v => decide (v ∉ L t)

def lrow {N : ℕ} (L : Fin N → Finset (Fin N)) (p0 p1 t p : Fin N) : Fin N → Bool :=
  fun v => decide (v = p ∨ (p1 ∈ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p1 ∉ L t ∧ p ≠ p0 ∧ v = p1))

def l0 {N : ℕ} (a : Fin N) : Fin N → Bool := fun v => decide (v = a)

def yp {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 a : Fin N) : Fin N → Bool :=
  fun v => decide (v ∉ L i0 ∨ v = a)

set_option maxHeartbeats 1600000 in
theorem lower (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N)
    (hcard : ∀ i : Fin N, (L i).card = q + 1)
    (hinter : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (hne : p0 ≠ p1) (hp0i : p0 ∈ L i0) (hp1i : p1 ∈ L i0)
    (C : Circuit) (o : Fin N → ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (htopo : ∀ k, ∀ hk : k < C.gates.length, ∀ w ∈ C.gates[k].inputs, w < N + k)
    (hev : ∀ (t : Fin N) (x : Fin N → Bool),
      (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) →
      value C x (o t) = decide (∃ v ∈ L t, x v = true)) :
    N * q ≤ C.gates.length := by
  classical
  have huniq : ∀ t t' : Fin N, t ≠ t' → ∀ a b : Fin N, a ∈ L t → a ∈ L t' → b ∈ L t →
      b ∈ L t' → a = b := by
    intro t t' htt a b ha ha' hb hb'
    exact Finset.card_le_one.mp (hinter t t' htt).le a (Finset.mem_inter.mpr ⟨ha, ha'⟩) b
      (Finset.mem_inter.mpr ⟨hb, hb'⟩)
  have hG : ∀ t : Fin N, t ≠ i0 → p0 ∈ L t → p1 ∈ L t → False := by
    intro t ht a b
    exact hne (huniq t i0 ht p0 p1 a hp0i b hp1i)
  have hrow_self : ∀ t p : Fin N, lrow L p0 p1 t p p = true := by
    intro t p
    exact decide_eq_true (Or.inl rfl)
  have hrow_in : ∀ t : Fin N, t ≠ i0 → ∀ p v : Fin N, v ∈ L t → lrow L p0 p1 t p v = true →
      v = p := by
    intro t ht p v hv h
    rcases of_decide_eq_true h with h | ⟨h1', _, h3⟩ | ⟨h1', _, h3⟩
    · exact h
    · rw [h3] at hv
      exact absurd h1' (fun h1' => hG t ht hv h1')
    · rw [h3] at hv
      exact absurd hv h1'
  have hrowD : ∀ t p : Fin N, lrow L p0 p1 t p p0 = true ∨ lrow L p0 p1 t p p1 = true ∨
      ∀ u : Fin N, u ∉ L i0 → lrow L p0 p1 t p u = true := by
    intro t p
    by_cases hp1t : p1 ∈ L t
    · by_cases hp : p = p1
      · exact Or.inr (Or.inl (decide_eq_true (Or.inl hp.symm)))
      · exact Or.inl (decide_eq_true (Or.inr (Or.inl ⟨hp1t, hp, rfl⟩)))
    · by_cases hp : p = p0
      · exact Or.inl (decide_eq_true (Or.inl hp.symm))
      · exact Or.inr (Or.inl (decide_eq_true (Or.inr (Or.inr ⟨hp1t, hp, rfl⟩))))
  have hdom : ∀ t j p : Fin N, p ∉ L j → (p1 ∈ L t → p ≠ p1 → p0 ∉ L j) →
      (p1 ∉ L t → p ≠ p0 → p1 ∉ L j) → ∀ v : Fin N, lrow L p0 p1 t p v = true →
      cy L j v = true := by
    intro t j p hp c1 c2 v h
    rcases of_decide_eq_true h with h | ⟨a, b, h3⟩ | ⟨a, b, h3⟩
    · rw [h]
      exact decide_eq_true hp
    · rw [h3]
      exact decide_eq_true (c1 a b)
    · rw [h3]
      exact decide_eq_true (c2 a b)
  have hout_true : ∀ t p : Fin N, p ∈ L t → value C (lrow L p0 p1 t p) (o t) = true := by
    intro t p hp
    rw [hev t _ (hrowD t p)]
    exact decide_eq_true ⟨p, hp, hrow_self t p⟩
  have hcyD : ∀ t : Fin N, cy L t p0 = true ∨ cy L t p1 = true ∨
      ∀ u : Fin N, u ∉ L i0 → cy L t u = true := by
    intro t
    by_cases ht : t = i0
    · rw [ht]
      exact Or.inr (Or.inr fun u hu => decide_eq_true hu)
    · by_cases hp1t : p1 ∈ L t
      · exact Or.inl (decide_eq_true fun h => hG t ht h hp1t)
      · exact Or.inr (Or.inl (decide_eq_true hp1t))
  have hout_false : ∀ t : Fin N, value C (cy L t) (o t) = false := by
    intro t
    rw [hev t _ (hcyD t)]
    refine decide_eq_false ?_
    rintro ⟨v, hv, h⟩
    exact (of_decide_eq_true h) hv
  have hin_row : ∀ t : Fin N, t ≠ i0 → ∀ p : Fin N, ∀ w : ℕ, ∀ hw : w < N,
      Sv C (lrow L p0 p1 t) (cy L t) p w → (⟨w, hw⟩ : Fin N) = p := by
    intro t ht p w hw hsv
    have e1 : lrow L p0 p1 t p ⟨w, hw⟩ = true := (input_value C _ ⟨w, hw⟩).symm.trans hsv.1
    have e2 : cy L t ⟨w, hw⟩ = false := (input_value C _ ⟨w, hw⟩).symm.trans hsv.2
    have e3 : ¬ ((⟨w, hw⟩ : Fin N) ∉ L t) := of_decide_eq_false e2
    exact hrow_in t ht p _ (not_not.mp e3) e1
  have hY : ∀ t j : Fin N, t ≠ j → (p1 ∈ L t → p0 ∉ L j) → (p1 ∉ L t → p1 ∉ L j) →
      ∀ w : ℕ, Multi C (L t) (lrow L p0 p1 t) (cy L t) w → value C (cy L j) w = true := by
    intro t j htj c1 c2 w hm
    obtain ⟨a, ha, b, hb, hab, hsa, hsb⟩ := hm
    by_cases haj : a ∈ L j
    · have hbj : b ∉ L j := fun hbj => hab (huniq t j htj a b ha haj hb hbj)
      exact mono C hg _ _ (hdom t j b hbj (fun h _ => c1 h) (fun h _ => c2 h)) w hsb.1
    · exact mono C hg _ _ (hdom t j a haj (fun h _ => c1 h) (fun h _ => c2 h)) w hsa.1
  let Z : Finset (Fin N) := Finset.univ.filter fun s => p0 ∈ L s ∧ s ≠ i0
  let Zt : Fin N → Finset (Fin N) := fun t => if p1 ∈ L t then Z else ∅
  have hZt : ∀ t s : Fin N, s ∈ Zt t → p1 ∈ L t ∧ p0 ∈ L s ∧ s ≠ i0 := by
    intro t s hs
    by_cases hp : p1 ∈ L t
    · have e : Zt t = Z := ite_eq_left hp
      rw [e] at hs
      exact ⟨hp, (Finset.mem_filter.mp hs).2⟩
    · have e : Zt t = ∅ := ite_eq_right hp
      rw [e] at hs
      exact absurd hs (Finset.notMem_empty s)
  have hZt' : ∀ t s : Fin N, p1 ∈ L t → p0 ∈ L s → s ≠ i0 → s ∈ Zt t := by
    intro t s hp hs hs'
    have e : Zt t = Z := ite_eq_left hp
    rw [e]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs, hs'⟩
  let KK : Fin N → Finset (Fin C.gates.length) := fun t => cfilter fun g : Fin C.gates.length =>
    C.gates[(g : ℕ)].op = GateOp.or ∧
      Multi C (L t) (lrow L p0 p1 t) (cy L t) (N + (g : ℕ)) ∧
      ∀ s ∈ Zt t, value C (cy L s) (N + (g : ℕ)) = true
  let AA : Fin N → Finset (Fin C.gates.length) := fun t => cfilter fun g : Fin C.gates.length =>
    C.gates[(g : ℕ)].op = GateOp.and ∧ value C (cy L t) (N + (g : ℕ)) = false ∧
      (∃ p ∈ L t, value C (lrow L p0 p1 t p) (N + (g : ℕ)) = true) ∧
      ∃ s ∈ Zt t, value C (cy L s) (N + (g : ℕ)) = false ∧
        ∀ r ∈ C.gates[(g : ℕ)].inputs,
          ¬ (value C (cy L t) r = false ∧ value C (cy L s) r = false)
  have hKA : ∀ t : Fin N, t ≠ i0 → q ≤ (KK t).card + (AA t).card := by
    intro t ht
    have hWt : ∀ k, ∀ hk : k < C.gates.length, C.gates[k].op = GateOp.or →
        Multi C (L t) (lrow L p0 p1 t) (cy L t) (N + k) →
        (∀ s ∈ Zt t, value C (cy L s) (N + k) = true) →
        N + k ∈ (KK t).image fun g : Fin C.gates.length => N + (g : ℕ) := by
      intro k hk hop hmu hhi
      have hm : (⟨k, hk⟩ : Fin C.gates.length) ∈ KK t := by
        refine (mem_cfilter _ _).mpr ?_
        exact ⟨hop, hmu, hhi⟩
      exact Finset.mem_image.mpr ⟨_, hm, rfl⟩
    have hAt : ∀ k, ∀ hk : k < C.gates.length, C.gates[k].op = GateOp.and →
        value C (cy L t) (N + k) = false →
        (∃ p ∈ L t, value C (lrow L p0 p1 t p) (N + k) = true) →
        (∃ s ∈ Zt t, value C (cy L s) (N + k) = false ∧
          ∀ r ∈ C.gates[k].inputs,
            ¬ (value C (cy L t) r = false ∧ value C (cy L s) r = false)) →
        N + k ∈ (AA t).image fun g : Fin C.gates.length => N + (g : ℕ) := by
      intro k hk hop hy hrow hsp
      have hm : (⟨k, hk⟩ : Fin C.gates.length) ∈ AA t := by
        refine (mem_cfilter _ _).mpr ?_
        exact ⟨hop, hy, hrow, hsp⟩
      exact Finset.mem_image.mpr ⟨_, hm, rfl⟩
    have h := frontier2 C (L t) (lrow L p0 p1 t) (cy L t) (Zt t) (cy L) hg
      ((KK t).image fun g : Fin C.gates.length => N + (g : ℕ)) ((AA t).image fun g : Fin C.gates.length => N + (g : ℕ))
      hWt hAt
      (fun w hw hm => by
        obtain ⟨a, _, b, _, hab, hsa, hsb⟩ := hm
        exact hab ((hin_row t ht a w hw hsa).symm.trans (hin_row t ht b w hw hsb)))
      (fun s hs p hp p' hp' w w' hw hw' hsv hsv' hy hy' => by
        obtain ⟨hp1t, hp0s, hsi⟩ := hZt t s hs
        have hst : t ≠ s := by
          intro e
          rw [← e] at hp0s
          exact hG t ht hp0s hp1t
        have e1 := hin_row t ht p w hw hsv
        have e2 := hin_row t ht p' w' hw' hsv'
        have m1 : cy L s ⟨w, hw⟩ = false := (input_value C _ ⟨w, hw⟩).symm.trans hy
        have m2 : cy L s ⟨w', hw'⟩ = false := (input_value C _ ⟨w', hw'⟩).symm.trans hy'
        have n1 : p ∈ L s := by
          rw [← e1]
          exact not_not.mp (of_decide_eq_false m1)
        have n2 : p' ∈ L s := by
          rw [← e2]
          exact not_not.mp (of_decide_eq_false m2)
        exact huniq t s hst p p' hp n1 hp' n2)
      (L t) (Finset.Subset.refl _) C.gates.length le_rfl {o t} ∅ (Finset.empty_subset _)
      (fun w _ hm => multi_lt C _ _ _ w hm)
      (fun p hp => Or.inl ⟨o t, Finset.mem_singleton_self _, hout_true t p hp, hout_false t⟩)
    have c1 := Finset.card_filter_le ((KK t).image fun g : Fin C.gates.length => N + (g : ℕ))
      (· < N + C.gates.length)
    have c2 := Finset.card_filter_le ((AA t).image fun g : Fin C.gates.length => N + (g : ℕ))
      (· < N + C.gates.length)
    have c3 : ((KK t).image fun g : Fin C.gates.length => N + (g : ℕ)).card ≤ (KK t).card := Finset.card_image_le
    have c4 : ((AA t).image fun g : Fin C.gates.length => N + (g : ℕ)).card ≤ (AA t).card := Finset.card_image_le
    rw [Finset.card_singleton, Finset.card_empty, hcard t] at h
    omega
  let ch : Fin C.gates.length → ℕ := fun g =>
    if h : ∃ r ∈ C.gates[(g : ℕ)].inputs, value C (cy L i0) r = false
    then Classical.choose h else o i0
  have hch2 : ∀ g : Fin C.gates.length, C.gates[(g : ℕ)].op = GateOp.and →
      value C (cy L i0) (N + (g : ℕ)) = false →
      ch g ∈ C.gates[(g : ℕ)].inputs ∧ value C (cy L i0) (ch g) = false := by
    intro g hop h
    have hx := and_false C g g.2 hop (htopo g g.2) (cy L i0) h
    have e : ch g = Classical.choose hx := dite_eq_left hx
    rw [e]
    exact Classical.choose_spec hx
  let K0 : Finset (Fin C.gates.length) := cfilter fun g : Fin C.gates.length =>
    C.gates[(g : ℕ)].op = GateOp.or ∧ Multi C (L i0) l0 (cy L i0) (N + (g : ℕ))
  let A0 : Finset (Fin C.gates.length) := cfilter fun g : Fin C.gates.length =>
    C.gates[(g : ℕ)].op = GateOp.and ∧ value C (cy L i0) (N + (g : ℕ)) = false ∧
      ∃ p ∈ L i0, p ≠ p0 ∧ p ≠ p1 ∧ value C (l0 p) (N + (g : ℕ)) = false ∧
        value C (l0 p) (ch g) = true
  let F0 : Finset ℕ := insert (o i0) (A0.image ch)
  have key : ∀ p : Fin N, p ∈ L i0 → p ≠ p0 → p ≠ p1 → ∀ w : ℕ,
      value C (yp L i0 p) w = true → value C (cy L i0) w = false →
      value C (l0 p) w = true ∨ ∃ d ∈ F0, value C (l0 p) d = true := by
    intro p hp hpp0 hpp1 w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro h1 h2
      by_cases hn : w < N
      · left
        have e1 : yp L i0 p ⟨w, hn⟩ = true := (input_value C _ ⟨w, hn⟩).symm.trans h1
        have e2 : cy L i0 ⟨w, hn⟩ = false := (input_value C _ ⟨w, hn⟩).symm.trans h2
        have e3 : (⟨w, hn⟩ : Fin N) ∉ L i0 ∨ (⟨w, hn⟩ : Fin N) = p := of_decide_eq_true e1
        have e4 : ¬ ((⟨w, hn⟩ : Fin N) ∉ L i0) := of_decide_eq_false e2
        have e5 : (⟨w, hn⟩ : Fin N) = p := e3.resolve_left e4
        have e6 : value C (l0 p) ((⟨w, hn⟩ : Fin N) : ℕ) = l0 p ⟨w, hn⟩ :=
          input_value C (l0 p) ⟨w, hn⟩
        exact e6.trans (decide_eq_true e5)
      by_cases hw : w < N + C.gates.length
      · have hk : w - N < C.gates.length := by omega
        have hwk : w = N + (w - N) := by omega
        rw [hwk] at h1 h2
        rcases (hg _ (List.getElem_mem hk)).1 with hop | hop
        · obtain ⟨hcm, hcy⟩ := hch2 ⟨w - N, hk⟩ hop h2
          have hin := (and_value C (w - N) hk hop (yp L i0 p)).mp h1 _ hcm
          have hlt := hin.1
          rcases ih _ (by omega) hin.2 hcy with h | h
          · by_cases hwv : value C (l0 p) (N + (w - N)) = true
            · left
              rw [hwk]
              exact hwv
            · right
              exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(⟨w - N, hk⟩ : Fin C.gates.length),
                (mem_cfilter _ _).mpr ⟨hop, h2, p, hp, hpp0, hpp1,
                  by simpa using hwv, h⟩, rfl⟩), h⟩
          · exact Or.inr h
        · obtain ⟨r, hr, hlt, hv⟩ := (or_value C (w - N) hk hop (yp L i0 p)).mp h1
          have hry : value C (cy L i0) r = false := by
            by_contra hne'
            have h3 := (or_value C (w - N) hk hop (cy L i0)).mpr
              ⟨r, hr, hlt, by simpa using hne'⟩
            exact Bool.noConfusion (h2.symm.trans h3)
          rcases ih r (by omega) hv hry with h | h
          · left
            rw [hwk]
            exact (or_value C (w - N) hk hop (l0 p)).mpr ⟨r, hr, hlt, h⟩
          · exact Or.inr h
      · have h3 := missing_value C (yp L i0 p) w (by unfold Circuit.size; omega)
        exact Bool.noConfusion (h3.symm.trans h1)
  have hF0y : ∀ w ∈ F0, value C (cy L i0) w = false := by
    intro w hw
    rcases Finset.mem_insert.mp hw with h | h
    · rw [h]
      exact hout_false i0
    · obtain ⟨g, hgA, hgw⟩ := Finset.mem_image.mp h
      obtain ⟨hop, hy, _⟩ := ((mem_cfilter _ _).mp hgA)
      rw [← hgw]
      exact (hch2 g hop hy).2
  have hcover : ∀ p ∈ L i0, ∃ w ∈ F0, Sv C l0 (cy L i0) p w := by
    intro p hp
    by_cases hpT : p = p0 ∨ p = p1
    · refine ⟨o i0, Finset.mem_insert_self _ _, ?_, hout_false i0⟩
      have hD : l0 p p0 = true ∨ l0 p p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → l0 p u = true := by
        rcases hpT with e | e
        · exact Or.inl (decide_eq_true e.symm)
        · exact Or.inr (Or.inl (decide_eq_true e.symm))
      rw [hev i0 _ hD]
      exact decide_eq_true ⟨p, hp, decide_eq_true rfl⟩
    · have hpp0 : p ≠ p0 := fun e => hpT (Or.inl e)
      have hpp1 : p ≠ p1 := fun e => hpT (Or.inr e)
      have h := hev i0 (yp L i0 p) (Or.inr (Or.inr fun u hu => decide_eq_true (Or.inl hu)))
      have h2 : decide (∃ v ∈ L i0, yp L i0 p v = true) = true :=
        decide_eq_true ⟨p, hp, decide_eq_true (Or.inr rfl)⟩
      rw [h2] at h
      rcases key p hp hpp0 hpp1 (o i0) h (hout_false i0) with h3 | ⟨d, hd, h3⟩
      · exact ⟨o i0, Finset.mem_insert_self _ _, h3, hout_false i0⟩
      · exact ⟨d, hd, h3, hF0y d hd⟩
  have h0q : q ≤ K0.card + A0.card := by
    have hW0 : ∀ k, ∀ hk : k < C.gates.length, C.gates[k].op = GateOp.or →
        Multi C (L i0) l0 (cy L i0) (N + k) → N + k ∈ K0.image fun g : Fin C.gates.length => N + (g : ℕ) := by
      intro k hk hop hmu
      have hm : (⟨k, hk⟩ : Fin C.gates.length) ∈ K0 := by
        refine (mem_cfilter _ _).mpr ?_
        exact ⟨hop, hmu⟩
      exact Finset.mem_image.mpr ⟨_, hm, rfl⟩
    have h := frontier2 C (L i0) l0 (cy L i0) (∅ : Finset (Fin N)) (cy L) hg
      (K0.image fun g : Fin C.gates.length => N + (g : ℕ)) ∅
      (fun k hk hop hmu _ => hW0 k hk hop hmu)
      (fun k hk _ _ _ hsp => by
        obtain ⟨s, hs, _⟩ := hsp
        exact absurd hs (Finset.notMem_empty s))
      (fun w hw hm => by
        obtain ⟨a, _, b, _, hab, hsa, hsb⟩ := hm
        have e1 : l0 a ⟨w, hw⟩ = true := (input_value C _ ⟨w, hw⟩).symm.trans hsa.1
        have e2 : l0 b ⟨w, hw⟩ = true := (input_value C _ ⟨w, hw⟩).symm.trans hsb.1
        exact hab ((of_decide_eq_true e1).symm.trans (of_decide_eq_true e2)))
      (fun s hs => absurd hs (Finset.notMem_empty s))
      (L i0) (Finset.Subset.refl _) C.gates.length le_rfl F0 ∅ (Finset.empty_subset _)
      (fun w _ hm => multi_lt C _ _ _ w hm)
      (fun p hp => Or.inl (hcover p hp))
    have c1 := Finset.card_filter_le (K0.image fun g : Fin C.gates.length => N + (g : ℕ))
      (· < N + C.gates.length)
    have c3 : (K0.image fun g : Fin C.gates.length => N + (g : ℕ)).card ≤ K0.card := Finset.card_image_le
    have c5 : (insert (o i0) (A0.image ch)).card ≤ A0.card + 1 := by
      have a1 := Finset.card_insert_le (o i0) (A0.image ch)
      have a2 : (A0.image ch).card ≤ A0.card := Finset.card_image_le
      omega
    have c6 : F0.card = (insert (o i0) (A0.image ch)).card := rfl
    simp only [Finset.card_empty, Finset.filter_empty, hcard i0] at h
    omega
  have hK0 : ∀ g ∈ K0, ∀ j : Fin N, j ≠ i0 → value C (cy L j) (N + (g : ℕ)) = true := by
    intro g hgK j hj
    obtain ⟨_, a, ha, b, hb, hab, hsa, hsb⟩ := ((mem_cfilter _ _).mp hgK)
    by_cases haj : a ∈ L j
    · have hbj : b ∉ L j := fun hbj => hab (huniq i0 j (Ne.symm hj) a b ha haj hb hbj)
      exact mono C hg (l0 b) _ (fun v hv => by
        have e : v = b := of_decide_eq_true hv
        rw [e]
        exact decide_eq_true hbj) _ hsb.1
    · exact mono C hg (l0 a) _ (fun v hv => by
        have e : v = a := of_decide_eq_true hv
        rw [e]
        exact decide_eq_true haj) _ hsa.1
  have sep0 : ∀ j : Fin N, j ≠ i0 → ∀ g : Fin C.gates.length, g ∈ K0 ∪ A0 →
      g ∈ KK j ∪ AA j → False := by
    intro j hj g m1 m2
    rcases Finset.mem_union.mp m1 with m1 | m1 <;> rcases Finset.mem_union.mp m2 with m2 | m2
    · obtain ⟨_, hm, _⟩ := ((mem_cfilter _ _).mp m2)
      obtain ⟨a, _, _, _, _, hs, _⟩ := hm
      exact Bool.noConfusion (hs.2.symm.trans (hK0 g m1 j hj))
    · have e1 := ((mem_cfilter _ _).mp m1).1
      have e2 := ((mem_cfilter _ _).mp m2).1
      cases e1.symm.trans e2
    · have e1 := ((mem_cfilter _ _).mp m1).1
      have e2 := ((mem_cfilter _ _).mp m2).1
      cases e1.symm.trans e2
    · obtain ⟨hop, hy0, p, hp, hpp0, hpp1, _, hlc⟩ := ((mem_cfilter _ _).mp m1)
      obtain ⟨_, hyj, _, s, hsZ, hys, hno⟩ := ((mem_cfilter _ _).mp m2)
      obtain ⟨hp1j, hp0s, hsi⟩ := hZt j s hsZ
      obtain ⟨hcm, _⟩ := hch2 g hop hy0
      have hps : p ∉ L s := fun h => hpp0 (huniq s i0 hsi p p0 h hp hp0s hp0i)
      have hpj : p ∉ L j := fun h => hpp1 (huniq j i0 hj p p1 h hp hp1j hp1i)
      have hcs : value C (cy L s) (ch g) = true := mono C hg (l0 p) _ (fun v hv => by
        have e : v = p := of_decide_eq_true hv
        rw [e]
        exact decide_eq_true hps) _ hlc
      have hcj : value C (cy L j) (ch g) = true := mono C hg (l0 p) _ (fun v hv => by
        have e : v = p := of_decide_eq_true hv
        rw [e]
        exact decide_eq_true hpj) _ hlc
      obtain ⟨r1, hr1, hr1s⟩ := and_false C g g.2 hop (htopo g g.2) (cy L s) hys
      obtain ⟨r2, hr2, hr2j⟩ := and_false C g g.2 hop (htopo g g.2) (cy L j) hyj
      have hr1j : value C (cy L j) r1 = true := by
        by_contra h
        exact hno r1 hr1 ⟨by simpa using h, hr1s⟩
      have d1 : ch g ≠ r1 := by
        intro e
        rw [e] at hcs
        exact Bool.noConfusion (hr1s.symm.trans hcs)
      have d2 : ch g ≠ r2 := by
        intro e
        rw [e] at hcj
        exact Bool.noConfusion (hr2j.symm.trans hcj)
      have d3 : r1 ≠ r2 := by
        intro e
        rw [e] at hr1j
        exact Bool.noConfusion (hr2j.symm.trans hr1j)
      have hsub : ({ch g, r1, r2} : Finset ℕ) ⊆ C.gates[(g : ℕ)].inputs.toFinset := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx | hx
        · rw [hx]
          exact List.mem_toFinset.mpr hcm
        · rw [hx]
          exact List.mem_toFinset.mpr hr1
        · rw [hx]
          exact List.mem_toFinset.mpr hr2
      have h3 : ({ch g, r1, r2} : Finset ℕ).card = 3 :=
        Finset.card_eq_three.mpr ⟨_, _, _, d1, d2, d3, rfl⟩
      have h4 := Finset.card_le_card hsub
      have h5 := List.toFinset_card_le C.gates[(g : ℕ)].inputs
      have h6 := (hg _ (List.getElem_mem g.2)).2
      omega
  have kk1 : ∀ t t' : Fin N, t ≠ t' → ∀ g : Fin C.gates.length, g ∈ KK t → g ∈ KK t' →
      (p1 ∈ L t → p0 ∉ L t') → (p1 ∉ L t → p1 ∉ L t') → False := by
    intro t t' htt g m1 m2 c1 c2
    obtain ⟨_, hm, _⟩ := ((mem_cfilter _ _).mp m1)
    obtain ⟨_, hm', _⟩ := ((mem_cfilter _ _).mp m2)
    obtain ⟨a, _, _, _, _, hs, _⟩ := hm'
    exact Bool.noConfusion (hs.2.symm.trans (hY t t' htt c1 c2 _ hm))
  have sep : ∀ t t' : Fin N, t ≠ i0 → t' ≠ i0 → t ≠ t' → ∀ g : Fin C.gates.length,
      g ∈ KK t ∪ AA t → g ∈ KK t' ∪ AA t' → False := by
    intro t t' ht ht' htt g m1 m2
    rcases Finset.mem_union.mp m1 with m1 | m1 <;> rcases Finset.mem_union.mp m2 with m2 | m2
    · by_cases a : p1 ∈ L t <;> by_cases b : p1 ∈ L t'
      · exact kk1 t t' htt g m1 m2 (fun _ h => hG t' ht' h b) (fun h => absurd a h)
      · by_cases c : p0 ∈ L t'
        · obtain ⟨_, _, hhi⟩ := ((mem_cfilter _ _).mp m1)
          obtain ⟨_, hm', _⟩ := ((mem_cfilter _ _).mp m2)
          obtain ⟨x, _, _, _, _, hs, _⟩ := hm'
          exact Bool.noConfusion (hs.2.symm.trans (hhi t' (hZt' t t' a c ht')))
        · exact kk1 t t' htt g m1 m2 (fun _ => c) (fun h => absurd a h)
      · by_cases c : p0 ∈ L t
        · obtain ⟨_, hm, _⟩ := ((mem_cfilter _ _).mp m1)
          obtain ⟨_, _, hhi⟩ := ((mem_cfilter _ _).mp m2)
          obtain ⟨x, _, _, _, _, hs, _⟩ := hm
          exact Bool.noConfusion (hs.2.symm.trans (hhi t (hZt' t' t b c ht)))
        · exact kk1 t' t (Ne.symm htt) g m2 m1 (fun _ => c) (fun h => absurd b h)
      · exact kk1 t t' htt g m1 m2 (fun h => absurd h a) (fun _ => b)
    · have e1 := ((mem_cfilter _ _).mp m1).1
      have e2 := ((mem_cfilter _ _).mp m2).1
      cases e1.symm.trans e2
    · have e1 := ((mem_cfilter _ _).mp m1).1
      have e2 := ((mem_cfilter _ _).mp m2).1
      cases e1.symm.trans e2
    · obtain ⟨_, _, ⟨bp, hbp, hrow⟩, s, hsZ, hys, _⟩ := ((mem_cfilter _ _).mp m1)
      obtain ⟨_, hyt', _, s', hsZ', _, _⟩ := ((mem_cfilter _ _).mp m2)
      obtain ⟨hp1t, hp0s, hsi⟩ := hZt t s hsZ
      obtain ⟨hp1t', _, _⟩ := hZt t' s' hsZ'
      by_cases hb : bp = p1
      · have hp1s : p1 ∉ L s := fun h => hG s hsi hp0s h
        have hd := hdom t s bp (by rw [hb]; exact hp1s) (fun _ h => absurd hb h)
          (fun h _ => absurd hp1t h)
        exact Bool.noConfusion (hys.symm.trans (mono C hg _ _ hd _ hrow))
      · have hbt' : bp ∉ L t' := fun h => hb (huniq t t' htt bp p1 hbp h hp1t hp1t')
        have hd := hdom t t' bp hbt' (fun _ _ h => hG t' ht' h hp1t')
          (fun h _ => absurd hp1t h)
        exact Bool.noConfusion (hyt'.symm.trans (mono C hg _ _ hd _ hrow))
  let B : Fin N → Finset (Fin C.gates.length) := fun t =>
    if t = i0 then K0 ∪ A0 else KK t ∪ AA t
  have hB0 : B i0 = K0 ∪ A0 := ite_eq_left rfl
  have hB1 : ∀ t : Fin N, t ≠ i0 → B t = KK t ∪ AA t := fun t ht => ite_eq_right ht
  have hBq : ∀ t : Fin N, q ≤ (B t).card := by
    intro t
    by_cases ht : t = i0
    · rw [ht, hB0, Finset.card_union_of_disjoint]
      · exact h0q
      · refine Finset.disjoint_left.mpr fun g a b => ?_
        have e1 := ((mem_cfilter _ _).mp a).1
        have e2 := ((mem_cfilter _ _).mp b).1
        cases e1.symm.trans e2
    · rw [hB1 t ht, Finset.card_union_of_disjoint]
      · exact hKA t ht
      · refine Finset.disjoint_left.mpr fun g a b => ?_
        have e1 := ((mem_cfilter _ _).mp a).1
        have e2 := ((mem_cfilter _ _).mp b).1
        cases e1.symm.trans e2
  have hBd : ∀ t t' : Fin N, t ≠ t' → Disjoint (B t) (B t') := by
    intro t t' htt
    refine Finset.disjoint_left.mpr fun g a b => ?_
    by_cases ht : t = i0
    · have ht' : t' ≠ i0 := fun e => htt (ht.trans e.symm)
      rw [ht, hB0] at a
      rw [hB1 t' ht'] at b
      exact sep0 t' ht' g a b
    · by_cases ht' : t' = i0
      · rw [ht', hB0] at b
        rw [hB1 t ht] at a
        exact sep0 t ht g b a
      · rw [hB1 t ht] at a
        rw [hB1 t' ht'] at b
        exact sep t t' ht ht' htt g a b
  have hU := count B hBq hBd
  have hle := Finset.card_le_univ (Finset.univ.biUnion B)
  rw [Fintype.card_fin] at hle
  omega

def pnt {N q : ℕ} (e : Fin N → Fin (q + 1) → Fin N) (t i : ℕ) : ℕ :=
  if h : t < N ∧ i < q + 1 then ((e ⟨t, h.1⟩ ⟨i, h.2⟩ : Fin N) : ℕ) else 0

def gateAt {N q : ℕ} (e : Fin N → Fin (q + 1) → Fin N) (k : ℕ) : Gate :=
  ⟨GateOp.or, if k % q = 0 then [pnt e (k / q) 0, pnt e (k / q) 1]
    else [N + (k - 1), pnt e (k / q) (k % q + 1)]⟩

def cgates {N q : ℕ} (e : Fin N → Fin (q + 1) → Fin N) : List Gate :=
  (List.range (N * q)).map (gateAt e)

lemma pnt_lt {N q : ℕ} (e : Fin N → Fin (q + 1) → Fin N) (t i : ℕ) (hN : 0 < N) :
    pnt e t i < N := by
  unfold pnt
  split_ifs
  · exact Fin.is_lt _
  · exact hN

lemma or_pair {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length) (a b : ℕ)
    (hgate : C.gates[k] = ⟨GateOp.or, [a, b]⟩) (ha : a < n + k) (hb : b < n + k)
    (x : Fin n → Bool) :
    value C x (n + k) = true ↔ (value C x a = true ∨ value C x b = true) := by
  have hop : C.gates[k].op = GateOp.or := by rw [hgate]
  rw [or_value C k hk hop x, hgate]
  constructor
  · rintro ⟨r, hr, _, hv⟩
    rcases List.mem_pair.mp hr with e | e
    · rw [e] at hv
      exact Or.inl hv
    · rw [e] at hv
      exact Or.inr hv
  · rintro (h | h)
    · exact ⟨a, List.mem_pair.mpr (Or.inl rfl), ha, h⟩
    · exact ⟨b, List.mem_pair.mpr (Or.inr rfl), hb, h⟩

lemma chain_val {N q : ℕ} (hq : 1 ≤ q) (e : Fin N → Fin (q + 1) → Fin N) (x : Fin N → Bool)
    (t : Fin N) : ∀ j : ℕ, j < q →
    (value ⟨cgates e, 0⟩ x (N + ((t : ℕ) * q + j)) = true ↔
      ∃ i : Fin (q + 1), (i : ℕ) ≤ j + 1 ∧ x (e t i) = true) := by
  have hlen : (cgates e).length = N * q := by simp [cgates]
  have hget : ∀ k, ∀ hk : k < (cgates e).length, (cgates e)[k] = gateAt e k := by
    intro k hk
    simp [cgates]
  have hkt : ∀ j, j < q → (t : ℕ) * q + j < (cgates e).length := by
    intro j hj
    rw [hlen]
    have h := Nat.mul_le_mul_right q (Nat.succ_le_of_lt t.2)
    rw [Nat.succ_mul] at h
    omega
  have hdiv : ∀ j, j < q → ((t : ℕ) * q + j) / q = t := by
    intro j hj
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < q), Nat.div_eq_of_lt hj,
      Nat.zero_add]
  have hmod : ∀ j, j < q → ((t : ℕ) * q + j) % q = j := by
    intro j hj
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  have hpl : ∀ i : ℕ, pnt e t i < N := fun i => pnt_lt e t i (Fin.pos t)
  have hpv : ∀ (i : ℕ) (hi : i < q + 1),
      value ⟨cgates e, 0⟩ x (pnt e t i) = x (e t ⟨i, hi⟩) := by
    intro i hi
    have ee : pnt e (t : ℕ) i = ((e t ⟨i, hi⟩ : Fin N) : ℕ) := dite_eq_left ⟨t.2, hi⟩
    rw [ee]
    exact input_value _ x (e t ⟨i, hi⟩)
  intro j
  induction j with
  | zero =>
    intro hj
    have hk := hkt 0 hj
    have hgk : (cgates e)[(t : ℕ) * q + 0] = ⟨GateOp.or, [pnt e t 0, pnt e t 1]⟩ := by
      rw [hget _ hk]
      unfold gateAt
      rw [ite_eq_left (hmod 0 hj), hdiv 0 hj]
    have h0 := hpl 0
    have h1 := hpl 1
    rw [or_pair ⟨cgates e, 0⟩ _ hk _ _ hgk (by omega) (by omega) x, hpv 0 (by omega),
      hpv 1 (by omega)]
    constructor
    · rintro (h | h)
      · exact ⟨⟨0, by omega⟩, Nat.zero_le _, h⟩
      · exact ⟨⟨1, by omega⟩, le_refl _, h⟩
    · rintro ⟨i, hi, h⟩
      have hc : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
      rcases hc with hc | hc
      · left
        have e2 : i = ⟨0, by omega⟩ := Fin.ext hc
        rw [← e2]
        exact h
      · right
        have e2 : i = ⟨1, by omega⟩ := Fin.ext hc
        rw [← e2]
        exact h
  | succ j ih =>
    intro hj
    have hk := hkt (j + 1) hj
    have hgk : (cgates e)[(t : ℕ) * q + (j + 1)] =
        ⟨GateOp.or, [N + ((t : ℕ) * q + j), pnt e t (j + 1 + 1)]⟩ := by
      rw [hget _ hk]
      unfold gateAt
      rw [ite_eq_right (by rw [hmod (j + 1) hj]; omega), hdiv (j + 1) hj, hmod (j + 1) hj]
      rfl
    have h2 := hpl (j + 1 + 1)
    rw [or_pair ⟨cgates e, 0⟩ _ hk _ _ hgk (by omega) (by omega) x, ih (by omega),
      hpv (j + 1 + 1) (by omega)]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨⟨j + 1 + 1, by omega⟩, le_refl _, h⟩
    · rintro ⟨i, hi, h⟩
      by_cases hij : (i : ℕ) = j + 1 + 1
      · right
        have e2 : i = ⟨j + 1 + 1, by omega⟩ := Fin.ext hij
        rw [← e2]
        exact h
      · left
        exact ⟨i, by omega, h⟩

theorem upper (q N : ℕ) (L : Fin N → Finset (Fin N)) (hq : 1 ≤ q)
    (hcard : ∀ i : Fin N, (L i).card = q + 1) :
    ∃ (gates : List Gate) (o : Fin N → ℕ),
      (∀ gt ∈ gates, (gt.op = GateOp.and ∨ gt.op = GateOp.or) ∧ gt.inputs.length ≤ 2) ∧
      (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) ∧
      (∀ (t : Fin N) (x : Fin N → Bool),
        Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) ∧
      gates.length = N * q := by
  classical
  obtain ⟨e, he_mem, he_surj⟩ : ∃ e : Fin N → Fin (q + 1) → Fin N,
      (∀ t i, e t i ∈ L t) ∧ ∀ t, ∀ v ∈ L t, ∃ i, e t i = v := by
    refine ⟨fun t i => (L t).orderEmbOfFin (hcard t) i,
      fun t i => Finset.orderEmbOfFin_mem _ _ _, fun t v hv => ?_⟩
    have hr : v ∈ Set.range ((L t).orderEmbOfFin (hcard t)) := by
      rw [Finset.range_orderEmbOfFin]
      exact hv
    exact hr
  have hlen : (cgates e).length = N * q := by simp [cgates]
  refine ⟨cgates e, fun t => N + ((t : ℕ) * q + (q - 1)), ?_, ?_, ?_, hlen⟩
  · intro gt hgt
    obtain ⟨k, _, hk⟩ := List.mem_map.mp hgt
    rw [← hk]
    refine ⟨Or.inr rfl, ?_⟩
    unfold gateAt
    dsimp only
    split_ifs <;> simp
  · intro i w hw
    have hi : (i : ℕ) < N * q := lt_of_lt_of_eq i.2 hlen
    have hNpos : 0 < N := by
      by_contra h0
      have hN0 : N = 0 := by omega
      have hz : N * q = 0 := by
        rw [hN0]
        exact Nat.zero_mul q
      omega
    have hgi : (cgates e)[(i : ℕ)] = gateAt e i := by simp [cgates]
    have hw : w ∈ ((cgates e)[(i : ℕ)]).inputs := hw
    rw [hgi] at hw
    unfold gateAt at hw
    dsimp only at hw
    have b0 := pnt_lt e ((i : ℕ) / q) 0 hNpos
    have b1 := pnt_lt e ((i : ℕ) / q) 1 hNpos
    have b2 := pnt_lt e ((i : ℕ) / q) ((i : ℕ) % q + 1) hNpos
    split_ifs at hw with hz
    · rcases List.mem_pair.mp hw with hw | hw <;> omega
    · have hi0 : (i : ℕ) ≠ 0 := by
        intro h
        rw [h] at hz
        exact hz (Nat.zero_mod q)
      rcases List.mem_pair.mp hw with hw | hw <;> omega
  · intro t x
    change value ⟨cgates e, 0⟩ x (N + ((t : ℕ) * q + (q - 1))) = decide _
    rw [Bool.eq_iff_iff, chain_val hq e x t (q - 1) (by omega), decide_eq_true_iff]
    constructor
    · rintro ⟨i, _, h⟩
      exact ⟨e t i, he_mem t i, h⟩
    · rintro ⟨v, hv, h⟩
      obtain ⟨i, hi⟩ := he_surj t v hv
      rw [← hi] at h
      have := i.2
      exact ⟨i, by omega, h⟩

end PEqualNP.Outside.L_meta_1643

theorem PEqualNP.Outside.L_meta_1643 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ),
      (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
      (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
      (∀ (t : Fin N) (x : Fin N → Bool), (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) →
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
      N * q ≤ gates.length) ∧
    ∃ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ),
      (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) ∧
      (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) ∧
      (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) ∧
      gates.length = N * q := by
  intro q N L i0 p0 p1 hq _ hcard hinter _ hne hp0 hp1
  refine ⟨fun gates o hg htopo hev => ?_, ?_⟩
  · exact PEqualNP.Outside.L_meta_1643.lower q N L i0 p0 p1 hcard hinter hne hp0 hp1
      ⟨gates, 0⟩ o hg (fun k hk w hw => htopo ⟨k, hk⟩ w hw) hev
  · exact PEqualNP.Outside.L_meta_1643.upper q N L (by omega) hcard
