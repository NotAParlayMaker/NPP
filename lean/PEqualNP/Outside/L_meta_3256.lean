import Mathlib.Tactic.Choose
import PEqualNP.Defs

-- Circuit evaluation and the frontier count are adapted from willakone's L-meta-2128.
namespace PEqualNP.Outside.L_meta_3256

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover


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

lemma list_cases (L : List ℕ) (hL : L.length ≤ 2) (Q : ℕ → Prop) :
    (L.length = 2 ∧ ∀ r ∈ L, Q r) ∨ ∃ c, ∀ r ∈ L, Q r → r = c := by
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
  · exact Or.inr ⟨0, fun r hr => absurd hr (by simp)⟩
  · exact Or.inr ⟨a, fun r hr _ => by simpa using hr⟩
  · by_cases ha : Q a
    · by_cases hb : Q b
      · refine Or.inl ⟨rfl, fun r hr => ?_⟩
        rcases List.mem_pair.mp hr with rfl | rfl
        · exact ha
        · exact hb
      · refine Or.inr ⟨a, fun r hr hq => ?_⟩
        rcases List.mem_pair.mp hr with rfl | rfl
        · rfl
        · exact absurd hq hb
    · refine Or.inr ⟨b, fun r hr hq => ?_⟩
      rcases List.mem_pair.mp hr with rfl | rfl
      · exact absurd hq ha
      · rfl
  · simp at hL

lemma step_cases {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (y : Fin n → Bool)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (k : ℕ) (hk : k < C.gates.length) (hm : Multi C T l y (n + k)) :
    (∃ r ∈ C.gates[k].inputs, r < n + k ∧ ∀ p ∈ T, Sv C l y p (n + k) → Sv C l y p r) ∨
    (C.gates[k].op = GateOp.or ∧ C.gates[k].inputs.length = 2 ∧
      (∀ r ∈ C.gates[k].inputs, ∃ p ∈ T, value C (l p) r = true) ∧
      ∀ p ∈ T, Sv C l y p (n + k) → ∃ r ∈ C.gates[k].inputs, r < n + k ∧ Sv C l y p r) := by
  obtain ⟨p0, hp0, _, _, _, hs0, _⟩ := hm
  rcases (hC _ (List.getElem_mem hk)).1 with hop | hop
  · left
    have hy := hs0.2
    by_contra hcon
    have hall : ∀ r ∈ C.gates[k].inputs, r < n + k ∧ value C y r = true := by
      intro r hr
      by_contra hr2
      apply hcon
      have hlt := ((and_value C k hk hop (l p0)).mp hs0.1 r hr).1
      refine ⟨r, hr, hlt, fun p _ hsp => ⟨((and_value C k hk hop (l p)).mp hsp.1 r hr).2, ?_⟩⟩
      by_contra hne
      exact hr2 ⟨hlt, by simpa using hne⟩
    rw [(and_value C k hk hop y).mpr hall] at hy
    exact Bool.noConfusion hy
  · have hyall : ∀ r ∈ C.gates[k].inputs, r < n + k → value C y r = false := by
      intro r hr hlt
      by_contra h
      have h2 : value C y (n + k) = true :=
        (or_value C k hk hop y).mpr ⟨r, hr, hlt, by simpa using h⟩
      rw [hs0.2] at h2
      exact Bool.noConfusion h2
    have hsv : ∀ p ∈ T, Sv C l y p (n + k) →
        ∃ r ∈ C.gates[k].inputs, r < n + k ∧ value C (l p) r = true ∧ Sv C l y p r := by
      intro p _ hsp
      obtain ⟨r, hr, hlt, hv⟩ := (or_value C k hk hop (l p)).mp hsp.1
      exact ⟨r, hr, hlt, hv, hv, hyall r hr hlt⟩
    rcases list_cases C.gates[k].inputs (hC _ (List.getElem_mem hk)).2
      (fun r => ∃ p ∈ T, r < n + k ∧ value C (l p) r = true) with ⟨hlen, hQ⟩ | ⟨c, hc⟩
    · right
      refine ⟨hop, hlen, fun r hr => ?_, fun p hp hsp => ?_⟩
      · obtain ⟨p, hp, _, hv⟩ := hQ r hr
        exact ⟨p, hp, hv⟩
      · obtain ⟨r, hr, hlt, _, hs⟩ := hsv p hp hsp
        exact ⟨r, hr, hlt, hs⟩
    · left
      obtain ⟨r, hr, hlt, hv, _⟩ := hsv p0 hp0 hs0
      have hrc := hc r hr ⟨p0, hp0, hlt, hv⟩
      refine ⟨r, hr, hlt, fun p hp hsp => ?_⟩
      obtain ⟨r', hr', hlt', hv', hs'⟩ := hsv p hp hsp
      have hrc' := hc r' hr' ⟨p, hp, hlt', hv'⟩
      rw [hrc, ← hrc']
      exact hs'

lemma frontier {n : ℕ} {ι : Type*} (C : Circuit) (T : Finset ι) (l : ι → Fin n → Bool)
    (y : Fin n → Bool)
    (hC : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (W : Finset ℕ)
    (hW : ∀ k, ∀ hk : k < C.gates.length, Multi C T l y (n + k) →
      C.gates[k].op = GateOp.or → C.gates[k].inputs.length = 2 →
      (∀ r ∈ C.gates[k].inputs, ∃ p ∈ T, value C (l p) r = true) → n + k ∈ W)
    (hlen : ∀ w, Multi C T l y w → n ≤ w ∧ w < n + C.gates.length)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, Multi C T l y w → w < t)
    (T' : Finset ι) (hT' : T' ⊆ T) (hs : ∀ p ∈ T', ∃ w ∈ F, Sv C l y p w) :
    T'.card ≤ F.card + (W.filter (· < t)).card := by
  classical
  induction t generalizing F with
  | zero =>
    choose! f hfF hfs using hs
    have hinj : Set.InjOn f T' := by
      intro p hp p' hp' e
      by_contra hne
      have hc : Multi C T l y (f p) :=
        ⟨p, hT' hp, p', hT' hp', hne, hfs p hp, by rw [e]; exact hfs p' hp'⟩
      have := hF (f p) (hfF p hp) hc
      omega
    have := Finset.card_le_card_of_injOn f (fun p hp => hfF p hp) hinj
    omega
  | succ t ih =>
    have hle : (W.filter (· < t)).card ≤ (W.filter (· < t + 1)).card :=
      Finset.card_le_card fun w hw =>
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,
          by have := (Finset.mem_filter.mp hw).2; omega⟩
    by_cases hex : t ∈ F ∧ Multi C T l y t
    · obtain ⟨h1, h2⟩ := hlen t hex.2
      have hk : t - n < C.gates.length := by omega
      have htk : t = n + (t - n) := by omega
      have hm : Multi C T l y (n + (t - n)) := by rw [← htk]; exact hex.2
      have he := Finset.card_erase_add_one hex.1
      rcases step_cases C T l y hC (t - n) hk hm with ⟨r, hr, hlt, hall⟩ | ⟨hop, hlen2, hQ, hsv⟩
      · rw [← htk] at hlt hall
        let F' := insert r (F.erase t)
        have hF' : ∀ w ∈ F', Multi C T l y w → w < t := by
          intro w hw hg
          rcases Finset.mem_insert.mp hw with hw | hw
          · rw [hw]; exact hlt
          · have hne := (Finset.mem_erase.mp hw).1
            have hlt := hF w (Finset.mem_erase.mp hw).2 hg
            omega
        have hs' : ∀ p ∈ T', ∃ w ∈ F', Sv C l y p w := by
          intro p hp
          obtain ⟨w, hw, hsv⟩ := hs p hp
          by_cases h : w = t
          · subst h
            exact ⟨r, Finset.mem_insert_self _ _, hall p (hT' hp) hsv⟩
          · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h, hw⟩), hsv⟩
        have hi := ih F' hF' hs'
        have hu := Finset.card_insert_le r (F.erase t)
        change F'.card ≤ _ at hu
        omega
      · rw [← htk] at hsv
        have htW : t ∈ W := by
          have := hW (t - n) hk hm hop hlen2 hQ
          rwa [← htk] at this
        let P : Finset ℕ := (C.gates[t - n].inputs.filter (· < t)).toFinset
        have hPcard : P.card ≤ 2 := by
          have h1 := List.toFinset_card_le (C.gates[t - n].inputs.filter (· < t))
          have h2 := List.length_filter_le (fun r => decide (r < t)) C.gates[t - n].inputs
          change P.card ≤ _ at h1
          omega
        let F' := F.erase t ∪ P
        have hF' : ∀ w ∈ F', Multi C T l y w → w < t := by
          intro w hw hg
          rcases Finset.mem_union.mp hw with hw | hw
          · have hne := (Finset.mem_erase.mp hw).1
            have hlt := hF w (Finset.mem_erase.mp hw).2 hg
            omega
          · have := (List.mem_filter.mp (List.mem_toFinset.mp hw)).2
            simpa using this
        have hs' : ∀ p ∈ T', ∃ w ∈ F', Sv C l y p w := by
          intro p hp
          obtain ⟨w, hw, hsvp⟩ := hs p hp
          by_cases h : w = t
          · subst h
            obtain ⟨r, hr, hlt, hsr⟩ := hsv p (hT' hp) hsvp
            exact ⟨r, Finset.mem_union_right _ (List.mem_toFinset.mpr
              (List.mem_filter.mpr ⟨hr, by simpa using hlt⟩)), hsr⟩
          · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩), hsvp⟩
        have hi := ih F' hF' hs'
        have hu := Finset.card_union_le (F.erase t) P
        change F'.card ≤ _ at hu
        have hfilter : W.filter (· < t + 1) = insert t (W.filter (· < t)) := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hg, hlt⟩
            by_cases h : w = t
            · exact Or.inl h
            · exact Or.inr ⟨hg, by omega⟩
          · rintro (rfl | ⟨hg, hlt⟩)
            · exact ⟨htW, by omega⟩
            · exact ⟨hg, by omega⟩
        rw [hfilter, Finset.card_insert_of_notMem (by simp)]
        omega
    · have hF' : ∀ w ∈ F, Multi C T l y w → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      have := ih F hF' hs
      omega

end PEqualNP.Outside.L_meta_3256

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.GenericRejection PEqualNP.Outside.L_meta_3256 in
theorem PEqualNP.Outside.L_meta_3256 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Fin x1)) (x4 : Fin x1),   PEqualNP.TopForm.IsAO2 (x1 + x1) x2 →     x2.output < x1 + x1 + x2.size →       (∀ x7 ∈ x3, x2.eval (PEqualNP.GenericRejection.incidenceInput {x7} {x4}) = Bool.true) →         x2.eval (PEqualNP.GenericRejection.incidenceInput x3ᶜ {x4}) = Bool.false →           ∃ (x9 : Finset ℕ),             x3.card ≤ x9.card + (1 : ℕ) ∧               ∀ x10 ∈ x9,                 x10 < x2.size ∧                   (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧                     have x12 : Finset (Fin x1) → Bool := fun (x12 : Finset (Fin x1)) => PEqualNP.CircuitLowerBounds.wireValue x2 (PEqualNP.GenericRejection.incidenceInput x12 {x4}) (x1 + x1 + x10);                     x12 x3ᶜ = Bool.false ∧ (∃ (x13 : Fin x1) (x14 : Fin x1), x13 ≠ x14 ∧ x12 {x13} = Bool.true ∧ x12 {x14} = Bool.true) ∧ ∀ (x13 : Fin x1), x12 {x13} = Bool.true → x13 ∈ x3 := by
  classical
  intro n C S l model output accepted rejected
  let input (X : Finset (Fin n)) : Fin (n + n) → Bool :=
    Fin.addCases (fun p => decide (p ∈ X)) (fun r => decide (r ∈ ({l} : Finset (Fin n))))
  let single (p : Fin n) := input {p}
  let rejectedInput := input Sᶜ
  have input_list (X : Finset (Fin n)) : List.ofFn (input X) = incidenceInput X {l} :=
    List.ofFn_fin_append _ _
  have point (X : Finset (Fin n)) (i : Fin n) :
      input X (Fin.castAdd n i) = decide (i ∈ X) := Fin.addCases_left ..
  have line (X : Finset (Fin n)) (i : Fin n) :
      input X (Fin.natAdd n i) = decide (i ∈ ({l} : Finset (Fin n))) := Fin.addCases_right ..
  have circuitModel : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
    fun g hg => ⟨model.1 g hg, (model.2.2 g hg).le⟩
  have outputSeparates (p : Fin n) (hp : p ∈ S) : Sv C single rejectedInput p C.output := by
    constructor
    · change (C.wires (List.ofFn (input {p}))).getD C.output false = true
      rw [input_list]
      exact accepted p hp
    · change (C.wires (List.ofFn (input Sᶜ))).getD C.output false = false
      rw [input_list]
      exact rejected
  have inputNotMulti (i : Fin (n + n)) : ¬ Multi C S single rejectedInput i := by
    refine Fin.addCases (motive := fun i => ¬ Multi C S single rejectedInput i) ?_ ?_ i
    · intro p h
      obtain ⟨u, _, v, _, distinct, hu, hv⟩ := h
      have hpu : p = u := by
        have h := hu.1
        change value C (single u) (Fin.castAdd n p) = true at h
        rw [input_value] at h
        simpa only [single, point, decide_eq_true_eq, Finset.mem_singleton] using h
      have hpv : p = v := by
        have h := hv.1
        change value C (single v) (Fin.castAdd n p) = true at h
        rw [input_value] at h
        simpa only [single, point, decide_eq_true_eq, Finset.mem_singleton] using h
      exact distinct (hpu.symm.trans hpv)
    · intro r h
      obtain ⟨u, _, _, _, _, hu, _⟩ := h
      have htrue := hu.1
      have hfalse := hu.2
      rw [input_value, show single u (Fin.natAdd n r) =
        decide (r ∈ ({l} : Finset (Fin n))) from line {u} r] at htrue
      rw [input_value, show rejectedInput (Fin.natAdd n r) =
        decide (r ∈ ({l} : Finset (Fin n))) from line Sᶜ r] at hfalse
      exact Bool.noConfusion (htrue.symm.trans hfalse)
  change C.output < n + n + C.gates.length at output
  have multiRange (w : ℕ) (hw : Multi C S single rejectedInput w) :
      n + n ≤ w ∧ w < n + n + C.gates.length := by
    constructor
    · by_contra h
      exact inputNotMulti ⟨w, by omega⟩ hw
    · by_contra h
      obtain ⟨p, _, _, _, _, sep, _⟩ := hw
      have ht := sep.1
      rw [missing_value C (single p) w (by change n + n + C.gates.length ≤ w; omega)] at ht
      exact Bool.noConfusion ht
  let G := (Finset.range C.gates.length).filter fun j =>
    (gateAt C j).op = GateOp.or ∧ Multi C S single rejectedInput (n + n + j)
  let W := G.image fun j => n + n + j
  have cardBound := frontier C S single rejectedInput circuitModel W
    (fun j hj hm hop _ _ => by
      refine Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, ?_⟩, rfl⟩
      refine ⟨?_, hm⟩
      have hget : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
      rwa [hget])
    multiRange (n + n + C.gates.length) {C.output}
    (fun w _ hw => (multiRange w hw).2) S (Finset.Subset.refl S)
    (fun p hp => ⟨C.output, Finset.mem_singleton_self _, outputSeparates p hp⟩)
  have filterLe := Finset.card_filter_le W (· < n + n + C.gates.length)
  have imageLe : W.card ≤ G.card := Finset.card_image_le
  rw [Finset.card_singleton] at cardBound
  refine ⟨G, by omega, ?_⟩
  intro j hj
  obtain ⟨hjRange, hor, hm⟩ := Finset.mem_filter.mp hj
  obtain ⟨p, _, q, _, distinct, hp, hq⟩ := hm
  have singletonValue (p : Fin n) : value C (single p) (n + n + j) =
      wireValue C (incidenceInput {p} {l}) (n + n + j) := by
    change (C.wires (List.ofFn (input {p}))).getD _ false = _
    rw [input_list]
    rfl
  have falseValue : value C rejectedInput (n + n + j) =
      wireValue C (incidenceInput Sᶜ {l}) (n + n + j) := by
    change (C.wires (List.ofFn (input Sᶜ))).getD _ false = _
    rw [input_list]
    rfl
  refine ⟨Finset.mem_range.mp hjRange, hor, falseValue.symm.trans hp.2,
    ⟨p, q, distinct, (singletonValue p).symm.trans hp.1, (singletonValue q).symm.trans hq.1⟩, ?_⟩
  intro u hu
  by_contra outside
  have implication (i : Fin (n + n)) : single u i = true → rejectedInput i = true := by
    refine Fin.addCases (motive := fun i => single u i = true → rejectedInput i = true) ?_ ?_ i
    · intro i hi
      have eq : i = u := by simpa [single, point] using hi
      subst i
      change input Sᶜ (Fin.castAdd n u) = true
      simpa only [point, decide_eq_true_eq, Finset.mem_compl] using outside
    · intro i hi
      simpa only [single, rejectedInput, line] using hi
  have result := mono C circuitModel (single u) rejectedInput implication (n + n + j)
    ((singletonValue u).trans hu)
  rw [hp.2] at result
  exact Bool.noConfusion result
