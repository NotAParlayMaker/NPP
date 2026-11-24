import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1469

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

def Step {n : ℕ} (C : Circuit) (X : (Fin n → Bool) → Prop) (R : Finset ℕ) : Prop :=
  ∀ w, n ≤ w → w < n + C.size → ∃ P : Finset ℕ, P.card ≤ 2 ∧ (w ∈ R → P.card ≤ 1) ∧
    (∀ r ∈ P, r < w) ∧
    ∀ (x y : Fin n → Bool), X x → X y → (∀ r ∈ P, value C x r = true → value C y r = true) →
      value C x w = true → value C y w = true

lemma value_mono {n : ℕ} (C : Circuit) (X : (Fin n → Bool) → Prop) (R : Finset ℕ)
    (hS : Step C X R)
    (x y : Fin n → Bool) (hx : X x) (hy : X y) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, _, hP, hstep⟩ := hS w (by omega) hw
      exact hstep x y hx hy fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

lemma cut {n : ℕ} (C : Circuit) (X : (Fin n → Bool) → Prop) (R : Finset ℕ)
    (hS : Step C X R)
    (G : Finset ℕ) (hGates : ∀ w ∈ G ∪ R, n ≤ w ∧ w < n + C.size)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G ∪ R → w < t) :
    ∃ B : Finset ℕ, Disjoint B (G ∪ R) ∧ B.card ≤ F.card + (G.filter (· < t)).card ∧
      ∀ x y : Fin n → Bool, X x → X y → (∀ w ∈ B, value C x w = true → value C y w = true) →
        ∀ w ∈ F, value C x w = true → value C y w = true := by
  induction t generalizing F with
  | zero =>
    exact ⟨F, Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega),
      Nat.le_add_right .., fun _ _ _ _ h => h⟩
  | succ t ih =>
    have hle : (G.filter (· < t)).card ≤ (G.filter (· < t + 1)).card :=
      Finset.card_le_card fun w hw =>
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,
          by have := (Finset.mem_filter.mp hw).2; omega⟩
    by_cases hex : t ∈ F ∧ t ∈ G ∪ R
    · obtain ⟨P, hPcard, hPR, hP, hp⟩ := hS t (hGates t hex.2).1 (hGates t hex.2).2
      let F' := F.erase t ∪ P
      have hF' : ∀ w ∈ F', w ∈ G ∪ R → w < t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hF w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact hP w hw
      obtain ⟨B, hd, hc, hi⟩ := ih F' hF'
      have hu := Finset.card_union_le (F.erase t) P
      have he := Finset.card_erase_add_one hex.1
      change F'.card ≤ _ at hu
      refine ⟨B, hd, ?_, ?_⟩
      · by_cases htG : t ∈ G
        · have hfilter : G.filter (· < t + 1) = insert t (G.filter (· < t)) := by
            ext w
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hg, hlt⟩
              by_cases h : w = t
              · exact Or.inl h
              · exact Or.inr ⟨hg, by omega⟩
            · rintro (rfl | ⟨hg, hlt⟩)
              · exact ⟨htG, by omega⟩
              · exact ⟨hg, by omega⟩
          rw [hfilter, Finset.card_insert_of_notMem (by simp)]
          omega
        · have htR : t ∈ R := (Finset.mem_union.mp hex.2).resolve_left htG
          have := hPR htR
          omega
      · intro x y hx hy hxy w hw
        by_cases h : w = t
        · subst w
          exact hp x y hx hy fun r hr => hi x y hx hy hxy r (Finset.mem_union_right _ hr)
        · exact hi x y hx hy hxy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩))
    · have hF' : ∀ w ∈ F, w ∈ G ∪ R → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      obtain ⟨B, hd, hc, hi⟩ := ih F hF'
      exact ⟨B, hd, by omega, hi⟩

def offSet {n : ℕ} (T : Finset (Fin n)) (p : Fin n) : Bool := decide (p ∉ T)

lemma weight {n : ℕ} (T : Finset (Fin n)) :
    (Finset.univ.filter (fun p => offSet T p = true)).card = n - T.card := by
  have h : Finset.univ.filter (fun p => offSet T p = true) = Tᶜ := by
    ext p
    simp [offSet]
  rw [h, Finset.card_compl, Fintype.card_fin]


def P (x y : Fin 7) : Bool := y - x == 1 || y - x == 2 || y - x == 4

theorem P_antisymm : ∀ x y : Fin 7, P x y = true → P y x = false := by decide

set_option maxRecDepth 100000 in
theorem P_dom : ∀ T : Finset (Fin 7), T.card ≤ 2 → ∃ z : Fin 7, z ∉ T ∧ ∀ y ∈ T, P z y = true := by
  decide +kernel


lemma anchors : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (A : Finset (Fin n)),
    A.card = 7 → (∀ i : Fin m, (S i ∩ A).card ≤ 2) →
    ∃ (r : Fin n → Fin n → Prop) (f : Fin m → Fin n), (∀ a b : Fin n, r a b → ¬ r b a) ∧
      ∀ i : Fin m, f i ∈ A ∧ f i ∉ S i ∧ ∀ y ∈ S i ∩ A, r (f i) y := by
  classical
  intro n m S A hA hS
  let e : A ≃ Fin 7 := Finset.equivFinOfCardEq hA
  have hinj : ∀ x y : Fin 7, ((e.symm x : A) : Fin n) = ((e.symm y : A) : Fin n) → x = y :=
    fun x y h => e.symm.injective (Subtype.ext h)
  let r : Fin n → Fin n → Prop := fun a b =>
    ∃ x y : Fin 7, ((e.symm x : A) : Fin n) = a ∧ ((e.symm y : A) : Fin n) = b ∧
      PEqualNP.Outside.L_meta_1469.P x y = true
  have hf : ∀ i : Fin m, ∃ z : Fin n, z ∈ A ∧ z ∉ S i ∧ ∀ y ∈ S i ∩ A, r z y := by
    intro i
    let T : Finset (Fin 7) := Finset.univ.filter fun z : Fin 7 => ((e.symm z : A) : Fin n) ∈ S i
    have hT : T.card ≤ 2 := by
      refine le_trans (Finset.card_le_card_of_injOn (fun z => ((e.symm z : A) : Fin n)) ?_ ?_) (hS i)
      · intro z hz
        have hz' : ((e.symm z : A) : Fin n) ∈ S i := by simpa [T] using hz
        exact Finset.mem_coe.2 (Finset.mem_inter.2 ⟨hz', (e.symm z).2⟩)
      · intro x _ y _ h
        exact hinj x y h
    obtain ⟨z, hz, hdom⟩ := PEqualNP.Outside.L_meta_1469.P_dom T hT
    refine ⟨((e.symm z : A) : Fin n), (e.symm z).2, ?_, ?_⟩
    · intro hin
      exact hz (by simpa [T] using hin)
    · intro y hy
      obtain ⟨hyS, hyA⟩ := Finset.mem_inter.1 hy
      refine ⟨z, e ⟨y, hyA⟩, rfl, by simp, ?_⟩
      apply hdom
      simpa [T] using hyS
  choose f hfA hfS hfr using hf
  refine ⟨r, f, ?_, fun i => ⟨hfA i, hfS i, hfr i⟩⟩
  rintro a b ⟨x, y, hxa, hyb, hP⟩ ⟨x', y', hxb, hya, hP'⟩
  have h1 : x' = y := hinj _ _ (hxb.trans hyb.symm)
  have h2 : y' = x := hinj _ _ (hya.trans hxa.symm)
  subst h1 h2
  rw [PEqualNP.Outside.L_meta_1469.P_antisymm _ _ hP] at hP'
  exact Bool.false_ne_true hP'

lemma main : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n)) (A : Finset (Fin n)),
    2 ≤ q → 1 ≤ m → q + 3 ≤ n → (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ v : Fin n, ∃ i : Fin m, v ∈ S i) →
    A.card = 7 → (∀ i : Fin m, (S i ∩ A).card ≤ 2) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) →
    (∀ x : Fin n → Bool, 2 ≤ (Finset.univ.filter (fun v => x v = true)).card →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn x) = false) →
    m * q + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length := by
  classical
  intro q n m S A hq hm hn hsize hinter _ hA hcap gates out j hg hj huniq heval hfalse
  let C : Circuit := ⟨gates, 0⟩
  let Rd := Finset.univ.filter (fun i : Fin gates.length =>
    j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)
  let R : Finset ℕ := insert (n + (j : ℕ)) (Rd.image (fun i : Fin gates.length => n + (i : ℕ)))
  let X : (Fin n → Bool) → Prop := fun x =>
    2 ≤ (Finset.univ.filter (fun v : Fin n => x v = true)).card
  have hjv : ∀ x, X x → value C x (n + (j : ℕ)) = false := fun x hx => hfalse x hx
  have hnotR : n + (j : ℕ) ∉ Rd.image (fun i : Fin gates.length => n + (i : ℕ)) := by
    intro h
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
    have := (Finset.mem_filter.mp hi).2.1
    have : (j : ℕ) < (i : ℕ) := this
    omega
  have hRcard : R.card = Rd.card + 1 := by
    rw [Finset.card_insert_of_notMem hnotR, Finset.card_image_of_injective]
    intro a b hab
    exact Fin.ext (by simpa using hab)
  have hR : ∀ w ∈ R, n ≤ w ∧ w < n + C.size := by
    intro w hw
    rcases Finset.mem_insert.mp hw with h | h
    · rw [h]
      exact ⟨by omega, by change _ < n + gates.length; omega⟩
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
      exact ⟨by omega, by change _ < n + gates.length; omega⟩
  have hS : Step C X R := by
    intro w hn hw
    have hk : w - n < gates.length := by change w < n + gates.length at hw; omega
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    simp only [Nat.add_sub_cancel_left] at hk
    by_cases hkj : k = (j : ℕ)
    · refine ⟨∅, by simp, by simp, by simp, fun x y hx hy _ h => ?_⟩
      rw [hkj, hjv x hx] at h
      exact Bool.noConfusion h
    · have hop : gates[k].op = GateOp.and ∨ gates[k].op = GateOp.or := by
        rcases (hg gates[k] (List.getElem_mem _)).1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd (congrArg Fin.val (huniq ⟨k, hk⟩ h)) hkj
      have hlen := (hg gates[k] (List.getElem_mem _)).2
      let P0 := gates[k].inputs.toFinset.filter (· < n + k)
      have hP0 : P0.card ≤ 2 :=
        (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen)
      by_cases hR' : n + k ∈ R
      · have hrd : (j : ℕ) < k ∧ n + (j : ℕ) ∈ gates[k].inputs := by
          rcases Finset.mem_insert.mp hR' with h | h
          · omega
          · obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
            have hik : (i : ℕ) = k := by omega
            have hi2 := (Finset.mem_filter.mp hi).2
            have e : i = ⟨k, hk⟩ := Fin.ext hik
            rw [e] at hi2
            exact ⟨hi2.1, hi2.2⟩
        have hmem : n + (j : ℕ) ∈ P0 :=
          Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hrd.2, by omega⟩
        refine ⟨P0.erase (n + (j : ℕ)), (Finset.card_erase_le).trans hP0, fun _ => ?_,
          fun r hr => (Finset.mem_filter.mp (Finset.mem_of_mem_erase hr)).2, ?_⟩
        · have := Finset.card_erase_add_one hmem
          omega
        · intro x y hx hy hxy
          refine gate_mono C k hk hop x y fun r hm hlt hv => ?_
          by_cases hrj : r = n + (j : ℕ)
          · rw [hrj, hjv x hx] at hv
            exact Bool.noConfusion hv
          · exact hxy r (Finset.mem_erase.mpr ⟨hrj,
              Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hm, hlt⟩⟩) hv
      · refine ⟨P0, hP0, fun h => absurd h hR', fun r hr => (Finset.mem_filter.mp hr).2, ?_⟩
        intro x y _ _ hxy
        exact gate_mono C k hk hop x y fun r hm hlt hv =>
          hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hm, hlt⟩) hv
  have htop : X (offSet (∅ : Finset (Fin n))) := by
    change 2 ≤ _
    rw [weight]
    simp
    omega
  have hread (x : Fin n → Bool) (hx : X x) :
      (((gates.get j).inputs.map (fun r => if r < n + j.val then value C x r else false)).headD false) = true := by
    have h := gate_value C x (n + j.val) (by omega) (by change _ < n + gates.length; omega)
    simp only [Nat.add_sub_cancel_left] at h
    change value C x (n + j.val) = (gates.get j).op.eval _ at h
    rw [hj, hjv x hx] at h
    simpa [GateOp.eval] using h.symm
  obtain ⟨u, tail, hlist⟩ : ∃ u tail, (gates.get j).inputs = u :: tail := by
    cases hh : (gates.get j).inputs with
    | nil =>
      have hh' := hread _ htop
      rw [hh] at hh'
      contradiction
    | cons u tail => exact ⟨u,tail,rfl⟩
  have hprev : u < n + j.val := by
    by_contra h
    have hh := hread _ htop
    rw [hlist] at hh
    simp [h] at hh
  have hu (x : Fin n → Bool) (hx : X x) : value C x u = true := by
    have hh := hread x hx
    rw [hlist] at hh
    simpa [hprev] using hh
  have hnu : n ≤ u := by
    by_contra! h
    let v : Fin n := ⟨u,h⟩
    have hx : X (offSet {v}) := by
      change 2 ≤ _
      rw [weight, Finset.card_singleton]
      omega
    have hh := hu _ hx
    change value C (offSet {v}) v = true at hh
    simp [input_value,offSet] at hh
  have huR : u ∉ R := by
    intro h
    rcases Finset.mem_insert.mp h with hh | hh
    · omega
    · obtain ⟨i,hi,hh⟩ := Finset.mem_image.mp hh
      have hji : j.val < i.val := (Finset.mem_filter.mp hi).2.1
      omega
  obtain ⟨r,f,hr,hf⟩ := anchors n m S A hA hcap
  let y (i : Fin m) := offSet (S i)
  let x (i : Fin m) (p : Fin n) (v : Fin n) := decide (v = p ∨ v = f i)
  have hy (i : Fin m) : X (y i) := by
    change 2 ≤ _
    rw [show y i = offSet (S i) from rfl, weight, hsize]
    omega
  have hx (i : Fin m) (p : Fin n) (hp : p ∈ S i) : X (x i p) := by
    have hne : p ≠ f i := fun h => (hf i).2.1 (h ▸ hp)
    have he : Finset.univ.filter (fun v => x i p v = true) = {p,f i} := by
      ext v
      simp [x]
    change 2 ≤ _
    rw [he]
    simp [hne]
  let D (i : Fin m) (w : ℕ) := (S i).filter (fun p => value C (x i p) w = true ∧ value C (y i) w = false)
  let G (i : Fin m) := (Finset.Ico n (n+C.size)).filter (fun w => w ∉ R ∧ 2 ≤ (D i w).card)
  have anchor_hit (i k : Fin m) (hik : i ≠ k) (w : ℕ) (hi : 2 ≤ (D i w).card)
      (hk : value C (y k) w = false) : f i ∈ S k := by
    by_contra hfk
    have hsub : D i w ⊆ S i ∩ S k := by
      intro p hp
      obtain ⟨hpS,hpx,_⟩ := Finset.mem_filter.mp hp
      refine Finset.mem_inter.mpr ⟨hpS,?_⟩
      by_contra hpk
      have hle : ∀ v, x i p v = true → y k v = true := by
        intro v hv
        rcases of_decide_eq_true hv with h | h
        · simpa [y,offSet,h] using hpk
        · simpa [y,offSet,h] using hfk
      have ht := value_mono C X R hS _ _ (hx i p hpS) (hy k) hle w hpx
      simp [hk] at ht
    have hc := (Finset.card_le_card hsub).trans (hinter i k hik)
    omega
  have neg_wire (i : Fin m) (w : ℕ) (hw : w ∈ G i) : value C (y i) w = false := by
    have hc := (Finset.mem_filter.mp hw).2.2
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < (D i w).card by omega)
    exact (Finset.mem_filter.mp hp).2.2
  have hd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ k _ hik
    refine Finset.disjoint_left.mpr fun w hi hk => ?_
    have ha := anchor_hit i k hik w (Finset.mem_filter.mp hi).2.2 (neg_wire k w hk)
    have hb := anchor_hit k i hik.symm w (Finset.mem_filter.mp hk).2.2 (neg_wire i w hi)
    exact hr _ _ ((hf i).2.2 _ (Finset.mem_inter.mpr ⟨hb,(hf k).1⟩))
      ((hf k).2.2 _ (Finset.mem_inter.mpr ⟨ha,(hf i).1⟩))
  have count (i : Fin m) : q ≤ (G i).card := by
    have bounds : ∀ w ∈ G i ∪ R, n ≤ w ∧ w < n + C.size := by
      intro w hw
      rcases Finset.mem_union.mp hw with h | h
      · exact Finset.mem_Ico.mp (Finset.mem_filter.mp h).1
      · exact hR w h
    obtain ⟨B,hdis,hcard,hcut⟩ := cut C X R hS (G i) bounds (n+C.size) {out i}
      (fun w _ hw => (bounds w hw).2)
    have cover : S i ⊆ B.biUnion (D i) := by
      intro p hp
      by_contra h
      have hle : ∀ w ∈ B, value C (x i p) w = true → value C (y i) w = true := by
        intro w hw hwx
        by_contra! hwy
        exact h (Finset.mem_biUnion.mpr ⟨w,hw,Finset.mem_filter.mpr ⟨hp,hwx,by simpa using hwy⟩⟩)
      have hpos := heval i (x i p)
      change value C (x i p) (out i) = _ at hpos
      have hex : ∃ v ∈ S i, x i p v = true := ⟨p,hp,by simp [x]⟩
      rw [decide_eq_true hex] at hpos
      have ht := hcut _ _ (hx i p hp) (hy i) hle (out i) (by simp) hpos
      have hneg := heval i (y i)
      change value C (y i) (out i) = _ at hneg
      have hnone : ¬ ∃ v ∈ S i, y i v = true := by simp [y,offSet]
      rw [decide_eq_false hnone] at hneg
      exact Bool.noConfusion (ht.symm.trans hneg)
    have small (w : ℕ) (hw : w ∈ B) : (D i w).card ≤ 1 := by
      by_contra! hl
      have hlarge : 2 ≤ (D i w).card := by omega
      have hnr := Finset.disjoint_left.mp hdis hw
      by_cases hlow : w < n
      · let v : Fin n := ⟨w,hlow⟩
        have hsub : D i w ⊆ {v} := by
          intro p hp
          obtain ⟨hpS,ht,hnv⟩ := Finset.mem_filter.mp hp
          change value C (x i p) v = true at ht
          change value C (y i) v = false at hnv
          simp only [input_value] at ht hnv
          have hvS : v ∈ S i := by simpa [y,offSet] using hnv
          rcases of_decide_eq_true ht with he | he
          · exact Finset.mem_singleton.mpr he.symm
          · exact False.elim ((hf i).2.1 (he ▸ hvS))
        have hc := Finset.card_le_card hsub
        simp only [Finset.card_singleton] at hc
        omega
      by_cases hhigh : w < n+C.size
      · apply hnr
        apply Finset.mem_union_left
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,hhigh⟩,
          fun h => hnr (Finset.mem_union_right _ h),hlarge⟩
      · obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < (D i w).card by omega)
        have ht := (Finset.mem_filter.mp hp).2.1
        simp [missing_value C (x i p) w (by omega)] at ht
    have h1 := Finset.card_le_card cover
    have h2 := Finset.card_biUnion_le_card_mul B (D i) 1 small
    have h3 := Finset.card_filter_le (G i) (· < n+C.size)
    rw [hsize] at h1
    simp only [Nat.mul_one] at h2
    simp only [Finset.card_singleton] at hcard
    omega
  let U := Finset.univ.biUnion G
  have hsum : m*q ≤ U.card := by
    calc
      m*q = ∑ _i : Fin m, q := by simp
      _ ≤ ∑ i : Fin m, (G i).card := Finset.sum_le_sum fun i _ => count i
      _ = U.card := (Finset.card_biUnion hd).symm
  have hdis : Disjoint U R := by
    refine Finset.disjoint_left.mpr fun w hw h => ?_
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hw
    exact (Finset.mem_filter.mp hi).2.1 h
  have hno : u ∉ U ∪ R := by
    intro hu'
    rcases Finset.mem_union.mp hu' with h | h
    · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp h
      exact Bool.noConfusion ((hu _ (hy i)).symm.trans (neg_wire i u hi))
    · exact huR h
  have hs : insert u (U ∪ R) ⊆ Finset.Ico n (n+C.size) := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact Finset.mem_Ico.mpr ⟨hnu,by change _ < n + gates.length; omega⟩
    rcases Finset.mem_union.mp hw with h | h
    · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp h
      exact (Finset.mem_filter.mp hi).1
    · exact Finset.mem_Ico.mpr (hR w h)
  have ht := Finset.card_le_card hs
  rw [Finset.card_insert_of_notMem hno, Finset.card_union_of_disjoint hdis, hRcard] at ht
  have he : (Finset.Ico n (n+C.size)).card = gates.length := by simp [C,Circuit.size]
  change m*q + Rd.card + 2 ≤ gates.length
  omega

end PEqualNP.Outside.L_meta_1469

theorem PEqualNP.Outside.L_meta_1469 : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n)) (A : Finset (Fin n)),
    2 ≤ q → 1 ≤ m → q + 3 ≤ n → (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ v : Fin n, ∃ i : Fin m, v ∈ S i) →
    A.card = 7 → (∀ i : Fin m, (S i ∩ A).card ≤ 2) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) →
    (∀ x : Fin n → Bool, 2 ≤ (Finset.univ.filter (fun v => x v = true)).card →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn x) = false) →
    m * q + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length :=
  PEqualNP.Outside.L_meta_1469.main
