import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1594

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

def Light {n : ℕ} (K : ℕ) (y : Fin n → Bool) : Prop :=
  (Finset.univ.filter (fun q : Fin n => y q = true)).card < K

lemma gate_inputs {n : ℕ} (C : Circuit) (t K : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hN : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not → (i : ℕ) = t)
    (hT : ∀ y : Fin n → Bool, Light K y → value C y (n + t) = true)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), Light K y →
        (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  by_cases ht : w = n + t
  · subst ht
    exact ⟨∅, by simp, by simp, fun x y hy _ _ => hT y hy⟩
  · have hj : w - n < C.gates.length := by unfold Circuit.size at hw; omega
    obtain ⟨hop, hlen⟩ := hG (C.gates[w - n]'hj) (List.getElem_mem _)
    have hnot : (C.gates[w - n]'hj).op ≠ GateOp.not := by
      intro h
      have h2 : w - n = t := hN ⟨w - n, hj⟩ h
      omega
    refine ⟨(C.gates[w - n]'hj).inputs.toFinset.filter (· < w),
      (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen), ?_, ?_⟩
    · intro r hr
      exact (Finset.mem_filter.mp hr).2
    · intro x y _ hxy hx
      have formula (z : Fin n → Bool) : value C z w = (C.gates[w - n]'hj).op.eval
          ((C.gates[w - n]'hj).inputs.map fun r => if r < w then value C z r else false) :=
        gate_value C z w hn hw
      rw [formula x] at hx
      rw [formula y]
      have hr (r : ℕ) (hr : r ∈ (C.gates[w - n]'hj).inputs) :
          (if r < w then value C x r else false) = true →
          (if r < w then value C y r else false) = true := by
        by_cases h : r < w
        · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, h⟩)
        · simp [h]
      rcases hop with hop | hop | hop
      · rw [hop] at hx ⊢
        simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hx ⊢
        rintro b ⟨r, hrm, rfl⟩
        exact hr r hrm (hx _ ⟨r, hrm, rfl⟩)
      · rw [hop] at hx ⊢
        simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
        obtain ⟨b, ⟨r, hrm, rfl⟩, hb⟩ := hx
        exact ⟨_, ⟨r, hrm, rfl⟩, hr r hrm hb⟩
      · exact absurd hop hnot

lemma value_mono {n : ℕ} (C : Circuit) (t K : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hN : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not → (i : ℕ) = t)
    (hT : ∀ y : Fin n → Bool, Light K y → value C y (n + t) = true)
    (x y : Fin n → Bool) (hy : Light K y) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := input_value C x ⟨w, hn⟩
      have h2 := input_value C y ⟨w, hn⟩
      simp only at h1 h2
      rw [h1, h2]
      exact hxy ⟨w, hn⟩
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C t K hG hN hT w (by omega) hw
      exact hstep x y hy fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

lemma cut {n : ℕ} (C : Circuit) (t K : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hN : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not → (i : ℕ) = t)
    (hT : ∀ y : Fin n → Bool, Light K y → value C y (n + t) = true)
    (G : Finset ℕ) (hGates : ∀ w ∈ G, n ≤ w ∧ w < n + C.size)
    (s : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G → w < s) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ F.card + (G.filter (· < s)).card ∧
      ∀ x y : Fin n → Bool, Light K y →
        (∀ w ∈ B, value C x w = true → value C y w = true) →
        ∀ w ∈ F, value C x w = true → value C y w = true := by
  induction s generalizing F with
  | zero =>
    exact ⟨F, Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega),
      Nat.le_add_right .., fun _ _ _ h => h⟩
  | succ s ih =>
    by_cases hex : s ∈ F ∧ s ∈ G
    · obtain ⟨P, hPcard, hP, hp⟩ :=
        gate_inputs C t K hG hN hT s (hGates s hex.2).1 (hGates s hex.2).2
      have hF' : ∀ w ∈ F.erase s ∪ P, w ∈ G → w < s := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hF w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact hP w hw
      obtain ⟨B, hd, hc, hi⟩ := ih (F.erase s ∪ P) hF'
      have hsize : (F.erase s ∪ P).card ≤ F.card + 1 := by
        have hu := Finset.card_union_le (F.erase s) P
        have he := Finset.card_erase_add_one hex.1
        omega
      have hfilter : G.filter (· < s + 1) = insert s (G.filter (· < s)) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hg, hlt⟩
          by_cases h : w = s
          · exact Or.inl h
          · exact Or.inr ⟨hg, by omega⟩
        · rintro (rfl | ⟨hg, hlt⟩)
          · exact ⟨hex.2, by omega⟩
          · exact ⟨hg, by omega⟩
      refine ⟨B, hd, ?_, ?_⟩
      · rw [hfilter, Finset.card_insert_of_notMem (by simp)]
        omega
      · intro x y hy hxy w hw
        by_cases h : w = s
        · subst w
          exact hp x y hy fun r hr => hi x y hy hxy r (Finset.mem_union_right _ hr)
        · exact hi x y hy hxy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩))
    · have hF' : ∀ w ∈ F, w ∈ G → w < s := by
        intro w hw hg
        have hne : w ≠ s := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      obtain ⟨B, hd, hc, hi⟩ := ih F hF'
      have hle : (G.filter (· < s)).card ≤ (G.filter (· < s + 1)).card :=
        Finset.card_le_card fun w hw =>
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,
            by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hd, by omega, hi⟩

def support {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => value C (fun q => decide (q = p)) w = true)

lemma mem_support {n : ℕ} (C : Circuit) (w : ℕ) (p : Fin n) :
    p ∈ support C w ↔ value C (fun q => decide (q = p)) w = true := by
  simp [support]

lemma support_gate {n : ℕ} (C : Circuit) (w : ℕ) (h : 2 ≤ (support (n := n) C w).card) :
    n ≤ w ∧ w < n + C.size := by
  constructor
  · by_contra! hw
    have hs : support C w ⊆ {(⟨w, hw⟩ : Fin n)} := by
      intro q hq
      have hv := (mem_support C w q).mp hq
      have h1 := input_value C (fun r => decide (r = q)) ⟨w, hw⟩
      simp only at h1
      rw [h1] at hv
      simpa [eq_comm] using hv
    have hb := Finset.card_le_card hs
    simp at hb
    omega
  · by_contra! hw
    have hs : support (n := n) C w = ∅ := by
      ext q
      simp [mem_support, missing_value C _ w hw]
    simp [hs] at h

def assigned {n : ℕ} (C : Circuit) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter fun w => support C w ⊆ T ∧ 2 ≤ (support (n := n) C w).card

lemma card_assigned {n c : ℕ} (C : Circuit) (T : Finset (Fin n)) (o t K : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hN : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not → (i : ℕ) = t)
    (hT : ∀ y : Fin n → Bool, Light K y → value C y (n + t) = true)
    (ho : ∀ p : Fin n, value C (fun q => decide (q = p)) o = true ↔ p ∈ T)
    (hsparse : ∀ x : Fin n → Bool, (∀ q ∈ T, x q = false) → value C x o = false)
    (hk : c < K) (hc : c + 1 ≤ T.card) : c ≤ (assigned C T).card := by
  classical
  by_contra! hsmall
  have hgate : ∀ w ∈ assigned C T, n ≤ w ∧ w < n + C.size := by
    intro w hw
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B, hd, hBcard, hcut⟩ := cut C t K hG hN hT (assigned C T) hgate (n + C.size) {o}
    (fun w _ hw => (hgate w hw).2)
  have hb : B.card ≤ c := by
    have hfilter := Finset.card_filter_le (assigned C T) (fun w => w < n + C.size)
    simp only [Finset.card_singleton] at hBcard
    omega
  let clean (w : ℕ) : Finset (Fin n) := if support C w ⊆ T then support C w else ∅
  have hclean : ∀ w ∈ B, (clean w).card ≤ 1 := by
    intro w hw
    by_cases hs : support C w ⊆ T
    · change (if support C w ⊆ T then support (n := n) C w else ∅).card ≤ 1
      rw [ite_eq_left hs]
      by_contra! hlarge
      exact Finset.disjoint_left.mp hd hw
        (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (support_gate C w (by omega)), hs, by omega⟩)
    · simp [clean, hs]
  have hcover : (B.biUnion clean).card < T.card := by
    have h := Finset.card_biUnion_le_card_mul B clean 1 hclean
    simp only [mul_one] at h
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  let D := B.filter (fun w => ¬ support C w ⊆ T)
  have hout (w : {w // w ∈ D}) : ∃ q : Fin n, q ∈ support C w.val ∧ q ∉ T := by
    by_contra! h
    exact (Finset.mem_filter.mp w.property).2 h
  choose q hq using hout
  let U := D.attach.image q
  let y : Fin n → Bool := fun r => decide (r ∈ U)
  have hu : U.card ≤ c := calc
    U.card ≤ D.attach.card := Finset.card_image_le
    _ = D.card := Finset.card_attach
    _ ≤ B.card := Finset.card_filter_le _ _
    _ ≤ c := hb
  have hylight : Light K y := by
    have hset : Finset.univ.filter (fun r => y r = true) = U := by ext r; simp [y]
    unfold Light
    rw [hset]
    omega
  have hyfalse : value C y o = false := by
    apply hsparse y
    intro r hr
    have hnot : r ∉ U := by
      intro hmem
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hmem
      exact (hq w).2 hr
    simp [y, hnot]
  have hytrue : value C y o = true := by
    apply hcut (fun r => decide (r = p)) y hylight _ o (Finset.mem_singleton_self o)
      ((ho p).mpr hp)
    intro w hw hx
    by_cases hs : support C w ⊆ T
    · exact False.elim (hpnot (Finset.mem_biUnion.mpr
        ⟨w, hw, by simpa only [clean, ite_eq_left hs, mem_support] using hx⟩))
    · apply value_mono C t K hG hN hT (fun r => decide (r = q ⟨w, Finset.mem_filter.mpr ⟨hw, hs⟩⟩))
        y hylight _ w
        ((mem_support C w (q ⟨w, Finset.mem_filter.mpr ⟨hw, hs⟩⟩)).mp
          (hq ⟨w, Finset.mem_filter.mpr ⟨hw, hs⟩⟩).1)
      intro r hr
      have he : r = q ⟨w, Finset.mem_filter.mpr ⟨hw, hs⟩⟩ := of_decide_eq_true hr
      have hm : q ⟨w, Finset.mem_filter.mpr ⟨hw, hs⟩⟩ ∈ U :=
        Finset.mem_image_of_mem q (Finset.mem_attach D _)
      rw [he]
      simp [y, hm]
  simp [hyfalse] at hytrue

lemma main (N M : ℕ) (A : Fin M → Finset (Fin N)) (D : Circuit) (u : Fin M → ℕ) (t : ℕ)
    (Y : Finset (Fin N))
    (hG : ∀ eb1 ∈ D.gates, (eb1.op = GateOp.and ∨ eb1.op = GateOp.or ∨ eb1.op = GateOp.not) ∧
      eb1.inputs.length ≤ 2)
    (hN : ∀ lb1 : Fin D.gates.length, (D.gates.get lb1).op = GateOp.not → (lb1 : ℕ) = t)
    (hu : ∀ (ab3 : Fin M) (zb1 : Fin N → Bool),
      (D.wires (List.ofFn zb1)).getD (u ab3) false = decide (∃ sb1 ∈ A ab3, zb1 sb1 = true))
    (hT : ∀ zb2 : Fin N → Bool, (Finset.univ.filter (fun vb1 : Fin N => zb2 vb1 = true)).card
      < Y.card → (D.wires (List.ofFn zb2)).getD (N + t) false = true)
    (hY : 2 ≤ Y.card) (b4 : Fin M) :
    min Y.card (A b4).card ≤ (Finset.univ.filter (fun h1 : Fin D.gates.length =>
      (∀ s2 : Fin N, (D.wires (List.ofFn (fun w1 : Fin N => decide (w1 = s2)))).getD (N + h1) false
        = true → s2 ∈ A b4) ∧ 2 ≤ (Finset.univ.filter (fun s3 : Fin N =>
        (D.wires (List.ofFn (fun w2 : Fin N => decide (w2 = s3)))).getD (N + h1) false
        = true)).card)).card + 1 := by
  have hmin := Nat.min_le_right Y.card (A b4).card
  have hmin2 := Nat.min_le_left Y.card (A b4).card
  by_cases hA : (A b4).card = 0
  · omega
  have ho : ∀ p : Fin N, value D (fun q => decide (q = p)) (u b4) = true ↔ p ∈ A b4 := by
    intro p
    change (D.wires (List.ofFn (fun q : Fin N => decide (q = p)))).getD (u b4) false = true ↔ _
    rw [hu b4]
    simp
  have hsparse : ∀ x : Fin N → Bool, (∀ q ∈ A b4, x q = false) → value D x (u b4) = false := by
    intro x hx
    change (D.wires (List.ofFn x)).getD (u b4) false = false
    rw [hu b4]
    simpa using hx
  have hc := card_assigned (c := min Y.card (A b4).card - 1) D (A b4) (u b4) t Y.card hG hN hT
    ho hsparse (by omega) (by omega)
  have key : (assigned D (A b4)).card ≤ (Finset.univ.filter (fun h1 : Fin D.gates.length =>
      (∀ s2 : Fin N, (D.wires (List.ofFn (fun w1 : Fin N => decide (w1 = s2)))).getD (N + h1) false
        = true → s2 ∈ A b4) ∧ 2 ≤ (Finset.univ.filter (fun s3 : Fin N =>
        (D.wires (List.ofFn (fun w2 : Fin N => decide (w2 = s3)))).getD (N + h1) false
        = true)).card)).card := by
    refine le_trans (Finset.card_le_card ?_)
      (Finset.card_image_le (f := fun h : Fin D.gates.length => N + (h : ℕ)))
    intro w hw
    obtain ⟨hI, hs, h2⟩ := Finset.mem_filter.mp hw
    have hI2 := Finset.mem_Ico.mp hI
    obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
    have hj : j < D.gates.length := by
      have := hI2.2
      unfold Circuit.size at this
      omega
    refine Finset.mem_image.mpr ⟨⟨j, hj⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, rfl⟩
    · intro s2 h
      exact hs ((mem_support D (N + j) s2).mpr h)
    · exact h2
  omega

end PEqualNP.Outside.L_meta_1594

theorem PEqualNP.Outside.L_meta_1594 : (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))) → (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size) → ∀ (N M : ℕ) (A : Fin M → Finset (Fin N)) (D : PEqualNP.CircuitLowerBounds.Circuit) (u : Fin M → ℕ) (t : ℕ) (Y : Finset (Fin N)), (∀ ab1 ab2 : Fin M, ab1 ≠ ab2 → (A ab1 ∩ A ab2).card ≤ 1) → (∀ eb1 ∈ D.gates, (eb1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ eb1.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ eb1.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ eb1.inputs.length ≤ 2) → (∀ lb1 : Fin D.gates.length, (D.gates.get lb1).op = PEqualNP.CircuitLowerBounds.GateOp.not → (lb1 : ℕ) = t) → (∀ (ab3 : Fin M) (zb1 : Fin N → Bool), (D.wires (List.ofFn zb1)).getD (u ab3) false = decide (∃ sb1 ∈ A ab3, zb1 sb1 = true)) → (∀ zb2 : Fin N → Bool, (Finset.univ.filter (fun vb1 : Fin N => zb2 vb1 = true)).card < Y.card → (D.wires (List.ofFn zb2)).getD (N + t) false = true) → (D.wires (List.ofFn (fun vb2 : Fin N => decide (vb2 ∈ Y)))).getD (N + t) false = false → 2 ≤ Y.card → ∀ b4 : Fin M, min Y.card (A b4).card ≤ (Finset.univ.filter (fun h1 : Fin D.gates.length => (∀ s2 : Fin N, (D.wires (List.ofFn (fun w1 : Fin N => decide (w1 = s2)))).getD (N + h1) false = true → s2 ∈ A b4) ∧ 2 ≤ (Finset.univ.filter (fun s3 : Fin N => (D.wires (List.ofFn (fun w2 : Fin N => decide (w2 = s3)))).getD (N + h1) false = true)).card)).card + 1 := by
  intro _ _ N M A D u t Y _ hG hN hu hT _ hY b4
  exact PEqualNP.Outside.L_meta_1594.main N M A D u t Y hG hN hu hT hY b4
