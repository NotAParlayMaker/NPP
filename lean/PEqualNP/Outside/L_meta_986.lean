import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_986

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

def value {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (run gs (List.ofFn x)).getD w false

lemma eval_eq {n : ℕ} (gs : List Gate) (k : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨gs, k⟩ (List.ofFn x) = value gs x k := rfl

lemma input_value {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (p : Fin n) :
    value gs x p = x p := by
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  unfold value
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : n + gs.length ≤ w) : value gs x w = false := by
  unfold value
  exact List.getD_eq_default _ _ (by simpa [run_length] using hw)

lemma gate_value {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (j : ℕ) (hj : j < gs.length) :
    value gs x (n + j) = gs[j].op.eval
      (gs[j].inputs.map fun r => if r < n + j then value gs x r else false) := by
  let g := gs[j]
  let earlier := run (gs.take j) (List.ofFn x)
  have plen : earlier.length = n + j := by
    simp [earlier, run_length, Nat.min_eq_left hj.le]
  have split : run gs (List.ofFn x) = run (g :: gs.drop (j + 1)) earlier := by
    rw [run_split gs (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < n + j then value gs x r else false := by
    by_cases hr : r < n + j
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run gs (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  show (run gs (List.ofFn x)).getD (n + j) false = _
  rw [split, run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read, g]

lemma op_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f g : ℕ → Bool) (h : ∀ r ∈ l, f r = true → g r = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    intro hx r hr
    exact h r hr (hx r hr)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
    rintro ⟨r, hr, hx⟩
    exact ⟨r, hr, h r hr hx⟩

lemma not_wire {n : ℕ} (gs : List Gate) (i0 : Fin gs.length) (hw : ℕ)
    (hi0 : (gs.get i0).op = GateOp.not) (hh : (gs.get i0).inputs.head? = some hw)
    (hhw : hw < n + i0.val) (x : Fin n → Bool) (hx : value gs x hw = false) :
    value gs x (n + i0.val) = true := by
  rw [gate_value gs x i0.val i0.isLt]
  simp only [List.get_eq_getElem] at hi0 hh
  rw [hi0]
  cases h : (gs[i0.val]).inputs with
  | nil => simp [h] at hh
  | cons a rest =>
    simp [h] at hh
    subst hh
    simp [GateOp.eval, hhw, hx]

lemma mono0 {n : ℕ} (gs : List Gate) (T : Finset (Fin n)) (i0 : Fin gs.length) (hw : ℕ)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gs.length, (gs.get q).op = GateOp.not → q = i0)
    (hi0 : (gs.get i0).op = GateOp.not) (hh : (gs.get i0).inputs.head? = some hw)
    (hhw : hw < n + i0.val)
    (hT : ∀ y : Fin n → Bool, (∀ t ∈ T, y t = false) → value gs y hw = false)
    (x y : Fin n → Bool) (hy : ∀ t ∈ T, y t = false) (hxy : ∀ p, x p = true → y p = true)
    (w : ℕ) : value gs x w = true → value gs y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value gs x p = true → value gs y p = true
      simpa only [input_value] using hxy p
    by_cases hw2 : w < n + gs.length
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < gs.length := by omega
      by_cases hnj : (gs[j]).op = GateOp.not
      · have he := hnot ⟨j, hj⟩ (by simpa using hnj)
        have hj0 : j = i0.val := by rw [← he]
        subst hj0
        intro _
        exact not_wire gs i0 hw hi0 hh hhw y (hT y hy)
      · have hop : (gs[j]).op = GateOp.and ∨ (gs[j]).op = GateOp.or := by
          rcases (hG _ (List.getElem_mem hj)).1 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd h hnj
        rw [gate_value gs x j hj, gate_value gs y j hj]
        apply op_mono _ hop
        intro r _
        by_cases hlt : r < n + j
        · simp only [hlt, ite_true]
          exact ih r hlt
        · simp [hlt]
    · simp [missing_value gs x w (by omega)]

lemma gate_inputs {n : ℕ} (gs : List Gate)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (j : ℕ) (hj : j < gs.length) (hop : (gs[j]).op = GateOp.and ∨ (gs[j]).op = GateOp.or) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < n + j) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value gs x r = true → value gs y r = true) →
        value gs x (n + j) = true → value gs y (n + j) = true := by
  classical
  let P := (gs[j]).inputs.toFinset.filter (· < n + j)
  refine ⟨P, ?_, ?_, ?_⟩
  · calc P.card ≤ (gs[j]).inputs.toFinset.card := Finset.card_filter_le _ _
      _ ≤ (gs[j]).inputs.length := List.toFinset_card_le _
      _ ≤ 2 := (hG _ (List.getElem_mem hj)).2
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hxy
    rw [gate_value gs x j hj, gate_value gs y j hj]
    apply op_mono _ hop
    intro r hr
    by_cases hlt : r < n + j
    · simp only [hlt, ite_true]
      exact hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, hlt⟩)
    · simp [hlt]

lemma cut {n : ℕ} (gs : List Gate)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (G : Finset ℕ) (hGates : ∀ w ∈ G, ∃ j, ∃ hj : j < gs.length, w = n + j ∧
      ((gs[j]).op = GateOp.and ∨ (gs[j]).op = GateOp.or))
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G → w < t) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ F.card + (G.filter (· < t)).card ∧
      ∀ x y : Fin n → Bool, (∀ w ∈ B, value gs x w = true → value gs y w = true) →
        ∀ w ∈ F, value gs x w = true → value gs y w = true := by
  classical
  induction t generalizing F with
  | zero =>
    exact ⟨F, Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega),
      Nat.le_add_right .., fun _ _ h => h⟩
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ G
    · obtain ⟨j, hj, htj, hop⟩ := hGates t hex.2
      obtain ⟨P, hPcard, hP, hp⟩ := gate_inputs (n := n) gs hG j hj hop
      rw [← htj] at hP hp
      let F' := F.erase t ∪ P
      have hF' : ∀ w ∈ F', w ∈ G → w < t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hF w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact hP w hw
      obtain ⟨B, hd, hc, hi⟩ := ih F' hF'
      have hsize : F'.card ≤ F.card + 1 := by
        have hu := Finset.card_union_le (F.erase t) P
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        omega
      have hfilter : G.filter (· < t + 1) = insert t (G.filter (· < t)) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hg, hlt⟩
          by_cases h : w = t
          · exact Or.inl h
          · exact Or.inr ⟨hg, by omega⟩
        · rintro (rfl | ⟨hg, hlt⟩)
          · exact ⟨hex.2, by omega⟩
          · exact ⟨hg, by omega⟩
      refine ⟨B, hd, ?_, ?_⟩
      · rw [hfilter, Finset.card_insert_of_notMem (by simp)]
        omega
      · intro x y hxy w hw
        by_cases h : w = t
        · subst w
          exact hp x y fun r hr => hi x y hxy r (Finset.mem_union_right _ hr)
        · exact hi x y hxy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩))
    · have hF' : ∀ w ∈ F, w ∈ G → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      obtain ⟨B, hd, hc, hi⟩ := ih F hF'
      have hle : (G.filter (· < t)).card ≤ (G.filter (· < t + 1)).card :=
        Finset.card_le_card fun w hw =>
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,
            by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hd, by omega, hi⟩

def support {n : ℕ} (gs : List Gate) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => value gs (fun q => decide (q = p)) w = true)

lemma mem_support {n : ℕ} (gs : List Gate) (w : ℕ) (p : Fin n) :
    p ∈ support gs w ↔ value gs (fun q => decide (q = p)) w = true := by
  simp [support]

lemma support_gate {n : ℕ} (gs : List Gate) (w : ℕ)
    (h : 2 ≤ (support (n := n) gs w).card) : n ≤ w ∧ w < n + gs.length := by
  constructor
  · by_contra! hw
    let p : Fin n := ⟨w, hw⟩
    have hs : support gs w ⊆ {p} := by
      intro q hq
      have hv := (mem_support gs w q).mp hq
      change value gs (fun r => decide (r = q)) p = true at hv
      simpa [input_value, eq_comm] using hv
    have hb := Finset.card_le_card hs
    simp at hb
    omega
  · by_contra! hw
    have hs : support (n := n) gs w = ∅ := by
      ext q
      simp [mem_support, missing_value gs _ w hw]
    simp [hs] at h

def assigned {n : ℕ} (gs : List Gate) (S T : Finset (Fin n)) (t0 : Fin n) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun w =>
    value gs (fun _ : Fin n => false) w = false ∧ support gs w ⊆ S ∪ T ∧
      2 ≤ (support gs w ∩ (S \ T.erase t0)).card

lemma card_assigned {n : ℕ} (gs : List Gate) (T : Finset (Fin n)) (i0 : Fin gs.length) (hw : ℕ)
    (hG : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gs.length, (gs.get q).op = GateOp.not → q = i0)
    (hi0 : (gs.get i0).op = GateOp.not) (hh : (gs.get i0).inputs.head? = some hw)
    (hhw : hw < n + i0.val)
    (hT : ∀ y : Fin n → Bool, (∀ t ∈ T, y t = false) → value gs y hw = false)
    (S : Finset (Fin n)) (t0 : Fin n) (o : ℕ)
    (hout : ∀ x : Fin n → Bool, value gs x o = decide (∃ v ∈ S, x v = true)) :
    (S \ T.erase t0).card ≤ (assigned gs S T t0).card + 1 := by
  classical
  let G := assigned gs S T t0
  let Ss := S \ T.erase t0
  by_contra! hsmall
  have hgate : ∀ w ∈ G, ∃ j, ∃ hj : j < gs.length, w = n + j ∧
      ((gs[j]).op = GateOp.and ∨ (gs[j]).op = GateOp.or) := by
    intro w hw'
    obtain ⟨hI, h0, _, _⟩ := Finset.mem_filter.mp hw'
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hI
    refine ⟨w - n, by omega, by omega, ?_⟩
    have hj : w - n < gs.length := by omega
    rcases (hG _ (List.getElem_mem hj)).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have he := hnot ⟨w - n, hj⟩ (by simpa using h)
      have hw0 : w = n + i0.val := by rw [← he]; simp; omega
      rw [hw0, not_wire gs i0 hw hi0 hh hhw _ (hT _ (fun _ _ => rfl))] at h0
      exact Bool.noConfusion h0
  obtain ⟨B, hd, hBcard, hcut⟩ := cut gs hG G hgate (n + gs.length) {o}
    (fun w _ hw' => by
      obtain ⟨j, hj, rfl, _⟩ := hgate w hw'
      omega)
  have hb : B.card < Ss.card := by
    have hfilter := Finset.card_filter_le G (fun w => w < n + gs.length)
    simp only [Finset.card_singleton] at hBcard
    change G.card + 1 < Ss.card at hsmall
    omega
  let clean (w : ℕ) : Finset (Fin n) :=
    if value gs (fun _ : Fin n => false) w = false ∧ support gs w ⊆ S ∪ T then
      support gs w ∩ Ss else ∅
  have hclean : ∀ w ∈ B, (clean w).card ≤ 1 := by
    intro w hw'
    by_cases hs : value gs (fun _ : Fin n => false) w = false ∧ support gs w ⊆ S ∪ T
    · change (if value gs (fun _ : Fin n => false) w = false ∧ support gs w ⊆ S ∪ T then
        support gs w ∩ Ss else ∅).card ≤ 1
      rw [ite_eq_left hs]
      by_contra! hlarge
      have hsup : 2 ≤ (support (n := n) gs w).card :=
        le_trans hlarge (Finset.card_le_card Finset.inter_subset_left)
      exact Finset.disjoint_left.mp hd hw'
        (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (support_gate gs w hsup), hs.1, hs.2,
          hlarge⟩)
    · simp [clean, hs]
  have hcover : (B.biUnion clean).card < Ss.card := by
    have h := Finset.card_biUnion_le_card_mul B clean 1 hclean
    simp only [mul_one] at h
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  have hpS : p ∈ S := (Finset.mem_sdiff.mp hp).1
  let D := B.filter (fun w => ¬ support gs w ⊆ S ∪ T)
  have hwit (w : {w // w ∈ D}) : ∃ q : Fin n, q ∈ support gs w.val ∧ q ∉ S ∪ T := by
    by_contra! h
    exact (Finset.mem_filter.mp w.property).2 h
  choose q hq using hwit
  let U := D.attach.image q
  let y : Fin n → Bool := fun r => decide (r ∈ U)
  have hU : ∀ r, y r = true → r ∉ S ∪ T := by
    intro r hr
    have hmem : r ∈ U := of_decide_eq_true hr
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hmem
    exact (hq w).2
  have hy : ∀ t ∈ T, y t = false := by
    intro t ht
    by_contra h
    exact hU t (by simpa using h) (Finset.mem_union_right _ ht)
  have hyfalse : value gs y o = false := by
    rw [hout y]
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro v hv hyv
    exact hU v hyv (Finset.mem_union_left _ hv)
  have hptrue : value gs (fun r => decide (r = p)) o = true := by
    rw [hout]
    simp only [decide_eq_true_eq]
    exact ⟨p, hpS, by simp⟩
  have hytrue : value gs y o = true := by
    apply hcut (fun r => decide (r = p)) y _ o (Finset.mem_singleton_self o) hptrue
    intro w hw' hx
    by_cases h0 : value gs (fun _ : Fin n => false) w = true
    · exact mono0 gs T i0 hw hG hnot hi0 hh hhw hT _ y hy (fun _ h => by simp at h) w h0
    by_cases hs : support gs w ⊆ S ∪ T
    · exfalso
      have hcond : value gs (fun _ : Fin n => false) w = false ∧ support gs w ⊆ S ∪ T :=
        ⟨by simpa using h0, hs⟩
      apply hpnot
      refine Finset.mem_biUnion.mpr ⟨w, hw', ?_⟩
      change p ∈ (if value gs (fun _ : Fin n => false) w = false ∧ support gs w ⊆ S ∪ T then
        support gs w ∩ Ss else ∅)
      rw [ite_eq_left hcond]
      exact Finset.mem_inter.mpr ⟨(mem_support gs w p).mpr hx, hp⟩
    · let d : {w // w ∈ D} := ⟨w, Finset.mem_filter.mpr ⟨hw', hs⟩⟩
      apply mono0 gs T i0 hw hG hnot hi0 hh hhw hT (fun r => decide (r = q d)) y hy _ w
        ((mem_support gs w (q d)).mp (hq d).1)
      intro r hr
      have he : r = q d := of_decide_eq_true hr
      subst r
      have hm : q d ∈ U := Finset.mem_image_of_mem q (Finset.mem_attach D d)
      simp [y, hm]
  simp [hyfalse] at hytrue

lemma inter_sub {n : ℕ} (S S' T X : Finset (Fin n)) (t0 : Fin n)
    (hX : X ⊆ S' ∪ T) (hS : t0 ∈ S → t0 ∈ S') :
    X ∩ (S \ T.erase t0) ⊆ S ∩ S' := by
  intro x hx
  obtain ⟨hxX, hxs⟩ := Finset.mem_inter.mp hx
  obtain ⟨hxS, hxT⟩ := Finset.mem_sdiff.mp hxs
  refine Finset.mem_inter.mpr ⟨hxS, ?_⟩
  rcases Finset.mem_union.mp (hX hxX) with h | h
  · exact h
  · have : x = t0 := by
      by_contra hne
      exact hxT (Finset.mem_erase.mpr ⟨hne, h⟩)
    subst this
    exact hS hxS

end PEqualNP.Outside.L_meta_986

open PEqualNP.Outside.L_meta_986 in
theorem PEqualNP.Outside.L_meta_986 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (i0 : Fin gates.length) (hw : ℕ) (T : Finset (Fin n)) (t0 : Fin n), (∀ i : Fin m, 2 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ q : Fin gates.length, (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not → q = i0) → (gates.get i0).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get i0).inputs.head? = some hw → hw < n + i0.val → (∀ (o : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true)) → (∀ y : Fin n → Bool, (∀ t ∈ T, y t = false) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, hw⟩ (List.ofFn y) = false) → t0 ∈ T → (∀ t ∈ T, (Finset.univ.filter (fun a : Fin m => t ∈ S a)).card ≤ (Finset.univ.filter (fun b : Fin m => t0 ∈ S b)).card) → 1 + ∑ s : Fin m, ((S s).card - 1) ≤ gates.length + ∑ u ∈ T.erase t0, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
  classical
  intro n m S gates out i0 hw T t0 _ hinter hG hnot hi0 hh hhw hout hT _ _
  have hT' : ∀ y : Fin n → Bool, (∀ t ∈ T, y t = false) → value gates y hw = false :=
    fun y hy => by rw [← eval_eq]; exact hT y hy
  have hout' : ∀ (o : Fin m) (x : Fin n → Bool),
      PEqualNP.Outside.L_meta_986.value gates x (out o) = decide (∃ v ∈ S o, x v = true) :=
    fun o x => by rw [← PEqualNP.Outside.L_meta_986.eval_eq]; exact hout o x
  let A (o : Fin m) := PEqualNP.Outside.L_meta_986.assigned gates (S o) T t0
  have hA : ∀ o, (S o \ T.erase t0).card ≤ (A o).card + 1 := fun o =>
    PEqualNP.Outside.L_meta_986.card_assigned gates T i0 hw hG hnot hi0 hh hhw hT' (S o) t0
      (out o) (hout' o)
  have hd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint A := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun w hwi hwj => ?_
    obtain ⟨_, _, hi1, hi2⟩ := Finset.mem_filter.mp hwi
    obtain ⟨_, _, hj1, hj2⟩ := Finset.mem_filter.mp hwj
    have hsmall := hinter i j hij
    by_cases hc : t0 ∈ S i → t0 ∈ S j
    · have hsub := PEqualNP.Outside.L_meta_986.inter_sub (S i) (S j) T _ t0 hj1 hc
      have := Finset.card_le_card hsub
      omega
    · have hc' : t0 ∈ S j → t0 ∈ S i := fun _ => by tauto
      have hsub := PEqualNP.Outside.L_meta_986.inter_sub (S j) (S i) T _ t0 hi1 hc'
      have := Finset.card_le_card hsub
      rw [Finset.inter_comm (S j) (S i)] at this
      omega
  have hnotA : ∀ o, n + i0.val ∉ A o := by
    intro o hmem
    obtain ⟨_, h0, _⟩ := Finset.mem_filter.mp hmem
    rw [PEqualNP.Outside.L_meta_986.not_wire gates i0 hw hi0 hh hhw _
      (hT' _ (fun _ _ => rfl))] at h0
    exact Bool.noConfusion h0
  have hU : (Finset.univ.biUnion A).card ≤ gates.length - 1 := by
    have hsub : Finset.univ.biUnion A ⊆ (Finset.Ico n (n + gates.length)).erase (n + i0.val) := by
      intro w hw'
      obtain ⟨o, _, ho⟩ := Finset.mem_biUnion.mp hw'
      refine Finset.mem_erase.mpr ⟨fun he => hnotA o (he ▸ ho), ?_⟩
      exact (Finset.mem_filter.mp ho).1
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (by simp)] at this
    simpa using this
  have hsumA : ∑ o, (A o).card = (Finset.univ.biUnion A).card := (Finset.card_biUnion hd).symm
  have hper : ∀ o, (S o).card - 1 ≤ (A o).card + (S o ∩ T.erase t0).card := by
    intro o
    have h1 := Finset.card_sdiff_add_card_inter (S o) (T.erase t0)
    have h2 := hA o
    omega
  have hswap : ∑ o, (S o ∩ T.erase t0).card =
      ∑ u ∈ T.erase t0, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
    have e1 : ∀ o, (S o ∩ T.erase t0).card = ∑ u ∈ T.erase t0, if u ∈ S o then 1 else 0 := by
      intro o
      rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]
    have e2 : ∀ u, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card =
        ∑ c : Fin m, if u ∈ S c then 1 else 0 := fun u => Finset.card_filter _ _
    simp only [e1, e2]
    exact Finset.sum_comm
  have hsum : ∑ s : Fin m, ((S s).card - 1) ≤
      ∑ o, (A o).card + ∑ o, (S o ∩ T.erase t0).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun o _ => hper o
  have hL : 1 ≤ gates.length := by have := i0.isLt; omega
  omega
