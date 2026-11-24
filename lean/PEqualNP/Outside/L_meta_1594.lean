import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.GetD
import Mathlib.Order.Interval.Finset.Nat
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

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ r ∈ l, f r = true → f' r = true)
    (hf : op.eval (l.map f) = true) : op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hf ⊢
    intro r hr
    exact h r hr (hf r hr)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hf ⊢
    obtain ⟨r, hr, hfr⟩ := hf
    exact ⟨r, hr, h r hr hfr⟩

lemma step {n K t : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ j : Fin C.gates.length, (C.gates.get j).op = GateOp.not → (j : ℕ) = t)
    (hlight : ∀ z : Fin n → Bool, (Finset.univ.filter (fun v : Fin n => z v = true)).card < K →
      value C z (n + t) = true)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ x y : Fin n → Bool, (Finset.univ.filter (fun v : Fin n => y v = true)).card < K →
        (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  classical
  have hj : w - n < C.gates.length := by unfold Circuit.size at hw; omega
  let g := C.gates[w - n]
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  refine ⟨g.inputs.toFinset.filter (· < w), ?_, ?_, ?_⟩
  · exact (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen)
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hy hxy hx
    by_cases hnt : g.op = GateOp.not
    · have ht : w - n = t := hnot ⟨w - n, hj⟩ (by simpa using hnt)
      have hwt : w = n + t := by omega
      rw [hwt]
      exact hlight y hy
    · have hop' : g.op = GateOp.and ∨ g.op = GateOp.or := by
        rcases hop with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hnt
      have hx' : value C x w =
          g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) :=
        gate_value C x w hn hw
      have hy' : value C y w =
          g.op.eval (g.inputs.map fun r => if r < w then value C y r else false) :=
        gate_value C y w hn hw
      rw [hx'] at hx
      rw [hy']
      refine eval_mono g.op hop' g.inputs _ _ ?_ hx
      intro r hr hrx
      by_cases hrw : r < w
      · rw [ite_eq_left hrw] at hrx ⊢
        exact hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, hrw⟩) hrx
      · rw [ite_eq_right hrw] at hrx
        exact absurd hrx (by simp)

lemma mono {n K t : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ j : Fin C.gates.length, (C.gates.get j).op = GateOp.not → (j : ℕ) = t)
    (hlight : ∀ z : Fin n → Bool, (Finset.univ.filter (fun v : Fin n => z v = true)).card < K →
      value C z (n + t) = true)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true)
    (hy : (Finset.univ.filter (fun v : Fin n => y v = true)).card < K) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, hP, hstep⟩ := step C hG hnot hlight w (by omega) hw
      exact hstep x y hy fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

lemma cut {X : Type} (V : X → ℕ → Bool) (R : X → X → Prop) (G : Finset ℕ)
    (hstep : ∀ w ∈ G, ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ x y, R x y → (∀ r ∈ P, V x r = true → V y r = true) → V x w = true → V y w = true)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G → w < t) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ F.card + (G.filter (· < t)).card ∧
      ∀ x y, R x y → (∀ w ∈ B, V x w = true → V y w = true) →
        ∀ w ∈ F, V x w = true → V y w = true := by
  induction t generalizing F with
  | zero =>
    exact ⟨F, Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega),
      Nat.le_add_right .., fun _ _ _ h => h⟩
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ G
    · obtain ⟨P, hPcard, hP, hp⟩ := hstep t hex.2
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
      · intro x y hR hxy w hw
        by_cases h : w = t
        · subst w
          exact hp x y hR fun r hr => hi x y hR hxy r (Finset.mem_union_right _ hr)
        · exact hi x y hR hxy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩))
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

def support {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => value C (fun q => decide (q = p)) w = true)

lemma mem_support {n : ℕ} (C : Circuit) (w : ℕ) (p : Fin n) :
    p ∈ support C w ↔ value C (fun q => decide (q = p)) w = true := by
  simp [support]

lemma support_gate {n : ℕ} (C : Circuit) (w : ℕ) (h : 2 ≤ (support (n := n) C w).card) :
    n ≤ w ∧ w < n + C.size := by
  constructor
  · by_contra! hw
    let p : Fin n := ⟨w, hw⟩
    have hs : support C w ⊆ {p} := by
      intro q hq
      have hv := (mem_support C w q).mp hq
      change value C (fun r => decide (r = q)) p = true at hv
      simpa [input_value, eq_comm] using hv
    have hb := Finset.card_le_card hs
    simp at hb
    omega
  · by_contra! hw
    have hs : support (n := n) C w = ∅ := by
      ext q
      simp [mem_support, missing_value C _ w hw]
    simp [hs] at h

lemma main_count {N : ℕ} (D : Circuit) (A Y : Finset (Fin N)) (u t : ℕ)
    (hG : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ j : Fin D.gates.length, (D.gates.get j).op = GateOp.not → (j : ℕ) = t)
    (hu : ∀ z : Fin N → Bool, value D z u = decide (∃ s ∈ A, z s = true))
    (hlight : ∀ z : Fin N → Bool,
      (Finset.univ.filter (fun v : Fin N => z v = true)).card < Y.card →
      value D z (N + t) = true) :
    min Y.card A.card ≤ (Finset.univ.filter (fun h : Fin D.gates.length =>
      (∀ s : Fin N, value D (fun w => decide (w = s)) (N + h) = true → s ∈ A) ∧
        2 ≤ (support (n := N) D (N + h)).card)).card + 1 := by
  classical
  set good := Finset.univ.filter (fun h : Fin D.gates.length =>
      (∀ s : Fin N, value D (fun w => decide (w = s)) (N + h) = true → s ∈ A) ∧
        2 ≤ (support (n := N) D (N + h)).card) with hgood
  by_contra hcon
  rw [not_le] at hcon
  have hcK : good.card + 1 < Y.card ∧ good.card + 1 < A.card := lt_min_iff.mp hcon
  let G : Finset ℕ := good.image (fun h : Fin D.gates.length => N + (h : ℕ))
  have hGcard : G.card = good.card := by
    apply Finset.card_image_of_injective
    intro a b hab
    apply Fin.ext
    simp only at hab
    omega
  have hGgate : ∀ w ∈ G, N ≤ w ∧ w < N + D.size := by
    intro w hw
    obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hw
    have := h.isLt
    unfold Circuit.size
    omega
  obtain ⟨B, hd, hBcard, hcut⟩ := cut (fun (x : Fin N → Bool) w => value D x w)
    (fun _ y => (Finset.univ.filter (fun v : Fin N => y v = true)).card < Y.card) G
    (fun w hw => step D hG hnot hlight w (hGgate w hw).1 (hGgate w hw).2)
    (N + D.size) {u} (fun w _ hw => (hGgate w hw).2)
  have hb : B.card ≤ good.card + 1 := by
    have hfilter := Finset.card_filter_le G (fun w => w < N + D.size)
    simp only [Finset.card_singleton] at hBcard
    omega
  let clean (w : ℕ) : Finset (Fin N) := if support D w ⊆ A then support D w else ∅
  have hclean : ∀ w ∈ B, (clean w).card ≤ 1 := by
    intro w hw
    by_cases hs : support (n := N) D w ⊆ A
    · change (if support (n := N) D w ⊆ A then support (n := N) D w else ∅).card ≤ 1
      rw [ite_eq_left hs]
      by_contra! hlarge
      obtain ⟨hNw, hwN⟩ := support_gate D w (by omega)
      have hlt : w - N < D.gates.length := by unfold Circuit.size at hwN; omega
      have heq : N + (w - N) = w := by omega
      apply Finset.disjoint_left.mp hd hw
      refine Finset.mem_image.mpr ⟨⟨w - N, hlt⟩, ?_, heq⟩
      rw [hgood, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro s hsv
        simp only at hsv
        rw [heq] at hsv
        exact hs ((mem_support D w s).mpr hsv)
      · simp only
        rw [heq]
        omega
    · simp [clean, hs]
  have hcover : (B.biUnion clean).card < A.card := by
    have h := Finset.card_biUnion_le_card_mul B clean 1 hclean
    simp only [mul_one] at h
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  let Dset := B.filter (fun w => ¬ support (n := N) D w ⊆ A)
  have hout (w : {w // w ∈ Dset}) : ∃ q : Fin N, q ∈ support D w.val ∧ q ∉ A := by
    by_contra! h
    exact (Finset.mem_filter.mp w.property).2 h
  choose q hq using hout
  let U := Dset.attach.image q
  let y : Fin N → Bool := fun r => decide (r ∈ U)
  have hU : U.card ≤ good.card + 1 := calc
    U.card ≤ Dset.attach.card := Finset.card_image_le
    _ = Dset.card := Finset.card_attach
    _ ≤ B.card := Finset.card_filter_le _ _
    _ ≤ good.card + 1 := hb
  have hset : Finset.univ.filter (fun r => y r = true) = U := by ext r; simp [y]
  have hylight : (Finset.univ.filter (fun v : Fin N => y v = true)).card < Y.card := by
    rw [hset]
    omega
  have hyfalse : value D y u = false := by
    rw [hu]
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro s hs hys
    have hsU : s ∈ U := by simpa [y] using hys
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hsU
    exact (hq d).2 hs
  have hytrue : value D y u = true := by
    refine hcut (fun r => decide (r = p)) y hylight ?_ u (Finset.mem_singleton_self u) ?_
    · intro w hw hx
      by_cases hs : support (n := N) D w ⊆ A
      · exact False.elim (hpnot (Finset.mem_biUnion.mpr
          ⟨w, hw, by simpa only [clean, ite_eq_left hs, mem_support] using hx⟩))
      · let d : {w // w ∈ Dset} := ⟨w, Finset.mem_filter.mpr ⟨hw, hs⟩⟩
        apply mono D hG hnot hlight (fun r => decide (r = q d)) y _ hylight w
          ((mem_support D w (q d)).mp (hq d).1)
        intro r hr
        have he : r = q d := of_decide_eq_true hr
        subst r
        have hm : q d ∈ U := Finset.mem_image_of_mem q (Finset.mem_attach Dset d)
        simp [y, hm]
    · rw [hu]
      simp only [decide_eq_true_eq]
      exact ⟨p, hp, by simp⟩
  simp [hyfalse] at hytrue

end PEqualNP.Outside.L_meta_1594

theorem PEqualNP.Outside.L_meta_1594 : (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))) → (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size) → ∀ (N M : ℕ) (A : Fin M → Finset (Fin N)) (D : PEqualNP.CircuitLowerBounds.Circuit) (u : Fin M → ℕ) (t : ℕ) (Y : Finset (Fin N)), (∀ ab1 ab2 : Fin M, ab1 ≠ ab2 → (A ab1 ∩ A ab2).card ≤ 1) → (∀ eb1 ∈ D.gates, (eb1.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ eb1.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ eb1.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ eb1.inputs.length ≤ 2) → (∀ lb1 : Fin D.gates.length, (D.gates.get lb1).op = PEqualNP.CircuitLowerBounds.GateOp.not → (lb1 : ℕ) = t) → (∀ (ab3 : Fin M) (zb1 : Fin N → Bool), (D.wires (List.ofFn zb1)).getD (u ab3) false = decide (∃ sb1 ∈ A ab3, zb1 sb1 = true)) → (∀ zb2 : Fin N → Bool, (Finset.univ.filter (fun vb1 : Fin N => zb2 vb1 = true)).card < Y.card → (D.wires (List.ofFn zb2)).getD (N + t) false = true) → (D.wires (List.ofFn (fun vb2 : Fin N => decide (vb2 ∈ Y)))).getD (N + t) false = false → 2 ≤ Y.card → ∀ b4 : Fin M, min Y.card (A b4).card ≤ (Finset.univ.filter (fun h1 : Fin D.gates.length => (∀ s2 : Fin N, (D.wires (List.ofFn (fun w1 : Fin N => decide (w1 = s2)))).getD (N + h1) false = true → s2 ∈ A b4) ∧ 2 ≤ (Finset.univ.filter (fun s3 : Fin N => (D.wires (List.ofFn (fun w2 : Fin N => decide (w2 = s3)))).getD (N + h1) false = true)).card)).card + 1 := by
  intro _ _ N M A D u t Y _ hD hnot hu hlight _ _ b4
  exact PEqualNP.Outside.L_meta_1594.main_count D (A b4) Y (u b4) t hD hnot (fun z => hu b4 z)
    hlight
