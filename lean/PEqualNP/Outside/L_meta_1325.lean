import Mathlib
import PEqualNP.Defs

-- The gate semantics and monotone counting lemmas below are adapted from the
-- project's checked steps L-meta-270, L-meta-669, L-meta-885, L-meta-924
-- and L-meta-1049. The recursive window argument and the fixed-base count
-- for the second bound follow those prerequisites.

-- Original proof by k-sandhu in PR 149.
-- Adapted here to the current proof-file namespace rules.

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1325_aux.Light

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

private lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

private lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

private lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

private def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

private lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

-- At a gate, reads of earlier wires agree with the completed run.
-- All other reads contribute false, even if the wire is produced later.
private lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
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

private lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, g.inputs = [a, b] := by
    cases h : g.inputs with
    | nil => simp [h] at hlen
    | cons a rest =>
      cases rest with
      | nil => simp [h] at hlen
      | cons b tail =>
        have : tail = [] := by simpa [h] using hlen
        exact ⟨a, b, by simp [this]⟩
  let P := ({a, b} : Finset ℕ).filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ?_, ?_, ?_⟩
  · by_cases h : a = b <;> simp [h, Finset.card_insert_of_notMem]
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have hr (r : ℕ) (hr : r ∈ ({a, b} : Finset ℕ)) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨hr, h⟩)
      · simp [h]
    have ha := hr a (by simp)
    have hb := hr b (by simp)
    have formula (z : Fin n → Bool) :
        value C z w = g.op.eval
          [if a < w then value C z a else false, if b < w then value C z b else false] := by
      simpa [g, hab] using gate_value C z w hn hw
    rw [formula x] at hx
    rw [formula y]
    rcases hop with hop | hop
    · simp only [hop, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true,
        Bool.and_eq_true] at hx ⊢
      exact ⟨ha hx.1, hb hx.2⟩
    · simp only [hop, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false,
        Bool.or_eq_true] at hx ⊢
      exact hx.imp ha hb

private lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C hG w (by omega) hw
      exact hstep x y fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

-- Expand the selected gates once each, in reverse evaluation order.
-- Replacing one wire by at most two earlier wires increases the cut by at most one.
private lemma cut {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (G : Finset ℕ) (hGates : ∀ w ∈ G, n ≤ w ∧ w < n + C.size)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G → w < t) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ F.card + (G.filter (· < t)).card ∧
      ∀ x y : Fin n → Bool, (∀ w ∈ B, value C x w = true → value C y w = true) →
        ∀ w ∈ F, value C x w = true → value C y w = true := by
  induction t generalizing F with
  | zero =>
    exact ⟨F, Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega),
      Nat.le_add_right .., fun _ _ h => h⟩
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ G
    · obtain ⟨P, hPcard, hP, hp⟩ := gate_inputs C hG t (hGates t hex.2).1 (hGates t hex.2).2
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
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hd, by omega, hi⟩

private def support {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => value C (fun q => decide (q = p)) w = true)

private lemma mem_support {n : ℕ} (C : Circuit) (w : ℕ) (p : Fin n) :
    p ∈ support C w ↔ value C (fun q => decide (q = p)) w = true := by
  simp [support]

private lemma support_gate {n : ℕ} (C : Circuit) (w : ℕ) (h : 2 ≤ (support (n := n) C w).card) :
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

private def assigned {n : ℕ} (C : Circuit) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter fun w => support C w ⊆ T ∧ 2 ≤ (support (n := n) C w).card

-- A small cut leaves some point of T uncovered by its clean wires.
-- Each other wire can be made true by a single point outside T.
private lemma card_assigned {n k c : ℕ} (C : Circuit) (T : Finset (Fin n)) (o : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (ho : ∀ p : Fin n, value C (fun q => decide (q = p)) o = true ↔ p ∈ T)
    (hsparse : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q => x q = true)).card ≤ k →
      (∀ q ∈ T, x q = false) → value C x o = false)
    (hk : c ≤ k) (hc : c + 1 ≤ T.card) : c ≤ (assigned C T).card := by
  classical
  let G := assigned C T
  by_contra! hsmall
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := by
    intro w hw
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B, hd, hBcard, hcut⟩ := cut C hG G hgate (n + C.size) {o}
    (fun w _ hw => (hgate w hw).2)
  have hb : B.card ≤ c := by
    have hfilter := Finset.card_filter_le G (fun w => w < n + C.size)
    simp only [Finset.card_singleton] at hBcard
    change G.card < c at hsmall
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
  have hu : U.card ≤ k := calc
    U.card ≤ D.attach.card := Finset.card_image_le
    _ = D.card := Finset.card_attach
    _ ≤ B.card := Finset.card_filter_le _ _
    _ ≤ k := hb.trans hk
  have hyfalse : value C y o = false := by
    apply hsparse y
    · have hset : Finset.univ.filter (fun r => y r = true) = U := by ext r; simp [y]
      rwa [hset]
    · intro r hr
      have hnot : r ∉ U := by
        intro hmem
        obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hmem
        exact (hq w).2 hr
      simp [y, hnot]
  have hytrue : value C y o = true := by
    apply hcut (fun r => decide (r = p)) y _ o (Finset.mem_singleton_self o) ((ho p).mpr hp)
    intro w hw hx
    by_cases hs : support C w ⊆ T
    · exact False.elim (hpnot (Finset.mem_biUnion.mpr
        ⟨w, hw, by simpa only [clean, ite_eq_left hs, mem_support] using hx⟩))
    · let d : {w // w ∈ D} := ⟨w, Finset.mem_filter.mpr ⟨hw, hs⟩⟩
      apply value_mono C hG (fun r => decide (r = q d)) y _ w ((mem_support C w (q d)).mp (hq d).1)
      intro r hr
      have he : r = q d := of_decide_eq_true hr
      subst r
      have hm : q d ∈ U := Finset.mem_image_of_mem q (Finset.mem_attach D d)
      simp [y, hm]
  simp [hyfalse] at hytrue

end PEqualNP.Outside.L_meta_1325_aux.Light

open PEqualNP.Outside.L_meta_1325_aux.Light in
theorem PEqualNP.Outside.L_meta_1325_aux.Light :
    ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (o : Fin m → ℕ) (c : Fin m → ℕ),
      (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
      (∀ i : Fin m, 2 ≤ (S i).card) →
      (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) →
      (∀ (i : Fin m) (p : Fin n),
        (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) →
      (∀ (i : Fin m) (x : Fin n → Bool),
        (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k →
        (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) →
      (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) →
      ∑ i : Fin m, c i ≤ C.size := by
  classical
  intro n m k S C o c hinter _ hG ho hsparse hk hc
  let G (i : Fin m) := assigned C (S i)
  have hd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun w hwi hwj => ?_
    have hi := (Finset.mem_filter.mp hwi).2
    have hj := (Finset.mem_filter.mp hwj).2
    have hsub : support C w ⊆ S i ∩ S j := fun p hp => Finset.mem_inter.mpr ⟨hi.1 hp, hj.1 hp⟩
    have hle := Finset.card_le_card hsub
    have hsmall := hinter i j hij
    omega
  calc
    ∑ i : Fin m, c i ≤ ∑ i : Fin m, (G i).card := Finset.sum_le_sum fun i _ =>
      card_assigned C (S i) (o i) hG (ho i) (hsparse i) (hk i) (hc i)
    _ = (Finset.univ.biUnion G).card := (Finset.card_biUnion hd).symm
    _ ≤ (Finset.Ico n (n + C.size)).card := Finset.card_le_card fun w hw => by
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
      exact (Finset.mem_filter.mp hi).1
    _ = C.size := by simp

namespace PEqualNP.Outside.L_meta_1325_aux.Restrict

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

def Rep {n : ℕ} (new : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ c : Bool, ∀ x : Fin n → Bool, f x = c) ∨
    (∃ j : ℕ, j < n + new.length ∧ ∀ x : Fin n → Bool, (W new x).getD j false = f x)

def Fan (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Ext (new new' : List Gate) : Prop :=
  new' = new ∨ ∃ h : Gate, new' = new ++ [h] ∧ Fan h

lemma rep_congr {n : ℕ} {new : List Gate} {f g : (Fin n → Bool) → Bool}
    (h : ∀ x, f x = g x) (hf : Rep new f) : Rep new g := by
  obtain rfl : f = g := funext h
  exact hf

lemma rep_mono {n : ℕ} {new new' : List Gate} (he : Ext new new')
    (f : (Fin n → Bool) → Bool) (h : Rep new f) : Rep new' f := by
  rcases he with rfl | ⟨k, rfl, _⟩
  · exact h
  · rcases h with hc | ⟨j, hj, hv⟩
    · exact Or.inl hc
    · have hne : ¬ j = n + new.length := by omega
      refine Or.inr ⟨j, by rw [List.length_append, List.length_singleton]; omega, fun x => ?_⟩
      rw [W_val, if_neg hne]
      exact hv x

lemma rep_and {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext new new' ∧ Rep new' (fun x => f x && g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | false =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
        show (f x && g x) = false
        simp [h1 x]⟩⟩
    | true =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x && g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | false =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
          show (f x && g x) = false
          simp [h2 x]⟩⟩
      | true =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x && g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.and, [j, k]⟩], Or.inr ⟨_, rfl, Or.inl rfl, rfl⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.and, [j, k]⟩]) x).getD (n + new.length) false = (f x && g x)
      rw [W_val, if_pos rfl]
      show GateOp.and.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_or {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext new new' ∧ Rep new' (fun x => f x || g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | true =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
        show (f x || g x) = true
        simp [h1 x]⟩⟩
    | false =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x || g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | true =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
          show (f x || g x) = true
          simp [h2 x]⟩⟩
      | false =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x || g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.or, [j, k]⟩], Or.inr ⟨_, rfl, Or.inr rfl, rfl⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.or, [j, k]⟩]) x).getD (n + new.length) false = (f x || g x)
      rw [W_val, if_pos rfl]
      show GateOp.or.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_input {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (t : ℕ) :
    Rep ([] : List Gate) (fun x => (W [] (ρ x)).getD t false) := by
  by_cases ht : t < n
  · have hval : ∀ y : Fin n → Bool, (W [] y).getD t false = y ⟨t, ht⟩ := by
      intro y
      show (List.ofFn y).getD t false = _
      rw [List.getD_eq_getElem _ _ (by simpa using ht)]
      simp
    rcases hρ ⟨t, ht⟩ with ⟨c, hc⟩ | hid
    · exact Or.inl ⟨c, fun x => by
        show (W [] (ρ x)).getD t false = c
        rw [hval, hc x]⟩
    · exact Or.inr ⟨t, by simpa using ht, fun x => by
        show (W [] x).getD t false = (W [] (ρ x)).getD t false
        rw [hval, hval, hid x]⟩
  · exact Or.inl ⟨false, fun x =>
      List.getD_eq_default _ _ (by rw [W_len, List.length_nil]; omega)⟩

lemma gate_rep {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old new : List Gate)
    (op : GateOp) (l : List ℕ) (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : l.length ≤ 2)
    (h : ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)) :
    ∃ new', Ext new new' ∧
      Rep new' (fun x => op.eval (l.map fun i => (W old (ρ x)).getD i false)) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c3, rest⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by simp [GateOp.eval]⟩⟩
    · exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by simp [GateOp.eval]⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
  · rcases hop with rfl | rfl
    · obtain ⟨new', he, hr⟩ := rep_and new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
    · obtain ⟨new', he, hr⟩ := rep_or new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
  · simp only [List.length_cons] at hlen
    omega

def Inv {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) : Prop :=
  ∃ new : List Gate, (∀ g ∈ new, Fan g) ∧ new.length ≤ old.length ∧
    ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)

lemma inv_step {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (h : Inv ρ old) : Inv ρ (old ++ [g]) := by
  obtain ⟨new, hfan, hl, hrep⟩ := h
  obtain ⟨new', he, hr⟩ := gate_rep ρ old new g.op g.inputs hop hlen hrep
  refine ⟨new', ?_, ?_, ?_⟩
  · rcases he with rfl | ⟨k, rfl, hk⟩
    · exact hfan
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hfan q hq
      · rw [List.mem_singleton] at hq
        rw [hq]
        exact hk
  · rcases he with rfl | ⟨k, rfl, hk⟩
    · rw [List.length_append, List.length_singleton]
      omega
    · rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton]
      omega
  · intro t
    by_cases ht : t = n + old.length
    · exact rep_congr (fun x => by
        show _ = (W (old ++ [g]) (ρ x)).getD t false
        rw [W_val, if_pos ht]) hr
    · exact rep_congr (fun x => by
        show _ = (W (old ++ [g]) (ρ x)).getD t false
        rw [W_val, if_neg ht]) (rep_mono he _ (hrep t))

lemma inv_all {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    Inv ρ gates := by
  have hall : ∀ (post pre : List Gate), pre ++ post = gates → Inv ρ pre → Inv ρ gates := by
    intro post
    induction post with
    | nil =>
      intro pre h hinv
      rw [List.append_nil] at h
      rw [← h]
      exact hinv
    | cons g post ih =>
      intro pre h hinv
      have hmem : g ∈ gates := by
        rw [← h]
        simp
      exact ih (pre ++ [g]) (by rw [List.append_assoc]; exact h)
        (inv_step ρ pre g (hg g hmem).1 (hg g hmem).2 hinv)
  exact hall gates [] (List.nil_append _)
    ⟨[], by simp, le_refl _, rep_input ρ hρ⟩

lemma inv_final {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (gates : List Gate)
    (h : Inv ρ gates) :
    ∃ (gates' : List Gate) (r : ℕ → ℕ), (∀ g ∈ gates', Fan g) ∧ gates'.length ≤ gates.length ∧
      ∀ o : ℕ, (∃ x y : Fin n → Bool,
        (W gates (ρ x)).getD o false ≠ (W gates (ρ y)).getD o false) →
        ∀ x : Fin n → Bool, (W gates' x).getD (r o) false = (W gates (ρ x)).getD o false := by
  obtain ⟨new, hfan, hl, hrep⟩ := h
  have hsel : ∀ o : ℕ, ∃ j : ℕ,
      (∃ c : Bool, ∀ x : Fin n → Bool, (W gates (ρ x)).getD o false = c) ∨
      (∀ x : Fin n → Bool, (W new x).getD j false = (W gates (ρ x)).getD o false) := by
    intro o
    rcases hrep o with hc | ⟨j, _, hj⟩
    · exact ⟨0, Or.inl hc⟩
    · exact ⟨j, Or.inr hj⟩
  choose r hr using hsel
  refine ⟨new, r, hfan, hl, ?_⟩
  intro o hne x
  rcases hr o with ⟨c, hc⟩ | hj
  · obtain ⟨x1, y1, hxy⟩ := hne
    exact absurd ((hc x1).trans (hc y1).symm) hxy
  · exact hj x

theorem main_aux : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) := by
  intro n gates T Z hg
  have hρ : ∀ i : Fin n,
      (∃ c : Bool, ∀ x : Fin n → Bool,
        (if i ∈ T then true else if i ∈ Z then false else x i) = c) ∨
      (∀ x : Fin n → Bool, (if i ∈ T then true else if i ∈ Z then false else x i) = x i) := by
    intro i
    by_cases h1 : i ∈ T
    · exact Or.inl ⟨true, fun x => by rw [if_pos h1]⟩
    · by_cases h2 : i ∈ Z
      · exact Or.inl ⟨false, fun x => by rw [if_neg h1, if_pos h2]⟩
      · exact Or.inr (fun x => by rw [if_neg h1, if_neg h2])
  exact inv_final (fun (x : Fin n → Bool) (i : Fin n) =>
    if i ∈ T then true else if i ∈ Z then false else x i) gates
    (inv_all _ hρ gates hg)

end PEqualNP.Outside.L_meta_1325_aux.Restrict

theorem PEqualNP.Outside.L_meta_1325_aux.Restrict : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) :=
  PEqualNP.Outside.L_meta_1325_aux.Restrict.main_aux

namespace PEqualNP.Outside.L_meta_1325_aux.Windows

open PEqualNP.CircuitLowerBounds

abbrev CountHyp := (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size)

abbrev ReduceHyp := (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)))

theorem linesHit {n m q : ℕ} (F : Fin m → Finset (Fin n))
    (reg : ∀ p : Fin n,(Finset.univ.filter (fun i : Fin m => p ∈ F i)).card = q+1)
    (pair : ∀ u v : Fin n, u ≠ v → ∃ i : Fin m, u ∈ F i ∧ v ∈ F i)
    (Y : Finset (Fin n)) :
    (Finset.univ.filter (fun i : Fin m => ¬ Disjoint Y (F i))).card ≤ q*Y.card+1 := by
  classical
  let lines (p : Fin n) := Finset.univ.filter (fun i : Fin m => p ∈ F i)
  have aux (A : Finset (Fin n)) : (A.biUnion lines).card ≤ q*A.card+1 := by
    induction A using Finset.induction_on with
    | empty => simp
    | @insert p A hp ih =>
      rw [Finset.biUnion_insert,Finset.card_insert_of_notMem hp,Nat.mul_add,Nat.mul_one]
      cases A.eq_empty_or_nonempty with
      | inl h => subst A; simpa [lines] using (reg p).le
      | inr h =>
        obtain ⟨r,hr⟩ := h
        have hpr : p ≠ r := fun eq => hp (eq ▸ hr)
        obtain ⟨i,hpi,hri⟩ := pair p r hpr
        have hi : i ∈ lines p ∩ A.biUnion lines := Finset.mem_inter.mpr
          ⟨by simpa [lines] using hpi,Finset.mem_biUnion.mpr ⟨r,hr,by simpa [lines] using hri⟩⟩
        have hpos : 0 < (lines p ∩ A.biUnion lines).card := Finset.card_pos.mpr ⟨i,hi⟩
        have hu := Finset.card_union_add_card_inter (lines p) (A.biUnion lines)
        have hcnt : (lines p).card = q+1 := reg p
        omega
  apply le_trans _ (aux Y)
  apply Finset.card_le_card
  intro i hi
  have h := (Finset.mem_filter.mp hi).2
  rw [Finset.not_disjoint_iff] at h
  obtain ⟨p,hp,hpi⟩ := h
  exact Finset.mem_biUnion.mpr ⟨p,hp,by simpa [lines] using hpi⟩

def bit {n : ℕ} (X : Finset (Fin n)) (i : Fin n) := decide (i ∈ X)
def supp {n : ℕ} (x : Fin n → Bool) := Finset.univ.filter (fun p => x p = true)
def untouched {n m : ℕ} (F : Fin m → Finset (Fin n)) (Y : Finset (Fin n)) :=
  Finset.univ.filter (fun i => Disjoint Y (F i))

theorem local_count (hc : CountHyp) (hr : ReduceHyp) {n m q k : ℕ}
    (hk : 1 ≤ k) (hq : 1 ≤ q) (F : Fin m → Finset (Fin n)) (Y : Finset (Fin n))
    (hs : ∀ i, (F i).card=q+1) (hd : ∀ i j, i≠j → (F i ∩ F j).card ≤ 1)
    (L : List Gate) (out : Fin m → ℕ)
    (ha : ∀ g ∈ L, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length ≤ 2)
    (win : ∀ i (X : Finset (Fin n)), X.card ≤ k → Circuit.eval ⟨L,out i⟩ (List.ofFn (bit (Y∪X))) =
      decide (∃ p ∈ F i, p ∈ Y∪X)) :
    (untouched F Y).card * min k q ≤ L.length := by
  classical
  let I := untouched F Y
  let e : Fin I.card ≃ I := (Fintype.equivFinOfCardEq (Fintype.card_coe I)).symm
  obtain ⟨D,r,hD,hsize,respond⟩ := hr n L Y ∅ ha
  let newF (i : Fin I.card) := F (e i).val
  let newO (i : Fin I.card) := r (out (e i).val)
  have hdis (i : Fin I.card) : Disjoint Y (newF i) := (Finset.mem_filter.mp (e i).property).2
  have align (x : Fin n → Bool) :
      (fun i => if i ∈ Y then true else if i ∈ (∅ : Finset (Fin n)) then false else x i) =
      bit (Y ∪ supp x) := by
    funext p
    by_cases h : p ∈ Y <;> cases hx : x p <;> simp [bit,supp,h,hx]
  have answer (i : Fin I.card) (x : Fin n → Bool) (hx : (supp x).card ≤ k) :
      Circuit.eval ⟨L,out (e i).val⟩ (List.ofFn (bit (Y∪supp x))) =
      decide (∃ p ∈ newF i, x p = true) := by
    rw [win _ _ hx]
    congr 1
    apply propext
    constructor
    · rintro ⟨p,hp,hu⟩
      rcases Finset.mem_union.mp hu with hy | hb
      · exact (Finset.disjoint_left.mp (hdis i) hy hp).elim
      · exact ⟨p,hp,(Finset.mem_filter.mp hb).2⟩
    · rintro ⟨p,hp,hb⟩
      exact ⟨p,hp,Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩)⟩
  have emptyS : supp (fun _ : Fin n => false) = ∅ := by ext; simp [supp]
  have singS (p : Fin n) : supp (fun a => decide (a=p)) = {p} := by ext; simp [supp]
  have live (i : Fin I.card) : ∃ x y : Fin n → Bool,
      Circuit.eval ⟨L,out (e i).val⟩ (List.ofFn (fun p => if p ∈ Y then true else if p ∈ (∅ : Finset (Fin n)) then false else x p)) ≠
      Circuit.eval ⟨L,out (e i).val⟩ (List.ofFn (fun p => if p ∈ Y then true else if p ∈ (∅ : Finset (Fin n)) then false else y p)) := by
    have hcard : (newF i).card = q+1 := hs _
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < (newF i).card by omega)
    refine ⟨fun _ => false,fun a => decide (a=p),?_⟩
    rw [align,align,answer i _ (by simp [emptyS]),answer i _ (by simpa [singS] using hk)]
    simp [hp]
  have result (i : Fin I.card) (x : Fin n → Bool) (hx : (supp x).card ≤ k) :
      Circuit.eval ⟨D,newO i⟩ (List.ofFn x) = decide (∃ p ∈ newF i, x p = true) := by
    rw [show Circuit.eval ⟨D,newO i⟩ (List.ofFn x) = _ from respond _ (live i) x,align,answer i x hx]
  have bound := hc n I.card k newF ⟨D,0⟩ newO (fun _ => min k q)
    (fun i j hij => hd _ _ (fun eq => hij (e.injective (Subtype.ext eq))))
    (fun i => by change 2 ≤ (F _).card; rw [hs]; omega) hD
    (fun i p => by
      change Circuit.eval ⟨D,newO i⟩ _ = true ↔ _
      rw [result i _ (by simpa [singS] using hk)]
      simp)
    (fun i x hx hnone => by
      change Circuit.eval ⟨D,newO i⟩ _ = false
      rw [result i x hx]
      simpa using hnone)
    (fun _ => min_le_left _ _) (fun i => by
      change min k q+1 ≤ (F _).card
      rw [hs]
      omega)
  simpa [I,Circuit.size] using le_trans bound hsize


end PEqualNP.Outside.L_meta_1325_aux.Windows

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1325_aux.Heavy

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

lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen), ?_, ?_⟩
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have hr (r : ℕ) (hm : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hm, h⟩)
      · simp [h]
    rw [gate_value C x w hn hw] at hx
    rw [gate_value C y w hn hw]
    change g.op.eval _ = true at hx ⊢
    rcases hop with hop | hop
    · simp only [hop, GateOp.eval, List.all_eq_true, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r, hm, rfl⟩ := List.mem_map.mp hb
      exact hr r hm (hx _ (List.mem_map.mpr ⟨r, hm, rfl⟩))
    · simp only [hop, GateOp.eval, List.any_eq_true, id_eq] at hx ⊢
      obtain ⟨b, hb, rfl⟩ := hx
      obtain ⟨r, hm, hv⟩ := List.mem_map.mp hb
      exact ⟨_, List.mem_map.mpr ⟨r, hm, rfl⟩, hr r hm hv⟩

lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C hG w (by omega) hw
      exact hstep x y fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

lemma cut {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (G : Finset ℕ) (hGates : ∀ w ∈ G, n ≤ w ∧ w < n + C.size)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G → w < t) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ F.card + (G.filter (· < t)).card ∧
      ∀ x y : Fin n → Bool, (∀ w ∈ B, value C x w = true → value C y w = true) →
        ∀ w ∈ F, value C x w = true → value C y w = true := by
  induction t generalizing F with
  | zero =>
    exact ⟨F, Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega),
      Nat.le_add_right .., fun _ _ h => h⟩
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ G
    · obtain ⟨P, hPcard, hP, hp⟩ := gate_inputs C hG t (hGates t hex.2).1 (hGates t hex.2).2
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
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hd, by omega, hi⟩


def offSet {n : ℕ} (T : Finset (Fin n)) (p : Fin n) : Bool := decide (p ∉ T)

lemma weight {n : ℕ} (T : Finset (Fin n)) :
    (Finset.univ.filter (fun p => offSet T p = true)).card = n - T.card := by
  have h : Finset.univ.filter (fun p => offSet T p = true) = Tᶜ := by
    ext p
    simp [offSet]
  rw [h, Finset.card_compl, Fintype.card_fin]

lemma union_bound {q n m : ℕ} (S : Fin m → Finset (Fin n))
    (hsize : ∀ i, (S i).card = q + 1)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (B : Finset ℕ) (A : ℕ → Finset (Fin n))
    (hA : ∀ w ∈ B, (A w).card ≤ q ∨ ∃ i, A w = S i) :
    (B.biUnion A).card ≤ B.card * q + 1 := by
  classical
  by_cases hbig : ∃ w ∈ B, ∃ i, A w = S i
  · obtain ⟨w,hw,i,hi⟩ := hbig
    let R := B.erase w
    have hdiff : ∀ v ∈ R, (A v \ S i).card ≤ q := by
      intro v hv
      rcases hA v (Finset.mem_erase.mp hv).2 with hs | ⟨j,hj⟩
      · exact (Finset.card_le_card Finset.sdiff_subset).trans hs
      · rw [hj]
        by_cases h : j = i
        · simp [h]
        · have he := Finset.card_sdiff_add_card_inter (S j) (S i)
          rw [hinter j i h, hsize] at he
          omega
    have hsub : B.biUnion A ⊆ S i ∪ R.biUnion (fun v => A v \ S i) := by
      intro p hp
      obtain ⟨v,hv,hp⟩ := Finset.mem_biUnion.mp hp
      by_cases h : p ∈ S i
      · exact Finset.mem_union_left _ h
      · have hne : v ≠ w := by rintro rfl; exact h (hi ▸ hp)
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨v,Finset.mem_erase.mpr ⟨hne,hv⟩,Finset.mem_sdiff.mpr ⟨hp,h⟩⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (S i) (R.biUnion (fun v => A v \ S i))
    have h3 := Finset.card_biUnion_le_card_mul R (fun v => A v \ S i) q hdiff
    have he : R.card + 1 = B.card := Finset.card_erase_add_one hw
    rw [← he, Nat.add_mul, Nat.one_mul]
    rw [hsize] at h2
    omega
  · have hsmall (v) (hv : v ∈ B) : (A v).card ≤ q :=
      (hA v hv).resolve_right (fun h => hbig ⟨v,hv,h⟩)
    exact (Finset.card_biUnion_le_card_mul B A q hsmall).trans (by omega)

end PEqualNP.Outside.L_meta_1325_aux.Heavy

namespace PEqualNP.Outside.L_meta_1325_aux.Trace

open PEqualNP.CircuitLowerBounds

def Allowed (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def Positive (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

def gateValue (values : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun w => values.getD w false)

def appendGate (values : List Bool) (g : Gate) : List Bool :=
  values ++ [gateValue values g]

def run (gates : List Gate) (values : List Bool) : List Bool :=
  gates.foldl appendGate values

def Below (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ w, x.getD w false = true → y.getD w false = true

theorem gateValue_pos (g : Gate) (hop : g.op = .and ∨ g.op = .or)
    (a b : List Bool) (h : Below a b) :
    gateValue a g = true → gateValue b g = true := by
  unfold gateValue
  rcases hop with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_map, Function.comp_def, id_eq, List.all_eq_true]
    intro ha w hw
    exact h.2 w (ha w hw)
  · rw [hg]
    simp only [GateOp.eval, List.any_map, Function.comp_def, id_eq, List.any_eq_true]
    rintro ⟨w, hw, ha⟩
    exact ⟨w, hw, h.2 w ha⟩

theorem gateValue_neg (g : Gate) (hop : g.op = .not) (a b : List Bool) (h : Below a b) :
    gateValue b g = true → gateValue a g = true := by
  unfold gateValue
  rw [hop]
  cases hi : g.inputs with
  | nil => simp [GateOp.eval]
  | cons w ws =>
    simp only [GateOp.eval, List.map_cons, List.headD_cons, Bool.not_eq_true']
    intro hf
    cases ha : a.getD w false
    · rfl
    · exact (Bool.false_ne_true (hf.symm.trans (h.2 w ha))).elim

theorem appendGate_below {a b : List Bool} (h : Below a b) (g : Gate)
    (hg : gateValue a g = true → gateValue b g = true) :
    Below (appendGate a g) (appendGate b g) := by
  refine ⟨by simp [appendGate, h.1], ?_⟩
  intro w
  unfold appendGate
  by_cases hw : w < a.length
  · have hwb : w < b.length := h.1 ▸ hw
    rw [List.getD_append _ _ _ _ hw, List.getD_append _ _ _ _ hwb]
    exact h.2 w
  · have ha := Nat.le_of_not_gt hw
    have hb : b.length ≤ w := h.1 ▸ ha
    rw [List.getD_append_right _ _ _ _ ha, List.getD_append_right _ _ _ _ hb, h.1]
    cases he : w - b.length with
    | zero => simpa using hg
    | succ k => simp

theorem initial_below {n : ℕ} (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) :
    Below (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro w
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split
  · rename_i hw
    simpa using h ⟨w, hw⟩
  · simp

theorem run_cons (g : Gate) (gs : List Gate) (a : List Bool) :
    run (g :: gs) a = run gs (appendGate a g) := rfl

theorem run_keeps (gs : List Gate) (a : List Bool) {w : ℕ} (h : w < a.length) :
    (run gs a).getD w false = a.getD w false := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp [appendGate]; omega), appendGate, List.getD_append _ _ _ _ h]

theorem value_first (g : Gate) (gs : List Gate) (a : List Bool) :
    (run (g :: gs) a).getD a.length false = gateValue a g := by
  rw [run_cons, run_keeps _ _ (by simp [appendGate]), appendGate]
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl a.length)]
  simp

theorem next_index (g : Gate) (gs : List Gate) (a : List Bool) (j : ℕ) :
    (run gs (appendGate a g)).getD ((appendGate a g).length + j) false =
      (run (g :: gs) a).getD (a.length + (j + 1)) false := by
  congr 1
  simp [appendGate]
  omega

def AgreesNot (gs : List Gate) (a b : List Bool) : Prop :=
  ∀ (j : ℕ) (g : Gate), gs[j]? = some g → g.op = .not →
    (run gs a).getD (a.length + j) false = (run gs b).getD (b.length + j) false

theorem AgreesNot.tail {g : Gate} {gs : List Gate} {a b : List Bool}
    (h : AgreesNot (g :: gs) a b) :
    AgreesNot gs (appendGate a g) (appendGate b g) := by
  intro j q hj hq
  rw [next_index, next_index]
  exact h (j+1) q (by simpa using hj) hq

theorem AgreesNot.first {g : Gate} {gs : List Gate} {a b : List Bool}
    (h : AgreesNot (g :: gs) a b) (hg : g.op = .not) :
    gateValue a g = gateValue b g := by
  have h0 := h 0 g rfl hg
  simpa only [Nat.add_zero, value_first] using h0

theorem run_below (gs : List Gate) (a b : List Bool) (h : Below a b)
    (hops : ∀ g ∈ gs, Allowed g) (hnot : AgreesNot gs a b) :
    Below (run gs a) (run gs b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    rw [run_cons, run_cons]
    apply ih _ _ (appendGate_below h g ?_)
      (fun q hq => hops q (List.mem_cons_of_mem _ hq)) hnot.tail
    rcases (hops _ (List.mem_cons_self ..)).1 with ha | ho | hn
    · exact gateValue_pos g (Or.inl ha) a b h
    · exact gateValue_pos g (Or.inr ho) a b h
    · rw [hnot.first hn]
      exact id

def booleanGate : Bool → Gate
  | true => ⟨.and, []⟩
  | false => ⟨.or, []⟩

theorem booleanGate_pos (b : Bool) : Positive (booleanGate b) := by
  cases b <;> simp [Positive, booleanGate]

theorem booleanGate_runs (b : Bool) (x : List Bool) :
    gateValue x (booleanGate b) = b := by
  cases b <;> rfl

noncomputable def freezeGate (a : List Bool) (g : Gate) : Gate := by
  classical
  exact if g.op = .not then booleanGate (gateValue a g) else g

noncomputable def freeze (a : List Bool) : List Gate → List Gate
  | [] => []
  | g :: gs => freezeGate a g :: freeze (appendGate a g) gs

theorem freeze_length (gs : List Gate) (a : List Bool) : (freeze a gs).length = gs.length := by
  induction gs generalizing a with
  | nil => rfl
  | cons g gs ih => simp [freeze, ih]

theorem freeze_pos (gs : List Gate) (a : List Bool) (h : ∀ g ∈ gs, Allowed g) :
    ∀ g ∈ freeze a gs, Positive g := by
  induction gs generalizing a with
  | nil => simp [freeze]
  | cons g gs ih =>
    intro q hq
    rw [freeze, List.mem_cons] at hq
    rcases hq with rfl | hq
    · classical
      unfold freezeGate
      split
      · exact booleanGate_pos _
      · rename_i hn
        obtain ⟨ha | ho | hh, hf⟩ := h g (List.mem_cons_self ..)
        · exact ⟨Or.inl ha, hf⟩
        · exact ⟨Or.inr ho, hf⟩
        · exact (hn hh).elim
    · exact ih _ (fun q hq => h q (List.mem_cons_of_mem _ hq)) _ hq

theorem freeze_run (gs : List Gate) (a b z : List Bool)
    (haz : Below a z) (hzb : Below z b) (hops : ∀ g ∈ gs, Allowed g)
    (hnot : AgreesNot gs a b) : run (freeze a gs) z = run gs z := by
  induction gs generalizing a b z with
  | nil => rfl
  | cons g gs ih =>
    rw [freeze, run_cons, run_cons]
    have hA : g ∈ g :: gs := List.mem_cons_self
    have hop := (hops g hA).1
    rcases hop with h | h | h
    · have hf : freezeGate a g = g := by
        classical
        simp [freezeGate, h]
      rw [hf]
      exact ih _ _ _ (appendGate_below haz g (gateValue_pos g (Or.inl h) a z haz))
        (appendGate_below hzb g (gateValue_pos g (Or.inl h) z b hzb))
        (fun q hq => hops q (List.mem_cons_of_mem _ hq)) hnot.tail
    · have hf : freezeGate a g = g := by
        classical
        simp [freezeGate, h]
      rw [hf]
      exact ih _ _ _ (appendGate_below haz g (gateValue_pos g (Or.inr h) a z haz))
        (appendGate_below hzb g (gateValue_pos g (Or.inr h) z b hzb))
        (fun q hq => hops q (List.mem_cons_of_mem _ hq)) hnot.tail
    · have he : gateValue a g = gateValue b g := hnot.first h
      have hze : gateValue z g = gateValue a g := by
        apply Bool.eq_iff_iff.mpr
        refine ⟨gateValue_neg g h a z haz, ?_⟩
        rw [he]
        exact gateValue_neg g h z b hzb
      have hf : appendGate z (freezeGate a g) = appendGate z g := by
        classical
        unfold appendGate
        simp [freezeGate, h, booleanGate_runs, hze]
      rw [hf]
      exact ih _ _ _ (appendGate_below haz g (by rw [hze]; exact id))
        (appendGate_below hzb g (by rw [hze, he]; exact id))
        (fun q hq => hops q (List.mem_cons_of_mem _ hq)) hnot.tail


theorem note_antitone (gs : List Gate) (a b : List Bool) (h : Below a b)
    (hops : ∀ g ∈ gs, Allowed g) (i : ℕ) (g : Gate) (hi : gs[i]? = some g)
    (hg : g.op = .not)
    (hprev : ∀ (j : ℕ) (q : Gate), j < i → gs[j]? = some q → q.op = .not →
      (run gs a).getD (a.length + j) false = (run gs b).getD (b.length + j) false) :
    (run gs b).getD (b.length + i) false = true →
      (run gs a).getD (a.length + i) false = true := by
  induction gs generalizing a b i g with
  | nil => simp at hi
  | cons q gs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst g
      simpa only [Nat.add_zero, value_first] using gateValue_neg q hg a b h
    | succ i =>
      have hb : Below (appendGate a q) (appendGate b q) := by
        apply appendGate_below h
        rcases (hops q (List.mem_cons_self ..)).1 with ha | ho | hn
        · exact gateValue_pos q (Or.inl ha) a b h
        · exact gateValue_pos q (Or.inr ho) a b h
        · have he := hprev 0 q (Nat.zero_lt_succ i) rfl hn
          simp only [Nat.add_zero, value_first] at he
          rw [he]
          exact id
      have hpre (j : ℕ) (r : Gate) (hji : j < i) (hj : gs[j]? = some r)
          (hr : r.op = .not) :
          (run gs (appendGate a q)).getD ((appendGate a q).length + j) false =
          (run gs (appendGate b q)).getD ((appendGate b q).length + j) false := by
        rw [next_index, next_index]
        exact hprev (j+1) r (by omega) (by simpa using hj) hr
      have got := ih _ _ hb (fun r hr => hops r (List.mem_cons_of_mem _ hr))
        i g (by simpa using hi) hg hpre
      rwa [next_index, next_index] at got

noncomputable def notIndices (gs : List Gate) : Finset (Fin gs.length) := by
  classical
  exact Finset.univ.filter (fun i => (gs.get i).op = .not)

theorem mem_notIndices (gs : List Gate) (j : Fin gs.length) :
    j ∈ notIndices gs ↔ (gs.get j).op = .not := by
  classical
  simp [notIndices]

noncomputable def notEmbedding (gs : List Gate) :
    Fin (notIndices gs).card ↪o Fin gs.length :=
  (notIndices gs).orderEmbOfFin rfl

theorem notEmbedding_mem (gs : List Gate) (j : Fin (notIndices gs).card) :
    notEmbedding gs j ∈ notIndices gs :=
  (notIndices gs).orderEmbOfFin_mem rfl j

theorem exists_notEmbedding (gs : List Gate) (j : Fin gs.length)
    (hj : j ∈ notIndices gs) : ∃ i, notEmbedding gs i = j := by
  have h := (notIndices gs).range_orderEmbOfFin rfl
  change Set.range (notEmbedding gs) = _ at h
  change j ∈ Set.range (notEmbedding gs)
  rw [h]
  exact hj

theorem card_notIndices (gs : List Gate) (t : ℕ)
    (h : ∃ f : Fin t → Fin gs.length,
      ∀ i : Fin gs.length, (gs.get i).op = .not → ∃ j, f j = i) :
    (notIndices gs).card ≤ t := by
  classical
  obtain ⟨f, h⟩ := h
  have hsub : notIndices gs ⊆ Finset.univ.image f := by
    intro j hj
    obtain ⟨i, hi⟩ := h j ((mem_notIndices gs j).1 hj)
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))

def trace {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin gs.length) : Bool :=
  (run gs (List.ofFn x)).getD (n + i.val) false

theorem trace_after {n m : ℕ} (gs : List Gate) (x : Fin m → Fin n → Bool)
    (hx : ∀ a b : Fin m, a ≤ b → ∀ w, x a w = true → x b w = true)
    (hg : ∀ g ∈ gs, Allowed g)
    (i : Fin (notIndices gs).card) (a b : Fin m) (hab : a ≤ b)
    (hprev : ∀ j : Fin (notIndices gs).card, j < i →
      trace gs (x a) (notEmbedding gs j) = trace gs (x b) (notEmbedding gs j)) :
    trace gs (x b) (notEmbedding gs i) = true →
      trace gs (x a) (notEmbedding gs i) = true := by
  let j := notEmbedding gs i
  have hj := (mem_notIndices gs j).1 (notEmbedding_mem gs i)
  have hi : gs[j.val]? = some (gs.get j) := List.getElem?_eq_getElem j.isLt
  have got := note_antitone gs (List.ofFn (x a)) (List.ofFn (x b))
    (initial_below _ _ (hx a b hab)) hg j.val (gs.get j) hi hj
  have earlier (k : ℕ) (q : Gate) (hk : k < j.val) (hq : gs[k]? = some q)
      (hqn : q.op = .not) :
      (run gs (List.ofFn (x a))).getD ((List.ofFn (x a)).length + k) false =
      (run gs (List.ofFn (x b))).getD ((List.ofFn (x b)).length + k) false := by
    have hkl : k < gs.length := by
      apply lt_trans hk
      exact j.isLt
    let k' : Fin gs.length := ⟨k, hkl⟩
    have hget : gs.get k' = q := by simpa [k', List.getElem?_eq_getElem hkl] using hq
    obtain ⟨p, hp⟩ := exists_notEmbedding gs k'
      ((mem_notIndices gs k').2 (hget ▸ hqn))
    have hpi : p < i := by
      have hlt : notEmbedding gs p < notEmbedding gs i := by
        rw [hp]
        exact hk
      exact (notEmbedding gs).lt_iff_lt.mp hlt
    have h := hprev p hpi
    rw [hp] at h
    simpa only [trace, List.length_ofFn, k'] using h
  simpa only [trace, List.length_ofFn, j] using got earlier

theorem trace_agrees {n : ℕ} (gs : List Gate) (a b : Fin n → Bool)
    (h : ∀ i : Fin (notIndices gs).card,
      trace gs a (notEmbedding gs i) = trace gs b (notEmbedding gs i)) :
    AgreesNot gs (List.ofFn a) (List.ofFn b) := by
  intro j g hj hg
  have hlt : j < gs.length := (List.getElem?_eq_some_iff.mp hj).choose
  let i : Fin gs.length := ⟨j, hlt⟩
  have he : gs.get i = g := by simpa [i, List.getElem?_eq_getElem hlt] using hj
  obtain ⟨p, hp⟩ := exists_notEmbedding gs i
    ((mem_notIndices gs i).2 (he ▸ hg))
  have hh := h p
  rw [hp] at hh
  simpa only [trace, List.length_ofFn, i] using hh

namespace Incidence

def through {n : ℕ} (S : Fin n → Finset (Fin n)) (p : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => p ∈ S i)

theorem through_card {n q : ℕ} (S : Fin n → Finset (Fin n))
    (hn : n = q*q + q + 1) (hq : 0 < q)
    (hS : ∀ i, (S i).card = q+1)
    (hcross : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (hjoin : ∀ p p' : Fin n, p ≠ p' → ∃ i, p ∈ S i ∧ p' ∈ S i)
    (p : Fin n) : (through S p).card = q + 1 := by
  let T := through S p
  have hdis : (T : Set (Fin n)).PairwiseDisjoint (fun i => (S i).erase p) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have hpi : p ∈ S i := by simpa [T, through] using hi
    have hpj : p ∈ S j := by simpa [T, through] using hj
    have hp : p ∈ S i ∩ S j := Finset.mem_inter.mpr ⟨hpi, hpj⟩
    have ha' : a ∈ S i ∩ S j := Finset.mem_inter.mpr
      ⟨Finset.mem_of_mem_erase ha, Finset.mem_of_mem_erase hb⟩
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (hcross i j hij)
    have hpv : p = v := by simpa [hv] using hp
    have hav : a = v := by simpa [hv] using ha'
    exact (Finset.mem_erase.mp ha).1 (hav.trans hpv.symm)
  have hcover : T.biUnion (fun i => (S i).erase p) =
      (Finset.univ : Finset (Fin n)).erase p := by
    ext a
    constructor
    · intro ha
      obtain ⟨i, _, hmem⟩ := Finset.mem_biUnion.mp ha
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hmem).1, Finset.mem_univ _⟩
    · intro ha
      have hpa : p ≠ a := Ne.symm (Finset.mem_erase.mp ha).1
      obtain ⟨i, hpi, hai⟩ := hjoin p a hpa
      exact Finset.mem_biUnion.mpr ⟨i, by simpa [T, through] using hpi,
        Finset.mem_erase.mpr ⟨Ne.symm hpa, hai⟩⟩
  have hf (i : Fin n) (hi : i ∈ T) : ((S i).erase p).card = q := by
    have hpi : p ∈ S i := by simpa [T, through] using hi
    rw [Finset.card_erase_of_mem hpi, hS]
    omega
  have hcount := Finset.card_biUnion hdis
  rw [hcover, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  calc
    (through S p).card = T.card := rfl
    _ = q + 1 := by
      have hsum : (∑ i ∈ T, ((S i).erase p).card) = T.card * q := by
        rw [Finset.sum_congr rfl hf, Finset.sum_const, nsmul_eq_mul]
        rfl
      rw [hsum] at hcount
      have hmul : q * T.card = q * (q+1) := by
        rw [Nat.mul_comm q T.card, ← hcount, hn]
        rw [Nat.mul_add, Nat.mul_one]
        omega
      exact Nat.eq_of_mul_eq_mul_left hq hmul

end Incidence
end PEqualNP.Outside.L_meta_1325_aux.Trace

namespace PEqualNP.Outside.L_meta_1325_aux

def Frozen {n s : ℕ} (color : Fin s → Finset (Fin n) → Bool) (d : ℕ) (Y : Finset (Fin n)) (K : ℕ) :=
  ∀ i : Fin s, i.val < d → ∀ X : Finset (Fin n), X.card ≤ K → color i (Y ∪ X) = color i Y

private lemma fold_bound {f : ℕ → ℕ} {L : List ℕ} {cap : ℕ} (h : ∀ j ∈ L, f j ≤ cap) :
    L.foldr (fun j a => max a (f j)) 0 ≤ cap := by
  induction L with
  | nil => exact Nat.zero_le _
  | cons j L ih =>
    exact max_le (ih (fun k hk => h k (List.mem_cons_of_mem _ hk))) (h j List.mem_cons_self)

theorem recursive_bound {n s cap : ℕ} (color : Fin s → Finset (Fin n) → Bool)
    (anti : ∀ i A B, A ⊆ B → (∀ j : Fin s, j < i → color j A = color j B) →
      color i B = true → color i A = true)
    (G : ℕ → ℕ → ℕ → ℕ)
    (step : ∀ t b K, G (t+1) b K = (List.range (K+1)).foldr
      (fun j acc => max acc (min (G t (b+j) (K-j)) (G t b j))) 0)
    (base : ∀ b K (Y : Finset (Fin n)), Y.card ≤ b → Frozen color s Y K → G 0 b K ≤ cap) :
    G s 0 n ≤ cap := by
  classical
  have game (r d : ℕ) (hd : d+r=s) (b K : ℕ) (Y : Finset (Fin n))
      (hy : Y.card ≤ b) (hfix : Frozen color d Y K) : G r b K ≤ cap := by
    induction r generalizing d b K Y with
    | zero =>
      have eq : d = s := by omega
      exact base b K Y hy (eq ▸ hfix)
    | succ r ih =>
      rw [step]
      apply fold_bound
      intro j hj
      have hjK : j ≤ K := by have := List.mem_range.mp hj; omega
      let i : Fin s := ⟨d,by omega⟩
      by_cases short : ∀ X : Finset (Fin n), X.card ≤ j → color i (Y ∪ X) = color i Y
      · apply le_trans (min_le_right _ _)
        apply ih (d+1) (by omega) b j Y hy
        intro u hu X hX
        by_cases old : u.val < d
        · exact hfix u old X (hX.trans hjK)
        · have he : u = i := Fin.ext (by change u.val = d; omega)
          exact he ▸ short X hX
      · push Not at short
        obtain ⟨X,hX,diff⟩ := short
        let A := Y ∪ X
        have hXK := hX.trans hjK
        have frozen (u : Fin s) (hu : u.val < d) (Z : Finset (Fin n)) (hZ : Z.card ≤ K-j) :
            color u (A ∪ Z) = color u A := by
          have hc := Finset.card_union_le X Z
          change color u ((Y ∪ X) ∪ Z) = color u (Y ∪ X)
          rw [Finset.union_assoc, hfix u hu (X∪Z) (by omega), hfix u hu X hXK]
        have fall : color i A = false := by
          cases he : color i A with
          | false => rfl
          | true =>
            have htrue := anti i Y A Finset.subset_union_left
              (fun u hu => (hfix u hu X hXK).symm) he
            exact (diff (he.trans htrue.symm)).elim
        apply le_trans (min_le_left _ _)
        apply ih (d+1) (by omega) (b+j) (K-j) A
          ((Finset.card_union_le Y X).trans (Nat.add_le_add hy hX))
        intro u hu Z hZ
        by_cases old : u.val < d
        · exact frozen u old Z hZ
        · have he : u = i := Fin.ext (by change u.val = d; omega)
          subst u
          rw [fall]
          apply Bool.eq_false_iff.mpr
          intro ht
          have contra := anti i A (A ∪ Z) Finset.subset_union_left
            (fun v hv => (frozen v hv Z hZ).symm) ht
          simp [fall] at contra
  exact game s 0 (by omega) 0 n ∅ (by simp) (fun _ h => (Nat.not_lt_zero _ h).elim)

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1325_aux.Trace (Allowed Positive AgreesNot trace trace_agrees trace_after
  notIndices notEmbedding card_notIndices initial_below freeze_run freeze freeze_pos freeze_length)
open PEqualNP.Outside.L_meta_1325_aux.Trace.Incidence (through_card)
open PEqualNP.Outside.L_meta_1325_aux.Windows (bit local_count linesHit untouched)

noncomputable def colors {n : ℕ} (gs : List Gate) (s : ℕ) (x : Fin n → Bool) (i : Fin s) : Bool :=
  if h : i.val < (notIndices gs).card then trace gs x (notEmbedding gs ⟨i.val,h⟩) else false

lemma colors_anti {n s : ℕ} (gs : List Gate) (hg : ∀ g ∈ gs, Allowed g)
    (x y : Fin n → Bool) (le : ∀ p, x p = true → y p = true) (i : Fin s)
    (earlier : ∀ j : Fin s, j < i → colors gs s x j = colors gs s y j) :
    colors gs s y i = true → colors gs s x i = true := by
  classical
  by_cases hi : i.val < (notIndices gs).card
  · let seq (v : Fin 2) := if v.val=0 then x else y
    have mono (a b : Fin 2) (ab : a ≤ b) (p : Fin n) : seq a p = true → seq b p = true := by
      fin_cases a <;> fin_cases b <;> first | exact le p | exact id | contradiction
    have h := trace_after gs seq mono hg ⟨i.val,hi⟩ 0 1 (by decide) (by
      intro j hj
      have hjs : j.val < s := lt_trans hj i.isLt
      simpa [colors,seq,j.isLt] using earlier ⟨j.val,hjs⟩ hj)
    simpa [colors,hi,seq] using h
  · simp [colors,hi]

lemma agree_of_colors {n s : ℕ} (gs : List Gate) (num : (notIndices gs).card ≤ s)
    (a b : Fin n → Bool) (h : ∀ i, colors gs s a i = colors gs s b i) :
    AgreesNot gs (List.ofFn a) (List.ofFn b) := by
  apply trace_agrees
  intro i
  have hi := h ⟨i.val,lt_of_lt_of_le i.isLt num⟩
  simpa [colors,i.isLt] using hi

lemma eval_frozen {n : ℕ} (gs : List Gate) (ops : ∀ g ∈ gs, Allowed g) (a b : Fin n → Bool)
    (ab : ∀ i, a i = true → b i = true) (eq : AgreesNot gs (List.ofFn a) (List.ofFn b))
    (o : ℕ) : Circuit.eval ⟨freeze (List.ofFn a) gs,o⟩ (List.ofFn b) =
      Circuit.eval ⟨gs,o⟩ (List.ofFn b) := by
  exact congrArg (fun w : List Bool => w.getD o false)
    (freeze_run gs (List.ofFn a) (List.ofFn b) (List.ofFn b)
      (initial_below _ _ ab) (initial_below b b (fun _ => id)) ops eq)

theorem first_cost {n q s : ℕ} (L : Fin n → Finset (Fin n))
    (hn : n=q*q+q+1) (hq : 2 ≤ q) (sz : ∀ i, (L i).card=q+1)
    (meet : ∀ i j, i≠j → (L i ∩ L j).card=1)
    (pair : ∀ a b : Fin n, a≠b → ∃ i, a ∈ L i ∧ b ∈ L i)
    (gs : List Gate) (out : Fin n → ℕ) (ops : ∀ g ∈ gs, Allowed g)
    (num : (notIndices gs).card ≤ s)
    (comp : ∀ w (x : Fin n → Bool), Circuit.eval ⟨gs,out w⟩ (List.ofFn x) =
      decide (∃ v ∈ L w, x v = true))
    (G : ℕ → ℕ → ℕ → ℕ)
    (zero : ∀ b K, G 0 b K = (n - (if b=0 then 0 else min n (b*q+1))) * min K q)
    (step : ∀ t b K, G (t+1) b K = (List.range (K+1)).foldr
      (fun j acc => max acc (min (G t (b+j) (K-j)) (G t b j))) 0) :
    G s 0 n ≤ gs.length := by
  classical
  let C (i : Fin s) (Y : Finset (Fin n)) := colors gs s (bit Y) i
  apply recursive_bound C (fun i A B h => colors_anti gs ops _ _
    (fun p hp => decide_eq_true (h (of_decide_eq_true hp))) i) G step
  intro b K Y hy hfix
  rw [zero]
  by_cases hk : K=0
  · simp [hk]
  let gs' := freeze (List.ofFn (bit Y)) gs
  have ok := freeze_pos gs (List.ofFn (bit Y)) ops
  have win (i : Fin n) (X : Finset (Fin n)) (hX : X.card ≤ K) :
      Circuit.eval ⟨gs',out i⟩ (List.ofFn (bit (Y ∪ X))) = decide (∃ p ∈ L i, p ∈ Y ∪ X) := by
    have eq := agree_of_colors gs num (bit Y) (bit (Y∪X)) (fun u => (hfix u u.isLt X hX).symm)
    calc
      _ = Circuit.eval ⟨gs,out i⟩ (List.ofFn (bit (Y ∪ X))) := eval_frozen gs ops (bit Y) (bit (Y ∪ X))
        (fun p hp => decide_eq_true (Finset.mem_union_left _ (of_decide_eq_true hp))) eq (out i)
      _ = _ := by rw [comp]; simp [bit]
  have price := local_count PEqualNP.Outside.L_meta_1325_aux.Light PEqualNP.Outside.L_meta_1325_aux.Restrict
    (by omega : 1 ≤ K) (by omega : 1 ≤ q) L Y sz (fun i j h => (meet i j h).le) gs' out ok win
  rw [show gs'.length=gs.length from freeze_length gs _] at price
  refine (Nat.mul_le_mul_right (min K q) ?_).trans price
  by_cases hb : b=0
  · have hy0 : Y=∅ := Finset.card_eq_zero.mp (by omega)
    simp [hb,hy0,untouched]
  · have reg (p : Fin n) := through_card L hn (by omega) sz meet pair p
    have hits := linesHit L reg pair Y
    have split := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i => Disjoint Y (L i))
    have hy' := Nat.mul_le_mul_right q hy
    simp only [Finset.card_univ,Fintype.card_fin] at split
    simp only [untouched,ite_eq_right hb]
    rw [Nat.mul_comm q Y.card] at hits
    omega

open PEqualNP.Outside.L_meta_1325_aux.Heavy (value offSet cut input_value missing_value value_mono union_bound)

private def owned {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n))
    (Z : Finset (Fin n)) (i : Fin m) : Finset ℕ :=
  (Finset.Ico n (n+C.size)).filter fun w =>
    value C (offSet (Z ∪ S i)) w = false ∧ ∀ j, j ≠ i → value C (offSet (Z ∪ S j)) w = true

private lemma based_count {q n m K : ℕ} (S : Fin m → Finset (Fin n))
    (hq : 2 ≤ q) (hsize : ∀ i, (S i).card = q+1)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (C : Circuit) (Z : Finset (Fin n)) (i : Fin m) (o c : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (heval : ∀ T : Finset (Fin n), T.card ≤ K →
      (value C (offSet (Z ∪ T)) o = false ↔ S i ⊆ Z ∪ T))
    (hc : c + 1 ≤ (S i \ Z).card) (hK : c*q < K) : c ≤ (owned C S Z i).card := by
  classical
  by_contra! hsmall
  let G := owned C S Z i
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := by
    intro w hw
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B, hd, hBC, hcut⟩ := cut C hg G hgate (n+C.size) {o} (fun w _ hw => (hgate w hw).2)
  have hb : B.card ≤ c := by
    have hf := Finset.card_filter_le G (fun w => w < n+C.size)
    simp only [Finset.card_singleton] at hBC
    change G.card < c at hsmall
    omega
  have hpositive : 1 ≤ c := by omega
  have hsK : (S i).card ≤ K := by
    have hp := Nat.mul_le_mul_right q hpositive
    rw [Nat.one_mul] at hp
    rw [hsize]
    omega
  have witness (w : ℕ) (hw : w ∈ B) : ∃ T : Finset (Fin n),
      (T.card ≤ q ∨ ∃ j, T = S j) ∧ (T ∩ S i).card ≤ 1 ∧
      (value C (offSet (Z ∪ T)) w = true → value C (offSet (Z ∪ S i)) w = true) := by
    by_cases hv : value C (offSet (Z ∪ S i)) w = true
    · exact ⟨∅,Or.inl (by simp),by simp,fun _ => hv⟩
    · by_cases hin : w < n
      · let p : Fin n := ⟨w,hin⟩
        refine ⟨{p},Or.inl (by simp; omega),?_,?_⟩
        · exact (Finset.card_le_card (Finset.inter_subset_left : {p} ∩ S i ⊆ {p})).trans (by simp)
        · intro h
          change value C (offSet (Z ∪ {p})) p = true at h
          simp [input_value,offSet] at h
      · by_cases bound : w < n+C.size
        · have hn : w ∉ owned C S Z i := Finset.disjoint_left.mp hd hw
          have hex : ∃ j, j ≠ i ∧ ¬ value C (offSet (Z ∪ S j)) w = true := by
            by_contra! neg
            apply hn
            refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,bound⟩,?_,neg⟩
            simpa using hv
          obtain ⟨j,hji,hj⟩ := hex
          exact ⟨S j,Or.inr ⟨j,rfl⟩,(hinter j i hji).le,fun h => absurd h hj⟩
        · refine ⟨∅,Or.inl (by simp),by simp,fun h => ?_⟩
          have hm := missing_value C (offSet (Z ∪ (∅ : Finset (Fin n)))) w (by omega)
          rw [hm] at h
          exact Bool.noConfusion h
  let A (w : ℕ) : Finset (Fin n) := if h : w ∈ B then (witness w h).choose else ∅
  have ha (w : ℕ) (hw : w ∈ B) :
      ((A w).card ≤ q ∨ ∃ j, A w = S j) ∧ (A w ∩ S i).card ≤ 1 ∧
      (value C (offSet (Z ∪ A w)) w = true → value C (offSet (Z ∪ S i)) w = true) := by
    simpa [A,hw] using (witness w hw).choose_spec
  let U := B.biUnion A
  have hu : U.card ≤ K := by
    have h := union_bound S hsize hinter B A (fun w hw => (ha w hw).1)
    have h' := Nat.mul_le_mul_right q hb
    change (B.biUnion A).card ≤ K
    omega
  have hSi : value C (offSet (Z ∪ S i)) o = false := (heval (S i) hsK).mpr Finset.subset_union_right
  have hot : value C (offSet (Z ∪ U)) o = false := by
    by_contra hne
    have ht : value C (offSet (Z ∪ U)) o = true := by simpa using hne
    have h2 := hcut (offSet (Z ∪ U)) (offSet (Z ∪ S i)) (fun w hw hp => by
      apply (ha w hw).2.2
      apply value_mono C hg (offSet (Z ∪ U)) (offSet (Z ∪ A w)) _ w hp
      intro p hp
      simp only [offSet, decide_eq_true_eq] at hp ⊢
      intro hm
      apply hp
      exact Finset.union_subset_union_right (Finset.subset_biUnion_of_mem A hw) hm) o (Finset.mem_singleton_self o) ht
    rw [hSi] at h2
    exact Bool.noConfusion h2
  have hSub := (heval U hu).mp hot
  have hcover : S i \ Z ⊆ B.biUnion (fun w => A w ∩ S i) := by
    intro p hp
    obtain ⟨hp,hz⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨w,hw,hm⟩ := Finset.mem_biUnion.mp ((Finset.mem_union.mp (hSub hp)).resolve_left hz)
    exact Finset.mem_biUnion.mpr ⟨w,hw,Finset.mem_inter.mpr ⟨hm,hp⟩⟩
  have h1 := Finset.card_le_card hcover
  have h2 := Finset.card_biUnion_le_card_mul B (fun w => A w ∩ S i) 1 (fun w hw => (ha w hw).2.1)
  simp only [Nat.mul_one] at h2
  omega

open PEqualNP.Outside.L_meta_1325_aux.Trace (freezeGate appendGate gateValue)

private lemma same_freeze (gs : List Gate) (a b : List Bool) (h : AgreesNot gs a b) :
    freeze a gs = freeze b gs := by
  induction gs generalizing a b with
  | nil => rfl
  | cons g gs ih =>
    have eqg : freezeGate a g = freezeGate b g := by
      by_cases hn : g.op = .not
      · simp [freezeGate,hn,h.first hn]
      · simp [freezeGate,hn]
    simp only [freeze,eqg]
    rw [ih _ _ h.tail]

private lemma heavy_price {n m q j : ℕ} (S : Fin m → Finset (Fin n)) (Z : Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (hq : 2 ≤ q)
    (hs : ∀ i, (S i).card=q+1) (hi : ∀ i j, i≠j → (S i ∩ S j).card=1)
    (ops : ∀ g ∈ C.gates, Positive g)
    (he : ∀ i T, T.card ≤ j*q+1 → (value C (offSet (Z∪T)) (o i) = false ↔ S i ⊆ Z∪T)) :
    (∑ i ∈ Finset.univ.filter (fun i => (S i ∩ Z).card + 1 ≤ q), min j (q-(S i ∩ Z).card)) ≤ C.size := by
  classical
  let R := Finset.univ.filter (fun i => (S i ∩ Z).card+1 ≤ q)
  let W := Finset.Ico n (n+C.size)
  have hd : (R : Set (Fin m)).PairwiseDisjoint (owned C S Z) := by
    intro i _ j _ hne
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    have y := (Finset.mem_filter.mp hw).2.2 j (Ne.symm hne)
    have z := (Finset.mem_filter.mp hw').2.1
    simp [y] at z
  calc
    _ ≤ ∑ i ∈ R, (owned C S Z i).card := by
      apply Finset.sum_le_sum
      intro i hI
      have sz := Finset.card_sdiff_add_card_inter (S i) Z
      rw [hs] at sz
      have hact := (Finset.mem_filter.mp hI).2
      apply based_count S hq hs hi C Z i (o i) _ ops (he i)
      · omega
      · have hmul := Nat.mul_le_mul_right q (min_le_left j (q-(S i ∩ Z).card))
        omega
    _ = (R.biUnion (owned C S Z)).card := (Finset.card_biUnion hd).symm
    _ ≤ W.card := Finset.card_le_card (Finset.biUnion_subset.mpr (fun i _ => Finset.filter_subset _ _))
    _ = C.size := by simp [W]

private lemma eval_heavy {n q j m : ℕ} (S : Fin m → Finset (Fin n)) (Z : Finset (Fin n))
    (gs : List Gate) (out : Fin m → ℕ) (hq : 2 ≤ q)
    (hs : ∀ i, (S i).card=q+1) (hi : ∀ i j, i≠j → (S i ∩ S j).card=1)
    (ops : ∀ g ∈ gs, Allowed g)
    (comp : ∀ w (x : Fin n → Bool), Circuit.eval ⟨gs,out w⟩ (List.ofFn x) =
      decide (∃ v ∈ S w, x v = true))
    (stable : ∀ X : Finset (Fin n), X.card ≤ j*q+1 →
      AgreesNot gs (List.ofFn (offSet (Z∪X))) (List.ofFn (offSet Z))) :
    (∑ i ∈ Finset.univ.filter (fun i => (S i ∩ Z).card + 1 ≤ q), min j (q-(S i ∩ Z).card)) ≤ gs.length := by
  let gs' := freeze (List.ofFn (offSet Z)) gs
  let C : Circuit := ⟨gs',0⟩
  have eq := freeze_length gs (List.ofFn (offSet Z))
  change gs'.length=gs.length at eq
  rw [← eq]
  apply heavy_price S Z C out hq hs hi (freeze_pos _ _ ops)
  intro i X hX
  let a := offSet (Z∪X)
  have fix : freeze (List.ofFn a) gs = gs' := same_freeze _ _ _ (stable _ hX)
  change Circuit.eval ⟨gs',out i⟩ (List.ofFn a) = false ↔ _
  rw [← fix, eval_frozen gs ops a a (fun _ => id) (fun _ _ _ _ => rfl), comp]
  simp [a,offSet,Finset.subset_iff]
  constructor
  · intro h p hp
    exact or_iff_not_imp_left.mpr (h p hp)
  · intro h p hp hn
    exact (h hp).resolve_left hn

private noncomputable def belowTrace {s : ℕ} (v : Fin s → Bool) : Finset (Fin s → Bool) := by
  classical
  exact Finset.univ.filter (fun a => toLex a < toLex v)

private lemma below_iff {s : ℕ} (a b : Fin s → Bool) : a ∈ belowTrace b ↔ toLex a < toLex b := by
  classical
  simp [belowTrace]

private lemma height_strict {s : ℕ} {a b : Fin s → Bool} (h : toLex a < toLex b) :
    (belowTrace a).card < (belowTrace b).card := by
  classical
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset (fun x hx => (below_iff x b).mpr
    (lt_trans ((below_iff x a).mp hx) h))).mpr
  exact ⟨a,(below_iff a b).mpr h,fun ha => lt_irrefl _ ((below_iff a a).mp ha)⟩

private lemma height_bound {s : ℕ} (a : Fin s → Bool) : (belowTrace a).card < 2^s := by
  classical
  calc
    (belowTrace a).card < (Finset.univ : Finset (Fin s → Bool)).card := by
      apply Finset.card_lt_card
      apply (Finset.ssubset_iff_of_subset (Finset.subset_univ _)).mpr
      exact ⟨a,Finset.mem_univ _,fun ha => lt_irrefl _ ((below_iff a a).mp ha)⟩
    _ = _ := by simp

private lemma false_lex {n s : ℕ} (gs : List Gate) (ops : ∀ g ∈ gs, Allowed g)
    (A B : Finset (Fin n)) (h : A ⊆ B) :
    toLex (colors gs s (offSet A)) ≤ toLex (colors gs s (offSet B)) := by
  apply le_of_not_gt
  intro hbad
  obtain ⟨i,earlier,hi⟩ := hbad
  have mono := colors_anti gs ops (offSet B) (offSet A) (fun p hp =>
    decide_eq_true (fun ha => (of_decide_eq_true hp) (h ha))) i earlier
  have hA : colors gs s (offSet A) i = true := by
    cases ha : colors gs s (offSet A) i <;> cases hb : colors gs s (offSet B) i <;> simp_all
    exact (by decide : ¬ true < false) hi
  have hB := mono hA
  change colors gs s (offSet B) i < colors gs s (offSet A) i at hi
  simp [hB,hA] at hi

private lemma stable_height {n : ℕ} (H : Finset (Fin n) → ℕ) (D : ℕ) :
    ∃ Z : Finset (Fin n), Z.card ≤ H Z * D ∧
       (∀ X : Finset (Fin n), X.card ≤ D → H (Z ∪ X) ≤ H Z) := by
  classical
  let P := Finset.univ.filter (fun A : Finset (Fin n) => A.card ≤ H A * D)
  have pn : P.Nonempty := ⟨∅,by simp [P]⟩
  obtain ⟨Z,hz,hm⟩ := Finset.exists_max_image P H pn
  have zc := (Finset.mem_filter.mp hz).2
  refine ⟨Z,zc,?_⟩
  intro X hx
  by_contra! increase
  have price : Z.card+X.card ≤ H (Z∪X)*D := by
    calc
      _ ≤ H Z*D+D := Nat.add_le_add zc hx
      _ = (H Z+1)*D := by simp [Nat.add_mul]
      _ ≤ _ := Nat.mul_le_mul_right D increase
  exact increase.not_ge (hm _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.card_union_le _ _).trans price⟩))

theorem second_cost {n q s : ℕ} (S : Fin n → Finset (Fin n))
    (hq : 2 ≤ q) (hs : ∀ i, (S i).card=q+1)
    (hi : ∀ i j, i≠j → (S i ∩ S j).card=1)
    (gs : List Gate) (out : Fin n → ℕ) (ops : ∀ g ∈ gs, Allowed g) (num : (notIndices gs).card ≤ s)
    (comp : ∀ w (x : Fin n → Bool), Circuit.eval ⟨gs,out w⟩ (List.ofFn x) =
      decide (∃ v ∈ S w, x v = true))
    (j F T : ℕ) (_hj : 1 ≤ j) (_hj' : j ≤ q) (hF : F+1 = 2^s)
    (early : ∀ i, i+1 ≤ F → ∀ Z : Finset (Fin n), Z.card ≤ i*(j*q+1) → T ≤
      ∑ l ∈ Finset.univ.filter (fun l => (S l ∩ Z).card+1 ≤ q), min j (q-(S l ∩ Z).card))
    (last : ∀ Z : Finset (Fin n), Z.card ≤ F*(j*q+1) → T ≤
      ∑ l ∈ Finset.univ.filter (fun l => (S l ∩ Z).card+1 ≤ q), (q-(S l ∩ Z).card)) :
    T ≤ gs.length := by
  classical
  let V (Z : Finset (Fin n)) := colors gs s (offSet Z)
  let H (Z : Finset (Fin n)) := (belowTrace (V Z)).card
  have bound (A : Finset (Fin n)) : H A ≤ F := by
    have h := height_bound (V A)
    change (belowTrace (V A)).card ≤ F
    omega
  obtain ⟨Z,hz,fixed⟩ := stable_height H (j*q+1)
  have agree (X : Finset (Fin n)) (hscore : H (Z∪X) ≤ H Z) :
      AgreesNot gs (List.ofFn (offSet (Z∪X))) (List.ofFn (offSet Z)) := by
    apply agree_of_colors gs num
    have le : toLex (V Z) ≤ toLex (V (Z∪X)) := false_lex gs ops _ _ Finset.subset_union_left
    have eq : toLex (V Z) = toLex (V (Z∪X)) := by
      rcases le.lt_or_eq with lt | eq
      · exact (hscore.not_gt (height_strict lt)).elim
      · exact eq
    exact fun i => congrFun (toLex_inj.mp eq.symm) i
  by_cases atMax : H Z = F
  · have zF : Z.card ≤ F*(j*q+1) := atMax ▸ hz
    apply (last Z zF).trans
    have big := eval_heavy (j := q) S Z gs out hq hs hi ops comp (fun X _ => agree X (atMax ▸ bound _))
    simpa [Nat.min_eq_right (Nat.sub_le q _)] using big
  · apply (early (H Z) (by have := bound Z; omega) Z hz).trans
    exact eval_heavy S Z gs out hq hs hi ops comp (fun X hx => agree X (fixed X hx))

end PEqualNP.Outside.L_meta_1325_aux

open PEqualNP.Outside.L_meta_1325_aux in
theorem PEqualNP.Outside.L_meta_1325 : ∀ (q s : ℕ) (L : Fin (q ^ 2 + q + 1) → Finset (Fin (q ^ 2 + q + 1))), 2 ≤ q → (∀ i : Fin (q ^ 2 + q + 1), (L i).card = q + 1) → (∀ i j : Fin (q ^ 2 + q + 1), i ≠ j → (L i ∩ L j).card = 1) → (∀ p p' : Fin (q ^ 2 + q + 1), p ≠ p' → ∃ i : Fin (q ^ 2 + q + 1), p ∈ L i ∧ p' ∈ L i) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin (q ^ 2 + q + 1) → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s, ι j = i) → (∀ (w : Fin (q ^ 2 + q + 1)) (x : Fin (q ^ 2 + q + 1) → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ L w, x v = true)) → (∀ G : ℕ → ℕ → ℕ → ℕ, (∀ b K : ℕ, G 0 b K = ((q ^ 2 + q + 1) - (if b = 0 then 0 else min (q ^ 2 + q + 1) (b * q + 1))) * min K q) → (∀ t b K : ℕ, G (t + 1) b K = (List.range (K + 1)).foldr (fun (j acc : ℕ) => max acc (min (G t (b + j) (K - j)) (G t b j))) 0) → G s 0 (q ^ 2 + q + 1) ≤ gates.length) ∧ (∀ j F T : ℕ, 1 ≤ j → j ≤ q → F + 1 = 2 ^ s → (∀ i : ℕ, i + 1 ≤ F → ∀ z : Finset (Fin (q ^ 2 + q + 1)), z.card ≤ i * (j * q + 1) → T ≤ ∑ l ∈ Finset.univ.filter (fun l : Fin (q ^ 2 + q + 1) => (L l ∩ z).card + 1 ≤ q), min j (q - (L l ∩ z).card)) → (∀ z : Finset (Fin (q ^ 2 + q + 1)), z.card ≤ F * (j * q + 1) → T ≤ ∑ l ∈ Finset.univ.filter (fun l : Fin (q ^ 2 + q + 1) => (L l ∩ z).card + 1 ≤ q), (q - (L l ∩ z).card)) → T ≤ gates.length) := by
  intro q s L hq sz meet pair gs out ops cover comp
  have num := PEqualNP.Outside.L_meta_1325_aux.Trace.card_notIndices gs s cover
  constructor
  · intro G zero step
    exact first_cost L (by simp [pow_two]) hq sz meet pair gs out ops num comp G zero step
  · exact second_cost L hq sz meet gs out ops num comp
