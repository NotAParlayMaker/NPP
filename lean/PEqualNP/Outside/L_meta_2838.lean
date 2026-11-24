import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_2838

-- Circuit basics, adapted from L-meta-782 to gates of fan-in at most two.

def Ok (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

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
    value C x w = (C.gates[w - n]'(by unfold Circuit.size at hw; omega)).op.eval
      ((C.gates[w - n]'(by unfold Circuit.size at hw; omega)).inputs.map
        fun r => if r < w then value C x r else false) := by
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

lemma gate_inputs {n : ℕ} (C : Circuit) (hG : Ok C)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  have hj : w - n < C.gates.length := by unfold Circuit.size at hw; omega
  let g := C.gates[w - n]
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen), ?_, ?_⟩
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have hr : ∀ r ∈ g.inputs, (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      intro r hr
      by_cases h : r < w
      · simp only [h, ite_true]
        exact hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, h⟩)
      · simp [h]
    have fx := gate_value C x w hn hw
    have fy := gate_value C y w hn hw
    change value C x w = g.op.eval _ at fx
    change value C y w = g.op.eval _ at fy
    rw [fx] at hx
    rw [fy]
    rcases hop with hop | hop
    · rw [hop] at hx ⊢
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hx ⊢
      intro r hrm
      exact hr r hrm (hx r hrm)
    · rw [hop] at hx ⊢
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq,
        exists_exists_and_eq_and] at hx ⊢
      obtain ⟨r, hrm, hv⟩ := hx
      exact ⟨r, hrm, hr r hrm hv⟩

lemma value_mono {n : ℕ} (C : Circuit) (hG : Ok C)
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

lemma cut {n : ℕ} (C : Circuit) (hG : Ok C)
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
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,
            by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hd, by omega, hi⟩

-- Sums seen through an embedding of one side of the inputs.

def single {n M : ℕ} (emb : Fin M → Fin n) (l : Fin M) : Fin n → Bool :=
  fun k => decide (k = emb l)

def ind {n M : ℕ} (emb : Fin M → Fin n) (Y : Finset (Fin M)) : Fin n → Bool :=
  fun k => decide (∃ l ∈ Y, k = emb l)

def supE {n M : ℕ} (C : Circuit) (emb : Fin M → Fin n) (w : ℕ) : Finset (Fin M) :=
  Finset.univ.filter (fun l => value C (single emb l) w = true)

def assignedE {n M : ℕ} (C : Circuit) (emb : Fin M → Fin n) (T : Finset (Fin M)) :
    Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter fun w => supE C emb w ⊆ T ∧ 2 ≤ (supE C emb w).card

lemma mem_supE {n M : ℕ} (C : Circuit) (emb : Fin M → Fin n) (w : ℕ) (l : Fin M) :
    l ∈ supE C emb w ↔ value C (single emb l) w = true := by
  simp [supE]

lemma supE_gate {n M : ℕ} (C : Circuit) (emb : Fin M → Fin n)
    (hemb : Function.Injective emb) (w : ℕ) (h : 2 ≤ (supE C emb w).card) :
    n ≤ w ∧ w < n + C.size := by
  constructor
  · by_contra! hw
    have hle : (supE C emb w).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      have va := (mem_supE C emb w a).mp ha
      have vb := (mem_supE C emb w b).mp hb
      have ia := input_value C (single emb a) ⟨w, hw⟩
      have ib := input_value C (single emb b) ⟨w, hw⟩
      change value C (single emb a) w = _ at ia
      change value C (single emb b) w = _ at ib
      rw [ia] at va
      rw [ib] at vb
      simp only [single, decide_eq_true_eq] at va vb
      exact hemb (va.symm.trans vb)
    omega
  · by_contra! hw
    have hs : supE C emb w = ∅ := by
      ext q
      simp [mem_supE, missing_value C _ w hw]
    simp [hs] at h

lemma count {n M : ℕ} (C : Circuit) (hG : Ok C) (emb : Fin M → Fin n)
    (hemb : Function.Injective emb) (T : Finset (Fin M)) (O : Finset ℕ)
    (hsp : ∀ Y : Finset (Fin M), Disjoint Y T → ∀ o ∈ O, value C (ind emb Y) o = false) :
    (O.biUnion (supE C emb)).card ≤ (assignedE C emb T).card + O.card := by
  classical
  let G := assignedE C emb T
  by_contra! hsmall
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := by
    intro w hw
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B, hd, hBcard, hcut⟩ := cut C hG G hgate (n + C.size) O
    (fun w _ hw => (hgate w hw).2)
  have hb : B.card < (O.biUnion (supE C emb)).card := by
    have hfilter := Finset.card_filter_le G (fun w => w < n + C.size)
    change G.card + O.card < _ at hsmall
    omega
  let clean (w : ℕ) : Finset (Fin M) := if supE C emb w ⊆ T then supE C emb w else ∅
  have hclean : ∀ w ∈ B, (clean w).card ≤ 1 := by
    intro w hw
    by_cases hs : supE C emb w ⊆ T
    · change (if supE C emb w ⊆ T then supE C emb w else ∅).card ≤ 1
      rw [ite_eq_left hs]
      by_contra! hlarge
      exact Finset.disjoint_left.mp hd hw
        (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (supE_gate C emb hemb w (by omega)), hs,
          by omega⟩)
    · simp [clean, hs]
  have hcover : (B.biUnion clean).card < (O.biUnion (supE C emb)).card := by
    have h := Finset.card_biUnion_le_card_mul B clean 1 hclean
    simp only [mul_one] at h
    omega
  obtain ⟨l, hl, hlnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  obtain ⟨o, ho, hlo⟩ := Finset.mem_biUnion.mp hl
  let D := B.filter (fun w => ¬ supE C emb w ⊆ T)
  have hout (w : {w // w ∈ D}) : ∃ q : Fin M, q ∈ supE C emb w.val ∧ q ∉ T := by
    by_contra! h
    exact (Finset.mem_filter.mp w.property).2 h
  choose q hq using hout
  let Y := D.attach.image q
  have hY : Disjoint Y T := by
    rw [Finset.disjoint_left]
    intro r hr hrT
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hr
    exact (hq w).2 hrT
  have hyfalse : value C (ind emb Y) o = false := hsp Y hY o ho
  have hytrue : value C (ind emb Y) o = true := by
    apply hcut (single emb l) (ind emb Y) _ o ho ((mem_supE C emb o l).mp hlo)
    intro w hw hx
    by_cases hs : supE C emb w ⊆ T
    · exact False.elim (hlnot (Finset.mem_biUnion.mpr
        ⟨w, hw, by simpa only [clean, ite_eq_left hs, mem_supE] using hx⟩))
    · let d : {w // w ∈ D} := ⟨w, Finset.mem_filter.mpr ⟨hw, hs⟩⟩
      apply value_mono C hG (single emb (q d)) (ind emb Y) _ w
        ((mem_supE C emb w (q d)).mp (hq d).1)
      intro r hr
      have hm : q d ∈ Y := Finset.mem_image_of_mem q (Finset.mem_attach D d)
      simp only [single, decide_eq_true_eq] at hr
      simp only [ind, decide_eq_true_eq]
      exact ⟨q d, hm, hr⟩
  simp [hyfalse] at hytrue

lemma sum_assigned {n M K : ℕ} (C : Circuit) (emb : Fin M → Fin n) (T : Fin K → Finset (Fin M))
    (hinter : ∀ i j : Fin K, i ≠ j → (T i ∩ T j).card ≤ 1) :
    ∑ i : Fin K, (assignedE C emb (T i)).card ≤ C.size := by
  classical
  let G (i : Fin K) := assignedE C emb (T i)
  have hd : ((Finset.univ : Finset (Fin K)) : Set (Fin K)).PairwiseDisjoint G := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun w hwi hwj => ?_
    have hi := (Finset.mem_filter.mp hwi).2
    have hj := (Finset.mem_filter.mp hwj).2
    have hsub : supE C emb w ⊆ T i ∩ T j := fun p hp => Finset.mem_inter.mpr ⟨hi.1 hp, hj.1 hp⟩
    have hle := Finset.card_le_card hsub
    have hsmall := hinter i j hij
    omega
  calc
    ∑ i : Fin K, (assignedE C emb (T i)).card = (Finset.univ.biUnion G).card :=
      (Finset.card_biUnion hd).symm
    _ ≤ (Finset.Ico n (n + C.size)).card := Finset.card_le_card fun w hw => by
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
      exact (Finset.mem_filter.mp hi).1
    _ = C.size := by simp

-- The plane: witness gates, their stars, and the two sides of the count.

lemma gate_value_j {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    value C x (n + j) = C.gates[j].op.eval
      (C.gates[j].inputs.map fun r => if r < n + j then value C x r else false) := by
  have h := gate_value C x (n + j) (by omega) (by unfold Circuit.size; omega)
  simp only [Nat.add_sub_cancel_left] at h
  exact h

lemma ne_cn (N : ℕ) (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have h2 := congrArg Fin.val h
  have := p.isLt
  simp only [Fin.val_castAdd, Fin.val_natAdd] at h2
  omega

lemma castAdd_inj (N : ℕ) : Function.Injective (Fin.castAdd N : Fin N → Fin (N + N)) := by
  intro a b h
  apply Fin.ext
  have h2 := congrArg Fin.val h
  simp only [Fin.val_castAdd] at h2
  exact h2

lemma natAdd_inj (N : ℕ) : Function.Injective (Fin.natAdd N : Fin N → Fin (N + N)) := by
  intro a b h
  apply Fin.ext
  have h2 := congrArg Fin.val h
  simp only [Fin.val_natAdd] at h2
  omega

def Below (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (j : ℕ) : Prop :=
  ∀ z : Fin (N + N) → Bool, (C.wires (List.ofFn z)).getD (N + N + j) false = true →
    ∃ p0 l0 : Fin N, I p0 l0 ∧ z (Fin.castAdd N p0) = true ∧ z (Fin.natAdd N l0) = true

def Wit (C : Circuit) (N : ℕ) (I : Fin N → Fin N → Prop) (j a c : ℕ) : Prop :=
  j < C.gates.length ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.and ∧
    ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [a, c] ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [c, a]) ∧
    Below C N I j

lemma wit_and {N : ℕ} {I : Fin N → Fin N → Prop} (C : Circuit)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C)
    {j a c : ℕ} (hw : Wit C N I j a c) (z : Fin (N + N) → Bool)
    (ha : value C z a = true) (hc : value C z c = true) : value C z (N + N + j) = true := by
  obtain ⟨hj, hop, hin, -⟩ := hw
  have hra : a < N + N + j := hR j hj a (by rcases hin with h | h <;> simp [h])
  have hrc : c < N + N + j := hR j hj c (by rcases hin with h | h <;> simp [h])
  have hgA : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    exact List.getD_eq_getElem _ _ hj
  rw [hgA] at hop hin
  rw [gate_value_j C z j hj, hop]
  rcases hin with h | h <;> simp [h, GateOp.eval, hra, hrc, ha, hc]

lemma wit_below {N : ℕ} {I : Fin N → Fin N → Prop} (C : Circuit)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C)
    {j a c : ℕ} (hw : Wit C N I j a c) (z : Fin (N + N) → Bool)
    (ha : value C z a = true) (hc : value C z c = true) :
    ∃ p0 l0 : Fin N, I p0 l0 ∧ z (Fin.castAdd N p0) = true ∧ z (Fin.natAdd N l0) = true :=
  hw.2.2.2 z (wit_and C hR hw z ha hc)

lemma orient {N : ℕ} {I : Fin N → Fin N → Prop} {C : Circuit} {j a c a' c' : ℕ}
    (hw : Wit C N I j a c) (hw' : Wit C N I j a' c') :
    (a = a' ∧ c = c') ∨ (a = c' ∧ c = a') := by
  rcases hw.2.2.1 with h | h <;> rcases hw'.2.2.1 with h' | h' <;> rw [h] at h' <;>
    simp only [List.cons.injEq, and_true] at h' <;> omega

lemma rect {N : ℕ} {I : Fin N → Fin N → Prop} (C : Circuit) (hG : Ok C)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C)
    {j a c : ℕ} (hw : Wit C N I j a c) {p l : Fin N}
    (hp : p ∈ supE C (Fin.castAdd N : Fin N → Fin (N + N)) a) (hl : l ∈ supE C (Fin.natAdd N : Fin N → Fin (N + N)) c) : I p l := by
  let z : Fin (N + N) → Bool := fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)
  have ha : value C z a = true := by
    apply value_mono C hG (single (Fin.castAdd N) p) z _ a ((mem_supE C _ a p).mp hp)
    intro k hk
    simp only [single, decide_eq_true_eq] at hk
    simp [z, hk]
  have hc : value C z c = true := by
    apply value_mono C hG (single (Fin.natAdd N) l) z _ c ((mem_supE C _ c l).mp hl)
    intro k hk
    simp only [single, decide_eq_true_eq] at hk
    simp [z, hk]
  obtain ⟨p0, l0, hi, h1, h2⟩ := wit_below C hR hw z ha hc
  simp only [z, decide_eq_true_eq] at h1 h2
  have e1 : p0 = p := by
    rcases h1 with h | h
    · exact castAdd_inj N h
    · exact absurd h (ne_cn N p0 l)
  have e2 : l0 = l := by
    rcases h2 with h | h
    · exact absurd h.symm (ne_cn N p l0)
    · exact natAdd_inj N h
  subst e1 e2
  exact hi

lemma two_points {N : ℕ} {I : Fin N → Fin N → Prop} (C : Circuit) (hG : Ok C)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C)
    {j a c : ℕ} (hw : Wit C N I j a c) {p1 p2 : Fin N}
    (h1 : p1 ∈ supE C (Fin.castAdd N : Fin N → Fin (N + N)) a) (h2 : p2 ∈ supE C (Fin.castAdd N : Fin N → Fin (N + N)) c) : False := by
  let z : Fin (N + N) → Bool := fun k => decide (k = Fin.castAdd N p1 ∨ k = Fin.castAdd N p2)
  have ha : value C z a = true := by
    apply value_mono C hG (single (Fin.castAdd N) p1) z _ a ((mem_supE C _ a p1).mp h1)
    intro k hk
    simp only [single, decide_eq_true_eq] at hk
    simp [z, hk]
  have hc : value C z c = true := by
    apply value_mono C hG (single (Fin.castAdd N) p2) z _ c ((mem_supE C _ c p2).mp h2)
    intro k hk
    simp only [single, decide_eq_true_eq] at hk
    simp [z, hk]
  obtain ⟨p0, l0, -, -, hl⟩ := wit_below C hR hw z ha hc
  simp only [z, decide_eq_true_eq] at hl
  rcases hl with h | h
  · exact ne_cn N p1 l0 h.symm
  · exact ne_cn N p2 l0 h.symm

lemma sparse1 {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] (C : Circuit) (hG : Ok C)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C)
    {j a c : ℕ} (hw : Wit C N I j a c) {p : Fin N} (hp : p ∈ supE C (Fin.castAdd N : Fin N → Fin (N + N)) a)
    (Y : Finset (Fin N)) (hY : Disjoint Y (Finset.univ.filter (fun l => I p l))) :
    value C (ind (Fin.natAdd N) Y) c = false := by
  by_contra hne
  have hc0 : value C (ind (Fin.natAdd N) Y) c = true := by simpa using hne
  let z : Fin (N + N) → Bool :=
    fun k => decide (k = Fin.castAdd N p ∨ ∃ l ∈ Y, k = Fin.natAdd N l)
  have ha : value C z a = true := by
    apply value_mono C hG (single (Fin.castAdd N) p) z _ a ((mem_supE C _ a p).mp hp)
    intro k hk
    simp only [single, decide_eq_true_eq] at hk
    simp [z, hk]
  have hc : value C z c = true := by
    apply value_mono C hG (ind (Fin.natAdd N) Y) z _ c hc0
    intro k hk
    simp only [ind, decide_eq_true_eq] at hk
    simp only [z, decide_eq_true_eq]
    exact Or.inr hk
  obtain ⟨p0, l0, hi, h1, h2⟩ := wit_below C hR hw z ha hc
  simp only [z, decide_eq_true_eq] at h1 h2
  have e1 : p0 = p := by
    rcases h1 with h | ⟨l, -, h⟩
    · exact castAdd_inj N h
    · exact absurd h (ne_cn N p0 l)
  subst e1
  have hl0 : l0 ∈ Y := by
    rcases h2 with h | ⟨l, hl, h⟩
    · exact absurd h.symm (ne_cn N p0 l0)
    · exact (natAdd_inj N h) ▸ hl
  exact Finset.disjoint_left.mp hY hl0 (by simp [hi])

lemma sparse2 {N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I] (C : Circuit) (hG : Ok C)
    (hR : PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C)
    {j a c : ℕ} (hw : Wit C N I j a c) {l : Fin N} (hl : l ∈ supE C (Fin.natAdd N : Fin N → Fin (N + N)) c)
    (X : Finset (Fin N)) (hX : Disjoint X (Finset.univ.filter (fun p => I p l))) :
    value C (ind (Fin.castAdd N) X) a = false := by
  by_contra hne
  have ha0 : value C (ind (Fin.castAdd N) X) a = true := by simpa using hne
  let z : Fin (N + N) → Bool :=
    fun k => decide ((∃ p ∈ X, k = Fin.castAdd N p) ∨ k = Fin.natAdd N l)
  have ha : value C z a = true := by
    apply value_mono C hG (ind (Fin.castAdd N) X) z _ a ha0
    intro k hk
    simp only [ind, decide_eq_true_eq] at hk
    simp only [z, decide_eq_true_eq]
    exact Or.inl hk
  have hc : value C z c = true := by
    apply value_mono C hG (single (Fin.natAdd N) l) z _ c ((mem_supE C _ c l).mp hl)
    intro k hk
    simp only [single, decide_eq_true_eq] at hk
    simp [z, hk]
  obtain ⟨p0, l0, hi, h1, h2⟩ := wit_below C hR hw z ha hc
  simp only [z, decide_eq_true_eq] at h1 h2
  have e2 : l0 = l := by
    rcases h2 with ⟨p, -, h⟩ | h
    · exact absurd h.symm (ne_cn N p l0)
    · exact natAdd_inj N h
  subst e2
  have hp0 : p0 ∈ X := by
    rcases h1 with ⟨p, hp, h⟩ | h
    · exact (castAdd_inj N h) ▸ hp
    · exact absurd h (ne_cn N p0 l0)
  exact Finset.disjoint_left.mp hX hp0 (by simp [hi])

end PEqualNP.Outside.L_meta_2838

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2838 in
theorem PEqualNP.Outside.L_meta_2838 : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) → (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q → (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) → {e : Fin N × Fin N | I e.1 e.2 ∧ ∃ j < C.gates.length, ∃ a c : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [a, c] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [c, a]) ∧ (∀ z : Fin (N + N) → Bool, (C.wires (List.ofFn z)).getD (N + N + j) false = true → ∃ p0 l0 : Fin N, I p0 l0 ∧ z (Fin.castAdd N p0) = true ∧ z (Fin.natAdd N l0) = true) ∧ (C.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.castAdd N e.1)))).getD a false = true ∧ (C.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.natAdd N e.2)))).getD c false = true}.ncard ≤ 3 * C.size + 2 * N := by
  classical
  intro q N I _ C _ _ _ huniq hmono hreads _ _
  have hG : Ok C := by
    intro g hg
    obtain ⟨h1, h2⟩ := hmono g hg
    exact ⟨by simpa using h1, h2⟩
  let T1 : Fin N → Finset (Fin N) := fun p => Finset.univ.filter (fun l => I p l)
  let T2 : Fin N → Finset (Fin N) := fun l => Finset.univ.filter (fun p => I p l)
  let R := Finset.range (N + N + C.gates.length)
  let O1 : Fin N → Finset ℕ := fun p => R.filter (fun c =>
    ∃ j a, Wit C N I j a c ∧ supE C (Fin.castAdd N : Fin N → Fin (N + N)) a = {p})
  let A2 : Fin N → Finset ℕ := fun l => R.filter (fun a =>
    ∃ j c, Wit C N I j a c ∧ 2 ≤ (supE C (Fin.castAdd N : Fin N → Fin (N + N)) a).card ∧
      supE C (Fin.natAdd N : Fin N → Fin (N + N)) c = {l})
  let U1 : Fin N → Finset (Fin N) := fun p => (O1 p).biUnion (supE C (Fin.natAdd N : Fin N → Fin (N + N)))
  let V2 : Fin N → Finset (Fin N) := fun l => (A2 l).biUnion (supE C (Fin.castAdd N : Fin N → Fin (N + N)))
  let K1 := (Finset.range C.gates.length).filter (fun j =>
    ∃ a c p, Wit C N I j a c ∧ supE C (Fin.castAdd N : Fin N → Fin (N + N)) a = {p})
  let K2 := (Finset.range C.gates.length).filter (fun j =>
    ∃ a c l, Wit C N I j a c ∧ 2 ≤ (supE C (Fin.castAdd N : Fin N → Fin (N + N)) a).card ∧
      supE C (Fin.natAdd N : Fin N → Fin (N + N)) c = {l})
  let E1 : Finset (Fin N × Fin N) := Finset.univ.biUnion (fun p => (U1 p).image (fun l => (p, l)))
  let E2 : Finset (Fin N × Fin N) := Finset.univ.biUnion (fun l => (V2 l).image (fun p => (p, l)))
  have hU1 : ∀ p, (U1 p).card ≤ (assignedE C (Fin.natAdd N : Fin N → Fin (N + N)) (T1 p)).card + (O1 p).card := by
    intro p
    apply count C hG (Fin.natAdd N) (natAdd_inj N) (T1 p) (O1 p)
    intro Y hY o ho
    obtain ⟨-, j, a, hw, hs⟩ := Finset.mem_filter.mp ho
    exact sparse1 C hG hreads hw (hs ▸ Finset.mem_singleton_self p) Y hY
  have hV2 : ∀ l, (V2 l).card ≤ (assignedE C (Fin.castAdd N : Fin N → Fin (N + N)) (T2 l)).card + (A2 l).card := by
    intro l
    apply count C hG (Fin.castAdd N) (castAdd_inj N) (T2 l) (A2 l)
    intro X hX o ho
    obtain ⟨-, j, c, hw, -, hs⟩ := Finset.mem_filter.mp ho
    exact sparse2 C hG hreads hw (hs ▸ Finset.mem_singleton_self l) X hX
  have hI1 : ∀ p p' : Fin N, p ≠ p' → (T1 p ∩ T1 p').card ≤ 1 := by
    intro p p' hne
    rw [Finset.card_le_one]
    intro x hx y hy
    simp only [T1, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    obtain ⟨l0, -, huq⟩ := huniq p p' hne
    exact (huq x hx).trans (huq y hy).symm
  have hI2 : ∀ l l' : Fin N, l ≠ l' → (T2 l ∩ T2 l').card ≤ 1 := by
    intro l l' hne
    rw [Finset.card_le_one]
    intro x hx y hy
    simp only [T2, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    by_contra hxy
    obtain ⟨l0, -, huq⟩ := huniq x y hxy
    exact hne ((huq l ⟨hx.1, hy.1⟩).trans (huq l' ⟨hx.2, hy.2⟩).symm)
  have hS1 := sum_assigned C (Fin.natAdd N) T1 hI1
  have hS2 := sum_assigned C (Fin.castAdd N) T2 hI2
  have hO1 : ∑ p, (O1 p).card ≤ K1.card := by
    rw [← Finset.card_sigma]
    apply Finset.card_le_card_of_forall_subsingleton
      (fun (x : (_ : Fin N) × ℕ) (j : ℕ) =>
        ∃ a, Wit C N I j a x.2 ∧ supE C (Fin.castAdd N : Fin N → Fin (N + N)) a = {x.1})
    · rintro ⟨p, c⟩ hx
      obtain ⟨-, hc⟩ := Finset.mem_sigma.mp hx
      obtain ⟨-, j, a, hw, hs⟩ := Finset.mem_filter.mp hc
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hw.1, a, c, p, hw, hs⟩, a, hw, hs⟩
    · intro j _ x hx y hy
      obtain ⟨-, a, hw, hs⟩ := hx
      obtain ⟨-, a', hw', hs'⟩ := hy
      obtain ⟨p, c⟩ := x
      obtain ⟨p', c'⟩ := y
      rcases orient hw hw' with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · subst e1 e2
        rw [hs] at hs'
        have := Finset.singleton_inj.mp hs'
        subst this
        rfl
      · exfalso
        subst e1 e2
        exact two_points C hG hreads hw (hs ▸ Finset.mem_singleton_self p)
          (hs' ▸ Finset.mem_singleton_self p')
  have hA2 : ∑ l, (A2 l).card ≤ K2.card := by
    rw [← Finset.card_sigma]
    apply Finset.card_le_card_of_forall_subsingleton
      (fun (x : (_ : Fin N) × ℕ) (j : ℕ) =>
        ∃ c, Wit C N I j x.2 c ∧ 2 ≤ (supE C (Fin.castAdd N : Fin N → Fin (N + N)) x.2).card ∧
          supE C (Fin.natAdd N : Fin N → Fin (N + N)) c = {x.1})
    · rintro ⟨l, a⟩ hx
      obtain ⟨-, ha⟩ := Finset.mem_sigma.mp hx
      obtain ⟨-, j, c, hw, h2, hs⟩ := Finset.mem_filter.mp ha
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hw.1, a, c, l, hw, h2, hs⟩,
        c, hw, h2, hs⟩
    · intro j _ x hx y hy
      obtain ⟨-, c, hw, h2, hs⟩ := hx
      obtain ⟨-, c', hw', h2', hs'⟩ := hy
      obtain ⟨l, a⟩ := x
      obtain ⟨l', a'⟩ := y
      rcases orient hw hw' with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · subst e1 e2
        rw [hs] at hs'
        have := Finset.singleton_inj.mp hs'
        subst this
        rfl
      · exfalso
        subst e1 e2
        obtain ⟨p1, hp1⟩ := Finset.card_pos.mp (lt_of_lt_of_le two_pos h2)
        obtain ⟨p2, hp2⟩ := Finset.card_pos.mp (lt_of_lt_of_le two_pos h2')
        exact two_points C hG hreads hw hp1 hp2
  have hK : K1.card + K2.card ≤ C.size := by
    have hdis : K1 ∩ K2 = ∅ := by
      ext j
      simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
      intro h1 h2
      obtain ⟨-, a, c, p, hw, hs⟩ := Finset.mem_filter.mp h1
      obtain ⟨-, a', c', l, hw', h2', -⟩ := Finset.mem_filter.mp h2
      rcases orient hw hw' with ⟨e1, -⟩ | ⟨-, e2⟩
      · subst e1
        rw [hs] at h2'
        simp at h2'
      · subst e2
        obtain ⟨p2, hp2⟩ := Finset.card_pos.mp (by omega : 0 < (supE C (Fin.castAdd N : Fin N → Fin (N + N)) c).card)
        exact two_points C hG hreads hw (hs ▸ Finset.mem_singleton_self p) hp2
    have hu := Finset.card_union_add_card_inter K1 K2
    rw [hdis, Finset.card_empty] at hu
    have hsub : K1 ∪ K2 ⊆ Finset.range C.gates.length :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have := Finset.card_le_card hsub
    simp only [Finset.card_range] at this
    unfold Circuit.size
    omega
  have hE : {e : Fin N × Fin N | I e.1 e.2 ∧ ∃ j < C.gates.length, ∃ a c : ℕ,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.and ∧
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [a, c] ∨
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [c, a]) ∧
      (∀ z : Fin (N + N) → Bool, (C.wires (List.ofFn z)).getD (N + N + j) false = true →
        ∃ p0 l0 : Fin N, I p0 l0 ∧ z (Fin.castAdd N p0) = true ∧
          z (Fin.natAdd N l0) = true) ∧
      (C.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.castAdd N e.1)))).getD a
        false = true ∧
      (C.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.natAdd N e.2)))).getD c
        false = true} ⊆ ((E1 ∪ E2 : Finset (Fin N × Fin N)) : Set (Fin N × Fin N)) := by
    rintro ⟨p, l⟩ ⟨-, j, hj, a, c, hop, hin, hbelow, ha, hc⟩
    have hw : Wit C N I j a c := ⟨hj, hop, hin, hbelow⟩
    have hp : p ∈ supE C (Fin.castAdd N : Fin N → Fin (N + N)) a := (mem_supE C _ a p).mpr ha
    have hl : l ∈ supE C (Fin.natAdd N : Fin N → Fin (N + N)) c := (mem_supE C _ c l).mpr hc
    have hra : a < N + N + j := hreads j hj a (by rcases hin with h | h <;> simp [h])
    have hrc : c < N + N + j := hreads j hj c (by rcases hin with h | h <;> simp [h])
    rw [Finset.coe_union, Set.mem_union]
    by_cases h1 : (supE C (Fin.castAdd N : Fin N → Fin (N + N)) a).card ≤ 1
    · have hs : supE C (Fin.castAdd N : Fin N → Fin (N + N)) a = {p} :=
        Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hp, fun x hx => Finset.card_le_one.mp h1 x hx p hp⟩
      left
      simp only [Finset.mem_coe, E1, Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_image, Prod.mk.injEq]
      refine ⟨p, l, ?_, rfl, rfl⟩
      exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), j, a, hw, hs⟩, hl⟩
    · push Not at h1
      have hs : supE C (Fin.natAdd N : Fin N → Fin (N + N)) c = {l} := by
        refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hl, fun l' hl' => ?_⟩
        obtain ⟨p1, p2, hp1, hp2, hne⟩ := Finset.one_lt_card_iff.mp h1
        obtain ⟨l0, -, huq⟩ := huniq p1 p2 hne
        exact (huq l' ⟨rect C hG hreads hw hp1 hl', rect C hG hreads hw hp2 hl'⟩).trans
          (huq l ⟨rect C hG hreads hw hp1 hl, rect C hG hreads hw hp2 hl⟩).symm
      right
      simp only [Finset.mem_coe, E2, Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_image, Prod.mk.injEq]
      refine ⟨l, p, ?_, rfl, rfl⟩
      exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), j, c, hw, h1, hs⟩, hp⟩
  have hE1 : E1.card ≤ ∑ p, (U1 p).card :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun p _ => Finset.card_image_le)
  have hE2 : E2.card ≤ ∑ l, (V2 l).card :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun l _ => Finset.card_image_le)
  have hsU : ∑ p, (U1 p).card ≤
      ∑ p, (assignedE C (Fin.natAdd N : Fin N → Fin (N + N)) (T1 p)).card + ∑ p, (O1 p).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun p _ => hU1 p
  have hsV : ∑ l, (V2 l).card ≤
      ∑ l, (assignedE C (Fin.castAdd N : Fin N → Fin (N + N)) (T2 l)).card + ∑ l, (A2 l).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun l _ => hV2 l
  have hcard := Set.ncard_le_ncard hE (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at hcard
  have hun := Finset.card_union_le E1 E2
  omega
