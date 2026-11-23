import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.GetD
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Group.Fin.Basic
import PEqualNP.Defs

-- Adapted from the project's few-NOT helpers and L-meta-900, L-meta-924 and L-meta-1049.
-- The counting proof in L-meta-900 credits k-sandhu, PR 149.
namespace PEqualNP.Outside.L_meta_1325

open PEqualNP.CircuitLowerBounds

namespace Part270

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

end Part270

open Part270 in
theorem promise :
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

namespace Part669

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

end Part669

theorem restrict : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) :=
  Part669.main_aux

namespace OneNot

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by simp

theorem on1_wires_append (l1 l2 : List Gate) (o o' : ℕ) (x : List Bool) :
    Circuit.wires ⟨l1 ++ l2, o⟩ x = wiresFrom l2 (Circuit.wires ⟨l1, o'⟩ x) :=
  wiresFrom_append l1 l2 x

theorem on1_wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w
      = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem on1_getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

def on1_Above (v v' : List Bool) : Prop :=
  v.length = v'.length ∧ ∀ i, v.getD i false = true → v'.getD i false = true

theorem on1_above_snoc {v v' : List Bool} {a a' : Bool} (h : on1_Above v v')
    (ha : a = true → a' = true) : on1_Above (v ++ [a]) (v' ++ [a']) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  by_cases hiv : i = v.length
  · subst hiv
    rw [getD_snoc_eq] at hi
    rw [h.1, getD_snoc_eq]; exact ha hi
  · rw [getD_snoc_ne _ _ _ _ hiv] at hi
    rw [getD_snoc_ne _ _ _ _ (by rw [← h.1]; exact hiv)]
    exact h.2 i hi

theorem on1_above_wiresFrom (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ v v' : List Bool, on1_Above v v' → on1_Above (wiresFrom gs v) (wiresFrom gs v') := by
  induction gs with
  | nil => intro v v' h; exact h
  | cons g gs ih =>
    intro v v' h
    rw [on1_wiresFrom_cons, on1_wiresFrom_cons]
    apply ih (fun g' hg' => hgs g' (by simp [hg']))
    apply on1_above_snoc h
    rcases hgs g (by simp) with hop | hop
    · rw [hop]
      simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
      intro hall b hb
      obtain ⟨j, hj, rfl⟩ := hb
      exact h.2 j (hall _ ⟨j, hj, rfl⟩)
    · rw [hop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
      rintro ⟨b, ⟨j, hj, rfl⟩, hb⟩
      exact ⟨_, ⟨j, hj, rfl⟩, h.2 j hb⟩

theorem on1_piece_h : ∀ (n : ℕ) (pre : List PEqualNP.CircuitLowerBounds.Gate) (ins : List ℕ),
    (∀ g ∈ pre, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) →
      ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
          (List.ofFn x)).getD i false).headD false) = true →
      ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
          (List.ofFn y)).getD i false).headD false) = true := by
  intro n pre ins hpre x y hxy
  have hab : on1_Above (wiresFrom pre (List.ofFn x)) (wiresFrom pre (List.ofFn y)) := by
    apply on1_above_wiresFrom pre (fun g hg => (hpre g hg).1)
    refine ⟨by simp, ?_⟩
    intro i hi
    by_cases hin : i < n
    · rw [on1_getD_ofFn _ _ hin] at hi ⊢; exact hxy _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; exact absurd hi (by simp)
  cases ins with
  | nil => simp
  | cons j _ =>
    simp only [List.map_cons, List.headD_cons]
    exact hab.2 j

theorem on1_wires_slot (pre post : List Gate) (g g' : Gate) (o o' : ℕ) (x : List Bool)
    (h : g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨pre, 0⟩ x).getD i false)
      = g'.op.eval (g'.inputs.map fun i => (Circuit.wires ⟨pre, 0⟩ x).getD i false)) :
    Circuit.wires ⟨pre ++ g :: post, o⟩ x = Circuit.wires ⟨pre ++ g' :: post, o'⟩ x := by
  rw [on1_wires_append _ _ o 0, on1_wires_append _ _ o' 0, on1_wiresFrom_cons,
    on1_wiresFrom_cons, h]

theorem on1_piece_d : ∀ (n : ℕ) (pre post : List PEqualNP.CircuitLowerBounds.Gate)
    (ins : List ℕ) (o : ℕ) (x : Fin n → Bool),
    ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
        (List.ofFn x)).getD i false).headD false) = false →
    PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [] } :
          PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x)
      = PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
          PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x) := by
  intro n pre post ins o x h
  unfold Circuit.eval
  rw [on1_wires_slot pre post _ _ o o (List.ofFn x)]
  simp only [GateOp.eval, List.map_nil, List.all_nil]
  rw [h]; rfl

theorem on1_piece_u_cheap : ∀ (n : ℕ) (pre post : List PEqualNP.CircuitLowerBounds.Gate)
    (ins : List ℕ) (o : ℕ) (x : Fin n → Bool),
    ((ins.map fun i => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨pre, 0⟩
        (List.ofFn x)).getD i false).headD false) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] } :
          PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x)
      = PEqualNP.CircuitLowerBounds.Circuit.eval
        ⟨pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
          PEqualNP.CircuitLowerBounds.Gate) :: post, o⟩ (List.ofFn x) := by
  intro n pre post ins o x h
  unfold Circuit.eval
  rw [on1_wires_slot pre post _ _ o o (List.ofFn x)]
  simp only [GateOp.eval, List.map_nil, List.any_nil]
  rw [h]; rfl

end OneNot

theorem fn_foldr_max_le {f : ℕ → ℕ} {r c : ℕ} (h : ∀ j ∈ List.range r, f j ≤ c) :
    (List.range r).foldr (fun (j acc : ℕ) => max acc (f j)) 0 ≤ c := by
  suffices H : ∀ l : List ℕ, (∀ j ∈ l, f j ≤ c) →
      l.foldr (fun (j acc : ℕ) => max acc (f j)) 0 ≤ c from H _ h
  intro l hl
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (ih fun j hj => hl j (List.mem_cons_of_mem a hj)) (hl a List.mem_cons_self)

def H270 : Prop :=
  ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size

def H669 : Prop :=
  ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))

def PSub : Prop :=
  ∀ (n m q : ℕ) (S : Fin m → Finset (Fin n)) (y : Finset (Fin n)), (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∃ (m' : ℕ) (e : Fin m' → Fin m), m' = (Finset.univ.filter (fun w : Fin m => Disjoint (S w) y)).card ∧ Function.Injective e ∧ (∀ w : Fin m, Disjoint (S w) y ↔ ∃ i : Fin m', e i = w) ∧ (∀ i : Fin m', (S (e i)).card = q + 1) ∧ (∀ i j : Fin m', i ≠ j → (S (e i) ∩ S (e j)).card ≤ 1)

def PSplit : Prop :=
  ∀ (s : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s, ι j = i) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∨ ∃ (s' : ℕ) (pre post : List PEqualNP.CircuitLowerBounds.Gate) (ins : List ℕ), s = s' + 1 ∧ gates = pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } : PEqualNP.CircuitLowerBounds.Gate) :: post ∧ ins.length ≤ 2 ∧ (∀ g ∈ pre, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ ∀ g' : PEqualNP.CircuitLowerBounds.Gate, (g'.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g'.op = PEqualNP.CircuitLowerBounds.GateOp.or) → g'.inputs.length ≤ 2 → (∀ g ∈ pre ++ g' :: post, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧ ∃ ι' : Fin s' → Fin (pre ++ g' :: post).length, ∀ i : Fin (pre ++ g' :: post).length, ((pre ++ g' :: post).get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s', ι' j = i

def OpsOK (gates : List Gate) : Prop :=
  ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2

def AndOr2 (gates : List Gate) : Prop :=
  ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def NotAtMost (s : ℕ) (gates : List Gate) : Prop :=
  ∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length,
    (gates.get i).op = GateOp.not → ∃ j : Fin s, ι j = i

def Win {n : ℕ} (y : Finset (Fin n)) (K : ℕ) (x : Fin n → Bool) : Prop :=
  (∀ p ∈ y, x p = true) ∧ (Finset.univ.filter (fun p : Fin n => x p = true ∧ p ∉ y)).card ≤ K

def Right {n m : ℕ} (S : Fin m → Finset (Fin n)) (y : Finset (Fin n)) (K : ℕ)
    (gates : List Gate) (out : Fin m → ℕ) : Prop :=
  ∀ (w : Fin m) (x : Fin n → Bool), Disjoint (S w) y → (∀ p ∈ y, x p = true) →
    (Finset.univ.filter (fun p : Fin n => x p = true ∧ p ∉ y)).card ≤ K →
    Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)

def fewNotGenG (m d : ℕ) (kappa : ℕ → ℕ) (s b K : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ)
    (fun b' K' : ℕ => (m - kappa b') * min K' (d - 1))
    (fun _ (g : ℕ → ℕ → ℕ) (b' K' : ℕ) =>
      (List.range (K' + 1)).foldr
        (fun (j acc : ℕ) => max acc (min (g (b' + j) (K' - j)) (g b' j))) 0)
    s b K

theorem fnp_genG_zero (m d : ℕ) (kappa : ℕ → ℕ) (b K : ℕ) :
    fewNotGenG m d kappa 0 b K = (m - kappa b) * min K (d - 1) := rfl

theorem fnp_genG_succ (m d : ℕ) (kappa : ℕ → ℕ) (s b K : ℕ) :
    fewNotGenG m d kappa (s + 1) b K = (List.range (K + 1)).foldr
      (fun (j acc : ℕ) => max acc (min (fewNotGenG m d kappa s (b + j) (K - j))
        (fewNotGenG m d kappa s b j))) 0 := rfl

def FamG (n m d : ℕ) (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ) : Prop :=
  (∀ i : Fin m, (S i).card = d) ∧
  (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) ∧
  (∀ (b : ℕ) (y : Finset (Fin n)), y.card ≤ b →
    (Finset.univ.filter (fun w : Fin m => ¬ Disjoint (S w) y)).card ≤ kappa b)

def ClaimG (n m d : ℕ) (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ) (s : ℕ) : Prop :=
  ∀ (b K : ℕ) (y : Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ), y.card ≤ b →
    OpsOK gates → NotAtMost s gates → Right S y K gates out →
    fewNotGenG m d kappa s b K ≤ gates.length

def BoundG : Prop :=
  ∀ (n m d : ℕ) (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ), FamG n m d S kappa →
    ∀ s : ℕ, ClaimG n m d S kappa s

def PSplitS : Prop :=
  ∀ (gates : List Gate) (s : ℕ), OpsOK gates → NotAtMost (s + 1) gates →
    NotAtMost s gates ∨
    ∃ (pre post : List Gate) (ins : List ℕ),
      gates = pre ++ ({ op := GateOp.not, inputs := ins } : Gate) :: post ∧ AndOr2 pre ∧
      OpsOK (pre ++ ({ op := GateOp.and, inputs := [] } : Gate) :: post) ∧
      OpsOK (pre ++ ({ op := GateOp.or, inputs := [] } : Gate) :: post) ∧
      NotAtMost s (pre ++ ({ op := GateOp.and, inputs := [] } : Gate) :: post) ∧
      NotAtMost s (pre ++ ({ op := GateOp.or, inputs := [] } : Gate) :: post)

theorem fnp_splitS (h : PSplit) : PSplitS := by
  intro gates s hops hnot
  rcases h (s + 1) gates hops hnot with hno | ⟨s', pre, post, ins, hs, heq, _, hpre, hvar⟩
  · left
    obtain ⟨ι, _⟩ := hnot
    refine ⟨fun _ => ι 0, fun i hi => ?_⟩
    rcases (hno _ (List.get_mem gates i)).1 with h' | h' <;> rw [h'] at hi <;> cases hi
  · obtain rfl : s' = s := by omega
    right
    have ha := hvar { op := GateOp.and, inputs := [] } (Or.inl rfl) (by simp)
    have ho := hvar { op := GateOp.or, inputs := [] } (Or.inr rfl) (by simp)
    exact ⟨pre, post, ins, heq, hpre, ha.1, ho.1, ha.2, ho.2⟩

def H669at : Prop :=
  ∀ (n : ℕ) (gates : List Gate) (y : Finset (Fin n)), AndOr2 gates →
    ∃ (gates' : List Gate) (r : ℕ → ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
      gates'.length ≤ gates.length ∧ ∀ o : ℕ,
      (∃ x x' : Fin n → Bool,
        Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ y then true else
          if i ∈ (∅ : Finset (Fin n)) then false else x i)) ≠
        Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ y then true else
          if i ∈ (∅ : Finset (Fin n)) then false else x' i))) →
      ∀ x : Fin n → Bool, Circuit.eval ⟨gates', r o⟩ (List.ofFn x) =
        Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ y then true else
          if i ∈ (∅ : Finset (Fin n)) then false else x i))

theorem fnp_669_at (h : H669) : H669at := fun n gates y hg => h n gates y ∅ hg

def PBaseG : Prop :=
  H270 → H669at → PSub → ∀ (n m d : ℕ) (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ),
    FamG n m d S kappa → ClaimG n m d S kappa 0

def PStepG : Prop :=
  PSplitS → ∀ (n m d : ℕ) (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ),
    FamG n m d S kappa → ∀ s : ℕ, ClaimG n m d S kappa s → ClaimG n m d S kappa (s + 1)

theorem fnp_assemblyG (hS : PSub) (hSp : PSplit) (hB : PBaseG) (hSt : PStepG) :
    H270 → H669 → BoundG := by
  intro h270 h669 n m d S kappa hF s
  induction s with
  | zero => exact hB h270 (fnp_669_at h669) hS n m d S kappa hF
  | succ s ih => exact hSt (fnp_splitS hSp) n m d S kappa hF s ih

theorem fnp_variant_length (pre post : List Gate) (g g' : Gate) :
    (pre ++ g :: post).length = (pre ++ g' :: post).length := by simp

theorem fn_split_getElem?_ne (pre post : List Gate) (a b : Gate) (i : ℕ)
    (hi : i ≠ pre.length) : (pre ++ b :: post)[i]? = (pre ++ a :: post)[i]? := by
  rcases Nat.lt_or_gt_of_ne hi with h | h
  · rw [List.getElem?_append_left h, List.getElem?_append_left h]
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    obtain ⟨k, hk⟩ : ∃ k, i - pre.length = k + 1 := ⟨i - pre.length - 1, by omega⟩
    rw [hk, List.getElem?_cons_succ, List.getElem?_cons_succ]

theorem fn_split_count (t : ℕ) (pre post : List Gate) (a b : Gate)
    (hb : b.op ≠ GateOp.not)
    (ι : Fin (t + 1) → Fin (pre ++ a :: post).length)
    (hι : ∀ i : Fin (pre ++ a :: post).length, ((pre ++ a :: post).get i).op = GateOp.not →
      ∃ j : Fin (t + 1), ι j = i)
    (j0 : Fin (t + 1)) (hj0 : (ι j0).val = pre.length) :
    ∃ ι' : Fin t → Fin (pre ++ b :: post).length,
      ∀ i : Fin (pre ++ b :: post).length, ((pre ++ b :: post).get i).op = GateOp.not →
        ∃ j : Fin t, ι' j = i := by
  have hlen : (pre ++ b :: post).length = (pre ++ a :: post).length := by simp
  refine ⟨fun j => ⟨(ι (j0.succAbove j)).val, by have := (ι (j0.succAbove j)).isLt; omega⟩, ?_⟩
  intro i hi
  have hne : i.val ≠ pre.length := by
    intro h
    apply hb
    have : (pre ++ b :: post).get i = b := by
      simp only [List.get_eq_getElem, h, List.getElem_append_right (Nat.le_refl _),
        Nat.sub_self, List.getElem_cons_zero]
    rw [← this]; exact hi
  have hget : (pre ++ a :: post).get ⟨i.val, by have := i.isLt; omega⟩ = (pre ++ b :: post).get i := by
    have := fn_split_getElem?_ne pre post a b i.val hne
    simp only [List.get_eq_getElem]
    rw [List.getElem?_eq_getElem i.isLt, List.getElem?_eq_getElem (by have := i.isLt; omega)] at this
    exact (Option.some.inj this).symm
  obtain ⟨j, hj⟩ := hι ⟨i.val, by have := i.isLt; omega⟩ (by rw [hget]; exact hi)
  have hjne : j ≠ j0 := by
    rintro rfl
    apply hne
    rw [← hj0, hj]
  obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hjne
  refine ⟨j', ?_⟩
  apply Fin.ext
  simp only [hj]

theorem fn_split_general : ∀ (s : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
    (∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length,
        (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s, ι j = i) →
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∨
    ∃ (s' : ℕ) (pre post : List PEqualNP.CircuitLowerBounds.Gate) (ins : List ℕ),
      s = s' + 1 ∧
      gates = pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
        PEqualNP.CircuitLowerBounds.Gate) :: post ∧
      ins.length ≤ 2 ∧
      (∀ g ∈ pre, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      ∀ g' : PEqualNP.CircuitLowerBounds.Gate,
        (g'.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          g'.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        g'.inputs.length ≤ 2 →
        (∀ g ∈ pre ++ g' :: post, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
            g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧
        ∃ ι' : Fin s' → Fin (pre ++ g' :: post).length,
          ∀ i : Fin (pre ++ g' :: post).length,
            ((pre ++ g' :: post).get i).op = PEqualNP.CircuitLowerBounds.GateOp.not →
            ∃ j : Fin s', ι' j = i := by
  intro s gates hops hcnt
  by_cases hex : ∃ k, ∃ hk : k < gates.length, (gates[k]'hk).op = GateOp.not
  · right
    classical
    let k := Nat.find hex
    obtain ⟨hk, hkop⟩ : ∃ hk : k < gates.length, (gates[k]'hk).op = GateOp.not :=
      Nat.find_spec hex
    have hmin : ∀ i < k, ∀ hi : i < gates.length, (gates[i]'hi).op ≠ GateOp.not :=
      fun i hi hi' hop => Nat.find_min hex hi ⟨hi', hop⟩
    set pre := gates.take k with hpre
    set post := gates.drop (k + 1) with hpost
    have hprelen : pre.length = k := by simp [hpre]; omega
    have hsplit : gates = pre ++ gates[k] :: post := by
      rw [hpre, hpost, ← List.drop_eq_getElem_cons hk, List.take_append_drop]
    have hgk : gates[k] = ({ op := GateOp.not, inputs := (gates[k]).inputs } : Gate) := by
      cases h : gates[k] with
      | mk op ins => rw [h] at hkop; simp only at hkop; subst hkop; rfl
    have hsplit' : gates = pre ++ ({ op := GateOp.not, inputs := (gates[k]).inputs } : Gate)
        :: post := by
      rw [← hgk]; exact hsplit
    obtain ⟨ι, hι⟩ := hcnt
    obtain ⟨j0, hj0⟩ := hι ⟨k, hk⟩ (by simpa using hkop)
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := by
      rcases s with _ | t
      · exact j0.elim0
      · exact ⟨t, rfl⟩
    refine ⟨t, pre, post, (gates[k]).inputs, rfl, hsplit',
      (hops gates[k] (List.getElem_mem hk)).2, ?_, ?_⟩
    · intro g hg
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
      have hik : i < k := by omega
      have hig : i < gates.length := by omega
      have heq : pre[i] = gates[i] := by simp [hpre]
      rw [heq]
      obtain ⟨h1 | h1 | h1, h2⟩ := hops gates[i] (List.getElem_mem hig)
      · exact ⟨Or.inl h1, h2⟩
      · exact ⟨Or.inr h1, h2⟩
      · exact absurd h1 (hmin i hik hig)
    · intro g' hg' hg'len
      have hg'op : g'.op ≠ GateOp.not := by
        rcases hg' with h | h <;> rw [h] <;> simp
      refine ⟨?_, ?_⟩
      · intro g hg
        rcases List.mem_append.mp hg with h | h
        · exact hops g (by rw [hsplit]; simp [h])
        · rcases List.mem_cons.mp h with h | h
          · subst h
            rcases hg' with h | h
            · exact ⟨Or.inl h, hg'len⟩
            · exact ⟨Or.inr (Or.inl h), hg'len⟩
          · exact hops g (by rw [hsplit]; simp [h])
      · have hgl : gates.length = (pre ++ gates[k] :: post).length := by rw [← hsplit]
        let ι2 : Fin (t + 1) → Fin (pre ++ gates[k] :: post).length :=
          fun j => ⟨(ι j).val, by have := (ι j).isLt; omega⟩
        have hι2 : ∀ i : Fin (pre ++ gates[k] :: post).length,
            ((pre ++ gates[k] :: post).get i).op = GateOp.not → ∃ j, ι2 j = i := by
          intro i hi
          have hget : gates.get ⟨i.val, by have := i.isLt; omega⟩ =
              (pre ++ gates[k] :: post).get i := by
            simp only [List.get_eq_getElem]
            congr 1
          obtain ⟨j, hj⟩ := hι ⟨i.val, by have := i.isLt; omega⟩ (by rw [hget]; exact hi)
          exact ⟨j, Fin.ext (by simp [ι2, hj])⟩
        exact fn_split_count t pre post gates[k] g' hg'op ι2 hι2 j0
          (by simp [ι2, hj0, hprelen])
  · left
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨h1 | h1 | h1, h2⟩ := hops gates[i] hg
    · exact ⟨Or.inl h1, h2⟩
    · exact ⟨Or.inr h1, h2⟩
    · exact absurd ⟨i, hi, h1⟩ hex

theorem fn_family_reindex (n m q : ℕ) (S : Fin m → Finset (Fin n)) (y : Finset (Fin n))
    (hcard : ∀ i : Fin m, (S i).card = q + 1)
    (hmeet : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) :
    ∃ (m' : ℕ) (e : Fin m' → Fin m),
      m' = (Finset.univ.filter (fun w : Fin m => Disjoint (S w) y)).card ∧
      Function.Injective e ∧
      (∀ w : Fin m, Disjoint (S w) y ↔ ∃ i : Fin m', e i = w) ∧
      (∀ i : Fin m', (S (e i)).card = q + 1) ∧
      (∀ i j : Fin m', i ≠ j → (S (e i) ∩ S (e j)).card ≤ 1) := by
  classical
  set F := Finset.univ.filter (fun w : Fin m => Disjoint (S w) y) with hF
  let f := F.orderEmbOfFin (rfl : F.card = F.card)
  refine ⟨F.card, fun i => f i, rfl, f.injective, ?_, fun i => hcard _, ?_⟩
  · intro w
    have hr : Set.range f = (F : Set (Fin m)) := Finset.range_orderEmbOfFin F rfl
    constructor
    · intro hw
      have : w ∈ (F : Set (Fin m)) := by simp [hF, hw]
      rw [← hr] at this
      exact this
    · rintro ⟨i, rfl⟩
      have : f i ∈ (F : Set (Fin m)) := hr ▸ Set.mem_range_self i
      simpa [hF] using this
  · intro i j hij
    exact hmeet _ _ (fun h => hij (f.injective h))

theorem fnb_andOr2_of_not0 (gates : List Gate) (hops : OpsOK gates)
    (hn : NotAtMost 0 gates) : AndOr2 gates := by
  intro g hg
  obtain ⟨ι, hι⟩ := hn
  refine ⟨?_, (hops g hg).2⟩
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hg
  rcases (hops _ hg).1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · obtain ⟨j, _⟩ := hι i h
    exact j.elim0

theorem fnb_card_disj {n m d : ℕ} (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ)
    (hF : FamG n m d S kappa) (b : ℕ) (y : Finset (Fin n)) (hy : y.card ≤ b) :
    m - kappa b ≤ (Finset.univ.filter (fun w : Fin m => Disjoint (S w) y)).card := by
  have hk := hF.2.2 b y hy
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m))) (fun w : Fin m => Disjoint (S w) y)
  rw [Finset.card_univ, Fintype.card_fin] at hsum
  omega

def fnb_force {n : ℕ} (y : Finset (Fin n)) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => if i ∈ y then true else if i ∈ (∅ : Finset (Fin n)) then false else x i

theorem fnb_right_force {n m : ℕ} (S : Fin m → Finset (Fin n)) (y : Finset (Fin n)) (K : ℕ)
    (gates : List Gate) (out : Fin m → ℕ) (hr : Right S y K gates out) (w : Fin m)
    (hw : Disjoint (S w) y) (x : Fin n → Bool)
    (hx : (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ K) :
    Circuit.eval ⟨gates, out w⟩ (List.ofFn (fnb_force y x)) =
      decide (∃ v ∈ S w, x v = true) := by
  have hv : ∀ v ∈ S w, fnb_force y x v = x v := fun v hv => by
    have : v ∉ y := Finset.disjoint_left.mp hw hv
    simp [fnb_force, this]
  rw [hr w (fnb_force y x) hw (fun p hp => by simp [fnb_force, hp]) ?_]
  · simp only [decide_eq_decide]
    exact ⟨fun ⟨v, h1, h2⟩ => ⟨v, h1, by rw [← hv v h1]; exact h2⟩,
      fun ⟨v, h1, h2⟩ => ⟨v, h1, by rw [hv v h1]; exact h2⟩⟩
  · refine le_trans (Finset.card_le_card ?_) hx
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨h1, h2⟩ := hp
    simpa [fnb_force, h2] using h1

theorem fnb_card_single {n : ℕ} (p : Fin n) :
    (Finset.univ.filter (fun q : Fin n => decide (q = p) = true)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at ha hc
  rw [ha, hc]

theorem fnb_main : PBaseG := by
  intro h270 h669 hsub n m d S kappa hF b K y gates out hy hops hnot hright
  rw [fnp_genG_zero]
  rcases Nat.eq_zero_or_pos (min K (d - 1)) with h0 | hpos
  · rw [h0, Nat.mul_zero]
    exact Nat.zero_le _
  obtain ⟨hK, hd⟩ := Nat.lt_min.mp hpos
  obtain ⟨gates', r, hg', hlen, hcomp⟩ := h669 n gates y (fnb_andOr2_of_not0 gates hops hnot)
  obtain ⟨m', e, hm', _, hiff, hcard', hpair'⟩ :=
    hsub n m (d - 1) S y (fun i => by rw [hF.1 i]; omega) hF.2.1
  have hc : ∀ w : Fin m, Disjoint (S w) y → ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ K →
      Circuit.eval ⟨gates', r (out w)⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true) := by
    intro w hw x hx
    have hne : ∃ x x' : Fin n → Bool,
        Circuit.eval ⟨gates, out w⟩ (List.ofFn (fnb_force y x)) ≠
          Circuit.eval ⟨gates, out w⟩ (List.ofFn (fnb_force y x')) := by
      obtain ⟨p, hp⟩ : (S w).Nonempty := by
        rw [← Finset.card_pos, hF.1 w]
        omega
      refine ⟨fun _ => false, fun q => decide (q = p), ?_⟩
      rw [fnb_right_force S y K gates out hright w hw _ (by simp),
        fnb_right_force S y K gates out hright w hw _ ((fnb_card_single p).trans hK)]
      have h2 : ∃ v ∈ S w, decide (v = p) = true := ⟨p, hp, by simp⟩
      rw [decide_eq_true h2]
      simp
    have h1 := hcomp (out w) hne x
    exact h1.trans (fnb_right_force S y K gates out hright w hw x hx)
  have hdisj : ∀ i : Fin m', Disjoint (S (e i)) y := fun i => (hiff (e i)).mpr ⟨i, rfl⟩
  have key := h270 n m' K (fun i => S (e i)) ⟨gates', 0⟩ (fun i => r (out (e i)))
    (fun _ => min K (d - 1)) hpair' (fun i => by rw [hcard' i]; omega) hg'
    (fun i p => by
      change Circuit.eval ⟨gates', r (out (e i))⟩ _ = true ↔ _
      rw [hc (e i) (hdisj i) _ ((fnb_card_single p).trans hK)]
      simp)
    (fun i x hx hz => by
      change Circuit.eval ⟨gates', r (out (e i))⟩ _ = false
      rw [hc (e i) (hdisj i) x hx]
      simp only [decide_eq_false_iff_not, not_exists, not_and]
      intro v hv
      simp [hz v hv])
    (fun _ => min_le_left _ _) (fun i => by rw [hcard' i]; omega)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Circuit.size] at key
  have hm : m - kappa b ≤ m' := hm' ▸ fnb_card_disj S kappa hF b y hy
  calc (m - kappa b) * min K (d - 1) ≤ m' * min K (d - 1) := Nat.mul_le_mul_right _ hm
    _ ≤ gates'.length := key
    _ ≤ gates.length := hlen

def fns_hv {n : ℕ} (pre : List Gate) (ins : List ℕ) (x : Fin n → Bool) : Bool :=
  (ins.map fun i => (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD i false).headD false

theorem fns_right_mono {n m : ℕ} (S : Fin m → Finset (Fin n)) (y : Finset (Fin n))
    {j K : ℕ} (hj : j ≤ K) (gates : List Gate) (out : Fin m → ℕ)
    (h : Right S y K gates out) : Right S y j gates out :=
  fun w x hd h1 h2 => h w x hd h1 (le_trans h2 hj)

theorem fns_right_congr {n m : ℕ} (S : Fin m → Finset (Fin n)) (y : Finset (Fin n))
    (K : ℕ) (gates gates' : List Gate) (out : Fin m → ℕ)
    (hag : ∀ x : Fin n → Bool, Win y K x → ∀ o : ℕ,
      Circuit.eval ⟨gates', o⟩ (List.ofFn x) = Circuit.eval ⟨gates, o⟩ (List.ofFn x))
    (h : Right S y K gates out) : Right S y K gates' out := by
  intro w x hd h1 h2
  rw [hag x ⟨h1, h2⟩ (out w)]
  exact h w x hd h1 h2

theorem fns_card_true {n : ℕ} (y : Finset (Fin n)) (b j : ℕ) (hy : y.card ≤ b)
    (x : Fin n → Bool) (hx : Win y j x) :
    (Finset.univ.filter (fun p : Fin n => x p = true)).card ≤ b + j := by
  have hsub : Finset.univ.filter (fun p : Fin n => x p = true) ⊆
      y ∪ Finset.univ.filter (fun p : Fin n => x p = true ∧ p ∉ y) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_cases hpy : p ∈ y
    · exact Finset.mem_union_left _ hpy
    · exact Finset.mem_union_right _ (by simp [hp, hpy])
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ b + j := Nat.add_le_add hy hx.2

theorem fns_win_above {n : ℕ} (y : Finset (Fin n)) {j K : ℕ} (hj : j ≤ K)
    (x0 : Fin n → Bool) (hx0 : Win y j x0) (x : Fin n → Bool)
    (hx : Win (Finset.univ.filter (fun p : Fin n => x0 p = true)) (K - j) x) :
    Win y K x := by
  refine ⟨fun p hp => hx.1 p (by simp [hx0.1 p hp]), ?_⟩
  have hsub : Finset.univ.filter (fun p : Fin n => x p = true ∧ p ∉ y) ⊆
      Finset.univ.filter (fun p : Fin n => x0 p = true ∧ p ∉ y) ∪
      Finset.univ.filter (fun p : Fin n => x p = true ∧
        p ∉ Finset.univ.filter (fun p : Fin n => x0 p = true)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_cases h0 : x0 p = true
    · exact Finset.mem_union_left _ (by simp [h0, hp.2])
    · exact Finset.mem_union_right _ (by simp [h0, hp.1])
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ j + (K - j) := Nat.add_le_add hx0.2 hx.2
    _ = K := by omega

theorem fns_right_base {n m : ℕ} (S : Fin m → Finset (Fin n)) (y y' : Finset (Fin n))
    (hyy : y ⊆ y') (K K' : ℕ) (gates : List Gate) (out : Fin m → ℕ)
    (hwin : ∀ x : Fin n → Bool, Win y' K' x → Win y K x)
    (h : Right S y K gates out) : Right S y' K' gates out := by
  intro w x hd h1 h2
  have hw := hwin x ⟨h1, h2⟩
  exact h w x (Finset.disjoint_of_subset_right hyy hd) hw.1 hw.2

theorem fns_term_split {n m d : ℕ} (S : Fin m → Finset (Fin n)) (kappa : ℕ → ℕ) (s : ℕ)
    (ih : ClaimG n m d S kappa s) (b K : ℕ) (y : Finset (Fin n)) (out : Fin m → ℕ)
    (hy : y.card ≤ b) (pre post : List Gate) (ins : List ℕ)
    (hpre : AndOr2 pre)
    (hopsA : OpsOK (pre ++ ({ op := GateOp.and, inputs := [] } : Gate) :: post))
    (hopsO : OpsOK (pre ++ ({ op := GateOp.or, inputs := [] } : Gate) :: post))
    (hnA : NotAtMost s (pre ++ ({ op := GateOp.and, inputs := [] } : Gate) :: post))
    (hnO : NotAtMost s (pre ++ ({ op := GateOp.or, inputs := [] } : Gate) :: post))
    (hR : Right S y K (pre ++ ({ op := GateOp.not, inputs := ins } : Gate) :: post) out)
    (j : ℕ) (hj : j ≤ K) :
    min (fewNotGenG m d kappa s (b + j) (K - j)) (fewNotGenG m d kappa s b j) ≤
      (pre ++ ({ op := GateOp.not, inputs := ins } : Gate) :: post).length := by
  classical
  by_cases hex : ∃ x0 : Fin n → Bool, Win y j x0 ∧ fns_hv pre ins x0 = true
  · obtain ⟨x0, hx0, hv⟩ := hex
    set y' := Finset.univ.filter (fun p : Fin n => x0 p = true) with hy'
    have hyy : y ⊆ y' := fun p hp => by simp [hy', hx0.1 p hp]
    have hRy := fns_right_base S y y' hyy K (K - j) _ out
      (fun x hx => fns_win_above y hj x0 hx0 x hx) hR
    have hRO : Right S y' (K - j)
        (pre ++ ({ op := GateOp.or, inputs := [] } : Gate) :: post) out := by
      refine fns_right_congr S y' (K - j) _ _ out ?_ hRy
      intro x hx o
      apply OneNot.on1_piece_u_cheap
      exact OneNot.on1_piece_h n pre ins hpre x0 x
        (fun i hi => hx.1 i (by simp [hy', hi])) hv
    have := ih (b + j) (K - j) y' _ out (fns_card_true y b j hy x0 hx0) hopsO hnO hRO
    rw [fnp_variant_length pre post _ ({ op := GateOp.or, inputs := [] } : Gate)]
    exact le_trans (min_le_left _ _) this
  · have hRA : Right S y j
        (pre ++ ({ op := GateOp.and, inputs := [] } : Gate) :: post) out := by
      refine fns_right_congr S y j _ _ out ?_ (fns_right_mono S y hj _ out hR)
      intro x hx o
      apply OneNot.on1_piece_d
      have hf : ¬ fns_hv pre ins x = true := fun ht => hex ⟨x, hx, ht⟩
      simpa [fns_hv] using hf
    have := ih b j y _ out hy hopsA hnA hRA
    rw [fnp_variant_length pre post _ ({ op := GateOp.and, inputs := [] } : Gate)]
    exact le_trans (min_le_right _ _) this

theorem fns_main : PStepG := by
  intro hsplit n m d S kappa _hF s ih b K y gates out hy hops hnot hR
  rw [fnp_genG_succ]
  apply fn_foldr_max_le
  intro j hjr
  have hj : j ≤ K := by
    have := List.mem_range.mp hjr
    omega
  rcases hsplit gates s hops hnot with hle | ⟨pre, post, ins, heq, hpre, hopsA, hopsO, hnA, hnO⟩
  · exact le_trans (min_le_right _ _) (ih b j y gates out hy hops hle (fns_right_mono S y hj _ out hR))
  · subst heq
    exact fns_term_split S kappa s ih b K y out hy pre post ins hpre hopsA hopsO hnA hnO hR j hj

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

lemma hit_bound {n q : ℕ} (S : Fin n → Finset (Fin n))
    (deg : ∀ p, (through S p).card = q + 1)
    (join : ∀ p p' : Fin n, p ≠ p' → ∃ i, p ∈ S i ∧ p' ∈ S i)
    (y : Finset (Fin n)) (hy : y.Nonempty) :
    (y.biUnion (through S)).card ≤ y.card * q + 1 := by
  classical
  obtain ⟨p, hp⟩ := hy
  let R := y.erase p
  have diff (u : Fin n) (hu : u ∈ R) : (through S u \ through S p).card ≤ q := by
    have hne := (Finset.mem_erase.mp hu).1
    obtain ⟨l, hlu, hlp⟩ := join u p hne
    have hm : l ∈ through S u ∩ through S p := by simp [through, hlu, hlp]
    have hpos := Finset.card_pos.mpr ⟨l, hm⟩
    have he := Finset.card_sdiff_add_card_inter (through S u) (through S p)
    rw [deg] at he
    omega
  have cover : y.biUnion (through S) ⊆
      through S p ∪ R.biUnion (fun u => through S u \ through S p) := by
    intro l hl
    obtain ⟨u, hu, hlu⟩ := Finset.mem_biUnion.mp hl
    by_cases h : l ∈ through S p
    · exact Finset.mem_union_left _ h
    · have hne : u ≠ p := fun e => h (e ▸ hlu)
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨u, Finset.mem_erase.mpr ⟨hne, hu⟩, Finset.mem_sdiff.mpr ⟨hlu, h⟩⟩)
  have h1 := Finset.card_le_card cover
  have h2 := Finset.card_union_le (through S p) (R.biUnion (fun u => through S u \ through S p))
  have h3 := Finset.card_biUnion_le_card_mul R (fun u => through S u \ through S p) q diff
  have hr : R.card + 1 = y.card := Finset.card_erase_add_one hp
  rw [deg] at h2
  rw [← hr, Nat.add_mul, Nat.one_mul]
  omega

lemma recursive_bound {n q s : ℕ} (S : Fin n → Finset (Fin n)) (hn : n = q*q+q+1)
    (hq : 2 ≤ q) (hs : ∀ i, (S i).card = q+1)
    (hc : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (hj : ∀ p p' : Fin n, p ≠ p' → ∃ i, p ∈ S i ∧ p' ∈ S i)
    (gates : List Gate) (out : Fin n → ℕ) (hg : OpsOK gates) (hnot : NotAtMost s gates)
    (he : ∀ w x, Circuit.eval ⟨gates,out w⟩ (List.ofFn x) = decide (∃ p ∈ S w, x p = true))
    (G : ℕ → ℕ → ℕ → ℕ)
    (h0 : ∀ b K, G 0 b K = (n - (if b = 0 then 0 else min n (b*q+1))) * min K q)
    (h1 : ∀ t b K, G (t+1) b K = (List.range (K+1)).foldr
      (fun j acc => max acc (min (G t (b+j) (K-j)) (G t b j))) 0) :
    G s 0 n ≤ gates.length := by
  classical
  let κ : ℕ → ℕ := fun b => if b = 0 then 0 else min n (b*q+1)
  have family : FamG n n (q+1) S κ := by
    refine ⟨hs, fun i j h => (hc i j h).le, ?_⟩
    intro b y hy
    by_cases h : y = ∅
    · simp [h]
    have hne : y.Nonempty := Finset.nonempty_iff_ne_empty.mpr h
    have bne : b ≠ 0 := by have := Finset.card_pos.mpr hne; omega
    have eqset : Finset.univ.filter (fun w : Fin n => ¬ Disjoint (S w) y) =
        y.biUnion (through S) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.not_disjoint_iff,
        Finset.mem_biUnion, through]
      exact ⟨fun ⟨p, h1, h2⟩ => ⟨p, h2, h1⟩, fun ⟨p, h1, h2⟩ => ⟨p, h2, h1⟩⟩
    rw [eqset]
    simp only [κ, if_neg bne]
    apply le_min
    · simpa using Finset.card_le_univ (y.biUnion (through S))
    · exact (hit_bound S (through_card S hn (by omega) hs hc hj) hj y hne).trans
        (Nat.add_le_add_right (Nat.mul_le_mul_right q hy) 1)
  have recEq (t : ℕ) : G t = fewNotGenG n (q+1) κ t := by
    induction t with
    | zero =>
      funext b K
      rw [h0, fnp_genG_zero]
      simp [κ]
    | succ t ih =>
      funext b K
      rw [h1, fnp_genG_succ, ih]
  rw [recEq]
  exact fnp_assemblyG fn_family_reindex fn_split_general fnb_main fns_main promise restrict
    n n (q+1) S κ family s 0 n ∅ gates out (by simp) hg hnot (fun w x _ _ _ => he w x)

namespace Freeze

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

theorem trace_pair {n : ℕ} (gs : List Gate) (a b : Fin n → Bool)
    (hab : ∀ w, a w = true → b w = true) (hg : ∀ g ∈ gs, Allowed g)
    (i : Fin (notIndices gs).card)
    (hprev : ∀ j : Fin (notIndices gs).card, j < i →
      trace gs a (notEmbedding gs j) = trace gs b (notEmbedding gs j)) :
    trace gs b (notEmbedding gs i) = true → trace gs a (notEmbedding gs i) = true := by
  let j := notEmbedding gs i
  have hj := (mem_notIndices gs j).1 (notEmbedding_mem gs i)
  have hi : gs[j.val]? = some (gs.get j) := List.getElem?_eq_getElem j.isLt
  have got := note_antitone gs (List.ofFn a) (List.ofFn b)
    (initial_below _ _ hab) hg j.val (gs.get j) hi hj
  have earlier (k : ℕ) (q : Gate) (hk : k < j.val) (hq : gs[k]? = some q)
      (hqn : q.op = .not) :
      (run gs (List.ofFn a)).getD ((List.ofFn a).length + k) false =
      (run gs (List.ofFn b)).getD ((List.ofFn b).length + k) false := by
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

def rank : (t : ℕ) → (Fin t → Bool) → ℕ
  | 0, _ => 0
  | t+1, v => (if v 0 then 2^t else 0) + rank t (fun j => v j.succ)

lemma rank_lt (t : ℕ) (v : Fin t → Bool) : rank t v < 2^t := by
  induction t with
  | zero => simp [rank]
  | succ t ih =>
    have h := ih (fun j => v j.succ)
    rw [rank, pow_succ]
    split <;> omega

lemma rank_order (t : ℕ) (a b : Fin t → Bool)
    (h : ∀ i, (∀ j, j < i → a j = b j) → b i = true → a i = true) :
    rank t b ≤ rank t a ∧ (rank t b = rank t a → a = b) := by
  induction t with
  | zero => exact ⟨le_rfl, fun _ => funext (fun i => Fin.elim0 i)⟩
  | succ t ih =>
    have h0 : b 0 = true → a 0 = true := h 0 (by intro j hj; exact (Fin.not_lt_zero _ hj).elim)
    by_cases same : a 0 = b 0
    · have hh (i : Fin t) (prev : ∀ j : Fin t, j < i → a j.succ = b j.succ) :
          b i.succ = true → a i.succ = true := by
        apply h i.succ
        intro j
        refine Fin.cases (fun _ => same) (fun k hk => prev k (Fin.succ_lt_succ_iff.mp hk)) j
      obtain ⟨le, eq⟩ := ih (fun j => a j.succ) (fun j => b j.succ) hh
      constructor
      · simpa only [rank, same, Nat.add_le_add_iff_left] using le
      · intro ht
        simp only [rank, same, Nat.add_left_cancel_iff] at ht
        exact funext (fun j => Fin.cases same (fun k => congrFun (eq ht) k) j)
    · have ha : a 0 = true := by cases aa : a 0 <;> cases bb : b 0 <;> simp_all
      have hb : b 0 = false := by cases bb : b 0 <;> simp_all
      have ht := rank_lt t (fun j => b j.succ)
      simp only [rank, ha, hb, Bool.false_eq_true, if_false, if_true, Nat.zero_add]
      constructor <;> omega

lemma freeze_same (gs : List Gate) (a b : List Bool) (h : AgreesNot gs a b) :
    run (freeze a gs) b = run gs b := by
  induction gs generalizing a b with
  | nil => rfl
  | cons g gs ih =>
    classical
    have heq : appendGate b (freezeGate a g) = appendGate b g := by
      by_cases hn : g.op = .not
      · simp [appendGate, freezeGate, hn, booleanGate_runs, h.first hn]
      · simp [freezeGate, hn]
    rw [freeze, run_cons, run_cons, heq]
    exact ih _ _ h.tail

end Freeze

namespace Price

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
def specific {n m : ℕ} (z : Finset (Fin n)) (C : Circuit) (S : Fin m → Finset (Fin n)) (i : Fin m) :
    Finset ℕ := (Finset.Ico n (n+C.size)).filter fun w =>
      value C (offSet (z ∪ S i)) w = false ∧ ∀ j, j ≠ i → value C (offSet (z ∪ S j)) w = true

lemma private_count {q n m K : ℕ} (z : Finset (Fin n)) (S : Fin m → Finset (Fin n))
    (hq : 2 ≤ q) (hsize : ∀ i, (S i).card = q+1)
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (C : Circuit) (i : Fin m) (o c : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (heval : ∀ T : Finset (Fin n), T.card ≤ K →
      (value C (offSet (z ∪ T)) o = false ↔ S i ⊆ z ∪ T))
    (hc : c < (S i \ z).card) (hK : c*q < K) : c ≤ (specific z C S i).card := by
  classical
  by_contra! hsmall
  let G := specific z C S i
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
      (value C (offSet (z ∪ T)) w = true → value C (offSet (z ∪ S i)) w = true) := by
    by_cases hv : value C (offSet (z ∪ S i)) w = true
    · exact ⟨∅,Or.inl (by simp),by simp,fun _ => hv⟩
    · by_cases hin : w < n
      · let p : Fin n := ⟨w,hin⟩
        refine ⟨{p},Or.inl (by simp; omega),?_,?_⟩
        · exact (Finset.card_le_card (Finset.inter_subset_left : {p} ∩ S i ⊆ {p})).trans (by simp)
        · intro h
          change value C (offSet (z ∪ {p})) p = true at h
          simp [input_value,offSet] at h
      · by_cases bound : w < n+C.size
        · have hn : w ∉ specific z C S i := Finset.disjoint_left.mp hd hw
          have hex : ∃ j, j ≠ i ∧ ¬ value C (offSet (z ∪ S j)) w = true := by
            by_contra! neg
            apply hn
            refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,bound⟩,?_,neg⟩
            simpa using hv
          obtain ⟨j,hji,hj⟩ := hex
          exact ⟨S j,Or.inr ⟨j,rfl⟩,(hinter j i hji).le,fun h => absurd h hj⟩
        · refine ⟨∅,Or.inl (by simp),by simp,fun h => ?_⟩
          have hm := missing_value C (offSet (z ∪ ∅)) w (by omega)
          rw [hm] at h
          exact Bool.noConfusion h
  let A (w : ℕ) : Finset (Fin n) := if h : w ∈ B then (witness w h).choose else ∅
  have ha (w : ℕ) (hw : w ∈ B) :
      ((A w).card ≤ q ∨ ∃ j, A w = S j) ∧ (A w ∩ S i).card ≤ 1 ∧
      (value C (offSet (z ∪ A w)) w = true → value C (offSet (z ∪ S i)) w = true) := by
    simpa [A,hw] using (witness w hw).choose_spec
  let U := B.biUnion A
  have hu : U.card ≤ K := by
    have h := union_bound S hsize hinter B A (fun w hw => (ha w hw).1)
    have h' := Nat.mul_le_mul_right q hb
    change (B.biUnion A).card ≤ K
    omega
  have hSi : value C (offSet (z ∪ S i)) o = false := (heval (S i) hsK).mpr Finset.subset_union_right
  have hot : value C (offSet (z ∪ U)) o = false := by
    by_contra hne
    have ht : value C (offSet (z ∪ U)) o = true := by simpa using hne
    have h2 := hcut (offSet (z ∪ U)) (offSet (z ∪ S i)) (fun w hw hp => by
      apply (ha w hw).2.2
      apply value_mono C hg (offSet (z ∪ U)) (offSet (z ∪ A w)) _ w hp
      intro p hp
      simp only [offSet, decide_eq_true_eq] at hp ⊢
      intro hm
      rcases Finset.mem_union.mp hm with hz | ha
      · exact hp (Finset.mem_union_left _ hz)
      · exact hp (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w,hw,ha⟩))) o (Finset.mem_singleton_self o) ht
    rw [hSi] at h2
    exact Bool.noConfusion h2
  have hSub := (heval U hu).mp hot
  have hcover : S i \ z ⊆ B.biUnion (fun w => A w ∩ S i) := by
    intro p hp
    obtain ⟨hp, hz⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨w,hw,hm⟩ := Finset.mem_biUnion.mp ((Finset.mem_union.mp (hSub hp)).resolve_left hz)
    exact Finset.mem_biUnion.mpr ⟨w,hw,Finset.mem_inter.mpr ⟨hm,hp⟩⟩
  have h1 := Finset.card_le_card hcover
  have h2 := Finset.card_biUnion_le_card_mul B (fun w => A w ∩ S i) 1 (fun w hw => (ha w hw).2.1)
  simp only [Nat.mul_one] at h2
  omega

theorem window_bound {q n m d : ℕ} (S : Fin m → Finset (Fin n))
    (hq : 2 ≤ q) (hsize : ∀ i, (S i).card = q+1)
    (hcross : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (z : Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ)
    (hg : AndOr2 gates)
    (heval : ∀ w (u : Finset (Fin n)), u.card ≤ d*q+1 →
      Circuit.eval ⟨gates,out w⟩ (List.ofFn (offSet (z ∪ u))) =
        decide (∃ p ∈ S w, offSet (z ∪ u) p = true)) :
    (∑ w ∈ Finset.univ.filter (fun w => (S w ∩ z).card + 1 ≤ q),
      min d (q - (S w ∩ z).card)) ≤ gates.length := by
  classical
  let C : Circuit := ⟨gates,0⟩
  let G (w : Fin m) := specific z C S w
  let I := Finset.univ.filter (fun w => (S w ∩ z).card + 1 ≤ q)
  have hd : (I : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro w hi hj
    have htrue := (Finset.mem_filter.mp hi).2.2 j (Ne.symm hij)
    have hfalse := (Finset.mem_filter.mp hj).2.1
    simp [htrue] at hfalse
  have hi (w : Fin m) (hw : w ∈ I) : min d (q - (S w ∩ z).card) ≤ (G w).card := by
    apply private_count z S hq hsize hcross C w (out w) _ hg (K := d*q+1)
    · intro u hu
      have he := heval w u hu
      change value C (offSet (z ∪ u)) (out w) = _ at he
      rw [he]
      simp [offSet, Finset.subset_iff]
      constructor
      · intro h x hx
        by_cases hz : x ∈ z
        · exact Or.inl hz
        · exact Or.inr (h x hx hz)
      · intro h x hx hz
        exact (h hx).resolve_left hz
    · have eq := Finset.card_sdiff_add_card_inter (S w) z
      rw [hsize] at eq
      have h := (Finset.mem_filter.mp hw).2
      omega
    · have := Nat.mul_le_mul_right q (min_le_left d (q - (S w ∩ z).card))
      omega
  have hs : I.biUnion G ⊆ Finset.Ico n (n+C.size) := by
    intro t ht
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ht
    exact (Finset.mem_filter.mp hi).1
  calc
    _ ≤ ∑ w ∈ I, (G w).card := Finset.sum_le_sum fun w hw => hi w hw
    _ = (I.biUnion G).card := (Finset.card_biUnion hd).symm
    _ ≤ (Finset.Ico n (n+C.size)).card := Finset.card_le_card hs
    _ = gates.length := by simp [C, Circuit.size]

end Price


lemma minimum_bound {q s n : ℕ} (S : Fin n → Finset (Fin n))
    (hq : 2 ≤ q) (hsize : ∀ i, (S i).card = q+1)
    (hc : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (gs : List Gate) (out : Fin n → ℕ) (hg : OpsOK gs) (hn : NotAtMost s gs)
    (he : ∀ w x, Circuit.eval ⟨gs,out w⟩ (List.ofFn x) = decide (∃ p ∈ S w, x p = true))
    (j F T : ℕ) (_hj : 1 ≤ j) (_hjq : j ≤ q) (hF : F + 1 = 2^s)
    (hsmall : ∀ i, i+1 ≤ F → ∀ z : Finset (Fin n), z.card ≤ i*(j*q+1) →
      T ≤ ∑ l ∈ Finset.univ.filter (fun l => (S l ∩ z).card+1 ≤ q), min j (q-(S l ∩ z).card))
    (hlarge : ∀ z : Finset (Fin n), z.card ≤ F*(j*q+1) →
      T ≤ ∑ l ∈ Finset.univ.filter (fun l => (S l ∩ z).card+1 ≤ q), (q-(S l ∩ z).card)) :
    T ≤ gs.length := by
  classical
  let t := (Freeze.notIndices gs).card
  let v (z : Finset (Fin n)) (i : Fin t) :=
    Freeze.trace gs (Price.offSet z) (Freeze.notEmbedding gs i)
  let R (z : Finset (Fin n)) := Freeze.rank t (v z)
  have hle (z : Finset (Fin n)) : R z ≤ F := by
    have ht : t ≤ s := Freeze.card_notIndices gs s hn
    have hp : 2^t ≤ 2^s := Nat.pow_le_pow_right (by decide) ht
    have hr := Freeze.rank_lt t (v z)
    change Freeze.rank t (v z) ≤ F
    omega
  have ord (z u : Finset (Fin n)) (hz : z ⊆ u) :
      R z ≤ R u ∧ (R z = R u → v u = v z) := by
    apply Freeze.rank_order
    intro i hi
    apply Freeze.trace_pair gs (Price.offSet u) (Price.offSet z) _ hg i hi
    intro p hp
    simp only [Price.offSet, decide_eq_true_eq] at hp ⊢
    exact fun h => hp (hz h)
  let A := Finset.univ.filter (fun z : Finset (Fin n) => z.card ≤ R z * (j*q+1))
  have empty : (∅ : Finset (Fin n)) ∈ A := by simp [A]
  obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image A R ⟨∅, empty⟩
  have hsizez : z.card ≤ R z * (j*q+1) := (Finset.mem_filter.mp hz).2
  have stable (u : Finset (Fin n)) (hu : u.card ≤ j*q+1 ∨ R z = F) :
      v z = v (z ∪ u) := by
    obtain ⟨hr, eq⟩ := ord z (z ∪ u) Finset.subset_union_left
    apply Eq.symm
    apply eq
    apply Nat.le_antisymm hr
    by_contra! bigger
    rcases hu with small | full
    · have hcard := Finset.card_union_le z u
      have hmul := Nat.mul_le_mul_right (j*q+1) bigger
      rw [Nat.succ_mul] at hmul
      have mem : z ∪ u ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
      exact (Nat.not_lt_of_ge (hmax (z ∪ u) mem)) bigger
    · have := hle (z ∪ u)
      omega
  let input := List.ofFn (Price.offSet z)
  let clean := Freeze.freeze input gs
  have hclean : AndOr2 clean := Freeze.freeze_pos gs input hg
  have hlen : clean.length = gs.length := Freeze.freeze_length gs input
  have correct (w : Fin n) (u : Finset (Fin n)) (hu : u.card ≤ j*q+1 ∨ R z = F) :
      Circuit.eval ⟨clean,out w⟩ (List.ofFn (Price.offSet (z ∪ u))) =
        decide (∃ p ∈ S w, Price.offSet (z ∪ u) p = true) := by
    have agree := Freeze.trace_agrees gs (Price.offSet z) (Price.offSet (z ∪ u))
      (fun i => congrFun (stable u hu) i)
    have eq := Freeze.freeze_same gs input _ agree
    exact (congrArg (fun wires : List Bool => wires.getD (out w) false) eq).trans
      (he w (Price.offSet (z ∪ u)))
  rw [← hlen]
  by_cases full : R z = F
  · have c := Price.window_bound (d := q) S hq hsize hc z clean out hclean
        (fun w u _ => correct w u (Or.inr full))
    simp only [Nat.min_eq_right (Nat.sub_le q _)] at c
    exact (hlarge z (full ▸ hsizez)).trans c
  · have hi : R z + 1 ≤ F := by have := hle z; omega
    exact (hsmall (R z) hi z hsizez).trans (Price.window_bound S hq hsize hc z clean out
      hclean (fun w u hu => correct w u (Or.inl hu)))

end PEqualNP.Outside.L_meta_1325

theorem PEqualNP.Outside.L_meta_1325 : ∀ (q s : ℕ) (L : Fin (q ^ 2 + q + 1) → Finset (Fin (q ^ 2 + q + 1))), 2 ≤ q → (∀ i : Fin (q ^ 2 + q + 1), (L i).card = q + 1) → (∀ i j : Fin (q ^ 2 + q + 1), i ≠ j → (L i ∩ L j).card = 1) → (∀ p p' : Fin (q ^ 2 + q + 1), p ≠ p' → ∃ i : Fin (q ^ 2 + q + 1), p ∈ L i ∧ p' ∈ L i) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin (q ^ 2 + q + 1) → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s, ι j = i) → (∀ (w : Fin (q ^ 2 + q + 1)) (x : Fin (q ^ 2 + q + 1) → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ L w, x v = true)) → (∀ G : ℕ → ℕ → ℕ → ℕ, (∀ b K : ℕ, G 0 b K = ((q ^ 2 + q + 1) - (if b = 0 then 0 else min (q ^ 2 + q + 1) (b * q + 1))) * min K q) → (∀ t b K : ℕ, G (t + 1) b K = (List.range (K + 1)).foldr (fun (j acc : ℕ) => max acc (min (G t (b + j) (K - j)) (G t b j))) 0) → G s 0 (q ^ 2 + q + 1) ≤ gates.length) ∧ (∀ j F T : ℕ, 1 ≤ j → j ≤ q → F + 1 = 2 ^ s → (∀ i : ℕ, i + 1 ≤ F → ∀ z : Finset (Fin (q ^ 2 + q + 1)), z.card ≤ i * (j * q + 1) → T ≤ ∑ l ∈ Finset.univ.filter (fun l : Fin (q ^ 2 + q + 1) => (L l ∩ z).card + 1 ≤ q), min j (q - (L l ∩ z).card)) → (∀ z : Finset (Fin (q ^ 2 + q + 1)), z.card ≤ F * (j * q + 1) → T ≤ ∑ l ∈ Finset.univ.filter (fun l : Fin (q ^ 2 + q + 1) => (L l ∩ z).card + 1 ≤ q), (q - (L l ∩ z).card)) → T ≤ gates.length) := by
  intro q s L hq hs hc hj gates out hg hn he
  constructor
  · exact PEqualNP.Outside.L_meta_1325.recursive_bound L (by simp [pow_two]) hq hs hc hj gates out hg hn he
  · exact PEqualNP.Outside.L_meta_1325.minimum_bound L hq hs hc gates out hg hn he
