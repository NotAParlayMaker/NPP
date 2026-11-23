import Mathlib
import PEqualNP.Defs

-- Original proof by k-sandhu in PR 149.
-- Adapted here to the current proof-file namespace rules.

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.Chain1049

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

private lemma value_mono {n : ℕ} (C : Circuit)
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

-- Expand the selected gates once each, in reverse evaluation order.
-- Replacing one wire by at most two earlier wires increases the cut by at most one.
private lemma cut {n : ℕ} (C : Circuit)
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
-- Adapted from L-meta-270. Count only the singleton inputs accepted by the output.
private lemma card_assigned {n k c : ℕ} (C : Circuit) (T : Finset (Fin n)) (o : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hsparse : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q => x q = true)).card ≤ k →
      (∀ q ∈ T, x q = false) → value C x o = false)
    (hk : c ≤ k) (hc : c + 1 ≤ (support (n := n) C o).card) : c ≤ (assigned C T).card := by
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
  have hcover : (B.biUnion clean).card < (support (n := n) C o).card := by
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
    apply hcut (fun r => decide (r = p)) y _ o (Finset.mem_singleton_self o) ((mem_support C o p).mp hp)
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

private theorem mono_count : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  classical
  intro n m k S C o c hinter _ hG _ hsparse hk hc
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
      card_assigned C (S i) (o i) hG (hsparse i) (hk i) (hc i)
    _ = (Finset.univ.biUnion G).card := (Finset.card_biUnion hd).symm
    _ ≤ (Finset.Ico n (n + C.size)).card := Finset.card_le_card fun w hw => by
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
      exact (Finset.mem_filter.mp hi).1
    _ = C.size := by simp

theorem monotone_lower {n q : Nat} (S : Fin n → Finset (Fin n)) (hq : 1 ≤ q)
    (size : ∀ i, (S i).card = q+1) (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card = 1)
    (gs : List Gate) (o : Fin n → Nat)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (he : ∀ w (x : Fin n → Bool), Circuit.eval ⟨gs,o w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v=true)) :
    n*q ≤ gs.length := by
  let C : Circuit := ⟨gs,0⟩
  have point (w v : Fin n) : (C.wires (List.ofFn fun i : Fin n => decide (i=v))).getD (o w) false = true ↔ v ∈ S w := by
    change Circuit.eval ⟨gs,o w⟩ _ = true ↔ _
    rw [he]; simp
  have supp (w : Fin n) : (Finset.univ.filter fun v : Fin n =>
      (C.wires (List.ofFn fun i : Fin n => decide (i=v))).getD (o w) false = true) = S w := by
    ext; simp only [Finset.mem_filter,Finset.mem_univ,true_and,point]
  have cnt := mono_count n n q S C o (fun _ => q) (fun i j h => (hlin i j h).le)
    (by intro w; rw [supp,size]; omega) hg
    (by intro w v h; exact (point w v).mp h)
    (by intro w x _ off; change Circuit.eval ⟨gs,o w⟩ _ = false; rw [he]; simp_all)
    (by simp) (by intro w; rw [supp,size])
  simpa [C,Circuit.size] using cnt
theorem no_nots (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (no : ∃ ι : Fin 0 → Fin gs.length, ∀ i : Fin gs.length, (gs.get i).op = .not → ∃ j, ι j = i) :
    ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  obtain ⟨ι,hh⟩ := no
  intro g hm
  obtain ⟨ho,hl⟩ := hg g hm
  refine ⟨?_,hl⟩
  rcases ho with ha|hb|hn
  · exact Or.inl ha
  · exact Or.inr hb
  · obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hm
    obtain ⟨j,_⟩ := hh ⟨i,hi⟩ hn
    exact j.elim0
end PEqualNP.Outside.Chain1049

namespace PEqualNP.Outside.Clamp1049
open CircuitLowerBounds
def mono (g : Gate) := (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2
def adapt (pin : Nat → Option Bool) (g : Gate) : Gate :=
  let stop := (match g.op with | .or => true | _ => false)
  if g.inputs.any (fun i => pin i == some stop) then
    if stop then ⟨.and,[]⟩ else ⟨.or,[]⟩
  else ⟨g.op,g.inputs.filter fun i => (pin i).isNone⟩
def compatible (pin : Nat → Option Bool) (x y : List Bool) :=
  ∀ i, x.getD i false = (pin i).getD (y.getD i false)
def read (g : Gate) (x : List Bool) := g.op.eval (g.inputs.map fun i => x.getD i false)
theorem adapt_mono (pin) (g) (h : mono g) : mono (adapt pin g) := by
  rcases h with ⟨ho,hl⟩
  rcases g with ⟨op,ins⟩
  change op = .and ∨ op = .or at ho
  rcases ho with rfl|rfl
  all_goals dsimp only [adapt]; split
  all_goals first | exact ⟨Or.inl rfl,(List.length_filter_le ..).trans hl⟩
                  | exact ⟨Or.inr rfl,(List.length_filter_le ..).trans hl⟩
                  | simp [mono]
theorem adapt_read (pin) (g : Gate) (h : mono g) (x y : List Bool) (hr : compatible pin x y) :
    read g x = read (adapt pin g) y := by
  rcases g with ⟨op,ins⟩
  rcases h with ⟨ho,hl⟩
  change op = .and ∨ op = .or at ho
  change ins.length ≤ 2 at hl
  rcases ins with _|⟨a,_|⟨b,_|⟨c,cs⟩⟩⟩
  · rcases ho with rfl|rfl <;> rfl
  · have va := hr a
    rcases ho with rfl|rfl <;> rcases ha : pin a with _|⟨_|_⟩ <;>
      simp_all [read,adapt,GateOp.eval,List.getD]
  · have va := hr a
    have vb := hr b
    rcases ho with rfl|rfl <;> rcases ha : pin a with _|⟨_|_⟩ <;>
      rcases hb : pin b with _|⟨_|_⟩ <;> simp_all [read,adapt,GateOp.eval,List.getD]
  · simp at hl
theorem push (pin : Nat → Option Bool) (x y : List Bool) (b : Bool) (he : x.length = y.length)
    (hn : ∀ i, x.length ≤ i → pin i = none) (hr : compatible pin x y) :
    compatible pin (x ++ [b]) (y ++ [b]) := by
  intro i
  by_cases hi : i < x.length
  · rw [List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ (he ▸ hi),hr i]
  · have hg : x.length ≤ i := by omega
    rw [hn i hg,List.getD_append_right _ _ _ _ hg,List.getD_append_right _ _ _ _ (he ▸ hg),he]
    rfl
theorem adapt_run (pin : Nat → Option Bool) (gs : List Gate) (hg : ∀ g ∈ gs, mono g)
    (x y : List Bool) (he : x.length = y.length)
    (hn : ∀ i, x.length ≤ i → pin i = none) (hr : compatible pin x y) :
    compatible pin (gs.foldl (fun w g => w ++ [read g w]) x)
      ((gs.map (adapt pin)).foldl (fun w g => w ++ [read g w]) y) := by
  induction gs generalizing x y with
  | nil => exact hr
  | cons g gs ih =>
    simp only [List.map_cons,List.foldl_cons]
    have eq := adapt_read pin g (hg _ (by simp)) x y hr
    apply ih (fun a ha => hg a (by simp [ha])) _ _ (by simp [he]) (fun i hi => hn i (by simp at hi; omega))
    rw [← eq]
    exact push pin x y _ he hn hr
def pin {n} (A B : Finset (Fin n)) (i : Nat) : Option Bool :=
  if hi : i<n then if (⟨i,hi⟩ : Fin n) ∈ A then some true else
    if (⟨i,hi⟩ : Fin n) ∈ B then none else some false else none
def clamp {n} (A B : Finset (Fin n)) (x : Fin n → Bool) (p : Fin n) :=
  decide (p ∈ A) || (decide (p ∈ B) && x p)
theorem clamps {n} (A B : Finset (Fin n)) (gs : List Gate) (hg : ∀ g ∈ gs, mono g)
    (x : Fin n → Bool) (o : Nat) :
    Circuit.eval ⟨gs,o⟩ (List.ofFn (clamp A B x)) =
      (pin A B o).getD (Circuit.eval ⟨gs.map (adapt (pin A B)),o⟩ (List.ofFn x)) := by
  apply adapt_run (pin A B) gs hg _ _ (by simp) (by intro i hi; simp at hi; simp [pin,show ¬i<n by omega])
  intro i
  by_cases hi : i < n
  · let p : Fin n := ⟨i,hi⟩
    by_cases ha : p ∈ A <;> by_cases hb : p ∈ B <;>
      simp [pin,clamp,List.getD_eq_getElem?_getD,hi,p] at ha hb ⊢ <;> simp_all
  · simp [pin,List.getD_eq_getElem?_getD,hi]
end PEqualNP.Outside.Clamp1049

namespace PEqualNP.Outside.Chain1049
open CircuitLowerBounds Clamp1049
theorem window {n m d : Nat} (A B : Finset (Fin n)) (I : Finset (Fin m))
    (L : Fin m → Finset (Fin n)) (sz : ∀ i ∈ I, (L i).card = d+1)
    (lin : ∀ i j, i ≠ j → (L i ∩ L j).card ≤ 1)
    (gs : List Gate) (out : Fin m → Nat) (hg : ∀ g ∈ gs, mono g)
    (he : ∀ i ∈ I, ∀ x : Fin n → Bool, Circuit.eval ⟨gs,out i⟩ (List.ofFn (clamp A B x)) =
         decide (∃ v ∈ L i, x v = true)) : I.card*d ≤ gs.length := by
  classical
  by_cases zero : d = 0
  · simp [zero]
  let e := I.equivFin.symm
  let R (j : Fin I.card) := L (e j)
  let D : Circuit := ⟨gs.map (adapt (pin A B)),0⟩
  let addr (j : Fin I.card) := out (e j)
  have size (j : Fin I.card) : (R j).card = d+1 := sz _ (e j).property
  have rel (a b : Fin I.card) (hne : a ≠ b) : (R a ∩ R b).card ≤ 1 :=
    lin _ _ (fun eq => hne (e.injective (Subtype.ext eq)))
  have ev (j : Fin I.card) (x : Fin n → Bool) :
      (D.wires (List.ofFn x)).getD (addr j) false = decide (∃ v ∈ R j, x v=true) := by
    have good (z : Fin n → Bool) := (clamps A B gs hg z (addr j)).symm.trans (he _ (e j).property z)
    have hpos : (R j).Nonempty := Finset.card_pos.mp (by rw [size]; omega)
    cases hp : pin A B (addr j) with
    | none => simpa [hp,D,R,Circuit.eval,Circuit.wires] using good x
    | some b =>
      have h0 := good (fun _ => false)
      have h1 := good (fun _ => true)
      change (pin A B (addr j)).getD _ = decide (∃ v ∈ R j, true = true) at h1
      simp [hp] at h0
      simp [hp,h0] at h1
      obtain ⟨v,hv⟩ := hpos; exact (h1 v hv).elim
  have point (w : Fin I.card) (v : Fin n) :
      (D.wires (List.ofFn fun i => decide (i=v))).getD (addr w) false = true ↔ v ∈ R w := by
    rw [ev]; simp
  have supp (w : Fin I.card) : (Finset.univ.filter fun v : Fin n =>
      (D.wires (List.ofFn fun i : Fin n => decide (i=v))).getD (addr w) false = true) = R w := by
    ext; simp only [Finset.mem_filter,Finset.mem_univ,true_and,point]
  have cnt := mono_count n I.card d R D addr (fun _ => d) rel
    (by intro w; rw [supp,size]; omega)
    (by intro g hm; obtain ⟨g',hm',rfl⟩ := List.mem_map.mp hm; exact adapt_mono _ _ (hg _ hm'))
    (by intro w v hv; exact (point w v).mp hv)
    (by intro w x _ off; rw [ev]; simp_all)
    (by simp) (by intro w; rw [supp,size])
  simpa [Circuit.size,D] using cnt
end PEqualNP.Outside.Chain1049

namespace PEqualNP.Outside.Chain1049
open CircuitLowerBounds
abbrev Valid (g : Gate) := g.op = .and ∨ g.op = .or ∨ g.op = .not
def IsNot (g : Gate) : Bool := match g.op with | .not => true | _ => false
def bit (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
def update (g : Gate) (w : List Bool) := w ++ [bit g w]
def rank : List Gate → List Bool → Nat → Nat
  | [], _, r => r
  | g::gs, w, r => rank gs (update g w) (if IsNot g then 2*r + (if bit g w then 0 else 1) else r)
def locks : List Gate → List Bool → List (Option Bool)
  | [], _ => []
  | g::gs,w => (if IsNot g then some (bit g w) else none) :: locks gs (update g w)

def ordered (a b : List Bool) := a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true
private theorem upd_ord {a b : List Bool} (h : ordered a b) (u v : Bool) (hp : u = true → v = true) :
    ordered (a ++ [u]) (b ++ [v]) := by
  refine ⟨by simp [h.1],?_⟩
  intro i
  by_cases hi : i < a.length
  · rw [List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ (h.1 ▸ hi)]
    exact h.2 i
  · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by have := h.1; omega),h.1]
    cases (i-b.length) <;> simp_all [List.getD]

private theorem bit_order {a b : List Bool} (h : ordered a b) (g : Gate) (hg : Valid g) :
    (IsNot g = false → bit g a = true → bit g b = true) ∧
    (IsNot g = true → bit g b = true → bit g a = true) := by
  have ho : ∀ i, a[i]?.getD false = true → b[i]?.getD false = true := h.2
  rcases g with ⟨op,is⟩
  rcases hg with rfl|rfl|rfl
  · simp [IsNot,bit,GateOp.eval]; grind
  · simp [IsNot,bit,GateOp.eval]; grind
  · simp only [IsNot,bit,GateOp.eval]
    cases is with
    | nil => simp
    | cons i is => simp; grind

theorem rank_bound (gs : List Gate) (w : List Bool) (r : Nat) :
    rank gs w r < (r+1)*2^(gs.countP IsNot) := by
  induction gs generalizing r w with
  | nil => simp [rank]
  | cons g gs ih =>
    rw [rank,List.countP_cons]
    cases hg : IsNot g <;> simp [hg]
    · exact ih _ _
    · have H := ih (update g w) (2*r + if bit g w then 0 else 1)
      cases hh : bit g w <;> simp [hh,pow_succ] at H ⊢ <;> nlinarith [H]

private theorem rank_floor (gs : List Gate) (w : List Bool) (r : Nat) :
    r*2^(gs.countP IsNot) ≤ rank gs w r := by
  induction gs generalizing r w with
  | nil => simp [rank]
  | cons g gs ih =>
    rw [rank,List.countP_cons]
    cases hg : IsNot g <;> simp [hg]
    · exact ih _ _
    · have H := ih (update g w) (2*r + if bit g w then 0 else 1)
      cases hh : bit g w <;> simp [hh,pow_succ] at H ⊢ <;> nlinarith [H]

private theorem rank_strict (gs : List Gate) (a b : List Bool) (r s : Nat) (h : r < s) :
    rank gs a r < rank gs b s :=
  lt_of_lt_of_le (rank_bound ..) ((Nat.mul_le_mul_right _ h).trans (rank_floor ..))

theorem ranks (gs : List Gate) (hg : ∀ g ∈ gs, Valid g) {a b : List Bool} (h : ordered a b) (r : Nat) :
    rank gs a r ≤ rank gs b r ∧ (rank gs a r = rank gs b r → locks gs a = locks gs b) := by
  induction gs generalizing a b r with
  | nil => simp [rank,locks]
  | cons g gs ih =>
    have O := bit_order h g (hg g (by simp))
    have H := @ih (fun x hx => hg x (by simp [hx]))
    simp only [rank,locks]
    cases hn : IsNot g with
    | false =>
      simp only [hn,Bool.false_eq_true,if_false,List.cons.injEq,true_and]
      exact H (upd_ord h _ _ (O.1 hn)) r
    | true =>
      simp only [hn,if_true,List.cons.injEq,Option.some.injEq]
      by_cases he : bit g a = bit g b
      · rw [he]
        have hu : ordered (update g a) (update g b) := upd_ord h _ _ (fun ha => he ▸ ha)
        simpa only [true_and] using H hu (2*r + if bit g b then 0 else 1)
      · have ha : bit g a = true := by cases ha : bit g a <;> cases hb : bit g b <;> grind
        have hb : bit g b = false := by cases hb : bit g b <;> grind
        simp [ha,hb]
        have hs := rank_strict gs (update g a) (update g b) (2*r) (2*r+1) (by omega)
        omega
theorem cuts (N M : Nat) (hM : 0 < M) (r : Nat → Nat) (hm : Monotone r) (hb : ∀ i < N, r i < M) :
    ∃ P ⊆ Finset.range N, P.card + 1 ≤ M ∧
      ∀ a b, a ≤ b → b < N → (∀ w ∈ P, ¬ (a < w ∧ w ≤ b)) → r a = r b := by
  let P := (Finset.range N).filter fun i => 0 < i ∧ r (i-1) < r i
  have mem {i : Nat} : i ∈ P ↔ i < N ∧ 0 < i ∧ r (i-1) < r i := by simp [P]
  have strict {i j : Nat} (_hi : i ∈ P) (hj : j ∈ P) (h : i < j) : r i < r j :=
    lt_of_le_of_lt (hm (by omega : i ≤ j-1)) (mem.mp hj).2.2
  have inj : Set.InjOn r P := by
    intro i hi j hj eq
    rcases lt_trichotomy i j with h|h|h
    · exact ((strict hi hj h).ne eq).elim
    · exact h
    · exact ((strict hj hi h).ne eq.symm).elim
  have sub : P.image r ⊆ Finset.Ico 1 M := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    have h := mem.mp hi
    exact Finset.mem_Ico.mpr ⟨by omega,hb _ h.1⟩
  have hc := Finset.card_le_card sub
  rw [Finset.card_image_of_injOn inj,Nat.card_Ico] at hc
  refine ⟨P,Finset.filter_subset ..,by omega,?_⟩
  intro a b hab hN hn
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    rw [ha]
  | succ b ih =>
    by_cases h : a = b+1
    · rw [h]
    have he : r b = r (b+1) := by
      have hle := hm (Nat.le_succ b)
      by_contra! hf
      have hi : b+1 ∈ P := mem.mpr ⟨hN,by omega,by simpa using (lt_of_le_of_ne hle hf)⟩
      exact hn _ hi ⟨by omega,le_rfl⟩
    exact (ih (by omega) (by omega) (fun w hw hab => hn w hw ⟨hab.1,by omega⟩)).trans he

theorem count_le (gs : List Gate) (t : Nat) (cover : ∃ ι : Fin t → Fin gs.length,
    ∀ i : Fin gs.length, (gs.get i).op = .not → ∃ j, ι j = i) : gs.countP IsNot ≤ t := by
  obtain ⟨ι,hι⟩ := cover
  let Q := Finset.univ.filter fun j : Fin gs.length => IsNot (gs.get j)
  have hc : gs.countP IsNot = Q.card := by
    simpa only [List.ofFn_get] using List.countP_ofFn gs.get IsNot
  have hs : Q ⊆ Finset.univ.image ι := by
    intro j hj
    have h := (Finset.mem_filter.mp hj).2
    have hop : (gs.get j).op = .not := by
      unfold IsNot at h
      cases ho : (gs.get j).op <;> simp_all
    obtain ⟨k,hk⟩ := hι j hop
    exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,hk⟩
  rw [hc]
  exact (Finset.card_le_card hs).trans (Finset.card_image_le.trans (by simp))

def freeze : List Gate → List Bool → List Gate
  | [], _ => []
  | g::gs,w =>
    (if IsNot g then (if bit g w then ⟨.and,[]⟩ else ⟨.or,[]⟩) else g) :: freeze gs (update g w)

theorem freeze_length (gs : List Gate) (w : List Bool) : (freeze gs w).length = gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons _ _ ih => simp [freeze, ih]

theorem freeze_mono (gs : List Gate) (w : List Bool)
    (hg : ∀ g ∈ gs, Valid g ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ freeze gs w, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  induction gs generalizing w with
  | nil => simp [freeze]
  | cons g gs ih =>
    obtain ⟨ho, hl⟩ := hg g (by simp)
    intro f hf
    rcases List.mem_cons.mp hf with rfl|ht
    · rcases ho with ha|ha|ha <;> simp [IsNot,ha,hl] <;> split <;> simp
    · exact ih _ (fun f hf => hg f (by simp [hf])) _ ht

theorem freeze_correct (gs : List Gate) (a b : List Bool) (h : locks gs a = locks gs b) :
    (freeze gs a).foldl (fun w g => update g w) b = gs.foldl (fun w g => update g w) b := by
  induction gs generalizing a b with
  | nil => rfl
  | cons g gs ih =>
    have Heq := List.cons.inj h
    have hv : update (if IsNot g then (if bit g a then ⟨.and,[]⟩ else ⟨.or,[]⟩) else g) b = update g b := by
      cases hn : IsNot g
      · rfl
      · have eq : bit g a = bit g b := by simpa [hn] using Heq.1
        rw [eq]
        unfold update
        cases hb : bit g b <;> rfl
    simp only [freeze,List.foldl_cons,hv]
    exact ih _ _ Heq.2

theorem ordered_ofFn {n : Nat} (a b : Fin n → Bool) (h : ∀ i, a i = true → b i = true) :
    ordered (List.ofFn a) (List.ofFn b) := by
  refine ⟨by simp,?_⟩
  intro i
  by_cases hi : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getD_eq_getElem _ _ (by simpa using hi)]
    simpa using h ⟨i,hi⟩
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem segments {n : Nat} (N t : Nat) (gs : List Gate)
    (hg : ∀ g ∈ gs, Valid g ∧ g.inputs.length ≤ 2)
    (cov : ∃ ι : Fin t → Fin gs.length, ∀ i : Fin gs.length, (gs.get i).op = .not → ∃ j, ι j = i)
    (X : Nat → Fin n → Bool) (hx : ∀ i j, i ≤ j → ∀ p, X i p = true → X j p = true) :
    ∃ P ⊆ Finset.range N, P.card + 1 ≤ 2^t ∧ ∀ i j, i ≤ j → j < N →
      (∀ w ∈ P, ¬ (i < w ∧ w ≤ j)) →
      ∃ ms : List Gate, ms.length = gs.length ∧
        (∀ g ∈ ms, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
        ∀ x : Fin n → Bool, (∀ p, X i p = true → x p = true) → (∀ p, x p = true → X j p = true) →
          ∀ o : Nat, (Circuit.mk ms o).eval (List.ofFn x) = (Circuit.mk gs o).eval (List.ofFn x) := by
  let R (x : Fin n → Bool) := rank gs (List.ofFn x) 0
  have Hv : ∀ g ∈ gs, Valid g := fun g h => (hg g h).1
  have mono : Monotone (fun i => R (X i)) := fun i j hij =>
    (ranks gs Hv (ordered_ofFn _ _ (hx i j hij)) 0).1
  have bound (i : Nat) : R (X i) < 2^t := by
    apply lt_of_lt_of_le _ (Nat.pow_le_pow_right (by decide : 0 < 2) (count_le gs t cov))
    simpa [R] using rank_bound gs (List.ofFn (X i)) 0
  obtain ⟨P,hs,hc,run⟩ := cuts N _ (by positivity) _ mono (fun i _ => bound i)
  refine ⟨P,hs,hc,?_⟩
  intro i j hij hj hp
  refine ⟨freeze gs (List.ofFn (X i)),freeze_length ..,freeze_mono _ _ hg,?_⟩
  intro x hix hxj o
  have l := ranks gs Hv (ordered_ofFn _ _ hix) 0
  have r := ranks gs Hv (ordered_ofFn _ _ hxj) 0
  have eq := run i j hij hj hp
  change R (X i) = R (X j) at eq
  have eq' : R (X i) = R x := le_antisymm l.1 (eq ▸ r.1)
  exact congrArg (fun w : List Bool => w.getD o false) (freeze_correct gs _ _ (l.2 eq'))

end PEqualNP.Outside.Chain1049

namespace PEqualNP.Outside.Game1049

def level (h q n i : ℕ) := if i = 0 then n else if i = h+2 then 0 else q*(q+1) / 2^(i-1) - q
def factor (h q j : ℕ) := if j = h+2 then q else 2^(j-1)-1
def runs (h : ℕ) (P : Finset ℕ) :=
  ((Finset.range (h+3)) ×ˢ (Finset.range (h+3))).filter fun uv =>
    uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2)
def score (h q n : ℕ) (P : Finset ℕ) :=
  (runs h P).sup fun uv => (level h q n uv.1 - level h q n uv.2) * factor h q uv.2
def game (h q n t : ℕ) :=
  WithTop.untopD 0 ((((Finset.range (h+3)).powerset.filter fun P => P.card+1 ≤ 2^t).image (score h q n)).min)

private theorem game_le (h q n t : ℕ) (P : Finset ℕ) (hP : P ⊆ Finset.range (h+3))
    (hc : P.card+1 ≤ 2^t) : game h q n t ≤ score h q n P := by
  apply WithTop.untopD_le
  apply Finset.min_le
  exact Finset.mem_image.mpr ⟨P, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hP,hc⟩,rfl⟩

private theorem level_le (h q n i : ℕ) (hn : n = q*q + q + 1) : level h q n i ≤ n := by
  have hmul : q * (q+1) ≤ n := by rw [hn,Nat.mul_add]; omega
  unfold level
  split_ifs <;> first | omega | exact (Nat.sub_le _ _).trans ((Nat.div_le_self _ _).trans hmul)

theorem game_le_mul (h q n t : ℕ) (hq : q = 2^h) (hn : n = q*q+q+1) :
    game h q n t ≤ n*q := by
  apply (game_le h q n t ∅ (by simp) (by simpa using (Nat.one_le_two_pow (n := t)))).trans
  apply Finset.sup_le
  intro uv huv
  obtain ⟨_,hv⟩ := Finset.mem_product.mp (Finset.mem_filter.mp huv).1
  have hv' := Finset.mem_range.mp hv
  apply Nat.mul_le_mul ((Nat.sub_le _ _).trans (level_le _ _ _ _ hn))
  unfold factor
  split_ifs with e
  · exact le_rfl
  · rw [hq]
    exact (Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by decide) (by omega))

theorem game_le_outputs (h q n t : ℕ) (hh : 1 ≤ h) (hn : n = q*q+q+1) (ht : h+1 ≤ 2^t) :
    game h q n t ≤ n := by
  let P := Finset.Ico 3 (h+3)
  have hP : P ⊆ Finset.range (h+3) := fun _ hw => Finset.mem_range.mpr (Finset.mem_Ico.mp hw).2
  have hc : P.card+1 ≤ 2^t := by simpa [P] using ht
  apply (game_le h q n t P hP hc).trans
  apply Finset.sup_le
  intro uv huv
  obtain ⟨hm,hle,cut⟩ := Finset.mem_filter.mp huv
  have hv := Finset.mem_range.mp (Finset.mem_product.mp hm).2
  by_cases eq : uv.1 = uv.2
  · simp [eq]
  have small : uv.2 ≤ 2 := by
    by_contra! h
    exact cut uv.2 (Finset.mem_Ico.mpr ⟨by omega,hv⟩) ⟨by omega,le_rfl⟩
  have hf : factor h q uv.2 ≤ 1 := by
    unfold factor
    have ne : uv.2 ≠ h+2 := by omega
    simp only [ne, reduceIte]
    have pw : 2^(uv.2-1) ≤ 2^1 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  simpa only [Nat.mul_one] using Nat.mul_le_mul ((Nat.sub_le _ _).trans (level_le _ _ _ _ hn)) hf
end PEqualNP.Outside.Game1049

namespace PEqualNP.Outside.Game1049
open Finset

def incident {n : ℕ} (S : Fin n → Finset (Fin n)) (p : Fin n) := univ.filter fun i => p ∈ S i
def misses {n : ℕ} (S : Fin n → Finset (Fin n)) (A : Finset (Fin n)) :=
  univ.filter fun i => Disjoint (S i) A

theorem incident_card {n q : ℕ} (S : Fin n → Finset (Fin n)) (hn : n=q*q+q+1) (hq : 0<q)
    (hcard : ∀ i,(S i).card=q+1) (hc : ∀ i j, i≠j → (S i ∩ S j).card=1)
    (hp : ∀ p p', p≠p' → ∃ i, p∈S i ∧ p'∈S i) (p : Fin n) : (incident S p).card=q+1 := by
  let I := incident S p
  have mem {i : Fin n} : i ∈ I ↔ p ∈ S i := by simp [I,incident]
  have dis : (I : Set (Fin n)).PairwiseDisjoint (fun i => (S i).erase p) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨hxp,hxi⟩ := Finset.mem_erase.mp hx
    have hxy := (Finset.mem_erase.mp hy).2
    exact hxp (Finset.card_le_one.mp (hc i j hij).le x (Finset.mem_inter.mpr ⟨hxi,hxy⟩)
      p (Finset.mem_inter.mpr ⟨mem.mp hi,mem.mp hj⟩))
  have un : I.biUnion (fun i => (S i).erase p) = univ.erase p := by
    ext x
    simp only [Finset.mem_biUnion,Finset.mem_erase,Finset.mem_univ,and_true]
    constructor
    · rintro ⟨i,_,hx,_⟩; exact hx
    · intro hx
      obtain ⟨i,hi,hit⟩ := hp p x hx.symm
      exact ⟨i,mem.mpr hi,hx,hit⟩
  have each (i : Fin n) (hi : i∈I) : ((S i).erase p).card=q := by
    rw [Finset.card_erase_of_mem (mem.mp hi),hcard]; omega
  have H := Finset.card_biUnion dis
  rw [un,Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,Fintype.card_fin,
    Finset.sum_congr rfl each,Finset.sum_const,Nat.nsmul_eq_mul] at H
  change I.card = q+1
  apply Nat.eq_of_mul_eq_mul_right hq
  rw [← H,hn,Nat.add_mul]; simp

theorem misses_card {n q d : ℕ} (S : Fin n → Finset (Fin n)) (A : Finset (Fin n))
    (hn : n=q*q+q+1) (hd : 0<d) (ha : A.card=(d-1)*q+d)
    (hr : ∀ p,(incident S p).card=q+1)
    (hvals : ∀ i,(S i ∩ A).card=0 ∨ (S i ∩ A).card=d) :
    (misses S A).card = q*(q+1)/d-q := by
  let hit := univ.filter fun i => ¬Disjoint (S i) A
  have inter (i : Fin n) : A.bipartiteAbove (fun (w p : Fin n) => p ∈ S w) i = S i ∩ A := by
    ext x; simp [Finset.bipartiteAbove,and_comm]
  have below (p : Fin n) : (univ : Finset (Fin n)).bipartiteBelow (fun w p : Fin n => p ∈ S w) p = incident S p := rfl
  have each (i : Fin n) : (S i ∩ A).card = if i ∈ hit then d else 0 := by
    have hz : (S i ∩ A).card=0 ↔ Disjoint (S i) A := by rw [Finset.card_eq_zero,Finset.disjoint_iff_inter_eq_empty]
    simp only [hit,Finset.mem_filter,Finset.mem_univ,true_and]
    split_ifs with hh
    · exact hz.mpr hh
    · exact (hvals i).resolve_left (fun h => hh (hz.mp h))
  have H := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s:=univ) (t:=A) (fun (w p : Fin n) => p ∈ S w)
  simp_rw [inter,below,hr,each] at H
  simp at H
  have part : hit.card + (misses S A).card=n := by
    simpa [hit,misses,add_comm] using
      (Finset.card_filter_add_card_filter_not (s:=(univ : Finset (Fin n))) (fun i => Disjoint (S i) A))
  rw [ha] at H
  have norm : (d-1)*q+q=d*q := by rw [← Nat.succ_mul]; congr 1; omega
  have prod : ((misses S A).card + q)*d=q*(q+1) := by
    have Hn := congrArg (fun m => m*d) part
    change (hit.card + (misses S A).card) * d = n * d at Hn
    have Hn2 := Hn.trans (congrArg (fun z => z*d) hn)
    nlinarith only [H,Hn2,congrArg (fun m : ℕ => m*(q+1)) norm]
  rw [← prod,Nat.mul_div_left _ hd]; omega

end PEqualNP.Outside.Game1049

namespace PEqualNP.Outside.Game1049
open Finset
def layer {h n : ℕ} (K : Fin (h+1) → Finset (Fin n)) (a : Fin (h+3)) :=
  if a.val = 0 then ∅ else if hj : a.val-1 < h+1 then K ⟨a.val-1,hj⟩ else univ

theorem layer_mono {h n : ℕ} (K : Fin (h+1) → Finset (Fin n))
    (hK : ∀ j j', j ≤ j' → K j ⊆ K j') {a b : Fin (h+3)} (hab : a≤b) :
    layer K a ⊆ layer K b := by
  have hv := Fin.le_iff_val_le_val.mp hab
  unfold layer
  split_ifs <;> first | exact Finset.empty_subset _ | exact Finset.subset_univ _ |
    exact hK _ _ (by apply Fin.le_iff_val_le_val.mpr; dsimp; omega) | omega

theorem misses_layer_card {h q n : ℕ} (S : Fin n → Finset (Fin n)) (K : Fin (h+1) → Finset (Fin n))
    (hn : n=q*q+q+1) (hr : ∀ p,(incident S p).card=q+1) (hs : ∀ i,(S i).card=q+1)
    (hk : ∀ j,(K j).card=(2^j.val-1)*q+2^j.val)
    (hvals : ∀ j i,(S i ∩ K j).card=0 ∨ (S i ∩ K j).card=2^j.val) (a : Fin (h+3)) :
    (misses S (layer K a)).card = level h q n a.val := by
  by_cases h0 : a.val = 0
  · simp [layer,level,h0,misses]
  by_cases hlast : a.val=h+2
  · have hj : ¬ a.val-1<h+1 := by omega
    have hempty : misses S univ = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      have eq := Finset.disjoint_iff_inter_eq_empty.mp hi'
      simp only [Finset.inter_univ] at eq
      have h := hs i
      rw [eq,Finset.card_empty] at h
      omega
    simp only [layer,h0,ite_false,hj,dite_false,hempty,Finset.card_empty,level]
    simp [hlast]
  · have hj : a.val-1<h+1 := by have := a.isLt; omega
    let j : Fin (h+1) := ⟨a.val-1,hj⟩
    simpa only [layer,h0,ite_false,hj,dite_true,level,hlast] using
      (misses_card S (K j) hn (pow_pos (by decide : 0<2) _) (hk j) hr (hvals j))

theorem window_card {h q n : ℕ} (S : Fin n → Finset (Fin n)) (K : Fin (h+1) → Finset (Fin n))
    (hn : n=q*q+q+1) (hr : ∀ p,(incident S p).card=q+1) (hs : ∀ i,(S i).card=q+1)
    (hk : ∀ j,(K j).card=(2^j.val-1)*q+2^j.val)
    (hvals : ∀ j i,(S i ∩ K j).card=0 ∨ (S i ∩ K j).card=2^j.val)
    (hK : ∀ j j', j ≤ j' → K j ⊆ K j') (a b : Fin (h+3)) (hab : a ≤ b) :
    (misses S (layer K a) \ misses S (layer K b)).card = level h q n a.val - level h q n b.val := by
  have sub : misses S (layer K b) ⊆ misses S (layer K a) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2.mono_right (layer_mono K hK hab)⟩
  rw [Finset.card_sdiff_of_subset sub,misses_layer_card S K hn hr hs hk hvals,misses_layer_card S K hn hr hs hk hvals]
theorem hit_card {h q n : ℕ} (S : Fin n → Finset (Fin n)) (K : Fin (h+1) → Finset (Fin n))
    (hs : ∀ i,(S i).card=q+1) (hvals : ∀ j i,(S i ∩ K j).card=0 ∨ (S i ∩ K j).card=2^j.val)
    (b : Fin (h+3)) (i : Fin n) (hb : b.val ≠ 0) (hit : i ∉ misses S (layer K b)) :
    (S i ∩ layer K b).card = factor h q b.val + 1 := by
  have hpos : (S i ∩ layer K b).card ≠ 0 := by
    intro hz
    exact hit (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hz)⟩)
  by_cases e : b.val = h+2
  · have hj : ¬ b.val-1<h+1 := by omega
    simp only [layer,hb,ite_false,hj,dite_false,Finset.inter_univ,hs,factor]
    simp [e]
  · have hj : b.val-1<h+1 := by have := b.isLt; omega
    let j : Fin (h+1) := ⟨b.val-1,hj⟩
    simp only [layer,hb,ite_false,hj,dite_true,factor,e] at hpos ⊢
    have eq := (hvals j i).resolve_left hpos
    have hp : 0 < 2^(b.val-1) := pow_pos (by decide) _
    change (S i ∩ K j).card = 2^(b.val-1)-1+1
    rw [eq]
    change 2^(b.val-1)=2^(b.val-1)-1+1
    omega
end PEqualNP.Outside.Game1049

namespace PEqualNP.Outside.Game1049
open CircuitLowerBounds Chain1049 Clamp1049 Finset

private theorem clamped_row {n : Nat} (A B s : Finset (Fin n)) (h : Disjoint s A) (x : Fin n → Bool) :
    (∃ p ∈ s, clamp A B x p = true) ↔ ∃ p ∈ s ∩ B, x p = true := by
  constructor
  · rintro ⟨p,hp,hv⟩
    have ha := Finset.disjoint_left.mp h hp
    simp [clamp,ha] at hv
    exact ⟨p,Finset.mem_inter.mpr ⟨hp,hv.1⟩,hv.2⟩
  · rintro ⟨p,hp,hx⟩
    obtain ⟨hs,hb⟩ := Finset.mem_inter.mp hp
    exact ⟨p,hs,by simp [clamp,hb,hx]⟩

end PEqualNP.Outside.Game1049
open PEqualNP.Outside.Game1049 PEqualNP.Outside.Chain1049 PEqualNP.Outside.Clamp1049 in
theorem PEqualNP.Outside.L_meta_1049 : ∀ (h q n t : ℕ) (S : Fin n → Finset (Fin n)) (K : Fin (h + 1) → Finset (Fin n)), 1 ≤ h → q = 2 ^ h → n = q * q + q + 1 → (∀ i : Fin n, (S i).card = q + 1) → (∀ i j : Fin n, i ≠ j → (S i ∩ S j).card = 1) → (∀ p p' : Fin n, p ≠ p' → ∃ i : Fin n, p ∈ S i ∧ p' ∈ S i) → (∀ j : Fin (h + 1), (K j).card = (2 ^ (j : ℕ) - 1) * q + 2 ^ (j : ℕ)) → (∀ (j : Fin (h + 1)) (i : Fin n), (S i ∩ K j).card = 0 ∨ (S i ∩ K j).card = 2 ^ (j : ℕ)) → (∀ j j' : Fin (h + 1), j ≤ j' → K j ⊆ K j') → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin n → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin t → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin t, ι j = i) → (∀ (w : Fin n) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → (WithTop.untopD 0 (((Finset.range (h + 3)).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)).image (fun P : Finset ℕ => ((Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup (fun uv : ℕ × ℕ => ((if uv.1 = 0 then n else if uv.1 = h + 2 then 0 else q * (q + 1) / 2 ^ (uv.1 - 1) - q) - (if uv.2 = 0 then n else if uv.2 = h + 2 then 0 else q * (q + 1) / 2 ^ (uv.2 - 1) - q)) * (if uv.2 = h + 2 then q else 2 ^ (uv.2 - 1) - 1)))).min) ≤ gates.length := by
  intro h q n t S K hh hq hn hs hcross hpairs hk hvals hK gs out hg hc he
  classical
  let addr (i : Nat) : Fin (h+3) := ⟨min i (h+2),by omega⟩
  let X (i : Nat) (p : Fin n) := decide (p ∈ layer K (addr i))
  have hm (i j : Nat) (hij : i≤j) (p : Fin n) (hp : X i p = true) : X j p = true := by
    apply decide_eq_true
    exact layer_mono K hK (show addr i ≤ addr j from min_le_min_right _ hij) (of_decide_eq_true hp)
  obtain ⟨P,hP,cp,segments'⟩ := segments (h+3) t gs hg hc X hm
  apply (PEqualNP.Outside.Game1049.game_le h q n t P hP cp).trans
  apply Finset.sup_le
  intro uv huv
  obtain ⟨hr,hij,hcut⟩ := Finset.mem_filter.mp huv
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hr
  have hia := Finset.mem_range.mp ha
  have hib := Finset.mem_range.mp hb
  let a : Fin (h+3) := ⟨uv.1,hia⟩
  let b : Fin (h+3) := ⟨uv.2,hib⟩
  have ha' : addr uv.1 = a := Fin.ext (Nat.min_eq_left (by omega))
  have hb' : addr uv.2 = b := Fin.ext (Nat.min_eq_left (by omega))
  let A := layer K a
  let B := layer K b
  have sub : A ⊆ B := layer_mono K hK (show a ≤ b from hij)
  let I := misses S A \ misses S B
  have qpos : 0 < q := by rw [hq]; positivity
  have incidence := incident_card S hn qpos hs hcross hpairs
  have count := window_card S K hn incidence hs hk hvals hK a b (show a≤b from hij)
  change I.card = level h q n uv.1 - level h q n uv.2 at count
  change (level h q n uv.1 - level h q n uv.2) * factor h q uv.2 ≤ gs.length
  rw [← count]
  by_cases bz : b.val = 0
  · have hf : factor h q uv.2 = 0 := by change factor h q b.val = 0; simp [factor,bz]
    simp [hf]
  obtain ⟨ms,hlen,hmono,agrees⟩ := segments' uv.1 uv.2 hij hib hcut
  let L (i : Fin n) := S i ∩ B
  have size (i : Fin n) (hi : i ∈ I) : (L i).card = factor h q uv.2 + 1 :=
    hit_card S K hs hvals b i bz (Finset.mem_sdiff.mp hi).2
  have cross (i j : Fin n) (ne : i≠j) : (L i ∩ L j).card ≤ 1 := by
    apply le_trans (Finset.card_le_card (show L i ∩ L j ⊆ S i ∩ S j from
      fun _ hp => Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hp).1).1,
        (Finset.mem_inter.mp (Finset.mem_inter.mp hp).2).1⟩)) (hcross i j ne).le
  rw [← hlen]
  apply window A B I L size cross ms out hmono
  intro i hi x
  have lower (p : Fin n) (hp : X uv.1 p = true) : clamp A B x p = true := by
    change decide (p ∈ layer K (addr uv.1)) = true at hp
    rw [ha'] at hp
    have hpa : p ∈ A := of_decide_eq_true hp
    simp [clamp,hpa]
  have upper (p : Fin n) (hp : clamp A B x p = true) : X uv.2 p = true := by
    change decide (p ∈ layer K (addr uv.2)) = true
    rw [hb']; apply decide_eq_true
    simp [clamp] at hp
    exact hp.elim (fun h => sub h) (fun h => h.1)
  rw [agrees _ lower upper (out i),he]
  exact decide_eq_decide.mpr (clamped_row A B (S i) (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).2 x)
