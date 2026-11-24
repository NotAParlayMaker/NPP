import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.GetD
import Mathlib.Order.Interval.Finset.Nat
import PEqualNP.Defs

-- Wire evaluation and reverse-cut accounting are adapted from the checked L-meta-1460 proof.
-- That proof uses the L-meta-925 and L-meta-270 arguments.


open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1535

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

private def onePoint {n : ℕ} (p : Fin n) : Fin n → Bool := fun v => decide (v = p)

private def clean {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (r : ℕ) : Prop :=
  ∀ p : Fin n, value C (onePoint p) r = true → p ∈ S

private noncomputable def singletons {n : ℕ} (C : Circuit) (r : ℕ) : Finset (Fin n) :=
  open Classical in Finset.univ.filter (fun p => value C (onePoint p) r = true)

private lemma mem_singletons {n : ℕ} (C : Circuit) (r : ℕ) (p : Fin n) :
    p ∈ singletons (n := n) C r ↔ value C (onePoint p) r = true := by
  classical
  simp [singletons]

private def core {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (out k : ℕ) : Prop :=
  ∀ K : Set ℕ,
    (∀ j, j < C.gates.length → out = n+j → clean C S (n+j) → j ∈ K) →
    (∀ j ∈ K, ∀ (g : Gate) (i : ℕ), C.gates[j]? = some g →
      n+i ∈ g.inputs → i < j → clean C S (n+i) → i ∈ K) →
    k ∈ K

private def usable {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (out : ℕ)
    (y : Fin n → Bool) (r : ℕ) : Prop :=
  value C y r = false ∧ clean C S r ∧
    ∀ k, r = n+k → k < C.gates.length → core C S out k

private def hitsDirty {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (out : ℕ)
    (y : Fin n → Bool) : Prop :=
  ∀ r, (∃ (k : ℕ) (g : Gate), core C S out k ∧ C.gates[k]? = some g ∧
    g.op = .and ∧ r ∈ g.inputs ∧ r < n+k ∧ ¬ clean C S r) →
      ∃ p : Fin n, value C (onePoint p) r = true ∧ y p = true

private lemma usable_child {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (out : ℕ)
    (y : Fin n → Bool) {r k : ℕ} {g : Gate}
    (parent : core C S out k) (hg : C.gates[k]? = some g) (hr : r ∈ g.inputs) (early : r < n+k)
    (hf : value C y r = false) (hc : clean C S r) : usable C S out y r := by
  refine ⟨hf,hc,?_⟩
  intro j hj _
  subst r
  intro K hRoot hStep
  exact hStep k (parent K hRoot hStep) g j hg hr (by omega) hc

private noncomputable def charged {n : ℕ} (C : Circuit) (S : Finset (Fin n)) : Finset ℕ :=
  open Classical in
    (Finset.Ico n (n+C.gates.length)).filter
      (fun r => clean C S r ∧ 1 < (singletons (n := n) C r).card)

private lemma wide_is_gate {n : ℕ} (C : Circuit) (w : ℕ)
    (hwide : 1 < (singletons (n := n) C w).card) : n ≤ w ∧ w < n+C.gates.length := by
  classical
  constructor
  · by_contra! h
    let p : Fin n := ⟨w,h⟩
    have hs : singletons C w ⊆ ({p} : Finset (Fin n)) := by
      intro u hu
      have hv : value C (onePoint u) p = true := (mem_singletons C w u).mp hu
      rw [input_value] at hv
      have he : p = u := of_decide_eq_true hv
      exact Finset.mem_singleton.mpr he.symm
    have := Finset.card_le_card hs
    rw [Finset.card_singleton] at this
    omega
  · by_contra! h
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0 < (singletons (n := n) C w).card)
    have hv := (mem_singletons C w p).mp hp
    rw [missing_value C (onePoint p) w (by simpa only [Circuit.size] using h)] at hv
    cases hv

private lemma expand_clean {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (out : ℕ)
    (y : Fin n → Bool)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hit : hitsDirty C S out y) (w : ℕ) (ok : usable C S out y w)
    (hwide : 1 < (singletons (n := n) C w).card) :
    ∃ B : Finset ℕ, B.card ≤ 2 ∧ (1 < B.card → w ∈ charged C S) ∧
      (∀ r ∈ B, r < w ∧ usable C S out y r) ∧
      singletons (n := n) C w ⊆ B.biUnion (singletons (n := n) C) := by
  classical
  obtain ⟨hn,hw⟩ := wide_is_gate C w hwide
  let k := w-n
  have hk : k < C.gates.length := by unfold k; omega
  have he : w = n+k := by unfold k; omega
  let g := C.gates[k]
  have hg : C.gates[k]? = some g := List.getElem?_eq_getElem hk
  have hCore := ok.2.2 k he hk
  obtain ⟨hop,hlen⟩ := hG g (List.getElem_mem hk)
  let read (x : Fin n → Bool) (r : ℕ) : Bool := if r < w then value C x r else false
  have evalGate (x : Fin n → Bool) :
      value C x w = g.op.eval (g.inputs.map (read x)) :=
    gate_value C x w hn (by simpa only [Circuit.size] using hw)
  rcases hop with hand | hor
  · have andParents (x : Fin n → Bool) :
        value C x w = true ↔ ∀ r ∈ g.inputs, read x r = true := by
      rw [evalGate,hand]
      simp [GateOp.eval,List.all_eq_true]
    have hne : ¬ ∀ r ∈ g.inputs, read y r = true := by
      intro allTrue
      exact Bool.false_ne_true (ok.1.symm.trans ((andParents y).mpr allTrue))
    push Not at hne
    obtain ⟨r,hr,hfalse⟩ := hne
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0 < (singletons (n := n) C w).card)
    have hrTrue := (andParents (onePoint p)).mp ((mem_singletons C w p).mp hp) r hr
    have early : r < w := by
      by_contra h
      simp [read,h] at hrTrue
    have hf : value C y r = false := by
      simpa [read,early] using hfalse
    have hc : clean C S r := by
      by_contra hn
      obtain ⟨u,hu,hy⟩ := hit r ⟨k,g,hCore,hg,hand,hr,he ▸ early,hn⟩
      have hxy (v : Fin n) (hv : onePoint u v = true) : y v = true := by
        have h : v = u := of_decide_eq_true hv
        simpa [h] using hy
      exact Bool.false_ne_true (hf.symm.trans (value_mono C hG _ _ hxy r hu))
    refine ⟨{r},by simp,by simp,?_,?_⟩
    · intro s hs
      obtain rfl := Finset.mem_singleton.mp hs
      exact ⟨early, usable_child C S out y hCore hg hr (he ▸ early) hf hc⟩
    · intro u hu
      have hu' := (andParents (onePoint u)).mp ((mem_singletons C w u).mp hu) r hr
      exact Finset.mem_biUnion.mpr ⟨r,by simp,(mem_singletons C r u).mpr (by simpa [read,early] using hu')⟩
  · let B := g.inputs.toFinset.filter (· < w)
    have orParents (x : Fin n → Bool) :
        value C x w = true ↔ ∃ r ∈ g.inputs, read x r = true := by
      rw [evalGate,hor]
      simp [GateOp.eval,List.any_eq_true]
    refine ⟨B,(Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen),?_,?_,?_⟩
    · intro _
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hn,hw⟩,ok.2.1,hwide⟩
    · intro r hr
      obtain ⟨hmem,early⟩ := Finset.mem_filter.mp hr
      have hR := List.mem_toFinset.mp hmem
      have hf : value C y r = false := by
        apply Bool.eq_false_iff.mpr
        intro ht
        exact Bool.false_ne_true (ok.1.symm.trans
          ((orParents y).mpr ⟨r,hR,by simpa [read,early] using ht⟩))
      have hc : clean C S r := by
        intro p hp
        exact ok.2.1 p ((orParents (onePoint p)).mpr ⟨r,hR,by simpa [read,early] using hp⟩)
      exact ⟨early,usable_child C S out y hCore hg hR (he ▸ early) hf hc⟩
    · intro p hp
      obtain ⟨r,hr,ht⟩ := (orParents (onePoint p)).mp ((mem_singletons C w p).mp hp)
      have early : r < w := by
        by_contra hn
        simp [read,hn] at ht
      exact Finset.mem_biUnion.mpr ⟨r,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,early⟩,
        (mem_singletons C r p).mpr (by simpa [read,early] using ht)⟩



private lemma card_prefix (G : Finset ℕ) (t : ℕ) :
    (G.filter (· < t + 1)).card = (G.filter (· < t)).card + if t ∈ G then 1 else 0 := by
  classical
  by_cases ht : t ∈ G
  · have h : G.filter (· < t + 1) = insert t (G.filter (· < t)) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hw, hlt⟩
        by_cases he : w = t
        · exact Or.inl he
        · exact Or.inr ⟨hw, by omega⟩
      · rintro (rfl | ⟨hw, hlt⟩)
        · exact ⟨ht, by omega⟩
        · exact ⟨hw, by omega⟩
    rw [h, Finset.card_insert_of_notMem (by simp), ite_eq_left ht]
  · have h : G.filter (· < t + 1) = G.filter (· < t) := by
      ext w
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hw, hlt⟩
        have hne : w ≠ t := fun e => ht (e ▸ hw)
        exact ⟨hw, by omega⟩
      · rintro ⟨hw, hlt⟩
        exact ⟨hw, by omega⟩
    rw [h, ite_eq_right ht, Nat.add_zero]

-- Count each expanding wire at most once by processing the frontier in reverse order.
private lemma cut_card {α : Type*} [DecidableEq α]
    (P : ℕ → Finset α) (ok : ℕ → Prop) (G : Finset ℕ)
    (expandWire : ∀ w, ok w → 1 < (P w).card →
      ∃ B : Finset ℕ, B.card ≤ 2 ∧ (1 < B.card → w ∈ G) ∧
        (∀ r ∈ B, r < w ∧ ok r) ∧ P w ⊆ B.biUnion P)
    (t : ℕ) (F : Finset ℕ)
    (hF : ∀ w ∈ F, ok w ∧ (1 < (P w).card → w < t)) :
    (F.biUnion P).card ≤ F.card + (G.filter (· < t)).card := by
  classical
  induction t generalizing F with
  | zero =>
    apply (Finset.card_biUnion_le_card_mul F P 1 ?_).trans
    · simp
    · intro r hr
      have h := (hF r hr).2
      omega
  | succ t ih =>
    by_cases ht : t ∈ F ∧ 1 < (P t).card
    · obtain ⟨B, hBcard, hcharge, hB, hcover⟩ := expandWire t (hF t ht.1).1 ht.2
      let F' := F.erase t ∪ B
      have hF' : ∀ w ∈ F', ok w ∧ (1 < (P w).card → w < t) := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
          have ⟨hok, hlt⟩ := hF w hmem
          exact ⟨hok, fun h => by have := hlt h; omega⟩
        · exact ⟨(hB w hw).2, fun _ => (hB w hw).1⟩
      have hU : F.biUnion P ⊆ F'.biUnion P := by
        intro p hp
        obtain ⟨w, hw, hpw⟩ := Finset.mem_biUnion.mp hp
        by_cases h : w = t
        · subst w
          obtain ⟨r, hr, hpr⟩ := Finset.mem_biUnion.mp (hcover hpw)
          exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_union_right _ hr, hpr⟩
        · exact Finset.mem_biUnion.mpr
            ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩), hpw⟩
      have hsize := Finset.card_union_le (F.erase t) B
      change F'.card ≤ _ at hsize
      have he := Finset.card_erase_add_one ht.1
      have hh := (Finset.card_le_card hU).trans (ih F' hF')
      rw [card_prefix]
      by_cases hg : t ∈ G
      · simp only [ite_eq_left hg]
        omega
      · simp only [ite_eq_right hg]
        have : B.card ≤ 1 := by by_contra! hl; exact hg (hcharge hl)
        omega
    · have hFt : ∀ w ∈ F, ok w ∧ (1 < (P w).card → w < t) := by
        intro w hw
        refine ⟨(hF w hw).1, fun h => ?_⟩
        have hne : w ≠ t := fun e => ht ⟨e ▸ hw, e ▸ h⟩
        have := (hF w hw).2 h
        omega
      have hh := ih F hFt
      rw [card_prefix]
      omega

private theorem count_clean {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (out : Fin m → ℕ)
    (hInter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hOut : ∀ (i : Fin m) (u : Fin n), value C (onePoint u) (out i) = true ↔ u ∈ S i)
    (hRows : ∀ i : Fin m, ∃ y : Fin n → Bool,
      value C y (out i) = false ∧ hitsDirty C (S i) (out i) y) :
    ∑ i : Fin m, (S i).card ≤
      C.gates.length + (Finset.univ.filter (fun i : Fin m => (S i).Nonempty)).card := by
  classical
  let G (i : Fin m) := charged C (S i)
  have support (i : Fin m) : singletons C (out i) = S i :=
    Finset.ext fun p => (mem_singletons C (out i) p).trans (hOut i p)
  have per_line (i : Fin m) :
      (S i).card ≤ (G i).card + if (S i).Nonempty then 1 else 0 := by
    by_cases hi : (S i).Nonempty
    · rw [ite_eq_left hi]
      obtain ⟨y,hFalse,hDirty⟩ := hRows i
      have hc : clean C (S i) (out i) := fun p hp => (hOut i p).mp hp
      have root : usable C (S i) (out i) y (out i) := by
        refine ⟨hFalse,hc,?_⟩
        intro k he hk K hRoot _
        exact hRoot k hk he (he ▸ hc)
      have bound := cut_card (singletons (n := n) C) (usable C (S i) (out i) y) (G i)
        (expand_clean C (S i) (out i) y hG hDirty) (out i+1) {out i} (by
          intro w hw
          obtain rfl := Finset.mem_singleton.mp hw
          exact ⟨root, by omega⟩)
      rw [Finset.singleton_biUnion,Finset.card_singleton,support] at bound
      have hf := Finset.card_filter_le (G i) (· < out i+1)
      omega
    · have hempty := Finset.not_nonempty_iff_eq_empty.mp hi
      simp [hempty]
  have disj : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ j _ hij
    change Disjoint (G i) (G j)
    rw [Finset.disjoint_left]
    intro r hi hj
    have ha := (Finset.mem_filter.mp hi).2
    have hb := (Finset.mem_filter.mp hj).2
    have hSub : singletons (n := n) C r ⊆ S i ∩ S j := by
      intro p hp
      have ht := (mem_singletons C r p).mp hp
      exact Finset.mem_inter.mpr ⟨ha.1 p ht,hb.1 p ht⟩
    have hcard := (Finset.card_le_card hSub).trans (hInter i j hij)
    exact (not_lt_of_ge hcard) ha.2
  have hAll : Finset.univ.biUnion G ⊆ Finset.Ico n (n+C.gates.length) := by
    intro r hr
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hr
    exact (Finset.mem_filter.mp hi).1
  have hSum : ∑ i : Fin m, (G i).card ≤ C.gates.length := by
    rw [← Finset.card_biUnion disj]
    exact (Finset.card_le_card hAll).trans (by simp)
  calc
    ∑ i : Fin m, (S i).card ≤
        ∑ i : Fin m, ((G i).card + if (S i).Nonempty then 1 else 0) :=
      Finset.sum_le_sum (fun i _ => per_line i)
    _ = (∑ i : Fin m, (G i).card) +
        (Finset.univ.filter (fun i : Fin m => (S i).Nonempty)).card := by
      simp only [Finset.sum_add_distrib,Finset.sum_boole,Nat.cast_id]
    _ ≤ _ := Nat.add_le_add_right hSum _

end PEqualNP.Outside.L_meta_1535


theorem PEqualNP.Outside.L_meta_1535 :
    ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ ak : ℕ, ak < gates.length → (Finset.univ.filter (fun au : Fin n => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun auk : Fin n => decide (auk = au)))).getD (n + ak) false = true)).card ≤ 1 → ∀ ax : Fin n → Bool, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn ax)).getD (n + ak) false = decide (∃ av : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun avk : Fin n => decide (avk = av)))).getD (n + ak) false = true ∧ ax av = true)) → (∀ (w : Fin m) (u : Fin n), (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun uk : Fin n => decide (uk = u)))).getD (out w) false = true ↔ u ∈ S w) → (∀ w0 : Fin m, ∃ y : Fin n → Bool, (∀ u3 ∈ S w0, y u3 = false) ∧ (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn y)).getD (out w0) false = false ∧ ∀ bw : ℕ, (∃ (bk : ℕ) (bg : PEqualNP.CircuitLowerBounds.Gate), (∀ bK : Set ℕ, (∀ bk0 : ℕ, bk0 < gates.length → out w0 = n + bk0 → (∀ bu0 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun bu0k : Fin n => decide (bu0k = bu0)))).getD (n + bk0) false = true → bu0 ∈ S w0) → bk0 ∈ bK) → (∀ bk1 ∈ bK, ∀ (bg1 : PEqualNP.CircuitLowerBounds.Gate) (bk2 : ℕ), gates[bk1]? = some bg1 → n + bk2 ∈ bg1.inputs → bk2 < bk1 → (∀ bu1 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun bu1k : Fin n => decide (bu1k = bu1)))).getD (n + bk2) false = true → bu1 ∈ S w0) → bk2 ∈ bK) → bk ∈ bK) ∧ gates[bk]? = some bg ∧ bg.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ bw ∈ bg.inputs ∧ bw < n + bk ∧ ¬ (∀ bu2 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun bu2k : Fin n => decide (bu2k = bu2)))).getD (bw) false = true → bu2 ∈ S w0)) → ∃ u4 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u4k : Fin n => decide (u4k = u4)))).getD (bw) false = true ∧ y u4 = true) → ∑ w1 : Fin m, (S w1).card ≤ gates.length + (Finset.univ.filter (fun w5 : Fin m => (S w5).Nonempty)).card := by
  intro n m S gates out hInter hG _hNormalize hOut hRows
  let C : Circuit := ⟨gates,0⟩
  apply PEqualNP.Outside.L_meta_1535.count_clean S C out hInter hG hOut
  intro i
  obtain ⟨y,_,hFalse,hHit⟩ := hRows i
  exact ⟨y,hFalse,hHit⟩
