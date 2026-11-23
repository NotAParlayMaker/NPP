import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_1374

open PEqualNP.CircuitLowerBounds

-- Wire evaluation and singleton supports follow the checked proof of L-meta-986.

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
  · exact fun r hr => (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have step (r) (hr : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,h⟩)
      · simp [h]
    have form (z : Fin n → Bool) :
        value C z w = g.op.eval (g.inputs.map fun r => if r < w then value C z r else false) :=
      gate_value C z w hn hw
    rw [form x] at hx
    rw [form y]
    rcases hop with hop|hop
    · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r,hr,rfl⟩ := hb
      exact step r hr (hx _ ⟨r,hr,rfl⟩)
    · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
      obtain ⟨b,⟨r,hr,rfl⟩,hv⟩ := hx
      exact ⟨_, ⟨r,hr,rfl⟩, step r hr hv⟩

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

abbrev good (C : Circuit) := ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2


-- Replace one wide wire in a frontier by its earlier witnesses. A branching
-- replacement costs one gate. A single predecessor costs nothing.
lemma frontier {α : Type*} [DecidableEq α] (U : ℕ → Finset α) (paid : Finset ℕ)
    (step : ∀ w, 1 < (U w).card → ∃ P : Finset ℕ,
      (∀ r ∈ P, r < w) ∧ U w ⊆ P.biUnion U ∧
      P.card ≤ 1 + (if w ∈ paid then 1 else 0)) (t : ℕ) (F : Finset ℕ)
    (ht : ∀ w ∈ F, 1 < (U w).card → w < t) :
    (F.biUnion U).card ≤ F.card + (paid.filter (· < t)).card := by
  classical
  induction t generalizing F with
  | zero =>
    have h := Finset.card_biUnion_le_card_mul F U 1 (fun w hw => by
      by_contra! h
      exact Nat.not_lt_zero _ (ht w hw h))
    simpa using h
  | succ t ih =>
    by_cases h : t ∈ F ∧ 1 < (U t).card
    · obtain ⟨P, hp, hcover, hsize⟩ := step t h.2
      let F' := F.erase t ∪ P
      have hnext : ∀ w ∈ F', 1 < (U w).card → w < t := by
        intro w hw hwide
        rcases Finset.mem_union.mp hw with hold | hnew
        · obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hold
          have := ht w hmem hwide
          omega
        · exact hp _ hnew
      have hsub : F.biUnion U ⊆ F'.biUnion U := by
        intro a ha
        obtain ⟨w, hw, ha⟩ := Finset.mem_biUnion.mp ha
        by_cases he : w = t
        · subst w
          obtain ⟨r, hr, har⟩ := Finset.mem_biUnion.mp (hcover ha)
          exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_union_right _ hr, har⟩
        · exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he, hw⟩), ha⟩
      have hc := Finset.card_le_card hsub
      have hr := ih F' hnext
      have hu : F'.card ≤ (F.erase t).card + P.card := Finset.card_union_le ..
      have he := Finset.card_erase_add_one h.1
      by_cases htmem : t ∈ paid
      · have hmore : insert t (paid.filter (· < t)) ⊆ paid.filter (· < t+1) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact Finset.mem_filter.mpr ⟨htmem, by omega⟩
          · obtain ⟨hw, hlt⟩ := Finset.mem_filter.mp hw
            exact Finset.mem_filter.mpr ⟨hw, by omega⟩
        have hin := Finset.card_le_card hmore
        rw [Finset.card_insert_of_notMem (by simp)] at hin
        simp [htmem] at hsize
        omega
      · have hmore : paid.filter (· < t) ⊆ paid.filter (· < t+1) := by
          intro w hw
          obtain ⟨hw, hlt⟩ := Finset.mem_filter.mp hw
          exact Finset.mem_filter.mpr ⟨hw, by omega⟩
        have hin := Finset.card_le_card hmore
        simp [htmem] at hsize
        omega
    · have hnext : ∀ w ∈ F, 1 < (U w).card → w < t := by
        intro w hw hwide
        have hlt := ht w hw hwide
        have hne : w ≠ t := by rintro rfl; exact h ⟨hw,hwide⟩
        omega
      exact (ih F hnext).trans (Nat.add_le_add_left (Finset.card_le_card (by
        intro w hw
        obtain ⟨hw,hlt⟩ := Finset.mem_filter.mp hw
        exact Finset.mem_filter.mpr ⟨hw, by omega⟩)) _)

lemma countWire {α : Type*} [DecidableEq α] (U : ℕ → Finset α) (paid : Finset ℕ)
    (step : ∀ w, 1 < (U w).card → ∃ P : Finset ℕ,
      (∀ r ∈ P, r < w) ∧ U w ⊆ P.biUnion U ∧
      P.card ≤ 1 + (if w ∈ paid then 1 else 0)) (o : ℕ) :
    (U o).card ≤ 1 + paid.card := by
  have h := frontier U paid step (o+1) {o} (by
    intro w hw _
    have : w = o := Finset.mem_singleton.mp hw
    omega)
  simpa using h.trans (Nat.add_le_add_left (Finset.card_filter_le ..) _)

def isAnd (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  ∃ g, C.gates[w-n]? = some g ∧ g.op = GateOp.and

-- On a wide wire the gate has genuine earlier inputs. OR takes their union.
-- At an AND, any false input on the reference assignment can be followed.
lemma gateForm {n : ℕ} (C : Circuit) (hg : good C) (w : ℕ)
    (hwide : 1 < (support (n := n) C w).card) :
    ∃ P : Finset ℕ, (∀ r ∈ P, r < w) ∧ P.card ≤ 2 ∧
      ((isAnd n C w ∧ ∀ x : Fin n → Bool,
          value C x w = true ↔ ∀ r ∈ P, value C x r = true) ∨
       (¬ isAnd n C w ∧ ∀ x : Fin n → Bool,
          value C x w = true ↔ ∃ r ∈ P, value C x r = true)) := by
  obtain ⟨hn, hw⟩ := support_gate C w hwide
  have hj : w-n < C.gates.length := by unfold Circuit.size at hw; omega
  let g := C.gates[w-n]
  have he : C.gates[w-n]? = some g := List.getElem?_eq_getElem hj
  obtain ⟨hop,hlen⟩ := hg g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, fun r hr => (Finset.mem_filter.mp hr).2,
    (Finset.card_filter_le ..).trans ((List.toFinset_card_le _).trans hlen), ?_⟩
  have form (x : Fin n → Bool) :
      value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) :=
    gate_value C x w hn hw
  rcases hop with ha | ho
  · refine Or.inl ⟨⟨g,he,ha⟩, ?_⟩
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0 < (support (n:=n) C w).card)
    have ht := (mem_support C w p).mp hp
    rw [form,ha] at ht
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at ht
    have prior (r) (hr : r ∈ g.inputs) : r < w := by
      have t := ht _ ⟨r,hr,rfl⟩
      by_contra hh
      simp [hh] at t
    intro x
    rw [form,ha]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    constructor
    · intro h r hr
      obtain ⟨hm, hlt⟩ := Finset.mem_filter.mp hr
      simpa [hlt] using h _ ⟨r,List.mem_toFinset.mp hm,rfl⟩
    · intro h b hb
      obtain ⟨r,hr,rfl⟩ := hb
      simpa [prior r hr] using h r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,prior r hr⟩)
  · refine Or.inr ⟨?_, ?_⟩
    · rintro ⟨g', hh, ha⟩
      rw [he] at hh
      cases hh
      simp [ho] at ha
    · intro x
      rw [form,ho]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
      constructor
      · rintro ⟨_,⟨r,hr,rfl⟩,ht⟩
        split at ht
        next h => exact ⟨r,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,h⟩,ht⟩
        next => contradiction
      · rintro ⟨r,hr,ht⟩
        have hlt := (Finset.mem_filter.mp hr).2
        exact ⟨_,⟨r,List.mem_toFinset.mp (Finset.mem_filter.mp hr).1,rfl⟩,by simpa [hlt] using ht⟩


-- A wire can be charged to a line if at least two singleton witnesses
-- identify that line, either among all points or just among points off R.
def charges {n : ℕ} (C : Circuit) (R S : Finset (Fin n)) : Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter fun w =>
    (support C w ⊆ S ∧ 1 < (support (n:=n) C w).card) ∨
    (support C w \ R ⊆ S ∧ 1 < (support C w \ R).card)

lemma fullCharge {n : ℕ} (C : Circuit) (R S : Finset (Fin n)) (w : ℕ)
    (hs : support C w ⊆ S) (hw : 1 < (support (n:=n) C w).card) : w ∈ charges C R S :=
  Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (support_gate C w hw), Or.inl ⟨hs,hw⟩⟩

lemma incompatible {α : Type*} [DecidableEq α] {A B U : Finset α}
    (h : (A ∩ B).card ≤ 1) (ha : U ⊆ A) (hb : U ⊆ B) (hc : 1 < U.card) : False := by
  have bound := Finset.card_le_card (Finset.subset_inter ha hb)
  omega

lemma separate {n : ℕ} (C : Circuit) (R A B : Finset (Fin n)) (hab : (A ∩ B).card ≤ 1) :
    Disjoint (charges C R A) (charges C R B) := by
  rw [Finset.disjoint_left]
  intro w ha hb
  have sub : support C w \ R ⊆ support C w := Finset.sdiff_subset
  rcases (Finset.mem_filter.mp ha).2 with ⟨a,ac⟩ | ⟨a,ac⟩ <;>
    rcases (Finset.mem_filter.mp hb).2 with ⟨b,bc⟩ | ⟨b,bc⟩
  · exact incompatible hab a b ac
  · exact incompatible hab (sub.trans a) b bc
  · exact incompatible hab a (sub.trans b) ac
  · exact incompatible hab a b ac

-- If a line has no AND with two private singleton witnesses, every safe wide
-- wire is an OR. Tracing these ORs back accounts for the entire line.
lemma fullRow {n : ℕ} (C : Circuit) (hg : good C) (R S : Finset (Fin n)) (o : ℕ)
    (hout : support C o = S)
    (hno : ∀ w ∈ charges C R S, ¬ isAnd n C w) :
    S.card ≤ 1 + (charges C R S).card := by
  classical
  let U : ℕ → Finset (Fin n) := fun w => if support C w ⊆ S then support C w else ∅
  have step (w : ℕ) (hw : 1 < (U w).card) : ∃ P : Finset ℕ,
      (∀ r ∈ P, r < w) ∧ U w ⊆ P.biUnion U ∧
      P.card ≤ 1 + (if w ∈ charges C R S then 1 else 0) := by
    have hs : support C w ⊆ S := by by_contra h; simp [U,h] at hw
    have wide : 1 < (support (n:=n) C w).card := by simpa [U,hs] using hw
    have paid := fullCharge C R S w hs wide
    obtain ⟨P, hprior, hc, hand | hor⟩ := gateForm C hg w wide
    · exact False.elim (hno w paid hand.1)
    · refine ⟨P, hprior, ?_, by simpa [paid] using hc⟩
      have sub (r) (hr : r ∈ P) : support (n:=n) C r ⊆ support C w := by
        intro p hp
        exact (mem_support C w p).mpr ((hor.2 _).mpr ⟨r,hr,(mem_support C r p).mp hp⟩)
      intro p hp
      have hmem : p ∈ support C w := by simpa [U,hs] using hp
      obtain ⟨r,hr,ht⟩ := (hor.2 _).mp ((mem_support C w p).mp hmem)
      refine Finset.mem_biUnion.mpr ⟨r,hr,?_⟩
      simpa [U,(sub r hr).trans hs] using (mem_support C r p).mpr ht
  simpa [U,hout] using countWire U (charges C R S) step o

def outside {n : ℕ} (R S : Finset (Fin n)) : Fin n → Bool :=
  fun p => decide (p ∉ R ∧ p ∉ S)

-- Off R, use the input that selects every point outside the line. An AND
-- that is false there has a false parent, so tracing it needs no new branch.
open Classical in
lemma offRow {n : ℕ} (C : Circuit) (hg : good C) (R S : Finset (Fin n)) (o : ℕ)
    (hout : support C o = S) (hz : value C (outside R S) o = false) :
    (S \ R).card ≤ 1 + ((charges C R S).filter fun w => ¬ isAnd n C w).card := by
  classical
  let y := outside R S
  let U := fun w => if value C y w = false then support C w \ R else ∅
  let A := (charges C R S).filter fun w => ¬ isAnd n C w
  have step (w : ℕ) (hw : 1 < (U w).card) : ∃ P : Finset ℕ,
      (∀ r ∈ P, r < w) ∧ U w ⊆ P.biUnion U ∧
      P.card ≤ 1 + (if w ∈ A then 1 else 0) := by
    have hfalse : value C y w = false := by by_contra h; simp [U,h] at hw
    have hcold : 1 < (support C w \ R).card := by simpa [U,hfalse] using hw
    have wide : 1 < (support (n:=n) C w).card :=
      lt_of_lt_of_le hcold (Finset.card_le_card Finset.sdiff_subset)
    have hs : support C w \ R ⊆ S := by
      intro p hp
      obtain ⟨hpos,hr⟩ := Finset.mem_sdiff.mp hp
      by_contra hns
      have hm := value_mono C hg (fun r => decide (r = p)) y (by
        intro r he
        have heq : r = p := of_decide_eq_true he
        subst r
        simp [y,outside,hr,hns]) w ((mem_support C w p).mp hpos)
      simp [hfalse] at hm
    have inCharge : w ∈ charges C R S :=
      Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (support_gate C w wide),Or.inr ⟨hs,hcold⟩⟩
    obtain ⟨P, hprior, hc, hand | hor⟩ := gateForm C hg w wide
    · have miss : ∃ r ∈ P, value C y r = false := by
        by_contra! h
        have hbad := (hand.2 y).mpr (fun r hr => by simpa using h r hr)
        simp [hfalse] at hbad
      obtain ⟨r,hr,hf⟩ := miss
      refine ⟨{r}, by simpa using hprior r hr, ?_, by simp⟩
      simp only [Finset.singleton_biUnion]
      intro p hp
      have hmem : p ∈ support C w \ R := by simpa [U,hfalse] using hp
      obtain ⟨hpw,hnr⟩ := Finset.mem_sdiff.mp hmem
      have hpr := (mem_support C r p).mpr (((hand.2 _).mp ((mem_support C w p).mp hpw)) r hr)
      simpa [U,hf] using Finset.mem_sdiff.mpr (⟨hpr,hnr⟩ : p ∈ support C r ∧ p ∉ R)
    · have paid : w ∈ A := Finset.mem_filter.mpr ⟨inCharge, hor.1⟩
      refine ⟨P, hprior, ?_, by simpa [paid] using hc⟩
      intro p hp
      have hmem : p ∈ support C w \ R := by simpa [U,hfalse] using hp
      obtain ⟨hpw,hnr⟩ := Finset.mem_sdiff.mp hmem
      obtain ⟨r,hr,ht⟩ := (hor.2 _).mp ((mem_support C w p).mp hpw)
      have hf : value C y r = false := by
        apply Bool.eq_false_iff.mpr
        intro hy
        have hbad := (hor.2 y).mpr ⟨r,hr,hy⟩
        simp [hfalse] at hbad
      refine Finset.mem_biUnion.mpr ⟨r,hr,?_⟩
      have hsr := (mem_support C r p).mpr ht
      simpa [U,hf] using Finset.mem_sdiff.mpr (⟨hsr,hnr⟩ : p ∈ support C r ∧ p ∉ R)
  simpa [U,y,hz,hout,A] using countWire U A step o


open Classical in
lemma rowBound {n q : ℕ} (C : Circuit) (hg : good C) (R S : Finset (Fin n)) (o : ℕ)
    (hsize : S.card = q + 1) (hout : support C o = S) (hz : value C (outside R S) o = false) :
    q ≤ (charges C R S).card + ((S ∩ R).card - 1) := by
  classical
  by_cases has : ∃ w ∈ charges C R S, isAnd n C w
  · obtain ⟨z,hzmem,hzand⟩ := has
    have h := offRow C hg R S o hout hz
    have hsub : ((charges C R S).filter fun w => ¬ isAnd n C w) ⊆ (charges C R S).erase z := by
      intro w hw
      obtain ⟨hw,hno⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_erase.mpr ⟨fun eq => hno (eq ▸ hzand), hw⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_erase_add_one hzmem
    have h3 := Finset.card_sdiff_add_card_inter S R
    omega
  · have h := fullRow C hg R S o hout (by simpa using has)
    omega

end PEqualNP.Outside.L_meta_1374

open PEqualNP.Outside.L_meta_1374 in
theorem PEqualNP.Outside.L_meta_1374 : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n)) (R : Finset (Fin n)),
    2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      ((∀ v ∈ R, x v = false) ∨ (∃ p ∈ R, ∀ v : Fin n, x v = decide (v = p))) →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
        decide (∃ v ∈ S w, x v = true)) →
    m * q ≤ gates.length + ∑ i : Fin m, ((S i ∩ R).card - 1) := by
  classical
  intro q n m S R _hq hsize hlinear gates out hg hcorrect
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates,0⟩
  have hsupport (i : Fin m) : support C (out i) = S i := by
    ext p
    let x : Fin n → Bool := fun v => decide (v = p)
    have htest : (∀ v ∈ R, x v = false) ∨ (∃ r ∈ R, ∀ v, x v = decide (v = r)) := by
      by_cases hp : p ∈ R
      · exact Or.inr ⟨p,hp,fun _ => rfl⟩
      · exact Or.inl (fun v hv => by
          have hne : v ≠ p := by rintro rfl; exact hp hv
          simp [x,hne])
    have he : value C x (out i) = decide (∃ v ∈ S i, x v = true) := hcorrect i x htest
    rw [mem_support]
    change value C x (out i) = true ↔ p ∈ S i
    simp [he,x]
  have hzero (i : Fin m) : value C (outside R (S i)) (out i) = false := by
    have he := hcorrect i (outside R (S i)) (Or.inl (by
      intro v hv
      simp [outside,hv]))
    change value C (outside R (S i)) (out i) = _ at he
    rw [he, decide_eq_false_iff_not]
    rintro ⟨v,hv,htrue⟩
    simp [outside,hv] at htrue
  let A := fun i => charges C R (S i)
  have hrow (i : Fin m) : q ≤ (A i).card + ((S i ∩ R).card - 1) :=
    rowBound C hg R (S i) (out i) (hsize i) (hsupport i) (hzero i)
  have hd : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint A :=
    fun i _ j _ hij => separate C R (S i) (S j) (hlinear i j hij)
  have hsub : Finset.univ.biUnion A ⊆ Finset.Ico n (n + C.size) := by
    intro w hw
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hw
    exact (Finset.mem_filter.mp hi).1
  have htotal := Finset.card_le_card hsub
  rw [Finset.card_biUnion hd] at htotal
  have hcount : ∑ i, (A i).card ≤ gates.length := by
    simpa [C,PEqualNP.CircuitLowerBounds.Circuit.size] using htotal
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  exact hsum.trans (Nat.add_le_add_right hcount _)
