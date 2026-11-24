import Mathlib
import PEqualNP.Defs

-- The circuit branching argument adapts the checked L_meta_1483 proof to pair correctness.

namespace PEqualNP.Outside.L_meta_2988_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

def Next (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ ∃ p g, C.gates[p]? = some g ∧ b = n+p ∧ a ∈ g.inputs

def Live (n : ℕ) (C : Circuit) (i : ℕ) : Prop :=
  ReflTransGen (Next n C) i C.output

def LNext (n : ℕ) (C : Circuit) (a b : ℕ) : Prop := Next n C a b ∧ Live n C b

def Trace (n : ℕ) (C : Circuit) (P : ℕ → Prop) (i j : ℕ) : Prop :=
  ReflTransGen (fun a b => P a ∧ LNext n C a b) i j

theorem next_le {n : ℕ} {C : Circuit} {a b : ℕ} (h : ReflTransGen (Next n C) a b) :
    a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.1.le

theorem trace_le {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.2.1.1.le

theorem live_before {n : ℕ} {C : Circuit} {a b : ℕ} (hn : Next n C a b) (h : Live n C b) :
    Live n C a := (ReflTransGen.single hn).trans h

theorem trace_start {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) (hb : P b) : P a := by
  rcases h.cases_head with rfl | ⟨_, hs, _⟩
  · exact hb
  · exact hs.1

theorem align {n : ℕ} {C : Circuit} {P Q : ℕ → Prop} {v b : ℕ}
    (p : Trace n C P v b)
    (unique : ∀ a j j', a < b → P a → LNext n C a j → LNext n C a j' → j = j') :
    ∀ d, Trace n C Q v d → (d < b ∧ P d) ∨ Trace n C Q b d := by
  induction p using ReflTransGen.head_induction_on with
  | refl =>
    intro d q
    exact Or.inr q
  | head hp pt ih =>
    intro d q
    have hlt := hp.2.1.1.trans_le (trace_le pt)
    rcases q.cases_head with rfl | ⟨j, hq, qt⟩
    · exact Or.inl ⟨hlt, hp.1⟩
    · have e := unique _ _ _ hlt hp.1 hp.2 hq.2
      subst j
      exact ih _ qt

theorem difference {n : ℕ} (C : Circuit) (x y : Fin n → Bool) :
    ∀ j, Live n C j → val C x j ≠ val C y j →
      ∃ i : Fin n, x i ≠ y i ∧ Trace n C (fun a => val C x a ≠ val C y a) i.val j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hd
    by_cases hin : j < n
    · let i : Fin n := ⟨j,hin⟩
      exact ⟨i, by simpa only [← val_input C x i, ← val_input C y i] using hd, .refl⟩
    have hb : j < n+C.gates.length := by
      by_contra! he
      exact hd ((val_beyond C x he).trans (val_beyond C y he).symm)
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hdiff : ∃ i ∈ g.inputs, i < n+p ∧ val C x i ≠ val C y i := by
      by_contra! hn
      apply hd
      rw [val_gate C x hg, val_gate C y hg]
      apply congrArg _
      apply List.map_congr_left
      intro i hi
      by_cases hj : i < n+p
      · simp [operand, hj, hn i hi hj]
      · simp [operand, hj]
    obtain ⟨a, ha, hlt, ha'⟩ := hdiff
    have hs : Next n C a (n+p) := ⟨hlt,p,g,hg,rfl,ha⟩
    obtain ⟨i, hi, hpath⟩ := ih a hlt (live_before hs hj) ha'
    exact ⟨i, hi, hpath.tail ⟨ha',hs,hj⟩⟩

end PEqualNP.Outside.L_meta_2988_aux


namespace PEqualNP.Outside.L_meta_2988_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit}

theorem acts_mono (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ j, val C x j = true → val C y j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    by_cases hin : j < n
    · let i : Fin n := ⟨j, hin⟩
      simpa only [← val_input C x i, ← val_input C y i] using hxy i (by
        simpa only [← val_input C x i] using hj)
    by_cases hgt : n + C.gates.length ≤ j
    · rw [val_beyond C x hgt] at hj
      contradiction
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hgate := (hC g (List.mem_of_getElem? hg)).1
    have hm (a : ℕ) : operand C x (n+p) a = true → operand C y (n+p) a = true := by
      by_cases ha : a < n+p
      · simp only [operand, ite_eq_left ha]
        exact ih a ha
      · simp [operand, ha]
    rw [val_gate C x hg] at hj
    rw [val_gate C y hg]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgate
    rcases hgate with h | h
    · simp only [h, GateOp.eval, List.all_map, Function.comp_apply, id, List.all_eq_true] at hj ⊢
      exact fun a ha => hm a (hj a ha)
    · simp only [h, GateOp.eval, List.any_map, Function.comp_apply, id, List.any_eq_true] at hj ⊢
      obtain ⟨a, ha, he⟩ := hj
      exact ⟨a, ha, hm a he⟩

def point (s : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ s)

theorem point_mono {s t : Finset (Fin n)} (h : s ⊆ t) :
    ∀ i, point s i = true → point t i = true := by
  intro i hi
  simpa only [point, decide_eq_true_eq] using h (by simpa only [point, decide_eq_true_eq] using hi)

theorem point_insert {s : Finset (Fin n)} {v u : Fin n} (h : u ≠ v) :
    point (insert v s) u = point s u := by simp [point, h]

def Carries (C : Circuit) (v : Fin n) (a : ℕ) : Prop :=
  val C (point {v}) a ≠ val C (point (∅ : Finset (Fin n))) a

theorem carries_iff (hC : Monotone2 C) {v : Fin n} {a : ℕ} :
    Carries C v a ↔
      val C (point {v}) a = true ∧ val C (point (∅ : Finset (Fin n))) a = false := by
  have hm := acts_mono hC (point_mono (Finset.empty_subset {v})) a
  unfold Carries
  cases ha : val C (point {v}) a <;>
    cases hb : val C (point (∅ : Finset (Fin n))) a <;> simp_all

theorem singleton_path {v : Fin n} {a : ℕ} (ha : Live n C a) (hd : Carries C v a) :
    Trace n C (Carries C v) v.val a := by
  obtain ⟨i, hi, hpath⟩ := difference C (point {v}) (point ∅) a ha hd
  have e : i = v := by
    by_contra h
    exact hi (by simp [point, h])
  exact e ▸ hpath

theorem influence {v : Fin n} {P : ℕ → Prop} {b j : ℕ} {x y : Fin n → Bool}
    (path : Trace n C P v.val b)
    (unique : ∀ a k k', a < b → P a → LNext n C a k → LNext n C a k' → k = k')
    (agrees : ∀ i, i ≠ v → x i = y i) (hj : Live n C j) (hd : val C x j ≠ val C y j) :
    (j < b ∧ P j) ∨ (b ≤ j ∧ val C x b ≠ val C y b) := by
  obtain ⟨i, hi, trace⟩ := difference C x y j hj hd
  have e : i = v := by
    by_contra h
    exact hi (agrees i h)
  subst i
  rcases align path unique j trace with ha | hb
  · exact Or.inl ha
  · exact Or.inr ⟨trace_le hb, trace_start hb hd⟩

noncomputable def readers (n : ℕ) (C : Circuit) (a : ℕ) : Finset ℕ :=
  open Classical in (Finset.range (n+C.gates.length)).filter (fun b => LNext n C a b)

theorem next_in_range {a b : ℕ} (h : Next n C a b) : b < n+C.gates.length := by
  obtain ⟨_,p,g,hg,rfl,_⟩ := h
  exact Nat.add_lt_add_left (List.getElem?_eq_some_iff.1 hg).1 n

theorem mem_readers {a b : ℕ} : b ∈ readers n C a ↔ LNext n C a b := by
  classical
  unfold readers
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨next_in_range h.1, h⟩⟩

def Branch (n : ℕ) (C : Circuit) (a : ℕ) : Prop := 2 ≤ (readers n C a).card

theorem nonbranch_unique {a j j' : ℕ} (h : ¬ Branch n C a)
    (hj : LNext n C a j) (hj' : LNext n C a j') : j = j' := by
  apply Finset.card_le_one_iff.1 (show (readers n C a).card ≤ 1 from by
    unfold Branch at h; omega) (mem_readers.2 hj) (mem_readers.2 hj')

def Eligible (C : Circuit) (v : Fin n) : Prop := ∃ b, Live n C b ∧ Carries C v b ∧ Branch n C b

noncomputable def firstBranch (C : Circuit) (v : Fin n) (h : Eligible C v) : ℕ := by
  classical exact Nat.find h

theorem firstBranch_spec (v : Fin n) (h : Eligible C v) :
    Live n C (firstBranch C v h) ∧ Carries C v (firstBranch C v h) ∧ Branch n C (firstBranch C v h) := by
  classical exact Nat.find_spec h

theorem firstBranch_unique (v : Fin n) (h : Eligible C v) :
    ∀ a j j', a < firstBranch C v h → Carries C v a → LNext n C a j → LNext n C a j' → j = j' := by
  classical
  intro a j j' hl hc hj hj'
  apply nonbranch_unique _ hj hj'
  intro hb
  exact (Nat.not_le_of_gt hl) (Nat.find_min' h ⟨live_before hj.1 hj.2,hc,hb⟩)

theorem no_eligible_unique {v : Fin n} (h : ¬ Eligible C v) :
    ∀ a j j', Carries C v a → LNext n C a j → LNext n C a j' → j = j' := by
  intro a j j' hc hj hj'
  exact nonbranch_unique (fun hb => h ⟨a,live_before hj.1 hj.2,hc,hb⟩) hj hj'

end PEqualNP.Outside.L_meta_2988_aux


namespace PEqualNP.Outside.L_meta_2988_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}

def GraphEval (C : Circuit) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ u v : Fin n, val C (point {u, v}) C.output = true ↔ G.Adj u v

theorem point_pair (he : GraphEval C G) (v w : Fin n) :
    val C (point {v, w}) C.output = true ↔ G.Adj v w :=
  he v w

theorem edge_in_set (hC : Monotone2 C) (he : GraphEval C G) {S : Finset (Fin n)}
    {u v : Fin n} (hu : u ∈ S) (hv : v ∈ S) (edge : G.Adj u v) :
    val C (point S) C.output = true := by
  have hs : ({u, v} : Finset (Fin n)) ⊆ S := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hu
    · exact hv
  exact acts_mono hC (point_mono hs) _ ((point_pair he u v).2 edge)

theorem point_pair_quiet (he : GraphEval C G) {v w : Fin n} (hn : ¬ G.Adj v w) :
    val C (point {v,w}) C.output = false := by
  rw [← Bool.not_eq_true, point_pair he]
  exact hn

theorem point_single_quiet (he : GraphEval C G) (v : Fin n) :
    val C (point {v}) C.output = false := by
  simpa using point_pair_quiet he (G.irrefl (v := v))

theorem edge_at_output (he : GraphEval C G) {v w : Fin n} (hvw : G.Adj v w) :
    n ≤ C.output ∧ C.output < n+C.gates.length := by
  have hp := (point_pair he v w).2 hvw
  constructor
  · by_contra! hl
    let i : Fin n := ⟨C.output,hl⟩
    have hv := point_single_quiet he i
    rw [show C.output = i.val from rfl,val_input] at hv
    simp [point] at hv
  · by_contra! hgt
    rw [val_beyond C _ hgt] at hp
    contradiction

theorem two_inputs {l : List ℕ} {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b)
    (hl : l.length ≤ 2) :
    ∀ i ∈ l, i = a ∨ i = b := by
  have hsub : ({a,b} : Finset ℕ) ⊆ l.toFinset := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact List.mem_toFinset.mpr ha
    · exact List.mem_toFinset.mpr hb
  have hcard : l.toFinset.card ≤ ({a,b} : Finset ℕ).card := by
    simpa [hne] using l.toFinset_card_le.trans hl
  have hEq := Finset.eq_of_subset_of_card_le hsub hcard
  intro i hi
  have hm : i ∈ ({a,b} : Finset ℕ) := hEq.symm ▸ (List.mem_toFinset.mpr hi)
  simpa using hm

theorem carries_separate (hC : Monotone2 C) {v w : Fin n} {a : ℕ}
    (h1 : val C (point {v}) a = true) (h0 : val C (point {w}) a = false) :
    Carries C v a ∧ ¬ Carries C w a := by
  have hb : val C (point (∅ : Finset (Fin n))) a = false := by
    rw [← Bool.not_eq_true]
    intro hc
    have hh := acts_mono hC (point_mono (Finset.empty_subset {w})) a hc
    rw [h0] at hh
    contradiction
  rw [carries_iff hC,carries_iff hC]
  simp [h1,h0,hb]

theorem meeting_gate (hC : Monotone2 C) (he : GraphEval C G) {v w : Fin n}
    (hvw : G.Adj v w) :
    ∃ p g a b, C.gates[p]? = some g ∧ g.op = GateOp.and ∧ Live n C (n+p) ∧
      LNext n C a (n+p) ∧ LNext n C b (n+p) ∧
      Carries C v a ∧ ¬ Carries C w a ∧ Carries C w b ∧ ¬ Carries C v b ∧
      (∀ i ∈ g.inputs, i = a ∨ i = b) := by
  classical
  let P (i : ℕ) := Live n C i ∧ val C (point {v,w}) i = true ∧
    val C (point {v}) i = false ∧ val C (point {w}) i = false
  have hex : ∃ i, P i :=
    ⟨C.output, .refl, (point_pair he v w).2 hvw, point_single_quiet he v, point_single_quiet he w⟩
  let j := Nat.find hex
  have hj : P j := Nat.find_spec hex
  have earlier (i : ℕ) (hlt : i < j) (hl : Live n C i)
      (htrue : val C (point {v,w}) i = true) :
      val C (point {v}) i = true ∨ val C (point {w}) i = true := by
    by_contra! h
    have h' : P i := ⟨hl, htrue, by simpa using h.1, by simpa using h.2⟩
    exact (Nat.not_le_of_gt hlt) (Nat.find_min' hex h')
  have hge : n ≤ j := by
    by_contra! hh
    let i : Fin n := ⟨j,hh⟩
    obtain ⟨_,ht,hv,hw⟩ := hj
    rw [show j = i.val from rfl,val_input] at ht hv hw
    simp only [point,decide_eq_true_eq,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with h | h
    · simp [point,h] at hv
    · simp [point,h] at hw
  have hlt : j < n+C.gates.length := by
    by_contra! hh
    have ht := hj.2.1
    rw [val_beyond C _ hh] at ht
    contradiction
  let p := j-n
  have hp : p < C.gates.length := by dsimp [p]; omega
  have ep : n+p = j := by dsimp [p]; omega
  let g := C.gates[p]
  have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp,rfl⟩
  have hl := hC g (List.mem_of_getElem? hg)
  have hh : Live n C (n+p) := ep ▸ hj.1
  have hs1 : val C (point {v,w}) (n+p) = true := ep ▸ hj.2.1
  have hs2 : val C (point {v}) (n+p) = false := ep ▸ hj.2.2.1
  have hs3 : val C (point {w}) (n+p) = false := ep ▸ hj.2.2.2
  have reads (i : ℕ) (hi : i < n+p) (hm : i ∈ g.inputs) : LNext n C i (n+p) :=
    ⟨⟨hi,p,g,hg,rfl,hm⟩,hh⟩
  have hAnd : g.op = GateOp.and := by
    rcases hl.1 with h | h
    · exact h
    have hop : g.op = GateOp.or := h
    simp only [val_gate C _ hg, hop, GateOp.eval, List.any_map, Function.comp_apply, id,
      List.any_eq_true] at hs1
    obtain ⟨i,hi,ht⟩ := hs1
    have hi' : i < n+p := by
      by_contra hh'
      simp [operand,hh'] at ht
    have ht' : val C (point {v,w}) i = true := by simpa [operand,hi'] using ht
    rcases earlier i (ep ▸ hi') (live_before (reads i hi' hi).1 hh) ht' with hV | hW
    · have hs := hs2
      rw [← Bool.not_eq_true, val_gate C _ hg,hop,GateOp.eval,List.any_map,List.any_eq_true] at hs
      exact (hs ⟨i,hi,by simpa [operand,hi'] using hV⟩).elim
    · have hs := hs3
      rw [← Bool.not_eq_true, val_gate C _ hg,hop,GateOp.eval,List.any_map,List.any_eq_true] at hs
      exact (hs ⟨i,hi,by simpa [operand,hi'] using hW⟩).elim
  have hAll : ∀ i ∈ g.inputs, operand C (point {v,w}) (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hs1
  have hFalse (x : Fin n → Bool) (hX : val C x (n+p) = false) :
      ∃ i ∈ g.inputs, operand C x (n+p) i = false := by
    by_contra! h
    have ht : val C x (n+p) = true := by
      rw [val_gate C _ hg,hAnd,GateOp.eval,List.all_map,List.all_eq_true]
      intro i hi
      simpa using h i hi
    rw [hX] at ht
    contradiction
  obtain ⟨a,ha,hwa⟩ := hFalse _ hs3
  obtain ⟨b,hb,hvb⟩ := hFalse _ hs2
  have before (i : ℕ) (h : i ∈ g.inputs) : i < n+p := by
    by_contra hi
    have hX := hAll i h
    simp [operand,hi] at hX
  have ha' := before a ha
  have hb' := before b hb
  rw [operand,ite_eq_left ha'] at hwa
  rw [operand,ite_eq_left hb'] at hvb
  have near (i : ℕ) (h : i ∈ g.inputs) :
      val C (point {v}) i = true ∨ val C (point {w}) i = true := by
    have hi := before i h
    apply earlier i (ep ▸ hi) (live_before (reads i hi h).1 hh)
    simpa [operand,hi] using hAll i h
  have hva := (near a ha).resolve_right (by rw [hwa]; decide)
  have hwb := (near b hb).resolve_left (by rw [hvb]; decide)
  have hne : a ≠ b := fun e => Bool.noConfusion (hva.symm.trans (e ▸ hvb))
  exact ⟨p,g,a,b,hg,hAnd,hh,reads a ha' ha,reads b hb' hb,
    (carries_separate hC hva hwa).1,(carries_separate hC hva hwa).2,
    (carries_separate hC hwb hvb).1,(carries_separate hC hwb hvb).2,
    two_inputs ha hb hne hl.2⟩

theorem covers_edge (hC : Monotone2 C) (he : GraphEval C G) {v w a₀ b₀ : Fin n}
    (hvw : G.Adj v w) (ha₀ : G.Adj v a₀) (_ha₁ : a₀ ≠ w)
    (hb₀ : G.Adj w b₀) (_hb₁ : b₀ ≠ v) (hind : a₀ = b₀ ∨ ¬ G.Adj a₀ b₀) :
    Eligible C v ∨ Eligible C w := by
  by_contra! bad
  obtain ⟨p,g,a,b,hg,hAnd,hj,ha,hb,hva,hwa,hwb,hvb,hs⟩ := meeting_gate hC he hvw
  have pathV : Trace n C (Carries C v) v.val (n+p) :=
    (singleton_path (live_before ha.1 ha.2) hva).tail ⟨hva,ha⟩
  have pathW : Trace n C (Carries C w) w.val (n+p) :=
    (singleton_path (live_before hb.1 hb.2) hwb).tail ⟨hwb,hb⟩
  have uniqueV : ∀ k j j', k < n+p → Carries C v k → LNext n C k j → LNext n C k j' → j=j' :=
    fun k j j' _ => no_eligible_unique bad.1 k j j'
  have uniqueW : ∀ k j j', k < n+p → Carries C w k → LNext n C k j → LNext n C k j' → j=j' :=
    fun k j j' _ => no_eligible_unique bad.2 k j j'
  let S : Finset (Fin n) := {a₀,b₀}
  let x := point S
  let y := point (insert v S)
  let z := point (insert w S)
  have hzero : val C x C.output = false :=
    point_pair_quiet he (hind.elim (fun e => e ▸ G.irrefl (v := a₀)) id)
  have hY : val C y C.output = true := edge_in_set hC he (by simp) (by simp [S]) ha₀
  have hZ : val C z C.output = true := edge_in_set hC he (by simp) (by simp [S]) hb₀
  have jout := next_le hj
  have hvj := influence pathV uniqueV (fun _ hi => (point_insert hi).symm) ReflTransGen.refl (show val C x C.output ≠ val C y C.output from by rw [hzero,hY]; decide)
  have hwj := influence pathW uniqueW (fun _ hi => (point_insert hi).symm) ReflTransGen.refl (show val C x C.output ≠ val C z C.output from by rw [hzero,hZ]; decide)
  have hdiffV := (hvj.resolve_left (fun h => (Nat.not_lt_of_ge jout) h.1)).2
  have hdiffW := (hwj.resolve_left (fun h => (Nat.not_lt_of_ge jout) h.1)).2
  have hX : val C x (n+p) = false := by
    rw [← Bool.not_eq_true]
    intro htrue
    exact hdiffV (htrue.trans (acts_mono hC (point_mono (Finset.subset_insert _ _)) _ htrue).symm)
  have hyj : val C y (n+p) = true := by
    rw [hX] at hdiffV
    simpa using hdiffV.symm
  have hzj : val C z (n+p) = true := by
    rw [hX] at hdiffW
    simpa using hdiffW.symm
  have hAX : val C x a = val C z a := by
    by_contra h
    rcases influence pathW uniqueW (fun _ hi => (point_insert hi).symm) (live_before ha.1 ha.2) h with h' | h'
    · exact hwa h'.2
    · exact (Nat.not_le_of_gt ha.1.1) h'.1
  have hBX : val C x b = val C y b := by
    by_contra h
    rcases influence pathV uniqueV (fun _ hi => (point_insert hi).symm) (live_before hb.1 hb.2) h with h' | h'
    · exact hvb h'.2
    · exact (Nat.not_le_of_gt hb.1.1) h'.1
  have hYall : ∀ i ∈ g.inputs, operand C y (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hyj
  have hZall : ∀ i ∈ g.inputs, operand C z (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hzj
  have hin (i : ℕ) : LNext n C i (n+p) → i ∈ g.inputs := by
    rintro ⟨⟨_,k,g',he',hk,hmem⟩,_⟩
    have e : k=p := by omega
    subst k
    rw [hg] at he'
    cases he'
    exact hmem
  have hxA := hZall a (hin a ha)
  have hxB := hYall b (hin b hb)
  rw [operand,ite_eq_left ha.1.1,← hAX] at hxA
  rw [operand,ite_eq_left hb.1.1,← hBX] at hxB
  have hs' : val C x (n+p) = true := by
    rw [val_gate C _ hg,hAnd,GateOp.eval,List.all_map,List.all_eq_true]
    intro i hi
    rcases hs i hi with rfl | rfl
    · simpa [Function.comp_apply,operand,ha.1.1] using hxA
    · simpa [Function.comp_apply,operand,hb.1.1] using hxB
  rw [hX] at hs'
  contradiction

end PEqualNP.Outside.L_meta_2988_aux


namespace PEqualNP.Outside.L_meta_2988_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}

theorem value_at_branch {v : Fin n} {x y : Fin n → Bool} (hv : Eligible C v)
    (agrees : ∀ i, i ≠ v → x i = y i)
    (hb : val C x (firstBranch C v hv) = val C y (firstBranch C v hv)) :
    val C x C.output = val C y C.output := by
  by_contra h
  have spec := firstBranch_spec v hv
  have path := singleton_path spec.1 spec.2.1
  rcases influence path (firstBranch_unique v hv) agrees ReflTransGen.refl h with bad | bad
  · exact (Nat.not_lt_of_ge (next_le spec.1)) bad.1
  · exact bad.2 hb

theorem branch_injective (hC : Monotone2 C) (he : GraphEval C G)
    (htwins : ∀ v w : Fin n, v ≠ w → ¬ G.Adj v w → ∃ u : Fin n, ¬ (G.Adj v u ↔ G.Adj w u))
    {v w : Fin n} (hv : Eligible C v) (hw : Eligible C w)
    (h : firstBranch C v hv = firstBranch C w hw) : v = w := by
  classical
  by_contra hne
  let b := firstBranch C v hv
  have hw_b : firstBranch C w hw = b := h.symm
  have hvtrue : val C (point {v}) b = true :=
    (carries_iff hC).1 (firstBranch_spec v hv).2.1 |>.1
  have hwtrue : val C (point {w}) b = true := by
    rw [← hw_b]
    exact (carries_iff hC).1 (firstBranch_spec w hw).2.1 |>.1
  by_cases hadj : G.Adj v w
  · have hbig : val C (point (insert w ({v} : Finset (Fin n)))) b = true :=
      acts_mono hC (point_mono (Finset.subset_insert _ _)) b hvtrue
    have eq := value_at_branch hw
      (x := point {v}) (y := point (insert w ({v} : Finset (Fin n))))
      (fun _ hi => (point_insert hi).symm) (by rw [hw_b,hvtrue,hbig])
    have hy : val C (point (insert w ({v} : Finset (Fin n)))) C.output = true :=
      (point_pair he w v).2 (G.adj_symm hadj)
    rw [point_single_quiet he v,hy] at eq
    contradiction
  obtain ⟨u,hu⟩ := htwins v w hne hadj
  have hx : val C (point {v,u}) b = true := acts_mono hC
    (point_mono (by simp)) b hvtrue
  have hy : val C (point {w,u}) b = true := acts_mono hC
    (point_mono (by simp)) b hwtrue
  have hxyz : val C (point (insert w ({v,u} : Finset (Fin n)))) b = true :=
    acts_mono hC (point_mono (Finset.subset_insert _ _)) b hx
  have hEq : (insert w ({v,u} : Finset (Fin n))) = insert v {w,u} :=
    Finset.insert_comm _ _ _
  have e1 := value_at_branch hw
    (x := point {v,u}) (y := point (insert w ({v,u} : Finset (Fin n))))
    (fun _ hi => (point_insert hi).symm) (by rw [hw_b,hx,hxyz])
  have e2 := value_at_branch hv
    (x := point {w,u}) (y := point (insert v ({w,u} : Finset (Fin n))))
    (fun _ hi => (point_insert hi).symm) (by rw [← hEq]; exact hy.trans hxyz.symm)
  have e : val C (point {v,u}) C.output = val C (point {w,u}) C.output :=
    e1.trans (by rw [hEq,e2])
  apply hu
  rw [← point_pair he v u, ← point_pair he w u, e]

noncomputable def living (n : ℕ) (C : Circuit) : Finset ℕ :=
  open Classical in (Finset.range (n+C.gates.length)).filter (Live n C)

theorem mem_living {w : ℕ} : w ∈ living n C ↔ w < n+C.gates.length ∧ Live n C w := by
  classical
  simp [living]

theorem input_live (he : GraphEval C G) {v u : Fin n} (hvu : G.Adj v u) :
    Live n C v.val := by
  have hx : val C (point {u}) C.output = false := point_single_quiet he u
  have hy : val C (point {v,u}) C.output = true := (point_pair he v u).2 hvu
  obtain ⟨i,hi,trace⟩ := difference C (point {u}) (point {v,u}) C.output ReflTransGen.refl
    (by rw [hx,hy]; decide)
  have ei : i=v := by
    by_contra h
    exact hi ((point_insert h).symm)
  subst i
  rcases trace.cases_head with h | ⟨b,hb,_⟩
  · rw [h]
    exact .refl
  · exact live_before hb.2.1 hb.2.2

theorem live_readers_nonempty {a : ℕ} (ha : Live n C a) (hneq : a ≠ C.output) :
    (readers n C a).Nonempty := by
  rcases ha.cases_head with h | ⟨b,hb,hpath⟩
  · exact (hneq h).elim
  · exact ⟨b,mem_readers.2 ⟨hb,hpath⟩⟩

theorem readers_filter (a : ℕ) :
    open Classical in readers n C a = (living n C).filter (fun b => LNext n C a b) := by
  classical
  ext b
  simp only [mem_readers,Finset.mem_filter,mem_living]
  exact ⟨fun h => ⟨⟨next_in_range h.1,h.2⟩,h⟩, And.right⟩

theorem incoming_bound {j : ℕ} (hC : Monotone2 C) (hj : j ∈ living n C) :
    open Classical in ((living n C).filter fun i => LNext n C i j).card ≤ if j<n then 0 else 2 := by
  classical
  by_cases hi : j < n
  · rw [ite_eq_left hi]
    apply Nat.le_of_eq
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.2
    intro i hm
    obtain ⟨_,⟨_,p,g,hg,hp,_⟩,_⟩ := Finset.mem_filter.mp hm
    omega
  rw [ite_eq_right hi]
  have hj' := (mem_living.1 hj).1
  let p := j-n
  have hp : p < C.gates.length := by dsimp [p]; omega
  have he : j=n+p := by dsimp [p]; omega
  let g := C.gates[p]
  have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp,rfl⟩
  have hsub : ((living n C).filter fun i => LNext n C i j) ⊆ g.inputs.toFinset := by
    intro a ha
    obtain ⟨_,⟨_,q,g',hg',hq,hm⟩,_⟩ := Finset.mem_filter.1 ha
    have ep : p=q := by omega
    subst q
    rw [hg] at hg'
    cases hg'
    exact List.mem_toFinset.2 hm
  exact (Finset.card_le_card hsub).trans (g.inputs.toFinset_card_le.trans
    (hC g (List.mem_of_getElem? hg)).2)

theorem branch_budget (hC : Monotone2 C) (he : GraphEval C G)
    (hdegree : ∀ v : Fin n, ∃ u, G.Adj v u) (ho : C.output ∈ living n C) :
    open Classical in n + ((living n C).filter (Branch n C)).card ≤ C.size + 1 := by
  classical
  let W := living n C
  let S := W.filter (fun a => ¬ a < n)
  let B := W.filter (Branch n C)
  let R := W.erase C.output
  have hSub : Finset.range n ⊆ W := by
    intro a ha
    have hi := Finset.mem_range.1 ha
    let v : Fin n := ⟨a,hi⟩
    obtain ⟨u,hu⟩ := hdegree v
    exact mem_living.2 ⟨by omega,input_live he hu⟩
  have hW : W.card = n + S.card := by
    have h := Finset.card_sdiff_add_card_eq_card hSub
    have e : W \ Finset.range n = S := by ext a; simp [S]
    rw [e,Finset.card_range] at h
    omega
  have hR : R.card + 1 = W.card := by
    dsimp [R]
    have h := Finset.card_erase_add_one ho
    exact h
  have hS : S.card ≤ C.gates.length := by
    rw [show C.gates.length = (Finset.range C.gates.length).card by simp]
    apply Finset.card_le_card_of_injOn (fun a => a-n)
    · intro a ha
      have h : a < n+C.gates.length := (mem_living.1 (Finset.mem_filter.1 ha).1).1
      have h0 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      apply Finset.mem_range.2
      change a-n < C.gates.length
      omega
    · intro a ha b hb hab
      have h1 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      have h2 : n ≤ b := Nat.le_of_not_gt (Finset.mem_filter.1 hb).2
      change a-n=b-n at hab
      omega
  have hoNone : ¬ Branch n C C.output := by
    intro h
    have hgt : 0 < (readers n C C.output).card := by unfold Branch at h; omega
    obtain ⟨b,hb⟩ := Finset.card_pos.1 hgt
    have hs := mem_readers.1 hb
    exact (Nat.not_lt_of_ge (next_le hs.2)) hs.1.1
  have hlow : R.card+B.card ≤ ∑ a ∈ W, (readers n C a).card := by
    have eR : (∑ a ∈ W, (if a=C.output then 0 else 1 : ℕ)) = R.card := by
      calc
        _ = ∑ a ∈ W, (if a≠C.output then 1 else 0 : ℕ) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : a=C.output <;> simp [h]
        _ = R.card := by rw [← Finset.sum_filter]; simp [R,Finset.filter_ne']
    have eB : (∑ a ∈ W, (if Branch n C a then 1 else 0 : ℕ)) = B.card := by
      rw [← Finset.sum_filter]
      simp [B]
    rw [← eR,← eB,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a ha
    have hl := (mem_living.1 ha).2
    by_cases heq : a=C.output
    · subst a
      simp [hoNone]
    · by_cases hb : Branch n C a
      · have hb' : 2 ≤ (readers n C a).card := hb
        simpa [heq,hb] using hb'
      · simpa [heq,hb] using Nat.succ_le_of_lt (Finset.card_pos.2 (live_readers_nonempty hl heq))
  have hcomm :
      (∑ a ∈ W, (readers n C a).card) =
        ∑ j ∈ W, (W.filter fun a => LNext n C a j).card := by
    simp_rw [readers_filter,Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Finset.sum_comm
  have hupp : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤ 2*S.card := by
    have H : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤
        ∑ j ∈ W, (if j<n then 0 else 2 : ℕ) :=
      Finset.sum_le_sum fun j hj => incoming_bound hC hj
    have e : (∑ j ∈ W, (if j<n then 0 else 2 : ℕ)) = 2*S.card := by
      simp [S,Finset.sum_ite, Nat.mul_comm]
    exact H.trans_eq e
  rw [hcomm] at hlow
  change n+B.card ≤ C.gates.length+1
  omega

end PEqualNP.Outside.L_meta_2988_aux


namespace PEqualNP.Outside.L_meta_2988_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem pair_lower (n t : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit)
    (hdegree : ∀ v : Fin n, ∃ w : Fin n, G.Adj v w)
    (htwins : ∀ v w : Fin n, v ≠ w → ¬ G.Adj v w →
      ∃ u : Fin n, ¬ (G.Adj v u ↔ G.Adj w u))
    (hadj : ∀ v w : Fin n, G.Adj v w →
      ∃ a b : Fin n, G.Adj v a ∧ a ≠ w ∧ G.Adj w b ∧ b ≠ v ∧ (a = b ∨ ¬ G.Adj a b))
    (ht : ∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) → t ≤ S.card)
    (hC : Monotone2 C) (he : GraphEval C G) : n + t ≤ C.size + 1 := by
  classical
  by_cases hn : n = 0
  · subst n
    have ht0 := ht ∅ (fun u => Fin.elim0 u)
    simp at ht0
    omega
  let v : Fin n := ⟨0, by omega⟩
  obtain ⟨w, hve⟩ := hdegree v
  have ho := (edge_at_output he hve).2
  have ho' : C.output ∈ living n C := mem_living.2 ⟨ho, Relation.ReflTransGen.refl⟩
  let S : Finset (Fin n) := Finset.univ.filter fun v => Eligible C v
  have hS (u : Fin n) : u ∈ S ↔ Eligible C u := by simp [S]
  have htc : t ≤ S.card := by
    apply ht S
    intro a b hab
    obtain ⟨u,v,hu,hu',hv,hv',hind⟩ := hadj a b hab
    rcases covers_edge hC he hab hu hu' hv hv' hind with ha | hb
    · exact Or.inl ((hS a).2 ha)
    · exact Or.inr ((hS b).2 hb)
  let B := (living n C).filter (Branch n C)
  let f (u : Fin n) := if h : Eligible C u then firstBranch C u h else 0
  have hf (u : Fin n) (hu : Eligible C u) : f u = firstBranch C u hu := by simp [f,hu]
  have hcap : S.card ≤ B.card := by
    apply Finset.card_le_card_of_injOn f
    · intro u hu
      have hs := (hS u).1 hu
      have hb := firstBranch_spec u hs
      have hlt := (next_le hb.1).trans_lt ho
      show f u ∈ B
      rw [hf u hs]
      exact Finset.mem_filter.2 ⟨mem_living.2 ⟨hlt,hb.1⟩,hb.2.2⟩
    · intro u hu v hv huv
      have hsu := (hS u).1 hu
      have hsv := (hS v).1 hv
      rw [hf u hsu,hf v hsv] at huv
      exact branch_injective hC he htwins hsu hsv huv
  have hbudget := branch_budget hC he hdegree ho'
  exact (Nat.add_le_add_left (htc.trans hcap) n).trans hbudget

end PEqualNP.Outside.L_meta_2988_aux

namespace PEqualNP.Outside.L_meta_2988_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The point-degree computation below is adapted from the checked L_meta_1778.

lemma lines_card (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) (c : Fin N) :
    (Finset.univ.filter (fun l => I c l)).card = q + 1 := by
  have e : (Finset.univ.filter (fun l => I c l)).biUnion
      (fun l => (Finset.univ.filter (fun p => I p l)).erase c) = Finset.univ.erase c := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true]
    constructor
    · rintro ⟨l, _, hp, _⟩
      exact hp
    · intro hp
      obtain ⟨l, ⟨h1, h2⟩, _⟩ := hu p c hp
      exact ⟨l, h2, hp, h1⟩
  have hd : ∀ l ∈ Finset.univ.filter (fun l => I c l), ∀ l' ∈ Finset.univ.filter (fun l => I c l),
      l ≠ l' → Disjoint ((Finset.univ.filter (fun p => I p l)).erase c)
        ((Finset.univ.filter (fun p => I p l')).erase c) := by
    intro l hl1 l' hl1' hne
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hl1 hl1' hp hp'
    obtain ⟨l0, _, hun⟩ := hu p c hp.1
    exact hne ((hun l ⟨hp.2, hl1⟩).trans (hun l' ⟨hp'.2, hl1'⟩).symm)
  have hc := Finset.card_biUnion hd
  rw [e] at hc
  have hs : ∀ l ∈ Finset.univ.filter (fun l => I c l),
      ((Finset.univ.filter (fun p => I p l)).erase c).card = q := by
    intro l hl1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl1
    rw [Finset.card_erase_of_mem (by simp [hl1]), hl l]
    rfl
  rw [Finset.sum_congr rfl hs, Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ c),
    Finset.card_univ, Fintype.card_fin] at hc
  have h3 : (Finset.univ.filter (fun l => I c l)).card * q = (q + 1) * q := by
    rw [← hc, hN]
    have : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
      rw [Nat.add_sub_cancel]
      ring
    exact this
  exact Nat.eq_of_mul_eq_mul_right (by omega) h3

abbrev pt {N : ℕ} (p : Fin N) : Fin (N + N) := Fin.castAdd N p
abbrev ln {N : ℕ} (l : Fin N) : Fin (N + N) := Fin.natAdd N l

theorem pt_ne_ln {N : ℕ} (p l : Fin N) : pt p ≠ ln l := by
  intro he
  have hv := congrArg Fin.val he
  simp only [pt, ln, Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

def incidenceGraph {N : ℕ} (I : Fin N → Fin N → Prop) : SimpleGraph (Fin (N + N)) :=
  SimpleGraph.fromRel (fun a b => ∃ p l, I p l ∧ a = pt p ∧ b = ln l)

theorem adj_shapes {N : ℕ} (I : Fin N → Fin N → Prop) (a b : Fin (N + N)) :
    (incidenceGraph I).Adj a b ↔
      ∃ p l, I p l ∧ (a = pt p ∧ b = ln l ∨ b = pt p ∧ a = ln l) := by
  unfold incidenceGraph
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, forward | backward⟩
    · obtain ⟨p, l, h, ha, hb⟩ := forward
      exact ⟨p, l, h, Or.inl ⟨ha, hb⟩⟩
    · obtain ⟨p, l, h, hb, ha⟩ := backward
      exact ⟨p, l, h, Or.inr ⟨hb, ha⟩⟩
  · rintro ⟨p, l, h, forward | backward⟩
    · obtain ⟨rfl, rfl⟩ := forward
      exact ⟨pt_ne_ln p l, Or.inl ⟨p, l, h, rfl, rfl⟩⟩
    · obtain ⟨rfl, rfl⟩ := backward
      exact ⟨(pt_ne_ln p l).symm, Or.inr ⟨p, l, h, rfl, rfl⟩⟩

theorem adj_pt_ln {N : ℕ} {I : Fin N → Fin N → Prop} (p l : Fin N) :
    (incidenceGraph I).Adj (pt p) (ln l) ↔ I p l := by
  rw [adj_shapes]
  constructor
  · rintro ⟨a, b, h, ⟨ha, hb⟩ | ⟨ha, _⟩⟩
    · have hp : p = a := Fin.castAdd_injective N N ha
      have hl : l = b := Fin.natAdd_injective N N hb
      simpa [hp, hl] using h
    · exact ((pt_ne_ln a l) ha.symm).elim
  · intro h
    exact ⟨p, l, h, Or.inl ⟨rfl, rfl⟩⟩

theorem no_pt_pt {N : ℕ} {I : Fin N → Fin N → Prop} (p a : Fin N) :
    ¬ (incidenceGraph I).Adj (pt p) (pt a) := by
  rw [adj_shapes]
  rintro ⟨q, l, _, ⟨_, he⟩ | ⟨_, he⟩⟩
  · exact pt_ne_ln a l he
  · exact pt_ne_ln p l he

theorem no_ln_ln {N : ℕ} {I : Fin N → Fin N → Prop} (l a : Fin N) :
    ¬ (incidenceGraph I).Adj (ln l) (ln a) := by
  rw [adj_shapes]
  rintro ⟨q, b, _, ⟨he, _⟩ | ⟨he, _⟩⟩
  · exact pt_ne_ln q l he.symm
  · exact pt_ne_ln q a he.symm

theorem not_only {α : Type*} [DecidableEq α] (S : Finset α)
    (h : 2 ≤ S.card) (i : α) : ∃ j ∈ S, j ≠ i := by
  by_contra! no
  have subset : S ⊆ {i} := by
    intro j hj
    simpa using no j hj
  have hc := Finset.card_le_card subset
  simp at hc
  omega

theorem vertex_cases {N : ℕ} (v : Fin (N + N)) :
    (∃ p, v = pt p) ∨ (∃ l, v = ln l) :=
  Fin.addCases (fun p => Or.inl ⟨p, rfl⟩) (fun l => Or.inr ⟨l, rfl⟩) v

variable {q N : ℕ} {I : Fin N → Fin N → Prop} [DecidableRel I]

theorem pick_line (hq : 2 ≤ q)
    (hp : ∀ p : Fin N, (Finset.univ.filter fun l => I p l).card = q + 1)
    (p l : Fin N) : ∃ l', I p l' ∧ l' ≠ l := by
  obtain ⟨l', mem, ne⟩ := not_only (Finset.univ.filter fun l' => I p l')
    (by rw [hp]; omega) l
  exact ⟨l', (Finset.mem_filter.mp mem).2, ne⟩

theorem pick_point (hq : 2 ≤ q)
    (hl : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (l p : Fin N) : ∃ p', I p' l ∧ p' ≠ p := by
  obtain ⟨p', mem, ne⟩ := not_only (Finset.univ.filter fun p' => I p' l)
    (by rw [hl]; omega) p
  exact ⟨p', (Finset.mem_filter.mp mem).2, ne⟩

theorem no_isolated (hq : 2 ≤ q)
    (hl : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (hp : ∀ p : Fin N, (Finset.univ.filter fun l => I p l).card = q + 1)
    (hN : 0 < N) (v : Fin (N + N)) : ∃ w, (incidenceGraph I).Adj v w := by
  rcases vertex_cases v with ⟨p, rfl⟩ | ⟨l, rfl⟩
  · obtain ⟨l, inc, _⟩ := pick_line hq hp p ⟨0, hN⟩
    exact ⟨ln l, (adj_pt_ln p l).2 inc⟩
  · obtain ⟨p, inc, _⟩ := pick_point hq hl l ⟨0, hN⟩
    exact ⟨pt p, (incidenceGraph I).adj_symm ((adj_pt_ln p l).2 inc)⟩

theorem distinct_neighbors (hq : 2 ≤ q)
    (hl : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (hp : ∀ p : Fin N, (Finset.univ.filter fun l => I p l).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
    (hN : 0 < N) (v w : Fin (N + N)) (hne : v ≠ w) :
    ∃ u, ¬ ((incidenceGraph I).Adj v u ↔ (incidenceGraph I).Adj w u) := by
  rcases vertex_cases v with ⟨p, rfl⟩ | ⟨l, rfl⟩
  · rcases vertex_cases w with ⟨p', rfl⟩ | ⟨l, rfl⟩
    · have hpp' : p ≠ p' := fun he => hne (congrArg pt he)
      obtain ⟨meet, _, unique⟩ := hu p p' hpp'
      obtain ⟨s, hps, hsm⟩ := pick_line hq hp p meet
      refine ⟨ln s, ?_⟩
      rw [adj_pt_ln, adj_pt_ln]
      exact fun he => hsm (unique s ⟨hps, he.mp hps⟩)
    · obtain ⟨s, hps, _⟩ := pick_line hq hp p l
      exact ⟨ln s, fun he => no_ln_ln l s (he.mp ((adj_pt_ln p s).2 hps))⟩
  · rcases vertex_cases w with ⟨p, rfl⟩ | ⟨l', rfl⟩
    · obtain ⟨a, hal, _⟩ := pick_point hq hl l p
      exact ⟨pt a, fun he => no_pt_pt p a
        (he.mp ((incidenceGraph I).adj_symm ((adj_pt_ln a l).2 hal)))⟩
    · by_contra! same
      let p₀ : Fin N := ⟨0, hN⟩
      obtain ⟨p, hpl, _⟩ := pick_point hq hl l p₀
      obtain ⟨p', hp'l, hpp'⟩ := pick_point hq hl l p
      obtain ⟨meet, _, unique⟩ := hu p p' hpp'.symm
      have common (a : Fin N) (hal : I a l) : I a l' := by
        apply (adj_pt_ln a l').1
        exact (incidenceGraph I).adj_symm
          ((same (pt a)).mp ((incidenceGraph I).adj_symm ((adj_pt_ln a l).2 hal)))
      have eq : l = l' := (unique l ⟨hpl, hp'l⟩).trans
        (unique l' ⟨common p hpl, common p' hp'l⟩).symm
      exact hne (congrArg ln eq)

theorem edge_certificate (hq : 2 ≤ q)
    (hl : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (hp : ∀ p : Fin N, (Finset.univ.filter fun l => I p l).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l)
    (v w : Fin (N + N)) (edge : (incidenceGraph I).Adj v w) :
    ∃ a b, (incidenceGraph I).Adj v a ∧ a ≠ w ∧
      (incidenceGraph I).Adj w b ∧ b ≠ v ∧ (a = b ∨ ¬ (incidenceGraph I).Adj a b) := by
  obtain ⟨p, l, inc, shape⟩ := (adj_shapes I v w).1 edge
  obtain ⟨l', hpl', hll'⟩ := pick_line hq hp p l
  obtain ⟨p', hp'l, hpp'⟩ := pick_point hq hl l p
  have hOff : ¬ I p' l' := by
    intro h
    obtain ⟨meet, _, unique⟩ := hu p p' hpp'.symm
    exact hll' ((unique l' ⟨hpl', h⟩).trans (unique l ⟨inc, hp'l⟩).symm)
  have e₁ : (incidenceGraph I).Adj (pt p) (ln l') := (adj_pt_ln p l').2 hpl'
  have e₂ : (incidenceGraph I).Adj (ln l) (pt p') :=
    (incidenceGraph I).adj_symm ((adj_pt_ln p' l).2 hp'l)
  have ne₁ : ln l' ≠ ln l := fun he => hll' (Fin.natAdd_injective N N he)
  have ne₂ : pt p' ≠ pt p := fun he => hpp' (Fin.castAdd_injective N N he)
  rcases shape with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨ln l', pt p', e₁, ne₁, e₂, ne₂, Or.inr
      (fun e => hOff ((adj_pt_ln p' l').1 ((incidenceGraph I).adj_symm e)))⟩
  · exact ⟨pt p', ln l', e₂, ne₂, e₁, ne₁, Or.inr
      (fun e => hOff ((adj_pt_ln p' l').1 e))⟩

theorem graph_eval (C : Circuit)
    (pairs : ∀ a b : Fin (N + N),
      circuitFun (N + N) C (fun i => decide (i = a ∨ i = b)) = true ↔
        ∃ p l, I p l ∧ (pt p = a ∨ pt p = b) ∧ (ln l = a ∨ ln l = b)) :
    GraphEval C (incidenceGraph I) := by
  intro a b
  change circuitFun (N + N) C (point {a, b}) = true ↔ _
  have test : point ({a, b} : Finset (Fin (N + N))) = (fun i => decide (i = a ∨ i = b)) := by
    funext i
    simp only [point, Finset.mem_insert, Finset.mem_singleton]
  rw [test, pairs, adj_shapes]
  constructor
  · rintro ⟨p, l, hi, ha | ha, hb | hb⟩
    · exact ((pt_ne_ln p l) (ha.trans hb.symm)).elim
    · exact ⟨p, l, hi, Or.inl ⟨ha.symm, hb.symm⟩⟩
    · exact ⟨p, l, hi, Or.inr ⟨ha.symm, hb.symm⟩⟩
    · exact ((pt_ne_ln p l) (ha.trans hb.symm)).elim
  · rintro ⟨p, l, hi, ⟨ha,hb⟩ | ⟨ha,hb⟩⟩
    · exact ⟨p, l, hi, Or.inl ha.symm, Or.inr hb.symm⟩
    · exact ⟨p, l, hi, Or.inr ha.symm, Or.inl hb.symm⟩

end PEqualNP.Outside.L_meta_2988_aux

namespace PEqualNP.Outside.L_meta_2988

open Finset

theorem bipartite_cover_bound (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hl : ∀ l, (Finset.univ.filter fun p => I p l).card = q + 1)
    (hp : ∀ p, (Finset.univ.filter fun l => I p l).card = q + 1)
    (S : Finset (Fin (N + N)))
    (cover : ∀ p l, I p l → Fin.castAdd N p ∈ S ∨ Fin.natAdd N l ∈ S) :
    N ≤ S.card := by
  let U : Finset (Fin N) := univ.filter (fun p => Fin.castAdd N p ∉ S)
  let P : Finset (Fin N) := univ.filter (fun p => Fin.castAdd N p ∈ S)
  let L : Finset (Fin N) := univ.filter (fun l => Fin.natAdd N l ∈ S)
  have points : P.card + U.card = N := by
    simpa only [P, U, card_univ, Fintype.card_fin] using
      card_filter_add_card_filter_not (s := (univ : Finset (Fin N)))
        (fun p => Fin.castAdd N p ∈ S)
  have point_sum (p : Fin N) (h : p ∈ U) : (∑ l ∈ L, if I p l then 1 else 0) = q + 1 := by
    rw [← hp p, Finset.card_filter]
    apply sum_subset (Finset.subset_univ L)
    intro l _ hL
    have hNoP := (Finset.mem_filter.mp h).2
    exact ite_eq_right (fun hI => hL (Finset.mem_filter.mpr
      ⟨Finset.mem_univ l, (cover p l hI).resolve_left hNoP⟩))
  have line_sum (l : Fin N) : (∑ p ∈ U, if I p l then 1 else 0) ≤ q + 1 := by
    rw [← hl l, ← Finset.card_filter]
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ U))
  have pairs : U.card * (q + 1) ≤ L.card * (q + 1) := by
    calc
      U.card * (q + 1) = ∑ p ∈ U, (q + 1) := by simp [Nat.mul_comm]
      _ = ∑ p ∈ U, ∑ l ∈ L, if I p l then 1 else 0 :=
        Finset.sum_congr rfl fun p hpU => (point_sum p hpU).symm
      _ = ∑ l ∈ L, ∑ p ∈ U, if I p l then 1 else 0 := Finset.sum_comm
      _ ≤ ∑ l ∈ L, (q + 1) := Finset.sum_le_sum fun l _ => line_sum l
      _ = L.card * (q + 1) := by simp [Nat.mul_comm]
  have unselected_le : U.card ≤ L.card := Nat.le_of_mul_le_mul_right pairs (by omega)
  let P' := P.image (Fin.castAdd N)
  let L' := L.image (Fin.natAdd N)
  have hP : P'.card = P.card := Finset.card_image_of_injective P (Fin.castAdd_injective N N)
  have hL : L'.card = L.card := by
    apply Finset.card_image_of_injective
    intro a b hab
    apply Fin.ext
    have he := congrArg Fin.val hab
    simp only [Fin.val_natAdd] at he
    omega
  have disj : Disjoint P' L' := by
    apply Finset.disjoint_left.mpr
    intro f hfP hfL
    obtain ⟨p, _, hpF⟩ := Finset.mem_image.mp hfP
    obtain ⟨l, _, hlF⟩ := Finset.mem_image.mp hfL
    have he := congrArg Fin.val (hpF.trans hlF.symm)
    simp only [Fin.val_castAdd, Fin.val_natAdd] at he
    have hpN := p.isLt
    omega
  have covered : P' ∪ L' ⊆ S := by
    intro x h
    rcases Finset.mem_union.mp h with left | right
    · obtain ⟨p, hP, rfl⟩ := Finset.mem_image.mp left
      exact (Finset.mem_filter.mp hP).2
    · obtain ⟨l, hL, rfl⟩ := Finset.mem_image.mp right
      exact (Finset.mem_filter.mp hL).2
  have h := Finset.card_le_card covered
  rw [Finset.card_union_of_disjoint disj, hP, hL] at h
  omega

end PEqualNP.Outside.L_meta_2988

theorem PEqualNP.Outside.L_meta_2988 :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin (x2 + x2)), (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = x11 ∨ x13 = x12)) = Bool.true ↔ ∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ (Fin.castAdd x2 x13 = x11 ∨ Fin.castAdd x2 x13 = x12) ∧ (Fin.natAdd x2 x14 = x11 ∨ Fin.natAdd x2 x14 = x12)) → (3 : ℕ) * x2 ≤ x5.size + (1 : ℕ) := by
  intro q N I inst C hq hN hl' hu mono pair
  open PEqualNP.Outside.L_meta_2988_aux in
  have hl : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1 := by
    intro l
    rw [← hl' l, Fintype.card_subtype]
  open PEqualNP.Outside.L_meta_2988_aux in
  have hp := lines_card q N I hq hN hl hu
  open PEqualNP.Outside.L_meta_2988_aux in
  have count : (N + N) + N ≤ C.size + 1 := by
    refine pair_lower (N + N) N (incidenceGraph I) C (no_isolated hq hl hp (by omega))
      (fun v w hne _ => distinct_neighbors hq hl hp hu (by omega) v w hne)
      (edge_certificate hq hl hp hu) ?_ mono (graph_eval C pair)
    intro S cover
    exact PEqualNP.Outside.L_meta_2988.bipartite_cover_bound q N I hl hp S
      (fun p l hi => cover _ _ ((adj_pt_ln p l).2 hi))
  omega
