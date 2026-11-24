import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import PEqualNP.Defs

-- Branch counting adapted from the repository proof of L-meta-614.
namespace PEqualNP.Outside.L_meta_3289

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

end PEqualNP.Outside.L_meta_3289


-- Branch counting adapted from the repository proof of L-meta-614.
namespace PEqualNP.Outside.L_meta_3289

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

end PEqualNP.Outside.L_meta_3289


-- Branch counting adapted from the repository proof of L-meta-614.
namespace PEqualNP.Outside.L_meta_3289

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}

def GraphEval (C : Circuit) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v w, val C (point {v,w}) C.output = true ↔ G.Adj v w

theorem point_pair (he : GraphEval C G) (v w : Fin n) :
    val C (point {v,w}) C.output = true ↔ G.Adj v w := he v w

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
  have hY : val C y C.output = true := by
    apply acts_mono hC (point_mono (s := {v,a₀}) (by simp [S])) C.output
    exact (he v a₀).2 ha₀

  have hZ : val C z C.output = true := by
    apply acts_mono hC (point_mono (s := {w,b₀}) (by simp [S])) C.output
    exact (he w b₀).2 hb₀

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

end PEqualNP.Outside.L_meta_3289


-- Branch counting adapted from the repository proof of L-meta-614.
namespace PEqualNP.Outside.L_meta_3289

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
    (htwins : ∀ v w : Fin n, v ≠ w → ¬ G.Adj v w → 2 ≤ (G.neighborSet v).ncard →
      2 ≤ (G.neighborSet w).ncard → ∃ u : Fin n, ¬ (G.Adj v u ↔ G.Adj w u))
    {v w : Fin n} (hv : Eligible C v) (hw : Eligible C w)
    (hdv : 2 ≤ (G.neighborSet v).ncard) (hdw : 2 ≤ (G.neighborSet w).ncard)
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
  obtain ⟨u,hu⟩ := htwins v w hne hadj hdv hdw
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
    (active : Finset (Fin n)) (hdegree : ∀ v ∈ active, ∃ u, G.Adj v u) (ho : C.output ∈ living n C) :
    open Classical in active.card + ((living n C).filter (Branch n C)).card ≤ C.size + 1 := by
  classical
  let W := living n C
  let S := W.filter (fun a => ¬ a < n)
  let B := W.filter (Branch n C)
  let R := W.erase C.output
  have hSub : active.image Fin.val ⊆ W \ S := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨u,hu⟩ := hdegree v hv
    exact Finset.mem_sdiff.mpr ⟨mem_living.2 ⟨by have := v.isLt; omega,input_live he hu⟩,
      fun h => (Finset.mem_filter.mp h).2 v.isLt⟩
  have hW : active.card + S.card ≤ W.card := by
    have h := Finset.card_le_card hSub
    rw [Finset.card_image_of_injective _ Fin.val_injective] at h
    have part := Finset.card_sdiff_add_card_eq_card (show S ⊆ W from Finset.filter_subset _ _)
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
  change active.card+B.card ≤ C.gates.length+1
  omega



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem coverBudget {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hC : Monotone2 C) (hE : GraphEval C G)
    (active : Finset (Fin n)) (hdegree : ∀ v ∈ active, ∃ u, G.Adj v u)
    (htwins : ∀ v w : Fin n, v ≠ w → ¬ G.Adj v w → 2 ≤ (G.neighborSet v).ncard →
      2 ≤ (G.neighborSet w).ncard → ∃ u, ¬ (G.Adj v u ↔ G.Adj w u))
    (hadj : ∀ v w : Fin n, G.Adj v w → 2 ≤ (G.neighborSet v).ncard →
      2 ≤ (G.neighborSet w).ncard → ∃ a b, G.Adj v a ∧ a ≠ w ∧
      G.Adj w b ∧ b ≠ v ∧ (a = b ∨ ¬ G.Adj a b)) :
    ∃ S : Finset (Fin n),
      (∀ u v, G.Adj u v → 2 ≤ (G.neighborSet u).ncard →
          2 ≤ (G.neighborSet v).ncard → u ∈ S ∨ v ∈ S) ∧ active.card + S.card ≤ C.size+1 := by
  classical
  by_cases h : ∃ v u, G.Adj v u
  swap
  · have empty : active = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro v hv
      obtain ⟨w,hw⟩ := hdegree v hv
      exact h ⟨v,w,hw⟩)
    exact ⟨∅, fun u v e => (h ⟨u,v,e⟩).elim, by simp [empty]⟩
  obtain ⟨v,u,edge⟩ := h
  have ho := (edge_at_output hE edge).2
  have ho' : C.output ∈ living n C := mem_living.2 ⟨ho, Relation.ReflTransGen.refl⟩
  let S : Finset (Fin n) := Finset.univ.filter fun v =>
    2 ≤ (G.neighborSet v).ncard ∧ Eligible C v
  have hS (u : Fin n) : u ∈ S ↔ 2 ≤ (G.neighborSet u).ncard ∧ Eligible C u := by
    simp [S]
  have covers : ∀ a b, G.Adj a b → 2 ≤ (G.neighborSet a).ncard → 2 ≤ (G.neighborSet b).ncard → a ∈ S ∨ b ∈ S := by
    intro a b hab hda hdb
    obtain ⟨u,v,hu,hu',hv,hv',hind⟩ := hadj a b hab hda hdb
    rcases covers_edge hC hE hab hu hu' hv hv' hind with ha | hb
    · exact Or.inl ((hS a).2 ⟨hda,ha⟩)
    · exact Or.inr ((hS b).2 ⟨hdb,hb⟩)
  let B := (living n C).filter (Branch n C)
  let f (u : Fin n) := if h : Eligible C u then firstBranch C u h else 0
  have hf (u : Fin n) (hu : Eligible C u) : f u = firstBranch C u hu := by simp [f,hu]
  have hcap : S.card ≤ B.card := by
    apply Finset.card_le_card_of_injOn f
    · intro u hu
      obtain ⟨_,hs⟩ := (hS u).1 hu
      have hb := firstBranch_spec u hs
      have hlt := (next_le hb.1).trans_lt ho
      show f u ∈ B
      rw [hf u hs]
      exact Finset.mem_filter.2 ⟨mem_living.2 ⟨hlt,hb.1⟩,hb.2.2⟩
    · intro u hu v hv huv
      obtain ⟨hdu,hsu⟩ := (hS u).1 hu
      obtain ⟨hdv,hsv⟩ := (hS v).1 hv
      rw [hf u hsu,hf v hsv] at huv
      exact branch_injective hC hE htwins hsu hsv hdu hdv huv
  have budget := branch_budget hC hE active hdegree ho'
  exact ⟨S,covers,(Nat.add_le_add_left hcap _).trans budget⟩

end PEqualNP.Outside.L_meta_3289

namespace PEqualNP.Outside.L_meta_3289
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Graph construction adapted from R_meta_2866_42.
theorem incidenceCover : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ p r, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      (∀ z : Fin (N+N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ 2 →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        PEqualNP.MetaComplexity.circuitFun (N+N) C z = false) →

      let E := Finset.univ.filter (fun e : Fin N × Fin N =>
        I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N+N) C
          (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true)
      let A := E.image Prod.fst
      let B := E.image Prod.snd
      ∃ U V : Finset (Fin N), (∀ e ∈ E, (∃ f ∈ E, f.1 = e.1 ∧ f.2 ≠ e.2) →
          (∃ g ∈ E, g.2 = e.2 ∧ g.1 ≠ e.1) → e.1 ∈ U ∨ e.2 ∈ V) ∧
        A.card+B.card+U.card+V.card ≤ C.size+1 := by
  classical
  let L {N : ℕ} : Fin N → Fin (N+N) := Fin.castAdd N
  let R {N : ℕ} : Fin N → Fin (N+N) := Fin.natAdd N
  have sides {N : ℕ} (p l : Fin N) : L p ≠ R l := by
    intro equal
    have val := congrArg Fin.val equal
    change p.val = N + l.val at val
    have inRange := p.isLt
    omega
  have leftInjective {N : ℕ} : Function.Injective (@L N) := by
    intro a b eq
    have valuations : (L a).val = (L b).val := congrArg Fin.val eq
    exact Fin.ext valuations
  have rightInjective {N : ℕ} : Function.Injective (@R N) := by
    intro a b eq
    have val := congrArg Fin.val eq
    change N + a.val = N + b.val at val
    exact Fin.ext (by omega)
  let graph {N : ℕ} (I : Fin N → Fin N → Prop) : SimpleGraph (Fin (N+N)) :=
    SimpleGraph.fromRel (fun x y => ∃ p l, x = L p ∧ y = R l ∧ I p l)
  have adjEither {N : ℕ} (I : Fin N → Fin N → Prop) (x y : Fin (N+N)) :
      (graph I).Adj x y ↔
        (∃ p l, x = L p ∧ y = R l ∧ I p l) ∨ (∃ p l, y = L p ∧ x = R l ∧ I p l) := by
    unfold graph
    rw [SimpleGraph.fromRel_adj]
    constructor
    · exact And.right
    · intro ok
      refine ⟨?_,ok⟩
      rintro rfl
      rcases ok with ⟨p,l,atP,atL,_⟩ | ⟨p,l,atP,atL,_⟩
      · exact sides p l (atP.symm.trans atL)
      · exact sides p l (atP.symm.trans atL)
  have leftNeighbors {N : ℕ} (I : Fin N → Fin N → Prop) (p : Fin N) (y : Fin (N+N)) :
      (graph I).Adj (L p) y ↔ ∃ l, y = R l ∧ I p l := by
    rw [adjEither]
    constructor
    · rintro (⟨p',l,atP,atL,inc⟩ | ⟨p',l,_,invalid,_⟩)
      · exact ⟨l, atL, (leftInjective atP).symm ▸ inc⟩
      · exact (sides p l invalid).elim
    · rintro ⟨l,eq,inc⟩
      exact Or.inl ⟨p,l,rfl,eq,inc⟩
  have rightNeighbors {N : ℕ} (I : Fin N → Fin N → Prop) (l : Fin N) (y : Fin (N+N)) :
      (graph I).Adj (R l) y ↔ ∃ p, y = L p ∧ I p l := by
    rw [adjEither]
    constructor
    · rintro (⟨p,l',invalid,_,_⟩ | ⟨p,l',atP,atL,inc⟩)
      · exact (sides p l invalid.symm).elim
      · exact ⟨p,atP,(rightInjective atL).symm ▸ inc⟩
    · rintro ⟨p,eq,inc⟩
      exact Or.inr ⟨p,l,eq,rfl,inc⟩
  have leftRight {N : ℕ} (I : Fin N → Fin N → Prop) (p l : Fin N) :
      (graph I).Adj (L p) (R l) ↔ I p l := by
    rw [leftNeighbors]
    constructor
    · rintro ⟨k,eq,inc⟩
      exact (rightInjective eq).symm ▸ inc
    · exact fun inc => ⟨l,rfl,inc⟩
  have noFour {N : ℕ} (I : Fin N → Fin N → Prop)
      (unique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
      (u v a b : Fin (N+N)) (vertices : u ≠ v) (neighbors : a ≠ b)
      (ua : (graph I).Adj u a) (ub : (graph I).Adj u b)
      (va : (graph I).Adj v a) (vb : (graph I).Adj v b) : False := by
    have crosses (p l : Fin N) (otherP otherL : Fin (N+N))
        (differentP : L p ≠ otherP) (differentL : R l ≠ otherL)
        (pl : I p l) (pOther : (graph I).Adj (L p) otherL)
        (otherL' : (graph I).Adj otherP (R l)) (pair : (graph I).Adj otherP otherL) : False := by
      obtain ⟨k, rfl, pk⟩ := (leftNeighbors I p otherL).mp pOther
      obtain ⟨r, rfl, rl⟩ := (rightNeighbors I l otherP).mp ((graph I).adj_symm otherL')
      have rk := (leftRight I r k).mp pair
      have distinct : p ≠ r := fun eq => differentP (congrArg L eq)
      have same := (unique p r distinct).unique ⟨pl,rl⟩ ⟨pk,rk⟩
      exact differentL (congrArg R same)
    rcases (adjEither I u a).mp ua with ⟨p,l,rfl,rfl,pl⟩ | ⟨p,l,rfl,rfl,pl⟩
    · exact crosses p l v b vertices neighbors pl ub va vb
    · exact crosses p l b v neighbors vertices pl ((graph I).adj_symm va) ((graph I).adj_symm ub) ((graph I).adj_symm vb)
  intro N I inst C mono uniq sound
  let pair (u v i : Fin (N+N)) := decide (i = u ∨ i = v)
  let J (p l : Fin N) := I p l ∧ circuitFun (N+N) C (pair (L p) (R l)) = true
  let E := Finset.univ.filter (fun e : Fin N × Fin N => J e.1 e.2)
  let G := graph J
  have subAdj {u v} (h : G.Adj u v) : (graph I).Adj u v := by
    rcases (adjEither J u v).mp h with ⟨p,l,rfl,rfl,j⟩ | ⟨p,l,rfl,rfl,j⟩
    · exact (leftRight I p l).mpr j.1
    · exact (graph I).adj_symm ((leftRight I p l).mpr j.1)
  have hE : GraphEval C G := by
    intro u v
    let x := pair u v
    have fx : point {u,v} = x := by funext i; simp [point,x,pair]
    rw [fx]
    change circuitFun (N+N) C x = true ↔ G.Adj u v
    constructor
    · intro recognized
      have small : Fintype.card {l : Fin N // x (R l) = true} ≤ 2 := by
        let emb (l : {l : Fin N // x (R l) = true}) : ↥({u,v} : Finset (Fin (N+N))) :=
          ⟨R l.val, by simpa [x,pair] using l.property⟩
        apply (Fintype.card_le_of_injective emb (by
          intro a b eq; exact Subtype.ext (rightInjective (congrArg Subtype.val eq)))).trans
        simpa only [Fintype.card_coe, Finset.card_singleton] using
          Finset.card_insert_le (a := u) (s := ({v} : Finset (Fin (N+N))))
      have existsInc : ∃ p l, I p l ∧ x (L p) = true ∧ x (R l) = true := by
        by_contra missing
        rw [sound x small missing] at recognized
        contradiction
      obtain ⟨p,l,inc,onP,onL⟩ := existsInc
      rcases of_decide_eq_true onP with hp | hp <;> rcases of_decide_eq_true onL with hl | hl
      · exact (sides p l (hp.trans hl.symm)).elim
      · subst u; subst v
        exact (leftRight J p l).mpr ⟨inc, recognized⟩
      · subst v; subst u
        apply G.adj_symm
        apply (leftRight J p l).mpr
        refine ⟨inc,?_⟩
        convert recognized using 1 <;> simp [x,pair,Bool.or_comm]
      · exact (sides p l (hp.trans hl.symm)).elim
    · intro hit
      rcases (adjEither J u v).mp hit with ⟨p,l,rfl,rfl,j⟩ | ⟨p,l,rfl,rfl,j⟩
      · exact j.2
      · have eq : x = pair (L p) (R l) := by funext i; simp [x,pair,Bool.or_comm]
        rw [eq]; exact j.2
  have neighbors (v : Fin (N+N)) (h : 2 ≤ (G.neighborSet v).ncard) :
      ∃ a b, a ≠ b ∧ G.Adj v a ∧ G.Adj v b := by
    have finite : (G.neighborSet v).Finite := Set.toFinite _
    rw [Set.ncard_eq_toFinset_card _ finite] at h
    obtain ⟨a,b,ha,hb,ne⟩ := Finset.one_lt_card_iff.mp h
    exact ⟨a,b,ne,finite.mem_toFinset.mp ha,finite.mem_toFinset.mp hb⟩
  have noTwins (v w : Fin (N+N)) (diff : v ≠ w) (_ : ¬ G.Adj v w)
      (hv : 2 ≤ (G.neighborSet v).ncard) (_ : 2 ≤ (G.neighborSet w).ncard) :
      ∃ a, ¬(G.Adj v a ↔ G.Adj w a) := by
    by_contra! same
    obtain ⟨a,b,distinct,va,vb⟩ := neighbors v hv
    exact noFour I uniq v w a b diff distinct (subAdj va) (subAdj vb)
      (subAdj ((same a).mp va)) (subAdj ((same b).mp vb))
  have other (v w : Fin (N+N)) (h : 2 ≤ (G.neighborSet v).ncard) : ∃ a, G.Adj v a ∧ a ≠ w := by
    obtain ⟨a,b,diff,ha,hb⟩ := neighbors v h
    by_cases eq : a = w
    · exact ⟨b,hb,fun h => diff (eq.trans h.symm)⟩
    · exact ⟨a,ha,eq⟩
  have adjacent (v w : Fin (N+N)) (edge : G.Adj v w)
      (hv : 2 ≤ (G.neighborSet v).ncard) (hw : 2 ≤ (G.neighborSet w).ncard) :
      ∃ a b, G.Adj v a ∧ a ≠ w ∧ G.Adj w b ∧ b ≠ v ∧ (a=b ∨ ¬ G.Adj a b) := by
    obtain ⟨a,va,aw⟩ := other v w hv
    obtain ⟨b,wb,bv⟩ := other w v hw
    exact ⟨a,b,va,aw,wb,bv,Or.inr (fun ab => noFour I uniq w a v b aw.symm bv.symm
      (subAdj (G.adj_symm edge)) (subAdj wb) (subAdj (G.adj_symm va)) (subAdj ab))⟩
  let A := E.image Prod.fst
  let B := E.image Prod.snd
  let active := A.image L ∪ B.image R
  have degree (v) (hv : v ∈ active) : ∃ u, G.Adj v u := by
    rcases Finset.mem_union.mp hv with ha | hb
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hp
      exact ⟨_,(leftRight J _ _).mpr (Finset.mem_filter.mp he).2⟩
    · obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hl
      exact ⟨_,G.adj_symm ((leftRight J _ _).mpr (Finset.mem_filter.mp he).2)⟩
  obtain ⟨S,covered,budget⟩ := coverBudget mono hE active degree noTwins adjacent
  let U := Finset.univ.filter fun p : Fin N => L p ∈ S
  let V := Finset.univ.filter fun l : Fin N => R l ∈ S
  refine ⟨U,V,?_,?_⟩
  · intro e he hl hr
    change e.1 ∈ U ∨ e.2 ∈ V
    have two {v a b : Fin (N+N)} (ha : G.Adj v a) (hb : G.Adj v b) (ne : a ≠ b) :
        2 ≤ (G.neighborSet v).ncard := by
      have finite : (G.neighborSet v).Finite := Set.toFinite _
      rw [Set.ncard_eq_toFinset_card _ finite]
      exact Finset.one_lt_card_iff.mpr ⟨a,b,finite.mem_toFinset.mpr ha,finite.mem_toFinset.mpr hb,ne⟩
    obtain ⟨f,hf,fe,off⟩ := hl
    obtain ⟨g,hg,ge,off'⟩ := hr
    have ee := (leftRight J _ _).mpr ((Finset.mem_filter.mp he).2 : J e.1 e.2)
    have ff := (leftRight J _ _).mpr ((Finset.mem_filter.mp hf).2 : J f.1 f.2)
    have gg := (leftRight J _ _).mpr ((Finset.mem_filter.mp hg).2 : J g.1 g.2)
    rw [fe] at ff
    rw [ge] at gg
    exact (covered _ _ ee (two ff ee (fun h => off (rightInjective h)))
      (two (G.adj_symm gg) (G.adj_symm ee) (fun h => off' (leftInjective h)))).imp
      (fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
      (fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  · have disjoint (X Y : Finset (Fin N)) : Disjoint (X.image L) (Y.image R) := by
      rw [Finset.disjoint_left]
      intro v h k
      obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨l,_,eq⟩ := Finset.mem_image.mp k
      exact sides p l eq.symm
    have activeCount : active.card = A.card+B.card := by
      rw [Finset.card_union_of_disjoint (disjoint A B), Finset.card_image_of_injective _ leftInjective,
        Finset.card_image_of_injective _ rightInjective]
    have less : U.image L ∪ V.image R ⊆ S := by
      intro v hv
      rcases Finset.mem_union.mp hv with h | h
      · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h; exact (Finset.mem_filter.mp hp).2
      · obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp h; exact (Finset.mem_filter.mp hl).2
    have hc := Finset.card_le_card less
    rw [Finset.card_union_of_disjoint (disjoint U V), Finset.card_image_of_injective _ leftInjective,
      Finset.card_image_of_injective _ rightInjective] at hc
    change A.card+B.card+U.card+V.card ≤ C.size+1
    omega

end PEqualNP.Outside.L_meta_3289

namespace PEqualNP.Outside.L_meta_3289

theorem side {α β : Type} [DecidableEq α] [DecidableEq β]
    (E X : Finset β) (f : β → α) (U : Finset α) (hX : X ⊆ E)
    (deg : ∀ u, (E.filter fun e => f e = u).card ≤ 131)
    (extra : ∀ e ∈ X, f e ∈ U ∨ (E.filter fun j => f j = f e).card ≤ 1) :
    E.card + X.card ≤ 131 * ((E.image f).card + U.card) := by
  classical
  let A := E.image f
  have hE := Finset.card_eq_sum_card_fiberwise (s := E) (t := A)
    (f := f) (fun e he => Finset.mem_image_of_mem f he)
  have hY := Finset.card_eq_sum_card_fiberwise (s := X) (t := A)
    (f := f) (fun e he => Finset.mem_image_of_mem f (hX he))
  rw [hE,hY,← Finset.sum_add_distrib]
  have each (u : α) :
      (E.filter fun e => f e = u).card + (X.filter fun e => f e = u).card ≤
        131 + (if u ∈ U then 131 else 0) := by
    have sub := Finset.card_le_card (Finset.filter_subset_filter (fun e => f e = u) hX)
    have main := deg u
    by_cases hu : u ∈ U
    · simp [hu]; omega
    · simp only [hu, ite_false, Nat.add_zero]
      by_cases h : (X.filter fun e => f e = u).Nonempty
      · obtain ⟨e,he⟩ := h
        obtain ⟨hx,rfl⟩ := Finset.mem_filter.mp he
        have small := (extra e hx).resolve_left hu
        omega
      · rw [Finset.not_nonempty_iff_eq_empty.mp h]
        simpa using main
  calc
    _ ≤ ∑ u ∈ A, (131 + (if u ∈ U then 131 else 0) : ℕ) :=
      Finset.sum_le_sum (fun u _ => each u)
    _ = 131 * A.card + 131 * (A.filter (· ∈ U)).card := by
      rw [Finset.sum_add_distrib,← Finset.sum_filter]
      simp [Nat.mul_comm]
    _ ≤ _ := by
      have h := Finset.card_le_card (show A.filter (· ∈ U) ⊆ U from
        fun _ h => (Finset.mem_filter.mp h).2)
      change _ ≤ 131 * (A.card + U.card)
      omega



theorem cover {N : ℕ} (E : Finset (Fin N × Fin N))
    (U V : Finset (Fin N))
    (left : ∀ u, (E.filter fun e => e.1 = u).card ≤ 131)
    (right : ∀ u, (E.filter fun e => e.2 = u).card ≤ 131)
    (cover : ∀ e ∈ E, (∃ f ∈ E, f.1 = e.1 ∧ f.2 ≠ e.2) →
          (∃ g ∈ E, g.2 = e.2 ∧ g.1 ≠ e.1) → e.1 ∈ U ∨ e.2 ∈ V) :
    3 * E.card ≤ 131*((E.image Prod.fst).card + (E.image Prod.snd).card + U.card + V.card) := by
  classical
  let L (e : Fin N × Fin N) := e.1 ∈ U ∨ (E.filter fun f => f.1 = e.1).card ≤ 1
  let X := E.filter L
  let Y := E.filter fun e => ¬ L e
  have l := PEqualNP.Outside.L_meta_3289.side E X Prod.fst U (Finset.filter_subset _ _) left
    (fun _ he => (Finset.mem_filter.mp he).2)
  have r := PEqualNP.Outside.L_meta_3289.side E Y Prod.snd V (Finset.filter_subset _ _) right (by
    intro e he
    obtain ⟨mem,neg⟩ := Finset.mem_filter.mp he
    change ¬ (_ ∨ _) at neg
    by_cases hv : e.2 ∈ V
    · exact Or.inl hv
    right
    have more : ∃ f ∈ E, f.1 = e.1 ∧ f.2 ≠ e.2 := by
      by_contra! no
      apply neg
      right
      apply Finset.card_le_one_iff.mpr
      intro a b ha hb
      obtain ⟨am,ae⟩ := Finset.mem_filter.mp ha
      obtain ⟨bm,be⟩ := Finset.mem_filter.mp hb
      exact Prod.ext (ae.trans be.symm) ((no a am ae).trans (no b bm be).symm)
    apply Finset.card_le_one_iff.mpr
    have uniq (g) (m : g ∈ E) (eq : g.2 = e.2) : g.1 = e.1 := by
      by_contra off
      exact (cover e mem more ⟨g,m,eq,off⟩).elim (fun u => neg (Or.inl u)) hv
    intro a b ha hb
    obtain ⟨am,ae⟩ := Finset.mem_filter.mp ha
    obtain ⟨bm,be⟩ := Finset.mem_filter.mp hb
    exact Prod.ext ((uniq a am ae).trans (uniq b bm be).symm) (ae.trans be.symm))
  have total : X.card + Y.card = E.card := Finset.card_filter_add_card_filter_not (s := E) L
  omega

theorem finish (e p l t s : Nat)
    (weight : 3*e ≤ 131*(p+l+t))
    (gateCount : p + l + t ≤ s + 1)
    (productBound : e ≤ p * l) : e ≤ 44 * s := by
  by_cases large : 131 ≤ s
  · omega
  · by_cases smallP : p ≤ 44
    · by_cases empty : p = 0
      · simp_all
      · have h := Nat.mul_le_mul_right l smallP
        omega
    · by_cases smallL : l ≤ 44
      · have h := Nat.mul_le_mul_left p smallL
        by_cases empty : l = 0
        · simp_all
        · omega
      · have aux : p*l + p*l ≤ p*p + l*l := by
          rcases Nat.le_total p l with hpl | hlp
          · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hpl
            simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm k p]
            omega
          · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hlp
            simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm k l]
            omega
        have sq := Nat.mul_le_mul_left (p+l) (show p+l ≤ 131 by omega)
        simp only [Nat.mul_add, Nat.add_mul, Nat.mul_comm l p] at sq
        omega


-- Point-degree proof adapted from R_meta_2130_1.
theorem geometry (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (upper : q ≤ 130) (hN : N = q^2+q+1)
    (hcol : ∀ l, Fintype.card {p : Fin N // I p l} = q+1)
    (huniq : ∀ p r, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (E : Finset (Fin N × Fin N)) (inc : ∀ e ∈ E, I e.1 e.2)
    (U V : Finset (Fin N)) (s : ℕ)
    (cover : ∀ e ∈ E, (∃ f ∈ E, f.1 = e.1 ∧ f.2 ≠ e.2) →
          (∃ g ∈ E, g.2 = e.2 ∧ g.1 ≠ e.1) → e.1 ∈ U ∨ e.2 ∈ V)
    (budget : (E.image Prod.fst).card+(E.image Prod.snd).card+U.card+V.card ≤ s+1) :
    E.card ≤ 44*s := by
  classical
  have hfour : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p' l ∧ I p l' ∧ I p' l') := by
    intro p p' l l' hpp hll h
    obtain ⟨h11, h21, h12, h22⟩ := h
    obtain ⟨lstar, _, huniq'⟩ := huniq p p' hpp
    exact hll ((huniq' l ⟨h11, h21⟩).trans (huniq' l' ⟨h12, h22⟩).symm)
  have hpt_deg : ∀ p : Fin N, (Finset.univ.filter fun l : Fin N => I p l).card = q + 1 := by
    intro p
    let Lp := Finset.univ.filter fun l : Fin N => I p l
    have hpart : (Finset.univ.erase p : Finset (Fin N)) =
        Lp.biUnion (fun l => (Finset.univ.filter fun p' : Fin N => I p' l).erase p) := by
      ext p'
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_biUnion, Lp,
        Finset.mem_filter, true_and]
      constructor
      · intro hne
        obtain ⟨l, ⟨hp1, hp2⟩, _⟩ := huniq p p' hne.symm
        exact ⟨l, hp1, hne, hp2⟩
      · rintro ⟨_, _, hne, _⟩
        exact hne
    have hdisj : Set.PairwiseDisjoint (↑Lp) (fun l => (Finset.univ.filter fun p' : Fin N => I p' l).erase p) := by
      intro l₁ hl₁ l₂ hl₂ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro p' hp1 hp2
      have h1 := Finset.mem_erase.mp hp1
      have h2 := Finset.mem_erase.mp hp2
      have h1' := (Finset.mem_filter.mp h1.2).2
      have h2' := (Finset.mem_filter.mp h2.2).2
      have hl1' := (Finset.mem_filter.mp hl₁).2
      have hl2' := (Finset.mem_filter.mp hl₂).2
      exact hfour p p' l₁ l₂ h1.1.symm hne ⟨hl1', h1', hl2', h2'⟩
    have hcard_eq := congrArg Finset.card hpart
    rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin,
      Finset.card_biUnion hdisj] at hcard_eq
    have hsum_q : ∑ l ∈ Lp, ((Finset.univ.filter fun p' : Fin N => I p' l).erase p).card = Lp.card * q := by
      have heach : ∀ l ∈ Lp, ((Finset.univ.filter fun p' : Fin N => I p' l).erase p).card = q := by
        intro l hl
        have hmem : p ∈ Finset.univ.filter (fun p' : Fin N => I p' l) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl).2⟩
        rw [Finset.card_erase_of_mem hmem]
        have hc := hcol l
        rw [Fintype.card_subtype] at hc
        omega
      rw [Finset.sum_congr rfl heach]
      simp
    rw [hsum_q] at hcard_eq
    have hN1 : N - 1 = (q + 1) * q := by
      rw [hN, Nat.add_sub_cancel]
      ring
    rw [hN1] at hcard_eq
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) hcard_eq.symm

  have left (u : Fin N) : (E.filter fun e => e.1 = u).card ≤ 131 := by
    apply le_trans (b := (Finset.univ.filter fun v => I u v).card)
    · apply Finset.card_le_card_of_injOn Prod.snd
      · intro e he
        obtain ⟨hm,rfl⟩ := Finset.mem_filter.mp he
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,inc e hm⟩
      · intro a ha b hb he
        exact Prod.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) he
    · rw [hpt_deg]; omega
  have right (v : Fin N) : (E.filter fun e => e.2 = v).card ≤ 131 := by
    apply le_trans (b := (Finset.univ.filter fun u => I u v).card)
    · apply Finset.card_le_card_of_injOn Prod.fst
      · intro e he
        obtain ⟨hm,rfl⟩ := Finset.mem_filter.mp he
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,inc e hm⟩
      · intro a ha b hb he
        exact Prod.ext he ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
    · have h := hcol v
      rw [Fintype.card_subtype] at h
      omega
  have weight := PEqualNP.Outside.L_meta_3289.cover E U V left right cover
  have contain : E ⊆ (E.image Prod.fst) ×ˢ (E.image Prod.snd) := fun e he =>
    Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ he, Finset.mem_image_of_mem _ he⟩
  apply PEqualNP.Outside.L_meta_3289.finish E.card _ _ (U.card+V.card) s
  · simpa only [Nat.add_assoc] using weight
  · simpa only [Nat.add_assoc] using budget
  · simpa only [Finset.card_product] using Finset.card_le_card contain

end PEqualNP.Outside.L_meta_3289

theorem PEqualNP.Outside.L_meta_3289 :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (2 : ℕ) ≤ x1 → x1 ≤ (130 : ℕ) → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → Fintype.card { x13 : Fin x2 × Fin x2 // x3 x13.1 x13.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x13.1 ∨ x14 = Fin.natAdd x2 x13.2)) = Bool.true } ≤ (44 : ℕ) * x5.size := by
  classical
  intro q N I inst C hq upper order columns unique mono sound
  let E := Finset.univ.filter (fun e : Fin N × Fin N =>
        I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N+N) C
          (fun i => decide (i = Fin.castAdd N e.1 ∨ i = Fin.natAdd N e.2)) = true)
  obtain ⟨U,V,covered,budget⟩ := PEqualNP.Outside.L_meta_3289.incidenceCover N I C mono unique
    (fun z h zneg => sound z (h.trans hq) zneg)
  have sub : ∀ e ∈ E, I e.1 e.2 := fun e he => (Finset.mem_filter.mp he).2.1
  have bound := PEqualNP.Outside.L_meta_3289.geometry q N I hq upper order columns unique E sub U V C.size covered budget
  simpa only [E, Fintype.card_subtype] using bound
