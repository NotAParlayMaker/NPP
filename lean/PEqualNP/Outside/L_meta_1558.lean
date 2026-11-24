import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1558

open PEqualNP.CircuitLowerBounds

-- The wire evaluation lemmas follow L-meta-1457.
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

lemma or_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n ≤ w) (h : w - n < C.gates.length) (hop : C.gates[w - n].op = GateOp.or) :
    value C x w = true ↔ ∃ r ∈ C.gates[w - n].inputs, r < w ∧ value C x r = true := by
  have hlt : w < n + C.size := by unfold Circuit.size; omega
  rw [gate_value C x w hw hlt]
  simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨r, hr, hv⟩
    by_cases h' : r < w
    · exact ⟨r, hr, h', by simpa [h'] using hv⟩
    · simp [h'] at hv
  · rintro ⟨r, hr, h', hv⟩
    exact ⟨r, hr, by simp [h', hv]⟩

lemma and_false {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n ≤ w) (h : w - n < C.gates.length) (hop : C.gates[w - n].op = GateOp.and) :
    value C x w = false ↔ ∃ r ∈ C.gates[w - n].inputs, w ≤ r ∨ value C x r = false := by
  have hlt : w < n + C.size := by unfold Circuit.size; omega
  rw [gate_value C x w hw hlt]
  simp only [hop, GateOp.eval, List.all_map, List.all_eq_false, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨r, hr, hf⟩
    by_cases h' : r < w
    · exact ⟨r, hr, Or.inr (by simpa [h'] using hf)⟩
    · exact ⟨r, hr, Or.inl (by omega)⟩
  · rintro ⟨r, hr, hf | hf⟩
    · exact ⟨r, hr, by simp [show ¬ r < w by omega]⟩
    · exact ⟨r, hr, by simp [hf]⟩

-- The backward expansion from L-meta-1461 is specialized to a fixed negative input.
private lemma cut {n : ℕ} (C : Circuit) (neg : Fin n → Bool) (G paid : Finset ℕ)
    (parents : ∀ w ∈ G, ∃ P : Finset ℕ, P.card ≤ 2 ∧ (w ∉ paid → P.card ≤ 1) ∧
      (∀ r ∈ P, r<w) ∧ ∀ x : Fin n → Bool,
        (∀ r ∈ P, value C x r=true → value C neg r=true) → value C x w=true → value C neg w=true)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G → w < t) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ F.card + ((G ∩ paid).filter (· < t)).card ∧
      ∀ x : Fin n → Bool,
        (∀ w ∈ B, value C x w=true → value C neg w=true) →
        ∀ w ∈ F, value C x w=true → value C neg w=true := by
  induction t generalizing F with
  | zero =>
    exact ⟨F,Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega),
      Nat.le_add_right ..,fun _ h => h⟩
  | succ t ih =>
    have increases : ((G ∩ paid).filter (· < t)).card ≤ ((G ∩ paid).filter (· < t+1)).card :=
      Finset.card_le_card fun w hw => Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hw).1,by have := (Finset.mem_filter.mp hw).2; omega⟩
    by_cases expand : t ∈ F ∧ t ∈ G
    · obtain ⟨P,lim,free,lt,step⟩ := parents t expand.2
      let F' := F.erase t ∪ P
      have smaller : ∀ w ∈ F', w ∈ G → w < t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw|hw
        · have ne := (Finset.mem_erase.mp hw).1
          have := hF w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact lt w hw
      obtain ⟨B,dis,size,chains⟩ := ih F' smaller
      refine ⟨B,dis,?_,?_⟩
      · have union := Finset.card_union_le (F.erase t) P
        change F'.card ≤ _ at union
        have old := Finset.card_erase_add_one expand.1
        by_cases hp : t ∈ paid
        · have eq : (G ∩ paid).filter (· < t+1) = insert t ((G ∩ paid).filter (· < t)) := by
            ext w
            simp only [Finset.mem_filter,Finset.mem_insert]
            constructor
            · rintro ⟨inc,bound⟩
              by_cases ne : w=t
              · exact Or.inl ne
              · exact Or.inr ⟨inc,by omega⟩
            · rintro (rfl|⟨inc,bound⟩)
              · exact ⟨Finset.mem_inter.mpr ⟨expand.2,hp⟩,by omega⟩
              · exact ⟨inc,by omega⟩
          rw [eq,Finset.card_insert_of_notMem (by simp)]
          omega
        · have := free hp
          omega
      · intro x hxy w hw
        by_cases eq : w=t
        · subst w
          exact step x fun r hr => chains x hxy r (Finset.mem_union_right _ hr)
        · exact chains x hxy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hw⟩))
    · have smaller : ∀ w ∈ F, w ∈ G → w<t := by
        intro w hw hg
        have ne : w≠t := fun e => expand ⟨e ▸ hw,e ▸ hg⟩
        have := hF w hw hg
        omega
      obtain ⟨B,dis,size,chains⟩ := ih F smaller
      exact ⟨B,dis,by omega,chains⟩

abbrev P := Fin 13
abbrev Good (C : Circuit) := ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def isOrWire (C : Circuit) (w : ℕ) : Prop :=
  ∃ i : Fin C.gates.length, w = 13 + i.val ∧ (C.gates.get i).op = GateOp.or

noncomputable def orWires (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.Ico 13 (13+C.size)).filter (isOrWire C)

def input (U : Finset P) (v : P) := decide (v ∈ U)
def neg (N : Finset P) (v : P) := decide (v ∉ N)
def hits (C : Circuit) (T : Finset P) (R : P → Finset P) (w : ℕ) :=
  T.filter (fun p => value C (input (R p)) w = true)

def wide (C : Circuit) (N T : Finset P) (R : P → Finset P) (w : ℕ) : Prop :=
  value C (neg N) w = false ∧ 2 ≤ (hits C T R w).card

noncomputable def eligible (C : Circuit) (N T : Finset P) (R : P → Finset P) : Finset ℕ := by
  classical
  exact (Finset.Ico 13 (13+C.size)).filter (wide C N T R)

noncomputable def pay (C : Circuit) (N T : Finset P) (R : P → Finset P) : Finset ℕ :=
  eligible C N T R ∩ orWires C

lemma row (C : Circuit) (valid : Good C) (N T : Finset P) (R : P → Finset P) (o : ℕ)
    (sep : ∀ p ∈ T, R p ∩ N = {p}) (hneg : value C (neg N) o = false)
    (hpos : ∀ p ∈ T, value C (input (R p)) o = true) :
    T.card - 1 ≤ (pay C N T R).card := by
  classical
  let G := eligible C N T R
  have isGate (w : ℕ) (c : wide C N T R w) : 13 ≤ w ∧ w < 13+C.size := by
    obtain ⟨zero,big⟩ := c
    constructor
    · by_contra! lt
      let a : P := ⟨w,lt⟩
      have aa : a ∈ N := by
        change value C (neg N) a = false at zero
        simpa [input_value, neg] using zero
      have sub : hits C T R w ⊆ {a} := by
        intro p hp
        obtain ⟨ht, hv⟩ := Finset.mem_filter.mp hp
        change value C (input (R p)) a = true at hv
        have both : a ∈ R p ∩ N := Finset.mem_inter.mpr ⟨by simpa [input_value,input] using hv,aa⟩
        rw [sep p ht, Finset.mem_singleton] at both
        simpa only [Finset.mem_singleton] using both.symm
      have bound := Finset.card_le_card sub
      simp only [Finset.card_singleton] at bound
      omega
    · by_contra! high
      have none : hits C T R w = ∅ := by ext p; simp [hits, missing_value C _ w high]
      simp [none] at big
  have parents (w : ℕ) (hw : w ∈ G) : ∃ S : Finset ℕ, S.card ≤ 2 ∧
      (w ∉ orWires C → S.card ≤ 1) ∧ (∀ r ∈ S, r < w) ∧
      ∀ x : P → Bool, (∀ r ∈ S, value C x r = true → value C (neg N) r = true) →
      value C x w = true → value C (neg N) w = true := by
    obtain ⟨bounds, c⟩ := Finset.mem_filter.mp (show w ∈ (Finset.Ico 13 (13+C.size)).filter (wide C N T R) from hw)
    obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp bounds
    have ix : w - 13 < C.gates.length := by unfold Circuit.size at hi; omega
    obtain ⟨ha | ho,_⟩ := valid C.gates[w-13] (List.getElem_mem _)
    · obtain ⟨r,hr,bad⟩ := (and_false C (neg N) w lo ix ha).mp c.1
      by_cases lt : r < w
      · have no := bad.resolve_left (Nat.not_le_of_gt lt)
        refine ⟨{r},by simp,by simp,by simpa using lt,?_⟩
        intro x step hx
        cases hx' : value C x r with
        | false => exact (Bool.false_ne_true (((and_false C x w lo ix ha).mpr ⟨r, hr, Or.inr hx'⟩).symm.trans hx)).elim
        | true => exact (Bool.false_ne_true (no.symm.trans (step r (Finset.mem_singleton_self r) hx'))).elim
      · refine ⟨∅,by simp,by simp,by simp,?_⟩
        intro x _ hx
        exact (Bool.false_ne_true (((and_false C x w lo ix ha).mpr ⟨r,hr,Or.inl (by omega)⟩).symm.trans hx)).elim
    · have isOr : w ∈ orWires C := Finset.mem_filter.mpr ⟨bounds, ⟨⟨w-13,ix⟩,by change w = 13 + (w-13); omega,ho⟩⟩
      obtain ⟨S, size, lt, step⟩ := gate_inputs C valid w lo hi
      exact ⟨S,size,fun missing => (missing isOr).elim,lt,fun x => step x (neg N)⟩
  obtain ⟨B,dis,size,chain⟩ := cut C (neg N) G (orWires C) parents (13+C.size) {o}
    (fun w _ hg => (Finset.mem_Ico.mp (Finset.mem_filter.mp hg).1).2)
  let parts (w : ℕ) := if value C (neg N) w = false then hits C T R w else ∅
  have small (w : ℕ) (hb : w ∈ B) : (parts w).card ≤ 1 := by
    by_cases zero : value C (neg N) w = false
    · simp only [parts,ite_eq_left zero]
      by_contra! big
      have c : wide C N T R w := ⟨zero,by omega⟩
      exact Finset.disjoint_left.mp dis hb (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (isGate w c),c⟩)
    · simp [parts,zero]
  have cover : T ⊆ B.biUnion parts := by
    intro p hp
    by_contra no
    have step (w : ℕ) (hb : w ∈ B) (yes : value C (input (R p)) w=true) : value C (neg N) w=true := by
      cases zero : value C (neg N) w with
      | true => rfl
      | false => exact (no (Finset.mem_biUnion.mpr ⟨w,hb,by simp [parts,zero,hits,hp,yes]⟩)).elim
    exact Bool.false_ne_true (hneg.symm.trans (chain (input (R p)) step o (Finset.mem_singleton_self o) (hpos p hp)))
  have bound := (Finset.card_le_card cover).trans (Finset.card_biUnion_le_card_mul B parts 1 small)
  have lim := Finset.card_filter_le (G ∩ orWires C) (· < 13+C.size)
  change ((G ∩ orWires C).filter (· < 13+C.size)).card ≤ (pay C N T R).card at lim
  simp only [Finset.card_singleton] at size
  simp only [mul_one] at bound
  omega

def clash (N T : P → Finset P) (R : P → P → Finset P) (i j : P) : Prop :=
  ∃ p ∈ T i, p ∉ N j ∧ (R i p ∩ N j).Nonempty

lemma collect (C : Circuit) (valid : Good C) (N T : P → Finset P) (R : P → P → Finset P)
    (o : P → ℕ) (inside : ∀ i, T i ⊆ N i) (thin : ∀ i j, i ≠ j → (N i ∩ N j).card ≤ 1)
    (sep : ∀ i p, p ∈ T i → R i p ∩ N i = {p})
    (apart : ∀ i j, i ≠ j → ¬ (clash N T R i j ∧ clash N T R j i))
    (low : ∀ i, value C (neg (N i)) (o i) = false)
    (pos : ∀ i p, p ∈ T i → value C (input (R i p)) (o i) = true) :
    (∑ i : P, ((T i).card - 1)) ≤ (orWires C).card := by
  classical
  let bills (i : P) := pay C (N i) (T i) (R i)
  have info {w : ℕ} {i : P} (hw : w ∈ bills i) : wide C (N i) (T i) (R i) w :=
    (Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).2
  have cross {w : ℕ} {i j : P} (ne : i ≠ j) (hi : w ∈ bills i) (hj : w ∈ bills j) : clash N T R i j := by
    let H := hits C (T i) (R i) w
    have many : 2 ≤ H.card := (info hi).2
    have outside : ∃ p ∈ H, p ∉ N j := by
      by_contra! allIn
      have sub : H ⊆ N i ∩ N j := fun p hp =>
        Finset.mem_inter.mpr ⟨inside i (Finset.mem_filter.mp hp).1,allIn p hp⟩
      have lim := Finset.card_le_card sub
      have lim' := thin i j ne
      omega
    obtain ⟨p,hp,pj⟩ := outside
    obtain ⟨pt,fires⟩ := Finset.mem_filter.mp hp
    refine ⟨p,pt,pj,?_⟩
    by_contra dry
    have le (v : P) (hv : input (R i p) v = true) : neg (N j) v = true := by
      exact decide_eq_true (fun h => dry ⟨v, Finset.mem_inter.mpr ⟨of_decide_eq_true hv,h⟩⟩)
    have both := value_mono C valid _ _ le w fires
    exact Bool.false_ne_true ((info hj).1.symm.trans both)
  have dis (i j : P) (diff : i ≠ j) : Disjoint (bills i) (bills j) := by
    apply Finset.disjoint_left.mpr
    intro w hi hj
    exact apart i j diff ⟨cross diff hi hj,cross diff.symm hj hi⟩
  have sub : Finset.univ.biUnion bills ⊆ orWires C := by
    intro w hw
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hw
    exact (Finset.mem_inter.mp hi).2
  calc
    (∑ i : P, ((T i).card-1)) ≤ ∑ i : P, (bills i).card :=
      Finset.sum_le_sum fun i _ => row C valid _ _ _ _ (sep i) (low i) (pos i)
    _ = (Finset.univ.biUnion bills).card := (Finset.card_biUnion (fun i _ j _ h => dis i j h)).symm
    _ ≤ _ := Finset.card_le_card sub

lemma or_split (C : Circuit) (onlyOr : ∀ g ∈ C.gates, g.op = GateOp.or)
    (x y : P → Bool) (w : ℕ) : value C (fun v => x v || y v) w = true →
    value C x w = true ∨ value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases var : w < 13
    · let p : P := ⟨w,var⟩
      change value C _ p = true → value C x p = true ∨ value C y p = true
      simp [input_value]
    by_cases range : w < 13+C.size
    · have before : w-13 < C.gates.length := by unfold Circuit.size at range; omega
      have hop := onlyOr C.gates[w-13] (List.getElem_mem _)
      simp only [or_value C _ w (by omega) before hop]
      rintro ⟨r,hr,lt,hy⟩
      rcases ih r lt hy with yes | yes
      · exact Or.inl ⟨r,hr,lt,yes⟩
      · exact Or.inr ⟨r,hr,lt,yes⟩
    · simp [missing_value C _ w (by omega : 13+C.size ≤ w)]

def line (i : P) : Finset P := {i, i + 1, i + 3, i + 9}

def domain (x : P → Bool) : Prop :=
  ∃ a b : P, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ line t ∧ b ∈ line t) ∧
    x a = true ∧ x b = true

def targets (i : P) : Finset P := if i = 0 then {1, 3, 9} else line i

def boost (i p : P) : Finset P :=
  match i.1, p.1 with
  | 0, 1 => {10}
  | 0, 3 => {10}
  | 0, 9 => {10}
  | 1, 1 => {12}
  | 1, 2 => {5}
  | 1, 4 => {12}
  | 1, 10 => {12}
  | 2, 2 => {1}
  | 2, 3 => {10}
  | 2, 5 => {1}
  | 2, 11 => {1}
  | 3, 3 => {5}
  | 3, 4 => {1}
  | 3, 6 => {5}
  | 3, 12 => {5}
  | 4, 0 => {9, 11}
  | 4, 4 => {9}
  | 4, 5 => {9}
  | 4, 7 => {9}
  | 5, 1 => {7}
  | 5, 5 => {9}
  | 5, 6 => {7}
  | 5, 8 => {7}
  | 6, 2 => {3}
  | 6, 6 => {3}
  | 6, 7 => {3}
  | 6, 9 => {10}
  | 7, 3 => {4}
  | 7, 7 => {11}
  | 7, 8 => {4}
  | 7, 10 => {4}
  | 8, 4 => {2}
  | 8, 8 => {3}
  | 8, 9 => {2}
  | 8, 11 => {2}
  | 9, 5 => {8}
  | 9, 9 => {8}
  | 9, 10 => {8}
  | 9, 12 => {6}
  | 10, 0 => {1, 4}
  | 10, 6 => {4}
  | 10, 10 => {8}
  | 10, 11 => {4}
  | 11, 1 => {8}
  | 11, 7 => {9}
  | 11, 11 => {9}
  | 11, 12 => {9}
  | 12, 0 => {3, 6}
  | 12, 2 => {3}
  | 12, 8 => {3}
  | 12, 12 => {7}
  | _, _ => ∅

def test (i p : P) : Finset P := insert p (boost i p)

lemma geoThin : ∀ i j : P, i ≠ j → (line i ∩ line j).card ≤ 1 := by decide

lemma target_sub : ∀ i : P, targets i ⊆ line i := by decide

lemma partial_sum : (∑ i : P, ((targets i).card - 1)) = 38 := by decide

lemma full_sum : (∑ i : P, ((line i).card - 1)) = 39 := by decide

set_option maxHeartbeats 2000000 in
lemma test_sep : ∀ i p : P, p ∈ targets i → test i p ∩ line i = {p} := by decide

def clashSet (i j : P) : Finset P :=
  (targets i).filter fun p => p ∉ line j ∧ (test i p ∩ line j).card ≠ 0

lemma clash_eq (i j : P) :
    clash line targets test i j ↔ (clashSet i j).card ≠ 0 := by
  constructor
  · rintro ⟨p, hpT, hpj, hv⟩
    refine Finset.card_ne_zero.mpr ⟨p, ?_⟩
    exact Finset.mem_filter.mpr ⟨hpT, And.intro hpj (Finset.card_ne_zero.mpr hv)⟩
  · intro hcard
    obtain ⟨p, hp⟩ := Finset.card_ne_zero.mp hcard
    have hsplit := Finset.mem_filter.mp hp
    exact ⟨p, hsplit.1, hsplit.2.1, Finset.card_ne_zero.mp hsplit.2.2⟩

set_option maxHeartbeats 2000000 in
lemma no_mutual : ∀ i j : P, i ≠ j →
    (clashSet i j).card = 0 ∨ (clashSet j i).card = 0 := by decide

lemma apart_ok : ∀ i j : P, i ≠ j →
    ¬ (clash line targets test i j ∧ clash line targets test j i) := by
  intro i j hij both
  have h := no_mutual i j hij
  have h1 := (clash_eq i j).mp both.1
  have h2 := (clash_eq j i).mp both.2
  cases h with
  | inl z => exact h1 z
  | inr z => exact h2 z

lemma not_together (a b : P)
    (h0 : ¬ (a ∈ line 0 ∧ b ∈ line 0))
    (h4 : ¬ (a ∈ line 4 ∧ b ∈ line 4))
    (h10 : ¬ (a ∈ line 10 ∧ b ∈ line 10))
    (h12 : ¬ (a ∈ line 12 ∧ b ∈ line 12)) :
    ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ line t ∧ b ∈ line t := by
  rintro ⟨t, ht, hab⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact h0 hab
  · exact h4 hab
  · exact h10 hab
  · exact h12 hab

def negA (i : P) : P :=
  match i.1 with
  | 0 => 2
  | 1 => 3
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 2
  | 6 => 1
  | 7 => 1
  | 8 => 1
  | 9 => 1
  | 10 => 1
  | 11 => 2
  | 12 => 1
  | _ => 0

def negB (i : P) : P :=
  match i.1 with
  | 0 => 4
  | 1 => 5
  | 2 => 4
  | 3 => 2
  | 4 => 2
  | 5 => 3
  | 6 => 4
  | 7 => 2
  | 8 => 2
  | 9 => 2
  | 10 => 2
  | 11 => 3
  | 12 => 4
  | _ => 0

set_option maxHeartbeats 2000000 in
lemma neg_flags : ∀ i : P,
    negA i ≠ 0 ∧ negB i ≠ 0 ∧
    ¬ (negA i ∈ line 0 ∧ negB i ∈ line 0) ∧
    ¬ (negA i ∈ line 4 ∧ negB i ∈ line 4) ∧
    ¬ (negA i ∈ line 10 ∧ negB i ∈ line 10) ∧
    ¬ (negA i ∈ line 12 ∧ negB i ∈ line 12) ∧
    neg (line i) (negA i) = true ∧ neg (line i) (negB i) = true := by decide

lemma neg_dom : ∀ i : P, domain (neg (line i)) := by
  intro i
  have h := neg_flags i
  refine ⟨negA i, negB i, ?_⟩
  exact And.intro
    (And.intro h.1 (And.intro h.2.1 (not_together _ _ h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1)))
    (And.intro h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2)

def testA (i p : P) : P :=
  match i.1, p.1 with
  | 0, 1 => 1
  | 0, 3 => 3
  | 0, 9 => 9
  | 1, 1 => 1
  | 1, 2 => 2
  | 1, 4 => 4
  | 1, 10 => 10
  | 2, 2 => 1
  | 2, 3 => 3
  | 2, 5 => 1
  | 2, 11 => 1
  | 3, 3 => 3
  | 3, 4 => 1
  | 3, 6 => 5
  | 3, 12 => 5
  | 4, 0 => 9
  | 4, 4 => 4
  | 4, 5 => 5
  | 4, 7 => 7
  | 5, 1 => 1
  | 5, 5 => 5
  | 5, 6 => 6
  | 5, 8 => 7
  | 6, 2 => 2
  | 6, 6 => 3
  | 6, 7 => 3
  | 6, 9 => 9
  | 7, 3 => 3
  | 7, 7 => 7
  | 7, 8 => 4
  | 7, 10 => 4
  | 8, 4 => 2
  | 8, 8 => 3
  | 8, 9 => 2
  | 8, 11 => 2
  | 9, 5 => 5
  | 9, 9 => 8
  | 9, 10 => 8
  | 9, 12 => 6
  | 10, 0 => 1
  | 10, 6 => 4
  | 10, 10 => 8
  | 10, 11 => 4
  | 11, 1 => 1
  | 11, 7 => 7
  | 11, 11 => 9
  | 11, 12 => 9
  | 12, 0 => 3
  | 12, 2 => 2
  | 12, 8 => 3
  | 12, 12 => 7
  | _, _ => 0

def testB (i p : P) : P :=
  match i.1, p.1 with
  | 0, 1 => 10
  | 0, 3 => 10
  | 0, 9 => 10
  | 1, 1 => 12
  | 1, 2 => 5
  | 1, 4 => 12
  | 1, 10 => 12
  | 2, 2 => 2
  | 2, 3 => 10
  | 2, 5 => 5
  | 2, 11 => 11
  | 3, 3 => 5
  | 3, 4 => 4
  | 3, 6 => 6
  | 3, 12 => 12
  | 4, 0 => 11
  | 4, 4 => 9
  | 4, 5 => 9
  | 4, 7 => 9
  | 5, 1 => 7
  | 5, 5 => 9
  | 5, 6 => 7
  | 5, 8 => 8
  | 6, 2 => 3
  | 6, 6 => 6
  | 6, 7 => 7
  | 6, 9 => 10
  | 7, 3 => 4
  | 7, 7 => 11
  | 7, 8 => 8
  | 7, 10 => 10
  | 8, 4 => 4
  | 8, 8 => 8
  | 8, 9 => 9
  | 8, 11 => 11
  | 9, 5 => 8
  | 9, 9 => 9
  | 9, 10 => 10
  | 9, 12 => 12
  | 10, 0 => 4
  | 10, 6 => 6
  | 10, 10 => 10
  | 10, 11 => 11
  | 11, 1 => 8
  | 11, 7 => 9
  | 11, 11 => 11
  | 11, 12 => 12
  | 12, 0 => 6
  | 12, 2 => 3
  | 12, 8 => 8
  | 12, 12 => 12
  | _, _ => 0

set_option maxHeartbeats 2000000 in
lemma test_flags : ∀ i p : P, p ∈ targets i →
    testA i p ≠ 0 ∧ testB i p ≠ 0 ∧
    ¬ (testA i p ∈ line 0 ∧ testB i p ∈ line 0) ∧
    ¬ (testA i p ∈ line 4 ∧ testB i p ∈ line 4) ∧
    ¬ (testA i p ∈ line 10 ∧ testB i p ∈ line 10) ∧
    ¬ (testA i p ∈ line 12 ∧ testB i p ∈ line 12) ∧
    input (test i p) (testA i p) = true ∧ input (test i p) (testB i p) = true := by decide

lemma test_dom : ∀ i p : P, p ∈ targets i → domain (input (test i p)) := by
  intro i p hp
  have h := test_flags i p hp
  refine ⟨testA i p, testB i p, ?_⟩
  exact And.intro
    (And.intro h.1 (And.intro h.2.1 (not_together _ _ h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1)))
    (And.intro h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2)

def spreadA (i p : P) : P :=
  match i.1, p.1 with
  | 0, 0 => 2
  | 0, 1 => 1
  | 0, 3 => 2
  | 0, 9 => 2
  | 1, 1 => 1
  | 1, 2 => 2
  | 1, 4 => 3
  | 1, 10 => 3
  | 2, 2 => 1
  | 2, 3 => 1
  | 2, 5 => 1
  | 2, 11 => 1
  | 3, 3 => 1
  | 3, 4 => 1
  | 3, 6 => 1
  | 3, 12 => 1
  | 4, 0 => 1
  | 4, 4 => 1
  | 4, 5 => 1
  | 4, 7 => 1
  | 5, 1 => 1
  | 5, 5 => 2
  | 5, 6 => 2
  | 5, 8 => 2
  | 6, 2 => 1
  | 6, 6 => 1
  | 6, 7 => 1
  | 6, 9 => 1
  | 7, 3 => 1
  | 7, 7 => 1
  | 7, 8 => 1
  | 7, 10 => 1
  | 8, 4 => 1
  | 8, 8 => 1
  | 8, 9 => 1
  | 8, 11 => 1
  | 9, 5 => 1
  | 9, 9 => 1
  | 9, 10 => 1
  | 9, 12 => 1
  | 10, 0 => 1
  | 10, 6 => 1
  | 10, 10 => 1
  | 10, 11 => 1
  | 11, 1 => 1
  | 11, 7 => 2
  | 11, 11 => 2
  | 11, 12 => 2
  | 12, 0 => 1
  | 12, 2 => 1
  | 12, 8 => 1
  | 12, 12 => 1
  | _, _ => 0

def spreadB (i p : P) : P :=
  match i.1, p.1 with
  | 0, 0 => 4
  | 0, 1 => 2
  | 0, 3 => 3
  | 0, 9 => 4
  | 1, 1 => 5
  | 1, 2 => 3
  | 1, 4 => 4
  | 1, 10 => 5
  | 2, 2 => 2
  | 2, 3 => 4
  | 2, 5 => 4
  | 2, 11 => 4
  | 3, 3 => 2
  | 3, 4 => 2
  | 3, 6 => 2
  | 3, 12 => 2
  | 4, 0 => 2
  | 4, 4 => 2
  | 4, 5 => 2
  | 4, 7 => 2
  | 5, 1 => 2
  | 5, 5 => 3
  | 5, 6 => 3
  | 5, 8 => 3
  | 6, 2 => 2
  | 6, 6 => 4
  | 6, 7 => 4
  | 6, 9 => 4
  | 7, 3 => 2
  | 7, 7 => 2
  | 7, 8 => 2
  | 7, 10 => 2
  | 8, 4 => 2
  | 8, 8 => 2
  | 8, 9 => 2
  | 8, 11 => 2
  | 9, 5 => 2
  | 9, 9 => 2
  | 9, 10 => 2
  | 9, 12 => 2
  | 10, 0 => 2
  | 10, 6 => 2
  | 10, 10 => 2
  | 10, 11 => 2
  | 11, 1 => 2
  | 11, 7 => 3
  | 11, 11 => 3
  | 11, 12 => 3
  | 12, 0 => 4
  | 12, 2 => 2
  | 12, 8 => 4
  | 12, 12 => 4
  | _, _ => 0

def spread (i p : P) (v : P) : Bool := neg (line i) v || input ({p} : Finset P) v

set_option maxHeartbeats 2000000 in
lemma spread_flags : ∀ i p : P, p ∈ line i →
    spreadA i p ≠ 0 ∧ spreadB i p ≠ 0 ∧
    ¬ (spreadA i p ∈ line 0 ∧ spreadB i p ∈ line 0) ∧
    ¬ (spreadA i p ∈ line 4 ∧ spreadB i p ∈ line 4) ∧
    ¬ (spreadA i p ∈ line 10 ∧ spreadB i p ∈ line 10) ∧
    ¬ (spreadA i p ∈ line 12 ∧ spreadB i p ∈ line 12) ∧
    spread i p (spreadA i p) = true ∧ spread i p (spreadB i p) = true := by decide

lemma spread_dom : ∀ i p : P, p ∈ line i → domain (spread i p) := by
  intro i p hp
  have h := spread_flags i p hp
  refine ⟨spreadA i p, spreadB i p, ?_⟩
  exact And.intro
    (And.intro h.1 (And.intro h.2.1 (not_together _ _ h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1)))
    (And.intro h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2)

lemma main_bound (C : Circuit) (o : P → ℕ) (valid : Good C)
    (correct : ∀ (i : P) (x : P → Bool), domain x →
      value C x (o i) = decide (∃ v ∈ line i, x v = true)) :
    39 ≤ C.size := by
  classical
  have low (i : P) : value C (neg (line i)) (o i) = false := by
    have dom : domain (neg (line i)) := neg_dom i
    rw [correct i _ dom]
    apply decide_eq_false
    rintro ⟨v, vin, h⟩
    exact (of_decide_eq_true h) vin
  have pos (i p : P) (hp : p ∈ targets i) : value C (input (test i p)) (o i) = true := by
    have dom : domain (input (test i p)) := test_dom i p hp
    rw [correct i _ dom]
    have both : p ∈ test i p ∩ line i := by rw [test_sep i p hp]; simp
    exact decide_eq_true ⟨p, target_sub i hp, decide_eq_true (Finset.mem_inter.mp both).1⟩
  have partialCount := collect C valid line targets test o target_sub geoThin test_sep apart_ok low pos
  rw [partial_sum] at partialCount
  by_contra! short
  have total : (Finset.Ico 13 (13 + C.size)).card = C.size := by simp
  have sub : orWires C ⊆ Finset.Ico 13 (13 + C.size) := Finset.filter_subset _ _
  have allGates : orWires C = Finset.Ico 13 (13 + C.size) :=
    Finset.eq_of_subset_of_card_le sub (by omega)
  have onlyOr : ∀ g ∈ C.gates, g.op = GateOp.or := by
    intro g hg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    have w : 13 + k ∈ orWires C := by
      rw [allGates]
      exact Finset.mem_Ico.mpr ⟨by omega, by unfold Circuit.size; omega⟩
    obtain ⟨j, hj, hop⟩ := (Finset.mem_filter.mp w).2
    have idx : j = (⟨k, hk⟩ : Fin C.gates.length) := by
      apply Fin.ext
      change j.val = k
      omega
    subst j
    exact hop
  let single (_ p : P) : Finset P := {p}
  have posSingle (i p : P) (hp : p ∈ line i) : value C (input (single i p)) (o i) = true := by
    let x := neg (line i)
    let y := input (single i p)
    have eqz : spread i p = fun v => x v || y v := by
      funext v
      simp [spread, x, y, single]
    have dom : domain (fun v => x v || y v) := by
      rw [← eqz]
      exact spread_dom i p hp
    have yes : value C (fun v => x v || y v) (o i) = true := by
      rw [correct i _ dom]
      exact decide_eq_true ⟨p, hp, by simp [y, single, input]⟩
    exact (or_split C onlyOr x y _ yes).resolve_left
      (fun h => Bool.false_ne_true ((low i).symm.trans h))
  have apart (i j : P) (_ : i ≠ j) :
      ¬ (clash line line single i j ∧ clash line line single j i) := by
    rintro ⟨⟨p, _, pj, v, hv⟩, _⟩
    obtain ⟨inS, vj⟩ := Finset.mem_inter.mp hv
    have eq : v = p := Finset.mem_singleton.mp inS
    exact pj (eq ▸ vj)
  have fullCount := collect C valid line line single o (fun _ => Finset.Subset.rfl) geoThin
    (fun i p hp => by simp [single, hp]) apart low posSingle
  rw [full_sum, allGates, total] at fullCount
  omega

end PEqualNP.Outside.L_meta_1558

open PEqualNP.Outside.L_meta_1558

theorem PEqualNP.Outside.L_meta_1558 : ∀ L : Fin 13 → Finset (Fin 13), (∀ t : Fin 13, L t = {t, t + 1, t + 3, t + 9}) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin 13 → ℕ),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ (t : Fin 13) (x : Fin 13 → Bool), (∃ a b : Fin 13, (a ≠ 0 ∧ b ≠ 0 ∧ ¬ ∃ t ∈ ({0, 4, 10, 12} : Finset (Fin 13)), a ∈ L t ∧ b ∈ L t) ∧ x a = true ∧ x b = true) →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    39 ≤ gates.length := by
  intro L hL gates o good correct
  have eq : L = line := funext hL
  subst L
  exact main_bound ⟨gates, 0⟩ o good correct
