import Mathlib
import PEqualNP.Defs

/- The circuit counting lemma is reproduced from the merged L-meta-1461.
The independent choice of a point outside each line is reproduced from the
merged L-meta-1467. We apply the former with the two-point tests consisting
of a point on a line and its chosen exterior point. -/

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1468.CircuitCount

-- The circuit evaluation and cut argument are adapted from L-meta-270,
-- originally proved by k-sandhu in PR 149.

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

private abbrev Valid (C : Circuit) :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

private abbrev Cold {n : ℕ} (C : Circuit) (mark : ℕ) (x : Fin n → Bool) :=
  value C x mark = false

/-- On rows where the marked wire is low, that predecessor can be removed
from each monotonicity comparison. A gate reading it has at most one remaining predecessor. -/
private lemma parents {n : ℕ} (C : Circuit) (valid : Valid C) (j : Fin C.size)
    (unique : ∀ i : Fin C.size, (C.gates.get i).op = GateOp.not → i = j)
    (w : ℕ) (hn : n ≤ w) (hw : w < n+C.size) :
    let i : Fin C.size := ⟨w-n,by omega⟩
    ∃ P : Finset ℕ, P.card ≤ 2 ∧
      (n+j.val ∈ (C.gates.get i).inputs → P.card ≤ 1) ∧ (∀ r ∈ P, r<w) ∧
      ∀ x y : Fin n → Bool, Cold C (n+j.val) x → Cold C (n+j.val) y →
        (∀ r ∈ P, value C x r=true → value C y r=true) →
        value C x w=true → value C y w=true := by
  let i : Fin C.size := ⟨w-n,by omega⟩
  let g := C.gates.get i
  obtain ⟨hop,hlen⟩ := valid g (List.get_mem ..)
  let mark := n+j.val
  let P := (g.inputs.toFinset.erase mark).filter (· < w)
  have bound := (Finset.card_filter_le (g.inputs.toFinset.erase mark) (· < w))
  have max := List.toFinset_card_le g.inputs |>.trans hlen
  refine ⟨P,bound.trans ((Finset.card_le_card (Finset.erase_subset ..)).trans max),?_,?_,?_⟩
  · intro read
    have h : mark ∈ g.inputs.toFinset := List.mem_toFinset.mpr read
    have e := Finset.card_erase_add_one h
    change P.card ≤ 1
    change P.card ≤ _ at bound
    omega
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y cx cy step hx
    rcases hop with hop|hop|hop
    all_goals try
      have same : w = n+j.val := by
        have e := congrArg Fin.val (unique i hop)
        change w-n=j.val at e
        omega
      rw [same] at hx
      exact (Bool.false_ne_true (cx.symm.trans hx)).elim
    all_goals
      have hr (r : ℕ) (hin : r ∈ g.inputs) :
          (if r < w then value C x r else false)=true →
          (if r < w then value C y r else false)=true := by
        by_cases lt : r < w
        · by_cases eq : r = mark
          · subst r; simp [lt,mark,cx]
          · simpa only [ite_eq_left lt] using step r
              (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨eq,List.mem_toFinset.mpr hin⟩,lt⟩)
        · simp [lt]
      have gx := gate_value C x w hn hw
      have gy := gate_value C y w hn hw
      change value C x w = g.op.eval _ at gx
      change value C y w = g.op.eval _ at gy
      rw [gx] at hx
      rw [gy]
    · simp only [hop,GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq] at hx ⊢
      exact fun z hz => hr z hz (hx z hz)
    · simp only [hop,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq] at hx ⊢
      obtain ⟨z,hz,yes⟩ := hx
      exact ⟨z,hz,hr z hz yes⟩

private lemma mono {n : ℕ} (C : Circuit) (valid : Valid C) (j : Fin C.size)
    (unique : ∀ i : Fin C.size, (C.gates.get i).op = GateOp.not → i=j)
    (x y : Fin n → Bool) (cx : Cold C (n+j.val) x) (cy : Cold C (n+j.val) y)
    (le : ∀ p, x p=true → y p=true) (w : ℕ) : value C x w=true → value C y w=true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases small : w<n
    · let p : Fin n := ⟨w,small⟩
      change value C x p=true → value C y p=true
      simpa only [input_value] using le p
    by_cases end' : w<n+C.size
    · obtain ⟨P,_,_,lt,step⟩ := parents C valid j unique w (by omega) end'
      exact step x y cx cy fun r hr => ih r (lt r hr)
    · simp [missing_value C x w (by omega)]

-- Reverse expansion with a separate charge set. A free expansion replaces
-- one wire by at most one predecessor, leaving the size of the boundary unchanged.
private lemma cut {n : ℕ} (C : Circuit) (mark : ℕ) (G paid : Finset ℕ)
    (parents : ∀ w ∈ G, ∃ P : Finset ℕ, P.card ≤ 2 ∧ (w ∉ paid → P.card ≤ 1) ∧
      (∀ r ∈ P, r<w) ∧ ∀ x y : Fin n → Bool, Cold C mark x → Cold C mark y →
        (∀ r ∈ P, value C x r=true → value C y r=true) → value C x w=true → value C y w=true)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G → w < t) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ F.card + ((G ∩ paid).filter (· < t)).card ∧
      ∀ x y : Fin n → Bool, Cold C mark x → Cold C mark y →
        (∀ w ∈ B, value C x w=true → value C y w=true) →
        ∀ w ∈ F, value C x w=true → value C y w=true := by
  induction t generalizing F with
  | zero =>
    exact ⟨F,Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega),
      Nat.le_add_right ..,fun _ _ _ _ h => h⟩
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
      · intro x y cx cy hxy w hw
        by_cases eq : w=t
        · subst w
          exact step x y cx cy fun r hr => chains x y cx cy hxy r (Finset.mem_union_right _ hr)
        · exact chains x y cx cy hxy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hw⟩))
    · have smaller : ∀ w ∈ F, w ∈ G → w<t := by
        intro w hw hg
        have ne : w≠t := fun e => expand ⟨e ▸ hw,e ▸ hg⟩
        have := hF w hw hg
        omega
      obtain ⟨B,dis,size,chains⟩ := ih F smaller
      exact ⟨B,dis,by omega,chains⟩

/-- Monotonicity between two ordered inputs on which the distinguished wire is false. -/
theorem row_mono {n : ℕ} (gs : List Gate) (j : Fin gs.length)
    (valid : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (unique : ∀ i : Fin gs.length, (gs.get i).op = GateOp.not → i=j)
    (x y : Fin n → Bool)
    (cx : (Circuit.mk gs (n+j.val)).eval (List.ofFn x)=false)
    (cy : (Circuit.mk gs (n+j.val)).eval (List.ofFn y)=false)
    (le : ∀ v, x v=true → y v=true) (w : ℕ) :
    (Circuit.mk gs w).eval (List.ofFn x)=true → (Circuit.mk gs w).eval (List.ofFn y)=true :=
  mono ⟨gs,w⟩ valid j unique x y cx cy le w

/-- On a separated family of positive rows, every output forces one fewer
distinct branching gate than the number of rows. Direct readers of the marked
wire participate in the reverse expansion without incurring a charge. -/
theorem row {n : ℕ} (gs : List Gate) (j : Fin gs.length)
    (valid : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (unique : ∀ i : Fin gs.length, (gs.get i).op = GateOp.not → i=j)
    (T : Finset (Fin n)) (R : Fin n → Finset (Fin n)) (o : ℕ)
    (sep : ∀ p ∈ T, R p ∩ T = {p})
    (cneg : (Circuit.mk gs (n+j.val)).eval (List.ofFn (fun v => decide (v ∉ T))) = false)
    (cpos : ∀ p ∈ T, (Circuit.mk gs (n+j.val)).eval (List.ofFn (fun v => decide (v ∈ R p))) = false)
    (hneg : (Circuit.mk gs o).eval (List.ofFn (fun v => decide (v ∉ T))) = false)
    (hpos : ∀ p ∈ T, (Circuit.mk gs o).eval (List.ofFn (fun v => decide (v ∈ R p))) = true) :
    ∃ A : Finset (Fin gs.length), T.card - 1 ≤ A.card ∧ ∀ i ∈ A,
      ¬ (j < i ∧ n+j.val ∈ (gs.get i).inputs) ∧
      (Circuit.mk gs (n+i.val)).eval (List.ofFn (fun v => decide (v ∉ T)))=false ∧
      2 ≤ (T.filter (fun p => (Circuit.mk gs (n+i.val)).eval (List.ofFn (fun v => decide (v ∈ R p)))=true)).card := by
  classical
  let C : Circuit := ⟨gs,o⟩
  let neg (v : Fin n) := decide (v ∉ T)
  let pos (p v : Fin n) := decide (v ∈ R p)
  let hits (w : ℕ) := T.filter (fun p => value C (pos p) w=true)
  let clean (w : ℕ) := value C neg w=false ∧ 2 ≤ (hits w).card
  let G := (Finset.Ico n (n+gs.length)).filter clean
  let A := Finset.univ.filter (fun i : Fin gs.length =>
    ¬ (j < i ∧ n+j.val ∈ (gs.get i).inputs) ∧ clean (n+i.val))
  let paid := A.image (fun i => n+i.val)
  have isGate (w : ℕ) (c : clean w) : n ≤ w ∧ w < n+gs.length := by
    obtain ⟨zero,big⟩ := c
    constructor
    · by_contra! lt
      let a : Fin n := ⟨w,lt⟩
      have aa : a ∈ T := by
        change value C neg a=false at zero
        simpa [input_value,neg] using zero
      have sub : hits w ⊆ {a} := by
        intro p hp
        obtain ⟨hpt,hw⟩ := Finset.mem_filter.mp hp
        change value C (pos p) a=true at hw
        have yes : a ∈ R p := by simpa [input_value,pos] using hw
        have both : a ∈ R p ∩ T := Finset.mem_inter.mpr ⟨yes,aa⟩
        rw [sep p hpt,Finset.mem_singleton] at both
        simpa only [Finset.mem_singleton] using both.symm
      have bound := Finset.card_le_card sub
      simp only [Finset.card_singleton] at bound
      omega
    · by_contra! high
      have none : hits w=∅ := by
        ext p
        simp [hits,missing_value C (pos p) w high]
      simp [none] at big
  have step (w : ℕ) (hw : w ∈ G) : ∃ P : Finset ℕ, P.card ≤ 2 ∧ (w ∉ paid → P.card ≤ 1) ∧
      (∀ r ∈ P, r<w) ∧ ∀ x y : Fin n → Bool, Cold C (n+j.val) x → Cold C (n+j.val) y →
        (∀ r ∈ P, value C x r=true → value C y r=true) → value C x w=true → value C y w=true := by
    obtain ⟨bounds,c⟩ := Finset.mem_filter.mp hw
    obtain ⟨low,high⟩ := Finset.mem_Ico.mp bounds
    let i : Fin gs.length := ⟨w-n,by omega⟩
    have idx : n+i.val=w := by dsimp [i]; omega
    obtain ⟨P,size,read,less,chain⟩ := parents C valid j unique w low high
    refine ⟨P,size,?_,less,chain⟩
    intro free
    apply read
    by_contra no
    apply free
    apply Finset.mem_image.mpr
    refine ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩,idx⟩
    · exact fun e => no e.2
    · rw [idx]
      exact c
  obtain ⟨B,dis,size,chain⟩ := cut C (n+j.val) G paid step (n+gs.length) {o}
    (fun w _ hg => (Finset.mem_Ico.mp (Finset.mem_filter.mp hg).1).2)
  let parts (w : ℕ) := if value C neg w=false then hits w else ∅
  have small (w : ℕ) (hb : w ∈ B) : (parts w).card ≤ 1 := by
    by_cases zero : value C neg w=false
    · simp only [parts,ite_eq_left zero]
      by_contra! big
      have c : clean w := ⟨zero,by omega⟩
      exact Finset.disjoint_left.mp dis hb (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (isGate w c),c⟩)
    · simp [parts,zero]
  have cover : T ⊆ B.biUnion parts := by
    intro p hp
    by_contra no
    have implication (w : ℕ) (hb : w ∈ B) (yes : value C (pos p) w=true) : value C neg w=true := by
      cases zero : value C neg w with
      | true => rfl
      | false =>
        exfalso
        exact no (Finset.mem_biUnion.mpr ⟨w,hb,by simp [parts,zero,hits,hp,yes]⟩)
    have bad := chain (pos p) neg (cpos p hp) cneg implication o (Finset.mem_singleton_self o) (hpos p hp)
    exact Bool.false_ne_true (hneg.symm.trans bad)
  have bound := (Finset.card_le_card cover).trans (Finset.card_biUnion_le_card_mul B parts 1 small)
  have use := (Finset.card_filter_le (G ∩ paid) (· < n+gs.length)).trans
    ((Finset.card_le_card (Finset.inter_subset_right (s₁:=G) (s₂:=paid))).trans (Finset.card_image_le))
  simp only [Finset.card_singleton] at size
  simp only [mul_one] at bound
  exact ⟨A,by omega,fun _ hi => (Finset.mem_filter.mp hi).2⟩

/-- The effective input of the NOT is a genuine earlier gate which fires on every
complement. This conclusion also handles empty, malformed and forward input lists. -/
theorem notInputSpare {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hm : 1 ≤ m) (cover : ∀ v : Fin n, ∃ i : Fin m, v ∈ S i)
    (gates : List Gate) (j : Fin gates.length) (op : (gates.get j).op=.not)
    (low : ∀ i : Fin m, (Circuit.mk gates (n+j.val)).eval
      (List.ofFn (fun v : Fin n => decide (v ∉ S i)))=false) :
    ∃ h : Fin gates.length, h < j ∧ ∀ i : Fin m, (Circuit.mk gates (n+h.val)).eval
      (List.ofFn (fun v : Fin n => decide (v ∉ S i)))=true := by
  let C : Circuit := ⟨gates,0⟩
  let x := fun (i : Fin m) (v : Fin n) => decide (v ∉ S i)
  have low' (i : Fin m) : value C (x i) (n+j.val) = false := low i
  have equation (i : Fin m) :
      value C (x i) (n+j.val) =
        !(((gates.get j).inputs.map fun r => if r<n+j.val then value C (x i) r else false).headD false) := by
    have h := gate_value C (x i) (n+j.val) (by omega)
        (by change n+j.val < n+gates.length; omega)
    change value C (x i) (n+j.val) = _ at h
    simpa [C,Nat.add_sub_cancel_left,← List.get_eq_getElem,op,GateOp.eval] using h
  let i0 : Fin m := ⟨0,by omega⟩
  cases args : (gates.get j).inputs with
  | nil =>
    have eq := equation i0
    rw [args,low'] at eq
    contradiction
  | cons w ws =>
    have live (i : Fin m) : (if w < n+j.val then value C (x i) w else false) = true := by
      have eq := equation i
      rw [args,low'] at eq
      simpa using eq.symm
    have before : w < n+j.val := by
      by_contra bad
      simpa [bad] using live i0
    have hit (i : Fin m) : value C (x i) w=true := by simpa [before] using live i
    have gate : n≤w := by
      by_contra! pri
      let v : Fin n := ⟨w,pri⟩
      obtain ⟨i,inside⟩ := cover v
      have yh := hit i
      change value C (x i) v.val=true at yh
      rw [input_value] at yh
      exact (of_decide_eq_true yh) inside
    let h : Fin gates.length := ⟨w-n,by have := j.isLt; omega⟩
    have idx : n+h.val=w := by dsimp [h]; omega
    refine ⟨h,?_,?_⟩
    · change w-n < j.val
      omega
    · intro i
      change value C (x i) (n+h.val)=true
      rw [idx]; exact hit i

/-- Accounting for the NOT, its effective input and all its later direct readers. -/
theorem paid_card {n : ℕ} (gates : List Gate) (j h : Fin gates.length) (earlier : h < j)
    (paid : Finset (Fin gates.length)) (hj : j ∉ paid) (hh : h ∉ paid)
    (noReader : ∀ i ∈ paid, j < i → n+j.val ∉ (gates.get i).inputs) :
    paid.card + (Finset.univ.filter (fun i : Fin gates.length =>
      j < i ∧ n+j.val ∈ (gates.get i).inputs)).card + 2 ≤ gates.length := by
  classical
  let rs := Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n+j.val∈(gates.get i).inputs)
  have dis : Disjoint paid rs := Finset.disjoint_left.mpr fun i hi hr =>
    noReader i hi (Finset.mem_filter.mp hr).2.1 (Finset.mem_filter.mp hr).2.2
  have outJ : j ∉ paid∪rs := by
    simp [rs,hj]
  have outH : h ∉ insert j (paid∪rs) := by
    simp [rs,hh,earlier.ne,not_lt_of_gt earlier]
  have cap := Finset.card_le_univ (insert h (insert j (paid∪rs)))
  rw [Finset.card_insert_of_notMem outH,Finset.card_insert_of_notMem outJ,
    Finset.card_union_of_disjoint dis,Fintype.card_fin] at cap
  change paid.card+rs.card+2 ≤ gates.length
  omega

theorem outsideWitness1461 {n : ℕ} {A B T : Finset (Fin n)}
    (thin : (A ∩ B).card ≤ 1) (sub : T ⊆ A) (many : 2 ≤ T.card) :
    ∃ p ∈ T, p ∉ B := by
  by_contra! inside
  have hsub : T ⊆ A ∩ B := fun p hp => Finset.mem_inter.mpr ⟨sub hp, inside p hp⟩
  have bound := Finset.card_le_card hsub
  omega

/-- A gate counted by two rows forces one selected test from each row to
intersect the other row outside their shared point. -/
theorem disjointPayments1461 {n m k : ℕ} (S : Fin m → Finset (Fin n))
    (R : Fin m → Fin n → Finset (Fin n)) (pay : Fin m → Finset (Fin k))
    (on : Fin k → Fin m → Fin n → Prop)
    (thin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (separated : ∀ i j, i ≠ j → ¬ ((∃ p ∈ S i \ S j, (R i p ∩ S j).Nonempty) ∧
      (∃ p ∈ S j \ S i, (R j p ∩ S i).Nonempty)))
    (wide : ∀ i t, t ∈ pay i → ∃ T : Finset (Fin n), T ⊆ S i ∧ 2 ≤ T.card ∧
      ∀ p ∈ T, on t i p)
    (cross : ∀ i p j t, p ∈ S i → on t i p → t ∈ pay j → (R i p ∩ S j).Nonempty) :
    ∀ i j, i ≠ j → Disjoint (pay i) (pay j) := by
  classical
  have witness {i j : Fin m} {t : Fin k} (diff : i ≠ j) (hi : t ∈ pay i) (hj : t ∈ pay j) :
      ∃ p ∈ S i \ S j, (R i p ∩ S j).Nonempty := by
    obtain ⟨T, ts, two, high⟩ := wide i t hi
    obtain ⟨p, pt, pb⟩ := outsideWitness1461 (thin i j diff) ts two
    exact ⟨p, Finset.mem_sdiff.mpr ⟨ts pt,pb⟩, cross i p j t (ts pt) (high p pt) hj⟩
  intro i j diff
  rw [Finset.disjoint_left]
  intro t hi hj
  exact separated i j diff ⟨witness diff hi hj, witness diff.symm hj hi⟩

theorem chargeUnion1461 {m k q : ℕ} (pay : Fin m → Finset (Fin k))
    (many : ∀ i, q ≤ (pay i).card)
    (disjoint : ∀ i j, i ≠ j → Disjoint (pay i) (pay j)) :
    m*q ≤ (Finset.univ.biUnion pay).card := by
  rw [Finset.card_biUnion (fun i _ j _ hij => disjoint i j hij)]
  simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => many i)

end PEqualNP.Outside.L_meta_1468.CircuitCount

open PEqualNP.Outside.L_meta_1468.CircuitCount

namespace PEqualNP.Outside.L_meta_1468.CircuitCount
theorem main : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n))
    (R : Fin m → Fin n → Finset (Fin n)),
    1 ≤ q → 1 ≤ m → (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ v : Fin n, ∃ i : Fin m, v ∈ S i) →
    (∀ (i : Fin m) (p : Fin n), p ∈ S i → R i p ∩ S i = {p}) →
    (∀ i j : Fin m, i ≠ j → ¬ ((∃ p ∈ S i \ S j, (R i p ∩ S j).Nonempty) ∧
      (∃ s ∈ S j \ S i, (R j s ∩ S i).Nonempty))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) →
    (∀ i : Fin m, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∉ S i))) = false) →
    (∀ (i : Fin m) (p : Fin n), p ∈ S i →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v ∈ R i p))) = false) →
    m * q + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length := by
  classical
  intro q n m S R _hq hm sz thin cover sep separated gates out j valid op unique computes low cold
  let yes (i : Fin m) (p v : Fin n) := decide (v ∈ R i p)
  let no (i : Fin m) (v : Fin n) := decide (v ∉ S i)
  have oneg (i : Fin m) : (Circuit.mk gates (out i)).eval (List.ofFn (no i)) = false := by
    rw [computes]
    apply decide_eq_false
    rintro ⟨v, hv, hy⟩
    exact (of_decide_eq_true hy) hv
  have opos (i : Fin m) (p : Fin n) (hp : p ∈ S i) :
      (Circuit.mk gates (out i)).eval (List.ofFn (yes i p)) = true := by
    have both : p ∈ R i p ∩ S i := by rw [sep i p hp]; simp
    rw [computes]
    exact decide_eq_true ⟨p, hp, decide_eq_true (Finset.mem_inter.mp both).1⟩
  have found (i : Fin m) := row gates j valid unique (S i) (R i) (out i)
    (sep i) (low i) (cold i) (oneg i) (opos i)
  choose pay many props using found
  let on (t : Fin gates.length) (i : Fin m) (p : Fin n) : Prop :=
    (Circuit.mk gates (n+t.val)).eval (List.ofFn (yes i p)) = true
  have wide (i : Fin m) (t : Fin gates.length) (ht : t ∈ pay i) :
      ∃ T : Finset (Fin n), T ⊆ S i ∧ 2 ≤ T.card ∧ ∀ p ∈ T, on t i p :=
    ⟨(S i).filter (on t i), Finset.filter_subset _ _, (props i t ht).2.2,
      fun _ hp => (Finset.mem_filter.mp hp).2⟩
  have cross (i : Fin m) (p : Fin n) (z : Fin m) (t : Fin gates.length)
      (hp : p ∈ S i) (hit : on t i p) (ht : t ∈ pay z) : (R i p ∩ S z).Nonempty := by
    by_contra hn
    have le (v : Fin n) (hv : yes i p v = true) : no z v = true := by
      apply decide_eq_true
      intro hz
      exact hn ⟨v, Finset.mem_inter.mpr ⟨of_decide_eq_true hv, hz⟩⟩
    have hi := row_mono gates j valid unique (yes i p) (no z) (cold i p hp)
      (low z) le (n+t.val) hit
    have lo : (Circuit.mk gates (n+t.val)).eval (List.ofFn (no z)) = false := (props z t ht).2.1
    rw [lo] at hi
    contradiction
  let paid := Finset.univ.biUnion pay
  have charge : m*q ≤ paid.card := chargeUnion1461 pay (fun i => by
    have h := many i
    rw [sz i] at h
    omega) (disjointPayments1461 S R pay on thin separated wide cross)
  obtain ⟨h, earlier, high⟩ := notInputSpare S hm cover gates j op low
  have noJ : j ∉ paid := by
    intro hj
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨T, sub, two, onRows⟩ := wide i j hi
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
    have pos : (Circuit.mk gates (n+j.val)).eval (List.ofFn (yes i p)) = true := onRows p hp
    have neg : (Circuit.mk gates (n+j.val)).eval (List.ofFn (yes i p)) = false := cold i p (sub hp)
    rw [neg] at pos
    contradiction
  have noH : h ∉ paid := by
    intro hh
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hh
    have lo := (props i h hi).2.1
    rw [high i] at lo
    contradiction
  have noReader (t : Fin gates.length) (ht : t ∈ paid) (jt : j < t) :
      n+j.val ∉ (gates.get t).inputs := by
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ht
    exact fun hn => (props i t hi).1 ⟨jt, hn⟩
  have cap := paid_card gates j h earlier paid noJ noH noReader
  omega
end PEqualNP.Outside.L_meta_1468.CircuitCount

namespace PEqualNP.Outside.L_meta_1468.PlaneChoice

theorem modlem (N a : ℕ) (h : a < 2 * N) : a % N = if a < N then a else a - N := by
  split_ifs with h1
  · exact Nat.mod_eq_of_lt h1
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The next residue. -/
def s {N : ℕ} (hN : 0 < N) (z : Fin N) : Fin N := ⟨(z.val + 1) % N, Nat.mod_lt _ hN⟩

/-- The previous residue. -/
def r {N : ℕ} (hN : 0 < N) (z : Fin N) : Fin N :=
  if z.val = 0 then ⟨N - 1, by omega⟩ else ⟨z.val - 1, by have := z.isLt; omega⟩

theorem sval {N : ℕ} (hN : 0 < N) (z : Fin N) :
    (s hN z).val = if z.val + 1 < N then z.val + 1 else 0 := by
  have hz := z.isLt
  simp only [s]
  rw [modlem N _ (by omega)]
  split_ifs <;> omega

theorem rval {N : ℕ} (hN : 0 < N) (z : Fin N) :
    (r hN z).val = if z.val = 0 then N - 1 else z.val - 1 := by
  simp only [r]
  split_ifs <;> rfl

theorem rs {N : ℕ} (hN : 0 < N) (z : Fin N) : r hN (s hN z) = z := by
  have hz := z.isLt
  apply Fin.ext
  rw [rval, sval]
  have hN1 : N - 1 + 1 = N := Nat.sub_add_cancel hN
  split_ifs with h1 h2 h2
  all_goals first | omega | contradiction

theorem s_ne {N : ℕ} (hN : 0 < N) (h3 : 3 ≤ N) (z : Fin N) : s hN z ≠ z := by
  intro h
  have hz := z.isLt
  have := congrArg Fin.val h
  rw [sval] at this
  split_ifs at this <;> omega

theorem ss_ne {N : ℕ} (hN : 0 < N) (h3 : 3 ≤ N) (z : Fin N) : s hN (s hN z) ≠ z := by
  intro h
  have hz := z.isLt
  have := congrArg Fin.val h
  rw [sval, sval] at this
  split_ifs at this <;> omega

theorem r_ne {N : ℕ} (hN : 0 < N) (h3 : 3 ≤ N) (z : Fin N) : r hN z ≠ z := by
  intro h
  have hz := z.isLt
  have := congrArg Fin.val h
  rw [rval] at this
  split_ifs at this <;> omega

theorem rr_ne {N : ℕ} (hN : 0 < N) (h3 : 3 ≤ N) (z : Fin N) : r hN (r hN z) ≠ z := by
  intro h
  have hz := z.isLt
  have := congrArg Fin.val h
  rw [rval, rval] at this
  split_ifs at this <;> omega

end PEqualNP.Outside.L_meta_1468.PlaneChoice

namespace PEqualNP.Outside.L_meta_1468.PlaneChoice
theorem main : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n)),
    2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) →
    (∀ u v : Fin n, u ≠ v → ∃ i : Fin m, u ∈ S i ∧ v ∈ S i) →
    (∃ (i : Fin m) (v : Fin n), v ∉ S i) →
    ∃ b : Fin m → Fin n, (∀ i : Fin m, b i ∉ S i) ∧
      ∀ i j : Fin m, i ≠ j → ¬ (b i ∈ S j ∧ b j ∈ S i) := by
  classical
  intro q n m S hq hcard hmeet hline hoff
  obtain ⟨i0, O, hO⟩ := hoff
  have hN : 0 < q + 1 := by omega
  have h3 : 3 ≤ q + 1 := by omega
  let e : S i0 ≃ Fin (q + 1) := Finset.equivFinOfCardEq (hcard i0)
  let pt : Fin (q + 1) → Fin n := fun z => ((e.symm z : S i0) : Fin n)
  have hpt0 : ∀ z, pt z ∈ S i0 := fun z => (e.symm z).2
  have hptinj : ∀ z z', pt z = pt z' → z = z' := fun z z' h => e.symm.injective (Subtype.ext h)
  have hptsurj : ∀ p ∈ S i0, ∃ z, pt z = p := fun p hp => ⟨e ⟨p, hp⟩, by simp [pt]⟩
  have huniq : ∀ i j : Fin m, ∀ u v : Fin n, u ≠ v → u ∈ S i → v ∈ S i → u ∈ S j → v ∈ S j →
      i = j := by
    intro i j u v huv hui hvi huj hvj
    by_contra hij
    have h1 := hmeet i j hij
    have hsub : ({u, v} : Finset (Fin n)) ⊆ S i ∩ S j := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [*]
    have := Finset.card_le_card hsub
    rw [Finset.card_pair huv, h1] at this
    omega
  have hD : ∀ i : Fin m, i ≠ i0 → ∃ z : Fin (q + 1), pt z ∈ S i ∧ ∀ z', pt z' ∈ S i → z' = z := by
    intro i hi
    obtain ⟨p, hp⟩ := Finset.card_eq_one.1 (hmeet i i0 hi)
    have hpm : p ∈ S i ∩ S i0 := by rw [hp]; simp
    obtain ⟨hpi, hp0⟩ := Finset.mem_inter.1 hpm
    obtain ⟨z, rfl⟩ := hptsurj p hp0
    refine ⟨z, hpi, fun z' hz' => hptinj _ _ ?_⟩
    have : pt z' ∈ S i ∩ S i0 := Finset.mem_inter.2 ⟨hz', hpt0 z'⟩
    rw [hp] at this
    simpa using this
  let D : Fin m → Fin (q + 1) := fun i => if h : i ≠ i0 then (hD i h).choose else ⟨0, hN⟩
  have hD1 : ∀ i, i ≠ i0 → pt (D i) ∈ S i := by
    intro i hi
    have : D i = (hD i hi).choose := by simp only [D]; rw [dif_pos hi]
    rw [this]; exact (hD i hi).choose_spec.1
  have hD2 : ∀ i, i ≠ i0 → ∀ z', pt z' ∈ S i → z' = D i := by
    intro i hi z' hz'
    have : D i = (hD i hi).choose := by simp only [D]; rw [dif_pos hi]
    rw [this]; exact (hD i hi).choose_spec.2 z' hz'
  have hK : ∀ z : Fin (q + 1), ∃ k : Fin m, O ∈ S k ∧ pt z ∈ S k := fun z =>
    hline O (pt z) (fun h => hO (h ▸ hpt0 z))
  choose K hKO hKz using hK
  have hKne : ∀ z, K z ≠ i0 := fun z h => hO (h ▸ hKO z)
  have hDK : ∀ z, D (K z) = z := fun z => (hD2 (K z) (hKne z) z (hKz z)).symm
  have hQ : ∀ z, ∃ x, x ∈ S (K z) ∧ x ≠ O ∧ x ∉ S i0 := by
    intro z
    have hc : 1 ≤ (((S (K z)).erase O).erase (pt z)).card := by
      have h1 := Finset.pred_card_le_card_erase (s := S (K z)) (a := O)
      have h2 := Finset.pred_card_le_card_erase (s := (S (K z)).erase O) (a := pt z)
      rw [hcard] at h1
      omega
    obtain ⟨x, hx⟩ := Finset.card_pos.1 hc
    simp only [Finset.mem_erase] at hx
    refine ⟨x, hx.2.2, hx.2.1, fun hx0 => ?_⟩
    obtain ⟨z', rfl⟩ := hptsurj x hx0
    have := hD2 (K z) (hKne z) z' hx.2.2
    rw [hDK] at this
    exact hx.1 (by rw [this])
  choose Q hQK hQO hQ0 using hQ
  have hQline : ∀ z j, Q z ∈ S j → O ∈ S j → j = K z := fun z j hQj hOj =>
    huniq j (K z) O (Q z) (Ne.symm (hQO z)) hOj hQj (hKO z) (hQK z)
  have hQline2 : ∀ z j, Q z ∈ S j → pt z ∈ S j → j = K z := fun z j hQj hpj =>
    huniq j (K z) (Q z) (pt z) (fun h => hQ0 z (h ▸ hpt0 z)) hQj hpj (hQK z) (hKz z)
  let b : Fin m → Fin n := fun i =>
    if i = i0 then O else if O ∈ S i then Q (r hN (D i)) else pt (s hN (D i))
  have b0 : b i0 = O := by simp [b]
  have b1 : ∀ i, i ≠ i0 → O ∈ S i → b i = Q (r hN (D i)) := by
    intro i hi hOi; simp only [b]; rw [if_neg hi, if_pos hOi]
  have b2 : ∀ i, i ≠ i0 → O ∉ S i → b i = pt (s hN (D i)) := by
    intro i hi hOi; simp only [b]; rw [if_neg hi, if_neg hOi]
  refine ⟨b, ?_, ?_⟩
  · intro i
    by_cases h0 : i = i0
    · subst h0; rw [b0]; exact hO
    · by_cases hOi : O ∈ S i
      · rw [b1 i h0 hOi]
        intro hin
        have h2 := congrArg D (hQline _ i hin hOi)
        rw [hDK] at h2
        exact r_ne hN h3 (D i) h2.symm
      · rw [b2 i h0 hOi]
        intro hin
        exact s_ne hN h3 _ (hD2 i h0 _ hin)
  · rintro i j hij ⟨hbi, hbj⟩
    by_cases hi0 : i = i0
    · subst hi0
      rw [b0] at hbi
      rw [b1 j (Ne.symm hij) hbi] at hbj
      exact hQ0 _ hbj
    by_cases hj0 : j = i0
    · subst hj0
      rw [b0] at hbj
      rw [b1 i hi0 hbj] at hbi
      exact hQ0 _ hbi
    by_cases hOi : O ∈ S i <;> by_cases hOj : O ∈ S j
    · rw [b1 i hi0 hOi] at hbi
      rw [b1 j hj0 hOj] at hbj
      have e1 := congrArg D (hQline _ j hbi hOj)
      have e2 := congrArg D (hQline _ i hbj hOi)
      rw [hDK] at e1 e2
      rw [e1] at e2
      exact rr_ne hN h3 (D i) e2.symm
    · rw [b1 i hi0 hOi] at hbi
      rw [b2 j hj0 hOj] at hbj
      have e1 := hD2 i hi0 _ hbj
      have e2 : r hN (D i) = D j := by rw [← e1, rs]
      rw [e2] at hbi
      have := hQline2 _ j hbi (hD1 j hj0)
      exact hOj (this ▸ hKO (D j))
    · rw [b2 i hi0 hOi] at hbi
      rw [b1 j hj0 hOj] at hbj
      have e1 := hD2 j hj0 _ hbi
      have e2 : r hN (D j) = D i := by rw [← e1, rs]
      rw [e2] at hbj
      have := hQline2 _ i hbj (hD1 i hi0)
      exact hOi (this ▸ hKO (D i))
    · rw [b2 i hi0 hOi] at hbi
      rw [b2 j hj0 hOj] at hbj
      have e1 := hD2 j hj0 _ hbi
      have e2 := hD2 i hi0 _ hbj
      rw [← e1] at e2
      exact ss_ne hN h3 (D i) e2
end PEqualNP.Outside.L_meta_1468.PlaneChoice

theorem PEqualNP.Outside.L_meta_1468 : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n)),
    2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) →
    (∀ u v : Fin n, u ≠ v → ∃ i : Fin m, u ∈ S i ∧ v ∈ S i) →
    (∃ (i : Fin m) (v : Fin n), v ∉ S i) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) →
    (∀ x : Fin n → Bool, 2 ≤ (Finset.univ.filter (fun v => x v = true)).card →
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn x) = false) →
    m * q + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length := by
  classical
  intro q n m S hq size meet pairs apart L o j legal ng only correct high
  obtain ⟨b, outside, anti⟩ := PEqualNP.Outside.L_meta_1468.PlaneChoice.main q n m S hq size meet pairs apart
  obtain ⟨i0,p0,hp0⟩ := apart
  have hm : 1 ≤ m := by have := i0.isLt;omega
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0<(S i0).card by rw [size];omega)
  have ap : a≠p0 := fun e => hp0 (e ▸ ha)
  obtain ⟨i1,_,h1⟩ := pairs a p0 ap
  have diff : i1≠i0 := fun e => hp0 (e ▸ h1)
  have cov (v : Fin n) : ∃ i,v∈S i := by
    by_cases e : v=p0
    · exact ⟨i1,e ▸ h1⟩
    · obtain ⟨i,hi,_⟩ := pairs v p0 e
      exact ⟨i,hi⟩
  let R (i : Fin m) (p : Fin n) : Finset (Fin n) := {p,b i}
  have rowTest (i : Fin m) (p : Fin n) (hp : p∈S i) : R i p∩S i={p} := by
    ext x
    simp [R,hp,outside,Finset.mem_inter]
  have hits {i k : Fin m} (h : ∃ p∈S i \ S k,(R i p ∩ S k).Nonempty) : b i∈S k := by
    obtain ⟨p,hp,x,hx⟩ := h
    obtain ⟨xr,xk⟩ := Finset.mem_inter.mp hx
    rcases Finset.mem_insert.mp xr with e|e
    · exact ((Finset.mem_sdiff.mp hp).2 (e ▸ xk)).elim
    · exact (Finset.mem_singleton.mp e) ▸ xk
  apply PEqualNP.Outside.L_meta_1468.CircuitCount.main q n m S R (by omega) hm size
    (fun i k h => (meet i k h).le) cov rowTest
    (fun i k ne h => anti i k ne ⟨hits h.1,hits h.2⟩) L o j legal ng only correct
  · intro i
    apply high
    obtain ⟨k,ne⟩ : ∃ k : Fin m,k≠i := by
      by_cases e : i=i0
      · exact ⟨i1,e ▸ diff⟩
      · exact ⟨i0,Ne.symm e⟩
    have sub : S k \ S i ⊆ Finset.univ.filter (fun v : Fin n => decide (v∉S i)=true) := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,decide_eq_true (Finset.mem_sdiff.mp hx).2⟩
    have count := Finset.card_sdiff_add_card_inter (S k) (S i)
    rw [meet k i ne,size] at count
    exact (show 2≤(S k \ S i).card by omega).trans (Finset.card_le_card sub)
  · intro i p hp
    apply high
    have ne : p≠b i := fun e => outside i (e ▸ hp)
    have testSet : Finset.univ.filter (fun v : Fin n => decide (v∈R i p)=true)=R i p := by
      ext x
      simp
    rw [testSet]
    exact (Finset.card_pair ne).ge
