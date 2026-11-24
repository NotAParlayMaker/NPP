import Mathlib
import PEqualNP.Defs

namespace L4187

-- On either ordered branch of an AND, its smaller operand can replace its output.
-- All earlier wires then evaluate to disjunctions of raw inputs or to constants.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev Mask := BitVec 14
abbrev Clause := Option Mask
def hit (a x : Mask) : Bool := (a &&& x) != 0
theorem hit_comm (a x : Mask) : hit a x = hit x a := by rw [hit,BitVec.and_comm];rfl
theorem hit_add (a b x : Mask) : hit (a ||| b) x = (hit a x || hit b x) := by
  apply Bool.eq_iff_iff.mpr
  simp [hit,BitVec.and_or_distrib_right,BitVec.or_eq_zero_iff] <;> tauto
theorem hit_add_r (a x y : Mask) : hit a (x ||| y) = (hit a x || hit a y) := by
  rw [hit_comm a,hit_add,hit_comm x a,hit_comm y a]
theorem hit_sub {a b : Mask} (ab : a &&& b = a) (x : Mask) (h : hit a x = true) : hit b x=true := by
  by_contra! no
  have eq : b &&& x = 0 := by simpa [hit] using no
  have z : a &&& x = 0 := by calc
    _ = (a &&& b) &&& x := by rw [ab]
    _ = a &&& (b &&& x) := BitVec.and_assoc ..
    _ = 0 := by simp [eq]
  simp [hit,z] at h
theorem strip_disj (a b : Mask) : (a &&& ~~~b) &&& (b &&& ~~~a) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [show (0 : Mask).getLsbD i = false from BitVec.getLsbD_zero]
  simp only [BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,BitVec.getLsbD_zero,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> decide
theorem parts (a b : Mask) : (a &&& b) ||| (a &&& ~~~b) = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,BitVec.getLsbD_zero,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> decide

def val (p : Clause) (x : Mask) : Bool := p.elim true (fun a => hit a x)
def merge : Clause → Clause → Clause
  | some a, some b => some (a ||| b)
  | _,_ => none
theorem val_merge (p q : Clause) (x : Mask) : val (merge p q) x = (val p x || val q x) := by
  cases p <;> cases q <;> simp [merge,val,hit_add]

def adm (a b x : Mask) : Prop := hit a x = true → hit b x = true
theorem choice_eq (a b x : Mask) (h : adm (a &&& ~~~b) (b &&& ~~~a) x) :
    (hit a x && hit b x) = hit a x := by
  have l := hit_add (a &&& b) (a &&& ~~~b) x
  have r := hit_add (b &&& a) (b &&& ~~~a) x
  rw [parts] at l r
  rw [BitVec.and_comm b a] at r
  rw [l,r]
  unfold adm at h
  cases h1 : hit (a &&& b) x <;> cases h2 : hit (a &&& ~~~b) x <;>
    cases h3 : hit (b &&& ~~~a) x <;> simp_all
theorem union_left {a b x : Mask} (eq : a ||| (x &&& b)=x) : a &&& x = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e := congrArg (fun q : Mask => q.getLsbD i) eq
  change (a ||| (x &&& b)).getLsbD i = x.getLsbD i at e
  simp only [BitVec.getLsbD_and,BitVec.getLsbD_or] at e ⊢
  cases ha : a.getLsbD i <;> cases hx : x.getLsbD i <;> simp only [ha,hx,Bool.true_or,Bool.false_or,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.true_eq_false] at e ⊢ <;> try contradiction
theorem skip_bit {a b v x : Mask} (eq : a ||| (x &&& (v ||| b))=x) (miss : v &&& x=0) :
    a ||| (x &&& b)=x := by
  rw [BitVec.and_or_distrib_left,BitVec.and_comm x v,miss] at eq
  simpa using eq
theorem include_bit {a b v x : Mask} (eq : a ||| (x &&& (v ||| b))=x) (on : v &&& x=v) :
    (a ||| v) ||| (x &&& b)=x := by
  rw [BitVec.and_or_distrib_left,BitVec.and_comm x v,on,← BitVec.or_assoc] at eq
  exact eq
theorem one_position (n i : Nat) (hi : i < 14) :
    ((1 : Mask) <<< n).getLsbD i = decide (i=n) := by
  change ((1#14) <<< n).getLsbD i = decide (i=n)
  simp only [BitVec.getLsbD_shiftLeft,BitVec.getLsbD_one,hi,decide_true,Bool.true_and]
  by_cases eq : i=n
  · subst i
    simp
  · by_cases le : n ≤ i
    · have ne : i-n ≠ 0 := by omega
      simp [le,ne,eq]
    · simp [le,eq]
theorem atom_mask (n : Fin 14) (x : Mask) :
    ((1 : Mask) <<< n.val) &&& x = if x.getLsbD n.val then ((1 : Mask) <<< n.val) else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and,one_position _ _ hi]
  by_cases e : i=n.val
  · subst i
    cases h : x.getLsbD n.val <;> simp only [h,decide_true,Bool.true_and,Bool.false_eq_true,
      ite_false,ite_true,one_position _ _ hi,show (0 : Mask).getLsbD n.val=false from BitVec.getLsbD_zero]
  · cases h : x.getLsbD n.val <;> simp only [h,e,decide_false,Bool.false_and,Bool.false_eq_true,
      ite_false,ite_true,one_position _ _ hi,show (0 : Mask).getLsbD i=false from BitVec.getLsbD_zero]
theorem singleton_hits (i : Fin 14) (x : Mask) : hit ((1 : Mask) <<< i.val) x = x.getLsbD i.val := by
  have nzero : ((1 : Mask) <<< i.val) ≠ 0 := by fin_cases i <;> decide
  unfold hit
  rw [atom_mask]
  cases h : x.getLsbD i.val
  · rfl
  · exact bne_iff_ne.mpr nzero

def Easy (f : Mask → Bool) : ℕ → (Mask → Prop) → Prop
  | 0,D => ∃ p : Clause, ∀ x, D x → val p x = f x
  | k+1,D => ∃ a b : Mask, a &&& b = 0 ∧
    Easy f k (fun x => D x ∧ adm a b x) ∧ Easy f k (fun x => D x ∧ adm b a x)

theorem restrict {f k D E} (h : Easy f k D) (sub : ∀ x, E x → D x) : Easy f k E := by
  induction k generalizing D E with
  | zero =>
    obtain ⟨p,h⟩ := h
    exact ⟨p,fun x hx => h x (sub x hx)⟩
  | succ k ih =>
    obtain ⟨a,b,dis,l,r⟩ := h
    exact ⟨a,b,dis,ih l (fun x hx => ⟨sub x hx.1,hx.2⟩),ih r (fun x hx => ⟨sub x hx.1,hx.2⟩)⟩

theorem pad {f k D} (h : Easy f k D) : Easy f (k+1) D :=
  ⟨0,0,rfl,restrict h (fun _ h => h.1),restrict h (fun _ h => h.1)⟩

def countAnd (g : Gate) := match g.op with | .and => true | _ => false
def port (w : List Clause) (i : ℕ) : Clause := w.getD i (some 0)
theorem port_val (w : List Clause) (x : Mask) (i : ℕ) :
    (w.map (fun p => val p x)).getD i false = val (port w i) x := by
  simp only [port,List.getD,List.getElem?_map]
  cases w[i]? <;> simp [val,hit]

def zeros (a b : Mask) := a &&& ~~~b
theorem split_disjoint (a b : Mask) : zeros a b &&& zeros b a = 0 := by
  exact strip_disj a b
theorem split_value (a b x : Mask) (h : adm (zeros a b) (zeros b a) x) :
    (hit a x && hit b x) = hit a x := by
  exact choice_eq a b x h

theorem tail_eval (g : Gate) (gs : List Gate) (o : ℕ) (w : List Bool) :
    (Circuit.mk (g::gs) o).eval w =
    (Circuit.mk gs o).eval (w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) := rfl

theorem gate_game (gs : List Gate) (o : ℕ) (ok : ∀ g ∈ gs, (g.op=.or ∨ g.op=.and) ∧ g.inputs.length≤2)
    (f : Mask→Bool) (D : Mask→Prop) (w : List Clause)
    (fits : ∀ x, D x → (Circuit.mk gs o).eval (w.map (fun p => val p x)) = f x) :
    Easy f (gs.countP countAnd) D := by
  induction gs generalizing D w with
  | nil =>
    refine ⟨port w o,fun x hx => ?_⟩
    rw [← port_val]
    exact fits x hx
  | cons g gs ih =>
    have good := ok g (by simp)
    have tail := ih (fun t ht => ok t (by simp [ht]))
    have step (p : Clause) (E : Mask→Prop) (sub : ∀ x, E x → D x)
        (result : ∀ x, E x → g.op.eval (g.inputs.map (fun i => val (port w i) x)) = val p x) :
        Easy f (gs.countP countAnd) E := by
      apply tail E (w++[p])
      intro x hx
      have h := fits x (sub x hx)
      rw [tail_eval] at h
      simp only [port_val] at h
      simpa only [List.map_append,List.map_cons,List.map_nil,← result x hx] using h
    rcases g with ⟨op,ins⟩
    rcases good.1 with ho|ha
    · change op=.or at ho
      subst op
      simp only [List.countP_cons,countAnd,ite_false,Bool.false_eq_true]
      apply step (ins.foldr (fun i p => merge (port w i) p) (some 0)) D (fun _ h => h)
      intro x _
      change List.any (ins.map _) id = _
      clear good step ok fits
      induction ins with
      | nil => simp [val,hit]
      | cons i rest ih => simp_all [val_merge]
    · change op=.and at ha
      subst op
      simp only [List.countP_cons,countAnd,ite_true]
      have len := good.2
      cases ins with
      | nil => exact pad (step none D (fun _ h => h) (by simp [GateOp.eval,val]))
      | cons i rest =>
        cases rest with
        | nil => exact pad (step (port w i) D (fun _ h => h) (by simp [GateOp.eval]))
        | cons j rest =>
          obtain rfl : rest=[] := by simpa using len
          cases pi : port w i with
          | none =>
            exact pad (step (port w j) D (fun _ h => h) (by simp [GateOp.eval,pi,val]))
          | some a =>
            cases pj : port w j with
            | none =>
              exact pad (step (some a) D (fun _ h => h) (by simp [GateOp.eval,pi,pj,val]))
            | some b =>
              refine ⟨zeros a b,zeros b a,split_disjoint _ _,step (some a) _ (fun _ h => h.1) ?_,
                step (some b) _ (fun _ h => h.1) ?_⟩
              · intro x hx
                simpa [GateOp.eval,pi,pj,val] using split_value a b x hx.2
              · intro x hx
                simpa [GateOp.eval,pi,pj,val,Bool.and_comm] using split_value b a x hx.2

-- A disjunction vanishing on two rows vanishes on their union. The domains
-- defined by the operand comparisons are closed under union.
theorem val_join (p : Clause) (x y : Mask) : val p (x ||| y) = (val p x || val p y) := by
  cases p <;> simp [val,hit_add_r]

theorem adm_join {a b x y} (hx : adm a b x) (hy : adm a b y) : adm a b (x ||| y) := by
  unfold adm at *
  rw [hit_add_r,hit_add_r]
  simp only [Bool.or_eq_true]
  exact fun h => h.imp hx hy

theorem capacity {f k D} (game : Easy f k D) (rows : Finset Mask)
    (inside : ∀ x ∈ rows, D x) (closed : ∀ x y, D x → D y → D (x ||| y))
    (neg : ∀ x ∈ rows, f x = false)
    (pair : ∀ x ∈ rows, ∀ y ∈ rows, x≠y → f (x ||| y) = true) : rows.card ≤ 2^k := by
  induction k generalizing rows D with
  | zero =>
    obtain ⟨p,h⟩ := game
    apply Finset.card_le_one.mpr
    intro x hx y hy
    by_contra ne
    have v := h _ (closed _ _ (inside _ hx) (inside _ hy))
    rw [val_join,h _ (inside _ hx),h _ (inside _ hy),neg _ hx,neg _ hy,pair _ hx _ hy ne] at v
    contradiction
  | succ k ih =>
    obtain ⟨a,b,_,l,r⟩ := game
    classical
    let L := rows.filter (adm a b)
    let R := rows.filter (adm b a)
    have small (s t : Mask) (h : Easy f k (fun x => D x ∧ adm s t x)) :
        (rows.filter (adm s t)).card ≤ 2^k := by
      apply ih h
      · intro x hx
        exact ⟨inside _ (Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2⟩
      · intro x y hx hy
        exact ⟨closed _ _ hx.1 hy.1,adm_join hx.2 hy.2⟩
      · intro x hx
        exact neg _ (Finset.mem_filter.mp hx).1
      · intro x hx y hy
        exact pair _ (Finset.mem_filter.mp hx).1 _ (Finset.mem_filter.mp hy).1
    have un : rows ⊆ L ∪ R := by
      intro x hx
      by_cases h : adm a b x
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx,h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx,by unfold adm at *;tauto⟩)
    have := (Finset.card_le_card un).trans (Finset.card_union_le L R)
    have hl : L.card ≤ 2^k := small a b l
    have hr : R.card ≤ 2^k := small b a r
    rw [pow_succ]
    omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev V := Fin 14
def edges : List (Nat × Nat) := [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),
  (3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
def vertex (i : Nat) : Mask := 1 <<< i
def assignment (x : Mask) (v : V) := hit (vertex v.val) x
def edge (x : Mask) := edges.any (fun e => hit (vertex e.1) x && hit (vertex e.2) x)
def target (y : V→Bool) := ∃ u v : V, (u.val,v.val) ∈ edges ∧ y u=true ∧ y v=true
theorem edge_ok (x : Mask) : edge x = true ↔ target (assignment x) := by
  have bounds : ∀ e ∈ edges, e.1<14 ∧ e.2<14 := by decide
  simp only [edge,List.any_eq_true,Bool.and_eq_true]
  constructor
  · rintro ⟨e,he,hu,hv⟩
    exact ⟨⟨e.1,(bounds e he).1⟩,⟨e.2,(bounds e he).2⟩,he,hu,hv⟩
  · rintro ⟨u,v,he,hu,hv⟩
    exact ⟨(u.val,v.val),he,hu,hv⟩

def input (y : V→Bool) := List.ofFn y ++ [y 0 || y 1]
def bank : List Clause := (List.ofFn (fun i : V => some (vertex i.val))) ++ [some 3]
theorem bank_eval (x : Mask) : bank.map (fun p => val p x) = input (assignment x) := by
  have q := hit_add (1 : Mask) 2 x
  change hit 3 x = (hit 1 x || hit 2 x) at q
  simp [bank,input,assignment,val,vertex]
  exact q

theorem get_le {l r : List Bool} (h : List.Forall₂ (·≤·) l r) (i : Nat) :
    l.getD i false ≤ r.getD i false := by
  induction h generalizing i with
  | nil => rfl
  | cons h _ ih => cases i <;> first | exact h | exact ih _

theorem eval_mono (gs : List Gate) (o : Nat) (ok : ∀ g ∈ gs, g.op=.and ∨ g.op=.or)
    (l r : List Bool) (w : List.Forall₂ (·≤·) l r) :
    (Circuit.mk gs o).eval l ≤ (Circuit.mk gs o).eval r := by
  induction gs generalizing l r with
  | nil => exact get_le w _
  | cons g gs ih =>
    rw [tail_eval,tail_eval]
    apply ih (fun _ hm => ok _ (by simp [hm]))
    apply List.rel_append w
    apply List.Forall₂.cons _ List.Forall₂.nil
    have portle := get_le w
    rcases ok g (by simp) with h|h
    · simp only [h,GateOp.eval,List.all_map,Function.comp_def,id_eq,Bool.le_iff_imp,
        List.all_eq_true]
      intro hy i hi
      exact (Bool.le_iff_imp.mp (portle i)) (hy i hi)
    · simp only [h,GateOp.eval,List.any_map,Function.comp_def,id_eq,Bool.le_iff_imp,
        List.any_eq_true]
      rintro ⟨i,hi,hy⟩
      exact ⟨i,hi,(Bool.le_iff_imp.mp (portle i)) hy⟩

theorem input_le {y z : V→Bool} (h : y≤z) : List.Forall₂ (·≤·) (input y) (input z) := by
  apply List.rel_append
  · apply List.forall₂_of_length_eq_of_get (by simp)
    intro i hi hj
    simp only [List.get_ofFn]
    exact h ⟨i,by simpa only [List.length_ofFn] using hi⟩
  · apply List.Forall₂.cons _ List.Forall₂.nil
    exact sup_le_sup (h 0) (h 1)

def boundary (y : V→Bool) := (target y ∧ ∀ i, y i=true → ¬target (Function.update y i false)) ∨
  ¬target y ∧ ∀ i, y i=false → target (Function.update y i true)
theorem extend (C : Circuit) (hm : Monotone2 C)
    (test : ∀ y, boundary y → (C.eval (input y)=true ↔ target y)) :
    ∀ y, C.eval (input y)=true ↔ target y := by
  classical
  have mono {y z : V→Bool} (h : y≤z) : C.eval (input y) ≤ C.eval (input z) :=
    eval_mono C.gates C.output (fun g hg => (hm g hg).1) _ _ (input_le h)
  intro y
  constructor
  · intro yes
    by_contra no
    obtain ⟨z,yz,hz⟩ := exists_maximal_ge_of_wellFoundedGT (fun y => ¬target y) y no
    have bd : boundary z := by
      refine Or.inr ⟨hz.1,fun i hi => ?_⟩
      by_contra absent
      have le : z ≤ Function.update z i true := by
        intro j
        by_cases e : j=i <;> simp [e]
      have back := hz.2 absent le i
      simp [hi] at back
      exact (by decide : ¬ (true ≤ false)) back
    exact hz.1 ((test _ bd).mp ((Bool.le_iff_imp.mp (mono yz)) yes))
  · intro yes
    obtain ⟨z,zy,hz⟩ := exists_minimal_le_of_wellFoundedLT target y yes
    have bd : boundary z := by
      refine Or.inl ⟨hz.1,fun i hi present => ?_⟩
      have le : Function.update z i false ≤ z := by
        intro j
        by_cases e : j=i <;> simp [e]
      have back := hz.2 present le i
      simp [hi] at back
      exact (by decide : ¬ (true ≤ false)) back
    exact (Bool.le_iff_imp.mp (mono zy)) ((test _ bd).mpr hz.1)

theorem start (C : Circuit) (hm : Monotone2 C)
    (test : ∀ y, boundary y → (C.eval (input y)=true ↔ target y)) :
    Easy edge (C.gates.countP countAnd) (fun _ => True) := by
  apply gate_game C.gates C.output _ _ _ bank
  · intro x _
    rw [bank_eval]
    exact Bool.eq_iff_iff.mpr ((extend C hm test _).trans (edge_ok x).symm)
  · intro g hg
    obtain ⟨op,le⟩ := hm g hg
    exact ⟨Or.symm op,le⟩

abbrev Rows := List Mask
def bits : List Mask := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192]
def enumPorts (ok : Mask → Bool) : List Mask → Mask → List Mask
  | [],a => if ok a then [a] else []
  | v::vs,a => if ok a then enumPorts ok vs a ++ enumPorts ok vs (a ||| v) else []
def small (rows : Rows) (n : Nat) (a : Mask) := decide (rows.countP (hit a) ≤ n)

theorem small_down {rows n x y} (h : x &&& y = x) (hy : small rows n y = true) :
    small rows n x = true := by
  simp only [small,decide_eq_true_eq] at *
  apply le_trans _ hy
  apply List.countP_mono_left
  intro t _ ht
  exact hit_sub h t ht

theorem enum_contains (rows : Rows) (n : Nat) (x : Mask) (ok : small rows n x = true)
    (vs : List Mask) (one : ∀ v ∈ vs, v &&& x = 0 ∨ v &&& x = v)
    (a : Mask) (eq : a ||| (x &&& vs.foldr (· ||| ·) 0) = x) :
    x ∈ enumPorts (small rows n) vs a := by
  induction vs generalizing a with
  | nil =>
    simp only [List.foldr_nil,BitVec.and_zero,BitVec.or_zero] at eq
    have ax : a=x := by simpa using eq
    subst a
    simp [enumPorts,ok]
  | cons v vs ih =>
    have le : a &&& x = a := by
      simp only [List.foldr_cons] at eq
      exact union_left eq
    simp only [enumPorts,small_down le ok,if_true,List.mem_append]
    have ov := one v (by simp)
    have tail := ih (fun u hu => one u (by simp [hu]))
    simp only [List.foldr_cons] at eq
    rcases ov with zero|whole
    · left
      apply tail a
      exact skip_bit eq zero
    · right
      apply tail (a ||| v)
      exact include_bit eq whole
theorem enumerate (rows : Rows) (n : Nat) (x : Mask) (ok : small rows n x = true) :
    x ∈ enumPorts (small rows n) bits 0 := by
  apply enum_contains _ _ _ ok
  · intro v hv
    have one (i : Fin 14) : ((1 : Mask) <<< i.val) &&& x = 0 ∨ ((1 : Mask) <<< i.val) &&& x = ((1 : Mask) <<< i.val) := by
      rw [atom_mask]
      cases x.getLsbD i.val <;> simp
    simp only [bits,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact one 0
    · exact one 1
    · exact one 2
    · exact one 3
    · exact one 4
    · exact one 5
    · exact one 6
    · exact one 7
    · exact one 8
    · exact one 9
    · exact one 10
    · exact one 11
    · exact one 12
    · exact one 13
  · change 0 ||| (x &&& BitVec.allOnes 14) = x
    exact (BitVec.zero_or (x:=x &&& BitVec.allOnes 14)).trans (BitVec.and_allOnes (x:=x))

def fast (x : Mask) := (hit (vertex 0) x && hit (vertex 7 ||| vertex 8 ||| vertex 10) x) ||
  (hit (vertex 1) x && hit (vertex 7 ||| vertex 9 ||| vertex 13) x) ||
  (hit (vertex 2) x && hit (vertex 8 ||| vertex 12 ||| vertex 13) x) ||
  (hit (vertex 3) x && hit (vertex 7 ||| vertex 11 ||| vertex 12) x) ||
  (hit (vertex 4) x && hit (vertex 10 ||| vertex 11 ||| vertex 13) x) ||
  (hit (vertex 5) x && hit (vertex 9 ||| vertex 10 ||| vertex 12) x) ||
  (hit (vertex 6) x && hit (vertex 8 ||| vertex 9 ||| vertex 11) x)
theorem fast_edge (x : Mask) : fast x = edge x := by
  simp only [fast,edge,edges,List.any_cons,List.any_nil,hit_add,Bool.and_or_distrib_left,
    Bool.or_false, Bool.or_assoc]

abbrev Rules := List (Mask × Mask)
def obey (a b x : Mask) := !hit a x || hit b x
theorem obey_iff (a b x : Mask) : obey a b x = true ↔ adm a b x := by
  unfold obey adm
  cases hit a x <;> cases hit b x <;> decide
def inDomain (rules : Rules) (x : Mask) := rules.all (fun r => obey r.1 r.2 x)
def D (rules : Rules) (x : Mask) := inDomain rules x = true
theorem in_cons (a b : Mask) (rs : Rules) (x : Mask) :
    D ((a,b)::rs) x ↔ D rs x ∧ adm a b x := by
  simp [D,inDomain,obey_iff,and_comm]
theorem domain_closed (rs : Rules) (x y : Mask) (hx : D rs x) (hy : D rs y) : D rs (x ||| y) := by
  simp only [D,inDomain,List.all_eq_true,obey_iff] at *
  exact fun r hr => adm_join (hx r hr) (hy r hr)
def valid (rs : Rules) (rows : Rows) : Bool :=
  rows.all (fun x => inDomain rs x && !fast x) && decide rows.Nodup &&
  rows.all (fun x => rows.all (fun y => x == y || fast (x ||| y)))
theorem bound_list {rs rows k} (bank : valid rs rows = true) (easy : Easy edge k (D rs)) :
    rows.length ≤ 2^k := by
  simp only [valid,Bool.and_eq_true,List.all_eq_true,Bool.not_eq_true',decide_eq_true_eq,
    Bool.or_eq_true,beq_iff_eq,fast_edge] at bank
  obtain ⟨⟨good,unique⟩,pairs⟩ := bank
  rw [← List.toFinset_card_of_nodup unique]
  apply capacity easy _ _ (domain_closed _) _ _
  · intro x hx
    exact (good x (List.mem_toFinset.mp hx)).1
  · intro x hx
    exact (good x (List.mem_toFinset.mp hx)).2
  · intro x hx y hy ne
    exact (pairs x (List.mem_toFinset.mp hx) y (List.mem_toFinset.mp hy)).resolve_left ne

def survives (a b : Mask) (rows : Rows) := rows.countP (obey a b)
theorem survive_le {rs rows k a b} (bank : valid rs rows = true)
    (easy : Easy edge k (D ((a,b)::rs))) : survives a b rows ≤ 2^k := by
  let t := rows.filter (obey a b)
  have cert : valid ((a,b)::rs) t = true := by
    simp only [valid,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at bank ⊢
    refine ⟨⟨?_,bank.1.2.filter _⟩,?_⟩
    · intro x hx
      obtain ⟨h,o⟩ := List.mem_filter.mp hx
      have g := bank.1.1 x h
      exact ⟨by change (obey a b x && inDomain rs x) = true; rw [o,g.1]; rfl,g.2⟩
    · intro x hx y hy
      exact bank.2 x (List.mem_filter.mp hx).1 y (List.mem_filter.mp hy).1
  simpa only [survives,List.countP_eq_length_filter] using bound_list cert easy
theorem port_small {rs rows k a b} (bank : valid rs rows = true)
    (easy : Easy edge k (D ((a,b)::rs))) : small rows (2^k) b = true := by
  simp only [small,decide_eq_true_eq]
  apply le_trans _ (survive_le bank easy)
  apply List.countP_mono_left
  intro x _ h
  simp [obey,h]

def seeds : Rows :=
  [127,2212,4304,6147,8416,244,2087,4370,2338,8488,314,10656,432,10273,2565,8713,
   4625,541,4179,660,12353,8297,792,5008,14849,3078,5186,9288,1102,13504,1220,7426,
   1290,1548,3716,9992,16256]

-- These twelve incidence-preserving involutions reduce the first comparison to finitely many cases.
def linked (u v : V) := (u.val,v.val) ∈ edges ∨ (v.val,u.val) ∈ edges
theorem edge_indices (x : Mask) : edge x = true ↔ ∃ u v : V, linked u v ∧
    x.getLsbD u.val = true ∧ x.getLsbD v.val = true := by
  rw [edge_ok]
  constructor
  · rintro ⟨u,v,e,a,b⟩
    exact ⟨u,v,Or.inl e,(singleton_hits u x).symm.trans a,(singleton_hits v x).symm.trans b⟩
  · rintro ⟨u,v,(e|e),a,b⟩
    · exact ⟨u,v,e,(singleton_hits u x).trans a,(singleton_hits v x).trans b⟩
    · exact ⟨v,u,e,(singleton_hits v x).trans b,(singleton_hits u x).trans a⟩
theorem hit_indices (a x : Mask) : hit a x = true ↔ ∃ i : V,
    a.getLsbD i.val = true ∧ x.getLsbD i.val = true := by
  constructor
  · intro h
    by_contra! none
    have e : a &&& x = 0 := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [show (0 : Mask).getLsbD i = false from BitVec.getLsbD_zero,BitVec.getLsbD_and]
      cases ha : a.getLsbD i <;> cases hx : x.getLsbD i <;> try rfl
      exact False.elim (none ⟨i,hi⟩ ha hx)
    simp [hit,e] at h
  · rintro ⟨i,ha,hx⟩
    by_contra! no
    have z : a &&& x = 0 := by simpa [hit] using no
    have bit := congrArg (fun w : Mask => w.getLsbD i.val) z
    change (a &&& x).getLsbD i.val = (0 : Mask).getLsbD i.val at bit
    rw [BitVec.getLsbD_and,ha,hx,show (0 : Mask).getLsbD i.val = false from BitVec.getLsbD_zero] at bit
    contradiction

theorem permutation_laws (f : Mask→Mask) (p : V→V)
    (bit : ∀ x (i : V), (f x).getLsbD i.val = x.getLsbD (p i).val)
    (inv : ∀ i, p (p i) = i) (inc : ∀ i j, linked i j → linked (p i) (p j))
    (x y : Mask) : f (f x) = x ∧ hit (f x) (f y) = hit x y ∧ edge (f x)=edge x := by
  have back (z : Mask) (i : V) : (f z).getLsbD (p i).val = z.getLsbD i.val :=
    (bit z (p i)).trans (congrArg (fun t : V => z.getLsbD t.val) (inv i))
  refine ⟨?_,?_,?_⟩
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    change (f (f x)).getLsbD (⟨i,hi⟩ : V).val = _
    exact (bit (f x) ⟨i,hi⟩).trans (back x ⟨i,hi⟩)
  · apply Bool.eq_iff_iff.mpr
    rw [hit_indices,hit_indices]
    constructor
    · rintro ⟨i,a,b⟩
      exact ⟨p i,(bit _ _).symm.trans a,(bit _ _).symm.trans b⟩
    · rintro ⟨i,a,b⟩
      exact ⟨p i,(back x i).trans a,(back y i).trans b⟩
  · apply Bool.eq_iff_iff.mpr
    rw [edge_indices,edge_indices]
    constructor
    · rintro ⟨i,j,e,a,b⟩
      exact ⟨p i,p j,inc _ _ e,(bit _ _).symm.trans a,(bit _ _).symm.trans b⟩
    · rintro ⟨i,j,e,a,b⟩
      exact ⟨p i,p j,inc _ _ e,(back x i).trans a,(back x j).trans b⟩

def ren0 (x : Mask) : Mask := ((x &&& 16256) >>> 7) ||| ((x &&& 127) <<< 7)
def perm0 : V → V := ![7,8,9,10,11,12,13,0,1,2,3,4,5,6]
theorem bitAction0 (x : Mask) (j : V) : (ren0 x).getLsbD j.val = x.getLsbD (perm0 j).val := by
  fin_cases j <;> simp [ren0,perm0,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight] <;> rfl
theorem laws0 (x y : Mask) : ren0 (ren0 x) = x ∧ hit (ren0 x) (ren0 y) = hit x y ∧ edge (ren0 x) = edge x :=
  permutation_laws _ perm0 bitAction0 (by decide +kernel) (by unfold linked edges;decide +kernel) x y

def ren1 (x : Mask) : Mask := ((x &&& 1040) >>> 2) ||| ((x &&& 4160) >>> 1) ||| (x &&& 8843) ||| ((x &&& 2080) <<< 1) ||| ((x &&& 260) <<< 2)
def perm1 : V → V := ![0,1,4,3,2,6,5,7,10,9,8,12,11,13]
theorem bitAction1 (x : Mask) (j : V) : (ren1 x).getLsbD j.val = x.getLsbD (perm1 j).val := by
  fin_cases j <;> simp [ren1,perm1,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight] <;> rfl
theorem laws1 (x y : Mask) : ren1 (ren1 x) = x ∧ hit (ren1 x) (ren1 y) = hit x y ∧ edge (ren1 x) = edge x :=
  permutation_laws _ perm1 bitAction1 (by decide +kernel) (by unfold linked edges;decide +kernel) x y

def ren2 (x : Mask) : Mask := ((x &&& 64) >>> 6) ||| ((x &&& 544) >>> 2) ||| ((x &&& 2048) >>> 1) ||| (x &&& 12566) ||| ((x &&& 1024) <<< 1) ||| ((x &&& 136) <<< 2) ||| ((x &&& 1) <<< 6)
def perm2 : V → V := ![6,1,2,5,4,3,0,9,8,7,11,10,12,13]
theorem bitAction2 (x : Mask) (j : V) : (ren2 x).getLsbD j.val = x.getLsbD (perm2 j).val := by
  fin_cases j <;> simp [ren2,perm2,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight] <;> rfl
theorem laws2 (x y : Mask) : ren2 (ren2 x) = x ∧ hit (ren2 x) (ren2 y) = hit x y ∧ edge (ren2 x) = edge x :=
  permutation_laws _ perm2 bitAction2 (by decide +kernel) (by unfold linked edges;decide +kernel) x y

def ren3 (x : Mask) : Mask := ((x &&& 2056) >>> 2) ||| ((x &&& 8224) >>> 1) ||| (x &&& 1477) ||| ((x &&& 4112) <<< 1) ||| ((x &&& 514) <<< 2)
def perm3 : V → V := ![0,3,2,1,5,4,6,7,8,11,10,9,13,12]
theorem bitAction3 (x : Mask) (j : V) : (ren3 x).getLsbD j.val = x.getLsbD (perm3 j).val := by
  fin_cases j <;> simp [ren3,perm3,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight] <;> rfl
theorem laws3 (x y : Mask) : ren3 (ren3 x) = x ∧ hit (ren3 x) (ren3 y) = hit x y ∧ edge (ren3 x) = edge x :=
  permutation_laws _ perm3 bitAction3 (by decide +kernel) (by unfold linked edges;decide +kernel) x y

def ren4 (x : Mask) : Mask := ((x &&& 4160) >>> 3) ||| ((x &&& 260) >>> 1) ||| (x &&& 11313) ||| ((x &&& 130) <<< 1) ||| ((x &&& 520) <<< 3)
def perm4 : V → V := ![0,2,1,6,4,5,3,8,7,12,10,11,9,13]
theorem bitAction4 (x : Mask) (j : V) : (ren4 x).getLsbD j.val = x.getLsbD (perm4 j).val := by
  fin_cases j <;> simp [ren4,perm4,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight] <;> rfl
theorem laws4 (x y : Mask) : ren4 (ren4 x) = x ∧ hit (ren4 x) (ren4 y) = hit x y ∧ edge (ren4 x) = edge x :=
  permutation_laws _ perm4 bitAction4 (by decide +kernel) (by unfold linked edges;decide +kernel) x y

def ren5 (x : Mask) : Mask := ((x &&& 8224) >>> 3) ||| ((x &&& 514) >>> 1) ||| (x &&& 6360) ||| ((x &&& 257) <<< 1) ||| ((x &&& 1028) <<< 3)
def perm5 : V → V := ![1,0,5,3,4,2,6,7,9,8,13,11,12,10]
theorem bitAction5 (x : Mask) (j : V) : (ren5 x).getLsbD j.val = x.getLsbD (perm5 j).val := by
  fin_cases j <;> simp [ren5,perm5,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight] <;> rfl
theorem laws5 (x y : Mask) : ren5 (ren5 x) = x ∧ hit (ren5 x) (ren5 y) = hit x y ∧ edge (ren5 x) = edge x :=
  permutation_laws _ perm5 bitAction5 (by decide +kernel) (by unfold linked edges;decide +kernel) x y

def ren6 (x : Mask) : Mask := ((x &&& 4096) >>> 12) ||| ((x &&& 2048) >>> 10) ||| ((x &&& 8192) >>> 7) ||| ((x &&& 256) >>> 6) ||| ((x &&& 1536) >>> 5) ||| ((x &&& 128) >>> 4) ||| ((x &&& 8) <<< 4) ||| ((x &&& 48) <<< 5) ||| ((x &&& 4) <<< 6) ||| ((x &&& 64) <<< 7) ||| ((x &&& 2) <<< 10) ||| ((x &&& 1) <<< 12)
def perm6 : V → V := ![12,11,8,7,9,10,13,3,2,4,5,1,0,6]
theorem bitAction6 (x : Mask) (j : V) : (ren6 x).getLsbD j.val = x.getLsbD (perm6 j).val := by
  fin_cases j <;> simp [ren6,perm6,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight] <;> rfl
theorem laws6 (x y : Mask) : ren6 (ren6 x) = x ∧ hit (ren6 x) (ren6 y) = hit x y ∧ edge (ren6 x) = edge x :=
  permutation_laws _ perm6 bitAction6 (by decide +kernel) (by unfold linked edges;decide +kernel) x y

def ren7 (x : Mask) : Mask := ((x &&& 8192) >>> 6) ||| ((x &&& 4100) >>> 2) ||| ((x &&& 16) >>> 1) ||| (x &&& 2914) ||| ((x &&& 8) <<< 1) ||| ((x &&& 1025) <<< 2) ||| ((x &&& 128) <<< 6)
def perm7 : V → V := ![2,1,0,4,3,5,6,13,8,9,12,11,10,7]
theorem bitAction7 (x : Mask) (j : V) : (ren7 x).getLsbD j.val = x.getLsbD (perm7 j).val := by
  fin_cases j <;> simp [ren7,perm7,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight] <;> rfl
theorem laws7 (x y : Mask) : ren7 (ren7 x) = x ∧ hit (ren7 x) (ren7 y) = hit x y ∧ edge (ren7 x) = edge x :=
  permutation_laws _ perm7 bitAction7 (by decide +kernel) (by unfold linked edges;decide +kernel) x y

def ren8 (x : Mask) : Mask := ((x &&& 64) >>> 4) ||| ((x &&& 4096) >>> 3) ||| ((x &&& 8200) >>> 2) ||| (x &&& 1457) ||| ((x &&& 2050) <<< 2) ||| ((x &&& 512) <<< 3) ||| ((x &&& 4) <<< 4)
def perm8 : V → V := ![0,3,6,1,4,5,2,7,8,12,10,13,9,11]
theorem bitAction8 (x : Mask) (j : V) : (ren8 x).getLsbD j.val = x.getLsbD (perm8 j).val := by
  fin_cases j <;> simp [ren8,perm8,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight] <;> rfl
theorem laws8 (x y : Mask) : ren8 (ren8 x) = x ∧ hit (ren8 x) (ren8 y) = hit x y ∧ edge (ren8 x) = edge x :=
  permutation_laws _ perm8 bitAction8 (by decide +kernel) (by unfold linked edges;decide +kernel) x y

def ren9 (x : Mask) : Mask := ((x &&& 8192) >>> 5) ||| ((x &&& 64) >>> 2) ||| ((x &&& 1026) >>> 1) ||| (x &&& 6316) ||| ((x &&& 513) <<< 1) ||| ((x &&& 16) <<< 2) ||| ((x &&& 256) <<< 5)
def perm9 : V → V := ![1,0,2,3,6,5,4,7,13,10,9,11,12,8]
theorem bitAction9 (x : Mask) (j : V) : (ren9 x).getLsbD j.val = x.getLsbD (perm9 j).val := by
  fin_cases j <;> simp [ren9,perm9,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight] <;> rfl
theorem laws9 (x y : Mask) : ren9 (ren9 x) = x ∧ hit (ren9 x) (ren9 y) = hit x y ∧ edge (ren9 x) = edge x :=
  permutation_laws _ perm9 bitAction9 (by decide +kernel) (by unfold linked edges;decide +kernel) x y

def ren10 (x : Mask) : Mask := ((x &&& 1024) >>> 10) ||| ((x &&& 6144) >>> 9) ||| ((x &&& 512) >>> 8) ||| ((x &&& 8192) >>> 7) ||| ((x &&& 256) >>> 4) ||| ((x &&& 128) >>> 2) ||| ((x &&& 32) <<< 2) ||| ((x &&& 16) <<< 4) ||| ((x &&& 64) <<< 7) ||| ((x &&& 2) <<< 8) ||| ((x &&& 12) <<< 9) ||| ((x &&& 1) <<< 10)
def perm10 : V → V := ![10,9,11,12,8,7,13,5,4,1,0,2,3,6]
theorem bitAction10 (x : Mask) (j : V) : (ren10 x).getLsbD j.val = x.getLsbD (perm10 j).val := by
  fin_cases j <;> simp [ren10,perm10,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight] <;> rfl
theorem laws10 (x y : Mask) : ren10 (ren10 x) = x ∧ hit (ren10 x) (ren10 y) = hit x y ∧ edge (ren10 x) = edge x :=
  permutation_laws _ perm10 bitAction10 (by decide +kernel) (by unfold linked edges;decide +kernel) x y

def ren11 (x : Mask) : Mask := ((x &&& 4096) >>> 4) ||| ((x &&& 8) >>> 3) ||| ((x &&& 2112) >>> 1) ||| (x &&& 8854) ||| ((x &&& 1056) <<< 1) ||| ((x &&& 1) <<< 3) ||| ((x &&& 256) <<< 4)
def perm11 : V → V := ![3,1,2,0,4,6,5,7,12,9,11,10,8,13]
theorem bitAction11 (x : Mask) (j : V) : (ren11 x).getLsbD j.val = x.getLsbD (perm11 j).val := by
  fin_cases j <;> simp [ren11,perm11,BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight] <;> rfl
theorem laws11 (x y : Mask) : ren11 (ren11 x) = x ∧ hit (ren11 x) (ren11 y) = hit x y ∧ edge (ren11 x) = edge x :=
  permutation_laws _ perm11 bitAction11 (by decide +kernel) (by unfold linked edges;decide +kernel) x y

def ren (i : Fin 12) : Mask → Mask := ![ren0,ren1,ren2,ren3,ren4,ren5,ren6,ren7,ren8,ren9,ren10,ren11] i
theorem ren_laws (i : Fin 12) (x y : Mask) : ren i (ren i x) = x ∧ hit (ren i x) (ren i y) = hit x y ∧ edge (ren i x) = edge x := by
  fin_cases i
  · exact laws0 x y
  · exact laws1 x y
  · exact laws2 x y
  · exact laws3 x y
  · exact laws4 x y
  · exact laws5 x y
  · exact laws6 x y
  · exact laws7 x y
  · exact laws8 x y
  · exact laws9 x y
  · exact laws10 x y
  · exact laws11 x y
theorem ren_clause (i : Fin 12) (p : Clause) (x : Mask) :
    val (p.map (ren i)) x = val p (ren i x) := by
  cases p with
  | none => rfl
  | some a =>
    change hit (ren i a) x = hit a (ren i x)
    have h := (ren_laws i a (ren i x)).2.1
    rwa [(ren_laws i x x).1] at h
theorem ren_easy (i : Fin 12) {k P} (easy : Easy edge k P) :
    Easy edge k (fun x => P (ren i x)) := by
  induction k generalizing P with
  | zero =>
    obtain ⟨p,h⟩ := easy
    exact ⟨p.map (ren i),fun x hx => (ren_clause i p x).trans ((h _ hx).trans (ren_laws i x x).2.2)⟩
  | succ k ih =>
    obtain ⟨a,b,dis,l,r⟩ := easy
    have rotate (a x : Mask) : hit (ren i a) x = hit a (ren i x) := ren_clause i (some a) x
    have cv {a b x : Mask} : adm (ren i a) (ren i b) x → adm a b (ren i x) := by
      simp only [adm,rotate]
      exact id
    refine ⟨ren i a,ren i b,?_,restrict (ih l) (fun x hx => ⟨hx.1,cv hx.2⟩),
      restrict (ih r) (fun x hx => ⟨hx.1,cv hx.2⟩)⟩
    have h := (ren_laws i a b).2.1
    simp [hit,dis] at h
    exact h

def pairOK (a b : Mask) := a &&& b = 0 ∧ Easy edge 5 (D [(a,b)]) ∧ Easy edge 5 (D [(b,a)])
theorem pair_flip {a b} (h : pairOK a b) : pairOK b a :=
  ⟨by rw [BitVec.and_comm,h.1],h.2.2,h.2.1⟩
theorem pair_ren (i : Fin 12) {a b} (h : pairOK a b) : pairOK (ren i a) (ren i b) := by
  have rot (c x : Mask) : hit (ren i c) x = hit c (ren i x) := ren_clause i (some c) x
  have go (p q : Mask) (e : Easy edge 5 (D [(p,q)])) : Easy edge 5 (D [(ren i p,ren i q)]) := by
    apply restrict (ren_easy i e)
    intro x hx
    simpa [D,inDomain,obey,rot] using hx
  have eq := (ren_laws i a b).2.1
  simp [hit,h.1] at eq
  exact ⟨eq,go _ _ h.2.1,go _ _ h.2.2⟩
def key (a b : Mask) := 16384*a.toNat+b.toNat
def firstOK (a : Mask) := (List.finRange 12).all (fun i => decide (a.toNat ≤ (ren i a).toNat))
def orderOK (a b : Mask) := decide (key a b ≤ key b a) &&
  (List.finRange 12).all (fun i => decide (key a b ≤ key (ren i a) (ren i b) ∧
     key a b ≤ key (ren i b) (ren i a)))
theorem canonical (e : Easy edge 6 (fun _ => True)) : ∃ a b, pairOK a b ∧ firstOK a = true ∧ orderOK a b = true := by
  classical
  obtain ⟨a,b,dis,l,r⟩ := e
  have init : pairOK a b := ⟨dis,restrict l (by intro x hx;simpa [D,inDomain,obey_iff] using hx),
    restrict r (by intro x hx;simpa [D,inDomain,obey_iff] using hx)⟩
  let P (n : Nat) := ∃ p q, pairOK p q ∧ key p q = n
  have ex : ∃ n, P n := ⟨_,a,b,init,rfl⟩
  obtain ⟨p,q,h,eq⟩ := Nat.find_spec ex
  have least (s t : Mask) (good : pairOK s t) : key p q ≤ key s t :=
    eq ▸ Nat.find_min' ex ⟨s,t,good,rfl⟩
  refine ⟨p,q,h,?_,?_⟩
  · simp only [firstOK,List.all_eq_true,decide_eq_true_eq]
    intro i _
    have k := least _ _ (pair_ren i h)
    have lt := (ren i q).isLt
    change (ren i q).toNat < 16384 at lt
    unfold key at k
    omega
  · simp only [orderOK,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq]
    exact ⟨least _ _ (pair_flip h),fun i _ => ⟨least _ _ (pair_ren i h),least _ _ (pair_flip (pair_ren i h))⟩⟩

-- Each row occupies one base-64 digit. With fewer than 63 rows, reduction modulo 63
-- counts the selected rows, and bitwise union combines disjunctions.
def digit (a : Nat) (b : Bool) := (a <<< 6) ||| b.toNat
def flags : Rows → (Mask → Bool) → Nat
  | [],_ => 0
  | x::xs,p => digit (flags xs p) (p x)
theorem digit_or (a c : Nat) (b d : Bool) : digit (a ||| c) (b || d) = digit a b ||| digit c d := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [digit,Nat.testBit_or,Nat.testBit_xor,Nat.testBit_shiftLeft,Nat.testBit_bool_toNat]
  by_cases z : i = 0
  · subst i
    simp
  · by_cases hi : 6 ≤ i <;> simp [z,hi]
theorem digit_xor (a c : Nat) (b d : Bool) : digit (a ^^^ c) (b ^^ d) = digit a b ^^^ digit c d := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [digit,Nat.testBit_or,Nat.testBit_xor,Nat.testBit_shiftLeft,Nat.testBit_bool_toNat]
  by_cases z : i = 0
  · subst i
    simp
  · by_cases hi : 6 ≤ i <;> simp [z,hi]
theorem flags_or (r : Rows) (p q : Mask→Bool) :
    flags r (fun x => p x || q x) = flags r p ||| flags r q := by
  induction r with
  | nil => simp [flags]
  | cons x r ih => simp only [flags,ih,digit_or]
theorem flags_xor (r : Rows) (p q : Mask→Bool) :
    flags r (fun x => p x ^^ q x) = flags r p ^^^ flags r q := by
  induction r with
  | nil => simp [flags]
  | cons x r ih => simp only [flags,ih,digit_xor]
theorem flags_join (r : Rows) (a b : Mask) :
    flags r (hit (a ||| b)) = flags r (hit a) ||| flags r (hit b) := by
  rw [← flags_or]
  congr 1
  funext x
  exact hit_add a b x
theorem flags_zero (r : Rows) : flags r (hit 0) = 0 := by
  induction r with
  | nil => rfl
  | cons x r ih => change digit (flags r (hit 0)) _ = 0;rw [ih];simp [digit,hit]
theorem mod_count (r : Rows) (p : Mask→Bool) (short : r.length<63) :
    flags r p % 63 = r.countP p := by
  induction r with
  | nil => rfl
  | cons x r ih =>
    have le := List.countP_le_length (p:=p) (l:=r)
    have h : r.length+1<63 := short
    have remainder := ih (by omega)
    have eq : digit (flags r p) (p x) = (flags r p)*64+(p x).toNat := by
      unfold digit
      rw [← Nat.shiftLeft_add_eq_or_of_lt (by cases p x <;> decide),Nat.shiftLeft_eq]
    change digit (flags r p) (p x) % 63 = _
    rw [eq,List.countP_cons]
    cases v : p x <;> simp only [v,Bool.false_eq_true,ite_false,ite_true,Bool.toNat_false,Bool.toNat_true] <;> omega
theorem survive_flags (r : Rows) (a b : Mask) (short : r.length<63) :
    ((flags r (fun _ => true) ^^^ flags r (hit a)) ||| flags r (hit b)) % 63 = survives a b r := by
  rw [← flags_xor,← flags_or]
  change flags r (fun x => (true ^^ hit a x) || hit b x) % 63 = r.countP (obey a b)
  have hh : (fun x => (true ^^ hit a x) || hit b x) = obey a b := by funext x;simp [obey]
  rw [hh,mod_count _ _ short]

abbrev PortPair := Mask × Nat
def packedEnum (cap : Nat) : List PortPair → Mask → Nat → List PortPair
  | [],a,w => if w % 63 ≤ cap then [(a,w)] else []
  | (v,t)::vs,a,w => if w % 63 ≤ cap then
      packedEnum cap vs a w ++ packedEnum cap vs (a ||| v) (w ||| t) else []
def labelled (r : Rows) (a : Mask) : PortPair := (a,flags r (hit a))
theorem enum_lab (r : Rows) (short : r.length<63) (cap : Nat) (vs : List Mask) (a : Mask) :
    packedEnum cap (vs.map (labelled r)) a (flags r (hit a)) =
      (enumPorts (small r cap) vs a).map (labelled r) := by
  induction vs generalizing a with
  | nil =>
    simp only [List.map_nil,packedEnum,enumPorts,small,decide_eq_true_eq,mod_count _ _ short]
    split <;> rfl
  | cons v vs ih =>
    simp only [List.map_cons,labelled,packedEnum,enumPorts,small,mod_count _ _ short,decide_eq_true_eq]
    split
    · rw [List.map_append,← flags_join,ih,ih]
    · rfl
def columns (r : Rows) := bits.map (labelled r)
def contestants (cap : Nat) (cs : List PortPair) := packedEnum cap cs 0 0
theorem contestant_mem (r : Rows) (short : r.length<63) (cap : Nat) (x : Mask) (ok : small r cap x = true) :
    labelled r x ∈ contestants cap (columns r) := by
  unfold contestants columns
  rw [← flags_zero r,enum_lab _ short]
  exact List.mem_map.mpr ⟨x,enumerate _ _ _ ok,rfl⟩

def keep (u a b : Nat) := ((u ^^^ a) ||| b) % 63
def weak (cap u : Nat) (a b : PortPair) : Bool :=
  (a.1 &&& b.1 != 0) || decide (cap < keep u a.2 b.2) || decide (cap < keep u b.2 a.2)
theorem weak_no {rs rows k a b} (cert : valid rs rows = true) (short : rows.length < 63)
    (dis : a &&& b = 0) (l : Easy edge k (D ((a,b)::rs))) (r : Easy edge k (D ((b,a)::rs))) :
    weak (2^k) (flags rows (fun _ => true)) (labelled rows a) (labelled rows b) = false := by
  have hl := survive_le cert l
  have hr := survive_le cert r
  simp [weak,keep,labelled,dis,survive_flags rows _ _ short,Nat.not_lt.mpr hl,Nat.not_lt.mpr hr]

def rootP := contestants 32 (columns seeds)
def rootU := flags seeds (fun _ => true)
def firstP := rootP.filter (fun a => firstOK a.1)

theorem low_weight {rs rows k a b} (bank : valid rs rows = true) (short : rows.length<63)
    (good : Easy edge k (D ((a,b)::rs))) : rows.length - 2^k ≤ (labelled rows a).2 % 63 := by
  have keep := survive_le bank good
  have off : rows.countP (fun x => !(hit a x)) ≤ survives a b rows := by
    apply List.countP_mono_left
    intro x _ hx
    cases h : hit a x <;> simp_all [obey]
  have sum := List.length_eq_countP_add_countP (l:=rows) (hit a)
  have neg : (fun x => decide (¬hit a x = true)) = (fun x => !(hit a x)) := by funext x;cases hit a x <;> rfl
  rw [neg] at sum
  change _ ≤ flags rows (hit a) % 63
  rw [mod_count _ _ short]
  omega

def childMoves (k : Nat) (rows : Rows) : List (Mask × Mask) :=
  let ps := (contestants (2^k) (columns rows)).filter (fun t => decide (rows.length - 2^k ≤ t.2 % 63))
  let u := flags rows (fun _ => true)
  ps.flatMap (fun a => ps.filterMap (fun b =>
    if a.1.toNat ≤ b.1.toNat ∧ weak (2^k) u a b = false then some (a.1,b.1) else none))

def Block (rs : Rules) (k : Nat) (ab : Mask × Mask) :=
  ¬Easy edge k (D (ab::rs)) ∨ ¬Easy edge k (D ((ab.2,ab.1)::rs))

theorem guided {k rs rows} (cert : valid rs rows = true) (short : rows.length<63)
    (blocks : ∀ p∈childMoves k rows, Block rs k p) : ¬Easy edge (k+1) (D rs) := by
  rintro ⟨a,b,dis,l,r⟩
  have lc : Easy edge k (D ((a,b)::rs)) := restrict l (fun x => (in_cons ..).mp)
  have rc : Easy edge k (D ((b,a)::rs)) := restrict r (fun x => (in_cons ..).mp)
  have go {p q : Mask} (d : p &&& q = 0) (ord : p.toNat ≤ q.toNat)
      (ll : Easy edge k (D ((p,q)::rs))) (rr : Easy edge k (D ((q,p)::rs))) : False := by
    have hp := contestant_mem _ short _ _ (port_small cert rr)
    have hq := contestant_mem _ short _ _ (port_small cert ll)
    have w := weak_no cert short d ll rr
    have mem : (p,q) ∈ childMoves k rows := by
      apply List.mem_flatMap.mpr
      refine ⟨_,List.mem_filter.mpr ⟨hp,decide_eq_true (low_weight cert short ll)⟩,List.mem_filterMap.mpr ⟨_,List.mem_filter.mpr ⟨hq,decide_eq_true (low_weight cert short rr)⟩,?_⟩⟩
      change (if p.toNat ≤ q.toNat ∧ weak _ _ _ _ = false then some (p,q) else none) = _
      rw [if_pos ⟨ord,w⟩]
    rcases blocks _ mem with left|right
    · exact left ll
    · exact right rr
  by_cases ord : a.toNat ≤ b.toNat
  · exact go dis ord lc rc
  · exact go (by rw [BitVec.and_comm,dis]) (by omega) rc lc
theorem valid_of_geom {rs rows} (geom : valid [] rows = true)
    (dom : rows.all (inDomain rs) = true) : valid rs rows = true := by
  simp only [valid,Bool.and_eq_true,List.all_eq_true] at *
  exact ⟨⟨fun x hx => ⟨dom _ hx,(geom.1.1 x hx).2⟩,geom.1.2⟩,geom.2⟩

def rootMoves (a : Mask) (u : Nat) := rootP.filterMap (fun b =>
  if weak 32 rootU (a,u) b = false ∧ orderOK a b.1 = true then some (a,b.1) else none)
theorem root_guided (h : ∀ t∈firstP, ∀ p∈rootMoves t.1 t.2, Block [] 5 p) :
    ¬ Easy edge 6 (fun _ => True) := by
  intro e
  obtain ⟨a,b,g,fa,ord⟩ := canonical e
  have ok : valid [] seeds = true := by decide +kernel
  have len : seeds.length<63 := by decide
  have ap := contestant_mem _ len _ _ (port_small ok g.2.2)
  have bp := contestant_mem _ len _ _ (port_small ok g.2.1)
  have w : weak 32 rootU (labelled seeds a) (labelled seeds b) = false := weak_no ok len g.1 g.2.1 g.2.2
  have mem : (a,b) ∈ rootMoves (labelled seeds a).1 (labelled seeds a).2 := by
    apply List.mem_filterMap.mpr
    refine ⟨_,bp,?_⟩
    change (if weak 32 rootU (labelled seeds a) (labelled seeds b) = false ∧ orderOK a b = true then some (a,b) else none) = _
    rw [if_pos ⟨w,ord⟩]
  rcases h _ (List.mem_filter.mpr ⟨ap,fa⟩) _ mem with left|right
  · exact left g.2.1
  · exact right g.2.2

-- The tables encode negative row banks, possible disjoint comparisons and their proof branches.
-- Row indices occupy nine bits. Each child reference includes the orientation of its comparison.
def rowLookup : Nat := 0xfe03f00fa03e00f603d00f203c00ec03a80e807a00e603900e203801e003780dc03680d803580d4034c0d103380cc03280c807200c603100c303041c103001bc02e80b802d00b202c00ac02a80a806a00a682920a282821a0828019e027089a0260894224c0912244090223088a0220988221a084a212083820a081a606881860608126048810602980a20217c01e007601d027009a016801902600d80260057005801502530144251014024e413104a412114841201464111244410d04241053414905141410434109041404d0124044f003a10e043408c843018c043008a842814a0428049a0248892024088a4209c8262094824208c82220848072018805200c7081a1060c182060414284c4113844c11284481118444110840e103040a10183900c603100c20294087421c08642180854214084420d082420506c01a004e813804c813004a811a04600f403c00e403500d002d00b001fc07e01f407c01ec07a01e407801dc07601d407301c807101bc06e01b406c01ac06a019c0660194062017c05e017405c016c05a0164058015c04f012c04700fc03e00f403b00dc02f007c00f
def maskLookup : Nat := 0x11b02cc05d01b41590c6411e046815c017015805c033004c01500003c0f801e02b817602d816621981a603a886a02a817202c88e221881a20a080ec09b00ac08b04b402d01e4139016406902a402e009823a02a80a204b013805a01a803c003a42e10b042e4013c2cb092c1c30b0c343090c3490f0405e0b1824608182421808020c0bc00f05ac06b08ac14b012c0e3058c063050c01d01b40e50594225081416909a414909240710d842610e84341090438101b804e01d80e601e816a01c807c09902440d8038005e2078a0e216889a23288d822608c8217821e033820e00e80da096805a0a682ca03280520870238096029803a02c80740001d490b60802d416a81a852a88285622588d222088942e40b802a00856881a0d283c22e083822a08b020c08a020960e482a20e080940025415a116905a146911a186921a086941a106901ac12904a4c2b10ad02980ac02900a05c913240c85524548152514845241487122c49312544851264496121848a1248494121049812c0490124189922408b1424c0b1026808a02480b402600b0020ce02380d60558c5611580961458116305841607184c6151814631184461418106301840a034809233084c211085823208482140845c017041c033008c0430c0c10300d4155015431504541250094145011430505c407102c415101441910584061028432105041810c04106064818200d0314006c482e2838c0e2038c263819606b018c06a018c2aa0a882a382ac0a302a80a202862c483062418a011e087830e143810e083831614582160c1813a0c6820a0c4831c147011c087032c08b030c04d07140c505140850324089014414c058616287840e107040c107880e205b01e0070016581960ca4929a424b218c86b012ca2328ac225601582b20486621988c683120c6251c846211a046238196125889624585860618c861218886241828c2230a0c06508940a15485581528c523160c56111845a1128452116045a146051824711123060c1850062882d283620d303640da03480d2194a25889682520956454916245b114c4551164456116845211704538156059815a05a8152058815c05b014c0550164056016805c014a2988a682920a52498926449c126609a824a09c825209d026409a024809c026a21288682128b222cb0b0c2c90b282c20b224c9130e0c9832a0c283220cb030c0c903280c91928642192a242892224b090c24909282459126444912244b110c4451124446112844211304491a2a2828a2428a0a2648c9212488922c4831234489122848212304889824609901240218d823a08c823c08cc43910e843210f043680d203900f803a00f003618686121870614886421e085821c086641c9052418906c413106441e1068412107041518a462618a862218b062508a422e089822a08b022b108c42d10a442e109842a108842c109460e181860a180860c183640c903c40b100c40e1028400670f0203d044b412d40b102d80b402d443110d843410d903380d603700f403500d8035125049582540960250094505641710744151058414105e017007401152914a512844a1c2910a582940a102954215091425909c4251084425c08702740b5026409e0238096021809c02500954845216485121708d5011405901c40d10184004ae02b242e10b882ec0b302e00b818c923848c123808e903240e103880ec03300e06984a412908a60292c2630914249098424e098826c093026061a4849218486221b084c218506301a406e013806c0124aa12a04aa02a852814a342a50aa42890a842a162058ac62318a0629488522a488922848ac22308a142b408d02940a902840a202b008c0285a01680ca252814a292824a212888a0228b0a0c2885227082c22308b420d0894229088422160b180c608180b208c82d203482520a48011b086cb0b0c2c50bc42d10b082d113044c2132c0c303140f103440c6030c6511904642194c24309442713144c41314c44311c4451110c8512108841412c073014c04501c40411a2c2830a542850ac44911245891222c0830254081580c611281c203085420608c4c113004c33104c43110458032044815401500607281d60b182ca0b482c60d1914a451814a0519246091904a411838606281860a282920a190864c583060c1910a44192064029001b000a404980150052046041c0060118062030814088c203109840608a820a10c84121088222068432130c0c100c0486821200e428a0930244042094c051012904840a8428108826211804402104220140070094026043004d042c1090428209a0052018024485101419104441a104840c506044c111044810a182060a48212828a02202580e2018a0c2810a0820a08200022408a027001c033004c0a3048c083029803a0068132044812404a03201480832204882a2028004c902008d1022086021052001501860030c049014406101100c601300540190042031608482140a680980228482122048a042c08b022404210b802c00040230008513000c1061808606c80b204c8032064809206880a207080c2050820102b10d04141280023119044400b40650094069012403100b800e00d82290824016019802601a802a012803209a0248028803c007007400d0054080092001e003801600700680822104000b10003400c201116c2090828200845011100458406104840210504c60012220200b1111003102440a182042810a102904205090430308022048a02a002081100400224098021010a082405880620488142010810219806201900002010304040018008580200d003200500100504204080120208000d00642040842880006840c40424000a83600d0022a0888202008140818806208802100200d00a408600b058000202400240011c043045811204081140c403800114604005a0018100402200a2808000002040088422014000880410204004801120a083000c0860000a046001800c0110b0028000042140844201030020040049200820220060000880014041401019002401a00281180002c00306080820600080002400e04184062018006010800c04104042013100840300000100500808600280014000444800a000224200028140002144000240c00060
def bad0 : Array Nat := #[0xffffffffffe,0xffffffffffd,0xffffffffffb,0xffffffffff7,0xfffffffffef,0xfffffffffdf,0xfffffffffbf,0xfffffffff7f,0xffffffffeff,0xffffffffdff,0xffffffffbff,0xffffffff7ff,0xfffffffefff,0xfffffffdfff,0xfffffffbfff,0xfffffff7fff,0xffffffeffff,0xffffffdffff,0xffffffbffff,0xffffff7ffff,0xfffffefffff,0xfffffdfffff,0xfffffbfffff,0xfffff7fffff,0xffffeffffff,0xffffdffffff,0xffffbffffff,0xffff7ffffff,0xfffefffffff,0xfffdfffffff,0xfffbfffffff,0xfff7fffffff]
def bad1 : Array Nat := #[0xffeffffffff,0xffdffffffff,0xffbffffffff,0xff7ffffffff,0xfefffffffff,0xfdfffffffff,0xfbfffffffff,0xf7fffffffff,0xeffffffffff,0xdffffffffff,0xbffffffffff,0x7ffffffffff,0xc47e00000000000,0x7d00000000000,0x1880000000000000000007b00000000000,0x7700000000000,0x6f00000000000,0x5f00000000000,0x3f00000000000,0x38403f0000000000000,0x3e8000000000000,0x3d8000000000000,0xfb8100000000000,0x378000000000000,0x2f8000000000000,0x1f8000000000000,0x3a00054000000000000001400000000000840100000000000,0x440100000000000,0xe0004000003fe000000000000000,0x1800000000000000000000000003fd000000000000000,0x3fb000000000000000,0x700020000000000003f7000000000000000]
def bad2 : Array Nat := #[0x7ef000000000000000,0x3df000000000000000,0x3bbf008000000000000,0x37f000000000000000,0x2ff000000000000000,0x1ff000000000000000,0x10000000000000000,0x58c80000000000000000000120003040008000000000000,0x3aa800000000000006840008000000000000,0x1840008000000000000,0x3aa800000000000001000000000000000000,0xe0000803ff0000000000000000000,0xbfe8000000000000000000,0x73fd8000000000000000000,0x3fb8000000000000000000,0x1c00020000000003f78000000000000000000,0x7ef8000000000000000000,0x3df8000000000000000000,0x3800100000000000000000003bf8000000000000000000,0x37f8000000000000000000,0x2ff8000000000000000000,0x1ff8000000000000000000,0x100000000000000000000,0x10000000000000000000,0xd540000e0020000000000000000000,0x58c80000000000000000000150020800000000000000000,0x30020000000000000000000,0xd54000010000000000000000000000,0x58c80000000000000000000020000800000000000000000,0xe00000000000ffc00000000000000000000000,0xe0ffa00000001000000000000000,0xe00ff600008000000000000000000]
def bad3 : Array Nat := #[0xfee00000000000000000000000,0x7000000100000000000000fde00000000000000000000000,0xefbe00000000000000000000000,0xf7e00000000000000000000000,0x1efe00000000000000000000000,0xdfe00000000000000000000000,0xbfe00000000000000000000000,0x7fe00000000000000000000000,0x10000000000000000000000000,0x1944400000220c04000000000000000000000000,0x3a00054000000000000001a04000000000400000000000000,0x604000000000000000000000000,0x3a00054000000000000000400000000000400000000000000,0x31800c100c10000000062001000000c000400000001000000000000000,0xd5a000490000001000000000000000,0x6000400000001000000000000000,0xd44000090000000000000000000000,0x19444000002c0200800008000000000000000000,0xdb4000890008000000000000000000,0x60000800008000000000000000000,0xc54000090000000000000000000000,0x1944400000020200000000000000000000000000,0x954000090000000000000000000000,0x554000090000000000000000000000,0xffdefe770ff40a020000e218000000000000000000000000000000000000,0x707fc000000000000008000000000000000,0x67fa000000000000000000000000000000,0x7f6000000000000000000000000000000,0x70000000000800000007ee000000000000000000000000000000,0x1c007de000000000080000000000000000000,0x7be000000000000000000000000000000,0x1f7e000000000000000000400000000000]
def bad4 : Array Nat := #[0x6fe000000000000000000000000000000,0x5fe000000000000000000000000000000,0x3fe000000000000000000000000000000,0x3ab080000000000005000000400000000000,0x880000000000000000000400000000000,0x3ac804000000000005000000000000000000,0x2004000000000000000000000000000000,0x3a2800000000000005000000000000000000,0x31800c100c100000000620060002002000000000008000000000000000,0x3da802000000000005008000000000000000,0x30002000000000000008000000000000000,0x32a800000000000005000000000000000000,0x2aa800000000000005000000000000000000,0x1aa800000000000005000000000000000000,0x1945800020220200000080000000000000000000,0x180a000005000000003400020000000000080000000000000000000,0xc00020000000000080000000000000000000,0x180a000005000000000800000000000000000000000000000000000,0x1940400000220200000000000000000000000000,0xffdefe770ff40a020000e210000001000000000000000000000000000000,0xffdefe770ff40a020000e208000001000000000000000000000000000000,0x31800c100c1000000006c0010000002000200000000000000000000000,0x19a4400000220200200000000000000000000000,0x60000000000000200000000000000000000000,0x1844400000220200000000000000000000000000,0xfffffe7f1ffc1a020000e438010001002000000000000000000000000000,0x31800c100c100000000220010000002000000000000000000000000000,0x1144400000220200000000000000000000000000,0x944400000220200000000000000000000000000,0xffdefe770ff40a020000c218000001000000000000000000000000000000,0xffdefe770ff40a020000a218000001000000000000000000000000000000,0xffdefe770ff40a0200006218000001000000000000000000000000000000]
def bad5 : Array Nat := #[0x700003fe0000000000000002000000000000000000000000,0x33fd0000000000000000000000000000000000000000,0x3fb0000000000000000000000000000000000000000,0x7000000003f70000000010000000000000000000000000000000,0x3803ef0000000000000000000400000000000000000000,0x3df0000000000000000000000000000000000000000,0xfbf0000000000000000000000000000000000000000,0x37f0000000000000000000000000000000000000000,0x2ff0000000000000000000000000000000000000000,0x1ff0000000000000000000000000000000000000000,0x3a00058400000000000001400000000000400000000000000,0x4400000000000000000000000000000000000000000,0x3a00064020000000000001400000000000400000000000000,0x10020000000000000000000000000000000000000000,0x3a00014000000000000001400000000000400000000000000,0x58d00000000000000000000120000802000000000000000,0x80000000000000000000000000002000000000000000,0xffdefe770ff40a000000e218000001000000000000000000000000000000,0x58880000000000000000000120000800000000000000000,0x5b480100000000000000000120400800000000000000000,0x180a000006800100002800000000000000400000000000000000000,0x1800100000000000000000000400000000000000000000,0x180a000001000000002800000000000000000000000000000000000,0x50c80000000000000000000120000800000000000000000,0x48c80000000000000000000120000800000000000000000,0xffdefe770ff408020000e218000001000000000000000000000000000000,0x18c80000000000000000000120000800000000000000000,0xffdefe770ff402020000e218000001000000000000000000000000000000,0x31800c100c600000010620010000002002000000000000000000000000,0x3d00054010000000000001402000000000400000000000000,0x300000010000000000000002000000000000000000000000,0x3200054000000000000001400000000000400000000000000]
def bad6 : Array Nat := #[0x2a00054000000000000001400000000000400000000000000,0x1a00054000000000000001400000000000400000000000000,0xfffffe7f1ff81a020000e638010001002000000000000000000000000000,0x31800c1004100000000620010000002000000000000000000000000000,0xffdefe770fe40a020000e218000001000000000000000000000000000000,0xffdefe770fd40a020000e218000001000000000000000000000000000000,0xffdefe770fb40a020000e218000001000000000000000000000000000000,0xffdefe770f740a020000e218000001000000000000000000000000000000,0xffdefe770ef40a020000e218000001000000000000000000000000000000,0xffdefe770df40a020000e218000001000000000000000000000000000000,0xffdefe770bf40a020000e218000001000000000000000000000000000000,0xffdefe7707f40a020000e218000001000000000000000000000000000000,0x31800c600c100000080620010010002000000000000000000000000000,0x180d000005000080002800010000000000000000000000000000000,0x3000000000080000000010000000000000000000000000000000,0x1802000005000000002800000000000000000000000000000000000,0xffdefe760ff40a020000e218000001000000000000000000000000000000,0xffdefe750ff40a020000e218000001000000000000000000000000000000,0xfffffe7b1ffc1a020000e638010001002000000000000000000000000000,0x318004100c100000000620010000002000000000000000000000000000,0xffdefe670ff40a020000e218000001000000000000000000000000000000,0xffdefe570ff40a020000e218000001000000000000000000000000000000,0xffdefe370ff40a020000e218000001000000000000000000000000000000,0x100a000005000000002800000000000000000000000000000000000,0x80a000005000000002800000000000000000000000000000000000,0xffdefc770ff40a020000e218000001000000000000000000000000000000,0xffdefa770ff40a020000e218000001000000000000000000000000000000,0xffdef6770ff40a020000e218000001000000000000000000000000000000,0xffdeee770ff40a020000e218000001000000000000000000000000000000,0xffdede770ff40a020000e218000001000000000000000000000000000000,0xffdebe770ff40a020000e218000001000000000000000000000000000000,0xffff7e7f1ffc1a020000e638010001002000000000000000000000000000]
def bad7 : Array Nat := #[0x30800c100c100000000620010000002000000000000000000000000000,0xffdcfe770ff40a020000e218000001000000000000000000000000000000,0xffdafe770ff40a020000e218000001000000000000000000000000000000,0xffd6fe770ff40a020000e218000001000000000000000000000000000000,0xffeffe7f1ffc1a020000e638010001002000000000000000000000000000,0x11800c100c100000000620010000002000000000000000000000000000,0xff9efe770ff40a020000e218000001000000000000000000000000000000,0xff5efe770ff40a020000e218000001000000000000000000000000000000,0xfedefe770ff40a020000e218000001000000000000000000000000000000,0xfddefe770ff40a020000e218000001000000000000000000000000000000,0xfbdefe770ff40a020000e218000001000000000000000000000000000000,0xf7defe770ff40a020000e218000001000000000000000000000000000000,0xefdefe770ff40a020000e218000001000000000000000000000000000000,0xdfdefe770ff40a020000e218000001000000000000000000000000000000,0xbfdefe770ff40a020000e218000001000000000000000000000000000000,0x7fdefe770ff40a020000e218000001000000000000000000000000000000]
def badTab : Array (Array Nat) := #[bad0,bad1,bad2,bad3,bad4,bad5,bad6,bad7]
def bad (i : Nat) : Nat := ((badTab[i/32]?).getD #[])[i % 32]?.getD 0
def nsup0 : Array Nat := #[0x80200100400244210a001081241400888980046002600004080000000000,0x80010100000244002a00108024540080098000c002600a04080000000000,0x80200100400004212a00108124140088800104e002600204080000000000,0x80210100400804610a0010812c140088818004e002600004080000000000,0x80010100400244002a00108024540080098000c002600a04080000000000,0x80200100400004212200108124540088818004e002600204080000000000,0x80200100400004212a00108124140088818004e002600204080000000000,0x80200100400004210a00108124540088888004e002600204080000000000,0x802101804008042122001081345400a8888004a002600200080000000000,0x80200080400244212200108124440088898004a002600200080000000000,0x802101804008042122001081344400a8888004e002600200080000000000,0x80200100400004210020108124440088898004e002600204080000000000,0x80200100400004212200108124440088898004e002600204080000000000,0x80210100400844610a0010812c140088808004e002600004080000000000,0x802001004008442522201081340500a9808004f002600200080000020000,0x80200100400044212a00108124140088808004e002600204080000000000,0x80000100000244202a00100124540080098000c802600a04080000000000,0x8020010040084465020010812c040889818104e042600004080000000002,0x80200100400044210a00108124140088818004e002600004080000000000,0x80200100400044212200108124040088818004e002600204080000000000,0x80200100400044212200108124540088888004a002600200080000000000,0x80200100400044212200108124440088888004e002600200080000000000,0x80200100400044212200108124540088888004e002600200080000000000,0x80200100400044210200108124440088898004e002600204080000000000,0x80200100400244212a00108124540000080800e002080a04080000000000,0x80200100400244212a001081245400000980008802080a04080000000000,0x80200100400244212a00108124540000098000e002080a04080000000000,0x80200100400241210a000881201040888180046000600804080000000000,0x802001004002442122001081245400000808008802600a04080000000000,0x80200100400244212a001081245400000808008802600a04080000000000,0x80200100400244212a00108124540000080800e002600a04080000000000,0x80200080400244212a001081245400000980008802600a04080000000000]
def nsup1 : Array Nat := #[0x80200100400244212a001081245400000980008802600a04080000000000,0x80200100400144212200108124440088880804e002600200080000000000,0x80200100400244212200108124540088080804e002200a00080000000000,0x80200080400244212200108124440080880804a002600a00080000000000,0x80200100400244212a00108124540000098004a002200a04080000000000,0x80200080400244212200108124540000080804a002600a04080000000000,0x802101804002c1210a0404022c9100c88180046040680806282040000084,0x80200100400a4421238010812c560028088800a806080a80084100000000,0x80200100400244212200108124440088088004e002080a00080000000000,0x80200100400244212200108124540088088004e002080a00080000000000,0x80200080400244212200108124440088888004a002600a00080000000000,0x80200100400244212a00108124540008088000e002080a04080000000000,0x80200100400244212a00108124540008098000a002080a04080000000000,0x80200080400244212200108124540008088000a002600a04080000000000,0x80200100400244212200108124540008088000a002600a04080000000000,0x80200100400244212a00108124540008088000a002600a04080000000000,0x80200080400b44212280148134450028088004b202200b800a0800000000,0x80200100400244212200108124440088088004e002200a00080000000000,0x80200100400244212200108124540088088004e002200a00080000000000,0x80200080400244212200108124540008088004a002600a04080000000000,0x80000100000200a02900100120520088898004e000600a04080000000000,0x80200100400144212200108124440088888004e002600200080000000000,0x80200100400a442122801081245500208888008806280b80082100000000,0x80200100400244212a001081245400008880008802200a00080000000000,0x80200100400244212200108124440088888004e002200a00080000000000,0x802000804002442122001081244400808880048802600a00080000000000,0x802001004002442122001081245400808880048802600a00080000000000,0x80200100400244212a00108124540000888000e002200a04080000000000,0x80200100400244212a001081245400008980008802200a04080000000000,0x802000804002442122001081245400008880008802600a04080000000000,0x802001004002442122001081245400008880008802600a04080000000000,0x80200100400244212a001081245400008880008802600a04080000000000]
def nsup2 : Array Nat := #[0x80200080400144212200108124440080888004a002600200080000000000,0x80200180400b442122001c8134540020888004a002200a00080000000000,0x80200080400244212200108124440080888004a002600a00080000000000,0x80200100400244212200108124540080888004a002600a00080000000000,0x80200080400244212200108124540000888004a002600a04080000000000,0x80200100400244212200108124540000888004a002600a04080000000000,0x80200080400144212200108124440088888004a002600200080000000000,0x80200080400b4421220014813445002888a000a002200b000a0000000000,0x80200180400b44212200148134540028888000a002200a00080000000000,0x80200100400244212a00108124540008888000a002200a00080000000000,0x80200080400244212200108124540008888000a002600a04080000000000,0x80200100400244212200108124540008888000a002600a04080000000000,0x80200080400244212200108124440008888004a002200a00080000000000,0x80200100400244212200108124540008888004a002200a00080000000000,0x80200100400244212a00108124540008888004a002200a00080000000000,0x80200100400244212a20148120550000180800e802002b16082000008000,0x80000100000200000800148124540088818014e002600a04080000000000,0x80200100400244212a00108100004088898004e000000a04080000000000,0x800001008002804008000c83345648c891c0047a46784a8729c530808480,0x800001084002012108200001245400888180046002600a04080000000000,0x80200100400244212a001081204040888980008802000a04080000000000,0x80200100400244212a00108120404088098004e002000a04080000000000,0x80000100800280404800148024540088818014e002684a07088020000000,0x80200100400244212a00108100140088898004e000000a04080000000000,0x802101004002c4612a00108320d40020198000e002000a04080000000000,0x800001008002804008000c83345648c891cc047246784a8729c530808480,0x80200100400244212a00108120404088898004a002200a00080000000000,0x80200100400244212200108120404088080804e002200a00080000000000,0x80200100400244212a00108120404088080804e002200a00080000000000,0x80200100400244212200108120404088898004e002200a00080000000000,0x800101004002400008800881245400888180046002600a04080000000000,0x80200100400244212a00108124404080880804a002600a00080000000000]
def nsup3 : Array Nat := #[0x80200100400244212a00108120540000080804e002200a04080000000000,0x800001008002804008001487345640e891c0046206684a8708c530808400,0x80200100400244212a00108100004088898004e002200a04080000000000,0x80200080400244212a00108120404000098004a002200a04080000000000,0x80200100400244212a00108120404000098004a002200a04080000000000,0x80200100400244212a00108120540000098004e002200a04080000000000,0x80000108400200052a000000245400888180046002600a04080000000000,0x80200108c00244216a00108500440088898004e000000200080000000000,0x80200100400244212a00108124440088888004a002600200080000000000,0x308100c40008188000a000000a00080000000000,0xa0200100400245212a000000200000000000000002000900000000000000,0x80200000000240000000108100440008088000a000000200080000000000,0x80000100000004200000108100440008088000a000000200080000000000,0xa0200100400245212a000000200000000000000002000800000000000000,0xa1210188c00bc5616ba43d8530c60808188910aa06002b90084900888410,0x80000108400201210a000000245400888180046002600a04080000000000,0x80200100400244212a00108120440088898000a002000a00080000000000,0x80200100400240018b0000002456008881c0047202700b84090400000000,0x80200100400244212a00108120440088088004e002000a00080000000000,0x80200100400244212200108120440088898004e002000a00080000000000,0x80200100400244212a00108120440088898004e002000a00080000000000,0x802101004002c4612a00108320d40028188000e002000a04080000000000,0x108100440008198100a000000a14080000000000,0x108100440008098100a000000a14080000000000,0x80210108400ac4656ba41c850046482819e910aa40002bb72e69188886c8,0x80200100400244212a00108100440088898004e000000a04080000000000,0x802001004002012108200000245400888180046002600a04080000000000,0x80200100400244612a04148120c40828198800a002002a04080000000010,0x80200080400244212a00108120440088898000a002000a04080000000000,0x80200100400244212a00108120440088898000a002000a04080000000000,0x80200100400244212a00108120440088098004e002000a04080000000000,0x80200100400244212a24108100540808098100e040000a14a80000080080]
def nsup4 : Array Nat := #[0x80200100400244212a00108100540088898004e000000a04080000000000,0x80200100400244212a00108120540008098000e002000a04080000000000,0x80210188400ac04048800402bcd6008891c00c7206784b87a9a568a20020,0x80200100400b44212b00148130460028188004a802200a00084000000000,0x80200080400244212200108120440088898004a002200a00080000000000,0x80200100400244212a00108120440088898004a002200a00080000000000,0x80200100400244212200108120440088088004e002200a00080000000000,0x80200100400244212a00108120440088088004e002200a00080000000000,0x80200100400244212200108120440088898004e002200a00080000000000,0x80200100400244212a00108120540008088004e002200a04080000000000,0x80200100400244212a00108100440008098004a002200a04080000000000,0x80200080400244212a00108120440008098004a002200a04080000000000,0x80200100400244212a00108120440008098004a002200a04080000000000,0x8020010840024421228010850404408889a004f200204020080008800000,0x80200100400244212a00108104040088898004e000200020080000000000,0x80200100400244212a001081240400808880048802600020080000000000,0x80200100400244212200108124040088898004e002600020080000000000,0x80200100400244212a801481244500009888008802280b80082100000000,0x80200100400244212a001081244400888980008802200a00080000000000,0x80200100400244212a001081244400808880048802600a00080000000000,0x8000010080020040480019033cd600c891c014ea02684a8708c530808400,0x80200100400244212a00108104040088898004e000200a04080000000000,0x80200080400244212a001081244400008980008802200a04080000000000,0x80200100400244212a001081244400008980008802200a04080000000000,0x80200100400244212a00108104140000898000e000200a04080000000000,0x8000010080028040480018073cd408e899810460467a4a17a8c1b0c4084a,0x80200188400344212200148504040088898004e002200200080000000000,0x80200100400244212a00108104040088898004e002200200080000000000,0x8020008040014421238010812c04008188800ca0067202000c0800000000,0x80200100400244212a00108124040080888004a002600200080000000000,0x80200100400244212200108124040088898004e002600200080000000000,0x80200080400b44212280148134440020888004a002220a80080800000000]
def nsup5 : Array Nat := #[0x80200180400b44212a001c8134440020888004a002200a00080000000000,0x80200080400244212200108124440088898004a002200a00080000000000,0x80200100400244212a00108124440080888004a002600a00080000000000,0x80200100400244212a00108104040000898004a002200a04080000000000,0x80200080400244212a00108124440000898004a002200a04080000000000,0x80200100400244212a00108124440000898004a002200a04080000000000,0x80200100400244212a00108104140000898004e002200a04080000000000,0x80200188400344212200148504440088898004e000200200080000000000,0x80200100400244212a00108104440088898004e000200200080000000000,0x80200180400b44212a00148134440028888000a002200a00080000000000,0x80200080400244212200108124440088898000a002200a00080000000000,0x80200100400244212a00108124440088898000a002200a00080000000000,0x80200100400244212a00108104440008898000a000200a04080000000000,0x80200080400244212a00108124440008898000a002200a04080000000000,0x80200100400244212a00108124440008898000a002200a04080000000000,0x80200100400244212a00108104540008898000e000200a04080000000000,0x80200100400244212b8010810446000888c004a0023202800c0800000000,0x80200100400244212200108104440088898004e002200200080000000000,0x80200100400244212a00108104440088898004e002200200080000000000,0x80200100400244212a00108124440008888004a002200a00080000000000,0x80200100400244212a00108104440008898004a002200a04080000000000,0x80000100000244012a00000024540088898004e002600a04080000000000,0x80000100000a40052a000000245400888980046002600a04080000000000,0x80000100000340002a00000034540088ab89046002e84a3788e1388e0800,0x80200100400244210a00108124540088898004e000000004080000000000,0x80010100000240002a000180245400888980046002600a04080000000000,0x80200100c00804610a001081245400a8800024e006600004080000000000,0x80000100000a41012a000000245400888980046002600a04080000000000,0x80200100000240012a000080245400888980046002600a04080000000000,0x80200100400204212a00108124540088080004e002000a04080000000000,0x80200100400244212a00108124540088080004e002000a04080000000000,0x80010100400240002a000080245400888980046002600a04080000000000]
def nsup6 : Array Nat := #[0x80200100400204212200108124540088880004e002600a00080000000000,0x80000100000a40002a000000245400a88980046002600a04080000000000,0x80000100000a40002a000000245400888980046002600a04080000000000,0x80200100400004212a00108124540088800004e002600204080000000000,0x80200108400204616a0010872c540000080004e006200a04080000000000,0x80200100400204212a00108124540088080004e002200a04080000000000,0x80200100400240052a000000245400888980046002600a04080000000000,0x80000100000240052a000000245400888980046002600a04080000000000,0x80010100400240002a000000245400888980046002600a04080000000000,0x80200100400004210020108124540088888004e002600200080000000000,0x80200100400244210020108124440088898004e002600200080000000000,0x80000100000a41212a000000245400888980046002600a04080000000000,0x80000100000241212a000000245400888980046002600a04080000000000,0x80200100400240012a000000245400888980046002600a04080000000000,0x80000100000a40012a000000245400888980046002600a04080000000000,0x80200100400244212a00108124540088088004e002000a00080000000000,0x80200100400204212020108124440088888004e002600a00080000000000,0x80200100000240052a000000245400888980046002600a04080000000000,0x80200100400244210a00108124540088898004e000000204080000000000,0x80200100400204212a00108120540088088004e002000a04080000000000,0x80200100400204212a00108124540088088004e002000a04080000000000,0x80200100400240002a000000245400888980046002600a04080000000000,0x80200100400004212200108124540088888004e002600200080000000000,0x80200100400204212200108124540088088004e002200a00080000000000,0x80200100400204212200108124440088888004e002600a00080000000000,0x80200100000240002a000000245400888980046002600a04080000000000,0x80200100400004212a00108124540088088004e002200204080000000000,0x80200100400204212a00108120540008088004e002200a04080000000000,0x80200100400204212a00108124540008088004e002200a04080000000000,0x80200100400204212a00108120540088088004e002200a04080000000000,0x80200100400244212a00108124540088808004e000200000080000000000,0x80200100400244210200108124540088898004e000200000080000000000]
def nsup7 : Array Nat := #[0x80200100400244210200108124540088898004e002600000080000000000,0x80000100000244002a000000245400a8898004e002600a04080000000000,0x80200100400244210a00108124540088898000e000200004080000000000,0x80000100000240042a000100245400888980046002600a04080000000000,0x80000100000240042a000000245400888980046002600a04080000000000,0x80200100400244212a00108124540088808004e000200004080000000000,0x80200100400244210a00108124540088898004e000200004080000000000,0x80200100400044210a00108124540088808004e002600004080000000000,0x80000100000240002a000000245400a88980046002600a04080000000000,0x80200100400244212200108124540088898004a002200200080000000000,0x802101804008442122001081345400a8808004e002200200080000000000,0x80000100000240002a000100245400888980046002600a04080000000000,0x80200100400044212200108124540088808004e002600200080000000000,0x80200100400044212a00108124540000808004e002200204080000000000,0x80200100400044212a00108124540088808004e002200204080000000000,0x80000100000244202a000000245400888980046002600a04080000000000,0x80200100400244212a00108124540088888004e000200200080000000000,0x80200100400244210200108124540088898004e000200200080000000000,0x802101804008442102001081344400a8888004e002600200080000000000,0x80200100400044210200108124540088888004e002600200080000000000,0x80200100400244210200108124440088898004e002600200080000000000,0x80000100000241202a000000245400888980046002600a04080000000000,0x80200100400244212200108124540088898000a002200a00080000000000,0x80000100000244002a000000245400888980046002600a04080000000000,0x80200100400244210a00108124540088898000e000200204080000000000,0x80200100400044210a00108104540088888004e000200204080000000000,0x80200100400044210a00108124540088888004e000200204080000000000,0x8020010040004421230010812457000888e004b0023003000e0000000000,0x8020010040004421228010810445008888a004f2022203800a0800000000,0x80200100400044212200108124540088888004e002200200080000000000,0x80200100400044212a00108124540008888004e002200204080000000000,0x80200100400044212a00108104540088888004e002200204080000000000]
def nsup8 : Array Nat := #[0x80000100400240212a000001245400888980046002600a04080000000000,0x80010100400240202a000001245400888980046002600a04080000000000,0x80200100000244212000108124440088898004e002600a00080000000000,0x80200100400240202a000001245400888980046002600a04080000000000,0x80000100400240202a000801245400888980046002600a04080000000000,0x8000010040024020aa000001245400888980046002600a04080000000000,0x80000100400240202a000001245400888980046002600a04080000000000,0x80200000400244212200108124440088898004a002600a00080000000000,0x80000100000204212a00100024540088898004e002600a04080000000000,0x80000100000204002800108124540088898004e002600a04080000000000,0x8000010000020400280018833c540088198004e002600a04080000000000,0x80000100000204012804108124540088098004e002600a04080000000000,0x80200100400244212a001081245400888980046000004004080000000000,0x80000100000204002800148124540088898000e002600a04080000000000,0x80200100400244212a00108124540088802004e000004004080000000000,0x80000108000204012804108124540088098000e002600a04080000000000,0x80200100400244212a00108100140088898004e000004004080000000000,0x80200100400244210a00108124540088898004e000004004080000000000,0x8000010000020400280010a12457008819a000e822700b06094200000000,0x80000100000244002804108124540088098000e002600a04080000000000,0x80200100400244212a001081245400808020046002600004080000000000,0x80010100000244002804108124540088098000e002600a04080000000000,0x80200100400244212a00100124140088802004e002600004080000000000,0x80000108000204012800108124540088098004e002600a04080000000000,0x80200100400244212a001081001400888980046000004a04080000000000,0x80200100400244212a00108100140088898004e000004a04080000000000,0x80200100400244212a000001241400808980046002600a04080000000000,0x80200100400244212a00108124540040802004e002200204080000000000,0x80200100400244212a00108100140088898004e002200204080000000000,0x80000100000a44002800108124540088898000e002600a04080000000000,0x80200188400244212a04000134140080802004e002600304080000000020,0x80200100400044212a00108124540080802004e002600204080000000000]
def nsup9 : Array Nat := #[0x80010100000244002800108124540088098000e002600a04080000000000,0x80200100400244212a00100124140088802004e002600204080000000000,0x80000108400204002800108124540088098000e002600a04080000000000,0x80000100000304002800108134560088198001e802600a06084000000000,0x80200100400244212a00108100000088898004e002200a04080000000000,0x8000010000020400280010a134570088198050e802600a06084200000000,0x80200080400244212a00108024000088898004a002600a04080000000000,0x80200100400244212a00108024000088898004a002600a04080000000000,0x80200100400244212a00100100140088898004e002200a04080000000000,0x80200100400244212a001081245400888180046000600004080000000000,0x802001084002c4212a001c83001400888980046000600004080000000000,0x80200100400241210a001081245400888980046000600004080000000000,0x8000010000020400280014833c540088098000e002600a04080000000000,0x80200100400244212a00108100140088898004e000600004080000000000,0x802101804002c4212a0004032c1400888180046002600004080000000000,0x80200100400244212a00100124140088818004e002600004080000000000,0x80200100400044210a00108124540088818004e002600004080000000000,0x8000010000030400280018832c540088198000e402700b04090000000000,0x80200100400244212a00108100000088898004e000600a04080000000000,0x80200100400b44612a000000240000889980046006600a04080000000000,0x80000100400204202820108124540088098000e002600a04080000000000,0x80200100400244212a001080240000888980046002600a04080000000000,0x80200100400241212a001081001400888980046000600a04080000000000,0x80200100400244212a001081001400888980046000600a04080000000000,0x80200100400244212a00100100140088898004e000600a04080000000000,0x80200100400a44616a001080000000a8998004e002600204080000000000,0x80000108400204002880108124540088098000e002600a04080000000000,0x80200100400244212a00108100000088898004e002600204080000000000,0x8000010000020400280010a134570088198210e802600a06084200000000,0x80000100400204002880108124540088098000e002600a04080000000000,0x80200100400244212a00108024000088898004e002600204080000000000,0x80200100400244212a00100124000088818004e002600204080000000000]
def nsup10 : Array Nat := #[0x80200100400244212200108124000088898004e002600204080000000000,0x80200100400244212a00100100140088818004e002600204080000000000,0x80200100400244212a00000124140088818004e002600204080000000000,0x80200100400044212a00100124140088818004e002600204080000000000,0x80200100400244212a00108000000088898004e002600a04080000000000,0x80200100400244212a00100100000088898004e002600a04080000000000,0x80200100400244212a00108100000088898004e002600a04080000000000,0x80200100400244212a00000024000088898004e002600a04080000000000,0x80200100400241210a001081245400888980046000200004080000000000,0x80200100400244212a001081245400888980046000200004080000000000,0x80000100000304002800108134560088598000e802600a06084000000000,0x802001084002c4210a001c8304140088898004e000200004080000000000,0x80200100400244212a00108104140088898004e000200004080000000000,0x80000100000304002800108124560088198000e822700b06094000000000,0x80200100400244212a001081245400808080046002600004080000000000,0x80200100400244212a00108124140088808004e002600004080000000000,0x80200100400244212a001081245400408980041000200a04080000000000,0x80000100000204202800108124540088098004e002600a04080000000000,0x8000010000020400280018832c540088198004f002700b04090000000000,0x80200100400344212a200080340500808980041002600a04080000020000,0x80200080400244212a001080240400888980041002600a04080000000000,0x80200100400244212a001080240400888980041002600a04080000000000,0x80200100400241212a001081041400888980046000200a04080000000000,0x80200100400244212a001081041400888980046000200a04080000000000,0x80200100400b44212a00148134540040808004a002200200080000000000,0x80000180000304002840108134560088198001e802600a06084000000000,0x80200100400244212a00108124540088808004e002200200080000000000,0x80000100000304002800108134560088198010e802600a06084000000000,0x80000100000304102840108134560088198010e802600a06084000000000,0x80200100400244212a00108124540080808004a002600200080000000000,0x80210088400344212200108034040088898004a002600200080000000000,0x80200100400244212a00108024040088898004a002600200080000000000]
def nsup11 : Array Nat := #[0x80000100200304002840108134560088198010e802600a06084000000000,0x80200100400244212a00108124040088808004e002600200080000000000,0x80200100400244212a00108124540040808004e002200204080000000000,0x80200100400244212a00108104140088808004e002200204080000000000,0x80200100400244212a00008124140080808004e002600204080000000000,0x80200100400044212a00108124540080808004e002600204080000000000,0x80200080400244212a00108004040088898004a002200a04080000000000,0x80200100400244212a00108004040088898004a002200a04080000000000,0x80200100400244212a00008024040080898004a002600a04080000000000,0x80000100000204202900108124540088098000e002600a04080000000000,0x802001084002c4212a001c8304040088818004e000600004080000000000,0x80000100000204002900108124540088198000e002700b04090000000000,0x80200100400244212a00108104040088898004e000600004080000000000,0x80200100400244210200108124540088898004e000600004080000000000,0x80000100000304002800108124560088198000ec02700b06094000000000,0x80200100400244212a001080240400888980046002600004080000000000,0x802001004002442102001081245400888980046002600004080000000000,0x80200100400244212a00108124040088818004e002600004080000000000,0x80200100400044210200108124540088818004e002600004080000000000,0x80200100400244210200108124040088898004e002600004080000000000,0x80200100400241210a001081041400888980046000600004080000000000,0x80200100400244212a001081041400888980046000600004080000000000,0x80200100400244212a00108104140088818004e000600004080000000000,0x80200100400044210a00108124540088818004e000600004080000000000,0x80200100400244210a00108104140088898004e000600004080000000000,0x80200100400244212a00108104140088898004e000600004080000000000,0x80200100400244212a000081241400888180046002600004080000000000,0x80200100400044210a001081245400888180046002600004080000000000,0x80200080400241212a001080040400888980046000600a04080000000000,0x80200100400244212a001080040400888980046000600a04080000000000,0x80200100400244212a000080240400888980046002600a04080000000000,0x80200080400244212200108004040088898004e002600204080000000000]
def nsup12 : Array Nat := #[0x80200100400244212a00108004040088898004e002600204080000000000,0x80200100400244212a00108104040088818004e002600204080000000000,0x80200100400244212200108104040088898004e002600204080000000000,0x80200100400244212a00008024040088818004e002600204080000000000,0x80200080400244212200108024040088898004e002600204080000000000,0x80000100000244002a00108124540088098004e002600a04080000000000,0x80000100000244002a00108124540088898000e002600a04080000000000,0x80000100000244002a00108124540088098000e002600a04080000000000,0x80000100000244012a00108124540088098000e002600a04080000000000,0x80000100100244002a00108124540088098000e002600a04080000000000,0x80010100000244002a00108124540088098000e002600a04080000000000,0x80200100400244212a00108124540088800004e002600004080000000000,0x80000108000244002a00108124540088098000e002600a04080000000000,0x80200100400244212a00108124540080800004e002600204080000000000,0x80000100000244002a00108124540088298000e002600a04080000000000,0x80000100000244002a00148124540088098000e002600a04080000000000,0x80000100400244002a00108124540088098000e002600a04080000000000,0x80000100000244202a00108124540088098000e002600a04080000000000,0x80000100000204212a00108120540088098004e002600a04080000000000,0x80000100000204002800188338540088998004e002600a04080000000000,0x80000100100204002804108120540088898004e002600a04080000000000,0x80200100400244212a001080245400888980000002600a04080000000000,0x80000100000204002800148124540088898004e002600a04080000000000,0x80000100000244002800108120540088898004e002600a04080000000000,0x80010100000244002800108120540088898004e002600a04080000000000,0x80200100400244212a00100124140088800004e002600204080000000000,0x80200100400044212a00108124540088800004e002600204080000000000,0x80200100400244212a00100124540088000004e002600a04080000000000,0x80000100000244002880108120540088898004e002600a04080000000000,0x80200100400244212a00108124540080800004a002600a04080000000000,0x80200100400244212a00000124540080800004e002600a04080000000000,0x80200100400044212a00108124540080800004e002600a04080000000000]
def nsup13 : Array Nat := #[0x80200100400244212a00000024540080898004a002600a04080000000000,0x80000100000204202800108120540088898004e002600a04080000000000,0x80200100400244212a001080240400888980040002600a04080000000000,0x80000100000204202900108120540088898004e002600a04080000000000,0x80200100400244212a001081245400808080040002600a04080000000000,0x80200100400044210200108124540088808004e002600a04080000000000,0x80200100400244212a000081245400808080046002600a04080000000000,0x80200080400241212a001080245400888980000002600a04080000000000,0x80200100400244212a000080245400808980040002600a04080000000000,0x80200100400244212a00008024540080808004a002600a04080000000000,0x80200100400044212200108124540080808004a002600a04080000000000,0x80000100000200000800148124540088898004e002600a04080000000000,0x80000100000200000800148124540088898014e002600a04080000000000,0x80000100000200000800108125544088898804e802e84a27088020000000,0x80000100000200000800108124544088898804e802684a27088020000000,0x80000100000200000800108125544088898804e802684a27088020000000,0x80200100400244212a00108120400088898004e002000a04080000000000,0x80200100400244212a001000244000808980048002600a04080000000000,0x80000100400200200820108124540088898004e002600a04080000000000,0x80200100400244212a001080244000888980048002600a04080000000000,0x80000108000200050800108124540088898004e002600a04080000000000,0x80200100000201010800108124540088898004e002600a04080000000000,0x80200100400244212a00100120540088098004e002000a04080000000000,0x80200100400244212a00108020400088898004a002200a00080000000000,0x80000108400200000880108124540088898004e002600a04080000000000,0x80200100400244212a00108120400088898004e002200a00080000000000,0x80000100400200000880108124540088898004e002600a04080000000000,0x80200100400244212a00108024400088898004a002600a00080000000000,0x80200100400244212a00100124400088880004e002600a00080000000000,0x80200100000240000800108124540088898004e002600a04080000000000,0x80000108400200000800108124540088898004e002600a04080000000000,0x80010100400200000800108124540088898004e002600a04080000000000]
def nsup14 : Array Nat := #[0x80200100400200000800108124540088898004e002600a04080000000000,0x80200100400244212a00108020400088898004a002200a04080000000000,0x80200100400244212a00100120400088098004e002200a04080000000000,0x80200100400244212a00100024400080898004a002600a04080000000000,0x80200100400244212a00100120540000098004e002200a04080000000000,0x80000100000200042900108124540088898004e002600a04080000000000,0x80000100000200000800108124544088898804e802e84a27088020000000,0x80000100000200002900108124540088898004e002600a04080000000000,0x80200100400244212a00108124040088898004e002600000080000000000,0x80200100400244212a001080244400888980008002200a00080000000000,0x80200100400244212a001080244400808880048002600a00080000000000,0x80000100000200200900108124540088898004e002600a04080000000000,0x80200100400244212a001080244400888980048002600a00080000000000,0x80000100000200000800108124540088898014e002600a04080000000000,0x80000100000200a00800108124540088898004e002600a04080000000000,0x80000100000201200800108124540088898004e002600a04080000000000,0x80200100400244212a001080244400888980008002200a04080000000000,0x80200080400244212a001080244400808980048002600a04080000000000,0x80200100400244212a001080244400808980048002600a04080000000000,0x80200080400244212200108024440088898004a002200a00080000000000,0x80200100400244212a00108024440088898004a002200a00080000000000,0x802100804003442122001080244400c0888004a002600a00080000000000,0x80200100400244212a00108024440080888004a002600a00080000000000,0x80200080400244212200108024440088898004a002600a00080000000000,0x80200080400244212a00008024040080898004a002600a04080000000000,0x80200080400244212a00108024440000898004a002200a04080000000000,0x80200100400244212a00108024440000898004a002200a04080000000000,0x80200100400244212a00008104140000898004e002200a04080000000000,0x80000100000244002800108124540088898004e002600a04080000000000,0x80000100400204002800108124540088898004e002600a04080000000000,0x80000100000204202800108124540088898004e002600a04080000000000,0x80000100000204002810108124540088898004e002600a04080000000000]
def nsup15 : Array Nat := #[0x40200080400144212200108114440048888004a002200200080000000000,0x80000100000204202900100120520088094004e002500a04040000000000,0x80000100000204202900100124540088094004e002600a04080000000000,0x80000100000244202a00100124540088098004e002600a04080000000000,0x80000100000204202900100120520088898004e002600a04080000000000,0x80000100000204202900100124540088898004e002600a04080000000000,0x80200100400244212a000080241400808180045002600904080000000000,0x80000100000204202900108120540088098004e002500a04080000000000,0x80000100000204202900108124540088098004e002600a04080000000000,0x80200100400241210a000881241400888180046000600804080000000000,0x80200080000204212100100124540088884004a002600a04080000000000,0x80200100400240010a001081245400888980004200600884080000000000,0x80200080000204212204100124420088885004a002600b00080000000020,0x80200080000204212200100124540088884004a002600a04080000000000,0x80200100400ac1610a040c832c1408808180004810600804280000000080,0x80000100400204202a00100120540088898004e002600a04080000000000,0x80000080000204202100100124540088898004e002600a04080000000000,0x80000100000204202100100124540088898004e002600a04080000000000,0x80200080000104212200100124420088898004e002600204080000000000,0x80200080000204212200100124420088898004e002600a04080000000000,0x80000080000204212200100124540088898004e002600a04080000000000,0x80000100000204212200100124540088898004e002600a04080000000000,0x2000004000412102800080040400008080041000220000080000000000,0x802101804002c1214b8404822c9408d091880450047a0806298000000080,0x80000080000204202100118124540048188004a002600a04080000000000,0x80200080000204212100108124540088888004a002600a04080000000000,0x80000080000244202a00108124540048098004a002600a04080000000000,0x80200080000124212240188134440088888004a202620280080800000000,0x850028802a0325a56364d98532c6c86858d914ba46394bb00fad3a8e8cae,0x80000100200225656264198722c4c8a858990cfa46294bb00bad288a08a8,0x80200080000324212200188124440088888004a002600a00080000000000,0x80000080000204212200108124540048088004a002600a04080000000000]
def nsup16 : Array Nat := #[0x80200080000204212200108124540088888004a002600a04080000000000,0x80200080000104212100108124440088898004e002600204080000000000,0x80000080000204202100108120468088898004f802700b04094000000000,0x80000080000204202100108124540088898004e002600a04080000000000,0x80000100000204202100108124540088898004e002600a04080000000000,0x80200080000104212200108124440088898004e002600204080000000000,0x80000080000204212200108120440088898004e002600a04080000000000,0x80000100000204212200108120440088898004e002600a04080000000000,0x80200100400244012a00108024540080898000c002600a04080000000000,0x80200100400244012a00008024140088818004e002600a04080000000000,0x80200100400240052a000080241400888980046002600a04080000000000,0x80200100400244212a00108124540088080004e002000204080000000000,0x80200100400240012a000180245400888980046000600a04080000000000,0x802101084002c1010a0008806c1400888188046010680806088000000000,0x2000004000410102000080040400088080042000200000080000000000,0x802101084002c1014a0204822c9400ca81c80460007808060da500000000,0x80200100400a44612a00148324540000180000e006000a04080000000000,0x2000004000400102000080040400488088042000280000080000000000,0x2000004000400102000080040400088088042000280000080000000000,0x80210108400ac041caa604c22c954cc891e90472447a4807ada5688a0886,0x80200100400204202a00108124540088080004e002000a04080000000000,0x80200100400204212a00100124540080880004e002600a04080000000000,0x80200100400244210a00008024140088818004e002600814080000000000,0x802101004002c1210a0004822c14008a8188046000680806088000000000,0x80200100400244202a001081245400888980008802000a04080000000000,0x80200080000244212a001001244200808980048802600a04080000000000,0x80200100400244010a000080241400a8818004e002600814080000000000,0x802101004002c4602a00108324d40020198000e002000a04080000000000,0x80200100400240010a000080241400a8898014e000600824080000000000,0x80200100400240052a000180241400888980046000600824080000000000,0x80200100400240052a000080241400888980046000600824080000000000,0x80200100400240012a000180241400888980046000600824080000000000]
def nsup17 : Array Nat := #[0x80200100400244212a001081245400000800008802600a04080000000000,0x22000210000002c5400000804000002600a14880000000000,0x8000018020022424614019012c5600e8080404f242700bb4a90401000040,0x80200100400204202100108124540088080004e002600a04080000000000,0x80200100400240210a000881241400888180046000600804080000000000,0x802001004002042121001081245400808800048802600a04080000000000,0x80200100000204212100100124540088880004e002600a04080000000000,0x80200100400104202a00108124540088080004e002600a04080000000000,0x80200108400224202a8010872c540000080400e002600a86080100000000,0x80200100400244212a00108124540000080000e002600a04080000000000,0x80000180400204206a0010053c540088080004e002600a04080000000000,0x80200100400204202a00108124540088080004e002600a04080000000000,0x80200100400244210a000080241400a8818004e000600804080000000000,0x80200100400244202a001081245400000980008802600a04080000000000,0x80200100400244202a00108124540000098000e002600a04080000000000,0x80000100400244202a00100124540000098000e002600a04080000000000,0x80200100400bc0410a2000802414088889c0047201620884a80400020008,0x80200100400240010a001081245400888980046000600884080000000000,0x80200100400240010a800080241400a889c8046200600886080500000000,0x80200100400244212a00108124540080880004a002600200080000000000,0x80200100400240010a000180245400888980046000600884080000000000,0x80200100400104212200108124540088880004e002600200080000000000,0x20000040004001020000800404000a8088042080280000080000000000,0x80210108400ac0514aa404822c9548ca91e90472c47a4807ada5688a0886,0x80200100400204212200108124540088080004e002200a00080000000000,0x80200108400ac0410a0008812c1400888188046000680806088000000000,0x80200100400204212200108124540080880004a002600a00080000000000,0x80200100400244212a00108124540080880004a002600a00080000000000,0x80200100000204212200100124420088880004e002600a00080000000000,0x80200100400ac0410a000080241400a889c0046200600884080400000000,0x80200100400104212a00108124540088080004e002200204080000000000,0x80200100400240010a001080245400888980046000600884080000000000]
def nsup18 : Array Nat := #[0x80200100400104212a00108124540080880004e002600204080000000000,0x80200100400104212a00100124540088880004e002600204080000000000,0x80200080000244212a00100124420080898004a002600a04080000000000,0x80200100400bc0510a200080241408e88980047000620804a80000020008,0x80200100400244212a00108124540000080004a002600a04080000000000,0x80200100400bc0410a0001802414288889c0046200620804280400000008,0x80200100400104212200108124540088080004e002600a04080000000000,0x80200188400ac0410a0018812c1400888980046000600804080000000000,0x80200100400104212200108124540080880004a002600a04080000000000,0x80200100000104212200100124540088880004e002600a04080000000000,0x80200100400204212244108724540820080004a002680a86080100000010,0x80000180200204216200110534540088080004e042700a04280000000040,0x80200100400204212200108124540088080004e002600a04080000000000,0x80200100400204212200108124540080880004a002600a04080000000000,0x80200100000204212200100124540088880004e002600a04080000000000,0x80200100400104212a00108124540000080004e002600a04080000000000,0x80200100400244212a00108124540000080004e002600a04080000000000,0x80000100400104212a00100124540088080004e002600a04080000000000,0x80200100400104212a00100124540080880004e002600a04080000000000,0x80000100400204212a80100124544000080004e202624aa5080820000000,0x80200100400204212a00108124540000080004e002600a04080000000000,0x80000100400204212a00100124540088080004e002600a04080000000000,0x80200100400244212a000080241400888180046002600904080000000000,0x80200100400240010a000080241500888180147002780906092000000000,0x80200100400240052a000080241400888180046002600904080000000000,0x80200100400244212a00108124540088088004e002000200080000000000,0x80200100400240a12a000080241400888180046000600904080000000000,0x80200180000104212100108134440088888004e002600200080000000000,0x80200100400104212100108124540088888004e002600200080000000000,0x80200100000244212100108124440088898004e002600200080000000000,0x802101004002c1210a0004822c1400888188046000680806088000000000,0x80200100400ac4612a0010812c540008088000a006040a00080000000000]
def nsup19 : Array Nat := #[0x80200100400244202100108124540088898000a002000a00080000000000,0x80210108400ac041cba404822c9548c891e90472447a4807ada5688a0886,0x80200100400204202100108124540088088004e002000a00080000000000,0x80200100400244202100108124540088898004e002000a00080000000000,0x80200080000324212100188124440088888004a002600a00080000000000,0x80200100400204212100108124540088888004a002600a00080000000000,0x80200080000244212100108124440088898004a002600a00080000000000,0x80200100000204212100108124440088888004e002600a00080000000000,0x80200100400244012a000080241400888180046002600904080000000000,0x80200100400240010a0004822c1400888180147002700904090000000000,0x80200100400244202a00108124540088898000e002000204080000000000,0x80200100400244212a00108124540088088004e002000204080000000000,0x802101084002c1014a0204822c9400c891c80460047808060da500000000,0x80210100400224202a2010832cd40008188000e802040a14080000008000,0x80200100400244212a00108124540008088000e002000a04080000000000,0x80000180400324202a00188122560088088004e002040a14880000040000,0x80200100400204202a00108124540088088004e002000a04080000000000,0x802101004002c4210a0004822c1400c88180046002600804080000000000,0x80200100400244202a00108124540088898000a002000a04080000000000,0x802101004002c4202a00108324d40028198000a002000a04080000000000,0x80200100400244202a00108124540008098000e002000a04080000000000,0x802101004002c4212b0004822c1400888180047000700804090000000000,0x8000010000010420210010813454008808c004e002600a24080010000000,0x80200100400104202100108124540088088004e002600a04080000000000,0x80200080000104212100108124540088888004a002600a04080000000000,0x8000010000020420210010813454008808c004e002600a24080010000000,0x80200100400204202100108124540088088004e002600a04080000000000,0x80200100400104202a00108124540008088000e002600a04080000000000,0x80000100400104202a00108124540088088004e002600a04080000000000,0x80000100400204202a00108124540008088000e002600a04080000000000,0x80200100400204202a00108124540008088000e002600a04080000000000,0x80000100400204202a00108124540088088004e002600a04080000000000]
def nsup20 : Array Nat := #[0x80200100400244202a00108124540008098000a002600a04080000000000,0x80000080000244202a00108124540008098000a002600a04080000000000,0x80000100400244202a00108124540008098000e002600a04080000000000,0x104212200000000000008088004a002200200080000000000,0x80200180c001242122401c833cd50028088004b2022003800a2900020800,0x80200180400b44212a001c8134540028088004a002200200080000000000,0x80210108400bc0414aa404823c9548c891e90472447a4847ada5688a0886,0x802001004001042122001081345400e8088004e002200200080000000000,0x80200100400244212a00108124540088088004e002200200080000000000,0x80200100400104212200108124540088888004a002600200080000000000,0x80200080000244212200108124440088898004a002600200080000000000,0x80200180000104212200108134440088888004e002600200080000000000,0x80200100400104212200108124540088888004e002600200080000000000,0x80200100000244212200108124440088898004e002600200080000000000,0x80210188400ac0414aa404822c9548c891e90472447a4807ada5688a0886,0x802001804002242122401c8134540008088804a006200a80080100000000,0x80200100400244212a00108124540008088004a002200a00080000000000,0x80210108400ac0414aa404822c9548c891e90472447a4807ada5688a0886,0x80200100400204212200108124540088888004a002600a00080000000000,0x80200080000244212200108124440088898004a002600a00080000000000,0x80200100000204212200108124440088888004e002600a00080000000000,0x80200100400104212a00108124540008088004e002200204080000000000,0x80200100400244212a00108124540008088004e002200204080000000000,0x80000100400104212a00108110540088088004e002200204080000000000,0x80200100400104212a00108124540088088004e002200204080000000000,0x80000100400204212a00108120540008088004e002200a04080000000000,0x80000100400204212a00108120540088088004e002200a04080000000000,0x80200100400104212200108124540008088004a002600a04080000000000,0x80000100000104212200108124540088088004e002600a04080000000000,0x80200080000104212200108124540088888004a002600a04080000000000,0x80000080000204212200108124540008088004a002600a04080000000000,0x80200100400204212200108124540008088004a002600a04080000000000]
def nsup21 : Array Nat := #[0x80000100000204212200108124540088088004e002600a04080000000000,0x80000100400204212a00108124540008088004e002600a04080000000000,0x80000080000244212a00108124540008098004a002600a04080000000000,0x80200100400240052a000080245400888180046002600a04080000000000,0x80200100400240010a000080245400888180046002600a04080000000000,0x80200100400240010a000880245400888180046002600a04080000000000,0x80200100400241010a000080645400888180046002600a04080000000000,0x80200100400240090a000880245400888180046002600a04080000000000,0x80200100400240010a00008024540088818014e002600a04080000000000,0x80200100400240010a000881245400888180046002600a04080000000000,0x80200100400240010a000081245400888180046002600a04080000000000,0x80200100400241210a000080245400888180046002600a04080000000000,0x80200100400244010a00008024540088818004e002600a04080000000000,0x80200100400240050a000080245400888180046002600a04080000000000,0x80200100400241010a000880245400888180046002600a04080000000000,0x80200100400240010a000085245400888180046002600a04080000000000,0x80200100400244212a00108124000088898004e002600200080000000000,0x80200100000244212200108124400088898004e002600a00080000000000,0x80200100400240010a001081245400888180046002600a04080000000000,0x80200100400244212a00108120400088898004a002200a04080000000000,0x80200100000244212a00108120400088898004e002200a04080000000000,0x80200100400240010a001080245400888180046002600a04080000000000,0x80000100400244212a00100120540088098004e002200a04080000000000,0x80200100400240010a000080245400888180146002600a04080000000000,0x80200100400244212a00108124540088898000a002000a00080000000000,0x80200100400240210a000080245400888180046002600a04080000000000,0x80200100400244012a000080245400888180046002600a04080000000000,0x80200100400244212a00108100540088898004e000000204080000000000,0x80200100400244202a00108120540088898000e002000a04080000000000,0x80200100400244210a000080245400888180046002600a04080000000000,0x80200100400244212a00108124540088898000a000000a04080000000000,0x80200100000244202a00108120440088898004e002000a04080000000000]
def nsup22 : Array Nat := #[0x80200100400244010a000080245400888180046002600a04080000000000,0x80200100400244202a00108124540088898000e000000a04080000000000,0x80200100400241010a000080245400888180046002600a04080000000000,0x80000100400244202a00108120540088098004e002000a04080000000000,0x80200100400244212a00108100440088898004e002200200080000000000,0x80200100000244212200108120440088898004e002200a00080000000000,0x80200080000244212a00108100440088898004a002200a04080000000000,0x80200100400244212a00108100440088898004a002200a04080000000000,0x80200100000244212a00108100440088898004e002200a04080000000000,0x80200080000244212a00108120440088898004a002200a04080000000000,0x80000100000244212a00108120440088098004e002200a04080000000000,0x80200100400244212a00108100540008098004e002200a04080000000000,0x80000100400244212a00108120540008098004e002200a04080000000000,0x80200100400240012a000080245400888980046002600a04080000000000,0x200000400044232a00008024540088818004e002600a04080000000000,0x80200100400244212a00108120100088898004e000400804000000100000,0x200001400044212200008024540088818004e002600a04080000000000,0x200000400044212200008924540088818004e002600a04080000000000,0x80200100400244212a00100120500088090004e002400a04000000100000,0x200000400044212200088124540088818004e002600a04080000000000,0x10200000400044212200088024540088818004e002600a04080000000000,0x200000400044212200488024540088818004e002600a04080000000000,0x200040c00044212200008024540088818004e002600a04080000000000,0x600000c00044212200008024540088818004e002600a04080000000000,0x200010c00044212200008024540088818004e002600a04080000000000,0x200100400044212200008124540088818004e002600a04080000000000,0x200020400044212200008024540088818004e002600a04080000000000,0x80200100400244212a00108120100088898004e000400a04080000000000,0x200000400044212200108124540088818004e002600a04080000000000,0x200000400044212200008024540088818004e002600a04080000000000,0x80200100400244212a00100120500088098004e002400a04080000000000,0x80200100000244202a00108120500088898004e002400a04080000000000]
def nsup23 : Array Nat := #[0x200040400044212200008024540088818004e002600a04080000000000,0x20200000400044212200088024540088818004e002600a04080000000000,0x201000400044212200008064540088818004e002600a04080000000000,0x600000400044212200008024540088818004e002600a04080000000000,0x40200000400044212200108024540088818004e002600a04080000000000,0x200000400044212200908024540088818004e002600a04080000000000,0x80200100400244202a00108120140088898004e000400a04080000000000,0x80000100400244202a00100120540088098004e002400a04080000000000,0x200100400044212a00008024540088818004e002600a04080000000000,0x10200080400044212200008024540088818004e002600a04080000000000,0x200880400044212200008024540088818004e002600a04080000000000,0x80200100000244202800108120540088898004e002400a04080000000000,0x202000004000c4212200008024540088818004e002600a04080000000000,0x201000400044212600008024540088818004e002600a04080000000000,0x10200000400044212200008024540088818004e002600a04080000000000,0x20200100400044212200008024540088818004e002600a04080000000000,0x201100400044212200008024540088818004e002600a04080000000000,0x40200080400044212200008024540088818004e002600a04080000000000,0x2000004000442122008080a4540088818004e002600a04080000000000,0x80200100000244202a00108120540088898004e000400a04080000000000,0x80000100000244202a00108120540088098004e002400a04080000000000,0x20200000400044212200008024540088818004e002600a04080000000000,0x40200000400044212200008024540088818004e002600a04080000000000,0x80200100400244212a00108120540088098000e000400a04080000000000,0x80000100400244202a00108120540088098004e002400a04080000000000,0x201100400041210a0010810c54000888800ce000600204080000000000,0x600000c000c0010a0010810c540009898000a000600204080000000000,0x22001004000c0210a00108104540018898000e000200204080000000000,0x80200100000204212900100124500088890004e002600a04010000000000,0x802001000002442029001080201000888980045002500904010000000000,0x80400001210204000104440800000004a040200200080000000000,0x41210200000000000048888004a800280200080000000000]
def nsup24 : Array Nat := #[0x80400000200200108100440808088000a040000200080000000000,0x60000300108106460008088000a000300200080000000000,0x108100440048888804a800200200080000000000,0x2000004000400102000180044500008880000000200200080000000000,0x2000004000400102000080044500008880000000200200080000000000,0x102108884208612103a615850647486888e904ba403e42b00ee93a8e8fff,0x80200100000244202900108020500088898004d002500a04010000000000,0x80000180800384202900190338d08089191004e002500a04010000000000,0x80200100000204212900100024500080890004d002600a04010000000000,0x202100004000c109020010810c440888898804a8006a0200388000000008,0x80000180400304202b00100130560080091004e202500aa5080410000000,0x2020010040004121020010810c540088888004e000600200880000000000,0x80200100000244202a00108020500088898004d002500a04080000000000,0x80000100000244202a00100120500088098004e002500a04080000000000,0x800001808003c5602b00100238d080e119a004d006500a17884008010000,0x80000100400244202a00100120540080098004e002500a04080000000000,0x80000100400244202a00100120540088098004e002500a04080000000000,0x202001004000c1210a00108104440088898004e000200201080000000000,0x80200100000204212900100024540080890004d002600a04080000000000,0x800001808003852069001006bcd500c0191004d002700a25a80004020040,0x80000180400204206a0010053c540080090004e002600a04080000000000,0x80000100000244202a00100024540080098004d002600a04080000000000,0x80000100400244202a00100124540080098004e002600a04080000000000,0x80200100000244212a00108020100088898004e002600a04080000000000,0x202001004000c0010a0010810c540088898000e000600204080000000000,0x80200100000204212a00100024500080890004e002600a04080000000000,0x80200100000204212a00100124500088890004e002600a04080000000000,0x442100804001400102008400142002448420000000200040000000000020,0x442100804001400102008400942100448000000100200000000000020000,0x442100804001400102008400940010448020000100200000000008000000,0x442100804001400102008400942100408000000000200040002000000000,0x50800080000100000000190112400048484000a000010200000000000040]
def nsup25 : Array Nat := #[0x50800080200100000000190112420048480080a000010200000000040000,0x50800080200120000040190110402048484000a000000200000010000000,0x50800080200100000040190112420048080000a000000200004000000000,0x54a12aa86b29601112e49d9596677b6ccce981ab412b42f00ee73a8e8cfe,0xa00001000002800008001000285000800900004000400884000000000000,0x80000000000004212200000020000080000004a002600200080000000000,0xa00001000002800008001000285000800900004000400804000000000000,0xa0000180800387616b20110638d080f0191004e846704ab7a840380e0040,0x80000100800284212a00180128500088090004e002600a04080000000000,0x80000180400204216a00100538540080090004e002600a04080000000000,0x80000180000344212b001000305080e0098004e806600a06084000000000,0x80000100000244212a00100120500088098004e002600a04080000000000,0x80000100400244212a00100120540080098004e002600a04080000000000,0x80000180000304216a00100434540080091004e042700a04280000000040,0x80200100000204212a00100024540080890004e002600a04080000000000,0x80000100400204212a00100124540080090004e002600a04080000000000,0x80000100000244212a00100024540080098004e002600a04080000000000,0x204100400044216a00108124540008888000a002200a02080000000000,0x202001004000c1210a8414810c540808888802a040200202180100000080,0x80200100000244202900108020500088898004e002600a04080000000000,0x80000100000204202900100120500088898004e002600a04080000000000,0x80200100000204212900100024500088898004e002600a04080000000000,0x4020008040014421230010811447000888e000a0022003000e6018060060,0x802001000002442029001080201000888980046002600904080000000000,0x8000018000030420290010003050808889c004e202700a94880400040000,0x80210188c0084461020414873cd7482888e900a0462042204e6002066416,0x80200100000244202a001080201000888980046002600a04080000000000,0x800001000003c4602a001000205000a8898004e006600a04080000000000,0x80200100000244202a00108020500088898004e002600a04080000000000,0x80000100000244202a00100120500088898004e002600a04080000000000,0x800001808003c4606a040002389080c899e90c6046604a27a8f0180f0064,0x800001808003846069000002bcd700c995e00c62066a4a87a8f63c020020]
def nsup26 : Array Nat := #[0x80000100000204202900100024540088898004e002600a04080000000000,0x80000100000244202a00100024540088898004e002600a04080000000000,0x80000100400244202a000001245400888980046002600a04080000000000,0x80210188400bc0414a201c833cd7482898e100aa052a0a120e66c0808808,0x80000100000384612a001000205000a8898004e006600a04080000000000,0x80000100000204212a00100120500088898004e002600a04080000000000,0x80200100000204212a00100024500088898004e002600a04080000000000,0x4212200000000000008808004a802280200080000000000,0x80000180800384612b240002389080d991e104fa467a4b37a8fe380804e2,0x80000100000244212a20000020100088898904e802680a16888000080000,0x80000100000244212a00100020500088898004e002600a04080000000000,0x80000100000244212a00100120500088898004e002600a04080000000000,0x80000100000204212a00000024540088818004e002600a04080000000000,0x80000100000244212a00000024540088898004e002600a04080000000000,0x80200100400240010a00108124540088898000e000600a04080000000000,0x200100400044212a00108104540008888004e002200204080000000000,0x220000c000c4212a00108104540008898004a002200204080000000000,0x80200100000244210800108124100088898004e002600804000000000000,0x2000084008400000011085044400288880000008020080000000000008,0x2000084008400000081085044400288880000200020000000000000800,0x2000084008400000801085044400288880000200001000000000800000,0x2000084008400000801085044400288880000080008080000100000000,0x210000400044a122000400040002008020140022200100000000000020,0x210000400044a122000400040100008000541002200008000000020000,0x210000400044a122000400040010008020141002200000000008000000,0x210000400044a122000400040100008000140402200100002000000000,0x31800c600c64a123ad1f8506475a28c8e954beea3ad3b80ee93a8e8cfe,0x80200100000244012800108024500088898004c002600a04000000000000,0x80200100000204212800100124500088890004e002600a04000000000000,0x80200100000244012800108024540088898004c002600a04080000000000,0x1020008040006421238410810447084888e804ba423a03800ee9188608e8,0x802001882003840168401406bcd40080991004c102604a25080000000000]
def nsup27 : Array Nat := #[0x2020010040004421228010810445008888a004f2022203800a0800000000,0x1020008040004421238410810447084888e804ba423a03800ee9188608e8,0x202001004000c4212a0010810c540008888004a002200202080000000000,0x600000c000c4212a0010810c540008888004a002200202080000000000,0x22001004000c4212a00108104540008888004a002200202080000000000,0x80200100000244012800108024500088898004e002600a04080000000000,0x80200100000204212800100124500088898004e002600a04080000000000,0x40200080400144212200108114440008888004a002200200080000000000,0x80200100000244210800108124100088898004e002600804080000000000,0x102100884000642123a410850647480888e904ba423a43b00ee9388e08e8,0x80000180800304202840100130508088898004e002600a04080000000000,0x80200100000204012800100024500088898004e002600a04080000000000,0x80200100000244012a00100024500088898004e002600a04080000000000,0x202001004000e4212b8010810446000888c004a0023202800c0800000000,0x80000100000204202800100124540088898004e002600a04080000000000,0x80200100000204012800100024540088898004e002600a04080000000000,0x4020008040014421238010810447000888e004b2023203800e6918860868,0x800001000002840028001002bc540088998004e002600a04080000000000,0x80000100000340102a000000b45400888989046002684a3788e1388e0800,0x80000100000244002a00100024540088898004e002600a04080000000000,0x802001000002442129001080245000888980048002600a02001000000000,0x220000c000c0010a00108104540088898004e000600204080000000000,0x200000410140a12200108104440088898004e000600204080000000000,0x200280400040a12200108104440088898004e000600204080000000000,0x80200100000204212900100124100088810004e002600904001000000000,0x20000840004001028450858647488889e90cfa407a42a52e8f3a868cfe,0x200880400041210200108104440088898004e000600204080000000000,0x80200100400244212a00108020500088898000c002400a04001000000000,0x80000180800384646900190738d080e9190004e006440a25001000000000,0x80200100000244202900108120500088898004e002400a04001000000000,0x1200080400040290204108104440888898004e000600204280000000080,0x80200100400244212a00100024500080890004c002600a04001000000000]
def nsup28 : Array Nat := #[0x80200100000204212900100124500088890004e002600a04001000000000,0x8200000400240812200108104c40088898004e000600a04080000000000,0x4200000400140812200108104440088898004e000600204080000000000,0x80200100400204212a001081245400808100046002600904080000000000,0x8200100400040a10200108104d40088898004e000600204080000000000,0x200500400040a10200108104d40088898004e000600204080000000000,0x22001004000402102041081045c0888898004e000600204280000000080,0x80200100000244212a001080245000888980048002600a04080000000000,0x40200080400044210200108114440088898004e002600204080000000000,0x202080400044210200108114440088898004e002600204080000000000,0x4200080400040a10200108104440088898004e000600204080000000000,0x80200100000244212a001080241000888980044002600a04080000000000,0x10200080400041210200108104440088898004e000600204080000000000,0x80210180400bc4612a20100238d080a0198000c406440a14880000001000,0x80200100400244212a00108020500088898000c002400a04080000000000,0x800001800003c4202a00100138508088098004e002440a04080000000000,0x80200100000244212a00100024500080898004c002600a04080000000000,0x80200100400244212a00100024500080898004c002600a04080000000000,0x280000c00240012a00108104440088898004e000600204080000000000,0x80200100000204212900100124540088880004e002600a04080000000000,0x40200080400144212200108104440088898004e000600204080000000000,0x202080400044212200108104440088898004e000600204080000000000,0x4200080400140a12200108104440088898004e000600204080000000000,0x80200100000204212900100124540088810004e002600a04080000000000,0x80200100000244202900108024540088898000c002600a04080000000000,0x80000100000204202900100124540088090004e002600a04080000000000,0x80200100000204212900100024540080890004c002600a04080000000000,0x80200100400204212a00100124540088800004e002600a04080000000000,0x40200000400144012200108104440088898004e000600204080000000000,0x80200100400204212a001081245400808100046002600a04080000000000,0x40200080400044210200108104440088898004e000600204080000000000,0x80200100000244202a001080245400888980004002600a04080000000000]
def nsup29 : Array Nat := #[0x80200100000244202a00108024540088898000c002600a04080000000000,0x80200100000244212a00100024540080898004c002600a04080000000000,0x80000100400244202a000001245400800980006002600a04080000000000,0x22001004000c0010a00108104540088898004e000600204080000000000,0x40200080400140010200108114440088898004e000600204080000000000,0x4200080400140010200108104440088898004e000600204080000000000,0x80200100000204212a00100124100088810004e002600a04080000000000,0x1021008040006001024410810647088889e804f8407a42842e871a06808c,0x80200100400244212a00100020500080090004e002600a04080000000000,0x80200100400244212a00100024500080890004e002600a04080000000000,0x8200000400240010200108104c40088898004e000600a04080000000000,0x80200188400204216a00000334940080810004e002600a04080000000000,0x80000100400204212a00100120540088090004e002600a04080000000000,0x80200100400040010200108124540088898004e000600204080000000000,0x204100400040010200108124540088898004e000600204080000000000,0x8200100400040010200108104d40088898004e000600204080000000000,0x80200100000244212a00108024100088898004a002600a04080000000000,0x80200100000244212a00100024500080898004a002600a04080000000000,0x40200080400040010200108114440088898004e000600204080000000000,0x80200100000b44612a00000024100080998004e006600a04080000000000,0x80000180000344212b001000305080a0098004e806600a06084000000000,0x80200100400244212a00100020500080098004e002600a04080000000000,0x80200100000244212a00100024500080898004e002600a04080000000000,0x80200100400240010a00108104440088898004e000600204080000000000,0x8200100400240010a00108104440088898004e000600204080000000000,0x80200100000204212a00100124540088800004e002600a04080000000000,0x22001004000c0010a00108104440088898004e000600204080000000000,0x80200100000204212a00100124540088880004e002600a04080000000000,0x40200080400140010200108104440088898004e000600204080000000000,0x80200100000204212a00100124540088810004e002600a04080000000000,0x80000180000304216a00100434540080090004e042700a04280000000040,0x80200100400244212a00100024540080090004e002600a04080000000000]
def nsup30 : Array Nat := #[0x80000100000204212a00100124540088090004e002600a04080000000000,0x8020000840024001560010850447008889e804f8007806040e871a000070,0x80200100400204212a00000124540080800004e002600a04080000000000,0x80000100400204212a04000124544880010004e042604a25280020000080,0x80200100400204212a00000124540080810004e002600a04080000000000,0x80000100400204212a00100124540088090004e002600a04080000000000,0x802101804000400102041c830447088889e804f8407a42042e871a06808c,0x80200100000244212a00000024540080898004a002600a04080000000000,0x80200100000244212a00100024540080898004a002600a04080000000000,0x80000100000244212a00000024540080098004e002600a04080000000000,0x80200100000244212a00000024540080898004e002600a04080000000000,0x80000100400244212a00000124540000098004e002600a04080000000000,0x80000100400244212a00000124540080098004e002600a04080000000000,0x200000400044212200108104440088898004e002600204080000000000,0x200000400044232a00108104440088898004e002600204080000000000,0x80200100400244212a001081245400808800048002600a02000000000000,0x2000004000c4212a00108104440088898004e002600204080000000000,0x200001400044212200108104440088898004e002600204080000000000,0x200000404044212200108104440088898004e002600204080000000000,0x200080400044212200108104440088898004e002600204080000000000,0x2000004010c4212200108104440088898004e002600204080000000000,0x10200000400044212200108104440088898004e002600204080000000000,0x80200100400204202a00108124540088090004e002400a04080000000000,0x200000440044612200108104440088898004e002600204080000000000,0x4200080400044212200108104440088898004e002600204080000000000,0x200000420044212200108104440088898004e002600204080000000000,0x1200080400044212200108104440088898004e002600204080000000000,0x8200000400044212200108104c40088898004e002600204080000000000,0x200000440044212200108104440088898004e002600204080000000000,0x80200100400244202a00108124540080098000e002400a04080000000000,0x80200100400244212a001081245400808800048002600a04080000000000,0x200100400044212a00108104440088898004e002600204080000000000]
def nsup31 : Array Nat := #[0x240000400144212200108104440088898004e002600204080000000000,0x10200080400044212200108104440088898004e002600204080000000000,0x80200100400244212a00108124540080090000c002600a04080000000000,0x80200100400204202800108124540088090004e002600a04080000000000,0x80200100000204212800100124540088890004e002600a04080000000000,0x280000400244212200108104440088898004e002600204080000000000,0x202000004000c4212200108104440088898004e002600204080000000000,0x6000004000c4212200108104440088898004e002600204080000000000,0x22000004000c4212200108104440088898004e002600204080000000000,0x80000100400204202a00100124540088090004e002600a04080000000000,0x80200100400044212200108104440088898004e002600204080000000000,0x8200100400044212200108104440088898004e002600204080000000000,0x20200100400044212200108104440088898004e002600204080000000000,0x80200100400244212a001081245400000980008002600a04080000000000,0x600000c00044212200108104440088898004e002600204080000000000,0x2200100400044212200108104440088898004e002600204080000000000,0x80200100000244012a001080245400888980048002600a04080000000000,0x40200080400044212200108104440088898004e002600204080000000000,0x80200000400044212200108104440088898004e002600204080000000000,0x20200000400044212200108104440088898004e002600204080000000000,0x40200000400044212200108104440088898004e002600204080000000000]
def nsupTab : Array (Array Nat) := #[nsup0,nsup1,nsup2,nsup3,nsup4,nsup5,nsup6,nsup7,nsup8,nsup9,nsup10,nsup11,nsup12,nsup13,nsup14,nsup15,nsup16,nsup17,nsup18,nsup19,nsup20,nsup21,nsup22,nsup23,nsup24,nsup25,nsup26,nsup27,nsup28,nsup29,nsup30,nsup31]
def nsup (i : Nat) : Nat := ((nsupTab[i/32]?).getD #[])[i % 32]?.getD 0
def sensor0 : Array Nat := #[0x2100085008500102ad04a005055a00a0ab6000002af0000aab6aaaafbf,0x19c540466c2a0acda0aad80002b00ccdb3dccfdf,0xddc1f1cd7368735005af0e3cef0def,0x5ada336000000000000000016bc72bc63380ff03f0ff6f7,0x3eff8e0000000000077f8bdeffffc00ff8fa,0x3e0007fc70000000000001dfe000000000fe73ffffff000fc,0x180e00000700bf800038017f0000000007f80000007cfffffffff00,0xaa4a555284928a424c002002289800911100084004400c07f00000000000,0xcc8c666309230c847000b11430e001201e00108007800ff8000000000000,0xf0f0787c0e3c0f078000c6183f0001c1e0001f0007fff000000000000000,0xff007f800fc00ff80000f81fc00001fe00001ffff8000000000000000000,0xffff80000ffff0000000ffe0000001ffffffe00000000000000000000000,0xfffffffff00000000000fffffffffe000000000000000000000000000000,0xffffffffffffffffffff0000000000000000000000000000000000000000]
def sensorTab : Array (Array Nat) := #[sensor0]
def sensor (i : Nat) : Nat := ((sensorTab[i/32]?).getD #[])[i % 32]?.getD 0
def nodeN : Nat := 1013
def rowN : Nat := 240
def portWidth : Nat := 11
def childWidth : Nat := 14
def bk0 : Array Nat := #[0x1dee56c33982be5d2d560ab54a712e9046a2908823b9ccde6b3419cb4562a9248c45190ae0,0x3bdc0d860af974ad55aa5389746a290c84411dcd6683395cac49231147639190add,0xef72b619cba5aac15aab54a712e9046a2908823b9ccde602d15cac55249188a39190adf,0x77b95b0ce5d2d560ab54a712e9046a2908823b9ccde6833968ae562a9248c45190ade,0x381b0ce5aaad52974821104733419cac55190ad1,0x30d6cb5582ad5273379a0ce5a2b1548c45190ad1,0x3959cb055aa52e8b45211046f3419c8c45190ad1,0x77b81b0ce60af974ad55aa5389746a290c84411dcd6683395cac49231147639190ade,0x1dee56c33974b5582b5529c4ba411a8a432110477399bcd0672d15cac55249188a39190ae0,0x1dee56c33974b5582b556a94e25d208d452110477399bcd0672d15cac55249188a39190ae0,0x1dee56c33974b5582ad529c4ba411a8a432110477399bcd6672d15cac55249188a39190ae0,0x77b95b0ce5d2d560ad54a712e9046a290c84411dce66f3599cb4572a9248c451c8ade,0x30d6ab056aa4ea73379acce5a2b95492451c8ad1,0x381aece5aab5529c4ba410c82399acce551c8ad1,0x3959cb056aa52e8c45219046f3599c92451c8ad1,0x1dee56bb3982be5d2d560ad54a712e9046a290c823b9ccde6b3419cb4572a9248c451c8ae0,0x77b95b0ce5d2d560ad54a712e9046a290c823b9ccde6b33968ae562a9248c451c8ade,0x3bdcad7673057cba5aac14a9c4ba411a8a43208ee73379acd0672d15cac55249188a39190ae1,0xef72b619cba5aac14a9c4ba411a8a43208ee73379acd0672d15cac55249188a39190adf,0x1dee56c33974b5582b5529c4ba411a8a43208ee73379acd0672d15cac55249188a39190ae0,0x77b95b0ce5f2e96ab055aa53897482351484411dce66f33968ae562a9248c45190ade,0x381b0ce5f2d556a94ba4108823999cac55190ad1,0x30d7cb65aac156a9399bcce5a2b1548c45190ad1,0x3959cbe582ad529745a2908823799c8c45190ad1,0x3bdcad8672f974b5582b5529c4ba411a8a411dce66f33968ae562a9248c451c8add,0x30d7cb5582b55275399bcce5a2b95492451c8ad1,0x395b0ce5aac14a8d45200de5a2b1509246228451,0x3959cbe592c15aa94ba3114823799c92451c8ad1,0x3959cbe582a52e8d45208e06f339248c451c8ad1,0x1dee56c3397cba5aac15aab54a712e9046a2908823b9ccde672d15cac55249188a39190ae0,0x77b6182be5d2d55aab54a71208d4521908823b9acd0672b958a649231147639190ade,0x3bdcad8672f974b5582a538974823514823b9ccde6833968ae562a9248c45190add]
def bk1 : Array Nat := #[0x395609c4ba35147b399bcc05a2b9389246228051,0x30d7cb65aac15273379a0ce5a2b1548c45190ad1,0x3959cbe582a52e8b45208e06f3419c8c45190ad1,0x3959cbe592c1529746a29046f339248c45190ad1,0xef72b619cbe5d2d560ab54a712e9046a2908823b9ccde6833968ae562a9248c45190adf,0xef72b619cbe5d2d560ad54a712e9046a290477399bcd0672d15cac55249188a39190adf,0xef72b619cbe5d2d560ad54a712e9046a290c84411dce66f3599cb4572a9248c451c8adf,0xef72b619cbe5d2d560ad54a712e9046a290c823b9ccde6b33968ae562a9248c451c8adf,0x1dee56c3397cba5aac15aa94e25d208d4521908823b9ccde6b33968ae562a9248c451c8ae0,0x3bdcad7673057cba5aac1529c4ba411a8a43208ee73379acd0672d15cac55249188a39190ae1,0x1dee56c3397cba5aac1529c4ba411a8a43208ee73379acd0672d15cac55249188a39190ae0,0xef72b619cc15f2e96ab056aad529c4ba411a8a43211046b3195cac552490c7639190adf,0x3bdcad8673057cba5aac15aab54a712e9046a290c84411dce66b31968ae562a924863b1c8ca1,0xef72b619cc15f2e96ab056aad529c4ba411a8a43211046b3419cae532490c7639190adf,0x3bdcad7673057cba5aac15aab54a712e9046a290c823b9bcd66833968ae53249188a3b1c8ca1,0x1dee56c33982be5d2d560ad55aa5389748235148642208d6683395cac552490c7639190ae0,0x3bdc0d8673057cb75aab556a94e25d208d421f8ee73379acd0672d15cac55231147635190ae1,0x77b95b0ce60af970b5582ad529b4ba411a843f1dce66f3419cb4562a9188a3b190ade,0x77b95b0ce60af974b5582b5529c4ba411a8a43211046b3195ca649231147639190ade,0xef72b619cc15f2e96ab056aad529c4ba411a8a43211046b3195ca649231147639190adf,0x3bdcad7673057cba5aac15aa94e25d208d4521908823b9bcd6632d15ca649231147639190ae1,0x3bdcad8673057cba5aac15aa94e25d208d4521908823b9bcd6632d15ca649231147639190ae1,0x3bdcad8673057cba5aac15aab54a712e9046a290c84411dcde6b31968ae53249188a3b1c8ca1,0x1dee56c33982be5d2d560ad55aa5389748235148642208d6632b958aa49231147639190ae0,0x1dee56bb3982be5d2d560ad55aa5389748235148642208d6683395ca649231147639190ae0,0x1dee56c33982be5d2d560ad55aa5389748235148642208d6683395ca649231147639190ae0,0x1dee56c33980be5d2d560ad54a712e9046a290c823b9ccde6b31968ae562a9248c451c8ae0,0x1dee56c33982be5d2d560ad54a712e9046a290c84411dce66b31968ae562a9248a3b1c8ae0,0xef72b5d9cc15f2e96ab056aa53897482351486411dcde6b31968ae55249188a3b1c8adf,0x3bdcad8673057cba5aac15aa94e25d208d452190477399bcd6632d15cac55249188a3b1c8ae1,0x1dee56c33982be5d2d560ad55aa5389748235148642208d66833968ae55249147639190ae0,0xef72b5d9cc15f2e96ab056aa5389748235148642208d6632d15caa49231147639190adf]
def bk2 : Array Nat := #[0x3bdcad7673057cba5aac15aa94e25d208d4521908823b9bcd6632d15caa49231147639190ae1,0x3bdcad8673057cba5aac15aab54a712e9046a290c84411acc65a2b958aa49231147639190ae1,0x1dee56c33982be5c2d560ab54a351484401dce66f3419cb4562a9188a3b190adc,0x39582be582891a8a399bcd0672d1388c451681d1,0x3619cc15f2d556a943a11006833958aa3b190ad1,0x381b0ce60af96aab54a1d08803419caa3b190ad1,0x39582be582891a8a3b9ccde68339689c46228091,0x395b0ce60af96ab055aa51a8a42200863b188951,0x269228b452110073379a0ce5a2b1548c45190ad1,0x395b0ce60af970b5582ad528d452110043188951,0x395b0ce60af970b5582ad528d45211003b188791,0x381b0ce5faf96aab54a1100733419cac55190ad1,0x395aece5f2d560a945200ec733799cb455228ad1,0x395aece5f2e16ab054a2900763799cb455228ad1,0x3959cbe5c2d560a945200ec733799cb455228ad1,0x3bdcad8673057cba5aac15aa94e25d208d452190882399acce572a924863b1c8add,0x30d82be5aac15aa93a9acce5525124863b1c8ad1,0x3959cc15f29d2e9046a290c84411acc63b1b8811,0x395b0ce5f2d560a94ba41168a42208ce55218ad1,0x36182b556aa1389046a1908813594c923b1c8991,0xef72b619cc15f2e96ab056aa53897482351486411dce66b33968ae562a924863b1c8adf,0x1dee56c33982be5d2d560ad54a712e9046a290c84411dce66b33968ae562a924863b1c8ae0,0x1dee56bb3982be5d2d560ad54a712e9046a290c823b9ccde6b33968ae55249188a3b1c8ae0,0x3bdcad7673057cba5aac15aa94e25d208d452190477399bcd66833968ae55249188a3b1c8ae1,0x1dee56c33982be5d2d560ad55aa5389748235148642208e66b3395cac552490c7639190ae0,0x1dee56c33982be5d2d560ad55aa5389748235148642208e66b3419cae552490c7639190ae0,0x3bdcad8673057cba5aac15aab54a712e9046a290c84411ccd6683395cac552490c7639190ae1,0x3bdcad7673017cba5aac15aa94e25d208d4521908823b9ccde6b33968ae55249188a3b1c8ca1,0xef72b5d9cc15f2e96ab056aa5389748235148642208e66b3395caa49231147639190adf,0xef72b619cc15f2e96ab056aa5389748235148642208e66b3395caa49231147639190adf,0x1dee56c33982be5d2d560ad55aa5389748235148642208e66b3395caa49231147639190ae0,0x3bdcad7673057cba5aac15aab54a712e9046a290c84411ccd6683395caa49231147639190ae1]
def bk3 : Array Nat := #[0x3bdcad7673057cba5aac15aa94e25d208d4521904733599cb4572a9248a3b1c8add,0x3959cc15f29d2e9046a290c82399acce511b88d1,0x30d80be5aac15aa93a9ccd6672b95492451c8ad1,0x395aece60af96ab056aa51a8a4015092451c0a51,0x2713497482311486411ccd6672b95492451c8ad1,0xef72b619cc15f2e96ab056aa53897482351486411dce66b33968ae562a9248a3b1c8adf,0x1dee56c33982be5d2d560ad54a712e9046a290c84411dce66b33968ae562a9248a3b1c8ae0,0x1dee56bb3982be5d2d560ad54a712e9046a290c84411ccd6672d15caa49231147639190ae0,0x77b6182b75aab556a84e2411a8642204ee73379acd0672d15cac55231147639190ade,0x1dee56c33980be5d2d560ad54a712e9046a290c823b9ccde6b33968ae562a9248c451c8ae0,0x3bdcad8673057cba5aac15aa94e25d208d452190882379acce57299248a3b1c8add,0x30d82be5aac15aa93a9acce53251248a3b1c8ad1,0x3959cc15f2d560ad54a35148440124863b1c0951,0x77b95b0ce60af974b5582b556a94e25d208d452190882379acce57299248a3b1c8ade,0x1dee56c33982be5d2d560ad54a712e9046a290c823b9ccde6b33968ae562a9248a3b1c8ae0,0xef72b5d9cc15f2e96ab056aa53897482351486411dcde6b33968ae53249188a3b1c8adf,0x1dee56c33982be5d2d560ad54a712e9046a290c84411dcde6b33968ae53249188a3b1c8ae0,0x3bdcad8673057cba5aac15aab54a712e9046a290c84411dcde6b33968ae53249188a3b1c8ae1,0x3bdcad7673057cba5aac15aa94e25d208d452190477399bcd66833968ae53249188a3b1c8ae1,0x1dee56c33982be5d2d560ad55aa5389748235148642208de6b3395cac55249147639190ae0,0x1dee56c33982be5d2d560ad55aa5389748235148642208de6b3419cae53249147639190ae0,0x3bdcad7673017cba5aac15aa94e25d208d4521908823b9bcd6672d15ca649231147639190ae1,0xef72b5d9cc15f2e96ab056aa5389748235148642208de6b3395ca649231147639190adf,0xef72b619cc15f2e96ab056aa5389748235148642208de6b3395ca649231147639190adf,0x1dee56c33982be5d2d560ad55aa5389748235148642208de6b3395ca649231147639190ae0,0x3bdcad7673057cba5aac15aa94e25d208d4521908823b9bcd6672d15ca649231147639190ae1,0x3bdcad8673057cba5aac15aa94e25d208d4521908823b9bcd6672d15ca649231147639190ae1,0x3bdcad7673057cba5aac15aab54a712e9046a290c84411bcd6683395ca649231147639190ae1,0x3bdcad8673057cba5aac15aab54a712e9046a290c84411bcd6683395ca649231147639190ae1,0x77b95aece602f974b5582b5529c4ba411a8a43208ee6f3599cb4572a9248c451c8ade,0x77b95b0ce60af974b5582b5529c4ba411a8a43211046f3599cb4572a9248a3b1c8ade,0x30d80be5aac15aa93a9bcd6672b95492451c8ad1]
def bk4 : Array Nat := #[0x2713497482311486411bcd6672b95492451c8ad1,0x395aece5f2d560a94da5d208a411bcce55228ad1,0xef72b5d9cc15f2e96ab056aa53897482351486411dcde6b33968ae55249188a3b1c8adf,0x1dee56c33982be5d2d560ad54a712e9046a290c84411dcde6b33968ae55249188a3b1c8ae0,0x3bdcad7673017cba5aac15aa94e25d208d4521908823b9bcd6672d15caa49231147639190ae1,0x1dee56bb3982be5d2d560ad54a712e9046a290c84411bcd6672d15caa49231147639190ae0,0x1dee56c33982be5d2d560ad54a712e9046a290c84411bcd6672d15caa49231147639190ae0,0x3bdcad7673057cba5aac15aa94e25d208d4521908823b9bcd6672d15caa49231147639190ae1,0xef72b5d9cc05f2e96ab056aa53897482351486411dce66f3599cb4572a9248c451c8adf,0x3bdcad7673057cba5aac15aa94e25d208d452190473379acce572a9248a3b1c8add,0x30d80be5aac15aa93a9ccde6b3395492451c8ad1,0x3959cc15f2d560ad54a3514803799492451c0a51,0x2713497482311486411ccde6b3395492451c8ad1,0x77b95b0ce60af974b5582b5529c4ba411a8a432110473379acce572a9248a3b1c8ade,0x395aece5f2d560a94ba411482399bcce55228ad1,0xef72b619cc15f2e96ab056aad529c4ba411a8a432110473379acce572a9248a3b1c8adf,0x1dee56bb3982be5d2d560ad54a712e9046a290c84411ccde6b3395caa49231147639190ae0,0x1dee56c33982be5d2d560ad54a712e9046a290c84411ccde6b3395caa49231147639190ae0,0x77b95aece60af974b5582b5529c4ba411a8a43208e66f3599cb4572a9248a3b1c8ade,0xef72b619cc15f2e96ab056aa5389748235148642208e66f3599cb4572a9248a3b1c8adf,0x1dee56c33982be5d2d560ad55aa5389748235148642208e66f3599cb4572a9248a3b1c8ae0,0x3bdcad7673057cba5aac15aa94e25d208d452190882399bcd6672d15caa49231147639190ae1,0x3bdcad8673057cba5aac15aab54a712e9046a1908823598cae562a9247639190add,0x395b0ce5aac14a9c4ba411a8642208a6491a03d1,0x2692e9046a190882361acc655248f47639190ad1,0x3959cc15f2d560ad55aa51a84401247638188951,0x77b6182ab4e2692e9046a290c84411dce66f3419cb85a2b958aa49231147639190ade,0x77b95b0ce60af974b5582b556a94e25d207e3b9ccde6b3419cb4572b1547639190ade,0x3bdcad8673057cba5aac15aab54a712e9046a28fc77379acd0672d15ca649231147639190ae1,0x1ded860aad369a4ba411a8a432110477399bcd0672d158aa49231147639190adc,0x361829b4d25d207e399bcd0672d158aa3e180751,0x305369a4ba35147b399bcd067271248c451681d1]
def bk5 : Array Nat := #[0x361829a4ba411a8a4321104532490c76391889d1,0x36182ab4da692e903f1ccde6833958aa3e180751,0x33d82ab46a290c84411a0ce49231147639190ad1,0x36182ab4da692e903f1ccde6833968ac551f0291,0x245208d4521908822d158aa49231147639190ad1,0x36182ab4da692e903f1ccde6833968ac551805d1,0x305569a4ba411a8a4321104532490c76391889d1,0x36182ab4d25d208d4521908822490c76391889d1,0x361829b4d25d208d45219088229924863b1c83d1,0x36182ab4d25d208d45219088229924863b1c83d1,0x1dce66f361a0ce5a2b1549449231147639190ad1,0x2fd6cab3b9ccde6833968ac55249188a39190ad1,0x36182ab4da692e9046a290c84411247639188811,0x3617eab4da5d208642208e66833958aa39190ad1,0x26d3497482311486411ccde672d15492451c8ad1,0x36182ab4da692e903b9ccde6833968ac55180711,0x36182ab482350c84409ccd066289187637190891,0x36182ab4d25d208d452190882299247639188991,0x36182ab46a1908682d158a849231107639190a11,0x26d3497482290c823b1ccde672d15492451c8ad1,0xef6c34d9cc15c2d560ab52a411a8a432110477399bcd0672d158aa49231147639190adf,0xef72b619cc15f2e96ab056aad529c4ba411a863f1dce66f359a0ce57299247639190adf,0x1dee56c33982be5d2d560ad55aa53897482350c7e3b9ccd66833968ae562a9247639190ae0,0x3bdcad8673057cba5aac15aab54a712e9046a18fc77399bcd66833968ae562a9247639190ae1,0x3bdcad8673057cba5aac15aab54a712e9046a290c7e3b9bcd66833968ae53249188a3b1c8ca1,0x3bdcad7673057cba5aac15aab54a712e9046a290c7e3b9ccde6b33968ae53249188a3b1c8ca1,0x3bdb0c155a71349746a290c84411dce66f3419cb85a2b958aa49231147639190add,0x361829c4d25cee73379a0ce5a2b958aa3e180751,0x361829c4d25d1a8a4321104572490c76391889d1,0x3615cab46a290c8441158aa49231147639190ad1,0x3617eab42208ee73379a0ce5a2b1548c45190ad1,0x3056cab3b9ccde6833968ac55231147639190ad1]
def bk6 : Array Nat := #[0xef72b619cc15f2e96ab056aad529c4ba4108823b9ccde6b3419cb4572b1547639190adf,0x77b95b0ce60af974b5582b556a94e25d208d43211046b3419cae562a9247639190ade,0x381b0ce5faf96aab54a5d2084411a0ce55190ad1,0x3057cb65aab556a93a9acd0672b1547639190ad1,0x25d229043a190882361acd0672b1547639190ad1,0x361829a4ba411a8a4321104632490c76391889d1,0x305569a4ba411a8a4321104632490c76391889d1,0x36182ab4da692e9046a290c8441124863b1c83d1,0x36182ab4d25d208d452190882319247639188811,0x36182ab4d25d208d452190882311247639188991,0x1dee56c33982be5d2d560ad55aa53897482350c7e3b9ccde6b3419cb4572a9248a3b1c8ae0,0x77b95b0ce60af974b5582b5529c4ba411a863f1dce66b31968ae562a9248a3b1c8ade,0xef72b619cc15f2e96ab056aad529c4ba411a863f1dce66b31968ae562a9248a3b1c8adf,0x1dee56c33982be5d2d560ad54a712e9046a18fc77399bcd66833968ae562a9248a3b1c8ae0,0x3bdcad8673057cba5aac15aab54a712e9046a18fc77399bcd66833968ae562a9248a3b1c8ae1,0xef703619cc15f2ad4e9b4ba411a8a432110477399bcd0672d158aa49231147639190adf,0x1dee56c33982be5d2d560ad55aa538974823514863f1dcde6b31968ae55249188a3b1c8ae0,0x3bdcad7673057cba5aac15aa94e25d208d45218fc77399bcd66833968ae55249188a3b1c8ae1,0x3bdcad8673057cba5aac15aa94e25d208d45218fc77399bcd6632d15cac55249188a3b1c8ae1,0x3bdcad8673057cba5aac15aab54a712e9046a290c7e3b9ccde6b31968ae562a9248c451d8e61,0xef72b619cc15f2e96ab056aad529c4ba411a8642208d6632d15cac55249147639190adf,0x1ded860aad389a4ba411a8a432110477399bcd0672d158aa49231147639190adc,0x361829c4d25d207e399bcd0672d158aa3e180751,0x361829c4d25d208d4521908822490c76391889d1,0x249229046a290c8441158aa49231147639190ad1,0x36182ab4e2692e903f1ccde6833958aa3e180751,0x36182ab4e2692e903f1ccde6833968ac551f0291,0x36182ab4e2692e903f1ccde6833968ac551805d1,0x1d4e66f361a0ce5a2b1549449231147639190ad1,0x36182ab4e2692e9046a290c8441124863b1c83d1,0x36182ab4e2692e9046a290c84411247639188811,0x3617eab4e25d208642208e66833958aa39190ad1]
def bk7 : Array Nat := #[0x2713497482311486411ccde672d15492451c8ad1,0x36182ab4e2692e903b9ccde6833968ac55180711,0x36182ab4e2692e9046a290c84411247639188991,0x2713497482290c823b1ccde672d15492451c8ad1,0x1dee56c33982be5d2d560ad55aa53897481f8ee73379acd0672d15cac55249147639190ae0,0x3bdcad7673057cba5aac15aab54a712e9046a28fc77379acd0672d15caa49231147639190ae1,0x3bdcad8673057cba5aac15aab54a712e9046a28fc77379acd0672d15caa49231147639190ae1,0x77b95aece60af974b5582b556a94e25d208d431f8d66833968ae55249147639190ade,0x77b95b0ce60af974b5582b556a94e25d208d431f8d66833968ae55249147639190ade,0x3bdcad7673057cba5aac15aab54a712e9046a18fc77399bcd66833968ae55249147639190ae1,0x3bdcad8673057cba5aac15aab54a712e9046a18fc77399bcd66833968ae55249147639190ae1,0x3bdcad8673057cba5aac15aab54a712e9046a18fc77399acd0672d15cac55249147639190ae1,0x3bdcad7673057cba5aac15aab54a712e9046a290c7e3b9bcd66833968ae55249188a3b1c8ca1,0x1dee56c33982be5d2d560ad55aa53897482350c84411acd0672d15cac55249147639190ae0,0x77b61a6ce60ac960ad55aa51a8a432110477399bcd0672d158aa49231147639190ade,0x3bdcad8673057cba5aac15aab54a712e9043208ee73379acd0672d15cac551c8add,0x361a6ce5aac15cad55aa524904115cac551c8ad1,0x3959ece60af960ad55aa52e82379acd0671c8ad1,0x1dee56c33982be5d2d560ad55aa53897482351486411dce66f3599cb4572a9248c451c8ae0,0xef72b619cc15f2e96ab056aad529c4ba411a86411ccd6672b954923b1c8adb,0x395b0ce5aa953897482350c8239980ae551a04d1,0x3619cb5572b556a9492411a8641154923b1c8ad1,0x395b0ce5aac14a9c4ba411a86411ccc0572a8291,0x3819cc15f2b556a94ba350c823599c923b1c8ad1,0x395b0ce60af94e97482350c82399acce511b88d1,0x3619cb5582b95aab54a4104572a928923b1c8ad1,0x361a6ce5aac15aab54a49208c43208aa491c8ad1,0x361a6ce5aac15cad55aa524904115caa491c8ad1,0x3057cb65aac15aab549acce572a928923b1c8ad1,0x30d82be5aac15aab549acce572a928923b1c8ad1,0x30d82be5b2d560ad55aa4d6672a928923b1c8ad1,0x395b0ce60af956a74ba411a86411ccd6672885d1]
def bk8 : Array Nat := #[0x35da6ce5aac15aa9492411a8641154923b1c8ad1,0x39582be582b5449c4ba350c7b3598c923b1c8111,0x395b0ce5aac14a9c4ba411a864115ca6491a03d1,0x395b0ce60af956a74ba411a86411acc63b1b8811,0x2713497482350c82399b0d6672a9247a3b1c8ad1,0x13a9c4ba410e86411ccd86b3395caa3b1c8ad0,0x2713497482310c82399acce5c2b954923d1c8ad1,0x1dee56c33982be5d2d560ad55aa51a491d8e10,0x3b5cad8672f970b5582a49,0x1dee560af938974821904733599cae551c8ad0,0x1ded85d2d538974821904733599cae551c8ad0,0x2753897482350c82399b0d6672b954923b1c8ad1,0x2713497482350c82399acce572a9247a3b1c8ad1,0xef72b619cc15f2e96ab056aad528d248ecf,0x2712e9046a190473361acce5c2b954923b1c8ad1,0x395b0ce5faf96ab055aa5369748208e6672a8ad1,0x395b0ce5f2e16ab055aa5369748208e6672a8ad1,0x395b0ce5faf970b5582ad529b4ba4104672a8ad1,0x3959cc15f2c15aab54a5d046b33928923b1c8ad1,0x3959cc15f2c15aab54a5d0e86411acce3b1c8ad1,0x3959ece60af960ad55aa53097411acce3b1c8ad1,0x3959cc05f2c15aa94ba350c823599c923b1c8ad1,0x36182b556aad509c482350c813594c923b1c8991,0x3a1cad8672f96ab055aa5369748208e6672a8ad1,0x77b61a6ce60ae16ab055aa51a8a432110477399bcd0672d158aa49231147639190ade,0x77b95b0ce60af974b5582b556a94e25d208d43208ee73379acd0672b954923b1c8ade,0x3bdcad8673057cb055aa51a8a432110477399bcd0672d158aa49231147639190add,0x36182ab46a190881399a0cc562a9187637190891,0x36182ab46a190881399a0cc51249187639190891,0x36182af55aa11a84399a0aa49231107638190a11,0x36182af55aa11a86421a0a849231107639190a11,0x77b95b0ce60af974b5582b556a94e25d208d43208ee733599cb4572b154923b1c8ade]
def bk9 : Array Nat := #[0xef72b619cc15f2e96ab056aa53897482350c823b9ccde6b3419cb4572b154923b1c8adf,0x1dee56c33982be5d2d560ad55aa53897482350c823b9ccde6b3419cb4572b154923b1c8ae0,0x77b95b0ce60af974b5582b556a94e25d208d4321104733599cae562a9247639190ade,0x381b0ce5faf96aab54a5d2084411ccce55190ad1,0x3057cb65aab556a93a9ccd6672b1547639190ad1,0x25d229043a190882399b0d6672b1547639190ad1,0xef72b619cc15f2e96ab056aad529c4ba410c82399acd0672b9547639190adb,0x39582be56a892e863d9ccd6683393876391681d1,0x395b0ce5aac14a9c4ba410c8239980ae551a04d1,0x3057cb65aab556a93a9ccd668339547639190ad1,0x3819cc15f2b556a94ba19046b3419c7639190ad1,0x395b0ce5d2d54a9c4ba410c8239980ae551a04d1,0x3619cb5572b556a9492410c822b9547639190ad1,0x30d82be592c15aab54a19046b3419c7639190ad1,0x395b0ce5d2d560a54e25d2086411ccc0572a8291,0x395b0ce60af94e97482190473359a0ce511b88d1,0x395b0ce60af92e9043208e66b3419c76371680d1,0x39582be56a712e863d9ccd6683395c76391680d1,0x361a6ce5aac15aab54a4920864115caa39190ad1,0x361a6ce5aac15cad55aa524904115caa39190ad1,0x3959cc15f2ad4e97482190473359a0ce511805d1,0x3959cc15f2ad4e97481f8e66b3419ca23b1905d1,0x381b0ce5faf96aab54a5d2082399a0ce55190ad1,0x30d82be592c15aab549ccd668339547639190ad1,0x395b0ce5d2d560a54e25d2086411ccae551a03d1,0x3bdcad8672e96ab052a712e9043208e6572a8251,0x3959cc15f2ad4e9748219046b3418c7637190811,0x2713497482190473361acd0672a8f47639190ad1,0x395b0ce60af974b5582b556a9341947638190a51,0x395b0ce4e25d2086411ccd6672e15caa3d1c8ad1,0x36174b54e2692e9043208e66b3395caa3d1c8ad1,0x13897482190473361acd0672b9547639190ad0]
def bk10 : Array Nat := #[0x2712086411ccc0572a8d09,0x27134974821904733599cb8572a8f47639190ad1,0x3bdcad8673057cba5aac15aab549a0ca3b1906d1,0x2713497482190473359a0ce5c2b9547a39190ad1,0x3bdcad8673057cba5aac15aab549a07638190951,0x2713497482190473359a0ce572a8f47639190ad1,0x9c4ba410c82399acd0672b9547639190acf,0x2713497482190473361acd0672b9547639190ad1,0x2712e9043208e66c359a0ce5c2b9547639190ad1,0x36182b556aa1389043204e66b3315caa3b1c8a91,0x39582be56a712e86399acd0672b9387639168191,0x36182b556a712086399acd0662b9547639168191,0x395b0ce5f2d560ab54a6d2e90411ccce55190ad1,0x395b0ce5faf96ab055aa5369748208ce55190ad1,0x36182b556aad509c481ccd668331547635190711,0x36182b556aad509c482190273359547639188991,0x36182b556aad509c48219026b3414c7639190991,0xef72b619cc15f2e96ab056aad529c4ba410c823b9ccde6b3419cb4572b1547639190adf,0x77b95b0ce60ae16ab055a951a8a432110477399bcd0672d158aa49231147639190ade,0x3bdcad8673057cba5aac15aab54a712e9046a190473359a0ce572a9247639190add,0x2713497482350c82399acce55248f47639190ad1,0x2712e9043a190473361acd0672b9547639190ad1,0xef72b5d9cc15f2e96ab056aad529c4ba411a86411dce66f359a0ce572a9247639190adf,0xef72b619cc15f2e96ab056aad529c4ba411a86411dce66f359a0ce572a9247639190adf,0x1dee56c33982be5d2d560ad55aa53897482350c823b9ccd66833968ae562a9247639190ae0,0x3bdcad8673057cba5aac15aab54a712e90432110473359a0ce572b1547639190add,0x395b0ce5aa952e9043211047330158aa341784d1,0x1dee56c33982be5d2d560ad55aa538974821908823b9ccde6b3419cb4572b1547639190ae0,0xef72b619cc15f2e96ab056aad529c4ba411a8642208e66b3419cae562a9247639190adf,0x1dee56c33982be55a9d1a8a432110477399bcd0672d158aa49231147639190adc,0x395b0ce60af956a7399bcd0672d158aa3e180751,0x2691a8a43211046f361a0ce49231147639190ad1]
def bk11 : Array Nat := #[0x34d9cae55a9d1a8a432110449231147639190ad1,0x361a6ce55a9d168a42208ac55249188a39190ad1,0x30d82be55a9cde68339549449231147639190ad1,0x2451a8a43211045b2d158aa49231147639190ad1,0x395b0ce60af956a73b9ccde6833968ac551805d1,0x3959cc15f2ad4e8d4521908822490c76391889d1,0x269228b452110473379a0ce5a2b1548c45190ad1,0x30d7ebe5b2ad4e73379a0ce5a2b1548c45190ad1,0x395b0ce60af956a746a290c84411247639188811,0x39582be46a28e66f3419cb449231147638168151,0x381b0ce5faf956a74321104733419caa39190ad1,0x395b0ce46a290c84411bcb4562a1248c45178451,0x3819cc15f2ad4e874321104733419c7639190ad1,0x395b0ce60af956a7399bcd0672d158aa3e1806d1,0x395b0ce60af956a73b9ccde6833968ac55180551,0x3959cc15f2ad4e8d4521908822490c7639188951,0x395b0ce60af956a746a290c84411247639188791,0x395aece5f29d188a43208e66f3395492451c8ad1,0x36182ab46a10e6682d158aa49231107638190a11,0x3959cbe53a3d188a43208e66f3395492451c8ad1,0x3959cbe53a311486411ccde672d15492451c8ad1,0x395aece5f29d1486411ccde672d15492451c8ad1,0x3bdcad8673057cba5aac15aab54a712e9046a1904733599cb4572a9248a3b1c8add,0x2712e9046a190473361acce572a9248a3b1c8ad1,0x2713497482310c82399acce5a2b95492451c8ad1,0xef72b5d9cc15f2e96ab056aa53897482350c823b9ccde6b3419cb4572a9248a3b1c8adf,0x1dee56c33982be5d2d560ad55aa53897482350c823b9ccde6b3419cb4572a9248a3b1c8ae0,0x77b95b0ce60af974b5582b5529c4ba411a86411dce66b33968ae562a9248a3b1c8ade,0xef72b619cc15f2e96ab056aad529c4ba411a86411dce66b33968ae562a9248a3b1c8adf,0x1dee56c33982be5d2d560ad54a712e9046a190477399bcd66833968ae562a9248a3b1c8ae0,0x1dee56c33982be5d2d560ad55aa53897482350c84411ccd6672d15cac55249147639190ae0,0x77b95b0ce60af974b5582b556a94e25d2086411ccd66833968ae55249147639190ade]
def bk12 : Array Nat := #[0xef72b5d9cc15f2e96ab056aad529c4ba411a86411ccd66833968ae55249147639190adf,0xef72b619cc15f2e96ab056aad529c4ba411a86411ccd66833968ae55249147639190adf,0x3bdcad7673057cba5aac15aab54a712e9046a190477399bcd66833968ae55249147639190ae1,0x3bdcad8673057cba5aac15aa94e25d208a411dce66f359a0ce5a2b958aa451a8add,0x361a6ce5aac15aa949241045a2b958aa451a8ad1,0x395b0ce60af94e97481f8e66f359a0ce562885d1,0x395b0ce60af96ab056aa4de6832968ac541f06d1,0x77b95b0ce60af974b5582b556a94e25d208a411dce66f359a0ce5a2b958aa451a8ade,0x77b95b0ce60af974b5582b556a94e25d208d45208ee6f3599cb457299248c451a8ade,0x1dee56c33982be5d2d560ad54a712e9046a290477399bcd66833968ae562a9248c451a8ae0,0x3bdcad8673057cba5aac15aab54a712e9046a290477399bcd66833968ae562a9248c451a8ae1,0x3bdcad8673057cba5aac15aab54a712e9046a290c82379acce57299248a3b1c8add,0x3959cc15f2ad4e97482351486411acc63b1b8811,0x2713497482351486411b0d667299248a3b1c8ad1,0x3959cc15f2d560ad55aa51a8a40124863b1c0951,0x1dee56c33982be5d2d560ad55aa53897482351486411dce66f359a0ce57299248a3b1c8ae0,0x1dee56c33982be5d2d560ad55aa53897482351486411dcde6b33968ae53249188a3b1c8ae0,0x1ded860aad389046a290c84411dce66f3419cb85a2b958aa49231147639190adc,0x361829c481dce66f3419cb85a2b958aa3e180751,0x361829c48235148642208ae532490c76391889d1,0x2611a8a43211046f361a0ce49231147639190ad1,0x36182ab4e240ee73379a0ce5a2b958aa3e180751,0x36182ab4e240ee73379a0ce5c2d15cac551f0291,0x36182ab4e240ee73379a0ce5c2d15cac551805d1,0x26d229045a290882399bcd0672b1548c45190ad1,0x36182ab4e2411a8a4321104532490c76391889d1,0x36182ab4e2411a8a43211045729924863b1c83d1,0x36182ab4e2411a8a43211045c2b9247639188811,0x3615cab4e2410e8642208e6672b1547639190ad1,0x271208c452190476399bcce5a2b95492451c8ad1,0x33d5cab46a290c84411bcce49231147639190ad1,0x36182ab4e240ee73379a0ce5c2d15cac55180711]
def bk13 : Array Nat := #[0x36182ab4e2411a8a432110457299247639188991,0x271208c4521904733799cb85a2b95492451c8ad1,0x1dee56c33982be5d2d560ad55aa53897482290477399bcd66833968ae562a9147639190ae0,0x3bdcad7673057cba5aac15aab54a712e9046a290477379acd0672d15ca649231147639190ae1,0x3bdcad8673057cba5aac15aab54a712e9046a290477379acd0672d15ca649231147639190ae1,0xef72b5d9cc15f2e96ab056aad529c4ba411a8a43208de6b3419cae53249147639190adf,0xef72b619cc15f2e96ab056aad529c4ba411a8a43208de6b3419cae53249147639190adf,0x3bdcad7673057cba5aac15aab54a712e9046a290c823b9ccde6b3419cae53249147639190ae1,0x3bdcad8673057cba5aac15aab54a712e9046a290c823b9ccde6b3419cae53249147639190ae1,0x77b95b0ce60af974b5582b556a94e25d208a42208de6b3419cae562a9147639190ade,0xef6c305569c48235148642208ee73379acd0672d158aa49231147639190adb,0x3bdb0c14e240ee73379acd0672d158aa3e180751,0x3bdb0c14e2411a8a43211046b2490c76391889d1,0x361389046a290c84411ccde60271248c451a0051,0x305388d45218f673379acd067271248c451a0051,0x361389046a290c7b399bcc0562a9248c451a0051,0x305388d45218f673379acc04e249188a3b1c8051,0x235148642208de6c359a0ce49231147639190ad1,0x36182ab4e240ee73379acd0672d158aa3e180751,0x3bdb0c155a712077399bcd66833968ac55180751,0x3051a8a431ece66f359a0ce492310476391680d1,0x361389046a290c84411ccde602b1548c411782d1,0x33d5cab46a290c8441168aa49231147639190ad1,0x3bdb0c155a712077399bcd66833968ac551805d1,0x1d4e66f361acd0672b1549449231147639190ad1,0x36182ab4e2411a8a43211046b2490c76391889d1,0x3bdb0c155a71208d4521908823592476391889d1,0x3bdb0c155a71208d452190882359247639188811,0x3615cab4821d0c84411ccd6672b1547639190ad1,0x3617eab4e2410c84411ccd66833958aa39190ad1,0x3056cab4e2410c82399acd0672b1547639190ad1,0x33d82ab4821d0c84411ccd668339547639190ad1]
def bk14 : Array Nat := #[0x271208c452190476399bcd6672d15492451c8ad1,0x305388d431ccde6b3419c9c49231107639168191,0x361389046a290c84411ccac55249188834178491,0x3bdb0c155a712077399bcd66833968ac55180711,0x3bdb0c155a712077399bcd66833968ac55180591,0x2fd6cab45208ee73379a0ce5a2b1548c45190ad1,0x3bdb0c155a71208d452190882359247639188991,0x3bdb0c155a71208d4521908823592476391887d1,0x77b95b0ce60af974b5582b5529c4ba4114823b9ccde6b3419cb4572b15492451c8ade,0x35da6ce5aac15aa94924114822b95492451c8ad1,0x2713497482290473379acce5a2b95492451c8ad1,0x3959cc05f2c15aa94ba29046f3599c92451c8ad1,0xef72b619cc15f2e96ab056aad529c4ba4114823b9ccde6b3419cb4572b15492451c8adf,0x3bdcad7673017cba5aac15aa94e25d208d45208ee6f3599cb4572a9248c451c8add,0x395aece602f94e9c4ba411a8a411bcd6672088d1,0x2e96ab056aa51a8a4116cb4572a9248c451c8ad1,0x2e96ab056aa4ee6f33968ae55251248c451c8ad1,0x35d80b556aa13890469dcd65a2b95492441c8a91,0x3959cbe582a52e8b45208ee6f33968aa46228ad1,0x77b95b0ce60af974b5582b556a94e25d208d45208ee6f3599cb4572a9248c451c8ade,0x1dee56c33982be5d2d560ad54a712e9046a290477399bcd66833968ae562a9248c451c8ae0,0x3bdcad7673057cba5aac15aa94e25d208d45219046f3599cb4572a9248a3b1c8add,0x3959cc15f29d2e9046a290c82379acce411b88d1,0x77b95b0ce60af974b5582b556a94e25d208d45219046f3599cb4572a9248a3b1c8ade,0x1dee56bb3982be5d2d560ad54a712e9046a290c823b9ccde6b3419cb4572a9248a3b1c8ae0,0x1dee56c33982be5d2d560ad55aa53897482351486411dcde6b33968ae55249188a3b1c8ae0,0x77b95b0ce60af974b5582b556a94e25d208a411bcd66833968ae55249147639190ade,0x3bdcad7673057cba5aac15aab54a712e9046a290477379acd0672d15caa49231147639190ae1,0x1dee56bb3982be5d2d560ad55aa53897482351486411bcd66833968ae55249147639190ae0,0x1dee56c33982be5d2d560ad55aa53897482351486411bcd66833968ae55249147639190ae0,0x1dee56c33982be5d2d560ad55aa53897482290882379acd0672d15cac55249147639190ae0,0x77b95b0ce60af974b5582b5529c4ba411486411dce66f359a0ce5a2b958aa451c8ade]
def bk15 : Array Nat := #[0x35da6ce5aac15aa94924114864115caa451c8ad1,0x2713497482290c82399bcd6672d15caa451c8ad1,0x3959cc05f2c15aa94ba290c82379acce451c8ad1,0xef72b619cc15f2e96ab056aad529c4ba411486411dce66f359a0ce5a2b958aa451c8adf,0x77b95b0ce60af974b5582b556a94e25d208d452190473379acce572a9248a3b1c8ade,0xef72b5d9cc15f2e96ab056aa53897482351486411dce66f359a0ce572a9248a3b1c8adf,0x1dee56c33982be5d2d560ad55aa53897482351486411dce66f359a0ce572a9248a3b1c8ae0,0x77b95b0ce60af974b5582b556a94e25d208a43208e66f359a0ce572a9147639190ade,0x1dee56bb3982be5d2d560ad55aa53897482351486411ccde6b3419cae55249147639190ae0,0x1dee56c33982be5d2d560ad55aa53897482351486411ccde6b3419cae55249147639190ae0,0x3bdcad7673057cba5aac15aab54a712e9046a290c823b9ccde6b3419cae55249147639190ae1,0x1dee56c33982be5d2d560ad55aa53897482290c84411ccde6b3419cae562a9147639190ae0,0x3bdcad8673057cba5aac15aab54a712e90452190473379acce5a2b95492451c8add,0x3959cc15f29d2e90452190473379acce411b88d1,0x36182b556aa1389043204e66b3315492441c8a91,0xef72b619cc15f2e96ab056aa53897482290c823b9ccde6b3419cb4572b15492451c8adf,0x1dee56c33982be5d2d560ad55aa53897482290c823b9ccde6b3419cb4572b15492451c8ae0,0xef72b619cc15f2e96ab056aad529c4ba411a8a43208e66f3599cb4572a9248a3b1c8adf,0x1dee56c33982be5d2d560ad55aa53897482290c82399bcd66833968ae55249147639190ae0,0x3bdcad7673057cba5aac15aab54a712e9046a290c82399bcd66833968ae55249147639190ae1,0x3bdb0c360af974b056aad528d4521908823b9d4e66f359a0ce5a2b958aa49231147639190ae1,0xef6c3057cba582b556a946a290c84411dce66f359a0ce5a2b958aa49231147639190adf,0x3bdcad860af964b056aad52984ba35148642208ee73379acd0672d158aa49231147639190ae1,0xef6c30d82be592c15aab54a35148642208ee73379acd0672d158aa49231147639190adf,0x1ded860af95aab54a35148642208ee73379acd0672d158aa49231147639190adc,0x3611a8a432110473379a4c055249188a341784d1,0x3611a8a43211047337968ac55249188a341784d1,0x3611a8a43211047337980b4562a9248c451784d1,0x36182be56aad5273379acd0672a91c7c35180751,0x36182be56aad5273379acd0672d158aa35180751,0x36182be56aad5273379acd0672d158aa3e180751,0x3611a8a432110473379a4c0562a9248c451782d1]
def bk16 : Array Nat := #[0x36182be56aad5277399bcd66833968ac551805d1,0x3057cad55aa5148642208da6b3190c76391889d1,0x3057cad55aa51a8a43211046b2490c76391889d1,0x3057cad55aa51a8a43211046b3192476391889d1,0x3057cad55aa5148642208da6b319247639188811,0x3611a8a432110477399bcb4562a9248c45178451,0x36182be56aad5273379acd0672b1548e3e1806d1,0x3017cad54a311486411ccde6b3395492451c8ad1,0x3057cad55aa5148642208da6b2490c7639188951,0x3611a8a432110473379a4ac55249188a34178491,0x36182be56aad5273379acd0672b1548e35180711,0x36182be56aad528d452190882359247639188991,0x2f95aa9462290c82399bcd6672d15492451c8ad1,0x3017cad54a290c82399bcd6672d15492451c8ad1,0xef72b619cc15f2e96ab055aa5389748235148642208ee73379acd0672d15cac55190adf,0xef7036182be56aad52984ba35148642208ee73379acd0672d158aa49231147639190adf,0x3bdcad8672e96ab055aa5389748235148642208ee7337968ae562a9248c45190add,0x30d6cb5582a4ea7337974ac55251248c45190ad1,0x3959ece582a52e8d452190882379248c45190ad1,0xef6c30d82be5c2c15aab54a35148642208ee73379acd0672d158aa49231147639190adf,0xef72b6182be582b556a94ba35148642208ee73379acd0672d158aa49231147639190adf,0xef72b619cc15d2d560ad55aa5389748235148642208ee7335968ae562a9247639190adf,0x1dee56c33982be5d2d560ad55aa5389748235148642208ee7335968ae562a9247639190ae0,0xef703619cc15f2b556a94ba35148642208ee73379acd0672d158aa49231147639190adf,0x1dee56c33982ba5aac15aa94e25d208d4521908823b9ccde6b2d15cac55249188a3b1c8ae0,0x77b6186c15f2b556a946a290c84411dcea73379acd0672d158aa49231147639190ade,0x3bdb0c360af95aab54a35148642208ee73379acd0672d158aa49231147639190add,0xef72b619cba5aac15aab54a712e9046a290c84411dce66f2d15cac55249188a39190adf,0x77b95b0ce60ae96ab056aad529c4ba411a8a43211046b2d15cac55249147639190ade,0x361a6ce5aac156a94822d148441158aa45190ad1,0x249229046a290c844115cac55249147639190ad1,0x2d96ab0572b556a92b958aa4a249147639190ad1]
def bk17 : Array Nat := #[0x1dee56c33982ba5aac15aab54a712e9046a290c84411dce66b2d15cac55249147639190ae0,0x1dee56c33982be592c15aab54a35148642208ee73379acd0672d158aa49231147639190ae0,0x77b6182be592c15aab54a35148642208ee73379acd0672d158aa49231147639190ade,0x77b81b0ce60af95aab54a35148642208ee73379acd0672d158aa49231147639190ade,0x77b95b0ce5d2d560a54e25d208d4521908823b9ccde6b33968ae562a9248c451c8ade,0x1dee56c33982be5d2d560a54e25d208d452190477399bcd66833968ae562a9248c451c8ae0,0x3bdcad8673057cba5aac14a9c4ba411a8a432110477399bcd66833968ae562a9248c451c8ae1,0x1ded861b057cb85aac15aab54a35148642208ee73379acd0672d158aa49231147639190ae0,0xef6c3057cb85aac15aab54a35148642208ee73379acd0672d158aa49231147639190adf,0xef72b619cc15f2c15aab54a35148642208ee73379acd0672d158aa49231147639190adf,0x77b6186c15f2c15aab54a35148642208ee73379acd0672d158aa49231147639190ade,0x1dee56c33982be5d2d560ad55aa5389748235148642208ee733599cb4572b154923b1c8ae0,0x3bdcad8673057cba5aac15aa54e25d208d4521908823b9ccde6b3419cb4572b154923b1c8ae1,0x1dee56c33982ba5aac15aa54e25d208d452190477399bcd6672d15cac55249188a3b1c8ae0,0x3bdcad86730574b5582b54a9c4ba411a8a432110477399bcd6672d15cac55249188a3b1c8ae1,0xef72b6182be592c15aab54a35148642208ee73379acd0672d158aa49231147639190adf,0x1dee56c33982be5d2d560ab54a712e9046a290c84411dce66f359a0ce5a2b958aa39190ae0,0xef72b619cc15d2d560ad55aa53897482350c84411dce66b33968ae562a9247639190adf,0x1dee56c33982ba5aac15aab54a712e9046a290c84411dce66b33968ae562a9247639190ae0,0x77b95b0ce60af95aab54a35148642208ee73379acd0672d158aa49231147639190ade,0xef72b619cba5aac15aa94e25d208d4521908823b9ccde6b33968ae562a9248c451c8adf,0xef72b619cc15d2d560ad54a712e9046a290c84411dce66b33968ae562a9248a3b1c8adf,0x1dee56c33982ba5aac15aa94e25d208d452190477399bcd6672d15cac55249188a3b1c8ae0,0x3bdcad860af95aab54a35148642208ee73379acd0672d158aa49231147639190add,0xef72b619cba5aac15aab54a712e9046a290c84411dce66b33968ae562a9248a39190adf,0xef72b619cc15d2d560ad55aa53897482350c84411ccd6672d15cac55249147639190adf,0x1dee56c33982ba5aac15aab54a712e9046a290c84411ccd6672d15cac55249147639190ae0,0x1dee56c33982ba5aac15aab54a712e9046a1908823b9ccd6672d15cac55249147639190ae0,0x77b95b0ce60af974b5582b556a94e25d208d4521908823b9ccde672d15cac55228ade,0x77b95b0ce60af974b5582a5389748235148642208ee73379acd0672d15cac55228ade,0x1dee56c33982be5d2d560a94e25d208d4521908823b9ccde6b3419cb4572b1549246228ae0,0xef6c3057cba56aad528d4521908823b9d4e66f359a0ce5a2b958aa49231147639190adf]
def bk18 : Array Nat := #[0xef72b619cc15f2e96ab055aa5389748235148642208ee73379acd0672b958aa45190adf,0x77b6182be592b556a94c235148642208ee73379acd0672d158aa49231147639190ade,0x3bdb0c15f2c95aab54a35148642208ee73379acd0672d158aa49231147639190add,0xef72b619cc15f2e96ab056aad529c4ba411a8a432110477399bcce5a2b958aa45190adf,0x1dee56c33982be5d2d560ab54a712e9046a290c84411dce66f359a0ce5a2b958aa45190ae0,0xef72b619cbe5d2d560ab54a712e9046a290c84411dce66f33968ae562a9248c45190adf,0x3bdb0c15f2b556a946a290c84411dcea73379acd0672d158aa49231147639190add,0x1dee56c33982be5d2d560ad54a712e9046a290c84411dce66f359a0ce5a2b95492451c8ae0,0x77b95b0ce5f2e96ab056aa5389748235148642208ee733799cb4572b15492451c8ade,0x381aece5f2d55aa94e25d2086411ccce551c8ad1,0x3959cbe582b55297462290c823799c92451c8ad1,0x3bdb0c15f2b556a94c235148642208ee73379acd0672d158aa49231147639190add,0xef72b619cbe5d2d560ad54a712e9046a290c84411dce66f33968ae562a9248c451c8adf,0x77b95b0ce5f2e96ab056aad529c4ba411a8a43211046f33968ae562a9248a39190ade,0x1dee56c3397cba5aac15aab54a712e9046a290c84411dce66f33968ae562a9248a39190ae0,0x77b6182be5d2d55aab54a35148642208ee73379acd0672d158aa49231147639190ade,0x1dee56c33982be5d2d560ad55aa5389748235148642208ee73379acce5a2b958aa451c8ae0,0xef72b619cc15f2e96ab054a712e9046a290c84411dce66f359a0ce5a2b958aa451c8adf,0x77b95b0ce5f2e96ab054a712e9046a290c823b9ccde6b33968ae562a9248c451c8ade,0x30d7cb5582a4ea73379acce5a2b95492451c8ad1,0x381aece5f2d5529c4ba410c82399acce551c8ad1,0x3959cbe582a52e8c45219046f3599c92451c8ad1,0xef72b619cbe5d2d560a94e25d208d4521908823b9ccde6b33968ae562a9248c451c8adf,0x1dee56c33982be5d2d560a94e25d208d452190477399bcd66833968ae562a9248c451c8ae0,0x77b6182be5c2d55aab54a35148642208ee73379acd0672d158aa49231147639190ade,0x1dee56c33982be5d2d560ad54a712e9046a290c84411dce66f359a0ce572a9248a3b1c8ae0,0x3bdb0c15f2e95aab54a35148642208ee73379acd0672d158aa49231147639190add,0x1dee56c33982be5d2d560ab54a712e9046a290c84411dce66f359a0ce572b1548a39190ae0,0x77b95b0ce5f2e96ab055aa53897482290c84411dce66f3599cb4572b1548a39190ade,0xef72b619cbe5d2d560ab54a712e9046a290c84411dce66f3599cb4572b1548a39190adf,0x3bdcad8672f974b5582b5529c4ba411a8a432110473379acce5a2b95492451c8add,0x3959cbe5aac15aa946a29006f3295092451c0a51]
def bk19 : Array Nat := #[0x3616aad54271208d43204e66b3315492441c8a91,0x3bdcad8672f974b5582b5529c4ba411486411dce66f3599cb4572b15492451c8add,0x3959cbe53a5d208a43208e66f3599ca2411b88d1,0x395b0ce5f2d560ad54a29006f3295092451c0a51,0xef72b619cbe5d2d560ad54a712e9046a290c84411dce66f3599cb4572b15492451c8adf,0x1dee56c3397cba5aac15aab54a712e9046a290c84411ccde6b33968ae562a9248a39190ae0,0x1dee56c3397cba5aac15aab54a712e904521908823b9ccde6b33968ae562a9248a39190ae0,0x1ded8673057cb5582b556a948235148642208ee73379acd0672d158aa49231147639190ae0,0x1dee06c33982be5aab556a948235148642208ee73379acd0672d158aa49231147639190ae0,0x1dee56c3057cba5aac15a9c4ba411a8a43208ee73379acd0672d15cac55249188a3b1c8ae0,0x1dee56c33982be5aab556a948235148642208ee73379acd0672d158aa49231147639190ae0,0x1ded8673057cb556aad529b48235148642208ee73379acd0672d158aa49231147639190ae0,0x1ded8673057cb557ab556a948235148642208ee73379acd0672d158aa49231147639190ae0,0xef6c33982be5aab556a948235148642208ee73379acd0672d158aa49231147639190adf,0x1dee5673057cba5aac15aa94e25d208d452190477399bcd66833968ae55249188a3b1c8ae0,0x1ded860ae96ab056aad529c46a290c84411dce66f359a0ce5a2b958aa49231147639190ae0,0x3bdb0d360ae96ab056aad529c46a290c84411dce66f359a0ce5a2b958aa49231147639190ae1,0x3bdb0cc60ae96ab056aad529c46a290c84411dce66f359a0ce5a2b958aa49231147639190ae1,0x3bdcad8673057cba5aac15aab54a712e9046a290c84411dce66f31968ae562a9248c45190ae1,0x3bdb0c360ae96ab056aad529c46a290c84411dce66f359a0ce5a2b958aa49231147639190ae1,0x3bdb0c15d2d560ad55aa5389a46a290c84411dce66f359a0ce5a2b958aa49231147639190ae1,0xef6c30574ad55a712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190adf,0x3bdb0d360ae960ad55a89389748235148642208ee73359a0ce5a2b958aa49231147639190ae1,0x77b6182ba56aad389748235148642208ee73359a0ce5a2b958aa49231147639190ade,0x25d1a8a43211046c359a0ce49231147639190ad1,0x26d2e914822d1484411ccd0672b1548c45190ad1,0x2712e90462290c82399acce5a2b95492451c8ad1,0x1ded860ae960ad55a89389748235148642208ee73359a0ce5a2b958aa49231147639190ae0,0x1dee56c33982be5d2d560ad55aa5389748235148642208ee73379acd0672d158aa3e190ae0,0xef6c30574ad55a71349748235148642208ee73379acd0672b958aa49231147639190adf,0x3bdb0c360af974b056aad449c4ba411a8a432110477399bcd6683395cac55249188a3b1c8ca1,0xef72b619cc15f2e96ab056aad529c4ba411a8a432110477399bcca5a2b958aa3e190adf]
def bk20 : Array Nat := #[0x1ded869b0574b056aad449c4ba411a8a432110477399acd0672b958aa49231147639190ae0,0x77b95b0ce60af974b5582b556a94e25d2084411dce66f359a0ce5a2b958aa3e190ade,0x1dee56c33982be5d2d560ab54a712e9046a290c84411dce66f359a0ce5a2b958aa3e190ae0,0x3bdcad8673057cba5aac15aab54a712e9046a290c84411dce66f359a0ce5a2b958aa3e190ae1,0x3bdb0c15d2b5569c4ba411a8a432110477399acd0672b958aa49231147639190add,0x36182ab4aa351484401a0ca56249188a3b190851,0x36182ad55a71208d43211026b299247639188991,0x36182ad55a350877341589a49231107638190a11,0xef6c3057cba56aad449c4ba411a8a432110477399acd0672b958aa49231147639190adf,0xef72b619cc15f2e96ab056aad529c4ba411a8a43211047737994b4562a9248c45190adf,0x1dee06c3057cba56aad449c4ba411a8a432110477399acd0672b958aa49231147639190ae0,0xef72b619cc15f2e96ab056aad529c482351484411dce66f32968ae562a9248c45190adf,0x3bdcad8673057cba5aac15aab54a712e9046a290c84411dce66f32968ae562a9248c45190ae1,0x3bdcad8673057cba5aac15aab54a712e9046a290c84411d8de6b3419cb4562a8f87639190ae1,0x1ded869b0574b056aad389748235148642208ee73359a0ce5a2b958aa49231147639190ae0,0xef72b619cc15f2e96ab056aad529c4ba4108823b9ccde6b3419cb4562a8f87639190adf,0x3bdcad8673057cb85aac15aab54a712e9046a290c84411dce66f359a0ce5a2b1547c3b1c8ca1,0x1dee56c33982be5d2d560ad55aa53897482110477399bcd66833968ae562a8f87639190ae0,0x1dee56c33982be5d2d560ad55aa5208d452110477379acd0672d158aa49231147639190ae0,0x1dee56c33982be5d2d560ad55aa5389748235148642208ec6f32968ae562a9248a39190ae0,0x1dee56c33982be5d2d560ad55aa53897482110477399bcd66833968ae562a9248a39190ae0,0x1ded861b057cba56aad389748235148642208ee73379acd0672b958aa49231147639190ae0,0x3bdcad8673057cba5aac15aab54a712e9046a290c84411dce66f32968ae562a9248a39190ae1,0x77b95b0ce60af974b5582b556a9482351484411dcde652d15cac55249188a39190ade,0x39582be582b5448d451dcde652d1248c451c0151,0x35da6ce5aac15aa94823114822b95492451c8ad1,0x1dee56c3397cba5aac15aab54a712e9046a290c84411dcde652d15cac55249188a39190ae0,0x3bdcad8673057cba5aac15aab54a712e9046a290c84411dcde652d15cac55249188a39190ae1,0xef7036182be5d2b5569c4ba411a8a432110477399acd0672b958aa49231147639190adf,0x1dee56c33982be5d2d560ad55aa5389046a2908823b9ccde652d15cac55249188a39190ae0,0x3bdcad8672f974b5582b556a94e25d208d4521908823b9ccde652d15cac55249188a39190ae1,0xef6c34d9cc15d2b5569c4ba411a8a432110477399acd0672b958aa49231147639190adf]
def bk21 : Array Nat := #[0x30174ad4e25d2086411ccd6672b95492451c8ad1,0x2712e90462290c82399acce582b95492451c8ad1,0xef72b619cc15f2e96ab056aad529c4ba40ee73379acd0672d15cac55249147639190adf,0x36182ab4aa351484401a0bc56249188a3b190851,0x2712e90462290c82399acce5c2b95492451c8ad1,0x1dee56bb3982be5d2d560ad55aa5389746a28ee73379acd0672d15caa49231147639190ae0,0x1dee56c33982be5d2d560ad55aa5389746a28ee73379acd0672d15caa49231147639190ae0,0x1dee56c33982be5d2d560ad55aa5389042208ee73379acd0672d15cac55249147639190ae0,0x1dee56c33982be5d2d560ad55aa5389748235148642208ee73379a0ce5a2b1548c45190ae0,0x77b95b0ce60af974b5582b556a94e25d2084411dce66f359a0ce5a2b1548c45190ade,0x361a6ce5aac156a948211045a2b1548c45190ad1,0x26d349748a410882399bcd0672b1548c45190ad1,0x3959cbf5f2c156a94ba11046f3419c8c45190ad1,0x1dee56c33982be5c2d560ab54a712e9046a290c84411dce66f359a0ce5a2b1548c45190ae0,0x77b6182ba56aad389a4ba411a8a432110477399acd0672b958aa49231147639190ade,0x2692e914822d1484411ccd0672b1548c45190ad1,0x3bdb0c360af974b056aad449c4ba411a8a432110477399acd0672b958aa49231147639190ae1,0xef72b619cc15f2e96ab056aad529c4ba4108823b9ccde6b3419cb4572b1548c45190adf,0x77b95b0ce60af974b5582b556a9482351484411dce66f3419cb4562a9248c45190ade,0x381b0ce5faf96aab54a410882399a0ce55190ad1,0x269229045a290882399bcd0672b1548c45190ad1,0x395aece5f2d560a94822904733799cb455228ad1,0x1dee56c33982be5d2d560ad55aa5389046a2908823b9ccde6833968ae562a9248c45190ae0,0x1dee56c3397cba5aac156a94e25d208d4521908823b9ccde6833968ae562a9248c45190ae0,0x3bdb0d36730574b5582b556a54e25d208d4521908823b9ccd6683395cac55249188a3b1c8ca1,0x36182ad55a35087734158a449231107638190a11,0x3bdb0d36730574b056aad4a9c4ba411a8a432110477399acd0672b958aa49231147639190ae1,0xef72b619cc15f2e96ab056aad529c4ba40ee73379acd0672d15cac55231147639190adf,0x77b95b0ce60af974b5582b556a946a28ee73379acd0672d158aa49231147639190ade,0x3057cb65aab556a9399acd0672b1547639190ad1,0x30d80be5aac15aa9399bcd6672d15492451c8ad1,0x1ccde6c359a0ce5a2b1549449231147639190ad1]
def bk22 : Array Nat := #[0x1ded86730574b556aad4a9c4ba411a8a432110477399acd0672b958aa49231147639190ae0,0x1dee56c33982be5d2d560ad55aa5389746a28ee73379acd0672d158aa49231147639190ae0,0x1dee56c33982be5c2d560ad55aa53897482110477399bcd66833968ac55231147639190ae0,0x1dee56c33982be5d2d560ad55aa53897482110477399bcd66833968ac55231147639190ae0,0x1dee56c33982be5d2d560ad55aa5389042208ee73379acd0672d15cac55231147639190ae0,0x77b95b0ce60af974b5582b556a94e25cee73379acd0672d15cac55249188a39190ade,0x30d82be582b556a9379acd067249188a39190ad1,0x2d96ab0572b556a92d15cac55249188a39190ad1,0x1d4e66f361acd0672d15cac55249188a39190ad1,0x1ded869b3982ba56aad4e9c4ba411a8a432110477399acd0672b958aa49231147639190ae0,0xef72b619cc15f2e96ab056aad529c4ba40ee73379acd0672d15cac55249188a39190adf,0x36182ab4aa351484401a0c256249188a3b190851,0xef6c33982ba56aad4e9c4ba411a8a432110477399acd0672b958aa49231147639190adf,0x1dee56c33982be5d2d560ad55aa5389746a28ee73379acd0672d15cac55249188a39190ae0,0x3bdc0d8673057cba56aad4e9c4ba411a8a432110477399acd0672b958aa49231147639190ae1,0xef72b619cc15f2e96ab056aad529c482351477399bcd0672d15cac55249188a39190adf,0x1dee56c33982be5d2d560ad54a712e9046a28ee73379acd0672d15cac55249188a39190ae0,0xef72b619cc15f2e96ab056aad529c482110477399bcd0672d15cac55249188a39190adf,0x1dee56c33982be5d2d560ad55aa5208d452110477399bcd0672d15cac55249188a39190ae0,0x1dee56c3397cba5aac15aab54a71208d452110477399bcd0672d15cac55249188a39190ae0,0xef72b619cc15f2e96ab056aad529c4b9dce66f359a0ce5a2b958aa49231147639190adf,0xef72b619cc15f2e96ab056aad529c481dce66f359a0ce5a2b958aa49231147639190adf,0x1dee56c33982be5d2d560ad55aa53897481dce66f359a0ce5a2b958aa49231147639190ae0,0xef72b619cc15f2e96ab056aad528d451dce66f359a0ce5a2b958aa49231147639190adf,0x3bdcad7673057cba5aac15aab54a712e8d451dce66f359a0ce5a2b958aa49231147639190ae1,0xef72b619cc15f2e16ab055aa5389748235148642208ee73379acd0672d158aa45190adf,0x1dee56c33982be5d2d560ad55aa5389748235148642208ee73379acd0672d158aa45190ae0,0x2712e90462290c82399b8d6672b95492451c8ad1,0x77b95b0ce60af974b5582ad529c4ba411484411dce66f359a0ce5a2b958aa45190ade,0x361a6ce5aac156a94822908822d158aa45190ad1,0x26d349748a411484411ccde6833958aa45190ad1,0x3959cbf5f2c156a94ba290882379a0ce45190ad1]
def bk23 : Array Nat := #[0xef72b619cc15f2e96ab056aad529c4ba411484411dce66f359a0ce5a2b958aa45190adf,0xef72b619cc15f2e96ab056aad529c4ba411a8a4321104773799cb4562a9248c45190adf,0x1dee56c33982be5d2d560ad55aa53897482351484411dce66f33968ae562a9248c45190ae0,0x1dee56c33982be5d2d560ad55aa5389748235148642208ec6f359a0ce5a2a1147639190ae0,0xef6c30574b556aad389748235148642208ee73359a0ce5a2b958aa49231147639190adf,0x36182ad55a3508682d158a849231107638190a11,0x3bdcad8673057cb85aac15aab54a712e9046a290c84411dce66f359a0ce5a2a1147639190ae1,0x3bdcad8673057cba5aac15aab54a712e9046a290c84411dce66f359a0ce5a2a1147639190ae1,0x77b95b0ce60af974b5582b556a94ba3514823b9bcd66833968a849231147639190ade,0x395b0ce5aac14a8d45200ee6f2d1509246228451,0x33980be582b5529746229046f3599c92451c8ad1,0x1dee56bb3982be5d2d560ad55aa5389746a290477399bcd66833968a849231147639190ae0,0x1dee56c33982be5d2d560ad55aa5389746a290477399bcd66833968a849231147639190ae0,0x3bdcad8673057cba5aac15aab54a712e9046a290c84411d8de6b3419cb4562a9147639190ae1,0x1dee56c33982be5c2d560ad55aa538974822908823b9ccde6b3419cb4562a9147639190ae0,0x1dee56c33982be5d2d560ad55aa538974822908823b9ccde6b3419cb4562a9147639190ae0,0x77b95b0ce60af974b5582b556a94e25d208d4521908823b1bcce5a2b95492451c8ade,0x30d80be5aac15aa93b1bcce5a2b95492451c8ad1,0x2713497482311486411bcce5a2b95492451c8ad1,0x35d80ad532712e9043208e66b3395492451c8ad1,0x1dee56c33982be5d2d560ad55aa5389748235148642208ee733799cb4572b15492451c8ae0,0x30168ad532712e9043208e66b3395492451c8ad1,0xef72b619cc15f2e96ab056aad529c4ba411a8a4321104773799cb4572a9248c451c8adf,0x77b95aece60af974b5582b5529c4ba3514823b9ccde6b3419cb4572a9248c451c8ade,0x35da6ce5aac15aa946229045a2b95492451c8ad1,0x381aece602f96aad54a712e82399acce551c8ad1,0xef72b619cc15f2e96ab056aad529c4ba3514823b9ccde6b3419cb4572a9248c451c8adf,0x33580ad532712e9043208e66b3395492451c8ad1,0xef72b619cc15f2e96ab056aad529c4ba411a8a411dce66f33968ae562a9248c451c8adf,0x1dee56c33982be5d2d560ad55aa5389748235148642208ec6f33968ae562a9248a39190ae0,0xef72b619cc15f2e96ab056aad529c4ba411484411dce66f33968ae562a9248a39190adf,0xef72b619cc15f2e96ab056aad5297482351484411dcde672d15cac55249188a39190adf]
def bk24 : Array Nat := #[0x1dee56c3397cba5aac15aab54a712e9046a290c84411dcde672d15cac55249188a39190ae0,0xef72b5d9cc15f2e96ab056aad529c4ba290477399bcd66833968ae55249147639190adf,0xef72b619cc15f2e96ab056aad529c4ba290477399bcd66833968ae55249147639190adf,0xef72b619cc15f2e96ab056aad529746a290477379acd0672d15caa49231147639190adf,0x3bdcad7673057cba5aac15aab54a712e8d45208ee73379acd0672d15caa49231147639190ae1,0xef6c30574b556aad509c4ba411a8a432110477399acd0672b958aa49231147639190adf,0x77b95b0ce60af974b5582b556a94e25d208a411dce66f3419cb4572b1548c45190ade,0x361a6ce5aac156a948229045a2b1548c45190ad1,0x26d349748a411482399bcd0672b1548c45190ad1,0x3959cbf5f2c156a94ba29046f3419c8c45190ad1,0x77b6182ba56aad509c4ba411a8a432110477399acd0672b958aa49231147639190ade,0x36182ad55aa11a843b9a0ac49231107638190a11,0xef72b619cc15f2e96ab056aad529c4ba4114823b9ccde6b3419cb4572b1548c45190adf,0x1dee56c33982be5d2d560a94e25d208d4521908823b9ccde6b3419cb4572b1548c45190ae0,0xef72b619cc15f2e96ab056aad529c4ba3514823b9ccde6b3419cb4562a9248c45190adf,0x1dee56c33982be5d2d560a94e25d208d4521908823b9ccde6b3419cb4562a9248c45190ae0,0x1dee56c33982be5d2d560ad55aa538974823514823b9ccde6833968ae562a9248c45190ae0,0xef72b619cbe5d2d560a94e25d208d4521908823b9ccde6833968ae562a9248c45190adf,0xef72b619cc15f2e96ab054a712e9046a290477399bcd66833968ae562a9248c45190adf,0x77b95b0ce60af970b5582ad529c4ba411484411dce66f359a0ce5a2b1548c45190ade,0xef72b619cc15f2e96ab056aad529c4ba411484411dce66f359a0ce5a2b1548c45190adf,0xef72b619cc15f2e96ab056aad529c4ba411484411dce66f3419cb4572b1548c45190adf,0xef72b619cbe5d2d560ab54a712e9046a290c84411dce66f3419cb4572b1548c45190adf,0xef72b619cc15f2e96ab055aa538974822908823b9ccde6b3419cb4572b1548c45190adf,0x1dee56c33982be5d2d560ad55aa538974822908823b9ccde6b3419cb4572b1548c45190ae0,0xef72b619cc15f2e96ab056aad5297482351484411dce66f3419cb4562a9248c45190adf,0xef72b619cbe5d2d560ab54a712e9046a290c84411dce66f3419cb4562a9248c45190adf,0xef72b5d9cc15f2e16ab056aad529c4ba290477399bcd66833968ac55231147639190adf,0xef72b619cc15f2e96ab056aad529c4ba290477399bcd66833968ac55231147639190adf,0x1dee56c33982be5d2d560ad55aa52e8d45208ee73379acd0672d158aa49231147639190ae0,0x3bdcad7673057cba5aac15aab54a712e8d45208ee73379acd0672d158aa49231147639190ae1,0x3bdcad8673057cb85aac15aab54a712e90452110477399bcd66833968ac55231147639190ae1]
def bk25 : Array Nat := #[0xef72b5d9cc15f2e96ab056aa5389745208ee73379acd0672d15cac55249188a39190adf,0x1dee56c33982be5d2d560ad55aa5389745208ee73379acd0672d15cac55249188a39190ae0,0x1dee56c33982be5d2d560ad55aa53897482290477399bcd0672d15cac55249188a39190ae0,0x1dee56c33982be5d2d560ad54a712e9045208ee73379acd0672d15cac55249188a39190ae0,0xef72b619cc15f2e96ab056aad529746a290477399bcd0672d15cac55249188a39190adf,0x1dee56bb3982be5d2d560ad54a712e8d45208ee73379acd0672d15cac55249188a39190ae0,0x3bdcad7673057cba5aac15aab54a712e8a411dce66f359a0ce5a2b958aa49231147639190ae1,0x1ded860af974ad55aa5389748235148642208ee73359a0ce5a2b958aa49231147639190ae0,0x3bdb0c15f2e95aab54a71349748235148642208ee73379acd0672b958aa49231147639190ae1,0x1ded860af974ad55aa5389748235148642208ee73379acd0672b958aa49231147639190ae0,0x3bdb0d360af974b056aad529c4ba411a8a432110477399acd0672b958aa49231147639190ae1,0xef6c3057cba56aad529c4ba411a8a432110477399acd0672b958aa49231147639190adf,0x1ded860af974b056aad529c4ba411a8a432110477399acd0672b958aa49231147639190ae0,0x1ded8663057cba56aad529c4ba411a8a432110477399acd0672b958aa49231147639190ae0,0x1dee06c3057cba56aad529c4ba411a8a432110477399acd0672b958aa49231147639190ae0,0x1dee56c33982be5d2d560ad55aa5389748235148642208ee7337968ae562a9248c45190ae0,0x1ded869b057cba56aad529c4ba411a8a432110477399acd0672b958aa49231147639190ae0,0x3bdb0c360af974ad55aa5389748235148642208ee73379acd0672b958aa49231147639190ae1,0x1dee56c33982be5d2d560ad55aa5389748235148642208ee6f2d15cac55249188a39190ae0,0x1ded860af974ad55aa5389748235148642208ee73369acd0672b958aa49231147639190ae0,0x1ded860af974ad55aa5389a4ba411a8a432110477399acd0672b958aa49231147639190ae0,0x3bdb0c360af974b056aad529c4ba411a8a432110477399acd0672b958aa49231147639190ae1,0x1ded8673057cba56aad529c4ba411a8a432110477399acd0672b958aa49231147639190ae0,0x1ded860af974b556aad529c4ba411a8a432110477399acd0672b958aa49231147639190ae0,0x1ded860ae96ab056aad529c4ba411a8642208ee73359a0ce5a2b958aa49231147639190ae0,0x3bdb0cc60ae96ab056aad529c4ba411a8642208ee73359a0ce5a2b958aa49231147639190ae1,0x3bdb0c15e2e96ab056aad529c4ba411a8642208ee73359a0ce5a2b958aa49231147639190ae1,0x3bdcad8673057cba5829d389748235148642208ee73379acd0672d158aa49231147639190ae1,0x3bdcad8673057cba582b556a94e25d208d4521908823b9bcd66833968a049231147639190ae1,0x3bdcad7673057cba582b556a94e25d1a8a432110477399bcd66833968a049231147639190ae1,0x77b6182ba56aad3897482350c84411dce66f359a0ce5a2b958aa49231147639190ade,0x25d1a8642208de6c359a0ce49231147639190ad1]
def bk26 : Array Nat := #[0x26d2e914822d0882399bcd0672b1548c45190ad1,0x2712e90462190473379acce5a2b95492451c8ad1,0x1ded86630574ad55a893897482350c84411dce66f359a0ce5a2b958aa49231147639190ae0,0x3bdc0d860af974ad55a893897482350c84411dce66f359a0ce5a2b958aa49231147639190ae1,0x1dee56c33982be5d2d560ad55aa5389746a290c84411dce66f359a0ce49231147639190ae0,0x3bdb0ce60ae96aad55a953897482350c84411dce66f359a0ce5a2b958aa49231147639190ae1,0x1ded860ae95aab4e2692e9046a290c84411dce66f359a0ce5a2b958aa49231147639190ae0,0xef6c3057cba56aad3897482350c84411dce66f359a0ce5a2b958aa49231147639190adf,0x1dee06c3057cba56aad3897482350c84411dce66f359a0ce5a2b958aa49231147639190ae0,0xef72b619cc15f2e96ab056aad529c482351484411dce66f2d15cac55249188a39190adf,0x1dee56c3397cba5aac15aab54a712e9046a290c84411dce66f2d15cac55249188a39190ae0,0x3bdb0d36730574ad55a712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190ae1,0x3bdcad8673057cba5aac15aab54a712e9045200ee73379acd0672d15cac55249147639190ae1,0x3bdcad7673057cba5aac15aab54a712e8d45200ee73379acd0672d15caa49231147639190ae1,0x3bdcad8673057cba5aac15aab54a712e8d45200ee73379acd0672d15caa49231147639190ae1,0x1dee56c33982be5d2d560ad55aa5389046a290c84411dce65a2b958aa49231147639190ae0,0x1ded860af974ad55a9d3897482350c84411dce66f359a0ce5a2b958aa49231147639190ae0,0x1dee56c33982be5d2d560ad55aa5389748235148642208ee6f2d15caa49231147639190ae0,0x3bdc0d8673057cba56aad4e9c4ba411a8642208ee73379acd0672d15cac55249188a3b1c8ca1,0xef72b619cc15f2e96ab056aad529046a290c84411dcde5a2b958aa49231147639190adf,0x1dee56c3397cba5aac15aab54a712e9046a290c84411dcde5a2b958aa49231147639190ae0,0x1dee56c33982be5d2d560ad55aa51a8a432110477379acd0672d15caa49231147639190ae0,0xef6c30574b556aad3897482350c84411dce66f359a0ce5a2b958aa49231147639190adf,0xef72b619cc15f2e96ab056aad529c4ba3514823b9ccde6b3419cb449231147639190adf,0x1ded860ae96aad55aa13897482350c84411dce66f359a0ce5a2b958aa49231147639190ae0,0xef72b619cc15f2e96ab056aad529c4ba411a8a4321104773799cb449231147639190adf,0x1dee56c3397cba5aac1529c4ba411a8a432110477399bcce5a2b958aa49231147639190ae0,0x1dee56c33982be5d2d560ad55aa52e9046a290c84411dcde672d158aa49231147639190ae0,0x1dee56bb3982be5c2d560ad55aa5389746a290c84411dce66f359a0ce49231147639190ae0,0xef72b619cc15f2e96ab056aad529746a290c84411dcde6b3419cb449231147639190adf,0x3bdcad7673057cba5aac15aab54a712e8d4521908823b9ccde6b3419cb449231147639190ae1,0xef72b619cc15f2e96ab056aad529746a290c84411dcde672d15caa49231147639190adf]
def bk27 : Array Nat := #[0xef72b619cbe5d2d560ad54a712e9046a290c84411dcde672d15caa49231147639190adf,0x77b6182ab4e2692e9046a290c84411dce66f359a0ce5a2b958aa49231147639190ade,0xef6c305569c4d25d208d4521908823b9ccde6b3419cb85a2b958aa49231147639190adf,0x3bdb0c155a712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190add,0x361829748220fc73379acd0672a91c7c35180751,0x3052e9046a290c84411acc6532490c76391889d1,0x361829c4ba40fc73379acd0672b1547c35180751,0x361829748220fc73379acd0672b1547c35180751,0x1dee56c33982be5d2d560ad55aa53897482350c77399bcd66833968ae562a9247639190ae0,0x77b95b0ce60af974b5582b556a94e23514863b9bcd66833968ae49231147639190ade,0x1ded8673056aab52a712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190ae0,0x1dee56c33982be5d2d560ad55aa5389746a290c77399bcd66833968ae49231147639190ae0,0x1ded869b0564b055a712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190ae0,0x1dee56c30570b055a712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190ae0,0x1dee56c33982be5d2d560ad55aa5389046a1908823b9ccd66833968ae562a9247639190ae0,0x77b95b0ce60af974b5582b556a94e25d1a863b9ccde6b3419cb4572a9248a3b1c8ade,0x3bdcad8673057cab53a712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190ae1,0x1ded869b3982ab53a712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190ae0,0x1dee56c33982be5d2d560ad55aa53897482350c77399bcd66833968ae562a9248a3b1c8ae0,0xef6c33982ab53a712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190adf,0x1dee56c33982be5d2d560ad55aa5389746a290c77399bcd66833968ae55249188a3b1c8ae0,0x3bdc0d8673057cab53a712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190ae1,0xef72b619cc15f2e96ab056aad529c4823514863b9ccde6b2d15cac55249188a3b1c8adf,0xef72b6182be55a712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190adf,0xef6c34d9cc155a712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190adf,0xef703619cc155a712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190adf,0xef72b619cc155a712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190adf,0xef72b619cc15f2e96ab056aad529c4ba350c77399bcd66833968ae55249147639190adf,0xef72b619cc15f2e96ab056aad529c482350c77399acd0672d15cac55249147639190adf,0xef72b619cc15f2e96ab056aad529c46a290c77379acd0672d15caa49231147639190adf,0x3bdcad7673057cba5aac15aab54a712e8d45218ee73379acd0672d15caa49231147639190ae1,0xef72b619cc15f2e96ab056aad529c482350c84411acd0672d15cac55249147639190adf]
def bk28 : Array Nat := #[0x1ded860ac95aab542712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190ae0,0x3618297481f8e66f359a0ce562a91c7c35180751,0xef6c3055aab542712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190adf,0x1dee56c33982be5d2d560ad55aa538974823514823b9ccde6b3419cb4572b1549246228ae0,0x77b95b0ce60af974b5582b556a94e25d1a8a43208ee73379acd0672b9248a3b1c8ade,0x77b95b0ce60af974b5582b556a94e25d1a8a43208ee6f3599cb457249188a3b1c8ade,0xef6c3056aab542712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190adf,0x1dee56c33982be5d2d560ad55aa5389746a290c823b9ccde6b3419cb457249188a3b1c8ae0,0x77b6182ab4e25d208d4521908823b9ccde6b3419cb85a2b958aa49231147639190ade,0xef6c3056eb555a712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190adf,0xef6c30570b555a712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190adf,0xef72b619cc15f2e96ab056aad529c4ba351486411dce66f359a0ce57249147639190adf,0x1dee56bb3982be5d2d560ad55aa5389746a290c823b9bcd66833968ae49231147639190ae0,0x1dee56c33982be5d2d560ad55aa5389746a290c823b9bcd66833968ae49231147639190ae0,0x3bdcad7673057cba5aac15aab54a712e8d452190477399bcd66833968ae49231147639190ae1,0xef72b5d9cc15f2e96ab056aa5389746a290c823b9ccde6b3419cb4572a9248a3b1c8adf,0x1dee56c33982be5d2d560ad55aa5389746a290c823b9ccde6b3419cb4572a9248a3b1c8ae0,0x77b95aece60af974b5582b5529c4ba351486411dcde6b33968ae55249188a3b1c8ade,0x381aece602f96aad54a712e86411acce551c8ad1,0x395aece5f2d560a94ba2904763799cb455228ad1,0xef72b619cc15f2e96ab056aad529c4ba351486411dcde6b33968ae55249188a3b1c8adf,0x1dee56bb3982be5d2d560ad54a712e8d452190477399bcd66833968ae55249188a3b1c8ae0,0xef72b5d9cc15f2e96ab056aad529746a290477379acd0672d15caa49231147639190adf,0xef72b5d9cc15f2e96ab056aad529c4ba351486411bcd66833968ae55249147639190adf,0xef72b619cc15f2e96ab056aad529c4ba351486411bcd66833968ae55249147639190adf,0x3bdcad7673057cba5aac15aab54a712e8d452190477399bcd66833968ae55249147639190ae1,0x3bdcad7673057cba5aac15aab54a712e8d452190477379acd0672d15caa49231147639190ae1,0xef72b619cc15f2e96ab056aad5297482290882379acd0672d15cac55249147639190adf,0x3bdb0cc60ae95aab512712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190ae1,0x3bdc0d860af974ad55a89389748235148642208ee73379acd0672d15cac55249188a3b1c8ca1,0x3bdb0d360ae95aab502712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190ae1,0x1ded860af974ad55a712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190ae0]
def bk29 : Array Nat := #[0x3bdc0d860af974ad55a712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190ae1,0x1ded86730574ad55a712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190ae0,0x1ded860ae96aad55a712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190ae0,0x1ded860ae95aab522712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190ae0,0x3adcad8673057cb75aac15aab54a712e904521d0c84411d0e66f359a0ce572b1548a3b1c8ca1,0x3bdcad860ae96ab056aad509c48235148642204ee73379acd0662d15cac55249188a3b1c8ca1,0x77395aece602f974b5582b5529c4ba41188a43208ec73379acce5a2b95492451c8ade,0x77b6182ba5aab556a84e2411a8642204ee73359a0cc5a2b958aa49231107639190a9e,0x3bdcad860ae96ab056aad509c48235148642208ee73379acd0662d15cac55249188a3b1c8ca1,0xef6c30574b556aad509c48235148642208ee73359a0cc5a2b958aa49231147639190adf,0x1ded860af974b556aad529c48235148642208ee73359a0ce5a2b958aa49231147639190ae0,0x3bdcad860ae96ab056aad529c48235148642204ee73379acd0662d15cac55249188a3b1c8ca1,0x3bdcad860ae96ab056aad509c48235148642204ee73379acd0672d15cac55249188a3b1c8ca1,0xef6c30574b556aad509c482350c84409dce66f359a0ce5a2b958aa49231147639190adf,0x1ded860ae96aad55aa1389046a290c84411dce66f359a0ce5a2b958aa49231147639190ae0,0xef72b619cc15f2e96ab056aad529746a2908823b9bcd0672d158a849231147638190adf,0xef6c30574b556aad509c4ba411a8642208ee73359a0ce5a2b958aa49231107639190adf,0x1ded860ae96aad55aa1389748235148642208ee73359a0ce5a2b958aa49231147639190ae0,0x3bdb0c15d2d55aab542712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190ae1,0x3bdcad8673057cb75aac156a94e25d208d4521908823b9ccde683395cac55231147634190ae1,0x3bdcad760af974b5582b556a94e2411a8a43204ee73379acd0672d15caa49231147639190ae1,0xef72b619cc15f2e16ab055aa53697482351484411dce66f3419cb4562a9188a3b190adf,0xef72b5d82ba5aac15aa84e2411a8a432110477399bcd6662d15caa49231147639190adf,0xef72b619cc15f2c156a94e25d208d4521908823b9ccde6b3419cac51231147637190adf,0x3bdcad760ae96ab056aa5389046a290c813b9ccde6b33168ae55249188a3b1c8add,0x39582b056a891a8a3b9bcc85a249188a3b1c0151,0xef72b5d82ba5aac15aa94e2411a8a432110477399bcd6662d15caa49231147639190adf,0x3bdcad8673057cb75aac15aab54a712e9046a290c84411dcde6b3419cae56299188a3b1c8ca1,0x3bdcad8673057cb85aac156a94da5d208d452110477379a0ce56299188a3b190add,0x39582be582892e8d451ecde68339308c451681d1,0x30d7ebe5b2d560ab549bcd0672b14c8c45190ad1,0x2692e914822d1484411bcd0672b14c8c45190ad1]
def bk30 : Array Nat := #[0x1ded86730574b556aad529c482350c84411dce66f359a0ce5a2b958aa49231147639190ae0,0x3bdcad760af974b5582b556a94e2411a8a43204ee73379acd0672d15cac55249188a3b1c8ca1,0x3bdcad8673057cb75aac15aab54a712e9046a2908823b9bcd6683395cac53231147635190ae1,0xef6bb0574b556aa1389046a290c84411dce66f359a0ce5a2b958aa49231147639190adf,0xef6c30574b556aa1389046a290c84411dce66f359a0ce5a2b958aa49231147639190adf,0x3bdcad760ae96ab056aa1389046a290c84411dce66f359a0ce5a2b958aa49231147639190ae1,0x3bdcad860ae96ab056aa1389046a290c84411dce66f359a0ce5a2b958aa49231147639190ae1,0x3bdaec15f2e96aad55aa5389046a290c84411dce66f359a0ce5a2b958aa49231147639190ae1,0xef72b5d80ba5aac15aa94e2411a8a43204ee73379acd0672d15cac55249188a39190adf,0x1dee56bb0574b5582b5529c482351486409dce66f359a0ce5a2b958aa49231147639190ae0,0x3bdcad7602e96ab056aa5389046a290c84411dce66f359a0ce5a2b958aa49231147639190ae1,0x1ded760ae96ab056aa5389046a290c84411dce66f359a0ce5a2b958aa49231147639190ae0,0x1ded860ae96ab056aa5389046a290c84411dce66f359a0ce5a2b958aa49231147639190ae0,0x3bdcad760ae96ab056aa5389046a290c84411dce66f359a0ce5a2b958aa49231147639190ae1,0x1dee56c33982be5c2d560ab54a5d1a8a42208ee6f3419cb4562a1188a3b190adc,0x36182b555aa11a843b9a0b4562a118883b190a11,0x39582be582892e8d451ecde68339688c451681d1,0x3619cc15f2d556a942208e86833958a83b190ad1,0x3619cc15f2d556a943a11046833958a83b190ad1,0x381b0ce60af96aab54a1d08823419ca83b190ad1,0x3619cb5572ad528d4521104562a1188a3b190ad1,0x3959cc15f2d560ab54a5d1a8a42208c6431889d1,0x3057cab549dcde6833968ac54251188a3b190ad1,0x2351484411dcde6c3419cb4562a1188a3b190ad1,0x2451a8a42208ee6f3419cb4562a1188a3b190ad1,0x269228d45211046f361a0ce562a1188a3b190ad1,0x381b0ce5faf96aab54a5d08823419cac54190ad1,0x2692e9145a290882379a0ce5a2b1508c45190ad1,0x395aece5f2d560a94ba2904763799cb454228ad1,0x1cace5f2e16ab054a5d14823799cb454228ad0,0x3959cbe53a29046f339049,0x3bdaec15d2d55aa84e25d208d4521908823b1ccd6672d15caa49231147639190add]
def bk31 : Array Nat := #[0x2612e8d452190882361acce49231147639190ad1,0x1dee56bb0574b5582b5509c4ba411a8a432110477399bcd6672d15caa49231147639190ae0,0x1ded760af974b556aad529c4ba411a8a432110476399acd0672d15caa49231147639190ae0,0x3bdcad7602e96ab056aa53897482351486411dce66f3599cb4572a9248c451c8add,0x39580a64ba411a8a43208e66f3599ca2411b88d1,0x395aebd5aac1529b4ba411482399bcce55228ad1,0x39580b056aa52e8c45219046f3599c92451c8ad1,0x77b5d82ba5aac15aa94e25d208d43208ec733599cb4572a9248a3b1c8ada,0x35d829c4ba411a86411d8e66b33944803b1b88d1,0x35d82b54e25d207e3b1ccd6672d15caa3e1a8751,0x35d6ab052a71208d3b1ccc05a2b95492451a04d1,0x35d82ad4e25d208d43208d66329924863b1c89d1,0x30560ad512711a863d9acb457271248a3b1c81d1,0x3055aa24e25d1a863d9ccd6672b938923b1c81d1,0x35d6aa54e25d208d43208ec7330168ae551a04d1,0x35d609c4ba411a86411ccc05a2b93892451a0051,0x305609c4ba350c7b399acce5a2b93892451a0051,0x35d82b5582b5529c481f8ec732d15caa3e1a8751,0x35d82b5582b5529c4b9ccd6672d15c9c3e1a8091,0x30560ad512712e8d399acce5a2b93892451a8091,0x33582b056aa5309746a19046b339248a3b1c8ad1,0x35d82b5582b5529c4ba40fc7330168ae551f0291,0x35d6ab052a712e9046a19047330168ae551f0291,0x35d82b5582953897481f8e66b33968ae551f0291,0x35d6ab052a712e90469f8e6602d15caa49228291,0x35d82b558295389748234fc733015caa3e1d8291,0x30560ad54a612e8d43208dc6b339248a3b1c8ad1,0x35d82a64e25d208d43208e66b33944803b1b88d1,0x3016ab056aa4ec75399acce5a2b95492451c8ad1,0x35d6ab056aa5249046219045a2b95492451c8ad1,0x35d82a64e25d208d43208ec733599ca23b1b88d1,0x35d82a64e25d208d43208ec733599ca2401b88d1]
def bk32 : Array Nat := #[0x35d6ab0572b5529041168ae55251248a3b1c8ad1,0x3055a9c4ba350c7b3b1ccd6672b924803b1c80d1,0x3bdaec14e25d208d43208ec733599c803b1b80d1,0x305609c4ba350c7b3b1ccd6672d1248a3b1b80d1,0x35d74b5582b95aa949241045a2b95492451c8ad1,0x375aeba5aac15aa949241045a2b95492451c8ad1,0x30574b5582b5526b33968ae55251248a3b1c8ad1,0x3056ab056aa4dc6b33968ae55251248a3b1c8ad1,0x3bdaec14e25d208d43208ec733599ca2401d82d1,0x3056ab056aa4ea6b33968ae55251248a3b1c8ad1,0x2e96ab0572b5528d43208b4572a9248a3b1c8ad1,0x3356ab0572b5528d43208b4572a9248a3b1c8ad1,0x3bdaec1532712e9046a190476399acce511d85d1,0x2d560ae56aa5248d43208b4572a9248a3b1c8ad1,0x35d82b5582b5529c46a18d66329924863b1c89d1,0x35d7ab5582a536974822504763999cb455228ad1,0x35d82b5582b5529c4ba411a864114c92431a03d1,0x35d6ab052a712e9046a19045a2b94c92451a03d1,0x35d82b5582b5529c4ba411a86411acc6531a8651,0x35d82b5582b5529c4ba40fc733599cae531a8651,0x2d560ae56aa4ec7333968ae55251248a3b1c8ad1,0x35d82ad532712e9046a19046b3195c923b1c8811,0x35d82b5582b5529c4ba411a86411acc63b1b8811,0x3bdaec1532712e9046a190476399acce3b1b8811,0x2e96ab056aa4ec753999cb4572a92892451c8ad1,0x32d74b5582b552763a9ccce5a2b95492451c8ad1,0x35d82b5582b5528d3f9d8c85a2a1248a3b1c0a51,0x2712e90462190476399acce5a2b95492451c8ad1,0x35d80b556aa538974821904733599cae551c8ad1,0x35d82ba5aac15aa9469d8c85a2a1248a3b1c0a51,0x35d82ba5aac15aa9469fcec5a2a1248a3b1c0a51,0x35d82ba5aac15aa9469fcec642d15092451c0a51]
def bk33 : Array Nat := #[0x35d6aa94e25d208743208e66c3599caa3b1c8ad1,0x30560ad512711a863b1acc85a2b9248a3b1c8151,0x3bdaec15d2d560ad54a34ec642d1248a3b1c0151,0x30560ad512712e8d3b1ccd6672d1248a3b1c0151,0x35d6eb554a712e9043a1904733599cae551c8ad1,0x3a9aeb75aaa538974821904733599cae551c8ad1,0x3055aa94e25d208743208e66b3395caa3b1c8ad1,0x33582ad54a712e9043a1904733599caa3b1c8ad1,0x3bdaec15d2d560ad54a34fe762d15092451d8451,0x3bdaec15d2d560ad54a34ec642d15092451d86d1,0x2712e9043a190473361acce5a2b9548a3b1c8ad1,0x35d82b5582b5529c46a18fe6b2b924863b1c8951,0x35d82b5582b5529c4ba411a8641124863b1c0951,0x3bdaec15d2d560ad54a34fe762d1248a3b1c0951,0x2712e9043208ec73361acce5c2d15caa451c8ad1,0x27d3897482190476399acce5c2d15caa451c8ad1,0x35d80b556aa1208c43204e66b3315492441c8a91,0x35d6a9c4ba411a86411d8e65a2b95492441a0491,0x35d6ab04e2411a86409d8e65a2b95492451a0491,0x33582b056aa5309746219046b339248a3b1c8ad1,0x35d82b5582b5529c481d8e66b33168ae551a8711,0x35d82b556aa13897481d8e66b33968ae551a8711,0x33580b056aa5309746a19046b339248a3b1c8ad1,0x30564b056aa52e8d43208dc6b339248a3b1c8ad1,0x33582b2582b5529746a19046b339248a3b1c8ad1,0x30564b056aa5309746a19046b339248a3b1c8ad1,0x2d560ae56aa52e8233968ae55251248a3b1c8ad1,0x35d82a64e25d208d43208e66b33944803b1b8891,0x35d6ab054a7936974822504763999cb455228ad1,0x35d92bd5c2d560a94ba4104763999cb455228ad1,0x36daeb85aac152974822504763999cb455228ad1,0x3a1aebd5aac1529b4ba4104763999cb455228ad1]
def bk34 : Array Nat := #[0x35d70b5582a536974822504763999cb455228ad1,0x35d7ab85aac1529b4ba4104763999cb455228ad1,0x2c1529c4ba410e86411ccd86b339548a3b1c8ad1,0x35d82b5582b5528d3f9d8c85a2a1248a3b1c0a11,0xef6c30574b5582b5529c4ba411a86411dce66b33968ae562a9248a3b1c8adb,0x36182b54e25d207e399acce5a2b958aa3e1a8751,0x3616ab052a71208d39980b4572b15492451a04d1,0x36182ad4e25d208d43208d66329924863b1c89d1,0x361829c4ba411a86411ccd6672b144803b1b88d1,0x3616aa54e25d208d43208e6602d15cac551a04d1,0x36182b556aa520823a9ccd6672b958aa3b1c8ad1,0x36182b556aa5249043a19046b33958aa3b1c8ad1,0x36182b5582b5529c481f8e65a2b958aa3e1a8751,0x3616aa9492411a8641168ae562a9248a3b1c8ad1,0x3616aae56aa5249046a1904562a9248a3b1c8ad1,0x36182a64ba411a86411ccd6672b144803b1b88d1,0x36182a64e25d208d43208e66b33958a23b1b88d1,0x3616ab056aa520894116cb4572b15492451c8ad1,0x361829c4ba411a86411dce66b33958803b1b80d1,0x3616ab0572b5529248208b4572b15492451c8ad1,0x361829c4ba411a86411dce66b33958a2401d82d1,0x3056cb5582b552753599cae55251248a3b1c8ad1,0x36182a64e25d208d43208ee733599cac511d85d1,0x36182b5582b5529c46a18d66329924863b1c89d1,0x3617ab5582a5369748225047333968ac55228ad1,0x3055aa93a9ccd6672d15cac55251248a3b1c8ad1,0x3056cb556aa4ea733599cb4572b1548a3b1c8ad1,0x2350c823a9ccd86b33968ae562a9248a3b1c8ad1,0x249229046a19047333968ae562a9248a3b1c8ad1,0x2f56cb5582b552773999cb4572b15492451c8ad1,0x36182a64e25d208d43208ee733599cac3b1b8811,0x2d96ab056aa4ea7333968ae562a92892451c8ad1]
def bk35 : Array Nat := #[0x36182b5582b5528d3f990b4562a1248a3b1c0a51,0x36182b5582b5528d3b990b4562a1248a3b1c0a51,0x36182b5582b5528d3f9dcb4562a1248a3b1c0a51,0x3617ab554a712e9043208e66b3395cac551c8ad1,0x36182ba5aac15aa9469dcc85a2b1248a3b1c0151,0x3616aa94e25d208743208e66b3395cac551c8ad1,0x36182ba5aac15aa9469fcee5a2b15092451d8451,0x36182ba5aac15aa9469dcc85a2b15092451d86d1,0x2712e91482350c82399b0d6672a9248a3b1c8ad1,0x2712e91482250c82399acce5a2b958aa451c8ad1,0x36182ba5aac15aa9469fcee5a2b1248a3b1c0951,0x2712e91482190473361acce5a2b958aa451c8ad1,0x36182a64ba411a86411ccd6672b144803b1b8891,0x3616ab054a6d2e9044a08ee7333968ac55228ad1,0x3617ab85aac1529748208ee7333968ac55228ad1,0x36170b5582a52e9044a08ee7333968ac55228ad1,0x3617ab5582a5369748208ee7333968ac55228ad1,0x36182b5582b5528d3f990b4562a1248a3b1c0a11,0x77b95aec15d2d560ad54a712e9046a290c823b9ccde6b33968ae55249188a3b1c8ade,0x77b5d82ba5aac15aa94e25d208d4521908823b1ccd6672d15caa49231147639190ade,0x1dee56bb0574b5582b5529c4ba411a8a432110477399bcd6672d15caa49231147639190ae0,0x3bdaec15f2e96ab056aad529c4ba411a8a432110476399acd0672d15caa49231147639190ae1,0x1dee56bb0174b5582b5509c4ba411a8a43208ee73379acd0672d15cac55249188a39190ae0,0x77b5d82ba5aab5509c4ba411a86411dce66f359a0ce5a2b958aa49231147639190ade,0x35d82b556aa1389046a19026b2b94c923b1c8991,0x35d82b556aa11a7f34158a849231107638190a11,0x3bdcad760ae96ab056aa13897482351486411dce66f359a0ce5a2b958aa49231147639190ae1,0x3bdcad7602e96ab056aa1389748235148642208ee73379acd0672d15cac55249188a3b1c8ca1,0x1ded760ae96aad542712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190ae0,0x1ded860ae96aad542712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190ae0,0x3bdcad760ae96ab056aa1389748235148642208ee73379acd0672d15cac55249188a3b1c8ca1,0x1dee56bb0174b5582b5529c4ba411a8a43208ee73379acd0672d15cac55249188a39190ae0]
def bk36 : Array Nat := #[0xef6bb0574b5582b5529c4ba411a86411dce66f359a0ce5a2b958aa49231147639190adf,0xef6c30574b5582b5529c4ba411a86411dce66f359a0ce5a2b958aa49231147639190adf,0x3bdcad760ae96ab056aa53897482351486411dce66f359a0ce5a2b958aa49231147639190ae1,0x3bdcad7602e96ab056aa5389748235148642208ee73379acd0672d15cac55249188a3b1c8ca1,0x3bdaec15d2d560ad54a712e9046a290c84411dce66f359a0ce5a2b958aa49231147639190ae1,0x3bdcad8673057cba582b556a94e25d1a8a432110477379acd0672b9589c49231147639190ae1,0x1dee56c33982be5d2c15aab54a712e8d4521908823b9bcd6683395cac49231147639190ae0,0x3bdcad8673057cba582b556a94e25d1a8a432110477379acd0672b9589649231147639190ae1,0x3bdcad8673057cba582b556a94e25d1a8a432110477379acd0672b9589e49231147639190ae1,0x3bdcad8672f574b5582b5529c4ba411a8a432110477399bcd0672d15cac55249188a39190ae1,0x3bdcad8672f574b5582ad529c4ba411a8a432110477399bcd6672d15cac55249188a39190ae1,0x3bdcad8673057cba582b556a94e25d1a8a432110477379acd0672b958a449231147639190ae1,0x3bdcad8672f574b5582a1389748235148642208ee73379acd0672d15cac55249188a39190ae1,0x3bdcad760af974b5582b5529c4ba411a8a43208ee73379acd0672d15cac55249188a39190ae1,0x3bdcad760af974b5582b556a94e25d2086411dce66f359a0ce5a2b958aa49231147639190ae1,0x3bdcad8673057cb055aa52e8d4521104773a9ccde6b3419cb85a2b958aa49231147639190ae1,0x1dee56c33982be5d2c15aab54a5d1a8a42208ee73379a0ce5a2b958aa49231147639190ae0,0x3bdcad8673057cb2582b556a94c25d1a8a432110477399bcd66833968ac55249188a3b1c8ca1,0x1dee56c33982be592c15aab54a5d1a8a42208ee73379acd0672d158aa49231147639190ae0,0xef72b619cc15f2e96ab056aad529c4ba411a8a432110477399acb4572b1549239190adf,0x3bdcad8673057cb7582b556a94ba351484411dcea73379acd0672d15cac55231147639190ae1,0x1dee56c33982be582b556a94c25d1a8a432110477399bcd66833968ac55231147639190ae0,0x3bdcad86730174b5582b556a94e25d208d4521908823b9ccde6b2d15cac55249188a39190ae1,0x3bdcad8673057cb8582ad529b4ba351484411dce66f3419cb4562a9188a3b190add,0x361a6ce582ad528e45a2908822b1548c45190ad1,0x3959cc15f2c156a94ba3514844118c98431889d1,0x381b0ce5faf956a94ba1104733419cac55190ad1,0x1dee56c33982be5c2c156a94ba351484411dce66f3419cb4562a9188a3b190adc,0x36182ab50a35087334198b4562a918883b190a91,0x381b0ce60af956a94ba1d08823419caa3b190ad1,0x361a6ce582b956a946a2908822a9188a3b190ad1,0x361a6ce582ad528b45211045a2b1548c45190ad1]
def bk37 : Array Nat := #[0x3959cc15f2c156a94ba3514844118c863b1889d1,0x3959cc15f2c156a94ba351484411c4c6431889d1,0x3959cc15f2c156a94ba351484411c4c63b188811,0x395b0ce60af960ab54a5d1a8a42208863b188951,0x2692e9145a290882399bcd0672b1548c45190ad1,0x3959cbe5c2c1529745208ec733799cb455228ad1,0x36182b855a350877399a0cc5a2b1548c3b190891,0x36182ab50a350877399a0b4562a918883b190a11,0x1cace5f2e160a94ba2904733799cb455228ad0,0x3bdcad8673057cba5aac15aab54a712e9046a290c84411acae562a9247639190add,0x30d82be5b2d560ad55aa4d655251247639190ad1,0x2692e9148235148642208d86b2a9247639190ad1,0xef72b619cc15f2c156a94ba351484411dce66f3419cb4562a9188a3b190adb,0x36182ab4b235087a399a0cc562a918883b190a91,0x36182af55a851a84399a0cc562a918883b190a91,0x39582be582892e8d451ece66f3419c8c451681d1,0x395b0ce582952e8d45211046f301688c451784d1,0x395b0ce5825d1a8a42208e66f301689c46228051,0x39582be5825d1a8a3d9ccde68339689c46228051,0x381b0ce60af956a943a11046833958aa3b190ad1,0x395b0ce60af960ab54a5cfc73379a0ce3e180751,0x395b0ce60af960ab54a5ce66f3419cb44e1f0091,0x39582be582892e8d451ccde68339689c46228091,0x361a6ce572ad528d4521104562a9188a3b190ad1,0x395b0ce4ba351484411ccde602b1548c411782d1,0x395b0ce60af960ab54a5cfc73379a0ce511805d1,0x395b0ce60af956a74b9f8e66f3419cac551805d1,0x30d7ebe5b2c156a9399bcd0672b1548c45190ad1,0x395b0ce60af960ab54a5d1a8a42208c6431889d1,0x2c15277399bcd86833968ac55251188a3b190ad1,0x395b0ce60af960ab54a5d1a8a42208c63b188811,0x395b0ce582952e8d45211046f2b1508c45178451]
def bk38 : Array Nat := #[0x395b0ce582951a8a42200e66f2b1548c45178451,0x395b0ce60af960ab549ccde6832958aa3e1806d1,0x25d0477399bcd86833968ac55251188a3b190ad1,0x3bdcad8673057cb055aa52e8d45211043b188791,0x3055eab50a591a843d1ccd0662a918883b190a91,0x36182ab4b235087a3b9ccd0662b1448c3b190891,0x36182ab4b235087a399a0cc5a2b1548c3b190891,0x36182af55a851a843b9a0b4562a118883b190a11,0x36182af55a851a84399a0b4562a918883b190a11,0x1cace5f2c1529745208ec733799cb455228ad0,0x3959cbe582a514823190c9,0xe5672f960a94ba2904733799cb455228acf,0x77b95b0ce60ae96aad55aa5389748235148642208ee7335968ae562a9247639190ade,0x1dee56c33982ba5aac15aab54a71208d4521908823b9bcd65a2b958aa49231147639190ae0,0x3bdcad8673057cba5aac156a94ba351484411dcea73379a0ce5a2b958aa49231147634190ae1,0x1dee56c33982be5d2d560ab54a5d1a8a42208ee73379a0ce5a2b958aa49231147634190ae0,0x3bdcad8673057cb85aac156a94ba351484411dce66f3419cb4562a9188a3b190add,0x381b0ce5faf96aab54a5d0882399a0ce55190ad1,0x1dee56c33982be5d2d55aab54a712e9046a290c84411dce66f359a0ce57299247639190ae0,0x1dee56bb057cba5aac15aab54a71208d452190277379acd0672d15ca649231147639190ae0,0x1dee56c33982be5d2c156a94ba351484411dcea73379a0ce5a2b958aa49231147634190ae0,0x77b95b0ce60af974b556aad529c4ba411a8a43211046b3419cae562a9247639190ade,0x3bdcad8673057cba5aac15aab54a5d1a8a42208ee75399bcd66833968ae562a9188a3b1a8ca1,0x1dee56c33982be582ad529746a2908823b9d4e66f359a0ce5c2d15cac55231147635190ae0,0x3bdcad8673057cba5aab5509c4ba411a8a432110477399bcd6683395ca649231147639190ae1,0x1dee56c33982be592c15aab54a612e8d452110477399bcd66833968ac55231147635190ae0,0xef72b619cc15f2c960ad55aa52e8d452110477399bcd66833968ac55231147635190adf,0x3bdcad8673057cb75aac15aab54a5d1a8a42208ee75399bcd66833968ae562a9188a3b1a8ca1,0x3bdcad8673057cba5aac15aab54a712e9046a290c84411dcde6b2d15ca649231147639190ae1,0x3bdcad8673057cb75aac15aab54a5d249046a2908823b9ccde6833968ae562a9188a3b1a8ca1,0xef72b619cc15f2c15aab54a612e8d452110477399bcd66833968ac55231147635190adf,0x3bdcad86730174b5582b5509c4ba411a8a432110477399bcd65a2b958aa49231147639190ae1]
def bk39 : Array Nat := #[0x77b95b0ce60af974b5582b556a94e25d208d4521908823595ca649231147639190ade,0x1ded860ae96aad54271208d4521908823b9ccd65a2b958aa49231147639190adc,0x33582ad54235148642208d649231147639190ad1,0x36182ba5aab5509c481dce66b2d15cac551a8611,0x33564ae56aa11a8a432110449231147639190ad1,0x3055aa84c235148642208d649231147639190ad1,0x182ad54235148642208d649231147639190ad0,0x2351486411248c451a0bc9,0x2f5508b45208c446228c89,0x2a1168a422088c45190ac9,0x3056aad541d8ea7335968ae55249147639190ad1,0x3617ab554241168a42208e6622b1548c45190ad1,0x3616aa84da41168a42208e6622b1548c45190ad1,0x3616aa84822d1484411dce65a2b1548c45190ad1,0x3616aa84da41168a42208e65a2b1548c45190ad1,0x3617ab55426d208b42208e6622b1548c45190ad1,0x35d82b556aa1389043208e66b2b9547639190ad1,0x3055a9c46a18e66b2d15c9c49231107639168191,0x36182a6482350c84409ccd656289187637190891,0x36182b556aa11a842d158a849231107638190a11,0xef72b619cc15d2d55aa84e25d208d4521908823b9ccd65a2b958aa49231147639190adf,0x77b95b0ce60af96ab055aa53697482351484411dce66f3419cb4562a9188a3b190ade,0xef72b619cc15d2d560ad542712e9046a290c84411dcde6b2d15ca649231147639190adf,0x3bdcad760af974b5582b5509c4ba411a8a432110477399bcd66833968ae53249188a3b1c8ca1,0xef72b6182ba5aac15aa84e2411a8a432110477399bcd65a2b958aa49231147639190adf,0x3bdcad86730574b5582b5509c4ba411a8a432110477399bcd65a2b958aa49231147639190ae1,0x3bdcad8673057cba582b556a94ba351484411dcea73379acd0672d15cac55231147635190ae1,0x1dee56c33980ba5aab556a94e25d208d4521908823b9ccd65a2b958aa49231147639190ae0,0x3bdcad8673057cb7582b556a94e25d1a8a42208ee73379acd0672d15cac55231147635190ae1,0x3bdcad8673057cb7582b556a94ba351484411dcea73379acd0672d15cac55231147635190ae1,0x3bdcad86730174b5582b556a94e2411a8a432110477399bcd65a2b958aa49231147639190ae1,0x3bdcad86730574b556aad529c4ba411a8a43211046b2b958aa49231147639190add]
def bk40 : Array Nat := #[0x361a6ce5aaad529045a2908822b1548c45190ad1,0x3959cc155a9d2e9046a290c84411ac7637188811,0x395b0ce5ead556a94ba41148441188aa45190ad1,0xef72b619cc15f2e96ab056aad529c4ba411a8a43211046b2b958aa49231147639190adf,0x77b619cc15d2d55aab54a71208d4521908823b9ccd65a2b958aa49231147639190ade,0x3619cb555aa5208b45211045a2b1548c45190ad1,0x3395cad55aa51a8a432110449231147639190ad1,0x35d9cb556aa52490462290c822b95492451c8ad1,0x1dee56c33982ba5aab556a94e25d208d4521908823b9ccd65a2b958aa49231147639190ae0,0xef72b619cc15f2e96ab055aa52e8d4521104773a9ccde6833968ae562a9188a3b190adf,0x3bdcad760af974b5582b556a94e2411a8a432110477379acd0672d15ca649231147639190ae1,0xef72b619cc15f2e96aad55aa5389748235148642208d6683395ca649231147639190adf,0x1dee56c33982be5d2d55aab54a712e9046a290c84411acd0672b958aa49231147639190ae0,0x77b619cc15f2e96aad55aa5389046a290c84411acd0672b958aa49231147639190ade,0x3bdcad8673057cb055aa52e8d452110477399bcd66833968ac55231147637190add,0x39582be4ba35147b379acd0672310476371680d1,0x36182ab46a10ee73359a0cc56289187637190891,0x3959cc05f2c1529745208e66f3599c90451b8ad1,0x1dee56c33982be582ad529c4ba411a8a432110477399bcd66833968ac55231147637190ae0,0x77b95b0ce60af960ab54a5d1a8a42208ee75399bcd66833968ac55231147637190ade,0x3959cc15f2ad4e9746a2908823598c7637188811,0x36182ab46a10ea73359a0cc56289187637190891,0xef72b619cc15f2e96ab056aad529c4ba411a8a432110477379acb4572a9248c451c8adf,0xef72b619cc15f2c156a94c25d1a8a432110477399bcd66833968ac55231147637190adf,0xef72b619cc05d2d560ad54a712e9046a290c84411dce66f35968ae562a9248c451c8adf,0x36182ab46a10ee7334198b4562a918883b190a91,0x3959cbe5a2c1529745208ec733799cb455228ad1,0x3bdb0c155a350877399a0cc5a2b1548c3b190891,0x3bdb0c155a350877399a0b4562a918883b190a11,0x3959cb054a2904712790c9,0x77b95b0ce60ae96ab056aa5389748235148642208ee7335968ae562a9248a3b1c8ade,0x3bdcad8673057cb055aa53697482351484411dce66f3419cb4562a9188a3b190add]
def bk41 : Array Nat := #[0x361a6ce582ad529045a2908822b1548c45190ad1,0x3959cc15f2c156a94ba411a8a42208c6431889d1,0x77b95b0ce60ae96ab056aa5389748235148642208ee6f35968ae55249188a3b1c8ade,0x1dee56c33982be5d2d560ad55aa5389748235148642208ee6f35968ae55249188a3b1c8ae0,0x3bdcad860ae96ab056aa5389046a290c813b9ccde6b2d15cac55249188a3b1c8add,0xef72b619cc05d2d560ad55aa5389748235148642208ee7335968ae562a9248a39190adf,0xef72b619cc15f2c156a94e25d1a8a432110477399bcd66833968ac55231147637190adf,0x1dee56c33980ba5aac15aab54a712e9046a290c84411dcde6b2d15cac55249188a39190ae0,0x1dee56c33980ba5aac15aab54a71208d4521908823b9ccde6b2d15cac55249188a39190ae0,0x1dee56bb057cba5aac15aab54a71208d452190277379acd0672d15caa49231147639190ae0,0x3bdcad8673057cb055aa52e8d4521104773a9ccde6b3419cb4562a9188a3b190add,0x39582be4ba35147b399bcd66833918823b1680d1,0x3959cc05f2c1529745208ea73379acce55228ad1,0xef72b619cc15f2e96ab056aad529c4ba411a8a43211046b2d15caa49231147639190adf,0x3bdcad8673057cb055aa5309746a2908823b9ccde6b3419cb4562a9188a3b190add,0x36182ab4c235087d399acd0662b1448c3b190891,0x3959cc05f2c152984ba290473379acce55228ad1,0x1dee56c33980ba5aac15aa94e25d208d4521908823b9ccd65a2b958aa49231147639190ae0,0x77b95b0ce60af960ab54a712e9046a2908823b9ccde6b3419cb4562a9188a3b190ade,0x395aece5f2c1529b4ba411482399bcce55228ad1,0xef72b619cc05d2d560ad54a712e9046a290c84411dcde6b2d15caa49231147639190adf,0xef72b6180ba5aac15aa94e2411a8a432110477399bcd65a2b958aa49231147639190adf,0x3bdcad86730174b5582b5529c4ba411a8a432110477399bcd65a2b958aa49231147639190ae1,0x3bdcad86730574b5582b5529c4ba411a8a43211046b2d15caa49231147639190add,0x30574b5582b5527535968ae55249147639190ad1,0x39582b056a89389746a290c7b35924863b1c8111,0x249229046a290c844115caa49231147639190ad1,0x395b0ce60a992e9046a290c84411ac7637188811,0x3bdb0c15d2d560ad54a71208d4521908823b9ccd65a2b958aa49231147639190add,0x3055aa94c235148642208d649231147639190ad1,0x33560ae56aa51a8a432110449231147639190ad1,0x35d6ab056aa52490462290c822b95492451c8ad1]
def bk42 : Array Nat := #[0x1dee56c33982ba5aac15aa94e25d208d4521908823b9ccd65a2b958aa49231147639190ae0,0xef72b619cc15d2d560ad54a712e9046a290c84411dcde6b2d15caa49231147639190adf,0xef72b6182ba5aac15aa94e2411a8a432110477399bcd65a2b958aa49231147639190adf,0xef72b619cc05d2d560ad55aa5389748235148642208d65a2b958aa49231147639190adf,0x1dee56c33982be5d2d560ad55aa5389748235148642208d65a2b958aa49231147639190ae0,0xef6c33980ba5aac15aab54a71208d4521908823b9ccd65a2b958aa49231147639190adf,0x3bdcad86730174b5582b556a94e25d208d4521908823b9ccd65a2b958aa49231147639190ae1,0x1dee56c33980ba5aac15aab54a71208d4521908823b9bcd65a2b958aa49231147639190ae0,0x3bdcad86730174b5582b556a94e25d208d4521908823b9bcd65a2b958aa49231147639190ae1,0x3bdb0ce60ae96ab056aad529c48235148642208d65a2b958aa49231147639190add,0x3619cc15aac15aab54a71207e2b1547c35180751,0x33982ab53a411a8a4321104512310476371908d1,0xef72b619cc15d2d560ad55aa5389748235148642208d65a2b958aa49231147639190adf,0xef6c33982ba5aac15aab54a71208d4521908823b9ccd65a2b958aa49231147639190adf,0x3bdcad760af974b5582b556a94e2411a8a432110477379acd0672d15caa49231147639190ae1,0x1dee56c33982be5d2d560ad55aa52e8d452110477399bcd0672d158aa49231147638190ae0,0x77b95b0ce60af960ab54a5d1a8a42208ee73379a0ce5c2d158aa49231147638190ade,0x3959cc15f2c156a946a2908802490c7638188951,0x36182ab46a10ee682d158a849231107638190a11,0xef72b619cc15f2c960ad55aa52e8d452110477399bcd0672d158aa49231147638190adf,0xef72b619cc15f2e96ab056aad529c4ba411a8a432110477399acce5a2b958aa491c8adf,0xef72b619cc15f2dd6ab056aad529746a2908823b9ccde6833968ac55231147638190adf,0x3bdcad8673057cba5aac15aa84e25d208d4521908823b9ccde6b3419cb4572a9248c451c8ae1,0x77b95b0c05d2d560ad542712e9046a290c823b9ccde6b33968ae562a9248c451c8ade,0x35d80b556aa138974821904733599cae551c8ad1,0x39580b056aa12e8c45219046f3599c92451c8ad1,0x1dee56c33980ba5aac15aa84e25d208d4521908823b9ccde6b33968ae562a9248c451c8ae0,0x1dee56c3057cba5aac15aa84e25d208d452190477399bcd66833968ae562a9248c451c8ae0,0x3bdcad8673057cba5aac15aab54a712e9046a290c84411ccd6672b954923b1c8add,0x3959cbf5f2d560ab54a5d208b452110467210ad1,0x77b95b0ce60af974b556aa1389748235148642208ee73379acd0672b954923b1c8ade,0x36182af55aa11a84399a0cc562a918883b190a91]
def bk43 : Array Nat := #[0x36182af55aa11a843b9a0b4562a118883b190a11,0x36182af55aa11a84399a0b4562a918883b190a11,0x3bdcad86730574b556aa1389748235148642208ee733599cb4572b154923b1c8add,0x1dee56c33982be5d2d55aa84e25d208d4521908823b9ccde6b3419cb4572b154923b1c8ae0,0x77b95aec15d2d560ad542712e9046a290c823b9ccde6b33968ae55249188a3b1c8ade,0x395aebd5aac1509b4ba411482399bcce55228ad1,0x1dee56c33982ba5aac15aa84e25d208d4521908823b9ccde6b33968ae55249188a3b1c8ae0,0x1dee56bb057cba5aac15aa84e25d208d452190477399bcd66833968ae55249188a3b1c8ae0,0xef72b6182ba5aac15aa84e25d208d452190477399bcd6672d15cac55249188a3b1c8adf,0x3bdcad86730574b5582b5509c4ba411a8a432110477399bcd6672d15cac55249188a3b1c8ae1,0x3bdcad860af974b5582b5509c4ba411a8a43208ee73379acd0672d15cac55249188a3b1c8ae1,0xef72b619cc15f2e960ad55aa52e8d452110477399bcd0672d158aa49231147638190adf,0x1dee56c33982be5d2d55aab54a712e9046a290c84411dce66f359a0ce572b1549239190ae0,0x1dee56c33982be5d2d560ad55aa5389748235148642208ee733599cb4572b1549239190ae0,0x3bdcad86730574b556aad529c4ba411a8a4321104733599cae562a9247639190add,0x381b0ce5ead556a94ba4108823999cac55190ad1,0x395b0ce5aa95389748235148642208a6491a03d1,0x395b0ce5aaad52974822d14844119caa42190ad1,0xef72b619cc15f2e96ab056aad529c4ba411a8a4321104733599cae562a9247639190adf,0x3bdb0ce60ae96aad55aa53897482350c84411dce66b33968ae562a9247639190add,0x3619cb555aa5208942208e6672d158aa42190ad1,0x3619cbd5aaad529b4ba4108823999cac55190ad1,0x3616a9c482350c84409ccb4572b1549234178491,0x35d9cc05aab5529c4ba410c82399acce551c8ad1,0xef72b619cc15d2d55aab54a712e9046a290c84411dce66b33968ae562a9247639190adf,0x77b95b0ce60af974b5582ad529746a2908823b9ccde6833968ac55249188a3b190ade,0x3959cbe5aac1529745208ec733799cb455228ad1,0x1dee56c33982be5d2d55aab54a712e9046a290c84411dce66f359a0ce572a9247639190ae0,0x77b95b0ce60af974b556aad529c4ba411a8a432110473359a0ce572a9247639190ade,0x3819cbf5f2d556a94ba410882399a0ce55190ad1,0x3057cb556aad5275399acd0672b9547639190ad1,0x25d229043a190882399b0d668339547639190ad1]
def bk44 : Array Nat := #[0xef72b619cc15f2e96aad55aa5389748235148642208e66b3419cae562a9247639190adf,0x77b95b0ce60af974b5582b556a94ba351484411dce66f3419cb4562a9188a3b190ade,0x36182b556aad508d421a0b4562a118883b190a11,0x3bdcad8673057cba5aab5509c4ba411a8a432110477399bcd6683395caa49231147639190ae1,0x77b6180ba5aab5509c4ba411a8a432110477399acce5a2b958aa49231147639190ade,0x36180b556aa138903b9ccd6662d15cac551a8711,0x1dee56c33980ba5aab5509c4ba411a8a432110477399acce5a2b958aa49231147639190ae0,0x1dee56bb0174b5582b5509c4ba411a8a432110477399bcd6672d15caa49231147639190ae0,0x3bdcad86730174b5582b5509c4ba411a8a432110477399bcd6672d15caa49231147639190ae1,0x3bdcad760af974b5582b5509c4ba411a8a432110477399bcd66833968ae55249188a3b1c8ca1,0x3bdcad8602e96ab056aa1389748235148642208ee73379acce5a2b958aa49231147639190ae1,0x3bdcad86730174b5582b5509c4ba411a8a432110477399bcd6672d15cac55249188a3b1c8ca1,0x77b6182ba5aab5509c4ba411a8a432110477399acce5a2b958aa49231147639190ade,0x36182b556aa138903b9ccd6662d15cac551a8711,0x1dee56c33982ba5aab5509c4ba411a8a432110477399acce5a2b958aa49231147639190ae0,0x3bdcad86730574b5582b5509c4ba411a8a432110477399bcd6672d15caa49231147639190ae1,0x3bdcad860ae96ab056aa1389748235148642208ee73379acce5a2b958aa49231147639190ae1,0xef72b619cc05d2d55aab54a712e9046a290c84411ccd6672b958aa49231147639190adf,0x1ded86730174b556aad529c4ba411a8a432110477399acce5a2b958aa49231147639190ae0,0x3bdcad86730174b556aad529c4ba411a8a432110477399acce5a2b958aa49231147639190ae1,0x77b619cc15d2d55aab54a712e9046a290c84411ccd6672b958aa49231147639190ade,0xef72b619cc15d2d55aab54a712e9046a290c84411ccd6672b958aa49231147639190adf,0x1ded86730574b556aad529c4ba411a8a432110477399acce5a2b958aa49231147639190ae0,0x1dee56c33982be5d2d55aab54a712e9046a290c84411ccd6683395caa49231147639190ae0,0x77b5d82be5d2d55aab54a712e9046a290c84411ccd6683395caa49231147639190ade,0x1ded8673057cba5aab556a94e25d208d452190882399acd0672b958aa49231147639190ae0,0x1dee56c33980ba5aac15aa94e25d208d452190882399acce5a2b95492451c8adc,0x3959cc05325d208d452190882399acce511b88d1,0x30174b5582b55275399acce5a2b95492451c8ad1,0x395b0ce602712e9046a290c84411ccd6672882d1,0x395b0ce602992e9046a290c84411ccd6671b8811,0x180ba5aac15aa9399acce5a2b95492451c8ad0]
def bk45 : Array Nat := #[0x395b0ce602d560ad54a3514844015092451c0a51,0x395b0ce602d560ad54a3514802d15092451c0a51,0x3015aa94e25d229043a190882399acce551c8ad1,0x395b0ce602d560ad54a35148440168a849228451,0x395b0ce602d560ad54a3514844016892451c0951,0x395b0ce5aac152974822d14844119cb455228ad1,0x3959cc0582b55297462290c823599c92451c8ad1,0x3959ece582b5529746a290c844119c92451c8ad1,0x395aece5ead560a94da5d208a411ccce55228ad1,0x77b95b0ce60af974b5582b556a94e25d208d452190882399acce5a2b95492451c8ade,0x395aece5f2d560a94da5d208a411ccce55228ad1,0x3959cc05f2c152974622904733799caa451b0ad1,0x3959cc05f2c1529746229046f33968aa451b0ad1,0x3959cbe582a52e8c45208ec733799cb455228ad1,0x3959cc05f2c1529745208ec733799cb455228ad1,0x77b95b0ce602e96ab056aa5389748235148642208ee733599cb4572b15492451c8ade,0x1dee56c33982be5d2d560ad55aa5389748235148642208ee733599cb4572b15492451c8ae0,0xef72b619cc05d2d560ad54a712e9046a290c84411dce66f3599cb4572a9248c451c8adf,0xef72b5d82be5d2d560ad54a712e9046a290c823b9ccde6b3419cb4572a9248c451c8adf,0x77b95b0c05d2d560ad54a712e9046a290c823b9ccde6b33968ae562a9248c451c8ade,0x1dee56c33980ba5aac15aa94e25d208d4521908823b9ccde6b33968ae562a9248c451c8ae0,0x1dee56c3057cba5aac15aa94e25d208d452190477399bcd66833968ae562a9248c451c8ae0,0x395aece5f2c1529745208ec733799cb455228ad1,0x3bdcad86730574b5582b5529c4ba411a8a4321104733599cb4572a9248a3b1c8add,0x395b0ce60a992e9046a290c84411acc63b1b8811,0xef72b619cc15f2e96ab056aad529c4ba411a8a4321104733599cb4572a9248a3b1c8adf,0x1dee56c33982ba5aac15aa94e25d208d4521908823b9ccde6b33968ae55249188a3b1c8ae0,0x1dee56bb057cba5aac15aa94e25d208d452190477399bcd66833968ae55249188a3b1c8ae0,0xef72b6182ba5aac15aa94e25d208d452190477399bcd6672d15cac55249188a3b1c8adf,0xef72b619cc05d2d560ad55aa5389748235148642208e66b33968ae562a9248a39190adf,0x1dee56c33982be5d2d560ad55aa5389748235148642208e66b33968ae562a9248a39190ae0,0x77b619cc05d2d560ad55aa53897482310c84411dce66b33968ae562a9248a39190ade]
def bk46 : Array Nat := #[0x1dee56c33980ba5aac15aab54a712e9046a290c84411dce66b33968ae562a9248a39190ae0,0x77b619cc15d2d560ad55aa53897482350c84411ccd6672d15cac55249147639190ade,0xef6c33982ba5aac15aab54a712e9046a1908823b9ccd6672d15cac55249147639190adf,0xef72b619cc05d2d560ad54a712e9046a290c84411ccd6672d15caa49231147639190adf,0xef6c30174b5582b5529c4ba411a8a432110477399acce5a2b958aa49231147639190adf,0x3bdcad86730174b5582b5529c4ba411a8a432110477399acce5a2b958aa49231147639190ae1,0x1dee56bb0174b5582b5529c4ba411a8a432110477399bcd6672d15caa49231147639190ae0,0x3bdcad86730174b5582b5529c4ba411a8a432110477399bcd6672d15caa49231147639190ae1,0x3bdcad8602e96ab056aa5389748235148642208ee73379acce5a2b958aa49231147639190ae1,0x3bdaec15d2d560ad54a712e9046a290c84411ccd6672d15caa49231147639190add,0xef72b619cc15d2d560ad54a712e9046a290c84411ccd6672d15caa49231147639190adf,0xef6c30574b5582b5529c4ba411a8a432110477399acce5a2b958aa49231147639190adf,0x3bdcad86730174b5582b556a94e25d208d452190882399acce5a2b958aa49231147639190ae1,0x3bdb0ce602e96ab056aad529c4ba411a8a432110477399acce5a2b958aa49231147639190ae1,0x1ded86730574b5582b556a94e25d208d452190882399acce5a2b958aa49231147639190ae0,0x1ded760af974b5582b556a94e25d208d452190882399acd0672d15caa49231147639190ae0,0x3bdcad8673057cb055aa52e9246a290c84411dce66f3419cb85a2b958aa49231147639190ae1,0x1dee56c33982be592c15aab54a5d1a8a432110477399bcd0672d158aa49231147639190ae0,0x77b95b0ce60af960ab54a5d1a8a432110477399bcd0672d158aa49231147639190ade,0xef72b619cc15f2c156a94da5d1a8a432110477399bcd0672d158aa49231147639190adf,0x1dee56c33982be5c2c156a94ba391a8a432110477399bcd0672d158aa49231147639190ae0,0x1dee56c33982be59ac156a94da5d1a8a432110477399bcd0672d158aa49231147639190ae0,0x3bdcad8673057cb055aa52e9248235148642208ee73379a0ce5c2d15cac55249188a3b1c8ca1,0x1dee56c33982be582ad529746a290c84411dce66f3419cb85a2b958aa49231147639190ae0,0x3bdcad8673057cb055aa52e9248235148642208ee73379a0ce5a2b958aa49231147639190ae1,0x1dee56c33982be582ad529b4ba411a8a432110477399bcd0672d158aa49231147639190ae0,0xef72b619cc15f2c156a94ba411a8a432110477399bcd0672d158aa49231147639190adf,0x1dee56c33982be5c2d560ab54a5d1a8a432110477399bcd0672d158aa49231147639190ae0,0x3bdcad8673057cba5aac15aab54a712e9046a290c84411dce66f359a0ce57299247639190ae1,0x3bdcad760af974b5582b556a94e25d208d45218ee73379acd0672d15ca649231147639190ae1,0x3bdcad8673057cb055aa5389746a290c84411dce66f3419cb85a2b958aa49231147639190ae1,0x3bdcad8673057cba582ad529749235148642208ee73379a0ce5a2b958aa49231147639190ae1]
def bk47 : Array Nat := #[0x1dee56c33982be5d2c156a94ba35148642208ee73379a0ce5a2b958aa49231147639190ae0,0xef72b619cc15f2c960ab54a5d1a8a432110477399bcd0672d158aa49231147639190adf,0x1dee56c33982be5c2c156a94da5d1a8a432110477399bcd0672d158aa49231147639190ae0,0x1dee56c33982be582ad5297492411a8a432110477399bcd0672d158aa49231147639190ae0,0x1dee56c33982be5d2d560ad55aa53897482351477399bcd66833968ae562a9248c451c8ae0,0x1dee56c3057cba5aac15aa94e25d208d45218ee73379acd0672d15cac55249188a3b1c8ae0,0x1dee56c33982be582ad529c4ba411a8a432110477399bcd0672d158aa49231147639190ae0,0x1dee56c33982be5d2d560ad55aa53897482350c77399bcd66833968ae55249147639190ae0,0x1dee56c3057cba5aac15aab54a712e9046a18ee73379acd0672d15cac55249147639190ae0,0x3bdcad760af974b5582b556a94e25d208d45218ee73379acd0672d15caa49231147639190ae1,0xef72b619cc15f2c156a94e25d1a8a432110477399bcd0672d158aa49231147639190adf,0x1ded8673057cba5aac15aab54a71208d432110477399acd0672d15cac55249147639190ae0,0xef72b619cc15f2c156a94ba35148642208ee73379a0ce5c2d158aa49231147639190adf,0x3bdcad8673057cb75aac15aab54a5d1a8a432110477399bcd0672d158aa49231147639190ae1,0x1dee56c33982be5d2d560ad55aa5389748235148642208ee73379acd0672b954923b1c8ae0,0xef72b619cc15f2d560ab54a5d1a8a432110477399bcd0672d158aa49231147639190adf,0x1dee56c33982be5d2c15aab54a5d1a8a432110477399bcd0672d158aa49231147639190ae0,0xef72b619cc15f2e96ab056aad529c4ba410c84411dce66f359a0ce5a2b958aa39190adf,0x1dee56c33982be5d2d55aab54a712e9046a1908823b9ccde6b3419cae562a9247639190ae0,0x1dee56c33982be5d2d560ab54a5d1a8a432110477399bcd0672d158aa49231147639190ae0,0x1dee56c33982be5d2d560ad55aa5389748235148642208ee73379acd0672b9547639190ae0,0xef72b6182be5d2d55aab54a712e9046a190477399bcd66833968ae562a9247639190adf,0xef72b619cc15f2e960ab54a5d1a8a432110477399bcd0672d158aa49231147639190adf,0x1dee56c33982be5d2d55aab54a712e9046a290c84411dce66f359a0ce572b1547639190ae0,0xef72b619cc15f2e160ab54a5d1a8a432110477399bcd0672d158aa49231147639190adf,0xef6c33982be5d2d55aab54a712e9046a1908823b9ccd66833968ae562a9247639190adf,0xef72b619cc15f2e96ab056aad529c4ba410c823b9ccde6b3419cb4572b15492451c8adf,0xef72b6182be5d2d560ad54a712e9046a190477399bcd66833968ae562a9248a3b1c8adf,0xef72b5d82be5d2d560ad55aa53897482190477399bcd66833968ae55249147639190adf,0x1dee56c33982be5d2d560ad55aa53897482190477399bcd66833968ae55249147639190ae0,0x1dee56c3057cba5aac15aab54a712e9043208ee73379acd0672d15cac55249147639190ae0,0x1dee56bb057cba5aac15aab54a712e9046a190477399bcd66833968ae55249147639190ae0]
def bk48 : Array Nat := #[0xef6c3057cba5aac15aab54a712e9046a190477399acd0672d15cac55249147639190adf,0x1dee56c33982be5d2d560ad55aa53897482190882399acd0672d15cac55249147639190ae0,0x1ded8673057cba5aac15aab54a712e9046a190882399acd0672d15cac55249147639190ae0,0x3bdcad8673057cb2582b556a94ba35148642208ee73379acd0672d158aa49231147639190ae1,0x1dee56c33982be582b556a94ba35148642208ee73379acd0672d158aa49231147639190ae0,0x3bdcad8673057cb056aad52984ba35148642208ee73379acd0672d158aa49231147639190ae1,0x3bdcad8673057cb8582b556a94ba35148642208ee73379acd0672d158aa49231147639190ae1,0x3bdcad8673057cb3582b556a94da5d1a8a432110477399bcd66833968ac55249188a3b1c8ca1,0x3bdcad8673057cb056aad529746a290c84411dcea73379acd0672d158aa49231147639190ae1,0x3bdcad8673057cb056aad529b4ba35148642208ee73379acd0672d158aa49231147639190ae1,0x3bdcad8673057cb056aad529746a290c84411dce66f359a0ce5c2d158aa49231147639190ae1,0x3bdcad8673057cb7582b556a94ba35148642208ee73379acd0672d158aa49231147639190ae1,0x1cace5f2e96ab1582b556a94ba35148642208ee73379a0ce5a2b958aa49231147639190ae0,0xef72b619cc15f2e96ab056aad529c4ba411a843b9ccde6b3419cb4572b1548c3b19051f,0xe5683397cba5aac15aa94ba35148642208ee73379a0ce5a2b958aa49231147639190adf,0x3959cbe5d2d560ad54a79369748235148642208ee73379a0ce5a2b958aa49231147639190ae1,0x1cace5f2e96ab056aa52e9348235148642208ee73379a0ce5a2b958aa49231147639190ae0,0xef72b619cc15f2e96ab056aad529c482350c843b9ccd6682d15cac5524918763919051f,0x1cace5f2e96ab056aa5369748235148642208ee73379a0ce5a2b958aa49231147639190ae0,0x3b5cace5faf974b5582b5529b4ba35148642208ee73379a0ce5a2b958aa49231147639190ae1,0x395b8ce5f2e96ab056aa9529747235148642208ee73379a0ce5a2b958aa49231147639190ae1,0x3a5cace5faf974b5582b5529b4ba35148642208ee73379a0ce5a2b958aa49231147639190ae1,0x1d8e5672f974b5582b5529b4ba35148642208ee73379a0ce5a2b958aa49231147639190ae0,0x1cace5f2e96ab056aa53c9b4ba35148642208ee73379a0ce5a2b958aa49231147639190ae0,0x1cad667b397cba5aac15aa94ba35148642208ee73379a0ce5a2b958aa49231147639190ae0,0x3b5cad8672f974b5582b5529b4ba411a8a432110477399bcd0672d15cac55249188a3b1c8ca1,0x395b8d8672f974b5582b5529748235148642208ee73379a0ce5a2b958aa49231147639190ae1,0x1cce567b397cba5aac15aa94ba35148642208ee73379a0ce5a2b958aa49231147639190ae0,0x1cad467b397cba5aac15aa94ba35148642208ee73379a0ce5a2b958aa49231147639190ae0,0x3a5cad8672f974b5582b5529b4ba411a8a432110477399bcd0672d15cac55249188a3b1c8ca1,0x1cad8672f974b5582b5529748235148642208ee73379a0ce5a2b958aa49231147639190ae0,0x3b9cad7672f974b5582b5529c4ba411a8a432110477399bcd0672d15cac55249188a3b1c8ca1]
def bk49 : Array Nat := #[0x3959cbe5d2d560ad54a7d389748235148642208ee73379a0ce5a2b958aa49231147639190ae1,0xe56ab397cba5aac15aa94ba35148642208ee73379a0ce5a2b958aa49231147639190adf,0x1dee56c33982be5d2d560ad55aa53897482350877399bcd66833968ae562a9187639190ae0,0x3a9cad7672f974b5582b5529c4ba411a8a432110477399bcd0672d15cac55249188a3b1c8ca1,0x1cace5f2e96ab056aa5389748235148642208ee73379a0ce5a2b958aa49231147639190ae0,0x3b1cad7672f974b5582b5529b4ba411a8a432110477399bcd0672d15cac55249188a3b1c8ca1,0x395b6d7672f974b5582b5529748235148642208ee73379a0ce5a2b958aa49231147639190ae1,0x72b397cba5aac15aa94ba35148642208ee73379a0ce5a2b958aa49231147639190ade,0x1dee56c33982be5d2d560ad55aa5389046a190877399acd0672d15cac55249187639190ae0,0x1dee56c3057cba5aab556a94e25d208d43210ee73379acd0672d15cac55249187639190ae0,0x3a1cad7672f974b5582b5529b4ba411a8a432110477399bcd0672d15cac55249188a3b1c8ca1,0xe56b3397cba5aac15aa94ba35148642208ee73379a0ce5a2b958aa49231147639190adf,0x1dae5672f974b5582b5529b4ba35148642208ee73379a0ce5a2b958aa49231147639190ae0,0x1cadc672f974b5582b5529747235148642208ee73379a0ce5a2b958aa49231147639190ae0,0xe672b397cba5aac15aa94ba35148642208ee73379a0ce5a2b958aa49231147639190adf,0x1dce5672f974b5582b5529c4ba35148642208ee73379a0ce5a2b958aa49231147639190ae0,0x1cace5f2e96ab056aa53e9c4ba35148642208ee73379a0ce5a2b958aa49231147639190ae0,0x1dee56c33982be5d2d55aab54a712e9046a110477399bcd66833968ae562a9187639190ae0,0xef6c33982be5d2d55aab54a71208d432110477399acd0672d15cac55249187639190adf,0x395accf672f974b5582b95aab54a5d1a8a432110477399bcd0672d15cac55249188a3b1c8ca1,0x395a2cf672f974b5582b95aab54a5d1a8a432110477399bcd0672d15cac55249188a3b1c8ca1,0x3b5cad8672fd7cba5aac15aab54a5d1a8a432110477399bcd0672d15cac55249188a3b1c8ca1,0x395b8d8672f974b5582b556a94ba35148642208ee73379a0ce5a2b958aa49231147639190ae1,0x399cacf672fd7cba5aac15aab54a5d1a8a432110477399bcd0672d15cac55249188a3b1c8ca1,0x395a8cf672f974b5582b556a94ba35148642208ee73379a0ce5a2b958aa49231147639190ae1,0x3a5cad8672fd7cba5aac15aab54a5d1a8a432110477399bcd0672d15cac55249188a3b1c8ca1,0x1cad8672f974b5582b556a94ba35148642208ee73379a0ce5a2b958aa49231147639190ae0,0x395c2cf672fd7cba5aac15aab54a5d1a8a432110477399bcd0672d15cac55249188a3b1c8ca1,0x3b9cad7673017cba5aac15aa94ba35148642208ee73379a0ce5a2b958aa49231147639190ae1,0x3959cbe5d2d560ad54a7d2e8f46a290c84411dce66f351a0ce5a2b958aa49231147639190ae1,0x3a9cad7673017cba5aac15aa94ba35148642208ee73379a0ce5a2b958aa49231147639190ae1,0x1d8e56bb397cba5aac15aa94ba35148642208ee73379a0ce5a2b958aa49231147639190ae0]
def bk50 : Array Nat := #[0x1cadb6bb397cba5aac15aa94ba35148642208ee73379a0ce5a2b958aa49231147639190ae0,0x1dee56c3057cba5aab5569c4ba411a8642208ee73379acd0672d15cac55249187639190ae0,0x1dae5672fd7cba5aac15aa94ba35148642208ee73379a0ce5a2b958aa49231147639190ae0,0x1cadc672f974b5582b554a94ba35148642208ee73379a0ce5a2b958aa49231147639190ae0,0xec72b397cba5aac15aa94ba35148642208ee73379a0ce5a2b958aa49231147639190adf,0x1dae56c3397cba5aac15aa94ba35148642208ee73379a0ce5a2b958aa49231147639190ae0,0x1cadc6c3397cba5aac15aa94ba35148642208ee73379a0ce5a2b958aa49231147639190ae0,0x1dce56bb397cba5aac15aa94ba35148642208ee73379a0ce5a2b958aa49231147639190ae0,0x1cace5f2e96ab056aa53e9747a35148642208ee73379a0ce5a2b958aa49231147639190ae0,0x1dee56c3057cba5aab556a94e25d208d432110477399bcd66833968ae562a9187639190ae0,0xef6c3057cba5aab556a94e25d208d432110477399acd0672d15cac55249187639190adf,0xed72b397cba5aac15aa94ba35148642208ee73379a0ce5a2b958aa49231147639190adf,0xee72b397cba5aac15aa94ba35148642208ee73379a0ce5a2b958aa49231147639190adf,0x1dee56c33982be5d2d560ad55aa53897482350c84411dce66b3419cae562a9187639190ae0,0x1ded8673057cba5aab556a94e25d208d432110477399acd0672d15cac55249187639190ae0,0x3959cbe5dae96cb5582b95aab54a71208a43208e66f3599cb65a2b958aa4a249188a3b1c8ca1,0x3bdcad860af974b5582b556a84e25d208d45210ee73379acd0672d15cac55249188a3b1c0ca1,0x1cadc6c3397cb85aac156a94e25d208b452190882399bcd6672d968ae562a9188a39190ae0,0x3bdcad8673057cba5aab556a84e25d208d452190477399bcd6672d15cac5424918883b1c8ca1,0x733959ece5faf960ab54a712e9045a290c84411cce06f359a0ce572a9188a39190ade,0x3bdcad860af974b556aad509c4ba411a86421dce66f359a0ce5a2b958aa49231107639190a21,0x74b95b0ce5faf96ab055aa53897482290c84411d0e66f359a0ce572b1548a39190ade,0x3bdcad860af974b5582b556a84e25d1a8a43210ee73379acd0672d15cac54249188a3b1c8ca1,0x1dee56c30574b5582b556a84e2411a8a43210ee73379acd05a2b958aa49231147639190a20,0x77b95b0c15f2e96aad55aa1389746a10ee73379acd0672d158a849231107638190a1e,0x3bdcad8673057cba5aab556a84e25d208d4521908823b9ccde6b33968ac5424918883b1c0ca1,0x76395aece5f2e16ab054a712e90452190476399bcd6672d15caa451c8ada,0x395aece5f25d208a43208e66f3599ca2411b88d1,0x395aeb5582953890451ccde602d15caa451a04d1,0x3957c9c4ba290c7b399bcd6672d15c9c451c81d1,0x35d6a9c482250c813b1ccd6662d15caa441c8a91,0x3957cb0512712e8a3d9d8e66f3599cb44e2281d1]
def bk51 : Array Nat := #[0x381aece5f2d5529c4ba410c823598cae551c8ad1,0x395609c4ba290c7b399bcd6602d15c9c451c8051,0x3957cb8582712e8a3d9d8e66f3599cb44e228051,0x381aece5f2d5529c4ba410c823599cae551c8ad1,0x395aece5f2d560a94e240fc732d15caa3e1a8751,0x35da6ce5aac15292482290c822d15caa451c8ad1,0x3957cb0512712e8a399bcd6672d15c9c451a8091,0x3957cb0512712e86399bcd6672d15c9c3e1c8091,0x3957cb8582893897451d8e66f3599cb44e228091,0x395aece5aac14a9c4ba40fc7337980ae551f0291,0x3957cb8582712e8a3b1ccde6b33968ae4e228011,0x395aece5f29d2e90452190473379acce411b88d1,0x395aece5f29d2e90452190473379acce511b88d1,0x395aece5f29d2e90452190473379acce512088d1,0x395aece5f2712e90452190473379acce411b80d1,0x3957cb04e25d14863d9d8e66f3599cb4451b80d1,0x36daed3672e16ab054a4114822d15caa451c8ad1,0x3957ca94e25d14863d9d8e66f3599cae411c8ad1,0x36daed3672e16ab054a4920822d15caa451c8ad1,0x30d7cb5582a4ec75399bcd6672d15caa451c8ad1,0x395aece5f2712e90452190473379acce512082d1,0x395aece4e25d208a43208e66f35980a2411c82d1,0x395aece5f29d3897482290c82399bcd6672885d1,0x395aece5f29d389748218fc73379acce511c85d1,0x35d9cb85aac15292482290c822d15caa451c8ad1,0x1aece5c2d560a9482290c822d15caa451c8ad0,0x2e160a2451ecb457271149,0x35da6ce5c2d560a9482290c822d15caa451c8ad1,0x395aece5f2712e90452190476399bcd667288211,0x395aece5f2d5529c4ba411486411acc6531c89d1,0x395aece5f2d560a94e25d208a43208c6532189d1,0x271349745218f676399bcd6672d15caa451c8ad1]
def bk52 : Array Nat := #[0x395aece5f2d560a94e25d14863d9acc6431c8111,0x3957cb0512712e8a431ecde6b31968ae451c8111,0x395aece5f2d560a94e25d208a43208a6431a03d1,0x395aece5aac14a9c4ba411486411aca6431c83d1,0x395aece5f2e16ab054a712e904521904532183d1,0x395aece5f2d560a94e25d20863f1acc6531c8651,0x395aece5f2e16ab054a712e90452190463298651,0x2713497452190476399bcd6672d15caa451c8ad1,0x395aece5f2e16ab054a712e90452190457298251,0x395aece5f2d560a94e25d208a43208d6631b8811,0x395aece5f29d3897482290c82399bcd6671b8811,0x32586be5c2d560a93b1ccde672d15caa451c8ad1,0x32586b85aac152763a9ccde672d15caa451c8ad1,0x395aece5f29d3897482290c823598cae451c8ad1,0x2f970b5582a4ec75399bcd6672d15caa451c8ad1,0x17cb85aac15276399bcd6672d15caa451c8ad0,0x2f970b5582a4ae53218e49,0x30d7cb85aac15276399bcd6672d15caa451c8ad1,0x395aece5f2e16ab054a29007637994b454228a51,0x1aece5aaa538974821904733599cae551c8ad0,0x2710c7b399acce57270e49,0x3b1cabe5c2c1449c4ba28ec73379acce5a228151,0x381aece5aaa538974821904733599cae551c8ad1,0x35d9cbd5aaa538974821904733599cae551c8ad1,0x3b1cad7672f970b5582a514803b1bcb454228451,0x3b1cad7672f970b5582a5147637994b4542286d1,0x17ca94e25d208a43208e66b3395caa451c8ad0,0x2712089409ccae55220e49,0x2712086409ccd6572a8e49,0x2a1389044a04e6572a9109,0x2f5509c48204e6572a8e49,0x3b1cad7672f970b5582a53897482290c82218951]
def bk53 : Array Nat := #[0x13897482190476399bcd6672d15caa451c8ad0,0x2712086411acc657298e49,0x2713497482190476399bcd6672d15caa451c8ad1,0x2712e9044a190476399bcd6672d15caa451c8ad1,0x35d7ab554271208943204e66b3315caa441c8a91,0x35d7ab5542712086409d8e66b33168ae551c8a91,0x35d7ab550a712089431ccd6662d15caa441c8191,0x3b1aeb85aa71208943204ec732d15caa441a0491,0x35d70b54e2411286409d8e66b2d15caa441c8491,0x35d9cb554a71208943208ec732d15caa441a0ad1,0x35d6a9c482250c813b1ccde672d15caa451a0ad1,0x3b1aebd5c2d5509c481d8e66b33168ae551a8711,0x35d7ab85aaa13890431d8e66b33168ae551c8711,0x35d9cbd5aaa53890411d8e66b33168ae551a8ad1,0x35d7ab5542712076399bcd6672d15caa451a8ad1,0x1cace5f2c152984ba290c82379acce451c8ad0,0x3959cbe582a51480379149,0xe5672f960a94ba290c82379acce451c8acf,0x35d7ab554271208943204e66b2d15caa421c8991,0x1dee56c3057cba5aab556a84e25d1a86421dce66f359a0ce5a2b958a849231107639190a20,0x1ded860ae96aad55aa1389046a190877399acd05a2b958aa49231107639190a1c,0x36182b556aad509043a10d6682b1547639190a11,0x33d82ad55aa11a86421acd049231107639190a11,0x3055aab542611a86421acd049231107639190a11,0x3055aab542350c84381acd049231107639190a11,0x3617eb555aa1369045a10e6682b1548c44190a11,0x3616aab5426d208b421ccd05a2b1548c44190a11,0x3617eb555aa120843b9ccd05a2b1548c44190a11,0x3616aab5424116843b9ccd05a2b1548c44190a11,0x3617eb555aa13690421ccd05a2b1548c44190a11,0x3617eb555aa1208b421ccd05a2b1548c44190a11,0x2451a86421ccd8682d158aa49231107639190a11]
def bk54 : Array Nat := #[0x35d80b556aa1208c431fce66b3215492441c8a11,0x2d55aa84e24118863f9ccd6642b95492441c8a11,0x3016aad542712086399acc85a2b95492441c8a11,0x35d6aad54271208c431fce66b2b95492441c8a11,0x35d80b556aa13890431fce66b3215492441c8a11,0x77b95b0c15d2d560ad55aa1388d452190877379acd05a2b958a849231147639190a1e,0x3b5cace5faf970b054a712e9045a290c823b9ccde6b3419cb4572a9188a39168add,0x3957ebe4e25d168a3d9ccde6b3419c8c411680d1,0x3959cbf5f2c152974822d14864118ca6431609d1,0x3819cbe59aa538974821904733599cae551c8ad1,0x3bdb0ce60ae96aad55aa5389046a1908823b9acd05a2b958aa49231107639190add,0x35d80b556aa5389046219046b3215492441c8ad1,0x36182b556aad509c481acd05a2b958aa35180711,0x36182ab482350c84409acd056289187637190891,0xed72b619cbe5c2d560a94e25d208b4521908823b9ccde6b33968ae562a9188a39178adf,0x1dee56c3057cba5aab556a94e25d1a86421dce66f359a0ce5a2b958a849231107639190ae0,0x77b6182be5d2d55aab54a71208d43210ee73359a0ce5a2b958aa49231107639190ade,0x3bdcad860af974b556aad529c4ba411a86421dce66f359a0ce5a2b958aa49231107639190ae1,0x1ded860af974b556aad529c46a190877359a0ce5a2b958a849231107639190adc,0x3616a9c46a1908772d15cac54249188834178411,0x3057cad55aa4e06b3419c9449231107639190ad1,0x3057cb65aab556a93a9acd0672b1507639190ad1,0x3617ebe5aaad528b421a0ce5a2b1508c44190ad1,0x3617ebe5aaad52843b9a0ce5a2b1508c44190ad1,0x36170b555aa516843b9a0ce5a2b1508c44190ad1,0x3617eb555aa516843b9a0ce5a2b1508c44190ad1,0x2451a86421b0d0672d158a849231107639190ad1,0x33d82be56aad529c43a19086b3419c7639190ad1,0x36174b54e2350c843b968ae562a1248c44178411,0x36182be5aab556a94e1dcd0652d15cac541806d1,0x35d80be5aab5529c46218fe6b3395092441c8ad1,0x3017cb556aa538863b1acce5a2b95092441c8ad1]
def bk55 : Array Nat := #[0x35d6aad54a7118863f9acce5a2b95092441c8ad1,0x35d80b556aa5388c431fcd6672b95092441c8ad1,0x3017cba5aab552763a9acce5a2b95092441c8ad1,0x36182b556aad509c46a19086b2b9247639188991,0x3617cb555aa516843b9a0ce5a2b1508c44190ad1,0x35d7cb556aa5388c431fcd6672b95092441c8ad1,0x35d80be5aab5529c431fcd6672b95092441c8ad1,0x3017cb556aa5388c431acce5a2b95092441c8ad1,0xef6c33982be5d2d55aab54a71208d432110477359a0ce5a2b958aa49231107639190adf,0x1ded8673057cba5aab556a94e2411a8642208ee73359a0ce5a2b958aa49231107639190ae0,0x3bdcad860af974b556aad509c4ba35148642208ee73379acd0672d158a849231147639190ae1,0xed72b619cbf5f2e16ab055aa53897482290c823b9ccde6b3419cb4572b1548a39180adf,0x3bdcad860af974b556aad509c4ba35148642208ee73379acd0672d15cac54249188a3b1c8ca1,0xef72b6182ba5aac15aab542711a8a432110477379acd05a2b958a849231147639190adf,0x1ded860ae96aad55aa1388d4521908823b9acd05a2b958a849231147639190adc,0x36182b556aad508742208d6682b1507639190ad1,0x249228d4521908822b958a849231147639190ad1,0x36182b556aad509c3b9acd05a2b958a835180691,0x33d5cad55aa11a8a432110449231147639190ad1,0x3617eb555aa1168a42208d05a2b1508c45190ad1,0x3617eb85aaad5084411dcd05a2b1508c45190ad1,0x3616aab5422d1484411dcd05a2b1508c45190ad1,0x3617eb555aa11684411dcd05a2b1508c45190ad1,0x3616a9c46a2908803b968ae562a1248c45178451,0x2711a8a43211046c359a0ae49231147639190ad1,0x36182ba5aab556a84e1dcd6682d15cac54180691,0x35d80b556aa1388c45219046b3215092451c8ad1,0x3016aad542710c823b1acc85a2b95092451c8ad1,0x35d6aad54271188a43208d65a2b95092451c8ad1,0x35d80b556aa1388c43208d6642b95092451c8ad1,0x3055a9c46a18ee6b34168ae49231107639168191,0x35d74b556aa1248c45219045a2b95092451c8ad1]
def bk56 : Array Nat := #[0x3617eb555aa11484411dcd05a2b1508c45190ad1,0x2d55aa84e23d188a43208d6642b95092451c8ad1,0x3016aad542711486411acc85a2b95092451c8ad1,0x35d80b556aa1388c45219046b2b95092451c8ad1,0x77b619cc15d2d55aab54a71208d4521908823b9acd05a2b958aa49231147639190ade,0x77b6182be5d2d55aab54a711a8a432110477359a0ce5a2b958a849231147639190ade,0x1ded8673057cba5aab556a94e2411a8a432110477359a0ce5a2b958aa49231147639190ae0,0x1dee56c3057cba5aac15aab54a712e8d421dce66f359a0ce5a2b958aa49231147639190ae0,0xed72b619cbf5f2c156a94e25d208b4521908823b9ccde6b3419cae562a9188a39190adf,0x77b95b0c15d2d560ad55aa5388d452190877379acd05a2b958aa49231147639190ade,0x1dee56c30574b5582b556a94e2411a8a43210ee73379acd05a2b958aa49231147639190ae0,0x3b9cad7673017cb054a712e90462290c823b1ccde6b3395caa451c8ad9,0x395aece4e25d208c45219047337980ae552082d1,0x395aec05f2712e903f1ccde6b3395caa3e1a8751,0x395aece582712e90462290c82399bcc0512282d1,0x39580be582712e8c45218f673379acce451b80d1,0x395aece602712e90462290c823598ca6431c89d1,0x39580be4e25d188a431ece66f3599cae411c80d1,0x3b9aec04e2411886409d8e66b3315caa401c8a91,0x39580be512712e8c431ece66f3599cae4e1c81d1,0x39580be58289389746228f673379acce4e2281d1,0x3959cbe582a53697462290476399bcce4e228ad1,0x395aece582953897482311486411bcc0451a04d1,0x395aece52a712e90462290c8239980ae551a04d1,0x381aece52a712e9043208ec733599cae551c8ad1,0x395aeb04e25d208c45218f67337980aa451a0051,0x39580b04e25d188a431ece66f359809c451c8051,0x381aece602f9529c4ba4104733599cae551c8ad1,0x381aece602f9529c4ba410c823599cae551c8ad1,0x395aece602f960a94e25cfc73379acce3e1a8751,0x395aece602f960a94c25d1482379acce451a8ad1,0x35da6ce582b152924823114864115caa451c8ad1]
def bk57 : Array Nat := #[0x395aece602f960a94e25ce66f3599c9c3e1a8091,0x395aec05f2c1449c4ba40e66f3599caa3e1a8091,0x39580be58289389746228e66f3599c9c451a8091,0x39580be58289389746218e66f3599c9c3e1c8091,0x35da6ce582a52490462290c822c15caa451c8ad1,0x395aece602f960a94e25d207e399bcc0551f0291,0x395aece58295389748231147e399bcc055228291,0x39580be582a53097462290c82379acce451c8ad1,0x3959cc05f2c152984ba311486411acce451c8ad1,0x30d80be5a2c15275399bcd6672b95490451c8ad1,0x35d9cc3602f960a948208de6b3395490451c8ad1,0x35d9cc05f2c15290411d4e66b3395caa451c8ad1,0x35d9cc05f2c1529248219046b3395caa451c8ad1,0x35da6ce602f960a948229046b3395caa451c8ad1,0x395aece602f960a94e25d207e399bcd6672885d1,0x395aece602f94e9c4ba40fc73379acce572a85d1,0x35d9cb054a512490462290c822c15caa451c8ad1,0x35daad3672c158a94823114864115caa451c8ad1,0x365aece582b152924823114864115caa451c8ad1,0x36daed3672c15290462290c822c15caa451c8ad1,0x375aed3672c152924823114864115caa451c8ad1,0x3017cb054a49208c45219046b3395caa451c8ad1,0x30d80be582a5188a43208de6b3395caa451c8ad1,0x34d9cc05f2c1528c45219046b3395caa451c8ad1,0x3017cb4582a5188a43208ea733599caa451c8ad1,0x395aece602f960a94ba41188a43208c6532189d1,0x395aece602f960a94da5d208a411bcce53228ad1,0x395aece602f960a94ba3114863d9acc6431c8111,0x39580be582893897462290c7b379acc6451c8111,0x395aece582a53697482290476399bcce55228ad1,0x395aece5f2c1529b4ba410476399bcce55228ad1,0x395aece602f960a94ba41188a43208a6431a03d1]
def bk58 : Array Nat := #[0x395aece582953897482311486411ccaa431a03d1,0x395aece582953897482311486411bca6451a03d1,0x395aece602c14a97482311486411aca6431c83d1,0x30d80be582a4ec75399bcd6672b95490451c8ad1,0x30d80be5a2c152763a9ccde6b3395caa451c8ad1,0x395aece602f960a94e25d207e399acc6551a8651,0x395aece602f960a94ba4118863f1acc6531c8651,0x2713497462290c823b1ccde6b3395caa451c8ad1,0x2713497482311486411d8e66f3395caa451c8ad1,0x395aece602f960a94ba41188a43208d6631b8811,0x395aece602f94e9c4ba41188a43208d6631c8811,0x35d9cb054a410475399bcd6672b95490451c8ad1,0x35d9cb0562a5249043208e66f3395caa451c8ad1,0x35d9cc35f2c15290411d8e66f3395caa451c8ad1,0x35da6ce582a5208a411d8e66f3395caa451c8ad1,0x3017cb0549e0ec75399bcd6672b95490451c8ad1,0x31586c05f2c15276399bcd6672b95490451c8ad1,0x32180be5a2c152763a9ccde6b3395caa451c8ad1,0x32586c05f2d160a93b1ccde6b3395caa451c8ad1,0x32d86c05f2c152763a9ccde6b3395caa451c8ad1,0x2c1528c4521904763a9ccde6b3395caa451c8ad1,0x2c15292482311486411d8e66f3395caa451c8ad1,0x34d9cb0562a5188a43208e66f3395caa451c8ad1,0x30d7cb4582a5188a43208e66f3395caa451c8ad1,0x395aece602f960a946229007637994a0451b0a51,0x3b9cad7673017cb054a3114803b1bcca451b0a51,0x35d389a4ba410c823b1ccde6b3395caa3e1c8ad1,0x3b9ae9c4ba411886411d8e66b3395caa401c8ad1,0x3b9cad7673017cb054a3114803b1bcca50228a51,0x38180be512712e904621904733599cae551c8ad1,0x301389a4ba41188a43208e66b3395caa431c8ad1,0x3b9809c4ba411886411d8e66b3395caa401c8ad1]
def bk59 : Array Nat := #[0x3b9aec0532712e904621904733599cae551c8ad1,0x1dce56bb3980be582a5188a3b1bcca451b0150,0x3a9c0d7672f952853c9c89,0x27d348c451d8de6a228d89,0x39580be58289389746228ec73379acce451b0151,0x381aece5f2a538974821904733599cae551c8ad1,0x3a9c0d7672a538974821904733599cae551c8ad1,0x3a9aece602a538974821904733599cae551c8ad1,0x1dce56bb3980be582a5188a401d8de50228450,0x3a9c0d7672a50a80391409,0x27d348f462290076281149,0x395aece582953897482311486411d8de50228451,0x3819cc05f2a538974821904733599cae551c8ad1,0x3a9c0c05f2a538974821904733599cae551c8ad1,0x3a9aec05f2a538974821904733599cae551c8ad1,0x395aece602f960a94e25cec73379acce501f06d1,0x2713497482311486411ccde6b3395caa451c8ad1,0x1dce56bb3980be582a5188a3b1bcca502286d0,0x3a9c0d7673017ca9391409,0x27d348f46228f876281149,0x27d389a4ba41188a43208e66b3395caa451c8ad1,0x27d3897482311486411d8e66b3395caa451c8ad1,0x395aece602f960a946229007637994a0451b0851,0x395aece602f960a94e25d208c4521904431b0951,0x1dce56bb3980be582a5188a401d8de451b0950,0x3a9c0d7673017ca942a009,0x27d348f462290076379149,0x2713497482290c823b1ccde6b3395caa451c8ad1,0x27d389a4ba410c823b1ccde6b3395caa451c8ad1,0x27d3897482310c823b1ccde6b3395caa451c8ad1,0x35d80a64e2411886409d8e66b3315caa401c8a91,0x3b9aec053271208c43204ec7335998ae551c8a91]
def bk60 : Array Nat := #[0x3959cbe582a53097462290c823b1bcce451a0ad1,0x3b9cace602f960a94ba3114823b1bcce451b0ad1,0x39580be4e25d18863b1ccde6b3395c9c401c8191,0x1dcd760271208c431d8e66b3315caa401c8190,0x39d809846218dc6b200e49,0x3b1ae9b48224ec732a9009,0x3b1cad7672f960a94da5d208a411bcce55228ad1,0x3b1cad7672f960a94ba4114823b1bcce55228ad1,0x395aece4e25d208c4521904763995caa401a0491,0x3959cc05f2c152984ba290c82379acce451c8ad1,0x1dcd760271208c43204ec733595caa401c8490,0x39d9ac04c231026e2f9009,0x3b1ae9b482250276399549,0x39dcace602f960a94c25d1482379acce451c8ad1,0x39dcace602f960a94ba311482379acce451c8ad1,0x3959cbe582a53097462290c82379acce451c8ad1,0x395aec05f2993897481d8e66f3599cae551a8711,0x1dcd760299389046218ec7335998ae551c8710,0x39d9ac053261187d370e49,0x3b1aebd5326d2076399549,0x39dcace5f2c152984ba311486411bcce451c8ad1,0x39dcace602f960a94ba311486411bcce451c8ad1,0x35d80a64e2411886409d8e66b3315caa401c8891,0x3959cbe582a53697482290476399bcce55228ad1,0x395aece602993897482311486411acae531c8991,0x1dcd7602993890462190276399acae551c8990,0x39d9ac0532611881358e49,0x3b1aea64da411276399549,0x3b1cace5f2c1529b4ba290476399bcce55228ad1,0x3b1cad7672f960a94ba290476399bcce55228ad1,0xef6c30574b5582b556a94e2350c843b9acd05a2b958aa49231147639190adb,0x3616ab052a711a772d15cac55249188a341784d1]
def bk61 : Array Nat := #[0x1ded860aad388d43210ee6b341588c3b1b8c90,0x3b5b0bf55a2cee56230c89,0x36182b556aad52843a9acd0572b1547639190ad1,0x36182b556aad528743210d6682b1547639190ad1,0x36182b556aad5287421d0d6682b1547639190ad1,0x36182b5582b556a94e1dcb4572b1547c35180751,0x3055aab54a611a86421acd049231147639190ad1,0x33d82ad55aa51a86421acd049231147639190ad1,0x35d80b5582b5529c46218fe6b3215492451c8ad1,0x30174b5582b552763a9acc85a2b95492451c8ad1,0x35d74b5582b5529246218fe5a2b95492451c8ad1,0x1deba5aac15aa9469dcb4572a9248c451c8ad0,0x3617eb5582ad528b421dcd05a2b1548c45190ad1,0x3617eb85aac156a9421dcd05a2b1548c45190ad1,0x36170b5582ad528b421dcd05a2b1548c45190ad1,0x3617eb85aaad528b421dcd05a2b1548c45190ad1,0x249228d43210d05a2b958aa49231147639190ad1,0x2611a86421b0d6682d158aa49231147639190ad1,0x2451a86421dcd8682d158aa49231147639190ad1,0x3616aae56aad529c43a19086b2b1547639190ad1,0x3056cb556aad529c431acd0572b1547639190ad1,0x3616ab052a711a843b968ae562a9248c45178451,0x271228d43210d65a2b958aa49231147639190ad1,0x36182b5582b556a94e1dcd05a2b958aa3e1806d1,0x3016ab056aa538863b1acc85a2b95492451c8ad1,0x35d6ab056aa5388c431fcd65a2b95492451c8ad1,0xef6c305569c46a190877359a0ac461d8c8f,0x3016ab056aa5388c431acc85a2b95492451c8ad1,0x35d80b5582b5529c46218fe6b2b95492451c8ad1,0x2710c6c359a0b4572b1549449231147639190ad1,0x3055a9c46a18d6682d15c9c49231107639168191,0x3616a9c46a1908772d15cac55249188834178491]
def bk62 : Array Nat := #[0x36182b556aad509c3b9acd05a2b958aa35180711,0x36182b556aad509c46a19086b299247639188991,0x36172b85aac156a9421dcd05a2b1548c45190ad1,0x3bdb0c15d2d560ad55aa5389046a190877399acd05a2b958aa49231147639190add,0x3617eb555aa5369045a10e6682b1548c45190ad1,0x77b619cc15d2d560ad55aa5389046a1908823b9acd05a2b958aa49231147639190ade,0x3619cb5582ad529045a11045a2b1548c45190ad1,0x33960ae56aad528d432110449231147639190ad1,0x35d9cb5582b55292482310c822b95492451c8ad1,0x3bdb0c15f2e96ab056aad529c46a190877359a0ce5a2b958aa49231147639190add,0x35d6ab056aa5388c431fcd6672b95492451c8ad1,0x3057cb056aad526b3419c9449231147639190ad1,0x3017cb5582b552763a9acce5a2b95492451c8ad1,0xef6c3057cba5aac15aab54a71208d43210ee73359a0ce5a2b958aa49231147639190adf,0x1ded8673057cba5aac15aab54a71208d432110477359a0ce5a2b958aa49231147639190ae0,0x3bdb0c15d2d560ad55aa5388d4521908823b9acd05a2b958aa49231147639190add,0x3016ab056aa53886411acc85a2b95492451c8ad1,0x2c15cad55aa51a8a432110449231147639190ad1,0x35d6ab056aa5248c45219045a2b95492451c8ad1,0xef72b6182ba5aac15aab54a711a8a432110477379acd05a2b958aa49231147639190adf,0xef6c33982ba5aac15aab54a71208d4521908823b9acd05a2b958aa49231147639190adf,0xef6c3057cba5aac15aab54a711a8a432110477359a0ce5a2b958aa49231147639190adf,0x1cade6c3397cba5aac15cad55aa5389748235148642208e66f3599cae55249147639188ae0,0x3b5cad8672fd7cb85aac156a94e25d208b452190882399bcd6672b9548a39188add,0x3957ebe582892e8b451ece66f3599c9c451601d1,0x395b0ce5faf956a74ba41168a432110463188811,0x2713497482290c82399bcd6672c95caa451c8ad1,0x1dee56c3057cba5aab556a84e25d1a86421dce66f359a0ce5a2b958aa49231147639190ae0,0x77b6182ba5aab556a84e2411a86421dce66f359a0ce5a2b958aa49231147639190ade,0x3bdcad860af974b556aad509c4ba411a86421dce66f359a0ce5a2b958aa49231147639190ae1,0x1dee56c30574b5582b556a84e2351486421dce66f359a0ce5a2b958aa49231147639190ae0,0x3bdcad860ae96ab056aad509c482351486421dce66f359a0ce5a2b958aa49231147639190ae1]
def bk63 : Array Nat := #[0x1dce56bb3980be5d2d560ad54a712e90462290c82399bcd6672b95492451c8adc,0x3959cc05f2d560ad54a3114803799492451c0a51,0x395aece602f96ab056aa5188a3799492451c0151,0x395aece602f974b5582b5528c45200de49228451,0x395aece602f974b5582b5528c451bcca492286d1,0x395aece602f96ab056aa5188a401bc92451c0951,0x35d80b556aa1389046219027335998aa491c8a91,0x35d80ba5aab5389046218e66b3315caa491c8191,0x35d80ba5aab538904621902733595caa491c8491,0x35d80b556aa1389046218e66b3315caa491c8711,0x35d80b556aa138904621902733595caa491c8991,0x77b95b0c15f2e96aad55aa1389746a10ee73379acd0672d158aa49231147638190ade,0x3bdb0c15d2d55aab542711a86421dce66f359a0ce5a2b958aa49231147639190add,0x35d80b556aa1388c431fce66b3395492451c8ad1,0x3616a9c46a1908732d15cac55249188834178491,0x36182ab46a190873359a0cc56289187637190891,0xef72b619cbe5d2d560a94e25d208d452190882399bcd6672b95492451c8adb,0x36174b54e2411a8642204e66b3315caa491c8a91,0x3bdb0ba5aa71208d4321102733595caa491c8a91,0x395609c4ba3514863d9ccde6b3013892451c8051,0x395b0ce5f2d560a94e25ce66f3599c9c3e1a8091,0x395b0be5aac1449c4ba40e66f3599caa3e1a8091,0x3957cb0512712e8d451ccde6b3393892451a8091,0x3957cb0512712e8d431ccde6b33938923e1c8091,0x395b0ce5f2d560a94e25d207e399bcc0551f0291,0x3619cb5582a5249043a1908822b95492451c8ad1,0x361a6ce5aac1529045a2908822b95492451c8ad1,0x30d7cb65aac15273379acce55251248a39170ad1,0x30d7cba5aac15275399bcd6672b95492451c8ad1,0x2d560a949245208d4521908822b95492451c8ad1,0x34d9ece5aac1528d4521908822b95492451c8ad1,0x3957cb0512712e8d45218f66f3598c92451c8111]
def bk64 : Array Nat := #[0x395b0ce5f2d560a94e25d207e399acc6551a8651,0x30d7cb5582a4ea73379acce572a92892451c8ad1,0x30d7cb65aac15275399bcd6672b95492451c8ad1,0x395b0ce5f2e96ab054a351484401bcca49228a51,0x3bdcad8672f974b5582a51a8a42200de49228a51,0x3bdcad8672f974b5582a51a8a401bcca49228a51,0x2f9529c4ba4520874321104733599cae551c8ad1,0x3bdcad8672f974b5582a51a8a42200de49228451,0x2712e914821d0c84411ccde6b3395caa451c8ad1,0x3bdcad8672f974b5582a51a8a42200de49228951,0x3bdcad8672f974b5582a51a8a42200de49228351,0x3bdb0ba5aa71208d43204e66b3315caa491c8a91,0x3959ece5f2c1529745a290882379acce451c8ad1,0x3bdb0ba5aa71208d4321102733595caa491c8491,0x3959ece5f2c1529745a290882399bcce55228ad1,0x3bdb0ba5aa71208d4321102733595caa491c8991,0x3bdb0ba5aa71208d4321102733595caa491c8391,0x77b95b0c15f2e96aad55aa5389746a10ee73379acd0672d158aa49231147639190ade,0x77b6182be5d2d55aab54a711a86421dce66f359a0ce5a2b958aa49231147639190ade,0x3057cad55aa4de6b3419c9449231147639190ad1,0x3017cb556aa4ea73379acce5a2b95492451c8ad1,0x2fd7cb65aaad5273379a0ce5a2b1548c45190ad1,0x1dee56c3057cba5aab556a94e25d1a86421dce66f359a0ce5a2b958aa49231147639190ae0,0xef6c3057cba5aab556a94e2411a86421dce66f359a0ce5a2b958aa49231147639190adf,0xef6c3057cba5aab556a946a10ee73379acd0672d158aa49231147639190adb,0x3bdb0ba5aa34ee7337980b4562a9248c451784d1,0x36174b546a10ee7337980b4562a9248c451784d1,0x3bdb0ba5aa350877399bcb4562a9248c451784d1,0x36182be5aab556a9399bcd668339689c3e1a8091,0x36182be5aab54473379acd0672d158aa3e1a8091,0x3057cad51234e66f359a0ce5a271248c451a8091,0x3057cad51234e66f359a0ce5a271247c3b1c8091]
def bk65 : Array Nat := #[0x3616aae56aad528742168ac55249147639190ad1,0x3616aad55aa516842d968ac55249188a39190ad1,0x2d55aa948a35085b2d158aa49231147639190ad1,0x33d6aae56aad528d42168aa49231147639190ad1,0x36182be5d2d55aab54a35086b3192476391889d1,0x3bdb0c15f2e96aad55aa51a6b3192476391889d1,0x3bdb0c15f2e96aad55aa51a843592476391889d1,0x3057cad51234de6b34194b449231147639168151,0x33d82be56aad5287421ccd668339547639190ad1,0x3bdb0ba5aa350877399bcb4562a9248c45178451,0x36182be5aab556a9399bcd0652d158aa3e1806d1,0x35d80be5aab5528c3f9ccde6b3395492451c8ad1,0x3017cba5aab55276399bcd6672d15492451c8ad1,0x24516843b9ccde6b3419cb4562a9188a39190ad1,0x3bdb0c15f2e96aad55aa51a84359247639188951,0x3055a8d399bcd668331689c49231147639168191,0x33d82be56aad5287421bcd668339147639190ad1,0x3bdb0ba5aa350877399bcb4562a9248c45178491,0x36182be5aab556a9399acd0662d158aa35180711,0x2f9529145a10ee73379a0ce5a2b1548c45190ad1,0x3bdb0c15f2e96aad55aa51a84359247639188991,0x3bdb0ba5aa350877399bcb4562a9248c45178411,0x3017cb556aa51876399bcd6672d15492451c8ad1,0x35d80be5aab55276399bcd6672d15492451c8ad1,0x3bdb0c15f2e96aad55aa51a84359247639188911,0x1ded860ae96aad55aa11a8a432110477399bcd0672d158aa49231147639190adc,0x36182b556aad5077399bcd0672d158aa3e180751,0x36182b556aad508d4521908822490c76391889d1,0x2fd6cb555aa0ee73379a0ce5a2b1548c45190ad1,0x3616aae56aad5087432110473339547639190ad1,0x3055a8d45218ee6f34194b449231147639168151,0x3056cb556aad5086411ccd0672b1547639190ad1]
def bk66 : Array Nat := #[0x3616a8d452110077399bcb4562a9248c45178451,0x36182b556aad5077399bcd0672d158aa3e1806d1,0x35d80b556aa1188a43208e66f3395492451c8ad1,0x36182ab46a290c84411bcd0652b118823b190851,0x36182ab46a290880399bcd0672b118823b190851,0x36182b556aad508d4521908822490c7639188951,0x3616aab5422d1484411bcce5a2b1548c45190ad1,0x3055aab54229046f3419c9449231147639190ad1,0x235148642208e06f361a0ce49231147639190ad1,0x36182ba5aab556a83b9ccde6833968ac55180711,0x36182ab46a290c84411ccd066289187637190891,0x36182ab46a190881399bcd067289187637190891,0x245168a42208ee73379a0ce5a2b1548c45190ad1,0x36182ba5aab556a846a290c84411247639188991,0x36182ba5aab556a83b9ccde6833968ac55180691,0x2d55aa847a311486411ccde6a3395492451c8ad1,0x3016aad542290c823b1ccde672d15492451c8ad1,0x35d6aad542311486411ccde672d15492451c8ad1,0x36182ba5aab556a846a290c84411247639188911,0x3bdcad860af974b556aad509c4ba35148642208ee73379acd0672d158aa49231147639190ae1,0xef6c30574b556aad509c46a290c84411dce66f359a0ce5a2b958aa49231147639190adf,0x3bdcad860ae96ab056aad509c46a290c84411dce66f359a0ce5a2b958aa49231147639190ae1,0x1ded860af974b556aad529c46a290c84411dce66f359a0ce5a2b958aa49231147639190ae0,0x1ded8673057cba5aab556a948235148642208ee73379acd0672d158aa49231147639190ae0,0x1dee56c33982be582ad529c4ba411a8a432110473379acce572a9147639188adc,0x36182ab4e2411a8642204e66b331547639188a91,0x3619cb0572ad529043a1908822a9147639188ad1,0x39582be4e25d1a8a431ece66f3599c823b1c80d1,0x30d82be582ad5273379acce55251147639188ad1,0x395b0ce4e25d208d452190882399bcc0552082d1,0x395b0ce5825d208d452190882399bcc0512282d1,0x395b0ce60af960ab54a5d207e399bcd6672885d1]
def bk67 : Array Nat := #[0x34d9cb0572ad528d4521908822a9147639188ad1,0x3819cbf5f2ad52974821104733799caa45188ad1,0x395b0ce582952e9046a290c84411ccaa431a03d1,0x395b0ce582952e9046a290c84411bca6451a03d1,0x2692e8d452190882399bcd86b339147639188ad1,0x3057cb6582ad5275399bcd6672a9147639188ad1,0x30d82be582ad5273379acce55241147639188ad1,0x2712e914821d0c84411ccd86b339547639188ad1,0x3959cc15f2c156a946a290880379948a3b188a51,0x381aece602f9529c4ba410c82399acce551c8ad1,0x3959cc15f2c156a946a290880379948a3b188851,0x395b0ce60af960ab54a351484401bc8a3b188951,0x395b0ce60af960ab54a351484401bc8a3b188791,0x3959cbf5f2c156a94ba2d1484411bcce45188ad1,0x3959cc05f2c15297462290c82379acce451c8ad1,0x36182ab4e2411a8642204e66b331547639188891,0x36182ab4e2411a8642204e66b2b9547639188991,0x36182ab4e2411a8642204e66b2b95476391887d1,0x77b6182ba5aac15aab54a711a86421dce66f359a0ce5a2b958aa49231147639190ade,0x30560ad55aa4de6b3419c9449231147639190ad1,0x3016ab056aa4ea73379acce5a2b95492451c8ad1,0x2fd6cb5582ad5273379a0ce5a2b1548c45190ad1,0xef6c30574b5582b556a94e2411a86421dce66f359a0ce5a2b958aa49231147639190adf,0x1dee56c30574b5582b556a94e2351486421dce66f359a0ce5a2b958aa49231147639190ae0,0xef6c30574b5582b556a946a10ee73379a0ce5a2b958aa49231147639190adb,0x3616ab052a34e66f3015cac55249188a341784d1,0x30560ad51234ee6f2d15c9c492311476391681d1,0x30560ad51234de6832968ae49231147639168151,0x36182ab46a10ee73379a0ce5628918823b1908d1,0x36182b556aad5287421a0ce572b1547639190ad1,0x3616ab0469dce66f30168ae562a9248c451a0051,0x30560ad469dce66f30168ae4e249188a3b1c8051]
def bk68 : Array Nat := #[0x36182b556aad5287421d0d0672b1547639190ad1,0x36182b5582b556a93b9ccb4572b1547c35180751,0x36182b5582b556a93b9ccde602d15cac551f0291,0x33d82b056aad528d421a0ce49231147639190ad1,0x3616ab052a34ee7337980b4572b1549246228291,0x33d82ad55aa51a84381a0ce49231147639190ad1,0x35d80b5582b5528c3f9ccde672b95492451c8ad1,0x30174b5582b55276399bcce5a2b95492451c8ad1,0x35d82ba5aac15aa9469fcb4572a9248a3b1c8ad1,0x1ccde6c3419cb4572b1549449231147639190ad1,0x36182b5582b556a946a10ae532490c76391889d1,0x36182ba5aac15aab54a34ae532490c76391889d1,0x30560ad51234e66f3419cb449231147638168151,0x3056cb556aad5274399a0ce572b1547639190ad1,0x36182b5582b556a9399bcd0672d158a83e1806d1,0x35d74b5582b5528c3f9ccce5a2b95492451c8ad1,0x3bdb0c155a350877399bcd0672b118823b190851,0x24516843b9ccde6833968ae562a9188a39190ad1,0x36182ba5aac15aab54a3508572490c7639188951,0x3055a8d399bcd0672d15c9c49231107639168191,0x30560ad55aa4e06f3419c9449231147639190ad1,0x36182b5582b556a9399a0cc5a2b958aa35180711,0x36182b556aad5073379a0ce5a2b958aa35180711,0x35d74b5582b5528c3f9bcce5a2b95492451c8ad1,0x3bdb0c155a350877399bcd0672b1448c3b190891,0x2c1529145a10ee73379a0ce5a2b1548c45190ad1,0x36182ba5aac15aab54a350857299247639188991,0x35d6ab056aa5187f399bcce5a2b95492451c8ad1,0xba5aac15aa9399bcce5a2b95492451c8acf,0x2e96ab05495ca649218e49,0x3016ab056aa51876399bcce5a2b95492451c8ad1,0x35d80b5582b55276399bcce5a2b95492451c8ad1]
def bk69 : Array Nat := #[0x3bdb0c15d2d560ad55aa51a842b9247639188911,0x3bdb0c15f2e96ab056aad528d421dce66f359a0ce5a2b958aa49231147639190add,0x3057cb5582b556a9469acc6532490c76391889d1,0xef6c3057cba5aac15aab54a711a86421dce66f359a0ce5a2b958aa49231147639190adf,0x1ded860af974b5582b556a94e2411a86421dce66f359a0ce5a2b958aa49231147639190ae0,0x77b6182ba5aac15aab54a35148642208ee73379a0ce5a2b958aa49231147639190ade,0x1ded860af974b5582b556a946a290c84411dce66f359a0ce5a2b958aa49231147639190ae0,0x3bdcad8673057cb3582ad529c4ba411a8a432110477399bcd6683395cac55231147639190ae1,0x1dee56c33982be582ad529c4ba411a8a432110477399bcd6683395cac55231147639190ae0,0x3bdcad8673057cba5aac15aab54a71208d45218fe77399bcd6642d15cac55249188a3b1c8ae1,0x3bdcad860af974b5582b5529c4ba411a8a431fcee73379acd0672d15cac55249188a3b1c8ae1,0x3bdcad86730574b5582b556a94e2411a8a432110477379acc85a2b958aa49231147639190ae1,0x3bdcad860af974b5582b556a94e25d208d431fcee73379acd0672d15cac55249147639190ae1,0x3bdcad760af974b5582b5529c4ba35148642208ee73379acd0672d15caa49231147639190ae1,0x3bdb0ce60af974b5582b556a94e2411a8a432110476359a0ce5a2b958aa49231147639190ae1,0x3bdcad860af974b5582b5509c4ba411a8a431fcee73379acd0672d15cac55249188a3b1c8ca1,0x3bdcad8673057cb8582ad529c4ba411a8a432110477399bcd6683395cac55231147639190ae1,0x3bdcad860af974b556aad529c4ba411a863f9dce66f359a0ce5a2b958aa49231147639190ae1,0x3bdcad860af974b5582b5529c4ba411a863f9dce66f359a0ce5a2b958aa49231147639190ae1,0x3bdcad760af974b5582b5529c4ba3514863f9dce66f359a0ce5a2b958aa49231147639190ae1,0x3bdcad760af974b5582b556a94e25d1a863f9dce66f359a0ce5a2b958aa49231147639190ae1,0x3bdcad760af974b5582b556a94e23514863f9dce66f359a0ce5a2b958aa49231147639190ae1,0x3bdcad760af974b5582b556a94e25d1a8a431fcee73379acd0672d15cac55249188a3b1c8ca1,0x3bdaec15f2e96ab056aad529c46a290c84411dce66f359a0ce5a2b958aa49231147639190ae1,0x72b619cbe5d2d560ad55aa53897482290c84411ccde6b33968ae562a9248a39190ade,0x1cae167b397ebe5d2d560ad55aa53897482290c84411ccde6b3419cb4572a9248a39190ae0,0x77b95b0c15f2e96ab055a712e9046a290877399bcd66833968ae562a9248c451d8c9e,0x3959cbe5d2d560ad54a712e90452190473379acce5a2b95492451c8ad9,0x3959cbe4e25d208a43208e66f3599ca2411b88d1,0x3957cb54e25d207e399bcd6672d15caa3e1a8751,0x3956ab052a71208a399bcc05a2b95492451a04d1,0x3959cad4e25d208a43208d6632b94c92431c89d1]
def bk70 : Array Nat := #[0x2d55a9c4ca411286409ccdc6b3315492441c8a91,0x3097ab556aa13890431ccdc6b3315492441c8a91,0x3499ab556aa1389044a1902733595492441c8a91,0x39560ad5127114863d9bcd65a2b93892451c81d1,0x3957cad512712e863d9ccde6b3395c9c491c81d1,0x3957cad54a712e863d9ccde6b3395c9c491c8ad1,0x3957cad512712e9043208e66f3599cae551c8ad1,0x3957cb0512712e8a3d9ccde6b339689c492281d1,0x3957cb0512712e8a3d9ccde6b33968aa49228ad1,0x3499cb556aa5389044a19046b2b95492441c8ad1,0x37d9cbd5aab5529c48219047335998aa491c8ad1,0x3959cb052a712e9045219046f3016892451a04d1,0x3959cb052a712e9045219046f3016892451c8ad1,0x3097cb556aa53890399b8d6672b95492441c8ad1,0x3959cb552a712e9045219047330168ae551a04d1,0x3959cb554a712e9045219047330168ae551a0ad1,0x3959cb552a712e904521904733599cae551c8ad1,0x3819cb552a712e9043208e66b33968ae551c8ad1,0x3959cb04e25d208a43208e66f3013892451a0051,0x3957cb04e25d14863d9ccde6b3393892451a0051,0x3956ab04e25d208a431ece66f3015492451a0051,0x39560ad4e25d14863d9ccde6b3013892451c8051,0x3819cbe5aab5529c4ba4104733599cae551c8ad1,0x3819cbe5aab5529c4ba410c823599cae551c8ad1,0x3959cbe5aac15aa94e240fc732d15caa3e1a8751,0x3959cbe5aac15aa94e24104732d15caa3e1a8ad1,0x3959cbe5aac15aa949240fc5a2b95492451c8ad1,0x3959cbe5aac15aa94e25cfc73379acce3e1a8751,0x3959cbe5aac15aa94e25cfc73379acce3e1c8ad1,0x2d53899482290c82399b8d6662b95492451c8ad1,0x3499ab556aa138904521904732b95492451c8ad1,0x3959cad4e25d208a43208d6632b94c92451c8ad1]
def bk71 : Array Nat := #[0x39560ad512711486411bcd65a2b93892451c8ad1,0x3959cbe5aac15aa94e25ce66f3599c9c3e1a8091,0x3957cb5582b5449c4ba40e66f3599caa3e1a8091,0x3957cb056a893897451ccde6b3393892451a8091,0x3957cb056a893897431ccde6b33938923e1c8091,0x34d9cb5582a5249045219045a2b95492451c8ad1,0x34d9cb5582b55292482290c822b95492451c8ad1,0x3959cbe5aac15aa94e25d207e399bcc0551f0291,0x3959cb5582953897482290c82399bcc0551f0291,0x3959cbe5aac14a9c4ba40fc73379acce551f0291,0x3959cb558295389748228fc7337980aa49228291,0x3957cb056aa5309745219046f3599c92451c8ad1,0x3959cbe582b552984ba290c823599c92451c8ad1,0x3959cbe53a712e90452190473379acce411b88d1,0x30d6ab056aa53890399bcc05a2b95492451c8ad1,0x34d9cb5582b5529c481f8e65a2b95492451c8ad1,0x3097ab5582b5529c481ccdc6b3315492451c8ad1,0x3499ab5582b5529c482250c813995492451c8ad1,0x3959cbe53a712e90452190473379acce511b88d1,0x3956ab056aa5248a431ecde5a2b95492451c8ad1,0x3956ab056aa51475399bcc05a2b95492451c8ad1,0x3957cba5aac15aa9451bcca5a2b95492451c8ad1,0x3959cba5aac15aa945200de5a2b95492451c8ad1,0x3959cbe53a712e90452190473379acce512088d1,0x34d6ab056aa5388a431ecd65a2b95492451c8ad1,0x30d7cb5582b5529c431acc65a2b95492451c8ad1,0x3097ab5582b5529c431ccdc6b3315492451c8ad1,0x3499ab5582b5529c482250c813595492451c8ad1,0x1cace5f2712e90452190473379acce411b80d0,0x34d9ca0492411482259049,0x30d7c75399bcd667208dc9,0x3957cb04e25d14863d9ccde6b3396892451b80d1]
def bk72 : Array Nat := #[0x3957cad4e25d14863d9ccde6b3395c92411c80d1,0x34d9cba5aac15aa949241045a2b95492451c8ad1,0x34d9cba5aac15aa948229045a2b95492451c8ad1,0x3499cb5582b55292482250c822b95492451c8ad1,0x1cace5f2712e90452190473379acce512082d0,0x34d9c92482290c82289049,0x30d7ca33a9ccde6b289049,0x3959cb54e25d208a43208e66f30168ae552082d1,0x3959cb04e25d208a43208e66f30168a2492282d1,0x30d7cba5aac15aa93a9acce5a2b95492451c8ad1,0x30d7cba5aac15aa9379acce5a2b95492451c8ad1,0x3097cb5582b55275399b8d6672b95492451c8ad1,0x3959cbe5aac15aa94e25d207e399bcd6672885d1,0x1cace5f29d3897482290c82399bcd6672885d0,0x34d9ca7492411482288f09,0x30d7ca73a9ccde6b339449,0x3959cbe5aa9d3897481f8e66f3599cb4572a85d1,0x34d74b5582b5529245219045a2b95492451c8ad1,0x34d9cba5aac15aa945219045a2b95492451c8ad1,0x3499ab5582b55292482290c822b95492451c8ad1,0x3959cbe5aac15aa94e218d6632b94c92431c89d1,0x3959cbe5aac15aa94e218d6672b94c92431c8ad1,0x3959cbe5aac15aa93a9acc65a2b95492451c8ad1,0x3957cb54e25d207e399bcd6672d15caa451a8ad1,0x3956ab052a71208a399bcce5a2b95492451a0ad1,0x3959cbe5aac15aa94e25d208a43208c6532189d1,0x3959cbe5aac15aa94e25d208a43208c655218ad1,0x2b53899482250c81399bcd6672b95492451c8ad1,0x3097ab556aa13886399bcd6672b95492451c8ad1,0x3959cbe5aac15aa94ba290c7b3598c92431c8111,0x3959cbe582b54497482290c823598c92431c8111,0x3957cb056a892e8a431ece66f3599c92431c8111]
def bk73 : Array Nat := #[0x3957cb056a89389745218f66f3598c92451c8111,0x3959cb5582a536974822904733799cb455228ad1,0x3959cbe5aac1529b4ba4104733799cb455228ad1,0x3959cbe5aac15aa94ba4114864114c92431a03d1,0x3959cb5582953897482290c823995492431a03d1,0x3959cb5582953897482290c823794c92451a03d1,0x3959cb5582b54a97482290c823594c92431c83d1,0x30d7cb056aa4ea73379acce5a2b95492451c8ad1,0x30d7cb5582b55275399bcd6672d15caa451c8ad1,0x3959cbe5aac15aa94ba411486411acc6531a8651,0x3959cbe5aac15aa94ba40fc73379acce531a8651,0x3959cbe5aac15aa94e25d207e399acc6551a8651,0x3959cbe5aac15aa94ba410c7e3598ca6491c8651,0x2713497452190473379acce5a2b95492451c8ad1,0x2713497482290c82399bcce5a2b95492451c8ad1,0x3959cbe5aac15aa94e25d208a43208d6631b8811,0x1cace5f29d3897482290c82399bcd6671b8810,0x34d9ca7492411486410dc9,0x30d7ca73a9ccde4f1f8dc9,0x3959cbe56a9d3897482290c823598cae491c8811,0x30d74b5582b55275399bcce5a2b95492451c8ad1,0x30d7cba5aac15aa9399bcce5a2b95492451c8ad1,0x3097ab5582b55275399bcd6672b95492451c8ad1,0x3959cbe5aac15aa945200de652d15092451c0a51,0x3959cbe5d2d560ad54a28de652d15092451c0a51,0x3959c9c4ba411486411ccde6b3395caa411c8ad1,0x3959c9c4ba411486411ccd6672b95492431c8ad1,0x3959cbe5d2d560ad54a29006f2d15092451c0a51,0x3957c9c4ba410c82399bcd6672d15caa3e1c8ad1,0x3957c9c4ba411486411ccde6b3395caa411c8ad1,0x3959cbe5d2d560ad54a29006f3296892451c0a51,0x2d5389a4ba410c82399bcd6672d15caa3e1c8ad1]
def bk74 : Array Nat := #[0x2d538994ba411286411ccdc6b3395492441c8ad1,0x3959cbe5d2d560ad54a29006f32968a849228a51,0x3817cad512712e9043208e66b3395caa491c8ad1,0x2b5389a4ba411486411ccd6672b95492431c8ad1,0x2b538994ba411286411ccdc6b3395492441c8ad1,0x37d9abd5aab550974821904733599caa491c8ad1,0x1cace5f2e96ab056aa5146f3296892451c0150,0x3819cbe5bad55279268e09,0x269146f32970b449228e09,0x3957cb056a893897451ccde6b3396892451c0151,0x3957cb056a89388a431bcd6652d15c92451c8151,0x3819cb75aaa538974821904733599cae551c8ad1,0x3819cbe5aaa538974821904733599cae551c8ad1,0x37d9cbd5aab5529c4ba410c82399acce551c8ad1,0x1cace5f2e96ab056aa5148037968a849228450,0x3819cb75aaa5005e2a0cc9,0x269148037970b454249149,0x3959cb5582953897482290c8237968a849228451,0x3959cb558295389045200e66f2d15caa49228451,0x3817cb756aa538974821904733599cae551c8ad1,0x3819cbe56aa538974821904733599cae551c8ad1,0x37d9abe5aab5529c4ba410c82399acce551c8ad1,0x3959cbe5aac15aa94e25ce66f3599cb4541f06d1,0x3959cbe5aac15aa94e240e66f32968ae551f06d1,0x1cace5f2e96ab056aa5146f32968a8492286d0,0x3819cbe5bad55aa9329509,0x269147c37970b454249149,0x2713497482290c82399bcd6672b95492451c8ad1,0x2713497482290c82399acce5c2b95492451c8ad1,0x2713297482290c82399b8d6672b95492451c8ad1,0x3959cbe5aac15aa94e25d208a4320892431c0951,0x1cace5f2e96ab056aa514803796892451c0950]
def bk75 : Array Nat := #[0x3819cbe5bad55aa9400e09,0x269148037970b452249149,0x3959cbe5aac15aa94e2290c803595c92431c8951,0x2713497482190473379acce5c2d15caa451c8ad1,0x2713297482250c82399bcd6672b95492451c8ad1,0x3919abd56aa1208943204e66e3599892441c8a91,0x37d9abd5aab5509c48219027335998aa491c8a91,0x37d9abe5aab5529c4821902733599cae551c8ad1,0x37d9abd5aab5509c4ba410c82399acce551c8ad1,0x3957cad4e25d1286399bcd6672b93892441c8191,0x3917ab556a712089431ccdc6b3315492441c8191,0x3957ab056a711486399bcd6662b93892451c8191,0x3917ab5582b55289431ccdc6b3315492451c8ad1,0x3917aad4e2250c73379acce5a2b95492451c8ad1,0x3917aad4ba411286411ccdc6b3395492441c8ad1,0x3959cb54e25d208a43208e66e2b95492441a0491,0x3959ab558271208a43204e66f2b95492451a0491,0x3919ab556a71208943204e66e3595492441c8491,0x3919ab54e2411486411ccdc5a2b95492451c8ad1,0x3919ab5582b5529044a1902733715492451c8ad1,0x3919ab54ba411286411ccdc6b3395492441c8ad1,0x3959cbe5aac15aa94e240e66e35998ae551a8711,0x3959abe5aab5509c4ba40e66f3599cae551a8711,0x3919abd5aab5509c48218e66e35998aa491c8711,0x3919abe5aab5529c481ccdc6b33968ae551c8ad1,0x3919abd5aac15aa9481ccdc6b3315492451c8ad1,0x3919abd5aab55097482190473371acce551c8ad1,0x3959cbe5aac15aa94e2411286409aca6491c8991,0x3959cbd5aab5509c4ba411486411aca6491c8991,0x3919abd5aab5509c482250c81399acaa491c8991,0x3919cbd5aab5529c482250c823595caa491c8ad1,0x3919abd5aac15aa9482250c813595492451c8ad1]
def bk76 : Array Nat := #[0x3919abd5aab55097482250c82399acce491c8ad1,0x77b95b0c15f2e960ad55a712e8d452190877399bcd66833968ae56249188a3b1c8c9e,0x77b95b0c15d2d560ad55a71208d452190877399bcd6682d15cac55249188a3b1c8c9e,0x3b5cad8672fd7cba5aac15aab54a712e90452190477399bcd66833968ae562a9248a39180ae1,0x3a5cad8672fd7cba5aac15aab54a712e90452190474399bcd66833968ae562a9248a39180ae1,0x1dee56c3057cba582b5569c4ba35148642208ee73379acd0672d15cac49231147639190ae0,0x1d8e56bb397cba5aac15aa94e25d208a43208ec73379acce5a2b95492451c8adc,0x395aece5f2d560ad54a5d208a43208c6532189d1,0x395aece5f2d560ad54a29006f3295092451c0a51,0x395aece5f2d560ad54a29006f32968a849228a51,0x395aece5f2d560ad54a28ec6f3296892451c0151,0x395aece5f2d560ad54a29007637968a849228451,0x395aece5f2d560ad54a28ec6f32968a8492286d1,0x395aece5f2d560ad54a2900763796892451c0951,0x35d7ab556aa1389043204e66b3315492441c8a91,0x35d7ab556a712086399accc5a2b95492441c8191,0x35d6aad4e2410c813b1ccd65a2b95492441c8491,0x35d7ab556aa13890431ccd6662d15caa491c8711,0x35d7ab556aa1389043204e66b2d15caa491c8991,0x1dee56c30574b056aad388d4521908823b9bcd6682d15cac49231147639190adc,0x36182ad55a710e8642208d6682b9587639190ad1,0x249228d4521908822d15cac49231147639190ad1,0x2691a8a43211046f361acd049231147639190ad1,0x34d60ae56aad1a8a432110449231147639190ad1,0x395b0c1582b5569c3b9bcd6682d15cac3e1a8c11,0x395b0c15d2c15aab4e1dcde6b34168ae561f0d51,0x395b0bf582ad168a42208de682d1588c45190ad1,0x395b0c15d2c15aab4e1dcde6b34168ae561f0c11,0x395aec0582b54c8c45219046f3599092451c8ad1,0x395b0c15d2c15aab4e1dcde6b34168ae561a8c11,0x395b0b055a2d1484411dcde682d1588c45190ad1,0x39560ad4e23d188a43208de6b3214092451c8ad1]
def bk77 : Array Nat := #[0x395aeb056a99388c45219046f3594092451c8ad1,0x3959ac0582b54c8c45219046f3599092451c8ad1,0x39580b056a71188a43208de6b3215c92451c8ad1,0x395aeb056a71188a43208de6b2b94092451c8ad1,0x395aec0582b54c9c462290c82379ac92451c8ad1,0x3b5cad8672f974b5582b5529c4ba411486411dce66f3599cb4572b15492451c8add,0x35d6aad542712086409ccd6662b95492441c8a91,0x35d6aad4e2410c76399accc5a2b95492441c8191,0x35d6aad5427120863b1ccd6662d15caa491c8711,0x35d6aad542712086409d8e66b2d15caa491c8991,0x395a2cf672f974b5582b95aab54a712e904521d0c84411ccde6b33968ae55249147639188ae1,0x1dae56c3397ebe5d2d560ad55aa538974822d148642208e66f3599cb4572a9248a39188ae0,0x1cce567b397ebe5d2d560ad55aa538974822d148642208e66f3599cb4572a9248a39188ae0,0xe972b619cbf5f2e96ab056aad529c4ba41148642208e66f3599cb4572a9248a39188adf,0x1dee56c3057cba582b5569c4ba351486421dce66f359a0ce5a2b958aa49231147639190ae0,0x1dee56c30574b5582b5569c482351486421dce66f359a0ce5a2b958aa49231147639190ae0,0x3b9cad7673017cba5aac15aa94e25d208c452190473379acce5a2b95492451c8add,0xef72b6182be5d2d560ab4e25d208d45210ee73379acd0672d15cac55249188a3b190adf,0xec72b5d9cbe5d2d560ad54a712e90452190473379acce5a2b95492451c8adb,0x35d6aad54271208943204e66b2b95492441c8a91,0x395aece5aa953897482290c8239980ae551a04d1,0x395aece5f2d560ad54a71207e3995caa3e1a8751,0x35da6ce5aac15aa949241045a2b95492451c8ad1,0x395aece5f2d560ad54a29006f2d15092451c0a51,0x395aece5f2e96ab056aa5146f3296892451c0151,0x395aece5f2e96ab056aa5148037968a849228451,0x395aece5f2e96ab056aa5146f32968a8492286d1,0x395aece5f2e96ab056aa514803796892451c0951,0x35d7ab556aa1208943204e66b3315492441c8a91,0x35d7ab556aa1389043204e66b3315caa491c8a91,0x35d7ab556a712089431ccd6662b95492441c8191,0x35d6aad4e2411286409ccd65a2b95492441c8491]
def bk78 : Array Nat := #[0x35d7ab556aa1389044a1902733595caa491c8991,0x3bdb0c15d2d55aab4e2411a86421dce66f359a0ce5a2b958aa49231147639190add,0x33d82ad55a350c84359a0ce49231147639190ad1,0x35d80b556a99208c431fce66b3395492451c8ad1,0x77b95b0c15d2c15aab4e2351486421dce66f359a0ce5a2b958aa49231147639190ade,0x1dee56c3057cba582b556a94e2351486421dce66f359a0ce5a2b958aa49231147639190ae0,0x3b5cad8672fd7cba5aac15aab54a712e90452190473379acce5a2b95492451c8add,0x3959cbf5f29d2e90452190473379acce411b88d1,0x3617ab556aa1389043204e66b3315492441c8a91,0xef6c30574b556aad389046a290c84411dce66f359a0ce5a2b958aa49231147639190adf,0xef72b6182ba582b5569c46a290c84411dce66f359a0ce5a2b958aa49231147639190adf,0x1dce56bb3980be5d2d560ad54a712e90452190473379acce5a2b95492451c8adc,0x3959cc05f29d2e90452190473379acce411b88d1,0x3959cc05f29d2e90452190473379acce511b88d1,0x395aece602f92e90452190473379acce411b80d1,0x395aece602f92e90452190473379acce512082d1,0x395aece602f94e97482290c82399bcd6672885d1,0x395aece602f94e97482290c82399bcd6671b8811,0x3959cc05f2d560ad54a29006f3295092451c0a51,0x395aece602f96ab056aa5146f3296892451c0151,0x395aece602f96ab056aa5148037968a849228451,0x395aece602f96ab056aa5146f32968a8492286d1,0x395aece602f96ab056aa514803796892451c0951,0x35d80b556aa1389043204e66b3315492441c8a91,0x35d80b556aa1389043204e66b3315caa491c8a91,0x35d80b556a712086399accc5a2b95492441c8191,0x35d80b556a712086409ccd65a2b95492441c8491,0x35d80b556aa13890431ccd6662d15caa491c8711,0x35d80b556aa1389043204e66b2d15caa491c8991,0x3bdb0c15d2b5569c46a290c84411dce66f359a0ce5a2b958aa49231147639190add,0x2711e8c452190473379acce5a2b95492451c8ad1,0x3611a8a43211047337980ac55249188a341784d1]
def bk79 : Array Nat := #[0x36182be56aad5273379acd0672b1547c35180751,0x3611a8a43211047337980b4562a9248c451782d1,0x3057cad55aa5148642208d6632490c76391889d1,0x3057cad55aa51a8a43211046b319247639188811,0x36182be56aad5273379acd0672d158aa3e1806d1,0x3057cad55aa51a8a43211046b2490c7639188951,0x3611a8a43211047337968ac55249188a34178491,0x36182be56aad5273379acd0672d158aa35180711,0x2f95aa947a311486411ccde6b3395492451c8ad1,0x3017cb456aa51486411ccde6b3395492451c8ad1,0xef6c3057cba56aad529c46a290c84411dce66f359a0ce5a2b958aa49231147639190adf,0x3bdcad86730574b5582b556a84e25d208d4521908823b9ccde5a2b958aa49231147638188921,0x395a2cf672f960ae56aad529c4ba411487432110477399bcd66833968ae562a9188a3b1c8ca1,0x1dee56c3057cba5aac15aab542712e8d452190877399bcd66833968ae49231147639188920,0xe570b3d9cbf5f2c156a94e25d208a432110477399bcd66833968ae562a9188a39190adf,0x3bdcad860af974b5582b556a84e25d208d452190877399bcd6672d15cac55249188a3b1c8c61,0x395bad7672f974b5582b5529c4ba41188a43208ee73379acd0672d15cac55249188a39190ae1,0xe56732180be5bad560ad54a712e90452190477399bcd66833968ae562a9188a39190adf,0xe56cb5d9cbe5bad560ad54a712e90452190477399bcd66833968ae562a9188a39190adf,0x3bdcad8673057cba5aac15aab542712e9046a290c84411dce66f3599cb456249188a3b1c0ca1,0x77b95b0c15d2d560ad55aa1389046a290877399bcd05a2b958aa4923114763819091e,0x3bdcad86730574b5582b556a84e25d208d4521908823b9ccde682d15cac55249188a3b1c0ca1,0xe5672f960a94f2712e90452190477399bcd66833968ae562a9188a39190adb,0x3959cbe4ba411486411ccde6b3419ca2411b88d1,0x3957c9c4ba40fc73379acd0672b1547c35180751,0x3957c9c4ba40fc73379acd0672b958aa3e180751,0x3957c9c4ba40fc73379acd0672b958aa3e1a8751,0x3957c9c4ba40e66f359a0ce5a2b958aa3e1a8091,0x3957c9c4ba40fc73379acd0672d15cac551f0291,0x3957c9c4ba40fc73379acd0672d15cac551805d1,0x3957c9c4ba40e66f359a0ce5a2b958aa35180711,0x3957cb04e25d147b399bcd668339388c451681d1]
def bk80 : Array Nat := #[0x271208943204e66b34198ae562a9188839190a91,0x27120863b9ccd66833168ae562a9188839190a91,0x2712086409dce66b34198b4572b1548c39190a91,0x2712089431ccd66833168ae562a9188839190191,0x271208943204e66b34168ae562a9188839190491,0x2793890431dce66b34198b4572b1548c39190711,0x271208943204e66b34198b4572b1548c39190891,0x3957cb05125d147b399bcd668339388c451681d1,0x3957cb0512712e8a3d9ccde6b3419c9c462281d1,0x395609c4ba290c7b399bcd6602b9388c451c8051,0x3957cb04e25d147b399bcd668339689c46228051,0x34d9cb054a49208a43208ae562a9188a39190ad1,0x3959cbe582a53897399bcd6683395c9c3e1a8091,0x3957cb0512712e86399bcd6683395c9c3e1c8091,0x3957cb0512712e8a399bcd668339689c46228091,0x3959cbe582a53897481f8e66f3015cac551f0291,0x3959cbe53a5d208a43208e66f359a0ce411b88d1,0x3959cbe53a5d208a43208e66f359a0ce512088d1,0x3957c9c4ba290c7b399bcd6683391882391680d1,0x3957c9745218f673379acd0672b11882371900d1,0x3957cb04e25d147b399bcd668339688c451680d1,0x3959cbe4e25d208a43208e66f359a0ce411b80d1,0x3959c97482290c82399bcd0602b1448c411902d1,0x3959cbe4e25d208a43208e66f359a0ce512082d1,0x3959cbe582a52e903f1ccde6b3419cac511805d1,0x3959cbe53a5d207e399bcd66833958a2461905d1,0x3959cbe53a712e90452190473379acd0672885d1,0x33960a949241148641168ae562a9188a39190ad1,0x33960a9482290c822d968ae562a9188a39190ad1,0x34d9cb054a41148641168ae562a9188a39190ad1,0x3959cbe582a53897482290c823598ca6431c89d1,0x3959cbe582a53897482290c823598cae431c89d1]
def bk81 : Array Nat := #[0x3959cbe582a53897482290c823598cae531c89d1,0x3959cbe582a53897482290c823598cae431c8111,0x3959cbe582a53897482290c823595ca6431c83d1,0x3959cbe582a53897482290c823598cae531c8651,0x3959cbe53a712e90452190473379acd0671b8811,0x3959cbe582a53c9c4ba411486411acc6571c8811,0x3959cbe582a51e8a401bcd0652b1508c45190a51,0x3959cbe582a51477379a0ca5a2b1508c45190a51,0x3959cbe582a514803b9bcd0652d1588c45190a51,0x3957cb0512712e8a399bcd668339688c45168151,0x3959cbe582a53c8a3b9bcd0652d1588c45190151,0x3959cbe582a51e8a401bcd05a2b1508c45190451,0x3959cbe582a51e8a379a0ca5a2b1508c451906d1,0x3959cbe582a51e8a401bcd0652d1588c45190851,0x72b6daece5f2e16ab054a712e90452190477399bcd66833968ae562a9188a39190ade,0xef72b619cc15f2e96ab056aad529c4ba350c843b9ccde6b3419cae5624918763919091f,0xef6c30574b556aad509c482350c843b9ccd6682d15cac5524918763919091b,0x36182b556aad509043a10d6682b1547639190911,0x36182ba5aab556a84e240ee732d15cac551a8c11,0x33d82ad55aa1308d43210d668249187639190911,0x3055aab542611a86421c0d668249187639190911,0x30564ad55aa11a86421c0d668249187639190911,0x33d82b256aad508d43210d668249187639190911,0x33d82ad55aa11a86421c0d668249187639190911,0x3616aae56aad509248210b4572b1549239190911,0x3056cb556aad5075359a0ae55251247639190911,0x3617eb555aa1369045a10e6682b1548c42190911,0x3616aab5426d208b421ccd05a2b1548c42190911,0x3617eb555aa120843b9ccd05a2b1548c42190911,0x3616aab5424116843b9ccd05a2b1548c42190911,0x3617eb555aa13690421dce6682d158aa46190911,0x3617eb555aa1208b421ccd05a2b1548c42190911]
def bk82 : Array Nat := #[0x2451a86421dce66c34168ac55249187639190911,0x271229046a190873361acae55249187639190911,0x35d80b556aa1389046218fe733595caa491c8911,0x2d55aa84e24118863f9d8e66b2d15caa491c8911,0x30174b556aa13890431d8e66b2d15caa491c8911,0x35d6aad54271208c431fce66b2d15caa491c8911,0x35d80b556aa13890431fce66b2d15caa491c8911,0x35d80b556aa13890431d8e66b2d15caa491c8911,0x1dee56c3057cba5aab556a84e25d208d43210ee73379acd0672d15cac55249187639190920,0x3a1cad7672f96ab054a712e90452190477399bcd66833968ae562a9188a39190add,0x3957cb3582892e8a3d9ccde6b3419c8c451681d1,0xef72b619cc15f2e96ab056aad529c46a290c843b9bcd6682d15cac4923114763919091f,0x3bdcad86730574b5582b556a84e25d208d4521908823b9bcd6682d15cac49231147639190921,0x3bdcad860af974b5582b556a84e25d1a8a43210ee73379acd0672d15cac49231147639190921,0x1dee56c30574b5582b556a84e2411a8a43210ee73379acd05a2b958aa49231147639190920,0x1d6e5673057cb7582b5529c4ba41148743208ee73379acd0672d15cac55231147639190ae0,0x753959cc05f2dd60ad54a712e90452190477399bcd66833968ae562a9188a39190ade,0x1dee56c33982ba5aac15aab54a712e9046a290c84411dcde682d158aa49231147638190ae0,0x395bcd8672f974b5582a5389748235148642208ee73379acd0672d15cac55249188a39190ae1,0x1d6e56c3397cb75aac1529c4ba411487432110477399bcd66833968ae562a9188a39190ae0,0x1cada6c3397cb75aac1529c4ba411487432110477399bcd66833968ae562a9188a39190ae0,0x74b95b0ce5f2d560a94e25d208a432110477399bcd66833968ae562a9188a39190ade,0x3957cb05125d14833d9ccde6b3419c8c451681d1,0x1dee56c3057cba5aac15aab54a712e8d452190877399bcd66833968ae49231147639190ae0,0x1dce56bb397cba5aac1529c4ba41188a43208ee73379acd0672d15cac55249188a39190ae0,0x1cadd6bb397cba5aac1529c4ba41188a43208ee73379acd0672d15cac55249188a39190ae0,0x75395aece5f2dd6ab054a712e90452190477399bcd66833968ae562a9188a39190ade,0xef72b6182be5d2d560ad55aa5389746a290877399bcd66833968ac49231147639190adf,0x76395aece5f2e16ab054a712e90452190477399bcd66833968ae562a9188a39190ade,0x1dee56c33982be5d2d560ad55aa5388d43210ee6b3419cae56249187639190adc,0x30d82be582b556a9359a0ce4a249187639190ad1,0x3057cb65aab556a93a9acd0672b9587639190ad1]
def bk83 : Array Nat := #[0x3819cc15f2b556a943a19086b3419c7639190ad1,0x395b0ce5aac14a9c46a1908572b1248c34178311,0x395b0ce5faf96ab055aa516843419c8c42190ad1,0x395b0ce5aac14a9c46a1908772b95892461a0311,0x271228d43210d86b3419cac52249187639190ad1,0x395b0ce5aac14a9c46a1908772b9589246178311,0x395aece602f96ab056aa518863f9acce491c8ad1,0x2711a86421b0d6683395cac52249187639190ad1,0x2711a86421dcd86b3419cae56249187639190ad1,0x271228d43210d86b3419cae56249187639190ad1,0x395b0ce5aac1388d43210ee572b1248c34178311,0x395b0ce5faf96ab055aa50868339588c42190ad1,0x395b0ce5faf96ab055aa508773419cac46190ad1,0x395b0ce5faf96ab055aa516843419cac46190ad1,0x3959cc05f2e96ab056aa538863599cae491c8ad1,0x3959cc05f2d560ad54a7118863f9acce491c8ad1,0x395aece602f96ab056aa538863f9acce491c8ad1,0x3959cc05f2d560ad54a7118863599cae491c8ad1,0x395aece602f96ab056aa538863599cae491c8ad1,0xef72b619cc15f2e96ab056aad529c4ba350c843b9ccde6b3419cae56249187639190adf,0x3bdb0c15f2e96aad55aa5389046a190877399acd0672d15cac55249187639190add,0x3617eb555aa5208b421ccd0672b1548c42190ad1,0x35d80b556aa5389046218fe733599caa491c8ad1,0xef72b6182be5d2d560ad55aa5388d452190877379acd0672d15cac49231147639190adf,0x1dee56c33982be5d2d560ad55aa5388d452190877379acd0672d15cac49231147639190ae0,0xe571b3d9cc15f2c15aab54a712e90452190477399bcd66833968ae562a9188a39190adf,0x1dee56c30574b5582b556a84e2411a8a432110477399bcd65a2b958aa49231147639190ae0,0x1dce56bb3980be5d2d560ad54a712e90452190477399bcd66833968ae562a9188a39190ae0,0xe56eb5d9cbe5d2d560ad54a712e90452190477399bcd66833968ae562a9188a39190adf,0x1d4e56bb3980be5bad560ad54a712e90452190477399bcd66833968ae562a9188a39190ae0,0x3bdcad860af974b5582b556a84e25d1a8a432110477399bcd66833968ac49231147639190ae1,0x1dee56c30574b5582b556a84e2411a8a432110477399bcd05a2b958aa49231147639190ae0]
def bk84 : Array Nat := #[0x1dee56c3057cba5aab556a84e25d1a8a432110477399bcd6683395cac49231147639190ae0,0x77b6182ba5aab556a84e2411a8a432110477399acd05a2b958aa49231147639190ade,0x77b95b0c15d2d560ad55aa1388d4521908823b9bcd6682d15cac49231147639190ade,0x3bdcad86730574b5582b556a84e25d208d4521908823b9bcd6682d15cac49231147639190ae1,0x3bdcad860ae96ab056aad509c48235148642208ee73379acd05a2b958aa49231147639190ae1,0x1dee56c33982ba5aac15aab54a71208d4521908823b9ccde5a2b958aa49231147639190ae0,0x773959cc05f2e960ad54a712e90452190477399bcd66833968ae562a9188a39190ade,0x1dee56c33982ba5aac15aab54a712e9046a290c84411dcde682d158aa49231147639190ae0,0x77395aece5f2e96ab054a712e90452190477399bcd66833968ae562a9188a39190ade,0xef72b6182be5d2d55aab54a712e8d4521908823b9ccde6b3419cac49231147639190adf,0x1dee56c3057cba5aab556a94e25d1a8a432110477399bcd6683395cac49231147639190ae0,0x1dee56c3057cba5aac15aab54a711a8a432110477379acd0672d15cac49231147639190ae0,0x3bdb0ce60af974b556aad529046a290c84411dcd66833958aa49231147639190add,0x395bcd8672f960ae55aa5389748235148642208ee73379acd0672d15cac55231147639190ae1,0x3adcad8673057cb055aa53897482290e8642208ee73379acd0672d15cac55231147639190ae1,0x395b4d8672f960ae55aa53897482290e8642208ee73379acd0672d15cac55231147639190ae1,0x395c6cf673057cb055aa53897482290e8642208ee73379acd0672d15cac55231147639190ae1,0x3bdcad86730574b5582b556a94e25d208d4521908823b9ccde5a2b958aa49231147639188ae1,0xe972b619cbf5f2c156a94e25d208a432110477399bcd66833968ae562a9188a39190adf,0x3bdcad860af974b5582b556a94e25d1a8a43210ee73379acd0672d15caa49231147639188ae1,0x77395aece602f960a94e25d208c452190477399bcd66833968ae562a9188a39190ade,0x3a9cad7673017cb054a712e90452190477399bcd66833968ae562a9188a39190add,0x77b95b0c15d2d560ad55aa5389046a290877399bcd05a2b958aa49231147639190ade,0x1d8e56bb397cb054a712e90452190477399bcd66833968ae562a9188a39190adc,0x35d389044a190273359a0cc562a9188839190a91,0x381aece5f2a52e90411ccd66833958aa39190ad1,0x395aece5f2c15297482290c823598ca6431c89d1,0x395aece5f2c1529c4ba411486411acc6531c89d1,0x395aece5f2c1529c4ba411486411aca6431c83d1,0x395aece5f2c1529c4ba411486411acc6531c8651,0x395aece5f2c1529c4ba411486411acc6571c8811,0x395aece5f2c1528a401bcd0652b1508c45190a51]
def bk85 : Array Nat := #[0x395aece5f2c1528a401bcd05a2b1508c45190451,0x395aece5f2c1528a379a0ca5a2b1508c451906d1,0x395aece5f2c1528a401bcd0652d1588c45190851,0x35d7aa6482250c81399acd0662a9188839190a91,0x35d7aa64e2410c81399acd0662b1548c39190a91,0x35d389044a190273359a0ae562a9188839190491,0x35d7aa64e2410c73359a0cc572b1548c39190711,0x35d7aa6482250c81399acd0662b1548c39190891,0x77b95b0ce60af974b5582b556a94e2350c843b9acd05a2b958aa49231147639190ade,0x1dee56c33982be5d2d560ad55aa5388d452190877379acd05a2b958aa49231147639190ae0,0x75b959cc15f2c1529c4ba41148743208ee73379acd0672d15cac55231147639190ade,0x77b95b0ce60ae96ab056aad529046a2908823b9bcd05a2b958aa49231147639190ade,0x3619cb5572b556a94821d08822b1547639190ad1,0x245208d45211045a2b958aa49231147639190ad1,0xef6c33982ba5aac15aab54a71208d432110477399acd05a2b958aa49231147639190adf,0x77b95b0ce5f2c1529c4ba411a8a432110477399bcd66833968ae562a9188a39190ade,0x72b79b0ce5f2c1529c4ba411a8a432110477399bcd66833968ae562a9188a39190ade,0x75b95b0ce5f2c1529c4ba411487432110477399bcd66833968ae562a9188a39190ade,0x1dee56c3057cba5aac15aab54a712e8d45210ee73379acd0672d15caa49231147639190ae0,0xef72b6182be5d2d560ad55aa5388d452190877379acd0672d15caa49231147639190adf,0x3b9cad7672f960a94e25d208c452190477399bcd66833968ae562a9188a39190add,0x77b95b0c15f2e96ab056aad528d45210ee6f359a0ce5a2b958aa49231147639190ade,0x3057cb65aab556a9359a0ce572b1547639190ad1,0x30d80be5aac15aa9379acce5a2b95492451c8ad1,0x1bcd86b3419cb4572b1549449231147639190ad1,0x3017cba5aac15aa93a9acce5a2b95492451c8ad1,0xef72b619cc15f2e96ab056aad529c46a190877359a0ce5a2b958aa49231147639190adf,0x1dee56c3057cba5aac15aab54a711a8a43210ee6f359a0ce5a2b958aa49231147639190ae0,0x77b95b0ce60af960ab54a712e90452190477399bcd66833968ae562a9188a39190ade,0x75b95b0ce60af960ab54a712e90452190477399bcd66833968ae562a9188a39190ade,0xef72b6182ba5aac15aab54a71208d4521908823b9ccde5a2b958aa49231147639190adf,0x74b95b0ce5faf960ab54a712e90452190477399bcd66833968ae562a9188a39190ade]
def bk86 : Array Nat := #[0x1dee56c30574b5582b556a94e2411a8a432110477399bcd65a2b958aa49231147639190ae0,0x3b9cad7673017cb054a712e90452190477399bcd66833968ae562a9188a39190add,0x1dee56c30574b5582b556a94e2411a8a432110477399bcd05a2b958aa49231147639190ae0,0x30174b5582b5529c43208d65a2b95492451c8ad1,0x1dee56c33982be5d2d560ad55aa5388d4521908823b9acd05a2b958aa49231147639190ae0,0xef6c30574b5582b556a94e2411a8a432110477399acd05a2b958aa49231147639190adf,0x1dee5673057cb054a712e90452190477399bcd66833968ae562a9188a39190adc,0x305389043204e66b34198ae562a9188839190a91,0x3053890431ccd66833168ae562a9188839190a91,0x34d9cb0572a524904521904562a9188a39190ad1,0x33960a94924114864115cac55231147439190ad1,0x34d9cb0552a5208a43208ae562a9188a39190ad1,0x34d9cb0562a524904521904562a9188a39190ad1,0x3959cc15f2c15297482290c823598ca6431c89d1,0x3959cc15f2c1529c4ba411486411acc6431c89d1,0x3959cc15f2c1529c4ba411486411acc6531c89d1,0x3959cc15f2c1529c4ba411486411acc6431c8111,0x3959cc15f2c1529c4ba411486411acc6531c8651,0x3959cc15f2c1529c4ba411486411acc6571c8811,0x3959cc15f2c1528a401bcd0652b1508c45190a51,0x3959cc15f2c1528a379a0ca5a2b1508c45190a51,0x3959cc15f2c1528a401bcd0652d1588c45190a51,0x3959cc15f2c1528a3b9bcd0652d1588c45190151,0x3959cc15f2c1528a379a0ca5a2b1508c451906d1,0x3959cc15f2c1528a401bcd0652d1588c45190851,0x305389043204e66b34198b4572b1548c39190a91,0x3053890431ccd66833168ae562a9188839190191,0x3053890431dce66b34198b4572b1548c39190711,0x305389043204e66b34198b4572b1548c39190891,0x77b95b0ce60ae96ab056aad529046a290c84411dcde5a2b958aa49231147639190ade,0x3bdb0ce60ae96ab056aad529046a290c84411dcd05a2b958aa49231147639190add,0x30560ad5123514863d95c9c492311476391681d1]
def bk87 : Array Nat := #[0x3619cc15aac15aab54a40fc572b1547c35180751,0xef72b619cc15d2d560ad55aa5208d4521908823b9bcd05a2b958aa49231147639190adf,0x1ded86730574b5582b556a94e2411a8a432110477399acd05a2b958aa49231147639190ae0,0x1dee56c3397cb054a712e90452190477399bcd66833968ae562a9188a39190adc,0x361389043204e66b34198ae562a9188839190a91,0x381b0ce5f2a52e90411ccd66833958aa39190ad1,0x395b0ce5f2c15297482290c823598ca6431c89d1,0x395b0ce5f2c1529c4ba411486411acc6531c89d1,0x395b0ce5f2c1529c4ba411486411aca6431c83d1,0x395b0ce5f2c1529c4ba411486411acc6531c8651,0x395b0ce5f2c1529c4ba411486411acc6571c8811,0x395b0ce5f2c1528a401bcd0652b1508c45190a51,0x395b0ce5f2c1528a401bcd05a2b1508c45190451,0x395b0ce5f2c1528a379a0ca5a2b1508c451906d1,0x395b0ce5f2c1528a401bcd0652d1588c45190851,0x361389043204e66b34198b4572b1548c39190a91,0x361389043204e66b34168ae562a9188839190491,0x3613890431dce66b34198b4572b1548c39190711,0x361389043204e66b34198b4572b1548c39190891,0xef72b6182be5d2d560ad55aa51a8a432110477379acd0672d15caa49231147639190adf,0x1dee56c3057cba5aac15aab54a711a8a432110477379acd0672d15caa49231147639190ae0,0x77b6182be5d2d560ad55aa51a8a432110477359a0ce5a2b958aa49231147639190ade,0x1dee56c3057cba5aac15aab54a35148642208ee6f359a0ce5a2b958aa49231147639190ae0,0xef6c33982be5d2d560ad55aa5208d452190882359a0ce5a2b958aa49231147639190adf,0x1ded8673057cba5aac15aab54a411a8a432110477359a0ce5a2b958aa49231147639190ae0,0x72b397cba5aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190ade,0x3959cc45faf974b5582b556a94e25d208a43208ee73379acd0672d15cac55249188a39190ae1,0x1cace5f2e96ab1582b556a94e25d208a43208ee73379acd0672d15cac55249188a39190ae0,0x3959cc75faf974b65aac15aab54a712e90452190477399bcd66833968ae562a9248c451c8ca1,0xef72b619cc15f2e96ab056aad529c4ba411a8a432110477379acb457249188a3b1c8c5f,0x1cace5faf974b5582b556a94e25d208a43208ee73379acd0672d15cac55249188a39190ae0,0x3959ece5f2e96ab056aad529c4ba41148642208ee73379acd0672d15cac55249188a39190ae1]
def bk88 : Array Nat := #[0xe5683397cba5aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190adf,0xe5673197cba5aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190adf,0xe56bb397cba5aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190adf,0x3b5cace5faf974b5582b5529c4ba41168a43208ee73379acd0672d15cac55249188a39190ae1,0x399cace5faf974b5582b5529c4ba41168a43208ee73379acd0672d15cac55249188a39190ae1,0x1cace622fd7cba5aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190ae0,0x3a5cace5faf974b5582b5529c4ba41148641a08ee73379acd0672d15cac55249188a39190ae1,0xec72b397cba5aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190adf,0x1dee56c33982ba5aab556a94e25d208d4521908823b9ccd6682d15cac55249187639190ae0,0x3adcad8672f974b5582b5529c4ba411487432110477399bcd66833968ae562a9248c451c8ca1,0x1cace652f974b65aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190ae0,0x3a5cad8672f974b5582b5529c4ba41148642208ee73379acd0672d15cac55249188a39190ae1,0x1d4e56bb397cba5aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190ae0,0xe5673257cba5aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190adf,0x1d0e56bb397cba5aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190ae0,0x1d6e5672f974b5582b5529c4ba41148743208ee73379acd0672d15cac55249188a39190ae0,0xe5673297cba5aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190adf,0x1dee56c33982be5d2d55aab54a712e9046a290c84411dcd6683395cac55249187639190ae0,0x395c6cf673057cba5aac15aab54a712e90452190477399bcd66833968ae562a9248c451c8ca1,0x3b5cad8672fd7cba5aac15aab54a712e90452190477399bcd66833968ae562a9248c451c8ca1,0x3959cca5faf974b65aac15aab54a712e90452190477399bcd66833968ae562a9248c451c8ca1,0x399cacf672fd7cba5aac15aab54a712e90452190477399bcd66833968ae562a9248c451c8ca1,0x3a5cad8672fd7cba5aac15aab54a712e90452190477399bcd66833968ae562a9248c451c8ca1,0x1dee56c33982be5d2d560ad55aa5389748235148642208ee6f35968ae49231147639190ae0,0x1cad8672f974b5582b556a94e25d208a43208ee73379acd0672d15cac55249188a39190ae0,0x395c2cf672fd7cba5aac15aab54a712e90452190477399bcd66833968ae562a9248c451c8ca1,0x3b9cad7673017cba5aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190ae1,0x3a9cad7673017cba5aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190ae1,0x1cae2673017cba5aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190ae0,0x1d8e56bb397cba5aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190ae0,0x1dee56c33982be5d2d560ad55aa5389748235148642208ee6b3415cac49231147639190ae0,0x1dee56c33982ba5aab5569c4ba411a8a432110477399acd05a2b958aa49231147639190ae0]
def bk89 : Array Nat := #[0x1dee56c30574b5582b5569c48235148642208ee73379acd05a2b958aa49231147639190ae0,0x1cae3673057cba5aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190ae0,0x1dae5672fd7cba5aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190ae0,0x1cce5672fd7cba5aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190ae0,0x1d2e5672fd7cba5aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190ae0,0xef6c33982ba5aab556a94e2411a8a432110477399acd05a2b958aa49231147639190adf,0x1dee56c3397cba5aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190ae0,0x1d6e56c3397cba5aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190ae0,0x1dae56c3397cba5aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190ae0,0xef72b619cc15f2e96ab056aad529c4ba411a8a43211046b3419cae49231147639190adf,0x1cce567b397cba5aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190ae0,0x1d2e56c3397cba5aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190ae0,0x1dee56c3057cba582b556a94e25d1a8a432110477399bcd66833968ae49231147639190ae0,0x1dce56bb397cba5aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190ae0,0xef72b397cba5aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190adf,0xed72b397cba5aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190adf,0xee72b397cba5aac15aa94e25d208a43208ee73379acd0672d15cac55249188a39190adf]
def bkTab : Array (Array Nat) := #[bk0,bk1,bk2,bk3,bk4,bk5,bk6,bk7,bk8,bk9,bk10,bk11,bk12,bk13,bk14,bk15,bk16,bk17,bk18,bk19,bk20,bk21,bk22,bk23,bk24,bk25,bk26,bk27,bk28,bk29,bk30,bk31,bk32,bk33,bk34,bk35,bk36,bk37,bk38,bk39,bk40,bk41,bk42,bk43,bk44,bk45,bk46,bk47,bk48,bk49,bk50,bk51,bk52,bk53,bk54,bk55,bk56,bk57,bk58,bk59,bk60,bk61,bk62,bk63,bk64,bk65,bk66,bk67,bk68,bk69,bk70,bk71,bk72,bk73,bk74,bk75,bk76,bk77,bk78,bk79,bk80,bk81,bk82,bk83,bk84,bk85,bk86,bk87,bk88,bk89]
def bk (i : Nat) : Nat := ((bkTab[i/32]?).getD #[])[i % 32]?.getD 0
def pr0 : Array Nat := #[0x4000,0x4001,0x4002,0x500800c0100100001c003,0x4007,0x4008,0x4009,0x400a,0xa0080240400700c01c00b,0x400f,0xa0080240400700c01c010,0x4012,0x4013,0x500800c0100100001c014,0x140580a0080240400700c024018,0x401d,0x401e,0x280580500800c0100100002401f,0x4024,0x4025,0x4026,0x4027,0x4028,0x402a,0x402b,0x402d,0x402f,0x4031,0x4032,0x4033,0x4037,0x4038]
def pr1 : Array Nat := #[0x4039,0x403a,0x403b,0x403c,0x403e,0x403f,0xa81282904a0a01282704a0981282104a01c1282004a0841202004808c0f82203e0840f82003e0500f01203a0500e0140360500d0130340480d0010320500c01202e0500b01402a050088130220480880d02003c0000e0000340000d018114042,0x841681705801c0c02b00c02404f,0x4054,0x4055,0x4056,0x4058,0x4059,0x405c,0x405d,0x405e,0xc40d03004401c0c02f05c024060,0x4065,0x4066,0x4067,0x4068,0x4069,0x3103401c0c02b00c01c06a,0x406d,0x406e,0x406f,0x4070,0x4073,0x4074,0x4076,0x4077,0x4078]
def pr2 : Array Nat := #[0x407d,0x2105a0c40d00703001c07e,0x4082,0x4083,0x4085,0x4086,0x4088,0x310340c01100703001c089,0x2105a0c40d00703001c08d,0x408f,0x4090,0x4091,0x4092,0x4093,0x4094,0x300340d01983200401c096,0x409a,0x409b,0x1101282704a10c1284204a1041282104a0c41282004a104120210480c4120200480501683103e0800f83b0160c4200200800040c81403000c0c012030050010030040500b01402200c088120220ec1f83b07c0d41f03a07c0ec1e83507a0ec1e0350780ec1c8350720e81c80d0180d00183801a0dc1a83606a16409d,0x40b4,0x40b5,0x40b6,0xc0100308a0d41e8350200d00183606a0340ba,0x40c0,0x300340c80100108a01c0c1,0x40ca,0x40cb,0x40cc,0x40cd,0x40cf,0x40d0,0x40d4]
def pr3 : Array Nat := #[0x1101282704a10c1284204a1041282104a0c41282004a0c4120200480501683103e0800f83b0160c4200200800040c81403000c0c012030050010030040500b01402200c088120220ec1f03507c0e81f03b07a0d41e83b0780d41e03b0720d41c83a0720d00183606a1340d5,0x40e4,0x40e7,0x40e8,0x40ed,0x40ee,0x1200204708c0140ef,0x40f2,0xa82b8590ae0f02b8580ae0842b8010ae1342b82105a1341680a016158020480080380204a00805c1603c05808416001058134160540aa14c2a8500aa0c42a8300aa13c2a8500381400d8500340c40d03003413c0d0540660d019853066140198310660c01984f066140290500a21402703109c0c02704f09c01c0c0320040042284d08a12c1f02f07c0ac0304a00c0bc0304c08c11c2304b08c0bc2302f05c0381e84a07a0340804a0921f40f3,0x3105,0xf02f84d0be1682f0170bc0f02f04d0bc1702b85b0ae0f02b84d0ae1741601d0581701605b058168160170580f01604d058093107,0x3109,0x310a,0xf02f84d0be1682f0170bc0f02f04d0bc1702b85b0ae0f02b84d0ae1741601d0581701605b058168160170580f01604d05809310d,0x4118,0x4119,0x841200a0480840f80a03e02411a,0x411f,0x4120,0x4121,0x300340c80100108a01c122,0x143682105a0141680a01605c16021058014160610580143606b0aa1502a86a0aa1a42a8500aa0c42a8300aa13c2a8500340c40d03003413c0d0500660c41983006613c1983101e140290310a4140340310d01402703109c0c02704f09c01c0c0630ce18c330630040c80104a0040042282f0ca12c1f02f07c11c2304b08c1842302f08c0bc170630c818c1e80e07a1281e80d02018c1384a04e128248630c4038310320c4128310610c01f4126,0x1c43984a0e61c81386304e1c41384a04e1c42484a0921c8310630c41c43104a0c41103186e0c61c0250440941bc2506e09409313f,0x1c43984a0e61c81386304e1c41384a04e1c42484a0921c8310630c41c43104a0c41103186e0c61c0250440941bc2506e094093146,0x4151,0x4152,0xc00d0310660c80100108a024153,0x4156,0x4157,0x4158,0x128248610c0014159,0x415b]
def pr4 : Array Nat := #[0x415c,0x841280a04a0c41282004a0841200a0480801202103e0280f82003e0500f0140340ec3b83b066038040320100040c80d0320503b0140300480c01402c0500a81402200c088130220480883b07e0ec1f03a07c1280306108c0ec1e03b0ea0ec1c8350721d01c83a07213415d,0x84168310340c019807030024176,0x4179,0x417a,0x417b,0x417c,0x417d,0x417e,0x417f,0x4180,0x4181,0x3106612c1f04708c01c183,0x4187,0x4188,0x4189,0x310340d01980703001c18b,0x418f,0x4190,0x1101282704a10c1284204a1e01284b04a0c41282004a0c4120200480501680305a04c1683103e0800f83b0160d4058740160c4200200800340c814030050010030040500a80302a0500880302204c0883b07c0ec1e83507a0ec3a83b0720d41c8740720d00183606a134191,0x41a2,0x41a5,0x41a6,0x41a9,0x1101282704a10c1284204a0c41282004a0c4120200480503e01405a00c1681305a0ec3d83b0160d405874016128020610580c420020080038040320100040c80d0320500c0030300480c0140f40500b01402a0500880302204c088120220ec1f03507c0e81f04a00c1842303b0780ec3c83b0ea0ec1c8350721d01c83a0720040000e000034000320000d00183606a1a41aa,0xa0160c41984b07c01c1c8,0x41cc,0x14168050160143602f0300bc1f02f05c0341cd,0x41d3,0x41d4,0x3103401c0c02f05c01c1d5,0x2105a0c40d00703001c1d7]
def pr5 : Array Nat := #[0x41d8,0x41d9,0x41da,0x41dc,0x41dd,0x41de,0xa0160c41984b07c01c1df,0x41e3,0x2105a0c40d00703001c1e4,0x41e5,0x41e6,0x41e7,0x41e8,0x41e9,0x41eb,0x143602f05c0141ec,0x41ef,0x41f0,0x41f1,0x41f2,0x41f5,0x41f7,0x1081280a04a01c1283104a080128200480501682003e0ec058630080500d0200800ec198630100500c0140f40500b01402a0500880302204c088120220ec1f06300c0ec1e03b0f20ec3a83b0720d41c8740720e81c8630fc18c3e8630c4038310320c41283106e0c61341f8,0x420e,0x420f,0x2000587f030014210,0x4213,0x4214,0x4215,0x4216,0x4217,0x4218]
def pr6 : Array Nat := #[0x4219,0x421a,0x421b,0x2f0300e84086108a01c21c,0x4220,0x4221,0x4222,0x4223,0x4224,0x4225,0x4227,0x4228,0x4229,0x422a,0x422b,0x422d,0x422f,0x4230,0x4231,0x4232,0x4233,0x4234,0x4235,0x4236,0x4237,0x4238,0x4239,0x423a,0x423b,0x423c,0x423d,0x423e]
def pr7 : Array Nat := #[0x423f,0x4240,0x4241,0x4242,0x4243,0x4244,0x4245,0x4246,0x4247,0xa0080240400700c01c248,0x424b,0x424c,0x424d,0x424e,0x424f,0x4250,0x4251,0xa0080240400700c01c252,0x4256,0x4257,0x4258,0x4259,0x425a,0x425b,0x425c,0x425d,0x143603004401425e,0xc01102f05c014261,0x4264,0x4265,0x4266,0x4267]
def pr8 : Array Nat := #[0x4268,0x4269,0x426a,0x426b,0x426c,0x426d,0x426e,0x426f,0x4275,0x3104804c1687401601c277,0x427b,0x427c,0x427d,0x427f,0x4280,0x4281,0x4282,0xc41201305a1d005809080024284,0x4288,0x4289,0x428a,0x428b,0x428e,0x428f,0x4291,0x4292,0x4293,0x4294,0x4295,0x12c2000d032014297,0x429a,0x429c]
def pr9 : Array Nat := #[0x429d,0x429f,0x42a2,0x42a5,0x42a6,0x42a7,0x42a8,0x501604c4086102001c2a9,0x42ad,0xc41201305a0142ae,0x42b1,0x2104804c0d00103201c2b2,0x42b6,0x42b7,0x42bb,0x1203401c2003201001c2bc,0x42c0,0x42c1,0x42c2,0x42c3,0x42c4,0x121020bc1f04a07a01c2c5,0x42c9,0x42ca,0x42cc,0x42cd,0x42cf,0x42d0,0x42d1,0x42d2,0x42d3,0x42d4]
def pr10 : Array Nat := #[0x42d5,0x42d6,0x42d7,0x42d9,0x42da,0x501604c4086102001c2dc,0x42e0,0x42e1,0x42e2,0x42e3,0x42e4,0x281200e0100142e8,0x42eb,0x42ec,0x42ee,0x42ef,0xc40d0070300142f0,0x42f4,0x42f6,0x240c84b08c0142f7,0x42fa,0x42fc,0x42fd,0x42fe,0x42ff,0x4300,0x4301,0x4302,0x4303,0x4305,0x501604c4086102001c306,0xc41207401601430a]
def pr11 : Array Nat := #[0x430c,0x430d,0x430e,0x430f,0x4310,0x4311,0x4312,0x4313,0x4314,0x4315,0x4316,0x4317,0x4318,0x4319,0x431a,0x431b,0x431c,0x431d,0x4320,0x4321,0x4322,0x4323,0x4324,0x4325,0x4327,0x4329,0x432b,0x432c,0x432d,0x432e,0x432f,0x4330]
def pr12 : Array Nat := #[0x4332,0x4333,0x4334,0x4336,0x4337,0x4338,0x3104804c1687401601c33e,0x4342,0x4344,0x4346,0x4347,0x4348,0x4349,0x434a,0x434f,0x4350,0x4351,0x4353,0x4354,0x4355,0x4356,0x4357,0x4358,0x4359,0x435a,0x435b,0x435c,0x435d,0x435f,0x4360,0x4361,0x4362]
def pr13 : Array Nat := #[0xd00183606a014363,0x4368,0x4369,0x436a,0x436b,0x436c,0x436d,0x436e,0x436f,0x4371,0x4372,0x4373,0x4374,0x4376,0x4377,0x4378,0x4379,0x437a,0x437b,0x437c,0x437d,0x437f,0x4380,0x4382,0x4383,0x4384,0x4385,0x4386,0x4387,0x4388,0x4389,0x438a]
def pr14 : Array Nat := #[0x438b,0x438c,0x438d,0x438f,0x4390,0x8416009032014391,0x4394,0x4395,0x4396,0x4397,0x4398,0x439b,0x439f,0x43a1,0x43a2,0x43a3,0x43a6,0x43a7,0x43a9,0x43aa,0x43ad,0x43ae,0x43af,0x43b0,0x43b1,0x43b5,0x43b6,0x43b7,0x903200c3b8,0x43ba,0x1303400c0c00d01801c3bc,0x43c0]
def pr15 : Array Nat := #[0x43c3,0x43c4,0x43c8,0x43c9,0x43cb,0x43cc,0xa81282904a0a01282704a2181282104a0281282004a028450860480841200a0480801202303e0880f82a03e0a40f82803e09c0f88603e0840f80a03e0800f80a112218440211100284402011004c0d00103221c4083a102048408120040480b80d02003c0000d0000c80000d0182144308410c20c4308210c2140508401420c050820141843ce,0xbc4a02f1262304902f1242301702f05c2344882f1222344802f1202384788d11e2304782f11e2384588d1162304582f1160933dd,0x7401600c3df,0x43e1,0x43e2,0xa0080841602f05c01c3e3,0x500480c01202a0ae0f02b8280ae1f82b8580ae2602b8260ae1042b8210ae0042b8610ae00c2b8130ae1342b82105a1341688d03e0bc0f8ab1580585609b1580385603515812856074158268560ab1540585509b1540285500e1540d45504a1541d05509a1540585489b1520d4548741522685480a0160d4058740162680581615026c5400e1501285409a1500280200e0081280209a0080841604d058268360a70342540d0360341100d0430341040d0500342800d03103404c0d0300340d0198500660c01987406618004050010038040300102980c8a50322900c8730321240c8580322740c8500320240c8010320c00c830044140288300a2140340300d01402700909c0c42703009c28c0c0a20302580c07f0302840c0260302340c0a003001c0c0030300bc0c03a102048408320040480102108a1342284105604c1589707c2341f03507c0bc1f02b00c2340304a00c0bc0309f08c1302309908c11c2309e08c2602309d08c2342304b08c1842302f08c0bc1708d1380bc4e08d11612c458071160bc458160c826c3200e0c80d43204a0c81d03209a0c80581e89b07a0281e80e07a0d41e84a07a1d01e89a07a0340803a0201d04c87408e034000320001283984a092260300610c025c2c03404c1a4468970020d00189601c1fc0709506a0d81a86905e58c3e7,0x1401203c0ae1f82b8210ae0042b8610ae00c2b8130ae1342b84d05a2340f81615426c5500a15403855035154128550741542685509a0162680204d0580d80d05003404c0d0340661401987406618004050010038040490321400c801032140288500d01402700909c0c42703009c1fc0c08d03000c0c03a102048408320040480104d08a04c1589707c2341f03507c0ac0308d00c1280304708c2342306108c2344e08d11612c458071160bc4589a07a0340803a0201d02380d0000c80004a0921843006911a25c008340061fc0703606a264444,0x8416009032014472,0x4473,0x4474,0x4476,0xc41201305a014477,0x447c,0x447d,0x447f,0x4480,0x4481,0x4486,0x4490,0x4492,0x4493,0x4495,0x10320480b86108c01c497,0xa81282904a0a01282704a2181282104a0281282004a21812021048028120200482180f82103e0280f82003e028448861100844400a1100804401403404c0d0120340040c8140300480c01202e0500b01202c050088130220480886108c0d40800e0002084308201413449b,0x34a8]
def pr16 : Array Nat := #[0xd01982b00c0144a9,0xa81282904a0a01282704a2181282104a0281282004a21812021048028120200482180f82103e0280f82003e028448861100844400a1100804401403c0500e01403404c0d0120341d01983215c038040320100040c8140ec0500c0030300480c01202e0500b01202c0500880302204c088120220e81f83507c0e81f04a00c184230ad020034080350200e80803a09003c0000e000034000320000c84000d0182084305410c208050540141f44ac,0x485a0121660505901216405058812162280580121602800b81202e2bc0b0a002c0500b01202c2bc088a0022050088120220934c9,0x485a0121660505901216405058812162280580121602800b81202e2bc0b0a002c0500b01202c2bc088a0022050088120220934cb,0x44cc,0x44cd,0x44cf,0x130340040c81202e01c4d0,0x44d2,0x44d3,0x44d4,0x300340c80100108a01c4d5,0x44d7,0x44d9,0x44da,0x44de,0x44e0,0xc41207e0ae1842b8130ae1342b84b03e0585503b1540d4550741542685503b16e0ec5b03b0160d40587401626805861058134160090102242287e08a1842281308a1342280700c2d41e81607a0ec1e83507a1d01e89a07a0ec3c83b0ea0ec1c8350721d01c89a0721344e1,0x1845d8bd0ae0142b8610ae1342b8321780c8400630fa0c83e8630c40c8310bb09a2e03186e0c62e8190b90642e01906e0640934e6,0x44f4,0x44f5,0x44f6,0x44f8,0x44fb,0x41602f0300e84086108a0244ff,0x4503,0x4b03e0d40586105801c504,0x4508,0x4509,0x450b,0x450c,0x450d]
def pr17 : Array Nat := #[0xa0480840f83201000c0c06108c02c50e,0x4512,0x840f803030014513,0x4516,0x4517,0x4518,0x451e,0x30300480b86108c01c51f,0x4522,0x4523,0x4524,0x4525,0x4526,0x4527,0x4528,0x4529,0xa0480840f83201000c0c06108c02c52a,0x452d,0x281202103e00c0c06108c02452e,0x4531,0x2103e00c0c06108c01c532,0x4534,0x4535,0xbc0c03a1021842280700c024537,0x12c0f8350161841607407a02453c,0x4540,0x4541,0x4542,0x4543,0x4544,0x4545,0x4547]
def pr18 : Array Nat := #[0x1c5687408e014549,0x454c,0x454d,0x454f,0x8412013034014550,0x4553,0x4554,0x4555,0x2802009010014557,0x455a,0x455b,0x5c1602b00c01455c,0x455e,0x4562,0x4563,0x8416009032014564,0x4566,0x4567,0x4568,0x456b,0x456c,0x456d,0x184160300340c80100108a02456e,0x4572,0x241200e0080041606108a024573,0x4578,0x2104804c0d00103201c579,0x457b,0x300340c80100108a01c57c,0x4580,0x2104804c0d00103201c581,0xc412074016014584]
def pr19 : Array Nat := #[0x4586,0x4587,0xc41207401601458c,0x458e,0x4591,0x4592,0x4594,0x4595,0x4596,0x4597,0x4598,0x4599,0x8416835016028020610581400d0310340c00d0500100c004030044140288300a21402703109c0c0270a217e1d45f8a117e3005f88d17e01c5f82f17e2f85f88d03001c0c02f0302f80c08d00c01c0302f00c2f80302f05c2344e02f138234458071160bc458be11613459a,0x359f,0x2105a0c40d00703001c5a9,0x280200700c0145af,0x45b0,0x45b1,0x45b2,0x28020090100145b3,0x45b4,0x45b5,0x841683103401c0c02f00c0245b7,0x45b9,0x45ba,0x45bb,0x45bc,0x45bd,0x45be,0x45bf,0x45c0,0x45c1]
def pr20 : Array Nat := #[0x45c2,0x45c3,0x45c4,0x45c6,0x45c9,0x45ca,0x45cb,0x45ce,0x45cf,0x45d1,0x45d2,0x45d3,0x45d4,0x45d5,0x45d7,0x45d9,0x45da,0x45db,0x45e0,0x45e1,0x45e2,0x45e3,0x45e4,0x45e5,0x45e6,0x45e7,0x45e8,0x45ea,0x45eb,0x45ec,0x45ee,0x45ef]
def pr21 : Array Nat := #[0x45f0,0x45f1,0x45f2,0x45f3,0x45f4,0x45f5,0x45f6,0x45f7,0x45f8,0x45f9,0x45fa,0x45fb,0x45fc,0x45fd,0x45fe,0x45ff,0x4600,0x4601,0x4602,0x4604,0x460c,0x460d,0x460e,0x4610,0x4611,0x4612,0x4616,0x4617,0x4618,0x461b,0x461c,0x461e]
def pr22 : Array Nat := #[0x4621,0x4622,0x4624,0x4627,0x4628,0x4629,0x462b,0x462c,0x462d,0x462e,0x462f,0x4630,0x4631,0x4632,0x463a,0x463f,0x4640,0x4641,0x4642,0x4643,0x4644,0x4645,0x4646,0x4647,0x4648,0x4649,0x464a,0x464b,0x464c,0x464d,0x464e,0x4651]
def pr23 : Array Nat := #[0x4653,0x4655,0x4657,0x4658,0x147d08605a0141681615823c5609b1580145600e1581d05609a1582c8550161542485508f1543e45509b154218550c215431c5500a1540145500e1541d05509a1540585489b1520145489a1522c8058160163e40589b0162180580a0160140589a0160585409b1500145409a1502c8020160083e40209b0082180200a0080140209a0080147c0860580141600514c0143609a0d8218750051d42184400a1100144409a1101507b8361ee0c07b8121ee1507b0361ec0c07b0121ec29c0e85403a2540e83603a1400e8a003a0c00e81203a29c0d0540342540d0360341400d0a00340c00d0120340c07a8301e8140798301e6140790301e40c0788301e01402e0300b8140198300660c0778301dc1405703015c140040300103a8768491da034768301da3a8760491d8034760301d8298758ea1d61cc758491d6274758501d6034758301d62980c8ea0321cc0c8490322740c8500320340c8300320c0118300441402d8300b61402703009c39c748e31d21d4748c01d200c748321d20bc748121d22f8748e817e39c5f8e417e2885f8e317e1d45f8a117e3005f82617e3985f88d17e2805f80717e00c5f83217e0bc5f81217e2f85f8e31ca1d47287f1ca300728031ca0bc728121ca2f8728e40302880c0e30301d40c0960301fc0c0a10303000c0260302340c0a003001c0c0030300bc0c0120302f80c0121c4280338120ce14c708121c204c700430b414c2d0a00b40482d04110204c408121be00c330120cc2f8330a01bc0486f0260042800100700400c010120042f8010011ba04c6e85808a1042280108a04c228531660485980314a10c0b85302e2800b81202e0983d0030f40bc6e08d1b60bc6d8d81b40546d0cf1b41f46d0611b40346d02f1b40e86d0c81b43646b8d81ae1306b8151ae3406b89e1ae33c6b87d1ae2606b89d1ae2346b8781ae12c6b8611ae0346b82f1ae0e86b8c81ae0bc6b07d1aa1846a82f1aa3206a88d07e0bc1f89e07c1f41f09807c2341f04b07c1841f02f07c3201f02f1a81d4698031a60bc698be1a62346902f1a42880307500c0980308d00c01c0300300c0bc030be00c054688471a233c6887d1a21846880d1a20bc688c81a21302301508c2642304708c3402309e08c33c2307d08c2602309d08c2342304b08c1842300d08c0bc230c808c0bc4982f19c0bc4902f05c320170be05c2344802f1202344e02f1382344782f11e2344584b11601c4582f116320458be1160346689d1980346609a0c80281e89a07a03465861194034650c81942746480d1922600809d02012c08061020034080c80201d04c8c708e1d02387a18c0346300118a2946207a1882746200d188160000010001e86180d1862940607a0182740600d018150430531301fc6106911a29c0285400a10c308530c22580707f01c3041786905eba465a,0xfd084004210fe1f81607e0fd1f80047e0970b03ec0089700204b679,0x131fe05058813162104158130562bc088410220500881302204b68f,0x184810fd084184210980c0184300fe1f82607e0fd1f81847e0531fc4004c05313010c7e8531fa404308430c2400308530c2093693,0x14530050d8218750051d4218440051101ac4305410c40c028a700a1ac0285400a06369a,0x505280314a050588031622bc3d0260f40503d0030f42bc08826022050088030224101303404c41801905006410018340060936a0,0xc0859070460c01183021441c11030044140848302124202d8500b641c2d8300b6140290300a44202705009c41c2703009c0936af,0xc0859070460c01183021441c11030044140848302124202d8500b641c2d8300b6140290300a44202705009c41c2703009c0936b1,0x46b3,0x904a12c1280704a0c41282004a21c8c05b0ae0042b8610ae00c2b8130ae1342b85215403855035154128550741542685500f22e2982009f08028c200a70801b02000908012c200070800c420020080458408871022282291508a4502291308a4482288908a16c2280108a1842280308a04c2284d08a4441e91007a43c1e90e07a4341e8b507a1481e80e07a0d41e84a07a1d01e89a07a4300000f0001cc6b4,0x46c5,0x24758090320480b84b2320246c6,0x4b03e0d40586c08001c6ca,0x46ce,0x46cf,0x46d0,0x1081280904a12c1280704a0801286323a0388e91c0ae16c2b8010ae1842b8030ae1342b80305a1341680703e0800f86323618c0200e0080c80204a0081b02004b08001c200200801d0198630100380411610221c4088a08a2242285b08a1842280308a134228630fa18c3100e0c40c83104a0c44683186e0c61646d2,0x46e8,0x46e9,0x46eb,0x46ed,0x2c41284b04a01c1283104a0801283b23e1d08f91e0ae16c2b8610ae00c2b8130ae1342b84b03e0800f83b16e0ec5b03b0160d4058740160e8058610581341606c08012c200070800802003b0661d01980e0102282288908a16c2286108a00c2284d08a0ec3c83b0ea0ec1c8350721d01c83a0724300000f0001646ee,0x4b03e0d40586105801c704,0x4705,0x4706,0x4707,0x4708,0x4709]
def pr24 : Array Nat := #[0x470a,0x16c7d00c1f40147d0031f404c7d02305a16c168c305a0301688605a0981684105a0141680305a04c1680526a2180f80503e14854880152014548351521d05490a0161480592601620005886016494058c7016014058350161d005852150120540051500385404a1504280205200849c02048008218020c2008490020050080380204a00816c7c0171f00047c0051f01847c02305816c160b305805c1605805821816098058004160050581841605214c2005300514c0143610a1d4148751261d4200750861d401475086110014440541ec0d87b0131ec0c07b0121ec29c0d0540342540d0360341040d0500342800d0130340c00d0120340c09a0500800c0200541e00d0780301e01d07803a1e029c1985406641419834066140198c70661e0198300661d01983a0663a8770601dc038770321dc0c0770a60103a804102010180040c201039804050010038040320100c0040ea1d8124760011d8034760301d82980c8ea0321cc0c8490321600c89d0321400c8010320340c8300323a8118540460d0118600460c0118542140d8850302140c0110a60b629c2d8ea0b61502d9050b60d02d9020b61802d8500b60c02d8a70a4150290950a40d8290500a40c02905009c0c0270032660d49983a2660489982626449499078264280990032640d49903a264048990e71d21d4748c01d200c748321d2128748121d22f8748e817e39c5f8a217e1d45f8a117e3005f82617e3985f92417e2805f80717e00c5f83217e1285f81217e2f85f86126200c9880d262048988982600989809d2602809806126000c9800d2600489800325e0489780325c048970031ca048728be1ca098968a025a00c9681225a0983b0a00ec00c3b0120ec0980c0a003001c0c0030300480c0be0301b8700531c004c700741c01104086e10210c40853102104408c710204c408741021d4330c00cc00c330320cc128330120cc2f8330a20041d4010a100430001026004398011240042800100700400c01032004128010120042f80103c1ba1f86e8011ba04c6e82a08a0f02282808a1f82285808a1042280108a04c22854166048598a702e1500b8a002e0480b8321b80d46e04a1b80e86e0e61b64946d9241b61e06d8321b60d46d84a1b60e86d8d81b40546d07d1b41846d00d1b40d46d03a1b43206d0d91ae3606b84c1ae0546b89e1ae1f46b8981ae2746b9251ae1e06b84b1ae1846b80d1ae0d46b83a1ae3206b8351ac0e86b0352580e8960351aa0e86a8c81aa4941f87807e0d41f83a07e494328780ca0d43283a0ca4941f07807c12c1f03507c0e81f0c807c1849580d2560c89584a2562609509d254398951242541849500d2540c89504a2540c86a04a1a80c86984a1a62f8698e61a4490690321a4128690e600c4900300700c0c80304a00c2f803061252034948611a2034688c81a22609409d2501849400d2502602309d08c12c2306108c034230c808c0583209b0c8038320740c82c81e81607a3e41e89b07a3081e8c707a0381e87407a0546507d1941846500d1940d46503a1943206504c0200540809e0201f408098020274081250201e00804b0201840800d0200d40803a0203200805424e0e8938a7090150240780900e82407a18a1e46280118a038628a50001e8000a40001e40005800030800001000038000520e61283983224c428248520924902484a092398400321003a86180d186184810a60183a80609d018034060980c01843005410c4884c03404c4884e9201cc0d89292024829c0285400a48c309220c24140183400648c0692201a484191200642541a83606a48425120094ed470b,0x5327a13c9e8430aa14c2a8310aa13c2a9362780249d9362764e4700871c014c7004f1c04e8409391024e04088710210c408531020c44084f10203c6293618a4dc0000f000024001360000db761,0x6e27a13c9e8440aa1b82a8310aa13c2a9362780249d9362764f8700871c01b87004f1c04fc4093e1024e0408871021104086e1020c44084f10203c6293618a4dc0000f000024001360000db768,0x4f27a0c42a84f0aa1e49e1362782909d8792760249d93627621c7004f1c04e0408871020c44084f1025006280f18a1e46293618a504001400004dc0000f00029000079000024001360000db771,0x4f27a0c42a84f0aa1e89e1362782949d87a2760249d93627621c7004f1c04e0408871020c44084f1025086280f18a1e86293618a50c001420004dc0000f0002940007a000024001360000db778,0x4d2900842b84d0ae26c5609a1583e45509b1540285509a1542246e84d1ba51c2288908a0842284d08a514320b50c826c3209a0c85181e94507a5101e8b507a3e41e89b07a0281e89a07a0db783,0x7e290134a40280ae1f82b8210ae1342b89a1580285509a1545246e8891ba1f86e84d1ba5282294908a51c2288908a0a02287e08a0842284d08a2d43209a0c85101e8b507a0281e89a07a0db78a,0x3c290134a402a0ae0f02b8210ae1342b89a1580285509a15452c6e8891ba0f06e84d1ba5302294b08a51c2288908a0a82283c08a0842284d08a2d43209a0c85101e8b507a0281e89a07a0db791,0x4d2900842b84d0ae0585609a1582c8550161540285509a1542246e84d1ba51c2288908a0842284d08a534320b50c80583209a0c85381e94d07a5101e8b507a2c81e81607a0281e89a07a0db799,0x2c41284204a2341284b04a01c1282004a4782b91c0ae16c2b88c0ae1842b8030ae1342b80305a1341688d2a42340f84b03e01c0f82003e0d40584a0081841604d0580480d06c0802c4200420802342004b08001c200200801d01983a066038040320100340c95110221c408741020e84088908a16c2286108a00c2284d08a2344e08d11612c45807116080458b507a0381e87407a1d02395000003c0000e0000c80014f11a1a44687f01c1f479e,0x16cab04d2ac54c2b85b0ae2402b84d0ae2289808926016c9804d2605542288a08a5502288908a54c2285b08a2402284d08a0937a0,0x37ab,0x16cab04d2ac54c2b85b0ae2402b84d0ae2289808926016c9804d2605542288a08a5502288908a54c2285b08a2402284d08a0937ba,0x224228b507a0147c3,0x4b03e0d40586105801c7c5,0xc1680703e1280204b0800247c9,0x47cd,0x47ce,0x12c0f835016184160070800247cf,0x47d3,0x47d4,0x47d5,0x47d6,0xc40e83103401cab80d0180247d7,0x47db,0x47dc,0x47de,0x147d08605a014168051522180580501601454086008014020051f021816005058014530050d8218750051d4218440051100c07b0500340c00d0301e0140198300660c0770500100c0040301d81400c8300320c085030044140290300a41402703009c1247e0,0x47eb,0x703e1280206c08001c7ec,0x218ac88605a0841680505a2180200a008014020050d8218750861100844400a110014440502b01400d0310340c00d050010024040300100c0110500b6140290500a21402700909c0c42703009c2885f87517e2845f8c017e01c5f8be17e01c0c0be0301d04080108a0d41f03a07c01c030be00c1842300d08c1d01e861020034080350200e80800100020c4305410c1a47f0]
def pr25 : Array Nat := #[0x4811,0x305a01c0f84a00801c812,0x4816,0x4817,0x50ad0a204a0a4128a104a1081280704a0801286323a0501680305a04c1680703e0800f87401618c0200e008128020010580500d0130340480d0070800802007406618c0400e0100c8040010320503d01402c0500a8130560500880302204c088120220d41f03a07c1842300d08c1840800d0200d40803a02018c3f0630fa18c3100e0c40c83104a0c41b83187f01c1a4818,0x50ad04b04a01c1283104a0801283b23e050ad81405a04c1684b03e01c0f82003e0ec5b03b0161d00584a0081841601403412c200070800802003b066038040320100040c80d0320500b01402a0500880302204c088120220ec1e03b0ea0ec1c8350721d01c83a072134839,0x4854,0x4856,0x4857,0x2183e0860da2181682105a2180f8861d421844021110028440051101400f0500381400d031034140200500b61402905009c0242703109c0c02700717e0c85f84a17e2f85f8741020c80104a0042f80100108a0d41f03a07c0c80304a00c2f80306108c0342305410c134858,0x305a01c0f84a00801c872,0x4876,0x4877,0x50ad0a204a0a4128a104a1081288d04a12c1280704a080128142b60501680305a04c1688d03e12c0f80703e0800f87416c0d405874016128020610580500d81403404c0d0120342342004b08001c200200800e8198320100040c80d0320500a81302a04c1581402200c088130220480888d12012c4808d11612c45807116080458b507a0381e83507a1d01e87408e03c000010000380000d0001a44695d0961a42595c00225c0087f01c1f4878,0x4caf81409804c260131fe05058813162104af0132bc2bc0a84102a0500a81302a104158130562bc088410220500881302209389c,0x4c1587f01c0148a1,0x48a3,0x48a4,0x48a5,0x48a6,0x48a8,0x48b8,0x48b9,0x48ba,0x5b1f42407d00c1f40147d0031f404c7d02305a16c1689305a240168c305a0301688605a0981684105a0141680305a04c1685215223c54880152014548351521d05490a0161480589201623c0592601620005886016494058c7016014058350161d00585215023c540481500145400e1501285410a0081480209200823c0212700812002086008308021240080140200e0081280205b1f005c7c0901f00047c0051f01847c02305816c160b305805c160930582401605805821816098058004160050581841605214c2005300514c0143610a1d4148751261d4200750861d401475086110014440541ec1a47b0361ec04c7b0301ec0487b0a70341500d0c10341a40d0950340d80d0410341400d0a003404c0d0300340480d0541e00d0780691e00c0780741e00e8780a7066150199050660d0198c10661a41985006631c198780660c0198740660e8198ea1dc270770601dc038770321dc0c0770a60103a8040ce01027004102010180040c201039804050010038040320100c0040ea1d8270760491d80047600d1d80c0760a60323a80c8ce0322700c8730321240c8580322740c8500320040c80d0320c00c8ea0461501183404618011830046150850362140c0850692c00d8b00302c00d0b38692ce0c0b38300442982d8a70b63a82d8540b64142d8340b64082d8600b61402d8300b629c290540a4254290360a4140290300a4304288690a2254288360a2140288300a2414340340d0304340690d0140340300d01402703009c208728681ca1fc728031ca0bc728121ca28c0c08203059c0c0680302580c07f0300980c08d0302800c0030300bc0c0120301b8700531c004c700741c00e8700121c01104086e10210c40853102104408c71021e0408a010204c408741020e8408121021d4330c00cc00c330320cc128330120cc28801075004284010c0004098010e6004490010a000400c01032004128010120040f06e87e1ba0046e8611ba00c6e8131ba0a82283c08a0a02287e08a1602289808a0982284108a0042286108a00c2281308a208598541665bc598121661fcb90362e21a47f96c1fe04c7f8a302e29c0b88202e1500b97002e5bc0b8a002e0480b8960ac1fc2b0952dc0d8b70c10561a41596d0565b01584105604c158831aa1446a8971aa0d46a82f1aa0e86a89f07c20c1f16007c1441f0fb07c25c1f12507c2341f07807c0d41f02f07c0e81f0821a61a06982b1a60c86984a1a60bc698a300c2080316700c1a0030ff00c0ac030e600c4900308d00c0c80304a00c0bc030831a2144688471a21846880d1a20bc6889f08c20c2316008c1442309908c11c2309808c2742308d08c1842300d08c0bc230831262084982b12625c4982f1261446706819c1fc6709719c0bc67083124208490471241fc4902f1240bc1709f12028c48083120208480ff1200ac480fb12025c4808d1200bc4816013859c4e0511381a04e0961381fc4e0fb13825c4e08d1380bc4e09f11e28c4788311e2084789911e11c4789611e1fc4788d11e0bc4788d1160bc458160c826c3200e0c80d43204a0c81d0320b207a0581e8f907a26c1e8c207a4941e92407a31c1e80e07a0d41e84a07a1d01e8151941f465061194034650351940e86504c0200540809e0201f408098020274081250201e008061020034080350200e8080972d60d07208324e150938b824e0e8938691325a04c8741323ec2c8970b2414718341c627c240a709020c240540905a8240b80901e02403a0903042386908e5a42396808e31c2387408e1e86287918a0046280e18a0346283218a2940007a00029000079000160000c2000274000e60000040000e00003400032000148398680e65943984a0e62089316324c0c89310a09259c248520921a02496609259424924092128248a31002084016410058c400e61000c8400ea18620c619611860346185120433c810612042980609f0183a806083018588061610182740600d018580300510c0340300cf0c0260300610c025c2c08310c2084305410c0d01307f1840d89286911a3ec0089700227c028a300a29c0288300a2080285400a414018340062580707f01c2541a83606a3041786905f12c8bb,0xc01d22f8748a117e3005f80717e2f85f9750cc574330c00cc2f8331760045d401174004574010a1004300010070042f8010c81b412c6b8c81ae2b4650c81945cc080ad02012c080c80200db8fc,0xbe1d201c5f8be17e574330be0cc5d00115d00401c010be0041f46d0c81b42786b87d1ae12c6b8c81ae5dc650ad1941f4650c81945e0081770205cc080ad0202780807d02012c080c80200db904,0x751d22f8748a217e1d45f80717e2f85f9790cc574330750cc2f83317a0045e401174004574010a20041d4010070042f8010c81b412c6b8c81ae2b4650c81945cc080ad02012c080c80200db90d,0xbe1d201c5f8be17e574330be0cc5d00115d00401c010be0040546d0c81b41306b8151ae12c6b8c81ae5ec650151942b4650c81945f00817b020130080150205cc080ad02012c080c80200db930,0x5327a13c9e8430aa14c2a8310aa13c2a9362780249d9362764e4700871c014c7004f1c04e8409391024e04088710210c408531020c44084f10203c6293618a4dc0000f000024001360000db946,0x6e27a13c9e8440aa1b82a8310aa13c2a9362780249d9362764f8700871c01b87004f1c04fc4093e1024e0408871021104086e1020c44084f10203c6293618a4dc0000f000024001360000db94e,0x4f27a0c42a84f0aa1e49e1362782909d8792760249d93627621c7004f1c04e0408871020c44084f1025006280f18a1e46293618a504001400004dc0000f00029000079000024001360000db958]
def pr26 : Array Nat := #[0x4f27a0c42a84f0aa1e89e1362782949d87a2760249d93627621c7004f1c04e0408871020c44084f1025086280f18a1e86293618a50c001420004dc0000f0002940007a000024001360000db95f,0x4981,0x4982,0x4985,0x51f42181680505a0145488601601405805150218020050080147c086058014160050d8218440051100c07b0500340c00d0301e0140198300660c0770500100c0040301d81400c8300320c0118300441402d8300b61402703009c0bc7288d0300bc0c0121662800b81202e0bc6a88d07c0bc1f02f1a62340302f00c0bc6888d08c0bc2302f1260bc1708d1200bc4808d1160bc4580d1862740600d0181cc986,0x2c41282704a1081280a04a12c1283104a0801282004816c2b8900ae1f82b8050ae1842b8130ae1342b84d05a0800f83b016134160200800ec198ea2761e89d89c2760389d80d2760c09d9362764d8041360321342283b0200ec3a83b0720d41c8740720e81c936000134993,0xc01102f05c0149a5,0x49ab,0x49ac,0x49ad,0x49ae,0x49af,0x49b0,0x49b1,0x51f42181680505a0145488601601405805150218020050080147c0860580141600514c014360861d401475086110014440301ec1400d0300340c0780500660c0198301dc14004030010124760301d81cc0c8490321400c8300320c0118302c00c0110500b60c02d8500a20c02885009c0c02702f1ca2340c02f030048598a002e0480b82f1aa2341f02f07c0bc6988d00c0bc030471a20bc6889908c11c2308d08c0bc2302f1260bc6702f05c2344802f1202344e02f1382344582f1161d04c8c708e1d02384a0e64902484a0920346189d0180340608310c27c0288300a28c9b2,0x1b0200b507a0149c1,0x49c4,0x49c5,0x143602f05c0149c6,0x49c9,0x49ca,0x51f42181680505a0145488601601405805150218020050080147c0860580141600514c014360861d401475086110014440301ec1400d0300340c0780500660c0198301dc140040300100c0760500320c00c8300441402703009c0bc7288d0300bc0c02f1aa2341f02f07c0bc6988d00c0bc0302f1a22342302f08c0bc6702f05c2344e02f1382344582f11619c9cb,0xc41201305a1d00580308a0249dd,0x49ea,0x49ed,0x49ee,0x49f1,0x49f2,0x49f4,0x2180f8860160d405886008218160861d42184400a110014440502a6140200500b81401985015c140040501d6034758500320340c8502121408e0500b60242d8300b6140290500d01402700909c0c0270141ca0bc728140300bc0c0141c0050408140cc050010141ba0502281414a0505901416200c588121620503d01402c050088030220480887d1ae12c6b8611ae0346b8351ae0bc6b83a1ae3206b82f1aa12c1f03a07c3201f02f1a601c0302f1a20348c84b08c184230c808c0bc4982f05c1d01e80d1921840803a0203200800d1880040000d1860340614f10c6004311a10c6084306b10c6044308210c150430540141500283801a6001a97f06a5f81a97d06a2541a83706a0d81a8c105e3149f6,0x4a2e,0x4a2f]
def pr27 : Array Nat := #[0xb104a0a41280904a12c1280704a0c41282004a0d08f88723016c2b83c0ae0042b8610ae00c2b8130ae1342b82b30e11cc30521540585500e1540d45504a1541d05509a1541d0c180f22e3e8200a90802982009f08028c200a70801b0200b10800a42000908012c200070800c42002008061419834066458408871022282294b08a4542291408a44c2291208a2242285b08a0f02280108a1842280308a04c2284d08a6100302b00c60c2304708c4441e94d07a4401e90f07a4381e90d07a2d41e85207a0581e80e07a0d41e84a07a1d01e89a07a4342387408e4300000f00028ca30,0x4a48,0xd01800ca49,0x4a4b,0x4a4e,0x4a4f,0x4a50,0x4a51,0x4a53,0x4a54,0xd01800ca55,0x4a57,0x4a58,0x4a59,0x4a5a,0x4a5b,0x4a5c,0x2c41282904a1081280904a0281280704a0801282004816c2b8900ae0f02b8010ae0142b8030ae1342b84d05a0800f863008134160540aa1a42a8530aa0c02a8740aa0482a84f0aa13c0d02008013c1986301013c40863004134228630fa18c3100e0c40c83104a0c4134a5d,0x4a73,0x1b02008908a014a74,0x4a77,0x4a78,0x4a79,0x4a7a,0x4a7b,0x4a7c,0x4a7d,0x4a7f,0x4a80,0x4a81,0x4a82,0x4a85]
def pr28 : Array Nat := #[0x4a86,0x4a87,0x4a88,0x4a89,0x4a8a,0x4a8b,0x4a8c,0x4a92,0x4a94,0x4a95,0x4a96,0x8603e218058860082187508611002844005110140a98500801402e050066140570500101402d8090b60c42d8300b61402700909c0c42703009c0507281403005070014102050330140040505281416200c58813162048588140f40500880302204c0881202212c2306108c184080010000340605410c15ca97,0x4aa8,0x4aa9,0x4aaa,0x4b0800e81980d03201caab,0x4aae,0x4aaf,0x4ab0,0x4ab1,0x4ab2,0x4ab3,0x4ab4,0x1203401c2003201001cab5,0x4aba,0x4abb,0x4abc,0x4abd,0x4abe,0x4abf,0x4ac0,0x4ac1]
def pr29 : Array Nat := #[0x4ac2,0x4ac4,0x4ac5,0x2180f886016218160861d42184402111002844005110140200500661400c8500b6140290500d01402700909c0c42703009c0500c014102050228141620503d01402c0500880302204c088120221f46b84b1ae1846b83a1ae3206b8c807c320230c80202084305410c134ac6,0x4add,0x1d023897002014ade,0x4ae1,0x4ae2,0x2180f886016218020861d4218440211100284400511014020050066140040500b60242d8300b61402700909c0c42703009c0500c014102050010141620503d01402200c088130220480886108c184080010000340605410c104ae3,0x4af3,0x4af4,0x4af5,0x4af6,0x4af7,0x4af8,0x4af9,0x4afb,0x4afd,0x4afe,0x4b00,0x4b01,0x4b02,0x4b05,0x4b07,0x4b08,0x4b0a,0x4b0c,0x4b0d,0x4b0e,0x4b0f,0x4b10,0x4b11]
def pr30 : Array Nat := #[0x4b17,0x4b18,0x4b1c,0x4b1d,0x4b1e,0x4b1f,0x4b20,0x4b21,0x4b22,0x4b23,0x4b24,0x4b25,0x4b26,0x4b27,0x4b28,0x4b29,0x4b2a,0x4b2b,0x4b2c,0x4b2d,0x4b2e,0x4b2f,0x4b30]
def prTab : Array (Array Nat) := #[pr0,pr1,pr2,pr3,pr4,pr5,pr6,pr7,pr8,pr9,pr10,pr11,pr12,pr13,pr14,pr15,pr16,pr17,pr18,pr19,pr20,pr21,pr22,pr23,pr24,pr25,pr26,pr27,pr28,pr29,pr30]
def pr (i : Nat) : Nat := ((prTab[i/32]?).getD #[])[i % 32]?.getD 0
def nd0 : Array Nat := #[0,1,2,0x64015004403,4,5,6,7,0xe403500c408,9,0xe403500c40a,11,12,0x17405901540d,0x7101b406801940e,15,16,0x8d0224085020011,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def nd1 : Array Nat := #[32,33,34,35,36,37,0x13104c413104c413904c413904c413104c413504d413104c4128049011c047011c048411c04b4128049011c047011c048411c04601150454111043026,0x14c0524144050427,40,41,42,43,44,45,46,47,0x1910630189061030,49,50,51,52,53,0x6c014406b436,55,56,57,58,59,60,61,62,63]
def nd2 : Array Nat := #[64,0x81420107f441,66,67,68,69,70,0x8c422c08a447,0x8e423108a448,73,74,75,76,77,78,0x99026109704f,80,81,0x2b90ae42b90ae42cd0b342b90ae42c80b202b90ae42c40b002c00af02b90ae42b50ac02ad0aa42a40a8029c0a602980a602940a502940a4428c0a242840a102840a1028409f028109f427909e452,83,84,85,0x2fd0be42890bd42f10bb456,87,0xc4430d0c2458,0x2b90ae42b90ae42cd0b342b90ae42c80b202b90ae43240b002c00af02b90ae42b50c803200aa431c0bf43180c603180c602940a502940a4428c0a242840a102840a1028409f031509f427909e452,89,90,91,92,93,94]
def nd3 : Array Nat := #[95,0x3810e043810e0438d0e343810e043810e043880b002c00e103810e0437d0de02ad0dc43740bf429c0a7029c0dc436c0db03610da02890d903640d903640d8435d0d6460,97,98,99,100,101,0x3c50f0466,103,105,0x4211084421108442110844211084421108442110844211084421108442110846a,107,108,0x4211084421108442110844211084421108442110844211084421108442110846d,0x44110f443d117444110f443d1160458115444d114444d112444510f444110f443d10e441106d843110b441106cc1af06a8419069c41110e441110441b610c442d10441b306bc1aa10641a7104440c102040410104010ff03f90fd43f10fa43ed0fa43e50f803dd0f603d50f4068,110,111,0x47811d047011b070,113,114,115,0x1254491123474,0x50014005001400500140050014005001400500140050114045011404501140476,0x50014005001400500140050014005001400500140050114045011404501140477,0x53c150053c14e053514c452c14a0524076c521076c51d077c515076c4ed144050d076c4ed1420505076c4ed13c04f013e44f013d44f013c04f013b44e813904e013804a513744d913404d413404cd13244c413004bc12e04b812a44b512c44a012804ac12804a912944a0127075,120,121,0x55515444a510107a,123,124,125,0x56812707e]
def nd4 : Array Nat := #[127,128,0x5d517445cd17142c817205c511c046c17145c016f05b816d05b116b05a916905a016802a91650594165059d166459416405901634589161457815e0578160457d15e081,0x45817845dd062482,131,132,133,134,135,136,137,138,139,0x186061418448c,141,142,143,0x18e063518c090,145,146,0x67519d467519d46851a1467519d467519d46801a006610b002c019f0679194467519d467119b06680bf46641990664199066119706580a246541950654194464d192493,148,149,150,151,0x7011c047011c047011c047011c0471c1c6071519847101c306791b147081c107011c046fd1be46f51bc46ec0ab46e11ba06e41b906e41b906611b846dc1b643611b506d01b206cc1b206c81b206c50d846c01af06b81ad06b11ab498,0x1cb47291c9499,154,0x74901c47441d0473d1ce09b,156,157,0x8041fd1d609e]
def nd5 : Array Nat := #[0x81420107f49f,160,161,162,163,164,165,0x1e247851e04a6,167,0x8e423108a4a8,169,170,171,172,173,174,0x7b81ed0af,176,177,178,179,180,181,0x81d207483520c481d207482c207482820908202074818205081020308042020804201080420108001ff07f81fd07f01fc07f01fc07f01fb07e81f907e41f907e41f94b6,183,184,0x8492114b9,186,187,188,189,190]
def nd6 : Array Nat := #[191,192,193,194,0x21f487921d4c3,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222]
def nd7 : Array Nat := #[223,224,225,226,227,228,229,230,231,232,0x24a49250194e9,234,235,236,237,238,239,240,0x25549512534f1,242,243,244,245,246,247,248,249,0x98025f0fa,0x98c2620fb,252,253,254]
def nd8 : Array Nat := #[255,0x100,0x101,0x102,0x103,0x104,0x105,0x106,0x107,0x108,0x27a49e5278509,0x10a,0x10b,0x10c,0x10d,0x10e,0x10f,0x110,0xa1c28609e1285111,0x112,0x113,0x114,0x115,0x116,0x117,0x118,0x119,0x11a,0x11b,0x11c,0xa6529811d,0x11e]
def nd9 : Array Nat := #[0x11f,0x120,0x121,0xa8528609e12a0511,0x122,0xa9128609e12a3111,0x123,0x124,0x125,0x126,0x2ac4aad2aa527,0x128,0x1912af529,0x12a,0x2b54ad12b352b,0x12c,0x12d,0xae427949e12a0511,0x12e,0x2bf4af92bd52f,0x130,0x131,0x132,0x133,0x134,0x2c84b1d2c6535,0x136,0x137,0xa9128609e12cb111,0x138,0x139,0x13a]
def nd10 : Array Nat := #[0x13b,0x13c,0x13d,0x13e,0x13f,0x140,0x141,0x142,0x143,0x144,0xb6d28609e12a0511,0x2df4b792dd545,0x146,0xa1c28609e12a0511,0x147,0x148,0x149,0x14a,0x2e509e5278509,0xba92e914b,0x14c,0x14d,0x14e,0x14f,0xbc92f1550,0xa8528609e12f3511,0x151,0xa9128609e12a0511,0xa9128609e12f5511,0x152,0xbe52f8553,0x154]
def nd11 : Array Nat := #[0xa9128609e12fb511,0x155,0x156,0x157,0x158,0x159,0x15a,0x15b,0x15c,0x15d,0x3094c2130755e,0xc2c27855f,0x160,0x161,0xae428609e12a0511,0x162,0x163,0x164,0x165,0x166,0x167,0x168,0x169,0x16a,0x16b,0x16c,0x16d,0x16e,0x16f,0x170,0x171,0x172]
def nd12 : Array Nat := #[0x173,0x174,0x175,0x176,0x177,0x178,0x179,0x17a,0x17b,0x17c,0x17d,0x17e,0x17f,0x180,0x181,0x182,0x183,0x184,0x185,0x3414d0133f586,0x187,0x188,0x189,0x18a,0x18b,0x18c,0x18d,0x18e,0x18f,0x190,0x191,0x192]
def nd13 : Array Nat := #[0x193,0x194,0x195,0x196,0x197,0x198,0x199,0x19a,0x19b,0x19c,0x19d,0x19e,0x19f,0xd953645a0,0xd953665a0,0xd953675a0,0x1a1,0x1a2,0x1a3,0x1a4,0x1a5,0x1a6,0x1a7,0x1a8,0x1a9,0x1aa,0x1ab,0x1ac,0x1ad,0x1ae,0x1af,0x1b0]
def nd14 : Array Nat := #[0x1b1,0x1b2,0x1b3,0x1b4,0x1b5,0x1b6,0xd953815a0,0x1b7,0x1b8,0x1b9,0x1ba,0x1bb,0x1bc,0x1bd,0x1be,0x1bf,0x1c0,0x1c1,0x1c2,0x1c3,0x1c4,0xe4d3925c5,0x1c6,0x1c7,0x1c8,0x1c9,0x1ca,0x1cb,0x1cc,0x1cd,0x1ce,0x1cf]
def nd15 : Array Nat := #[0x1d0,0x1d1,0x1d2,0x1d3,0x1d4,0x1d5,0x1d6,0x1d7,0x1d8,0x1d9,0x1da,0x1db,0x3b91dc,0x1dd,0x3bf4ef93bd1de,0x1df,0x1e0,0x1e1,0x1e2,0x1e3,0x1e4,0x1e5,0xf783de0f783de0f783de0f783de0f783de0f783de0f783de0f783de0f783de1e7,0xf713dc4f713dc47db3dc47db3dc4f3c3cf0f713cf0f713dc4f713dc4f713dc4f711f6cf711f6cf713cf0f3c3dc4f3c3dc4f6d3da4f653d84f5d3d64f543d44f4d3d24f453d00f3d3cf4f3d3cf4f3d3cf4f3d3cf5e6,0x3e05e8,0x1e9,0x1ea,0x3e64f953e41eb,0x44311094415105440510143f50f943d50f140f50fd43e50f543c503d40f503d43b10e94394fd13fa4fd143850dd3fa4fd14394fd13fa4fd13f450e14374fe93f44fd13fa50d44340fd143650d44340fd13f44fe943210c43f450cd43210c43f4503d40f50c041b50bd42e506d41b50ac42d10b041b50ac42a45dd42905dd1775099428109d426507141c50714255091421108c4221071421108141f107841e107441d106841c506d41a0ff13fc50654184ff1415105c4160ff141510514131048411104040f503d40e103840d503040b5029409502040750193fd4ff540550113fd500440310083fd50044004ffc3fe0ff83fb0ff53fc4fec3f44fe93f80fdc3f60fd43f44fd13fa4fe43f80fdc3f60fd43f44fcc3f20fc43f10fc03ef0fb83ee0fb43ed0fb13eb4fa13ec4fad3ea4fa93e94fa53e85ec,0x11c447051b545851c146f51b946d516145851b03f44fe93f44fd143850dd3fa4fd13f44fd145851ad46a11a5468519c1775099466109d4655190463518846111804601180460117d45e117545c516d45a5165458515c40d515840b5155454101d4535148451514044f113c44f113c3f4513944d513044b51294490fb44484fb144751194455ed,0xf9541c5ee,0x1ef]
def nd16 : Array Nat := #[0x1f0,0x1f1,0x11e44781f2,0x1f3,0x1f4,0x1f5,0x1f6,0x1f7,0x1f8,0x1f9,0x1fa,0x1fb,0x1fc,0x49a52644985fd,0x1ff,0x12954a552954a5483b4a5483b4a5529c4a5529c4a552984a552984a5527049c127049c12704a312914a312694a212884a112804a012804a0128049f527949d527149c5fe,0x12ad4aa600,0x13284ca13284ca13284ca13284ca13284ca13284ca13284ca13284ca13284ca202,0x13284ca13284ca13284ca13284ca13284ca13284ca13284ca13284ca13284ca203,0x847211c847211c84b211c84b211d3204c713204c713184c513184c513104c413104c413104c3128c4a312914c253044bf13004bf12694be12f84bb52f54bc12804a012804bb52914a012e44ba12e44b8127d4b752d849e52d44b412cd49d52c84b112c04af12b94ad52b94ad601,0x204,0x205,0x206,0x4a453454a1207,0x208,0x209,0x20a,0xc4430d0c260b,0x20c,0x20d,0x20e,0x20f]
def nd17 : Array Nat := #[0x210,0x13a54e953a14e953a14e7139c4e7139c4e7139c4e8139d4e7539d4e7539d4e7612,0x13cc4ee53b54ec53ad4f21389221d3894e553894e3138c4e313914e313894f113ad4f053bd4ee53b54ec53ad4ea53894e248874e253954e2538c4e3138c4e4538c4e2611,0x213,0x214,0x215,0x216,0x217,0x14095010361500618,0x219,0x507541950561a,0x21b,0x21c,0x21d,0x21e,0x21f,0x51154404bf12ed50f220,0x221,0x1454514222,0x223,0x224,0x225,0x132851d13284ca147451d13284ca147451d13284ca13284ca147451d147451d203,0x146951a546951a48db51a48db51a547051a547051a546c51a546c51a5464519146951914694c3128c4a312914c253044bf13004bf12694be12884bb52884a112804a012804a012804a012e44ba12e44b8127d4b752d849e52d44b412cd49d52c84b112c04af14655195465519601,0x226,0x4bb5484520627,0x228,0x229,0x22a,0x14544bb622,0x22b,0x22c]
def nd18 : Array Nat := #[0x22d,0x22e,0x22f,0x52c54694bf12ed52b230,0x231,0x14c152f12ed52b232,0x233,0x53352ed520634,0x235,0x236,0x14ec53a54e4538637,0x14fd53e53c453d638,0x239,0x23a,0x23b,0x23c,0x23d,0x23e,0x23f,0x152c54a240,0x241,0x242,0x243,0x1548551244,0x245,0x246,0x247,0x1565558648,0x249,0x24a,0x4a453453d5207,0x15750fe64b]
def nd19 : Array Nat := #[0x24c,0x847211c847211c84b211c84b211d5845601584560146c211d46c211d57c55f157c55f157c4c3128c4a312914c253044bf13004bf12694be12f84bb52f54bc12804a012804bb52914a012e44ba12e44b8127d4b752d849e52d44b412cd49d52c84b112c04af157d519557d519601,0x24d,0x24e,0x159555864f,0x250,0x251,0x252,0x253,0x15484a4644,0x254,0x255,0x12954a552954a5483b4a5483b4a5529c4a5529c4a552984a552984a5527049c127049c12704a312914a312694be12f54bc12804a012804a4528049f527949d527149c5fe,0x15c512555c056f656,0x257,0x15dd57615d5574658,0x259,0x57a52914d165a,0x25b,0x57f55f957d65c,0x25d,0x58212914d165e,0x9e958525f,0x260,0x261,0x9e958d262,0x263,0x264,0x265,0x266,0x267,0x268]
def nd20 : Array Nat := #[0x269,0x26a,0x26b,0x26d,0x16a15a756995a5569006456905a316895a116805a01680064568059c567159c5671283d671283d67159e167159e167159d167159d167159b166c59b166c59b166c59b26c,0x5aa419106266e,0x8475ae48475ad484b211d6ad5ab5470211d6ad5ab546c211d6b15ab5464519146451916ad4c3128c4a312914c253044bf13004bf12694be12f84bb52f54bc12804a012804bb52914a012e44ba12e44b8127d4b752d849e52d44b412cd49d52c84b112c04af14655195465519601,0x16993fc66f,0x270,0x271,0x272,0xf9941c673,0x274,0x275,0x16d95b656d95b6484b5b6484b5b654705b654705b6546c5b6546c5b6546451916d951916d94c3128c4a312914c253044bf13004bf12694be12f84bb52f54bc12804a012804bb52914a012e44ba12e44b8127d4b752d849e52d44b412cd49d52c84b112c04af14655195465519601,0x16a106456e0406676,0x277,0x847211c847211c84b211c84b211d470211d470211d46c211d46c211d464519146451914644c3128c4a312914c253044bf13004bf12694be12f84bb52f54bc12804a012804bb52914a012e44ba12e44b8127d4b752d849e52d44b412cd49d52c84b112c04af14655195465519601,0x278,0x279,0x27a,0x27b,0x27c,0x27d,0x27e,0x27f,0x280,0x281,0x282,0x283,0x284,0x285]
def nd21 : Array Nat := #[0x286,0x287,0x288,0x289,0x28a,0x28b,0x28c,0x28d,0x28e,0x28f,0x290,0x291,0x292,0x293,0x294,0x295,0x296,0x297,0x298,0x299,0x29a,0x29b,0x29c,0x29d,0x29e,0x29f,0x2a0,0x2a1,0x2a2,0x2a3,0x2a4,0x2a5]
def nd22 : Array Nat := #[0x2a6,0x2a7,0x2a8,0x2a9,0x2aa,0x2ab,0x2ac,0x2ad,0x2ae,0x2af,0x2b0,0x2b1,0x2b2,0x2b3,0x2b4,0x2b5,0x2b6,0x2b7,0x2b8,0x2b9,0x2ba,0x2bb,0x2bc,0x2bd,0x2be,0x2bf,0x2c0,0x2c1,0x2c2,0x2c3,0x2c4,0x2c5]
def nd23 : Array Nat := #[0x2c6,0x2c7,0x2c8,0x2c9,0x2ca,0x2cb,0x2cc,0x2cd,0x2ce,0x2cf,0x2d0,0x2d1,0x2d2,0x2d3,0x2d4,0x2d5,0x2d6,0x2d7,0x2d8,0x2d9,0x2da,0x2db,0x2dc,0x2dd,0x2de,0x2df,0x2e0,0x2e1,0x2e2,0x2e3,0x67a19e867a19e867a19e867a59e967a6e5,0x6901a406901a406901a406901a406902e6]
def nd24 : Array Nat := #[0x1a506941a506941a506941a506941a506945a516945a516945a516945a516946e7,0x1a7869d1a7869e1a7469d1a7169b5a7169b5a7169b6e8,0x1a846a11a846a11a846a11a846a11a846a11a846a11a856a15a856a15a856a16e9,0x1ac06b01ac06b01ac06b01ac06b01ac06b01ac06b01ac06b01ac06b01ac06b02ea,0x1ac06b01ac06b01ac06b01ac06b01ac06b01ac06b01ac06b01ac06b01ac06b02eb,0x1ac86b21ac8303cc0f303cc13303cc0f303cc0f303cc0f303cc0f303cc13303cc0f303cc13303cc0f303dab86ad1ab06ab1ab86ae1ab46ad1ab06ab1ab06ab1aa86a91aa06a71aa86aa1aa46a91aa06a71aa06a71a986a61a986a51a906a41a946a51a906a41a906a41a8d6a24c0b69f1a8d6a24c0b69f1a8d6a35a896a24c0b69f0c0b69f1a8d6a35a896a24c0b69f0c0b69f0c07301cc07301cc07301da646991a646991a646991a606981a606981a606981a5d6965a54300da5d6965a54300da5d6975a596965a54300da54300da5d6975a596965a54300da54300da486921a486921a4869219cd69159cd6735a4568e4bff68e59cd67359cd69159cd69159cd67359cd6915a392ffda396735a4568e4bff68e59cd68d19cd68c59cd68b5a2868919cd68d19cd68d19cd68c5a3167359cd68b5a2868919cd68b5a2868919cd6881a206881a1d6861a146875a1d6861a186851a146841a0c68219cd6841a106831a086735a0c68219cd6811a006811a006811a0067f59f867d19fd67f59f867e19f467d19f067c19f0665599567b599567b59e12fed9e16655995665599566559ed66559ed66559ed6784bfb678599567b59e12fed9e166559d866559dc676199567619d8665599567719d866559dc676199567419cd67519d067359d067419cd67359d467419cd67519d0673599567259c466559c166f19b8665599566559c967259c466559c466559c166f19b866559c166f19b866559b466c19ac262098826219b466d19b066c19ac66b09882620988262098826219a866a19a866919a466919a0667199866559a0668199c66619956671998665599066419906635988661198d66359886621984661198165f1981660597c65f197965d597165b597965e597565d597165c596d65b6e4,0x2ec,0x6c45b0d6c25b056c05afd6be5af56bc5aed6ba5ae56b65ad96b65ae16b75ad96b55b116c35b096c15b016c45b0d6c25b056c05afd6bf5af96bd5af16bb5ae96b95af96bd5af16bb5ae96b95ad96b65ad96b85add6b65ad96b65ad96b85add6b65ad56b56ed,0x2ee,0x1b256c95b206c72ef,0x6cd1b306cb6f0,0x2f1,0x2f2,0x2f3,0x1b9d6e65b956df5b796dc1b6d6d75b596d75b916d75b596e31b596e25b796d31b4c6d31b556d45b856e05b7d6de5b746dc1b6d6da5b696d95b656d65b616d75b596d31b4c6d31b556d45b4d6d36f4,0x2f5,0x2f6,0x2f7,0x2f8,0x1c0d6fc5c097015be96f91be16f55bcd6f55c016f55bcd6ff5be96f11bc46f11bc96f11bc16fe1bcd6fd5bf16fb5be96f91be16f71bd96f65bcd6f55bd16f35bc46f11bc46f25bc46f05bbd6ef6f9,0x50754195056fa,0x2fb,0x2fc,0x2fd,0x2fe,0x2ff,0x300,0x7635d8d7635d8d7635d8d7625d897625d8d7635d8d7635d8d7635d8d7635d8d7635d8d7635d897625d897625d89762702,0x76a5da976a5da976a5da97695da57695da976a5da976a5da976a5da976a5da976a5da976a5da57695da57695da5769703,0x7735dcd7735dc97725dc97725dc97725dcd7735dcd7735dcd7735dc97725dc97725dc97725dc97725dc97725dc9772704,0x77a5de977a5de57795de57795de57795de977a5de977a5de977a5de57795de57795de57795de57795de57795de5779705,0x7855e157855e117845e117845e117845e157855e157855e157855e117845e117845e117845e117845e117845e11784706]
def nd25 : Array Nat := #[0x78c5e3178c5e3178c5e3178b5e2d78b5e3178c5e3178c5e3178c5e3178c5e3178c5e3178c5e2d78b5e2d78b5e2d78b707,0x7935e4d7935e4d7935e4d7925e497925e4d7935e4d7935e4d7935e4d7935e4d7935e4d7935e497925e497925e49792708,0x79b5e6d79b5e6979a5e6979a5e6979a5e6d79b5e6d79b5e6d79b5e6979a5e6979a5e6979a5e6979a5e6979a5e6979a709,0x1e7579c4c8a7981e5d79d5e7579c5e713229e607974c8a7981e5d7961e587961e557944c867901e3d7955e557945e513219e4078f4c867901e3d78e5e353209e257881e3978e5e3578d4c827895e203209e257881e1d78654cd31f9e087875e1d7865e195334c7e78214cd31f9e087815e0177f1df87815e057805e0177f1dfc77e1df877d5df177b4c7a7771df577d5df177c5ded31e9ddc77b4c7a7771dd87761dd87755dd131d9dc176f1dd57755dd17744c767705dbc31d9dc176f1db976d5db176b0c7276e5db976d5db576c5dac31c9db176b0c727675d997655d9031b9d9d7675d997665d957640c6e7655d9031b9d8175f5d7975d5d7075b5d697591d607605d7d7605d7d75e5d7975d5d7575c1d7075b5d6d75a5d697591d647581d607575d597555d517575d597555d517575d597555d517535d117435d497515d4174f5ca57535d4d7445d117435d0d7525d457505d3d7295d497515d4174f5ca574e5d3574c5d2d74e5d3574c5d2d74e5d3574c5d2d74a1d2474a1d2474a1d247295d287491d287491d287491d287491d287491ca574a1d247295d217475d187451d217485d1d7475d187451d187451d117435d087411d0073f1ca57445d117435d0d7421d047401cfc7295d087411d0073f1ca573e5cf573c1cec73e5cf973d5cf573c1cec73c1cec73a1ce473a1ce87391ce47385cdd7365cd57385cdd7365cd57385cdd7365cd57345c7d7245ccd7325cc57305c7d7345cd171f5c7d7245c917335cc97315cc171f5ccd7325cc57305c7d72f1cb872f1cb872f1cb871f5cbc72e1cbc72e1cbc72e1cbc72e1cbc72e1c7d72f1cb871f5cb572c5cad72a5cb572c5cad72a5cb572c5cad72a5c3870c1c3870c1ca570e1c3070e1c3070e1c307295c3870c1ca57111c3c7111c3c71f5c4470f1c4470f1c4470f1c7d7111c3c71f5ca17275c987251ca17285c9d7275c987251c987251c7d7245c8c7221c847201c7d71f5c7d7245c917231c887211c8071f5c8c7221c847201c7d71e1c7471e1c7871d1c7471c5c6d71a1c6471c5c7171b5c6d71a1c6471a1c647181c5c7161c607181c5c7171c587161c547141c4c7151c547141c507131c4c7125c457105c3d70e5c3570c5c497125c457115c417105c3d70f5c3970e5c3570d5c3170c701,0x1e857a15e857a15e857a15e857a15e857a15e857a15e857a15e857a15e857a170b,0x30c,0x1e857a15e857a15e857a15e857a15e857a15e857a15e857a15e857a15e857a170d,0x1ef17bb4c9a7b95ee17a85eb97ad5eb17c25eb97ad5eb17c11f04325cc927aa5ea57a85f007bf1ef87be1ef57a85ef17bb4c9a7b95ee17a85edc7b65ed47b45ecd7b05ec97b15ec17af5eb17ae5eb57ac4c973249ea97a95ea17a75e9d7a65e947a25e917a35e89324cc9379f70a,0x1f117a770e,0x7c85f1d7c670f,0x1f047cc5f2d7ca710,0x311,0x312,0x1f497d15ef87d0713,0x314,0x315,0x316,0x317,0x1f697da5f647d8318,0x319,0x31a,0x31b,0x1fa87ea1fa87e91fa47e91fa07e81fa07e71f9c7e71f987e61f987e61f987e61f947e51f947e41f907e41f8c7e31f8c7e21f887e21f847e11f847e11f847e131c,0x31d,0x7ef1fb87ed71e,0x204080f023980e6034255603180b1fc47f102392555fc480a202408c602180709518066014803200c804200c25442318031ff18025ff18015ff17fb5ff17fb60007ff1ff97fd5ff17fb5fe97f95fe07f71fd87f51fd07f31fc97f171f,0x320,0x8156051813721,0x322,0x323,0x20e082c60dd82c60d982c60ad83520d081560cd82c60ad83220c4830604d82f20b882d4afd82c60ad82a20a48284af582720908242098825209081560902bf608d8226085820607c81e207481c206881b206881a0af58136069819724,0x2148851614184f610984e213484d213184b212884261248492121847611984521108432109841210083f60f883d60ec83b20ec83c60ec0aa60e883a20e86f260e8163725]
def nd26 : Array Nat := #[0x326,0x327,0x328,0x21c487021c053361bc859216485921b986d61b086b21ac77061a886821a086821a5868219d866619585c6171864618c8622171861618185f217885d217185b2169859729,0x87561d187372a,0x32b,0x32c,0x227489d227489d227489d227489d227489d227489d227489d227489d227489d32e,0x2280887627d8876279347e26d887621989a22688756265898225d88762198952258895225189322488922245889624088f621d886623888d61ec88c222888a222c88a21d588a222587c222187c21f0887621988562108836208881220187f21f887d61f187c61f187b61e987972d,0x228887972f,0x330,0x331,0x332,0x333,0x334,0x335,0x336,0x337,0x8fe63f98fe63f98fe63f98fe63f98fe63f98fe63f98fe63f98fe63f98fe63f98fd63f58fd63f58fd63f58fd63f58fd739,0x906641990664199066419906641990664159056415905641590564159056415905641590564159056415905641590573a,0x90f643d90f643d90f643d90f643d90f643d90f643d90f643d90f643d90f643d90e643990e643990e643990e643990e73b,0x93264c993264c993264c993264c993264c593164c593164c593164c593164c593164c593164c593164c593164c593173c,0x948652194865219486521947651d947652194865219486521948652194865219486521948651d947651d947651d94773d,0x95065419506541950654194f653d94f654195065419506541950654195065419506541950653d94f653d94f653d94f73e,0x95a656995a656595965659596565959656995a656995a656995a65659596565959656595965659596565959656595973f,0x9616585961658196065819606581960658596165859616585961658196065819606581960658196065819606581960740,0x98025fc97e25f497c25ec980260097f25fc97e25f897d25f097b25f497c25ec97a25e497825dc97625d497a25e897925e497825e097725d897525dc97625d497425cc97225c497025bc97425d097325cc97225c897125c096f25c497025bc96e25b496c25ac96a25a496e25b896d25b496c25b096b25a896925ac96a25a4968259c966259496825a0967259c9662598965259496447859636588359a57896465911e14785963658d9620d6695e2588359a57895d657195b4d62957255895d657595c657195b656d358a55c9560d629572558955655195365489510d5e95565559546551953654d9522544357a5489510d5e94d653194b65289490d5a94d653594c653194b652d94a2524356a5289490d5a94565119436509941250193f64f893d64f193b24e993964e093725159446515944650d94365099426504941250194064fd93f64f893e24f593d64f193c64ec93b24e993a64e593964e093824dc93724d993564d19330d5692f24d993664d593564d193464cc355a4bc9330d5692f24b992d64b092b24a892924b992e64b592d64b092b24a892924b092b24a892924a19276498925249092324a1928649d92764989252490923249892524909232489921648091f247891d24899226485921648091f247891d248091f247891d247191b646891924619176458915245091c646d91c646d91a246891924649186461917645d91624589152454914245091364499116440354a430913644d912644991164459100d5290c2440354a43090b642990964209070d4e90b642d90a64299096425908241c353a4209070d4e903640990164008ff0d4a903640d9026409901640590023fc352a4008ff0d4a8fb63e98f963e18f723d98f563d18f363c88f163c18ef63b98ed09888fb63e98fb63e98f963e58f863e18f723dc8f663d58f663d58f463d18f363cd8f223c88f163c18f163c18ef63bd8ee63b98ed23b426209888ec63ad8ea23a48e8239c8ec63b18eb63ad8ea23a48e8239c8ea23a48e8239c8e663958e4238c8e223848e663998e563958e4238c8e223848e4238c8e223848e0637d8de63758dc236c8da23648d823818e0637d8df63798dd63798dd63708dc236c8db23688da23648d923608d8235d8d663548d4234c8d2235d8d763598d663548d4234c8d223548d4234c8d223448d0233c8ce23358cc232c8d123408d123408cf233c8ce23388cd63358cc23308cb232c8ca63258c8231c8c623148c423298c963298c963208c8231c8c723188c623148c523108c4230d8c263058c062fd8be62f58bc630d8c363098c163018c263058c062fd8bf62f98be62f58bd62f18bc738,0x341,0x342,0x343,0x9922648992264499126449902640990263c98f263c98e263898e263498d263498c263098c262c98b262c98a262898a2624988262498926209881a2868a1a28987261c98719d867619d867419d067419b866e19b866d098866d19b426209888c7231c8c7344,0x26919a366899a1668199f667199c666999a667999a667999e666999a667199d266999c666c994665199466519946651994665199466699992660998265d9966655994745]
def nd27 : Array Nat := #[0x98c262346,0x9a926a49a926a09a826a09902640990269c9a7269c9a626989a6263498d263498c263098c262c98b262c98a262898a2624988262498926209881a2868a1a28987261c98719d867619d867419d067419b866e19b866d098866d19b426209888c7231c8c7344,0x347,0x348,0x349,0x34a,0x34b,0x34c,0x34d,0x9c027009c0264499126449bf26fc9bf26f89be26f89bd26f09bd26f49bc26f09bb26ec9bb26e89ba26e89b926e49b91a599b81a5969666e09b826249b7262098926249b726dc988262068a1a2868a261c987261c67619d867619d067419d09b659b89b666d966e19b866d19b026219b466d19b066c098826226d49b526d49b426d09b4231c8c7231c9b366cd9b374e,0x270d9c274f,0x350,0x351,0x27209c7352,0x353,0x354,0x9dc27709dc276c9db276c9da27689da27649d927649d8275c9d827609d7275c9d627589d627549d527549d427509d4274c9d3274c9d227489d227449d127449d027409d0273c9cf273c9ce27389ce27349cc27349cd27309cc355,0x277984c46c50be756,0x81d20767a59e8481d207482c207679c9e627942076790205278c203278820227889e227889e208009e107f81fd27809e027809e027801fb07e89df277c9df277c9df4b6,0x357,0x358,0x359,0x35a,0x35b,0x35c,0x2818a0527f8a04280ca022800a002800a2d28b4a2c28b0a2b28aca2a28a4a2a28a4a28289ca262898a2628a0a272898a262898a252890a252890a23288ca222888a212884a20287ca1e2878a1e2880a1f2878a1e2878a0b682da1d686da1d6871a1b682da1a2864a18282da172858a152850a132848a0b6844a10283ca0e2834a0c282da0a2824a08281ca066815a04680da026805a016801a0068019ff67f99fd67f19fb67e99f967e19f775d,0x35e,0x35f,0xa42691da466915a44690da426905a4068fda3e68f9a3d68f1a3b68e9a3968e1a3768cda3368d9a3568d1a3368c8a316909a476919a456911a436909a42691da466915a44690da426905a416901a4068fda3e68f9a3d68f1a3b68e9a3f68f9a3e68f5a3c68eda3a68e5a3968e1a3868dda3368cda3668d5a3468cda3768cda3368d9a3568d1a3368c8a3228c5a31760,0x361,0xa4a362,0x363]
def nd28 : Array Nat := #[0x364,0x365,0x366,0x367,0x368,0x369,0xa5636a,0x36b,0x36c,0x36d,0x36e,0x36f,0x370,0x2999a7269c5a7069bda6e6999a666989a6d69b1a6c6989a6b6989a626999a6a2989a6469a5a686991a68699da646991a666991a652991a632989a612984a60697da5e771,0x372,0x29d9a75773,0x374,0x375,0x376,0x377,0x378,0x379,0x37a,0x37b,0x37c,0x37d,0x37e,0x37f,0x380,0x381,0x382,0x383]
def nd29 : Array Nat := #[0x384,0x385,0x386,0x387,0x388,0x389,0x38a,0xaa72a98aa52a90aa32a8caa32a88aa22a84aa12a80aa02a7ca9f2a7ca9f2a7ca9f2a7ca9f2a78a9e2a74a9d2a70a9c2a6ca9a2a68a9a2a68a9b2a68a9a2a68a9a284ca122834a99681ca9878b,0x38c,0x38d,0x38e,0x2996ab5aac78f,0x390,0x391,0x392,0x393,0x394,0x395,0x396,0xab86addab6797,0x1f04ab95f2d7ca710,0x398,0x399,0x39a,0x39b,0x39c,0x39d,0x39e,0x39f,0x3a0,0x1f497d15ef8ac3713,0x3a1]
def nd30 : Array Nat := #[0x3a2,0x2b70adb2b68ad92b1cac72b1cac72b60ad72b58ad32b54ad42b4cad32b4cad32b48ad12b40acd2b3cace2b34acd2b34acd282dacc6b2daca6b25ac96b25ac96b21ac77a3,0x3a4,0x2b80adf7a5,0x3a6,0x3a7,0x2bc8af12bc0aef2b905336b90ae42bb8aed2bb0aeb2bacaeb2bacaeb2bacaeb2ba8ae92ba0ae62b9cae62b983086b98a122834ae5681cae47a8,0x3a9,0x3aa,0x3ab,0x3ac,0x3ad,0x3ae,0x3af,0x3b0,0x3b1,0x3b2,0x3b3,0x3b4,0x3b5,0x3b6,0x3b7,0x3b8,0x3b9,0x3ba,0x3bb,0x3bc,0x3bd,0x3be,0x3bf,0x3c0,0x3c1]
def nd31 : Array Nat := #[0x3c2,0x3c3,0x3c4,0x3c5,0x3c6,0x3c7,0x3c8,0x3c9,0x3ca,0x3cb,0x3cc,0x3cd,0x3ce,0x3cf,0x3d0,0x3d1,0x3d2,0x3d3,0x3d4,0x3d5,0x3d6]
def ndTab : Array (Array Nat) := #[nd0,nd1,nd2,nd3,nd4,nd5,nd6,nd7,nd8,nd9,nd10,nd11,nd12,nd13,nd14,nd15,nd16,nd17,nd18,nd19,nd20,nd21,nd22,nd23,nd24,nd25,nd26,nd27,nd28,nd29,nd30,nd31]
def nd (i : Nat) : Nat := ((ndTab[i/32]?).getD #[])[i % 32]?.getD 0
def top0 : Array Nat := #[0,0x1780a401680560098052013804a0008046010c03e00e8036000803200b804400a8026008801e0068016004c00e000800a001c002,0x25405b015c02a80e204e813604c80d6046812e04a816c05700aa0388126048811e035811a08701160448210043810a04180d604081f007c01ec07a01e403f80fa03d81d402e00f202e00ee07201c403a80e603880de03680d6034c0ce05700aa03280c6030817c02f80ba02d816c05a00b202b815c02a80a6028809e026c104040009602480f4023808a0218082020807e01e80d803500d001d807201bc0c101a80b801980b002c0062,0x7cc0b4815c02a80e20a182ce04c81a204682ca0b182c20af87a80ae82b60ac815c02a80e20ab82aa0a981a204682a20a7829a0a582921db028e057028a04280e20a1828209f827a09d827209b826a099c26202e06a01a7025e09686901a30256095825303b81c8093824a0918628090823e08e8236182023208b822a089822605700aa088821e0868216084820e082c206081820208081fe07e81fa07d81f207b81eb07981e607881d605700aa07481ce07281c707081bf06e81a2067819b06581960ec03ac0eb03a80e9019206383980e5018a062818706081820d303480d1017e05ec33805d817205b816a059c162058815e057815b0b902e00b702dc0558152053c14b09c0146050c13e,0x3fe0fe815c02a80e204d813201680560fd83f20e983ee0fa83e60f883df05700aa03883da0f5c3d20f383ca0f183c20e4c3930efc3bf00f83ba0ed810e04281060ec83af0ea83a60e8c0ee0e780360e683960e4c38f0e283870e0837e0de83760dc836e0da83670d8835e0d5c30b0d5c35a0c8c30b0d5c3520d382ef007801e0d282db0d1c8b80d088b00cf833b0cdc3330cbc8980ca83260c8c31f0b6c31b0c583120c382e70c2c3070c082ff0be82f60bcc2ef0ba82e70b882df0b6c7d90b5c7d1,0x41e106c0e2106c41b105c3d2104c407103c40a101c403,0x423108c423108c423108c423108c423108c423108c423108c423108c423108c423108c423108c423108c423108c423108c423108c423108c423108c423108c423108c423108c423108c423108c423108c423108c423108c423108c423108c423108c9c127349d1108c4232704423108c9cd2744423108c423108c423108c9c1108c9d1108c423108c9c1108c42327049cd108c423108c9c1108c9c82714423108c423108c9c1108c423108c4232704423,0x326004e184860e182860618085fe31f0c7817e85f617c84c2012800217b85ea17985e217785da12b85d617484a617385ca17185af17085be169c5a716ec5b616c85af16bc5aa169c4c7169c4a630405a2167859a00f859616483ba163858a09e83b2161858315f857a15d857315bc26e09a856a0ea852b0e9848f159c562157855a2ed0556154854e09582560958b9c2e6054b151c5420e7853e00d800214e853714dc39a14c852e0e5852b14ac526148842b10ac42b2d8051e146851a1458512122c50e142850614084fe2ce44fa13dc4f313b84eb12cc4e613884de13684d6134c4ce1328ae912cc4c72b844c212f8457000844f12e84b610fcac112cc4ae12a843f12984a2127849a125c492122c437123c48b29e0486120ca6c11f847a11c8472296047710dc47211c846e11a846611984372900462117ca3428c044f11684570008452113c44b2830446110843f10e89f910dc43210bc42b2764427,0x187c612187c60a1818602187c4c2187c002187c61f179861f187c61f12b861f187c4a6187c61f171861f191c61f191c647187c5b6187c61f187c61f191c61f191c4a600f8596187c3ba187c58a09e861f187c61f187c61f187c61f187c61f187c56a187c61f0e9861f187c61f187c53e187c002187c61f187c39a187c61f187c61f187c617185c617185c61718ac50a18fc643187c4fa187c61f18fc61f187c4be18ac627187c61f187cca9335463f188c61f32a463b187c61f18ac636187c61f11c8633186ccc5328447218cc61b18b861f187c62b189c61f187c61f2830623187cca9186cca1185c617,0x64b192c64b192c64b192c64b192c64b192c64b192c64b192c64b192ccf433c064b192c64b192c64b192c64b192ccf0192c64b192c64b192ccec192c64b339464b192cce9192c64b192cce5192c64b,0x6aa1a98c10168859e166803e1658592163827a0ec8586193c57e193c576193c64f09b864f193c64f193cd781a886561a7869a1a586961a3c68f1a4868f193c6561a3c68a1a1c64f0958256095864f1a1c53e193c002193c682198c67e19e866e19ccd4919d8673193c66e196cd3834d064f34c0d2d196c42734b466a199866318d865f193c65b345464f1958d0d193c46a193cd0d194c64f,0x76e39a0e641da876616887621aec75e1d6875603887521d386bb1aec27a1aec6bb09b826a1cdce381d287461d0873f1aec73f1aec73b09582561cdc0ee1cc872f1ca87261aec7221c7c6bb1c6c7171c4871237e070e1bfc70a1c0c7061bec6af1c0c6bb1bfc4921bec6af1abc6f71bc8dd51bb86eb1aec6e61b8c6af37046de1abc6da1b686af1b5c46a05786d31acc6ce1b2c6c61b086af1afc6af1aec6b71acc6af,0xc10109c427109c03e1658427109c27a109c427109c427109c427109c427109c427109c427109c4271dec427095877f09584271dec53e109c002109c65b1278777109c42734b465b109cd2d1dcc4273a046361dcc42711c8e79196c47239e446a109ce7539c4427,0x1dec77b,0xec83b20ec83b2068e1a3868e1a3864a192864a19287a21e7879e1e7879b1e58eb03ac0eb01e48eb03ac0eb03ab0eac3ab0eac3ab0eac1e3878e1e3878e3a8078a3a80e943a507861e18e941e0ce943a50e91,0x484120c482081e206881647e081220391ec47a080a20191d420087fe1fe87f61fc87ee1fa87e61f887df3cd07d61f48f283c10f041f387ca3c70f183c507c61f08f093c10f041ef87bb3bb47b63b40ed01ec87af1e387a71ea87a73b40ecd,0x1238208d234208c823208c82348c0823208c82348b4823208c823208c823208c823208c823208c823208c823208d228208c823208c823208d224208d221208c823208c823208c823208c823208d21d208d215,0x208d234208c823208c823208c823208c823208c823208c823208c823208d215,0x2a28a865cd17302008a8229f8a7a5c8171c29d971429c8a6e29a83722998a622978a5a2958a522938a4a1fe835e291ca4228f8a3b28d8a3228b8a2a28987ee2888a1e286c3a62858a122828a022818a0227f89fa27d964c27c89ee590162458f07e627a89e658300be25ec97b58b1628589162027889de276960c02f89d727489d227289ce27289c727089be26e89b626cc9ae258c96326a89a7268d5a8569099e2668996264898e0cf898a261c98225f897b25d897225b955825ac96b258c966258c963256c95f256d53854e08562558942254894e4fe15202529518251894224f893a24d88e724c892e244892a239d4d82498922247c91a245c912243c90a024890a02488560c58312496090624088ff23e88f70c088f223b88ea239c8e2237c8d6234c8ce232c8c7230c8ba22f88ba50a078e02088b61e9d4281e3808222cc85622b88aa22988a220dd3f84fd53f1227887721cd3e94f9089a4f713702258893223888a4d80882217c7a74df087f4dd53704db487b21dd36021cd35921b886b2198862217c85b4ce48560be8852213c84220fc8374960833494482e20ad245209d23d,0x2cc8b2e2ca8b2608c8a932c88b1e2c68a930898a932948a4e2a4cb160878a930858a932a4ca9328d8a2a0688a932c48a930e98a932a4cb0e2bc82062c2c2022adcb062b7cb032b7cafe07e8a932abc1f62abca932abc1e62adcafa2bdcadf2bdcadf2bc8a932bb8a8f2b7caeb56a099e2668ae726381d22a4ca932a4cae22abca932abca9325d97b55ed41a22a4ca8f2b7cadf2b68a972a5cad75e90aa72a9cad21c28a932b38aab2a9caa72afcacb2b2c4922a4cabf2afcacb2158a972a5c47211c847211c8ac61bc8a932aacaa71b98a932a4ca932aacaa72b08a932afca932a4cabf1b68a932a6ca972aec15e2adcab35d0577d5de57742a9c6c22a4ca935dc0aaf2aacaa75d84a932a8d7592a7ca9b2a5ca932a3d741,0x2cdcb372cdcb372cdcb372cdcb372cdcb372cdcb372cdcb372cdcb372cdcb372cdcb372cdcb372cdcb372cdcb372cdcb372cdcb376064b372cdd82d6034b37603580d60a4b372cdcb372cdcb372cdcb372cdcb372cdcb372cdd80d2cdd80d60358296094b372cdcb3760558216084b376084b372cdcb37608581d2cdcb372cdcb376064b372cdd8156034b376035245,0xbe22eecbde2f6cb8f2bc8bd72e0cbd22eacba72f38bcb2f1cb632d7cbc32efcb5b2eecbb72eccbae2ddcbab2e9d8f92dad8f563c58ed2e8d8e52ced8e163758d963558d16334b9e2d5cb532e68b972e4cb8f2e2cb872e0d8a92df8b7a2ddcb47626583d6254b736234b6e2dad88161f4b6761d4b632d7d8696194b5b2d5cb5361558516134b4f2d28b4760f4b432cf8b3b,0x34d8d361088d321088d3234b8d2a3178d2634b8d2a3178d263468d163448c5e3488d1a3458d123178d0f3428d0a34183be34183be8550796340a14c33fa1541e58d028530cfe33d8cf233b8cea33e8cf633c8cee33a8ce71ef87be7df0cd67dd0cd23338ce26500cde336df7c3359f743348cce332d940331ccc23308cbe32f8cba32d8cba32d8cb232c8cae32a8cae32a8ca63298c6a3198ca23278c5e323cc6a3198beb318cc5e3168c5a1e38c561e38c563148c523129bb03139ba83129bb0311dba83108c3e3108c3e6d10c3630c8c3a6d10c3630c8c2f30a8c272fc9958308995030799483068c1765019642fd8bf26560bef6540beb6520be7650193d,0x8b70d3b34ecd3b8b622d434ee2d034ecd3b34ee2cc34ee2c834ecd3b34ecd3b34ecf1834ee2c434ee2c18af0d3b34ecd3b8ae0d3b8ab0d3b8ad0d3b8ad0d3b8ad0d3b34ee2b034ecd3b34ee2ac34ee2a88a90d3b34ecd3b34ecd3b34ecd3b34ecd3b34ee29d34ecd3b34ee29d,0x106841a3738dca3738dca36f8dba3718dc336f8dba36dcdb236c87be1ef8d9a3658dae36a8da73688d9f3668d96364cd8f362e6a91e38d871e38d8335d8d7e35ecd76984660d35c8d6e35acd46350cd3f,0xf323cb8cc23ca8f263c88f1e3c6cf1632f8f123c3885639b8f0a3c1ccba3c08efe3be8ef63a5cef33bb8eeb3b98ee33b7ccb23b68cae3b58ed23b38c5e3b2cec63b08ebf3aeceb73ac8ca63ab88563aacc6a3a98c663288ea23a7ce9a3a5cc5e3a4cdd7a930e8fa912a41a8f6a39a8d4e8a3a1878e3a08e3338ace7e39ece76382ce7339baa10a830e6a3998e6238cce5ea7e0ddb396ce57394ce4e392c46a11a8e463908b7e38f8e3a37ace3638cce2e38ace27388ce1e386ce17384e9493838e0b2158e07380a934a4c0dfe37ecdf637c8dee37acde765027d4378a7cc377cddb9f067bc375cdd29ec67ac,0x3d5cfd322e8fcf3f2cf6b1e38f673e1cf633f1cfc23efcfbb3ed8f5f3eccfaf3eacfa63d5cf833e8cf533e7cf9b3e5cf9235d8f4b3dacf8e3cdcf8a3d9cf873e0ec6db1a6c653dfcf7aafc6c59afa6c553cdec51b136c493dd846a3dccf6f3dacf673d8ec2d3d7ec253d68f373d5ec193d4ec11b034f373d3cf4b3cdcf373d1ebfd3d0cf3eafc4f3bafa4f37]
def topTab : Array (Array Nat) := #[top0]
def top (i : Nat) : Nat := ((topTab[i/32]?).getD #[])[i % 32]?.getD 0
def rt0 : Array Nat := #[0,0x34c620d2988348620d1988344620d0988340620cf98833c620ce988338620cd988334620cc988330620cb98832c620ca988328620c9988324620c8988320620c798831c620c6988318620c5988314620c49880781b0,0xf60b13d62c4f50b13d22c4f40b13ce2c4f30b12aa2c4d18b13ca2c4f20b13c62c4f10b13c22c4f00b13be2c4ef0b13ba2c4450b13b82c4860b13b62c4ed0b13b22c4ec0b13ae2c4eb0b13aa2c4cd0b12a42c4ea0b13a62c4e90b13a22c4e80b139e2c4e70b12962c45b8b139a2c4e60b13962c4e50b13922c4e40b138e2c48a8b138c2c4e28b12262c4880b11d42c4e20b13862c4e10b13822c4e00b12a62c4798b137e2c4df0b10b82c4a00b137a2c4de0b11d62c4dd8b13742c4dc8b12122c48e0b10b62c4dc0b136e2c41f8b136c2c4da8b13682c4d98b13642c4d88b13602c4d78b11922c4d70b135a2c42c8b13582c4718b10782c43c8b13562c4d50b13522c4d40b134e2c4060b1184084,0x12c8e04b0380f50e03d2380f40e04ae3812b0e02aa3812a8e03ca3812a0e04a6381290e04a2381280e049e381270e049a380f08e03c0380ef8e0498381258e0494381248e0218381240e048e381230e048a381220e0486381210e0482381200e03ac3811f8e047c3811e8e02a83811e0e0476380a90e04743811c8e029e3811c0e039a3811b8e046c3811a8e02923811a0e0396381198e04643808d0e0462380e48e0460381178e0224381170e045a380358e0458380878e0456381150e0452381140e044e381130e0386380e10e044a381120e0380381118e0444381108e02a6381100e043e3810f0e043a3810e0e04363810d0e04323810c0e042e380570e042c3810a8e027c3810a0e0376380dd0e0426381090e0422380848e04203808f0e041e381070e041a381060e0416381050e0412381040e040e381030e040a381020e01a4381018e0404381008e0400380900e03fe3808c8e03fc380da8e03fa380fe0e0368380fd8e03f4380fc8e0122380fc0e03ee380fb0e0188380fa8e03e8380f98e03e4380f88e03e0380f78e03dc380f68e019e380b60e00de3805d0e00dc3801c0e0264094,0x1500e253e388f50e23d2388f40e23cc388aa8e2348388d18e253c3894e8e25383894d8e25343894c8e25303894b8e23c2388f00e23be3894b0e23ba3894a8e2528388ee0e2526389490e2522388888e2520388420e2336389478e251c388eb8e23ac388ea8e251a388cd0e2518389458e2514389448e2510388cc8e250e389430e250a388a28e2508389418e2504389408e25003893f8e24fc389130e24fa3893e0e24f6388e08e23803893d0e22a63893c8e23283893c0e24ee3893b0e24ea3893a0e24e6388c88e24e4389388e24e0389378e24dc389368e24d8388dc8e2212389358e2238389350e24d2389340e24ce389330e24ca388290e24c8389318e24c4388c58e24c2388ba8e24c0388da8e24be388d40e234e3892f0e24ba388c50e24b83892d8e22ca3884d8e24b4388600e21bc0b4,0xf52a13d2a84f42a13c2a84f02a13bea854aaa13aca853daa1380a85512a14dca8536aa10340f4,0x174aa35d0a8d73aa35cca8d72aa35c8a8d4d2a35c6a8d4c2a35c4a8d70aa35c0a8d4aaa3528a8d6faa35bca8d24aa3526a8d242a3524a8d48aa35baa8d6e2a3520a8d6daa35b4a8d6caa35b0a8d6baa35aca8d6aaa3466a8d192a35a8a8d69aa35a4a8d68aa3510a8d682a3332a8ccc2a359ea8d672a359aa8d43aa3598a8d65aa350ca8d42aa3594a8d64aa3508a8d642a358ea8d632a343ca8d0eaa358aa8d622a3586a8d612a3582a8d602a342ca8d5faa357ca8d5eaa3578a8d5daa3574a8d392a3572a8d5c2a356ea8d5b2a356aa8d5a2a3566a8d592a3562a8cfaaa33e8a8d582a355ea8d572a355aa8d562a3556a8d552a3312a8d54aa3550a8d2e2a354ea8d532a34b6a8d52aa34b4a8d522a312ea8cb7aa319419c,0x6c03c4d00f16be3c5af0f16ba3c5ae0f16b63c5ad0f16b23c5ac0f16ae3c5ab0f16aa3c5aa0f133e3c4cf0f16a63c5a90f16a23c5a80f169e3c5a70f169a3c5a60f16963c5a50f16923c5a40f168e3c4ce8f168c3c5a28f13383c5a20f16863c5a10f16823c5a00f167e3c59f0f167a3c59e0f12b63c59d8f16743c59c8f16703c59b8f13363c59b0f166a3c5478f16683c5998f14783c5468f16643c4cd0f16623c5980f165e3c5970f14763c51d0f14723c5968f15183c5960f15163c5958f16543c5948f15b03c56b8f15ac3c5940f164e3c51a0f14663c5190f15a83c5698f15a43c5930f12363c5688f15103c5680f13323c4cc0f159e3c5670f159a3c5438f15983c5658f150c3c5428f15943c5648f15083c5640f158e3c5630f164a3c5920f16463c5910f16423c5900f163e3c4c80f163c3c58e8f16383c58d8f131c3c58d0f16323c58c0f162e3c58b0f162a3c58a0f16263c5890f16223c5880f161e3c5870f161a3c5860f16163c5850f11b03c5848f16103c4c68f13183c5838f160c3c5828f16083c5818f16043c5808f16003c57f8f15fc3c57e8f15f83c57d8f14063c5008f14003c57d0f15f23c4bb8f14c43c57c0f13163c57b8f15ec3c57a8f15e83c5798f15e43c5308f15e23c5780f15de3c5770f15da3c4fa8f13e83c5760f155c3c5568f15583c5558f15543c52e8f15d63c4c50f13123c5548f15d43c4800f15503c52e0f154e3c5530f14b63c4b28f12d03c5528f14b43c5520f112e3c4b78f1320192,0x3403d5af8f56bc3d5ae8f56b83d5ad8f56b43d5aa0f533e3d4cf0f56a63d5a90f56a23d5a80f569e3d5a70f569a3d5a60f56963d5a50f56923d5a40f568e3d4ce8f568c3d5a28f53383d5a20f56863d5a10f56823d5a00f567e3d59f0f567a3d59e0f52b63d59d8f53363d59b0f566a3d5478f56683d5998f54783d5468f56643d4cd0f56623d5980f565e3d5970f54763d51d0f54723d5968f55183d5960f55163d5958f56543d5948f55103d5680f53323d4cc0f559e3d5670f559a3d5438f55983d5658f550c3d5428f55943d5648f55083d5640f558e3d5630f53203d58f0f563a3d58e0f56363d58d0f56303d58b8f562a3d58a0f56123d5840f531a3d4c60f560e3d5830f560a3d5820f56063d5810f56023d5800f55fe3d57f0f54c43d57c0f53163d57b8f55ec3d57a8f55e83d5798f55e43d5308f55e23d5780f55de3d5770f55543d52e8f55d63d4c50f53123d5548f55d43d4800f55503d52e0f554e3d5530f54b63d4b40f554a3d5520f52181b2,0x1ba3616e6d85b93616a8d84cfb6133cd85a9b6169ad85a4b61690d84ceb6168cd84ce361688d85a136167ad85b8b616e0d85b7b616dcd85b6b616d8d85b5b616d4d85b4b615b2d856ab615a4d84ccb61330d8543b61508d85b43616ced85b3361318d85b2b61602d85b23616c6d85b136155cd84c4b614b8d852d3610b418a,0x1c68f77183dd9d0f76723dd9c0f766e3dccd8f766c3dd9a8f76683dd1e0f751a3dd990f73343dd988f76603dd978f765c3dd1d8f74743dd1c8f76583dd958f76543ddb88f77163ddc50f77123ddc40f76dc3ddb68f76d83ddb58f770e3ddb50f770c3ddc28f73063dd940f764e3dd1a0f74663dd190f75a83dd930f72363dd680f73323dccc0f759a3ddc20f77063ddc10f77023ddc00f76fe3ddbf0f76fa3ddbe0f76f63ddbd0f75fa3dd7e0f75f63dd018f74023dd000f75f43dd7c8f72ee3dd310f75f03dcc58f75ee3dd7b0f75ea3dd788f76f23ddbc0f76ee3ddbb0f76ea3dd768f75d63dcc50f73123dc800f715c186,0x12313d7324f5cc13d48a4f52213d6724f52193d4844f52093d4804f4eb13d47e4f5cb93d47c4f51e93d2a84f51e13d4764f4a913d4744f51c93d4704f5cb13d72a4f4e693d46e4f51b13d46a4f4a493d4684f4e593d4664f51913d2344f51893d7284f4e493d4604f51793d2244f51713d45a4f43593d4584f48793d4164f50513d7264f5c913d4124f50413d40e4f50313d40a4f50213d1a44f50193d4044f50093d4004f49013d3fe4f48c93d3fc4f4da93d7224f4fe93d3f84f4fd93d3f44f4fc93d1224f4fc13d3ee4f5c813d71e4f4fb13d1884f57693d3ea4f4fa13d3e64f5c713d3e44f4f893d3e04f4f713d3da4f4b613d0de4f45d13d0dc4f41c13d174096,0x19d39a672e699c39a66ee68cdb9a66ce699ab9a668e691e39a51ae699939a334e6998b9a660e6997b9a65ce691db9a474e691cb9a658e6995b9a654e699439a64ee691a39a466e691939a5a8e699339a236e696839a332e68cc39a59ae697eb9a5f8e697db9a406e6900b9a400e697d39a5f2e68bbb9a4c4e697c39a316e697bb9a5ece697ab9a5e8e6979b9a5e2e697839a5dee6976b9a5d6e68c539a312e688039a0ec196,0x670e6d7839b008596,0x1cd8887342209e8880aa221d30881ee2207b088034221d28886c22209a0880802207888821622011888044220270881c0221d208874622052888162221d10887422203d088740221cf88819c220da8883682204e08873c220c40880c82201e8882d6220150880b2221ce8880b02204308804222004888040221ce0880022209b0880bc001,0x7881b1e186c7841b1e086c7801b1df86c77c1b1de86c0ba1b1de06c7761b00e86c2841b1dd06c7721b0e206c3841b0e006c2a61b1dc06c1e61b1db86c0b81b02d86c76c1b1da86c7681b1d986c7641b1d886c7601b09686c75e1b1d706c75a1b1d606c0b41b1d586c7541b1d486c7501b00b86c0f41b0db86c4121b10106c3681b04e06c74e1b0d786c0b21b01e06c3541b02486c0d8081,0x1ed14c32e531ec94c7b0531eb94c7ac531ea94c7a8530cb14c7a6531e914c7a2531e814c79e531e714c79a5313c94c328530c994c324531e614c796531e514c7925310b14c42a530c894c7905319194c644530c814c638530c794c31c531e394c62e5318b14c78c530c694c318531e294c400530c594c5e65317794c314530c494c0bc191,0x32ef6decbdb7aaf6dea3db32cf6de6bdb4f2f6cca3db326f6cc93db322f6cc83db31ef6cc6bdb318f6cc5bdb314f6cc4bdb0481b1,0x7743ea2a0fa8a63ea290fa7723ea288fa8a03e8e20fa89e3ea270fa89a3ea260fa8963ea250fa4fe3e93f0fa44c3e93e8fa4f83ea248fa8903e93d8fa3863ea238fa3843e8e08fa3803ea230fa4f43e8a98fa79a3e93c8fa3283e8c98fa3243e9dc0fa88a3e93c0fa4ee3ea220fa8863ea210fa8823ea200fa1e63ea1f8fa87c3ea1e8fa8783ea1d8fa8743ea1c8fa8703ea1b8fa86c3e9db8fa86a3ea1a0fa8663e8df8fa37c3e82e0fa8643ea188fa8603ea178fa2803ea170fa85a3ea160fa8563ea150fa37a3ea148fa8503e8de0fa5783ea138fa4ec3e93a8fa84c3e93a0fa1d63e95b8fa4e23e9380fa5683e9588fa2b83e9510fa4de3e9370fa3763ea128fa3743e9368fa4d83e8dc8fa2123e9358fa8483e88e0fa4d23e9340fa4ce3ea118fa8443ea108fa4cc3ea100fa4ca3e8290fa83e3ea0f0fa0d03ea0e8fa8383ea0d8fa8343ea0c8fa8303e8dc0fa7063e9c10fa82e3ea0b0fa82a3ea0a0fa8263ea090fa8223e8db8fa8203ea078fa81c3ea068fa07e3e9bf8fa6fc3e9be0fa0ca3ea060fa8163ea050fa2f23e9048fa36c3e9010fa8123ea040fa4c83e9318fa4c43e8c58fa5ec3ea038fa4c23e8ba8fa4c03e8da8fa80c3ea028fa3683e8d98fa8083ea018fa3643ea010fa8023e84e0fa8003e9ff8fa7fc3e9fe8fa7f83e9d38fa3623e8d80fa35e3e9fd8fa7f43e9fc8fa7f03e9fb8fa7ec3e9fa8fa7e83e9f98fa1923e9bb0fa7e43e9f88fa7e03e9f78fa7dc3e8738fa7da3e9f60fa7d63e8d70fa35a3e82c8fa7d43e9f48fa7d03e8d60fa1c63e81e0fa7ce3e9f30fa7ca3e9f20fa2c63e9f18fa0903e9f10fa7c23e83a8fa3563e9f00fa3543e9ef8fa3523e9ef0fa0fe3e9ee8fa4be3e8d40fa34e3e9ee0fa4bc3e8060fa4ba3e8c50fa5d43e92d8fa2ca3e84d8fa4b43e8b78fa3c0085,0x8e115637c558dd15515c5545515514c557a1155e7c5579d1551445544f155134554f7154e1c5538515512c55449154e045544715511455443154a9c5579b154c9c558db155dc455799155e5c55889155e5455793156364558d71551045543f1550f45543b15561c5558515560c55439156354554371550d4558511550cc554311550bc5515d1550b45542b1555ec555791555dc558d31549f4558d11550a4555731555c4555671555945554515537455377154dd4554db15509c5542515508c5521315633c554d71550845523d15507c554d315611c558451550745541b155064558cd15632c558c915505c5541515631c55727155c94554131563145541115503c5540d15502c55409154694555f715501c5540515500c554011557cc552ef15490455811154ffc552331557a4555e7155784555df15630c553fd154dac553fb154fe4553f7154fd4553f315448c553f1154fbc558c11562fc558bd1562ec558b91562dc55721155c7c558b5154fb455189154fac553e91555745555b155564553e7154f94553e3154f84553df154f74558b3155efc553db154b64558b11545d4558af1545c4557bb1562b45507115553c5554d15552455280095,0x4ff1c53f47144d1c53ec714f91c624c718911c53dc713871c623c713851c4e0c713811c6234714f51c4a9c7179b1c53cc713291c4c9c713251c622c714f11c53bc718891c621c718851c53b4714eb1c6134714e91c539c713231c639c714e51c55bc714e31c5384715631c5514714df1c5374714db1c5364713731c484c718491c5354714d31c5344714cf1c5334718411c532c710a51c60f4718111c5324714c71c5314713171c57bc715ed1c530c712eb1c53047180d1c6394718051c5eec714bf1c4d447134f1c5ee4714bd1c5554714bb1c4c54714b91c52dc712cb1c44dc711480b5,0x24847491f1d2474742791d2364748d71d10fc7443b1d246c749191d077c749171d09fc741dd1d2354744351d10c47415d1d10ac741db1d2344741d71d2454742171d244c740471d09bc749111d09c4740451d1374743771d0dd4744db1d1094742131d08f4740b71d134c744191d243c7490d1d06347490b1d24247418b1d1c7c748b51d0624743e91d241c749051d240c749011d23fc741a11d0b6c740511d0384740e71d23f4748fb1d02247404f1d0f94743551d0f7c748f91d067c740fd1d05e4748f71d061c747bb1d22b4740191d23d4748f31d23c4740831d23bc748ed1d23ac7414c01d,0x9700925b824546090998247680909902496c0925a824968090748249660925902463e0905f8249620925802495e090be0241ca091d802495c090ab8242f60900c024542092568249580907102475e09033824956092550241c2092548241c0091d68247580902d0249500904082494e092530241be0906c8240cc092528249480906f0241b009001024946091d4024748091d18249440905a0249420905982494009026024162091d10247420924f8241600924f02402e0924e82402a0924e0249360924d0243700924c8241ac090db82407e0924c0244140924b8241a8091038241a40924b024232091d002473e0904a024126090b982405c090da824368090488241200905682492a091ff02473c090c402474e090d7824196090648242d60924a0240540904c8240b2092498240780902382490e0906302471e09062024904092400241a0090140243de0923e02419e0903f0241860900602473a0907f0240b00924902410c09047024130090108248ee09046824096091ce0241fa0900082417a090028241180903082492209017824248003,0x9912e5db4b976b2e5da4b998f2e5d94b99672e6634b99652e58fcb998b2e6624b97612e661cb995d2e6614b92af2e58e4b92f72e5d74b97592e660cb994b2e5d44b99812e5d14b993f2e4584b997f2e64dcb98372e4dc4b997d2e4dbcb997b2e41fcb99792e6324b94152e6314b940f2e502cb91a52e6044b92332e630cb93fd2e4dacb93fb2e4da4b93f52e448cb99772e4484b98bf2e65d4b974f2e5fbcb971f2e4f7cb98f92e5eecb90f8083,0x542096568259580947102575e09433825956096550251c20947002575a095d60250b40966602575409651825750095d2025996095d18251680945982594009458825744096650257420945802502e0964e82573c094c402574e094d7825992094b5825054095f58250b20941e02573a0947f02510c0963b8257380947e8250b800b,0x27915a9e256a4e15a9e05686e15a83a56a0e15a1b656a7795a93456a7715a1b456a0d95a70656a0b95a1ae56a4c95a9da56a7615a1ac56a7595a2585686a95a824568db95a6fc5683295a07c56a4c15a9d456a4b95a9d25686a15a9d0568bc15a1a65690495a5f65690115a2ee5680315a9ce56a4b15a9cc56a0415a80e569d015a9ca569cf95a12856a7215a12656a7195a19c568b995a05c568da95a3fa568da15a806568d915a9c45684e15a15a5686695a9c2569cf15a9c0568c415a9be56a6f15a0c856a6e95a9b85686515a6ec56a6d95a9b4568b595a9b256a4a15a05456a6c15a9ae568b215a1485684c95a052569f615a7cc56a6b15a9aa56a6a15a90656a4115a90056a3f95a1a0568b695a05056a6995a0e65684f15a04e568f915a35456a6915a0925683e95a9a25688115a7ba5683015a73a5687f15a9a056a3d15a0b056a4915a10c56a3c15a1305682095a8ee56a6795a18456a6715a13a5687315a09656a6695a7385687e95a9225683195a21c007,0x92b3cc66cf37ff3cdff4f31993ce70cf373d3ce814f33113ce6fcf30c93ce80cf37f93cdd3cf33633ccd84f335f3cdfdcf307b3ce804f31973ce7fcf37ef3cdfb4f37eb3cc64cf36ed3ce6dcf39933ce6d4f32d73ce7f4f39b33ce7ecf31c93cc154f39b13cc524f30533cdf64f37d73ccd74f335b3cc2ccf37d53cdf4cf33593cc71cf30793cdf34f39f93ce6b4f33573ce6acf39073ce7dcf30e73ccd54f33533cc24cf39f53ce7ccf31873cdeecf33513ccd3cf30193cdcecf31fd3ce684f39f13cc57cf38ef3ce66cf39ef3ce7b4f39eb3ce3acf39e93cc0a4f314000f]
def rtTab : Array (Array Nat) := #[rt0]
def rt (i : Nat) : Nat := ((rtTab[i/32]?).getD #[])[i % 32]?.getD 0
def bankN : Nat := 2865
def profileN : Nat := 983
def rootN : Nat := 27

def field (w off x : Nat) := (x >>> off) % (2^w)
def slot (w i x : Nat) := field w (w*i) x
def obs (i : Nat) : Mask := BitVec.ofNat 14 (slot 14 i rowLookup)
def atom (i : Nat) : Mask := BitVec.ofNat 14 (slot 14 i maskLookup)
def ids (n : Nat) : List Nat :=
  let x := bk n
  (List.range (x % 64)).map (fun i => slot 9 i (x>>>6))
def bankRows (n : Nat) := (ids n).map obs
def pairList (size : Nat) (x : Nat) :=
  (List.range size).map (fun i => (atom (slot portWidth (2*i) x), atom (slot portWidth (2*i+1) x)))
def bankId (idx : Nat) := (pr idx) % 4096
def exponent (idx : Nat) := field 3 12 (pr idx)
def pmoves (idx : Nat) := pairList (field 10 15 (pr idx)) ((pr idx)>>>25)
def initial (idx : Nat) : Mask := BitVec.ofNat 14 ((rt idx) % 16384)
def rmoves (idx : Nat) := pairList (field 10 14 (rt idx)) ((rt idx)>>>24)
def obsCheck (i : Nat) := !fast (obs i) &&
  (List.range rowN).all (fun j => decide (i=j) || (bad i).testBit j || fast (obs i ||| obs j))
def indexSet : List Nat → Nat
  | [] => 0
  | i::is => (1 <<< i) ||| indexSet is
theorem index_in (xs : List Nat) (i : Nat) (mem : i∈xs) : (indexSet xs).testBit i = true := by
  induction xs with
  | nil => simp at mem
  | cons x xs ih =>
    rcases List.mem_cons.mp mem with rfl|h
    · simp [indexSet,Nat.testBit_shiftLeft]
    · simp [indexSet,ih h]
def cachedGeom (n : Nat) :=
  let xs := ids n
  let all := indexSet xs
  decide (bankRows n).Nodup && xs.all (fun i => decide (i<rowN) && ((bad i &&& all) == 0))
theorem cached_geometry {n} (base : ∀ i<rowN, obsCheck i = true) (good : cachedGeom n = true) :
    valid [] (bankRows n) = true := by
  simp only [cachedGeom,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq,beq_iff_eq] at good
  simp only [valid,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq,Bool.not_eq_true',Bool.or_eq_true,beq_iff_eq]
  refine ⟨⟨?_,good.1⟩,?_⟩
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    have b := base i (good.2 i hi).1
    simp only [obsCheck,Bool.and_eq_true,Bool.not_eq_true'] at b
    exact ⟨rfl,b.1⟩
  · intro x hx y hy
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hy
    have b := base i (good.2 i hi).1
    simp only [obsCheck,Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,decide_eq_true_eq] at b
    rcases b.2 j (List.mem_range.mpr (good.2 j hj).1) with (rfl|ban)|ok
    · exact Or.inl rfl
    · have z := congrArg (fun w : Nat => w.testBit j) (good.2 i hi).2
      simp [Nat.testBit_and,ban,index_in _ _ hj] at z
    · exact Or.inr ok

def profileCheck (n : Nat) := decide (bankId n < bankN) &&
  decide ((bankRows (bankId n)).length < 63) &&
  (childMoves (exponent n) (bankRows (bankId n)) == pmoves n)
def rootCheck (n : Nat) := rootMoves (initial n) (flags seeds (hit (initial n))) == rmoves n
def dbFlags (rs : Rules) (n : Nat) := (bankRows n).all (inDomain rs)
def branchRule (ab : Mask × Mask) (side : Nat) := if side % 2=0 then ab else (ab.2,ab.1)
def iterCheck (ps : List (Mask × Mask)) (tape : Nat) (f : Mask × Mask → Nat → Bool) :=
  (ps.zipIdx).all (fun z => f z.1 (slot childWidth z.2 tape))
theorem iter_ok {ps tape f} (checked : iterCheck ps tape f = true) (p) (hp : p∈ps) :
    ∃ c, f p c = true := by
  simp only [iterCheck,List.all_eq_true] at checked
  obtain ⟨i,hi⟩ : ∃ i, (p,i) ∈ ps.zipIdx := by
    have h : p ∈ ps.zipIdx.map Prod.fst := by simpa using hp
    obtain ⟨⟨x,i⟩,hx,rfl⟩ := List.mem_map.mp h
    exact ⟨i,hx⟩
  exact ⟨_,checked (p,i) hi⟩

theorem pickBlock {k rs ab ch} (no : ¬Easy edge k (D (branchRule ab ch::rs))) : Block rs k ab := by
  unfold branchRule at no
  split at no
  · exact Or.inl no
  · exact Or.inr no

-- A branch records every negative row needed below it. Containment of these row sets
-- permits the same checked branch to serve under different earlier comparisons.
def selectNum (b : Bool) (n : Nat) := if b then n else 0
theorem select_bit (b : Bool) (n j : Nat) : (selectNum b n).testBit j = (b && n.testBit j) := by
  cases b <;> simp [selectNum]
def hiAll (a : Mask) := (selectNum (hit a 1) (sensor 0)) ||| (selectNum (hit a 2) (sensor 1)) ||| (selectNum (hit a 4) (sensor 2)) ||| (selectNum (hit a 8) (sensor 3)) ||| (selectNum (hit a 16) (sensor 4)) ||| (selectNum (hit a 32) (sensor 5)) ||| (selectNum (hit a 64) (sensor 6)) ||| (selectNum (hit a 128) (sensor 7)) ||| (selectNum (hit a 256) (sensor 8)) ||| (selectNum (hit a 512) (sensor 9)) ||| (selectNum (hit a 1024) (sensor 10)) ||| (selectNum (hit a 2048) (sensor 11)) ||| (selectNum (hit a 4096) (sensor 12)) ||| (selectNum (hit a 8192) (sensor 13))
def sensorCheck (j : Nat) := (List.range 14).all (fun i =>
  (sensor i).testBit j == hit (vertex i) (obs j))
theorem nonzero_components (x : Mask) :
    (x.getLsbD 0 || x.getLsbD 1 || x.getLsbD 2 || x.getLsbD 3 || x.getLsbD 4 || x.getLsbD 5 || x.getLsbD 6 || x.getLsbD 7 || x.getLsbD 8 || x.getLsbD 9 || x.getLsbD 10 || x.getLsbD 11 || x.getLsbD 12 || x.getLsbD 13) = (x != 0) := by
  by_cases zero : x=0
  · subst x
    decide
  · rw [show (x != 0) = true from bne_iff_ne.mpr zero]
    simp only [Bool.or_eq_true]
    by_contra! no
    apply zero
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [show (0 : Mask).getLsbD i = false from BitVec.getLsbD_zero]
    apply Bool.eq_false_iff.mpr
    interval_cases i <;> tauto
theorem sensor_bit {j} (h : sensorCheck j = true) (a : Mask) :
    (hiAll a).testBit j = hit a (obs j) := by
  simp only [sensorCheck,List.all_eq_true,beq_iff_eq] at h
  simp only [hiAll,Nat.testBit_or,select_bit,h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide),h 4 (by decide),h 5 (by decide),h 6 (by decide),h 7 (by decide),h 8 (by decide),h 9 (by decide),h 10 (by decide),h 11 (by decide),h 12 (by decide),h 13 (by decide)]
  generalize obs j = x
  have component (v : Fin 14) : (hit a (vertex v.val) && hit (vertex v.val) x) =
      (a &&& x).getLsbD v.val := by
    rw [hit_comm a,show hit (vertex v.val) a = a.getLsbD v.val from singleton_hits v a,
      show hit (vertex v.val) x = x.getLsbD v.val from singleton_hits v x,BitVec.getLsbD_and]
  change ((hit a (vertex (0 : Fin 14).val) && hit (vertex (0 : Fin 14).val) x) || (hit a (vertex (1 : Fin 14).val) && hit (vertex (1 : Fin 14).val) x) || (hit a (vertex (2 : Fin 14).val) && hit (vertex (2 : Fin 14).val) x) || (hit a (vertex (3 : Fin 14).val) && hit (vertex (3 : Fin 14).val) x) || (hit a (vertex (4 : Fin 14).val) && hit (vertex (4 : Fin 14).val) x) || (hit a (vertex (5 : Fin 14).val) && hit (vertex (5 : Fin 14).val) x) || (hit a (vertex (6 : Fin 14).val) && hit (vertex (6 : Fin 14).val) x) || (hit a (vertex (7 : Fin 14).val) && hit (vertex (7 : Fin 14).val) x) || (hit a (vertex (8 : Fin 14).val) && hit (vertex (8 : Fin 14).val) x) || (hit a (vertex (9 : Fin 14).val) && hit (vertex (9 : Fin 14).val) x) || (hit a (vertex (10 : Fin 14).val) && hit (vertex (10 : Fin 14).val) x) || (hit a (vertex (11 : Fin 14).val) && hit (vertex (11 : Fin 14).val) x) || (hit a (vertex (12 : Fin 14).val) && hit (vertex (12 : Fin 14).val) x) || (hit a (vertex (13 : Fin 14).val) && hit (vertex (13 : Fin 14).val) x)) = _
  rw [component 0,component 1,component 2,component 3,component 4,component 5,component 6,component 7,component 8,component 9,component 10,component 11,component 12,component 13]
  exact nonzero_components (a &&& x)

def below (x y : Nat) := (x &&& y) == x
theorem bit_below {x y j : Nat} (sub : below x y = true) (on : x.testBit j = true) : y.testBit j = true := by
  have eq : x &&& y = x := beq_iff_eq.mp sub
  have h := congrArg (fun w : Nat => w.testBit j) eq
  simpa [Nat.testBit_and,on] using h

def domainMask (rs : Rules) (s : Nat) :=
  ∀ j<rowN, s.testBit j = true → D rs (obs j)
def ruleFits (p : Mask × Mask) (s : Nat) := below (s &&& hiAll p.1) (hiAll p.2)
theorem narrower {p s rs bigger} (sensors : ∀ j<rowN, sensorCheck j = true)
    (parent : domainMask rs bigger) (sub : below s bigger = true) (fit : ruleFits p s = true) :
    domainMask (p::rs) s := by
  intro j hj on
  apply (in_cons _ _ _ _).mpr
  refine ⟨parent _ hj (bit_below sub on),?_⟩
  intro yes
  have y : (s &&& hiAll p.1).testBit j = true := by simp [Nat.testBit_and,on,sensor_bit (sensors j hj),yes]
  simpa [sensor_bit (sensors j hj)] using bit_below fit y

def nodeProfile (i : Nat) := nd i % 1024
def bankSet (b : Nat) := indexSet (ids b)
def support (c : Nat) := if c % 2=0 then bankSet (c/2) else nsup (c/2)
def typed (k c : Nat) := if c % 2=0 then decide (c/2<bankN ∧ 2^k < (ids (c/2)).length)
  else decide (c/2<nodeN ∧ exponent (nodeProfile (c/2))+1=k)
def down (i : Nat) (k : Nat) (s : Nat) (ab : Mask × Mask) (ch : Nat) :=
  let c := ch/2
  typed k c && decide (c % 2=0 ∨ c/2 < i) && below (support c) s && ruleFits (branchRule ab ch) (support c)
def nodeCheck (i : Nat) :=
  let p := nodeProfile i
  decide (p<profileN) && below (bankSet (bankId p)) (nsup i) &&
    iterCheck (pmoves p) (nd i >>> 10) (down i (exponent p) (nsup i))
def rootCert (i : Nat) := iterCheck (rmoves i) (top i) (fun ab ch =>
  typed 5 (ch/2) && ruleFits (branchRule ab ch) (support (ch/2)))

theorem valid_inside {b rs} (base : ∀ i<rowN, obsCheck i = true) (g : cachedGeom b = true)
    (d : domainMask rs (bankSet b)) : valid rs (bankRows b) = true := by
  apply valid_of_geom (cached_geometry base g)
  simp only [List.all_eq_true]
  intro x hx
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
  simp only [cachedGeom,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at g
  exact d i (g.2 i hi).1 (index_in _ _ hi)

theorem terminals {rs k c} (base : ∀ j<rowN, obsCheck j = true)
    (banks : ∀ b<bankN, cachedGeom b = true) (even : c % 2=0) (size : typed k c = true)
    (good : domainMask rs (support c)) : ¬Easy edge k (D rs) := by
  simp only [typed,if_pos even,decide_eq_true_eq] at size
  have ok := valid_inside base (banks _ size.1) (by simpa [support,even] using good)
  intro easy
  have cap := bound_list ok easy
  simp only [bankRows,List.length_map] at cap
  omega

theorem nodes_sound (base : ∀ j<rowN, obsCheck j = true) (sensors : ∀ j<rowN, sensorCheck j = true)
    (banks : ∀ b<bankN, cachedGeom b = true) (profiles : ∀ p<profileN, profileCheck p = true)
    (nodes : ∀ i<nodeN, nodeCheck i = true) (i : Nat) (bound : i<nodeN)
    (rs : Rules) (domain : domainMask rs (nsup i)) :
    ¬Easy edge (exponent (nodeProfile i)+1) (D rs) := by
  induction i using Nat.strong_induction_on generalizing rs with
  | ind i ih =>
    have data := nodes _ bound
    simp only [nodeCheck,Bool.and_eq_true,decide_eq_true_eq] at data
    have profile := profiles _ data.1.1
    simp only [profileCheck,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at profile
    have d : domainMask rs (bankSet (bankId (nodeProfile i))) :=
      fun j hj on => domain j hj (bit_below data.1.2 on)
    apply guided (valid_inside base (banks _ profile.1.1) d) profile.1.2
    intro ab member
    rw [profile.2] at member
    obtain ⟨ch,h⟩ := iter_ok data.2 ab member
    simp only [down,Bool.and_eq_true,decide_eq_true_eq] at h
    have good := narrower sensors domain h.1.2 h.2
    apply pickBlock (ch:=ch)
    by_cases even : ch/2 % 2=0
    · exact terminals base banks even h.1.1.1 good
    · have ty := h.1.1.1
      simp only [typed,if_neg even,decide_eq_true_eq] at ty
      rw [← ty.2]
      exact ih _ (h.1.1.2.resolve_left even) ty.1 _ (by simpa [support,even] using good)

theorem compact_sound (roots : firstP.map Prod.fst = (List.range rootN).map initial)
    (base : ∀ j<rowN, obsCheck j = true) (sensors : ∀ j<rowN, sensorCheck j = true)
    (banks : ∀ b<bankN, cachedGeom b = true) (profiles : ∀ p<profileN, profileCheck p = true)
    (nodes : ∀ i<nodeN, nodeCheck i = true) (shapes : ∀ i<rootN, rootCheck i = true)
    (tops : ∀ i<rootN, rootCert i = true) : ¬Easy edge 6 (fun _ => True) := by
  apply root_guided
  intro a ha ab hm
  have mem : a.1 ∈ (List.range rootN).map initial := roots ▸ List.mem_map.mpr ⟨a,ha,rfl⟩
  obtain ⟨i,hi,eq⟩ := List.mem_map.mp mem
  have lab : a.2 = flags seeds (hit a.1) := by
    have h := (List.mem_filter.mp ha).1
    change a ∈ contestants 32 (columns seeds) at h
    unfold contestants columns at h
    rw [← flags_zero seeds,enum_lab _ (by decide : seeds.length<63)] at h
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp h
    rfl
  have shape : rootMoves (initial i) (flags seeds (hit (initial i))) = rmoves i :=
    beq_iff_eq.mp (shapes i (List.mem_range.mp hi))
  rw [lab,←eq,shape] at hm
  obtain ⟨ch,h⟩ := iter_ok (tops i (List.mem_range.mp hi)) ab hm
  obtain ⟨typedC,fit⟩ := Bool.and_eq_true_iff.mp h
  have empty : domainMask [] (support (ch/2)) := by intro j hj on;rfl
  have self : below (support (ch/2)) (support (ch/2)) = true := by simp [below]
  have good := narrower sensors empty self fit
  apply pickBlock (ch:=ch)
  by_cases even : ch/2 % 2=0
  · exact terminals base banks even typedC good
  · simp only [typed,if_neg even,decide_eq_true_eq] at typedC
    rw [← typedC.2]
    exact nodes_sound base sensors banks profiles nodes _ typedC.1 _ (by simpa [support,even] using good)

def slice (p : Nat→Bool) (lo len : Nat) := (List.range len).all (fun i => p (lo+i))
def interval (p : Nat→Bool) (a b : Nat) := ∀ j, a≤j → j<b → p j=true
theorem slice_proof {p lo len} (h : slice p lo len = true) : interval p lo (lo+len) := by
  intro j left right
  have hi : j-lo < len := by omega
  have eq : lo+(j-lo)=j := by omega
  exact eq ▸ (List.all_eq_true.mp h (j-lo) (List.mem_range.mpr hi))
theorem combined {p a b c} (l : interval p a b) (r : interval p b c) : interval p a c := by
  intro j lo hi
  by_cases h : j<b
  · exact l _ lo h
  · exact r _ (by omega) hi
theorem complete_interval {p n} (h : interval p 0 n) : ∀ j<n, p j=true := fun j hj => h j (Nat.zero_le _) hj

theorem enlarge {f n m E} (easy : Easy f n E) (le : n ≤ m) : Easy f m E := by
  induction le with
  | refl => exact easy
  | step _ ih => exact pad ih

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt0 : interval obsCheck 0 8 := slice_proof (lo:=0) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt8 : interval obsCheck 8 16 := slice_proof (lo:=8) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt16 : interval obsCheck 16 24 := slice_proof (lo:=16) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt24 : interval obsCheck 24 32 := slice_proof (lo:=24) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt32 : interval obsCheck 32 40 := slice_proof (lo:=32) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt40 : interval obsCheck 40 48 := slice_proof (lo:=40) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt48 : interval obsCheck 48 56 := slice_proof (lo:=48) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt56 : interval obsCheck 56 64 := slice_proof (lo:=56) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt64 : interval obsCheck 64 72 := slice_proof (lo:=64) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt72 : interval obsCheck 72 80 := slice_proof (lo:=72) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt80 : interval obsCheck 80 88 := slice_proof (lo:=80) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt88 : interval obsCheck 88 96 := slice_proof (lo:=88) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt96 : interval obsCheck 96 104 := slice_proof (lo:=96) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt104 : interval obsCheck 104 112 := slice_proof (lo:=104) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt112 : interval obsCheck 112 120 := slice_proof (lo:=112) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt120 : interval obsCheck 120 128 := slice_proof (lo:=120) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt128 : interval obsCheck 128 136 := slice_proof (lo:=128) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt136 : interval obsCheck 136 144 := slice_proof (lo:=136) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt144 : interval obsCheck 144 152 := slice_proof (lo:=144) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt152 : interval obsCheck 152 160 := slice_proof (lo:=152) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt160 : interval obsCheck 160 168 := slice_proof (lo:=160) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt168 : interval obsCheck 168 176 := slice_proof (lo:=168) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt176 : interval obsCheck 176 184 := slice_proof (lo:=176) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt184 : interval obsCheck 184 192 := slice_proof (lo:=184) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt192 : interval obsCheck 192 200 := slice_proof (lo:=192) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt200 : interval obsCheck 200 208 := slice_proof (lo:=200) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt208 : interval obsCheck 208 216 := slice_proof (lo:=208) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt216 : interval obsCheck 216 224 := slice_proof (lo:=216) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt224 : interval obsCheck 224 232 := slice_proof (lo:=224) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem obsCheckAt232 : interval obsCheck 232 240 := slice_proof (lo:=232) (len:=8) (by decide +kernel)
theorem allobsCheck : ∀ i<240, obsCheck i = true := complete_interval (combined (combined (combined (combined obsCheckAt0 (combined obsCheckAt8 obsCheckAt16)) (combined (combined obsCheckAt24 obsCheckAt32) (combined obsCheckAt40 obsCheckAt48))) (combined (combined (combined obsCheckAt56 obsCheckAt64) (combined obsCheckAt72 obsCheckAt80)) (combined (combined obsCheckAt88 obsCheckAt96) (combined obsCheckAt104 obsCheckAt112)))) (combined (combined (combined obsCheckAt120 (combined obsCheckAt128 obsCheckAt136)) (combined (combined obsCheckAt144 obsCheckAt152) (combined obsCheckAt160 obsCheckAt168))) (combined (combined (combined obsCheckAt176 obsCheckAt184) (combined obsCheckAt192 obsCheckAt200)) (combined (combined obsCheckAt208 obsCheckAt216) (combined obsCheckAt224 obsCheckAt232)))))
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem sensorCheckAt0 : interval sensorCheck 0 64 := slice_proof (lo:=0) (len:=64) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem sensorCheckAt64 : interval sensorCheck 64 128 := slice_proof (lo:=64) (len:=64) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem sensorCheckAt128 : interval sensorCheck 128 192 := slice_proof (lo:=128) (len:=64) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem sensorCheckAt192 : interval sensorCheck 192 240 := slice_proof (lo:=192) (len:=48) (by decide +kernel)
theorem allsensorCheck : ∀ i<240, sensorCheck i = true := complete_interval (combined (combined sensorCheckAt0 sensorCheckAt64) (combined sensorCheckAt128 sensorCheckAt192))
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt0 : interval cachedGeom 0 46 := slice_proof (lo:=0) (len:=46) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt46 : interval cachedGeom 46 91 := slice_proof (lo:=46) (len:=45) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt91 : interval cachedGeom 91 133 := slice_proof (lo:=91) (len:=42) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt133 : interval cachedGeom 133 184 := slice_proof (lo:=133) (len:=51) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt184 : interval cachedGeom 184 234 := slice_proof (lo:=184) (len:=50) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt234 : interval cachedGeom 234 293 := slice_proof (lo:=234) (len:=59) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt293 : interval cachedGeom 293 355 := slice_proof (lo:=293) (len:=62) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt355 : interval cachedGeom 355 409 := slice_proof (lo:=355) (len:=54) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt409 : interval cachedGeom 409 468 := slice_proof (lo:=409) (len:=59) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt468 : interval cachedGeom 468 512 := slice_proof (lo:=468) (len:=44) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt512 : interval cachedGeom 512 559 := slice_proof (lo:=512) (len:=47) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt559 : interval cachedGeom 559 600 := slice_proof (lo:=559) (len:=41) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt600 : interval cachedGeom 600 641 := slice_proof (lo:=600) (len:=41) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt641 : interval cachedGeom 641 683 := slice_proof (lo:=641) (len:=42) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt683 : interval cachedGeom 683 727 := slice_proof (lo:=683) (len:=44) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt727 : interval cachedGeom 727 771 := slice_proof (lo:=727) (len:=44) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt771 : interval cachedGeom 771 810 := slice_proof (lo:=771) (len:=39) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt810 : interval cachedGeom 810 848 := slice_proof (lo:=810) (len:=38) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt848 : interval cachedGeom 848 887 := slice_proof (lo:=848) (len:=39) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt887 : interval cachedGeom 887 926 := slice_proof (lo:=887) (len:=39) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt926 : interval cachedGeom 926 965 := slice_proof (lo:=926) (len:=39) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt965 : interval cachedGeom 965 1023 := slice_proof (lo:=965) (len:=58) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt1023 : interval cachedGeom 1023 1093 := slice_proof (lo:=1023) (len:=70) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt1093 : interval cachedGeom 1093 1152 := slice_proof (lo:=1093) (len:=59) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt1152 : interval cachedGeom 1152 1198 := slice_proof (lo:=1152) (len:=46) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt1198 : interval cachedGeom 1198 1251 := slice_proof (lo:=1198) (len:=53) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt1251 : interval cachedGeom 1251 1302 := slice_proof (lo:=1251) (len:=51) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt1302 : interval cachedGeom 1302 1349 := slice_proof (lo:=1302) (len:=47) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt1349 : interval cachedGeom 1349 1393 := slice_proof (lo:=1349) (len:=44) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt1393 : interval cachedGeom 1393 1438 := slice_proof (lo:=1393) (len:=45) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt1438 : interval cachedGeom 1438 1484 := slice_proof (lo:=1438) (len:=46) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt1484 : interval cachedGeom 1484 1521 := slice_proof (lo:=1484) (len:=37) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt1521 : interval cachedGeom 1521 1558 := slice_proof (lo:=1521) (len:=37) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt1558 : interval cachedGeom 1558 1595 := slice_proof (lo:=1558) (len:=37) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt1595 : interval cachedGeom 1595 1637 := slice_proof (lo:=1595) (len:=42) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt1637 : interval cachedGeom 1637 1711 := slice_proof (lo:=1637) (len:=74) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt1711 : interval cachedGeom 1711 1771 := slice_proof (lo:=1711) (len:=60) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt1771 : interval cachedGeom 1771 1832 := slice_proof (lo:=1771) (len:=61) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt1832 : interval cachedGeom 1832 1904 := slice_proof (lo:=1832) (len:=72) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt1904 : interval cachedGeom 1904 1980 := slice_proof (lo:=1904) (len:=76) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt1980 : interval cachedGeom 1980 2034 := slice_proof (lo:=1980) (len:=54) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt2034 : interval cachedGeom 2034 2100 := slice_proof (lo:=2034) (len:=66) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt2100 : interval cachedGeom 2100 2164 := slice_proof (lo:=2100) (len:=64) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt2164 : interval cachedGeom 2164 2222 := slice_proof (lo:=2164) (len:=58) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt2222 : interval cachedGeom 2222 2280 := slice_proof (lo:=2222) (len:=58) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt2280 : interval cachedGeom 2280 2354 := slice_proof (lo:=2280) (len:=74) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt2354 : interval cachedGeom 2354 2429 := slice_proof (lo:=2354) (len:=75) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt2429 : interval cachedGeom 2429 2485 := slice_proof (lo:=2429) (len:=56) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt2485 : interval cachedGeom 2485 2544 := slice_proof (lo:=2485) (len:=59) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt2544 : interval cachedGeom 2544 2607 := slice_proof (lo:=2544) (len:=63) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt2607 : interval cachedGeom 2607 2659 := slice_proof (lo:=2607) (len:=52) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt2659 : interval cachedGeom 2659 2705 := slice_proof (lo:=2659) (len:=46) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt2705 : interval cachedGeom 2705 2754 := slice_proof (lo:=2705) (len:=49) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt2754 : interval cachedGeom 2754 2810 := slice_proof (lo:=2754) (len:=56) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt2810 : interval cachedGeom 2810 2847 := slice_proof (lo:=2810) (len:=37) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem cachedGeomAt2847 : interval cachedGeom 2847 2865 := slice_proof (lo:=2847) (len:=18) (by decide +kernel)
theorem allcachedGeom : ∀ i<2865, cachedGeom i = true := complete_interval (combined (combined (combined (combined (combined cachedGeomAt0 (combined cachedGeomAt46 cachedGeomAt91)) (combined (combined cachedGeomAt133 cachedGeomAt184) (combined cachedGeomAt234 cachedGeomAt293))) (combined (combined cachedGeomAt355 (combined cachedGeomAt409 cachedGeomAt468)) (combined (combined cachedGeomAt512 cachedGeomAt559) (combined cachedGeomAt600 cachedGeomAt641)))) (combined (combined (combined cachedGeomAt683 (combined cachedGeomAt727 cachedGeomAt771)) (combined (combined cachedGeomAt810 cachedGeomAt848) (combined cachedGeomAt887 cachedGeomAt926))) (combined (combined cachedGeomAt965 (combined cachedGeomAt1023 cachedGeomAt1093)) (combined (combined cachedGeomAt1152 cachedGeomAt1198) (combined cachedGeomAt1251 cachedGeomAt1302))))) (combined (combined (combined (combined cachedGeomAt1349 (combined cachedGeomAt1393 cachedGeomAt1438)) (combined (combined cachedGeomAt1484 cachedGeomAt1521) (combined cachedGeomAt1558 cachedGeomAt1595))) (combined (combined cachedGeomAt1637 (combined cachedGeomAt1711 cachedGeomAt1771)) (combined (combined cachedGeomAt1832 cachedGeomAt1904) (combined cachedGeomAt1980 cachedGeomAt2034)))) (combined (combined (combined cachedGeomAt2100 (combined cachedGeomAt2164 cachedGeomAt2222)) (combined (combined cachedGeomAt2280 cachedGeomAt2354) (combined cachedGeomAt2429 cachedGeomAt2485))) (combined (combined cachedGeomAt2544 (combined cachedGeomAt2607 cachedGeomAt2659)) (combined (combined cachedGeomAt2705 cachedGeomAt2754) (combined cachedGeomAt2810 cachedGeomAt2847))))))
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt0 : interval profileCheck 0 4 := slice_proof (lo:=0) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt4 : interval profileCheck 4 10 := slice_proof (lo:=4) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt10 : interval profileCheck 10 15 := slice_proof (lo:=10) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt15 : interval profileCheck 15 20 := slice_proof (lo:=15) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt20 : interval profileCheck 20 27 := slice_proof (lo:=20) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt27 : interval profileCheck 27 32 := slice_proof (lo:=27) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt32 : interval profileCheck 32 38 := slice_proof (lo:=32) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt38 : interval profileCheck 38 39 := slice_proof (lo:=38) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt39 : interval profileCheck 39 45 := slice_proof (lo:=39) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt45 : interval profileCheck 45 50 := slice_proof (lo:=45) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt50 : interval profileCheck 50 55 := slice_proof (lo:=50) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt55 : interval profileCheck 55 61 := slice_proof (lo:=55) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt61 : interval profileCheck 61 66 := slice_proof (lo:=61) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt66 : interval profileCheck 66 71 := slice_proof (lo:=66) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt71 : interval profileCheck 71 76 := slice_proof (lo:=71) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt76 : interval profileCheck 76 80 := slice_proof (lo:=76) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt80 : interval profileCheck 80 82 := slice_proof (lo:=80) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt82 : interval profileCheck 82 84 := slice_proof (lo:=82) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt84 : interval profileCheck 84 88 := slice_proof (lo:=84) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt88 : interval profileCheck 88 93 := slice_proof (lo:=88) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt93 : interval profileCheck 93 97 := slice_proof (lo:=93) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt97 : interval profileCheck 97 102 := slice_proof (lo:=97) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt102 : interval profileCheck 102 104 := slice_proof (lo:=102) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt104 : interval profileCheck 104 105 := slice_proof (lo:=104) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt105 : interval profileCheck 105 106 := slice_proof (lo:=105) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt106 : interval profileCheck 106 107 := slice_proof (lo:=106) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt107 : interval profileCheck 107 108 := slice_proof (lo:=107) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt108 : interval profileCheck 108 109 := slice_proof (lo:=108) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt109 : interval profileCheck 109 110 := slice_proof (lo:=109) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt110 : interval profileCheck 110 114 := slice_proof (lo:=110) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt114 : interval profileCheck 114 117 := slice_proof (lo:=114) (len:=3) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt117 : interval profileCheck 117 118 := slice_proof (lo:=117) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt118 : interval profileCheck 118 119 := slice_proof (lo:=118) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt119 : interval profileCheck 119 120 := slice_proof (lo:=119) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt120 : interval profileCheck 120 124 := slice_proof (lo:=120) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt124 : interval profileCheck 124 129 := slice_proof (lo:=124) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt129 : interval profileCheck 129 133 := slice_proof (lo:=129) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt133 : interval profileCheck 133 139 := slice_proof (lo:=133) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt139 : interval profileCheck 139 142 := slice_proof (lo:=139) (len:=3) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt142 : interval profileCheck 142 147 := slice_proof (lo:=142) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt147 : interval profileCheck 147 151 := slice_proof (lo:=147) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt151 : interval profileCheck 151 153 := slice_proof (lo:=151) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt153 : interval profileCheck 153 157 := slice_proof (lo:=153) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt157 : interval profileCheck 157 162 := slice_proof (lo:=157) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt162 : interval profileCheck 162 168 := slice_proof (lo:=162) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt168 : interval profileCheck 168 175 := slice_proof (lo:=168) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt175 : interval profileCheck 175 181 := slice_proof (lo:=175) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt181 : interval profileCheck 181 184 := slice_proof (lo:=181) (len:=3) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt184 : interval profileCheck 184 188 := slice_proof (lo:=184) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt188 : interval profileCheck 188 193 := slice_proof (lo:=188) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt193 : interval profileCheck 193 198 := slice_proof (lo:=193) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt198 : interval profileCheck 198 203 := slice_proof (lo:=198) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt203 : interval profileCheck 203 209 := slice_proof (lo:=203) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt209 : interval profileCheck 209 215 := slice_proof (lo:=209) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt215 : interval profileCheck 215 221 := slice_proof (lo:=215) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt221 : interval profileCheck 221 226 := slice_proof (lo:=221) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt226 : interval profileCheck 226 231 := slice_proof (lo:=226) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt231 : interval profileCheck 231 235 := slice_proof (lo:=231) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt235 : interval profileCheck 235 241 := slice_proof (lo:=235) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt241 : interval profileCheck 241 246 := slice_proof (lo:=241) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt246 : interval profileCheck 246 250 := slice_proof (lo:=246) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt250 : interval profileCheck 250 253 := slice_proof (lo:=250) (len:=3) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt253 : interval profileCheck 253 260 := slice_proof (lo:=253) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt260 : interval profileCheck 260 267 := slice_proof (lo:=260) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt267 : interval profileCheck 267 273 := slice_proof (lo:=267) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt273 : interval profileCheck 273 278 := slice_proof (lo:=273) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt278 : interval profileCheck 278 285 := slice_proof (lo:=278) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt285 : interval profileCheck 285 291 := slice_proof (lo:=285) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt291 : interval profileCheck 291 298 := slice_proof (lo:=291) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt298 : interval profileCheck 298 305 := slice_proof (lo:=298) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt305 : interval profileCheck 305 312 := slice_proof (lo:=305) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt312 : interval profileCheck 312 319 := slice_proof (lo:=312) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt319 : interval profileCheck 319 327 := slice_proof (lo:=319) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt327 : interval profileCheck 327 334 := slice_proof (lo:=327) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt334 : interval profileCheck 334 340 := slice_proof (lo:=334) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt340 : interval profileCheck 340 346 := slice_proof (lo:=340) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt346 : interval profileCheck 346 351 := slice_proof (lo:=346) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt351 : interval profileCheck 351 358 := slice_proof (lo:=351) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt358 : interval profileCheck 358 365 := slice_proof (lo:=358) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt365 : interval profileCheck 365 371 := slice_proof (lo:=365) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt371 : interval profileCheck 371 378 := slice_proof (lo:=371) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt378 : interval profileCheck 378 386 := slice_proof (lo:=378) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt386 : interval profileCheck 386 394 := slice_proof (lo:=386) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt394 : interval profileCheck 394 401 := slice_proof (lo:=394) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt401 : interval profileCheck 401 408 := slice_proof (lo:=401) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt408 : interval profileCheck 408 414 := slice_proof (lo:=408) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt414 : interval profileCheck 414 418 := slice_proof (lo:=414) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt418 : interval profileCheck 418 425 := slice_proof (lo:=418) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt425 : interval profileCheck 425 432 := slice_proof (lo:=425) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt432 : interval profileCheck 432 438 := slice_proof (lo:=432) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt438 : interval profileCheck 438 445 := slice_proof (lo:=438) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt445 : interval profileCheck 445 451 := slice_proof (lo:=445) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt451 : interval profileCheck 451 457 := slice_proof (lo:=451) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt457 : interval profileCheck 457 464 := slice_proof (lo:=457) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt464 : interval profileCheck 464 466 := slice_proof (lo:=464) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt466 : interval profileCheck 466 472 := slice_proof (lo:=466) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt472 : interval profileCheck 472 477 := slice_proof (lo:=472) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt477 : interval profileCheck 477 481 := slice_proof (lo:=477) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt481 : interval profileCheck 481 486 := slice_proof (lo:=481) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt486 : interval profileCheck 486 487 := slice_proof (lo:=486) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt487 : interval profileCheck 487 488 := slice_proof (lo:=487) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt488 : interval profileCheck 488 492 := slice_proof (lo:=488) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt492 : interval profileCheck 492 493 := slice_proof (lo:=492) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt493 : interval profileCheck 493 495 := slice_proof (lo:=493) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt495 : interval profileCheck 495 502 := slice_proof (lo:=495) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt502 : interval profileCheck 502 509 := slice_proof (lo:=502) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt509 : interval profileCheck 509 511 := slice_proof (lo:=509) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt511 : interval profileCheck 511 512 := slice_proof (lo:=511) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt512 : interval profileCheck 512 513 := slice_proof (lo:=512) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt513 : interval profileCheck 513 514 := slice_proof (lo:=513) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt514 : interval profileCheck 514 515 := slice_proof (lo:=514) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt515 : interval profileCheck 515 516 := slice_proof (lo:=515) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt516 : interval profileCheck 516 521 := slice_proof (lo:=516) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt521 : interval profileCheck 521 528 := slice_proof (lo:=521) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt528 : interval profileCheck 528 530 := slice_proof (lo:=528) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt530 : interval profileCheck 530 531 := slice_proof (lo:=530) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt531 : interval profileCheck 531 536 := slice_proof (lo:=531) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt536 : interval profileCheck 536 541 := slice_proof (lo:=536) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt541 : interval profileCheck 541 546 := slice_proof (lo:=541) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt546 : interval profileCheck 546 551 := slice_proof (lo:=546) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt551 : interval profileCheck 551 554 := slice_proof (lo:=551) (len:=3) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt554 : interval profileCheck 554 560 := slice_proof (lo:=554) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt560 : interval profileCheck 560 564 := slice_proof (lo:=560) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt564 : interval profileCheck 564 568 := slice_proof (lo:=564) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt568 : interval profileCheck 568 574 := slice_proof (lo:=568) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt574 : interval profileCheck 574 579 := slice_proof (lo:=574) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt579 : interval profileCheck 579 584 := slice_proof (lo:=579) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt584 : interval profileCheck 584 588 := slice_proof (lo:=584) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt588 : interval profileCheck 588 592 := slice_proof (lo:=588) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt592 : interval profileCheck 592 598 := slice_proof (lo:=592) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt598 : interval profileCheck 598 602 := slice_proof (lo:=598) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt602 : interval profileCheck 602 607 := slice_proof (lo:=602) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt607 : interval profileCheck 607 613 := slice_proof (lo:=607) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt613 : interval profileCheck 613 619 := slice_proof (lo:=613) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt619 : interval profileCheck 619 621 := slice_proof (lo:=619) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt621 : interval profileCheck 621 623 := slice_proof (lo:=621) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt623 : interval profileCheck 623 630 := slice_proof (lo:=623) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt630 : interval profileCheck 630 636 := slice_proof (lo:=630) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt636 : interval profileCheck 636 642 := slice_proof (lo:=636) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt642 : interval profileCheck 642 647 := slice_proof (lo:=642) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt647 : interval profileCheck 647 654 := slice_proof (lo:=647) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt654 : interval profileCheck 654 661 := slice_proof (lo:=654) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt661 : interval profileCheck 661 669 := slice_proof (lo:=661) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt669 : interval profileCheck 669 676 := slice_proof (lo:=669) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt676 : interval profileCheck 676 683 := slice_proof (lo:=676) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt683 : interval profileCheck 683 690 := slice_proof (lo:=683) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt690 : interval profileCheck 690 696 := slice_proof (lo:=690) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt696 : interval profileCheck 696 702 := slice_proof (lo:=696) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt702 : interval profileCheck 702 707 := slice_proof (lo:=702) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt707 : interval profileCheck 707 713 := slice_proof (lo:=707) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt713 : interval profileCheck 713 720 := slice_proof (lo:=713) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt720 : interval profileCheck 720 726 := slice_proof (lo:=720) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt726 : interval profileCheck 726 732 := slice_proof (lo:=726) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt732 : interval profileCheck 732 737 := slice_proof (lo:=732) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt737 : interval profileCheck 737 740 := slice_proof (lo:=737) (len:=3) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt740 : interval profileCheck 740 741 := slice_proof (lo:=740) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt741 : interval profileCheck 741 742 := slice_proof (lo:=741) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt742 : interval profileCheck 742 743 := slice_proof (lo:=742) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt743 : interval profileCheck 743 744 := slice_proof (lo:=743) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt744 : interval profileCheck 744 745 := slice_proof (lo:=744) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt745 : interval profileCheck 745 746 := slice_proof (lo:=745) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt746 : interval profileCheck 746 747 := slice_proof (lo:=746) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt747 : interval profileCheck 747 748 := slice_proof (lo:=747) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt748 : interval profileCheck 748 750 := slice_proof (lo:=748) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt750 : interval profileCheck 750 752 := slice_proof (lo:=750) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt752 : interval profileCheck 752 756 := slice_proof (lo:=752) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt756 : interval profileCheck 756 759 := slice_proof (lo:=756) (len:=3) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt759 : interval profileCheck 759 761 := slice_proof (lo:=759) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt761 : interval profileCheck 761 763 := slice_proof (lo:=761) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt763 : interval profileCheck 763 769 := slice_proof (lo:=763) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt769 : interval profileCheck 769 770 := slice_proof (lo:=769) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt770 : interval profileCheck 770 771 := slice_proof (lo:=770) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt771 : interval profileCheck 771 772 := slice_proof (lo:=771) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt772 : interval profileCheck 772 773 := slice_proof (lo:=772) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt773 : interval profileCheck 773 774 := slice_proof (lo:=773) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt774 : interval profileCheck 774 775 := slice_proof (lo:=774) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt775 : interval profileCheck 775 776 := slice_proof (lo:=775) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt776 : interval profileCheck 776 777 := slice_proof (lo:=776) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt777 : interval profileCheck 777 778 := slice_proof (lo:=777) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt778 : interval profileCheck 778 779 := slice_proof (lo:=778) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt779 : interval profileCheck 779 780 := slice_proof (lo:=779) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt780 : interval profileCheck 780 781 := slice_proof (lo:=780) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt781 : interval profileCheck 781 782 := slice_proof (lo:=781) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt782 : interval profileCheck 782 785 := slice_proof (lo:=782) (len:=3) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt785 : interval profileCheck 785 791 := slice_proof (lo:=785) (len:=6) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt791 : interval profileCheck 791 796 := slice_proof (lo:=791) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt796 : interval profileCheck 796 797 := slice_proof (lo:=796) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt797 : interval profileCheck 797 799 := slice_proof (lo:=797) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt799 : interval profileCheck 799 801 := slice_proof (lo:=799) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt801 : interval profileCheck 801 804 := slice_proof (lo:=801) (len:=3) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt804 : interval profileCheck 804 805 := slice_proof (lo:=804) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt805 : interval profileCheck 805 809 := slice_proof (lo:=805) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt809 : interval profileCheck 809 813 := slice_proof (lo:=809) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt813 : interval profileCheck 813 814 := slice_proof (lo:=813) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt814 : interval profileCheck 814 815 := slice_proof (lo:=814) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt815 : interval profileCheck 815 820 := slice_proof (lo:=815) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt820 : interval profileCheck 820 824 := slice_proof (lo:=820) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt824 : interval profileCheck 824 825 := slice_proof (lo:=824) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt825 : interval profileCheck 825 826 := slice_proof (lo:=825) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt826 : interval profileCheck 826 827 := slice_proof (lo:=826) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt827 : interval profileCheck 827 828 := slice_proof (lo:=827) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt828 : interval profileCheck 828 829 := slice_proof (lo:=828) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt829 : interval profileCheck 829 830 := slice_proof (lo:=829) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt830 : interval profileCheck 830 831 := slice_proof (lo:=830) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt831 : interval profileCheck 831 832 := slice_proof (lo:=831) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt832 : interval profileCheck 832 833 := slice_proof (lo:=832) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt833 : interval profileCheck 833 836 := slice_proof (lo:=833) (len:=3) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt836 : interval profileCheck 836 837 := slice_proof (lo:=836) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt837 : interval profileCheck 837 840 := slice_proof (lo:=837) (len:=3) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt840 : interval profileCheck 840 844 := slice_proof (lo:=840) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt844 : interval profileCheck 844 846 := slice_proof (lo:=844) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt846 : interval profileCheck 846 847 := slice_proof (lo:=846) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt847 : interval profileCheck 847 850 := slice_proof (lo:=847) (len:=3) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt850 : interval profileCheck 850 853 := slice_proof (lo:=850) (len:=3) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt853 : interval profileCheck 853 854 := slice_proof (lo:=853) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt854 : interval profileCheck 854 858 := slice_proof (lo:=854) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt858 : interval profileCheck 858 861 := slice_proof (lo:=858) (len:=3) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt861 : interval profileCheck 861 862 := slice_proof (lo:=861) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt862 : interval profileCheck 862 864 := slice_proof (lo:=862) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt864 : interval profileCheck 864 865 := slice_proof (lo:=864) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt865 : interval profileCheck 865 870 := slice_proof (lo:=865) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt870 : interval profileCheck 870 875 := slice_proof (lo:=870) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt875 : interval profileCheck 875 880 := slice_proof (lo:=875) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt880 : interval profileCheck 880 883 := slice_proof (lo:=880) (len:=3) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt883 : interval profileCheck 883 887 := slice_proof (lo:=883) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt887 : interval profileCheck 887 894 := slice_proof (lo:=887) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt894 : interval profileCheck 894 899 := slice_proof (lo:=894) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt899 : interval profileCheck 899 904 := slice_proof (lo:=899) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt904 : interval profileCheck 904 907 := slice_proof (lo:=904) (len:=3) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt907 : interval profileCheck 907 910 := slice_proof (lo:=907) (len:=3) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt910 : interval profileCheck 910 915 := slice_proof (lo:=910) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt915 : interval profileCheck 915 919 := slice_proof (lo:=915) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt919 : interval profileCheck 919 924 := slice_proof (lo:=919) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt924 : interval profileCheck 924 928 := slice_proof (lo:=924) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt928 : interval profileCheck 928 933 := slice_proof (lo:=928) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt933 : interval profileCheck 933 936 := slice_proof (lo:=933) (len:=3) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt936 : interval profileCheck 936 940 := slice_proof (lo:=936) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt940 : interval profileCheck 940 947 := slice_proof (lo:=940) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt947 : interval profileCheck 947 954 := slice_proof (lo:=947) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt954 : interval profileCheck 954 962 := slice_proof (lo:=954) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt962 : interval profileCheck 962 971 := slice_proof (lo:=962) (len:=9) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt971 : interval profileCheck 971 980 := slice_proof (lo:=971) (len:=9) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem profileCheckAt980 : interval profileCheck 980 983 := slice_proof (lo:=980) (len:=3) (by decide +kernel)
theorem allprofileCheck : ∀ i<983, profileCheck i = true := complete_interval (combined (combined (combined (combined (combined (combined (combined profileCheckAt0 (combined profileCheckAt4 profileCheckAt10)) (combined (combined profileCheckAt15 profileCheckAt20) (combined profileCheckAt27 profileCheckAt32))) (combined (combined (combined profileCheckAt38 profileCheckAt39) (combined profileCheckAt45 profileCheckAt50)) (combined (combined profileCheckAt55 profileCheckAt61) (combined profileCheckAt66 profileCheckAt71)))) (combined (combined (combined profileCheckAt76 (combined profileCheckAt80 profileCheckAt82)) (combined (combined profileCheckAt84 profileCheckAt88) (combined profileCheckAt93 profileCheckAt97))) (combined (combined (combined profileCheckAt102 profileCheckAt104) (combined profileCheckAt105 profileCheckAt106)) (combined (combined profileCheckAt107 profileCheckAt108) (combined profileCheckAt109 profileCheckAt110))))) (combined (combined (combined (combined profileCheckAt114 (combined profileCheckAt117 profileCheckAt118)) (combined (combined profileCheckAt119 profileCheckAt120) (combined profileCheckAt124 profileCheckAt129))) (combined (combined (combined profileCheckAt133 profileCheckAt139) (combined profileCheckAt142 profileCheckAt147)) (combined (combined profileCheckAt151 profileCheckAt153) (combined profileCheckAt157 profileCheckAt162)))) (combined (combined (combined profileCheckAt168 (combined profileCheckAt175 profileCheckAt181)) (combined (combined profileCheckAt184 profileCheckAt188) (combined profileCheckAt193 profileCheckAt198))) (combined (combined (combined profileCheckAt203 profileCheckAt209) (combined profileCheckAt215 profileCheckAt221)) (combined (combined profileCheckAt226 profileCheckAt231) (combined profileCheckAt235 profileCheckAt241)))))) (combined (combined (combined (combined (combined profileCheckAt246 (combined profileCheckAt250 profileCheckAt253)) (combined (combined profileCheckAt260 profileCheckAt267) (combined profileCheckAt273 profileCheckAt278))) (combined (combined (combined profileCheckAt285 profileCheckAt291) (combined profileCheckAt298 profileCheckAt305)) (combined (combined profileCheckAt312 profileCheckAt319) (combined profileCheckAt327 profileCheckAt334)))) (combined (combined (combined profileCheckAt340 (combined profileCheckAt346 profileCheckAt351)) (combined (combined profileCheckAt358 profileCheckAt365) (combined profileCheckAt371 profileCheckAt378))) (combined (combined (combined profileCheckAt386 profileCheckAt394) (combined profileCheckAt401 profileCheckAt408)) (combined (combined profileCheckAt414 profileCheckAt418) (combined profileCheckAt425 profileCheckAt432))))) (combined (combined (combined (combined profileCheckAt438 (combined profileCheckAt445 profileCheckAt451)) (combined (combined profileCheckAt457 profileCheckAt464) (combined profileCheckAt466 profileCheckAt472))) (combined (combined (combined profileCheckAt477 profileCheckAt481) (combined profileCheckAt486 profileCheckAt487)) (combined (combined profileCheckAt488 profileCheckAt492) (combined profileCheckAt493 profileCheckAt495)))) (combined (combined (combined (combined profileCheckAt502 profileCheckAt509) (combined profileCheckAt511 profileCheckAt512)) (combined (combined profileCheckAt513 profileCheckAt514) (combined profileCheckAt515 profileCheckAt516))) (combined (combined (combined profileCheckAt521 profileCheckAt528) (combined profileCheckAt530 profileCheckAt531)) (combined (combined profileCheckAt536 profileCheckAt541) (combined profileCheckAt546 profileCheckAt551))))))) (combined (combined (combined (combined (combined (combined profileCheckAt554 (combined profileCheckAt560 profileCheckAt564)) (combined (combined profileCheckAt568 profileCheckAt574) (combined profileCheckAt579 profileCheckAt584))) (combined (combined (combined profileCheckAt588 profileCheckAt592) (combined profileCheckAt598 profileCheckAt602)) (combined (combined profileCheckAt607 profileCheckAt613) (combined profileCheckAt619 profileCheckAt621)))) (combined (combined (combined profileCheckAt623 (combined profileCheckAt630 profileCheckAt636)) (combined (combined profileCheckAt642 profileCheckAt647) (combined profileCheckAt654 profileCheckAt661))) (combined (combined (combined profileCheckAt669 profileCheckAt676) (combined profileCheckAt683 profileCheckAt690)) (combined (combined profileCheckAt696 profileCheckAt702) (combined profileCheckAt707 profileCheckAt713))))) (combined (combined (combined (combined profileCheckAt720 (combined profileCheckAt726 profileCheckAt732)) (combined (combined profileCheckAt737 profileCheckAt740) (combined profileCheckAt741 profileCheckAt742))) (combined (combined (combined profileCheckAt743 profileCheckAt744) (combined profileCheckAt745 profileCheckAt746)) (combined (combined profileCheckAt747 profileCheckAt748) (combined profileCheckAt750 profileCheckAt752)))) (combined (combined (combined (combined profileCheckAt756 profileCheckAt759) (combined profileCheckAt761 profileCheckAt763)) (combined (combined profileCheckAt769 profileCheckAt770) (combined profileCheckAt771 profileCheckAt772))) (combined (combined (combined profileCheckAt773 profileCheckAt774) (combined profileCheckAt775 profileCheckAt776)) (combined (combined profileCheckAt777 profileCheckAt778) (combined profileCheckAt779 profileCheckAt780)))))) (combined (combined (combined (combined (combined profileCheckAt781 (combined profileCheckAt782 profileCheckAt785)) (combined (combined profileCheckAt791 profileCheckAt796) (combined profileCheckAt797 profileCheckAt799))) (combined (combined (combined profileCheckAt801 profileCheckAt804) (combined profileCheckAt805 profileCheckAt809)) (combined (combined profileCheckAt813 profileCheckAt814) (combined profileCheckAt815 profileCheckAt820)))) (combined (combined (combined profileCheckAt824 (combined profileCheckAt825 profileCheckAt826)) (combined (combined profileCheckAt827 profileCheckAt828) (combined profileCheckAt829 profileCheckAt830))) (combined (combined (combined profileCheckAt831 profileCheckAt832) (combined profileCheckAt833 profileCheckAt836)) (combined (combined profileCheckAt837 profileCheckAt840) (combined profileCheckAt844 profileCheckAt846))))) (combined (combined (combined (combined profileCheckAt847 (combined profileCheckAt850 profileCheckAt853)) (combined (combined profileCheckAt854 profileCheckAt858) (combined profileCheckAt861 profileCheckAt862))) (combined (combined (combined profileCheckAt864 profileCheckAt865) (combined profileCheckAt870 profileCheckAt875)) (combined (combined profileCheckAt880 profileCheckAt883) (combined profileCheckAt887 profileCheckAt894)))) (combined (combined (combined (combined profileCheckAt899 profileCheckAt904) (combined profileCheckAt907 profileCheckAt910)) (combined (combined profileCheckAt915 profileCheckAt919) (combined profileCheckAt924 profileCheckAt928))) (combined (combined (combined profileCheckAt933 profileCheckAt936) (combined profileCheckAt940 profileCheckAt947)) (combined (combined profileCheckAt954 profileCheckAt962) (combined profileCheckAt971 profileCheckAt980))))))))
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt0 : interval nodeCheck 0 38 := slice_proof (lo:=0) (len:=38) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt38 : interval nodeCheck 38 72 := slice_proof (lo:=38) (len:=34) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt72 : interval nodeCheck 72 89 := slice_proof (lo:=72) (len:=17) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt89 : interval nodeCheck 89 97 := slice_proof (lo:=89) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt97 : interval nodeCheck 97 109 := slice_proof (lo:=97) (len:=12) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt109 : interval nodeCheck 109 111 := slice_proof (lo:=109) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt111 : interval nodeCheck 111 120 := slice_proof (lo:=111) (len:=9) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt120 : interval nodeCheck 120 130 := slice_proof (lo:=120) (len:=10) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt130 : interval nodeCheck 130 148 := slice_proof (lo:=130) (len:=18) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt148 : interval nodeCheck 148 153 := slice_proof (lo:=148) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt153 : interval nodeCheck 153 169 := slice_proof (lo:=153) (len:=16) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt169 : interval nodeCheck 169 206 := slice_proof (lo:=169) (len:=37) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt206 : interval nodeCheck 206 275 := slice_proof (lo:=206) (len:=69) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt275 : interval nodeCheck 275 330 := slice_proof (lo:=275) (len:=55) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt330 : interval nodeCheck 330 379 := slice_proof (lo:=330) (len:=49) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt379 : interval nodeCheck 379 454 := slice_proof (lo:=379) (len:=75) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt454 : interval nodeCheck 454 503 := slice_proof (lo:=454) (len:=49) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt503 : interval nodeCheck 503 508 := slice_proof (lo:=503) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt508 : interval nodeCheck 508 509 := slice_proof (lo:=508) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt509 : interval nodeCheck 509 513 := slice_proof (lo:=509) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt513 : interval nodeCheck 513 530 := slice_proof (lo:=513) (len:=17) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt530 : interval nodeCheck 530 532 := slice_proof (lo:=530) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt532 : interval nodeCheck 532 552 := slice_proof (lo:=532) (len:=20) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt552 : interval nodeCheck 552 567 := slice_proof (lo:=552) (len:=15) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt567 : interval nodeCheck 567 579 := slice_proof (lo:=567) (len:=12) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt579 : interval nodeCheck 579 609 := slice_proof (lo:=579) (len:=30) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt609 : interval nodeCheck 609 620 := slice_proof (lo:=609) (len:=11) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt620 : interval nodeCheck 620 644 := slice_proof (lo:=620) (len:=24) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt644 : interval nodeCheck 644 646 := slice_proof (lo:=644) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt646 : interval nodeCheck 646 654 := slice_proof (lo:=646) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt654 : interval nodeCheck 654 657 := slice_proof (lo:=654) (len:=3) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt657 : interval nodeCheck 657 676 := slice_proof (lo:=657) (len:=19) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt676 : interval nodeCheck 676 756 := slice_proof (lo:=676) (len:=80) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt756 : interval nodeCheck 756 771 := slice_proof (lo:=756) (len:=15) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt771 : interval nodeCheck 771 773 := slice_proof (lo:=771) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt773 : interval nodeCheck 773 774 := slice_proof (lo:=773) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt774 : interval nodeCheck 774 782 := slice_proof (lo:=774) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt782 : interval nodeCheck 782 787 := slice_proof (lo:=782) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt787 : interval nodeCheck 787 796 := slice_proof (lo:=787) (len:=9) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt796 : interval nodeCheck 796 798 := slice_proof (lo:=796) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt798 : interval nodeCheck 798 800 := slice_proof (lo:=798) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt800 : interval nodeCheck 800 802 := slice_proof (lo:=800) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt802 : interval nodeCheck 802 803 := slice_proof (lo:=802) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt803 : interval nodeCheck 803 804 := slice_proof (lo:=803) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt804 : interval nodeCheck 804 807 := slice_proof (lo:=804) (len:=3) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt807 : interval nodeCheck 807 817 := slice_proof (lo:=807) (len:=10) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt817 : interval nodeCheck 817 825 := slice_proof (lo:=817) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt825 : interval nodeCheck 825 830 := slice_proof (lo:=825) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt830 : interval nodeCheck 830 831 := slice_proof (lo:=830) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt831 : interval nodeCheck 831 836 := slice_proof (lo:=831) (len:=5) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt836 : interval nodeCheck 836 840 := slice_proof (lo:=836) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt840 : interval nodeCheck 840 850 := slice_proof (lo:=840) (len:=10) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt850 : interval nodeCheck 850 852 := slice_proof (lo:=850) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt852 : interval nodeCheck 852 854 := slice_proof (lo:=852) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt854 : interval nodeCheck 854 856 := slice_proof (lo:=854) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt856 : interval nodeCheck 856 858 := slice_proof (lo:=856) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt858 : interval nodeCheck 858 859 := slice_proof (lo:=858) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt859 : interval nodeCheck 859 863 := slice_proof (lo:=859) (len:=4) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt863 : interval nodeCheck 863 865 := slice_proof (lo:=863) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt865 : interval nodeCheck 865 873 := slice_proof (lo:=865) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt873 : interval nodeCheck 873 874 := slice_proof (lo:=873) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt874 : interval nodeCheck 874 882 := slice_proof (lo:=874) (len:=8) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt882 : interval nodeCheck 882 889 := slice_proof (lo:=882) (len:=7) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt889 : interval nodeCheck 889 890 := slice_proof (lo:=889) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt890 : interval nodeCheck 890 892 := slice_proof (lo:=890) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt892 : interval nodeCheck 892 893 := slice_proof (lo:=892) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt893 : interval nodeCheck 893 935 := slice_proof (lo:=893) (len:=42) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt935 : interval nodeCheck 935 961 := slice_proof (lo:=935) (len:=26) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt961 : interval nodeCheck 961 972 := slice_proof (lo:=961) (len:=11) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem nodeCheckAt972 : interval nodeCheck 972 1013 := slice_proof (lo:=972) (len:=41) (by decide +kernel)
theorem allnodeCheck : ∀ i<1013, nodeCheck i = true := complete_interval (combined (combined (combined (combined (combined (combined nodeCheckAt0 nodeCheckAt38) (combined nodeCheckAt72 nodeCheckAt89)) (combined (combined nodeCheckAt97 nodeCheckAt109) (combined nodeCheckAt111 nodeCheckAt120))) (combined (combined (combined nodeCheckAt130 nodeCheckAt148) (combined nodeCheckAt153 nodeCheckAt169)) (combined (combined nodeCheckAt206 nodeCheckAt275) (combined nodeCheckAt330 (combined nodeCheckAt379 nodeCheckAt454))))) (combined (combined (combined (combined nodeCheckAt503 nodeCheckAt508) (combined nodeCheckAt509 nodeCheckAt513)) (combined (combined nodeCheckAt530 nodeCheckAt532) (combined nodeCheckAt552 (combined nodeCheckAt567 nodeCheckAt579)))) (combined (combined (combined nodeCheckAt609 nodeCheckAt620) (combined nodeCheckAt644 nodeCheckAt646)) (combined (combined nodeCheckAt654 nodeCheckAt657) (combined nodeCheckAt676 (combined nodeCheckAt756 nodeCheckAt771)))))) (combined (combined (combined (combined (combined nodeCheckAt773 nodeCheckAt774) (combined nodeCheckAt782 nodeCheckAt787)) (combined (combined nodeCheckAt796 nodeCheckAt798) (combined nodeCheckAt800 nodeCheckAt802))) (combined (combined (combined nodeCheckAt803 nodeCheckAt804) (combined nodeCheckAt807 nodeCheckAt817)) (combined (combined nodeCheckAt825 nodeCheckAt830) (combined nodeCheckAt831 (combined nodeCheckAt836 nodeCheckAt840))))) (combined (combined (combined (combined nodeCheckAt850 nodeCheckAt852) (combined nodeCheckAt854 nodeCheckAt856)) (combined (combined nodeCheckAt858 nodeCheckAt859) (combined nodeCheckAt863 (combined nodeCheckAt865 nodeCheckAt873)))) (combined (combined (combined nodeCheckAt874 nodeCheckAt882) (combined nodeCheckAt889 nodeCheckAt890)) (combined (combined nodeCheckAt892 nodeCheckAt893) (combined nodeCheckAt935 (combined nodeCheckAt961 nodeCheckAt972)))))))
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCheckAt0 : interval rootCheck 0 1 := slice_proof (lo:=0) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCheckAt1 : interval rootCheck 1 2 := slice_proof (lo:=1) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCheckAt2 : interval rootCheck 2 3 := slice_proof (lo:=2) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCheckAt3 : interval rootCheck 3 4 := slice_proof (lo:=3) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCheckAt4 : interval rootCheck 4 5 := slice_proof (lo:=4) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCheckAt5 : interval rootCheck 5 6 := slice_proof (lo:=5) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCheckAt6 : interval rootCheck 6 7 := slice_proof (lo:=6) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCheckAt7 : interval rootCheck 7 8 := slice_proof (lo:=7) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCheckAt8 : interval rootCheck 8 9 := slice_proof (lo:=8) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCheckAt9 : interval rootCheck 9 10 := slice_proof (lo:=9) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCheckAt10 : interval rootCheck 10 11 := slice_proof (lo:=10) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCheckAt11 : interval rootCheck 11 12 := slice_proof (lo:=11) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCheckAt12 : interval rootCheck 12 13 := slice_proof (lo:=12) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCheckAt13 : interval rootCheck 13 14 := slice_proof (lo:=13) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCheckAt14 : interval rootCheck 14 15 := slice_proof (lo:=14) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCheckAt15 : interval rootCheck 15 16 := slice_proof (lo:=15) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCheckAt16 : interval rootCheck 16 17 := slice_proof (lo:=16) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCheckAt17 : interval rootCheck 17 18 := slice_proof (lo:=17) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCheckAt18 : interval rootCheck 18 19 := slice_proof (lo:=18) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCheckAt19 : interval rootCheck 19 20 := slice_proof (lo:=19) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCheckAt20 : interval rootCheck 20 21 := slice_proof (lo:=20) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCheckAt21 : interval rootCheck 21 22 := slice_proof (lo:=21) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCheckAt22 : interval rootCheck 22 23 := slice_proof (lo:=22) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCheckAt23 : interval rootCheck 23 24 := slice_proof (lo:=23) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCheckAt24 : interval rootCheck 24 25 := slice_proof (lo:=24) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCheckAt25 : interval rootCheck 25 26 := slice_proof (lo:=25) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCheckAt26 : interval rootCheck 26 27 := slice_proof (lo:=26) (len:=1) (by decide +kernel)
theorem allrootCheck : ∀ i<27, rootCheck i = true := complete_interval (combined (combined (combined (combined rootCheckAt0 (combined rootCheckAt1 rootCheckAt2)) (combined rootCheckAt3 (combined rootCheckAt4 rootCheckAt5))) (combined (combined rootCheckAt6 (combined rootCheckAt7 rootCheckAt8)) (combined (combined rootCheckAt9 rootCheckAt10) (combined rootCheckAt11 rootCheckAt12)))) (combined (combined (combined rootCheckAt13 (combined rootCheckAt14 rootCheckAt15)) (combined (combined rootCheckAt16 rootCheckAt17) (combined rootCheckAt18 rootCheckAt19))) (combined (combined rootCheckAt20 (combined rootCheckAt21 rootCheckAt22)) (combined (combined rootCheckAt23 rootCheckAt24) (combined rootCheckAt25 rootCheckAt26)))))
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCertAt0 : interval rootCert 0 3 := slice_proof (lo:=0) (len:=3) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCertAt3 : interval rootCert 3 4 := slice_proof (lo:=3) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCertAt4 : interval rootCert 4 6 := slice_proof (lo:=4) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCertAt6 : interval rootCert 6 7 := slice_proof (lo:=6) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCertAt7 : interval rootCert 7 8 := slice_proof (lo:=7) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCertAt8 : interval rootCert 8 9 := slice_proof (lo:=8) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCertAt9 : interval rootCert 9 11 := slice_proof (lo:=9) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCertAt11 : interval rootCert 11 12 := slice_proof (lo:=11) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCertAt12 : interval rootCert 12 15 := slice_proof (lo:=12) (len:=3) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCertAt15 : interval rootCert 15 18 := slice_proof (lo:=15) (len:=3) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCertAt18 : interval rootCert 18 19 := slice_proof (lo:=18) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCertAt19 : interval rootCert 19 20 := slice_proof (lo:=19) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCertAt20 : interval rootCert 20 21 := slice_proof (lo:=20) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCertAt21 : interval rootCert 21 22 := slice_proof (lo:=21) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCertAt22 : interval rootCert 22 23 := slice_proof (lo:=22) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCertAt23 : interval rootCert 23 25 := slice_proof (lo:=23) (len:=2) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCertAt25 : interval rootCert 25 26 := slice_proof (lo:=25) (len:=1) (by decide +kernel)
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem rootCertAt26 : interval rootCert 26 27 := slice_proof (lo:=26) (len:=1) (by decide +kernel)
theorem allrootCert : ∀ i<27, rootCert i = true := complete_interval (combined (combined (combined (combined rootCertAt0 rootCertAt3) (combined rootCertAt4 rootCertAt6)) (combined (combined rootCertAt7 rootCertAt8) (combined rootCertAt9 (combined rootCertAt11 rootCertAt12)))) (combined (combined (combined rootCertAt15 rootCertAt18) (combined rootCertAt19 rootCertAt20)) (combined (combined rootCertAt21 rootCertAt22) (combined rootCertAt23 (combined rootCertAt25 rootCertAt26)))))
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem impossible : ¬ Easy edge 6 (fun _ => True) := by
  apply compact_sound (by decide +kernel) allobsCheck allsensorCheck allcachedGeom allprofileCheck allnodeCheck allrootCheck allrootCert

end L4187

open L4187

theorem PEqualNP.Outside.L_meta_4187 :
have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : (Fin (14 : ℕ) → Bool) → Prop := fun (x3 : Fin (14 : ℕ) → Bool) => (x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.true → ¬x2 (Function.update x3 x4 Bool.false)) ∨ ¬x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.false → x2 (Function.update x3 x4 Bool.true); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x6 : Fin (14 : ℕ) → Bool), x3 x6 → (x4.eval (List.ofFn x6 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval [x6 (0 : Fin (14 : ℕ)), x6 (1 : Fin (14 : ℕ))]]) = Bool.true ↔ x2 x6)) → (7 : ℕ) ≤ List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.casesOn x7.op Bool.true Bool.false Bool.false (fun (x8 : ℕ) => Bool.false) Bool.false) x4.gates := by
  dsimp only
  intro C hm tests
  have h := start C hm (by
    intro x hx
    simpa only [input,target,edges,PEqualNP.CircuitLowerBounds.GateOp.eval,List.any_cons,List.any_nil,
      id_eq,Bool.or_false] using tests x hx)
  have lower : 7 ≤ C.gates.countP countAnd := by
    by_contra! small
    exact impossible (enlarge h (by omega))
  change 7 ≤ C.gates.countP _
  convert lower using 2
  funext g
  cases g with
  | mk op ins => cases op <;> rfl
