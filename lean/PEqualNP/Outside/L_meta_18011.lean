import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_18011_aux

def step (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]

def run (gs : List Gate) (ws : List Bool) := gs.foldl step ws

def down (p i : ℕ) : ℕ := if i < p then i else i-1

def lower (p : ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map (down p)⟩

theorem run_append (gs hs : List Gate) (ws : List Bool) :
    run (gs++hs) ws = run hs (run gs ws) := by simp [run, List.foldl_append]

theorem run_suffix (gs : List Gate) (ws : List Bool) : ∃ t, run gs ws = ws++t ∧ t.length = gs.length := by
  induction gs generalizing ws with
  | nil => exact ⟨[], by simp [run], rfl⟩
  | cons g gs ih =>
    obtain ⟨t,h,hl⟩ := ih (step ws g)
    exact ⟨_::t, by simpa [run,step,List.append_assoc] using h, by simp [hl]⟩

theorem down_lookup (l r : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ b :: r).getD i false = (l ++ r).getD (down l.length i) false := by
  by_cases h : i < l.length
  · simp [down,h,List.getD_eq_getElem?_getD,List.getElem?_append_left h]
  · have hle : l.length ≤ i := by omega
    have hi' : l.length ≤ i-1 := by omega
    have hadd : i - l.length = (i - 1 - l.length) + 1 := by omega
    simp only [down,if_neg h,List.getD_eq_getElem?_getD,List.getElem?_append_right hle,
      List.getElem?_append_right hi',hadd,List.getElem?_cons_succ]

theorem run_down (gs : List Gate) (l r : List Bool) (b : Bool)
    (avoid : ∀ g ∈ gs, l.length ∉ g.inputs) :
    ∃ t, run gs (l ++ b :: r) = l ++ b :: (r++t) ∧
      run (gs.map (lower l.length)) (l ++ r) = l ++ (r++t) := by
  induction gs generalizing r with
  | nil => exact ⟨[], by simp [run], by simp [run]⟩
  | cons g gs ih =>
    let z := g.op.eval (g.inputs.map fun i => (l ++ b :: r).getD i false)
    have eqv : (lower l.length g).op.eval
        ((lower l.length g).inputs.map fun i => (l++r).getD i false) = z := by
      change g.op.eval _ = g.op.eval _
      congr 1
      simp only [lower, List.map_map]
      apply List.map_congr_left
      intro k hk
      exact (down_lookup l r b k (fun he => avoid g (by simp) (he ▸ hk))).symm
    obtain ⟨t, h1,h2⟩ := ih (r++[z]) (fun t ht => avoid t (List.mem_cons_of_mem _ ht))
    refine ⟨z::t, ?_, ?_⟩
    · change run gs (step _ g) = _
      simpa only [step,List.append_assoc,List.cons_append,List.singleton_append,List.nil_append,z] using h1
    · change run (gs.map (lower l.length)) (step _ (lower l.length g)) = _
      simp only [step,eqv,List.append_assoc]
      simpa [List.append_assoc] using h2

def Good (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), (gs[j].op = .and ∨ gs[j].op = .or) ∧
    gs[j].inputs.length = 2 ∧ ∀ i ∈ gs[j].inputs, i < n+j

theorem good_iff {n : ℕ} {C : Circuit} : Good n C.gates ↔ IsAO2 n C := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hg
      exact (h i hi).1
    · intro j hj w hw
      apply (h j hj).2.2
      simpa [gateAt, List.getElem?_eq_getElem hj] using hw
    · intro g hg
      obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hg
      exact (h i hi).2.1
  · intro h j hj
    refine ⟨h.1 _ (List.getElem_mem hj), h.2.2 _ (List.getElem_mem hj), ?_⟩
    intro i hi
    exact h.2.1 j hj i (by simpa [gateAt, List.getElem?_eq_getElem hj] using hi)

def At (n : ℕ) (g : Gate) :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i < n

theorem good_cons {n : ℕ} {g : Gate} {gs} : Good n (g::gs) ↔ At n g ∧ Good (n+1) gs := by
  constructor
  · intro h
    have head := h 0 (by simp)
    change At (n+0) g at head
    refine ⟨by simpa using head, ?_⟩
    intro j hj
    have q := h (j+1) (by simp [hj])
    change At (n+(j+1)) gs[j] at q
    change At ((n+1)+j) gs[j]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using q
  · rintro ⟨h,hs⟩ j hj
    cases j with
    | zero => simpa [At] using h
    | succ j =>
      have ht := hs j (by simpa using hj)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht

theorem good_append {n : ℕ} (a b : List Gate) :
    Good n (a++b) ↔ Good n a ∧ Good (n+a.length) b := by
  induction a generalizing n with
  | nil => simp [Good]
  | cons g a ih =>
    simp only [List.cons_append,good_cons, ih, List.length_cons]
    simp [and_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem good_down {n p : ℕ} (gs : List Gate) (hp : p < n)
    (ha : Good n gs) (avoid : ∀ g ∈ gs, p ∉ g.inputs) :
    Good (n-1) (gs.map (lower p)) := by
  induction gs generalizing n with
  | nil => simpa [Good]
  | cons g gs ih =>
    obtain ⟨⟨hop,har,hins⟩, ht⟩ := good_cons.mp ha
    apply good_cons.mpr
    constructor
    · refine ⟨hop, by simpa [lower] using har, ?_⟩
      intro i hi
      obtain ⟨a,hm,rfl⟩ := List.mem_map.mp hi
      have hai := hins a hm
      have hne : a ≠ p := fun he => avoid g (by simp) (he ▸ hm)
      unfold down
      split <;> omega
    · have h := ih (by omega : p < n+1) ht (fun k hk => avoid k (List.mem_cons_of_mem _ hk))
      rwa [show n+1-1=n-1+1 by omega] at h

theorem value_down (gs : List Gate) (l r : List Bool) (b : Bool) (i : ℕ)
    (avoid : ∀ g ∈ gs, l.length ∉ g.inputs) (hi : i ≠ l.length) :
    (run gs (l++b::r)).getD i false = (run (gs.map (lower l.length)) (l++r)).getD (down l.length i) false := by
  obtain ⟨t,h1,h2⟩ := run_down gs l r b avoid
  rw [h1,h2]
  exact down_lookup _ _ _ _ hi

def slots (C : Circuit) := C.output :: C.gates.flatMap Gate.inputs

theorem remove_unread (C : Circuit) (n : ℕ) (h : Good n C.gates)
    (j : ℕ) (hj : j < C.gates.length) (unused : n+j ∉ slots C) :
    ∃ D : Circuit, Good n D.gates ∧ D.size < C.size ∧ ∀ x : Fin n → Bool,
      D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  let a := C.gates.take j
  let g := C.gates[j]
  let b := C.gates.drop (j+1)
  have hs : a ++ g::b = C.gates := by
    have split := List.take_append_drop j C.gates
    rwa [List.drop_eq_getElem_cons hj] at split
  have la : a.length = j := by simp [a, Nat.min_eq_left hj.le]
  have ho : C.output ≠ n+j := fun e => unused (by simp [slots,e])
  have no : ∀ g ∈ b, n+j ∉ g.inputs := by
    intro t ht hm
    exact unused (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨t,List.mem_of_mem_drop ht,hm⟩))
  have leg : Good n a ∧ At (n+j) g ∧ Good (n+j+1) b := by
    have hh := h
    rw [← hs,good_append,la,good_cons] at hh
    exact hh
  let D : Circuit := ⟨a ++ b.map (lower (n+j)),down (n+j) C.output⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · apply (good_append _ _).mpr
    refine ⟨leg.1, ?_⟩
    rw [la]
    simpa using good_down b (by omega : n+j < n+j+1) leg.2.2 no
  · have hh := congrArg List.length hs
    simp [Circuit.size,D] at *
    omega
  · intro x
    let w := run a (List.ofFn x)
    obtain ⟨t,ht,hl⟩ := run_suffix a (List.ofFn x)
    have lw : w.length = n+j := by simp [w,ht,hl,la]
    let z := g.op.eval (g.inputs.map fun i => w.getD i false)
    have v := value_down b w [] z C.output (by simpa [lw] using no) (by simpa [lw] using ho)
    change (run (a++b.map (lower (n+j))) (List.ofFn x)).getD _ false =
      (run C.gates (List.ofFn x)).getD _ false
    rw [← hs,run_append,run_append]
    rw [lw] at v
    simpa [w,step,run,List.append_assoc,D,z] using v.symm

theorem live_version {n : ℕ} (C : Circuit) (h : Good n C.gates) :
    ∃ D : Circuit, Good n D.gates ∧ D.size ≤ C.size ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
      ∀ j < D.size, n+j ∈ slots D := by
  classical
  let Q (s : ℕ) := ∃ D : Circuit, Good n D.gates ∧
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧ D.size=s
  have existsQ : ∃ s, Q s := ⟨_, C, h, fun _ => rfl, rfl⟩
  obtain ⟨D,hd,eq,size⟩ : Q (Nat.find existsQ) := Nat.find_spec existsQ
  refine ⟨D,hd,?_,eq,?_⟩
  · rw [size]
    exact Nat.find_min' existsQ (show Q C.size from ⟨C,h,fun _ => rfl,rfl⟩)
  · intro j hj
    by_contra hn
    obtain ⟨D',hd',short,eq'⟩ := remove_unread D n hd j hj hn
    apply Nat.find_min existsQ (show D'.size < Nat.find existsQ by omega)
    exact ⟨D',hd',fun x => (eq' x).trans (eq x),rfl⟩

theorem insert_form (p : Fin 10) (y : Fin 9 → Bool) (b : Bool) :
  List.ofFn (p.insertNth b y) = (List.ofFn y).take p ++ b::(List.ofFn y).drop p := by
  fin_cases p <;> rfl

theorem elen (p : Fin 10) (y : Fin 9 → Bool) : ((List.ofFn y).take p).length = p := by
  simp [List.length_take,Nat.min_eq_left (show (p:ℕ) ≤ 9 by omega)]

theorem unaffected_raw : ∀ (p : Fin 10), ∃ q : Fin 10, ∀ (y : Fin 9 → Bool),
    (q.insertNth (α := fun _ => Bool) false y) p = (q.insertNth (α := fun _ => Bool) true y) p := by
  intro p
  fin_cases p <;> first | exact ⟨0,fun _ => rfl⟩ | exact ⟨1,fun _ => rfl⟩

theorem output_not_raw (C : Circuit)
    (ess : ∀ p : Fin 10, ∃ y : Fin 9 → Bool,
      C.eval (List.ofFn (p.insertNth false y)) ≠ C.eval (List.ofFn (p.insertNth true y))) :
    ∀ p : Fin 10, C.output ≠ p := by
  intro p hout
  obtain ⟨q,hq⟩ := unaffected_raw p
  obtain ⟨y,hy⟩ := ess q
  apply hy
  have h (b : Bool) : C.eval (List.ofFn (q.insertNth b y)) = (q.insertNth (α := fun _ => Bool) b y) p := by
    obtain ⟨t,ht,_⟩ := run_suffix C.gates (List.ofFn (q.insertNth b y))
    change (run C.gates _).getD _ _ = _
    rw [ht,hout,List.getD_append _ _ _ _ (by simp)]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  rw [h,h,hq]

theorem read_raw (C : Circuit) (p : Fin 10) (ho : C.output ≠ p)
    (ess : ∃ y : Fin 9 → Bool,
      C.eval (List.ofFn (p.insertNth false y)) ≠ C.eval (List.ofFn (p.insertNth true y))) :
    (p:ℕ) ∈ C.gates.flatMap Gate.inputs := by
  by_contra hn
  obtain ⟨y,h⟩ := ess
  apply h
  let l := (List.ofFn y).take p
  let r := (List.ofFn y).drop p
  have len : l.length = p := elen p y
  have avoid : ∀ g ∈ C.gates, l.length ∉ g.inputs := by
    intro g hg hm
    exact hn (List.mem_flatMap.mpr ⟨g,hg,len ▸ hm⟩)
  have evalB (b:Bool) := value_down C.gates l r b C.output avoid (by rwa [len])
  change (run C.gates _).getD _ _ = (run C.gates _).getD _ _
  rw [insert_form,insert_form,evalB false,evalB true]

private lemma gateSlotBound (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g tail ih =>
    have hg := h g List.mem_cons_self
    have ht := ih (fun t hm => h t (List.mem_cons_of_mem _ hm))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

private lemma countBound (xs : List ℕ) (S : Finset ℕ) :
    ∑ i ∈ S, xs.count i ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib, List.length_cons]
    by_cases h : a ∈ S <;> simp [h, Finset.sum_ite_eq] <;> omega

theorem split_unique (x2 : ℕ) : ∀ gs : List Gate, (gs.flatMap Gate.inputs).count x2 = 1 →
    ∃ pre g post, gs = pre ++ g :: post ∧ x2 ∈ g.inputs ∧ (∀ h ∈ pre, x2 ∉ h.inputs) ∧
      (∀ h ∈ post, x2 ∉ h.inputs) := by
  intro gs
  induction gs with
  | nil => intro h; simp at h
  | cons h t ih =>
    intro hc
    rw [List.flatMap_cons, List.count_append] at hc
    by_cases h0 : h.inputs.count x2 = 0
    · rw [h0, Nat.zero_add] at hc
      obtain ⟨pre, g, post, rfl, hg, hpre, hpost⟩ := ih hc
      refine ⟨h :: pre, g, post, rfl, hg, ?_, hpost⟩
      intro h' hh'
      rcases List.mem_cons.1 hh' with rfl | hh'
      · exact List.count_eq_zero.1 h0
      · exact hpre h' hh'
    · have h1 : (t.flatMap Gate.inputs).count x2 = 0 := by omega
      refine ⟨[], h, t, rfl, List.count_pos_iff.1 (Nat.pos_of_ne_zero h0), by simp, ?_⟩
      intro h' hh' hx
      have : x2 ∈ t.flatMap Gate.inputs := List.mem_flatMap.2 ⟨h', hh', hx⟩
      exact (List.count_eq_zero.1 h1) this


theorem once_input (C : Circuit) (hg : Good 10 C.gates) (hs : C.size ≤ 18)
    (live : ∀ j < C.size, 10+j ∈ slots C)
    (ess : ∀ p : Fin 10, ∃ y : Fin 9 → Bool,
      C.eval (List.ofFn (p.insertNth false y)) ≠ C.eval (List.ofFn (p.insertNth true y))) :
    ∃ p : Fin 10, (C.gates.flatMap Gate.inputs).count (p:ℕ) = 1 := by
  classical
  by_contra! bad
  have counted : ∑ i ∈ Finset.range (10+C.size), (slots C).count i ≤ (slots C).length :=
    countBound _ _
  rw [Finset.sum_range_add] at counted
  have hi : ∀ i ∈ Finset.range 10, 2 ≤ (slots C).count i := by
    intro i hi
    let p : Fin 10 := ⟨i,Finset.mem_range.mp hi⟩
    have neq := output_not_raw C ess p
    have hpos := List.count_pos_iff.mpr (read_raw C p neq (ess p))
    have hbad := bad p
    change 0 < (C.gates.flatMap Gate.inputs).count i at hpos
    change (C.gates.flatMap Gate.inputs).count i ≠ 1 at hbad
    have hge : 2 ≤ (C.gates.flatMap Gate.inputs).count i := by omega
    exact hge.trans (by simp [slots,List.count_cons])
  have raw := Finset.sum_le_sum hi
  have internal : ∀ j ∈ Finset.range C.size, 1 ≤ (slots C).count (10+j) := by
    intro j hj
    exact List.count_pos_iff.mpr (live j (Finset.mem_range.mp hj))
  have others := Finset.sum_le_sum internal
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul,mul_one] at raw others
  have cb := gateSlotBound C.gates (fun g gm => ((good_iff.mp hg).2.2 g gm).le)
  have leSlots : (slots C).length ≤ 2*C.size+1 := by
    change (C.gates.flatMap Gate.inputs).length+1 ≤ 2*C.gates.length+1
    omega
  change C.gates.length ≤ 18 at hs
  change C.gates.length ≤ _ at others
  change (slots C).length ≤ 2 * C.gates.length + 1 at leSlots
  omega

def combine (flag a b : Bool) := if flag then a && b else a || b

theorem gate_choice {N p : ℕ} {g : Gate} (hg : At N g) (mem : p ∈ g.inputs)
    (once : g.inputs.count p ≤ 1) :
    ∃ q < N, q ≠ p ∧ ∃ flag : Bool, ∀ w : List Bool,
      g.op.eval (g.inputs.map fun i => w.getD i false) =
        combine flag (w.getD p false) (w.getD q false) := by
  obtain ⟨hop,hl,reads⟩ := hg
  obtain ⟨a,b,he⟩ := List.length_eq_two.mp hl
  rw [he] at mem once reads
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl
  · refine ⟨b,reads b (by simp),?_,?_⟩
    · rintro rfl
      simp at once
    · rcases hop with e | e
      · exact ⟨true,fun w => by simp [e,he,combine,GateOp.eval]⟩
      · exact ⟨false,fun w => by simp [e,he,combine,GateOp.eval]⟩
  · refine ⟨a,reads a (by simp),?_,?_⟩
    · rintro rfl
      simp at once
    · rcases hop with e | e
      · exact ⟨true,fun w => by simp [e,he,combine,GateOp.eval,Bool.and_comm]⟩
      · exact ⟨false,fun w => by simp [e,he,combine,GateOp.eval,Bool.or_comm]⟩

theorem cut_run (a b : List Gate) (g : Gate) (l r : List Bool) (x flag : Bool) (q o : ℕ)
    (avoidA : ∀ h ∈ a, l.length ∉ h.inputs) (avoidB : ∀ h ∈ b, l.length ∉ h.inputs)
    (hq : q ≠ l.length) (ho : o ≠ l.length)
    (hg : ∀ w : List Bool, g.op.eval (g.inputs.map fun i => w.getD i false) =
      combine flag (w.getD l.length false) (w.getD q false)) :
    (run (a++g::b) (l++x::r)).getD o false =
    (run (b.map (lower l.length))
      (run (a.map (lower l.length)) (l++r) ++
      [combine flag x ((run (a.map (lower l.length)) (l++r)).getD (down l.length q) false)])).getD (down l.length o) false := by
  obtain ⟨t,big,small⟩ := run_down a l r x avoidA
  rw [run_append,big,small]
  change (run b (step (l++x::(r++t)) g)).getD _ _ = _
  unfold step
  rw [hg,down_lookup l (r++t) x q hq]
  have pin : (l++x::(r++t)).getD l.length false = x := by simp [List.getD_eq_getElem?_getD]
  rw [pin]
  let z := combine flag x ((l++(r++t)).getD (down l.length q) false)
  have eq := value_down b l ((r++t)++[z]) x o avoidB ho
  simpa only [List.append_assoc,List.cons_append,z] using eq

end PEqualNP.Outside.L_meta_18011_aux

open PEqualNP.Outside.L_meta_18011_aux in
theorem PEqualNP.Outside.L_meta_18011 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 → x1.size ≤ (18 : ℕ) → (∀ (x4 : Fin (10 : ℕ)), ∃ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn (x4.insertNth Bool.false x5)) ≠ x1.eval (List.ofFn (x4.insertNth Bool.true x5))) → ∃ (x5 : Fin (10 : ℕ)) (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : Bool), PEqualNP.TopForm.IsAO2 (9 : ℕ) x6 ∧ PEqualNP.TopForm.IsAO2 ((10 : ℕ) + x6.size) x7 ∧ x6.size + x7.size ≤ (17 : ℕ) ∧ x6.output < (9 : ℕ) + x6.size ∧ ∀ (x9 : Fin (9 : ℕ) → Bool) (x10 : Bool), x1.eval (List.ofFn (x5.insertNth x10 x9)) = x7.eval (x6.wires (List.ofFn x9) ++ [if x8 = Bool.true then x10 && x6.eval (List.ofFn x9) else x10 || x6.eval (List.ofFn x9)]) := by
  intro C hc cap essential
  obtain ⟨D,hd,le,eq,live⟩ := live_version C (good_iff.mpr hc)
  have ess : ∀ p : Fin 10, ∃ y : Fin 9 → Bool, D.eval (List.ofFn (p.insertNth false y)) ≠
      D.eval (List.ofFn (p.insertNth true y)) := by
    intro p
    obtain ⟨y,hy⟩ := essential p
    exact ⟨y, by simpa only [eq] using hy⟩
  obtain ⟨p,once⟩ := once_input D hd (le.trans cap) live ess
  have ho := output_not_raw D ess p
  obtain ⟨a,g,b,hs,hm,na,nb⟩ := split_unique (p:ℕ) D.gates once
  have leg := hd
  rw [hs,good_append,good_cons] at leg
  have gcount : g.inputs.count (p:ℕ) ≤ 1 := by
    rw [hs,List.flatMap_append,List.flatMap_cons,List.count_append,List.count_append] at once
    omega
  obtain ⟨q,hq,hqp,flag,op⟩ := gate_choice leg.2.1 hm gcount
  let A : Circuit := ⟨a.map (lower p),down p q⟩
  let B : Circuit := ⟨b.map (lower p),down p D.output⟩
  have sizeA : A.size = a.length := by simp [Circuit.size,A]
  have sizeB : B.size = b.length := by simp [Circuit.size,B]
  refine ⟨p,A,B,flag,good_iff.mp ?_,good_iff.mp ?_,?_,?_,?_⟩
  · exact good_down a p.isLt leg.1 na
  · rw [sizeA]
    exact (by simpa using good_down b (show (p:ℕ) < 10+a.length+1 by omega) leg.2.2 nb)
  · have sizeD : D.size = a.length + 1 + b.length := by simp [Circuit.size,hs]; omega
    omega
  · rw [sizeA]
    change down p q < 9+a.length
    unfold down
    split <;> omega
  · intro y z
    rw [← eq]
    let l := (List.ofFn y).take p
    let r := (List.ofFn y).drop p
    have len : l.length = p := elen p y
    have lr : l++r=List.ofFn y := List.take_append_drop _ _
    have ev := cut_run a b g l r z flag q D.output (by simpa [len] using na)
      (by simpa [len] using nb) (by simpa [len] using hqp) (by simpa [len] using ho)
      (by simpa [len] using op)
    change (run D.gates (List.ofFn (p.insertNth z y))).getD D.output false =
      (run (b.map (lower p)) (run (a.map (lower p)) (List.ofFn y) ++
        [combine flag z ((run (a.map (lower p)) (List.ofFn y)).getD (down p q) false)])).getD (down p D.output) false
    rw [hs,insert_form]
    simpa only [len, lr] using ev
