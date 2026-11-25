import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16501.Frame
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def target (x : Fin 6 → Bool) := Nat.testBit (4008372968 * 2 ^ 32 + 4008241864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def witness : Circuit := ⟨[⟨.or,[2,4]⟩, ⟨.and,[3,6]⟩, ⟨.or,[2,7]⟩, ⟨.and,[1,8]⟩, ⟨.and,[2,4]⟩, ⟨.and,[5,6]⟩, ⟨.or,[10,11]⟩, ⟨.or,[3,12]⟩, ⟨.or,[1,13]⟩, ⟨.and,[0,14]⟩, ⟨.or,[9,15]⟩],16⟩
theorem wmono : Monotone2 witness := by simp [Monotone2,witness]
theorem wcomputes : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x)=target x := by decide +kernel
end PEqualNP.Outside.L_meta_16501.Frame

namespace PEqualNP.Outside.L_meta_16501

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Word := BitVec 64
def ones : Word := BitVec.allOnes 64
def goal : Word := 0xeeeaeae8eee8eac8
def roots : List Word := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

def join (d : Bool) (a b : Word) : Word := if d then a ||| b else a &&& b

def Live (b n : Nat) (S : Finset Word) : Prop :=
  ∀ (P : Nat → Nat → Finset Word → Prop),
    P 0 0 {goal} →
    (∀ {i j : Nat} {a x : Word} {U : Finset Word} (d : Bool), a ≠ x →
      join d a x ∉ insert a (insert x U) → (join d a x ≠ 0 ∧ join d a x ≠ ones) →
      P i j (insert (join d a x) U) → P (i+1) j (insert a (insert x U))) →
    (∀ {i j : Nat} {a : Word} {U : Finset Word},
      ~~~a ∉ insert a U → (~~~a ≠ 0 ∧ ~~~a ≠ ones) →
      P i j (insert (~~~a) U) → P i (j+1) (insert a U)) →
    P b n S

theorem Live.done : Live 0 0 {goal} :=
  fun _ done _ _ => done

theorem Live.binary {b n : Nat} {a x : Word} {U : Finset Word} (d : Bool) (ne : a ≠ x)
    (fresh : join d a x ∉ insert a (insert x U))
    (proper : join d a x ≠ 0 ∧ join d a x ≠ ones)
    (tail : Live b n (insert (join d a x) U)) :
    Live (b+1) n (insert a (insert x U)) :=
  fun P done binary inversion => binary d ne fresh proper (tail P done binary inversion)

theorem Live.inversion {b n : Nat} {a : Word} {U : Finset Word}
    (fresh : ~~~a ∉ insert a U) (proper : ~~~a ≠ 0 ∧ ~~~a ≠ ones)
    (tail : Live b n (insert (~~~a) U)) : Live b (n+1) (insert a U) :=
  fun P done binary inversion => inversion fresh proper (tail P done binary inversion)

theorem Live.recPlain {motive : ∀ {b n S}, Live b n S → Prop}
    (done : motive Live.done)
    (binary : ∀ {b n : Nat} {a x : Word} {U : Finset Word} (d : Bool) (ne : a ≠ x)
      (fresh : join d a x ∉ insert a (insert x U))
      (proper : join d a x ≠ 0 ∧ join d a x ≠ ones)
      (tail : Live b n (insert (join d a x) U)),
      motive tail → motive (Live.binary d ne fresh proper tail))
    (inversion : ∀ {b n : Nat} {a : Word} {U : Finset Word}
      (fresh : ~~~a ∉ insert a U) (proper : ~~~a ≠ 0 ∧ ~~~a ≠ ones)
      (tail : Live b n (insert (~~~a) U)),
      motive tail → motive (Live.inversion fresh proper tail))
    {b n : Nat} {S : Finset Word} (h : Live b n S) : motive h := by
  let P (b n : Nat) (S : Finset Word) : Prop := ∃ p : Live b n S, motive p
  have result : P b n S := by
    apply h P
    · exact ⟨Live.done,done⟩
    · intro i j a x U d ne fresh proper tail
      obtain ⟨p,ih⟩ := tail
      exact ⟨Live.binary d ne fresh proper p,binary d ne fresh proper p ih⟩
    · intro i j a U fresh proper tail
      obtain ⟨p,ih⟩ := tail
      exact ⟨Live.inversion fresh proper p,inversion fresh proper p ih⟩
  obtain ⟨_,proof⟩ := result
  exact proof

theorem Live.casesPlain {motive : ∀ {b n S}, Live b n S → Prop}
    (done : motive Live.done)
    (binary : ∀ {b n : Nat} {a x : Word} {U : Finset Word} (d : Bool) (ne : a ≠ x)
      (fresh : join d a x ∉ insert a (insert x U))
      (proper : join d a x ≠ 0 ∧ join d a x ≠ ones)
      (tail : Live b n (insert (join d a x) U)), motive (Live.binary d ne fresh proper tail))
    (inversion : ∀ {b n : Nat} {a : Word} {U : Finset Word}
      (fresh : ~~~a ∉ insert a U) (proper : ~~~a ≠ 0 ∧ ~~~a ≠ ones)
      (tail : Live b n (insert (~~~a) U)), motive (Live.inversion fresh proper tail))
    {b n : Nat} {S : Finset Word} (h : Live b n S) : motive h := by
  apply Live.recPlain (motive := @motive) done _ _ h
  · intro i j a x U d ne fresh proper tail _
    exact binary d ne fresh proper tail
  · intro i j a U fresh proper tail _
    exact inversion fresh proper tail

theorem goal_proper : goal ≠ 0 ∧ goal ≠ ones := by decide +kernel

def assignment (r : Fin 64) : Fin 6 → Bool := fun i => r.val.testBit i.val
def readBit (r : Fin 64) (v : Word) := v.getLsbD r

@[local simp] theorem read_ones (r : Fin 64) : readBit r ones = true := by
  exact (BitVec.getLsbD_allOnes).trans (decide_eq_true r.isLt)

@[local simp] theorem read_zero (r : Fin 64) : readBit r 0 = false := by simp [readBit]

@[local simp] theorem ones_and (a : Word) : ones &&& a = a := BitVec.allOnes_and
@[local simp] theorem and_ones (a : Word) : a &&& ones = a := BitVec.and_allOnes
@[local simp] theorem ones_or (a : Word) : ones ||| a = ones := BitVec.allOnes_or
@[local simp] theorem or_ones (a : Word) : a ||| ones = ones := BitVec.or_allOnes

theorem roots_bits : ∀ r : Fin 64, roots.map (readBit r) = List.ofFn (assignment r) :=
  by decide +kernel

abbrev graph := Frame.target

theorem row_flags : ∀ r : Fin 64, graph (assignment r) = readBit r goal := by decide +kernel

theorem getD_map {α β} (f : α → β) (s : List α) (i : Nat) (a : α) :
    (s.map f).getD i (f a) = f (s.getD i a) := by
  induction s generalizing i with
  | nil => simp
  | cons x s ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem getD_mem_or (w : List Word) (i : Nat) : w.getD i 0 ∈ w ∨ w.getD i 0 = 0 := by
  by_cases h : i < w.length
  · left
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    exact List.getElem_mem h
  · right
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

def binaryWord (w : List Word) (g : Gate) : Word :=
  let d := match g.op with | .or => true | _ => false
  match g.inputs with
  | [] => if d then 0 else ones
  | [a] => w.getD a 0
  | a::b::_ => join d (w.getD a 0) (w.getD b 0)

def gateWord (w : List Word) (g : Gate) : Word :=
  match g.op with
  | .not => match g.inputs with | [] => ones | a::_ => ~~~(w.getD a 0)
  | _ => binaryWord w g

def binCost (g : Gate) : Nat :=
  match g.op, g.inputs with | .and, _::_::_ | .or, _::_::_ => 1 | _, _ => 0
def invCost (g : Gate) : Nat := match g.op with | .not => 1 | _ => 0

def binaryCount : List Gate → Nat
  | [] => 0 | g::gs => binaryCount gs + binCost g
def inversionCount : List Gate → Nat
  | [] => 0 | g::gs => inversionCount gs + invCost g

def stepWord (w : List Word) (g : Gate) := w ++ [gateWord w g]
def stepBit (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def allowed (g : Gate) := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

theorem step_correct (r : Fin 64) (w : List Word) (g : Gate) (h : allowed g) :
    (stepWord w g).map (readBit r) = stepBit (w.map (readBit r)) g := by
  have get (j : Nat) : (w[j]?.map (readBit r)).getD false = readBit r (w[j]?.getD 0) := by
    cases w[j]? <;> simp [readBit]
  rcases g with ⟨op,ins⟩
  rcases h with ⟨hOp, hlen⟩
  change op = .and ∨ op = .or ∨ op = .not at hOp
  change ins.length ≤ 2 at hlen
  rcases hOp with rfl|rfl|rfl <;> cases ins with
  | nil => simp [stepWord,stepBit,gateWord,binaryWord,GateOp.eval] <;> exact read_zero r
  | cons a rest =>
    cases rest with
    | nil => simp [stepWord,stepBit,gateWord,binaryWord,get,GateOp.eval,readBit]
    | cons b tail =>
      cases tail with
      | nil => simp [stepWord,stepBit,gateWord,binaryWord,get,GateOp.eval,join,readBit]
      | cons c rest => simp at hlen

theorem fold_correct (r : Fin 64) (gs : List Gate) (w : List Word)
    (h : ∀ g ∈ gs, allowed g) :
    (gs.foldl stepWord w).map (readBit r) = gs.foldl stepBit (w.map (readBit r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by grind), step_correct r w g (h _ (by simp))]

theorem sampled_circuit (C : Circuit) (hp : ∀ g ∈ C.gates, allowed g)
    (accept : ∀ r : Fin 64, C.eval (List.ofFn (assignment r)) = readBit r goal) :
    (C.gates.foldl stepWord roots).getD C.output 0 = goal := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let r : Fin 64 := ⟨i,hi⟩
  change readBit r ((C.gates.foldl stepWord roots).getD C.output 0) = readBit r goal
  rw [← getD_map (readBit r) (C.gates.foldl stepWord roots) C.output 0]
  rw [fold_correct r C.gates roots hp, roots_bits]
  rw [read_zero]
  exact accept r

theorem nontrivial_join (d : Bool) (a b : Word)
    (haa : join d a b ≠ a) (hbb : join d a b ≠ b)
    (h0 : join d a b ≠ 0) (h1 : join d a b ≠ ones) :
    a ≠ 0 ∧ b ≠ 0 ∧ a ≠ ones ∧ b ≠ ones ∧ a ≠ b := by
  refine ⟨?_,?_,?_,?_,?_⟩ <;> rintro rfl <;> cases d <;> simp_all [join]

theorem not_ones : ~~~ones = (0 : Word) := by decide +kernel
theorem not_zero : ~~~(0 : Word) = ones := by decide +kernel

def Parents (w : List Word) (g : Gate) (c : Word) : Prop :=
  (∃ d a b, c = join d a b ∧ binCost g = 1 ∧ a ∈ w ∧ b ∈ w ∧
    a ≠ 0 ∧ b ≠ 0 ∧ a ≠ ones ∧ b ≠ ones ∧ a ≠ b) ∨
  (∃ a, c = ~~~a ∧ invCost g = 1 ∧ a ∈ w ∧ a ≠ 0 ∧ a ≠ ones)

theorem binary_parents (w : List Word) (op : GateOp) (opok : op = .and ∨ op = .or)
    (ins : List Nat) (missing : binaryWord w ⟨op,ins⟩ ∉ w)
    (p0 : binaryWord w ⟨op,ins⟩ ≠ 0) (p1 : binaryWord w ⟨op,ins⟩ ≠ ones) :
    Parents w ⟨op,ins⟩ (binaryWord w ⟨op,ins⟩) := by
  let d := match op with | .or => true | _ => false
  cases ins with
  | nil =>
    change (if d then 0 else ones) ≠ 0 at p0
    change (if d then 0 else ones) ≠ ones at p1
    cases d <;> simp_all
  | cons i rest =>
    cases rest with
    | nil =>
      change w.getD i 0 ∉ w at missing
      change w.getD i 0 ≠ 0 at p0
      exact (getD_mem_or w i).elim (fun h => (missing h).elim) (fun h => (p0 h).elim)
    | cons j tail =>
      let a := w.getD i 0
      let b := w.getD j 0
      change join d a b ∉ w at missing
      change join d a b ≠ 0 at p0
      change join d a b ≠ ones at p1
      have absent (u : Word) (mem : u ∈ w ∨ u = 0) : join d a b ≠ u := by
        intro e
        exact mem.elim (fun m => missing (e ▸ m)) (fun z => p0 (e.trans z))
      have parts := nontrivial_join d a b (absent _ (getD_mem_or w i))
        (absent _ (getD_mem_or w j)) p0 p1

      have cost : binCost ⟨op,i::j::tail⟩ = 1 := by rcases opok with rfl|rfl <;> rfl
      exact Or.inl ⟨d,a,b,rfl,cost,(getD_mem_or w i).resolve_right parts.1,
        (getD_mem_or w j).resolve_right parts.2.1,parts⟩

theorem gate_parents (w : List Word) (g : Gate) (okay : allowed g)
    (missing : gateWord w g ∉ w) (p0 : gateWord w g ≠ 0) (p1 : gateWord w g ≠ ones) :
    Parents w g (gateWord w g) := by
  rcases g with ⟨op,ins⟩
  have ops : op = .and ∨ op = .or ∨ op = .not := okay.1
  rcases ops with h|h|h
  · subst op
    exact binary_parents w _ (.inl rfl) ins missing p0 p1
  · subst op
    exact binary_parents w _ (.inr rfl) ins missing p0 p1
  · subst op
    cases ins with
    | nil => exact (p1 rfl).elim
    | cons i rest =>
      let a := w.getD i 0
      change ~~~a ≠ 0 at p0
      change ~~~a ≠ ones at p1
      have a0 : a ≠ 0 := fun e => p1 (e ▸ not_zero)
      have a1 : a ≠ ones := fun e => p0 (e ▸ not_ones)
      exact Or.inr ⟨a,rfl,rfl,(getD_mem_or w i).resolve_right a0,a0,a1⟩

def Trace (b n : Nat) (w : List Word) : Prop :=
  ∃ (k j : Nat) (S : Finset Word), k ≤ b ∧ j ≤ n ∧
    (∀ x ∈ S, x ∈ w ∧ x ≠ 0 ∧ x ≠ ones) ∧ Live k j S

theorem unwind (b n : Nat) (w : List Word) (g : Gate) (okay : allowed g)
    (t : Trace b n (stepWord w g)) : Trace (b + binCost g) (n + invCost g) w := by
  obtain ⟨k,j,S,hk,hj,valid,live⟩ := t
  let c := gateWord w g
  have prev (x : Word) (hx : x ∈ S) : (x ∈ w ∨ x = c) ∧ x ≠ 0 ∧ x ≠ ones := by
    simpa [c,stepWord] using valid x hx
  by_cases used : c ∈ S
  · by_cases old : c ∈ w
    · exact ⟨k,j,S,by omega,by omega,fun x hx => by have h := prev x hx; grind,live⟩
    · let U := S.erase c
      have uc : c ∉ U := Finset.notMem_erase _ _
      have sub (x : Word) (hx : x ∈ U) : x ∈ w ∧ x ≠ 0 ∧ x ≠ ones := by
        have hx' := Finset.mem_erase.mp hx
        have h := prev x hx'.2
        exact ⟨h.1.resolve_right hx'.1,h.2⟩
      have back : insert c U = S := Finset.insert_erase used
      rcases gate_parents w g okay old (valid c used).2.1 (valid c used).2.2 with binary|inv
      · obtain ⟨d,a,x,eqc,cost,ha,hx,a0,x0,a1,x1,ne⟩ := binary
        change c = join d a x at eqc
        have ca : c ≠ a := fun e => old (e ▸ ha)
        have cx : c ≠ x := fun e => old (e ▸ hx)
        refine ⟨k+1,j,insert a (insert x U),by omega,by omega,?_,?_⟩
        · intro y hy
          rcases Finset.mem_insert.mp hy with rfl|hy
          · exact ⟨ha,a0,a1⟩
          rcases Finset.mem_insert.mp hy with rfl|hy
          · exact ⟨hx,x0,x1⟩
          exact sub _ hy
        · apply Live.binary d ne
          · simpa [← eqc,ca,cx] using uc
          · exact eqc ▸ (valid c used).2
          · rwa [← eqc,back]
      · obtain ⟨a,eqc,cost,ha,a0,a1⟩ := inv
        change c = ~~~a at eqc
        have ca : c ≠ a := fun e => old (e ▸ ha)
        refine ⟨k,j+1,insert a U,by omega,by omega,?_,?_⟩
        · intro y hy
          rcases Finset.mem_insert.mp hy with rfl|hy
          · exact ⟨ha,a0,a1⟩
          exact sub _ hy
        · apply Live.inversion
          · simpa [←eqc,ca] using uc
          · exact eqc ▸ (valid c used).2
          · rwa [←eqc,back]
  · exact ⟨k,j,S,by omega,by omega,fun x hx => by have h := prev x hx; grind,live⟩

theorem trace_aux (gs : List Gate) (w : List Word) (out : Nat) (hp : ∀ g ∈ gs, allowed g)
    (success : (gs.foldl stepWord w).getD out 0 = goal) :
    Trace (binaryCount gs) (inversionCount gs) w := by
  induction gs generalizing w with
  | nil =>
    change w.getD out 0 = goal at success
    have h := (getD_mem_or w out).resolve_right (success ▸ goal_proper.1)
    rw [success] at h
    refine ⟨0,0,{goal},by simp [binaryCount],by simp [inversionCount],?_,Live.done⟩
    simpa using And.intro h goal_proper
  | cons g gs ih => exact unwind _ _ w g (hp _ (by simp)) (ih _ (by grind) success)

theorem circuit_live (C : Circuit) (legal : ∀ g ∈ C.gates, allowed g)
    (correct : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = graph x) :
    ∃ b ≤ binaryCount C.gates, ∃ n ≤ inversionCount C.gates, ∃ S ⊆ roots.toFinset, Live b n S := by
  have accept (r : Fin 64) : C.eval (List.ofFn (assignment r)) = readBit r goal :=
    (correct _).trans (row_flags r)
  obtain ⟨b,n,S,hb,hn,incl,live⟩ := trace_aux _ _ _ legal (sampled_circuit C legal accept)
  exact ⟨b,hb,n,hn,S,fun x hx => List.mem_toFinset.mpr (incl x hx).1,live⟩

theorem agree_join (p q : Fin 64) (d : Bool) (a x : Word)
    (ha : readBit p a = readBit q a) (hx : readBit p x = readBit q x) :
    readBit p (join d a x) = readBit q (join d a x) := by
  cases d <;> simp_all [join,readBit]

theorem agree_not (p q : Fin 64) (a : Word) (ha : readBit p a = readBit q a) :
    readBit p (~~~a) = readBit q (~~~a) := by simp_all [readBit]

theorem live_agrees {b n S} (live : Live b n S) (p q : Fin 64)
    (same : ∀ x ∈ S, readBit p x = readBit q x) : readBit p goal = readBit q goal := by
  induction live using Live.recPlain with
  | done => exact same goal (by simp)
  | @binary b n a x U d _ _ _ _ ih =>
    apply ih
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl|hy
    · exact agree_join p q d a x (same _ (by simp)) (same _ (by simp))
    · exact same _ (by simp [hy])
  | @inversion b n a U _ _ _ ih =>
    apply ih
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl|hy
    · exact agree_not p q a (same _ (by simp))
    · exact same _ (by simp [hy])

def witnesses (i : Fin 6) : Fin 64 × Fin 64 :=
  ([(2, 3), (1, 3), (2, 6), (1, 9), (5, 21), (5, 37)]
    : List (Fin 64 × Fin 64)).get i

theorem witness_correct : ∀ i : Fin 6,
    readBit (witnesses i).1 goal ≠ readBit (witnesses i).2 goal ∧
    ∀ j : Fin 6, readBit (witnesses i).1 (roots.get j) =
      readBit (witnesses i).2 (roots.get j) ∨ j = i := by decide +kernel

theorem roots_full {b n S} (live : Live b n S) (sub : S ⊆ roots.toFinset) :
    S = roots.toFinset := by
  apply Finset.Subset.antisymm sub
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hx)
  obtain ⟨distinct,only⟩ := witness_correct i
  by_contra missing
  apply distinct (live_agrees live _ _ ?_)
  intro w hw
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp (sub hw))
  exact (only j).resolve_right (by rintro rfl; exact missing hw)

theorem cost_bound (gs : List Gate) : binaryCount gs + inversionCount gs ≤ gs.length := by
  induction gs with
  | nil => simp [binaryCount,inversionCount]
  | cons g gs ih =>
    have hg : binCost g + invCost g ≤ 1 := by
      rcases g with ⟨op,ins⟩
      cases op <;> cases ins with
      | nil => simp [binCost,invCost]
      | cons i tail => cases tail <;> simp [binCost,invCost]
    simp only [binaryCount,inversionCount,List.length_cons]
    omega

theorem zero_inversions (gs : List Gate) (none : ∀ g ∈ gs, g.op ≠ .not) :
    inversionCount gs = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have ng := none g (by simp)
    have cost : invCost g = 0 := by rcases g with ⟨op,ins⟩; cases op <;> simp_all [invCost]
    rw [inversionCount,cost,ih (by grind),Nat.add_zero]

theorem unique_inversion (gs : List Gate)
    (uniq : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i=j) :
    inversionCount gs ≤ 1 := by
  induction gs with
  | nil => decide
  | cons g gs ih =>
    by_cases head : g.op = .not
    · have none (x : Gate) (hx : x ∈ gs) : x.op ≠ .not := by
        obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hx
        intro nj
        have eq := uniq ⟨0,by simp⟩ j.succ head nj
        have e := congrArg Fin.val eq
        simp at e
      have one : invCost g = 1 := by simp [invCost,head]
      rw [inversionCount,zero_inversions gs none,one]
    · have zero : invCost g = 0 := by rcases g with ⟨op,ins⟩; cases op <;> simp_all [invCost]
      rw [inversionCount,zero,Nat.add_zero]
      apply ih
      intro i j ni nj
      exact Fin.succ_injective _ (uniq i.succ j.succ ni nj)

theorem full_chain (gates : List Gate) (out : Nat)
    (legal : ∀ g ∈ gates, allowed g)
    (uniq : ∀ i j : Fin gates.length, (gates.get i).op = .not → (gates.get j).op = .not → i=j)
    (correct : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gates,out⟩ (List.ofFn x) = graph x) :
    ∃ b n, b+n ≤ gates.length ∧ n ≤ 1 ∧ Live b n roots.toFinset := by
  obtain ⟨b,hb,n,hn,S,sub,live⟩ := circuit_live ⟨gates,out⟩ legal correct
  rw [roots_full live sub] at live
  exact ⟨b,n,(Nat.add_le_add hb hn).trans (cost_bound gates),hn.trans (unique_inversion gates uniq),live⟩

theorem has_inversion_cost (gates : List Gate) (hasNot : ∃ g ∈ gates, g.op = .not) :
    1 ≤ inversionCount gates := by
  induction gates with
  | nil => simp at hasNot
  | cons g gs ih =>
    by_cases top : g.op = .not
    · simp [inversionCount, invCost, top]
    · obtain ⟨f,hf,inv⟩ := hasNot
      have hin : f ∈ gs := (List.mem_cons.mp hf).resolve_left (fun eq => top (eq ▸ inv))
      have tail := ih ⟨f,hin,inv⟩
      rw [inversionCount]
      omega

theorem signed_chain {gates : List Gate} {out : Nat}
    (legal : ∀ g ∈ gates, allowed g)
    (uniq : ∀ i j : Fin gates.length, (gates.get i).op = .not → (gates.get j).op = .not → i=j)
    (correct : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gates,out⟩ (List.ofFn x) = graph x)
    (hasNot : ∃ g ∈ gates, g.op = .not) :
    ∃ b n, b+1 ≤ gates.length ∧ n ≤ 1 ∧ Live b n roots.toFinset := by
  obtain ⟨b,hb,n,hn,S,sub,live⟩ := circuit_live ⟨gates,out⟩ legal correct
  rw [roots_full live sub] at live
  exact ⟨b,n,(Nat.add_le_add hb (has_inversion_cost gates hasNot)).trans (cost_bound gates),
    hn.trans (unique_inversion gates uniq),live⟩

def counted (g : Gate) : Bool := match g.op with | .not => false | _ => true

theorem binaryCount_le_countP (gs : List Gate) :
    binaryCount gs ≤ gs.countP counted := by
  induction gs with
  | nil => simp [binaryCount]
  | cons g gs ih =>
    have cap : binCost g ≤ (counted g).toNat := by
      obtain ⟨op, inputs⟩ := g
      cases op <;> cases inputs with
      | nil => simp [binCost, counted]
      | cons a rest => cases rest <;> simp [binCost, counted]
    rw [binaryCount, List.countP_cons]
    cases h : counted g <;> simp [h] at cap ⊢ <;> omega

theorem circuit_chain (gs : List Gate) (o : Nat)
    (legal : FanInTwo ⟨gs,o⟩)
    (correct : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Frame.target x) :
    ∃ b n, b ≤ gs.countP counted ∧ Live b n roots.toFinset := by
  obtain ⟨b,hb,n,_,S,sub,live⟩ := circuit_live ⟨gs,o⟩ legal correct
  rw [roots_full live sub] at live
  exact ⟨b,n,hb.trans (binaryCount_le_countP gs),live⟩

theorem freely_chain (gs : List Gate) (o : Nat)
    (legal : FanInTwo ⟨gs,o⟩)
    (correct : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Frame.target x)
    (hasNot : ∃ g ∈ gs, g.op = .not) :
    ∃ b n, b+1 ≤ gs.length ∧ Live b n roots.toFinset := by
  obtain ⟨b,hb,n,_,S,sub,live⟩ := circuit_live ⟨gs,o⟩ legal correct
  rw [roots_full live sub] at live
  exact ⟨b,n,(Nat.add_le_add hb (has_inversion_cost gs hasNot)).trans (cost_bound gs),live⟩

end PEqualNP.Outside.L_meta_16501
namespace PEqualNP.Outside.L_meta_16501.Reduce
variable {m : Nat}
def canon (w : BitVec (m+1)) := if w.getLsbD 0 then ~~~w else w
def signed (d : Bool) (w : BitVec (m+1)) := if d then ~~~w else w
def gate (s t : Bool) (a b : BitVec (m+1)) := canon (signed s a &&& signed t b)
def Path (goal : BitVec (m+1)) (k : Nat) (S : Finset (BitVec (m+1))) : Prop :=
  ∀ P : Nat → Finset (BitVec (m+1)) → Prop, P 0 {goal} →
    (∀ {k a b U} (s t : Bool), a ≠ b → gate s t a b ∉ insert a (insert b U) →
      gate s t a b ≠ 0 → P k (insert (gate s t a b) U) → P (k+1) (insert a (insert b U))) →
    P k S
theorem Path.done {g : BitVec (m+1)} : Path g 0 {g} := fun _ d _ => d
theorem Path.binary {g : BitVec (m+1)} {k a b U} (s t : Bool) (ne : a ≠ b)
    (fresh : gate s t a b ∉ insert a (insert b U)) (proper : gate s t a b ≠ 0)
    (tail : Path g k (insert (gate s t a b) U)) : Path g (k+1) (insert a (insert b U)) :=
  fun P d f => f s t ne fresh proper (tail P d f)
theorem canon_not (x : BitVec (m+1)) : canon (~~~x) = canon x := by
  unfold canon
  simp only [BitVec.getLsbD_not, Nat.zero_lt_succ,decide_true, Bool.true_and]
  cases x.getLsbD 0 <;> simp

theorem canon_canon (x : BitVec (m+1)) : canon (canon x) = canon x := by
  by_cases h : x.getLsbD 0 = true
  · rw [show canon x = ~~~x from if_pos h,canon_not,show canon x = ~~~x from if_pos h]
  · rw [show canon x = x from if_neg h]
    exact if_neg h

theorem sign_back (x : BitVec (m+1)) : signed (x.getLsbD 0) (canon x) = x := by
  unfold signed canon
  cases x.getLsbD 0 <;> simp

theorem canon_zero : canon (0 : BitVec (m+1)) = 0 := by simp [canon]
theorem gate_left_zero (s t : Bool) (x : BitVec (m+1)) :
    gate s t 0 x = 0 ∨ gate s t 0 x = canon x := by
  cases s with
  | false => exact Or.inl ((congrArg canon (BitVec.zero_and (x := signed t x))).trans canon_zero)
  | true =>
    cases t with
    | false => right; simp [gate,signed]
    | true => right; simp [gate,signed,canon_not]

theorem gate_right_zero (s t : Bool) (x : BitVec (m+1)) :
    gate s t x 0 = 0 ∨ gate s t x 0 = canon x := by
  rw [show gate s t x 0 = gate t s 0 x from congrArg canon (BitVec.and_comm ..)]
  exact gate_left_zero _ _ _

theorem gate_same (s t : Bool) (x : BitVec (m+1)) : gate s t x x = 0 ∨ gate s t x x = canon x := by
  cases s <;> cases t
  · exact Or.inr (congrArg canon (BitVec.and_self (x := x)))
  · exact Or.inl ((congrArg canon (BitVec.and_not_self x)).trans canon_zero)
  · exact Or.inl ((congrArg canon (BitVec.not_and_self x)).trans canon_zero)
  · exact Or.inr ((congrArg canon (BitVec.and_self (x := ~~~x))).trans (canon_not x))

variable {A : Type} [DecidableEq A] (pin : A → BitVec (m+1))
def avail (S : Finset A) := (S.image pin).erase 0
def lost (S : Finset A) := (S.filter fun x => pin x = 0).card
theorem avail_mem {S : Finset A} {x : BitVec (m+1)} :
    x ∈ avail pin S ↔ x ≠ 0 ∧ ∃ a ∈ S, pin a = x := by simp [avail]

theorem avail_mono {S T : Finset A} (h : S ⊆ T) : avail pin S ⊆ avail pin T := by
  intro y hy
  obtain ⟨hn,x,hx,rfl⟩ := (avail_mem pin).mp hy
  exact (avail_mem pin).mpr ⟨hn,x,h hx,rfl⟩

theorem avail_cases {S : Finset A} {c : A} {x : BitVec (m+1)} (h : x ∈ avail pin (insert c S)) :
    x = pin c ∨ x ∈ avail pin S := by
  obtain ⟨hn,y,hy,rfl⟩ := (avail_mem pin).mp h
  rcases Finset.mem_insert.mp hy with rfl|hy
  · exact Or.inl rfl
  · exact Or.inr ((avail_mem pin).mpr ⟨hn,y,hy,rfl⟩)

theorem lost_insert (c : A) (S : Finset A) :
    lost pin (insert c S) = lost pin S + (if pin c = 0 ∧ c ∉ S then 1 else 0) := by
  by_cases mem : c ∈ S
  · rw [Finset.insert_eq_of_mem mem,if_neg (fun q => q.2 mem),Nat.add_zero]
  · by_cases h : pin c = 0
    · rw [if_pos ⟨h,mem⟩]
      unfold lost
      rw [Finset.filter_insert,if_pos h,Finset.card_insert_of_notMem]
      exact fun q => mem (Finset.mem_filter.mp q).1
    · rw [if_neg (fun q => h q.1),Nat.add_zero]
      unfold lost
      rw [Finset.filter_insert,if_neg h]

theorem cost_skip (a b c : A) (U : Finset A) (fresh : c ∉ U)
    (both : pin a = 0 → pin b = 0 → pin c = 0) :
    lost pin (insert a (insert b U)) ≤ lost pin (insert c U) + 1 := by
  simp only [lost_insert]
  split_ifs <;> grind

def Proj (goal : BitVec (m+1)) (limit extra : Nat) (S : Finset A) : Prop :=
  ∃ k, k + lost pin S + extra ≤ limit ∧ ∃ T ⊆ avail pin S, Path goal k T

theorem proj_done (x : A) (nz : pin x ≠ 0) : Proj pin (pin x) 0 0 {x} := by
  refine ⟨0,?_,{pin x},?_,Path.done⟩ <;> simp [lost,avail] <;> exact nz
theorem proj_inv {g : BitVec (m+1)} {limit extra : Nat} (a c : A) (U : Finset A)
    (newc : c ∉ U) (eq : pin c = pin a) (tail : Proj pin g limit extra (insert c U)) :
    Proj pin g limit extra (insert a U) := by
  obtain ⟨k,hle,T,sub,path⟩ := tail
  refine ⟨k,?_,T,?_,path⟩
  · simp only [lost_insert,eq] at hle ⊢
    split_ifs at * <;> grind
  · intro x hx
    rcases avail_cases pin (sub hx) with eq'|old
    · exact (avail_mem pin).mpr ⟨((avail_mem pin).mp (sub hx)).1,a,by simp,(eq'.trans eq).symm⟩
    · exact avail_mono pin (Finset.subset_insert _ _) old

theorem proj_strong {g : BitVec (m+1)} {limit : Nat} (a b c : A) (U : Finset A)
    (newc : c ∉ U) (hc : pin c = 0) (one : pin a ≠ 0 ∨ pin b ≠ 0)
    (tail : Proj pin g limit 0 (insert c U)) : Proj pin g (limit+1) 1 (insert a (insert b U)) := by
  obtain ⟨k,le,T,sub,path⟩ := tail
  refine ⟨k,?_,T,?_,path⟩
  · simp only [lost_insert,hc] at le ⊢
    split_ifs at * <;> grind
  · intro x hx
    rcases avail_cases pin (sub hx) with eq|old
    · exact (((avail_mem pin).mp (sub hx)).1 (eq.trans hc)).elim
    · exact avail_mono pin (by intro _ mem; simp [mem]) old

theorem proj_bin {g : BitVec (m+1)} {b extra : Nat} (a x c : A) (U : Finset A)
    (can : ∀ v, canon (pin v) = pin v) (cnew : c ∉ U) (s t : Bool)
    (repr : pin c = gate s t (pin a) (pin x))
    (tail : Proj pin g b extra (insert c U)) : Proj pin g (b+1) extra (insert a (insert x U)) := by
  let prev := insert a (insert x U)
  obtain ⟨k,hle,T,sub,path⟩ := tail
  change k + lost pin (insert c U) + extra ≤ b at hle
  change T ⊆ avail pin (insert c U) at sub
  have both (ha : pin a = 0) (hx : pin x = 0) : pin c = 0 := by
    rw [repr,ha,hx]
    exact (gate_same s t 0).elim id (fun q => q.trans canon_zero)
  have skipcost := cost_skip pin a x c U cnew both
  have liftU : avail pin U ⊆ avail pin prev := avail_mono pin (by intro u hu; simp [prev,hu])
  by_cases useful : pin c ∈ T ∧ pin c ∉ avail pin prev
  · have nz := ((avail_mem pin).mp (sub useful.1)).1
    have df (v : A) (hv : v ∈ prev) : pin c ≠ pin v := by
      intro e
      exact useful.2 ((avail_mem pin).mpr ⟨nz,v,hv,e.symm⟩)
    have da := df a (by simp [prev])
    have dx := df x (by simp [prev])
    have ha : pin a ≠ 0 := by
      intro h
      have drop := gate_left_zero s t (pin x)
      rw [h] at repr
      rw [←repr,can] at drop
      exact drop.elim nz dx
    have hx : pin x ≠ 0 := by
      intro h
      have drop := gate_right_zero s t (pin a)
      rw [h] at repr
      rw [←repr,can] at drop
      exact drop.elim nz da
    have distinct : pin a ≠ pin x := by
      intro e
      have drop := gate_same s t (pin x)
      rw [e] at repr
      rw [←repr,can] at drop
      exact drop.elim nz dx
    have vcost : lost pin prev ≤ lost pin (insert c U) := by
      simp only [prev,lost_insert]
      split_ifs <;> grind
    let V := T.erase (pin c)
    have old (v : BitVec (m+1)) (hv : v ∈ V) : v ∈ avail pin U :=
      (avail_cases pin (sub (Finset.mem_erase.mp hv).2)).resolve_left (Finset.mem_erase.mp hv).1
    refine ⟨k+1,by change k+1+lost pin prev + extra ≤ b+1; omega,insert (pin a) (insert (pin x) V),?_,?_⟩
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl|hv
      · exact (avail_mem pin).mpr ⟨ha,a,by simp [prev],rfl⟩
      rcases Finset.mem_insert.mp hv with rfl|hv
      · exact (avail_mem pin).mpr ⟨hx,x,by simp [prev],rfl⟩
      exact liftU (old _ hv)
    · apply Path.binary s t distinct
      · rw [←repr]
        simp [V,da,dx]
      · rwa [←repr]
      · rwa [←repr,show insert (pin c) V = T from Finset.insert_erase useful.1]
  · refine ⟨k,by change k+lost pin (insert a (insert x U)) + extra ≤ b+1; omega,T,?_,path⟩
    intro v hv
    rcases avail_cases pin (sub hv) with rfl|old
    · by_contra miss
      exact useful ⟨hv,miss⟩
    · exact liftU old
end PEqualNP.Outside.L_meta_16501.Reduce
namespace PEqualNP.Outside.L_meta_16501.Reduce
open PEqualNP.Outside.L_meta_16501

def half (b : Bool) (w : Word) : BitVec 32 :=
  if b then w.extractLsb' 32 32 else w.extractLsb' 0 32
def pin6 (b : Bool) (w : Word) := canon (half b w)
def lit : Word := 0xffffffff00000000
def literal (w : Word) := w = lit ∨ w = ~~~lit
def indep (w : Word) := half false w = half true w
def safe (w : Word) : Prop := literal w ∨ indep w ∧ pin6 false w ≠ 0

theorem half_not (b : Bool) (v : Word) : half b (~~~v) = ~~~half b v := by
  cases b <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj <;>
    simp [half,BitVec.getLsbD_not,hj,show 32+j < 64 by omega,show j < 64 by omega]
theorem half_and (b : Bool) (v w : Word) : half b (v &&& w) = half b v &&& half b w := by
  cases b <;> exact BitVec.extractLsb'_and
theorem half_or (b : Bool) (v w : Word) : half b (v ||| w) = half b v ||| half b w := by
  cases b <;> exact BitVec.extractLsb'_or
theorem indep_nz (w : Word) (h : indep w) (hp : w ≠ 0 ∧ w ≠ ones) : pin6 false w ≠ 0 := by
  change half false w = half true w at h
  have rebuild : half true w ++ half false w = w := BitVec.extractLsb'_append_extractLsb'
  rw [←h] at rebuild
  unfold pin6 canon
  intro bad
  split at bad
  · have both := congrArg (fun x : BitVec 32 => ~~~x) bad
    simp only [BitVec.not_not,BitVec.not_zero] at both
    rw [both] at rebuild
    exact hp.2 (rebuild.symm.trans (by decide))
  · rw [bad] at rebuild
    exact hp.1 (rebuild.symm.trans (by decide))
theorem safe_not (v : Word) (h : safe v) : safe (~~~v) := by
  rcases h with (rfl|rfl)|⟨e,q⟩
  · exact Or.inl (Or.inr rfl)
  · exact Or.inl (Or.inl BitVec.not_not)
  · right
    exact ⟨by simpa only [indep,half_not] using congrArg (fun t => ~~~t) e,
      by simpa only [pin6,half_not,canon_not] using q⟩
theorem indep_join (d : Bool) {a b : Word} (ha : indep a) (hb : indep b) :
    indep (join d a b) := by
  unfold indep at *
  cases d <;> simp [join,half_or,half_and,ha,hb]
theorem p6neg (b : Bool) (w : Word) : pin6 b (~~~w) = pin6 b w := by
  simp [pin6,half_not,canon_not]
theorem p6repr (e d : Bool) (a b : Word) :
    ∃ s t, pin6 e (join d a b) = gate s t (pin6 e a) (pin6 e b) := by
  cases d
  · exact ⟨(half e a).getLsbD 0,(half e b).getLsbD 0,by simp only [pin6,gate,sign_back]; exact congrArg canon (half_and _ _ _)⟩
  · refine ⟨(~~~(half e a)).getLsbD 0,(~~~(half e b)).getLsbD 0,?_⟩
    unfold gate pin6
    rw [←canon_not (half e a),←canon_not (half e b),sign_back,sign_back,←BitVec.not_or,canon_not]
    exact congrArg canon (half_or _ _ _)
theorem pin6goal (e : Bool) : pin6 e goal ≠ 0 := by cases e <;> decide +kernel
theorem ordinary {b n S} (h : Live b n S) (e : Bool) : Proj (pin6 e) (pin6 e goal) b 0 S := by
  induction h using Live.recPlain with
  | done => exact proj_done _ _ (pin6goal _)
  | @inversion b n a U fresh proper tail ih =>
    exact proj_inv _ _ _ _ (fun h => fresh (by simp [h])) (p6neg e a) ih
  | @binary b n a x U d ne fresh proper tail ih =>
    obtain ⟨s,t,rep⟩ := p6repr e d a x
    exact proj_bin _ _ _ _ _ (fun v => canon_canon _) (fun h => fresh (by simp [h])) s t rep ih

theorem choose_kill (d : Bool) (v w : Word) (h : literal v) :
    ∃ e, pin6 e (join d v w) = 0 := by
  rcases h with rfl|rfl <;> cases d
  · exact ⟨false,by rw [pin6,show join false lit w = lit &&& w from rfl,half_and,show half false lit = 0 by decide]; simp only [show ∀ v : BitVec 32, (0 : BitVec 32) &&& v = 0 from fun v => BitVec.zero_and]; decide⟩
  · exact ⟨true,by rw [pin6,show join true lit w = lit ||| w from rfl,half_or,show half true lit = BitVec.allOnes 32 by decide,BitVec.allOnes_or]; decide⟩
  · exact ⟨true,by rw [pin6,show join false (~~~lit) w = (~~~lit) &&& w from rfl,half_and,show half true (~~~lit) = 0 by decide]; simp only [show ∀ v : BitVec 32, (0 : BitVec 32) &&& v = 0 from fun v => BitVec.zero_and]; decide⟩
  · exact ⟨false,by rw [pin6,show join true (~~~lit) w = (~~~lit) ||| w from rfl,half_or,show half false (~~~lit) = BitVec.allOnes 32 by decide,BitVec.allOnes_or]; decide⟩
theorem nz_else {w : Word} (h : indep w) (nz : pin6 false w ≠ 0) (e : Bool) : pin6 e w ≠ 0 := by
  cases e
  · exact nz
  · change half false w = half true w at h
    simpa only [pin6,←h] using nz
theorem impossible_lits (d : Bool) (a x : Word) (ha : literal a) (hx : literal x)
    (ne : a ≠ x) (proper : join d a x ≠ 0 ∧ join d a x ≠ ones) : False := by
  rcases ha with rfl|rfl <;> rcases hx with rfl|rfl <;> cases d <;>
    first | exact ne rfl | exact proper.1 (by decide) | exact proper.2 (by decide)
theorem join_comm (d : Bool) (a b : Word) : join d a b = join d b a := by
  cases d <;> simp [join,BitVec.and_comm,BitVec.or_comm]

theorem chooseFirst {b n S} (h : Live b n S) :
    (∀ v ∈ S, safe v) → ∃ e, Proj (pin6 e) (pin6 e goal) b 1 S := by
  induction h using Live.recPlain with
  | done =>
    intro ok
    exact (show ¬ safe goal by unfold safe literal indep; decide +kernel) (ok _ (by simp)) |>.elim
  | @inversion b n a U fresh proper tail ih =>
    intro ok
    have ta : ∀ v ∈ insert (~~~a) U, safe v := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl|vU
      · exact safe_not a (ok a (by simp))
      · exact ok v (by simp [vU])
    obtain ⟨e,good⟩ := ih ta
    exact ⟨e,proj_inv _ _ _ _ (fun h => fresh (by simp [h])) (p6neg e a) good⟩
  | @binary b n a x U d ne fresh proper tail ih =>
    intro ok
    have freshU : join d a x ∉ U := fun h => fresh (by simp [h])
    rcases ok a (by simp) with ha|⟨ea,na⟩ <;> rcases ok x (by simp) with hx|⟨ex,nx⟩
    · exact (impossible_lits d a x ha hx ne proper).elim
    · obtain ⟨e,kill⟩ := choose_kill d a x ha
      exact ⟨e,proj_strong _ _ _ _ _ freshU kill (Or.inr (nz_else ex nx e)) (ordinary tail e)⟩
    · obtain ⟨e,kill⟩ := choose_kill d x a hx
      rw [join_comm d x a] at kill
      exact ⟨e,proj_strong _ _ _ _ _ freshU kill (Or.inl (nz_else ea na e)) (ordinary tail e)⟩
    · have ec := indep_join d ea ex
      have ta : ∀ v ∈ insert (join d a x) U, safe v := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl|vU
        · exact Or.inr ⟨ec,indep_nz _ ec proper⟩
        · exact ok v (by simp [vU])
      obtain ⟨e,good⟩ := ih ta
      obtain ⟨s,t,rep⟩ := p6repr e d a x
      exact ⟨e,proj_bin _ _ _ _ _ (fun v => canon_canon _) freshU s t rep good⟩
end PEqualNP.Outside.L_meta_16501.Reduce

namespace PEqualNP.Outside.L_meta_16501.Reduce
def fiveRaw : List (BitVec 32) := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
theorem select {b n} (h : Live b n roots.toFinset) :
    ∃ e k, k+2 ≤ b ∧ ∃ T ⊆ fiveRaw.toFinset, Path (pin6 e goal) k T := by
  have ok : ∀ v ∈ roots.toFinset, safe v := by
    simp only [List.mem_toFinset,roots,List.mem_cons,List.not_mem_nil,or_false]
    intro v hv
    rcases hv with rfl|rfl|rfl|rfl|rfl|rfl <;> unfold safe literal indep <;> decide +kernel
  obtain ⟨e,k,hk,T,sub,hp⟩ := chooseFirst h ok
  have av : avail (pin6 e) roots.toFinset = fiveRaw.toFinset := by cases e <;> decide +kernel
  have ls : lost (pin6 e) roots.toFinset = 1 := by cases e <;> decide +kernel
  rw [av] at sub
  rw [ls] at hk
  exact ⟨e,k,by omega,T,sub,hp⟩
end PEqualNP.Outside.L_meta_16501.Reduce

namespace PEqualNP.Outside.L_meta_16501.Support

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Wire := Bool × ℕ
def zero : Wire := (false,0)
def flip (a : Wire) : Wire := (!a.1,a.2)
def combine (d a b : ℕ) : ℕ :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
def opIndex (a b : Bool) : ℕ :=
  if a then (if b then 1 else 3) else (if b then 2 else 0)
def meet (a b : Wire) : Wire := (a.1 && b.1,combine (opIndex a.1 b.1) a.2 b.2)
def join (a b : Wire) : Wire := flip (meet (flip a) (flip b))
def read (j : ℕ) (a : Wire) : Bool := a.1 != a.2.testBit j
lemma read_zero (j : ℕ) : read j zero=false := by simp [read,zero]
lemma read_flip (j : ℕ) (a : Wire) : read j (flip a)=!(read j a) := by
  cases a with | mk s a => cases s <;> cases h : a.testBit j <;> simp [read,flip,h]
lemma read_meet (j : ℕ) (a b : Wire) : read j (meet a b) = (read j a && read j b) := by
  obtain ⟨s,a⟩ := a;obtain ⟨t,b⟩ := b
  cases s <;> cases t <;> cases h : a.testBit j <;> cases g : b.testBit j <;>
    simp [read,meet,combine,opIndex,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,h,g]
lemma read_join (j : ℕ) (a b : Wire) : read j (join a b) = (read j a || read j b) := by
  simp only [join,read_flip,read_meet];cases read j a <;> cases read j b <;> rfl

def gate (w : List Wire) (g : Gate) : Wire :=
  let arg := fun i => w.getD i zero
  match g.op,g.inputs with
  | .not, xs => flip (arg (xs.headD w.length))
  | .and, [] => flip zero
  | .or, [] => zero
  | .and, [i] | .or, [i] => arg i
  | .and, i::j::_ => meet (arg i) (arg j)
  | .or, i::j::_ => join (arg i) (arg j)
  | _,_ => zero
def execute (gs : List Gate) (w : List Wire) : List Wire :=
  gs.foldl (fun w g => w++[gate w g]) w
def boolRun (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) w
lemma read_get (j : ℕ) (w : List Wire) (i : ℕ) :
    (w.map (read j)).getD i false = read j (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases h : w[i]? with
  | none => exact (read_zero j).symm
  | some a => rfl
lemma gate_read (w : List Wire) (g : Gate) (legal : g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) (j : ℕ) :
    read j (gate w g) = g.op.eval (g.inputs.map fun i => (w.map (read j)).getD i false) := by
  simp_rw [read_get]
  obtain ⟨op,xs⟩ := g
  obtain ⟨ops,len⟩ := legal
  change op ∈ ({.and,.or,.not} : Set GateOp) at ops
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops
  rcases ops with rfl|rfl|rfl <;>
    rcases xs with _|⟨i,_|⟨k,_|⟨h,rest⟩⟩⟩ <;>
    simp_all [gate,GateOp.eval,read_flip,read_meet,read_join,read_get,read_zero,List.getD_eq_default]
lemma execute_read (j : ℕ) (gs : List Gate) (w : List Wire) (legal : ∀ g ∈ gs,
    g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (execute gs w).map (read j) = boolRun gs (w.map (read j)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gate w g])).map (read j) = boolRun gs (_++[_])
    rw [ih _ (fun v hv => legal v (.tail _ hv))]
    simp [gate_read w g (legal g List.mem_cons_self) j]

def counted (g : Gate) : Bool := match g.op with | .not => false | _ => true
def reps (w : List Wire) := w.map Prod.snd
def simple (w : List Wire) (z : ℕ) := z=0 ∨ z∈reps w
def priced (w : List Wire) (paid : Bool) (z : ℕ) := simple w z ∨
    (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a≠0 ∧ b≠0 ∧ a≠b ∧ z=combine d a b)
lemma get_simple (w : List Wire) (i : ℕ) : simple w (w.getD i zero).2 := by
  simp only [List.getD_eq_getElem?_getD]
  cases eq : w[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_map.mpr ⟨a,List.mem_of_getElem? eq,rfl⟩)
lemma combine_eq_cases (d a b : ℕ) (hd : d<4) (h : a=0 ∨ b=0 ∨ a=b) :
    combine d a b=0 ∨ combine d a b=a ∨ combine d a b=b := by
  rcases h with h|h|h <;> subst_vars <;> interval_cases d <;> simp [combine]
lemma made (w : List Wire) (d : ℕ) (a b : Wire) (hd : d<4) (pa : simple w a.2) (pb : simple w b.2) :
    priced w true (combine d a.2 b.2) := by
  by_cases h : a.2=0 ∨ b.2=0 ∨ a.2=b.2
  · rcases combine_eq_cases _ _ _ hd h with e|e|e
    · exact Or.inl (Or.inl e)
    · apply Or.inl; rw [e]; exact pa
    · apply Or.inl; rw [e]; exact pb
  · push Not at h
    exact Or.inr ⟨rfl,d,hd,a.2,pa.resolve_left h.1,b.2,pb.resolve_left h.2.1,h.1,h.2.1,h.2.2,rfl⟩
lemma op_lt (s t : Bool) : opIndex s t < 4 := by cases s <;> cases t <;> decide
lemma gate_priced (w : List Wire) (g : Gate) : priced w (counted g) (gate w g).2 := by
  obtain ⟨op,xs⟩ := g
  cases op with
  | and =>
    rcases xs with _|⟨i,_|⟨j,t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made w _ _ _ (op_lt _ _) (get_simple w i) (get_simple w j)
  | or =>
    rcases xs with _|⟨i,_|⟨j,t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made w _ _ _ (op_lt _ _) (get_simple w i) (get_simple w j)
  | mod _ | maj => exact Or.inl (Or.inl rfl)
  | _ => exact Or.inl (get_simple w _)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def Good (m a : ℕ) := ∀ i<m, a.testBit i ≠ a.testBit (m+i)

def Live (m : ℕ) : ℕ → Finset ℕ → Prop
  | 0, S => ∃ a, S = {a} ∧ Good m a ∧ a ≠ 0
  | k+1, S => ∃ (U : Finset ℕ) (a b d : ℕ),
      S = insert a (insert b U) ∧
      d < 4 ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      combine d a b ∉ insert a (insert b U) ∧
      Live m k (insert (combine d a b) U)

namespace Live

lemma done {m a : ℕ} (hg : Good m a) (nonzero : a ≠ 0) : Live m 0 {a} := by
  rw [Live]
  exact ⟨a, rfl, hg, nonzero⟩

lemma step {m k : ℕ} {U : Finset ℕ} {a b d : ℕ}
    (hd : d < 4) (ha : a ≠ 0) (hb : b ≠ 0) (diff : a ≠ b)
    (fresh : combine d a b ∉ insert a (insert b U))
    (next : Live m k (insert (combine d a b) U)) :
    Live m (k+1) (insert a (insert b U)) := by
  rw [Live]
  exact ⟨U, a, b, d, rfl, hd, ha, hb, diff, fresh, next⟩

end Live

lemma liveNonzero {m k S} (h : Live m k S) : ∀ a∈S,a≠0 := by
  induction k generalizing S with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rfl, _, hn⟩ := h
    simpa using hn
  | succ k ih =>
    rw [Live] at h
    obtain ⟨U, a, b, d, rfl, _, ha, hb, _, _, tail⟩ := h
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact hb
    exact ih tail x (Finset.mem_insert_of_mem hx)
lemma liveSize {m k S} (h : Live m k S) : S.card≤k+1 := by
  induction k generalizing S with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rfl, _, _⟩ := h
    simp
  | succ k ih =>
    rw [Live] at h
    obtain ⟨U, a, b, d, rfl, _, _, _, _, fresh, tail⟩ := h
    have bound := ih tail
    have z : combine d a b ∉ U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    rw [Finset.card_insert_of_notMem z] at bound
    have u := Finset.card_insert_le a (insert b U)
    have v := Finset.card_insert_le b U
    omega
lemma combine_congr_bits (d a b i j : ℕ) (p : a.testBit i=a.testBit j) (q : b.testBit i=b.testBit j) :
    (combine d a b).testBit i=(combine d a b).testBit j := by
  rcases d with _|(_|(_|d)) <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,p,q]
lemma liveSeparates {m k S} (h : Live m k S) (i : ℕ) (hi : i<m) :
    ∃ a∈S,a.testBit i≠a.testBit (m+i) := by
  induction k generalizing S with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rfl, hg, _⟩ := h
    exact ⟨a, Finset.mem_singleton_self a, hg i hi⟩
  | succ k ih =>
    rw [Live] at h
    obtain ⟨U, a, b, d, rfl, _, _, _, _, _, tail⟩ := h
    obtain ⟨x,hx,dist⟩ := ih tail
    rcases Finset.mem_insert.mp hx with rfl|hx
    · by_cases v : a.testBit i=a.testBit (m+i)
      · exact ⟨b,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),fun u => dist (combine_congr_bits _ _ _ _ _ v u)⟩
      · exact ⟨a,Finset.mem_insert_self _ _,v⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx),dist⟩

lemma pull {m k S w z p} (h : Live m k S) (op : priced w p z)
    (sub : ∀ a∈S, a∈reps w ++ [z]) :
    ∃ l T, l ≤ k + p.toNat ∧ Live m l T ∧ ∀ a∈T, a∈reps w := by
  by_cases needed : z∈S
  · by_cases available : z∈reps w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a∈reps w ∨ a=z) with old|rfl
      · exact old
      · exact available
    · rcases op with easy|⟨rfl,d,hd,a,xa,b,xb,na,nb,ab,rfl⟩
      · rcases easy with e|e
        · exact ((liveNonzero h z needed) e).elim
        · exact (available e).elim
      · let g := combine d a b
        let U := S.erase g
        have tail : Live m k (insert g U) := by change Live m k (insert g (S.erase g)); rw [Finset.insert_erase (show g∈S from needed)]; exact h
        have old (x : ℕ) (hx : x∈U) : x∈reps w := by
          obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hx
          have h' : x∈reps w ∨ x=g := by simpa using sub x mem
          exact h'.resolve_right ne
        have fresh : g ∉ insert a (insert b U) := by
          intro eq
          rcases Finset.mem_insert.mp eq with e|h'
          · exact available (show g∈reps w by rw [e];exact xa)
          rcases Finset.mem_insert.mp h' with e|u
          · exact available (show g∈reps w by rw [e];exact xb)
          · exact available (old _ u)
        refine ⟨k+1,insert a (insert b U),by simp,Live.step hd na nb ab fresh tail,?_⟩
        simpa using And.intro xa (And.intro xb old)
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have ne : a≠z := fun e => needed (e ▸ ha)
    simpa [ne] using sub a ha

lemma extract {m out} (hg : Good m out) (hn : out≠0) (gs : List Gate) (w : List Wire)
    (found : out∈reps (execute gs w)) :
    ∃ k S, k≤gs.countP counted ∧ Live m k S ∧ ∀ a∈S, a∈reps w := by
  induction gs generalizing w with
  | nil => exact ⟨0,{out},by simp,Live.done hg hn,by simpa [execute] using found⟩
  | cons g gs ih =>
    obtain ⟨k,S,lim,h,sub⟩ := ih (w++[gate w g]) found
    have sub' : ∀ a∈S,a∈reps w ++ [(gate w g).2] := by simpa [reps] using sub
    obtain ⟨l,T,cost,ht,raw⟩ := pull h (gate_priced w g) sub'
    refine ⟨l,T,?_,ht,raw⟩
    cases e : counted g <;> simp [e,Bool.toNat] at cost ⊢ <;> omega
def separation (m a : ℕ) := a ^^^ (a >>> m)
def cover (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | a::t => separation m a ||| cover m t
def full (m : ℕ) := (1 <<< m)-1
def enough (m c : ℕ) := (c &&& full m) == full m
lemma coverBit (m i : ℕ) (v : List ℕ) : (cover m v).testBit i=true ↔
    ∃ a∈v,a.testBit i≠a.testBit (m+i) := by
  induction v with
  | nil => simp [cover]
  | cons a t ih =>
    simp only [cover,Nat.testBit_or,Bool.or_eq_true,ih,List.mem_cons,separation,Nat.testBit_xor,Nat.testBit_shiftRight]
    cases v1 : a.testBit i <;> cases v2 : a.testBit (m+i) <;> simp [v1,v2] <;> aesop
lemma enoughLive {m k S} (h : Live m k S) (v : List ℕ) (rep : v.toFinset=S) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have bit : (full m).testBit i=decide (i<m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases hi : i<m
  · have ⟨x,hx,good⟩ := liveSeparates h i hi
    have xc : x∈v := List.mem_toFinset.mp (rep ▸ hx)
    have mark := (coverBit m i v).2 ⟨x,xc,good⟩
    simp [mark,bit,hi]
  · simp [bit,hi]

def save (keep : Bool) (a : ℕ) (rest : List ℕ) := if keep then a::rest else rest
def without (v : List ℕ) (a b : ℕ) := v.filter (fun x => x != a && x != b)
def optionStep (m fuel : ℕ) (go : List ℕ → Bool) (rest : List ℕ) (n cv a b z : ℕ) (ka kb : Bool) : Bool :=
  let len := 1+n+ka.toNat+kb.toNat
  len ≤ fuel+1 && enough m (((separation m z ||| cv) ||| (if ka then separation m a else 0)) |||
    (if kb then separation m b else 0)) && go (z::save ka a (save kb b rest))
def gateStep (m fuel : ℕ) (go : List ℕ → Bool) (v rest : List ℕ) (n cv a b z : ℕ) : Bool :=
  z != 0 && !(v.contains z) &&
  (optionStep m fuel go rest n cv a b z false false || optionStep m fuel go rest n cv a b z true false ||
   optionStep m fuel go rest n cv a b z false true || optionStep m fuel go rest n cv a b z true true)
def pairStep (m fuel : ℕ) (go : List ℕ → Bool) (v : List ℕ) (a b : ℕ) : Bool :=
  if a<b then
    let rest := without v a b
    let check := gateStep m fuel go v rest rest.length (cover m rest) a b
    check (a &&& b) || check (a ||| b) || check (a ^^^ (a &&& b)) || check (b ^^^ (a &&& b))
  else false
def anyGate (m fuel : ℕ) (go : List ℕ → Bool) (v : List ℕ) : Bool :=
  v.any (fun a => v.any (fun b => pairStep m fuel go v a b))
def terminal (m : ℕ) (v : List ℕ) := v.any (fun a => enough m (separation m a))
def search (m : ℕ) : ℕ → List ℕ → Bool
  | 0, v => terminal m v
  | fuel+1, v => terminal m v || anyGate m fuel (search m fuel) v

lemma surface (m a i : ℕ) : (separation m a).testBit i=true ↔ a.testBit i≠a.testBit (m+i) := by
  simp only [separation,Nat.testBit_xor,Nat.testBit_shiftRight]
  cases a.testBit i <;> cases a.testBit (m+i) <;> decide
lemma ends {m a} (h : Good m a) (v : List ℕ) (mem : a∈v) : terminal m v=true := by
  apply List.any_eq_true.mpr;refine ⟨a,mem,?_⟩
  apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i;rw [Nat.testBit_and]
  have e : (full m).testBit i=decide (i<m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases l : i<m
  · simp [e,l,(surface _ _ _).2 (h i l)]
  · simp [e,l]
lemma option_ok {m fuel go rest a b z ka kb} (lim : (z::save ka a (save kb b rest)).length≤fuel+1)
    (cov : enough m (cover m (z::save ka a (save kb b rest)))=true)
    (next : go (z::save ka a (save kb b rest))=true) :
    optionStep m fuel go rest rest.length (cover m rest) a b z ka kb=true := by
  have size : 1+rest.length+ka.toNat+kb.toNat≤fuel+1 := by
    cases ka <;> cases kb <;> simp [save,Bool.toNat] at lim ⊢ <;> omega
  have eq : enough m (((separation m z ||| cover m rest) ||| (if ka then separation m a else 0)) ||| (if kb then separation m b else 0))=true := by
    cases ka <;> cases kb <;> simpa [save,cover,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using cov
  simp [optionStep,size,eq,next]
lemma gate_ok {m fuel go v rest n cv a b z ka kb} (nz : z≠0) (fresh : z∉v)
    (which : optionStep m fuel go rest n cv a b z ka kb=true) :
    gateStep m fuel go v rest n cv a b z=true := by
  cases ka <;> cases kb <;> simp [gateStep,nz,fresh,which]
lemma pair_ok {m fuel go v a b d} (ordered : a<b) (hd : d<4)
    (step : let rest := without v a b;gateStep m fuel go v rest rest.length (cover m rest) a b (combine d a b)=true) :
    pairStep m fuel go v a b=true := by
  interval_cases d <;> simp only [combine] at step <;> simp [pairStep,ordered,step]
lemma swapOp (d a b : ℕ) (hd : d<4) : ∃ e<4,combine d a b=combine e b a := by
  interval_cases d
  · exact ⟨0,by decide,Nat.and_comm a b⟩
  · exact ⟨1,by decide,Nat.or_comm a b⟩
  · exact ⟨3,by decide,by simp [combine,Nat.and_comm]⟩
  · exact ⟨2,by decide,by simp [combine,Nat.and_comm]⟩
lemma listNext {v : List ℕ} {a b z : ℕ} {U : Finset ℕ} (rep : v.toFinset=insert a (insert b U))
    (ab : a≠b) (fz : z∉insert a (insert b U)) (nd : v.Nodup) :
    let rest := without v a b
    let next := z::save (decide (a∈U)) a (save (decide (b∈U)) b rest)
    next.toFinset=insert z U ∧ next.Nodup := by
  dsimp only
  have mem (x : ℕ) : x∈without v a b ↔ x∈U ∧ x≠a ∧ x≠b := by
    simp only [without,List.mem_filter,Bool.and_eq_true,bne_iff_ne]
    have e : x∈v ↔ x=a ∨ x=b ∨ x∈U := by rw [← List.mem_toFinset,rep];simp
    tauto
  have nr := nd.filter (fun x => x != a && x != b)
  change (without v a b).Nodup at nr
  have md (x : ℕ) : (x∈save (decide (a∈U)) a (save (decide (b∈U)) b (without v a b))) ↔ x∈U := by
    by_cases xa : x=a
    · subst x; by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,ab]
    by_cases xb : x=b
    · subst x; by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,Ne.symm ab]
    by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,xa,xb]
  constructor
  · ext x;simp [md]
  · simp only [List.nodup_cons,md]
    refine ⟨fun m => fz (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m)),?_⟩
    have an : a∉without v a b := fun x => (mem _).1 x |>.2.1 rfl
    have bn : b∉without v a b := fun x => (mem _).1 x |>.2.2 rfl
    by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,nr,ab,an,bn]
lemma orderedStep {m fuel n U a b d v} {go : List ℕ→Bool} (hd : d<4)
    (lt : a<b) (nz : combine d a b≠0) (fresh : combine d a b∉insert a (insert b U))
    (rep : List.toFinset v=insert a (insert b U)) (nd : v.Nodup) (lim : n≤fuel)
    (tail : Live m n (insert (combine d a b) U))
    (nextOK : ∀ v : List ℕ, v.toFinset=insert (combine d a b) U → v.Nodup → go v=true) :
    pairStep m fuel go v a b=true := by
  let z := combine d a b
  let rest := without v a b
  let next := z::save (decide (a∈U)) a (save (decide (b∈U)) b rest)
  obtain ⟨r,nu⟩ := listNext (z:=z) rep (Nat.ne_of_lt lt) fresh nd
  have small := liveSize tail
  change (insert z U).card≤n+1 at small
  have length : next.length=(insert z U).card := by rw [←r,List.toFinset_card_of_nodup nu]
  have bound : next.length≤fuel+1 := by omega
  have coverOK := enoughLive tail next r
  have ok := option_ok bound coverOK (nextOK next r nu)
  apply pair_ok lt hd
  exact gate_ok nz (fun h => fresh (rep ▸ List.mem_toFinset.mpr h)) ok
lemma transition {m fuel n U a b d v} {go : List ℕ→Bool} (hd : d<4)
    (ab : a≠b) (fresh : combine d a b∉insert a (insert b U))
    (rep : List.toFinset v=insert a (insert b U)) (nd : v.Nodup) (lim : n≤fuel)
    (tail : Live m n (insert (combine d a b) U))
    (nextOK : ∀ v : List ℕ, v.toFinset=insert (combine d a b) U → v.Nodup → go v=true) :
    anyGate m fuel go v=true := by
  have ma : a∈v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_self _ _)
  have mb : b∈v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have nz := liveNonzero tail _ (Finset.mem_insert_self _ _)
  rcases lt_or_gt_of_ne ab with lt|gt
  · exact List.any_eq_true.mpr ⟨a,ma,List.any_eq_true.mpr ⟨b,mb,orderedStep hd lt nz fresh rep nd lim tail nextOK⟩⟩
  · obtain ⟨e,he,eq⟩ := swapOp d a b hd
    have rev : insert a (insert b U)=insert b (insert a U) := Finset.insert_comm a b U
    rw [rev] at fresh rep
    rw [eq] at fresh nz tail nextOK
    exact List.any_eq_true.mpr ⟨b,mb,List.any_eq_true.mpr ⟨a,ma,orderedStep he gt nz fresh rep nd lim tail nextOK⟩⟩

theorem complete (m fuel : ℕ) {n S} (h : Live m n S) (lim : n≤fuel)
    (v : List ℕ) (rep : v.toFinset=S) (nd : v.Nodup) : search m fuel v=true := by
  induction fuel generalizing n S v with
  | zero =>
    cases n with
    | zero =>
      rw [Live] at h
      obtain ⟨a, rfl, hg, _⟩ := h
      exact ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a))
    | succ n => omega
  | succ k ih =>
    rw [search,Bool.or_eq_true]
    cases n with
    | zero =>
      rw [Live] at h
      obtain ⟨a, rfl, hg, _⟩ := h
      exact Or.inl (ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a)))
    | succ n =>
      rw [Live] at h
      obtain ⟨U, a, b, d, rfl, hd, _, _, ab, fresh, tail⟩ := h
      exact Or.inr (transition hd ab fresh rep nd (by omega) tail (fun v hv nv => ih tail (by omega) v hv nv))

abbrev Projection (m h : ℕ) := { f : ℕ → ℕ //
  f 0 = 0 ∧ (∀ d a b, d < 4 → f (combine d a b) = combine d (f a) (f b)) ∧
  (∀ a, Good m a → Good h (f a)) ∧ 0 < h }

namespace Projection
def toFun {m h : ℕ} (p : Projection m h) : ℕ → ℕ := p.val
theorem atZero {m h : ℕ} (p : Projection m h) : p.toFun 0 = 0 := p.property.1
theorem combineEq {m h : ℕ} (p : Projection m h) (d a b : ℕ) (hd : d < 4) :
    p.toFun (combine d a b) = combine d (p.toFun a) (p.toFun b) :=
  p.property.2.1 d a b hd
theorem good {m h : ℕ} (p : Projection m h) (a : ℕ) (ha : Good m a) :
    Good h (p.toFun a) := p.property.2.2.1 a ha
theorem someRow {m h : ℕ} (p : Projection m h) : 0 < h := p.property.2.2.2
end Projection

def Possible (m k : ℕ) (av : List ℕ) :=
  ∃ j S, j≤k ∧ Live m j S ∧ ∀ x∈S,x∈av
def charge (av : List ℕ) (z : ℕ) := z != 0 && !(av.contains z)
lemma pullPaid {m k d a b : ℕ} {av : List ℕ} (hd : d<4) (ha : a∈av) (hb : b∈av)
    (later : Possible m k (av++[combine d a b])) :
    Possible m (k+(charge av (combine d a b)).toNat) av := by
  let w := av.map (fun x => (false,x))
  have repr : reps w=av := by simp [w,reps,List.map_map,Function.comp_def]
  obtain ⟨j,S,lim,live,sub⟩ := later
  have needed : ∀ x∈S,x∈reps w++[combine d a b] := by simpa [repr] using sub
  have price : priced w (charge av (combine d a b)) (combine d a b) := by
    by_cases nz : combine d a b=0
    · exact Or.inl (Or.inl nz)
    by_cases old : combine d a b∈av
    · exact Or.inl (Or.inr (repr ▸ old))
    have paid : charge av (combine d a b)=true := by simp [charge,nz,old]
    have special : ¬(a=0 ∨ b=0 ∨ a=b) := by
      intro h
      rcases combine_eq_cases _ _ _ hd h with zero|rfl'|rfl'
      · exact nz zero
      · exact old (by rw [rfl'];exact ha)
      · exact old (by rw [rfl'];exact hb)
    exact Or.inr ⟨paid,d,hd,a,repr ▸ ha,b,repr ▸ hb,
      fun x => special (Or.inl x),fun x => special (Or.inr (Or.inl x)),fun x => special (Or.inr (Or.inr x)),rfl⟩
  obtain ⟨l,T,le,ok,sub'⟩ := pull live price needed
  exact ⟨l,T,by omega,ok,by simpa [repr] using sub'⟩

def dead (p : ℕ→ℕ) (S : Finset ℕ) := (S.filter (fun x => p x=0)).card
lemma deadStay {p : ℕ→ℕ} {a : ℕ} {S : Finset ℕ} (h : p a≠0) : dead p (insert a S)=dead p S := by
  simp [dead,Finset.filter_insert,h]
lemma deadLimit (p : ℕ→ℕ) (a : ℕ) (S : Finset ℕ) : dead p (insert a S)≤dead p S+1 := by
  by_cases x : p a=0
  · simpa [dead,Finset.filter_insert,x] using Finset.card_insert_le a (S.filter (fun x => p x=0))
  · simp [deadStay x]
lemma deadMono (p : ℕ→ℕ) (a : ℕ) (S : Finset ℕ) : dead p S ≤ dead p (insert a S) := by
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
lemma deadGrow {p : ℕ→ℕ} {a : ℕ} {S : Finset ℕ} (z : p a=0) (fresh : a∉S) :
    dead p (insert a S)=dead p S+1 := by
  have nf : a∉S.filter (fun x => p x=0) := fun h => fresh (Finset.mem_filter.mp h).1
  simp [dead,Finset.filter_insert,z,Finset.card_insert_of_notMem nf]
lemma countCharge {m h d a b : ℕ} (p : Projection m h) (hd : d<4) (U : Finset ℕ)
    (fz : combine d a b∉insert a (insert b U)) (av : List ℕ) (ma : p.toFun a∈av) (mb : p.toFun b∈av) :
    (charge av (p.toFun (combine d a b))).toNat + dead p.toFun (insert a (insert b U)) ≤
      1+dead p.toFun (insert (combine d a b) U) := by
  have up := deadMono p.toFun (combine d a b) U
  have la := deadLimit p.toFun a (insert b U)
  have lb := deadLimit p.toFun b U
  have free (bad : p.toFun a=0 ∨ p.toFun b=0) : charge av (p.toFun (combine d a b))=false := by
    rw [p.combineEq _ _ _ hd]
    rcases combine_eq_cases _ _ _ hd (bad.imp_right Or.inl) with e|e|e <;> simp [charge,e,ma,mb]
  by_cases az : p.toFun a=0
  · rw [free (Or.inl az)];simp only [Bool.toNat_false,Nat.zero_add]
    by_cases bz : p.toFun b=0
    · have zz : p.toFun (combine d a b)=0 := by
        rw [p.combineEq _ _ _ hd,az,bz];interval_cases d <;> decide
      have fresh : combine d a b∉U := fun m => fz (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
      rw [deadGrow zz fresh];omega
    · rw [deadStay bz] at la;omega
  · rw [deadStay az]
    by_cases bz : p.toFun b=0
    · rw [free (Or.inr bz)];simp only [Bool.toNat_false,Nat.zero_add];omega
    · rw [deadStay bz];cases charge av (p.toFun (combine d a b)) <;> simp [Bool.toNat] <;> omega

theorem projectLive {m h k S} (p : Projection m h) (live : Live m k S) :
    ∃ j T,j+dead p.toFun S≤k ∧ Live h j T ∧ ∀ x∈T,x∈S.image p.toFun := by
  induction k generalizing S with
  | zero =>
    rw [Live] at live
    obtain ⟨a, rfl, hg, _⟩ := live
    have gp := p.good a hg
    have nz : p.toFun a≠0 := by intro e;have x := gp 0 p.someRow;simp [e] at x
    exact ⟨0,{p.toFun a},by simp [dead,nz],Live.done gp nz,by simp⟩
  | succ k ih =>
    rw [Live] at live
    obtain ⟨U, a, b, d, rfl, hd, ha, hb, ab, fz, tail⟩ := live
    obtain ⟨j,T,cost,ok,raw⟩ := ih tail
    let av := ((insert a (insert b U)).image p.toFun).toList
    have ma : p.toFun a∈av := by simp [av]
    have mb : p.toFun b∈av := by simp [av]
    have later : Possible h j (av++[combine d (p.toFun a) (p.toFun b)]) := by
      refine ⟨j,T,le_rfl,ok,?_⟩
      intro z hz
      have has := raw _ hz
      simp only [Finset.image_insert,Finset.mem_insert] at has
      rcases has with rfl|old
      · simp [p.combineEq d a b hd]
      · have inav : z∈av := by simpa [av] using (Or.inr (Or.inr old) : z=p.toFun a ∨ z=p.toFun b ∨ z∈U.image p.toFun)
        simp [inav]
    obtain ⟨l,V,lim,good,sub⟩ := pullPaid hd ma mb later
    rw [←p.combineEq d a b hd] at lim
    have bound := countCharge p hd U fz av ma mb
    exact ⟨l,V,by omega,good,by simpa [av] using sub⟩

lemma full_bit (m i : ℕ) : (full m).testBit i=decide (i<m) := by
  simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]

lemma enoughSup {m k S} (h : Live m k S) (v : List ℕ) (sub : ∀ x∈S,x∈v) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i
  rw [Nat.testBit_and,full_bit]
  by_cases hi : i<m
  · obtain ⟨x,hx,g⟩ := liveSeparates h i hi
    have bit := (coverBit m i v).2 ⟨x,sub _ hx,g⟩
    simp [bit,hi]
  · simp [hi]
def start (m fuel : ℕ) (av : List ℕ) :=
  let v := av.eraseDups.filter (fun x => x != 0)
  let needed := fun a => !(enough m (cover m (v.filter (fun x => x != a))))
  let must := v.filter needed
  let extra := v.filter (fun x => !needed x)
  extra.sublists.any (fun t =>
    let s := (must++t).dedup
    s.length≤fuel+1 && enough m (cover m s) && search m fuel s)

theorem start_complete {m k S} (h : Live m k S) (av : List ℕ) (sub : ∀ x∈S,x∈av)
    (fuel : ℕ) (lim : k≤fuel) : start m fuel av=true := by
  let v := av.eraseDups.filter (fun x => x != 0)
  let needed := fun a => !(enough m (cover m (v.filter (fun x => x != a))))
  let must := v.filter needed
  let extra := v.filter (fun x => !needed x)
  let t := extra.filter (fun x => decide (x∈S))
  let s := (must++t).dedup
  have inV (x : ℕ) (hx : x∈S) : x∈v := by simp [v,sub x hx,liveNonzero h x hx]
  have fixed (a : ℕ) (ha : a∈must) : a∈S := by
    by_contra absent
    have no := (List.mem_filter.mp ha).2
    have all (x : ℕ) (hx : x∈S) : x∈v.filter (fun y => y != a) := by
      have ne : x≠a := by rintro rfl;exact absent hx
      simp [inV x hx,ne]
    have yes := enoughSup h _ all
    simpa [needed,yes] using no
  have eq : s.toFinset=S := by
    ext x
    constructor
    · intro mem
      have e : x∈must ∨ x∈t := by simpa [s] using mem
      rcases e with l|r
      · exact fixed x l
      · simpa using (List.mem_filter.mp r).2
    · intro mem
      have raw := inV x mem
      cases H : needed x <;> simp [s,must,t,extra,H,raw,mem]
  have nd : s.Nodup := List.nodup_dedup _
  have size : s.length≤fuel+1 := by
    have vsize := liveSize h
    rw [←eq,List.toFinset_card_of_nodup nd] at vsize;omega
  have test := complete m fuel h lim s eq nd
  have cov := enoughLive h s eq
  apply List.any_eq_true.mpr
  refine ⟨t,List.mem_sublists.mpr (List.filter_sublist),?_⟩
  change (decide (s.length≤fuel+1) && enough m (cover m s) && search m fuel s)=true
  simp [size,cov,test]

def actL : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, w => Nat.bit (w.testBit p) (actL ps w)

theorem actL_testBit : ∀ (pi : List ℕ) (w k : ℕ),
    (actL pi w).testBit k = (pi[k]?.map w.testBit).getD false
  | [], w, k => by simp [actL]
  | p :: ps, w, 0 => by simp [actL, Nat.testBit_bit_zero]
  | p :: ps, w, k + 1 => by simp [actL, Nat.testBit_bit_succ, actL_testBit ps w k]

theorem actL_and (pi : List ℕ) (a b : ℕ) : actL pi (a &&& b) = actL pi a &&& actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_and]

theorem actL_or (pi : List ℕ) (a b : ℕ) : actL pi (a ||| b) = actL pi a ||| actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_or, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_or]

theorem actL_xor (pi : List ℕ) (a b : ℕ) : actL pi (a ^^^ b) = actL pi a ^^^ actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_xor, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_xor]

def coord (m : ℕ) (r : List ℕ) := actL (r ++ r.map (m+·))

theorem coordC (m : ℕ) (r : List ℕ) (d a b : ℕ) (hd : d < 4) :
    coord m r (combine d a b) = combine d (coord m r a) (coord m r b) := by
  interval_cases d <;> simp [combine,coord,actL_and,actL_or,actL_xor]

def pick {m h : ℕ} (r : List ℕ) (len : r.length=h) (small : ∀ i∈r,i<m) (pos : 0<h) : Projection m h := by
  refine ⟨coord m r, ?_, coordC m r, ?_, pos⟩
  · apply Nat.eq_of_testBit_eq
    intro i
    simp only [coord,actL_testBit,Nat.zero_testBit]
    cases (r ++ r.map (m+·))[i]? <;> simp
  · intro a ha i hi
    have ir : i<r.length := by omega
    have b := ha r[i] (small _ (List.getElem_mem ir))
    have H₁ : (r ++ r.map (m+·))[i]? = some r[i] := by simp [List.getElem?_append,ir]
    have H₂ : (r ++ r.map (m+·))[h+i]? = some (m+r[i]) := by
      have ne : ¬h+i<r.length := by omega
      have sub : h+i-r.length=i := by omega
      simp [List.getElem?_append,ne,sub,ir]
    simpa [coord,actL_testBit,H₁,H₂] using b

def Ban (m fuel : ℕ) (v : List ℕ) := ∀ n, n ≤ fuel → ¬Live m n v.toFinset
def Wide (m fuel : ℕ) (v : List ℕ) := ¬Possible m fuel v

theorem viaSearch {m fuel v} (test : start m fuel v=false) : Wide m fuel v := by
  rintro ⟨k,S,le,live,sub⟩
  have := start_complete live v sub fuel le
  simp_all

theorem viaCut {m h f t : ℕ} {v w : List ℕ} (p : Projection m h)
    (bound : Wide h t w) (nd : v.Nodup)
    (mem : ∀ a∈v, p.toFun a=0 ∨ p.toFun a∈w)
    (cost : f≤t+(v.map p.toFun).count 0) : Ban m f v := by
  intro k lim run
  obtain ⟨j,T,c,ok,incl⟩ := projectLive p run
  have fixed : dead p.toFun v.toFinset=(v.map p.toFun).count 0 := by
    dsimp [dead]
    have E : v.toFinset.filter (fun x => p.toFun x=0) = (v.filter (fun x => decide (p.toFun x=0))).toFinset := by ext x;simp
    rw [E,List.toFinset_card_of_nodup (nd.filter _)]
    simp only [List.count_eq_countP,List.countP_map,Function.comp_apply]
    rw [List.countP_eq_length_filter]
    congr 2
  rw [fixed] at c
  apply bound
  refine ⟨j,T,by omega,ok,?_⟩
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp (incl _ hx)
  exact (mem y (List.mem_toFinset.mp hy)).resolve_left (liveNonzero ok _ hx)

theorem renameLive {m h k S} (p : Projection m h) (q : Projection h m)
    (run : Live m k S) (rec : ∀ x∈S, q.toFun (p.toFun x)=x) : Live h k (S.image p.toFun) := by
  induction k generalizing S with
  | zero =>
    rw [Live] at run
    obtain ⟨a,rfl,good,nz⟩ := run
    simp only [Finset.image_singleton]
    apply Live.done (p.good a good)
    intro e
    have := rec a (Finset.mem_singleton_self a)
    rw [e,q.atZero] at this
    exact nz this.symm
  | succ k ih =>
    rw [Live] at run
    obtain ⟨U,a,b,d,rfl,hd,ha,hb,ab,fr,tail⟩ := run
    let z := combine d a b
    have ra := rec a (Finset.mem_insert_self _ _)
    have rb := rec b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have rz : q.toFun (p.toFun z)=z := by simp only [z,p.combineEq _ _ _ hd,q.combineEq _ _ _ hd,ra,rb]
    have ru (x) (hx : x∈U) := rec x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
    have nr := ih tail (by intro x hx; rcases Finset.mem_insert.mp hx with rfl|h; exact rz; exact ru _ h)
    have eqz : p.toFun z=combine d (p.toFun a) (p.toFun b) := p.combineEq _ _ _ hd
    simp only [Finset.image_insert] at nr ⊢
    apply Live.step hd
    · intro e;rw [e,q.atZero] at ra;exact ha ra.symm
    · intro e;rw [e,q.atZero] at rb;exact hb rb.symm
    · intro e;rw [e,rb] at ra;exact ab ra.symm
    · rw [←eqz]
      intro bad
      rcases Finset.mem_insert.mp bad with e|bad
      · have hza := congrArg q.toFun e
        rw [rz,ra] at hza
        exact fr (Finset.mem_insert.mpr (Or.inl hza))
      rcases Finset.mem_insert.mp bad with e|bad
      · have hzb := congrArg q.toFun e
        rw [rz,rb] at hzb
        exact fr (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl hzb)))
      obtain ⟨x,hx,e⟩ := Finset.mem_image.mp bad
      have eq := congrArg q.toFun e
      rw [ru x hx,rz] at eq
      exact fr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (eq ▸ hx : z ∈ U)))
    · simpa only [p.combineEq _ _ _ hd] using nr

theorem viaPerm {m h f v w} (p : Projection m h) (q : Projection h m)
    (ban : Ban h f w) (rec : ∀ a∈v, q.toFun (p.toFun a)=a)
    (eq : (v.map p.toFun).toFinset=w.toFinset) : Ban m f v := by
  intro n hn live
  have ok := renameLive p q live (by simpa using rec)
  apply ban n hn
  have E : (v.map p.toFun).toFinset=v.toFinset.image p.toFun := by ext x;simp
  rw [←eq,E];exact ok

def ordered (v : List ℕ) := v.insertionSort (· ≤ ·)
theorem ord_eq (v : List ℕ) : (ordered v).toFinset=v.toFinset := by
  ext x;simp [ordered,List.mem_insertionSort]
def banList (m f : ℕ) (vs : List (List ℕ)) := ∀ v∈vs, Ban m f v
theorem consBan {m f a l} (h : Ban m f a) (t : banList m f l) : banList m f (a::l) := by
  intro v hv;rcases List.mem_cons.mp hv with rfl|e;exact h;exact t _ e
theorem nilBan (m f) : banList m f [] := by simp [banList]

theorem viaBranch {m f : ℕ} {v : List ℕ} {ws : List (List ℕ)} (closed : banList m f ws)
    (nd : v.Nodup) (no : terminal m v=false)
    (test : anyGate m f (fun u => !ws.contains (ordered u)) v=false) : Ban m (f+1) v := by
  intro n lim live
  cases n with
  | zero =>
    rw [Live] at live
    obtain ⟨a,rep,g,_⟩ := live
    have ev := ends g v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a))
    simp_all
  | succ n =>
    rw [Live] at live
    obtain ⟨U,a,b,d,rep,hd,_,_,ab,fr,tail⟩ := live
    have yes := @transition m f n U a b d v (fun u => !ws.contains (ordered u)) hd ab fr rep nd (by omega) tail (by
      intro u hu nu
      change (!ws.contains (ordered u))=true
      simp
      intro found
      have hv := closed _ found n (by omega)
      rw [ord_eq,hu] at hv
      exact hv tail)
    simp_all

theorem widen {m f v} (ess : ∀ a∈v, ∃ i : Fin m, ∀ b∈v, b.testBit i.val≠b.testBit (m+i.val) → b=a)
    (h : Ban m f v) : Wide m f v := by
  rintro ⟨n,S,le,live,sub⟩
  have eq : S=v.toFinset := by
    apply Finset.Subset.antisymm (fun x hx => List.mem_toFinset.mpr (sub _ hx))
    intro a ha
    obtain ⟨i,hi⟩ := ess a (List.mem_toFinset.mp ha)
    obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
    exact hi b (sub b hb) sep ▸ hb
  exact h n le (eq ▸ live)

theorem viaSmall {m f v} (ex : search m f v=false) (nd : v.Nodup) : Ban m f v := by
  intro n le live
  have := complete m f live le v rfl nd
  simp_all

theorem viaSub {m f v ws} (bs : banList m f ws) (nd : v.Nodup)
    (check : v.sublists.all (fun u => !(u.length≤f+1 && enough m (cover m u)) || ws.contains u)=true) :
    Wide m f v := by
  rintro ⟨n,S,lim,live,sub⟩
  let u := v.filter (fun x => decide (x∈S))
  have eq : u.toFinset=S := by ext x; simp [u]; exact fun hx => sub _ hx
  have nd' : u.Nodup := nd.filter _
  have len := liveSize live
  rw [←eq,List.toFinset_card_of_nodup nd'] at len
  have ok := List.all_eq_true.mp check u (List.mem_sublists.mpr List.filter_sublist)
  have cap : u.length≤f+1 := by omega
  have cov := enoughLive live u eq
  simp [cap,cov] at ok
  exact bs u ok n lim (eq ▸ live)

end PEqualNP.Outside.L_meta_16501.Support

namespace PEqualNP.Outside.L_meta_16501.Support.Core0
theorem smallByCut {m h f t : Nat} {v w : List Nat} (p : Projection m h) (bound : Wide h t w)
    (nd : v.Nodup := by decide) (mem : ∀ a∈v, p.toFun a=0 ∨ p.toFun a∈w := by decide +kernel)
    (cost : f≤t+(v.map p.toFun).count 0 := by decide +kernel) : Ban m f v :=
  viaCut p bound nd mem cost

theorem solid {m f : Nat} {v : List Nat} (bound : Ban m f v)
    (ess : ∀ a∈v, ∃ i : Fin m, ∀ b∈v, b.testBit i.val≠b.testBit (m+i.val) → b=a := by decide +kernel) :
    Wide m f v := widen ess bound

theorem bySubset {m f t : Nat} {v w : List Nat} (bound : Wide m t w)
    (sub : ∀ a∈v, a∈w := by decide +kernel) (le : f≤t := by decide) : Ban m f v := by
  intro j h hb
  exact bound ⟨j,v.toFinset,h.trans le,hb,fun x hx => sub x (List.mem_toFinset.mp hx)⟩

theorem checkedSmall {m f : Nat} {v : List Nat} (ex : search m f v = false := by decide +kernel)
    (nd : v.Nodup := by decide) : Ban m f v := viaSmall ex nd

def t0 := 0x2344c519f3f3
def t1 := 0x188921ae63c9f
def t2 := 0xc152c6307cf1c
def t3 := 0xec03b03f80fe0
def t4 := 0xf7ec003fff000
def v0 := [t0,t1,t2,t3,t4]
def t5 := 0x3093
def v1 := [t5,t0,t1,t2,t3,t4]
def t6 := 0x2344c519c360
def v2 := [t5,t6,t1,t2,t3,t4]
def v3 := [t6,t0,t1,t2,t3,t4]
def t7 := 0x188921ae60c0c
def v4 := [t5,t0,t7,t2,t3,t4]
def v5 := [t0,t7,t1,t2,t3,t4]
def t8 := 0x10
def v6 := [t8,t0,t1,t2,t3,t4]
def t9 := 0xc152c6307ff9f
def v7 := [t0,t1,t9,t3,t4]
def v8 := [t5,t0,t1,t9,t3,t4]
def v9 := [t0,t1,t2,t9,t3,t4]
def t10 := 0x3083
def v10 := [t10,t0,t1,t2,t3,t4]
def t11 := 0xc152c6307cf0c
def v11 := [t0,t1,t11,t3,t4]
def v12 := [t5,t0,t1,t11,t3,t4]
def v13 := [t0,t1,t11,t2,t3,t4]
def t12 := 0x80
def v14 := [t12,t0,t1,t2,t3,t4]
def t13 := 0xec03b03f83ff3
def v15 := [t0,t1,t2,t13,t4]
def v16 := [t5,t0,t1,t2,t13,t4]
def v17 := [t0,t1,t2,t3,t13,t4]
def t14 := 0x3013
def v18 := [t14,t0,t1,t2,t3,t4]
def t15 := 0xec03b03f80f60
def v19 := [t0,t1,t2,t15,t4]
def v20 := [t5,t0,t1,t2,t15,t4]
def v21 := [t0,t1,t2,t15,t3,t4]
def t16 := 0x3000
def v22 := [t16,t0,t1,t2,t3,t4]
def t17 := 0xf7ec003fff093
def v23 := [t0,t1,t2,t3,t17]
def v24 := [t5,t0,t1,t2,t3,t17]
def v25 := [t0,t1,t2,t3,t4,t17]
def t18 := 0x93
def v26 := [t18,t0,t1,t2,t3,t4]
def t19 := 0xf7ec003ffc000
def v27 := [t0,t1,t2,t3,t19]
def v28 := [t5,t0,t1,t2,t3,t19]
def v29 := [t0,t1,t2,t3,t19,t4]
def t20 := 0x1abd6dfffffff
def v30 := [t5,t20,t2,t3,t4]
def v31 := [t5,t0,t20,t2,t3,t4]
def v32 := [t5,t1,t20,t2,t3,t4]
def v33 := [t0,t1,t20,t2,t3,t4]
def v34 := [t6,t0,t20,t2,t3,t4]
def v35 := [t7,t1,t20,t2,t3,t4]
def t21 := 0xc376ce71fffff
def v36 := [t1,t20,t2,t21,t3,t4]
def t22 := 0x2240841830e3
def v37 := [t22,t1,t20,t2,t3,t4]
def t23 := 0xfc8bb1bfe3fff
def v38 := [t0,t20,t2,t3,t4,t23]
def t24 := 0x108801806301f
def v39 := [t0,t24,t20,t2,t3,t4]
def t25 := 0x1044307cf1c
def v40 := [t25,t0,t1,t3,t4]
def v41 := [t25,t0,t1,t20,t3,t4]
def v42 := [t25,t0,t1,t2,t3,t4]
def t26 := 0xdbffeffffffff
def v43 := [t0,t1,t2,t26,t3,t4]
def t27 := 0x1aad29cf830e3
def v44 := [t0,t1,t27,t3,t4]
def v45 := [t0,t1,t27,t20,t3,t4]
def v46 := [t0,t1,t27,t2,t3,t4]
def t28 := 0xc142820000000
def v47 := [t0,t1,t28,t2,t3,t4]
def t29 := 0x801203f80fe0
def v48 := [t0,t29,t1,t2,t4]
def v49 := [t0,t29,t1,t20,t2,t4]
def v50 := [t0,t29,t1,t2,t3,t4]
def t30 := 0xfebffdfffffff
def v51 := [t0,t1,t2,t3,t4,t30]
def t31 := 0x12bc4dc07f01f
def v52 := [t0,t31,t1,t2,t4]
def v53 := [t0,t31,t1,t20,t2,t4]
def v54 := [t0,t31,t1,t2,t3,t4]
def t32 := 0xe402900000000
def v55 := [t0,t1,t2,t32,t3,t4]
def t33 := 0x12ac003fff000
def v56 := [t0,t33,t1,t2,t3]
def v57 := [t0,t33,t1,t20,t2,t3]
def v58 := [t0,t33,t1,t2,t3,t4]
def t34 := 0xfffd6dfffffff
def v59 := [t0,t1,t2,t3,t4,t34]
def t35 := 0x8116dc000fff
def v60 := [t0,t35,t1,t2,t3]
def v61 := [t0,t35,t1,t20,t2,t3]
def v62 := [t0,t35,t1,t2,t3,t4]
def t36 := 0xe540000000000
def v63 := [t0,t1,t2,t36,t3,t4]
def t37 := 0x1044101c300
def v64 := [t37,t0,t1,t2,t3,t4]
def t38 := 0xc376ce71fcf7c
def v65 := [t0,t1,t2,t38,t3,t4]
def t39 := 0x224084180060
def v66 := [t39,t0,t1,t2,t3,t4]
def t40 := 0xc142822060c1c
def v67 := [t0,t1,t40,t2,t3,t4]
def t41 := 0x1180360
def v68 := [t41,t0,t1,t2,t3,t4]
def t42 := 0xee37fc7f9cfe0
def v69 := [t0,t1,t2,t3,t42,t4]
def t43 := 0x2344c401c000
def v70 := [t43,t0,t1,t2,t3,t4]
def t44 := 0xec03b02e00c80
def v71 := [t0,t1,t2,t44,t3,t4]
def t45 := 0x22400119c000
def v72 := [t45,t0,t1,t2,t3,t4]
def t46 := 0xf7fc4c7fff360
def v73 := [t0,t1,t2,t3,t4,t46]
def t47 := 0x104c4000360
def v74 := [t47,t0,t1,t2,t3,t4]
def t48 := 0xf5c8002e63000
def v75 := [t0,t1,t2,t3,t48,t4]
def v76 := [t6,t7,t2,t3,t4]
def v77 := [t6,t0,t7,t2,t3,t4]
def v78 := [t6,t7,t1,t2,t3,t4]
def v79 := [t6,t1,t2,t21,t3,t4]
def v80 := [t22,t6,t1,t2,t3,t4]
def map31_1 : Projection 26 26 := pick [1,0,5,6,7,2,3,4,10,11,8,9,13,12,21,22,23,19,20,17,18,14,15,16,25,24] rfl (by decide +kernel) (by decide)
def t49 := 0x1044101c310
def v81 := [t49,t0,t1,t2,t3,t4]
def v82 := [t0,t1,t2,t21,t3,t4]
def v83 := [t49,t1,t21,t3,t4]
def v84 := [t49,t0,t1,t21,t3,t4]
def v85 := [t49,t1,t2,t21,t3,t4]
def v86 := [t22,t0,t1,t21,t3,t4]
def t50 := 0xc142822060c0c
def v87 := [t1,t50,t2,t21,t3,t4]
def v88 := [t0,t1,t50,t2,t3,t4]
def t51 := 0xd9dbe7be7ff9f
def v89 := [t0,t1,t21,t51,t3,t4]
def t52 := 0xc152c6101c300
def v90 := [t0,t1,t52,t21,t3,t4]
def t53 := 0x2063c9f
def v91 := [t53,t0,t1,t2,t3,t4]
def t54 := 0x1889218e00000
def v92 := [t0,t54,t1,t2,t3,t4]
def t55 := 0xc376ce519c360
def v93 := [t0,t1,t2,t55,t3,t4]
def v94 := [t22,t0,t1,t2,t3,t4]
def t56 := 0xed53f63ffcffc
def v95 := [t0,t1,t21,t3,t56,t4]
def t57 := 0x15046007c01c
def v96 := [t57,t0,t1,t21,t3,t4]
def t58 := 0xc14000307c000
def v97 := [t0,t1,t58,t21,t3,t4]
def t59 := 0x36ac000f83000
def v98 := [t0,t1,t59,t21,t3,t4]
def t60 := 0xc002803180fe0
def v99 := [t0,t1,t60,t2,t3,t4]
def t61 := 0xef77fe7ffffff
def v100 := [t0,t1,t2,t3,t61,t4]
def t62 := 0x3744e407f01f
def v101 := [t0,t62,t1,t2,t3,t4]
def t63 := 0x2c01300e00000
def v102 := [t0,t1,t63,t2,t3,t4]
def t64 := 0xc3640031ff000
def v103 := [t0,t1,t2,t64,t3,t4]
def t65 := 0xf7fece7ffffff
def v104 := [t0,t1,t2,t3,t4,t65]
def t66 := 0x12ce4000fff
def v105 := [t66,t0,t1,t2,t3,t4]
def t67 := 0x3488000e00000
def v106 := [t0,t1,t67,t2,t3,t4]
def v107 := [t49,t22,t1,t2,t3,t4]
def t68 := 0x1aad29efe3cff
def v108 := [t0,t1,t68,t2,t3,t4]
def t69 := 0x188921ae60c1c
def v109 := [t0,t69,t1,t2,t3,t4]
def t70 := 0x1800e0
def v110 := [t70,t0,t1,t2,t3,t4]
def t71 := 0xee27b87f83fe3
def v111 := [t0,t1,t2,t3,t71,t4]
def t72 := 0x224084003003
def v112 := [t72,t0,t1,t2,t3,t4]
def t73 := 0xec03b03e00f00
def v113 := [t0,t1,t2,t73,t3,t4]
def t74 := 0x224000183000
def v114 := [t74,t0,t1,t2,t3,t4]
def t75 := 0xf7ec087fff0e3
def v115 := [t0,t1,t2,t3,t75]
def v116 := [t22,t0,t1,t2,t3,t75]
def v117 := [t0,t1,t2,t3,t4,t75]
def t76 := 0x840000e3
def v118 := [t76,t0,t1,t2,t3,t4]
def t77 := 0xf5c8003e7c000
def v119 := [t0,t1,t2,t3,t77]
def v120 := [t22,t0,t1,t2,t3,t77]
def v121 := [t0,t1,t2,t3,t77,t4]
def v122 := [t22,t1,t50,t3,t4]
def v123 := [t22,t0,t1,t50,t3,t4]
def v124 := [t22,t1,t50,t2,t3,t4]
def t78 := 0x2060c1c
def v125 := [t78,t22,t0,t1,t3,t4]
def t79 := 0x1889218e03083
def v126 := [t22,t0,t79,t1,t3,t4]
def t80 := 0x1b13f3
def t81 := 0x446c7f
def t82 := 0xa98f9c
def t83 := 0xf60fe0
def v127 := [t80,t81,t82,t83]
def p31_27 : Projection 26 12 := pick [1,0,5,6,7,13,12,21,22,23,19,20] rfl (by decide +kernel) (by decide)
def t84 := 0x11803e0
def v128 := [t84,t0,t1,t2,t3,t4]
def p31_23 : Projection 26 12 := pick [0,1,2,3,4,12,13,14,15,16,17,18] rfl (by decide +kernel) (by decide)
def t85 := 0xee37fc7f9fff3
def v129 := [t0,t1,t2,t3,t85,t4]
def v130 := [t0,t1,t2,t51,t3,t4]
def v131 := [t0,t1,t50,t51,t3,t4]
def t86 := 0x1044101f393
def v132 := [t86,t0,t1,t2,t3,t4]
def t87 := 0xd9cba3ae60c0c
def v133 := [t0,t1,t2,t87,t3,t4]
def v134 := [t78,t0,t51,t3,t4]
def v135 := [t78,t0,t1,t51,t3,t4]
def v136 := [t78,t0,t2,t51,t3,t4]
def v137 := [t0,t79,t1,t51,t3,t4]
def v138 := [t0,t52,t2,t51,t3,t4]
def v139 := [t0,t1,t52,t2,t3,t4]
def v140 := [t0,t79,t1,t2,t3,t4]
def t88 := 0xc803a03e00f80
def v141 := [t0,t1,t2,t88,t3,t4]
def t89 := 0xfddbf7bffffff
def v142 := [t0,t1,t2,t3,t4,t89]
def t90 := 0x11d847807f01f
def v143 := [t0,t90,t1,t2,t3,t4]
def t91 := 0x2400100180060
def v144 := [t0,t1,t91,t2,t3,t4]
def t92 := 0xd1c8003e7f000
def v145 := [t0,t1,t2,t92,t3]
def v146 := [t0,t1,t2,t92,t51,t3]
def v147 := [t0,t1,t2,t92,t3,t4]
def t93 := 0xffffe7bffff9f
def v148 := [t0,t1,t2,t3,t4,t93]
def t94 := 0x813e78000f9f
def v149 := [t0,t94,t1,t2,t3]
def v150 := [t0,t94,t1,t2,t51,t3]
def v151 := [t0,t94,t1,t2,t3,t4]
def t95 := 0x2624000180000
def v152 := [t0,t1,t95,t2,t3,t4]
def t96 := 0x2344c401f013
def v153 := [t96,t0,t1,t2,t3,t4]
def v154 := [t84,t96,t1,t2,t3,t4]
def t97 := 0x1abd6dee7fc9f
def v155 := [t0,t1,t97,t2,t3,t4]
def t98 := 0x188921ae60c8c
def v156 := [t0,t98,t1,t2,t3,t4]
def t99 := 0x1044001c010
def v157 := [t99,t0,t1,t2,t3,t4]
def t100 := 0xc376ce707ff1f
def v158 := [t0,t1,t2,t100,t3,t4]
def t101 := 0xc142823060f0c
def v159 := [t0,t1,t101,t2,t3,t4]
def v160 := [t96,t0,t1,t2,t85,t4]
def t102 := 0x22400001f000
def v161 := [t102,t0,t1,t2,t3,t4]
def t103 := 0xf7fc4c7fff013
def v162 := [t0,t1,t2,t3,t4,t103]
def t104 := 0x104c4000013
def v163 := [t104,t0,t1,t2,t3,t4]
def t105 := 0xf5c8003fe0000
def v164 := [t0,t1,t2,t3,t105,t4]
def t106 := 0xec03b02e00c00
def v165 := [t96,t1,t2,t106,t4]
def v166 := [t96,t0,t1,t2,t106,t4]
def v167 := [t96,t1,t2,t106,t3,t4]
def t107 := 0x801202e00c80
def v168 := [t96,t0,t107,t1,t2,t4]
def v169 := [t96,t0,t24,t1,t2,t4]
def v170 := [t96,t0,t1,t2,t56,t4]
def t108 := 0x2c01300f800e0
def v171 := [t96,t0,t1,t108,t2,t4]
def t109 := 0xe400003f80000
def v172 := [t96,t0,t1,t2,t109,t4]
def t110 := 0x13ec00007f000
def v173 := [t96,t0,t110,t1,t2,t4]
def v174 := [t0,t1,t2,t106,t3,t4]
def t111 := 0x22400119f000
def v175 := [t111,t0,t1,t2,t3,t4]
def t112 := 0x104c40003f3
def v176 := [t112,t111,t1,t2,t3,t4]
def v177 := [t112,t0,t1,t2,t3,t4]
def t113 := 0x1aad21bfffc9f
def v178 := [t0,t1,t113,t2,t3,t4]
def t114 := 0x188921ae60c9f
def v179 := [t0,t114,t1,t2,t3,t4]
def t115 := 0x101c000
def v180 := [t115,t0,t1,t2,t3,t4]
def t116 := 0xc376c631fff1c
def v181 := [t0,t1,t2,t116,t3,t4]
def t117 := 0xc152c62060f1c
def v182 := [t0,t1,t117,t2,t3,t4]
def t118 := 0x1180000
def v183 := [t118,t0,t1,t2,t3,t4]
def t119 := 0xee27b03f9ffe0
def v184 := [t0,t1,t2,t3,t119,t4]
def t120 := 0xec03b02e00fe0
def v185 := [t0,t1,t2,t120,t3,t4]
def t121 := 0xf5c8002e60000
def v186 := [t111,t0,t1,t2,t3,t121]
def v187 := [t0,t1,t2,t3,t121,t4]
def t122 := 0xf7fc4c7fff3f3
def v188 := [t111,t1,t2,t3,t122]
def v189 := [t111,t0,t1,t2,t3,t122]
def v190 := [t111,t1,t2,t3,t4,t122]
def t123 := 0x1088002e63000
def v191 := [t111,t0,t123,t1,t2,t3]
def t124 := 0x801218000c9f
def v192 := [t111,t0,t124,t1,t2,t3]
def t125 := 0xf7fec63ffff1c
def v193 := [t111,t0,t1,t2,t3,t125]
def v194 := [t111,t0,t1,t59,t2,t3]
def v195 := [t111,t0,t1,t2,t109,t3]
def t126 := 0x803b00000fe0
def v196 := [t111,t0,t126,t1,t2,t3]
def v197 := [t0,t1,t2,t3,t4,t122]
def v198 := [t112,t0,t1,t2,t3,t122]
def v199 := [t1,t2,t3,t121,t4,t122]
def t127 := 0xffed21bfffc9f
def v200 := [t0,t1,t2,t3,t122,t127]
def t128 := 0xe76400119c000
def v201 := [t0,t1,t2,t128,t3,t122]
def t129 := 0x1088002e63093
def v202 := [t0,t129,t1,t2,t3,t4]
def t130 := 0x801218000c0c
def v203 := [t0,t130,t1,t2,t3,t4]
def t131 := 0xe7744c519c360
def v204 := [t0,t1,t2,t131,t3,t4]
def v205 := [t0,t1,t58,t2,t3,t122]
def t132 := 0x12c60000f1c
def v206 := [t132,t0,t1,t2,t3,t122]
def t133 := 0xc15044307c310
def v207 := [t0,t1,t133,t2,t3,t4]
def t134 := 0x2820000c0c
def v208 := [t134,t0,t1,t2,t3,t4]
def t135 := 0x36ac084f830e3
def v209 := [t0,t1,t135,t2,t3,t4]
def t136 := 0xffefb03ffffe0
def v210 := [t0,t1,t2,t3,t122,t136]
def v211 := [t0,t110,t1,t2,t3,t122]
def t137 := 0xe400003f803e0
def v212 := [t0,t1,t2,t137,t4]
def v213 := [t0,t1,t2,t137,t3,t4]
def v214 := [t0,t1,t2,t137,t4,t122]
def t138 := 0xfffffc7fffff3
def v215 := [t0,t1,t2,t3,t4,t138]
def t139 := 0x803b00000c00
def v216 := [t0,t139,t1,t2,t3,t4]
def t140 := 0x13fc4c407f013
def v217 := [t0,t140,t1,t2,t4]
def v218 := [t0,t140,t1,t2,t3,t4]
def v219 := [t0,t140,t1,t2,t4,t122]
def t141 := 0x18996dee63fff
def v220 := [t0,t1,t141,t2,t3,t4]
def t142 := 0x188921ae63c0c
def v221 := [t0,t142,t1,t2,t3,t4]
def t143 := 0x10440000310
def v222 := [t143,t0,t1,t2,t3,t4]
def t144 := 0xc152ce707cfff
def v223 := [t0,t1,t144,t3,t4]
def v224 := [t112,t0,t1,t144,t3,t4]
def v225 := [t0,t1,t2,t144,t3,t4]
def t145 := 0xc14282307cc0c
def v226 := [t0,t1,t145,t3,t4]
def v227 := [t112,t0,t1,t145,t3,t4]
def v228 := [t0,t1,t145,t2,t3,t4]
def t146 := 0x3e0
def v229 := [t146,t0,t1,t2,t3,t4]
def t147 := 0xec13fc7f80ff3
def v230 := [t0,t1,t2,t3,t147,t4]
def t148 := 0xec03b03f80c00
def v231 := [t0,t1,t2,t148,t3,t4]
def v232 := [t112,t1,t2,t3,t121]
def v233 := [t112,t0,t1,t2,t3,t121]
def v234 := [t112,t1,t2,t3,t121,t4]
def v235 := [t112,t0,t123,t1,t2,t3]
def v236 := [t112,t0,t124,t1,t2,t3]
def v237 := [t112,t0,t1,t2,t3,t125]
def v238 := [t112,t0,t1,t59,t2,t3]
def v239 := [t112,t0,t1,t2,t109,t3]
def v240 := [t112,t0,t126,t1,t2,t3]
def v241 := [t0,t1,t2,t128,t3,t4]
def t149 := 0xe7744c519f3f3
def v242 := [t0,t1,t2,t149,t3,t4]
def t150 := 0x104c40033f3
def v243 := [t150,t0,t1,t2,t3,t4]
def v244 := [t0,t1,t2,t128,t3,t121]
def v245 := [t0,t1,t2,t3,t4,t127]
def v246 := [t0,t2,t128,t3,t4,t127]
def v247 := [t0,t123,t1,t2,t128,t3]
def v248 := [t0,t124,t2,t128,t3]
def v249 := [t0,t124,t1,t2,t128,t3]
def v250 := [t0,t124,t2,t128,t3,t4]
def t151 := 0xc14000101c000
def v251 := [t0,t1,t151,t2,t3,t4]
def t152 := 0xe776c631fcf1c
def v252 := [t0,t1,t2,t152,t3,t4]
def t153 := 0x12c62060f1c
def v253 := [t153,t0,t1,t2,t3,t4]
def v254 := [t0,t1,t2,t128,t3,t125]
def v255 := [t0,t1,t59,t2,t128,t3]
def t154 := 0xe400001180000
def v256 := [t0,t1,t2,t154,t3,t4]
def t155 := 0xef67b03f9cfe0
def v257 := [t0,t1,t2,t3,t155,t4]
def t156 := 0x803b02e00fe0
def v258 := [t0,t156,t1,t2,t3,t4]
def t157 := 0x36400001c000
def v259 := [t0,t157,t1,t2,t3,t4]
def v260 := [t0,t1,t2,t109,t128,t3]
def v261 := [t0,t126,t1,t2,t128,t3]
def v262 := [t0,t123,t1,t2,t3,t4]
def v263 := [t78,t0,t1,t2,t3,t4]
def v264 := [t0,t107,t1,t2,t3,t4]
def v265 := [t0,t1,t2,t3,t4,t23]
def v266 := [t0,t24,t1,t2,t3,t4]
def t158 := 0xe402901180360
def v267 := [t0,t1,t2,t158,t3,t4]
def v268 := [t0,t124,t1,t2,t3,t4]
def t159 := 0xc002803000f00
def v269 := [t0,t1,t159,t2,t3,t4]
def v270 := [t0,t1,t2,t3,t56,t4]
def v271 := [t0,t1,t50,t3,t56,t4]
def v272 := [t84,t0,t1,t2,t56,t4]
def t160 := 0x1044119c3f0
def v273 := [t160,t0,t1,t2,t3,t4]
def t161 := 0xed43b22e60c0c
def v274 := [t0,t1,t2,t3,t161,t4]
def v275 := [t78,t0,t1,t3,t56,t4]
def v276 := [t0,t79,t1,t3,t56,t4]
def v277 := [t0,t1,t2,t56,t4,t23]
def v278 := [t0,t1,t2,t158,t56,t4]
def t162 := 0x801202e60c9c
def v279 := [t0,t162,t1,t2,t3,t4]
def t163 := 0x1088018003003
def v280 := [t0,t163,t1,t2,t3,t4]
def t164 := 0xe552d6119c360
def v281 := [t0,t1,t2,t164,t3,t4]
def v282 := [t0,t1,t159,t56,t4]
def v283 := [t0,t1,t159,t2,t56,t4]
def v284 := [t0,t1,t159,t3,t56,t4]
def v285 := [t57,t0,t1,t2,t56,t4]
def v286 := [t0,t1,t108,t3,t56,t4]
def v287 := [t0,t1,t108,t2,t3,t4]
def v288 := [t0,t1,t3,t56,t4,t125]
def v289 := [t132,t0,t1,t3,t56,t4]
def v290 := [t57,t0,t1,t2,t3,t4]
def v291 := [t0,t1,t2,t56,t4,t136]
def v292 := [t0,t126,t1,t2,t56,t4]
def t165 := 0xe540003ffc000
def v293 := [t0,t1,t2,t165,t3]
def v294 := [t0,t1,t2,t165,t3,t56]
def v295 := [t0,t1,t2,t165,t3,t4]
def t166 := 0xfffff63fffffc
def v296 := [t0,t1,t2,t3,t4,t166]
def t167 := 0x813f60000ffc
def v297 := [t0,t167,t1,t2,t3]
def v298 := [t0,t167,t1,t2,t3,t56]
def v299 := [t0,t167,t1,t2,t3,t4]
def t168 := 0x12ac000003000
def v300 := [t0,t168,t1,t2,t3,t4]
def v301 := [t0,t1,t58,t2,t3,t4]
def v302 := [t0,t1,t2,t3,t4,t125]
def t169 := 0x23444119f310
def v303 := [t169,t0,t1,t2,t3,t4]
def t170 := 0xf5ca822e60c0c
def v304 := [t0,t1,t2,t3,t170,t4]
def v305 := [t0,t1,t2,t3,t125,t127]
def t171 := 0x1088002e63c1c
def v306 := [t0,t171,t1,t2,t3,t4]
def t172 := 0x801218000083
def v307 := [t0,t172,t1,t2,t3,t4]
def t173 := 0xe776c6119c300
def v308 := [t0,t1,t2,t173,t3,t4]
def v309 := [t57,t0,t1,t3,t4,t125]
def v310 := [t0,t1,t58,t3,t125]
def v311 := [t0,t1,t58,t2,t3,t125]
def v312 := [t0,t1,t58,t3,t4,t125]
def v313 := [t132,t0,t1,t2,t3,t125]
def v314 := [t0,t1,t59,t3,t4,t125]
def v315 := [t0,t1,t59,t2,t3,t4]
def v316 := [t0,t1,t2,t3,t125,t136]
def v317 := [t0,t110,t1,t2,t3,t125]
def t174 := 0xe402803f80f00
def v318 := [t0,t1,t2,t174,t3,t4]
def t175 := 0x8013000000e0
def v319 := [t0,t175,t1,t2,t3,t4]
def t176 := 0x13fc46007f01c
def v320 := [t0,t176,t1,t2,t3,t4]
def v321 := [t132,t0,t1,t2,t3,t4]
def v322 := [t0,t126,t1,t2,t3,t4]
def v323 := [t0,t110,t1,t2,t3,t4]
def t177 := 0x13fc4c51ff3f3
def v324 := [t0,t177,t1,t2,t3,t4]
def t178 := 0x104c51803f3
def v325 := [t178,t0,t1,t2,t3,t4]
def t179 := 0x11c8000060000
def v326 := [t0,t179,t1,t2,t3,t4]
def v327 := [t84,t0,t110,t1,t2,t4]
def v328 := [t0,t110,t1,t2,t3,t121]
def t180 := 0x1088000063000
def v329 := [t0,t180,t1,t2,t3,t4]
def t181 := 0x1bed21ae7fc9f
def v330 := [t0,t1,t181,t2,t3,t4]
def t182 := 0x80121ae00c9f
def v331 := [t0,t182,t1,t2,t3,t4]
def v332 := [t0,t110,t1,t2,t4,t23]
def v333 := [t0,t110,t1,t2,t158,t4]
def v334 := [t0,t123,t110,t1,t2,t3]
def v335 := [t0,t124,t110,t1,t2,t3]
def t183 := 0x14000007c000
def v336 := [t183,t0,t1,t2,t3,t4]
def t184 := 0xd3fec6307ff1c
def v337 := [t0,t1,t2,t184,t3,t4]
def t185 := 0xc012c63000f1c
def v338 := [t0,t1,t185,t2,t3,t4]
def v339 := [t0,t110,t1,t2,t4,t136]
def v340 := [t0,t1,t2,t3,t4,t136]
def v341 := [t0,t110,t1,t2,t109,t3]
def v342 := [t0,t1,t2,t109,t3,t4]
def v343 := [t0,t110,t1,t59,t2,t3]
def v344 := [t0,t126,t110,t1,t2]
def v345 := [t0,t126,t110,t1,t2,t3]
def v346 := [t0,t126,t110,t1,t2,t4]
theorem b0 : Ban 26 5 v2 := checkedSmall
theorem b1 : Ban 26 5 v3 := checkedSmall
theorem b2 : Ban 26 5 v4 := checkedSmall
theorem b3 : Ban 26 5 v5 := checkedSmall
theorem b133 : Ban 12 4 v127 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w0 : Wide 12 4 v127 := viaSub (ws := [v127]) (consBan b133 (nilBan 12 4)) (by decide) (by decide +kernel)
theorem b4 : Ban 26 5 v6 := smallByCut p31_27 w0
theorem b5 : Ban 26 5 v7 := checkedSmall
theorem b6 : Ban 26 5 v8 := checkedSmall
theorem b7 : Ban 26 5 v9 := checkedSmall
theorem b8 : Ban 26 5 v10 := checkedSmall
theorem b9 : Ban 26 5 v11 := smallByCut p31_27 w0
theorem b10 : Ban 26 5 v12 := checkedSmall
theorem b11 : Ban 26 5 v13 := smallByCut p31_27 w0
theorem b12 : Ban 26 5 v14 := smallByCut p31_23 w0
theorem b13 : Ban 26 5 v15 := checkedSmall
theorem b14 : Ban 26 5 v16 := checkedSmall
theorem b15 : Ban 26 5 v17 := checkedSmall
theorem b16 : Ban 26 5 v18 := checkedSmall
theorem b17 : Ban 26 5 v19 := smallByCut p31_23 w0
theorem b18 : Ban 26 5 v20 := checkedSmall
theorem b19 : Ban 26 5 v21 := smallByCut p31_23 w0
theorem b20 : Ban 26 5 v22 := checkedSmall
theorem b21 : Ban 26 5 v23 := checkedSmall
theorem b22 : Ban 26 5 v24 := checkedSmall
theorem b23 : Ban 26 5 v25 := checkedSmall
theorem b24 : Ban 26 5 v26 := checkedSmall
theorem b25 : Ban 26 5 v27 := checkedSmall
theorem b26 : Ban 26 5 v28 := checkedSmall
theorem b27 : Ban 26 5 v29 := checkedSmall
theorem b28 : Ban 26 5 v30 := checkedSmall
theorem b29 : Ban 26 5 v31 := checkedSmall
theorem b30 : Ban 26 5 v32 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b31 : Ban 26 6 v1 := viaBranch (ws := [v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32]) (consBan b0 (consBan b1 (consBan b2 (consBan b3 (consBan b4 (consBan b5 (consBan b6 (consBan b7 (consBan b8 (consBan b9 (consBan b10 (consBan b11 (consBan b12 (consBan b13 (consBan b14 (consBan b15 (consBan b16 (consBan b17 (consBan b18 (consBan b19 (consBan b20 (consBan b21 (consBan b22 (consBan b23 (consBan b24 (consBan b25 (consBan b26 (consBan b27 (consBan b28 (consBan b29 (consBan b30 (nilBan 26 5)))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b32 : Ban 26 5 v34 := checkedSmall
theorem b33 : Ban 26 5 v35 := checkedSmall
theorem b34 : Ban 26 5 v36 := checkedSmall
theorem b35 : Ban 26 5 v37 := checkedSmall
theorem b36 : Ban 26 5 v38 := checkedSmall
theorem b37 : Ban 26 5 v39 := checkedSmall
theorem b38 : Ban 26 5 v40 := smallByCut p31_27 w0
theorem b39 : Ban 26 5 v41 := checkedSmall
theorem b40 : Ban 26 5 v42 := smallByCut p31_27 w0
theorem b41 : Ban 26 5 v43 := checkedSmall
theorem b42 : Ban 26 5 v44 := checkedSmall
theorem b43 : Ban 26 5 v45 := checkedSmall
theorem b44 : Ban 26 5 v46 := checkedSmall
theorem b45 : Ban 26 5 v47 := smallByCut p31_27 w0
theorem b46 : Ban 26 5 v48 := smallByCut p31_23 w0
theorem b47 : Ban 26 5 v49 := checkedSmall
theorem b48 : Ban 26 5 v50 := smallByCut p31_23 w0
theorem b49 : Ban 26 5 v51 := checkedSmall
theorem b50 : Ban 26 5 v52 := checkedSmall
theorem b51 : Ban 26 5 v53 := checkedSmall
theorem b52 : Ban 26 5 v54 := checkedSmall
theorem b53 : Ban 26 5 v55 := smallByCut p31_23 w0
theorem b54 : Ban 26 5 v56 := checkedSmall
theorem b55 : Ban 26 5 v57 := checkedSmall
theorem b56 : Ban 26 5 v58 := checkedSmall
theorem b57 : Ban 26 5 v59 := checkedSmall
theorem b58 : Ban 26 5 v60 := checkedSmall
theorem b59 : Ban 26 5 v61 := checkedSmall
theorem b60 : Ban 26 5 v62 := checkedSmall
theorem b61 : Ban 26 5 v63 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b62 : Ban 26 6 v33 := viaBranch (ws := [v30,v31,v32,v34,v35,v5,v36,v37,v3,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51,v52,v53,v54,v55,v56,v57,v58,v59,v60,v61,v62,v63]) (consBan b28 (consBan b29 (consBan b30 (consBan b32 (consBan b33 (consBan b3 (consBan b34 (consBan b35 (consBan b1 (consBan b36 (consBan b37 (consBan b38 (consBan b39 (consBan b40 (consBan b41 (consBan b42 (consBan b43 (consBan b44 (consBan b45 (consBan b46 (consBan b47 (consBan b48 (consBan b49 (consBan b50 (consBan b51 (consBan b52 (consBan b53 (consBan b54 (consBan b55 (consBan b56 (consBan b57 (consBan b58 (consBan b59 (consBan b60 (consBan b61 (nilBan 26 5)))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b63 : Ban 26 5 v1 := checkedSmall
theorem b64 : Ban 26 5 v33 := checkedSmall
theorem b65 : Ban 26 5 v64 := smallByCut p31_27 w0
theorem b66 : Ban 26 5 v65 := checkedSmall
theorem b67 : Ban 26 5 v66 := checkedSmall
theorem b68 : Ban 26 5 v67 := smallByCut p31_27 w0
theorem b69 : Ban 26 5 v68 := smallByCut p31_23 w0
theorem b70 : Ban 26 5 v69 := checkedSmall
theorem b71 : Ban 26 5 v70 := checkedSmall
theorem b72 : Ban 26 5 v71 := smallByCut p31_23 w0
theorem b73 : Ban 26 5 v72 := checkedSmall
theorem b74 : Ban 26 5 v73 := checkedSmall
theorem b75 : Ban 26 5 v74 := checkedSmall
theorem b76 : Ban 26 5 v75 := checkedSmall
theorem b77 : Ban 26 5 v76 := checkedSmall
theorem b78 : Ban 26 5 v77 := checkedSmall
theorem b79 : Ban 26 5 v78 := checkedSmall
theorem b80 : Ban 26 5 v79 := checkedSmall
theorem b81 : Ban 26 5 v80 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b82 : Ban 26 6 v3 := viaBranch (ws := [v2,v1,v34,v33,v64,v65,v66,v67,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77,v78,v79,v80]) (consBan b0 (consBan b63 (consBan b32 (consBan b64 (consBan b65 (consBan b66 (consBan b67 (consBan b68 (consBan b69 (consBan b70 (consBan b71 (consBan b72 (consBan b73 (consBan b74 (consBan b75 (consBan b76 (consBan b77 (consBan b78 (consBan b79 (consBan b80 (consBan b81 (nilBan 26 5)))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b83 : Ban 26 6 v5 := viaPerm map31_1 map31_1 b82 (by decide +kernel) (by decide +kernel)
theorem b84 : Ban 26 6 v81 := smallByCut p31_27 w0
theorem b85 : Ban 26 5 v83 := smallByCut p31_27 w0
theorem b86 : Ban 26 5 v84 := smallByCut p31_27 w0
theorem b87 : Ban 26 5 v85 := smallByCut p31_27 w0
theorem b88 : Ban 26 5 v86 := checkedSmall
theorem b89 : Ban 26 5 v87 := smallByCut p31_27 w0
theorem b90 : Ban 26 5 v88 := smallByCut p31_27 w0
theorem b91 : Ban 26 5 v89 := checkedSmall
theorem b92 : Ban 26 5 v90 := smallByCut p31_27 w0
theorem b93 : Ban 26 5 v91 := checkedSmall
theorem b94 : Ban 26 5 v92 := checkedSmall
theorem b95 : Ban 26 5 v93 := checkedSmall
theorem b96 : Ban 26 5 v94 := smallByCut p31_27 w0
theorem b97 : Ban 26 5 v95 := checkedSmall
theorem b98 : Ban 26 5 v96 := smallByCut p31_27 w0
theorem b99 : Ban 26 5 v97 := smallByCut p31_27 w0
theorem b100 : Ban 26 5 v98 := checkedSmall
theorem b101 : Ban 26 5 v99 := smallByCut p31_23 w0
theorem b102 : Ban 26 5 v100 := checkedSmall
theorem b103 : Ban 26 5 v101 := checkedSmall
theorem b104 : Ban 26 5 v102 := smallByCut p31_23 w0
theorem b105 : Ban 26 5 v103 := checkedSmall
theorem b106 : Ban 26 5 v104 := checkedSmall
theorem b107 : Ban 26 5 v105 := checkedSmall
theorem b108 : Ban 26 5 v106 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b109 : Ban 26 6 v82 := viaBranch (ws := [v36,v79,v83,v84,v85,v86,v87,v88,v89,v90,v91,v43,v92,v93,v94,v95,v96,v97,v98,v99,v100,v101,v102,v103,v104,v105,v106]) (consBan b34 (consBan b80 (consBan b85 (consBan b86 (consBan b87 (consBan b88 (consBan b89 (consBan b90 (consBan b91 (consBan b92 (consBan b93 (consBan b41 (consBan b94 (consBan b95 (consBan b96 (consBan b97 (consBan b98 (consBan b99 (consBan b100 (consBan b101 (consBan b102 (consBan b103 (consBan b104 (consBan b105 (consBan b106 (consBan b107 (consBan b108 (nilBan 26 5)))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b110 : Ban 26 5 v107 := smallByCut p31_27 w0
theorem b111 : Ban 26 5 v81 := smallByCut p31_27 w0
theorem b112 : Ban 26 5 v108 := checkedSmall
theorem b113 : Ban 26 5 v109 := checkedSmall
theorem b114 : Ban 26 5 v82 := smallByCut p31_27 w0
theorem b115 : Ban 26 5 v110 := smallByCut p31_23 w0
theorem b116 : Ban 26 5 v111 := checkedSmall
theorem b117 : Ban 26 5 v112 := checkedSmall
theorem b118 : Ban 26 5 v113 := smallByCut p31_23 w0
theorem b119 : Ban 26 5 v114 := checkedSmall
theorem b120 : Ban 26 5 v115 := checkedSmall
theorem b121 : Ban 26 5 v116 := checkedSmall
theorem b122 : Ban 26 5 v117 := checkedSmall
theorem b123 : Ban 26 5 v118 := checkedSmall
theorem b124 : Ban 26 5 v119 := checkedSmall
theorem b125 : Ban 26 5 v120 := checkedSmall
theorem b126 : Ban 26 5 v121 := checkedSmall
theorem b127 : Ban 26 5 v122 := smallByCut p31_27 w0
theorem b128 : Ban 26 5 v123 := smallByCut p31_27 w0
theorem b129 : Ban 26 5 v124 := smallByCut p31_27 w0
theorem b130 : Ban 26 5 v125 := smallByCut p31_27 w0
theorem b131 : Ban 26 5 v126 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b132 : Ban 26 6 v94 := viaBranch (ws := [v107,v81,v10,v108,v66,v109,v86,v82,v110,v111,v112,v113,v114,v115,v116,v117,v118,v119,v120,v121,v37,v80,v122,v123,v124,v125,v126]) (consBan b110 (consBan b111 (consBan b8 (consBan b112 (consBan b67 (consBan b113 (consBan b88 (consBan b114 (consBan b115 (consBan b116 (consBan b117 (consBan b118 (consBan b119 (consBan b120 (consBan b121 (consBan b122 (consBan b123 (consBan b124 (consBan b125 (consBan b126 (consBan b35 (consBan b81 (consBan b127 (consBan b128 (consBan b129 (consBan b130 (consBan b131 (nilBan 26 5)))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b134 : Ban 26 6 v88 := smallByCut p31_27 w0
theorem b135 : Ban 26 6 v128 := smallByCut p31_23 w0
theorem b136 : Ban 26 5 v131 := smallByCut p31_27 w0
theorem b137 : Ban 26 5 v132 := checkedSmall
theorem b138 : Ban 26 5 v133 := checkedSmall
theorem b139 : Ban 26 5 v134 := smallByCut p31_27 w0
theorem b140 : Ban 26 5 v135 := smallByCut p31_27 w0
theorem b141 : Ban 26 5 v136 := smallByCut p31_27 w0
theorem b142 : Ban 26 5 v137 := checkedSmall
theorem b143 : Ban 26 5 v138 := smallByCut p31_27 w0
theorem b144 : Ban 26 5 v139 := smallByCut p31_27 w0
theorem b145 : Ban 26 5 v140 := smallByCut p31_27 w0
theorem b146 : Ban 26 5 v141 := smallByCut p31_23 w0
theorem b147 : Ban 26 5 v142 := checkedSmall
theorem b148 : Ban 26 5 v143 := checkedSmall
theorem b149 : Ban 26 5 v144 := smallByCut p31_23 w0
theorem b150 : Ban 26 5 v145 := checkedSmall
theorem b151 : Ban 26 5 v146 := checkedSmall
theorem b152 : Ban 26 5 v147 := checkedSmall
theorem b153 : Ban 26 5 v148 := checkedSmall
theorem b154 : Ban 26 5 v149 := checkedSmall
theorem b155 : Ban 26 5 v150 := checkedSmall
theorem b156 : Ban 26 5 v151 := checkedSmall
theorem b157 : Ban 26 5 v152 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b158 : Ban 26 6 v130 := viaBranch (ws := [v89,v131,v132,v43,v66,v133,v134,v135,v136,v137,v138,v139,v140,v141,v142,v143,v144,v145,v146,v147,v148,v149,v150,v151,v152]) (consBan b91 (consBan b136 (consBan b137 (consBan b41 (consBan b67 (consBan b138 (consBan b139 (consBan b140 (consBan b141 (consBan b142 (consBan b143 (consBan b144 (consBan b145 (consBan b146 (consBan b147 (consBan b148 (consBan b149 (consBan b150 (consBan b151 (consBan b152 (consBan b153 (consBan b154 (consBan b155 (consBan b156 (consBan b157 (nilBan 26 5)))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b159 : Ban 26 6 v129 := viaPerm map31_1 map31_1 b158 (by decide +kernel) (by decide +kernel)
theorem b160 : Ban 26 5 v154 := smallByCut p31_23 w0
theorem b161 : Ban 26 5 v128 := smallByCut p31_23 w0
theorem b162 : Ban 26 5 v155 := checkedSmall
theorem b163 : Ban 26 5 v156 := checkedSmall
theorem b164 : Ban 26 5 v157 := smallByCut p31_27 w0
theorem b165 : Ban 26 5 v158 := checkedSmall
theorem b166 : Ban 26 5 v159 := smallByCut p31_27 w0
theorem b167 : Ban 26 5 v160 := checkedSmall
theorem b168 : Ban 26 5 v129 := smallByCut p31_23 w0
theorem b169 : Ban 26 5 v161 := checkedSmall
theorem b170 : Ban 26 5 v162 := checkedSmall
theorem b171 : Ban 26 5 v163 := checkedSmall
theorem b172 : Ban 26 5 v164 := checkedSmall
theorem b173 : Ban 26 5 v165 := smallByCut p31_23 w0
theorem b174 : Ban 26 5 v166 := smallByCut p31_23 w0
theorem b175 : Ban 26 5 v167 := smallByCut p31_23 w0
theorem b176 : Ban 26 5 v168 := smallByCut p31_23 w0
theorem b177 : Ban 26 5 v169 := checkedSmall
theorem b178 : Ban 26 5 v170 := checkedSmall
theorem b179 : Ban 26 5 v171 := smallByCut p31_23 w0
theorem b180 : Ban 26 5 v172 := smallByCut p31_23 w0
theorem b181 : Ban 26 5 v173 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b182 : Ban 26 6 v153 := viaBranch (ws := [v154,v128,v18,v155,v70,v156,v157,v158,v112,v159,v160,v129,v161,v162,v163,v164,v165,v166,v167,v168,v169,v170,v171,v172,v173]) (consBan b160 (consBan b161 (consBan b16 (consBan b162 (consBan b71 (consBan b163 (consBan b164 (consBan b165 (consBan b117 (consBan b166 (consBan b167 (consBan b168 (consBan b169 (consBan b170 (consBan b171 (consBan b172 (consBan b173 (consBan b174 (consBan b175 (consBan b176 (consBan b177 (consBan b178 (consBan b179 (consBan b180 (consBan b181 (nilBan 26 5)))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b183 : Ban 26 6 v174 := smallByCut p31_23 w0
theorem b184 : Ban 26 5 v176 := checkedSmall
theorem b185 : Ban 26 5 v177 := checkedSmall
theorem b186 : Ban 26 5 v178 := checkedSmall
theorem b187 : Ban 26 5 v179 := checkedSmall
theorem b188 : Ban 26 5 v180 := smallByCut p31_27 w0
theorem b189 : Ban 26 5 v181 := checkedSmall
theorem b190 : Ban 26 5 v182 := smallByCut p31_27 w0
theorem b191 : Ban 26 5 v183 := smallByCut p31_23 w0
theorem b192 : Ban 26 5 v184 := checkedSmall
theorem b193 : Ban 26 5 v185 := smallByCut p31_23 w0
theorem b194 : Ban 26 5 v186 := checkedSmall
theorem b195 : Ban 26 5 v187 := checkedSmall
theorem b196 : Ban 26 5 v188 := checkedSmall
theorem b197 : Ban 26 5 v189 := checkedSmall
theorem b198 : Ban 26 5 v190 := checkedSmall
theorem b199 : Ban 26 5 v191 := checkedSmall
theorem b200 : Ban 26 5 v192 := checkedSmall
theorem b201 : Ban 26 5 v193 := checkedSmall
theorem b202 : Ban 26 5 v194 := checkedSmall
theorem b203 : Ban 26 5 v195 := checkedSmall
theorem b204 : Ban 26 5 v196 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b205 : Ban 26 6 v175 := viaBranch (ws := [v176,v177,v22,v178,v72,v179,v180,v181,v114,v182,v183,v184,v161,v185,v186,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196]) (consBan b184 (consBan b185 (consBan b20 (consBan b186 (consBan b73 (consBan b187 (consBan b188 (consBan b189 (consBan b119 (consBan b190 (consBan b191 (consBan b192 (consBan b169 (consBan b193 (consBan b194 (consBan b195 (consBan b196 (consBan b197 (consBan b198 (consBan b199 (consBan b200 (consBan b201 (consBan b202 (consBan b203 (consBan b204 (nilBan 26 5)))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b206 : Ban 26 5 v198 := checkedSmall
theorem b207 : Ban 26 5 v199 := checkedSmall
theorem b208 : Ban 26 5 v200 := checkedSmall
theorem b209 : Ban 26 5 v201 := checkedSmall
theorem b210 : Ban 26 5 v202 := checkedSmall
theorem b211 : Ban 26 5 v203 := checkedSmall
theorem b212 : Ban 26 5 v204 := checkedSmall
theorem b213 : Ban 26 5 v205 := checkedSmall
theorem b214 : Ban 26 5 v206 := checkedSmall
theorem b215 : Ban 26 5 v207 := smallByCut p31_27 w0
theorem b216 : Ban 26 5 v208 := smallByCut p31_27 w0
theorem b217 : Ban 26 5 v209 := checkedSmall
theorem b218 : Ban 26 5 v210 := checkedSmall
theorem b219 : Ban 26 5 v211 := checkedSmall
theorem b220 : Ban 26 5 v212 := smallByCut p31_23 w0
theorem b221 : Ban 26 5 v213 := smallByCut p31_23 w0
theorem b222 : Ban 26 5 v214 := checkedSmall
theorem b223 : Ban 26 5 v215 := checkedSmall
theorem b224 : Ban 26 5 v216 := smallByCut p31_23 w0
theorem b225 : Ban 26 5 v217 := checkedSmall
theorem b226 : Ban 26 5 v218 := checkedSmall
theorem b227 : Ban 26 5 v219 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b228 : Ban 26 6 v197 := viaBranch (ws := [v188,v189,v190,v198,v199,v187,v200,v201,v202,v59,v203,v204,v205,v206,v207,v104,v208,v209,v210,v211,v212,v213,v214,v215,v216,v217,v218,v219,v177]) (consBan b196 (consBan b197 (consBan b198 (consBan b206 (consBan b207 (consBan b195 (consBan b208 (consBan b209 (consBan b210 (consBan b57 (consBan b211 (consBan b212 (consBan b213 (consBan b214 (consBan b215 (consBan b106 (consBan b216 (consBan b217 (consBan b218 (consBan b219 (consBan b220 (consBan b221 (consBan b222 (consBan b223 (consBan b224 (consBan b225 (consBan b226 (consBan b227 (consBan b185 (nilBan 26 5)))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b229 : Ban 26 5 v175 := checkedSmall
theorem b230 : Ban 26 5 v220 := checkedSmall
theorem b231 : Ban 26 5 v221 := checkedSmall
theorem b232 : Ban 26 5 v222 := smallByCut p31_27 w0
theorem b233 : Ban 26 5 v223 := checkedSmall
theorem b234 : Ban 26 5 v224 := checkedSmall
theorem b235 : Ban 26 5 v225 := checkedSmall
theorem b236 : Ban 26 5 v226 := smallByCut p31_27 w0
theorem b237 : Ban 26 5 v227 := checkedSmall
theorem b238 : Ban 26 5 v228 := smallByCut p31_27 w0
theorem b239 : Ban 26 5 v229 := smallByCut p31_23 w0
theorem b240 : Ban 26 5 v230 := checkedSmall
theorem b241 : Ban 26 5 v231 := smallByCut p31_23 w0
theorem b242 : Ban 26 5 v197 := checkedSmall
theorem b243 : Ban 26 5 v232 := checkedSmall
theorem b244 : Ban 26 5 v233 := checkedSmall
theorem b245 : Ban 26 5 v234 := checkedSmall
theorem b246 : Ban 26 5 v235 := checkedSmall
theorem b247 : Ban 26 5 v236 := checkedSmall
theorem b248 : Ban 26 5 v237 := checkedSmall
theorem b249 : Ban 26 5 v238 := checkedSmall
theorem b250 : Ban 26 5 v239 := checkedSmall
theorem b251 : Ban 26 5 v240 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b252 : Ban 26 6 v177 := viaBranch (ws := [v176,v175,v26,v220,v74,v221,v222,v223,v224,v225,v118,v226,v227,v228,v229,v230,v163,v231,v198,v197,v232,v233,v234,v235,v236,v237,v238,v239,v240]) (consBan b184 (consBan b229 (consBan b24 (consBan b230 (consBan b75 (consBan b231 (consBan b232 (consBan b233 (consBan b234 (consBan b235 (consBan b123 (consBan b236 (consBan b237 (consBan b238 (consBan b239 (consBan b240 (consBan b171 (consBan b241 (consBan b206 (consBan b242 (consBan b243 (consBan b244 (consBan b245 (consBan b246 (consBan b247 (consBan b248 (consBan b249 (consBan b250 (consBan b251 (nilBan 26 5)))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b253 : Ban 26 5 v242 := checkedSmall
theorem b254 : Ban 26 5 v243 := checkedSmall
theorem b255 : Ban 26 5 v244 := checkedSmall
theorem b256 : Ban 26 5 v245 := checkedSmall
theorem b257 : Ban 26 5 v246 := checkedSmall
theorem b258 : Ban 26 5 v247 := checkedSmall
theorem b259 : Ban 26 5 v248 := checkedSmall
theorem b260 : Ban 26 5 v249 := checkedSmall
theorem b261 : Ban 26 5 v250 := checkedSmall
theorem b262 : Ban 26 5 v251 := smallByCut p31_27 w0
theorem b263 : Ban 26 5 v252 := checkedSmall
theorem b264 : Ban 26 5 v253 := smallByCut p31_27 w0
theorem b265 : Ban 26 5 v254 := checkedSmall
theorem b266 : Ban 26 5 v255 := checkedSmall
theorem b267 : Ban 26 5 v256 := smallByCut p31_23 w0
theorem b268 : Ban 26 5 v257 := checkedSmall
theorem b269 : Ban 26 5 v258 := smallByCut p31_23 w0
theorem b270 : Ban 26 5 v259 := checkedSmall
theorem b271 : Ban 26 5 v260 := checkedSmall
theorem b272 : Ban 26 5 v261 := checkedSmall
theorem b273 : Ban 26 5 v262 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b274 : Ban 26 6 v241 := viaBranch (ws := [v72,v242,v243,v63,v201,v244,v245,v246,v247,v248,v249,v250,v251,v252,v253,v152,v254,v255,v256,v257,v258,v259,v260,v261,v262]) (consBan b73 (consBan b253 (consBan b254 (consBan b61 (consBan b209 (consBan b255 (consBan b256 (consBan b257 (consBan b258 (consBan b259 (consBan b260 (consBan b261 (consBan b262 (consBan b263 (consBan b264 (consBan b157 (consBan b265 (consBan b266 (consBan b267 (consBan b268 (consBan b269 (consBan b270 (consBan b271 (consBan b272 (consBan b273 (nilBan 26 5)))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b275 : Ban 26 6 v187 := viaPerm map31_1 map31_1 b274 (by decide +kernel) (by decide +kernel)
theorem b276 : Ban 26 6 v263 := smallByCut p31_27 w0
theorem b277 : Ban 26 6 v140 := viaPerm map31_1 map31_1 b182 (by decide +kernel) (by decide +kernel)
theorem b278 : Ban 26 6 v139 := smallByCut p31_27 w0
theorem b279 : Ban 26 6 v264 := smallByCut p31_23 w0
theorem b280 : Ban 26 6 v265 := viaPerm map31_1 map31_1 b109 (by decide +kernel) (by decide +kernel)
theorem b281 : Ban 26 6 v266 := viaPerm map31_1 map31_1 b132 (by decide +kernel) (by decide +kernel)
theorem b282 : Ban 26 6 v267 := smallByCut p31_23 w0
theorem b283 : Ban 26 6 v262 := viaPerm map31_1 map31_1 b205 (by decide +kernel) (by decide +kernel)
theorem b284 : Ban 26 6 v245 := viaPerm map31_1 map31_1 b228 (by decide +kernel) (by decide +kernel)
theorem b285 : Ban 26 6 v268 := viaPerm map31_1 map31_1 b252 (by decide +kernel) (by decide +kernel)
theorem b286 : Ban 26 6 v269 := smallByCut p31_23 w0
theorem b287 : Ban 26 5 v271 := smallByCut p31_27 w0
theorem b288 : Ban 26 5 v272 := smallByCut p31_23 w0
theorem b289 : Ban 26 5 v273 := checkedSmall
theorem b290 : Ban 26 5 v274 := checkedSmall
theorem b291 : Ban 26 5 v275 := smallByCut p31_27 w0
theorem b292 : Ban 26 5 v276 := checkedSmall
theorem b293 : Ban 26 5 v277 := checkedSmall
theorem b294 : Ban 26 5 v278 := smallByCut p31_23 w0
theorem b295 : Ban 26 5 v279 := checkedSmall
theorem b296 : Ban 26 5 v280 := checkedSmall
theorem b297 : Ban 26 5 v281 := checkedSmall
theorem b298 : Ban 26 5 v282 := smallByCut p31_23 w0
theorem b299 : Ban 26 5 v283 := smallByCut p31_23 w0
theorem b300 : Ban 26 5 v284 := smallByCut p31_23 w0
theorem b301 : Ban 26 5 v285 := smallByCut p31_27 w0
theorem b302 : Ban 26 5 v286 := smallByCut p31_23 w0
theorem b303 : Ban 26 5 v287 := smallByCut p31_23 w0
theorem b304 : Ban 26 5 v288 := checkedSmall
theorem b305 : Ban 26 5 v289 := smallByCut p31_27 w0
theorem b306 : Ban 26 5 v290 := smallByCut p31_23 w0
theorem b307 : Ban 26 5 v291 := checkedSmall
theorem b308 : Ban 26 5 v292 := smallByCut p31_23 w0
theorem b309 : Ban 26 5 v293 := checkedSmall
theorem b310 : Ban 26 5 v294 := checkedSmall
theorem b311 : Ban 26 5 v295 := checkedSmall
theorem b312 : Ban 26 5 v296 := checkedSmall
theorem b313 : Ban 26 5 v297 := checkedSmall
theorem b314 : Ban 26 5 v298 := checkedSmall
theorem b315 : Ban 26 5 v299 := checkedSmall
theorem b316 : Ban 26 5 v300 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b317 : Ban 26 6 v270 := viaBranch (ws := [v95,v271,v272,v170,v273,v100,v112,v274,v275,v276,v277,v278,v279,v142,v280,v281,v282,v283,v284,v285,v286,v287,v288,v289,v290,v291,v292,v293,v294,v295,v296,v297,v298,v299,v300]) (consBan b97 (consBan b287 (consBan b288 (consBan b178 (consBan b289 (consBan b102 (consBan b117 (consBan b290 (consBan b291 (consBan b292 (consBan b293 (consBan b294 (consBan b295 (consBan b147 (consBan b296 (consBan b297 (consBan b298 (consBan b299 (consBan b300 (consBan b301 (consBan b302 (consBan b303 (consBan b304 (consBan b305 (consBan b306 (consBan b307 (consBan b308 (consBan b309 (consBan b310 (consBan b311 (consBan b312 (consBan b313 (consBan b314 (consBan b315 (consBan b316 (nilBan 26 5)))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b318 : Ban 26 6 v290 := smallByCut p31_27 w0
theorem b319 : Ban 26 6 v287 := smallByCut p31_23 w0
theorem b320 : Ban 26 6 v301 := smallByCut p31_27 w0
theorem b321 : Ban 26 5 v303 := checkedSmall
theorem b322 : Ban 26 5 v304 := checkedSmall
theorem b323 : Ban 26 5 v305 := checkedSmall
theorem b324 : Ban 26 5 v306 := checkedSmall
theorem b325 : Ban 26 5 v307 := checkedSmall
theorem b326 : Ban 26 5 v308 := checkedSmall
theorem b327 : Ban 26 5 v309 := smallByCut p31_27 w0
theorem b328 : Ban 26 5 v310 := smallByCut p31_27 w0
theorem b329 : Ban 26 5 v311 := smallByCut p31_27 w0
theorem b330 : Ban 26 5 v312 := smallByCut p31_27 w0
theorem b331 : Ban 26 5 v313 := smallByCut p31_27 w0
theorem b332 : Ban 26 5 v314 := checkedSmall
theorem b333 : Ban 26 5 v315 := smallByCut p31_27 w0
theorem b334 : Ban 26 5 v316 := checkedSmall
theorem b335 : Ban 26 5 v317 := checkedSmall
theorem b336 : Ban 26 5 v318 := smallByCut p31_23 w0
theorem b337 : Ban 26 5 v319 := smallByCut p31_23 w0
theorem b338 : Ban 26 5 v320 := checkedSmall
theorem b339 : Ban 26 5 v321 := smallByCut p31_27 w0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b340 : Ban 26 6 v302 := viaBranch (ws := [v193,v237,v303,v104,v118,v304,v305,v254,v306,v148,v307,v308,v288,v309,v310,v311,v312,v313,v314,v315,v316,v317,v318,v296,v319,v320,v321]) (consBan b201 (consBan b248 (consBan b321 (consBan b106 (consBan b123 (consBan b322 (consBan b323 (consBan b265 (consBan b324 (consBan b153 (consBan b325 (consBan b326 (consBan b304 (consBan b327 (consBan b328 (consBan b329 (consBan b330 (consBan b331 (consBan b332 (consBan b333 (consBan b334 (consBan b335 (consBan b336 (consBan b312 (consBan b337 (consBan b338 (consBan b339 (nilBan 26 5)))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b342 : Ban 26 6 v321 := smallByCut p31_27 w0
theorem b343 : Ban 26 5 v324 := checkedSmall
theorem b344 : Ban 26 5 v325 := checkedSmall
theorem b345 : Ban 26 5 v326 := checkedSmall
theorem b346 : Ban 26 5 v327 := smallByCut p31_23 w0
theorem b347 : Ban 26 5 v328 := checkedSmall
theorem b348 : Ban 26 5 v329 := checkedSmall
theorem b349 : Ban 26 5 v330 := checkedSmall
theorem b350 : Ban 26 5 v331 := checkedSmall
theorem b351 : Ban 26 5 v332 := checkedSmall
theorem b352 : Ban 26 5 v333 := smallByCut p31_23 w0
theorem b353 : Ban 26 5 v334 := checkedSmall
theorem b354 : Ban 26 5 v335 := checkedSmall
theorem b355 : Ban 26 5 v336 := smallByCut p31_27 w0
theorem b356 : Ban 26 5 v337 := checkedSmall
theorem b357 : Ban 26 5 v338 := smallByCut p31_27 w0
theorem b358 : Ban 26 5 v339 := checkedSmall
theorem b359 : Ban 26 5 v340 := smallByCut p31_23 w0
theorem b360 : Ban 26 5 v341 := smallByCut p31_23 w0
theorem b361 : Ban 26 5 v342 := smallByCut p31_23 w0
theorem b362 : Ban 26 5 v343 := checkedSmall
theorem b363 : Ban 26 5 v344 := smallByCut p31_23 w0
theorem b364 : Ban 26 5 v345 := smallByCut p31_23 w0
theorem b365 : Ban 26 5 v346 := smallByCut p31_23 w0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b366 : Ban 26 6 v323 := viaBranch (ws := [v161,v324,v325,v326,v327,v173,v211,v328,v329,v330,v331,v259,v332,v333,v334,v335,v336,v337,v300,v338,v339,v340,v341,v342,v317,v343,v344,v345,v346]) (consBan b169 (consBan b343 (consBan b344 (consBan b345 (consBan b346 (consBan b181 (consBan b219 (consBan b347 (consBan b348 (consBan b349 (consBan b350 (consBan b270 (consBan b351 (consBan b352 (consBan b353 (consBan b354 (consBan b355 (consBan b356 (consBan b316 (consBan b357 (consBan b358 (consBan b359 (consBan b360 (consBan b361 (consBan b335 (consBan b362 (consBan b363 (consBan b364 (consBan b365 (nilBan 26 5)))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b367 : Ban 26 6 v315 := viaPerm map31_1 map31_1 b366 (by decide +kernel) (by decide +kernel)
theorem b368 : Ban 26 6 v342 := smallByCut p31_23 w0
theorem b369 : Ban 26 6 v340 := viaPerm map31_1 map31_1 b340 (by decide +kernel) (by decide +kernel)
theorem b341 : Ban 26 6 v322 := smallByCut p31_23 w0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b370 : Ban 26 7 v0 := viaBranch (ws := [v1,v33,v3,v5,v81,v82,v94,v88,v128,v129,v153,v174,v175,v197,v177,v187,v263,v130,v140,v139,v264,v265,v266,v267,v262,v245,v268,v241,v269,v270,v290,v287,v301,v302,v321,v315,v342,v340,v322,v323]) (consBan b31 (consBan b62 (consBan b82 (consBan b83 (consBan b84 (consBan b109 (consBan b132 (consBan b134 (consBan b135 (consBan b159 (consBan b182 (consBan b183 (consBan b205 (consBan b228 (consBan b252 (consBan b275 (consBan b276 (consBan b158 (consBan b277 (consBan b278 (consBan b279 (consBan b280 (consBan b281 (consBan b282 (consBan b283 (consBan b284 (consBan b285 (consBan b274 (consBan b286 (consBan b317 (consBan b318 (consBan b319 (consBan b320 (consBan b340 (consBan b342 (consBan b367 (consBan b368 (consBan b369 (consBan b341 (consBan b366 (nilBan 26 6))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem verifiedPin : Wide 26 7 v0 := widen (by decide +kernel) b370
end PEqualNP.Outside.L_meta_16501.Support.Core0

namespace PEqualNP.Outside.L_meta_16501.Support.Core1
theorem smallByCut {m h f t : Nat} {v w : List Nat} (p : Projection m h) (bound : Wide h t w)
    (nd : v.Nodup := by decide) (mem : ∀ a∈v, p.toFun a=0 ∨ p.toFun a∈w := by decide +kernel)
    (cost : f≤t+(v.map p.toFun).count 0 := by decide +kernel) : Ban m f v :=
  viaCut p bound nd mem cost

theorem solid {m f : Nat} {v : List Nat} (bound : Ban m f v)
    (ess : ∀ a∈v, ∃ i : Fin m, ∀ b∈v, b.testBit i.val≠b.testBit (m+i.val) → b=a := by decide +kernel) :
    Wide m f v := widen ess bound

theorem bySubset {m f t : Nat} {v w : List Nat} (bound : Wide m t w)
    (sub : ∀ a∈v, a∈w := by decide +kernel) (le : f≤t := by decide) : Ban m f v := by
  intro j h hb
  exact bound ⟨j,v.toFinset,h.trans le,hb,fun x hx => sub x (List.mem_toFinset.mp hx)⟩

theorem checkedSmall {m f : Nat} {v : List Nat} (ex : search m f v = false := by decide +kernel)
    (nd : v.Nodup := by decide) : Ban m f v := viaSmall ex nd

def t0 := 0x104544f3cf
def t1 := 0x194512bb4d33
def t2 := 0xc28a28c38e3c
def t3 := 0xec0f80fc0fc0
def t4 := 0xf7e000fff000
def v0 := [t0,t1,t2,t3,t4]
def t5 := 0x4103
def v1 := [t5,t0,t1,t2,t3,t4]
def t6 := 0x251ff
def t7 := 0x692e93
def t8 := 0xb18f1c
def t9 := 0xdc0fe0
def v2 := [t6,t7,t8,t9]
def t10 := 0x93
def v3 := [t10,t6,t7,t8,t9]
def t11 := 0x6b7fff
def v4 := [t6,t7,t11,t8,t9]
def t12 := 0x2516c
def v5 := [t12,t6,t7,t8,t9]
def t13 := 0x692e00
def v6 := [t6,t13,t7,t8,t9]
def t14 := 0x11c
def v7 := [t14,t6,t7,t8,t9]
def t15 := 0xb3dfff
def v8 := [t6,t7,t8,t15,t9]
def t16 := 0x250e3
def v9 := [t16,t6,t7,t8,t9]
def t17 := 0xb18e00
def v10 := [t6,t7,t17,t8,t9]
def t18 := 0x1e0
def v11 := [t18,t6,t7,t8,t9]
def t19 := 0xde5fff
def v12 := [t6,t7,t8,t9,t19]
def t20 := 0x2501f
def v13 := [t20,t6,t7,t8,t9]
def t21 := 0xdc0e00
def v14 := [t6,t7,t8,t21,t9]
def t22 := 0x210e10
def v15 := [t6,t22,t7,t8,t9]
def t23 := 0xf9af9f
def v16 := [t6,t7,t8,t9,t23]
def t24 := 0x482083
def v17 := [t6,t24,t7,t8,t9]
def t25 := 0x90810c
def v18 := [t6,t7,t25,t8,t9]
def t26 := 0x480e80
def v19 := [t6,t26,t7,t8,t9]
def t27 := 0xfd2ff3
def v20 := [t6,t7,t8,t9,t27]
def t28 := 0x212013
def v21 := [t6,t28,t7,t8,t9]
def t29 := 0x940160
def v22 := [t6,t7,t29,t8,t9]
def t30 := 0x900f00
def v23 := [t6,t7,t30,t8,t9]
def t31 := 0xfd8ffc
def v24 := [t6,t7,t8,t9,t31]
def t32 := 0x21801c
def v25 := [t6,t32,t7,t8,t9]
def t33 := 0x4c00e0
def v26 := [t6,t33,t7,t8,t9]
def v27 := [t14,t16,t7,t8,t9]
def t34 := 0x10
def v28 := [t34,t6,t7,t8,t9]
def t35 := 0x692f9f
def v29 := [t6,t35,t8,t9]
def v30 := [t14,t6,t35,t8,t9]
def v31 := [t6,t7,t35,t8,t9]
def t36 := 0x10c
def v32 := [t36,t6,t7,t8,t9]
def t37 := 0x692e83
def v33 := [t6,t37,t8,t9]
def v34 := [t14,t6,t37,t8,t9]
def v35 := [t6,t37,t7,t8,t9]
def v36 := [t14,t6,t7,t17,t9]
def t38 := 0x100
def v37 := [t38,t6,t7,t8,t9]
def t39 := 0xdc0ffc
def v38 := [t6,t7,t8,t39]
def v39 := [t14,t6,t7,t8,t39]
def v40 := [t6,t7,t8,t9,t39]
def t40 := 0x1c
def v41 := [t40,t6,t7,t8,t9]
def t41 := 0xdc0ee0
def v42 := [t6,t7,t8,t41]
def v43 := [t14,t6,t7,t8,t41]
def v44 := [t6,t7,t8,t41,t9]
def v45 := [t14,t7,t15,t9]
def v46 := [t14,t6,t7,t15,t9]
def v47 := [t14,t7,t8,t15,t9]
def v48 := [t14,t6,t22,t7,t9]
def v49 := [t14,t6,t24,t7,t9]
def v50 := [t14,t6,t7,t30,t9]
def v51 := [t14,t6,t33,t7,t9]
def map27_2 : Projection 12 12 := pick [2,3,0,1,4,5,6,8,7,9,11,10] rfl (by decide +kernel) (by decide)
def p31_27 : Projection 24 12 := pick [0,1,6,7,8,12,13,14,18,19,20,21] rfl (by decide +kernel) (by decide)
def t42 := 0x195557ffffff
def v52 := [t0,t1,t42,t2,t3,t4]
def v53 := [t10,t11,t8,t9]
def v54 := [t10,t6,t11,t8,t9]
def v55 := [t10,t7,t11,t8,t9]
def v56 := [t12,t6,t11,t8,t9]
def v57 := [t13,t7,t11,t8,t9]
def v58 := [t6,t11,t8,t9,t23]
def v59 := [t6,t24,t11,t8,t9]
def v60 := [t6,t11,t8,t9,t27]
def v61 := [t6,t28,t11,t8,t9]
def t43 := 0x210f1c
def v62 := [t6,t43,t7,t9]
def v63 := [t6,t43,t7,t11,t9]
def v64 := [t6,t43,t7,t8,t9]
def t44 := 0xfbffff
def v65 := [t6,t7,t8,t9,t44]
def t45 := 0x4a70e3
def v66 := [t6,t45,t7,t9]
def v67 := [t6,t45,t7,t11,t9]
def v68 := [t6,t45,t7,t8,t9]
def t46 := 0x908000
def v69 := [t6,t7,t46,t8,t9]
def t47 := 0x480fe0
def v70 := [t6,t47,t7,t8]
def v71 := [t6,t47,t7,t11,t8]
def v72 := [t6,t47,t7,t8,t9]
def t48 := 0xff7fff
def v73 := [t6,t7,t8,t9,t48]
def t49 := 0x23701f
def v74 := [t6,t49,t7,t8]
def v75 := [t6,t49,t7,t11,t8]
def v76 := [t6,t49,t7,t8,t9]
def t50 := 0x940000
def v77 := [t6,t7,t50,t8,t9]
def t51 := 0x104544b2cc
def v78 := [t51,t0,t1,t2,t3,t4]
def v79 := [t18,t20,t7,t8,t9]
def t52 := 0x13
def v80 := [t52,t6,t7,t8,t9]
def t53 := 0x6b7e9f
def v81 := [t6,t7,t53,t8,t9]
def t54 := 0x2500c
def v82 := [t54,t6,t7,t8,t9]
def t55 := 0x692e80
def v83 := [t6,t55,t7,t8,t9]
def t56 := 0xb3df1f
def v84 := [t6,t7,t8,t56,t9]
def t57 := 0x25003
def v85 := [t57,t6,t7,t8,t9]
def t58 := 0xb18f00
def v86 := [t6,t7,t58,t8,t9]
def v87 := [t20,t6,t7,t8,t19]
def v88 := [t20,t7,t8,t21]
def v89 := [t20,t6,t7,t8,t21]
def v90 := [t20,t7,t8,t21,t9]
def v91 := [t20,t6,t26,t7,t8]
def v92 := [t20,t6,t28,t7,t8]
def v93 := [t20,t6,t7,t30,t8]
def v94 := [t20,t6,t32,t7,t8]
def map27_3 : Projection 12 12 := pick [2,3,5,6,8,0,1,4,7,11,9,10] rfl (by decide +kernel) (by decide)
def map27_4 : Projection 12 12 := pick [5,6,0,1,7,2,3,8,4,10,11,9] rfl (by decide +kernel) (by decide)
def t59 := 0x194512bb0c30
def v95 := [t0,t59,t1,t2,t3,t4]
def v96 := [t10,t6,t13,t8,t9]
def v97 := [t12,t13,t8,t9]
def v98 := [t12,t6,t13,t8,t9]
def v99 := [t12,t13,t7,t8,t9]
def t60 := 0x210e00
def v100 := [t6,t60,t7,t8,t9]
def t61 := 0xf9af1c
def v101 := [t6,t7,t8,t9,t61]
def t62 := 0x482000
def v102 := [t6,t62,t7,t8,t9]
def t63 := 0x90811c
def v103 := [t6,t7,t63,t8,t9]
def t64 := 0x480e00
def v104 := [t6,t64,t7,t8,t9]
def t65 := 0xfd2fe0
def v105 := [t6,t7,t8,t9,t65]
def t66 := 0x212000
def v106 := [t6,t66,t7,t8,t9]
def t67 := 0x9401e0
def v107 := [t6,t7,t67,t8,t9]
def v108 := [t6,t13,t8,t9,t23]
def v109 := [t6,t24,t13,t8,t9]
def v110 := [t6,t13,t8,t9,t27]
def v111 := [t6,t28,t13,t8,t9]
def t68 := 0x40820c
def v112 := [t68,t0,t1,t2,t3,t4]
def t69 := 0xc29a6dc7ffff
def v113 := [t0,t1,t2,t69,t3,t4]
def t70 := 0x10450471c3
def v114 := [t70,t0,t1,t2,t3,t4]
def t71 := 0xc28a28830c30
def v115 := [t0,t1,t71,t2,t3,t4]
def t72 := 0x4403c0
def v116 := [t72,t0,t1,t2,t3,t4]
def t73 := 0x14f
def t74 := 0x4b3
def t75 := 0xa3c
def v117 := [t73,t74,t75]
def p31_7 : Projection 24 6 := pick [0,1,2,3,4,5] rfl (by decide +kernel) (by decide)
def t76 := 0xec1fc5fcffcf
def v118 := [t0,t1,t2,t3,t76,t4]
def t77 := 0xf7f045fff3cf
def v119 := [t0,t1,t2,t3,t4,t77]
def map31_1 : Projection 24 24 := pick [0,1,2,3,4,5,12,13,14,15,16,17,6,7,8,9,10,11,18,20,19,21,22,23] rfl (by decide +kernel) (by decide)
def t78 := 0x104500f00f
def v120 := [t78,t0,t1,t2,t3,t4]
def t79 := 0x10450003cf
def v121 := [t79,t0,t1,t2,t3,t4]
def t80 := 0xec0f80b80c00
def v122 := [t0,t1,t2,t80,t3,t4]
def t81 := 0x44f000
def v123 := [t81,t0,t1,t2,t3,t4]
def t82 := 0xf7e000bb0000
def v124 := [t0,t1,t2,t3,t82,t4]
def t83 := 0x830c30
def v125 := [t83,t0,t1,t2,t3,t4]
def t84 := 0xdbcf3afbcf3f
def v126 := [t0,t1,t2,t84,t3,t4]
def t85 := 0x194512384103
def v127 := [t0,t85,t1,t2,t3,t4]
def t86 := 0xc28a2840820c
def v128 := [t0,t1,t86,t2,t3,t4]
def t87 := 0x80500b80d00
def v129 := [t0,t87,t1,t2,t3,t4]
def t88 := 0x114000bb4000
def v130 := [t0,t88,t1,t2,t3,t4]
def t89 := 0xfd4f92ff4ff3
def v131 := [t0,t1,t2,t3,t4,t89]
def t90 := 0xffe512fffd33
def v132 := [t0,t1,t2,t3,t4,t90]
def v133 := [t0,t42,t2,t3,t4,t90]
def v134 := [t0,t59,t2,t3,t4,t90]
def v135 := [t0,t1,t2,t3,t77,t90]
def v136 := [t0,t1,t2,t3,t82,t90]
def t91 := 0x44f103
def v137 := [t91,t0,t1,t2,t3,t4]
def t92 := 0xfff557ffffff
def v138 := [t0,t1,t2,t3,t4,t92]
def t93 := 0x10450002cc
def v139 := [t93,t0,t1,t2,t3,t4]
def t94 := 0xffe512bb0c30
def v140 := [t0,t1,t2,t3,t4,t94]
def v141 := [t0,t88,t2,t3,t90]
def v142 := [t0,t88,t1,t2,t3,t90]
def v143 := [t0,t88,t2,t3,t4,t90]
def t95 := 0x80512000d33
def v144 := [t0,t95,t1,t2,t3,t90]
def t96 := 0xe6a00044b000
def v145 := [t0,t2,t96,t3,t4,t90]
def v146 := [t0,t1,t2,t96,t3,t4]
def t97 := 0xee8fa8ff8ffc
def v147 := [t0,t1,t2,t97,t4,t90]
def t98 := 0x2c05803c01c0
def v148 := [t0,t1,t98,t2,t4,t90]
def t99 := 0xf7ea28fffe3c
def v149 := [t0,t1,t2,t3,t99,t90]
def t100 := 0x3560003c7000
def v150 := [t0,t1,t100,t2,t3,t90]
def t101 := 0xc28000c38c30
def v151 := [t0,t1,t101,t2,t3,t4]
def t102 := 0xffef3affff3f
def v152 := [t0,t1,t2,t3,t4,t102]
def t103 := 0xa2800020c
def v153 := [t103,t0,t1,t2,t3,t4]
def t104 := 0x3d65123c7103
def v154 := [t0,t1,t104,t2,t3,t4]
def t105 := 0xe40000fc0000
def v155 := [t0,t1,t2,t105,t3,t90]
def t106 := 0x80f80000fc0
def v156 := [t0,t106,t1,t2,t3,t90]
def t107 := 0xec0500fc0d00
def v157 := [t0,t1,t2,t107,t3,t4]
def t108 := 0xffef92fffff3
def v158 := [t0,t1,t2,t3,t4,t108]
def t109 := 0xa800002c0
def v159 := [t109,t0,t1,t2,t3,t4]
def t110 := 0x13e01203f033
def v160 := [t0,t110,t1,t2,t3,t4]
def v161 := [t0,t95,t1,t2,t3,t4]
def t111 := 0x114012034033
def v162 := [t0,t111,t1,t2,t3,t4]
def t112 := 0x23d1ff
def v163 := [t6,t112,t7,t8,t9]
def t113 := 0x251e3
def v164 := [t113,t6,t7,t8,t9]
def t114 := 0x218000
def v165 := [t6,t114,t7,t8,t9]
def v166 := [t6,t32,t7,t15,t9]
def v167 := [t6,t32,t7,t17,t9]
def v168 := [t18,t6,t32,t7,t8]
def t115 := 0x210010
def v169 := [t6,t115,t7,t8,t9]
def t116 := 0x69ae9f
def v170 := [t6,t116,t8,t9]
def v171 := [t6,t32,t116,t8,t9]
def v172 := [t6,t7,t116,t8,t9]
def t117 := 0x800c
def v173 := [t117,t6,t7,t8,t9]
def t118 := 0x482e83
def v174 := [t6,t118,t8,t9]
def v175 := [t6,t32,t118,t8,t9]
def v176 := [t6,t118,t7,t8,t9]
def v177 := [t6,t32,t7,t30,t9]
def v178 := [t6,t32,t7,t8,t31]
def v179 := [t6,t22,t32,t7,t9]
def v180 := [t6,t32,t24,t7,t9]
def v181 := [t6,t32,t7,t8,t27]
def v182 := [t6,t32,t7,t29,t8]
def v183 := [t6,t32,t33,t7]
def v184 := [t6,t32,t33,t7,t8]
def v185 := [t6,t32,t33,t7,t9]
def t119 := 0xe40a804402c0
def v186 := [t0,t1,t2,t119,t3,t4]
def t120 := 0xc00a00c00e00
def v187 := [t0,t1,t120,t2,t3,t4]
def v188 := [t0,t1,t2,t97,t4]
def v189 := [t0,t1,t2,t3,t97,t4]
def t121 := 0x2802803803c
def v190 := [t0,t121,t1,t2,t3,t4]
def v191 := [t0,t1,t98,t2,t4]
def v192 := [t0,t1,t98,t2,t3,t4]
def t122 := 0xc28000c38000
def v193 := [t0,t1,t122,t2,t3,t4]
def v194 := [t0,t1,t2,t3,t99]
def v195 := [t0,t1,t2,t3,t4,t99]
def t123 := 0xa28000e3c
def v196 := [t123,t0,t1,t2,t3,t4]
def v197 := [t0,t1,t100,t2,t3]
def v198 := [t0,t1,t100,t2,t3,t4]
def v199 := [t0,t1,t2,t105,t3,t4]
def t124 := 0xffef80ffffc0
def v200 := [t0,t1,t2,t3,t4,t124]
def v201 := [t0,t106,t1,t2,t3,t4]
def t125 := 0x13e00003f000
def v202 := [t0,t125,t1,t2,t3,t4]
theorem b0 : Ban 12 4 v3 := checkedSmall
theorem b1 : Ban 12 4 v4 := checkedSmall
theorem b2 : Ban 12 4 v5 := checkedSmall
theorem b3 : Ban 12 4 v6 := checkedSmall
theorem b4 : Ban 12 4 v7 := checkedSmall
theorem b5 : Ban 12 4 v8 := checkedSmall
theorem b6 : Ban 12 4 v9 := checkedSmall
theorem b7 : Ban 12 4 v10 := checkedSmall
theorem b8 : Ban 12 4 v11 := checkedSmall
theorem b9 : Ban 12 4 v12 := checkedSmall
theorem b10 : Ban 12 4 v13 := checkedSmall
theorem b11 : Ban 12 4 v14 := checkedSmall
theorem b12 : Ban 12 4 v15 := checkedSmall
theorem b13 : Ban 12 4 v16 := checkedSmall
theorem b14 : Ban 12 4 v17 := checkedSmall
theorem b15 : Ban 12 4 v18 := checkedSmall
theorem b16 : Ban 12 4 v19 := checkedSmall
theorem b17 : Ban 12 4 v20 := checkedSmall
theorem b18 : Ban 12 4 v21 := checkedSmall
theorem b19 : Ban 12 4 v22 := checkedSmall
theorem b20 : Ban 12 4 v23 := checkedSmall
theorem b21 : Ban 12 4 v24 := checkedSmall
theorem b22 : Ban 12 4 v25 := checkedSmall
theorem b23 : Ban 12 4 v26 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b24 : Ban 12 5 v2 := viaBranch (ws := [v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26]) (consBan b0 (consBan b1 (consBan b2 (consBan b3 (consBan b4 (consBan b5 (consBan b6 (consBan b7 (consBan b8 (consBan b9 (consBan b10 (consBan b11 (consBan b12 (consBan b13 (consBan b14 (consBan b15 (consBan b16 (consBan b17 (consBan b18 (consBan b19 (consBan b20 (consBan b21 (consBan b22 (consBan b23 (nilBan 12 4))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b25 : Ban 12 4 v27 := checkedSmall
theorem b26 : Ban 12 4 v28 := checkedSmall
theorem b27 : Ban 12 4 v29 := checkedSmall
theorem b28 : Ban 12 4 v30 := checkedSmall
theorem b29 : Ban 12 4 v31 := checkedSmall
theorem b30 : Ban 12 4 v32 := checkedSmall
theorem b31 : Ban 12 4 v33 := checkedSmall
theorem b32 : Ban 12 4 v34 := checkedSmall
theorem b33 : Ban 12 4 v35 := checkedSmall
theorem b34 : Ban 12 4 v36 := checkedSmall
theorem b35 : Ban 12 4 v37 := checkedSmall
theorem b36 : Ban 12 4 v38 := checkedSmall
theorem b37 : Ban 12 4 v39 := checkedSmall
theorem b38 : Ban 12 4 v40 := checkedSmall
theorem b39 : Ban 12 4 v41 := checkedSmall
theorem b40 : Ban 12 4 v42 := checkedSmall
theorem b41 : Ban 12 4 v43 := checkedSmall
theorem b42 : Ban 12 4 v44 := checkedSmall
theorem b43 : Ban 12 4 v45 := checkedSmall
theorem b44 : Ban 12 4 v46 := checkedSmall
theorem b45 : Ban 12 4 v47 := checkedSmall
theorem b46 : Ban 12 4 v48 := checkedSmall
theorem b47 : Ban 12 4 v49 := checkedSmall
theorem b48 : Ban 12 4 v50 := checkedSmall
theorem b49 : Ban 12 4 v51 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b50 : Ban 12 5 v7 := viaBranch (ws := [v27,v9,v28,v29,v30,v31,v32,v33,v34,v35,v36,v10,v37,v38,v39,v40,v41,v42,v43,v44,v45,v46,v47,v48,v49,v50,v51]) (consBan b25 (consBan b6 (consBan b26 (consBan b27 (consBan b28 (consBan b29 (consBan b30 (consBan b31 (consBan b32 (consBan b33 (consBan b34 (consBan b7 (consBan b35 (consBan b36 (consBan b37 (consBan b38 (consBan b39 (consBan b40 (consBan b41 (consBan b42 (consBan b43 (consBan b44 (consBan b45 (consBan b46 (consBan b47 (consBan b48 (consBan b49 (nilBan 12 4)))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b51 : Ban 12 5 v3 := viaPerm map27_2 map27_2 b50 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w0 : Wide 12 5 v3 := viaSub (ws := [v2,v3]) (consBan b24 (consBan b51 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b52 : Ban 24 6 v1 := smallByCut p31_27 w0
theorem b53 : Ban 12 4 v53 := checkedSmall
theorem b54 : Ban 12 4 v54 := checkedSmall
theorem b55 : Ban 12 4 v55 := checkedSmall
theorem b56 : Ban 12 4 v56 := checkedSmall
theorem b57 : Ban 12 4 v57 := checkedSmall
theorem b58 : Ban 12 4 v58 := checkedSmall
theorem b59 : Ban 12 4 v59 := checkedSmall
theorem b60 : Ban 12 4 v60 := checkedSmall
theorem b61 : Ban 12 4 v61 := checkedSmall
theorem b62 : Ban 12 4 v62 := checkedSmall
theorem b63 : Ban 12 4 v63 := checkedSmall
theorem b64 : Ban 12 4 v64 := checkedSmall
theorem b65 : Ban 12 4 v65 := checkedSmall
theorem b66 : Ban 12 4 v66 := checkedSmall
theorem b67 : Ban 12 4 v67 := checkedSmall
theorem b68 : Ban 12 4 v68 := checkedSmall
theorem b69 : Ban 12 4 v69 := checkedSmall
theorem b70 : Ban 12 4 v70 := checkedSmall
theorem b71 : Ban 12 4 v71 := checkedSmall
theorem b72 : Ban 12 4 v72 := checkedSmall
theorem b73 : Ban 12 4 v73 := checkedSmall
theorem b74 : Ban 12 4 v74 := checkedSmall
theorem b75 : Ban 12 4 v75 := checkedSmall
theorem b76 : Ban 12 4 v76 := checkedSmall
theorem b77 : Ban 12 4 v77 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b78 : Ban 12 5 v4 := viaBranch (ws := [v53,v54,v55,v56,v57,v6,v5,v58,v59,v60,v61,v62,v63,v64,v65,v66,v67,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77]) (consBan b53 (consBan b54 (consBan b55 (consBan b56 (consBan b57 (consBan b3 (consBan b2 (consBan b58 (consBan b59 (consBan b60 (consBan b61 (consBan b62 (consBan b63 (consBan b64 (consBan b65 (consBan b66 (consBan b67 (consBan b68 (consBan b69 (consBan b70 (consBan b71 (consBan b72 (consBan b73 (consBan b74 (consBan b75 (consBan b76 (consBan b77 (nilBan 12 4)))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w1 : Wide 12 5 v4 := viaSub (ws := [v2,v4]) (consBan b24 (consBan b78 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b79 : Ban 24 6 v52 := smallByCut p31_27 w1
theorem b80 : Ban 12 4 v79 := checkedSmall
theorem b81 : Ban 12 4 v80 := checkedSmall
theorem b82 : Ban 12 4 v81 := checkedSmall
theorem b83 : Ban 12 4 v82 := checkedSmall
theorem b84 : Ban 12 4 v83 := checkedSmall
theorem b85 : Ban 12 4 v84 := checkedSmall
theorem b86 : Ban 12 4 v85 := checkedSmall
theorem b87 : Ban 12 4 v86 := checkedSmall
theorem b88 : Ban 12 4 v87 := checkedSmall
theorem b89 : Ban 12 4 v88 := checkedSmall
theorem b90 : Ban 12 4 v89 := checkedSmall
theorem b91 : Ban 12 4 v90 := checkedSmall
theorem b92 : Ban 12 4 v91 := checkedSmall
theorem b93 : Ban 12 4 v92 := checkedSmall
theorem b94 : Ban 12 4 v93 := checkedSmall
theorem b95 : Ban 12 4 v94 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b96 : Ban 12 5 v13 := viaBranch (ws := [v79,v11,v80,v81,v82,v83,v41,v84,v85,v86,v87,v12,v88,v89,v90,v91,v92,v93,v94]) (consBan b80 (consBan b8 (consBan b81 (consBan b82 (consBan b83 (consBan b84 (consBan b39 (consBan b85 (consBan b86 (consBan b87 (consBan b88 (consBan b9 (consBan b89 (consBan b90 (consBan b91 (consBan b92 (consBan b93 (consBan b94 (consBan b95 (nilBan 12 4)))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b97 : Ban 12 5 v5 := viaPerm map27_3 map27_4 b96 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w2 : Wide 12 5 v5 := viaSub (ws := [v2,v5]) (consBan b24 (consBan b97 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b98 : Ban 24 6 v78 := smallByCut p31_27 w2
theorem b99 : Ban 12 4 v96 := checkedSmall
theorem b100 : Ban 12 4 v97 := checkedSmall
theorem b101 : Ban 12 4 v98 := checkedSmall
theorem b102 : Ban 12 4 v99 := checkedSmall
theorem b103 : Ban 12 4 v100 := checkedSmall
theorem b104 : Ban 12 4 v101 := checkedSmall
theorem b105 : Ban 12 4 v102 := checkedSmall
theorem b106 : Ban 12 4 v103 := checkedSmall
theorem b107 : Ban 12 4 v104 := checkedSmall
theorem b108 : Ban 12 4 v105 := checkedSmall
theorem b109 : Ban 12 4 v106 := checkedSmall
theorem b110 : Ban 12 4 v107 := checkedSmall
theorem b111 : Ban 12 4 v108 := checkedSmall
theorem b112 : Ban 12 4 v109 := checkedSmall
theorem b113 : Ban 12 4 v110 := checkedSmall
theorem b114 : Ban 12 4 v111 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b115 : Ban 12 5 v6 := viaBranch (ws := [v4,v57,v96,v97,v98,v99,v3,v100,v101,v102,v103,v104,v105,v106,v107,v108,v109,v110,v111]) (consBan b1 (consBan b57 (consBan b99 (consBan b100 (consBan b101 (consBan b102 (consBan b0 (consBan b103 (consBan b104 (consBan b105 (consBan b106 (consBan b107 (consBan b108 (consBan b109 (consBan b110 (consBan b111 (consBan b112 (consBan b113 (consBan b114 (nilBan 12 4)))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w3 : Wide 12 5 v6 := viaSub (ws := [v2,v6]) (consBan b24 (consBan b115 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b116 : Ban 24 6 v95 := smallByCut p31_27 w3
theorem b169 : Ban 12 4 v163 := checkedSmall
theorem b170 : Ban 12 4 v164 := checkedSmall
theorem b171 : Ban 12 4 v165 := checkedSmall
theorem b172 : Ban 12 4 v166 := checkedSmall
theorem b173 : Ban 12 4 v167 := checkedSmall
theorem b174 : Ban 12 4 v168 := checkedSmall
theorem b175 : Ban 12 4 v169 := checkedSmall
theorem b176 : Ban 12 4 v170 := checkedSmall
theorem b177 : Ban 12 4 v171 := checkedSmall
theorem b178 : Ban 12 4 v172 := checkedSmall
theorem b179 : Ban 12 4 v173 := checkedSmall
theorem b180 : Ban 12 4 v174 := checkedSmall
theorem b181 : Ban 12 4 v175 := checkedSmall
theorem b182 : Ban 12 4 v176 := checkedSmall
theorem b183 : Ban 12 4 v177 := checkedSmall
theorem b184 : Ban 12 4 v178 := checkedSmall
theorem b185 : Ban 12 4 v179 := checkedSmall
theorem b186 : Ban 12 4 v180 := checkedSmall
theorem b187 : Ban 12 4 v181 := checkedSmall
theorem b188 : Ban 12 4 v182 := checkedSmall
theorem b189 : Ban 12 4 v183 := checkedSmall
theorem b190 : Ban 12 4 v184 := checkedSmall
theorem b191 : Ban 12 4 v185 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b192 : Ban 12 5 v25 := viaBranch (ws := [v41,v163,v164,v165,v166,v167,v168,v94,v169,v170,v171,v172,v173,v174,v175,v176,v177,v23,v178,v24,v179,v180,v181,v182,v183,v184,v185]) (consBan b39 (consBan b169 (consBan b170 (consBan b171 (consBan b172 (consBan b173 (consBan b174 (consBan b95 (consBan b175 (consBan b176 (consBan b177 (consBan b178 (consBan b179 (consBan b180 (consBan b181 (consBan b182 (consBan b183 (consBan b20 (consBan b184 (consBan b21 (consBan b185 (consBan b186 (consBan b187 (consBan b188 (consBan b189 (consBan b190 (consBan b191 (nilBan 12 4)))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b193 : Ban 12 5 v17 := viaPerm map27_4 map27_3 b192 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w9 : Wide 12 5 v17 := viaSub (ws := [v2,v17]) (consBan b24 (consBan b193 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b118 : Ban 24 6 v112 := smallByCut p31_27 w9
theorem b119 : Ban 24 6 v113 := smallByCut p31_27 w9
theorem b120 : Ban 24 6 v114 := smallByCut p31_27 w9
theorem b121 : Ban 24 6 v115 := smallByCut p31_27 w9
theorem b122 : Ban 6 3 v117 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w6 : Wide 6 3 v117 := viaSub (ws := [v117]) (consBan b122 (nilBan 6 3)) (by decide) (by decide +kernel)
theorem b123 : Ban 24 6 v116 := smallByCut p31_7 w6
theorem b124 : Ban 12 5 v12 := viaPerm map27_4 map27_3 b78 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w7 : Wide 12 5 v12 := viaSub (ws := [v2,v12]) (consBan b24 (consBan b124 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b125 : Ban 24 6 v119 := smallByCut p31_27 w7
theorem b126 : Ban 24 6 v118 := viaPerm map31_1 map31_1 b125 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w8 : Wide 12 5 v13 := viaSub (ws := [v2,v13]) (consBan b24 (consBan b96 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b127 : Ban 24 6 v121 := smallByCut p31_27 w8
theorem b128 : Ban 24 6 v120 := viaPerm map31_1 map31_1 b127 (by decide +kernel) (by decide +kernel)
theorem b129 : Ban 24 6 v122 := smallByCut p31_7 w6
theorem b130 : Ban 24 6 v123 := smallByCut p31_7 w6
theorem b131 : Ban 24 6 v124 := smallByCut p31_7 w6
theorem b132 : Ban 24 6 v125 := smallByCut p31_27 w9
theorem b133 : Ban 24 6 v126 := smallByCut p31_27 w9
theorem b134 : Ban 24 6 v127 := smallByCut p31_27 w9
theorem b135 : Ban 24 6 v128 := smallByCut p31_27 w9
theorem b137 : Ban 24 6 v129 := smallByCut p31_7 w6
theorem solidb60 : Wide 12 4 v60 := solid b60
theorem b138 : Ban 24 5 v133 := smallByCut p31_27 solidb60
theorem solidb113 : Wide 12 4 v110 := solid b113
theorem b139 : Ban 24 5 v134 := smallByCut p31_27 solidb113
theorem b140 : Ban 24 5 v135 := checkedSmall
theorem b141 : Ban 24 5 v136 := smallByCut p31_7 w6
theorem b142 : Ban 24 5 v137 := checkedSmall
theorem b143 : Ban 24 5 v138 := checkedSmall
theorem b144 : Ban 24 5 v139 := checkedSmall
theorem b145 : Ban 24 5 v140 := checkedSmall
theorem b146 : Ban 24 5 v141 := smallByCut p31_7 w6
theorem b147 : Ban 24 5 v142 := smallByCut p31_7 w6
theorem b148 : Ban 24 5 v143 := smallByCut p31_7 w6
theorem b149 : Ban 24 5 v144 := checkedSmall
theorem b150 : Ban 24 5 v145 := smallByCut p31_7 w6
theorem b151 : Ban 24 5 v146 := smallByCut p31_7 w6
theorem b152 : Ban 24 5 v147 := checkedSmall
theorem b153 : Ban 24 5 v148 := smallByCut p31_7 w6
theorem b154 : Ban 24 5 v149 := checkedSmall
theorem b155 : Ban 24 5 v150 := smallByCut p31_7 w6
theorem b156 : Ban 24 5 v151 := smallByCut p31_27 w9
theorem b157 : Ban 24 5 v152 := checkedSmall
theorem b158 : Ban 24 5 v153 := smallByCut p31_27 w9
theorem b159 : Ban 24 5 v154 := checkedSmall
theorem b160 : Ban 24 5 v155 := smallByCut p31_7 w6
theorem b161 : Ban 24 5 v156 := smallByCut p31_7 w6
theorem b162 : Ban 24 5 v157 := smallByCut p31_7 w6
theorem b163 : Ban 24 5 v158 := smallByCut p31_7 w6
theorem b164 : Ban 24 5 v159 := smallByCut p31_7 w6
theorem b165 : Ban 24 5 v160 := smallByCut p31_7 w6
theorem b166 : Ban 24 5 v161 := smallByCut p31_7 w6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b167 : Ban 24 6 v132 := viaBranch (ws := [v133,v134,v135,v136,v137,v138,v139,v140,v141,v142,v143,v144,v145,v146,v147,v148,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v159,v160,v161]) (consBan b138 (consBan b139 (consBan b140 (consBan b141 (consBan b142 (consBan b143 (consBan b144 (consBan b145 (consBan b146 (consBan b147 (consBan b148 (consBan b149 (consBan b150 (consBan b151 (consBan b152 (consBan b153 (consBan b154 (consBan b155 (consBan b156 (consBan b157 (consBan b158 (consBan b159 (consBan b160 (consBan b161 (consBan b162 (consBan b163 (consBan b164 (consBan b165 (consBan b166 (nilBan 24 5)))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b168 : Ban 24 6 v131 := viaPerm map31_1 map31_1 b167 (by decide +kernel) (by decide +kernel)
theorem b194 : Ban 24 6 v162 := smallByCut p31_27 w9
theorem b195 : Ban 24 6 v186 := smallByCut p31_7 w6
theorem b136 : Ban 24 6 v130 := smallByCut p31_7 w6
theorem b196 : Ban 24 6 v161 := viaPerm map31_1 map31_1 b194 (by decide +kernel) (by decide +kernel)
theorem b197 : Ban 24 6 v146 := smallByCut p31_7 w6
theorem b198 : Ban 24 6 v187 := smallByCut p31_7 w6
theorem b199 : Ban 24 6 v188 := smallByCut p31_27 w9
theorem b200 : Ban 24 6 v189 := smallByCut p31_27 w9
theorem b201 : Ban 24 6 v190 := smallByCut p31_27 w9
theorem b202 : Ban 24 6 v191 := smallByCut p31_27 w9
theorem b203 : Ban 24 6 v192 := smallByCut p31_7 w6
theorem b204 : Ban 24 6 v193 := smallByCut p31_7 w6
theorem b205 : Ban 24 6 v194 := smallByCut p31_27 w9
theorem b206 : Ban 24 6 v195 := smallByCut p31_27 w9
theorem b207 : Ban 24 6 v196 := smallByCut p31_27 w9
theorem b208 : Ban 24 6 v197 := smallByCut p31_27 w9
theorem b209 : Ban 24 6 v198 := smallByCut p31_7 w6
theorem b210 : Ban 24 6 v199 := smallByCut p31_7 w6
theorem b211 : Ban 24 6 v200 := smallByCut p31_7 w6
theorem b212 : Ban 24 6 v201 := smallByCut p31_7 w6
theorem b213 : Ban 24 6 v202 := smallByCut p31_7 w6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b214 : Ban 24 7 v0 := viaBranch (ws := [v1,v52,v78,v95,v112,v113,v114,v115,v116,v118,v120,v122,v123,v119,v121,v124,v125,v126,v127,v128,v129,v131,v162,v186,v130,v132,v161,v146,v187,v188,v189,v190,v191,v192,v193,v194,v195,v196,v197,v198,v199,v200,v201,v202]) (consBan b52 (consBan b79 (consBan b98 (consBan b116 (consBan b118 (consBan b119 (consBan b120 (consBan b121 (consBan b123 (consBan b126 (consBan b128 (consBan b129 (consBan b130 (consBan b125 (consBan b127 (consBan b131 (consBan b132 (consBan b133 (consBan b134 (consBan b135 (consBan b137 (consBan b168 (consBan b194 (consBan b195 (consBan b136 (consBan b167 (consBan b196 (consBan b197 (consBan b198 (consBan b199 (consBan b200 (consBan b201 (consBan b202 (consBan b203 (consBan b204 (consBan b205 (consBan b206 (consBan b207 (consBan b208 (consBan b209 (consBan b210 (consBan b211 (consBan b212 (consBan b213 (nilBan 24 6))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem verifiedPin : Wide 24 7 v0 := widen (by decide +kernel) b214
end PEqualNP.Outside.L_meta_16501.Support.Core1

namespace PEqualNP.Outside.L_meta_16501.Reduce
namespace Ground0
open PEqualNP.Outside.L_meta_16501.Support PEqualNP.Outside.L_meta_16501.Support.Core0

def coreGoal := pin6 false goal
def rows : List Nat := [3, 3, 6, 6, 7, 9, 9, 11, 13, 13, 14, 14, 19, 19, 21, 21, 21, 22, 22, 25, 25, 26, 26, 26, 29, 30, 1, 2, 2, 4, 5, 1, 8, 10, 5, 12, 10, 12, 17, 18, 5, 17, 20, 18, 20, 17, 24, 10, 18, 24, 28, 28]
def pack (w : BitVec 32) := actL rows (canon w).toNat

private def mix (s t : Bool) (a b : BitVec 32) : BitVec 32 :=
  if s then (if t then a ||| b else b ^^^ (a &&& b))
  else if t then a ^^^ (a &&& b) else a &&& b

private theorem mix_correct (x y : BitVec 32) :
    canon (x &&& y) = mix (x.getLsbD 0) (y.getLsbD 0) (canon x) (canon y) := by
  cases hx : x.getLsbD 0 <;> cases hy : y.getLsbD 0 <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    cases hp : x.getLsbD i <;> cases hq : y.getLsbD i <;>
    simp only [canon, mix, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_xor,
      BitVec.getLsbD_or, hx, hy, hp, hq, decide_eq_true hi, Bool.false_and, Bool.true_and, ite_false, ite_true, Bool.false_eq_true] <;> rfl

private theorem pack_mix (s t : Bool) (a b : BitVec 32) :
    actL rows (mix s t a b).toNat =
      combine (opIndex s t) (actL rows a.toNat) (actL rows b.toNat) := by
  cases s <;> cases t <;> simp [mix, opIndex, combine, BitVec.toNat_xor, BitVec.toNat_and,
    BitVec.toNat_or, actL_and, actL_or, actL_xor]

private theorem canon_signed (s : Bool) (x : BitVec 32) : canon (signed s x) = canon x := by
  cases s
  · rfl
  · exact canon_not x

private theorem pack_gate (s t : Bool) (a b : BitVec 32) :
    ∃ d < 4, pack (gate s t a b) = combine d (pack a) (pack b) := by
  let x := signed s a
  let y := signed t b
  refine ⟨opIndex (x.getLsbD 0) (y.getLsbD 0), op_lt _ _, ?_⟩
  change actL rows (canon (canon (x &&& y))).toNat = _
  rw [canon_canon, mix_correct, pack_mix]
  simp [x, y, pack, canon_signed]

private theorem word_sep : Good 26 (pack coreGoal) := by
  intro i hi
  have h : ∀ j : Fin 26, (pack coreGoal).testBit j.val ≠ (pack coreGoal).testBit (26+j.val) := by decide +kernel
  exact h ⟨i,hi⟩

theorem possible {k S} (h : Path coreGoal k S) {av : List Nat}
    (carry : ∀ w∈S, pack w ∈ av) : Possible 26 k av := by
  apply h (fun n T => ∀ av : List Nat, (∀ w∈T, pack w ∈ av) → Possible 26 n av) ?_ ?_ av carry
  · intro v yes
    refine ⟨0,{pack coreGoal},le_rfl,?_,?_⟩
    · exact PEqualNP.Outside.L_meta_16501.Support.Live.done word_sep (by decide +kernel)
    · simpa using yes coreGoal (by simp)
  · intro k a b U s t _ _ _ ih v yes
    obtain ⟨d,hd,hop⟩ := pack_gate s t a b
    have future : Possible 26 k (v ++ [combine d (pack a) (pack b)]) := by
      apply ih
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | old
      · simp [hop]
      · exact List.mem_append_left _ (yes w (by simp [old]))
    obtain ⟨n,T,le,live,mem⟩ := pullPaid hd (yes _ (by simp)) (yes _ (by simp)) future
    refine ⟨n,T,?_,live,mem⟩
    cases h : charge v (combine d (pack a) (pack b)) <;> simp [h] at le <;> omega

theorem lower (k : Nat) (T : Finset (BitVec 32)) (raw : T ⊆ fiveRaw.toFinset)
    (path : Path coreGoal k T) : 8 ≤ k := by
  by_contra! short
  have tick : ∀ w∈fiveRaw, pack w ∈ v0 := by
    simp [fiveRaw]
    decide +kernel
  obtain ⟨n,S,le,live,inc⟩ := possible path (fun w hw => tick w (List.mem_toFinset.mp (raw hw)))
  exact verifiedPin ⟨n,S,by omega,live,inc⟩

end Ground0
end PEqualNP.Outside.L_meta_16501.Reduce

namespace PEqualNP.Outside.L_meta_16501.Reduce
namespace Ground1
open PEqualNP.Outside.L_meta_16501.Support PEqualNP.Outside.L_meta_16501.Support.Core1

def coreGoal := pin6 true goal
def rows : List Nat := [3, 3, 5, 5, 6, 6, 9, 9, 11, 13, 14, 14, 17, 17, 19, 21, 22, 22, 25, 26, 26, 26, 29, 30, 1, 2, 1, 4, 2, 4, 1, 8, 10, 12, 10, 12, 1, 16, 18, 20, 18, 20, 24, 10, 18, 24, 28, 28]
def pack (w : BitVec 32) := actL rows (canon w).toNat

private def mix (s t : Bool) (a b : BitVec 32) : BitVec 32 :=
  if s then (if t then a ||| b else b ^^^ (a &&& b))
  else if t then a ^^^ (a &&& b) else a &&& b

private theorem mix_correct (x y : BitVec 32) :
    canon (x &&& y) = mix (x.getLsbD 0) (y.getLsbD 0) (canon x) (canon y) := by
  cases hx : x.getLsbD 0 <;> cases hy : y.getLsbD 0 <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    cases hp : x.getLsbD i <;> cases hq : y.getLsbD i <;>
    simp only [canon, mix, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_xor,
      BitVec.getLsbD_or, hx, hy, hp, hq, decide_eq_true hi, Bool.false_and, Bool.true_and, ite_false, ite_true, Bool.false_eq_true] <;> rfl

private theorem pack_mix (s t : Bool) (a b : BitVec 32) :
    actL rows (mix s t a b).toNat =
      combine (opIndex s t) (actL rows a.toNat) (actL rows b.toNat) := by
  cases s <;> cases t <;> simp [mix, opIndex, combine, BitVec.toNat_xor, BitVec.toNat_and,
    BitVec.toNat_or, actL_and, actL_or, actL_xor]

private theorem canon_signed (s : Bool) (x : BitVec 32) : canon (signed s x) = canon x := by
  cases s
  · rfl
  · exact canon_not x

private theorem pack_gate (s t : Bool) (a b : BitVec 32) :
    ∃ d < 4, pack (gate s t a b) = combine d (pack a) (pack b) := by
  let x := signed s a
  let y := signed t b
  refine ⟨opIndex (x.getLsbD 0) (y.getLsbD 0), op_lt _ _, ?_⟩
  change actL rows (canon (canon (x &&& y))).toNat = _
  rw [canon_canon, mix_correct, pack_mix]
  simp [x, y, pack, canon_signed]

private theorem word_sep : Good 24 (pack coreGoal) := by
  intro i hi
  have h : ∀ j : Fin 24, (pack coreGoal).testBit j.val ≠ (pack coreGoal).testBit (24+j.val) := by decide +kernel
  exact h ⟨i,hi⟩

theorem possible {k S} (h : Path coreGoal k S) {av : List Nat}
    (carry : ∀ w∈S, pack w ∈ av) : Possible 24 k av := by
  apply h (fun n T => ∀ av : List Nat, (∀ w∈T, pack w ∈ av) → Possible 24 n av) ?_ ?_ av carry
  · intro v yes
    refine ⟨0,{pack coreGoal},le_rfl,?_,?_⟩
    · exact PEqualNP.Outside.L_meta_16501.Support.Live.done word_sep (by decide +kernel)
    · simpa using yes coreGoal (by simp)
  · intro k a b U s t _ _ _ ih v yes
    obtain ⟨d,hd,hop⟩ := pack_gate s t a b
    have future : Possible 24 k (v ++ [combine d (pack a) (pack b)]) := by
      apply ih
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | old
      · simp [hop]
      · exact List.mem_append_left _ (yes w (by simp [old]))
    obtain ⟨n,T,le,live,mem⟩ := pullPaid hd (yes _ (by simp)) (yes _ (by simp)) future
    refine ⟨n,T,?_,live,mem⟩
    cases h : charge v (combine d (pack a) (pack b)) <;> simp [h] at le <;> omega

theorem lower (k : Nat) (T : Finset (BitVec 32)) (raw : T ⊆ fiveRaw.toFinset)
    (path : Path coreGoal k T) : 8 ≤ k := by
  by_contra! short
  have tick : ∀ w∈fiveRaw, pack w ∈ v0 := by
    simp [fiveRaw]
    decide +kernel
  obtain ⟨n,S,le,live,inc⟩ := possible path (fun w hw => tick w (List.mem_toFinset.mp (raw hw)))
  exact verifiedPin ⟨n,S,by omega,live,inc⟩

end Ground1
end PEqualNP.Outside.L_meta_16501.Reduce
namespace PEqualNP.Outside.L_meta_16501.Frame
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem enough : ∀ s, HasCircuitSize 6 target s → ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x)=target x := by
  rintro s ⟨C,fan,sz,correct⟩
  by_cases hn : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨b,n,hb,h⟩ := freely_chain C.gates C.output fan correct hn
    obtain ⟨e,k,hk,T,sub,path⟩ := Reduce.select h
    have low : 8 ≤ k := by
      cases e
      · exact Reduce.Ground0.lower k T sub path
      · exact Reduce.Ground1.lower k T sub path
    refine ⟨witness,wmono,?_,wcomputes⟩
    change C.gates.length ≤ s at sz
    change 11 ≤ s
    omega
  · refine ⟨C,?_,sz,correct⟩
    intro g hg
    obtain ⟨op,len⟩ := fan g hg
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.imp_right (fun h => h.resolve_right (fun e => hn ⟨g,hg,e⟩)),len⟩
end PEqualNP.Outside.L_meta_16501.Frame
theorem PEqualNP.Outside.L_meta_16501 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4008241864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 4008241864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := PEqualNP.Outside.L_meta_16501.Frame.enough
