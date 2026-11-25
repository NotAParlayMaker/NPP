import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12104.Frame
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def target (x : Fin 6 → Bool) := Nat.testBit (4276676608 * 2 ^ 32 + 3900735488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def witness : Circuit := ⟨[⟨.or,[0,1]⟩, ⟨.and,[0,1]⟩, ⟨.or,[2,5]⟩, ⟨.and,[2,5]⟩, ⟨.and,[6,8]⟩, ⟨.or,[7,9]⟩, ⟨.or,[10,11]⟩, ⟨.and,[10,11]⟩, ⟨.or,[3,4]⟩, ⟨.and,[3,4]⟩, ⟨.and,[13,14]⟩, ⟨.and,[12,15]⟩, ⟨.or,[16,17]⟩],18⟩
theorem wmono : Monotone2 witness := by simp [Monotone2,witness]
theorem wcomputes : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x)=target x := by decide +kernel
end PEqualNP.Outside.L_meta_12104.Frame

namespace PEqualNP.Outside.L_meta_12104

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Word := BitVec 64
def ones : Word := BitVec.allOnes 64
def goal : Word := 0xe8e8fe008080e8
def roots : List Word := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff, 0xffff0000ffff, 0xffffffff00000000]

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

def assignment (r : Fin 64) : Fin 6 → Bool := fun i => (r.val ^^^ 24).testBit i.val
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
  ([(2, 3), (1, 3), (1, 5), (3, 11), (3, 19), (1, 33)]
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

end PEqualNP.Outside.L_meta_12104
namespace PEqualNP.Outside.L_meta_12104.Reduce
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
end PEqualNP.Outside.L_meta_12104.Reduce
namespace PEqualNP.Outside.L_meta_12104.Reduce
open PEqualNP.Outside.L_meta_12104

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
end PEqualNP.Outside.L_meta_12104.Reduce

namespace PEqualNP.Outside.L_meta_12104.Reduce
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
end PEqualNP.Outside.L_meta_12104.Reduce

namespace PEqualNP.Outside.L_meta_12104.Support

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

end PEqualNP.Outside.L_meta_12104.Support
namespace PEqualNP.Outside.L_meta_12104.Support.Core0
def w0 : ℕ := 0x842108400f83ff
def w1 : ℕ := 0x108421081f07c1f
def w2 : ℕ := 0x21084213e007fe0
def w3 : ℕ := 0x42108423fff8000
def v0 : List ℕ := [w0,w1,w2,w3]
def w4 : ℕ := 0x1f
def v1 : List ℕ := [w4,w0,w1,w2,w3]
def w5 : ℕ := 0x842108400f83e0
def v2 : List ℕ := [w4,w5,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b4 : Ban 30 4 v2 := viaSmall (by decide +kernel) (by decide)
def w6 : ℕ := 0x108421081f07c00
def v3 : List ℕ := [w4,w0,w6,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b5 : Ban 30 4 v3 := viaSmall (by decide +kernel) (by decide)
def w7 : ℕ := 0x42108423fff801f
def v4 : List ℕ := [w4,w0,w1,w2,w7]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b6 : Ban 30 4 v4 := viaSmall (by decide +kernel) (by decide)
def w8 : ℕ := 0x21084213e007fff
def v5 : List ℕ := [w4,w0,w1,w8,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b7 : Ban 30 4 v5 := viaSmall (by decide +kernel) (by decide)
def w9 : ℕ := 0x18c6318c1ffffff
def v6 : List ℕ := [w4,w0,w9,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b8 : Ban 30 4 v6 := viaSmall (by decide +kernel) (by decide)
def v7 : List ℕ := [w4,w1,w9,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b9 : Ban 30 4 v7 := viaSmall (by decide +kernel) (by decide)
def v8 : List ℕ := [w4,w9,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b10 : Ban 30 4 v8 := viaSmall (by decide +kernel) (by decide)
def v9 : List ℕ := [w5,w0,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b11 : Ban 30 4 v9 := viaSmall (by decide +kernel) (by decide)
def v10 : List ℕ := [w0,w6,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b12 : Ban 30 4 v10 := viaSmall (by decide +kernel) (by decide)
def v11 : List ℕ := [w0,w1,w2,w8,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b13 : Ban 30 4 v11 := viaSmall (by decide +kernel) (by decide)
def v12 : List ℕ := [w0,w1,w2,w3,w7]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b14 : Ban 30 4 v12 := viaSmall (by decide +kernel) (by decide)
def v13 : List ℕ := [w0,w1,w2,w7]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b15 : Ban 30 4 v13 := viaSmall (by decide +kernel) (by decide)
def v14 : List ℕ := [w0,w1,w8,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b16 : Ban 30 4 v14 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b3 : Ban 30 5 v1 := viaBranch (ws := [v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14])
  (consBan b4 (consBan b5 (consBan b6 (consBan b7 (consBan b8 (consBan b9 (consBan b10 (consBan b11 (consBan b12 (consBan b13 (consBan b14 (consBan b15 (consBan b16 (nilBan _ _))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def w10 : ℕ := 0x3e0
def v15 : List ℕ := [w10,w0,w1,w2,w3]
def proj0 : Projection 30 30 := pick [5,7,6,8,9,0,2,1,3,4,10,12,11,13,14,15,17,16,18,19,25,27,26,28,29,20,22,21,23,24] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b17 : Ban 30 5 v15 := viaPerm proj0 proj0 b3 (by decide +kernel) (by decide +kernel)
def w11 : ℕ := 0x7c00
def v16 : List ℕ := [w11,w0,w1,w2,w3]
def proj1 : Projection 30 30 := pick [11,12,10,13,14,1,2,0,3,4,6,7,5,8,9,21,22,20,23,24,26,27,25,28,29,16,17,15,18,19] rfl (by decide +kernel) (by decide)
def proj2 : Projection 30 30 := pick [7,5,6,8,9,12,10,11,13,14,2,0,1,3,4,27,25,26,28,29,17,15,16,18,19,22,20,21,23,24] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b18 : Ban 30 5 v16 := viaPerm proj1 proj2 b3 (by decide +kernel) (by decide +kernel)
def w12 : ℕ := 0xf8000
def v17 : List ℕ := [w12,w0,w1,w2,w3]
def proj3 : Projection 30 30 := pick [15,18,16,17,19,0,3,1,2,4,20,23,21,22,24,5,8,6,7,9,25,28,26,27,29,10,13,11,12,14] rfl (by decide +kernel) (by decide)
def proj4 : Projection 30 30 := pick [5,7,8,6,9,15,17,18,16,19,25,27,28,26,29,0,2,3,1,4,10,12,13,11,14,20,22,23,21,24] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b19 : Ban 30 5 v17 := viaPerm proj3 proj4 b3 (by decide +kernel) (by decide +kernel)
def w13 : ℕ := 0x1f00000
def v18 : List ℕ := [w13,w0,w1,w2,w3]
def proj5 : Projection 30 30 := pick [21,23,20,22,24,1,3,0,2,4,16,18,15,17,19,11,13,10,12,14,26,28,25,27,29,6,8,5,7,9] rfl (by decide +kernel) (by decide)
def proj6 : Projection 30 30 := pick [7,5,8,6,9,27,25,28,26,29,17,15,18,16,19,12,10,13,11,14,2,0,3,1,4,22,20,23,21,24] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b20 : Ban 30 5 v18 := viaPerm proj5 proj6 b3 (by decide +kernel) (by decide +kernel)
def w14 : ℕ := 0x3e000000
def v19 : List ℕ := [w14,w0,w1,w2,w3]
def proj7 : Projection 30 30 := pick [27,28,25,26,29,7,8,5,6,9,17,18,15,16,19,12,13,10,11,14,22,23,20,21,24,2,3,0,1,4] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b21 : Ban 30 5 v19 := viaPerm proj7 proj7 b3 (by decide +kernel) (by decide +kernel)
def w15 : ℕ := 0x842108400003ff
def v20 : List ℕ := [w15,w0,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b23 : Ban 30 4 v1 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b24 : Ban 30 4 v15 := viaSmall (by decide +kernel) (by decide)
def v21 : List ℕ := [w12,w15,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b25 : Ban 30 4 v21 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b26 : Ban 30 4 v17 := viaSmall (by decide +kernel) (by decide)
def w16 : ℕ := 0x8421084000001f
def v22 : List ℕ := [w16,w0,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b27 : Ban 30 4 v22 := viaSmall (by decide +kernel) (by decide)
def w17 : ℕ := 0x842108400003e0
def v23 : List ℕ := [w17,w0,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b28 : Ban 30 4 v23 := viaSmall (by decide +kernel) (by decide)
def w18 : ℕ := 0x842108400f801f
def v24 : List ℕ := [w15,w18,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b29 : Ban 30 4 v24 := viaSmall (by decide +kernel) (by decide)
def v25 : List ℕ := [w15,w5,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b30 : Ban 30 4 v25 := viaSmall (by decide +kernel) (by decide)
def w19 : ℕ := 0x42108423ff00000
def v26 : List ℕ := [w15,w0,w1,w2,w19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b31 : Ban 30 4 v26 := viaSmall (by decide +kernel) (by decide)
def w20 : ℕ := 0x4a5294a7fff83ff
def v27 : List ℕ := [w15,w0,w1,w2,w20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b32 : Ban 30 4 v27 := viaSmall (by decide +kernel) (by decide)
def v28 : List ℕ := [w15,w1,w9,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b33 : Ban 30 4 v28 := viaSmall (by decide +kernel) (by decide)
def w21 : ℕ := 0x294a5297e0fffff
def v29 : List ℕ := [w15,w1,w2,w21,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b34 : Ban 30 4 v29 := viaSmall (by decide +kernel) (by decide)
def v30 : List ℕ := [w15,w1,w2,w19,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b35 : Ban 30 4 v30 := viaSmall (by decide +kernel) (by decide)
def w22 : ℕ := 0x18c6318c1f07fff
def v31 : List ℕ := [w0,w1,w22,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b36 : Ban 30 4 v31 := viaSmall (by decide +kernel) (by decide)
def w23 : ℕ := 0x21084213e007c00
def v32 : List ℕ := [w0,w1,w23,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b37 : Ban 30 4 v32 := viaSmall (by decide +kernel) (by decide)
def w24 : ℕ := 0x294a5297e007fff
def v33 : List ℕ := [w0,w1,w2,w24,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b38 : Ban 30 4 v33 := viaSmall (by decide +kernel) (by decide)
def v34 : List ℕ := [w0,w1,w2,w3,w20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b39 : Ban 30 4 v34 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b22 : Ban 30 5 v20 := viaBranch (ws := [v1,v15,v21,v17,v22,v23,v24,v25,v26,v27,v28,v29,v30,v10,v31,v32,v33,v34])
  (consBan b23 (consBan b24 (consBan b25 (consBan b26 (consBan b27 (consBan b28 (consBan b29 (consBan b30 (consBan b31 (consBan b32 (consBan b33 (consBan b34 (consBan b35 (consBan b12 (consBan b36 (consBan b37 (consBan b38 (consBan b39 (nilBan _ _)))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def v35 : List ℕ := [w18,w0,w1,w2,w3]
def proj8 : Projection 30 30 := pick [0,1,3,2,4,15,16,18,17,19,20,21,23,22,24,5,6,8,7,9,10,11,13,12,14,25,26,28,27,29] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b40 : Ban 30 5 v35 := viaPerm proj8 proj8 b22 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b41 : Ban 30 5 v9 := viaPerm proj4 proj3 b22 (by decide +kernel) (by decide +kernel)
def w25 : ℕ := 0x108421080007c1f
def v36 : List ℕ := [w0,w25,w1,w2,w3]
def proj9 : Projection 30 30 := pick [1,0,2,3,4,11,10,12,13,14,6,5,7,8,9,21,20,22,23,24,16,15,17,18,19,26,25,27,28,29] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b42 : Ban 30 5 v36 := viaPerm proj9 proj9 b22 (by decide +kernel) (by decide +kernel)
def w26 : ℕ := 0x108421081f0001f
def v37 : List ℕ := [w0,w26,w1,w2,w3]
def proj10 : Projection 30 30 := pick [1,0,3,2,4,21,20,23,22,24,16,15,18,17,19,11,10,13,12,14,6,5,8,7,9,26,25,28,27,29] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b43 : Ban 30 5 v37 := viaPerm proj10 proj10 b22 (by decide +kernel) (by decide +kernel)
def proj11 : Projection 30 30 := pick [11,12,13,10,14,21,22,23,20,24,26,27,28,25,29,1,2,3,0,4,6,7,8,5,9,16,17,18,15,19] rfl (by decide +kernel) (by decide)
def proj12 : Projection 30 30 := pick [18,15,16,17,19,23,20,21,22,24,3,0,1,2,4,28,25,26,27,29,8,5,6,7,9,13,10,11,12,14] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b44 : Ban 30 5 v10 := viaPerm proj11 proj12 b22 (by decide +kernel) (by decide +kernel)
def v38 : List ℕ := [w0,w1,w9,w2,w3]
def w27 : ℕ := 0x7fe0
def v39 : List ℕ := [w27,w0,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b46 : Ban 30 4 v39 := viaSmall (by decide +kernel) (by decide)
def w28 : ℕ := 0x1ff8000
def v40 : List ℕ := [w28,w0,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b47 : Ban 30 4 v40 := viaSmall (by decide +kernel) (by decide)
def v41 : List ℕ := [w18,w1,w9,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b48 : Ban 30 4 v41 := viaSmall (by decide +kernel) (by decide)
def v42 : List ℕ := [w5,w0,w9,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b49 : Ban 30 4 v42 := viaSmall (by decide +kernel) (by decide)
def v43 : List ℕ := [w0,w25,w9,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b50 : Ban 30 4 v43 := viaSmall (by decide +kernel) (by decide)
def v44 : List ℕ := [w0,w26,w9,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b51 : Ban 30 4 v44 := viaSmall (by decide +kernel) (by decide)
def w29 : ℕ := 0x18c6318c0007fff
def v45 : List ℕ := [w0,w1,w29,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b52 : Ban 30 4 v45 := viaSmall (by decide +kernel) (by decide)
def w30 : ℕ := 0x18c6318c1ff801f
def v46 : List ℕ := [w0,w1,w30,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b53 : Ban 30 4 v46 := viaSmall (by decide +kernel) (by decide)
def w31 : ℕ := 0x21084213e000000
def v47 : List ℕ := [w0,w1,w31,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b54 : Ban 30 4 v47 := viaSmall (by decide +kernel) (by decide)
def w32 : ℕ := 0x39ce739ffffffff
def v48 : List ℕ := [w0,w1,w2,w32,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b55 : Ban 30 4 v48 := viaSmall (by decide +kernel) (by decide)
def w33 : ℕ := 0x42108423e000000
def v49 : List ℕ := [w0,w1,w2,w33,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b56 : Ban 30 4 v49 := viaSmall (by decide +kernel) (by decide)
def w34 : ℕ := 0x5ad6b5affffffff
def v50 : List ℕ := [w0,w1,w2,w3,w34]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b57 : Ban 30 4 v50 := viaSmall (by decide +kernel) (by decide)
def w35 : ℕ := 0x318c631bff07fff
def v51 : List ℕ := [w0,w9,w2,w35,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b58 : Ban 30 4 v51 := viaSmall (by decide +kernel) (by decide)
def w36 : ℕ := 0x5294a52bffffc1f
def v52 : List ℕ := [w0,w9,w2,w3,w36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b59 : Ban 30 4 v52 := viaSmall (by decide +kernel) (by decide)
def v53 : List ℕ := [w6,w1,w9,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b60 : Ban 30 4 v53 := viaSmall (by decide +kernel) (by decide)
def v54 : List ℕ := [w1,w9,w2,w21,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b61 : Ban 30 4 v54 := viaSmall (by decide +kernel) (by decide)
def v55 : List ℕ := [w1,w9,w2,w3,w20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b62 : Ban 30 4 v55 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b45 : Ban 30 5 v38 := viaBranch (ws := [v6,v7,v8,v39,v40,v28,v41,v9,v42,v43,v44,v10,v45,v46,v47,v48,v49,v50,v51,v52,v53,v54,v55])
  (consBan b8 (consBan b9 (consBan b10 (consBan b46 (consBan b47 (consBan b33 (consBan b48 (consBan b11 (consBan b49 (consBan b50 (consBan b51 (consBan b12 (consBan b52 (consBan b53 (consBan b54 (consBan b55 (consBan b56 (consBan b57 (consBan b58 (consBan b59 (consBan b60 (consBan b61 (consBan b62 (nilBan _ _))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def w37 : ℕ := 0x210842100007fe0
def v56 : List ℕ := [w0,w1,w37,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b63 : Ban 30 5 v56 := viaPerm proj2 proj1 b22 (by decide +kernel) (by decide +kernel)
def w38 : ℕ := 0x21084213e0003e0
def v57 : List ℕ := [w0,w1,w38,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b64 : Ban 30 5 v57 := viaPerm proj6 proj5 b22 (by decide +kernel) (by decide +kernel)
def proj13 : Projection 30 30 := pick [12,11,13,10,14,27,26,28,25,29,22,21,23,20,24,7,6,8,5,9,2,1,3,0,4,17,16,18,15,19] rfl (by decide +kernel) (by decide)
def proj14 : Projection 30 30 := pick [23,21,20,22,24,18,16,15,17,19,3,1,0,2,4,28,26,25,27,29,13,11,10,12,14,8,6,5,7,9] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b65 : Ban 30 5 v32 := viaPerm proj13 proj14 b22 (by decide +kernel) (by decide +kernel)
def v58 : List ℕ := [w0,w1,w2,w21,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b66 : Ban 30 5 v58 := viaPerm proj0 proj0 b45 (by decide +kernel) (by decide +kernel)
def v59 : List ℕ := [w0,w1,w2,w35,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b67 : Ban 30 5 v59 := viaPerm proj1 proj2 b45 (by decide +kernel) (by decide +kernel)
def w39 : ℕ := 0x421084201ff8000
def v60 : List ℕ := [w0,w1,w2,w39,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b68 : Ban 30 5 v60 := viaPerm proj12 proj11 b22 (by decide +kernel) (by decide +kernel)
def w40 : ℕ := 0x42108423e0f8000
def v61 : List ℕ := [w0,w1,w2,w40,w3]
def proj15 : Projection 30 30 := pick [18,15,17,16,19,28,25,27,26,29,8,5,7,6,9,23,20,22,21,24,3,0,2,1,4,13,10,12,11,14] rfl (by decide +kernel) (by decide)
def proj16 : Projection 30 30 := pick [21,23,22,20,24,11,13,12,10,14,26,28,27,25,29,1,3,2,0,4,16,18,17,15,19,6,8,7,5,9] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b69 : Ban 30 5 v61 := viaPerm proj15 proj16 b22 (by decide +kernel) (by decide +kernel)
def v62 : List ℕ := [w0,w1,w2,w19,w3]
def proj17 : Projection 30 30 := pick [23,21,22,20,24,28,26,27,25,29,13,11,12,10,14,18,16,17,15,19,3,1,2,0,4,8,6,7,5,9] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b70 : Ban 30 5 v62 := viaPerm proj17 proj17 b22 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b71 : Ban 30 5 v34 := viaPerm proj3 proj4 b45 (by decide +kernel) (by decide +kernel)
def v63 : List ℕ := [w0,w1,w2,w3,w36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b72 : Ban 30 5 v63 := viaPerm proj5 proj6 b45 (by decide +kernel) (by decide +kernel)
def w41 : ℕ := 0x6318c633fffffe0
def v64 : List ℕ := [w0,w1,w2,w3,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b73 : Ban 30 5 v64 := viaPerm proj7 proj7 b45 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b2 : Ban 30 6 v0 := viaBranch (ws := [v1,v15,v16,v17,v18,v19,v20,v35,v9,v36,v37,v10,v38,v56,v57,v32,v58,v59,v60,v61,v62,v34,v63,v64])
  (consBan b3 (consBan b17 (consBan b18 (consBan b19 (consBan b20 (consBan b21 (consBan b22 (consBan b40 (consBan b41 (consBan b42 (consBan b43 (consBan b44 (consBan b45 (consBan b63 (consBan b64 (consBan b65 (consBan b66 (consBan b67 (consBan b68 (consBan b69 (consBan b70 (consBan b71 (consBan b72 (consBan b73 (nilBan _ _)))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit0 : Wide 30 6 v0 := viaSub (ws := [v0])
  (consBan b2 (nilBan _ _))
  (by decide) (by decide +kernel)
def w42 : ℕ := 0x3f
def w43 : ℕ := 0x4104104104104100003f000fc0fff
def w44 : ℕ := 0x82082082082082000fc003f03f03f
def w45 : ℕ := 0x10410410410410403f000fc003ffc0
def w46 : ℕ := 0x208208208208208fc0000ffffc0000
def w47 : ℕ := 0x410410410410410ffffff000000000
def v65 : List ℕ := [w42,w43,w44,w45,w46,w47]
def proj18 : Projection 60 30 := pick [13,14,15,16,17,25,26,27,28,29,31,32,33,34,35,43,44,45,46,47,49,50,51,52,53,55,56,57,58,59] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b74 : Ban 60 8 v65 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def w48 : ℕ := 0xfc0
def v66 : List ℕ := [w48,w43,w44,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b75 : Ban 60 8 v66 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def w49 : ℕ := 0x3f000
def v67 : List ℕ := [w49,w43,w44,w45,w46,w47]
def proj19 : Projection 60 30 := pick [6,8,9,10,11,18,20,21,22,23,30,32,33,34,35,36,38,39,40,41,48,50,51,52,53,54,56,57,58,59] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b76 : Ban 60 8 v67 := viaCut proj19 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def w50 : ℕ := 0xfc0000
def v68 : List ℕ := [w50,w43,w44,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b77 : Ban 60 8 v68 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def w51 : ℕ := 0x3f000000
def v69 : List ℕ := [w51,w43,w44,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b78 : Ban 60 8 v69 := viaCut proj19 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def w52 : ℕ := 0xfc0000000
def v70 : List ℕ := [w52,w43,w44,w45,w46,w47]
def proj20 : Projection 60 30 := pick [0,1,3,4,5,18,19,21,22,23,24,25,27,28,29,36,37,39,40,41,42,43,45,46,47,54,55,57,58,59] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b79 : Ban 60 8 v70 := viaCut proj20 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def w53 : ℕ := 0x3f000000000
def v71 : List ℕ := [w53,w43,w44,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b80 : Ban 60 8 v71 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def w54 : ℕ := 0xfc0000000000
def v72 : List ℕ := [w54,w43,w44,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b81 : Ban 60 8 v72 := viaCut proj19 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def w55 : ℕ := 0x3f000000000000
def v73 : List ℕ := [w55,w43,w44,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b82 : Ban 60 8 v73 := viaCut proj20 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def w56 : ℕ := 0xfc0000000000000
def v74 : List ℕ := [w56,w43,w44,w45,w46,w47]
def proj21 : Projection 60 30 := pick [0,1,2,4,5,6,7,8,10,11,12,13,14,16,17,36,37,38,40,41,42,43,44,46,47,48,49,50,52,53] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b83 : Ban 60 8 v74 := viaCut proj21 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def w57 : ℕ := 0x41041041041041000000000fc0fff
def v75 : List ℕ := [w57,w43,w44,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b84 : Ban 60 8 v75 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def w58 : ℕ := 0x4104104104104100003f000000fff
def v76 : List ℕ := [w58,w43,w44,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b85 : Ban 60 8 v76 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def w59 : ℕ := 0x4104104104104100003f000fc003f
def v77 : List ℕ := [w59,w43,w44,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b86 : Ban 60 8 v77 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def w60 : ℕ := 0x4104104104104100003f000fc0fc0
def v78 : List ℕ := [w60,w43,w44,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b87 : Ban 60 8 v78 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def w61 : ℕ := 0x8208208208208200000003f03f03f
def v79 : List ℕ := [w43,w61,w44,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b88 : Ban 60 8 v79 := viaCut proj19 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def w62 : ℕ := 0x82082082082082000fc000003f03f
def v80 : List ℕ := [w43,w62,w44,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b89 : Ban 60 8 v80 := viaCut proj19 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def w63 : ℕ := 0x82082082082082000fc003f00003f
def v81 : List ℕ := [w43,w63,w44,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b90 : Ban 60 8 v81 := viaCut proj19 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def w64 : ℕ := 0x82082082082082000fc003f03f000
def v82 : List ℕ := [w43,w64,w44,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b91 : Ban 60 8 v82 := viaCut proj19 petit0 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b94 : Ban 30 4 v16 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b95 : Ban 30 4 v18 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b96 : Ban 30 4 v19 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b97 : Ban 30 4 v20 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b98 : Ban 30 4 v35 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b99 : Ban 30 4 v36 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b100 : Ban 30 4 v37 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b101 : Ban 30 4 v38 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b102 : Ban 30 4 v56 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b103 : Ban 30 4 v57 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b104 : Ban 30 4 v58 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b105 : Ban 30 4 v59 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b106 : Ban 30 4 v60 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b107 : Ban 30 4 v61 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b108 : Ban 30 4 v62 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b109 : Ban 30 4 v63 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b110 : Ban 30 4 v64 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b93 : Ban 30 5 v0 := viaBranch (ws := [v1,v15,v16,v17,v18,v19,v20,v35,v9,v36,v37,v10,v38,v56,v57,v32,v58,v59,v60,v61,v62,v34,v63,v64])
  (consBan b23 (consBan b24 (consBan b94 (consBan b26 (consBan b95 (consBan b96 (consBan b97 (consBan b98 (consBan b11 (consBan b99 (consBan b100 (consBan b12 (consBan b101 (consBan b102 (consBan b103 (consBan b37 (consBan b104 (consBan b105 (consBan b106 (consBan b107 (consBan b108 (consBan b39 (consBan b109 (consBan b110 (nilBan _ _)))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit1 : Wide 30 5 v0 := viaSub (ws := [v0])
  (consBan b93 (nilBan _ _))
  (by decide) (by decide +kernel)
def w65 : ℕ := 0xc30c30c30c30c3000fff03fffffff
def v83 : List ℕ := [w42,w43,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b111 : Ban 60 7 v83 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v84 : List ℕ := [w42,w43,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b112 : Ban 60 7 v84 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v85 : List ℕ := [w42,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b113 : Ban 60 7 v85 := viaCut proj19 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v86 : List ℕ := [w42,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b114 : Ban 60 7 v86 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def v87 : List ℕ := [w48,w43,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b115 : Ban 60 7 v87 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v88 : List ℕ := [w49,w43,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b116 : Ban 60 7 v88 := viaCut proj19 petit1 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit2 : Wide 30 5 v38 := viaSub (ws := [v0,v38])
  (consBan b93 (consBan b45 (nilBan _ _)))
  (by decide) (by decide +kernel)
def w66 : ℕ := 0x3ffc0
def v89 : List ℕ := [w66,w43,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b117 : Ban 60 7 v89 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v90 : List ℕ := [w66,w43,w44,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b118 : Ban 60 7 v90 := viaCut proj20 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v91 : List ℕ := [w50,w43,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b119 : Ban 60 7 v91 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v92 : List ℕ := [w51,w43,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b120 : Ban 60 7 v92 := viaCut proj19 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def w67 : ℕ := 0x3ffc0000
def v93 : List ℕ := [w67,w43,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b121 : Ban 60 7 v93 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v94 : List ℕ := [w67,w43,w44,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b122 : Ban 60 7 v94 := viaCut proj21 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v95 : List ℕ := [w52,w43,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b123 : Ban 60 7 v95 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v96 : List ℕ := [w53,w43,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b124 : Ban 60 7 v96 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v97 : List ℕ := [w54,w43,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b125 : Ban 60 7 v97 := viaCut proj19 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def w68 : ℕ := 0xfff000000000
def v98 : List ℕ := [w68,w43,w44,w65,w45,w46,w47]
def proj22 : Projection 60 30 := pick [0,1,2,3,5,6,7,8,9,11,12,13,14,15,17,18,19,20,21,23,24,25,26,27,29,30,31,32,33,35] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b126 : Ban 60 7 v98 := viaCut proj22 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v99 : List ℕ := [w68,w43,w44,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b127 : Ban 60 7 v99 := viaCut proj22 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v100 : List ℕ := [w55,w43,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b128 : Ban 60 7 v100 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v101 : List ℕ := [w56,w43,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b129 : Ban 60 7 v101 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v102 : List ℕ := [w57,w43,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b130 : Ban 60 7 v102 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v103 : List ℕ := [w57,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b131 : Ban 60 7 v103 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def v104 : List ℕ := [w58,w43,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b132 : Ban 60 7 v104 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v105 : List ℕ := [w58,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b133 : Ban 60 7 v105 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def v106 : List ℕ := [w59,w43,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b134 : Ban 60 7 v106 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v107 : List ℕ := [w59,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b135 : Ban 60 7 v107 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def v108 : List ℕ := [w60,w43,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b136 : Ban 60 7 v108 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b137 : Ban 60 7 v78 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v109 : List ℕ := [w60,w43,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b138 : Ban 60 7 v109 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v110 : List ℕ := [w43,w61,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b139 : Ban 60 7 v110 := viaCut proj19 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v111 : List ℕ := [w43,w61,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b140 : Ban 60 7 v111 := viaCut proj19 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def v112 : List ℕ := [w43,w62,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b141 : Ban 60 7 v112 := viaCut proj19 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v113 : List ℕ := [w43,w62,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b142 : Ban 60 7 v113 := viaCut proj19 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def v114 : List ℕ := [w43,w63,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b143 : Ban 60 7 v114 := viaCut proj19 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v115 : List ℕ := [w43,w63,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b144 : Ban 60 7 v115 := viaCut proj19 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def v116 : List ℕ := [w43,w64,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b145 : Ban 60 7 v116 := viaCut proj19 petit1 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b146 : Ban 60 7 v82 := viaCut proj19 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v117 : List ℕ := [w4,w15,w0,w1,w2,w3]
def v118 : List ℕ := [w4,w15,w9,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b149 : Ban 30 4 v118 := viaSmall (by decide +kernel) (by decide)
def v119 : List ℕ := [w4,w0,w22,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b150 : Ban 30 4 v119 := viaSmall (by decide +kernel) (by decide)
def v120 : List ℕ := [w15,w0,w1,w2,w7]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b151 : Ban 30 4 v120 := viaSmall (by decide +kernel) (by decide)
def v121 : List ℕ := [w15,w0,w1,w8,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b152 : Ban 30 4 v121 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b148 : Ban 30 5 v117 := viaBranch (ws := [v118,v3,v119,v23,v25,v120,v121])
  (consBan b149 (consBan b5 (consBan b150 (consBan b28 (consBan b30 (consBan b151 (consBan b152 (nilBan _ _))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def v122 : List ℕ := [w10,w15,w0,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b153 : Ban 30 5 v122 := viaPerm proj0 proj0 b148 (by decide +kernel) (by decide +kernel)
def v123 : List ℕ := [w11,w15,w0,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b154 : Ban 30 5 v123 := viaSmall (by decide +kernel) (by decide)
def v124 : List ℕ := [w12,w15,w0,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b155 : Ban 30 5 v124 := viaSmall (by decide +kernel) (by decide)
def v125 : List ℕ := [w4,w5,w6,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b158 : Ban 30 4 v125 := viaSmall (by decide +kernel) (by decide)
def v126 : List ℕ := [w4,w5,w1,w2,w7]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b159 : Ban 30 4 v126 := viaSmall (by decide +kernel) (by decide)
def v127 : List ℕ := [w4,w5,w1,w8,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b160 : Ban 30 4 v127 := viaSmall (by decide +kernel) (by decide)
def v128 : List ℕ := [w4,w5,w9,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b161 : Ban 30 4 v128 := viaSmall (by decide +kernel) (by decide)
def v129 : List ℕ := [w5,w6,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b162 : Ban 30 4 v129 := viaSmall (by decide +kernel) (by decide)
def v130 : List ℕ := [w5,w1,w2,w8,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b163 : Ban 30 4 v130 := viaSmall (by decide +kernel) (by decide)
def v131 : List ℕ := [w5,w1,w2,w3,w7]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b164 : Ban 30 4 v131 := viaSmall (by decide +kernel) (by decide)
def v132 : List ℕ := [w5,w1,w2,w7]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b165 : Ban 30 4 v132 := viaSmall (by decide +kernel) (by decide)
def v133 : List ℕ := [w5,w1,w8,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b166 : Ban 30 4 v133 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b167 : Ban 30 4 v0 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b157 : Ban 30 5 v2 := viaBranch (ws := [v125,v126,v127,v128,v1,v7,v8,v9,v129,v130,v131,v132,v133,v0])
  (consBan b158 (consBan b159 (consBan b160 (consBan b161 (consBan b23 (consBan b9 (consBan b10 (consBan b11 (consBan b162 (consBan b163 (consBan b164 (consBan b165 (consBan b166 (consBan b167 (nilBan _ _)))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b156 : Ban 30 5 v21 := viaPerm proj3 proj4 b157 (by decide +kernel) (by decide +kernel)
def v134 : List ℕ := [w13,w15,w0,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b168 : Ban 30 5 v134 := viaSmall (by decide +kernel) (by decide)
def v135 : List ℕ := [w14,w15,w0,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b169 : Ban 30 5 v135 := viaSmall (by decide +kernel) (by decide)
def v136 : List ℕ := [w16,w15,w0,w1,w2,w3]
def w69 : ℕ := 0xf83e0
def v137 : List ℕ := [w69,w15,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b171 : Ban 30 4 v137 := viaSmall (by decide +kernel) (by decide)
def v138 : List ℕ := [w16,w15,w1,w21,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b172 : Ban 30 4 v138 := viaSmall (by decide +kernel) (by decide)
def v139 : List ℕ := [w16,w0,w1,w23,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b173 : Ban 30 4 v139 := viaSmall (by decide +kernel) (by decide)
def v140 : List ℕ := [w16,w0,w1,w2,w20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b174 : Ban 30 4 v140 := viaSmall (by decide +kernel) (by decide)
def v141 : List ℕ := [w16,w0,w1,w24,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b175 : Ban 30 4 v141 := viaSmall (by decide +kernel) (by decide)
def w70 : ℕ := 0x4a5294a7fff801f
def v142 : List ℕ := [w15,w0,w1,w2,w70]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b176 : Ban 30 4 v142 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b170 : Ban 30 5 v136 := viaBranch (ws := [v15,v137,v138,v139,v140,v141,v142])
  (consBan b24 (consBan b171 (consBan b172 (consBan b173 (consBan b174 (consBan b175 (consBan b176 (nilBan _ _))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def v143 : List ℕ := [w69,w16,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b178 : Ban 30 4 v143 := viaSmall (by decide +kernel) (by decide)
def v144 : List ℕ := [w69,w0,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b179 : Ban 30 4 v144 := viaSmall (by decide +kernel) (by decide)
def w71 : ℕ := 0x84210840000000
def v145 : List ℕ := [w71,w0,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b180 : Ban 30 4 v145 := viaSmall (by decide +kernel) (by decide)
def v146 : List ℕ := [w16,w5,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b181 : Ban 30 4 v146 := viaSmall (by decide +kernel) (by decide)
def v147 : List ℕ := [w16,w0,w1,w2,w19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b182 : Ban 30 4 v147 := viaSmall (by decide +kernel) (by decide)
def v148 : List ℕ := [w16,w0,w1,w2,w70]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b183 : Ban 30 4 v148 := viaSmall (by decide +kernel) (by decide)
def v149 : List ℕ := [w16,w0,w1,w21,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b184 : Ban 30 4 v149 := viaSmall (by decide +kernel) (by decide)
def v150 : List ℕ := [w16,w1,w9,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b185 : Ban 30 4 v150 := viaSmall (by decide +kernel) (by decide)
def w72 : ℕ := 0x18c6318c1f07c1f
def v151 : List ℕ := [w0,w1,w72,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b186 : Ban 30 4 v151 := viaSmall (by decide +kernel) (by decide)
def v152 : List ℕ := [w0,w1,w2,w3,w70]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b187 : Ban 30 4 v152 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b177 : Ban 30 5 v22 := viaBranch (ws := [v1,v143,v144,v145,v146,v139,v147,v148,v140,v141,v149,v150,v10,v151,v33,v152])
  (consBan b23 (consBan b178 (consBan b179 (consBan b180 (consBan b181 (consBan b173 (consBan b182 (consBan b183 (consBan b174 (consBan b175 (consBan b184 (consBan b185 (consBan b12 (consBan b186 (consBan b38 (consBan b187 (nilBan _ _)))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def v153 : List ℕ := [w17,w15,w0,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b188 : Ban 30 5 v153 := viaPerm proj0 proj0 b170 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b189 : Ban 30 5 v23 := viaPerm proj0 proj0 b177 (by decide +kernel) (by decide +kernel)
def v154 : List ℕ := [w15,w18,w0,w1,w2,w3]
def v155 : List ℕ := [w15,w18,w1,w23,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b191 : Ban 30 4 v155 := viaSmall (by decide +kernel) (by decide)
def v156 : List ℕ := [w15,w18,w1,w2,w19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b192 : Ban 30 4 v156 := viaSmall (by decide +kernel) (by decide)
def v157 : List ℕ := [w15,w18,w1,w2,w20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b193 : Ban 30 4 v157 := viaSmall (by decide +kernel) (by decide)
def v158 : List ℕ := [w15,w18,w1,w21,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b194 : Ban 30 4 v158 := viaSmall (by decide +kernel) (by decide)
def v159 : List ℕ := [w18,w0,w1,w23,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b195 : Ban 30 4 v159 := viaSmall (by decide +kernel) (by decide)
def v160 : List ℕ := [w18,w0,w1,w24,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b196 : Ban 30 4 v160 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b190 : Ban 30 5 v154 := viaBranch (ws := [v15,v17,v22,v155,v156,v157,v158,v26,v142,v159,v160])
  (consBan b24 (consBan b26 (consBan b27 (consBan b191 (consBan b192 (consBan b193 (consBan b194 (consBan b31 (consBan b176 (consBan b195 (consBan b196 (nilBan _ _))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def v161 : List ℕ := [w10,w18,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b198 : Ban 30 4 v161 := viaSmall (by decide +kernel) (by decide)
def v162 : List ℕ := [w17,w18,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b199 : Ban 30 4 v162 := viaSmall (by decide +kernel) (by decide)
def w73 : ℕ := 0x842108400f8000
def v163 : List ℕ := [w15,w73,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b200 : Ban 30 4 v163 := viaSmall (by decide +kernel) (by decide)
def v164 : List ℕ := [w15,w18,w1,w2,w70]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b201 : Ban 30 4 v164 := viaSmall (by decide +kernel) (by decide)
def v165 : List ℕ := [w15,w18,w1,w24,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b202 : Ban 30 4 v165 := viaSmall (by decide +kernel) (by decide)
def w74 : ℕ := 0x18c6318c1fffc1f
def v166 : List ℕ := [w15,w1,w74,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b203 : Ban 30 4 v166 := viaSmall (by decide +kernel) (by decide)
def v167 : List ℕ := [w18,w1,w22,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b204 : Ban 30 4 v167 := viaSmall (by decide +kernel) (by decide)
def v168 : List ℕ := [w18,w1,w23,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b205 : Ban 30 4 v168 := viaSmall (by decide +kernel) (by decide)
def v169 : List ℕ := [w18,w1,w2,w3,w20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b206 : Ban 30 4 v169 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b197 : Ban 30 5 v24 := viaBranch (ws := [v161,v21,v162,v163,v155,v156,v164,v157,v165,v158,v20,v166,v29,v30,v35,v167,v168,v169,v0])
  (consBan b198 (consBan b25 (consBan b199 (consBan b200 (consBan b191 (consBan b192 (consBan b201 (consBan b193 (consBan b202 (consBan b194 (consBan b97 (consBan b203 (consBan b34 (consBan b35 (consBan b98 (consBan b204 (consBan b205 (consBan b206 (consBan b167 (nilBan _ _))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def v170 : List ℕ := [w15,w5,w0,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b207 : Ban 30 5 v170 := viaPerm proj0 proj0 b190 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b208 : Ban 30 5 v25 := viaPerm proj0 proj0 b197 (by decide +kernel) (by decide +kernel)
def v171 : List ℕ := [w15,w0,w25,w1,w2,w3]
def v172 : List ℕ := [w15,w25,w9,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b210 : Ban 30 4 v172 := viaSmall (by decide +kernel) (by decide)
def w75 : ℕ := 0x18c6318c00fffff
def v173 : List ℕ := [w15,w1,w75,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b211 : Ban 30 4 v173 := viaSmall (by decide +kernel) (by decide)
def w76 : ℕ := 0x108421080007c00
def v174 : List ℕ := [w0,w76,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b212 : Ban 30 4 v174 := viaSmall (by decide +kernel) (by decide)
def v175 : List ℕ := [w0,w25,w6,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b213 : Ban 30 4 v175 := viaSmall (by decide +kernel) (by decide)
def v176 : List ℕ := [w0,w25,w22,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b214 : Ban 30 4 v176 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b209 : Ban 30 5 v171 := viaBranch (ws := [v1,v23,v25,v172,v173,v174,v175,v176,v45])
  (consBan b23 (consBan b28 (consBan b30 (consBan b210 (consBan b211 (consBan b212 (consBan b213 (consBan b214 (consBan b52 (nilBan _ _))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def v177 : List ℕ := [w15,w0,w26,w1,w2,w3]
def v178 : List ℕ := [w15,w26,w9,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b216 : Ban 30 4 v178 := viaSmall (by decide +kernel) (by decide)
def w77 : ℕ := 0x18c6318c1ff83ff
def v179 : List ℕ := [w15,w1,w77,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b217 : Ban 30 4 v179 := viaSmall (by decide +kernel) (by decide)
def w78 : ℕ := 0x108421081f00000
def v180 : List ℕ := [w0,w78,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b218 : Ban 30 4 v180 := viaSmall (by decide +kernel) (by decide)
def v181 : List ℕ := [w0,w26,w6,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b219 : Ban 30 4 v181 := viaSmall (by decide +kernel) (by decide)
def v182 : List ℕ := [w0,w26,w22,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b220 : Ban 30 4 v182 := viaSmall (by decide +kernel) (by decide)
def w79 : ℕ := 0x18c6318c1f003ff
def v183 : List ℕ := [w0,w1,w79,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b221 : Ban 30 4 v183 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b215 : Ban 30 5 v177 := viaBranch (ws := [v1,v23,v25,v178,v179,v180,v181,v182,v183])
  (consBan b23 (consBan b28 (consBan b30 (consBan b216 (consBan b217 (consBan b218 (consBan b219 (consBan b220 (consBan b221 (nilBan _ _))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def v184 : List ℕ := [w15,w0,w6,w1,w2,w3]
def v185 : List ℕ := [w17,w0,w6,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b223 : Ban 30 4 v185 := viaSmall (by decide +kernel) (by decide)
def v186 : List ℕ := [w15,w5,w6,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b224 : Ban 30 4 v186 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b222 : Ban 30 5 v184 := viaBranch (ws := [v3,v185,v186,v28,v31])
  (consBan b5 (consBan b223 (consBan b224 (consBan b33 (consBan b36 (nilBan _ _))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def v187 : List ℕ := [w15,w0,w1,w22,w2,w3]
def v188 : List ℕ := [w17,w0,w22,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b226 : Ban 30 4 v188 := viaSmall (by decide +kernel) (by decide)
def v189 : List ℕ := [w15,w5,w22,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b227 : Ban 30 4 v189 := viaSmall (by decide +kernel) (by decide)
def v190 : List ℕ := [w0,w1,w22,w2,w20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b228 : Ban 30 4 v190 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b225 : Ban 30 5 v187 := viaBranch (ws := [v119,v21,v188,v189,v28,v10,v190])
  (consBan b150 (consBan b25 (consBan b226 (consBan b227 (consBan b33 (consBan b12 (consBan b228 (nilBan _ _))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def v191 : List ℕ := [w15,w0,w1,w9,w2,w3]
def v192 : List ℕ := [w17,w0,w9,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b230 : Ban 30 4 v192 := viaSmall (by decide +kernel) (by decide)
def v193 : List ℕ := [w15,w5,w9,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b231 : Ban 30 4 v193 := viaSmall (by decide +kernel) (by decide)
def v194 : List ℕ := [w15,w1,w9,w2,w19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b232 : Ban 30 4 v194 := viaSmall (by decide +kernel) (by decide)
def v195 : List ℕ := [w15,w1,w9,w2,w20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b233 : Ban 30 4 v195 := viaSmall (by decide +kernel) (by decide)
def w80 : ℕ := 0x108421081fffc00
def v196 : List ℕ := [w0,w1,w80,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b234 : Ban 30 4 v196 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b229 : Ban 30 5 v191 := viaBranch (ws := [v118,v6,v192,v193,v194,v195,v196])
  (consBan b149 (consBan b8 (consBan b230 (consBan b231 (consBan b232 (consBan b233 (consBan b234 (nilBan _ _))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def v197 : List ℕ := [w15,w0,w1,w37,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b235 : Ban 30 5 v197 := viaPerm proj0 proj0 b209 (by decide +kernel) (by decide +kernel)
def v198 : List ℕ := [w15,w0,w1,w38,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b236 : Ban 30 5 v198 := viaPerm proj0 proj0 b215 (by decide +kernel) (by decide +kernel)
def v199 : List ℕ := [w15,w0,w1,w23,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b237 : Ban 30 5 v199 := viaPerm proj0 proj0 b222 (by decide +kernel) (by decide +kernel)
def v200 : List ℕ := [w15,w0,w1,w2,w24,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b238 : Ban 30 5 v200 := viaPerm proj0 proj0 b225 (by decide +kernel) (by decide +kernel)
def v201 : List ℕ := [w15,w0,w1,w2,w21,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b239 : Ban 30 5 v201 := viaPerm proj0 proj0 b229 (by decide +kernel) (by decide +kernel)
def v202 : List ℕ := [w15,w0,w1,w2,w35,w3]
def w81 : ℕ := 0x3ff
def v203 : List ℕ := [w81,w0,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b241 : Ban 30 4 v203 := viaSmall (by decide +kernel) (by decide)
def v204 : List ℕ := [w11,w15,w0,w35,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b242 : Ban 30 4 v204 := viaSmall (by decide +kernel) (by decide)
def w82 : ℕ := 0x3ff00000
def v205 : List ℕ := [w82,w15,w0,w1,w2]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b243 : Ban 30 4 v205 := viaSmall (by decide +kernel) (by decide)
def w83 : ℕ := 0x318c63180007fff
def v206 : List ℕ := [w15,w0,w1,w2,w83]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b244 : Ban 30 4 v206 := viaSmall (by decide +kernel) (by decide)
def v207 : List ℕ := [w15,w1,w2,w32,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b245 : Ban 30 4 v207 := viaSmall (by decide +kernel) (by decide)
def v208 : List ℕ := [w15,w1,w21,w35,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b246 : Ban 30 4 v208 := viaSmall (by decide +kernel) (by decide)
def v209 : List ℕ := [w15,w9,w2,w35,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b247 : Ban 30 4 v209 := viaSmall (by decide +kernel) (by decide)
def v210 : List ℕ := [w0,w6,w2,w35,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b248 : Ban 30 4 v210 := viaSmall (by decide +kernel) (by decide)
def v211 : List ℕ := [w0,w1,w23,w35,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b249 : Ban 30 4 v211 := viaSmall (by decide +kernel) (by decide)
def w84 : ℕ := 0x318c631bff07c00
def v212 : List ℕ := [w0,w1,w2,w84,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b250 : Ban 30 4 v212 := viaSmall (by decide +kernel) (by decide)
def w85 : ℕ := 0x39ce739fff07fff
def v213 : List ℕ := [w0,w1,w2,w85,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b251 : Ban 30 4 v213 := viaSmall (by decide +kernel) (by decide)
def v214 : List ℕ := [w0,w1,w24,w35,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b252 : Ban 30 4 v214 := viaSmall (by decide +kernel) (by decide)
def v215 : List ℕ := [w0,w22,w2,w35,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b253 : Ban 30 4 v215 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b240 : Ban 30 5 v202 := viaBranch (ws := [v203,v204,v205,v145,v163,v206,v207,v208,v209,v210,v211,v212,v213,v214,v215])
  (consBan b241 (consBan b242 (consBan b243 (consBan b180 (consBan b200 (consBan b244 (consBan b245 (consBan b246 (consBan b247 (consBan b248 (consBan b249 (consBan b250 (consBan b251 (consBan b252 (consBan b253 (nilBan _ _))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def v216 : List ℕ := [w15,w0,w1,w2,w39,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b254 : Ban 30 5 v216 := viaPerm proj12 proj11 b222 (by decide +kernel) (by decide +kernel)
def v217 : List ℕ := [w15,w0,w1,w2,w40,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b255 : Ban 30 5 v217 := viaPerm proj15 proj16 b222 (by decide +kernel) (by decide +kernel)
def v218 : List ℕ := [w12,w15,w1,w2,w19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b257 : Ban 30 4 v218 := viaSmall (by decide +kernel) (by decide)
def v219 : List ℕ := [w12,w0,w1,w2,w19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b258 : Ban 30 4 v219 := viaSmall (by decide +kernel) (by decide)
def v220 : List ℕ := [w17,w0,w1,w2,w19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b259 : Ban 30 4 v220 := viaSmall (by decide +kernel) (by decide)
def v221 : List ℕ := [w15,w5,w1,w2,w19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b260 : Ban 30 4 v221 := viaSmall (by decide +kernel) (by decide)
def w86 : ℕ := 0x4a5294a7ff003ff
def v222 : List ℕ := [w15,w0,w1,w2,w86]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b261 : Ban 30 4 v222 := viaSmall (by decide +kernel) (by decide)
def v223 : List ℕ := [w15,w1,w2,w21,w19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b262 : Ban 30 4 v223 := viaSmall (by decide +kernel) (by decide)
def v224 : List ℕ := [w15,w1,w2,w19,w20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b263 : Ban 30 4 v224 := viaSmall (by decide +kernel) (by decide)
def v225 : List ℕ := [w0,w1,w22,w2,w19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b264 : Ban 30 4 v225 := viaSmall (by decide +kernel) (by decide)
def v226 : List ℕ := [w0,w1,w2,w24,w19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b265 : Ban 30 4 v226 := viaSmall (by decide +kernel) (by decide)
def v227 : List ℕ := [w0,w1,w2,w19,w86]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b266 : Ban 30 4 v227 := viaSmall (by decide +kernel) (by decide)
def v228 : List ℕ := [w0,w1,w2,w86]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b267 : Ban 30 4 v228 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b256 : Ban 30 5 v26 := viaBranch (ws := [v218,v219,v147,v220,v156,v221,v222,v27,v194,v223,v224,v225,v226,v227,v228])
  (consBan b257 (consBan b258 (consBan b182 (consBan b259 (consBan b192 (consBan b260 (consBan b261 (consBan b32 (consBan b232 (consBan b262 (consBan b263 (consBan b264 (consBan b265 (consBan b266 (consBan b267 (nilBan _ _))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def v229 : List ℕ := [w15,w0,w1,w2,w19,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b268 : Ban 30 5 v229 := viaSmall (by decide +kernel) (by decide)
def v230 : List ℕ := [w15,w0,w1,w2,w3,w20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b269 : Ban 30 5 v230 := viaSmall (by decide +kernel) (by decide)
def v231 : List ℕ := [w15,w0,w1,w2,w3,w36]
def w87 : ℕ := 0xf801f
def v232 : List ℕ := [w87,w15,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b271 : Ban 30 4 v232 := viaSmall (by decide +kernel) (by decide)
def v233 : List ℕ := [w13,w15,w0,w2,w36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b272 : Ban 30 4 v233 := viaSmall (by decide +kernel) (by decide)
def v234 : List ℕ := [w15,w1,w2,w19,w36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b273 : Ban 30 4 v234 := viaSmall (by decide +kernel) (by decide)
def w88 : ℕ := 0x5294a52bff07c00
def v235 : List ℕ := [w15,w1,w2,w3,w88]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b274 : Ban 30 4 v235 := viaSmall (by decide +kernel) (by decide)
def v236 : List ℕ := [w15,w9,w2,w3,w36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b275 : Ban 30 4 v236 := viaSmall (by decide +kernel) (by decide)
def v237 : List ℕ := [w0,w6,w2,w3,w36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b276 : Ban 30 4 v237 := viaSmall (by decide +kernel) (by decide)
def w89 : ℕ := 0x5294a52bffffc00
def v238 : List ℕ := [w0,w1,w2,w3,w89]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b277 : Ban 30 4 v238 := viaSmall (by decide +kernel) (by decide)
def v239 : List ℕ := [w0,w1,w2,w20,w36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b278 : Ban 30 4 v239 := viaSmall (by decide +kernel) (by decide)
def v240 : List ℕ := [w0,w22,w2,w3,w36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b279 : Ban 30 4 v240 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b270 : Ban 30 5 v231 := viaBranch (ws := [v1,v232,v233,v23,v234,v235,v236,v237,v238,v50,v239,v240])
  (consBan b23 (consBan b271 (consBan b272 (consBan b28 (consBan b273 (consBan b274 (consBan b275 (consBan b276 (consBan b277 (consBan b57 (consBan b278 (consBan b279 (nilBan _ _)))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def v241 : List ℕ := [w15,w0,w1,w2,w3,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b280 : Ban 30 5 v241 := viaPerm proj0 proj0 b270 (by decide +kernel) (by decide +kernel)
def v242 : List ℕ := [w12,w15,w1,w2,w20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b282 : Ban 30 4 v242 := viaSmall (by decide +kernel) (by decide)
def v243 : List ℕ := [w12,w0,w1,w2,w20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b283 : Ban 30 4 v243 := viaSmall (by decide +kernel) (by decide)
def v244 : List ℕ := [w12,w1,w2,w20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b284 : Ban 30 4 v244 := viaSmall (by decide +kernel) (by decide)
def v245 : List ℕ := [w17,w0,w1,w2,w20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b285 : Ban 30 4 v245 := viaSmall (by decide +kernel) (by decide)
def v246 : List ℕ := [w15,w5,w1,w2,w20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b286 : Ban 30 4 v246 := viaSmall (by decide +kernel) (by decide)
def v247 : List ℕ := [w15,w1,w2,w21,w20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b287 : Ban 30 4 v247 := viaSmall (by decide +kernel) (by decide)
def v248 : List ℕ := [w0,w1,w2,w24,w20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b288 : Ban 30 4 v248 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b281 : Ban 30 5 v27 := viaBranch (ws := [v242,v243,v244,v140,v245,v157,v246,v26,v20,v195,v247,v224,v190,v248,v0,v34])
  (consBan b282 (consBan b283 (consBan b284 (consBan b174 (consBan b285 (consBan b193 (consBan b286 (consBan b31 (consBan b97 (consBan b233 (consBan b287 (consBan b263 (consBan b228 (consBan b288 (consBan b167 (consBan b39 (nilBan _ _)))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def v249 : List ℕ := [w28,w15,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b290 : Ban 30 4 v249 := viaSmall (by decide +kernel) (by decide)
def v250 : List ℕ := [w17,w15,w9,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b291 : Ban 30 4 v250 := viaSmall (by decide +kernel) (by decide)
def v251 : List ℕ := [w15,w1,w80,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b292 : Ban 30 4 v251 := viaSmall (by decide +kernel) (by decide)
def v252 : List ℕ := [w15,w1,w30,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b293 : Ban 30 4 v252 := viaSmall (by decide +kernel) (by decide)
def v253 : List ℕ := [w15,w1,w2,w33,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b294 : Ban 30 4 v253 := viaSmall (by decide +kernel) (by decide)
def v254 : List ℕ := [w1,w80,w9,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b295 : Ban 30 4 v254 := viaSmall (by decide +kernel) (by decide)
def v255 : List ℕ := [w1,w9,w2,w24,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b296 : Ban 30 4 v255 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b289 : Ban 30 5 v28 := viaBranch (ws := [v118,v7,v8,v249,v150,v250,v25,v193,v172,v178,v251,v252,v195,v207,v253,v209,v236,v53,v254,v255,v55])
  (consBan b149 (consBan b9 (consBan b10 (consBan b290 (consBan b185 (consBan b291 (consBan b30 (consBan b231 (consBan b210 (consBan b216 (consBan b292 (consBan b293 (consBan b233 (consBan b245 (consBan b294 (consBan b247 (consBan b275 (consBan b60 (consBan b295 (consBan b296 (consBan b62 (nilBan _ _))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b297 : Ban 30 5 v29 := viaPerm proj0 proj0 b289 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b298 : Ban 30 5 v30 := viaPerm proj17 proj17 b256 (by decide +kernel) (by decide +kernel)
def v256 : List ℕ := [w0,w1,w75,w2,w3]
def v257 : List ℕ := [w4,w1,w75,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b301 : Ban 30 4 v257 := viaSmall (by decide +kernel) (by decide)
def v258 : List ℕ := [w18,w1,w75,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b302 : Ban 30 4 v258 := viaSmall (by decide +kernel) (by decide)
def v259 : List ℕ := [w0,w26,w75,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b303 : Ban 30 4 v259 := viaSmall (by decide +kernel) (by decide)
def w90 : ℕ := 0x18c6318c00f801f
def v260 : List ℕ := [w0,w1,w90,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b304 : Ban 30 4 v260 := viaSmall (by decide +kernel) (by decide)
def v261 : List ℕ := [w0,w1,w75,w2,w40]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b305 : Ban 30 4 v261 := viaSmall (by decide +kernel) (by decide)
def v262 : List ℕ := [w0,w1,w75,w2,w36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b306 : Ban 30 4 v262 := viaSmall (by decide +kernel) (by decide)
def w91 : ℕ := 0x39ce739fe0fffff
def v263 : List ℕ := [w0,w1,w2,w91,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b307 : Ban 30 4 v263 := viaSmall (by decide +kernel) (by decide)
def v264 : List ℕ := [w0,w75,w2,w35,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b308 : Ban 30 4 v264 := viaSmall (by decide +kernel) (by decide)
def v265 : List ℕ := [w76,w1,w75,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b309 : Ban 30 4 v265 := viaSmall (by decide +kernel) (by decide)
def v266 : List ℕ := [w6,w1,w75,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b310 : Ban 30 4 v266 := viaSmall (by decide +kernel) (by decide)
def v267 : List ℕ := [w1,w75,w2,w21,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b311 : Ban 30 4 v267 := viaSmall (by decide +kernel) (by decide)
def v268 : List ℕ := [w1,w75,w2,w3,w20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b312 : Ban 30 4 v268 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b300 : Ban 30 5 v256 := viaBranch (ws := [v257,v39,v17,v18,v173,v258,v9,v174,v36,v259,v45,v260,v261,v262,v38,v47,v263,v62,v50,v264,v265,v266,v267,v268])
  (consBan b301 (consBan b46 (consBan b26 (consBan b95 (consBan b211 (consBan b302 (consBan b11 (consBan b212 (consBan b99 (consBan b303 (consBan b52 (consBan b304 (consBan b305 (consBan b306 (consBan b101 (consBan b54 (consBan b307 (consBan b108 (consBan b57 (consBan b308 (consBan b309 (consBan b310 (consBan b311 (consBan b312 (nilBan _ _)))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b299 : Ban 30 5 v31 := viaPerm proj9 proj9 b300 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b313 : Ban 30 5 v33 := viaPerm proj2 proj1 b300 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b147 : Ban 30 6 v20 := viaBranch (ws := [v117,v1,v122,v15,v123,v124,v21,v17,v134,v135,v136,v22,v153,v23,v154,v24,v170,v25,v171,v177,v184,v187,v191,v197,v198,v199,v200,v201,v202,v216,v217,v26,v229,v230,v231,v241,v27,v28,v29,v30,v10,v31,v32,v33,v34])
  (consBan b148 (consBan b3 (consBan b153 (consBan b17 (consBan b154 (consBan b155 (consBan b156 (consBan b19 (consBan b168 (consBan b169 (consBan b170 (consBan b177 (consBan b188 (consBan b189 (consBan b190 (consBan b197 (consBan b207 (consBan b208 (consBan b209 (consBan b215 (consBan b222 (consBan b225 (consBan b229 (consBan b235 (consBan b236 (consBan b237 (consBan b238 (consBan b239 (consBan b240 (consBan b254 (consBan b255 (consBan b256 (consBan b268 (consBan b269 (consBan b270 (consBan b280 (consBan b281 (consBan b289 (consBan b297 (consBan b298 (consBan b44 (consBan b299 (consBan b65 (consBan b313 (consBan b71 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit3 : Wide 30 6 v20 := viaSub (ws := [v0,v20])
  (consBan b2 (consBan b147 (nilBan _ _)))
  (by decide) (by decide +kernel)
def w92 : ℕ := 0xc30c30c30c30c300000003fffffff
def v269 : List ℕ := [w43,w44,w92,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b314 : Ban 60 7 v269 := viaCut proj18 petit3 (by decide) (by decide +kernel) (by decide +kernel)
def v270 : List ℕ := [w43,w44,w92,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b315 : Ban 60 7 v270 := viaCut proj18 petit3 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b316 : Ban 30 6 v35 := viaPerm proj8 proj8 b147 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit4 : Wide 30 6 v35 := viaSub (ws := [v0,v35])
  (consBan b2 (consBan b316 (nilBan _ _)))
  (by decide) (by decide +kernel)
def w93 : ℕ := 0xc30c30c30c30c3000fff00003ffff
def v271 : List ℕ := [w43,w44,w93,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b317 : Ban 60 7 v271 := viaCut proj18 petit4 (by decide) (by decide +kernel) (by decide +kernel)
def v272 : List ℕ := [w43,w44,w93,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b318 : Ban 60 7 v272 := viaCut proj18 petit4 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b319 : Ban 30 6 v9 := viaPerm proj4 proj3 b147 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit5 : Wide 30 6 v9 := viaSub (ws := [v0,v9])
  (consBan b2 (consBan b319 (nilBan _ _)))
  (by decide) (by decide +kernel)
def w94 : ℕ := 0xc30c30c30c30c3000fff03ffc003f
def v273 : List ℕ := [w43,w44,w94,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b320 : Ban 60 7 v273 := viaCut proj18 petit5 (by decide) (by decide +kernel) (by decide +kernel)
def v274 : List ℕ := [w43,w44,w94,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b321 : Ban 60 7 v274 := viaCut proj18 petit5 (by decide) (by decide +kernel) (by decide +kernel)
def w95 : ℕ := 0x104104104104104000000fc003ffc0
def v275 : List ℕ := [w43,w44,w65,w95,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b322 : Ban 60 7 v275 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def w96 : ℕ := 0x10410410410410403f00000003ffc0
def v276 : List ℕ := [w43,w44,w65,w96,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b323 : Ban 60 7 v276 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def w97 : ℕ := 0x10410410410410403f000fc0000000
def v277 : List ℕ := [w43,w44,w65,w97,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b324 : Ban 60 7 v277 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def w98 : ℕ := 0x10410410410410403f000fc0000fc0
def v278 : List ℕ := [w43,w44,w65,w98,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b325 : Ban 60 7 v278 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def w99 : ℕ := 0x10410410410410403f000fc003f000
def v279 : List ℕ := [w43,w44,w65,w99,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b326 : Ban 60 7 v279 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def w100 : ℕ := 0x14514514514514503f03ffc0ffffff
def v280 : List ℕ := [w43,w44,w65,w45,w100,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b327 : Ban 60 7 v280 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def w101 : ℕ := 0x18618618618618603ffc0fff03ffff
def v281 : List ℕ := [w43,w44,w65,w45,w101,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b328 : Ban 60 7 v281 := viaCut proj19 petit0 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit6 : Wide 30 4 v38 := viaSearch (by decide +kernel)
def w102 : ℕ := 0x1c71c71c71c71c703fffffffffffff
def v282 : List ℕ := [w42,w43,w65,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b330 : Ban 60 6 v282 := viaCut proj18 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v283 : List ℕ := [w42,w44,w65,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b331 : Ban 60 6 v283 := viaCut proj19 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v284 : List ℕ := [w42,w65,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b332 : Ban 60 6 v284 := viaCut proj18 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v285 : List ℕ := [w66,w43,w44,w65,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b333 : Ban 60 6 v285 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v286 : List ℕ := [w66,w43,w44,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b334 : Ban 60 6 v286 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v287 : List ℕ := [w66,w43,w44,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b335 : Ban 60 6 v287 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit7 : Wide 30 4 v48 := viaSearch (by decide +kernel)
def v288 : List ℕ := [w67,w43,w44,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b336 : Ban 60 6 v288 := viaCut proj21 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def w103 : ℕ := 0xffffc0000
def v289 : List ℕ := [w103,w43,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b337 : Ban 60 6 v289 := viaCut proj21 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v290 : List ℕ := [w68,w43,w44,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b338 : Ban 60 6 v290 := viaCut proj22 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def w104 : ℕ := 0x3ffff000000000
def v291 : List ℕ := [w104,w43,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b339 : Ban 60 6 v291 := viaCut proj22 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v292 : List ℕ := [w57,w44,w65,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b340 : Ban 60 6 v292 := viaCut proj18 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v293 : List ℕ := [w58,w44,w65,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b341 : Ban 60 6 v293 := viaCut proj18 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v294 : List ℕ := [w59,w44,w65,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b342 : Ban 60 6 v294 := viaCut proj18 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v295 : List ℕ := [w60,w43,w44,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b343 : Ban 60 6 v295 := viaCut proj18 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v296 : List ℕ := [w60,w43,w65,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b344 : Ban 60 6 v296 := viaCut proj18 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v297 : List ℕ := [w43,w61,w65,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b345 : Ban 60 6 v297 := viaCut proj19 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v298 : List ℕ := [w43,w62,w65,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b346 : Ban 60 6 v298 := viaCut proj19 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v299 : List ℕ := [w43,w63,w65,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b347 : Ban 60 6 v299 := viaCut proj19 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v300 : List ℕ := [w43,w64,w44,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b348 : Ban 60 6 v300 := viaCut proj19 petit6 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit8 : Wide 30 5 v191 := viaSub (ws := [v0,v20,v28,v38,v191])
  (consBan b93 (consBan b22 (consBan b289 (consBan b45 (consBan b229 (nilBan _ _))))))
  (by decide) (by decide +kernel)
def v301 : List ℕ := [w43,w44,w92,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b349 : Ban 60 6 v301 := viaCut proj18 petit8 (by decide) (by decide +kernel) (by decide +kernel)
def v302 : List ℕ := [w18,w0,w1,w9,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b350 : Ban 30 5 v41 := viaPerm proj8 proj8 b289 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b351 : Ban 30 5 v302 := viaPerm proj8 proj8 b229 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit9 : Wide 30 5 v302 := viaSub (ws := [v0,v35,v41,v38,v302])
  (consBan b93 (consBan b40 (consBan b350 (consBan b45 (consBan b351 (nilBan _ _))))))
  (by decide) (by decide +kernel)
def v303 : List ℕ := [w43,w44,w93,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b352 : Ban 60 6 v303 := viaCut proj18 petit9 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit10 : Wide 30 5 v9 := viaSub (ws := [v0,v9])
  (consBan b93 (consBan b41 (nilBan _ _)))
  (by decide) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b353 : Ban 60 6 v273 := viaCut proj18 petit10 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b354 : Ban 30 5 v42 := viaPerm proj4 proj3 b281 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit11 : Wide 30 5 v42 := viaSub (ws := [v42])
  (consBan b354 (nilBan _ _))
  (by decide) (by decide +kernel)
def v304 : List ℕ := [w43,w44,w94,w65,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b355 : Ban 60 6 v304 := viaCut proj18 petit11 (by decide) (by decide +kernel) (by decide +kernel)
def v305 : List ℕ := [w43,w44,w94,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b356 : Ban 60 6 v305 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v306 : List ℕ := [w43,w44,w94,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b357 : Ban 60 6 v306 := viaCut proj18 petit11 (by decide) (by decide +kernel) (by decide +kernel)
def v307 : List ℕ := [w43,w44,w65,w95,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b358 : Ban 60 6 v307 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v308 : List ℕ := [w43,w44,w65,w96,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b359 : Ban 60 6 v308 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b360 : Ban 60 6 v277 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit12 : Wide 30 5 v10 := viaSub (ws := [v0,v10])
  (consBan b93 (consBan b44 (nilBan _ _)))
  (by decide) (by decide +kernel)
def w105 : ℕ := 0x14514514514514503f03ffc0fc0fc0
def v309 : List ℕ := [w43,w44,w65,w45,w105,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b361 : Ban 60 6 v309 := viaCut proj18 petit12 (by decide) (by decide +kernel) (by decide +kernel)
def w106 : ℕ := 0x18618618618618603ffc0fff03f000
def v310 : List ℕ := [w43,w44,w65,w45,w106,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b362 : Ban 60 6 v310 := viaCut proj19 petit12 (by decide) (by decide +kernel) (by decide +kernel)
def v311 : List ℕ := [w14,w0,w1,w29,w2]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b364 : Ban 30 4 v311 := viaSmall (by decide +kernel) (by decide)
def v312 : List ℕ := [w18,w1,w29,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b365 : Ban 30 4 v312 := viaSmall (by decide +kernel) (by decide)
def v313 : List ℕ := [w0,w26,w29,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b366 : Ban 30 4 v313 := viaSmall (by decide +kernel) (by decide)
def w107 : ℕ := 0x18c6318c000001f
def v314 : List ℕ := [w0,w1,w107,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b367 : Ban 30 4 v314 := viaSmall (by decide +kernel) (by decide)
def v315 : List ℕ := [w0,w1,w29,w37,w2]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b368 : Ban 30 4 v315 := viaSmall (by decide +kernel) (by decide)
def v316 : List ℕ := [w0,w1,w29,w2,w40]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b369 : Ban 30 4 v316 := viaSmall (by decide +kernel) (by decide)
def v317 : List ℕ := [w0,w1,w29,w2,w19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b370 : Ban 30 4 v317 := viaSmall (by decide +kernel) (by decide)
def v318 : List ℕ := [w0,w1,w29,w2,w20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b371 : Ban 30 4 v318 := viaSmall (by decide +kernel) (by decide)
def v319 : List ℕ := [w0,w1,w29,w2,w36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b372 : Ban 30 4 v319 := viaSmall (by decide +kernel) (by decide)
def v320 : List ℕ := [w0,w1,w29,w2,w34]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b373 : Ban 30 4 v320 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b374 : Ban 30 4 v256 := viaSmall (by decide +kernel) (by decide)
def w108 : ℕ := 0x39ce739fe007fff
def v321 : List ℕ := [w0,w1,w2,w108,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b375 : Ban 30 4 v321 := viaSmall (by decide +kernel) (by decide)
def v322 : List ℕ := [w0,w29,w2,w35,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b376 : Ban 30 4 v322 := viaSmall (by decide +kernel) (by decide)
def v323 : List ℕ := [w1,w29,w2,w21,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b377 : Ban 30 4 v323 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b363 : Ban 30 5 v45 := viaBranch (ws := [v39,v17,v18,v311,v23,v20,v312,v174,v36,v313,v314,v315,v316,v317,v318,v319,v320,v256,v31,v47,v321,v50,v322,v323])
  (consBan b46 (consBan b26 (consBan b95 (consBan b364 (consBan b28 (consBan b97 (consBan b365 (consBan b212 (consBan b99 (consBan b366 (consBan b367 (consBan b368 (consBan b369 (consBan b370 (consBan b371 (consBan b372 (consBan b373 (consBan b374 (consBan b36 (consBan b54 (consBan b375 (consBan b57 (consBan b376 (consBan b377 (nilBan _ _)))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit13 : Wide 30 5 v45 := viaSub (ws := [v0,v45])
  (consBan b93 (consBan b363 (nilBan _ _)))
  (by decide) (by decide +kernel)
def w109 : ℕ := 0x1c71c71c71c71c7000000fffffffff
def v324 : List ℕ := [w43,w44,w65,w45,w109,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b378 : Ban 60 6 v324 := viaCut proj18 petit13 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b379 : Ban 30 5 v46 := viaPerm proj8 proj8 b363 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit14 : Wide 30 5 v46 := viaSub (ws := [v0,v46])
  (consBan b93 (consBan b379 (nilBan _ _)))
  (by decide) (by decide +kernel)
def w110 : ℕ := 0x1c71c71c71c71c703ffff00003ffff
def v325 : List ℕ := [w43,w44,w65,w45,w110,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b380 : Ban 60 6 v325 := viaCut proj18 petit14 (by decide) (by decide +kernel) (by decide +kernel)
def w111 : ℕ := 0x208208208208208fc0000000000000
def v326 : List ℕ := [w43,w44,w65,w45,w111,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b381 : Ban 60 6 v326 := viaCut proj21 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def w112 : ℕ := 0x3fff8000
def v327 : List ℕ := [w112,w0,w1,w2]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b383 : Ban 30 4 v327 := viaSmall (by decide +kernel) (by decide)
def v328 : List ℕ := [w112,w0,w1,w2,w32]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b384 : Ban 30 4 v328 := viaSmall (by decide +kernel) (by decide)
def v329 : List ℕ := [w112,w0,w1,w2,w3]
def w113 : ℕ := 0xf83ff
def v330 : List ℕ := [w113,w0,w1,w2,w3]
def v331 : List ℕ := [w113,w6,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b387 : Ban 30 3 v331 := viaSmall (by decide +kernel) (by decide)
def v332 : List ℕ := [w113,w1,w23,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b388 : Ban 30 3 v332 := viaSmall (by decide +kernel) (by decide)
def v333 : List ℕ := [w113,w1,w2,w19]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b389 : Ban 30 3 v333 := viaSmall (by decide +kernel) (by decide)
def v334 : List ℕ := [w113,w1,w2,w20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b390 : Ban 30 3 v334 := viaSmall (by decide +kernel) (by decide)
def v335 : List ℕ := [w113,w1,w21,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b391 : Ban 30 3 v335 := viaSmall (by decide +kernel) (by decide)
def v336 : List ℕ := [w113,w9,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b392 : Ban 30 3 v336 := viaSmall (by decide +kernel) (by decide)
def w114 : ℕ := 0x42108423fff83ff
def v337 : List ℕ := [w0,w1,w2,w114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b393 : Ban 30 3 v337 := viaSmall (by decide +kernel) (by decide)
def w115 : ℕ := 0x21084213e0fffff
def v338 : List ℕ := [w0,w1,w115,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b394 : Ban 30 3 v338 := viaSmall (by decide +kernel) (by decide)
def w116 : ℕ := 0x108421081ffffff
def v339 : List ℕ := [w0,w116,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b395 : Ban 30 3 v339 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b386 : Ban 30 4 v330 := viaBranch (ws := [v331,v332,v333,v334,v335,v336,v337,v338,v339])
  (consBan b387 (consBan b388 (consBan b389 (consBan b390 (consBan b391 (consBan b392 (consBan b393 (consBan b394 (consBan b395 (nilBan _ _))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b385 : Ban 30 4 v329 := viaPerm proj12 proj11 b386 (by decide +kernel) (by decide +kernel)
def v340 : List ℕ := [w0,w25,w2,w32,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b396 : Ban 30 4 v340 := viaSmall (by decide +kernel) (by decide)
def v341 : List ℕ := [w0,w1,w30,w32,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b397 : Ban 30 4 v341 := viaSmall (by decide +kernel) (by decide)
def v342 : List ℕ := [w0,w1,w37,w32,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b398 : Ban 30 4 v342 := viaSmall (by decide +kernel) (by decide)
def w117 : ℕ := 0x294a5297e0f83e0
def v343 : List ℕ := [w0,w1,w2,w117,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b399 : Ban 30 4 v343 := viaSmall (by decide +kernel) (by decide)
def w118 : ℕ := 0x39ce739c0007fff
def v344 : List ℕ := [w0,w1,w2,w118]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b400 : Ban 30 4 v344 := viaSmall (by decide +kernel) (by decide)
def v345 : List ℕ := [w0,w1,w2,w118,w32]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b401 : Ban 30 4 v345 := viaSmall (by decide +kernel) (by decide)
def v346 : List ℕ := [w0,w1,w2,w118,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b402 : Ban 30 4 v346 := viaSmall (by decide +kernel) (by decide)
def w119 : ℕ := 0x421084200000000
def v347 : List ℕ := [w0,w1,w2,w119,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b403 : Ban 30 4 v347 := viaSmall (by decide +kernel) (by decide)
def w120 : ℕ := 0x7bdef7bffffffff
def v348 : List ℕ := [w0,w1,w2,w3,w120]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b404 : Ban 30 4 v348 := viaSmall (by decide +kernel) (by decide)
def v349 : List ℕ := [w0,w1,w32,w3,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b405 : Ban 30 4 v349 := viaSmall (by decide +kernel) (by decide)
def v350 : List ℕ := [w0,w2,w117,w32,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b406 : Ban 30 4 v350 := viaSmall (by decide +kernel) (by decide)
def v351 : List ℕ := [w0,w2,w32,w3,w36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b407 : Ban 30 4 v351 := viaSmall (by decide +kernel) (by decide)
def v352 : List ℕ := [w1,w2,w84,w32,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b408 : Ban 30 4 v352 := viaSmall (by decide +kernel) (by decide)
def v353 : List ℕ := [w1,w2,w32,w3,w20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b409 : Ban 30 4 v353 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b382 : Ban 30 5 v48 := viaBranch (ws := [v327,v328,v329,v207,v340,v46,v341,v342,v343,v212,v344,v345,v346,v347,v348,v349,v350,v351,v352,v353])
  (consBan b383 (consBan b384 (consBan b385 (consBan b245 (consBan b396 (consBan b53 (consBan b397 (consBan b398 (consBan b399 (consBan b250 (consBan b400 (consBan b401 (consBan b402 (consBan b403 (consBan b404 (consBan b405 (consBan b406 (consBan b407 (consBan b408 (consBan b409 (nilBan _ _)))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit15 : Wide 30 5 v48 := viaSub (ws := [v0,v48])
  (consBan b93 (consBan b382 (nilBan _ _)))
  (by decide) (by decide +kernel)
def w121 : ℕ := 0x3cf3cf3cf3cf3cffffffffffffffff
def v354 : List ℕ := [w43,w44,w65,w45,w46,w121,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b410 : Ban 60 6 v354 := viaCut proj18 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def w122 : ℕ := 0x410410410410410fc0000000000000
def v355 : List ℕ := [w43,w44,w65,w45,w46,w122,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b411 : Ban 60 6 v355 := viaCut proj22 petit6 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b412 : Ban 30 5 v50 := viaPerm proj8 proj8 b382 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit16 : Wide 30 5 v50 := viaSub (ws := [v0,v50])
  (consBan b93 (consBan b412 (nilBan _ _)))
  (by decide) (by decide +kernel)
def w123 : ℕ := 0x5d75d75d75d75d7fffffffffffffff
def v356 : List ℕ := [w43,w44,w65,w45,w46,w47,w123]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b413 : Ban 60 6 v356 := viaCut proj18 petit16 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit17 : Wide 30 4 v239 := viaSearch (by decide +kernel)
def w124 : ℕ := 0x4d34d34d34d34d3ffffff03fffffff
def w125 : ℕ := 0x514514514514514fffffffc003ffc0
def v357 : List ℕ := [w42,w65,w45,w46,w124,w125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b415 : Ban 60 5 v357 := viaCut proj18 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def v358 : List ℕ := [w87,w0,w1,w2,w20]
def v359 : List ℕ := [w87,w1,w2,w20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b416 : Ban 30 4 v359 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b417 : Ban 30 4 v358 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit18 : Wide 30 4 v358 := viaSub (ws := [v359,v358])
  (consBan b416 (consBan b417 (nilBan _ _)))
  (by decide) (by decide +kernel)
def w126 : ℕ := 0xfff00003ffc0
def v360 : List ℕ := [w126,w43,w44,w45,w46,w124]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b418 : Ban 60 5 v360 := viaCut proj18 petit18 (by decide) (by decide +kernel) (by decide +kernel)
def w127 : ℕ := 0x3f00000003ffc0
def v361 : List ℕ := [w127,w43,w44,w65,w46,w125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b419 : Ban 60 5 v361 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit19 : Wide 30 4 v245 := viaSearch (by decide +kernel)
def w128 : ℕ := 0xc30c30c30c30c300000003ffc003f
def v362 : List ℕ := [w43,w44,w128,w45,w46,w124]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b420 : Ban 60 5 v362 := viaCut proj18 petit19 (by decide) (by decide +kernel) (by decide +kernel)
def w129 : ℕ := 0x410410410410410ffffff00003ffc0
def v363 : List ℕ := [w43,w44,w65,w45,w46,w129]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b421 : Ban 60 5 v363 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit20 : Wide 30 4 v50 := viaSearch (by decide +kernel)
def v364 : List ℕ := [w43,w44,w97,w46,w124,w125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b422 : Ban 60 5 v364 := viaCut proj20 petit20 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit21 : Wide 30 4 v0 := viaSearch (by decide +kernel)
def w130 : ℕ := 0x410410410410410fff000000000000
def v365 : List ℕ := [w43,w44,w45,w46,w130,w125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b423 : Ban 60 5 v365 := viaCut proj22 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def v366 : List ℕ := [w0,w9,w2,w20,w36]
def v367 : List ℕ := [w9,w2,w20,w36]
def v368 : List ℕ := [w0,w35,w36,w41]
def w131 : ℕ := 0x10842108000001f
def v369 : List ℕ := [w0,w131,w35,w36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b426 : Ban 30 3 v369 := viaSmall (by decide +kernel) (by decide)
def w132 : ℕ := 0x1084210bff07c1f
def v370 : List ℕ := [w0,w132,w35,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b427 : Ban 30 3 v370 := viaSmall (by decide +kernel) (by decide)
def v371 : List ℕ := [w0,w132,w36,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b428 : Ban 30 3 v371 := viaSmall (by decide +kernel) (by decide)
def v372 : List ℕ := [w0,w132,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b429 : Ban 30 3 v372 := viaSmall (by decide +kernel) (by decide)
def w133 : ℕ := 0x2108421000003e0
def v373 : List ℕ := [w0,w133,w35,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b430 : Ban 30 3 v373 := viaSmall (by decide +kernel) (by decide)
def w134 : ℕ := 0x21084213ff07fe0
def v374 : List ℕ := [w0,w134,w35,w36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b431 : Ban 30 3 v374 := viaSmall (by decide +kernel) (by decide)
def v375 : List ℕ := [w0,w134,w36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b432 : Ban 30 3 v375 := viaSmall (by decide +kernel) (by decide)
def v376 : List ℕ := [w0,w134,w36,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b433 : Ban 30 3 v376 := viaSmall (by decide +kernel) (by decide)
def v377 : List ℕ := [w0,w84,w36,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b434 : Ban 30 3 v377 := viaSmall (by decide +kernel) (by decide)
def w135 : ℕ := 0x42108423ffffc00
def v378 : List ℕ := [w0,w35,w135]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b435 : Ban 30 3 v378 := viaSmall (by decide +kernel) (by decide)
def v379 : List ℕ := [w0,w35,w135,w36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b436 : Ban 30 3 v379 := viaSmall (by decide +kernel) (by decide)
def v380 : List ℕ := [w0,w35,w135,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b437 : Ban 30 3 v380 := viaSmall (by decide +kernel) (by decide)
def v381 : List ℕ := [w0,w35,w88,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b438 : Ban 30 3 v381 := viaSmall (by decide +kernel) (by decide)
def w136 : ℕ := 0x6318c633ff07c00
def v382 : List ℕ := [w0,w35,w36,w136]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b439 : Ban 30 3 v382 := viaSmall (by decide +kernel) (by decide)
def w137 : ℕ := 0x6b5ad6b7fffffff
def v383 : List ℕ := [w0,w35,w36,w137]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b440 : Ban 30 3 v383 := viaSmall (by decide +kernel) (by decide)
def v384 : List ℕ := [w0,w35,w34,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b441 : Ban 30 3 v384 := viaSmall (by decide +kernel) (by decide)
def v385 : List ℕ := [w0,w32,w36,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b442 : Ban 30 3 v385 := viaSmall (by decide +kernel) (by decide)
def w138 : ℕ := 0x4210842000f8000
def v386 : List ℕ := [w0,w138,w36,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b443 : Ban 30 3 v386 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b425 : Ban 30 4 v368 := viaBranch (ws := [v369,v370,v371,v372,v373,v374,v375,v376,v377,v378,v379,v380,v381,v382,v383,v384,v385,v386])
  (consBan b426 (consBan b427 (consBan b428 (consBan b429 (consBan b430 (consBan b431 (consBan b432 (consBan b433 (consBan b434 (consBan b435 (consBan b436 (consBan b437 (consBan b438 (consBan b439 (consBan b440 (consBan b441 (consBan b442 (consBan b443 (nilBan _ _)))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b424 : Ban 30 4 v367 := viaPerm proj2 proj1 b425 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b444 : Ban 30 4 v366 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit22 : Wide 30 4 v366 := viaSub (ws := [v367,v366])
  (consBan b424 (consBan b444 (nilBan _ _)))
  (by decide) (by decide +kernel)
def v387 : List ℕ := [w43,w44,w102,w46,w124,w125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b445 : Ban 60 5 v387 := viaCut proj18 petit22 (by decide) (by decide +kernel) (by decide +kernel)
def v388 : List ℕ := [w0,w1,w2,w19,w36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit23 : Wide 30 4 v388 := viaSearch (by decide +kernel)
def w139 : ℕ := 0x451451451451451fff03f000fc0fc0
def v389 : List ℕ := [w43,w65,w45,w46,w139,w125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b446 : Ban 60 5 v389 := viaCut proj18 petit23 (by decide) (by decide +kernel) (by decide +kernel)
def v390 : List ℕ := [w43,w65,w101,w46,w124,w125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b447 : Ban 60 5 v390 := viaCut proj18 petit22 (by decide) (by decide +kernel) (by decide +kernel)
def w140 : ℕ := 0x492492492492492ffffc003f03f000
def v391 : List ℕ := [w44,w65,w45,w46,w140,w125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b448 : Ban 60 5 v391 := viaCut proj19 petit23 (by decide) (by decide +kernel) (by decide +kernel)
def v392 : List ℕ := [w44,w65,w100,w46,w124,w125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b449 : Ban 60 5 v392 := viaCut proj19 petit22 (by decide) (by decide +kernel) (by decide +kernel)
def v393 : List ℕ := [w43,w44,w65,w45,w46,w124,w125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b414 : Ban 60 6 v393 := viaBranch (ws := [v357,v360,v361,v362,v363,v364,v365,v387,v389,v390,v391,v392])
  (consBan b415 (consBan b418 (consBan b419 (consBan b420 (consBan b421 (consBan b422 (consBan b423 (consBan b445 (consBan b446 (consBan b447 (consBan b448 (consBan b449 (nilBan _ _)))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def proj23 : Projection 60 60 := pick [0,1,3,4,2,5,18,19,21,22,20,23,24,25,27,28,26,29,36,37,39,40,38,41,42,43,45,46,44,47,54,55,57,58,56,59,6,7,9,10,8,11,12,13,15,16,14,17,30,31,33,34,32,35,48,49,51,52,50,53] rfl (by decide +kernel) (by decide)
def proj24 : Projection 60 60 := pick [0,1,4,2,3,5,36,37,40,38,39,41,42,43,46,44,45,47,6,7,10,8,9,11,12,13,16,14,15,17,48,49,52,50,51,53,18,19,22,20,21,23,24,25,28,26,27,29,54,55,58,56,57,59,30,31,34,32,33,35] rfl (by decide +kernel) (by decide)
def w141 : ℕ := 0x30c30c30c30c30cfff000fffffffc0
def v394 : List ℕ := [w43,w44,w65,w102,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b450 : Ban 60 6 v394 := viaPerm proj23 proj24 b414 (by decide +kernel) (by decide +kernel)
def proj25 : Projection 60 60 := pick [0,1,4,3,2,5,36,37,40,39,38,41,42,43,46,45,44,47,18,19,22,21,20,23,24,25,28,27,26,29,54,55,58,57,56,59,6,7,10,9,8,11,12,13,16,15,14,17,48,49,52,51,50,53,30,31,34,33,32,35] rfl (by decide +kernel) (by decide)
def v395 : List ℕ := [w43,w44,w65,w102,w46,w47,w125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b451 : Ban 60 6 v395 := viaPerm proj25 proj25 b414 (by decide +kernel) (by decide +kernel)
def v396 : List ℕ := [w43,w44,w97,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b452 : Ban 60 6 v396 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v397 : List ℕ := [w43,w44,w97,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b453 : Ban 60 6 v397 := viaCut proj20 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def w142 : ℕ := 0x208208208208208fc0000fc0000000
def v398 : List ℕ := [w43,w44,w45,w102,w142,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b454 : Ban 60 6 v398 := viaCut proj21 petit7 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit24 : Wide 30 4 v54 := viaSearch (by decide +kernel)
def w143 : ℕ := 0x2cb2cb2cb2cb2cbfc0ffffffffffff
def v399 : List ℕ := [w42,w45,w102,w46,w143,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b456 : Ban 60 5 v399 := viaCut proj18 petit24 (by decide) (by decide +kernel) (by decide +kernel)
def w144 : ℕ := 0xfc003ffc0
def v400 : List ℕ := [w144,w43,w44,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b457 : Ban 60 5 v400 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v401 : List ℕ := [w103,w43,w44,w45,w143,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b458 : Ban 60 5 v401 := viaCut proj21 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def w145 : ℕ := 0x842108400fffff
def v402 : List ℕ := [w0,w145,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit25 : Wide 30 4 v402 := viaSearch (by decide +kernel)
def w146 : ℕ := 0xc30c30c30c30c3000ffffffffffff
def v403 : List ℕ := [w43,w44,w146,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b459 : Ban 60 5 v403 := viaCut proj18 petit25 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit26 : Wide 30 3 v0 := viaSearch (by decide +kernel)
def w147 : ℕ := 0x10410410410410403f000000000000
def v404 : List ℕ := [w43,w44,w147,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b460 : Ban 60 5 v404 := viaCut proj20 petit26 (by decide) (by decide +kernel) (by decide +kernel)
def v405 : List ℕ := [w0,w1,w30,w21,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit27 : Wide 30 4 v405 := viaSearch (by decide +kernel)
def v406 : List ℕ := [w43,w44,w45,w110,w143,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b461 : Ban 60 5 v406 := viaCut proj18 petit27 (by decide) (by decide +kernel) (by decide +kernel)
def v407 : List ℕ := [w43,w44,w45,w111,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b462 : Ban 60 5 v407 := viaCut proj21 petit26 (by decide) (by decide +kernel) (by decide +kernel)
def v408 : List ℕ := [w43,w44,w45,w46,w121,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b463 : Ban 60 5 v408 := viaCut proj18 petit7 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit28 : Wide 30 4 v341 := viaSearch (by decide +kernel)
def w148 : ℕ := 0x2cb2cb2cb2cb2cbfc0fff03ffc003f
def v409 : List ℕ := [w43,w44,w102,w46,w148,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b464 : Ban 60 5 v409 := viaCut proj21 petit28 (by decide) (by decide +kernel) (by decide +kernel)
def v410 : List ℕ := [w0,w9,w21,w35,w3]
def v411 : List ℕ := [w9,w21,w35,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b465 : Ban 30 4 v411 := viaPerm proj12 proj11 b425 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b466 : Ban 30 4 v410 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit29 : Wide 30 4 v410 := viaSub (ws := [v411,v410])
  (consBan b465 (consBan b466 (nilBan _ _)))
  (by decide) (by decide +kernel)
def v412 : List ℕ := [w43,w44,w102,w143,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b467 : Ban 60 5 v412 := viaCut proj18 petit29 (by decide) (by decide +kernel) (by decide +kernel)
def v413 : List ℕ := [w43,w44,w45,w102,w46,w143,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b455 : Ban 60 6 v413 := viaBranch (ws := [v399,v400,v401,v403,v404,v406,v407,v408,v409,v412])
  (consBan b456 (consBan b457 (consBan b458 (consBan b459 (consBan b460 (consBan b461 (consBan b462 (consBan b463 (consBan b464 (consBan b467 (nilBan _ _)))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def v414 : List ℕ := [w43,w44,w45,w102,w46,w130,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b468 : Ban 60 6 v414 := viaCut proj22 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def proj26 : Projection 60 60 := pick [0,1,2,4,3,5,6,7,8,10,9,11,12,13,14,16,15,17,36,37,38,40,39,41,42,43,44,46,45,47,48,49,50,52,51,53,18,19,20,22,21,23,24,25,26,28,27,29,30,31,32,34,33,35,54,55,56,58,57,59] rfl (by decide +kernel) (by decide)
def v415 : List ℕ := [w43,w44,w45,w102,w46,w47,w124]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b469 : Ban 60 6 v415 := viaPerm proj26 proj26 b455 (by decide +kernel) (by decide +kernel)
def v416 : List ℕ := [w43,w65,w45,w105,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b470 : Ban 60 6 v416 := viaCut proj20 petit11 (by decide) (by decide +kernel) (by decide +kernel)
def v417 : List ℕ := [w43,w65,w45,w105,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b471 : Ban 60 6 v417 := viaCut proj18 petit12 (by decide) (by decide +kernel) (by decide +kernel)
def v418 : List ℕ := [w43,w65,w45,w101,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b472 : Ban 60 6 v418 := viaCut proj18 petit2 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit30 : Wide 30 4 v63 := viaSearch (by decide +kernel)
def w149 : ℕ := 0x3f00000003f
def w150 : ℕ := 0x451451451451451ffffff000fc0fff
def w151 : ℕ := 0x555555555555555fffffffc0ffffff
def v419 : List ℕ := [w149,w44,w45,w46,w150,w151]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b474 : Ban 60 5 v419 := viaCut proj18 petit30 (by decide) (by decide +kernel) (by decide +kernel)
def w152 : ℕ := 0xfc000000003f
def w153 : ℕ := 0x492492492492492ffffff03f03f03f
def v420 : List ℕ := [w152,w43,w45,w46,w153,w151]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b475 : Ban 60 5 v420 := viaCut proj19 petit20 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit31 : Wide 30 4 v34 := viaSearch (by decide +kernel)
def w154 : ℕ := 0xfc000003f03f
def v421 : List ℕ := [w154,w43,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b476 : Ban 60 5 v421 := viaCut proj19 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def w155 : ℕ := 0x3f000000000fc0
def v422 : List ℕ := [w155,w43,w44,w46,w153,w151]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b477 : Ban 60 5 v422 := viaCut proj20 petit17 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit32 : Wide 30 4 v174 := viaSearch (by decide +kernel)
def w156 : ℕ := 0x145145145145145000000fc0fc0fc0
def v423 : List ℕ := [w43,w44,w45,w156,w46,w150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b478 : Ban 60 5 v423 := viaCut proj18 petit32 (by decide) (by decide +kernel) (by decide +kernel)
def w157 : ℕ := 0x410410410410410ffffff00000003f
def v424 : List ℕ := [w43,w44,w45,w46,w157,w151]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b479 : Ban 60 5 v424 := viaCut proj18 petit30 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit33 : Wide 30 4 v12 := viaSearch (by decide +kernel)
def w158 : ℕ := 0x410410410410410ffffff00003f03f
def v425 : List ℕ := [w43,w44,w45,w46,w158,w150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b480 : Ban 60 5 v425 := viaCut proj18 petit33 (by decide) (by decide +kernel) (by decide +kernel)
def w159 : ℕ := 0x4a5294a7e0f83e0
def v426 : List ℕ := [w0,w2,w3,w159,w34]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit34 : Wide 30 4 v426 := viaSearch (by decide +kernel)
def w160 : ℕ := 0x451451451451451fc0fff000fc003f
def v427 : List ℕ := [w43,w44,w46,w160,w153,w151]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b481 : Ban 60 5 v427 := viaCut proj19 petit34 (by decide) (by decide +kernel) (by decide +kernel)
def v428 : List ℕ := [w0,w2,w159,w20,w36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit35 : Wide 30 4 v428 := viaSearch (by decide +kernel)
def v429 : List ℕ := [w43,w45,w46,w139,w153,w151]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b482 : Ban 60 5 v429 := viaCut proj20 petit35 (by decide) (by decide +kernel) (by decide +kernel)
def v430 : List ℕ := [w1,w2,w3,w20,w88]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit36 : Wide 30 4 v430 := viaSearch (by decide +kernel)
def w161 : ℕ := 0x555555555555555fff03ffc0fc0fc0
def v431 : List ℕ := [w43,w45,w46,w150,w153,w161]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b483 : Ban 60 5 v431 := viaCut proj18 petit36 (by decide) (by decide +kernel) (by decide +kernel)
def v432 : List ℕ := [w9,w2,w3,w20,w36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b484 : Ban 30 4 v432 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit37 : Wide 30 4 v432 := viaSub (ws := [v367,v432])
  (consBan b424 (consBan b484 (nilBan _ _)))
  (by decide) (by decide +kernel)
def v433 : List ℕ := [w43,w101,w46,w150,w153,w151]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b485 : Ban 60 5 v433 := viaCut proj18 petit37 (by decide) (by decide +kernel) (by decide +kernel)
def w162 : ℕ := 0x514514514514514ffffc0fc003f000
def v434 : List ℕ := [w44,w45,w46,w150,w153,w162]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b486 : Ban 60 5 v434 := viaCut proj19 petit36 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit38 : Wide 30 4 v367 := viaSub (ws := [v367])
  (consBan b424 (nilBan _ _))
  (by decide) (by decide +kernel)
def v435 : List ℕ := [w65,w45,w46,w150,w153,w151]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b487 : Ban 60 5 v435 := viaCut proj20 petit38 (by decide) (by decide +kernel) (by decide +kernel)
def v436 : List ℕ := [w43,w44,w45,w46,w150,w153,w151]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b473 : Ban 60 6 v436 := viaBranch (ws := [v419,v420,v421,v422,v423,v424,v425,v427,v429,v431,v433,v434,v435])
  (consBan b474 (consBan b475 (consBan b476 (consBan b477 (consBan b478 (consBan b479 (consBan b480 (consBan b481 (consBan b482 (consBan b483 (consBan b485 (consBan b486 (consBan b487 (nilBan _ _))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def proj27 : Projection 60 60 := pick [18,21,20,22,19,23,6,9,8,10,7,11,30,33,32,34,31,35,36,39,38,40,37,41,54,57,56,58,55,59,48,51,50,52,49,53,0,3,2,4,1,5,24,27,26,28,25,29,12,15,14,16,13,17,42,45,44,46,43,47] rfl (by decide +kernel) (by decide)
def proj28 : Projection 60 60 := pick [36,40,38,37,39,41,6,10,8,7,9,11,48,52,50,49,51,53,0,4,2,1,3,5,42,46,44,43,45,47,12,16,14,13,15,17,18,22,20,19,21,23,54,58,56,55,57,59,30,34,32,31,33,35,24,28,26,25,27,29] rfl (by decide +kernel) (by decide)
def w163 : ℕ := 0x28a28a28a28a28afc0fc0ffffff03f
def v437 : List ℕ := [w43,w65,w45,w102,w46,w163,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b488 : Ban 60 6 v437 := viaPerm proj27 proj28 b473 (by decide +kernel) (by decide +kernel)
def proj29 : Projection 60 60 := pick [36,40,38,39,37,41,6,10,8,9,7,11,48,52,50,51,49,53,18,22,20,21,19,23,54,58,56,57,55,59,30,34,32,33,31,35,0,4,2,3,1,5,42,46,44,45,43,47,12,16,14,15,13,17,24,28,26,27,25,29] rfl (by decide +kernel) (by decide)
def v438 : List ℕ := [w43,w65,w45,w102,w46,w47,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b489 : Ban 60 6 v438 := viaPerm proj29 proj29 b473 (by decide +kernel) (by decide +kernel)
def v439 : List ℕ := [w64,w44,w65,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b490 : Ban 60 6 v439 := viaCut proj19 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v440 : List ℕ := [w44,w65,w45,w100,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b491 : Ban 60 6 v440 := viaCut proj19 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v441 : List ℕ := [w0,w6,w1,w9,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b492 : Ban 30 5 v53 := viaPerm proj11 proj12 b281 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b493 : Ban 30 5 v441 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit39 : Wide 30 5 v441 := viaSub (ws := [v0,v10,v38,v53,v441])
  (consBan b93 (consBan b44 (consBan b45 (consBan b492 (consBan b493 (nilBan _ _))))))
  (by decide) (by decide +kernel)
def v442 : List ℕ := [w44,w65,w45,w106,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b494 : Ban 60 6 v442 := viaCut proj19 petit39 (by decide) (by decide +kernel) (by decide +kernel)
def v443 : List ℕ := [w44,w65,w45,w106,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b495 : Ban 60 6 v443 := viaCut proj19 petit12 (by decide) (by decide +kernel) (by decide +kernel)
def proj30 : Projection 60 60 := pick [25,27,26,28,24,29,13,15,14,16,12,17,31,33,32,34,30,35,43,45,44,46,42,47,55,57,56,58,54,59,49,51,50,52,48,53,1,3,2,4,0,5,19,21,20,22,18,23,7,9,8,10,6,11,37,39,38,40,36,41] rfl (by decide +kernel) (by decide)
def proj31 : Projection 60 60 := pick [40,36,38,37,39,41,52,48,50,49,51,53,10,6,8,7,9,11,46,42,44,43,45,47,4,0,2,1,3,5,16,12,14,13,15,17,58,54,56,55,57,59,22,18,20,19,21,23,34,30,32,31,33,35,28,24,26,25,27,29] rfl (by decide +kernel) (by decide)
def w164 : ℕ := 0x249249249249249fc003fffffc0fff
def v444 : List ℕ := [w44,w65,w45,w102,w46,w164,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b496 : Ban 60 6 v444 := viaPerm proj30 proj31 b473 (by decide +kernel) (by decide +kernel)
def proj32 : Projection 60 60 := pick [43,46,44,45,42,47,13,16,14,15,12,17,49,52,50,51,48,53,25,28,26,27,24,29,55,58,56,57,54,59,31,34,32,33,30,35,1,4,2,3,0,5,37,40,38,39,36,41,7,10,8,9,6,11,19,22,20,21,18,23] rfl (by decide +kernel) (by decide)
def proj33 : Projection 60 60 := pick [40,36,38,39,37,41,52,48,50,51,49,53,10,6,8,9,7,11,58,54,56,57,55,59,22,18,20,21,19,23,34,30,32,33,31,35,46,42,44,45,43,47,4,0,2,3,1,5,16,12,14,15,13,17,28,24,26,27,25,29] rfl (by decide +kernel) (by decide)
def v445 : List ℕ := [w44,w65,w45,w102,w46,w47,w150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b497 : Ban 60 6 v445 := viaPerm proj32 proj33 b473 (by decide +kernel) (by decide +kernel)
def v446 : List ℕ := [w43,w44,w65,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b329 : Ban 60 7 v446 := viaBranch (ws := [v282,v283,v284,v285,v286,v287,v288,v289,v290,v291,v292,v293,v294,v295,v296,v297,v298,v299,v300,v301,v303,v273,v304,v305,v306,v307,v308,v277,v309,v310,v324,v325,v326,v354,v355,v356,v394,v395,v396,v397,v398,v413,v414,v415,v416,v417,v418,v437,v438,v439,v440,v442,v443,v444,v445])
  (consBan b330 (consBan b331 (consBan b332 (consBan b333 (consBan b334 (consBan b335 (consBan b336 (consBan b337 (consBan b338 (consBan b339 (consBan b340 (consBan b341 (consBan b342 (consBan b343 (consBan b344 (consBan b345 (consBan b346 (consBan b347 (consBan b348 (consBan b349 (consBan b352 (consBan b353 (consBan b355 (consBan b356 (consBan b357 (consBan b358 (consBan b359 (consBan b360 (consBan b361 (consBan b362 (consBan b378 (consBan b380 (consBan b381 (consBan b410 (consBan b411 (consBan b413 (consBan b450 (consBan b451 (consBan b452 (consBan b453 (consBan b454 (consBan b455 (consBan b468 (consBan b469 (consBan b470 (consBan b471 (consBan b472 (consBan b488 (consBan b489 (consBan b490 (consBan b491 (consBan b494 (consBan b495 (consBan b496 (consBan b497 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def w165 : ℕ := 0x208208208208208000000ffffc0000
def v447 : List ℕ := [w43,w44,w65,w45,w165,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b498 : Ban 60 7 v447 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def w166 : ℕ := 0x208208208208208fc000003ffc0000
def v448 : List ℕ := [w43,w44,w65,w45,w166,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b499 : Ban 60 7 v448 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v449 : List ℕ := [w43,w44,w65,w45,w142,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b500 : Ban 60 7 v449 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def w167 : ℕ := 0x208208208208208fc0000fc0fc0000
def v450 : List ℕ := [w43,w44,w65,w45,w167,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b501 : Ban 60 7 v450 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def w168 : ℕ := 0x208208208208208fc0000fff000000
def v451 : List ℕ := [w43,w44,w65,w45,w168,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b502 : Ban 60 7 v451 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v452 : List ℕ := [w43,w44,w65,w45,w46,w164,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b503 : Ban 60 7 v452 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def v453 : List ℕ := [w43,w44,w65,w45,w46,w163,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b504 : Ban 60 7 v453 := viaCut proj19 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def proj34 : Projection 60 60 := pick [0,1,3,2,4,5,18,19,21,20,22,23,24,25,27,26,28,29,6,7,9,8,10,11,12,13,15,14,16,17,30,31,33,32,34,35,36,37,39,38,40,41,42,43,45,44,46,47,54,55,57,56,58,59,48,49,51,50,52,53] rfl (by decide +kernel) (by decide)
def v454 : List ℕ := [w43,w44,w65,w45,w46,w143,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b505 : Ban 60 7 v454 := viaPerm proj34 proj34 b329 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit40 : Wide 30 4 v59 := viaSearch (by decide +kernel)
def v455 : List ℕ := [w42,w43,w65,w45,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b507 : Ban 60 6 v455 := viaCut proj18 petit40 (by decide) (by decide +kernel) (by decide +kernel)
def v456 : List ℕ := [w42,w44,w65,w45,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b508 : Ban 60 6 v456 := viaCut proj19 petit40 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit41 : Wide 30 5 v59 := viaSub (ws := [v0,v59])
  (consBan b93 (consBan b67 (nilBan _ _)))
  (by decide) (by decide +kernel)
def v457 : List ℕ := [w42,w65,w45,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b509 : Ban 60 6 v457 := viaCut proj18 petit41 (by decide) (by decide +kernel) (by decide +kernel)
def v458 : List ℕ := [w66,w43,w44,w45,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b510 : Ban 60 6 v458 := viaCut proj20 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def w169 : ℕ := 0xfc0fc0
def v459 : List ℕ := [w169,w43,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b511 : Ban 60 6 v459 := viaCut proj18 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def w170 : ℕ := 0x3f03f000
def v460 : List ℕ := [w170,w43,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b512 : Ban 60 6 v460 := viaCut proj19 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def v461 : List ℕ := [w67,w43,w44,w45,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b513 : Ban 60 6 v461 := viaCut proj21 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def v462 : List ℕ := [w81,w12,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b515 : Ban 30 4 v462 := viaSmall (by decide +kernel) (by decide)
def v463 : List ℕ := [w81,w73,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b516 : Ban 30 4 v463 := viaSmall (by decide +kernel) (by decide)
def v464 : List ℕ := [w81,w18,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b517 : Ban 30 4 v464 := viaSmall (by decide +kernel) (by decide)
def v465 : List ℕ := [w81,w5,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b518 : Ban 30 4 v465 := viaSmall (by decide +kernel) (by decide)
def v466 : List ℕ := [w81,w0,w6,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b519 : Ban 30 4 v466 := viaSmall (by decide +kernel) (by decide)
def v467 : List ℕ := [w81,w0,w1,w23,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b520 : Ban 30 4 v467 := viaSmall (by decide +kernel) (by decide)
def v468 : List ℕ := [w81,w0,w1,w2,w114]
def v469 : List ℕ := [w81,w1,w21,w114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b522 : Ban 30 3 v469 := viaSmall (by decide +kernel) (by decide)
def v470 : List ℕ := [w81,w9,w2,w114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b523 : Ban 30 3 v470 := viaSmall (by decide +kernel) (by decide)
def v471 : List ℕ := [w73,w1,w2,w114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b524 : Ban 30 3 v471 := viaSmall (by decide +kernel) (by decide)
def v472 : List ℕ := [w0,w6,w2,w114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b525 : Ban 30 3 v472 := viaSmall (by decide +kernel) (by decide)
def v473 : List ℕ := [w0,w1,w23,w114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b526 : Ban 30 3 v473 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b527 : Ban 30 3 v0 := viaSmall (by decide +kernel) (by decide)
def v474 : List ℕ := [w0,w1,w8,w114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b528 : Ban 30 3 v474 := viaSmall (by decide +kernel) (by decide)
def w171 : ℕ := 0x108421081f07fff
def v475 : List ℕ := [w0,w171,w2,w114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b529 : Ban 30 3 v475 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b521 : Ban 30 4 v468 := viaBranch (ws := [v469,v470,v471,v472,v473,v0,v474,v475])
  (consBan b522 (consBan b523 (consBan b524 (consBan b525 (consBan b526 (consBan b527 (consBan b528 (consBan b529 (nilBan _ _)))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def v476 : List ℕ := [w81,w0,w1,w8,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b530 : Ban 30 4 v476 := viaSmall (by decide +kernel) (by decide)
def v477 : List ℕ := [w81,w0,w1,w21,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b531 : Ban 30 4 v477 := viaSmall (by decide +kernel) (by decide)
def v478 : List ℕ := [w81,w0,w171,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b532 : Ban 30 4 v478 := viaSmall (by decide +kernel) (by decide)
def v479 : List ℕ := [w81,w0,w9,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b533 : Ban 30 4 v479 := viaSmall (by decide +kernel) (by decide)
def v480 : List ℕ := [w81,w1,w9,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b534 : Ban 30 4 v480 := viaSmall (by decide +kernel) (by decide)
def v481 : List ℕ := [w81,w1,w2,w21,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b535 : Ban 30 4 v481 := viaSmall (by decide +kernel) (by decide)
def v482 : List ℕ := [w81,w1,w2,w19,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b536 : Ban 30 4 v482 := viaSmall (by decide +kernel) (by decide)
def v483 : List ℕ := [w81,w1,w21,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b537 : Ban 30 4 v483 := viaSmall (by decide +kernel) (by decide)
def v484 : List ℕ := [w81,w9,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b538 : Ban 30 4 v484 := viaSmall (by decide +kernel) (by decide)
def v485 : List ℕ := [w73,w0,w1,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b539 : Ban 30 4 v485 := viaSmall (by decide +kernel) (by decide)
def v486 : List ℕ := [w0,w1,w171,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b540 : Ban 30 4 v486 := viaSmall (by decide +kernel) (by decide)
def v487 : List ℕ := [w0,w1,w2,w3,w114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b541 : Ban 30 4 v487 := viaSmall (by decide +kernel) (by decide)
def v488 : List ℕ := [w113,w1,w2,w114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b543 : Ban 30 3 v488 := viaSmall (by decide +kernel) (by decide)
def v489 : List ℕ := [w18,w1,w2,w114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b544 : Ban 30 3 v489 := viaSmall (by decide +kernel) (by decide)
def v490 : List ℕ := [w5,w1,w2,w114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b545 : Ban 30 3 v490 := viaSmall (by decide +kernel) (by decide)
def v491 : List ℕ := [w0,w1,w21,w114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b546 : Ban 30 3 v491 := viaSmall (by decide +kernel) (by decide)
def v492 : List ℕ := [w0,w9,w2,w114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b547 : Ban 30 3 v492 := viaSmall (by decide +kernel) (by decide)
def v493 : List ℕ := [w1,w9,w2,w114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b548 : Ban 30 3 v493 := viaSmall (by decide +kernel) (by decide)
def v494 : List ℕ := [w1,w2,w21,w114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b549 : Ban 30 3 v494 := viaSmall (by decide +kernel) (by decide)
def v495 : List ℕ := [w1,w2,w19,w114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b550 : Ban 30 3 v495 := viaSmall (by decide +kernel) (by decide)
def v496 : List ℕ := [w1,w21,w114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b551 : Ban 30 3 v496 := viaSmall (by decide +kernel) (by decide)
def v497 : List ℕ := [w9,w2,w114]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b552 : Ban 30 3 v497 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b542 : Ban 30 4 v337 := viaBranch (ws := [v488,v489,v490,v472,v473,v491,v492,v493,v494,v495,v496,v497])
  (consBan b543 (consBan b544 (consBan b545 (consBan b525 (consBan b526 (consBan b546 (consBan b547 (consBan b548 (consBan b549 (consBan b550 (consBan b551 (consBan b552 (nilBan _ _)))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def v498 : List ℕ := [w0,w171,w2,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b553 : Ban 30 4 v498 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b514 : Ban 30 5 v203 := viaBranch (ws := [v1,v15,v462,v463,v464,v465,v466,v467,v468,v476,v477,v478,v479,v480,v481,v482,v483,v484,v485,v10,v486,v32,v11,v487,v337,v14,v498])
  (consBan b23 (consBan b24 (consBan b515 (consBan b516 (consBan b517 (consBan b518 (consBan b519 (consBan b520 (consBan b521 (consBan b530 (consBan b531 (consBan b532 (consBan b533 (consBan b534 (consBan b535 (consBan b536 (consBan b537 (consBan b538 (consBan b539 (consBan b12 (consBan b540 (consBan b37 (consBan b13 (consBan b541 (consBan b542 (consBan b16 (consBan b553 (nilBan _ _))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit42 : Wide 30 5 v203 := viaSub (ws := [v0,v203])
  (consBan b93 (consBan b514 (nilBan _ _)))
  (by decide) (by decide +kernel)
def w172 : ℕ := 0x3fffffc0
def v499 : List ℕ := [w172,w43,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b554 : Ban 60 6 v499 := viaCut proj18 petit42 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b555 : Ban 30 5 v39 := viaPerm proj2 proj1 b514 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit43 : Wide 30 5 v39 := viaSub (ws := [v0,v39])
  (consBan b93 (consBan b555 (nilBan _ _)))
  (by decide) (by decide +kernel)
def v500 : List ℕ := [w172,w43,w44,w45,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b556 : Ban 60 6 v500 := viaCut proj20 petit43 (by decide) (by decide +kernel) (by decide +kernel)
def v501 : List ℕ := [w172,w43,w44,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b557 : Ban 60 6 v501 := viaCut proj18 petit42 (by decide) (by decide +kernel) (by decide +kernel)
def v502 : List ℕ := [w52,w43,w44,w65,w45,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b558 : Ban 60 6 v502 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v503 : List ℕ := [w52,w43,w44,w65,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b559 : Ban 60 6 v503 := viaCut proj21 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v504 : List ℕ := [w52,w43,w44,w65,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b560 : Ban 60 6 v504 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit44 : Wide 30 4 v64 := viaSearch (by decide +kernel)
def v505 : List ℕ := [w68,w43,w44,w45,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b561 : Ban 60 6 v505 := viaCut proj22 petit44 (by decide) (by decide +kernel) (by decide +kernel)
def w173 : ℕ := 0xfff000000000000
def v506 : List ℕ := [w173,w43,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b562 : Ban 60 6 v506 := viaCut proj22 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v507 : List ℕ := [w57,w44,w65,w45,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b563 : Ban 60 6 v507 := viaCut proj18 petit41 (by decide) (by decide +kernel) (by decide +kernel)
def w174 : ℕ := 0x4104104104104100003f00000003f
def v508 : List ℕ := [w174,w43,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b564 : Ban 60 6 v508 := viaCut proj18 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def v509 : List ℕ := [w174,w44,w65,w45,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b565 : Ban 60 6 v509 := viaCut proj18 petit41 (by decide) (by decide +kernel) (by decide +kernel)
def v510 : List ℕ := [w174,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b566 : Ban 60 6 v510 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v511 : List ℕ := [w58,w44,w65,w45,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b567 : Ban 60 6 v511 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v512 : List ℕ := [w59,w44,w65,w45,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b568 : Ban 60 6 v512 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v513 : List ℕ := [w60,w43,w44,w45,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b569 : Ban 60 6 v513 := viaCut proj18 petit40 (by decide) (by decide +kernel) (by decide +kernel)
def v514 : List ℕ := [w60,w43,w65,w45,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b570 : Ban 60 6 v514 := viaCut proj18 petit40 (by decide) (by decide +kernel) (by decide +kernel)
def v515 : List ℕ := [w43,w61,w65,w45,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b571 : Ban 60 6 v515 := viaCut proj19 petit41 (by decide) (by decide +kernel) (by decide +kernel)
def w175 : ℕ := 0x82082082082082000fc000000003f
def v516 : List ℕ := [w43,w175,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b572 : Ban 60 6 v516 := viaCut proj19 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def v517 : List ℕ := [w43,w175,w65,w45,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b573 : Ban 60 6 v517 := viaCut proj19 petit41 (by decide) (by decide +kernel) (by decide +kernel)
def v518 : List ℕ := [w43,w175,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b574 : Ban 60 6 v518 := viaCut proj19 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v519 : List ℕ := [w43,w62,w65,w45,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b575 : Ban 60 6 v519 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v520 : List ℕ := [w43,w63,w65,w45,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b576 : Ban 60 6 v520 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v521 : List ℕ := [w43,w64,w44,w45,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b577 : Ban 60 6 v521 := viaCut proj19 petit40 (by decide) (by decide +kernel) (by decide +kernel)
def v522 : List ℕ := [w43,w44,w92,w45,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b578 : Ban 60 6 v522 := viaCut proj20 petit13 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b579 : Ban 30 5 v485 := viaPerm proj3 proj4 b177 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit45 : Wide 30 5 v485 := viaSub (ws := [v0,v485])
  (consBan b93 (consBan b579 (nilBan _ _)))
  (by decide) (by decide +kernel)
def w176 : ℕ := 0xc30c30c30c30c3000fff00000003f
def v523 : List ℕ := [w43,w44,w176,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b580 : Ban 60 6 v523 := viaCut proj18 petit45 (by decide) (by decide +kernel) (by decide +kernel)
def v524 : List ℕ := [w43,w44,w176,w45,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b581 : Ban 60 6 v524 := viaCut proj20 petit14 (by decide) (by decide +kernel) (by decide +kernel)
def v525 : List ℕ := [w43,w44,w176,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b582 : Ban 60 6 v525 := viaCut proj18 petit45 (by decide) (by decide +kernel) (by decide +kernel)
def v526 : List ℕ := [w43,w44,w93,w45,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b583 : Ban 60 6 v526 := viaCut proj20 petit14 (by decide) (by decide +kernel) (by decide +kernel)
def v527 : List ℕ := [w43,w44,w94,w45,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b584 : Ban 60 6 v527 := viaCut proj21 petit14 (by decide) (by decide +kernel) (by decide +kernel)
def v528 : List ℕ := [w43,w44,w65,w95,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b585 : Ban 60 6 v528 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b586 : Ban 60 6 v276 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v529 : List ℕ := [w43,w44,w65,w96,w45,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b587 : Ban 60 6 v529 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v530 : List ℕ := [w43,w44,w65,w97,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b588 : Ban 60 6 v530 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v531 : List ℕ := [w43,w44,w65,w98,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b589 : Ban 60 6 v531 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v532 : List ℕ := [w43,w44,w65,w99,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b590 : Ban 60 6 v532 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v533 : List ℕ := [w43,w44,w65,w45,w165,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b591 : Ban 60 6 v533 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b592 : Ban 60 6 v448 := viaCut proj21 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v534 : List ℕ := [w43,w44,w65,w45,w142,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b593 : Ban 60 6 v534 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v535 : List ℕ := [w43,w44,w65,w45,w167,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b594 : Ban 60 6 v535 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v536 : List ℕ := [w43,w44,w65,w45,w168,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b595 : Ban 60 6 v536 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v537 : List ℕ := [w0,w1,w2,w83,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b596 : Ban 30 5 v537 := viaPerm proj1 proj2 b363 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit46 : Wide 30 5 v537 := viaSub (ws := [v0,v537])
  (consBan b93 (consBan b596 (nilBan _ _)))
  (by decide) (by decide +kernel)
def w177 : ℕ := 0x30c30c30c30c30c000000fffffffc0
def v538 : List ℕ := [w43,w44,w65,w45,w46,w177,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b597 : Ban 60 6 v538 := viaCut proj18 petit46 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b598 : Ban 30 5 v212 := viaPerm proj11 proj12 b363 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit47 : Wide 30 5 v212 := viaSub (ws := [v0,v212])
  (consBan b93 (consBan b598 (nilBan _ _)))
  (by decide) (by decide +kernel)
def w178 : ℕ := 0x30c30c30c30c30cfff000fc0000000
def v539 : List ℕ := [w43,w44,w65,w45,w46,w178,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b599 : Ban 60 6 v539 := viaCut proj18 petit47 (by decide) (by decide +kernel) (by decide +kernel)
def w179 : ℕ := 0x30c30c30c30c30cfff000fc0fc0fc0
def v540 : List ℕ := [w43,w44,w65,w45,w46,w179,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b600 : Ban 60 6 v540 := viaCut proj18 petit47 (by decide) (by decide +kernel) (by decide +kernel)
def w180 : ℕ := 0x30c30c30c30c30cfff000fff03f000
def v541 : List ℕ := [w43,w44,w65,w45,w46,w180,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b601 : Ban 60 6 v541 := viaCut proj19 petit47 (by decide) (by decide +kernel) (by decide +kernel)
def w181 : ℕ := 0x34d34d34d34d34dfff03ffffffffff
def v542 : List ℕ := [w43,w44,w65,w45,w46,w181,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b602 : Ban 60 6 v542 := viaCut proj18 petit41 (by decide) (by decide +kernel) (by decide +kernel)
def w182 : ℕ := 0x38e38e38e38e38effffc0fffffffff
def v543 : List ℕ := [w43,w44,w65,w45,w46,w182,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b603 : Ban 60 6 v543 := viaCut proj19 petit41 (by decide) (by decide +kernel) (by decide +kernel)
def w183 : ℕ := 0x410410410410410000fff000000000
def v544 : List ℕ := [w43,w44,w65,w45,w46,w183,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b604 : Ban 60 6 v544 := viaCut proj22 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def w184 : ℕ := 0x739ce73bfffffff
def v545 : List ℕ := [w0,w1,w2,w3,w184]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b605 : Ban 30 5 v545 := viaPerm proj11 proj12 b382 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit48 : Wide 30 5 v545 := viaSub (ws := [v0,v545])
  (consBan b93 (consBan b605 (nilBan _ _)))
  (by decide) (by decide +kernel)
def w185 : ℕ := 0x71c71c71c71c71cfffffffffffffc0
def v546 : List ℕ := [w43,w44,w65,w45,w46,w47,w185]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b606 : Ban 60 6 v546 := viaCut proj18 petit48 (by decide) (by decide +kernel) (by decide +kernel)
def v547 : List ℕ := [w43,w44,w65,w45,w164,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b607 : Ban 60 6 v547 := viaCut proj18 petit41 (by decide) (by decide +kernel) (by decide +kernel)
def v548 : List ℕ := [w43,w44,w65,w45,w163,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b608 : Ban 60 6 v548 := viaCut proj19 petit41 (by decide) (by decide +kernel) (by decide +kernel)
def v549 : List ℕ := [w43,w44,w65,w45,w143,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b609 : Ban 60 6 v549 := viaPerm proj26 proj26 b414 (by decide +kernel) (by decide +kernel)
def v550 : List ℕ := [w0,w1,w2,w36,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit49 : Wide 30 4 v550 := viaSearch (by decide +kernel)
def w186 : ℕ := 0x618618618618618ffffffffffc0000
def v551 : List ℕ := [w42,w65,w45,w46,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b611 : Ban 60 5 v551 := viaCut proj18 petit49 (by decide) (by decide +kernel) (by decide +kernel)
def w187 : ℕ := 0x3f000fc0000000
def v552 : List ℕ := [w187,w43,w44,w65,w46,w125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b612 : Ban 60 5 v552 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def w188 : ℕ := 0xfc0000fc0000000
def v553 : List ℕ := [w188,w43,w44,w65,w45,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b613 : Ban 60 5 v553 := viaCut proj21 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def w189 : ℕ := 0x410410410410410fffffffc0000000
def v554 : List ℕ := [w43,w44,w65,w45,w46,w189]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b614 : Ban 60 5 v554 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit50 : Wide 30 4 v368 := viaSub (ws := [v368])
  (consBan b425 (nilBan _ _))
  (by decide) (by decide +kernel)
def v555 : List ℕ := [w43,w44,w65,w141,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b615 : Ban 60 5 v555 := viaCut proj18 petit50 (by decide) (by decide +kernel) (by decide +kernel)
def v556 : List ℕ := [w43,w44,w97,w46,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b616 : Ban 60 5 v556 := viaCut proj20 petit44 (by decide) (by decide +kernel) (by decide +kernel)
def v557 : List ℕ := [w43,w44,w45,w142,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b617 : Ban 60 5 v557 := viaCut proj21 petit44 (by decide) (by decide +kernel) (by decide +kernel)
def w190 : ℕ := 0x6318c633e000000
def v558 : List ℕ := [w0,w1,w2,w3,w190]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit51 : Wide 30 4 v558 := viaSearch (by decide +kernel)
def w191 : ℕ := 0x514514514514514fff000fc0000000
def v559 : List ℕ := [w43,w44,w45,w46,w191,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b618 : Ban 60 5 v559 := viaCut proj21 petit51 (by decide) (by decide +kernel) (by decide +kernel)
def w192 : ℕ := 0x618618618618618fff000fc0000000
def v560 : List ℕ := [w43,w44,w45,w46,w125,w192]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b619 : Ban 60 5 v560 := viaCut proj20 petit51 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit52 : Wide 30 4 v348 := viaSearch (by decide +kernel)
def w193 : ℕ := 0x6db6db6db6db6dbfffffffffffffff
def v561 : List ℕ := [w43,w44,w45,w46,w125,w193]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b620 : Ban 60 5 v561 := viaCut proj20 petit52 (by decide) (by decide +kernel) (by decide +kernel)
def v562 : List ℕ := [w43,w44,w45,w46,w123,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b621 : Ban 60 5 v562 := viaCut proj21 petit52 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit53 : Wide 30 4 v349 := viaSearch (by decide +kernel)
def v563 : List ℕ := [w43,w44,w45,w143,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b622 : Ban 60 5 v563 := viaCut proj20 petit53 (by decide) (by decide +kernel) (by decide +kernel)
def v564 : List ℕ := [w43,w44,w102,w46,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b623 : Ban 60 5 v564 := viaCut proj21 petit53 (by decide) (by decide +kernel) (by decide +kernel)
def v565 : List ℕ := [w0,w1,w2,w36,w137]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit54 : Wide 30 4 v565 := viaSearch (by decide +kernel)
def w194 : ℕ := 0x69a69a69a69a69affffffffffff03f
def v566 : List ℕ := [w43,w65,w45,w46,w125,w194]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b624 : Ban 60 5 v566 := viaCut proj18 petit54 (by decide) (by decide +kernel) (by decide +kernel)
def v567 : List ℕ := [w0,w1,w2,w34,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit55 : Wide 30 4 v567 := viaSearch (by decide +kernel)
def w195 : ℕ := 0x596596596596596fffffffff03ffff
def v568 : List ℕ := [w43,w65,w45,w46,w195,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b625 : Ban 60 5 v568 := viaCut proj18 petit55 (by decide) (by decide +kernel) (by decide +kernel)
def v569 : List ℕ := [w43,w44,w121,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b627 : Ban 60 4 v569 := viaCut proj22 petit52 (by decide) (by decide +kernel) (by decide +kernel)
def v570 : List ℕ := [w1,w21,w34,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit56 : Wide 30 3 v570 := viaSearch (by decide +kernel)
def v571 : List ℕ := [w43,w100,w163,w195,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b628 : Ban 60 4 v571 := viaCut proj18 petit56 (by decide) (by decide +kernel) (by decide +kernel)
def v572 : List ℕ := [w43,w102,w163,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b629 : Ban 60 4 v572 := viaCut proj21 petit53 (by decide) (by decide +kernel) (by decide +kernel)
def v573 : List ℕ := [w9,w2,w36,w137]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit57 : Wide 30 3 v573 := viaSearch (by decide +kernel)
def w196 : ℕ := 0x659659659659659ffffffffffc0fff
def v574 : List ℕ := [w44,w100,w163,w125,w196]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b630 : Ban 60 4 v574 := viaCut proj19 petit57 (by decide) (by decide +kernel) (by decide +kernel)
def v575 : List ℕ := [w44,w100,w143,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b631 : Ban 60 4 v575 := viaCut proj20 petit53 (by decide) (by decide +kernel) (by decide +kernel)
def v576 : List ℕ := [w65,w100,w163,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b632 : Ban 60 4 v576 := viaBranch (ws := [])
  (nilBan _ _)
  (by decide) (by decide +kernel) (by decide +kernel)
def v577 : List ℕ := [w43,w44,w100,w163,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b626 : Ban 60 5 v577 := viaBranch (ws := [v569,v571,v572,v574,v575,v576])
  (consBan b627 (consBan b628 (consBan b629 (consBan b630 (consBan b631 (consBan b632 (nilBan _ _)))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def proj35 : Projection 60 60 := pick [6,8,7,10,9,11,0,2,1,4,3,5,12,14,13,16,15,17,36,38,37,40,39,41,48,50,49,52,51,53,42,44,43,46,45,47,18,20,19,22,21,23,30,32,31,34,33,35,24,26,25,28,27,29,54,56,55,58,57,59] rfl (by decide +kernel) (by decide)
def v578 : List ℕ := [w43,w65,w45,w163,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b633 : Ban 60 5 v578 := viaPerm proj35 proj35 b626 (by decide +kernel) (by decide +kernel)
def proj36 : Projection 60 60 := pick [18,21,19,22,20,23,0,3,1,4,2,5,24,27,25,28,26,29,36,39,37,40,38,41,54,57,55,58,56,59,42,45,43,46,44,47,6,9,7,10,8,11,30,33,31,34,32,35,12,15,13,16,14,17,48,51,49,52,50,53] rfl (by decide +kernel) (by decide)
def proj37 : Projection 60 60 := pick [6,8,10,7,9,11,36,38,40,37,39,41,48,50,52,49,51,53,0,2,4,1,3,5,12,14,16,13,15,17,42,44,46,43,45,47,18,20,22,19,21,23,30,32,34,31,33,35,54,56,58,55,57,59,24,26,28,25,27,29] rfl (by decide +kernel) (by decide)
def v579 : List ℕ := [w43,w65,w101,w46,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b634 : Ban 60 5 v579 := viaPerm proj36 proj37 b626 (by decide +kernel) (by decide +kernel)
def v580 : List ℕ := [w44,w65,w45,w46,w125,w196]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b635 : Ban 60 5 v580 := viaCut proj19 petit54 (by decide) (by decide +kernel) (by decide +kernel)
def v581 : List ℕ := [w44,w65,w45,w46,w151,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b636 : Ban 60 5 v581 := viaCut proj19 petit55 (by decide) (by decide +kernel) (by decide +kernel)
def proj38 : Projection 60 60 := pick [13,14,12,16,15,17,1,2,0,4,3,5,7,8,6,10,9,11,43,44,42,46,45,47,49,50,48,52,51,53,37,38,36,40,39,41,25,26,24,28,27,29,31,32,30,34,33,35,19,20,18,22,21,23,55,56,54,58,57,59] rfl (by decide +kernel) (by decide)
def proj39 : Projection 60 60 := pick [8,6,7,10,9,11,14,12,13,16,15,17,2,0,1,4,3,5,50,48,49,52,51,53,38,36,37,40,39,41,44,42,43,46,45,47,32,30,31,34,33,35,20,18,19,22,21,23,26,24,25,28,27,29,56,54,55,58,57,59] rfl (by decide +kernel) (by decide)
def v582 : List ℕ := [w44,w65,w45,w164,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b637 : Ban 60 5 v582 := viaPerm proj38 proj39 b626 (by decide +kernel) (by decide +kernel)
def proj40 : Projection 60 60 := pick [25,27,24,28,26,29,1,3,0,4,2,5,19,21,18,22,20,23,43,45,42,46,44,47,55,57,54,58,56,59,37,39,36,40,38,41,13,15,12,16,14,17,31,33,30,34,32,35,7,9,6,10,8,11,49,51,48,52,50,53] rfl (by decide +kernel) (by decide)
def proj41 : Projection 60 60 := pick [8,6,10,7,9,11,50,48,52,49,51,53,38,36,40,37,39,41,14,12,16,13,15,17,2,0,4,1,3,5,44,42,46,43,45,47,32,30,34,31,33,35,20,18,22,19,21,23,56,54,58,55,57,59,26,24,28,25,27,29] rfl (by decide +kernel) (by decide)
def v583 : List ℕ := [w44,w65,w100,w46,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b638 : Ban 60 5 v583 := viaPerm proj40 proj41 b626 (by decide +kernel) (by decide +kernel)
def v584 : List ℕ := [w43,w44,w65,w45,w46,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b610 : Ban 60 6 v584 := viaBranch (ws := [v551,v552,v553,v554,v555,v556,v557,v559,v560,v561,v562,v563,v564,v566,v568,v578,v579,v580,v581,v582,v583])
  (consBan b611 (consBan b612 (consBan b613 (consBan b614 (consBan b615 (consBan b616 (consBan b617 (consBan b618 (consBan b619 (consBan b620 (consBan b621 (consBan b622 (consBan b623 (consBan b624 (consBan b625 (consBan b633 (consBan b634 (consBan b635 (consBan b636 (consBan b637 (consBan b638 (nilBan _ _))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def v585 : List ℕ := [w43,w44,w65,w45,w141,w47,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b639 : Ban 60 6 v585 := viaPerm proj26 proj26 b610 (by decide +kernel) (by decide +kernel)
def v586 : List ℕ := [w43,w44,w65,w100,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b640 : Ban 60 6 v586 := viaCut proj18 petit41 (by decide) (by decide +kernel) (by decide +kernel)
def v587 : List ℕ := [w43,w44,w65,w101,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b641 : Ban 60 6 v587 := viaCut proj19 petit41 (by decide) (by decide +kernel) (by decide +kernel)
def v588 : List ℕ := [w43,w44,w65,w166,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b642 : Ban 60 6 v588 := viaCut proj21 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v589 : List ℕ := [w43,w44,w65,w46,w141,w47,w125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b643 : Ban 60 6 v589 := viaPerm proj23 proj24 b610 (by decide +kernel) (by decide +kernel)
def v590 : List ℕ := [w43,w44,w97,w45,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b644 : Ban 60 6 v590 := viaCut proj20 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def v591 : List ℕ := [w43,w44,w97,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b645 : Ban 60 6 v591 := viaCut proj20 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v592 : List ℕ := [w43,w44,w45,w102,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b646 : Ban 60 6 v592 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v593 : List ℕ := [w43,w44,w45,w142,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b647 : Ban 60 6 v593 := viaCut proj21 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def v594 : List ℕ := [w43,w44,w45,w142,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b648 : Ban 60 6 v594 := viaCut proj21 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v595 : List ℕ := [w43,w44,w45,w46,w143,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b649 : Ban 60 6 v595 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b650 : Ban 30 5 v47 := viaPerm proj7 proj7 b177 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit58 : Wide 30 5 v47 := viaSub (ws := [v0,v47])
  (consBan b93 (consBan b650 (nilBan _ _)))
  (by decide) (by decide +kernel)
def v596 : List ℕ := [w43,w44,w45,w46,w178,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b651 : Ban 60 6 v596 := viaCut proj20 petit58 (by decide) (by decide +kernel) (by decide +kernel)
def v597 : List ℕ := [w43,w44,w45,w46,w178,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b652 : Ban 60 6 v597 := viaCut proj20 petit58 (by decide) (by decide +kernel) (by decide +kernel)
def v598 : List ℕ := [w43,w44,w45,w46,w141,w121,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b653 : Ban 60 6 v598 := viaCut proj20 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def v599 : List ℕ := [w43,w44,w45,w46,w141,w130,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b654 : Ban 60 6 v599 := viaCut proj22 petit44 (by decide) (by decide +kernel) (by decide +kernel)
def v600 : List ℕ := [w43,w44,w45,w46,w141,w47,w124]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b655 : Ban 60 6 v600 := viaCut proj20 petit16 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b656 : Ban 60 6 v408 := viaCut proj18 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def v601 : List ℕ := [w43,w44,w45,w143,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b657 : Ban 60 6 v601 := viaCut proj20 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def v602 : List ℕ := [w43,w44,w102,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b658 : Ban 60 6 v602 := viaCut proj21 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def v603 : List ℕ := [w43,w65,w45,w101,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b659 : Ban 60 6 v603 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v604 : List ℕ := [w43,w65,w45,w46,w163,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b660 : Ban 60 6 v604 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def proj42 : Projection 60 60 := pick [32,33,30,34,31,35,8,9,6,10,7,11,20,21,18,22,19,23,50,51,48,52,49,53,56,57,54,58,55,59,38,39,36,40,37,41,14,15,12,16,13,17,26,27,24,28,25,29,2,3,0,4,1,5,44,45,42,46,43,47] rfl (by decide +kernel) (by decide)
def proj43 : Projection 60 60 := pick [50,52,48,49,51,53,8,10,6,7,9,11,38,40,36,37,39,41,14,16,12,13,15,17,44,46,42,43,45,47,2,4,0,1,3,5,32,34,30,31,33,35,56,58,54,55,57,59,20,22,18,19,21,23,26,28,24,25,27,29] rfl (by decide +kernel) (by decide)
def v605 : List ℕ := [w43,w65,w45,w46,w141,w182,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b661 : Ban 60 6 v605 := viaPerm proj42 proj43 b414 (by decide +kernel) (by decide +kernel)
def v606 : List ℕ := [w43,w65,w45,w46,w141,w47,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b662 : Ban 60 6 v606 := viaPerm proj42 proj43 b610 (by decide +kernel) (by decide +kernel)
def v607 : List ℕ := [w43,w65,w45,w46,w182,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b663 : Ban 60 6 v607 := viaCut proj18 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def v608 : List ℕ := [w0,w1,w2,w20,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit59 : Wide 30 4 v608 := viaSearch (by decide +kernel)
def w197 : ℕ := 0x3f000fc0000
def v609 : List ℕ := [w197,w44,w45,w164,w153,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b665 : Ban 60 5 v609 := viaCut proj18 petit59 (by decide) (by decide +kernel) (by decide +kernel)
def v610 : List ℕ := [w0,w1,w21,w3,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit60 : Wide 30 4 v610 := viaSearch (by decide +kernel)
def w198 : ℕ := 0xfc003f000000
def v611 : List ℕ := [w198,w43,w45,w164,w153,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b666 : Ban 60 5 v611 := viaCut proj19 petit60 (by decide) (by decide +kernel) (by decide +kernel)
def w199 : ℕ := 0x3e0003e0
def v612 : List ℕ := [w199,w0,w1,w2,w41]
def v613 : List ℕ := [w199,w0,w1,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b667 : Ban 30 4 v613 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b668 : Ban 30 4 v612 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit61 : Wide 30 4 v612 := viaSub (ws := [v613,v612])
  (consBan b667 (consBan b668 (nilBan _ _)))
  (by decide) (by decide +kernel)
def w200 : ℕ := 0xfc003f03f00003f
def v614 : List ℕ := [w200,w43,w44,w45,w164,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b669 : Ban 60 5 v614 := viaCut proj18 petit61 (by decide) (by decide +kernel) (by decide +kernel)
def w201 : ℕ := 0x3e0f8000
def v615 : List ℕ := [w201,w0,w1,w3,w41]
def v616 : List ℕ := [w201,w0,w1,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b670 : Ban 30 4 v616 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b671 : Ban 30 4 v615 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit62 : Wide 30 4 v615 := viaSub (ws := [v616,v615])
  (consBan b670 (consBan b671 (nilBan _ _)))
  (by decide) (by decide +kernel)
def v617 : List ℕ := [w200,w43,w44,w45,w153,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b672 : Ban 60 5 v617 := viaCut proj19 petit62 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit63 : Wide 30 4 v613 := viaSearch (by decide +kernel)
def v618 : List ℕ := [w200,w43,w44,w45,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b673 : Ban 60 5 v618 := viaCut proj18 petit63 (by decide) (by decide +kernel) (by decide +kernel)
def w202 : ℕ := 0x41041041041041000000000fc0fc0
def v619 : List ℕ := [w202,w44,w45,w164,w153,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b674 : Ban 60 5 v619 := viaCut proj18 petit59 (by decide) (by decide +kernel) (by decide +kernel)
def v620 : List ℕ := [w59,w44,w45,w164,w153,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b675 : Ban 60 5 v620 := viaCut proj18 petit59 (by decide) (by decide +kernel) (by decide +kernel)
def v621 : List ℕ := [w60,w44,w45,w164,w153,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b676 : Ban 60 5 v621 := viaCut proj18 petit59 (by decide) (by decide +kernel) (by decide +kernel)
def w203 : ℕ := 0x82082082082082000fc000003f000
def v622 : List ℕ := [w43,w203,w45,w164,w153,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b677 : Ban 60 5 v622 := viaCut proj19 petit60 (by decide) (by decide +kernel) (by decide +kernel)
def v623 : List ℕ := [w43,w63,w45,w164,w153,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b678 : Ban 60 5 v623 := viaCut proj19 petit60 (by decide) (by decide +kernel) (by decide +kernel)
def v624 : List ℕ := [w43,w64,w45,w164,w153,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b679 : Ban 60 5 v624 := viaCut proj18 petit59 (by decide) (by decide +kernel) (by decide +kernel)
def w204 : ℕ := 0x208208208208208000000fc0fc0000
def v625 : List ℕ := [w43,w44,w45,w204,w164,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b680 : Ban 60 5 v625 := viaCut proj21 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def v626 : List ℕ := [w43,w44,w45,w168,w153,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b681 : Ban 60 5 v626 := viaCut proj21 petit30 (by decide) (by decide +kernel) (by decide +kernel)
def w205 : ℕ := 0x208208208208208fc003fffffc0000
def v627 : List ℕ := [w43,w44,w45,w205,w153,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b682 : Ban 60 5 v627 := viaCut proj22 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def w206 : ℕ := 0x210842100007c00
def v628 : List ℕ := [w0,w1,w206,w2,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit64 : Wide 30 4 v628 := viaSearch (by decide +kernel)
def w207 : ℕ := 0x249249249249249000000fc0fc0fc0
def v629 : List ℕ := [w43,w44,w45,w207,w164,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b683 : Ban 60 5 v629 := viaCut proj18 petit64 (by decide) (by decide +kernel) (by decide +kernel)
def v630 : List ℕ := [w0,w1,w117,w3,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit65 : Wide 30 4 v630 := viaSearch (by decide +kernel)
def w208 : ℕ := 0x249249249249249fc003f03ffc003f
def v631 : List ℕ := [w43,w44,w45,w208,w153,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b684 : Ban 60 5 v631 := viaCut proj19 petit65 (by decide) (by decide +kernel) (by decide +kernel)
def w209 : ℕ := 0x249249249249249fc003ffc0fc0fc0
def v632 : List ℕ := [w43,w44,w45,w209,w153,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b685 : Ban 60 5 v632 := viaCut proj19 petit60 (by decide) (by decide +kernel) (by decide +kernel)
def w210 : ℕ := 0x410410410410410fff03f000000000
def v633 : List ℕ := [w43,w44,w45,w164,w210,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b686 : Ban 60 5 v633 := viaCut proj22 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def w211 : ℕ := 0x410410410410410ffffff03f000000
def v634 : List ℕ := [w43,w44,w45,w164,w211,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b687 : Ban 60 5 v634 := viaCut proj21 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v635 : List ℕ := [w0,w1,w2,w159,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit66 : Wide 30 4 v635 := viaSearch (by decide +kernel)
def w212 : ℕ := 0x492492492492492fc0fff03f00003f
def v636 : List ℕ := [w43,w44,w45,w164,w212,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b688 : Ban 60 5 v636 := viaCut proj18 petit66 (by decide) (by decide +kernel) (by decide +kernel)
def v637 : List ℕ := [w43,w44,w45,w164,w140,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b689 : Ban 60 5 v637 := viaCut proj18 petit59 (by decide) (by decide +kernel) (by decide +kernel)
def w213 : ℕ := 0x6318c633e0f83e0
def v638 : List ℕ := [w0,w1,w2,w20,w213]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit67 : Wide 30 4 v638 := viaSearch (by decide +kernel)
def w214 : ℕ := 0x618618618618618fc0fff03ffc0000
def v639 : List ℕ := [w43,w44,w45,w164,w153,w214]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b690 : Ban 60 5 v639 := viaCut proj18 petit67 (by decide) (by decide +kernel) (by decide +kernel)
def v640 : List ℕ := [w0,w1,w2,w20,w184]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit68 : Wide 30 4 v640 := viaSearch (by decide +kernel)
def v641 : List ℕ := [w43,w44,w45,w164,w153,w185]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b691 : Ban 60 5 v641 := viaCut proj18 petit68 (by decide) (by decide +kernel) (by decide +kernel)
def v642 : List ℕ := [w43,w44,w45,w164,w124,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b692 : Ban 60 5 v642 := viaCut proj18 petit59 (by decide) (by decide +kernel) (by decide +kernel)
def v643 : List ℕ := [w43,w44,w45,w164,w195,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b693 : Ban 60 5 v643 := viaCut proj18 petit55 (by decide) (by decide +kernel) (by decide +kernel)
def v644 : List ℕ := [w43,w44,w45,w143,w153,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b694 : Ban 60 5 v644 := viaCut proj19 petit60 (by decide) (by decide +kernel) (by decide +kernel)
def v645 : List ℕ := [w43,w44,w45,w181,w153,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b695 : Ban 60 5 v645 := viaCut proj19 petit53 (by decide) (by decide +kernel) (by decide +kernel)
def w215 : ℕ := 0x41041041041041003ffc0000000000
def v646 : List ℕ := [w43,w44,w45,w215,w153,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b696 : Ban 60 5 v646 := viaCut proj22 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def w216 : ℕ := 0x421084201f00000
def v647 : List ℕ := [w0,w1,w216,w3,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit69 : Wide 30 4 v647 := viaSearch (by decide +kernel)
def w217 : ℕ := 0x49249249249249203ffc000003f000
def v648 : List ℕ := [w43,w44,w45,w217,w153,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b697 : Ban 60 5 v648 := viaCut proj19 petit69 (by decide) (by decide +kernel) (by decide +kernel)
def v649 : List ℕ := [w43,w65,w45,w164,w153,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b698 : Ban 60 5 v649 := viaCut proj18 petit59 (by decide) (by decide +kernel) (by decide +kernel)
def proj44 : Projection 60 60 := pick [6,8,9,7,10,11,18,20,21,19,22,23,30,32,33,31,34,35,0,2,3,1,4,5,12,14,15,13,16,17,24,26,27,25,28,29,36,38,39,37,40,41,48,50,51,49,52,53,54,56,57,55,58,59,42,44,45,43,46,47] rfl (by decide +kernel) (by decide)
def proj45 : Projection 60 60 := pick [18,21,19,20,22,23,0,3,1,2,4,5,24,27,25,26,28,29,6,9,7,8,10,11,30,33,31,32,34,35,12,15,13,14,16,17,36,39,37,38,40,41,54,57,55,56,58,59,42,45,43,44,46,47,48,51,49,50,52,53] rfl (by decide +kernel) (by decide)
def v650 : List ℕ := [w43,w45,w101,w164,w153,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b699 : Ban 60 5 v650 := viaPerm proj44 proj45 b626 (by decide +kernel) (by decide +kernel)
def v651 : List ℕ := [w1,w2,w21,w20,w41]
def v652 : List ℕ := [w1,w21,w20,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b700 : Ban 30 4 v652 := viaPerm proj9 proj9 b425 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b701 : Ban 30 4 v651 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit70 : Wide 30 4 v651 := viaSub (ws := [v652,v651])
  (consBan b700 (consBan b701 (nilBan _ _)))
  (by decide) (by decide +kernel)
def v653 : List ℕ := [w43,w45,w164,w143,w153,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b702 : Ban 60 5 v653 := viaCut proj18 petit70 (by decide) (by decide +kernel) (by decide +kernel)
def v654 : List ℕ := [w43,w45,w164,w210,w153,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b703 : Ban 60 5 v654 := viaCut proj22 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def v655 : List ℕ := [w1,w2,w20,w136,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit71 : Wide 30 4 v655 := viaSearch (by decide +kernel)
def w218 : ℕ := 0x618618618618618fff03ffc0fc0000
def v656 : List ℕ := [w43,w45,w164,w153,w218,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b704 : Ban 60 5 v656 := viaCut proj18 petit71 (by decide) (by decide +kernel) (by decide +kernel)
def v657 : List ℕ := [w43,w45,w143,w153,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b705 : Ban 60 5 v657 := viaCut proj22 petit16 (by decide) (by decide +kernel) (by decide +kernel)
def v658 : List ℕ := [w44,w65,w45,w164,w153,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b706 : Ban 60 5 v658 := viaCut proj19 petit60 (by decide) (by decide +kernel) (by decide +kernel)
def proj46 : Projection 60 60 := pick [13,14,16,12,15,17,43,44,46,42,45,47,49,50,52,48,51,53,1,2,4,0,3,5,7,8,10,6,9,11,37,38,40,36,39,41,25,26,28,24,27,29,31,32,34,30,33,35,55,56,58,54,57,59,19,20,22,18,21,23] rfl (by decide +kernel) (by decide)
def proj47 : Projection 60 60 := pick [21,18,19,22,20,23,27,24,25,28,26,29,3,0,1,4,2,5,57,54,55,58,56,59,39,36,37,40,38,41,45,42,43,46,44,47,33,30,31,34,32,35,9,6,7,10,8,11,15,12,13,16,14,17,51,48,49,52,50,53] rfl (by decide +kernel) (by decide)
def v659 : List ℕ := [w44,w45,w100,w164,w153,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b707 : Ban 60 5 v659 := viaPerm proj46 proj47 b626 (by decide +kernel) (by decide +kernel)
def v660 : List ℕ := [w44,w45,w168,w164,w153,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b708 : Ban 60 5 v660 := viaCut proj21 petit30 (by decide) (by decide +kernel) (by decide +kernel)
def v661 : List ℕ := [w1,w21,w3,w20,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b709 : Ban 30 4 v661 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit72 : Wide 30 4 v661 := viaSub (ws := [v652,v661])
  (consBan b700 (consBan b709 (nilBan _ _)))
  (by decide) (by decide +kernel)
def v662 : List ℕ := [w44,w45,w164,w153,w124,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b710 : Ban 60 5 v662 := viaCut proj19 petit72 (by decide) (by decide +kernel) (by decide +kernel)
def v663 : List ℕ := [w1,w21,w3,w136,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit73 : Wide 30 4 v663 := viaSearch (by decide +kernel)
def w219 : ℕ := 0x618618618618618ffffc0fff000000
def v664 : List ℕ := [w44,w45,w164,w153,w219,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b711 : Ban 60 5 v664 := viaCut proj19 petit73 (by decide) (by decide +kernel) (by decide +kernel)
def v665 : List ℕ := [w44,w45,w164,w124,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b712 : Ban 60 5 v665 := viaCut proj21 petit16 (by decide) (by decide +kernel) (by decide +kernel)
def w220 : ℕ := 0x1f07c00
def v666 : List ℕ := [w220,w0,w1,w2,w36]
def v667 : List ℕ := [w220,w0,w2,w36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b714 : Ban 30 4 v667 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b715 : Ban 30 4 v666 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit74 : Wide 30 4 v666 := viaSub (ws := [v667,v666])
  (consBan b714 (consBan b715 (nilBan _ _)))
  (by decide) (by decide +kernel)
def w221 : ℕ := 0x3ffc0fff000000
def v668 : List ℕ := [w221,w43,w101,w163,w125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b716 : Ban 60 4 v668 := viaCut proj19 petit74 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit75 : Wide 30 4 v667 := viaSearch (by decide +kernel)
def v669 : List ℕ := [w221,w43,w163,w125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b717 : Ban 60 4 v669 := viaCut proj19 petit75 (by decide) (by decide +kernel) (by decide +kernel)
def v670 : List ℕ := [w82,w0,w1,w3,w41]
def v671 : List ℕ := [w82,w0,w1,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b718 : Ban 30 4 v671 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b719 : Ban 30 4 v670 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit76 : Wide 30 4 v670 := viaSub (ws := [v671,v670])
  (consBan b718 (consBan b719 (nilBan _ _)))
  (by decide) (by decide +kernel)
def v672 : List ℕ := [w221,w43,w163,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b720 : Ban 60 4 v672 := viaCut proj21 petit76 (by decide) (by decide +kernel) (by decide +kernel)
def v673 : List ℕ := [w220,w0,w1,w35,w3]
def v674 : List ℕ := [w220,w0,w35,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b721 : Ban 30 4 v674 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b722 : Ban 30 4 v673 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit77 : Wide 30 4 v673 := viaSub (ws := [v674,v673])
  (consBan b721 (consBan b722 (nilBan _ _)))
  (by decide) (by decide +kernel)
def w222 : ℕ := 0xfc0fc0fc003f000
def v675 : List ℕ := [w222,w43,w101,w163,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b723 : Ban 60 4 v675 := viaCut proj21 petit77 (by decide) (by decide +kernel) (by decide +kernel)
def w223 : ℕ := 0x3e007c00
def v676 : List ℕ := [w223,w0,w2,w35,w3]
def v677 : List ℕ := [w223,w0,w35,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b724 : Ban 30 4 v677 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b725 : Ban 30 4 v676 := viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit78 : Wide 30 4 v676 := viaSub (ws := [v677,v676])
  (consBan b724 (consBan b725 (nilBan _ _)))
  (by decide) (by decide +kernel)
def v678 : List ℕ := [w222,w43,w101,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b726 : Ban 60 4 v678 := viaCut proj22 petit78 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit79 : Wide 30 4 v674 := viaSearch (by decide +kernel)
def v679 : List ℕ := [w222,w43,w101,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b727 : Ban 60 4 v679 := viaCut proj21 petit79 (by decide) (by decide +kernel) (by decide +kernel)
def v680 : List ℕ := [w0,w131,w1,w2,w36]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit80 : Wide 30 4 v680 := viaSearch (by decide +kernel)
def w224 : ℕ := 0x18618618618618600000000003ffff
def v681 : List ℕ := [w43,w224,w101,w163,w125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b728 : Ban 60 4 v681 := viaCut proj19 petit80 (by decide) (by decide +kernel) (by decide +kernel)
def v682 : List ℕ := [w0,w1,w84,w3,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit81 : Wide 30 4 v682 := viaSearch (by decide +kernel)
def v683 : List ℕ := [w43,w106,w163,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b729 : Ban 60 4 v683 := viaCut proj21 petit81 (by decide) (by decide +kernel) (by decide +kernel)
def v684 : List ℕ := [w0,w131,w1,w35,w3]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit82 : Wide 30 4 v684 := viaSearch (by decide +kernel)
def w225 : ℕ := 0x28a28a28a28a28a00000003ffc003f
def v685 : List ℕ := [w43,w101,w225,w163,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b730 : Ban 60 4 v685 := viaCut proj21 petit82 (by decide) (by decide +kernel) (by decide +kernel)
def w226 : ℕ := 0x28a28a28a28a28afc0fc0fff03f000
def v686 : List ℕ := [w43,w101,w226,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b731 : Ban 60 4 v686 := viaCut proj20 petit81 (by decide) (by decide +kernel) (by decide +kernel)
def v687 : List ℕ := [w0,w1,w2,w88,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit83 : Wide 30 4 v687 := viaSearch (by decide +kernel)
def v688 : List ℕ := [w43,w101,w163,w162,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b732 : Ban 60 4 v688 := viaCut proj19 petit83 (by decide) (by decide +kernel) (by decide +kernel)
def v689 : List ℕ := [w0,w1,w2,w36,w136]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit84 : Wide 30 4 v689 := viaSearch (by decide +kernel)
def v690 : List ℕ := [w43,w101,w163,w125,w219]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b733 : Ban 60 4 v690 := viaCut proj19 petit84 (by decide) (by decide +kernel) (by decide +kernel)
def v691 : List ℕ := [w43,w101,w163,w125,w196]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b734 : Ban 60 4 v691 := viaCut proj19 petit54 (by decide) (by decide +kernel) (by decide +kernel)
def v692 : List ℕ := [w43,w101,w163,w151,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b735 : Ban 60 4 v692 := viaCut proj19 petit55 (by decide) (by decide +kernel) (by decide +kernel)
def v693 : List ℕ := [w43,w101,w143,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b736 : Ban 60 4 v693 := viaCut proj20 petit53 (by decide) (by decide +kernel) (by decide +kernel)
def v694 : List ℕ := [w0,w1,w138,w3,w41]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit85 : Wide 30 4 v694 := viaSearch (by decide +kernel)
def w227 : ℕ := 0x51451451451451403f03f000000fc0
def v695 : List ℕ := [w43,w101,w227,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b737 : Ban 60 4 v695 := viaCut proj20 petit85 (by decide) (by decide +kernel) (by decide +kernel)
def w228 : ℕ := 0x618618618618618fc003f000fc0000
def v696 : List ℕ := [w43,w163,w125,w228,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b738 : Ban 60 4 v696 := viaCut proj21 petit85 (by decide) (by decide +kernel) (by decide +kernel)
def v697 : List ℕ := [w43,w101,w163,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b713 : Ban 60 5 v697 := viaBranch (ws := [v668,v669,v672,v675,v678,v679,v681,v683,v685,v686,v688,v690,v691,v692,v693,v695,v572,v696])
  (consBan b716 (consBan b717 (consBan b720 (consBan b723 (consBan b726 (consBan b727 (consBan b728 (consBan b729 (consBan b730 (consBan b731 (consBan b732 (consBan b733 (consBan b734 (consBan b735 (consBan b736 (consBan b737 (consBan b629 (consBan b738 (nilBan _ _)))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def proj48 : Projection 60 60 := pick [8,6,7,9,10,11,14,12,13,15,16,17,2,0,1,3,4,5,32,30,31,33,34,35,20,18,19,21,22,23,26,24,25,27,28,29,50,48,49,51,52,53,38,36,37,39,40,41,44,42,43,45,46,47,56,54,55,57,58,59] rfl (by decide +kernel) (by decide)
def proj49 : Projection 60 60 := pick [13,14,12,15,16,17,1,2,0,3,4,5,7,8,6,9,10,11,25,26,24,27,28,29,31,32,30,33,34,35,19,20,18,21,22,23,43,44,42,45,46,47,49,50,48,51,52,53,37,38,36,39,40,41,55,56,54,57,58,59] rfl (by decide +kernel) (by decide)
def v698 : List ℕ := [w65,w45,w164,w153,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b739 : Ban 60 5 v698 := viaPerm proj48 proj49 b713 (by decide +kernel) (by decide +kernel)
def v699 : List ℕ := [w43,w44,w45,w164,w153,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b664 : Ban 60 6 v699 := viaBranch (ws := [v609,v611,v614,v617,v618,v619,v620,v621,v622,v623,v624,v625,v626,v627,v629,v631,v632,v633,v634,v636,v637,v639,v641,v642,v643,v644,v645,v646,v648,v649,v650,v653,v654,v656,v657,v658,v659,v660,v662,v664,v665,v698])
  (consBan b665 (consBan b666 (consBan b669 (consBan b672 (consBan b673 (consBan b674 (consBan b675 (consBan b676 (consBan b677 (consBan b678 (consBan b679 (consBan b680 (consBan b681 (consBan b682 (consBan b683 (consBan b684 (consBan b685 (consBan b686 (consBan b687 (consBan b688 (consBan b689 (consBan b690 (consBan b691 (consBan b692 (consBan b693 (consBan b694 (consBan b695 (consBan b696 (consBan b697 (consBan b698 (consBan b699 (consBan b702 (consBan b703 (consBan b704 (consBan b705 (consBan b706 (consBan b707 (consBan b708 (consBan b710 (consBan b711 (consBan b712 (consBan b739 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def v700 : List ℕ := [w43,w65,w45,w163,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b740 : Ban 60 6 v700 := viaPerm proj37 proj36 b664 (by decide +kernel) (by decide +kernel)
def proj50 : Projection 60 60 := pick [18,21,22,19,20,23,36,39,40,37,38,41,54,57,58,55,56,59,0,3,4,1,2,5,24,27,28,25,26,29,42,45,46,43,44,47,6,9,10,7,8,11,30,33,34,31,32,35,48,51,52,49,50,53,12,15,16,13,14,17] rfl (by decide +kernel) (by decide)
def v701 : List ℕ := [w43,w65,w101,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b741 : Ban 60 6 v701 := viaPerm proj50 proj50 b664 (by decide +kernel) (by decide +kernel)
def v702 : List ℕ := [w64,w44,w65,w45,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b742 : Ban 60 6 v702 := viaCut proj19 petit40 (by decide) (by decide +kernel) (by decide +kernel)
def v703 : List ℕ := [w44,w65,w45,w100,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b743 : Ban 60 6 v703 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v704 : List ℕ := [w44,w65,w45,w46,w164,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b744 : Ban 60 6 v704 := viaCut proj21 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def proj51 : Projection 60 60 := pick [32,33,31,34,30,35,14,15,13,16,12,17,26,27,25,28,24,29,50,51,49,52,48,53,56,57,55,58,54,59,44,45,43,46,42,47,8,9,7,10,6,11,20,21,19,22,18,23,2,3,1,4,0,5,38,39,37,40,36,41] rfl (by decide +kernel) (by decide)
def proj52 : Projection 60 60 := pick [52,50,48,49,51,53,40,38,36,37,39,41,10,8,6,7,9,11,46,44,42,43,45,47,16,14,12,13,15,17,4,2,0,1,3,5,58,56,54,55,57,59,34,32,30,31,33,35,22,20,18,19,21,23,28,26,24,25,27,29] rfl (by decide +kernel) (by decide)
def v705 : List ℕ := [w44,w65,w45,w46,w141,w181,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b745 : Ban 60 6 v705 := viaPerm proj51 proj52 b414 (by decide +kernel) (by decide +kernel)
def v706 : List ℕ := [w44,w65,w45,w46,w141,w47,w150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b746 : Ban 60 6 v706 := viaPerm proj51 proj52 b610 (by decide +kernel) (by decide +kernel)
def v707 : List ℕ := [w44,w65,w45,w46,w181,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b747 : Ban 60 6 v707 := viaCut proj19 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def v708 : List ℕ := [w44,w65,w45,w164,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b748 : Ban 60 6 v708 := viaPerm proj46 proj47 b664 (by decide +kernel) (by decide +kernel)
def proj53 : Projection 60 60 := pick [25,27,28,24,26,29,43,45,46,42,44,47,55,57,58,54,56,59,1,3,4,0,2,5,19,21,22,18,20,23,37,39,40,36,38,41,13,15,16,12,14,17,31,33,34,30,32,35,49,51,52,48,50,53,7,9,10,6,8,11] rfl (by decide +kernel) (by decide)
def proj54 : Projection 60 60 := pick [21,18,22,19,20,23,57,54,58,55,56,59,39,36,40,37,38,41,27,24,28,25,26,29,3,0,4,1,2,5,45,42,46,43,44,47,33,30,34,31,32,35,9,6,10,7,8,11,51,48,52,49,50,53,15,12,16,13,14,17] rfl (by decide +kernel) (by decide)
def v709 : List ℕ := [w44,w65,w100,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b749 : Ban 60 6 v709 := viaPerm proj53 proj54 b664 (by decide +kernel) (by decide +kernel)
def v710 : List ℕ := [w43,w44,w65,w45,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b506 : Ban 60 7 v710 := viaBranch (ws := [v455,v456,v457,v458,v459,v460,v461,v499,v500,v501,v502,v503,v504,v505,v506,v507,v508,v509,v510,v511,v512,v513,v514,v515,v516,v517,v518,v519,v520,v521,v522,v523,v524,v525,v526,v527,v528,v276,v529,v530,v531,v532,v533,v448,v534,v535,v536,v538,v539,v540,v541,v542,v543,v354,v544,v546,v547,v548,v549,v585,v586,v587,v394,v588,v589,v590,v591,v592,v593,v594,v595,v596,v597,v598,v599,v600,v408,v601,v602,v603,v604,v605,v606,v607,v700,v701,v702,v703,v704,v705,v706,v707,v708,v709])
  (consBan b507 (consBan b508 (consBan b509 (consBan b510 (consBan b511 (consBan b512 (consBan b513 (consBan b554 (consBan b556 (consBan b557 (consBan b558 (consBan b559 (consBan b560 (consBan b561 (consBan b562 (consBan b563 (consBan b564 (consBan b565 (consBan b566 (consBan b567 (consBan b568 (consBan b569 (consBan b570 (consBan b571 (consBan b572 (consBan b573 (consBan b574 (consBan b575 (consBan b576 (consBan b577 (consBan b578 (consBan b580 (consBan b581 (consBan b582 (consBan b583 (consBan b584 (consBan b585 (consBan b586 (consBan b587 (consBan b588 (consBan b589 (consBan b590 (consBan b591 (consBan b592 (consBan b593 (consBan b594 (consBan b595 (consBan b597 (consBan b599 (consBan b600 (consBan b601 (consBan b602 (consBan b603 (consBan b410 (consBan b604 (consBan b606 (consBan b607 (consBan b608 (consBan b609 (consBan b639 (consBan b640 (consBan b641 (consBan b450 (consBan b642 (consBan b643 (consBan b644 (consBan b645 (consBan b646 (consBan b647 (consBan b648 (consBan b649 (consBan b651 (consBan b652 (consBan b653 (consBan b654 (consBan b655 (consBan b656 (consBan b657 (consBan b658 (consBan b659 (consBan b660 (consBan b661 (consBan b662 (consBan b663 (consBan b740 (consBan b741 (consBan b742 (consBan b743 (consBan b744 (consBan b745 (consBan b746 (consBan b747 (consBan b748 (consBan b749 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def w229 : ℕ := 0x41041041041041003ffff000000000
def v711 : List ℕ := [w43,w44,w65,w45,w46,w229,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b750 : Ban 60 7 v711 := viaCut proj22 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def w230 : ℕ := 0x410410410410410fc0fff000000000
def v712 : List ℕ := [w43,w44,w65,w45,w46,w230,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b751 : Ban 60 7 v712 := viaCut proj22 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v713 : List ℕ := [w43,w44,w65,w45,w46,w130,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b752 : Ban 60 7 v713 := viaCut proj22 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v714 : List ℕ := [w43,w44,w65,w45,w46,w210,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b753 : Ban 60 7 v714 := viaCut proj22 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def w231 : ℕ := 0x410410410410410ffffc0000000000
def v715 : List ℕ := [w43,w44,w65,w45,w46,w231,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b754 : Ban 60 7 v715 := viaCut proj22 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v716 : List ℕ := [w43,w44,w65,w45,w46,w47,w150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b755 : Ban 60 7 v716 := viaCut proj18 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def v717 : List ℕ := [w43,w44,w65,w45,w46,w47,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b756 : Ban 60 7 v717 := viaCut proj19 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def v718 : List ℕ := [w43,w44,w65,w45,w46,w47,w124]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b757 : Ban 60 7 v718 := viaPerm proj24 proj23 b329 (by decide +kernel) (by decide +kernel)
def v719 : List ℕ := [w43,w44,w65,w45,w46,w47,w125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b758 : Ban 60 7 v719 := viaPerm proj26 proj26 b506 (by decide +kernel) (by decide +kernel)
def v720 : List ℕ := [w43,w44,w65,w45,w46,w47,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b759 : Ban 60 7 v720 := viaPerm proj23 proj24 b506 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b760 : Ban 60 7 v397 := viaCut proj20 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v721 : List ℕ := [w42,w43,w44,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b762 : Ban 60 6 v721 := viaCut proj18 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v722 : List ℕ := [w48,w43,w44,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b763 : Ban 60 6 v722 := viaCut proj18 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v723 : List ℕ := [w49,w43,w44,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b764 : Ban 60 6 v723 := viaCut proj19 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v724 : List ℕ := [w50,w43,w44,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b765 : Ban 60 6 v724 := viaCut proj18 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v725 : List ℕ := [w51,w43,w44,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b766 : Ban 60 6 v725 := viaCut proj19 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v726 : List ℕ := [w52,w43,w44,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b767 : Ban 60 6 v726 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v727 : List ℕ := [w103,w43,w44,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b768 : Ban 60 6 v727 := viaCut proj21 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def v728 : List ℕ := [w103,w43,w44,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b769 : Ban 60 6 v728 := viaCut proj21 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def v729 : List ℕ := [w53,w43,w44,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b770 : Ban 60 6 v729 := viaCut proj18 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v730 : List ℕ := [w54,w43,w44,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b771 : Ban 60 6 v730 := viaCut proj19 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v731 : List ℕ := [w55,w43,w44,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b772 : Ban 60 6 v731 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v732 : List ℕ := [w104,w43,w44,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b773 : Ban 60 6 v732 := viaCut proj22 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def v733 : List ℕ := [w104,w43,w44,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b774 : Ban 60 6 v733 := viaCut proj22 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def v734 : List ℕ := [w56,w43,w44,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b775 : Ban 60 6 v734 := viaCut proj21 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def v735 : List ℕ := [w57,w43,w44,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b776 : Ban 60 6 v735 := viaCut proj18 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v736 : List ℕ := [w57,w44,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b777 : Ban 60 6 v736 := viaCut proj18 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v737 : List ℕ := [w58,w43,w44,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b778 : Ban 60 6 v737 := viaCut proj18 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v738 : List ℕ := [w58,w44,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b779 : Ban 60 6 v738 := viaCut proj18 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v739 : List ℕ := [w59,w43,w44,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b780 : Ban 60 6 v739 := viaCut proj18 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v740 : List ℕ := [w43,w61,w44,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b781 : Ban 60 6 v740 := viaCut proj19 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v741 : List ℕ := [w43,w61,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b782 : Ban 60 6 v741 := viaCut proj19 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v742 : List ℕ := [w43,w62,w44,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b783 : Ban 60 6 v742 := viaCut proj19 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v743 : List ℕ := [w43,w62,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b784 : Ban 60 6 v743 := viaCut proj19 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v744 : List ℕ := [w43,w63,w44,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b785 : Ban 60 6 v744 := viaCut proj19 petit6 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b786 : Ban 60 6 v274 := viaCut proj18 petit10 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b787 : Ban 60 6 v446 := viaCut proj18 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v745 : List ℕ := [w43,w44,w95,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b788 : Ban 60 6 v745 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v746 : List ℕ := [w43,w44,w95,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b789 : Ban 60 6 v746 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v747 : List ℕ := [w43,w44,w96,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b790 : Ban 60 6 v747 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v748 : List ℕ := [w43,w44,w96,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b791 : Ban 60 6 v748 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v749 : List ℕ := [w43,w44,w98,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b792 : Ban 60 6 v749 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v750 : List ℕ := [w43,w44,w99,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b793 : Ban 60 6 v750 := viaCut proj20 petit6 (by decide) (by decide +kernel) (by decide +kernel)
def v751 : List ℕ := [w43,w44,w45,w105,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b794 : Ban 60 6 v751 := viaCut proj19 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v752 : List ℕ := [w43,w44,w45,w105,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b795 : Ban 60 6 v752 := viaCut proj20 petit10 (by decide) (by decide +kernel) (by decide +kernel)
def v753 : List ℕ := [w43,w44,w45,w100,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b796 : Ban 60 6 v753 := viaCut proj18 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v754 : List ℕ := [w43,w44,w45,w106,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b797 : Ban 60 6 v754 := viaCut proj18 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v755 : List ℕ := [w43,w44,w45,w106,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b798 : Ban 60 6 v755 := viaCut proj19 petit12 (by decide) (by decide +kernel) (by decide +kernel)
def v756 : List ℕ := [w43,w44,w45,w101,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b799 : Ban 60 6 v756 := viaCut proj18 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v757 : List ℕ := [w43,w44,w45,w109,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b800 : Ban 60 6 v757 := viaCut proj22 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def v758 : List ℕ := [w43,w44,w45,w109,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b801 : Ban 60 6 v758 := viaCut proj18 petit13 (by decide) (by decide +kernel) (by decide +kernel)
def v759 : List ℕ := [w43,w44,w45,w110,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b802 : Ban 60 6 v759 := viaCut proj21 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def v760 : List ℕ := [w43,w44,w45,w110,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b803 : Ban 60 6 v760 := viaCut proj18 petit14 (by decide) (by decide +kernel) (by decide +kernel)
def v761 : List ℕ := [w43,w44,w45,w102,w165,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b804 : Ban 60 6 v761 := viaCut proj21 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def v762 : List ℕ := [w43,w44,w45,w102,w111,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b805 : Ban 60 6 v762 := viaCut proj21 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def v763 : List ℕ := [w43,w44,w45,w102,w166,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b806 : Ban 60 6 v763 := viaCut proj21 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def v764 : List ℕ := [w43,w44,w45,w102,w167,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b807 : Ban 60 6 v764 := viaCut proj21 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def v765 : List ℕ := [w43,w44,w45,w102,w168,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b808 : Ban 60 6 v765 := viaCut proj21 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def v766 : List ℕ := [w43,w44,w45,w102,w46,w164,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b809 : Ban 60 6 v766 := viaCut proj18 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v767 : List ℕ := [w43,w44,w45,w102,w46,w163,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b810 : Ban 60 6 v767 := viaCut proj19 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v768 : List ℕ := [w43,w44,w45,w102,w46,w121,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b811 : Ban 60 6 v768 := viaCut proj21 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def v769 : List ℕ := [w43,w44,w45,w102,w46,w229,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b812 : Ban 60 6 v769 := viaCut proj22 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def v770 : List ℕ := [w43,w44,w45,w102,w46,w122,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b813 : Ban 60 6 v770 := viaCut proj22 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def v771 : List ℕ := [w43,w44,w45,w102,w46,w230,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b814 : Ban 60 6 v771 := viaCut proj22 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def v772 : List ℕ := [w43,w44,w45,w102,w46,w210,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b815 : Ban 60 6 v772 := viaCut proj22 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def v773 : List ℕ := [w43,w44,w45,w102,w46,w231,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b816 : Ban 60 6 v773 := viaCut proj22 petit7 (by decide) (by decide +kernel) (by decide +kernel)
def v774 : List ℕ := [w43,w44,w45,w102,w46,w47,w150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b817 : Ban 60 6 v774 := viaCut proj18 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v775 : List ℕ := [w43,w44,w45,w102,w46,w47,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b818 : Ban 60 6 v775 := viaCut proj19 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v776 : List ℕ := [w43,w44,w45,w102,w46,w47,w125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b819 : Ban 60 6 v776 := viaCut proj20 petit2 (by decide) (by decide +kernel) (by decide +kernel)
def v777 : List ℕ := [w43,w44,w45,w102,w46,w47,w123]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b820 : Ban 60 6 v777 := viaCut proj22 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def v778 : List ℕ := [w43,w44,w45,w102,w46,w47,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b821 : Ban 60 6 v778 := viaCut proj21 petit15 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b822 : Ban 60 6 v407 := viaCut proj21 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def v779 : List ℕ := [w43,w44,w45,w46,w122,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b823 : Ban 60 6 v779 := viaCut proj22 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def v780 : List ℕ := [w43,w44,w45,w46,w47,w123]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b824 : Ban 60 6 v780 := viaCut proj22 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def v781 : List ℕ := [w43,w44,w102,w46,w47,w125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b825 : Ban 60 6 v781 := viaCut proj22 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def v782 : List ℕ := [w43,w45,w105,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b826 : Ban 60 6 v782 := viaCut proj20 petit11 (by decide) (by decide +kernel) (by decide +kernel)
def v783 : List ℕ := [w43,w45,w102,w46,w163,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b827 : Ban 60 6 v783 := viaCut proj21 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def v784 : List ℕ := [w43,w45,w102,w46,w47,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b828 : Ban 60 6 v784 := viaCut proj22 petit15 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit86 : Wide 30 5 v53 := viaSub (ws := [v53])
  (consBan b492 (nilBan _ _))
  (by decide) (by decide +kernel)
def v785 : List ℕ := [w44,w45,w106,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b829 : Ban 60 6 v785 := viaCut proj19 petit86 (by decide) (by decide +kernel) (by decide +kernel)
def v786 : List ℕ := [w44,w45,w102,w46,w164,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b830 : Ban 60 6 v786 := viaCut proj21 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def v787 : List ℕ := [w44,w45,w102,w46,w47,w150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b831 : Ban 60 6 v787 := viaCut proj22 petit15 (by decide) (by decide +kernel) (by decide +kernel)
def v788 : List ℕ := [w43,w44,w45,w102,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b761 : Ban 60 7 v788 := viaBranch (ws := [v721,v722,v723,v724,v725,v726,v727,v728,v729,v730,v731,v732,v733,v734,v735,v736,v737,v738,v739,v295,v740,v741,v742,v743,v744,v300,v305,v274,v306,v446,v745,v746,v747,v748,v749,v750,v751,v752,v753,v754,v755,v756,v757,v758,v759,v760,v761,v762,v763,v764,v765,v766,v767,v592,v768,v769,v770,v771,v772,v773,v774,v775,v776,v777,v778,v407,v408,v779,v780,v602,v781,v782,v783,v784,v785,v786,v787])
  (consBan b762 (consBan b763 (consBan b764 (consBan b765 (consBan b766 (consBan b767 (consBan b768 (consBan b769 (consBan b770 (consBan b771 (consBan b772 (consBan b773 (consBan b774 (consBan b775 (consBan b776 (consBan b777 (consBan b778 (consBan b779 (consBan b780 (consBan b343 (consBan b781 (consBan b782 (consBan b783 (consBan b784 (consBan b785 (consBan b348 (consBan b356 (consBan b786 (consBan b357 (consBan b787 (consBan b788 (consBan b789 (consBan b790 (consBan b791 (consBan b792 (consBan b793 (consBan b794 (consBan b795 (consBan b796 (consBan b797 (consBan b798 (consBan b799 (consBan b800 (consBan b801 (consBan b802 (consBan b803 (consBan b804 (consBan b805 (consBan b806 (consBan b807 (consBan b808 (consBan b809 (consBan b810 (consBan b646 (consBan b811 (consBan b812 (consBan b813 (consBan b814 (consBan b815 (consBan b816 (consBan b817 (consBan b818 (consBan b819 (consBan b820 (consBan b821 (consBan b822 (consBan b656 (consBan b823 (consBan b824 (consBan b658 (consBan b825 (consBan b826 (consBan b827 (consBan b828 (consBan b829 (consBan b830 (consBan b831 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def v789 : List ℕ := [w43,w44,w45,w142,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b832 : Ban 60 7 v789 := viaCut proj21 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v790 : List ℕ := [w43,w44,w45,w46,w143,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b833 : Ban 60 7 v790 := viaPerm proj34 proj34 b761 (by decide +kernel) (by decide +kernel)
def v791 : List ℕ := [w43,w44,w45,w46,w130,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b834 : Ban 60 7 v791 := viaCut proj22 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v792 : List ℕ := [w43,w44,w45,w46,w47,w124]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b835 : Ban 60 7 v792 := viaPerm proj24 proj23 b761 (by decide +kernel) (by decide +kernel)
def v793 : List ℕ := [w42,w43,w44,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b837 : Ban 60 6 v793 := viaCut proj18 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def v794 : List ℕ := [w48,w43,w44,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b838 : Ban 60 6 v794 := viaCut proj18 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def v795 : List ℕ := [w49,w43,w44,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b839 : Ban 60 6 v795 := viaCut proj19 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def v796 : List ℕ := [w50,w43,w44,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b840 : Ban 60 6 v796 := viaCut proj18 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def v797 : List ℕ := [w51,w43,w44,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b841 : Ban 60 6 v797 := viaCut proj19 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def v798 : List ℕ := [w52,w43,w44,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b842 : Ban 60 6 v798 := viaCut proj20 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def v799 : List ℕ := [w149,w43,w44,w45,w46,w150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b843 : Ban 60 6 v799 := viaCut proj18 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def v800 : List ℕ := [w149,w43,w44,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b844 : Ban 60 6 v800 := viaCut proj18 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def v801 : List ℕ := [w149,w44,w45,w46,w150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b845 : Ban 60 6 v801 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit87 : Wide 30 5 v34 := viaSub (ws := [v0,v34])
  (consBan b93 (consBan b71 (nilBan _ _)))
  (by decide) (by decide +kernel)
def v802 : List ℕ := [w149,w44,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b846 : Ban 60 6 v802 := viaCut proj18 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def v803 : List ℕ := [w152,w43,w44,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b847 : Ban 60 6 v803 := viaCut proj19 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def v804 : List ℕ := [w152,w43,w44,w45,w46,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b848 : Ban 60 6 v804 := viaCut proj19 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def v805 : List ℕ := [w152,w43,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b849 : Ban 60 6 v805 := viaCut proj19 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def v806 : List ℕ := [w152,w43,w45,w46,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b850 : Ban 60 6 v806 := viaCut proj19 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v807 : List ℕ := [w155,w43,w44,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b851 : Ban 60 6 v807 := viaCut proj20 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def w232 : ℕ := 0x3f00000003f000
def v808 : List ℕ := [w232,w43,w44,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b852 : Ban 60 6 v808 := viaCut proj20 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def w233 : ℕ := 0xfc0000000fc0000
def v809 : List ℕ := [w233,w43,w44,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b853 : Ban 60 6 v809 := viaCut proj21 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def w234 : ℕ := 0xfc000003f000000
def v810 : List ℕ := [w234,w43,w44,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b854 : Ban 60 6 v810 := viaCut proj21 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def v811 : List ℕ := [w202,w43,w44,w45,w46,w150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b855 : Ban 60 6 v811 := viaCut proj18 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def v812 : List ℕ := [w202,w43,w44,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b856 : Ban 60 6 v812 := viaCut proj18 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def v813 : List ℕ := [w58,w43,w44,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b857 : Ban 60 6 v813 := viaCut proj18 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def v814 : List ℕ := [w58,w44,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b858 : Ban 60 6 v814 := viaCut proj18 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def v815 : List ℕ := [w59,w43,w44,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b859 : Ban 60 6 v815 := viaCut proj18 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def v816 : List ℕ := [w59,w44,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b860 : Ban 60 6 v816 := viaCut proj18 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def v817 : List ℕ := [w60,w43,w44,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b861 : Ban 60 6 v817 := viaCut proj18 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def v818 : List ℕ := [w60,w44,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b862 : Ban 60 6 v818 := viaCut proj18 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def w235 : ℕ := 0x8208208208208200000003f03f000
def v819 : List ℕ := [w43,w235,w44,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b863 : Ban 60 6 v819 := viaCut proj19 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def v820 : List ℕ := [w43,w235,w44,w45,w46,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b864 : Ban 60 6 v820 := viaCut proj19 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def v821 : List ℕ := [w43,w62,w44,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b865 : Ban 60 6 v821 := viaCut proj19 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def v822 : List ℕ := [w43,w62,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b866 : Ban 60 6 v822 := viaCut proj19 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def v823 : List ℕ := [w43,w63,w44,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b867 : Ban 60 6 v823 := viaCut proj19 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def v824 : List ℕ := [w43,w63,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b868 : Ban 60 6 v824 := viaCut proj19 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def v825 : List ℕ := [w43,w64,w44,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b869 : Ban 60 6 v825 := viaCut proj19 petit31 (by decide) (by decide +kernel) (by decide +kernel)
def v826 : List ℕ := [w43,w64,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b870 : Ban 60 6 v826 := viaCut proj18 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def v827 : List ℕ := [w43,w44,w65,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b871 : Ban 60 6 v827 := viaCut proj18 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def w236 : ℕ := 0x104104104104104000000fc0000fc0
def v828 : List ℕ := [w43,w44,w236,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b872 : Ban 60 6 v828 := viaCut proj20 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def w237 : ℕ := 0x104104104104104000000fc003f000
def v829 : List ℕ := [w43,w44,w237,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b873 : Ban 60 6 v829 := viaCut proj20 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def v830 : List ℕ := [w43,w44,w96,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b874 : Ban 60 6 v830 := viaCut proj20 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def v831 : List ℕ := [w43,w44,w98,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b875 : Ban 60 6 v831 := viaCut proj20 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def v832 : List ℕ := [w43,w44,w99,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b876 : Ban 60 6 v832 := viaCut proj20 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def v833 : List ℕ := [w43,w44,w45,w100,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b877 : Ban 60 6 v833 := viaCut proj18 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def v834 : List ℕ := [w43,w44,w45,w101,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b878 : Ban 60 6 v834 := viaCut proj19 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def v835 : List ℕ := [w43,w44,w45,w204,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b879 : Ban 60 6 v835 := viaCut proj21 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def w238 : ℕ := 0x208208208208208000000fff000000
def v836 : List ℕ := [w43,w44,w45,w238,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b880 : Ban 60 6 v836 := viaCut proj21 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def v837 : List ℕ := [w43,w44,w45,w166,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b881 : Ban 60 6 v837 := viaCut proj21 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def v838 : List ℕ := [w43,w44,w45,w167,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b882 : Ban 60 6 v838 := viaCut proj21 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def v839 : List ℕ := [w43,w44,w45,w168,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b883 : Ban 60 6 v839 := viaCut proj21 petit17 (by decide) (by decide +kernel) (by decide +kernel)
def v840 : List ℕ := [w43,w44,w45,w46,w164,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b884 : Ban 60 6 v840 := viaCut proj18 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def v841 : List ℕ := [w43,w44,w45,w46,w163,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b885 : Ban 60 6 v841 := viaCut proj19 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def proj55 : Projection 60 60 := pick [32,33,30,31,34,35,8,9,6,7,10,11,20,21,18,19,22,23,14,15,12,13,16,17,26,27,24,25,28,29,2,3,0,1,4,5,50,51,48,49,52,53,56,57,54,55,58,59,38,39,36,37,40,41,44,45,42,43,46,47] rfl (by decide +kernel) (by decide)
def v842 : List ℕ := [w43,w44,w45,w46,w141,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b886 : Ban 60 6 v842 := viaPerm proj55 proj55 b610 (by decide +kernel) (by decide +kernel)
def v843 : List ℕ := [w43,w44,w45,w46,w210,w150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b887 : Ban 60 6 v843 := viaCut proj22 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v844 : List ℕ := [w43,w44,w45,w46,w210,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b888 : Ban 60 6 v844 := viaCut proj22 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v845 : List ℕ := [w43,w44,w45,w46,w231,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b889 : Ban 60 6 v845 := viaCut proj22 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v846 : List ℕ := [w43,w44,w45,w46,w231,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b890 : Ban 60 6 v846 := viaCut proj22 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v847 : List ℕ := [w43,w44,w45,w46,w157]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b891 : Ban 60 6 v847 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v848 : List ℕ := [w43,w44,w45,w46,w157,w150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b892 : Ban 60 6 v848 := viaCut proj18 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v849 : List ℕ := [w43,w44,w45,w46,w157,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b893 : Ban 60 6 v849 := viaCut proj18 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def v850 : List ℕ := [w43,w44,w45,w46,w157,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b894 : Ban 60 6 v850 := viaCut proj19 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v851 : List ℕ := [w0,w1,w2,w39,w3,w20]
def v852 : List ℕ := [w0,w1,w2,w39,w20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b895 : Ban 30 5 v852 := viaPerm proj12 proj11 b289 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b896 : Ban 30 5 v851 := viaPerm proj12 proj11 b229 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit88 : Wide 30 5 v851 := viaSub (ws := [v0,v60,v852,v34,v851])
  (consBan b93 (consBan b68 (consBan b895 (consBan b71 (consBan b896 (nilBan _ _))))))
  (by decide) (by decide +kernel)
def w239 : ℕ := 0x45145145145145103ffff000000fff
def v853 : List ℕ := [w43,w44,w45,w46,w239,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b897 : Ban 60 6 v853 := viaCut proj18 petit88 (by decide) (by decide +kernel) (by decide +kernel)
def w240 : ℕ := 0x4a5294a41ff801f
def v854 : List ℕ := [w0,w1,w2,w3,w240]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b898 : Ban 30 5 v854 := viaPerm proj3 proj4 b363 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit89 : Wide 30 5 v854 := viaSub (ws := [v0,v854])
  (consBan b93 (consBan b898 (nilBan _ _)))
  (by decide) (by decide +kernel)
def v855 : List ℕ := [w43,w44,w45,w46,w239,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b899 : Ban 60 6 v855 := viaCut proj19 petit89 (by decide) (by decide +kernel) (by decide +kernel)
def v856 : List ℕ := [w0,w1,w2,w40,w3,w20]
def v857 : List ℕ := [w0,w1,w2,w40,w20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b900 : Ban 30 5 v857 := viaPerm proj15 proj16 b289 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b901 : Ban 30 5 v856 := viaPerm proj15 proj16 b229 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit90 : Wide 30 5 v856 := viaSub (ws := [v0,v61,v857,v34,v856])
  (consBan b93 (consBan b69 (consBan b900 (consBan b71 (consBan b901 (nilBan _ _))))))
  (by decide) (by decide +kernel)
def v858 : List ℕ := [w43,w44,w45,w46,w160,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b902 : Ban 60 6 v858 := viaCut proj18 petit90 (by decide) (by decide +kernel) (by decide +kernel)
def v859 : List ℕ := [w0,w1,w2,w3,w159]
def proj56 : Projection 30 30 := pick [15,18,17,16,19,5,8,7,6,9,25,28,27,26,29,0,3,2,1,4,20,23,22,21,24,10,13,12,11,14] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b903 : Ban 30 5 v859 := viaPerm proj56 proj56 b363 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit91 : Wide 30 5 v859 := viaSub (ws := [v0,v859])
  (consBan b93 (consBan b903 (nilBan _ _)))
  (by decide) (by decide +kernel)
def v860 : List ℕ := [w43,w44,w45,w46,w160,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b904 : Ban 60 6 v860 := viaCut proj19 petit91 (by decide) (by decide +kernel) (by decide +kernel)
def v861 : List ℕ := [w43,w44,w45,w46,w139,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b905 : Ban 60 6 v861 := viaCut proj19 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def w241 : ℕ := 0x49249249249249203ffff00003f03f
def v862 : List ℕ := [w43,w44,w45,w46,w150,w241]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b906 : Ban 60 6 v862 := viaCut proj18 petit89 (by decide) (by decide +kernel) (by decide +kernel)
def v863 : List ℕ := [w43,w44,w45,w46,w150,w241,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b907 : Ban 60 6 v863 := viaCut proj19 petit88 (by decide) (by decide +kernel) (by decide +kernel)
def v864 : List ℕ := [w43,w44,w45,w46,w150,w212]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b908 : Ban 60 6 v864 := viaCut proj18 petit91 (by decide) (by decide +kernel) (by decide +kernel)
def v865 : List ℕ := [w43,w44,w45,w46,w150,w212,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b909 : Ban 60 6 v865 := viaCut proj19 petit90 (by decide) (by decide +kernel) (by decide +kernel)
def v866 : List ℕ := [w43,w44,w45,w46,w150,w140,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b910 : Ban 60 6 v866 := viaCut proj18 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def v867 : List ℕ := [w43,w44,w45,w46,w150,w153,w124]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b911 : Ban 60 6 v867 := viaCut proj18 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def proj57 : Projection 60 60 := pick [1,0,2,3,4,5,13,12,14,15,16,17,7,6,8,9,10,11,25,24,26,27,28,29,19,18,20,21,22,23,31,30,32,33,34,35,43,42,44,45,46,47,37,36,38,39,40,41,49,48,50,51,52,53,55,54,56,57,58,59] rfl (by decide +kernel) (by decide)
def v868 : List ℕ := [w43,w44,w45,w46,w150,w153,w195]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b912 : Ban 60 6 v868 := viaPerm proj57 proj57 b473 (by decide +kernel) (by decide +kernel)
def v869 : List ℕ := [w43,w44,w45,w46,w150,w153,w196]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b913 : Ban 60 6 v869 := viaPerm proj34 proj34 b473 (by decide +kernel) (by decide +kernel)
def proj58 : Projection 60 60 := pick [1,0,3,2,4,5,25,24,27,26,28,29,19,18,21,20,22,23,13,12,15,14,16,17,7,6,9,8,10,11,31,30,33,32,34,35,43,42,45,44,46,47,37,36,39,38,40,41,55,54,57,56,58,59,49,48,51,50,52,53] rfl (by decide +kernel) (by decide)
def v870 : List ℕ := [w43,w44,w45,w46,w150,w153,w194]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b914 : Ban 60 6 v870 := viaPerm proj58 proj58 b473 (by decide +kernel) (by decide +kernel)
def v871 : List ℕ := [w43,w44,w45,w46,w150,w195]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b915 : Ban 60 6 v871 := viaCut proj18 petit16 (by decide) (by decide +kernel) (by decide +kernel)
def v872 : List ℕ := [w0,w1,w2,w3,w137]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b916 : Ban 30 5 v872 := viaPerm proj4 proj3 b382 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit92 : Wide 30 5 v872 := viaSub (ws := [v0,v872])
  (consBan b93 (consBan b916 (nilBan _ _)))
  (by decide) (by decide +kernel)
def v873 : List ℕ := [w43,w44,w45,w46,w150,w194]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b917 : Ban 60 6 v873 := viaCut proj18 petit92 (by decide) (by decide +kernel) (by decide +kernel)
def v874 : List ℕ := [w43,w44,w45,w46,w153,w151]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b918 : Ban 60 6 v874 := viaCut proj19 petit16 (by decide) (by decide +kernel) (by decide +kernel)
def v875 : List ℕ := [w43,w44,w45,w46,w153,w196]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b919 : Ban 60 6 v875 := viaCut proj19 petit92 (by decide) (by decide +kernel) (by decide +kernel)
def v876 : List ℕ := [w43,w65,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b920 : Ban 60 6 v876 := viaCut proj18 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def proj59 : Projection 60 60 := pick [6,8,9,10,7,11,18,20,21,22,19,23,30,32,33,34,31,35,36,38,39,40,37,41,48,50,51,52,49,53,54,56,57,58,55,59,0,2,3,4,1,5,12,14,15,16,13,17,24,26,27,28,25,29,42,44,45,46,43,47] rfl (by decide +kernel) (by decide)
def proj60 : Projection 60 60 := pick [36,40,37,38,39,41,0,4,1,2,3,5,42,46,43,44,45,47,6,10,7,8,9,11,48,52,49,50,51,53,12,16,13,14,15,17,18,22,19,20,21,23,54,58,55,56,57,59,24,28,25,26,27,29,30,34,31,32,33,35] rfl (by decide +kernel) (by decide)
def v877 : List ℕ := [w43,w45,w101,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b921 : Ban 60 6 v877 := viaPerm proj59 proj60 b664 (by decide +kernel) (by decide +kernel)
def v878 : List ℕ := [w43,w45,w46,w163,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b922 : Ban 60 6 v878 := viaPerm proj27 proj28 b664 (by decide +kernel) (by decide +kernel)
def v879 : List ℕ := [w43,w45,w46,w210,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b923 : Ban 60 6 v879 := viaCut proj22 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v880 : List ℕ := [w1,w2,w19,w3,w20]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b924 : Ban 30 5 v880 := viaPerm proj17 proj17 b281 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit93 : Wide 30 5 v880 := viaSub (ws := [v880])
  (consBan b924 (nilBan _ _))
  (by decide) (by decide +kernel)
def v881 : List ℕ := [w43,w45,w46,w139,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b925 : Ban 60 6 v881 := viaCut proj18 petit93 (by decide) (by decide +kernel) (by decide +kernel)
def v882 : List ℕ := [w44,w65,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b926 : Ban 60 6 v882 := viaCut proj19 petit87 (by decide) (by decide +kernel) (by decide +kernel)
def proj61 : Projection 60 60 := pick [13,14,15,16,12,17,25,26,27,28,24,29,31,32,33,34,30,35,43,44,45,46,42,47,49,50,51,52,48,53,55,56,57,58,54,59,1,2,3,4,0,5,7,8,9,10,6,11,19,20,21,22,18,23,37,38,39,40,36,41] rfl (by decide +kernel) (by decide)
def proj62 : Projection 60 60 := pick [40,36,37,38,39,41,46,42,43,44,45,47,4,0,1,2,3,5,52,48,49,50,51,53,10,6,7,8,9,11,16,12,13,14,15,17,58,54,55,56,57,59,22,18,19,20,21,23,28,24,25,26,27,29,34,30,31,32,33,35] rfl (by decide +kernel) (by decide)
def v883 : List ℕ := [w44,w45,w100,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b927 : Ban 60 6 v883 := viaPerm proj61 proj62 b664 (by decide +kernel) (by decide +kernel)
def v884 : List ℕ := [w44,w45,w46,w164,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b928 : Ban 60 6 v884 := viaPerm proj30 proj31 b664 (by decide +kernel) (by decide +kernel)
def v885 : List ℕ := [w44,w45,w46,w231,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b929 : Ban 60 6 v885 := viaCut proj22 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v886 : List ℕ := [w44,w45,w46,w150,w140,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b930 : Ban 60 6 v886 := viaCut proj19 petit93 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit94 : Wide 30 3 v368 := viaSearch (by decide +kernel)
def v887 : List ℕ := [w42,w43,w44,w141,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b932 : Ban 60 5 v887 := viaCut proj18 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def v888 : List ℕ := [w169,w43,w44,w141,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b933 : Ban 60 5 v888 := viaCut proj18 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def v889 : List ℕ := [w170,w43,w44,w141,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b934 : Ban 60 5 v889 := viaCut proj19 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def w242 : ℕ := 0x3f000000fc0
def v890 : List ℕ := [w242,w43,w44,w141,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b935 : Ban 60 5 v890 := viaCut proj18 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def v891 : List ℕ := [w197,w43,w44,w141,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b936 : Ban 60 5 v891 := viaCut proj18 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def w243 : ℕ := 0xfc000003f000
def v892 : List ℕ := [w243,w43,w44,w141,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b937 : Ban 60 5 v892 := viaCut proj19 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def v893 : List ℕ := [w198,w43,w44,w141,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b938 : Ban 60 5 v893 := viaCut proj19 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def w244 : ℕ := 0x41041041041041000000000000fff
def v894 : List ℕ := [w244,w43,w44,w141,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b939 : Ban 60 5 v894 := viaCut proj18 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def w245 : ℕ := 0x41041041041041000000000fc003f
def v895 : List ℕ := [w245,w43,w44,w141,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b940 : Ban 60 5 v895 := viaCut proj18 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def v896 : List ℕ := [w174,w43,w44,w141,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b941 : Ban 60 5 v896 := viaCut proj18 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def v897 : List ℕ := [w60,w43,w44,w141,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b942 : Ban 60 5 v897 := viaCut proj18 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def w246 : ℕ := 0x8208208208208200000000003f03f
def v898 : List ℕ := [w43,w246,w44,w141,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b943 : Ban 60 5 v898 := viaCut proj19 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def w247 : ℕ := 0x8208208208208200000003f00003f
def v899 : List ℕ := [w43,w247,w44,w141,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b944 : Ban 60 5 v899 := viaCut proj19 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def v900 : List ℕ := [w43,w175,w44,w141,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b945 : Ban 60 5 v900 := viaCut proj19 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def v901 : List ℕ := [w43,w64,w44,w141,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b946 : Ban 60 5 v901 := viaCut proj19 petit94 (by decide) (by decide +kernel) (by decide +kernel)
def w248 : ℕ := 0x10410410410410400000000003ffc0
def v902 : List ℕ := [w43,w44,w248,w141,w125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b947 : Ban 60 5 v902 := viaCut proj20 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def v903 : List ℕ := [w43,w44,w248,w141,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b948 : Ban 60 5 v903 := viaCut proj20 petit44 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit95 : Wide 30 5 v64 := viaSub (ws := [v0,v64])
  (consBan b93 (consBan b73 (nilBan _ _)))
  (by decide) (by decide +kernel)
def w249 : ℕ := 0x104104104104104fff000fc003ffc0
def v904 : List ℕ := [w43,w44,w249,w141,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b949 : Ban 60 5 v904 := viaCut proj21 petit95 (by decide) (by decide +kernel) (by decide +kernel)
def v905 : List ℕ := [w43,w44,w249,w141,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b950 : Ban 60 5 v905 := viaCut proj21 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v906 : List ℕ := [w43,w44,w249,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b951 : Ban 60 5 v906 := viaCut proj22 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v907 : List ℕ := [w43,w44,w249,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b952 : Ban 60 5 v907 := viaCut proj21 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def w250 : ℕ := 0x20820820820820800000003ffc0000
def v908 : List ℕ := [w43,w44,w250,w141,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b953 : Ban 60 5 v908 := viaCut proj21 petit44 (by decide) (by decide +kernel) (by decide +kernel)
def v909 : List ℕ := [w43,w44,w250,w141,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b954 : Ban 60 5 v909 := viaCut proj21 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def w251 : ℕ := 0x208208208208208fff000ffffc0000
def v910 : List ℕ := [w43,w44,w251,w141,w125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b955 : Ban 60 5 v910 := viaCut proj20 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v911 : List ℕ := [w43,w44,w251,w141,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b956 : Ban 60 5 v911 := viaCut proj20 petit95 (by decide) (by decide +kernel) (by decide +kernel)
def v912 : List ℕ := [w43,w44,w251,w125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b957 : Ban 60 5 v912 := viaCut proj20 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v913 : List ℕ := [w43,w44,w251,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b958 : Ban 60 5 v913 := viaCut proj22 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v914 : List ℕ := [w43,w44,w179,w141,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b959 : Ban 60 5 v914 := viaCut proj19 petit50 (by decide) (by decide +kernel) (by decide +kernel)
def v915 : List ℕ := [w0,w1,w2,w3,w213]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b960 : Ban 30 5 v915 := viaPerm proj7 proj7 b363 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit96 : Wide 30 5 v915 := viaSub (ws := [v0,v915])
  (consBan b93 (consBan b960 (nilBan _ _)))
  (by decide) (by decide +kernel)
def v916 : List ℕ := [w43,w44,w179,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b961 : Ban 60 5 v916 := viaCut proj22 petit96 (by decide) (by decide +kernel) (by decide +kernel)
def v917 : List ℕ := [w43,w44,w180,w141,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b962 : Ban 60 5 v917 := viaCut proj18 petit50 (by decide) (by decide +kernel) (by decide +kernel)
def v918 : List ℕ := [w0,w1,w2,w3,w136]
def proj63 : Projection 30 30 := pick [27,28,26,25,29,12,13,11,10,14,22,23,21,20,24,7,8,6,5,9,17,18,16,15,19,2,3,1,0,4] rfl (by decide +kernel) (by decide)
def proj64 : Projection 30 30 := pick [28,27,25,26,29,18,17,15,16,19,8,7,5,6,9,23,22,20,21,24,13,12,10,11,14,3,2,0,1,4] rfl (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b963 : Ban 30 5 v918 := viaPerm proj63 proj64 b363 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem petit97 : Wide 30 5 v918 := viaSub (ws := [v0,v918])
  (consBan b93 (consBan b963 (nilBan _ _)))
  (by decide) (by decide +kernel)
def v919 : List ℕ := [w43,w44,w180,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b964 : Ban 60 5 v919 := viaCut proj22 petit97 (by decide) (by decide +kernel) (by decide +kernel)
def v920 : List ℕ := [w43,w44,w141,w181,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b965 : Ban 60 5 v920 := viaCut proj18 petit50 (by decide) (by decide +kernel) (by decide +kernel)
def v921 : List ℕ := [w43,w44,w141,w182,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b966 : Ban 60 5 v921 := viaCut proj19 petit50 (by decide) (by decide +kernel) (by decide +kernel)
def v922 : List ℕ := [w43,w44,w141,w183,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b967 : Ban 60 5 v922 := viaCut proj22 petit44 (by decide) (by decide +kernel) (by decide +kernel)
def v923 : List ℕ := [w43,w44,w141,w189]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b968 : Ban 60 5 v923 := viaCut proj20 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v924 : List ℕ := [w43,w44,w141,w189,w125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b969 : Ban 60 5 v924 := viaCut proj20 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v925 : List ℕ := [w43,w44,w141,w189,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b970 : Ban 60 5 v925 := viaCut proj20 petit95 (by decide) (by decide +kernel) (by decide +kernel)
def v926 : List ℕ := [w43,w44,w141,w189,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b971 : Ban 60 5 v926 := viaCut proj21 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def w252 : ℕ := 0x514514514514514fff03ffc0000fc0
def v927 : List ℕ := [w43,w44,w141,w252,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b972 : Ban 60 5 v927 := viaCut proj19 petit50 (by decide) (by decide +kernel) (by decide +kernel)
def v928 : List ℕ := [w43,w44,w141,w252,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b973 : Ban 60 5 v928 := viaCut proj21 petit96 (by decide) (by decide +kernel) (by decide +kernel)
def v929 : List ℕ := [w43,w44,w141,w162,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b974 : Ban 60 5 v929 := viaCut proj18 petit50 (by decide) (by decide +kernel) (by decide +kernel)
def v930 : List ℕ := [w43,w44,w141,w162,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b975 : Ban 60 5 v930 := viaCut proj21 petit97 (by decide) (by decide +kernel) (by decide +kernel)
def v931 : List ℕ := [w43,w44,w141,w125,w151,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b976 : Ban 60 5 v931 := viaCut proj18 petit50 (by decide) (by decide +kernel) (by decide +kernel)
def v932 : List ℕ := [w43,w44,w141,w125,w195,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b977 : Ban 60 5 v932 := viaCut proj19 petit50 (by decide) (by decide +kernel) (by decide +kernel)
def v933 : List ℕ := [w43,w44,w141,w125,w218]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b978 : Ban 60 5 v933 := viaCut proj20 petit96 (by decide) (by decide +kernel) (by decide +kernel)
def v934 : List ℕ := [w43,w44,w141,w125,w218,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b979 : Ban 60 5 v934 := viaCut proj19 petit50 (by decide) (by decide +kernel) (by decide +kernel)
def v935 : List ℕ := [w43,w44,w141,w125,w219]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b980 : Ban 60 5 v935 := viaCut proj20 petit97 (by decide) (by decide +kernel) (by decide +kernel)
def v936 : List ℕ := [w43,w44,w141,w125,w219,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b981 : Ban 60 5 v936 := viaCut proj18 petit50 (by decide) (by decide +kernel) (by decide +kernel)
def v937 : List ℕ := [w43,w44,w141,w125,w186,w196]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b982 : Ban 60 5 v937 := viaCut proj18 petit50 (by decide) (by decide +kernel) (by decide +kernel)
def v938 : List ℕ := [w43,w44,w141,w125,w186,w194]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b983 : Ban 60 5 v938 := viaCut proj19 petit50 (by decide) (by decide +kernel) (by decide +kernel)
def v939 : List ℕ := [w43,w44,w141,w125,w186,w185]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b984 : Ban 60 5 v939 := viaCut proj20 petit95 (by decide) (by decide +kernel) (by decide +kernel)
def v940 : List ℕ := [w43,w44,w141,w125,w196]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b985 : Ban 60 5 v940 := viaCut proj20 petit92 (by decide) (by decide +kernel) (by decide +kernel)
def v941 : List ℕ := [w43,w44,w141,w125,w194]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b986 : Ban 60 5 v941 := viaCut proj20 petit48 (by decide) (by decide +kernel) (by decide +kernel)
def v942 : List ℕ := [w43,w44,w141,w151,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b987 : Ban 60 5 v942 := viaCut proj21 petit92 (by decide) (by decide +kernel) (by decide +kernel)
def v943 : List ℕ := [w43,w44,w141,w195,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b988 : Ban 60 5 v943 := viaCut proj21 petit48 (by decide) (by decide +kernel) (by decide +kernel)
def v944 : List ℕ := [w43,w44,w181,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b989 : Ban 60 5 v944 := viaCut proj22 petit92 (by decide) (by decide +kernel) (by decide +kernel)
def v945 : List ℕ := [w43,w44,w182,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b990 : Ban 60 5 v945 := viaCut proj22 petit48 (by decide) (by decide +kernel) (by decide +kernel)
def v946 : List ℕ := [w43,w44,w183,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b991 : Ban 60 5 v946 := viaCut proj22 petit21 (by decide) (by decide +kernel) (by decide +kernel)
def v947 : List ℕ := [w43,w44,w141,w125,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b931 : Ban 60 6 v947 := viaBranch (ws := [v887,v888,v889,v890,v891,v892,v893,v894,v895,v896,v897,v898,v899,v900,v901,v555,v902,v903,v904,v905,v906,v907,v908,v909,v910,v911,v912,v913,v914,v916,v917,v919,v920,v921,v922,v923,v924,v925,v926,v927,v928,v929,v930,v931,v932,v933,v934,v935,v936,v937,v938,v939,v940,v941,v942,v943,v944,v945,v946])
  (consBan b932 (consBan b933 (consBan b934 (consBan b935 (consBan b936 (consBan b937 (consBan b938 (consBan b939 (consBan b940 (consBan b941 (consBan b942 (consBan b943 (consBan b944 (consBan b945 (consBan b946 (consBan b615 (consBan b947 (consBan b948 (consBan b949 (consBan b950 (consBan b951 (consBan b952 (consBan b953 (consBan b954 (consBan b955 (consBan b956 (consBan b957 (consBan b958 (consBan b959 (consBan b961 (consBan b962 (consBan b964 (consBan b965 (consBan b966 (consBan b967 (consBan b968 (consBan b969 (consBan b970 (consBan b971 (consBan b972 (consBan b973 (consBan b974 (consBan b975 (consBan b976 (consBan b977 (consBan b978 (consBan b979 (consBan b980 (consBan b981 (consBan b982 (consBan b983 (consBan b984 (consBan b985 (consBan b986 (consBan b987 (consBan b988 (consBan b989 (consBan b990 (consBan b991 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def v948 : List ℕ := [w65,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b992 : Ban 60 6 v948 := viaPerm proj55 proj55 b931 (by decide +kernel) (by decide +kernel)
def v949 : List ℕ := [w43,w44,w45,w46,w150,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b836 : Ban 60 7 v949 := viaBranch (ws := [v793,v794,v795,v796,v797,v798,v799,v800,v801,v802,v803,v804,v805,v806,v807,v808,v809,v810,v811,v812,v813,v814,v815,v816,v817,v818,v819,v820,v821,v822,v823,v824,v825,v826,v827,v828,v829,v830,v831,v832,v833,v834,v835,v836,v837,v838,v839,v840,v841,v842,v843,v844,v845,v846,v847,v848,v849,v850,v853,v855,v858,v860,v861,v862,v863,v864,v865,v866,v867,v436,v868,v869,v870,v871,v873,v874,v875,v876,v877,v878,v879,v881,v882,v883,v884,v885,v886,v948])
  (consBan b837 (consBan b838 (consBan b839 (consBan b840 (consBan b841 (consBan b842 (consBan b843 (consBan b844 (consBan b845 (consBan b846 (consBan b847 (consBan b848 (consBan b849 (consBan b850 (consBan b851 (consBan b852 (consBan b853 (consBan b854 (consBan b855 (consBan b856 (consBan b857 (consBan b858 (consBan b859 (consBan b860 (consBan b861 (consBan b862 (consBan b863 (consBan b864 (consBan b865 (consBan b866 (consBan b867 (consBan b868 (consBan b869 (consBan b870 (consBan b871 (consBan b872 (consBan b873 (consBan b874 (consBan b875 (consBan b876 (consBan b877 (consBan b878 (consBan b879 (consBan b880 (consBan b881 (consBan b882 (consBan b883 (consBan b884 (consBan b885 (consBan b886 (consBan b887 (consBan b888 (consBan b889 (consBan b890 (consBan b891 (consBan b892 (consBan b893 (consBan b894 (consBan b897 (consBan b899 (consBan b902 (consBan b904 (consBan b905 (consBan b906 (consBan b907 (consBan b908 (consBan b909 (consBan b910 (consBan b911 (consBan b473 (consBan b912 (consBan b913 (consBan b914 (consBan b915 (consBan b917 (consBan b918 (consBan b919 (consBan b920 (consBan b921 (consBan b922 (consBan b923 (consBan b925 (consBan b926 (consBan b927 (consBan b928 (consBan b929 (consBan b930 (consBan b992 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def v950 : List ℕ := [w43,w65,w45,w101,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b993 : Ban 60 7 v950 := viaPerm proj59 proj60 b836 (by decide +kernel) (by decide +kernel)
def v951 : List ℕ := [w43,w65,w45,w46,w163,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b994 : Ban 60 7 v951 := viaPerm proj27 proj28 b836 (by decide +kernel) (by decide +kernel)
def v952 : List ℕ := [w43,w65,w45,w46,w47,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b995 : Ban 60 7 v952 := viaPerm proj29 proj29 b836 (by decide +kernel) (by decide +kernel)
def v953 : List ℕ := [w64,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b996 : Ban 60 7 v953 := viaCut proj19 petit1 (by decide) (by decide +kernel) (by decide +kernel)
def v954 : List ℕ := [w44,w65,w45,w100,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b997 : Ban 60 7 v954 := viaPerm proj61 proj62 b836 (by decide +kernel) (by decide +kernel)
def v955 : List ℕ := [w44,w65,w45,w46,w164,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b998 : Ban 60 7 v955 := viaPerm proj30 proj31 b836 (by decide +kernel) (by decide +kernel)
def v956 : List ℕ := [w44,w65,w45,w46,w47,w150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b999 : Ban 60 7 v956 := viaPerm proj32 proj33 b836 (by decide +kernel) (by decide +kernel)
def v957 : List ℕ := [w43,w44,w65,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b92 : Ban 60 8 v957 := viaBranch (ws := [v83,v84,v85,v86,v87,v88,v89,v90,v91,v92,v93,v94,v95,v96,v97,v98,v99,v100,v101,v102,v103,v104,v105,v106,v107,v108,v78,v109,v110,v111,v112,v113,v114,v115,v116,v82,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v446,v447,v448,v449,v450,v451,v452,v453,v454,v710,v711,v712,v713,v714,v715,v716,v717,v718,v719,v720,v397,v788,v789,v790,v791,v792,v950,v951,v952,v953,v954,v955,v956])
  (consBan b111 (consBan b112 (consBan b113 (consBan b114 (consBan b115 (consBan b116 (consBan b117 (consBan b118 (consBan b119 (consBan b120 (consBan b121 (consBan b122 (consBan b123 (consBan b124 (consBan b125 (consBan b126 (consBan b127 (consBan b128 (consBan b129 (consBan b130 (consBan b131 (consBan b132 (consBan b133 (consBan b134 (consBan b135 (consBan b136 (consBan b137 (consBan b138 (consBan b139 (consBan b140 (consBan b141 (consBan b142 (consBan b143 (consBan b144 (consBan b145 (consBan b146 (consBan b314 (consBan b315 (consBan b317 (consBan b318 (consBan b320 (consBan b321 (consBan b322 (consBan b323 (consBan b324 (consBan b325 (consBan b326 (consBan b327 (consBan b328 (consBan b329 (consBan b498 (consBan b499 (consBan b500 (consBan b501 (consBan b502 (consBan b503 (consBan b504 (consBan b505 (consBan b506 (consBan b750 (consBan b751 (consBan b752 (consBan b753 (consBan b754 (consBan b755 (consBan b756 (consBan b757 (consBan b758 (consBan b759 (consBan b760 (consBan b761 (consBan b832 (consBan b833 (consBan b834 (consBan b835 (consBan b993 (consBan b994 (consBan b995 (consBan b996 (consBan b997 (consBan b998 (consBan b999 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
def v958 : List ℕ := [w43,w44,w95,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b1000 : Ban 60 8 v958 := viaCut proj20 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def v959 : List ℕ := [w43,w44,w96,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b1001 : Ban 60 8 v959 := viaCut proj20 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def v960 : List ℕ := [w43,w44,w98,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b1002 : Ban 60 8 v960 := viaCut proj20 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def v961 : List ℕ := [w43,w44,w99,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b1003 : Ban 60 8 v961 := viaCut proj20 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def proj65 : Projection 60 60 := pick [6,8,7,9,10,11,0,2,1,3,4,5,12,14,13,15,16,17,18,20,19,21,22,23,30,32,31,33,34,35,24,26,25,27,28,29,36,38,37,39,40,41,48,50,49,51,52,53,42,44,43,45,46,47,54,56,55,57,58,59] rfl (by decide +kernel) (by decide)
def v962 : List ℕ := [w43,w44,w45,w100,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b1004 : Ban 60 8 v962 := viaPerm proj65 proj65 b92 (by decide +kernel) (by decide +kernel)
def v963 : List ℕ := [w43,w44,w45,w101,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b1005 : Ban 60 8 v963 := viaPerm proj49 proj48 b92 (by decide +kernel) (by decide +kernel)
def v964 : List ℕ := [w43,w44,w45,w165,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b1006 : Ban 60 8 v964 := viaCut proj21 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def v965 : List ℕ := [w43,w44,w45,w166,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b1007 : Ban 60 8 v965 := viaCut proj21 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def v966 : List ℕ := [w43,w44,w45,w167,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b1008 : Ban 60 8 v966 := viaCut proj21 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def v967 : List ℕ := [w43,w44,w45,w168,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b1009 : Ban 60 8 v967 := viaCut proj21 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def v968 : List ℕ := [w43,w44,w45,w46,w164,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b1010 : Ban 60 8 v968 := viaPerm proj45 proj44 b92 (by decide +kernel) (by decide +kernel)
def proj66 : Projection 60 60 := pick [25,27,24,26,28,29,1,3,0,2,4,5,19,21,18,20,22,23,13,15,12,14,16,17,31,33,30,32,34,35,7,9,6,8,10,11,43,45,42,44,46,47,55,57,54,56,58,59,37,39,36,38,40,41,49,51,48,50,52,53] rfl (by decide +kernel) (by decide)
def proj67 : Projection 60 60 := pick [8,6,9,7,10,11,32,30,33,31,34,35,20,18,21,19,22,23,14,12,15,13,16,17,2,0,3,1,4,5,26,24,27,25,28,29,50,48,51,49,52,53,38,36,39,37,40,41,56,54,57,55,58,59,44,42,45,43,46,47] rfl (by decide +kernel) (by decide)
def v969 : List ℕ := [w43,w44,w45,w46,w163,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b1011 : Ban 60 8 v969 := viaPerm proj66 proj67 b92 (by decide +kernel) (by decide +kernel)
def v970 : List ℕ := [w43,w44,w45,w46,w141,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b1012 : Ban 60 8 v970 := viaPerm proj55 proj55 b92 (by decide +kernel) (by decide +kernel)
def v971 : List ℕ := [w43,w44,w45,w46,w229,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b1013 : Ban 60 8 v971 := viaCut proj22 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def v972 : List ℕ := [w43,w44,w45,w46,w230,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b1014 : Ban 60 8 v972 := viaCut proj22 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def v973 : List ℕ := [w43,w44,w45,w46,w210,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b1015 : Ban 60 8 v973 := viaCut proj22 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def v974 : List ℕ := [w43,w44,w45,w46,w231,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b1016 : Ban 60 8 v974 := viaCut proj22 petit0 (by decide) (by decide +kernel) (by decide +kernel)
def v975 : List ℕ := [w43,w44,w45,w46,w47,w150]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b1017 : Ban 60 8 v975 := viaPerm proj60 proj59 b92 (by decide +kernel) (by decide +kernel)
def proj68 : Projection 60 60 := pick [43,46,42,44,45,47,1,4,0,2,3,5,37,40,36,38,39,41,13,16,12,14,15,17,49,52,48,50,51,53,7,10,6,8,9,11,25,28,24,26,27,29,55,58,54,56,57,59,19,22,18,20,21,23,31,34,30,32,33,35] rfl (by decide +kernel) (by decide)
def proj69 : Projection 60 60 := pick [8,6,9,10,7,11,32,30,33,34,31,35,20,18,21,22,19,23,50,48,51,52,49,53,38,36,39,40,37,41,56,54,57,58,55,59,14,12,15,16,13,17,2,0,3,4,1,5,26,24,27,28,25,29,44,42,45,46,43,47] rfl (by decide +kernel) (by decide)
def v976 : List ℕ := [w43,w44,w45,w46,w47,w153]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b1018 : Ban 60 8 v976 := viaPerm proj68 proj69 b92 (by decide +kernel) (by decide +kernel)
def v977 : List ℕ := [w43,w44,w45,w46,w47,w125]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b1019 : Ban 60 8 v977 := viaPerm proj43 proj42 b92 (by decide +kernel) (by decide +kernel)
def proj70 : Projection 60 60 := pick [57,58,54,55,56,59,21,22,18,19,20,23,39,40,36,37,38,41,27,28,24,25,26,29,45,46,42,43,44,47,3,4,0,1,2,5,33,34,30,31,32,35,51,52,48,49,50,53,9,10,6,7,8,11,15,16,12,13,14,17] rfl (by decide +kernel) (by decide)
def proj71 : Projection 60 60 := pick [32,33,34,30,31,35,50,51,52,48,49,53,56,57,58,54,55,59,8,9,10,6,7,11,20,21,22,18,19,23,38,39,40,36,37,41,14,15,16,12,13,17,26,27,28,24,25,29,44,45,46,42,43,47,2,3,4,0,1,5] rfl (by decide +kernel) (by decide)
def v978 : List ℕ := [w43,w44,w45,w46,w47,w186]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b1020 : Ban 60 8 v978 := viaPerm proj70 proj71 b92 (by decide +kernel) (by decide +kernel)
def v979 : List ℕ := [w43,w44,w45,w46,w47]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem b1 : Ban 60 9 v979 := viaBranch (ws := [v65,v66,v67,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82,v957,v958,v959,v960,v961,v962,v963,v964,v965,v966,v967,v968,v969,v970,v971,v972,v973,v974,v975,v976,v977,v978])
  (consBan b74 (consBan b75 (consBan b76 (consBan b77 (consBan b78 (consBan b79 (consBan b80 (consBan b81 (consBan b82 (consBan b83 (consBan b84 (consBan b85 (consBan b86 (consBan b87 (consBan b88 (consBan b89 (consBan b90 (consBan b91 (consBan b92 (consBan b1000 (consBan b1001 (consBan b1002 (consBan b1003 (consBan b1004 (consBan b1005 (consBan b1006 (consBan b1007 (consBan b1008 (consBan b1009 (consBan b1010 (consBan b1011 (consBan b1012 (consBan b1013 (consBan b1014 (consBan b1015 (consBan b1016 (consBan b1017 (consBan b1018 (consBan b1019 (consBan b1020 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))
  (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem cinq : Wide 60 9 v979 := widen (by decide +kernel) b1
end PEqualNP.Outside.L_meta_12104.Support.Core0

namespace PEqualNP.Outside.L_meta_12104.Support.Core1

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

def t0 := 0x22d8b40d1fc7e07
def t1 := 0x324ffd24007fe00
def t2 := 0x346d1861e3f8e38
def t3 := 0x3b0ec301fc7f1c0
def t4 := 0x3ffc9249ff80000
def v0 := [t0,t1,t2,t3,t4]
def t5 := 0x2048100103c0e00
def v1 := [t5,t0,t1,t2,t3,t4]
def t6 := 0x9d21c0
def t7 := 0xb46fc7
def t8 := 0xdb0ff8
def t9 := 0xf24e00
def v2 := [t6,t7,t8,t9]
def t10 := 0x9421c0
def v3 := [t10,t6,t7,t8,t9]
def t11 := 0xbd6fc7
def v4 := [t6,t7,t11,t8,t9]
def t12 := 0x90000
def v5 := [t12,t6,t7,t8,t9]
def t13 := 0x204e07
def v6 := [t13,t6,t7,t8,t9]
def t14 := 0x9901c0
def v7 := [t14,t6,t7,t8,t9]
def t15 := 0xdf2ff8
def v8 := [t6,t7,t8,t15,t9]
def t16 := 0x42000
def v9 := [t16,t6,t7,t8,t9]
def t17 := 0x420e38
def v10 := [t17,t6,t7,t8,t9]
def t18 := 0x900000
def v11 := [t18,t6,t7,t8,t9]
def t19 := 0xff6fc0
def v12 := [t6,t7,t8,t9,t19]
def t20 := 0xd21c0
def v13 := [t20,t6,t7,t8,t9]
def t21 := 0x624e00
def v14 := [t21,t6,t7,t8,t9]
def t22 := 0x900fc0
def v15 := [t22,t6,t7,t8,t9]
def t23 := 0xff6fff
def v16 := [t6,t7,t8,t9,t23]
def t24 := 0x246007
def v17 := [t24,t6,t7,t8,t9]
def t25 := 0x4b0038
def v18 := [t25,t6,t7,t8,t9]
def t26 := 0xb04e00
def v19 := [t6,t26,t7,t8,t9]
def t27 := 0xf66fc7
def v20 := [t6,t7,t8,t9,t27]
def t28 := 0x421c7
def v21 := [t28,t6,t7,t8,t9]
def t29 := 0x420000
def v22 := [t29,t6,t7,t8,t9]
def t30 := 0xd20e00
def v23 := [t6,t7,t30,t8,t9]
def t31 := 0xfb4ff8
def v24 := [t6,t7,t8,t9,t31]
def t32 := 0x901f8
def v25 := [t32,t6,t7,t8,t9]
def t33 := 0x204000
def v26 := [t33,t6,t7,t8,t9]
def p31_29 : Projection 29 12 := pick [0,1,2,6,7,8,12,13,14,22,23,24] rfl (by decide +kernel) (by decide)
def t34 := 0x36fdbc6dffffe3f
def v27 := [t0,t1,t2,t34,t3,t4]
def v28 := [t5,t1,t34,t3,t4]
def v29 := [t5,t0,t1,t34,t3,t4]
def v30 := [t5,t1,t2,t34,t3,t4]
def map31_4 : Projection 29 29 := pick [3,4,5,0,1,2,6,7,8,10,9,11,15,16,17,12,13,14,18,20,19,21,25,26,27,22,23,24,28] rfl (by decide +kernel) (by decide)
def v31 := [t5,t0,t1,t2,t34,t3,t4]
def t35 := 0x290a40c1c07007
def v32 := [t35,t0,t1,t34,t3,t4]
def t36 := 0xd0340c0380e07
def t37 := 0x3bdef70dfffffc7
def v33 := [t36,t0,t1,t2,t37,t4]
def p31_30 : Projection 29 12 := pick [3,4,5,6,7,8,15,16,17,25,26,27] rfl (by decide +kernel) (by decide)
def map31_2 : Projection 29 29 := pick [0,1,2,6,7,8,3,4,5,12,13,14,9,10,11,16,15,17,18,22,23,24,19,20,21,26,25,27,28] rfl (by decide +kernel) (by decide)
def v34 := [t35,t0,t1,t2,t34,t3,t4]
def v35 := [t36,t0,t1,t2,t3,t37,t4]
def p31_27 : Projection 29 12 := pick [0,1,2,3,4,5,9,10,11,19,20,21] rfl (by decide +kernel) (by decide)
def t38 := 0x14250860e038038
def v36 := [t38,t1,t2,t34,t3,t4]
def map31_6 : Projection 29 29 := pick [3,4,5,6,7,8,0,1,2,15,16,17,10,9,11,13,12,14,18,25,26,27,20,19,21,23,22,24,28] rfl (by decide +kernel) (by decide)
def map31_8 : Projection 29 29 := pick [6,7,8,0,1,2,3,4,5,13,12,14,16,15,17,9,10,11,18,23,22,24,26,25,27,19,20,21,28] rfl (by decide +kernel) (by decide)
def v37 := [t38,t0,t1,t2,t34,t3,t4]
def t39 := 0x220880011c47000
def v38 := [t39,t0,t1,t2,t34,t3,t4]
def v39 := [t5,t0,t1,t2,t3,t37,t4]
def v40 := [t1,t2,t34,t3,t37,t4]
def t40 := 0x3f6fdb61ffffff8
def v41 := [t0,t1,t2,t37,t40,t4]
def v42 := [t5,t0,t1,t2,t37,t40,t4]
def v43 := [t1,t34,t37,t40,t4]
def t41 := 0x324dbc24007fe00
def v44 := [t41,t1,t34,t37,t40,t4]
def t42 := 0x36fffd6dffffe3f
def v45 := [t1,t34,t42,t37,t40,t4]
def t43 := 0x241000000000
def v46 := [t43,t1,t34,t37,t40,t4]
def t44 := 0x4b00049ff8003f
def v47 := [t44,t1,t34,t37,t40,t4]
def t45 := 0x324ef504007fe00
def v48 := [t45,t1,t34,t37,t40,t4]
def t46 := 0x3bdfff2dfffffc7
def v49 := [t1,t34,t37,t46,t40,t4]
def t47 := 0x108200000000
def v50 := [t47,t1,t34,t37,t40,t4]
def t48 := 0x9900209ff801c7
def v51 := [t48,t1,t34,t37,t40,t4]
def t49 := 0x324fd920007fe00
def v52 := [t49,t1,t34,t37,t40,t4]
def t50 := 0x3f6fff65ffffff8
def v53 := [t1,t34,t37,t40,t50,t4]
def t51 := 0x24040000000
def v54 := [t51,t1,t34,t37,t40,t4]
def t52 := 0xd200241ff801f8
def v55 := [t52,t1,t34,t37,t40,t4]
def t53 := 0x324c90000000000
def v56 := [t53,t1,t34,t37,t40,t4]
def t54 := 0x3fffff6dffffe00
def v57 := [t1,t34,t37,t40,t4,t54]
def t55 := 0x36d24007fe00
def v58 := [t55,t1,t34,t37,t40,t4]
def t56 := 0xdb00249ff80000
def v59 := [t56,t1,t34,t37,t40,t4]
def t57 := 0x32dcb40dffffe07
def v60 := [t1,t57,t40,t4]
def v61 := [t1,t57,t34,t40,t4]
def v62 := [t1,t57,t37,t40,t4]
def v63 := [t1,t57,t34,t37,t40,t4]
def t58 := 0x3fffff6dfffffff
def v64 := [t1,t34,t37,t40,t4,t58]
def t59 := 0x42108600000038
def v65 := [t59,t1,t34,t40,t4]
def v66 := [t59,t1,t34,t37,t40,t4]
def t60 := 0x902430000001c0
def v67 := [t60,t1,t37,t40,t4]
def v68 := [t60,t1,t34,t37,t40,t4]
def t61 := 0x366d9861ffffe38
def v69 := [t1,t61,t37,t4]
def v70 := [t1,t61,t34,t37,t4]
def v71 := [t1,t61,t37,t40,t4]
def v72 := [t1,t61,t34,t37,t40,t4]
def t62 := 0x90240c0000007
def v73 := [t62,t1,t34,t37,t4]
def v74 := [t62,t1,t34,t37,t40,t4]
def t63 := 0x36fc9049ff80000
def v75 := [t1,t63,t34,t37,t40,t4]
def t64 := 0x3ffdbe6dffffe3f
def v76 := [t1,t34,t37,t40,t4,t64]
def t65 := 0x12c24007fe3f
def v77 := [t65,t1,t34,t37,t40,t4]
def t66 := 0x90002000000000
def v78 := [t66,t1,t34,t37,t40,t4]
def t67 := 0x3b4ed301fffffc0
def v79 := [t1,t34,t67,t4]
def v80 := [t1,t34,t67,t37,t4]
def v81 := [t1,t34,t67,t40,t4]
def v82 := [t1,t34,t67,t37,t40,t4]
def t68 := 0x3bdc9209ff80000
def v83 := [t1,t34,t68,t37,t40,t4]
def t69 := 0x3ffef74dfffffc7
def v84 := [t1,t34,t37,t40,t4,t69]
def t70 := 0x26504007ffc7
def v85 := [t70,t1,t34,t37,t40,t4]
def t71 := 0x42000400000000
def v86 := [t71,t1,t34,t37,t40,t4]
def t72 := 0x3f6c9241ff80000
def v87 := [t1,t34,t37,t72,t40,t4]
def t73 := 0x3fffdb69ffffff8
def v88 := [t1,t34,t37,t40,t4,t73]
def t74 := 0x34920007fff8
def v89 := [t74,t1,t34,t37,t40,t4]
def t75 := 0x9000080000000
def v90 := [t75,t1,t34,t37,t40,t4]
def v91 := [t0,t1,t34,t37,t40,t4]
def v92 := [t1,t2,t34,t37,t40,t4]
def v93 := [t0,t1,t2,t34,t37,t40,t4]
def v94 := [t35,t1,t2,t37,t40,t4]
def v95 := [t35,t0,t1,t2,t37,t40,t4]
def v96 := [t38,t0,t1,t37,t40,t4]
def v97 := [t38,t0,t1,t2,t37,t40,t4]
def t76 := 0x2248b4040047e00
def v98 := [t76,t0,t1,t2,t37,t40,t4]
def t77 := 0x32dffd2d1fffe07
def v99 := [t0,t1,t77,t2,t37,t40,t4]
def t78 := 0x9000091f80007
def v100 := [t78,t0,t1,t2,t37,t40,t4]
def t79 := 0x100749200038000
def v101 := [t79,t0,t1,t2,t37,t40,t4]
def t80 := 0x19064300e0381c0
def v102 := [t80,t0,t1,t2,t40,t4]
def v103 := [t80,t1,t2,t37,t40,t4]
def v104 := [t80,t0,t1,t2,t37,t40,t4]
def t81 := 0x224890011fc7e00
def v105 := [t81,t1,t2,t37,t4]
def v106 := [t81,t0,t1,t2,t37,t4]
def v107 := [t81,t1,t2,t37,t40,t4]
def v108 := [t81,t0,t1,t2,t37,t40,t4]
def v109 := [t0,t1,t2,t37,t40,t4,t58]
def v110 := [t62,t0,t1,t2,t37,t4]
def v111 := [t62,t0,t1,t2,t37,t40,t4]
def t82 := 0x1d274b60e0381f8
def v112 := [t82,t1,t2,t37,t40,t4]
def v113 := [t82,t0,t1,t2,t37,t40,t4]
def t83 := 0x22d890091f80000
def v114 := [t83,t0,t1,t2,t37,t40,t4]
def t84 := 0x3ffcb64dffc7e07
def v115 := [t0,t1,t2,t37,t40,t4,t84]
def t85 := 0x24040047e07
def v116 := [t85,t0,t1,t2,t37,t40,t4]
def t86 := 0x1d240240e000000
def v117 := [t86,t0,t1,t2,t37,t40,t4]
def t87 := 0x304d18200078e00
def v118 := [t0,t87,t1,t2,t37,t40,t4]
def t88 := 0x366ffd65e3ffe38
def v119 := [t0,t1,t2,t88,t37,t40,t4]
def t89 := 0x4200041e380038
def v120 := [t89,t0,t1,t2,t37,t40,t4]
def t90 := 0x202e5040007000
def v121 := [t90,t0,t1,t2,t37,t40,t4]
def t91 := 0x304c1001e3f8e00
def v122 := [t0,t91,t1,t40,t4]
def v123 := [t0,t91,t1,t2,t40,t4]
def v124 := [t0,t91,t1,t37,t40,t4]
def v125 := [t0,t91,t1,t2,t37,t40,t4]
def v126 := [t59,t0,t1,t2,t40,t4]
def v127 := [t59,t0,t1,t2,t37,t40,t4]
def t92 := 0xb92e70c1c071c7
def v128 := [t92,t0,t1,t37,t40,t4]
def v129 := [t92,t0,t1,t2,t37,t40,t4]
def t93 := 0xb02c3001c071c0
def v130 := [t93,t0,t1,t2,t37,t4]
def v131 := [t93,t0,t1,t37,t40,t4]
def v132 := [t93,t0,t1,t2,t37,t40,t4]
def t94 := 0x346c1041e380000
def v133 := [t0,t1,t94,t2,t37,t40,t4]
def t95 := 0x3ffd9a69fff8e38
def v134 := [t0,t1,t2,t37,t40,t4,t95]
def t96 := 0x108200078e38
def v135 := [t96,t0,t1,t2,t37,t40,t4]
def t97 := 0xb9082081c00000
def v136 := [t97,t0,t1,t2,t37,t40,t4]
def v137 := [t0,t45,t1,t2,t37,t40,t4]
def v138 := [t0,t1,t2,t37,t46,t40,t4]
def v139 := [t47,t0,t1,t2,t37,t40,t4]
def v140 := [t48,t0,t1,t2,t37,t40,t4]
def v141 := [t0,t49,t1,t2,t37,t40,t4]
def v142 := [t0,t1,t2,t37,t40,t50,t4]
def v143 := [t51,t0,t1,t2,t37,t40,t4]
def v144 := [t52,t0,t1,t2,t37,t40,t4]
def v145 := [t0,t53,t1,t2,t37,t40,t4]
def v146 := [t0,t1,t2,t37,t40,t4,t54]
def v147 := [t55,t0,t1,t2,t37,t40,t4]
def v148 := [t56,t0,t1,t2,t37,t40,t4]
def v149 := [t0,t1,t2,t67,t4]
def v150 := [t0,t1,t2,t67,t37,t4]
def v151 := [t0,t1,t2,t67,t40,t4]
def v152 := [t0,t1,t2,t67,t37,t40,t4]
def v153 := [t0,t1,t2,t68,t37,t40,t4]
def v154 := [t0,t1,t2,t37,t40,t4,t69]
def v155 := [t70,t0,t1,t2,t37,t40,t4]
def v156 := [t71,t0,t1,t2,t37,t40,t4]
def v157 := [t0,t1,t2,t37,t72,t40,t4]
def v158 := [t0,t1,t2,t37,t40,t4,t73]
def v159 := [t74,t0,t1,t2,t37,t40,t4]
def v160 := [t75,t0,t1,t2,t37,t40,t4]
def v161 := [t0,t1,t2,t34,t3,t37,t4]
def v162 := [t36,t1,t2,t34,t3,t4]
def v163 := [t36,t0,t1,t2,t34,t3,t4]
def v164 := [t80,t0,t1,t2,t34,t3,t4]
def v165 := [t36,t0,t1,t2,t3,t40,t4]
def map31_10 : Projection 29 29 := pick [6,7,8,3,4,5,0,1,2,16,15,17,13,12,14,10,9,11,18,26,25,27,23,22,24,20,19,21,28] rfl (by decide +kernel) (by decide)
def v166 := [t76,t0,t1,t2,t34,t3,t4]
def v167 := [t0,t1,t77,t2,t34,t3,t4]
def v168 := [t78,t0,t1,t2,t34,t3,t4]
def v169 := [t89,t0,t1,t2,t34,t3,t4]
def v170 := [t79,t0,t1,t2,t34,t3,t4]
def t98 := 0x413c240000e00
def v171 := [t98,t0,t1,t2,t3,t37,t4]
def v172 := [t38,t0,t1,t2,t3,t4]
def v173 := [t36,t0,t1,t2,t3,t4]
def v174 := [t83,t0,t1,t2,t34,t3,t4]
def map31_1 : Projection 29 29 := pick [0,2,1,3,5,4,6,8,7,19,20,21,22,23,24,25,26,27,28,9,10,11,12,13,14,15,16,17,18] rfl (by decide +kernel) (by decide)
def v175 := [t0,t1,t2,t34,t3,t4,t84]
def v176 := [t85,t0,t1,t2,t34,t3,t4]
def map31_5 : Projection 29 29 := pick [3,5,4,0,2,1,6,8,7,20,19,21,25,26,27,22,23,24,28,10,9,11,15,16,17,12,13,14,18] rfl (by decide +kernel) (by decide)
def v177 := [t86,t0,t1,t2,t34,t3,t4]
def map31_7 : Projection 29 29 := pick [3,5,4,6,8,7,0,2,1,25,26,27,20,19,21,23,22,24,28,15,16,17,10,9,11,13,12,14,18] rfl (by decide +kernel) (by decide)
def map31_9 : Projection 29 29 := pick [6,8,7,0,2,1,3,5,4,23,22,24,26,25,27,19,20,21,28,13,12,14,16,15,17,9,10,11,18] rfl (by decide +kernel) (by decide)
def t99 := 0x300c0001e078000
def v178 := [t0,t99,t1,t2,t34,t3,t4]
def v179 := [t0,t1,t34,t3,t40,t4]
def v180 := [t0,t1,t2,t34,t3,t40,t4]
def t100 := 0x46118600380e38
def v181 := [t100,t0,t1,t34,t3,t4]
def v182 := [t100,t0,t1,t2,t34,t3,t4]
def v183 := [t93,t0,t1,t2,t34,t3,t4]
def v184 := [t0,t87,t1,t2,t34,t3,t4]
def v185 := [t0,t1,t2,t88,t34,t3,t4]
def v186 := [t90,t0,t1,t2,t34,t3,t4]
def v187 := [t35,t0,t1,t2,t3,t4]
def v188 := [t0,t1,t94,t2,t34,t3,t4]
def v189 := [t0,t1,t2,t34,t3,t4,t95]
def v190 := [t96,t0,t1,t2,t34,t3,t4]
def v191 := [t97,t0,t1,t2,t34,t3,t4]
def map31_3 : Projection 29 29 := pick [0,2,1,6,8,7,3,5,4,22,23,24,19,20,21,26,25,27,28,12,13,14,9,10,11,16,15,17,18] rfl (by decide +kernel) (by decide)
def t101 := 0x320ec100007f000
def v192 := [t0,t101,t1,t2,t34,t3,t4]
def v193 := [t76,t0,t1,t2,t3,t40,t4]
def t102 := 0x3b4fff25fc7ffc0
def v194 := [t0,t1,t2,t34,t3,t102,t4]
def v195 := [t0,t1,t77,t2,t3,t40,t4]
def v196 := [t10,t11,t8,t9]
def v197 := [t10,t6,t11,t8,t9]
def v198 := [t10,t7,t11,t8,t9]
def v199 := [t10,t6,t7,t11,t8,t9]
def v200 := [t12,t6,t11,t8,t9]
def v201 := [t12,t6,t7,t11,t8,t9]
def v202 := [t13,t7,t11,t8,t9]
def v203 := [t13,t6,t7,t11,t8,t9]
def v204 := [t14,t6,t7,t11,t8,t9]
def v205 := [t6,t7,t11,t8,t15,t9]
def v206 := [t16,t6,t7,t11,t8,t9]
def v207 := [t17,t6,t7,t11,t8,t9]
def v208 := [t18,t6,t7,t11,t8,t9]
def v209 := [t6,t7,t11,t8,t9,t19]
def v210 := [t20,t6,t7,t11,t8,t9]
def v211 := [t21,t6,t7,t11,t8,t9]
def v212 := [t22,t6,t11,t8,t9]
def v213 := [t22,t6,t7,t11,t8,t9]
def v214 := [t6,t7,t11,t8,t9,t23]
def v215 := [t24,t6,t7,t11,t8,t9]
def v216 := [t25,t6,t11,t8,t9]
def v217 := [t25,t6,t7,t11,t8,t9]
def v218 := [t6,t26,t7,t11,t8,t9]
def v219 := [t6,t11,t8,t9,t27]
def v220 := [t6,t7,t11,t8,t9,t27]
def v221 := [t28,t6,t11,t8,t9]
def v222 := [t28,t6,t7,t11,t8,t9]
def v223 := [t29,t6,t7,t11,t8,t9]
def t103 := 0x990fc0
def v224 := [t103,t6,t7,t8,t9]
def v225 := [t103,t6,t7,t11,t8,t9]
def t104 := 0x420038
def v226 := [t104,t6,t7,t8,t9]
def v227 := [t104,t6,t7,t11,t8,t9]
def t105 := 0xff6fc7
def v228 := [t6,t7,t8,t9,t105]
def v229 := [t6,t7,t11,t8,t9,t105]
def t106 := 0xd21c7
def v230 := [t106,t6,t7,t8,t9]
def v231 := [t106,t6,t7,t11,t8,t9]
def v232 := [t6,t7,t11,t30,t8,t9]
def v233 := [t6,t7,t11,t8,t9,t31]
def v234 := [t32,t6,t7,t11,t8,t9]
def v235 := [t33,t6,t7,t11,t8,t9]
def t107 := 0x9000201fc001c0
def v236 := [t107,t0,t1,t2,t34,t3,t4]
def v237 := [t89,t0,t1,t2,t3,t37,t4]
def v238 := [t98,t0,t1,t2,t34,t3,t4]
def t108 := 0x1423c3
def t109 := 0x488ccc
def t110 := 0xa20f30
def t111 := 0xfeafc0
def v239 := [t108,t109,t110,t111]
def t112 := 0x5cafcf
def v240 := [t108,t109,t112,t110,t111]
def p31_23 : Projection 29 12 := pick [0,2,3,5,6,8,19,20,22,23,25,26] rfl (by decide +kernel) (by decide)
def t113 := 0x320c8001fc7f000
def v241 := [t0,t113,t1,t2,t3,t4]
def v242 := [t81,t0,t1,t2,t3,t4]
def v243 := [t0,t113,t1,t2,t34,t3,t4]
def v244 := [t81,t0,t1,t2,t3,t40,t4]
def v245 := [t0,t1,t2,t3,t4,t58]
def v246 := [t5,t0,t1,t2,t3,t4,t58]
def v247 := [t0,t1,t2,t34,t3,t4,t58]
def v248 := [t35,t0,t1,t2,t3,t4,t58]
def v249 := [t38,t0,t1,t2,t3,t4,t58]
def v250 := [t39,t0,t1,t2,t3,t4,t58]
def v251 := [t0,t1,t2,t3,t37,t4,t58]
def v252 := [t36,t0,t1,t2,t3,t4,t58]
def v253 := [t80,t0,t1,t2,t3,t4,t58]
def v254 := [t76,t0,t1,t2,t3,t4,t58]
def v255 := [t0,t1,t77,t2,t3,t4,t58]
def v256 := [t78,t0,t1,t2,t3,t4,t58]
def v257 := [t79,t0,t1,t2,t3,t4,t58]
def v258 := [t83,t0,t1,t2,t3,t4,t58]
def v259 := [t0,t1,t2,t3,t4,t84,t58]
def v260 := [t85,t0,t1,t2,t3,t4,t58]
def v261 := [t86,t0,t1,t2,t3,t4,t58]
def v262 := [t82,t0,t1,t2,t3,t4]
def v263 := [t82,t1,t2,t3,t4,t58]
def v264 := [t82,t0,t1,t2,t3,t4,t58]
def v265 := [t0,t99,t1,t2,t3,t4,t58]
def v266 := [t0,t1,t2,t3,t40,t4,t58]
def v267 := [t100,t0,t1,t2,t3,t4,t58]
def v268 := [t93,t0,t1,t2,t3,t4,t58]
def v269 := [t0,t87,t1,t2,t3,t4,t58]
def v270 := [t0,t1,t2,t88,t3,t4,t58]
def v271 := [t89,t0,t1,t2,t3,t4,t58]
def v272 := [t90,t0,t1,t2,t3,t4,t58]
def v273 := [t0,t1,t94,t2,t3,t4,t58]
def v274 := [t0,t1,t2,t3,t4,t95,t58]
def v275 := [t96,t0,t1,t2,t3,t4,t58]
def v276 := [t97,t0,t1,t2,t3,t4,t58]
def v277 := [t92,t0,t1,t2,t3,t4]
def v278 := [t92,t0,t1,t3,t4,t58]
def v279 := [t92,t0,t1,t2,t3,t4,t58]
def v280 := [t0,t101,t1,t2,t3,t4,t58]
def v281 := [t0,t1,t2,t3,t102,t4,t58]
def v282 := [t107,t0,t1,t2,t3,t4,t58]
def v283 := [t98,t0,t1,t2,t3,t4,t58]
def t114 := 0x3b0c8201fc00000
def v284 := [t0,t1,t2,t114,t3,t4,t58]
def t115 := 0x3ffed349ffff1c0
def v285 := [t0,t1,t2,t3,t4,t115,t58]
def t116 := 0x24100007f1c0
def v286 := [t116,t0,t1,t2,t3,t4,t58]
def t117 := 0x4f010480380000
def v287 := [t117,t0,t1,t2,t3,t4,t58]
def t118 := 0x4f13c6c0380e3f
def v288 := [t118,t0,t1,t2,t3,t4]
def v289 := [t118,t0,t1,t2,t4,t58]
def v290 := [t118,t0,t1,t2,t3,t4,t58]
def v291 := [t0,t53,t1,t2,t3,t4,t58]
def v292 := [t0,t1,t2,t3,t4,t54,t58]
def v293 := [t55,t0,t1,t2,t3,t4,t58]
def v294 := [t56,t0,t1,t2,t3,t4,t58]
def t119 := 0xdb00249ff801ff
def v295 := [t119,t0,t2,t3,t4]
def v296 := [t119,t0,t1,t2,t3,t4]
def v297 := [t119,t0,t2,t3,t4,t58]
def v298 := [t119,t0,t1,t2,t3,t4,t58]
def t120 := 0x36d24007ffff
def v299 := [t120,t0,t1,t2,t3]
def v300 := [t120,t0,t1,t2,t3,t4]
def v301 := [t120,t0,t1,t2,t3,t58]
def v302 := [t120,t0,t1,t2,t3,t4,t58]
def v303 := [t5,t1,t34,t3,t4,t58]
def v304 := [t5,t0,t1,t34,t3,t4,t58]
def v305 := [t5,t1,t2,t34,t3,t4,t58]
def v306 := [t35,t0,t1,t34,t3,t4,t58]
def v307 := [t38,t1,t2,t34,t3,t4,t58]
def v308 := [t1,t2,t34,t3,t37,t4,t58]
def v309 := [t36,t1,t2,t34,t3,t4,t58]
def v310 := [t82,t1,t2,t34,t3,t4]
def v311 := [t82,t0,t1,t2,t34,t3,t4]
def v312 := [t82,t1,t2,t34,t3,t4,t58]
def v313 := [t0,t1,t34,t3,t40,t4,t58]
def v314 := [t100,t0,t1,t34,t3,t4,t58]
def v315 := [t92,t0,t1,t34,t3,t4]
def v316 := [t92,t0,t1,t2,t34,t3,t4]
def v317 := [t92,t0,t1,t34,t3,t4,t58]
def v318 := [t0,t113,t1,t2,t4,t58]
def v319 := [t81,t1,t2,t3,t4,t58]
def v320 := [t0,t113,t1,t2,t3,t4,t58]
def v321 := [t0,t113,t1,t2,t34,t4,t58]
def v322 := [t60,t0,t1,t2,t3,t4,t58]
def v323 := [t118,t0,t1,t2,t34,t4,t58]
def v324 := [t118,t0,t1,t2,t34,t3,t4]
def v325 := [t0,t41,t1,t2,t3,t4,t58]
def v326 := [t0,t1,t2,t42,t3,t4,t58]
def v327 := [t43,t0,t1,t2,t3,t4,t58]
def v328 := [t44,t0,t1,t2,t3,t4,t58]
def v329 := [t119,t0,t2,t34,t3,t4]
def v330 := [t119,t0,t1,t2,t34,t3,t4]
def v331 := [t119,t0,t2,t34,t3,t4,t58]
def v332 := [t0,t1,t2,t63,t3,t4,t58]
def v333 := [t0,t1,t2,t3,t4,t64,t58]
def v334 := [t65,t0,t1,t2,t3,t4,t58]
def v335 := [t66,t0,t1,t2,t3,t4,t58]
def v336 := [t60,t0,t1,t2,t3,t4]
def v337 := [t60,t0,t1,t2,t34,t3,t4]
def v338 := [t120,t0,t1,t2,t34,t3]
def v339 := [t120,t0,t1,t2,t34,t3,t4]
def v340 := [t120,t0,t1,t2,t34,t3,t58]
def v341 := [t59,t0,t1,t2,t3,t4]
def v342 := [t59,t0,t1,t2,t3,t37,t4]
def t121 := 0xc0
def v343 := [t121,t108,t109,t110,t111]
def t122 := 0x142303
def v344 := [t122,t108,t109,t110,t111]
def t123 := 0x488c0c
def v345 := [t108,t123,t109,t110,t111]
def t124 := 0x300
def v346 := [t124,t108,t109,t110,t111]
def t125 := 0xb62ff3
def v347 := [t108,t109,t110,t125,t111]
def t126 := 0x1420c3
def v348 := [t126,t108,t109,t110,t111]
def t127 := 0xa20c30
def v349 := [t108,t109,t127,t110,t111]
def t128 := 0x1423c0
def v350 := [t128,t108,t109,t110,t111]
def t129 := 0xfeafc3
def v351 := [t108,t109,t110,t111,t129]
def t130 := 0x3
def v352 := [t130,t108,t109,t110,t111]
def t131 := 0xea8c00
def v353 := [t108,t109,t110,t131,t111]
def t132 := 0xc00
def v354 := [t132,t108,t109,t110,t111]
def t133 := 0xea8ffc
def v355 := [t108,t109,t110,t133,t111]
def t134 := 0x4880cc
def v356 := [t108,t134,t109,t110,t111]
def t135 := 0xa20330
def v357 := [t108,t109,t135,t110,t111]
def t136 := 0x488cc0
def v358 := [t108,t136,t109,t110,t111]
def t137 := 0xfeafcc
def v359 := [t108,t109,t110,t111,t137]
def t138 := 0xc
def v360 := [t138,t108,t109,t110,t111]
def t139 := 0xb62300
def v361 := [t108,t109,t110,t139,t111]
def t140 := 0xa20f00
def v362 := [t108,t109,t140,t110,t111]
def t141 := 0xfeaff0
def v363 := [t108,t109,t110,t111,t141]
def t142 := 0x30
def v364 := [t142,t108,t109,t110,t111]
def t143 := 0x5ca0c0
def v365 := [t108,t109,t143,t110,t111]
def t144 := 0x5ca0cf
def v366 := [t108,t109,t144,t110,t111]
def v367 := [t121,t108,t109,t144,t110,t111]
def v368 := [t108,t109,t144,t112,t110,t111]
def v369 := [t122,t108,t109,t144,t110,t111]
def v370 := [t108,t123,t109,t144,t110,t111]
def v371 := [t126,t108,t109,t144,t110,t111]
def t145 := 0x5ca3cf
def v372 := [t108,t109,t145,t110,t111]
def v373 := [t108,t109,t144,t145,t110,t111]
def v374 := [t124,t108,t109,t144,t110,t111]
def t146 := 0x48800c
def v375 := [t108,t146,t109,t110,t111]
def v376 := [t108,t146,t109,t144,t110,t111]
def v377 := [t108,t109,t144,t125,t111]
def v378 := [t108,t109,t144,t110,t125,t111]
def v379 := [t108,t109,t144,t127,t111]
def v380 := [t108,t109,t144,t127,t110,t111]
def v381 := [t128,t109,t144,t110,t111]
def v382 := [t128,t108,t109,t144,t110,t111]
def v383 := [t108,t109,t144,t110,t111,t129]
def v384 := [t130,t108,t109,t144,t110,t111]
def v385 := [t109,t144,t110,t131,t111]
def v386 := [t108,t109,t144,t110,t131,t111]
def v387 := [t108,t134,t109,t144,t110,t111]
def t147 := 0x5caccf
def v388 := [t108,t109,t147,t110,t111]
def v389 := [t108,t109,t144,t147,t110,t111]
def v390 := [t132,t108,t109,t144,t110,t111]
def t148 := 0x142003
def v391 := [t148,t108,t109,t110,t111]
def v392 := [t148,t108,t109,t144,t110,t111]
def v393 := [t108,t109,t144,t133,t111]
def v394 := [t108,t109,t144,t110,t133,t111]
def v395 := [t108,t109,t144,t135,t111]
def v396 := [t108,t109,t144,t135,t110,t111]
def v397 := [t108,t136,t144,t110,t111]
def v398 := [t108,t136,t109,t144,t110,t111]
def v399 := [t108,t109,t144,t110,t111,t137]
def v400 := [t138,t108,t109,t144,t110,t111]
def v401 := [t108,t144,t110,t139,t111]
def v402 := [t108,t109,t144,t110,t139,t111]
def t149 := 0xfeafff
def v403 := [t108,t109,t144,t111,t149]
def v404 := [t108,t109,t110,t111,t149]
def v405 := [t108,t109,t144,t110,t111,t149]
def v406 := [t108,t109,t143,t144,t110,t111]
def t150 := 0xfeafcf
def v407 := [t108,t109,t110,t111,t150]
def v408 := [t108,t109,t144,t110,t111,t150]
def t151 := 0xf
def v409 := [t151,t108,t109,t110,t111]
def v410 := [t151,t108,t109,t144,t110,t111]
def v411 := [t108,t109,t144,t140,t110,t111]
def v412 := [t108,t109,t144,t111,t141]
def v413 := [t108,t109,t144,t110,t111,t141]
def v414 := [t142,t108,t109,t144,t111]
def v415 := [t142,t108,t109,t144,t110,t111]
def p31_15 : Projection 29 12 := pick [0,1,3,4,6,7,9,10,12,13,15,16] rfl (by decide +kernel) (by decide)
def v416 := [t16,t24,t6,t7,t8,t9]
def t152 := 0xbd61c7
def v417 := [t6,t7,t152,t8,t9]
def v418 := [t24,t6,t7,t152,t8,t9]
def t153 := 0x204007
def v419 := [t153,t6,t7,t8,t9]
def v420 := [t153,t24,t6,t7,t8,t9]
def v421 := [t24,t14,t6,t7,t8,t9]
def v422 := [t24,t22,t6,t8,t9]
def v423 := [t24,t22,t6,t7,t8,t9]
def v424 := [t24,t6,t7,t9,t23]
def v425 := [t24,t6,t7,t8,t9,t23]
def v426 := [t33,t24,t6,t7,t8,t9]
def t154 := 0xf66e07
def v427 := [t6,t7,t8,t9,t154]
def v428 := [t24,t6,t7,t8,t9,t154]
def t155 := 0x42007
def v429 := [t155,t6,t7,t8,t9]
def v430 := [t155,t24,t6,t7,t8,t9]
def v431 := [t24,t6,t7,t30,t8,t9]
def v432 := [t24,t10,t6,t7,t8,t9]
def v433 := [t12,t24,t6,t7,t8,t9]
def v434 := [t13,t24,t6,t7,t8,t9]
def v435 := [t24,t6,t7,t15,t9]
def v436 := [t24,t6,t7,t8,t15,t9]
def v437 := [t24,t17,t6,t7,t9]
def v438 := [t24,t17,t6,t7,t8,t9]
def v439 := [t24,t18,t6,t7,t8,t9]
def v440 := [t24,t6,t7,t8,t9,t19]
def v441 := [t20,t24,t6,t7,t8,t9]
def v442 := [t24,t21,t6,t7,t8,t9]
def v443 := [t24,t25,t6,t9]
def v444 := [t24,t25,t6,t7,t9]
def v445 := [t24,t25,t6,t8,t9]
def v446 := [t24,t25,t6,t7,t8,t9]
def v447 := [t24,t6,t26,t7,t8,t9]
def v448 := [t24,t6,t7,t8,t9,t27]
def v449 := [t28,t24,t6,t7,t8,t9]
def v450 := [t24,t29,t6,t7,t8,t9]
def v451 := [t24,t6,t7,t9,t31]
def v452 := [t24,t6,t7,t8,t9,t31]
def v453 := [t32,t24,t6,t7,t9]
def v454 := [t32,t24,t6,t7,t8,t9]
def v455 := [t0,t1,t2,t34,t114,t3,t4]
def v456 := [t0,t1,t2,t34,t3,t4,t115]
def v457 := [t116,t0,t1,t2,t34,t3,t4]
def v458 := [t117,t0,t1,t2,t34,t3,t4]
def v459 := [t0,t41,t1,t2,t3,t4]
def v460 := [t0,t41,t1,t2,t34,t3,t4]
def v461 := [t0,t1,t2,t42,t3,t4]
def v462 := [t0,t1,t2,t34,t42,t3,t4]
def v463 := [t43,t0,t1,t2,t3,t4]
def v464 := [t71,t0,t1,t2,t3,t4]
def v465 := [t43,t0,t1,t2,t34,t3,t4]
def v466 := [t71,t0,t1,t2,t3,t37,t4]
def v467 := [t44,t0,t1,t2,t3,t4]
def v468 := [t78,t0,t1,t2,t3,t4]
def v469 := [t78,t44,t0,t1,t2,t3,t4]
def t156 := 0x26f8b44dffc7e3f
def v470 := [t0,t156,t1,t2,t3,t4]
def v471 := [t44,t0,t156,t1,t2,t3,t4]
def t157 := 0x4200040e000038
def v472 := [t157,t0,t1,t2,t3,t4]
def v473 := [t157,t44,t0,t1,t2,t3,t4]
def v474 := [t76,t0,t1,t2,t3,t4]
def v475 := [t44,t76,t0,t1,t2,t3,t4]
def v476 := [t89,t0,t1,t2,t3,t4]
def v477 := [t89,t44,t0,t1,t2,t3,t4]
def t158 := 0x34fd1869fff8e3f
def v478 := [t0,t1,t2,t158,t3,t4]
def v479 := [t44,t0,t1,t2,t158,t3,t4]
def t159 := 0x9000081c00007
def v480 := [t159,t0,t1,t2,t3,t4]
def v481 := [t159,t44,t0,t1,t2,t3,t4]
def v482 := [t0,t87,t1,t2,t3,t4]
def v483 := [t44,t0,t87,t1,t2,t3,t4]
def t160 := 0x1fc00000
def v484 := [t160,t0,t1,t2,t3,t4]
def v485 := [t160,t44,t0,t1,t2,t3,t4]
def t161 := 0x3fbec349ffff1ff
def v486 := [t0,t1,t2,t3,t161,t4]
def v487 := [t44,t0,t1,t2,t3,t161,t4]
def t162 := 0x4b00048038003f
def v488 := [t162,t0,t1,t2,t3,t4]
def v489 := [t162,t44,t0,t1,t2,t3,t4]
def t163 := 0x3b0ec300007f1c0
def v490 := [t0,t1,t2,t163,t3,t4]
def v491 := [t44,t0,t1,t2,t163,t3,t4]
def v492 := [t44,t0,t2,t42,t3,t4]
def v493 := [t44,t0,t1,t2,t42,t3,t4]
def t164 := 0x4b00049ff80000
def v494 := [t164,t0,t1,t2,t3,t4]
def v495 := [t164,t44,t0,t1,t2,t3,t4]
def t165 := 0x3ffc9249ff8003f
def v496 := [t0,t1,t2,t3,t4,t165]
def v497 := [t44,t0,t1,t2,t3,t4,t165]
def t166 := 0x3f
def v498 := [t166,t0,t1,t2,t3,t4]
def v499 := [t166,t44,t0,t1,t2,t3,t4]
def t167 := 0x3b4c92000000000
def v500 := [t0,t1,t2,t3,t167,t4]
def v501 := [t44,t0,t1,t2,t3,t167,t4]
def v502 := [t44,t5,t0,t1,t2,t3,t4]
def v503 := [t44,t0,t1,t2,t34,t3,t4]
def v504 := [t35,t44,t0,t1,t2,t3,t4]
def v505 := [t44,t38,t0,t1,t2,t3,t4]
def v506 := [t44,t39,t0,t1,t2,t3,t4]
def v507 := [t44,t0,t1,t2,t3,t37,t4]
def v508 := [t36,t44,t0,t1,t2,t3,t4]
def v509 := [t44,t80,t0,t1,t2,t3,t4]
def v510 := [t44,t0,t77,t2,t3,t4]
def v511 := [t44,t0,t1,t77,t2,t3,t4]
def v512 := [t44,t79,t0,t2,t3,t4]
def v513 := [t44,t79,t0,t1,t2,t3,t4]
def v514 := [t44,t83,t0,t1,t2,t3,t4]
def v515 := [t44,t0,t1,t2,t3,t4,t84]
def v516 := [t85,t44,t0,t1,t2,t3,t4]
def v517 := [t44,t86,t0,t1,t2,t3,t4]
def v518 := [t44,t0,t99,t1,t2,t3,t4]
def v519 := [t44,t0,t1,t2,t3,t40,t4]
def v520 := [t100,t44,t0,t1,t2,t3,t4]
def v521 := [t44,t93,t0,t1,t2,t3,t4]
def v522 := [t44,t0,t2,t88,t3,t4]
def v523 := [t44,t0,t1,t2,t88,t3,t4]
def v524 := [t90,t44,t0,t2,t3,t4]
def v525 := [t90,t44,t0,t1,t2,t3,t4]
def v526 := [t44,t0,t1,t94,t2,t3,t4]
def v527 := [t44,t0,t1,t2,t3,t4,t95]
def v528 := [t96,t44,t0,t1,t2,t3,t4]
def v529 := [t44,t97,t0,t1,t2,t3,t4]
def v530 := [t44,t0,t101,t2,t3,t4]
def v531 := [t44,t0,t101,t1,t2,t3,t4]
def v532 := [t44,t0,t1,t2,t3,t102,t4]
def v533 := [t44,t107,t0,t2,t3,t4]
def v534 := [t44,t107,t0,t1,t2,t3,t4]
def v535 := [t98,t44,t0,t1,t2,t3,t4]
def v536 := [t44,t0,t1,t2,t114,t3,t4]
def v537 := [t44,t0,t1,t2,t3,t4,t115]
def v538 := [t116,t44,t0,t1,t2,t3,t4]
def v539 := [t44,t117,t0,t1,t2,t3,t4]
def v540 := [t44,t0,t53,t1,t2,t3,t4]
def v541 := [t44,t0,t2,t3,t4,t54]
def v542 := [t44,t0,t1,t2,t3,t4,t54]
def v543 := [t55,t44,t0,t2,t3,t4]
def v544 := [t55,t44,t0,t1,t2,t3,t4]
def v545 := [t44,t56,t0,t1,t2,t3,t4]
def v546 := [t0,t156,t1,t2,t34,t3,t4]
def v547 := [t157,t0,t1,t2,t34,t3,t4]
def v548 := [t0,t1,t2,t158,t34,t3,t4]
def v549 := [t159,t0,t1,t2,t34,t3,t4]
def v550 := [t160,t0,t1,t2,t34,t3,t4]
def v551 := [t0,t1,t2,t34,t3,t161,t4]
def v552 := [t162,t0,t1,t2,t34,t3,t4]
def v553 := [t0,t1,t2,t34,t163,t3,t4]
def v554 := [t44,t0,t2,t34,t42,t3,t4]
def v555 := [t44,t0,t41,t1,t2,t3,t4]
def v556 := [t164,t0,t1,t2,t34,t3,t4]
def v557 := [t0,t1,t2,t34,t3,t4,t165]
def v558 := [t166,t0,t1,t2,t34,t3,t4]
def v559 := [t0,t1,t2,t34,t3,t167,t4]
def v560 := [t44,t5,t1,t34,t3,t4]
def v561 := [t44,t5,t0,t1,t34,t3,t4]
def v562 := [t44,t5,t1,t2,t34,t3,t4]
def v563 := [t35,t44,t0,t1,t34,t3,t4]
def v564 := [t44,t38,t1,t2,t34,t3,t4]
def v565 := [t44,t1,t2,t34,t3,t37,t4]
def v566 := [t36,t44,t1,t2,t34,t3,t4]
def v567 := [t44,t0,t77,t2,t34,t3,t4]
def v568 := [t44,t79,t0,t2,t34,t3,t4]
def v569 := [t44,t0,t1,t34,t3,t40,t4]
def v570 := [t100,t44,t0,t1,t34,t3,t4]
def v571 := [t44,t0,t2,t88,t34,t3,t4]
def v572 := [t90,t44,t0,t2,t34,t3,t4]
def v573 := [t44,t0,t101,t2,t34,t3,t4]
def v574 := [t44,t107,t0,t2,t34,t3,t4]
def v575 := [t44,t0,t113,t1,t2,t3,t4]
def v576 := [t44,t60,t0,t1,t2,t3,t4]
def v577 := [t44,t118,t0,t1,t2,t3,t4]
def v578 := [t43,t44,t0,t2,t3,t4]
def v579 := [t51,t52,t0,t2,t3,t4]
def t168 := 0x624e3f
def v580 := [t168,t7,t8,t9]
def v581 := [t43,t44,t0,t1,t2,t3,t4]
def v582 := [t43,t44,t0,t2,t34,t3,t4]
def v583 := [t44,t0,t2,t34,t3,t4,t54]
def v584 := [t55,t44,t0,t2,t34,t3,t4]
def v585 := [t44,t0,t1,t2,t63,t3,t4]
def v586 := [t44,t0,t1,t2,t3,t4,t64]
def v587 := [t65,t44,t0,t1,t2,t3,t4]
def v588 := [t44,t66,t0,t1,t2,t3,t4]
def v589 := [t0,t53,t1,t2,t34,t3,t4]
def v590 := [t0,t1,t2,t34,t3,t4,t54]
def v591 := [t5,t1,t34,t3,t4,t54]
def v592 := [t5,t0,t1,t34,t3,t4,t54]
def v593 := [t5,t1,t2,t34,t3,t4,t54]
def v594 := [t35,t0,t1,t34,t3,t4,t54]
def v595 := [t38,t1,t2,t34,t3,t4,t54]
def v596 := [t1,t2,t34,t3,t37,t4,t54]
def v597 := [t36,t1,t2,t34,t3,t4,t54]
def v598 := [t38,t0,t1,t2,t3,t4,t54]
def t169 := 0x22d8b40d1fc7e00
def v599 := [t169,t1,t2,t34,t3,t4]
def v600 := [t169,t0,t1,t2,t34,t3,t4]
def v601 := [t169,t1,t2,t34,t3,t4,t54]
def t170 := 0x3fffff6dffffe07
def v602 := [t0,t1,t2,t34,t3,t4,t170]
def t171 := 0x7
def v603 := [t171,t0,t1,t2,t34,t3,t4]
def t172 := 0x1d274b60e038000
def v604 := [t172,t1,t2,t34,t3,t4]
def v605 := [t172,t0,t1,t2,t34,t3,t4]
def v606 := [t172,t1,t2,t34,t3,t4,t54]
def v607 := [t0,t1,t34,t3,t40,t4,t54]
def v608 := [t100,t0,t1,t34,t3,t4,t54]
def v609 := [t35,t0,t1,t2,t3,t4,t54]
def t173 := 0x346d1861e3f8e00
def v610 := [t0,t1,t173,t34,t3,t4]
def v611 := [t0,t1,t173,t2,t34,t3,t4]
def v612 := [t0,t1,t173,t34,t3,t4,t54]
def t174 := 0x3fffff6dffffe38
def v613 := [t0,t1,t2,t34,t3,t4,t174]
def t175 := 0x38
def v614 := [t175,t0,t1,t2,t34,t3,t4]
def t176 := 0xb92e70c1c07000
def v615 := [t176,t0,t1,t34,t3,t4]
def v616 := [t176,t0,t1,t2,t34,t3,t4]
def v617 := [t176,t0,t1,t34,t3,t4,t54]
def v618 := [t0,t113,t1,t2,t3,t4,t54]
def v619 := [t60,t0,t1,t2,t3,t4,t54]
def v620 := [t118,t0,t1,t2,t3,t4,t54]
def t177 := 0x3b0ec301fc7f000
def v621 := [t0,t1,t2,t34,t177,t3,t4]
def t178 := 0x3fffff6dfffffc0
def v622 := [t0,t1,t2,t34,t3,t4,t178]
def t179 := 0x1c0
def v623 := [t179,t0,t1,t2,t34,t3,t4]
def t180 := 0x4f13c6c0380e00
def v624 := [t180,t0,t1,t2,t34,t3,t4]
def v625 := [t0,t41,t2,t3,t4,t54]
def v626 := [t0,t41,t1,t2,t3,t4,t54]
def v627 := [t0,t41,t2,t34,t3,t4,t54]
def v628 := [t0,t1,t2,t42,t3,t4,t54]
def v629 := [t43,t0,t1,t2,t3,t4,t54]
def v630 := [t0,t53,t2,t34,t3,t54]
def v631 := [t0,t53,t1,t2,t34,t3,t54]
def v632 := [t0,t53,t2,t34,t3,t4,t54]
def v633 := [t55,t0,t1,t2,t34,t3,t54]
def v634 := [t56,t0,t2,t34,t3,t4,t54]
def v635 := [t56,t0,t1,t2,t34,t3,t4]
def v636 := [t0,t1,t2,t63,t3,t54]
def v637 := [t0,t1,t2,t63,t34,t3,t54]
def v638 := [t0,t1,t2,t63,t3,t4,t54]
def v639 := [t0,t1,t2,t3,t4,t64,t54]
def v640 := [t65,t0,t1,t2,t3,t54]
def v641 := [t65,t0,t1,t2,t34,t3,t54]
def v642 := [t65,t0,t1,t2,t3,t4,t54]
def v643 := [t66,t0,t1,t2,t3,t4,t54]
def t181 := 0x36fdbc6dffffe00
def v644 := [t0,t1,t2,t181,t3,t4]
def v645 := [t0,t1,t2,t181,t34,t3,t4]
def v646 := [t0,t1,t2,t181,t3,t4,t54]
def t182 := 0x3fffff6dffffe3f
def v647 := [t0,t1,t2,t3,t4,t182]
def v648 := [t0,t1,t2,t34,t3,t4,t182]
def v649 := [t0,t1,t2,t3,t4,t54,t182]
def v650 := [t166,t0,t1,t2,t3,t4,t54]
def t183 := 0x90243000000000
def v651 := [t183,t0,t1,t2,t3,t4]
def v652 := [t183,t0,t1,t2,t34,t3,t4]
def v653 := [t183,t0,t1,t2,t3,t4,t54]
def v654 := [t55,t0,t1,t2,t34,t3,t4]
def v655 := [t0,t1,t2,t63,t3,t4]
def v656 := [t0,t1,t2,t63,t34,t3,t4]
def v657 := [t0,t1,t2,t3,t4,t64]
def v658 := [t0,t1,t2,t34,t3,t4,t64]
def v659 := [t65,t0,t1,t2,t3,t4]
def v660 := [t65,t0,t1,t2,t34,t3,t4]
def v661 := [t66,t0,t1,t2,t3,t4]
def v662 := [t66,t0,t1,t2,t34,t3,t4]
def v663 := [t39,t0,t1,t2,t3,t4]
def v664 := [t0,t1,t2,t3,t37,t4]
def v665 := [t80,t0,t1,t2,t3,t4]
def v666 := [t0,t1,t77,t2,t3,t4]
def v667 := [t5,t0,t1,t77,t2,t3,t4]
def v668 := [t35,t0,t1,t77,t2,t3,t4]
def v669 := [t36,t0,t1,t77,t2,t3,t4]
def v670 := [t38,t0,t1,t77,t2,t3,t4]
def v671 := [t36,t0,t1,t2,t3,t102,t4]
def v672 := [t39,t0,t1,t77,t2,t3,t4]
def v673 := [t0,t1,t77,t2,t3,t37,t4]
def v674 := [t80,t0,t1,t77,t2,t3,t4]
def v675 := [t76,t77,t2,t3,t4]
def v676 := [t76,t0,t77,t2,t3,t4]
def v677 := [t76,t1,t77,t2,t3,t4]
def v678 := [t76,t0,t1,t77,t2,t3,t4]
def v679 := [t78,t0,t77,t2,t3,t4]
def v680 := [t89,t0,t2,t88,t3,t4]
def v681 := [t78,t0,t1,t77,t2,t3,t4]
def v682 := [t89,t0,t1,t2,t88,t3,t4]
def v683 := [t79,t1,t77,t2,t3,t4]
def v684 := [t98,t0,t1,t2,t102,t4]
def v685 := [t79,t0,t1,t77,t2,t3,t4]
def v686 := [t98,t0,t1,t2,t3,t102,t4]
def v687 := [t79,t0,t1,t2,t3,t4]
def v688 := [t98,t0,t1,t2,t3,t4]
def v689 := [t83,t0,t1,t77,t2,t3,t4]
def v690 := [t76,t0,t1,t2,t3,t4,t84]
def v691 := [t1,t77,t2,t3,t4,t84]
def v692 := [t0,t1,t2,t102,t4,t115]
def v693 := [t6,t7,t15,t9,t31]
def v694 := [t10,t6,t7,t15,t9,t31]
def v695 := [t6,t7,t11,t15,t9,t31]
def v696 := [t12,t6,t7,t15,t9,t31]
def v697 := [t13,t6,t7,t15,t9,t31]
def v698 := [t17,t6,t7,t9,t31]
def v699 := [t17,t7,t15,t9,t31]
def v700 := [t17,t6,t7,t15,t9,t31]
def v701 := [t18,t6,t7,t15,t9,t31]
def v702 := [t6,t7,t15,t9,t31,t19]
def v703 := [t20,t6,t7,t15,t9,t31]
def v704 := [t21,t6,t7,t15,t9,t31]
def v705 := [t14,t7,t15,t9]
def v706 := [t14,t6,t7,t15,t9]
def v707 := [t14,t7,t15,t9,t31]
def v708 := [t14,t6,t7,t15,t9,t31]
def t184 := 0xff6ff8
def v709 := [t6,t7,t15,t9,t31,t184]
def v710 := [t16,t6,t7,t15,t9]
def v711 := [t16,t6,t7,t15,t9,t31]
def t185 := 0x624e38
def v712 := [t185,t7,t15,t9,t31]
def v713 := [t185,t6,t7,t15,t9,t31]
def t186 := 0x942fc0
def v714 := [t186,t6,t7,t9,t31]
def v715 := [t186,t6,t7,t15,t9,t31]
def v716 := [t6,t7,t15,t9,t31,t23]
def v717 := [t153,t6,t7,t9,t31]
def v718 := [t153,t6,t7,t15,t9,t31]
def v719 := [t25,t6,t7,t15,t9,t31]
def v720 := [t6,t26,t7,t15,t9,t31]
def v721 := [t6,t7,t15,t9,t27,t31]
def v722 := [t28,t6,t7,t15,t9,t31]
def v723 := [t29,t6,t7,t15,t9,t31]
def t187 := 0xb04fc0
def v724 := [t6,t187,t7,t15,t9]
def v725 := [t6,t187,t7,t15,t9,t31]
def v726 := [t155,t6,t7,t15,t9]
def v727 := [t155,t6,t7,t15,t9,t31]
def v728 := [t6,t7,t30,t31]
def v729 := [t6,t7,t30,t15,t31]
def v730 := [t6,t7,t30,t9,t31]
def v731 := [t6,t7,t30,t15,t9,t31]
def t188 := 0xd21f8
def v732 := [t188,t6,t7,t15,t31]
def v733 := [t188,t6,t7,t15,t9,t31]
def v734 := [t33,t6,t7,t9,t31]
def v735 := [t33,t6,t7,t15,t9,t31]
def v736 := [t6,t7,t8,t15,t9,t31]
def v737 := [t32,t6,t7,t15,t9]
def v738 := [t32,t6,t7,t15,t31]
def v739 := [t32,t6,t7,t15,t9,t31]
def v740 := [t0,t1,t77,t2,t3,t4,t84]
def v741 := [t85,t1,t77,t2,t3,t4]
def v742 := [t89,t0,t1,t3,t4,t95]
def v743 := [t85,t0,t1,t77,t2,t3,t4]
def v744 := [t89,t0,t1,t2,t3,t4,t95]
def v745 := [t86,t0,t1,t77,t2,t3,t4]
def v746 := [t98,t0,t1,t2,t3,t4,t115]
def v747 := [t0,t99,t1,t77,t2,t3,t4]
def v748 := [t5,t0,t1,t2,t3,t102,t4]
def v749 := [t100,t0,t1,t77,t2,t3,t4]
def v750 := [t36,t0,t1,t2,t88,t3,t4]
def v751 := [t93,t0,t1,t77,t2,t3,t4]
def v752 := [t0,t87,t1,t77,t2,t3,t4]
def v753 := [t76,t0,t1,t2,t88,t3,t4]
def v754 := [t0,t1,t77,t2,t88,t3,t4]
def v755 := [t89,t0,t1,t77,t2,t3,t4]
def v756 := [t90,t0,t1,t77,t2,t3,t4]
def v757 := [t98,t0,t1,t77,t2,t3,t4]
def t189 := 0x304d182103f8e00
def v758 := [t0,t189,t1,t2,t3,t4]
def t190 := 0x2248b40503c7e00
def v759 := [t190,t0,t1,t2,t3,t4]
def v760 := [t0,t189,t1,t77,t2,t3,t4]
def v761 := [t190,t0,t1,t2,t88,t3,t4]
def v762 := [t0,t1,t77,t2,t42,t3,t4]
def t191 := 0x42000400380038
def v763 := [t191,t0,t1,t2,t3,t4]
def v764 := [t157,t0,t1,t77,t2,t3,t4]
def v765 := [t191,t0,t1,t2,t3,t102,t4]
def t192 := 0x292e50c1c07007
def v766 := [t192,t0,t1,t2,t3,t4]
def t193 := 0xd13c2c0380e07
def v767 := [t193,t0,t1,t2,t3,t4]
def v768 := [t192,t0,t1,t77,t2,t3,t4]
def v769 := [t193,t0,t1,t77,t2,t3,t4]
def v770 := [t0,t1,t77,t94,t2,t3,t4]
def v771 := [t76,t0,t1,t2,t3,t4,t95]
def v772 := [t0,t1,t77,t2,t3,t4,t95]
def v773 := [t96,t0,t1,t77,t2,t3,t4]
def v774 := [t89,t0,t1,t2,t3,t4,t84]
def v775 := [t97,t0,t1,t77,t2,t3,t4]
def v776 := [t98,t0,t1,t2,t3,t4,t84]
def v777 := [t0,t101,t1,t77,t2,t3,t4]
def v778 := [t0,t1,t77,t2,t3,t102,t4]
def v779 := [t107,t0,t1,t77,t2,t3,t4]
def t194 := 0x320ec1011c7f000
def v780 := [t0,t194,t1,t2,t3,t4]
def v781 := [t0,t194,t1,t77,t2,t3,t4]
def v782 := [t0,t1,t2,t3,t46,t4]
def v783 := [t0,t1,t77,t2,t3,t46,t4]
def t195 := 0x9000200e0001c0
def v784 := [t195,t0,t1,t2,t3,t4]
def v785 := [t195,t0,t1,t77,t2,t3,t4]
def v786 := [t0,t1,t77,t2,t114,t3,t4]
def v787 := [t0,t1,t77,t2,t3,t4,t115]
def v788 := [t116,t0,t1,t77,t2,t3,t4]
def v789 := [t117,t0,t1,t77,t2,t3,t4]
def v790 := [t0,t53,t1,t77,t2,t3,t4]
def v791 := [t0,t1,t77,t2,t3,t4,t54]
def v792 := [t55,t0,t1,t77,t2,t3,t4]
def v793 := [t56,t0,t1,t2,t3,t4,t84]
def v794 := [t56,t0,t1,t77,t2,t3,t4]
def t196 := 0x32dc90091f80000
def v795 := [t0,t1,t196,t2,t3,t4]
def t197 := 0x324cb4040047e00
def v796 := [t0,t197,t1,t2,t3,t4]
def v797 := [t0,t1,t196,t77,t2,t3,t4]
def v798 := [t0,t197,t1,t2,t3,t4,t84]
def v799 := [t0,t1,t2,t3,t4,t170]
def v800 := [t121,t108,t109,t110,t111,t129]
def v801 := [t108,t109,t112,t110,t111,t129]
def v802 := [t122,t108,t109,t110,t111,t129]
def v803 := [t108,t123,t109,t110,t111,t129]
def v804 := [t124,t108,t109,t110,t111,t129]
def v805 := [t108,t109,t110,t125,t111,t129]
def v806 := [t126,t108,t109,t110,t111,t129]
def v807 := [t108,t109,t127,t110,t111,t129]
def v808 := [t128,t109,t110,t129]
def v809 := [t128,t108,t109,t110,t129]
def v810 := [t128,t109,t110,t111,t129]
def v811 := [t128,t108,t109,t110,t111,t129]
def v812 := [t130,t108,t109,t110,t129]
def v813 := [t130,t108,t109,t110,t111,t129]
def v814 := [t109,t110,t131,t111,t129]
def v815 := [t108,t109,t110,t131,t111,t129]
def v816 := [t132,t108,t109,t110,t111,t129]
def v817 := [t108,t109,t110,t133,t111,t129]
def v818 := [t108,t134,t109,t110,t111,t129]
def v819 := [t108,t109,t135,t110,t111,t129]
def v820 := [t108,t136,t109,t110,t111,t129]
def v821 := [t108,t109,t110,t129,t137]
def v822 := [t108,t109,t110,t111,t129,t137]
def v823 := [t138,t108,t109,t110,t111,t129]
def v824 := [t108,t109,t110,t139,t129]
def v825 := [t108,t109,t110,t139,t111,t129]
def v826 := [t108,t109,t110,t111,t129,t150]
def t198 := 0xb62303
def v827 := [t108,t109,t110,t198,t111]
def v828 := [t108,t109,t110,t198,t111,t129]
def v829 := [t108,t109,t140,t110,t111,t129]
def v830 := [t108,t109,t110,t129,t141]
def v831 := [t108,t109,t110,t111,t129,t141]
def v832 := [t142,t108,t109,t110,t111,t129]
def v833 := [t108,t109,t143,t110,t129]
def v834 := [t108,t109,t143,t110,t111,t129]
def t199 := 0xfeaff3
def v835 := [t108,t109,t110,t111,t199]
def v836 := [t108,t109,t110,t111,t129,t199]
def t200 := 0x5ca0c3
def v837 := [t108,t109,t200,t110,t111]
def v838 := [t108,t109,t200,t110,t111,t129]
def v839 := [t0,t1,t77,t2,t3,t4,t170]
def t201 := 0x36d24007fe07
def v840 := [t201,t0,t1,t2,t3,t4]
def t202 := 0xdb00249ff80007
def v841 := [t202,t0,t1,t2,t3,t4]
def v842 := [t201,t0,t1,t77,t2,t3,t4]
def v843 := [t202,t0,t1,t2,t3,t4,t84]
def t203 := 0xd200240e000000
def v844 := [t203,t0,t1,t2,t3,t4]
def t204 := 0x4b000480380000
def v845 := [t204,t0,t1,t2,t3,t4]
def v846 := [t203,t0,t1,t77,t2,t3,t4]
def v847 := [t204,t0,t1,t2,t3,t102,t4]
def v848 := [t83,t0,t1,t2,t3,t4]
def v849 := [t0,t1,t2,t3,t4,t84]
def v850 := [t85,t0,t1,t2,t3,t4]
def v851 := [t86,t0,t1,t2,t3,t4]
def v852 := [t0,t99,t1,t2,t3,t4]
def v853 := [t0,t1,t2,t3,t40,t4]
def v854 := [t100,t0,t1,t2,t3,t4]
def v855 := [t93,t0,t1,t2,t3,t4]
def v856 := [t0,t1,t2,t88,t3,t4]
def v857 := [t90,t0,t1,t2,t3,t4]
def v858 := [t0,t1,t94,t2,t3,t4]
def v859 := [t0,t1,t2,t3,t4,t95]
def v860 := [t96,t0,t1,t2,t3,t4]
def v861 := [t97,t0,t1,t2,t3,t4]
def v862 := [t0,t101,t1,t2,t3,t4]
def v863 := [t0,t1,t2,t3,t102,t4]
def v864 := [t107,t0,t1,t2,t3,t4]
def v865 := [t0,t1,t2,t114,t3,t4]
def v866 := [t0,t1,t2,t3,t4,t115]
def v867 := [t116,t0,t1,t2,t3,t4]
def v868 := [t117,t0,t1,t2,t3,t4]
def v869 := [t0,t53,t1,t2,t3,t4]
def v870 := [t0,t1,t2,t3,t4,t54]
def v871 := [t5,t0,t1,t2,t3,t4,t54]
def v872 := [t36,t0,t1,t2,t3,t4,t54]
def v873 := [t39,t0,t1,t2,t3,t4,t54]
def v874 := [t0,t1,t2,t3,t37,t4,t54]
def v875 := [t80,t0,t1,t2,t3,t4,t54]
def v876 := [t76,t0,t1,t2,t3,t4,t54]
def v877 := [t78,t0,t1,t2,t3,t4,t54]
def v878 := [t89,t0,t1,t2,t3,t4,t54]
def v879 := [t79,t0,t1,t2,t3,t4,t54]
def v880 := [t98,t0,t1,t2,t3,t4,t54]
def v881 := [t83,t0,t1,t2,t3,t4,t54]
def v882 := [t0,t1,t2,t3,t4,t84,t54]
def v883 := [t85,t0,t1,t2,t3,t4,t54]
def v884 := [t86,t0,t1,t2,t3,t4,t54]
def v885 := [t169,t0,t1,t2,t3,t4]
def v886 := [t169,t0,t1,t2,t3,t4,t54]
def v887 := [t0,t1,t2,t3,t4,t54,t170]
def v888 := [t171,t0,t1,t2,t3,t4]
def v889 := [t171,t0,t1,t2,t3,t4,t54]
def v890 := [t172,t0,t1,t2,t3,t4]
def v891 := [t180,t0,t1,t2,t3,t4]
def t205 := 0xd0340c0380e00
def v892 := [t205,t0,t1,t2,t3,t4]
def v893 := [t205,t180,t0,t1,t2,t3,t4]
def t206 := 0x26f9bc6d1fc7e07
def v894 := [t0,t206,t1,t2,t3,t4]
def v895 := [t180,t0,t206,t1,t2,t3,t4]
def t207 := 0x42108600000000
def v896 := [t207,t0,t1,t2,t3,t4]
def v897 := [t207,t180,t0,t1,t2,t3,t4]
def t208 := 0x220880011c47007
def v898 := [t208,t0,t1,t2,t3,t4]
def v899 := [t180,t208,t0,t1,t2,t3,t4]
def t209 := 0x46118600380e00
def v900 := [t209,t0,t1,t2,t3,t4]
def v901 := [t209,t180,t0,t1,t2,t3,t4]
def t210 := 0x34fd3c6de3f8e38
def v902 := [t0,t1,t2,t210,t3,t4]
def v903 := [t180,t0,t1,t2,t210,t3,t4]
def t211 := 0x90240c0000000
def v904 := [t211,t0,t1,t2,t3,t4]
def v905 := [t211,t180,t0,t1,t2,t3,t4]
def t212 := 0x300c0001e078038
def v906 := [t0,t212,t1,t2,t3,t4]
def v907 := [t180,t0,t212,t1,t2,t3,t4]
def v908 := [t180,t0,t1,t2,t4,t178]
def v909 := [t0,t1,t2,t3,t4,t178]
def v910 := [t180,t0,t1,t2,t3,t4,t178]
def v911 := [t98,t180,t0,t1,t2,t3,t4]
def t213 := 0x36fffd6c03ffe00
def v912 := [t0,t1,t2,t213,t3,t4]
def v913 := [t180,t0,t1,t2,t213,t3,t4]
def v914 := [t204,t180,t0,t1,t2,t3,t4]
def v915 := [t180,t0,t101,t1,t2,t3,t4]
def v916 := [t117,t180,t0,t1,t2,t3,t4]
def t214 := 0x3ffdbe6dff80e00
def v917 := [t0,t1,t2,t3,t4,t214]
def v918 := [t180,t0,t1,t2,t3,t4,t214]
def t215 := 0x12c240000e00
def v919 := [t215,t0,t1,t2,t3,t4]
def v920 := [t215,t180,t0,t1,t2,t3,t4]
def v921 := [t180,t0,t1,t2,t114,t3,t4]
def v922 := [t180,t5,t0,t1,t2,t3,t4]
def v923 := [t35,t180,t0,t1,t2,t3,t4]
def v924 := [t180,t38,t0,t1,t2,t3,t4]
def v925 := [t180,t39,t0,t1,t2,t3,t4]
def v926 := [t180,t0,t1,t2,t37,t4]
def v927 := [t180,t0,t1,t2,t3,t37,t4]
def v928 := [t36,t180,t0,t1,t2,t3,t4]
def v929 := [t180,t80,t0,t1,t2,t4]
def v930 := [t180,t80,t0,t1,t2,t3,t4]
def v931 := [t180,t76,t0,t1,t2,t3,t4]
def v932 := [t180,t0,t1,t77,t2,t3,t4]
def v933 := [t78,t180,t0,t1,t2,t3,t4]
def v934 := [t180,t79,t0,t1,t2,t3,t4]
def v935 := [t180,t83,t0,t1,t2,t3,t4]
def v936 := [t180,t0,t1,t2,t3,t4,t84]
def v937 := [t85,t180,t0,t1,t2,t3,t4]
def v938 := [t180,t86,t0,t1,t2,t3,t4]
def v939 := [t180,t0,t99,t1,t2,t3,t4]
def v940 := [t180,t0,t1,t2,t40,t4]
def v941 := [t180,t0,t1,t2,t3,t40,t4]
def v942 := [t100,t180,t0,t1,t2,t3,t4]
def v943 := [t180,t93,t0,t1,t2,t4]
def v944 := [t180,t93,t0,t1,t2,t3,t4]
def v945 := [t180,t0,t87,t1,t2,t3,t4]
def v946 := [t180,t0,t1,t2,t88,t3,t4]
def v947 := [t89,t180,t0,t1,t2,t3,t4]
def v948 := [t90,t180,t0,t1,t2,t3,t4]
def v949 := [t180,t0,t1,t94,t2,t3,t4]
def v950 := [t180,t0,t1,t2,t3,t4,t95]
def v951 := [t96,t180,t0,t1,t2,t3,t4]
def v952 := [t180,t97,t0,t1,t2,t3,t4]
def v953 := [t180,t0,t1,t2,t102,t4]
def v954 := [t180,t0,t1,t2,t3,t102,t4]
def v955 := [t180,t107,t0,t1,t2,t4]
def v956 := [t180,t107,t0,t1,t2,t3,t4]
def v957 := [t180,t0,t1,t2,t4,t115]
def v958 := [t180,t0,t1,t2,t3,t4,t115]
def v959 := [t116,t180,t0,t1,t2,t4]
def v960 := [t116,t180,t0,t1,t2,t3,t4]
def v961 := [t180,t0,t53,t1,t2,t3,t4]
def v962 := [t180,t0,t1,t2,t3,t4,t54]
def v963 := [t55,t180,t0,t1,t2,t3,t4]
def v964 := [t180,t56,t0,t1,t2,t3,t4]
def v965 := [t172,t0,t1,t2,t3,t4,t54]
def v966 := [t205,t0,t1,t2,t3,t4,t54]
def v967 := [t0,t206,t1,t2,t3,t4,t54]
def v968 := [t207,t0,t1,t2,t3,t4,t54]
def v969 := [t208,t0,t1,t2,t3,t4,t54]
def v970 := [t209,t0,t1,t2,t3,t4,t54]
def v971 := [t0,t1,t2,t210,t3,t4,t54]
def v972 := [t211,t0,t1,t2,t3,t4,t54]
def v973 := [t0,t212,t1,t2,t3,t4,t54]
def v974 := [t180,t0,t1,t2,t4,t54,t178]
def v975 := [t0,t1,t2,t3,t4,t54,t178]
def v976 := [t0,t1,t2,t213,t3,t4,t54]
def v977 := [t204,t0,t1,t2,t3,t4,t54]
def v978 := [t0,t101,t1,t2,t3,t4,t54]
def v979 := [t117,t0,t1,t2,t3,t4,t54]
def v980 := [t0,t1,t2,t3,t4,t214,t54]
def v981 := [t215,t0,t1,t2,t3,t4,t54]
def v982 := [t0,t1,t2,t114,t3,t4,t54]
def v983 := [t0,t1,t2,t177,t3,t4]
def v984 := [t180,t0,t1,t2,t177,t3,t4]
def v985 := [t0,t1,t2,t177,t3,t4,t54]
def v986 := [t180,t0,t1,t2,t37,t4,t54]
def v987 := [t180,t80,t0,t1,t2,t4,t54]
def v988 := [t180,t169,t0,t1,t2,t3,t4]
def v989 := [t180,t0,t1,t2,t3,t4,t170]
def v990 := [t171,t180,t0,t1,t2,t3,t4]
def v991 := [t180,t172,t0,t1,t2,t3,t4]
def v992 := [t180,t0,t1,t2,t40,t4,t54]
def v993 := [t180,t93,t0,t1,t2,t4,t54]
def v994 := [t180,t0,t1,t173,t2,t3,t4]
def v995 := [t180,t0,t1,t2,t3,t4,t174]
def v996 := [t175,t180,t0,t1,t2,t3,t4]
def v997 := [t180,t176,t0,t1,t2,t3,t4]
def v998 := [t180,t0,t1,t2,t102,t4,t54]
def v999 := [t180,t107,t0,t1,t2,t4,t54]
def v1000 := [t180,t0,t1,t2,t4,t115,t54]
def v1001 := [t116,t180,t0,t1,t2,t4,t54]
def v1002 := [t179,t180,t0,t1,t2,t4]
def v1003 := [t179,t180,t0,t1,t2,t3,t4]
def v1004 := [t179,t180,t0,t1,t2,t4,t54]
def v1005 := [t180,t0,t53,t2,t3,t54]
def v1006 := [t180,t0,t53,t1,t2,t3,t54]
def v1007 := [t180,t0,t53,t2,t3,t4,t54]
def v1008 := [t55,t180,t0,t1,t2,t3,t54]
def v1009 := [t180,t56,t0,t2,t3,t4,t54]
def v1010 := [t0,t99,t1,t2,t3,t4,t54]
def v1011 := [t0,t1,t2,t3,t40,t4,t54]
def v1012 := [t100,t0,t1,t2,t3,t4,t54]
def v1013 := [t93,t0,t1,t2,t3,t4,t54]
def v1014 := [t0,t87,t1,t2,t3,t4,t54]
def v1015 := [t0,t1,t2,t88,t3,t4,t54]
def v1016 := [t90,t0,t1,t2,t3,t4,t54]
def v1017 := [t0,t1,t94,t2,t3,t4,t54]
def v1018 := [t0,t1,t2,t3,t4,t95,t54]
def v1019 := [t96,t0,t1,t2,t3,t4,t54]
def v1020 := [t97,t0,t1,t2,t3,t4,t54]
def v1021 := [t0,t1,t173,t2,t3,t4]
def v1022 := [t0,t1,t173,t2,t3,t4,t54]
def v1023 := [t0,t1,t2,t3,t4,t174]
def v1024 := [t0,t1,t2,t3,t4,t54,t174]
def v1025 := [t175,t0,t1,t2,t3,t4]
def v1026 := [t175,t0,t1,t2,t3,t4,t54]
def v1027 := [t176,t0,t1,t2,t3,t4]
def v1028 := [t176,t0,t1,t2,t3,t4,t54]
def v1029 := [t0,t1,t2,t3,t102,t4,t54]
def v1030 := [t107,t0,t1,t2,t3,t4,t54]
def v1031 := [t0,t1,t2,t3,t4,t115,t54]
def v1032 := [t116,t0,t1,t2,t3,t4,t54]
def v1033 := [t179,t0,t1,t2,t3,t4]
def v1034 := [t179,t0,t1,t2,t3,t4,t54]
def v1035 := [t0,t53,t2,t3,t54]
def v1036 := [t0,t53,t1,t2,t3,t54]
def v1037 := [t0,t53,t2,t3,t4,t54]
def v1038 := [t0,t53,t1,t2,t3,t4,t54]
def v1039 := [t55,t0,t1,t2,t3,t54]
def v1040 := [t56,t0,t2,t3,t4,t54]
def v1041 := [t55,t0,t1,t2,t3,t4,t54]
def v1042 := [t56,t0,t1,t2,t3,t4,t54]
def v1043 := [t56,t0,t1,t2,t3,t4]
def v1044 := [t55,t0,t1,t2,t3,t4]
theorem b0 : Ban 12 5 v3 := checkedSmall
theorem b1 : Ban 12 5 v4 := checkedSmall
theorem b2 : Ban 12 5 v5 := checkedSmall
theorem b3 : Ban 12 5 v6 := checkedSmall
theorem b4 : Ban 12 5 v7 := checkedSmall
theorem b5 : Ban 12 5 v8 := checkedSmall
theorem b6 : Ban 12 5 v9 := checkedSmall
theorem b7 : Ban 12 5 v10 := checkedSmall
theorem b8 : Ban 12 5 v11 := checkedSmall
theorem b9 : Ban 12 5 v12 := checkedSmall
theorem b10 : Ban 12 5 v13 := checkedSmall
theorem b11 : Ban 12 5 v14 := checkedSmall
theorem b12 : Ban 12 5 v15 := checkedSmall
theorem b13 : Ban 12 5 v16 := checkedSmall
theorem b14 : Ban 12 5 v17 := checkedSmall
theorem b15 : Ban 12 5 v18 := checkedSmall
theorem b16 : Ban 12 5 v19 := checkedSmall
theorem b17 : Ban 12 5 v20 := checkedSmall
theorem b18 : Ban 12 5 v21 := checkedSmall
theorem b19 : Ban 12 5 v22 := checkedSmall
theorem b20 : Ban 12 5 v23 := checkedSmall
theorem b21 : Ban 12 5 v24 := checkedSmall
theorem b22 : Ban 12 5 v25 := checkedSmall
theorem b23 : Ban 12 5 v26 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b24 : Ban 12 6 v2 := viaBranch (ws := [v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26]) (consBan b0 (consBan b1 (consBan b2 (consBan b3 (consBan b4 (consBan b5 (consBan b6 (consBan b7 (consBan b8 (consBan b9 (consBan b10 (consBan b11 (consBan b12 (consBan b13 (consBan b14 (consBan b15 (consBan b16 (consBan b17 (consBan b18 (consBan b19 (consBan b20 (consBan b21 (consBan b22 (consBan b23 (nilBan 12 5))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b421 : Ban 12 5 v416 := checkedSmall
theorem b422 : Ban 12 5 v417 := checkedSmall
theorem b423 : Ban 12 5 v418 := checkedSmall
theorem b424 : Ban 12 5 v419 := checkedSmall
theorem b425 : Ban 12 5 v420 := checkedSmall
theorem b426 : Ban 12 5 v421 := checkedSmall
theorem b427 : Ban 12 5 v422 := checkedSmall
theorem b428 : Ban 12 5 v423 := checkedSmall
theorem b429 : Ban 12 5 v424 := checkedSmall
theorem b430 : Ban 12 5 v425 := checkedSmall
theorem b431 : Ban 12 5 v426 := checkedSmall
theorem b432 : Ban 12 5 v427 := checkedSmall
theorem b433 : Ban 12 5 v428 := checkedSmall
theorem b434 : Ban 12 5 v429 := checkedSmall
theorem b435 : Ban 12 5 v430 := checkedSmall
theorem b436 : Ban 12 5 v431 := checkedSmall
theorem b437 : Ban 12 5 v432 := checkedSmall
theorem b212 : Ban 12 5 v215 := checkedSmall
theorem b438 : Ban 12 5 v433 := checkedSmall
theorem b439 : Ban 12 5 v434 := checkedSmall
theorem b440 : Ban 12 5 v435 := checkedSmall
theorem b441 : Ban 12 5 v436 := checkedSmall
theorem b442 : Ban 12 5 v437 := checkedSmall
theorem b443 : Ban 12 5 v438 := checkedSmall
theorem b444 : Ban 12 5 v439 := checkedSmall
theorem b445 : Ban 12 5 v440 := checkedSmall
theorem b446 : Ban 12 5 v441 := checkedSmall
theorem b447 : Ban 12 5 v442 := checkedSmall
theorem b448 : Ban 12 5 v443 := checkedSmall
theorem b449 : Ban 12 5 v444 := checkedSmall
theorem b450 : Ban 12 5 v445 := checkedSmall
theorem b451 : Ban 12 5 v446 := checkedSmall
theorem b452 : Ban 12 5 v447 := checkedSmall
theorem b453 : Ban 12 5 v448 := checkedSmall
theorem b454 : Ban 12 5 v449 := checkedSmall
theorem b455 : Ban 12 5 v450 := checkedSmall
theorem b456 : Ban 12 5 v451 := checkedSmall
theorem b457 : Ban 12 5 v452 := checkedSmall
theorem b458 : Ban 12 5 v453 := checkedSmall
theorem b459 : Ban 12 5 v454 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b460 : Ban 12 6 v17 := viaBranch (ws := [v9,v416,v417,v418,v419,v420,v7,v421,v422,v15,v423,v424,v16,v425,v26,v426,v427,v428,v429,v430,v23,v431,v432,v215,v433,v434,v435,v436,v437,v438,v439,v440,v441,v442,v443,v444,v445,v446,v447,v448,v449,v450,v451,v452,v453,v454]) (consBan b6 (consBan b421 (consBan b422 (consBan b423 (consBan b424 (consBan b425 (consBan b4 (consBan b426 (consBan b427 (consBan b12 (consBan b428 (consBan b429 (consBan b13 (consBan b430 (consBan b23 (consBan b431 (consBan b432 (consBan b433 (consBan b434 (consBan b435 (consBan b20 (consBan b436 (consBan b437 (consBan b212 (consBan b438 (consBan b439 (consBan b440 (consBan b441 (consBan b442 (consBan b443 (consBan b444 (consBan b445 (consBan b446 (consBan b447 (consBan b448 (consBan b449 (consBan b450 (consBan b451 (consBan b452 (consBan b453 (consBan b454 (consBan b455 (consBan b456 (consBan b457 (consBan b458 (consBan b459 (nilBan 12 5))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w6 : Wide 12 6 v17 := viaSub (ws := [v2,v17]) (consBan b24 (consBan b460 (nilBan 12 6))) (by decide) (by decide +kernel)
theorem b25 : Ban 29 8 v1 := smallByCut p31_29 w6
theorem b26 : Ban 29 7 v28 := smallByCut p31_29 w6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w0 : Wide 12 6 v2 := viaSub (ws := [v2]) (consBan b24 (nilBan 12 6)) (by decide) (by decide +kernel)
theorem b29 : Ban 12 5 v2 := bySubset w0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w15 : Wide 12 5 v20 := viaSub (ws := [v2,v20]) (consBan b29 (consBan b17 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b27 : Ban 29 7 v29 := smallByCut p31_30 w15
theorem b28 : Ban 29 7 v30 := smallByCut p31_29 w15
theorem b30 : Ban 29 7 v31 := smallByCut p31_29 w15
theorem b32 : Ban 29 7 v32 := smallByCut p31_30 w15
theorem b34 : Ban 29 7 v34 := smallByCut p31_30 w15
theorem b35 : Ban 29 7 v36 := smallByCut p31_29 w15
theorem b36 : Ban 29 7 v37 := smallByCut p31_29 w15
theorem b38 : Ban 29 7 v38 := smallByCut p31_30 w15
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w2 : Wide 12 5 v16 := viaSub (ws := [v2,v16]) (consBan b29 (consBan b13 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b39 : Ban 29 6 v42 := smallByCut p31_29 w2
theorem b40 : Ban 29 5 v44 := smallByCut p31_27 w2
theorem b41 : Ban 29 5 v45 := smallByCut p31_27 w2
theorem b42 : Ban 29 5 v46 := smallByCut p31_27 w2
theorem b43 : Ban 29 5 v47 := checkedSmall
theorem b44 : Ban 29 5 v48 := smallByCut p31_29 w2
theorem b45 : Ban 29 5 v49 := smallByCut p31_29 w2
theorem b46 : Ban 29 5 v50 := smallByCut p31_29 w2
theorem b47 : Ban 29 5 v51 := checkedSmall
theorem b48 : Ban 29 5 v52 := smallByCut p31_30 w2
theorem b49 : Ban 29 5 v53 := smallByCut p31_30 w2
theorem b50 : Ban 29 5 v54 := smallByCut p31_30 w2
theorem b51 : Ban 29 5 v55 := checkedSmall
theorem b52 : Ban 29 5 v56 := checkedSmall
theorem b53 : Ban 29 5 v57 := checkedSmall
theorem b54 : Ban 29 5 v58 := checkedSmall
theorem b55 : Ban 29 5 v59 := checkedSmall
theorem b56 : Ban 29 5 v60 := smallByCut p31_27 w15
theorem b57 : Ban 29 5 v61 := smallByCut p31_29 w15
theorem b58 : Ban 29 5 v62 := smallByCut p31_27 w15
theorem b59 : Ban 29 5 v63 := smallByCut p31_27 w2
theorem b60 : Ban 29 5 v64 := smallByCut p31_27 w2
theorem b61 : Ban 29 5 v65 := smallByCut p31_29 w15
theorem b62 : Ban 29 5 v66 := smallByCut p31_29 w2
theorem b63 : Ban 29 5 v67 := smallByCut p31_27 w15
theorem b64 : Ban 29 5 v68 := smallByCut p31_27 w2
theorem b65 : Ban 29 5 v69 := smallByCut p31_27 w15
theorem b66 : Ban 29 5 v70 := smallByCut p31_30 w15
theorem b67 : Ban 29 5 v71 := smallByCut p31_27 w15
theorem b68 : Ban 29 5 v72 := smallByCut p31_27 w2
theorem b69 : Ban 29 5 v73 := smallByCut p31_30 w15
theorem b70 : Ban 29 5 v74 := smallByCut p31_30 w2
theorem b71 : Ban 29 5 v75 := smallByCut p31_27 w2
theorem b72 : Ban 29 5 v76 := smallByCut p31_27 w2
theorem b73 : Ban 29 5 v77 := checkedSmall
theorem b74 : Ban 29 5 v78 := smallByCut p31_27 w2
theorem b75 : Ban 29 5 v79 := smallByCut p31_29 w15
theorem b76 : Ban 29 5 v80 := smallByCut p31_30 w15
theorem b77 : Ban 29 5 v81 := smallByCut p31_29 w15
theorem b78 : Ban 29 5 v82 := smallByCut p31_29 w2
theorem b79 : Ban 29 5 v83 := smallByCut p31_29 w2
theorem b80 : Ban 29 5 v84 := smallByCut p31_29 w2
theorem b81 : Ban 29 5 v85 := checkedSmall
theorem b82 : Ban 29 5 v86 := smallByCut p31_29 w2
theorem b83 : Ban 29 5 v87 := smallByCut p31_30 w2
theorem b84 : Ban 29 5 v88 := smallByCut p31_30 w2
theorem b85 : Ban 29 5 v89 := checkedSmall
theorem b86 : Ban 29 5 v90 := smallByCut p31_30 w2
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b87 : Ban 29 6 v43 := viaBranch (ws := [v44,v45,v46,v47,v48,v49,v50,v51,v52,v53,v54,v55,v56,v57,v58,v59,v60,v61,v62,v63,v64,v65,v66,v67,v68,v69,v70,v71,v72,v73,v74,v75,v76,v77,v78,v79,v80,v81,v82,v83,v84,v85,v86,v87,v88,v89,v90]) (consBan b40 (consBan b41 (consBan b42 (consBan b43 (consBan b44 (consBan b45 (consBan b46 (consBan b47 (consBan b48 (consBan b49 (consBan b50 (consBan b51 (consBan b52 (consBan b53 (consBan b54 (consBan b55 (consBan b56 (consBan b57 (consBan b58 (consBan b59 (consBan b60 (consBan b61 (consBan b62 (consBan b63 (consBan b64 (consBan b65 (consBan b66 (consBan b67 (consBan b68 (consBan b69 (consBan b70 (consBan b71 (consBan b72 (consBan b73 (consBan b74 (consBan b75 (consBan b76 (consBan b77 (consBan b78 (consBan b79 (consBan b80 (consBan b81 (consBan b82 (consBan b83 (consBan b84 (consBan b85 (consBan b86 (nilBan 29 5)))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b88 : Ban 29 6 v91 := smallByCut p31_30 w2
theorem b89 : Ban 29 6 v92 := smallByCut p31_29 w2
theorem b90 : Ban 29 6 v93 := smallByCut p31_29 w2
theorem b91 : Ban 29 6 v94 := smallByCut p31_27 w6
theorem b92 : Ban 29 6 v95 := smallByCut p31_27 w6
theorem b93 : Ban 29 6 v96 := smallByCut p31_29 w2
theorem b94 : Ban 29 6 v97 := smallByCut p31_29 w2
theorem b95 : Ban 29 6 v98 := smallByCut p31_30 w2
theorem b193 : Ban 12 5 v196 := checkedSmall
theorem b194 : Ban 12 5 v197 := checkedSmall
theorem b195 : Ban 12 5 v198 := checkedSmall
theorem b196 : Ban 12 5 v199 := checkedSmall
theorem b197 : Ban 12 5 v200 := checkedSmall
theorem b198 : Ban 12 5 v201 := checkedSmall
theorem b199 : Ban 12 5 v202 := checkedSmall
theorem b200 : Ban 12 5 v203 := checkedSmall
theorem b201 : Ban 12 5 v204 := checkedSmall
theorem b202 : Ban 12 5 v205 := checkedSmall
theorem b203 : Ban 12 5 v206 := checkedSmall
theorem b204 : Ban 12 5 v207 := checkedSmall
theorem b205 : Ban 12 5 v208 := checkedSmall
theorem b206 : Ban 12 5 v209 := checkedSmall
theorem b207 : Ban 12 5 v210 := checkedSmall
theorem b208 : Ban 12 5 v211 := checkedSmall
theorem b209 : Ban 12 5 v212 := checkedSmall
theorem b210 : Ban 12 5 v213 := checkedSmall
theorem b211 : Ban 12 5 v214 := checkedSmall
theorem b213 : Ban 12 5 v216 := checkedSmall
theorem b214 : Ban 12 5 v217 := checkedSmall
theorem b215 : Ban 12 5 v218 := checkedSmall
theorem b216 : Ban 12 5 v219 := checkedSmall
theorem b217 : Ban 12 5 v220 := checkedSmall
theorem b218 : Ban 12 5 v221 := checkedSmall
theorem b219 : Ban 12 5 v222 := checkedSmall
theorem b220 : Ban 12 5 v223 := checkedSmall
theorem b221 : Ban 12 5 v224 := checkedSmall
theorem b222 : Ban 12 5 v225 := checkedSmall
theorem b223 : Ban 12 5 v226 := checkedSmall
theorem b224 : Ban 12 5 v227 := checkedSmall
theorem b225 : Ban 12 5 v228 := checkedSmall
theorem b226 : Ban 12 5 v229 := checkedSmall
theorem b227 : Ban 12 5 v230 := checkedSmall
theorem b228 : Ban 12 5 v231 := checkedSmall
theorem b229 : Ban 12 5 v232 := checkedSmall
theorem b230 : Ban 12 5 v233 := checkedSmall
theorem b231 : Ban 12 5 v234 := checkedSmall
theorem b232 : Ban 12 5 v235 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b233 : Ban 12 6 v4 := viaBranch (ws := [v196,v197,v198,v199,v200,v201,v202,v203,v6,v204,v205,v206,v207,v208,v209,v210,v211,v5,v212,v213,v214,v215,v216,v217,v218,v219,v220,v221,v222,v223,v224,v225,v16,v17,v226,v227,v19,v228,v229,v230,v231,v22,v232,v233,v234,v235]) (consBan b193 (consBan b194 (consBan b195 (consBan b196 (consBan b197 (consBan b198 (consBan b199 (consBan b200 (consBan b3 (consBan b201 (consBan b202 (consBan b203 (consBan b204 (consBan b205 (consBan b206 (consBan b207 (consBan b208 (consBan b2 (consBan b209 (consBan b210 (consBan b211 (consBan b212 (consBan b213 (consBan b214 (consBan b215 (consBan b216 (consBan b217 (consBan b218 (consBan b219 (consBan b220 (consBan b221 (consBan b222 (consBan b13 (consBan b14 (consBan b223 (consBan b224 (consBan b16 (consBan b225 (consBan b226 (consBan b227 (consBan b228 (consBan b19 (consBan b229 (consBan b230 (consBan b231 (consBan b232 (nilBan 12 5))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w3 : Wide 12 6 v4 := viaSub (ws := [v2,v4]) (consBan b24 (consBan b233 (nilBan 12 6))) (by decide) (by decide +kernel)
theorem b96 : Ban 29 6 v99 := smallByCut p31_27 w3
theorem b97 : Ban 29 6 v100 := smallByCut p31_30 w2
theorem b98 : Ban 29 6 v101 := smallByCut p31_30 w2
theorem b99 : Ban 29 6 v102 := smallByCut p31_27 w15
theorem b100 : Ban 29 6 v103 := smallByCut p31_27 w15
theorem b101 : Ban 29 6 v104 := smallByCut p31_27 w15
theorem b102 : Ban 29 6 v105 := smallByCut p31_30 w15
theorem b103 : Ban 29 6 v106 := smallByCut p31_30 w15
theorem b104 : Ban 29 6 v107 := smallByCut p31_30 w2
theorem b105 : Ban 29 6 v108 := smallByCut p31_30 w2
theorem b106 : Ban 29 6 v109 := smallByCut p31_29 w2
theorem b107 : Ban 29 6 v110 := smallByCut p31_30 w15
theorem b108 : Ban 29 6 v111 := smallByCut p31_27 w6
theorem b109 : Ban 29 6 v112 := checkedSmall
theorem b110 : Ban 29 6 v113 := smallByCut p31_30 w2
theorem b111 : Ban 29 6 v114 := smallByCut p31_30 w2
theorem b112 : Ban 29 6 v115 := smallByCut p31_30 w2
theorem b113 : Ban 29 6 v116 := smallByCut p31_30 w2
theorem b114 : Ban 29 6 v117 := smallByCut p31_30 w2
theorem b115 : Ban 29 6 v118 := smallByCut p31_29 w2
theorem b116 : Ban 29 6 v119 := smallByCut p31_29 w2
theorem b117 : Ban 29 6 v120 := smallByCut p31_29 w2
theorem b118 : Ban 29 6 v121 := smallByCut p31_29 w2
theorem b119 : Ban 29 6 v122 := smallByCut p31_29 w15
theorem b120 : Ban 29 6 v123 := smallByCut p31_29 w15
theorem b121 : Ban 29 6 v124 := smallByCut p31_29 w2
theorem b122 : Ban 29 6 v125 := smallByCut p31_29 w2
theorem b123 : Ban 29 6 v126 := smallByCut p31_29 w15
theorem b124 : Ban 29 6 v127 := smallByCut p31_29 w2
theorem b125 : Ban 29 6 v128 := smallByCut p31_27 w6
theorem b126 : Ban 29 6 v129 := smallByCut p31_27 w6
theorem b127 : Ban 29 6 v130 := smallByCut p31_27 w15
theorem b128 : Ban 29 6 v131 := smallByCut p31_27 w15
theorem b129 : Ban 29 6 v132 := smallByCut p31_27 w15
theorem b130 : Ban 29 6 v133 := smallByCut p31_29 w2
theorem b131 : Ban 29 6 v134 := smallByCut p31_29 w2
theorem b132 : Ban 29 6 v135 := smallByCut p31_29 w2
theorem b133 : Ban 29 6 v136 := smallByCut p31_29 w2
theorem b134 : Ban 29 6 v137 := smallByCut p31_29 w2
theorem b135 : Ban 29 6 v138 := smallByCut p31_27 w3
theorem b136 : Ban 29 6 v139 := smallByCut p31_29 w2
theorem b137 : Ban 29 6 v140 := checkedSmall
theorem b138 : Ban 29 6 v141 := smallByCut p31_30 w2
theorem b139 : Ban 29 6 v142 := smallByCut p31_30 w2
theorem b140 : Ban 29 6 v143 := smallByCut p31_30 w2
theorem b141 : Ban 29 6 v144 := checkedSmall
theorem b142 : Ban 29 6 v145 := checkedSmall
theorem b143 : Ban 29 6 v146 := checkedSmall
theorem b144 : Ban 29 6 v147 := checkedSmall
theorem b145 : Ban 29 6 v148 := checkedSmall
theorem b146 : Ban 29 6 v149 := smallByCut p31_29 w15
theorem b147 : Ban 29 6 v150 := smallByCut p31_30 w15
theorem b148 : Ban 29 6 v151 := smallByCut p31_29 w15
theorem b149 : Ban 29 6 v152 := smallByCut p31_29 w2
theorem b150 : Ban 29 6 v153 := smallByCut p31_29 w2
theorem b151 : Ban 29 6 v154 := smallByCut p31_29 w2
theorem b152 : Ban 29 6 v155 := checkedSmall
theorem b153 : Ban 29 6 v156 := smallByCut p31_29 w2
theorem b154 : Ban 29 6 v157 := smallByCut p31_30 w2
theorem b155 : Ban 29 6 v158 := smallByCut p31_30 w2
theorem b156 : Ban 29 6 v159 := checkedSmall
theorem b157 : Ban 29 6 v160 := smallByCut p31_30 w2
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b158 : Ban 29 7 v41 := viaBranch (ws := [v42,v43,v91,v92,v93,v94,v95,v96,v97,v98,v99,v100,v101,v102,v103,v104,v105,v106,v107,v108,v109,v110,v111,v112,v113,v114,v115,v116,v117,v118,v119,v120,v121,v122,v123,v124,v125,v126,v127,v128,v129,v130,v131,v132,v133,v134,v135,v136,v137,v138,v139,v140,v141,v142,v143,v144,v145,v146,v147,v148,v149,v150,v151,v152,v153,v154,v155,v156,v157,v158,v159,v160]) (consBan b39 (consBan b87 (consBan b88 (consBan b89 (consBan b90 (consBan b91 (consBan b92 (consBan b93 (consBan b94 (consBan b95 (consBan b96 (consBan b97 (consBan b98 (consBan b99 (consBan b100 (consBan b101 (consBan b102 (consBan b103 (consBan b104 (consBan b105 (consBan b106 (consBan b107 (consBan b108 (consBan b109 (consBan b110 (consBan b111 (consBan b112 (consBan b113 (consBan b114 (consBan b115 (consBan b116 (consBan b117 (consBan b118 (consBan b119 (consBan b120 (consBan b121 (consBan b122 (consBan b123 (consBan b124 (consBan b125 (consBan b126 (consBan b127 (consBan b128 (consBan b129 (consBan b130 (consBan b131 (consBan b132 (consBan b133 (consBan b134 (consBan b135 (consBan b136 (consBan b137 (consBan b138 (consBan b139 (consBan b140 (consBan b141 (consBan b142 (consBan b143 (consBan b144 (consBan b145 (consBan b146 (consBan b147 (consBan b148 (consBan b149 (consBan b150 (consBan b151 (consBan b152 (consBan b153 (consBan b154 (consBan b155 (consBan b156 (consBan b157 (nilBan 29 6))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b159 : Ban 29 7 v40 := viaPerm map31_6 map31_8 b158 (by decide +kernel) (by decide +kernel)
theorem b160 : Ban 29 7 v161 := smallByCut p31_30 w6
theorem b161 : Ban 29 7 v162 := smallByCut p31_29 w6
theorem b162 : Ban 29 7 v163 := smallByCut p31_30 w15
theorem b164 : Ban 29 7 v164 := smallByCut p31_30 w6
theorem b165 : Ban 29 7 v166 := smallByCut p31_30 w15
theorem b166 : Ban 29 7 v167 := smallByCut p31_30 w6
theorem b168 : Ban 29 7 v168 := smallByCut p31_30 w15
theorem b170 : Ban 29 7 v170 := smallByCut p31_30 w6
theorem b172 : Ban 29 7 v172 := smallByCut p31_29 w15
theorem b173 : Ban 29 7 v174 := smallByCut p31_30 w15
theorem b174 : Ban 29 7 v175 := smallByCut p31_30 w6
theorem b175 : Ban 29 7 v176 := smallByCut p31_30 w15
theorem b176 : Ban 29 7 v177 := smallByCut p31_30 w6
theorem b177 : Ban 29 7 v178 := smallByCut p31_29 w15
theorem b178 : Ban 29 7 v179 := viaPerm map31_2 map31_2 b158 (by decide +kernel) (by decide +kernel)
theorem b179 : Ban 29 7 v180 := smallByCut p31_29 w6
theorem b180 : Ban 29 7 v181 := smallByCut p31_29 w6
theorem b181 : Ban 29 7 v182 := smallByCut p31_29 w15
theorem b182 : Ban 29 7 v183 := smallByCut p31_29 w6
theorem b183 : Ban 29 7 v184 := smallByCut p31_29 w15
theorem b184 : Ban 29 7 v185 := smallByCut p31_29 w6
theorem b167 : Ban 29 7 v169 := smallByCut p31_29 w15
theorem b185 : Ban 29 7 v186 := smallByCut p31_29 w6
theorem b186 : Ban 29 7 v187 := smallByCut p31_30 w15
theorem b187 : Ban 29 7 v188 := smallByCut p31_29 w15
theorem b188 : Ban 29 7 v189 := smallByCut p31_29 w6
theorem b189 : Ban 29 7 v190 := smallByCut p31_29 w15
theorem b190 : Ban 29 7 v191 := smallByCut p31_29 w6
theorem b238 : Ban 12 5 v239 := checkedSmall
theorem b239 : Ban 12 5 v240 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w4 : Wide 12 5 v240 := viaSub (ws := [v239,v240]) (consBan b238 (consBan b239 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b192 : Ban 29 7 v192 := smallByCut p31_23 w4
theorem b234 : Ban 29 7 v195 := smallByCut p31_27 w3
theorem b235 : Ban 29 7 v194 := viaPerm map31_8 map31_6 b234 (by decide +kernel) (by decide +kernel)
theorem b237 : Ban 29 7 v236 := smallByCut p31_27 w2
theorem b240 : Ban 29 7 v238 := smallByCut p31_23 w4
theorem b242 : Ban 29 7 v241 := smallByCut p31_27 w15
theorem b244 : Ban 29 7 v243 := smallByCut p31_27 w2
theorem b245 : Ban 29 6 v246 := smallByCut p31_29 w2
theorem b246 : Ban 29 6 v247 := smallByCut p31_27 w2
theorem b247 : Ban 29 6 v248 := smallByCut p31_29 w2
theorem b248 : Ban 29 6 v249 := smallByCut p31_29 w2
theorem b249 : Ban 29 6 v250 := smallByCut p31_27 w2
theorem b250 : Ban 29 6 v251 := smallByCut p31_27 w2
theorem b251 : Ban 29 6 v252 := smallByCut p31_27 w2
theorem b252 : Ban 29 6 v253 := smallByCut p31_27 w2
theorem b253 : Ban 29 6 v254 := smallByCut p31_30 w2
theorem b254 : Ban 29 6 v255 := smallByCut p31_30 w2
theorem b255 : Ban 29 6 v256 := smallByCut p31_30 w2
theorem b256 : Ban 29 6 v257 := smallByCut p31_30 w2
theorem b257 : Ban 29 6 v258 := smallByCut p31_30 w2
theorem b258 : Ban 29 6 v259 := smallByCut p31_30 w2
theorem b259 : Ban 29 6 v260 := smallByCut p31_30 w2
theorem b260 : Ban 29 6 v261 := smallByCut p31_30 w2
theorem b261 : Ban 29 6 v262 := smallByCut p31_30 w2
theorem b262 : Ban 29 6 v263 := checkedSmall
theorem b263 : Ban 29 6 v264 := smallByCut p31_30 w2
theorem b264 : Ban 29 6 v265 := smallByCut p31_27 w2
theorem b265 : Ban 29 6 v266 := smallByCut p31_27 w2
theorem b266 : Ban 29 6 v267 := smallByCut p31_27 w2
theorem b267 : Ban 29 6 v268 := smallByCut p31_27 w2
theorem b268 : Ban 29 6 v269 := smallByCut p31_29 w2
theorem b269 : Ban 29 6 v270 := smallByCut p31_29 w2
theorem b270 : Ban 29 6 v271 := smallByCut p31_29 w2
theorem b271 : Ban 29 6 v272 := smallByCut p31_29 w2
theorem b272 : Ban 29 6 v273 := smallByCut p31_29 w2
theorem b273 : Ban 29 6 v274 := smallByCut p31_29 w2
theorem b274 : Ban 29 6 v275 := smallByCut p31_29 w2
theorem b275 : Ban 29 6 v276 := smallByCut p31_29 w2
theorem b276 : Ban 29 6 v277 := smallByCut p31_27 w6
theorem solidb429 : Wide 12 5 v424 := solid b429
theorem b277 : Ban 29 6 v278 := smallByCut p31_27 solidb429
theorem b278 : Ban 29 6 v279 := smallByCut p31_29 w2
theorem b279 : Ban 29 6 v280 := smallByCut p31_27 w2
theorem b280 : Ban 29 6 v281 := smallByCut p31_27 w2
theorem b281 : Ban 29 6 v282 := smallByCut p31_27 w2
theorem b282 : Ban 29 6 v283 := smallByCut p31_27 w2
theorem b283 : Ban 29 6 v284 := smallByCut p31_27 w2
theorem b284 : Ban 29 6 v285 := smallByCut p31_27 w2
theorem b285 : Ban 29 6 v286 := smallByCut p31_27 w2
theorem b286 : Ban 29 6 v287 := smallByCut p31_27 w2
theorem b287 : Ban 29 6 v288 := smallByCut p31_29 w6
theorem b288 : Ban 29 6 v289 := smallByCut p31_29 solidb429
theorem b289 : Ban 29 6 v290 := smallByCut p31_27 w2
theorem b290 : Ban 29 6 v291 := checkedSmall
theorem b291 : Ban 29 6 v292 := checkedSmall
theorem b292 : Ban 29 6 v293 := checkedSmall
theorem b293 : Ban 29 6 v294 := checkedSmall
theorem b294 : Ban 29 6 v295 := checkedSmall
theorem b295 : Ban 29 6 v296 := checkedSmall
theorem b296 : Ban 29 6 v297 := checkedSmall
theorem b297 : Ban 29 6 v298 := checkedSmall
theorem b298 : Ban 29 6 v299 := checkedSmall
theorem b299 : Ban 29 6 v300 := checkedSmall
theorem b300 : Ban 29 6 v301 := checkedSmall
theorem b301 : Ban 29 6 v302 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b302 : Ban 29 7 v245 := viaBranch (ws := [v246,v247,v248,v249,v250,v251,v252,v253,v254,v255,v256,v257,v258,v259,v260,v261,v262,v263,v264,v265,v266,v267,v268,v269,v270,v271,v272,v273,v274,v275,v276,v277,v278,v279,v280,v281,v282,v283,v284,v285,v286,v287,v288,v289,v290,v291,v292,v293,v294,v295,v296,v297,v298,v299,v300,v301,v302]) (consBan b245 (consBan b246 (consBan b247 (consBan b248 (consBan b249 (consBan b250 (consBan b251 (consBan b252 (consBan b253 (consBan b254 (consBan b255 (consBan b256 (consBan b257 (consBan b258 (consBan b259 (consBan b260 (consBan b261 (consBan b262 (consBan b263 (consBan b264 (consBan b265 (consBan b266 (consBan b267 (consBan b268 (consBan b269 (consBan b270 (consBan b271 (consBan b272 (consBan b273 (consBan b274 (consBan b275 (consBan b276 (consBan b277 (consBan b278 (consBan b279 (consBan b280 (consBan b281 (consBan b282 (consBan b283 (consBan b284 (consBan b285 (consBan b286 (consBan b287 (consBan b288 (consBan b289 (consBan b290 (consBan b291 (consBan b292 (consBan b293 (consBan b294 (consBan b295 (consBan b296 (consBan b297 (consBan b298 (consBan b299 (consBan b300 (consBan b301 (nilBan 29 6)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b303 : Ban 29 6 v303 := smallByCut p31_29 w2
theorem b304 : Ban 29 6 v304 := smallByCut p31_29 w2
theorem b305 : Ban 29 6 v305 := smallByCut p31_29 w2
theorem b306 : Ban 29 6 v306 := smallByCut p31_30 w2
theorem b307 : Ban 29 6 v307 := smallByCut p31_29 w2
theorem b308 : Ban 29 6 v308 := smallByCut p31_27 w2
theorem b309 : Ban 29 6 v309 := smallByCut p31_27 w2
theorem b310 : Ban 29 6 v310 := checkedSmall
theorem b311 : Ban 29 6 v311 := smallByCut p31_30 w2
theorem b312 : Ban 29 6 v312 := checkedSmall
theorem b313 : Ban 29 6 v313 := smallByCut p31_27 w2
theorem b314 : Ban 29 6 v314 := smallByCut p31_27 w2
theorem b315 : Ban 29 6 v315 := smallByCut p31_27 solidb429
theorem b316 : Ban 29 6 v316 := smallByCut p31_29 w2
theorem b317 : Ban 29 6 v317 := smallByCut p31_27 solidb429
theorem b319 : Ban 29 6 v318 := smallByCut p31_27 w2
theorem b320 : Ban 29 6 v320 := smallByCut p31_27 w2
theorem b321 : Ban 29 6 v321 := smallByCut p31_27 w2
theorem b322 : Ban 29 6 v322 := smallByCut p31_27 w2
theorem b323 : Ban 29 6 v323 := smallByCut p31_29 solidb429
theorem b324 : Ban 29 6 v324 := smallByCut p31_29 w6
theorem b325 : Ban 29 6 v325 := smallByCut p31_27 w2
theorem b326 : Ban 29 6 v326 := smallByCut p31_27 w2
theorem b327 : Ban 29 6 v327 := smallByCut p31_27 w2
theorem b328 : Ban 29 6 v328 := checkedSmall
theorem b329 : Ban 29 6 v329 := checkedSmall
theorem b330 : Ban 29 6 v330 := checkedSmall
theorem b331 : Ban 29 6 v331 := checkedSmall
theorem b332 : Ban 29 6 v332 := smallByCut p31_27 w2
theorem b333 : Ban 29 6 v333 := smallByCut p31_27 w2
theorem b334 : Ban 29 6 v334 := checkedSmall
theorem b335 : Ban 29 6 v335 := smallByCut p31_27 w2
theorem b336 : Ban 29 6 v336 := smallByCut p31_27 w15
theorem b337 : Ban 29 6 v337 := smallByCut p31_27 w2
theorem b338 : Ban 29 6 v338 := checkedSmall
theorem b339 : Ban 29 6 v339 := checkedSmall
theorem b340 : Ban 29 6 v340 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b341 : Ban 29 7 v247 := viaBranch (ws := [v303,v304,v305,v306,v307,v308,v309,v249,v310,v311,v312,v313,v314,v248,v315,v316,v317,v318,v320,v321,v322,v289,v290,v323,v324,v325,v326,v327,v328,v329,v330,v331,v332,v333,v334,v335,v336,v337,v338,v339,v340]) (consBan b303 (consBan b304 (consBan b305 (consBan b306 (consBan b307 (consBan b308 (consBan b309 (consBan b248 (consBan b310 (consBan b311 (consBan b312 (consBan b313 (consBan b314 (consBan b247 (consBan b315 (consBan b316 (consBan b317 (consBan b319 (consBan b320 (consBan b321 (consBan b322 (consBan b288 (consBan b289 (consBan b323 (consBan b324 (consBan b325 (consBan b326 (consBan b327 (consBan b328 (consBan b329 (consBan b330 (consBan b331 (consBan b332 (consBan b333 (consBan b334 (consBan b335 (consBan b336 (consBan b337 (consBan b338 (consBan b339 (consBan b340 (nilBan 29 6)))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b343 : Ban 29 7 v336 := smallByCut p31_27 w15
theorem b345 : Ban 29 7 v337 := smallByCut p31_27 w2
theorem b420 : Ban 29 7 v288 := smallByCut p31_29 w6
theorem b461 : Ban 29 7 v324 := smallByCut p31_29 w6
theorem b462 : Ban 29 7 v455 := smallByCut p31_15 w4
theorem b463 : Ban 29 7 v456 := viaPerm map31_9 map31_7 b234 (by decide +kernel) (by decide +kernel)
theorem b464 : Ban 29 7 v457 := smallByCut p31_27 w2
theorem b465 : Ban 29 7 v458 := smallByCut p31_15 w4
theorem b368 : Ban 12 5 v365 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w20 : Wide 12 5 v365 := viaSub (ws := [v239,v365]) (consBan b238 (consBan b368 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b466 : Ban 29 7 v459 := smallByCut p31_23 w20
theorem b467 : Ban 29 7 v460 := smallByCut p31_23 w4
theorem b468 : Ban 29 7 v461 := smallByCut p31_29 w3
theorem b469 : Ban 29 7 v462 := smallByCut p31_29 w3
theorem b471 : Ban 29 7 v463 := smallByCut p31_23 w20
theorem b473 : Ban 29 7 v465 := smallByCut p31_23 w4
theorem b474 : Ban 29 6 v468 := smallByCut p31_23 w20
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w7 : Wide 12 5 v6 := viaSub (ws := [v2,v6]) (consBan b29 (consBan b3 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b475 : Ban 29 6 v469 := smallByCut p31_29 w7
theorem b476 : Ban 29 6 v470 := smallByCut p31_29 w15
theorem b477 : Ban 29 6 v471 := smallByCut p31_29 w7
theorem b478 : Ban 29 6 v472 := smallByCut p31_29 w15
theorem b479 : Ban 29 6 v473 := smallByCut p31_29 w7
theorem b480 : Ban 29 6 v474 := smallByCut p31_23 w20
theorem b481 : Ban 29 6 v475 := smallByCut p31_30 w7
theorem b482 : Ban 29 6 v476 := smallByCut p31_23 w20
theorem b483 : Ban 29 6 v477 := smallByCut p31_29 w7
theorem b484 : Ban 29 6 v478 := smallByCut p31_30 w15
theorem b485 : Ban 29 6 v479 := smallByCut p31_29 w7
theorem b486 : Ban 29 6 v480 := smallByCut p31_30 w15
theorem b487 : Ban 29 6 v481 := smallByCut p31_29 w7
theorem b488 : Ban 29 6 v482 := smallByCut p31_23 w20
theorem b489 : Ban 29 6 v483 := smallByCut p31_29 w7
theorem b490 : Ban 29 6 v484 := smallByCut p31_15 w20
theorem b491 : Ban 29 6 v485 := checkedSmall
theorem b492 : Ban 29 6 v486 := checkedSmall
theorem b493 : Ban 29 6 v487 := checkedSmall
theorem b346 : Ban 12 5 v343 := checkedSmall
theorem b347 : Ban 12 5 v344 := checkedSmall
theorem b348 : Ban 12 5 v345 := checkedSmall
theorem b349 : Ban 12 5 v346 := checkedSmall
theorem b350 : Ban 12 5 v347 := checkedSmall
theorem b351 : Ban 12 5 v348 := checkedSmall
theorem b352 : Ban 12 5 v349 := checkedSmall
theorem b353 : Ban 12 5 v350 := checkedSmall
theorem b354 : Ban 12 5 v351 := checkedSmall
theorem b355 : Ban 12 5 v352 := checkedSmall
theorem b356 : Ban 12 5 v353 := checkedSmall
theorem b357 : Ban 12 5 v354 := checkedSmall
theorem b358 : Ban 12 5 v355 := checkedSmall
theorem b359 : Ban 12 5 v356 := checkedSmall
theorem b360 : Ban 12 5 v357 := checkedSmall
theorem b361 : Ban 12 5 v358 := checkedSmall
theorem b362 : Ban 12 5 v359 := checkedSmall
theorem b363 : Ban 12 5 v360 := checkedSmall
theorem b364 : Ban 12 5 v361 := checkedSmall
theorem b365 : Ban 12 5 v362 := checkedSmall
theorem b366 : Ban 12 5 v363 := checkedSmall
theorem b367 : Ban 12 5 v364 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b369 : Ban 12 6 v239 := viaBranch (ws := [v343,v240,v344,v345,v346,v347,v348,v349,v350,v351,v352,v353,v354,v355,v356,v357,v358,v359,v360,v361,v362,v363,v364,v365]) (consBan b346 (consBan b239 (consBan b347 (consBan b348 (consBan b349 (consBan b350 (consBan b351 (consBan b352 (consBan b353 (consBan b354 (consBan b355 (consBan b356 (consBan b357 (consBan b358 (consBan b359 (consBan b360 (consBan b361 (consBan b362 (consBan b363 (consBan b364 (consBan b365 (consBan b366 (consBan b367 (consBan b368 (nilBan 12 5))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b370 : Ban 12 5 v367 := checkedSmall
theorem b371 : Ban 12 5 v368 := checkedSmall
theorem b372 : Ban 12 5 v369 := checkedSmall
theorem b373 : Ban 12 5 v370 := checkedSmall
theorem b374 : Ban 12 5 v371 := checkedSmall
theorem b375 : Ban 12 5 v372 := checkedSmall
theorem b376 : Ban 12 5 v373 := checkedSmall
theorem b377 : Ban 12 5 v374 := checkedSmall
theorem b378 : Ban 12 5 v375 := checkedSmall
theorem b379 : Ban 12 5 v376 := checkedSmall
theorem b380 : Ban 12 5 v377 := checkedSmall
theorem b381 : Ban 12 5 v378 := checkedSmall
theorem b382 : Ban 12 5 v379 := checkedSmall
theorem b383 : Ban 12 5 v380 := checkedSmall
theorem b384 : Ban 12 5 v381 := checkedSmall
theorem b385 : Ban 12 5 v382 := checkedSmall
theorem b386 : Ban 12 5 v383 := checkedSmall
theorem b387 : Ban 12 5 v384 := checkedSmall
theorem b388 : Ban 12 5 v385 := checkedSmall
theorem b389 : Ban 12 5 v386 := checkedSmall
theorem b390 : Ban 12 5 v387 := checkedSmall
theorem b391 : Ban 12 5 v388 := checkedSmall
theorem b392 : Ban 12 5 v389 := checkedSmall
theorem b393 : Ban 12 5 v390 := checkedSmall
theorem b394 : Ban 12 5 v391 := checkedSmall
theorem b395 : Ban 12 5 v392 := checkedSmall
theorem b396 : Ban 12 5 v393 := checkedSmall
theorem b397 : Ban 12 5 v394 := checkedSmall
theorem b398 : Ban 12 5 v395 := checkedSmall
theorem b399 : Ban 12 5 v396 := checkedSmall
theorem b400 : Ban 12 5 v397 := checkedSmall
theorem b401 : Ban 12 5 v398 := checkedSmall
theorem b402 : Ban 12 5 v399 := checkedSmall
theorem b403 : Ban 12 5 v400 := checkedSmall
theorem b404 : Ban 12 5 v401 := checkedSmall
theorem b405 : Ban 12 5 v402 := checkedSmall
theorem b406 : Ban 12 5 v403 := checkedSmall
theorem b407 : Ban 12 5 v404 := checkedSmall
theorem b408 : Ban 12 5 v405 := checkedSmall
theorem b409 : Ban 12 5 v406 := checkedSmall
theorem b410 : Ban 12 5 v407 := checkedSmall
theorem b411 : Ban 12 5 v408 := checkedSmall
theorem b412 : Ban 12 5 v409 := checkedSmall
theorem b413 : Ban 12 5 v410 := checkedSmall
theorem b414 : Ban 12 5 v411 := checkedSmall
theorem b415 : Ban 12 5 v412 := checkedSmall
theorem b416 : Ban 12 5 v413 := checkedSmall
theorem b417 : Ban 12 5 v414 := checkedSmall
theorem b418 : Ban 12 5 v415 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b419 : Ban 12 6 v366 := viaBranch (ws := [v367,v368,v369,v370,v348,v371,v372,v373,v346,v374,v375,v376,v377,v378,v379,v380,v381,v382,v383,v384,v385,v386,v356,v387,v388,v389,v354,v390,v391,v392,v393,v394,v395,v396,v397,v398,v399,v400,v401,v402,v403,v404,v405,v365,v406,v407,v408,v409,v410,v362,v411,v412,v413,v414,v415]) (consBan b370 (consBan b371 (consBan b372 (consBan b373 (consBan b351 (consBan b374 (consBan b375 (consBan b376 (consBan b349 (consBan b377 (consBan b378 (consBan b379 (consBan b380 (consBan b381 (consBan b382 (consBan b383 (consBan b384 (consBan b385 (consBan b386 (consBan b387 (consBan b388 (consBan b389 (consBan b359 (consBan b390 (consBan b391 (consBan b392 (consBan b357 (consBan b393 (consBan b394 (consBan b395 (consBan b396 (consBan b397 (consBan b398 (consBan b399 (consBan b400 (consBan b401 (consBan b402 (consBan b403 (consBan b404 (consBan b405 (consBan b406 (consBan b407 (consBan b408 (consBan b368 (consBan b409 (consBan b410 (consBan b411 (consBan b412 (consBan b413 (consBan b365 (consBan b414 (consBan b415 (consBan b416 (consBan b417 (consBan b418 (nilBan 12 5)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w5 : Wide 12 6 v366 := viaSub (ws := [v239,v366]) (consBan b369 (consBan b419 (nilBan 12 6))) (by decide) (by decide +kernel)
theorem b494 : Ban 29 6 v488 := smallByCut p31_23 w5
theorem b495 : Ban 29 6 v489 := checkedSmall
theorem b496 : Ban 29 6 v490 := smallByCut p31_15 w20
theorem b497 : Ban 29 6 v491 := checkedSmall
theorem solidb199 : Wide 12 5 v202 := solid b199
theorem b498 : Ban 29 6 v492 := smallByCut p31_29 solidb199
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w13 : Wide 12 5 v4 := viaSub (ws := [v2,v4]) (consBan b29 (consBan b1 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b499 : Ban 29 6 v461 := smallByCut p31_29 w13
theorem b500 : Ban 29 6 v493 := smallByCut p31_23 w4
theorem b501 : Ban 29 6 v494 := smallByCut p31_15 w20
theorem b502 : Ban 29 6 v495 := checkedSmall
theorem b503 : Ban 29 6 v496 := checkedSmall
theorem b504 : Ban 29 6 v497 := checkedSmall
theorem b505 : Ban 29 6 v498 := checkedSmall
theorem b506 : Ban 29 6 v499 := checkedSmall
theorem b507 : Ban 29 6 v500 := smallByCut p31_15 w20
theorem b508 : Ban 29 6 v501 := checkedSmall
theorem b509 : Ban 29 6 v502 := smallByCut p31_29 w7
theorem b510 : Ban 29 6 v503 := smallByCut p31_29 w7
theorem b511 : Ban 29 6 v504 := smallByCut p31_29 w7
theorem b512 : Ban 29 6 v505 := smallByCut p31_29 w7
theorem b513 : Ban 29 6 v506 := smallByCut p31_30 w7
theorem b514 : Ban 29 6 v507 := smallByCut p31_30 w7
theorem b515 : Ban 29 6 v508 := smallByCut p31_30 w7
theorem b516 : Ban 29 6 v509 := smallByCut p31_30 w7
theorem b517 : Ban 29 6 v510 := smallByCut p31_30 w7
theorem b518 : Ban 29 6 v511 := smallByCut p31_30 w7
theorem b519 : Ban 29 6 v512 := smallByCut p31_30 w7
theorem b520 : Ban 29 6 v513 := smallByCut p31_30 w7
theorem b521 : Ban 29 6 v514 := smallByCut p31_30 w7
theorem b522 : Ban 29 6 v515 := smallByCut p31_30 w7
theorem b523 : Ban 29 6 v516 := smallByCut p31_30 w7
theorem b524 : Ban 29 6 v517 := smallByCut p31_30 w7
theorem b525 : Ban 29 6 v518 := smallByCut p31_29 w7
theorem b526 : Ban 29 6 v519 := smallByCut p31_29 w7
theorem b527 : Ban 29 6 v520 := smallByCut p31_29 w7
theorem b528 : Ban 29 6 v521 := smallByCut p31_29 w7
theorem b529 : Ban 29 6 v522 := smallByCut p31_29 w7
theorem b530 : Ban 29 6 v523 := smallByCut p31_29 w7
theorem b531 : Ban 29 6 v524 := smallByCut p31_29 w7
theorem b532 : Ban 29 6 v525 := smallByCut p31_29 w7
theorem b533 : Ban 29 6 v526 := smallByCut p31_29 w7
theorem b534 : Ban 29 6 v527 := smallByCut p31_29 w7
theorem b535 : Ban 29 6 v528 := smallByCut p31_29 w7
theorem b536 : Ban 29 6 v529 := smallByCut p31_29 w7
theorem b593 : Ban 12 4 v580 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w8 : Wide 12 4 v580 := viaSub (ws := [v580]) (consBan b593 (nilBan 12 4)) (by decide) (by decide +kernel)
theorem b537 : Ban 29 6 v530 := smallByCut p31_27 w8
theorem b538 : Ban 29 6 v531 := smallByCut p31_23 w4
theorem b539 : Ban 29 6 v532 := smallByCut p31_23 w4
theorem b540 : Ban 29 6 v533 := smallByCut p31_27 w8
theorem b541 : Ban 29 6 v534 := smallByCut p31_23 w4
theorem b542 : Ban 29 6 v535 := smallByCut p31_23 w4
theorem b543 : Ban 29 6 v536 := checkedSmall
theorem b544 : Ban 29 6 v537 := checkedSmall
theorem b545 : Ban 29 6 v538 := checkedSmall
theorem b546 : Ban 29 6 v539 := checkedSmall
theorem b547 : Ban 29 6 v540 := smallByCut p31_23 w4
theorem b548 : Ban 29 6 v541 := checkedSmall
theorem b549 : Ban 29 6 v542 := smallByCut p31_23 w4
theorem b550 : Ban 29 6 v543 := smallByCut p31_23 w4
theorem b551 : Ban 29 6 v544 := smallByCut p31_23 w4
theorem b552 : Ban 29 6 v545 := smallByCut p31_23 w4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b553 : Ban 29 7 v467 := viaBranch (ws := [v468,v469,v470,v471,v472,v473,v474,v475,v476,v477,v478,v479,v480,v481,v482,v483,v484,v485,v486,v487,v488,v489,v490,v491,v492,v461,v493,v494,v495,v496,v497,v498,v499,v500,v501,v502,v503,v504,v505,v506,v507,v508,v509,v510,v511,v512,v513,v514,v515,v516,v517,v518,v519,v520,v521,v522,v523,v524,v525,v526,v527,v528,v529,v530,v531,v532,v533,v534,v535,v536,v537,v538,v539,v540,v541,v542,v543,v544,v545]) (consBan b474 (consBan b475 (consBan b476 (consBan b477 (consBan b478 (consBan b479 (consBan b480 (consBan b481 (consBan b482 (consBan b483 (consBan b484 (consBan b485 (consBan b486 (consBan b487 (consBan b488 (consBan b489 (consBan b490 (consBan b491 (consBan b492 (consBan b493 (consBan b494 (consBan b495 (consBan b496 (consBan b497 (consBan b498 (consBan b499 (consBan b500 (consBan b501 (consBan b502 (consBan b503 (consBan b504 (consBan b505 (consBan b506 (consBan b507 (consBan b508 (consBan b509 (consBan b510 (consBan b511 (consBan b512 (consBan b513 (consBan b514 (consBan b515 (consBan b516 (consBan b517 (consBan b518 (consBan b519 (consBan b520 (consBan b521 (consBan b522 (consBan b523 (consBan b524 (consBan b525 (consBan b526 (consBan b527 (consBan b528 (consBan b529 (consBan b530 (consBan b531 (consBan b532 (consBan b533 (consBan b534 (consBan b535 (consBan b536 (consBan b537 (consBan b538 (consBan b539 (consBan b540 (consBan b541 (consBan b542 (consBan b543 (consBan b544 (consBan b545 (consBan b546 (consBan b547 (consBan b548 (consBan b549 (consBan b550 (consBan b551 (consBan b552 (nilBan 29 6)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b554 : Ban 29 6 v168 := smallByCut p31_30 w15
theorem b555 : Ban 29 6 v546 := smallByCut p31_29 w15
theorem b556 : Ban 29 6 v547 := smallByCut p31_29 w15
theorem b557 : Ban 29 6 v166 := smallByCut p31_30 w15
theorem b558 : Ban 29 6 v169 := smallByCut p31_29 w15
theorem b559 : Ban 29 6 v548 := smallByCut p31_30 w15
theorem b560 : Ban 29 6 v549 := smallByCut p31_30 w15
theorem b561 : Ban 29 6 v184 := smallByCut p31_29 w15
theorem b562 : Ban 29 6 v550 := smallByCut p31_15 w4
theorem b563 : Ban 29 6 v551 := checkedSmall
theorem b564 : Ban 29 6 v552 := checkedSmall
theorem b565 : Ban 29 6 v553 := smallByCut p31_15 w4
theorem b566 : Ban 29 6 v554 := smallByCut p31_29 solidb199
theorem b567 : Ban 29 6 v462 := smallByCut p31_29 w13
theorem b568 : Ban 29 6 v459 := smallByCut p31_23 w20
theorem b569 : Ban 29 6 v555 := smallByCut p31_23 w4
theorem b570 : Ban 29 6 v460 := smallByCut p31_23 w4
theorem b571 : Ban 29 6 v556 := smallByCut p31_15 w4
theorem b572 : Ban 29 6 v557 := checkedSmall
theorem b573 : Ban 29 6 v558 := checkedSmall
theorem b574 : Ban 29 6 v559 := smallByCut p31_15 w4
theorem b575 : Ban 29 6 v560 := smallByCut p31_29 w7
theorem b576 : Ban 29 6 v561 := smallByCut p31_29 w7
theorem b577 : Ban 29 6 v562 := smallByCut p31_29 w7
theorem b578 : Ban 29 6 v563 := smallByCut p31_30 w7
theorem b579 : Ban 29 6 v564 := smallByCut p31_29 w7
theorem b580 : Ban 29 6 v565 := checkedSmall
theorem b581 : Ban 29 6 v566 := smallByCut p31_30 w7
theorem b582 : Ban 29 6 v567 := smallByCut p31_30 w7
theorem b583 : Ban 29 6 v568 := smallByCut p31_30 w7
theorem b584 : Ban 29 6 v569 := checkedSmall
theorem b585 : Ban 29 6 v570 := smallByCut p31_29 w7
theorem b586 : Ban 29 6 v571 := smallByCut p31_29 w7
theorem b587 : Ban 29 6 v572 := smallByCut p31_29 w7
theorem b588 : Ban 29 6 v573 := smallByCut p31_23 w4
theorem b589 : Ban 29 6 v574 := checkedSmall
theorem b590 : Ban 29 6 v575 := checkedSmall
theorem b591 : Ban 29 6 v576 := checkedSmall
theorem b592 : Ban 29 6 v577 := checkedSmall
theorem b595 : Ban 29 6 v578 := smallByCut p31_27 w8
theorem b596 : Ban 29 6 v581 := smallByCut p31_23 w4
theorem b597 : Ban 29 6 v582 := smallByCut p31_23 w4
theorem b598 : Ban 29 6 v583 := checkedSmall
theorem b599 : Ban 29 6 v584 := smallByCut p31_23 w4
theorem b600 : Ban 29 6 v585 := checkedSmall
theorem b601 : Ban 29 6 v586 := checkedSmall
theorem b602 : Ban 29 6 v587 := checkedSmall
theorem b603 : Ban 29 6 v588 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b604 : Ban 29 7 v503 := viaBranch (ws := [v168,v546,v547,v166,v169,v548,v549,v184,v550,v551,v552,v553,v554,v462,v459,v555,v460,v556,v557,v558,v559,v560,v561,v562,v563,v564,v565,v566,v567,v568,v505,v569,v570,v571,v572,v504,v573,v574,v575,v328,v576,v577,v492,v493,v578,v581,v582,v583,v584,v585,v586,v587,v588]) (consBan b554 (consBan b555 (consBan b556 (consBan b557 (consBan b558 (consBan b559 (consBan b560 (consBan b561 (consBan b562 (consBan b563 (consBan b564 (consBan b565 (consBan b566 (consBan b567 (consBan b568 (consBan b569 (consBan b570 (consBan b571 (consBan b572 (consBan b573 (consBan b574 (consBan b575 (consBan b576 (consBan b577 (consBan b578 (consBan b579 (consBan b580 (consBan b581 (consBan b582 (consBan b583 (consBan b512 (consBan b584 (consBan b585 (consBan b586 (consBan b587 (consBan b511 (consBan b588 (consBan b589 (consBan b590 (consBan b328 (consBan b591 (consBan b592 (consBan b498 (consBan b500 (consBan b595 (consBan b596 (consBan b597 (consBan b598 (consBan b599 (consBan b600 (consBan b601 (consBan b602 (consBan b603 (nilBan 29 6)))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b605 : Ban 29 7 v589 := smallByCut p31_15 w4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w9 : Wide 12 5 v12 := viaSub (ws := [v2,v12]) (consBan b29 (consBan b9 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b606 : Ban 29 6 v591 := smallByCut p31_29 w9
theorem b607 : Ban 29 6 v592 := smallByCut p31_29 w9
theorem b608 : Ban 29 6 v593 := smallByCut p31_29 w9
theorem b609 : Ban 29 6 v594 := smallByCut p31_30 w9
theorem b610 : Ban 29 6 v595 := smallByCut p31_29 w9
theorem b611 : Ban 29 6 v596 := checkedSmall
theorem b612 : Ban 29 6 v597 := smallByCut p31_30 w9
theorem b613 : Ban 29 6 v598 := smallByCut p31_29 w9
theorem b614 : Ban 29 6 v599 := smallByCut p31_30 w15
theorem b615 : Ban 29 6 v600 := smallByCut p31_30 w15
theorem b616 : Ban 29 6 v601 := smallByCut p31_30 w9
theorem b617 : Ban 29 6 v602 := smallByCut p31_30 w9
theorem b618 : Ban 29 6 v603 := smallByCut p31_30 w15
theorem b619 : Ban 29 6 v604 := checkedSmall
theorem b620 : Ban 29 6 v605 := smallByCut p31_30 w9
theorem b621 : Ban 29 6 v606 := checkedSmall
theorem b622 : Ban 29 6 v607 := checkedSmall
theorem b623 : Ban 29 6 v608 := smallByCut p31_29 w9
theorem b624 : Ban 29 6 v609 := smallByCut p31_29 w9
theorem b625 : Ban 29 6 v610 := smallByCut p31_29 w15
theorem b626 : Ban 29 6 v611 := smallByCut p31_29 w15
theorem b627 : Ban 29 6 v612 := smallByCut p31_29 w9
theorem b628 : Ban 29 6 v613 := smallByCut p31_29 w9
theorem b629 : Ban 29 6 v614 := smallByCut p31_29 w15
theorem b630 : Ban 29 6 v615 := checkedSmall
theorem b631 : Ban 29 6 v616 := smallByCut p31_29 w9
theorem b632 : Ban 29 6 v617 := checkedSmall
theorem b633 : Ban 29 6 v618 := smallByCut p31_27 w9
theorem b634 : Ban 29 6 v619 := smallByCut p31_27 w9
theorem b635 : Ban 29 6 v620 := smallByCut p31_15 w5
theorem b636 : Ban 29 6 v621 := smallByCut p31_27 w2
theorem b637 : Ban 29 6 v622 := checkedSmall
theorem b638 : Ban 29 6 v623 := smallByCut p31_27 w2
theorem b639 : Ban 29 6 v624 := checkedSmall
theorem b640 : Ban 29 6 v625 := smallByCut p31_23 w20
theorem b641 : Ban 29 6 v626 := smallByCut p31_23 w20
theorem b642 : Ban 29 6 v627 := smallByCut p31_23 w4
theorem b643 : Ban 29 6 v628 := smallByCut p31_23 w4
theorem b644 : Ban 29 6 v629 := smallByCut p31_23 w20
theorem b645 : Ban 29 6 v630 := smallByCut p31_15 w4
theorem b646 : Ban 29 6 v631 := smallByCut p31_15 w4
theorem b647 : Ban 29 6 v632 := smallByCut p31_15 w4
theorem b648 : Ban 29 6 v633 := smallByCut p31_23 w4
theorem b649 : Ban 29 6 v634 := smallByCut p31_15 w4
theorem b650 : Ban 29 6 v635 := smallByCut p31_15 w4
theorem b651 : Ban 29 6 v636 := smallByCut p31_15 w20
theorem b652 : Ban 29 6 v637 := smallByCut p31_15 w4
theorem b653 : Ban 29 6 v638 := smallByCut p31_15 w20
theorem b654 : Ban 29 6 v639 := smallByCut p31_15 w4
theorem b655 : Ban 29 6 v640 := checkedSmall
theorem b656 : Ban 29 6 v641 := checkedSmall
theorem b657 : Ban 29 6 v642 := smallByCut p31_15 w4
theorem b658 : Ban 29 6 v643 := smallByCut p31_15 w20
theorem b659 : Ban 29 6 v644 := smallByCut p31_27 w9
theorem b660 : Ban 29 6 v645 := checkedSmall
theorem b661 : Ban 29 6 v646 := smallByCut p31_27 w9
theorem b662 : Ban 29 6 v647 := smallByCut p31_27 w2
theorem b663 : Ban 29 6 v648 := smallByCut p31_27 w2
theorem b664 : Ban 29 6 v649 := checkedSmall
theorem b665 : Ban 29 6 v650 := checkedSmall
theorem b666 : Ban 29 6 v651 := smallByCut p31_27 w15
theorem b667 : Ban 29 6 v652 := smallByCut p31_27 w2
theorem b668 : Ban 29 6 v653 := smallByCut p31_27 w9
theorem b669 : Ban 29 6 v654 := smallByCut p31_15 w4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b670 : Ban 29 7 v590 := viaBranch (ws := [v591,v592,v593,v594,v595,v596,v597,v598,v599,v600,v601,v602,v603,v604,v605,v606,v607,v608,v609,v610,v611,v612,v613,v614,v615,v616,v617,v618,v292,v619,v620,v621,v622,v623,v624,v625,v626,v627,v628,v629,v541,v542,v583,v630,v631,v632,v633,v634,v635,v636,v637,v638,v639,v640,v641,v642,v643,v644,v645,v646,v647,v648,v649,v498,v558,v650,v651,v652,v653,v654]) (consBan b606 (consBan b607 (consBan b608 (consBan b609 (consBan b610 (consBan b611 (consBan b612 (consBan b613 (consBan b614 (consBan b615 (consBan b616 (consBan b617 (consBan b618 (consBan b619 (consBan b620 (consBan b621 (consBan b622 (consBan b623 (consBan b624 (consBan b625 (consBan b626 (consBan b627 (consBan b628 (consBan b629 (consBan b630 (consBan b631 (consBan b632 (consBan b633 (consBan b291 (consBan b634 (consBan b635 (consBan b636 (consBan b637 (consBan b638 (consBan b639 (consBan b640 (consBan b641 (consBan b642 (consBan b643 (consBan b644 (consBan b548 (consBan b549 (consBan b598 (consBan b645 (consBan b646 (consBan b647 (consBan b648 (consBan b649 (consBan b650 (consBan b651 (consBan b652 (consBan b653 (consBan b654 (consBan b655 (consBan b656 (consBan b657 (consBan b658 (consBan b659 (consBan b660 (consBan b661 (consBan b662 (consBan b663 (consBan b664 (consBan b505 (consBan b573 (consBan b665 (consBan b666 (consBan b667 (consBan b668 (consBan b669 (nilBan 29 6))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b672 : Ban 29 7 v654 := smallByCut p31_23 w4
theorem b671 : Ban 29 7 v635 := smallByCut p31_15 w4
theorem b673 : Ban 29 7 v655 := smallByCut p31_15 w20
theorem b674 : Ban 29 7 v656 := smallByCut p31_15 w4
theorem b675 : Ban 29 7 v657 := viaPerm map31_1 map31_1 b468 (by decide +kernel) (by decide +kernel)
theorem b676 : Ban 29 7 v658 := viaPerm map31_1 map31_1 b469 (by decide +kernel) (by decide +kernel)
theorem b677 : Ban 29 7 v659 := viaPerm map31_1 map31_1 b553 (by decide +kernel) (by decide +kernel)
theorem b678 : Ban 29 7 v660 := viaPerm map31_1 map31_1 b604 (by decide +kernel) (by decide +kernel)
theorem b679 : Ban 29 7 v661 := smallByCut p31_15 w20
theorem b680 : Ban 29 7 v662 := smallByCut p31_15 w4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b681 : Ban 29 8 v27 := viaBranch (ws := [v28,v29,v30,v31,v32,v34,v36,v37,v38,v40,v161,v162,v163,v164,v166,v167,v168,v170,v172,v174,v175,v176,v177,v178,v179,v180,v181,v182,v183,v184,v185,v169,v186,v187,v188,v189,v190,v191,v192,v194,v236,v238,v241,v243,v245,v247,v336,v337,v288,v324,v455,v456,v457,v458,v459,v460,v461,v462,v463,v465,v467,v503,v589,v590,v654,v635,v655,v656,v657,v658,v659,v660,v661,v662]) (consBan b26 (consBan b27 (consBan b28 (consBan b30 (consBan b32 (consBan b34 (consBan b35 (consBan b36 (consBan b38 (consBan b159 (consBan b160 (consBan b161 (consBan b162 (consBan b164 (consBan b165 (consBan b166 (consBan b168 (consBan b170 (consBan b172 (consBan b173 (consBan b174 (consBan b175 (consBan b176 (consBan b177 (consBan b178 (consBan b179 (consBan b180 (consBan b181 (consBan b182 (consBan b183 (consBan b184 (consBan b167 (consBan b185 (consBan b186 (consBan b187 (consBan b188 (consBan b189 (consBan b190 (consBan b192 (consBan b235 (consBan b237 (consBan b240 (consBan b242 (consBan b244 (consBan b302 (consBan b341 (consBan b343 (consBan b345 (consBan b420 (consBan b461 (consBan b462 (consBan b463 (consBan b464 (consBan b465 (consBan b466 (consBan b467 (consBan b468 (consBan b469 (consBan b471 (consBan b473 (consBan b553 (consBan b604 (consBan b605 (consBan b670 (consBan b672 (consBan b671 (consBan b673 (consBan b674 (consBan b675 (consBan b676 (consBan b677 (consBan b678 (consBan b679 (consBan b680 (nilBan 29 7))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b683 : Ban 29 8 v187 := smallByCut p31_30 w6
theorem b684 : Ban 29 8 v172 := smallByCut p31_29 w6
theorem b685 : Ban 29 8 v663 := smallByCut p31_27 w6
theorem b686 : Ban 29 8 v664 := viaPerm map31_2 map31_2 b681 (by decide +kernel) (by decide +kernel)
theorem b682 : Ban 29 8 v173 := smallByCut p31_30 w6
theorem b687 : Ban 29 8 v665 := smallByCut p31_27 w6
theorem b824 : Ban 12 5 v800 := checkedSmall
theorem b825 : Ban 12 5 v801 := checkedSmall
theorem b826 : Ban 12 5 v802 := checkedSmall
theorem b827 : Ban 12 5 v803 := checkedSmall
theorem b828 : Ban 12 5 v804 := checkedSmall
theorem b829 : Ban 12 5 v805 := checkedSmall
theorem b830 : Ban 12 5 v806 := checkedSmall
theorem b831 : Ban 12 5 v807 := checkedSmall
theorem b832 : Ban 12 5 v808 := checkedSmall
theorem b833 : Ban 12 5 v809 := checkedSmall
theorem b834 : Ban 12 5 v810 := checkedSmall
theorem b835 : Ban 12 5 v811 := checkedSmall
theorem b836 : Ban 12 5 v812 := checkedSmall
theorem b837 : Ban 12 5 v813 := checkedSmall
theorem b838 : Ban 12 5 v814 := checkedSmall
theorem b839 : Ban 12 5 v815 := checkedSmall
theorem b840 : Ban 12 5 v816 := checkedSmall
theorem b841 : Ban 12 5 v817 := checkedSmall
theorem b842 : Ban 12 5 v818 := checkedSmall
theorem b843 : Ban 12 5 v819 := checkedSmall
theorem b844 : Ban 12 5 v820 := checkedSmall
theorem b845 : Ban 12 5 v821 := checkedSmall
theorem b846 : Ban 12 5 v822 := checkedSmall
theorem b847 : Ban 12 5 v823 := checkedSmall
theorem b848 : Ban 12 5 v824 := checkedSmall
theorem b849 : Ban 12 5 v825 := checkedSmall
theorem b850 : Ban 12 5 v826 := checkedSmall
theorem b851 : Ban 12 5 v827 := checkedSmall
theorem b852 : Ban 12 5 v828 := checkedSmall
theorem b853 : Ban 12 5 v829 := checkedSmall
theorem b854 : Ban 12 5 v830 := checkedSmall
theorem b855 : Ban 12 5 v831 := checkedSmall
theorem b856 : Ban 12 5 v832 := checkedSmall
theorem b857 : Ban 12 5 v833 := checkedSmall
theorem b858 : Ban 12 5 v834 := checkedSmall
theorem b859 : Ban 12 5 v835 := checkedSmall
theorem b860 : Ban 12 5 v836 := checkedSmall
theorem b861 : Ban 12 5 v837 := checkedSmall
theorem b862 : Ban 12 5 v838 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b863 : Ban 12 6 v351 := viaBranch (ws := [v800,v801,v802,v803,v804,v805,v806,v807,v808,v809,v810,v811,v812,v813,v814,v815,v353,v816,v817,v818,v819,v820,v821,v822,v823,v824,v825,v358,v407,v826,v360,v827,v828,v829,v830,v831,v832,v833,v834,v362,v835,v836,v364,v837,v838,v352]) (consBan b824 (consBan b825 (consBan b826 (consBan b827 (consBan b828 (consBan b829 (consBan b830 (consBan b831 (consBan b832 (consBan b833 (consBan b834 (consBan b835 (consBan b836 (consBan b837 (consBan b838 (consBan b839 (consBan b356 (consBan b840 (consBan b841 (consBan b842 (consBan b843 (consBan b844 (consBan b845 (consBan b846 (consBan b847 (consBan b848 (consBan b849 (consBan b361 (consBan b410 (consBan b850 (consBan b363 (consBan b851 (consBan b852 (consBan b853 (consBan b854 (consBan b855 (consBan b856 (consBan b857 (consBan b858 (consBan b365 (consBan b859 (consBan b860 (consBan b367 (consBan b861 (consBan b862 (consBan b355 (nilBan 12 5))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w18 : Wide 12 6 v351 := viaSub (ws := [v239,v351]) (consBan b369 (consBan b863 (nilBan 12 6))) (by decide) (by decide +kernel)
theorem b688 : Ban 29 8 v474 := smallByCut p31_23 w18
theorem b689 : Ban 29 7 v667 := smallByCut p31_30 w15
theorem b691 : Ban 29 7 v668 := smallByCut p31_30 w15
theorem b693 : Ban 29 7 v670 := smallByCut p31_29 w13
theorem b694 : Ban 29 7 v672 := smallByCut p31_30 w15
theorem b695 : Ban 29 7 v673 := smallByCut p31_30 w6
theorem b690 : Ban 29 7 v669 := smallByCut p31_30 w15
theorem b696 : Ban 29 7 v674 := smallByCut p31_27 w13
theorem b697 : Ban 29 7 v675 := smallByCut p31_23 w18
theorem b698 : Ban 29 7 v676 := smallByCut p31_23 w18
theorem b699 : Ban 29 7 v677 := smallByCut p31_23 w20
theorem b700 : Ban 29 7 v678 := smallByCut p31_23 w20
theorem b702 : Ban 29 7 v679 := smallByCut p31_30 w15
theorem b704 : Ban 29 7 v681 := smallByCut p31_23 w18
theorem b706 : Ban 29 7 v683 := smallByCut p31_23 w20
theorem b708 : Ban 29 7 v685 := smallByCut p31_23 w20
theorem b710 : Ban 29 7 v687 := smallByCut p31_23 w20
theorem b712 : Ban 29 7 v689 := smallByCut p31_15 w18
theorem b761 : Ban 29 7 v691 := smallByCut p31_15 w18
theorem b762 : Ban 29 7 v740 := smallByCut p31_15 w18
theorem b764 : Ban 29 7 v741 := smallByCut p31_15 w18
theorem b766 : Ban 29 7 v743 := smallByCut p31_15 w18
theorem b768 : Ban 29 7 v745 := smallByCut p31_15 w18
theorem b770 : Ban 29 7 v747 := smallByCut p31_27 w13
theorem b772 : Ban 29 7 v749 := smallByCut p31_29 w13
theorem b773 : Ban 29 7 v751 := smallByCut p31_27 w13
theorem b775 : Ban 29 7 v752 := smallByCut p31_23 w20
theorem b776 : Ban 29 7 v754 := smallByCut p31_23 w18
theorem b777 : Ban 29 7 v755 := smallByCut p31_23 w18
theorem b779 : Ban 29 7 v756 := smallByCut p31_23 w20
theorem b781 : Ban 29 7 v758 := smallByCut p31_29 w15
theorem b783 : Ban 29 7 v760 := smallByCut p31_29 w13
theorem b784 : Ban 29 7 v762 := smallByCut p31_29 w3
theorem b786 : Ban 29 7 v472 := smallByCut p31_29 w15
theorem b788 : Ban 29 7 v764 := smallByCut p31_29 w13
theorem b790 : Ban 29 7 v766 := smallByCut p31_27 w6
theorem b792 : Ban 29 7 v768 := smallByCut p31_29 w3
theorem b794 : Ban 29 7 v770 := smallByCut p31_15 w18
theorem b795 : Ban 29 7 v772 := smallByCut p31_15 w18
theorem b797 : Ban 29 7 v773 := smallByCut p31_15 w18
theorem b799 : Ban 29 7 v775 := smallByCut p31_15 w18
theorem b800 : Ban 29 7 v777 := smallByCut p31_23 w20
theorem b801 : Ban 29 7 v778 := smallByCut p31_23 w18
theorem b802 : Ban 29 7 v779 := smallByCut p31_23 w18
theorem b778 : Ban 29 7 v757 := smallByCut p31_23 w20
theorem b803 : Ban 29 7 v780 := smallByCut p31_27 w15
theorem b804 : Ban 29 7 v781 := smallByCut p31_27 w13
theorem b805 : Ban 29 7 v782 := smallByCut p31_27 w3
theorem b806 : Ban 29 7 v783 := smallByCut p31_27 w3
theorem b807 : Ban 29 7 v784 := smallByCut p31_27 w15
theorem b808 : Ban 29 7 v785 := smallByCut p31_27 w13
theorem b789 : Ban 29 7 v767 := smallByCut p31_29 w6
theorem b791 : Ban 29 7 v769 := smallByCut p31_27 w3
theorem b809 : Ban 29 7 v786 := smallByCut p31_15 w18
theorem b810 : Ban 29 7 v787 := smallByCut p31_15 w18
theorem b811 : Ban 29 7 v788 := smallByCut p31_15 w18
theorem b812 : Ban 29 7 v789 := smallByCut p31_15 w18
theorem b814 : Ban 29 7 v468 := smallByCut p31_23 w18
theorem b815 : Ban 29 7 v790 := smallByCut p31_23 w20
theorem b816 : Ban 29 7 v791 := smallByCut p31_15 w18
theorem b818 : Ban 29 7 v792 := smallByCut p31_23 w20
theorem b819 : Ban 29 7 v794 := smallByCut p31_15 w18
theorem b821 : Ban 29 7 v795 := smallByCut p31_15 w20
theorem b823 : Ban 29 7 v797 := smallByCut p31_15 w18
theorem b864 : Ban 29 7 v799 := smallByCut p31_15 w18
theorem b865 : Ban 29 7 v839 := smallByCut p31_15 w18
theorem b867 : Ban 29 7 v840 := smallByCut p31_15 w18
theorem b869 : Ban 29 7 v842 := smallByCut p31_15 w18
theorem b871 : Ban 29 7 v844 := smallByCut p31_15 w20
theorem b873 : Ban 29 7 v846 := smallByCut p31_15 w18
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b874 : Ban 29 8 v666 := viaBranch (ws := [v667,v167,v668,v670,v672,v673,v669,v674,v675,v676,v677,v678,v679,v681,v683,v685,v687,v689,v691,v740,v741,v743,v745,v747,v195,v749,v751,v752,v754,v755,v756,v758,v760,v461,v762,v472,v764,v766,v768,v770,v772,v773,v775,v777,v778,v779,v757,v780,v781,v782,v783,v784,v785,v767,v769,v786,v787,v788,v789,v468,v790,v791,v792,v794,v795,v797,v799,v839,v840,v842,v844,v846]) (consBan b689 (consBan b166 (consBan b691 (consBan b693 (consBan b694 (consBan b695 (consBan b690 (consBan b696 (consBan b697 (consBan b698 (consBan b699 (consBan b700 (consBan b702 (consBan b704 (consBan b706 (consBan b708 (consBan b710 (consBan b712 (consBan b761 (consBan b762 (consBan b764 (consBan b766 (consBan b768 (consBan b770 (consBan b234 (consBan b772 (consBan b773 (consBan b775 (consBan b776 (consBan b777 (consBan b779 (consBan b781 (consBan b783 (consBan b468 (consBan b784 (consBan b786 (consBan b788 (consBan b790 (consBan b792 (consBan b794 (consBan b795 (consBan b797 (consBan b799 (consBan b800 (consBan b801 (consBan b802 (consBan b778 (consBan b803 (consBan b804 (consBan b805 (consBan b806 (consBan b807 (consBan b808 (consBan b789 (consBan b791 (consBan b809 (consBan b810 (consBan b811 (consBan b812 (consBan b814 (consBan b815 (consBan b816 (consBan b818 (consBan b819 (consBan b821 (consBan b823 (consBan b864 (consBan b865 (consBan b867 (consBan b869 (consBan b871 (consBan b873 (nilBan 29 7))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b876 : Ban 29 8 v468 := smallByCut p31_30 w6
theorem b878 : Ban 29 8 v687 := smallByCut p31_23 w18
theorem b879 : Ban 29 8 v848 := smallByCut p31_15 w18
theorem b880 : Ban 29 8 v849 := viaPerm map31_1 map31_1 b874 (by decide +kernel) (by decide +kernel)
theorem b881 : Ban 29 8 v850 := smallByCut p31_30 w6
theorem b882 : Ban 29 8 v851 := smallByCut p31_15 w18
theorem b883 : Ban 29 8 v852 := smallByCut p31_27 w6
theorem b884 : Ban 29 8 v853 := viaPerm map31_6 map31_8 b681 (by decide +kernel) (by decide +kernel)
theorem b885 : Ban 29 8 v854 := smallByCut p31_29 w6
theorem b886 : Ban 29 8 v855 := smallByCut p31_27 w6
theorem b887 : Ban 29 8 v482 := smallByCut p31_23 w18
theorem b888 : Ban 29 8 v856 := viaPerm map31_4 map31_4 b874 (by decide +kernel) (by decide +kernel)
theorem b875 : Ban 29 8 v476 := smallByCut p31_29 w6
theorem b889 : Ban 29 8 v857 := smallByCut p31_23 w18
theorem b890 : Ban 29 8 v858 := smallByCut p31_15 w18
theorem b891 : Ban 29 8 v859 := viaPerm map31_5 map31_5 b874 (by decide +kernel) (by decide +kernel)
theorem b892 : Ban 29 8 v860 := smallByCut p31_29 w6
theorem b893 : Ban 29 8 v861 := smallByCut p31_15 w18
theorem b894 : Ban 29 8 v862 := smallByCut p31_23 w18
theorem b895 : Ban 29 8 v863 := viaPerm map31_8 map31_6 b874 (by decide +kernel) (by decide +kernel)
theorem b896 : Ban 29 8 v864 := smallByCut p31_27 w6
theorem b877 : Ban 29 8 v688 := smallByCut p31_23 w18
theorem b897 : Ban 29 8 v865 := smallByCut p31_15 w18
theorem b898 : Ban 29 8 v866 := viaPerm map31_9 map31_7 b874 (by decide +kernel) (by decide +kernel)
theorem b899 : Ban 29 8 v867 := smallByCut p31_27 w6
theorem b900 : Ban 29 8 v868 := smallByCut p31_15 w18
theorem b901 : Ban 29 8 v869 := smallByCut p31_15 w18
theorem b902 : Ban 29 7 v871 := smallByCut p31_29 w9
theorem b904 : Ban 29 7 v609 := smallByCut p31_30 w9
theorem b905 : Ban 29 7 v598 := smallByCut p31_29 w9
theorem b906 : Ban 29 7 v873 := smallByCut p31_27 w9
theorem b907 : Ban 29 7 v874 := viaPerm map31_2 map31_2 b670 (by decide +kernel) (by decide +kernel)
theorem b903 : Ban 29 7 v872 := smallByCut p31_30 w9
theorem b908 : Ban 29 7 v875 := smallByCut p31_27 w9
theorem b909 : Ban 29 7 v876 := smallByCut p31_23 w20
theorem b911 : Ban 29 7 v877 := smallByCut p31_23 w18
theorem b913 : Ban 29 7 v879 := smallByCut p31_23 w20
theorem b914 : Ban 29 7 v881 := smallByCut p31_15 w20
theorem b915 : Ban 29 7 v882 := smallByCut p31_15 w18
theorem b916 : Ban 29 7 v883 := smallByCut p31_15 w18
theorem b917 : Ban 29 7 v884 := smallByCut p31_15 w20
theorem b918 : Ban 29 7 v885 := smallByCut p31_30 w15
theorem b919 : Ban 29 7 v886 := smallByCut p31_30 w9
theorem b920 : Ban 29 7 v887 := smallByCut p31_15 w18
theorem b921 : Ban 29 7 v888 := smallByCut p31_30 w15
theorem b922 : Ban 29 7 v889 := smallByCut p31_30 w9
theorem b923 : Ban 29 6 v892 := smallByCut p31_30 w15
theorem b924 : Ban 29 6 v893 := checkedSmall
theorem b925 : Ban 29 6 v894 := smallByCut p31_29 w15
theorem b926 : Ban 29 6 v895 := checkedSmall
theorem b927 : Ban 29 6 v896 := smallByCut p31_29 w15
theorem b928 : Ban 29 6 v897 := checkedSmall
theorem b929 : Ban 29 6 v898 := smallByCut p31_30 w15
theorem b930 : Ban 29 6 v899 := checkedSmall
theorem b931 : Ban 29 6 v900 := smallByCut p31_29 w15
theorem b932 : Ban 29 6 v901 := checkedSmall
theorem b933 : Ban 29 6 v902 := smallByCut p31_30 w15
theorem b934 : Ban 29 6 v903 := checkedSmall
theorem b935 : Ban 29 6 v904 := smallByCut p31_30 w15
theorem b936 : Ban 29 6 v905 := checkedSmall
theorem b937 : Ban 29 6 v906 := smallByCut p31_29 w15
theorem b938 : Ban 29 6 v907 := checkedSmall
theorem b939 : Ban 29 6 v908 := checkedSmall
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem w19 : Wide 12 5 v363 := viaSub (ws := [v239,v363]) (consBan b238 (consBan b366 (nilBan 12 5))) (by decide) (by decide +kernel)
theorem b940 : Ban 29 6 v909 := smallByCut p31_15 w19
theorem b941 : Ban 29 6 v910 := smallByCut p31_27 w9
theorem b942 : Ban 29 6 v688 := smallByCut p31_15 w20
theorem b943 : Ban 29 6 v911 := smallByCut p31_15 w20
theorem b944 : Ban 29 6 v912 := smallByCut p31_15 w20
theorem b945 : Ban 29 6 v913 := smallByCut p31_15 w20
theorem b946 : Ban 29 6 v845 := smallByCut p31_15 w20
theorem b947 : Ban 29 6 v914 := smallByCut p31_15 w20
theorem b948 : Ban 29 6 v862 := smallByCut p31_23 w20
theorem b949 : Ban 29 6 v915 := smallByCut p31_23 w20
theorem b950 : Ban 29 6 v868 := smallByCut p31_15 w20
theorem b951 : Ban 29 6 v916 := smallByCut p31_15 w20
theorem b952 : Ban 29 6 v917 := smallByCut p31_15 w20
theorem b953 : Ban 29 6 v918 := smallByCut p31_15 w20
theorem b954 : Ban 29 6 v919 := smallByCut p31_15 w20
theorem b955 : Ban 29 6 v920 := smallByCut p31_15 w20
theorem b956 : Ban 29 6 v865 := smallByCut p31_15 w20
theorem b957 : Ban 29 6 v921 := smallByCut p31_15 w20
theorem b958 : Ban 29 6 v922 := checkedSmall
theorem b959 : Ban 29 6 v923 := checkedSmall
theorem b960 : Ban 29 6 v924 := checkedSmall
theorem b961 : Ban 29 6 v925 := smallByCut p31_27 w9
theorem b962 : Ban 29 6 v926 := checkedSmall
theorem b963 : Ban 29 6 v927 := smallByCut p31_27 w9
theorem b964 : Ban 29 6 v928 := smallByCut p31_27 w9
theorem b965 : Ban 29 6 v929 := smallByCut p31_27 w9
theorem b966 : Ban 29 6 v930 := smallByCut p31_27 w9
theorem b967 : Ban 29 6 v931 := smallByCut p31_23 w20
theorem b968 : Ban 29 6 v932 := smallByCut p31_23 w20
theorem b969 : Ban 29 6 v933 := smallByCut p31_23 w20
theorem b970 : Ban 29 6 v934 := smallByCut p31_23 w20
theorem b971 : Ban 29 6 v935 := smallByCut p31_15 w20
theorem b972 : Ban 29 6 v936 := smallByCut p31_15 w20
theorem b973 : Ban 29 6 v937 := smallByCut p31_15 w20
theorem b974 : Ban 29 6 v938 := smallByCut p31_15 w20
theorem b975 : Ban 29 6 v939 := smallByCut p31_27 w9
theorem b976 : Ban 29 6 v940 := checkedSmall
theorem b977 : Ban 29 6 v941 := smallByCut p31_27 w9
theorem b978 : Ban 29 6 v942 := smallByCut p31_27 w9
theorem b979 : Ban 29 6 v943 := smallByCut p31_27 w9
theorem b980 : Ban 29 6 v944 := smallByCut p31_27 w9
theorem b981 : Ban 29 6 v945 := smallByCut p31_23 w20
theorem b982 : Ban 29 6 v946 := smallByCut p31_23 w20
theorem b983 : Ban 29 6 v947 := smallByCut p31_23 w20
theorem b984 : Ban 29 6 v948 := smallByCut p31_23 w20
theorem b985 : Ban 29 6 v949 := smallByCut p31_15 w20
theorem b986 : Ban 29 6 v950 := smallByCut p31_15 w20
theorem b987 : Ban 29 6 v951 := smallByCut p31_15 w20
theorem b988 : Ban 29 6 v952 := smallByCut p31_15 w20
theorem b989 : Ban 29 6 v953 := smallByCut p31_23 w20
theorem b990 : Ban 29 6 v954 := smallByCut p31_23 w20
theorem b991 : Ban 29 6 v955 := smallByCut p31_23 w20
theorem b992 : Ban 29 6 v956 := smallByCut p31_23 w20
theorem b993 : Ban 29 6 v957 := smallByCut p31_15 w20
theorem b994 : Ban 29 6 v958 := smallByCut p31_15 w20
theorem b995 : Ban 29 6 v959 := smallByCut p31_15 w20
theorem b996 : Ban 29 6 v960 := smallByCut p31_15 w20
theorem b997 : Ban 29 6 v961 := smallByCut p31_15 w20
theorem b998 : Ban 29 6 v962 := smallByCut p31_15 w20
theorem b999 : Ban 29 6 v963 := smallByCut p31_15 w20
theorem b1000 : Ban 29 6 v964 := smallByCut p31_15 w20
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1001 : Ban 29 7 v891 := viaBranch (ws := [v892,v893,v894,v895,v896,v897,v898,v899,v900,v901,v902,v903,v904,v905,v906,v907,v908,v909,v910,v688,v911,v912,v913,v845,v914,v862,v915,v868,v916,v917,v918,v919,v920,v865,v921,v922,v624,v923,v924,v925,v926,v927,v928,v929,v930,v931,v932,v933,v934,v935,v936,v937,v938,v939,v940,v941,v942,v943,v944,v945,v946,v947,v948,v949,v950,v951,v952,v953,v954,v955,v956,v957,v958,v959,v960,v961,v962,v963,v964]) (consBan b923 (consBan b924 (consBan b925 (consBan b926 (consBan b927 (consBan b928 (consBan b929 (consBan b930 (consBan b931 (consBan b932 (consBan b933 (consBan b934 (consBan b935 (consBan b936 (consBan b937 (consBan b938 (consBan b939 (consBan b940 (consBan b941 (consBan b942 (consBan b943 (consBan b944 (consBan b945 (consBan b946 (consBan b947 (consBan b948 (consBan b949 (consBan b950 (consBan b951 (consBan b952 (consBan b953 (consBan b954 (consBan b955 (consBan b956 (consBan b957 (consBan b958 (consBan b639 (consBan b959 (consBan b960 (consBan b961 (consBan b962 (consBan b963 (consBan b964 (consBan b965 (consBan b966 (consBan b967 (consBan b968 (consBan b969 (consBan b970 (consBan b971 (consBan b972 (consBan b973 (consBan b974 (consBan b975 (consBan b976 (consBan b977 (consBan b978 (consBan b979 (consBan b980 (consBan b981 (consBan b982 (consBan b983 (consBan b984 (consBan b985 (consBan b986 (consBan b987 (consBan b988 (consBan b989 (consBan b990 (consBan b991 (consBan b992 (consBan b993 (consBan b994 (consBan b995 (consBan b996 (consBan b997 (consBan b998 (consBan b999 (consBan b1000 (nilBan 29 6)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1002 : Ban 29 7 v890 := viaPerm map31_6 map31_8 b1001 (by decide +kernel) (by decide +kernel)
theorem b1003 : Ban 29 6 v966 := smallByCut p31_30 w9
theorem b1004 : Ban 29 6 v967 := smallByCut p31_29 w9
theorem b1005 : Ban 29 6 v968 := smallByCut p31_29 w9
theorem b1006 : Ban 29 6 v969 := smallByCut p31_30 w9
theorem b1007 : Ban 29 6 v970 := smallByCut p31_29 w9
theorem b1008 : Ban 29 6 v971 := smallByCut p31_30 w9
theorem b1009 : Ban 29 6 v972 := smallByCut p31_30 w9
theorem b1010 : Ban 29 6 v973 := smallByCut p31_29 w9
theorem b1011 : Ban 29 6 v974 := checkedSmall
theorem b1012 : Ban 29 6 v975 := smallByCut p31_15 w19
theorem b1013 : Ban 29 6 v880 := smallByCut p31_15 w20
theorem b1014 : Ban 29 6 v976 := smallByCut p31_15 w20
theorem b1015 : Ban 29 6 v977 := smallByCut p31_15 w20
theorem b1016 : Ban 29 6 v978 := smallByCut p31_23 w20
theorem b1017 : Ban 29 6 v979 := smallByCut p31_15 w20
theorem b1018 : Ban 29 6 v980 := smallByCut p31_15 w20
theorem b1019 : Ban 29 6 v981 := smallByCut p31_15 w20
theorem b1020 : Ban 29 6 v982 := smallByCut p31_15 w20
theorem b1021 : Ban 29 6 v983 := smallByCut p31_27 w15
theorem b1022 : Ban 29 6 v984 := smallByCut p31_27 w9
theorem b1023 : Ban 29 6 v985 := smallByCut p31_27 w9
theorem b1024 : Ban 29 6 v986 := checkedSmall
theorem b1025 : Ban 29 6 v987 := smallByCut p31_27 w9
theorem b1026 : Ban 29 6 v988 := checkedSmall
theorem b1027 : Ban 29 6 v989 := checkedSmall
theorem b1028 : Ban 29 6 v990 := checkedSmall
theorem b1029 : Ban 29 6 v991 := checkedSmall
theorem b1030 : Ban 29 6 v992 := checkedSmall
theorem b1031 : Ban 29 6 v993 := smallByCut p31_27 w9
theorem b1032 : Ban 29 6 v994 := checkedSmall
theorem b1033 : Ban 29 6 v995 := checkedSmall
theorem b1034 : Ban 29 6 v996 := checkedSmall
theorem b1035 : Ban 29 6 v997 := checkedSmall
theorem b1036 : Ban 29 6 v998 := smallByCut p31_23 w20
theorem b1037 : Ban 29 6 v999 := smallByCut p31_23 w20
theorem b1038 : Ban 29 6 v1000 := smallByCut p31_15 w20
theorem b1039 : Ban 29 6 v1001 := smallByCut p31_15 w20
theorem b1040 : Ban 29 6 v1002 := smallByCut p31_27 w9
theorem b1041 : Ban 29 6 v1003 := smallByCut p31_27 w9
theorem b1042 : Ban 29 6 v1004 := smallByCut p31_27 w9
theorem b1043 : Ban 29 6 v1005 := smallByCut p31_15 w20
theorem b1044 : Ban 29 6 v1006 := smallByCut p31_15 w20
theorem b1045 : Ban 29 6 v1007 := smallByCut p31_15 w20
theorem b1046 : Ban 29 6 v1008 := smallByCut p31_23 w20
theorem b1047 : Ban 29 6 v1009 := smallByCut p31_15 w20
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1048 : Ban 29 7 v962 := viaBranch (ws := [v966,v967,v968,v969,v970,v971,v972,v973,v974,v975,v880,v976,v977,v978,v979,v980,v981,v982,v983,v984,v985,v986,v987,v988,v989,v990,v991,v992,v993,v994,v995,v996,v997,v998,v999,v1000,v1001,v908,v910,v1002,v1003,v1004,v1005,v1006,v1007,v1008,v1009,v964,v963]) (consBan b1003 (consBan b1004 (consBan b1005 (consBan b1006 (consBan b1007 (consBan b1008 (consBan b1009 (consBan b1010 (consBan b1011 (consBan b1012 (consBan b1013 (consBan b1014 (consBan b1015 (consBan b1016 (consBan b1017 (consBan b1018 (consBan b1019 (consBan b1020 (consBan b1021 (consBan b1022 (consBan b1023 (consBan b1024 (consBan b1025 (consBan b1026 (consBan b1027 (consBan b1028 (consBan b1029 (consBan b1030 (consBan b1031 (consBan b1032 (consBan b1033 (consBan b1034 (consBan b1035 (consBan b1036 (consBan b1037 (consBan b1038 (consBan b1039 (consBan b939 (consBan b941 (consBan b1040 (consBan b1041 (consBan b1042 (consBan b1043 (consBan b1044 (consBan b1045 (consBan b1046 (consBan b1047 (consBan b1000 (consBan b999 (nilBan 29 6)))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1049 : Ban 29 7 v965 := viaPerm map31_6 map31_8 b1048 (by decide +kernel) (by decide +kernel)
theorem b1050 : Ban 29 7 v1010 := smallByCut p31_27 w9
theorem b1051 : Ban 29 7 v1011 := viaPerm map31_6 map31_8 b670 (by decide +kernel) (by decide +kernel)
theorem b1052 : Ban 29 7 v1012 := smallByCut p31_29 w9
theorem b1053 : Ban 29 7 v1013 := smallByCut p31_27 w9
theorem b1054 : Ban 29 7 v1014 := smallByCut p31_23 w20
theorem b1055 : Ban 29 7 v1015 := smallByCut p31_23 w18
theorem b910 : Ban 29 7 v878 := smallByCut p31_23 w18
theorem b1056 : Ban 29 7 v1016 := smallByCut p31_23 w20
theorem b1057 : Ban 29 7 v1017 := smallByCut p31_15 w20
theorem b1058 : Ban 29 7 v1018 := smallByCut p31_15 w18
theorem b1059 : Ban 29 7 v1019 := smallByCut p31_15 w18
theorem b1060 : Ban 29 7 v1020 := smallByCut p31_15 w20
theorem b1061 : Ban 29 7 v1021 := smallByCut p31_29 w15
theorem b1062 : Ban 29 7 v1022 := smallByCut p31_29 w9
theorem b1063 : Ban 29 7 v1023 := viaPerm map31_4 map31_4 b864 (by decide +kernel) (by decide +kernel)
theorem b1064 : Ban 29 7 v1024 := viaPerm map31_4 map31_4 b920 (by decide +kernel) (by decide +kernel)
theorem b1065 : Ban 29 7 v1025 := smallByCut p31_29 w15
theorem b1066 : Ban 29 7 v1026 := smallByCut p31_29 w9
theorem b1067 : Ban 29 7 v1027 := viaPerm map31_2 map31_2 b1001 (by decide +kernel) (by decide +kernel)
theorem b1068 : Ban 29 7 v1028 := viaPerm map31_2 map31_2 b1048 (by decide +kernel) (by decide +kernel)
theorem b1069 : Ban 29 7 v978 := smallByCut p31_23 w20
theorem b1070 : Ban 29 7 v1029 := smallByCut p31_23 w18
theorem b1071 : Ban 29 7 v1030 := smallByCut p31_23 w18
theorem b912 : Ban 29 7 v880 := smallByCut p31_23 w20
theorem b1072 : Ban 29 7 v982 := smallByCut p31_15 w20
theorem b1073 : Ban 29 7 v1031 := smallByCut p31_15 w18
theorem b1074 : Ban 29 7 v1032 := smallByCut p31_15 w18
theorem b1075 : Ban 29 7 v979 := smallByCut p31_15 w20
theorem b1076 : Ban 29 7 v983 := smallByCut p31_27 w15
theorem b1077 : Ban 29 7 v985 := smallByCut p31_27 w9
theorem b1078 : Ban 29 7 v909 := viaPerm map31_8 map31_6 b864 (by decide +kernel) (by decide +kernel)
theorem b1079 : Ban 29 7 v975 := viaPerm map31_8 map31_6 b920 (by decide +kernel) (by decide +kernel)
theorem b1080 : Ban 29 7 v1033 := smallByCut p31_27 w15
theorem b1081 : Ban 29 7 v1034 := smallByCut p31_27 w9
theorem b1082 : Ban 29 7 v1035 := smallByCut p31_15 w18
theorem b1083 : Ban 29 7 v1036 := smallByCut p31_23 w20
theorem b1084 : Ban 29 7 v1037 := smallByCut p31_15 w20
theorem b1085 : Ban 29 7 v1038 := smallByCut p31_15 w20
theorem b1087 : Ban 29 7 v1039 := smallByCut p31_23 w20
theorem b1089 : Ban 29 7 v1041 := smallByCut p31_23 w20
theorem b1086 : Ban 29 7 v1040 := smallByCut p31_15 w20
theorem b1088 : Ban 29 7 v1042 := smallByCut p31_15 w20
theorem b1090 : Ban 29 7 v1043 := smallByCut p31_15 w20
theorem b1091 : Ban 29 7 v1044 := smallByCut p31_23 w20
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1092 : Ban 29 8 v870 := viaBranch (ws := [v871,v590,v609,v598,v873,v874,v872,v875,v876,v791,v877,v879,v881,v882,v883,v884,v885,v886,v799,v887,v888,v889,v890,v965,v1010,v1011,v1012,v1013,v1014,v1015,v878,v1016,v1017,v1018,v1019,v1020,v1021,v1022,v1023,v1024,v1025,v1026,v1027,v1028,v978,v1029,v1030,v880,v982,v1031,v1032,v979,v983,v985,v909,v975,v1033,v1034,v891,v962,v1035,v1036,v1037,v1038,v1039,v1041,v1040,v1042,v1043,v1044]) (consBan b902 (consBan b670 (consBan b904 (consBan b905 (consBan b906 (consBan b907 (consBan b903 (consBan b908 (consBan b909 (consBan b816 (consBan b911 (consBan b913 (consBan b914 (consBan b915 (consBan b916 (consBan b917 (consBan b918 (consBan b919 (consBan b864 (consBan b920 (consBan b921 (consBan b922 (consBan b1002 (consBan b1049 (consBan b1050 (consBan b1051 (consBan b1052 (consBan b1053 (consBan b1054 (consBan b1055 (consBan b910 (consBan b1056 (consBan b1057 (consBan b1058 (consBan b1059 (consBan b1060 (consBan b1061 (consBan b1062 (consBan b1063 (consBan b1064 (consBan b1065 (consBan b1066 (consBan b1067 (consBan b1068 (consBan b1069 (consBan b1070 (consBan b1071 (consBan b912 (consBan b1072 (consBan b1073 (consBan b1074 (consBan b1075 (consBan b1076 (consBan b1077 (consBan b1078 (consBan b1079 (consBan b1080 (consBan b1081 (consBan b1001 (consBan b1048 (consBan b1082 (consBan b1083 (consBan b1084 (consBan b1085 (consBan b1087 (consBan b1089 (consBan b1086 (consBan b1088 (consBan b1090 (consBan b1091 (nilBan 29 7))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1094 : Ban 29 8 v1044 := smallByCut p31_23 w18
theorem b1093 : Ban 29 8 v1043 := smallByCut p31_15 w18
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem b1095 : Ban 29 9 v0 := viaBranch (ws := [v1,v27,v187,v172,v663,v664,v173,v665,v474,v666,v468,v687,v848,v849,v850,v851,v852,v853,v854,v855,v482,v856,v476,v857,v858,v859,v860,v861,v862,v863,v864,v688,v865,v866,v867,v868,v869,v870,v1044,v1043]) (consBan b25 (consBan b681 (consBan b683 (consBan b684 (consBan b685 (consBan b686 (consBan b682 (consBan b687 (consBan b688 (consBan b874 (consBan b876 (consBan b878 (consBan b879 (consBan b880 (consBan b881 (consBan b882 (consBan b883 (consBan b884 (consBan b885 (consBan b886 (consBan b887 (consBan b888 (consBan b875 (consBan b889 (consBan b890 (consBan b891 (consBan b892 (consBan b893 (consBan b894 (consBan b895 (consBan b896 (consBan b877 (consBan b897 (consBan b898 (consBan b899 (consBan b900 (consBan b901 (consBan b1092 (consBan b1094 (consBan b1093 (nilBan 29 8))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem verifiedPin : Wide 29 9 v0 := widen (by decide +kernel) b1095
end PEqualNP.Outside.L_meta_12104.Support.Core1

namespace PEqualNP.Outside.L_meta_12104.Reduce
namespace Ground0
open PEqualNP.Outside.L_meta_12104.Support PEqualNP.Outside.L_meta_12104.Support.Core0

def coreGoal := pin6 false goal
def rows : List Nat := [22, 22, 22, 22, 22, 22, 21, 21, 21, 21, 21, 21, 4, 4, 4, 4, 4, 4, 19, 19, 19, 19, 19, 19, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 31, 31, 31, 31, 31, 31, 14, 14, 14, 14, 14, 14, 13, 13, 13, 13, 13, 13, 11, 11, 11, 11, 11, 11, 23, 6, 5, 3, 15, 7, 23, 6, 5, 3, 15, 7, 23, 6, 5, 3, 15, 7, 23, 6, 5, 3, 15, 7, 23, 6, 5, 3, 15, 7, 23, 6, 5, 3, 15, 7, 23, 6, 5, 3, 15, 7, 23, 6, 5, 3, 15, 7, 23, 6, 5, 3, 15, 7, 23, 6, 5, 3, 15, 7]
def orient (w : BitVec 32) := if w.getLsbD 7 then ~~~w else w
private theorem orient_not (w : BitVec 32) : orient (~~~w) = orient w := by
  unfold orient
  simp only [BitVec.getLsbD_not, show 7<32 by decide, decide_true, Bool.true_and]
  cases w.getLsbD 7 <;> simp
private theorem orient_canon (w : BitVec 32) : orient (canon w) = orient w := by
  unfold canon
  split <;> simp [orient_not]
def pack (w : BitVec 32) := actL rows (orient w).toNat

private def mix (s t : Bool) (a b : BitVec 32) : BitVec 32 :=
  if s then (if t then a ||| b else b ^^^ (a &&& b))
  else if t then a ^^^ (a &&& b) else a &&& b

private theorem mix_correct (x y : BitVec 32) :
    orient (x &&& y) = mix (x.getLsbD 7) (y.getLsbD 7) (orient x) (orient y) := by
  cases hx : x.getLsbD 7 <;> cases hy : y.getLsbD 7 <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    cases hp : x.getLsbD i <;> cases hq : y.getLsbD i <;>
    simp only [orient, mix, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_xor,
      BitVec.getLsbD_or, hx, hy, hp, hq, decide_eq_true hi, Bool.false_and, Bool.true_and, ite_false, ite_true, Bool.false_eq_true] <;> rfl

private theorem pack_mix (s t : Bool) (a b : BitVec 32) :
    actL rows (mix s t a b).toNat =
      combine (opIndex s t) (actL rows a.toNat) (actL rows b.toNat) := by
  cases s <;> cases t <;> simp [mix, opIndex, combine, BitVec.toNat_xor, BitVec.toNat_and,
    BitVec.toNat_or, actL_and, actL_or, actL_xor]

private theorem canon_signed (s : Bool) (x : BitVec 32) : orient (signed s x) = orient x := by
  cases s
  · rfl
  · exact orient_not x

private theorem pack_gate (s t : Bool) (a b : BitVec 32) :
    ∃ d < 4, pack (gate s t a b) = combine d (pack a) (pack b) := by
  let x := signed s a
  let y := signed t b
  refine ⟨opIndex (x.getLsbD 7) (y.getLsbD 7), op_lt _ _, ?_⟩
  change actL rows (orient (canon (x &&& y))).toNat = _
  rw [orient_canon, mix_correct, pack_mix]
  simp [x, y, pack, canon_signed]

private theorem word_sep : Good 60 (pack coreGoal) := by
  intro i hi
  have h : ∀ j : Fin 60, (pack coreGoal).testBit j.val ≠ (pack coreGoal).testBit (60+j.val) := by decide +kernel
  exact h ⟨i,hi⟩

theorem possible {k S} (h : Path coreGoal k S) {av : List Nat}
    (carry : ∀ w∈S, pack w ∈ av) : Possible 60 k av := by
  apply h (fun n T => ∀ av : List Nat, (∀ w∈T, pack w ∈ av) → Possible 60 n av) ?_ ?_ av carry
  · intro v yes
    refine ⟨0,{pack coreGoal},le_rfl,?_,?_⟩
    · exact PEqualNP.Outside.L_meta_12104.Support.Live.done word_sep (by decide +kernel)
    · simpa using yes coreGoal (by simp)
  · intro k a b U s t _ _ _ ih v yes
    obtain ⟨d,hd,hop⟩ := pack_gate s t a b
    have future : Possible 60 k (v ++ [combine d (pack a) (pack b)]) := by
      apply ih
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | old
      · simp [hop]
      · exact List.mem_append_left _ (yes w (by simp [old]))
    obtain ⟨n,T,le,live,mem⟩ := pullPaid hd (yes _ (by simp)) (yes _ (by simp)) future
    refine ⟨n,T,?_,live,mem⟩
    cases h : charge v (combine d (pack a) (pack b)) <;> simp [h] at le <;> omega

theorem lower (k : Nat) (T : Finset (BitVec 32)) (raw : T ⊆ fiveRaw.toFinset)
    (path : Path coreGoal k T) : 10 ≤ k := by
  by_contra! short
  have tick : ∀ w∈fiveRaw, pack w ∈ v979 := by
    simp [fiveRaw]
    decide +kernel
  obtain ⟨n,S,le,live,inc⟩ := possible path (fun w hw => tick w (List.mem_toFinset.mp (raw hw)))
  exact cinq ⟨n,S,by omega,live,inc⟩

end Ground0
end PEqualNP.Outside.L_meta_12104.Reduce

namespace PEqualNP.Outside.L_meta_12104.Reduce
namespace Ground1
open PEqualNP.Outside.L_meta_12104.Support PEqualNP.Outside.L_meta_12104.Support.Core1

def coreGoal := pin6 true goal
def rows : List Nat := [1, 1, 1, 2, 2, 2, 4, 4, 4, 11, 11, 11, 13, 13, 13, 14, 14, 14, 15, 19, 19, 19, 21, 21, 21, 22, 22, 22, 23, 0, 9, 17, 0, 10, 18, 0, 12, 20, 9, 10, 27, 9, 12, 29, 10, 12, 30, 31, 17, 18, 27, 17, 20, 29, 18, 20, 30, 31]
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

private theorem word_sep : Good 29 (pack coreGoal) := by
  intro i hi
  have h : ∀ j : Fin 29, (pack coreGoal).testBit j.val ≠ (pack coreGoal).testBit (29+j.val) := by decide +kernel
  exact h ⟨i,hi⟩

theorem possible {k S} (h : Path coreGoal k S) {av : List Nat}
    (carry : ∀ w∈S, pack w ∈ av) : Possible 29 k av := by
  apply h (fun n T => ∀ av : List Nat, (∀ w∈T, pack w ∈ av) → Possible 29 n av) ?_ ?_ av carry
  · intro v yes
    refine ⟨0,{pack coreGoal},le_rfl,?_,?_⟩
    · exact PEqualNP.Outside.L_meta_12104.Support.Live.done word_sep (by decide +kernel)
    · simpa using yes coreGoal (by simp)
  · intro k a b U s t _ _ _ ih v yes
    obtain ⟨d,hd,hop⟩ := pack_gate s t a b
    have future : Possible 29 k (v ++ [combine d (pack a) (pack b)]) := by
      apply ih
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | old
      · simp [hop]
      · exact List.mem_append_left _ (yes w (by simp [old]))
    obtain ⟨n,T,le,live,mem⟩ := pullPaid hd (yes _ (by simp)) (yes _ (by simp)) future
    refine ⟨n,T,?_,live,mem⟩
    cases h : charge v (combine d (pack a) (pack b)) <;> simp [h] at le <;> omega

theorem lower (k : Nat) (T : Finset (BitVec 32)) (raw : T ⊆ fiveRaw.toFinset)
    (path : Path coreGoal k T) : 10 ≤ k := by
  by_contra! short
  have tick : ∀ w∈fiveRaw, pack w ∈ v0 := by
    simp [fiveRaw]
    decide +kernel
  obtain ⟨n,S,le,live,inc⟩ := possible path (fun w hw => tick w (List.mem_toFinset.mp (raw hw)))
  exact verifiedPin ⟨n,S,by omega,live,inc⟩

end Ground1
end PEqualNP.Outside.L_meta_12104.Reduce

namespace PEqualNP.Outside.L_meta_12104.Frame
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem enough : ∀ s, HasCircuitSize 6 target s → ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x)=target x := by
  rintro s ⟨C,fan,sz,correct⟩
  by_cases hn : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨b,n,hb,h⟩ := freely_chain C.gates C.output fan correct hn
    obtain ⟨e,k,hk,T,sub,path⟩ := Reduce.select h
    have low : 10 ≤ k := by
      cases e
      · exact Reduce.Ground0.lower k T sub path
      · exact Reduce.Ground1.lower k T sub path
    refine ⟨witness,wmono,?_,wcomputes⟩
    change C.gates.length ≤ s at sz
    change 13 ≤ s
    omega
  · refine ⟨C,?_,sz,correct⟩
    intro g hg
    obtain ⟨op,len⟩ := fan g hg
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.imp_right (fun h => h.resolve_right (fun e => hn ⟨g,hg,e⟩)),len⟩
end PEqualNP.Outside.L_meta_12104.Frame
theorem PEqualNP.Outside.L_meta_12104 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676608 * 2 ^ 32 + 3900735488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676608 * 2 ^ 32 + 3900735488) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := PEqualNP.Outside.L_meta_12104.Frame.enough
