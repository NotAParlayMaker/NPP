import PEqualNP.Defs

-- The live-wire and cofactor bounds build on the checked proofs of L-meta-1667 and L-meta-1920.
-- Their authors credit PressF10 for the framework. These proofs use the Apache 2.0 license.
namespace PEqualNP.Outside.L_meta_2193
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

inductive Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | stop (hp : proper target) : Live target 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
      Live target (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
      Live target (k+1) t (insert a (insert b U))

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩


def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]




abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

inductive Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | start : Reach roots 0 roots
  | one {p bank a} : Reach roots p bank → Available bank a →
      Reach roots (p+1) (inv a :: bank)
  | two {p bank a b} (op : Bool) : Reach roots p bank → Available bank a →
      Available bank b → Reach roots (p+1) (combine op a b :: bank)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

inductive Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | stop : Run goal 0 [goal]
  | perm {s xs zs} : xs.Perm zs → Run goal s xs → Run goal s zs
  | one {s a rest} (save : Bool) : Run goal s (inv a :: kept save a rest) →
      Run goal (s+1) (a::rest)
  | two {s a b rest} (op ka kb : Bool) :
      Run goal s (combine op a b :: kept ka a (kept kb b rest)) →
      Run goal (s+1) (a::b::rest)

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v := by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr

theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r
  cases d <;> exact bit_bin _ _ _ _

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]

theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z

theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (hs : ∀ a ∈ S, a ∈ z::w) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm

theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ha ih =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩

theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S, k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs

theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def seed4 : Sig := neg (inputs.getD 4 zero)

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed4_table : ∀ r : Row, bit r seed4 = !(sample r 4) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed4_nonzero : seed4 ≠ zero := by decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

theorem exec_extends (gs : List Gate) (ws : List Sig) : ∃ l, execute gs ws = ws ++ l := by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩

def neighbor (i : Fin 9) : Nat := [4,2,1,2,3,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_neg (f : Row → Row) (a : Sig) : rename f (neg a) = neg (rename f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a)) = bit ⟨j,hj⟩ (neg (rename f a))
  rw [bit_rename,bit_neg,bit_neg,bit_rename]
theorem rename_bin (f : Row → Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b)) = bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename,bit_bin,bit_bin,bit_rename,bit_rename]
theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {T k t S} (h : Live T k t S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p

def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live hp h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v := by
    have avail : Available ([] : List (Wire Row)) (observe v) := Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pT hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega



def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k t hk h
  generalize he : ws.toFinset = S at h
  cases h with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      have nk := kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne,rest]
    have sc := (live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → t=0) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  intro hh
  have eq := of_decide_eq_true hh
  have bound := (live_size h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega



def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m)

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available bank (restrictRows f (observe a))

theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a = true) : Available bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,masked_zero dom hz⟩
  · exact Or.inr ⟨true,masked_one dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1 && (c.1==2 || availableB d pool c.2.2)

theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q+1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  have ok : availableB d pool c.2.1 = true ∧ (c.1==2 || availableB d pool c.2.2) = true := by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha := availableB_sound dom hs ok.1
  let z := restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank) := by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2 = true := by simpa [unary] using ok.2
      have hz' := Reach.two (c.1==1) hp ha (availableB_sound dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w) = combine b (restrictRows f v) (restrictRows f w) := by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact available_cons _ (hs _ hm)

def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none

theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q+cs.length) next ∧ poolSupply f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB d pool)

theorem poolCut_sound {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws = true) :
    Impossible T cap ws.toFinset := by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega



abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {roots w} (ok : freeWord roots w = true) :
    Available (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)

theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := (live_size run).2
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩



def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then (if m.testBit 9 && j == 4 then neg (inputs.getD 4 zero) else inputs.getD j zero) else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (baseRow mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,Fin.ofNat 512 baseRow,Fin.ofNat 512 (baseRow ^^^ (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  let base := if m.testBit 9 && m.testBit 4 then 16 else 0
  (selected m).map fun (i,a) =>
    let r := base ^^^ (1 <<< ((hints >>> (4*i)) &&& 15))
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ^^^ (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {m hints L} (h : assertSize m hints L = true) :
    Lower (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := (m &&& 511) ^^^ ((m &&& 511) &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let baseRow := if m.testBit 9 && free.testBit 4 then 16 else 0
  let xs := supportPairs baseRow s
  let count := (xs.map Prod.fst).toFinset.card
  let drop := colFree free q 0
  let lz := if m.testBit 9 && drop.testBit 4 then drop &&& (511 ^^^ 16) else drop
  let lo := if m.testBit 9 && drop.testBit 4 then 16 else 0
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows lz lo) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let baseRow := if m.testBit 9 && free.testBit 4 then 16 else 0
  let xs := supportPairs baseRow s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) _ hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (vars q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


structure BoundPool where
  domain : Sig
  bound : Nat
  paid : Nat
  wires : List Sig

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires ∧ True

theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa using hr,hs,trivial⟩

theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB c.domain c.wires a = true)
    (buy : if paid then choiceOK c.domain c.wires choice = true
       else availableB c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible T k (choiceVal choice :: rest).toFinset := by
  intro t num ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n out)
      (zs : poolSupply f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have avail := availableB_sound dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : availableB c.domain c.wires a = true := known _ hm
        have point : ∀ u ∈ c.wires, Available out (restrictRows f (observe u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact availableB_sound dom point ha
      · exact Or.inr con

def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires)) && (!extra || choiceOK c.domain c.wires op)

theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {raw T d L cs c} (slice : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 768
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 768 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 768 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 768 → Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b) = if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
theorem faithful_neg {r s x} (h : faithful r s x) : faithful r s (dneg x) := by
  change x.2 = _ at h
  simp only [faithful,dneg,pairSig,ofRows_neg, h]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]

def codeDecor (op : Nat) (x y : Decor) := if op=2 then dneg x else dbin (op==1) x y
def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get base _)
      · exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then (if m.testBit 9 && j == 4 then ~~~(v 4) else v j) else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then (if m.testBit 9 && j.val == 4 then ~~~(v 4) else v j.val) else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · by_cases hf : (m.testBit 9 && j.val == 4) = true
    · have hj4 : j.val = 4 := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hf; exact hf.2
      simp only [vertex, hh, hf, ite_true, bit_neg, BitVec.getLsbD_not, i.isLt, decide_true, Bool.true_and]
      exact congrArg Bool.not (asRow_bit v i ⟨4, by decide⟩)
    · simpa [vertex, hh, hf] using asRow_bit v i j
  · simp [vertex, hh, bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then (if m.testBit 9 && j == 4 then ~~~(v 4) else v j) else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2



theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩


def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

abbrev ExtraCut := Nat → List Sig → Bool
abbrev ChildLinks := (Nat → List (List Sig)) × ExtraCut

def closeChild (pools : List BoundPool) (links : ChildLinks) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links.1 (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op) || links.2 k ws

theorem closeChild_sound {raw T pools} {links : ChildLinks} {k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links.1 tag → Impossible T k (List.toFinset xs))
    (cutValid : ∀ ws : List Sig, ws.Nodup → links.2 k ws = true → Impossible T k ws.toFinset)
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with (⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩) | cutProof
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok
  · exact cutValid _ nd cutProof

abbrev CovPair := Cov × Cov
def preCov (ws : List Decor) : CovPair := (coverage false ws,coverage true ws)
def getCov (c : CovPair) (d : Bool) := if d then c.2 else c.1
theorem get_preCov (ws) (d : Bool) : getCov (preCov ws) d = coverage d ws := by cases d <;> rfl
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb

theorem rest_coverage {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un=false → a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb := by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact cover_one d a ha ka

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws := by
  cases un
  · exact (delOne_sub _ _ _).trans (delOne_sub _ _ _)
  · exact delOne_sub _ _ _
theorem len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un=false → a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un || kb then 0 else 1) := by
  cases un
  · have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]

def movedDecor (op : Nat) (a b : Decor) := codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)
theorem moved_full (op) (a b : Decor) :
    (movedDecor op a b).1 = choiceVal (movedChoice op a b) := by
  by_cases h : op=2
  · simp [movedDecor,codeDecor,h,dneg,choiceVal,movedChoice]
  · cases hh : op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,choiceVal,movedChoice]
theorem moved_faithful {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b) := by
  unfold movedDecor codeDecor
  split
  · exact faithful_neg ha
  · exact faithful_bin _ ha hb

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × ChildLinks
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools} {links : ChildLinks} {cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links.1 tag → Impossible T (cap-1) (List.toFinset xs))
    (cv : ∀ words : List Sig, words.Nodup → links.2 (cap-1) words = true → Impossible T (cap-1) words.toFinset)
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h hk ndc (pair_sep pairs)
  have ce : cap-1+1=cap := by omega
  rw [ce] at sep
  let d := child.length==cap
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  have deq : decide (child.length=cap) = (child.length==cap) := by by_cases he : child.length=cap <;> simp [he]
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 768 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768) = false := by simp [sep]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  have val := moved_full op a b
  change z.1 = _ at val
  change Live T k t child.toFinset at h
  have nd' := ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact closeChild_sound pv lv cv nd' test k t hk h


def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  evalMove ctx 2 a a z false false && evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false && testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_unary {ctx ws} (h : testAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalMove ctx 2 a a (movedDecor 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPair ctx a b d=true ∨ testPair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (un=true ∨ v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  cases un <;> simp only [opKeep,Bool.false_eq_true,ite_false,ite_true,delTwo,List.mem_map,
    mem_delone wn,mem_delone dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (unique_value nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem unary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a : Decor} (ha : a∈ws)
    (keep : Bool) :
    (moveFront ws 2 a a keep keep).toFinset = (childOne (ws.map Prod.fst) a.1 keep).toFinset := by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha ha,keep_mem,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv := List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a d kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto

theorem node_sound {raw T r s ws pools} {links : ChildLinks} {cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links.1 tag → Impossible T (cap-1) (List.toFinset xs))
    (cv : ∀ words : List Sig, words.Nodup → links.2 (cap-1) words = true → Impossible T (cap-1) words.toFinset)
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    cases h
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv cv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links) a b d = true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv cv
        (eq ▸ pr) (eq ▸ fr) (testPair_at test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh


theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh)%slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


inductive IndexTree (α : Type) where
  | leaf (items : List α)
  | fork (pivot : Nat) (left right : IndexTree α)
def IndexTree.read {α} : IndexTree α → Nat → Option α
  | .leaf xs,i => xs[i]?
  | .fork pivot a b,i => if i<pivot then a.read i else b.read (i-pivot)
def IndexTree.values {α} : IndexTree α → List α
  | .leaf xs => xs
  | .fork _ a b => a.values ++ b.values
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values := by
  induction tree generalizing i with
  | leaf xs => exact List.mem_of_getElem? e
  | fork pivot a b ia ib =>
    simp only [IndexTree.read] at e
    split at e
    · exact List.mem_append_left _ (ia e)
    · exact List.mem_append_right _ (ib e)

structure Forest where
  mask : Nat
  cap : Nat
  samples : Nat → Bits × Bits
  cols : IndexTree ColumnInfo
  autos : Array (List Nat)
  levels : Nat → Packing
  index : Nat → Nat → Option (Nat × Nat)
  cut : ExtraCut := fun _ _ => false
  cut_sound : ∀ k (ws : List Sig), ws.Nodup → cut k ws = true → Impossible (chartGoal mask) k ws.toFinset := by
    intros
    contradiction

  recipes3095 : Option (Nat → Nat → Nat × Nat) := none
  rules3095 : Option (Nat → Nat → List (Nat × Nat)) := none

def wiresOf (g : Forest) :=
  rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a :=
  raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) := liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val :=
  bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 768) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let packet := match g.recipes3095 with
    | some reader => reader k i
    | none =>
      let recp := packedAt data (i*width) width
      (recp &&& ((1 <<< len)-1),recp >>> len)
  let ops := packet.1
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive packet.2 bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (g.cols.read_mem e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let entries := match g.rules3095 with
    | some reader => reader k i
    | none => getPairs data cw depth nr st
  let rules := entries.filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls,g.cut) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    cases h
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (g.cut_sound _) (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h


def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (vars g.mask) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known [] := by simp [Known]
def lanePlace (v : Nat) (upper : Nat) := 2^769*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
theorem broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat = combineLanes (fun _ => a) xs := by
  induction xs with
  | nil => simp [units,combineLanes]
  | cons v xs ih => simp only [List.length_cons,units,combineLanes,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]

def fullMarks (r packed : Nat) := ((packed+r) >>> 768) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i := by omega
      have ge : ¬769*(i+1)<769 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 768 = (a==BitVec.allOnes 768) := by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^768-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769 := by omega
      have di : 769*(i+1)+768-769=769*i+768 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)


abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
theorem top_xor (a : Bits) : BitVec.allOnes 768 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 768).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs := by
  by_cases un : op=2
  · simp only [packedOp,un,ite_true,packedSig,broadcast,lanes_xor,top_xor,movedDecor,codeDecor,dneg]
  · by_cases one : op=1 <;> simp [packedOp,un,one,packedSig,lanes_or,lanes_and,movedDecor,codeDecor,dbin]

def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (un ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) un ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) un ka kb) xs := by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 769) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (masked p.domain)).any (fun v => v==m)
theorem available_mask (p : BoundPool) (x : Sig) :
    availableB p.domain p.wires x = availableMasked p (masked p.domain x) := rfl

def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un || kb) ≤
    (opKeep un ka kb a b ws).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  cases un <;> simp only [opKeep,delTwo,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [constantLoss]; omega

abbrev QuickPool := BoundPool × Nat × Bool
def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p := s.1
  let un := op==2
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := choiceVal (movedChoice op a b)
  let zm := masked p.domain z
  let zc := isMaskedConstant p.domain z
  let cm := s.2.1 - constantLoss const a ka - constantLoss const b (un || kb) + zc.toNat
  let free := zc || zm==masked p.domain a.1 || zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)

theorem fastCost_good {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws)
    (h : fastCost (summarizePool ws p) k a b op ka kb=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true := by
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let free := isMaskedConstant p.domain z || masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest := opKeep (op==2) ka kb a b ws
  have ck := keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2) || kb) ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB p.domain p.wires w.1)=true
  · have hav := List.all_eq_true.mp all
    have ready : free=true → availableB p.domain p.wires z=true := by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have extra : (!availableB p.domain p.wires z).toNat ≤ (!free).toNat := by
      cases hf : free <;> cases he : availableB p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires)=true := by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact hav w ((keep_sub ws a b (op==2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.wires (movedChoice op a b)=true := by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b ((op==2)||kb)+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h

def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)

theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have closed := fastCost_good (mem _ hi) (mem _ hj) ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (contextWire c i) (contextWire c j) c.2.2.1).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true,Bool.true_or]
  repeat' split
  all_goals rfl

def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length ∧ j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1 yes.2 h
    next => contradiction
  · exact h
def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then true else
    let d := len==k
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs

theorem batchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  let d := len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((opKeep (op==2) ka kb (contextWire xs[q] i) (contextWire xs[q] j) xs[q].2.2.1).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,len,d,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := if d then packedCov (fun c : NodeContext => c.2.2.2.1.2) xs
            else packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r*(BitVec.allOnes 768).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 768
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := batchMove b xs i j op
  f false false && f true false && f false true && f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false && batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0 && batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow b xs i js && batchRows b xs js

theorem batchRows_at (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMove_at k n xs
    refine ⟨⟨⟨check hi hi hq budget arity allRows.1.1.1,check hi hi hq budget arity allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true := by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,check hi hj' hq budget arity pass.1.1.2⟩,
        check hi hj' hq budget arity pass.1.2⟩,check hi hj' hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩

def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let entries := match g.rules3095 with
    | some reader => reader k i
    | none => getPairs data cw depth nr st
  let rules := entries.filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls,g.cut)


def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
def deadsamples : Array (Bits × Bits) := #[(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadcolumns : IndexTree ColumnInfo := (.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (.fork 4 (.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (.fork 8 (.fork 4 (.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (.fork 4 (.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (.fork 4 (.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (.fork 8 (.fork 4 (.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (.fork 4 (.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (.fork 4 (.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (.fork 8 (.fork 4 (.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (.fork 4 (.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (.fork 4 (.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (.fork 8 (.fork 4 (.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (.fork 4 (.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def deadautos : Array (List Nat) := #[[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]

def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : IndexTree ColumnInfo := (.leaf [])
def g15autos : Array (List Nat) := #[[],[33,48]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index,fun _ _ => false, by simp,none,none⟩
def key31l6 (i : Nat) : Nat := 0x820007028af371d000003180048302e380000000003819155875690d58000003d
def g31d5 (i : Nat) : Nat := 0x84001e90fd02fd01fa00
def g31l5 : Packing := (3,1,3,0,4,4,0,g31d5)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,2,4,0,0,g31d6)
def g31samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : IndexTree ColumnInfo := (.fork 2 (.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def g31autos : Array (List Nat) := #[[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index,fun _ _ => false, by simp,none,none⟩
def g47samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : IndexTree ColumnInfo := (.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index,fun _ _ => false, by simp,none,none⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index,fun _ _ => false, by simp,none,none⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index,fun _ _ => false, by simp,none,none⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo := (.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index,fun _ _ => false, by simp,none,none⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := (.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat) := #[[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat → Packing
  | _ => emptyPacking
def g119index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest := ⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index,fun _ _ => false, by simp,none,none⟩
def key189l7 (i : Nat) : Nat := 0xa81337040d4b600002948880000590cc33d41450272020001b1
def g189d6 (i : Nat) : Nat := 0x82000f487f40bfa03fa00
def g189l6 : Packing := (3,1,3,0,4,4,0,g189d6)
def g189d7 (i : Nat) : Nat := 0x1f5859bf
def g189l7 : Packing := (1,0,3,2,4,0,0,g189d7)
def g189samples : Array (Bits × Bits) := #[(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : IndexTree ColumnInfo := (.fork 4 (.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def g189autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index,fun _ _ => false, by simp,none,none⟩
def g127samples : Array (Bits × Bits) := #[(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : IndexTree ColumnInfo := (.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat) := #[[],[101,66,16]]
def g127levels : Nat → Packing
  | _ => emptyPacking
def g127index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest := ⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,g127index,fun _ _ => false, by simp,none,none⟩
def key191l10 (i : Nat) : Nat := 0xa2d43b28d7001ab368009df79a6668d8a485480048c00a24000002900046192841e000000005078511fa7b8000001d8000000000050332001c2200008044
def key191l9 (i : Nat) : Nat := 0xb5d65558d2140ea31b806b286019a820212fb2e35aa613228a5a077246e6fc20ca1a41bb2d080a9c3e39f318874648000323b01b537426ceae26842215792e4b19e71cc72290229e7cad73d5f333056000d205f83e366a30000000d49821b1f1088000bb771a5c8c0000000000eb0000e0cb6ac6bec3c000c1b800347e18451880000012040006004d1cd8e0000001866e151a0000282800081e2a5e9518b100010bc00000030815564ae0000000000000ba722a1a34000000e6c5a954a6f09e6780014941d61a7112de27d595e7f09e40be3dc9678ab0bf3d70002c438a3dd4912345fe50900b4e481ecbbcceb07786be83e621d46430465b9b583a98309000098f882ae3a444b1d707c001bdad01b2c800179a0001f6d90464c82da1658b094500004b589e042e51604dd58429e06b90ff614389938aaeb6d12bb049522a72f25c09129e0463116174d50c3960b150c0a182d435d81d03dcbc0b346f3525916e494182a5649d22c9002ab560902d0004c5bd2828ce425700001e0842090d9c2ec56f6a2934aac61902201440c3800d7464005040d9808000b00120008008026140608781000c78f2e086830a0c98000580830000a023a002141e004000c001040a00380
def key191l8 (i : Nat) : Nat := 0x18cd14b25011e7225b26001876a3412158c6fc726c2320d6e3243bdd05603f1613ebb0007f7c604089b00125f5892200bf9421800b5e245039f1cf3cb8436d7f2000047800310000002025492575bf0012c00000042000001b8021c00800c01d000c080081
def key191l7 (i : Nat) : Nat := 0x2c
def g191d6 (i : Nat) : Nat := 0x47d6448788a00
def g191l6 : Packing := (1,4,6,0,2,0,0,g191d6)
def g191d7 (i : Nat) : Nat := 0x1021aae2c480c58812165850610304200048200685020d100000000000200100000fce5cec0b2a49f918c877974664f4a45403b36312c2722140f0a0500fd51548d13edd3641903fd51544d03fe92540d02df57305d02ff10305d02df4179dd02bf5819dd02df5819dd029fd819dd02df5155cd019fe885c901fe92440901ff114409019fc8788a009bd849dd039f5819dd02ed6668ce11f56558ce119f47840a11f3a5591200eda668ce00f5a558ce00bb9841ca00fca3388a00fb24484600fd23384600fe22284600
def g191l7 : Packing := (28,3,6,0,2,8,0,g191d7)
def g191d8 (i : Nat) : Nat := 0x850910304081c2440c0e2128f09183458e0d563c424bf1e12406128b1c7846402045834a31022c1244b4112285081c2449f022410c0418818084041a2060210127868c180849614f082043003c28008103c00a001050011a0c10d03085c404064a2030a0610180108a409488504804aab1e40a0610805408d7f063c2499716b62841c098f1800a084818401971629005810a08556544b736241080077f04053c18a8a2824181120efe78c80844603045000e102828008e8b070510443840106263000efe5858a100024042202241d09811e292070e043021810a5c588002801000c0052e2c5001418110006003021810c08516144821810a085042001810afc7897e3c49e14f0a7850604482184f83a8258107f37d67c179c77f77274572070b6f66e16cc6bf6aa69568066b64e63962c61f61a60d5f85e35ce5b95ac59758256d55053b50e4f94d44bf4a247d45843b4264113e43d73ca3b53a039338635934432f3122d52c02b328e27925c24f22a21d1f81db1be1b11a419718217516815b14e13912c11710a0fd0f00e30d60c10b40a709a08d08007305e04903c02f02200d000ffa4c91ffd0548ffe93227ff41513ffa4c81ffd1640ffe83207ff49503ffa2a81ffd0540ffea2a05ff4d502ffae6817fd2340bfe89a05ff40d02ffa2e817fe7740bfe9b203ff51501ffa6a80ffd24407fe91a03ff5cd01ffa0680ffd72407fe81203ff4da00ffa47007fd13803fe89401ff88a00bfceea2dfe774d6febb247f74d923bfcee91dfd7644efebaa27fd45513bfcee89fdd2344efebb207f74d903bfaea81fdd3540eff3ba07f744d03fba4d19fdd168cfee83467f749633fba2b19fdd058cefeb9a05fe40d02fbc66817f41740aff3ba057f5cc02fbc66015fd7100afeba203fd45101f7c8880dfd73407ef19a037f5c901ff20480dfe77407faa2c23fd4d611fea4708ff503847fa81423fd00a11ff209007be44803fc81c01f78ce00ff205007f901803fb08c01fe4da00ff28b007f935803fc92401fe45200ff247007f913803fc89401fe1ca00ff445006de668cfaf2ac67f58ce11f7489007da33803f511401fc84600
def g191l8 : Packing := (100,2,6,5,2,12,0,g191d8)
def g191d9 (i : Nat) : Nat := 0x180327c7c11a70600f8f1304b1c05f0c3c541303017c38f1204e0ef8f13040180df9e0e080325463418a006077cbcf0238c0ef961b3c041381be3e0900df9e30006fcf825f86eb1755933dd9099319085000ff517fd35ff48ffd13ff40ffd02ff00bfd01ff803de33fd847fa00
def g191l9 : Packing := (12,1,6,7,2,9,0,g191d9)
def g191d10 (i : Nat) : Nat := 0x1f3c11ff
def g191l10 : Packing := (1,0,6,4,2,0,0,g191d10)
def g191samples : Array (Bits × Bits) := #[(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]
def g191columns : IndexTree ColumnInfo := (.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (.fork 2 (.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (.fork 9 (.fork 4 (.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (.fork 5 (.fork 2 (.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (.fork 2 (.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def g191autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g191levels : Nat → Packing
  | 6 => g191l6
  | 7 => g191l7
  | 8 => g191l8
  | 9 => g191l9
  | 10 => g191l10
  | _ => emptyPacking
def g191index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 3 0 6 0 2 (key191l7)
  | 8 => lookupWord 17 64 6 11 5 2 (key191l8)
  | 9 => lookupWord 68 242 7 13 7 2 (key191l9)
  | 10 => lookupWord 9 46 4 10 4 2 (key191l10)
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index,fun _ _ => false, by simp,none,none⟩
def g251samples : Array (Bits × Bits) := #[(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : IndexTree ColumnInfo := (.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index,fun _ _ => false, by simp,none,none⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := (.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat → Packing
  | _ => emptyPacking
def g255index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,g255index,fun _ _ => false, by simp,none,none⟩
def key383l12 (i : Nat) : Nat := 0xf8400002630000023000000000000000000b83d5688000000000341000030000000000814000015d0000000210344000018d003b10000000000e080000000e70005c3803500091000000000008
def key383l11 (i : Nat) : Nat := 0x404c001fd7a0dd080d1200990f207c017043e0ac430a491c9aec7438f32422a414035a0e000e6f384202824e3e5491f317a0090ee161490000d0e481ce32000c4b9104c1860ad6100030920000000003c06000000722ae38f1200000035c780290bd08d23d219503209024ec0512fd44dc0985ef07266b48508d728f004824e9809324688ad260642ee33843c9e425582082c2260138002f8f81ac0c0002216a57414583e222000012800202204f00400024f34c01300e78608380c041012080080846040
def key383l10 (i : Nat) : Nat := 0x8a7028008f8208641c25de616202731427f0aa3ea6a9bc18603a40bac46606be46000184a7c7d25a0000000b98af69a264a6b01ac3b3a21709000001146294f5b28f5117b2b2368000000119a0000000503689a2858e10b056a96282c8039064ce4000005a1824c4b68b4a1ca0160003a96c1c5108908a005faaaa16a13000042ba8544116a040004b6aa18802880c23178071841517e2559911705a04117c6495c00000000085d314e242a96a0880000a01fc56687256502c84968668866a1180000003d68390f815a1fa922000012b8020000c2a6caf0234475dcf201fa032887c28e092c47a60725df80221bc02a000007a61e192100d1c1f61f683d817642e40874ab202e012c0cd05141d60b104cb094626909c0000000c0e573a858d7326a6285e00010ac0007468e22e50bc16f60921b5c8f41249001273800322800110cb04e0005728622182280ff076809bc29a93800081a596455d1053c0607cc3a5870000108081400524002801c04219100c0821c60cc13c0c2030a201001e00285000001f020030024000800c08280
def key383l9 (i : Nat) : Nat := 0x6977b1303806491384c288005f480044300b4273a470aef249bb09d0238c000000000000000603688ce51876813ab9e6c881d7b37687df408050502a181c84000606800000000000000424bbbaa9612800409100800346576b8a520800702905aa985610b9a10486080010008502020c0020a18085
def g383d8 (i : Nat) : Nat := 0x7c610014028800000000000000302080140040000000a09b827d78736e69645f5a55504b4637322d1e19140f0a0500cef45d94a2103afbaa93760801f7445d0744d03aaf69017618038fb68a9960d01ad76949760c01af34a89760c01af64289760c01adb6943760801aeb69037608018fb6683760801af94683760801afa42837608018ef690988ce009fcaa9190de009fa68a9944e009deaa99504e009deaa99520e009ee690988ce00be6690178ce00be6690918ce00be6690988ce00bf84a83784600bbc6989384600f749de3384600
def g383l8 : Packing := (25,4,6,0,3,8,0,g383d8)
def g383d9 (i : Nat) : Nat := 0x2dd0028c0601f18c02041010022160ac183c0004580028bb3c71c058816e807460680741c30700441602883bd0180c08009e92a09189248391a905315048c4c0a178c440a1c344e20480c5e3ec8c4124f1f67a1c70097c7d918050801b86cae3f18d8123489e81e3f187030392c68303e84a0683078305e30e0607e38f83c60f060a511f174250341f8c5e031010ee21078c3c161c0cee22050c28801004142c00504800c7c3000f402160a08ae97100120112003c70a082689408970b120030209083000c003000838e14007c610001c70838e1020020212004000023e3ec8cb8e14489e2f1a14a23e23d15c47a2b88f457115cca2f195c5e3ecf438e4f9debbcbf80ec1d2799709dd3b93626add2d9db38e63c8786afd5e3b876b2cad6ca75446864ec9992b24646c8990d60abf57bcf1dd3b7e6bccf98f3075e0b6565abd55ea85452734dc95d24a3b45a858ff9f13c6754e39b9356698cc18a2f85dcb916d2be568a61472724d08e918226438650b3138214370570800a4005ff65c1840f7fa2f442077fd9720d01dfe9bd1080dffa6537006ffd329bc017fd9704e009fe44a2e81ddf6541840f7ea300c2077bd94a2103ddeca51081cff6468840ffb20e89a07fd41844d03def4422681cff6241700f5fa2ec3007afc1761803d7e8cb0c01cff65d8100f7ea2ec08073fe99604039fe44a6e80cff65d834067fd32c1a03bdd8320d019fec4a0680cff64e884067fb121b8033fd9760c01dee9bb0600ef70dd830067fd32c1803bdd9760c01dee4bb0600ef7a65830077da6ec1003bec37608019fe44a6f005ef65037802fda521bc017f5190de00bfc8486f004ff22513802efb2a09c017f90904e00bfccba07007f644d03803fb20719c013fc988ce00bfcc9a03007fc406118027f93108c017f8894de00bfd4ca6f005fe46437802ff32e89c01ff11744e00bfc44a27005fea6513802ff32e09c017f99720e00fec89907005fe64483803fb26f19c01fd9138ce00bfc4c467007f645e33803fb02f19c01fd8918ce00fec4c467005fe64c81803fb46640c01ff11384600fed19c23005fe26211803fe26f08c01ff03784600ff849c23007fc8ce11803fe13108c013bd94a210397f4cb0c01cf7a6583006f73281bc017e9290de00bf88c86f005de65413802ef32a41c01fd23384600
def g383l9 : Packing := (91,3,6,5,3,11,0,g383d9)
def g383d10 (i : Nat) : Nat := 0xb1c029771ece80316e3a8b78f40771ca00d1002da03a69a8d16d01d28d4d3292968b98ba7f8c288f4271a30301042b0c2ce3d9d0c753d16f1a58de8639cbb8c715c8d44b554a1a9a3e0a89a12200921586544f91de7c3c6840c59058fc73e70a427a578082339c40459aa8af185209a7d34148d4cb55354aae60605689f215010071ece816c5e382c02c0800b78f67401b1c150a01655c62e06083462ae3d9d02d06c70541505820071ece801e380c14030a8b4a07c8d48497c63f8e66a4b4202e31fc73a14025b571ece863a00201e95c8d50005c7b3a084978e980d957652718d2b8da90a038f655cc3ed026a4b80d9d0683120b8d0ca07c4503e24b0080e3d9d0c73a100400171ece863a2041f8deb9e05d31c9dc29ad59e194d8397a571169d5a94d53c132d2591c5050edce08cf4b60acc9f89047f075c62859452044c3f83242b025c208114003ff45d03ffd1840fff06103ffe8840fff44d03ffd1700fff05c03ffd37407ff60d01ffc83407ff40d01ffe88407ff4dc01ffc37007ff4de00ffc37803ff44e00ffc13803ff8ce00ffe11802ffa2103fdd1340eff60403bfd83406ffa2101bfd83007fe40e00ff901803fe4de00ff837803fe44e00ff813803fe20e00ffa33803fe20600ffa11802bf61803bdd83006fb60801fda33803fc84600
def g383l10 : Packing := (41,2,6,7,3,12,0,g383d10)
def g383d11 (i : Nat) : Nat := 0x540b1d9a02e3804632e686a85e3b342382008507c4a8582c71cf98063b342397069da95ca003fe81ffc03ffa03ff007ff007fa00
def g383l11 : Packing := (6,1,6,6,3,8,0,g383d11)
def g383d12 (i : Nat) : Nat := 0x11b280e4ff
def g383l12 : Packing := (1,0,6,3,3,0,0,g383d12)
def g383samples : Array (Bits × Bits) := #[(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]
def g383columns : IndexTree ColumnInfo := (.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (.fork 3 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (.fork 7 (.fork 3 (.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (.fork 4 (.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (.fork 4 (.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (.fork 7 (.fork 3 (.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (.fork 4 (.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def g383autos : Array (List Nat) := #[[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
def g383levels : Nat → Packing
  | 8 => g383l8
  | 9 => g383l9
  | 10 => g383l10
  | 11 => g383l11
  | 12 => g383l12
  | _ => emptyPacking
def g383index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 17 68 7 12 5 3 (key383l9)
  | 10 => lookupWord 57 200 7 14 7 3 (key383l10)
  | 11 => lookupWord 30 108 6 13 6 3 (key383l11)
  | 12 => lookupWord 6 61 1 10 3 3 (key383l12)
  | _ => fun _ => none
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index,fun _ _ => false, by simp,none,none⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3 : Lower (vars 3) (graphGoal 3) 1 := size_of (hints:=1) (by decide +kernel)
def maps3 : List (Nat × List Nat) := []
def known3 := extendKnown [] 1 maps3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3 : Known known3 := extendKnown_ok baseKnown low3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 2 := size_of (hints:=257) (by decide +kernel)
def maps7 : List (Nat × List Nat) := []
def known7 := extendKnown known3 2 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7 := extendKnown_ok valid3 low7 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom15 : graphValid g15 (boundsBefore known7) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s15_3_0 : block g15 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl15_3 : block g15 3 0 1 = true := s15_3_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact bl15_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower (vars 15) (graphGoal 15) 4 :=
  lower_forest (g:=g15) (i:=0) (hints:=8449) (before_sound known7 valid7) geom15 tables15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat) := [(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def known15 := extendKnown known7 4 maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known known15 := extendKnown_ok valid7 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45 : Lower (vars 45) (graphGoal 45) 3 := size_of (hints:=8965) (by decide +kernel)
def maps45 : List (Nat × List Nat) := []
def known45 := extendKnown known15 3 maps45
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid45 : Known known45 := extendKnown_ok valid15 low45 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low51 : Lower (vars 51) (graphGoal 51) 3 := size_of (hints:=1) (by decide +kernel)
def maps51 : List (Nat × List Nat) := []
def known51 := extendKnown known45 3 maps51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid51 : Known known51 := extendKnown_ok valid45 low51 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known51) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_5 : block g31 5 0 3 = true := (@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_6_0 : block g31 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_6 : block g31 6 0 1 = true := s31_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact (rfl : block g31 4 0 0 = true)
  · exact bl31_5
  · exact bl31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower (vars 31) (graphGoal 31) 7 :=
  lower_forest (g:=g31) (i:=0) (hints:=8449) (before_sound known51 valid51) geom31 tables31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat) := [(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def known31 := extendKnown known51 7 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31 := extendKnown_ok valid51 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 5 :=
  lower_discard (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (before_sound known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat) := [(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47 := extendKnown known31 5 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47 := extendKnown_ok valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 5 :=
  lower_discard (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (before_sound known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat) := [(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55 := extendKnown known47 5 maps55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known known55 := extendKnown_ok valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_discard (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (before_sound known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat) := [(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63 := extendKnown known55 8 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63 := extendKnown_ok valid55 low63 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom111 : graphValid g111 (boundsBefore known63) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s111_6_0 : block g111 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl111_6 : block g111 6 0 1 = true := s111_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact bl111_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower (vars 111) (graphGoal 111) 7 :=
  lower_forest (g:=g111) (i:=0) (hints:=16785665) (before_sound known63 valid63) geom111 tables111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111 : List (Nat × List Nat) := [(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def known111 := extendKnown known63 7 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111 := extendKnown_ok valid63 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  lower_discard (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (before_sound known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat) := [(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119 := extendKnown known111 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119 := extendKnown_ok valid111 low119 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom189 : graphValid g189 (boundsBefore known119) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_0 : block g189 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_6 : block g189 6 0 3 = true := (@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_7_0 : block g189 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_7 : block g189 7 0 1 = true := s189_7_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact (rfl : block g189 5 0 0 = true)
  · exact bl189_6
  · exact bl189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower (vars 189) (graphGoal 189) 8 :=
  lower_forest (g:=g189) (i:=0) (hints:=536879876) (before_sound known119 valid119) geom189 tables189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps189 : List (Nat × List Nat) := [(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def known189 := extendKnown known119 8 maps189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known known189 := extendKnown_ok valid119 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 5 := size_of (hints:=1366507616) (by decide +kernel)
def maps250 : List (Nat × List Nat) := []
def known250 := extendKnown known189 5 maps250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid250 : Known known250 := extendKnown_ok valid189 low250 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  lower_discard (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (before_sound known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat) := [(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127 := extendKnown known250 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127 := extendKnown_ok valid250 low127 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom191 : graphValid g191 (boundsBefore known127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_6_0 : block g191 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_6 : block g191 6 0 1 = true := s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_0 : block g191 7 0 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_7 : block g191 7 0 28 = true := (@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_0 : block g191 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_8 : block g191 8 0 100 = true := (@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_0 : block g191 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_9 : block g191 9 0 12 = true := (@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_10 : block g191 10 0 1 = true := s191_10_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact bl191_6
  · exact bl191_7
  · exact bl191_8
  · exact bl191_9
  · exact bl191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower (vars 191) (graphGoal 191) 11 :=
  lower_forest (g:=g191) (i:=0) (hints:=536879361) (before_sound known127 valid127) geom191 tables191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191 : List (Nat × List Nat) := [(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def known191 := extendKnown known127 11 maps191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known known191 := extendKnown_ok valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 8 :=
  lower_discard (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (before_sound known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat) := [(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251 := extendKnown known191 8 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251 := extendKnown_ok valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 12 :=
  lower_discard (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (before_sound known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255 := extendKnown known251 12 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok valid251 low255 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom383 : graphValid g383 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_0 : block g383 8 0 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : block g383 8 23 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_8 : block g383 8 0 25 = true := (@block_merge g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_0 : block g383 9 0 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : block g383 9 84 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_9 : block g383 9 0 91 = true := (@block_merge g383 9 0 84 7 (@block_merge g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_0 : block g383 10 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : block g383 10 5 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_10 : block g383 10 0 41 = true := (@block_merge g383 10 0 21 20 (@block_merge g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_0 : block g383 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : block g383 11 1 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_11 : block g383 11 0 6 = true := (@block_merge g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_12_0 : block g383 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_12 : block g383 12 0 1 = true := s383_12_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g383 0 0 0 = true)
  · exact (rfl : block g383 1 0 0 = true)
  · exact (rfl : block g383 2 0 0 = true)
  · exact (rfl : block g383 3 0 0 = true)
  · exact (rfl : block g383 4 0 0 = true)
  · exact (rfl : block g383 5 0 0 = true)
  · exact (rfl : block g383 6 0 0 = true)
  · exact (rfl : block g383 7 0 0 = true)
  · exact bl383_8
  · exact bl383_9
  · exact bl383_10
  · exact bl383_11
  · exact bl383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower (vars 383) (graphGoal 383) 13 :=
  lower_forest (g:=g383) (i:=0) (hints:=12901687553) (before_sound known255 valid255) geom383 tables383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat) := [(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383 := extendKnown known255 13 maps383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known known383 := extendKnown_ok valid255 low383 (by decide +kernel)
def hashdeadl14 (i : Nat) : Nat := 0x4592c8500000000002800049a6c68a83340e9800000aa00684000000054a001bcc7001e180000682000000000000001d46a1840000003a00000001c
def hashdeadl13 (i : Nat) : Nat := 0x301a0007b2f00e0aa2992094818000e2e0000000269e056438000000000d33e40e4a200074d00000000000003b10001e0240a9bd45d962582900000000000001430001e1400000fc03b84a000614e69108a1108000810000d04c9d0000000408800000160f24180010b9d040003080001e0c000000000001997f401183740ee12000000000080d312c00102c00000000012070000000001d35000308c000a4c0001b30000000cb3800183000070f0000001abcc008002c8cc133000000000000000000000020b000000064ec0a00000f8000cc5000105d8204160001a38001c1c467309c000000a7700000016de30f80000008380b08e000d3001
def hashdeadl12 (i : Nat) : Nat := (if i<1 then 0x7b02c3200425d610a000042a0327300000000106b33757005e04600006037d811679d009461963480703e1077f067f2582384275d80a540a20109b59b4006305d00000000ab6dfb0bf59ec084c806986b30597776440b146b100c50a956520000878e0000747c463e108bc029e7600000395ef090d06800000000f0550000d0b1e4af00000000f324d141840ca4380000000051505017000067300000e779907b0000e77730641201ea62a089a48ff0924111e9a7a041b2a180aee462f29d9b47b01eb0427030e02a5973605b9086f08d5081d04bb014363000006038c0b6d110106cc731308e0023a07fb1305601ba1839b4c088a10b88011043e427e75a600831464016903d3ba52b1ec095000ec050b011b0730478f11a0000755e331ef63db004a00a000069a91680e225f60f90092a9d0000764650a40000c591f95ac03baa33c5a1283d11871a6d2772c01c1057280f201f5012328b908232a5505e000fe02b507cf0809817c267c05c9528506d997696872194b206264030ad402d007d586d7228701d30605840f67838625a51443ce034d47ed45f704cb08730a1794e1252000070330000b56f0000b0b4000000000000a842e047609d406ae26b67b08a4de12aa0a34019000000000000b664342c50b50000c0af924dc9aa401870366002b26d00000000841e0000000060986614000000000000783ae10d980ee051d0ab4022a615808f0000a0832619a148d81500007000e007d616b032d01b483f163f00104028276b2015141030631049a027580cd0a7a05ab977802fb09ff07a97899053b0a80816e83be0790a1b809b8b460a4f0000178b0000847be03cf139a1170000b07850b3605408416262696b908af0aa7b1f5b446070d024601a42492101d496f4b4e035922127ab0000e18600008284831c00440000f031500310656013b071b045b25b4113766b5b4c6b0800008291b4888a50000000000000e38b0000225eb04d807230618425c0b097ae226f809e00000000f00d93480485e88728040000b11c3039204e9432711f445c905f004a300b97ada05680211292f09a7b1a696f3106704f19748066703f00000204d074ba20a118f025458794596091a06f000065946020913b783e342dd08c819b5b452076c21dc075e0991a4a183c3b19d7a750a68058c8379643a487b408d0523762d062b422e0b2d47fc0ac224a46231a5dca3b6069a4390000768a5433e07e0000da410b00003102090604000a010a1f88080000080d030b0c310304001300040113030203141f0c0001000232030b0801010a010007110002020208010605020401010119010b0304070203070506000210070d110100150b0a0504051d050002020b05000c0402003d0e1500260200020108040b03090500060204000d0602010100180501000001030f04 else 0xe0a0512830933085c048e216509713746026a02ec09cb040548400000268f701103ac254729fc29e8096145a39ab47552144806e00019612b7b4491ea44bc1)
def hashdeadl11 (i : Nat) : Nat := 0x5b144463e05aea749a36008e0000f05f008fc82400000000057a08357304bb42c02b0000807cd1701823000007095811411b96631031e07218223334c77b980e8010305dd000180820521064ca3ef0420000409b626cd483a833f03ac022e048a008f80a513f0000db73410f3393ca38834018881012b081c465a02c6142704300002631809700000000715300007115b00dd054b2886014000054161b183099000000000129f0870000a24110110427972915960000477d5b457113518aa01a00007134a023d08a1053002d678ef06b604a6076520f5468b025698fe62d5060c1370000e07eb793c95be02a510198285417000000000000000000005b72220ea00f9098e036e09602120000503908396112556c56084a3a211d0342f0784635707b4293308d0624205556235211962a72516903a0190235010e7765e07d5784f16feb3c248834149073d088b0134091f720f0803275f0052809446ed494b01b1b0305939136b20cf495111aba390000db890950e9807026e609a0205015880ba66b8778d4967988f077f007110cd289d0160000e278401d0000000000000000f032027400000000a08c6209804c4030102eb368a33f3b1d798e0000538a70215061a44e228300000000000000000000d01710838075e4517067406f00000000609a00003253a089a4002093b00a8125000090790000c0599583180c00000000c0411830f1160047224900000000906992725046700b000050511a67544b00000407c35bb06d0000504d3821ca470002762e0000cb1760948827b10a603b4009e06552019464444f9688a0286169097ab82524185057db2feb3d000e6303670ac01e70822426b090d664c05cf764008be03c365d6a2549347068706a71244461f086277c5780380d698dd120b27c20626037d807f403502fe1110000ea6e5071301cb0388044704f411c809595011003b20deb1a98372208b0561092820a91190049704bb03ec070670890335001a03f64504063613c50294b430832441aba46e146c8120193598c103df8314066401fd460e0745084044c100c7760b24b824f4006205b0000563070507a7c9058000000006a440000506e3040e97d006cd027646a6207807fb0450138e56fa018704e8482e0356085662f762c5b3be05eb81f1004f836000000000000000046203a6ac89692730000b034807a613d00008145702433536a79b0407805012a04e80082c50a0c0e782286421a0e4c00400004833a1491a02243880c0851202004211c6408c1835c192e081800c39681005000c04e408002001860c34c8040000000400008087400400100892c38005148410524200800478080001438126000000020022
def hashdeadl10 (i : Nat) : Nat := 0x1c05302000382d2ecf474c3a08f618409ea54931a0a2272b385214e934380040192451090d15cc0564307983441ce005970002c06068f08a82680cc070001a2c5d4a1440400018207150002808001022205d856c41e1700072d518800084a2900000a334a12801820030b1a27
def hashdeadl9 (i : Nat) : Nat := 0x202e0
def deadd8 (i : Nat) : Nat := 0xa24b7baf6624ad253281df927589c4d52540d02
def deadl8 : Packing := (2,6,7,0,4,3,0,deadd8)
def deadd9 (i : Nat) : Nat := 0x17a6100d01602e1f830400f202c200003405840f980801c0010720e8006a183c001d000f8007c00200001509fc5a0b0071b79b2bc5ba99429c459e8d258238d84a14078280a00a7becc495a4a6503c6fdb66689a4d50287fcbc661a544d029ef9c6aed1840d02bed9c626d3540d02ff49184d52540d02ff489c4d52540d02d7f11826d1540d02ffc1184951340d029f6cbc4a1354950195fdc7aed2564d01ff49384d52540901ff61384951540901ef4935496aa40d02df49b54951340d02f7493549503a6502bf62cc4951540901ef6125456aa40901f7612545502a6501fb61284612545600fbc1284612344e009dd9c7aed258ce009ee9c6aed1888a009df1c7aed2584600ff42558ce2284600
def deadl9 : Packing := (25,5,7,1,4,9,0,deadd9)
def deadd10 (i : Nat) : Nat := (if i<1 then 0x2693540b3fecd1349aa055ff26d1a4d502cffb30d2a26815ffabb4610340bfec8c26a81a05ff626d3540d02ffd23092a06817ff1184550340abff5da6b4ca059ff4d5a1a65029ff9569426a80cffdb8aa9354067fed95549aa03fdb4a13549501affb7092b2680e7fda849593407bf69424ac9a035ffaed2564d01cffab15532680e7fd25aa993406bfedc26ac92035ffaed3564901cffab0d1b2480e7fd38aa9924073fe9ad54c92037fe6e13540901fef2b09aa0480ffd9384d502406ffd5da6a81203ffa4e12540901ffe2708aa0480f7f95864d02406bff5da714ca03df74e135a6501affd769ad3280d7febb49699407bbe9aa4b4ca035ff6e123a6501efda5091d3280d7fdb548e99406bff5da474ca039ef495a4a65038ffb63553308167f9b0aa998408bff5dd54cc2053bf6daaa461028ffb6a4d2268157fabb6610340bbf4cc24a81a055fe26d1540d02cff33155206816fd935aa90340b7f492d5481a057f66d51340d02ff924a89a06816fdaaa44d0340b3fcd42074ca05df64d503a6502efd24a81d328157fabb40e9940bbec89a074ca059fd461a1a65029bfb6f5524a80c7febb6a1934063fedc554c9a031ff6d6aa64d01cf7b695532680c7fdb2aa9934073fcd8554c9a031ffaeda8649018ffb6ad1b2480c7febb68d92406ff55da4a81203fda4d52540901fee34a8aa0480f7e92564d02406bfd5db2681203bfa496aa40901dfe22b5520480e7f993aa902407bf492a054ca03dfc45502a65019ff36755251004ff9b1aa928802ff55da5092c01efa4a11849600dfd2515524b007f692849515803fb88c24a8ac017deaed2545600def55492a2b004ffabb6a123802ff55da5091c01efa4a11848e00dfd25155247004ffabb6a1138027fc55a5089c01afe6a12844e00bfe5768c227007bf128461138027fd5db4a89c01bde6952544e00dfe23155227004ff9b8aa9138027fcdad5489c013fe6caaa44e00ff925091a27007fd11848d13802fed5da4689c01bf6aa92344e00bfb57692c67005fdabb45633803fac92a2b19c013feaeda844a009ff370d2a25004ffabb695128027fcdc346894013fe6d5a344a009ff576d1a25006ff1a844d12802ff95da2689401bf66963344a00dfe22755225006fda33aa912802ff55da71114017faaed1888a00bfd3709ac45007fc9384d622802ff55da6b114017fa6e11388a00ffc23089c45007bea8844e22802ff4daa27114017faaed1388a00bfe5769c423007fd1384d611802ff95da6b08c017fcaed2584600fee26a92c23005ff1b848e11803ff09424708c017fc6d52384600bfe57691c23007fd1588ce11803fe89446708c01ff44963384600ffc27111423007fe13588a11803fa49aa4a81a05fd849515409019bf36f5524b007bd2888ce11803df14444508c01ff08ce2284600 else 0x4000888405e986c113905805080340b02e1f06087905c2003f080d05c2010004400c0288128f50060048004020800804100127c503a3f6c170230c990618643002074409038882341900e30020304004060800870140c00228180045c08224a09086c45817020801a183810008ad48702001100108e2b0c1c0800456383810230b0200117dff6de0be2c10281f00a20021f8a108140c707c503e3f8bed83901520010dd505020c988c1183426000e000e00086905c20a40d058002020340034003c1834002fd2040bdb798060306e1b00c84f01a5f8a10bc3024202bf0c090605c00880505210010fc506e1cc0693effc5f6de600097e28190cc11092183f1414080603412860a40cc6004380038003800340034003c003c0020e00107000f000801c0020e00100f78ee2192287800ec3041c003c00361820e001f8a1e001e001e00100000b0411ef1dc4377ae886cc5917b60fc50f000d8e083e2840000016a420f6c1b1c100000b521002c30416383f1420003e284000100c4aca220cd523db61a02c91b20b40600a0dbf169c61a02c9f6de60578fe2fb6f303f8bedbcc0fe2fb6f303d0acfaceacb9c93c83c68c63c53c38c1dc02bd1bb6b9bb96b70b4ab24b09aeeac8aada92a77a5ca41a31a169fb9eb9e69e19d19b69a698b97096094593591a8ff8c38a889887284c81b80b7f07bf7af79f78f7747597497397297197096f96de6b867c64b62560a5ef5df5ae5725415315164fb4d54c54b54a549548547546545545044043b42b41b4164114013fc3ec3e73cc3a639639138137136135c34c33c32c31c30c3073022fd2f82e82cd2b229728727726725725224223d23823322e2292192142041f41ef1ea1e51e01d01cb1c61b61b11a119118c18718217216d16810009807204c026000affd7692d3281defdb6)
def deadl10 : Packing := (156,4,7,5,4,12,0,deadd10)
def deadd11 (i : Nat) : Nat := (if i<1 then 0x86120d08111f407ad1db072b1c206d11ab867718d8613174859115b85231388497118042910183c50e603570c082b709d822b07a8195055010902a80410003ffd1849503fff6692540fffd2546503fff4613540bffd9a4d502fff2693540bffd1a4d502fff4619340bffd3546502fff4d69940bffd9a4e101fff6a135407ffd284d501fff4a935407ffd9a4d501fffaa935407ffd3849501fff4e925407ffd9a49501fff56123407ffd9a48d01fff56193407ffd2864d01fff49593407ffd5864901fff4e192407ffd3564901bff6a11940f7fd9846503dff6551940effeaa46503dff4a51940f7fd25a6503bffaa99840b7fd1a66102dffaa99840b7fd9a46102bffaa91840bbfd9846102dff6619340affda564d02dff6559340affeaa64d02bff6951340bfdd9344d02ffe6a10340bff99840d02ffe4610340bff9a540d02ffe6550340bff91540d02ffe4690340affda846502dff6611940affda346502dff64d1940bff90346502dff6629940b7fd93a6502ffe40e9940b7fd18a6502dff4d69940b7fd13a6502dff66935406ffeaa4d501dff66925406ffeaa49501fdf4d525406ffda864d01dff66193406ffeaa64d01dff561934077fda864d01dff4a1934077fda564d01dff495934077fd2a64d01dffaa993406ffda864901dff66192406ffda564901dff65592406ffda364901dff64d924077fd3864901dff6a1924077fd3564901dff68d92407ff95840901ffe4e102407ff9a840901ffe66102407ff93540901ffe69502407ff99540901ffe68d02407ff99340901dff4e2994077fd35a6501dff496994077fd23a6501ffe4e928803ff91a4a200ffeaa928803ff9a849600ffe46125803ff93a49600ffe46925803ff92845600ffe4e915803ff92a45600ffe6a123803ff91848e00ffe69523803ff91548e00ffe46923803ff9a844e00ffe4a113803ff9a544e00ffe49513803ff92a44e00ffeaa913803ff95844a00ffe4e112803ff9a844a00ffe4d512803ff9a544a00ffe68d128027feaa661029ff2693540a7fc9a44d02dfe6610340bfd93540d02ffa4950340affaaa40d02ff644d0340a7fda8a6502dfe40e9940a7fda3a65029ff6869940a7fda864d019ffaa9934067fda8649019ff68d924067feaa64901ffa49502407ff11540901dfe64d02406ffaaa40901dfe40a99406ffaaa4a200ffa4a125802ffaaa49600bfeaa915803f792545600bfe6a123803fe92848e00bfeaa923802ff9a844e00ffc46113802ff9a544e00bfeaa913803fd92344e00ff649633803fd9158ce00bfe6a112802ff9a544a00bfe68d12803ff11344a00ff68cd12802ffaaa44a00ffa4e222803fe91888a00ffa4d622803fe91388a00ffc4e211803ff13584600ffc49611803ff123846009ef6929940fbea8888a00ff48ce11803fe22284600 else (if i<2 then 0x6718d1b071686b63b38c6ac837ab208143ea5f4a804c20460a84911c7405186a093027a82ae19d57d066c694fa70dcc0ac4ea478ce31a1ecaeaf303c8c241ac2f19b38c69c83fbee47302190238ea2305424c6856399d2085637d12388c0c16cbeff1d208076416c80b40c0049e29d5208144b23f46802b201800c183275231bc58d5919c2ba9ed854030806003067bf9c352078df64634afd056e600c20020b418eaf319c182b832c8683382f1c2de703e3ac80ac412003efc19433aad06707f7f38754282036168bdf159a0ce09fa590158824f17a919786904bef86bc33ab209458f7dd8e39c8904deff5232b9120958e0b701b7e8611b1e288d8776dd9609e2b1c2f1582105b80098e0b90124824976d090cd009250909820be81c002d484d8f144c3068ea08444c12222609117812260911961224208de83785dd4e900b63480dfc5edb981b80c307224fbfd4f301f09477d2a0d202e2010188cddb353cc69017202256222f7fb60add5a80164f6c116903054660bb98d200c6e0e18f8afa73037818602100ed9a0d20beff8bdb752d00186f7fc5ea78e6e01e33bfe2f534770c056718d202388c2401066f7fc5ea68ee1b388131a6862ef8df646718d182bf7fa963ac8ce31a3fbfe2f6dd4f31c70187010d8f7c2b7561a05a04ce121581816fbfdb3530d74005590a1982b682c8ce0be2f6dcc0184f14410307c705b875e98d59067d2d5c686717058176d8d1b06f7c92f17b6e602d3634e457030b7007d2a0b20be2be9500fdf0b7b6c68d029b1803bfe2d415c1bc57d2a01fbfc3600ead415c1bdf363c5c6a8eae0d8d3915c0fdfe0b00ed9a9a81c83fbfc3600ead40dc1ba9e3b0e77f1ab22b839c4d4e356457053ab00682c8ae0bdb341640fdfea700682c8ae0dd49c58d1bc4ea782c02c87d1a03753c751d873bf64634dc23dfe0a86c03b6755a03fbfd4e0164340dc1a82ea786c03c57d1a03fbfc36015c3aad01bdfe3a8ec3ab86a71a7211eff5380570d03906f7fc5edba9e1b82040ec751d87590fa7538d71ddc2586a198ec1bdff16b8ea71ae195efb915c7ab8d74068ed23878d423198bda2f18b3a2a189fa24788e221f881a1e387521a785ea14384820fd83ba0cb82a2071816203f8099ff97ee1f8b7d29f137b21e9179b9e377829ddd76c1d8d7581d3373c9cb17239c6170f9bfd6f41ba36e01b536c99af96b31a9f69c9a4568619f5665990f63618ab610981f5f517935dc17435c0969959b163558495c7566954f54b14f552f949151914374f393a14ce130b4b2929349c124347e11cb46c9185456112143a90a941c9063415103b4088ff53f70fc33ea8f9b3e30f7d3d68f4b3cc8f233c50f053bd8edd3b38eb53a70e8339d0e5b3930e3d37a0da73570d2f3368c7b3160c0d2f30b952d50b132af8a3727d89ab2580901226 else 0x6c244e0445e2e80648bc5050262048e47300a0565ed8f60346f5d8ae98260a0c0068580a0c27015b807c906026158e08c030604c2b2a82103cee10cc378bc503c5a1a381a3a2d03cb121b082409e29104f14d80b00b29b02601632490481068e0401093981802127303093987200a0aca00c1820060c1003060ba9e62b81ec8b40d15c753cc0a26ae1d5e606624740ac47cc0483c9bdf72398ae02b28b1eff6cec705e2c44719c65bd0520ccbd4b702a0c67030651f4282f8a37f6c0f90083dbc507c95c01a2901847d2a015c7efbab500764fd1d5a800524460a84613d40171bdf12bb67568e07cc1703e060df4d22a00b883dd40220c2777c2ed22a06e0defe90110884fd1d5a800526915008831e748a802e219d5c0560f91f4ea40c1509ef89ad00884fd0566800c25702b3400611df1500c10c813b1c0f00a44001e0b8625494a83ec3b7532876c0fa40c07c018307cf7fb66a40f0d782d231a682c8a82a1e8185ce3c519b1a206a008183e7be5a8cd9c5ab50287af14281809827bfc7))
def deadl11 : Packing := (183,3,7,8,4,14,0,deadd11)
def deadd12 (i : Nat) : Nat := 0x226c48bbfb654c3991828d28cddfe2ea731865c0891b87a0bb538ea405a3487b1d9bfa906e3a90b8064694310477f6ca947523051a4f7f6c2ed4a3a91828d23bfa90b0351c15a42e0191a577f8ab8d4e631c0c3f7e91b6d4c6b1c0c3811c4dfe2ea51d869c41234a020c7bed54772271048d2408d8efaa71cc89c4123490277f528e4932271048d27e9c5d4a830c011d1fe8c8d4907400c377f8bb6d4e1b04223bd3538ea46e23461177f6da950523047efedb538ea4608191a477f8ba94761a711a3f7f538e644e0191a3f7f5398d032019383963e9c516e8018413c39e9a98d63991b83b6205dfdb2a635a0646093df6ac6b41c816ae0f00efedb52a0493230488077f8ba95061970704f7f531ac732112b842091d02eff176da98d61b04a4140bbec8db6a6358ec1250d06eff1571a98d6830c994a8fd8b08517fb7ae74f70b6c76686125bc5665224e74a34684243d739334f30b2c728322d1e919c15810b0ac056000ffe92a07ffd1940fffb30817ff46102ffe9aa05ffd9340bffa26817ff46502fff4ca05ffd38407ffa6a80fff49501ffe91a03ffd93407ffb2480dffa6503bfecc205ff90340affd32815ff64d01bfec9203ff902406ffd3280ffe4a200ffc92c01ff915803ff247007fe44e00ffc89401fda33803fd445007fc84600
def deadl12 : Packing := (32,2,7,8,4,12,0,deadd12)
def deadd13 (i : Nat) : Nat := 0x22dfc5b6a90e86821a4efdb54c724410d1f7f16a63a18e01069005bf8b6d52351d0d049cf924d00ffd03ffd02ffd01ffa00
def deadl13 : Packing := (4,1,7,5,4,8,0,deadd13)
def deadd14 (i : Nat) : Nat := 0x17e2b6526070604013ff
def deadl14 : Packing := (1,0,7,2,4,0,0,deadd14)
def deadlevels : Nat → Packing
  | 8 => deadl8
  | 9 => deadl9
  | 10 => deadl10
  | 11 => deadl11
  | 12 => deadl12
  | 13 => deadl13
  | 14 => deadl14
  | _ => emptyPacking
def deadindex : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 1 3 0 9 1 4 (hashdeadl9)
  | 10 => lookupWord 17 61 5 13 5 4 (hashdeadl10)
  | 11 => lookupWord 124 434 7 16 8 4 (hashdeadl11)
  | 12 => lookupWord 137 475 8 16 8 4 (hashdeadl12)
  | 13 => lookupWord 26 148 3 13 5 4 (hashdeadl13)
  | 14 => lookupWord 7 47 1 10 2 4 (hashdeadl14)
  | _ => fun _ => none
def dead : Forest := ⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,deadlevels,deadindex,fun _ _ => false, by simp,none,none⟩
set_option maxHeartbeats 0 in
theorem geomdead : graphValid dead (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead8_0 : block dead 8 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead8 : block dead 8 0 2=true := sdead8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_0 : block dead 9 0 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_12 : block dead 9 12 13=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead9 : block dead 9 0 25=true := (@block_merge dead 9 0 12 13 sdead9_0 sdead9_12)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_0 : block dead 10 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_6 : block dead 10 6 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_42 : block dead 10 42 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_78 : block dead 10 78 35=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_113 : block dead 10 113 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_149 : block dead 10 149 7=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead10 : block dead 10 0 156=true := (@block_merge dead 10 0 149 7 (@block_merge dead 10 0 113 36 (@block_merge dead 10 0 78 35 (@block_merge dead 10 0 42 36 (@block_merge dead 10 0 6 36 sdead10_0 sdead10_6) sdead10_42) sdead10_78) sdead10_113) sdead10_149)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_0 : block dead 11 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_4 : block dead 11 4 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_40 : block dead 11 40 15=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_55 : block dead 11 55 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_91 : block dead 11 91 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_127 : block dead 11 127 29=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_156 : block dead 11 156 27=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead11 : block dead 11 0 183=true := (@block_merge dead 11 0 156 27 (@block_merge dead 11 0 127 29 (@block_merge dead 11 0 91 36 (@block_merge dead 11 0 55 36 (@block_merge dead 11 0 40 15 (@block_merge dead 11 0 4 36 sdead11_0 sdead11_4) sdead11_40) sdead11_55) sdead11_91) sdead11_127) sdead11_156)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_0 : block dead 12 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_3 : block dead 12 3 14=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_17 : block dead 12 17 15=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead12 : block dead 12 0 32=true := (@block_merge dead 12 0 17 15 (@block_merge dead 12 0 3 14 sdead12_0 sdead12_3) sdead12_17)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_0 : block dead 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_1 : block dead 13 1 3=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead13 : block dead 13 0 4=true := (@block_merge dead 13 0 1 3 sdead13_0 sdead13_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead14_0 : block dead 14 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead14 : block dead 14 0 1=true := sdead14_0
theorem tablesdead : checkedTables dead 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block dead 0 0 0 = true)
  · exact (rfl : block dead 1 0 0 = true)
  · exact (rfl : block dead 2 0 0 = true)
  · exact (rfl : block dead 3 0 0 = true)
  · exact (rfl : block dead 4 0 0 = true)
  · exact (rfl : block dead 5 0 0 = true)
  · exact (rfl : block dead 6 0 0 = true)
  · exact (rfl : block dead 7 0 0 = true)
  · exact alldead8
  · exact alldead9
  · exact alldead10
  · exact alldead11
  · exact alldead12
  · exact alldead13
  · exact alldead14

theorem dead_start : Impossible graph 14 inputs.toFinset := by
  have noRun := root_index (g:=dead) (before_sound known383 valid383) geomdead tablesdead (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf dead=graph := by decide +kernel
  exact tgt ▸ noRun




theorem low511 : Lower (vars 511) (graphGoal 511) 15 :=
  lower_forest (g:=dead) (i:=0) (hints:=13438755073)
    (before_sound known383 valid383) geomdead tablesdead (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
def bounds511 (q : Nat) := if q = 511 then 15 else boundsBefore known383 q
theorem bounds511_sound (q : Nat) : Lower (vars q) (graphGoal q) (bounds511 q) := by
  unfold bounds511
  split
  next h => exact h ▸ low511
  next => exact before_sound known383 valid383 q


private lemma cutLiveSize {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

private lemma cutBitBin (i : Row) (d : Bool) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]
private lemma cutBitNeg (i : Row) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
theorem inverted_pair {T k t S} (l : Live T k t S) {p n : Row}
    (pp : bit p T = true) (nn : bit n T = false)
    (h : ∀ w∈S, bit p w=true → bit n w=true) : t ≠ 0 := by
  intro eq
  obtain ⟨w,hw,wp,wn⟩ := mono_row_difference l eq pp nn
  exact Bool.noConfusion ((h w hw wp).symm.trans wn)

def Sensitive (T : Sig) (S : Finset Sig) (r : Row) (v : Sig) : Prop :=
  ∃ s, bit r T ≠ bit s T ∧ ∀ u ∈ S, u ≠ v → bit r u = bit s u

def Pivot (T : Sig) (S : Finset Sig) (r s : Row) (v : Sig) : Prop :=
  Sensitive T S r v ∧ Sensitive T S s v

private theorem sensitive_mem (l : Live T k t S) (h : Sensitive T S r v) : v∈S := by
  rcases h with ⟨s,d,h⟩
  obtain ⟨u,hu,hd⟩ := live_row_difference l d
  by_contra z
  exact hd (h _ hu (fun e => z (e ▸ hu)))

private theorem sensitive_unary (az : a∉U) (h : Sensitive T (insert a U) r v) :
    Sensitive T (insert (neg a) U) r (if v=a then neg a else v) := by
  rcases h with ⟨s,hd,hn⟩
  refine ⟨s,hd,?_⟩
  intro u hu ne
  rcases Finset.mem_insert.mp hu with rfl|hu
  · by_cases eq : v=a
    · simp [eq] at ne
    · rw [cutBitNeg,cutBitNeg,hn _ (by simp) (Ne.symm eq)]
  · apply hn _ (Finset.mem_insert_of_mem hu)
    intro e
    subst u
    by_cases eq : v=a
    · exact az (eq ▸ hu)
    · simp [eq] at ne

private theorem sensitive_binary (az : a∉U) (bz : b∉U)
    (h : Sensitive T (insert a (insert b U)) r v) :
    Sensitive T (insert (bin d a b) U) r (if v=a ∨ v=b then bin d a b else v) := by
  rcases h with ⟨s,hd,hn⟩
  refine ⟨s,hd,?_⟩
  intro u hu ne
  rcases Finset.mem_insert.mp hu with rfl|hu
  · by_cases eq : v=a ∨ v=b
    · simp [eq] at ne
    · rw [cutBitBin,cutBitBin,hn a (by simp) (fun e => eq (.inl e.symm)),
        hn b (by simp) (fun e => eq (.inr e.symm))]
  · apply hn _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
    intro e
    subst u
    by_cases eq : v=a ∨ v=b
    · rcases eq with e|e
      · exact az (e ▸ hu)
      · exact bz (e ▸ hu)
    · simp [eq] at ne

private theorem sensitive_pass {g a b : Sig} {d : Bool} (az : a∉U) (ab : a≠b)
    (law : ∀ r, bit r g = (if d then bit r a || bit r b else bit r a && bit r b))
    (l : Live T k t (insert g U)) (h : Sensitive T (insert a (insert b U)) r a) :
    bit r b = !d ∧ bit r g = bit r a := by
  rcases h with ⟨s,hd,hn⟩
  obtain ⟨u,hu,uh⟩ := live_row_difference l hd
  rcases Finset.mem_insert.mp hu with rfl | hu
  · have eq := hn b (by simp) ab.symm
    rw [law,law] at uh
    rw [law,←eq] at *
    all_goals cases d <;> cases a' : bit r a <;> cases b' : bit r b <;>
      cases c' : bit s a <;> simp_all
  · exact (uh (hn _ (by simp [hu]) (fun e => az (e ▸ hu)))).elim

private theorem two_split {U : Finset Sig} {i j a b : Sig} {d : Bool}
    (az : a∉U) (bz : b∉U) (ab : a≠b) (hf : bin d a b ∉ insert a (insert b U)) (l : Live T k t (insert (bin d a b) U))
    (p : Pivot T (insert a (insert b U)) r s i)
    (q : Pivot T (insert a (insert b U)) r s j)
    (hi : bit r i ≠ bit s i) (hj : bit r j ≠ bit s j) (ne : i≠j) :
    ∃ i' j', Pivot T (insert (bin d a b) U) r s i' ∧ Pivot T (insert (bin d a b) U) r s j' ∧
      bit r i' ≠ bit s i' ∧ bit r j' ≠ bit s j' ∧ i'≠j' := by
  let f (v : Sig) := if v=a ∨ v=b then bin d a b else v
  have lift {v} (pv : Pivot T (insert a (insert b U)) r s v) :
       Pivot T (insert (bin d a b) U) r s (f v) :=
    ⟨sensitive_binary az bz pv.1,sensitive_binary az bz pv.2⟩
  have passA {row} (pv : Sensitive T (insert a (insert b U)) row a) :=
    sensitive_pass az ab (d:=d) (fun i => cutBitBin i d a b) l pv
  have passB {row} (pv : Sensitive T (insert a (insert b U)) row b) :
      bit row a = !d ∧ bit row (bin d a b) = bit row b := by
    apply sensitive_pass bz ab.symm (d:=d) (fun i => ?_) l
    · simpa [Finset.insert_comm] using pv
    · rw [cutBitBin]; cases d <;> simp [Bool.and_comm,Bool.or_comm]
  have val {v} (pv : Pivot T (insert a (insert b U)) r s v) :
      bit r (f v)=bit r v ∧ bit s (f v)=bit s v := by
    by_cases eq : v=a ∨ v=b
    · simp only [f,ite_eq_left eq]
      rcases eq with rfl|rfl
      · exact ⟨(passA pv.1).2,(passA pv.2).2⟩
      · exact ⟨(passB pv.1).2,(passB pv.2).2⟩
    · simp [f,eq]
  have fresh {v} (pv : Pivot T (insert a (insert b U)) r s v) (h : ¬(v=a ∨ v=b))
      (fv : v=bin d a b) (hf : bin d a b ∉ insert a (insert b U)) : False := by
    subst v
    obtain ⟨row,hd,ex⟩ := pv.1
    obtain ⟨u,hu,uh⟩ := live_row_difference l hd
    rcases Finset.mem_insert.mp hu with rfl | hu
    · rw [cutBitBin,cutBitBin,ex a (by simp) (fun e => h (.inl e.symm)),
        ex b (by simp) (fun e => h (.inr e.symm))] at uh
      exact uh rfl
    · exact uh (ex _ (by simp [hu]) (fun e => hf (e ▸ (by simp [hu]))))
  refine ⟨f i,f j,lift p,lift q,by rwa [(val p).1,(val p).2],by rwa [(val q).1,(val q).2],?_⟩
  by_cases ei : i=a ∨ i=b <;> by_cases ej : j=a ∨ j=b
  · rcases ei with rfl|rfl <;> rcases ej with rfl|rfl
    · contradiction
    · exact (hj ((passA p.1).1.trans (passA p.2).1.symm)).elim
    · exact (hj ((passB p.1).1.trans (passB p.2).1.symm)).elim
    · contradiction
  · simp only [f,ite_eq_left ei,ite_eq_right ej]
    intro e
    exact fresh q ej e.symm hf
  · simp only [f,ite_eq_right ei,ite_eq_left ej]
    intro e
    exact fresh p ei e hf
  · simpa [f,ei,ej] using ne

theorem tight_no_conflict {T k t S} (l : Live T k t S) (tight : k+1≤S.card+t)
    {r s i j} (p : Pivot T S r s i) (q : Pivot T S r s j)
    (hi : bit r i ≠ bit s i) (hj : bit r j ≠ bit s j) (ne : i≠j) : False := by
  induction l generalizing i j with
  | stop hp =>
    have mem := sensitive_mem (Live.stop hp) p.1
    have mem' := sensitive_mem (Live.stop hp) q.1
    simp only [Finset.mem_singleton] at mem mem'
    exact ne (mem.trans mem'.symm)
  | @unary k t U a ha hf tail ih =>
    have hfU : neg a ∉ U := fun h => hf (by simp [h])
    have size := (cutLiveSize tail).2
    rw [Finset.card_insert_of_notMem hfU] at size
    have az : a ∉ U := by
      intro hal
      rw [Finset.insert_eq_of_mem hal] at tight
      omega
    rw [Finset.card_insert_of_notMem az] at tight
    have next : k+1 ≤ (insert (neg a) U).card+t := by
      rw [Finset.card_insert_of_notMem hfU]; omega
    let f (v : Sig) := if v=a then neg a else v
    have lift {v} (pv : Pivot T (insert a U) r s v) :
        Pivot T (insert (neg a) U) r s (f v) := ⟨sensitive_unary az pv.1,sensitive_unary az pv.2⟩
    have dv {v} (dd : bit r v ≠ bit s v) : bit r (f v) ≠ bit s (f v) := by
      by_cases e : v=a
      · subst v; simpa [f,cutBitNeg] using dd
      · simpa [f,e] using dd
    apply ih next (lift p) (lift q) (dv hi) (dv hj)
    have mi := sensitive_mem (.unary ha hf tail) p.1
    have mj := sensitive_mem (.unary ha hf tail) q.1
    by_cases ei : i=a <;> by_cases ej : j=a
    · exact (ne (ei.trans ej.symm)).elim
    · simp only [f,ite_eq_left ei,ite_eq_right ej]
      exact fun e => hf (e ▸ mj)
    · simp only [f,ite_eq_right ei,ite_eq_left ej]
      exact fun e => hf (e ▸ mi)
    · simpa [f,ei,ej] using ne
  | @binary k t U a b d ha hb ab hf tail ih =>
    have hfU : bin d a b ∉ U := fun h => hf (by simp [h])
    have size := (cutLiveSize tail).2
    rw [Finset.card_insert_of_notMem hfU] at size
    have lim := Finset.card_insert_le (a:=a) (s:=insert b U)
    have bl := Finset.card_insert_le (a:=b) (s:=U)
    have bz : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight lim
      omega
    have az : a∉insert b U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight
      omega
    rw [Finset.card_insert_of_notMem az,Finset.card_insert_of_notMem bz] at tight
    have next : k+1 ≤ (insert (bin d a b) U).card+t := by
      rw [Finset.card_insert_of_notMem hfU]; omega
    obtain ⟨i',j',pi,pj,ii,jj,z⟩ := two_split (fun hm => az (by simp [hm])) bz ab hf tail p q hi hj ne
    exact ih next pi pj ii jj z

theorem tight_no_binate {T k t S} (l : Live T k t S) (tight : k+1≤S.card+t)
    {r s i} (p : Pivot T S r s i) (hi : bit r i = bit s i) (goal : bit r T ≠ bit s T) : False := by
  induction l generalizing i with
  | stop hp =>
    have mi := sensitive_mem (Live.stop hp) p.1
    simp only [Finset.mem_singleton] at mi
    exact goal (mi ▸ hi)
  | @unary k t U a ha hf tail ih =>
    have hfU : neg a ∉ U := fun h => hf (by simp [h])
    have size := (cutLiveSize tail).2
    rw [Finset.card_insert_of_notMem hfU] at size
    have az : a ∉ U := by
      intro hal
      rw [Finset.insert_eq_of_mem hal] at tight
      omega
    rw [Finset.card_insert_of_notMem az] at tight
    have next : k+1 ≤ (insert (neg a) U).card+t := by
      rw [Finset.card_insert_of_notMem hfU]; omega
    let f (v : Sig) := if v=a then neg a else v
    have lift {v} (pv : Pivot T (insert a U) r s v) :
        Pivot T (insert (neg a) U) r s (f v) := ⟨sensitive_unary az pv.1,sensitive_unary az pv.2⟩
    have dv {v} (dd : bit r v = bit s v) : bit r (f v) = bit s (f v) := by
      by_cases e : v=a
      · subst v; simpa [f,cutBitNeg] using dd
      · simpa [f,e] using dd
    exact ih next (lift p) (dv hi)
  | @binary k t U a b d ha hb ab hf tail ih =>
    have hfU : bin d a b ∉ U := fun h => hf (by simp [h])
    have size := (cutLiveSize tail).2
    rw [Finset.card_insert_of_notMem hfU] at size
    have lim := Finset.card_insert_le (a:=a) (s:=insert b U)
    have bl := Finset.card_insert_le (a:=b) (s:=U)
    have bz : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight lim
      omega
    have az : a∉insert b U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight
      omega
    rw [Finset.card_insert_of_notMem az,Finset.card_insert_of_notMem bz] at tight
    have next : k+1 ≤ (insert (bin d a b) U).card+t := by
      rw [Finset.card_insert_of_notMem hfU]; omega
    have nz : a∉U := fun h => az (Finset.mem_insert_of_mem h)
    let f (v : Sig) := if v=a ∨ v=b then bin d a b else v
    have lift : Pivot T (insert (bin d a b) U) r s (f i) :=
      ⟨sensitive_binary nz bz p.1,sensitive_binary nz bz p.2⟩
    apply ih next lift
    by_cases eq : i=a ∨ i=b
    · simp only [f,ite_eq_left eq]
      rcases eq with e|e
      · subst i
        have pick {row} (pv : Sensitive T (insert a (insert b U)) row a) :=
          (sensitive_pass nz ab (d:=d) (fun j => cutBitBin j d a b) tail pv).2
        exact (pick p.1).trans (hi.trans (pick p.2).symm)
      · subst i
        have law (row : Row) : bit row (bin d a b) =
            (if d then bit row b || bit row a else bit row b && bit row a) := by
          rw [cutBitBin]; cases d <;> simp [Bool.and_comm,Bool.or_comm]
        have pick {row} (pv : Sensitive T (insert a (insert b U)) row b) :=
          (sensitive_pass bz ab.symm law tail (by simpa [Finset.insert_comm] using pv)).2
        exact (pick p.1).trans (hi.trans (pick p.2).symm)
    · simpa [f,eq] using hi



structure Six3640 where
  p : Row
  n : Row
  ni : Row
  pi : Row
  nj : Row
  pj : Row

def invRows3640 : List (Row × Row) :=
 [(139,138), (101,100), (401,400), (170,138), (154,146), (325,261), (6,10), (180,52), (298,42), (98,104), (7,261), (120,116), (404,402), (43,42), (403,402), (197,201), (277,276), (320,68), (131,385), (304,50), (13,5), (132,384), (152,146), (273,257), (81,80), (168,138), (160,136), (105,104), (152,400), (66,72), (288,40), (264,258)]

def sixRows3640 : List Six3640 :=
 [⟨160,69,128,101,32,197⟩, ⟨17,10,1,26,16,11⟩, ⟨320,50,256,114,64,306⟩, ⟨24,5,16,13,8,21⟩, ⟨33,272,32,273,1,304⟩, ⟨132,42,128,46,4,170⟩, ⟨66,385,64,387,2,449⟩, ⟨288,138,32,394,256,170⟩, ⟨17,104,1,120,16,105⟩, ⟨12,385,8,389,4,393⟩, ⟨264,50,256,58,8,306⟩, ⟨6,104,4,106,2,108⟩, ⟨12,208,8,212,4,216⟩, ⟨288,65,32,321,256,97⟩, ⟨33,208,32,209,1,240⟩, ⟨3,80,2,81,1,82⟩, ⟨6,385,4,387,2,389⟩, ⟨12,50,8,54,4,58⟩, ⟨24,257,16,265,8,273⟩, ⟨264,69,256,77,8,325⟩, ⟨320,138,256,202,64,394⟩, ⟨3,104,2,105,1,106⟩, ⟨17,138,1,154,16,139⟩, ⟨3,276,2,277,1,278⟩, ⟨6,208,4,210,2,212⟩, ⟨264,208,256,216,8,464⟩, ⟨160,260,128,292,32,388⟩]

def inversion3640 (ws : List Sig) (rn : Row × Row) : Bool :=
  ws.all fun w => !bit rn.1 w || bit rn.2 w

def deviates3640 (p n r s : Row) (w : Sig) : Bool :=
  (bit p w != bit r w) || (bit n w != bit s w)

def pick3640 (ws : List Sig) (p n r s : Row) : Option Sig :=
  match ws.filter (deviates3640 p n r s) with
  | [w] => if (bit p w != bit r w) && (bit n w != bit s w) then some w else none
  | _ => none

def pairCut3640 (p n : Row) (a b : Option Sig) : Bool :=
  match a,b with
  | some u,some v => (bit p u == bit n u) || (bit p v == bit n v) || (u != v)
  | some u,none => bit p u == bit n u
  | none,some v => bit p v == bit n v
  | none,none => false

def sixCut3640 (ws : List Sig) (s : Six3640) : Bool :=
  pairCut3640 s.p s.n (pick3640 ws s.p s.n s.ni s.pi) (pick3640 ws s.p s.n s.nj s.pj)

def shapeCut3640 (k : Nat) (ws : List Sig) : Bool :=
  (k+1 ≤ ws.length || (k == ws.length && invRows3640.any (inversion3640 ws))) &&
    sixRows3640.any (sixCut3640 ws)

def sixValid3640 (T : Sig) (s : Six3640) : Bool :=
  (bit s.p T != bit s.n T) && (bit s.p T != bit s.ni T) &&
  (bit s.n T != bit s.pi T) && (bit s.p T != bit s.nj T) && (bit s.n T != bit s.pj T)

theorem sixRows3640_valid :
    sixRows3640.all (sixValid3640 (chartGoal 511)) = true := by decide +kernel

theorem invRows3640_valid :
    invRows3640.all (fun rn => bit rn.1 (chartGoal 511) && !bit rn.2 (chartGoal 511)) = true := by
  decide +kernel


private theorem pick_single3640 {ws p n r s v}
    (h : pick3640 ws p n r s = some v) : ws.filter (deviates3640 p n r s) = [v] := by
  unfold pick3640 at h
  split at h
  next w eq =>
    split at h
    · cases h
      exact eq
    · contradiction
  next => contradiction

private theorem pick_pivot3640 {ws p n r s v T}
    (h : pick3640 ws p n r s = some v) (dr : bit p T ≠ bit r T) (ds : bit n T ≠ bit s T) :
    Pivot T ws.toFinset p n v := by
  have good := pick_single3640 h
  have agree (u : Sig) (hu : u ∈ ws.toFinset) (ne : u ≠ v) :
      bit p u = bit r u ∧ bit n u = bit s u := by
    have hd : deviates3640 p n r s u = false := by
      cases e : deviates3640 p n r s u with
      | false => rfl
      | true =>
        have a := List.mem_filter.mpr ⟨List.mem_toFinset.mp hu,e⟩
        rw [good] at a
        exact False.elim (ne (List.mem_singleton.mp a))
    simpa [deviates3640] using hd
  exact ⟨⟨r,dr,fun u hu ne => (agree u hu ne).1⟩,
    ⟨s,ds,fun u hu ne => (agree u hu ne).2⟩⟩

private theorem six_impossible3640 {ws k t T s} (run : Live T k t ws.toFinset)
    (tight : k+1 ≤ ws.toFinset.card+t) (valid : sixValid3640 T s = true)
    (cut : sixCut3640 ws s = true) : False := by
  simp [sixValid3640,and_assoc] at valid
  obtain ⟨diff,dr,ds,er,es⟩ := valid
  let pi := pick3640 ws s.p s.n s.ni s.pi
  let pj := pick3640 ws s.p s.n s.nj s.pj
  change pairCut3640 s.p s.n pi pj = true at cut
  cases hi : pi with
  | none =>
    cases hj : pj with
    | none => simp [pairCut3640,hi,hj] at cut
    | some v =>
      have pv := pick_pivot3640 (v:=v) (show pick3640 ws s.p s.n s.nj s.pj = some v from hj) er es
      exact tight_no_binate run tight pv (by simpa [pairCut3640,hi,hj] using cut) diff
  | some u =>
    have pu := pick_pivot3640 (v:=u) (show pick3640 ws s.p s.n s.ni s.pi = some u from hi) dr ds
    by_cases eu : bit s.p u = bit s.n u
    · exact tight_no_binate run tight pu eu diff
    cases hj : pj with
    | none => simp [pairCut3640,hi,hj,eu] at cut
    | some v =>
      have pv := pick_pivot3640 (v:=v) (show pick3640 ws s.p s.n s.nj s.pj = some v from hj) er es
      by_cases ev : bit s.p v = bit s.n v
      · exact tight_no_binate run tight pv ev diff
      exact tight_no_conflict run tight pu pv eu ev (by simpa [pairCut3640,hi,hj,eu,ev] using cut)

theorem shapeCut3640_sound (k : Nat) (ws : List Sig) (nd : ws.Nodup)
    (cut : shapeCut3640 k ws = true) : Impossible (chartGoal 511) k ws.toFinset := by
  intro j t budget run
  simp only [shapeCut3640, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    beq_iff_eq, List.any_eq_true] at cut
  obtain ⟨room,s,hs,why⟩ := cut
  have tight : j+1 ≤ ws.toFinset.card+t := by
    rw [List.toFinset_card_of_nodup nd]
    rcases room with room|⟨eq,p,hp,inv⟩
    · omega
    · have test := List.all_eq_true.mp invRows3640_valid p hp
      have sign : bit p.1 (chartGoal 511) = true ∧ bit p.2 (chartGoal 511) = false := by simpa using test
      have need : t ≠ 0 := by
        intro zeroNot
        obtain ⟨w,hw,h1,h0⟩ := mono_row_difference run zeroNot sign.1 sign.2
        have wi := List.all_eq_true.mp inv w (List.mem_toFinset.mp hw)
        simp [h1,h0] at wi
      omega
  exact six_impossible3640 run tight (List.all_eq_true.mp sixRows3640_valid s hs) why



def orRootSig (a b : Nat) := bin true (inputs.getD a zero) (inputs.getD b zero)

def seededRule (g : Forest) (aug : ColumnInfo → Option (List Sig))
    (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize ((aug ci).getD (vars g.mask)) (chosenSteps bank ops paid d)
      (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem seededRule_sound (g : Forest) (aug : ColumnInfo → Option (List Sig))
    (extra : ∀ ci r, aug ci = some r →
      Slice r (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : seededRule g aug ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold seededRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    cases eq : aug ci with
    | none =>
      simp only [eq,Option.getD_none] at h
      exact materialize_sound (cols ci (g.cols.read_mem e)) h
    | some r =>
      simp only [eq,Option.getD_some] at h
      change ValidPool r (targetOf g) c
      exact materialize_sound (extra ci r eq) h



theorem lower_of_seedRoot {T : Sig} {roots : List Sig} {seed : Sig} {cap : Nat}
    (good : proper T) (prior : Lower roots T (cap+1))
    (essential : ∀ a ∈ roots, Essential T (roots++[seed]) a)
    (blocked : Impossible T cap (roots++[seed]).toFinset) :
    Lower (roots++[seed]) T (cap+1) := by
  intro p bank fuel hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live good fuel hit
  have keep (a : Sig) (ha : a∈roots) : a∈S := by
    obtain ⟨r,s,neq,iso⟩ := essential a ha
    exact raw_required run _ a sub r s neq iso
  by_contra! small
  by_cases hasSeed : seed∈S
  · have eqv : (roots++[seed]).toFinset = S := by
      ext a
      rw [List.mem_toFinset]
      refine ⟨?_,sub a⟩
      intro hm
      rcases List.mem_append.mp hm with h|h
      · exact keep _ h
      · have eqv : a=seed := by simpa only [List.mem_singleton] using h
        exact eqv.symm ▸ hasSeed
    exact blocked k t (by omega) (eqv.symm ▸ run)
  · have supp : supply (roots.map observe) (S.toList.map observe) := by
      intro v hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
      have m := Finset.mem_toList.mp ha
      rcases List.mem_append.mp (sub a m) with h|h
      · exact Or.inl (List.mem_map.mpr ⟨a,h,rfl⟩)
      · have eqv : a=seed := by simpa using h
        exact False.elim (hasSeed (eqv ▸ m))
    have r := list_run run S.toList S.nodup_toList (by simp)
    obtain ⟨q,bank',reach',hit',cut⟩ := contraction (observe_proper good) r
      (roots.map observe) Reach.start supp
    have cost := prior q bank' reach' hit'
    omega

def seedInputsOK (m a b : Nat) (rs : List (Row × Row)) :=
  let roots := vars m ++ [orRootSig a b]
  let xs := (vars m).zip rs
  decide (xs.map Prod.fst = vars m) && checkEssential (chartGoal m) roots xs
theorem seedInputs_ok {m a b rs} (ok : seedInputsOK m a b rs = true) :
    ∀ v ∈ vars m, Essential (chartGoal m) (vars m ++ [orRootSig a b]) v := by
  simp only [seedInputsOK,Bool.and_eq_true,decide_eq_true_eq] at ok
  intro v h
  apply essential_ok ok.2 v
  exact List.mem_toFinset.mpr (ok.1.symm ▸ h)


structure SeedForest extends Forest where
  augment : ColumnInfo → Option (List Sig)
instance : Coe SeedForest Forest := ⟨SeedForest.toForest⟩
def SeedForest.Valid (g : SeedForest) := ∀ ci r, g.augment ci = some r →
  Slice r (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2

def seedNodeVerified (g : SeedForest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let entries := match g.rules3095 with
    | some reader => reader k i
    | none => getPairs data cw depth nr st
  let rules := entries.filterMap (fun (a,b) => seededRule g g.augment ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls,g.cut) ws)


theorem seedNodeVerified_sound (g : SeedForest) (good : g.Valid) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : seedNodeVerified g k i = true) : Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [seedNodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    cases h
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (g.cut_sound _) (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact seededRule_sound g g.augment good cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h



def seedBlock (g : SeedForest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => seedNodeVerified g k (start+n) && seedBlock g k start n

theorem seedBlock_at {g k start n} (h : seedBlock g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    seedNodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [seedBlock,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem seedBlock_merge {g k start a b} (h : seedBlock g k start a=true)
    (h' : seedBlock g k (start+a) b=true) : seedBlock g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [seedBlock,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,seedBlock,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩


def seedCheckedTables (g : SeedForest) (top : Nat) :=
  ∀ k ≤ top, seedBlock g k 0 (g.levels k).1 = true

theorem seedForest_all (g : SeedForest) (good : g.Valid) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : seedCheckedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply seedNodeVerified_sound g good 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact seedBlock_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply seedNodeVerified_sound g good _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact seedBlock_at (rows _ hk) i (by omega) (by omega)


theorem seedRoot_index {g : SeedForest} {top prior k i ws} (good : g.Valid) (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : seedCheckedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact seedForest_all g good top prior low geom blocks _ le i idx.1


def seedContextOf (g : SeedForest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let entries := match g.rules3095 with
    | some reader => reader k i
    | none => getPairs data cw depth nr st
  let rules := entries.filterMap (fun (a,b) => seededRule g g.augment ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls,g.cut)



theorem seedFrom_context (g : SeedForest) (k i : Nat) :
    seedNodeVerified g k i = (prelim (targetOf g) (seedContextOf g k i) &&
      (if k=0 then true else testAll (seedContextOf g k i) (seedContextOf g k i).2.2.1)) := rfl


theorem seedMakeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → seedNodeVerified g k i = true) :
    seedBlock g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [seedBlock,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩


def seedContexts (g : SeedForest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (seedContextOf g k)

def seedHeader (g : SeedForest) (k start n ar : Nat) :=
  (seedContexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)

def seedRowCut (g : SeedForest) (k start n ar lo len : Nat) :=
  let xs := seedContexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))

theorem seedRowCut_at {g k start n ar lo len} (h : seedRowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (seedContexts g k start n)) (seedContexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha


theorem seedRowCut_merge {g k start n ar lo a b}
    (h : seedRowCut g k start n ar lo a=true) (t : seedRowCut g k start n ar (lo+a) b=true) :
    seedRowCut g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact seedRowCut_at h (lo+j) (by omega) (by omega)
  · exact seedRowCut_at t (lo+j) (by omega) (by omega)


theorem seedCutsRun {g k start n ar} (h : seedRowCut g k start n ar 0 ar=true) :
    runBatch k ar (seedContexts g k start n)=true := by
  let xs := seedContexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := seedRowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)


theorem seedCutsBlock {g k start n ar} (hd : seedHeader g k start n ar=true)
    (h : seedRowCut g k start n ar 0 ar=true) : seedBlock g k start n=true := by
  apply seedMakeBlock
  intro i lo hi
  let xs := seedContexts g k start n
  have hm : seedContextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [seedFrom_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (seedCutsRun h)


def seedBoxes (g : SeedForest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => seedRowCut g k start n ar lo num=true
  | d+1 => seedBoxes g k start n ar lo (num/2) d ∧ seedBoxes g k start n ar (lo+num/2) (num-num/2) d

theorem seedBoxesCut {g k start n ar lo num d} (h : seedBoxes g k start n ar lo num d) :
    seedRowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := seedRowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v


def seedCells (g : SeedForest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => seedHeader g k start n ar=true ∧ seedBoxes g k start n ar 0 ar rows
  | d+1 => seedCells g k start (n/2) ar rows d ∧ seedCells g k (start+n/2) (n-n/2) ar rows d

theorem seedCellsBlock {g k start n ar rows d} (h : seedCells g k start n ar rows d) :
    seedBlock g k start n=true := by
  induction d generalizing start n with
  | zero => exact seedCutsBlock h.1 (seedBoxesCut h.2)
  | succ d ih =>
    have v := seedBlock_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v



abbrev SeedItem := ColumnInfo × Nat × Nat × Nat × List Nat
def seedAug (m a b : Nat) (items : List SeedItem) (col : ColumnInfo) :=
  if items.any (fun item => item.1 == col) then some (vars m ++ [orRootSig a b]) else none
def seedItemOK (m a b : Nat) (e : SeedItem) :=
  let (col,q,i,j,sw) := e
  let ms := sw.map swapRows ++ fixRows (m ^^^ col.2.2.1) col.2.1
  checkMap ms (vars m ++ [orRootSig a b]) (chartGoal m)
    (vars q ++ [orRootSig i j]) (chartGoal q) &&
    (movedWord ms (subcube col.1 col.2.1) == one) && properB (chartGoal q)
def seedItemsOK (m a b : Nat) (items : List SeedItem) := items.all (seedItemOK m a b)

theorem seedItem_valid {m a b e L} (ok : seedItemOK m a b e=true)
    (low : Lower (vars e.2.1 ++ [orRootSig e.2.2.1 e.2.2.2.1]) (chartGoal e.2.1) L) :
    Slice (vars m ++ [orRootSig a b]) (chartGoal m) (subcube e.1.1 e.1.2.1) L := by
  obtain ⟨col,q,i,j,sw⟩ := e
  simp only [seedItemOK,Bool.and_eq_true,beq_iff_eq] at ok
  exact slice_correct ok.1.1 ok.1.2 (proper_of _ ok.2) low

def SeedPrior (items : List SeedItem) := ∀ e ∈ items,
  Lower (vars e.2.1 ++ [orRootSig e.2.2.1 e.2.2.2.1]) (chartGoal e.2.1) e.1.2.2.2.2

theorem seedItems_valid {g : Forest} {a b items} (tested : seedItemsOK g.mask a b items = true)
    (lower : SeedPrior items) : (SeedForest.mk g (seedAug g.mask a b items)).Valid := by
  intro ci r eq
  change seedAug g.mask a b items ci = some r at eq
  unfold seedAug at eq
  split at eq
  next hit =>
    obtain ⟨e,em,ec⟩ := List.any_eq_true.mp hit
    have ce := beq_iff_eq.mp ec
    subst ci
    cases eq
    exact seedItem_valid (List.all_eq_true.mp tested e em) (lower e em)
  next => contradiction



abbrev SeedKey := Nat × Nat × Nat × Nat
def SeedKey.Holds (e : SeedKey) := Lower (vars e.1 ++ [orRootSig e.2.1 e.2.2.1]) (chartGoal e.1) e.2.2.2
def SeedLedger (ks : List SeedKey) := ∀ e ∈ ks, e.Holds
theorem seedLedger_empty : SeedLedger [] := by simp [SeedLedger]
theorem seedLedger_cons {e ks} (head : SeedKey.Holds e) (tail : SeedLedger ks) : SeedLedger (e::ks) := by
  intro j hj
  rcases List.mem_cons.mp hj with rfl|hj
  · exact head
  · exact tail _ hj

def seedRefs (xs : List SeedItem) (ls : List SeedKey) :=
  xs.all fun e => ls.contains (e.2.1,e.2.2.1,e.2.2.2.1,e.1.2.2.2.2)
theorem seedRefs_sound {xs ls} (hl : SeedLedger ls) (ok : seedRefs xs ls = true) : SeedPrior xs := by
  intro e he
  have m := List.all_eq_true.mp ok e he
  exact hl _ (List.contains_iff_mem.mp m)

def seedGateOK (g : Forest) (m a b cap : Nat) (rs : List (Row × Row)) (items : List SeedItem)
    (keys : List SeedKey) (prior : Nat → Nat) :=
  graphValid g prior &&
  seedItemsOK m a b items && seedRefs items keys &&
  seedInputsOK m a b rs && properB (chartGoal m) &&
  indexedRoot g cap 0 (vars m ++ [orRootSig a b])

theorem seedRootClosed {g : Forest} {a b cap rs items keys prior}
    (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (parents : SeedLedger keys)
    (geo : seedGateOK g g.mask a b cap rs items keys prior = true)
    (t : seedCheckedTables ⟨g,seedAug g.mask a b items⟩ cap) :
    Impossible (chartGoal g.mask) cap (vars g.mask ++ [orRootSig a b]).toFinset := by
  simp only [seedGateOK,Bool.and_eq_true] at geo
  apply seedRoot_index (g:=⟨g,seedAug g.mask a b items⟩)
    (seedItems_valid geo.1.1.1.1.2 (seedRefs_sound parents geo.1.1.1.2))
    low geo.1.1.1.1.1 t (Nat.le_refl _) geo.2

theorem seedRootLower {g : Forest} {a b cap rs items keys prior}
    (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ordinary : Lower (vars g.mask) (chartGoal g.mask) (cap+1))
    (parents : SeedLedger keys)
    (geo : seedGateOK g g.mask a b cap rs items keys prior = true)
    (t : seedCheckedTables ⟨g,seedAug g.mask a b items⟩ cap) :
    Lower (vars g.mask ++ [orRootSig a b]) (chartGoal g.mask) (cap+1) := by
  have checks := geo
  simp only [seedGateOK,Bool.and_eq_true] at checks
  apply lower_of_seedRoot (proper_of _ checks.1.2) ordinary (seedInputs_ok checks.1.1.2)
  exact seedRootClosed low parents geo t


def sampleSeed15 := g15samples
def autosSeed15 : Array (List Nat) := #[[],[33,48]]
namespace S15_0_1
def cols : IndexTree ColumnInfo := (.leaf [])
def seeds : List SeedItem := []
def n3 (i : Nat) : Nat := 0x7d10

def lv : Nat → Packing
  | 3 => (1,1,0,0,0,0,0,n3)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g : SeedForest := ⟨⟨15,3,fun j => sampleSeed15[j]?.getD (0,0),cols,autosSeed15,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 15 0 1 seeds⟩
def rows : List (Row × Row) := [(2,3),(1,3),(2,6),(4,12)]
end S15_0_1
namespace S15_1_2
def cols : IndexTree ColumnInfo := (.leaf [])
def seeds : List SeedItem := []
def n3 (i : Nat) : Nat := 0x7d21

def lv : Nat → Packing
  | 3 => (1,1,0,0,0,0,0,n3)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g : SeedForest := ⟨⟨15,3,fun j => sampleSeed15[j]?.getD (0,0),cols,autosSeed15,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 15 1 2 seeds⟩
def rows : List (Row × Row) := [(2,3),(4,6),(2,6),(4,12)]
end S15_1_2
def sampleSeed31 := g31samples
def autosSeed31 : Array (List Nat) := #[[],[50,65],[66,16],[64,48,32,16],[67,32],[16,64,49,32],[33,48],[33,32,65,48],[50,33,16,64],[49,64]]
namespace S31_0_1
def cols : IndexTree ColumnInfo := (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)])
def seeds : List SeedItem := [((4,0,27,0,4),15,0,1,[66,16]),((8,0,23,0,4),15,1,2,[64,48,32,16]),((16,0,15,0,4),15,0,1,[])]
def n5 (i : Nat) : Nat := 0x1008001db920bf2aa217d35442fa4a887e48110

def n6 (i : Nat) : Nat := 0x1103fd10

def x6 (i : Nat) : Nat := 0x1919280030000f2000d340000000000cb

def lv : Nat → Packing
  | 5 => (4,2,2,0,0,5,0,n5)
  | 6 => (1,1,2,0,0,0,0,n6)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 15 0 10 2 4 x6
  | _ => fun _ => none
def g : SeedForest := ⟨⟨31,6,fun j => sampleSeed31[j]?.getD (0,0),cols,autosSeed31,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 31 0 1 seeds⟩
def rows : List (Row × Row) := [(2,3),(1,3),(2,6),(4,12),(1,17)]
end S31_0_1
def sampleSeed47 := g47samples
def autosSeed47 : Array (List Nat) := #[[],[83,32]]
namespace S47_0_1
def cols : IndexTree ColumnInfo := (.leaf [])
def seeds : List SeedItem := []
def n4 (i : Nat) : Nat := 0xfd10

def lv : Nat → Packing
  | 4 => (1,1,0,0,0,0,0,n4)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g : SeedForest := ⟨⟨47,4,fun j => sampleSeed47[j]?.getD (0,0),cols,autosSeed47,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 47 0 1 seeds⟩
def rows : List (Row × Row) := [(2,3),(1,3),(2,6),(4,12),(1,33)]
end S47_0_1
namespace S47_0_5
def cols : IndexTree ColumnInfo := (.leaf [])
def seeds : List SeedItem := []
def n4 (i : Nat) : Nat := 0xfd40

def lv : Nat → Packing
  | 4 => (1,1,0,0,0,0,0,n4)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g : SeedForest := ⟨⟨47,4,fun j => sampleSeed47[j]?.getD (0,0),cols,autosSeed47,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 47 0 5 seeds⟩
def rows : List (Row × Row) := [(32,33),(1,3),(2,6),(4,12),(1,33)]
end S47_0_5
def sampleSeed55 := g55samples
def autosSeed55 : Array (List Nat) := #[[],[84]]
namespace S55_0_1
def cols : IndexTree ColumnInfo := (.leaf [])
def seeds : List SeedItem := []
def n4 (i : Nat) : Nat := 0xfd10

def lv : Nat → Packing
  | 4 => (1,1,0,0,0,0,0,n4)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g : SeedForest := ⟨⟨55,4,fun j => sampleSeed55[j]?.getD (0,0),cols,autosSeed55,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 55 0 1 seeds⟩
def rows : List (Row × Row) := [(2,3),(1,3),(2,6),(1,17),(1,33)]
end S55_0_1
namespace S55_0_4
def cols : IndexTree ColumnInfo := (.leaf [])
def seeds : List SeedItem := []
def n4 (i : Nat) : Nat := 0xfd30

def lv : Nat → Packing
  | 4 => (1,1,0,0,0,0,0,n4)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g : SeedForest := ⟨⟨55,4,fun j => sampleSeed55[j]?.getD (0,0),cols,autosSeed55,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 55 0 4 seeds⟩
def rows : List (Row × Row) := [(16,17),(1,3),(2,6),(1,17),(1,33)]
end S55_0_4
namespace S55_1_2
def cols : IndexTree ColumnInfo := (.leaf [])
def seeds : List SeedItem := []
def n4 (i : Nat) : Nat := 0xfd21

def lv : Nat → Packing
  | 4 => (1,1,0,0,0,0,0,n4)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g : SeedForest := ⟨⟨55,4,fun j => sampleSeed55[j]?.getD (0,0),cols,autosSeed55,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 55 1 2 seeds⟩
def rows : List (Row × Row) := [(2,3),(4,6),(2,6),(1,17),(1,33)]
end S55_1_2
def sampleSeed63 := g63samples
def autosSeed63 : Array (List Nat) := #[[],[50,65]]
namespace S63_0_1
def cols : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def seeds : List SeedItem := [((32,0,31,0,7),31,0,1,[])]
def n7 (i : Nat) : Nat := 0x3fd10

def lv : Nat → Packing
  | 7 => (1,1,0,0,0,0,0,n7)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g : SeedForest := ⟨⟨63,7,fun j => sampleSeed63[j]?.getD (0,0),cols,autosSeed63,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 63 0 1 seeds⟩
def rows : List (Row × Row) := [(2,3),(1,3),(2,6),(4,12),(1,17),(1,33)]
end S63_0_1
namespace S63_0_5
def cols : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def seeds : List SeedItem := []
def n7 (i : Nat) : Nat := 0x3fd50

def lv : Nat → Packing
  | 7 => (1,1,0,0,0,0,0,n7)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g : SeedForest := ⟨⟨63,7,fun j => sampleSeed63[j]?.getD (0,0),cols,autosSeed63,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 63 0 5 seeds⟩
def rows : List (Row × Row) := [(32,33),(1,3),(2,6),(4,12),(1,17),(1,33)]
end S63_0_5
namespace S63_1_2
def cols : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def seeds : List SeedItem := [((32,0,31,0,7),31,0,1,[67,32])]
def n7 (i : Nat) : Nat := 0x3fd21

def lv : Nat → Packing
  | 7 => (1,1,0,0,0,0,0,n7)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g : SeedForest := ⟨⟨63,7,fun j => sampleSeed63[j]?.getD (0,0),cols,autosSeed63,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 63 1 2 seeds⟩
def rows : List (Row × Row) := [(2,3),(4,6),(2,6),(4,12),(1,17),(1,33)]
end S63_1_2
namespace S63_2_3
def cols : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def seeds : List SeedItem := [((32,0,31,0,7),31,0,1,[33,48])]
def n7 (i : Nat) : Nat := 0x3fd32

def lv : Nat → Packing
  | 7 => (1,1,0,0,0,0,0,n7)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g : SeedForest := ⟨⟨63,7,fun j => sampleSeed63[j]?.getD (0,0),cols,autosSeed63,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 63 2 3 seeds⟩
def rows : List (Row × Row) := [(2,3),(1,3),(8,12),(4,12),(1,17),(1,33)]
end S63_2_3
def sampleSeed111 := g111samples
def autosSeed111 : Array (List Nat) := #[[],[83,32]]
namespace S111_0_1
def cols : IndexTree ColumnInfo := (.leaf [(1,32,78,0,4),(96,0,15,0,4)])
def seeds : List SeedItem := [((96,0,15,0,4),15,0,1,[])]
def n5 (i : Nat) : Nat := 0x22de54110

def n6 (i : Nat) : Nat := 0x45fd10

def x6 (i : Nat) : Nat := 0x1a

def lv : Nat → Packing
  | 5 => (1,2,1,0,0,0,0,n5)
  | 6 => (1,1,1,0,0,0,0,n6)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 5 0 1 x6
  | _ => fun _ => none
def g : SeedForest := ⟨⟨111,6,fun j => sampleSeed111[j]?.getD (0,0),cols,autosSeed111,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 111 0 1 seeds⟩
def rows : List (Row × Row) := [(2,3),(1,3),(2,6),(4,12),(1,33),(2,66)]
end S111_0_1
namespace S111_0_5
def cols : IndexTree ColumnInfo := (.leaf [])
def seeds : List SeedItem := []
def n6 (i : Nat) : Nat := 0x1fd40

def lv : Nat → Packing
  | 6 => (1,1,0,0,0,0,0,n6)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g : SeedForest := ⟨⟨111,6,fun j => sampleSeed111[j]?.getD (0,0),cols,autosSeed111,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 111 0 5 seeds⟩
def rows : List (Row × Row) := [(32,33),(1,3),(2,6),(4,12),(1,33),(2,66)]
end S111_0_5
namespace S111_1_6
def cols : IndexTree ColumnInfo := (.leaf [])
def seeds : List SeedItem := []
def n6 (i : Nat) : Nat := 0x1fd51

def lv : Nat → Packing
  | 6 => (1,1,0,0,0,0,0,n6)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g : SeedForest := ⟨⟨111,6,fun j => sampleSeed111[j]?.getD (0,0),cols,autosSeed111,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 111 1 6 seeds⟩
def rows : List (Row × Row) := [(2,3),(64,66),(2,6),(4,12),(1,33),(2,66)]
end S111_1_6
def sampleSeed119 := g119samples
def autosSeed119 : Array (List Nat) := #[[],[84],[98],[84,98],[101,66,16],[82,98,66,16],[100,66,82,16],[100,82,16]]
namespace S119_0_1
def cols : IndexTree ColumnInfo := (.leaf [])
def seeds : List SeedItem := []
def n5 (i : Nat) : Nat := 0x1fd10

def lv : Nat → Packing
  | 5 => (1,1,0,0,0,0,0,n5)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g : SeedForest := ⟨⟨119,5,fun j => sampleSeed119[j]?.getD (0,0),cols,autosSeed119,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 119 0 1 seeds⟩
def rows : List (Row × Row) := [(2,3),(1,3),(2,6),(1,17),(1,33),(2,66)]
end S119_0_1
namespace S119_0_4
def cols : IndexTree ColumnInfo := (.leaf [])
def seeds : List SeedItem := []
def n5 (i : Nat) : Nat := 0x1fd30

def lv : Nat → Packing
  | 5 => (1,1,0,0,0,0,0,n5)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g : SeedForest := ⟨⟨119,5,fun j => sampleSeed119[j]?.getD (0,0),cols,autosSeed119,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 119 0 4 seeds⟩
def rows : List (Row × Row) := [(16,17),(1,3),(2,6),(1,17),(1,33),(2,66)]
end S119_0_4
def sampleSeed189 := g189samples
def autosSeed189 : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32],[82,48],[66,112,82,48],[80,48,50,114,64],[83,114,64],[116,50,80],[114,32,66,50,80],[82,48,66,112],[66,112]]
namespace S189_0_4
def cols : IndexTree ColumnInfo := (.leaf [(8,0,181,0,5),(12,0,177,0,4),(17,0,172,0,4)])
def seeds : List SeedItem := [((8,0,181,0,5),47,0,5,[114,81,98,50,65]),((12,0,177,0,4),15,0,1,[115,99,82,64,16])]
def n6 (i : Nat) : Nat := 0x2100c920bf58930bf58530fe48130

def n7 (i : Nat) : Nat := 0x83fd30

def x7 (i : Nat) : Nat := 0x66ac1002dc1035200000f76

def lv : Nat → Packing
  | 6 => (3,2,2,0,0,5,0,n6)
  | 7 => (1,1,2,0,0,0,0,n7)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 2 10 1 10 2 4 x7
  | _ => fun _ => none
def g : SeedForest := ⟨⟨189,7,fun j => sampleSeed189[j]?.getD (0,0),cols,autosSeed189,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 189 0 4 seeds⟩
def rows : List (Row × Row) := [(16,17),(8,12),(4,12),(1,17),(1,33),(4,132)]
end S189_0_4
def sampleSeed127 := g127samples
def autosSeed127 : Array (List Nat) := #[[],[101,66,16]]
namespace S127_0_1
def cols : IndexTree ColumnInfo := (.leaf [(32,0,95,0,8)])
def seeds : List SeedItem := [((32,0,95,0,8),63,0,1,[101,66,16])]
def n8 (i : Nat) : Nat := 0x7fd10

def lv : Nat → Packing
  | 8 => (1,1,0,0,0,0,0,n8)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g : SeedForest := ⟨⟨127,8,fun j => sampleSeed127[j]?.getD (0,0),cols,autosSeed127,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 127 0 1 seeds⟩
def rows : List (Row × Row) := [(2,3),(1,3),(2,6),(4,12),(1,17),(1,33),(2,66)]
end S127_0_1
namespace S127_0_4
def cols : IndexTree ColumnInfo := (.leaf [(32,0,95,0,8)])
def seeds : List SeedItem := [((32,0,95,0,8),63,1,2,[101,66,16])]
def n8 (i : Nat) : Nat := 0x7fd40

def lv : Nat → Packing
  | 8 => (1,1,0,0,0,0,0,n8)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g : SeedForest := ⟨⟨127,8,fun j => sampleSeed127[j]?.getD (0,0),cols,autosSeed127,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 127 0 4 seeds⟩
def rows : List (Row × Row) := [(16,17),(1,3),(2,6),(4,12),(1,17),(1,33),(2,66)]
end S127_0_4
namespace S127_0_5
def cols : IndexTree ColumnInfo := (.leaf [(32,0,95,0,8)])
def seeds : List SeedItem := []
def n8 (i : Nat) : Nat := 0x7fd50

def lv : Nat → Packing
  | 8 => (1,1,0,0,0,0,0,n8)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g : SeedForest := ⟨⟨127,8,fun j => sampleSeed127[j]?.getD (0,0),cols,autosSeed127,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 127 0 5 seeds⟩
def rows : List (Row × Row) := [(32,33),(1,3),(2,6),(4,12),(1,17),(1,33),(2,66)]
end S127_0_5
namespace S127_2_3
def cols : IndexTree ColumnInfo := (.leaf [(32,0,95,0,8)])
def seeds : List SeedItem := [((32,0,95,0,8),63,1,2,[101,50,33,16,64])]
def n8 (i : Nat) : Nat := 0x7fd32

def lv : Nat → Packing
  | 8 => (1,1,0,0,0,0,0,n8)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g : SeedForest := ⟨⟨127,8,fun j => sampleSeed127[j]?.getD (0,0),cols,autosSeed127,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 127 2 3 seeds⟩
def rows : List (Row × Row) := [(2,3),(1,3),(8,12),(4,12),(1,17),(1,33),(2,66)]
end S127_2_3
def sampleSeed191 := g191samples
def autosSeed191 : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
namespace S191_0_1
def cols : IndexTree ColumnInfo := (.fork 19 (.fork 9 (.fork 4 (.leaf [(0,0,191,0,11),(2,0,189,0,8),(8,0,183,0,8),(16,0,175,0,8)]) (.fork 2 (.leaf [(32,0,159,0,8),(128,0,63,0,8)]) (.leaf [(1,0,190,0,7),(4,0,187,0,7),(24,0,167,0,7)]))) (.fork 5 (.fork 2 (.leaf [(160,0,31,0,7),(0,8,163,20,6)]) (.leaf [(0,16,166,9,6),(0,32,30,129,6),(0,128,27,36,6)])) (.fork 2 (.leaf [(1,16,166,8,5),(1,32,30,128,5)]) (.leaf [(3,0,188,0,5),(4,8,163,16,5),(4,128,27,32,5)])))) (.fork 9 (.fork 4 (.leaf [(6,0,185,0,5),(8,16,166,1,5),(10,0,181,0,5),(12,0,179,0,5)]) (.fork 2 (.leaf [(16,8,163,4,5),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(136,0,55,0,5),(9,16,166,0,4)]))) (.fork 5 (.fork 2 (.leaf [(14,0,177,0,4),(19,0,172,0,4)]) (.leaf [(20,8,163,0,4),(25,0,166,0,4),(28,0,163,0,4)])) (.fork 2 (.leaf [(35,0,156,0,4),(36,128,27,0,4)]) (.leaf [(56,0,135,0,4),(129,32,30,0,4),(134,0,57,0,4)])))))
def seeds : List SeedItem := [((8,0,183,0,8),63,0,1,[115,84,99]),((16,0,175,0,8),63,1,2,[116,100,83,32]),((32,0,159,0,8),63,1,2,[117,101,67,32]),((128,0,63,0,8),63,0,1,[]),((4,0,187,0,7),111,1,6,[117,80,66,96,16]),((24,0,167,0,7),31,0,1,[115,67,100,83]),((160,0,31,0,7),31,0,1,[]),((12,0,179,0,5),55,0,4,[114,81,98,50,65]),((40,0,151,0,5),47,0,1,[115,99,83,67]),((48,0,143,0,5),55,1,2,[117,101,67,32]),((136,0,55,0,5),55,0,1,[]),((28,0,163,0,4),15,0,1,[115,50,98,83,66,16]),((56,0,135,0,4),15,0,1,[115,99,83,67])]
def n5 (i : Nat) : Nat := 0x15c856c985094148110

def n6 (i : Nat) : Nat := 0xe081009070800e8640a8810000942070208f7f6f5f5a4a2f2a2515050087d46a9961d20442da8a755142481108fc2a15950520443da14259d4148110de826142505204427715a2614148110e6c5208750520443da14221d4148110a7c46a8821d204435b1675248148110d6c4dd49205204437a1525248148110

def x6 (i : Nat) : Nat := 0x14

def n7 (i : Nat) : Nat := 0xf00200000000208038443a102040210001e0040038406080007040f03806804840910241c207848841c402041d103a10001d08188a044c1840e204440841c081c100000001c44080e204400000000000051542ced38cd933cc52ecb129c7510c3906c1101bfcf7bd4edb98e3b84d9b0cb6abca7a6c98a3084a087f9e0759a4619544d9183e8f0398dc348c825864168501183c0c82807814028015bd490a27744277a934426e8857d4668849d108fe8cd1093a219f519a21274423fa5243aa88847f4a48758d108fe9490ea9a213dd39a2142442b792eb22848856f25d5450910edaa12cea0a215f56909d414433eab013a828876d59d41501109dea4d10982217f119a21204427ea33442408847fa658748110ef4a926e902215f89755120442fd2b2a1240887ea5914248110fd4aa284902217f15950520443f6290a0a408877c59d4148110ff0a928290221fb14250520443f5284a0a40885fc2614148110ef843a8290221de93748520443fc26290a40887ec5054048110cfd4410e902219f94821d20443bd28443a40885fc5248148110bdaa490290221df13720520443fc28440a408847d26127845108dea4d109ba211f519a2127442fc25240282884fa4a48050510fd0a1282902217b149205204423eb133b820884eda654804110cdb3ba9008221ab6665201044366caaa4020886e58cd4804110dd311290082219b5675201044336a6ea40208866d09d4804110

def x7 (i : Nat) : Nat := 0x207001480000024c000009970644a63057ec00f1890f4880f09caf680000000001d1

def n8 (i : Nat) : Nat := (if i < 1 then 0x92080110dfe2251d10bfd5851d10dfd5751d10dfd6251d10dfd5251d10bfe884dd10bfd684dd10bfd584dd10dfd674dd10dfd574dd10dfd624dd10dfd524dd10dfe8849d10bfe8849d10bfd4849d10dfd3849d10bfd3849d10dfd4749d10dfd3749d10dfd6349d10dfd5349d10bfe8855110bfe8858d10bfe8854d10bfe8850910bfd5850910fbd6450910fbd5450910bfe884c910bfd684c910bfd584c910fdd634c910ff62250510bfd5850510ff56750510dfd6750510ff55750510dfd5750510ff52750510ff56250510ff55250510fbd4250510ff55150510bfe884c510dfe774c510bfd684c510bfd584c510dfd674c510dfd574c510dfd274c510fdd324c510ff5514c510dfe7748510dfd4748510dfd3748510ff53148510bfd5850110dfd6750110dfd5750110dfd2750110fbd5450110ff55150110bfe884c110dfe774c110bfd684c110bfd584c110dfd674c110dfd574c110dfd274c110fdd634c110fdd534c110ff5514c110fdd314c110ffa8848110bfe8848110ffa7748110dfe7748110ff94848110bfd4848110ff93848110bfd3848110ff94748110dfd4748110ff93748110dfd3748110dfd2748110ff95448110ff96348110ff95348110ff94248110fed4248110ff93248110ff98148110bfd8148110ff94148110ff54148110ff93148110ff92148110ff94048110ff93048110ff88748110dfc8748110ff48148110bfd3809d10dfd5409d10bfd3808110dbe449dd10dde339dd10dee229dd109fd489dd109fd389dd109fd289dd10df5189dd10f3e5591110ede668cd10f5e558cd10fae4488910fce33889109fc7888910dec7888910bf80888910fe80888910df67784510fb64484510fd63384510fe62284510df54784510df53784510df52784510df42784510dfa7780110fba4480110fda3380110fea2280110ff21180110bf92880110df94780110df93780110df92780110ff14180110df827801109fe8851d10cfe6651d10d7e5551d10dee2251d109fd5851d109fe884dd10cfe664dd10d7e554dd10dee224dd109fd684dd109fd584dd109fe8849d10dde3349d109fd3849d109fc87551109fc8758d109fc8754d109fc87509109fc874c910bf68850510df67750510ef66650510f765550510fe62250510bf55850510df56750510fb54250510df42750510ff08050510bf88050510bf8804c5109fc8748510bf88048510fb54150110bfa8848110dfa7748110fba4448110fda3348110fea2248110ff211481109fd8748110df93748110fe94248110ff14148110fe92148110df88748110fe82748110dec2748110ff08148110dbe4409d10dde3309d109fd4809d109fd3809d10ded2709d10fe92008110df67704110fb64404110fd63304110fe62204110bf54804110df53704110df42704110bb54804110 else 0x21c2828307468708083a191028342108604880e8781640505841008543e209842006121c3a2040c20b0e88161d448e041b0a8d1308038e10144c2050808444b081846108911102013141c262440510144050614404141a10283020c83841a0508300f10801c244c201c102214284040386160508141012241e101a143030708060e0e8913031226062818606181843b0312241e1d81920208121206203054502430406070501860f1089130214083020c04284810a0e10102c3a2440443834107040e0e891303140c3030a101c207a105810d8a041d1226100a0092100f108d130814203080a14102420509081074206838a0f811018202838404884089101d070d1011408d100a008c3a10707448803c046880881e0244086021038445010a200e20720c4070a04204085060e0e8d048112042830e8a028812042810a042820c1c19010591041e007801e0070a071086c811c4874782c48747c0080000001a210501c3a5e00424110781c3a5e0078010001c00a203c00c043c00800000183c00a203c00a0c3c00874362e007801e0070a070a0c1a0c0d8543c5840610184061007448789858407860d0602c141009f0313884f00288c485c70903040464848745090e881b081087480d810843a4e007801818606181843a061206c88744c206870406c6010f07460000240f0e8709010804061d0d93801e00603c01407802038502106830160ac4e20c070f091010707402882204385c10883c812800810c0780280f0041d0d882c1e10000000000000c18bec57628d12f88c44061b10c1859c27211d077830416e09b03680b3fd9facfc87d8be8df06f5a7a1bcb1e3cf107813bd1dccecf75c3a85d14e7372e38cdc4ae056f7375db6eda96c4b5c9ab6d4469b34a1a34d0366d330d958c9563ab15587cc2760cb02d7fabe65e7aee1730b815b52d4d68ab375902c255e4adb5592a494f6a6d52fa921474a2350aa7f93ce9d04dca6893049624a124d123a8fd46a23191708a1449a1f10ca857424a11106c8163ff9fc4fb47c33da9e9cf3278b3b11d50e8c7383951c04dc26c13599ab8d526a434f9a68cd065a3141868c1860730117f4bde5e12e99714b6e5b22d696a0b465952c395e4ad655d2a794e0a5451c28713b89784ae25012488d24491f98f9478a39c1c28db868a31c1870c005e42e416b0ab451a26d126892048623e10a881c3bc1d00e106ac3281860bc04f424c118077838415e0aa052825c10006902900ec06c031016009c04401d00c004c01c000dfe229dd10dfd379dd10dfd279dd10dfd549dd10dfd639dd10dfd539dd10dfd429dd10dfd329dd10dfc289dd10dfd3780110dfd2780110ff)

def x8 (i : Nat) : Nat := 0x9f7000705000104e570007ce000000720c2f00de3a86a101ef8613247663a75e08a4071224a24600043900087a00072300000000076e162242000a1800089900000000000021c82e96400071a63200000000095fe1b4f6000254d2c751000000d3342480a000919c3156981da9a000e678e8b70045000f71f11000c30000000766402a5960b8218d00000002655d9000516203a52a6d70f000856206cda153f14d5517400051f000b5ba1e66fd49343e2b000427a5a515000000000000207c0c2600009000222044620503062044014061201a

def n9 (i : Nat) : Nat := 0x8582070681211d38908c08844c4039e16081e04188474e103a207118908203c4c40c1c6438742420c0e3502222012107070f1811210908387100ec484142a0458422420c103a2071c100189083098844c41004207460e23020312106100107818988309088083908e9848441c8474a0e0d80430311123a88189081c0c4840e041e262300b13100c024068988c0812838e874484141e04462420b800f0313105060e891d0828083c0c4c4160884044488741ce0c1ac749a74cd495f24a2ec207c6ed9c0b6c66ec497aac0516959149e438e6a8be9582563f8688a40ee12806800ffcee887fe22443ff00221ff51d10ffa6e887fd27443feaa221ff58d10ffaa6887fd42443fe99221ff50510ffa62887fd21443fea0221ff4c110ffa40887fc27443fe102217f9dd10f7c88887de33443f711221fd84510ff400885fd47442fe9ba217f49d10fea82887f920442fe13a21fd04110

def x9 (i : Nat) : Nat := 0x389b0000000453800000000000000000000000054540000003dc54080000000195500000b1d560000000000011910a86188000923c0000003878000000086028290001492000018f0003d95000253884d84430001d5b435b332000000000000000000000247800000000480002165000350ae5c11d00001554b2ea871000354f00000004adc000e1af440a3058a6954109f0000132f23400072955d3b4f4000b6d631ed46c59644d400072465a9a4edc0662cc000f5d1593000000026280000001911f174000773000033394c42c4ac2e000000085af99f0000000000180ac70a49802f1d694670d923504000d22800000000000000abc5a1c00070f80008091126a21400041e40003057887972c40cc2b75be61b4000c606182051612382a607b2ef2c19d6f3495569aa9615a9d97c631c6965a2918118015fe72507c157242260d8000117806c84a8989244e8b0f8cb44d4508000131f9b90000000e49400000019c00003f9500005a151f400000000005434000e158000f226834a29c00064a488e11fb394c143290549ed0285c400000000000003dd78677bb800000005585b760003d1aa54c0000000000a4c2c37650c000d0974a304dcb330001f9a943387a00021c73464000d748483742602d86b1d7366b61cf95801ba75770a0b6c8c585eddd0e255e55246ac4889050000a32000000035c1f0e088675dc000fd2c000000000097100000000f870000000c4fc00072ec00045b893ce72a5a740ac0006558000756669500000000000000000000092f7803c527c99e3458a40002cc6840c82c05331622108d0181c80000003dc8466d1bbc02ed4496f40ac675410f05bc00036440000002579c2e4d07951849411a1c8c80368470000000862cda300000a290094230000186b4700001500198ce42da595ee061d258104b652dae206bd8e1015c00b420b1f758f09a60ec9886087934f04d4d050aa16615e094df6c35b8f57b0314da9dd6c21000051dcd3a66695cd00035c3f1c31aaee59457000157cf5ff948775000066c48af9a5296d5640575d4a3a31e61271600e48270001d1400000002e5d9a874bfb31532c17d94c6c3c52d349c8402564f309506c5f8947c67a14aa44207335e8000000129ae34a9a48d04000000000045b2151fdba09d5241828245dfbf159d9cea56b1d190cb84c46d9187000144fe0f44ab242d972941601d00004c024f3c001418e043c000000430021404c20042400860c11452551c32081c10470000000c13c31400410c10410c700054248014f0930017400c600320e0010410c200d18400000008c74000010010a0142c20413c14c0000080

def n10 (i : Nat) : Nat := 0x22440ffd10

def x10 (i : Nat) : Nat := 0x9680000078595eefd9b2e40000000ababd0d845dbc16001e6c005aa000ae80000084a7cb4e42700000000000a6a6429080000122a1d8007738cd58fb88502c15ea29a5ca2edf00000049b51000e2f80e89d14859e8000623f5a000000bc318240032010060

def lv : Nat → Packing
  | 5 => (1,6,6,0,0,0,0,n5)
  | 6 => (12,5,6,0,0,8,0,n6)
  | 7 => (59,4,6,0,0,10,0,n7)
  | 8 => (216,3,6,0,0,13,0,n8)
  | 9 => (32,2,6,0,0,11,0,n9)
  | 10 => (1,1,6,0,0,0,0,n10)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 6 0 2 x6
  | 7 => lookupWord 5 27 2 10 4 2 x7
  | 8 => lookupWord 29 131 4 12 6 2 x8
  | 9 => lookupWord 118 498 6 14 8 2 x9
  | 10 => lookupWord 15 69 4 11 5 2 x10
  | _ => fun _ => none
def g : SeedForest := ⟨⟨191,10,fun j => sampleSeed191[j]?.getD (0,0),cols,autosSeed191,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 191 0 1 seeds⟩
def rows : List (Row × Row) := [(2,3),(1,3),(2,6),(4,12),(1,17),(1,33),(4,132)]
end S191_0_1
namespace S191_0_4
def cols : IndexTree ColumnInfo := (.fork 19 (.fork 9 (.fork 4 (.leaf [(0,0,191,0,11),(2,0,189,0,8),(8,0,183,0,8),(16,0,175,0,8)]) (.fork 2 (.leaf [(32,0,159,0,8),(128,0,63,0,8)]) (.leaf [(1,0,190,0,7),(4,0,187,0,7),(24,0,167,0,7)]))) (.fork 5 (.fork 2 (.leaf [(160,0,31,0,7),(0,8,163,20,6)]) (.leaf [(0,16,166,9,6),(0,32,30,129,6),(0,128,27,36,6)])) (.fork 2 (.leaf [(1,16,166,8,5),(1,32,30,128,5)]) (.leaf [(4,8,163,16,5),(4,128,27,32,5),(6,0,185,0,5)])))) (.fork 10 (.fork 5 (.fork 2 (.leaf [(8,16,166,1,5),(10,0,181,0,5)]) (.leaf [(12,0,179,0,5),(16,8,163,4,5),(17,0,174,0,5)])) (.fork 2 (.leaf [(40,0,151,0,5),(130,0,61,0,5)]) (.leaf [(136,0,55,0,5),(9,16,166,0,4),(14,0,177,0,4)]))) (.fork 5 (.fork 2 (.leaf [(19,0,172,0,4),(20,8,163,0,4)]) (.leaf [(25,0,166,0,4),(35,0,156,0,4),(36,128,27,0,4)])) (.fork 2 (.leaf [(129,32,30,0,4),(134,0,57,0,4)]) (.leaf [(162,0,29,0,4),(164,0,27,0,4),(168,0,23,0,4)])))))
def seeds : List SeedItem := [((2,0,189,0,8),189,0,4,[]),((8,0,183,0,8),63,0,5,[115,84,99]),((32,0,159,0,8),63,2,3,[117,101,67,32]),((128,0,63,0,8),63,0,1,[50,65]),((4,0,187,0,7),111,0,1,[115,50,32,83,66,96,16]),((160,0,31,0,7),31,0,1,[50,65]),((6,0,185,0,5),47,0,1,[115,50,83,98,64,16]),((10,0,181,0,5),47,0,5,[114,81,98,50,65]),((12,0,179,0,5),55,0,4,[114,98,50,81]),((40,0,151,0,5),47,0,5,[115,99,83,67]),((130,0,61,0,5),47,0,1,[50,65]),((136,0,55,0,5),55,0,4,[]),((14,0,177,0,4),15,0,1,[115,99,82,64,16]),((134,0,57,0,4),15,1,2,[32,82,64,16]),((162,0,29,0,4),15,0,1,[50,65]),((164,0,27,0,4),15,1,2,[66,16]),((168,0,23,0,4),15,0,1,[64,48,32,16])]
def n7 (i : Nat) : Nat := 0x18107020830222440003050c12078b010c02c10a010c038120e0b101c804400212408889c0848102c206040b0a0204c40f827010c8940840620204042058400000000014104c20003618081e06c6000000041010000004101b56d0b2ec6b06b2a8e9ea16809ee7699e4e8fe2685dea745cc71dae6557c5dd5e51522425043d4f0384d2334c830cbe2e4b42bca02448c21c781545012c461043c0dc2808c1e0641403c008fe4c2af112819bd541e2225023fa33442cea047f4a68855d408fe8cd10aba811fd9221d635023fb2443aa6a047f466885c940e9eaa2a4b92812fd69a2152502af92ea9aa4a06771e1634c940afa8cceeb0a8197c87549515023fb2443aa2a076d5c96150540f5ab12c2a0a81bb56850531503f2a64a0a62a066f550784c5409beacd10b0281eb56150560503e72a8a9260a07e658d414c140fcca9a8298281fb16150530503f32a898a60a07f4545314c140f6cb1ac0982813f519a21205033eaf040a40a06ed5a14144140fd8a0a40882811f4985ca115022fab3442cea04f64e48059140bcc9c900aa2813d9392015450237a93442e6a04774e6885c9408fa8cd10b92811dc898cd725033a90640ae4a05e64e480505409ec9c900a0a81f195454d30503f228298a60a046f626771014099f4cab02028193e775604050347cccac080a06cb8895810140d9b08ab02028193d725604050276d328c080a066d9dd1810140d5b3323020281b36554604050374c448c080a066d5c91810140

def n8 (i : Nat) : Nat := (if i < 1 then 0xd4154140dfc7254140bfd684c140bfd584c140fdd634c140fdd534c140ff9624c140ff9524c140ff9614c140ff9514c140fdd314c140ff9214c140ff9604c140ff9504c140bfe8848140dfe7748140bfd6848140bfd5848140bfd3848140dfd6748140dfd5748140fbd5448140dfd7348140dfd7248140fed5248140dfd7148140fbd4148140fed2148140ff96048140ff93048140dfc7848140ff48148140bfd6844140bfd5844140bfd3844140bfd2844140dfd6744140dfd5744140fbd5444140dfd7344140dfd7244140ff55144140ff93044140ff92044140bfd681c940bfd581c940dfd571c940fbd541c940dfd541c940bfd6808140bfd5808140cfe669dd40d7e559dd409fd689dd409fd589dd40dbd489dd409fd389dd409fd289dd409fd189dd40dbe7791140ebe6691140f3e5591140dbd6791140dbd5791140dde778cd40ede668cd40f5e558cd40ddd678cd40ddd578cd40f9d548cd40dee7788940eee6688940f6e5588940fae4488940fce3388940ded6788940ded5788940fad5488940ded7388940ded72889409fc7888940dec7888940df67784540ef66684540f765584540fb64484540fd63384540fe62284540df56784540df55784540fb55484540df57384540df57284540df47284540dfa7780140efa6680140f7a5580140fba4480140fda3380140fea2280140ff21180140bf93880140df96780140df95780140fb95480140df97380140df97280140df97180140fb94180140df872801409fe8859d409fe8855d40bf88059140bbe8855140dbe7755140fb88055140bf880551409fe885cd40cfe665cd40d7e555cd409fd685cd409fd585cd40cfd6758d409fc8758d40f3d5454d409fc8754d409fe885c940cfe665c940d7e555c940dbe445c940dde335c9409fd685c9409fd585c940dbd545c940ddc835c940df4815c9409fc8758940f3d54549409fc87549409fc8750940dec7250940bf880509409fd784c9409fc784c9409fe885c540cfe665c540d7e555c540dbe445c540dde335c540dee225c5409fd685c5409fd585c5409fc87585409fc8754540bbe8850540dbe7750540ebe6650540f3e5550540f9e3350540fae2250540bbd5850540dbd7250540fb56150540fb88050540bf880505409fd784c540fb5414c5409fc784c5409fd78485409fc7848540f3d5454140bfa884c140dfa774c140efa664c140f7a554c140fea224c140ff2114c140fb9544c140fd9634c140fd9534c140df9724c140fb9414c140fd9314c1409fd7848140dec7248140fb54144140cfe661c940d7e551c940dbe441c940dde331c9409fd681c9409fd581c9409fd381c940ded721c9409fd811c940dbe7710140ebe6610140f3e5510140fae2210140fb61110140bbd5810140bbd1810140dbd7210140b3d5810140bb51810140 else (if i < 2 then 0x48746170d8800c0807120a203419080e103a1b17003c00f003c00f00289c10847850384c7090f88c3a40307c483e0078018086021808602103404441b220a021b1e090e89009000c48404010a40a0e1b283419080e100589098c18230b87080307824364e007801810604181060418122436309a24041e22103c28107836381204363012043c3c22200223099400101874364e007801e0078011188442111082a1e10018110e870800000000210104018408030b0bd850c2160f704d80fbf7df62f8378fbaedcf6e4d70fb77db62d716a1b40d9aaca763cb0e5816bdd5ceadbd65eb01569aa4d4a6a254fba7252ee937484a32511285b41f9ffcfa27a33b19bfcda266d30d976cb3656d29693fc9a24b5243911c8323d91d58e3c6c23331828b1452e269126887c3be1c30ca859c27211d077830412606501b806bfd9facfbf7cb3dd9ebef48798bc45df4eda75d3a8dcf4e5a718b869bf4de36e636d5b4ed906bcb5adabad3d693343d9f0ce1669b2f195cc8e63bb181892c3b612307d810be85ed2f0d76aba75c3ad796a0b3958cabc15c4add56c2b29578aae554aa9152ca8853d29b14cea6252ea961494a3c51728814009ce4e026c935a9a84d1a67933298b4bea5bd2c294a49e24b925292448fa46922a91048123d11cc8d846522a913888e44021a50a484d41fa0c50588274082008fe87d43da1e2ced675439e9c50de86d435e9a98ce86423111808bd65cb2d5962cae856f2b51504a3050127993949ae4c925d926c8f6452219109082c4081fd0fb07bc3b51ca8db06ce3621a58c645e02d015389f84e026212a091847022a10507843941aa0c505a827013308503f01dc0e006902ec14808d044017c0b4055028012c08c04101e00b802e000dfe7788940dfd5788940fbd5488940dfc8255d40fbc8255140bfe8858d40dfe7758d40bfe8854d40dfe7754d40dfd635c940dfd535c940dfd525c940dfe7758940dfd7358940efd6358940bfe8854940dfe7754940f7d5454940dfd7354940f7d5354940bfe884c940bfd684c940bfd584c940fdd634c940dfe225c540dfd635c540dfd535c540dfd525c540bfe8858540dfe7758540dfd7358540dfd7258540bfe8854540dfe7754540dfd7354540dfd7254540f7d5254540dfc7254540fbe2250540fbd6350540fbd5350540fbd6250540fbd5250540ff56150540bfe884c540dfe774c540bfd684c540bfd584c540dfd674c540dfd574c540fbd544c540dfd724c540fdd324c540ff5514c540bfe8848540dfe7748540dfd7848540bfd6848540bfd5848540bfd3848540dfd6748540dfd5748540fbd5448540dfd7348540dfd7248540ff56148540ff53148540bfe8858140dfe7758140dfd7358140efd6358140dfd7258140dfd7158140efd6158140fbd4158140dfe7754140dfd7354140fb else 0x41c1628385081003e0820d05841f0504c61807883e131068268280878a1809a0a021e2c0a028918341620807c40d0f208625078a120b060d060910403f091a083c20a8584160b891217078c2285121c3a2098690430986040b0ea2461906883a0b10283301182d042318801e20e82c40a0f8840828082c8098083c687060a021d438c3b01410c3b01140428907c0470300882816104c3a1f185e040780858a170b0912130a40a02509852050122120413184c3c1c18720220f84e0430905c41d05883810588c4890785c6160e091211118c161212102100e08390112144620e079043c18885090b8a12104a2048240c24709082502284a045040b8a0810720448343891308103e1020d82041b087a0424487a0438105841f09c082c40d8210230f40848984083708141f060b1c1c3a24482c3a34483c3a300a204890701e0240701e0234203a020f24051024420602307a1040e0e881c811204303428a0288107421d0a24161d183c3a20da2040b0e8913011404284070a0214103a02307a1041b44083b01121420f4208084078a0e0c058d0a1072105c00f003821087478203874444e004261e160b121d181d03890f93801001121e007801001121e005081e00400001121e005081e0050481e00c1a0c038783a5e0078010000002243c00a103c00a0b802e007801000000010414487801420780141207803e005021e004421b142436207003c008001f0d8b801e0051381108f0b81080e04090d8849028487461311083a26103418170d920501e00e0501e00e028814078020160402890994058100a2426581210363c0e24263c484c41f848747820488861f8))

def x8 (i : Nat) : Nat := 0xd01d1b82a620f0a308b2fb07b34d785009ebb15000b1c719000a32f13f2d631f2571a50cd2600000000000000000000000002100000000080d000b060000000000003118109b000050b518e1f22e036324b17f03f1463ac0200000093340e7a951e230739000a04000312d16a7b635c2c509b77123028122805d2741d70f300a70004c04020eae6317c62

def n9 (i : Nat) : Nat := 0x683171b2088f408bc444839e0c1e2418746cc0e2302122650781091320388c0848d941c0e04246ca043e2631f1a071e811b090840f8c038f408d8404a0081c0606244cc1a2f0310461c1270f172581880e0938403c0c48d94587e046c722420e023a2630d070b82231d0109410038587c10e8084a004746c62c3a0e38371202108820b011d891c301870388c0c4049c0c381e062024c3e1036382078101031d891b401808e8c441c7c7483a362060781c088891d1b440c4048e062024703120c1048189081c083c4c460162620047020d1381105820711811b09303c4408d8496081a046c24a0e110237123c68202010781891b38e83c400c48d9a08187624046cd02363d12105820310211d07304030a186091fbdf09e75dc1d0dc99b85a7199d8a97b570160d5994853712fd1e9115020f4ced8dc4d50cbcc68b54ae0a6c9d89648b083c7886b460054c4783842b01dc128054003ff3ba81ff88940ffc00a07fd67503feaba81ff59140ffaa8a07fd73503feb1a81ff54d40ffae4a07fd62503fea9281ff50940ffa64a07fd71503feb0a81ff54540ffa82a07fd31503fe90a81ff58140ffaa0a07fd30503fe90281ff44140ff8e4a07fc20502ff3ba81bf99940efcaaa07be44503ef19a81fb88940fec22a07fa00502feb3a817f55d40f7aa8a05fd73502feb92817f5c540f7a82a07f930502fe39281ef10140

def x9 (i : Nat) : Nat := 0x7aa828000001be84f50e3402162c3c6a40c4c1dea97448080a8403d0a0204d0000a0420001c810113000003de41dd8f30001021646d000000000002c758000000060c0037000000f8004b4820000000101a800000000001a008000000000014002487910d0001e28c000000030e3a12982d103c00004ae3083800030b8c4438438000a1dac23c000000020f0c18800002ce70c8811800058a52141a2ad46b404e30ac0415e1f0000b12f808000000000000000000030d58d79c42800020590000c3a3023e0810001a0dc0006053000000000004a229de0000200720b171f00001856800001c4000000000000000e0b40000000f0d6a11480c507ae0b1941506538a1f18dc324000301530658348c0d8051e12241db46819096108e2d0802b0b900000001c59a8ae0000000000068f6305822cac3462ab2232e36d86c98cba598c33304a5854c179c0a7e1e908800014265c3f18c02010000347c80003a056994a5d108b409600000004b1600e12438000383aa1d302f90618000c1c1a304439589f922fa2b2c36a004105fc42f83d8813e022000106f289500000142c2088b681480000026c8a60000000086c0000619ae0701240000101ba27247200000001040c06290d78019209186100000000000241f80000001e45400028fb808021548698000000000000841033600de289c0f98ff3174a00d844c83191c2c02af24a879e10c0001c1c68f1e04ac20a80a082eb1dc00000005adc02019c34000786690efc03c000789b8152e275e8250f200c3419fc34da35104f417b8639816c1d400034835060911aa9ce448383470be2248000207d2dc0e13e05ee8cef056000143fd8c8c0ae63f400060f0000000000000000d6300000000000000010259c1180000001aa9c00068df000183f102d800001150263c2100000000c24ec0e800735766396831e0ece16ac34580bf8b7a0030448021f8dd0000000345d80cf00000002c0c80000000a2ab086000000000002436582a206c0000000401a21f4e23387a00008228439b82600002017609a85fe4deba06a2bf4470000e07263f8c73c874000121d744180003222000072234e590a4e026d380046200d1814000b3c60c03050001c200600404d0000473440080830060030034c100000000100608300418430000b20404108510020110528a005101080101485084040200000000

def n10 (i : Nat) : Nat := 0x22048ffd40

def x10 (i : Nat) : Nat := 0x28a800101181b82e95180187800000000000194084b8860a682210191a0378cf8b3712050000003a400048f000512096800193a05800592d00a88b0de8c2868958060abc0eb96087000000194813000000000083b0d000000000589309800000000110b0e64f800001709c200484041861

def lv : Nat → Packing
  | 7 => (60,4,6,0,0,10,0,n7)
  | 8 => (282,3,6,0,0,13,0,n8)
  | 9 => (46,2,6,0,0,12,0,n9)
  | 10 => (1,1,6,0,0,0,0,n10)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 20 86 5 12 6 2 x8
  | 9 => lookupWord 99 420 6 15 9 2 x9
  | 10 => lookupWord 15 69 5 12 6 2 x10
  | _ => fun _ => none
def g : SeedForest := ⟨⟨191,10,fun j => sampleSeed191[j]?.getD (0,0),cols,autosSeed191,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 191 0 4 seeds⟩
def rows : List (Row × Row) := [(16,17),(1,3),(2,6),(4,12),(1,17),(1,33),(4,132)]
end S191_0_4
namespace S191_3_4
def cols : IndexTree ColumnInfo := (.fork 13 (.fork 6 (.fork 3 (.leaf [(0,0,191,0,11),(2,0,189,0,8),(32,0,159,0,8)]) (.leaf [(128,0,63,0,8),(1,0,190,0,7),(4,0,187,0,7)])) (.fork 3 (.leaf [(24,0,167,0,7),(160,0,31,0,7),(0,8,163,20,6)]) (.leaf [(0,32,30,129,6),(0,128,27,36,6),(1,16,166,8,5),(1,32,30,128,5)]))) (.fork 6 (.fork 3 (.leaf [(3,0,188,0,5),(4,8,163,16,5),(4,128,27,32,5)]) (.leaf [(130,0,61,0,5),(9,16,166,0,4),(20,8,163,0,4)])) (.fork 3 (.leaf [(25,0,166,0,4),(26,0,165,0,4),(35,0,156,0,4)]) (.leaf [(36,128,27,0,4),(56,0,135,0,4),(129,32,30,0,4),(161,0,30,0,4)]))))
def seeds : List SeedItem := [((2,0,189,0,8),189,0,4,[82,48]),((32,0,159,0,8),63,1,2,[117,101,33,32,65,48]),((128,0,63,0,8),63,1,2,[50,65]),((1,0,190,0,7),111,0,5,[114,83,48,33,97,64]),((4,0,187,0,7),111,0,5,[115,50,32,83,66,96,16]),((160,0,31,0,7),31,0,1,[16,64,49,32]),((3,0,188,0,5),47,0,5,[114,83,48,33,97,64]),((130,0,61,0,5),47,0,1,[48,80,65,32]),((35,0,156,0,4),15,0,1,[115,99,49,81,64]),((161,0,30,0,4),15,0,1,[49,64])]
def n6 (i : Nat) : Nat := 0x3f81422053048143

def n7 (i : Nat) : Nat := 0x1c10000083044446088aad084f5c335c5c04df56688581439fa8cd1090287fc9524c12050ffa10298240a1e7d5e08148143fd4a1240882871bd49a217050e73930a1260a1fe25093048143

def x7 (i : Nat) : Nat := 0x280

def n8 (i : Nat) : Nat := 0x15c61070988384d1c61020823081512385082338c2870b181a083850c57184162a2410c3051c3a186110c2860b12385820c102118c2410a3846300905c302e041038c2816821c48146107a1882e051878c10dc61011c23186118c208c610586882c544161a2460a106042081810e3058b182c40e00800007007803c01460f007802081171110a088b80208301c3131117007803c0147c1161e1e0870d182c587c01860c3061820816243041210583090c1048582038e104461216387084c2c4081c2bf779ae4dacb2f62abed68a974ba8cd049ef3aa66cb894721a3cc648af0c9febd8786eb9c8b846deda9a6b38646c397cae45aeb295eab0546a393ca744ce9892ea584a69191ca2c43e849029f83c6738e09a431e608ba9682964b8889041ee3a86e8c01562383c85407e0a80a800bfe8854543dfd625c143dfd525c143dfd615c143dfd515c143dfd605c143dfd505c143bfe8858143dfd7158143efd6158143bfe8854143dfd7154143f7d5154143fdd624c143fdd524c143fdd614c143fdd514c143fdd604c143fdd504c143bfe8848143dfd7848143bfd5848143dfd5748143dfd7148143dfd7048143ff96048143fdd3048143ff48148143bfe8844143dfd7844143bfd6844143bfd5844143bfd2844143dfd6744143dfd5744143dfd7244143fbd4244143ff55144143dfd7044143fdd3044143ff92044143bfd5808143bfd1808143f765584543df55784543efa6680143f7a5580143fea2280143ff21180143df96780143df95780143df97280143fb94280143df97180143df97080143fd930801439fe8855d439fe885c543d7e555c5439fd585c5439fe885c143cfe665c143d7e555c143df6115c1439fd685c1439fd585c143cfd6758143bde884c143ede664c143f5e554c143fd6114c143ddd674c143ddd574c143f9d424c143ddd714c1439fd7848143fd930481439fd78441439fd7808143bdd3808143

def x8 (i : Nat) : Nat := 0x66a20003140039400b9c000024238106d8fa470c000006161

def n9 (i : Nat) : Nat := 0x40b063c622612142010f18c282c10f18a242c10f18b040c78c40a063c62462220f18406308246105081a092221ce1420e022e3863850d048c724682447470c5e8686f3519843df8e96b30d1a5714003ff00287ff54543ffac0a1ffd5050ffe90287ff44143ff840a1f7e5550ffb08a87fe80143bfaaea1dfd7150efeb8287f74c143

def x9 (i : Nat) : Nat := 0x832000551100ac1399c7850000000000486d862f22b9054d9e8064f5858000c8f22349a0002c11527520403ba5e02d000000000000051504e4e0692698ad0fe014000581390701f8180005c000000000000000246000795f073c675420000cf3298106717544a21a22228d800109924b801e4c566a000000087d89ba240007d06c32e36d1eb844000d2c00000000000000000001613e3092164ede3f026c15800206a31cfa7000087c00000054dd04e000692991665dc1d0004ce8a09849e1d0003018316804f51929a0009a3c02f83504ea0ab8dfc5050848f0800001714000092aa20000116000000050550f000000091a0000002c8c000824000364820d4013842a1e2175039085c25439421f0a7203e4420c0102887182220000608020010262980218065008c0095a4

def n10 (i : Nat) : Nat := 0x8e30ffd43

def x10 (i : Nat) : Nat := 0x7a36100000003a3c07adfafe72a62662c0000124cb0000024dd2800c2000630a2aa800f9400a1000f0da0a1800e6000001

def lv : Nat → Packing
  | 6 => (1,5,5,0,0,0,0,n6)
  | 7 => (9,4,5,0,0,7,0,n7)
  | 8 => (80,3,5,0,0,11,0,n8)
  | 9 => (14,2,5,0,0,9,0,n9)
  | 10 => (1,1,5,0,0,0,0,n10)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 6 0 2 x7
  | 8 => lookupWord 4 19 2 10 4 2 x8
  | 9 => lookupWord 40 171 5 13 7 2 x9
  | 10 => lookupWord 8 37 4 10 4 2 x10
  | _ => fun _ => none
def g : SeedForest := ⟨⟨191,10,fun j => sampleSeed191[j]?.getD (0,0),cols,autosSeed191,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 191 3 4 seeds⟩
def rows : List (Row × Row) := [(2,3),(1,3),(2,6),(16,24),(8,24),(1,33),(4,132)]
end S191_3_4
def sampleSeed255 := g255samples
def autosSeed255 : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
namespace S255_0_1
def cols : IndexTree ColumnInfo := (.leaf [(64,0,191,0,11)])
def seeds : List SeedItem := [((64,0,191,0,11),191,0,1,[])]
def n11 (i : Nat) : Nat := 0xffd10

def lv : Nat → Packing
  | 11 => (1,1,0,0,0,0,0,n11)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g : SeedForest := ⟨⟨255,11,fun j => sampleSeed255[j]?.getD (0,0),cols,autosSeed255,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 255 0 1 seeds⟩
def rows : List (Row × Row) := [(2,3),(1,3),(2,6),(4,12),(1,17),(1,33),(2,66),(4,132)]
end S255_0_1
namespace S255_0_4
def cols : IndexTree ColumnInfo := (.leaf [(64,0,191,0,11)])
def seeds : List SeedItem := [((64,0,191,0,11),191,0,4,[])]
def n11 (i : Nat) : Nat := 0xffd40

def lv : Nat → Packing
  | 11 => (1,1,0,0,0,0,0,n11)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g : SeedForest := ⟨⟨255,11,fun j => sampleSeed255[j]?.getD (0,0),cols,autosSeed255,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 255 0 4 seeds⟩
def rows : List (Row × Row) := [(16,17),(1,3),(2,6),(4,12),(1,17),(1,33),(2,66),(4,132)]
end S255_0_4
def sampleSeed383 := g383samples
def autosSeed383 : Array (List Nat) := #[[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[84,66,16,98,129,48],[100,49,128],[98,82,16,66,49,128]]
namespace S383_0_1
def cols : IndexTree ColumnInfo := (.fork 27 (.fork 13 (.fork 6 (.fork 3 (.leaf [(0,0,383,0,13),(4,0,379,0,11),(16,0,367,0,11)]) (.leaf [(32,0,351,0,11),(64,0,319,0,11),(1,0,382,0,9)])) (.fork 3 (.leaf [(2,0,381,0,9),(8,0,375,0,9),(256,0,127,0,9)]) (.leaf [(6,0,377,0,8),(12,0,371,0,8),(17,0,366,0,8),(24,0,359,0,8)]))) (.fork 7 (.fork 3 (.leaf [(33,0,350,0,8),(66,0,317,0,8),(320,0,63,0,8)]) (.leaf [(0,1,332,50,7),(0,2,312,69,7),(0,4,369,10,7),(0,8,99,276,7)])) (.fork 3 (.leaf [(0,256,23,104,7),(28,0,355,0,7),(49,0,334,0,7)]) (.leaf [(70,0,313,0,7),(352,0,31,0,7),(1,2,312,68,6),(2,1,332,48,6)])))) (.fork 13 (.fork 6 (.fork 3 (.leaf [(2,64,61,256,6),(3,0,380,0,6),(8,256,23,96,6)]) (.leaf [(16,1,332,34,6),(32,1,332,18,6),(256,8,99,20,6)])) (.fork 3 (.leaf [(264,0,119,0,6),(5,2,312,64,5),(7,0,376,0,5)]) (.leaf [(9,16,358,0,5),(10,4,369,0,5),(18,1,332,32,5),(19,0,364,0,5)]))) (.fork 7 (.fork 3 (.leaf [(20,8,99,256,5),(34,1,332,16,5),(35,0,348,0,5)]) (.leaf [(40,256,23,64,5),(48,1,332,2,5),(65,2,312,4,5),(67,0,316,0,5)])) (.fork 3 (.leaf [(68,2,312,1,5),(96,256,23,8,5),(260,8,99,16,5)]) (.leaf [(268,0,115,0,5),(272,8,99,4,5),(280,0,103,0,5),(288,64,29,2,5)])))))
def seeds : List SeedItem := [((4,0,379,0,11),191,0,4,[130,50,81,115,98,65]),((16,0,367,0,11),191,0,4,[130,50,97,115,82,16,64]),((32,0,351,0,11),191,0,4,[135,101,50,33,16,64]),((64,0,319,0,11),191,0,4,[135,50,65]),((8,0,375,0,9),127,0,1,[131,84,115,98]),((256,0,127,0,9),127,0,1,[]),((12,0,371,0,8),63,0,1,[131,84,115,98]),((24,0,359,0,8),63,0,1,[131,67,116,99,82,16]),((320,0,63,0,8),63,0,1,[]),((28,0,355,0,7),31,0,1,[131,50,66,116,99,82]),((352,0,31,0,7),31,0,1,[]),((264,0,119,0,6),119,0,1,[]),((268,0,115,0,5),55,0,1,[98,50]),((280,0,103,0,5),55,0,1,[82,98,66,16])]
def n8 (i : Nat) : Nat := 0xf801f801f80107c00800000000000000000000000dbd6d1ccc7c2bdb8b3aea9a49484746f5f5a55504b46413c37322d28231e19140f0a0500aebab63d272082215f36c87a4e4104429eebd9509c8208853dd7b0e13904110aebab639a72082215f36c8734e4104429f69d8f0948208853ed7b0e12904110addad639a52082215db56c734a410442bd6a58e6948208847edba1cd2904110a79a564d467442212ee52eaa4e2004425f495d549c400884f715b2853080110c3dcee955329c2218eb5292aa65384421f695d54bca708843ed2baa9984c1108eed76ad122982218dda215a245304432bb3bab448a6088675633568914c11087bb37552701c2215ec52ca1640734431ed19b35440208871ea77a212904110e794674425208221d729de334a410442b74b58e6948208857695b1cd2904110af529639a52082211fa6e8734a4104429f4dc0e6948208857e1b11cd2904110

def n9 (i : Nat) : Nat := (if i < 1 then 0x2904110aff5e838041109ff6a47304110bfb6887304110e779de33a2110cf726a33a2110c7f9dd39a2110cf78cd39a21108ff5e939a2110cf74e139a2110ef68cd09a2110dfc46509a2110efc46509a21108ff2a573a2110adf56839a2110afe42839a2110cf74e439a21108ff6a438a21108ff6a473a2110afb68873a2110afe68073a2110af722a778cd10e779dc898cd108ff5e8898cd10af75e8898cd10af7628798cd10bf34a8098cd10ef68ce8880110afe4ea8880110f769de3380110afe22a3380110ef622a3380110efca221180110ff48ce1180110efc4e21180110efc0e21180110afeaa93880110e7e9dd3880110ef68cd3880110afe5e93880110cfe2a538801108ff2a53880110afe2a53880110afe2a173801109fe2a53180110ef60e13180110afe2a13080110ef60e13080110bfc2853080110ef68cc8980110afe4e88980110afe6283980110bde5683980110bfc4683980110e7e9dc3880110afe5e83880110ef64e03880110bee5287380110afe6a07380110bfa6887380110bfc6847380110bde5683180110c7f9de994e1108ff5ea994e110cf74ea994e110afb4aa994e1109fb4aa994e110cfb4aa994e110afe42a994e1108ff42a994e110cfe42a994e1108ff26a774e110c7f26a774e110e779de334e110af726a334e1108ffaa9794e110c7f5e4794e1108ffaa8985cd109ef52a994c1109fd46a994c110af74ea884c110af722a334c1108ffaa9984c110c7f9dd984c1108ff5e9984c110cfe261704c1108ffaa8984c110c7f9dc984c1108ff5e8984c110cf7a64384c110e779dc384c110cfda20914c110d7d9dc914c110df58cc914c110bdd568914c110cfd4e0914c1108ffaa9790e110c7f9dd790e1108ff2a1790e110c7f1e1790e110af7aa9380e110e779dd380e1108ffaa9981cd109feaa9901cd10dfc285901cd108ff66a880c1108ff2a1790c110c7f1e1790c1109bfaa9690c110cbfa21690c110d3f9dd690c110cbf5e1690c110cbf1e1690c110ef68ce88041109fe66a88041108ff66a8804110cfe66a8804110f769de33041109f7aa93904110cf7a213904110d779dd3904110cf76a13904110cf75e13904110df65c13904110cf72a139041108ff2a13904110cf71e13904110cf70e13904110dfaa212904110cfba212904110dfa9dd2904110d7b9dd2904110dfa8cd2904110df38cd2904110dfa5e12904110cfb5e12904110dfa4e12904110cfb4e12904110dfa5cd2904110df94c52904110dfa5c12904110dfa4c12904110dfa1e12904110cfb1e12904110dfa0e12904110cfb0e12904110dfa1cd2904110bee52873041109fe6a47304110afe6a07304110bfa6887304110bfc68473041108fb4aa994e1109dd568914c1108fe66a8804110cfaa212904110d7a9dd2904110df28cd2904110 else (if i < 2 then 0xc130e0c8343c1414120a438800f003e007c00f04cc0463f00281001c0f801e13830d022203bc2306460445f0020c8420e102c08c846130118f05c1898254845130130fc0080308545e004980f80107801078010001c1702207801e0b81112a1e1383e0b81202010402217801f00208041e00400070212543e007c0083c0083c00f801f0024387c00f8010802b1780108384e0f82604283041c2214161384e0c200989e003c206425178010802b178018542098784e082b08880c603408c610709850584f002f178008050304c3c27061984448543c27070a8504e0d060986080462f003c27070504c400000070508080108562f003c1130118c0004190c0443f00200702217044c0463078010702217801a13838542d206b0604630001c088400780107022178010821685c2820490b42e1492060f090b0463053848582320410742c119384858231c0a107022103c0083c00f09c1898785e160b49c150226221785822202050242d1f07030b828184085a0e08c6083a1608c60000000024c0f05c1f0814866112382c14171f07c122e3e0f82816172707c142e3e0f8285c715889fc49a21b0f486dc33216709a840c1a20b3040818c011fd6fd27d7be59ee6f5a7a0bc79e0aeec769bae9d42e88737b959c7ae24705b7c9bb2dac6c4b599a86d2a683b3b9996cb264cb25191ec80638b18987ec26610b049806bd65cfae41702b54598ac115c2ad2566aad154aa96543aa094e6a6e52fa9694aaa5051ba8c9446a0a4fda73937e9a64cba6212f29744b2a5812b69564a3a4e125291a48aa4192028f2471a35118a8b6453a2390fe83e4089f90f967b23d19e28ef676c3ae9cc0e5670836d9b08d3e6903319950c4e6042f59770b5e5aa2d29680b365962be95e0abe55029694a0a4651e27d93b09ce4ce255929892e47e237910883e41a20a8ff07ee3f21f18f2877638e1b08d4865e30216a8ac854628a14289d84e226212488704061d60e886b832a17c0bb855029e12c093848823a11808984381720960398118046000cff5e139a2110affaa973a2110aff5e839a2110aff5e838a2110bfb68873a21109ff26a778cd109ff5e8898cd10aff5e83880110bef5287380110bfb68873801109ff5ea994e1109ff26a774e110aff22a774e110aff2a1734e110cff660985cd10aff680985cd109ff5ea994c110aff5ea884c1109ff26a774c110aff22a774c110aff2a1734c1109ff2a5714c110bfb688794c110cff9dc984c1109ffaa9790e1109ffaa9790c110cffa21790c110dbf9dd690c110dbf5e9690c110df7aa939041109ffaa93904110cffa213904110df79dd3904110df78cd3904110df75e939041109ff5e93904110cff5e13904110df75cd3904110df71e93904110df71cd3904110dfb9dd2904110dfb8cd2904110dfb5cd2904110dfb1cd else 0xe138308460e02022201013100e0b05c18410826281c3828202c1b05160d8289880404440782e0450a8784e0f82e04842f802c1c1c1043c1020301c2417044303a3218271032120b82080241b100e8a8804c5440282a201c13100e081b0b84120262a1c1310380c8988070443826204c1c10200e0b84e0c1921c9028260e0d880641a190e0c83436201c130e0e40c30641))

def x9 (i : Nat) : Nat := 0x391661e0000000db18df088fe473a200054c8002124815949a85c001007e070000015c5d000000000000022c6018000000000002654440da4f1877c1e01f24b00680006a30245066930642b118810000001000596fc2069fa0b0546d2f000423580c00061bc50800308a6184098001c100000000000dba000402800100529c30a3a81019e49000000000000070e692a0820009111913db404000000011200000513af1754001310200607

def n10 (i : Nat) : Nat := (if i < 1 then 0xa704073061f07054d8402c1706152c1707820b911184c1c5480602887098318054f84c18546190c0546180a880c1a0c05481c420b41a152e0f05058b9307828b8c38190b85881c0c85c2c4c1e082e3b9fdc5adb76b2b40595ec4b605af2d6f2b2758eabbd53aa5d4f3a655286903461a2550aa8153ea9e54dae6973079664ab250723f8de462a2b1114883437619f0c1859c24e0c305381e409601cfdc7e73eddf52f9b7c23dd9e88f2d78fbbb5d76e80734b96dc40dd36ba34e5a20cc3636b17d8a2c0d5e02e396b8b185732af5504a6b52a28d144c9d04caa61d2ce94748aa3b11bc891438a0fd03e8113f41f8cf9877f3b41cd8e6271a38a9b8cdbc6913149824b9c5932b514749b249e23611548463d61d20dec64a2b413808d44061da0d885b429a12d08b03b41760920390124040000fff19d10887ff5ce88443ff8e744221ffe778cd10fff19c00887ff5ce00443ff8e700221ffe774e110ffeb9a70887ff1e538443ffb30b9a21ffc985cd10ffe482e6887ff9dd30443ffae698221ffd714c110ffe98a60887ff1e530443ff8f098221ffe770e110ffebc070887ff9dc30443ffc6608221ffd7304110ffe39820886ff8ce88443fbc67442217fd39a2110dfe9cd10887fe426884437fa1344221bfd38a2110dfeb9d10886ff0e6884437f87144221bfc73a2110fef3bc66885ff22633443fb91319a21fdc798cd10fee04c66887fea22004437fd1100221ffa3380110fef19c00887fe84600443ff27100221bfd3880110ffcb9c00887fe4c600443ff26100221ff83980110ffc0cc00887fe0e2004437f87100221ff87380110ffc18c00886ffa6538442ffd329c221bfe774e110eff3ba70887f78cd384437faf29c2217fd794e110dfebc270886ff1e5384437f930b9a217fe994c110dff442608877f9dd30443fbc66982217fd794c110dfebc260886ff4e130442ffb2298221fdd314c110ffcb8260886ff261304437f8f098221fdc384c110ffa48a60886ff9dc38443bfcee1c2217fd790e110dfebc070887f74e0384437f8f01c2217fd981cd10bfec80e6886ffa2030443bfcee182217fd790c110bfe8c860886ff5e0304437f8f018221ffa8804110dff44020887fe8cc10443fbc66082217fd3904110ffc9c020886ff4e010443ff2e608221ff93004110ffc1c020886ff0e010443ff0e608221bde33a21109fe9cd10886fe42688443bbcef19a213fc898cd10dee44c66886fea2200443fb46700221ff21180110dfc9c400886fe226004437f071002213fe994e110cff3ba70886f78cd384427faf29c2213fc985cd109fecc260884ff261304437b870982217f4914c110cff3b870884ff5e4384437ba701c2213fd981cd10bf6c90e6885fe64073442dfad218221bfa8804110fed19820885f74e410442fda52082217e92904110 else 0x1058307020872c160c1c0810221c82c1820873081101d83920c870e0420a50e418210520660c1043c14b82c0a206080a840782c0841104c260f058120032211608400544100a10060f098202818321a30640c050a930420120408200809c61c83a20784c1883905440c3887830c321c828c321a438c3b0882c19101a0ce13069554160dc018210e13c1e0b08233a204184c1a30466e00705e3432143822222305814384c5e2c384042144421e0b060e04c3384c1e0b02e0ea1f082c11161184c1a30465088403905832612a7440709830608c8070a203c00a1b81051a1a0a1c16088a870c1a0a282a18582c0891184c0c2c585e0040b81160828708150c2e006118486a3046502a1c5c00e0b0220178b0a200e41c5e2c2e050c85c1260626c16044150e130782c0a60506c260f05814441c5e2c461306880460a0f81038bc58ac08442098c10c4d84c1e086441041702060d612142c442304068384f0981c18993820830383c10680c8f850b0f83446080e1ac2428588106102a2914141020c20545851061306060289844703a3e141a1617060c1209881c02843049818980e1016082028aa3c563e00410110a084201cc1e102a9c18442115c20acc100c313023183c142c1818340f050b0b84c189c444e0041014108703384068550050e0bc784c1c545a2b2c3130231c14384c189c444001f8020401c321c120802c17460b0224404e2f161114182830801d43c3a2c2328211058321f0983c1605008038140c87c0e0b09831988d783c125c7074460f0584c0981020c1e105415322309830a910c8843e0f05848b60510543c1b0782c2604f84c1e091d16c0991184c1e0b0250b25c40582e13069528203582c0e130633112309834c60b02584613061522203383c1613022b178b1207840220e0602e070584c18d046c040444183c20a42)

def x10 (i : Nat) : Nat := 0x2c038030c4b0a0319de28c4230000000577832444c60c40000000715ea95814e0b9900000000000487040d842c956358640035494654ea814b494d71dc858000e2c6899694500000000004c000000000002aac42cb83e74c8416983a12940000a06400000000000e1e65434b7dd021843a94080000000000308b190700000001150b8b1c7360a6992d800024700001c899b25609d641b4e21041953c00000003011c237499ec2612880001ca7c0007d5200000001cc12111657d0a5e8b2527800000000000706f0001411dd8d11b945472e2882c33b7d96800000003ba40000e16d111bdbba6c200bbc0ecaa72a922d5092a8000000000021c8800000010b2000048bf44598ca800000009578000000000000001ee69ada681884b22e5ca9d927e6b7509715267f45958a000211d096b000121fcc478000c5800000000311d96f600000007a1f00000002c16eaa600004111fda000000010f0f11122bdc140846a1555909d419e1001439948864c2dd81c8485c137f0f23d383128d429699bc00aa96c639ee1d0414224566ee9df954c20a9589891901a684d46f581a591ef06af0142dc80000936000000008840a6000010878000424bfaece60550978170001a10c00000009478000000043a195444e00000722154a80000000000085840000000000050ca00031ce8000fae4000045b000020380003c17a28d00000001436884fe6c7e20fd1cc062749ba9eac819a25dd68810ac96500f350b6c19c450000d183a9ec0005392b103c428160800087880001d3c80008746a64e4110000d75104a61d9a0b57487247259d2a93c0018e790bc109db0cf0df11d2f1b517400000c3000000000000000072a4b0f0000344d0000000000000002012307ea97d50c0000250800000470162301a64040006776d180000000042054753615fcc54161302a0003cb3e25d60e74626c0dd28f933a0001dc498b7000000033b91016213d0ac70560000713e61f8ea2e04682d909780003e45b171443c5299b950001001103880000000a880000299aa22e0001558000000018c7e0164a7f209020080001b28212720140000000000045d86a81abbd01d267883400000000000275df1a0061d8702c56e32300002a3818b6066000001b81270000f610a9f203bfaa800000001dc40000a43800020817a27450400008b97b8b253118cc405e28c424406dc09a8000576bc9a892d086b24af0ee583ac92b0800000050450000040403c00800820800410406010860020403081436850d124100600104024014c0c00c31420490c00000201471080090402459870c00010000020810c410620808e2c9000380081040188243

def n11 (i : Nat) : Nat := 0x80711050683828184232c5840302c2418a98201c1870661204590103433050307082a5e58a0605848382811815404030d02c0c141c20a962a0e10a8548302a21c19840d1528e0c8b8b10201c141a120e0a051050309062a50683828481163044140c2418a9a120c54707042e3c2ed6a463c7dda25f5684ed16344a41bc3a07400ffe88443ff8cd10ffe00443ff4e110ffd73443ff4c110ffc38443ff1cd10ffc30443ff04110bfe88443f78cd10ffa00442ff4e110bfc38443fe04110

def x11 (i : Nat) : Nat := (if i < 1 then 0x680d466400000000000000000000006953f448cd0f8964a0d42c40000000526f000044c40000000000000000003b88c4a400000002b5000000000000000006f00000db9c354930a00025117215f0aa1a0e9ba8000030e00021930000e2b800019a380000000000000042837425e569807000000000000000000000000001da7bb70964a00bc000000000000002a88491e00010e280000000e08a00014238000d44784f400040240001c16400000000001d62adbf800000000000000000000000001421000000000001c0bd24500000000000000044ca00005217d11000000000000000d4be0000f3e8000a604000293afa60010e0000d05800000000002c9f800000000001dbc8000000000000001334ab062412497391a86bd8d100000000148e000000000000000000213dd05a000000000000000000000000001b3a000000009b680000001a5f80000000000081e800000000000000000039064eb600019914932c2aa0002fa20284000008a0000734b0001899c000090196ef4c4e98f8000341c000159c80000001a0c80000000b6d60000000532166ddc4951b3a15b00008907cbfc32d971200000000b01f4d20000000147d0716408c0004056e6d8eca4000695f0000249c000395dc019ddf40003a1b000089700000000000000000000000aad60000000095800000000000000000000000000000000000000000000034e14cf40000000000000015847801000000000000000000000000000000000000011b0800000000000000425d0001a57b9318000f452886542f8000000000000000a2ab70741f80004b760001010c083b1440516a944c3c8957000000010038000f4ee0000d28000000000000000000000000000000633786c400000000000d0b10c2c51b0000000089340001146000000000004b1e000000000000000741e0000000636800016df85c30000f24200014aa1b7200006c1ec0aa266625400030b00000c6d2000288b80000001e48c0002956000000035278000000000000000201863a00000000000000000000000000e2da0000000000000000000000321f000000034968000000049680000000000000000000000000000000000000000000000006b71cb00c89ad0be05c000000000005b3320ec00000000000005c000214175440001a900000083000000003c241a728428a0f508b22786055a8e303012370000a0f800000000001edbfd32000000000001995db1ac2c2360400052279286882518c6a070000a80d50100000001acc40000000000000011388000000000000000000000000034bb000000001c0800008003060007e0000017000000428180800400000001400100780000600601000010000081000008000020018000000000008000060003e000000000000000000000000010002000000000000 else 0xc118000321c000164cc5c2800000000001d2a800000012cb20a3b915a0780003d09d924000025640000000000000030800000647800000000a32f68c000000000000001294e829937476b706189b50000270800000000000000000000000000000000000000000b4ac00011927b20e692000000000002206000208c80000000000000000000000893a9251a2f74d5a0b400000000001aca00000000000000016beb23ae00be8280003d4962dc00000000000f66a00021438000000000024bc800000007532800000000000002031a32e00002c180000000b4d8000000000000001c09dd10205d000000000005003e0620064000655bc6980000000000000000000000000000000000000503bd6f800000000239c6080)

def n12 (i : Nat) : Nat := 0x80c10127fd10

def x12 (i : Nat) : Nat := 0x270003d70bef58a9c99493e2e00000000000000000000014d04e8a20004400000000000214b3de0e6cd9cf24a6c001d8000b7e0015b90a001485ed8001750c400000000000006b50002f000000000668000009540000200800

def lv : Nat → Packing
  | 8 => (36,5,6,0,0,8,0,n8)
  | 9 => (201,4,6,0,0,13,0,n9)
  | 10 => (140,3,6,0,0,13,0,n10)
  | 11 => (16,2,6,0,0,10,0,n11)
  | 12 => (1,1,6,0,0,0,0,n12)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 22 98 4 13 6 3 x9
  | 10 => lookupWord 112 472 6 15 8 3 x10
  | 11 => lookupWord 91 655 7 15 8 3 x11
  | 12 => lookupWord 10 62 3 11 4 3 x12
  | _ => fun _ => none
def g : SeedForest := ⟨⟨383,12,fun j => sampleSeed383[j]?.getD (0,0),cols,autosSeed383,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 383 0 1 seeds⟩
def rows : List (Row × Row) := [(2,3),(1,3),(2,6),(4,12),(1,17),(1,33),(2,66),(8,264)]
end S383_0_1
namespace S383_0_4
def cols : IndexTree ColumnInfo := (.fork 38 (.fork 19 (.fork 9 (.fork 4 (.leaf [(0,0,383,0,13),(4,0,379,0,11),(16,0,367,0,11),(32,0,351,0,11)]) (.fork 2 (.leaf [(64,0,319,0,11),(1,0,382,0,9)]) (.leaf [(2,0,381,0,9),(8,0,375,0,9),(256,0,127,0,9)]))) (.fork 5 (.fork 2 (.leaf [(6,0,377,0,8),(12,0,371,0,8)]) (.leaf [(17,0,366,0,8),(24,0,359,0,8),(66,0,317,0,8)])) (.fork 2 (.leaf [(288,0,95,0,8),(320,0,63,0,8)]) (.leaf [(0,1,332,50,7),(0,2,312,69,7),(0,8,99,276,7)])))) (.fork 9 (.fork 4 (.leaf [(0,16,358,9,7),(0,256,23,104,7),(18,0,365,0,7),(34,0,349,0,7)]) (.fork 2 (.leaf [(28,0,355,0,7),(49,0,334,0,7)]) (.leaf [(70,0,313,0,7),(352,0,31,0,7),(1,2,312,68,6)]))) (.fork 5 (.fork 2 (.leaf [(1,16,358,8,6),(1,32,94,256,6)]) (.leaf [(2,1,332,48,6),(2,64,61,256,6),(4,2,312,65,6)])) (.fork 2 (.leaf [(8,16,358,1,6),(8,256,23,96,6)]) (.leaf [(16,8,99,260,6),(32,1,332,18,6),(32,16,326,9,6)]))))) (.fork 19 (.fork 9 (.fork 4 (.leaf [(64,2,312,5,6),(64,256,23,40,6),(256,8,99,20,6),(256,32,94,1,6)]) (.fork 2 (.leaf [(264,0,119,0,6),(10,0,369,0,5)]) (.leaf [(258,0,61,0,5),(5,2,312,64,5),(5,16,354,8,5)]))) (.fork 5 (.fork 2 (.leaf [(6,64,57,256,5),(9,16,358,0,5)]) (.leaf [(10,4,369,0,5),(12,16,354,1,5),(14,0,369,0,5)])) (.fork 2 (.leaf [(17,32,78,256,5),(18,1,332,32,5)]) (.leaf [(19,0,364,0,5),(20,8,99,256,5),(25,0,358,0,5)])))) (.fork 10 (.fork 5 (.fork 2 (.leaf [(34,1,332,16,5),(34,64,29,256,5)]) (.leaf [(40,16,326,1,5),(40,256,23,64,5),(48,1,332,2,5)])) (.fork 2 (.leaf [(65,2,312,4,5),(68,2,312,1,5)]) (.leaf [(72,4,305,2,5),(72,256,23,32,5),(96,256,23,8,5)]))) (.fork 5 (.fork 2 (.leaf [(257,32,94,0,5),(258,64,61,0,5)]) (.leaf [(260,8,99,16,5),(268,0,115,0,5),(272,8,99,4,5)])) (.fork 2 (.leaf [(280,0,103,0,5),(320,32,30,1,5)]) (.leaf [(322,0,61,0,5),(328,0,55,0,5),(13,0,354,0,4)]))))))
def seeds : List SeedItem := [((4,0,379,0,11),191,0,4,[130,114,98,81]),((32,0,351,0,11),191,3,4,[133,117,101,33,48]),((64,0,319,0,11),191,0,1,[135,50,65]),((2,0,381,0,9),127,2,3,[128,84,66,16,98,113,48]),((8,0,375,0,9),127,0,5,[131,84,115,98]),((256,0,127,0,9),127,0,4,[]),((6,0,377,0,8),63,2,3,[128,81,67,112,97,32]),((12,0,371,0,8),63,0,5,[131,84,115,98]),((66,0,317,0,8),63,1,2,[132,116,65,48,80,97,32]),((288,0,95,0,8),63,1,2,[101,66,16]),((320,0,63,0,8),63,0,1,[50,65]),((34,0,349,0,7),111,0,5,[130,50,115,48,49,98,65,80]),((70,0,313,0,7),31,0,1,[131,115,65,50,98,81]),((352,0,31,0,7),31,0,1,[50,65]),((264,0,119,0,6),119,0,4,[]),((10,0,369,0,5),47,0,5,[130,50,81,115,98,65]),((258,0,61,0,5),47,0,1,[50,65]),((14,0,369,0,5),47,0,5,[130,50,81,115,98,65]),((268,0,115,0,5),55,0,4,[98,50]),((322,0,61,0,5),47,0,1,[50,65]),((328,0,55,0,5),55,0,4,[])]
def n8 (i : Nat) : Nat := 0x7820400003c0c20078087c0c08440621f02083e0020f800fc007e003f001003e003f00100010020f800fc007e00200000000000000000034080740e207880860602f800fc007e003f001f80080f2038190c00000008810300818841102088130603c118305030380e08820440834083c26ffbd6d3b26bfad6aba267f9d653865f7755cb6a59f5f55b4e51743503384bf2d4ab2247f1743b0640f013fafc3e6f73d2f23beed3aae8396e3382c62deaf29a9e2568d1e2761ce711ba6c18e5b14a4a106330aa2204e0b0220046fd6b26a77845408fda564d46708a814bf5ae99a21715025dea5d54c1ae2a052fd6ba65835c540c77d544c2e6a0a8166f5ec835c5415031f7442554ca62a063ed784aa994c5408dfad7552f298a811fb4aeaa5e5315025beadd54bc262a05add6b28d784c540b76af644a8298a813be5aeaa5c5305021bead9353bd10a0517d5b26a77a2140877a964d51119a812d756eaa5e2335025baadd54bc422a04bb54baa98384540b56ad641a8308a812bdaed6a20e1150347b3bad441c22a04b795baa9788014097729755307002810bf5aeaa5e5815021beadd54bcb02a042fc9b5a8835c540e33cee4c466a0a812afaed6a20d4150315f4cad441a82a068be775a88350540c57930b50e6a0a818eb261a21cd415031da4c34239a82a063b8986807350540877b744c0e6a0a813e6aed3a241415036cd3ba7448282a06799794e89050540d732f09d120a0a81be46c53a241415021dea5d54c4a62a043ed2baa9894c540bf236051a8298a817e44eca050531502bd85ca82c8a60a04f395b2a5414c1408e7ab654a82982817e4aed414c5305037c95528298a60a0779299505314c140f72510a0a6298281f649dd414c530503dc8bc28298a60a07b908a505314c140bf2172a0a62982817e452c914c5305027d85d28298220a060fe77aa96920d40a4fb6a3d2d241a814af6d07a5a483502976d90f4b4906a052f5b11e96920d40a5f3603d2d241a8143f5eca15a48350293ead942b4906a052bd4b2856920d40a5da5650ad241a814be6c0a15a4835029da5c294c88e6a052bd6b20d491c540

def n9 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0x884c5408ffaa9894c5408ff5e9894c5408ff2a5784c540bedaa9414c540deda65414c540eeda21414c540f6d9dd414c540fe58cd414c540eed5e1414c540eed225414c540eed2a1414c540fe528d414c540fec281414c5408ff6a4784c540afd684784c5409df56a995c1409ef52a995c1409ef269415c140cfea22994c140d7e9de994c140bee52a994c1409ef52a994c140dee52a994c140cfe5e2994c140e7e9de884c140e7e22a774c140ef6a22334c140f769de334c140ef65e2334c140dfca66114c140efca22114c140f7c9de114c140ff48ce114c140efc5e2114c140fec506114c140ff44c6114c140ff40ea114c140afeaa9784c140e7e9dd784c140cfe2a5784c140ef628d784c140fec505914c140beeaa9414c140deea65414c140eeea21414c140f6e9dd414c140fe68cd414c140eee5e1414c140fe668d414c140bee2a5414c1409ef2a5414c140bf6aa9314c140df6a65314c140ef6a21314c140f769dd314c140ef65e1314c140ff45c5314c140fec505314c140fe6505314c140fe5505314c140ef6229314c140ff4245314c140bfa688794c140bde568914c140bee528914c140afe628714c140bee528714c140bf64e8714c1409ef52a99441408ff6a578441408ff6a58344140bedaa94144140deda654144140f6d9dd4144140fe58cd4144140ded4e54144140eed5e14144140fec50530441408ffaa9931e1408ffaa9911e1408ffaa97920d40c7f9dd7920d40cbfaa96920d40cbf9dd6920d40cbf5e96920d40cbf6856920d40cbf1e96920d40cbf2856920d408ffaa99120d40c7f9dd9120d408ffaa9891cd40cbfa21691cd40cdfa21591cd40cefa21491cd40cfba21921cd409fdaa9911cd40cfda21911cd40cfd629911cd40ded529911cd40cfd229911cd409feaa9901cd40cfea21901cd40e779de33205408ffaa97920540c7f9dd7920540cf78cd7920540c7f5cd79205408ffaa93920540c7f9dd3920540cf78cd39205408ff5e93920540abf5a87320540adf5687320540aef52873205408ff6a47320540afb6887320540afd6847320540afe68073205408ffaa9891c540cf78cd891c5409efaa9491c540cefa21491c540de78cd491c540cef60d491c540cef20d491c5408ff629391c540abf5a8831c5408ff6a4831c5408ffaa9890c540c7f9dd890c5408ff5e9890c540c7f5e1790c5409dfaa9590c540cdfa21590c540d5f9dd590c540cdf6a1590c540cdf5e1590c540dcf691590c540cdf1e1590c540cefa21490c540d6f9dd490c540cef5e1490c5409feaa9900c540cfea21900c540d7e9dd900c540cfe5e1900c5408ff6a4780c540abd5a883845408df56a995e1408ef52a9960d40ce72623350540c6f9dc9850540aaf5a88350540be64e89050540fe4505314c1408bfaa96920d40c3f9dd6920d40 else (if i < 2 then 0xeed20d4184540afd6293184540e7d9dc8984540ef58cc8984540afd5e88984540afd4e88984540afd6287984540bf94a87984540afd6283984540bbd5a83984540bfc4283984540afd68c7884540afd6847884540e7d9dc8384540afd5e88384540abf5a88384540afd6848384540afd6287384540bbd5a87384540bdd5687384540bed5287384540bf96887384540bfc6807384540f769de3380140ef65e23380140ef660e33801409fe26a3380140df626a3380140f7c9de1180140ff48ce1180140efc5e21180140efc60e1180140efc6061180140fec5061180140afeaa97880140e7e9dd7880140cfe2a57880140afeaa98380140e7e9dd8380140afe5e98380140afeaa98180140e7e9dd8180140ef68cd8180140afe5e98180140beeaa94180140f6e9dd4180140fe68cd4180140eee5e14180140afe6293180140fec5053180140afe6287380140bbe5a87380140bde5687380140bee5287380140bfa6887380140bfc6847380140afe6287180140bee5287180140afe6283180140bde5683180140bee5283180140adf56a995e1409df56a995e140cdf56a995e140aef52a995e140cef52a995e1408ff4ea995e1408ff46a995e140afe42a995e1409fe42a995e1408ff42a995e140cfe42a995e140abf5a8935e140cf764c935e140cfd644915e140aef52a9960d40cef52a9960d408ff46a9960d40cfd6449160d408ff62a995cd408ff26a885cd40c7f9de99605408ff5ea9960540aef52a9960540cef52a99605408ff4ea9960540cfe42a99605408ff26a7760540c7f26a7760540cf7a663360540e779de3360540cf75e633605408ff26a3360540cf726a33605408ffaa97960540c7f9dd79605408ff2a57360540c7f5e47960540cf764c93605408ff6687360540abf5a87360540adf5687360540aef5287360540afb6887360540afd6847360540afe68073605408ff62a995c5409bf5aa995c5408ff26a885c5408ff269835c5408ff668835c540a7f5e8835c540abf5a8835c540afd684835c540d6f9de9950540cefa668850540e6f9de8850540e6f22a7750540de7a663350540ee7a223350540f679de3350540ee75e23350540fe506a3350540fe602a3350540ee72623350540cef2623350540aefaa97850540cefa657850540e6f9dd7850540cef2a57850540eed2857850540cef2619350540cef2617350540cef9dc9850540e6f9dc9850540aef5e89850540cef5e49850540bcf5689350540bee6809350540cefa648350540e6f9dc8350540aef5e883505409ef6687350540aef6287350540baf5a87350540bcf5687350540beb6887350540bed6847350540bee6807350540cef2607350540f6e9dc9050540fe68cc9050540bee4e89050540dee5e49050540eee5e090505408ff62a994c5409fb4aa994c5408ff26a else 0xc7884540aff5e88384540bbf5a87384540bdf5687384540bef5287384540bfb6887384540bfd6847384540aff684935e140aff4e8915e140aff5e89160d409ff46a995cd40cffa66885cd40cff261915cd40aff684985cd40aff628915cd40bef528915cd40cff9de9960540affaa97360540cffa657360540aff68c7960540aff5e89360540bbf5aa995c540dbf5aa995c5409ff4ea995c540cffa66885c5409ff26a335c540cff261935c540affaa9835c540cffa65835c540aff68c985c540aff628935c540bdf568935c540bef528935c540bfe680935c540befaa97350540eef5e17350540eef2a17350540eef2617350540eef5e17150540eef20d7150540bef68c7950540eef9dc9850540bef5e89350540eef9dc8350540cffa22994c5409ff5ea994c540bfb4aa994c540dfb4aa994c540cff5e2994c5409ff26a774c5409ffaa9794c540cffa21794c540cff2a1794c540affaa9784c540cff2a5784c5409ff2a5784c540ef728d784c540efda21714c5409ff6a5714c540efd225714c540efd2a1714c540fed9dd414c540eef5e1414c540fed5cd414c540fed1e9414c540fed1e5414c540aff5e8894c540cff5e4894c540aff628794c540bef528794c5409ff4ea995c1409ff26a335c140f7d5c5315c140fed505315c1409ff269315c140bbf5a8935c140bfeaa9714c140fee9dd414c140fee5cd414c140fee5c5414c140ff65c5314c140ff55c5314c140fee505314c140bfe684794c140bfe5e8914c140fed9dd4144140fed5cd4144140bbf5a87344140bdf5687344140bef5287344140bfb6887344140bfd6847344140cff9dd9120d40dfdaa9911cd409ffaa9911cd40cffa21911cd40dfd681911cd40affaa973205409ffaa9391c540cffa21391c540cff9dd890c5409ffaa9790c540cffa21790c540ddf9dd590c540def9dd490c540dfe9dd900c5408ff26a77a2140c7f26a77a2140a7f4e8899dd40a7f468899dd40a7f628399dd40b7e428399dd40a7f628199dd40b5f568199dd40b6f528199dd40e779de888cd408ff26a888cd40e7722a778cd40af7aa9788cd40e779dd788cd408ff2a5788cd40af72a5788cd40e779dc898cd40af75e8898cd40af7468898cd40af7628798cd40af7628198cd40be7528198cd40f769dc098cd40ef65e0098cd40af768c788cd40af7684788cd40e7d9de88845408ff26a8884540afd26a8884540e7d22a7784540ef5a223384540f759de3384540ef55e23384540ef522a3384540ff402a3384540ef51e23384540afdaa97884540e7d9dd78845408ff2a57884540afd2a57884540afdaa98384540e7d9dd8384540afd5e983845408ff2a58384540afd2a58384540e7d9dd8184540ef58cd8184540afd5e98184540eeda214184540f6d9dd4184540fe58cd4184540eed5e1418454)) else (if i < 4 then 0xc8e8104883246090220c83919072300bc7c108c031183605c2f001e09c0e0503924060422f0016160c05e0020a6068321c1602d034191382016060380f0641a0fc00603060302117800f800f020c060602e024681b0c8c1171303e05c138084106a124172181703e0211782039098743286050660c081b0210884280c178270103005480c00ab02e0682f80847e080e416aa0c417141882e2b78adc7b6b2d91b5dad5bb4d6d0fb3a6cc3b276c82b172c36b06ec00af96bcaaebeb94ae12b69ad3ab33ac62afdab5eabcaa86a86a9aea50a8aaa0fa7a69c3a676982a59e957a4f2937a47290ca39a8c0a29687fa16683ea08e7f29f5e7b19e5a77b9d2a72f9c527049ba66c39ace68d99ca65798f261697ee5e096ea59495e655394b6512940a4f293324b1925a4869182445907e4048fd23e48efa3a38e4e3838da234d8cca3178bf22e18b1a2ab8a42275896a23f889220987ba1d386e219d860a1518506131848611184060f183860d183320b182b209c8232071818605c813203c80b201c80320077fddfe77f5dfd27eddfa77e89f9d7e61f887e0df7e7de5f697d65f3e7cb9f1e7c65f097bb9ede7b65ed47ae5eb47a91e947a11e697965e54793de3f78bde1f783ddff77bdddf773ddbf76bdd9f75b9d5e7539d3e74b9d1e7439cfe73e5ce97391cd4733dcca7315cb572c1cab726dc8b71edc6b716dc567119c3670c5c2c7045c0c6ff1bec6f45bc16ec5ba16e45b816dc5b616d45b416cc5b216c45b016b6dac06a69a7f69bda5468e5a1e680d9e867619a7668999d65dd95c650593c64598e563558af625188461a585960a181860218035fa17cd5ef57975e1d7565d4574c5cc57165bed6e05b1569f5a1165e585d5e656d558455795435475518542150353cd4ee53a54e453254b952a549951a1458512142d501d4024f453b64e153754d693344c392f34b8d2d34a5d27c49852514905231488521147ad1e647851dc475d1d2468515a44a50f8431d08041c1060414104040c0ff43f38fa83e8cf9e3db4f523cdcf1c3c5cf073c08edc3b04eb13a84e9c3a30e8739dce673988e5d3934e3d3888e123808df23788dc73658d9135acd5b352cd3b34acd1b33d4cda32d0c993224c7931a4c593074bec2f18bab2e40b8b2e18b602d14b1f2be4ad32ae0a9d29dca4628d8a262858a0627ac9ba267c98425a494e24f892324208ed231c896219484a20e881f20107e91f387b31e8c7881db475d1cdc7271c307071bb06dc1b306b11a5868619d865018a860417785b8164856c151852b146c50b13c04e012e8489118c43d105c3fc0fb03bb0e803900dd43650cfc30e0ba02c20ac82a20a1c277099c25708f021607ec19e053013104580da02a4036006c0009ff26a778cd40aff684788cd409ff26a77845409ff26a33845409ff2a57384540aff68 else (if i < 5 then 0xd82c5c0f810b8106810470163a0408c5c128101b1f04036203c18141e040c0238c0f702140b0c0b0f020602e040c04070860b81030101b218261008840cc0d881981b130b0422e0406c40ab030815023130b03c261005040a805898581e1308616280c42c5c08858b8201e0780b89e003e003e003e003c083e003e002418200700b840f001e0610240c05e0020f001f001e061f00120c107800f800f800801b02d178008000e0610001e003c0c2078168bc007c0041c0c2078168bc00400e09c0c4080c180c180c180d4085c042007030f020f800f800f800f800f020f800f800f020f80084407445c1b13c007c007c007c0048387c00781041c0c2020e10001c0c2001060f800f0308100f800838187c00400e09c0c408161816120de005c043e003e003e003e00241c3e003e003e0024183e003e00241820790d0321e0b064203c104170fc00211780082106e203c0b45e00180bc0030101c08e2f00160807f818322001e001c0351838072203c0e04003d868190f8201e2300b89e0020ef0c8361f800422f0010420d85e003c138083c06c4f001f0010704e0620240c05e00209c1d82d191a0f04e061181b10002340c8446819088d032111a06422340c8441c8703f191a0642e060c8220c1f701045c0c1602d3704042460171381f010880e09c130d10c05a420fc101e0c2203c170420e0b460816107800800040de005e003e003e00342381a190604f001f00180de005c0d06832182847034320b888650c0a05b0783210c9e003018180b81c19060306c054180c0a83016020e020f0406c084850182805060200c0c040c020c020c020c020c0282505d1a1800000023f04e060c4811f827030560f81b980a7042300b880a38203b05a4e09c078183f2704e0407b818220626f001f001f001f001f00106281f827010605c0fc10168e8103207c300084118e020f8843c168b058391780042207020818120b07234160c85e003e0020f00107020c070801c083c08281fc0098107c007c007c00603f801704e068281c901c0d810351d020f800f800d020d020a070720c06054180a8170306a38300d45e003e003e003e003c0c03f0108e0d4bc0f8270108e460408c180c0d839101e05a2003810470603e040e44c08898391807e040e46c08898391f020722f000845c13818321828e07c041f93c0060586058605860583510060600601a900c035102a06e206c0b440a81e0bc0042002f102208820960bc502a0c0441d048150602212820418300c480c4168bc0041c02e102163026160c0442c170810b181780082163028340c840c0303e053181f80090b060200440782f001f00180c1084048188bc007c00606c1806e321e42b0c0c8790a0683e024681c0c87a18062321e42b0c0c8790ac303e024681c0c1b02e17800f80090b05c280c18100960 else 0xa8118b03828104a036206606c40400d8b030111606e040a8781b05f021e06c17c086431058331e06c17c0868180d8b818310423e060c40f0c0f038101b0162a160405c1380888302a1021054205416100404040090809021102106c20420d84c100d82c182c036204602c542c0808080231704e022e080440f0c0801117040501107c100f04a1f040421287c10838b827021013090740c20215042281a1e08113010c1b01506a361105440d8108151844c0541c6c2c080819847102b60206c11901581b170302011c611c19880801b1704e02c2c08138270110320242e06103d42c5c0c0f0321c07081b01706460c7808b820441047216203c0c6048c85823102106a2036084238c117010623e09c04407819832183306411c782c080886040f0781b0203c303)))

def x9 (i : Nat) : Nat := 0x6812e0cc016c1c202a0000000e02d05460d387a000200e00070034145c8b21220240000001f11c86c00040600000000e0f7886000000900d80000000001d536045c200c6e606806b6136815e07a04ba0e5076608d8788212804219788de09845e2084043e161800801ec682189857b93901c000000160b8000000000061f8000000206600000000000001420a07c000785e0174890e0f983ac0b28300005872000000120a0000623e053322380c0000000000401800408400001074c1a685a300ee0204167820970d2208c60015e0

def n10 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xebcb06a06ff5e1835037fb22c1a81bfc9160d40bff4cae6a06ffa2173503bfceeb9a81bfd985cd40dfebc2e6a06ff261735037fd32c0a817fe9960540dff3bb02a077f9dd81503fbc66c0a81bfe3360540dfebcb02a05ff5e5815037faf0c0a81bfd9360540dfec1b02a06ff5cd815037fae2c0a81bfc7960540dfe49b02a06ff1cd81502ffd32b8a81bfe885c540eff3bae2a07f78cd715037fb30b8a81bfd785c540dfec1ae2a06ff261715037f906b8a81fbe9950540fdf3ba82a07ef8cd41503f7af2a0a81fbd7850540fdec9a82a07ef60d41503f7ae6a0a81fbd7150540fdec8282a07ef1e541503f7926a0a81fbc7350540bff4ca62a06ffa2131503bfcee98a81fde334c540bfec4a62a06ff62531502ffaf298a81bfd784c540dfec0a62a07fd5c531503f7a8298a81bfc894c540dfe3c262a05ffa6570503bfceeb8281fde335c140ffb08ae0a06ff60d705037fb02b8281dfd715c140fdea0ae0a07fea6530502ffd3298281ffa774c140eff3ba60a07f78cd30503ff42298281ff6114c140ffcbca60a05ff5e530503ff2f098281bfd784c140ffcb9a60a07fe64530503ff30298281bfd814c140ffcb8a60a07ef50530503ff26298281fdd314c140ffcb8260a07fe1e530503ff12298281ff8714c140bff4ca20a077f9dd10503fbc6688281ff61144140bfebca20a05ff4e5105037faf088281bfd8344140fdea0a20a07fe4c1105037fcee41a81bfe881cd40bfec48e6a05ff64473502ffb2039a81bfe7720540dff19902a06ff5cc815037f8e640a81bfe881c540fef198e2a05ff62471502ffa7238a81bfd831c540bfec80e2a06ff20c715037fd1018a81dfe770c540bfec4862a05ff5e4315037faf018a817fd900c540dfe3c062a067f9de885033f9133ba81bde888cd40eef3bc66a06f75e2335037b91319a81fd8098cd40dee3c466a06fda2211503becef08a81fd63384540dfabc422a06fd60e115037eb0308a81fb54184540dfa44c22a06fd1e2115037e90708a81dfa7780140fed19c00a07fc846005037f2f100281bf98380140dfcc0c00a07ee506005027fd32bc2819fe775e1409ff4cb06a04ffa65815033fceec0a81bde33605409febcb02a05efa654150377d10a0a81dbe7750540fcf19a82a06ef5e14150377930a0a81bbc8350540fdc48282a04ff62531503f6a8298a817fa994c140dfd44260a077e9dd30503fb46698281ff2114c140dfcbc260a07ee50530503fb26298281fb541441409fec98f0a04ff644785033fcee41a813fd7920d409fec8906a04ff62473502dfad239a8177d591cd40bdea48e6a05fb64873502feb2239a817f9901cd40cff3b902a06f78cc815027faf240a813fd39205409fec48e2a05ef524715027fb1218a8177d590c540bdea4862a05fe6403150277930a0a812fd6920d40 else 0xc9d721bc6b7167c43708bc026fafbd06ee7ba86e33b7b6d7fb446cb7b216c3faf96b8bad16aebaae6a4ba7c6997a4f68e3a2768439ff67a39d766c79aa668b98265d7969658793764bf923646f91463f78e263578c462df8a6627b87961c7856612784260d7829608781a600f7e35f5b7ca5ef77b15ea779d5e437895e0777a5d7b7435cef7255c3b6f35b4b6bc5a9769e5a1f667594363f58035d657275a955fb56d555b53b544350954074e1532b4b9526347d515f4144fa73d34ef33a64d8b3384caf31f4c0f2e84a7f28949a325748c720c47c31da46e719e45a714e44f311c43ef0e5428707741ab05e410b02c3fb6faa3e12f503cbef193bf6ee23b56ec93af2ea139eee6a393ae333872df737aadde36f6db13656d7a357ad3e344ecf3334acb231f6c6c311ac353052bf42f62bc22eaeb9f2e4ab862d96b452c7eaff2ba2ac32a9ea912a12a5a290ea23280a9ec276a9c927069b5262a979259e95124fe93824ae90123968d4230a8a7225687a2166839209e8161ffe7e41f0e7a31e0a7621d067261c667031b9e6d11aea6a41a22668191e63117f25dc168a564150e52313ba4ce12ca49711da44210ae40b0fd23c50e563750d7a33e0c9e3070b4a29909a624908a220807b21cc06ae19505fa168054613b049211304060f003660c3029e08c01ae05000d201900320007ff9de33503ffcef08a81ffe3384540ffeb9c22a07ff1ce11503ffceec1a81ffd7360d40fff4cae6a07ff66173503ffaf0b9a81ffd915cd40ffec82e6a07ff24573503ffceec0a81ffd7360540ffeb8b02a07ffa6571503ffc66b8a81ffd985c540ffebc2e2a07ff64d71503ffb06b8a81ffd735c540ffec82e2a07ff24d71503ffd3298a81ffe774c540ffec4a62a07ff5e531503ffaf098a81ffd834c540ffeb9a62a07ff60531503ffae298a81ffd904c540ffe3ca62a07ff8cd70503ffae6b8281ffd715c140ffe98ae0a07ff24d70503ffcee98281ffd734c140ffeb8a60a07ff4c530503ffcee88281ffe3344140ffeb9a20a07ff5c510503ffa6288281ffc7344140fff198e2a07ff9dc315037fcef44281dfc399dd40efe0cceea06ffa2233503fbcef19a81dfe778cd40feebc466a06ff5e233503fbb0719a81fdd738cd40fee3cc66a07f7066335037f8f119a81bfe8884540ffb3bc22a077f9de11503fec6708a81fde3384540ffabc422a06ff5e211503feb0708a81bfd8384540ffab9c22a07fd60611503feae308a81ff53184540ffa3cc22a07fd0e6115037f8f108a81bfc8384540ffa39c22a07fe9de00503ff46700281ffa1180140ffcb9c00a07fe5c600503ff26300281ff87380140ffc38c00a07fe0c6005037fd32bc2817fe995e140eff3baf0a06ff64d785037fb22bc281bfc935e140dfe48af0a06ffa6583502ffd32c1a81dfe7760d40bf) else (if i < 3 then 0x220701f0311f04c0550401703a300c85a6c070446031260208e088c08a5c1208c060b0e4b814302c0a1816050c08080620f45c392c101820e040308c8727c120b0e46810608c8301a960782f020c0392c0f058701c930202d0646b01860473e05058b0282c48460803c15810726c0a0b160980e058186a5c1302c06180e4b8200f050301c9704c041801c300e4d8201623e078120d0c06e811f04c041ec083d321182604038641c9908c0807464300e4c0f416110610388f80e0782604a02c390c0781e0805c30238141b9f0107a181e098100f050301c9b0201f0111d1a0c0d8101781a32181702464470e49034161b072482f021417810a0bc0858260403c330c072602304c0b0182c39320e84060034320c07274220841c068643d306c168301a9208c130201d0a0783d3e0381416878785c120a46030207019080b040210cc1bc2c1706918202e8587240a107423018604430448420f81c321c181404a198608874321c0e19460351c0c10d832101781055858461a81c0ca047864391e041b0723c090a8683624328c060381821b064202c140ab0bc0c390301946061141a1c8645c08360e47052341b0e0781b04c06182e0980a30342106c1301460a84603816090be06641a07c0b04c0703360980a303c100a460703e0287a30442107c1301460a8460980c3381e04641f04c0619c0f02320f826030ce05819908c0a06c1303c04c8460483a1781832640815c0d0b064a0ca30281b0143d1826050360885230542304c0618220f826030c1106c1301860883a0d826020c15084190cc1301060c8420e0ae0980830605704c0418200e03417816078086b82078172a0781a0bc0b01068c0400d8141981c318088b82072172c36020070570207b03c0618c103b0b598140f826068d60268230241f04c0f0136040382884603826061a8761fab04c07030560b808d8260283c0c0c1606c0f0482f012c0c83e0782417809907818064200bc0703c10390c941082a0c0324086020db04428183609808300a9008c081ec0f04c04454603f4a050386181a3180e081d85a9c130181f0382f02360980c0e0c130481e0bc0703c08d826070582e4c120782f01c0f02340e03e0823e0381606208641ca835056070c102c040bc0f040c839581705e0623e03816081b87290d830c07040b418300c09055808160d18070db010800b068d81211824150c14060502ac100a060c040638204c0503060181e05c1a20438582e0d1021c2c17068809a160b83440870b05c1a20438582e0d101e05c1a1a110cc30341e198606038440c03240202806019200f8106007032542c150c00e064a0406d81848060326058390d00c064a0f6068c0180c9436c0c240301928320c080a0605e23781fdf17757dbf76b7da1762bd8375dbd60754fd4774d7d24744bcf7735bcca72cf else 0x10b81c471c178121085c0c581a0b42d0c203c85c178140c582c1e8190c207105a1030860b140f0405411911808428c0b0442f0108c88c60420782a106d05a1030da0b084782037058f0481a081281b2e0810c160320e859b0446058203c03230442f01c101b26081c2160f1006c110b82c142e09812303c10210204a260211c0d038660d9a0bc050b4200611cc85e020f0644c110b06f0108ca0383c8c0644c090b0c868580d05e0211941e42c321a1603c160c836542c1b07b01c08a19e020388e4432181021814303c101ec0a18260580c300f13030410c1e041821105902382c582061814160f17010c02382c98106d05a1040c03682d0c24161b02181130406e0b1e020f0370590300410c1c0c10a0e23910b422061c0f0320e8360287c30741c2830608c1206829180c0c85a10282e0712301c0d068190b02e07468324216142f801210141830388a8d070482207865180d4a85a10282f02818685a0e282f0281868c070341d0881f02864393a16142208432190e4a85f00242c285e08242f011210141c303c128d06c4c0a08c0e0d45c36300c83890882c483c16241a0b1416182f041417808a0b0a0c182c381c16138641c97048201e860322c301c130342839260886e0619103104041c0c322e0618e040a2321c9a0b830380e4905c181c064482c3826030c0724c0c0801d0f82839360381a1a2291190e0391828150178160980e161183d07c2f81b2060aa0881d06c1301461105f002c0d060790b85c4236068340c8584403c2e212304119181c160a86c19120b818150d832285103e021b20f05c128d220b0c1618210841e0d86032360981a34191304860321e060440c032341919080a3010ec3f2a110420e0380d0c87270d82a05108044100490cc13010c303865b8221083c0e0d8110c07e80a3014683626098186c1910110c11a0c88250178100e1160980c100803785c3381b6071120841e06c0704461105e08282f0416078105b8207850190b8241a0f0a1c0880a4118120f03216088501ae0381e08ec130146044202381603822161e1a02054301e020a81683c1305a347423030180b41e190c0f826070c81618160d018180c888460981e0205860642006062190c0a05a0e0dc0c1086b81e0980c30a02d078600d0b4a0306c180c1501836c051a0d4d8260780c040a8606c041b468302010198178103782603038218588f0ce06d821080c60781b04c05184417808a0bc0440460980a30191701099181148058298140f030360861623e0782602c0c50881c07046060883011c35c1303c05a844110380e8c032169c1b08b020))

def x10 (i : Nat) : Nat := (if i < 1 then 0xc000071260000000060f550a9a06e117c0000b8eed129d18000000000000071ac203500000000f030d1a4816f907ea116604ee00bf10b409fa821310310f431da503c10d3c08a012d00008163211530b0f08e0000c0a2b0f321ce31280000d1a5b12fc1740000000000008120d90aa11091302114000040f1c149216ba0000000617f0000e072919ea191115dc093b094519b0964d0160000000010980000000081aee12ba10f40ab0059a1c7714220f7f1c6d12501c100000000014d313d3037416760e1000000000000d183611d8057007030507913104570ae815001d0000000000000a0aa000071b47011b14cd196c0d7109a50fe701e00003138d0c46034a0632181418e0000e089f1b0117b10b830bab07d4187015b00000031f0e5306ac05fc1ba002e6122001c9807e0e0e1dc6946a08c00000000a0d00000b15711130000b1d240a8012cf0c3c17e0000000020ce0000b0760000c0f0d0e720b580cc0000c1b7204f0000f8560046e0db70827147d10cb1880000f0f90000000031a70000000020bf00006001a1120000b0e680a071c2b0c9519fe0280000206f00000000d1b6b10ab173a14f000030fc0000219930c00194909591af8153901020400106f0600000000000009056e07991a29156106800000000f09e108f110ed15930eb30c7581f0039218ca026a182c03da16180fbf01571bfc02710520000c0dd9914515c2111593970ad00000000000030e8b04700000000200d303200004172e0654069808b00000000317800004042b0d950781048d09910c2e061916cf0b90000b03f8012a0b791050000b14a000000000000a0200000e0e900005062803b4100f108201810b1f944e1b8000020ca0154000050550088e11e0000f0b60000000060060000000090810000f097d1090000a0cf804400000000000030d800000000704151070000000021a381d5e1d1b13450c8b02c000000000000e11701b960ed0000419761b331c5f1b1d11b50090000f104d043f0ac20bc105d000000000000c019d0be909df024c0a5c193718f7131e0de908d103e400c60d2505a000060a3b1b270c6510d1096d04d000000007143d1a9212ef049d0e3801b089b7184213ae9bde18d11d480140000a077a04c006c00002171d15f0000000000000000f08471c000000000000070f601c9514be13b0000705bc004a0eaf16940d1907f015a0000f136a1cd000000000000c1ada18531a8d198a073000000001146302be17900008140546045003141a072c115014b0000445031012070010480d00430090820402820041014ca110bc01401021403041006c01ca00634404a0400000880420061400430430030c02c02020820011000010002401000c500100e0001400022850451000400820820401480c01020420020c3001007182197041001041 else 0x21db000051dd10649189900ac1d6805341d88085000009451054c075516a507b0000703800000000000000003022813f20e200000000d00350b2a195515e8162419a0000000021bec07a000061cb80a7f1241192e09c80cb0000f02d61d3e0a1b1236148f071d1655025d01381a1702f0000813241ab000001580000c0920000000000870000317500000000017d106700000000000000000000d8ed8058d00541bb9029b008a1510000618b5090e1602166c06d41a6a03a414e70ec40f260a60000200e601ac11aa9210000f144d170300f3186813571c40000c0dc20d5404a000000000000a0fa0000504b0000505e710179bc001d40b4902340bd0000d1d9c1180000b13c0000b002000091d7b0f8f1550000d0a4000000000000000030910000f0b3a16e21778152819000000000000021a000009139416810c59102b137e03341b5000000000000611f307ce1272133b0c100000000000030660000206b30fd00000000b0d421c8000011760000e9150000219d61aa0000a051000058ef00000000517a0000908320e4a19c811ce91b000030af01413080000071c3712ae02aa074603660dfb01790ff00000000000000000000318a0000e1ca81cf0000c1cc016df0bb70d600da0000000088cd113ef1193086405)

def n11 (i : Nat) : Nat := 0xb0381a050185868e08030841703824602e80402c0e1e81c0a301940200e060f40608320c207008034083d01820c83090581810078140e09018c246c0803c0608320c86100b038200d0281c060918482016070340e050480c6120703022041e80c103080401a04300f412021840200e360840a09010c8612218585c3440f42e040e0c943d0b818303250401c0d0480860d038141035018c1a0503064120318340e0504808663068240430303818170481c0a021a40200c078140e09010c20100705c12030281865103824043218281e0702824043068083c3038141014182064302d939f317de2b194da74c9387afc1d1b4d648bc96028549483cea1b42ce4686689b0c01000b800ffe77503ff8cd40ffe11503ff5e140ffd83503ff5cd40ffd81503ff5c540ffd31503ff5c140ffd30503ff44140ffc73503ff1c540ffc31502ffa2140dfe77503f78cd40ff611503fe80140bfd78502ff60d40bfd81503ef50540ff930502ff1e140bfc83502ff20540

def x11 (i : Nat) : Nat := 0x3e0f80000000280374098c46400010170000302308137839dc4980000c24142248334c05c830ec1c2809303cec442c2e24115427941e1c3f8c463c30bc3f480d00022c02e418e0294c075407342d0004c000240ac4238e0d140f8036ac43c43d40000c3aec2b400000000000142740003441000008351a312422080b943dd8166c21c000000034050c0840000000000000000000000000001c24dc2b282bfc1b30179c3140003c259c1f68107e15144b640a641d5c17dc392011cc43502f9c0e242cc0001c4840019440fc02b4271436c0000c4bb8144000000000000000384180000837800034408000242c94236c4288470c1540002801000000000000282c00001c1cac1580000000000000002c06c00000002c0dc00038100000340d9827c0003049400000001834382eb03a9c4a8000000038004000283d381b4000003a444a443e00000416c000100a80000000301ec42c5c13c0001c188c1dc000082e544044065c249c190e19304540002c1d2423f000c00c00001038bc361818440ebc31c03a3c10e44274364842c0000000301e9c34f40540000000303248206032202dc0002015d046c0003e315c07e043301a9011042f64002c1cc0000c45c820b232943e7c05ae29f0445c3f00000c1c400014493c301828203040000e2180003c16844504420c376c37d80fc00034068c0d5011884b082d843b40488000303c78396c28c03e80000c41400000000000283ee441ec35f446ac2f0c20f01280002c49c41b8445881a0000001a4000303c00003838f429941ac02adc1800000c0e40000000000000001444800000000000282d5c131025e0212025400ee03980003c08983c800000003426080a0000281fc0001c140000000000124000102ab8381c217c04804acc35bc2ec8400810801208139017583848480019a00818045437000030252c35600f3026482688228000282a54025809c0003414940c90286834801d8c01f81f901e401f0c19c000042b9431380c503180000000180b7047800000000000000000001c34400000000000103b000024202847c0000c14d8476803c83da63920194000102fc00030163812f04a041bd0040843bc014044fc22f803842180001032f026c000003bc0000000280b1e08a0288000003fc033a40cf4008c08e433f42440003809700f40000000003b80000000120bdc06000780002403102928332c2a1048c4b0224a1034022291460821cd0040002402d30407012cb01c0810d20000412c80cb0000094c20020091ce08000314000b10100004400000604b1000000045400c0182104046201400002043040

def n12 (i : Nat) : Nat := 0x2030401182ffd40

def x12 (i : Nat) : Nat := 0xf05f16414f1a703000a0db11a04000c18000e0700000000030a50211200080b00061900000011b401a0f000508e1550c00000001300000000011700028610980ea10300d53010600

def lv : Nat → Packing
  | 8 => (73,5,7,0,0,10,0,n8)
  | 9 => (478,4,7,0,0,14,0,n9)
  | 10 => (303,3,7,0,0,14,0,n10)
  | 11 => (28,2,7,0,0,11,0,n11)
  | 12 => (1,1,7,0,0,0,0,n12)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 25 109 5 14 7 3 x9
  | 10 => lookupWord 162 687 6 16 9 3 x10
  | 11 => lookupWord 103 436 6 16 9 3 x11
  | 12 => lookupWord 9 45 4 12 5 3 x12
  | _ => fun _ => none
def g : SeedForest := ⟨⟨383,12,fun j => sampleSeed383[j]?.getD (0,0),cols,autosSeed383,lv,ix,fun _ _ => false, by simp,none,none⟩,seedAug 383 0 4 seeds⟩
def rows : List (Row × Row) := [(16,17),(1,3),(2,6),(4,12),(1,17),(1,33),(2,66),(8,264)]
end S383_0_4
namespace S511_0_1
def cols : IndexTree ColumnInfo := (.fork 52 (.fork 26 (.fork 13 (.fork 6 (.fork 3 (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7)])) (.fork 3 (.leaf [(4,0,507,0,12),(5,0,506,0,8),(6,0,505,0,9)]) (.leaf [(4,2,440,65,7),(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6)]))) (.fork 6 (.fork 3 (.leaf [(8,0,503,0,12),(0,8,227,276,8),(9,0,486,0,8)]) (.leaf [(10,0,501,0,8),(12,0,499,0,9),(8,4,369,130,7)])) (.fork 3 (.leaf [(14,0,497,0,7),(10,4,369,128,6),(15,0,480,0,4)]) (.leaf [(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11),(19,0,492,0,8)])))) (.fork 13 (.fork 6 (.fork 3 (.leaf [(21,0,490,0,7),(21,2,424,64,5),(25,0,486,0,8)]) (.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5)])) (.fork 3 (.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12)]) (.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (.fork 6 (.fork 3 (.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8)]) (.leaf [(49,0,462,0,8),(48,1,460,2,6),(50,1,460,0,5)])) (.fork 3 (.leaf [(56,0,455,0,7),(64,0,447,0,13),(0,64,189,258,10)]) (.leaf [(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8),(66,1,396,48,6)]))))) (.fork 26 (.fork 13 (.fork 6 (.fork 3 (.leaf [(69,2,440,0,5),(74,4,305,128,5),(83,0,428,0,7)]) (.leaf [(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (.fork 3 (.leaf [(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (.fork 6 (.fork 3 (.leaf [(140,0,371,0,8),(132,8,99,272,6),(138,4,369,0,5)]) (.leaf [(152,4,353,2,5),(160,0,351,0,11),(160,1,332,18,6)])) (.fork 3 (.leaf [(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (.leaf [(172,0,339,0,5),(176,1,332,2,5),(198,0,313,0,7),(256,0,255,0,12)])))) (.fork 13 (.fork 6 (.fork 3 (.leaf [(258,0,189,0,8),(260,0,251,0,8),(264,0,247,0,9)]) (.leaf [(256,8,227,20,7),(268,0,243,0,7),(260,8,227,16,6)])) (.fork 3 (.leaf [(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (.fork 7 (.fork 3 (.leaf [(296,0,215,0,7),(40,256,151,64,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (.fork 3 (.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,8,163,16,5)]) (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def seeds : List SeedItem := [((4,0,507,0,12),255,0,4,[99,81,115,130,65]),((8,0,503,0,12),255,0,1,[115,82,98,131,66,16]),((16,0,495,0,13),383,0,4,[83,114,99,33,16,64]),((32,0,479,0,12),255,0,4,[118,101,133,50,33,16,64]),((64,0,447,0,13),383,0,4,[98,118,81,130,50,65]),((128,0,383,0,13),383,0,1,[]),((256,0,255,0,12),255,0,1,[])]
def n8 (i : Nat) : Nat := 0x29431e2d6d750bc54d8254910c7ca751d02f153609524431f61d1740bc54d8254910

def n9 (i : Nat) : Nat := 0x152100000cf082a4200008c20991040000006810538400001002000397833b2712feb66e5a45fde9a18d79655108c0ac98843c2814026ed99aa9b04a95328863af5b1c42ad5360910c7dce238055aa6c12218ff1c1700ab54d824432edbb25e2a6c12a48867cb750bc54d82549109fb2e8978a9b04a92219f69d02f153609524427e999aa9b04a92608857d62f553549804c11097b666aa6c52a4902217f62dd60d5254520442bed17aa9aa4c02408861af5b14caed8a4e51082fe6daf955352a92218f715a32d8a545204427ec1b8a9272a8a408857e8534ba6c95148110beb0bed98a92a2902215f60db6295254520442bec17a9d2a4a8a40885dd8365c35495148110bf90a6974a92a290221cf60ba549514c5204433ec386e12b650a408877c854d5252ca148110

def x9 (i : Nat) : Nat := 0x108a280000400

def n10 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x9ff11caed8948110a7f51caa989481109fe8bc5498948110b7b94caed39481109fb94caed3948110b7e92caed39481109fe92caed394811097ed2caed394811097f8cb629394811087fccb629394811087fdcb5693948110b7e8cb54939481109fe8cb5493948110bde97caed5248110bfe11caa95248110b7e8c962d5248110b7e8c96cd5248110bf6acc54d5248110ff498354d52481109ef96caed8148110ff6152a6551481109ff0cb62951481109ff0bc4e95148110cff0ba4e95148110ff61524e55148110f769524e55148110c7f8ba4e55148110ff615a6c95148110dfe1b36c95148110dfe0ba6c95148110f7e0c96c95148110ff62cc5495148110df6abb5495148110ff62aa5495148110ff618a5495148110ff613a5495148110ff61c95495148110ff61c35495148110ff61835495148110ff60ba5495148110ff60c95495148110ff61526055148110bfb14c2e95148110cff1b32e95148110df695b5493148110cfe8ba5493148110ff61525453148110aff0ca5453148110cff0ba5453148110d7e95b4e52148110bfe15c4c52148110dfe15b4c52148110ffc13a4c521481109fe8bc5498048110bfb14c2c58048110bf715c2858048110bfb14c2858048110ff61514855048110bf715c2855048110bfb14c28550481109fb94caed3048110ff49535493048110ffc1314853048110bf715c2853048110df72cc56ca148110df718c56ca148110df71ca56ca148110cf75ca56ca148110df718a56ca148110cf758a56ca148110df713a56ca148110cf753a56ca148110df71c956ca148110df718956ca148110d7758956ca148110df713956ca148110df718556ca148110df71c356ca148110df718356ca148110df715356ca148110dfe1c256ca148110df65c256ca148110df655256ca148110df71c056ca148110dfb18a52ca148110cfb58a52ca148110dfb15a52ca148110cfb55a52ca148110dfb13a52ca148110dfb18952ca148110dfb15952ca148110dfb13952ca148110dfb18552ca148110dfb18352ca148110dfb15352ca148110dfa55252ca148110aff2cc568a148110aff2cc4e8a148110aff15c4e8a148110efe2aa548a148110ff6153548a14811096f96caed8980110c3be8852eaa4e510c73e5552eaa4e510a7ad4caaa224e510f76152a655148110cfe0ba6c95148110bf62cc5495148110ef62aa5495148110ff42335495148110ef60ba5495148110aef16c2e95148110afe0ca4c521481109f72cc56ca148110cf72aa56ca148110d7729956ca148110db728856ca148110df523356ca148110df61c256ca148110df615256ca1481109fb2cc52ca148110cfb2aa52ca148110d7b29952ca148110dbb28852ca148110df325552ca148110df923352ca148110cfb13a52ca148110dfa15252ca148110 else 0x8ff51c2e932a65108ff90c2e932a6510c3fd8a62eaa4e51087fd8c56eaa4e510c7bd8b52eaa4e510c7bd5b52eaa4e510c7bd8a52eaa4e510c7bd5a52eaa4e510c7bd8552eaa4e510d79d4b4eeaa4e510c7bd4b4aeaa4e510d7d53b46eaa4e510d7b94b42eaa4e510cfb94b42eaa4e510c7bd4b42eaa4e510d7d93b42eaa4e510d7f11b42eaa4e510cff11b42eaa4e51096fd6caed8a4e510a7bd4caed8a4e510c7bd4caed8a4e51097dd3caed8a4e51087fd2caed8a4e51097f51caed8a4e510c7f51caed8a4e51097f90caed8a4e51087fd0caed8a4e51097f51caed5a4e51097f90caed5a4e510a7bd4caa9894e51097f51caeda24e510a7bd4caa9a24e51087fcacaed824e51087fdbcaa9824e510a7bd4caa9824e51087fd5c2e9824e51095fd7caed524e51087fcacaed524e51087fdbcaa9524e510a7bd4caa9524e510a7ed2caa9524e51087fcca62d524e510a7ecca609524e510c7f58a46eaa4a510a6fd6caed8a4a51096fd6caed8a4a510c6fd6caed8a4a51087fd3caed8a4a510c7ed2caed8a4a510a7f51caed8a4a51097f51caed8a4a51087fd1caed8a4a510a7f90caed8a4a51097f90caed8a4a51087fd0caed8a4a5108dfd7caed5a4a51087fd5caed3a4a510a7bd4caed3a4a51097bd4caed3a4a510c7bd4caed3a4a51097ed2caed3a4a510a7f51caed3a4a51097f51caed3a4a51087fd1caed3a4a510c7f51caed3a4a51087fecc56d3a4a51087fd8c56d3a4a51096fd6caed894a51097bd4caed394a51093fd8c26eaa6091097ed2c26eaa6091097ed2caeda96091087fdc92ad53609108ff9c02ad5360910c77d5356ca96091087fd5c4eca960910c7dd534eca960910c5fcc95eeaa5491097ed2c26eaa54910c5fd7b26eaa54910a5fd7caa9a95491087fdac2e583549109f6cbc54d825491087fecc4eca95491087fd8c4eca95491087fd8c56ca94c91093fd8caed39601108dfd7c2ad53601108dfd7c2ad3160110cfb5a552ca160110dbb58552ca160110cfb5a252ca160110df715b540a160110dfb14b540a160110a7bd4caaa994c1108ff51caed8a4c11087fecc6e58a4c1108ff51caed5a4c11096fd6caed894c11097dd3caed894c110a7bd4caa9894c11097dcbc54d894c11097f90caed594c110a7bd4caa9594c110a7bd4caa9294c110fb598554d804c1109fd8bc54d804c110fbd1814c5804c1109fd8bc4c5804c1109fe92caed8a481109ff11caed8a481108ff51caed8a4811087fecc6e58a48110bfb14c2c58a48110afb54c2c58a481109df97caed5a481108dfd7caed5a481109ff11caed5a481108ff51caed5a48110e775512e55a481109fb94caed3a481109ff11caed3a481108ff51caed3a4811087fecc6e53a481109ef96caed894811096fd6caed89481109fe92caed894811097ed2caed8948110) else (if i < 3 then 0x79cf9700d00593ce402c0d87e73e5d03bc0c4f39f2e81de06279cf9700ef0313ce6c5900781a4c0074de5ce4503be720165962656c959e556951651c93fe4ee93164b4922e46e917644090be41e90363f08f4e3b68e963888dde3668d8635c8d5e32e8c4630c8c1e2f68b662d48b0e2be8ab629089ce26288e621c87ce1d686e619c85fe16e854613483ce0d682b6084819e04a80b60047f9dfca7e55f607cadf0e7bc5ee07b0dea67a25e78799de5678b5df8776ddbe7685d8475cdd5674e5d1c73fdcd672e5c9071cdc567085bec6e4db5e6cd5ae86afda726955a2c680d9da66f59a0663d97e65b595064fd92e64458f4635d8ae6245874615d83a60758005fbd7ae5de57505ccd7165be56dc5acd69659e5644589d5fe57855c4569d57e5495508537d4b65265458508d41250053fc4fad3da4ef53a04d7d3424c052e44aed29e49d5240488d1fa46e519c45cd156451512843cd0e243450b4425d08641a5064411d0364064fe43f1cfaa3e64f7c3dacf423cf4f203c0cef23b84ec43a9ce8a3954e50392ce223814e0037ecdea36d4d9835ecd6a3594d54344ccea3364ca4321cc523134c24304cbea2f04b8c2d5cb222b84aa029aca362864a0827ac9e627249b8269c97e2584944246c91624148e8232c8ae227488c21bc83a20447f41f8c7de1f047a41e1c7761d6473c1cac70e1bc46d41b3c6ca1b146c01aec6aa1a6468819dc666192462c183c5f217845c416fc5ba16d45a4167c59a1654590162c56214e4510139c4a611c443c101c3de0ea43680c9c2f20af4294097c22a07d41c0062c15604b40f8030c08e0104000d77db554d82a651097fcbc54d82a6510f76d5360952a65108ffdacaed53609108ffcacaed53609108ffecc2ad5360910c7fdc92ad53609109fbdc42ad5360910cfbdc42ad53609109ff5c12ad5360910cff9c02ad5360910bf6cbc54d8254910af7cac54d5260110f75d53549894c1109fdcbc54d824c110df5d8b54d524c110ff4d53609524c110ff5953549804c1109ff8bc54d8a481108ffcbc54d8a48110ff69535498948110f76d5354989481109ff98caed5348110ef6d536295248110bfeacc60d5248110ff698c54d5248110ff4d8354d5248110f7e9524e58148110ff69535498148110bff2cc60d5148110ffe1836c95148110ff69835495148110ffe1526053148110f7e9854e52148110ffc98354d2148110ffe1854c52148110fb798554d80481109ff8bc54d8048110ff69535498048110ff598554d304811087fd9c2e983a65108ff90c2e983a651087fd9c2e982a651087fd5c2e982a651097bd4c2e982a65108ff51c2e982a651087fd1c2e982a651097f51c2e982a65108ff90c2e982a651087fd0c2e982a651095fd7caed52a65108ff90c2e952a651087fcca56d32a651087fd9c2e932a6510 else (if i < 4 then 0x1b100085c000ac40180422f4df2ef16f0d0282b800158bcb812806c7e9a46c096370202c138001588007c585e720c803c3051015101180a8bcb81500d012c9e73e5c0540ac4f39f2e81d05d250680a8802405440121b0000c15800158803005440121009080f07c5819012c7e5ce2c0680964067034130682b0802410c4e0401220010b80006080300b04e040122001f16179700a8258dc080d0403402a096305301e103400f0bce40248741909e5db7603c0bc4f4d1a7043f2ed22d06f16381e02183280f13ce41900787e9be5de04069e7243a6f39d220431da6f9cf9769168300f1bce41485e5ce9a066372e0370441ea681b8220c19c06c40240ac20010f9707cb8200a0682f2e0f03040300b04050096202305e138b00a8258c054110400202a2001f39138101988007cb8400a0682001081e00b82303200d97ce7c5bcb81109e1a2c6096301504b179702e0841010c4c0c0862f2e0d204b18010160a0101585e73e5d0160bc480405617970220140c41010c40ca0422028044179c81a82f0f5342a416bc5bcbbce6c34e01c03c2f1680b068183440982f0f8000b05a1a075e5c0a81925d02e000c9c36220087800203220d91040040545c000582f2e02f01706701b2f000160b537ce7c580d00b0bc000ac2f2e01504b1f000160bc5b8340b07e9be5c02a096401504b17977830258fce7cbbc181500b0a064058280405402c1805016080b03c000682f2e02f06701b2400860043c0c058202804b1016078000d040e0602c1016078000d0402e08c0c80364e0602c1006016080b03c00086202c0f976a681a0c1c0c0582e0602c1016040b03c000862e0602c100f0160bce7c5819011080069178b0218c0f40844006030648b01bce7c5882620362804040100e84003a1f4df1660604b034280a30301a0d0002018a054000864a00034179ca8101c00d901e721900863d0208058050200fcb808411c7e9a06be2c08e4f4df39436043279cf9702f0219016bc5bcb8087ce4be5c014c01e2c0805a0600af39436279779c81081a100b00d054001a060401000500d0440010310a006030060e4080d04800068200b902043180150300200e2801e06101281a08094204a1e0602c16007a681c0259002c0640d070020342e060810040f45e728022401007120087c590045e2c8022e060f97703090078005e2dc0c200000070007800204a14010a0087ce50045e72802240101a17977030b818362dc0c20001c00100000079cf8b0b18fce7cba0747e73e5d03a3f39f2e21d1f9778b012805f9c97cbbc5bce40949e5de2c191e724f2ef1600bf39279778b79c8fcbbc5bce40949e73e2dc0c0c604a5f39f2ef1600b0132f9cf9778b70313ce7cbbc5802c9e7201606c3f39f2ef16e06279cf9778b70313cbbc5bce402c9e73261e2c0164f3901d03601a2 else 0x2c34361ba9a20005040903e5de2c1523d0de4d1067874379342a4619e1d0de4d0a9180a0678a4883e5c0462a0d0d068408c2047a9a2e0601410548118bcb83e5c0462e060811840007973030048fcb80244006810743402440b220838183c0c0462023d4d170307c188d812c6e000562f2e037044181182f0a81006c4e0406820050)))

def x10 (i : Nat) : Nat := 0x1647301400c8aa000127490c8146100000001cb2e51ba60000000000f04800201b04bf097844000c520000000e9c613822005000aa56f2c0003c09c540005021c0c000e00883fc2e000e029030000

def n11 (i : Nat) : Nat := (if i < 5 then (if i < 2 then (if i < 1 then 0x8ce22442bf65cb0b112215fb2e58388910afd972a9c448873fa88a6600443bbd2ad3300221df68ce9980110efd4454cc00887b7a8895600443ded4446700221fd69563380110f7d51111400887f6a5588a00443fe519c4500221ff48ce1180110ffc44508c008877f13984600443bf894c23002215feaed8980110eef4aac4c008877da3362600443bf511313002215feaed5980110efb466acc008877ea22566004433fc5d2b3002215feaed3980110e7f5109cc0088777a554e600443bf511273002215fe62d3980110aff2b69cc008867f8ba4e600442bfd5da5300221cfea212980110eef4aa94c008877da334a600442bfcc5a53002215fe56d2980110aff27694c00885ff2bb54600443bf94caa300221efca215180110ffa466a8c00887fe22254600443bf8c4aa300221fdc5495180110dfe174a8c00884ff8ba546004427fc5d263002218ffa22aa4e510cefcab552728847fd8baa9394423feadd549ca215ef52eaa4e5109f7a97552728867bd4baa9394433ee9dd549ca211ff4aeaa4e510cfea37552728857f90baa9394423fe85d549ca219fe42eaa4e510e6fd112aa728867eeaa889394439f7444449ca21ddb956224e510cfdb15112728847febb629394423fe5d3049ca218ffa22aa4a510cfbc67552528847fd8baa9294423fe9dd5494a215fd46eaa4a5108ffa37552528867f51baa9294433fc85d5494a21cf7a22334a510eebcab19a528847febb629294433ef19b1494a211ffaed3a4a510cefcaa9d2528847fd5b4e9294423fe5d2a694a211ff4aca960d108ffb37553048867de332a5824423fead952c12211ff4eca9609109bfaf7552a48867de332a5524423fe9d952a92211ff56ca94c9109fea3755300885fb54b285804427dea5d54982211ff6e58a4c110d7f51155240886f7a55aa9204437ed19d54902217fc46eaa481109fea3755240886ff11baa9204433fd5553290221cfea229948110eef4ab4ca408877da33a6520442bfc9dd3290221dfa54a9948110f6f5112aa40887bda888cd20443fad2ac66902211ff6e58a481108ffb729d2408857fabb4e5204433fd5527290221cfea213948110eef4aa9ca408877e9524e520442ff55daa490221bfaaa95248110f7d510a9240887fca3354920443fb4a9aa490221bfcaa95148110efe532a8a40887fd23354520443ff0d92a290221fda5495148110dfe174a8a40884ff8ba545204427fc5d26290221bfaaa92148110efd53290a40887bea8848520443fe519a4290221dfa4e52148110ffc26290a40886ff2aa28520443bf94c94290221efca20a148110fee4aa50a40887fd23328520442ff8ad942902217dd56ca148110bf6a9650a40886ff15a285204437f89d14290221ff8548a1481108f7a9755272887f615254520442fb8ad942902217ec52ca148110 else 0x219ff4e98948110ffd2a4c4a408877ed5262520442ffd5dab2902215ffaed5948110cffd54aca40885ff98b56520442bfec5ab2902219ff6295948110cffa74aca408877f98956520443bfd5da72902217feaed3948110affd769ca408877faaa4e5204433ff5527290221dfe62d3948110bff3169ca408857fd8b4e520443bfcada72902217fe56d3948110affab69ca408877f98a4e5204433fec527290221dfe5693948110cffab49ca408877f9894e520443bfcaca7290221dfe6153948110ffd2a49ca408877ed524e520442ffd5db0a902217feaed8348110bff576a9a40885ff98b54d20443fbcc2aa690221ff660d5348110ffd576a9240887feaaa549204437f7552a490221ffa62d5248110ffd314a9240886fed8a54920443ff49d2a490221ffa6e55248110efdb72a9240887fe9b354920443ff4c1aa490221fdb54d5248110ffd362a9240887fe8b954920442ffd5db02902217fe6e981481109ffb74c0a40887bf98a605204435fec530290221dfe4e58148110ffd2a4c0a40885ffabb54520443ff9552a290221ffca655148110bff316a8a40887ff1ba54520442ffcdd2a2902213ff6e95148110ffe314a8a40887f795a54520443ff89d2a290221ffc4e55148110eff272a8a40887ff18354520443ff4d92a290221fdb5495148110ffe302a8a40887ff0ba54520442ffd5da62902217fe62d3148110bff2b698a40885ff9ba4c5204427fedd26290221ff64e93148110dfba7498a40887fe9524c520443ff8c0a6290221ffc5453148110bfdab690a40887fe98a48520443ff49d24290221ffa6252148110efdb1290a40887fe95948520443bf6aca4290221ffa4e52148110efda7290a40887fe98348520443ff4a9a4290221ff94c52148110bff576c0240886ff93a60120443bfcacb0090221dfe4e58048110f7f30ac0240887fe95260120443dfcc0b0090221ffa4858048110ffe162c0240887ff0a160120442ffd5daa0902217fe62d5048110dff314a82408877f98954120443bfc9caa090221fde5455048110ffd242a8240887ff0a154120442ffd5da6090221dfea653048110bff31698240885ff95b4c1204437fcc526090221dfe6253048110eff2b298240887fd9534c120443ff4a926090221ff64c53048110ffd24298240887ff0a14c120442ffaad94290221ffc628a148110dfeb1450a40887ff15a285204437faad14290221ffc4e8a148110dfea7450a40887ff18928520443bfac494290221ffc564a148110ffe27250a40887ff18528520443ff8c194290221ffc54ca148110ffcaa450a408873de888ce994439f7444454ca21ddb95622a6510ef9c67115328863fe884ea994433bf2aa754ca219fb8893aa6510c7fd109553288677e554aa994433ef19a554ca211ff2e982a6510f79d1119c44887f4e55) else (if i < 3 then 0xb755304884ffd3baa9824427fe8dd54c12213ff42eaa60910aff937553048867fc9baa982442bff5db52c12219ffaa9a960910cffb4ad4b048867fda36a582442bfe5cb4ac12213ff2ad5360910cff952d0b048867fca968182442bfead952c12219ff6a4a960910cffb4a54b048867fd532a5824427fecdd54a922177f5eeaa54910dbfaf7552a4884ffd3baa9524427fe85d54a92215ff26eaa54910cff937552a48857febb6a5524433ff55352a92219ff68da954910efdb04d4aa48857fcb968d52442bfe5cb06a92217fbaed8254910efdb72c12a4887f6d5360952443bf65cb04a92219ff6a4a954910cffb0654aa48867fda9685324433fed4952992219ff614a94c9109ffab755300884ffd3baa9804427fe95d54c02213ff46eaa60110cffd554cb008873fd85a6580442bff5da72c02219ffaa93960110e7fb0a9cb008857febb4a5804433ff55252c02215ff4ed2960110e7fb0a94b00885bfebb61580442bfedcb46c0221edf61553601109ff956a9b008857fdb9689804427fe55aa4c02213ff2ad32601109ff95698b00885ff55b285804437fad2942c0221efd614a160110dfeb4650b00886ff5a228580443ff8a8142c02219ff62a9954110affd7694aa08867fd8a4a5504433ff55532982219ff62a994c110cffab54ca608877dd53a65304427ff5db14982219ff6e58a4c110affb72c52608867fcb9629304437fa58b14982213ffaed5a4c1109ffb16ad2608867fdb956930442bfedcab4982219ff2e55a4c110dfe962ad2608857febb625304433ff5531298221df754d894c110affd76aca608867feaa56530442bff5da52982219ffaa9294c110affb1694a608857fd5b4a5304433fec5252982219ff569294c110efbaa694a60886fdd8a54d30443beedcaa698221fd7615534c110efb972a9a608857fdb968930443faea9aa4982213ff6e9814c110efbb1298a608877dd594c530443bee94a6298221ff54c5214c110eff532c02608877f92960130443dfcc2b0098221ff654d804c110f7f302c0260887fd93160130443ff858b00982219ff62a9948110cffab54ca408867fd3aa6520443bfc9cd3290221ffa54a9948110efdaa54ca40885ffabb629204427ff5db14902219ff6e58a48110affb72c52408877f8b9629204433fe5cb1490221ffc2c58a48110dfe962c5240885ffabb569204427ff5dab4902217fe62d5a481109ffb16ad240886ff98a56920443bfc5cab4902219ff2e55a48110ffe162ad240886ff4b156920442ffd5da74902213ffaed3a48110bff3169d240884ffd8b4e920442ffcada74902213ff56d3a48110dff3149d2408867fdb94e920442bfedca7490221dfe2e53a48110cff9729d240887ff0b14e9204437fa58a74902217feaed8948110affd76c4a408867feaa625204433fead312902 else (if i < 4 then 0x2443bfea9272c0221fdf54d5260110f7fb0a99300887fed824c950443bfea931298221dff609594c110dffab4c1260887fdd5360930442ffec5aa498221ffb609524c110fff2a4c0260887ff953629204437fea9b1490221ffe60d5a48110dffb06ad240887ff9854e920443ffca9b1290221dff54d8948110fff306aca408877fd8356520443ffcc2a7290221dff6153948110fff366c2a40887ff9b560d20443ffcc5aa690221fdf6155348110ffbb06a9a40887fed8354920443ffca9b0290221ffe60d5148110fff30a98a40887ff95360120443ffcc1aa090221ffe6153048110cffb0a9d5328867fd824ea994433fea92754ca219ff6152aa6510cffb06955328867fd534aa99442bfec5a734ca215ff62d29a6510affab694d328857fd3b4a699443bfaa8a534ca215ffaed83a6510cffb74c1d32884ffcba60e99442bfe5d3074ca215ffaed82a6510cffb74c1532884ffcba60a99442bfe5d3054ca215ffaed52a6510cffb74a95328877ed8254a994427fe5d2a54ca215ff2e952a6510affd76995328857fd8b4ca99442bfeada654ca219ff6e932a65109ff974995328857fcba4ca99442bfec5d549ca213ff62eaa4e510cffb17552728857fd5baa9394427feadd549ca219ff56eaa4e510bf7a97552728877bd4baa9394437dea5d549ca21df74eeaa4e510affa5755272884ffd2baa9394433fe95d549ca21dfd46eaa4e510dfea37552728867fd1baa939442ffc85d549ca215ff42eaa4e510eff21755272886ff90baa9394433fe85d549ca219ff62aaa4e510cffab5552728867fd85aa9394433ff5db149ca215ffaed8a4e5109ffd76c52728867fdb262939442bff5dab49ca215ff62d5a4e510cffb14ad2728867feaa62539442bfe5d30a9ca213ff2e9854e510affd76d12728867feaa68939442bfec5b449ca215ff56da24e510cffb14d12728867fd5a68939442bff5db049ca219ffaa9824e510cffb74c12728857fcba609394427fe5d3049ca215ffaed524e510cffd54a92728857fd8b549394433fedd2a49ca219ff629524e510efdb04a92728857fcba549394427fe5d2a49ca219ff62aaa4a510cffa75552528867fd83aa9294433fea9d5494a219ffaed8a4a510affd76c5252884ffebb629294433fed9b1494a219ff54d8a4a5109ffd76ad2528867febb4e929442bff5da7494a213ffaed3a4a510affb169d2528867fd5b4e929442bfeada7494a213ff56d3a4a510cffb149d2528867fd5a4e9294433fec2a7494a215ffaed894a510cffd54c4a528867fd3a625294433ff552b294a219ff4e9594a510affd769ca528867feaa4e529442bfec5a7294a215ff56d394a510cffb149ca528867fd5a4e5294433fedd30694a215ffaed534a510affb16a9a528867fdba54d294433fed4952c1a213ff66eaa609109ffa else 0xe79ce724e696e634e5d2e55ae4cce412e384e30ce2c0e21ce1bae142e0cae068e006dfe6df84dee0de52ddf0dd8edd16dcb4dc52dbc4daded9f8d996d934d8fed844d7a0d6fcd684d5f6d568d4dad4a4d416d35cd2a2d240d1b2d10ed080d04ad02ad00acfbecfb4cf7ecef0ce62cdd4cd5ccce4cc40cbf4cb3acad8ca60c9fec9b2c8e2c83ec7dcc764c6ecc6a0c5e6c56ec4e0c43cc3aec30ac292c204c160c0bcc018bf74befcbe9abdf6bd94bd1cbc8ebc42bbcabb7ebb1cbad0ba84ba0cb994b906b88eb82cb7e0b768b6dab662b616b5b4b57eb4f0b44cb400b39eb352b2f0b2d0b29ab20cb168b0f0b04cafeaaf88af10aec4ae78adeaad30aca2abfeab5aaaa0aa3ea9c6a94ea8eca8a0a854a808a77aa6eca65ea5a4a500a45ca3b8a36ca30aa266a1eea160a0e8a0449fe29f289e849de09d949d069c629bd49b469ace9a4099b2995098d8984a977a96d6964895a49516947293ce932a927091cc913e90b090388fd68fb68f288e9a8e228d7e8d068ca48c168b728ace8a1489b2897c893088e48882883687be871a86a2862a85de853a84c2844a83d2835a82f8826a81dc8190811880cc806a7fc67f4e7eec7e5e7dd07d587d0c7caa7c487bd07b587ae07a947a4879d0795878ca7894784877d07742769e75ce755674de747c7430738c73147270720e71967176714070f47066701a6fa26efe6e9c6e3a6dee6d8c6d406cb26bf86b806ac66a38697e68da687867ea67886752671c66e666b0667a664465f865c26576655665206516650c650264cc63fc632c625c618c60fe60705fe25f545ec65e385daa5cda5c0a5ba85b5c5ae45a5659c8593a58ac57f25738567e55c4550a5450540453b8531452c8520e516a50c650224f7e4eda4e364dd44cee4c4a4ba64b024a5e49ba495848b44810476c46c84624458044dc447a442e43a04328429a42224194413240e6409a3ff63f523e403d2e3c323b783a663a30391e38d2384437b6375436b0360c356834c43420330e326a31c6312230682f982ef42e3a2dd82d8c2ce82c442b482aa4299228ee280827902718268a263e25b0254e24522406238e232c22882226216c209c200e1f6a1ec61e221d7e1d1c1ca41c161b721ace1a6c19c8193a18ac18081722165215da154c14d4145c137612d2124411cc113e106e0fb40efa0e820d9c0cb60c280b840af60a940a4809e6096e08b407b80756070a06a8063005b8052a04de047c03ee036002e80244017400ba0001dff54d82a6510effb06a95328877fd854ca99443bfea93129ca217ff62d524e510ffdb04a9272886ffd53629294437fec1ab494a21dff60d594a510effb0a9ca52886ffda568d82442fff5daa6c12217ff6ad5360910ffdb64a9b04885ffcab54d824437fec5346a9221bffaa98354910ffdb66c12a4887feda36095))) else (if i < 8 then (if i < 6 then 0xe645c5b9c81b0c812d416f9cf2e05a02cbc8b9cf2e0aa02cbc8b8b739e5c0b0291b9c85286c3c9b81b9c85206c094dc8b9c8360a4467229f80702e9bc3711606e5dc58142d86c4886c3e9ac342884806c5e9a0942083622040b5c3797739068150fce40e8320a84e45c1ba6815e5dce41c00f4722c1bc1aa6f39c301599804b4e00e73cbb81716c0c6c00c8b9cf2ee05c5b031f0030de73cbb81716c0c7e9bce421f16e5c12c059fa6f16e720839704b0167e73cbb8b00b2739e5d81b8b00b2f2ee738038b404c0c6645cbb9ce00e2d013031d86f2ee738038b404c0c7e72c341b00b272e80881b00716e72c88fc0a9172ee73c5b031b8150de5dce78b6063702a1ac8b97739e2d818fc8b8685cc0dce70c54d088cc025aba6f22a1b81b9ce180accc025a797739a1bc5b03179750dc01ce78b606372ea1bce78b6062f2ea1bce78b6062827e5c81a86f4d645c5b9c838042ae5d80064522e73c5a031f97406a45c5805f39372e80dc5b9cd222f2e80cc378b739a4460161220374de2cc3797739042901780281739e2dcbb03522400b04b48b03739e5c0138b239cf2ee2d48b031786a0004d48b9771604bce43281b500b091d350371604bce420021a60ae73c590072ec0c094dce78b031001cba9100b3f39e2c0c405f2e0266e5dce78b00b27390160d8701b9cf16a60461b01b9cf16a605e9ac3603716a61ce41c021474d027c8a03716017ce58684326006d7ce79700b0344e7202c1b0f9ce06e2d4c09ce591716c0d4c0bce586e06e2d4c0a01f9cf2ee2d819911b9c8320343e720741901a200164581b9cf16a606e7200586e06e2d4c0c02f9cf166454c0bd3791706e5dce79801d38040904890374de1bcbb8b7394f4de1b81b9cf162600f41b23a6f22c0dce49801d07a0d913d613d413d373c933c5d3c273bf13bd13bb13b653b193af93ac33a8d3a4139df39d5399f393d38c5388f386f383937c13775373f370936bd365b360f35d935b9356d354d350134b534693449342933dd339133713351333132fb32c532a532593239320331b73181311f30652fed2f492ea52e012d5d2cfb2c992c0b2ba92b892a772a2b29df29932897284b27ff27b3268b2629256f253924ed23f122df21e32181214b20ff209d1ff91fad1f4b1ed31e871e251dc31d611d151c9d1c251bd91b771aff1a871a2519c31977191518b3182517ad16c7164f15c1151d14bb141713b5132712af122111a910ef107710150f9d0f250e970df30d7b0d190ca10c130b010a1b091f08a707c1070706790617059f051104150303028b023f01b1014f00ab0032ffa4ff2cfe9efe26fdaefd36fca8fc30fb8cfa90fa18f9a0f912f884f7f6f77ef6f0f662f5d4f546f4a2f414f318f232f1baf142f0caefb8ee90edd6ed32ece6ecb0ec22ebaaeb1ceaa4ea16e8eee88ce82a else (if i < 7 then 0x60b09d3405f39a1a0d816180081dc0c06898000388008071001a0420020f45ce400880081a171603a0047cbb030b97001c0c3c0c1e2d81840002816001722e0d435a6f39e5dc03987164f22e1ad379cf2ee0141b987164f4de1bce797700a0cc8b987164f4de44c379cf2ee0141b987164f22a1bc19a6f3986c6e9b43783322e730d8dd379150d60dce61b1b9170da0cd379cc36374de1b4199173986c6e9bc8a8330de730d8c05f8b739e5c0b0291b91700e05435a6f39c0dcbb8b27a6f00e054379ce06645cbb8b27037392ae4d89ce4291361d0dc0dce6911362f22e1bc19a6f3986c6e9bc3783322e730d8dd379170661bce61b1ba6f22e1bce583436370de0dcb9a6f39e6148b0c2391706e5d435a6f39e618611d378372ea1bce798322c308e45c379734de73cc283618474de1bcbb9cf30a0cc8b0c23a6f22e5cc379cf30a0d8610c379cc361f3960d0d87d379130de0c8739c8363f3906c02c75379170de0d0139cf2ec308a9bc3783739645863971ea6f22e0cc379ce18e5c7a9bc8b86b06e73863971fa6f0de0dce79771604a7e9b48b8330de73cbb0c1fa6d22e1ac1b9cf2ec307e73cbb8b025250de9bc880ef06e5d0739cc32c30ae454378334de73cbb0c1fa6d0de0cc8b9cf2ec307e9bc8a86f39e5cc1b0c1da6f22a1bc1b9cf2ec307e9ac8a86f06e73cbb0c1f9cf2ee2c04c9d379170de73cbb8b00b3f22e1b419a6f39e5d860fd3786d06645ce7976183f4de4541986f39e5d860ed379170da0dce70c72e3f4d645c368372ec31ce4fd379130da0dce7976183f16e5dce412939c83604a3a04d3797739a45860d40b97739a45860b4098372ee7348b0c19a6f39c31cba911583502e5c0979ce183739e2dcb812939c83604a3e720d8098f91706c1ad379cf2ee2c7e9bc1b06b22e73cbb8b1f9170601e04306f160acd379cf2e0d00799d3407810047c1b8b60d645cbb9c86503cce9bc8b8300362c14f9701de720e00aaf8360de9bc8b977390680750c5801f4de45c1b06f2e43a1939c83802ace728d85d3407810e4402706f16e5cc1b9c86403cce73cb90e8f9c866e2dcb825813374de45ce7973180266e73cbb8b60d260de0d489a6f39e5dc58fd379160de73cba837163f22c1ad379cf2ea0dc58fd3706b22e73cba837163b4de4583683739e5dc58e00417f2202fc1aa6e0de73c5b97067036ce440738b739e5c078291f9170dc0cd379cf2ee2c7e9bc8b0330de73cbb8b1da6f22e1bc5b9cf2e0be02d1d3586f22e2dce42b72e08802d3d379cf16097cb82200b3f4de45cbb8b70de728d805a39cf16e5c02c9c592600b1f22c0d435a6f39e5dc58fd370350d645ce797716382fe45c3400d4de7381b8b72e0ce06d75379160661bce78b72e3f4de4405c09d0dc0dc5b9cf2e0961900db3a6d0dc0cc8b9cf2ee2c7e9b81a86f2 else 0xc5800b021f16002c087ce79704ea9b818161a0273909d8181a02c370dc0013b9700b0966a9bce59170d0c5cbb5d82c454de2cc343172ed760b0fcb99170d0095341c04b3f2e090c8b86838c0012ce0a81282c1e060180941613a6f39e1a097030330367e73c37976060585e73cbb86e060680b0c09786be0d760b0a0478b30de9bcbb5d82c3d2269b81816138b7390080400e6060c80b11ce7970100394370302c3f3903b010086060680b0f8000582c1f4de5dc580800b0966e73cb9a6f1606f8180d9f9cf2ee2cf830302c3739e5dc5b030340586e73c58326060585e9bce797716c0c0b0dd379cf16c0c0d0161b9ce0606a0b09c5a86be0d760b0bd3424606e720d4161b9c848e2d4370374de5daec16279cf16e5cd3686e060587e9bce79750dc0c0b0cc8b9750de720e3037163f1640dd36868380966e9a12286a06071860259f86f02e73cba91716c0c7e45c0b9cf2ea1bc5b031e86f4de05ce797716a45819143781522e5dce78b6063b4de5dce78b50dc0c669bcbb9cf16c0d488dce78b40619010ca0ae0300b08640161e5c12291739e2c10cdcba0352260410c1619a6d2206bc582397a6f2ee2d489810430587e9bce79702b0865e721970c043274de73cba91716086680dcb986835e7348b8b1e0305ae5c0d586f39c307401c5ba6f390910191b04347390143211b10b101b1043a600b07c361904b180b0194c01610064190703e4581821f2e036502802d91716059ce6981e8160604a024161797522c0002c16169100c06c3e73c3405d22e2d4c01a1fa6f0de720d01617a6f390874c01617a6f39e1b0c825979cf0dc0dcb816140580ca600b09d379cf16c0dcb8161ba6f39c0dc5a9103436060580d07ce797716a45818b408128341e0004d0d820139cf0d0c5c58985220687e72409000340585c000500981b2739e4402f8b5300686e9bce405b22a6006cdd379cf16a600b0bd361b04b180b019408109002e000190d89cba86b22e2c10cb434317162040d0bd379cf166440d0a0981281b1843a600b07d378b043a600b0bc3423c0606406cbce786c060640b01a1812834100504a0d07d3423c060320d0bd379cc060320b01a1b9101461b02f9cf16a607e9a0501332261b02f9cf16a609017ce5868190685e73cbaa6e06058540581aa682c254dc0c0b07ce79771661b5370302c3f2e0090030302c2f2e645c3402739a9a0b0e02c060320584e1a02f9c83205850a8100201c40a81282c1f39e5dc34816060586a44808160da6e02a458181617a6f39e5d48986e0605870160319802c2302e72094161000e0600e3c0d8080e02c26060320b07ce78b1027c1818161ba6f39e5dc5881602c0c0b10f835da02a1a0b0bce797716c04f8286e060588e9bce797606a1a0b0dd379cf2ec0500005e060588039c5ba6f2ee73434161c0630201)) else (if i < 9 then 0x62722e721489b138b72ee72c889b0523722e1b81b9c9362b22e5dc5a9b7390a46645ce619056274de1a0d025919c8a7e2dcb81417a6f0d14fcbb8b0283004e05c03a6b0de2dcb86423a6f0d0043239804b37390b04d86484328651920847ce41e00be5c0942f04338040ca32022138173961a19422179cf2ee2cd3421979cd0d26c128988b9c85226c480c1e2dcbb110432014e2d5379705e61bce4e02b1172ee2dce4291ba6f0d1904d88d3586c4886c4e45c58320130885e9bc8860936234d6451061b1397004e1bc182a04b3722c080139cb0de0c16823f2e0a8ae1a011837220b58139773906a1515801020340584e739361902c24320582e0c0400ee4de73cba8682c4716e0c04286833c9a12ce15f9cd0de0dcbb0c02c3f39e1bb800582c2f0d01141819e4d0966e2cc37975bbc9a0b0c02f9cf0dc01cb8161802600172ee2d4378306805860469378305ae73cba86e184031e0dce726d0de5d4882a239770d2980b0948b86e4de5c150641b910130b5937970541827e7216b26813864078c4082a080087000400f1603a305020a82e73c37830578640b0dd379770dd8a02c16180434da0dc379804b3404c1a8700081e2f39e0c1421b02c2f4de73c1b0002986c0b0f8020202c1f0603a1438154dc1a0cc25a38b70666012c9c5b970428380b0bce7832360584003c59810fa6f06c0007414f02c1a0cc25a78b34dc1bc18017300967e73c59980562739e5dc5a0e0562f4de73c191b02c2801e2cc087c5b8304ea9bce79760d0588e0c13b9721c0965e735378372ec000b0dd379cf16c1a0d01282c3f4de5dc1812a1c0966e9bce797716c1a02c161fa6f2e0108702595a6f16e5d6ef0682c3739e2dd37975bbc1a0b0fc580434dc1b41b9804b3f160118368374de6012cfd379cf2e01741b0002c3b4de0d489f004b2f39e5d8602b138302481bcbb9cb4dc307a45ce42da36274de2c5320e02c2a0de5c1979cd06c306e0d0d8258f9cc0da600d016140282503630198000582c200b0180d878340202c1d4de737830682c2f39e0dcbb0682c2f39e5dc1a8154d05862c407306832058503d5340202c230203a1507ce78684f8640b0bd3786827e730c8161ba6f390230d81617030190583c01ce60202c241908e2c0d02f9c84f06a0b0dc3427f02a9b8181984b3f3966017c610d980340584086cc0160f9cf0d4640b080042005810b0373904a09c1a82c374de1a09f8160606612cf81b9c8352040b0bce5a6e06e1a00b9804b3d22a04c081613a68350900b09d3786f394640b0bce400b021f39002c08781b9c81c0220d4161ba681d023c0a86e0606612d1ce797716c0c408161b8b34da1b818017300967e9bcbb8b606e72408161f9cf2ee2dd341a802d760b11436813020584605d378b24c0585e9bce78b0340585e2cc081002c27160400b07 else (if i < 10 then 0xbe448d8218c0ea32096308c8c80d8e91700e040a00274de1a72397716e738da8337a6f3946c10c9c5b86f0269bc6397739a44846412c5ce51901b1d0de00013a6f22e5dc5889f39c6d41978100205269bcbb9150da0dc039cf30e2cc009c038174d6454368372ee2d8db9cafa6f2246c10c88c8258823232036369bc580f0562722e0d835a6f39e5c078ed342881e1b22e2c078161306b2201e07816159102303c362d8340a84b231643a0040a9306a1d02a0d09c580f01b1f1660c0400f01b2e0d60c0400f0342b0601207868778b01e03646048110e81e058543a8100f0380365e2d8340f04b201ee2c0d025938b01e03634098340f02c22044380300f139771669a00c3204b3716e72f141c0562f000aed3591706e2d83416739e5cae5dc58018640965e2c07401d4d0c812cc0c40e850a9b8341a04b3f1660dcb825938b01d04a00e910640967e5dc583204b272e69bc5a910640966e5d537068340965a9bc5b9cf2ea44078d8379cf2e1ae078bc580e80b00604e830640968e2d418018640965e5dc583204b2739a0dc583204b2b4de2dcba8304b2d06e73cbb8b3220ac6e2c13f80739e45cc02b1c27809e2dce43217977160ac1a09c5b9cf2e03c158b5379ce0de5d4180f1a91027029c0b8074d3918379cf2ea0dc59809fa6d22a0c09b8b72ec1a06f9cab06d06e05c01a6f2ea441901af39e2cbe2dce79705e086504f835a680ca454181372ee2dce5408da6f2e06b8378b739a448a45c5b9cf2ea0c078d837970c803c4e5dc89f000b0885e9bcbb8b30d01612cc02c2860669bc8986c0be7210f97716580b05381811f4d644c379740be720d78b339754d0160d42596a68380883e1a0c427d4d06812cdc5986f2e096405200f03023e5dce42f9fa6f0d04e0d025978b00b00604c3204b374d0274341c0442f4d03b434098340966e5dc59a68350965e72c8b8b0640965e73c5ba68370885e73c5a86f4d06812cdc59a6f2ea1a12cbce78b50de9bcb9910443857a1b81b8034d64414f97739071c597c370354d06812cbcbb86de001612cbcbb8b30d069534259ba6f2ee1b7140581b371661bd36910340966e9b81a868340965e9bcbb8b50d01612cdc59a6d0de5d818259b8b50de9bcbb0304b372e69bc581a50d0966e73c5b0374d069434259f97716c0dc0b8c0683029017c0b80522e9b81b9cf2ee2d435602f8170069b48a86e06e73cbb8b2b8b702e721942b1791706c1bce49b178b64de1a0d025978684f009c0b8064d1a5ce591716e5d819833c27814009c0b80722c9bce586f2ee2d819b93427f22e2dc340023e0688e2c13f86802dc1aec161c2c93608630d00845c003080be5c17c219b970040141a022179cf2ee01cc191044372ee00c34108682f0dc9b81b9cd2226c606207454804e05c0326f39a1bc5b97522c0cde45ce42913 else 0x1ce420e5cc8b8b306013834231f9cf161522e2c2e5c08c5ce438183c5811e061f39a1a02878183ce4050b2685a150dc9a33c60939cd0d0144000ac44261b5379c85a2322e2cc1b268462d06c9a2c001a1b8885cb991716c1a118bc5800e0d1f160022c0008c5ce78b60d1d22e2c08f0692a6e0d08c3c0c050408c20539ce061f390823e2d8187cb811e061f2ec0c08c781838183c5811e061e06c3008c7818381838183437030a9160616000d4d0134c074083436810aa6e060463a458185c5b03023a1a40aed359150de0dce433436404fe45ce60c8642827644c1ba6d0de730d8e15da6b22e1b41b9cc36385069ac3791739a0d0d8e0a59130de9b41b9cc363f060a10d825938684f86412c9d379cf0d04f0c8259ba681186c12c802c353780702009c8b8b706e5c7579ce36a1ace0c864340c04a32096308c8c80d8f807020095379170de5dc5b9ce36a0c))))

def x11 (i : Nat) : Nat := (if i < 1 then 0x5c3280000f5170034482d0c1de251f72994810c0001c0c71a573917bc0d3084e106dc11988237a0a2622da02ebc12ce091f065d04bb911e010e0037182d8424668d3a00f1004f80e50036e233b02ec00fc800e955ef009e88d7cee98465c80b192270451304b80003001b84550000119d400000000022e80003c1fd40fb000068420806a00902024000000000a037601f00002c8dc652b7080b53ac0001c0e634804828f01e60000b052800000001610a104af12af01f9c111f05af036090966414d23efd3f70106000000000000080ec0000a07e8000000012077a88900000010ac08200003821a2cea00001466933180000000000001904c00000000000058008c23448cc3031000004045e1070000000000000e0230000000000000000000003009049620000605e00001d954c051d002391cb40100000f096c801c0000c5280000382244182c02000007807280cbc08a0000000000000200f008800001c8a640c0e02ee2131003aa109028c00000000000000232484ae814000000000000000000203a00007c131894e00000000400ed00c3e03c0000300f40000a07900007016ac0934eec7241e02e00000846c000000003c2240000f03c0000399896131d344da13580b9a534225ba80fc0000000020028000309ca0000307b99206014da45fa04d00000423a2074448a000000001e0c30000480e301f120195299c8044020520ac903e000e408340000ca8e8000000000000000070356802e805e307c800024904000000001006800015518b22e0000000000000c2590000221960000128e783fc00000000000000000000000009031e83680001a8ce5240291680000e0d770866008400004462000059270000000000000023500000601200001136dd1a340a4922ce811201b28eeb5663d04a6895f00a8b4859802400ffc5036001e033ee229a00ae826f019e81e800003018f00ca4066000082908000041f4c0e070772904b51080000108cc244981bb0034a082202a581e0c0dc304f1824b40e3e00b328d683872a1a60ca896b414bd88ad8527228b9945480d584b0028cc00b541bc9113003e894a8c1edc4add040513a80081409d40259831700df0e6d729691280c93de12a178e8041400cd806cd000b017d826b24944292d148100aba0c9004e003ca81e3a4604407f814d8167c08d5047582c5c24f44169090104a2c0a980e5b0084845189124018907518206e8b3e04c3006704960172a042b223383a04249e5306089d0019053c0401c1406a8400006b730000840604911000d8820edc61c02182936240400093c0076410000144410d10300030000007201838144001170210200103400000040830008b0b161d00002080003a481000000000160c013100000a0a08026000010800000000228000020c000000c00022000050014018 else 0x1468493f4c93ac026828f78485ddfac11f74694022fc11800000023881e98094a117000000002421e6025645f7c138000000009281741d440e00000c4653806c0000000000006013c00000000a22c734000000000000000030ac05e00000000080540000000000000000000006041808f0000010eb250c4238680c000000000908a80000000160f500002d27c0000000000000000000000000000000000000194ec000028220c126c132328b73308010fa4b60000583b6a9d3a052b000701140991e05600006118400a1c12c000000003c97800d0207109a640000000000005915c000160a10000783900001e09b0000000000000643dd0172037c0000000000000000000000000d0147849800018298c14c80001882280731073f80a9820c8029c03de02fd8056a01fa09153212c22c0000608e21a2d41c6a463000)

def n12 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x3ffda260110fff54980443ffd3260110fff4c580443ffd8954110fff4e550443ffd2954110fff60950443ffd3254110fff4c550443ffd2154110fff62930443ffd5a4c110fff62530443ffd594c110fff4a530443ffd854c110fff68930443ffd824c110fff54930443ffd814c110fff48530443ffd8a48110fff56920443ffd3a48110fff62520443ffd5948110fff4e520443ffd8548110fff60d20443ffd5348110fff60520443ffd5148110fff4c520443fde33a6510ffb88a994437fd39a6510dff4a6994437fd83a6510dff60a994437fd52a6510dff4ca99443fed8588910ffb60e22443fed5388910ffe62600443ff95980110ffe4e600443ff92980110ffe61600443ff98380110ffe54e00443ff98280110ffe54a00443ff93280110ffe60600443ff95180110ffe4c600443ff92180110dffaa939442ffeaa4e510effa2139443f7e554e510ffb889394437fd8a4e510bff629394437fd5a4e510dff625394437fd854e510dff689394437fd824e510dff549394437feaa4a510bffaa929443bfe884a510fdf95529443fde334a510dff62929442ffd8a4a510bff569294437fd3a4a510bff4e9294437fd894a510dff565294437fd394a510dff60d294437fd534a510bffaa982443fde3360910dff6a5824437fca960910bffaa952443fde3354910dff6a552443fed8254910bffaa9804437fe9960110fdf95580443fde3360110ffb889804437fd3960110dff4a580443bfd8560110ffd285804437fe9954110ff78cd50443fee2254110dff4a550442ffeaa4c110dffa6530443bfe884c110fdf95530443fee224c110bff62930442ffd5a4c110dff625304437fd594c110dff4a530443fdd534c110ff74c530443ff9804c110ffeaa920442ffeaa48110ffea65204437fe9948110effa2120443f7e5548110ff78cd20443ff98a48110bff62920443ff95a48110bff56920443ff93a48110bff4e920443ff98948110dff62520443ff95948110dff56520443ff93948110dff4e520443ff98548110ffe60d20443ff95348110ffb54920443ff98148110ffe54520443ff93148110ffb48520443ff98048110ffe54120443ff93048110ffd285204437de33a6510dfb88a994427fd3aa65109ff4aa99443bde888cd10efba2222443f6e5588910ff38ce224437fa9980110efea2200443f7a5580110ff68ce00443fea2280110ffc846004437f98980110dfe566004437f93980110dfe4a600443ff151801109ffaa9394433fe884e510ddf955394437ee224e5109ff629394427feaa4a510cffa21294437de334a5109ff629294427fd3a4a5109ff2a5834427fca9609109ff2a5524427fca94c910bfeaa9204437fa9948110efea2120443f7a5548110ff68cd204437f93948110ffa54920443ff15148110ffa48520443ff0a148110 else 0x9160d9ce5c12c308c0b4dc8b0643739cba184011a6e4586a0d9ce5c05c309d3502c370648b39cb8258613810398069b9160d06e739762cac0b00c8b068354dce72ec59381601a6e0d06a459ce5d8b2702c034dc8a0d41b39cbb164e05806458329b06e739762c90234dc8b0d81b39cbb1602d3816019161b0329b9ce5d8b2702c034dc8a0643739cbb164e058064586a9b036738b65c9c0b00d372243606ce72ec5939160d9c8a01b172293606ce4520d8da6e1a2406c4d3722104362401a6e059161b036739762c05a80b8034dc8b0dcbb16ce6060d959161b8129b9ce5d8b40c8d370dc0922ce72ec5a06469b9160486e739762d032302d37224372ece7168190020918100da6e1b9762d9ca44ad370dce72ec5922818fa6e440361b9ce2c05a608d3722c360601316ce41a4c1365fac94d8d4b0ff60fabfed7bcaf0b5c72b6dd672abff5722abed53caa0b5362a50d438a7b34dc298dd2a8a50b48228d4d140a19b41927f8cf889e8f3b7a735cdf89b33347267ccc9a98772fc25becb64961f2b3a54bca60941726da49cc8ee90e320223cfc74a8deb1afa325c5d88af314e2271c48488730fba1d1c31c858f092a0e1c14681e302c2032c01a7fc6fed9fbfbf027d1ef849edebd727a3af321e39bc2877baed81d71ba6673d2e629c95b8cc7102e179c0eb7f06f0edc79b5ab64c6bc6d5e9a92b4ee695ad1d99fcb3686612caa9925b1e262dec419849b02a5f82bd39772ae7c5c26b6d16aaacf6591ab0695d3ab3e5596a9b1506a990523aa2a941ba7d84ea29bf133fa6204b469511263a47c483a8ef91afa2f6451a88690f6a198425e8319033a0123f7a7d50f759e823c1e7698e9e9cde38ea7008de09b4435b669f0d1899e6330e64a0c6498422f9e5d48b7496622bde5618a8994aa28824f609b79310256249488ef916c21f242188228fdc1ed23bb075f8e561bda36b06b08d02194631105f28ba4168a2b985438a2813ce262049988de10fe20803db87580df21a6831d85dc0afa147825f846008520fa01dd838e064a0af01338212037a05a007f80b400be0003ffd83a6510fff60a99443ffd52a6510fff4ca99443ffeaa4e510fff62939443ffd5a4e510fff62539443ffd854e510fff68939443ffd824e510fff54939443ffd8a4a510fff56929443ffd3a4a510fff62529443ffd594a510fff4e529443ffd854a510fff60d29443ffd534a510fff6a583443ffda060d10fff2a583443ffeaa60910fff6a582443ffda560910fff68d82443ffd5360910fff68582443ffda060910fff2a582443ffeaa54910fff6a552443ffda354910fff60d52443ffda054910fff2a552443ffda94c910fff61532443ffda14c910fff68132443ffca94c910fffaa980443ffd5960110fff4e580443ffd2960110fff69580443ffda360110fff54d8044) else (if i < 3 then 0x6019129a86c0d9ce5d8b2c0b0a702c034d4890d81b2ece716589e026058064586c9b9ce2d9740cbc8b00c0a4d43739c5b2e8193268b98164586e2d030439ce31970d022372240102c5b2ece53614902400981601a6e1b116730365d8b190cd3700c0a0643716cba22ce53110298069b86e5d036618b67232888c12302c030d53716cbb398892136458161b830a99ce5d0c46d26896cc8b0dc1b39934460d8f8140586e0d9ca459743126a70280b22c190dce72e8624d4e050164586a0d9ce5d0c49a909b22c1b2ece618434369344b504d9161b974319ca0c1b49a25a8570104dc3706ce72e48a188d84b58099ca602a120088b4dc3706ce4250d91814550169b8321b9ce5d0c444ac0a2a80b4dc3506ce72e86222569b9761b0c672834441b0969c8b02d3706cbb390e01c44019169b836730688c1b230287202c8b0653739cba0d8615814390169b836729165d06c30ac0a1c80b4dc8906ce72e83618504d91005836739729b06c311b096b00b4dc1922ce72e836188d84b504d9160d9ce5d0c29a1b41a25ab4dcbb0648b39860368344b484d9169b976730c20c1b41a25a8040341cd370648b390972e8604b5e9b9cc00238801b1b224082607306ce72ec58365360d12d991401a6c0d86e738b65c25816ac0b4d81b22c3739cba1802d30069b9161b9c8161b1e06d3722c373902c363e050164586a9b9ce5d034309c0a02d370dce72e48a06861381405a6e4486e739740d0c2722c340b09902c0b2e81b39c594d0d44b684d9100586e73974310329b1b096bc340b40b02cbb4d81922c5b390d44b6005a6e1a9165d0c6730346c25ab2202c2640b02d372e43606ce7160d44b684d91005a6e739721b034311b096bc8809c3739c5b2e534368184b54059101986c319ce5ca686d03096b0274dcbb0dc5b39488368184b569b86a4412e5d9cc310306825ab220274dcbb39c590d0da0612d5816440669b9ca1b9740d0c096a02f0dc094d48b39cbb16819205e458129a86e739762d03240bd370243522cbb39c5a064890024080369b86e5c916721c430b02d6218b22c37168194dce53006d60584a1369b86e2d032459c836982c0b04f4dc8b3981b16434434c01b5e9b9161b9c8161b1b2209b0dcbb39c5a060d94d12d415405a6e5d86e2d9ca450306c25ac2607202c8b4dcbb39c5a060d90d12d881672190344d3700c0b22c1b2ec590dce636569b806059161b9762c836731b2b4dc8b06437390d8da6e459ce1a833761b1f02c0322c194d83739cbb164e058064586a9b036739762c9c0b00d370d48a06ce72ec59381601a6e4486c0d9ce5d8b274dc8b0dc1b390d8d9160586e0d9729b9cc311b274dc0b0dc1b2e48b39862364e9b816458365c86e730c46c9d3702c8b0dcb906ce6188d93a6e4586e0d9c86c6c0862c8b0dc194dce72e8613a6e1a else (if i < 4 then 0xb9ce5c9143126b10640a4dc36e06ec2c38b4024050261a1320d972459cc3126b00480b228110d41b39cba1893540600a0f4019160d9cc9a8686cace70dc1a00888320942c469b9ce0d004441b04a1622008882502c2c2c4b0104b86c08a6a0d9ce5d0c444b896020974d8110d41b2ece6228617a681886e0c814019c84a1b2502803390940b0d8d8b41b9ce0c813c00e0588c5a0dd3739cbb064081c0b12a6c019ce0d0686c161f4d80040834360942c3e9b9cc010686c0585878701c0120208f068114d48b39cba0d861b8b41ba6e5c813760e05888701c01202c8a0453506ce72e8620d64380e00901047a6c08832459767306c30d0140c8716207200c8b06ce60d53436669b9100b00673068161b2339cbb0d8180b0b0da6e5d86e7303016161f4dce72ec5a0602c2c3e1a05c0c1909658180b0944b269a05c0c1b096582e0208c0bc360453522ce72e81a1864170101791408a6a1b9ce5d03430b82e0208c0bd36044372e48b3981a1866458681681672a68640da00b48a06800040e01b3e9b9101681672868640da34dc8b06c0302437398d91a6e4586e018120d9cc6c8c1b4dc8b394343f0d8e8369b9161b9c8161b1c0414300c0b22c1b2ec594d437398d980209f806059161b8b65ca6a0d9cc6cc01048c0302d370dcbb1648906ce636600808e018169b9165d8b21a836731b330dc030253606ce522c5b2e4e4580604a6e7286c0d9762c9d3700c090d81b39cb922c592a6e4586e0c316721b1f390d8251e9b9121b836721b1808ce40b0d890200986e0ca6e059ce5c91430a81004c8b0653702ce50dcba1854080269b8365c86e619ca450c2a0401322c354dc0906ce72e861502009a6e1b9720d982459cc30a81004d3722cb90d41b30ce618564586e0cb10c4a6e721b220040b39094362e9b9160d9ca1a1b1a000233902c362809a6e458303906e73970818b0c825b300c0a04c8b060734d02716ce60dcb81f12dd806059160d06a9b9ce5d8b2700c0b4dc1a0dce522cbb164e018169b9141b9ca0d9762c9c8b068354dce440cbb161904b56018164583672a6e2d06e5c1a096b8374dc180c48b2ec5b390e056560181645836738b29b9741a1a096b15f02c03065352283739cbb16569b9141b9ca0d970818b0c825a84fc0b005372283506c5b39cb856589181601a6a4506e5c8362d9cab0d01008d3722ce716cb84402d591011a6c0d86e738b65c25816ac0302c8b0d5373981b2ec59380605a6e1b9cc0c9165d8b2700c0b4dc890dce606cbb1648079161b036738b65ca686a25ab00c0b2281b0dce7165372e0d04b5e0181245a6e1b0362d9ce5c1a096b81b220250dcbb4dce7160d44b5601816450369b9ce5d8b21a1a096bc8b39c5b0d81b2e5343412d29169b9ce2d86e5d0306825a700c0b2200f4dcbb16ce50d0da0612d8058a181 else 0xc03025372243706ce63646018129b9161a836731b2300c0b4dc352241b398d9180605a6e4486a0d9cc6c8c5a040720d0784b365d8b41aa6868259922c5a0dd343412cca6e0d0686c259404813065360d48826ce72ec5948362d06e9a1a096601204c894d0310683739cbb1654080269a0641a9104d9720d8b672bc3606cb80b12cba6e739761b03016259f4dcbb168180b12cd86c0c1901625960602c2512c9a6c0c1b01625940bc360b5352209a06ce716cb9405e44a6a1b05e730362d97240bd360b4352209a06ce72ec5946864506e0c826738b65c81424d83502c88d0c1904ce72e46179c9a09b0f0d13c0ac0b00c8a4d34b39c5a06cb99268139161a8240d9ce2d972606c364dc0b0005122c5b2ece55268a581601911a40521b9ce2d972e04c0b009350d48a06ce716cb9404c0d86c9a80644820299ce2c982e06c364d40b2241014ce72e46159161b26c0d9ca6c6ce60688b02c034dc372ec58c8519004c4411e9b86c0d8b65c9b672b1234d32302c02061690dc5b2ece5781600a6a1b1140d8b65d9ca4231230d32102d341441222cb918ce599c9909b0c910274dc890481b39cbb164e058029b06a45036738b65c9d372202739c593004ce08c1a8169b91040820299ce5c8c2cc14d859ce1b834019849a2a0588c3706934320944b321b8349a1b0965c364d0c80b12ca9120526e7386e0d700588c59029373943706b802c40b4024050260c1321)))

def x12 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x146e0d1f600722da870589c0b5731efca31623a74150a2829824d8067c504610634ca4040146ca4c20915da2f207300000000004164000000000f23cf8021f00d80000701d44913008334a45723f40184f04a21014a0653812da26d7806df039b814e00000000000000c16f0000301edd092c000000003c0fca198f8a7c00002c06500000018800000000000001d0280000021d2247c40000000034227e0625c08700000418c323fc4229829600a34c065400009b7928181e7263002212265c215803094256a05b788472052a6a5c624a9d1e3e042c052f000000000b8750000000107996a000000000b23ac5848b0863890f800f4c0fd000000000624c400008040c0000b073c00008002a09b700000000000001400d00000c9de727e640f70000000000000260d58237cca7110095419b707808896d09031047628e5c18f526acc200e00ec000000002983c2150340b7209be0191423b2c16700001c22200000cd2c8065f0201805fc00001068000007027801dd7079009225010c0000000008094c2622c802000000000502ec0000000000000ca50c0000d003340ffa229b8c46000000000000000000000000000202300000000038254000030a47906600000a07ed8a3a901d04225e25fbc87ca044e88910000141a1000000000506734a570000000000000088e01811dc120c0994c105f01f341f360284081fd20b25027100228091c0503485b7025881174069c0000008a881f2f05852a0e00001c0fe329bb80af009080000d0436813b7223000004058009dc10769c1e800002c05ffa0e100cc002660055306b500bfc03c800000000389bb000038a6d000000000d01b351ef00001857d8a3bb401da021540c89096b819d000014a7b00000000000001c10cc134649b300000c0190000310500000080c1a47c80000729d0021740348000000003ca3f00000689800000022bd04c00000000000000426e8889fd0984000000002c1d0a396c4a70409280000000000000223b7c16cb87b1802ef28cbc21d566a529d5d24214a417131c48d8f0614000000003c8971040181f7b082ac1de521c2c8cd3087c820900000000000001c006a037c044500000409b09204b04344210208304038f00c28104128200a0c230208a1400000050410021cd01104c0042cd0470020010c300200430008212700c0cd00900120320304804608250a1c01c508a1811c014008700258200214404654100c0040820850451080c00801010020050c528005b00300004208014000510420b1c60010853c00471000c11440000880040010002403c000000054100210000004208911b0001c504008204004350a0451441c50060801804144850410040020020810472c600204e0cc0400800001020011462000411040080410000002800830c00008802801c1501040000 else 0xc0953095e4001920a891535085811ed800d28090407024262b0473006111323021ae096d025fc264e48ef50082c57200002421960014000062761dc572226c49bc5028bc0e3708b00000208d6c570a093800007222c0000d079b8040602a00000a07f001b0403b6021e00003e518000030a5910812020800003d5e1601c00000b05e2c0dbb120f82760000000000000000000000000008222400000000240cbf0248c84c708908236000024042d475241a6f299ec106d0724c1e33404f012600001010400000000000002c22622162014870715c1d7b04d281d8a2064c0c900002057f47451098610487891a102d342668160000000000000000000000000000000000000280b900002c258929740000e804804821053189379a6af59ea92084000034040ad3d624b70255f84fa951522910402d402b2c813705c442072811a4175c071c000000000000020971c0c3a000d401a4248fc0be1221941742206e408ac233000008162ac11400003010230393c0b152220167a000000000794454c74e00a40000404480000e4795113d303806a6cb00bd89040000340a3000000000b0571495bb029c000050201407370044407f00000104d7a15900136413a8122f23840000000034068b21b800006040699e6d611c49b6f0754404dd22495827e01aa881a5131b8205602a68895e27640000000000000000030149b2466c1310000140ab93208000000003408daa15c01b21033888f600000c02b000028093c00cac8c45478b41b9a47840000901d800007025d409b20294cd2bda84710120067800c5d005c000060600404ce07a40000a022e41d600002c0d4912ec818e0000380aae03bec214b23de0192b080c88906022429680000000000000000000000209e40000341c3a05a68577b0872c23e6b78601fee320c0000000000063302c800002023c0000823e000000000000006350000008744000000000140d900003c0b8e01e389b4d21b40000000000000000000000000038905000000000e050800001099e414f000000000744fac1e7509abe00fd24cea9b17298c000000000c969000014024d283c0000504ac000090098c1070000000000000000000413c0000000034069428b4000000001c97a735c80000b03940000f09bb447b704ce80cda053500eb708354137000000d1b000010260d056e4157b02f180d752127c0fa42366889e0000181df62688813ea1324000070926898c000000000d80a1016ef28c00a75000000000b56a00000b240e42630000100e1b43700000f03c6854bc07640a43d0161424c00001465b00000000000000c12400000000000002883db09180000305640000828cc0000d29bc00008247e810ad001d026bb072f4270c02b781f5a012401caca9ec00003045400009414fa844920ec814310374c20b000000000b) else (if i < 3 then 0x2482fa21bfc243706fbdc4480038412a4465ac186f09cf082b429470535e19931011300e8d00fd47c20132fb1190248525780000000000000205c14a3b309c4000000001c4813003d425190721409a2229200a0605764259ea8bb02207974cc8a1c20fc0000b056bc146a944941f9901b800001412dc2442043f8978901c881c2f07180a7600000000000000a67a22239019a00002417e414b1001500000811ad070400000a9d6c277120a40000600fbca4e68130000000000000000000000000000808e000034136b29ea4156c09778077203d58196003100066d068b40b6a22695e0e000000000d005800002275c817be2775904ca24e081b4211d2892e626ba805d5435701a50000009676091e0123f093f91f40000000000000388f930209c0e9000000000000000000000000000e03cc00000000140233051c0000504740000b812fcd35000008151b20fb80103062e022df412800000049c4172e08dc0000b257ec1ff226f4013d00000000000001806200001001e000000000f27f0402c7760d0887124c101dc6243010de42782c23da43628064d05e5019000000c053203880000b744ac0395775481650994c486c5094a8139326b04d30a238d007d0000140009b8b5a011000000000d1924005a000000c84823a8c1afc0167c0ba70843481c004ff505100000000000002403500000025e0000148fb600c649be2a414420640328c0da9007c0079b2373c00900000c8eed259ac1bf814b40000313158228701e98872d094e10540000042386068c0000d23eb42690000000001021b516a0000080f00269088c3506e800000000000007240b0d4d00001c22e0000000000000041089047a803c3a7e2104500003d1e76296f8212000000000b05138037e222ba9991292d81525035a0a56f412411f37205c0000e678541ee40363d65a1033c0000304e0000000003022100000000000003c05c000000000000000000e97e800002018308e2f23a1c158823c5c11bf039c91d2b0303813ac046601f6179480223704bf4901006aac9b8f24d10033301780000c414b096d05266011fd435800007057d04be939901518705f00000000000000f0690000000000c116b1958409d0000211ecc290a80ae205eb00bd0000208da00001c1822437489eb5031881db904a400001b3984484000000000000000000506cc0000329e70018f436a09b925530c0fb881240000b07340000000000000103e60125000020907e27580000000004830914aec1876027cc15e235de421300002e9d19080b009cc2481ea3cd002c0000c04bbc145a2295a010000000000715d8d154d02cec232b22880000000000000e04240000028b80000127100000c29a00000e09a38957604608818000000000101bf8071000000000d052c0000a034c000000001027800001 else 0x1c8f06199a0932505540000221c700d0f05050a4df2994000000000000000000488500003a0d6000000000f03a1858c300108958d04f3406b8639788f40043bc163d00a840b0c09cac96b166a0e914274174067f05cf051f101fa40dc000028030e094000000000288e7805ad081d0000341fd425a281ce0086f40474059a405b623f14a62902214987))

def n13 (i : Nat) : Nat := 0x8040a9b2286c1a72364402054d9141a5d1606ce46ca05c02054d914362d2e034e46cb021420500914189a0d9ccba2cb0240a0122869340d398b4b94042440a014d868880d2e8b4e560408c0a014d910340d3997459602914360d2e0c4e49a364808554d86c1a5c189c8886ca010729b22834ba7218068d940b01536450d974e40c181b2a9b008148a1b069745a7236540a014d914181b399745930280536450d034e65d164d36052286c1a5d390c0d930280536450606ce65d164c0a014d914340d399745934d914360539974580c8c57732b24fc93b0d5e6b77630ae52d1fb34a53c7c8a309a003ffd32887ff4e510ffe94a21ffd83443ffb04887ff54910ffe99221ffd80443ffaa0887ff4c110ffe902217fe99443fbc66887fb88910ffd002217fd39442ffa52887fe48110

def x13 (i : Nat) : Nat := (if i < 1 then 0xc10989100863480c42280002014c000000020a6c820000000000000011b2c3af83b80003889d8afdcb7a0ac90bcc000246f986f3408000008891c024183a0cfcc8d7038000039660c915099c0001cae400010af8e03c000349ffcb6000024bb6002301c440a2c09d02ca08d800000003c9d00001011c43400000c8ffc89400000000000000000002e1b589b40000000382608b8400010291cb880000000000000003aa5d48564246424200f78230000000000000000000000000000041780000491b431f57880001c37b41422b85cb4b421686e882b648e6c13fc2e98226c984000142c400000002e66000014aa268340d5c0001c2d748a4ab4400024a7ec93dc2218a45cad44a420a9282d95041c2e4000381ac00729f840000405840d000004a1041dc0000000000030254000000000000d4da4d620ae102ac000088590a5b413041b444ff4a8bcb5342fb0945c8f1436a88c24a7283c64a678265805344e7cb0400014bc4000389738a1689c3817051b78b4241114bd1417c406806f7438981c98b9643234384820c00000003424e49ed89894ba54ab80000839800000001803102d00002c1508543c94e8b238ce400030993831280c44103c82e8325c96b97b0000382f40002822d412601280000818040bd48ca487140974b0f0a7800854299801a0a25429400014a560538014acab4000101c3095281efc30803970145ea07c81a018d83a482864306806369b400005048000242dca043446c4560000348bd82a8cabe4250eb7c000389dc889ac8a15b28903f84b40000000341e5407b00ec018bddb7427bc94381d202a74107081f9004000080da0174000141bbe04480d64998000181600000ca2d48cd0319c08c438e01f2c9e1503800028957c92c8d38c565c37049cc0000807d02bd03a80003488000000000000208770a8008a80003c0c000000002104400038ad0000340de4a200002c1540001dbc688218b3d01e00a9a4236ca9400000002429c0002c12cc0f9891c0001de5e8884c1340000000140f388e940a40003c2cf95f849bc00024a74427c008a430c00030a6082c2c209828c48d040aec19800000002abd1c3be00674b9000004a3521b000000003c1a1416f0114021c41690248000168d4000188c781928012c3540b8180e1c23880aa088a415c000240b80003800303c3284e1737828142f28041836459c640e40c6e0a0400000995d1e942a30a5181da06ee582a4a6800030b4c000000035b380000c0ccc0ca11d641ab8a3d4bc80000405c4a8503a0c8ef4259431681a45000103053780cc730e1400400120002800c10800c60000850cd2981801812014402441400870c024b00038034600f14604118000301a0010410c518b00000304220124434208d1802040c40c008008b00a04708118f047086404003005000002010 else 0x3021800000002001c0003410f80578aa68210000000000002023d836cca29435a91c80ee8c0b1c35c8808000389fb4184000000020348856a032e8bb000000000c275839d80fc000000000000000282b000019a64c55d826c40e8000000000000000000000000000000000003c00d600483ce812000000000000240b400000000000281f8033000030a8c000000000003aa702b74c1580002c11800000002dcd725f983b2801783000000000000014930000000000003c1f5)

def n14 (i : Nat) : Nat := 0x4009a441a0c725c2c9ffd10

def x14 (i : Nat) : Nat := 0x826800000160200069a4001a430002944000000802c03fc0180d0005920000000000000069d808723381c000000a40c93109f65000000000000000006828c94000422211fc522400003407484000000200e8200000000000000e04cb5eb2c000a4500000001050038

def lv : Nat → Packing
  | 8 => (3,7,7,0,0,4,0,n8)
  | 9 => (26,6,7,0,0,8,0,n9)
  | 10 => (310,5,7,0,0,14,0,n10)
  | 11 => (637,4,7,0,0,16,0,n11)
  | 12 => (245,3,7,0,0,15,0,n12)
  | 13 => (18,2,7,0,0,11,0,n13)
  | 14 => (1,1,7,0,0,0,0,n14)
  | _ => emptyPacking
def ix : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 5 0 10 2 4 x9
  | 10 => lookupWord 10 46 4 13 5 4 x10
  | 11 => lookupWord 135 575 7 17 9 4 x11
  | 12 => lookupWord 313 1322 6 18 10 4 x12
  | 13 => lookupWord 131 555 6 16 8 4 x13
  | 14 => lookupWord 10 62 3 13 5 4 x14
  | _ => fun _ => none
def g : SeedForest := ⟨⟨511,14,fun j => deadsamples[j]?.getD (0,0),cols,deadautos,lv,ix,shapeCut3640,shapeCut3640_sound,none,none⟩,seedAug 511 0 1 seeds⟩
def rows : List (Row × Row) := [(2,3),(1,3),(2,6),(4,12),(1,17),(1,33),(2,66),(4,132),(8,264)]
end S511_0_1


def book0 : List SeedKey := []
def book1 : List SeedKey := (15,0,1,4)::book0
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg0 : seedGateOK S15_0_1.g 15 0 1 3 S15_0_1.rows S15_0_1.seeds book0 bounds511 = true := by decide +kernel
def book2 : List SeedKey := (15,1,2,4)::book1
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg1 : seedGateOK S15_1_2.g 15 1 2 3 S15_1_2.rows S15_1_2.seeds book1 bounds511 = true := by decide +kernel
def book3 : List SeedKey := (31,0,1,7)::book2
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg2 : seedGateOK S31_0_1.g 31 0 1 6 S31_0_1.rows S31_0_1.seeds book2 bounds511 = true := by decide +kernel
def book4 : List SeedKey := (47,0,1,5)::book3
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg3 : seedGateOK S47_0_1.g 47 0 1 4 S47_0_1.rows S47_0_1.seeds book3 bounds511 = true := by decide +kernel
def book5 : List SeedKey := (47,0,5,5)::book4
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg4 : seedGateOK S47_0_5.g 47 0 5 4 S47_0_5.rows S47_0_5.seeds book4 bounds511 = true := by decide +kernel
def book6 : List SeedKey := (55,0,1,5)::book5
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg5 : seedGateOK S55_0_1.g 55 0 1 4 S55_0_1.rows S55_0_1.seeds book5 bounds511 = true := by decide +kernel
def book7 : List SeedKey := (55,0,4,5)::book6
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg6 : seedGateOK S55_0_4.g 55 0 4 4 S55_0_4.rows S55_0_4.seeds book6 bounds511 = true := by decide +kernel
def book8 : List SeedKey := (55,1,2,5)::book7
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg7 : seedGateOK S55_1_2.g 55 1 2 4 S55_1_2.rows S55_1_2.seeds book7 bounds511 = true := by decide +kernel
def book9 : List SeedKey := (63,0,1,8)::book8
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg8 : seedGateOK S63_0_1.g 63 0 1 7 S63_0_1.rows S63_0_1.seeds book8 bounds511 = true := by decide +kernel
def book10 : List SeedKey := (63,0,5,8)::book9
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg9 : seedGateOK S63_0_5.g 63 0 5 7 S63_0_5.rows S63_0_5.seeds book9 bounds511 = true := by decide +kernel
def book11 : List SeedKey := (63,1,2,8)::book10
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg10 : seedGateOK S63_1_2.g 63 1 2 7 S63_1_2.rows S63_1_2.seeds book10 bounds511 = true := by decide +kernel
def book12 : List SeedKey := (63,2,3,8)::book11
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg11 : seedGateOK S63_2_3.g 63 2 3 7 S63_2_3.rows S63_2_3.seeds book11 bounds511 = true := by decide +kernel
def book13 : List SeedKey := (111,0,1,7)::book12
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg12 : seedGateOK S111_0_1.g 111 0 1 6 S111_0_1.rows S111_0_1.seeds book12 bounds511 = true := by decide +kernel
def book14 : List SeedKey := (111,0,5,7)::book13
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg13 : seedGateOK S111_0_5.g 111 0 5 6 S111_0_5.rows S111_0_5.seeds book13 bounds511 = true := by decide +kernel
def book15 : List SeedKey := (111,1,6,7)::book14
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg14 : seedGateOK S111_1_6.g 111 1 6 6 S111_1_6.rows S111_1_6.seeds book14 bounds511 = true := by decide +kernel
def book16 : List SeedKey := (119,0,1,6)::book15
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg15 : seedGateOK S119_0_1.g 119 0 1 5 S119_0_1.rows S119_0_1.seeds book15 bounds511 = true := by decide +kernel
def book17 : List SeedKey := (119,0,4,6)::book16
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg16 : seedGateOK S119_0_4.g 119 0 4 5 S119_0_4.rows S119_0_4.seeds book16 bounds511 = true := by decide +kernel
def book18 : List SeedKey := (189,0,4,8)::book17
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg17 : seedGateOK S189_0_4.g 189 0 4 7 S189_0_4.rows S189_0_4.seeds book17 bounds511 = true := by decide +kernel
def book19 : List SeedKey := (127,0,1,9)::book18
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg18 : seedGateOK S127_0_1.g 127 0 1 8 S127_0_1.rows S127_0_1.seeds book18 bounds511 = true := by decide +kernel
def book20 : List SeedKey := (127,0,4,9)::book19
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg19 : seedGateOK S127_0_4.g 127 0 4 8 S127_0_4.rows S127_0_4.seeds book19 bounds511 = true := by decide +kernel
def book21 : List SeedKey := (127,0,5,9)::book20
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg20 : seedGateOK S127_0_5.g 127 0 5 8 S127_0_5.rows S127_0_5.seeds book20 bounds511 = true := by decide +kernel
def book22 : List SeedKey := (127,2,3,9)::book21
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg21 : seedGateOK S127_2_3.g 127 2 3 8 S127_2_3.rows S127_2_3.seeds book21 bounds511 = true := by decide +kernel
def book23 : List SeedKey := (191,0,1,11)::book22
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg22 : seedGateOK S191_0_1.g 191 0 1 10 S191_0_1.rows S191_0_1.seeds book22 bounds511 = true := by decide +kernel
def book24 : List SeedKey := (191,0,4,11)::book23
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg23 : seedGateOK S191_0_4.g 191 0 4 10 S191_0_4.rows S191_0_4.seeds book23 bounds511 = true := by decide +kernel
def book25 : List SeedKey := (191,3,4,11)::book24
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg24 : seedGateOK S191_3_4.g 191 3 4 10 S191_3_4.rows S191_3_4.seeds book24 bounds511 = true := by decide +kernel
def book26 : List SeedKey := (255,0,1,12)::book25
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg25 : seedGateOK S255_0_1.g 255 0 1 11 S255_0_1.rows S255_0_1.seeds book25 bounds511 = true := by decide +kernel
def book27 : List SeedKey := (255,0,4,12)::book26
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg26 : seedGateOK S255_0_4.g 255 0 4 11 S255_0_4.rows S255_0_4.seeds book26 bounds511 = true := by decide +kernel
def book28 : List SeedKey := (383,0,1,13)::book27
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg27 : seedGateOK S383_0_1.g 383 0 1 12 S383_0_1.rows S383_0_1.seeds book27 bounds511 = true := by decide +kernel
def book29 : List SeedKey := (383,0,4,13)::book28
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg28 : seedGateOK S383_0_4.g 383 0 4 12 S383_0_4.rows S383_0_4.seeds book28 bounds511 = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sg29 : seedGateOK S511_0_1.g 511 0 1 14 S511_0_1.rows S511_0_1.seeds book29 bounds511 = true := by decide +kernel


namespace S15_0_1
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 3 := by
  intro k h
  interval_cases k <;> decide +kernel
end S15_0_1
namespace S15_1_2
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 3 := by
  intro k h
  interval_cases k <;> decide +kernel
end S15_1_2
namespace S31_0_1
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 6 := by
  intro k h
  interval_cases k <;> decide +kernel
end S31_0_1
namespace S47_0_1
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 4 := by
  intro k h
  interval_cases k <;> decide +kernel
end S47_0_1
namespace S47_0_5
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 4 := by
  intro k h
  interval_cases k <;> decide +kernel
end S47_0_5
namespace S55_0_1
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 4 := by
  intro k h
  interval_cases k <;> decide +kernel
end S55_0_1
namespace S55_0_4
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 4 := by
  intro k h
  interval_cases k <;> decide +kernel
end S55_0_4
namespace S55_1_2
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 4 := by
  intro k h
  interval_cases k <;> decide +kernel
end S55_1_2
namespace S63_0_1
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 7 := by
  intro k h
  interval_cases k <;> decide +kernel
end S63_0_1
namespace S63_0_5
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 7 := by
  intro k h
  interval_cases k <;> decide +kernel
end S63_0_5
namespace S63_1_2
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 7 := by
  intro k h
  interval_cases k <;> decide +kernel
end S63_1_2
namespace S63_2_3
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 7 := by
  intro k h
  interval_cases k <;> decide +kernel
end S63_2_3
namespace S111_0_1
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 6 := by
  intro k h
  interval_cases k <;> decide +kernel
end S111_0_1
namespace S111_0_5
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 6 := by
  intro k h
  interval_cases k <;> decide +kernel
end S111_0_5
namespace S111_1_6
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 6 := by
  intro k h
  interval_cases k <;> decide +kernel
end S111_1_6
namespace S119_0_1
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 5 := by
  intro k h
  interval_cases k <;> decide +kernel
end S119_0_1
namespace S119_0_4
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 5 := by
  intro k h
  interval_cases k <;> decide +kernel
end S119_0_4
namespace S189_0_4
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 7 := by
  intro k h
  interval_cases k <;> decide +kernel
end S189_0_4
namespace S127_0_1
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 8 := by
  intro k h
  interval_cases k <;> decide +kernel
end S127_0_1
namespace S127_0_4
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 8 := by
  intro k h
  interval_cases k <;> decide +kernel
end S127_0_4
namespace S127_0_5
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 8 := by
  intro k h
  interval_cases k <;> decide +kernel
end S127_0_5
namespace S127_2_3
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 8 := by
  intro k h
  interval_cases k <;> decide +kernel
end S127_2_3
namespace S191_0_1
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h5_0 : seedBlock g 5 0 1=true := by
  apply seedCellsBlock (ar:=6) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h6_0 : seedBlock g 6 0 12=true := by
  apply seedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h7_0 : seedBlock g 7 0 17=true := by
  apply seedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h7_17 : seedBlock g 7 17 42=true := by
  apply seedCellsBlock (ar:=8) (rows:=1) (d:=1)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h8_0 : seedBlock g 8 0 1=true := by
  apply seedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h8_1 : seedBlock g 8 1 97=true := by
  apply seedCellsBlock (ar:=8) (rows:=1) (d:=2)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h8_98 : seedBlock g 8 98 118=true := by
  apply seedCellsBlock (ar:=9) (rows:=1) (d:=2)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h9_0 : seedBlock g 9 0 13=true := by
  apply seedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h9_13 : seedBlock g 9 13 19=true := by
  apply seedCellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h10_0 : seedBlock g 10 0 1=true := by
  apply seedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 10 := by
  intro k h
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact h5_0
  · exact h6_0
  · exact (@seedBlock_merge g 7 0 17 42 h7_0 h7_17)
  · exact (@seedBlock_merge g 8 0 1 215 h8_0 (@seedBlock_merge g 8 1 97 118 h8_1 h8_98))
  · exact (@seedBlock_merge g 9 0 13 19 h9_0 h9_13)
  · exact h10_0
end S191_0_1
namespace S191_0_4
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h7_0 : seedBlock g 7 0 27=true := by
  apply seedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h7_27 : seedBlock g 7 27 33=true := by
  apply seedCellsBlock (ar:=8) (rows:=1) (d:=1)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h8_0 : seedBlock g 8 0 2=true := by
  apply seedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h8_2 : seedBlock g 8 2 152=true := by
  apply seedCellsBlock (ar:=8) (rows:=1) (d:=3)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h8_154 : seedBlock g 8 154 128=true := by
  apply seedCellsBlock (ar:=9) (rows:=1) (d:=2)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h9_0 : seedBlock g 9 0 18=true := by
  apply seedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h9_18 : seedBlock g 9 18 28=true := by
  apply seedCellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h10_0 : seedBlock g 10 0 1=true := by
  apply seedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 10 := by
  intro k h
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact (@seedBlock_merge g 7 0 27 33 h7_0 h7_27)
  · exact (@seedBlock_merge g 8 0 2 280 h8_0 (@seedBlock_merge g 8 2 152 128 h8_2 h8_154))
  · exact (@seedBlock_merge g 9 0 18 28 h9_0 h9_18)
  · exact h10_0
end S191_0_4
namespace S191_3_4
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h6_0 : seedBlock g 6 0 1=true := by
  apply seedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h7_0 : seedBlock g 7 0 3=true := by
  apply seedCellsBlock (ar:=7) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h7_3 : seedBlock g 7 3 6=true := by
  apply seedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h8_0 : seedBlock g 8 0 37=true := by
  apply seedCellsBlock (ar:=8) (rows:=1) (d:=1)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h8_37 : seedBlock g 8 37 43=true := by
  apply seedCellsBlock (ar:=9) (rows:=1) (d:=1)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h9_0 : seedBlock g 9 0 7=true := by
  apply seedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h9_7 : seedBlock g 9 7 7=true := by
  apply seedCellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h10_0 : seedBlock g 10 0 1=true := by
  apply seedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 10 := by
  intro k h
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact h6_0
  · exact (@seedBlock_merge g 7 0 3 6 h7_0 h7_3)
  · exact (@seedBlock_merge g 8 0 37 43 h8_0 h8_37)
  · exact (@seedBlock_merge g 9 0 7 7 h9_0 h9_7)
  · exact h10_0
end S191_3_4
namespace S255_0_1
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 11 := by
  intro k h
  interval_cases k <;> decide +kernel
end S255_0_1
namespace S255_0_4
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 11 := by
  intro k h
  interval_cases k <;> decide +kernel
end S255_0_4
namespace S383_0_1
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h8_0 : seedBlock g 8 0 24=true := by
  apply seedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h8_24 : seedBlock g 8 24 12=true := by
  apply seedCellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h9_0 : seedBlock g 9 0 6=true := by
  apply seedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h9_6 : seedBlock g 9 6 148=true := by
  apply seedCellsBlock (ar:=9) (rows:=1) (d:=3)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h9_154 : seedBlock g 9 154 47=true := by
  apply seedCellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h10_0 : seedBlock g 10 0 1=true := by
  apply seedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h10_1 : seedBlock g 10 1 32=true := by
  apply seedCellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h10_33 : seedBlock g 10 33 82=true := by
  apply seedCellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h10_115 : seedBlock g 10 115 25=true := by
  apply seedCellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h11_0 : seedBlock g 11 0 6=true := by
  apply seedCellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h11_6 : seedBlock g 11 6 10=true := by
  apply seedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h12_0 : seedBlock g 12 0 1=true := by
  apply seedCellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 12 := by
  intro k h
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact (@seedBlock_merge g 8 0 24 12 h8_0 h8_24)
  · exact (@seedBlock_merge g 9 0 6 195 h9_0 (@seedBlock_merge g 9 6 148 47 h9_6 h9_154))
  · exact (@seedBlock_merge g 10 0 33 107 (@seedBlock_merge g 10 0 1 32 h10_0 h10_1) (@seedBlock_merge g 10 33 82 25 h10_33 h10_115))
  · exact (@seedBlock_merge g 11 0 6 10 h11_0 h11_6)
  · exact h12_0
end S383_0_1
namespace S383_0_4
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h8_0 : seedBlock g 8 0 58=true := by
  apply seedCellsBlock (ar:=8) (rows:=1) (d:=1)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h8_58 : seedBlock g 8 58 15=true := by
  apply seedCellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h9_0 : seedBlock g 9 0 10=true := by
  apply seedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h9_10 : seedBlock g 9 10 357=true := by
  apply seedCellsBlock (ar:=9) (rows:=1) (d:=4)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h9_367 : seedBlock g 9 367 111=true := by
  apply seedCellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h10_0 : seedBlock g 10 0 2=true := by
  apply seedCellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h10_2 : seedBlock g 10 2 73=true := by
  apply seedCellsBlock (ar:=9) (rows:=1) (d:=2)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h10_75 : seedBlock g 10 75 175=true := by
  apply seedCellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h10_250 : seedBlock g 10 250 53=true := by
  apply seedCellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h11_0 : seedBlock g 11 0 13=true := by
  apply seedCellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h11_13 : seedBlock g 11 13 15=true := by
  apply seedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h12_0 : seedBlock g 12 0 1=true := by
  apply seedCellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 12 := by
  intro k h
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact (@seedBlock_merge g 8 0 58 15 h8_0 h8_58)
  · exact (@seedBlock_merge g 9 0 10 468 h9_0 (@seedBlock_merge g 9 10 357 111 h9_10 h9_367))
  · exact (@seedBlock_merge g 10 0 75 228 (@seedBlock_merge g 10 0 2 73 h10_0 h10_2) (@seedBlock_merge g 10 75 175 53 h10_75 h10_250))
  · exact (@seedBlock_merge g 11 0 13 15 h11_0 h11_13)
  · exact h12_0
end S383_0_4
namespace S511_0_1
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h8_0 : seedBlock g 8 0 3=true := by
  apply seedCellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h9_0 : seedBlock g 9 0 13=true := by
  apply seedCellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h9_13 : seedBlock g 9 13 13=true := by
  apply seedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h10_0 : seedBlock g 10 0 27=true := by
  apply seedCellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h10_27 : seedBlock g 10 27 243=true := by
  apply seedCellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h10_270 : seedBlock g 10 270 40=true := by
  apply seedCellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h11_0 : seedBlock g 11 0 4=true := by
  apply seedCellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h11_4 : seedBlock g 11 4 163=true := by
  apply seedCellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h11_167 : seedBlock g 11 167 417=true := by
  apply seedCellsBlock (ar:=11) (rows:=1) (d:=4)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h11_584 : seedBlock g 11 584 53=true := by
  apply seedCellsBlock (ar:=12) (rows:=1) (d:=1)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h12_0 : seedBlock g 12 0 43=true := by
  apply seedCellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h12_43 : seedBlock g 12 43 118=true := by
  apply seedCellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h12_161 : seedBlock g 12 161 84=true := by
  apply seedCellsBlock (ar:=12) (rows:=1) (d:=2)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h13_0 : seedBlock g 13 0 7=true := by
  apply seedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h13_7 : seedBlock g 13 7 11=true := by
  apply seedCellsBlock (ar:=11) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem h14_0 : seedBlock g 14 0 1=true := by
  apply seedCellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [seedCells,seedBoxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem tb : seedCheckedTables g 14 := by
  intro k h
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact h8_0
  · exact (@seedBlock_merge g 9 0 13 13 h9_0 h9_13)
  · exact (@seedBlock_merge g 10 0 27 283 h10_0 (@seedBlock_merge g 10 27 243 40 h10_27 h10_270))
  · exact (@seedBlock_merge g 11 0 167 470 (@seedBlock_merge g 11 0 4 163 h11_0 h11_4) (@seedBlock_merge g 11 167 417 53 h11_167 h11_584))
  · exact (@seedBlock_merge g 12 0 43 202 h12_0 (@seedBlock_merge g 12 43 118 84 h12_43 h12_161))
  · exact (@seedBlock_merge g 13 0 7 11 h13_0 h13_7)
  · exact h14_0
end S511_0_1


set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb0 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 15) (chartGoal 15) 4) (pre : SeedLedger book0)
    (t : seedCheckedTables S15_0_1.g 3) : SeedLedger book1 :=
  seedLedger_cons (seedRootLower (g:=S15_0_1.g.toForest) major r pre sg0 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb1 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 15) (chartGoal 15) 4) (pre : SeedLedger book1)
    (t : seedCheckedTables S15_1_2.g 3) : SeedLedger book2 :=
  seedLedger_cons (seedRootLower (g:=S15_1_2.g.toForest) major r pre sg1 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb2 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 31) (chartGoal 31) 7) (pre : SeedLedger book2)
    (t : seedCheckedTables S31_0_1.g 6) : SeedLedger book3 :=
  seedLedger_cons (seedRootLower (g:=S31_0_1.g.toForest) major r pre sg2 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb3 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 47) (chartGoal 47) 5) (pre : SeedLedger book3)
    (t : seedCheckedTables S47_0_1.g 4) : SeedLedger book4 :=
  seedLedger_cons (seedRootLower (g:=S47_0_1.g.toForest) major r pre sg3 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb4 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 47) (chartGoal 47) 5) (pre : SeedLedger book4)
    (t : seedCheckedTables S47_0_5.g 4) : SeedLedger book5 :=
  seedLedger_cons (seedRootLower (g:=S47_0_5.g.toForest) major r pre sg4 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb5 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 55) (chartGoal 55) 5) (pre : SeedLedger book5)
    (t : seedCheckedTables S55_0_1.g 4) : SeedLedger book6 :=
  seedLedger_cons (seedRootLower (g:=S55_0_1.g.toForest) major r pre sg5 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb6 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 55) (chartGoal 55) 5) (pre : SeedLedger book6)
    (t : seedCheckedTables S55_0_4.g 4) : SeedLedger book7 :=
  seedLedger_cons (seedRootLower (g:=S55_0_4.g.toForest) major r pre sg6 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb7 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 55) (chartGoal 55) 5) (pre : SeedLedger book7)
    (t : seedCheckedTables S55_1_2.g 4) : SeedLedger book8 :=
  seedLedger_cons (seedRootLower (g:=S55_1_2.g.toForest) major r pre sg7 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb8 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 63) (chartGoal 63) 8) (pre : SeedLedger book8)
    (t : seedCheckedTables S63_0_1.g 7) : SeedLedger book9 :=
  seedLedger_cons (seedRootLower (g:=S63_0_1.g.toForest) major r pre sg8 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb9 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 63) (chartGoal 63) 8) (pre : SeedLedger book9)
    (t : seedCheckedTables S63_0_5.g 7) : SeedLedger book10 :=
  seedLedger_cons (seedRootLower (g:=S63_0_5.g.toForest) major r pre sg9 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb10 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 63) (chartGoal 63) 8) (pre : SeedLedger book10)
    (t : seedCheckedTables S63_1_2.g 7) : SeedLedger book11 :=
  seedLedger_cons (seedRootLower (g:=S63_1_2.g.toForest) major r pre sg10 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb11 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 63) (chartGoal 63) 8) (pre : SeedLedger book11)
    (t : seedCheckedTables S63_2_3.g 7) : SeedLedger book12 :=
  seedLedger_cons (seedRootLower (g:=S63_2_3.g.toForest) major r pre sg11 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb12 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 111) (chartGoal 111) 7) (pre : SeedLedger book12)
    (t : seedCheckedTables S111_0_1.g 6) : SeedLedger book13 :=
  seedLedger_cons (seedRootLower (g:=S111_0_1.g.toForest) major r pre sg12 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb13 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 111) (chartGoal 111) 7) (pre : SeedLedger book13)
    (t : seedCheckedTables S111_0_5.g 6) : SeedLedger book14 :=
  seedLedger_cons (seedRootLower (g:=S111_0_5.g.toForest) major r pre sg13 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb14 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 111) (chartGoal 111) 7) (pre : SeedLedger book14)
    (t : seedCheckedTables S111_1_6.g 6) : SeedLedger book15 :=
  seedLedger_cons (seedRootLower (g:=S111_1_6.g.toForest) major r pre sg14 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb15 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 119) (chartGoal 119) 6) (pre : SeedLedger book15)
    (t : seedCheckedTables S119_0_1.g 5) : SeedLedger book16 :=
  seedLedger_cons (seedRootLower (g:=S119_0_1.g.toForest) major r pre sg15 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb16 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 119) (chartGoal 119) 6) (pre : SeedLedger book16)
    (t : seedCheckedTables S119_0_4.g 5) : SeedLedger book17 :=
  seedLedger_cons (seedRootLower (g:=S119_0_4.g.toForest) major r pre sg16 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb17 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 189) (chartGoal 189) 8) (pre : SeedLedger book17)
    (t : seedCheckedTables S189_0_4.g 7) : SeedLedger book18 :=
  seedLedger_cons (seedRootLower (g:=S189_0_4.g.toForest) major r pre sg17 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb18 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 127) (chartGoal 127) 9) (pre : SeedLedger book18)
    (t : seedCheckedTables S127_0_1.g 8) : SeedLedger book19 :=
  seedLedger_cons (seedRootLower (g:=S127_0_1.g.toForest) major r pre sg18 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb19 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 127) (chartGoal 127) 9) (pre : SeedLedger book19)
    (t : seedCheckedTables S127_0_4.g 8) : SeedLedger book20 :=
  seedLedger_cons (seedRootLower (g:=S127_0_4.g.toForest) major r pre sg19 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb20 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 127) (chartGoal 127) 9) (pre : SeedLedger book20)
    (t : seedCheckedTables S127_0_5.g 8) : SeedLedger book21 :=
  seedLedger_cons (seedRootLower (g:=S127_0_5.g.toForest) major r pre sg20 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb21 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 127) (chartGoal 127) 9) (pre : SeedLedger book21)
    (t : seedCheckedTables S127_2_3.g 8) : SeedLedger book22 :=
  seedLedger_cons (seedRootLower (g:=S127_2_3.g.toForest) major r pre sg21 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb22 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 191) (chartGoal 191) 11) (pre : SeedLedger book22)
    (t : seedCheckedTables S191_0_1.g 10) : SeedLedger book23 :=
  seedLedger_cons (seedRootLower (g:=S191_0_1.g.toForest) major r pre sg22 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb23 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 191) (chartGoal 191) 11) (pre : SeedLedger book23)
    (t : seedCheckedTables S191_0_4.g 10) : SeedLedger book24 :=
  seedLedger_cons (seedRootLower (g:=S191_0_4.g.toForest) major r pre sg23 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb24 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 191) (chartGoal 191) 11) (pre : SeedLedger book24)
    (t : seedCheckedTables S191_3_4.g 10) : SeedLedger book25 :=
  seedLedger_cons (seedRootLower (g:=S191_3_4.g.toForest) major r pre sg24 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb25 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 255) (chartGoal 255) 12) (pre : SeedLedger book25)
    (t : seedCheckedTables S255_0_1.g 11) : SeedLedger book26 :=
  seedLedger_cons (seedRootLower (g:=S255_0_1.g.toForest) major r pre sg25 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb26 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 255) (chartGoal 255) 12) (pre : SeedLedger book26)
    (t : seedCheckedTables S255_0_4.g 11) : SeedLedger book27 :=
  seedLedger_cons (seedRootLower (g:=S255_0_4.g.toForest) major r pre sg26 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb27 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 383) (chartGoal 383) 13) (pre : SeedLedger book27)
    (t : seedCheckedTables S383_0_1.g 12) : SeedLedger book28 :=
  seedLedger_cons (seedRootLower (g:=S383_0_1.g.toForest) major r pre sg27 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem sb28 (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (r : Lower (vars 383) (chartGoal 383) 13) (pre : SeedLedger book28)
    (t : seedCheckedTables S383_0_4.g 12) : SeedLedger book29 :=
  seedLedger_cons (seedRootLower (g:=S383_0_4.g.toForest) major r pre sg28 t) pre
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem seedLast (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (pre : SeedLedger book29) (t : seedCheckedTables S511_0_1.g 14) :
    Impossible (chartGoal 511) 14 (vars 511 ++ [orRootSig 0 1]).toFinset :=
  seedRootClosed (g:=S511_0_1.g.toForest) major pre sg29 t


set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem seedFinal (major : ∀ q, Lower (vars q) (graphGoal q) (bounds511 q)) (lo15 : Lower (vars 15) (chartGoal 15) 4) (lo31 : Lower (vars 31) (chartGoal 31) 7) (lo47 : Lower (vars 47) (chartGoal 47) 5) (lo55 : Lower (vars 55) (chartGoal 55) 5) (lo63 : Lower (vars 63) (chartGoal 63) 8) (lo111 : Lower (vars 111) (chartGoal 111) 7) (lo119 : Lower (vars 119) (chartGoal 119) 6) (lo127 : Lower (vars 127) (chartGoal 127) 9) (lo189 : Lower (vars 189) (chartGoal 189) 8) (lo191 : Lower (vars 191) (chartGoal 191) 11) (lo255 : Lower (vars 255) (chartGoal 255) 12) (lo383 : Lower (vars 383) (chartGoal 383) 13)
    (t0 : seedCheckedTables S15_0_1.g 3)
    (t1 : seedCheckedTables S15_1_2.g 3)
    (t2 : seedCheckedTables S31_0_1.g 6)
    (t3 : seedCheckedTables S47_0_1.g 4)
    (t4 : seedCheckedTables S47_0_5.g 4)
    (t5 : seedCheckedTables S55_0_1.g 4)
    (t6 : seedCheckedTables S55_0_4.g 4)
    (t7 : seedCheckedTables S55_1_2.g 4)
    (t8 : seedCheckedTables S63_0_1.g 7)
    (t9 : seedCheckedTables S63_0_5.g 7)
    (t10 : seedCheckedTables S63_1_2.g 7)
    (t11 : seedCheckedTables S63_2_3.g 7)
    (t12 : seedCheckedTables S111_0_1.g 6)
    (t13 : seedCheckedTables S111_0_5.g 6)
    (t14 : seedCheckedTables S111_1_6.g 6)
    (t15 : seedCheckedTables S119_0_1.g 5)
    (t16 : seedCheckedTables S119_0_4.g 5)
    (t17 : seedCheckedTables S189_0_4.g 7)
    (t18 : seedCheckedTables S127_0_1.g 8)
    (t19 : seedCheckedTables S127_0_4.g 8)
    (t20 : seedCheckedTables S127_0_5.g 8)
    (t21 : seedCheckedTables S127_2_3.g 8)
    (t22 : seedCheckedTables S191_0_1.g 10)
    (t23 : seedCheckedTables S191_0_4.g 10)
    (t24 : seedCheckedTables S191_3_4.g 10)
    (t25 : seedCheckedTables S255_0_1.g 11)
    (t26 : seedCheckedTables S255_0_4.g 11)
    (t27 : seedCheckedTables S383_0_1.g 12)
    (t28 : seedCheckedTables S383_0_4.g 12)
    (t29 : seedCheckedTables S511_0_1.g 14) :
    Impossible graph 14 (inputs++[orRootSig 0 1]).toFinset := by
  have h0 : SeedLedger book0 := seedLedger_empty
  have h1 := sb0 major lo15 h0 t0
  have h2 := sb1 major lo15 h1 t1
  have h3 := sb2 major lo31 h2 t2
  have h4 := sb3 major lo47 h3 t3
  have h5 := sb4 major lo47 h4 t4
  have h6 := sb5 major lo55 h5 t5
  have h7 := sb6 major lo55 h6 t6
  have h8 := sb7 major lo55 h7 t7
  have h9 := sb8 major lo63 h8 t8
  have h10 := sb9 major lo63 h9 t9
  have h11 := sb10 major lo63 h10 t10
  have h12 := sb11 major lo63 h11 t11
  have h13 := sb12 major lo111 h12 t12
  have h14 := sb13 major lo111 h13 t13
  have h15 := sb14 major lo111 h14 t14
  have h16 := sb15 major lo119 h15 t15
  have h17 := sb16 major lo119 h16 t16
  have h18 := sb17 major lo189 h17 t17
  have h19 := sb18 major lo127 h18 t18
  have h20 := sb19 major lo127 h19 t19
  have h21 := sb20 major lo127 h20 t20
  have h22 := sb21 major lo127 h21 t21
  have h23 := sb22 major lo191 h22 t22
  have h24 := sb23 major lo191 h23 t23
  have h25 := sb24 major lo191 h24 t24
  have h26 := sb25 major lo255 h25 t25
  have h27 := sb26 major lo255 h26 t26
  have h28 := sb27 major lo383 h27 t27
  have h29 := sb28 major lo383 h28 t28
  exact seedLast major h29 t29

def seed3095 : Sig := bin true (inputs.getD 0 zero) (inputs.getD 1 zero)
theorem seed_table : ∀ r : Row, bit r seed3095 = (sample r 0 || sample r 1) := by decide +kernel
theorem seed_nonzero : seed3095 ≠ zero := by decide +kernel
def absent3095 (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< ([1,0,1,2,3,0,1,2,3] : List Nat).getD i.val 0)
def present3095 (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (absent3095 i).val)

theorem seed_witness : ∀ i : Fin 9,
    (bit (absent3095 i) graph != bit (present3095 i) graph) &&
    ((inputs++[seed3095]).all fun w => w == inputs.getD i.val zero ||
      bit (absent3095 i) w == bit (present3095 i) w) = true := by decide +kernel

theorem all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[seed3095]) :
    S=inputs.toFinset ∨ S=(inputs++[seed3095]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := seed_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (absent3095 i) (present3095 i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : seed3095 ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hseed)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx := sub w hw
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hseed hw)) needed

theorem seededSolution : Impossible graph 14 (inputs++[seed3095]).toFinset :=
  seedFinal bounds511_sound low15 low31 low47 low55 low63 low111 low119 low127 low189 low191 low255 low383
    S15_0_1.tb S15_1_2.tb S31_0_1.tb S47_0_1.tb S47_0_5.tb S55_0_1.tb S55_0_4.tb S55_1_2.tb S63_0_1.tb S63_0_5.tb S63_1_2.tb S63_2_3.tb S111_0_1.tb S111_0_5.tb S111_1_6.tb S119_0_1.tb S119_0_4.tb S189_0_4.tb S127_0_1.tb S127_0_4.tb S127_0_5.tb S127_2_3.tb S191_0_1.tb S191_0_4.tb S191_3_4.tb S255_0_1.tb S255_0_4.tb S383_0_1.tb S383_0_4.tb S511_0_1.tb


-- The lower bound with an extra OR wire was proved in L-meta-3095 (PR 8372).
-- Here the final conjunction costs one gate, so thirteen preceding gates would violate the bound.

theorem exact2193 (dead : Impossible graph 14 inputs.toFinset) (full : Impossible graph 14 (inputs++[seed3095]).toFinset) : ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : Fin (13 : ℕ)),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       (∀ (x5 : Fin x1.length), ∀ x6 ∈ (x1.get x5).inputs, x6 < (10 : ℕ) + ↑x5) →         (∀ (x6 : Fin (9 : ℕ)), ∃ x7 ∈ x1, ↑x6 ∈ x7.inputs) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ))]);             (x8.getD ((10 : ℕ) + ↑x2) Bool.false && x8.getD (22 : ℕ) Bool.false) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := by
  intro gs ix size fan _ _
  let i : Nat := 10 + ix.val
  let j : Nat := 22
  by_contra! eq
  let bank := inputs++[seed3095]
  let out := execute gs bank
  have bits (r : Row) : out.map (bit r) =
      (Circuit.mk gs 0).wires (List.ofFn (sample r)++[sample r 0 || sample r 1]) := by
    change (execute gs bank).map (bit r) = _
    rw [execute_bits _ _ _ (fun g hg => (fan g hg).1)]
    have e : bank.map (bit r) = List.ofFn (sample r)++[sample r 0 || sample r 1] := by
      simp [bank,←sampled,seed_table]
    rw [e]
    rfl
  have target : bin false (out.getD i zero) (out.getD j zero) = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro n hn
    let r : Row := ⟨n,hn⟩
    change bit r _ = bit r graph
    rw [bit_bin,←b_read,←b_read,bits r,edge_table]
    exact Classical.not_not.mp (eq (sample r))
  let g : Gate := ⟨.and,[i,j]⟩
  have hgate : gv out g=graph := by
    change bin false (out.getD i zero) (bin false (out.getD j zero) one) = graph
    simpa only [bin, Bool.false_eq_true, if_false,one,BitVec.and_allOnes] using target
  have ht : graph ∈ execute (gs++[g]) bank := by
    change graph ∈ List.foldl _ bank (gs++[g])
    rw [List.foldl_append]
    change graph ∈ out++[gv out g]
    rw [hgate]
    simp
  have legal : ∀ v∈gs++[g],v.op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ v.inputs.length≤2 := by
    intro v hv
    simp only [List.mem_append,List.mem_singleton] at hv
    rcases hv with h|rfl
    · exact fan _ h
    · simp [g]
  obtain ⟨k,t,S,hk,l,hs⟩ := extract (gs++[g]) bank legal graph_proper ht
  have cap : k≤14 := by simpa only [List.length_append,List.length_singleton,size] using hk
  rcases all_roots l hs with e|e
  · exact dead k t cap (e ▸ l)
  · exact full k t cap (e ▸ l)

end PEqualNP.Outside.L_meta_2193
theorem PEqualNP.Outside.L_meta_2193 : ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : Fin (13 : ℕ)),   x1.length = (13 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →       (∀ (x5 : Fin x1.length), ∀ x6 ∈ (x1.get x5).inputs, x6 < (10 : ℕ) + ↑x5) →         (∀ (x6 : Fin (9 : ℕ)), ∃ x7 ∈ x1, ↑x6 ∈ x7.inputs) →           ∃ (x7 : Fin (9 : ℕ) → Bool),             have x8 : List Bool := { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x7 ++ [x7 (0 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ))]);             (x8.getD ((10 : ℕ) + ↑x2) Bool.false && x8.getD (22 : ℕ) Bool.false) ≠ (x7 (0 : Fin (9 : ℕ)) && x7 (1 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (2 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (3 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (4 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) && x7 (0 : Fin (9 : ℕ)) || x7 (0 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ)) || x7 (1 : Fin (9 : ℕ)) && x7 (6 : Fin (9 : ℕ)) || x7 (2 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (3 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (5 : Fin (9 : ℕ)) && x7 (7 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)) && x7 (8 : Fin (9 : ℕ)) || x7 (8 : Fin (9 : ℕ)) && x7 (5 : Fin (9 : ℕ))) := PEqualNP.Outside.L_meta_2193.exact2193 PEqualNP.Outside.L_meta_2193.dead_start PEqualNP.Outside.L_meta_2193.seededSolution
