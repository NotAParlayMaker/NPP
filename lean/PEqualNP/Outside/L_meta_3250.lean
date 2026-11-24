import Mathlib
import PEqualNP.Defs

-- The checker and the plain bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
namespace PEqualNP.Outside.L_meta_3250
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

def Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | 0,t,S => t=0 ∧ S={target} ∧ proper target
  | k+1,t,S =>
    (∃ (u : Nat) (U : Finset Sig) (a : Sig), t=u+1 ∧ S=insert a U ∧ proper a ∧
      neg a ∉ insert a U ∧ Live target k u (insert (neg a) U)) ∨
    (∃ (U : Finset Sig) (a b : Sig) (d : Bool), S=insert a (insert b U) ∧ proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live target k t (insert (bin d a b) U))
theorem Live.stop {target : Sig} (hp : proper target) : Live target 0 0 {target} := ⟨rfl,rfl,hp⟩
theorem Live.unary {target : Sig} {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
    (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
    Live target (k+1) (t+1) (insert a U) :=
  Or.inl ⟨t,U,a,rfl,rfl,ha,hfresh,tail⟩
theorem Live.binary {target : Sig} {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
    Live target (k+1) t (insert a (insert b U)) :=
  Or.inr ⟨U,a,b,d,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {target : Sig} {motive : ∀ (k t : Nat) (S : Finset Sig), Live target k t S → Prop}
    (stop : ∀ (hp : proper target), motive 0 0 {target} (Live.stop hp))
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)),
      motive k t (insert (neg a) U) tail → motive (k+1) (t+1) (insert a U) (Live.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)),
      motive k t (insert (bin d a b) U) tail →
      motive (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hfresh tail))
    {k t : Nat} {S : Finset Sig} (h : Live target k t S) : motive k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail (ih tail)
    · exact binary ha hb hab hf tail (ih tail)

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using Live.ind with
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

def Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => (∃ bank a, Reach roots p bank ∧ Available bank a ∧ c=inv a :: bank) ∨
    (∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach roots p bank ∧ Available bank a ∧
      Available bank b ∧ c=combine op a b :: bank)
theorem Reach.start {R} {roots : List (Wire R)} : Reach roots 0 roots := rfl
theorem Reach.one {R} {roots : List (Wire R)} {p bank a} (h : Reach roots p bank)
    (ha : Available bank a) : Reach roots (p+1) (inv a :: bank) := Or.inl ⟨bank,a,h,ha,rfl⟩
theorem Reach.two {R} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) : Reach roots (p+1) (combine op a b :: bank) :=
  Or.inr ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R} {roots : List (Wire R)} {motive : ∀ p bank, Reach roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (one : ∀ {p bank a} (h : Reach roots p bank) (ha : Available bank a), motive p bank h →
      motive (p+1) (inv a :: bank) (Reach.one h ha))
    (two : ∀ {p bank a b} (op : Bool) (h : Reach roots p bank) (ha : Available bank a)
      (hb : Available bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    rcases h with ⟨bank,a,h,ha,rfl⟩ | ⟨op,bank,a,b,h,ha,hb,rfl⟩
    · exact one h ha (ih h)
    · exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => (∃ (save : Bool) (a : Wire R) (rest : List (Wire R)), (a::rest).Perm zs ∧
      Run goal s (inv a :: kept save a rest)) ∨
    (∃ (op ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), (a::b::rest).Perm zs ∧
      Run goal s (combine op a b :: kept ka a (kept kb b rest)))
theorem Run.stop {R} {goal : Wire R} : Run goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run goal s xs) : Run goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    rcases h with ⟨save,a,rest,q,h⟩ | ⟨op,ka,kb,a,b,rest,q,h⟩
    · exact Or.inl ⟨save,a,rest,q.trans p,h⟩
    · exact Or.inr ⟨op,ka,kb,a,b,rest,q.trans p,h⟩
theorem Run.one {R} {goal : Wire R} {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool)
    (h : Run goal s (inv a :: kept save a rest)) : Run goal (s+1) (a::rest) :=
  Or.inl ⟨save,a,rest,List.Perm.refl _,h⟩
theorem Run.two {R} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool)
    (h : Run goal s (combine op a b :: kept ka a (kept kb b rest))) : Run goal (s+1) (a::b::rest) :=
  Or.inr ⟨op,ka,kb,a,b,rest,List.Perm.refl _,h⟩
theorem Run.ind {R} {goal : Wire R} {motive : ∀ s ws, Run goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (one : ∀ {s a rest} (save : Bool) (h : Run goal s (inv a :: kept save a rest)),
      motive s _ h → motive (s+1) (a::rest) (Run.one save h))
    (two : ∀ {s a b rest} (op ka kb : Bool) (h : Run goal s (combine op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op ka kb h))
    {s ws} (h : Run goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    rcases h with ⟨save,a,rest,p,h⟩ | ⟨op,ka,kb,a,b,rest,p,h⟩
    · exact perm p (Run.one save h) (one save h (ih h))
    · exact perm p (Run.two op ka kb h) (two op ka kb h (ih h))

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
  induction h using Run.ind generalizing p bank with
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
  induction h using Run.ind with
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
  induction h using Live.ind generalizing v with
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
  induction h using Reach.ind generalizing k t S with
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
  induction h using Live.ind with
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
def seed : Sig := bin true (inputs.getD 0 zero) (inputs.getD 6 zero)

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 || sample r 6) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed_nonzero : seed ≠ zero := by decide +kernel
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

theorem initial_live (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t S, k ≤ 14 ∧ Live graph k t S ∧ ∀ a ∈ S, a ∈ inputs++[seed] := by
  have headEq : (execute C.gates inputs).getD 9 zero = seed := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (seed_table r).symm)
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have out := get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  cases hgs : C.gates with
  | nil =>
    rw [hgs] at headEq
    exact False.elim (seed_nonzero headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g = seed := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = seed at headEq
      obtain ⟨l,hl⟩ := exec_extends gs (inputs++[gv inputs g])
      rw [hl] at headEq
      exact headEq
    rw [hgs] at targetIn
    change graph ∈ execute gs (inputs++[gv inputs g]) at targetIn
    rw [eq0] at targetIn
    have tailLegal : ∀ gate ∈ gs, gate.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ gate.inputs.length≤2 := by
      intro gate hg
      apply legal
      rw [hgs]
      exact List.mem_cons_of_mem _ hg
    obtain ⟨k,t,S,hk,run,hs⟩ := extract gs _ tailLegal graph_proper targetIn
    have len : gs.length+1 ≤ 15 := by simpa [Circuit.size,hgs] using small
    exact ⟨k,t,S,by omega,run,hs⟩


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
  induction h using Live.ind with
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
  induction h using Live.ind with
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
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail _ =>
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
  | @binary k t U a b d ha hb hab hf tail _ =>
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
def typeWord (t : Nat) : Sig :=
  if t/81==2 then neg (inputs.getD (t/9 % 9) zero)
  else bin (t/81==1) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
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

def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

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
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.2.2.1/512)
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · subst hq
    simp only [colCheck,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower (varsX rep) (graphGoal rep) L) : Lower (varsX old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (varsX q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires ∧ True

theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

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
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
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

def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op)

theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

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

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
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
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
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
  exact closeChild_sound pv lv nd' test k t hk h


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

theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨_,hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
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
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
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
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g : Forest) : Nat := g.1
def Forest.cap (g : Forest) : Nat := g.2.1
def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1
def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
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
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)

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
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
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
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5+32*packedAt data (pos+5) lw
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
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
    obtain ⟨_,hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
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
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
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
theorem root_index {g top prior k i ws} (low : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
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

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (varsX (rawMask g.mask ci)) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (varsX e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (varsX m) (graphGoal m) L)
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
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
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
  let nr := packedAt data pos 5+32*packedAt data (pos+5) lw
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls)


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
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : List ColumnInfo := []
def g15autos : List (List Nat) := [[],[33,48]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
def key31l6 (i : Nat) : Nat := 0x820007028af371d000003180048302e380000000003819155875690d58000003d
def g31d5 (i : Nat) : Nat := 0x84001e90fd02fd01fa00
def g31l5 : Packing := (3,1,3,0,4,4,0,g31d5)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,2,4,0,0,g31d6)
def g31samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : List ColumnInfo := [(1,0,30,0,4),(2,0,29,0,4),(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]
def g31autos : List (List Nat) := [[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : List ColumnInfo := [(8,0,39,0,4)]
def g47autos : List (List Nat) := [[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : List ColumnInfo := [(16,0,39,0,4)]
def g55autos : List (List Nat) := [[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : List ColumnInfo := [(32,0,31,0,7)]
def g63autos : List (List Nat) := [[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : List ColumnInfo := [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)]
def g111autos : List (List Nat) := [[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : List ColumnInfo := [(4,0,115,0,5)]
def g119autos : List (List Nat) := [[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat → Packing
  | _ => emptyPacking
def g119index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest := ⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index⟩
def key189l7 (i : Nat) : Nat := 0xa81337040d4b600002948880000590cc33d41450272020001b1
def g189d6 (i : Nat) : Nat := 0x82000f487f40bfa03fa00
def g189l6 : Packing := (3,1,3,0,4,4,0,g189d6)
def g189d7 (i : Nat) : Nat := 0x1f5859bf
def g189l7 : Packing := (1,0,3,2,4,0,0,g189d7)
def g189samples : Array (Bits × Bits) := #[(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : List ColumnInfo := [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4),(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]
def g189autos : List (List Nat) := [[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples : Array (Bits × Bits) := #[(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : List ColumnInfo := [(32,0,95,0,8)]
def g127autos : List (List Nat) := [[],[101,66,16]]
def g127levels : Nat → Packing
  | _ => emptyPacking
def g127index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest := ⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,g127index⟩
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
def g191columns : List ColumnInfo := [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7),(6,0,185,0,5),(8,0,183,0,8),(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5),(4,8,163,16,5),(14,0,177,0,4),(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5),(19,0,172,0,4),(24,0,167,0,7),(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4),(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5),(35,0,156,0,4),(40,0,151,0,5),(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8),(130,0,61,0,5),(4,128,27,32,5),(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5),(32,128,27,4,5),(161,0,30,0,4),(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)]
def g191autos : List (List Nat) := [[],[84,115],[117,67,32],[116,83,32]]
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
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
def g251samples : Array (Bits × Bits) := #[(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : List ColumnInfo := [(8,0,243,0,7)]
def g251autos : List (List Nat) := [[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : List ColumnInfo := [(64,0,191,0,11)]
def g255autos : List (List Nat) := [[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat → Packing
  | _ => emptyPacking
def g255index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,g255index⟩
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
def g383columns : List ColumnInfo := [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9),(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6),(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5),(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8),(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11),(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5),(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5),(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5),(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7),(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11),(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5),(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7),(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6),(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5),(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5),(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)]
def g383autos : List (List Nat) := [[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
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
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3 : Lower (vars 3) (graphGoal 3) 1 := size_of (hints:=1) (by decide +kernel)
def maps3 : List (Nat × List Nat) := []
def known3 := extendKnown [] 1 maps3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3 : Known known3 := extendKnown_ok (m:=3) baseKnown low3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 2 := size_of (hints:=257) (by decide +kernel)
def maps7 : List (Nat × List Nat) := []
def known7 := extendKnown known3 2 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7 := extendKnown_ok (m:=7) valid3 low7 (by decide +kernel)
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
theorem valid15 : Known known15 := extendKnown_ok (m:=15) valid7 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45 : Lower (vars 45) (graphGoal 45) 3 := size_of (hints:=8965) (by decide +kernel)
def maps45 : List (Nat × List Nat) := []
def known45 := extendKnown known15 3 maps45
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid45 : Known known45 := extendKnown_ok (m:=45) valid15 low45 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low51 : Lower (vars 51) (graphGoal 51) 3 := size_of (hints:=1) (by decide +kernel)
def maps51 : List (Nat × List Nat) := []
def known51 := extendKnown known45 3 maps51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid51 : Known known51 := extendKnown_ok (m:=51) valid45 low51 (by decide +kernel)
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
theorem valid31 : Known known31 := extendKnown_ok (m:=31) valid51 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 5 :=
  lower_discard (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (before_sound known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat) := [(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47 := extendKnown known31 5 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47 := extendKnown_ok (m:=47) valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 5 :=
  lower_discard (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (before_sound known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat) := [(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55 := extendKnown known47 5 maps55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known known55 := extendKnown_ok (m:=55) valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_discard (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (before_sound known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat) := [(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63 := extendKnown known55 8 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63 := extendKnown_ok (m:=63) valid55 low63 (by decide +kernel)
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
theorem valid111 : Known known111 := extendKnown_ok (m:=111) valid63 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  lower_discard (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (before_sound known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat) := [(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119 := extendKnown known111 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119 := extendKnown_ok (m:=119) valid111 low119 (by decide +kernel)
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
theorem valid189 : Known known189 := extendKnown_ok (m:=189) valid119 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 5 := size_of (hints:=1366507616) (by decide +kernel)
def maps250 : List (Nat × List Nat) := []
def known250 := extendKnown known189 5 maps250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid250 : Known known250 := extendKnown_ok (m:=250) valid189 low250 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  lower_discard (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (before_sound known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat) := [(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127 := extendKnown known250 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127 := extendKnown_ok (m:=127) valid250 low127 (by decide +kernel)
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
theorem valid191 : Known known191 := extendKnown_ok (m:=191) valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 8 :=
  lower_discard (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (before_sound known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat) := [(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251 := extendKnown known191 8 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251 := extendKnown_ok (m:=251) valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 12 :=
  lower_discard (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (before_sound known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255 := extendKnown known251 12 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok (m:=255) valid251 low255 (by decide +kernel)
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
theorem valid383 : Known known383 := extendKnown_ok (m:=383) valid255 low383 (by decide +kernel)
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
def deadsamples : Array (Bits × Bits) := #[(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadcolumns : List ColumnInfo := [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12),(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12),(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7),(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12),(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9),(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6),(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11),(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7),(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8),(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6),(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8),(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6),(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8),(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13),(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8),(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7),(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7),(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13),(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9),(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5),(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6),(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11),(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8),(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11),(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8),(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7),(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5),(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6),(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6),(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9),(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5),(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]
def deadautos : List (List Nat) := [[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
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
def dead : Forest := ⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,deadlevels,deadindex⟩
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
def hashrestrictedl13 (i : Nat) : Nat := 0x3266d629c3000cc09800002c5a916a703a921aa561d5132e8d2800000381db0ef80ad078788712ce0036333c001b9c02082090848
def hashrestrictedl12 (i : Nat) : Nat := 0x62203295be14261132f30f3f1b40f70c8570ea66463a299d46c1ba2855693691546f740aeb454505f848713832723d0330abaef704500000000000000000002246c7f88ca8ddb1706419d9dfb457c0dd31f15082e0960004df3cf70400398003d17a2e309f11f451c7ee3c12b621bf3c50e3a1244b5ac092482789280c6564dc983c8302b1b20b118a5000015fc042239f2935ba13ff30f307a60f4e277ab838768f4897601ade5b3cc02721800000040b41f3cd8ce1d764963e1314d739b00162400126810b794f6be00053524d7cba0002ad8002c0325551ae8fc431233c90982be9e00000000034280009902110cb80007548254000000f1d800124d8a5e47463801066bfc798d0000b73042ca022e292214900000004943bd408c0000000005cc584c000c8b8002534e7c000622267486115380024940580007aa1947a4c4a8696fd33d25c0d7104063e0ecbc168c6eab8544eeabead2c83731524e6b306c0d0e1c4a7181079a312f870459c1949b742b43a40fe50dc8574d5a519b98ac54ed289cdc149c2f696baac46c504797113ed0d22df2d4cbc0010484160000231227702a9c9c08c67c09295f541c2a112421e513a8f00011e703768da14b1f5e046066c37470001c9cc81a1a4000000510127b5220000000000d36c76a3a000140e000bcd80000011496038b063a005800610001005489e36724000a60786185c2900f1439b5a08b00124c018022858000b4043180008626004825c0c3870a0401806148870c0c2800a1c3000204301042c184
theorem slice_self {raw : List Sig} {T : Sig} {L : Nat} (pT : proper T) (h : Lower raw T L) :
    Slice raw T one L := by
  refine ⟨id,raw,fun r => bit_one r,fun a ha => ?_,observe_proper pT,h⟩
  exact Or.inl (List.mem_map_of_mem ha)

theorem plainA {m q cap : Nat} {prior : Nat → Nat} (low : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
    (e : (graphGoal q == graphGoal m && (varsX q == vars m) && (prior q == cap+1) && properB (graphGoal m) &&
      decide (vars m).Nodup && poolCut one (cap+1) cap 0 (vars m) (vars m)) = true) :
    Impossible (graphGoal m) cap (vars m).toFinset := by
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩ := e
  have h := low q
  rw [e1,e2,e3] at h
  exact poolCut_sound (slice_self (proper_of _ e4) h) [] rfl e5 e6

theorem cut_root {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Lower (varsX q) (graphGoal q) (prior q)) (ci : ColumnInfo)
    (ok : colCheck m ci prior = true)
    (cut : (decide ws.Nodup && poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (col_sound ci prior low ok) [] rfl cut.1 cut.2

theorem index_root {g : Forest} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (low : ∀ q, Lower (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g cap)
    (idx : indexedRoot g cap i ws = true) : Impossible (graphGoal m) cap ws.toFinset := by
  subst hm
  exact root_index low geom blocks (Nat.le_refl _) idx


def witPairs (m : Nat) (rs : List Nat) : List (Sig × Row × Row) :=
  ((selected m).zip rs).map fun x => (x.1.2,Fin.ofNat 512 x.2,Fin.ofNat 512 (x.2 ||| (1 <<< x.1.1)))
def fullOK (m : Nat) (rs : List Nat) : Bool :=
  let xs := witPairs m rs
  checkEssential (graphGoal m) (varsX m) xs && (xs.map Prod.fst == vars m) &&
    properB (graphGoal m) && decide (varsX m = vars m ++ [typeWord (m/512-1)])
theorem full_split {m : Nat} {rs : List Nat} (ok : fullOK m rs = true) {k t : Nat} {S : Finset Sig}
    (h : Live (graphGoal m) k t S) (sub : ∀ v ∈ S, v ∈ varsX m) :
    S=(vars m).toFinset ∨ S=(varsX m).toFinset := by
  simp only [fullOK,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨ess,alls⟩,_⟩,hX⟩ := ok
  have rest : ∀ v ∈ vars m, v ∈ S := by
    intro v hv
    rw [←alls] at hv
    obtain ⟨r,s,hd,hi⟩ := essential_ok ess v (List.mem_toFinset.mpr hv)
    exact raw_required h (varsX m) v sub r s hd hi
  have mem : ∀ v, v ∈ varsX m ↔ v ∈ vars m ∨ v=typeWord (m/512-1) := by
    intro v; rw [hX]; simp
  by_cases hs : typeWord (m/512-1) ∈ S
  · refine Or.inr ?_
    ext v
    rw [List.mem_toFinset]
    refine ⟨sub v,fun hv => ?_⟩
    rcases (mem v).mp hv with hv | rfl
    · exact rest v hv
    · exact hs
  · refine Or.inl ?_
    ext v
    rw [List.mem_toFinset]
    refine ⟨fun hv => ?_,rest v⟩
    rcases (mem v).mp (sub v hv) with hv | rfl
    · exact hv
    · exact absurd hv hs
theorem strong_full {m q cap : Nat} {rs : List Nat} (ok : fullOK m rs = true)
    (e : graphGoal m = graphGoal q) (ev : vars m = vars q)
    (a : Impossible (graphGoal q) cap (vars q).toFinset)
    (b : Impossible (graphGoal q) cap (varsX m).toFinset) :
    Lower (varsX m) (graphGoal m) (cap+1) := by
  have ok' := ok
  simp only [fullOK,Bool.and_eq_true] at ok'
  intro p bank hr ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live (proper_of _ ok'.1.2) hr ha
  by_contra! small
  rcases full_split ok run hs with h | h
  · rw [ev] at h; rw [e,h] at run; exact a k t (by omega) run
  · rw [e,h] at run; exact b k t (by omega) run

def dropOK (m : Nat) (hd : Sig) (rs : List Nat) (u v : Nat) : Bool :=
  let xs := (witPairs m rs).filter (fun x => x.1 != hd)
  checkEssential (graphGoal m) (varsX m) xs &&
    (vars m).all (fun w => w == hd || (xs.map Prod.fst).contains w) &&
    (vars m).contains hd &&
    properB (graphGoal m) && decide (varsX m = vars m ++ [typeWord (m/512-1)]) &&
    (bit (Fin.ofNat 512 u) (graphGoal m) != bit (Fin.ofNat 512 v) (graphGoal m)) &&
    (varsX m).all (fun w => w == hd || w == typeWord (m/512-1) ||
      bit (Fin.ofNat 512 u) w == bit (Fin.ofNat 512 v) w)
def varsD (m : Nat) (hd : Sig) : List Sig := (vars m).filter (fun w => w != hd) ++ [typeWord (m/512-1)]
theorem drop_split {m : Nat} {hd : Sig} {rs : List Nat} {u v : Nat} (ok : dropOK m hd rs u v = true)
    {k t : Nat} {S : Finset Sig}
    (h : Live (graphGoal m) k t S) (sub : ∀ v ∈ S, v ∈ varsX m) :
    S=(vars m).toFinset ∨ S=(varsX m).toFinset ∨ S=(varsD m hd).toFinset := by
  simp only [dropOK,Bool.and_eq_true,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨⟨⟨ess,alls⟩,hc⟩,_⟩,hX⟩,diff⟩,iso⟩ := ok
  have hm : hd ∈ vars m := by simpa using hc
  have rest : ∀ v ∈ vars m, v ≠ hd → v ∈ S := by
    intro v hv hne
    have hx := List.all_eq_true.mp alls v hv
    simp only [Bool.or_eq_true,beq_iff_eq,hne,false_or,List.contains_eq_mem,decide_eq_true_eq] at hx
    obtain ⟨r,s,hd,hi⟩ := essential_ok ess v (List.mem_toFinset.mpr hx)
    exact raw_required h (varsX m) v sub r s hd hi
  have mem : ∀ v, v ∈ varsX m ↔ v ∈ vars m ∨ v=typeWord (m/512-1) := by
    intro v; rw [hX]; simp
  have memD : ∀ v, v ∈ varsD m hd ↔ (v ∈ vars m ∧ v ≠ hd) ∨ v=typeWord (m/512-1) := by
    intro v; simp [varsD]
  have one : hd ∈ S ∨ typeWord (m/512-1) ∈ S := by
    obtain ⟨w,hw,hne⟩ := live_row_difference h (bne_iff_ne.mp diff)
    have hc := List.all_eq_true.mp iso w (sub w hw)
    simp only [Bool.or_eq_true,beq_iff_eq] at hc
    rcases hc with (rfl | rfl) | hc
    · exact Or.inl hw
    · exact Or.inr hw
    · exact False.elim (hne hc)
  by_cases hs : typeWord (m/512-1) ∈ S
  · refine Or.inr ?_
    by_cases hh : hd ∈ S
    · refine Or.inl ?_
      ext v
      rw [List.mem_toFinset]
      refine ⟨sub v,fun hv => ?_⟩
      rcases (mem v).mp hv with hv | rfl
      · by_cases e : v=hd
        · exact e ▸ hh
        · exact rest v hv e
      · exact hs
    · refine Or.inr ?_
      ext v
      rw [List.mem_toFinset,memD]
      constructor
      · intro hv
        rcases (mem v).mp (sub v hv) with h1 | h1
        · exact Or.inl ⟨h1,fun e => hh (e ▸ hv)⟩
        · exact Or.inr h1
      · rintro (⟨h1,h2⟩ | rfl)
        · exact rest v h1 h2
        · exact hs
  · have hh := one.resolve_right hs
    refine Or.inl ?_
    ext v
    rw [List.mem_toFinset]
    constructor
    · intro hv
      rcases (mem v).mp (sub v hv) with h1 | rfl
      · exact h1
      · exact absurd hv hs
    · intro hv
      by_cases e : v=hd
      · exact e ▸ hh
      · exact rest v hv e
theorem strong_drop {m q cap : Nat} {hd : Sig} {rs : List Nat} {u v : Nat} (ok : dropOK m hd rs u v = true)
    (e : graphGoal m = graphGoal q) (ev : vars m = vars q)
    (a : Impossible (graphGoal q) cap (vars q).toFinset)
    (b : Impossible (graphGoal q) cap (varsX m).toFinset)
    (c : Impossible (graphGoal q) cap (varsD m hd).toFinset) :
    Lower (varsX m) (graphGoal m) (cap+1) := by
  have ok' := ok
  simp only [dropOK,Bool.and_eq_true] at ok'
  intro p bank hr ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live (proper_of _ ok'.1.1.1.2) hr ha
  by_contra! small
  rcases drop_split ok run hs with h | h | h
  · rw [ev] at h; rw [e,h] at run; exact a k t (by omega) run
  · rw [e,h] at run; exact b k t (by omega) run
  · rw [e,h] at run; exact c k t (by omega) run

def sh (i : Nat) : Nat := if i<8 then ([1,0,5,8,2,4,7,3] : List Nat).getD i 0 else i+1
def shG (g : Gate) : Gate := ⟨g.op,g.inputs.map sh⟩
def stepW (w : List Bool) (g : Gate) : List Bool := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def RelW (w v : List Bool) : Prop :=
  9 ≤ w.length ∧ v.length = w.length+1 ∧ ∀ i, v.getD (sh i) false = w.getD i false
theorem getD_push (l : List Bool) (a : Bool) (i : Nat) :
    (l++[a]).getD i false = if i<l.length then l.getD i false else if i=l.length then a else false := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h : i<l.length
  · simp [h,List.getElem?_append_left h]
  · by_cases e : i=l.length
    · subst e; simp
    · have : l.length+1 ≤ i := by omega
      simp [h,e,List.getElem?_eq_none_iff.mpr (show (l++[a]).length ≤ i by simpa using this)]
theorem sh_lt {i n : Nat} (hn : 9 ≤ n) : sh i < n+1 ↔ i<n := by
  unfold sh
  split
  next h => interval_cases i <;> simp <;> omega
  next h => omega
theorem sh_eq {i n : Nat} (hn : 9 ≤ n) : sh i = n+1 ↔ i=n := by
  unfold sh
  split
  next h => interval_cases i <;> simp <;> omega
  next h => omega
theorem rel_push {w v : List Bool} (h : RelW w v) (a : Bool) : RelW (w++[a]) (v++[a]) := by
  obtain ⟨h1,h2,h3⟩ := h
  refine ⟨by simp; omega,by simp [h2],fun i => ?_⟩
  rw [getD_push,getD_push,h2,h3]
  simp only [sh_lt h1,sh_eq h1]
theorem rel_fold (gs : List Gate) {w v : List Bool} (h : RelW w v) :
    RelW (gs.foldl stepW w) ((gs.map shG).foldl stepW v) := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.map_cons,List.foldl_cons]
    apply ih
    have e : (shG g).op.eval ((shG g).inputs.map fun i => v.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [shG,List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact h.2.2 i
    unfold stepW
    rw [e]
    exact rel_push h _
theorem fold_prefix (gs : List Gate) (w : List Bool) (i : Nat) (hi : i<w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,ih _ (by simp [stepW]; omega)]
    unfold stepW
    rw [getD_push,if_pos hi]
theorem wires_fold (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl
def joined (x2 x3 : Circuit) (x4 : Nat) : Circuit :=
  ⟨⟨GateOp.or,[0,6]⟩ :: (x2.gates.map shG ++ ⟨GateOp.or,[sh x4,6]⟩ :: x3.gates.map shG),sh x3.output⟩
def pull (y : Fin 9 → Bool) (j : Fin 8) : Bool := y (([1,0,5,8,2,4,7,3] : List (Fin 9)).getD j.val 0)
theorem rel_start (y : Fin 9 → Bool) :
    RelW (List.ofFn (pull y) ++ [pull y 1 || y 6]) (List.ofFn y ++ [y 0 || y 6]) := by
  refine ⟨by simp,by simp,fun i => ?_⟩
  by_cases h : i<9
  · interval_cases i <;> simp [sh,List.ofFn_succ,pull]
  · have hs : sh i = i+1 := by unfold sh; rw [if_neg (by omega)]
    rw [hs,getD_push,getD_push]
    simp only [List.length_ofFn]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
theorem joined_value (x2 x3 : Circuit) (x4 : Nat) (y : Fin 9 → Bool) :
    ((joined x2 x3 x4).wires (List.ofFn y)).getD 9 false = (y 0 || y 6) ∧
    (joined x2 x3 x4).eval (List.ofFn y) =
      x3.eval (x2.wires (List.ofFn (pull y) ++ [pull y 1 || y 6]) ++
        [(x2.wires (List.ofFn (pull y) ++ [pull y 1 || y 6])).getD x4 false || y 6]) := by
  have g0 : stepW (List.ofFn y) ⟨GateOp.or,[0,6]⟩ = List.ofFn y ++ [y 0 || y 6] := by
    simp [stepW,GateOp.eval,List.ofFn_succ]
  have e : (joined x2 x3 x4).wires (List.ofFn y) = (x3.gates.map shG).foldl stepW
      (stepW ((x2.gates.map shG).foldl stepW (List.ofFn y ++ [y 0 || y 6])) ⟨GateOp.or,[sh x4,6]⟩) := by
    rw [wires_fold]
    simp only [joined,List.foldl_cons,List.foldl_append,g0]
  have r2 := rel_fold x2.gates (rel_start y)
  rw [←wires_fold] at r2
  have six : ((x2.gates.map shG).foldl stepW (List.ofFn y ++ [y 0 || y 6])).getD 6 false = y 6 := by
    rw [fold_prefix _ _ _ (by simp)]
    simp [List.ofFn_succ]
  have ga : stepW ((x2.gates.map shG).foldl stepW (List.ofFn y ++ [y 0 || y 6])) ⟨GateOp.or,[sh x4,6]⟩ =
      (x2.gates.map shG).foldl stepW (List.ofFn y ++ [y 0 || y 6]) ++
        [(x2.wires (List.ofFn (pull y) ++ [pull y 1 || y 6])).getD x4 false || y 6] := by
    simp only [stepW,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,r2.2.2,six,id,Bool.or_false]
  rw [ga] at e
  have r3 := rel_fold x3.gates (rel_push r2 ((x2.wires (List.ofFn (pull y) ++ [pull y 1 || y 6])).getD x4 false || y 6))
  refine ⟨?_,?_⟩
  · have len : 9 < ((x2.gates.map shG).foldl stepW (List.ofFn y ++ [y 0 || y 6])).length := by
      have := r2.1; have := r2.2.1; omega
    rw [e,fold_prefix _ _ _ (by rw [List.length_append]; omega),getD_push,if_pos len,fold_prefix _ _ _ (by simp)]
    simp [List.ofFn_succ]
  · unfold Circuit.eval
    rw [e]
    exact r3.2.2 _
theorem joined_legal {x2 x3 : Circuit} {x4 : Nat} (h2 : PEqualNP.MetaComplexity.FanInTwo x2)
    (h3 : PEqualNP.MetaComplexity.FanInTwo x3) : PEqualNP.MetaComplexity.FanInTwo (joined x2 x3 x4) := by
  intro g hg
  simp only [joined,List.mem_cons,List.mem_append,List.mem_map] at hg
  rcases hg with rfl | ⟨a,ha,rfl⟩ | rfl | ⟨a,ha,rfl⟩
  · simp
  · exact ⟨(h2 a ha).1,by simpa [shG] using (h2 a ha).2⟩
  · simp
  · exact ⟨(h3 a ha).1,by simpa [shG] using (h3 a ha).2⟩
def small8 (x1 : Fin 8 → Bool) : Bool := x1 0 && x1 1 || x1 1 && x1 2 || x1 2 && x1 3 || x1 0 && x1 4 || x1 1 && x1 5 || x1 2 && x1 6 || x1 3 && x1 7 || x1 4 && x1 6 || x1 5 && x1 7 || x1 7 && x1 4
theorem match0 (y : Fin 9 → Bool) (h : y 6 = false) : small8 (pull y) = edge y := by
  simp only [small8,pull,edge,h]
  simp
  generalize y 0 = a0; generalize y 1 = a1; generalize y 2 = a2; generalize y 3 = a3
  generalize y 4 = a4; generalize y 5 = a5; generalize y 7 = a7; generalize y 8 = a8
  revert a0 a1 a2 a3 a4 a5 a7 a8
  decide +kernel
theorem match1 (y : Fin 9 → Bool) (h : y 6 = true) : (small8 (pull y) || pull y 0 || pull y 3) = edge y := by
  simp only [small8,pull,edge,h]
  simp
  generalize y 0 = a0; generalize y 1 = a1; generalize y 2 = a2; generalize y 3 = a3
  generalize y 4 = a4; generalize y 5 = a5; generalize y 7 = a7; generalize y 8 = a8
  revert a0 a1 a2 a3 a4 a5 a7 a8
  decide +kernel
theorem glue (bound : ∀ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = edge → 16 ≤ C.size)
    (x2 x3 : Circuit) (x4 : Nat) (h2 : PEqualNP.MetaComplexity.FanInTwo x2)
    (h3 : PEqualNP.MetaComplexity.FanInTwo x3) (hs : x2.size+x3.size ≤ 13)
    (h0 : ∀ x9 : Fin 8 → Bool, x3.eval (x2.wires (List.ofFn x9 ++ [x9 1 || false]) ++
      [(x2.wires (List.ofFn x9 ++ [x9 1 || false])).getD x4 false]) = small8 x9) :
    ∃ x10 : Fin 8 → Bool, x3.eval (x2.wires (List.ofFn x10 ++ [x10 1 || true]) ++ [true]) ≠
      (small8 x10 || x10 0 || x10 3) := by
  by_contra! h1
  have big := bound (joined x2 x3 x4) (joined_legal h2 h3) (fun y => (joined_value x2 x3 x4 y).1) (by
    funext y
    change (joined x2 x3 x4).eval (List.ofFn y) = _
    rw [(joined_value x2 x3 x4 y).2]
    cases h : y 6 with
    | false => rw [Bool.or_false (List.getD _ _ _),h0,match0 y h]
    | true => rw [Bool.or_true (List.getD _ _ _),h1,match1 y h])
  have sz : (joined x2 x3 x4).size = x2.size+x3.size+2 := by
    simp only [Circuit.size,joined,List.length_cons,List.length_append,List.length_map]; omega
  omega
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low511 : Lower (vars 511) (graphGoal 511) 15 :=
  lower_forest (g:=dead) (i:=0) (hints:=13438558465) (before_sound known383 valid383) geomdead tablesdead (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps511 : List (Nat × List Nat) := [(511,[])]
def known511 := extendKnown known383 15 maps511
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid511 : Known known511 := extendKnown_ok (m:=511) valid383 low511 (by decide +kernel)
def x31d6 (i : Nat) : Nat := 0x4321029908c02a029d6340fe00fd10fc20fa00
def x31l6 : Packing := (4,1,3,0,0,6,0,x31d6)
def x31h6 (i : Nat) : Nat := 0x300a0420400003e8661061400000000a0000000f12e4d81f1604918
def x31d5 (i : Nat) : Nat := 0x611844000000ca86543ca140bf2aa21f920442faa6885f54c20bea92217d51083e423007a88a00
def x31l5 : Packing := (8,2,3,0,0,6,0,x31d5)
def x31samples : Array (Bits × Bits) := #[(0xf17e2dd5acf7b3ffe5bfc6d3ad8fd9ae77df9c06df6f2e7ff2465fb547acecd4be963b7a737cb4ff66f4debefea7bd3e7d37cee3da7eb1fd4ef7ffa3bc393ef77ebf5333d97899d84cb7e721f3b67d9bf321f5df9e9e85f97b766cc36e047293,0x80400641c8f40044c11260082a009004c135481a686884140086c1225031072893190210d10ae050089453030c80142c21848a18e8b1801c04e3e040d085c00258c04207000320030a028154000410201401a02802321218e2c064d6a2412492),(0x827bf6ffa79ea4ce5dae3f753ba5eed8b75ccfdbdb4c22d12fd3adeaf5eff46e97bea49ad7ee4b37e1efaa62d368ae5de37c176efdbaadaabfdcef7ab6ff2768f7afdbd3ddefe99496dee85489efcf19e5b7cdfd4f8fb3dbc2ceb008aea2ce1f,0x1cbb61802203532802648921446a44802c0011009003000a0500009c20462014002200210280100891092034010d03c19c594000024c40614900138804003c880006a56028a8072805811e212002401d688e188101402c000d1383084c86c829),(0x8bb0dacd19efdd771b20bd8d5d7f7feede3b67bda6fafa9e3dbfaeda3d43bc557f49fed7befaf577979968fee5190b7d6ee5d1bcbb567fca33e35c5bce021c3c8171ced2771b9facf33d7e6fdedbf86799bf7ef35d897207f9ec955791228d7c,0x400854584824121818665013840b5813560a00404866106a01a4200589100ab4580910d52c0e00269484c0c01020344200af830510a40690534072bb214001b561180087129016720241508c48308200106242c2054323220c1ca703210754),(0x3ff109e2db67ee736ad6c8ff7f77ca9f4ee964e0ad90ff27392ec3faadfc2ffbe267e2c5aa5befe9beb36b9bf4fce881aeb9b97c1cc97ba5d7c9a1d661fff97064caae9faebdf677b1c67abf6f38eefccc5aa74f2c787ef5e4bd677c19d90960,0x800083aa84800380016100806062b001048101590220900010941a1a503203e543011200200011ab004312062e69840a3092003490e800b00124a000408800244088202210c0260180480c010120457d1da811002802341009416150bcd48880),(0x74cf15a242c1bb12bd7171a2e28f15b5ada77f56a92f57a8e410fe65ca3fd7fe2bab5fba04679eed3cd2bf1d2eeffdef9c7f7ce5f6cf30ddf0bebca539e7ddf708f4efbedbbee4cb4e639d96f4557e927e7d1026bc707d2b3f9ddaab41dd7080,0x5d886800130a0c1904801747958109303a48042490926ac9a60820c4a48c88122c26096b06150600c6002848110248918c28108100043f43aa08100f28720f1805119080e430d06c508460a09a9a228200004cd49500402410129a29412a5260),(0,0),(0,0),(0,0),(0,0)]
def x31columns : List ColumnInfo := [(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4),(2,0,29,0,4),(0,0,31,0,7)]
def x31autos : List (List Nat) := [[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]
def x31levels : Nat → Packing
  | 6 => x31l6
  | 5 => x31l5
  | _ => emptyPacking
def x31index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 3 19 3 11 3 4 x31h6
  | _ => fun _ => none
def x31 : Forest := ⟨31,6,fun j => x31samples[j]?.getD (0,0),x31columns,x31autos,x31levels,x31index⟩
set_option maxHeartbeats 0 in
theorem geomx31 : graphValid x31 (boundsBefore known511) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx31_6_0 : block x31 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx31_6_1 : block x31 6 1 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx31_6 : block x31 6 0 4=true := (@block_merge x31 6 0 1 3 sx31_6_0 sx31_6_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx31_5_0 : block x31 5 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx31_5_2 : block x31 5 2 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx31_5 : block x31 5 0 8=true := (@block_merge x31 5 0 2 6 sx31_5_0 sx31_5_2)
theorem tablesx31 : checkedTables x31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x31 0 0 0 = true)
  · exact (rfl : block x31 1 0 0 = true)
  · exact (rfl : block x31 2 0 0 = true)
  · exact (rfl : block x31 3 0 0 = true)
  · exact (rfl : block x31 4 0 0 = true)
  · exact allx31_5
  · exact allx31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem plx31 : Impossible (graphGoal 31) 6 (vars 31).toFinset := plainA (q:=31) (prior:=boundsBefore known511) (before_sound known511 valid511) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1567 : Lower (varsX 1567) (graphGoal 1567) 7 :=
  strong_full (q:=31) (rs:=[2, 1, 2, 4, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx31
    (index_root (g:=x31) (i:=1) rfl (before_sound known511 valid511) geomx31 tablesx31 (by decide +kernel))
def maps1567 : List (Nat × List Nat) := [(1567,[]),(2079,[50,65]),(6687,[50,33,16,64]),(1703,[115,67,100,83]),(4263,[114,33,97,82,50,65]),(7847,[115,50,98,83,66,16]),(12455,[113,97,82,32,65,48]),(12716,[49,129,115,67,32,97,80]),(17324,[129,50,114,48,66,97,80])]
def known1567 := extendKnown known511 7 maps1567
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1567 : Known known1567 := extendKnown_ok (m:=1567) valid511 low1567 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42527 : Lower (varsX 42527) (graphGoal 42527) 7 :=
  strong_full (q:=31) (rs:=[2, 1, 2, 4, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx31
    (index_root (g:=x31) (i:=2) rfl (before_sound known511 valid511) geomx31 tablesx31 (by decide +kernel))
def maps42527 : List (Nat × List Nat) := [(42527,[]),(44063,[50,65]),(47647,[50,33,16,64]),(52767,[33,32,65,48]),(57887,[16,64,49,32]),(42663,[115,67,100,83]),(44711,[114,33,97,82,50,65]),(47783,[114,98,83,33,16,64]),(54951,[113,97,82,32,65,48]),(68775,[113,16,96,81,49,64]),(44857,[130,114,98,81]),(53164,[130,50,116,49,32,97,80]),(55212,[49,129,115,67,32,97,80]),(60332,[129,50,114,48,66,97,80])]
def known42527 := extendKnown known1567 7 maps42527
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42527 : Known known42527 := extendKnown_ok (m:=42527) valid1567 low42527 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low83487 : Lower (varsX 83487) (graphGoal 83487) 7 :=
  strong_drop (q:=31) (hd:=inputs.getD 0 zero) (rs:=[0, 1, 2, 4, 1]) (u:=2) (v:=3) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx31
    (index_root (g:=x31) (i:=3) rfl (before_sound known511 valid511) geomx31 tablesx31 (by decide +kernel))
    (index_root (g:=x31) (i:=0) rfl (before_sound known511 valid511) geomx31 tablesx31 (by decide +kernel))
def maps83487 : List (Nat × List Nat) := [(83487,[]),(88607,[66,16]),(93727,[67,32]),(98847,[16,64,49,32]),(103967,[64,48,32,16]),(83623,[115,67,100,83]),(88743,[115,50,98,83,66,16]),(93863,[116,100,83,32]),(109223,[116,100,80,48,32,16]),(119463,[112,96,81,64,49,32]),(83769,[131,115,65,50,98,81]),(99150,[132,67,115,100,48,33,80]),(114510,[132,64,112,100,80]),(124750,[128,112,97,65,49,33,80]),(94124,[130,50,116,49,32,97,80]),(99244,[66,130,116,48,33,97,80]),(109484,[65,129,116,97,80]),(119724,[131,64,116,50,33,97,80])]
def known83487 := extendKnown known42527 7 maps83487
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid83487 : Known known83487 := extendKnown_ok (m:=83487) valid42527 low83487 (by decide +kernel)
def x187d6 (i : Nat) : Nat := 0x40440804242424384b03081007f803fa61fd10fd00778cfdc45f611
def x187l6 : Packing := (7,1,2,0,0,6,0,x187d6)
def x187h6 (i : Nat) : Nat := 0x2a000068
def x187d5 (i : Nat) : Nat := 0x101028f54c530bd58600
def x187l5 : Packing := (2,2,2,0,0,3,0,x187d5)
def x187samples : Array (Bits × Bits) := #[(0xbffc17f0fbe99ef9bb49f7b96b6d36b6759faf8bf6dbb4b847dfedd9b77f5e8fc77eefd9dfebf239dfedd2f72e3fefff5fd6cbade3d8ead5ff71fb756725ddfdd8dc8351d69d0faf99bbbb35d9ebef7f54fb96dda077b2b75534484cbf0ef27f,0x30000706000024200008514480240480414000281280001040890180010d1080050009541000080102401148a082810800400c340409005c00218400225000200020a0205510000101c0808b028022006082a80588150285108208402a00222a),(0xcc859ef33d9abc2cc888f69d372d90061c127fabde21daf3007c3ff26b547ea836468eea35afb6ab4c72377336f682bfd20bfd0a36e227b7e51778e9cf19962249112c6785c49616f18ecb58d6fa66ff3de408bbd16ef9c8203c11841fca4c4f,0xb002059fa7c1b865832ac03545120719ea15303a91a6c268d5608295e32ac013af114a2034336dcbd314635065124853e0e90403822c7831bc061f25c878dcd7e0d5c91aa2fbb0e54363a645052d482844051200148dd5aef3d518ed5cb4c45),(0,0),(0xd713fa0716869583df4bebe6b3daaf6f0a835b9ee42d9a750bd6f4b5cdd3cee3dae179822c6859d2365cefc5dbc2fc66f4231ae31c97e96250ce1598dd1b3b657f877bf9c6f3d575c66d8bddea0550172b63bf9ed6896509104b1e014cf38f8c,0x702086050c6b0521a1315172654404c6be07aa18c299229486bc4808ed21d6c0c05269790c2b000ec0242b2b1d294a0b7062006e020d258413163d818aad40460d7a04a458356d880fc1e381744c4095676284d609075b8f5ca61e0b4ca38b0c),(0xef76ad6447a6b55a8d51ef86469fbd8f7713169432289bc87fbf66740c7384b2fbb3fb22ba394fcea99cfb82b7e9df9ebafd588efc4e5ffe168f6ebee9feabcff7331de10bfadb24ffdcd48c79c6df2cef524f5a5bb96d65255be00960fd0ff0,0x5cc30686084da8c58442600108a82080020004601644960304232101000082f208990002350c0d0258b8490001404d00398520110a2ca02c000403e00000b9970851019a04880660030081488000122800c500810482470a359e004905c04d0),(0xb10bd71f927f6a857bfeda67bd6ad2f5daeec167ebdee7ffbbe2babfdba86775eacbcd3f7054eeff5efbc7eece5e6cf205df2ffbcb739e7c5c708f4edbcdfb764cfce63f796b65dde927e6f3065b4784d2aff9347d8d8a5afa80bff280fef000,0xc45c686814918194cb6782820203896632ba62840c12208c0120c868ca90ed7e4045f002879010602c1044100c040012c4a0e0801050402220803025008a40d01a40185f226400c82800201005091184860d413a2000205a0305852a10ffd000),(0,0),(0x2921db1b8cfd66766ef74177dedf7661ec62c6f9ef864d87f576f60eebd9277c667b593681d6c6adb276d6796e7136ef087d2e783131573bc7df2d9abbf1f19a19686d8ee9e571ffb90047fe0e7dd1abc95f6ce01fdb9969aad8bff32f000000,0x39810793616a7c6314806c10c1582001cd00090320c95a418a030781342e00003a28041140252704c3488b81e3581b41381b051b05a69710d14d4b180a24372f049520004d19bb2353e1d087c862e0415150a404461647a5ecfa7ad5ef000000),(0,0)]
def x187columns : List ColumnInfo := [(10,0,177,0,4),(16,8,163,0,4),(160,0,27,0,4)]
def x187autos : List (List Nat) := [[],[115,84]]
def x187levels : Nat → Packing
  | 6 => x187l6
  | 5 => x187l5
  | _ => emptyPacking
def x187index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 5 1 6 1 1 x187h6
  | _ => fun _ => none
def x187 : Forest := ⟨187,6,fun j => x187samples[j]?.getD (0,0),x187columns,x187autos,x187levels,x187index⟩
set_option maxHeartbeats 0 in
theorem geomx187 : graphValid x187 (boundsBefore known83487) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx187_6_0 : block x187 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx187_6_4 : block x187 6 4 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx187_6 : block x187 6 0 7=true := (@block_merge x187 6 0 4 3 sx187_6_0 sx187_6_4)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx187_5_0 : block x187 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx187_5 : block x187 5 0 2=true := sx187_5_0
theorem tablesx187 : checkedTables x187 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x187 0 0 0 = true)
  · exact (rfl : block x187 1 0 0 = true)
  · exact (rfl : block x187 2 0 0 = true)
  · exact (rfl : block x187 3 0 0 = true)
  · exact (rfl : block x187 4 0 0 = true)
  · exact allx187_5
  · exact allx187_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem plx187 : Impossible (graphGoal 187) 6 (vars 187).toFinset := plainA (q:=187) (prior:=boundsBefore known83487) (before_sound known83487 valid83487) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42683 : Lower (varsX 42683) (graphGoal 42683) 7 :=
  strong_full (q:=187) (rs:=[2, 1, 16, 1, 1, 32]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx187
    (index_root (g:=x187) (i:=4) rfl (before_sound known83487 valid83487) geomx187 tablesx187 (by decide +kernel))
def maps42683 : List (Nat × List Nat) := [(42683,[]),(47806,[117,67,32])]
def known42683 := extendKnown known83487 7 maps42683
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42683 : Known known42683 := extendKnown_ok (m:=42683) valid83487 low42683 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low44219 : Lower (varsX 44219) (graphGoal 44219) 7 :=
  strong_full (q:=187) (rs:=[16, 1, 16, 1, 1, 32]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx187
    (index_root (g:=x187) (i:=5) rfl (before_sound known83487 valid83487) geomx187 tablesx187 (by decide +kernel))
def maps44219 : List (Nat × List Nat) := [(44219,[]),(44731,[84,115]),(52926,[117,67,32]),(54974,[116,83,32]),(48071,[115,83,133,99,50,66,16])]
def known44219 := extendKnown known42683 7 maps44219
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid44219 : Known known44219 := extendKnown_ok (m:=44219) valid42683 low44219 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low88763 : Lower (varsX 88763) (graphGoal 88763) 7 :=
  strong_drop (q:=187) (hd:=inputs.getD 1 zero) (rs:=[2, 0, 16, 1, 1, 32]) (u:=1) (v:=3) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx187
    (cut_root (prior:=boundsBefore known83487) (before_sound known83487 valid83487) (2,0,185,0,5) (by decide +kernel) (by decide +kernel))
    (index_root (g:=x187) (i:=0) rfl (before_sound known83487 valid83487) geomx187 tablesx187 (by decide +kernel))
def maps88763 : List (Nat × List Nat) := [(88763,[]),(88766,[117,67,32]),(83911,[115,83,133,99,50,66,16])]
def known88763 := extendKnown known44219 7 maps88763
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid88763 : Known known88763 := extendKnown_ok (m:=88763) valid44219 low88763 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low99003 : Lower (varsX 99003) (graphGoal 99003) 7 :=
  strong_drop (q:=187) (hd:=inputs.getD 3 zero) (rs:=[2, 1, 0, 1, 1, 32]) (u:=16) (v:=24) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx187
    (cut_root (prior:=boundsBefore known83487) (before_sound known83487 valid83487) (0,8,163,16,5) (by decide +kernel) (by decide +kernel))
    (index_root (g:=x187) (i:=1) rfl (before_sound known83487 valid83487) geomx187 tablesx187 (by decide +kernel))
def maps99003 : List (Nat × List Nat) := [(99003,[]),(119483,[84,115]),(104126,[117,67,32]),(109246,[116,83,32]),(119751,[115,83,133,99,50,66,16])]
def known99003 := extendKnown known88763 7 maps99003
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid99003 : Known known99003 := extendKnown_ok (m:=99003) valid88763 low99003 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low104123 : Lower (varsX 104123) (graphGoal 104123) 7 :=
  strong_drop (q:=187) (hd:=inputs.getD 4 zero) (rs:=[2, 1, 16, 0, 1, 32]) (u:=1) (v:=17) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx187
    (cut_root (prior:=boundsBefore known83487) (before_sound known83487 valid83487) (24,0,163,0,4) (by decide +kernel) (by decide +kernel))
    (index_root (g:=x187) (i:=2) rfl (before_sound known83487 valid83487) geomx187 tablesx187 (by decide +kernel))
def maps104123 : List (Nat × List Nat) := [(104123,[]),(109243,[84,115]),(99006,[117,67,32]),(119486,[116,83,32]),(94151,[115,83,133,99,50,66,16])]
def known104123 := extendKnown known99003 7 maps104123
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid104123 : Known known104123 := extendKnown_ok (m:=104123) valid99003 low104123 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low83643 : Lower (varsX 83643) (graphGoal 83643) 7 :=
  strong_drop (q:=187) (hd:=inputs.getD 0 zero) (rs:=[0, 1, 16, 1, 1, 32]) (u:=2) (v:=3) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx187
    (index_root (g:=x187) (i:=6) rfl (before_sound known83487 valid83487) geomx187 tablesx187 (by decide +kernel))
    (index_root (g:=x187) (i:=3) rfl (before_sound known83487 valid83487) geomx187 tablesx187 (by decide +kernel))
def maps83643 : List (Nat × List Nat) := [(83643,[]),(93886,[117,67,32]),(89031,[115,83,133,99,50,66,16])]
def known83643 := extendKnown known104123 7 maps83643
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid83643 : Known known83643 := extendKnown_ok (m:=83643) valid104123 low83643 (by decide +kernel)
def x63d7 (i : Nat) : Nat := 0x3a04840ac3f865fc10
def x63l7 : Packing := (2,1,2,0,0,4,0,x63d7)
def x63h7 (i : Nat) : Nat := 0x1520079d85d46b7171000680020c0000f391436008009b010
def x63d6 (i : Nat) : Nat := 0x101087cc4000804bc46202f211880840401ffdb4e4b74a0b44658480fb48032fd4c410bf58032bf58c10bf590109f59432be580329f59410bd58432bb58810af59010b758c10
def x63l6 : Packing := (12,2,2,0,0,7,0,x63d6)
def x63h6 (i : Nat) : Nat := 0x24f9400060ba8030352
def x63d5 (i : Nat) : Nat := 0x108421104210872a1e50a03e498240196e52058432cea62b2821b54c1610cb5a98ac8086e53158810
def x63l5 : Packing := (6,3,2,0,0,6,0,x63d5)
def x63h5 (i : Nat) : Nat := 0x20034000
def x63d4 (i : Nat) : Nat := 0x3b04813058432
def x63l4 : Packing := (1,4,2,0,0,0,0,x63d4)
def x63samples : Array (Bits × Bits) := #[(0xad6cf48cefeeb366bfc468999fd96bae1fbdeec0977aac7fbfcbeefb28d7d852b5bbbfb4b6aab7fcfcfe5f9edf07f96da6bd9f9eef3f2dcf3ffd96271b7686bd5dcf3d6b7e75af15fa3d7e9cea759eefbcb7dd91dcefb70e703d01cd3e217673,0x210090020094000a005082040012104040504021812104004002a08110000a002000010808200300000090156a0430090000100000020028000000012040030000802200044010080204500000c80000004008440b217a841020024212652),(0xead31e9bfaeed4bdefd2d6f675727155041569a6474dff0ab7fff33a3a7659ea2f661cfc6e337ffeffbfbca9b1ee5d36ef81ade956b4b6ef205fcb6aa4826eaeaf566fef7b68e6f21aea0bf7dd89b0b7e683c34ef9da8a8808dd14a2c8c6c87f,0xc1986004a83302aa31f32935cbb32c88829a0832ce7688020906784742019671108e26c082854c080b8a0d0000808bc2842e108a02846c32846716daf2c288ac45331f148100a28d30b8aa8455b10488a5810422aa105a801ae24a688c4c829),(0x17b5fa17971655db771bd77effa7862210ca1f4e6e9bdb2cdea0ad249d2fffaffb49ca8eeae56ad3eb6979743cfd20703f567e8d90e296ab9158cb46e699795aa690eef2a79ff3edff59cdea97d1d3b2d35c78ff25ee08b0cac0f132f1070f9c,0x3144418c814040d1484081088104c9302292403840080460036d08428886420828e504819001881d2000492200204701530c16440415303810908810109312513988020c0100e0052c840140980462811082c2881542b8505c11d31871030514),(0xff2edff42d9bdc0259bb87fcc6c4f679eac35ebfec9f58e8fc353d9dd73be64dd61fd7f7397f2a81d2f2ecef60387ecffa47ea6c6a54c037e60a6ffdf2bb75677570e875849fddca55c6de07b6ceef0bf1cbb7a226fd407d8702ee3101f88fe0,0xb212615c2aa00c9487041410022404080829c7847210037810e22841410c90440820406c4410220263a044261ea00080728009f048c1c08e0a61014008840284540083a45d02600161049105b01958c2083154c018462fa364002300b08ae0),(0x4963d3f385a53a226aee73bbcb557dfbe95e6277bc3ff4f88d3c1af8f7ffa11bbbef73fb63b0fd7668aa80a3cbfddebe7655c671c203ff7cc7623ab8db2fb0d2d9b20185d9be496fe897f41d54fe2f5b9c5ff2288bff69c345228fc801fff000,0x780c4c9622444092680842830520189821b250387105a988046910412020106b090112ab833024d4c9841d8098a014906b0c48560207280f70640a24a86468cd4a01227443a0980eba04820a0a07c22138d680a9120009c0549afdcc014e5000),(0xcfd8fb590010af70f723ee571e7d962d9a33c41ad70d0f5749b3af5b24b766d773bda176db8999c23c4d377c9c9e0a41b4ea3e1befafab5c7ddb84f3b160faa55a1dd2518025f8f65bfcf64c7e97360f1c391f3fd3a15ccc32008df5fe008000,0xf04842e69c4934342200f875d905081a40b9e099644009adb2310614b0c8eb3e052d2ad86e2c001144f27ce620084c385a61dadac0735fd40002bcc0da48cb1747a412e5478eb3f4e6661a0acd07a078de2f62794a394de817befdffda008000),(0,0),(0,0),(0,0)]
def x63columns : List ColumnInfo := [(1,32,30,0,4),(6,0,57,0,4),(24,0,39,0,4),(32,0,31,0,7)]
def x63autos : List (List Nat) := [[],[65,50]]
def x63levels : Nat → Packing
  | 7 => x63l7
  | 6 => x63l6
  | 5 => x63l5
  | 4 => x63l4
  | _ => emptyPacking
def x63index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 7 21 2 9 4 1 x63h7
  | 6 => lookupWord 2 9 1 8 3 1 x63h6
  | 5 => lookupWord 1 5 1 6 1 1 x63h5
  | _ => fun _ => none
def x63 : Forest := ⟨63,7,fun j => x63samples[j]?.getD (0,0),x63columns,x63autos,x63levels,x63index⟩
set_option maxHeartbeats 0 in
theorem geomx63 : graphValid x63 (boundsBefore known83643) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx63_7_0 : block x63 7 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx63_7 : block x63 7 0 2=true := sx63_7_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx63_6_0 : block x63 6 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx63_6_7 : block x63 6 7 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx63_6 : block x63 6 0 12=true := (@block_merge x63 6 0 7 5 sx63_6_0 sx63_6_7)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx63_5_0 : block x63 5 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx63_5 : block x63 5 0 6=true := sx63_5_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx63_4_0 : block x63 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx63_4 : block x63 4 0 1=true := sx63_4_0
theorem tablesx63 : checkedTables x63 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x63 0 0 0 = true)
  · exact (rfl : block x63 1 0 0 = true)
  · exact (rfl : block x63 2 0 0 = true)
  · exact (rfl : block x63 3 0 0 = true)
  · exact allx63_4
  · exact allx63_5
  · exact allx63_6
  · exact allx63_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem plx63 : Impossible (graphGoal 63) 7 (vars 63).toFinset := plainA (q:=63) (prior:=boundsBefore known83643) (before_sound known83643 valid83643) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1087 : Lower (varsX 1087) (graphGoal 1087) 8 :=
  strong_full (q:=63) (rs:=[16, 4, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx63
    (index_root (g:=x63) (i:=0) rfl (before_sound known83643 valid83643) geomx63 tablesx63 (by decide +kernel))
def maps1087 : List (Nat × List Nat) := [(2623,[50,65]),(1119,[101,66,16]),(6303,[117,101,67,32]),(11423,[117,101,33,32,65,48]),(6319,[116,100,83,32]),(13487,[113,97,82,32,65,48]),(1207,[115,84,99]),(3255,[114,81,98,50,65]),(11694,[130,116,49,32,81,96]),(11708,[132,67,84,48,33,113,96])]
def known1087 := extendKnown known83643 8 maps1087
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1087 : Known known1087 := extendKnown_ok (m:=1087) valid83643 low1087 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low11327 : Lower (varsX 11327) (graphGoal 11327) 8 :=
  strong_full (q:=63) (rs:=[2, 1, 2, 16, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx63
    (index_root (g:=x63) (i:=1) rfl (before_sound known83643 valid83643) geomx63 tablesx63 (by decide +kernel))
def maps11327 : List (Nat × List Nat) := [(2719,[117,101,67,32]),(3247,[116,100,83,32]),(13495,[115,84,99])]
def known11327 := extendKnown known1087 8 maps11327
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid11327 : Known known11327 := extendKnown_ok (m:=11327) valid1087 low11327 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1599 : Lower (varsX 1599) (graphGoal 1599) 8 :=
  strong_full (q:=63) (rs:=[2, 1, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx63
    (cut_root (prior:=boundsBefore known83643) (before_sound known83643 valid83643) (32,0,1567,0,7) (by decide +kernel) (by decide +kernel))
def maps1599 : List (Nat × List Nat) := [(1719,[115,84,99])]
def known1599 := extendKnown known11327 8 maps1599
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1599 : Known known1599 := extendKnown_ok (m:=1599) valid11327 low1599 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47679 : Lower (varsX 47679) (graphGoal 47679) 8 :=
  strong_full (q:=63) (rs:=[2, 4, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx63
    (cut_root (prior:=boundsBefore known83643) (before_sound known83643 valid83643) (32,0,47647,0,7) (by decide +kernel) (by decide +kernel))
def maps47679 : List (Nat × List Nat) := [(42671,[116,100,83,32]),(68783,[113,97,82,32,65,48]),(47799,[115,84,99]),(68791,[114,81,98,50,65])]
def known47679 := extendKnown known1599 8 maps47679
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47679 : Known known47679 := extendKnown_ok (m:=47679) valid1599 low47679 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42559 : Lower (varsX 42559) (graphGoal 42559) 8 :=
  strong_full (q:=63) (rs:=[2, 1, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx63
    (cut_root (prior:=boundsBefore known83643) (before_sound known83643 valid83643) (32,0,42527,0,7) (by decide +kernel) (by decide +kernel))
def maps42559 : List (Nat × List Nat) := [(47791,[116,100,83,32]),(54959,[113,97,82,32,65,48]),(42679,[115,84,99]),(44727,[114,81,98,50,65])]
def known42559 := extendKnown known47679 8 maps42559
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42559 : Known known42559 := extendKnown_ok (m:=42559) valid47679 low42559 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low52799 : Lower (varsX 52799) (graphGoal 52799) 8 :=
  strong_full (q:=63) (rs:=[2, 1, 8, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx63
    (cut_root (prior:=boundsBefore known83643) (before_sound known83643 valid83643) (32,0,52767,0,7) (by decide +kernel) (by decide +kernel))
def maps52799 : List (Nat × List Nat) := [(44719,[116,100,83,32]),(54967,[115,84,99])]
def known52799 := extendKnown known42559 8 maps52799
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid52799 : Known known52799 := extendKnown_ok (m:=52799) valid42559 low52799 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low88639 : Lower (varsX 88639) (graphGoal 88639) 8 :=
  strong_drop (q:=63) (hd:=inputs.getD 1 zero) (rs:=[2, 0, 2, 4, 1, 1]) (u:=1) (v:=3) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx63
    (cut_root (prior:=boundsBefore known83643) (before_sound known83643 valid83643) (32,0,88607,0,7) (by decide +kernel) (by decide +kernel))
    (cut_root (prior:=boundsBefore known83643) (before_sound known83643 valid83643) (32,0,88607,0,7) (by decide +kernel) (by decide +kernel))
def maps88639 : List (Nat × List Nat) := [(88751,[116,100,83,32]),(119471,[113,97,82,32,65,48]),(88759,[115,84,99]),(109239,[114,81,98,50,65])]
def known88639 := extendKnown known52799 8 maps88639
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid88639 : Known known88639 := extendKnown_ok (m:=88639) valid52799 low88639 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low93759 : Lower (varsX 93759) (graphGoal 93759) 8 :=
  strong_drop (q:=63) (hd:=inputs.getD 2 zero) (rs:=[2, 1, 0, 4, 1, 1]) (u:=2) (v:=6) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx63
    (cut_root (prior:=boundsBefore known83643) (before_sound known83643 valid83643) (32,0,93727,0,7) (by decide +kernel) (by decide +kernel))
    (cut_root (prior:=boundsBefore known83643) (before_sound known83643 valid83643) (32,0,93727,0,7) (by decide +kernel) (by decide +kernel))
def maps93759 : List (Nat × List Nat) := [(83631,[116,100,83,32]),(109231,[113,97,82,32,65,48]),(93879,[115,84,99]),(119479,[114,81,98,50,65])]
def known93759 := extendKnown known88639 8 maps93759
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid93759 : Known known93759 := extendKnown_ok (m:=93759) valid88639 low93759 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low83519 : Lower (varsX 83519) (graphGoal 83519) 8 :=
  strong_drop (q:=63) (hd:=inputs.getD 0 zero) (rs:=[0, 1, 2, 4, 1, 1]) (u:=2) (v:=3) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx63
    (cut_root (prior:=boundsBefore known83643) (before_sound known83643 valid83643) (32,0,83487,0,7) (by decide +kernel) (by decide +kernel))
    (cut_root (prior:=boundsBefore known83643) (before_sound known83643 valid83643) (32,0,83487,0,7) (by decide +kernel) (by decide +kernel))
def maps83519 : List (Nat × List Nat) := [(93871,[116,100,83,32]),(83639,[115,84,99]),(94158,[83,133,115,67,32,96])]
def known83519 := extendKnown known93759 8 maps83519
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid83519 : Known known83519 := extendKnown_ok (m:=83519) valid93759 low83519 (by decide +kernel)
def x189d7 (i : Nat) : Nat := 0x1880d0260231012190108406a02b5460333c3407f803fa61fd10fe187f043f841fa00
def x189l7 : Packing := (7,1,3,0,0,7,0,x189d7)
def x189h7 (i : Nat) : Nat := 0x581f03838f3cd8080000031c538000382fbe3054bd15580038dc1581da06000000414000486e0c4811858000890041099821030806bbf048085221009201600000058
def x189d6 (i : Nat) : Nat := 0x8421000210800000004082d508d05bad508cf19283c280bf99910fe48130bf58910bf58430fe54030fe48110bf58930bf59420fc846009f59420f68ce00fa88a00bb58830bd58430
def x189l6 : Packing := (14,2,3,0,0,7,0,x189d6)
def x189h6 (i : Nat) : Nat := 0x700009040000000000ddd0800002
def x189d5 (i : Nat) : Nat := 0x104208141ba541620c36698ac4186f15058430
def x189l5 : Packing := (3,3,3,0,0,5,0,x189d5)
def x189samples : Array (Bits × Bits) := #[(0xcdea8b576bc32cb8da56a736d32badddf5df04eea7b64efcafec7dadde7b0fceffabfc4e43c67ad17f263aadb5b516e908d95c8c33e7cc9ee88dfcd128bfbb9bf3e7bd865fa767ed5aac216c7a63f05c21bf71d8d6bca8e401f103257832f474,0x492c1b0dd3663000030e020230604094280504000042041a2018311e3212c1121f000217ea404e11e00401501094c36a00c85104c10800c00aa01040f00250101a824118014441c40040c129f92e1c901608a8580b00b0a100dc4b38d802a424),(0,0),(0xd3f7b87ebfabdfaf65653a819edf5e416cb74f4b4ec8e16243f99ef58c50da4b862f57faeeac51eacbedffae64d4c9b4e047ca76eeadfc4af3a453876f7edbab05776f20d7d05072f523657c73551fe7ba9705dc35f35183c00eba035f29c84f,0x80804012405db20024208704300441210a0897926402a8440098a11c00808e3803100860154870a0222604766088499008412c140212340309868809000200400070203a40711910c2438150600802838411690814019a293409a191428c84a),(0xf3fb994b17ae18b5dc3f25d8a7ecda697eadbffc9fdfb65594405389fce7e1bb82da51e3375dfd3eeff7e33fd8f7fdc2f766f97658fcc335bff4cc7afff295f769f9649cf49f1fea6993db63df5c0b2919f5fee35dd3671202074e3041cf0f87,0x362b34530004114494c20410931888280320040901141a21e2648a3222d3101c84e1514e0840a404c41180002600202900052c3f80c0af8b009145063918334ca041880040c20c40c2418859ec0d03472021441e2ae450088f6420e0830685),(0x28396853586e2269a38a9ca9a6ba033392ad2cecbcb7f1efb2b85fefb1df25d87938e647d56d96df3229c0744d3e365f0d3db794b236e37d981da6ff50750c9e4619fbf46467bf1b4fdddbcfdcfb60dc5dedfe8bef6f879ca370503220f40f70,0x16c10442041140ae986115f00b08a4231178d1cbb414034010010021c14504cc0033082000950102182a4e0fe2091c941401084200670200045f4a0a0044818880093e666030082188010854001160680084148160d40b0ef720900701740950),(0x97e5efe723bd7ff138f5d776c324b3cefdd299d68f078ebb5def6173ff30bd6c91e7aab7551ffa02bf5373e9da99c771f2a8670957fb1d827c6e7c74deb5a45cfa9c3afb3bb890b45b7855c19a9fab96e548577af41f29683c8315cd80faf088,0x844304d02808848e00e0246c450a040a54a009d50610090498230240c1c908e020330408001d80060688308e2f2004004500a6c32e70372814532882008c240b84202247601b84200d0408100400a00100501720c00809523b03b08120f95088),(0,0),(0x560f75fce45cf36aa9c85bf17b7574cf1d71f737ca9e1f5b6fff8956f9707bfbac7777dcb8b3d6a9383d5d47fae82e3d52c62fa9c44fb4e465e25b44a22f4fe39e9f4ae9404ff23287ec26fa66d1bdaac673a97d250a760dfc18b5eade000088,0x6394012643b020011c1111002814b861285f4202990d0060201434aa2822121c4d08e34158804031a0048710808462262a394004110e0083c00090556953d100400009b81ba0604c004043a8d0cf445603a840481095e60d44bc4566cb040000),(0,0)]
def x189columns : List ColumnInfo := [(33,0,156,0,4),(24,0,165,0,4),(12,0,177,0,4),(132,0,57,0,4),(17,0,172,0,4),(0,0,189,0,8)]
def x189autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]
def x189levels : Nat → Packing
  | 7 => x189l7
  | 6 => x189l6
  | 5 => x189l5
  | _ => emptyPacking
def x189index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 29 37 3 12 4 4 x189h7
  | 6 => lookupWord 2 11 1 10 2 4 x189h6
  | _ => fun _ => none
def x189 : Forest := ⟨189,7,fun j => x189samples[j]?.getD (0,0),x189columns,x189autos,x189levels,x189index⟩
set_option maxHeartbeats 0 in
theorem geomx189 : graphValid x189 (boundsBefore known83519) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx189_7_0 : block x189 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx189_7_1 : block x189 7 1 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx189_7 : block x189 7 0 7=true := (@block_merge x189 7 0 1 6 sx189_7_0 sx189_7_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx189_6_0 : block x189 6 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx189_6_6 : block x189 6 6 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx189_6 : block x189 6 0 14=true := (@block_merge x189 6 0 6 8 sx189_6_0 sx189_6_6)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx189_5_0 : block x189 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx189_5 : block x189 5 0 3=true := sx189_5_0
theorem tablesx189 : checkedTables x189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x189 0 0 0 = true)
  · exact (rfl : block x189 1 0 0 = true)
  · exact (rfl : block x189 2 0 0 = true)
  · exact (rfl : block x189 3 0 0 = true)
  · exact (rfl : block x189 4 0 0 = true)
  · exact allx189_5
  · exact allx189_6
  · exact allx189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem plx189 : Impossible (graphGoal 189) 7 (vars 189).toFinset := plainA (q:=189) (prior:=boundsBefore known83519) (before_sound known83519 valid83519) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2237 : Lower (varsX 2237) (graphGoal 2237) 8 :=
  strong_full (q:=189) (rs:=[16, 8, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx189
    (index_root (g:=x189) (i:=1) rfl (before_sound known83519 valid83519) geomx189 tablesx189 (by decide +kernel))
def maps2237 : List (Nat × List Nat) := [(2237,[]),(12477,[116,83,32]),(18109,[82,48,66,112])]
def known2237 := extendKnown known83519 8 maps2237
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2237 : Known known2237 := extendKnown_ok (m:=2237) valid83519 low2237 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1725 : Lower (varsX 1725) (graphGoal 1725) 8 :=
  strong_full (q:=189) (rs:=[16, 8, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx189
    (index_root (g:=x189) (i:=2) rfl (before_sound known83519 valid83519) geomx189 tablesx189 (by decide +kernel))
def maps1725 : List (Nat × List Nat) := [(1725,[]),(17085,[82,48])]
def known1725 := extendKnown known2237 8 maps1725
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1725 : Known known1725 := extendKnown_ok (m:=1725) valid2237 low1725 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2749 : Lower (varsX 2749) (graphGoal 2749) 8 :=
  strong_full (q:=189) (rs:=[32, 8, 4, 8, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx189
    (index_root (g:=x189) (i:=3) rfl (before_sound known83519 valid83519) geomx189 tablesx189 (by decide +kernel))
def maps2749 : List (Nat × List Nat) := [(2749,[]),(3261,[84,115]),(11453,[117,67,32])]
def known2749 := extendKnown known1725 8 maps2749
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2749 : Known known2749 := extendKnown_ok (m:=2749) valid1725 low2749 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low43197 : Lower (varsX 43197) (graphGoal 43197) 8 :=
  strong_full (q:=189) (rs:=[20, 9, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx189
    (index_root (g:=x189) (i:=4) rfl (before_sound known83519 valid83519) geomx189 tablesx189 (by decide +kernel))
def maps43197 : List (Nat × List Nat) := [(43197,[]),(58557,[82,48]),(64189,[83,114,64]),(46427,[130,50,98,82,115,33,65]),(48475,[135,101,50,33,16,64]),(63835,[135,98,82,33,49,64]),(49638,[115,83,82,130,99,66,16]),(55782,[117,130,99,32,64,16])]
def known43197 := extendKnown known2749 8 maps43197
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid43197 : Known known43197 := extendKnown_ok (m:=43197) valid2749 low43197 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low44221 : Lower (varsX 44221) (graphGoal 44221) 8 :=
  strong_full (q:=189) (rs:=[16, 8, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx189
    (index_root (g:=x189) (i:=5) rfl (before_sound known83519 valid83519) geomx189 tablesx189 (by decide +kernel))
def maps44221 : List (Nat × List Nat) := [(44221,[]),(44733,[84,115]),(52925,[117,67,32]),(54973,[116,83,32]),(58045,[82,48]),(68797,[116,50,80]),(42843,[130,50,98,82,115,33,65]),(50011,[131,67,99,116,50,33,16,80]),(58203,[133,117,101,33,48]),(60251,[132,67,100,84,48,33,112]),(50150,[67,132,99,82,16]),(55270,[66,114,50,132,99,32,80,16]),(69094,[84,117,80,132,96,48,32,16])]
def known44221 := extendKnown known43197 8 maps44221
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid44221 : Known known44221 := extendKnown_ok (m:=44221) valid43197 low44221 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low83645 : Lower (varsX 83645) (graphGoal 83645) 8 :=
  strong_drop (q:=189) (hd:=inputs.getD 0 zero) (rs:=[0, 8, 4, 1, 1, 4]) (u:=16) (v:=17) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx189
    (index_root (g:=x189) (i:=6) rfl (before_sound known83519 valid83519) geomx189 tablesx189 (by decide +kernel))
    (index_root (g:=x189) (i:=0) rfl (before_sound known83519 valid83519) geomx189 tablesx189 (by decide +kernel))
def maps83645 : List (Nat × List Nat) := [(83645,[]),(93885,[117,67,32]),(99005,[82,48]),(104125,[83,114,64]),(109245,[80,48,50,114,64]),(119485,[66,112,82,48]),(83803,[130,50,98,82,115,33,65]),(88923,[135,101,50,33,16,64]),(99163,[133,117,101,33,48]),(104283,[135,98,82,33,49,64]),(124763,[128,64,96,116,80,16,49,32]),(109542,[84,117,80,132,96,48,32,16]),(114662,[82,32,117,128,98,50,64,16]),(119782,[112,32,130,96,66,48,16])]
def known83645 := extendKnown known44221 8 maps83645
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid83645 : Known known83645 := extendKnown_ok (m:=83645) valid44221 low83645 (by decide +kernel)
def x251d7 (i : Nat) : Nat := 0x60bfd31
def x251l7 : Packing := (1,1,1,0,0,0,0,x251d7)
def x251samples : Array (Bits × Bits) := #[(0x6f9a1f9cf47fecb79eeafdf7e35afad9bd95adcf6f752b967f8be6c93760ba11abfa6667e4df8e60f03dd3a65fefdb981d9a5ff9ad3f9639cc61ec7a0febf2b2cbfebe9bcbcf67f14f7ffddd3c340021ee01fffe490e402109fc2670e40ff27f,0x6128200080811121081068a8442a900c0a236894812cb4101814101c408080a800265c509190081100819408088305b2734948020108000321380280102404802a080fe80c006808018b040d1944208080808080490a402108a80450a401222a),(0xf78e13fbeb3d07d6aef5ac2d287bf226e678f815ef1fea626336fd0d1144f1084cfc68436abfd6e23fdaf741fb7be2eed2d45798bb339117477d23c9c29fdd0bc0e8db5953dcf9b96f4c3efdb1f2488e110001fe0033fcc6313cd9833fca4c4f,0x9e0402182a2aa40403020102389428f17008000810000125878020a39d0c301520008009680006aac4602040032ca00d801084780804e484d4063422c3120a4a113320158201010560603202021356067666666600212cc63114910212ca4c45),(0,0),(0x6ea5bce187811b2df864f3c4bfb18fcf33f5a7685cdcd24bd44f71bd499f4165222bd7d1f0eff07f48533c71e05e0d24e9ecc71423bbe9f4affa3b7fe25add40e35a9eab6afbdf72ecc2c2daf74a001000fe000071c380f83e331e1c38f38f8c,0x26f30f1729502a8322b9d01ac548f10c6d4a0948c12b8b100c1440444a30059c18a7353292872c434f018e44882ce1d557dc466b9510221224240b0209380998b83066f43438eb8e00806486015066caaaaaaaaa718380f82c321e1838a38b0c),(0x18e2eeaebfd47f397687fd07ca6ebc9e1a305e6b9e8dd07119cf0bfede9a3a15423b9bb6f6c16c32870dfeb7bc468fd6c5aae6d585ac6ed5a75f7f96ae4d51d87ba0b716f2addaae3cb3cbf66a2a001000fffe0181fc0f003fc3e01fc0fc0ff0,0x80048020060a8454104607003a04062190041422189000c96169a9a004036801a248008d6c20d0ac207e010202001008082020104281548c8ac0d0112002826304811003c2421401ac048240268199355555555580740f001341e007405c04d0),(0xaef7fde33d6b8e975fff96d3178e11dfd9cfc5cd8d7d47ffe61d4ca6b563eff7f7441c5c4b014bef473da3899b9e19ef2b55ae66c35c87afdfa482fc7f623f6474ff85ed1f1206fed54e38b4eccdb761ee000001fe000fffc003ffe000fff000,0x800061a423006804302121000952ad01000904a241040e8a0600200843b25109040020c4221228a2f1420128400c00c048400800a120d40da002c5028d06a0301000004c3649696a850e2008601036e0f1e1e1f24000a948003fba000fed000),(0x9fa60102696b13560cddde9c4b2bf5e3e1d4fcf18d7f91673030ffe5b5365c4eefc07c71376512523bfbf7d45b53aefe7620ef927235ed48dc0ccf4757b59c8f3393df0e509dd1bf9d7119b74df0488e11000001fffff0000003ffffff000000,0x21616d0515d108eb1c9046a90123460a0e81b4860abc7c90100a0410603280000fa06c74860d3940098e0239d0c206b070466b80f4da02510198029d182815b44e08cde831b4beb286104560f188a9f989999999ffded00000036efded000000),(0xd8f5d8c31445e44475434bf75ebec1e914cb8a59ec8027dbf6919576926d75ef3217e17a6d58fd9fdf7d50ceb89ccb2b3ec5fbb746e76dfb52b813b1be80f924fcf3917d176e54e79e835ca1b003b74000000001fffffffffffc000000000000,0x214521e401c21802a805e90fc202040ac33e04219a2733144316297e1800424a2b0bfcc1251cc80150c85b8962731ca1ca3ac75ed529803f20bb132c840281b0dcecfa6a208a4020468804b02196fc91f0e1e1e0dbfff56b7ffc000000000000),(0,0)]
def x251columns : List ColumnInfo := [(88,0,163,0,4),(8,0,243,0,7)]
def x251autos : List (List Nat) := [[],[115,84],[65,99],[65,115,81,99],[81,118],[81,99,65,115]]
def x251levels : Nat → Packing
  | 7 => x251l7
  | _ => emptyPacking
def x251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def x251 : Forest := ⟨251,7,fun j => x251samples[j]?.getD (0,0),x251columns,x251autos,x251levels,x251index⟩
set_option maxHeartbeats 0 in
theorem geomx251 : graphValid x251 (boundsBefore known83645) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx251_7_0 : block x251 7 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx251_7 : block x251 7 0 1=true := sx251_7_0
theorem tablesx251 : checkedTables x251 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x251 0 0 0 = true)
  · exact (rfl : block x251 1 0 0 = true)
  · exact (rfl : block x251 2 0 0 = true)
  · exact (rfl : block x251 3 0 0 = true)
  · exact (rfl : block x251 4 0 0 = true)
  · exact (rfl : block x251 5 0 0 = true)
  · exact (rfl : block x251 6 0 0 = true)
  · exact allx251_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem plx251 : Impossible (graphGoal 251) 7 (vars 251).toFinset := plainA (q:=251) (prior:=boundsBefore known83645) (before_sound known83645 valid83645) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low48891 : Lower (varsX 48891) (graphGoal 48891) 8 :=
  strong_full (q:=251) (rs:=[2, 80, 16, 10, 1, 2, 32]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx251
    (index_root (g:=x251) (i:=0) rfl (before_sound known83645 valid83645) geomx251 tablesx251 (by decide +kernel))
def maps48891 : List (Nat × List Nat) := [(45527,[131,100,50,82,16]),(68602,[100,116,81,128,49,32])]
def known48891 := extendKnown known83645 8 maps48891
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid48891 : Known known48891 := extendKnown_ok (m:=48891) valid83645 low48891 (by decide +kernel)
def x127d8 (i : Nat) : Nat := 0x148813fd30
def x127l8 : Packing := (1,1,3,0,0,0,0,x127d8)
def x127h8 (i : Nat) : Nat := 0xe8021d0
def x127d7 (i : Nat) : Nat := 0x34846d20c63c80742806fd604c3bea8a616f1d130
def x127l7 : Packing := (3,2,3,0,0,6,0,x127d7)
def x127samples : Array (Bits × Bits) := #[(0x2be72dbe676a7f1c840974ffbc5ee5c6fdf77d5f86a3b1fe1c65ee7fbefbd57b5997fbeab9eb03f5bfcf2dc20cbe1e7e791fe734379f7dc73db66e6bb27dd287fe93fe9025c7baf771fd36d8767340885a0e0883f5d059a33c9405c73e21f673,0x8304480008425141008055220084050000084a405260281040020950288100620910129905041050061088058420202010a400209000022853000209904e058004409444246020892200000010d33420030c40091222c94000224212652),(0xdff48e77bb1fe2b361bfef5f734bf69766dedf753bfe7f9deedff167c7f67cd7a2789ef784bf9a7ec939c3fbf378dde225f27ee9e9c11710f38d23fd6f640dacc76fea5e6d7e8d98332ad5c37c8ea6632ca1c077f0232604c0ff62a4c8c6487f,0x20010869950500190010090420100c2010501023209108921000200044041000030820606440102149020000204000c61918ca404c8520e02980a4800120000008003288008102050022810032040600c304b0c31420400804264a488c44829),(0xfd9ac1a630a71da3f7758aa9e782bef51cb84597f87ad41ad9adc514b91e75c21b9e383ff757c888d5567b3da06dc5cdfb20938bcaa1eb795eebab93ccae58fb936a580ddab84d4f3b4fe5deb1c552c480a0a374088cb8470f188338f1078f9c,0x200303216401a86a490ca20504341c049a520ca84d10e5020041082981111062af015561400028c00802d2172119b24280203249613084112147c105e4218e58362f08413e14e0480940800ca496048630c8b0924c8838470a18831071038514),(0x8cea7cd2b39c88417ad2c75227e87f3bc4d1a3dfdf1e5f640fb47491d92f53bdffaaf4ef6e0d77f092bb1ff5c3c56597b37ef37a0d2ed16f064c9bf2dc9b77f101aee36fd307792c9dd16f3fefbefb14835037080a0fc0780fe0f83f01f80fe0,0x1e08988200f6531536e01048d00841ba41853241a20112084402d0866284831c000420820190933463c5004040000920184001b602005802d0382cd20a18102740508488400a15a0069c10b053604019cf170d659047c03005e0502f00b00ae0),(0x8daff17e5cbe4f6599a77e8e893a65494173602d49de86fbc8cfdcf836aa43edde168a0dade5f69765f9fdb26741e34c52dd9175505e11768bb7f0cf7049e8da7ac21dbdac33307e85dfecfb7338bd50015ed4080ef0007ff000ffc001fff000,0x8127054d2009242048012eb728a19a409c00c098400a6000a9682800096a44436bb04020720208830002ac901671268924940200082484d427444000154066100f004833340088102921484e8097b86200a8d28a2bb8004dd000afc0014ed000),(0x6b5aa8c2b17670a934fd88af0267c460dd715c350495a33cdadee7880a03ad9223e1efeff47d07714f0d957228c2c835ed9863b00fbc3cffffe9bdacd8f8fa109aba136996fac265592d56282dd788d85a00e8800bb77f800000fbfffe000000,0xcd9fe484983582714202e46220a19e65040ec32223196a108064f9790220d440c7c99e0cf2540d2726a0c5147437852885e51424be2400bf671c420811d000b90127758284b1b53079c2699b95905e72ccbdffcf3bff6e800000fffdda000000),(0x6ea0e59aa009f49837b43f5cc1d6428fa56e37d5022495f3b97d155e322f9d5ee7d8e81d8499e0b7afbbac9fc930a2e57892b43636d31728fb2836fa3992727ac477ed7a60815c6843796701ecf57b32601e0000ab77fffffff000000000000,0x3c452101202b255a0d18f96fbd02f82c8c1a5aad88700f600245d9224b2a9ee5b881180118a33e6d01235d0b9183ea209a64314a0b278cc10920c50205a56fdd937b04c5732044400109d2a8bcca8d9ff3cfb4f3cebdfbff7fbd000000000000),(0,0),(0,0)]
def x127columns : List ColumnInfo := [(20,8,99,0,4),(96,0,31,0,7),(2,64,61,0,5),(17,32,78,0,4),(34,64,29,0,4),(32,0,1119,0,8)]
def x127autos : List (List Nat) := [[],[16,66,101]]
def x127levels : Nat → Packing
  | 8 => x127l8
  | 7 => x127l7
  | _ => emptyPacking
def x127index : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 5 1 7 2 1 x127h8
  | _ => fun _ => none
def x127 : Forest := ⟨127,8,fun j => x127samples[j]?.getD (0,0),x127columns,x127autos,x127levels,x127index⟩
set_option maxHeartbeats 0 in
theorem geomx127 : graphValid x127 (boundsBefore known48891) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx127_8_0 : block x127 8 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx127_8 : block x127 8 0 1=true := sx127_8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx127_7_0 : block x127 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx127_7_1 : block x127 7 1 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx127_7 : block x127 7 0 3=true := (@block_merge x127 7 0 1 2 sx127_7_0 sx127_7_1)
theorem tablesx127 : checkedTables x127 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x127 0 0 0 = true)
  · exact (rfl : block x127 1 0 0 = true)
  · exact (rfl : block x127 2 0 0 = true)
  · exact (rfl : block x127 3 0 0 = true)
  · exact (rfl : block x127 4 0 0 = true)
  · exact (rfl : block x127 5 0 0 = true)
  · exact (rfl : block x127 6 0 0 = true)
  · exact allx127_7
  · exact allx127_8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem plx127 : Impossible (graphGoal 127) 8 (vars 127).toFinset := plainA (q:=127) (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1151 : Lower (varsX 1151) (graphGoal 1151) 9 :=
  strong_full (q:=127) (rs:=[16, 4, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx127
    (cut_root (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (32,0,1119,0,8) (by decide +kernel) (by decide +kernel))
def maps1151 : List (Nat × List Nat) := [(11742,[82,133,99,49,32,65,112])]
def known1151 := extendKnown known48891 9 maps1151
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1151 : Known known1151 := extendKnown_ok (m:=1151) valid48891 low1151 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low43647 : Lower (varsX 43647) (graphGoal 43647) 9 :=
  strong_full (q:=127) (rs:=[10, 1, 2, 5, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx127
    (index_root (g:=x127) (i:=0) rfl (before_sound known48891 valid48891) geomx127 tablesx127 (by decide +kernel))
def maps43647 : List (Nat × List Nat) := [(43935,[101,134,117,33,48]),(54206,[66,132,100,49,32,81,112]),(58814,[66,130,67,84,48,33,97,112]),(54750,[82,133,99,49,32,65,112]),(59358,[99,132,84,48,33,112]),(55789,[32,80,81,130,66,50,113,96]),(45555,[98,99,81,131,114,65])]
def known43647 := extendKnown known1151 9 maps43647
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid43647 : Known known43647 := extendKnown_ok (m:=43647) valid1151 low43647 (by decide +kernel)
def x191d10 (i : Nat) : Nat := 0x3513412a2048403830787068282019da00034f8f4f0ece8e4e0dcd8d49ccc2890d0bc06266026400431302f2e2d2c2b2a29252128006938085801004989464846022644426201f1e1d1c1b1a191817161514130078904840383070682878201888034403834143c100c2c0121e1c1a180a0806160090a090807060504030201005df9f9aa09514fced000087e02685e48b6fb9b0b3c59eaa946a583b65b8908d40ee12812800ff803fe33ff847fd40ff50ffd53ff443fc20ff103fc30ff14ffc63ff0c7fa00f78cff611
def x191l10 : Packing := (16,1,7,0,0,11,0,x191d10)
def x191h10 (i : Nat) : Nat := 0xb040000a1e000046556d152d79120000873836313aec1113fe1660d7636d803a69ab96bdaf1784df21adb38e08f93ef148618eee4a2670a23a39805a147ae8cb15abde22ecaa42178613cb9188e1ee17182c98394bb5447047e0fc1b15828d0ca98f54cc86809540ada34d94df20702062ed87ea116e7722000caa0918cd253d1979347779c5989b2e19e147c61af308abe933237117b41d9a80c4ad82a0c3ad49204a840148911d1169c65a5d0001448db62a549125489a172000092e000000000000018b2f90cc062323e4e704f86351b701a800000000016614e81830495c000798000b3261881d183fa171115c1917701c3d50c6f40e60007efa000000122a55b2c1d68b522afb30e030000fc680018340000000303722357220000000168660c00000002d20001612ccc9e2e681c416f81e3d8ba4c993092186d211a00000000000001eb0000000000000000a3aa45000000000012c901611e63a46000709a0004eaa34784cbac80000a03907c0004a74000000121480000000000c19114226e800000026672a7000142840f40000001d033095b4ece4803558c5813783502f55938a1510e000197c000000000000018dad41c0000e21c3f90920996087437f19fb9ea0f9e62891964d382e0006129c6843574322b8f91ae8555dc183c000733c0000000000108822c399d84049a5a2940e823b28f2a12000155ab7807d95310e09e8e1c0ff288edd0000250000101b2aa8bc9f8ef93580000004e41c408000000000000029b80001f2c000509f8417c7b2e008c22511ecba558000e05a90600009aa00068fad4e1cea0004807002a9b102fc19360ed96c02dd1900001831a4d800173499274d4786e066bf5000000012a0f21000038e5e45cafa425fcaec8da85ca3880000001162c17ca63015e9a9683792c068d16f83a8001e5a0001e6bcc49a562c4d6c5d154c662c99810d01bc29896568d316ba52b90a00010ae811e15f833f9090318d41391f9508d00cdfd0a82aa00890f140ce81403da80844c000062400103c7f08304f231ec27415a0005b2aa5fa30004283061400000000800024000045810304280020a1ab0014040c03200408028c684002c200022408a000402700000090c0800400000033004006001cb80040440100380ba00501190c00307080c081000c0800c180000008b81020c00302181830400081164c58400000020000c800c0410206485000a0c1810214000040000008000020e181800400301020008300006000200007
def x191d9 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x4b54945523ba3f4473c8db117da2c9452e899511e21f8437a862d09620bb41007ff4fd39f483e2c7b00f4b9e6e3c547774eb19d3a39ec7238e2e1c1837cc6d20d5e1a5d3468670cc97189930745f24bbe17262d8e597cb1695c52b265584a9314b528d050d89e2936f25ea4a108fc116321e441e08080fd51eec3cec7848e741c8438646e18d3719c231c061a8c1e17ea2f0c59b8b1715b82a3c51809a41278242846c08af10fa20e440807ba0ea41c8035c063e0c18166c2b905400a2e127423e841e07240c1816e8251046208440c2815c01a002300007fd2050ffea8281ff4c940ffae2107fd63803fe90c01ff48140ffae4a07fd510c3fe98281ff58233ff8e5007fd52503febb281ff58e11ffae6a07fe77503feb22a7ff50153ffa60887fd600c3feb1841ff58d10ffa85007fd2018ffe90a21ff5c910ffaa9007fe77443fe900a7ff44153ffa4119ffd42443feaa281ff4c553ffa82a07fd53083feb0a81ff58153ffaa519ffd10803fe98841ff5d540ffa40887fd6354fff002a7ff58d40ffaa2207fe7754ffeb1281ff1c940ffa61007fd60103fe902a7ff4c211ffa84a07fd200c3ff11401ff4c910ffae2a9ffd20803feb0881ff4ca00ffa40207fd31443fe88041ff54543ffae2a07fd610c3feb0287ff54153ffa60a9ffd7454ffeba221ff55110ffa82a9ffd73443feb9841ff50200ffa60107fd600c7fe382a7ff1c910ffa80887fd618cffea9061ff50600ffa63007fd520c7fea9081ff54633ffae0a9ffd41443fea8a81ff58140ffa62a07fd20083fea0041ef50040bfae4887f420847ee98c67fe48200bfae2a1ff553847ee99467f754233f7a84207dd6354efeb82877f5ca00fea2108dfd71083fc884017f1c233fec0108ff520847fd11401f748633fba4119fbd41503faa0423fd1c211fba6119dfd7054efeb8861fe5ce00ff2e3007de008cefe39281fe48110fbaa519ff920083ee384677f5d830ff265005fe77443fa98c23fd50510bfceea07f963802feb90817f9dc20bfae431fdd108cefe392217f1c211bfae3005fd7018efe394677f5c553fbaa719fdd548cefeb88c7fe50200fba8119ff953803fc984017f5cc20bfaea18fdc728cfef114677f5d831bf8e0a9dfd73803fc982817f1ca00bfaea205fd720c7ee982877f5c453fba60a9fdd648cefeba2217f5cd10bfaec207dd518cffc90c017f9dd53bfae2207f974803eea0c67f74c030ff0e5007f530847eeb0c677f5d543fbc66105fd72503fa082217f5c053bfae4187f972803fc98c01ef55140ff285007f941803fd00041f758233fbac719fdd428cffab1c237f5d430bfae9005fd75502feb8063f758a33ff2a9007f200847cf22467b799a33beae229ded72102beba881ee91200beae2207d633847af2ac673f5d840fb467005dd73103f5114013f5d830 else 0x92a950a4331d918a20a22114920109c0c6592a950a4432308ca20b220008a491a84e02d1788c082a86094920b0028622e168b0602f128a8b647118018230584e0000139809282c10c58041d8bc54400024b043158ec602f150b0004050300823098b45e2a12968160059086a13208a8a58158b0623b180bc4a40150016421a84c822a29086a13208a8a0109922445a109814301508c921316010024400009831170b4602f15160008218ec802b2c1414310211c4613170a8025b000098592514c8a51231842611494894552a14c46012882c92441504db33188b85630168bc5445304c800c3419ccc652b134b04b056fc26602d11c46f188b8602d160bc5423058043a2b24854880080c40e301604c082a81028025b0030622e180ac5a2c128bc5445244a000d178a8461302094200e2202c00b8584c172724980c58188b85643178ec54002028464519c988c25308e024893094a31158c05a251508c16010e8b85e57239240102c10c003b20142641150d49272e08c26012492060404874302e180bc4a2a118c4560b1685088007954a851299086a41098a9258188c0562d218bc5425200ec00c048201e0415000c132108ac011a0bc858218ec004028c0562d16094545c1184c022f240008a287960424318049a0099cc88a62c954a851120ec6a1340381a0f11804082a2200016a0502410060683c5401070100e138896800f2c954a8512990c8435208a826b210d4264115142600999146451a84c822a210826411a8a8a592a950a6432104ce581d80080421938760f0200c0e4000246230170b4423b178a85640002cac53008d05e50403c1c032488c02042200022b2a950a6522508c025105924881315344733228c8585048200e06118100702050048800610c762e201084350990454529b05543520845c31160c05a2f128ac54bc76001abe18900672388845a25020bc540b0028301d170b0602d17894542b18c562813003cbc1d188b8582d17894542b1855e2813003d7859760a886b0e8b0622e168c04a2a158beaf1509801e3b600bc6bd181006180e8b8602d160bc4a2a188ae2b1409801ebb21b005440e860602e168b04a2f150c457158a04c00f9fafca2b66810956727938100f038380c0d0182408118904c00f85f90b0611f420c837f05ca092c0e18183023e02a3ff57f62fdd9f903f007daef8e5ee8bd967adaf511e84bcbc7914f041deabb887688ec49d673a78747ae7c1cdab98c72c6e459c60387c705ee03dbeeb7876ecedc8db5936896cc0d895afe35a66afad49da68b4966892cff19dc3398662acb21946b240638cc6518a3b12761b4c2a182db0055fb8bf157c52ef55d86ba6972fae365bf6b7496cbad775a30b399655ac4c5822af7d5c4ab4e5626ab1953ca9ff531ca571490a8ef519ea19d411a78e4ea69b8935ca62d) else (if i<3 then 0x9188a42204cc0492134b700239186645192022261911c900b80c009292d1149301239020072512c4c250084c8c44404cb4601936664619114a4b11c984d2512c2e000a49a8166019084e482304c004939a49a31128aa022e231208a32003027002212480b0017092423914b646190b8c4d238848c4318a891010042c921322a42a528012480a11c2c270013920b8494c9e14482216e164517c05246808ca16212298a41228c94944424c0106024940545a2214484813168c838241104a71398092331948a20a1a918950b2240046452484dc14974b4c0472212600832124882a2d18cc520a1464a4a221260081b8489626138d476481c02a164412b48e4825918885964949248228a4510040cc8c45184a0f0e2d11c921180209847240a2005310444e48220b0004941844e068584e020b00181248001709241291844b2e11488261298be5e2e8c05a2c17c2c904513894b8462480204b244984c252968264524109a001904c8c45308400452412145b23c0405003170164624908e480092c8c4430044a46196e0f0e1d91c90450090200a089120000249402008584c8c45310898448992216491a84c54a85124890101400c5722400004928ee0d0d24114024022401327138b09000249874370a0284a463134890024918664519209a472291a0300000c904d260b05e2a240b46446858cc4a00692c94492411c842212118884509b08c22119108a5158c4602f15000c4a25c9815252804ac5319608604188c04a2a200b47600590a7e411a88c541338ac5c31160c05a2f1288c5413240a48b280040ac5313804682f310c5c311d8c05a2f1501080230030b03b161009150e8b8582d17894542b188c2286022801e7336140c8342089864002049c926005b8562e188c05a7011804582f128a801282298206325164a4552a14ca24300908160022114921388f87a3c1b0dcac331d8d014351784c02e9148416002d918485a22248413208a86a5170c45830168bc4a04221240013615868351794ca56298d05e0a29446a4115108a43200ec5a42c10e7f00200ec007098008d3219914c5619804682f28f8783d1b0dc663b05004a6a2c0c4082c1d8c05e25200a82600608c172724124586888b80830178a846311682cb41222001c552a14ca2421a90454134954a8592890c8441150d426a2c0ec802a2194ca683395884472308c42925c9a4a0a210c76002010d06733158b042119c622c020c05e250010d031020b44a2a118045c2f2491c001168d426411510a623234986b25221c7c3d1b158a6271a8e0680117ac2645931184a52c88c8a0199118547210d4264115143a0a160c05e251506056318ac505c2d099800112c94caa5421914020b24800465a3011c26f168bc4a0109810545a05801458200ec4a43419ccc58211688c4712180882360dcc65 else 0x25b25148a2005329348c44190b0c2b170b05a5a129208c451519064210038265b23168885211a889012404c822a40b4544439914925a25201423800cc650b2280104d99800673219114f002212462c129c00045291e025a24902006319488e4a2dca88a492104d44980c008e46228c8e4d9991c8c32229a73382d1208834179aa029001c08a3098008c4521bcc8021909c5c31160c0b8472411492280580224d138c04a5c151208c2c1900164b2409a16011298a41180124844099808e4259a8904413094c2324c0454448584c8a896c94190b8014dc391b0e06e331a96c4c2d1289014d2582a4c2692894c422202e020009914928258984a010991888796c94210b801496272e1208826129c152d9288c263b3542e00913114c10b22094c6d109348d01000c88a830c2c4e492e980c33))
def x191l9 : Packing := (223,2,7,0,0,15,0,x191d9)
def x191h9 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xb41d0000c1f362370000b0e0a5b102aca5e700000000e02bb050608bf03418a1e29e910100000000000000000000f61725486dfc0000000081d8e00700000000314600000000351c0000e2a9000050f300000000b2c816fdb28a221622c30243a21bf218529f200b64498307d83fb1c622a8a2f451a252f121b8ba7912b9000012074148b1e21199428e81bc0000c56600003159150664bd71f6f19b0161748b21aa4504c0fd9069025d9195506bb175a196d11d51a5a2b151eec077c30f0000623fa041b18600000000015d55600000f28100700000115672aae0f2931e84f8790092fe9185030810fac123e6100000a0ad00008263f08352a500000000c075724b0000e2dc11bd000082ef331b72a030ed000000000000000000000000000000000000a29246900000000042fbe13a000000008279cabe331660408312a9cba284016f120ee29a847c41a1723b0115f0cd2d80419e129d00000000fc0301f2e0d352d895ca9eef616e14c7d13d80e30000c1cfb27295cbf147b0a8e14c10733d309131318dc6d4558c264b900ce2a222b44039d12b52973003c29b5018313cd0af1100300ed53832cd7a6a45bf9add11c1701200000000a142b024015161410010d08c000038449282047e708e000058791d4f5429d4627019663a72ec0000230a3c795458000001b00000e315f67f92c6000074790000e10d22060000d8e1422579f65dfb218c9270e317ae6a170c00000000a9380000e1b90000328b989ab60c086cd5d20000916bc0a300000000d80821b741ad72b242c42dcbe69ca2de953911e90000031d04a941e16269c1818087210ebc08ad0de4a5d066400fa88142324242f632f40812d1e86a95b99238a0b9a11799d1c088d0468cb8d02600000000b6d651e765dbe0828277000050604c17009630ee000050bae60fa235e84da176992e14ff00007309a8b812d0e29081ce00000000b2b611fad0b66271b8c7c4aa0000f0a5a48d000090dfd07800000000025082410001410103001600160915040d0e2c651600113a130d01070017030607013e04080a2e006f04190601041406263e0e3a042602050300171092000c000b062420031632121d07047700100b002b051d042b023c820805094617012a026602380f002701060d00102c040302191503040000250103120a062410090e011f3c021d0317010834021d080c04001a0003050e5416180f020b00143c0c08010e1f0404083232080b0f0d0a100c01000200020100021c0704141908000106210e451e000a0500020b00028f000f01010a07020e0c021411390d0f04000015000c010000000217000120020401001f0009150307041933230b070036010042012b1104051513060d002d02160200041c2b000508071b040131020104110e0502020217170f06170b0c000a0205 else 0xa28300007d790000c2011204905924b545940d9471d6b579206e022dd0c3822e301782fda1de31c22994d152c604d139e04e89d90000119892620000219a0000760176400000d980b2be22d680ff0000da955d81c3024e599cf20000d0d9024c0000d59fc67041c96229624ec522d015888b730e90ac00005222e1b5d6b300003d7d5280a305b0fc06ddb1574b0d905be0bbc043096ad0a22c8146e34d29097ef1b15257fec90000417e802dc1918c4de669a11b214a601f830182cf0275dc9a0000c41ea0c5a2d70000793532d40000f08fd2bf82489e0b5049f09f81e391bbb04d0000e14db076320c00b4016cf2a691da4256e14515fb5e8262dfd1fb01bf2ce8f2340df682e00000402a527300003020e07d0000000000005c9011f9a19da2b0a0a700670000a4a7d1f8c6c942d30000fc400000800dd28575fff6d3dab7023e6ca70000e2cbc57c7890830cc0dbfaa9000041770000000040e600000000954ed04b34020000640ad1080000d05e6c775463612732d500008035526b625cd0dee252c118609d80b80000f0eacd8b7deb32ff2668a1a300001599327e908148c3b2c024830000140f000000000000000031a9802c000000007022c0cfe70971a6b0952ca10000d82c0244d1cc80c2425a21ff00008084e1f1000062d2a26ee160b000020572536804c4a292ddc1f5b0f410f892e7a00510fb4665f18fb1147032306492123086aa04a24d70d550b37b1ac2e30000a104027c6109000091674254000072d902ba8876d1689226914362e8405f309c407b000081b3513b0000247bcc6500006514c30622611144242d6470f1ace20b097a823dbefc0000000002a4827bb699000083130000b0f0c09196d20000cc490000d2f8161b1163431140d0d52f705650ce0000002501d9c089bc7660b5497da5dacac9e194201421286ccc000051790000de4a000080a1a8e46cc5d0e80000901b0000f1d0731c000079daf1873011a0cc807a0000c476511e91fd366300008e1542f3acead0f9401ce43720234cfa7d6a000061f4b26c704c71be0000010500003d5884af8ee512c7780e55960000030d515381b64184a190ae11a071e1c0b4038ea381ea459a00005137000031e5b298b21fe1330000d65fe289427451fcc677821a4ad61ecab03169376319517f149b61c73d3ad576367292db042690d43457b112f2a770e426a7f0bf29050000117a000060c74a97d17c000052c90000526800006871c165818a0000000080e7e6e590bc0000000000000000b2cc51a07df9000000000000f8220000000012b50000527d00006d1f715c820d0000c02e3b190000010b50ae314e0000801a00000000126af09a44b700000000310f0000703f00000000f09000008c837def0642000002ca000065e4a03d00000000e0940000b2f9c30000) else (if i<3 then 0x17c5e2805de0f1c1b2921d41c30000c121e162d06dce9d211100f5a14000007a8d1033f11c322c7080b31470270000b1c5000081507122f981b0b2023035eda1fef221a0c0187bc2f71258225940e571ab902952ad1129a21ef49601df553524ee00ab128824cc60c63971e053552930fea1d4902fc4bf2155b120005420e192f2b0d28008ba828c39d18011baf15f5d5c00000000f2b30000d13e6001d4f3c66e0000000052b7012c947592143169031852ae1224103cd287e16d3c3286a3303e78ad412f129c00002299e18bdf0031cd000046b1b2110037a1265cad0000d052949e415b725f0000007910eb1097c624214f703b40740000e6be3264000000000231f9580000e002870d80f7752b669e2ce0000022e4b6893016608d515e100a0000acc8d2470000a215a25bd2e9405a3996e584c15a10580000c0c470a6000046ce0000000000000000c1d2924601e8a11a653262fad2eefa8b952ac8c83303ec2150efa057686d717800d841e4169de4c832e22527c46f958ba2da72e670ec50aa16cd629571821ea841d5511f0202d05500002223895a9072901ec125b1320000c10c644c0000e92f0d840000000039f9002862af40ca000021ca000065d7000022494d9610b70000c1667ef6f43fc2409dd702030000f173d8a0810a15dee4b62051726f307f0db5e0e9960e0000d51a8164159800001aec28bb000006ace2e1f88d0000f8836236e03044bb903aee609102b1837d6782ed12eb12abc0f6c1eda63f8188a293d0d7a28ce46dd977e294c1f074ca3d2eda99f038a2283603c13f31c4e2516220b1f78e83352d1494e6787443c1ae2278c30b10c9d1db54a00000725ed0b05286b17dc481521c45efc24a7304908570a045cde0be4006809b72330000e1359420e1ec21af0013c110f23c8065e90a9267c2009895ca08e136aa4c949d7cfc228fe68a0000000011eb865722605c6821c80000000032bb00000000e0a47099000000000000aa52e18e41a490a9c68e9068ad3581b4c8ce0000ed8592b8000052c1883d0000000000000000fcb100000000ca1000000000000072bd52e570b1000000000000000016380000831a00004ebe7510accededd214bf2914119a501405c0000604f0000906f12ce80456170b20f90426c590000e036b0d1309ec2fc612a0193e4c25213a49a10cb9a12316a9093306169d7e004c4040000fcbeca66320ae0dc8544b55fb5a8000061dc040552bc64d1c26d42a10000c296c6056208669ad26639ba0000000072766a759154f4db82f500000000c1a80000000020980000b4c3f06c000050c1a5b6de1056830000908a0000f07c00002ed10000d6df00004cb07845b42c00000000e8a9b91c024f0000201db96eca83612ea219f1d70000f41bba8a000081d180c89158f6bd997910e2f1ef065400 else 0xa00970da3047b1e6b28dd1e0722fc06361dd00484580225520d6f44072093636f22b522a00000000f124c2c512f051130138e09200000000d103000034a3b10601a7d19245f82210f0bd456466e2c5f959ca0000310700007245d130117b523ac1d3023902eaeaebb27a0000baaab894e2a300006b181227919752c20000befa00002a77e27f0000104400008189bae4e65552f661342a8150210000a3100000c1cb4149219f6954419c00002174b06a017200000000b04a807e9062d116812dd171a0dd8265e2))
def x191d8 (i : Nat) : Nat := (if i<4 then (if i<2 then (if i<1 then 0x20054e11bfa884c600fd9618ce00bfa8848110ddd718cc20fb95291200fd9634c140f5d5258d53ff08148200fba4448600fd91080233fb54150110bfa8850600bdd8154233f5d1095633fda331ca009fc8754633bdd8159233cfd515d8409fd859dd40fcd2048633df5515cd109fd839dd10fd53058e11d7d205d440bdc8758633dbd425d200f76554c211fd93048153bdd8644233fd5514c633bde8848633df9105ca00bf88748600fd92044233bf98348600df57154440bf98154e00ded7254830fd96080233fb5414c540fb94255200ddd7058d539fd855c543fb64480211df5605c440bde8844233df5311c2119fd811c153fe95388a009fd874c420f5d5458d53d7d7554430bf88750a00bf9841ca00fe62280211fe93288a00cfd205d8309fe885c153ded201c910fcd2088a33ddd615cc40bfa8858e00fe94288a009fd819dd40df974800209fd815d540fd92058233dbd7255140f5d5255233f5d5254633ddd605cc40bde884c153df5714c4209fc8750153fe93188a00bf8874c600df5205c440df9305ca00ddd305d543ff11050600fba4488a009fc874c910fd63348211fd9201c233f5e0095633bf58348211fd551442339fc8750a00fd9314c200df5865c440bf98048600fda3388a00dec7250a00df5525c440bf9804ca00fd9314ca00bfa8850a00edd6359153ddd764c030dfa009dd53fb541509109fc8748233f3d5450153bdd8255233ff14148110fe92050a00edd2199a33bdd861c2339fc8758e00bde88546339fd815d830cfd815d840f5d20956339fd825d431f5d5254e33bdd8254233df5419dd10dbd419dd409fd8750940fd48148233dbd7250540fad4248040bf88050540bdc8754a33bde8858633df5855c440fce2254233bf5831c2119fc8750910df9201c233f795254e00cfd7654430bdd821c2339fd811ca00fd9204c143bdd804ca33df973800209fc87585409fc8754a33bf58054e11fd93258e00fb88050540f9d4259233ddd714c030d7d515d440bbd8454540bdd8158a339fc8755110f5d5154233cfd205d840cfd525d830fd9314c140df57154430fd61158a33d7d815d440bbd8250040ddd734c420d7d605d440df97080153ff14280211fd9301c153dbd549dd40df973480209fe885cd109fc874c211df5315c600fd930801539fd801ca33bdd8158e33bfa884ca00bdd854ca33fd63380211ded515c840fda0058a33bf980506009fc8758633fda33486009fe885cc20d7d525d4319fd869dd40df9205c0539fd87544309f48748211fe21188a00f561195633eda0099a33db57150040d3d7550040bb58404110ece2299a33d9d425cc40cbd425d8408fd861c1539bd841ca00d3d425d440fca3388a00db5425c440ed61199a33fd23380211fb24480211f5a0095633bb9841ca00cdd764c0309dc8750a33 else 0x55200ddd7358c209fc8759153bf58308211f5d524c153bdd8244233ded615c840ddd205cc40dbd7550040bdc8754633ff08050510ff08148020fb9544c140fd9528ce009fd805c5539fd8758d10f9c844c153bfa8855200bf98255200cfd615d830ddd7354c20f7a5550600bdd8358153ddc835c9409fd825d5439fd835c910df5615c440df97180020dbd425d5439fd849dd10fb54158540fe92188a00fd63308211bf48758e11fe92048600ff1315c6009fd815d8409fd821c233df9205c600df9205c063bf58258e119fe885d110f9d4255233bfa8848600bdd82502339fd825d540edd6058e33d7d525d5439fd8754c20cfd815d8309fd809dd539fd831c2119fc8780153fd9634c200bf88755200fb94250600cfd615d840bf9831ca009fd841c910df4721c211ede6680233fd56148633cfd605d831ff12080211bdd8058e33fe62250211f9d2091233bdc87582339fd851c940ddd305c543bf58155110edd2099a339fd805d831fb9425d200bdd8058a33fd92080233fd9534c140bdc8748233df5205c453bf4874c211ddd754c030fba441ca00ded805c8409fd825d440d7d825d440ff13080211bf6884c211d7d525d4309fc87506009fc874c540df9724c140bde8854a33ded855c840bf88750600cfd605d830ddd305c553ff14080211bf98448600fe92044020fd5304c611ff130482119fd819dd53bf98158e00ddd768cc20bde8858233fd53054e11fd53258e11fce2254633df9205ce00bf68850211fd61154233fe9421ca00bf98254e009fc8744153bdd8059233ded605c840bf688482119fd815d440bdd801ca33bbd841ca009fd829dd10bf5864c611fce2258a33ddd515cc409fc8758e11ff13148600ddc8750a33bf98050a00edd6158233bf68850510bf9811ca00ded72548409fc8758233df97348110fb9414c1409fd874c940df4815c940df57304110bde8848233d7d615d440fcd5288a33ddd525cc409fd821c153ff21155200df8705c153cfd525d8409fd861c233ff16150600bf98258e00cfd605d840fcd2050a339fd811c940edd6059233fe96388a00df5411c9109fc8748600f9d424c143d7d521c153bf88758e00bdd85486339fc87481539fd831ca009fd829dd40fb88055140bbe8850540dbd425d840bf58404110bde8858a339fe885c4209fd851ca339fd841c1539fd841ca00afd861c153bdd85506339fc8758d10edd6158a33bbe8855140ddd309dd53dbd425c440ded721c910bf8874ca00f9d6091233f9d4150233edd6358153f9d5191233ddd758cc20f3d5454940dbd71500409fc874c6009fd805c863fe92050910ddd301ca33dec725c940f5c854c1539fe885c553f9d4250633dbd425d440bf88754e00f5e558cc209fe885c910bf583442119fc8755200bdd851ca33fcd2188a33bf9864c200ff) else (if i<3 then 0x8143ff92050110dfd805c863dfd7344020dfd605c440fbc8255140bfd8258153dfd525d110dfd7254430bfd854c211dfd205c840dfd605c831bfd8058633fbd4250553bfd8550110fed4248110bfe885c910dfd615d200fdd3058d10dfe885c910fdd634c940dfd8748143bfc874c600bfe8854540f7d5254540dfd205c863fdd524c143bfd8344200f7d5250153dfd7258540dfd765cc20dfd205c440bfe8858540dfd755cc20bfe8858233bfe8848063dfd764c110efd6058d53ff5514c510bfd825d110dfc8748233ff5514c540dfd541c910ff9524c140dfe7754140fbd4258040dfd7448110fbd4158140fbd4154140dfd205c063dfd724c540bfe8858440ff9205cd10dfc8748153dfd205c553dfd615c840dfd7254540dfd525c031bfe8858143fdd634c140bfe8854831dfd611c233bfe884c600ff48148040dfd205c463ff9604c140dfd739dd10dfd605c143ff9209dd10ff56150553fbd4258440fbd541c940bfe8848053bfd8054831dfd855c830ff93048200fdd314c140bfe8848233dfd7254830dfd7650020bfd855d110f7d5250553ff9614c140fdd3050553bfd864ca00dfd754c420dfd7348020dfd315ca00dfd725d110bfe8854543dfd615ce00dfd7550020dfd511c940bfd8258e11dfd635c910bfd821c153dfd8748063fdd3058e11ff5514c910ff98448110bfe8850910dfd735c910dfd205c453bfd865d110bfd8258031efd6158030dfd109dd53dfd7244153ff92058030dfd7250110dfd7254140ff48148143dfd7250553dfd825c053bfd864c140bfe8858140dfd209dd53dfd515c143fdd304c510dfd7158940ffa8848110ff93048110dfd855c831dfd7150153ff9204c140dfe7754540ff48148153ff56150600fdd3044153dfd635ca00dfd7158140bfd8254633bfd831c910ff48148140bfe8858633bfd865cd10dfe774c110fdd6350553bfd8054633dfd764c510bfd8348110dfd7248030ff48148233dfd714c020fdd534c140bfe8854633bfe8848110dfd205d440fbd5450110dfd615c143bfd8550510dfd7258030fbd4050553ff98348110ff92058040fdd3059153bfd814ca00dfd855c840ff21158e00bf98055200fe92088a00fe9201c910bf981552009fd825c0539fc8758940fe9211ca009fd8758c209fd8758940bf68854e11fcd2054a33fe88788a00ff2111ca00df97148020bf98344200bf9801ca00ede668cc20efa6650600bdd8154e339fd861c9409fe885d540df9209dd10fda0054233fd56150633edd1099a33bf58058e11fb94050600d7d525d4409fc874ca009fc8788a009fc8754940fd61158233df48748211f3d54541409fc8754540bf68858e11ede6688a33fd9204c2339fe885c940f9d5450233bde8854233dec72486009fd825d430ded201c940bf88788a009fd831c910fb94 else 0x46c88b61112221042b8848104a1fe03ef87d00f961ef03db87800e921c7038186c20d521a68340867c0cb2195032286220c3a18102f085be0b2215e02b985500a6e147827384b008ca11301d8832a055a08980c5817c01c2032005c80aa012201e001b8000bfd8148143dfd7254940bfd8158e00ff56150540fdd314ca00fbd4254543dfd7158c20bfe8848143bfe8848153ff92058d10dfe7758d10dfd8748053dfd631c211bfe8855110bfd8255110efd6058d40dfd8748153fdd634ca00dfd7154c20dfd205d540dfd755d110dfd7159153bfe8858e00bfd864c200dfd205c543fbd4250510dfd205d430dfd865c440fbd4254440dfe7754940ff92058153dfd825c063bfd8054a33ff9205d110dfd205c053ff92055110fdd3048153dfe7758540ff55150510bfd861c940bfd8058940dfc825d540fdd314c200bfd811c153bfd864c510fbd4248040dfe7755110fdd2058d53dfd7254440bfd8258430dfd205c143fdd204c143dfd205d840ff48148063bfe8848140bfe885cd10efd6158140ff92044153dfd215d540dfd764c420ff92050910dfd635c600ff48148053bfd835c910dfd7148020dfd835c910bfd8158040fbd4154940ff92044200bfe884c110ff5514c553bfc8758e00dfd764c910dfd7154830bfe8844153dfd7348110bfd8250110fbd4158940bfe8854940fed2054a33dfd429dd10ff5514c110bfd8148063dfd615d440dfe7758940dfd305c910f7d5255140dfc7255200fdd3054543dfd7258140fbd4254840dfd605c840bfd8148053bfd8148233bfd8258633dfd605c031ff53148510fbd4255110ff48148030ff92058233fbd4158d40bfe8858031dfc829dd10dfd525c143efd6058633dfd7248140dfd511ca33dfd765d110bfd851c940ff55150910fbd4148140bfd8058e11fbd544c540ff48148200dfd7650110bfd8158030ff92058143f7d5254543dfd754c020ff55150110ff92058140bfd8258440dfd7158030dfd205c153dfd729dd10dfd7148030dfd7258d40bfe8854a33dfd535c910f7d5244153fdd634c200ff5514c420ff5415c910fdd3258d10bfe8858430bfd804c940dfd865c031fdd314c940bfe8858e11f7d5254633bfd8258233ff9514c140bfd8650110bfe8858d10dfc7250600bfd8254543bfd8058d10bfe884c910ff9204c910dfd7650510dfd7258430dfd525c831efd6158040fdd604c143bfd8054543dfd7348510bfd854c940bfe8848600bfd824c211ff5515d110bfe884c211dfd7254840dfc725d540dfd865c430dfd205d830dfd605c543dfd764c020ff53148600fbd2055140bfe884ca00fed2054940bfd8158d40dfd7650910dfe7748110dfe774c910ff48148020ff5515cd10dfd7154840dfd765cd10dfe7758140dfd205d543ff54148110dfd7154140dfd209dd40bfd825)) else (if i<6 then (if i<5 then 0x821f0402073c0ce816b024a041c07480b700e200fbffc7fc6ff29fd3bf8e7ed6fd49f9cbf207e22fbe1f6fbebc7d5afa79f3dbe4e7c42f821ef2bdcc7b66f691ec0bd5e7a8af489e8ebcfa799af2a9e3ebc647896f0c9e0cbc0077f6ef61ddabb9c771aedd1da8bb2e762aec19d76bade758aea89d44ba7a74c2e971d21ba2a7436e831cf9b9da736ee679cc2b96c72a6e4e9c95b91271f2e3a9c68b8b8712ae1f1c36b84a7076e089c04b7f06f9aded1bcdb7786ed2dd19b9bb7146df6db61b5fb6b06d2ed9d1b23b6386c3ed7f1af1b5de6b76d6b1ac9b5846ac2d521a9cb52069fad391a60b4a8690ad1b1a2eb44e686ad099a06b3fe67b6cf099d4b39066dacd51998b30465d6cb49961b2be655eca8194db28c64bec8c9911b20a63a6c7118d5b1a66342c6718c1b16a62cac5818a8b138623ec441885b0f261dac329858b07a6086c0097efafd05f96bea17bdaf6c5ecebd39790af085df2bb0974fae9a5d16b9c972cae365c3ab8396f0add25b22b4f169bad285a46b47967dacec5992b249641ac7458a2b091605ac0657daaf295d3ab845686acd1588aaee556eaac9556aa9e550aa9b151faa1253f2a7094d9a99a5302a5c94aca92c5212a399461a89650faa169420a81e501e9fb13dfa7b04f2e9e213c1a76a4e8e9d0938fa71a4e169bf1371a6ca4d4e9a6133aa65c4c7298a9308a6024b9696f12dba5a84aa694c1281a4f449ca9331259a48648c69151218a42247fe8f991f0a3c847868e811c3a36446968cf1196a31445f68bd9173a2d845a68b11155a28844de8909114a1fc43c687010d3a18e43128571092a10c41fa836905ba0a8413281b1029a030401a7f80fe39fc23f667dc8fb19f363dd67b98f709ec83d5e7a58f439e643c967878f029e003bba7698ebc9d603aa274e0e859cf239b27350e629ca2393a7238e359c48385e7058dfe9be437966ec8dd19b9436ba6d60da49b3a36426bd0d779ae0357a6ae0d3b9a40344e6838d049a0433c26720cc8998232fa6478c8298ec31a66338c5598a6312e6248c41987430ca60e0c0f981030166018bf197d42f8a5f00bdd97982f125d98ba1972a2e0e5b90b60966c2cba58e8b1596122bf25780ae895c22b665668ac595682ab25500a9894fa29ae52a8a43948228aa5118a1b940027f64f889da938826de4d809ad935626164bc897692de253a4a3893f9252248648a890891e4238246788b89162227e4498890910821664268840906820c6410081d902c204e40387fa8fd21f5e3db87af8f5a1e823c507788ed81d923ac07558e9c1cf239307198e1a1bda37506e78dc01b3a36386b08d341a4a34086748cc6196e32a06388c62186a307060b8c0817f22f305e38bae17162d5059d8b1816122b485578a8c14fa294051b8a1e140a28004f389e2137e26484c18956127a23c8 else 0x440c2611204712845110a0168601016000c02490444000012482108a21142000a312a242508e24c00718049100b60c5d16890220930018470908111c4602c7020261168491081058a3202c00114820400000c3b100491a2a294002490000a26098c031186a1022a0a842902828c4a2508824c00804c00102630084504c4011e2511060800200bd0010802488231804518540980038ba2d1804412600367e100462289578004c12481a855000c42000422846011c4012431184a228c47125001808228922102001014228029290138004080022408a350c490893000e02390498007011c85e840b130491c000008400ec49188a10002008920008822973f0c660080022912511440400223841380044124800bc13108e3008838b44789449180a1540024004412470004451244b11c5a2c5b000c030ee0000060984481245b1188238c020bc4910840008020000204002209238cc1312445208e111c0104c5c20762488518944a4504911e00388e248933000601888800002490009c00220924000289826300c1514a0012481509222a820000201684711449180a8508e808922296635080011480980021084b0044911e0030b100084808810008100088248c02286404005b18048114401000248c0011c461c5b12c17001044124406fd2f2bc65a25e23052a1056188601785450ac310c02f0a8a120a82c8aa288761a9cd04ac40ee2a170581685e1504a1586218628000c022bc310b0300b42f1802a0942bc500011c4568b22a894298a2224c2088262388a24b0661946819c5612c58efc231805a11c456eae0e85c1605a1785412856188618a0003008af2ac3ab83a170581805a128541586217e2a000c022bcb44bc45504aa0982950842efc4020621805e1500060c4300bc2a0acb5c22b6dd6aead2b59cab2cd640ac4f583aafad5dcab9b56aaac8d564aa9754a2a87d4f6a9a752eaa50d488a8cb510aa0ad3fca7ef4f7a9ddd3a2a7274dc29b0d348a6734c5a97ed2e4a5974aa2951d280a4cf4912915d212a3cb47328d9d190a2c74502898d118a1ff4372866d0b4a137420a834d05aa09740ca811d00a9fcf3f3a7dacfa69f433dfa7adcf429e2b3bca76ccec09d3b39ea730ce529c733882703cde49b8336a26bdcd589a573472681ccea99a332ba645cc8698db312a618cc2297ff2f9a5e1cbaa97372e0a5afcb3c96472c02573cac495572a4a53cca56948f2892505c9f2938b26b24c4c95c928724aa48dc8ee91bf231a45bc89e910b21da42ec84490431fd23e3c7ae8f2b1df23b1c7408e4f1c6237ac6d28d731a5a339c65a8c5b182a2fdc5e28ba716ea2cbc5928b1b15aa2a3c5248a17137a262c4a288d710fa212c40c880f0f921e0c3a8870b0d12190c30885df0b32159c2a4851709a2122c21883eb07720e6c1be832305e20aac13c) else (if i<7 then 0x890230845089200085a082622092312413108a2d884904c50888e248c46124492890050e154504712482388a21681312ae1009212d82080020089223c0041204916c4620b41118471016008002208a5124220092200001504a20d413100100045b11c42289228942080000100340be0018260009571120000049289023892228b45120131144c11c4930902308e32d02004c45124609c6438088411c2080000108c23892229040000424840a11c451245a2816260923077e116860102600081311c60188e2e08450816000c02492250c5d168c022400249852450518944a11049801004002000009908a3300224800300c2302e250004728c01124220855000e001240011c8098c02001630085a1a84518162209230000b18071745a3008824c006110211890228c4416c451c9a19a0000c645001010c5a09882a114424c003808e411c4a12460206a098a2d8950c82e00288e111845108000085a087700080b00400124820400000c4800049188e230923126001c04720922e08001146018b824882a04c00189211082a0007000920008e44a822308a2028201004710040008e3008100000301781400223892204c6010262289232f8205898238c420a841d880238cb508923009000c5b1288905c005114200a822922828c4a2508824c00802c4c1246abc002609242a8222840012442308a211c491684620003008a31242ab898248c4508222488e304c601002a114400bc01000617a00211c491706214002124224845300042b00020400111420114220c00211e2511062040021491580049267e0088138004412481dc00211c5b114637888215a00100138004412489ca702388a3514010a842284350aa0018762008e311422d0657110001248248c0282823180600266228c011244411499908a2067e18ba2d180441260031a0155e001304920a223894300882289270004712442488e20aa00108e14544911c70000021244611c5a240000080008c0230c0a11c451245a28422400022900b124515044012441188e098b841686010d42308000040095c4718047088e37888302c4712462308a21804510b824884380043788820ec471000100022384a168010a1411504ec087600080b4004911c80124280064248c02d08e128920009860044711049800a8544a21200010002e0c0248c3b00041608a0e8010a94490820a1684811d25110451245c485e12885c1244204002008215400300901024a104c27604454c8001808238922cfc20008c0988a3114224840011c4418070006001104918002d09230ef3f108f12a4c31246011062985e000d14148518944a1104980108004230a84519601124601081128a0000042d041308b410ee2510901400441247000400124460864d1680100045288415000302c00124602026240923022a29400249 else (if i<8 then 0x30451c14128880010441244011500146422892312447121811a8481686230600110480862704c49188e22884612442308a20c845118600a800114622092212c4711070a200217049124f0589223904412440008e24a60000069488b0000044504911c780040011442d08a20c901114624045a12442488e2406251092350b00084a11100a124a111c44146423092304c44108822880008064168471c22220923170491046244028010251104518b623084512450588a248c6049445188b128800088824884711449280020c80b00062388a248c45124480a0119092495c4740062922a238924000224000212000140022080a0945a184a2208a304162408464040018920008440a502488e310045146605200311049124c111c49144a2208a311813114623088242c4500062d08820c8450006238882120471050240a2111449188a10ca0040060008e211c44124e11893001047110496814220c604046a114824800217049104a142c2a00049208a149425104c116c47140023084408b4230847110420402240c5c1220b1688380c022c0041144410d42208461144248de211c2511062d088212028588a000d2d168471c002d8847110491a5022c00312400141416846241032118491892180046108c11204514ae80000300112124471a502289238844912062d08a24cc13114492090248a0b11449189a23203000c0542e2511460208e22085a1104049a2511072b888248d26894519092238d291704804c45124c8008c228c4412442288c21304517070008c216821288a21104712462388a000c2711c5c124893092238c4412442305140a050508e24904817042f000240c4412449288a09a00416822d89220941310b42208210c8471814144c22289220c8461247000b424a00012462d0e0218000108a800b6312447144a22094311c45108a248847000400050b8944248b8242e25110612850008e10008a3804441144922643040000104512450a88e800c451185190922124286400000c601145a18b623884b8950118027120491c5d168c0239100110451a0505092239049000422800211c001092238848124408b625168699400000c461144940413110485c00000c6040047188c24880008922d8911088a098901000451890000a11088a2488024800218200108a112422209224005a14162d08a309445108800084916c422092211049108811a84810b824880a085e22086311050524a050c60114492862d894441888111c44108e22085c124413088248c4712442280020b044114780050b12446188810ca00000600092249c5c124622092211822308a21084804c69284a80090416c2230c024ce000006228922021700092304c2098d428c8224402350c48110423044800042588c220c00118435216000c44000424216000c4811842d070 else 0x45000480a011908e410a0b126002002000a6316844188a80084411c422800217049109623886a11040504481244718b82488260944412481940020290b40063209221104912661189231104910de248847124435054220c481))))
def x191l8 : Packing := (799,3,7,0,0,15,0,x191d8)
def x191h8 (i : Nat) : Nat := 0x28c60000124000248d00000007129cf005a70f50000000f0a4000f019866a1de43d73a00000003c3474b7cd2812ef86a0bf414d11000052fc000e2d554f63344f2e1a7012e13f0e3e351ae57126c1b8e70822407c8c4103484520454a0000000000c344ce6038d7601dc9554aeca5f2a2479c1ec5157232fb8d1048533193e37b23b8b400014ae303f4bd00030d0e2204d5d22c000008c0000000c2d91d1c4022fb4a6000090ac15e82c834c000a6c90dd50394c5224b8131118042c8b00000000000f1a0000924c0df0002839000000040e00000000000f0820add270000818f08ff28800062ac83b232400082840007140000526b55c833f0b600dc805430f03163684c72251819205e0364145b2c50a94ea1005881c0ff7af48708241151c5d63bb4ed30f003e335b47e1c11c354d0c86a2360800f338000732245fb36d875329e45a71830e101cb03262ec000139400000020e652bfb3a519e53a8010c80b21e05ec2aa09700bbcc1702c00081adceff8f0000000057091b74215218402826e8cce122803c2c909eb2c40000003043c09b06c1171cc000034f400020ba0000000000000000000005b0541d00000006095c0c71e287c524752c9c284d951b8c2bf2c1473d194000c1398a4758096758acc84264b78750eb4cb9370000b3ae0282259c59371b8336345c70d1d9456000186f026002700014900378471828e81c552e0ece20e0b7e328015e061c8a42a5c58a380000000007a00000000002099000050e0003f2b6276882406a0c272f1c5b33cf4f1000084d5214000000049f60428e492e7052c18646222b1c89311dc09102280ac2e0455339ece9e388000f1f400052cf20631fc0000002193205881e0230060000403807417c90080000090062000001c35400122400400000851810860c00020cf3000c00801040091831031c10400032410c00000010400430440410090400490400801c014100200008000010210a0400020410810021400023c1000043002001281000000
def x191d7 (i : Nat) : Nat := (if i<1 then 0x48754a33cfab8d10b0881db5425c5511033e922c02e431d7d655714c4208fe4bb0c99401db54261571103f4a8440a40204fd6468848233cbe43aa4a02a71fd9021d618ce3fb23442e4a047f6488758e11afa4bac2a0c015bd9420a77443a7a84c12ea2073d245205d8408fec910ea8a811fd91a21755023fb2443a20a9e7d261205c4538fec910eaa2213f59121d638023f92f442430076b481425d840ef848a40b80a7dd5515cd310833eae34424029c7f25d824c211cfab0b033ba81db57150960103b3a84902e62076d50576501108ff4cb04b80a797c875495150397a84902ec2074f509815d4408fecbd10900c7d9d42581731031f90eb02c319cef652885cd10e3eb0ac0ba8811fd9121d208ce3fb2043ac708cfd6468848110ceeb190e994015f591a21724433eae2c12c22077c5457348110e9ebaa84b08815ed9158172103be122900e119cef652884c211ef4902c0b90819f48121d208cfb6a82bb284884df6568858233ef4902eca12215f59261971103b6ac2b9282a07ec50520509108fec910ea02a7d3d4254575102bdb24b0ae42067d545831c9109becad10b00639bd4260575103b3ae6a12c2207ea4814255110ceeb9d10b08815f591581711033bae6c12c2206ed5058158d40eea48a40b9881d3d7550920103fa260a8a62a076d5c54258440af6cc2c2b90811fd91a217054f9e922902ec187e6505634c140ff0902a2a1221cdd61581731039dac2b02e42067d2058748053cde43a84aa2213dd93a21424423f92ec12c708d7da6487482119fac8d10902812fd96a215250397a84a8aec2067d2058748153eec9810e902a7f3954549305033eb0e40a40a076d509525c440cdeaa10e98a81db57150920102fe130a0a40887f44c08148143eec902c0b9881f69524811054fc3ac8aa2c6a9fe84814150910af84ba4100423eca0088a668cf36b08b98208872b509205d840fc490284982871f49760d208465bb2d442a519c7e25d815520087e4c2a4bb0613ba99610728036b30b198e50067521e3348211fe119c23114013b594a21308463e930902e229e1f549861c153bf0c890f11401f49205493054ef332640282a06ec612111ca00f6900423334670fc98549761026bb2b442c119cfc6448758e009ecc9900a0a813d993a214280373309198e50063721d63591538ee4bb04aa4671bd94a21734423eb23442e4885e664c80551408deca510b82a71bd9421d518cf2eb0ab9820884f564688482338eec9d10b92819b5825c5401023b92ec128119f4b509205d4409f8c890f11401b398591072803e9445004ab19e7520c815c940ec6a1240b9881f5200846558cefc324402828847d646885c940fc8a0a6298281ec622846668cf3390e42260a9fc64c154501539ceca10ea8c67da5424817110327b04baa802047d6448758e00 else (if i<2 then 0x1010a100100a08c205156281246008e124442a128451800044a11c228c22842404248424842484000002284220424840120248800004908490e2a08022841000238824840000024041cfc20000108a144a1145efc2000450a2508a20000000300451803004228480051284510000834d74c348346f45b3c33572eb2ab2971ff1bf17f16b1571430d7097083016fd6f12efee92e7ee6ae2adbed26d12ca6c3ac26c12ba6b92b7eb6ab2aaeaad6a6aa56a16a029ee9da99a98697295e94a90a8f68e287680a79e78a74a7367226e264a60a57255e54a53652250e4fa4e64d24be45243e42a41640239632a2ea2d62c22ae29a25a2462061f218617215e14a10a0f60e20ce0ba04e039ff9fe5fd1fbdfa9f95f81f41f01eeded9ec5e85e19dadd99d85d19cd9c6dc59bedbadb99b2db19b05ac5ab1a71a319f198594593191d8b189d83181d7dd7c975d6f16b167163161d60959d5314f14dd49d4893c53b13452ad24122d2192051991590ed08106d000fecfd8f98f84f70f5cef0edce70e30dc4db0d44cd8cc4c2cc18bacb14b00aecad8a40a009c09809409008ec8d88c48b08708307f07dc77075c7487346f46b467466062060c5a056054c5385245104d04bc47c4684283e837c33c3283142d426825424022c1941801401000c00540140033eb2243c450047f6448788a008fec910eb1c011fd984817114e3fb2443ac6887ec5058448110fcaa0a6299281eb56150562502beb22aa0e4884fd6468848063e9ea92e4aa2811fd9021d528cfb5a84902ea204fd6468848053cfb4c90e904231fd984817118e3fb2043ac8a9dfc6468848110cf6b9510b0881fa92050960103be122902e031efc48181551108fe4bb00b1c23eb541585605023f92ec2a6108c7f6448758e00cfc9010eaa2215f5964c571803af240b02ea20779245805c840e9ea12c0ba881f9930551315023fb25442eaa04bf65a8854a33f6cb1ac0982819f591a21724433e930902e2206fa4818255110afac8a40b88a75dd91581731033e902c3a40a1f67509515cc409becad10b028757d91581751026fb2b442c0a07e64c14050553cbea9308382a79dc874c1638473e90243a40a9d7d661205c4538fecbd10900a71fd9121d6454ff9240a9260a1e7d245825c053cbebab04b0881fb14158530503b3a84a92e62076d509865c440cfa40b0e900c7fb141481404432f90ea9220a9e7721d3048153afacb902900a7df120581711023f92ec0ac70047f261205c5538fec890eb04679bd5161072803ae922902ea2047fa65805c863fe898102902a797d75a21611025fb2d442a418e7d245801ca33afb4cb0cb8881d3d425497510277b29442608847f648874c211cbea9302382a73f591a212050f9eb0cb02e22073d585605c440ed6a1240b88813f591a212054e3fb2243a40a9c7f64 else 0x248400414028928c2d046105b08c24021023208f000611021142000022849120a0830a84716000901026114249010c824880002612841a850558a0491820aa00104500020009920010000000108810045400200440800085e100000092100030200155740020c08004008c100180068aa1409230d41090110248c0000000000155d000800000220491044092244a1000002001000008022a0010000000100000aae8004008a100000000238700040000490e152002a288004004320922a28108a80040a2a8005100200881244000000800004000423843010010440800c50248808943008018020003000440512880005000400040008a80041208008228401102089a18080a002030a100107008a80061808008000060000208a10881244110248810942288000881000142e800804c900098006aba00))
def x191l7 : Packing := (246,4,7,0,0,12,0,x191d7)
def x191h7 (i : Nat) : Nat := 0x68e86000083591a2800282388f1f65bc9015c0ee0af2981412000004a200000242c8c11ac2f406904274288180200c72c0
def x191d6 (i : Nat) : Nat := 0x4408248400e1508228400c15080118200000000345420c01047049800182487fbb7735f4b06c2ae9a5641fde9d5c1ad9985712ce84403d49524c087481538fc2a520605544430dd636408759153de85089850520443f40a1481524c153f6848171509601039a92021d425511087d686996097014e1f5a1a65805c863f4a4814258175103d2542245205d4409dc6949850520443d8542245205cc4087d68497a2121803f81424c08148143e695089848171103ca542245205d840e744c08121d2054e1f5a95c68848053f625092058173103da1414817650910b0729d645516354e07ca9549861c153
def x191l6 : Packing := (23,5,7,0,0,8,0,x191d6)
def x191h6 (i : Nat) : Nat := 0x81900
def x191d5 (i : Nat) : Nat := 0xa3390a134a4c28290221e50549302048748153
def x191l5 : Packing := (2,6,7,0,0,3,0,x191d5)
def x191samples : Array (Bits × Bits) := #[(0x4fde62e1b3f8637c014def51a9d57194af990ccab2734dfeb29ceed37fcdb0f29173eb3da8eda9eabb91ff09f2c0e44aceb1de4caea7bef923a5f3abffd1c8366ddd7b6db1ab3e794a17a2b303a5d3a08d057d614d52462e5050041d6a22f277,0x1212c4110744011041388400000108000080122046088460200114000004642900528498002008014624a400004008030001000440060a80995030001421008000218b0280932c60aa01a5972a05488088805da0420020247018200020228002),(0x5310af345aef1b7459d91f1af9c77e3cfcdccdc19329fee32848a3e7516aff4dda5df883aa8e2320c4e2e595cf1fb39922e5f70c77775253a27edfeca59e893e6bb4a02e488edd7d14500e3ac400c3d3804d285828a088001781a6949cc6ea3b,0x64c91342381184228a05180554183300d525c90aa1011b035450ea4a031a12048d813100f585561889081bbc358343982e1a2780228070544203c142c11a030343c230015424831410704a289598904f024d205bb8b50e4285c1d7a68cc56b7d),(0xb40fbe9f70ad72d9b8377c3a4c3ecffaafeee95f1f6834d7edc3c17d4046e7ef9898b6b84717d2db66e7a7b4373e54dfaba20ebb0b5590c4c76fec14b6574fef7c3f888c784144efa682bd807a4561326378820025a5b0c0bea6a74295050888,0x8804288040a028815040006200458006080a10311000409808840084f000004a0200422e0010206000400000001014210000d0020860048200a00a891001085080380482080200c16486a4404a0621304120d2800502d0811a2a001051008000),(0xda3f33779cd409dbeaef9ef527ef9785d07be9344cdf95b423803372ba7cc33e6ad4c6df2e3c3c274ac7a7a25bf31e9439cfa5db5c070b22da775f53deb767eb76cfaaad5afdc2cc89c883949c73a005dcb203db9200004020014bc005f90da0,0x11c84709ad5b901403170484bb22350000802a00486e810774005551001027b180d4b40081e10188420236d8e1018002d0c4245c778201509d5e203067fca28215c1737495352700896143b615718804bc820115ca842220a090e3c124b20ef4),(0xbef9d3fda7f20dc8c385decd1e028ac7fa25860ef0a7b5fe50f7d1d1f5f924c46ea40b575779828fb718ffc32de71e56f8edc3d052cbbdebbff44cf368fda5cecbe84b183be0368c554b304d809a160d0c6ec0bad77bc20c08414c0801fc7140,0xec241040400048a330c0021844900242707441180081408000a0802c2e4398420d2148641e0c4272295001260c2c20a8062288a00041500f60a043890002407c020a00806248008f149a1848c08a1659036ca20a357bc4cb0c611c3e414d7100),(0x797e25d66afae44396d73f38758851881726dfacbeb677331f77edf70b810bb5955ee80758924e4e2c2968eadd876feb0d38ecb89858439c174da4dc862bfa109cc87757af76efe41d644048456c8c6851f41505118a1d334b191ea9ea000404,0xa160380a4008848892025932c02cf097ea024801802300901e90880e35300142752c0045011424c829c0002059305080e002d22281800062600c822008044752a20840112a40121055c44840d5629038517c0005958e5b030a218e3fca010110),(0,0),(0xe56d857ac9728f56ed0d22c59a79f35ebdcf1e36861e7e94d5af533a82be6d4fa61de2fbdb45f6f546bb68c76898eba339bb756d8a7bd6cd45b3fd4780289050bb06561eb755a73a722952cb26984ecbbe83a114202d3999c92e10e224002600,0x449b02540b1702622001a2880d820f20010502442c1cb02000621450000b94808803a590dc225b13d4371a82a4c62b5a08fc01d53204d21510137512444a20001583b22084b10020023912ab20984ec3ae83291a6271247ce58471c024022644),(0,0)]
def x191columns : List ColumnInfo := [(24,0,167,0,7),(2,0,189,0,8),(160,0,6687,0,7),(8,0,83639,0,8),(8,0,93879,0,8),(8,0,1719,0,8),(8,0,44727,0,8),(8,0,54967,0,8),(8,0,109239,0,8),(8,0,119479,0,8),(2,0,43197,0,8),(160,0,31,0,7),(2,0,18109,0,8),(8,0,42679,0,8),(8,0,47799,0,8),(8,0,88759,0,8),(2,0,17085,0,8),(160,0,2079,0,7),(2,0,2237,0,8),(1,0,190,0,7),(2,0,2749,0,8),(32,0,2719,0,8),(16,0,93871,0,8),(16,0,119471,0,8),(16,0,13487,0,8),(16,0,42671,0,8),(16,0,44719,0,8),(16,0,47791,0,8),(16,0,54959,0,8),(16,0,68783,0,8),(16,0,83631,0,8),(16,0,88751,0,8),(16,0,109231,0,8),(24,0,1703,0,7),(160,0,1567,0,7),(4,0,187,0,7),(2,0,1725,0,8),(24,0,42663,0,7),(160,0,42527,0,7),(2,0,58557,0,8),(160,0,57887,0,7),(2,0,58045,0,8),(24,0,83623,0,7),(24,0,93863,0,7),(24,0,44711,0,7),(24,0,47783,0,7),(24,0,54951,0,7),(24,0,88743,0,7),(24,0,109223,0,7),(24,0,119463,0,7),(160,0,44063,0,7),(2,0,44221,0,8),(160,0,88607,0,7),(2,0,83645,0,8),(2,0,93885,0,8),(2,0,44733,0,8),(2,0,52925,0,8),(2,0,54973,0,8),(2,0,64189,0,8),(2,0,99005,0,8),(2,0,104125,0,8),(2,0,109245,0,8),(2,0,119485,0,8),(0,0,191,0,11),(160,0,98847,0,7),(160,0,83487,0,7),(4,0,83643,0,7),(1,0,99006,0,7),(35,0,156,0,4),(9,16,166,0,4),(19,0,172,0,4),(36,128,27,0,4),(4,8,163,16,5),(129,32,30,0,4),(1,0,47806,0,7),(4,0,42683,0,7),(26,0,165,0,4),(4,0,44219,0,7),(8,0,13495,0,8),(8,0,68791,0,8),(160,0,93727,0,7),(1,0,93886,0,7),(1,0,54974,0,7),(1,0,88766,0,7),(1,0,109246,0,7),(1,0,119486,0,7),(4,0,88763,0,7),(128,0,2623,0,8),(4,0,99003,0,7),(1,0,104126,0,7),(14,0,177,0,4),(134,0,57,0,4),(56,0,135,0,4),(24,0,7847,0,7),(24,0,12455,0,7),(24,0,68775,0,7),(20,8,163,0,4),(8,0,3255,0,8),(32,0,11423,0,8),(1,0,52926,0,7),(160,0,52767,0,7),(4,0,44731,0,7),(4,0,104123,0,7),(4,0,109243,0,7),(4,0,119483,0,7),(24,0,4263,0,7),(168,0,23,0,4),(16,0,6319,0,8),(160,0,103967,0,7),(16,0,3247,0,8),(2,0,3261,0,8),(152,0,39,0,4),(25,0,166,0,4),(8,0,1207,0,8),(32,0,6303,0,8),(160,0,47647,0,7)]
def x191autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116]]
def x191levels : Nat → Packing
  | 10 => x191l10
  | 9 => x191l9
  | 8 => x191l8
  | 7 => x191l7
  | 6 => x191l6
  | 5 => x191l5
  | _ => emptyPacking
def x191index : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 173 433 7 14 8 2 x191h10
  | 9 => lookupWord 297 1487 8 16 10 2 x191h9
  | 8 => lookupWord 142 357 6 14 8 2 x191h8
  | 7 => lookupWord 13 33 3 11 5 2 x191h7
  | 6 => lookupWord 1 3 1 7 1 2 x191h6
  | _ => fun _ => none
def x191 : Forest := ⟨191,10,fun j => x191samples[j]?.getD (0,0),x191columns,x191autos,x191levels,x191index⟩
set_option maxHeartbeats 0 in
theorem geomx191 : graphValid x191 (boundsBefore known43647) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_10_0 : block x191 10 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_10_3 : block x191 10 3 13=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_10 : block x191 10 0 16=true := (@block_merge x191 10 0 3 13 sx191_10_0 sx191_10_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_0 : block x191 9 0 15=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_15 : block x191 9 15 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_51 : block x191 9 51 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_87 : block x191 9 87 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_123 : block x191 9 123 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_125 : block x191 9 125 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_161 : block x191 9 161 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_197 : block x191 9 197 26=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_9 : block x191 9 0 223=true := (@block_merge x191 9 0 197 26 (@block_merge x191 9 0 161 36 (@block_merge x191 9 0 125 36 (@block_merge x191 9 0 123 2 (@block_merge x191 9 0 87 36 (@block_merge x191 9 0 51 36 (@block_merge x191 9 0 15 36 sx191_9_0 sx191_9_15) sx191_9_51) sx191_9_87) sx191_9_123) sx191_9_125) sx191_9_161) sx191_9_197)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_0 : block x191 8 0 22=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_22 : block x191 8 22 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_58 : block x191 8 58 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_94 : block x191 8 94 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_130 : block x191 8 130 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_166 : block x191 8 166 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_202 : block x191 8 202 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_238 : block x191 8 238 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_274 : block x191 8 274 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_310 : block x191 8 310 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_346 : block x191 8 346 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_382 : block x191 8 382 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_418 : block x191 8 418 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_454 : block x191 8 454 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_457 : block x191 8 457 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_493 : block x191 8 493 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_529 : block x191 8 529 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_565 : block x191 8 565 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_601 : block x191 8 601 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_637 : block x191 8 637 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_673 : block x191 8 673 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_709 : block x191 8 709 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_745 : block x191 8 745 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_781 : block x191 8 781 18=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_8 : block x191 8 0 799=true := (@block_merge x191 8 0 781 18 (@block_merge x191 8 0 745 36 (@block_merge x191 8 0 709 36 (@block_merge x191 8 0 673 36 (@block_merge x191 8 0 637 36 (@block_merge x191 8 0 601 36 (@block_merge x191 8 0 565 36 (@block_merge x191 8 0 529 36 (@block_merge x191 8 0 493 36 (@block_merge x191 8 0 457 36 (@block_merge x191 8 0 454 3 (@block_merge x191 8 0 418 36 (@block_merge x191 8 0 382 36 (@block_merge x191 8 0 346 36 (@block_merge x191 8 0 310 36 (@block_merge x191 8 0 274 36 (@block_merge x191 8 0 238 36 (@block_merge x191 8 0 202 36 (@block_merge x191 8 0 166 36 (@block_merge x191 8 0 130 36 (@block_merge x191 8 0 94 36 (@block_merge x191 8 0 58 36 (@block_merge x191 8 0 22 36 sx191_8_0 sx191_8_22) sx191_8_58) sx191_8_94) sx191_8_130) sx191_8_166) sx191_8_202) sx191_8_238) sx191_8_274) sx191_8_310) sx191_8_346) sx191_8_382) sx191_8_418) sx191_8_454) sx191_8_457) sx191_8_493) sx191_8_529) sx191_8_565) sx191_8_601) sx191_8_637) sx191_8_673) sx191_8_709) sx191_8_745) sx191_8_781)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_7_0 : block x191 7 0 36=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_7_36 : block x191 7 36 22=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_7_58 : block x191 7 58 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_7_94 : block x191 7 94 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_7_130 : block x191 7 130 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_7_166 : block x191 7 166 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_7_202 : block x191 7 202 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_7_238 : block x191 7 238 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_7 : block x191 7 0 246=true := (@block_merge x191 7 0 238 8 (@block_merge x191 7 0 202 36 (@block_merge x191 7 0 166 36 (@block_merge x191 7 0 130 36 (@block_merge x191 7 0 94 36 (@block_merge x191 7 0 58 36 (@block_merge x191 7 0 36 22 sx191_7_0 sx191_7_36) sx191_7_58) sx191_7_94) sx191_7_130) sx191_7_166) sx191_7_202) sx191_7_238)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_6_0 : block x191 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_6_2 : block x191 6 2 21=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_6 : block x191 6 0 23=true := (@block_merge x191 6 0 2 21 sx191_6_0 sx191_6_2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_5_0 : block x191 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_5 : block x191 5 0 2=true := sx191_5_0
theorem tablesx191 : checkedTables x191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x191 0 0 0 = true)
  · exact (rfl : block x191 1 0 0 = true)
  · exact (rfl : block x191 2 0 0 = true)
  · exact (rfl : block x191 3 0 0 = true)
  · exact (rfl : block x191 4 0 0 = true)
  · exact allx191_5
  · exact allx191_6
  · exact allx191_7
  · exact allx191_8
  · exact allx191_9
  · exact allx191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem plx191 : Impossible (graphGoal 191) 10 (vars 191).toFinset := plainA (q:=191) (prior:=boundsBefore known43647) (before_sound known43647 valid43647) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low6847 : Lower (varsX 6847) (graphGoal 6847) 11 :=
  strong_full (q:=191) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx191
    (index_root (g:=x191) (i:=3) rfl (before_sound known43647 valid43647) geomx191 tablesx191 (by decide +kernel))
def maps6847 : List (Nat × List Nat) := [(5053,[129,82,97,48]),(17390,[66,114,132,49,32,81,96])]
def known6847 := extendKnown known43647 11 maps6847
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid6847 : Known known6847 := extendKnown_ok (m:=6847) valid43647 low6847 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low18111 : Lower (varsX 18111) (graphGoal 18111) 11 :=
  strong_full (q:=191) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx191
    (index_root (g:=x191) (i:=4) rfl (before_sound known43647 valid43647) geomx191 tablesx191 (by decide +kernel))
def maps18111 : List (Nat × List Nat) := [(4541,[129,82,97,48])]
def known18111 := extendKnown known6847 11 maps18111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid18111 : Known known18111 := extendKnown_ok (m:=18111) valid6847 low18111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low17087 : Lower (varsX 17087) (graphGoal 17087) 11 :=
  strong_full (q:=191) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx191
    (index_root (g:=x191) (i:=5) rfl (before_sound known43647 valid43647) geomx191 tablesx191 (by decide +kernel))
def maps17087 : List (Nat × List Nat) := [(17087,[]),(1981,[129,82,97,48])]
def known17087 := extendKnown known18111 11 maps17087
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid17087 : Known known17087 := extendKnown_ok (m:=17087) valid18111 low17087 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2239 : Lower (varsX 2239) (graphGoal 2239) 11 :=
  strong_full (q:=191) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx191
    (index_root (g:=x191) (i:=6) rfl (before_sound known43647 valid43647) geomx191 tablesx191 (by decide +kernel))
def maps2239 : List (Nat × List Nat) := [(2239,[]),(12479,[116,83,32]),(2427,[130,114,98,81]),(1967,[113,129,97,82,32,65,48]),(2493,[129,82,97,48]),(12733,[129,116,50,97,80]),(12775,[84,117,80,132,96,48,32,16]),(12782,[66,114,132,49,32,81,96])]
def known2239 := extendKnown known17087 11 maps2239
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2239 : Known known2239 := extendKnown_ok (m:=2239) valid17087 low2239 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2751 : Lower (varsX 2751) (graphGoal 2751) 11 :=
  strong_full (q:=191) (rs:=[2, 1, 2, 4, 8, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx191
    (index_root (g:=x191) (i:=7) rfl (before_sound known43647 valid43647) geomx191 tablesx191 (by decide +kernel))
def maps2751 : List (Nat × List Nat) := [(2751,[]),(3263,[84,115]),(11455,[117,67,32]),(3503,[133,80,96,113,49,64]),(3517,[129,80,48,50,114,97,64]),(11709,[129,82,48,66,97,112]),(6631,[115,83,82,130,99,66,16])]
def known2751 := extendKnown known2239 11 maps2751
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2751 : Known known2751 := extendKnown_ok (m:=2751) valid2239 low2751 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1727 : Lower (varsX 1727) (graphGoal 1727) 11 :=
  strong_full (q:=191) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx191
    (index_root (g:=x191) (i:=8) rfl (before_sound known43647 valid43647) geomx191 tablesx191 (by decide +kernel))
def maps1727 : List (Nat × List Nat) := [(1727,[]),(2367,[135,50,65]),(7007,[135,101,50,33,16,64]),(12719,[113,129,97,82,32,65,48]),(17341,[129,82,97,48])]
def known1727 := extendKnown known2751 11 maps1727
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1727 : Known known1727 := extendKnown_ok (m:=1727) valid2751 low1727 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42687 : Lower (varsX 42687) (graphGoal 42687) 11 :=
  strong_full (q:=191) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx191
    (index_root (g:=x191) (i:=9) rfl (before_sound known43647 valid43647) geomx191 tablesx191 (by decide +kernel))
def maps42687 : List (Nat × List Nat) := [(42687,[]),(47807,[117,67,32]),(44351,[135,50,65]),(58175,[133,117,16,64,49,32]),(47967,[135,101,50,33,16,64]),(53087,[133,117,101,33,48]),(44923,[130,50,81,115,98,65]),(69499,[128,64,116,81,96,49,32]),(55215,[113,129,97,82,32,65,48]),(69039,[133,80,96,113,49,64]),(60349,[129,82,97,48]),(69565,[129,80,48,50,114,97,64]),(42983,[115,83,82,130,99,66,16]),(45031,[84,117,80,132,96,48,32,16]),(53230,[50,117,131,49,32,65,96]),(60398,[64,132,49,96])]
def known42687 := extendKnown known1727 11 maps42687
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42687 : Known known42687 := extendKnown_ok (m:=42687) valid1727 low42687 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low58559 : Lower (varsX 58559) (graphGoal 58559) 11 :=
  strong_full (q:=191) (rs:=[2, 1, 2, 36, 1, 9, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx191
    (index_root (g:=x191) (i:=10) rfl (before_sound known43647 valid43647) geomx191 tablesx191 (by decide +kernel))
def maps58559 : List (Nat × List Nat) := [(58559,[]),(64191,[117,67,32]),(51007,[133,117,16,64,49,32]),(54079,[135,50,65]),(46431,[133,117,101,33,48]),(63839,[135,101,50,33,16,64]),(54127,[128,97,65,49,33,112]),(48507,[128,64,116,81,96,49,32]),(63867,[128,80,81,67,96,113,32]),(43951,[113,129,97,82,32,65,48]),(51119,[133,80,96,113,49,64]),(43453,[129,82,97,48]),(64445,[129,80,48,50,114,97,64]),(55783,[84,117,80,132,96,48,32,16]),(49646,[64,132,49,96]),(73710,[50,117,131,49,32,65,96])]
def known58559 := extendKnown known42687 11 maps58559
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid58559 : Known known58559 := extendKnown_ok (m:=58559) valid42687 low58559 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low58047 : Lower (varsX 58047) (graphGoal 58047) 11 :=
  strong_full (q:=191) (rs:=[2, 1, 2, 16, 8, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx191
    (index_root (g:=x191) (i:=11) rfl (before_sound known43647 valid43647) geomx191 tablesx191 (by decide +kernel))
def maps58047 : List (Nat × List Nat) := [(58047,[]),(68799,[116,83,32]),(47935,[133,117,16,64,49,32]),(69439,[132,65,48,80,113,32]),(50043,[128,64,116,81,96,49,32]),(58235,[130,114,98,81]),(42927,[113,129,97,82,32,65,48]),(60335,[132,100,113,80]),(44477,[129,82,97,48]),(55229,[129,116,50,97,80]),(55271,[84,117,80,132,96,48,32,16]),(50158,[64,132,49,96]),(69102,[66,114,132,49,32,81,96])]
def known58047 := extendKnown known58559 11 maps58047
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid58047 : Known known58047 := extendKnown_ok (m:=58047) valid58559 low58047 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low44223 : Lower (varsX 44223) (graphGoal 44223) 11 :=
  strong_full (q:=191) (rs:=[16, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx191
    (index_root (g:=x191) (i:=12) rfl (before_sound known43647 valid43647) geomx191 tablesx191 (by decide +kernel))
def maps44223 : List (Nat × List Nat) := [(44223,[]),(44735,[84,115]),(52927,[117,67,32]),(54975,[116,83,32]),(42815,[135,50,65]),(44863,[131,65,50,114,81]),(53055,[133,117,16,64,49,32]),(60223,[132,65,48,80,113,32]),(42847,[135,101,50,33,16,64]),(50015,[131,67,99,116,50,33,16,80]),(58207,[133,117,101,33,48]),(60255,[132,67,100,84,48,33,112]),(42875,[130,50,81,115,98,65]),(60283,[128,80,81,67,96,113,32]),(44975,[133,80,96,113,49,64]),(48047,[113,129,97,82,32,65,48]),(53167,[131,33,99,67,32,81,112]),(69551,[132,100,113,80]),(44989,[129,80,48,50,114,97,64]),(53181,[129,82,48,66,97,112]),(58301,[129,82,97,48]),(69053,[129,116,50,97,80]),(48103,[115,83,82,130,99,66,16]),(50151,[67,132,99,82,16]),(69095,[84,117,80,132,96,48,32,16]),(69607,[80,132,99,112,32,16]),(48110,[50,117,131,49,32,65,96]),(55278,[66,114,132,49,32,81,96]),(69614,[80,84,132,49,113,96]),(74222,[64,132,49,96])]
def known44223 := extendKnown known58047 11 maps44223
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid44223 : Known known44223 := extendKnown_ok (m:=44223) valid58047 low44223 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low88767 : Lower (varsX 88767) (graphGoal 88767) 11 :=
  strong_drop (q:=191) (hd:=inputs.getD 1 zero) (rs:=[2, 0, 2, 4, 1, 1, 4]) (u:=1) (v:=3) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx191
    (index_root (g:=x191) (i:=13) rfl (before_sound known43647 valid43647) geomx191 tablesx191 (by decide +kernel))
    (index_root (g:=x191) (i:=0) rfl (before_sound known43647 valid43647) geomx191 tablesx191 (by decide +kernel))
def maps88767 : List (Nat × List Nat) := [(88767,[]),(104255,[135,50,65]),(94047,[133,117,101,33,48]),(109435,[130,50,81,115,98,65]),(119727,[113,129,97,82,32,65,48]),(124861,[129,82,97,48]),(83943,[115,83,82,130,99,66,16]),(99310,[64,132,49,96])]
def known88767 := extendKnown known44223 11 maps88767
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid88767 : Known known88767 := extendKnown_ok (m:=88767) valid44223 low88767 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low99007 : Lower (varsX 99007) (graphGoal 99007) 11 :=
  strong_drop (q:=191) (hd:=inputs.getD 3 zero) (rs:=[2, 1, 2, 0, 1, 1, 4]) (u:=4) (v:=12) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx191
    (index_root (g:=x191) (i:=14) rfl (before_sound known43647 valid43647) geomx191 tablesx191 (by decide +kernel))
    (index_root (g:=x191) (i:=1) rfl (before_sound known43647 valid43647) geomx191 tablesx191 (by decide +kernel))
def maps99007 : List (Nat × List Nat) := [(99007,[]),(104127,[117,67,32]),(109247,[116,83,32]),(119487,[84,115]),(88895,[133,117,16,64,49,32]),(94015,[135,50,65]),(109375,[132,65,48,80,113,32]),(124735,[131,65,50,114,81]),(83807,[133,117,101,33,48]),(104287,[135,101,50,33,16,64]),(124767,[131,67,99,116,50,33,16,80]),(99195,[130,114,98,81]),(104315,[128,80,81,67,96,113,32]),(83887,[113,129,97,82,32,65,48]),(89007,[133,80,96,113,49,64]),(99247,[132,100,113,80]),(124847,[131,33,99,67,32,81,112]),(83901,[129,82,97,48]),(94141,[129,116,50,97,80]),(104381,[129,80,48,50,114,97,64]),(119741,[129,82,48,66,97,112]),(94183,[84,117,80,132,96,48,32,16]),(114663,[80,132,99,112,32,16]),(119783,[115,83,82,130,99,66,16]),(89070,[64,132,49,96]),(109550,[66,114,132,49,32,81,96]),(114670,[50,117,131,49,32,65,96]),(119790,[80,84,132,49,113,96])]
def known99007 := extendKnown known88767 11 maps99007
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid99007 : Known known99007 := extendKnown_ok (m:=99007) valid88767 low99007 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low83647 : Lower (varsX 83647) (graphGoal 83647) 11 :=
  strong_drop (q:=191) (hd:=inputs.getD 0 zero) (rs:=[0, 1, 2, 4, 1, 1, 4]) (u:=2) (v:=3) (by decide +kernel) (by decide +kernel) (by decide +kernel) plx191
    (index_root (g:=x191) (i:=15) rfl (before_sound known43647 valid43647) geomx191 tablesx191 (by decide +kernel))
    (index_root (g:=x191) (i:=2) rfl (before_sound known43647 valid43647) geomx191 tablesx191 (by decide +kernel))
def maps83647 : List (Nat × List Nat) := [(83647,[]),(93887,[117,67,32]),(83775,[135,50,65]),(99135,[133,117,16,64,49,32]),(88927,[135,101,50,33,16,64]),(99167,[133,117,101,33,48]),(83835,[130,50,81,115,98,65]),(124795,[128,64,116,81,96,49,32]),(94127,[113,129,97,82,32,65,48]),(109487,[133,80,96,113,49,64]),(99261,[129,82,97,48]),(109501,[129,80,48,50,114,97,64]),(89063,[115,83,82,130,99,66,16]),(109543,[84,117,80,132,96,48,32,16]),(94190,[50,117,131,49,32,65,96]),(124910,[64,132,49,96])]
def known83647 := extendKnown known99007 11 maps83647
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid83647 : Known known83647 := extendKnown_ok (m:=83647) valid99007 low83647 (by decide +kernel)
def x511d14 (i : Nat) : Nat := 0x380c0280801804008008ffd60
def x511l14 : Packing := (1,1,9,0,0,0,0,x511d14)
def x511h14 (i : Nat) : Nat := 0x1430b081a330000000d07c000f0cc41a400c000f0d0000e050000000242a60a3825000000080f40000001c0b3009010905cc12000243f003101b10180003036432000000070700000003c24f09800000000000000000000001d0000023000000080b602e000140fe0638010002c3c0000439b0bd00a0003811f0d643b00b38162065429e088ed7702440000010270000000000000000ac00070e083a4012036e020000e01c0000000000a0f80000000000000281300000000000000000203100010050000000d087c0e9078000000203700008158922440dae01
def x511d13 (i : Nat) : Nat := (if i<1 then 0x32818d0ef1d83aa740128ac08873080818a0340580822b40e0300580a01e038068630280600000909a18830a61802d05501215c2a05d0b21590305f0bc05d159c1742185a0b01582aa070b201115a0605e024d0a013c2704d09812c2504909011c2304507901a0003e00e0782083d08491004803040c8430841042003f07c0f41e00307602410180e81c83806e0d81a8340660c81883005e0b81682c05002601c0640e02011822042098128278008ae0102a00208210520a01382604b0901182204208004c0503e0040f01d40e882b00f00404a0604215024014240000305601a00a0780802413120a0108250d81b41342480a1b83589e40e138008a60ce081100000c00806802818048e00003806802025158471c5020651c9ec4205a0181b81f1201c0302b0120802b81a12e12490be1402784509a1241f84707c1081e03d5260241d003040883806e0d41a03205c1781683a07208c1402704c1b411207524024008205448a074f89d03d0590161b41e922344605c0fa18c2d0580a80ec2b85500000c0302b0ba164480040120bd509011c1f8490841042002b00c01c1f03d0780240183a07604c10261b4140270420981282b00c01c118220022002502a0ca081109011c1f849084104204768490141f03d0780240187e0fa06c10261201f8420821002383e07a1241e00905a00c1d81304080030020000380480281c04901c838a704df091158580141ac1e141b83686c0d69a834a6884901424857002068101c19c330650360740a81c02e0300c01602004c0580a0280380681a002990048005c0d01802c050090110200300580a01e038068090b80002d850482d0590b015c2b0550a894c2922b40c0100e05109e781c0360680c81802e0580a8140260480881001e0380680c0160280380300c01602009010001bbedaf37b87ad5db322b8eac3e9f6a47e76c992256690022e788160cb8131f6a7a4ddc7754dc036e95b52686198e643d87a5f956e258dd5ce54e54a450c13594ae5224442d0813c40e4f3798d7d32f0c693058bad2d10a83265892d21007691aa05d1146c4bd11243a90a981da04bc000ffea9ac1ffc32583ffa40b07ff66160fff2aac1ffd41583ffb28b07ff60160ffec9ac1ffd84583ffae6b07ff5d160ffeb8ac1ffd51583ffa42b07ff60960ffe29ac1ffd92583ffb06b07ff54160fff112c1ffd30583ff92ab07ff24960ffeb82c1ffd32583ffaa4b07ffa6560ffe882c1ffd81583ffb2ab07ff24d60fff19ac1ffd75583ff8a4b07ff61560ffeb92c1ffd97583ffa62b07ff64560ffea12c1ffd43582ffb2ab05ff64d60fdf222c1efd65582ffb24b07df95560bff4cac1efd61583dfac8b07f78cd60bfecbac17fd91582ffb28b07fd84560ffc882c1efd63583fdc44b07fe80160ffcc02c1bfe88583bfceeb05ff66160 else 0x4038030ad1588f08681d03018253529a10301804a7b1280411583f40e589f0b61444b86212a1e00402f80101d0382b80c1cc3706d0bc1b0358201048ac00847640c817024070088100300580780e01a0300580a80802004a2a294727480a08115a6f4f62100606e07c818d05c12c0f04a0600b4040780a013c2684505e1781c84004c1202384207a0e81f03c80881c0482070128830861b4008840e281c40009040586203806c1785e02a0401d0390180600b40312a02c0501a01c034098144c80240080064300820ee1483c8990d220c3d043456818420710410101320701298a70680c8180670cc0203c01c0360bc2f0150220e81c8260300580581403500e15a2b40f0190301d01804c0509b8080240082a000082714c1703e86310a2302d0580ac2400481f1002342a0590761542bc000bb00d15a0640e011a03e1e01785e04c1682c0560aa1502c8574562744c02a00219825aa5505204e03c1284605009e1342285607c1081e40045681c2588509817c2404908e0f603a0607600c50809008082014617c2804f08a0fc2484708500215c070981002083d0781341f0480068181c809040c8a209012420c7684881d0303e07a0f00484214211c01896118054102819c3301903a1940e01b024062018170220400780c01c02c0a01a02a04c0501601b00515809000e09f1389a2028094e021c0920608281cb13c2744e0520f20a44c8691061c421c0200681d030840f500515809500881a0288191580c01e0380680b0140580c0000122344a8451369a9a13225c3647680a01915a070dc1ac368200a80040a098090928e4f808137a700e20283583c456509712c2542d8510fc188398780bc0e601c2b457019030070dc1ac0402f0da0e8364048000041502004cf09451400537a7401e818101023d470874f8035158201c4688c0f01703e86310a0e81c85a0b01582ac0340c1780405d0b215e000540768ac45820002011c51509115a0604081c418890aa05836042304440740e0243fa2b40d00201c010ac58870fe20c408750860044207a0e215c04820341c83f0841042003e07a0f02404707604c101a2182284d02a11c0c014020108208400350ae0340707c0f41e013040214180095c420831042043484345681c3d07104015010a06012787f0ea0053da700ba81c07020253e27b0f50141022b4e09d0368590160f5039a1e42c0550a81742c8570ac8ac26078)
def x511l13 : Packing := (64,2,9,0,0,14,1,x511d13)
def x511h13 (i : Nat) : Nat := (if i<1 then 0x1e14ee0aa780d682bfb0b120aec025ce1e2002e0000548b80000e1160000000000000c0b7000000003806e5748703ed053281ec41009744e84c0000000000000700ef4048807f307c8000000014011000000002c2a761227b7c385d000000000c03c00002e1f2010700000000120a4c12d0000381140001c0f80000000039d720000813680000000060dd20420000042cf0002c05518127c230c147e0a5d85cb5d560000e04900000000000000000000000000c0df00003819402ca0000b0273a2f80000a0076010200a9c0960000f07dc01000000017b0000681ac000000006073f04cf80062e4c567bc0340000120d4509ca811000000000000000000000120194055800000001887ff07ae81d1c137930cf951e84e0c2620000d006d834a40f2aef6506b00002d9a92146b044c0589424820fd0000000001cec0000d73b8000280c7410b4040204afc0500000000000000c2f244ea00004bc0141df201e000000003c09f811bf41a7020480442e6e8078a83cbed6f0127c0208820800000000000000001028840c5708080000000000000000000000000ed75fa2e7013381d200611b7f48450802e40d8e073485bec064805a20a4a0478c1b46171f05d453a8416581250000000000000003d10891023b015a0000d929e84d980b041411767d836f0087c366205b403b71a9c530f4054680d21c65916e78507040801b82094790ee84858193206db02cfad041c8aa11fb680d4a6aa47720cff7024cbf7eae1409aa09e9858f107e0000000000001804680d5694b80002c149ad79c03e083fc858b202140af6153180b8210410387030400000000f013ac325412ca0060000602ba41ca0000b0973838da4d7ed0b7063303445d928e880000504f800000000504e000000000000020a800002424c00000000305a80221010550048000184a4207a1091c84a80000a0a1b000805814121e108e053e027e40bc000001000a0100680080088080080203800005c4300040094000800300020f0000000e00940108400034001000318000080000000918820004000004000000000002000180001001000808020800500000000010000080201000000801100004000000c40000067000100c0a08020880210000068000000010002210820000e1000600100038000008c400000000220000448060100000080098000030600000008001000000040002c010042108d440002020000204000800001c00100200086000000000000140000920000000002000001000600000c008000000008000004070080100080008020080000000004010140000400084050000000080080060880008c40000000902000000000200002000002000003800000000000070000000000004600000008001000000000000c000140018020000020000008840010002200000404 else 0x21d29816ce049e02a4e413a0b82752c00c40145c0bc0748082cc00ea4e31f02ef21c3a448eefa1048f856400000000000000000c094401000366c98ec0b70106f0b7402c18233c85c602a2801000000000600a0000000014169000000002c2ea0000f038800000000200eb70b1c18594c2ed54d76618155427e40e84708f838381f4412c702138556808ec00ba075d051400000000094d8393ec066876a0417b014301ee802d401e0814f0294c158d070a8220000120dea75b545c3c2532066698310559c2e066bcf028881f9815900f3c2b7a000382cc60990000184754207ad6f000058cb4000160e20000682160197203000870000061a8000000000000125f0412019046b8a9118b401b316fd05e3815e213cc063e8455cdb1e062703d800000001c03f800b5a0ab1c84000000000000000000000eb48800000001601adb940035d011a0e2f8901401dc00000000e17d00000c1fcc0ec000058be4819020674703f8503626bc0980000000000000606f00000000000000161e0457055c0000000030663020cc05360a52087802838169407320a7bca4f42a40000c0050817fc2d7482097128000000000000000000000000124dd000000000410ee06860991804d026a0000000030061803a40560000021e2c21a0000300400000000040fcd92380000813d415cc05de84e9802ba04dd029380140001001fb7502c8629cc480eaa15580536c223e177e062083b941632137400908593e9cf40b5201f13ba7405ff28b106718233410c000c101c1c4eec2d0000070a180002c117ce7bf05f800018276811abbb0800010238000070780b496dd7f406a3007803340001ae0fd373f811b4285416df9149830bc1a68134000000003406d6117b0167455a0218a15a10947856c004a202b1053402f800000220600e280e7025f526c56ab98180c226c072772080002c17a0800a034c4ad410f8217cb061c0d8c00000000000000000000188e8d233b81d8807440268b6ef0302dc61c0d930a88042780aec0950000302e40001d133d0854832b8091ac5e00000000240ddc0e4b0bb33b9302f4e89e10479019000000000a04e885200000000000006028f02e780f40000000000)
def x511d12 (i : Nat) : Nat := (if i<5 then (if i<2 then (if i<1 then 0x2ffda344160bffaa952582ffeaa54d60dff64d805837fd9261560ff754a33583fbd545d160bffaa9325837fd5365160fbf58d50583efd6554160ffe601425837fd9348160fbf59530583efd3159160ffe4c1705837fd9314960ffe60171583ff93044160fbf54964583ff55160560bff69492583ff95244160fbf58d70583efd8259160ffb549205837fc9264d60fbf54d64582ffda214d60dff28993583ff53148560fbf59580583ff9a360160dffa64535837fd935c560bff68c525837fca364960dffa6622582ffda254160fbf59521583efd6550d60bff68c95583efd8258560fbf4c5655837fd52a6560dff6a5535837fd9354160fbf595205837fc9564d60fef50974583efd6360160dff6a532583f7d5254560bff68895583bfd52a2160dff289955837fd925d160fbf58d105837fd9344160fbf59432583ff55284560dff6a5315837fe994c960dff60997583efd5258560dffa64325837fd53a6560dff649505837fca954d60dff6a5525837fd925d560fbf58d51583efda654560ffb4ca225837fd9295560dff64d75583efd6348160bff68032583fbd5291160ff754e33583efd6314960dff545975837fd3064960bff69493583efd6324960dff4c597583efd6524960dff48195583f7d5254d60dffa64525837fd9224d60ffe60141582ffda224d60ffe545805837fe9995560fbf59633583efd6348560f7f61d71583efda654d60bff69532583dfd735c960dff549945837fd9261160ffb54a225837fd3265560ff754d30583f7d3295560dff54d91583ff930601609ff68d97583cfd639dd60dbf596995835fd7165d609ffaa9925833fd92a2160fbe58e00582efda614960efe60184583e7d63955609ffaa9935827fda914960bfd68432582efda60c960f9f594955827fda914d609ff68d915837ee99889609ff2a553583edd6324d60fbe58d105827fca995560df764a33583ebd6391160efe601855837de998cd60f3f596775837dc9364d609ff6a4325833fd9860560b7f69c32582f7da50c960efe601815837f992801609ff2a532582efda358560ebf58e885837f993801609ff6a532583afd65a2160bef69052582efda614d60d7f64e775836fd6364960bbf695615827fca9549609ff696995827fca988960dfe64d80583ef96560160fbe601615837ed9224960fdb88a555827fda95c960fd79563358377c9565560df765633583ebd6461160fbd58581583fce228cd60dfb2a622583ef96580160ddfa665558377d93955609ffaa995582bfda80c960fbe601645827fda3a6560dbf58e995827fda266160cff64e88582ff9a00c960df72a633583ebd64505609ff2a6335827fca950560dfe65600583ef96544160dbf58d945827fda2a6560bef69032583ef96360160ffc54510583edd658cd60ddf2a6555835fd929dd60 else 0x31fc30c82e142b90284c25f8240421501efc1ca81b7419b0181c1448125410600f2c0ca80a840710042c02f801940003ffd8750960fff54e22583ffd825c160fff5cd98583ffd534c560fff54980583ffca254d60fff5cd80583ffda74c160fff54d72583ffd824c160fff54992583ffd7161160fff5cd41583ffd535c560fff68980583ffd534c160fff60920583ffd5464960fff6a573583ffda954960fff54d20583ffd315c160fff54d50583ffd5354560fff5c193583ffda354960fff54d42583ffd8254560fff54921583ffd5260d60fff54951583ffd535d160fff4c580583ffda54c960fff69d53583ffda354160fff54573583ffd305c560fff69153583ffd7348160fff68985583ffd314c160fff54991583ffda548160fff4c584583ffd7364960fff68153583ffd8250560fff68951583ffd5250560fff54920583ffd3150960fff69521583ffd5260960fff54953583ffda060960fff68552583ffca354960fff61d20583ffda74c560fff54910583ffda04c560fff4c173583ffda854960fff50971583ffda454960fff54985583ffd5250d60fff54d21583ffd3065560fff5c580583ffda54c560fff60971583ffd3060560fff69182583ffd528cd60fff69d80583ffd5265560fff5c192583ffca348160fffaa953583ffd4264960fff54993583ffd5250960fff54d32583ffd524c960fff5cd93583ffd3064960fff68950583ffda354560fff6a120583ffd5261160fff54d10583ffd5265160fff68553583ffd5260560fff68530583ffeaa54960fff54998583ffda560960fff68152583ffda254d60fff54930583ffd3160960fff69530583ffd5254160fff549315837fc3265560fbf59510583efd635d160dff549935837fd958cd60bff68d75583ff9a760160ffe4c5805837fda960d60fbf54d615837fd3065560fdf54e55583efd5258d60fbf59532582ffda354560f7f5cd745837fd9354560bff69521583fbd4250d60fbf594935837fd3166160dff549915837fd935c160f7f5c570583efd6550960ffe5cd805837fd9348560dff24995583fbd5391160ff74ca33583ff93048160ffd54571583bfd8260d60ffd4c5815837fd9225560eff609815837fe998cd60bff68d50583fbd4161160fbf58d755837fd9260160fef551845837fd5364960ffe54e00583efd6395560ffe48180583fdd314c160bff694325837fd9214d60ffe48170583ff95280160fef50941582ffda260160ffb54e22583efd634c160eff60181582ffda550d60f7f54e77583ff9a344160ffb54982582ffda35c560dff24d95582ffda261560ffe54d10583efd655d160dff64e55583efda64c560ffe54980583efd6325560fdf54a555837fd5166160fbf58d715837fd5266160ffd54e115837fda960960dff64970582ffda324960ffe6898058) else (if i<3 then 0xf0af034040c07707a083043071084607057897009503cc0940e40540b021801803003c05c06315c04004ba04602e05810d0910160320299da17216c02584d453412980d1024f605507e45702014240ec27027b08985980b091301682782f01f01e349015004810249c01fc2249ec81e16602c08101a50a011f09e0ff0f109b08b0810bd08507a12000307d07980801340e0414a6a86c40502a86b86d268801098069501f82482382101e01e81001695e804a80949ee1ac2000a8024c18c0e410e11e0fe00c00e1221410af034c56040d26a29a881c0627b09483f22b8100a1207584103303383280b80e00700580680a00600b00c00500d532303804c828c0fc10010410812411c0f80f40f002408204caf60b5f40f4f84e90da1780f4627428a26fa7b80c2060a03827c2d23b42cd03115c28829237ae378bf748b72076ef36ccf6adb66a76513622f5f1b5d5759b356cf52fb51f74f734c2f4afb49f7486345df444b42b741233fef3e2b3a873713348f30eb2e372b83286f267b24e723831dcf1c0b1a4715e3141f10db0fa70e130c4f09cb08070673047f016afeb6fc02fa6ef5aaf356f102ef0eecbae8b6e6c2e52ee2daded6dce2da5ed80ad616d302d0aecf4acdb6cc52c8dec56ac166bf42be3ebcdabba6b9b2b8aeb77ab5e6b122aefeacdaaab6a9b2a84ea71aa5b6a0629ece9d9a9c6699b2987e96ba955691228f5e8d9a8ab68772860e844a7fb67e527c5e7afa793677d274be714a6ce66af2698e66aa6456620260ce5e1a5b9658b2556e53aa51b64ea24afe466a42063d12393e374a35863302316e2d6a28a62592221e205a1d161b52192e170a15d611d20dfe0c0a0a76094205ce028a0005fed1fa9df8d9f5c5f2e1f0edebf9e8b5e691e3ade129dcf5d951d72dd3e9d1f5d061cefdcbe9c845c6b1c45dc0b9bbf5b761b59db169adc5ac91a94da699a445a2219e1d9bc999d59811967d9489938592518d2d8a49852582117ced7be9784575c1727d6f696da56b21662d643961b560515eed5d895b955881559d513950054bd14a6d47b946254401423d41093fa53d51397d375935653431317d2fb92d9529f1288d245922951fb11d5d1b391945175115bd12190e150c810a5d0749064504b1034d00f8fea4fd40fa8cf808f674f4b0f2ecf068ef34eb60e93ce838e644e2a0e10ce008df04dd70dabcd868d764d600d1fcd0c8cd24cb60ca2cc868c3d4c210c04cbdc8ba54b5f0b3ccb268af54ad90ab0ca5e8a514a380a18ca0b89cb49ac0998c9828930491d08e2c8cc88a4488b0874c85e883c482907fac7e487c547af0798c78287574744072ac71486fb46d906b6c694866346470639c620860145e505c5c5ac858a4577055ac523850d44fa04d4c4be848d445f0430c41a840443f103d7c3c183ae43950375c35f834c43330 else (if i<4 then 0x54003000151b85982f090009202c02d02b503515929c288292020421020c10c1e81c415e25c3d0025487b05e012120409c09e02909d052079099069071083c020a102a09004302007a084c01a2b009ac0902821223b021c05c0617442d804aa1ba1ac2c415c9a81a4d8ec4e840d0e6456130012783001d01b05b00d82601c06209501503900c01303a05e01806d06c01400a09b01a00966402a0208f8d82d50354743713d842181801dc1481e42641a41e820c20826c24010c0802101c609b010454026600e4e840d0e645613001273142de26a29ac060812c827b89422b8102070a1693514d60313d815103915804a025020c1c49d0818024080e05713e0e240c40e130012784084283d04383e83c09060783b83a0095d38515d37a2b838839184484382803182441fc24000401801c1ca81a060444081e0e20fe1124f60ba012040704004904804703e03c02003b2c8009514513a137d3dc061030101c0f700a81e9d09f21b41e8e4f614d0d759900240e13c700b00c01600a020018b0b01aabf00906106226484d753e503d3a22b83d048989bca289d28ae14481826014900e20fe1124f68ba012040726a29a00627bc0120722b0094420420808421021c1f41ec1e442a04004ae2049a8a690189ee2520fc8ae04081c28571024d45341204f712907e45702040e142b00e84d01000d08201484283e04301a83d83c885664830009853502484c015437436986c00834a428205843008080be09e07c078613527074012801100b01604300c00a09b05c85b009543984c202c37435c00c2b935034a41c421010c00e1541eaa2a8ae1b0025402002c0160145cd0b620c01282cc07327487709822b84081102a2060a15c4f83890310384c0049a16216a15824281a8ac94e144149213c13a0a40f20d21320e20f411280408600600e109802c0f456013203f04203d03c29383a0093873874848e000480101831828025023c1fc2441c82aa15e0682e808184f811e51c113014456040781781c80d80b08280c81481604381a80a000607a64426009800e83283380780700800684100b00580d005400932004bc03a1340702080520fa10a0f010c06a0f6b799900e8025e0f4086108112456012040767047126f40a28e46b43c3801803c2cc2f04800499a392111b89d10309ec2f10f901281060e24e840c0120407a07a7c27486d0bc07a300e02f00600507c349015004a00400f810810c0f40f1a4c2150e80254cde8e24e08144f88d6878727c28e08980a22b0723535436435c3693440084c034a2a3a81a9ed15c210280d0b540d51d0dc4f6108606908108408208304306102007107a8218540f4009717415f93514d60304093d84dc4a115c1f850903b429c2542080700341780301b01b410c18802806a81d990004026218c0ea12211e0fe0e4140120c else 0xd07812180180f07b0120121428ad073006161600909426f27428a29080f2060204974073c05c0540d40c05de3b33b202804c2842d9734003c1a421020c10c2a82081eb00681a084024395903e0970f10da00d0dd40f00245754a13ab04083904804703e03c2c803b009020541f06141cc23c1e05416441d8048102a9aaa6a9ed0182528ae81c20501c85c709309108f07d07907ac488498eccec1420400130070370fc8ad30e20e184e84c81e84f84984883c0430ab007a4483e83d8420af8410200e0009ad45503515d03859a2b8418632037e23616502a1d981d0582ce0bc24002565bd0a108b09308f079084ced04004107a5870130745270070081a7b0940dd0dc2b15b03047858303c2bc4b821a01200aa1b6004ac8368264e1b21b01ae1ac1aa12080284140c11f030152c0d3400a06409403c01a2b4070090ae8560ca602623b42c915c3c50303c9c17c13c1080f428c1301000f010c0f981e81a0e4025c08008208608407c07814607a156527072150012d28e09007145541646c442089401f23b400503d3a14743750304224b4616215616615a8ae1e28181e521a10a30f10dd0db0bc1630d70d8055457002104d29a27b81022b0cf02a3067166966414410c37435c13436b02a02c0390384f04c010433c00c2722b509c02a70158161b42441ea0f49d106081d611340d0e74560ee50c904343e80744143d0b0439090009522da28a31237235a36400515a4aa36c03303404804803844a00c238544c9c01fc9ee1742242c010c081010811345601204050ad43d82f0c7009284204185803d303515804810203151b82a201d81d8ad1b51b11ac0ae151004260209c12005580740e40e4578030868ac113030160c077a74a2b0ba0752821b0353dc2e8448048101c2f825a12e0c119607a1350710340e41790690620fa0f610a0f281c2a0024082a0fe4f70ba10611204060bb09981004381a43e44260762b44d81343d43c8000b00392640a80099d3dd45503d15d37d3a04205d050268ae9c21b49d281c1e8c14540c07c07811857214312c012984c46781e41784d41541a84884783e41883c842c0720622b05283d0610a1803c01290009c05b80c054e00a00d0350385b021a620c080024226058a2a1b21082c1256a0b40ae0a80ad0c00b20ba52102f0bd0be456d82882186e86b86c82686d00980760662b09082a84a801865456820944ac33c3343143c40e40b436c0540c44da01d03d0320340ec0604dc00415315c00804dc1c89f31d99d81c42409be02a1ae0f08ad6c0ec569121545148d8106787e89685186e82f85e86d20686b83a02a0ac8014180a808f825514504223605020b14713da21242a610a0fa0f40820ad8ae0f181d81a0ee0e810da0c503703902a05e0bc07501d01b019028c498060d901f0260db015035031856c56040))) else (if i<7 then (if i<6 then 0xec00c0726f02a020290c03009104c0228e0b06601e1591580485bc2181013a40c13d8582e18a0721ba17a06a1b61b02ec10e81820a05202a0028ac3c40000a82a2004026a09a0c28ed40f0170190010c208657f0c4012c10320709127c07a0aa80b86d83d274542b835915854515c3301542584c26a282cc08215605a1b210822501520410566030d64f7100130086054a86b05429a0b10992d4d436435c3684c84c191990760c106c1890701ba0981780e40e90601b681c25905104d0681ac2ed9901b10028ad0263e03fb70a30dd0bd0d90db80540c80d0d7456056113002150104f0fc87e89785185b89682f86e80885e83906102a400403a2b86289586b86c86d09802082a4098010a8dc4b027c2f01f01e81e021b02803821055d49015059804810421f621416c2581881e20ee1501b80201780e81ae15b00e81a17425615c1b01b70028ac0040aa0102a3611340d0e74560ee52fa84b46740e84f81e41541a84283c0bb83da0785f400a2b2640a8009981c836036c1f312067c23c1e41d96440985401034b121fa16e0a20b62560e609a0ea1b63e281cbda026004a4a082214608302608407808785780e07c07a16110a0c21e0872013027c00928e08908f29080d22b0204c2141e33b424c23c1ec04961416c09c1015ec01b41f616e25a18a1e21ba0220e61ac15a1b100100e81a25415217815c0ec1668ac17401226102600751f0014c490020400181665ec196012a85b89586e80886b87386d8014568470b007f0a86d03042044b158048700101ebd98161ac9eca480a810ce16601302513f08240c1127099069090084082c0162b826089009502302482401e81e61200481f05144b05982395c92240a855c218803c04006a1b28ae81e25402a1b42082ec992004025e1e61e503702f01f03902b01701902902702cc48013015035030c56176c0e12b0001517090009a70a070ba0873446426427c1dc24c2b41f42141e021d03003103c1ec2f850c02213010515854004d82cc0260461cc81a100224e1e00a40f2cd4d3508e086152cf7803456c0e112012ea7ca06a07a8e0b3071a2b072454d437058103c3683fc2440095940a0542c1080f681c2880f02ccbbe25802530d90d70025d740e052626f09428a2740432060203c2280541e821b1233b00b41f05996f41d004b013817c12c13c12412011c0f80f20198ac1181080f407810e8180802cc026900ec0ec0c120c570348ad0510921600feb018c02c01007a0642ba070e00ca0435048435c2a14d05884c983161461ba17834281e1ae1b21b68ac2a2004260209cce81060874560e340ec0c012040906e8570a585409802084b22b8660a102a5c3100700e42f00600d436436821d15c4a80504100a05d815532400804cea281082421561b022420cf1470a108b08108309309108f08507 else 0x5a422808446c4a859c021811a0541220681080f30170180f42cc0f810e0c026e2142ac02640e2106086c0f4e8c5740c012040984584801a84283dc76043c0600d08200a83e8300b38850ab0098d38503515d3d85983d22b86e048a6aca1b82c08ae1ae152122050a682a023d68800f10390260bc87c879808012054040ba6f0562d1878a06079344ac3140e40640540d43604c021a01d03203c0740a436c00000315c00854004d444206c0be07205604c17a05203206b00c0830ac0ea0282620260002c00aa81538050078034561b4112c0cc0e086a86b60506984941826826a08f4515d3785893dd030421825418a07017a03206206989181c1ac1b41b02ee0018ac0042a020a50b712d05e89f0c50108910d887c87812288e8128061e0150041188126a89429a27b02000909081022b83f2070b06820c4f844d0350384e18ac816c1e02561501881b80201ae1581b201b01e15c1b43c300000511c8ae0102a2c0d30da05461b0350030924d00fe90cb02d05b02f07884f06200884884783c83e80962b02a020840e40640c405436c36103400315878802065c008540413c3620ac8ac1c89c01c60f21ac9bd061461e1c312f0fc1970a30b70f112c5350c50110bd0721130d880080659112a4f70d68081e4812055a84d43943a84801a84283e83c0bb04308283d8850f00a80090208c14c14602915c3581040e975c0f0580152c4383649bca289d215e15a0ac8ac14a14613c81894d061e18c12307d078c48c0b08e157076591026150040d81b86781180d81580c80b814816818090c0386581a80a813061809800ab44560b0b427425428426c22c1f41e81560042bc24503048303810404c01922055cc20d9ec10c2c28ac1c517581e81802408176170190290310358ec40f0130160c204001300057f0c509a1611b0a84984760583c8038202bd2c8043500fc2f435c36436d1584e84c202428ae9bc2c49ee818210e09809e09209007a1e007808608207c08408d488612156013081d86581b86781581681880a80b81381a0bb8016072f18098002640b09841d3a021838b03d0300481020280a289d31d99d8210a382420321ba0f8819889902f02103888419208700ec0f056c5687c87a8780c216087215001330a404e08c04f05704805604703e04203d03c043407a2b04c04b05f03ba066070040200a1009cc0dc07c0ac0640a409c0b40c40d40505dc01c03b03804c05b03315848400404a2b404058620f60f301581408035cb8e1f810d220a0f30cf02f0210390170290348ec08680745701902d01480d0230018021a6013685b87886289585786ea06a0740785486d06140922b4478010f08040a898479471158418448101a07619e07202e03205a06206a0282ed89181c3ce0018ac2a020a218c12309107d07840c45708e15707659102615004) else (if i<8 then 0xc0760782b4000a8386540ec1843383fc1cc1d41340a40d40c601d03c04c4ac09c4d84d81040424814801500485822b400400f0b218142c211e00caf410e081108700240e8ad041012608f0ab62b4200430b0303fc22c0ac23c0c603b03c1840985824801022b404b90258ac0a900c0802a0c5885865840ff0ac40c45652016094048002060bb6078090b03860860432c08c0ac0840a40540d40c33b15fc09c0b600c04804830a10406857400582b824108181d0ea15900d0042c1217011e08780740e40cc56840160989580883986c86d0a880983a40929002a0b045682607f795a223041040a0f222c0a821815201e00e03041810122004859c50258ac23e0980800a82a0e56416213205500204109013016090af0ae0ad0ac0ab81e84a84584984884783dc00a0780740629002a809009020846244803c33d840b3550300488b0729c0fe0e61b011c0f40f000caf402408140ad0d64f745754a13a05478038000090900b10898268094564a02d15d3843693a03d08b1e1e49bca289d215e1580240828ac2421e206481a130b442c2103b0370ce90b01702b02702d015002013034c0e1e6c564c9000151286544b86781744d81c8150828140bb43e43c62b41e81a44243d800043607a640b3009bc0b405084406059821c4ac4680484daab798160f0c24a4e0e810ce8dc40d056c568d68da8d801285400f0a9090803028150f26f28a0a96050900a008486e41827b83e206604d815401c00600c0383fd0385884482b404b281e8ac2cca2a1b020cd09f08507d07816004080f85645707b40c1e1072086e05405905727b86b86c05d89d2a586629084b02a6c2642fc27864c2141ec1f41e303d15844021c1c854004beae612611e10b1da0f081e0f4082024024286054bbe00e2582c220518480424f604103a5a903c0549083a7b0b0043071606a0705d009020522640e40a856a1e40330322121ea1f322086021859c04004c212612211e10a0fa0f201d81c0260f424181a02428600e0ea04d15a08270fd0b70f112d07712b0c50dd0af0bd0ad0d70db0d940c0410a80c3003456812055008151844c85b89689586283980885e86c43e09843c0a820622b10e44844743d403409290020bc3f014428816c2dc4ac0442f436848201a00503811812c4b43141cc35c36010515c1504c204c00e8bea19a06e19e05d21605604e02907d1660682ed1558ad81e02499200044e814212140d07d07911857314312c012a084083043a0707aa0662b0090204c1413dc35854e02b0284f40081042710396620c349ef0901e91550591b1108225012e0a20b605e0c40dc01140c12a0bc0d60db80c04045611200380005508e15152ef29305005f8852640458578560470420a103cc00c072e304803d0a80a30900094392060abc80680580a00500d04d80780600c17a9 else (if i<9 then 0x112a29308fc0343b04362b2d10b0414d302e0101005804c0541cc08bbe23621517c9911360ed12616615911d0f8be42a02c0a40243000a4ca2826d28c28402617512100d0e481bd10a92c85f0bf076142012040150930142d62b43a0a940142002a0b04980159246a2a22ba2cc04435a2b43617c855e0020042f04d85414804822ec23c00915dc3fcafe05002618826e1341842c121fa53512d05f01089087ac0c8121c288ec561d218c80605404118438036074568208093439e00200115b03e0103f8542205410c81d10826c0240800a83ed25f313a83e8b3087006c0e52040e1508ba457012d08f42062b29a43ac024034010b0486920ba09a05303004865c102228e10210408081981c0261202ac2c1509506112d05b03d0100ff04d0910741a61600540128ad04102bf28e80886b0ae80908208986c20680184722b07f717bc17c04413224221201803a04870810303015055b99d8080bbe05611c0242842ad05ec5ea5bc5641970ca51d02903503101501b02b02611302c40d0120121210408401a700045792922932bd28a07f09004382022b2072060b0640ba4ac0540b054603303065c06c00200841311281fe1582b82410808ad81d00c2c145e2586d68d901678018064568130acc0e520c48d87841c86b86c4610ab0a8400c07a076072bf0612900200b080109822b082ac2342405c401810404b03004922055aa0e42c00a802611e04caf608101dc59085e811091012012150c0d006040156c2d188d29a495854408857859c00c03a06a2b2b52c843a46c89080985d80402aaa3283f84860095fa09a00303a0485828bb607902109a1200808ac0251b00a82402842ada85a0fe84d0ac15c120456874840c0e802160c2648140900092bf86209b84d0610b05076175c14410869a12015014c13058010400c0ec0f16a503c20f02ac080ae42c03582de28828623225810d9456c5701240e012040150743b815a0745f0a10090200a84423420c018103030218559cafc91221612e1320ee1161582a00820188ac18105834c0242843aa41d309b08a81102a8748728d908e8db086150c0cc5702710b01204122b443081781181542f81481380a81ac06a2b80943a60680d4010ae4208000cba86a85714804883d03fc05c36c1e93a044ac9902c20002ec2a0a04040d40ec0e4570121607a0760780922b0200a8306584140443660106291586d815055a881823c9ec2dc2c0b0528d8456041012156684302a80120745628807f809416a15fc4b414416947410c04435c13600044c1d436103404a04c16055857048601050915c00e49ec2e02a431810c20e108a2a1b1060225618c51c15d01210612102d0d9084514112b2d186045984345560645d62b22b2078095c0480484a010054142c40ab0080802c02602a0f14604108216008615660cb082 else 0x246a0ec4b43c20e20a209886435a0d030c1530301020495fc1d43601514800487005585804820011584d850c00a027c2dc3543801c823c1c60f09be1ad06022570f112b0748158ec130c0e81b0ae82c1e01661510a90768004561600c214300300968174590f330c8004550bb0b062b80806109b809695c96896414d13d854c1e810515c21057c23078103103821c22560e901081981c2ec02604e0020042c16e14dbc157807086086602c5703016ea2fa0fa48545989583a85e0a8290c0362b80945581a81350c30c0090bb264800801b400903b15a04870015202054209d215e158354380448a2810c18217881a17cad50628ade82f05e82a8268288308148350d980707580c81a150800197028e843803206a0760707f22b8094a2620f42da27c0ac3141c84da02303503b15a2fc4a8508151480048104cb452351650ee02217a12034d8198ad1552400240aa081e5d711909f0765144e90ac0541600414571490be1505201aa60413040c08740826078000bb0a8287e968c1793d87020496441d436315a0c04781534ac8afe1ac37d02900000301a819818bd42261b20040808ac20a213108640f012040150620785da07290409283fc2b20191587db03a048582217a1ae1b02a02402082dc3c02c106200611c23db0f10108068121310a80401e080da6058010200b18480980b0415e847d15b15810103821858202ce0248ac0240802a0c0ff0ac15c121806456812c0e16092d182882182d27b0e00a90ab090c0340983a82030110c02009841802a9c2620bc22a09a0541f63b53b021b03a06a0b45185803b850c1c804c8a3a1271d99d824091008039611cbbe056258285a21060f0170290341368490120121d303052101c16616108b12a5eb00132bd29307f847607009839848a0722b8032060200b0714542b93dc2b06505491587001004ec25a0c01504c3a18a0560690f42ec2a18ac20a05110a8182cc2c03a402408211061aa15c18c10702d0d8515084))))
def x511l12 : Packing := (381,3,9,0,0,16,0,x511d12)
def x511h12 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x401f7c028a03a5e173d990b613c0c93280aa78255e148401e3a0fb73bad415f5044981707015e409880489c08f00000c18038132a0e560304ee8308186a53bf859bad7a4820b213900124e07c5351481576198b80dfd046de0dca347a41584bafd01756a301922568046806300000e139820000012081c003004000344000000058080000021818000050000002120c02200400000034101000008a000400000005000000005000c0130004008020108200000a400001800a040050000c00020012700042001a1c0810600000040000c0000c830004b050000380000001000380860204f80120470100053800a1ce0000000140000300000800300000001600000000001f003c001040c00000000870000002000c39e00000020000004000c080000000108000830800000100408000140040002200000000000080010000002080000000000030a0000000000000400100040000000200860c000070e043801e10302020008702009000000017000088316500000000000000000000040000638003000000000181800000800120000700040010404200080800100002020c2c092000068000003870008000080000024046010014489000008000000000000008040000000780000008d030020002003000004000000004006000000100004000c00000000000000040040600102004000202045000200001040000000000000a0818302000010c0000000080000014010040400000000000000007060040000000001628100040000500003800000000000048000000001800000160000000000170620003002000000000000600000000008018000020004000000850102002800000080000010600200010000000000018006000010204003000000000000010000002020010500201810008380000000104000000604001001010400000020000080000400004000000000000000c002000038000000000000001000000000040000e14000002c10000042000400180000000000000000000000060000002000000000100160400302000000018005000000000100000028000000000302000000018200000008000080090008000000c0000008002020410700001800210007020000000001830200080000818000000010000002000008a00040010008000020038002000000000004020000100040010000000000000004040000000004020008000000000034081000008002080000004003020000202004000000000020400008040000000181000000000000800e04001000008000000000000000000c00004002800000002020400400000000008000080000000300000000000001858002000800018000000000000000000200001080410000180020004000000000002000000000001040000000042800010002000000000000081200000 else 0xe1e089b0319012600001a0cce0182000040025932ecbaf7e08648051a00d984d3017f0000060f200000000063d37311ad80788091985a940ace82320160fa2f4e0284c201e090c851e602c7055ba10ca82afa164102c0e130d99660b4c80207e0d1d8569c14c53acc6e9cedd0c68ec000000000000000000780720000795620e7710440a12800000000000000000000000000073848009d1047fe155183e7cb78bbdb3ed2072c2fe14af834ea02334807616300000a0f62b99a002a38425a969402505740980c0c07b10599214e001a9010a981eb2135b8573e0dad8a866c3af00a5c1343043e00005a286000000001e0bc800000000105ec00000000000001b9ebe07080000000040136000000313e1118851d203e000006b538b2760000000000000783b5c01c704b6e004401a0f2097355c00fc9035dc0ce5843800004021000001baf20000602a1a0d8dd10ba05ad03d60080f021360b988149509968146014518259003290345013dd03ce2e42000000000585e5e0ec6805a00000000000001052560225016352c21823120c2fc36040a5c009f60c7c3ca1356a081afc0244b52600f1f0972611e0023f2e221a176a89c0054400e490385c1320853aa11848566a10750188b2f6c00c38122a93d2525918110e0ca0000000003b273c06da80fa000000000801d68388e00e002db207bc858b2103f029536424053c216ff05f1801983901203b605cbe01730492c07500000000000000e17a800004037681ce416c0000000002b8720000482d4e0f50000180d4904a4a0a100000000000001601d800000000080124083788c6213f384c7c10a003a7610b8059660f15c532c0a2b8042013bdcbe2ec687057761384bccd8f52800000000000002031905a1209a8b50bc0931b4a50f3170314013ae83700000201420000380166ccf00000000078c3de0ef80000000000000000000000a05b0000040d298500000000000e09000000e04aa3adc000000000e07615c5f403680001077b0000000000000000000000100534032200006000de363e85576c837849ec46b55d10a08963dc0403780001d2440000081246804960a6f8465e142404bc2859c82d7200163cbf40cea83bb607a000e7214c8cd2f40e5904b2a0f4fa47ca419b0063c007b02040349338dfc01a401a3a0517482ec17ca38cfa038f80cda02fa8156ee09904c54043183ea4d53dc9efa069802a3a13a584fa202648298a1160b49b456f9004e0000300acc01ef05d60000705dda011002d280e7705ade0c70000000006825b4f102024a000000000a0a3e099c802f5048da0bc00001211c503e400000000000000000000007041600007837b81725391c614f88a5c9250ba495805d80552e03c481ca611ba85ef80df6b3600000003ca0077e01b4c42980001409380000809ce82be000) else (if i<3 then 0x21085d1e16f48481e0915835f202068405400c580414109cac3d2121f9425e0564045b0348f04d8a03a80a180042d02ca610c2832b4006f8374601f002f481050000000006830dc141abdcd923ed811c804f2852c000000000000000001813688537a001a38d8a05b800008137a0166006c9809bc11a00001e0ab00000000000000c540800007212d018e241b6858e0000000008074e2275210000000d21e00000000d784dc612a88ce9a16dc818580d0f02c4a0bdc0350e03168302af7380000a0e019de5409c284ce0e52903dfc0b1d85b40840280000000383dc0000204200006000000000501aa00000000000000000000003046200000000001028000020ead82fe4012c4d97ae7c100d6f1488acee007758386e021e44a6000000001212b7847a440ab95f840055049560e6181bd52cc28406e16ef844d00ea581db004a201084f6e4056ea13b50364aeade857860998ab296ea0804e30f74d84759279b806f806f800002144ac94400fd60368005c03a2b2062a037621697044aa09a6c88b216ab84af0546b8359c023f82ea616bf34e62064d011b200eb8288c05964bf4614a6029ea0cbe82e4608023d0b816cb0216203bd8021c0db5b983cef19bdc460f46851a609e8854f40cfd857500c4634cc0e4e184532159101526efb8802c009b104a281761c8592d2fd01d620fa50584609f0ccd100e68832cee8128175c08d385f76b78780f6c08b4856200000000192e580000c88600001a13f80001a08aa02b1f29f00000c01b5850240b40000177750000080a980000c15c00000000000456b27300000000000001612980000803500000407e00001600f800010150201b0000000001811478b86601af4a7a00000000000000000020fc5828320b6202b4e179eca3a0000081b9d26f783ffe171b04f4a0c3f0434000018594005e480c8c10ec8118826a709aa0125980ff60e820519c142d85f8409723d134027704d5c0aea8542c00aa8229a04500001a0bed00b220e4084b8069d18101e07d4852ee092782dce10208057a0be2827ea070081068d7c0000180e2a83c27032a019400001019a00d06812e2016602cfc055705e381675cd91e0d524b22374ce8940200bac34a80798492780c2003fda141283e240b88000000006000aa0b32c8e200007043de901644b2000000000000000000000000000000000001211990278000000000126dc839e0000000000000000000053f02de4000c02c9a35dc813e000073a580000300b800004017b007900001f1730000000000c9bba10b300fcad35580d0af5743c03a156281c7a8469049a000000001a08700000000000000e06ea01fda149800000000582222eec88281c095c80b5a0259c97140949056b00c0200ce005fd3355015780141607178131012d648100049e814a017878264e8bfc81 else 0x51bd1e00a501cdc0c6f815180f6e8b4b0168b803de161b84f9c034881fe811d9d5bf351e9040362c128190c107cba1bc154020f5a003a8418a169f036680aaa0168c0868000180180000000007a9de000000001a12f8000040d580103e14580001a0982d02e611748379b178985100153685d397469c8b7c065d80e4e06640324c05f6835b2013482e0c04d0cc692ac11838e00ee038cdad5c884a98777c021420bb3825f6160480aa20cf68349c10360321c04b404cbe120f383340f80ba4c0009b0326816210238a067800000000000000000082b68817e806553296b98a204ee09a480155bbf9b0958029c8130082ee011c8bc39a0c1805c3e70c5a0de000000000437180001207e80001427b0000160b08847dc0747011ee12eb009480a488b46c17a78092204150534d20f0828d6151805cda01fa801de12700000f2bb90277ef06e826ec0572029140d308022c40d482a494e9a234ea056e00e9807200000000000001c043b05c4000000000c0827046bef7420522000000001e15f80000000000000ed7400000e05cf3dc9812c1b89800004848eeecd080b600001850c9413800008045c03ac0d14100d80000000000000283f980cc30a81c06b3050fc083d83a380fea83f6608da386e0000783600000403b78b59600e0000000001017ee0a580000000000000502fcee4a03c11af7cf00ba215e800000000403ee0000180ae000072387ccd1800000177985486d1a80000acd3ebb5400005836e0104f85b9684d00001ab46800018117c81f20000000000000781a5406763abc322780000603d00000a0f310a4b20af20383217f9822000000000000000000002d22812352a3a0121c08ba00a660cd9813800000018083508bb69e106aa4a200c588009217d48484a03c80001ef23803bc0000000004164d82e8e0448805fa23c6540540ec8000000003a2500b39700338edb384cd376f484426108e03afac3938334808e905da202290436402080000611145ca768e900000e0ae14398c11540052e0f01059e8113d8160883dcd9f6213cb054b20e35041000a1b856c6087809b3c0))
def x511d11 (i : Nat) : Nat := (if i<7 then (if i<3 then (if i<1 then 0x648955833fecab40192c1bbf698a254d60febaa4a9c66b07fd5314c1815833fe54b42a9ac1fbe5496380160edfaa4b2d32b057fdb12a553583df6a9304c0ac1fbd5496160560cffb52d1aa4b07ef97358d805833fe98554c92c1ff654d3044160cffb72d2864b05feebb54920582ffd5daa7002c15ff6d52065560ffe220d12a2b057febb54994583bdeaa324c22c1fb758d3150960aff972d2304b0777db954a55582bfed912ac9ac19ff549a94c960ebfb72a9ceeb04ffebb68d50583bf711264caac13ff6c9a354160cffb44a9328b067fd526899858377ed3340a9ac1fbe5c16360160e7fb72c1306b04ffdb5689805833feb9b44cc2c1fbe6dd8059160dff34ed1b00b07ddd7354d74583f7c982ca882c17fe6d53044160edfaa4b1b24b077f5b954a11582bfedcb46a92c1cff54993a2160ffe2a2d1a20b057fdb5249935827fed9d54a92c15ff6c5935c160eefaa4c9caab07afd5258e885837fcdd300b8ac19ff6a4a254d609ffb74b9a40b07eed5260964582bfe5cb4ac12c17fe6d53060160bfbb6a99466b04ffdb568d1058377ed3348a9ac11ff2e95165d60ddeb42b2864b07bf13160181583f37112c72aac11ff2e99354560cdfacad1532b067be9969032583fa7114ab19ac11ff6c8a9955608ffb6454a82b047fcba54d925833fadcb42192c11ff2e99295560bdb974b2c66b047fcba60997582beed915319ac1fb54c56348560e7eaa2cc302b067bd9569032582bbe5d3272aac1ddb88993955608ffb6454aa6b067bda464c525823fed9554caac1fbc5456344160c7fb72d4064b0577db22a6555831ff4cb50192c15f72e9928cd60ef9c44cac66b07ef110699515833bf4cb4a192c19bf594a954d60cbfd32d3864b057edb32a622582f3e5d2c72aac1fb3889658cd60e7f30ac9b00b067bca950941582bee5d32b19ac15fb6d4a988960af7972a0b08b047fcba656335823fed9953112c19ef69299149608ffb6755324b07f7152545105823feda952992c15fd6c432655608ff974c9caab073f531661815823fed99532aac11ff2e93166160f77300a0b08b047fdb82a55258277e5d2cb19ac11ff6caaa64d608ff97498b2eb077ce22a66335833fd4cb40192c1dd7955928cd60dcfb6cd2864b067f995680325835fcd8350192c19bf58da2a6560eebc674ccaab047fdb32a54158337eb1952a9ac1ebd6096160560f5f308b2b00b06ebda458c525833fc54b00a0ac11ff6d4a9889609df974b1caab06ef96568032583df8c0aa2c02c11ff6d4a98cd608ffb6454c66b0776e22a66555833bedcb4a192c19fda65a10c960aefb6654caab066fda62a553582beeda95319ac1baf595a40c9609bfb6f552a4b047fdb32a5525823fe5d2a2cc2c11ef6d2aa64d60fce2a2b2a20b047f5b1aa992583d5cc02c8c22c1ebc6016160560 else (if i<2 then 0xc17fb6d53288960ffe220d1aa2b077f55164d715833fe54b4ea9ac15ff6e4a354960fd7aa4b1c88b04ffdba61d20583f76a9304b0ac1bbf69d6360160f9fae0b1ae2b04ffebb68985583f3ea934ca8ac1df7649534c160fd7acaa1282b067fd5268d91583bfcb8326902c1df76e5538cd60b7fb66a9510b07bf9b360185583faea9946a92c17fe6d5a360160ddfb44d32a2b077dd3028d92583bf6a9144caac15ffaed53a6560cffb72d130ab05efdb628d52583f6edb2a719ac1df754a998cd60cffae654aa6b05f7ebb54951583bfca9326c02c19ff2e5a261560bff576d3b00b067fdb96952158377ed3554a9ac1dfd485a94c560b7fd76a9510b077ed53a6622583f7c982c6c02c1dbf5c16364960feeaa4a9c22b067fda969153583fbca9aa5002c1dfe6e55380160eefaa4a8b30b067fda364d715833fed4b42a92c1fdd5495160560e7fb72a9510b07edd6368131582fdeda144a9ac1f7e6dd805c5609ffb61552a6b077ed32a6622582f7edab04b22c17bf6c56550960affb72a9a84b05feebb54e22582f7ed8aa4b22c1bbf6896354160fdf346b2a20b07fd9314c170583f7ca92c6882c1ddf5495365160fdea62b2a42b057febb54a995833fe5cb46b8ac1f3f6d9539dd60e7fb0ed4b04b07e7d5258e555833fed4b44a9ac1efe4c18060560eefcaad4a64b05ff5b254e11582bfed92a2cc2c19ff695a94c960bf7b66a9488b07ebd42595435833fed2d32992c17feaeda260160affb64a9b22b07fd9304c580582bff5daa6c8ac1cff54998605609ff974b9b24b06efda25955058377eb2b40192c1bbf699a254d60fdf284b2b00b0777d52a66555827fedd2e2c02c13ff2e95348160fdf2a4c02c2b07fb98050941583efcb8260b8ac1fbe58d205c160dff260d1300b07df9705c580583f7adb26290ac1f7e69d73601609ffd76d2a42b077f97064d8058377ea9346b0ac17feaed52441609ff974a9c44b05efebb54961583bf6dcaa5112c1fdb54d52889609ff974a9262b07bf9b760184583b7eaa2c6c92c1fb74c1a64c560bfbb6a98a60b04ffdb368985583bfca9327002c1bbf69563249609ffb61552a4b07bf58254581582ffcdaa40c02c19ff2e5a354560eefaa6c94aab067fdb969532582ffcd8a60b82c19ff4c2aa65560dfdaa4d1300b05ff9b568d10583ff4a9344c02c1dfb54ca988960cffb24d2a86b07edd654c5305827ff5db4a992c1dfb54a9988960cff972d1aeab077edb954982583f76db2a7112c17bf6c5635c160bdfb64a9ac2b07bf5814c582582ffcdd2a4882c1dfb6e55388960cffb454c8a6b06efeaa595325833fed1a60caac15ffaed5364960bff576a9400b07edd3259633583f7cd1acac02c13ff6e9305c560cffb4ad4b04b0777e994ca55583bfa58b52a92c1dbf54963a6560cffb4454aa6b067fda2 else 0xa4a9d32b057fdb728d92583bfab8aa2cc2c1fbd58d515c560efdb72a9240b04ffcba54a335833fed4b48c12c13ff6e95244160bff368d3b00b06ff5b568432582bfeda944c9ac1bbf6896325560eff324982e0b067fd52aa993582bff5daa4c8ac1bbf6d9a50c960eefaa4d4aa6b05fdebb54d30582ffcd9aa4c02c1efe5498060560cff972d2a42b073fd826a583583f7cd9b00b0ac17fe6e1205c160dfd944d12a6b077f9a764d80582f7edab04b0ac1dfb5499348160bdfd76a9ac2b05fdcba54a335833ff4cb46292c1bfe68d805c5609ffb63552a6b07ef9b760161583beeb9952a9ac1efe601a261560f7f300a9308b077f97364d80583fb6a9144a9ac1ddf548a954d60cffae755324b05fedb354982583afeb8326b8ac17fe6c18748160fbf2e0982e6b057fdb969152582bff5db52a92c1bdf549a354560affb66a9330b07ddd535cd725833fed4b48a92c19ff6a6aa54960befd76994aab06efda558d2158377ed2aca492c1fbe4c16548160bfed76a9422b07ebd5259184582efedb946902c1e7f61d825c560cffd3355264b07f795254d1058377ed1aca882c17fe6c13160160ddfb4cd3aa6b05efebb549645837ee51b46a92c13ff6caaa54d60affd76a9326b07ef9b654e00583bbedcaa72aac17fe6c95344160cffb53552a6b0777d53a6655583fec902a6982c1dfe4c120655609ffd76d12a0b06dfda75c5805837fcd1b44c02c19ff6899261160cffb46c92a0b07ef9a758d805833fed4946a92c1faf6d95391160eefaa4c9aa2b077f93064980583b7e982c6c92c17fb2e95388960edfacaa9330b05ff9b054910582bfedcb42a92c1bbf699a04c560cff973552a4b07f3d5354a44582ffd5daa6882c15ffaed5266160bff576a9300b067fd70aa9935833fed2d32192c1df7548a98cd60cffb52d42a4b077bdb954a44583f3ea92a6b22c1fd7549534c160bfbd76a9466b076fd5258d94582bfed92a6ca2c1efd4c58060560cff972d2a64b06efda769931583bee9953319ac13ff2e95264d60dbfb6f552a4b07ef95258d80583fb6a9aa4902c1efe6cd8060560fcfaa4b1aa2b057fdb22a5535833fed3b5298ac17feaeda360160cffb52d3aa6b05efdb254d645827fedd2a690ac13ffaeda3545609ffb71552a4b077f9b954a00582ffb5daa708ac15ff2e95264d60bf7d76a9488b04ffdba60951582ffcdd262c02c1df76e5528cd60bbfb6f552a4b057fdb96a152583beea9d3319ac1efb5498260d60efdaa49032ab07e7d5269953583f3edb2a72aac1def6e55391160affb66c92e0b04ffdb3689805833fed2b2690ac1bbf69d634c1609ffb63552a4b07ebd6550974583f7c982cac02c1fb76d9534c160bff374b9b00b077bd9255174583b7eb9ac6c92c19ff5c2aa64960bff366a9400b07bf9b260185582ffcd92a2c02)) else (if i<5 then (if i<4 then 0x1582ffed9aa4ca2c1dff5492065560fff2a4d1b00b077fd7364d20582ffed92a6982c1bff6898254560bffd76d2a64b07efd5258d20582ffed9aa4902c1fbfaed5358560fdfae6b1aa2b07fdd524c530583f7eb2b48c12c17ffaed5344160fff300d0262b07ff910aa953583ffaa8b04b8ac1dff2c953a6560bffb64a9a20b06ffd5268d10583f7ea92c6982c17ffaeda060960fdfac6a12e2b07efd654c173583bfea9324c02c1dff64da254560fdfb6ca9ae4b077fd524c195583bfeb9a62cc2c1bff695824c160effaa498b30b077fd9269153583ffc88340a92c17ff6cd5260960fdfac6d3b00b05ffdb354993583bff4caa6992c1ffe54d3048160fff260d0304b077fd526a583583bfea92a6c8ac1bff685305cd60ffdaa4d0304b077fd9254953583bfeb9b24c22c17ffaed528cd60fff2a498b00b07efcba549635837fe51b4a902c1dff646aa54960bffb62a9260b077fd52a6633582ffed9ae2c02c1fbf5496548160bffd76a9326b07efdb654e22583bfea9d33112c1dff646aa54d60fff30098a84b07efd6468d52582fff5daa7112c1ffe4c15260160eff974a9326b07ff93060920583f7eb0b50a92c1bff5cda354560bffb7051a40b05ffebb54981583ffca9260882c1fdf2cd5254560fff16690300b07bfdb560983583fee982a698ac1fbf5496344160bffb66d2b04b06ffda74c580583ffca9344c02c1fbf58da054960bffd76a9328b07ff9b254d10582ffed9aa8c92c1fef5514264960f7fb0ed0304b077fcb354998582fff5daa4982c1fbf591a854960fff2a4d1a20b07fed5260941583f7ea9ac6902c1eff6d58260560bffd76a9220b077fd5254d94583bfec9b42a92c1dffa65a54c960fefaa4a9a42b05ffdb128d52583ff6a9262c12c1fbf5cd6360160fdfb6ca9a60b06ffd5268980583bfed92a6ca2c1ffb5494264960fdfb64a9ac8b077fd5264984583f7eb1aa4c2ac1dff6cd5264560effaa4d4a62b07fdd304c582583ffcd9aa4882c1dff5499348160bffb6ad0304b07efd7359520583f7ea92ca982c17ff6e95260d60fdfaa4b1b00b05efebb54963583e7eb9ac6b82c1efe6c98061160fef2a4a8b00b05ff9b768980583f76a92ca902c1ffc4c58050560befd76a92a6b07ebd5259141582bfeda924caac13ffaeda260160ffd2a490300b077ed526a5825833fe54ae6a0ac1faf5955461160bfdd76a9304b0777d5254d91583dfcc0262c22c1ff64c0a348160fdf240b1a60b0777db954951583f3ea92a6b0ac15ffaed3265560fedaa4c12a2b05ff9b568980583ff4982a4902c1bfe69da260160cff973552a6b0777d536a5525833fed1326a82c1d7f54d929dd60bff366d1300b07eed5258d20583f7c502a4b1ac1aff6c1a80c960f7f300b8b08b077f95364a00583f7ca9300b22c1bdf54aaa54d60eefa else 0xc260b800ada0a4e0974088007c006cc05d80462029e01760001ffe69d3160160fff360c12e0b07ff9824c170582ffed92a698ac1ffe5498050560bffd76a9a42b05ffdb55cd92583bfea9326882c1bff68d535c560effb27552a4b07fbd7155184583bfec9554a9ac1ffe4c57360160effaa6c9a40b05ffdb550992583efec3a60b8ac1ffe4c18748160fefaa8a9ae2b05ffdb354991583ff6a9146902c1bff695a060960bffb6051aa4b07efd654c542583f7eb1b4a90ac1dff64d515cd60effb26d02a4b07efd634c171583dfec1260c0ac1fbf58d5254560fbfae0b9b26b07efd6369520583ff6982a4c12c1fbf58da154960ff7aa4a0b08b07ff95260142583f7edb2a6902c1dff64d5254560bffb64a9a42b05ffebb69582583bfea9326c02c17ff6c1524c560effb72a9220b07efd6468552582ffed82a4c0ac17ff6c55261160ffba60512a6b077fd9268153583dfea9300c0ac1ffe4c13160160fff34698b00b07ff9ba4c580583bfea9b24ba2c17ff6c4a254d60fdfaa498acab07ff95248180583ffc88340a9ac1fbf595314c160effae0d4b04b077fdb954983583fbea92a698ac1dff6e5524c160effaa69032ab077fe9954932583f7ea9aca902c1fbf6d58258560dff946d0aa4b05ffdb74c584582ffed9b40c12c1dff4c1a960960fbfae0a9ae2b05ffdb828d52583efeb9b4ec02c1fbf6d58259160bffd76a9308b07f7d53549205837fed2b48c12c1dff6c95364560eff964a9b22b07dfd875cd41582ffedab04a0ac17ff6c13160960fefaa4c12a2b07efd7358d20583bfeca554a92c1dff5493064960fdfac6d22a4b05ffdb354983582ffed9aa4c92c1dff6cd5265160fbfae6c3a40b07fecb354920583bfec9aa4c2ac1fbf549a64c560eff966a9532b05ffdb354981583efeb9ae0c92c1ffd5493160560dffb4a98b04b05ffebb54931582fff5daa6902c1fdf549534c160effb26d2a42b077fd7354598583efeb8b0ea12c1ffe4c15248160fdfacad0262b07ff5314c181583ff6a9304902c17ff6c95350960fff300b9a82b07ff9704c580583efeb8304b8ac1eff5498260560fdfb66a92c2b07efd63aa952583fdea0b0ea12c17ff6d53060560dff946d42a4b07ff9204c173583f7eb1b44a8ac1fdf5495350960fff374a9220b07efdb654d42583bfeb9b26c02c1bff28da054960bffd76a9306b05ffebb54991583fdea9284a0ac17ff6d5824c160dffb74c12a2b07ff98069d31583ffcdd2a6882c1fdf5495344160eff966a9322b05ffdb028953583bfe90352a9ac1fbf6c95358560f7fb0ec1282b07efd524c564583ff6a9348c12c1ffe4c5305c160fff300982e6b07bfd8769182582ffeda946902c1dff4c0a265560fdfb6ca9a64b05ffebb54943583bfedba62cc2c17ffaed5250560dff944d02a6b07fdd7354d3) else (if i<6 then 0x92d38d5384937bd374b370d3681362935b7357934b9344733d5334932bd326531f3319b315d30d1305f2fd32ef92d832d2b2c9f2c2d2bbb2b152af12a7f2a27296728db284f277526b5269125eb251124ed246123ef2397233f22cd224122032191213920c720071f951f231eb11e8d1e011d5b1ce91c431c1f1bc71b211a9519d5194918a317fd177116e5160b1531148b13e512f111c9117110e510a710010f5b0ee90e770e050d790d6f0cc90c090b7d0ad70a7f0a0d096708f5084f07dd0737060f05b705ad053b047b03ef036302d7014700d50048fff0ff16fe22fd7cfcf0fc98fbf2fb9afb0efab6fa44f99ef8f8f886f82ef788f6fcf63cf57cf572f4b2f3d8f39af342f29cf1f6f19ef12cf0baf02eef88ef16ee3ced96ecd6ec30ebd8eb4ceac0ea00e9a8e91ce890e81ee778e720e6e2e656e5b0e53ee4b2e40ce3cee328e2eae292e23ae1e2e170e0cae03edfccdf26decede5cddd0dcf6dc9edc2cdba0dae0da20d994d8d4d862d7f0d764d6a4d64cd5f4d582d52ad49ed412d3a0d2fad288d230d122d096d00acf98cf40ceb4ce28cd68cbf2cb4ccaf4ca4ec9c2c91cc890c7d0c75ec6ecc67ac5d4c562c4d6c3e2c356c2cac272c1b2c10cc032bf0abe64be0cbd80bd0ebc4ebbdcbb9ebb2cba6cba62b9f0b94ab8f2b8b4b842b7d0b744b6d2b660b5eeb5b0b4f0b464b3beb366b2dab24eb1f6b19eb0aaaf9caf5eaeecaeaeae70ae32ad72ad00ac8eac1cab76aa68a9c2a936a8dea81ea792a706a6aea622a5b0a50aa498a40ca39aa2f4a234a1a8a150a0dea0a09fe09f3a9ee29e709de49d3e9ccc9c749c029b769ad09a44996a98769804977897209660955294fa945493c892ee927c920a914a90be90328fa68ee68e748e028d908cea8c448bb88b7a8b568a9689f0896488d8888087c0873486a8863685c4853884e0846e83c8835682b0823e8198810c80b47ff47f687e747e1c7d907d047cac7c067b7a7b087a967a3e79cc7974790277f4779c775e76b8762c756c751474bc747e73f27380730e724e722a719e7146710870b070246f306e8a6de46d3e6c7e6c0c6bb46b766b1e6a926a0668de685267c66754671666566596653e64986440639a62f46234618e60805ff45f4e5ea85de85d425c685ba85b1c5a765a5259ac5920586057ba56ac56065594553c549653d6531652a451fe51725100505a4f804eda4dcc4c704bca4b0a4a4a49be48fe4824462c453844ac43ec434642d44248413a3fde3f383e923dec3cde3c523adc39ce38f4386837dc373636aa356834dc343633aa3304325e31b830c42f822edc2e502d5c2c9c2bc22b50295827c8273c269625d624ae23d422e021d2212c20a01edc1e6a1e121d861ce01c061b601a6c19ac195417de1752165e151c14aa1334124011b410da0f7e0ea40db00d580cb20 else 0xec0400ff329c016786d03d0184a05203c82640d207a04182b805782604201c404008204803f81c00098802705e0c7056914f84712390c12927b9158455102534731b887ca7453d9210d26a93d82418032079158329102893549ee40f22b0542204c11695fc9ec1b922bc1f844c1d409b481e810807142b801c0120203a9d08f44911831812384f047e1e307802b069e0f80540900148380040e529a9c00860200889401504281e810e07c0b336f50e80129007807419486d436216c01409b93220042260096281945602a83b9005341c831417b08583ec1e82a3079a0700482ec1600207028012208fc05026d4de0b391580812a6fc37281810809b2c9aa4f602a603481e4560a8440a10340bb22110f008703921f10f4156c8505802a0012d05049c00fe02b059a9d022c020401ca4f785903fe02c0c208907000812a8e23891c8726a93dc81e4560ca4409a4f720704083751285937a9ec12180c9030280c0d906c02a408608f0889a4e0405c05a9d012259354a6a4f6c0604a48ae40e8814700380e26f148700d0ad10414702c120e707480241220e00480080e0f2a21010c01343da1e50e41920bb481800ee05203c82100e3c04015002520a3020012408e04201e810c07c03cd640082076839004b813809e04e80a40a407904c81a4106071e01010c0f4084e00e8ac013100e020801801487c00280356f673200a8012b007020802904281f40f008601a81edb7a10ae6421d0025da6a5a681a5dba583a4f7a49fa447a3bba2e1a255a1c9a109a0b1a0259fcd9f759f1d9ec59e879dfb9d899d4b9ca59c339bc19b4f9add9a6b99df99a19963990b9899980d97b5974396d1967995ed956194ef947d942593999327929b920f919d914590ed90958fd58f498ebd8e4b8df38d9b8d438c838c2b8b858b138a8789fb89bd89318871881987a7871b865b860385c5855384fb846f841783a5836782db828381f7818580f980537fe17f3b7ee37e717dff7d737ce77c757c037b917b537afb7a897a3179bf7967790f788377f77785772d76bb764975d7757f74f37481740f73b7734572d3726171d5716370f1709970416fe96f916f1f6ead6e6f6dfd6d8b6d196cc16c696c116b856b136a876a4969d7693168bf684d67f5676966f76685661365a1652f646f63e36357631962c162016175611d60ab60395fe15f6f5f175e715dff5d735d1b5cc35c375bab5b1f5ac75a3b59c9593d58cb58a7581b57c3575156df56875615555554c9547153ff53a7534f52dd525151f9516d50e1506f4ffd4f3d4e7d4e254d994d5b4ce94c5d4beb4b454a854a4749ef497d48f1487f47f3479b4743469d464545ed459544ef449744254399432742cf424341b7412b40b93ff93fa13f493f0b3eb33e5b3e1d3ddf3d6d3ce13c6f3bfd3ba53b4d3af53a9d3a1139853))) else (if i<10 then (if i<8 then 0xc2090bc45705840001668015324025484591580241361132c20840e00900202c01506086400c013808089834cc11833263e00400b380482a0ea6440040048080f3054190ae0a904c032b0974180150a41083905080aa00002080482a0e69a059e00c0400a82c00c041007515c0241a66072870ac40320002601600d33039d0b905b8048024b2c8054200c0122bd01002ace68e04498ac110020804985882c31610bc70ac00905703800402905038481200904c03c015060420260120a06201728ed0091a892800a2b804826c150640c02a180200990382cc1c0708bd013801407048026c1507c7c432d0ad009213a41c0406c0b1080180631584581360b00541412207a13a48ac92c811580240400b00541903102aa00d8ac15284300482c10043a1e824287200906499628a6a53dd0195900a1891a81d4560815406817684241f20f008788541e82cf0600ab0898025a67054729bd8d74762389b08583dc1e581c0120c90439c0f4084038a15c00c0090101c12927b915845510255381a3915466f60531ad878706349d000e072c06034e40c0204613f0b7878047e2570c5c04c1e82401a40c603901fc21983e03a82ec1a6020984801b20d805082400400f002182a52c0693d82041c20a12801d4e80b0c374a381500843a9c30da02a93a281c0f46004e0bc23c0ff249ef01611153e0244a0a201e80f807811bd77e2594880ab004a819284241ea0f00860b0c42a0f8226c3905582a0012d93dc9a9c0d22b08b2204ca6fc3702424f6a0604218ce0a8e537b1ac8d647130438140091d0381c8218090c0c0354040a04c281945602a83b9704206904181e810804301061500e208201543d01a60097028c08004902380f80780209642af4012a9354a6980d27be00c8ac10209b449d30181115470280a08193dc8ac1b88cf290930daa7b93e281c0f4653e29c0cdec6b2389409204201f00f004003d05190b4156abd0540025889493dc8ac22a8812a9bc0fe0435030080222644a49ee4561154409651c089048602a456072329bf0dc09850349ec108653e29c0cdec6b23591c4c80c40d20280c2ebf5321c2c2260094e13e0b707883160f01200d3c1f2026c5602a010314e186d202c9d140e07a349f08ed80a53781c8b440c0e417a87d43c00482c00540204a9c005607ac3682ce4e81163823e51c091d37e02a4560e00102145611505d01d4809e02901e413206903883c014202a02181e810608404802b81300ab070002670a381ec0fa04002080480260930395856b23026c5605582c1e0a0c0b02c0218020299ec10266ad0304581ca6537ea3b0dca0693d82a01087056a0f9078043c42a0f508540808982ac012b06349bc056091c0648181c00204607287c090021802416180808d82ed281c02f03f903543ea1e002415002a010281d2c0b04802 else (if i<9 then 0x83646a2b0698284226404c28184818601c81801210c2100380e43a715c024012020054180f643e5158c142020515802480bb315981e0120b02c01d51504204803181c0604f026004122b228ad0550291a8ac041083058130000b0004844c1505c1d0357076020086410cd815a01c0240400a8299d004062b05483841c00a8821a281104380182c1c0e02062b02a2012905848ad0120ab2281c15009801002c0a81081502a0608f40c300640c84321002c0f01d43103f90d60b0089a1b1003264804a81400905030c40d009004826c1560a8303c001341805b82aca0bb059c10c16103a0541992012803100810120fe2125b00602005412565078836215a00322b2411e85609b603c208150517d60560120200541414489693b0024156517d099302c60708c6000226701000241600ab24001c5609b0541261383a549c0249813c1682cf00602016118013418c35a8af0780b7360e81678030100b0ca83c915881121054600c4560fb0048a40166733238af1f002008982a0d003600a8ae01242a283c200700901002aca02005402ac60ae115802709ab0b01002c0e11a034a15e0030092aa38112a2b0104024a00901002c0150482102c00120ab24208c5780004d82a0a0ab02182c060a981f48ac1084945205908410c4630328c22b364008015040700185802e2b80482a0d08210302c01504964600c0120a801002acc113030e0001600a8281c80e322b1a07815202004c08ae0548293e2588060a82048080a0b70570380520020004e1b30840b0481c8120a2b1e1330f029008982c0b45660180240c20d32906240e0d81e1e013105420483841e06c008384d140a88219488400905582cc80b3c0182841504435906240e301000241e80b3241b01300b31c0841360a80701015d418c01808015229007010a8151043501a7002020180a945628078185002e2b80482a0c22bc01826c1560a82d00c841009004b01080c0d33828095522b1e1581600d31815e0122815500540c0d505814041009055834c800906fc0a8150440c40a980362b004c81c1667044868100f00102024156502182ac160302b81fc4606804802460d604802a48400432e11601a0a824802c208610562b40252e76801c10e8746de8049980722b00484301600d33405e000455303c02422660700285802020515c0241507c01a10e0400a8202b45200ca180804562034e0040403c03981c1600e50541487767601002c01565c14609a8ad8650826128c0c0ae0598240040ba01a00413082a804945ee40320480a8156520082c08400e0220fa40c233783801e460604400820127415400d45700900482601a67030826240e3015008253400905802a0c07108618ac729a11580240400b00541900662b00483f80c20d33400cc5700900482ec00c0d33a062c5684320093e0160644a else 0x8020c009a281aa098821990900f00100024156594523181aa0b025005c0c020522402415660488431456314800810120f220b105862c214802c0a02a800410c1600f2089a9920128c00e11c1603715c0240401132428e08783922b4024a0ab215835811e0a9c0c0354e0ab703401d4884060100380e02ac0000241e40a82a0610860b000482608400e039a2b0020988219045602082182c080a882180801600ab28b10586c6560980805200b03d1590120dd182c00120201e09a8ac8090791013c0b00100c40e020050c0241565a0198ae0120200541507b45622b202482c41618b084562900581b0ac0a1058034c809181001e86108806844e03509b80c02ba568b07c22ab00e02001582c0150580c500540f0430581413641890382a48418015481c602020482601660a82c208a1980001002a0a0e084b62300541190544024e11d08e045c1c243bc4ae022801403503481c166020015385e2c0301002cc5100ab348ae05489d1a189002e2b807c024150620c110f00208f05814226061315e0000400a83212c45689d81502a0a6d1821c00d45610c804834ce00904803c01504034826004122b202080c20a808992073003315981e0120b0301c80e322b1159114602002182c01565577a17c193856a03c0ad456009054241aa0a9600844c1605c2b02a0c0e2902049554b0078048e104290103443280009b0541f08b043054600d0ad0093420a0000b0515e004136a64804a2098c9662f4121873047801a8194570090102c0412bf004e18b09a0b03428e0120b0182a58060da22182a0a02d81520240404070401c1c2c5605402220127a0028ac2180a82481c136205d81864560092018a4c8e0580c0184150113380c5611601002a09039202381c0400ab0581b08f0090048e012009119ec0410430581109a0b0c31834c848242b181c520409281848312070549012207a22bc0248098810044c1aa44048024542607040001fc0a85324024f2bfc26e1881800b02844c13180000482c01506c4602b8194340c00810860b705816848a070048430156505d82c0012303940800e2334d218a10486c800410c137009079248a8457801b81a00ec78600a8ac1a7009502854562a00826c8400e0200aa4562903837050090580940c40751582420060200701c1ca0a1058034c9813055c024160442851588ac809203c1007606404808015663850454157843e018384c5602ac0c02dd42fa13250570070090541a4f600901002c0150503904314563c7c432c1366bfc008262012720f61b08126930559421840001040a81c0503882c00e43c03881c1308090559653505404dc2648087059c00c0410090541980602007802a08020801cb2157b00928356054aed82190144290515802712c0b3303f815660600482401a60b03c91100629005702aca418903)) else (if i<12 then (if i<11 then 0x7002c06a2ba01843019448008240160a2b004826c150706cc13e4560522044f000020054100fe02a22b4208805d0cafc22d22b46783c8b41e40a80aa8be0090541824104991581a4904307963e015066480498c561315c10c1603c2388ae012c04148034cc45f06498ac0120b02cbbc0be0a342b48ae8721223a11e40c0b0015834ca0a8004e02d40f83d1481a569403a0083482260d33081c0120a105802a0b80031581842260a82a2525900e5c08028640e081055a0d1c0a808618ac1fc0e004440250a8a53783c940c0208049b009001601a0ac1420a83426c1a702a07003f81500b062b40253849a2b600f0260b0c1d18181a60b30480081688114802c07018a01a81c2180ca2a0800402c09838300662b01002c0c0bb821844f0606648049b1180f205582c08a070048430226405980820120a820c8490580405082a0a0532044e000e2b04d82a0c0b3821e0eb0066bf0104024e0b0a03824140c0a8299d015780307082a2086604881e940e301000241e80b3229101e4a2ba0040245f4611580810860ab22214cc8020059c0241506a0082a41aa0b0204601ff84d05401842266c18207704c83941d20600540f205463e0cc8b800044c1c030034e8020a90581014209082182a14570090699c1a7813004aad0160564b40241420200541452102b84102841505968cb210a929a24a90208bc43ae01a818040a2b2362010054fc2b02841600d32615812002006982c0a22b82182c0781305d834c1c082a3528024160882b83541c1056915e17f0bcc181482580722ba0082601600d332159806020058034ca0a025502cc72b9103c23312c020804985200200580c23f406515c20815050580080012387c1a4a0550092032f0100c5044836c1566c21600c4560d314803a8c00990323181664964315a0863030c00d45602080482a0c62b80480240400a82823d030c01b15a10c8400b03e0b704d83a004e3e01e42c43804560d593d834f03002005b9c1c00b0337e0981a609007f02a10418047881304189038c1500b0964008307704332061802c0301002dc1c060504080108305bd06011e0a826000c5610c0541013002000482c01505103402452140381002a0cc03089826c1504415501940ca0706900820120d344120054020050c26415065324002c0ee2b04dc024226760182a100d22b059834cc41890382a4704308ce0e58ad0092a00680700904d82a0a69a821c00cc0e0ae2154024e07251581c4660640483ec1200b02a0e416780305082a0b85601582c01a64078200ec0c80901002acc09006982c06207915881a0674c1682a20865c0982ecd1d80804802c0d813c018bc41604715824022b00905416128020515a81e1020b0302454e826019082457400030834cc84e9768b002af68218f0758260580c12207a0580e00e4568154024 else 0xc81c1500201a0804570208049016e0d50700a408a2b05882b8722b8158080150405982a0160385190ee0864078048c30d40305440241e044088184166800089970060a80100c1560204048c05484305402c0840545188ac5200b00049422a0ab821810c1605c01808015038048a420400200541480920780380a8980d055e0000120bb2981c61802a057101301a0180830002900541640c1190558c830098d1582c082900860328150408982ba012305402cd0400b02301016700331582be0120b03a10d80740105482c0a0a80580284642003082b816049322024160350380801503070010c1660b0202dd10402007000a8a0e0c00032c6113030c01c1e40e029a28c0c62b06a82c0aa2b404b00c840480482a0c0c0b02210d80662b40482241520b0384330014033158a4015c0e0382b81660b01b0120062f10584024b056c03891040aea0202a08c3b90348ac1200b02a0250400f2054108ae0ae059a81a0120b030be8521403315e0001500b0391581302c0083c80123435906016e0b0202cc15604350302c0b20690382a41604059d108156409015150ac0982038c1aa0b00558d003206c0003c81500b03609a8ac809180801134001a1598020a11c10e04100905808ac1c0601030001f83004e04c1560b0240e40558030544080aec805982c1012404118af0003474c06240a88d05996087009c01a080040501de0e608e07f010144560ae05810808290a01a81a04100905682a0f80005401846856603c8ac6020004890778038218e0400ab0048c0400ab13010808231583cd0120902515b00202005802a0a85604c108180e4c018b0a0400f02504c161009182dc80e418198ae0128201e00c1500201981a40e62b06a82c0a119c2b02424560d32c8ac1aa0ae182c045704319b2052040905703c0b081a22d00c1610092e2560000bb04d908318011208201220605402c0a60606a82c07401115c080040404c02c04290a01e00080c62b06502b8f26405820240c24a2b18ac1aa0b0202bf07e0b30860380b081a0182a00120ab2d1581420b01a8181a60900541016022bc000c18a290102a05206060580260a06107002ec1604202281a1040bb058160ac809069e01c1fc0b024c02cd06d10709a68077895c04617b0d9400a01a81945605d0153819609b0540e073813801c0241605c0001842260a8201841200a8058120c484201500800120fe318ac302d34940aa012408d8a40194384102c380f42b004e000150784160000400b00541680700900490181a65a46844c1200b041000800540d3419900c280008820260540b03a0242607315e0e81aac568219902a043054510804000901503ed00940a178136e060151208a0d307282841944c1d2b7a086308602601663c22d04e0120b02044cc5780004d82a0a07f0540980640408982a080ab) else (if i<13 then 0x40d20708982c0e113401a02460b7021901c1200a82c0800120f01e00e0400a8183801420fc180820860b018080150284131590400b0115960120a805810808290054088840b3201808081302a300810120a105590192098054038080a891582401a6441d80a9006020250e80120ab0541257a07f903301d01254100080522b069895680a80580c0fe856603c8ac981360202c00410092d00c160aa5182dd002418058110120a808c832880b0078410c60610698a401600092a81a0120ca07902a0a0b3050834c150422b02a0160820221580acc071b0e80400b007502a0a62b07920241604015410d40c0a805815086c0390382a41605a1d40241560a82500e0120201844c137009182ac041009182760960a904c20a85200a839c28156420421810cb00350320185200b02e00004062b058110860b02100c8064090100c166c040508d08a0ae44dd1588ac2900581c1120ae8218c520c0305402c02180d3302dc2180a80581015d22b40482cc160505b82a080c41805814143803103c81672060581024b403903c01cc560f280482ace0e0c0010807403465826c1a6480483c040c0a805814d682f1c2b02408120b30581c4c8607c000d0098f8160200120fe058104574568158e568a2b06982c084053030354160305483841c00432304d0122a0982c00400f08049416642007e0e8260ab00482b8160518661b022ea2b249be40d22b04802c0b803803834c5200200541a802607203cbb48ab405d81841c00090581b0060200540e8ac62b06a82c0830030388ac5204441515a40c0a8058164c8090404c184194584082ce8020f0202ba8ac0900581004181305803a89020055890fe0f08048c1660ae0784024829005982b87043c1582a0156462b481e00e391584641563064c0240120b0089944564090048430142501002861200a82200d0120201d02004080904d910400a811582c0822b05800801a644100080054305800805f50090781404022b054028486de21583c2012482b0158160342b481980f22b2504c8120200049287502007d82a080f2059c15816040929178150a2b0861114720601002c080b0903834c60a822b02c0641805bc0a860bb054026c62900544158160405d8a400120b020080012281680801420d324ad01500b0079104560ae058208080b3055a024704305820807847015600c60b3a2b18ad012090298ac8560ab0541016f0180540430160540202c0441306998ac012440240aa00e2c4055c024d2b404d82c01a64070b00c40e020202a004009b1cad0012c040700284bc0204102ac160408630041660a8210600540b09031304c0fb07f02c080b380482b81564c2560b45200b0004e0e80407015410c1568430581700660682182c2012501002a0429001582a06a64030e0020020f205402c0f85e186101c150a2b2 else 0x5f4a64058044d809009360103001303a0ac0400a1054181e00d38218f06102005402c2012582182c01563c018024156306160e60130200541608780310320814570090780381185690348ac1200d3282a01608090048080b018421b00e))))
def x511l11 : Packing := (769,4,9,0,0,16,0,x511d11)
def x511h11 (i : Nat) : Nat := 0x43b741aec20a9dd4000000004052ea1b81b2838c0001c37b42cac2a51e5400000000000000000003c0361da003968196408a42780000029680c1c211c134c1b40002019c801000000000000040180000c325813001fc5daf833e80c9dafa42dd435bc1cada4640fdc32f8371036642d80000c04b0329902c0001417d0096c118000201e0816f82071e894b3f82aec1a4c0a100e2c26d02bf43a200d8c1401a09807400000003400800000002c18c0308c377036240de5e254171429942ebc26a41e8c353823301a110fdc2d00000806d4311c0b000000002805ec35e655980d5422741d801f281bc408703b19f539a6ac33b1a038273de8c1eaa0217817581140003009c000000000000000001680000000019c91eb801580001c27d424d887e814f401747a00000000382a203029fa30022c004000080f002b802e181838110000000020384000200400002400ec100c22f825ee480000000029e4bc23a020e40ce003281d7c346de840000c2b280288354c1ce40f800000000000000c5c0640001818a439a42639ba2439f822103881a84802c431c82754258000000015e16a4f6421800000003c09b0152c1a80001c250000246780000812e81c400000001828400009fa6c0bc00010139834a40b94072c04c0000000201640000000000000001c1f567a886cfa9da436b0600dfac808d9df9c28ca4c200e540f542c39069819140ad403c9de80106cae5031642410063834fc3a5c198c2c6d145c2aa5e340122037cc0028090007e8254836cc2f442ec000000000003ddb0c26581ec00031e09001f010a015481e40000000000028079423c00000000000001c00000000000000024000000034617421e813d830c904e4184824b82d781b85e9400011b505ace815e431ac3428160d9eb0055c039c22800011efb4125406942fdc2b703a913b280d2005bc3ac81df02f28383828100a800000003814800000000000000034082823400000000000000039a15c20042ce4046812bc33782e75e12c33041d00002896640e800000002c244c820000000000002429080ec428ac17b811c000200a7810c000180b40003c30581fa832000021e6c0000000000000000000000000000039282fb9d70814507431f2d429c460800120861430c030100008318300878c0c70420408000820000801000070408530421c00410470800000040000420013c004000000804600004000808f1000000020400001402412c50830040c00000490000000400121c00800861480003000c0000001006001143085002000000000000
def x511d10 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xdcfdb758eaa54960b7facc5499360160dbf980aed5260560a7fcca54e9988960e5fca961d7350560fed963601305cd609efecc6d58258560bef9c35498059160fed9306d95348160fbb9805494161160dedd636e95260d6097fecc6c95365160cefda66c0a254d60fcf96169d73601609dfdc7aed5264d609dfdc7aed5261160f3f5815493166160d5fdc7aed52645608ffdc3aeda254160cefda66c1524c560b6fecc54963651608ffdc3aeda2615609dfdc7aed5264560fee920549634c16097fdc3aed5264560d5fdb7646aa54960aefdca549634c160befacc54980591609dfdc7aed524c16097fdc52e5a460960c7bd526d2aa64d6095fdc7aed5265160e6bca95954250560fcd9305cd635c16097eecc6cca988960facd635498260d609dbdc7aed529116097decc6d4a98cd6097bdc52e541611609f79c5aeda76016087fdc22e99395560c7ddb34c2aa6556097f5c1aeda954960c6fdb2594a954d60cebda66d0a254d6087fccaaed5364960c7f5b14c2aa64960a77cca6e5539556087fccaaed326556087fdc22e9958cd6087fdc56caaa64d608dfdc7aeda54c960fab9526016461160df7110aed5254560f74e3388a9995560977ecc6c8a995560cfd9302e95348160a77cca6e55295560977dc26cca995560e7f0a94c58050560d7cdb2548a98cd60fb71526055160160977ecc6cca995560faf1616cd8060560c7dd302e953649609df9c7aed5260160eaf9656c1a80c9609cfdc7aed5258d60a7edc22e6aa5496095fdc7aed526456087fccaaed5264d609df9c7aed528016097ddc22e9958cd60977dc22e9939556097ddc26d4a98cd6087fdc32e992955609df5c7aed5284560a7ecca6e55288960a7ddc32e6aa54d60fa798568d656016097decc6c8a98cd60a77dc52e6aa54960c5fdb76a6aa5496095fdc7aed5264d608dfdc7aeda548560fe7152441a6545609cfdc7aed5259160c5fdb72e6aa5496087fdc22e95166160a7dcca6e5538cd6097ddc52e9928cd609cfdc7aed5258560a77dc52e6aa54d60c7bdb46a4a254d6099fdc7aed52a2160fe7165545a344160a7bdc52a5425056097eecc6d4a9889608dfdc7aeda25416095fdc7aed52661609df9c7aed5244160c7f5b15c2aa649609bf9c8aeda26016087fccb69593485609fb9c4aeda360160f3755254598605609dddc7aed528cd60fb65526095160560c7ddb34c2aa64960c6fda66c8a954d60fbd1804c53060560fae552609616056095fdc7aed52a656087fdc22e99354560c6fdb258ca954d60fab9846dd8059160c7f5736c6aa64960c77d522e95166160e7b8a96014250560c7f5316c8a950560e67ca9549a654d608dfdc7aeda261560ff49534c15248160faf152601616056097edcb54ca988960a7f4ca6e55284560c5fcc96deaa54960d3b8b96014161160 else 0xa32f4caa3224c68311cbfc2e8cb902e2cb782dccb602cfcaf42b84ac02a7ca7029aca3c28349de272c972250c930247490a23a48ba229c8942204836208c8101f4c7961dd47461bec6da1aac69819dc64818d45f8179459a153c53c146c4de1284480117c43e10743fc0fa43ba0e643940dcc3360c1c2d80b4c27a08f420e077c1a2067416004fc0e6034c0b20244000f75d535493064960c7fd546ceaa64960dedd636c1524c560eafd656c1a80c960cefd636c2aa54960e5fd7068d935c560dbf980aed5261160aefdca5496360160a7fdc12e6aa54d609efecc6d58259160d7ddb15cca954d60fbe58154931609609dfdc7aed528cd60faf5616d58260560e6fcc96956348560a7fcca54a998cd60a7fdc32e5a548560adfdc728da54816097fdc2aed53645609dfdc7aed5250d60d5fdb7652aa54960f76d535499348160d5fdc7aed5265160ff59534c152481609efecc6c95359160cefd636e9305c5609dfdc7aed5260d6097fdc3aed5265160dbed816cd5260960fcf9635c1305c560c7fd876c8a950560bebecc5496461160cefd636e95244160bef9c35498058560a7fecc549a364560e5fd936deaa54960a7fdc12a5a754d60ff695254d3048160eedda64c0a254d60dbf9806dd31611609dfdc7aeda54c960e7f8a960173505609dfdc7aed524c560beedc35498258560c7fdb25c2aa64d60befacc549805856097fdc3aed52a6560beddc3595305cd609dfdc7aed5250560bef6cc5496160560ddedb7548a3481608ffdc3aeda260160b7bcc95058750960a7fdc82e5a35c560dbf9806cd5260560a7fdc32e5a261560fed96354d3048160ecfd636deaa54960f5f9735c19360160bdf9c72cd2060160a7fecc54aaa64d60d77db1548a954d609efecc6c95358560cefd636e2aa549609efdc36d582585609efdc2aed5358560fbf1815493160160fadd636d58260d609ff9c2aed5344160bef5c35496160560d5fdb764eaa54960d3fd816cd5266160befacc5496360160ff595254d3044160a7fecc6959348560aefecc549a358560eedd63685305cd609dfdc7aed5260560fe6d535496348160e5fd735c2aa649609dfdc7aeda5609608ffdc3aeda548560dedd636cd5260d60fed963481305cd60d3fd98aed52605609dfdc7aed524416097fdc2aed53a6560fbf1804c53060560aefdca5cd6354560c7fd986c6aa54960c7fdb1688a954d60aefecc6956348560edf9a35c1305c5609dfdc7aed5265160c7fd986ceaa54960a7fdc55ceaa64960def963aed5244160bebecc549645056097fecc6c953645608ffdc2aeda354160c7fd936e2aa54960cefda06d8a3549609ffacc6c95344160dbf9806c55261160ecfda35c1635c560aefecc6896354160c7fdb24c2aa65560fcf9735c16360160bef9c05496360160f5f9705cd9348160) else (if i<3 then 0x1222ad00b00184722f5456202c03c0184020002444048136202c0a2b008060048160200800f0101600048b80328ae0201800b00024405800122600c381684020002440100012200240ca1340c2100832502c0531590122c00ca2b8080020201600048802a034c544ae0000100c0b00184451582182b01d22b101601000400048809020244600654a20c900b0002468150150202de41820040b0201500582012302c00611004000488c016060434982260598f8010f0100580900340240f018120058080200024530310402c01c2010001220600e010080200024404801609158f007226040515b8f81016000489c5680aa0091f051c137010058709406001a67024102a2024636881c23640d34c4ab010c2f30d9a0068075035456303b722b098ac804880b008160180a80ca10227c0001503026c0a8100120700b856034c0b018181880a8c0102cc805401560580ec01a8aec0002a08058040d302cc404c01f6202840f2101c014870d9c210160502ec0b002a202a399200931012100150101012102600a8160c5421005400481e45a9d0300481602049c0a8101560100226307027c0181603cafc11303ec6069f00e0580c4200f093c09f074058018006998090034c0b0181601a81c20540410c8080400481300540c0b00901211080243100c2059815008997207088401049ac0302c00d320161c130180069900b002ac501c81560580f82de09b83a02c38f8281a60580800904640d31816010432a0717074161f00631080340c180360181c0402c02401810e059804005417062034c09003c202a2e456102c00a817011c0981a605813813e0b42c2e00c807801502044c0a810232079080dc02a0500481e0202c0205840120558c00903804020240ab1408605428ad00490090034c0b01801208c81a6304cc8c7c016601002300541a04302a2009034c9021c0120580e06220240fe1815ac21004006990014870c5c268160402c00a81017702189c20544012732190200e8ac404880d302c0540e40bc05de87c004e87805401600150040a84ee11a83e60ca82de096824606281060127ffdfde7ef5faa7e5df767d55f347c4def27b0dea27a05e6078fde1077f5ddc7725da875add5874ddd24740dce27305ca071fdc5e70f5c1c7025be86f1dbc26e85b806d0db306c3daee6b35a9e6a2da6a6925a366855a0267859ce66b599a65e595864dd924640d8e262cd88461c585e60f582a5fb57cc5ee57a65e157645cd57145c056ee5b356ac59f565c58ed61a57ad5e657155a4564557e557553c546d4fa53654b851ed45a50e540a4fa53c84e9d3944e3d36e4d3532c4bf52dc4a7d270493d22e48351de472d1aa45ed15a44e511844150e4437d0be427506e4135048409d0063f5cf703d04e8639cce5238fce2c382cddc36ecd9a35acd6634a4cf else 0xe00c0a810160054098039818595f81e40898c0b00945681008004d81605158cc0302c0419401600048ea06081608048b80702c04050841260804000488809038041482808200800091704c0580809002c122b18150a038809002c04054605620ca00b0144568100040302c020100012200242c01804020080009034c0b020160120800a110150100240d310120069880b00080405401602606202a14c56804880d302c0401000542034c20580012200ac0a81000200024460041302e12b82d02c383a20160103c029010040004880900080592210404048e62b09012070080b7101c40580700000805c0004090002440558432402c04058040b002845c018040203c1009101d41e00c020101600308809048ac0d3181760584c56302c020580400902ac405804c03a8ac42000809c098160202c02055840d302c0401))
def x511l10 : Packing := (238,5,9,0,0,14,0,x511d10)
def x511h10 (i : Nat) : Nat := 0x60417c1826c0e20d50478740000000000002ddb011000439c000000c07b0334006ec90a40660372c8677882bde901a914705641cc10671b3a9c2d25c00010181fa21200f0001426000b20400cc312170002007804000474202d00ac1c070021020010014009000000000040000300000000000
def x511d9 (i : Nat) : Nat := 0x70070e0621176201601000b00b80308005404002c02b81c3c0b420000ab080058040580405805c0384130015035207180b00800908005804058040001601f7f6f71a4cfe2eef72af5668b318ec6226ff7d399a4be55294e65f25918641e0c8500147bedd549b4aa99358269fbaf662a4b1b28b059ee754a960142505609e7aebd98a92c2c0ac13cf9d7b315260164583397ac8e3d76a9308b0673e58dc7aed524416092feebd98a9554c9ac1daf161601b3549815822bfbaf66364a9b22b0633f58dc7aeda254160e2fab9b62b8554c92c13cbdd7b3152591415822bfbaf66364a9b28b061fd6c5c55ceaa6496092feebd98d2b2690ac199f9c7602bb5498158259fbaf6634ab1a42b04d7e75ecc5499360160ff24a9a40a92c6982c185fda371ebb5499158333f300e3d76a9308b06f3671d63601305cd609e7cebd98a92c6c02c17ae5d35498258581582f5e5baa9300b0b02b0647f71d98aed5260560967eebd98a9346b0ac13cf9d7b315260161582f575baa9300b2308b054ee754b96014161160
def x511l9 : Packing := (31,6,9,0,0,9,0,x511d9)
def x511h9 (i : Nat) : Nat := 0x1e170000c
def x511d8 (i : Nat) : Nat := 0x294278b9e7b75526016461160ce3c605d7b31526016158305bdb475ecc54aaa64d60
def x511l8 : Packing := (3,7,9,0,0,4,0,x511d8)
def x511samples : Array (Bits × Bits) := #[(0x7f3f03eb25ec1cd0d307c75df4ea7ebbd441ffae469e0dd9423eebc36892a1529a8892126b2124071b4850b563294f989a92032046080430200022110144062101831d04000911800803c61814040123082787cb30da41a23484846b3e21f673,0x150744000154c20a800001d500000000a52849022011520408c2e510104002016040d46a682024111aca1011a3700f2140530201420b60146c1220155245005e11884880800811240805061844a009223823421320ca41202484441224212652),(0xba6d219b9f3a2ba4cf7c1167281c949697911e5bbc9f04551afcef4b694a275ef9074b80a111d2e520000d4f080540c3f0042653080280cd93435050002d40204b4200140043200130821828c0299c3b00c4a4cc3121e604c0ff0600c8c6487f,0x8010806406000021669414082061a052405004b1402420008008002140821c348b060b009101d2e4a015066c0805f08290842412102088cb104054808c02c801484215142043284031825826b00d501000c424c4132190008842202488c44829),(0xacd46f21db1393ff5475d9fcdd3fd0e7abc349db97815d666a5a0e880a613e1274b0c8cf4e46418206e021118be029580038c00ce24115078504302edc2404440c1500110502c00581102062e8abb9c433003837c0282c4403180000f1078f9c,0xa0b448820221dd400600b8040121ba00ea541000808854e08100490024102820490c48f4ac2010202e8218120c809580031c0e9cf4954048534200c425d1640203500088500c025803c201008020a862300900a80406c440218c31871038514),(0xf46ed4295bfdaa2eeeaba4084f479a6cda17c7387ee3842c6378964dc2638f75ed658121a0aca88068338634c2d6d784054a8900909240510c5c8d378a82310c400400e8a08c000241f83fc6005226003e010030020880790be0188301f80fe0,0x102000400a844002850420568404400d1008201030031a81400251202418004938650110b12da0a05002d674c206f2a32e4a0b0000268851004807b3b08201ae17808440508c000200001506307ca4001c050060002a103109e0302300b00ae0),(0x95eea7429dccdaed067970f59fe69ecba731158567a1ecb9ddc59b551de04f584b1a298444da5c4ed5230088280d105c05a4a42e1e901408229c4a4101503500c8870188a973019900cbc01510440004c2013f000410887ef00018c001fff000,0xead89a30b0280950523198002890b6d0004386cd43c88458160d024ac8012812011a288404d25a4e853528881c09005c11a4f4be3d9016aa12a5d8480d38b401e877310a297308d941fac04180035205c200bd8806108c4ed0108bcc014ed000),(0x7ff38bb76b67cf37ef128f98f2eee56c429d907d6c7ceb6cf419925f9ac9f3c5e1972491926e5040422cf52c44868a222a7811d2816c362910c455420090fa93003d56025e01087bbe0400010f100004cdf8000005d233800400f96bfe000000,0x2189a284280005451a1780882902b035044a03845000000000410088104850a03a70091924e50604020e1a64c8480102a2c495081a01c01806c13622c107aa0064714007e810853a40840072a069204879480800230228008109b45da000000),(0xd71b16d2f8e8356eda0a178b7e0ffc0afa72381ebdae041b57e85cb82fb7b3eaa809b006ab740a78d7a0f85252080211624534498a02bcd0e62329e1200d6604b340a8000f7cf605000000010f5065f802024000081523fdf3ef021400000000,0x40624a0089840644190208d003980d8c010aa208011102211a7269c8b300810b10a9a013227e080857a2f992520802352a41534dab0b7634e63f2b6331e426ae1780a8021fac94a1400c00410f72a7e932008000001663fd73bd830000000000),(0x5bef0bc2d89072a1d2b67cdaf6c111dda65c64453519feecfa1f7036feb04a7f1a4c31583451bd8db4c494408333e62287c0741e610521da3002e419558000c0cd20ea7300000800000400012fd125fccdf93f27fd8d88030000608000000000,0x4120001488040203860a0055156c000881101cc3b23438b1346b2a054c820014004831602511ae8dbd171440933376a7d5c236062014a3fa3283cc9191a2810bd988ebf30002018041000040d5f9657958696f757d8f9003040024a000000000),(0xf2e2f63ce412c031a397490bc52a843bd43b2f6096e73b9afc4538b7ec9c9efeb8525e6e4c02a51fa858220915100d4080a3a88000605a1849e081802212881af818aa715ffcf67efee3bfa800014200000240000f8518030800019400000000,0x18105922011a02820108420684310708e9049c2022ce45881008615086138b040105e6c4c000717a85d000901310d48d090a0804440010a0980c00c02098051e83843bd8050630c1bf3aab8c0814802000240180dc10c020400449800000000)]
def x511columns : List ColumnInfo := [(320,0,191,0,11),(17,0,494,0,11),(64,0,447,0,13),(66,0,445,0,11),(192,0,319,0,11),(4,0,507,0,12),(160,0,351,0,11),(24,0,487,0,11),(17,0,74222,0,11),(258,64,189,0,8),(320,0,93887,0,11),(320,0,99007,0,11),(320,0,109247,0,11),(320,0,1727,0,11),(320,0,2239,0,11),(320,0,3263,0,11),(320,0,11455,0,11),(320,0,12479,0,11),(320,0,17087,0,11),(320,0,42687,0,11),(320,0,44735,0,11),(320,0,47807,0,11),(320,0,52927,0,11),(320,0,54975,0,11),(320,0,58559,0,11),(320,0,68799,0,11),(320,0,83647,0,11),(320,0,88767,0,11),(320,0,119487,0,11),(320,0,58047,0,11),(66,0,58301,0,11),(192,0,58175,0,11),(83,0,428,0,7),(80,0,44975,0,11),(80,0,94127,0,11),(80,0,109487,0,11),(32,0,479,0,12),(80,0,12719,0,11),(80,0,43951,0,11),(80,0,53167,0,11),(80,0,83887,0,11),(258,64,58045,0,8),(9,16,486,0,8),(132,0,379,0,11),(80,0,1967,0,11),(80,0,42927,0,11),(80,0,48047,0,11),(17,0,73710,0,11),(80,0,51119,0,11),(80,0,55215,0,11),(80,0,60335,0,11),(80,0,69039,0,11),(80,0,69551,0,11),(80,0,89007,0,11),(80,0,99247,0,11),(80,0,119727,0,11),(80,0,124847,0,11),(17,0,49646,0,11),(17,0,50158,0,11),(192,0,42815,0,11),(66,0,94141,0,11),(66,0,99261,0,11),(66,0,109501,0,11),(66,0,11709,0,11),(66,0,12733,0,11),(66,0,17341,0,11),(66,0,53181,0,11),(258,64,58557,0,8),(132,0,48507,0,11),(66,0,60349,0,11),(66,0,2493,0,11),(66,0,43453,0,11),(66,0,44989,0,11),(66,0,83901,0,11),(66,0,44477,0,11),(66,0,64445,0,11),(66,0,69053,0,11),(66,0,69565,0,11),(66,0,104381,0,11),(66,0,119741,0,11),(66,0,124861,0,11),(17,0,119790,0,11),(258,64,119485,0,8),(24,0,119783,0,11),(192,0,44863,0,11),(192,0,53055,0,11),(192,0,54079,0,11),(192,0,83775,0,11),(192,0,94015,0,11),(192,0,99135,0,11),(192,0,109375,0,11),(17,0,124910,0,11),(192,0,124735,0,11),(192,0,2367,0,11),(17,0,55278,0,11),(66,0,55229,0,11),(258,64,54973,0,8),(480,0,31,0,7),(17,0,69614,0,11),(192,0,69439,0,11),(160,0,46431,0,11),(320,0,44223,0,11),(320,0,64191,0,11),(320,0,104127,0,11),(160,0,83807,0,11),(258,64,83645,0,8),(24,0,83943,0,11),(17,0,94190,0,11),(17,0,53230,0,11),(17,0,99310,0,11),(17,0,109550,0,11),(160,0,94047,0,11),(24,0,94183,0,11),(258,64,93885,0,8),(83,0,94124,0,7),(17,0,12782,0,11),(160,0,99167,0,11),(83,0,12716,0,7),(8,0,503,0,12),(258,64,12477,0,8),(17,0,69102,0,11),(258,64,68797,0,8),(258,64,99005,0,8),(24,0,109543,0,11),(132,0,99195,0,11),(192,0,88895,0,11),(17,0,89070,0,11),(65,0,54206,0,9),(192,0,44351,0,11),(258,64,11453,0,8),(258,64,43197,0,8),(258,64,52925,0,8),(258,64,109245,0,8),(192,0,51007,0,11),(66,0,5053,0,11),(83,0,17324,0,7),(164,0,347,0,8),(12,0,45555,0,9),(160,0,53087,0,11),(161,0,350,0,8),(192,0,47935,0,11),(192,0,60223,0,11),(132,0,109435,0,11),(65,0,58814,0,9),(36,128,347,0,8),(83,0,99244,0,7),(160,0,63839,0,11),(160,0,50015,0,11),(81,0,11694,0,8),(17,0,60398,0,11),(17,0,48110,0,11),(17,0,114670,0,11),(177,0,334,0,7),(258,64,44733,0,8),(24,0,45031,0,11),(344,0,167,0,7),(258,64,17085,0,8),(258,64,64189,0,8),(258,64,104125,0,8),(17,0,17390,0,11),(83,0,109484,0,7),(198,0,313,0,7),(66,0,1981,0,11),(66,0,3517,0,11),(66,0,4541,0,11),(144,0,367,0,11),(192,0,104255,0,11),(320,0,2751,0,11),(178,1,332,0,4),(56,0,455,0,7),(12,0,499,0,9),(85,2,424,0,4),(65,32,30,384,6),(74,0,437,0,7),(138,4,369,0,5),(164,0,48475,0,8),(449,32,30,0,4),(33,0,59358,0,9),(132,0,44923,0,11),(270,64,177,0,4),(24,0,55783,0,11),(24,0,55271,0,11),(145,32,78,256,5),(40,0,45527,0,8),(80,8,163,260,6),(24,0,48103,0,11),(480,0,83487,0,7),(321,0,190,0,7),(177,0,99150,0,7),(160,0,42847,0,11),(258,64,44221,0,8),(132,0,69499,0,11),(356,128,27,0,4),(1,16,55782,8,9),(164,0,42843,0,8),(164,0,50011,0,8),(164,0,63835,0,8),(5,0,68602,0,8),(83,0,53164,0,7),(36,128,48475,0,8),(24,0,42983,0,11),(162,0,349,0,7),(401,32,78,0,4),(9,16,55782,0,8),(160,0,104287,0,11),(132,0,104315,0,11),(164,0,104283,0,8),(67,0,11708,0,8),(7,0,504,0,7),(24,0,69095,0,11),(18,0,55789,0,9),(154,4,353,0,4),(132,0,58235,0,11),(44,128,339,0,5),(56,0,48071,0,7),(56,0,89031,0,7),(56,0,94151,0,7),(56,0,119751,0,7),(33,0,54750,0,9),(133,0,378,0,7),(344,0,83623,0,7),(198,0,83769,0,7),(132,0,50043,0,11),(260,0,251,0,8),(404,8,99,0,4),(9,16,50150,0,8),(133,2,312,64,5),(160,0,88927,0,11),(164,0,88923,0,8),(198,0,44857,0,7),(160,0,124767,0,11),(164,0,124763,0,8),(132,0,124795,0,11),(83,0,60332,0,7),(390,64,57,0,4),(160,0,58207,0,11),(164,0,58203,0,8),(144,0,54127,0,11),(193,2,312,4,5),(160,0,47967,0,11),(197,2,312,0,4),(164,0,46427,0,8),(345,0,166,0,4),(200,256,23,32,5),(177,0,114510,0,7),(132,0,60283,0,11),(132,0,63867,0,11),(24,0,6631,0,11),(80,0,431,0,11),(136,0,375,0,9),(32,128,46427,4,9),(282,64,165,0,4),(96,1,396,18,6),(9,16,49638,0,8),(329,16,166,0,4),(480,0,1567,0,7),(132,0,2427,0,11),(24,0,12775,0,11),(160,0,7007,0,11),(164,0,99163,0,8),(49,0,94158,0,8),(56,256,135,64,5),(177,0,124750,0,7),(160,0,60255,0,11),(164,0,60251,0,8),(24,0,50151,0,11),(132,0,42875,0,11),(24,0,69607,0,11),(156,0,355,0,7),(132,0,83835,0,11),(83,0,119724,0,7),(24,0,114663,0,11),(80,0,3503,0,11),(296,0,215,0,7),(83,0,55212,0,7),(232,256,23,0,4),(24,0,89063,0,11),(9,16,114662,0,8),(344,0,44711,0,7),(9,16,55270,0,8),(88,256,135,32,5),(166,0,345,0,5),(164,0,83803,0,8),(14,0,497,0,7),(9,16,69094,0,8),(9,16,119782,0,8),(268,0,243,0,7),(96,0,43935,0,9),(56,0,83911,0,7),(36,128,46427,0,8),(418,64,29,0,4),(33,0,11742,0,9),(32,128,50011,4,9),(32,128,42843,4,9),(193,0,318,0,7),(1,16,109542,8,9),(32,128,63835,4,9)]
def x511autos : List (List Nat) := [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def x511levels : Nat → Packing
  | 14 => x511l14
  | 13 => x511l13
  | 12 => x511l12
  | 11 => x511l11
  | 10 => x511l10
  | 9 => x511l9
  | 8 => x511l8
  | _ => emptyPacking
def x511index : Nat → Nat → Option (Nat × Nat)
  | 14 => lookupWord 16 121 3 14 6 4 x511h14
  | 13 => lookupWord 521 705 5 17 9 4 x511h13
  | 12 => lookupWord 1041 1303 7 18 10 4 x511h12
  | 11 => lookupWord 151 409 6 16 8 4 x511h11
  | 10 => lookupWord 45 57 4 13 5 4 x511h10
  | 9 => lookupWord 3 5 1 10 2 4 x511h9
  | _ => fun _ => none
def x511 : Forest := ⟨511,14,fun j => x511samples[j]?.getD (0,0),x511columns,x511autos,x511levels,x511index⟩
set_option maxHeartbeats 0 in
theorem geomx511 : graphValid x511 (boundsBefore known83647) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_14_0 : block x511 14 0 1=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx511_14 : block x511 14 0 1=true := sx511_14_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_13_0 : block x511 13 0 22=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_13_22 : block x511 13 22 36=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_13_58 : block x511 13 58 6=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx511_13 : block x511 13 0 64=true := (@block_merge x511 13 0 58 6 (@block_merge x511 13 0 22 36 sx511_13_0 sx511_13_22) sx511_13_58)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_12_0 : block x511 12 0 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_12_36 : block x511 12 36 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_12_72 : block x511 12 72 14=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_12_86 : block x511 12 86 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_12_122 : block x511 12 122 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_12_158 : block x511 12 158 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_12_194 : block x511 12 194 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_12_230 : block x511 12 230 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_12_266 : block x511 12 266 7=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_12_273 : block x511 12 273 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_12_309 : block x511 12 309 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_12_345 : block x511 12 345 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx511_12 : block x511 12 0 381=true := (@block_merge x511 12 0 345 36 (@block_merge x511 12 0 309 36 (@block_merge x511 12 0 273 36 (@block_merge x511 12 0 266 7 (@block_merge x511 12 0 230 36 (@block_merge x511 12 0 194 36 (@block_merge x511 12 0 158 36 (@block_merge x511 12 0 122 36 (@block_merge x511 12 0 86 36 (@block_merge x511 12 0 72 14 (@block_merge x511 12 0 36 36 sx511_12_0 sx511_12_36) sx511_12_72) sx511_12_86) sx511_12_122) sx511_12_158) sx511_12_194) sx511_12_230) sx511_12_266) sx511_12_273) sx511_12_309) sx511_12_345)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_0 : block x511 11 0 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_5 : block x511 11 5 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_41 : block x511 11 41 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_77 : block x511 11 77 16=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_93 : block x511 11 93 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_129 : block x511 11 129 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_165 : block x511 11 165 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_201 : block x511 11 201 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_237 : block x511 11 237 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_273 : block x511 11 273 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_309 : block x511 11 309 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_345 : block x511 11 345 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_381 : block x511 11 381 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_417 : block x511 11 417 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_453 : block x511 11 453 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_489 : block x511 11 489 14=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_503 : block x511 11 503 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_539 : block x511 11 539 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_575 : block x511 11 575 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_611 : block x511 11 611 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_647 : block x511 11 647 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_683 : block x511 11 683 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_719 : block x511 11 719 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_11_755 : block x511 11 755 14=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx511_11 : block x511 11 0 769=true := (@block_merge x511 11 0 755 14 (@block_merge x511 11 0 719 36 (@block_merge x511 11 0 683 36 (@block_merge x511 11 0 647 36 (@block_merge x511 11 0 611 36 (@block_merge x511 11 0 575 36 (@block_merge x511 11 0 539 36 (@block_merge x511 11 0 503 36 (@block_merge x511 11 0 489 14 (@block_merge x511 11 0 453 36 (@block_merge x511 11 0 417 36 (@block_merge x511 11 0 381 36 (@block_merge x511 11 0 345 36 (@block_merge x511 11 0 309 36 (@block_merge x511 11 0 273 36 (@block_merge x511 11 0 237 36 (@block_merge x511 11 0 201 36 (@block_merge x511 11 0 165 36 (@block_merge x511 11 0 129 36 (@block_merge x511 11 0 93 36 (@block_merge x511 11 0 77 16 (@block_merge x511 11 0 41 36 (@block_merge x511 11 0 5 36 sx511_11_0 sx511_11_5) sx511_11_41) sx511_11_77) sx511_11_93) sx511_11_129) sx511_11_165) sx511_11_201) sx511_11_237) sx511_11_273) sx511_11_309) sx511_11_345) sx511_11_381) sx511_11_417) sx511_11_453) sx511_11_489) sx511_11_503) sx511_11_539) sx511_11_575) sx511_11_611) sx511_11_647) sx511_11_683) sx511_11_719) sx511_11_755)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_10_0 : block x511 10 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_10_1 : block x511 10 1 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_10_37 : block x511 10 37 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_10_73 : block x511 10 73 25=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_10_98 : block x511 10 98 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_10_134 : block x511 10 134 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_10_170 : block x511 10 170 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_10_206 : block x511 10 206 32=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx511_10 : block x511 10 0 238=true := (@block_merge x511 10 0 206 32 (@block_merge x511 10 0 170 36 (@block_merge x511 10 0 134 36 (@block_merge x511 10 0 98 36 (@block_merge x511 10 0 73 25 (@block_merge x511 10 0 37 36 (@block_merge x511 10 0 1 36 sx511_10_0 sx511_10_1) sx511_10_37) sx511_10_73) sx511_10_98) sx511_10_134) sx511_10_170) sx511_10_206)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_9_0 : block x511 9 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_9_1 : block x511 9 1 30=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx511_9 : block x511 9 0 31=true := (@block_merge x511 9 0 1 30 sx511_9_0 sx511_9_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx511_8_0 : block x511 8 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx511_8 : block x511 8 0 3=true := sx511_8_0
theorem tablesx511 : checkedTables x511 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x511 0 0 0 = true)
  · exact (rfl : block x511 1 0 0 = true)
  · exact (rfl : block x511 2 0 0 = true)
  · exact (rfl : block x511 3 0 0 = true)
  · exact (rfl : block x511 4 0 0 = true)
  · exact (rfl : block x511 5 0 0 = true)
  · exact (rfl : block x511 6 0 0 = true)
  · exact (rfl : block x511 7 0 0 = true)
  · exact allx511_8
  · exact allx511_9
  · exact allx511_10
  · exact allx511_11
  · exact allx511_12
  · exact allx511_13
  · exact allx511_14
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem caseA : Impossible (graphGoal 511) 14 (vars 511).toFinset := by
  have h := root_index (g:=dead) (before_sound known383 valid383) geomdead tablesdead (k:=14) (by decide)
    (i:=0) (ws:=vars 511) (by decide +kernel)
  have e : targetOf dead=graphGoal 511 := by decide +kernel
  exact e ▸ h
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem caseB : Impossible (graphGoal 511) 14 (varsX 45567).toFinset :=
  index_root (g:=x511) (i:=0) rfl (before_sound known83647 valid83647) geomx511 tablesx511 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem bound : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = edge → 16 ≤ C.size := by
  intro C legal first h
  by_contra! small
  obtain ⟨k,t,S,hk,run,sub⟩ := initial_live C legal first h (by omega)
  have eg : graph=graphGoal 45567 := by decide +kernel
  have er : inputs++[seed]=varsX 45567 := by decide +kernel
  have e1 : graphGoal 45567=graphGoal 511 := by decide +kernel
  have e2 : vars 45567=vars 511 := by decide +kernel
  rw [eg] at run
  rw [er] at sub
  have ok : fullOK 45567 [80, 1, 2, 4, 1, 1, 257, 4, 8] = true := by decide +kernel
  rcases full_split ok run sub with e | e
  · rw [e1,e,e2] at run; exact caseA k t hk run
  · rw [e1,e] at run; exact caseB k t hk run
def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w
theorem run_len (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton l a ih =>
    simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
      List.length_singleton] at ih ⊢
    omega
theorem run_old (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    refine (ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (by simp; omega)).trans ?_
    exact List.getD_append _ _ _ _ hi
def bw (y : Fin 9 → Bool) : List Bool := List.ofFn y ++ [y 0 || y 6]
theorem base (gs : List Gate) (o : ℕ) (legal : PEqualNP.MetaComplexity.FanInTwo ⟨gs, o⟩)
    (small : gs.length ≤ 14) (h : ∀ y, (run gs (bw y)).getD o false = edge y) : False := by
  have e : ∀ y : Fin 9 → Bool, (Circuit.mk (⟨GateOp.or, [0, 6]⟩ :: gs) o).wires (List.ofFn y) = run gs (bw y) := by
    intro y
    have e1 : GateOp.eval GateOp.or (([0, 6] : List ℕ).map fun i => (List.ofFn y).getD i false) = (y 0 || y 6) := by
      simp [GateOp.eval, List.ofFn_succ]
    change run gs (List.ofFn y ++ [GateOp.eval GateOp.or (([0, 6] : List ℕ).map fun i => (List.ofFn y).getD i false)]) = _
    rw [e1]
    rfl
  have b := bound ⟨⟨GateOp.or, [0, 6]⟩ :: gs, o⟩ (by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · simp
      · exact legal g hg) (by
      intro y
      rw [e, run_old _ _ _ (by simp [bw])]
      simp [bw, List.getD_eq_getElem?_getD]) (by
      funext y
      change ((Circuit.mk (⟨GateOp.or, [0, 6]⟩ :: gs) o).wires (List.ofFn y)).getD o false = _
      rw [e]
      exact h y)
  have s : (Circuit.mk (⟨GateOp.or, [0, 6]⟩ :: gs) o).size = gs.length + 1 := rfl
  omega
def step (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)
theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) : run (g :: gs) w = run gs (w ++ [step w g]) := rfl
theorem run_app (as bs : List Gate) (w : List Bool) : run (as ++ bs) w = run bs (run as w) := by
  simp [run]
theorem step_congr (w w' : List Bool) (g : Gate) (f : ℕ → ℕ)
    (h : ∀ i ∈ g.inputs, w'.getD (f i) false = w.getD i false) :
    step w' ⟨g.op, g.inputs.map f⟩ = step w g := by
  unfold step
  rw [List.map_map]
  congr 1
  exact List.map_congr_left h
theorem run_set (as : List Gate) (w : List Bool) (j : ℕ) (v : Bool) (hj : j < w.length)
    (hA : ∀ g ∈ as, j ∉ g.inputs) : run as (w.set j v) = (run as w).set j v := by
  induction as generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, run_cons, ← ih _ (by simp; omega) fun g' hg' => hA g' (List.mem_cons_of_mem _ hg'),
      List.set_append_left _ _ hj]
    have e : step (w.set j v) g = step w g := by
      have := step_congr w (w.set j v) g id fun i hi => by
        have : j ≠ i := fun e => hA g (by simp) (e ▸ hi)
        simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne this]
      simpa using this
    rw [e]
def re (j n i : ℕ) : ℕ := if i = j then n else if i < n then i else i + 1
theorem run_re (j n : ℕ) (hj : j < n) (bs : List Gate) (s t : List Bool) (hs : n ≤ s.length)
    (hl : t.length = s.length + 1) (h : ∀ i, t.getD (re j n i) false = s.getD i false) (i : ℕ) :
    (run (bs.map fun g => ⟨g.op, g.inputs.map (re j n)⟩) t).getD (re j n i) false
      = (run bs s).getD i false := by
  induction bs generalizing s t with
  | nil => exact h i
  | cons g gs ih =>
    rw [List.map_cons, run_cons, run_cons, step_congr s t g (re j n) fun i _ => h i]
    refine ih _ _ (by simp; omega) (by simp [hl]) fun i => ?_
    rcases Nat.lt_trichotomy i s.length with hi | hi | hi
    · rw [List.getD_append _ _ _ _ hi, ← h i]
      refine List.getD_append _ _ _ _ ?_
      unfold re
      split_ifs <;> omega
    · have e : re j n i = t.length := by
        unfold re
        split_ifs <;> omega
      rw [e, hi]
      simp [List.getD_eq_getElem?_getD]
    · have e : re j n i = i + 1 := by
        unfold re
        split_ifs <;> omega
      rw [e, List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
theorem key (j n : ℕ) (hj : j < n) (w : List Bool) (v : Bool) (hl : w.length = n) (i : ℕ) :
    (w ++ [v]).getD (re j n i) false = (w.set j v).getD i false := by
  subst hl
  unfold re
  split_ifs with h1 h2
  · subst h1
    simp [List.getD_eq_getElem?_getD, hj]
  · rw [List.getD_append _ _ _ _ h2]
    have : j ≠ i := fun e => h1 e.symm
    simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne this]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
theorem rd (y : Fin 9 → Bool) (j : Fin 9) : (bw y).getD (j : ℕ) false = y j := by
  fin_cases j <;> rfl
theorem ins (j : Fin 9) (C : Circuit) (n : ℕ) (g : Gate) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (small : C.size ≤ 13) (hn : 10 ≤ n) (hn' : n ≤ 10 + C.size)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hA : ∀ a ∈ C.gates.take (n - 10), (j : ℕ) ∉ a.inputs)
    (h : ∀ y, C.eval ((bw y).set j (g.op.eval (g.inputs.map fun i =>
      if i < n then (C.wires (bw y)).getD i false else false))) = edge y) : False := by
  obtain ⟨gs, o⟩ := C
  change gs.length ≤ 13 at small
  change n ≤ 10 + gs.length at hn'
  simp only at hA
  have hj : (j : ℕ) < n := by omega
  have lA : (gs.take (n - 10)).length = n - 10 := by
    rw [List.length_take]
    omega
  have hgs : gs = gs.take (n - 10) ++ gs.drop (n - 10) := (List.take_append_drop _ _).symm
  have lr : ∀ y, (run (gs.take (n - 10)) (bw y)).length = n := by
    intro y
    rw [run_len, lA]
    simp [bw]
    omega
  refine base (gs.take (n - 10) ++ g :: (gs.drop (n - 10)).map fun g => ⟨g.op, g.inputs.map (re j n)⟩)
    (re j n o) ?_ ?_ fun y => ?_
  · intro a ha
    simp only [List.mem_append, List.mem_cons, List.mem_map] at ha
    rcases ha with ha | rfl | ⟨b, hb, rfl⟩
    · exact legal a (List.mem_of_mem_take ha)
    · simpa using hg
    · have := legal b (List.mem_of_mem_drop hb)
      simpa using this
  · simp only [List.length_append, List.length_cons, List.length_map, List.length_drop, lA]
    omega
  · rw [← h y, run_app, run_cons]
    have ev : g.op.eval (g.inputs.map fun i =>
        if i < n then ((Circuit.mk gs o).wires (bw y)).getD i false else false) =
        step (run (gs.take (n - 10)) (bw y)) g := by
      unfold step
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with hi
      · change (run gs (bw y)).getD i false = _
        conv_lhs => rw [hgs, run_app]
        exact run_old _ _ _ (by rw [lr]; exact hi)
      · exact (List.getD_eq_default _ _ (by rw [lr]; omega)).symm
    rw [ev]
    change _ = (run gs ((bw y).set j (step (run (gs.take (n - 10)) (bw y)) g))).getD o false
    have er : ∀ w, run gs w = run (gs.drop (n - 10)) (run (gs.take (n - 10)) w) := fun w => by
      conv_lhs => rw [hgs, run_app]
    rw [er, run_set (gs.take (n - 10)) (bw y) j (step (run (gs.take (n - 10)) (bw y)) g) (by simp [bw]; omega) hA]
    refine run_re j n hj _ _ _ (by rw [List.length_set, lr]) (by simp) (fun i => key j n hj _ _ (lr y) i) o
end PEqualNP.Outside.L_meta_3250

theorem PEqualNP.Outside.L_meta_3250 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : Fin (9 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ) (x6 : Bool),   x2 ≠ (0 : Fin (9 : ℕ)) →     x2 ≠ (6 : Fin (9 : ℕ)) →       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           (10 : ℕ) ≤ x5 →             x5 < x4 →               x4 ≤ (10 : ℕ) + x3.size →                 (∀ x14 ∈ List.take (x4 - (10 : ℕ)) x3.gates, ↑x2 ∉ x14.inputs) →                   (∀ (x15 : Fin (9 : ℕ) → Bool),                       have x16 : Fin (9 : ℕ) → Bool := Function.update x15 x2 Bool.false;                       x1 x16 ≠ x1 (Function.update x15 x2 Bool.true) → (x3.wires (List.ofFn x16 ++ [x16 (0 : Fin (9 : ℕ)) || x16 (6 : Fin (9 : ℕ))])).getD x5 Bool.false = !x6) →                     ∃ (x16 : Fin (9 : ℕ) → Bool),                       have x17 : List Bool := List.ofFn x16 ++ [x16 (0 : Fin (9 : ℕ)) || x16 (6 : Fin (9 : ℕ))];                       have x18 : Bool := (x3.wires x17).getD x5 Bool.false;                       x3.eval (x17.set (↑x2) (if x6 = Bool.true then x16 x2 || x18 else x16 x2 && x18)) ≠ x1 x16 := by
  intro x1 j C n i b _ _ legal small h1 hi h2 hA _
  by_contra hne
  refine PEqualNP.Outside.L_meta_3250.ins j C n ⟨if b = true then PEqualNP.CircuitLowerBounds.GateOp.or else
    PEqualNP.CircuitLowerBounds.GateOp.and, [(j : ℕ), i]⟩ legal small (by omega) h2
    (by cases b <;> simp) hA fun y => ?_
  by_contra hh
  refine hne ⟨y, fun e => hh ?_⟩
  have ev : (C.wires (PEqualNP.Outside.L_meta_3250.bw y)).getD (j : ℕ) false = y j := by
    refine (PEqualNP.Outside.L_meta_3250.run_old C.gates _ _ (by simp [PEqualNP.Outside.L_meta_3250.bw]; omega)).trans ?_
    exact PEqualNP.Outside.L_meta_3250.rd y j
  have hj : (j : ℕ) < n := by omega
  simp only [List.map_cons, List.map_nil, ev, hj, hi, ite_true]
  refine Eq.trans ?_ (Eq.trans e (by simp [x1, PEqualNP.Outside.L_meta_3250.edge, Bool.or_assoc]))
  cases b <;> simp [PEqualNP.CircuitLowerBounds.GateOp.eval, PEqualNP.Outside.L_meta_3250.bw]
