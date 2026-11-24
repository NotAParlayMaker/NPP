import PEqualNP.Defs
-- First-negated-input certificate adapted from dsgallups, PR 6907, commit b18267b08b735cbbf99bee66e0f71d168c62ba9c, Apache-2.0.
-- The 131-row verifier below retains the 618 negated-input states reachable from the three prescribed OR ports.
-- Search framework and the plain 15-gate tables adapted from PEqualNP/Outside/L_meta_1667.lean, Apache-2.0.
namespace PEqualNP.Outside.L_meta_3863
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
  | 0,t,S => t = 0 ∧ proper target ∧ S = {target}
  | k+1,t,S => (∃ (u : Nat) (U : Finset Sig) (a : Sig), t = u+1 ∧ S = insert a U ∧ proper a ∧
        neg a ∉ insert a U ∧ Live target k u (insert (neg a) U)) ∨
      (∃ (U : Finset Sig) (a b : Sig) (d : Bool), S = insert a (insert b U) ∧ proper a ∧ proper b ∧
        a ≠ b ∧ bin d a b ∉ insert a (insert b U) ∧ Live target k t (insert (bin d a b) U))
theorem Live.stop {target : Sig} (hp : proper target) : Live target 0 0 {target} := ⟨rfl,hp,rfl⟩
theorem Live.unary {target : Sig} {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
    (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
    Live target (k+1) (t+1) (insert a U) := Or.inl ⟨t,U,a,rfl,rfl,ha,hfresh,tail⟩
theorem Live.binary {target : Sig} {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
    Live target (k+1) t (insert a (insert b U)) := Or.inr ⟨U,a,b,d,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {target : Sig} {motive : ∀ (k t : Nat) (S : Finset Sig), Live target k t S → Prop}
    (stop : ∀ (hp : proper target), motive 0 0 {target} (Live.stop hp))
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)),
      motive _ _ _ tail → motive _ _ _ (Live.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)),
      motive _ _ _ tail → motive _ _ _ (Live.binary ha hb hab hfresh tail))
    {k t : Nat} {S : Finset Sig} (h : Live target k t S) : motive k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,hp,rfl⟩ := h
    exact stop hp
  | succ k ih =>
    have hh := h
    rcases hh with ⟨u,U,a,rfl,rfl,ha,hf,tl⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tl⟩
    · exact unary ha hf tl (ih tl)
    · exact binary ha hb hab hf tl (ih tl)

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
  | 0,bank => bank = roots
  | p+1,bank => (∃ (b : List (Wire R)) (a : Wire R), bank = inv a :: b ∧ Reach roots p b ∧ Available b a) ∨
      (∃ (b : List (Wire R)) (a c : Wire R) (op : Bool), bank = combine op a c :: b ∧ Reach roots p b ∧
        Available b a ∧ Available b c)
theorem Reach.start {R} {roots : List (Wire R)} : Reach roots 0 roots := rfl
theorem Reach.one {R} {roots : List (Wire R)} {p : Nat} {bank : List (Wire R)} {a : Wire R}
    (h : Reach roots p bank) (ha : Available bank a) : Reach roots (p+1) (inv a :: bank) :=
  Or.inl ⟨bank,a,rfl,h,ha⟩
theorem Reach.two {R} {roots : List (Wire R)} {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool)
    (h : Reach roots p bank) (ha : Available bank a) (hb : Available bank b) :
    Reach roots (p+1) (combine op a b :: bank) := Or.inr ⟨bank,a,b,op,rfl,h,ha,hb⟩
theorem Reach.ind {R} {roots : List (Wire R)}
    {motive : ∀ (p : Nat) (bank : List (Wire R)), Reach roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (one : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R} (h : Reach roots p bank) (ha : Available bank a),
      motive _ _ h → motive _ _ (Reach.one h ha))
    (two : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (h : Reach roots p bank)
      (ha : Available bank a) (hb : Available bank b), motive _ _ h → motive _ _ (Reach.two op h ha hb))
    {p : Nat} {bank : List (Wire R)} (h : Reach roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    have hh := h
    obtain rfl : bank = roots := hh
    exact start
  | succ p ih =>
    have hh := h
    rcases hh with ⟨b,a,rfl,hb,ha⟩ | ⟨b,a,c,op,rfl,hb,ha,hc⟩
    · exact one hb ha (ih hb)
    · exact two op hb ha hc (ih hb)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (goal : Wire R) (s : Nat) (xs : List (Wire R)) : Prop :=
  ∀ P : Nat → List (Wire R) → Prop, P 0 [goal] →
    (∀ {s : Nat} {xs zs : List (Wire R)}, xs.Perm zs → P s xs → P s zs) →
    (∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool),
      P s (inv a :: kept save a rest) → P (s+1) (a::rest)) →
    (∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool),
      P s (combine op a b :: kept ka a (kept kb b rest)) → P (s+1) (a::b::rest)) → P s xs
theorem Run.stop {R} {goal : Wire R} : Run goal 0 [goal] := fun _ h0 _ _ _ => h0
theorem Run.perm {R} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run goal s xs) : Run goal s zs := fun P h0 hp h1 h2 => hp p (h P h0 hp h1 h2)
theorem Run.one {R} {goal : Wire R} {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool)
    (h : Run goal s (inv a :: kept save a rest)) : Run goal (s+1) (a::rest) :=
  fun P h0 hp h1 h2 => h1 save (h P h0 hp h1 h2)
theorem Run.two {R} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool)
    (h : Run goal s (combine op a b :: kept ka a (kept kb b rest))) : Run goal (s+1) (a::b::rest) :=
  fun P h0 hp h1 h2 => h2 op ka kb (h P h0 hp h1 h2)
theorem Run.ind {R} {goal : Wire R} {motive : ∀ (s : Nat) (xs : List (Wire R)), Run goal s xs → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs) (h : Run goal s xs),
      motive _ _ h → motive _ _ (Run.perm p h))
    (one : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool)
      (h : Run goal s (inv a :: kept save a rest)), motive _ _ h → motive _ _ (Run.one save h))
    (two : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool)
      (h : Run goal s (combine op a b :: kept ka a (kept kb b rest))), motive _ _ h →
      motive _ _ (Run.two op ka kb h))
    {s : Nat} {xs : List (Wire R)} (h : Run goal s xs) : motive s xs h := by
  have key : ∃ h' : Run goal s xs, motive s xs h' := by
    refine h (fun s xs => ∃ h' : Run goal s xs, motive s xs h') ⟨_,stop⟩ ?_ ?_ ?_
    · rintro s xs zs p ⟨h',m⟩
      exact ⟨_,perm p h' m⟩
    · rintro s a rest save ⟨h',m⟩
      exact ⟨_,one save h' m⟩
    · rintro s a b rest op ka kb ⟨h',m⟩
      exact ⟨_,two op ka kb h' m⟩
  exact key.2

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
def seed : Sig := neg (inputs.getD 0 zero)

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = !(sample r 0) := by decide +kernel
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

theorem seed_witness : ∀ i : Fin 9, i ≠ 0 →
    ((bit (absentRow i) graph != bit (presentRow i) graph) &&
    ((inputs++[seed]).all fun w => w == inputs.getD i.val zero ||
      bit (absentRow i) w == bit (presentRow i) w)) = true := by decide +kernel
def EssentialAt (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v
theorem split_roots {T : Sig} {k t S} (ws : List Sig) (x n : Sig) (h : Live T k t S)
    (sub : ∀ v ∈ S, v ∈ ws++[n])
    (ess : ∀ a ∈ ws, a ≠ x → EssentialAt T (ws++[n]) a) (r s : Row) (d : bit r T ≠ bit s T)
    (iso : ∀ v ∈ ws, v ≠ x → bit r v = bit s v) :
    S=ws.toFinset ∨ S=(ws++[n]).toFinset ∨ S=(ws.filter (fun a => a != x) ++ [n]).toFinset := by
  have all : ∀ a ∈ ws, a ≠ x → a ∈ S := by
    intro a ha hne
    obtain ⟨r,s,hd,hi⟩ := ess a ha hne
    exact raw_required h _ a sub r s hd hi
  have cover : ∀ v ∈ S, v ∈ ws ∨ v = n := by
    intro v hv
    simpa using sub v hv
  by_cases hn : n ∈ S <;> by_cases hx : x ∈ S
  · right; left
    ext a
    simp only [List.toFinset_append,Finset.mem_union,List.mem_toFinset,List.mem_singleton]
    refine ⟨cover a,?_⟩
    rintro (ha | rfl)
    · by_cases e : a=x
      · exact e ▸ hx
      · exact all a ha e
    · exact hn
  · right; right
    ext a
    simp only [List.toFinset_append,Finset.mem_union,List.mem_toFinset,List.mem_singleton,
      List.mem_filter,bne_iff_ne]
    constructor
    · intro ha
      rcases cover a ha with hw | e
      · exact Or.inl ⟨hw,fun e => hx (e ▸ ha)⟩
      · exact Or.inr e
    · rintro (⟨ha,e⟩ | rfl)
      · exact all a ha e
      · exact hn
  · left
    ext a
    simp only [List.mem_toFinset]
    constructor
    · intro ha
      exact (cover a ha).resolve_right (fun e => hn (e ▸ ha))
    · intro ha
      by_cases e : a=x
      · exact e ▸ hx
      · exact all a ha e
  · exfalso
    obtain ⟨v,hv,hd⟩ := live_row_difference h d
    have hw := (cover v hv).resolve_right (fun e => hn (e ▸ hv))
    exact hd (iso v hw (fun e => hx (e ▸ hv)))

theorem x0_row : bit (Fin.ofNat 512 2) graph ≠ bit (Fin.ofNat 512 3) graph := by decide +kernel
theorem x0_all : (inputs.all fun v => v == inputs.getD 0 zero ||
    bit (Fin.ofNat 512 2) v == bit (Fin.ofNat 512 3) v) = true := by decide +kernel
theorem x0_iso : ∀ v ∈ inputs, v ≠ inputs.getD 0 zero →
    bit (Fin.ofNat 512 2) v = bit (Fin.ofNat 512 3) v := by
  intro v hv hne
  have h := List.all_eq_true.mp x0_all v hv
  simp only [Bool.or_eq_true,beq_iff_eq] at h
  exact h.resolve_left hne
def lowInputs := inputs.filter (fun a => a != inputs.getD 0 zero) ++ [seed]

theorem all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[seed]) :
    S=inputs.toFinset ∨ S=(inputs++[seed]).toFinset ∨ S=lowInputs.toFinset := by
  apply split_roots inputs (inputs.getD 0 zero) seed h sub _ _ _ x0_row x0_iso
  intro a ha hne
  rw [←input_list,List.mem_ofFn] at ha
  obtain ⟨i,rfl⟩ := ha
  have hi : i ≠ 0 := fun e => hne (by rw [e]; rfl)
  have cut := seed_witness i hi
  simp only [Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at cut
  exact ⟨absentRow i,presentRow i,cut.1,fun v hv hne => (cut.2 v hv).resolve_left hne⟩

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
def negInput : Sig := neg (inputs.getD 0 zero)
def vars (m : Nat) := (selected m).map Prod.snd ++ (if m.testBit 9 then [negInput] else [])
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
def colFree (m z o : Nat) :=
  let f := m ^^^ (m &&& (z ||| o))
  if (z ||| o).testBit 0 then f &&& 511 else f
def chartGoal (m : Nat) : Sig := graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def remapOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem remap_of {old rep L swaps} (ok : remapOK old rep swaps = true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L := by
  simp only [remapOK,Bool.and_eq_true] at ok
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


abbrev BoundPool := Sig × Nat × Nat × List Sig
abbrev BoundPool.domain (c : BoundPool) : Sig := c.1
abbrev BoundPool.bound (c : BoundPool) : Nat := c.2.1
abbrev BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
abbrev BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

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


abbrev Bits := BitVec 131
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 131 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 131 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 131 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 131 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 131 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 131 → Row) (d : Bool) (a b : Sig) :
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

def asRow (cols : Nat → Bits) (i : Fin 131) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 131) (j : Fin 9) :
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
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 131) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 131) :
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
    if (rs ||| column d z.2) != BitVec.allOnes 131 then true else
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
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 131 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 131) = false := by simp [sep]
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
    obtain ⟨_,_,rfl⟩ := h
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
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
  let row := (h/nb+sh)%slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


abbrev IndexTree (α : Type) := List α
abbrev IndexTree.read {α} (xs : IndexTree α) (i : Nat) : Option α := xs[i]?
abbrev IndexTree.values {α} (xs : IndexTree α) : List α := xs
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : IndexTree.read tree i=some x) :
    x ∈ IndexTree.values tree := List.mem_of_getElem? e

abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × Array (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
abbrev Forest.mask (g : Forest) : Nat := g.1
abbrev Forest.cap (g : Forest) : Nat := g.2.1
abbrev Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1
abbrev Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1
abbrev Forest.autos (g : Forest) : Array (List Nat) := g.2.2.2.2.1
abbrev Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1
abbrev Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  if g.mask.testBit 9 then ws ++ [dneg (ws.getD 0 defaultDecor)] else ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  have base := raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · rcases List.mem_append.mp ha with hm | hm
    · exact base _ hm
    · obtain rfl := List.mem_singleton.mp hm
      exact faithful_neg (faithful_get base 0)
  · exact base _ ha

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) := liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 131) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 131) (hq : chartSamples m q = 0) :
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
  (IndexTree.read g.cols idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ (IndexTree.values g.cols), Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : IndexTree.read g.cols i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (IndexTree.read_mem g.cols e)

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
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ (IndexTree.values g.cols), Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
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
    obtain ⟨_,_,rfl⟩ := h
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
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

def goodRange (g:Forest) (k start count:Nat):Prop:=
  ∀ (i : Nat), start ≤ i → i < start + count → nodeVerified g k i=true ∨ Impossible (targetOf g) k (stateSet g k i).toFinset
lemma goodPlain {g k start count} (ok:block g k start count=true):goodRange g k start count:=
  fun i lo hi=>Or.inl (block_at ok i lo hi)
lemma goodJoin {g k start a b} (l:goodRange g k start a) (r:goodRange g k (start+a) b):
    goodRange g k start (a+b):=by
  intro i lo hi
  by_cases c:i<start+a
  · exact l _ lo c
  · exact r _ (by omega) (by omega)
def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, goodRange g k 0 (g.levels k).1
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 131) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  (IndexTree.values g.cols).all (fun c => colCheck g.mask c prior) &&
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
    obtain yes|done:=rows 0 hk i (by omega) (by simpa using hi)
    swap;exact done
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact yes
  | succ k ih =>
    intro hk i hi
    obtain yes|done:=rows _ hk i (by omega) (by simpa using hi)
    swap;exact done
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact yes

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
def extendKnown (old : List (Nat × Nat)) (L : Nat) (remaps : List (Nat × List Nat)) :=
  remaps.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m remaps} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : remaps.all (fun v => remapOK v.1 m v.2) = true) :
    Known (extendKnown old L remaps) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact remap_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known [] := by simp [Known]
def lanePlace (v : Nat) (upper : Nat) := 2^132*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^132 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<132 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<132 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<132 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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

def fullMarks (r packed : Nat) := ((packed+r) >>> 131) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (132*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^132)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 132*(i+1)-132=132*i := by omega
      have ge : ¬132*(i+1)<132 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 131 = (a==BitVec.allOnes 131) := by
  by_cases h : a=BitVec.allOnes 131
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^131-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^131 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (132*i) =
      (f xs[i]==BitVec.allOnes 131) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^132*u+x+(2^132*v+1)=2^132*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^132 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬132*(i+1)+131<132 := by omega
      have di : 132*(i+1)+131-132=132*i+131 := by omega
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
theorem top_xor (a : Bits) : BitVec.allOnes 131 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 131).toNat) op
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
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 132) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (132*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 132) (i:=i) (by simpa using hi) _ ok.2
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
    let z := packedOp (r*(BitVec.allOnes 131).toNat) op a b'
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
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 131 then true
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
        packedColumn d (packedOp (r*(BitVec.allOnes 131).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 131
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
def goes (x y:Row) (w:Sig) := bit x w=true → bit y w=true
def upFour (r s u v:Row) (w:Sig) := goes r s w ∧ goes s u w ∧ goes u v w
lemma monoFor {T k t S} (h:Live T k t S) (zero:t=0) {x y:Row}
    (pos:bit x T=true) (negAt:bit y T=false) (all:∀w∈S,goes x y w) : False:=by
  obtain ⟨w,hw,yes,no⟩:=mono_row_difference h zero pos negAt
  exact Bool.noConfusion (no.symm.trans (all w hw yes))
lemma upBin {r s u v:Row} {a b:Sig} (ha:upFour r s u v a) (hb:upFour r s u v b) (d:Bool):
    upFour r s u v (bin d a b):=by
  have step (x y:Row) (i:goes x y a) (j:goes x y b):goes x y (bin d a b):=by
    unfold goes at *
    rw [bit_bin,bit_bin]
    cases d <;> simp_all <;> tauto
  exact ⟨step _ _ ha.1 hb.1,step _ _ ha.2.1 hb.2.1,step _ _ ha.2.2 hb.2.2⟩
theorem twoDescents {T k t S} (h:Live T k t S) (ht:t≤1) (r s u v:Row)
    (hr:bit r T=true) (hs:bit s T=false) (hu:bit u T=true) (hv:bit v T=false)
    (all:∀w∈S,upFour r s u v w):False:=by
  induction h using Live.ind with
  | stop hp=>exact Bool.noConfusion (hs.symm.trans ((all _ (Finset.mem_singleton_self _)).1 hr))
  | @unary k t U a ha hf tail ih=>
    have z:t=0:=by omega
    have oa:=all a (Finset.mem_insert_self _ _)
    cases hsa:bit s a
    · have hra:bit r a=false:=Bool.eq_false_iff.mpr (fun e=>Bool.noConfusion (hsa.symm.trans (oa.1 e)))
      apply monoFor tail z hr hs
      intro w hw;rcases Finset.mem_insert.mp hw with rfl|hw
      · simp [goes,bit_neg,hra,hsa]
      · exact (all _ (Finset.mem_insert_of_mem hw)).1
    · have hua:=oa.2.1 hsa;have hva:=oa.2.2 hua
      apply monoFor tail z hu hv
      intro w hw;rcases Finset.mem_insert.mp hw with rfl|hw
      · simp [goes,bit_neg,hua,hva]
      · exact (all _ (Finset.mem_insert_of_mem hw)).2.2
  | @binary k t U a b d ha hb hab fresh tail ih=>
    apply ih ht
    intro w hw;rcases Finset.mem_insert.mp hw with rfl|hw
    · exact upBin (all a (by simp)) (all b (by simp)) d
    · exact all w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))
def readRow (data j:Nat):Row:=Fin.ofNat 512 ((data >>> (9*j)) &&& 511)
def chainCheck (T:Sig) (k:Nat) (ws:List Sig) (data:Nat):Bool:=
  let r:=readRow data 0
  let s:=readRow data 1
  let u:=readRow data 2
  let v:=readRow data 3
  decide ws.Nodup && decide (k≤ws.length) &&
    bit r T && !(bit s T) && bit u T && !(bit v T) &&
    ws.all (fun w=>(!(bit r w) || bit s w) && (!(bit s w) || bit u w) && (!(bit u w) || bit v w))
lemma chainCheck_ok {T k ws data} (ok:chainCheck T k ws data=true):Impossible T k ws.toFinset:=by
  intro k' t lim h
  simp only [chainCheck,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨nd,cap⟩,r⟩,s⟩,u⟩,v⟩,all⟩:=ok
  have sz:=(live_size h).2
  rw [List.toFinset_card_of_nodup nd] at sz
  apply twoDescents h (by omega) _ _ _ _ r s u v
  intro w hw
  have a:=all w (List.mem_toFinset.mp hw)
  simp only [Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true'] at a
  unfold upFour goes
  obtain ⟨⟨x,y⟩,z⟩:=a
  exact ⟨fun o=>x.resolve_left (fun e=>Bool.noConfusion (e.symm.trans o)),
    fun o=>y.resolve_left (fun e=>Bool.noConfusion (e.symm.trans o)),
    fun o=>z.resolve_left (fun e=>Bool.noConfusion (e.symm.trans o))⟩
def listRange (start count:Nat):List Nat:=(List.range count).map (start+·)
def slower (hint:Nat→Nat) (start count:Nat):List Nat:=(listRange start count).filter (fun i=>hint i==0)
def linkedChecks (g:Forest) (k start count:Nat) (hint:Nat→Nat):Bool:=
  (listRange start count).all (fun i=>hint i==0 || chainCheck (targetOf g) k (stateSet g k i) (hint i))
def slowerContexts (g:Forest) (k start count:Nat) (hint:Nat→Nat):List NodeContext:=
  (slower hint start count).map (contextOf g k)
def weakHead (g:Forest) (k start count ar:Nat) (hint:Nat→Nat):Bool:=
  (slowerContexts g k start count hint).all (fun c=>c.2.1==ar && prelim (targetOf g) c)
lemma mixAt {g k start count ar hint}
    (direct:linkedChecks g k start count hint=true)
    (hd:weakHead g k start count ar hint=true)
    (h:runBatch k ar (slowerContexts g k start count hint)=true):goodRange g k start count:=by
  intro i lo hi
  have inside:i∈listRange start count:=List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩
  by_cases eq:hint i=0
  · left
    let xs:=slowerContexts g k start count hint
    have hm:contextOf g k i ∈ xs:=List.mem_map.mpr ⟨i,List.mem_filter.mpr ⟨inside,by simp [eq]⟩,rfl⟩
    obtain ⟨q,hq,e⟩:=List.getElem_of_mem hm
    have a:=List.all_eq_true.mp hd _ hm
    simp only [Bool.and_eq_true,beq_iff_eq] at a
    have hb:xs[q].1=k:=by rw [e];rfl
    have ha:xs[q].2.1=ar:=e ▸ a.1
    have hn:xs[q].2.2.1.length=ar:=e ▸ a.1
    rw [from_context,Bool.and_eq_true]
    refine ⟨a.2,?_⟩
    split
    · rfl
    · exact e ▸ runBatch_at hq hb ha hn h
  · right
    have dec:=List.all_eq_true.mp direct i inside
    simp only [Bool.or_eq_true,beq_iff_eq] at dec
    exact chainCheck_ok (dec.resolve_left eq)
def pieces (g:Forest) (k start n ar:Nat) (hint:Nat→Nat) : Nat→Prop
  | 0=>linkedChecks g k start n hint=true ∧ weakHead g k start n ar hint=true ∧ runBatch k ar (slowerContexts g k start n hint)=true
  | d+1=>pieces g k start (n/2) ar hint d ∧ pieces g k (start+n/2) (n-n/2) ar hint d
lemma piecesGood {g k start n ar hint d} (ok:pieces g k start n ar hint d):goodRange g k start n:=by
  induction d generalizing start n with
  | zero=>exact mixAt ok.1 ok.2.1 ok.2.2
  | succ d ih=>
    have z:=goodJoin (ih ok.1) (ih ok.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using z
def hintg191at7 (i:Nat):Nat:=if 11 ≤ i then 0 else (0xb95ead5eaba5dae57a000000000e87c2e171b57ab95cba2d369369000000000e0f168b4daa55aa553a2d36934ba4d368b47 >>> (36*(i % 64))) &&& 68719476735
def hintg383at8 (i:Nat):Nat:=if 11 ≤ i then 0 else (0x4221904830000000004120d02a14120d02a1000000000522950a8d522950a8d4a2550a8d48245028350285028342a35138b >>> (36*(i % 64))) &&& 68719476735
def hintg383at9 (i:Nat):Nat:=if 26 ≤ i then 0 else (0xc160f038949269148b0000000004a2550a8d4a2550a8d522950a8d4a2550a8d000000000522950a8d542a5128349269148b000000000422190483422190483502850283542a5128b422190483000000000000000000000000000000000000000000000000000000000000000000000000000000000 >>> (36*(i % 64))) &&& 68719476735
def hintdeadat9 (i:Nat):Nat:=if 4 ≤ i then 0 else (0xa0540a0d8945a29150a0540a07452a8542f >>> (36*(i % 64))) &&& 68719476735
def hintdeadat10 (i:Nat):Nat:=if 70 ≤ i then 0 else ((if i/64 < 1 then 0xa0540a210000000000502c120d000000000890582815000000000000000000000000000140a4120300000000000000000000000000082018040300000000000000000000000000000000000000000000009068140b0a0540a0d0a0540a0d09068140b884460309000000000000000000000000000000000000000000000000000000000000000020180403884460309140a412030a0540a0d0502c120d8945a29150905828150905828150502c120d48245028548245028560b148b454824502850502c120d140a4120b020180403140a4120b0a0540a072010804031008402031008402032010804030a0540a0702834120b140a4120b80c24120b40a140a0740a140a07000000000000000000000000000000000000000000000000000000 else 0x140b04825000000000890582815000000000000000000412804021) >>> (36*(i % 64))) &&& 68719476735
def hintn31at5 (i:Nat):Nat:=if 2 ≤ i then 0 else (0xf97dbe9f5f279bc5e3 >>> (36*(i % 64))) &&& 68719476735
def hintn189at6 (i:Nat):Nat:=if 3 ≤ i then 0 else (0xa556aa553ab55e8f4fb55ae974f >>> (36*(i % 64))) &&& 68719476735
def hintn191at7 (i:Nat):Nat:=if 25 ≤ i then 0 else (0xaa5568b4db05868351b05868351b25968b4daa5568b4d000000000a955aa955e572f93cdaa5568b6d000000000e97cae573b57ab95cbb95ead56bb05868343e0f168b4f000000000000000000000000000000000000000000000000000000b159ac965000000000000000000a251a8543 >>> (36*(i % 64))) &&& 68719476735
def hintn191at8 (i:Nat):Nat:=if 173 ≤ i then 0 else ((if i/64 < 1 then 0xa2d36934b000000000000000000a4d368b47aa5568bc5000000000a85468361000000000a955aa955000000000a85468343000000000b57ab95c3000000000a550e8361000000000000000000000000000a552e934d000000000b45868343000000000000000000000000000b25868351000000000000000000aa5568b4d000000000000000000000000000000000000000000000aa5468343000000000a150e8351000000000a956a954b000000000a251a8543000000000a150e8351000000000a956a954b000000000000000000a552e934d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else (if i/64 < 2 then 0xe0782c161000000000000000000000000000000000000aa5568bc5000000000e0782c161000000000e874783c5000000000000000000000000000000000000000000000b05868351000000000b85e2d169000000000000000000a251a8543a251a8543a251a8543a251a8543a251a8543a251a8543a85468343b05868343b05868343000000000000000000e4763a1f0000000000000000000000000000000000000aa753a1d8000000000a2d369369000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a4d368b55000000000e0f168b4da955aa955000000000000000000000000000000000000000000000 else 0xa150e8351a150e8361000000000000000000000000000000000000aa5568b4daa5568b4da150e8351aa5568b4da955aa955000000000b05868351000000000b85e2d169000000000000000000000000000aa5568bc5000000000a150e8361000000000000000000000000000000000000000000000000000000000000000aa5568bc5000000000a150e8361000000000a955aa955000000000a955aa955a955aa955a955aa955a955aa955a150e8351aa5568b4da955aa955000000000000000000b25968bc5000000000)) >>> (36*(i % 64))) &&& 68719476735
def hintn351at7 (i:Nat):Nat:=if 44 ≤ i then 0 else (0x5a2d54aad5a2d54aadd168f43a95a2d54aad000000000000000000000000000000000000000000000000000000000000000000000000da7d1e8f5d2f95caed000000000000000000556ab45a3000000000593c9e0f15a2d54aad592d968b5000000000000000000592d968b5000000000000000000582c542a3da6db65b3743e1e0f37038944a3d269b45aa52ab553ab72bb5d2ebd16a954bb72f974ba7d2f95cae7552e964b7d0ea552af000000000000000000000000000000000000000000000000000000 >>> (36*(i % 64))) &&& 68719476735
def hintn351at8 (i:Nat):Nat:=if 273 ≤ i then 0 else ((if i/64 < 2 then (if i/64 < 1 then 0x54ea743a3d0f85c2e300000000052ab552ab54ab54aa7000000000d168f43a9d96db68b5000000000d269b44a30000000000000000007a2d54aad000000000000000000782c542a3000000000000000000552ad53a9000000000000000000000000000000000000552ad52ad000000000000000000743a954a30000000007a3c5c3e1000000000da6c743e10000000000000000005a2d54aad0000000000000000005a2c542a3000000000000000000552ad53a9000000000d168f43e1000000000000000000592e954ab000000000552ad52ad000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0xd86c743a9000000000000000000556ab45a3d86c743e1552e964b3000000000592e954ab000000000d229944a37038944a35a29944a37438944a35229944a35229944a35229944a35229944a37038944a37038944a35229944a35229944a37038944a3743a954ab582c542a3582c542a37038944a37038944a300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000052ab553a9d2f95caed5a2d54aad00000000000000000000000000074bb5cbe5553a9d0ec000000000d0ea552ad000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if i/64 < 3 then 0x592d968b5000000000000000000000000000542e160b10000000005a2d54aad000000000592d968b5000000000000000000542e160b10000000005a2d54aad000000000592d968b5000000000000000000000000000552ad53a9000000000593c9e0f10000000000000000000000000005a2d54aad000000000592d968b5000000000000000000000000000000000000552ad53a9000000000593c9e0f10000000005128d42b1000000000000000000592e954ab000000000000000000592d968b5000000000000000000000000000783c5c3e1000000000593c9e0f10000000005128d42b15a2d54aad000000000592d968b57438944a3000000000000000000000000000783c5c3e1000000000d86c743e1000000000542e160b1000000000 else (if i/64 < 4 then 0x593c9e0f10000000005a2d54aadd168f43a97a3d5caad592e954ab0000000000000000000000000005a2d54aad5a2d54aad5a2d54aad5a2d54aad5a2d54aadd168f43a95a2d54aad5a2d54aadd86c743a9000000000000000000000000000000000000592e954ab000000000000000000542e160b10000000000000000005a2d54aad000000000000000000552ad53a9000000000d168f43e1000000000000000000d168f43a9000000000000000000000000000000000000000000000593c9e0f10000000005a2d54aad000000000000000000552ad52ad552ad52ad592d968b5592d968b5592d968b5592d968b5552ad52ad000000000783c5c3e1000000000d86c743e1000000000d86c743a9000000000 else 0x783c5c3e1000000000593c9e0f1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000552ad53a9000000000d168f43e1000000000))) >>> (36*(i % 64))) &&& 68719476735
def hintn487at7 (i:Nat):Nat:=if 21 ≤ i then 0 else (0x8d4ec34390000000000000000001d0f8783d0000000000000000008ec6c3a1b1c0e4321b6cf67339b2c168341b6c36934ba2ed763b1f8ed74ba5f8e4f0783f0000000000000000000000000000000000000000000003e1e8b85a000000000 >>> (36*(i % 64))) &&& 68719476735
def hintn487at8 (i:Nat):Nat:=if 105 ≤ i then 0 else ((if i/64 < 1 then 0xe078341b0e078341b0e078341b0e078341b0e078341b0e078341b2c168341b1e0f8743b0e078341b1c0e4321b1c0e4321b2c168341b0000000000000000006cb74bb5dcce763b5d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ea75329b0000000006c36934ba4ca743a1f1c0e4321b0000000003e1e4b3590000000000000000000000000008e4f078390000000000000000000000000001e0e4321b0000000000000000001d2e9349b0000000000d06c32390000000004d26d329d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0x1e0f43a9d0000000000000000000000000001d0f8783d0000000000000000000000000001d4ea351b0000000000000000001d1e8f0790000000000000000000000000000000000001d0f8783d0000000000000000000000000004d26d329d4d2e070390000000000000000000000000003c1e4b3590000000001d1e8f0790000000000000000000000000000000000001d2e9349b0000000000000000000000000001c0e4321b6c168341b1e078341b0e078341b0e078341b) >>> (36*(i % 64))) &&& 68719476735
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[(0x10,0x7fffffffffffffffffffffffffffffff7),(0x7fffffffffffffffffffffffffffffff9,0x8),(0x7ffffffffffffffffffffffffffffffef,0x7ffffffffffffffffffffffffffffffe5),(0x16,0x12),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g15columns : IndexTree ColumnInfo := []
def g15autos : Array (List Nat) := #[[],[33,48]]
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
def g31samples : Array (Bits × Bits) := #[(0x7ffffffffffffffffffffffffffffc9e5,0x7ffffffffffffffffffffffffffffc525),(0x27a,0xa58),(0x7ffffffffffffffffffffffffffffc58f,0x186),(0x7fffffffffffffffffffffffffffff771,0x7ffffffffffffffffffffffffffffd471),(0x3a9e,0x2a8a),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g31columns : IndexTree ColumnInfo := [(1,0,30,0,4),(2,0,29,0,4),(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]
def g31autos : Array (List Nat) := #[[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples : Array (Bits × Bits) := #[(0x7ffffffffffffffffffffffffffffffff,0x0),(0x7ffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x7ffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g47columns : IndexTree ColumnInfo := [(8,0,39,0,4)]
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[(0x7ffffffffffffffffffffffffffffffff,0x0),(0x7ffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x7ffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g55columns : IndexTree ColumnInfo := [(16,0,39,0,4)]
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[(0x7ffffffffffffffffffffffffffffffff,0x0),(0x7ffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x7ffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63columns : IndexTree ColumnInfo := [(32,0,31,0,7)]
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0x7fffffffffffffffffffffffffffff17b,0x13a),(0x7ffffffffffffffffffffffffffffe2a5,0x7ffffffffffffffffffffffffffffe281),(0x1c9e,0x181c),(0xd72,0x762),(0x0,0x0),(0x1dcc,0x1ec4),(0xf60,0xd70),(0x0,0x0),(0x0,0x0)]
def g111columns : IndexTree ColumnInfo := [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)]
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[(0x7ffffffffffffffffffffffffffffffff,0x0),(0x7ffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x7ffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g119columns : IndexTree ColumnInfo := [(4,0,115,0,5)]
def g119autos : Array (List Nat) := #[[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
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
def g189samples : Array (Bits × Bits) := #[(0x7fffffffffffffffffffffffffff3662b,0x7fffffffffffffffffffffffffff9e02b),(0x0,0x0),(0x7fffffffffffffffffffffffffffad83b,0x7fffffffffffffffffffffffffff2902b),(0x7fffffffffffffffffffffffffffced45,0x86d04),(0x513d2,0x412d0),(0x63da4,0x61d04),(0x0,0x0),(0x952dc,0x942d0),(0x0,0x0)]
def g189columns : IndexTree ColumnInfo := [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4),(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]
def g189autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples : Array (Bits × Bits) := #[(0x7ffffffffffffffffffffffffffffffff,0x0),(0x7ffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x7ffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g127columns : IndexTree ColumnInfo := [(32,0,95,0,8)]
def g127autos : Array (List Nat) := #[[],[101,66,16]]
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
def g191samples : Array (Bits × Bits) := #[(0x7fffffffffffffffd0c0c402004fef2db,0x7fffffffffffffff80804000200e6f9fd),(0x11b148275f1c286a0,0x11782c171f1000600),(0x7fffffffffffffffe531122c7040d21fd,0x7fffffffffffffffa40191604044901fd),(0x2c1e025583913b710,0x119c0a85a3812b202),(0x6c0e955b5db084440,0x6c22957a5c3080400),(0x648ab82dfe311c0a,0x245c8b22d9c110402),(0x0,0x0),(0x7fffffffffffffff92a03d9dae3060a05,0x12a2649d263060a00),(0x0,0x0)]
def g191columns : IndexTree ColumnInfo := [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7),(6,0,185,0,5),(8,0,183,0,8),(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5),(4,8,163,16,5),(14,0,177,0,4),(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5),(19,0,172,0,4),(24,0,167,0,7),(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4),(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5),(35,0,156,0,4),(40,0,151,0,5),(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8),(130,0,61,0,5),(4,128,27,32,5),(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5),(32,128,27,4,5),(161,0,30,0,4),(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)]
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
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
def g251samples : Array (Bits × Bits) := #[(0x7ffffffffffffffffffffffffffffffff,0x0),(0x7ffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x7ffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g251columns : IndexTree ColumnInfo := [(8,0,243,0,7)]
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[(0x7ffffffffffffffffffffffffffffffff,0x0),(0x7ffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x7ffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g255columns : IndexTree ColumnInfo := [(64,0,191,0,11)]
def g255autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
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
def g383samples : Array (Bits × Bits) := #[(0xc60dd118c12693bdc,0x727d0084122921c8),(0x7fffffffffffffff95cc2a44f8492746f,0x7ffffffffffffffe00c80e8498c025227),(0xf503f97a55354c080,0xf503f15a451548080),(0x7fffffffffffffff4a9202a30ea296fc7,0x28002a10a2a97e7c),(0x7fffffffffffffffe8508744b7d550001,0x7fffffffffffffffe8500544b4d540001),(0x7fffffffffffffffb0014017ba48c1e31,0x7fffffffffffffffb0000013ba4801e31),(0x18560541a2a3aaac98,0x18520601a222a8ac98),(0x0,0x0),(0x2aed1c8d455748122,0x85d1d44451540102)]
def g383columns : IndexTree ColumnInfo := [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9),(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6),(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5),(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8),(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11),(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5),(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5),(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5),(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7),(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11),(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5),(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7),(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6),(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5),(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5),(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)]
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
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
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
theorem s15_3_0 : goodRange g15 3 0 1 := by
  apply goodPlain
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl15_3 : goodRange g15 3 0 1 := s15_3_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k
  · exact goodPlain (rfl : block g15 0 0 0 = true)
  · exact goodPlain (rfl : block g15 1 0 0 = true)
  · exact goodPlain (rfl : block g15 2 0 0 = true)
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
theorem s31_5_0 : goodRange g31 5 0 1 := by
  apply goodPlain
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : goodRange g31 5 1 2 := by
  apply goodPlain
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_5 : goodRange g31 5 0 3 := (@goodJoin g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_6_0 : goodRange g31 6 0 1 := by
  apply goodPlain
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_6 : goodRange g31 6 0 1 := s31_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · exact goodPlain (rfl : block g31 0 0 0 = true)
  · exact goodPlain (rfl : block g31 1 0 0 = true)
  · exact goodPlain (rfl : block g31 2 0 0 = true)
  · exact goodPlain (rfl : block g31 3 0 0 = true)
  · exact goodPlain (rfl : block g31 4 0 0 = true)
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
theorem s111_6_0 : goodRange g111 6 0 1 := by
  apply goodPlain
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl111_6 : goodRange g111 6 0 1 := s111_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · exact goodPlain (rfl : block g111 0 0 0 = true)
  · exact goodPlain (rfl : block g111 1 0 0 = true)
  · exact goodPlain (rfl : block g111 2 0 0 = true)
  · exact goodPlain (rfl : block g111 3 0 0 = true)
  · exact goodPlain (rfl : block g111 4 0 0 = true)
  · exact goodPlain (rfl : block g111 5 0 0 = true)
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
theorem s189_6_0 : goodRange g189 6 0 1 := by
  apply goodPlain
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : goodRange g189 6 1 2 := by
  apply goodPlain
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_6 : goodRange g189 6 0 3 := (@goodJoin g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_7_0 : goodRange g189 7 0 1 := by
  apply goodPlain
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_7 : goodRange g189 7 0 1 := s189_7_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · exact goodPlain (rfl : block g189 0 0 0 = true)
  · exact goodPlain (rfl : block g189 1 0 0 = true)
  · exact goodPlain (rfl : block g189 2 0 0 = true)
  · exact goodPlain (rfl : block g189 3 0 0 = true)
  · exact goodPlain (rfl : block g189 4 0 0 = true)
  · exact goodPlain (rfl : block g189 5 0 0 = true)
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
theorem s191_6_0 : goodRange g191 6 0 1 := by
  apply goodPlain
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_6 : goodRange g191 6 0 1 := s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_0 : goodRange g191 7 0 13 := by
  apply piecesGood (hint:=hintg191at7) (ar:=7) (d:=1)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : goodRange g191 7 13 15 := by
  apply goodPlain
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_7 : goodRange g191 7 0 28 := (@goodJoin g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_0 : goodRange g191 8 0 7 := by
  apply goodPlain
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : goodRange g191 8 7 61 := by
  apply goodPlain
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : goodRange g191 8 68 32 := by
  apply goodPlain
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_8 : goodRange g191 8 0 100 := (@goodJoin g191 8 0 68 32 (@goodJoin g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_0 : goodRange g191 9 0 3 := by
  apply goodPlain
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : goodRange g191 9 3 9 := by
  apply goodPlain
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_9 : goodRange g191 9 0 12 := (@goodJoin g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_10_0 : goodRange g191 10 0 1 := by
  apply goodPlain
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_10 : goodRange g191 10 0 1 := s191_10_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact goodPlain (rfl : block g191 0 0 0 = true)
  · exact goodPlain (rfl : block g191 1 0 0 = true)
  · exact goodPlain (rfl : block g191 2 0 0 = true)
  · exact goodPlain (rfl : block g191 3 0 0 = true)
  · exact goodPlain (rfl : block g191 4 0 0 = true)
  · exact goodPlain (rfl : block g191 5 0 0 = true)
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
theorem s383_8_0 : goodRange g383 8 0 23 := by
  apply piecesGood (hint:=hintg383at8) (ar:=8) (d:=2)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : goodRange g383 8 23 2 := by
  apply goodPlain
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_8 : goodRange g383 8 0 25 := (@goodJoin g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_0 : goodRange g383 9 0 9 := by
  apply goodPlain
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : goodRange g383 9 9 75 := by
  apply piecesGood (hint:=hintg383at9) (ar:=9) (d:=4)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : goodRange g383 9 84 7 := by
  apply goodPlain
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_9 : goodRange g383 9 0 91 := (@goodJoin g383 9 0 84 7 (@goodJoin g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_0 : goodRange g383 10 0 5 := by
  apply goodPlain
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : goodRange g383 10 5 16 := by
  apply goodPlain
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : goodRange g383 10 21 20 := by
  apply goodPlain
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_10 : goodRange g383 10 0 41 := (@goodJoin g383 10 0 21 20 (@goodJoin g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_0 : goodRange g383 11 0 1 := by
  apply goodPlain
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : goodRange g383 11 1 5 := by
  apply goodPlain
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_11 : goodRange g383 11 0 6 := (@goodJoin g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_12_0 : goodRange g383 12 0 1 := by
  apply goodPlain
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_12 : goodRange g383 12 0 1 := s383_12_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k
  · exact goodPlain (rfl : block g383 0 0 0 = true)
  · exact goodPlain (rfl : block g383 1 0 0 = true)
  · exact goodPlain (rfl : block g383 2 0 0 = true)
  · exact goodPlain (rfl : block g383 3 0 0 = true)
  · exact goodPlain (rfl : block g383 4 0 0 = true)
  · exact goodPlain (rfl : block g383 5 0 0 = true)
  · exact goodPlain (rfl : block g383 6 0 0 = true)
  · exact goodPlain (rfl : block g383 7 0 0 = true)
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
def deadsamples : Array (Bits × Bits) := #[(0x1c8d4051c0de200a4a1521a9a552,0xb404180ce00084a38408fe044),(0x7fffff112d21048047165d40186c406a3,0x7ffffe150821240006161940101401ea3),(0x7fffff8afe10211224b0e6a32141b6019,0x10a64100310202066a522c394010),(0x38080ec9485c608946ad24109ee,0x888e488c4c408142cd20085aa),(0x7fffffdf433cb47193ff526432d701a11,0x7fffffdf4330a47113bf520432d701a11),(0x7fffff0509d24528184c731546a50d729,0x7fffff0209920500184463147b2401709),(0x102a12c429c39cba53fcd22d0108,0x102a10c429c19c9a437cd22d0108),(0x19253f877478f08d004086a8e2,0x19241f867478b084004086a8e2),(0x7602e02a04aa311a8880d9872d4,0x340661a022a230188800d906054)]
def deadcolumns : IndexTree ColumnInfo := [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12),(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12),(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7),(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12),(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9),(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6),(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11),(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7),(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8),(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6),(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8),(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6),(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8),(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13),(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8),(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7),(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7),(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13),(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9),(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5),(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6),(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11),(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8),(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11),(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8),(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7),(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5),(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6),(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6),(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9),(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5),(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]
def deadautos : Array (List Nat) := #[[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
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
theorem sdead8_0 : goodRange dead 8 0 2 := by
  apply goodPlain
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead8 : goodRange dead 8 0 2 := sdead8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_0 : goodRange dead 9 0 12 := by
  apply piecesGood (hint:=hintdeadat9) (ar:=9) (d:=1)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_12 : goodRange dead 9 12 13 := by
  apply goodPlain
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead9 : goodRange dead 9 0 25 := (@goodJoin dead 9 0 12 13 sdead9_0 sdead9_12)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_0 : goodRange dead 10 0 6 := by
  apply goodPlain
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_6 : goodRange dead 10 6 36 := by
  apply piecesGood (hint:=hintdeadat10) (ar:=10) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_42 : goodRange dead 10 42 36 := by
  apply piecesGood (hint:=hintdeadat10) (ar:=10) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_78 : goodRange dead 10 78 35 := by
  apply goodPlain
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_113 : goodRange dead 10 113 36 := by
  apply goodPlain
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_149 : goodRange dead 10 149 7 := by
  apply goodPlain
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead10 : goodRange dead 10 0 156 := (@goodJoin dead 10 0 149 7 (@goodJoin dead 10 0 113 36 (@goodJoin dead 10 0 78 35 (@goodJoin dead 10 0 42 36 (@goodJoin dead 10 0 6 36 sdead10_0 sdead10_6) sdead10_42) sdead10_78) sdead10_113) sdead10_149)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_0 : goodRange dead 11 0 4 := by
  apply goodPlain
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_4 : goodRange dead 11 4 36 := by
  apply goodPlain
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_40 : goodRange dead 11 40 15 := by
  apply goodPlain
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_55 : goodRange dead 11 55 36 := by
  apply goodPlain
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_91 : goodRange dead 11 91 36 := by
  apply goodPlain
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_127 : goodRange dead 11 127 29 := by
  apply goodPlain
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_156 : goodRange dead 11 156 27 := by
  apply goodPlain
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead11 : goodRange dead 11 0 183 := (@goodJoin dead 11 0 156 27 (@goodJoin dead 11 0 127 29 (@goodJoin dead 11 0 91 36 (@goodJoin dead 11 0 55 36 (@goodJoin dead 11 0 40 15 (@goodJoin dead 11 0 4 36 sdead11_0 sdead11_4) sdead11_40) sdead11_55) sdead11_91) sdead11_127) sdead11_156)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_0 : goodRange dead 12 0 3 := by
  apply goodPlain
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_3 : goodRange dead 12 3 14 := by
  apply goodPlain
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_17 : goodRange dead 12 17 15 := by
  apply goodPlain
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead12 : goodRange dead 12 0 32 := (@goodJoin dead 12 0 17 15 (@goodJoin dead 12 0 3 14 sdead12_0 sdead12_3) sdead12_17)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_0 : goodRange dead 13 0 1 := by
  apply goodPlain
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_1 : goodRange dead 13 1 3 := by
  apply goodPlain
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead13 : goodRange dead 13 0 4 := (@goodJoin dead 13 0 1 3 sdead13_0 sdead13_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead14_0 : goodRange dead 14 0 1 := by
  apply goodPlain
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead14 : goodRange dead 14 0 1 := sdead14_0
theorem tablesdead : checkedTables dead 14 := by
  intro k hk
  interval_cases k
  · exact goodPlain (rfl : block dead 0 0 0 = true)
  · exact goodPlain (rfl : block dead 1 0 0 = true)
  · exact goodPlain (rfl : block dead 2 0 0 = true)
  · exact goodPlain (rfl : block dead 3 0 0 = true)
  · exact goodPlain (rfl : block dead 4 0 0 = true)
  · exact goodPlain (rfl : block dead 5 0 0 = true)
  · exact goodPlain (rfl : block dead 6 0 0 = true)
  · exact goodPlain (rfl : block dead 7 0 0 = true)
  · exact alldead8
  · exact alldead9
  · exact alldead10
  · exact alldead11
  · exact alldead12
  · exact alldead13
  · exact alldead14
theorem dead_start {prior : Nat → Nat}
    (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid dead prior=true) (checks : checkedTables dead 14) :
    Impossible graph 14 inputs.toFinset := by
  have noRun := root_index (g:=dead) low geometry checks (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf dead=graph := by decide +kernel
  exact tgt ▸ noRun

theorem live_reach {T : Sig} (hp : proper T) {k t} {ws : List Sig} (nd : ws.Nodup)
    (h : Live T k t ws.toFinset) :
    ∃ q bank, Reach (ws.map observe) q bank ∧ Available bank (observe T) ∧ q ≤ k := by
  obtain ⟨q,bank,hr,ha,hl⟩ := contraction (observe_proper hp) (list_run h ws nd rfl)
    (ws.map observe) (Reach.start) (fun a ha => Or.inl ha)
  exact ⟨q,bank,hr,ha,by omega⟩

theorem lower_split {T : Sig} {ws : List Sig} {x n : Sig} {L : Nat} (hp : proper T) (nd : ws.Nodup)
    (ess : ∀ a ∈ ws, a ≠ x → Essential T (ws++[n]) a) (r s : Row) (d : bit r T ≠ bit s T)
    (iso : ∀ v ∈ ws, v ≠ x → bit r v = bit s v)
    (plain : Lower ws T (L+1)) (both : Impossible T L (ws++[n]).toFinset)
    (only : Impossible T L (ws.filter (fun a => a != x) ++ [n]).toFinset) :
    Lower (ws++[n]) T (L+1) := by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live hp h ha
  by_contra! small
  rcases split_roots ws x n run hs ess r s d iso with e | e | e <;> subst e
  · obtain ⟨q,bk,hr,hb,hq⟩ := live_reach hp nd run
    have := plain q bk hr hb
    omega
  · exact both k t (by omega) run
  · exact only k t (by omega) run

theorem reach_extra {ws : List (Wire Row)} {n : Wire Row} {a : Wire Row} (ha : a ∈ ws) (hn : n = inv a)
    {p bank} (h : Reach (ws++[n]) p bank) :
    ∃ out, Reach ws (p+1) out ∧ ∀ v ∈ bank, v ∈ out := by
  induction h using Reach.ind with
  | start =>
    refine ⟨inv a :: ws,Reach.one Reach.start (Or.inl ha),?_⟩
    intro v hv
    rcases List.mem_append.mp hv with h | h
    · exact List.mem_cons_of_mem _ h
    · rw [List.mem_singleton.mp h,hn]
      exact List.mem_cons_self
  | one h hv ih =>
    obtain ⟨out,hr,hs⟩ := ih
    refine ⟨_,Reach.one hr (hv.imp (hs _) id),?_⟩
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hs _ hv)
  | two op h hv hw ih =>
    obtain ⟨out,hr,hs⟩ := ih
    refine ⟨_,Reach.two op hr (hv.imp (hs _) id) (hw.imp (hs _) id),?_⟩
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hs _ hv)

theorem lower_weak {T : Sig} {ws : List Sig} {x : Sig} {L : Nat} (hx : x ∈ ws)
    (h : Lower ws T (L+1)) : Lower (ws++[neg x]) T L := by
  intro p bank hr ha
  rw [List.map_append] at hr
  obtain ⟨out,ho,hs⟩ := reach_extra (a:=observe x) (List.mem_map_of_mem hx) (obs_neg x) hr
  have := h (p+1) out ho (ha.imp (hs _) id)
  omega

def x0 : Sig := inputs.getD 0 zero
def weakOK (old : List (Nat × Nat)) (e : Nat × Nat) :=
  (vars e.1 == vars (e.1-512) ++ [neg x0]) && (vars (e.1-512)).contains x0 &&
    (graphGoal e.1 == graphGoal (e.1-512)) && (boundsBefore old (e.1-512) == e.2+1)
theorem addWeak {old : List (Nat × Nat)} (es : List (Nat × Nat)) (previous : Known old)
    (ok : es.all (weakOK old) = true) : Known (es ++ old) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · have w := List.all_eq_true.mp ok e hx
    simp only [weakOK,Bool.and_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at w
    have low := before_sound old previous (e.1-512)
    rw [w.2] at low
    rw [w.1.1.1,w.1.2]
    exact lower_weak w.1.1.2 low
  · exact previous e h

def splitOK (g : Forest) (m hints : Nat) (r s : Row) (old : List (Nat × Nat)) (i j : Nat) :=
  (vars g.mask == vars m ++ [neg x0]) && decide ((vars m).Nodup) && properB (targetOf g) &&
    (graphGoal m == targetOf g) && (boundsBefore old m == g.cap+1) &&
    ((vars m).all (fun a => a==x0 || ((graphPairs (m-1) hints).map Prod.fst).contains a)) &&
    checkEssential (targetOf g) (vars g.mask) (graphPairs (m-1) hints) &&
    (bit r (targetOf g) != bit s (targetOf g)) && (vars m).all (fun v => v==x0 || bit r v == bit s v) &&
    indexedRoot g g.cap i (vars g.mask) &&
    indexedRoot g g.cap j ((vars m).filter (fun a => a != x0) ++ [neg x0])

theorem lower_forest9 {g : Forest} {old m hints r s i j} (previous : Known old)
    (geom : graphValid g (boundsBefore old) = true) (blocks : checkedTables g g.cap)
    (ok : splitOK g m hints r s old i j = true) : Lower (vars g.mask) (graphGoal g.mask) (g.cap+1) := by
  simp only [splitOK,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,bne_iff_ne,List.all_eq_true,
    Bool.or_eq_true,List.contains_eq_mem] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv,nd⟩,hp⟩,hg⟩,hb⟩,hall⟩,hess⟩,hd⟩,hiso⟩,ia⟩,ib⟩ := ok
  have low := before_sound old previous
  have plain := low m
  rw [hb,hg] at plain
  have A := root_index low geom blocks (Nat.le_refl _) ia
  have B := root_index low geom blocks (Nat.le_refl _) ib
  rw [hv] at A hess
  have all := essential_ok hess
  change Lower (vars g.mask) (targetOf g) (g.cap+1)
  rw [hv]
  apply lower_split (x:=x0) (proper_of _ hp) nd _ r s hd _ plain A B
  · intro a ha hne
    exact all a (List.mem_toFinset.mpr ((hall a ha).resolve_left hne))
  · intro v hv hne
    exact (hiso v hv).resolve_left hne

def n15d3 (i : Nat) : Nat := 0xa3df
def n15l3 : Packing := (2,0,0,0,0,3,0,n15d3)
def n15samples : Array (Bits × Bits) := #[(0x7ffffffffffffffffffffffffffffffff,0x0),(0x7ffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def n15columns : List ColumnInfo := []
def n15autos : Array (List Nat) := #[[],[48,33]]
def n15levels : Nat → Packing
  | 3 => n15l3
  | _ => emptyPacking
def n15index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def n15 : Forest := (527,3,fun j => n15samples[j]?.getD (0,0),n15columns,n15autos,n15levels,n15index)
set_option maxHeartbeats 0 in
theorem geomn15 : graphValid n15 (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn153_0 : goodRange n15 3 0 1 := by
  apply goodPlain
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn153_1 : goodRange n15 3 1 1 := by
  apply goodPlain
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alln153 : goodRange n15 3 0 2 := (@goodJoin n15 3 0 1 1 sn153_0 sn153_1)
theorem tablesn15 : checkedTables n15 3 := by
  intro k hk
  interval_cases k
  · exact goodPlain (rfl : block n15 0 0 0 = true)
  · exact goodPlain (rfl : block n15 1 0 0 = true)
  · exact goodPlain (rfl : block n15 2 0 0 = true)
  · exact alln153
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lown15 : Lower (vars 527) (graphGoal 527) 4 :=
  lower_forest9 (g:=n15) (m:=15) (hints:=8993) (r:=2) (s:=3) (i:=0) (j:=1) valid383 geomn15 tablesn15 (by decide +kernel)
def mapsn15 : List (Nat × List Nat) := [(527,[]),(541,[50,65]),(647,[115,99,83,67]),(677,[114,33,97,82,50,65]),(793,[131,115,99,50,82,65]),(865,[130,33,113,99,82,65])]
def knownn15 := extendKnown known383 4 mapsn15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validn15 : Known knownn15 := extendKnown_ok valid383 lown15 (by decide +kernel)
def n23d3 (i : Nat) : Nat := 0xa3df
def n23l3 : Packing := (2,0,0,0,0,3,0,n23d3)
def n23samples : Array (Bits × Bits) := #[(0x7ffffffffffffffffffffffffffffffff,0x0),(0x7ffffffffffffffffffffffffffffffff,0x7ffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def n23columns : List ColumnInfo := []
def n23autos : Array (List Nat) := #[[],[16,66]]
def n23levels : Nat → Packing
  | 3 => n23l3
  | _ => emptyPacking
def n23index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def n23 : Forest := (535,3,fun j => n23samples[j]?.getD (0,0),n23columns,n23autos,n23levels,n23index)
set_option maxHeartbeats 0 in
theorem geomn23 : graphValid n23 (boundsBefore knownn15) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn233_0 : goodRange n23 3 0 1 := by
  apply goodPlain
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn233_1 : goodRange n23 3 1 1 := by
  apply goodPlain
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alln233 : goodRange n23 3 0 2 := (@goodJoin n23 3 0 1 1 sn233_0 sn233_1)
theorem tablesn23 : checkedTables n23 3 := by
  intro k hk
  interval_cases k
  · exact goodPlain (rfl : block n23 0 0 0 = true)
  · exact goodPlain (rfl : block n23 1 0 0 = true)
  · exact goodPlain (rfl : block n23 2 0 0 = true)
  · exact alln233
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lown23 : Lower (vars 535) (graphGoal 535) 4 :=
  lower_forest9 (g:=n23) (m:=23) (hints:=289) (r:=2) (s:=3) (i:=0) (j:=1) validn15 geomn23 tablesn23 (by decide +kernel)
def mapsn23 : List (Nat × List Nat) := [(535,[]),(539,[50,65]),(551,[84]),(569,[65,33,82,49]),(611,[66,100,82,50]),(675,[114,33,97,82,50,65]),(689,[114,33,97,82,49]),(817,[130,114,33,97,82,49])]
def knownn23 := extendKnown knownn15 4 mapsn23
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validn23 : Known knownn23 := extendKnown_ok validn15 lown23 (by decide +kernel)
def n31d5 (i : Nat) : Nat := 0x5285e957d445f211
def n31l5 : Packing := (3,1,3,0,0,4,0,n31d5)
def n31d6 (i : Nat) : Nat := 0x63441680fbf
def n31l6 : Packing := (2,0,3,0,0,5,0,n31d6)
def hashn31l6 (i : Nat) : Nat := 0xd5f40780000649c0
def n31samples : Array (Bits × Bits) := #[(0x7fffffffffffffffffffffffffffffd4f,0x7fffffffffffffffffffffffffffffc47),(0x3f0,0x390),(0x7fffffffffffffffffffffffffffffc3f,0x2e),(0x7ffffffffffffffffffffffffffffffc5,0x7ffffffffffffffffffffffffffffff41),(0x2ba,0xb8),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def n31columns : List ColumnInfo := [(1,0,30,0,4),(2,0,541,0,4),(4,0,539,0,4),(8,0,535,0,4),(16,0,527,0,4)]
def n31autos : Array (List Nat) := #[[],[65,50],[16,66],[64,65,66,67],[32,67],[48,65,50,67],[48,33],[32,49,66,67],[16,33,50,67],[64,49]]
def n31levels : Nat → Packing
  | 5 => n31l5
  | 6 => n31l6
  | _ => emptyPacking
def n31index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 4 8 2 7 2 1 (hashn31l6)
  | _ => fun _ => none
def n31 : Forest := (543,6,fun j => n31samples[j]?.getD (0,0),n31columns,n31autos,n31levels,n31index)
set_option maxHeartbeats 0 in
theorem geomn31 : graphValid n31 (boundsBefore knownn23) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn315_0 : goodRange n31 5 0 3 := by
  apply piecesGood (hint:=hintn31at5) (ar:=5) (d:=0)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alln315 : goodRange n31 5 0 3 := sn315_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn316_0 : goodRange n31 6 0 1 := by
  apply goodPlain
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn316_1 : goodRange n31 6 1 1 := by
  apply goodPlain
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alln316 : goodRange n31 6 0 2 := (@goodJoin n31 6 0 1 1 sn316_0 sn316_1)
theorem tablesn31 : checkedTables n31 6 := by
  intro k hk
  interval_cases k
  · exact goodPlain (rfl : block n31 0 0 0 = true)
  · exact goodPlain (rfl : block n31 1 0 0 = true)
  · exact goodPlain (rfl : block n31 2 0 0 = true)
  · exact goodPlain (rfl : block n31 3 0 0 = true)
  · exact goodPlain (rfl : block n31 4 0 0 = true)
  · exact alln315
  · exact alln316
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lown31 : Lower (vars 543) (graphGoal 543) 7 :=
  lower_forest9 (g:=n31) (m:=31) (hints:=17185) (r:=2) (s:=3) (i:=0) (j:=1) validn23 geomn31 tablesn31 (by decide +kernel)
def mapsn31 : List (Nat × List Nat) := [(543,[]),(679,[115,67,100,83]),(825,[131,115,65,50,98,81]),(867,[131,50,66,116,99,82])]
def knownn31 := extendKnown knownn23 7 mapsn31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validn31 : Known knownn31 := extendKnown_ok validn23 lown31 (by decide +kernel)
def n187d5 (i : Nat) : Nat := 0x2f561
def n187l5 : Packing := (1,1,1,0,0,0,0,n187d5)
def n187d6 (i : Nat) : Nat := 0x10c2e3f7f
def n187l6 : Packing := (2,0,1,0,0,3,0,n187d6)
def hashn187l6 (i : Nat) : Nat := 0x4
def n187samples : Array (Bits × Bits) := #[(0x7fffffffffffffffffffffffffffffbc3,0x2c2),(0x7fffffffffffffffffffffffffffffa1f,0x7fffffffffffffffffffffffffffff81d),(0x0,0x0),(0x7fffffffffffffffffffffffffffffc27,0x7fffffffffffffffffffffffffffff807),(0x57c,0x538),(0xb8,0x28),(0x0,0x0),(0x758,0x750),(0x0,0x0)]
def n187columns : List ColumnInfo := [(10,0,689,0,4),(130,0,569,0,4)]
def n187autos : Array (List Nat) := #[[],[115,84]]
def n187levels : Nat → Packing
  | 5 => n187l5
  | 6 => n187l6
  | _ => emptyPacking
def n187index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 1 0 6 1 1 (hashn187l6)
  | _ => fun _ => none
def n187 : Forest := (699,6,fun j => n187samples[j]?.getD (0,0),n187columns,n187autos,n187levels,n187index)
set_option maxHeartbeats 0 in
theorem geomn187 : graphValid n187 (boundsBefore knownn31) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1875_0 : goodRange n187 5 0 1 := by
  apply goodPlain
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alln1875 : goodRange n187 5 0 1 := sn1875_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1876_0 : goodRange n187 6 0 1 := by
  apply goodPlain
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1876_1 : goodRange n187 6 1 1 := by
  apply goodPlain
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alln1876 : goodRange n187 6 0 2 := (@goodJoin n187 6 0 1 1 sn1876_0 sn1876_1)
theorem tablesn187 : checkedTables n187 6 := by
  intro k hk
  interval_cases k
  · exact goodPlain (rfl : block n187 0 0 0 = true)
  · exact goodPlain (rfl : block n187 1 0 0 = true)
  · exact goodPlain (rfl : block n187 2 0 0 = true)
  · exact goodPlain (rfl : block n187 3 0 0 = true)
  · exact goodPlain (rfl : block n187 4 0 0 = true)
  · exact alln1875
  · exact alln1876
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lown187 : Lower (vars 699) (graphGoal 699) 7 :=
  lower_forest9 (g:=n187) (m:=187) (hints:=1349533697) (r:=2) (s:=3) (i:=0) (j:=1) validn31 geomn187 tablesn187 (by decide +kernel)
def mapsn187 : List (Nat × List Nat) := [(699,[]),(755,[99,65])]
def knownn187 := extendKnown knownn31 7 mapsn187
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validn187 : Known knownn187 := extendKnown_ok validn31 lown187 (by decide +kernel)
def n189d6 (i : Nat) : Nat := 0xfa50be99bda33fa88bf211
def n189l6 : Packing := (4,1,2,0,0,4,0,n189d6)
def n189d7 (i : Nat) : Nat := 0x20a71343f7f
def n189l7 : Packing := (2,0,2,0,0,4,0,n189d7)
def hashn189l7 (i : Nat) : Nat := 0x110b00018ce4002680
def n189samples : Array (Bits × Bits) := #[(0x1b9b8,0x19930),(0x0,0x0),(0x7fffffffffffffffffffffffffffead31,0x22930),(0x1474a,0x1060a),(0x7fffffffffffffffffffffffffffe72e5,0x7fffffffffffffffffffffffffffe60c5),(0x14e0e,0x460a),(0x0,0x0),(0x7fffffffffffffffffffffffffffe90d7,0x7fffffffffffffffffffffffffffc90c5),(0x0,0x0)]
def n189columns : List ColumnInfo := [(12,0,689,0,4),(17,0,172,0,4),(33,0,156,0,4),(132,0,569,0,4)]
def n189autos : Array (List Nat) := #[[],[115,84],[32,67,117],[32,83,116],[48,82],[112,66,115,84],[80,50,67,84,117],[64,114,83],[80,50,116],[64,114,115,116,117],[48,82,115,84],[112,66]]
def n189levels : Nat → Packing
  | 6 => n189l6
  | 7 => n189l7
  | _ => emptyPacking
def n189index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 4 10 0 7 2 1 (hashn189l7)
  | _ => fun _ => none
def n189 : Forest := (701,7,fun j => n189samples[j]?.getD (0,0),n189columns,n189autos,n189levels,n189index)
set_option maxHeartbeats 0 in
theorem geomn189 : graphValid n189 (boundsBefore knownn187) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1896_0 : goodRange n189 6 0 4 := by
  apply piecesGood (hint:=hintn189at6) (ar:=6) (d:=0)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alln1896 : goodRange n189 6 0 4 := sn1896_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1897_0 : goodRange n189 7 0 1 := by
  apply goodPlain
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1897_1 : goodRange n189 7 1 1 := by
  apply goodPlain
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alln1897 : goodRange n189 7 0 2 := (@goodJoin n189 7 0 1 1 sn1897_0 sn1897_1)
theorem tablesn189 : checkedTables n189 7 := by
  intro k hk
  interval_cases k
  · exact goodPlain (rfl : block n189 0 0 0 = true)
  · exact goodPlain (rfl : block n189 1 0 0 = true)
  · exact goodPlain (rfl : block n189 2 0 0 = true)
  · exact goodPlain (rfl : block n189 3 0 0 = true)
  · exact goodPlain (rfl : block n189 4 0 0 = true)
  · exact goodPlain (rfl : block n189 5 0 0 = true)
  · exact alln1896
  · exact alln1897
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lown189 : Lower (vars 701) (graphGoal 701) 8 :=
  lower_forest9 (g:=n189) (m:=189) (hints:=544228101) (r:=32) (s:=33) (i:=0) (j:=1) validn187 geomn189 tablesn189 (by decide +kernel)
def mapsn189 : List (Nat × List Nat) := [(701,[]),(859,[130,114,98,33,81])]
def knownn189 := extendKnown knownn187 8 mapsn189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validn189 : Known knownn189 := extendKnown_ok validn187 lown189 (by decide +kernel)
def n215d6 (i : Nat) : Nat := 0x41c3f7f
def n215l6 : Packing := (2,0,1,0,0,3,0,n215d6)
def n215samples : Array (Bits × Bits) := #[(0x7fffffffffffffffffffffffffffffb2b,0x30a),(0x7fffffffffffffffffffffffffffff955,0x7fffffffffffffffffffffffffffff851),(0x6ce,0x28c),(0x0,0x0),(0xbc,0xb4),(0x0,0x0),(0x4b0,0x4a0),(0x7a2,0x522),(0x0,0x0)]
def n215columns : List ColumnInfo := [(1,16,198,0,4)]
def n215autos : Array (List Nat) := #[[],[32,116]]
def n215levels : Nat → Packing
  | 6 => n215l6
  | _ => emptyPacking
def n215index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def n215 : Forest := (727,6,fun j => n215samples[j]?.getD (0,0),n215columns,n215autos,n215levels,n215index)
set_option maxHeartbeats 0 in
theorem geomn215 : graphValid n215 (boundsBefore knownn189) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn2156_0 : goodRange n215 6 0 1 := by
  apply goodPlain
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn2156_1 : goodRange n215 6 1 1 := by
  apply goodPlain
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alln2156 : goodRange n215 6 0 2 := (@goodJoin n215 6 0 1 1 sn2156_0 sn2156_1)
theorem tablesn215 : checkedTables n215 6 := by
  intro k hk
  interval_cases k
  · exact goodPlain (rfl : block n215 0 0 0 = true)
  · exact goodPlain (rfl : block n215 1 0 0 = true)
  · exact goodPlain (rfl : block n215 2 0 0 = true)
  · exact goodPlain (rfl : block n215 3 0 0 = true)
  · exact goodPlain (rfl : block n215 4 0 0 = true)
  · exact goodPlain (rfl : block n215 5 0 0 = true)
  · exact alln2156
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lown215 : Lower (vars 727) (graphGoal 727) 7 :=
  lower_forest9 (g:=n215) (m:=215) (hints:=553649953) (r:=2) (s:=3) (i:=0) (j:=1) validn189 geomn215 tablesn215 (by decide +kernel)
def mapsn215 : List (Nat × List Nat) := [(727,[]),(1009,[118,33,129,82,49])]
def knownn215 := extendKnown knownn189 7 mapsn215
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validn215 : Known knownn215 := extendKnown_ok validn189 lown215 (by decide +kernel)
def n349d6 (i : Nat) : Nat := 0x20a3f7f
def n349l6 : Packing := (2,0,1,0,0,3,0,n349d6)
def n349samples : Array (Bits × Bits) := #[(0x7fffffffffffffffffffffffffffffba3,0x3a2),(0x0,0x0),(0x256,0x46),(0x6b4,0x630),(0x7fffffffffffffffffffffffffffffc4f,0x7fffffffffffffffffffffffffffff84d),(0x0,0x0),(0x7fffffffffffffffffffffffffffffb5d,0x7fffffffffffffffffffffffffffffa55),(0x0,0x0),(0x1e8,0x188)]
def n349columns : List ColumnInfo := [(0,1,332,16,5)]
def n349autos : Array (List Nat) := #[[],[96,132]]
def n349levels : Nat → Packing
  | 6 => n349l6
  | _ => emptyPacking
def n349index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def n349 : Forest := (861,6,fun j => n349samples[j]?.getD (0,0),n349columns,n349autos,n349levels,n349index)
set_option maxHeartbeats 0 in
theorem geomn349 : graphValid n349 (boundsBefore knownn215) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3496_0 : goodRange n349 6 0 1 := by
  apply goodPlain
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3496_1 : goodRange n349 6 1 1 := by
  apply goodPlain
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alln3496 : goodRange n349 6 0 2 := (@goodJoin n349 6 0 1 1 sn3496_0 sn3496_1)
theorem tablesn349 : checkedTables n349 6 := by
  intro k hk
  interval_cases k
  · exact goodPlain (rfl : block n349 0 0 0 = true)
  · exact goodPlain (rfl : block n349 1 0 0 = true)
  · exact goodPlain (rfl : block n349 2 0 0 = true)
  · exact goodPlain (rfl : block n349 3 0 0 = true)
  · exact goodPlain (rfl : block n349 4 0 0 = true)
  · exact goodPlain (rfl : block n349 5 0 0 = true)
  · exact alln3496
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lown349 : Lower (vars 861) (graphGoal 861) 7 :=
  lower_forest9 (g:=n349) (m:=349) (hints:=13019136772) (r:=16) (s:=17) (i:=0) (j:=1) validn215 geomn349 tablesn349 (by decide +kernel)
def mapsn349 : List (Nat × List Nat) := [(861,[])]
def knownn349 := extendKnown knownn215 7 mapsn349
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validn349 : Known knownn349 := extendKnown_ok validn215 lown349 (by decide +kernel)
def n455d6 (i : Nat) : Nat := 0x20a3f7f
def n455l6 : Packing := (2,0,1,0,0,3,0,n455d6)
def n455samples : Array (Bits × Bits) := #[(0x7ffffffffffffffffffffffffffffff85,0x784),(0x7fffffffffffffffffffffffffffff867,0x7fffffffffffffffffffffffffffff823),(0x592,0x190),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x3e8,0x348),(0x570,0x460),(0x29e,0x96)]
def n455columns : List ColumnInfo := [(0,256,647,64,5)]
def n455autos : Array (List Nat) := #[[],[98,135]]
def n455levels : Nat → Packing
  | 6 => n455l6
  | _ => emptyPacking
def n455index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def n455 : Forest := (967,6,fun j => n455samples[j]?.getD (0,0),n455columns,n455autos,n455levels,n455index)
set_option maxHeartbeats 0 in
theorem geomn455 : graphValid n455 (boundsBefore knownn349) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn4556_0 : goodRange n455 6 0 1 := by
  apply goodPlain
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn4556_1 : goodRange n455 6 1 1 := by
  apply goodPlain
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alln4556 : goodRange n455 6 0 2 := (@goodJoin n455 6 0 1 1 sn4556_0 sn4556_1)
theorem tablesn455 : checkedTables n455 6 := by
  intro k hk
  interval_cases k
  · exact goodPlain (rfl : block n455 0 0 0 = true)
  · exact goodPlain (rfl : block n455 1 0 0 = true)
  · exact goodPlain (rfl : block n455 2 0 0 = true)
  · exact goodPlain (rfl : block n455 3 0 0 = true)
  · exact goodPlain (rfl : block n455 4 0 0 = true)
  · exact goodPlain (rfl : block n455 5 0 0 = true)
  · exact alln4556
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lown455 : Lower (vars 967) (graphGoal 967) 7 :=
  lower_forest9 (g:=n455) (m:=455) (hints:=26440894241) (r:=2) (s:=3) (i:=0) (j:=1) validn349 geomn455 tablesn455 (by decide +kernel)
def mapsn455 : List (Nat × List Nat) := [(967,[])]
def knownn455 := extendKnown knownn349 7 mapsn455
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validn455 : Known knownn455 := extendKnown_ok validn349 lown455 (by decide +kernel)
def n191d6 (i : Nat) : Nat := 0x2887d684985d22287d68497a2121
def n191l6 : Packing := (2,4,4,0,0,3,0,n191d6)
def n191d7 (i : Nat) : Nat := 0x9080000000502012112904902000000005085089080000002840000208000000010210210210200040c4082bb51a651e853d9c4ce4f228b40deef276ba1c6de6cb3582b5582ad4ca14e2411686409d4e06b33184b857258fc6627110742205004fd6448758e3fb2443ac71fd9121d638fe4bb0c9967721d634ca3fb2243c459f59121e228fe4c2e91147f262225c6afb2a392831fc9761931cfac32e298f754c9714c73e90ea8a631fc97a2121abeca8e4a04fd646884823fb30392215bd941c910afac88e48857e640724427e32243ac73d8988cd729dd4cb08396ce616441cb6b30b198e5b99848cc729ecc9d10a15f86448788bd94cd19c45f4a558ce228fc4bb0aa0fcc95644847da4cd19c23f52558ce11bd8ca0e508ff08ce228463eb2243ac71be9961072c9ec2c8839657616331cb33b09198e51f59121e22be4c99011156d650728467e323442413f09884520
def n191l7 : Packing := (47,3,4,0,0,9,0,n191d7)
def hashn191l7 (i : Nat) : Nat := 0xe6c
def n191d8 (i : Nat) : Nat := (if i<1 then 0x5aa9a65a51a25a119cd9b998d9619359098dd8c989d88985d83181d8097f57c97b577175d73171d6a967d66963d5e15555295154e94d54794353a93652f12c526923d1c91550f909d010f3cee0eb4ea0e74e60e4ce20df4dc8d6cce0c84c10b84b58b44b18b04aa8a7ca68a54a28a149d09bc9789649208f48c889c8588147d07a47607347086946506245e05b458855c5305044d84ac49846c45842c4183ec3d83ac39836c35832c3002ec2c027c2381f41c816c1401140e80bc002ffa2163bfc8758f7f58d72bfd831caff60472dfd541caffa2132bfc874caff61932dfd764cb7f5d532fdd634cb7f5c932dfd7488b7f58d71dfd325c77f88971dfc72506ffa2131bfc874c6ff61931dfd764c77f5d531dfd724c7f74c931ff5514c6ffa2121dfd87486ff21d21dfd74486ff60d21dfd734877f5c921fec72487fd4c521dfc72502ff61930fdd634c3f74c530bfe88482ff60d20ff481483fb48520ff930482ff60d10bfd824437f1c910ff920442fea2154bf887553ee5d644f7a555cefea2163bf88758efea2153bf88754ff65da33fd9758cfee91172fda335cbfa88972bf9841cbee91072bf9831cbf68cc72bf9811cafea2142bf88750bbe99942bf98550bde95542fb97450bee59142fb95450bfa1c942bfa884cafe21d32bf9864cbbe99932bf9854cbde95532fd9634cbfa21e22fea7788bfa5d222fe97388bfa58e22fe95388bee91171fda335c7fa88971bfa88506fe21d41efa66506fe61541f7a55507ee50941bfa884c6fe21d31bf9864c7be99931bf9854c7de95531fd9324c7fa88931ff1714c7fc54531bfa88486fe21d21bf984487ee91121bf983487f68cd21fe872487fc4c521ff174847fc55211ff173847fc58e11ff153847fc5ca11ff072847fc50a11ff1328467f21d54dbd75913cf95644d7e555ce7f21d639fc8754f775da33ede668cf775d633f5e558cf6f91172dde335caef61072bf9801ca7f61072dbe441ca7f60c72dde331ca7f604729fc8750b6f5d142dec7250a7f21d329fc8788b7b5ca22ded7488beb91222ded7388bf38ce22fe88088b6f91171dde335c77b889719fc875067f21d31df5714c67f21d21dec724877d5d211fb6448477d5ce11fd6338477d5ca11df472847f988a11efa66502fe61540f7a55503ee55140fea22503ee50540ff211502fe61930efa664c2fe61530f7a554c3f658d30fd9534c37e5c930fea224c3f64c530ff2114c2fea2120dfa77482fe61120fba44482fe60d20df973483f68cd20fe942483fa88920ff0814837e5c520fe921483fc84520bf984083ee91020bf983083f68cc20bf981083fc84420bf984443ee91110bf983443f68cd10bf9824437e5c910fea22443fc50510f3a55913b699a33f5a558ceee61072dea7788bf28ce22fb244847f48ce11fe2228466f61072 else 0xa10801122087104388708118a088008411c408e2682d50204810248811c31a8150110a009008803541001c43a02687406386241aa063847684000710e00801c403438c00c040e31c1112510301a206440200e19031e010e00880043c040c708811001541a8200541a83506a08015102a835502602404408040d01128150121a150110813412881501a03405a081a081a08080800c040000280d01050100840a80d01128102808081040a0340630c61602060208c2c04000301034c080c040286484428206822d448c50c8a822941014103551036aa1099b1d02510310e53009180b038a31c210230e410a1c120840231280463042d0394608504800a1d1534c0c108010800084108212870463042d03964a1018c10239021850442d410541054d303a020050100040800102010d0a80d01a02434220a10040a808640a8088111a613206c0a3086c0980c6160318530a614c20602060204c20602060208c20040c05aa04d5026a810814da606c0580b018c2c0d98a0f421eeb2e9ee5ae16dd2d76d32d1ecf2caec6ac3ebfabb6b72b16aeaaa6a62a369c297e93a8de89a83e8127ce7ba7767326ee69266660a5c656a50e4ca4b645a4163d238e3323062da29626a23e22a2161ea1be19216615213e0fa0ce08a05e032005ff1fc5f99f55f29ee5eb9e75e49e05dd9dadd81d55d41d15d01cd5cc1c95c81c6dc41c2dc19c05bf1bc5b99b85b59b45b01ad)
def n191l8 : Packing := (223,2,4,0,0,12,0,n191d8)
def hashn191l8 (i : Nat) : Nat := 0x891c2721554742dc16b0d54c000428222155017f9a000eca000208e43801e19b0221210fc00000c1140302024ba1405fd2b00090b21c324b5ce0751eb2e456f13d1be0c12a81811aa8840ae8a80ea04009e2541f929f2c000442126065b4a521f1000022311db053464065573480a1cd1001020046005
def n191d9 (i : Nat) : Nat := 0x901352047490b30290729013520479883ac10072027a404c514ce0d20e62827ac10e400f48098a2240e01e90910467c03470127a404c520a7a020e310664d60082083ac0c072006a41483501050106a41483520050106a414041a90520d48014041006a4100352084520602808a1a0a020d4828148190829e80834f48190a29e8083cf481a90414c3ac0133317582195326b052083a1e007d60630106a414041a90552003214041100a40ca41a9049e9039e90354c9ac175818ed5582ab54ca87ce797f2723544283efdde53a2708d99a432a618bb9682c1550a3d38a5346a870fc9e537a6a4bb95426c4387d0dc17c280488730b411819014001ff553feb1ffd53ff8e5ff50bfe997fe22ffa83ff4c7fe90ffd40ffa61ff483fe887fa77ff2e9fe553fcb9ff963ff2a7fe5cbfc397f942ff265fe5c7fca0ff931ff2437f5d3df225fd73fbc677f5cafe397ee22bfae3fd847fca07f930ff241fe083fc885fa77f7489f68cff5117f211
def n191l9 : Packing := (47,1,4,0,0,11,0,n191d9)
def hashn191l9 (i : Nat) : Nat := 0x930786134c48673454805509a9534615484274bc37f58f0663197d2286b09a1824a89ab1c5ddba337c2ea67f40fc2eb0d4a2c94d700008b0b4d6c414568e3682bac29d21400050954004629449b0a0000e0f6c94c07acc6f459080105709640715980001688157c00075e2ca1c1f4879030fcd515c2e2781f8000a14e02cc1d508391d8d1e34f207a7627891472688ca520452c29743baddbca6e18f704b3584d234ac00331628d0e2275a6e2da56c85e703e9332195b45fc87f71c49b443b0810003493a590587928842dc18bd9e0000981868d93a0000827808f676e0cc859501d01130bf43af05b84ba362d1d1082038502d9bc265a09e464224811c1186128d1c111d3928e314442050ed8d8496e31874dc5476fc00045c616f654a045d038d21863e559a24207841331b2d4478dc05255c04585c5dc08b8bf910d8dd375109d76524a9d1ac07cf43c000d32c4dad811c4dc41f954404b520a122898b1a00000000000b2be4be0001cd1000203fa6d8c7bd42a576d2ae81a68935060003175f0d9c73351e05a431000024cd08640a9497d15f07fa11d08b12e40005128cac957057a4441c196035899f6690b4002a95686920b3f682c5cb544801a3015270001157140b939b63800031b40000001c56020acc8704f48d32c74bba0085bb10ad43254ca8d30512806072346f4145d2f02f5c3904b352d000209ca2285b9969512a3087dcf032989f00001140002088a1b00001715174d13f455d4eccdbe3259ab25ba08f95fccce382e46a517a88ec47e13f014241490f2460307f009c10085b353616bf2820a433661cd025601827448b832a80dee30a8a8b1b80448754d584041167b29cc24b6cc0c712b6100f91bc64e410103e1dd804d0c2d46502380c917c0b7e33ed69113bc35005dcbc00c447221a4c4650d08b5f07581b010c000d091e0203040b08020d0f0a0c250000010c080108040113048d000a000252000e020d01040002022920002a0f0011292400130e201a013505000804000602060a061903040107180432070401001310263e030c06030a000201010515031b2a13055521141e02020002271a1b46241e2e0019
def n191d10 (i : Nat) : Nat := 0x3a81985412a0feff
def n191l10 : Packing := (2,0,4,0,0,5,0,n191d10)
def hashn191l10 (i : Nat) : Nat := 0x3831c5fcafd3cc9c892d53825846d8ec66c3c82983789bc7e848c581b2927801d62850c19485c0a5494b000397c002804414001d2399c0398a0000c83d9b089d45c96812d0a042954d0f47480c003d40a3295d17400201f48cc4f16eda9c7b82f9924238b546acb846f0a7da7463c564704a860454c610d01e08b14307d181019000b80
def n191samples : Array (Bits × Bits) := #[(0x7ffffffffffffffec0f3e6d224e80836b,0x7ffffffffffffff020c1e4d004880824b),(0x3c82e55a19de070882,0x3c02e1100832574d90),(0x7ffffffffffffff7390430293809892af,0x7ffffffffffffff41800402f380889263),(0x6f3842f4cc43375e10,0x2e3c42e40c6a370580),(0x8509a9935715856c54,0x9183a1125315406814),(0xc174b1342d3076b130,0x5152a1b26d20341130),(0x0,0x0),(0x7ffffffffffffff8865c84008336b280d,0x82254840001b43680c),(0x0,0x0)]
def n191columns : List ColumnInfo := [(1,0,190,0,7),(1,16,166,8,5),(1,32,30,128,5),(2,0,701,0,8),(4,0,699,0,7),(4,8,675,16,5),(4,128,539,32,5),(14,0,689,0,4),(24,0,679,0,7),(152,0,551,0,4),(160,0,543,0,7)]
def n191autos : Array (List Nat) := #[[],[115,84],[32,67,117],[32,83,116]]
def n191levels : Nat → Packing
  | 6 => n191l6
  | 7 => n191l7
  | 8 => n191l8
  | 9 => n191l9
  | 10 => n191l10
  | _ => emptyPacking
def n191index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 3 0 6 1 1 (hashn191l7)
  | 8 => lookupWord 16 71 6 12 6 2 (hashn191l8)
  | 9 => lookupWord 118 382 8 14 8 2 (hashn191l9)
  | 10 => lookupWord 23 76 6 12 6 2 (hashn191l10)
  | _ => fun _ => none
def n191 : Forest := (703,10,fun j => n191samples[j]?.getD (0,0),n191columns,n191autos,n191levels,n191index)
set_option maxHeartbeats 0 in
theorem geomn191 : graphValid n191 (boundsBefore knownn455) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1916_0 : goodRange n191 6 0 2 := by
  apply goodPlain
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alln1916 : goodRange n191 6 0 2 := sn1916_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1917_0 : goodRange n191 7 0 26 := by
  apply piecesGood (hint:=hintn191at7) (ar:=7) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1917_26 : goodRange n191 7 26 21 := by
  apply goodPlain
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alln1917 : goodRange n191 7 0 47 := (@goodJoin n191 7 0 26 21 sn1917_0 sn1917_26)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1918_0 : goodRange n191 8 0 10 := by
  apply goodPlain
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1918_10 : goodRange n191 8 10 36 := by
  apply piecesGood (hint:=hintn191at8) (ar:=8) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1918_46 : goodRange n191 8 46 36 := by
  apply piecesGood (hint:=hintn191at8) (ar:=8) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1918_82 : goodRange n191 8 82 36 := by
  apply piecesGood (hint:=hintn191at8) (ar:=8) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1918_118 : goodRange n191 8 118 36 := by
  apply piecesGood (hint:=hintn191at8) (ar:=8) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1918_154 : goodRange n191 8 154 21 := by
  apply piecesGood (hint:=hintn191at8) (ar:=8) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1918_175 : goodRange n191 8 175 36 := by
  apply goodPlain
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1918_211 : goodRange n191 8 211 12 := by
  apply goodPlain
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alln1918 : goodRange n191 8 0 223 := (@goodJoin n191 8 0 211 12 (@goodJoin n191 8 0 175 36 (@goodJoin n191 8 0 154 21 (@goodJoin n191 8 0 118 36 (@goodJoin n191 8 0 82 36 (@goodJoin n191 8 0 46 36 (@goodJoin n191 8 0 10 36 sn1918_0 sn1918_10) sn1918_46) sn1918_82) sn1918_118) sn1918_154) sn1918_175) sn1918_211)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1919_0 : goodRange n191 9 0 5 := by
  apply goodPlain
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1919_5 : goodRange n191 9 5 28 := by
  apply goodPlain
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn1919_33 : goodRange n191 9 33 14 := by
  apply goodPlain
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alln1919 : goodRange n191 9 0 47 := (@goodJoin n191 9 0 33 14 (@goodJoin n191 9 0 5 28 sn1919_0 sn1919_5) sn1919_33)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn19110_0 : goodRange n191 10 0 1 := by
  apply goodPlain
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn19110_1 : goodRange n191 10 1 1 := by
  apply goodPlain
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alln19110 : goodRange n191 10 0 2 := (@goodJoin n191 10 0 1 1 sn19110_0 sn19110_1)
theorem tablesn191 : checkedTables n191 10 := by
  intro k hk
  interval_cases k
  · exact goodPlain (rfl : block n191 0 0 0 = true)
  · exact goodPlain (rfl : block n191 1 0 0 = true)
  · exact goodPlain (rfl : block n191 2 0 0 = true)
  · exact goodPlain (rfl : block n191 3 0 0 = true)
  · exact goodPlain (rfl : block n191 4 0 0 = true)
  · exact goodPlain (rfl : block n191 5 0 0 = true)
  · exact alln1916
  · exact alln1917
  · exact alln1918
  · exact alln1919
  · exact alln19110
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lown191 : Lower (vars 703) (graphGoal 703) 11 :=
  lower_forest9 (g:=n191) (m:=191) (hints:=544228129) (r:=2) (s:=3) (i:=0) (j:=1) validn455 geomn191 tablesn191 (by decide +kernel)
def mapsn191 : List (Nat × List Nat) := [(703,[]),(831,[135,50,65]),(891,[130,114,98,81])]
def knownn191 := extendKnown knownn455 11 mapsn191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validn191 : Known knownn191 := extendKnown_ok validn455 lown191 (by decide +kernel)
def n351d6 (i : Nat) : Nat := 0x28a7a68a889dd3187b68a9960c71
def n351l6 : Packing := (2,4,4,0,0,3,0,n351d6)
def n351d7 (i : Nat) : Nat := 0x20820c90800000208010400820000000a100108328728728440408400003107107107107287287287284001010210010800000108008440400000000000000000420439429439432949b244871f465134350ac2105c0cfd3eaf4bc8ec3a6e7392e237ed9b5cd133ac8b0abcadab0ab8abaa4a6a829aa528ea22829f2769d0719ae6598c5d16a58156531344a9123e8f0398dc348c82f8b42a8a02588c20878180480c0180067ea22774c63fd32c10e71fd9221d6397ecb510a9c7f6488754e3fb2643ac51fd9321d52cbe43aa6a967b21d624ca3fd32c18e39ec9260c718fecc26438e7760d321c66fb2b442c31fd9321d618fec910eb0c7f64c875467db25442631fd9221d31aeec90e698e7b21c824c7b98e6412631fd9321d218fecc0e690d7d64473487ba8e698a433799520d649f4c9106b24fc644835925f32d442a71f89760633bccca10f19d7625d818cedb32c40c6779994206339dcca10eb14de6548358a7732841ac53f19120d629ec49b0ca14be6588350a6f32a41a853f19120d42f952ac89117d29563388a6f32b442c31f89761941c7c43ccca0c7e25d855072f10f2aa839d8878cd41cf443c44a0cfa64a884c63f12ec22633e898889318fc4bb0890cde65483846be12ea0c23eb26691211f992ac8908ddc65483847ba4ef19c23ed2668ce11fa92ac6708fe491233847dc4cd11423f625588a11fd12244508ff08ce2284637b2843c6759d9421e338deca10eb14de6548358277329442613799520d20
def n351l7 : Packing := (75,3,4,0,0,10,0,n351d7)
def hashn351l7 (i : Nat) : Nat := 0x63d
def n351d8 (i : Nat) : Nat := (if i<1 then 0xfbe99873bf9851cfde95473bf9821cefe60473bfa8858efe21d63ef96458efea2153bf88754fde55153bfa8850efe61943efa6650efe61543f7a5550fee59143dfa778cefe61a33bf9858cfde95633bf9848cff61ce33fd9638cff654e33fd9438cefe60a33bf9818cff6a2233fd8878cff661a33fd9858cff661233fd9648cff655233fd9828cff660633fd8818cefea2162bf88758afe20d62ef96358bf68cd62bfa8854afe21d52fba4454afe20d52f795354bf68cd52bfa8850afe61942efa6650afe61542f7a5550afe20d42fb94350bf68cd42fe95250afea2132bf8874cafe61932bf9854cbde95532bf9844cbf68cd32fe9624cbfa50932fe96488bfa55222fe87388bfa58e22fe95388bfa50e22fea3388afe61871efa661c6fe61471f7a551c6fe60c71fda331c6fe60871fea221c6fea2161bf887587be59161fba44586fe20d61fda33587be58961fea22586fea2151bf887547ee91151bf883547f68cd51f7952547fa88951bfa885077e21d41bf986507be99941bf985507de95541fb964507ee55141bf883507f68cd41fb942507fa88941bfa884c6fe21d31dfa774c6fe61931efa664c6fe61531f7a554c6fe61131fba444c7f61cd31fd9534c7f68cd31fe8824c7f64c931fea224c7fc58531ff1414c6fe61831efa660c6fe61431f7a550c6fe61031fba440c7f68cc31bf9820c7fa88831ff1310c6fea2121bf887486fe61921efa66486fe61521f7a55486fe61121fba44486fe60d21bf883487f68cd21fe952487fc4c521efa66847de95611fba44846fe20e11fda33847fa88a11ff161847fc54611ff141847fc4c611ff121847fc21e11ff164847fc55211ff083847fc1ce11ff163847fc54e11ff143847fc8ce11ff162847fc54a11ff142847fc4ca119fe881ce7f61873cfe661ce7f61473d7e551ce7f608739fd811ce7f21d639fc8754e7f21e33ddc738cefe60233ddc878cfb799a33f5e558cff6602339fc8758a7f21d529fc874cbbb99a22f6e5588b7b1ce22fce3388a7f61871cfe661c67f61471d7e551c67f60c71dde331c67f60871dee221c67f21d619fc875467f21d31ddc734c6fe600319fc874867f21e11df487847bd99a11f76558477d1ce11fd633847f988a11bf883583f68cd60fea22583be58560ff211582fe20d50f7953543f68cd50fea22543de54550ff211542fea2130bf9864c3be99930bf9854c3de95530df8734c3f68cd30fea224c37e1c530fd9314c3fc84530bf986483be99920bf985483de95520bf983482fe20d20fda33483fa58920fe921483fc84520bfa88442fe61910efa66442fe61510f7a55442fe60d10bf883443f68cd10bf982443fa88910ff211443ce95644f5a558cfba99a22f6a5588bea91222fca3388a7e21d41df277847bc99a11f7255847ec91211fd233847f888a11 else (if i<2 then 0xc118914419424ca29432865082508250ca1a42a849145485508828840b2103210084880089108204408040800c8402044244c840c840003210321044154248b10e208220aa100b1082244094328650ca194310a288328650c41542c859081508190aa1032100190800c8400040004200010521a420122a43486908448a90d21a420a42024010041442059081908190b219420482002a16525461322882132288212a2882a8590c414829040c8550b21032102a10012080110620b2104410441044188200891441000038a2001908009040002a1542003210000054201461c630a38c708e40870903ca320794120948231290460882042084108000a550474aa30c7215048000e101240e3202310220238444a41823ca30c80aa40875461903aa09081d518611c8543208a921915080028400942004a104a11491001284128650ca115914a110328650a028a50ca1942002510250ca104a19420942c841284014a2942048200321642c8590c4188220a2552646c8590aa15651241e29e18e07df6debddadc9db8da7da2d91d7ad75d6ad59d48d31d26d15cfecedcdccd1cc0cb5c98c7bc70c5fc54c49c38c27c16bf9be8bd7bccbbbbb0ba5b94b89b7eb73b6eb63b5eb53b48b3db32b21b16b0bafaaefae4adfad4acfabeaa1a96a8ba86a7ba76a71a66a61a56a45a3aa35a2aa25a20a1ba10a0ba009fb9f09e59ce9c39be9b39a89a399298197c97196695b95094593492991e9139088fd8f28e78e28d78d28c78bc8b78ac8a78a289789288d88287d87286d85c85784c84783c83182081580a7ff7ee7e37d87cd7c87bd7b87a77a279178677b77676b76675b75074574073573072b7207096f86ed6dc6d16c06b56aa69f69468967e67966e66365865364864363863362e62361e61960e6035f85f35e85e35d85d35c85bd5b85a759c59759258d57c57757256756255d55254d54854353852d52852351851350e5095044f94f44dd4c64bb4aa49f48846b45443d42c42141640b4064013fc3e53ce3b13ac3a739c39738037536435933c33131a30f2fe2e72ca2b32a828b26e26325e25924e24924423923422f22421f2142031fe1f91ee1e91de1d31c81b71ac1a119618b17a16f16415915414313e13312812311810d1080fd0f20ed0e20dd0cc0c10bc0b10ac0a709c09108607b07006505403d03202701c00b000dfd821ceffa2163bfe8854effa2162efd6358affa2152dfc7354bdf54d52bfe884cb7f21d32bfd864caff61532dfc734cbfb58932dfd631c77f8cc71dfd621c77f4c871bfe88587bf58961bfe885477f1cd51f7d52546ffa2131dfc874c6ff61931bfd854c77f1cd31fdd534c7fb20931fdd324c7fd58531bfd860c6ff61431bfd86486ff61521bfd834877f1cd21fed52487fd4c521bfa88592fe20d64bfa88552fe20d54bf9861c else 0x8a204510228a209028812041122045100114409228c0484704438220421c6084114409290c1144402204208a254208448a4042159244105916a10423b2214110a088188914830a204510))
def n351l8 : Packing := (318,2,4,0,0,12,0,n351d8)
def hashn351l8 (i : Nat) : Nat := 0x1622421408400163fe00800000000080c306f93fe32ac4906683ee3c60f28f8c6a027401210010e81df1ed0b802bc04c1430ccc8a21ca18a09b02802ff23502406d02ac1bb023121213b0d409542501100398a700c0000001911c0b80e32488c145ac2bf06800082c63a00838e3018843c0788b2017800000480f8688852055107472a48023e081c2fa24325488c001a3b0185600d6b83880586c200cbf1140100ae4
def n351d9 (i : Nat) : Nat := 0xb926a5400f24d4c0966a42a8870093539002326a600b35210e8926a6248c9a9402966a52033519459a8c8492401a98402a482015241012520805490402a480124a404b35200a24900512480488a4024a2200a21152311523124a3024552140249443926a0249351c9351813209ca6966a3c8aa3cc90501640cd4820152410125208092900911482480a4008a924aa91caa91cb2519659a92b910cb2066a59b12d64bc6f8990ce083f27a8ed9ceb7a6c2d2197b165fab9165ab2532a0133a584888c10e2033e8780e39b333e5f0b415426c474820eb1a42e4500870e617c2583203c003feb1ffd53ffc67ff58bfea97fd32ffac3ff547fe98ffc31ffa43ff847fcb27f954ff0e7fe58ffca9ff943ff467fe58bfca97f942ff265fe1c7fcb0ff951ff283fe4c7fc18ff921ff423bf99bbf2adfc73fbc67fb88afe38ff611ff2c1fe543fc987f920ff2217e9df7d3377a55f7489f68cff5117f211
def n351l9 : Packing := (50,1,4,0,0,11,0,n351d9)
def hashn351l9 (i : Nat) : Nat := 0x3a819127a184c478015e2516310f02202bb20840d800048adc26fa361076a899c0a04217410a8731038c172467805b51f60000000382d22740001464e859924c82cb102c930d27a000285e984821c00042830590021d522c54968000119da144000604dc230000043d912fc0bc82e747218da51cca0c7486184761a2424b04e282ad1ebe348d3c803f20c861ba029e00a30b4840ac1ae0c6a15041fa887004370a82371448b04111de84710998877a23d0030031d802022ba2c3c5768fe307740458272826a01e635c89ce81741e80002879a88c9147801f45b890601446aee4074116b195826d095393bc08b63f00003006000064500005884606083f5c38686ca129a0b88550000115e20d38340000f05e20a50480919a19b611b42500b621ce3a1683b78271100835000070235104a0f00618000d26bc3c0c01f025203ca090000692bb26360dfc43d20c80f9c0e04682818721084048317812c088a46d04ed11f000082e2855b869e114000280fa8e8f246e1cb884e110a405e41fc0b10eed08002f3c9e092ce0d58490094d8b4620a622255a0000f0a5238c000704c00004315881a8394159b9ef0539055f0bb83dac44d91ac1b7806b03fd8bb526583e9876509661e58b8d89c68be2085815d443111d60ebe0f9019b0ffb198a011485789e9103a3c608ba0a6f0cb20f4805f90b90328198090700580f38355471688b60e8c27fc1d00000245643702f9136d25c430b00eb0a5c1404305465980851a681af46b2801f026c31d872900db09fa293046a020e1ba0000824a05671d3e28643c490f2058a26b47c38670000a37e06cb0f70000c262447512740e3a449890f8581107a494000009780fb80c803d48b340360002854986f0001e2d7875986d21c20001c110000722680a0000401421f2000000048c0022284d2c5f8000b013c32305d0000e0002378c25f09519001506130e07084e080002050006001102170400071f02000009040021640003100f001817170007030100212d0d1e17004d0200002b09080806110a18060a18000a0e000092012216370d3b070525022a1a7a1619163b421b000080a2
def n351d10 (i : Nat) : Nat := 0x295194a8e20feff
def n351l10 : Packing := (2,0,4,0,0,5,0,n351d10)
def hashn351l10 (i : Nat) : Nat := 0x18b05359e534a764e6ab75043d46330a1c20c0009b22ee97420b1232c4ed0b82c2a24a80781f12000d3f10210c8a5572045381dd700060b42ad7800e3122d1180015b0524b0005494180000001a07c004116000900041900001005602104
def n351samples : Array (Bits × Bits) := #[(0x7fffffffffffcb3751f0634d04dd43081,0x7fffffffffffca145030620c045d41081),(0x2162362c59d380a0fc946,0x62040415f3a1a02ed06),(0x7ffffffffffff9001ccc3680d859c1bc1,0x350038d92200485bc1040),(0x7ffffffffffffe100e2305381591296bf,0x7fffffffffffc21246240c3016a0006bf),(0x625c9c2a1a4c809b605c,0x142989ca8180e802b6040),(0x0,0x0),(0x7fffffffffffc3d8b392aa027a771500b,0x7fffffffffffc7983382aa00521310049),(0x0,0x0),(0xd88851c2dc6f4e88c20,0x1040885140cc294cc8900)]
def n351columns : List ColumnInfo := [(2,0,861,0,7),(2,1,332,16,5),(4,0,859,0,8),(7,0,344,0,4),(9,16,326,0,4),(17,0,334,0,7),(70,0,793,0,4),(72,256,535,0,4),(258,64,541,0,4),(320,0,543,0,7),(324,0,539,0,4),(328,0,535,0,4)]
def n351autos : Array (List Nat) := #[[],[64,49,134],[96,132],[128,49,100]]
def n351levels : Nat → Packing
  | 6 => n351l6
  | 7 => n351l7
  | 8 => n351l8
  | 9 => n351l9
  | 10 => n351l10
  | _ => emptyPacking
def n351index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 2 4 0 6 1 1 (hashn351l7)
  | 8 => lookupWord 28 89 5 13 7 2 (hashn351l8)
  | 9 => lookupWord 94 366 8 15 9 2 (hashn351l9)
  | 10 => lookupWord 25 59 4 11 6 1 (hashn351l10)
  | _ => fun _ => none
def n351 : Forest := (863,10,fun j => n351samples[j]?.getD (0,0),n351columns,n351autos,n351levels,n351index)
set_option maxHeartbeats 0 in
theorem geomn351 : graphValid n351 (boundsBefore knownn191) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3516_0 : goodRange n351 6 0 2 := by
  apply goodPlain
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alln3516 : goodRange n351 6 0 2 := sn3516_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3517_0 : goodRange n351 7 0 36 := by
  apply piecesGood (hint:=hintn351at7) (ar:=7) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3517_36 : goodRange n351 7 36 13 := by
  apply piecesGood (hint:=hintn351at7) (ar:=7) (d:=2)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3517_49 : goodRange n351 7 49 26 := by
  apply goodPlain
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alln3517 : goodRange n351 7 0 75 := (@goodJoin n351 7 0 49 26 (@goodJoin n351 7 0 36 13 sn3517_0 sn3517_36) sn3517_49)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3518_0 : goodRange n351 8 0 13 := by
  apply goodPlain
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3518_13 : goodRange n351 8 13 36 := by
  apply piecesGood (hint:=hintn351at8) (ar:=8) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3518_49 : goodRange n351 8 49 36 := by
  apply piecesGood (hint:=hintn351at8) (ar:=8) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3518_85 : goodRange n351 8 85 36 := by
  apply piecesGood (hint:=hintn351at8) (ar:=8) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3518_121 : goodRange n351 8 121 36 := by
  apply piecesGood (hint:=hintn351at8) (ar:=8) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3518_157 : goodRange n351 8 157 36 := by
  apply piecesGood (hint:=hintn351at8) (ar:=8) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3518_193 : goodRange n351 8 193 36 := by
  apply piecesGood (hint:=hintn351at8) (ar:=8) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3518_229 : goodRange n351 8 229 36 := by
  apply piecesGood (hint:=hintn351at8) (ar:=8) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3518_265 : goodRange n351 8 265 13 := by
  apply piecesGood (hint:=hintn351at8) (ar:=8) (d:=2)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3518_278 : goodRange n351 8 278 36 := by
  apply goodPlain
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3518_314 : goodRange n351 8 314 4 := by
  apply goodPlain
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alln3518 : goodRange n351 8 0 318 := (@goodJoin n351 8 0 314 4 (@goodJoin n351 8 0 278 36 (@goodJoin n351 8 0 265 13 (@goodJoin n351 8 0 229 36 (@goodJoin n351 8 0 193 36 (@goodJoin n351 8 0 157 36 (@goodJoin n351 8 0 121 36 (@goodJoin n351 8 0 85 36 (@goodJoin n351 8 0 49 36 (@goodJoin n351 8 0 13 36 sn3518_0 sn3518_13) sn3518_49) sn3518_85) sn3518_121) sn3518_157) sn3518_193) sn3518_229) sn3518_265) sn3518_278) sn3518_314)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3519_0 : goodRange n351 9 0 7 := by
  apply goodPlain
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3519_7 : goodRange n351 9 7 31 := by
  apply goodPlain
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn3519_38 : goodRange n351 9 38 12 := by
  apply goodPlain
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alln3519 : goodRange n351 9 0 50 := (@goodJoin n351 9 0 38 12 (@goodJoin n351 9 0 7 31 sn3519_0 sn3519_7) sn3519_38)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn35110_0 : goodRange n351 10 0 1 := by
  apply goodPlain
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn35110_1 : goodRange n351 10 1 1 := by
  apply goodPlain
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alln35110 : goodRange n351 10 0 2 := (@goodJoin n351 10 0 1 1 sn35110_0 sn35110_1)
theorem tablesn351 : checkedTables n351 10 := by
  intro k hk
  interval_cases k
  · exact goodPlain (rfl : block n351 0 0 0 = true)
  · exact goodPlain (rfl : block n351 1 0 0 = true)
  · exact goodPlain (rfl : block n351 2 0 0 = true)
  · exact goodPlain (rfl : block n351 3 0 0 = true)
  · exact goodPlain (rfl : block n351 4 0 0 = true)
  · exact goodPlain (rfl : block n351 5 0 0 = true)
  · exact alln3516
  · exact alln3517
  · exact alln3518
  · exact alln3519
  · exact alln35110
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lown351 : Lower (vars 863) (graphGoal 863) 11 :=
  lower_forest9 (g:=n351) (m:=351) (hints:=13019136801) (r:=2) (s:=3) (i:=0) (j:=1) validn191 geomn351 tablesn351 (by decide +kernel)
def mapsn351 : List (Nat × List Nat) := [(863,[]),(879,[84,131,98]),(943,[98,118,81,130,50,65]),(957,[118,130,81])]
def knownn351 := extendKnown knownn191 11 mapsn351
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validn351 : Known knownn351 := extendKnown_ok validn191 lown351 (by decide +kernel)
def n487d6 (i : Nat) : Nat := 0x87eaa89760d10
def n487l6 : Packing := (1,4,4,0,0,0,0,n487d6)
def n487d7 (i : Nat) : Nat := 0x1000000040a2005084080008a1005084080000a10000000000081081081004080000810000000000c01c01c01c01c01003057dbc5cedd69ab5468b399a4be551e8cc3602fc7bbc9cce16e35da4cd6430d7cb2532692a89421fcf46e34990be5a2a94096461d0b8441605014015fa9921d31cfd4c90e98e7ea22774c63fb2243ac51fd9321d428fec890ea165f615651c63fd32c18e31fd9560c718fe4bd10a8cfb64a885463fb2643aa31fc9761951abe4bacaa8d5f25d545463fb3039aa35f5911cd518fe4bd1098cfe642884c63fd3243a631fd9521d31afaca8e298d7d25d514c7ba8e6a8a631fd9321d218fe4bb0c90c7f25d844863f92ec1a435ec97509219bcca902b14de6548150a7b32640a859d9831cc719f4c9510a8c7ea64874c73d10f11263dd0731c5318fc4bb0690df824542486be12e98c23e726695611bf0c910708f749de33847dc4cd11423fa24488a11fe119c4508cfc245844825f32c40a4137995205209dcca102904f664c814837c10290a411f89760d10
def n487l7 : Packing := (53,3,4,0,0,9,0,n487d7)
def hashn487l7 (i : Nat) : Nat := 0x3c
def n487d8 (i : Nat) : Nat := 0x10010800840c5004008648a324511210e510014020055080188900400409442062242386294328650ca140248128d50820081508250ca115914a124511228a5080140206505460402a855080128650b2194328650ca11c910600a390708072451aa10015080006420001954400000002a15421ca50c794a18001c038840c51e010a38410c712028e00621040863a021011c311028638881010863ca090214904800500a010001000100410040904000a2803004100550820082008010c0104ac899944065512a156512a1c878cb10e16c177d2f1dd8b8f6f2d8da6b3762abcd6eabb532a0d30a4b46a87d049f338a6bcd298f30a5bcb294f27245c808df17a29c4887b0e210c1c823019fdbf67e2f99edbd078aee9d7ba4726dd9b5b6669ed119fb3a65eca992b2062ac4185b065eabc175ae65c2b716bacc582aa949a8e5129b124a3e4367f8f99d6366658c596e2a25189d9302564808d916222418808f61e2398708d018a2e85a8aa13e2684788a0fe1e8378640be1381e83804e07005800bfe8858affa2142dfd651c77f60c71bfe88546ff61951f7d65547df55151dfc73546ffa2131dfc874c77f1c531ff5514c6ff61031bfd86486ff61121bfd834877f1cd21fed424877f1ce11bfa8858afe21d62bf88158afea2142bf88750afe20542bf9851c7de95471bf9831c77e1cc71bf9821c7fa88871bfa88546fe21d51bf986547be99951f7965547de55151fba44546fea2131bf8874c77e21d31dfa774c7fa88931ff0714c7fc54531bf9820c7fa88831fd9310c6fea2121bf887486fe61921efa66486fe61121fba44486fe60d21fe9424877e9de11bf985847de95611bf983846fe60a11fea22847fc1c611ff151847fc4c611ff031847fc48611ff288847fc21e11ff185847fc59611ff183847fc20e11ff073847fc54e11ff233847fc60a11ff162847fc50a11ff1328467f21d629fc8750bbb99a22fae4488a7fa20719fd851c75f954719fd831c67f60871dee221c67f21d519fc874c77d1c531bf9800c67f21d219fc878477d1c611bf9808477d21e11f76558477d1ce11fd633847f988a11ff180846fe61920efa66482fe61120fba444837e1cd20fda33483fa4c920bf881483fa48520ff211482fea2110bf985443de95510bf983443f68cd10bf982443fa88910df871443fc4c510ff211443ba99a22faa4488a7e21d31df277847dc95611fd233847f888a11
def n487l8 : Packing := (132,2,4,0,0,11,0,n487d8)
def hashn487l8 (i : Nat) : Nat := 0x11b8e772122e932617e4b00042dd22e20527612305b0ad31100807df1b3320670b416d2f02a11d000000830cd1d26fa740cd01f13749a02f51e1a3a6f28223000a25214cc7629719000303f47715d1cc1f71ed0903460fc6600840432409190d04e658cc902b000000f8c156b2ce1088d08760e811c180289312100000450b3101022100d02023130e
def n487d9 (i : Nat) : Nat := 0x142184854c10a104854c0e2264b028ab981100364413660509055cc02500925200492904928080124a414125200420092520a19a932580c59a9c04366b0189202904928082024a4864a3043352475093e8edb70cfb02b429e9b23a821ea6e186579183c0be2305a0c801ff58bfea17fd51ffa63ff0c7fe90ffe11ff2c5fe50bfc38ff951ff263fe0c7fc90ffa11fdc457f1c7fb08ff920ff2217e9dff5117f211
def n487l9 : Packing := (23,1,4,0,0,10,0,n487d9)
def hashn487l9 (i : Nat) : Nat := 0x18420003d29b04d85ba9854468047c54d16545e5200c2ea009917751b01b10f642291a4168c13574c5d59c06e07f911715d00a712d04cd1a80006515c4189de5560003007b1b8851c1f40000002472f40ac61814c47b91d645f0002455f0a025ef87cc7020e3805720442981ce755c501c1d0002c213821d64adc80630126d5d81de0826101573111165fa90a80f48520456402c04f1b400030afc209855e0fe10ec71b933015805875ff9cd425504a15eb8b246461e800020ea0185555c4a307a74f80a8000d87a92d0000658306800c852ee5791f0a542d4080949f383c350f6559dcec30c5c792a80035779ddc000d0ef8233168b15313ac67e9fbc7e60c453870fbc3f6d6306f495ba8160d4e68ac64d1f20bdc0e7d50a33700ea380002019000317c39c306858e776041fc00040cd237f85ae0e01e0000b0e502c7188065305310e659400054f6c34000267d643f047d563c27a471810f20cc08e1ad77d70d914d489bc17c80953325a494cb122536e550150b80ed35c070d7520b4a4891dab3551b150be02e00d342a52cc9c98526141001e18184fb0900006dd4e0c4525879f1624374175032009814871d0c5c415ba3c1199f160e001513050f074e0a000127045f010203150b010e044b5502050f6409402003060a0229040011000402890100a70900290c13030045020001011c02070d25110b0000
def n487d10 (i : Nat) : Nat := 0x951ca80e20feff
def n487l10 : Packing := (2,0,4,0,0,5,0,n487d10)
def hashn487l10 (i : Nat) : Nat := 0x3544c9123e098fa8da23ca9f10aae004b3c48937b2264a9b81b1cc0800e12534c346150a10e1a00c0012bdd8cc500021ce73210013d1b3bb6848c2f4a10a6d2609a850300001113d9002584696000426439a8d0dde802c02e0db42900095
def n487samples : Array (Bits × Bits) := #[(0x7c6a1fe870051c,0x544a0fa000051c),(0x7fffffffffffffffffe55bc98c1273283,0x7fffffffffffffffffd09a410510a22a3),(0x285928e3c364e58,0x2c0528e0c344c08),(0x0,0x0),(0x0,0x0),(0x7ffffffffffffffffff2801654b7de2a3,0x7fffffffffffffffffc0900c04a7de223),(0x92454e00913d54,0xd04b4c00911454),(0x1368750b40091fe,0x1268d11b08011d4),(0x7fffffffffffffffffc86f433a78a4d0d,0x6b433b5020908)]
def n487columns : List ColumnInfo := [(1,0,486,0,8),(7,0,480,0,4),(32,0,967,0,7),(96,256,647,0,4),(130,4,865,0,4),(132,0,867,0,7),(161,0,326,0,4),(258,64,677,0,4),(289,0,198,0,4),(320,0,679,0,7),(324,0,675,0,4)]
def n487autos : Array (List Nat) := #[[],[98,135],[81,114,134],[81,130,118]]
def n487levels : Nat → Packing
  | 6 => n487l6
  | 7 => n487l7
  | 8 => n487l8
  | 9 => n487l9
  | 10 => n487l10
  | _ => emptyPacking
def n487index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 1 0 6 1 1 (hashn487l7)
  | 8 => lookupWord 37 79 4 12 6 2 (hashn487l8)
  | 9 => lookupWord 67 251 8 14 8 2 (hashn487l9)
  | 10 => lookupWord 16 61 5 11 5 2 (hashn487l10)
  | _ => fun _ => none
def n487 : Forest := (999,10,fun j => n487samples[j]?.getD (0,0),n487columns,n487autos,n487levels,n487index)
set_option maxHeartbeats 0 in
theorem geomn487 : graphValid n487 (boundsBefore knownn351) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn4876_0 : goodRange n487 6 0 1 := by
  apply goodPlain
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alln4876 : goodRange n487 6 0 1 := sn4876_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn4877_0 : goodRange n487 7 0 24 := by
  apply piecesGood (hint:=hintn487at7) (ar:=7) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn4877_24 : goodRange n487 7 24 29 := by
  apply goodPlain
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alln4877 : goodRange n487 7 0 53 := (@goodJoin n487 7 0 24 29 sn4877_0 sn4877_24)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn4878_0 : goodRange n487 8 0 7 := by
  apply goodPlain
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn4878_7 : goodRange n487 8 7 36 := by
  apply piecesGood (hint:=hintn487at8) (ar:=8) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn4878_43 : goodRange n487 8 43 36 := by
  apply piecesGood (hint:=hintn487at8) (ar:=8) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn4878_79 : goodRange n487 8 79 33 := by
  apply piecesGood (hint:=hintn487at8) (ar:=8) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn4878_112 : goodRange n487 8 112 20 := by
  apply goodPlain
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alln4878 : goodRange n487 8 0 132 := (@goodJoin n487 8 0 112 20 (@goodJoin n487 8 0 79 33 (@goodJoin n487 8 0 43 36 (@goodJoin n487 8 0 7 36 sn4878_0 sn4878_7) sn4878_43) sn4878_79) sn4878_112)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn4879_0 : goodRange n487 9 0 3 := by
  apply goodPlain
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn4879_3 : goodRange n487 9 3 13 := by
  apply goodPlain
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn4879_16 : goodRange n487 9 16 7 := by
  apply goodPlain
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alln4879 : goodRange n487 9 0 23 := (@goodJoin n487 9 0 16 7 (@goodJoin n487 9 0 3 13 sn4879_0 sn4879_3) sn4879_16)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn48710_0 : goodRange n487 10 0 1 := by
  apply goodPlain
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sn48710_1 : goodRange n487 10 1 1 := by
  apply goodPlain
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alln48710 : goodRange n487 10 0 2 := (@goodJoin n487 10 0 1 1 sn48710_0 sn48710_1)
theorem tablesn487 : checkedTables n487 10 := by
  intro k hk
  interval_cases k
  · exact goodPlain (rfl : block n487 0 0 0 = true)
  · exact goodPlain (rfl : block n487 1 0 0 = true)
  · exact goodPlain (rfl : block n487 2 0 0 = true)
  · exact goodPlain (rfl : block n487 3 0 0 = true)
  · exact goodPlain (rfl : block n487 4 0 0 = true)
  · exact goodPlain (rfl : block n487 5 0 0 = true)
  · exact alln4876
  · exact alln4877
  · exact alln4878
  · exact alln4879
  · exact alln48710
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem lown487 : Lower (vars 999) (graphGoal 999) 11 :=
  lower_forest9 (g:=n487) (m:=487) (hints:=22153266977) (r:=2) (s:=3) (i:=0) (j:=1) validn351 geomn487 tablesn487 (by decide +kernel)
def mapsn487 : List (Nat × List Nat) := [(999,[])]
def knownn487 := extendKnown knownn351 11 mapsn487
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem validn487 : Known knownn487 := extendKnown_ok validn351 lown487 (by decide +kernel)
def gzsamples : Array (Bits × Bits) := #[(0x8445b200673679400480a449dc72860c,0x440b040651468400400a049dc528208),(0x68418ef8c031934c390e981e002897182,0x4801a43858209148b908a189022893012),(0x6290104f000caa43851726039dd30827e,0x2212184104042a0206150602cc4308289),(0x148c82001a0cc82c702a90a968acc5f45,0x88d22080b98c42cf00a100900a8c0d46),(0x161cd482706611027db540f2641337001,0x3612d482f02611030fb565f2621217081),(0x30224c026a03cb26d80112aa22853c40,0x2a0320c831a828306f0011022028534c7),(0x2a903d1c3002a2842f25054b4f05cfc8,0x328a03c183982e2042a25054b4904cfc8),(0x4398a40660c0c18d90e9ee78131cee930,0x51888406c851c58d90e8e8781314a4930),(0x5224113090451e30e55cb840947a003b,0x5204816040511c30055ae804b4720010)]
def gzcolumns : List ColumnInfo := [(5,2,440,64,6),(7,0,504,0,7),(9,16,486,0,8),(11,16,484,0,5),(14,0,1009,0,7),(17,0,494,0,11),(19,0,492,0,8),(24,0,999,0,11),(26,4,865,128,5),(34,1,460,16,6),(35,0,476,0,7),(36,128,859,0,8),(39,128,344,0,4),(49,0,462,0,8),(56,256,647,64,5),(65,0,446,0,9),(66,0,957,0,11),(80,0,943,0,11),(129,0,382,0,9),(130,1,332,48,6),(132,0,891,0,11),(136,256,535,96,6),(144,0,879,0,11),(156,0,867,0,7),(160,0,863,0,11),(192,0,831,0,11),(198,0,825,0,7),(206,0,817,0,4),(257,0,254,0,8),(257,32,94,128,6),(258,64,701,0,8),(268,0,755,0,7),(270,64,689,0,4),(296,0,727,0,7),(320,0,703,0,11),(324,8,675,16,5),(344,0,679,0,7),(384,8,611,20,6),(480,0,543,0,7)]
def gzautos : Array (List Nat) := #[[],[81,130,118],[16,82,131,100],[80,81,82,83,116,133,118],[32,83,116],[128,81,130,83,100,118],[48,33,133,118],[48,129,82],[16,33,50,131,100,133,118],[80,129,50,116],[128,49,100],[32,49,130,83,116,118]]
def z3d9 (i : Nat) : Nat := 0xab282e74bea9606c0ade86db04c0a629863daaecca54d524835cd195332a6a92418f6acc2e95254520e5b45d510a92a29073d22ea33549514839ec174a9302a8a41eb61a85498154520
def z3l9 : Packing := (8,5,6,0,0,6,0,z3d9)
def z3d10 (i : Nat) : Nat := (if i<1 then 0xcc54d524837daaed5354920fb6a8854d52483f9a9995354920ff498354d524837f2aee3354920fbca888cd52483fb299a3354920b7e8c96c5524827be71abb6052097f8c96e981482cfe325a860520abfacc6a1814832feaeda860520e3f8c96a181483af66a23360520ebe9a8549814825fe325ba545208ff9c82e9514823fe70cba54520cbf8baa21514833f62ea3354520bf6acc549514837daaed5254520fb6a8854951483fd28cd5254520cff0ba60551483afc6a18154520ff6152605514825fe326bb4c5208ff9c82e9314823fe714ba4c520cbf8baa21314833de2ea554c520afdacc68d314833f6aeda34c520ebda8868d31483bd6955a34c520cfe8ba549314837da6d5524c520cff0ba60531483afc6a1814c520efd1a360531482dfa325b848520b7e8c96a1214836faaee8848520b7e8c96d5214827fab31b548520d7e8c96d5214836faa21b548520df6abb95521483edaa225548520dfcabb8cd21483ef2a223348520dfc9b58cd21483fd29563348520bfe2cc4c5214837f8aed3148520fbe2884c521483fd89553148520ffc1a34c521482dfc325a884520aff2cc6a2114839fc325a884520ef71a895611483edca225584520aff2cc68e11483afca21a384520ef725568e11482bfc7298384520efd1a88ce11483ef4a223384520ff52558ce11482ff8b315284520efe1a854a11483ef8a215284520ff615354a11483ff08cd52845208ff9c5aeda84423fe70ebb6a1108ff9c2aeda84433fc706bb6a110a7f8c96dda84429fe325b56a110a7f8c96cda84429fe325b26a110adfacc6a2774431fe2e5b369510af7acc6a2554429fe325a568d108ff9c8aeda34423fe716bb68d10cfb9c4aeda34423fe70abb68d10a7f8c96e1a34432feaee8868d10e3f8b9a21a34429fe325b768d10cdfabb9dda344397e2e67768d10e9fa889dda34429fe325b568d10cf7abb955a34439de2e65568d10eb7a88955a34423feb31ba60d10c7f8c96e98344337e6ea7760d10cf79ba955834423feb31ba54d10c7f8c96e953442bf6b31a88cd10ebda8869e33443b766a2778cd10ef59a8956334429fe325b868910cbfabba21a24429fe325b568910cf7abb955a2443adea225568910cfdabb8cda2443af6a223368910ef5a558cda24423feb31ba60910c7f8c96e9824433de6ea5560910cfd9ba8cd824423feb31ba54910c7f8c96e9524423fe72da854910cfd9ba8cd524423feb31ba4c9108ff9cb6a1324432fe6ea884c9108ff9cb695324433de6ea554c910afeacc6a222442bfa7298588910ef69a895622442bfab31a388910ebea8868e22443bda955a388910afe9ca60e22442bfa7295388910efc9a88ce22442bfcb31a854510cff2bb6a151443bf46a23354510ef71a854951443bf86a22254510af68ca54d524833da2e95254520 else (if i<2 then 0x785c502126a1c2d2805139338f78bb8a786b8077cb78f77b76772b6ef6b364f5c358754b50f4d34bf48344740b3f73bb37f36b32f2f32b727b23f20319f1631270eb0d709b05f022fe6faaf6ef0aef6ee2e7ee6ae2edf2dded7ad66d2aceecb2c76c3abfebc2b86b72b36afaabea82a46a329f69ba97e9429068ca88e8528167da79e7626fe6c268664a6366225e65d259655a4f64ba45641a4063f23b63a23663022c628a24e2121d61c21ae1721360fa0be082046009fa5f41f2df19f05ef1e8de29deddb1d75d39cd5c71c5dc49c0dbd1b6db09aa5a419dd9a19659298ed8b18758397fd7c178574970d6d16bd6a969568161d6095f55e15cd5b957d5415054c94b54a148d4293ed3b13753392fd2c128524920d1d119515911d0b907d018fdcfa0f64f28eeceb0e9ce60e24e10dd4d70d34d20ce4c58c1cbb8b54af0a8ca50a3ca009c49889749389249108fc8e88d48708347f87bc75871c6b867c6185b45785144d849c4604243e83ac37030c2d02942802442081a41680b400277e71ebb54960fe6a5558e22583fb25963388960ff4a558ce225825fe326bb609309fd9c3aed824c25fe325ba5893097f9c82e5a14c34fe2e68868530d5f8b99dda14c27be71abb6053097f8c96e9814c25fe325ba5c53097f8c96e9514c25feb30b954530d7d9c32e5514c25fe708b954530d7d8b96cd514c35fa2e622545309fd9c5aed314c2df6720b94c530b7d8c96e1314c36f6aee884c530f3d8b9a21314c2df6325b74c530dddabb9dd314c3d762e6774c530f9da889dd314c2df6325b54c530d7d8b96d5314c27f6b31b54c530d7d8c96d5314c2df6325a54c5309fd8cb609314c37f2aee224c530fbca88889314c37f26d6224c530bfd2cc605314c37f4aed814c530f7d0b9605314c3f749dd814c530dfd1b5605314c3ef4609814c530ffc222605314c25fe325b548530bfd2cc4c5214c37f4aed3148530dfd1b84c5214c3ef4a213148530ebf28869e114c3e7ca227784530b7f0c9696114c2ff4b315384530f7d0c954e114c3ef4a215384530ff518554e114c3fd454d5284530fbe28888a114c3fd89562284530ffc15388a114c25fe704b96a1208ff9c3aeda84833fa70abb6a1208ff9c1aeda84829fe325b16a1209ff1c1aeda64825fe325ba6152097f8c96e965482dde325a8955208ff9c8aeda34823fe716bb68d20cfb9c4aeda34833f670ebb68d208ff9c1aeda34832feaee8868d20a7f8c96d9a34833beaee6668d20a7f8c96d5a34833deaee5568d20eb7a88955a3483b9e99a5568d208ffacc6e9834825fe325ba58d2097f8c96e9534833be2ea6654d20afdacc6a233483ed6a22558cd20ef59a695633483f9699a558cd20b7e8c96e152482dfa325a854920dbeabba2152482dfa325b654920deeabb99952482dfa325b354920bf6a else 0xac06870b30101041009871026108020070e104c2098413e1c5ac027c38c00081010003c38400004000a0410000140820c40200040008041000209875000848107100a0410404100030107070e0e1808209f0e200002a1c40a1c3c38404153020530120824107870f0e1660204040808008081010202040408083470e8e140828104080a04102028104080a041c1c383840800840404080820100190080080810140b181010140b1810101000210825808058c0b180e301020200040008000f041f0a3c1b602000401080214081e10048f080000000078405000200020084010802142c1e10168f080007830f040102c40080020001e1000020800078400041f0a04100020104000c04140828f04020c04100830104000000400440000002083438687090e1000000d30226034c04010d30187830f04000a0c100020004000800127820058e227820068e2d1c3a3840008001000281040000502083070801a389020830708000103c300028820e2441071000010800d1c44f040c8059008001000010000000000f08000a201440205f20200020b7202458201720205b90122c1e4016122c1278248059009041a5834b049624044b0590082180a30102e581230100))
def z3l10 : Packing := (247,4,6,0,0,12,0,z3d10)
def z3d11 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x963483fbd2aac6905ffabb54d20bff374a9a41bfe6e953482ffcdc2a6907bfa8854d20bff36ca9a41bfe69953483f7d332a6907f798554d20ffb306a9a41ff66a233483fecd3466907fd9a58cd20ffb30b19a41ff659633483ff4dc2a4907fe9a854920ffd36ca9241ffa69952483ff4d9aa4907fe9a354920ffd306a9241ffa58d52483ff4d8aa4906ff9a868520f7f510d0a41bfe695a1483fbd2ab42906ff9a368520ffb466d0a41ffa549a1482ffd5db02905ff9ba60520dff374c0a41efe6a181483fbd2ab02906ff9a360520ffb466c0a41ffa54981482ffd5daa2905ff9ba54520dff374a8a417fe6e1514837fcd42a2907bfa8854520fef34aa8a41bfe68d51483fed19aa2907fe9b254520ffe302a8a417feaed31482ffcdd262906ff9ba4c520bff37098a41bfe6a131483dfd44262905ff9b54c520fef4aa98a41ff668d31483ff4a9262907ff1814c520ffd37090a41ffa6a121483ff4daa42907fe9a548520ffd30a90a41ffa6cd21483ff4d1a42907fe98348520ffd2a690a41ffc6a211483ff8d2c22907ff18584520ffe34708a41ffc60e11483ff8a9c22906ffabb6a110dff36ed4221bfe6d5a84437fcd9b50886ff9b26a110dff576d1a21bfe6e1a34437fcdbb46886ff98768d10dff36ad1a21bfe615a34437fcd9346886ff9a760d10dff350b9a21bfe6a1534437fcdc344886ff9b568910dff30ad1221bfe6cda24437fcc1b44886ff95368910dff346c1221bfe6a1524437fcd1aa4886ff9a84c910fcf4aab1ac1fb659633583fad2ac66b07ee96588960fed4ab112c1fba58e22583fe519c44b07bea8888930dfd34d11261fba99a224c2bfc5cb429857f8b954530bfb57698a61df62e5314c3ded44262987dda774c530bfb36a98a61ff2889314c3fe8c0a62987fd13148530f7e51108a61bfc69e114c3ef93bc22987f725584530ffa2a708a61ff888a114c2bfc5cb50904ffabb6a120cff172d4241edea22554837bcd34aa907e7a66955209ff576d1a41afea21a348377d33346906f7a5568d209ff374c1a413fe2e9534837ecd4466907bda888cd20dfb34d19a41fb699a33483fad2ac66905feabb54920f7d510a9241fba99952483fb4a9aa4907fca3354920d7f350c0a413fe2e951483fb4a92a2904ff8ba4c520dfb34698a417faaed21483df544242905fe9b548520fed4aa90a41ff28cd21483ff098a42906ff1a884520f7e51108a41fdc956114837f8d1c22907fd23384520ffc2a508a413feaeda84435fd4434e886df9a89dd10def3512aa213feaeda34433fc5cb46886bfa8868d10dbf4eed1a21bde955a34427fcdd306884ff9ba54d10dfb35119a21bf669e334427fd5db44886bfa8868910def4aad1221bf68cda24427fcdd304884ff9ba549109ff37499221bfa6a2224437f4d1c44886ff1a854510 else 0xbe14f70bda6f5e3d4af473ceef303c92f193c36ef93ba4eddbb48ec23ab6e9dba36e8239ece6fb97ee5438fee2fb87ee143822dfd37c6de1b734dc636eadaf368ed983632d8135c4d613556d45b4d6d25b456d0a33faceeb38ccd7b31ecbc32b0ca0b242c80b1e6c72b19cc5bb12ec4030d2c24b076c16b01abfb2fd0be8af62bd1af18bbaaebcba3ae72b912e16b7eadccb6c2d82b552d26b39acb8b22ac4ab072beeae72b6ead02b24abdaac8aa22a5aa8b29daa6b297ea542922a3428a2a1d28229fd27b49dd27349b8a6a29a1a65898aa5fc973a5a0958252093824a0913a3fc8e1a3348afa26c87da18084720a6819a0147f51f947d09ede7a31e287711d4e7361c746ff9b886cd9ac069b99f8669993062e98445f397585b8966c57d959254714a650c13ba4d113164ac923c471916244890ac40d8fc03db8f403bb8e9c38e0dd43578ce831c8bfc2e18b102ab0a36274894a23088161f587601ba867417f858814484ae10e03b00ca02b208f01c605400c801480017feaed535837fcdd2a6b07ef9b654d60bff576a92c1bfe6e952583f7cb1aa4b07f795354960ffb466a92c17feaed325837fcdd264b05ff9b54c960fdf2ca992c1fde95532583ff4a9c44b05ffabb69930bff576d1261bfe6a1a24c37fcd3344987efa6668930bff576c12617fe6e9824c37fcdd304985ffabb58930bff374b1261ffa6a2224c3ff4d3444985ffabb68530eff172d0a61bfe6a1a14c3dfd44342986ff9a768530fbf4eed0a61bfe695a14c37fcd1342987fea2268530bff576c0a617fe6e9814c37fcdd302986ff9a760530fbf4eec0a61efe609814c3ff511302985ffabb5c530bff374b8a617fe6e1714c3dfd442e2987df9875c530bff576a8a617fe6e9514c37fcdd2a29877f8b954530ffb366a8a61ffa889514c3ff8c0aa2987fdabb4c530ffb37098a61ff66a1314c3fecdba62987fd9a74c530ffb30e98a61ff66d5314c3fecd2a62987fd9b24c530ffb34498a61ff6609314c3feca9262985ffabb48530bff37490a61bfe6e9214c2ffcdc242987bfa8848530bff36a90a61ff654d214c3ff8d4422987ff1a784530ffe30f08a61ffc696114c3ff8c2c22987ff1a284530ffe30508a61ffc54a114c2ffd5db509077f8b96a120dff576d4241bfe6cda84837fcd8b50905ffabb69920bff576d2a41bfe6a1a5483dfd4434a906ff9a669520fdf4ccd2a417feaed85482ffcdd30a906ff9ba61520bff576b2a417fe6e965483f7cd32ca907f79a895520fef34d2aa417feaeda34837fcd4346907bfa8868d20dff34cd1a41fbe999a34837fcd2b46907f7a5568d20dff576d1a41bfe6e1a34837fcdb346906ff9b568d20dff30ad1a41bfe595a34837fcd8b46905ffabb60d20bff374c1a41bfe6e983483fbd2ab06905ffabb58d20bff374b1a41fbe69) else (if i<3 then 0xe2ac09a085ac0c34d0ac0d0ac7ac0c2ec7ac0dc5581342b024282eb0300d4051aa808021aa80e355010050b501c6aa020d5400230087aa03a806a0100d4051ea8083c85a80e3d621262c4205006b03ac06b0100d60c4305560558082c02205216b03ac06b00a1161c4200810404c28b0a100b88404c28a0a100e14505081002282b60402710a2050008c0350100434205b62a030f38840102080c0202004802710804d8100428b6c0802e210040c041805c4200b6041c035883c4b13604d8b10ac4c71352c42030100547238a8e26a51c42605c1db046c51c42183b886046a51c62105d1c61705d1dc4410d1dc437104a8011005c420231c41f638802c7107ea8c71a881754182d0f54181145471c41b1478f1121476c278994a3e89b185c81aa9856c278987aa689b185c819455463a7899863e8aa985c8193d98c2d51c587361d3154c2a78b98c2b42a8e2c39aa187020c1550ac61c907a8614750428106e283d430a483b61a950c296a1076c61480483b52a18528083d0771614a0243810a154c29b2950cc615c587361d4550c2a2cba2c2b52a0d8c39b29a2c2d41b18735410ed8c2934598c2d41a987358b28850f903e1e0c616c594358b28850f913d87ac38b0b9433410f94c2d613c6c3d61c4d0c2e50c0281088301e0b9a21188be51c54734622ee2ca3428e6ca48a2f1e6c51cc210087f2962a3983d47ac0044254f2603f947151cc9ecc615c547ca19a098c2e528e9e36630ae26851f286c8689b185a3e50d85058a171471616b0585c51c4d0c2d60c011082d8f858a1a16c78a616b05ca616a030107aa185ca028c010502ea1854a18161eca5430a0430132985a8130a1a146a2950c291b1508a61491a6c452a18528118f858a540a010231ca114c2990ee24c6530b50361f30e2a86172868f61db150c2e50c1e4c0132950639a3d98c2d418f94322d2950c2b60b060a01c17850f1b2107716161654f6410f54c2d61c4705a79c487c2d632078300a04220c6141790a3a72085020f21478c42dc585348a8ed4c83630a605d1e45906c614d90a38601762c298161ea3e42b1853641309e45d1dc46a3a8b218545940e220c6143401346b21078c5530ae23c6a0f54916430ad83c8a3004aa6418e6026403154c2d88c040f5532185ac183c18025532147327b20874c616a8e23a893004c85518e60f615c558253f94ee53794ce530b4b752af49bd22f48051c1464d153444d0d3424d053404cfd33e04f533c94ed33a94e653894dd33694d6534dcce532dcc7730dcbf72e94b772d24af72adca7728dc9e526dc965244c8d3220486520dc7f71f247891d2471b1b6c68919245f71724589152451b1324489116c41b0fb43d10e443630c8c2f50ad4275088c1f506d417504d40f5031c0ab016402b003bfe0fecbf84fd5bf28fbebebafa7be82f90 else 0x841f5818840f581a884358183c3d58186ab0243d6041a638a1f1eac0c1e1ea38c3547103c3cd81a628e287c7a8e347b1d3c3c383e043008082e38385dc430be1dc438bc0b0e30f80ac587207f0e2b161c41a015430e42861c4a44161c6a46861c60a0161ea040261c462c3d40750c388a08783b60950c388b187a80ca1876a0c0902c38c041ea861c850c3890f50102c3c87a8120587a80ca850c38e0587a80c340baa61c854c388040b2861c90285d430e42818b0e3055400587261c350c3881550c38ea00a140aa1871988b187180808201541c431201ca002200a20d4185db007a81220d8100aa0d8180a0f501b500820200a0f50200a20e21c41b020200b0e30261c587089005871c0b0e20b80b0e34382c4a44161c6974161c68245b8b0e44161c4827161c6974161c7877120868bc3b6061cb1083e10e0043f62207d8e268041f6210281623156050bac09a158142eb0213006b03ac06b011307aa030d5404010d140b04710534d0100a8e23151c517a389a147145e8e26c51c517a388021f0151c81f7151c6d0a38a8ed8109a0ed818983d07681008d0a38c4801a38c3f47151c324a38849472f0c034710043450a39249478f0c4201ac0c8f58101eb0210d60421ac08021e710c42900f560958091dc422c38841f710934d0122db02533604a66c278685715606))
def z3l11 : Packing := (311,3,6,0,0,14,0,z3d11)
def z3d12 (i : Nat) : Nat := 0x4216a81e3d0b20b08f44a0f17020b1e54a2859058507ac4c0b8f42d12a23c8285d60921d658940090a0b02ec50ea80471f1e505898028562548750d2c4c010f42b12a2843a95189621d4008c0434a83cb1310aa0c50ea1a62a20b0285585054875050d31512a0143a82c42a8098a8962606a1541521d58fa1b0c5290a61ac7d862859450385f163ca6842ac1c791e1c9806518a15612028f0e4c3cb0c50b28a0a17e2d847d0948538f2c4c1200a3b14a42a405626090791d8a1651414432002c48eb1290a81a94508501280ac4c23c38f3142ca282804298a891e1d62154251402083cc4b1308ea1290aac7d485581e2cf63ea5142ac481f635214651c78d333db10ba9448f2089ed8c7a28554903acec42ea438f196762175189421cfb1c50ba0a90e6e207d8d450853716c42ea28439b631f418a5214db18fa0c50b28650d8c785941e36c63b142a84a1b1f8963421650c2e3db1c48fa1290a8d8e285d0479430a6385f16842ac1f8b631c51406a14fc5b18f0aa12861e0bc7d862d4859047163c2c805942f8b611f524214e03c5b18ea9210a348c58c03baeb69b2cad7a82a4d9f89a394e8f98c488784a7fd7a876b71e6c96846576025ad55852b4ee4b94744374023c539035b3262f12bc28725221d1d81a31661290f40af082045000ffe54d60ffe54960ffe4c960ffe69930ffe68930ffe60930ffe58930ffe68530ffe60530ffe5c530ffe54530ffe48530ffe6a120ffe69920ffe69520ffe61520ffe59520ffe68d20ffe60d20ffe58d20ffe54d20ffe68520ffe60520ffe54520ffe4c520fbe59560fde95560fbe58d60ff68cd60ffa88960bfe69930fbe99930ffa88930ff64c530ffc84530bfe6a120efea2120bfe69920fbe99920fde95520bfe68d20ff68cd20ffa54920ffa48520ffc84520bfe6a110bfe69d10bfe68d10bfe68910
def z3l12 : Packing := (49,2,6,0,0,12,0,z3d12)
def z3d13 (i : Nat) : Nat := 0x2c1e8e651540a411671580b528073d88f8a805286cabc07fe583ff261ff920
def z3l13 : Packing := (3,1,6,0,0,7,0,z3d13)
def hashz3l10 (i : Nat) : Nat := 0xe1f807e83fe07ee5f807e81ff8ffc03807e01fc80783f987ee1f807f81f987ec1fd87fe1fe87ee1fd87fa1ff00ae1ff87e01f880501fb0ffe3ff8ffe3fb0032dfc07f41fd00de1f907fe3f88fff1fe87f21fc07e01f807fe1fa000c1fc87f21fc87e01fc87fa1fc07e00240fe81f807e41fc87e1021f103c0200e431800209000
def hashz3l11 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x1fff40a930ffc03ffd0ffcc0e8d0ffd040dc0ffe83ff61263807490ffe47ff91393845930ffc40bea0fff43ff91ffc07ff91ffc03fff0ffec035e0ffec7ffe027ee3ff802dd43ff8003f47ff50ffd47ffd03b3c3fff0ffe87ffb0ffd87ff20ffe43ffa1fff43ffa1ffdc3ffe1ffe80bd71ffd47ffa0ffc449fa1ffec0e10000203ff61fff43ff10fff83ff86fffc49416ffe0413b0270000050ffc000010fff43ff0000047ff30ffd43ff0000143ffa0ffc000000001c7ff00003c7ff80ffc0000f0ffe83ffd0ffe83ffb0ffdc07640ffc40f410ffd87ff90fff43fff0ffc004f701b147ff28ffd8003f6ffc000061ffe07ff0038fc3ff10ffd03ff30ffd03ff10ffc00c990ffd03ff8022983ff702ac83ff0000183ffc0fff47ffe011ec3ff0000000001037ddfff50ffd07ff31ffc07ff00003c3ffb0ffd43ff40ffc83ffd0ffd87ff400d980ac81fff47ff3029c43ff10ffd07ff301c983ff41ffe43ff88ffc83ff91ffe07fff0ffd4070faffc040250ffe83fff00aa83ffe0ffe802731ffe8019b0fffc3ff63ffcc030c6ffe43ff51ffc43ff74ffc03ff7036183ff50ffc07ffe013587ffd0fff03ffe0ffec45cd1ffc47ff60ffcc3ff90ffc03ffe1ffd83ffa0ffe87ff70fff83ffe1ffc404100ffec3ff20ffc40dc51ffd03ff303108046c0345c3ff60ffc83ffa0fff03ff50ffc83ff30ffd43fff1fff83ff70ffdc3ff40ffc004b601d50024a007e83ffa0ffec7ffe1fffc3ffc116147ff9005e43ff70fff43ffd0ffe43ff20ffc83ffd0fff43ff060000130601011206011105010414400408151a0b000437000d0b000019011e03110819040c173702026b1f3f0022000b0a010208061c0b08020a1003020204080b002d230b01041223091f0a00364a1e0000500f081206053e040801100e0006020a00670a4a030506010601070a0719014c01020200020300000305180e021311040102170105d500041a0b16031e0e00070000640f0405010223083c0d230629020600000700461b292e4100060026001b0900000007000201000b001904003c003600021b020f12015d031f6d01270d00000059020e00120114053a5b0a14003a0d0206050f2f1409030004060021020921000d16010005e000000002000905080200000b02000206050001040a020a0000020009010c00001902103a03430008072c01200b1f2c0e01050327190a0d1800360100280b0004000000010303011c1e03324b70063b0c2c00032c063d002a0000000200001e120102040e020006000402100e0003080101210007191a2a00060302280317010002050721001301060406041b0609060903096600390600003a00000c014101090b052e00000c1f05040808000800000c050003012500000201004a034c022c08000400290c3f00172d13260b08011000000101 else 0x83ff0000207ff41ffd40aa90ffe83ff40ffcc3ff60ffd402e0101303ff80ffc408520fff03ff221ea23ffd101d03ff9008343ff40ffe83ff2029a03ff51fff03ffc0fffc3ffc1fff83ff70ffd03fff0ffc87ffbbffe07ff00001c3ff6123fc03f90fffc3ffb023983ff90fffc3ff01ffe87ff0032e23ff71ffec499f0ffe47ff30ffd83ff70fff00eb78ffd03ff11ffd03ffc8ffe07ffe0ffc83ff90fff07ff112f080f571ffc000050ffe40bc50ffc0000001e40000d0352005791fff03ffe0ffe83ff0000183ff0000340ba00000c3ff0000143ffa0fff83ff00003c3ff40fff005a0022d87ff00ffec3ffc0fff40c79021f87ff60fff87ff91348000018ffc40d220ffd47ff20ffd408d0000040de40ffe43ff8028a87ff71fff03ffe124783ff0000303ffd1ffd83ffa0ffdc3ff40ffd40e080ffc000060ffc83ff203b9c3ffd0ffec7ff00ffc4408a0ffc03ffd0fff03ff81ffc04c1b0ffe40088027803ffa0ffc0000c0ffd40a890ffc000080ffd03ffa2ffc0000d0ffc83fff0ffc47ffd031643ff403038bffb0ffc47ff0010a03fff1ffd87ff0000083ffd0ffc0000c02ec47ff40ffc000000ffc03ff0000313ffa1ffc000000003848172ffdebff10ffc000040ffdc3ff00003c3ff0000240ce40ffc000080ffe43fff0ffc0000701f144b80000144f370ffc47ff000000000b0fff47ff0000083ff70ffdc3ff90fff87ff00000000090fff13ffe1ffc03ff30ffc00000000243ff0016e47ff1affc041070fff03ffb129cc3ffa1ffe446440ffd43ff6039783ff212f6009400ffe03fff0fff43ff40ffec3ffc0ffc042f8102bc7ff70ffd43ff200c9c3ff501bf8089f0286048810009804cf1ffdc7ff00ffd83ff70fff03ffe0ffe43ff0affd80151124fc3ffc005b8040c0ffe83ff7124243ff0000383ff81ffe07fff0ffc03ffe107403fff0ffd03ffd7ffc003a60ffc43fff0ffe83ff01fff83ff6037583fff1ffc03ffa00e284bbb113dc083702e747ff00000c0ed2003143ff0000003ff10ffdc7ff0000183ff2130147ff801afc06a343c8009271ffdc3ffa4fff03ff00000000031ffc00006125400000000343ff01fff43ff80ffc00003006f47ff02ffc000080ffc000020ffc43ffb0ffd44d3a0fff87ff71ffd40bf40ffc83ff02ffc0000d0fffc0990000183ff50ffd03ff9026883ffb0ffe07ff0000000000000283ffc0fff03ff50ffd87ffb1ffcc3ffe0ffcc7ffe0ffd80f6a0fffc3ff00ffcc3ff70ffc000070ffdc3ff613340000f0ffcc3ff61ffc406d00001c3ff80ffd43ffd0fff03ffd0fff848000000000021ffc0000412980000d0154000001ffe8053b0ffc000000000000020ffdc3ff000014025a1ffd2bff00ffd43ff9102c03ff40fffc3ffa11f903ff21ffc0000c0ffc40e4201fdc3ff30ffd43ffc4fffc3ffc) else (if i<3 then 0x21ffc83ff00ffe83ff0000000004122e43ff000002fff91ffec3ff40fff07ff5031a00c30000007ff0000344650000343ff40ffc47ffe02d443ffc0ffe03ffb0ffe40c1400a6c3ff902b447ff0000387ff002c40000b0ffc0000301cc80eab0062c42b40ffd87ff002bc0000d0ffc000050ffc87ff000000000f1ffc0000000000000f0ffd47ff70ffc03ffa0fff87ff91fff03ffe6ffd007d0000383ffa0fffc3ff00000c3ff00001c4be613d40000a0ffc000080ffdc3ff51fff400511183c056c0ffce3ff00000000011145c3ffb0ffdc7ff61ffd47ff0000183ff0000203ff90ffc03ffc11c3407190ffdc7ff40fff006240ffe00679001043ff90ffec3ff81ffdc3ff31fffc08420ffe43ff80ffd804a10ffc03ff01ffd400b31ffe8052d10c044c490ffc03ff801a203ff61ffc43ff90ffcc7ff20ffd03ffc1ffc03ffd1ffd404381ffd04c2b1ffc87ffe0ffcc7ff63ffd43ff20ffd8bfff0ffc4049c0fff43ffb0fff63ff81ffd00341130f83ff8125f43ff7020ac3ff00ffc03ffb0ffe800980fffc06311ffe43ff10ffe00c80000307ff801e80000000000000e0ffd83ffb1fffc7ffd0ffd87ff60fffc07b90ffec3ffd1ffcc3ffa1ffd83ff00ffd07ff38ffc4069a5fffc3ff91ffe03ffa0fffc3ffb1ffe07ffa0ffc000070ffe87ffb0ffc47ffb1ffe402390ffe07ff41024c0f34135b4bffb1ffd07ff40ffc83ff20fff83ffe0ffec06468ffd04db30fff83ff111b9006641ffd83ff32ffd47ffb004a44e670ffc00b800ffc0000c1ffe83fff03c283ff402cd03ffd2ffc83ff11ffe4096e1ffc8489a0ffd8080611ee87ff30ffe47ff312dc402d2114c87ff20ffc40ca1035b4bfff024d43fff0fff00b0e00cc47ff90ffe53ffd0ffe43ff2035587ff70ffcc3fff036b9bff11ffc807e20fff03ffb0005042530fff43fff02451bffa007907ff6007043ff40ffc000070ffe83ff90ffc83ffb0fff03ff2126c43ff60ffc87ffcafff43ff810cecfffa1ffd00b2000000028f2ffc0000d0ffc43ff80261005db0ffe048a900c6043f80ffd43ff70fff80cf85fff83ff00ffd447240ffd841a70ffc83ffc3fff8065300b2c3ff461ea83ff00001c3fff1ffc84f4d100c0000000024051b0fffc3ff000001fffe004e03ff0000243ff68fff43fff0364000000ffd87ff7017843ff40ffdc7ffc0ffe809dc0ffc000001fff83ff9003800000000347ff30ffc43ff30ffc000030ffd07ff8025c000051fff03fff0ffd03ff40fff43ffe0fff83ff82ffd83ff41ffcc3ffd2ffc000090ffc43ff41ffec3ffd1fffc0224023c0000e0fff83ff50ffc43ff50ffdc7ffb0ffd43ff51ffc03ff00ffee3ff31ffc07ff65fff04a8d0ffd0045f1fffc3ff81ffc00e2b0ffd0405b0fff83ffb3ffc000038ffe47fff1ffc43ff0000007ff00000 else 0x3ffd0ffd07ff30ffe13ff00ffd43ff4018503ffe03c9c7ffa0ffd47ff20fffc3ffa0ffe43ffe0ffec3ff10ffd8427c0ffe43ffc0ffd87ffe0ffe00a071fff07ff61fff83ff0000223ff50164c42c00ffc47ffb0183c3ff90fff03ffc1ffc43ff31ffd03ff10ffc03ffe0fff07ff31ffc83ff71ffdc3ff20ffc47ff41ffcc4a000ffc80d3412ff43ffc0fff07ff41269c0a532fff47ff70fffc3ff36fff03ff6013a83ff00fff43ff70ffd47ffe017cc3ff20ffec3ffa1ffd404401fff43ff80ffc83ff3001a03fff004607ffd104543ff70ffe001aa124947ff30fff002f3030800f1e0243c4f63028cc3ff4002b43ff60ffcc08890ffd87ff100af43ff80ffc000090ffdc7ff00001c3ff81ffc03ff5103a003c41ffc43ff0000203ff52fffc3ff51081c3ff30ffcc3ffd0ffdc3ff11ffdc3ffd0ffc000000003c7ff40ffd03ff71ffc4415c0ffe47ff71fffa8f2d0ffc6bffd0ffc43ff31ffc43ff40ffe00958008583ff12fff07ffa015283ff003a4c7ff30fff03ffa0042c3fff0ffe1bffb4ffe03ffd001f63ff0000083ff20204000050ffd80cd50ffd43ff0000140b430ffdc4c55039e47fff1ffdc3ffd0ffe83ff30ffe0fffa1ffd43ffd0ffd8048f0ffe847c70ffe83ffb6ffc80ae801e203fff021803ffa0fff83ffd0ffc07ff00000cbff10ffd07ff50ffe43ff27ffec3ff30ffe83ff30ffec3ff00ffd87ffe0ffe47ffc1278845670ffec3ff00001c7ffe0fffc7ffc0ffe401de0fff87ff20ffd0bffe0ffe83ff30172c0db30163c09b20fff43ff21148c3ff31ffee3fff0fff43ff60ffc00000000080d0e0ffc43ffa0ffc4bff30fff07ff31ffd83ffa1ffd43ff40ffe43ffd0291c077c02db03ff50fff0426d00e683fff1064844d0000183ff21fff03ff0000207ff00050005000000000000000000040ffe43ff9000303ff80ffc87ff0000083ff2125b03ff20fff83ff41ffd83ffb00fac3ff50ffc000091fff43ff20ffc049d51ffec3ffd1ffc23ffb01b900ccb0fff83fff0fff83ff300de03ff70ffc03ff6023283ffa0ffcc3ff60fff43ffc1fff03ff78ffc43ff40ffdc3ff0000393ffd5ffd8026c003763ffe0fff8bff111fc1bff20ffd07ff3039b43ff70ffe03ff01fff43ff56fff43ff51fff403b87fff47ff100f707ffc035c40ef10ffc000060fffc7ff0000143ff))
def hashz3l12 (i : Nat) : Nat := (if i<3 then (if i<1 then 0x7ffb07ffd0fff81ffd4067407ffb0fffa244307fff8ffff1fffe3ffc83ffd87ff91fffa024347ffa07ff30fff83fff000618fff50183c1ffd43fff80026103961ffc03ff807ff10ffe41ffc07ffe08d83107463ffdc7ffb07ffa0fffe1ffec7ff907ff01ffe00237c7ffb07ffe1fff43ffd03ffb87ff80fff03fffc01bb8fffd8ffe01ffcc7ffa3fff61fffc040983ffb87ff60fff2203a8449a07ff51ffec1fffc3ff80fff60ffea04804010507ff50fff41ffd4063e80a500fff601cc03ffc8918c0ffe01ffd03ff887ff31ffea1ffc83ffe81221121e01ffc03ffc07ffe0fffe23bd03ff807ff72ffe01fffc002807ff10fffe1ffc43ff807ffc0fffe1ffc43ff907ff30ffe63ffc40724813512ffe63ffd43ffa08ad71ffea3ffcc3ff847ff310b02020003fff0fff00ffec1ffc83ff807ff10fffe240583ff807ff00ffea3ffc03ff807ff00fff0012b47fff47ff60ffe81ffcc3ffe0fff60fffe048dc07e807ffb1fffa1ffec3ffc87ff00fff81fff03ff807ffe106041ffe43ffb07ff80ffe01ffc03ff807ffe0ffe003c0c068380e650fffa245c03ffa07ff00ffe623fa804168fffc0ffe01ffec498e87ff00fff81ffc8097807ff70ffe81ffc03fff87ffa0fff21ffe47ffa0038a0ffe01fff4098807ff6111c01ffd03ffa07ff0559210506030a010e1f08000620043609040001110e01510303020b01030303080101060b1800002901025b0b1a0005070304002b195b1c0001030d06330025000207131d1e0702360a0606086d001605030017040c0115010002020104140f0f100c00002b0118032704021a0a011c0b057802151f010a010c1e0a1c0f0b06010102076642025b00031e00000103390d02010c0e1a0500001109070b0004033001060c00681f280501000d0200051b080200011b0410550c1b2e041110090500030008181017000a2d3f0d00050c1318090212153d00090815061a020901040501010002000306020e010201000904090b1d02070f250b00080504016a020300040040020800010100001c3111180102010b0919060e130600071c000c033c0e118a180e170406004101010301460056150d20023c04090217070403d01005010a1b05041c00010310040400010033003a0a010615040c00000018020d55020f031a000706020e040301054601041425351245154809030c0109040c1b424e091f000c140304050a000005010a01051708060107010700002902030008030c07072d011901030000040001440104010d6a0169150c0b090d0013080c4e081a01089100180f081a200302001e00000500110216010621060108200f02164601000913000304171e1102000e08250e14004704192504001c000b0e2b01191b120b0002660316101a0b0c0005010301011b080c02060e0100000131231008000021 else (if i<2 then 0x8fffa7ffea1ffd03ffe87ff20ffea3ffe83ff807ffe019b81ffec3ff807ff00fff21fff43ffc07ffb001323ffc03ffa87fff0fff81ffe43ff987ff61fffc229447ff807ff4000ea1fff47ffb87fff015e01ffc43ff807ff08fffa3ffcc7ffb8863a0ffee1ffd47ffd8fffd11e0c1ffc83ffd8fffa1fffe1ffd83ffa07ff61fffa1ffec3ffc87ff71fff83fffc05d48fff40ffe21ffc0bffb0fff91ffe81ffe405cc091e50ffe223d803ff9800ee0fffa1ffe87ff887ff4000121ffe03ff807ff70fff41ffd03ffa0fff80fffc1ffec3ff80ffff01efa3ffc03ffe87ff96ffe4021f43ffc07ffa1fffa3ffe83ff907ff00ffe63ffc03ffe8fff20ffe41ffc63ffe07ff00fffa3ffe00265083670ffea1ffd4076007ff90ffe41ffc03ff98ffff1ffec034403ff800e0f0ffee1ffd43ff880b580ffea1ffd843308088f1ffe83fff03ffd87ff51ffe6fffc03ff808ecd003ee1ffe87ffc0fff30ffee00564026ddfff20fffa3fff03ff807ff66fff01ffcd3fff811701ffee1ffc43ff98fffe0fffa1ffd8421187ffa1ffe01ffdc7ffe893310fff61ffc87fff07ff00ffe41fffa3ffe0fffa01ad43ffd83ff807ffa001401ffd03ff807ff00ffe01ffc03ffb07ff91ffe11ffcc3ffd87ff60ffec1fff445cf87ffc0ffe01ffd801c887ff80fffe230b03ffe0ffff0fff61ffc802088fffe0ffea1ffd87ffe07ff00ffe41fff0008d8fffb0ffe21ffc43ff88fffb0ffe63ffd03ff807ff70ffe41ffc03ffb8071a0ffe61ffcc3ff987ff900bb42106c7ffe8fff40ffe03fff03ffa57ff00ffe01fff47ff807ff00ffe01ffc03ffa8828d11d481ffc87ffc07ff401f821fffc7ff807ff90ffe01ffd8025807ff00fff822d9809a087ff40ffe01ffd03ff907ff5112a01ffcc3ffe07ff80fff21ffe03ffe80c230ffe01ffc03ff807ffb0fff21ffc03ffe07ff91fffe02e1c3ff807ff00ffec1ffc03ff98fffb012c01ffc83ffe8fffe0ffe204a7046d087fff0ffe21fff93ff807ff51fffe1ffd43fff00bf50ffe203bcc04da07ff10fff61fff43ffa47ff0008140167c7ffa011e00fff21ffc4024307ff00fffc219003ffb893090fff81fff07ff8afff00ffe81ffe83ffd87ff00ffe01ffe03ffa8fffa0ffe600cd802be07ffa0fffe0264c3ffc07ffc0ffee1ffc803c00fffa0ffee0276c3ff980c870ffe63fffc00e887ff20ffec1ffc03ff807ff90fff41ffc03ff917ff41fff8015683ff807ffd0ffe01fff83ffe00bcb0ffec1ffd03ff887ff30ffe01ffc03ff807fff1ffe404c003ff907ff60fff01ffc07ffa07ff6023721ffcc407c07ff80ffe01ffcc3ffe885a00fffe1ffc8413e87ff90fffc01f4804a10fff00ffe03fff83ff807ff3104b61ffc03ff817ff2126ba1ffc03ff807ff30ffec045803ff880a7f107ee1ffd07ffd07ff11ffec3ffec else 0xd0fffc5ffdc416507ff00fffc24690bffc07ff60fff2242003ff98fff80ffec1ffdc3ffe00e340fffe1fff03ff907ff911e321ffc03ffc87ff91fff01ffd842a007ff4affe402d803ff807ff00ffe41ffc43ff800ed60ffe81ffdc7fff07ff30ffec1ffe83ffb8fff30ffe81ffe8bffe07ff60ffea1ffc4494887ff61ffe41fff4099b87ffa0fff21ffc83ffb80454116b81fff83ff807ff70ffea235e83ffb07ff90ffe01fffc7ffc8fff81ffe63ffe03ffe87ffe0fff2215b83ff807ff0016543fff07ffbafff80ffe204b203ffb8fff81269c1ffc03ffe07ff00fff60255c7ff807ff101ca41ffdc3fff07ff30ffe01ffc43fff0ffff0ffe43ffe83ff807ffe2fff43ffe83ffd87ff6114f81ffe43ffd8105f2fff21ffec3ff807ff900c9a1fff47ffe07ff4014121ffe03ff807ff71ffe01ffd87ffc0fff70fff41ffea3ffd97ff80fffa001243ffc00ca00ffe81ffd83ff807ff90fffe1ffc03ff80035e1073c1ffd8087f87ff00fff00470c3ffe87ff61ffe01ffe03ffe80c43022b423edc3ffe87ff50fff21ffc83ff8008c00fffd7ffdc3ff88829c1ffe01ffc03ff88054701abc1ffd43ffd07ff01fff43ffec7ffc87ffb0fff601ad03ffd0fff00ffe01fff43ff8004400ffe01fff805a707ff00fff21ffd83ffe87fff01fc01ffc43ffc810ed0ffe57ffc43ff807ff60ffe63ffc03fff010b00fffe1ffe87ff807ff5015ae1ffcc7ff807ff41ffe01ffc03ffc07ff60fff55fff001db0019d0ffe01ffc809b5808500ffe01ffec7ffe807900ffe82398004d687ffb1ffe61ffc83ffd8fff6024a61ffcc3ff807ff10ffe41ffec7ffb87ffb115d21ffc43ffe07ff70fff8044c03ffd07ffd025461ffc03ff888ba91fff41ffd07ff908866112c6047e43ff807ff01ffe61ffc4034f07ff20ffe01ffc03ff807ff00fffa3ffd83ff88fffb0ffe01ffc03ffb07ff80fffe3ffec7ffb00cf00fff21fffc3ffa87ff30fffa3ffe03ffd87ffd11d201ffe83ff8803d01fff83ffc07ff80fffd0fff01ffd83ffa07ff31ffe81ffd87ff987ff60fff802a3801b487ff11fff00463c3ffd27ff11fffc1ffc03ff807ff00ffe11ffe03ff807ff10ffe61ffcc3ffb07ffa0248c1ffc03ffc092cb00c0a008c43ffe07ff400e8c3ffc848160fffb0fff201b18005e002c5014c81ffc00665082dc1ffee3fff0054b87ff00fff81ffdc3fff8fff60fff03fff83ff807ffa0fffc3ffe03ff807ff80ffea1fffc7ffb87ff6008e01ffd43ffa87ff00ffe2212643ffc093200ffe8032d07ffb07ff00fff6010bc7ffd0fff80ffe41ffd4007d0fff00ffe41ffe0044e87ff40ffe00245807f987ff51fff202f403ff807ff31ffee04b983ffd87fff1ffe21ffc47ff800e8b1fff61ffe43fff87ff00ffe21fffc7ffe8859f1ffe81fff03ff807ff00fff61ffca3ff8)) else (if i<4 then 0xf6009d842ae0066c1fff0020c07ffb0fff31fffa1ffc03ffe87ff00fff21ffc03ff800f28125761ffd07ff807ffb0fff43ffe87ff807ffa0fff81ffd4081c07fff0fff01ffc03ffe8fff70ffe01ffdc3fff87ffa1fff01ffc03ffb0fff00ffe4036483ffa004f90ffe61fffc3ff807ff500f50015803ffd80a3f0fff400b8c3ffb80f4d0ffec0485c3ff807ff100b7c3fff83ffa881571ffe21ffc03ffe07ff00ffec218a43ffe87ff30ffec1ffec3ffc07ff41035600d1803da87ff50ffee2122c3ffa07ffe013f23ffe43ff8a7ff90ffe0004e03ffa889200ffee1ffd83ffa0fff01ffe21ffe83ff987ffa11f3e1fffc7ffd0fff91ffea3ffd43ff987ffd0fff2221003ffd87ff00fff41ffd07ffb87ff90ffea1ffe07ff807ff00ffee1ffe0027487ff91fffa3fff03ffd87ff00fffc021ac08a007ff00ffe01ffd806075fff00fffc1ffe03ffe0fff10ffe81ffc83ffe801be0ffe01ffc03ffe803f20fffe1ffe07ff90fffa0ffe81fff83ffa87ff10fff83fff03ffd009830007e1ffd07fff07ffe0ffea1ffd03ffb07ff91fffc1ffe03ffe0ffff0fff21fffc3ff8001881fffa044b03ffd8fff90ffee036e43ff987ff1018c61ffe03ffe87ff40ffea1ffc43ffe88fc20ffec3fff801f107ffe0fff61ffe87ff8006a00fff41ffc43fff8fff00ffec3fff03ff807ff81ffe01ffc03fff87ff00ffee3ffcc7ff887ffc1ffee3ffec3ff98fff60ffe8014bc3ffe8fff41ffe01ffc03ffd0108e023a01ffd03ff807ff78ffea1ffe805f38058b1182e041087ff900b33114d203a403ffc003090ffee008883ffe8fff00fff21ffd83ffd005110ffe01ffdc46318fff00ffe01ffc03fff07ffe0fff01fff43ff908905011e002c7c7ff987ff00ffe31ffc03ffb0fff5021401ffcc08d0005c511dba01d403ff987ff00fff41ffe03ff8890b70ffec0143c3ff807ff00ffee1ffec3ffd07ff70fff21fff83ff807ffd008ca1ffc03ffc87ff30fff81ffcc3ffb0fff40fff43fff03fff87ff40fffe044283fff00e7c0ffee3ffd87ffa87ffd0fffa1ffc83ffe07ffa0ffe61ffc805dd07ff1105521ffd43ffd8fff701f081ffc409908fff30ffec20d003ff987ffc01b0c1ffe07ffd87ff811dc01ffd83ff807fff0ffe01ffc400b30fff61fff2dffe8459b0fff40ffe31ffc03ff807ff00ffea035c03ff807ff71fffe1ffd406ea87ff700b401ffe03ffd07ff500ed81fff4079f07ff40ffec3ffd83ffe87ff31ffe20179c012007ffe0ffe61ffd57ffa812d00ffec3ffec44cf07ff01ffe01ffec3ffc8077d0ffee1fff03ffc00b011fff01ffc43ff887ff00ffe01ffc03ffe87ff00fffc004803fff8fffd01ec00196c3ff807ff11ffe61ffdc457887ff40fff222f3c3ffe87ff11ffe01ffc03ffe07ff00ffe81ffe43ffc87fff0ffe21fff8037f87ff else (if i<5 then 0xfcc7ffc00c510ffe01ffc03ff807ff81fffe01f343ff987ffc1ffe01ffc801d007ff30ffee3ffdc3ff90fffe0ffe01ffcc7ff887ff28fffa203487ff807ff71ffee1ffc07ff98fff51ffe21ffcc3ffa808e00ffe01ffc03ff807ff90ffe01ffd47ff907ff201c401ffc03ff887ff5005ba1ffc03ffa07ff60ffe6210fc3ff807ff110f741ffdc7ff807ff20086a1ffdc3fff07ffc4ffe022e0c3ffa87ffa0ffe01ffd43ffc00dc00fff01ffc03ff807ff21215a1ffd83ff987ff50ffe01ffd43ff80802d8fff01ffd449b1c7ffc0ffe23ffec7ffc8fff00ffe223d403ffc87ff00fff63ffd87ffd8fff401e321ffcc405f890e80ffe4043683ff80fffb0fffc3ffc000e307ff20ffe01ffd004ba07ff41fff81ffc03ffc87ff20ffe01ffdc03f58fff610af03ffc83ffc07ffc0fffc1ffe8077407ff00fff41ffdc061e87ffe0fffe01c803fff0fff901246040343ffd80ae01fff61ffe806a380eb20fff41fff83fff87ff10ffe81ffe4484d0fffa01be6239f83fff87ff40fff61fffc3ffe87ff1009341ffec0384888d94ffec02b3c3ff807ff31ffec3ffd03ff80fff91ffe03fffc3ffb07ffc0fff01ffd87ffa07ff60ffee1ffd43ffa07ff70ffe81ffe4403e8fffb0ffe21fff03fff07ff61ffea1fff07ffa3fff2025001ffd87ff88fff10fff01fffc3ffb87ff30fff81ffcc7ff887ff7022283fff07ffc8fff20ffea1ffc43ffc87ffe0ffe201ff87ffb87ffc0ffe81fff47ffd8031b0ffe01ffc03ffb87ffe01c38204143ffd87ff20ffee24490455c07ff20ffe01fff87ffe87ff00fffe1ffd83ff887ff01ffe81ffc9bffe009350fff81ffc47ff807ff30fff4231003ffc87ff601f6c1ffc07ffe003c00ffe21ffe43ffa0fff20fffa3ffd03fff808a00ffe01ffc47fff87ff00ffec3ffc03ff9008b92fff41ffc07fff8fff61ffee1ffc03ffc0fffe0ffe61ffcc7ff807ffa0fff01fffc7ffa07ffe0fffe1ffc03ffc00dee01566027003ffc87ff10ffe01fffc7ffe07ff91ffe01ffc03ffd87ffa0ffe83ffc83ffd0fffa0fff41ffe83fff0fffa0fff41ffd43fff87ffb0ffee3ffec3ffe97ff56fffa1ffe03ffc07ffe0fff23ffec7ffe07ffc0fff81ffe47fff00c950ffe81ffe87ffd87ff10fff420134470e085bc0ffe61ffe83ffe87ffb0fff01ffcdbffd87ff20fffa1ffcc7ffd0fff301a48020703ffd87ff90fffa1ffe03ffc08bd40ffea1ffec3ffa07ffe0ffe81ffcc45a2006381ffe21ffe0bff88fff61fffa017c83ff8800130ffe01ffe87ff807ff21fff822ddc7fff8fff00ffe01ffc03ff9885390ffe6231c03ffb87ff6115201ffd87ff807ffa0fff61ffc03ffc87ffd0fff61ffe43ff807ff00ffe01ffe43ff887ff6123301ffcc3ffa0fff81ffe55ffcc0069001451fff01fff03ffa081f6107061ffc0083807ff91ff else 0x587ff60fffe1ffd408348fff80fff61ffe07ff807ff00ffe01ffc83ff807ff70ffe61ffd83ffd87ff400dc81ffe43ff80029f0fff43ffd43ffc8fff00fff81ffd03ff807ffa1fffc1ffe83ffda7ff60ffe03ffc03ff807ff201d4e04058019187ff00ffe01ffcc3ff807fff8ffe01ffcc3ffe8805800ce23ffec7ffb000800fffc1ffd004f607ff81ffe21fff43ffe07ff50ffe41ffdc3fff07fff0ffe21ffdc3ff907ffb0ffe01ffe83ffb87ffb0fff41ffd407af07ff00fffa3ffdc3ff8010cd00da01fff00308002ae6fffe3ffd03ffc8006d1056a004183ff807ff31fff21ffd5bffa87fff01b481fff47ffe87ff80fffe3ffc47ff987ff20ffe01ffc83ffc00a18024f23ffc23fff0fff80fff03fff03ffe08eb301f5a3ffcc3fff07ff00ffe41ffc83ffe87ff00ffe23ffc43ff807ff101f301ffcebff807ff10ffe61ffd800b807ff00fffe1ffcc3ff807ffb1fffa1fff8012d81267016e01ffdc7ffc07fff0ffec1ffc03fff8021c0fff83ffd83ffa17ff610be41ffc03ffe802650ffe01ffd8051007fff0fff43fff83ffb87ffc0fff01ffce3ffc07ff70fffe1fffc3ffc07ffc00c4c1ffe43ffc07fff1ffee1fff805278fff40fff401a003ffc87ff00ffe0220d43ff807ff10fff41ffdc7ffb87ffe0ffee1ffc87ff9001e0affe4205307ffc8fffa125e01ffc03ff807ff00fffe021003ffd001aa1ffe21ffe47ffa87ff00fff83ffe83ffb87ff0100023ffc83ff907ffc0ffe01ffc03ffc07ff00ffe01ffc03ffc081321ffee3fff8015b0fff5125581fff0405007ff6015501ffc07ffe87ff9025783ffc03ffe07ffb0ffe01ffe03ff807ff10ffe43ffc03ff807ff00fffc1ffe03ff9810900fff41ffc4014207ffb005fe1ffe07ffc07ff510d003ffc03ffd87fff0ffe01fff83ffa87ff00fff21ffe8069807ff06fffe04650029a07ff21ffe01f)))
def hashz3l13 (i : Nat) : Nat := (if i<1 then 0x1ff9803807ff83ff00ffe805403fe01ff00ff807ff03fee1ff00ffc87fe4443c1ff0001c0fff13fee1ff80ffe87fe03fe25ffd0ff807fe47fe21fff0ffb87ff43ff41ff21ffe87fcc3fe43ff90ffe87fe87fe61ff81ffd07fdc3ff401de008007ff47ffa1ff20ffbbffd83fea1ff0017807fc03ff03ff10ff90ffe003721ff30ff917fe43fec1ffe1ffd006a43fec1ff40ffb07ff23ff80062015907ff43fe43ff50ffe87fd03fe41ff80fff0ffe43fec1ff51ffa87fc87ffc22dd0ffe87fdc3ffa1ff100b70ffcc7fe03ff60ffa0ffd87ff41ffc1ff880780460800781fff07fc03ffe0020000807ffc7ffa02e61ffe008803ff83fff6ff807fcc3fe01ff10ffe07fc03fec22c81ff887fc03ff41ffe0fff87fd43ffc01210ffa07fd8405c3ff801450ffd87ff03fff0ff987ff07ff21ff61ffd07ff03fee1fff1fff07fe87fe01ff00ff807fd43fe01ff00ffc87fcc3fe01ffd0ffb07fd03fe81ff00ff8086747ff41fff00e107fc801101ffa0ffa88a483ff21ffa1fff008e43fe03ff50ffa0ffc43fe01ffe0ffc87ff8048a1ff60ffe87ff83fec3ff610e007fe83ff01ff70ffb885ac3ff41ffc10f607ff47ff41ffb0ffe8ffe47ffa1ffd0ff8009587fe21ff0110007fc03ff61ff81ffb808783fea3ff00ffa87fc40402fffe1ff80ffc03ff61ffd0ffd07fec3ff41ffe8ffa005e83fee1ff010be083d43ff61ffe1ffc804c03fe420830ffa0ffdc3fe83ff40fff08ab87ff41fff103487fe87fe01ffe0ff807fc43fea1ffe0ffd07fc03fee1ff20ff907fd03fe41ff71ffb0fffc3fea225e1ffb0ffd83fec1ff80fff2ffc83ffe3ffa0ffa87ff43fe03ff20ff9002803ff01ff51ffc8026842401ffb1ff887fe403341ff10ffd07ff4413e227f0ffd0fff87ffa1ff91ffd07ffc7fe43ffd0ff807fe07fe01ffe0ffc07fd43fec02a00ff807ff03fe61ff80fff806003fea1ff80ff887fd57ffc1ff91ff987fc83fe21ff51ffa47fd03fe4000c117a0ffc83ff41ffd1ffb08a287ff01ffc0ffc08324bfee1ff7013797fdc3ff0dffe0ffb0ffe47fee3ff5bffd003083fe01ff01ff987ffc3ff05ffa1fff07ff47fec3ff61ffe37fc43ffa3ff1100907ff03ff61fff0ffe805143fec21450ffa87ffc02221ff00ffd07ff07fee20e70fff87fe403ea1ffd0ff80ffcc3ff61ff07060c0533002102040e032a00040121020205010511003a01020000005b2908000001100933040002000100121214422100010e0000001e09020a090d0806090305000c0016000015022f0005000000050606052b25000d011c100a001c110345023e0f07000a0200092501063c370000000007300a0e0606000113030003031d0102000a371b190000133006103b0303280115093a100e00000209000002000214000000000a050a011044d32a00000400010a070000 else 0x802980ff900b403fea203f0ffb87fec3ff01ff10ff887ff87fe21ffe0ffd47fd804e43ffd1ffd8ffec01ea1ffc0ff80ffc07fe21ffa0ffa07fd83fe03ff7108587ff83fea1ff5002487fdc3ff01ff50ffb0ffd800aa1ff10ffb87ffc3fea1ff7018707fec42235ffd0ffc87fcc3ff61ffc0ffd0fffc3fe03ff80ffd881c43ff63ff601658ffdc3fe23ff7006e8ffc43fe23ffd0ff807ffc3fe01ff00ffb0ffc83fee1ff00ffa0ffc03ff61ff7005807ff03fe21ff30ff907fc03fe01fff0ff987fc03fea1ff60ffa0ffd83fea3ffc)
def z3levels : Nat → Packing
  | 9 => z3l9
  | 10 => z3l10
  | 11 => z3l11
  | 12 => z3l12
  | 13 => z3l13
  | _ => emptyPacking
def z3index : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 21 66 5 14 6 4 (hashz3l10)
  | 11 => lookupWord 462 1537 8 18 10 4 (hashz3l11)
  | 12 => lookupWord 545 2213 8 19 11 4 (hashz3l12)
  | 13 => lookupWord 183 493 8 17 9 4 (hashz3l13)
  | _ => fun _ => none
def z3 : Forest := (1023,13,fun j => gzsamples[j]?.getD (0,0),gzcolumns,gzautos,z3levels,z3index)
def hintZ3at9 (i : Nat) : Nat := if 8 ≤ i then 0 else (0x194c0452019058601511018044334130500d8a4c2092034130500d34130500d000000000 >>> (36*(i % 64))) &&& 68719476735
def hintZ3at10 (i : Nat) : Nat := if 247 ≤ i then 0 else ((if i/64<2 then (if i/64<1 then 0x100c02210000000000000000000000000000000000000000000000000000000502c13090542a05030000000001128904831108440a04522d13890000000000100c02210100c022104c2603210000000000000000001128904830100c022100000000000000000009068140b0502c1309152a9148b0502c12290000000000502c13090000000000100c022104c2603210a0540a0d0283413090283412290000000000000000000100c02210a0540a0d0000000000000000000000000000a0540a0d0000000000000000000502c13090000000000100c02210502c120d0502c120d048340a250502c120d249348b45048340a250502c120d0502c120d0502c120d120180403820180403884460309000000000c82450285000000000000000000 else 0x2a14483410a0540a0d000000000000000000000000000000000000000000000000000000184c2211108044022109068140b0a0540a0d1a4d229110a04402210000000000000000000000000000000000000000000000000000000000000001a4d229150000000000000000000000000001a4d229110a0540a2520d0603210a0540a0d0283413090a0540a0d0283412290a0540a070000000001a4d229110a04402210000000000a04402030a04402030a04402036030904a20542a05220a044020304c260303452a854230a044020302834120b1148a050a4926914aa0a0540a078804402038a44603030a044020302834120b000000000000000000000000000020180403000000000000000000000000000000000000112890483000000000) else (if i/64<3 then 0x24128140324128140322d160b07824904826048340a070000000000000000000905828110000000000000000000000000000000000000000000000a04402210000000000000000000000000000906814030000000000502c1309000000000151a8d0610000000000500c022104c260321151a8d06100000000000000000000000000009148a0510a0540a0d442a051280283412292293492690000000000000000001a4d229150000000008a4560b450000000000a0540a250000000002a14483418a44603410000000000a0540a0d02834130982d148a4d0000000000000000000000000000000000000542a05031a4c221110000000000a0540a0d000000000000000000000000000000000000184c221110a0540a0d0000000000a0540a25 else 0x341b0c825341a4120d11098482c0000000000000000000000000000000000000502c13091408440a00000000000000000000000000000000000000000000000000000000000000000000000000502c120d0000000000000000000000000000502c13090502c1309000000000152a9148b1408440a04522d13890000000000000000000000000000000000000000000000000000000502c120d249348b450502c120d140a4120b000000000000000000152a9148b000000000000000000140a4120d000000000000000000140a4120b000000000140a4130904c26030360f070383140840203140a4120b140a4020304c260303)) >>> (36*(i % 64))) &&& 68719476735
def hintZ3at11 (i : Nat) : Nat := if 311 ≤ i then 0 else ((if i/64<2 then (if i/64<1 then 0x0 else 0xa04402030a04402030a04402030a04402030a04402030a0440203000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if i/64<3 then 0xa04402210000000000000000000000000000000000002a14483410000000000000000008a44603410000000000000000000a0540a0d0a0540a0d0a0540a0d0a0540a0d0a0540a0d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a4d229110000000000a04402210000000000a0540a0d0000000000000000000000000000000000000000000000a04402210000000000a0540a0d0000000000000000000000000000000000000000000000000000002a14483410000000000000000000a0540a0d0000000000000000000000000000000000000000000000000000000000000001a4d229110000000000a0440221000000000000000000000000000 else (if i/64<4 then 0x140a413090000000000000000001408402031408402031408402031408402032412814031408402031408402032412814030000000000000000000000000000000000000000000000000000000000000000000000001a4d229110000000008a44603410000000000000000000000000000000000000000000000000000000a04402210a04402210000000000000000001a4d229110000000008a44603410000000000a04402210000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0440221000000000 else 0x2a0540a0d000000000000000000000000000000000000280440221682450285000000000000000000000000000000000000151a8d0610000000000000000000000000000000000000000000000502c120d0502c120d0000000000000000000000000000502c1309000000000152a914830000000000000000000502c120d000000000000000000000000000000000000152a91483000000000140a4120d000000000000000000000000000140a413090000000000000000000000000000000000000000000000000000000502c120d000000000000000000))) >>> (36*(i % 64))) &&& 68719476735
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem geomZ3 : graphValid z3 (boundsBefore knownn487) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z3block9_0 : goodRange z3 9 0 8 := by
  apply piecesGood (hint:=hintZ3at9) (ar:=9) (d:=1)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allZ3at9 : goodRange z3 9 0 8 := z3block9_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z3block10_0 : goodRange z3 10 0 2 := by
  apply goodPlain
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z3block10_2 : goodRange z3 10 2 32 := by
  apply piecesGood (hint:=hintZ3at10) (ar:=10) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z3block10_34 : goodRange z3 10 34 32 := by
  apply piecesGood (hint:=hintZ3at10) (ar:=10) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z3block10_66 : goodRange z3 10 66 32 := by
  apply piecesGood (hint:=hintZ3at10) (ar:=10) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z3block10_98 : goodRange z3 10 98 32 := by
  apply piecesGood (hint:=hintZ3at10) (ar:=10) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z3block10_130 : goodRange z3 10 130 32 := by
  apply piecesGood (hint:=hintZ3at10) (ar:=10) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z3block10_162 : goodRange z3 10 162 32 := by
  apply piecesGood (hint:=hintZ3at10) (ar:=10) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z3block10_194 : goodRange z3 10 194 32 := by
  apply piecesGood (hint:=hintZ3at10) (ar:=10) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z3block10_226 : goodRange z3 10 226 21 := by
  apply piecesGood (hint:=hintZ3at10) (ar:=10) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allZ3at10 : goodRange z3 10 0 247 := (@goodJoin z3 10 0 226 21 (@goodJoin z3 10 0 194 32 (@goodJoin z3 10 0 162 32 (@goodJoin z3 10 0 130 32 (@goodJoin z3 10 0 98 32 (@goodJoin z3 10 0 66 32 (@goodJoin z3 10 0 34 32 (@goodJoin z3 10 0 2 32 z3block10_0 z3block10_2) z3block10_34) z3block10_66) z3block10_98) z3block10_130) z3block10_162) z3block10_194) z3block10_226)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z3block11_0 : goodRange z3 11 0 32 := by
  apply goodPlain
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z3block11_32 : goodRange z3 11 32 32 := by
  apply goodPlain
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z3block11_64 : goodRange z3 11 64 24 := by
  apply goodPlain
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z3block11_88 : goodRange z3 11 88 32 := by
  apply piecesGood (hint:=hintZ3at11) (ar:=11) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z3block11_120 : goodRange z3 11 120 32 := by
  apply piecesGood (hint:=hintZ3at11) (ar:=11) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z3block11_152 : goodRange z3 11 152 32 := by
  apply piecesGood (hint:=hintZ3at11) (ar:=11) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z3block11_184 : goodRange z3 11 184 32 := by
  apply piecesGood (hint:=hintZ3at11) (ar:=11) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z3block11_216 : goodRange z3 11 216 32 := by
  apply piecesGood (hint:=hintZ3at11) (ar:=11) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z3block11_248 : goodRange z3 11 248 32 := by
  apply piecesGood (hint:=hintZ3at11) (ar:=11) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z3block11_280 : goodRange z3 11 280 31 := by
  apply piecesGood (hint:=hintZ3at11) (ar:=11) (d:=3)
  simp only [pieces,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allZ3at11 : goodRange z3 11 0 311 := (@goodJoin z3 11 0 280 31 (@goodJoin z3 11 0 248 32 (@goodJoin z3 11 0 216 32 (@goodJoin z3 11 0 184 32 (@goodJoin z3 11 0 152 32 (@goodJoin z3 11 0 120 32 (@goodJoin z3 11 0 88 32 (@goodJoin z3 11 0 64 24 (@goodJoin z3 11 0 32 32 z3block11_0 z3block11_32) z3block11_64) z3block11_88) z3block11_120) z3block11_152) z3block11_184) z3block11_216) z3block11_248) z3block11_280)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z3block12_0 : goodRange z3 12 0 24 := by
  apply goodPlain
  apply cellsBlock (ar:=10) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z3block12_24 : goodRange z3 12 24 25 := by
  apply goodPlain
  apply cellsBlock (ar:=11) (rows:=1) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allZ3at12 : goodRange z3 12 0 49 := (@goodJoin z3 12 0 24 25 z3block12_0 z3block12_24)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z3block13_0 : goodRange z3 13 0 3 := by
  apply goodPlain
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allZ3at13 : goodRange z3 13 0 3 := z3block13_0
theorem tablesZ3 : checkedTables z3 13 := by
  intro k hk
  interval_cases k
  · exact goodPlain (rfl : block z3 0 0 0=true)
  · exact goodPlain (rfl : block z3 1 0 0=true)
  · exact goodPlain (rfl : block z3 2 0 0=true)
  · exact goodPlain (rfl : block z3 3 0 0=true)
  · exact goodPlain (rfl : block z3 4 0 0=true)
  · exact goodPlain (rfl : block z3 5 0 0=true)
  · exact goodPlain (rfl : block z3 6 0 0=true)
  · exact goodPlain (rfl : block z3 7 0 0=true)
  · exact goodPlain (rfl : block z3 8 0 0=true)
  · exact allZ3at9
  · exact allZ3at10
  · exact allZ3at11
  · exact allZ3at12
  · exact allZ3at13
def mate (b : Fin 3) : Fin 9 := [2,3,6].getD b.val 2
def xzero := inputs.getD 0 zero
def rawTail := inputs.tail
def portWord (b : Fin 3) := bin true xzero (inputs.getD (mate b).val zero)
def physical (b : Fin 3) := inputs ++ [seed,portWord b]
def forms3 (b : Fin 3) (t : Nat) :=
  (if t.testBit 2 then [portWord b] else []) ++ (if t.testBit 0 then inputs else rawTail) ++
    (if t.testBit 1 then [seed] else [])
def witness3 (b : Fin 3) (j : Fin 9) : Nat :=
  ([[20,1,9,4,1,1,2,4,8],[10,1,2,5,1,1,2,4,8],[80,1,2,4,1,1,257,4,8]] :
    List (List Nat)).getD b.val [] |>.getD j.val 0
def lowRow3 (b : Fin 3) (j : Fin 9) : Row := Fin.ofNat 512 (witness3 b j)
def highRow3 (b : Fin 3) (j : Fin 9) : Row := Fin.ofNat 512 ((witness3 b j) ||| (1 <<< j.val))
theorem witness3_ok : ∀ (b : Fin 3) (j : Fin 9),
    ((bit (lowRow3 b j) graph != bit (highRow3 b j) graph) &&
    (physical b).all (fun a => a==inputs.getD j.val zero || (j==0 && a==seed) ||
      bit (lowRow3 b j) a == bit (highRow3 b j) a))=true := by decide +kernel
theorem tail_present3 {b k t S} (h:Live graph k t S) (sub:∀v∈S,v∈physical b) :
    ∀ v ∈ rawTail, v ∈ S := by
  intro v hv
  have listTail : List.ofFn (fun i:Fin 8 => inputs.getD (i.val+1) zero)=rawTail:=rfl
  rw [←listTail,List.mem_ofFn] at hv
  obtain ⟨j,rfl⟩:=hv
  let i : Fin 9 := ⟨j.val+1,by omega⟩
  have hi : i≠0:=by intro h; have hh:=congrArg Fin.val h; change j.val+1=0 at hh; omega
  have a:=witness3_ok b i
  simp only [Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at a
  apply raw_required h (physical b) (inputs.getD i.val zero) sub _ _ a.1
  intro v hv hne
  rcases a.2 v hv with (e|⟨e,_⟩)|e
  · exact (hne e).elim
  · exact (hi e).elim
  · exact e
theorem polarity3 {b k t S} (h:Live graph k t S) (sub:∀v∈S,v∈physical b) :
    xzero ∈ S ∨ seed ∈ S := by
  have a:=witness3_ok b 0
  simp only [Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at a
  obtain ⟨v,hv,hd⟩:=live_row_difference h a.1
  rcases a.2 v (sub v hv) with (e|⟨_,e⟩)|e
  · exact Or.inl (show inputs.getD (0:Fin 9).val zero∈S from e ▸ hv)
  · exact Or.inr (e ▸ hv)
  · contradiction
theorem forms3_complete {b k t S} (run:Live graph k t S) (sub:∀v∈S,v∈physical b) :
    ∃ t ∈ ([1,2,3,5,6,7]:List Nat), S=(forms3 b t).toFinset := by
  classical
  have tail:=tail_present3 run sub
  have polarity:=polarity3 run sub
  have ls : inputs=xzero::rawTail:=rfl
  have cover : ∀v∈S,v=xzero ∨ v∈rawTail ∨ v=seed ∨ v=portWord b:=by
    intro v hv
    have a:=sub v hv
    simpa only [physical,ls,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] using a
  have either : S=((if portWord b∈S then [portWord b] else []) ++
      (if xzero∈S then [xzero] else []) ++ rawTail ++ (if seed∈S then [seed] else [])).toFinset := by
    ext v
    by_cases hp : portWord b∈S <;> by_cases hx : xzero∈S <;> by_cases hn : seed∈S <;>
      simp only [List.mem_toFinset,hp,hx,hn,ite_true,ite_false,List.mem_append,List.mem_singleton,
        List.not_mem_nil,false_or,or_false] <;> grind
  by_cases hp : portWord b∈S <;> by_cases hx : xzero∈S <;> by_cases hn : seed∈S
  all_goals try exact False.elim (polarity.elim hx hn)
  all_goals simp only [hp,hx,hn,ite_true,ite_false,List.nil_append,List.append_nil,List.singleton_append] at either
  · exact ⟨7,by decide,either⟩
  · exact ⟨5,by decide,either⟩
  · exact ⟨6,by decide,either⟩
  · exact ⟨3,by decide,either⟩
  · exact ⟨1,by decide,either⟩
  · exact ⟨2,by decide,either⟩
set_option maxRecDepth 16384 in
theorem cutForm3 {prior} (lower:∀ q,Lower (vars q) (graphGoal q) (prior q))
    (geometry:graphValid dead prior=true) (ci:ColumnInfo)
    (member:ci∈IndexTree.values dead.cols) (ws:List Sig)
    (nd:ws.Nodup) (check:poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 13 0 (vars 511) ws=true) :
    Impossible graph 13 ws.toFinset:=by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  have ok:=geometry.1.2 ci member
  have sl:=col_sound ci prior lower ok
  have e:chartGoal 511=graph:=by decide +kernel
  exact e ▸ poolCut_sound sl ([]:List Choice) rfl nd check
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem fixedRows3 {pd pz}
    (ld:∀ q,Lower (vars q) (graphGoal q) (pd q))
    (gd:graphValid dead pd=true) (td:checkedTables dead 14)
    (lz:∀ q,Lower (vars q) (graphGoal q) (pz q))
    (gz:graphValid z3 pz=true) (tz:checkedTables z3 13)
    (b:Fin 3) (t:Nat) (ht:t∈([1,2,3,5,6,7]:List Nat)) : Impossible graph 13 (forms3 b t).toFinset:=by
  have zt:targetOf z3=graph:=by decide +kernel
  have dt:targetOf dead=graph:=by decide +kernel
  fin_cases b <;> rcases List.mem_cons.mp ht with rfl|ht
  all_goals try rcases List.mem_cons.mp ht with rfl|ht
  all_goals try rcases List.mem_cons.mp ht with rfl|ht
  all_goals try rcases List.mem_cons.mp ht with rfl|ht
  all_goals try rcases List.mem_cons.mp ht with rfl|ht
  all_goals try rcases List.mem_singleton.mp ht with rfl
  · exact cutForm3 ld gd (16,0,495,0,13) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact dt ▸ root_index (g:=dead) ld gd td (k:=13) (by decide) (i:=0) (by decide +kernel)
  · exact cutForm3 ld gd (1,0,510,0,12) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact dt ▸ root_index (g:=dead) ld gd td (k:=13) (by decide) (i:=2) (by decide +kernel)
  · exact zt ▸ root_index (g:=z3) lz gz tz (k:=13) (by decide) (i:=0) (by decide +kernel)
  · exact cutForm3 ld gd (1,0,510,0,12) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact cutForm3 ld gd (16,0,495,0,13) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact dt ▸ root_index (g:=dead) ld gd td (k:=13) (by decide) (i:=0) (by decide +kernel)
  · exact cutForm3 ld gd (1,0,510,0,12) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact dt ▸ root_index (g:=dead) ld gd td (k:=13) (by decide) (i:=3) (by decide +kernel)
  · exact zt ▸ root_index (g:=z3) lz gz tz (k:=13) (by decide) (i:=1) (by decide +kernel)
  · exact cutForm3 ld gd (1,0,510,0,12) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact cutForm3 ld gd (16,0,495,0,13) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact dt ▸ root_index (g:=dead) ld gd td (k:=13) (by decide) (i:=0) (by decide +kernel)
  · exact cutForm3 ld gd (1,0,510,0,12) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact cutForm3 ld gd (64,0,447,0,13) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
  · exact zt ▸ root_index (g:=z3) lz gz tz (k:=13) (by decide) (i:=2) (by decide +kernel)
  · exact cutForm3 ld gd (1,0,510,0,12) (by decide +kernel) _ (by decide +kernel) (by decide +kernel)
open PEqualNP.CircuitLowerBounds
theorem port3exact (b:Fin 3) (C:Circuit) (fan:PEqualNP.MetaComplexity.FanInTwo C) (cap:C.size≤13)
    (exclude:∀ t∈([1,2,3,5,6,7]:List Nat),Impossible graph 13 (forms3 b t).toFinset) :
    ∃x:Fin 9→Bool,C.eval ((List.ofFn x++[!x 0])++[x 0 || x (mate b)])≠edge x:=by
  by_contra! agree
  have goalEq:(execute C.gates (physical b)).getD C.output zero=graph:=by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r:Row:=⟨j,hj⟩
    change bit r ((execute C.gates (physical b)).getD C.output zero)=bit r graph
    rw [←b_read,execute_bits _ _ _ (fun g hg=>(fan g hg).1),edge_table]
    have fed : (physical b).map (bit r)=(List.ofFn (sample r)++[!sample r 0])++
        [sample r 0 || sample r (mate b)]:=by
      simp only [physical,List.map_append,List.map_cons,List.map_nil,sampled,seed_table,portWord,bit_bin]
      rfl
    rw [fed]
    exact agree (sample r)
  have outside:=get_rep (execute C.gates (physical b)) C.output
  rw [goalEq] at outside
  obtain ⟨k,t,S,small,run,sub⟩:=extract C.gates (physical b) fan graph_proper (outside.resolve_right (fun h=>h graph_proper))
  obtain ⟨u,hu,e⟩:=forms3_complete run sub
  exact exclude u hu k t (small.trans cap) (e ▸ run)
theorem physical3 (cost:∀b t,t∈([1,2,3,5,6,7]:List Nat)→Impossible graph 13 (forms3 b t).toFinset) : ∀ (x1 : List ℕ),   x1 = [(0 : ℕ), (2 : ℕ)] ∨ x1 = [(0 : ℕ), (3 : ℕ)] ∨ x1 = [(0 : ℕ), (6 : ℕ)] →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro ports legal C fan cap
  obtain ⟨b,hb⟩ : ∃ b : Fin 3,ports=[0,(mate b).val] := by
    rcases legal with h|h|h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
  obtain ⟨x,hx⟩:=port3exact b C fan cap (cost b)
  refine ⟨x,?_⟩
  let xs : List Bool:=List.ofFn x++[!x 0]
  have read (i:Fin 9) : xs.getD i.val false=x i:=by fin_cases i <;> rfl
  have eq : PEqualNP.CircuitLowerBounds.GateOp.or.eval (ports.map (fun i=>xs.getD i false))=(x 0 || x (mate b)):=by
    rw [hb]
    change (xs.getD (0:Fin 9).val false || (xs.getD (mate b).val false || false))=_
    rw [read,read,Bool.or_false]
  change C.eval (xs++[PEqualNP.CircuitLowerBounds.GateOp.or.eval (ports.map (fun i=>xs.getD i false))])≠_
  rw [eq]
  exact hx
end PEqualNP.Outside.L_meta_3863
theorem PEqualNP.Outside.L_meta_3863 :
∀ (x1 : List ℕ),   x1 = [(0 : ℕ), (2 : ℕ)] ∨ x1 = [(0 : ℕ), (3 : ℕ)] ∨ x1 = [(0 : ℕ), (6 : ℕ)] →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) :=
  PEqualNP.Outside.L_meta_3863.physical3 (PEqualNP.Outside.L_meta_3863.fixedRows3 (PEqualNP.Outside.L_meta_3863.before_sound PEqualNP.Outside.L_meta_3863.known383 PEqualNP.Outside.L_meta_3863.valid383) PEqualNP.Outside.L_meta_3863.geomdead PEqualNP.Outside.L_meta_3863.tablesdead (PEqualNP.Outside.L_meta_3863.before_sound PEqualNP.Outside.L_meta_3863.knownn487 PEqualNP.Outside.L_meta_3863.validn487) PEqualNP.Outside.L_meta_3863.geomZ3 PEqualNP.Outside.L_meta_3863.tablesZ3)
