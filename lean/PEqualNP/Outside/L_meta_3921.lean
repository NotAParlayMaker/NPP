import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3921
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

def Live (target : Sig) : Nat → Nat → Finset Sig → Prop := fun k t S =>
  ∀ (M : (Nat → Nat → Finset Sig → Prop)), (proper target → M 0 0 {target}) →
  (∀ {k t : Nat} {U : Finset Sig} {a : Sig}, proper a → neg a ∉ insert a U → M k t (insert (neg a) U) → M (k+1) (t+1) (insert a U)) →
  (∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}, proper a → proper b → a ≠ b → bin d a b ∉ insert a (insert b U) → M k t (insert (bin d a b) U) → M (k+1) t (insert a (insert b U))) →
  M k t S
theorem Live.stop {target : Sig}  (h0 : proper target) : Live target 0 0 {target} := fun M stop unary binary => @stop  h0
theorem Live.unary {target : Sig} {k t : Nat} {U : Finset Sig} {a : Sig} (h0 : proper a) (h1 : neg a ∉ insert a U) (h2 : Live target k t (insert (neg a) U)) : Live target (k+1) (t+1) (insert a U) := fun M stop unary binary => @unary k t U a h0 h1 (h2 M stop unary binary)
theorem Live.binary {target : Sig} {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (h0 : proper a) (h1 : proper b) (h2 : a ≠ b) (h3 : bin d a b ∉ insert a (insert b U)) (h4 : Live target k t (insert (bin d a b) U)) : Live target (k+1) t (insert a (insert b U)) := fun M stop unary binary => @binary k t U a b d h0 h1 h2 h3 (h4 M stop unary binary)
theorem Live.induct {target : Sig} {M : (Nat → Nat → Finset Sig → Prop)} {k t S} (h : Live target k t S)
  (stop : proper target → M 0 0 {target})
  (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig}, proper a → neg a ∉ insert a U → Live target k t (insert (neg a) U) → M k t (insert (neg a) U) → M (k+1) (t+1) (insert a U))
  (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}, proper a → proper b → a ≠ b → bin d a b ∉ insert a (insert b U) → Live target k t (insert (bin d a b) U) → M k t (insert (bin d a b) U) → M (k+1) t (insert a (insert b U))) : M k t S :=
  (h (fun k t S => Live target k t S ∧ M k t S)
  (fun h0 => ⟨@Live.stop target  h0,@stop  h0⟩)
  (@fun k t U a h0 h1 h2 => ⟨@Live.unary target k t U a h0 h1 h2.1,@unary k t U a h0 h1 h2.1 h2.2⟩)
  (@fun k t U a b d h0 h1 h2 h3 h4 => ⟨@Live.binary target k t U a b d h0 h1 h2 h3 h4.1,@binary k t U a b d h0 h1 h2 h3 h4.1 h4.2⟩)).2
theorem Live.recurse {target : Sig} {M : ∀ (k t : Nat) (S : Finset Sig) (proof : Live target k t S), Prop}
  (stop : ∀ (h0 : proper target), M 0 0 {target} (@Live.stop target  h0))
  (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (h0 : proper a) (h1 : neg a ∉ insert a U) (h2 : Live target k t (insert (neg a) U)) (ih : M k t (insert (neg a) U) h2), M (k+1) (t+1) (insert a U) (@Live.unary target k t U a h0 h1 h2))
  (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (h0 : proper a) (h1 : proper b) (h2 : a ≠ b) (h3 : bin d a b ∉ insert a (insert b U)) (h4 : Live target k t (insert (bin d a b) U)) (ih : M k t (insert (bin d a b) U) h4), M (k+1) t (insert a (insert b U)) (@Live.binary target k t U a b d h0 h1 h2 h3 h4))
  {k t S} (h : Live target k t S) : M k t S h := by
  have r := Live.induct (M := fun k t S => ∀ hh : Live target k t S, M k t S hh) h
    (fun h0 _ => @stop  h0)
    (@fun k t U a h0 h1 h2 h3 _ => @unary k t U a h0 h1 h2 (h3 h2))
    (@fun k t U a b d h0 h1 h2 h3 h4 h5 _ => @binary k t U a b d h0 h1 h2 h3 h4 (h5 h4))
  exact r h



theorem Live.zeroSet {T t S} (h : Live T 0 t S) : S = {T} := by
  have hh := h (fun k _ W => k = 0 → W = {T}) (fun _ _ => rfl)
    (@fun _ _ _ _ _ _ _ e => by omega)
    (@fun _ _ _ _ _ _ _ _ _ _ _ e => by omega)
  exact hh rfl

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h using Live.recurse with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using Live.recurse with
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

def Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop := fun p bank =>
  ∀ (M : (Nat → List (Wire R) → Prop)), (M 0 roots) →
  (∀ {p : Nat} {bank : List (Wire R)} {a : Wire R}, M p bank → Available bank a → M (p+1) (inv a :: bank)) →
  (∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool), M p bank → Available bank a → Available bank b → M (p+1) (combine op a b :: bank)) →
  M p bank
theorem Reach.start {R} {roots : List (Wire R)}   : Reach roots 0 roots := fun M start one two => @start 
theorem Reach.one {R} {roots : List (Wire R)} {p : Nat} {bank : List (Wire R)} {a : Wire R} (h0 : Reach roots p bank) (h1 : Available bank a) : Reach roots (p+1) (inv a :: bank) := fun M start one two => @one p bank a (h0 M start one two) h1
theorem Reach.two {R} {roots : List (Wire R)} {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (h0 : Reach roots p bank) (h1 : Available bank a) (h2 : Available bank b) : Reach roots (p+1) (combine op a b :: bank) := fun M start one two => @two p bank a b op (h0 M start one two) h1 h2
theorem Reach.induct {R} {roots : List (Wire R)} {M : (Nat → List (Wire R) → Prop)} {p bank} (h : Reach roots p bank)
  (start : M 0 roots)
  (one : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R}, Reach roots p bank → M p bank → Available bank a → M (p+1) (inv a :: bank))
  (two : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool), Reach roots p bank → M p bank → Available bank a → Available bank b → M (p+1) (combine op a b :: bank)) : M p bank :=
  (h (fun p bank => Reach roots p bank ∧ M p bank)
  (⟨@Reach.start R roots  ,@start  ⟩)
  (@fun p bank a h0 h1 => ⟨@Reach.one R roots p bank a h0.1 h1,@one p bank a h0.1 h0.2 h1⟩)
  (@fun p bank a b op h0 h1 h2 => ⟨@Reach.two R roots p bank a b op h0.1 h1 h2,@two p bank a b op h0.1 h0.2 h1 h2⟩)).2
theorem Reach.recurse {R} {roots : List (Wire R)} {M : ∀ (p : Nat) (bank : List (Wire R)) (proof : Reach roots p bank), Prop}
  (start : M 0 roots (@Reach.start R roots  ))
  (one : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R} (h0 : Reach roots p bank) (ih : M p bank h0) (h2 : Available bank a), M (p+1) (inv a :: bank) (@Reach.one R roots p bank a h0 h2))
  (two : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (h0 : Reach roots p bank) (ih : M p bank h0) (h2 : Available bank a) (h3 : Available bank b), M (p+1) (combine op a b :: bank) (@Reach.two R roots p bank a b op h0 h2 h3))
  {p bank} (h : Reach roots p bank) : M p bank h := by
  have r := Reach.induct (M := fun p bank => ∀ hh : Reach roots p bank, M p bank hh) h
    (fun  _ => @start  )
    (@fun p bank a h0 h1 h2 _ => @one p bank a h0 (h1 h0) h2)
    (@fun p bank a b op h0 h1 h2 h3 _ => @two p bank a b op h0 (h1 h0) h2 h3)
  exact r h



def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop := fun s ws =>
  ∀ (M : (Nat → List (Wire R) → Prop)), (M 0 [goal]) →
  (∀ {s : Nat} {xs zs : List (Wire R)}, xs.Perm zs → M s xs → M s zs) →
  (∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool), M s (inv a :: kept save a rest) → M (s+1) (a::rest)) →
  (∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool), M s (combine op a b :: kept ka a (kept kb b rest)) → M (s+1) (a::b::rest)) →
  M s ws
theorem Run.stop {R} {goal : Wire R}   : Run goal 0 [goal] := fun M stop perm one two => @stop 
theorem Run.perm {R} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (h0 : xs.Perm zs) (h1 : Run goal s xs) : Run goal s zs := fun M stop perm one two => @perm s xs zs h0 (h1 M stop perm one two)
theorem Run.one {R} {goal : Wire R} {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (h0 : Run goal s (inv a :: kept save a rest)) : Run goal (s+1) (a::rest) := fun M stop perm one two => @one s a rest save (h0 M stop perm one two)
theorem Run.two {R} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool) (h0 : Run goal s (combine op a b :: kept ka a (kept kb b rest))) : Run goal (s+1) (a::b::rest) := fun M stop perm one two => @two s a b rest op ka kb (h0 M stop perm one two)
theorem Run.induct {R} {goal : Wire R} {M : (Nat → List (Wire R) → Prop)} {s ws} (h : Run goal s ws)
  (stop : M 0 [goal])
  (perm : ∀ {s : Nat} {xs zs : List (Wire R)}, xs.Perm zs → Run goal s xs → M s xs → M s zs)
  (one : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool), Run goal s (inv a :: kept save a rest) → M s (inv a :: kept save a rest) → M (s+1) (a::rest))
  (two : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool), Run goal s (combine op a b :: kept ka a (kept kb b rest)) → M s (combine op a b :: kept ka a (kept kb b rest)) → M (s+1) (a::b::rest)) : M s ws :=
  (h (fun s ws => Run goal s ws ∧ M s ws)
  (⟨@Run.stop R goal  ,@stop  ⟩)
  (@fun s xs zs h0 h1 => ⟨@Run.perm R goal s xs zs h0 h1.1,@perm s xs zs h0 h1.1 h1.2⟩)
  (@fun s a rest save h0 => ⟨@Run.one R goal s a rest save h0.1,@one s a rest save h0.1 h0.2⟩)
  (@fun s a b rest op ka kb h0 => ⟨@Run.two R goal s a b rest op ka kb h0.1,@two s a b rest op ka kb h0.1 h0.2⟩)).2
theorem Run.recurse {R} {goal : Wire R} {M : ∀ (s : Nat) (ws : List (Wire R)) (proof : Run goal s ws), Prop}
  (stop : M 0 [goal] (@Run.stop R goal  ))
  (perm : ∀ {s : Nat} {xs zs : List (Wire R)} (h0 : xs.Perm zs) (h1 : Run goal s xs) (ih : M s xs h1), M s zs (@Run.perm R goal s xs zs h0 h1))
  (one : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (h0 : Run goal s (inv a :: kept save a rest)) (ih : M s (inv a :: kept save a rest) h0), M (s+1) (a::rest) (@Run.one R goal s a rest save h0))
  (two : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op ka kb : Bool) (h0 : Run goal s (combine op a b :: kept ka a (kept kb b rest))) (ih : M s (combine op a b :: kept ka a (kept kb b rest)) h0), M (s+1) (a::b::rest) (@Run.two R goal s a b rest op ka kb h0))
  {s ws} (h : Run goal s ws) : M s ws h := by
  have r := Run.induct (M := fun s ws => ∀ hh : Run goal s ws, M s ws hh) h
    (fun  _ => @stop  )
    (@fun s xs zs h0 h1 h2 _ => @perm s xs zs h0 h1 (h2 h1))
    (@fun s a rest save h0 h1 _ => @one s a rest save h0 (h1 h0))
    (@fun s a b rest op ka kb h0 h1 _ => @two s a b rest op ka kb h0 (h1 h0))
  exact r h



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
  induction h using Run.recurse generalizing p bank with
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
  induction h using Run.recurse with
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
  induction h using Live.recurse generalizing v with
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
  induction h using Reach.recurse generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ih ha =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ih ha hb =>
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
  induction h using Live.recurse with
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
def oldSeed : Sig := 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888

def seed : Sig := inputs.getD 0 zero ||| inputs.getD 4 zero
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 || sample r 4) := by decide +kernel
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

def neighbor (i : Fin 9) : Nat := [4,2,1,2,0,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))

theorem seed_witness : ∀ i : Fin 9,
    (bit (absentRow i) graph != bit (presentRow i) graph) &&
    ((inputs++[seed]).all fun w => w == inputs.getD i.val zero ||
      bit (absentRow i) w == bit (presentRow i) w) = true := by decide +kernel

theorem all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[seed]) :
    S=inputs.toFinset ∨ S=(inputs++[seed]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := seed_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (absentRow i) (presentRow i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : seed ∈ S
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

theorem initial_live (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t, k ≤ 14 ∧ (Live graph k t inputs.toFinset ∨ Live graph k t (inputs++[seed]).toFinset) := by
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
    refine ⟨k,t,by omega,?_⟩
    rcases all_roots run hs with h | h
    · exact Or.inl (h ▸ run)
    · exact Or.inr (h ▸ run)


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
  induction h using Live.recurse with
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
  induction h using Live.recurse with
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
  induction h using Live.recurse with
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
def chartGoal (m : Nat) : Sig :=
  if m=1023 then graphGoal m &&& ~~~oldSeed else graphGoal m
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


abbrev BoundPool := (Sig) × (Nat) × (Nat) × (List Sig)
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
  | none => simp [he, Option.map] at h
  | some pool =>
    rw [he] at h
    change some _ = some c at h
    injection h with h
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
    rw [h.zeroSet] at he
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


def IndexTree (α : Type) := List α
def IndexTree.leaf {α} (xs : List α) : IndexTree α := xs
def IndexTree.fork {α} (_ : Nat) (a b : IndexTree α) : IndexTree α := List.append a b
def IndexTree.read {α} (tree : IndexTree α) (i : Nat) := (show List α from tree)[i]?
def IndexTree.values {α} (tree : IndexTree α) : List α := tree
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values := List.mem_of_getElem? e

def Forest := (Nat) × (Nat) × (Nat → Bits × Bits) × (IndexTree ColumnInfo) × (Array (List Nat)) × (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (c : Forest) : Nat := c.1
def Forest.cap (c : Forest) : Nat := c.2.1
def Forest.samples (c : Forest) : Nat → Bits × Bits := c.2.2.1
def Forest.cols (c : Forest) : IndexTree ColumnInfo := c.2.2.2.1
def Forest.autos (c : Forest) : Array (List Nat) := c.2.2.2.2.1
def Forest.levels (c : Forest) : Nat → Packing := c.2.2.2.2.2.1
def Forest.index (c : Forest) : Nat → Nat → Option (Nat × Nat) := c.2.2.2.2.2.2


def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  let nonedge := dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 1 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  have base := raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
      (faithful_get base 0) (faithful_get base 1)))
  · exact base _ ha

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 1) else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  by_cases e : m=1023
  · have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (1 : Fin 9)
    have h := bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 1 zero).getLsbD (asRow v i).val = (v 1).getLsbD i.val at w
    have seedEq : oldSeed = inputs.getD 0 zero &&& inputs.getD 1 zero := by decide +kernel
    simp only [chartGoal,chartSamples,e,ite_true,bit,seedEq,BitVec.getLsbD_and,
      BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
    rw [h]
  · simpa only [chartGoal,chartSamples,e,ite_false] using bit_liftGoal m v i
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
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)

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
    rw [h.zeroSet] at he
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
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits) := Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : IndexTree ColumnInfo := (.leaf [])
def g15autos : Array (List Nat) := Array.mk [[],[33,48]]
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
def g31samples : Array (Bits × Bits) := Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : IndexTree ColumnInfo := (.fork 2 (.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def g31autos : Array (List Nat) := Array.mk [[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples : Array (Bits × Bits) := Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : IndexTree ColumnInfo := (.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := Array.mk [[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := Array.mk [(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := Array.mk [[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := Array.mk [(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := Array.mk [[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := Array.mk [(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo := (.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := Array.mk [[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := Array.mk [(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := (.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat) := Array.mk [[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
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
def g189samples : Array (Bits × Bits) := Array.mk [(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : IndexTree ColumnInfo := (.fork 4 (.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def g189autos : Array (List Nat) := Array.mk [[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples : Array (Bits × Bits) := Array.mk [(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : IndexTree ColumnInfo := (.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat) := Array.mk [[],[101,66,16]]
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
def g191samples : Array (Bits × Bits) := Array.mk [(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]
def g191columns : IndexTree ColumnInfo := (.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (.fork 2 (.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (.fork 9 (.fork 4 (.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (.fork 5 (.fork 2 (.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (.fork 2 (.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def g191autos : Array (List Nat) := Array.mk [[],[84,115],[117,67,32],[116,83,32]]
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
def g251samples : Array (Bits × Bits) := Array.mk [(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : IndexTree ColumnInfo := (.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := Array.mk [[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := Array.mk [(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := (.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat) := Array.mk [[],[84,115],[117,67,32],[116,83,32]]
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
def g383samples : Array (Bits × Bits) := Array.mk [(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]
def g383columns : IndexTree ColumnInfo := (.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (.fork 3 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (.fork 7 (.fork 3 (.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (.fork 4 (.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (.fork 4 (.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (.fork 7 (.fork 3 (.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (.fork 4 (.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def g383autos : Array (List Nat) := Array.mk [[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
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
def deadsamples : Array (Bits × Bits) := Array.mk [(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadcolumns : IndexTree ColumnInfo := (.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (.fork 4 (.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (.fork 8 (.fork 4 (.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (.fork 4 (.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (.fork 4 (.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (.fork 8 (.fork 4 (.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (.fork 4 (.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (.fork 4 (.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (.fork 8 (.fork 4 (.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (.fork 4 (.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (.fork 4 (.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (.fork 8 (.fork 4 (.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (.fork 4 (.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def deadautos : Array (List Nat) := Array.mk [[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def dead : Forest := ⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
theorem geomdead : graphValid dead (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

def ImpossibleU (T : Sig) (cap tm : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → (tm = 0 → t = 0) → ¬Live T k t S

theorem imp_to_impU {T cap tm S} (h : Impossible T cap S) : ImpossibleU T cap tm S :=
  fun k t hk _ => h k t hk

theorem rotate_excludedU {T n tm} {ws : List Sig} (hi : ImpossibleU T n tm ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : ImpossibleU T n tm (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk ht h
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
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩; simpa only [inv] using hw
    · intro ha; exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk ht run

def childU (tm cap len : Nat) : Nat :=
  if len == cap || tm == 0 then 0 else 1

theorem enum_stepU {T : Sig} {cap tm : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : tm > 0 → ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      ImpossibleU T (cap-1) (childU tm cap (childOne ws a keep).length) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      ImpossibleU T (cap-1) (childU tm cap (childTwo ws a b d ka kb).length)
        (childTwo ws a b d ka kb).toFinset) :
    ImpossibleU T cap tm ws.toFinset := by
  classical
  intro k t hk ht h
  generalize he : ws.toFinset = S at h
  induction h using Live.recurse with
  | stop hp =>
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  | @unary k t U a ha hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin,er,he]; by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      refine List.nodup_cons.mpr ⟨fun h => hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h)),
        kept_nd keep a (ws.erase a) (hn.erase _) na⟩
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne,rest]
    have sc := (live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by rw [←List.toFinset_card_of_nodup nd,eq]; omega
    have htm_pos : tm > 0 := by
      by_contra h0
      have := ht (by omega); omega
    have ht' : childU tm cap (childOne ws a keep).length = 0 → t = 0 := by
      intro hcu
      unfold childU at hcu
      by_cases hlen : (childOne ws a keep).length = cap
      · rw [←List.toFinset_card_of_nodup nd,eq] at hlen; omega
      · have hne : ((childOne ws a keep).length == cap || tm == 0) = false := by
          simp [beq_eq_false_iff_ne.mpr hlen, beq_eq_false_iff_ne.mpr (by omega : tm ≠ 0)]
        rw [hne] at hcu; cases hcu
    exact oneStep htm_pos a am keep fresh hz len k t (by omega) ht' (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin, kept_fin, er, he]
      ext j
      by_cases hja : j = a
      · subst j; by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> simp [ka, kb, aa, bb, hab]
      · by_cases hjb : j = b
        · subst j; by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> simp [ka, kb, aa, bb, hja]
        · by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> simp [ka, kb, aa, bb, hja, hjb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => hn.not_mem_erase (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup :=
      List.nodup_cons.mpr ⟨fun h => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h))),
        kept_nd ka a _ nk ax⟩
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _; simp [ke]
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by rw [←List.toFinset_card_of_nodup nd,eq]; omega
    have ht' : childU tm cap (childTwo ws a b d ka kb).length = 0 → t = 0 := by
      intro hcu
      unfold childU at hcu
      by_cases hlen : (childTwo ws a b d ka kb).length = cap
      · rw [←List.toFinset_card_of_nodup nd,eq] at hlen; omega
      · by_cases htm0 : tm = 0
        · exact ht htm0
        · have hne : ((childTwo ws a b d ka kb).length == cap || tm == 0) = false := by
            simp [beq_eq_false_iff_ne.mpr hlen, beq_eq_false_iff_ne.mpr htm0]
          rw [hne] at hcu; cases hcu
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) ht' (eq.symm ▸ tail)

theorem closeChildU_sound {raw T pools links k tm rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → ImpossibleU T k tm (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    ImpossibleU T k tm (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]; exact lValid _ _ hx
  · exact imp_to_impU (scalarPoolCut_sound (pValid _ hp) nd ok)

abbrev LinkFn := Nat → List (List Sig)
abbrev NodeContextU :=
  Nat × Nat × Nat × List Decor × CovPair × List BoundPool × List QuickPool × LinkFn × LinkFn

def ctxWireU (c : NodeContextU) (i : Nat) : Decor := c.2.2.2.1.getD i defaultDecor

def evalMoveU (c : NodeContextU) (op : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let (cap,tm,n,ws,cov,pools,qpools,l0,l1) := c
  let un := op == 2
  let len := 1 + (n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len > cap then true else
    let ct := childU tm cap len
    let d := ct == 0
    if (restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1 == z.1) then true else
    if qpools.any (fun qp => fastCost qp (cap-1) a b op ka kb) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      let links := if d then l0 else l1
      closeChild pools links (cap-1) rest (movedChoice op a b)

theorem evalMoveU_sound {raw T r s ws pools l0 l1 cap tm a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op == 2) = false → a ≠ b) (hcap : 0 < cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv0 : ∀ tag xs, xs ∈ l0 tag → ImpossibleU T (cap-1) 0 (List.toFinset xs))
    (lv1 : ∀ tag xs, xs ∈ l1 tag → ImpossibleU T (cap-1) 1 (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMoveU (cap,tm,ws.length,ws,preCov ws,pools,pools.map (summarizePool ws),l0,l1)
      op a b (movedDecor op a b) ka kb = true) :
    ImpossibleU T (cap-1) (childU tm cap (moveFront ws op a b ka kb).length)
      (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm), nd.sublist (sub.map _)⟩
  have val := moved_full op a b
  have fr : ws.any (fun v => v.1 == z.1) = false := by
    apply Bool.eq_false_iff.mpr; intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh ((beq_iff_eq.mp he).symm ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk ht h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMoveU at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  let ct := childU tm cap child.length
  have ht0 : (ct == 0) = true → t = 0 := fun hct => ht (beq_iff_eq.mp hct)
  have sep := cover_sound h rfl (pair_sep pairs) (ct == 0) ht0
  let d := ct == 0
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768) = false := by
    rw [sep, bne_self_eq_false]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1 == z.1) then true else if _ then true else _) = true at test
  rw [be, pp, fr] at test
  simp only [Bool.false_eq_true, ite_false, Bool.not_true, Bool.false_or] at test
  have nd' : (choiceVal (movedChoice op a b) :: rest.map Prod.fst).Nodup := val ▸ ndc
  have h' : Live T k t (choiceVal (movedChoice op a b) :: rest.map Prod.fst).toFinset := val ▸ h
  by_cases hq : (pools.map (summarizePool ws)).any (fun qp => fastCost qp (cap-1) a b op ka kb) = true
  · obtain ⟨qp,hqp,hfc⟩ := List.any_eq_true.mp hq
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hqp
    exact scalarPoolCut_sound (pv p hp) nd' (fastCost_good ha hb hfc) k t hk h'
  · have hqf : (pools.map (summarizePool ws)).any (fun qp => fastCost qp (cap-1) a b op ka kb) = false :=
      Bool.eq_false_iff.mpr hq
    change (if ((pools.map (summarizePool ws)).any fun qp => fastCost qp (cap-1) a b op ka kb) = true then true else _) = true at test
    rw [hqf] at test
    simp only [Bool.false_eq_true, ite_false] at test
    by_cases hd : d = true
    · dsimp only [d, ct] at hd; rw [hd] at test; simp only [ite_true] at test
      exact closeChildU_sound pv lv0 nd' test k t hk (fun _ => ht0 hd) h'
    · have hdf : d = false := Bool.eq_false_iff.mpr hd
      dsimp only [d, ct] at hdf; rw [hdf] at test; simp only [Bool.false_eq_true, ite_false] at test
      exact closeChildU_sound pv lv1 nd' test k t hk (fun h0 => by cases h0) h'

def testPairU (ctx : NodeContextU) (a b : Decor) (d : Bool) : Bool :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  evalMoveU ctx op a b z false false && evalMoveU ctx op a b z true false &&
    evalMoveU ctx op a b z false true && evalMoveU ctx op a b z true true

def testRowU (ctx : NodeContextU) (a : Decor) (bs : List Decor) : Bool :=
  let unOk := if ctx.2.1 == 0 then true else
    let n := movedDecor 2 a a
    evalMoveU ctx 2 a a n false false && evalMoveU ctx 2 a a n true true
  unOk && bs.all (fun b => testPairU ctx a b false && testPairU ctx a b true)

def testAllU (ctx : NodeContextU) : List Decor → Bool
  | [] => true
  | a :: ws => testRowU ctx a ws && testAllU ctx ws

theorem all_unaryU {ctx} {ws : List Decor} (h : testAllU ctx ws = true) (ht : ctx.2.1 > 0) {a : Decor} (ha : a ∈ ws) (keep : Bool) :
    evalMoveU ctx 2 a a (movedDecor 2 a a) keep keep = true := by
  induction ws with
  | nil => cases ha
  | cons x xs ih =>
    simp only [testAllU, Bool.and_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · have hr := h.1
      simp only [testRowU, Bool.and_eq_true] at hr
      have hne : (ctx.2.1 == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
      have hu := hr.1
      rw [hne] at hu; simp only [Bool.false_eq_true, ite_false, Bool.and_eq_true] at hu
      cases keep <;> [exact hu.1; exact hu.2]
    · exact ih h.2 hm

theorem all_binaryU {ctx} {ws : List Decor} (h : testAllU ctx ws = true) {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (d : Bool) :
    testPairU ctx a b d = true ∨ testPairU ctx b a d = true := by
  induction ws with
  | nil => cases ha
  | cons x xs ih =>
    simp only [testAllU, Bool.and_eq_true, testRowU, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · exact False.elim (ne rfl)
    · left; cases d <;> [exact (h.1.2 b hb').1; exact (h.1.2 b hb').2]
    · right; cases d <;> [exact (h.1.2 a ha').1; exact (h.1.2 a ha').2]
    · exact ih h.2 ha' hb'

theorem testPairU_at {ctx a b d} (h : testPairU ctx a b d = true) (ka kb : Bool) :
    evalMoveU ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [testPairU, Bool.and_eq_true] at h
  cases ka <;> cases kb <;> simp [h]

theorem nodeU_sound {raw T r s ws pools l0 l1 cap tm}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv0 : ∀ tag xs, xs ∈ l0 tag → ImpossibleU T (cap-1) 0 (List.toFinset xs))
    (lv1 : ∀ tag xs, xs ∈ l1 tag → ImpossibleU T (cap-1) 1 (List.toFinset xs))
    (checks : cap = 0 ∨ testAllU (cap,tm,ws.length,ws,preCov ws,pools,pools.map (summarizePool ws),l0,l1) ws = true) :
    ImpossibleU T cap tm (ws.map Prod.fst).toFinset := by
  rcases checks with rfl | checks
  · intro k t hk _ h
    have hk0 : k = 0 := by omega
    subst hk0
    generalize he : (ws.map Prod.fst).toFinset = S at h
    have eqS : S = {_} := h (fun k _ S => k = 0 → S = {_}) (fun _ _ => rfl)
      (fun _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn))
      (fun _ _ _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn)) rfl
    exact out (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
  by_cases hc : cap = 0
  · subst hc
    intro k t hk _ h
    have hk0 : k = 0 := by omega
    subst hk0
    generalize he : (ws.map Prod.fst).toFinset = S at h
    have eqS : S = {_} := h (fun k _ S => k = 0 → S = {_}) (fun _ _ => rfl)
      (fun _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn))
      (fun _ _ _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn)) rfl
    exact out (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
  have hc' : 0 < cap := by omega
  apply enum_stepU nd out
  · intro htpos v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    have hev := evalMoveU_sound (op := 2) pairs faith nd ha ha (by simp) hc' pv lv0 lv1 pro fresh (all_unaryU checks htpos ha keep)
    have hlenEq : (moveFront ws 2 a a keep keep).length = (childOne (ws.map Prod.fst) a.1 keep).length := by
      have nd1 : (moveFront ws 2 a a keep keep).Nodup := by
        unfold moveFront
        have sub := keep_sub ws a a true keep keep
        exact List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm), nd.sublist (sub.map _)⟩
      have nd2 : (childOne (ws.map Prod.fst) a.1 keep).Nodup := by
        unfold childOne
        have na : a.1 ∉ (ws.map Prod.fst).erase a.1 := nd.not_mem_erase
        refine List.nodup_cons.mpr ⟨fun hm => ?_, kept_nd keep a.1 _ (nd.erase _) na⟩
        rw [keep_mem] at hm
        rcases hm with ⟨heq,_⟩ | hm
        · exact fresh (heq.symm ▸ List.mem_map_of_mem ha)
        · exact fresh (List.mem_of_mem_erase hm)
      rw [←List.toFinset_card_of_nodup nd1, ←List.toFinset_card_of_nodup nd2, hf]
    rw [hf, hlenEq] at hev
    exact hev
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a ≠ b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a ∈ ws) (bb : b ∈ ws) (ne' : a.1 ≠ b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPairU (cap,tm,ws.length,ws,preCov ws,pools,pools.map (summarizePool ws),l0,l1) a b d = true) :
        ImpossibleU T (cap-1) (childU tm cap (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length)
          (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      have hf := binary_front nd aa bb ne' d ka kb
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      have hev := evalMoveU_sound (op := if d then 1 else 0) pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv0 lv1
        (eq ▸ pr) (eq ▸ fr) (testPairU_at test ka kb)
      have hlenEq : (moveFront ws (if d then 1 else 0) a b ka kb).length =
          (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length := by
        have nd1 : (moveFront ws (if d then 1 else 0) a b ka kb).Nodup := by
          unfold moveFront
          have sub := keep_sub ws a b ((if d then 1 else 0) == 2) ka kb
          exact List.nodup_cons.mpr ⟨fun hm => (eq ▸ fr) ((sub.map _).subset hm), nd.sublist (sub.map _)⟩
        have nd2 : (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).Nodup := by
          unfold childTwo
          let r0 := ((ws.map Prod.fst).erase a.1).erase b.1
          have rn : r0.Nodup := (nd.erase _).erase _
          have ar : a.1 ∉ r0 := fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
          have br : b.1 ∉ r0 := (nd.erase a.1).not_mem_erase
          have nk := kept_nd kb b.1 r0 rn br
          have ax : a.1 ∉ kept kb b.1 r0 := by cases kb <;> simp [kept,ar,ne']
          refine List.nodup_cons.mpr ⟨fun hm => ?_, kept_nd ka a.1 _ nk ax⟩
          rw [keep_mem] at hm
          rcases hm with ⟨heq,_⟩ | hm
          · exact fr (heq.symm ▸ List.mem_map_of_mem aa)
          · rw [keep_mem] at hm
            rcases hm with ⟨heq,_⟩ | hm
            · exact fr (heq.symm ▸ List.mem_map_of_mem bb)
            · exact fr (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        rw [←List.toFinset_card_of_nodup nd1, ←List.toFinset_card_of_nodup nd2, hf]
      rw [hf, hlenEq] at hev
      exact hev
    rcases all_binaryU checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · have hsw := childTwo_swap (ws.map Prod.fst) nd a.1 b.1 d ka kb
      have hlenSw : (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length =
          (childTwo (ws.map Prod.fst) b.1 a.1 d kb ka).length := by
        have ndA : (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).Nodup := by
          unfold childTwo
          let rA := ((ws.map Prod.fst).erase a.1).erase b.1
          have rn : rA.Nodup := (nd.erase a.1).erase b.1
          have ar : a.1 ∉ rA := fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
          have br : b.1 ∉ rA := (nd.erase a.1).not_mem_erase
          have nk := kept_nd kb b.1 rA rn br
          have ax : a.1 ∉ kept kb b.1 rA := by cases kb <;> simp [kept,ar,ne]
          refine List.nodup_cons.mpr ⟨fun hm => ?_, kept_nd ka a.1 _ nk ax⟩
          rw [keep_mem] at hm; rcases hm with ⟨heq,_⟩ | hm
          · exact fresh (heq.symm ▸ List.mem_map_of_mem haW)
          · rw [keep_mem] at hm; rcases hm with ⟨heq,_⟩ | hm
            · exact fresh (heq.symm ▸ List.mem_map_of_mem hbW)
            · exact fresh (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        have ndB : (childTwo (ws.map Prod.fst) b.1 a.1 d kb ka).Nodup := by
          unfold childTwo
          let rB := ((ws.map Prod.fst).erase b.1).erase a.1
          have rn : rB.Nodup := (nd.erase b.1).erase a.1
          have br : b.1 ∉ rB := fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
          have ar : a.1 ∉ rB := (nd.erase b.1).not_mem_erase
          have nk := kept_nd ka a.1 rB rn ar
          have bx : b.1 ∉ kept ka a.1 rB := by cases ka <;> simp [kept,br,Ne.symm ne]
          refine List.nodup_cons.mpr ⟨fun hm => ?_, kept_nd kb b.1 _ nk bx⟩
          rw [bin_comm d b.1 a.1] at hm
          rw [keep_mem] at hm; rcases hm with ⟨heq,_⟩ | hm
          · exact fresh (heq.symm ▸ List.mem_map_of_mem hbW)
          · rw [keep_mem] at hm; rcases hm with ⟨heq,_⟩ | hm
            · exact fresh (heq.symm ▸ List.mem_map_of_mem haW)
            · exact fresh (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        rw [←List.toFinset_card_of_nodup ndA, ←List.toFinset_card_of_nodup ndB, hsw]
      rw [hsw, hlenSw]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro) (bin_comm d a.1 b.1 ▸ fresh) hh
abbrev PackingT := Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPackingT : PackingT := (0, 0, 0, 0, fun _ => 0)

def deadWires : List Decor := wiresOf dead
def deadSigs : List Sig := deadWires.map Prod.fst

def decodeSigs (n : Nat) (bits : Nat) (ws : List Sig) : List Sig :=
  match n with
  | 0 => ws
  | k + 1 =>
    let a := ws.getD (bits &&& 15) zero
    let b := ws.getD ((bits >>> 4) &&& 15) zero
    let op := (bits >>> 8) &&& 3
    decodeSigs k (bits >>> 10) (ws ++ [if op = 2 then neg a else bin (op == 1) a b])

theorem decodeSigs_eq (n bits : Nat) (ws : List Decor) :
    decodeSigs n bits (ws.map Prod.fst) = (decodeBank n bits ws).map Prod.fst := by
  induction n generalizing bits ws with
  | zero => rfl
  | succ k ih =>
    simp only [decodeSigs, decodeBank]
    have hget : ∀ i, (ws.map Prod.fst).getD i zero = (ws.getD i defaultDecor).1 := by
      intro i
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases ws[i]? <;> rfl
    have hcode : (if ((bits >>> 8) &&& 3) = 2 then neg ((ws.map Prod.fst).getD (bits &&& 15) zero)
        else bin (((bits >>> 8) &&& 3) == 1) ((ws.map Prod.fst).getD (bits &&& 15) zero) ((ws.map Prod.fst).getD ((bits >>> 4) &&& 15) zero)) =
        (codeDecor ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) defaultDecor) (ws.getD ((bits >>> 4) &&& 15) defaultDecor)).1 := by
      rw [hget, hget]
      unfold codeDecor dbin dneg
      split
      · rfl
      · split <;> rfl
    rw [hcode, ← List.map_singleton, ← List.map_append]
    exact ih (bits >>> 10) _

theorem selectLive_map {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    selectLive bits (ws.map f) = (selectLive bits ws).map f := by
  induction ws generalizing bits with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, selectLive]
    split <;> simp [ih]

def readNodeT (levels : Nat → PackingT) (slot i : Nat) : Nat × List Decor × List Decor :=
  let raw := deadWires
  let (_, depth, _, _, data) := levels slot
  let len := 10 * depth
  let width := len + raw.length + depth
  let recp := packedAt data (i * width) width
  let ops := recp &&& ((1 <<< len) - 1)
  let bank := decodeBank depth ops raw
  (ops, bank, selectLive (recp >>> len) bank)

def stateSetT (levels : Nat → PackingT) (slot i : Nat) : List Sig :=
  let (_, depth, _, _, data) := levels slot
  let len := 10 * depth
  let width := len + deadSigs.length + depth
  let recp := packedAt data (i * width) width
  let ops := recp &&& ((1 <<< len) - 1)
  selectLive (recp >>> len) (decodeSigs depth ops deadSigs)

theorem stateSetT_eq (levels : Nat → PackingT) (slot i : Nat) :
    stateSetT levels slot i = (readNodeT levels slot i).2.2.map Prod.fst := by
  unfold stateSetT readNodeT
  rcases levels slot with ⟨num, depth, cw, offw, data⟩
  dsimp only
  have hlen : deadSigs.length = deadWires.length := by simp [deadSigs]
  rw [hlen]
  dsimp only [deadSigs]
  rw [decodeSigs_eq, selectLive_map]


def linkedSetT (levels : Nat → PackingT) (slot : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (levels slot).1 then none else
    (dead.autos[pair.2]?).map fun perm => (stateSetT levels slot pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSetU_sound (levels : Nat → PackingT) (k tm : Nat)
    (names : ∀ x ∈ dead.autos.toList, autoOK (targetOf dead) (x.map swapRows) = true)
    (earlier : ∀ i < (levels (3*k+tm)).1, ImpossibleU (targetOf dead) k tm (stateSetT levels (3*k+tm) i).toFinset)
    {pair out} (h : linkedSetT levels (3*k+tm) pair = some out) :
    ImpossibleU (targetOf dead) k tm out.toFinset := by
  unfold linkedSetT at h
  split at h
  · cases h
  next valid =>
    cases e : dead.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excludedU (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))

def contextOfU (levels : Nat → PackingT) (idx0 idx1 : Nat → Nat → Option (Nat × Nat)) (k tm i : Nat) : NodeContextU :=
  let slot := 3 * k + tm
  let raw := deadWires
  let (num, depth, cw, offw, data) := levels slot
  let (ops, bank, ws) := readNodeT levels slot i
  let start := num * (10 * depth + raw.length + depth)
  let pos := start + num * offw + packedAt data (start + i * offw) offw
  let nr := packedAt data pos 5
  let st := pos + 5
  let rules := (getPairs data cw depth nr st).filterMap (fun (a, b) => buildRule dead ops depth bank a b)
  let ls0 := fun tag => ((idx0 slot tag).bind (linkedSetT levels (3*(k-1)))).toList
  let ls1 := fun tag => ((idx1 slot tag).bind (linkedSetT levels (3*(k-1)+1))).toList
  (k, tm, ws.length, ws, preCov ws, rules, rules.map (summarizePool ws), ls0, ls1)

def prelimU (T : Sig) (c : NodeContextU) : Bool :=
  let ws := c.2.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)

def nodeVerifiedU (levels : Nat → PackingT) (idx0 idx1 : Nat → Nat → Option (Nat × Nat)) (k tm i : Nat) : Bool :=
  let c := contextOfU levels idx0 idx1 k tm i
  prelimU (targetOf dead) c && (if k = 0 then true else testAllU c c.2.2.2.1)

theorem nodeVerifiedU_sound (levels : Nat → PackingT) (idx0 idx1 : Nat → Nat → Option (Nat × Nat)) (k tm i : Nat)
    (samples : properPairs (targetOf dead) (asRow fun j => (dead.samples j).1) (asRow fun j => (dead.samples j).2))
    (cols : ∀ ci ∈ dead.cols.values, Slice (vars dead.mask) (targetOf dead) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ dead.autos.toList, autoOK (targetOf dead) (x.map swapRows) = true)
    (prior0 : k > 0 → ∀ j < (levels (3*(k-1))).1, ImpossibleU (targetOf dead) (k-1) 0 (stateSetT levels (3*(k-1)) j).toFinset)
    (prior1 : k > 0 → ∀ j < (levels (3*(k-1)+1)).1, ImpossibleU (targetOf dead) (k-1) 1 (stateSetT levels (3*(k-1)+1) j).toFinset)
    (checked : nodeVerifiedU levels idx0 idx1 k tm i = true) :
    ImpossibleU (targetOf dead) k tm (stateSetT levels (3*k+tm) i).toFinset := by
  rw [stateSetT_eq]
  simp only [nodeVerifiedU, prelimU, contextOfU, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at checked
  have hN := checked.1.1
  have hT : targetOf dead ∉ (readNodeT levels (3*k+tm) i).2.2.map Prod.fst := checked.1.2
  by_cases h0 : k = 0
  · subst k
    intro k' t' hk' _ h
    have hk0 : k' = 0 := by omega
    subst k'
    generalize he : ((readNodeT levels (3*0+tm) i).2.2.map Prod.fst).toFinset = S at h
    have eqS : S = {_} := h (fun k _ S => k = 0 → S = {_}) (fun _ _ => rfl)
      (fun _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn))
      (fun _ _ _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn)) rfl
    exact hT (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
  apply nodeU_sound (raw:=vars dead.mask) samples _ hN hT _ _ _ (Or.inr (by simpa only [h0,ite_false] using checked.2))
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful dead) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound dead cols h
  · intro tag xs hx
    have e : ((idx0 (3*k+tm) tag).bind (linkedSetT levels (3*(k-1)))) = some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    have h0' : 3*(k-1) = 3*(k-1)+0 := by omega
    rw [h0'] at h
    exact linkedSetU_sound levels (k-1) 0 names (by simpa [←h0'] using prior0 (by omega)) h
  · intro tag xs hx
    have e : ((idx1 (3*k+tm) tag).bind (linkedSetT levels (3*(k-1)+1))) = some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSetU_sound levels (k-1) 1 names (prior1 (by omega)) h

def blockU (levels : Nat → PackingT) (idx0 idx1 : Nat → Nat → Option (Nat × Nat)) (k tm start : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => nodeVerifiedU levels idx0 idx1 k tm start && blockU levels idx0 idx1 k tm (start + 1) n

theorem blockU_at {levels idx0 idx1 k tm start n} (h : blockU levels idx0 idx1 k tm start n = true)
    (i : Nat) (lo : start ≤ i) (hi : i < start + n) : nodeVerifiedU levels idx0 idx1 k tm i = true := by
  induction n generalizing start with
  | zero => omega
  | succ n ih =>
    simp only [blockU,Bool.and_eq_true] at h
    by_cases eq : i = start
    · exact eq ▸ h.1
    · exact ih h.2 (by omega) (by omega)

theorem blockU_merge {levels idx0 idx1 k tm start a b}
    (ha : blockU levels idx0 idx1 k tm start a = true)
    (hb : blockU levels idx0 idx1 k tm (start + a) b = true) :
    blockU levels idx0 idx1 k tm start (a + b) = true := by
  induction a generalizing start with
  | zero => simpa [blockU] using hb
  | succ a ih =>
    simp only [blockU,Nat.succ_add,Bool.and_eq_true] at ha ⊢
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm 1] using hb)⟩

theorem makeBlockU {levels idx0 idx1 k tm start n}
    (h : ∀ i, start ≤ i → i < start + n → nodeVerifiedU levels idx0 idx1 k tm i = true) :
    blockU levels idx0 idx1 k tm start n = true := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [blockU, Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega), ih (fun i lo hi => h i (by omega) (by omega))⟩

def checkAtU (c : NodeContextU) (i j op : Nat) (ka kb : Bool) : Bool :=
  let a := ctxWireU c i
  let b := ctxWireU c j
  evalMoveU c op a b (movedDecor op a b) ka kb

def combFieldU (c : NodeContextU) (d un ka kb : Bool) (op i j : Nat) : Bits :=
  let a := ctxWireU c i
  let b := ctxWireU c j
  restCov (getCov c.2.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2

def fallbackFastU (c : NodeContextU) (i j op : Nat) (ka kb : Bool) : Bool :=
  let (cap,tm,n,ws,_,pools,qpools,l0,l1) := c
  let a := ws.getD i defaultDecor
  let b := ws.getD j defaultDecor
  let un := op == 2
  let len := 1 + (n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  let ct := childU tm cap len
  let z1 := choiceVal (movedChoice op a b)
  if !properB z1 || ws.any (fun v => v.1 == z1) then true else
  if qpools.any (fun qp => fastCost qp (cap-1) a b op ka kb) then true else
    let rest := (opKeep un ka kb a b ws).map Prod.fst
    let links := if ct == 0 then l0 else l1
    closeChild pools links (cap-1) rest (movedChoice op a b)

theorem fallbackFastU_sound {c i j op ka kb}
    (hlen : ¬(1 + (c.2.2.1 - (if ka then 0 else 1) - (if (op == 2) || kb then 0 else 1)) > c.1))
    (h : fallbackFastU c i j op ka kb = true) :
    checkAtU c i j op ka kb = true := by
  rcases c with ⟨cap, tm, n, ws, cov, pools, qpools, l0, l1⟩
  dsimp only [checkAtU, evalMoveU, ctxWireU]
  dsimp only at hlen
  rw [if_neg hlen]
  dsimp only [fallbackFastU] at h
  have hz1 : (movedDecor op (ws.getD i defaultDecor) (ws.getD j defaultDecor)).1 =
      choiceVal (movedChoice op (ws.getD i defaultDecor) (ws.getD j defaultDecor)) :=
    moved_full op _ _
  set len := 1 + (n - (if ka then 0 else 1) - (if (op == 2) || kb then 0 else 1))
  set ct := childU tm cap len
  set d := ct == 0
  by_cases hcomb : ((restCov (getCov cov d) (column d (ws.getD i defaultDecor).2) (column d (ws.getD j defaultDecor).2) (op == 2) ka kb ||| column d (movedDecor op (ws.getD i defaultDecor) (ws.getD j defaultDecor)).2) != BitVec.allOnes 768) = true
  · simp only [hcomb, ite_true]
  · simp only [hcomb, ite_false, hz1]
    exact h

def makeBatchU (k n : Nat) (xs : List NodeContextU) : Batch :=
  (k, n, units xs.length,
    (List.range n).map (fun i => packedSig (fun c => (ctxWireU c i).2) xs),
    packedCov (fun c => c.2.2.2.2.1.1) xs,
    packedCov (fun c => c.2.2.2.2.1.2) xs)

theorem laneWireU_at (k n : Nat) (xs : List NodeContextU) {i : Nat} (h : i < n) :
    laneWire (makeBatchU k n xs) i = packedSig (fun c => (ctxWireU c i).2) xs := by
  simp [laneWire, makeBatchU, List.getD_eq_getElem?_getD, h]

def batchMoveU (b : Batch) (tm : Nat) (xs : List NodeContextU) (i j op : Nat) (ka kb : Bool) : Bool :=
  let (k, n, r, _, u, v) := b
  let un := op == 2
  let len := 1 + (n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len > k then true else
    let d := childU tm k len == 0
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r * (BitVec.allOnes 768).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackFastU c i j op ka kb) mask xs

theorem batchMoveU_at (k tm n : Nat) (xs : List NodeContextU) {i j op : Nat} {ka kb}
    (hi : i < n) (hj : j < n) {q : Nat} (hq : q < xs.length)
    (budget : xs[q].1 = k) (ht : xs[q].2.1 = tm) (arity : xs[q].2.2.1 = n)
    (pass : batchMoveU (makeBatchU k n xs) tm xs i j op ka kb = true) :
    checkAtU xs[q] i j op ka kb = true := by
  let len := 1 + (n - (if ka then 0 else 1) - (if (op == 2) || kb then 0 else 1))
  let d := childU tm k len == 0
  have eval : checkAtU xs[q] i j op ka kb =
      if len > k then true else if combFieldU xs[q] d (op == 2) ka kb op i j != BitVec.allOnes 768 then true
      else fallbackFastU xs[q] i j op ka kb := by
    rcases hxq : xs[q] with ⟨cap, tmm, nn, ws, cov, pools, qpools, l0, l1⟩
    rw [hxq] at budget ht arity
    dsimp only at budget ht arity
    subst budget ht arity
    unfold checkAtU evalMoveU combFieldU fallbackFastU ctxWireU
    dsimp only [len, d]
    have hz1 : (movedDecor op (ws.getD i defaultDecor) (ws.getD j defaultDecor)).1 =
        choiceVal (movedChoice op (ws.getD i defaultDecor) (ws.getD j defaultDecor)) := moved_full op _ _
    rw [hz1]
  by_cases small : len > k
  · simp [eval, small]
  · let r := units xs.length
    let a := laneWire (makeBatchU k n xs) i
    let b := laneWire (makeBatchU k n xs) j
    let cov := if d then packedCov (fun c : NodeContextU => c.2.2.2.2.1.2) xs
               else packedCov (fun c : NodeContextU => c.2.2.2.2.1.1) xs
    change (if len > k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op == 2) ka kb |||
        packedColumn d (packedOp (r * (BitVec.allOnes 768).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.2.1 d) xs := by
      dsimp only [cov]; cases d <;> rfl
    have ca : a = _ := laneWireU_at k n xs hi
    have cb : b = _ := laneWireU_at k n xs hj
    dsimp only [r] at pass
    rw [ca, cb, packed_op, packed_column, packed_column, packed_column, chosen, takePacked_ok, lanes_or] at pass
    by_cases hit : combFieldU xs[q] d (op == 2) ka kb op i j = BitVec.allOnes 768
    · have hlenq : ¬(1 + (xs[q].2.2.1 - (if ka then 0 else 1) - (if (op == 2) || kb then 0 else 1)) > xs[q].1) := by
        rw [budget, arity]; exact small
      apply fallbackFastU_sound hlenq
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval, if_neg small, if_pos (bne_iff_ne.mpr hit)]

def batchPairU (b : Batch) (tm : Nat) (xs : List NodeContextU) (i j op : Nat) : Bool :=
  let f := batchMoveU b tm xs i j op
  f false false && f true false && f false true && f true true

def batchRowU (b : Batch) (tm : Nat) (xs : List NodeContextU) (i : Nat) (js : List Nat) : Bool :=
  let unOk := if tm == 0 then true else
    batchMoveU b tm xs i i 2 false false && batchMoveU b tm xs i i 2 true true
  unOk && js.all (fun j => batchPairU b tm xs i j 0 && batchPairU b tm xs i j 1)

def batchRowsU (b : Batch) (tm : Nat) (xs : List NodeContextU) : List Nat → Bool
  | [] => true
  | i :: js => batchRowU b tm xs i js && batchRowsU b tm xs js

theorem batchRowsU_at (k tm n : Nat) (xs : List NodeContextU) {q : Nat} (hq : q < xs.length)
    (budget : xs[q].1 = k) (ht : xs[q].2.1 = tm) (arity : xs[q].2.2.1 = n) (js : List Nat)
    (bounds : ∀ j ∈ js, j < n) (allRows : batchRowsU (makeBatchU k n xs) tm xs js = true) :
    testAllU xs[q] (js.map (ctxWireU xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRowsU, Bool.and_eq_true, batchRowU, List.all_eq_true] at allRows
    simp only [List.map_cons, testAllU, testRowU, Bool.and_eq_true, List.all_eq_true, List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMoveU_at k tm n xs
    have hun : (if xs[q].2.1 == 0 then true else
        evalMoveU xs[q] 2 (ctxWireU xs[q] i) (ctxWireU xs[q] i) (movedDecor 2 (ctxWireU xs[q] i) (ctxWireU xs[q] i)) false false &&
        evalMoveU xs[q] 2 (ctxWireU xs[q] i) (ctxWireU xs[q] i) (movedDecor 2 (ctxWireU xs[q] i) (ctxWireU xs[q] i)) true true) = true := by
      rw [ht]
      cases htm : (tm == 0)
      · simp only [Bool.false_eq_true, ite_false, Bool.and_eq_true]
        have h1 := allRows.1.1
        simp only [htm, Bool.false_eq_true, ite_false, Bool.and_eq_true] at h1
        exact ⟨check hi hi hq budget ht arity h1.1, check hi hi hq budget ht arity h1.2⟩
      · simp
    refine ⟨⟨hun, ?_⟩, ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j, hj, rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPairU (makeBatchU k n xs) tm xs i j (if d then 1 else 0) = true) :
        testPairU xs[q] (ctxWireU xs[q] i) (ctxWireU xs[q] j) d = true := by
      simp only [batchPairU, Bool.and_eq_true] at pass
      simp only [testPairU, Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget ht arity pass.1.1.1, check hi hj' hq budget ht arity pass.1.1.2⟩,
        check hi hj' hq budget ht arity pass.1.2⟩, check hi hj' hq budget ht arity pass.2⟩
    exact ⟨opCheck false both.1, opCheck true both.2⟩

def runBatchU (k tm n : Nat) (xs : List NodeContextU) : Bool :=
  batchRowsU (makeBatchU k n xs) tm xs (List.range n)

theorem runBatchU_at {k tm n} {xs : List NodeContextU} {q} (hq : q < xs.length)
    (hb : xs[q].1 = k) (ht : xs[q].2.1 = tm) (ha : xs[q].2.2.1 = n) (hn : xs[q].2.2.2.1.length = n)
    (pass : runBatchU k tm n xs = true) : testAllU xs[q] xs[q].2.2.2.1 = true := by
  have all := batchRowsU_at k tm n xs hq hb ht ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (ctxWireU xs[q]) = xs[q].2.2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [ctxWireU, List.getD_eq_getElem?_getD, h2]
  rwa [eq] at all

def contextsU (levels : Nat → PackingT) (idx0 idx1 : Nat → Nat → Option (Nat × Nat)) (k tm start n : Nat) : List NodeContextU :=
  ((List.range n).map (start + ·)).map (contextOfU levels idx0 idx1 k tm)

def chunkCheckU (levels : Nat → PackingT) (idx0 idx1 : Nat → Nat → Option (Nat × Nat)) (k tm start n ar : Nat) : Bool :=
  let xs := contextsU levels idx0 idx1 k tm start n
  xs.all (fun c => c.2.2.1 == ar && prelimU (targetOf dead) c) &&
  let b := makeBatchU k ar xs
  (List.range ar).all (fun i => batchRowU b tm xs i (List.range' (i + 1) (ar - (i + 1))))

theorem chunkBlockU {levels idx0 idx1 k tm start n ar}
    (h : chunkCheckU levels idx0 idx1 k tm start n ar = true) :
    blockU levels idx0 idx1 k tm start n = true := by
  unfold chunkCheckU at h
  rw [Bool.and_eq_true] at h
  let xs := contextsU levels idx0 idx1 k tm start n
  have hrun : runBatchU k tm ar xs = true := by
    have go (lo num : Nat) (eq : lo + num = ar) :
        batchRowsU (makeBatchU k ar xs) tm xs (List.range' lo num) = true := by
      induction num generalizing lo with
      | zero => rfl
      | succ num ih =>
        simp only [List.range'_succ, batchRowsU, Bool.and_eq_true]
        refine ⟨?_, ih (lo + 1) (by omega)⟩
        have ok := List.all_eq_true.mp h.2 lo (List.mem_range.mpr (by omega))
        simpa only [show ar - (lo + 1) = num by omega] using ok
    unfold runBatchU; rw [List.range_eq_range']; exact go 0 ar (by omega)
  apply makeBlockU
  intro i lo hi
  have hm : contextOfU levels idx0 idx1 k tm i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i, List.mem_map.mpr ⟨i - start, List.mem_range.mpr (by omega), by omega⟩, rfl⟩
  obtain ⟨q, hq, e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp h.1 _ hm
  simp only [Bool.and_eq_true, beq_iff_eq] at one
  have hb : xs[q].1 = k := by rw [e]; rfl
  have ht : xs[q].2.1 = tm := by rw [e]; rfl
  have ha : xs[q].2.2.1 = ar := e ▸ one.1
  have hn : xs[q].2.2.2.1.length = ar := by rw [e]; exact one.1
  simp only [nodeVerifiedU, Bool.and_eq_true]
  refine ⟨one.2, ?_⟩
  split
  · rfl
  · exact e ▸ runBatchU_at hq hb ht ha hn hrun

def cellsU (levels : Nat → PackingT) (idx0 idx1 : Nat → Nat → Option (Nat × Nat)) (k tm start n ar : Nat) : Nat → Prop
  | 0 => chunkCheckU levels idx0 idx1 k tm start n ar = true
  | d + 1 => cellsU levels idx0 idx1 k tm start (n / 2) ar d ∧ cellsU levels idx0 idx1 k tm (start + n / 2) (n - n / 2) ar d

theorem kU {levels idx0 idx1 k tm start n ar}
    (h : chunkCheckU levels idx0 idx1 k tm start n ar = true) :
    cellsU levels idx0 idx1 k tm start n ar 0 := h

theorem cellsBlockU {levels idx0 idx1 k tm start n ar d}
    (h : cellsU levels idx0 idx1 k tm start n ar d) :
    blockU levels idx0 idx1 k tm start n = true := by
  induction d generalizing start n with
  | zero => exact chunkBlockU h
  | succ d ih =>
    have v := blockU_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

theorem forestU_all (levels : Nat → PackingT) (idx0 idx1 : Nat → Nat → Option (Nat × Nat)) (top : Nat)
    (prior : Nat → Nat)
    (lo : ∀ m, Lower (vars m) (graphGoal m) (prior m))
    (valid : graphValid dead prior = true)
    (tabs : ∀ k ≤ top, ∀ tm ≤ 1, blockU levels idx0 idx1 k tm 0 (levels (3*k+tm)).1 = true) :
    ∀ k ≤ top, ∀ tm ≤ 1, ∀ i < (levels (3*k+tm)).1, ImpossibleU (targetOf dead) k tm (stateSetT levels (3*k+tm) i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at valid
  have pairs := chart_pairs valid.1.1.1 valid.1.1.2
  have cols : ∀ ci ∈ dead.cols.values, Slice (vars dead.mask) (targetOf dead) (subcube ci.1 ci.2.1) ci.2.2.2.2 :=
    fun ci hc => col_sound ci prior lo (valid.1.2 ci hc)
  have names := valid.2
  intro k
  induction k with
  | zero =>
    intro hk tm htm i hi
    have hb := tabs 0 hk tm htm
    exact nodeVerifiedU_sound levels idx0 idx1 0 tm i pairs cols names
      (fun h => False.elim (Nat.lt_irrefl 0 h))
      (fun h => False.elim (Nat.lt_irrefl 0 h))
      (blockU_at hb i (Nat.zero_le i) (by simpa using hi))
  | succ k ih =>
    intro hk tm htm i hi
    have hb := tabs (k + 1) hk tm htm
    exact nodeVerifiedU_sound levels idx0 idx1 (k + 1) tm i pairs cols names
      (fun _ j hj => ih (by omega) 0 (by decide) j hj)
      (fun _ j hj => ih (by omega) 1 (by decide) j hj)
      (blockU_at hb i (Nat.zero_le i) (by simpa using hi))
def fR1L40F (i : Nat) : Nat := 0x181c18100281ff
def fR1L40 : PackingT := (1,0,7,6,fR1L40F)
def fR1Levels : Nat → PackingT
  | 40 => fR1L40
  | _ => emptyPackingT
def fR1Idx0 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def fR1Idx1 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
abbrev bkT := blockU fR1Levels fR1Idx0 fR1Idx1
abbrev bmT (k tm s a b : Nat) := @blockU_merge fR1Levels fR1Idx0 fR1Idx1 k tm s a b
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem c40_0 : bkT 13 1 0 1=true := by
  apply cellsBlockU (ar:=9) (d:=0)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem a40 : bkT 13 1 0 1 = true := c40_0
theorem tablesfR1 : ∀ k ≤ 13, ∀ tmax ≤ 1, blockU fR1Levels fR1Idx0 fR1Idx1 k tmax 0 (fR1Levels (3*k+tmax)).1 = true := by
  intro k hk tmax ht
  interval_cases k <;> interval_cases tmax
  · exact (rfl : blockU fR1Levels fR1Idx0 fR1Idx1 0 0 0 0 = true)
  · exact (rfl : blockU fR1Levels fR1Idx0 fR1Idx1 0 1 0 0 = true)
  · exact (rfl : blockU fR1Levels fR1Idx0 fR1Idx1 1 0 0 0 = true)
  · exact (rfl : blockU fR1Levels fR1Idx0 fR1Idx1 1 1 0 0 = true)
  · exact (rfl : blockU fR1Levels fR1Idx0 fR1Idx1 2 0 0 0 = true)
  · exact (rfl : blockU fR1Levels fR1Idx0 fR1Idx1 2 1 0 0 = true)
  · exact (rfl : blockU fR1Levels fR1Idx0 fR1Idx1 3 0 0 0 = true)
  · exact (rfl : blockU fR1Levels fR1Idx0 fR1Idx1 3 1 0 0 = true)
  · exact (rfl : blockU fR1Levels fR1Idx0 fR1Idx1 4 0 0 0 = true)
  · exact (rfl : blockU fR1Levels fR1Idx0 fR1Idx1 4 1 0 0 = true)
  · exact (rfl : blockU fR1Levels fR1Idx0 fR1Idx1 5 0 0 0 = true)
  · exact (rfl : blockU fR1Levels fR1Idx0 fR1Idx1 5 1 0 0 = true)
  · exact (rfl : blockU fR1Levels fR1Idx0 fR1Idx1 6 0 0 0 = true)
  · exact (rfl : blockU fR1Levels fR1Idx0 fR1Idx1 6 1 0 0 = true)
  · exact (rfl : blockU fR1Levels fR1Idx0 fR1Idx1 7 0 0 0 = true)
  · exact (rfl : blockU fR1Levels fR1Idx0 fR1Idx1 7 1 0 0 = true)
  · exact (rfl : blockU fR1Levels fR1Idx0 fR1Idx1 8 0 0 0 = true)
  · exact (rfl : blockU fR1Levels fR1Idx0 fR1Idx1 8 1 0 0 = true)
  · exact (rfl : blockU fR1Levels fR1Idx0 fR1Idx1 9 0 0 0 = true)
  · exact (rfl : blockU fR1Levels fR1Idx0 fR1Idx1 9 1 0 0 = true)
  · exact (rfl : blockU fR1Levels fR1Idx0 fR1Idx1 10 0 0 0 = true)
  · exact (rfl : blockU fR1Levels fR1Idx0 fR1Idx1 10 1 0 0 = true)
  · exact (rfl : blockU fR1Levels fR1Idx0 fR1Idx1 11 0 0 0 = true)
  · exact (rfl : blockU fR1Levels fR1Idx0 fR1Idx1 11 1 0 0 = true)
  · exact (rfl : blockU fR1Levels fR1Idx0 fR1Idx1 12 0 0 0 = true)
  · exact (rfl : blockU fR1Levels fR1Idx0 fR1Idx1 12 1 0 0 = true)
  · exact (rfl : blockU fR1Levels fR1Idx0 fR1Idx1 13 0 0 0 = true)
  · exact a40
def fR2L28F (i : Nat) : Nat := 0x3c003e001000009543ca140fb61825498154600fbc1824c9814c6009ed9c6aed818ce009ee9c6aed8188a009df1c7aed5284600ff42558ce2284600
def fR2L28 : PackingT := (6,5,7,6,fR2L28F)
def fR2L31F (i : Nat) : Nat := 0xe001e001e0010001c003c0020e001e0010005bf00170008c913223b80104370017000806ff0017000f00083800462f00170008002df800864f0010c516dc007c0022db800862f00108ee00200006a42038a100006a42001b6080c704000186080d4840038a131c10000f142003b6f8be634113e2fb6f303f8bedbcc0fe2fb6f3037f0fa1ec3d379cf25dcba9748e51c237f6f4d7da7b1e606bcd772d3586acd5729e5069cd3726949c8cd069fd3c471cd61a7344674c69882f05ccb71692b2550a793f2744a89292023642c830f61e23b06e0cc18e3085e8ad15028c3904c04c0027fcd9d54c14013fe6c6aa60a009ff576d4265005feabb609328037f4c1554994016feaed8260600f7d304a9303007be9824c9818035fcc1554c0c01efc6098154600fee2a4c0aa3005ff2bb605518037f8c0d54a8c013feaeda84c6009ff576d2a63004ff8ba609318035fcd430498c01ff2609324c600bfb57699263006ff1a560531803df8c130298c01ff44c9814c600bfe576c0a63004ff9b8aa9318027fcdad5498c013fe6caaa4c600dfb26555263006ff181aa9318027fd5db5090c013feaeda5486009ff374c2a43004ffabb68d218027fcdd30690c013fe6e95348600dfe35098a43005ff2bb4c5218037f898d5490c017f6aed818ce00ffa302a8c67005fdabb54633802fecdaa4319c017f6aed218ce00bfd576c1c45005fe9b854e22803fe4c1aa7114017faaed5388a00bfd576c0c45005fe9b84c622802ff4daa6311401ff86053188a00bfd57698c45007be931a2222802ff95db0708c01efc60d8284600bfe576c1423007fe18254a11802ff95daa508c017fc6e13284600bfe36a99423007fe1824ca11802ff95da6508c01ff46163384600ffa30519c23007fd1528ce11803ff0c1c4508c01ff854e22846009df36d55303007bd2888ce11803df14444508c01ff08ce2284600
def fR2L31 : PackingT := (70,4,7,11,fR2L31F)
def fR2H1_31F (i : Nat) : Nat := 0x1ac158100c4000300600d8154c20300c043c4e8400c0180300600c01a4400620000
def fR2H1_31 (h : Nat) : Option (Nat × Nat) := lookupWord 4 23 5 11 3 4 fR2H1_31F h
def fR2L34F (i : Nat) : Nat := 0xc760026d982c006431bf800c92c004e2925800d82c005db353800fb663b001f6cc36003361c5adb0021255b600363b00138ac360030b70011258009df6db001b53800986c0058004d871486c0084111d800c896db001b8a44e003227001113800889c00444e002c00a923adf20bc5edb98a19380152413bfe2f6dcc51d4325dff17b6e628e2e006f95249105e2f6dcc50c9c03c5edb9861a8236005491c7b10d6ff8bdb731412b0077fc5edaa9e60c6f91c1690d54f8bdb7314127002a48677fc5edb98a3a824e006f90de2f6cd4f31475049c03c5edb9861a8233bfe2f6dcc51c5c00df2a486a3bc5edb98a09380152473bfe2f6dcc50d41270037c8ef17b66a798a1a824e006f953e2f6dcc31d435049f17b6e618ea18b801be549124750de2f6dcc504aa3b006a58677fc5edb98609347600efb0de2f6cd4f30c1268ec01df6a7c5edb98619824d0d80352c13bfe2f6dcc31c9a1b0077d82f17b66a798639343600d4b1ceff8bdb730c12686c01df6a7c5edb98639824d0580352c33bfe2f6dcc31c9a0b006a58e77fc5edb98619341600efb1de2f6cd4f30c32682c01df6a7c5edb98639864bbf43601e2f6dd4f31c7704963a82c03dff17b6ea798e192c3505807bfe2f6dd4f31c72790b87f7f378f70369f6135874fb4473bb3572cb2672031771130af072fbef32ea6e1adb6d52ceec8ab0e9928b673a63649238e212095f19e15d39bbda418c574966d4c934d1d1054ed8d5cbe0a648e876c5f04742f817c003ff9a360a00ffe68582803ffaaa60a00ffe6a132803ff9a54ca00ffe68532803ff9a560600ffe68d81803ff9a260600ffe54981803ff93260600ffe68d51803ff9a254600ffe60951803ff93254600ffe6a131803ff9a54c600ffe68931803ff9824c600ffe54931803ffaaa4c600ffe6a121803ff9a548600ffe61521803ff9a348600ffe60d21803ff95348600bfeaa982802ff9a84ca00ffa60932802ffaaa4ca00efe60981802ffaaa60600ffc60551802ffaaa54600bfe6a131802ff9a54c600ff64c931803ff1814c600bfeaa931802ff9a848600bfe69521802ff9a348600ffc4c521802ffaaa48600ff660633803fd9518ce00ff648633803fe98388a00ffa54e22803fe98188a00ffa4c622803ff18384600ffc60a11803ff15284600ffc4ca11803bea8888a00ff48ce11803fe22284600
def fR2L34 : PackingT := (59,3,7,12,fR2L34F)
def fR2H1_34F (i : Nat) : Nat := 0xd00230099008c011a000bb9f813a0119813f815db26c22246050a58036807ec59503c811c421b413609a2024cc7a805d02c008cc2d48060046008de2490489804d02fe439c478046008c0118023103671200118540b095d01c20e2e02e9065001e090c08a844e82000a30158a12db2d4078c019016a086c8028039081008da2f00230046008c0118814d904008c101c0237013505d5030023681aa03a011a90c8030008d8233806e90bc0058816803282f008c01180230046008c01180230046008da0e402300462028011b9838046008c011a84fa8a49046a2600230046008c0118023383d821820ddc028046008c01184100046008c4234023203a008c01180236035008c01180230046008ca859c0c8046b081cc1958eed99a202f66ec1f3032f80cae1f41d8a146816011802340217116011a0228046008c01180230046008c011802368c2c05a0118e078046a08401180230008971030200230046008c0119d099110008d209402300463172011900e5809c062e26dc20f00f781d20880235c0a5812011941570331020011ac82d83f008dc4238050046008c011b00c08c4050405000500010501010d04030b010105060e0009000004070600030102040100040303030d0009160001000401
def fR2H1_34 (h : Nat) : Option (Nat × Nat) := lookupWord 46 223 8 15 7 4 fR2H1_34F h
def fR2L37F (i : Nat) : Nat := 0x401bfc5db6a7318e436093004977f8bb6d4e611c86c12a00f66ff176da9cc63b0c8254005bdfe2ed95398c761904a8077f8bb6d4e611d8641260089eff176da9cc6390c82523a01dfe2edb5398c36092868077f8bb6d4e631d824a0a01dfe2edb5398c761936a4eb0b36eb0a04560ac007fe60a00ffc99401ff981803ff2a3007fe4c600ffc90c01fda33803fd445007fc84600
def fR2L37 : PackingT := (9,2,7,10,fR2L37F)
def fR2H1_37F (i : Nat) : Nat := 0x180200ec03b00ec03b00ec03b00eec0800ec02b302803b00edc6e00edc80720c03b00ec03bf073025f0a803800ec03b0041c39012c041403d2c7b205020507803bf1a003b00ec03b5184436511846c80191c1941c0005815460a09803b00ec03b903401d508e44a580c03b960403b011403be0c003b912585200ec03bb16d81b51666ca00ed411e17403bd066c1a90c7807e0d403b608601800ec03b00ec03b30df829e05403b703380100ec03be08803be0cc03b00ee01fe0ba83200ef02c300c03be0e8814305c03b219c03b00efc1200ec03b00ec809e01081600ec03b00ef80500edc2d00ec03b00ec80e713403bc02c03b00ee834311003b7633c79d04ce013090d0a00ec03b415fc5100eec2f00ef02700edc8500ec03b00ec03bc0a003b0000000201000201010100010002000901020102020000010001000001000001
def fR2H1_37 (h : Nat) : Option (Nat × Nat) := lookupWord 32 165 8 14 6 4 fR2H1_37F h
def fR2L40F (i : Nat) : Nat := 0xdfc5b6a9988e8682480ffa00
def fR2L40 : PackingT := (1,1,7,7,fR2L40F)
def fR2H1_40F (i : Nat) : Nat := 0x13a23c27e10012c0c02860f20140ba07e0401242f20922020201262c700420
def fR2H1_40 (h : Nat) : Option (Nat × Nat) := lookupWord 5 19 5 12 4 4 fR2H1_40F h
def fR2Levels : Nat → PackingT
  | 28 => fR2L28
  | 31 => fR2L31
  | 34 => fR2L34
  | 37 => fR2L37
  | 40 => fR2L40
  | _ => emptyPackingT
def fR2Idx0 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def fR2Idx1 : Nat → Nat → Option (Nat × Nat)
  | 31 => fR2H1_31
  | 34 => fR2H1_34
  | 37 => fR2H1_37
  | 40 => fR2H1_40
  | _ => fun _ => none
abbrev T2_bkT := blockU fR2Levels fR2Idx0 fR2Idx1
abbrev T2_bmT (k tm s a b : Nat) := @blockU_merge fR2Levels fR2Idx0 fR2Idx1 k tm s a b
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T2_c28_0 : T2_bkT 9 1 0 6=true := by
  apply cellsBlockU (ar:=9) (d:=0)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T2_a28 : T2_bkT 9 1 0 6 = true := T2_c28_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T2_c31_0 : T2_bkT 10 1 0 4=true := by
  apply cellsBlockU (ar:=9) (d:=0)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T2_c31_4 : T2_bkT 10 1 4 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T2_c31_52 : T2_bkT 10 1 52 18=true := by
  apply cellsBlockU (ar:=10) (d:=1)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T2_a31 : T2_bkT 10 1 0 70 = true := (T2_bmT 10 1 0 4 66 T2_c31_0 (T2_bmT 10 1 4 48 18 T2_c31_4 T2_c31_52))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T2_c34_0 : T2_bkT 11 1 0 3=true := by
  apply cellsBlockU (ar:=9) (d:=0)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T2_c34_3 : T2_bkT 11 1 3 29=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T2_c34_32 : T2_bkT 11 1 32 27=true := by
  apply cellsBlockU (ar:=11) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T2_a34 : T2_bkT 11 1 0 59 = true := (T2_bmT 11 1 0 3 56 T2_c34_0 (T2_bmT 11 1 3 29 27 T2_c34_3 T2_c34_32))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T2_c37_0 : T2_bkT 12 1 0 3=true := by
  apply cellsBlockU (ar:=9) (d:=0)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T2_c37_3 : T2_bkT 12 1 3 6=true := by
  apply cellsBlockU (ar:=10) (d:=0)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T2_a37 : T2_bkT 12 1 0 9 = true := (T2_bmT 12 1 0 3 6 T2_c37_0 T2_c37_3)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T2_c40_0 : T2_bkT 13 1 0 1=true := by
  apply cellsBlockU (ar:=9) (d:=0)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T2_a40 : T2_bkT 13 1 0 1 = true := T2_c40_0
theorem tablesfR2 : ∀ k ≤ 13, ∀ tmax ≤ 1, blockU fR2Levels fR2Idx0 fR2Idx1 k tmax 0 (fR2Levels (3*k+tmax)).1 = true := by
  intro k hk tmax ht
  interval_cases k <;> interval_cases tmax
  · exact (rfl : blockU fR2Levels fR2Idx0 fR2Idx1 0 0 0 0 = true)
  · exact (rfl : blockU fR2Levels fR2Idx0 fR2Idx1 0 1 0 0 = true)
  · exact (rfl : blockU fR2Levels fR2Idx0 fR2Idx1 1 0 0 0 = true)
  · exact (rfl : blockU fR2Levels fR2Idx0 fR2Idx1 1 1 0 0 = true)
  · exact (rfl : blockU fR2Levels fR2Idx0 fR2Idx1 2 0 0 0 = true)
  · exact (rfl : blockU fR2Levels fR2Idx0 fR2Idx1 2 1 0 0 = true)
  · exact (rfl : blockU fR2Levels fR2Idx0 fR2Idx1 3 0 0 0 = true)
  · exact (rfl : blockU fR2Levels fR2Idx0 fR2Idx1 3 1 0 0 = true)
  · exact (rfl : blockU fR2Levels fR2Idx0 fR2Idx1 4 0 0 0 = true)
  · exact (rfl : blockU fR2Levels fR2Idx0 fR2Idx1 4 1 0 0 = true)
  · exact (rfl : blockU fR2Levels fR2Idx0 fR2Idx1 5 0 0 0 = true)
  · exact (rfl : blockU fR2Levels fR2Idx0 fR2Idx1 5 1 0 0 = true)
  · exact (rfl : blockU fR2Levels fR2Idx0 fR2Idx1 6 0 0 0 = true)
  · exact (rfl : blockU fR2Levels fR2Idx0 fR2Idx1 6 1 0 0 = true)
  · exact (rfl : blockU fR2Levels fR2Idx0 fR2Idx1 7 0 0 0 = true)
  · exact (rfl : blockU fR2Levels fR2Idx0 fR2Idx1 7 1 0 0 = true)
  · exact (rfl : blockU fR2Levels fR2Idx0 fR2Idx1 8 0 0 0 = true)
  · exact (rfl : blockU fR2Levels fR2Idx0 fR2Idx1 8 1 0 0 = true)
  · exact (rfl : blockU fR2Levels fR2Idx0 fR2Idx1 9 0 0 0 = true)
  · exact T2_a28
  · exact (rfl : blockU fR2Levels fR2Idx0 fR2Idx1 10 0 0 0 = true)
  · exact T2_a31
  · exact (rfl : blockU fR2Levels fR2Idx0 fR2Idx1 11 0 0 0 = true)
  · exact T2_a34
  · exact (rfl : blockU fR2Levels fR2Idx0 fR2Idx1 12 0 0 0 = true)
  · exact T2_a37
  · exact (rfl : blockU fR2Levels fR2Idx0 fR2Idx1 13 0 0 0 = true)
  · exact T2_a40
def fR3L40F (i : Nat) : Nat := 0x10ffe00
def fR3L40 : PackingT := (1,1,7,4,fR3L40F)
def fR3Levels : Nat → PackingT
  | 40 => fR3L40
  | _ => emptyPackingT
def fR3Idx0 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def fR3Idx1 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
abbrev T3_bkT := blockU fR3Levels fR3Idx0 fR3Idx1
abbrev T3_bmT (k tm s a b : Nat) := @blockU_merge fR3Levels fR3Idx0 fR3Idx1 k tm s a b
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T3_c40_0 : T3_bkT 13 1 0 1=true := by
  apply cellsBlockU (ar:=10) (d:=0)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T3_a40 : T3_bkT 13 1 0 1 = true := T3_c40_0
theorem tablesfR3 : ∀ k ≤ 13, ∀ tmax ≤ 1, blockU fR3Levels fR3Idx0 fR3Idx1 k tmax 0 (fR3Levels (3*k+tmax)).1 = true := by
  intro k hk tmax ht
  interval_cases k <;> interval_cases tmax
  · exact (rfl : blockU fR3Levels fR3Idx0 fR3Idx1 0 0 0 0 = true)
  · exact (rfl : blockU fR3Levels fR3Idx0 fR3Idx1 0 1 0 0 = true)
  · exact (rfl : blockU fR3Levels fR3Idx0 fR3Idx1 1 0 0 0 = true)
  · exact (rfl : blockU fR3Levels fR3Idx0 fR3Idx1 1 1 0 0 = true)
  · exact (rfl : blockU fR3Levels fR3Idx0 fR3Idx1 2 0 0 0 = true)
  · exact (rfl : blockU fR3Levels fR3Idx0 fR3Idx1 2 1 0 0 = true)
  · exact (rfl : blockU fR3Levels fR3Idx0 fR3Idx1 3 0 0 0 = true)
  · exact (rfl : blockU fR3Levels fR3Idx0 fR3Idx1 3 1 0 0 = true)
  · exact (rfl : blockU fR3Levels fR3Idx0 fR3Idx1 4 0 0 0 = true)
  · exact (rfl : blockU fR3Levels fR3Idx0 fR3Idx1 4 1 0 0 = true)
  · exact (rfl : blockU fR3Levels fR3Idx0 fR3Idx1 5 0 0 0 = true)
  · exact (rfl : blockU fR3Levels fR3Idx0 fR3Idx1 5 1 0 0 = true)
  · exact (rfl : blockU fR3Levels fR3Idx0 fR3Idx1 6 0 0 0 = true)
  · exact (rfl : blockU fR3Levels fR3Idx0 fR3Idx1 6 1 0 0 = true)
  · exact (rfl : blockU fR3Levels fR3Idx0 fR3Idx1 7 0 0 0 = true)
  · exact (rfl : blockU fR3Levels fR3Idx0 fR3Idx1 7 1 0 0 = true)
  · exact (rfl : blockU fR3Levels fR3Idx0 fR3Idx1 8 0 0 0 = true)
  · exact (rfl : blockU fR3Levels fR3Idx0 fR3Idx1 8 1 0 0 = true)
  · exact (rfl : blockU fR3Levels fR3Idx0 fR3Idx1 9 0 0 0 = true)
  · exact (rfl : blockU fR3Levels fR3Idx0 fR3Idx1 9 1 0 0 = true)
  · exact (rfl : blockU fR3Levels fR3Idx0 fR3Idx1 10 0 0 0 = true)
  · exact (rfl : blockU fR3Levels fR3Idx0 fR3Idx1 10 1 0 0 = true)
  · exact (rfl : blockU fR3Levels fR3Idx0 fR3Idx1 11 0 0 0 = true)
  · exact (rfl : blockU fR3Levels fR3Idx0 fR3Idx1 11 1 0 0 = true)
  · exact (rfl : blockU fR3Levels fR3Idx0 fR3Idx1 12 0 0 0 = true)
  · exact (rfl : blockU fR3Levels fR3Idx0 fR3Idx1 12 1 0 0 = true)
  · exact (rfl : blockU fR3Levels fR3Idx0 fR3Idx1 13 0 0 0 = true)
  · exact T3_a40
def fR4L24F (i : Nat) : Nat := 0x76c96d152604a960951
def fR4L24 : PackingT := (1,6,7,3,fR4L24F)
def fR4L27F (i : Nat) : Nat := 0x5a286ca4202c01a05c3000b006880f8af6c2003a6003405860b6a57c775a5538332e0500c7bdb464aaa4c151cfb5b4606aa4c15187fccb6a19348151e7f0a96053048151ff61526053048151fb658260d5244151c7bda96d0a960951dbb5b4604a960951fb6552604a960951fb6552605824c151ff61524418348151
def fR4L27 : PackingT := (11,5,7,8,fR4L27F)
def fR4H0_27F (i : Nat) : Nat := 0x100004
def fR4H0_27 (h : Nat) : Option (Nat × Nat) := lookupWord 1 3 2 9 1 4 fR4H0_27F h
def fR4L28F (i : Nat) : Nat := 0x1804101601400d1e4006200380419800e40062003d001a07766554433221100eb658254aaa60551f749935493048151bf62cc5492044151ef6152482aa44151f3658254981a6551f7615248110a6551d3e4b96058088951fb61816015088951fb61825498180151
def fR4L28 : PackingT := (9,5,7,8,fR4L28F)
def fR4L30F (i : Nat) : Nat := 0x38018bdb040380326e300601d9b0f14840082d100100e200e004401c0088180401949d300049a6006880180168a3652100209d9b498201601a0b8602243336182e01a2c00130d80040c00131d800580020b40188038031007024231c102400c400406880080d13c576c2e041058023202c36100081028a4db4c00e0007d30034170c0086248a30101911ba0243203d001d0004009151ea2a42e83d00df43cd764e89b8b56660c8177ac9546a213c25d4b092116a1d40479ce61bc342618b59502804ec850b81241b00d00a00a0027fed9d54c92a39ff2e9984c951affd76cc264a8e7fd98aa932546ffb5da64c0aa35ff6e13264151affd7699320a8e7fd82aa9905473fe99554c82a39ff2e9924c151affd76c9260a8ff7552605305473fec9554982a3bfd606aa4c151cffb30d1a40a8e7fda864d20547bfccc260902a3ffc6053048151bfed76c1a20a8fbf58360910547fbac1aa4882a37fd6e13244151ffcb0499220a8dff6bb4c910546bff5db054caa35ff6e132a6551cffb5099532a8f7ed824ca99546bff5da654caa39ff609a0a6551cffa64d0532a8e7fda92a582546fdeda152c12a3efd604a960951aff972d0304a8d7fdb960930547dfac0b04982a39ff6a58348151cff952c1a40a8f7ed9260d20547fb6a9306902a3ffc4418348151
def fR4L30 : PackingT := (42,4,7,11,fR4L30F)
def fR4H0_30F (i : Nat) : Nat := 0x1c0d802400017208a2c01720501520601601740ea2601601600ae12c101000e0
def fR4H0_30 (h : Nat) : Option (Nat × Nat) := lookupWord 5 19 5 12 4 4 fR4H0_30F h
def fR4L31F (i : Nat) : Nat := (if i<1 then 0x3003c00e86e05a01409c0c00600418c0000f385f08a0d80c0012e80086443202394f98900003812017729f3003781140b00db1de63e2f023680080a053009effc5f6da00ef7fe2e80f6c4d00105a0b1018e40044005c70601060107948407729f300078116c006c006c004c004a4e801680082400640041a002050010137d0020480093690022001248c92990052012005200320022002025320040d001231a004050010000c002066c1652103000b000801a0025274008a2936d00328ba00457f400b400740040068a165210336081948400015805e1803082dc0402c057c5f6de63c7780682f0100b40580afbff17db798f1cab18ae7a489f69a499496e8f08e08d085d84d81c7e07d075d70b6cf6bf6626265df5cf57d54c53c5165064f64e64d64c64b647a46a45a44a43a41f40f40a3fa3ea3e53d53d03c03bb3a039b38b3703343193092f92e92e42c92c42b429929428427f27a27526526025024023b22b21b2162112011e61c01a518a17a16a16516015014013b12b12611611110c107073000cfeb6355326a8c7fdb0aa9935463fedc554c92a397f6deaa649518ffb6755324a8e7edb2aa9925463fed8554c92a31ffaeda960951d7eb0555302a8ef7552aa9815463ff5db52982a35f7aed934c151efab26c0a60a8cfbdb4aa9305473eec9d54982a31ffaeda9481518ffb6654a40a8c7fdba64d20546fb75daa4902a39fe2a53048151efb32698240a8ff69524c1205467fb5db50882a3bdd6a15244151fecb04a9220a8df76bb54910547ff0c9240882a3bdd54aaa44151dfe24155220a8e7f5a3606995479fac13034caa3ddd54981a6551afed76c0d32a8e7f9a04c299547bb6a92414caa35fd6e110a6551eeeaa488532a8f7f12044299546bef5db2519aa3fd5549818cd51bfad76c0c66a8d7debb64233547faaa922119aa37f5aed108cd51afbb654cc66a8f7d581a6633546beed853319aa3df5442998cd51afdd76cc444a8dfe6bb60622546bf75db21112a35fb6e58088951afd972c0444a8f3ed9860222547df2c0b01112a3fd96055088951fed300a8444a8df6ebb54222546ff2dc221112a37f9aed1088951afdb714cc44a8d7edb3a6622547bf2c0d33112a35fb6c29988951eedaa14cc44a8f7e510a66225479f6c8511112a3ef94428888951e7dd3344444a8f7cd988ce22547fe2c0c67112a3df36423388951fe9aa119c44a8ffc5108ce22547be74cc67112a3ef3a223388951aff576c9c00a8d7fabb64a00546bfcdcb05002a35fe6e53280151efe326c0c00a8fbf18260600547fb8a9303002a37fcaed8180151efe3034cc00a8f7d9928ce00547fe8c0c67002a3df6a663380151efd33111400a8f7e99388a00547ff0c0c45002a3dfaa662280151f7d51111400a8ffca3388a00547db2c12a4c0aa3fd85492044151 else 0x604101a01800b8027c508bed81b729f300600780ed0dc08008007bee061827cc01301be03811c0980fd0dc080080071c7e04101a005c00f6f84906fca7cc00f007a1800800e04b804180410c7f17db024033a3803801e05a015a003edaeff9801a4021edb477c505c590010c8127db00cf)
def fR4L31 : PackingT := (96,4,7,12,fR4L31F)
def fR4H0_31F (i : Nat) : Nat := 0xd00f05f07902b0a51a00b00bd19e01809b061450
def fR4H0_31 (h : Nat) : Option (Nat × Nat) := lookupWord 4 12 4 12 4 4 fR4H0_31F h
def fR4H1_31F (i : Nat) : Nat := 0x25c08c1e49ec5f48c02615c0264c402402481a401010024024024c04024025414025c6398344402400d99142002420018a1
def fR4H1_31 (h : Nat) : Option (Nat × Nat) := lookupWord 6 31 5 12 4 4 fR4H1_31F h
def fR4L33F (i : Nat) : Nat := 0x715b602c0a2002e02c6c1924e2886501c1219240185adb102701c126608168d6050c030b445105ae2d3006d00171ca288a98238660ba00385c0685a30b6021ae29028a0185b01452485e127bdd66cd8656536474d221c640b400fff6a582547ffca960951fff68182547ffda94c951fff6a132547ffd984c951fff68132547ffd8264151fff4c990547ffd924c151fff60930547ffd8348151fff60a99547ffd32a6551
def fR4L33 : PackingT := (14,3,7,10,fR4L33F)
def fR4H0_33F (i : Nat) : Nat := 0x18914410055601f80e602005480088120150054c00000a022f8050050054804280c0150054330000
def fR4H0_33 (h : Nat) : Option (Nat × Nat) := lookupWord 5 21 5 14 6 4 fR4H0_33F h
def fR4L34F (i : Nat) : Nat := (if i<1 then 0x31401866f7fc5edb9863b860b51eff8bdb731c730c169c2dca52977fc5ed902e61016e53eff8bdb731c770d81300a0b7c5ed902e6180351cafa01e2f6d94f30c36049a39dff17b6ca798351cafa0de2f6d94f31813009f17b6ca798600b472be836528078bdb7318126864390077fc5edb29e63024bbfe2f6d94f305a195f43bc5edb29e630260134378bdb731813006f17b6ca798600b432be876528078bdb7318125dfa1b0ec03c5edb29e63024b1d436bf8078bdb653cc6049a015f41bc5edb29e618ec093402be8778bdb653cc30d81268077fc5edb29e60cafa1c16a0d94f8bdb73181258ea035fc1bc5edb29e63024b0d406bf8778bdb653cc604999ae6209706530927e4188f0e36e8c8e29288f61de86260e4819e01c7f45f727c75ea0792dde275bdd24733dc7a6f2db086aa5a4067fd964639d8a660f57e85e4d7665c956bc59c5612571d56854754c8517d3f64e5d32e4c05234459d0d6422d068413d02c4024ff03f5cfbe3ebcf823d7cf463c8cf0a3bc4e74378cd7a34bccbc3124c082e7cb2c2b0ca5a277496a242c88e206c7da1e1473a1b9467c18ec5dc166c53c14144a6111c4100ec43700ce42da09ec21c06f415e04740be017c000bffaa9935477fda064d51dffaa9935477fd9864951dff64d92546ffeaa64951dff6a1925477fda364951dff681925477feaa64951bff6a5825477fda94c951bff6a5325477fd984c951bffaa932547ff5a360551ffd64d81547ff5a260551ffd64981547ff53260551ffd681815477fd9364151dff64990547ff58164151dff68d905477fda264151dff609905477fd3264151dff6a530546ffda94c151ff764d305477fd924c151ffd60530546ffeaa4c151bff6a520546ffda348151dff64d20547fed9248151ffe4c120547ff5a844151ffd66110547ff5a344151ffd64d10547ff58344151ffd68910547ff59244151ffd60910547ff53244151dff64e995477fd92a6551ffd606995477fd82a6551dff4ca995477fd30a6551dff48299547fdd928cd51ff764233547fde998cd51ffb66222547fed9388951ffb60e22547fed9088951ffb60222547fed3088951ffba6622547ff99380151ffe64a00547ff98280151ffe4ca005467feaa64d519ffaa9925467fda9609519ff2a582547bf58260551fdd54981546ff6aa605519ffaa9905467fda94c151df764d305467fda9481519ff2a520547f6d5248151bfd6a110547f755244151ffc48110546ff6aa441519ff68e995467fda2a6551dfd606995467fda0a6551dfd442995477dd928cd51ff5606335477dd908cd51ff5442335477de998cd51dfb66222547fe58188951dfb64222547f6d5088951ff9442225477ee9988951efba2222547fce3388951dfe64e005477f99280151ffc606005477fa9980151ff68ce00547fea2280151 else 0x6bf7fc5ed8110ab98a3831034035fbfe2f6dcc014c0006718fdff17b6047980b4310353431bee2d8adb56c153314c31d4710c06806ea19dfb7dc5b15b6ad82a66298238860340370d7ef8b3e2f6c04855cc71d4305e06806d77fc5edb98e3b8001c0347bfe2f6dcc31dc000e01a3dff17b6e638e6000338d7ef8b3e2f6c04f3009f1c1685e06f0003badff17b60ab98e380d00d0afa8a9b2304901f8170003a7dff17b60ab98a380d00d00180e0965314f6d4701de2d0c033bfcc6048050100b4dfd7c29edb98c63c524880c03026652e2a52cc76c068067b7fc5edb986380d00cf94b8a94b30c730ddb01a01a62937dc5ed9986380d00d03000616e5294f6cc778b6fb0dcc300cf1729e638e02bb66000343bee2b6c16b314c11c0550001a9df715b60b598a618ea3886a0003585bdb5314701540006777dc56d82de618ee180143bee2b6c16f31c730c00a0070042d77fc5e6218638668398601bb6ca702a0080880e0085a093bf2ff6d1b65294b1c0778ac300dcc60540101357d454d8a2e600fe1b0200526f98a5b05a157314701540006a0b42ca002ee600d300600820afdbfdb56d4701d94f8b81730c3500f1802df16c5ed80da3b29a19dfa0398605bdb145e2c001718df314b60b42ae638ea1a8000d4169bfdb31d43731e285c80215fedb29e63c56380d405a1605c0693b663a86e63c50b8ce2a53db330c700815d0005006a7159863bb6a000a00ceefb8a94f6ccc0574001401a5df71598eda8002803380616bbfe2f3194b0ddb5009ed80c6182ba020200ceefb8acc31ddb30d40006800c2d77fc5e618eca7b6a0186500616bbf94a53e2f31db500c3280e77dc56d9980b40d00e80480cefb8adb330c705a06807402802ed82d03480385a018c2eff8bcc430c70cd0730c0376d94e041730100405401c2d00c1277e5feda36ca58e03bc561806e63020b98080202a05a083bf2fb8b22b6d1b01dcc30d0305cc0382d02006e602e035803b8ac3500360080120494d00377db6a006c7500258a8013004008800a44cc2004011024a6801b1d4009c561a80185b400912a004330da06fbfe2f6d94f314770d81700c1260904e581b7dff17b6ca798e3a86c0b8070076ff8bdb653cc71d43605c02819f17b6e6065a182d38c2168d80578bdb653cc71cc3700b1806b5600ab7fc5edb98e3986e0163b405e2f6d94f3060b7dff17b6ca798e3b86c0a8050cc00fbfe2f6d94f314770d81500b1980ff7fc5edb29e6386c0a805003eff8bdb653cc71d4360540283706408f7fc5edb29e638ea1b02a0180405a0581beff8bdb731c7605402c0377fc5edb29e638ee1a804c081780816015eff8bdb731c730d40302d0ac0c02bdff17b6ca798e3986585be2f6d94f)
def fR4L34 : PackingT := (110,3,7,14,fR4L34F)
def fR4H0_34F (i : Nat) : Nat := 0x706b025c13ec01980a45d00a840300a840b703802a515482000aa01c00a84239059c13607d057364244ef108c2400ab01b00abc052032c27d63ac12d05002ad04740fb037410607946100aa019e104059219f804005684b507745be09a044f0a7c2800a840000a9c1800a802a00a802a00abdd4b264c174170808d653421b01b4220c18c86022c18b141008504004802408000
def fR4H0_34 (h : Nat) : Option (Nat × Nat) := lookupWord 20 74 7 14 6 4 fR4H0_34F h
def fR4H1_34F (i : Nat) : Nat := 0x1d486d5191649128030189fd060a03403040c85135e00601078b0402001800307040c059872784c202ff07d210d05d8822f0a642f789ea0848427011342613119078143cc05f05400c14a180300060311f283c030503d971c3640c5981a500c001800305d5e4092a229c2800604105a17b92f14a92296018202b9897e0704114030234700c001800306856803d407d82d08d600c0018105af04f995561728d48060d12b2010c04b8df551e4030c0c60329185952c466b034129c631b42681ac903ac843811f00514a68242c65b8596159e0a8054d83ff04c001f80e2847c14de529c430254900460495e0c016f183e514c2fd2df202b405d01b214f2391a28949d009c601ea04e856803bd053e00c445f828803601810656a4b30aac0ad012883a00c0e02b825b821c35760dd05e094ce062e0cf4698060d10ec239c00205200c08280855806090340180412385800c1a28c0306039c09452b28138051f05a269fc276006c084e066c2410af505de339e258035218fc02202dc014101c944e8089846a082c2a0eaa705d614e0180444face0007030401320100001422000a060302300007020105040c00031017060104110700050e040d01260b12000000060d022310030512130010040000000f03
def fR4H1_34 (h : Nat) : Option (Nat × Nat) := lookupWord 62 214 8 15 7 4 fR4H1_34F h
def fR4L37F (i : Nat) : Nat := 0xda0d01f7f8bb694e611d868160186d01f7f8bb694e631c868160166116b7f8bb694e631c868160162d0924bbfc5db4a7308e4340b00c16f7f8bb694e631d8681201422172885bdfe2eda53984761a048068205a2e06f7f8bb694e631c8681201a0214f7f8bb6cc63b0c2d4f7f8bb694e611d86816013dfe2eda5398c721a058049d9bfc5db4a7318ec360122deff176d29cc63b0d0240285bdfe2eda5398c761900916ca7bfc5db6631d868160148eeff176d29cc61a05804a1bbfc5db4a7318e8160128016f7f8bb694e631d86812b05da3a7732a35bf16eec8565a7543e700b510b16a17c007ff64d51ffec92a3ffd82547ffa64a8fff64151ffe982a3ffd20547ffd32a8dff64d51bfec92a3ff581546ffb20a8ffd44151bff4caa3fde33547fdc44a8ffe80151
def fR4L37 : PackingT := (17,2,7,11,fR4L37F)
def fR4H0_37F (i : Nat) : Nat := 0xe00e20000ec0900e70500ec0760890de03318d0480be10212315c14f6bc0c00a66600ec0100e10600e00e30200e86100e0c90001801c0
def fR4H0_37 (h : Nat) : Option (Nat × Nat) := lookupWord 8 33 6 12 4 4 fR4H0_37F h
def fR4H1_37F (i : Nat) : Nat := 0x70b1c030a01bc2a1047015e607c037744ab187203e012b83d2173c0a2800503940b140ab0302b2a70838126017b8524041213800db81c110d42ee86eb080f1a56067e8fb8d61675c2db1a9d08d00dda03986390484099e2b92b62883c0454040c55a0072046e1a8802e03fc012017b86150448095a16c05bc096b06c205b866888f00100326434002b00dd022a058189a00dc43850a3f14ae2919414c2a8833d0a760e100a006b40a16efe04e003a508a804c164809160d9c1b5465608831a82079c2e680b917828808203b6370348028016e059b43f009144f785d10cb222c102d017235e82ffc1d886620b542cf454d895d04cc189414982ea006e03341a184fc042400981e30d72059e10b02b006111c0c1a4c2b9d203337e24b067389b419601ba474d0354108a046c526093d0cf417dca4db3fa18a00ca4324001108d60c7031806e209b409dca5806e503a2011c9be012a0a2d2bf01ba043707de0570569a6c109782c8806e8300b00000b310b0372170010016b010a00070b0d0526010f090426141c1506a21900012c3c031c000c0900001b2c3a01170085010d13000508050036000003
def fR4H1_37 (h : Nat) : Option (Nat × Nat) := lookupWord 62 193 8 15 7 4 fR4H1_37F h
def fR4L40F (i : Nat) : Nat := 0xdfc5b629988e860280480ffd51
def fR4L40 : PackingT := (1,1,7,7,fR4L40F)
def fR4H1_40F (i : Nat) : Nat := 0x11008f8100238036108044022011105a83402201100880440220110088044023426b078047454011200b01f41c6069060044022011008a014022011008f841c5e011d1200468104275010044023a2dd051025c00011000000001000
def fR4H1_40 (h : Nat) : Option (Nat × Nat) := lookupWord 8 53 6 13 5 4 fR4H1_40F h
def fR4Levels : Nat → PackingT
  | 24 => fR4L24
  | 27 => fR4L27
  | 28 => fR4L28
  | 30 => fR4L30
  | 31 => fR4L31
  | 33 => fR4L33
  | 34 => fR4L34
  | 37 => fR4L37
  | 40 => fR4L40
  | _ => emptyPackingT
def fR4Idx0 : Nat → Nat → Option (Nat × Nat)
  | 27 => fR4H0_27
  | 30 => fR4H0_30
  | 31 => fR4H0_31
  | 33 => fR4H0_33
  | 34 => fR4H0_34
  | 37 => fR4H0_37
  | _ => fun _ => none
def fR4Idx1 : Nat → Nat → Option (Nat × Nat)
  | 31 => fR4H1_31
  | 34 => fR4H1_34
  | 37 => fR4H1_37
  | 40 => fR4H1_40
  | _ => fun _ => none
abbrev T4_bkT := blockU fR4Levels fR4Idx0 fR4Idx1
abbrev T4_bmT (k tm s a b : Nat) := @blockU_merge fR4Levels fR4Idx0 fR4Idx1 k tm s a b
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T4_c24_0 : T4_bkT 8 0 0 1=true := by
  apply cellsBlockU (ar:=9) (d:=0)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T4_a24 : T4_bkT 8 0 0 1 = true := T4_c24_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T4_c27_0 : T4_bkT 9 0 0 11=true := by
  apply cellsBlockU (ar:=10) (d:=0)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T4_a27 : T4_bkT 9 0 0 11 = true := T4_c27_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T4_c28_0 : T4_bkT 9 1 0 9=true := by
  apply cellsBlockU (ar:=9) (d:=0)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T4_a28 : T4_bkT 9 1 0 9 = true := T4_c28_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T4_c30_0 : T4_bkT 10 0 0 42=true := by
  apply cellsBlockU (ar:=11) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T4_a30 : T4_bkT 10 0 0 42 = true := T4_c30_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T4_c31_0 : T4_bkT 10 1 0 2=true := by
  apply cellsBlockU (ar:=9) (d:=0)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T4_c31_2 : T4_bkT 10 1 2 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T4_c31_50 : T4_bkT 10 1 50 46=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T4_a31 : T4_bkT 10 1 0 96 = true := (T4_bmT 10 1 0 2 94 T4_c31_0 (T4_bmT 10 1 2 48 46 T4_c31_2 T4_c31_50))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T4_c33_0 : T4_bkT 11 0 0 14=true := by
  apply cellsBlockU (ar:=12) (d:=1)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T4_a33 : T4_bkT 11 0 0 14 = true := T4_c33_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T4_c34_0 : T4_bkT 11 1 0 41=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T4_c34_41 : T4_bkT 11 1 41 48=true := by
  apply cellsBlockU (ar:=11) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T4_c34_89 : T4_bkT 11 1 89 21=true := by
  apply cellsBlockU (ar:=11) (d:=1)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T4_a34 : T4_bkT 11 1 0 110 = true := (T4_bmT 11 1 0 41 69 T4_c34_0 (T4_bmT 11 1 41 48 21 T4_c34_41 T4_c34_89))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T4_c37_0 : T4_bkT 12 1 0 9=true := by
  apply cellsBlockU (ar:=10) (d:=0)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T4_c37_9 : T4_bkT 12 1 9 8=true := by
  apply cellsBlockU (ar:=11) (d:=0)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T4_a37 : T4_bkT 12 1 0 17 = true := (T4_bmT 12 1 0 9 8 T4_c37_0 T4_c37_9)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T4_c40_0 : T4_bkT 13 1 0 1=true := by
  apply cellsBlockU (ar:=10) (d:=0)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T4_a40 : T4_bkT 13 1 0 1 = true := T4_c40_0
theorem tablesfR4 : ∀ k ≤ 13, ∀ tmax ≤ 1, blockU fR4Levels fR4Idx0 fR4Idx1 k tmax 0 (fR4Levels (3*k+tmax)).1 = true := by
  intro k hk tmax ht
  interval_cases k <;> interval_cases tmax
  · exact (rfl : blockU fR4Levels fR4Idx0 fR4Idx1 0 0 0 0 = true)
  · exact (rfl : blockU fR4Levels fR4Idx0 fR4Idx1 0 1 0 0 = true)
  · exact (rfl : blockU fR4Levels fR4Idx0 fR4Idx1 1 0 0 0 = true)
  · exact (rfl : blockU fR4Levels fR4Idx0 fR4Idx1 1 1 0 0 = true)
  · exact (rfl : blockU fR4Levels fR4Idx0 fR4Idx1 2 0 0 0 = true)
  · exact (rfl : blockU fR4Levels fR4Idx0 fR4Idx1 2 1 0 0 = true)
  · exact (rfl : blockU fR4Levels fR4Idx0 fR4Idx1 3 0 0 0 = true)
  · exact (rfl : blockU fR4Levels fR4Idx0 fR4Idx1 3 1 0 0 = true)
  · exact (rfl : blockU fR4Levels fR4Idx0 fR4Idx1 4 0 0 0 = true)
  · exact (rfl : blockU fR4Levels fR4Idx0 fR4Idx1 4 1 0 0 = true)
  · exact (rfl : blockU fR4Levels fR4Idx0 fR4Idx1 5 0 0 0 = true)
  · exact (rfl : blockU fR4Levels fR4Idx0 fR4Idx1 5 1 0 0 = true)
  · exact (rfl : blockU fR4Levels fR4Idx0 fR4Idx1 6 0 0 0 = true)
  · exact (rfl : blockU fR4Levels fR4Idx0 fR4Idx1 6 1 0 0 = true)
  · exact (rfl : blockU fR4Levels fR4Idx0 fR4Idx1 7 0 0 0 = true)
  · exact (rfl : blockU fR4Levels fR4Idx0 fR4Idx1 7 1 0 0 = true)
  · exact T4_a24
  · exact (rfl : blockU fR4Levels fR4Idx0 fR4Idx1 8 1 0 0 = true)
  · exact T4_a27
  · exact T4_a28
  · exact T4_a30
  · exact T4_a31
  · exact T4_a33
  · exact T4_a34
  · exact (rfl : blockU fR4Levels fR4Idx0 fR4Idx1 12 0 0 0 = true)
  · exact T4_a37
  · exact (rfl : blockU fR4Levels fR4Idx0 fR4Idx1 13 0 0 0 = true)
  · exact T4_a40
def fR5L28F (i : Nat) : Nat := 0x61005041e020f00820b800400b80040f000f0083c020800882e01080000000000000000000000000000000000000bd5a2ad519fcb6511688c31f4f571b457eba5aa59228c43a08fa78399b8d2642f968aa5025918823c1b8c85a28118783214078280a0087ecedd98d1946a8c0185f8c92ddb4689518030df192db348512a30043fa76ecc688a254600c7b4a9196d1b04a8c011ef0db718a260551802f6c3a45ab04c0aa3005ed8748956098154600bdb0ea964c1302a8c017b61d82895260551802f6c3b0492a4c0aa3007ad8369825498154600bdb06cb04a9302a8c01fa60b66095260551803d6c346c12a4c0aa3005ed8b75825498154600edb0c12a55db02a8c019e70cb595625c551803d6c304a9303552a3007b1c5d9655c6aa54600f6b0b92a4b8d54a8c012cf9d7b31a299951803f4c304a9303332a3007f185c9525c66654600b27c6cb493bccca8c012cf8dc68a77999518025b73af66345222a3007ec8609526064454600fe18bb2cab8c88a8c01fd217254971911518025d71b8d44cd222a3004b7675ecc68a3354600fda0c12a4c0c66a8c01fc5176595718cd51803fa82e4a92e319aa3004bb6371a899a33546009774eb598d4444a8c01fa61865958188951802c7d1b2d2511112a300597a365a49de225460097746e35133444a8c0166e8d969266889518025be3af6634508aa30058fc365a4a221154600b2f86cb493bc22a8c012df0dc68a7784551802cee1b2d24ab08aa30059f8365a488a1154600
def fR5L28 : PackingT := (48,6,7,9,fR5L28F)
def fR5L31F (i : Nat) : Nat := (if i<5 then (if i<2 then (if i<1 then 0xaff1c82a61154600aff1c72a61154600aff1c32a61154600aff1c22a61154600aff0c96a21154600aff2cc6a21154600aff1ca2621154600ebf1a82621154600bfb1c42621154600aff0c969e1154600aff1ca61e1154600edf1a761e1154600bf71c22561154600b7f0c96921154600cff0cb68e1154600aff0c968e1154600aff2cc68e1154600aff1ca24e1154600efd1a324e1154600aff1ca60e1154600aff1ca20e1154600bdf1c720e1154600bef1c620e1154600bf71c520e1154600bfb1c420e1154600bfe1c220e1154600aff1ca5ce11546009ff0cb54e1154600aff0c968a1154600edf0c768a1154600aff2cc68a1154600aff1ca24a1154600bf71c524a1154600bfb1c424a1154600efe1a224a1154600aff1ca60a1154600aff1ca20a1154600bf71c520a1154600aff1ca5ca1154600bf70c954a1154600df70b954a1154600fd70c754a1154600ef71a754a1154600ef71a354a1154600ff609254a1154600ff618254a1154600ff617254a1154600bf72cc54a1154600aff1ca4ca1154600aff1ca0ca1154600bbf1c80ca1154600bdf1c70ca1154600bef1c60ca1154600bf71c50ca1154600bfb1c40ca1154600ef7152aaa11546009ff0cba221154600ebf1a8a221154600dbf0cba221154600ebf0caa221154600dbf0b9a221154600ebf0a9a221154600ebf1a7a221154600fb7095a221154600ebf1a4a221154600ebf1a3a221154600ebf1a2a221154600fb7152a221154600ebf2aaa221154600ddf0b99de1154600edf0a99de1154600edf1a89de1154600edf1a49de1154600edf1a39de1154600edf1a29de1154600fd71529de1154600f9f2889de1154600ef71a49561154600ef71a39561154600ef71a29561154600efb1a89121154600efb1a79121154600efb1a39121154600efb1a29121154600ff31529121154600efb2aa9121154600fbb2889121154600fdb2779121154600ff32559121154600efd1a38ce1154600efd0ca8ce1154600dfd0b98ce1154600efd0a98ce1154600efd1a88ce1154600efd1a78ce1154600ff50958ce1154600efd1a28ce1154600ff51528ce1154600efd2aa8ce1154600fbd2888ce1154600fdd2778ce1154600ff52558ce1154600ff92448ce1154600efe1a288a1154600ff615288a1154600efe0ca88a1154600dfe0b988a1154600efe0a988a1154600efe1a888a1154600efe1a788a1154600ff60c588a1154600ff609588a1154600efe1a488a1154600efe1a388a1154600efe2aa88a1154600fbe28888a1154600fde27788a1154600ff625588a1154600ffa24488a1154600ffc23388a11546008df9c7aeda254600fb61825498154600fc71765957154600fd617254971546008ef8cb6a26654600a6f8c96926654600a7e8c96922254600a7f0c96921154600 else 0xbfe1c12622254600afe8c969e2254600afe8ca61e2254600afe8cb69a2254600afe8c969a2254600afeacc69a2254600afe9ca61a2254600bf69c62d62254600bf69c62562254600bf68cb5962254600bf68c95962254600ef69a85962254600fe69865962254600fe69765962254600bf6acc5962254600b7e8c96922254600afe8cb6922254600afe8ca6122254600afe9ca2ce2254600afe8c968e2254600afeacc68e2254600efc9a328e2254600afe9ca24e2254600efc9a324e2254600afe9ca60e2254600afe8ca60e2254600afe9ca20e2254600bde9c720e2254600bee9c620e2254600bf69c520e2254600bfa9c420e2254600bfe1c120e2254600afe9ca58e2254600afe8ca58e2254600bfe1c82462254600ff60b52462254600afe9ca6062254600bfe0c96062254600fbe0b86062254600fbe0a86062254600fbe0986062254600fee0c66062254600efe1a66062254600fbe1866062254600ff60c56062254600ff60b56062254600ff60956062254600ff61656062254600efe1a36062254600bfe2cc6062254600bfe0c95c62254600ff61655c62254600afe9ca4c62254600afe8cbaaa2254600afe8c9aaa2254600afe9c8aaa2254600afe9c6aaa2254600ef68b5aaa2254600ef6895aaa2254600ef6965aaa2254600afe9c3aaa2254600efe091aaa2254600efe181aaa2254600efe171aaa2254600afe8caa222254600ebe9a8a222254600fbe181a222254600ebe8baa222254600ebe8a9a222254600ebe9a6a222254600ebe9a4a222254600ebe9a3a222254600fbe0c1a222254600fbe091a222254600fbe171a222254600ebeaaaa222254600ede8a99de2254600ede9a89de2254600ede9a69de2254600fd69659de2254600ede9a49de2254600fde0919de2254600fde1819de2254600edeaaa9de2254600eee8ba99a2254600eee8a999a2254600eee9a899a2254600eee9a799a2254600fe68b599a2254600fe689599a2254600eee9a499a2254600eee9a399a2254600fee18199a2254600fee17199a2254600eeeaaa99a2254600faea8899a2254600fcea7799a2254600efa8ba9122254600efa9a89122254600efa9a79122254600efa9a69122254600ff28b59122254600ff29659122254600efa9a39122254600ffa1819122254600ffa1719122254600efaaaa9122254600fbaa889122254600fdaa779122254600feaa669122254600afe8ca8ce2254600efc8ca8ce2254600efc8ba8ce2254600efc8a98ce2254600efc9a88ce2254600efc9a78ce2254600efc9a68ce2254600ff48b58ce2254600ff48958ce2254600ff49658ce2254600ffc0918ce2254600ffc1818ce2254600ffc1718ce2254600efcaaa8ce2254600fbca888ce2254600fdca778ce2254600feca668ce2254600ff8a448ce2254600) else (if i<3 then 0xafd9ca2ca3354600bf59c52ca3354600afd8cb68a3354600afd8c968a3354600edd8c768a3354600afdacc68a3354600bed9c628a3354600bf99c428a3354600efc9a228a3354600afd9ca24a3354600bf59c524a3354600bf99c424a3354600efc9a224a3354600afd9ca60a3354600afd8ca60a3354600afd9ca20a3354600bfd1c120a3354600afd9ca5ca3354600afd9ca58a3354600afd8ca58a3354600eed9a658a3354600afd8ca50a3354600bfd1c82463354600bfd1c72463354600efd0ba6063354600bfd0c96063354600fbd0a86063354600fbd0986063354600fed0c66063354600efd1a66063354600fbd1866063354600ff50c56063354600ff50956063354600fbd1826063354600ff51526063354600bfd2cc6063354600bfd0c95c63354600bfd1c85c63354600fdd1875c63354600fdd1765c63354600ff51655c63354600efd1a25c63354600fdd1725c63354600ff51525c63354600bfd2cc5c63354600afd9ca4863354600afd8cbaaa3354600afd8c9aaa3354600afd9c6aaa3354600afd9c2aaa3354600efd091aaa3354600efd181aaa3354600efd171aaa3354600eed8ba99a3354600eed8a999a3354600eed9a899a3354600eed9a799a3354600fe589599a3354600eed9a299a3354600fe595299a3354600fed18199a3354600fed17199a3354600eedaaa99a3354600fcda7799a3354600ef99a69123354600ef99a29123354600ff91819123354600ff91719123354600ef9aaa9123354600fe9a6691233546008ff9c82ea22546008ff9c32ea2254600afe9c22a622546008ff8cb6a222546008ff8cb69a2254600bf69c225622546009f78cb59622546008ff8cb6922254600a7f8c969222546008ff8cb68e2254600afe8c968a2254600cfe8b968a2254600afe9ca60a2254600afe8ca60a2254600afe9ca58a2254600eee9a658a2254600fe696558a2254600bf68c954a2254600df68b954a2254600bf69c654a2254600ef69a354a2254600afe9ca4ca2254600ff61522462254600fbe1826062254600ff615260622546008ff8cbaaa2254600ef6952aaa2254600cef8ba99a2254600eee9a299a2254600fe695299a2254600cfb8ba9122254600efa9a29122254600ff29529122254600cfd8ba8ce2254600efc9a28ce2254600ff49528ce2254600afe9c82ea2254600afe9c62ea2254600afe9c32ea2254600afeacc2ea2254600afe8cb2a62254600afe9c82a62254600afe9c62a62254600afe9c32a62254600afeacc2a62254600afe9ca2e22254600bde9c72e22254600bfe1c12e22254600afe8cb6a22254600afe8c96a22254600eee8c66a22254600afeacc6a22254600ebe9a82a22254600bde9c72a22254600bfa9c42a22254600afe9ca2622254600ebe9a82622254600bfa9c42622254600 else (if i<4 then 0xee79a754a6654600ee79a354a6654600fe68a254a6654600fe689254a6654600fe698254a6654600fe697254a6654600be7acc54a6654600aef8ca50a6654600aef9ca4ca6654600aef8ca4ca6654600aef9ca0ca6654600baf9c80ca6654600bcf9c70ca6654600be79c50ca6654600beb9c40ca6654600bef1c10ca6654600def0cb6066654600bef0c96066654600fe70956066654600eef1a36066654600faf1826066654600fe71526066654600bef2cc6066654600bef0c95c66654600bef1c85c66654600fcf1875c66654600eef1a25c66654600fcf1725c66654600fe71525c66654600bef2cc5c66654600aef8c9aaa6654600aef9c8aaa6654600aef9c7aaa6654600ee7895aaa6654600aef9c3aaa6654600aef9c2aaa6654600ee7952aaa6654600eef181aaa6654600eef171aaa6654600ecf8a99de6654600ecf9a49de6654600ecf9a39de6654600ecf9a29de6654600fcf1819de6654600ecfaaa9de6654600afbacc69a4454600afb9ca5da4454600afbacc68e4454600afb9ca58e4454600afb8ca58e4454600edb8c768a4454600afbacc68a4454600beb9c628a4454600efa9a228a4454600afb9ca60a4454600afb8ca60a4454600afb9ca20a4454600bfb1c120a4454600afb9ca5ca4454600afb9ca58a4454600afb8ca58a4454600eeb9a658a4454600afb9ca4ca4454600afb8ca4ca4454600fbb0a86064454600feb0c66064454600efb1a66064454600fbb1866064454600ff30c56064454600efb1a36064454600fbb1826064454600ff31526064454600bfb2cc6064454600bfb1c85c64454600fdb1875c64454600fdb1765c64454600ff31655c64454600efb1a25c64454600fdb1725c64454600ff31525c64454600bfb2cc5c64454600afb9ca4864454600afb9c6aaa4454600afb9c3aaa4454600afb9c2aaa4454600efb181aaa4454600efb171aaa4454600eeb9a899a4454600eeb9a799a4454600eeb9a399a4454600eeb9a299a4454600fe395299a4454600feb18199a4454600feb17199a4454600eebaaa99a4454600fcba7799a44546008ff9c22ea33546009fb9c42e63354600c7f8b92a63354600afd9c32a633546008ff8cb69a3354600afd8c968e3354600cfd8b968e3354600afd9ca58e3354600afd8ca58e33546008ff8cb68a3354600afd9ca4ca3354600cff0ba6063354600efd1a360633546008ff8cbaaa3354600cef8ba99a3354600eed9a399a3354600bf99c42ea3354600afd9c62ea3354600ef99c42ea3354600afd9c22ea3354600afdacc2ea3354600bf99c42e63354600afd8cb2a63354600e7d8b92a63354600afd9c62a63354600afd9c22a63354600afdacc2a63354600afd8cb69a3354600afd8c969a3354600afdacc69a3354600afd9ca5da3354600b7d8c96923354600 else 0xbdf1c70c98154600bef1c60c98154600bf71c50c98154600bfb1c40c98154600bef1c6aed8154600def0b6aed81546009ff0c9aed8154600dbf0a8aed8154600dbf098aed8154600def1c6aed8154600dbf186aed8154600df7095aed8154600cff1a3aed8154600dbf182aed8154600df7152aed8154600a7f8c96917154600fd697254971546009ff1c82e571546009ff2cc2e571546009ff0c96e17154600bfb1c42a17154600aff1ca2617154600bfb1c42617154600bdf0c961d7154600df70b95957154600b7f0c96917154600aff1ca20d7154600bef1c620d7154600bf71c520d7154600bfb1c420d7154600bfe1c220d7154600aff2cc6897154600fd71655c971546009ff0cb5897154600fe71655897154600df70b95497154600bf71c65497154600ff618254971546009ff1c8aed7154600df7165aed71546008ff8c96e931546008ff9ca2e531546008ff9cb2a531546009f78cb5493154600cff1ba60531546009f79c5aed31546008ff8c96e921546008ff9ca2e521546008ff9cb2a521546008ff9cb6a12154600a7f8c969121546008ff9cb68d2154600a7f8c9692aa54600aef9c62ceaa54600aff1c12ceaa546008ff8cb58eaa54600af79c52caaa54600aff1c12caaa54600af79c524aaa54600afb9c424aaa546008ff8cb60aaa54600aff1c120aaa54600abf9c80caaa54600adf9c70caaa54600aef9c60caaa54600af79c50caaa54600afb9c40caaa54600aff1c10caaa54600aff1c8246aa54600aff1c7246aa54600aff0c9606aa54600ebf098606aa54600eef0c6606aa54600ebf186606aa54600ef70c5606aa54600ef7095606aa54600cff1b3606aa54600ebf182606aa54600ef7152606aa54600aff2cc606aa54600aff0c95c6aa54600aff1c85c6aa54600edf1875c6aa54600edf1765c6aa54600ef71655c6aa54600cff1b25c6aa54600edf1725c6aa54600ef71525c6aa54600aef9c82a66654600aef9c72a66654600aef9c32a66654600aef9c22a66654600aefacc2a666546009ef8cb6a26654600cef8cb6a26654600aef8c96a26654600aefacc6a26654600aef8c969e6654600aefacc69e6654600aef9ca61e6654600aef8ca61e6654600ecf9a761e6654600be79c22566654600b6f8c96926654600aef8ca6126654600aef8c968e6654600aefacc68e6654600eed9a328e6654600aef9ca24e6654600eed9a324e6654600aef9ca60e6654600aef8ca60e6654600aef9ca5ce6654600aef8ca5ce6654600aef8c968a6654600ecf8c768a6654600aefacc68a6654600beb9c428a6654600eee9a228a6654600aef9ca24a6654600be79c524a6654600beb9c424a6654600eee9a224a6654600aef9ca60a6654600aef8ca60a6654600aef9ca5ca6654600be78c954a6654600fc78c754a6654600))) else (if i<7 then (if i<6 then 0xa7f8c969172546008ff8c96e962546008ff9c82e962546008ff9c32e962546008ff9ca2e562546009f79c52e56254600cef8b96996254600a7f8c96916254600cef8ba58d62546009ff1c1aed625460097f8c96e942546008ff9c82e942546008ff9c32e942546008ff8c96e93254600cdf8c76e932546008ffacc6e932546008ff9c82e932546008ff9ca2e532546008ff9cb2a532546008ff9cb6a132546008ff8c96e832546008ffacc6e832546008ff9cb2a43254600cbf9ca6e03254600cbf8a96e03254600dbf1c16e032546009bfacc6e032546008ff9cb6a03254600cbf9b86a03254600cdf8a96dc3254600cdf9a86dc3254600cef8a96d83254600cef9a86d832546009efacc6d83254600cbf9b86983254600cdf9b769832546009f78c96d43254600cf78a96d43254600cf79a86d43254600cf79a66d432546009f7acc6d43254600cfb8a96d03254600cfb9a86d03254600cfb9a66d032546009ff0c96c43254600cff0a96c43254600cff1a86c43254600cff1a66c432546009ff2cc6c432546009ff2cc6e091546009ff1cb20c9154600aff1ca20c9154600bdf1c720c9154600bef1c620c9154600bf71c520c9154600bfb1c420c9154600bfe1c220c9154600dbf1b860891546009ff1cb2089154600bf71c520891546009ff1cb0c89154600aff1ca0c89154600bbf1c80c89154600bdf1c70c89154600bef1c60c89154600bf71c50c89154600bfb1c40c891546008ff9cb2a58154600a7f8c969181546009ef9c6aed81546009ff2cc2e58154600bbf1c22a18154600bbf1c22618154600aff0ca61d8154600def0b92d98154600def1b72d98154600bf71c22d58154600fe70b62558154600fb71862558154600bf71c22558154600b7f0c96918154600ebf0a86918154600def0b66cd8154600aff1ca2cd8154600ebf0a868d8154600cff0cb68d8154600ebf0c868d8154600ebf09868d8154600eef0b668d8154600ebf18668d8154600aff2cc68d8154600aff1ca24d8154600efd1a324d8154600faf18658d8154600def0b62c98154600bf71c52c98154600dfe1b22c98154600bbf1c82898154600bef1c62898154600bfb1c42898154600bbf1c82498154600bf71c52498154600bfb1c42498154600aff0ca6098154600ebf0ca6098154600bbf0c96098154600faf0b66098154600ebf1a66098154600fb70b56098154600fb70956098154600ebf1a36098154600fbe0b26098154600bbf2cc60981546009ff0cb5898154600bbf1c85898154600fbe1825898154600fbe1825498154600df70b95498154600fe70b65498154600ef71a35498154600ff60a25498154600ff60925498154600fb71825498154600ff61725498154600fbe1824c981546009ff1cb0c98154600aff1ca0c98154600bbf1c80c98154600 else 0xd543500d2c33a0cd43300cac31a0c543100c2c3060c042fc0bdc2f20b842d00b2c2c60b042b00aac2a60a842900a2c2860a04270097c25a095424408cc22e08a4224087c21a082420407fc1ee07a41e4074c1c206f41b806cc1ae06a4198061c18205f4178059c1620574158054c14e052414404fc13a04d4130044c0d202a4074012c02e00740008ffacc6cca954600cdf8c76c8a9546008ffacc6c8a9546008ff9c82e5a6546008ff9c32e5a6546008ff9c22e5a6546008ffacc2e5a6546008ff9c3aeda6546008ff9c2aeda6546008ff8c96e9765460097facc2e5a454600c7f8b9699a454600c7f8b95d9a45460097f8c96e96454600a7f8c9691a3546008ff9c22e5a3546008ffacc2e5a354600abf8c86d9a354600a7f8c96d1a354600aef9c62c9a354600afb9c42c9a354600cfe9b22c9a354600aff1c1aeda3546008ff8c9aeda354600cfd9c3aeda3546008ff9c2aeda354600cff1c1aeda3546008ff9c1aeda354600ef596568ca354600afdacc68ca3546008ffacc6e89354600afdacc68c93546008ff8c96e963546008ff9c82e963546008ff9c22e96354600cbfa882e963546008ff9ca2e563546008ff8cb69d63546008ff9caaed635460097f8c96e94354600a7f8c9691a2546009df9c7aeda2546008ff9c82e5a2546008ff9c32e5a2546008ffacc2e5a254600cbf9b82e1a254600cdf8b92dda254600cdf9b82dda254600cdf8b82dda254600cdf8b76d9a254600a7f8c96d1a254600cdf8b76d1a254600cdf8b76cda254600cfd9b32cda2546008ff9cb24da2546008ff8cb58da254600adf9c7aeda254600cdf8b7aeda2546008ff8c9aeda2546008ff9c8aeda254600cdf9c7aeda254600cf79c5aeda2546008ff9c3aeda254600cfe9c2aeda254600cff1c1aeda2546008ff9ca6e0a254600cef9a86d8a2546009efacc6d8a254600cfb9a86d0a254600cfb9a66d0a2546009fbacc6d0a254600a7f8c9690a254600cef9b6690a2546008ff9ca6cca254600cef9b668ca254600cfb9b468ca254600afeacc688a2546008ffacc6e892546008ff9cb6a09254600cf79a66d492546009f7acc6d49254600cfb9a86d09254600cfb9a66d092546009fbacc6d092546008ff9cb68c9254600cf79b568c9254600cfb9b468c9254600afeacc68892546008ff8c96e98254600cef8c66e982546008ffacc6e98254600afb9c42e982546008ff9c32e982546008ff9ca2e582546009fb9c42e582546008ff9cb2a582546008ff8cb69982546008ff8cb6918254600a7f8c969182546008ff8cb68d82546008ff9caaed82546008ff8c96e882546008ffacc6e882546008ff9cb2a48254600a7f8c969082546008ff9cb68c8254600cfd9b368c82546009ff0c96c48254600cff1a36c482546009ff2cc6c482546008ff8c96e97254600) else (if i<8 then 0xc066f75bb46ebdb9e6e35b886e0db5a6cc5b146c0daf26b85ad06b2daba6aa5a986a1da6a6935a30684d9f667659bc667d99a6655990662d98665d597065ad966658595064fd92e64a591863ed8de63058a4624d876616583c607d8025f957e05f0d7a65e257785d6d73e5ce57285c5d7065bd56f05b4d6b65a9569459dd64e58f5620583d5fe57e55dc575d5d257355bc56ad5a6565558455cd562554554054ed53654c552c549d5225475518544d50e54254f853cd4ee53754d8534d4ce53254c452cd4ae52a5498524d48e522548451cd46e51a545850ed42a5095420503d40a50154004fed3f64f953e04f3d3ca4f153c04eed3b64ec53ac4e6d3964e453744d8d35e4d653484cdd3264c8531c4c5d3124c352fc4bad2e64b852dc4b5d2c64b052b04a7d29a4a5528449fd27a49d5270497d24e48f523848cd22e48a5224487d21a482520447fd1fa47d51f047ad1e647851d0472d1c647051bc46ad1a6468519c465d19245d5164457d14e4525138446d10a43e50f443bd0de43350c8430d0b242b50a8428d092420507041ad05a4155050412d03a40d5024407d01a4055010402d0063fd4fe43f4cfc23ef4fb83e9cf963e14f803dbcf6a3d94f543d3cf3e3cb4f1c3c2cefa3ba4ee43b7ceda3b54ed03afceba3aa4e983a4ce8239f4e7839cce6e39a4e64394ce4238f4e3838cce2e38a4e24387ce1a3824e0437fcde23744dcc36ecdb63694d8835dcd663584d5c355cd523534d4834dcd263484d1c345cd123434d08340ccf23384cd0332ccba32d4cb032acc9a3254c90322cc863204c7c31dcc663184c5c315cc523104c30307cc0e3024c042ffcbee2f74bcc2f1cbc22e94b942e0cb722d84b5c2d2cb3a2ca4b182c4cb0e2bc4ae02b3cabe2ab4aa82a8ca922a04a7029aca662984a4428fca3a28a4a18284ca0227c49ec276c9ca26e49b426bc9aa2694994263c98a261498025ec96a2594960256c956254494c251c94224f4938249c922241490023ec8f623c48ec239c8e223748cc231c8b622c48ac229c896224488c221c88221f4878219c8622174858214c84220f482c206c816204480c1fec7f61fc47ec1f9c7d61f147c01eec7b61ec47ac1e6c7961e447801dec76a1d947601d6c7561d4474c1cec7361cc472c1c9c7161c147001bec6f61bc46ec1b9c6e21b446cc1b1c6b61ac46a01a6c6961a1468019ec67619c466c199c6621974658191c63618c462c189c622184460c181c60217c45ec176c5ca17145c016ec5b61694594163c58a15e457415bc56a1594554153c53e14b4528148c51e1464514140c4fe13e44e8138c4d213344c8130c4be12b449c125c4921234488120c47e11e4468118c45e1164448110c43e10b4428108c41e1064414100c3fe0fe43dc0f5c3c60f043bc0edc3a60e543840dfc37a0dd43700d7c35a0 else (if i<9 then 0x100088c20000000b7080a182000000000a0820005b9628888c20054304a18250c100000014304b142000005041014306b7c20016f8400000aa42d5212c50800000000298080000000003548400000b7c20000002c52b6104c04050c1016284a18a08450c12c508015be12df08005be1000055216a9096e84058a1000058a1004c8400000006c50b4105aa42d5210038083600158e08380820016f841c0412c50d0104b7c3c04142308000000a60200a10ac704058a100000000b14250410000000000282080058a56c20a1080a18202c5094314108a18250c100000002b7c25be100000000055216a9096e84058a1000058a10000000008461000006c50b4105aa42d5210000d8a16a90b5484000b6e02170104b143c041e020838083c04100a0f0104002c52b6111184b14210c1a8208005041086096284000064f0108006c50b41040d8a1682081b142d0412b608000015b0400000055210000000000000aa4200c92a91000000000015b0401b210000446100000000ad82000005041014704b7c20000ad82000015be12df08000000b7c20006c840192100000000a60200000d6c16a908000000006a90800d6c1034104006a90800000000001aa42d521000006b608000682081aa42d52100000223091184006b6080000341040d5216a908000000ad82001628401721000002b60816840000000015b0400004104002860800000020820016295b08010410001904128609430400000b1420000010410000d6c100000000006c50a410400035b040002410400036285ad82003628520820000002230800d6c1001b14290410000003628520820001ad8200000000000000364324405a1b21efe0180451dd0f70d918e406cf80601102dc7d12e0644797022230e5c1118ac6eb176c40b0bec1eb006bf0af7ebceaef6b7cadaeb5aad26b38ac6eb0aabb6adcab2eabaaaa6a8ca9bea6aa966a54a8dea32a8b6a1ca85ea06a7a69d8a74e9c2a6c69a0a63e972a586944a4ce922a47690ca3be8dea3368bca2ae89aa256878a19e84aa0b68109ffe7ee9fa67d89f4e7ce9ec67949e3e7729d8675c9cce7229c467009bbe6ea9b666bc9a7e69a99f666c999e65698e6628988e61297d65cc96ee5aa9666588957e54e94c6520940e4f293864d092fe4ae927648091be452913643c90ae41a8ff63ec8f6e3be8eb639c8e2e36e8d7634c8cee32a8c662fc8bae2da8af62948a0e272898624488ce21688461f4872e1ba867618c85be16a856614884de12683f60e0836e0ca82b609c822e07a814603480be02a80660087fddfe67f55fc47ecdfa27e45f807dbdf5e7d35f3c7cadf1a7c25eec7b3debe7ae5ea87a5de927a05e64797de4e78c5e20780ddf27755db8769dd967615d74755dd467505d24744dd027395cc8730dca67225c6c716dc3e7085c1c705d else 0x1a001d000864e800ac00360010c5b001580078083c04170008170156d00050019400c28321003080184316c0056001bb6e021001878083c0417c5080030108265c0040e020802d9808400680040e0010b6e0217010416001e020f010400c3b8a0062e02085b5800ac0036001038005edb8085c041e020801878083c0410062d800b808218bc0420c9e021064b800b8083c041070104000b6e02105e701080f6dc042e020832082640287c041e020f010780820d00085b6800821b400406b6d001680041a001086d001680040e0010dde02106485bf010f8083c041b000d80043142dac007c041099e02110c842678085c0417000f0106c0020141e02084370109c00210d40420380048642e0010b6e02170106c0021056002700090c878082152c0420030f01078082e001e020864f010b808360010c5b00106285b7010dc003c041b000b5b70109c002d52c042005b7010821aadb8086e0016b6e021380042f380840e020f0105c002e0010866b6e021843701080e0016b6e02170105c002e0010866b6a0218435010800d000e80074003a001d000e80074003a001d000e80074003a001d000e80074003a001d00085b5800b6d800c58041060106c00207000b54e0108160010b9b001580072a400c58041aa9c02106fe010b00838041c020b800637f00858041006fd800ac0038041882c02106c6010819538042ca9c021654e010ac0029536002ca9b001000e0018828dfc02186f87ae010c0e001c0208001041ef80430820b9c02187be010b0082e001c020e01040e001c020e0107008215380420d8c021654e010b2a7008595380424a9c021654e010b37f00840000000f708000000187008360010380072a7008418b6002ca9b001154b8009c00395200620c5c021654e01092a700859538042ca9c021002e7008410580420b9c021380042e700841b38042006c85c0036001b0008037e008400180427000d8004316c00418a16d80430030862e010800c3c0410047701080005800780820e020f01078083c041e020b0104000000000000001684006a9080000002dc20016284000002d820005b84b7caa445be))))
def fR5L31 : PackingT := (879,5,7,14,fR5L31F)
def fR5H1_31F (i : Nat) : Nat := 0x7064456312c001207f842e02c0309194810306003000c0416b04484a00c140f1034030414984800c302700c202000c003090b980560a6806a084859616e8259026415f0a340eb0aa42d00c301400c0c02808c030205d013804b42f607a004f17fc4340af81d608b468a06c462b19b000a0b14085030030211280700c0030506803000c1824302b84db09941c300c3910604081001c18308080030a003800010080
def fR5H1_31 (h : Nat) : Option (Nat × Nat) := lookupWord 22 81 7 14 6 4 fR5H1_31F h
def fR5L34F (i : Nat) : Nat := (if i<4 then (if i<2 then (if i<1 then 0x84551803ff841422a8c01ffc5ca1154600ffe2a508aa3007ff14284551803ff899422a8c01ffc0ca1154600ffe51108aa3007ff23384551803ff911422a8c013fe6d8a9546009ff36654aa3004ff9b22a5518027fd5d952a8c013fe2e5a6546009ff576d32a3004ff9ba5d951802bfc5cb48a8c013fe2e5a3546009ff576d1aa3006fd9a328d518027fcdd126a8c01bf668c93546009ff374b1aa3004ff8ba58d518027fc5cb44a8c01b7e2dda2546009ff576d12a3005ef9b628951802fdcda144a8c01bfa688a2546009ff374492a3005f79b524951802fdcda124a8c01bfa68892546009ff374c12a3004ff8ba609518027fcdd104a8c017fc6c482546009ff374b92a3004ff9ba589518027fc5d2c4a8c01bbe69962546009ff174a12a3004ff9ba4c9518027fc5d264a8c013fe6e83254600b7f370192a3005df9b70c951802f7cdb064a8c017de6d43254600bf7368192a3005ff1b10c951802ff8dc122a8c017fc6dc9154600bfe172c0aa3007bf0a860551803df84c302a8c01fbc2d98154600dfe34cc0aa3007bf18660551803fb85ab02a8c01fdc2558154600dfe346c0aa3007bf18260551803fb8a9302a8c017fcaed8154600bfe172b8aa3005ff1b85c551803ef8c3ae2a8c01f7c5d97154600fee2cab8aa3006ff1a25c551803ef8b92e2a8c01fdc5497154600bfe576b8aa3004ff9ba4c5518027fcdd242a8c013fe2e6aa546009ff36d552a3004ff9b3aa9518027fcd9554a8c01bfc246aa54600dfe303552a3006ff171aa95180377c54ccca8c01bbe6a26654600ddf34f332a3007e78959995180377cd24cca8c01bbe68e6654600ddf345332a3007e795299951803f78c0ccca8c01fbc5c66654600ddf555332a3007cfa77999518037dcd3488a8c01bee68e4454600df7345222a3007fb18191151803fd8b8c88a8c01beeaaa4454600fd74cd222a3004ff8ba8cd518037ecd1c66a8c01bf62ea3354600dfb15319aa3006fd9a68cd518037ecd1466a8c01ff42463354600ffa30319aa3007fd1718cd518037ed55466a8c01fb699a3354600ff348919aa3004ff8ba889518037f4d1444a8c01fda54a2254600dfd175112a3006fe8a9889518037f4d4444a8c01bfa69e2254600dfd34d112a3007f68b588951803fb44ac44a8c01fda5962254600dfd349112a3006fe9a388951803ff048c44a8c01ff86062254600ffc2e3112a3006feaaa88951803df544444a8c01f7a9de2254600fdd4cd112a3007faa4488951803fe519c44a8c017fc2e61154600dfe15308aa3006ff1a8845518037f8d3c22a8c01fdc2561154600dfe34908aa3006ff1a3845518037f8d1422a8c01fdc54a1154600dfe55508aa3007bf28884551803ef93bc22a8c01fdc9561154600ff648908aa3007fd23384551803ff111422a8c011fe2e5a454600 else 0x1bfe506aa54600dff263552a3006ff921aa951803f7c54ccca8c01fbe6a26654600fdf34f332a3007ef98799951803f7cc2ccca8c01fbe6926654600fdf309332a3007ef97499951803f7caa4cca8c01fbe68e6654600fdf147332a3007ef89399951803f7cc1ccca8c01fbe5ce6654600fdf2a7332a3007ef94399951803f7cd14cca8c01fbe28a6654600fdf125332a3007ef98299951803f7cb94cca8c01fbe54a6654600fdf285332a3007ef93299951803f7c194cca8c01fbeaaa6654600ff734d222a3007fb97691151803fdcd1c88a8c01fee58e4454600ff7345222a3007fb8a291151803fdcc1488a8c01fee20a4454600ff72e5222a3007fb96291151803fdc99488a8c01fee6064454600ff72e3222a3007fb93191151803fdc90c88a8c01feeaaa4454600bff17319aa3006ff8a98cd518037fcd3466a8c01ff668e3354600ffb2c719aa3006ff9a28cd51803fec99466a8c01ffc2463354600ffe30319aa3007ff1718cd51803fec98c66a8c01bfeaaa3354600fdf4cd19aa3007fd8ba8cd51803fec5cc66a8c01ff62a63354600ffb34d19aa3007fd9768cd51803fecd2466a8c01ff65923354600ffb16519aa3007fd9a28cd51803fec51466a8c01ff624a3354600ffb30519aa3007fd8828cd51803fecb9466a8c01ff658a3354600ffb28519aa3007fd9818cd51803fecb8c66a8c01ff65063354600ffb24319aa3007fdaaa8cd51802ffc5cc44a8c01bfe2a62254600dff351112a3006ff9a688951803fbc4ac44a8c01fde5962254600dff349112a3006ff9a388951803ff4d1444a8c01ffa60a2254600ffd2c5112a3007fe95288951803ff4a1444a8c01ffa4ca2254600ffe123112a3007ff18188951803ff490c44a8c01bfeaaa2254600fdf4cd112a3007fba4488951803fed19c44a8c01ffa2ea2254600ffd173112a3007fe8a988951803ff45c444a8c01ffa6a22254600ffd151112a3007fe89888951803ff4d3c44a8c01ffa61e2254600ffd34d112a3007fe98688951803ff4bb444a8c01ffa6162254600ffd2cb112a3007fe9a488951803ff4c2444a8c01ffa5d22254600ffd2c9112a3007fe95488951803ff459c44a8c01ffa68e2254600ffd147112a3007fe89388951803ff4c1c44a8c01ffa20e2254600ffd2e7112a3007fe96388951803ff4a9c44a8c01ffa50e2254600ffd303112a3007fe97188951803ff4a0c44a8c01ffa4c62254600ffd555112a3007fea8888951803ff519c44a8c01ffc6a21154600ffe13108aa3007ff1a784551803ff8c3c22a8c01ffc6161154600ffe34908aa3007ff18484551803ff8ba422a8c01ffc5521154600ffe34708aa3007ff09384551803ff8c1c22a8c01ffc20e1154600ffe2e708aa3007ff15384551803ff8a1c22a8c01ffc68a1154600ffe12508aa3007ff182) else (if i<3 then 0x52c0aa3006ff9a860551803dfc4c302a8c01bfe69d8154600fef12ac0aa3006ff9a4605518037fcd1b02a8c01bfe6898154600f7f304c0aa3005ffabb60551803ff85d302a8c01ffc2e58154600ffe152c0aa3007ff1b760551803ff8d3b02a8c01ffc61d8154600ffe36cc0aa3007ff1a660551803ff8bb302a8c01ffc6d58154600ffe368c0aa3007ff1a460551803ff8c2302a8c01ffc5d18154600ffe2c8c0aa3007ff1b360551803ff859b02a8c01ffc68d8154600ffe146c0aa3007ff09360551803ff8c1b02a8c01ffc5cd8154600ffe2c6c0aa3007ff14360551803ff8d9302a8c01ffc2c98154600ffe344c0aa3007ff0a260551803ff849302a8c01ffc6098154600ffe2e4c0aa3007ff16260551803ff8a9302a8c01ffc5098154600ffe264c0aa3007ff03260551803ff95db02a8c017fe2e57154600dff152b8aa3005ff9b85c5518037fcd42e2a8c01f7e61d7154600dff348b8aa3006ff9a35c5518037fcd12e2a8c01f7e5c97154600fef2a4b8aa3007ff1815c551802ffd5dae2a8c01ffc2e57154600ffe152b8aa3007ff0b85c551803ff8d42e2a8c01ffc2a17154600ffe130b8aa3007ff1a65c551803ff8c32e2a8c01ffc6917154600ffe308b8aa3007ff1645c551803ff859ae2a8c01ffc68d7154600ffe146b8aa3007ff0935c551803ff8c1ae2a8c01ffc20d7154600ffe2c6b8aa3007ff1435c551803ff8d12e2a8c01ffc6097154600ffe2c4b8aa3007ff1425c551803ff8992e2a8c017fe6e14154600dff350a0aa3005ff9b7505518037fcd3a82a8c01fee6114154600dff346a0aa3006ff9a250551803fbca9282a8c01fee5094154600ffe302a0aa3007ff17150551802ffc5ca62a8c01bfe2a53154600bff37098aa3006ff9a84c551802ffcdba62a8c01bfe69d3154600bff36a98aa3007f78b54c551803fbc4aa62a8c017fe6d13154600dff34698aa3007fd8934c5518037fcd1262a8c01fde5493154600ffb26498aa3007ff1814c551803ff8b8a62a8c01ffc5053154600bff57698aa3005ff8b9485518037fc54a42a8c017fe6e12154600dff35090aa3005ff9b7485518037fcd3a42a8c017fe6d52154600fef12a90aa3005ff9b4485518037fcd2242a8c017fe6cd2154600dff34690aa3006ff9a248551803ff449242a8c01fde5492154600ffe30290aa3007ff17148551803ff898a42a8c017feaed2154600dff34d552a3006ff9a4aa9518037fcd1d54a8c01bfe68aaa54600ffe303552a3007ff171aa9518037fcbb554a8c01bfe592aa54600dff167552a3006ff893aa9518037fcb1d54a8c01bfe50eaa54600dff165552a3006ff892aa9518037fcc1554a8c01bfe20aaa54600dff2e5552a3006ff962aa9518037fca1554a8c01bfe4caaa54600dff065552a3006ff981aa9518037fcb8d54a8c else 0x1802ffcd9146a8c017fe6e89354600bff36c49aa3006ff9a624d51803fecd1926a8c017fe6c89354600bff36249aa3005ff9ba58d518037fc5d2c6a8c017fe2e56354600dff152b1aa3005ff9b758d518037fcd3ac6a8c01fbe5916354600dff346b1aa3005ffabb58d51802ffcdd286a8c017fe6d94354600dff34ca1aa3005ff8b9689518037fc54b44a8c01bfe6a1a254600fbf16ed12a3006ff9a7689518037fcd3344a8c01bfe691a254600dff346d12a3006ff8a368951802ffd5db44a8c01bfe2e5a254600dff370d12a3006ff8b8689518037fcdbb44a8c01bfe6d9a254600dff2ecd12a3006ff9b4689518037fcba344a8c01bfe591a254600dff366d12a3006ff8b3689518037fc49b44a8c01bfe5cda254600dff2c6d12a3006ff943689518037fd5db44a8c017fe6e0a254600dff350512a3005ff9b6289518037fcd3144a8c017fe6d0a254600dff348512a3005ff9b3289518037fcd1944a8c017fe6e89254600bff370492a3006ff9a824951802ffcdb124a8c01bfe6989254600bff36a492a3005ff9b3249518037fcd1924a8c01ffa6889254600bff362492a3006ff9ba60951802ffcdd304a8c01bfe2e98254600bff172c12a3006ff8a9609518037fcd3304a8c01bfe6918254600dff346c12a3006ff9a260951802ffd5db04a8c017fe6e88254600dff152412a3005ff9b4209518037fcd2104a8c017fe6cc8254600dff346412a3005ff9b120951802ffcdd2e4a8c01bfe2a57254600dff350b92a3006ff9a65c9518037fcd22e4a8c01bfe68d7254600fbf2e6b92a3005ff9ba58951802ffc5cac4a8c01bfe2a56254600bff370b12a3006ff9a858951802ffcdbac4a8c01bfe69d6254600fdf34cb12a3007ef976589518037fcd22c4a8c01bfe68d6254600fdf2c6b12a3006ff9a258951803ff4c12c4a8c017feaed6254600bff374a12a3005ff9b8509518037fcd4284a8c017fe6dd4254600dff34ea12a3005ff9b6509518037fcd3284a8c01fee6914254600ff72e8a12a3006ff9a350951803fdca1a84a8c01bfe6894254600bff576a12a3006ff9ba4c951802ffcdd264a8c017fe2e53254600dff152992a3005ff9b84c9518037fcd4264a8c017fe6dd3254600dff34e992a3005ff9b64c9518037fcd3264a8c017fe6d13254600dff346992a3007fd9734c9518037fcd1264a8c01ffa6093254600ffd284992a3005ffabb4c951802ffcdd064a8c01bfe2a43254600bff370192a3006ff9a80c951802ffcdb064a8c01bfe6983254600bff36a192a3005ff9b10c951803ff8d4122a8c01ffc69c9154600ffe30e48aa3007ff1a324551803ff8c1922a8c01ffc20c9154600ffe2e648aa3007ff1a224551803ff8c1122a8c01ffc2089154600ffe2e448aa3007ff13224551803ff819122a8c017fe2e58154600dff1)) else (if i<6 then (if i<5 then 0x1477c8e971c6a374c6c38d3b19de32e462b8bc916fa2d1c5888ac514f228b44f089951292239c458887b108a203c3ec87a30eda1c2c36a869f0cd218742e8859b0aca140c250845508120ef41b8830f058609dc10a81b302ce046c06780830015fefbfc47f68fe65fb9bf587e7afc31f733ecb7d1ef979f16be077bd8f719ed03d7a7aa8f4b9e843ce27978f259e3dbc55785ef025df1bbb276eced15d84bae3757aea5dd333a407434e7d1ce739b3731ae5c9ca639317216e3c1c6538a470d0e0ddc08b7e06f48ddcdba6b7276decdb99b6b36c66d6cda41b4036706caad8bdb1536256c2ad841b0035cf6b68d691ac4b5796ae8d591a99b5236a3cd3e1a6eb4cd697ad2b5a4eb48d68e4d1b5a2eb44d687ad0e1a0933ec678cce819c2b35f6672cc7998732fe65b0cb2195c329d6504c971920b2316442c8198fb31e663acc7198d5b19b6316c5ed8b5b16662acc51989b31266200c36985a308e60e6c10980e2ff65fa0bed57c7af5e5e70bc7578c2efd5d82ba9974b2e7b5c94b8916ff2de35b90b6b56cead775aceb55d6a3ad375a4eb45d67e2cec59b8b3056532c8058e0b181622ac2a5808afd15f7abea57b4af555d7ab8956f2ad4d59c2b1255d8ab19555aa9054eaa99551faa2f5428a7e54e9a9b8533aa6094ae294c5278a4b148328eb518aa2a9442287450c8a12541ca7fd4fc49f493d627864ed69d1537f26ac4cb498212db257a4a669359242240647d68e391b9a32c45f68aa513121d9435085dd0ae210a417081150151fc23ef67ca4f769e9b3cbe7860ef91db63a9c7448e4f9c37379e6d70d749a8134326748cd0996532946490c7f18d83164625cc3318352fdc5e9cbb017452e545c10b6f16ad2d0e5984b23162b2b865540a7f14ac28ca50789f693a627004ce4973929524de48cc8f611a5231445908aa10f7214a417880b8fc51f123db87780ea91cc438406e48d821a60334c65c0c8718ee2fb85d38b2915da2a6c5350a2313b825fc49c08e6119622c04500864100e1f843d2878a0e0219e031305d40aac1360259048c08740fa01e10386067e0bb4158825403ee06940af010c017401740005ff9b62a551802ffcd9952a8c017fe6c8a954600dff36c54aa3006ff9b32a5518037fcd9152a8c017fe2e5a654600dff152d32a3006ff9a769951802ffd5db4ca8c01bfe2e5a654600dff166d32a3006ff8b269951802ffcdd2eca8c01bfe2a57654600eff172d22a3006ff9a669151802ffd5db48a8c01bfe5d9a454600bff374b22a3005ff9b7591518037fcd3ac8a8c017fe2e5a354600dff152d1aa3006ff9a668d518037fcd2346a8c017feaeda354600dff172d1aa3006ff9b668d518037fcbb346a8c01bfe6d1a354600dff2c8d1aa3006ff9b268d518037fc59346a8c01bfeaeda354600bff36c51aa3006ff9a628d5 else 0x8697065beb1511a9851d2e0ca1a5c087b2a93e835aa15beb1511a9851ca1b54cb84600dbfa63476865ab2e0f4696fac551ca195c1a8d2df58aad9431a032df58aad94751aa01808eb7d54d1aa00808b4696a896fac556ca394351ad53a0941500c04bdbfb168d68ed0cae0c3245b823340638169816a005beb155b28634075beb155b02350c680c2396fac556ca198d19002df58a2854c2865707400b7d62ab6142a628060242b863425beaa68020222d50a005beb155b0a1530a1b54e8250540301336fec5847a63432b831a0dbfb175b686635aa741300a0180962dc4c9c830c0b4a0b56fab6446a61471c8382d1b0a08e4116fab6446a61471c832df192b155b28e6346192b155b223530a3a8060242df56ca61470c95aa65be32562a23530a395c1d549c812d5634257015beb155b39844655be32562ab6446a628060240d9570c686b7c6caa9a00808a3656a896f8c958aad911a9851daa741282a018098b7e43600d8badb4c68ed53a0980500c04c3918036feb6d31a396a9e43600dbfb174c68e570790db7f62eb6d1cc6b54e82601403012e436dfd8bad911e98d53a0980500c04b1700b58d0e5c02d63431d4b1511a9851ca1a5c1d6fa23530a39434b85aa75ab2e18d0d6fac550d2e111956fac5446a61434b830d85beb1511a9851d2e0e3605482d50d2e0ab7d4c28e05aa196acb890485bf80362ca9d31a3b434b84600dbfa6347686970b54e0b74c68ed0cb565c1b6fec5952c6b476869707dbfb1654a23d31a1a5c1d43600dbfb1654e98d1d2e11b575c598f8bedb54823d048d0afa0f340b67fbcfc19eeb3d5678fcebd9cb738ee702cdcf9b5f358e696cccb98d330765fecbb196cb2d16587caad949728564fac9bf92e724f6478c8bb9137219640cc7f98f871e8e3a0c6f58d7f1a2631ec5f18b771616291c4d7891710fe1f9c3a7870f0cee177c2cf8507082e0eac17381f7020e010bfeb7f3efdfdf99bf137dbafa45f17bde37b02f47de74bcb378cef015dd1bb4175beeaa5d2eb9fb735ee58dc8bb8e17156e22dc2ab8096f4edd6db87b6d96d46d9b5b10b5d56b12d5a5a99b4fd6962d1eda2db40f67b2cee59c1b33765d6cad593fb21d63fac6c58a7b103616ec1ad80fafe95f3abd45777ae8d5c2ab7256bead1b5972b1b5605ab93568eabed562aa635402a6d54a9a8f1514aa1bd411a7d74f169ca536ea6a74ce298ed302a5cf4b0694dd275a489487a8fc51dda36f46468bb5150a255446a87fd0d9a15141de82350159fc93f267d74f889ef13da27ac4f489e5b3c76786cef29dc53b4a7564e869cab38ea704cde39b6536326adcd409a3533a66674cb3990531466104bfa97bf2ee65c9cb6296632c02572caca953329fa52c4a3d944527f24f0c9bb934125be4a4c91891e5235e45e48a1910d215641d481f8ff31f4e3d) else (if i<7 then 0x8005db056e85cc0450ac012860bc50a820a8608143056405410450856fbb6552378ab15548dcc21c5303552a19410d412a9100805a2a5801016886600356c21b010cdb086c043152c004a08db602199810c88f011254886c04305af1440178a08461816bc5152a08a0791188490654b0012a93bf2a50110c302d112395221b010e54c8614a990c295321846182020432a91b000adf0bb60aa90adf0bc50aa91b2276c15e815ba3644b7d4109db2b6504373014461446b4c488d6009cc298504351c1001470406194730018c91a0b146ad82a3954a821a2354025beed9548de2ac555237308714c0d54a8e128255225bea084a3823a816bb6182d08d505a205aaa443aa4102d1832730205a88c488c168819482530305a151c105a1104a39800c16ac5148251caa4688d50086c3c505a350c105a1104a1840b42362413c5152a18a0b51188168441286600305b2096f8c16a8e102d552a186314470861eb4695c186f8c918a2dc5b086a3471be324628b716c23a8d1c6f8c516c2384351a05a71be3246288e10cc6a5c1c000c91323d65c144c08e1eb35464cb837c5f6d6808d6a9d04036cc206f8c918a2dc5b08663471be324628b716c2644c02d10dc03012cd002d10df1923145b8b610d468c720c751a10df18a260430f59706192266db02d20df1923145b8b611cc68fc03db79819cb54e4186f8c916e2d844899130238168d8e0180982e4e418605a4132720c302d21c805a21be2dc5b08e391468c31f6f8b91b0208e451a30c713207b6feb6d1d40354e8239061947228d08648c516e2d84c89811dc030124430c916e08c6f82d3000132260471c83e8618e224549c83e8618a37c5b09811c3266a9c838c51302387acb828861042646f0bc05a610c3d45c0c648b710c07816946f8c918a2dc5b099131c0301245b8991a02481694000df16e2db54e82390680c718650e2c01adb54e82390680c71864e00dbfadb54e82390680c718648bcc01b7c5cea9d04720d018e30cac01b7c5ceb61b0208e41a031c61958036feb6d53a08d01c831c61938036feb61122a4e41a031c61920b46c8f61522e28d18168b8a3436480b46c8a91eec68a7d016887b1f463431c1aa4fa0c7b9f476c31ec7d1db0d6a8f6102d1eeb558d106f8f5e010088208168df1b3c020118410a91b23df8040234821b22a47b88280469aac6842a46c8816aa91b233baed86c8c610cbb8aed883666a9c818d91aa7206364e40a6a8d910001be2196acb8552680c748248001be2644c08e3912e154986904a1be3145b08e10cc68169c6289811c2187abb605a71be3145b09810c0b4c37c628b6130238169816ab8504c6880b47aaa9504209011816a825aa35beb15472866352e0cb1511a9851ca18fa4b83adf446a61472865ab2e0eb558d4b81adf58aa1911cb82adf58a88d4c2 else (if i<8 then 0x4310d808461962e021ac511d808663b0108c70a1c0431240b7010f010443300102d5bf808621a802b6c04405aad85ce022086a002df0110c3082553808861844a82404476d40040b680086caa9a003a001a001a001a00178b400540034002366800a80068004168a9600305b6d9800d5b5b6953008877d8008648dfb6d00882a6db30018991bf6da01106fdb680431beb16db402202d80421523da010cfa2a915300883d9800816b0012d576caa60112549df78b00892a5e2aa980449beaa6010cfa40210d91ef0086aa5db4021cdf76caa60112549df731008819c6fb98804495300852a6010a6fbb6553008937e010a549df804395300852a58008711df804395300843d654c021ca980429beed954c0220d810500872a4efbc5804495220a010e54b0014a9804295300843de01086c0a978b00892a6010a54c0214a960100862087b4021dc505a2a580106482d60031926d854c0225c518aada0110169c5553008826462c021dc518b008771462c02182d804219620ae2c0225c538aaa662bb6004615232e010c65b00102d600298a366010ee2bb68043952366010e548d96003952716010e548d98043952715cc40224a980429530085316010ae2c0214a98042952c0052a6010a54b001b300892a6010a54c0215c58042952366010e548d9804395300852a601084c9b615300896615b09880441322a6010ecc098804305a662010ecc0988043b30b144c402201c10500860b4cc402181c5bf2600110cc2a9930008808854b00182211cc0066d854c021ab611d0086325628a930d008a324474021c8e80425521152c00426454c021ca9804231cc004b1447186804410461a010c16c02118e91cb7ddb002298e91cb140110c748e53000882a64740218896002112219800cdb0a9804356c21a010ce40a9804339021a010ce2c868043113209800c4c8a9804313221a010c54c0210869050086b1444c021986104c00621a414021aa990c6180110e448658a61801154718690c00882a444c86905008a2d816e021898133808623816e02188678a0b7011016882404305a209010c168ddc043132303010c16e02102d11cc0062df01084c8a0c04305b80840b443300182dc04205a21b010c168c8c04305a2f05b282c0451320784c602202d12580860b443300c0441be0b5db2a9404518a0b554a02221c132808623816a02188605aa0901118004fa05e28554865c2df504373014461446b4c4e614c2821800a382058a1970a3954a822223540278a136ca084a18205901970f15432822223080db2866003504aa44ed82b7426802ad82f14266141080a182b202a08205beed9548de2ac55523340aa5470d54a865043504aa4404016b00182d11cc00623b010816855b056288ec043124160015528084aa50108c702d552311d8085238263820404709 else 0x16d00102da00238a0b6800c16d00102da00278a0b6800d800416b0015b638a6db0112db0b81858088c0022df01085be02160208b705ac007660018acc1b63318088072cc032c044132377010f01044c82dc043132303010d8004c730013b636c63b0111cc19831d808823b01098005db60210b71bb8086e6301084c8c0c04378b808580820b70109db02dc043c041125808540022dc16ab6a00416e23a800cc75001092a00231c2a6800cefdb6c04316d80840b580085b82d16cc0082dc16e0218b716d8086638606021db616d80860b65b6021e02089905b8086264506021b000dc530cc00677ee2bb630d808a7230109e29c530d8088edae29b630d808ae62e299830d808b714c7186c044b8b80842246c6021b000bc576d80878082f170109e2bb6c0431ba3146ce0223c57318086264698c5c04413230262e0223c5c04219d808423a62b0018c919c31701105bcc516d8088264504c5c0441120b46c602202dc04276d20b010c168b910580882de41602189973180872084ce021892c042905808540020b68008432b6a00305a2e441500208616f4006618415001892a00210d400461a8008c3089a00358aadb010ce29b6c043c04105ac0040b580086f8f5c0431338085808237d62e02182dc042c04110cc0040784ce021886133808624b0108436021186112a09011301046482d60031923215b60220b719180862646460218c919180866186460219c5c04205a209800c168b7600305a2e44160220bc16c3df0110168b910436701145e0b7c04305b20b010cc30b91b380882645e482c0441782df010c5b98e90580896d9628b6905808a6d87be0218bc173808671701081689931d80882640f2b6c0441320b7010c0f09910d808826416882c04413207b010c16e02118613380860784ce021986133808766162898c04403c267010d62e0211c5c042124c004249800816e02109256d808632416e0218c912580862dc16882c04416e24b010c4c82dc))))
def fR5L34 : PackingT := (655,4,7,15,fR5L34F)
def fR5H1_34F (i : Nat) : Nat := (if i<4 then (if i<2 then (if i<1 then 0x76dc05ef0d00036f00dbc036f20640036ff071c036f00dbc036f00dbe40da00dbe44f700dbe431600dbc036f00dbc036f00dbc036f00dbc036fb0c44036f00dbe412f00dbfc67060b66441ef0bf6866200dbd428550505031350b0c036f90854036f00dbec0f3c0b7ac116a130e826900dbc036f00dbc036f00dbc036f409234429b013f86cc00dbc036f4157cc049a1406045100dbc036f00dbc036f00dbd00250070c036f00dbc036f90982015e00dbc036f00dbec21300dbc036f00dbe805f1031c036f00dbc036f00dbc036fb11d0030451333862800dbc036f00dbc036f00dbc036f00dbc036f00dbc036f00dbc036f00dbc435d401ec036fa02bc036f2058341b0e061b013500dbc036f00dbc036f00dbc036f916ac036f00dbe4590706a0036f00dbc036f309e8036f00dbc036f00dbf401f00dbcc1b570d90036f00dbc036f31198036f3030e405800dbd435b90d1c036f11aa0036f004f0036f00dbc036f00dbec34b00dbc036f00dbf0541c0990036f00dbc817601854036f00dbc036f311c0036f00dbfc20b00dbc036f005000000002000001000006003002005000000000000000005002001000004000000000000001000002002000003001000000002003000002003001000001000000000001003000001000003000001000003001000001000000000000002000000002001001000000000001000000001000001000004003001000000000002000000001004001000000000001000000000000000000002000004000001000000000000005000001000000000001001000000005002002000000001000001000000000000000002000001000001001000001002002000000001000003000001001000000001001000005005000000000002000000001000000001000000000002000002000000000002000000000000000003002000001000000001007003000003000000000000000000000000000000000000003001005000000004000001001000001002001000000006000000003000001002000002002000000000006001000000000001000003000000002004001000000000000000001000001004000000001000001000000002000000000000000001000000000002000000001000001000003001000000000000001000001001000001001000001001000000003000000000004001003001000000003000000000000000000001001004003001002001003000000000000001000003002001000002000000005000000003000000000002000000000000000000000000003001000000001000001001004000002005000003000000002000000001002000000000003000000000000000000002004002000002001000001005001005002001000001002001005002001000000000001003003002000003008002000000001 else 0x36f00dbc036f706dc05c600dbc01a9c0b38036f508f801a000dbc036f00dbc036f00dbe41f800dbdc6af00dbc036f00dbc036f00dbdc58c00dbc009d00dbc036f2060c01af00dbc036f30090036fc0becc1cae10bb4263f0d54036f50c86829e00dbc036fe0cd4036f00dbcc27990403c54f61200036f00dbc036f11d4c036fa0600036f00dbc036f00dbc036f00dbc036f5167c036f801e4036f00dbc806730698036f8032846c731618036f00dbf021400dbc036f00dbfc43300dbc036f00dbc036f00dbe015de0cc0036f00dbd04b500dbe842b00dbc036f00dbc036f8199c036f00dbc036f00dbd81a100dbf430b00dbc036f00dbc036fc046442653000c036f00dbc036f60b8f043000dbc036f71a10036fd0030036f00dbc804b90c90c3674088a446800dbc036f013cc036f00dbc036f00dbc061730104036ff078e41b900dbc036fd0018036f00dbc036ff020102b2b0780036f304e0036f00dbc036f00dbe816100dbec0e300dbc036f00dbc036f00dbd41e6514fc036fa09dc036f40b29806400dbc036f2050b86aa50228036f00dbc036f00dbcc1bb00dbe033800dbc036f008ccc10100dbc036fd05ac036f00dbe85a600dbc036f307cc036f00dbcc614e00b0036fb1864036f00dbc036f00dbc036f00dbc036f00dbd443900dbc036fb0ca0036f00dbe80e000dbc036f00dbc036f00dbc036f00dbc036fd16844007209d0036f00dbc036f00dbe80ff213d0036fc0048036fb0068c52d00dbc834500dbc036f00dbc036f00dbd8697d0710c04200dbc036f00dbc036f00dbc036f00dbc036f00dbc036fd114c036f910fb0223b0cb9419a00dbc036f00dbc036f00dbc036f30964036f00dbc036f01754036f50a25028300dbc036f00dbc036f00dbc036f00dbd007a6046c036ff09c0036f00dbc036f00dbc036f80360423b00dbf043b00dbc036f00dbcc257f02e8036b00dbc036f00dbc036f20cfc036f00dbc036f00dbc036f00dbc036f8058c036f00dbfc01600dbc407500dbc036f00dbc830d00dbc41de00dbc036f00dbc036f00dbe04b200dbf012d00dbc036f00dbc865b00dbc036fd1560036fa12bf001400dbc036f00dbc036f00dbcc27100dbc036fc08a305d400dbc036ff0660030a00dbc036f00dbd029200dbec0bdd072c052800dbc036f00dbe8089208b4027e00dbd028200dbc036f00dbc036f3188c036f00dbc050800dbc036fc0bd4036f00dbc047600dbfc56f60570036ff052c036f00dbc036ff0500036f71000036f70830036f00dbc036f00dbc036f704c0036f00dbc036f00903c08d811c80267f054c036fe19a5c1fcf07f8025b00dbc8177d1085427500dbc036f00dbc006d4011c411d00dbc036f40637c0e600dbc036f00dbc036f00dbc036f30294036f00dbc036f00dbc036f00dbf40db10a6001272) else (if i<3 then 0xdbc036ff0254036f00dbc036f00dbc036f00dbf40a600dbc036f00dbe823600dbc036f00dbc036ff1858036f00a2ec29b10a93c5b900dbf015000dbf414e00dbc036ff054a41e950318036f20764036fc0388036fd03e0c5b5512b785bc00dbdc10400dbc036f00dbc036fc060900c8202a4036f50b24036f00dbc036f00dbc81e271b24036f00dbe003150824036fc1437828dd1cb5072700dbc036f00dbc036f00dbec08550425427b00dbc860000dbe048200dbc036f00dbc444420984036f00dbc036f00670036f00dbc036f00dbc036f50905c0f500dbc036f20d4f02d100dbcc11500dbc036fd0db8036f00dbd42c000dbd4738e1108036f50be800e510d88036f00dbc05ad00dbe460f00dbc036f00dbf043400da0036f00dbc013f00432c05c90b33c56500dbc036f00dbd016e50a9c036fe0471c53100dbf815800dbc036f00dbc036f00dbc036f906e0036f017e403328086f42f100dbd01ff10838036f00ca981f900dbc036f50434036f00dbc036f00dbe4020b07ad066800dbc036f808dc036f00dbe40b2a0868408171aa4036f00dbc036f00dbc036f00dbcc26e30390036f00dbc036f00ba3013d7051c846d00dbc82f400dbc036fd18b3c2f200dbc036fc0b2c036f00dbdc50710890036f00dbc036f00dbc036fe008b0702309ce447700dbc036f00dbc036fc0758036f00dbc82e200dbec1bc00dbc036fa0314036f00dbe80d000dbc036f112f8036f00dbc036f00dbc036f00dbc036f807c9809a30688c0b9608c3c642c0194036f41654036f00dbc036ff074c036fe0708036f00dbd420890c20a83e00dbc036f00dbc036f00dbc036f00dbc826d00dbc036f00dbc036fd11b0036f8018c036f00dbc036ff05e1446700dbc036f00dbd842521932c18f00dbf84bc00dbc85fb00dbd448400dbe801e00dbe44eb00dbe008200dbc04cb00dbc036f209d9c149c009c036f61150036f00dbc036f1151a011e00dbf0686507d5821700dbfc246e0bfa012500dbd436c00dbc036f00dbc036f00dbc036f00dbc036f00dbe062700dbe029fb13a4036f00dbc036f00dbe4448b1924036f00dbc036f00dbc036f00dbfc422700d5429100dbec11f00dbc036f00dbfc16400dbed43e00dbc036f00dbe403700dbc036f00dbe426800dbc81c0a1639063400dbc036f00dbc036f00dbc036f00dbc036f906fbc2f900dbe035cb1d1a023280898036f00dbc036f00dbf808400dbc0658f091c80eb61870036f00dbe40cb00dbc036f00dbc036f00dbc036f00dbc036f00dbdc14de16d2871500dbc805de1578036f7057c036f00dbc036ff049801cf70884036fd0bf08235d1587854900dbf8758f1418855971d50036f403a642ea00dbc036f00dbc036f00dbc036f00dbc036f00dbc036f60ac4036f50354036f00dbc0057e11f4036f00dbc else 0xd043700dbc036f00dbc036f00dbc4510b0c1641ba00dbc036f00dbc036f00dbc036f00dbc036f00dbc036f00dbc434e510f2845841a60036f00dbc40a100dbc003d00dbc036f00dbc036f00dbc036f00dbc036f00dbc036fa11ec036f200fe04e000dbcc499c06a841fba1715010b7099840fd0048e81ed01168036f400d0813ef1115c17151408036f00dbc036f10760036fe0d5d0122007e8036fa03f0036f00dbc036f00dbc036f00dbf42dcb08f0036f80d58036f00dbc036fd0110036f00dbc036f00dbdc01be06ac008c3021c036f00dbfc296006ba82c700dbc036ff018b032300dbc036fe034e813771238036f00dbc82a9d074a818140d09c054812fe45fcf014d44e500dbd509800dbc036f00dbd420000dbc036f00dbe401800dbe06a200dbf82f300dbc036fc0008036f00dbc036f909fe033eb003c036f2077f0096d04ca4493d0863833da0120036f00dbc80f600dbe00acc0c8a80264152f42ac00dbf426b00dbe82be00dbd822700dbc036f00dbc036f00dbc45de00dbc036f00dbe012b411e0c08fc0aa0036fb07a8c36100dbc036f00dbc036f00dbc036f00dbc036fc0c77401d00dbc036f00dbc036f00dbc406fc0d0405bfa09bd82f850717c50400dbc036f0023bc1b420878036f31b20036f00dbfc23800dbc036f00dbc036ff03b8036fd0abb814300dbc036f00dbc036f00dbc036f00dbc036ff0568036f00dbdc2c2301b8036fb1a47821900dbc036fb0c54036f00dbe031ac18788092a1a98036f00dbf011100dbf403a11a8c036f80b54036f00dbcc4028069e018800dbc036f00dbc036f00dbe825c8029f426ce18c8036f00dbc036f708d10618913b9c34800dbdc2da00dbe4547f00bc036f00dbc036f00dbc036fd18d8862d00dbc036f00dbc036f00dbc036f00dbc036f00dbd819d00dbc85ea801dc036f00dbc036f00dbc036fd056c036f00dbc036f00dbec17400dbc036f00dbc036f00dbd45c100dbc036f00dbc036f70184036f00dbc036f111f8036f00dbcc49800dbec34fb0aee46bb70d8201f4c13a8036f00dbd0534f1031456700dbd454470633428c40c0d046a00dbc036f00dbc834300dbc036f00dbc036f00dbc84fdb00ac434d80858036f61256824bd0a1942889024c036fa0ae504aef0655453c00dbc433bd1934036f417e8036f00dbc036f00dbc036f01ae0c5945067c036f00dbc036f00dbc036f00d28036f00dbc036f00dbfc0f1808c7817500dbfc4d000dbd01f600dbf80198064dc61a00dbc036f00dbc036fd09314071a01a4036f00dbc036f010bc036f00dbc036f00dbf02b400dbc036f514a4036f00dbf009800dbc036f00dbc82aab05308488503a9c2a600dbf40ddf0a96456e00dbc036f6094c036f00dbc807800dbc036f00dbc036f00dbc036ff097c90e8d0934c4e311100036f)) else (if i<6 then (if i<5 then 0xf00dbc036f61154036f00dbc81f700dbc036fd013a81f100dbc036f00dbc036f00dbc036f50b4ec14ae145a822ae03ec036f00dbc036ff0057424e00dbc036f00dbf42ec1081d400100dbc036f00dbf431e00dbc036fb07b0036f00dbf82b32025180f000dbd4294e1848036f00dbc036f00dbc036f00dbc036f00dbec08b90646c22000dbc036ff04430763f0c4a04b700dbe464a00dbec17de076944b000dbc036f00dbc036f00dbd012100dbc036f90a28007ef08ba447a40514036f00dbc036f00dbc036f00dbc036fe0ad8036f00dbc020100dbc036f00dbf067120cbc036f00dbc055201662c0fe1044e419690664c30f00dbc036f00dbc036f00dbc036f1061301667021bc1e100dbc01dc70c1c036f10d98036f00dbc82d8807224611c05f2031800dbc036f704d3840a00dbc036f00dbc036f30c00854a00dbf832d00dbc036f00dbc036f00dbc816f00dbd80d400dbfc19b00dbc409c00dbf0103d08be04ec800a085fe01064036f00dbec24400dbc036f00dbf80a200dbc036f00dbe825100dbc036f407bec1d100dbc059170b3c036f9016e412a30894036fa0373827d00dbd014f00dbf435f00dbc036f00dbd45db00dbec35210d78036f41398036f00dbc036f00dbc036fb1520036f00dbc036f00dbc036f00dbcc63300dbd8278b0c65416800dbc036f516a6c02d00dbc036f207f4036f00dbc036f00dbdc23d70808036f00dbdc00a00dbc036f00dbd824900dbfc10500dbd85e140279c5e000dbc036fa0b04036f00dbf824500dbc036f6062c036fe00a8036f00dbc40ecb0a04036f00dbc036f61874036f00dbc036fd12d8036f00dbd817300dbc036f00dbc036f21b2fc35000dbc036f00dbc036f00dbc036f00dbd065d00dbfc1a300dbec06890114036f00dbc84c400dbc01b62127c036f00dbc036f1055c036f00dbc036f00dbc036f00dbc036fa189480be00dbc036f90ad500d600dbc8664213c4036f70b7f81f000dbd450500dbc036f00dbc036ff1d54036f00dbc036f00dbc036f00dbc036f00dbc036f00dbe40f200dbf440400dbc036f00dbd429da169c036f00dbdc21100dbc036fb0130036fd1170036fb037d6c9800dbc036f00dbc036f00dbc036f7065dc2e700dbc036f543b046b7f01ac036f00dbc036f00dbc820a00dbc036f00dbc036f00dbc036f00dbc036fd04c4036f00dbcc2eb00dbe04ac20338036f00dbec0c000dbc036fb027c036f00dbf84bd00dbc036f00dbe42f700dbd02c400dbc036f80da4036f00dbd85a400dbec25a00dbd434900dbc036f00dbc036f00dbe44413061e865090ae0036f00dbc036f00dbc036ff0974036f800e0036f00dbc036f00dbc036f1020c01c100dbc806a00dbc036f00dbc036f00dbc036f00dbc036f210e0036f00dbc036fa122780a4e08b28254f0a3c036f00db else 0xbf854c00dbc036f00dbc05dd00dbd828410c9e465321a94036fc06fc036f10364042a80324036f90448036f00dbc036f00dbcc49c00dbc036f00135c36300dbdc4f900dbc036f113cb42c600dbc036f803ea42d6a0a38036f00dbc036f51a2c036f00dbd415100dbd06a400dbc036ff06c8007000724036f00dbc036f00dbc036f00dbc036fb1a27004000dbc036f00dbcc43540280036f21569423a00dbc036f00dbc036f802fc036f00dbc036f00dbc036f00dbf010e30648036ff146684b1a0c94036f00dbcc2af00dbc036f00dbc036f00dbd02a28058b02bc00dbc036f00dbc036f00dbc036f00dbc404600dbf446900dbc036f00dbc036f00dbc036f00dbc036fe1388036f00dbc460e50bdb009b00dbc036f50958036f00dbc036f00dbc036f00dbc036f314f8036f00dbc036f00dbc036f00dbc036f00dbc036f00dbc036f00dbd41a500dbc036f00dbc036f108ac036f00dbe820300dbc036f00dbc036f00dbd401000dbc036f00dbc036f00dbc036f00dbc45cf00dbc42582140c45ae103d34626a016902b0b05ea42ba00dbc036f00dbc036f8025cc0a800dbc036f00dbf403c2106fc2a100dbec4a000dbc036f00dbc036f00dbc036fa12cc036fa0bc0036f00dbe801300dbc036f00dbe82ede0348036f20b74036f30718036f019bfc53d90483432600dbc036f80b90036f00dbc036f00dbc001c90d10036f00dbc036f00dbc036f00dbc036fb087c036f00dbc036f00dbc036f00dbf02e50039c036f00dbc036f00dbc036f00dbc036fe02e141ad00dbd025500dbc036f00dbc036f00dbc036f00dbc036f00dbc036f602ac036f00dbc036f00dbe021cc16a0036f00dbf828000dbc036f00dbc460300dbc036f00dbc036f102d0036f00dbd801700dbe865a00dbc036f00dbd823f00c30036f00220036f302a8036f00dbc036fa1314036f00dbf005500dbf40aef0bff8050a148c036f00dbc036f00dbc036fa1949c1ac60bbc036f1001481e700dbc036f00dbe400800dbc40b700dbc036f201d0036f00dbc006600dbc036fc0554036f51a3c036f00dbc036f00dbfc021d0b4ac44600dbc036f00dbec0d700dbc036f00dbc036f00dbc036fd10ff010700dbc036f901f2068700dbc81b300dbc036f00dbc036f00dbc036f00dbd003600dbf042600dbc036f00dbc036f419a8036f513f8036f70848036f6010c036f00dbc036f00dbc036f00dbf040100dbc036f00dbc036f0012801e800dbc036f3030b4309e081b44f0b0594036ff1074036f30344036fd0180036f00dbc036f311bc848c00dbc036f00dbe80b3e04a7824a31a4a02c500dbc036f20d30036f00dbe01ce8075202ee00dbc036f51a5ac52141994036fe1b1086b100dbc036fe0558036ff05c8036f00dbec2e6511b8036f00dbc036f00dbc036f00dbc036ff008c036) else (if i<7 then 0x6f00dbc036f00dbfc43600dbfc29700dbf42b700dbc036f00dbf053a60c50036f00dbc036f505a8036f9097901cd00dbc036f00dbc036f91bb4036f00dbc831000dbc024f00dbec6ca61a2b05ba119afc06c00dbc036f00dbf417000dbc036fe0468036fd1ac3403e00dbdc2ad00dbc036f304b0036fa02c0036f00dbc036f00dbc036f00dbc036f00dbc036f00dbd80bc00dbc036f00dbfc5aa50cac036f00dbc036f00dbc41e500dbc02e151148003b20810036f00dbc016980b34c00bf0db6c41c00dbc036f00dbc036f00dbc036f20d52435820cc4c0bbe05b0036fb03bcc33680b81042000dbc036f00dbc036f00dbc813b00dbc036f00dbc036f00dbd81d000518036f00dbec47f21498036f00dbfc35100dbc036f00dbc036f00dbd410a316d8036f00dbd010600dbc036f00dbc036fa00c0036f00dbd06f88062ac65fb0551800e00dbc036f00dbc00c400dbc036fc00c8036f71538036f00dbc036f50520036f906f60287517f7829350c38036f10565836a00dbc036ff11e4036f00dbc036f00dbc036f00dbe400d00dbc036f50841c4e860c19819e911d4036f00dbc036f00dbc036fc08a4036f80c80036f80b40c20f013d6460400dbc036f9014b850000dbc036f00dbc036f00dbc036fa028c036ff07b8036f900e4442300dbc036fa0d66005100dbc036f00dbc036f604da02ab00dbfc46bf0834036f00dbc036f00dbc036f00dbc036f50d96875f00dbc036f00dbc036f00dbd411400dbf01cc10513433c00dbd013900dbc036f00dbc036fc0ca4036f310a0036f00dbc036f00dbc036f00dbc036f2139c036f00dbf0666a1386018500dbc036f502c7405650ccc036fb1240036f00dbc036f00dbc00e800dbc036f40000036f00dbc036f00dbc44ff00dbc036f00dbc036f00dbc402990336c52500dbf81d5501c8036f00dbec17e00dbc036f00dbc036f00dbc036f40b5c01d740638036f30d6a449180a73807f00dbc036f00dbc036f00dbc036f00dbc036f00dbf851f00dbc40ad00dbc036f30cdc433a61807454d00dbc036f00dbf455480c05048d00dbc036f00dbe41dd00dbc036f00dbc036f61880036f00dbc036f00dbe807600dbc036f00dbc4099108764205b0490036f00dbc036f00dbc036f00dbc036f00dbc036f00dbcc26240242426af132486ff0132084dbc0af4036f00dbc036f00dbc036f601cc036f00dbc036f00dbc036f204ba800930cd100cf00dbc036f00dbc036f00dbc036fb116c036fd06c4036fe177c036f10010036f000b8036f305ec809140421031b00dbc036f00dbc001100dbc036f00dbec593f0c09c0c1e02d4036f003df02393159140f900dbc036f00dbc036f00dbc036fd10b7411700dbcc50e00dbc036f00dbc036f00dbf847371a14036f904a0036f71984036f20908036f00dbc036f00d else 0x30a8202e900dbc036f00dbcc638b05b6031cc0cb0036f00dbc036f00dbc036fd0330036fe0948036f00dbc036f00dbcc13300dbc036f00dbc036f00dbc461300dbfc2500090fc189b0a4085ff00dbc81a400dbc036f00dbc036f00dbc033900dbc036fd0a8d445600dbc036f40460036f00dbc036f00dbc036f00dbc036f00dbc036fb01f644e400dbc036f00dbc036f00dbc036f00dbe42db00dbd029900dbc036f40b51413a00dbc036f00dbc036f00dbcc0de00dbc036f00dbc036f00dbf046500dbc036f005fc036f00dbd0295b0c7c036f00dbc036f00dbe010220384036f00dbc036f00dbc036ff0164036f218b8036f00dbc036f00dbc036f00dbd461fb0b20036f00dbd058700dbc036f00dbc036f00dbcc45000dbc036f00dbc036f5127785b0f043ec179803b4027c00dbe4346a14b0036f00dbc036f1059c036f00dbc036f00dbc036fc10f4036f00dbc036f00dbc036f00dbc036f70a6bc1e400dbc036f00dbc036fd198c036f00dbc036f00dbd80b6312e8827200dbe803300dbc036f00dbec2bf00dbc036f00dbc036ff0650036f00dbc031700dbc03)))
def fR5H1_34 (h : Nat) : Option (Nat × Nat) := lookupWord 416 3092 12 18 10 4 fR5H1_34F h
def fR5L37F (i : Nat) : Nat := 0x11a0b45803e9e2f30c730c5c1d00802dfa628ea19dd354b84bbfe2f6cd030c8d55341330908edfb151aa3a86701982e12eff8bdb73016b1cc355341601012da06382d1dbf62d6d4355341234c720b70b50077edf716c52a59808e9823986a18b878476fd8b5b50c8d55341340977dc5f17b6e618e0b586aa682c02026104e430c1692dfada8eaa6827211a619016b8b62b6d5b3314c31d473bec355341601013d0080298a3aa9a09c87d1864a01005bf5b531471aae420bc0b500801dfb7dc5b14b92a598a618ea38862e200f05aefdbee2d8adb56c11b1d4710c8d5534133102482d77edf716c56dab666023a618e61aa9a0b0080a2804016fd6d54d04e4340c730ca0b4df716c53d8a96629863a8e61a86c00b8209eefdbecc530c751cc350d801706a904cb7ec5a3a86070b86608243bf6fb8b62952cc0474c05a4730d43170413a0077edf716c5224a96629863a8e0b4862e0827bbee2b6c41330c730c5485a90b5dfb7dc5b15b6adb0061a86aa682681a16bbf6fb6d5b152cc530c751d8055341390e37ed523886ae02df17b6aa51aa0976a8464710d8016efa78b54f305c2cdfb5486ae198f17b6aa423a0946fdaa11b404357180405e2f6d54f30c7504e37cc5b5423239c8ae30080bc5edaa9e6186a09f6a85be297154a34637ca97d2d5c000277fc5edaa9e617801b3db1abcc390637ed508c8e21ab80b482c0202f17b6aa798a09f6ad1d43600fa78b54f305c26dfb568646ab84030080bc5edaa9682826dbf6a84743570c720180405e2f6d54f31413adfb568eae1864030080bc5edaa9e62826c016fdab4750c16f8a5c553cc2a4ff2348eac5da22f0a4840c0b1f22f3275aba21c66d9869cb39187eb9a575aa093ce96a48aa210fd278a38199c8bfe58c29192487ee3b61a18c084ce2080c083c00d2000ffe2a551803ff9a654600ffe5d951803ff9a454600ffe59151803ff9a354600ffe28d51803ff89354600ffe58d51803ff94354600ffe68951803ff8a254600ffe24951803ff98254600ffe20951803ff97254600ffe58951803ff94254600ffe4c951803ff83254600ffe60551803ff97154600ffe50551803ff93154600ffe48551803ffaaa54600ffe8cd51803ffa2254600bfe2a551802ff9a654600bfe69151802ff9a354600bfe68951803ff09154600ffc60551803ff17154600bfeaa951803efa6654600fee91151803fda3354600ffa88951803ff21154600
def fR5L37 : PackingT := (42,3,7,13,fR5L37F)
def fR5H1_37F (i : Nat) : Nat := (if i<2 then (if i<1 then 0x1f233f0051e01478051e6312b814e00f800226204d0051e607f8051f211558b2fe11460cc7c05408cc5e083408060255708bc012a38b3e01478051f029c0051e01478051f43273823201478051e01478051e01478051f00a9b0a2e01478051e01478051fa01da84c3c1388051e0147b025001478051e0147d04b60147d818601479815a01478051ee0fb8051e01478051e830d201580147b08380147d03fb60e8e82af025cc00a742c28051e01478051ec299e85076139e089a0147880916202a82a46100684c140ed7036f61238051ea305182420147b8cda01478051fc10978baee11fc01a9a0938051ee02c5034b2275c81dd811ce027ae0e7f850a00d49029401478051e0147f827480df58a4a0147f04b360ac80c18c2e78051f2299500bb801b10c32a1360051fe00df017ee0eb4825e811f0051fa12ea801481100051e0268d84d60143d816601478051e01348051e0147d01b4e017788180147f8211a0478051ea25d0051f002638b0ce028484c8c249f842920cd4013b432b88c0b4031f8a90e276f0b8fa2f2683b900852018f22d8e002402538051e20b450019424d689520147d0aef80108051f00b71001201478051e01478051f40d88051e0147c82fa01478051e0147b81a001478051e0147a011001478817102930051e0147b0be601478051e01478051fe01e8051f00bd0051e0147c001a01478051fc10d0051e00ce0051e2025d808a0147a0264c0ccb8af601478051e01478051fa0fe0051e01478051e408c5028a6274a8197205ce0cf20040500600a03001800008010000050100080680600800003006002010060000000000000000602c00806000010000000000000000200200c000030040040080000000c0000301a0000080000000c0200100000402000000004000000160000280601c01401805000008008030120000080a00000000002010004058010000000000500000007800002000010000020040300000001c00000002000008070000080000102a0000e0010020040000300a0000000600a00000802000000000020000040280001400c0300100000000000000000000030000000100300c00001009006048050000000040400300a0100101b01a000000060020700600300200c05002000020020010000000080000a000008010000040000c00a01400003000004048020000340180200e00000800008040000000180000080600a0080180200e004010030160340000000e0100280a00e010000060000200180100400c008010080240180000a0000000001c004028000000000500000800000000000000010000040100180301e0180000000201c0080a0000100000100e01c0300300000401001002014018010060000000000e00c008020020000000b00600404807016004008020020480301400c0040180c else 0x47d09bd60198051ec0fdc0ba803008051e0147881f3600838022607e8051e0147c808c40c458089206f804ce41445803d609c08c2801478051fa2e58051e01478051e014780413a1120051e0147b016321058051e01478051e8285509e142aaa04afe29fa014de2de0051ee271a01320147c8b662230e837001478051e01478051e01478051ec0690051e01478051f42120051fe1267830320928051f822870c2e0147c830f4088e821c80ec308440147b01c601478051e82b6b029a80f500ca1431138a12202f581272250f84fba1076895fe2a340cf60147a851c0147e8b3401478051fa0600051f00a1101d661188051f400a8051e01478051e01478051f2222e83b2c25a8051f800e6887d810b0051e0147d01120147a88e9412e1036001478051f428068a26e0918051fc32fa09e60147a01e240810051e6339604c40147b8af2028c78a7342ce88516a0aaa047b6040c81a60147e88920147b00fd027678279a00a18259403ed84f90282e823c203e58ad2c25120ccf602cc011d22918051e0137f81cb40969016e02cf38443007c60cd601478051ec04960b93a0e48051e01478051e01478051ee0f010213a06bb044fc2a3e83464116b09a8014790474a260883ab008b0051e0147d804840ada0228003fc83e7c01c38b160147b82c9a29df028cc13b0051fc07470aaf0323e848801478026180cc689320147a0c8140e4788b440e58051e01478051e80278051e0147d802e01478051ee0b0e81b001478051f22e70051e01380051ee265900160147c8b20231f2010c20f4184a2a079984f20147c0a57601b8051f62ee0051e80eef819e00e6783e9c0c7e84d58241e84900147e0bd601478051e0147e042b6206d0365626768b260147e812e604da89e9031a881f842088051ec0cd8051f229a8051e02f178006221c8051e01478051e20204850c0147a08540147d0c000147f8af4c2dc8051e01478051e01478051e0147c821e0147a00f40147f801c20dc8051f405d0051e00e688414a31d8897c0147e840ec0bf70a62805048be20147a024580f74842e012b0051f811c18216c02150acfa10f98287c01fa885042f8780db00310051e01478051f40348051f42819833b4045f892520391004d806f0051e0147e02880147902d401478051ec13ae8143a146184100111b8adda239c8313e02fc826c2060e0b866225f80ea827220a5201478051e8021e80ada2a98051fc09f40a6c01478051e01478051e62158051e0147d8c3180c9e023a608ad0068c0bc303c22070c851201478051e80f11029702ed8051f60d00051ea2eae844461281805401034015de00f8051e0147a82020147d813ce094902eb42add094a6327d881601478051ea126800b40147b892e0147f8a6fa048f818c4011e0956c1060051e00e980b9a014798cb040b9005) else (if i<3 then 0x1c1a0238051f20fc202bf026e6030802c60051e60f23006162640051e01478051f42c00051ec0da0051e0147b0ade01478051f02b4681ce60ac008840147904ee01478051e014788ab82296283ae607b783fe20c85007ce0450051fe0818051fa04b780aea0c29020b20188051e01478051f401e58a3c0147c8267e3070051ec05e284cba00b0051fc2971835601478051f808d0051fa0d9f84520147b0cdc412d0043a01478051f6204784aa029f30c8262fe402efc22e0051e01478051e01478051e01478051ec016b881fc2160051e01478051e01479815201478051e0147e08a920e0a00d52123103ebc13f803a4a343981ba4042f8b74e26fc8b5182e06822001478051e01478051e0147e817762030051e0147d0492a0bb00988c301b893d80bfe085dc30af831881175000520c078cde0147b098a42471096f00cf6083401478051f22e64824c0147c8193e118402728269201da01478051ea1158051e01478051e01478051e01478051e0147d807360bc8051f22be7896940248051e01478051f6287f01d3e0f2f89d0014798a5a01478051f00e158467812288b0401478051f80c88051e01478051e0147d838f2083c88420147e82c60147a8a480095f88dde22070a74610e0051e0147a0cb6c25350b36e0dab00e640a38051e01478051e0147e041f607d10504c0f90051e01478051e00528051e20a818b6001478051e222b0051ec2f50051e4291582c5a00378030e2dea03a980f1c8bdee0b8280530108b83d9822258045c0ad70208e285e0503a22d8051e20a73898c82fc88481c13940095605848b1a01478051e40578051e01478051e60c1f8a0401478051e809a504c60147889860147e8119e0f5a80f20147d02cc02d70051e01478051f40e5589c342f4200e000028051e01478051e0147d81e401478051ee2b60051ea04f8051e40650051e00c10035922e5384d001478051e01479880401479038c01478051e403a481c40147a00aa01478051f402958a8882ec984fc0147d0348e086603d3a1128051e014790970227bd0c8a0147a0b08407db8d19c0040051e01479094862c450ab3020b001200147c83bf422330a18225e1034201478051e0147b839c00300840801478051e01478051e01478051e40f78012b81190051e008be035401478051f406c80b380147a800001479032e00e030201c0b6d8876a0e80051f021b8051e014780ca5830818d1282faf82e94101b8107c26628c6e02c880387025de0478014780a820147f008282945843360fb180cd42c3c8482014798bf401478051e01479843601478051ee0158051ee3322838801478051f63098051e01478051e60178019001478051e01478051e42da48238c2868051e42897823e014788a60613d4888e0147d01cde333302e7a0510019c0147d8a4f20ff0051e01 else 0x28283e04c0051e214228b6401478051e01478051ee2b26810f221070027611b9045e62b83843c01478051f413d8051ea0c3481ac0147d014801478051f411b0051e0147f8c120147902800147b02c0012c70bb0c100a81c860dd0051fa0d40034c0147d82a20147c844d80668051e822410032225430acda03de0420a127d0aa1a2ed1893ee05a8051e02ac40224c2aee08878287281e801479811a01478051fa2050051e0147e027e232ec0921c0ef604db011dd012980c5901d4006dd8cec227530494606140101a0f30093b612f681b80003b81e12051e895a00de502766013f89fd42eea040b40ae200f1c01950189e02a60caa2146c823781270051e01478051f607b8051e0147d80de0147d081c01478051e0147989c00147b8cd26216c8c1aa29a2026b80410051f60900051e20328051f80f6a04dd40d6982f82027009f701293013940c68051f40b890cd5c125801980147900c80147f0404a10688a03a14570008a0a7902f7e09738427a0fcc04f001478051f60de8051f8055082bb220d8051fa278c09800147b835e202d8051fc026a89b5e098b850001478051e212198376612fa826ea06ab817ac0c90051e0147d0995c27fe08820147902dec01460b1f00aa183b60147e83ce0147a035c80a4b032960628051e0147904e8c2090051f021af0993a23108035a0b3b816dc07f0051f6295001080028b00b921330051f403b8051e0147d005842f60051e01478051f028e0051e003b0051fe27e9036c01478051e20688051e01478051fa2fd8051e014780af00147a0c5a20a41894001479046801479837e805a0051e0147c8b712219f004bc28a10947220388a5ea077d81eba037401d8c00ee00ce40b4d02ca02fff001fa347109ce0147b0b4b010c38a9780d3e84a60147c882980950051e01478051e01478051e01478051f20c508c6560e2f00d601478051e01478051ee2bab032ce21b182bc0147d00d121162004000b61000240cfa00c3e2e0e03f480a60051fe2560051e0147c8d1601478051e0147b8c1f02790051ee01a8051e222a8051ec0b5d00d9a20ef831c01478051e01478051f208690c10a0558051e0147f832a0147c02ac4038b8345c2610051f801d30164e05f483e3c1212095c0147f046a209230))
def fR5H1_37 (h : Nat) : Option (Nat × Nat) := lookupWord 335 1527 11 18 10 4 fR5H1_37F h
def fR5L40F (i : Nat) : Nat := 0x37daa8e432e20002e2ed95398413007fe54600
def fR5L40 : PackingT := (1,2,7,7,fR5L40F)
def fR5H1_40F (i : Nat) : Nat := 0x188ec24a882015005401578a9412982402f204e01500540150054015005401520a52220054c0d805460f0054611005580b6829607d8b28118054015404cc0e10d02108003e2478ada2e80b0c0ad8a3c0f9001405f08de0ed03082628aaa03002f82b805401500544070055227605360100540048055e14005582d700ee0800554020054c123811e30a8a7c20701b609a832a2fe8ca60d18072100819202c022e0500540c085020c6800010185000020100282800608384
def fR5H1_40 (h : Nat) : Option (Nat × Nat) := lookupWord 23 93 7 14 6 4 fR5H1_40F h
def fR5Levels : Nat → PackingT
  | 28 => fR5L28
  | 31 => fR5L31
  | 34 => fR5L34
  | 37 => fR5L37
  | 40 => fR5L40
  | _ => emptyPackingT
def fR5Idx0 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def fR5Idx1 : Nat → Nat → Option (Nat × Nat)
  | 31 => fR5H1_31
  | 34 => fR5H1_34
  | 37 => fR5H1_37
  | 40 => fR5H1_40
  | _ => fun _ => none
abbrev T5_bkT := blockU fR5Levels fR5Idx0 fR5Idx1
abbrev T5_bmT (k tm s a b : Nat) := @blockU_merge fR5Levels fR5Idx0 fR5Idx1 k tm s a b
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c28_0 : T5_bkT 9 1 0 48=true := by
  apply cellsBlockU (ar:=9) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T5_a28 : T5_bkT 9 1 0 48 = true := T5_c28_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c31_0 : T5_bkT 10 1 0 8=true := by
  apply cellsBlockU (ar:=9) (d:=0)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c31_8 : T5_bkT 10 1 8 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c31_56 : T5_bkT 10 1 56 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c31_104 : T5_bkT 10 1 104 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c31_152 : T5_bkT 10 1 152 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c31_200 : T5_bkT 10 1 200 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c31_248 : T5_bkT 10 1 248 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c31_296 : T5_bkT 10 1 296 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c31_344 : T5_bkT 10 1 344 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c31_392 : T5_bkT 10 1 392 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c31_440 : T5_bkT 10 1 440 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c31_488 : T5_bkT 10 1 488 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c31_536 : T5_bkT 10 1 536 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c31_584 : T5_bkT 10 1 584 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c31_632 : T5_bkT 10 1 632 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c31_680 : T5_bkT 10 1 680 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c31_728 : T5_bkT 10 1 728 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c31_776 : T5_bkT 10 1 776 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c31_824 : T5_bkT 10 1 824 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c31_872 : T5_bkT 10 1 872 7=true := by
  apply cellsBlockU (ar:=10) (d:=0)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T5_a31 : T5_bkT 10 1 0 879 = true := (T5_bmT 10 1 0 440 439 (T5_bmT 10 1 0 200 240 (T5_bmT 10 1 0 56 144 (T5_bmT 10 1 0 8 48 T5_c31_0 T5_c31_8) (T5_bmT 10 1 56 48 96 T5_c31_56 (T5_bmT 10 1 104 48 48 T5_c31_104 T5_c31_152))) (T5_bmT 10 1 200 96 144 (T5_bmT 10 1 200 48 48 T5_c31_200 T5_c31_248) (T5_bmT 10 1 296 48 96 T5_c31_296 (T5_bmT 10 1 344 48 48 T5_c31_344 T5_c31_392)))) (T5_bmT 10 1 440 240 199 (T5_bmT 10 1 440 96 144 (T5_bmT 10 1 440 48 48 T5_c31_440 T5_c31_488) (T5_bmT 10 1 536 48 96 T5_c31_536 (T5_bmT 10 1 584 48 48 T5_c31_584 T5_c31_632))) (T5_bmT 10 1 680 96 103 (T5_bmT 10 1 680 48 48 T5_c31_680 T5_c31_728) (T5_bmT 10 1 776 48 55 T5_c31_776 (T5_bmT 10 1 824 48 7 T5_c31_824 T5_c31_872)))))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c34_0 : T5_bkT 11 1 0 1=true := by
  apply cellsBlockU (ar:=9) (d:=0)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c34_1 : T5_bkT 11 1 1 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c34_49 : T5_bkT 11 1 49 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c34_97 : T5_bkT 11 1 97 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c34_145 : T5_bkT 11 1 145 48=true := by
  apply cellsBlockU (ar:=11) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c34_193 : T5_bkT 11 1 193 48=true := by
  apply cellsBlockU (ar:=11) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c34_241 : T5_bkT 11 1 241 48=true := by
  apply cellsBlockU (ar:=11) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c34_289 : T5_bkT 11 1 289 48=true := by
  apply cellsBlockU (ar:=11) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c34_337 : T5_bkT 11 1 337 48=true := by
  apply cellsBlockU (ar:=11) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c34_385 : T5_bkT 11 1 385 48=true := by
  apply cellsBlockU (ar:=11) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c34_433 : T5_bkT 11 1 433 48=true := by
  apply cellsBlockU (ar:=11) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c34_481 : T5_bkT 11 1 481 48=true := by
  apply cellsBlockU (ar:=11) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c34_529 : T5_bkT 11 1 529 48=true := by
  apply cellsBlockU (ar:=11) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c34_577 : T5_bkT 11 1 577 48=true := by
  apply cellsBlockU (ar:=11) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c34_625 : T5_bkT 11 1 625 30=true := by
  apply cellsBlockU (ar:=11) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T5_a34 : T5_bkT 11 1 0 655 = true := (T5_bmT 11 1 0 289 366 (T5_bmT 11 1 0 97 192 (T5_bmT 11 1 0 1 96 T5_c34_0 (T5_bmT 11 1 1 48 48 T5_c34_1 T5_c34_49)) (T5_bmT 11 1 97 96 96 (T5_bmT 11 1 97 48 48 T5_c34_97 T5_c34_145) (T5_bmT 11 1 193 48 48 T5_c34_193 T5_c34_241))) (T5_bmT 11 1 289 192 174 (T5_bmT 11 1 289 96 96 (T5_bmT 11 1 289 48 48 T5_c34_289 T5_c34_337) (T5_bmT 11 1 385 48 48 T5_c34_385 T5_c34_433)) (T5_bmT 11 1 481 96 78 (T5_bmT 11 1 481 48 48 T5_c34_481 T5_c34_529) (T5_bmT 11 1 577 48 30 T5_c34_577 T5_c34_625))))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c37_0 : T5_bkT 12 1 0 14=true := by
  apply cellsBlockU (ar:=10) (d:=1)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c37_14 : T5_bkT 12 1 14 28=true := by
  apply cellsBlockU (ar:=11) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T5_a37 : T5_bkT 12 1 0 42 = true := (T5_bmT 12 1 0 14 28 T5_c37_0 T5_c37_14)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T5_c40_0 : T5_bkT 13 1 0 1=true := by
  apply cellsBlockU (ar:=10) (d:=0)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T5_a40 : T5_bkT 13 1 0 1 = true := T5_c40_0
theorem tablesfR5 : ∀ k ≤ 13, ∀ tmax ≤ 1, blockU fR5Levels fR5Idx0 fR5Idx1 k tmax 0 (fR5Levels (3*k+tmax)).1 = true := by
  intro k hk tmax ht
  interval_cases k <;> interval_cases tmax
  · exact (rfl : blockU fR5Levels fR5Idx0 fR5Idx1 0 0 0 0 = true)
  · exact (rfl : blockU fR5Levels fR5Idx0 fR5Idx1 0 1 0 0 = true)
  · exact (rfl : blockU fR5Levels fR5Idx0 fR5Idx1 1 0 0 0 = true)
  · exact (rfl : blockU fR5Levels fR5Idx0 fR5Idx1 1 1 0 0 = true)
  · exact (rfl : blockU fR5Levels fR5Idx0 fR5Idx1 2 0 0 0 = true)
  · exact (rfl : blockU fR5Levels fR5Idx0 fR5Idx1 2 1 0 0 = true)
  · exact (rfl : blockU fR5Levels fR5Idx0 fR5Idx1 3 0 0 0 = true)
  · exact (rfl : blockU fR5Levels fR5Idx0 fR5Idx1 3 1 0 0 = true)
  · exact (rfl : blockU fR5Levels fR5Idx0 fR5Idx1 4 0 0 0 = true)
  · exact (rfl : blockU fR5Levels fR5Idx0 fR5Idx1 4 1 0 0 = true)
  · exact (rfl : blockU fR5Levels fR5Idx0 fR5Idx1 5 0 0 0 = true)
  · exact (rfl : blockU fR5Levels fR5Idx0 fR5Idx1 5 1 0 0 = true)
  · exact (rfl : blockU fR5Levels fR5Idx0 fR5Idx1 6 0 0 0 = true)
  · exact (rfl : blockU fR5Levels fR5Idx0 fR5Idx1 6 1 0 0 = true)
  · exact (rfl : blockU fR5Levels fR5Idx0 fR5Idx1 7 0 0 0 = true)
  · exact (rfl : blockU fR5Levels fR5Idx0 fR5Idx1 7 1 0 0 = true)
  · exact (rfl : blockU fR5Levels fR5Idx0 fR5Idx1 8 0 0 0 = true)
  · exact (rfl : blockU fR5Levels fR5Idx0 fR5Idx1 8 1 0 0 = true)
  · exact (rfl : blockU fR5Levels fR5Idx0 fR5Idx1 9 0 0 0 = true)
  · exact T5_a28
  · exact (rfl : blockU fR5Levels fR5Idx0 fR5Idx1 10 0 0 0 = true)
  · exact T5_a31
  · exact (rfl : blockU fR5Levels fR5Idx0 fR5Idx1 11 0 0 0 = true)
  · exact T5_a34
  · exact (rfl : blockU fR5Levels fR5Idx0 fR5Idx1 12 0 0 0 = true)
  · exact T5_a37
  · exact (rfl : blockU fR5Levels fR5Idx0 fR5Idx1 13 0 0 0 = true)
  · exact T5_a40
def fR6L24F (i : Nat) : Nat := 0x3b325c4549812e58254600
def fR6L24 : PackingT := (1,7,7,3,fR6L24F)
def fR6L27F (i : Nat) : Nat := 0x142ec575b0800d6287952100000d628755218566615c4a38332e29241200daba64b0eb2ae2a8c0187bdba710b960951803676b88c0972c12a3007cd9549812e58254600a3deea172d1304a8c0137b5d432582605518032de972e3106b8aa30065dd2e5c520d7154600cbda5cb8841ae2a8c0197e4b9708835c5518028f7ba85cb4519aa30055ed750b96063354600
def fR6L27 : PackingT := (12,6,7,8,fR6L27F)
def fR6H0_27F (i : Nat) : Nat := 0x100b00
def fR6H0_27 (h : Nat) : Option (Nat × Nat) := lookupWord 1 3 2 9 1 4 fR6H0_27F h
def fR6L28F (i : Nat) : Nat := 0x13405c00d78013a001000090008120014a38332e29171200b9b26cb04a9302a8c01db61b8549814815180259f3ae65301332a3006abc329816026654600976ceb19490466a8c01d760b9549108895180357c194c0b01112a30075d82e5524821154600
def fR6L28 : PackingT := (8,6,7,8,fR6L28F)
def fR6L30F (i : Nat) : Nat := (if i<1 then 0xd902b1e54ea2f148d2a415f5147953a8bc523ca9d45e29182b825ea286c900ac205a002202d0011000a168801c004400e002200d001100000088034004400600358a3055484001c0022bf7bcebb1b88b6bb42b19af0ac7aaaa8da70a53a36a0d9f09c799e97595892f9128f58d88bb89286984c82f7fa7dd7c07af78676974072f71e70d6f06df6da6bd68866b64e6195fc5df5c25a558856b5425255144f74da4b149447745a43d4204033e63d53b838f35a35533831b2f22e12dc2cb29626125c23320a1e11b818f15a14912c10f0f20d50b809b07e06103803302201d000c7fd876c8a954600c7fd87aeca954600a7fdc32a57654600a7fdc22a57654600a7fecc2a5765460097fdc82e56354600c7fda82e5635460097fdc22e56354600a7fdc82a56354600a7fecc2a563546008ffdc3aeda25460097fdc32e58254600a7fecc2a5825460097fdc82e53254600a7fdc82a53254600a7fecc2a53254600fd75875957154600a7fecc2a63354600f5f57161ca954600c7fcb961da654600f67d652a576546008ffccb61da354600c7fcb961da354600c7fcb95d9a354600c7fca96dd6354600a7fcc969d6354600a7fcc968d6354600c7fca9aed63546008ffccb61da254600a7fcc961da254600c7fcb961da254600c7fcb95d9a254600c7fcb92cda254600c7fcb95cda2546008ffccb58da254600c7fcb958da254600a7fcc96e98254600ef6d522e98254600a7fdca2e58254600c7fdba2e58254600b7bdc42e58254600f3f5812e58254600a7fcc969982546008ffccb68d8254600a7fcc968d8254600a7fcc96898254600c7fcb96898254600c7fca9aed8254600c7fca96cc8254600e5fca95cd7254600c7fca96e16254600c7fca96dd6254600e6fca95d96254600e6fca958d6254600e7eca96096254600a7fcc96e93254600c7fca96e13254600a7fcc96a13254600c7fcb96a13254600c7fca96dd3254600a7fcc969d3254600c7fca96d93254600a7fcc96993254600a7fcc968d3254600e7dca95cd3254600a7fcc96893254600e7eca96093254600c7fca9aed3254600c7fca96e03254600b7f4c961d8154600d7f4b95cd8154600b7f4c958d8154600faf58658d8154600b7f4c96098154600b7f4c94c98154600d7f4b94c98154600fbe5824c98154600e5fca961d7154600fe75656197154600d7f4b960d7154600d7f4b920d7154600bef5c620d7154600bf75c520d7154600bfb5c420d7154600bfe5c220d7154600ff65526097154600d7f4b9a217154600c7fcb961eaa54600c7fcb95daaa54600c7fcb958eaa54600c7fcb960aaa54600c7fcb94caaa54600a7fcc969a33546008ffccb68a3354600a7fcc968a3354600c7fcb968a3354600b7f4c96063354600d7f4b96063354600b7f4c95c63354600a7fcc9aaa3354600 else 0x707b04518008068228c034174400e0ba08a300100d10018168800c00c0052d8600605a004300d03e036180691688000004400605a200100d10018168801c0488d8600201a20440b9b361800806c800c0b6aa7400600208e202db0003d18008238800411c401a002200d001100680081b0c0340040d8601a002200100d1001800c6286c90034004401a002270008068008228c000004401a00206c3700081706c002d8ad6c202e08001c004400213361c0da400700110038008800c006b15400801a002200100d1216cc30801c004400e002200d9861006a16cc70e6d90dc4e00100700110038008800c006ad8600e002200700110038008801c004400e002298624510038008a638201a002200100d25f1801e549801149000079522174e291654b800368f2a420e290802823c413801015c1782e75148000d)
def fR6L30 : PackingT := (100,5,7,12,fR6L30F)
def fR6H0_30F (i : Nat) : Nat := 0x18833014019a0500301261601920840ac0de11006018e00e0e018018010c05
def fR6H0_30 (h : Nat) : Option (Nat × Nat) := lookupWord 5 19 5 12 4 4 fR6H0_30F h
def fR6L31F (i : Nat) : Nat := (if i<2 then (if i<1 then 0xb7d4c95c63354600afd8cb6823354600e7d8c96823354600afdacc6823354600afd9ca5823354600eed9a65823354600fe59655823354600afd9ca4823354600afd8ca4823354600efc9a24823354600ff49524823354600e7d8a94423354600f7d0a94423354600bfd1c84423354600bfd1c74423354600ff51654423354600ff51524423354600bfd2cc4423354600a7dcc9aaa3354600afd9c0aaa3354600efd110aaa3354600e6dca999a3354600eed9a099a3354600fe595099a3354600fed11099a3354600a7edc22a62254600a7ecc968a2254600c7ecb968a2254600d76cb954a2254600afe9ca4822254600bf69c54822254600d7f0b94422254600ff61524422254600afe9c02ea2254600a7eccb2a62254600a7edc82a62254600a7edc32a62254600a7eecc2a62254600a7ecc96a22254600a7ecc969e2254600a7ecc969a2254600bf69c02d62254600b76cc95962254600a7ecc968e2254600b7e4c96062254600afe8cb6822254600e7e8c96822254600afeacc6822254600afe9ca6022254600afe8ca6022254600ebe9a86022254600fbe1816022254600afe9ca5822254600eee9a65822254600fe69655822254600e7e8a95422254600bf68cb5422254600f768a95422254600bf69c65422254600ff61815422254600ff61715422254600bf6acc5422254600afe9ca4c22254600e7e8a94c22254600efc9a34c22254600e7e8a94422254600f7e0b94422254600f7e0a94422254600bfe1c84422254600ff60b54422254600ff61654422254600bfe2cc4422254600a7ecc9aaa2254600afe9c0aaa2254600ef6950aaa2254600efe110aaa2254600e3eca9a222254600ebe9a0a222254600fbe110a222254600e5eca99de2254600ede9a09de2254600fd69509de2254600fde1109de2254600e6eca999a2254600eee9a099a2254600fe695099a2254600fee11099a2254600e7cca98ce2254600efc9a08ce2254600ff49508ce2254600ffc1108ce2254600a7f5c82a61154600a7f5c32a61154600a7f5c22a61154600a7f4c96a21154600a7f4c969e1154600a7f4c968e1154600a7f4c968a1154600b774c954a1154600d774b954a1154600aff1ca6021154600ebf1a86021154600aff1ca5c21154600edf1a75c21154600aff1ca4c21154600e7f0a94c21154600efd1a34c21154600aff1ca4821154600d7f0b94821154600efe1a24821154600ff61524821154600d3f4b9a221154600e3f4a9a221154600ebf1a0a221154600fb7150a221154600d5f4b99de1154600e5f4a99de1154600edf1a09de1154600fd71509de1154600d7d4b98ce1154600e7d4a98ce1154600efd1a08ce1154600ff51508ce1154600d7e4b988a1154600e7e4a988a1154600efe1a088a1154600ff615088a11546008ef9c62e92054600 else 0xef69a75492054600ef69a35492054600ff60c15492054600bf6acc5492054600cff0ba6052054600dbf1b86052054600ff61526052054600efe1a25c52054600ff61525c52054600afe9ca4852054600cfe9a2aed2054600df6952aed2054600a7f9c22a51054600a7f8c96a11054600a7f8c969d10546008ff9ca6cd1054600c7f8a96cd1054600a7f8c968d10546008ff9ca6c91054600a7f8c96891054600b7f1c22a51054600cff0ca6e11054600def0c66e11054600df70c56e110546009ff2cc6e11054600b7f0c96a11054600b7f0c969d1054600b7f0c96991054600f770a95951054600df71b85951054600df71b75951054600fe71865951054600fe71765951054600bf72cc5951054600b7f0c96cd1054600b7f0c968d10546009ff1cb20d1054600aff1ca20d1054600bdf1c720d1054600bef1c620d1054600bf71c520d1054600bfb1c420d1054600bfe1c220d1054600b7f0c968910546009ff1cb2091054600bf71c52091054600fe71655891054600f770a95491054600df71b85491054600fd70c75491054600bf71c65491054600ff61825491054600ff61725491054600bf72cc54910546009ff1cb0c91054600aff1ca0c91054600bbf1c80c91054600bdf1c70c91054600bef1c60c91054600bf71c50c91054600bfb1c40c91054600df7152aed1054600a7f4c9606aa54600a7f4c95c6aa54600ee7965582aa54600ef6952482aa54600aff1c8442aa54600aff1c7442aa54600ef7165442aa54600ef7152442aa54600a6fdc82a66654600a6fdc32a66654600a6fdc22a66654600a6fecc2a666546008efccb6a26654600a6fcc96a26654600a6fcc969e6654600a6fcc968e6654600a6fcc968a6654600b67cc954a6654600e6f8c96826654600aefacc6826654600aef9ca6026654600aef8ca6026654600eaf9a86026654600faf1816026654600aef9ca5c26654600aef8ca5c26654600ecf9a75c26654600fcf1715c26654600e6f8a95426654600f678a95426654600fe71815426654600fe71715426654600be7acc5426654600aef9ca4c26654600e6f8a94c26654600eed9a34c26654600aef9ca4826654600aef8ca4826654600be79c54826654600eee9a24826654600fe69524826654600f6f0a94426654600bef1c84426654600bef1c74426654600fe71524426654600a6fcc9aaa6654600aef9c0aaa6654600ee7950aaa6654600eef110aaa6654600e4fca99de6654600ecf9a09de6654600fcf1109de665460097bdc42e63354600a7ddc32a63354600a7dcc968e3354600c7dcb968e3354600afd9ca4c23354600e7d8a94c23354600afd9c02ea3354600b79dc42e63354600a7dccb2a63354600a7ddc22a63354600a7decc2a63354600a7dcc969a3354600a7dcc968a3354600b7d4c96063354600) else (if i<3 then 0x574558154c54e1524538149c50a13e44e8135c4c612d44a4127c49a122446c116c44a10e4428105c41210043f00f7c3da0f543d00efc3960e143800dec36a0d943600d6c3560d143400cec3360c943140c0c2fe0be42f40b8c2de0b642d40b0c2be0ae42b40abc2aa0a642940a3c27e09b4268098c252090423c08dc22608541f8079c1ca06e41a8065c18605d4164054c14204f412c046c10a03e40e8035c0c603040bc02dc0b2028409c025c092020407c01dc072018405c015c052010400087fecc6cca954600c5fcc76c8a95460087fecc6c8a95460087fdc82e5a65460087fdc32e5a65460087fdc22e5a6546008ff9c0aeda65460087fcc96e9765460087fdc22e5a35460087fecc2e5a35460087fcc9aeda3546008ff9c0aeda35460087fcc96e9635460087fdca2e5635460087fdc82e5a25460087fdc32e5a25460087fecc2e5a254600c5fcb92dda254600cdf8b76c1a25460087fcc9aeda2546008dfdc7aeda2546008ff9c0aeda25460087fcc96e9825460087fdca2e5825460097bdc42e5825460087fdcb2a5825460087fcc96e8825460087fdcb2a4825460087fcc96e9725460087fcc96e9625460087fcc96e9325460087fdca2e5325460087fdcb2a5325460087fcc96e8325460087fdcb2a43254600c3fca96e03254600c5fca96dc3254600c6fca96d83254600c77ca96d43254600c7bca96d03254600c7f4a96c43254600c7f8a96c03254600bf71c02d58154600b3f4c96098154600d774b95498154600fb65825498154600def0b66c18154600df70b56c1815460097f4c9aed81546009ff1c0aed815460097f5c82e5715460097f4c96e17154600b5f4c961d7154600b774c95957154600fc75765957154600fd657254971546009ff1c0aed715460087fcc96e9315460087fdca2e5315460087fdcb2a5315460087fcc96e92154600a7f8c96d9a054600a7f8c96cda054600a7f8c96c9a0546008ff9cb209a0546008ff9cb0c9a054600abf9c80c9a054600adf9c70c9a054600aef9c60c9a054600af79c50c9a054600afb9c40c9a054600aff1c10c9a054600fe71655c56054600c7f8c96e930546008ffacc6e93054600c7f9cb2a53054600e7d9c32a53054600a7f9c22a53054600a7facc2a53054600a7f8c96993054600e7d8a968d3054600a7f8c968d3054600e7d8c968d3054600afdacc68d3054600a7f8c96893054600efd1a36053054600afd9ca4c53054600e7d8a94c53054600c7f8a9aed30546009fb9c4aed3054600cfd9a3aed3054600c7f8c96e92054600cdf8c76e920546008ffacc6e920546008ff9c82e920546008ff9c32e920546008ff9cb6a120546008ff9cb68d2054600a7f8c96892054600e7e8c96892054600ede8c76892054600afeacc6892054600fd68c75492054600df69b75492054600 else (if i<4 then 0xd600006700d70000118008400420021d000e80074003a001d0008026800b400210da0020b9d00128d000882674004b3000220010809840380ae4680149b30002200d0ecc0008803420d98001168007400200a198e0e800400021d000864e800b4003a0010c50b6d00186284c6800c004200e1d0008340021b3a002d000e8004000f5082d001816e800b4003a0010d9d001680040000a0800840042131a0029980011000843174004002100a08616800830b4004000018400c2006102c0e80042a74005a001d0008000c20061010d001680074003a001d000e800740020061008d00168006013400401410a9d001680074003a001d000800234005a001d000e80074003a001d00081c002e001000000000de400520012459001480040342a0015000a80054002a0010002dc24465522200080040055222000800000005301b98090004b14216c5044464004282090004002a90954840a0010000003000404011263815c0b8b20015000a8004a6037301058004866c00448b20029000a80054002a00150008000010004058a12820a120019000400015484aa420001400200000c0016000922c80094002a001500096284a0822001002c00246d20029000c80054002a0015000814002a001500080002b608649119548c8002001000400000a0820000a6037301200080002a90800050008000001800200300058002003000580020030005800246d20029000922c80094002a0015000a80054002a0012b6090004040012980dcc04800258a11000900040000180020001800200018002000180021ea09405ba340185808dfd67dc5f307bbdea27a45e5c783ddda75a5d58748dce27255c48707dbde6f35b5c6badada6ac5a6468bd9e266b595464ad90263658a4615d8225f257705c5d6be599560c56cd57e55b5538543d49e520547c51ad46650f54144fad3c24d752f84bcd2be49f522447ed1ea47651c846dd1a6465518445cd1564515128442d0ee43450b4428d092417504040bd0124004ffc3f7cfce3ef4fac3e6cf8a3e14f743d8cf463cd4f243beced23b04eb03a7ce9a3a24e6c396ce4a3914e40385cdfa37a4dd836ecdaa3694da0363cd7e35b4d5034ccd223414cf4338ccc632a4ca4327cc8e31f4c6c316cc4a30b4c1c302cc062fd4be42f1cbb62e94b942e0cb722d84b502cccb222c14af42b5cac62ad4aa42a4ca8e29c4a60293ca3e28b4a1c282ca0627d49e4277c9da27549d0272c9c626a499825ec96a256494824dc926245490423fc8fa23a48cc22ec8b622c4894220c87e21e487421bc86a2194854210c83220847ec1f6c7ca1f147c01ebc79e1e647881e0c77e1de47741dbc75e1c7470c1bec6ea1b646c81b0c6b21a54678199c6561914634188c61e1864614183c5fe17e45e816fc5ae16a45a4167c58e15f457815cc56e1 else 0x6304703701101900d001007006003d0058187cc009806e80003981901240dc02406404c02b401008a00003001c01a505f04500001800d282f82280c00700000399c00201a00ee00002405f0450360180000073006803000d801018c1180dc09006403c01c00dc012e00100d007700001201700c005580001941140d8000060038034c0be08a06c00003001a600d001b00181838038c38700696c0020c809206e01803201e00e006e009030f5ff36e29f18f0ed06f00e024b8004035c00004605c05403001d600006604412105702e202281b00c00700000398036619c0000480be08a06c00003001c01a700d7000011806b800008c035c00004605c031600006405f0450360180000073006cc33800009017c1140d8000060038034e0c2c8ac6cc00c3001c01a704865f63660061800e00d381e32fb22b0030c0070069c02197d9158d9860038034e03ccbec8ac6cc0001c01a765f64563660061800e00d3806cc318000090180207a05c01ae00406d04d700192c026fa281ef9b78c006f8778026aa6c00407000800f4036c00607a01ae0030440d9700180281eb800c5740f7d7fc63c3bc03c182e5029001bebfe6de31e01e1c1b280006803b80000900b806002ac0000ca0be08a06c03)))
def fR6L31 : PackingT := (360,5,7,14,fR6L31F)
def fR6H0_31F (i : Nat) : Nat := 0xa0b91640100c20600700c60000c00c00c00c317711d1080831002
def fR6H0_31 (h : Nat) : Option (Nat × Nat) := lookupWord 4 16 5 12 4 4 fR6H0_31F h
def fR6H1_31F (i : Nat) : Nat := 0x8000008602201a04106a05203008c07200
def fR6H1_31 (h : Nat) : Option (Nat × Nat) := lookupWord 3 11 4 12 4 4 fR6H1_31F h
def fR6L33F (i : Nat) : Nat := (if i<1 then 0x441becd87a80d286661c1b406900682d40140162906300d2000bb00629c04612444b0062901b808c61a16948c018a7011817600c522e44160207a705d803148b91058081e9f000b9c538081e9406c2d0798031498e9058091803148f7c040f4bc00892c5180d05ac0060348002ec018a7011806892401401afab6300d2000bb00629c04601a249005002a0d14c0348002ec018a441602380d40140022336280d10c8028011221c630d80162b45c53808c03500500224b1447106398ec018a701100690005d80314e02302ec00b7dafe29c04034f2a5800762bef1554e293b5d07b8a47b9006cdf600182afe2934a96005883b15fc526952c003e55f68b8a4c03654b000ed57d9b6293ca90edc00afe290da6952c02afe2921c505caa714f008046952c002b85e1b3517149e54b000af517149406ca9600366a2e290ae7952c002b85ea8acdb149e54b000ae12ea28d9c527952c00a804ba8b8a4d2a58005738b517149806b0005d000629406b0005d00080341740085acd8a0358002e800401ac0017400200d05ac00603500500088cd8a0350050058ac18aaa416d006bf8a4aaa68005768b8a4a0350050005c48e6c6722ed14587f430a139055801bec5ed4f4477ebb31cdee126f636edb40d6f699b409976c74616af99728b425832aa54daa47510a76932694c482a2cd0ee8303f49e5cecc71f36699ecc946032de15d4a464dc25591908243d61c20cc85c029912908583ca1a90bc051c2420e505481b4062000effb0e54aa3006ffd8769951803bfe54aeca8c01bff61da354600dffaecd1aa3006ffcba58d51803bfe54ac6a8c017ff6dd6354600dffb4eb1aa3006ffda358d51802fff5dac6a8c01bff61da254600dffaecd12a3006ffcb3689518037feb9b44a8c01bff58da254600dffb74c12a3006ffcba60951803bfe5cb04a8c01dff2a58254600dffb4cc12a3006ffda3609518037fed1304a8c017ffaed8254600bffb66412a3007dfd735c951802ffedc2c4a8c017ff6dd6254600fdfaecb12a3007efd6358951803ff6c12c4a8c01bff6e93254600eff952992a3005ffdb84c9518037fed4264a8c017ff6dd3254600dffb4e992a3005ffdb64c9518037fed3264a8c01bff68d3254600ffbae6992a3006ffda24c951803ff6c1264a8c017ffaed3254600bffb70192a3007ff58760551803ffabb302a8c01ffd2cd8154600ffeb06c0aa3007ff57360551803ffab1b02a8c01ffd6098154600ffea64c0aa3007dfd875c551803ffac32e2a8c01ffd60d7154600ffe906b8aa3007ff5635c551803ffac12e2a8c01ffd4c97154600ffed10b8aa3006ffd87aa9518037febb554a8c01bff58eaa54600dffb05552a3006ffd32aa951803bfe54c66a8c01bff69a3354600dffb4519aa3007ff5818cd51803ffab8c66a8c01bffaaa3354600 else 0xb436aa901b400ac0022047a6c405ac001e8d8007b08f43880346eb006bb00287190003e05c8b69b1406a2d600301a40017600c53808c035005000aed145b536380d4014001f0b6a6c438e0348002ec018a7011a000c51b231bad76000c5a0c0f4cc3b80030a0c401a33980150800315a2d06400d6000fe004c516ccda8323802c556c30c3c0017223206105c205a1b58000d2)
def fR6L33 : PackingT := (72,4,7,13,fR6L33F)
def fR6H0_33F (i : Nat) : Nat := 0x203a02670240066802e804483470a18078020f8195061804ec1e504ae035e08d013081f801ae00bc078031b00600bd803402c4031202b004a82ee07de096c13a805600e0193c10502dd0816070025b811006c61190091848809da26c4007038506ba075822b8422036e05380a9817107200ec0320847e008e13585d3051301940a1c21e8495056a0a7827e001704380ea02270228021e0fe01900371055e0f403228163c0033003281021c00b0002004a668000020c253850604800
def fR6H0_33 (h : Nat) : Option (Nat × Nat) := lookupWord 28 87 7 15 7 4 fR6H0_33F h
def fR6L34F (i : Nat) : Nat := (if i<2 then (if i<1 then 0x44151803ff8d4220a8c01ffc6dd1054600ffe34e882a3007ff18744151803ff8d3220a8c01ffc6191054600ffe2ec882a3007ff18544151803ff8b2a20a8c01ffc6cd1054600ffe346882a3007ff18344151803ff841a20a8c01ffc5cd1054600ffe2c6882a3007ff15344151803ff8d9220a8c01ffc6891054600ffe304882a3007ff08244151803ff8b9220a8c01ffc5891054600ffe2a4882a3007ff13244151803ff819220a8c01bfd606aa54600dfeae3552a3006ff960aa9518037fc98554a8c01bfe482aa54600edf953332a3006efda89995180377ed3ccca8c01bbf68e6654600ddfb45332a3007e7d5299951803f7ac0ccca8c01fbd5c66654600fdf341332a3007ef98099951803f7cb84cca8c01fbe5426654600fdf261332a3007ef9209995180377f554cca8c01f3f9de6654600aff97319aa30067fca98cd518037eed1c66a8c01bfe6823354600ffb26119aa3007ff1108cd518037ee5d466a8c01df72e63354600efb95319aa3006fdda68cd518037eed1466a8c01ff56063354600ffaae319aa3007fd9a08cd51803fecb0466a8c01ff64823354600ffb22119aa3006fdeaa8cd51803f6f33466a8c015ff2e62254600cff953112a3006feda288951803fb6a9444a8c01bfe6822254600fef2a1112a3007fe92088951803ff888444a8c01bfb2ea2254600efd973112a30077eca9889518037f6d4444a8c01bfb69e2254600dfdb4d112a3007f6cb588951803fb6b2c44a8c01bfb68e2254600ffcb03112a3007fe57188951803ff4d0444a8c01ffa6022254600ffd2e1112a3007fe96088951803ff4a8444a8c01ffa4c22254600ffd221112a3006feeaa88951803df744444a8c01f7b9de2254600fddccd112a3007fce33889518037fad4422a8c01bfd69e1154600dfeb4708aa3006ff5a284551803fbaa9422a8c01ffc6021154600ffe2e108aa3007ff13084551803ff890422a8c01efda221154600fbecef08aa3007fd63384551803ff311422a8c011ff6cca9546008ffb6454aa30047febb2a5518023fe5cb4ca8c011ff2e5a3546008ff972d12a30057f4b960551802bfa5cae2a8c019fe2e5a0546009ff576d02a3004ff9ba5815180377cd32c0a8c01f9e59560546009ff374982a30067f8a94c1518037ecd1a60a8c013fe6e920546009ff174902a3006fe9a248151803fb4a9240a8c019fe2a51054600efe152882a3005ff1b844151802ff8dba20a8c01fdc5951054600fee2a4882a3005ff2bb441518023fe5cd54a8c013fe6c2aa54600dfe221552a30066fca99995180377cd04cca8c01f9e5426654600fde221332a30067dca98cd518037ecd0466a8c01ff44423354600cfd953112a3006fe9a088951803fb4a8444a8c01ff84422254600afe97308aa30067f4a9845518037f8d0422a8c01fdc5421154600 else 0x6d024c03d405c80880098009800057fdb32a551802bfed9152a8c019ff6d8a954600cffb6654aa30067fdb22a551802bfe5cb4ca8c019ff2a5a654600cff972d32a3004ffebb699518027fedd2eca8c019ff2a57654600aff972d1aa30067fca968d518033fe5cb46a8c01bfe6c1a3546009ffd76d1aa3004ffdba58d51802bfe5cac6a8c019ff2a56354600aff972d12a30067fca9689518033fe5cb44a8c01b7f2dda254600dff360d12a3004ffebb689518027fedd304a8c015ff2e58254600cff952c12a3004ffdba209518033fe54904a8c017fd6c48254600bff360412a3004ffdba5c9518033fe54ae4a8c013ff6e96254600cff952b12a3006efda6589518027fedd264a8c015ff2e53254600cff952992a3004ffdba0c9518033fe54864a8c016ff6e03254600bbfb6e192a3005efdb60c951802fbeda864a8c017ef6d03254600bfeb62192a3005ff9b00c9518033fe54b02a8c01dfd2a58154600fde96cc0aa3006ff5a660551803dfac3302a8c01fdd2d58154600dfeb46c0aa3007bf58260551803fbaa9302a8c01ffc6c18154600bfed76c0aa30067fca95c551803bfa54ae2a8c017fd6e17154600fbeb0eb8aa3007df5765c551803fbab2ae2a8c01bfd6897154600fbeae4b8aa3007f75525c551802ffb5dae2a8c013ff6e93154600aff97298aa30067fca94c5518027fedd242a8c019ff2a52154600dff34cd02a3006ff9a3681518037fcd1340a8c01ffc605a054600ffe2e2d02a3006ff9b6681518037fcbb340a8c01bfe6cda054600dff2c6d02a3006ff9b2681518037fcc1340a8c01bfe209a054600dff2e4d02a3006ff962681518037fc99340a8c01bfe0c9a054600dff302d02a3006ff971681518037fc98b40a8c01bfe485a054600bff374b02a3006ff9a858151802ffcdbac0a8c01bfe69d6054600fdf34cb02a3007ef965581518037fcd1ac0a8c01fbe58d6054600dff344b02a3007f795258151803ff8c0ac0a8c01ffc5c56054600dff374982a3005ff9ba4c151803bfc54a60a8c017fe6d93054600dff34c982a3007fd9a34c1518037fcd1a60a8c01bfe6893054600ffe302982a3007ff1714c151803fec98a60a8c017feaed3054600dff374902a3005ff9ba48151802ffcdc240a8c01bfe6a12054600bff36e902a3006ff9a748151802ffcdb240a8c01bfe6992054600fef36a902a3007f796548151802ffcd9a40a8c01bfe68d2054600ffd344902a3006ff9a248151803ff4a9240a8c01fde5492054600ffe302902a3007ff17148151803ff490a40a8c017feaed2054600bff370882a3006ff9a844151802ffcdba20a8c01bfe69d1054600bff366882a3006ff9a344151802ffcd9220a8c01bfe6891054600fef2a4882a3007ff18144151803ff8b8a20a8c01ffc4c51054600ffe242882a3007ff1b8) else (if i<3 then 0x511398100c0e2990580078a6416001e2990580078a641600185f0921ec1b87900c1982683d05818fe2fb6d53469c700dd05402617c2484506e1e80705207e03436fc5f6daa68d01370da0a80482f87a01c0182683d0dbf17db51a01a0b680342f8490020380304d16e0dc36fc5d52c6806cb8600f0be1241b87a00c1341e86df8bedb54b1ab1c03741300805f0920dc3d00101d7201e80d0181b7e2fb6d52c6ac368260122920b42686df8a1db54b1a01ac0140b40685e9aac6825b00391a05a21be3145b08e10d468169c6288e10c3d68d4b830f5a342e060b47bd1a17041be324628b716c21a8d1c07001234321d468437c648c516e2d84751a38b710408c2502da34030e41a8d084300805a1608351a34b805a46a41101c82d23430ec36454d1a20a9a3436460e8020b876d468b0086c82da3441700b68d0c2f87a01c0182603d0d7f17db31a0140b580346f8c516c2384331a05a705ac68497d24a4541c8198d4b860085beb15472866352e0c8a58d4b81a045522e18d100725f4929151ba3640cc698024472df58aad94331a3202408aa58d112f84948a8dd1b20e634c010b7c64ac556ca398d1914a32504c6888086ca04552c68a2e016b1a60044932e016b1a60059700b58d0c16cb863438dcf19d231c45f18b3f150a272c4b488c50f921b343098543096a11fc1958219034200dbfbe7e80fbb9f48be767b98f50de78bc0576e2ec51d50ba8673fae681c8bb8ba70a4df25bcc36ac6c04d695a88b47d67a6cca5950320c631cc441864b0565fdcbe457bb2f0e5d62b95170c2df25ad2b45d662ac685800ae615982ade54eca9414e3a975521aa1b940e28014fcc9f013d2a78a4ede9d25391a6f24d989ac534b26704c9498bd30a25ee4b9096b52c925824aa2948127d24df4972924d236a43c482c8fed1e523af47288de51a4231745f88b59152a27f44b288f910c21fd43c4871d0d0a17b42aa849107f20d841648231038a05640608054fec9fbe3f307dc8fa09f1b3e007b68f651ea43d2879e4f2f1e2d3bf8772ced81d7f3a9c74cce869cf2399872f0e561c9c39027198e201c3038407040e001bf037946e64dbf1b6e36bc6d38d999b0d35fa6bb4d639aa134e068d0d0199e833846670cbb194532286360c4e189731246234c33984c308e6058bf817a92d7a5a5cb38964b2c765880afd15df2b725620aab95262a425444a8614e6296a523ca0e137226824c4097512cf25684a649449258247a48308ed91b5231e457889c11072196431886090a6212c41c082a902f1ffc3f607d90f8c1ecc3cd47878ee91d703a487410e721cae391c7108dfb1baa36bc66c8c0e16f42b4050d895011ba222c438081e0fae1ec43c0072e0e101bb434d86490c5c179c2db05900abe14e427e84cc094c10481e003a506900c0416d82aa048407ec0e501 else (if i<4 then 0x684de0089be1d9db2a96005abf8a7800c2485705b2e354a18b3083ac730090403580b5806a907ac618700d38a96be0f78c70e1b3c00e0b5aff36553c63870d9e00805a5741ef5f76dc63870d9e00948417bafb36b8bc638703de00918bd7c06d45e6dc63870d9e009291d7c1ef18e1c367801c25f5fa8a0f79b718e1c3678026a28d9e0031bfd7c62f4516dcd914898e304380000d602d9700474c48e904034f77c16dc5952862cc00e970035237faf8c5e8a2db9b229131c604770e20c00006b82c02d43083a5c00d018705b400463a8009e2986a00305b40040b6800816d0010b705b4006e6016d0018b705a2da8011e282da00305b400421a80086482da00316e0b6800c495001086a00205aeda800de282da00311d400421a800a80041d0b61ef40080b45c8d9a00416e0ea800c16d0011b605b40060e85bd0018b707540062dc1d2c5a004172a0a800c7bd0012a907436680128d5001198a002b300b442dc16998a00416e042cc500202da002b3043a800c082c5b314008aa6cc5001aa9b31400608a80080802da00358b4004716800816d00100856d40060b46cd0018c901140060b45c882a0040102de800c04058a0035042e6800c16998a00301140040b6800962906a00305b40040202c08620d400aaa68009548d9a00301820a800c0402d15340086d854d001ab6a0021922a6800e800454998a003a0010194004b1680080208280540081d9db2a9a0040960b554d0022a9a00201203002500207676caa68011db500104b55340060b680086caa9a003a001a001a0010094004012800954b98a003a001a001a001a001a001008aa6800c0480c0094008f16800a80068006800402500100478b400740034002d7f14f001b45c53c0060b41d0b6600405a041cc08e600505a02043300230020026be802800da2a00a00361c802800d62b064014008a0983602a0045521d9afe29a005552179a2e29a0050000c01412a91a2273020629c04802801314e02c00305a110910574000b8c0b43225fbbe92522dc546e8dadb4a9432862cc01340d63806c82600402a800c7500182d11cc006040473981b000823e002020239800d8010013364014006b1583200a004552d7f14d0022a968b8a6801008e820600811410f14e0240140098a701600180805a0b81483d231a608768e01aa05a97eefa45b8a8dadb200952862cc20eb1c01806bd62a0030d400816301186a00405a219800c16b00100810c2952c005c0020204322960046004004d7d5b200a00468a80064d00233640140068a7017001a8266d80a801187200a003552d7f14d0022a9096d146cd0028001286c891d05802825523444e604c01022821e29c04802801314e02c003c5380b000f14e02c003c5380b000dafab64014008d15005001b0e4014006b1583200a00460d20a800c1684168 else 0x5002be5149b02c2300b48000d4d002be5149b02c2304381690001aa076e61c702d01a57bef15db39805a034cf7de2bb6730e381680d3b0005c0b08c10e05a40006a02202d600c62cc30eb1c0350c00220b701a4a6c1138700dc042df801c6ff5f08f8a44c71811dc385b80001ab01a0dc3ea5f9aac6907206970c02eead8002e05a0b3cc58e200035177ee282db6cc018c59821c03521b7e2fb6f30c000699cc300106debe11fa28b7e6c09314899e300b68700dc05c01e37faf8c5e8b4db14898e31438000b701ac6340f81f85705c506e0b52fddf492916e282c952c680783f40d61a5c300830005c0b08c10e05a40006a2efdc505b6d980318b30c3ac710601ab0dbf17db79861cc00069faff36e300c387506e000350f15800836f5f08fd145bf361138a44cf18e1d41806e02e00fabe317a28b6e6d8a44c71811dc380000d602d088c68333000ae0b8e0b43204948b7151ba36b6d2a58d5980cc83ac700700c1b64100d600402a37caf8c5e8a2db9b02c131c604770e000035a17ee403d058c690700db0c801257fa2e2907bc6006f0e30dc01402180086ff5f16dcdb14898e3023b870c900003581252fa3663483a6a84db9081bfd7c62f45c522638c08ee1c2dc0000d602d4be9141b82c6348381ea04303ce8b8a78c70e1ea0345ba46ff5f18bd145b736c522638c50e00003581118d15005c40020492fddf092916e2a3746d6d8164a901e0380380663520806b0020151bfd7c62f4516dcdb1482c131c604710ec0400006bd2fdc807a0b18d00e01b6190388b16c5e8b8a41ee98e3023887602c00035a320a46dfebf8a41ee98e3023887602c00035a2f01e6dfebfb17a28b9c53a638c08e21d80b0000d7858dbfd7f62f45059adb9b698e3023887602c00035e07f6ff5fd8bd171483d11c43b0160001ac013b7fafec5e8b8a41ee98e302388760001ad0100bb1483dd31c604710ec04035802c3502db8b2e254a18b3083ac730001ab05ac001eb1861c034d37c3055fe8b8a78c70e01aedb80286ff4566d8a78c70e01bc007aa4ba745c521b78c70e07bc010182af886fd5fe8a0f714f1861c0378027a2e29e31c381e86d01bc01157c1ef18e1cc183)))
def fR6L34 : PackingT := (307,4,7,15,fR6L34F)
def fR6H0_34F (i : Nat) : Nat := 0x7f4215837c05ea13382e006400c80191451c051901521270129031f0c20190032582be02d210fc0ea0d5e00601900326021005de18dc2980640108808a853800100c80190410006400c8a142011f05400c80190032488200c8e06c032006400c80192c3020137073609b06a20af00c9e0d301910aa9000e18a8453018d08ac154032006450520192c54006400c80192864f89600c9e056422280d0060c2c7c1b28b5d066a17642b806430be019382c006400c880a0032301400c9c26900b806400c8a284402006400c801904040064015a0193420780270b40190032006400c80190032082400c98038032788800c80190032006400c94033c5200646096a01f82b006400c8c32bc2d80b200c8e0b682680644032019003240b0c0b201900326009606b0179424300b40340193402a01c70a580e803238da00000103010311000400090007060404010a03010102010002010302040100000000
def fR6H0_34 (h : Nat) : Option (Nat × Nat) := lookupWord 34 167 8 15 7 4 fR6H0_34F h
def fR6H1_34F (i : Nat) : Nat := (if i<1 then 0x690064f885984e60168b170f0259029d803800b40024c81e76072c088a88de80a482ce10ae805a380de010aa209384fac16082bc0021805a384aac1409062005a3054282246073a8965c0e6a06b00b450a1002d1e2e3c16f681d301ca01684103283ec803da2bbc0985813d05ca61356062e0d1c02d040f1d00458555813b610b609c209bd823da2796057f0354c296c0cfe080d023545dce0cad035102cd41c8a0f2f02d802e8c485e2b88134104690625e01b3011f8399429842a58023b809a0039a11790963811402d1a103d05eb0582013542ef90af4086d857440045180b80adc57d20427043202b8053622b2f103f84b6004be24e81687889900f702e0505a005a3c57e2054601d5801402d0016860503823d84b680d33151c83e9421ae218a10d1036ec2242166513ae8222c08d62fe302fd8b5ec29320356052e00f685b4400cd110302db0548a14660aa005a1403f0254b0644883a85254018001de00f00158e0e9f02e4049505b18137a01a2051c05fbc29e00b42835e042f2165017cd8460c5cdc22fa122102124089c03f00b41024002d0016800b4005a080580168c017001b245be6246e038b8985418d20edd0a9100f802d001683012302a6c1ec00f500b4088d701df210f00b4680b40132c119308130b4c802aa23f40b1f0523426c01688083805a002d12010708a404f0c288c07d310e8037800126231c099488c24552820f91241026e0244c2099025b01e3c2a00168a04a682a101a80001803c98c000179812bb04510a7c02d0016800b4005a1424620cc00b4005a3419c016820206817802d0016800b4103f50063404c71884037c02d0016800b4204a802d140b190787053c423fe156a076401d9059601687006d820802d0807c503d783a002d0016830a0b09d145260168a05fb8ae402d122405026b005a8226016820804015402d0e26900b460b59c15a615700a1280da01e8e06690a5005a1c04f411bc110b022441f0016800b43029002d00168b04bb020c02d00168d19db0b7180c8c278d153201f882bf201a903820272c045a0c3b05c3016201a58236a12280202c55bc25c107558abe45b74306706e181a3844f6006417890362c0c40168c024909a845a200d603c250180901013014000440d05c0601401004260000000000004000240400803000040380500c0400804000180480f0000500c0801414060010001b02805014160080e09007008110042f0040502003058010080500424008ac09809060020041e0000300c2404c03030570000409c230001103000018090140603c000341c01c0701001004080081a014100600100c00020090240102016020041a4000000000c0d02c0000004008140402e1a40206c6900c0000000000010045800830050080040b0040b0200c0000100c0500408000100042a0140e else 0x44a2e164d04f882f802d1211ca028880a141c00168f1599819e4095c0141127e03fd014241059042e02c944f7e0750071603ba8241e0008157283f9012560a2309260aae454fc158f093408a30446601dc0718829c4594235f80287815fc10f40bbe04ad84ecc49ac2fa2060a801e854140205102d80bf42b72059e02b481b4863f413da05cd0121422100f7e10fe8085c1302272a020a824584b020daa02e8004901a280a3f12848bb6856ca13f807e4827802d0407fd0319832d04144128b08ee829a80b58116609d005a3c0152081e0a1900cb4544e28ed8097041942520168008420138448342e2908a985474072016820ad005a002d0013170152814fc005c01700b4300c1048642cc112d40239456020f9b10a805a1c0dc42fc315ec058a8118016800b4005a2863482aa8014c0335018040d9f105c0b55021d61211166b003b40660134e116981dfc45c016830ae28b658267400b00b4284248184e153f09708b4b828a62cf00b4603ae42c34060519e4831c85e5614da001984314155c294c06e909c402d00168a106f0067806e0168717fb0864816ec061508258930c1c2c0138008805a002d040d060acf01978568826b5093d84e502ce60b500b4284bc01576330c0458803ec4e04)
def fR6H1_34 (h : Nat) : Option (Nat × Nat) := lookupWord 172 598 10 17 9 4 fR6H1_34F h
def fR6L37F (i : Nat) : Nat := 0x444da290b198c618e0b70e80b00035806dbfaf9ab8d5318c51d8750d83171803bae77f5f717456db368a42c663180b50e80b00035e5b85a1f3bf6febee2d8ba285854c538d11c8730d4360c5c601477f5f717456db368a42c6631863b0e0b50680b000362169beafb8b62e8adb56d9b15314e354c630c751d8710c830da4140406e01837d5f722c5d142c8a43dc6a98c628ec3a0240200036216a916febf5b66d8d5318c51d871ab012010009b00b43cb7f5fb17450b229c6a98c628ec3882809008003d912416a24efdbfafb8b62e8adb56d9b05854c524721c4320d8d1050101b8062dfd7dc8b17450b2290f71aa63182390e809008000d88ecafb8a16e8a54c525c3314c630c751d87600804000690537144b15c2d514a98a6a92e198a631863a8ec3b004020003482a3bfafb8a16e8a54c52cc5318c11c87170412010001b10275f0b7458a698c600ca3b0e219062e08240200036216bbf6febee2d8ba2b6d5b66c54c538d5318c30d4360c41404c760160b5dfb7f5f716c5d14a98a43d66298c618ea3b0e80986c000da0b21c8f42687a36f8bdb2340685a8030dfd7c4423b0e21b06134b71b7c5aa71a034b879bfaf8f48710d8309a1e8dbe2f6d54e34c701b4140dfd7cc51e88ec39067203d0340c1b7c5edaa9c6986a0a46f9523b2befa45216e1d8309a1e8daeff8bdb5538d01b212f5f15c2dc383d367b63571a03568d05a2b7c3ab14b92a58ea3986a191a2e1616844efdbee2d8adb56c4721cc350d54d048d3c080b5dfb7dc5b15b6ad98ea388641aa9a091a78085c05a8d104537f5f1ea2923b0e21b061343d8086df17b6c680d0b636febf62e8b14d1d8750d836345c2edfd7ec5d16b6cda29a1b0680aa9a098ec69d6febf62e8b5b66d14d1d8740554d04c3634ed7f458a70ec18b80b71a40be2486f6a81c0357016f8bdb5528d5048038dfb548e21ab80b7c5edaa946a8258041d0096a85be2f6d54a349ac0d3c28ab38896cc79226b0907ebbb89c66d70651afd168aa644cba4690fe7da39099a0bea5dc2b493388663fc1a68b684921b80b183480be000fff69951803ffd7654600fff68d51803ffd6354600fff68951803ffd8254600fff20951803ffd7254600fff58951803ffd3254600fff0c951803ffd8154600fff5c551803ffd3154600fff48551803ffe3354600fff889518037fca954600bff69951802ffda354600bff68951803ff58154600ffd5c551803ff9a054600ffe58151803ff93054600ffe48151803ff91054600bffaa951803efe6654600ff78cd51803fee2254600ffd845518027fca954600bfe68151803ff11054600
def fR6L37 : PackingT := (36,3,7,13,fR6L37F)
def fR6H0_37F (i : Nat) : Nat := 0x2450adc0520122c1938bfd106e2234538048c02601200244090b032012002450b9711a01200245811b0280123013589d301ee0d9452a0ae00900122c13f84400914114024402c009120fb409081b7148421b048a02b214740d18559822602020a2040981ec005e06881d80480091a0f505f28350090012141d0006902b2060c491031e08ee27c010c897b00be02604c902df047c0dd00600481080805bc0380480091e0ce020c09400900123054b03c301bc2ccc01902ad177c097c50401d00900121018482f318200b801c180af02fa2c40240000308c0012441281c003e410bc4200484003602ec1ce808d041e2b184b604300908090407583f050802000400030109000002000003000309010305000202040803020701001a080100
def fR6H0_37 (h : Nat) : Option (Nat × Nat) := lookupWord 35 134 8 15 7 4 fR6H0_37F h
def fR6H1_37F (i : Nat) : Nat := (if i<1 then 0xd85e801338057004cf01ee0133708b804cfc1f500af7032d8c520080a24e9196004cd80b722140099804cec05601330099804ce0014e2b0c16540440855a01330099804cc026601330099804cc0266c2c40099804cc8565c20c512da016402660133a1603804641252129915c58ac402058010705fe80fc0267028a9087388cc0266e0530099f801f865dc2605091804cdc61a800d7062d043c02676016e07a004cd04cc801fb01db8336001f8041f15f78298026601334049a81880266011c0099804cc02660133009990320026682d9c04f68a38026601330099804cf811601330099804cd41520133d03d784ca411e0133502ac832c8113c11ad161a89664481629f0099d01d4026601330099804cc026601330099880b802660133a03dc034c026601330099e012f846fc0ce0099804cf0078a20d0099d8222c50c013361112808c02326050016a203e48148605cc091004cfc0b42001300d7090402660133a143804cc0266830000998081c026601338016804cf01ed6208708e8838002660239b07f004cec5e5612cc11e1835c00f22003b070c8c0402664309a00ad8c8a80a40133601f589dac22201330099c841c0266825c0099804cc02660133a01ca837e066201330099d89ec026760f00073004cc026640053038c0beb01700133f05888bab41a201330099e8a58803d80b70099d838c026601335040482ac81ca0133b08df01bec0880133804de893002660133e18920800026601330099804cd412c01330099804cc026702bf0099a0174416422133171689fc420a01330099d00b1c03001330099804cc457a6081d01c0885c816a82d0901820080026601330099d0ab00266a00ea08540162c08401333011004cd8431e0b6b046004cfc02401330099804cec489e0c3711f004cc026601330099804cc026601332038000ce009e01330099f89be4260e12dd04f804cc02660133b117502538139e3300099a8c2f41a5211fd028f835384fc0133a064c833ec0640133f148b03be02100133a03310882c0d360760099f0a5c026601330099804cc02676201602fc81f7852801330099e0b68421840ec4138684508460622bf04c98208c548c20e708b004cc02660133806250362c1dba0610099804cc45d0e1250099881b04090013300400000000080000c0500800024000000600000010030000600c00008000080303004008020500400c010000301c000040000400018070000302805014000300500805004000180000004000000040200800000030100300000010130240603c00000070040000c0c0080100003000000000200404000020080300000030000000301c0000005000010000000403010020140000404010040140202000020000140b0000000401010020000600000000010140d004000100200c00008000040000400 else 0x307488008026601330099804cfc21b805e0053e02eac48740ff5054004cc45bfe0d0b17ee011bc1c402350099804cc02660133302b004cc05b7612800998021ac14700915129d81b402660133406a804cc820740263080f81b8026600fbf0439811681766054104ba8480c036c121701a804cc026601330093282e484f201330034004cc0266812a009980021c01801330099804cc02660133b07ac82b14500e2a7f07c60864026601335172903f3805e60f1906cb04b8857440e4208f001cb815a00b31014804cd424801330099804cc02660133005a004cc026601337002004cc8490013300999809cc0420133907590210018542e30099809c80267826d0099804cc026601330099e8924026601330099f8294026601334126804cf00638254706e78b5a454601335063804cc026722cd0099804cc02660133115b208c8026601330099a0914026702e7a03e30375022680000099b005c026680c1f05f004cc026601337012804cfc20ce009e00a303c9c03962d2a065700e841340133e149804cf4068420f0099804cc02660133f074004cc026741270099804cc02660133606018a3dc0c9620261419833241b58090b13e40a33061fc006e035e0412414522f38102a8a95c45e2271d10b00986821201330099804cdc5d3a0600099a02760544e0781041804cc0263408d304aa0064026760a00099e818c026661120099982148641a21c514c804cc026601330099804cf4256a25f203a004cc026601337026804cc026601330099804cd008f607e904550a9a40ee22fbd01208c44026601335075408e2c03b20fd0099a015c0266804e9039804cdc59c01330099f88eb01dd8049906320378c4c401330099881a8026601330099804cc0266404a115b804cc013001330099804cc026601330099804ce04f1410bb06b30c780267e2063172700a8026661001050804cc026780bca02630975006ec234601ea82f6c5dc22d8816b804cc02660133a073804cd425fa00b0099804ce85bd427a1033d036dc1e762f52149004cd4050c0b0601b004cc02660133a139e046005aa0133b169e810ec42b0115017b6895c4155a07fd146e823944aae0130099804c)
def fR6H1_37 (h : Nat) : Option (Nat × Nat) := lookupWord 156 764 10 17 9 4 fR6H1_37F h
def fR6L40F (i : Nat) : Nat := 0x6fd7c52d5474390d06012e05bc5db2a634828007ff54600
def fR6L40 : PackingT := (1,2,7,8,fR6L40F)
def fR6H1_40F (i : Nat) : Nat := 0x90024009002400900240090024504bc590093c0be110024507c024009200da157448009001b0092005915c02400920490093423009140700900240090024e020024009002400900240090024009281000900240091056009002400900240092401e04c024009002400900240090c1d0092800009284e6018024009002400900240093014814e01e009244f2066043008600a0090024009002000900240090024d010024516fc0c00900241160024009002400900241180024009002400900240090422e060c4b81180240090024a147c5f009305c0090024009002400914090090002c0680240090024009000f009002400938030090024a0380240058024d05d45a8045c40009002431340245070024c05402400900630100000200000001010000000000010000000200
def fR6H1_40 (h : Nat) : Option (Nat × Nat) := lookupWord 20 160 8 14 6 4 fR6H1_40F h
def fR6Levels : Nat → PackingT
  | 24 => fR6L24
  | 27 => fR6L27
  | 28 => fR6L28
  | 30 => fR6L30
  | 31 => fR6L31
  | 33 => fR6L33
  | 34 => fR6L34
  | 37 => fR6L37
  | 40 => fR6L40
  | _ => emptyPackingT
def fR6Idx0 : Nat → Nat → Option (Nat × Nat)
  | 27 => fR6H0_27
  | 30 => fR6H0_30
  | 31 => fR6H0_31
  | 33 => fR6H0_33
  | 34 => fR6H0_34
  | 37 => fR6H0_37
  | _ => fun _ => none
def fR6Idx1 : Nat → Nat → Option (Nat × Nat)
  | 31 => fR6H1_31
  | 34 => fR6H1_34
  | 37 => fR6H1_37
  | 40 => fR6H1_40
  | _ => fun _ => none
abbrev T6_bkT := blockU fR6Levels fR6Idx0 fR6Idx1
abbrev T6_bmT (k tm s a b : Nat) := @blockU_merge fR6Levels fR6Idx0 fR6Idx1 k tm s a b
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c24_0 : T6_bkT 8 0 0 1=true := by
  apply cellsBlockU (ar:=9) (d:=0)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T6_a24 : T6_bkT 8 0 0 1 = true := T6_c24_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c27_0 : T6_bkT 9 0 0 12=true := by
  apply cellsBlockU (ar:=10) (d:=0)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T6_a27 : T6_bkT 9 0 0 12 = true := T6_c27_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c28_0 : T6_bkT 9 1 0 8=true := by
  apply cellsBlockU (ar:=9) (d:=0)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T6_a28 : T6_bkT 9 1 0 8 = true := T6_c28_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c30_0 : T6_bkT 10 0 0 48=true := by
  apply cellsBlockU (ar:=11) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c30_48 : T6_bkT 10 0 48 48=true := by
  apply cellsBlockU (ar:=11) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c30_96 : T6_bkT 10 0 96 4=true := by
  apply cellsBlockU (ar:=11) (d:=0)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T6_a30 : T6_bkT 10 0 0 100 = true := (T6_bmT 10 0 0 48 52 T6_c30_0 (T6_bmT 10 0 48 48 4 T6_c30_48 T6_c30_96))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c31_0 : T6_bkT 10 1 0 1=true := by
  apply cellsBlockU (ar:=9) (d:=0)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c31_1 : T6_bkT 10 1 1 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c31_49 : T6_bkT 10 1 49 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c31_97 : T6_bkT 10 1 97 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c31_145 : T6_bkT 10 1 145 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c31_193 : T6_bkT 10 1 193 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c31_241 : T6_bkT 10 1 241 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c31_289 : T6_bkT 10 1 289 48=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c31_337 : T6_bkT 10 1 337 23=true := by
  apply cellsBlockU (ar:=10) (d:=1)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T6_a31 : T6_bkT 10 1 0 360 = true := (T6_bmT 10 1 0 145 215 (T6_bmT 10 1 0 49 96 (T6_bmT 10 1 0 1 48 T6_c31_0 T6_c31_1) (T6_bmT 10 1 49 48 48 T6_c31_49 T6_c31_97)) (T6_bmT 10 1 145 96 119 (T6_bmT 10 1 145 48 48 T6_c31_145 T6_c31_193) (T6_bmT 10 1 241 48 71 T6_c31_241 (T6_bmT 10 1 289 48 23 T6_c31_289 T6_c31_337))))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c33_0 : T6_bkT 11 0 0 48=true := by
  apply cellsBlockU (ar:=12) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c33_48 : T6_bkT 11 0 48 24=true := by
  apply cellsBlockU (ar:=12) (d:=1)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T6_a33 : T6_bkT 11 0 0 72 = true := (T6_bmT 11 0 0 48 24 T6_c33_0 T6_c33_48)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c34_0 : T6_bkT 11 1 0 45=true := by
  apply cellsBlockU (ar:=10) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c34_45 : T6_bkT 11 1 45 48=true := by
  apply cellsBlockU (ar:=11) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c34_93 : T6_bkT 11 1 93 48=true := by
  apply cellsBlockU (ar:=11) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c34_141 : T6_bkT 11 1 141 48=true := by
  apply cellsBlockU (ar:=11) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c34_189 : T6_bkT 11 1 189 48=true := by
  apply cellsBlockU (ar:=11) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c34_237 : T6_bkT 11 1 237 48=true := by
  apply cellsBlockU (ar:=11) (d:=2)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c34_285 : T6_bkT 11 1 285 22=true := by
  apply cellsBlockU (ar:=11) (d:=1)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T6_a34 : T6_bkT 11 1 0 307 = true := (T6_bmT 11 1 0 141 166 (T6_bmT 11 1 0 45 96 T6_c34_0 (T6_bmT 11 1 45 48 48 T6_c34_45 T6_c34_93)) (T6_bmT 11 1 141 96 70 (T6_bmT 11 1 141 48 48 T6_c34_141 T6_c34_189) (T6_bmT 11 1 237 48 22 T6_c34_237 T6_c34_285)))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c37_0 : T6_bkT 12 1 0 3=true := by
  apply cellsBlockU (ar:=10) (d:=0)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c37_3 : T6_bkT 12 1 3 16=true := by
  apply cellsBlockU (ar:=11) (d:=1)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c37_19 : T6_bkT 12 1 19 17=true := by
  apply cellsBlockU (ar:=12) (d:=1)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T6_a37 : T6_bkT 12 1 0 36 = true := (T6_bmT 12 1 0 3 33 T6_c37_0 (T6_bmT 12 1 3 16 17 T6_c37_3 T6_c37_19))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem T6_c40_0 : T6_bkT 13 1 0 1=true := by
  apply cellsBlockU (ar:=11) (d:=0)
  simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
theorem T6_a40 : T6_bkT 13 1 0 1 = true := T6_c40_0
theorem tablesfR6 : ∀ k ≤ 13, ∀ tmax ≤ 1, blockU fR6Levels fR6Idx0 fR6Idx1 k tmax 0 (fR6Levels (3*k+tmax)).1 = true := by
  intro k hk tmax ht
  interval_cases k <;> interval_cases tmax
  · exact (rfl : blockU fR6Levels fR6Idx0 fR6Idx1 0 0 0 0 = true)
  · exact (rfl : blockU fR6Levels fR6Idx0 fR6Idx1 0 1 0 0 = true)
  · exact (rfl : blockU fR6Levels fR6Idx0 fR6Idx1 1 0 0 0 = true)
  · exact (rfl : blockU fR6Levels fR6Idx0 fR6Idx1 1 1 0 0 = true)
  · exact (rfl : blockU fR6Levels fR6Idx0 fR6Idx1 2 0 0 0 = true)
  · exact (rfl : blockU fR6Levels fR6Idx0 fR6Idx1 2 1 0 0 = true)
  · exact (rfl : blockU fR6Levels fR6Idx0 fR6Idx1 3 0 0 0 = true)
  · exact (rfl : blockU fR6Levels fR6Idx0 fR6Idx1 3 1 0 0 = true)
  · exact (rfl : blockU fR6Levels fR6Idx0 fR6Idx1 4 0 0 0 = true)
  · exact (rfl : blockU fR6Levels fR6Idx0 fR6Idx1 4 1 0 0 = true)
  · exact (rfl : blockU fR6Levels fR6Idx0 fR6Idx1 5 0 0 0 = true)
  · exact (rfl : blockU fR6Levels fR6Idx0 fR6Idx1 5 1 0 0 = true)
  · exact (rfl : blockU fR6Levels fR6Idx0 fR6Idx1 6 0 0 0 = true)
  · exact (rfl : blockU fR6Levels fR6Idx0 fR6Idx1 6 1 0 0 = true)
  · exact (rfl : blockU fR6Levels fR6Idx0 fR6Idx1 7 0 0 0 = true)
  · exact (rfl : blockU fR6Levels fR6Idx0 fR6Idx1 7 1 0 0 = true)
  · exact T6_a24
  · exact (rfl : blockU fR6Levels fR6Idx0 fR6Idx1 8 1 0 0 = true)
  · exact T6_a27
  · exact T6_a28
  · exact T6_a30
  · exact T6_a31
  · exact T6_a33
  · exact T6_a34
  · exact (rfl : blockU fR6Levels fR6Idx0 fR6Idx1 12 0 0 0 = true)
  · exact T6_a37
  · exact (rfl : blockU fR6Levels fR6Idx0 fR6Idx1 13 0 0 0 = true)
  · exact T6_a40

def s0 : Sig := inputs.getD 0 zero
def s1 : Sig := inputs.getD 1 zero
def s2 : Sig := inputs.getD 2 zero
def s3 : Sig := inputs.getD 3 zero
def s4 : Sig := inputs.getD 4 zero
def s5 : Sig := inputs.getD 5 zero
def s6 : Sig := inputs.getD 6 zero
def s7 : Sig := inputs.getD 7 zero
def s8 : Sig := inputs.getD 8 zero
def nx0 : Sig := neg (inputs.getD 0 zero)
def w15 : Sig := bin true (inputs.getD 1 zero) (inputs.getD 5 zero)
def bank (w : Sig) : List Sig := [s0, s1, s2, s3, s4, s5, s6, s7, s8, nx0, w]

def RL1 : List Sig := [s0, s1, s2, s3, s4, s5, s6, s7, s8]

theorem noRoot1 : ImpossibleU graph 13 1 RL1.toFinset := by
  have hall := forestU_all fR1Levels fR1Idx0 fR1Idx1 13 (boundsBefore known383)
    (before_sound known383 valid383) geomdead tablesfR1 13 (by decide) 1 (by decide) 0 (by decide)
  have htgt : targetOf dead = graph := by decide +kernel
  have hs : sameWords (stateSetT fR1Levels 40 0) RL1 = true := by decide +kernel
  rw [htgt, sameWords_sound hs] at hall
  exact hall

def RL2 : List Sig := [s1, s2, s3, s4, s5, s6, s7, s8, nx0]

theorem noRoot2 : ImpossibleU graph 13 1 RL2.toFinset := by
  have hall := forestU_all fR2Levels fR2Idx0 fR2Idx1 13 (boundsBefore known383)
    (before_sound known383 valid383) geomdead tablesfR2 13 (by decide) 1 (by decide) 0 (by decide)
  have htgt : targetOf dead = graph := by decide +kernel
  have hs : sameWords (stateSetT fR2Levels 40 0) RL2 = true := by decide +kernel
  rw [htgt, sameWords_sound hs] at hall
  exact hall

def RL3 : List Sig := [s0, s1, s2, s3, s4, s5, s6, s7, s8, nx0]

theorem noRoot3 : ImpossibleU graph 13 1 RL3.toFinset := by
  have hall := forestU_all fR3Levels fR3Idx0 fR3Idx1 13 (boundsBefore known383)
    (before_sound known383 valid383) geomdead tablesfR3 13 (by decide) 1 (by decide) 0 (by decide)
  have htgt : targetOf dead = graph := by decide +kernel
  have hs : sameWords (stateSetT fR3Levels 40 0) RL3 = true := by decide +kernel
  rw [htgt, sameWords_sound hs] at hall
  exact hall

def RL4 : List Sig := [s0, s1, s2, s3, s4, s5, s6, s7, s8, w15]

theorem noRoot4 : ImpossibleU graph 13 1 RL4.toFinset := by
  have hall := forestU_all fR4Levels fR4Idx0 fR4Idx1 13 (boundsBefore known383)
    (before_sound known383 valid383) geomdead tablesfR4 13 (by decide) 1 (by decide) 0 (by decide)
  have htgt : targetOf dead = graph := by decide +kernel
  have hs : sameWords (stateSetT fR4Levels 40 0) RL4 = true := by decide +kernel
  rw [htgt, sameWords_sound hs] at hall
  exact hall

def RL5 : List Sig := [s1, s2, s3, s4, s5, s6, s7, s8, nx0, w15]

theorem noRoot5 : ImpossibleU graph 13 1 RL5.toFinset := by
  have hall := forestU_all fR5Levels fR5Idx0 fR5Idx1 13 (boundsBefore known383)
    (before_sound known383 valid383) geomdead tablesfR5 13 (by decide) 1 (by decide) 0 (by decide)
  have htgt : targetOf dead = graph := by decide +kernel
  have hs : sameWords (stateSetT fR5Levels 40 0) RL5 = true := by decide +kernel
  rw [htgt, sameWords_sound hs] at hall
  exact hall

def RL6 : List Sig := [s0, s1, s2, s3, s4, s5, s6, s7, s8, nx0, w15]

theorem noRoot6 : ImpossibleU graph 13 1 RL6.toFinset := by
  have hall := forestU_all fR6Levels fR6Idx0 fR6Idx1 13 (boundsBefore known383)
    (before_sound known383 valid383) geomdead tablesfR6 13 (by decide) 1 (by decide) 0 (by decide)
  have htgt : targetOf dead = graph := by decide +kernel
  have hs : sameWords (stateSetT fR6Levels 40 0) RL6 = true := by decide +kernel
  rw [htgt, sameWords_sound hs] at hall
  exact hall

theorem req_of {k t : Nat} {S : Finset Sig} (h : Live graph k t S) (roots : List Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (a : Sig) (r s : Row)
    (chk : ((bit r graph != bit s graph) && roots.all (fun v => v == a || bit r v == bit s v)) = true) :
    a ∈ S := by
  simp only [Bool.and_eq_true, bne_iff_ne] at chk
  have h2 := List.all_eq_true.mp chk.2
  exact raw_required h roots a sub r s chk.1 (fun v hv hn => by
    have ha := h2 v hv
    have hne : (v == a) = false := beq_eq_false_iff_ne.mpr hn
    rw [hne] at ha; simp only [Bool.false_or] at ha; exact beq_iff_eq.mp ha)

theorem one_of {k t : Nat} {S : Finset Sig} (h : Live graph k t S) (roots : List Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (a b : Sig) (r s : Row)
    (chk : ((bit r graph != bit s graph) && roots.all (fun v => v == a || v == b || bit r v == bit s v)) = true) :
    a ∈ S ∨ b ∈ S := by
  simp only [Bool.and_eq_true, bne_iff_ne] at chk
  obtain ⟨v, hv, hd⟩ := live_row_difference h chk.1
  have hc := List.all_eq_true.mp chk.2 v (sub v hv)
  simp only [Bool.or_eq_true, beq_iff_eq] at hc
  rcases hc with (rfl | rfl) | he
  · exact Or.inl hv
  · exact Or.inr hv
  · exact absurd he hd

theorem bank_mem {w u : Sig} (hw : w = s1 ∨ w = w15) (h : u ∈ bank w) :
    u = s0 ∨ u = s1 ∨ u = s2 ∨ u = s3 ∨ u = s4 ∨ u = s5 ∨ u = s6 ∨ u = s7 ∨ u = s8 ∨ u = nx0 ∨ u = w15 := by
  simp only [bank, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h
  all_goals first
    | (subst h; simp)
    | (rcases hw with rfl | rfl <;> subst h <;> simp)

theorem core (w : Sig) (v : (Fin 9 → Bool) → Bool) (hv : ∀ r : Row, bit r w = v (sample r))
    (hw : w = s1 ∨ w = w15) (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C) (hsz : C.size ≤ 13)
    (hcomp : ∀ x : Fin 9 → Bool, C.eval ((List.ofFn x ++ [!x 0]) ++ [v x]) = edge x) : False := by
  have bmap : ∀ r : Row, (bank w).map (bit r) = (List.ofFn (sample r) ++ [!sample r 0]) ++ [v (sample r)] := by
    intro r
    simp only [bank, List.map_cons, List.map_nil, hv, nx0, bit_neg, List.ofFn_succ, List.ofFn_zero,
      List.cons_append, List.nil_append]
    rfl
  have goalEq : (execute C.gates (bank w)).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro m hm
    let r : Row := ⟨m, hm⟩
    change bit r ((execute C.gates (bank w)).getD C.output zero) = bit r graph
    rw [← b_read, execute_bits _ _ _ (fun g hg => (legal g hg).1), bmap r]
    exact (hcomp (sample r)).trans (edge_table r).symm
  have out := get_rep (execute C.gates (bank w)) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  obtain ⟨k, t, S, hk, run, hsub⟩ := extract C.gates (bank w) legal graph_proper targetIn
  have f1 : s1 ∈ S := req_of run (bank w) hsub s1 ⟨36, by decide⟩ ⟨38, by decide⟩ (by rcases hw with rfl | rfl <;> decide +kernel)
  have f2 : s2 ∈ S := req_of run (bank w) hsub s2 ⟨2, by decide⟩ ⟨6, by decide⟩ (by rcases hw with rfl | rfl <;> decide +kernel)
  have f3 : s3 ∈ S := req_of run (bank w) hsub s3 ⟨4, by decide⟩ ⟨12, by decide⟩ (by rcases hw with rfl | rfl <;> decide +kernel)
  have f4 : s4 ∈ S := req_of run (bank w) hsub s4 ⟨1, by decide⟩ ⟨17, by decide⟩ (by rcases hw with rfl | rfl <;> decide +kernel)
  have f5 : s5 ∈ S := req_of run (bank w) hsub s5 ⟨130, by decide⟩ ⟨162, by decide⟩ (by rcases hw with rfl | rfl <;> decide +kernel)
  have f6 : s6 ∈ S := req_of run (bank w) hsub s6 ⟨2, by decide⟩ ⟨66, by decide⟩ (by rcases hw with rfl | rfl <;> decide +kernel)
  have f7 : s7 ∈ S := req_of run (bank w) hsub s7 ⟨4, by decide⟩ ⟨132, by decide⟩ (by rcases hw with rfl | rfl <;> decide +kernel)
  have f8 : s8 ∈ S := req_of run (bank w) hsub s8 ⟨8, by decide⟩ ⟨264, by decide⟩ (by rcases hw with rfl | rfl <;> decide +kernel)
  have f0 : s0 ∈ S ∨ nx0 ∈ S := one_of run (bank w) hsub s0 nx0 ⟨2, by decide⟩ ⟨3, by decide⟩ (by rcases hw with rfl | rfl <;> decide +kernel)
  by_cases h0 : s0 ∈ S <;> by_cases hn : nx0 ∈ S <;> by_cases hx : w15 ∈ S
  · have eqS : S = RL6.toFinset := by
      apply Finset.Subset.antisymm
      · intro u hu
        rcases bank_mem hw (hsub u hu) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact List.mem_toFinset.mpr (by simp only [RL6, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL6, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL6, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL6, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL6, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL6, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL6, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL6, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL6, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL6, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL6, List.mem_cons, eq_self_iff_true, true_or, or_true])
      · intro u hu
        simp only [RL6, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [h0, f1, f2, f3, f4, f5, f6, f7, f8, hn, hx]
    exact noRoot6 k t (hk.trans hsz) (fun hz => by cases hz) (eqS ▸ run)
  · have eqS : S = RL3.toFinset := by
      apply Finset.Subset.antisymm
      · intro u hu
        rcases bank_mem hw (hsub u hu) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact List.mem_toFinset.mpr (by simp only [RL3, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL3, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL3, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL3, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL3, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL3, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL3, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL3, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL3, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL3, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact absurd hu hx
      · intro u hu
        simp only [RL3, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [h0, f1, f2, f3, f4, f5, f6, f7, f8, hn]
    exact noRoot3 k t (hk.trans hsz) (fun hz => by cases hz) (eqS ▸ run)
  · have eqS : S = RL4.toFinset := by
      apply Finset.Subset.antisymm
      · intro u hu
        rcases bank_mem hw (hsub u hu) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact List.mem_toFinset.mpr (by simp only [RL4, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL4, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL4, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL4, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL4, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL4, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL4, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL4, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL4, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact absurd hu hn
        · exact List.mem_toFinset.mpr (by simp only [RL4, List.mem_cons, eq_self_iff_true, true_or, or_true])
      · intro u hu
        simp only [RL4, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [h0, f1, f2, f3, f4, f5, f6, f7, f8, hx]
    exact noRoot4 k t (hk.trans hsz) (fun hz => by cases hz) (eqS ▸ run)
  · have eqS : S = RL1.toFinset := by
      apply Finset.Subset.antisymm
      · intro u hu
        rcases bank_mem hw (hsub u hu) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact List.mem_toFinset.mpr (by simp only [RL1, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL1, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL1, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL1, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL1, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL1, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL1, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL1, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL1, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact absurd hu hn
        · exact absurd hu hx
      · intro u hu
        simp only [RL1, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [h0, f1, f2, f3, f4, f5, f6, f7, f8]
    exact noRoot1 k t (hk.trans hsz) (fun hz => by cases hz) (eqS ▸ run)
  · have eqS : S = RL5.toFinset := by
      apply Finset.Subset.antisymm
      · intro u hu
        rcases bank_mem hw (hsub u hu) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd hu h0
        · exact List.mem_toFinset.mpr (by simp only [RL5, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL5, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL5, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL5, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL5, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL5, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL5, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL5, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL5, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL5, List.mem_cons, eq_self_iff_true, true_or, or_true])
      · intro u hu
        simp only [RL5, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [f1, f2, f3, f4, f5, f6, f7, f8, hn, hx]
    exact noRoot5 k t (hk.trans hsz) (fun hz => by cases hz) (eqS ▸ run)
  · have eqS : S = RL2.toFinset := by
      apply Finset.Subset.antisymm
      · intro u hu
        rcases bank_mem hw (hsub u hu) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd hu h0
        · exact List.mem_toFinset.mpr (by simp only [RL2, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL2, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL2, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL2, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL2, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL2, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL2, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL2, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact List.mem_toFinset.mpr (by simp only [RL2, List.mem_cons, eq_self_iff_true, true_or, or_true])
        · exact absurd hu hx
      · intro u hu
        simp only [RL2, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        exacts [f1, f2, f3, f4, f5, f6, f7, f8, hn]
    exact noRoot2 k t (hk.trans hsz) (fun hz => by cases hz) (eqS ▸ run)
  · rcases f0 with h | h
    · exact absurd h h0
    · exact absurd h hn
  · rcases f0 with h | h
    · exact absurd h h0
    · exact absurd h hn

theorem gdl (x : Fin 9 → Bool) : List.ofFn x ++ [!x 0] = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, !x 0] := by
  simp [List.ofFn_succ]

theorem mainStep : ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       (∀ x4 ∈ x1, x4 = (1 : ℕ) ∨ x4 = (5 : ℕ)) →         (1 : ℕ) ∈ x1 →           ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit),             PEqualNP.MetaComplexity.FanInTwo x6 →               x6.size ≤ (13 : ℕ) →                 ∃ (x9 : Fin (9 : ℕ) → Bool),                   have x10 : List Bool := List.ofFn x9 ++ [!x9 (0 : Fin (9 : ℕ))];                   x6.eval (x10 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x11 : ℕ) => x10.getD x11 Bool.false) x1)]) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) := by
  intro l hlen hA hB h1 C legal hsz
  by_contra hne
  have key : ∀ x : Fin 9 → Bool, C.eval ((List.ofFn x ++ [!x 0]) ++ [GateOp.or.eval (List.map (fun i => (List.ofFn x ++ [!x 0]).getD i false) l)]) = edge x := by
    intro x
    by_contra hx
    exact hne ⟨x, hx⟩
  obtain ⟨a, b, rfl⟩ : ∃ a b, l = [a, b] := by
    match l, hlen with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  have ha := hB a (by simp)
  have hb := hB b (by simp)
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact core s1 (fun x => x 1) (fun r => rfl) (Or.inl rfl) C legal hsz (fun x => by
      have e : GateOp.or.eval (List.map (fun i => (List.ofFn x ++ [!x 0]).getD i false) [1, 1]) = x 1 := by
        rw [gdl]; simp [GateOp.eval]
      rw [← e]; exact key x)
  · exact core w15 (fun x => x 1 || x 5) (fun r => by simp only [w15, bit_bin, ite_true]; rfl) (Or.inr rfl) C legal hsz (fun x => by
      have e : GateOp.or.eval (List.map (fun i => (List.ofFn x ++ [!x 0]).getD i false) [1, 5]) = (x 1 || x 5) := by
        rw [gdl]; simp [GateOp.eval]
      rw [← e]; exact key x)
  · exact core w15 (fun x => x 1 || x 5) (fun r => by simp only [w15, bit_bin, ite_true]; rfl) (Or.inr rfl) C legal hsz (fun x => by
      have e : GateOp.or.eval (List.map (fun i => (List.ofFn x ++ [!x 0]).getD i false) [5, 1]) = (x 1 || x 5) := by
        rw [gdl]; simp [GateOp.eval, Bool.or_comm]
      rw [← e]; exact key x)
  · simp at h1

end PEqualNP.Outside.L_meta_3921

theorem PEqualNP.Outside.L_meta_3921 : ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 = (1 : ℕ) ∨ x3 = (2 : ℕ) ∨ x3 = (3 : ℕ) ∨ x3 = (5 : ℕ) ∨ x3 = (8 : ℕ)) →       (∀ x4 ∈ x1, x4 = (1 : ℕ) ∨ x4 = (5 : ℕ)) →         (1 : ℕ) ∈ x1 →           ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit),             PEqualNP.MetaComplexity.FanInTwo x6 →               x6.size ≤ (13 : ℕ) →                 ∃ (x9 : Fin (9 : ℕ) → Bool),                   have x10 : List Bool := List.ofFn x9 ++ [!x9 (0 : Fin (9 : ℕ))];                   x6.eval (x10 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x11 : ℕ) => x10.getD x11 Bool.false) x1)]) ≠ (x9 (0 : Fin (9 : ℕ)) && x9 (1 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (2 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (3 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (4 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ)) && x9 (0 : Fin (9 : ℕ)) || x9 (0 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ)) || x9 (1 : Fin (9 : ℕ)) && x9 (6 : Fin (9 : ℕ)) || x9 (2 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (3 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (5 : Fin (9 : ℕ)) && x9 (7 : Fin (9 : ℕ)) || x9 (6 : Fin (9 : ℕ)) && x9 (8 : Fin (9 : ℕ)) || x9 (8 : Fin (9 : ℕ)) && x9 (5 : Fin (9 : ℕ))) :=
  PEqualNP.Outside.L_meta_3921.mainStep
