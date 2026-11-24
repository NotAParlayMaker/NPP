import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_2046
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

def isNotT (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false

private lemma gate_repT (w : List Sig) (g : Gate)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨
      (if isNotT g.op then ∃ a, a∈w ∧ proper a ∧ gv w g = neg a
       else ∃ d a b, a∈w ∧ b∈w ∧ proper a ∧ proper b ∧ a≠b ∧ gv w g = bin d a b) := by
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ ∃ x, x∈w ∧ proper x ∧ neg a = neg x := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
    · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
    · exact Or.inr ⟨a,hm,hp,rfl⟩
  have bn (d : Bool) (a b : Sig) (ha : represented w a) (hb : represented w b) :
      represented w (bin d a b) ∨ ∃ d' x y, x∈w ∧ y∈w ∧ proper x ∧ proper y ∧ x≠y ∧ bin d a b = bin d' x y := by
    have bzero : ∀ v, bin false v zero = zero ∧ bin true v zero = v := fun v => ⟨(bin_laws v).2.2.1, (bin_laws v).2.1⟩
    have bone : ∀ v, bin false v one = v ∧ bin true v one = one := fun v => ⟨(bin_laws v).1, (bin_laws v).2.2.2.1⟩
    rcases operand_cases ha with rfl | rfl | ⟨hma,hpa⟩
    · rw [bin_comm]
      cases d
      · exact Or.inl (Or.inr fun h => h.1 (bzero b).1)
      · rw [(bzero b).2]; exact Or.inl hb
    · rw [bin_comm]
      cases d
      · rw [(bone b).1]; exact Or.inl hb
      · exact Or.inl (Or.inr fun h => h.2 (bone b).2)
    · rcases operand_cases hb with rfl | rfl | ⟨hmb,hpb⟩
      · cases d
        · exact Or.inl (Or.inr fun h => h.1 (bzero a).1)
        · rw [(bzero a).2]; exact Or.inl (Or.inl hma)
      · cases d
        · rw [(bone a).1]; exact Or.inl (Or.inl hma)
        · exact Or.inl (Or.inr fun h => h.2 (bone a).2)
      · by_cases eq : a = b
        · subst b
          cases d
          · rw [(bin_laws a).2.2.2.2.1]; exact Or.inl (Or.inl hma)
          · rw [(bin_laws a).2.2.2.2.2]; exact Or.inl (Or.inl hma)
        · exact Or.inr ⟨d,a,b,hma,hmb,hpa,hpb,eq,rfl⟩
  obtain ⟨ho,hl⟩ := hg
  rcases ho with ho | ho | ho
  · simp only [ho, isNotT, Bool.false_eq_true, ite_false]
    cases hi : g.inputs with
    | nil => exact Or.inl (Or.inr fun h => h.2 (by simp [gv, ho, hi]))
    | cons i t =>
      cases t with
      | nil => exact Or.inl (by simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using get_rep w i)
      | cons j u =>
        cases u with
        | cons _ _ => simp [hi] at hl
        | nil => simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bn false _ _ (get_rep w i) (get_rep w j)
  · simp only [ho, isNotT, Bool.false_eq_true, ite_false]
    cases hi : g.inputs with
    | nil => exact Or.inl (Or.inr fun h => h.1 (by simp [gv, ho, hi]))
    | cons i t =>
      cases t with
      | nil => exact Or.inl (by simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using get_rep w i)
      | cons j u =>
        cases u with
        | cons _ _ => simp [hi] at hl
        | nil => simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bn true _ _ (get_rep w i) (get_rep w j)
  · rw [Set.mem_singleton_iff] at ho
    simp only [ho, isNotT, ite_true]
    cases hi : g.inputs with
    | nil =>
      have hgv : gv w g = one := by simp only [gv, ho, hi, List.map_nil, List.headD_nil, neg_laws.1]
      exact Or.inl (Or.inr fun h => h.2 hgv)
    | cons i t =>
      have hgv : gv w g = neg (w.getD i zero) := by simp only [gv, ho, hi, List.map_cons, List.headD_cons]
      rw [hgv]; exact nx _ (get_rep w i)

private lemma pull_gateT {w : List Sig} {z : Sig} {k t S} (isN : Bool) (h : Live target k t S)
    (hz : represented w z ∨
      (if isN then ∃ a, a∈w ∧ proper a ∧ z = neg a
       else ∃ d a b, a∈w ∧ b∈w ∧ proper a ∧ proper b ∧ a≠b ∧ z = bin d a b))
    (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ t' ≤ t + isN.toNat ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,by cases isN <;> simp,h,?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | hwit
      · exact False.elim ((hr.resolve_left hw) hp)
      · cases isN with
        | true =>
          simp only [ite_true] at hwit
          obtain ⟨a,ha,hp',eq⟩ := hwit
          subst z
          let U := S.erase (neg a)
          have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
          have hu : ∀ v ∈ U, v ∈ w := fun v hv => by
            obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
          have hf : neg a ∉ insert a U := fun hh => by
            rcases Finset.mem_insert.mp hh with eq | u
            · exact hw (eq.symm ▸ ha)
            · exact hw (hu _ u)
          exact ⟨k+1,t+1,insert a U,Nat.le_refl _,by simp,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
        | false =>
          simp only [Bool.false_eq_true,ite_false] at hwit
          obtain ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩ := hwit
          subst z
          let U := S.erase (bin d a b)
          have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
          have hu : ∀ v ∈ U, v ∈ w := fun v hv => by
            obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
          have hf : bin d a b ∉ insert a (insert b U) := fun hh => by
            rcases Finset.mem_insert.mp hh with eq | u
            · exact hw (eq.symm ▸ ha)
            rcases Finset.mem_insert.mp u with eq | u
            · exact hw (eq.symm ▸ hb)
            · exact hw (hu _ u)
          exact ⟨k+1,t,insert a (insert b U),Nat.le_refl _,by simp,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,by cases isN <;> simp,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extractT (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ t ≤ gs.countP (fun g => isNotT g.op) ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hl,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl',hu',hlu,hT⟩ := pull_gateT (isNotT g.op) hl (gate_repT w g (legal g (by simp))) hs
    refine ⟨l,u,T,by simp; omega,?_,hlu,hT⟩
    simp only [List.countP_cons]
    cases h : isNotT g.op <;> simp [h] at hu' ⊢ <;> omega

def ImpossibleT (T : Sig) (cap tmax : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → t ≤ tmax → ¬Live T k t S

theorem imp_to_impT {T cap tmax S} (h : Impossible T cap S) : ImpossibleT T cap tmax S :=
  fun k t hk _ => h k t hk

theorem rotate_excludedT {T n tmax} {ws : List Sig} (hi : ImpossibleT T n tmax ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : ImpossibleT T n tmax (ws.map (movedWord p.reverse)).toFinset := by
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

theorem enum_stepT {T : Sig} {cap tmax : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : tmax > 0 → ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      ImpossibleT T (cap-1) (if (childOne ws a keep).length = cap then 0 else tmax-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      ImpossibleT T (cap-1) (if (childTwo ws a b d ka kb).length = cap then 0 else tmax)
        (childTwo ws a b d ka kb).toFinset) :
    ImpossibleT T cap tmax ws.toFinset := by
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
    have ht' : t ≤ if (childOne ws a keep).length = cap then 0 else tmax - 1 := by
      split_ifs with hlen
      · rw [←List.toFinset_card_of_nodup nd,eq] at hlen; omega
      · omega
    exact oneStep (by omega) a am keep fresh hz len k t (by omega) ht' (eq.symm ▸ tail)
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
    have ht' : t ≤ if (childTwo ws a b d ka kb).length = cap then 0 else tmax := by
      split_ifs with hlen
      · rw [←List.toFinset_card_of_nodup nd,eq] at hlen; omega
      · exact ht
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) ht' (eq.symm ▸ tail)

theorem closeChildT_sound {raw T pools links k tmax rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → ImpossibleT T k tmax (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    ImpossibleT T k tmax (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]; exact lValid _ _ hx
  · exact imp_to_impT (scalarPoolCut_sound (pValid _ hp) nd ok)

def childT (tmax cap len op : Nat) : Nat :=
  if len == cap then 0 else if op == 2 then tmax - 1 else tmax

abbrev LinkFn := Nat → List (List Sig)
abbrev NodeContextT :=
  Nat × Nat × Nat × List Decor × CovPair × List BoundPool × List QuickPool × LinkFn × LinkFn × LinkFn

def ctxWireT (c : NodeContextT) (i : Nat) : Decor := c.2.2.2.1.getD i defaultDecor
def ctxLinksT (c : NodeContextT) (ct : Nat) : LinkFn :=
  if ct == 0 then c.2.2.2.2.2.2.2.1
  else if ct == 1 then c.2.2.2.2.2.2.2.2.1
  else c.2.2.2.2.2.2.2.2.2

def evalMoveT (c : NodeContextT) (op : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let (cap,tmax,n,ws,cov,pools,qpools,l0,l1,l2) := c
  let un := op == 2
  let len := 1 + (n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len > cap then true else
    let ct := childT tmax cap len op
    let d := ct == 0
    if (restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1 == z.1) then true else
    if qpools.any (fun qp => fastCost qp (cap-1) a b op ka kb) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      let links := if ct == 0 then l0 else if ct == 1 then l1 else l2
      closeChild pools links (cap-1) rest (movedChoice op a b)

theorem evalMoveT_sound {raw T r s ws pools l0 l1 l2 cap tmax a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op == 2) = false → a ≠ b) (hcap : 0 < cap) (htmax : tmax ≤ 2)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv0 : ∀ tag xs, xs ∈ l0 tag → ImpossibleT T (cap-1) 0 (List.toFinset xs))
    (lv1 : ∀ tag xs, xs ∈ l1 tag → ImpossibleT T (cap-1) 1 (List.toFinset xs))
    (lv2 : ∀ tag xs, xs ∈ l2 tag → ImpossibleT T (cap-1) 2 (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMoveT (cap,tmax,ws.length,ws,preCov ws,pools,pools.map (summarizePool ws),l0,l1,l2)
      op a b (movedDecor op a b) ka kb = true) :
    ImpossibleT T (cap-1)
      (childT tmax cap (moveFront ws op a b ka kb).length op)
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
  unfold evalMoveT at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  let ct := childT tmax cap child.length op
  have ht0 : (ct == 0) = true → t = 0 := by
    intro hct
    have hc0 : ct = 0 := beq_iff_eq.mp hct
    change t ≤ ct at ht
    omega
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
    have hct_le : ct ≤ 2 := by
      dsimp only [ct, childT]; split_ifs <;> omega
    by_cases hct0 : ct = 0
    · have hctb : (ct == 0) = true := beq_iff_eq.mpr hct0
      rw [hctb] at test; simp only [ite_true] at test
      exact closeChildT_sound pv lv0 nd' test k t hk (hct0 ▸ ht) h'
    · have hctb0 : (ct == 0) = false := beq_eq_false_iff_ne.mpr hct0
      rw [hctb0] at test; simp only [Bool.false_eq_true, ite_false] at test
      by_cases hct1 : ct = 1
      · have hctb1 : (ct == 1) = true := beq_iff_eq.mpr hct1
        rw [hctb1] at test; simp only [ite_true] at test
        exact closeChildT_sound pv lv1 nd' test k t hk (hct1 ▸ ht) h'
      · have hctb1 : (ct == 1) = false := beq_eq_false_iff_ne.mpr hct1
        rw [hctb1] at test; simp only [Bool.false_eq_true, ite_false] at test
        have hct2 : ct = 2 := by omega
        exact closeChildT_sound pv lv2 nd' test k t hk (hct2 ▸ ht) h'

def testPairT (ctx : NodeContextT) (a b : Decor) (d : Bool) : Bool :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let f := evalMoveT ctx op a b z
  f false false && f true false && f false true && f true true

def testRowT (ctx : NodeContextT) (a : Decor) (bs : List Decor) : Bool :=
  let unOk := if ctx.2.1 == 0 then true else
    let z := movedDecor 2 a a
    evalMoveT ctx 2 a a z false false && evalMoveT ctx 2 a a z true true
  unOk && bs.all (fun b => testPairT ctx a b false && testPairT ctx a b true)

def testAllT (ctx : NodeContextT) : List Decor → Bool
  | [] => true
  | a :: bs => testRowT ctx a bs && testAllT ctx bs

theorem all_unaryT {ctx} {ws : List Decor} (h : testAllT ctx ws = true) (ht : ctx.2.1 > 0) {a : Decor} (ha : a ∈ ws) (keep : Bool) :
    evalMoveT ctx 2 a a (movedDecor 2 a a) keep keep = true := by
  have hne : (ctx.2.1 == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAllT,Bool.and_eq_true,testRowT,hne,Bool.false_eq_true,ite_false] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem all_binaryT {ctx} {ws : List Decor} (h : testAllT ctx ws = true) {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (d : Bool) : testPairT ctx a b d = true ∨ testPairT ctx b a d = true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAllT,Bool.and_eq_true,testRowT,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left; cases d <;> first | exact (h.1.2 _ bm).1 | exact (h.1.2 _ bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right; cases d <;> first | exact (h.1.2 _ haTail).1 | exact (h.1.2 _ haTail).2
      · exact ih h.2 haTail hbTail

theorem testPairT_at {ctx a b d} (h : testPairT ctx a b d = true) (ka kb : Bool) :
    evalMoveT ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [testPairT,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem nodeT_sound {raw T r s ws pools l0 l1 l2 cap tmax}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv0 : ∀ tag xs, xs ∈ l0 tag → ImpossibleT T (cap-1) 0 (List.toFinset xs))
    (lv1 : ∀ tag xs, xs ∈ l1 tag → ImpossibleT T (cap-1) 1 (List.toFinset xs))
    (lv2 : ∀ tag xs, xs ∈ l2 tag → ImpossibleT T (cap-1) 2 (List.toFinset xs))
    (htmax : tmax ≤ 2)
    (checks : testAllT (cap,tmax,ws.length,ws,preCov ws,pools,pools.map (summarizePool ws),l0,l1,l2) ws = true) :
    ImpossibleT T cap tmax (ws.map Prod.fst).toFinset := by
  by_cases hc : cap = 0
  · intro k t hk _ h
    have ke : k = 0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    have eqS : S = {_} := h (fun k _ S => k = 0 → S = {_}) (fun _ _ => rfl)
      (fun _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn))
      (fun _ _ _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn)) rfl
    exact out (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
  have hc' : 0 < cap := by omega
  apply enum_stepT nd out
  · intro htpos v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    have hev := evalMoveT_sound (op := 2) pairs faith nd ha ha (by simp) hc' htmax pv lv0 lv1 lv2 pro fresh (all_unaryT checks htpos ha keep)
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
    simpa [childT] using hev
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a ≠ b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a ∈ ws) (bb : b ∈ ws) (ne' : a.1 ≠ b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPairT (cap,tmax,ws.length,ws,preCov ws,pools,pools.map (summarizePool ws),l0,l1,l2) a b d = true) :
        ImpossibleT T (cap-1) (if (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).length = cap then 0 else tmax)
          (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      have hf := binary_front nd aa bb ne' d ka kb
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      have hev := evalMoveT_sound (op := if d then 1 else 0) pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' htmax pv lv0 lv1 lv2
        (eq ▸ pr) (eq ▸ fr) (testPairT_at test ka kb)
      have hop : ((if d then 1 else 0) == 2) = false := by cases d <;> rfl
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
      simpa [childT, hop] using hev
    rcases all_binaryT checks haW hbW ab d with hh | hh
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

theorem linkedSetT_sound (levels : Nat → PackingT) (k tmax : Nat)
    (names : ∀ x ∈ dead.autos.toList, autoOK (targetOf dead) (x.map swapRows) = true)
    (earlier : ∀ i < (levels (3*k+tmax)).1, ImpossibleT (targetOf dead) k tmax (stateSetT levels (3*k+tmax) i).toFinset)
    {pair out} (h : linkedSetT levels (3*k+tmax) pair = some out) :
    ImpossibleT (targetOf dead) k tmax out.toFinset := by
  unfold linkedSetT at h
  split at h
  · cases h
  next valid =>
    cases e : dead.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excludedT (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))

def contextOfT (levels : Nat → PackingT) (idx0 idx1 idx2 : Nat → Nat → Option (Nat × Nat)) (k tmax i : Nat) : NodeContextT :=
  let slot := 3 * k + tmax
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
  let ls2 := fun tag => ((idx2 slot tag).bind (linkedSetT levels (3*(k-1)+2))).toList
  (k, tmax, ws.length, ws, preCov ws, rules, rules.map (summarizePool ws), ls0, ls1, ls2)

def prelimT (T : Sig) (c : NodeContextT) : Bool :=
  let ws := c.2.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)

def nodeVerifiedT (levels : Nat → PackingT) (idx0 idx1 idx2 : Nat → Nat → Option (Nat × Nat)) (k tmax i : Nat) : Bool :=
  let c := contextOfT levels idx0 idx1 idx2 k tmax i
  prelimT (targetOf dead) c && (if k = 0 then true else testAllT c c.2.2.2.1)

theorem nodeVerifiedT_sound (levels : Nat → PackingT) (idx0 idx1 idx2 : Nat → Nat → Option (Nat × Nat)) (k tmax i : Nat)
    (htmax : tmax ≤ 2)
    (samples : properPairs (targetOf dead) (asRow fun j => (dead.samples j).1) (asRow fun j => (dead.samples j).2))
    (cols : ∀ ci ∈ dead.cols.values, Slice (vars dead.mask) (targetOf dead) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ dead.autos.toList, autoOK (targetOf dead) (x.map swapRows) = true)
    (prior0 : k > 0 → ∀ j < (levels (3*(k-1))).1, ImpossibleT (targetOf dead) (k-1) 0 (stateSetT levels (3*(k-1)) j).toFinset)
    (prior1 : k > 0 → ∀ j < (levels (3*(k-1)+1)).1, ImpossibleT (targetOf dead) (k-1) 1 (stateSetT levels (3*(k-1)+1) j).toFinset)
    (prior2 : k > 0 → ∀ j < (levels (3*(k-1)+2)).1, ImpossibleT (targetOf dead) (k-1) 2 (stateSetT levels (3*(k-1)+2) j).toFinset)
    (checked : nodeVerifiedT levels idx0 idx1 idx2 k tmax i = true) :
    ImpossibleT (targetOf dead) k tmax (stateSetT levels (3*k+tmax) i).toFinset := by
  rw [stateSetT_eq]
  simp only [nodeVerifiedT, prelimT, contextOfT, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at checked
  have hN := checked.1.1
  have hT : targetOf dead ∉ (readNodeT levels (3*k+tmax) i).2.2.map Prod.fst := checked.1.2
  by_cases h0 : k = 0
  · subst k
    intro k' t' hk' _ h
    have hk0 : k' = 0 := by omega
    subst k'
    generalize he : ((readNodeT levels (3*0+tmax) i).2.2.map Prod.fst).toFinset = S at h
    have eqS : S = {_} := h (fun k _ S => k = 0 → S = {_}) (fun _ _ => rfl)
      (fun _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn))
      (fun _ _ _ _ _ hn => False.elim (Nat.succ_ne_zero _ hn)) rfl
    exact hT (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
  apply nodeT_sound (raw:=vars dead.mask) samples _ hN hT _ _ _ _ htmax (by simpa only [h0,ite_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful dead) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound dead cols h
  · intro tag xs hx
    have e : ((idx0 (3*k+tmax) tag).bind (linkedSetT levels (3*(k-1)))) = some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    have h0' : 3*(k-1) = 3*(k-1)+0 := by omega
    rw [h0'] at h
    exact linkedSetT_sound levels (k-1) 0 names (by simpa [←h0'] using prior0 (by omega)) h
  · intro tag xs hx
    have e : ((idx1 (3*k+tmax) tag).bind (linkedSetT levels (3*(k-1)+1))) = some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSetT_sound levels (k-1) 1 names (prior1 (by omega)) h
  · intro tag xs hx
    have e : ((idx2 (3*k+tmax) tag).bind (linkedSetT levels (3*(k-1)+2))) = some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSetT_sound levels (k-1) 2 names (prior2 (by omega)) h

def blockT (levels : Nat → PackingT) (idx0 idx1 idx2 : Nat → Nat → Option (Nat × Nat)) (k tmax start : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => nodeVerifiedT levels idx0 idx1 idx2 k tmax start && blockT levels idx0 idx1 idx2 k tmax (start + 1) n

theorem blockT_at {levels idx0 idx1 idx2 k tmax start n} (h : blockT levels idx0 idx1 idx2 k tmax start n = true)
    (i : Nat) (lo : start ≤ i) (hi : i < start + n) : nodeVerifiedT levels idx0 idx1 idx2 k tmax i = true := by
  induction n generalizing start with
  | zero => omega
  | succ n ih =>
    simp only [blockT,Bool.and_eq_true] at h
    by_cases eq : i = start
    · exact eq ▸ h.1
    · exact ih h.2 (by omega) (by omega)

theorem blockT_merge {levels idx0 idx1 idx2 k tmax start a b}
    (ha : blockT levels idx0 idx1 idx2 k tmax start a = true)
    (hb : blockT levels idx0 idx1 idx2 k tmax (start + a) b = true) :
    blockT levels idx0 idx1 idx2 k tmax start (a + b) = true := by
  induction a generalizing start with
  | zero => simpa [blockT] using hb
  | succ a ih =>
    simp only [blockT,Nat.succ_add,Bool.and_eq_true] at ha ⊢
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm 1] using hb)⟩

theorem makeBlockT {levels idx0 idx1 idx2 k tmax start n}
    (h : ∀ i, start ≤ i → i < start + n → nodeVerifiedT levels idx0 idx1 idx2 k tmax i = true) :
    blockT levels idx0 idx1 idx2 k tmax start n = true := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [blockT, Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega), ih (fun i lo hi => h i (by omega) (by omega))⟩

def checkAtT (c : NodeContextT) (i j op : Nat) (ka kb : Bool) : Bool :=
  let a := ctxWireT c i
  let b := ctxWireT c j
  evalMoveT c op a b (movedDecor op a b) ka kb

def combFieldT (c : NodeContextT) (d un ka kb : Bool) (op i j : Nat) : Bits :=
  let a := ctxWireT c i
  let b := ctxWireT c j
  restCov (getCov c.2.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2

def fallbackFastT (c : NodeContextT) (i j op : Nat) (ka kb : Bool) : Bool :=
  let (cap,tmax,n,ws,_,pools,qpools,l0,l1,l2) := c
  let a := ws.getD i defaultDecor
  let b := ws.getD j defaultDecor
  let un := op == 2
  let len := 1 + (n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  let ct := childT tmax cap len op
  let z1 := choiceVal (movedChoice op a b)
  if !properB z1 || ws.any (fun v => v.1 == z1) then true else
  if qpools.any (fun qp => fastCost qp (cap-1) a b op ka kb) then true else
    let rest := (opKeep un ka kb a b ws).map Prod.fst
    let links := if ct == 0 then l0 else if ct == 1 then l1 else l2
    closeChild pools links (cap-1) rest (movedChoice op a b)

theorem fallbackFastT_sound {c i j op ka kb}
    (hlen : ¬(1 + (c.2.2.1 - (if ka then 0 else 1) - (if (op == 2) || kb then 0 else 1)) > c.1))
    (h : fallbackFastT c i j op ka kb = true) :
    checkAtT c i j op ka kb = true := by
  rcases c with ⟨cap, tmax, n, ws, cov, pools, qpools, l0, l1, l2⟩
  dsimp only [checkAtT, evalMoveT, ctxWireT]
  dsimp only at hlen
  rw [if_neg hlen]
  dsimp only [fallbackFastT] at h
  have hz1 : (movedDecor op (ws.getD i defaultDecor) (ws.getD j defaultDecor)).1 =
      choiceVal (movedChoice op (ws.getD i defaultDecor) (ws.getD j defaultDecor)) :=
    moved_full op _ _
  set len := 1 + (n - (if ka then 0 else 1) - (if (op == 2) || kb then 0 else 1))
  set ct := childT tmax cap len op
  set d := ct == 0
  by_cases hcomb : ((restCov (getCov cov d) (column d (ws.getD i defaultDecor).2) (column d (ws.getD j defaultDecor).2) (op == 2) ka kb ||| column d (movedDecor op (ws.getD i defaultDecor) (ws.getD j defaultDecor)).2) != BitVec.allOnes 768) = true
  · simp only [hcomb, ite_true]
  · simp only [hcomb, ite_false, hz1]
    exact h

def makeBatchT (k n : Nat) (xs : List NodeContextT) : Batch :=
  (k, n, units xs.length,
    (List.range n).map (fun i => packedSig (fun c => (ctxWireT c i).2) xs),
    packedCov (fun c => c.2.2.2.2.1.1) xs,
    packedCov (fun c => c.2.2.2.2.1.2) xs)

theorem laneWireT_at (k n : Nat) (xs : List NodeContextT) {i : Nat} (h : i < n) :
    laneWire (makeBatchT k n xs) i = packedSig (fun c => (ctxWireT c i).2) xs := by
  simp [laneWire, makeBatchT, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, h]

def batchMoveT (b : Batch) (tmax : Nat) (xs : List NodeContextT) (i j op : Nat) (ka kb : Bool) : Bool :=
  let (k, n, r, _, u, v) := b
  let un := op == 2
  let len := 1 + (n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len > k then true else
    let ct := childT tmax k len op
    let d := ct == 0
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r * (BitVec.allOnes 768).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackFastT c i j op ka kb) mask xs

theorem batchMoveT_at (k tmax n : Nat) (xs : List NodeContextT) {i j op : Nat} {ka kb}
    (hi : i < n) (hj : j < n) {q : Nat} (hq : q < xs.length)
    (budget : xs[q].1 = k) (ht : xs[q].2.1 = tmax) (arity : xs[q].2.2.1 = n)
    (pass : batchMoveT (makeBatchT k n xs) tmax xs i j op ka kb = true) :
    checkAtT xs[q] i j op ka kb = true := by
  let len := 1 + (n - (if ka then 0 else 1) - (if (op == 2) || kb then 0 else 1))
  let ct := childT tmax k len op
  let d := ct == 0
  have eval : checkAtT xs[q] i j op ka kb =
      if len > k then true else if combFieldT xs[q] d (op == 2) ka kb op i j != BitVec.allOnes 768 then true
      else fallbackFastT xs[q] i j op ka kb := by
    rcases hxq : xs[q] with ⟨cap, tm, nn, ws, cov, pools, qpools, l0, l1, l2⟩
    rw [hxq] at budget ht arity
    dsimp only at budget ht arity
    subst budget ht arity
    unfold checkAtT evalMoveT combFieldT fallbackFastT ctxWireT
    dsimp only [len, ct, d]
    have hz1 : (movedDecor op (ws.getD i defaultDecor) (ws.getD j defaultDecor)).1 =
        choiceVal (movedChoice op (ws.getD i defaultDecor) (ws.getD j defaultDecor)) := moved_full op _ _
    rw [hz1]
  by_cases small : len > k
  · simp [eval, small]
  · let r := units xs.length
    let a := laneWire (makeBatchT k n xs) i
    let b := laneWire (makeBatchT k n xs) j
    let cov := if d then packedCov (fun c : NodeContextT => c.2.2.2.2.1.2) xs
               else packedCov (fun c : NodeContextT => c.2.2.2.2.1.1) xs
    change (if len > k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op == 2) ka kb |||
        packedColumn d (packedOp (r * (BitVec.allOnes 768).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.2.1 d) xs := by
      dsimp only [cov]; cases d <;> rfl
    have ca : a = _ := laneWireT_at k n xs hi
    have cb : b = _ := laneWireT_at k n xs hj
    dsimp only [r] at pass
    rw [ca, cb, packed_op, packed_column, packed_column, packed_column, chosen, takePacked_ok, lanes_or] at pass
    by_cases hit : combFieldT xs[q] d (op == 2) ka kb op i j = BitVec.allOnes 768
    · have hlenq : ¬(1 + (xs[q].2.2.1 - (if ka then 0 else 1) - (if (op == 2) || kb then 0 else 1)) > xs[q].1) := by
        rw [budget, arity]; exact small
      apply fallbackFastT_sound hlenq
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval, if_neg small, if_pos (bne_iff_ne.mpr hit)]

def batchPairT (b : Batch) (tmax : Nat) (xs : List NodeContextT) (i j op : Nat) : Bool :=
  let f := batchMoveT b tmax xs i j op
  f false false && f true false && f false true && f true true

def batchRowT (b : Batch) (tmax : Nat) (xs : List NodeContextT) (i : Nat) (js : List Nat) : Bool :=
  let unOk := if tmax == 0 then true else
    batchMoveT b tmax xs i i 2 false false && batchMoveT b tmax xs i i 2 true true
  unOk && js.all (fun j => batchPairT b tmax xs i j 0 && batchPairT b tmax xs i j 1)

def batchRowsT (b : Batch) (tmax : Nat) (xs : List NodeContextT) : List Nat → Bool
  | [] => true
  | i :: js => batchRowT b tmax xs i js && batchRowsT b tmax xs js

theorem batchRowsT_at (k tmax n : Nat) (xs : List NodeContextT) {q : Nat} (hq : q < xs.length)
    (budget : xs[q].1 = k) (ht : xs[q].2.1 = tmax) (arity : xs[q].2.2.1 = n) (js : List Nat)
    (bounds : ∀ j ∈ js, j < n) (allRows : batchRowsT (makeBatchT k n xs) tmax xs js = true) :
    testAllT xs[q] (js.map (ctxWireT xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRowsT, Bool.and_eq_true, batchRowT, List.all_eq_true] at allRows
    simp only [List.map_cons, testAllT, testRowT, Bool.and_eq_true, List.all_eq_true, List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMoveT_at k tmax n xs
    have hun : (if xs[q].2.1 == 0 then true else
        evalMoveT xs[q] 2 (ctxWireT xs[q] i) (ctxWireT xs[q] i) (movedDecor 2 (ctxWireT xs[q] i) (ctxWireT xs[q] i)) false false &&
        evalMoveT xs[q] 2 (ctxWireT xs[q] i) (ctxWireT xs[q] i) (movedDecor 2 (ctxWireT xs[q] i) (ctxWireT xs[q] i)) true true) = true := by
      rw [ht]
      cases htm : (tmax == 0)
      · simp only [Bool.false_eq_true, ite_false, Bool.and_eq_true]
        have h1 := allRows.1.1
        simp only [htm, Bool.false_eq_true, ite_false, Bool.and_eq_true] at h1
        exact ⟨check hi hi hq budget ht arity h1.1, check hi hi hq budget ht arity h1.2⟩
      · simp
    refine ⟨⟨hun, ?_⟩, ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j, hj, rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPairT (makeBatchT k n xs) tmax xs i j (if d then 1 else 0) = true) :
        testPairT xs[q] (ctxWireT xs[q] i) (ctxWireT xs[q] j) d = true := by
      simp only [batchPairT, Bool.and_eq_true] at pass
      simp only [testPairT, Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget ht arity pass.1.1.1, check hi hj' hq budget ht arity pass.1.1.2⟩,
        check hi hj' hq budget ht arity pass.1.2⟩, check hi hj' hq budget ht arity pass.2⟩
    exact ⟨opCheck false both.1, opCheck true both.2⟩

def runBatchT (k tmax n : Nat) (xs : List NodeContextT) : Bool :=
  batchRowsT (makeBatchT k n xs) tmax xs (List.range n)

theorem runBatchT_at {k tmax n} {xs : List NodeContextT} {q} (hq : q < xs.length)
    (hb : xs[q].1 = k) (ht : xs[q].2.1 = tmax) (ha : xs[q].2.2.1 = n) (hn : xs[q].2.2.2.1.length = n)
    (pass : runBatchT k tmax n xs = true) : testAllT xs[q] xs[q].2.2.2.1 = true := by
  have all := batchRowsT_at k tmax n xs hq hb ht ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (ctxWireT xs[q]) = xs[q].2.2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [ctxWireT, List.getD_eq_getElem?_getD, h2]
  rwa [eq] at all

def contextsT (levels : Nat → PackingT) (idx0 idx1 idx2 : Nat → Nat → Option (Nat × Nat)) (k tmax start n : Nat) : List NodeContextT :=
  ((List.range n).map (start + ·)).map (contextOfT levels idx0 idx1 idx2 k tmax)

def headerT (levels : Nat → PackingT) (idx0 idx1 idx2 : Nat → Nat → Option (Nat × Nat)) (k tmax start n ar : Nat) : Bool :=
  (contextsT levels idx0 idx1 idx2 k tmax start n).all (fun c => c.2.2.1 == ar && prelimT (targetOf dead) c)

def rowCutT (levels : Nat → PackingT) (idx0 idx1 idx2 : Nat → Nat → Option (Nat × Nat)) (k tmax start n ar lo len : Nat) : Bool :=
  let xs := contextsT levels idx0 idx1 idx2 k tmax start n
  let b := makeBatchT k ar xs
  (List.range len).all (fun d =>
    let i := lo + d
    batchRowT b tmax xs i (List.range' (i + 1) (ar - (i + 1))))

theorem rowCutT_at {levels idx0 idx1 idx2 k tmax start n ar lo len}
    (h : rowCutT levels idx0 idx1 idx2 k tmax start n ar lo len = true)
    (i : Nat) (l : lo ≤ i) (r : i < lo + len) :
    batchRowT (makeBatchT k ar (contextsT levels idx0 idx1 idx2 k tmax start n)) tmax
      (contextsT levels idx0 idx1 idx2 k tmax start n) i (List.range' (i + 1) (ar - (i + 1))) = true := by
  have ha := List.all_eq_true.mp h (i - lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem cutsRunT {levels idx0 idx1 idx2 k tmax start n ar}
    (h : rowCutT levels idx0 idx1 idx2 k tmax start n ar 0 ar = true) :
    runBatchT k tmax ar (contextsT levels idx0 idx1 idx2 k tmax start n) = true := by
  let xs := contextsT levels idx0 idx1 idx2 k tmax start n
  have go (lo num : Nat) (eq : lo + num = ar) :
      batchRowsT (makeBatchT k ar xs) tmax xs (List.range' lo num) = true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ, batchRowsT, Bool.and_eq_true]
      refine ⟨?_, ih (lo + 1) (by omega)⟩
      have ok := rowCutT_at h lo (by omega) (by omega)
      simpa only [show ar - (lo + 1) = num by omega] using ok
  unfold runBatchT
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlockT {levels idx0 idx1 idx2 k tmax start n ar}
    (hd : headerT levels idx0 idx1 idx2 k tmax start n ar = true)
    (h : rowCutT levels idx0 idx1 idx2 k tmax start n ar 0 ar = true) :
    blockT levels idx0 idx1 idx2 k tmax start n = true := by
  apply makeBlockT
  intro i lo hi
  let xs := contextsT levels idx0 idx1 idx2 k tmax start n
  have hm : contextOfT levels idx0 idx1 idx2 k tmax i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i, List.mem_map.mpr ⟨i - start, List.mem_range.mpr (by omega), by omega⟩, rfl⟩
  obtain ⟨q, hq, e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true, beq_iff_eq] at one
  have hb : xs[q].1 = k := by rw [e]; rfl
  have ht : xs[q].2.1 = tmax := by rw [e]; rfl
  have ha : xs[q].2.2.1 = ar := e ▸ one.1
  have hn : xs[q].2.2.2.1.length = ar := by rw [e]; exact one.1
  simp only [nodeVerifiedT, Bool.and_eq_true]
  refine ⟨one.2, ?_⟩
  split
  · rfl
  · exact e ▸ runBatchT_at hq hb ht ha hn (cutsRunT h)

def chunkCheckT (levels : Nat → PackingT) (idx0 idx1 idx2 : Nat → Nat → Option (Nat × Nat)) (k tmax start n ar : Nat) : Bool :=
  let xs := contextsT levels idx0 idx1 idx2 k tmax start n
  xs.all (fun c => c.2.2.1 == ar && prelimT (targetOf dead) c) &&
  let b := makeBatchT k ar xs
  (List.range ar).all (fun i => batchRowT b tmax xs i (List.range' (i + 1) (ar - (i + 1))))

theorem chunkBlockT {levels idx0 idx1 idx2 k tmax start n ar}
    (h : chunkCheckT levels idx0 idx1 idx2 k tmax start n ar = true) :
    blockT levels idx0 idx1 idx2 k tmax start n = true := by
  unfold chunkCheckT at h
  rw [Bool.and_eq_true] at h
  exact cutsBlockT h.1 (by simpa [rowCutT, Nat.zero_add] using h.2)

def cellsT (levels : Nat → PackingT) (idx0 idx1 idx2 : Nat → Nat → Option (Nat × Nat)) (k tmax start n ar : Nat) : Nat → Prop
  | 0 => chunkCheckT levels idx0 idx1 idx2 k tmax start n ar = true
  | d + 1 => cellsT levels idx0 idx1 idx2 k tmax start (n / 2) ar d ∧ cellsT levels idx0 idx1 idx2 k tmax (start + n / 2) (n - n / 2) ar d

theorem kT {levels idx0 idx1 idx2 k tmax start n ar}
    (h : chunkCheckT levels idx0 idx1 idx2 k tmax start n ar = true) :
    cellsT levels idx0 idx1 idx2 k tmax start n ar 0 := h

theorem cellsBlockT {levels idx0 idx1 idx2 k tmax start n ar d}
    (h : cellsT levels idx0 idx1 idx2 k tmax start n ar d) :
    blockT levels idx0 idx1 idx2 k tmax start n = true := by
  induction d generalizing start n with
  | zero => exact chunkBlockT h
  | succ d ih =>
    have v := blockT_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

theorem forestT_all (levels : Nat → PackingT) (idx0 idx1 idx2 : Nat → Nat → Option (Nat × Nat)) (top : Nat)
    (prior : Nat → Nat)
    (lo : ∀ m, Lower (vars m) (graphGoal m) (prior m))
    (valid : graphValid dead prior = true)
    (tabs : ∀ k ≤ top, ∀ tmax ≤ 2, blockT levels idx0 idx1 idx2 k tmax 0 (levels (3*k+tmax)).1 = true) :
    ∀ k ≤ top, ∀ tmax ≤ 2, ∀ i < (levels (3*k+tmax)).1, ImpossibleT (targetOf dead) k tmax (stateSetT levels (3*k+tmax) i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at valid
  have pairs := chart_pairs valid.1.1.1 valid.1.1.2
  have cols : ∀ ci ∈ dead.cols.values, Slice (vars dead.mask) (targetOf dead) (subcube ci.1 ci.2.1) ci.2.2.2.2 :=
    fun ci hc => col_sound ci prior lo (valid.1.2 ci hc)
  have names := valid.2
  intro k
  induction k with
  | zero =>
    intro hk tmax htmax i hi
    have hb := tabs 0 hk tmax htmax
    exact nodeVerifiedT_sound levels idx0 idx1 idx2 0 tmax i htmax pairs cols names
      (fun h => False.elim (Nat.lt_irrefl 0 h))
      (fun h => False.elim (Nat.lt_irrefl 0 h))
      (fun h => False.elim (Nat.lt_irrefl 0 h))
      (blockT_at hb i (Nat.zero_le i) (by simpa using hi))
  | succ k ih =>
    intro hk tmax htmax i hi
    have hb := tabs (k + 1) hk tmax htmax
    exact nodeVerifiedT_sound levels idx0 idx1 idx2 (k + 1) tmax i htmax pairs cols names
      (fun _ j hj => ih (by omega) 0 (by decide) j hj)
      (fun _ j hj => ih (by omega) 1 (by decide) j hj)
      (fun _ j hj => ih (by omega) 2 (by decide) j hj)
      (blockT_at hb i (Nat.zero_le i) (by simpa using hi))
def f3108L24F (i : Nat) : Nat := 0x3b649c6549302e95348020
def f3108L24 : PackingT := (1,7,7,3,f3108L24F)
def f3108L27F (i : Nat) : Nat := 0x1600680b86000504001600689e8af181000016e9b0034600025e81b802bd00c6301c000cc2380018c4000265215a284009800400d5696f374b15767d1f8d455d2e46fb69909c4b9e0b2542792870261087014050041ffb75c92e98558c2083ff6eb925d2c6c084107fcdc6a1b54c5200834fe194c0aa2982401050ff36da56616360420c37e6598cd432a98841f7c13148152605300830dfb74e3174a9a40106db6719302e95348020fba4a92605d2a690041f749524c153605200832ed996a92a6c1220107dd254d2060d5244020fbb0a8a40c1aa48804192fdb9718b854d8108365bb8cc9970a9b021064fe6e5c02e15360420d9bccab805c2a6c0841b3d993700b854d810830dfb8ccad76d4262107cb558d81619954c420f96ac3326b2b0298841c7b5b460551aa9300830f7b8ada243552601051bf76ca664eaa60420c37ee4b6ca9d54c0841c6ddb664d53aa9810830dfb92db0a7553021041bf770a6aeda960420
def f3108L27 : PackingT := (29,6,7,9,f3108L27F)
def f3108H0_27F (i : Nat) : Nat := 0x100b80
def f3108H0_27 (h : Nat) : Option (Nat × Nat) := lookupWord 1 3 2 9 1 4 f3108H0_27F h
def f3108L28F (i : Nat) : Nat := 0xd002805860014281e3d1a8605314c120082a5bbac59b62cc306105cd3748a86558354c20
def f3108L28 : PackingT := (3,6,7,6,f3108L28F)
def f3108L30F (i : Nat) : Nat := (if i<2 then (if i<1 then 0xe77d65546aa64c20e7f581546aa64c20a7fdc9546aa60c20e77d95546aa60c20e7f591546aa60c20a7fdc9146aa60c20e7f5c96865520c20a7fdca6465520c20e6fda66465520c20e77da56465520c20e7bda46465520c20e7eda26465520c20e7f5a16465520c20e7f9916825520c20a7fdc9296aa58c20c7fdb8656aa58c20a7fdc9616aa58c20c7fdb9616aa58c20e3fd98616aa58c20c7fdb564eaa58c20c7fd956c6aa58c20c7fd936c6aa58c20c7fdb5646aa58c20a7fdc9546aa58c20e77d95546aa58c20e7f591546aa58c20c7fdb8646aa54c20cbfdb8606aa54c20a7fdc9586aa54c20c7fdb9586aa54c20e6fd96586aa54c20a7fdc854eaa64420e7dd8354eaa64420d6fdb664eaa60420e6fca664eaa60420e6fdb664eaa60420c7fdb664eaa60420c7fdb564eaa60420cefdb660eaa60420a7fdc954eaa60420cefdb654eaa60420e7dd9354eaa60420a7fdc914eaa60420cefdb614eaa60420a7fdc9616aa4c420c7fdb9616aa4c420e3fd98616aa4c420a7fcca54d91a2020a7fcca6e1958cc20a7fcca6d9958cc20f37d98615658cc20a7fcca615918cc20a7fcca595918cc20c7fcba655818cc20f3f598605618cc20f77565645518cc20f77595605518cc208ffdc82e9538442097fdcb661538442097fccb6615384420d3fdb86615384420b7ddc960d5384420f3dd9860d5384420f75d9560d538442087fecc6e9834402087fecc6e9824402087fecc6e93244020a77ecc6e5a520c2087fecc6e99520c2087fecc6e99854c2087fecc6e9984c42087fecc6e9954c42087fdc1aeda84802087fdc8aeda34402087fdc5aeda344020c7bdc4aeda34402087fdc2aeda34402096fdc6aeda166020c6fda6aed9520c20c77da5aed9520c20c7bda4aed9520c20c7eda2aed9520c20c7f5a1aed9520c20c7f9a0aed9520c2087fdc9aeda858c2087fdc8aeda954c2087fdc1aeda954c2087fdc9aeda654c208bfdc8aeda654c2096fdc6aeda864420c6fca6aeda960420a6fdc6aeda960420c6fcb6aeda960420c6fdc6aeda96042087fdc3aeda96042087fdc9aeda84c4208efdc6aeda84c42087fdc9aeda54c420c7bdb4606aa4c020c7bdb4546aa4c020c7bdb4486aa4c020c7f5b1606aa48020c3fdb8662aa58c20c6fda96daaa60420d2fd986daaa604208efdcb29aaa60420e2fd9829aaa60420c6fd986daaa60420c6fdb664eaa60420c6fdb6646aa6042087fdc92e953a202087fcca6e553a202087fdc52e9988cc2087fdc12e9988cc2087fdc92e9858cc2087fcca6e5858cc20c3fcba661858cc2087fdc92e9658cc2087fcca6e5658cc20c6fcba659658cc2087fdc92e9818cc2087fcca6e5818cc20c3fcba661818cc2087fdc52e9988442087fdc92e953844208efdc62e9538442087fcca6e55384420c7dcba64d5384420 else 0x97fdc92e98558c20d3fd982e98558c20a7fcca6e58558c20a7fcca6159358c20b7ddc92958358c20a7fdc9295a158c20c7fd81aeda954c20c7fd61aeda954c20a7fdc92c5a854c20c7fdb92c5a854c20e3fd982c5a854c20c7fd91aeda854c20c7fda96c4a854c20d7dd936c4a854c20c7fda96e0a154c20d7dd936e0a154c20c7fdb96a0a154c20d7ddb960ca154c20f75d9560ca154c2097fdc3aeda864420f75d536158364420a7fdca2d56364420b7f5c12d5636442097fccb6156364420a7fdca2e15364420b6fdc62e15364420b7f5c12e15364420b7f9c02e1536442097fccb6a15364420b3fcc86d9536442097fdcb60d5364420c7fd63aeda960420c7fdb9694a360420a7fcca6d99360420e6fca6695936042097fdcb2959360420e6fca62959360420b7ddc32959360420a7fdca6556360420c7fcba6556360420f2fd866556360420e7dda36556360420d7f5b16556360420f7d5316556360420c7fcba64d6360420f2fd8664d6360420b3fdc92e15360420d3fdb92e15360420bafdc62e15360420f3dd932e15360420bbf9c02e15360420d6fdb92995360420f6dd932995360420d3fdb96195360420f3dd936195360420f75d9560d5360420d6fdb92985360420c7fd93aeda858420c7fdb96a15358420e7dd936a1535842097fdcb6615358420d3fdb86615358420b7ddc960d5358420f3dd9860d5358420f75d9560d5358420c7fdb96a0535842097fdcb6605358420d3fdb86605358420b7f5c954d8158420f3f59854d8158420f7d59354d8158420b7f5c914d8158420c7fd85aeda94c420c7fd65aeda94c420a7fdc92d5a84c420c7fd95aeda84c420a7fdc92d5a64c420c7fd95aeda64c420a7fdca619954c420f6dd63619954c420f3f581619954c420a7fcca6e5854c420c7fdb9699854c420e3fd98699854c420c7fda96e1654c420d7dd936e1654c420d7f5916e1654c420e6fda9619654c420f6dd93619654c420f6f591619654c420e77da9615654c420f37d98615654c420f75d93615654c420f77591615654c420b7ddc92d5634c420f7d5912d5634c420b7ddc9615634c420f3dd98615634c420f7d591615634c420c7fdba655814c420b7f5c92d5814c420f7d5932d5814c420f7d593615814c420d7f5b9595814c420f3f598595814c420faf586595814c420f7d593595814c420e7f581546aa4c020a7fdc5486aa4c020c7fdb560eaa48020a7fdc854eaa48020e7dd8354eaa48020c7fd836c6aa48020c7fd536c6aa48020e3fd8360aaa44020e7ed8254aaa44020a7fdc84caaa44020a7fdc54caaa44020e7ed824caaa44020a7fdc8596aa64c20e6fd86596aa64c20e77d85596aa64c20e6fcc6606aa64c20e3fd86606aa64c20a7fdc8586aa64c20e7f581586aa64c20a7fdc8546aa64c20a7fdc6546aa64c20) else (if i<3 then 0x1208e01493360cd056006da2766cd90f60ed7c75e0d70f5a6d627578d5cf56ed547534d45f512d3d74f0d37f4c2d2c74acd26f496d1e745cd0ff42ed0a73f4cf2f3a2cdb7350cccf2dacb572c4caff266c987238c86f1fec7871c4c66f172c527138c46f0f2c3570c4c29f08ac1e705cc12f03ac076ff4bf8efd2bea6f8cbdeef76bd96f48bcaef1abbf6eecbb6eecabb16ea8ba8ee86b9d6e40b88ee06b7a6dccb6bed86b5a6d4cb4bed12b3d6cccb28ec7ab146c1cb02ebfaafa6be4af1ebaaae06b70ad1eb1eac06ad8ab1eaaaaa36a7ca97ea42a896a14a7de9daa7269c4a6fe9a2a616968a52e922a4168f4a35e8baa276880a1be852a0d6830a07e80e9fc67d49ede7a69e567789d6e73e9c867049b9e6ca9ab66a89a5e67a99d664c98be61e986660897ae5da97565c4966e57e958655094ce51694164f4935e4ae927648091be45e9106430904e4028f663bc8eae39a8df636c8d6e33e8c862f88b3e2a689f6254887e1f687661b0864e16a8506124841e0ea83360b0827e08e819603c807e0027fc5fd47f0df9a7df5f607cddf1a7bf5ee07b3debe7a85e9079cde567915e28782ddee7775dc0768dd8675a5d64754dd367465ca8725dc867205c7c6ffdb826c15ab867fd96a63b587060ed7b25d056f45acd64e5775584541d4964fd53904bbd27e4865178447d0f642150143e5cf3e3ad4e20371cd323334c68309cbe62dd4b042b0ca8229049d0251c91221347881bcc67617b4564145c48e10143a00c2c27608741a0048c0be0134000c7fda86d53148020f7f1815453048020e7eda36095244020c7fda86d53244020c7fdb86953244020b7f9c854d2044020f7798554d2044020f7d98354d2044020c7fda56c4a366020d3fd856c4a366020c7fccb6a19558c20c7fcca6e58558c2097fecc6e58558c20a7fdc12e1a954c20a7fdc82c5a954c20c7fdb82c5a954c20d7f5c96c4a854c20c7fcc16e99854c20c7fccb6a56360420e3fda56616360420d3fcc86e55360420c7fccb6a1954c420e6fcc66a1954c420c7fcca6e5854c420f6f4b6655814c420f7e920549814c020c7fdba2e95348020b6fdc62e95348020f7d9302e95348020a7fcca6c55348020f7d93054d8148020c7fd85aeda344020c7fd52aeda344020c7fd83aeda244020c7fd53aeda24402097fccb54d8244020f3dd8354d8244020b7edc254d8244020f76d5254d8244020a7fdca60d5244020f7e92060d5244020c7fdba615324402097fdc5aeda664c2097fdc1aeda664c20c7fd61aeda960c20c7fd51aeda960c20c7fd91aeda520c20e77d91aeda520c20c7fda1aed9520c20a7fdc92d5a858c20c7fd95aeda858c20a7fcca6d59858c20a7fcca6c59858c20c7fdb96a0a558c2097fdcb660a558c20d3fdb8660a558c20d6fdb9618a558c20a7fcca6e19558c20 else (if i<4 then 0x6376c300300f100180a08050200800623a90a5b0300050c18000c40c0006201003733618078080ac00190401e0062b0009800418000c560010110031008805080282008006268e28e1347147081982006008200341510150078a6da2e04002d08000320800800c55be08e26e21c23225201600600a900a08948400024f4503702a019d0e007001e02e0050067a281b81578c007800e837017002818fd17cd80a806400403341b80b80140546300b4605600600602d04703702a010019018a8e00ed06001003002d00000782d02381b81500c807e830008018016800003005411c0dc0a806403f41800f40000140c608e06e02a03201fa0c007a00000a005702003e00202281b012014f8c00c6870038037017002c0900afc6006343801c01b80b801202f808014003c05c00600a706007e02e002bdb7e28367cc0327036c1700200f817e51403a41a4ca40b402401205401d20c265205a01200702005f94593600e906132902d00900500902fca2c9b0074994816804802404417e5164ca4da466461a3803b41a41b402401a0200bf28b26c01c002265204803e047eb602a01901400f7060060030027000006822fdb01480c0030010326800002417c1140d806001400f40000100c808e06205403202801ee0c00c006004e00000d064f4802af1a00f0b9f003e02001f000f5201b246419341800dedb4024012f6c06df8a0d9f300c9a0c007a009037d4806cd1a064d060037b6d0090056a403668d032683001e801c0381140d80a406003f41801800800f401602208e06e05403201401ee0c00c006e00000c037064f48f1a00f003f00383202381b80880c805007b83003001b8000031043d16d16ca6c1bcdb83b801002005de6dc1d41d60de8bc008017f36f45e0ee00282ff9b001f0370016d23ad80b2ca526405003c02ac012474074e8ae52e30e1ce0c006e009602bb68b600a70028707a478d001f801438002aed9c01400a47576ce8ae52e300c8e0cc04e00903703d064a5fb29b48b1ab06a0200ab005d02541001d801011c1140dc0d80400a406406003c039c1801800c009c00002008e08a06e06c02005203203001e01d60c00c006005600001004502a036019018a8ed06006003002d00000600702281b01480c001003001e800002811c0dc064052a39c1801800c009c00001608e06e03201ed1d60c00c006005600000b04701449968e00a000303202380c80a5473830030018013800002c18c11c06403da3ac1801800c00ac00001608e0cc932d1d60c015605600800404703702a019014706006003002700000600202381b81500c807d830030018015800003011c0500b1266c18028000e08a06c03001c055a0c00d505a00000a06404703701900a706006a82700000501b837fa4416f8d40ad417802019011c0dc066c1800da0ac0000 else 0x580340b8605c01a2061929618180082d4a2b1b100040b45804130ec021194e010800ce084014100003c0a840060b4200f05a1000c400c40db6090025b0bad82000308337c028402da6c2745718170004160446e058028402ed3600d1812000c0c8c005d1606401c8018002200c001100209b88708c8af8018009c02be10000817ea291b01490c0031c00020d4830301000f10010050800c03c400601e200300408218189821c10c04400c4086e00102a00f101681f06f8e0e81904e00100f03e10800750aa38205405a270008ef86c000a840205be01e3cb60b800403c191ed8600601e2700081c002006008200330210050403c1684e0017000d548400080062000191688800200986c3be006403100310188330800c0c440620cc20040031418d1b00a0c00c010400606e2700bb614890318a44802840b40be0f23912079adf182d03c8050c00c0f80d8605a05496c9be46820a5b0537c2091206313410318bad81984c47d6c12f4f000661b8075b0318dc0019840060c08be300a083a5410aa080f45d6c100351210078018800c1684a001003038108025c084a42000018080800c0e042009702cb615f103c00565b0cc032d8596c10150031001c0a89c003084054006270008150018800c0b44003d0d800400c0f84a001d42003015130005800242b35229a960014d4b000a6d90d8536d96c29b660014db30009c000b440c82098064108000605a96c370005a100504081c100a337119b840652100300134518040158802000446521003005100180288c182652100400110020009a28cc38202001e23a909db0400c1804704100300f11db0400c03ced8600601e238209d48400c03c4600130008310020800c054400602b30439299049821894c824c10e4a64126087253209304320001500310422948822c10c0a8000405405a6be302a00f101500a0148cc000b22a4602001e200302d10020050800c010400601e230009800400c01020861048)))
def f3108L30 : PackingT := (314,5,7,14,f3108L30F)
def f3108H0_30F (i : Nat) : Nat := 0x7444a01d708007692c01de469049d8a01d2730074c09413705c814811e15100ba3241841670baa08c0ca8ba133829404e03a0c0213822a9460c905181201d00ed3bc03a00e00ef83ed0f60760d703680001d094148001061001140140
def f3108H0_30 (h : Nat) : Option (Nat × Nat) := lookupWord 14 51 6 13 5 4 f3108H0_30F h
def f3108L31F (i : Nat) : Nat := (if i<1 then 0xc7f5b5684a166020b3ddc52cd9860c20d3dcb36c59860c20c77db96c5a520c20c7f5b96d5a120c20a7f5cb655a120c20e775b5655a120c2087fdc52e99858c2087fdc92e98558c20c3fcba6618558c20f2ddc66618358c20c3fdb82e1a954c20a3fcc86d9a954c20c7f5b12c5a954c20c3fdb96a0a854c20c6fda96d8a854c20c7f5a96c4a854c20c7f9a96c0a854c2087fdc12e99854c20d75db56cd9854c20c3fda92e1a654c20b2fcc86999654c20e3dda82a19354c20b6ddc62a19354c20b7cdc22a19354c20b7d5c12a19354c20b7d9c02a19354c20b3dcc86999354c2087fdcb6a58354c20c3fdba6618354c20b3ddc92a18354c20e3dda92a18354c20bbcdc22a18354c20f35dc56618354c20e3dd986998354c20f35ca86558354c20d75db96158354c20f35d986158354c20c7f5b9684a154c20e7d593684a154c20c77dca6d48364420d775c16d48364420c6fcb66cda960420c7ddb32cda960420b1fdc72cd9860420b2fdc62cd9860420b37dc52cd9860420b3bdc42cd9860420d3ddb32cd9860420b3f5c12cd9860420b3f5c52c59860420e2fd98299a360420c6fdb9298a360420e2fd98298a360420e3dd9868ca360420c6fdba299936042087fdc92e96360420c3fcba661636042087fdc92e9536042093fccb661536042087fdcb6a45360420c7f5a96c45360420d3f5986c4536042087fdcb6a55320420c7ddb968d5320420a7ddca64d5320420c7ddba64d5320420e75da564d5320420c6fdb92d9a84c420c6fcc66e9984c42087fdc52e9984c420e2fcc66a1984c42087fdcb6a5854c420c3fdba661854c42087fdcb6a4854c420c5fda96dc854c420c6fda96d8854c420c7dda96cc854c420c7eda96c8854c420c7f5a96c4854c420c7f9a96c0854c42097ddcb215934c420a7ddca215934c420b5ddc7215934c420b6ddc6215934c420b7cdc2215934c420b7d5c1215934c420b7d9c0215934c420e3dda8661634c42097f5cb215914c420a7f5ca215914c420b5f5c7215914c420b6f5c6215914c420b7d5c3215914c420b7e5c2215914c420b7f1c0215914c420f6d58658d914c42087fdcb6a5814c420c3fdba661814c420c7f4ca6e5814c420d6f4c66e5814c420d7d4c36e5814c420d6f5b92d9814c420f2f5982d9814c420e3f598699814c420c7f5b9695814c420e3f598695814c420b7d5c92cd814c420d7d5b92cd814c420f3d5982cd814c420f6d4b664d814c420f3d58664d814c420e7d5a564d814c420d7d5b958d814c420f3d59858d814c420fad58658d814c42087fdcb6a5514c420c7ddba64d514c420c7f5ba645514c42087fdcb6a5850c420c77db9695850c420e37d98695850c420f749535493048020f761525452044020c75db568ca366020b2ddc62cd9860c20b35dc52cd9860c2087f5c12e99854c20 else (if i<2 then 0x8dbf69163560d600574572971800f7067000033fe28217cc683680001981140db77c06003801800b4000a93f8a585f30029a000146045036018006000003325b0050000c17c1140d80a406001800000d0292c6c052c0ce34c000c6704264502960671a600063382fb22b1b014b0338d300007a00bd9158d80a5c6980018ce0bec8ac6c052c30c0cc00006802d64563602960631a06338010079efe8d6836806001c03c02b41b400808f8727527bfa35a0da018008137d483a93dfd1ad06d00c00461c8ac1efe8d680600190e402b41b01b403000c05ba918727527bea35a0c74b6014064b1ab06e82b00380701ee836801000c05341b4009a340cda0da0043dfd483a9d1a0b9d06d0039efe8d00a6836016801b46819b4006a340cda0c30b9015064d1ad06c02d00382281b01480c0030000019d2d8052c180009f8a07c063f3001d60d600006803e003e8eb067b6b0030000d839c1aed9c00a9be015d1ce0d76ce0060dfbb600a7067002818801b83380110e4029c19c008000284802ac19edac00a07b60d600303db06b00181f5db00a83238d3833801c198190cdeed8055c69c19c01066e07be91e35e0de00605f04503601800600000338055800800ec1ac00608a06c03001c00c004000054874802a519a8e70670033a401638d547380150880bc0400c402281805004fd7fd17cdbc63c09a05a01005e014017009ebfe8be6de31e1cbe00edf10308418420c3a90063a34007bbff8bf6dd53f31d1da0da00da4368cca19e8269f967a49d2e7169bb66b8997e5fa971659094de50293f64b0915e40a8f263648bfe29a890620087ee1f687c61a485be10a83560647e4df2e7b85edc7a0de7e79e5e44780ddda75a5d1c72ddc5e7165c246fbdba26de5b2c6b4da9e6a35a7c69dda2a67759cc65fd91a645591062dd85e60158005ecd7365ba569c5a5d6565945604567d53a54d54dc508d3a64d653184acd27e48c51cc462d13e44250c841bd0223ec4f643c5ceee3a24e30375cd723464cb4316cc022f34b682c0cab629a4a1026dc982253491822fc87221248201f1c76e1ce46d41a1c68219045f416cc57e152454414fc53a13e44d0129c44e0fa439c0d0c3260bf4298092c20a05a40e0030c0b2028400087fdc52e93148020e3f9a86053048020a7f8ca5453048020b7d9c54c53048020f7d1814c5304802087fdcb6953244020e7e9a35492044020f769535492044020f7e1c25452044020d37dc86d4a366020c6fdb6694a366020c77db5694a366020d2fdb6614a366020d37db5614a366020c7bda56d0a366020d3bd856d0a366020c7ddb568ca366020d3f5c86c4a366020c7f5a56c4a366020d3f5856c4a366020a5fdc728da166020a6fdc628da166020a77dc528da166020a7bdc428da166020c7bda56d0a166020d3bd856d0a166020 else 0x1140d80600380180081ac0000a93e31e6c05da1d6045064219008b29f18c00000b024017394f8c006d8115d7fcd803781bc60a0be08a06c0300025906006800f4570ee02f183b877a2f0178c100b40b080c7c90f6c059c0043b6bc5b98a06b82a000643f245db5cc0075035c1700015201e01b41938009c9176c059c0043987c57b6606782e000643bdb036832700100f6c07a014009c0dc0060117c57b6798606e000643f243db036f0d4c77001b6db660967000190a07db8bb53b3180c0db8000c88031dc5db6d98c0606de0006442cc6e2edb6d4e03036f0003220e63921ed9e398180081b4fc91371047305c0050000054e3591d9bee90e00603d003706700202f9a299b18c007183180001a00f402ac1ac00806fa9003001da0c005d6da00054902d03774801003602a02901901800f00e7060060030027000008da407506fa4cd8300575b580201852d8199e08192c00c0fc5d1ad06bb83dfd0000f3800e340c6e000b4406371a9df70005a298d03182d0f77ff17edbaa7e63a3b41b40000d251c553a91a35a0da00674571a706702db69df70000f409bfe2e8d4dc1efe8000a1c1a35a0c0c7a00405ad1a063d0020056a41efe8d6836801946b41818c7a35a0c01f76c7bfa00604503601800600200000f3a5b00a005000100c4204610032830da458d5835801837c199c69c1aed9c00c04610299df74871a7067003030c47454ba403338d383380200005f63661800ee4860002a3ceff2401670d4c77037001ef16ea6e62419eda40000ce0d1a07815938ed00c00303c6a4098e8d68307a8369c76806002b5234681b41e0e3b400c533a900f00da71da006001ef5b005683680141b8bb53b3176ca00014640474807a519003bb670051243a4037b8d38326fddb3806c7200a8aa52a31a0ca0176c0067004047045db603602a02971a00e706003002066700000782383201658d58347a06ff41033580280100dc06400dc00168c26e0f02620bf600504503602901800e006000003400731b001b80108e7ad802a209c19c00c0be08a06c03000c00400001e805f00f71a7067002802007b6fd8d5835801803ec19a0ac))
def f3108L31 : PackingT := (154,5,7,14,f3108L31F)
def f3108H0_31F (i : Nat) : Nat := 0x681d814a1000e807403b013207c837c38c16207386403a01d006486d02401d04580770100110c4
def f3108H0_31 (h : Nat) : Option (Nat × Nat) := lookupWord 5 22 5 13 5 4 f3108H0_31F h
def f3108H1_31F (i : Nat) : Nat := 0xfc000c06a08d000e8100e5a00
def f3108H1_31 (h : Nat) : Option (Nat × Nat) := lookupWord 2 10 4 10 2 4 f3108H1_31F h
def f3108L33F (i : Nat) : Nat := (if i<3 then (if i<1 then 0x54633083bfed9b3108841dff6e58384420effb30c1c221077fd9560e11083bfedcaa7088417ff6e15384420effb30a9c22107fdd8354e11082bff5db42980415ffaeda848020cffd76d42401057febb68d20082bff5db46880419ffaeda344020affd76d0b301057febb69993082bff5db4ac98413ffaeda520c20defd76d29061057febb654830827ff5db50b18415ffaeda954c20cffd76d4aa6104ffebb6a1530827ff5db4ca98415ffaeda864420affd76d4b021067febb6a5810827ff5db50b08413ffaeda84c4209ffd76d3262104ffebb695310833fec0d54980419ff546aa4c020cffa43552601067fda8aa9200833fed1d5490041dfe4c2aa48020cffb07552401067fd53aa9200833fec0d54900419ff4c6aa48020cffb07552201067fd82aa9100833fea9554880419ff4caaa44020cffb4b553301073fd85aa9980833fed0d54cc041cff606aa66020cff96b553301067fd85aa9980833feb1d54cc0419ff54eaa66020cff963553301067fd81aa9980833feb0d54cc0419ff146aa66020cffa63553301067fd53aa9960833fe29d54cb0419ff61aaa64c20cffb0b553261067fd65aa9930833fec0d54c98419ff586aa64c20cffaa3553261067fd96aa9830833fecad54c18419ff646aa60c20cffb532a906106efda6954830837bed2caa41841bef6925520c20dfdb452a906106ff5a1954830837fcd04aa418413ff6e2aa58c20cffb31552c6104ffdb5aa9630833fecad54b18419ff64eaa58c209ffb63552c61067fd91aa9630833fed4d54a9841df764eaa54c209ffb71552a61067fd98aa9530827fedb554a98419ff65aaa54c20cffb27552a6104ffdb1aa9530833fec8d54a98419ff60eaa64420cffaa7553221067fda9aa9810839fecc554c08417bf6daaa60420ddf94d553021067fd98aa98108377edb554c08413ff6daaa604209ffb67553021067fd93aa9810833fec8d54c08419ff662aa4c420cffb2d552621067fd95aa9310827fe5d2a7440415ff6e553a2020efbb26a9d101057fdb914688082bfedca6344041df764d31a2020efeb2298d101057fdb961a330827fe5d30b198415ff6e5858cc20e7fb30c2c66104ffcba59633082bfedcacb19841dbf659658cc209ff974c0c661057fdb9606330839fecc303198415ff6e5618cc20edfb2cb0c661057fdb954633083bbecaaa319841dfd645518cc20affb72c1c221073fd9860e110827fe5d2a7088415ff6e55384420efbb26a9c221047febb6a1200823ff5db46880411ffaeda2440208ffd76d4b061047febb6a5530823ff5db52c08411ffaeda94c4208ffb71552401047fdb3aa9200823fed8d54900411ff6ceaa660208ffb63553301047fdb9aa9630823fedcd54a98413bf6daaa604208ffb73552621047fcba662330823fe5d331088411ef6d2aa4c020 else (if i<2 then 0x41ff760ca154c20effb74c1b221077fda860d91083bfedb306c8841dff6d58364420effb4ac1b221077fd8560d91083bfed8b06c8841dff2d56364420effb0ab1b221077fd8358d91083bfedd2a6c8841dff6e15364420eff970a9b221077fda854d91083bfedb2a6c8841dff6195364420effb06a9b221077fd6354d91083bfed8aa6c88417ff6d4a360420dffb4a51b021077fdba64d81083bfedb326c0841dff6999360420effb6ac9b021077fda564d81083bfe52b26c0841dff68d9360420effb2ac1b021077fd9558d81083bfec9ac6c0841dff6e55360420bffb70a9b02107bfcb854d81083f7e532a6c0841eff6195360420effb26a9b02107fdd8354d81083f7e530a6c0841dff60d9160420effaa6c8b021077fdb366161083bfedc326b0841dff6d59358420effb72c1ac21077fd9560d61083bfec9b06b0841dff6e55358420bffb70a9ac2106ffda854d61083bfecc2a6b0841dff64d5358420ffbb06a9ac2105ffdb814d610837fed40a6b0841dff6605358420ffeaa6c0ac2107ff453605610837fe5ab5098841dff6d5984c420effb62cc262106ffcb569931083bfedd32a98841dff6e1954c420effb50caa621077fdb665531083bfed332a98841dff619954c420effb4acaa621077fdb365531083bfedcb0a98841dff6a5854c420dffb50c2a621077fd98615310837fed330a98841dff655854c420effb52b2a62105ffdb8595310837fed42ca98841dff661654c420fdfb0cb2a621077fd9559531083fbec2aca98841dff615934c420effacac9a621077fd9560d31083bfecaac698841ff72d5634c420ffbb0ab1a621077fd9554d31083bfec2b2298841dff661814c420effb2ac0a62107ff4b560531083ffac2b0298841ffd595814c420effb30a8a621077fd83aa920083bfea9d5490041bff596aa60c20dffac355306106ffd51aa9830837fe28d54c1841bff6865520c20effb232a906105ffdb5aa9630837fe52d54b1841dff656aa58c20dffb6b552c6106ffd85aa9630837fea8d54b1841dff646aa54c20dffb03552a6106ffd61aa953083bfec9d54c0841bff60eaa60420dffaa755302106ffc53aa9810837fec2d5498841bff596aa4c420effb66c8d101077fd5364688083bfec98a344041dff65531a2020effb2298d101077fdb865633083bfedb32b19841dff619958cc20effb62cac661077fd9661633083bfecab0b198417ff6e1658cc20effb30b2c66107efd8659633083bfecaacb19841fdf615658cc20effb0cc8c661077fd8564633083bfeb2b2319841fbf2d9818cc20f7fb0cc0c661077fd9560633082ffedc2c319841dff661618cc20effb2ab0c66107ff58158633083bfedcaa3198417ff6e1518cc20effb30a8c66105ffdb654633083bfecb2a319841dff655518cc20fefacaa8c66107ff581 else 0xc5878a37136e221c327841705ce083c09b805efe5df95be937bf6f4dde4fbc077686e94dcf3b94f70bedf1db81b6136a46d17d9e3b2d76426c53d85baff35e06b8fd6d3acb7578eac0d51fa97b50be9f1d36ba5e7493e8f6d18ba2534216827d0039f6f3e0678fcea79ce337e66c0cd1f992331165e6cb5595e729ee50cc9cd930323ce45ec88790771f663c6c7418dbf1aa6323c6118bb7153626ac45d87f70f161a6c2bf8463073e0abc0f580fb0015fd1bf157d92f9f5f0dbda37a2af21de1dbbef771aecadd64ba517386e4d5c5eb8456f9adcfdb63b6656c06d6dda9fb4c768cacf059afb2fd650ac8358cab1336176c1bd7f0af695db6b98d70badcb5a22b315610ab7d55dea92d4f4a94551c6a0a53c2a70d4cfe97c529ba4a948368ddd17fa2c9447686b508fa09140327edcfaa9ef33d4e7864ec59d5539ba71ece179b333416638cc0997592ce6552ca53942f26664a3c8df90c3203e3e447348d6d19662e2c5318951107e1cb430d84c70796092c0b280c10065fa1be627b86f599e58bc07768eea75d1539e372f6e529c6bb8646fb6dd1db7ab6986b9ad48da3cb40666facb2191a31a061ecc0d97c0aed75c9cb6656722c6657e6ae0158c2aa5547aa7554a628b84fc49de9383a6474c0096b9298249148688da519c22c543c884e9048201d3f547d8cf831e883c82770ceb31c85387c6dccd5999d232ea6358c2c17982d9a5968af9153d299450809d1133a253648a08e59137218840107c30ebb1c7a36d066f0c4a17ae2c5c5470a0512f8242442f87890da818242cb0523096010441c402f404aa075c09100c500ba0003bfedd30298041dff689814c020effaa4c0a601077fdba54d20083bfe5d2a690041dff6c55348020effaa6d0a401077fda360520083bfea9b0290041dff6e98344020effb06d12201077fdba60910083bfedab0488041dff6958244020effb66c12201077fda360910083bfea9b0488041dff6e95244020effb66a92201077fda354910083bfec1aa488041dff6e93244020effb6a992201077fda54c910083bfec2a6488041dff2d5a664c20effb74cab061077fdb865583083bfedb32ac1841dff6999560c20effb4acab061077fdb365583083bfed8b2ac1841dff6558560c20bffd76c2b061077fd95685830837fe5ab50b1841dff6d59858c20effb62cc2c6105ffdb8295630837fed414ab1841dff660a558c20fdfb0c52ac6105ffdb129563083bfedd32ab1841dff6e19558c20effb50caac61077fda565563083bfed9b2ab1841dff6c59558c20bff974c2ac61077fdb961563083bfecab0ab1841dff2959358c20effb0ac9ac61077fd9560d63083fee52b06b1841bff295a158c20effb2ad0ac6106ffcb16a153082ffed8950a9841dff6558354c20effb2ab1aa6105ffdb8285530837fed4142a98)) else (if i<5 then (if i<4 then 0xdf014c0288107b306006c000018308df6908e7db32902b2a58d20e9040518300640523805300903a07aed9948159528e58d20e9040518300640523805300882d6bf37d1cb3696c05454b4863483a4101460c0190148e014c0000517a71a0b5c1805082e00001051762936d6d2a58d10640c18c816dfd04c010038096c5d6d2a58d3060c7b7f41300400b691b149beb61524674c063209b7f4730640c60841300401102a51762936d6c18c94edfd5203e4730640c00e4131a6008025b175b063d5320b6fb1a60cc010028026c5d6daa58d6980ccc1980243c4df28bb165b129d524634769801cc19031396008021d203c8eae34a3b8300a105c000028a2ec526dada54918d3041903064205a3b41300400fd8b6db5b4a9d308183268ed04c01002fa40c20cdc69477060148578024afedf28bb1654918d1da600730640c4e58020076c59525d74769860c8189cb00400ae903d816014e34057800004145d8a4db5b118d30419034820dfa39802006ec5b6dadb4c2069041bf47300400adbe4eb62937253aa48c918d31a380730640c00e413004011171b1754e8ed30c18054822eac01002c168642bfb7c9b936d6d2a48c918d31a3807003904d2180200902ddbe4e75b31ad31a3805482690c0160b437edf691b175b4a9635a6347306600c0cb37c23945d8a4dc9b6b6253aa58d48e60c41903682004c01004c32847d8baa58d69891dae183206d04c01003437f48014ae016f1a02bc1941700505a2bfb7c9b936d6d2a58d48e690c1883206d0400980200885adbed2023ec5d6d2a58d306d04c0100301480e0df57fa2f3605dc600b606e05801817c1202903219ba2f36e3143b83602c00c0bfca406745e6dc6387506c0580140a43e865005b7ea47c5f6c1b28d79801fa3a83500785f06e1e40802d0b400831d48f8bed8156a9a35e6007e8ea0d40260101b8360521f4075480de1928d798a0c18401e82a0100be1e40a8290c7523e2fb6a35e600200fd1d41808003d0540240a7a2f360dfc638700cc0dc0b00282ff45e6dca78c30e01981b81600505fe52023a2f36e31c3b03302c00a05200b247c50f1ed83686fc35e6007b8ec0d801d92014fc50dbed832e1af3018401b82c00c0be0a433348f8a0fb5c31af3005347306600d0041b833348f8bed8166a9635e600a68e60cc01c2dc1eedfe91f178d798015c1b41700585f052199a47c507ded98d798023a380700a60da098042a40780db4680aa8ea0d40115215c02d0cb4680ad065054013ca783010e8bcdb07702c008f6c7ec47d657a99f529e9bbd1ef9ebf333e5cfca6f932f203e36fc5af884f0bde0b7bf37794eec7dd23b8bf6f1ed97dac3b4af67aeca9d8bbb0475cceb63d5d7a9cf508e9dbd2f3a3af444e83dcfb79e3f396e6f7cd8399d7314e5b1caf794bf27ce481c86b8fa71ade30f else 0x42ff456530a78c318830c3a0740400dcdb01600782f6bf17f9b33686c0a78c318830c3a0740400dd170160088126bf17f9b33686cca61480ee8b01003718c05801e0a5e2bb6730191c1061b058020029db06d0c8186c1600300278aed9cc0610d81930040048780d81930013e2fb6f30e381886d70418416e00502978aed836b980c8e0830c02c00a06e0f9e2c457530a70d382804ed833600603178b115db43605386807066704196016006e487718683086c0c9800e009e2b980c2bd036064c008c90ee22286d7530a70d398830199c707881d818018025e98024187240477710df0d4190df03b0300570400b004007861022f1622bb686cea6148660060083261ac0d801e0e81561a01f1d72460687300b002a3ae48874ea70d41971d81a1cc02c0100181d02fe4878b1141b3a9853869cc41870504a0160080100d417f243b686c0a70d398830e0a09402c00d084f7e2f836c900a70d39883104a01415c00d0c017f243c588aeda1b3a9853869cc41800504b003e2fe487711141b3a9853869cc41283003d4760600600b004416bdf8beeda1b029c34e620941801ea3801802c9180200e9a2cc565219654b1a9308398330207b2093ab00782d4eacda5b0a9690c6981065904c0000300227566d2d99486595283a6f803104d218d014600002037da45c546f6d90ca12b30419015a9b04a390730020100da8dd6ff48e34a3a835a9b05c02802c157485e9c694750635360b8050050a0433d217a28ea0d6a6c1700a00a024d217a71a51d6a6c1700a00902bd217a5a9e34a3b83506e014014043a42f4634a3a835a9b04c0120fba402ce3418c0a7061efc0121901f3486521b58d20e96c051830f7600c07c1b7a46b6059c6847014e0c02841700000d07c0b5afcdfd6c8da4702a152d218d20e96c05183302904c00004c1b0636908498d30660403d80241f0f7e91ad854f1a10402b80000503e1ee2e75b23691cca654a0e96c00c41348634051800008b1a01e16ac130020060522381631a0b403d801c18879f6dc682d014e0c02841700000b0621846fb4598bed98c49860c019814820dec01c37c37f1a0b40185cf0000080620e83ccdf76cd2114c8e058c69074a9028c198103d904c0240a42d00f600406237c378b607bc682d00ae0000140c40206f6bf37d9b0b996c8a64720e95200c41348058c680a30000140c417c23bc588aea614e1a01d0eb03003505802003c18bdf8bf0e9db43605386a0200ec9181801a82c00f690cd81e86c634191830036004014009a403df6c1b18d0641be02980285b748e34380057003748e343800500376dc028021a42f4f6c1b18d06460c019010df600be91c687000a007c00cbd3a40a9e342385bf0657002b417005f48153c68078f6015c000020300100c897e4123966d2d994ca901e239a431a60c019014) else (if i<6 then 0x3a980501460118a00147108260118a00140ad2901460b8014949044092382c98230a907dc001b814282c07d4000a100783e91d2d880fb80014182c028c02000a9280a028c001f400283191d2a40a100501460100037bb6104701405180400206090537c0510053000c01900a140a00a6011da00147b00a6011da00140a80a60100080281f40082a8e4a0540180419045bf01154a8e0cc620497d094820c652640b66f8150cd208cc0080015006208ba3816ca91e8e05b2a464dc9928e5e903a192b69528d1c0b6548d1d48e0f26d95b4a92ea76004010702d91c3a8549c4701426e40307600320e0db238331df5be4dce1989be0ec0046004010702d91c308549c3360ec005d484dc8228e5e903a022b690480c84114740e808aa6411c9bc0e8090564114050e0e0180032482318227383b002b690460c84c90702d91d6d954c82400a0284dc8060ec00626e8383c48eb70b7cc4dc9920e05b23a5c2a939b617183b00175280305a2014050806000c86d8c1950706d05ab7c37980501420183b00137313a07523816ab6272660040016e8e152530583b0013921a905b800379032e820c337c8197410e21b00200184716821be605a809194820caaa4da082d084100a20180b001432c820deb7c86a70160018248440878c004029c1a81600022005757fa2f36057ca78c013e1c19c038050c2005a023a2f36057ca78c013e1c19c038050c2005a09c11f18a1c0400380502400520901180a80804001811002804808f8c004015c18080030220054013247c51ebed83661af3019303061b05801a18f2461a07504807e00382d0b504807e002831e913d01571a91dc1805082e0000160c67a71a0b4e0b8030039450b3bd283132205a3a8040048660c9d201671a02803f830b9e0000160401551a05a03c2d5003810a340b40785aa0060ddd203c82c055c680a00fe0c02841700000d0cdd201602ae3405007f06173c00002c238b9c3581a020610078010012a47c5073ed836119f3019283061007401a012a47c507bed83651af3019283061007401a1d85c064e91ad81671a02802801f00000c02a193a403d059c680a00f01400f80000603e0cdd22db02ce340500780a007c0000303374807a0541571a02803c05003e0000181802ff4568b11594c2960d08a03302005cdb07600782d05c0a79b30684501981002e8b8016025afc5f65308a14c10e3106183006e6cc0801745c1d802217da2b36652c618700800e01400a80702763002003805c0070100af8c000026014c03c040010c4d7c2ff4588aca614f1861c03b9b60601ac0a01600980f01000418b5f0df17f9b4366520a78c30e01dd170300d60500b0050040600bed1622f366530a58c41861d03806e0070080220580773601b81b00203105fe8ad1622b29853c600773660d01203602405802018 else 0x222e6dc600680528270214db8c1020c6014e5611142268b4db0c19a2b180260508001a0b00a0c060080260ac809c04005a6cc628100d39768ec57c37d3601b008e8119b318180c00201068119b09020070c2d1480b4008041a0400e18460900080463040cc1be020d0203001402c881017f4561c0b0059812004a8ac608300a05672b081202545220402e240801c0934521120020106449024041c1201e226405040b435883282d0d632641880a0c991a9028305403c16a8ea00505a1ac4c008002d1521aca238356000c8050a4c8315b6028406fc0041866f8640fa40c337d5b0640fa198c0507570086e406ec02800c1f0ea06e1f48a381bd00180a2004b61b90992f4102a05a226403c1f0e801325e8305403c16ab651c50544b45c011b9df18ea0542600400168ea0545a01048078e804120c632648cb5b4b691c050d2d83ea371b00a000dc603c1f0b80040505ae00305aaa40a0a9601238c0b554cb60282a647180a05a0de36001bc4aa43789023b61003408ed8603d1d090200f0c4305a00c020cc72040c90109801023b61a0406e8b46812024361ee4b6c6d80a98e028540980048101881418310b208cd4866280476c00c681018a3602843e88de020b90f253528120200e028576c6d80a8142600408a0861686f86f0f4028ac00323b60144224ed83c80a211256c18c6448303b601440b40416feb60c65224181db00a206c0b4b7c6449db07931c028a0b432232905ad8a4dc16a3296c460044a5b063205a4bfad8319005082201800326b63700d6c1986383804df0de028a3d1412391720f4ac008005a9bfad84706339a9c001b35b12c77000c8028800e80404d6c40083da804005bfad8019f5c07d12b801e0406ae007810180fd70205a8dd194b823002000425c00f280fd7020142e0806004ea50141691ba00a0050f08dc336b823002000425c00f11c63538013a8c050b82018013a940508e46e8028014870f5d701f4802a5b3003bf1d4a02a5b07d8ea4e001b0610c0a8610c830c8054053b6505400dc001b880ad00101505a0a860b408bb6014402a0b4150c16811014326e05619079250002a20540540a28e202a1d4200605440280aa00a001915b198006102a37c3214050ea4014011b958002d02a0a8800d0a880501526e4030014050c24001f45b439303e0cc77c3e93796c63528549be00230005a0565b02a29b6c012da1c900ad0080023831968040082a03c47141681190405080b6db01591c052411816b0026e3904c021c8cd481402b238805680400006208a77c05015b6cc0241181681191d6d80100a300a0b41bc723980064180a91cc001c900886691c02880040440080c401100009c060565058051804628009d4c0280a3008c5001)))
def f3108L33 : PackingT := (374,4,7,15,f3108L33F)
def f3108H0_33F (i : Nat) : Nat := 0xba80611018a80598892d03b0812a908240a592457a310020c00ac7055b000bc145e024606dc8337c0cdc0de3050004ea0134800e4045403de001448f0e073723c9405288b9502d182fd01d327125068b840480fac21d0050903184a22e11fc047e0372546ea1123061a2176d0848510711b8046b81c72077806b902e4c5298014a067f824f41894098f410882b7422920ed806a604114177688fb06080317108080a9e0841039f8237c02a3072d037400fd60fda048303b940e860a7f077b8274d23b0027400f98247c0c70099208670203d12a806e6052183c5812c80be1025f04364171c08ea085e80b4010f404ca035600c200690f20c0411016e119d805cd046383fd11c800f07041fa04fc018013a003fd019dc1f18068800880250c0210022b036a0386c0d2802b009d523001192a05e408850363c23da0b0a00c703278002085ab460b801b00dfa01ef0852024a014661001465c040a408c0054e0572236b813d00311065082d1819de120805b7832d80a520d0404e2a4630090a086848868323592780eb4013602d6420f001ca07a7827ec0ea013a8007e843bc1e7c05d20661806d8230005f009d4810c02744514009d1020701e4013a000c804eac01b611c5036083d601094016405ef215a40c040d2603dd0465005da21b3590780a21e22c0c74032a8236410a4293306b114815121c0e43027f8127c0e1a48c808ba8474008280d98588682a9c0b2013a009d59c8001c18072708b08c4b411680dad4004a16fc22328c6642cd840c02754044d05e082ce0010e047346e2010300ac41159246d8001c1fc08cd3057900c841f26e94307d7816101a74088e030c80dbc047a0174022e002c4009004d704d902dc8916407af0093806b81512057903c000258227a91b0074781e6806a804e6028903ef41c46055c07b500bec14da097f01bd8354027540fc3084f0082d0bde064d044f025681bfe02134762801e420a6005e00ed03a9c0a62003744c9a171404a4c1c2190081af00852013003e581434066a015a42f80301c162e10f3a88983b34165a071f0398441200308340000000fc0e1c050000e00080042c06072d8001a000043a001cbd422620401004150081c1c0c0f0080205058cc140a0583490000b09044070108c2600000044804068440c32070240c05018150400060480007038302a0800810021c02800120800000160b050040e0c3880c7219128900000000000e030d0c07204
def f3108H0_33 (h : Nat) : Option (Nat × Nat) := lookupWord 115 358 9 17 9 4 f3108H0_33F h
def f3108L34F (i : Nat) : Nat := (if i<5 then (if i<2 then (if i<1 then 0x655310833fed432a988419ff699954c420eefb4acaa62104ffdba61531082bfedcb0a988419ff6a5854c420e7fb30c2a62104ffdba21531082bfedc90a988419ff6a4854c420bbfb6e42a62105efdb621531082feed990a988417fb6c8854c420bfeb6242a62105ff9b0215310827fedd2ca988419ff6a5654c420cffb50c9a621067fda664d310833fed2b2698841df76e1934c420efbb50c9a621077ddb664d31083beed332698841df7619934c420efbb6ac9a621077dda564d31083beec2b2698841df7215934c420efbacac9a621057fdb960d310833fed4b0698841cff661834c420efbb26c1a621067fda958d31083beec9ac698841df76a5634c420dfbb50b1a621077dd9858d31083f6ec32c698841df7655634c420affb72a9a621067fda954d31083bbecaaa698841df764d534c420cffb50c8a621067fda564531083bfadc32298841dfd6a1914c420efeb4cc8a621077f58664531083bfadab2298841dfd695914c420efeb0ac8a621077f48564531083bfab2b2298841dfd60d914c420efeac6c8a621077f553645310827fedd302988415ff6e5814c420cffb52c0a621073fd9860531083beec9b0298841dfd645814c420efeb72c0a621077f5a960531083bfacc30298841fbd2d9814c420dfeb4cc0a62107bf586605310837fad2b0298841dfd655814c420ffa966c0a621077f59360531083feab1b02988413ff6e9514c420cffb52a8a621077dd9354531083bfac8aa2988419ff661a50c420cffb50ca8621057fdb9614310833fed4b0a18841bdf695850c4208ff974a9a401047fcba4c5200833fcd426090041df654d3048020efd2a4982401077d9314c1200823fedd306880411ff6e982440208ffb74992201067f9a348110083bf4a924088041dfc5452044020abfb6e51b301056fdb628d98082bbeda946cc0415ef6d0a366020cfbb4651b301057f5b128d98082bdeda142cc0419fd684a166020e7b966cc30610677db9694830823fedd32a418419bf6999520c20cefb4aca9061067bd95690830833f6cab44418419fd6e5a120c20cfeb2ad09061067f995680830823fe5d330b1841cf76618358c208ffb74cc2a61047fcba661530831fed4330a98415f76e58354c20e7bb30c1aa610775d9560d530823fedd106c884157f6dc8364420adfb6c41b2210577db520d91082bdeda106c88415fb6c88364420afeb6241b221057f9b020d910823fedd0a6c88415fd6c45364420cdf96cd4b021073f4b16618108337ed494cc0841cbf660a6604208ffb74c99021065fda764c810833eed1b2640841cfd66181584208ffb74cc2621047fcba661310831fed4330988411ff6e9954c420cfbb4ac9a621067f5a564531083beab1b22988415fd6e5814c420e7eb30c0a621077d593605310823fedd32a188419df695950c420 else 0x419ff6e5a854c20affb72542a61067fda92a1530835fed4150a98417bf6d8a854c20bfeb62542a6105ff9b02a1530833fedd330a98415ff6e99854c20e7fb50cc2a61067fda866153083beed9b30a98419ff6a5a654c20b7f970d32a6106bfcb8699530833fecc34ca98415ff6e99654c20cffb50cb2a61076fda6659530827fedd30ca98415ff6e58654c20cffb52c32a6106efda6619530833fed4326a98419ff6999354c20efbb70c9aa61077dda864d53083bee54326a9841df76d99354c20efbb4cc9aa61077dd8664d53083beed8b26a98413ff6e98354c20affb72c1aa61067fda960d530839fecc306a9841ddf6558354c20efbb26c1aa61077ddb960d53083beed4b06a9841ef72a18354c20efbb30c1aa6106fdda660d53083beecb306a9841df76558354c20febb0ac1aa61057fdb958d530833fed4ac6a9841dbf6596354c20eefb2ab1aa61077dd9358d530833fed4b42a9841df764da154c20affb7250aa61067fda928553083beec9942a9841bfd684a154c20cffb30d08a61067fd96684530833fed4346c88419ff695a364420cffb74c1b221057fdba60d91082bfeda906c88415ff6e16364420edfb0cb1b221077dd8358d910833fedd2a6c88415ff6e95364420affb70a9b221057fdb654d91083beec1aa6c8841dfd6c55364420affb7029b221057fdb614d91083b7e5b352c08419ff6d9a960420cffb66d4b021067fcb36a5810839fedb330c0841cff6cd9860420e7f966cc3021067fda9699810839fecc34cc0841dbf6a4a660420e7fb52c33021067fda968d810839fecc346c0841bbf299a360420affb7251b021067fda928d810839fecc146c0841bbf298a360420dfbb4651b021067fdba64d81082bfedd326c0841dbf2999360420e7fb0cc9b021057fdb960d810833fed4b06c0841cff66183604209ff974b1b021067fda958d810839fecc2c6c0841ebf61963604209ff974a9b021057fdb954d810833fed4aa6c0841cff6615360420efbb26a9b021057fdb914d810833fed48a6c08417fd6c45360420cffb4ac9902104ffdba54c81082bfedcaa6408419ff6a55320420dfbb46a99021077dd9354c810833fedd330b08419ff6e99358420cffb50c9ac21057fdb960d610839fecc306b08415ff6e55358420cffb52a9ac21076fd9654d61083beec9aa6b08413ff6e85358420affb7229ac21067fda914d61083b7ecb0a6b0841dfd6e58158420efeb26c0ac21067fdb86a5310833fedb352988419ff6d5a94c420cffb52d42621067fdb96a13108377e5b350988419ff6e9984c420affb74cc2621073fda8661310833fed433098841dfd6c5984c420cffb52d32621067fd98699310827fedd30c988419ff6a5864c420cffb52d2a621067fdb9695310833fecc34a988419ff659a54c420cffb74caa621057fdba) else (if i<3 then 0xa364735ea358d353b34e9348133f8337a331d329f324231da317d312030b8305b30092fa12f232ebb2e3d2dd52d6d2d102cb32c402bd82b9c2b3f2ad72a592a1d29d629792906289e283627972792274b26ee2691262925e225852549250d24b0243d23d5234122b8224521c7214920cb20581fda1f671eff1e811df81d851d071c7e1c161bf01b671ad31ab81a9d1a1f1996190d188f1811177216e9164a15b61522149913ef1324129011e6115210b3102a0fac0f230e9a0e1c0d9e0d200c8c0bf80b7a0adb0ab50a16098208ee085a07d10753069e05f4055504a0040c037802fa027101c7011d00890000cffb50d0a601067fda5685300833fed1342980415ff6e9814c020cffb62d42401067fda868d200833fed2b46900415ff6e95348020cffb50d0a401067fda3685200833fedd302900415ff6e98148020e7fb50c0a401057fdba4c520082bfedaa6290041dfe6c13148020eff370982401077f9a84c120083bfcdaa6090041dfe6953048020eff362982401077f9a14c120083bfcc0a6090041dfe5453048020cffb50d1a201067fdb868d100833fedab46880419ff6c9a344020affb74c1a201067fda8689100833fed2b44880419ff68da244020cffb70d12201067fdb3689100833fedd304880415ff6e98244020cffb4ac12201067fda3609100833fedd2a4880415ff6e95244020cffb46a92201077ed8254910082bfedd264880415ff6d53244020cffb4a992201077f9b848110083bfcd424088041dfe6d52044020eff34a902201077f98548110083bfcd9a4088041dfe68d2044020eff306902201077f953481100833fed3346cc0419ff695a366020affb6a51b301067fda528d980839fec2946cc0415ff6c4a366020edf96cd0b301067fda6685980833fed1b42cc0419ff28da166020affb6a50b301067fda5285980839fec2942cc0419ff6a1a664c20affb74c33261067fda8695930833fed334ac98419ff6a1a164c20cffb4cd0b261067fda5685930833fedb352c18419ff6d5a960c20cffb62d4b061073fdb6661830839fedab30c1841cff6c59860c20cffb52d33061073fd98699830833fed4b4ac1841cff661a560c20cffb74cab061057fdba655830833fed4b0ac1841cff6618560c20cffb52d0b061073fd98685830833fedcb4a41841bdf6c5a520c20cffb74ca9061067fda5654830833fecab4241841bfd6d5a120c20cffb74cc2c61076fdb666163082bfedc94ab1841bdf694a558c20cffb74caac61067fda865563083b7ec332ab18413ff2e98558c20affb72c2ac61073fd98615630833fed4326b1841dbf6199358c20affb72c1ac61073fd9860d63083beec9b06b1841df76e58358c20efbb2ac1ac61067fdb86a5530833fe5c352a98419ff6d9a954c20cffb62d4aa61067fcb16a5530833fed4b50a98 else (if i<4 then 0x6d04d06f9230d0150cbf17db1a9f3063b03682c00dc9186801865f8bed8d4f9831d81b002c2103ea901be8d00376df14367980c941b4150072b80ca1846ca5873480dec6801db6f8a1b3cc06460da098039a406f6352e0055b6f8a1b3cc06460da098036a42b8a340556ffc5f6c0b7cc58ea0ca0a80355c059a341240aadff6c0b7cc58ea0ca0a8036a42b8a3403d6ffc5f6c0b7cc50650540181e07b4b8691ad98d00a0fbe61833005d4806e0d81487da3403c01fc5f6c1b3cc68ea0da0a80402483e03346807061023f17db06df31a3a83682a00fa90ad83ed1a02802be2fb60d9e6347506d05401c17c1b879a900aa8d0030c7f17db5a9f31a3a83682a0100f35201651a01418fe2fb6753e6283682a00d0f35201651a00619be2fb6753e6347506a00d074056a451a80819be2bb6f3141a802c073480ccc6801fc5f6c1bfcc68e60cc018184088df072d203331a015f17db06ff31a398330078600737d031815690c690900abbff17db79860cc01f5215c51a05a197e2fb6b53e6147506505401b5215c51a054197e2fb6f30a3a83282a00cb7a7b713b669b601b5a4b505b466b3feb396b32eb2d1b269b22db1c5b168b137b0dab067afffaf8caf24aed2ae54ae0dad63ad06aca9ac4cabefab7cab2aaab7aa65aa13a9b6a959a899a83ca7c9a76ca6b7a62ea5d1a511a43ba3e9a376a319a2bca23ea1eca179a106a0889fde9f299eed9e6f9e129db59d589cda9c3b9b9c9b4a9aed9a8599f1999f9916986c97ee977b96fd96a0964e95fc9589952194c4943093d3934a92ed929b924991aa91009077900f8fbd8f6b8f198e858e3e8de18d848d3d8cd58cd08c7e8bc98b4b8ae38a4489b08948890c887887fa8792872a86ac864f861385b68559851d8489843783da837d8378833c82f582b98267820a81c3812480f3807580187fbb7f537eeb7e8e7e267dd47d827d257cd37c607bed7b7a7b127ac07a4d79e57993792b78d9783a77a6771d76b5761675e575727562751b74b37440740473b27313729572017199713170b37056700f6fc86f556f506ef36eb76e396dd16d696d0c6cba6c686c216bda6b726b156a6069f8696468fc689f684d67f06793672b66ad664565f3658b64ec649a643263eb635762fa62a8626c620461a7613f613a60d2606a5fcb5f4d5ec45e305d865d135c5e5beb5b785b3c5a7c5a1459b7592e58b0583d57d5578e573156be564055d8554f54f2548a53ca5362531052a8522a51d85186512950d7506f50074faa4f214ec44e674e0a4d974d2f4cc74c5f4bf74bbb4b3d4b014aa44a3149c9496c490448b2483f47e2476f470746524592456144f94444437942da427d41ff4197415040fe40ac406540083fc13f593eba3e473ddf3d6c3cee3c913c133bc13b643ae63a893a0b3982390f3891381337ab372d36b else 0x524600a80e970c1980003904ab8b2e2d4815b3123983300006902b2e18000a90450257165c5a9b30c000548245c5b536600248e170c19800034cdff8acd837f9841da381eb0660000d60541eb0660000ca18433306600190ef9a6ff48015c683cf0676dc01037c3374846eed80571a0c7c1b80281c83de91c683cbb60cdc1b80246f866e900f435f1a0c7c1b8024300119bf2383203966c1ada431a41c199833007003c863634c010928e303de900e4333b6e35c1b8020337489706a78d28e015c0100b65c015b312398348260000d20b65c598904c00051816d9802b2385c30660000d0d225c31a0ca0b4aae2a451a0ca0b4ad235c02a634c1980064d0480c8d20152b86356614730620c81140a832748571c6947706505c0121b81b80c011d7fa2f36a53c6287606e05801a1241b808ebfd179b729e3143b03502c00c05c005aff45e6dca78c50ec0dc0940c404014057d7fa2f36653c6303702582f05708809f5fe8bcd994f18a1dc0960440400d00bd7fa2f36e53c63033025801abfd179b729e3143b83602c00a0de006aff45e6dca78c70ea0d80b002c00f5fe8bcdb94f18a1d41b016005001ebfd179b729e30c3a83602482f05602e0275fe8bcd994f18e1d80960b41580a018013aff45e6cca78c70ea0cc31c1e30d061dbfed82cf9802b80141bcc7648c343d430fc50dbe600ae00598ec901e30d06d0c3b7fe2fb6f30057003324078340187e2fb60da05700270018edbe30f19230d0150c3f17db06df3063b03600664837008c0e061dbff17db02d02b818c160069b80ca20f01845239a44f46340aa6ffc5f6de600ab005a8ea90bd28d02a5bff17db5a9f300568031475480d74697a5325bff16d4f9802b4018a3aa42f4a340a96ffc5f6de600ad005b489e81ac994a09bff17db3a902ac01604a471489e81ad8d3329bff17db3a9f300558039a44f463405401cdff8bedbcc48e60cc0193d1a406b634cc80acdff8bed9d4f9891cc198038113489e81ac8d13202137fe2fb6753e600ab6a400ea341842f83ef8a1b7cc68ea0dae280343286107cd235b31a0281f7cc306d70c0180dc01064a900aa8d00fbbff17db6a9f31a3a83500784906e0380c829a901e28d05f06377fe2fb6d53e6347506a0120cb5201651a028193e2fb6d53e6347506a00d0521943786c6901b58d00fbbff17db6a9f30c19803c1886f6901b58d065029f17db6a9f30c19803454df40d6195a431a464052effc5f6de618330071f4c918680a9dff8bedbcc18ec0da0b0030fa61a02a77fdb059f3063b03682c00b3e99230d0b902a77fe2f9831d81b4160061f4c918680a9dff8bedbcc18ec0da0b0030fa648340054effc5f6c63b03682c00b3e89230d0153bff17db79831da0b002f241f4c34054effc5f6de60c7606c00b3e808b2421a020054effc5f6de60c76))) else (if i<7 then (if i<6 then 0x32f98a0da0a80064494526c4a48c01501f41a800034bb602a0528000a2d0058aad954a980cc01a010000c877d618433506a00190b77ee2da902b66183300006806e0f86fb48b6d2a58d00a60019940dc32748b6c2a78d00f015c0120dda4229970c6980079be88bbf716db015b3003d8330000690c7f17db79860cc00019c30b484732d81631a014c0000066503a9bf3151c82c6340501ea16fac556c0b7cc68ea0da0a8002a515f28a4d88c01501f41a80003482d0c857d5b439a6c0a854d48a350380a50680402a80401b83e05ab7eafbb626c0a854d48a350380a50680402a80440a814a000288193a40b607a0ab8d00f015c0120466fb4826e4db5b02a952038330030041918d30660100d40543205f6908dd1b5b60540a64706360c41801c82634c02418475348d8b6db5b02c9521983200a634c198038eff4807a6a78d014015c010045a46c526fad8548036344a5000665b48be808d83003634c0031da949493e80b78d066e0061844dfa402de3419b801fa41f405a77f8d014e0076907d016f1a0cdc00c77fa41a9e3418c1e80ae008e907d016b1a0ccc00c37c3374806e0ab8d00f015c0120dc0a87d4bf77da402a05203e47306970c69803962ab6552a620948ea0d00a8000f52c5552a620950680418e8000f4ac556ca620950680418c0000f91ca024f15db3a950418e8d50620100007ac0abc576c03dd4b98a000290f15d4812505a0831d1aa0d4020000f5bdf78a03dd4b98a00028f5203cab8a3541a804007e8878aed809282d0418e8d50620100007adefbc576c03dcc015a00029003c0ad4876d0e41600a50546a83500580fa90fd21c823014f7e8d506a01001d4b00780a02af7ea402c57146a83500514526c4a40a8020c6c698310040003d7716db015b53239834826348008000f5db602b23807064634401000144815b8b6dad4c820c6c698310040003d76dae286302b6a583682634c0007aae2812b5320831e82634c198000f506302a0f74131a60cc0007a3a44390cdc6b834b8d05c010d209bcb8d04c69800663937e901985c71ae0dc00e0f808b5f028d225c31a60cc0125149b01591c00831b1ad04c188020001ecb8b6d80a86391cc198d68240040007ac0ac8e01c1998d6824000511716db01540520831b1a60c4010000f5ac5552a62024b8a0d40001a16fac556ca6202506a0000e4125e2ba9730a381d506a0000d0f15db3a97300528350000687bef140aba97300528350000690075203cd1a0cd41a803f4402d730a381d506a0000cef7de2bb67300540a506a0000d200c0a864a90ed81651a51c19a835005803a90fd011d1a0cd41a803a9480302af7ea402ca34051473b6a0d4016010323c576cea68d28e2000512011e2c040ccea68d500028a392011e2bb60cd4694710002883bfd225c0a9e340500570041452 else 0xc918680a0b987471727d32461a0cc0e8c03e1b0f7c9186a1d1831fc5f6c0ab0d606d0580007a4ef9c536c66003204c0000d01b8020641726d93ae3685303801882c900b30d014c0103be8d87be480598680a0b947493be6a4310310d83dd3ae3685392036e1ac00d4080c4337c5f6c0b30d60002891729d7241a9c358003281540f7c906a70d000172054ff14367980c9419db5000068f8aed8367980c941a8000347c576ded83679871d41a800034d48f8a3dc1f51af314180186fa001917f17cc506570ed8365008001913ad83287d0d8402000643d480df468050780da37e8038e4b45b8a4d994da96316618758e60c41980100006eb8b6dad4d98b1cc00051da2b29630c3870306b6cc0001a5a2db60d8c603203d3345b8acdadb329b52c62cc10e07ac19800036fc5b6c1b3cc58e07ac000523a45a9e341e5db00ae007690c69801121ec56903d98d3069be1bd80064b1c9690c69830df1ec1bd8058e40e0e901eb8d4df82aedac770048162ab6552a6089506d0540007a7e2936f6c1b3cc58ea0d40001a6890600c917e94d8ea9146a834020f2029db50071370e80f430529a9146a83079571401651762918d30419030029e81b0802000c8c48b7150c59801d3d103106d041b1001000c8db8bb16cc69821d238832064052087a06c200800323fa4039059c685b7061be1987b700503e690916e2db606c8a6d4a19431662c71060cc4007bc030b4896d6a58d58e20c198800f750f60c9d205cf1a07bc18330b8e00ae3437c7b05ae0050b41803205f26e4db5b4a9635239a43060060083586360110628d87bb1a690c1801b000de91efad98d34860c0298006f400f0b41b1a46c5d6d2a58d3060141b5803032348d8a4df5b31ad3000cd4b00224b6908d87bb1a60c00ed4b000c96394193a46b607a6a78d18ee0dc012b7d5c548a340b40a996ff485700ab8d282029c0105142ceb805408d8d30660018f412802348b8a8dedb02a634209801000ccb01fd215c02d5bfc6b83282e00901ed2023859d700b36f823634c198068267c5d6c1b3cc506d0540032216fac5552a6089506d0540007a41b876020190afeb686caa69480f11d5228d50680402a80441bb48252c6807b069e8c035c243234863405183300d70706e57c1531a01ed2183300d7090620a58d00e4ead2183003904c011bad8d34860c02a41275600701ed201631a60cc035c1c7af4806e6a78d18e015c0100dda41a9634c00896b83a756900a58d306006c011bd8e4b48634c190300a4eac010058e4b45d6cca58c30e60cc0001a0300030713d0afeb665218da431a60cc018f15db3a97300568350000687bef15d4b9802b41a8000343df78aed9cc015a0d40001a2e2db6b52056cc00f60cc008000357c566ded83679801ec19800034bb60c9d206171a02803c057004ac556caa4) else (if i<8 then 0x265400151c1b82d0c857f5b4360542a6a451a81c05283282a0540200f835d48a350397a066a0ce0a815005f480ea37f8d706015ad875700483707cd20154a963403a7a06660c40b416b6600e0c23a9a46c50c80b254b1a0ccc1b416b6600d58aaa54c412a0ca0a8150001e9a34e0831d008245d6d37ca2ec506c18c94ea9634c180ab0001ed0c20fb6286496daa58d015600052472e6f863024c698330202ac0007a5a2863652c6983302d6cc0007a43100f07d3d035b48634c19816b6600b7bff17db51aa0ce0a8000f43f4a3418e8005a2863f8aeda8d50677140007a031fc5f6d46a83382a0003d0ee28d382a00168a57da2dc566d6d98d30620cc0ac130020003dbf17db79860cc098000f3937024c6819066062c002d202cdf4046c6a548636001690026fc683305ae0050147d38d1df0b5c00c7d18d0660b4c00ab155b29850419680064394526d46a831020df40007a018bb6a341be80014350058b5155b536852a628c006505408000643beea341b2800652345b8a18c1531a60cc0ac15b660003d7d201571ab716d8ef814e008e900ab8d0b9b6c1980a70040611bed201631a1ef6d980066495f0c7f141551aa0d6e28000f483a58a2d94c2820001e4baa09b8310cdf141651a3714000a2432748055c685c814e007062c69a4306272c00379c1bb480d6c69013000f37d1037fa406be341985cf003ac556ca620948ea0ca0a8150001ea5beb1431a9882541a81415a0003d4f15db2a90c7469c1012a0100007a9efbc576c0b28d50670540007a42cbf404746831d000b4778aaa409063a35419c110080003d4f143182ca35419c13b6a0003d352036d1a0f3402003f4381502418e83382a344020000f4f483e8aa78d082029c00e51762936d6c0a431b1a60c40b4110040003e47382fa45b8a8dadb4a963523983202b04c0007b430831d8b6db5b064635a088020002923980c8325c5b6cc6ac1100029239337ee2db60252a431b1a60cc0ac130020080007b98d06560003c92a4afb4566c18d8d306604c0007a811843331a0d8c00329df30df01fd2035f1ae0c3dddb7004862062d21db229634c19813002eaa690c1835a3255250c818fa41f4e35c1b801c1b945d8b2d81486363523983102d044010000f75b648b7141b063952c698301560003d64dc189b6d8a1998d48e605a0980100400051a0cae2866635238070156000513714094a90c6c698301560003d2d16e2b36b6cc69831020c6c008000f5fc5f6cc69835820c6c0007a0379b86346098005a306fb70c698005ab04601e1bda4047b702398d306601609402723d654b48634c0032815403d634c009c8152bc576cea5cc01531c81a0320080000d60b5cc01531c81a0320080000d29151b2290cb86b03682c0003d2714db1a93300190260000683e9edb2402cc358000a9c321a9 else (if i<9 then 0x7fa2f36e53c6183003002828a4d89491820c81001801450668acd994b1861c03083003002aa0c0b58c30e018418009e8335f68acd994b1801841801801534566cca58c30e018004ed7da2b36652c60060013f45e6dca78c013c0580003a0a29362524608720400600500040382dabfd178c5180cc83a8750600dcd994e02c010022187a2a29e6d80b8c6000cc84be563a2f36055c6009e02c0001d457ca293623043902003002800201c1202f4bf57f9b536a520a587745c05c6283600806100e0bdafa5fe8b83a94e02e318039b30af94526c4a48c204006005001c0085a00857f2fd0e81dd1701002653c6300000e6d41a20040382d02497eaff36a6cca494d0e01dd1683006e3180b004009b4566cc3815f18c04004ed159b30e20c01015f1801580800a9afb4566cc3994f18c0400500b587106653c6005602002801000402745e6cc3a83106653c63012dafb4566c0af8c60200276bed159b00420c0af8c00ac04005402000804e8aca587736a0dc63012804001008d7f9b30ee8b41994f18c04b76cf16e29b6731660c706c40d019c1582401000323de2dc576d6d8d4b98b306383620680ce0ac120080019200c81886f02a1b4af142c878055869033829bf8003258e58590f01b70d0641bf802c720026480f01b70d6000c20551f17cc6063701b1db6000c8878b715db398b3081a031820d9800322de2dc576d6d9cc59831c81a031820d8802000647648b8a3dedb06fb5386acc4060061b56fe000c8e065920dc61a0ca0b4309c2ce48b7186832e060db60901672402cb7186832e06c0160936d8efbc5b8a6d9d4da9c35819c1582c0003da714d499830484b0000f39df78b715db5b635386b03382b0580007b1db3dfbbef16e29b6353869034067056090040001ef78aed9d481540d018c161a40100007addb3df78aea40ae0630586b0000f53df78aed80aa0680c60b0d20080003d6f15d4865a35419dc50001e878aeda8d3820cb400079de2bb675346832d0001e778ae61473b60d8419c11008001914e614707d0d8419c11008001912ed9cc07d0ca1b0804000c8868b7149b329b52c69831066056098010001edb8b6dad4b1ab31609800144345b8acdadb129634c198158260040007b2e2db6635662c10656000510b155b0065044ca8002a394526d46881065a0003ce916e28299e8862cc06c40c41901582400400323ae2ec59536634c48e1e81b083206b05a08802000c8f68b7159b5b66536a58d306204c008000f65c5b6d6a432b1af3160980014485af8bedbcc0156000a8f3d38d0159bfd20167003ac556c4cbcc015a000a8f40162ab6264a628c00e00ca0a810000546a5ad227a06b634c000a9a6ff480d60f78d48e015c010b1554865f3141b5c5000c880c337dc1066a00190c3a9a47c502403f4730625a4c9205beb1403282 else 0x28115f68b5159b5366534a407b06a0c40b8c00175026bf57da2d4566d4d894b06a0c40b8c0016d026bf57da2d4566d4d994d2901e41881718c00005e5149b129445c6007f06a040053d179b729e31c3803b020028a1c57da2d4566d4d994d296314608700700a005d439afd5f68b5159b536252c628c10e00e01400bbaff45e6d4a78c50e00e01400a5a2b36652c618700c00f40800a5afb4566cca58c00c00f40800a7a2f36e53c6387606c0000d05149b12923043806007a04005202005d0201a014a57ca293625246006007a040052020aff36653c63a2d0e01a80220500b00a202268acdb0302be3001400a20335fe8bcd88702be3004c0280156066bed159b206653c60028014c066bed159b10e653c6009805002a6bed159b022c0c0af8c30200290180af8c013605000009c0800800ad7fa2b29c0dc639b50e604be6d43b03718e8a0b8d438afb45a8acda9b329a52c628c10e60d418018017b5fe8bcdb94f18e0c00c00a3aff45e6cca78c7060060051d))))
def f3108L34 : PackingT := (428,4,7,16,f3108L34F)
def f3108H0_34F (i : Nat) : Nat := 0x4e80274013a301778361419b2b344096f52348106a0a2c09080342825740b64083f83200274c113a08960184412d40a4a085004eb8184013a009d50354027480fa2088184e6008a8044d07812c69d08e88db40667a263c071087fb068f02dc027540bb1055004e9c1cc810da070f03a002758075009d001e40274013a009d004eb912ee0583069004e80275e08c2062804e80274013a009d03ae00206013a009d004e8591640a8a28b804e80274013a8054a82c951034ebd9076983ac0274013a009d702b40275a136f06a68182c2651313646e380ec0274013a9018284ba2a22002c9050982b00275e12f009d004e880f0013a6038804ebc0a760ee8456804e80274ab10d0217039c0275a896978a804e8027480517039883e151abe0e23098b808c0274013a009d004e9414ea049809aa81b5017e013ae06bf84a26d122074a063c14d915230130b012804e841d4c124501e283019162609fa98b004e80170609d7455a00e7007d00310078801bec114013a043ec027801c9f118009d004eb40aa013a0444004e8027580a6009d721a0027500be009d0031b402a013a6061e22976e28013a006ce0283c1ea60fcd06d88411c16300c9a455004e80274c8a9009d004e9c1e4a886009d004e80274013a009d004e80275c120174850465c253090c009d784940274013a009d004e900bee87e6457804ead1bbe8a3b464004e80274013a343e5a28a81e8605d209bca2a04086e076009d600f41149c072009d004e80274013a506e8a19c0275c123009d70338910e603a009d004eb419f35340424619e84255c893c0528045181f6013ad031804e80274013a704ae229ec183487bb07f42299024440cb0084f80bc0275a510b042004e88138013a805c804e80274013a224a421980274013a5476a81592e6f40df175e301dd41a6013a0490804eac132013a009d00310027480981096182bc0274013ae06b184040274013ae04d700fc0274013a009d503cf8160013ab0650038191ae211b304bb849c0274013a405d004e80275a10bf051a84d002744133009d004e8027560b4009d004e802748880045f804ebc156013a544d804e9c080a0efa041784e2805ae11dc07c923b8027460bd8088a8215c1ec68ac009d40104c24c020001404000080400000281c0e0004810000a030080802008000002008000407008000002020100401010480202008001205000080002000002200008000405060041a02010200a0401004000c0300c0001020005802030000004000180001
def f3108H0_34 (h : Nat) : Option (Nat × Nat) := lookupWord 85 386 9 17 9 4 f3108H0_34F h
def f3108H1_34F (i : Nat) : Nat := 0x4017f8357004ea2c684cb8302834934c804d0001004d201e744a9012521aaa34d038d839804d682c804d703fa845281ed14a004d204c1038004d004d004d3002f80d901ce84b7225004d004d503c7bcb7028d000600c222e7a246832aa1ee03ae849522fa82d004d004d1016a84aca30ea12aa2650113033f819fcc9604a082f1812b34b2003100c9029c035ea339806e809680ee216a00f4026c0204845e249804d70332041801b000a083e004d102a2022201018177018002b804d004d48071809d80888273836d821e14972194a2df23320ca50247006004d5837404298145015f001a020f00ba8cc7048101be80ab80e004d7211004d6217181d88465811b82ac003e007d818b8296a0bba10c9cb801338058031d02e322eb3a13213004d180b283be34ac83b12120a167049903d12304814e844921fd0217830921a68424a1e02183948b0397a14c82fa834182b004d2043180f98401004782388236207e027a847223720081031724b4a4930150a1f004d004d4000804d6219804d501aaa34004d003a6a05020d804d3810b022ba18e037d046e211d832381a3215222f1982583d9b03a03cc844004d004d59ca004d5a15c043ea0c004d383f1828601c32106848824be248b217f825583e804d004d702c622a804d004d2a1410259a0cda327005602eb01d1826381fe02dd84bb840d80d681f78197047c841400248139824b836101600810020a0b00212021500a0300814040202828000012898101809008020801010a6030600406020008c06060181c0413010340007010180a0f008001e080c808440209814000002000020001070003b020000000
def f3108H1_34 (h : Nat) : Option (Nat × Nat) := lookupWord 75 259 9 16 8 4 f3108H1_34F h
def f3108L36F (i : Nat) : Nat := 0x59d22f4c6b066a582a3b0080141f0cda411d8d1735b0298024311e48e0b31a2a41416b004905a46347b1be056007d22f42a46bc688e19982b7e82c017a4370d4e34335bf4760d0330580400c05748bd1a9aa46620adfc6b06c0167a1be32690db35354e358320d03305475058040103a8df193486dab62a71ac190681982a3a82c01e6126eefdbedb69054e358351d4142b8034f637c64d21b6ad9776a6a9c68820568ec01d073716fe90db35354e340ae00a0b60e77edf6dab62a71a05748c016329bfa435354e340ad718350580400c169dfb7eb80b71a05748c1a82c016afe539b61d8c00da28190025a960a48f1478ed86d1b21ae606519206801c31152410cb6fe91e2f6d8d7300a51d83600e0f8df2a4f7d22b8c6b980528ec1b0060626f8f22d10433691e2f6c165538d7300a51d8360111d8a923b48f14f7edb1ae60df02b06a0b0071be3c95233691e2f6d8d7300a815835058038124a6a944902a0948f16f4ed91ae60636390640200220894d53475e832dbea43708d20cc1200e37c654a6a977fb6a08645211a0568e419007074afa7494d52bba90db2340ad1c83200d0c93257edfed8a96a6825211a0568e4190070096fd5232f6c412900aa354720cc1200d184dfaa42da3948ae11a05506a090060256fd535c05a472900aa34c720d41200d17f29c1822d1736c620ec0a0056be2fe5387011a2e6d8c40d81400b17f29c3804d1736c630680a00506f7a052070052478bdb435cc0cb03400d0e875bd248f161ae6039ae20680162f85232f6c014910d02a0951d03400c17c290b40e9203a8681581804a0a006480a34714487cc21a012f96778b959b9ed3e66ab1897cab72589aa093e2974462a0d0f466fe3369770aaa4c421e8f006722d012e87d02da0fa03e8003ffe5520c20fffaa963083ffeaa54c20fffaa981083ffd53a2020fff14688083ffd31a2020fff61a33083ffd858cc20fff59633083ffd818cc20fff58633083ffd518cc20fff60e11083ffd5384420dffaa9200837feaa66020bffaa983082ffeaa58c20bffaa953082ffeaa60420bffaa9310837fd93a2020dff646880837fd988cc20dff65a330837fd958cc20dff646330837fd9884420dff64e110827feaa4c0209ffaa9200827feaa440209ffaa9980827feaa658209ffaa9930827feaa64420
def f3108L36 : PackingT := (37,3,7,13,f3108L36F)
def f3108H0_36F (i : Nat) : Nat := 0x68190d12e8046601c920ad80066041f236101c640c7207400bb005da00e5c09ff055082bc8145c0029056805d802ec0176502928344406d8005d63c60075c0a0e025f057080d540cc202ae05a280b8005e40cb0439a008040efe016202ec209d502e8014102c005db11760176f45ba204d00a98068605e58304c12860b3d022e031b5088c09cd002120a741860176104ee825e506500751063805d84086017600bb005db51a5206f00bb005d802ec017600641007140a6e019d0650019402ed406a605c6033ec043e03b00bb680d2804700175030805d802ede02b00bb005da80e6a875a053e825402ed807830492825b400c0176005cf808802ed009b7037005d800710899c460fa2e1d07820ba301ee81b2c03e0176202fc029002ecc0c900bb1029b80ce017600bb7a02b40e0e0d200bb005d802ed40bb00bb00172413480284034e82784026017600bb501ac02ec80480014801378075e0263023d0093417b60c2400f5011002ed00570058c82fec0b4a04f0005582cb11242279b04cc814402eda04be055c01e5c02a01761004805db0188203ce052805d940aa01761050005d8c07e017600bb005d802eca8741460005d800ac403700bb482a6c037e0184066f013340c1c02d0050b02d4c19de865613be010981a1803ec42fd82fa406200a320566a021d0e1201a2019a812402ec017600bb005d802ec0176303b005d880940176f000805dac010805900bb005dbc04e60c500bb1826002ec017600bb302de4016017600bb005d802ec01768027581b7c19960a800bb58303c080883fc049805d802ecc81600bb005d802ed6896202dc11b802ec800700bb005d802ec205e00bb700c200c4800000bb282d802ec20b06419c00c802ec402c010000808010000638000180000038000400168000800010040007010000805010000c22000002c010701c0400008000a010100008040002802080000008550100004060180804090202c060300024100a
def f3108H0_36 (h : Nat) : Option (Nat × Nat) := lookupWord 72 299 9 17 9 4 f3108H0_36F h
def f3108L37F (i : Nat) : Nat := (if i<2 then (if i<1 then 0x9c2f259e11bbce76f2ec91d58ba34736ee4e9c63b8546fd6ddb9b73b6746beed611a83b48a681ace19989b29663cec559876b07a5fd2bdb1772ae685bc2b4c9641ac0656feabb9547aa0852b2a34941ba7c44e7a9a89308a562498e90611c8a30044f287f10b5a0ee40ce7e68f8e9e8c3b927530e4e9bda36a66b30cfa996431ba6130bd3970c2cf657d0ab694c8280a4da895d922022e243808318fdc1e6e3ac07148dca1ad634306518c3a17662c885618a5a13f6264848f88c010ae1f903b886ea0cda17c02c8851e090610401c4830c04f608200bb80fa010e0003ffda660c20fff69583083ffd8560c20fff68583083ffda858c20fff69563083ffca558c20fff61563083ffd8358c20fff68563083ffda854c20fff2a153083ffda654c20fff61953083ffd8354c20fff58d53083ffda154c20fff28553083ffda660420fff68d81083ffca360420fff60d81083ffd6360420fff54d81083ffc5360420fff54c81083ffd8358420fff54d61083ffc5358420fff6a131083ffda64c420fff61931083ffda54c420fff61531083ffc854c420fff59531083ffd834c420fff58d31083ffd534c420fff60531083ffd514c420fff614310837fda14c020dff605300837fda848020dff68d200837fd5348020dff685200837fd8148020dff4c5200837fda344020dff60d100837fda244020dff609100837fd5244020dff4c9100837fda666020dff68d980837fca366020dff685980837fca166020dff6a1930837fda664c20dff619930837fda564c20dff685930837fda960c20dff661830837fd9660c20dff655830837fd9360c20bff694830837fd9520c20bff68483082ffda858c20dff66163083efd8658c20dff655630837fd9358c20ff760d630837fda954c20bff6a1530837fd9854c20bff699530837fd9654c20dff64d53083fdd8354c20dff65853082ffda114c20dff6a1910837fd8664420dff68d910837fd8364420dff20d910837fd6364420dff54d910837fc5364420dff6a5810837fd9860420fbf29981083bfd8660420dff64d810837fd9160420bff68c810837fd9320420bff6a1610837fd9858420dff64d61083ff58158420dff6a531082ffda84c420dff66131082ffda64c420dff65931082ffda54c420dff655310837fd934c420ff758d310837fd914c420ffd60531082ffda50c420dff654310827fda848020dfe4c1200827fda3440209ff689100837f920440209ff6a5860827fda960c20cff661830827fda920c20b7f69c83082efda620c20bdf69483082fbda420c20bfb68883082ff5a120c20bfe680830827fda958c20dbf659630827fda954c20df764d530827fda914c209ff6a5810833fd98604209ff6a481082fbda4204209ff6a5610836fd96584209ff6a5310837dd934c420dfd645310827fda90c420 else 0xd03505004e4886815197c5ed9a9e618e81a8280189b252872907b8de8d5be01f8bdb0d9cc0c883504804529aa50ea386f18402520f4468dff17b61b39819106a090099c07a6918d170db0156ff8bcc60d41600d0e4f6d231a2e0b90f7c56db98c1a82c01a300241cd6d7a253548caa45708d02a895bfe2f6dcc31c835048055482e11a01003b7fc5ed82de601541882401da46345c02a6ff8bdb05bcc31d831058036b808d4846815b7fc5ed82de618e41a82401c1b9527b11c7a6918d170053bfe2d6dcc60d4160100dd2943948468f41e2b877fc5adb9841a82401e1ba52a4234895717a78b5b730c720d41200e1d4f62e0f4d231a029dff16b6e6306c01a1c8f2a42340a8c7e2f6dcc51c835048034b61ddf42a748c6814029dff17b6e628ec1a82c0203c872fa253548cca45708d0ca0abbfe2f6dcc51c83504804cdf0dca9d231a2e00a19bc56db98a3b06a0b00787494d52a40f23ba341c82afa78adb7314720d41201137c79d202cc680a19bc5ed9a9e628ec1a82c01e192bf6f872a45708d05a0af8bdb353cc51c835048044391e5480091a05463f17b6e608e41a82401c1c82ba41718d0cde2b6dcc60d41600c011482e11a057c5ed82de628e41882401a6f91c3bbe80ae9033634053bfe2f6dcc51d836010d20b8c682d197c5ed9a9e608ec1882c01b5c2908d05a32f8bdb353cc51c8350480355fd1736ca718c3a06c0a004845afe8b9b6538c21d036049d7f45cdb29c610ec1a028012066bfa2e6d94e318720d01400a03004d7f45cdb29c630e41a025052071e8a42341c86f6ff8bcc20d5c200d0def40a4025211a196dff17b6e628e4190072908d0cbe2f6dcc51c832009520f44681237fc5edb9805500511c7a6346ff6c2cf300ae00923b48c6b063d0dff179805700511da41e98d60c6ff8bdb7300ae00bd20f4c18a037fc5ed815c012a41e98d0246ff8bdb7300ae00ad20f4c681537fc5edb9823b06c016116907a234082006ff8bdb7300aac291d548468390def4f1798a3906ae10068eaa42341c86e7a78bcc51c8317080305f0dc025211af17b6aa798a39064018a42340978bdb553cc20c8024375211a04865f17b62a79805500586e1b5e81481ca45708d5bfe2f6dcc20d41200f0e6b6522b846bc5edb9841a824016a41708d0086ff8bdb05bcc02a831048037482e023070dff17b60b415c1882c0181481c3aa908d1701bde9e2d6dcc20d41200e5211a1d4b80dcf4f179841a8240162f86e14a915c2340af8bdb7314720d41200e0e412522b846815f17b6e6106a09006074022908d02be2f6dcc51c83200b520b846804197c5ed82de608e41882401b28ba4f1c98e9273236a43dc8088eef1c12352c65a8c0b16c22adc4fc893b1122203c3bc86bb0c4a15ec25e835f04ca069c074803eff51fb5bf0c7d6ef989edebd727) else (if i<3 then 0x51058d60d8043487d0230b71a19b0039840abbf6f873a405854828471718d60d803b481dc151971a053003b6da4072d482a335058d0298011cbd207905466c6a82053004690d4e340a970056004123480b71a054b82080ac010160ca3269016d718d51d83505802c6600422d7f45cdb29c620ec19028018112ed112bfa2e6d94e310760c81400c0b8160055fd1736ca718c3a06c0a00605c00ebfa2e6d94e308740d81400b0c408d7f45cd929c610e81b028016066bfa2e6d94e318740c81400a1d80d0315fd1736ca718c3a0640a0060220b01a066bfa2e6d94e308740c81400d00404d7f45cdb29c610ec1a028016022c5022bfa2e6d94e308760d01400c03004d7f45cdb29c630e41a02801630809022bfa2e6d94e318720d01400c011588135fd17364a718c390680a00600889409afe8b9b6538c21c834050031b69207a868791e3c51b398192066e20068fb2443432f8bdb0d9cc31d03400b63a481e21a37c61f17b61b79805600636cd48fac70de30c90dc435e2f6c367303240cc14011921b81961a186dff17b60b7980560660a0074910d0ca093bfe2f6dcc02b0029df6a6488681218fc56db9805600586f14c910d0f2fa424eff8bcc51d033710039df1e6488681218fc5ed9a9e601580183cc910d02a090c7e2f6dcc51d033050034751f54846865f17b61b398a39064018072907a234329bfe2f6c367314720c80343a2d929aa5481e51a1dc75196dff1798a39066e10088643ade881504a4234990cb6ff8bdb353cc51c832011048752394846865b7fc5edb9805500611da41e98d60c161bfe2f6cd4f300ae00d1668e522f41ad1a4cadff17b66a7980550076907a6346ff8bdb7300ae0090dca93d348c681477fc5e628ec1ab8c01a3087c1ba53549e8a456c8d0cceff8bcc51c835708044373d348c68662dddff1798a3b062e300686e1f064a456c8d2657a78ad4f314720d5c200fb7ea95211a04863f16b6e601540163a8ca7a6915b6340a3bfe2f318357180355f1e502169480a91a18fc5edaa9e628e419007be841690166340a3bfe2f6d54f314760d8038610c502a086f5206d4686677fc5edaa9e628e4190089be1b9efa436c166343378b54f314760cdc600f0c43a0ddb65dd481e91a1e5f4f16a9e628e419b840236f8f2a4234090c7e2f6d54f304702a8034a97d065d206dc681477fc5edaa9e6306c01c1bd1cbba908d26e32f8adb553cc02a803748c6815197c5ed8a9e608ec1982c0181d4910d006023bfe2f6c16f300ac0d41400e0de48869f40e9dff15b6e6206a0a006075244340a809e2f6c16f30c740d41400d0123a1d5f46a629922b8868151960477fc5edb9863a06a0a00a3e9244340abbfe2f6dcc31d035050030376a648868b90e9f4f15b6e618e81a82801c18808efcbf1d4915c05b0d02b0278bdb353cc31 else 0x75d21b66a465c69b8053004e903ce34c10ca0a600719348c68f41b582197004690db0eed4e34328298020f419b486a71a2e6b60530049e9a4352336345cd6c0a60093ab4823837c6814a3b064b5a9c016756903a85854e34471e83360cc15055b600eadb481d4656a6a9c6815053002397a406ed4e345c0ccc10298027481e42cc69820530038b2fa0478d152330b58023481982cc69b86d814c0107a6903d0db8d5043ce008d20791971a60a82053002393a436c548cd8d11c0a8298027481e42ac698219814c01037b718d3042d60060e7486db1a3d80ac00e32690db3538d31c1e815802748c6b0637d8e3db0038c9a45538d0147a0cb8023482d9a9c698ec18663df0048b46f8de7bb6d5b4ee54e344769183014410da33601102865193483deb69df1a055a963b0060b3a4570168478d0cd416009d20756a71a053063d2b8c012ef8598d029a460d5c6008d21a9c6b0663ab8c00e33690db07ad482b8d02805600a19b480e5a90571a0500ac0120a873a45525c6343ce00819b480f415c681402b0041d40a9bfa436d5b0ee16152470cc0))
def f3108L37 : PackingT := (153,3,7,15,f3108L37F)
def f3108H0_37F (i : Nat) : Nat := (if i<1 then 0xb51a1e1660078024cb824408eaf48ce85c600ba611344746a351402f4112307ee84524114809460a06836f01cd4161a0aba81a5d1d648ab802b10166c27de098c079180ae00eac04de4573a419406040fba4853822d41f50d5f201da248cc23a61469019005d981d4e071408fa03cf8218c152c07f805d240c9e55e348ba80d891358944e0b4580f001afe0e810aa785b5916dc02ee027a85ce41bb40e0609868050c286ef6fdab3f034e8023656b249a384aa8d9a412d5051125668279c142423cf012c02ed28e03020584d642c568f0e075eb5d3d038c0ecd08ae2086d153014ea4792a3b7010fa0f8a0142209bc2a00076d06a10123411060c9a022681b05291a12ea013800e500fdc90080ad704808074411650b560201d1cac0f49093c046002ec01764471115d1aec7c01d105de04fe0243a061746c404cf026c00bdd49baa36581e2e04904724a515c196615c70962a3a4d160801b3023704ea8297c11e74590017f523568d7b06cc03f2421b216990544818801d3010e14118850518e0608f2bafd03e69df520c6a018c80b210b6e11ac0281019580dc28b300bb005d88174890cc0a50858241250f70c014f8535c0a3e8a2544e9057cc1ac60ef30611dd9e421528df60b218109c01a80f730463814b514a606f209350306029100a480064033ec2b6016eba39e85cbc2d8808920b8684259282c8575080b044440f60176b6365029c02ec001ed095805d966cac0cc701f984e002edc92200bb405960277693f7088781e629a400e400bb5958802ed6151423c1958ed031757400bb4840002ed2efe8009805d84021a1580073e82e101be4117b094da35beed22568e0aae84a3c247a81a102ad81d181326e6f905bd84c8026920c4106410415829fe0c350847855a81c308e3b40cf01f3915941750022f206e01cb085a2049b821641c5c153e029ea39a00e4c877709288211d25620dad0a2300be903ca0be6092484c5402c6955b458e820dc1a3a0eec44dd02f24156006d00bb72356103aa10fd02a1a2a3001f007f24526357b522ca89f607ad2439114f003de0472035511efe8ff4043484e711f040bf108dc84709049413d6451f0517119c28b5a04b8003902dfa0824450e851cdda2e1068081d22b68123289c202e023d0916841043052c0242921f416b449c5037a8292e058e48fe3dd0c26e610740b3e3bf240240127800004a04800560503800140d1e090001f0002c08041d040180905005483c0110c009b0e0149e031605832000100006040580404000203c3e0607808121f1080450000f86c0600040840232020441629148503e3a039ac002c02030460000000021f118094824001640a59058c40e090101422010701c085201800000107008080e118143e195e0c896151c00c1406020b00606000185608038741200048003400 else 0x7470b838d915e60f69097a058c6ad788a0d0aee01e940bde956b46d38371411b80ed008110531c09d68aa1739500dec0faa01c50af120804103c1593497b25ba8181a91ca01370254c0d04119304b3231780e1c89ec7b58a29a41fca10b706c3a3b)
def f3108H0_37 (h : Nat) : Option (Nat × Nat) := lookupWord 145 451 9 17 9 4 f3108H0_37F h
def f3108H1_37F (i : Nat) : Nat := (if i<1 then 0x1fae0ad40374026b50fa8119411e003dc00e8a0b0d0c8e1dfc1072e95d14833053400fa2917842e781d5c07041542009203c09d68c996504a9862a414f41a3109f40088413e88bb242f484d2801c01877065ca55c42e96093d0bbc063851cc008d30d47031f1129217d4081aa2fdd22700ee7026c24255127e05030bae867c528c089ba40f7a08183212094106b4038a4194f0446048c0349503e2052b759d864cc258889134be30658415840ae546d6a30c92856899003dc019e911a63a7f435e15ee00a3c11750729013cd1c9e0fc9094151048c70400dd08a4831041c7c39990a8c8322c30748a4c01c806b340a801acd489006b141fee10a7090f03e302aa8066f4541a1618247808900d66a44492218105704058dfe4241c082b09fc8489c2dfa19560a2503c4c094811cf07a88408508c8032d012f01570130a171f0b93852fc0e6e09e80a4c00c7c185219700d61960003596037400f188fc0358690c00d600004c348e587e05cba1ba9f1e01ac80bb006b0025201ac803b701f2812540d7b085f863f80c108a200d67a143416401ac00d65a5146f0460684473b38579315a905f44af039990c2a0dc80751240e0b3a01ac00d658017911f80d34001500009b026057b00caa02e404c01ac00d66001a0317085b008c6042042b8214f95bd1806e011d023d76c07800e82d1e1a190443029781816165c09c821bc51ba6975c06af8427cf28a86df01d4a57880ca2048145ab8266caf4e11384692051e01a8008fe0d1006b391a1801fc0664036712d801ac00d660412c103212fe466a00bf419bc0271486b223810098f76a062a85e003598862c025f83cf816a412a70b1c02bfc2f3a01456c1b0347825cc03440a5585b7402601ac00d679685410760def02e6242342f5205e345f7841e0f0a80b700d6381ca433da8ccb0a1a063310f721467004804188162819410a16bbaac177019c10d490218d23be8f3c600b01930afe4807901f402eb5208f586905c58501422001ac90ad480c24023688840a2e2554d12480bd2010a8083af00212d05c040880a00052010270481703c350001601402508050183a0f400000b6008000100001c120141201c0a000130380300440018083740002018074060084206405118dd0b0132a4520300f00883000010ac061fc010183f0002701c120000700c0b21c03028021a84b48c0005811260062c4010080009808030300381201c3402001090030144901401034b4058010000003c00761880341c000d300415008000006913c260000c044200b804000000002213c0d0280b1647b08c0e058084e40e178000600001000084f95781a028650000061c00000110080000011011820344000124004000000c0204a22c1c110240100202c000040007059004760103a03073000030c4380412218c0700c0f06019 else 0x2c23d009d44a5280b6421960977045da45980e2843ce003d162002f7ec4622c7786370053201cd019c811dc1f2a0aad01daa34e2307e13b603fc022a8182890b042d001dd66edc13a2ac38031950d2e10de3cee818d821d00a1c0c000293c17d41364026086499afe4f9bf0cd5269b024f016c9442e830fcafa00e16048482a200e008901054d23d99eee00a6143e28212db39e02470a94816301390189e01ab2150c30200c920abd81e30aeda8d9246e00530c1e8b18637d209e0f80db20fb52d41847ed14321303023383b082c2a185a02020112022c013190744826d81daa01d34cf1828d409d2c4460b9c02d980ad0188648d48675db3d805ff4cd78282c33661583452830eb024b203da42933e57806c08ed10c11805a41b1a0faf09c600ae00fc095ca4456844ac873c16760ccf039c8051b77fa4ca5005440d7e97ed433082fdd1748045a4b6e02d1827b001780b5504f34341e583d48e605bb82d2e5772087ea2e442a74053708dc83a580df606c60cc705fceb2aa07af0b5e821d1082e85520b37a260eaef48f90762c20edc047a16090af68446928e60dd007f6a655c03480ebc0b86818741de8840600270342d116615b903c9562781578943d480704d5911908def0a84a52d51a228afe0b268564807940f20024f802dd0c6e59570d35828bc2c4611a3bc1fde251013c00840a73a4641f3a978665d3880bbc1b48115146a7061141ec80ce94949a6638256208cc42be849942bee15d908eba14cd25c81245007f8505501ca00a5425aa33911c600b3741893b130c7ee0185080e0166012c090a90d5c200c8086ea3c146ac1650401841334020a0619c0b4a0fd50679836ec0c40085403540e0fd1b0003f502de010b0b0520df80ab4a1949140002a509be25d8534421a720be3852141c14100140788176005820101463b2128c1c9e132e0d2aa3d300d3617e40d5302f21)
def f3108H1_37 (h : Nat) : Option (Nat × Nat) := lookupWord 218 678 10 17 9 4 f3108H1_37F h
def f3108L39F (i : Nat) : Nat := 0xa94720a91c57a6da359832c1a00c6faa4cbb64152234154741a00b6faa45a8ea42e234158320a00b681a001ffe88083ffc66107ff84420
def f3108L39 : PackingT := (3,2,7,9,f3108L39F)
def f3108H0_39F (i : Nat) : Nat := 0x25b03941d6029c1c0094025b01e8201035009c032816406c0253438d07445c0181068025007d80b507a408f05c025606751e5804300040
def f3108H0_39 (h : Nat) : Option (Nat × Nat) := lookupWord 8 29 5 14 6 4 f3108H0_39F h
def f3108L40F (i : Nat) : Nat := 0xa4469e8dfe2e620cb88025e8a94152234656ff176d984741a00d47521e91a8337f8bb6cc05600b1baa690b68d3d38b98474197100637d05488d7176ca9cc23a0d005a3a911a831978bb654e602b005ad8eef454a3a90b88d37f8bb6cc41905007d21711a6ff176c2dcc0560c828032911a5c3d38ab6cc4190500537d53485c4682bc5db6611d0641401b485c468cbc5db0b7308e8320a00c1157e8b3694c601d068100155fa2cda53188701a04004812bf459b4a6310e8300800a7a0a41c0224069bfc5db6600c0062d8523a071dc901a1bbd38b98032e000e2f8a404480d04b8bb6cc2380c00617c742907121701a027176d980320800eecdbb342613b5750e5bc467cedb57e29d48e7a0bb8f4106003ffb0c107ff60c20ffe41841ffd63083ffaa6107ff14c20ffec0841ffc81083ffac2107ff4c420ffe188417fd30082ffa40105ff44020bfecc0417fd96082ffb26105ff64420
def f3108L40 : PackingT := (18,2,7,11,f3108L40F)
def f3108H0_40F (i : Nat) : Nat := 0x959180094025009780c009540400965090094025200f00f0094025009540900950200094025009402500944110095408301c025242e810c46b51c00940250094025e02dc1480680250097824b000025b08c02500940250097c05009402570040250094025009591b0094025009551d005c02500974120094025009441d00940130094025d0390150094c1eb058025009580d00940250096d190094025f08402500940250095c1900964060094025b00882200940250094025343050a0094001000008000042000000000
def f3108H0_40 (h : Nat) : Option (Nat × Nat) := lookupWord 14 109 7 14 6 4 f3108H0_40F h
def f3108H1_40F (i : Nat) : Nat := 0x8095205a0099b0651094a475407790636003f041a02ba03b9008821c0074307b144e744ba086a42a0099f02ac06d00990099009944890099371ce0190099104b0099105e0099c00ab45f009900995037009900999738e4301069100f3098e062400e103550820099b046576ec477a0883039306b144ce44200990099e0400099146b00995620200d14030099a04ef11cc0480099305300990099242d608e009970700099e0115b63b4831a63574000995043116ee025d038003400998066303e200b00995485911d30137083009900990099804f009900990099009900997012a085c067009930040099009900997418009900990099b45420710099a05f0099009900997054b2660099009900995059c61f208b0099009900990099009900990099009900999076d08f8467b04d840b303a2027671d00990099009900990099405b009900996491f006e21a0099e471c77c0099941a00990099708c0099c0610099b0000099406cf0560099009900990099504a943c54335007f07ff031d05520896018f8201455e4270099401010753068202cc02e503c0099208d0099203000990099009900996028201df21ba07a305800998029009900993026e0210099f04c70780022848a602db45370528097b362307d408a901b00990099941f0099206fc0871042a26300990099f04774310099b61c0099009957410099009924760099f072c406b092981c2024500c4429d07cf002a421703fd051c4220099f05dd66e0099401600990099f020009970930099848200990099009900999050c41d009900998017009900990099c41700990015540df9620099b472e42500993014005c301af03695680099f079009900990099009900997032009900990099009924430099002fb005c001303d8091009900990099e16d40902264006ac01f0099361d00990099e43b009910490099306000990045009960819033b009b4790099845ec06404840099009950570099d08400990450245914280099f0730099c01e84012268601cc02300990099507ea09660440099740e947e0099e43d0080643a846f0099e44d0099706e009900990261009900000020605000000300004020c0000000000180c0800098140c050280806000000402000000004060000000040202412000082806030000002000080002000001800050202004000001c00080001414010280000070100c1401
def f3108H1_40 (h : Nat) : Option (Nat × Nat) := lookupWord 80 393 9 16 8 4 f3108H1_40F h
def f3108L43F (i : Nat) : Nat := 0x17d14d8a46038180801290358b6d300c0073d007fc20ffc20
def f3108L43 : PackingT := (2,1,7,8,f3108L43F)
def f3108H0_43F (i : Nat) : Nat := 0xa0803644039000300c03b040300
def f3108H0_43 (h : Nat) : Option (Nat × Nat) := lookupWord 2 10 4 10 2 4 f3108H0_43F h
def f3108H1_43F (i : Nat) : Nat := 0x9404690e08fd72b914024403243183980a0020090048024201c23004b812012406f220c4ad240090048024012009004a8ca012305c8180240120090048025a90672004914a0120090048410ea4900781c51c012a320048024c0cd0832040240120093012c480120090048c1e0120090048024e0a001010000000000000100
def f3108H1_43 (h : Nat) : Option (Nat × Nat) := lookupWord 12 72 7 13 5 4 f3108H1_43F h
def f3108Levels : Nat → PackingT
  | 24 => f3108L24
  | 27 => f3108L27
  | 28 => f3108L28
  | 30 => f3108L30
  | 31 => f3108L31
  | 33 => f3108L33
  | 34 => f3108L34
  | 36 => f3108L36
  | 37 => f3108L37
  | 39 => f3108L39
  | 40 => f3108L40
  | 43 => f3108L43
  | _ => emptyPackingT
def f3108Idx0 : Nat → Nat → Option (Nat × Nat)
  | 27 => f3108H0_27
  | 30 => f3108H0_30
  | 31 => f3108H0_31
  | 33 => f3108H0_33
  | 34 => f3108H0_34
  | 36 => f3108H0_36
  | 37 => f3108H0_37
  | 39 => f3108H0_39
  | 40 => f3108H0_40
  | 43 => f3108H0_43
  | _ => fun _ => none
def f3108Idx1 : Nat → Nat → Option (Nat × Nat)
  | 31 => f3108H1_31
  | 34 => f3108H1_34
  | 37 => f3108H1_37
  | 40 => f3108H1_40
  | 43 => f3108H1_43
  | _ => fun _ => none
def f3108Idx2 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
abbrev bkT := blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2
abbrev bmT (k tm s a b : Nat) := @blockT_merge f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 k tm s a b
set_option maxHeartbeats 0 in
theorem c24_0 : bkT 8 0 0 1=true:=chunkBlockT (ar:=9) (by decide +kernel)
theorem a24 : bkT 8 0 0 1 = true := c24_0
set_option maxHeartbeats 0 in
theorem c27_0 : bkT 9 0 0 1=true:=chunkBlockT (ar:=9) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c27_1 : bkT 9 0 1 28=true:=cellsBlockT (ar:=10) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
theorem a27 : bkT 9 0 0 29 = true := (bmT 9 0 0 1 28 c27_0 c27_1)
set_option maxHeartbeats 0 in
theorem c28_0 : bkT 9 1 0 3=true:=chunkBlockT (ar:=9) (by decide +kernel)
theorem a28 : bkT 9 1 0 3 = true := c28_0
set_option maxHeartbeats 0 in
theorem c30_0 : bkT 10 0 0 48=true:=cellsBlockT (ar:=10) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_48 : bkT 10 0 48 16=true:=cellsBlockT (ar:=10) (d:=1) ⟨kT (by decide +kernel),kT (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c30_64 : bkT 10 0 64 48=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_112 : bkT 10 0 112 48=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_160 : bkT 10 0 160 48=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_208 : bkT 10 0 208 48=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_256 : bkT 10 0 256 48=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_304 : bkT 10 0 304 10=true:=chunkBlockT (ar:=11) (by decide +kernel)
theorem a30 : bkT 10 0 0 314 = true := (bmT 10 0 0 160 154 (bmT 10 0 0 64 96 (bmT 10 0 0 48 16 c30_0 c30_48) (bmT 10 0 64 48 48 c30_64 c30_112)) (bmT 10 0 160 96 58 (bmT 10 0 160 48 48 c30_160 c30_208) (bmT 10 0 256 48 10 c30_256 c30_304)))
set_option maxHeartbeats 0 in
theorem c31_0 : bkT 10 1 0 6=true:=chunkBlockT (ar:=9) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c31_6 : bkT 10 1 6 48=true:=cellsBlockT (ar:=10) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c31_54 : bkT 10 1 54 48=true:=cellsBlockT (ar:=10) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c31_102 : bkT 10 1 102 48=true:=cellsBlockT (ar:=10) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c31_150 : bkT 10 1 150 4=true:=chunkBlockT (ar:=10) (by decide +kernel)
theorem a31 : bkT 10 1 0 154 = true := (bmT 10 1 0 54 100 (bmT 10 1 0 6 48 c31_0 c31_6) (bmT 10 1 54 48 52 c31_54 (bmT 10 1 102 48 4 c31_102 c31_150)))
set_option maxHeartbeats 0 in
theorem c33_0 : bkT 11 0 0 1=true:=chunkBlockT (ar:=9) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c33_1 : bkT 11 0 1 18=true:=cellsBlockT (ar:=10) (d:=1) ⟨kT (by decide +kernel),kT (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c33_19 : bkT 11 0 19 48=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c33_67 : bkT 11 0 67 48=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c33_115 : bkT 11 0 115 31=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c33_146 : bkT 11 0 146 48=true:=cellsBlockT (ar:=12) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c33_194 : bkT 11 0 194 48=true:=cellsBlockT (ar:=12) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c33_242 : bkT 11 0 242 48=true:=cellsBlockT (ar:=12) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c33_290 : bkT 11 0 290 48=true:=cellsBlockT (ar:=12) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c33_338 : bkT 11 0 338 36=true:=cellsBlockT (ar:=12) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
theorem a33 : bkT 11 0 0 374 = true := (bmT 11 0 0 146 228 (bmT 11 0 0 19 127 (bmT 11 0 0 1 18 c33_0 c33_1) (bmT 11 0 19 48 79 c33_19 (bmT 11 0 67 48 31 c33_67 c33_115))) (bmT 11 0 146 96 132 (bmT 11 0 146 48 48 c33_146 c33_194) (bmT 11 0 242 48 84 c33_242 (bmT 11 0 290 48 36 c33_290 c33_338))))
set_option maxHeartbeats 0 in
theorem c34_0 : bkT 11 1 0 48=true:=cellsBlockT (ar:=10) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_48 : bkT 11 1 48 20=true:=cellsBlockT (ar:=10) (d:=1) ⟨kT (by decide +kernel),kT (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c34_68 : bkT 11 1 68 48=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_116 : bkT 11 1 116 48=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_164 : bkT 11 1 164 48=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_212 : bkT 11 1 212 48=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_260 : bkT 11 1 260 48=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_308 : bkT 11 1 308 48=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_356 : bkT 11 1 356 48=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_404 : bkT 11 1 404 24=true:=cellsBlockT (ar:=11) (d:=1) ⟨kT (by decide +kernel),kT (by decide +kernel)⟩
theorem a34 : bkT 11 1 0 428 = true := (bmT 11 1 0 212 216 (bmT 11 1 0 68 144 (bmT 11 1 0 48 20 c34_0 c34_48) (bmT 11 1 68 48 96 c34_68 (bmT 11 1 116 48 48 c34_116 c34_164))) (bmT 11 1 212 96 120 (bmT 11 1 212 48 48 c34_212 c34_260) (bmT 11 1 308 48 72 c34_308 (bmT 11 1 356 48 24 c34_356 c34_404))))
set_option maxHeartbeats 0 in
theorem c36_0 : bkT 12 0 0 7=true:=chunkBlockT (ar:=10) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c36_7 : bkT 12 0 7 15=true:=cellsBlockT (ar:=11) (d:=1) ⟨kT (by decide +kernel),kT (by decide +kernel)⟩
set_option maxHeartbeats 0 in
theorem c36_22 : bkT 12 0 22 15=true:=cellsBlockT (ar:=12) (d:=1) ⟨kT (by decide +kernel),kT (by decide +kernel)⟩
theorem a36 : bkT 12 0 0 37 = true := (bmT 12 0 0 7 30 c36_0 (bmT 12 0 7 15 15 c36_7 c36_22))
set_option maxHeartbeats 0 in
theorem c37_0 : bkT 12 1 0 31=true:=cellsBlockT (ar:=10) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c37_31 : bkT 12 1 31 48=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c37_79 : bkT 12 1 79 32=true:=cellsBlockT (ar:=11) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c37_111 : bkT 12 1 111 42=true:=cellsBlockT (ar:=12) (d:=2) ⟨⟨kT (by decide +kernel),kT (by decide +kernel)⟩,⟨kT (by decide +kernel),kT (by decide +kernel)⟩⟩
theorem a37 : bkT 12 1 0 153 = true := (bmT 12 1 0 79 74 (bmT 12 1 0 31 48 c37_0 c37_31) (bmT 12 1 79 32 42 c37_79 c37_111))
set_option maxHeartbeats 0 in
theorem c39_0 : bkT 13 0 0 3=true:=chunkBlockT (ar:=11) (by decide +kernel)
theorem a39 : bkT 13 0 0 3 = true := c39_0
set_option maxHeartbeats 0 in
theorem c40_0 : bkT 13 1 0 7=true:=chunkBlockT (ar:=10) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c40_7 : bkT 13 1 7 11=true:=chunkBlockT (ar:=11) (by decide +kernel)
theorem a40 : bkT 13 1 0 18 = true := (bmT 13 1 0 7 11 c40_0 c40_7)
set_option maxHeartbeats 0 in
theorem c43_0 : bkT 14 1 0 1=true:=chunkBlockT (ar:=10) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c43_1 : bkT 14 1 1 1=true:=chunkBlockT (ar:=9) (by decide +kernel)
theorem a43 : bkT 14 1 0 2 = true := (bmT 14 1 0 1 1 c43_0 c43_1)
theorem tables3108 : ∀ k ≤ 14, ∀ tmax ≤ 2, blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 k tmax 0 (f3108Levels (3*k+tmax)).1 = true := by
  intro k hk tmax ht
  interval_cases k <;> interval_cases tmax
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 0 0 0 0 = true)
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 0 1 0 0 = true)
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 0 2 0 0 = true)
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 1 0 0 0 = true)
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 1 1 0 0 = true)
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 1 2 0 0 = true)
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 2 0 0 0 = true)
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 2 1 0 0 = true)
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 2 2 0 0 = true)
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 3 0 0 0 = true)
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 3 1 0 0 = true)
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 3 2 0 0 = true)
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 4 0 0 0 = true)
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 4 1 0 0 = true)
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 4 2 0 0 = true)
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 5 0 0 0 = true)
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 5 1 0 0 = true)
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 5 2 0 0 = true)
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 6 0 0 0 = true)
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 6 1 0 0 = true)
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 6 2 0 0 = true)
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 7 0 0 0 = true)
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 7 1 0 0 = true)
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 7 2 0 0 = true)
  · exact a24
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 8 1 0 0 = true)
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 8 2 0 0 = true)
  · exact a27
  · exact a28
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 9 2 0 0 = true)
  · exact a30
  · exact a31
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 10 2 0 0 = true)
  · exact a33
  · exact a34
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 11 2 0 0 = true)
  · exact a36
  · exact a37
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 12 2 0 0 = true)
  · exact a39
  · exact a40
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 13 2 0 0 = true)
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 14 0 0 0 = true)
  · exact a43
  · exact (rfl : blockT f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 14 2 0 0 = true)

def seed3108 : Sig := bin false (inputs.getD 0 zero) (inputs.getD 2 zero)
def roots3108 : List Sig := inputs ++ [seed3108]

theorem seed3108_witness : ∀ i : Fin 9,
    (bit (absentRow i) graph != bit (presentRow i) graph) &&
    (roots3108.all fun w => w == inputs.getD i.val zero ||
      bit (absentRow i) w == bit (presentRow i) w) = true := by decide +kernel

theorem all_roots3108 {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ roots3108) :
    S = inputs.toFinset ∨ S = roots3108.toFinset := by
  have haveIn : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [← input_list, List.mem_ofFn] at hm
    obtain ⟨i, rfl⟩ := hm
    have hh := seed3108_witness i
    simp only [Bool.and_eq_true, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hh
    exact raw_required h _ _ sub _ _ hh.1 (fun w hw hn => (of_decide_eq_true hh.2 w hw).resolve_left hn)
  by_cases hs : seed3108 ∈ S
  · right
    apply Finset.Subset.antisymm
    · intro v hv; exact List.mem_toFinset.mpr (sub v hv)
    · intro v hv
      have hm := List.mem_toFinset.mp hv
      simp only [roots3108, List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · exact haveIn (List.mem_toFinset.mpr hm)
      · exact hs
  · left
    apply Finset.Subset.antisymm
    · intro v hv
      have hm := sub v hv
      simp only [roots3108, List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · exact List.mem_toFinset.mpr hm
      · exact False.elim (hs hv)
    · exact haveIn

theorem noSup3108 : ImpossibleT graph 14 1 roots3108.toFinset := by
  have hall := forestT_all f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 14 (boundsBefore known383)
    (before_sound known383 valid383) geomdead tables3108 14 (by decide) 1 (by decide) 0 (by decide)
  have hsame : sameWords (stateSetT f3108Levels 43 0) roots3108 = true := by decide +kernel
  have htgt : targetOf dead = graph := by decide +kernel
  rw [← sameWords_sound hsame, ← htgt]
  exact hall

theorem noPos3108 : ImpossibleT graph 14 1 inputs.toFinset := by
  have hall := forestT_all f3108Levels f3108Idx0 f3108Idx1 f3108Idx2 14 (boundsBefore known383)
    (before_sound known383 valid383) geomdead tables3108 14 (by decide) 1 (by decide) 1 (by decide)
  have hsame : sameWords (stateSetT f3108Levels 43 1) inputs = true := by decide +kernel
  have htgt : targetOf dead = graph := by decide +kernel
  rw [← sameWords_sound hsame, ← htgt]
  exact hall

theorem bit_seed3108 (r : Row) : bit r seed3108 = (sample r 0 && sample r 2) := by
  revert r; decide +kernel

theorem main2046 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)))) → x1.size = (15 : ℕ) → List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x6 : ℕ) => Bool.false) Bool.false x5.op) x1.gates = (1 : ℕ) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) := by
  intro C legal first hsz hcnt hfun
  have headEq : (execute C.gates inputs).getD 9 zero = seed3108 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j, hj⟩
    change bit r ((execute C.gates inputs).getD 9 zero) = bit r seed3108
    rw [← b_read, execute_bits _ _ _ (fun g hg => (legal g hg).1), ← sampled]
    exact (first (sample r)).trans (bit_seed3108 r).symm
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j, hj⟩
    change bit r ((execute C.gates inputs).getD C.output zero) = bit r graph
    rw [← b_read, execute_bits _ _ _ (fun g hg => (legal g hg).1), ← sampled]
    exact (congrFun hfun (sample r)).trans (edge_table r).symm
  have out := get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  cases hgs : C.gates with
  | nil =>
    rw [hgs] at targetIn
    exact (show graph ∉ inputs from fun hm => by
      have hnc : inputs.contains graph = false := by decide +kernel
      rw [List.contains_eq_mem, decide_eq_false_iff_not] at hnc; exact hnc hm) targetIn
  | cons g rest =>
    have eq0 : gv inputs g = seed3108 := by
      rw [hgs] at headEq
      change (execute rest (inputs ++ [gv inputs g])).getD 9 zero = seed3108 at headEq
      obtain ⟨l, hl⟩ := exec_extends rest (inputs ++ [gv inputs g])
      rw [hl] at headEq
      exact headEq
    rw [hgs] at targetIn
    change graph ∈ execute rest (inputs ++ [gv inputs g]) at targetIn
    rw [eq0] at targetIn
    have tailLegal : ∀ gate ∈ rest, gate.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ gate.inputs.length ≤ 2 :=
      fun gate hg => legal gate (by rw [hgs]; exact List.mem_cons_of_mem _ hg)
    have len : rest.length ≤ 14 := by simp [Circuit.size, hgs] at hsz; omega
    have hcntEq : C.gates.countP (fun q => isNotT q.op) = 1 := by
      rw [← hcnt]; congr 1; funext q; cases q.op <;> rfl
    have ht1 : rest.countP (fun q => isNotT q.op) ≤ 1 := by
      rw [hgs, List.countP_cons] at hcntEq; omega
    obtain ⟨k, t, S, hk, ht, run, hs⟩ := extractT rest roots3108 tailLegal graph_proper targetIn
    rcases all_roots3108 run hs with e | e
    · exact noPos3108 k t (hk.trans len) (ht.trans ht1) (e ▸ run)
    · exact noSup3108 k t (hk.trans len) (ht.trans ht1) (e ▸ run)

end PEqualNP.Outside.L_meta_2046

theorem PEqualNP.Outside.L_meta_2046 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) && x3 (2 : Fin (9 : ℕ)))) → x1.size = (15 : ℕ) → List.countP (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x6 : ℕ) => Bool.false) Bool.false x5.op) x1.gates = (1 : ℕ) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 ≠ fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) :=
  PEqualNP.Outside.L_meta_2046.main2046
