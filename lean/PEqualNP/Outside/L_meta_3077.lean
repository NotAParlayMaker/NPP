import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3077
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
def f3077uL24F (i : Nat) : Nat := 0x50c1af759b4b3181aa9395034794da505c16cc854a540
def f3077uL24 : PackingT := (2,7,7,4,f3077uL24F)
def f3077uL27F (i : Nat) : Nat := 0x583820e01040000000000009db0670419c10670419db0675219e28670c1000b82c0e080000d0f03820002c6c100000000000000000000000140e0e8382000007c1050842c210b08424210b0842000000000149d1d3e4ef32cc12dcad28c9923c851ec7119c4307bfaf5bb2e3b6ad1b3cc62f4baae0af298a3a849ea56932428e22e8921a842067f1f27a1de751ca701b66b1a266174541464f13243904380bc26074140460f0320a01e0500a00617f328c76e1525a5408afeebd98dc2a4b4a8194fdc758ebb549695022bfbaf6636a992d2a04d6f75ecc549415a5408bf6e9598dba62b4a8115fdd7b31b5485695024bfbaf662a5552d2a061bf719a7aed814e540c37e6518cdc2e29ca8116fdd6b31b85c5395022bfbaf6636a90a72a071af6d0c6606aa4e540937eeb598c0d549ca8187bdb4b3181aa9395030f7b68e42e355272a0716f6d1875c6aa4e540e2deda2ecb8d549ca81c6bdb458961aa9395038f6b68c0ac355272a071ed6d181546aa4e540c3deda38a90d549ca81c7b5b45c521aa9395028fb9b4e0b6642a52a075e5505c16cc854a540c1fe65190db2a694a8113fdd8b31b654d295030dfb8cd3d76c0a52a065af71954aed814a5409b7ceb598c0a6094a81a7f0ca605514c1295030bf99463b70a9232a0457f75ecc6e15246540c2fee3b515daa48ca8185fdc769abb549195030bfb8ed1d76a9232a0457f75ecc6d5324654092fe6e30ed2ae28ca8125fdd7b3152aa919503e2bb0ab9b0ea9ad2a065db32d5254d825a540f8b6bab04c3aa4b4a81f34d5360983549695032eb996a9ae6a92d2a07d5354d725cd525a540f8e6b9b04c3a64b4a81f565525c572545695022bfbae65cab112d2a07d1d595715d9514e540f9b2a9302c12a29ca81f565525c57254539503e9cac4b8aec90a72a045bf758cba22114e540f9acc2a60c3aa694a8116fdd632d5360929503ec5aa8b12caa9252a070fd2e981619514a540f93ab2b02c32a294a81f2d563605864c529503e7a3029830c98a52a041ff770ba215314a540c2fe5d38e42a6294a8186fcba718854c5295030fb974e190a98a52a061fe2e9c0215314a540f8aec2ae6c3aa68ca81976ccb5495360919503e2daeac130ea9232a07cd354d8260d5246540cbae65aa6b9aa48ca81f54d535c97354919503e39ae6c130e99232a0457f75ccb9562246540
def f3077uL27 : PackingT := (73,6,7,10,f3077uL27F)
def f3077uH0_27F (i : Nat) : Nat := 0x28001004008
def f3077uH0_27 (h : Nat) : Option (Nat × Nat) := lookupWord 1 4 3 10 2 4 f3077uH0_27F h
def f3077uL28F (i : Nat) : Nat := 0x2da2379950f285030b7b8eda10355272a061af719b4086aa4e540c39ee2b6810d549ca8187b9b470021aa939502c97ba9554ef33272a058ed752aaa22114e540b2daea5553bc229ca8166b5d4aaa6684539502ce6ba9554ab08a72a059e9752aa88a114e540
def f3077uL28 : PackingT := (10,6,7,6,f3077uL28F)
def f3077uL30F (i : Nat) : Nat := (if i<4 then (if i<2 then (if i<1 then 0x97fccb606554a540a7fcca4c6554a540c7fcba61e114a540c7fcba616114a540c7fcba60e114a540c7fcba54e114a540c7fcbaa22114a540c7fcba6d58746540f1fd875d98546540f37d8561d6546540f75d536158346540f1fd876157346540f75d53615734654097fccb61d6346540b5fdc72e15346540b6fdc62e15346540b7edc22e15346540b7f5c12e15346540b7f9c02e1534654097fdcb61d534654097fccb61d5346540d5fdb761d5346540f37d8561d5346540b7ddc361d5346540f5dd7361d5346540b3fcc86d95346540b6fdc62c95346540f76d522c95346540f1fd875d98246540b6fdc62d58246540f76d522d58246540f1fd875d58246540f76d525d5824654097fccb5cd8246540b3fdc85cd8246540d5fdb75cd8246540f1fd875cd8246540f7cd325cd824654097fccb58d8246540f3dd8358d824654097fccb54d8246540d77db554d8246540f3dd8354d8246540b7edc254d8246540f76d5254d824654097fdcb54c8246540d77db554c8246540d7ddb354c8246540f5dd7354d7246540f76d5254d7246540f3ed8261d6246540f3ed8260d6246540d5fcb76e15246540d5fcb72e1524654097fdcb61d524654097fccb61d5246540d3fdb861d5246540f57d7561d5246540b7edc261d5246540f3ed8261d5246540d5fcb76d95246540d5fcb76cd5246540f75d5360d5246540f3ed8260d524654097fccb5cd5246540b77dc55cd5246540d7ddb35cd5246540f75d535cd5246540f5ed725cd524654097fccb58d524654097fdcb6095246540b5fdc7aed5246540d5fcb7aed524654097fdcb60c5246540d3fdb860c5246540d6fdb660c5246540d7ddb360c524654097fdcb61d324654097fccb61d3246540f5dd7361d3246540f3ed8261d324654097fdcb615324654097fdcb2153246540b5fdc72153246540b6fdc62153246540b7ddc32153246540b7edc22153246540b7f5c12153246540b7f9c0215324654097fdcb5d53246540f3ed825498146540f3ed824c98146540f1fd876157146540b5fdc76097146540f1fd876097146540f5ed725497146540d5fdb761d5146540f5f57161d5146540f76d526095146540d5fdb761d3146540b5fdc72153146540b6fdc62153146540b7ddc32153146540b7edc22153146540b7f9c02153146540f7cd326093146540f5f57161d2146540b5fdc72152146540b6fdc62152146540b7ddc32152146540b7edc22152146540b7f9c0215214654097fccb5ce884654097fccb54e884654097fccb54a884654097fccb4ca884654097fccb58e554654097fccb60a554654097fccb4ca5546540b5fdc72162246540b6fdc62162246540b7ddc32162246540b7edc22162246540b7f9c0216224654097fccb58e224654097fccb54e224654097fccba22224654097fccb9562246540 else 0xf5f5715d9214e54097fdcb615214e54097fdcb5d5214e54097fdcb595214e540f6ed62595214e54097fdcb545214e54097fdcb614214e540d6fdb6614214e540d77db5614214e540d7f9b0614214e54097fccb54a114e54097fccba22114e54097fccb88a114e54097fdcb618a54a540d6fdb6618a54a540a7fcca6dd854a540a7fcca61d854a540a7fcca6d9854a540f67d655d9854a540a7fcca6c5854a540a7fcca6e1654a540a7fcca61d654a540f37d8561d654a540f73d54615654a540a7fcca6cd654a540a7fcca6dd834a540a7fcca6d9834a540f75d53615834a540b7ddc3595834a540a7fcca6c5834a540f75d53615734a540a7fcca6e1634a540a7fcca6dd634a540c7fcba61d634a540a7fcca6d5634a540c7fcba615634a540d77db5615634a540c7fcba5d5634a540b5fdc72e1534a540b6fdc62e1534a540b7edc22e1534a540b7f5c12e1534a540b7f9c02e1534a54097fccb61d534a540f37d8561d534a540f7d93061d534a540a7fcca6d9534a540b3fcc86d9534a54097fdcb619534a540d6fdb6619534a540f7d930619534a540c7fcba5d9534a540f7d9305d9534a540f7d930615534a540a7fcca6c5534a540b6fdc62d5824a540d6fdb6595824a540f6ed62595824a54097fccb54d824a540f3dd8354d824a540f67d65615624a540f6dd6360d624a540b6fdc654d624a540f7d93054d624a540f73d54595524a540f6ed62595524a540f75d5360d524a540f7d93054d524a540b5fdc7215324a540b6fdc6215324a540b7ddc3215324a540b7f5c1215324a540b7f9c0215324a540d3fdb861ca14a54097fdcb614a14a540f2fd86595814a540d77db5595814a540f77551595814a540f2fd8658d814a540d7ddb358d814a540f7d53158d814a54097fccb54d814a540f7d93054d814a54097fdcb54c814a540d5fdb754c814a540d77db554c814a540d7ddb354c814a540f77551595714a540c7fcba61d514a540c7fcba619514a540f67d65619514a540f3f581619514a540c7fcba5d9514a540f67d655d9514a540c7fcba60d514a540c7fcba5cd514a540c7fcba58d514a540f67d65589514a540f73d54549514a54097fdcb60c514a540d7ddb360c514a540c7fcba61d314a540f7d93061d314a540f6dd63619314a540f3f581619314a540f7d930619314a540f7d9305d9314a540c7fcba615314a540f7d930615314a540c7fcba215314a540b5fdc7215314a540b6fdc6215314a540b7ddc3215314a540b7f9c0215314a540c7fcba5d5314a540b5fdc7215214a540b6fdc6215214a540b7ddc3215214a540b7f9c0215214a540f6ed62595214a540f7d93054d214a54097fccb54e884a540a7fcca546884a540a7fcca4c6884a540c7fcba60e554a540a7fcca58e554a540c7fcba58e554a54097fccb60a554a540) else (if i<3 then 0x97fdc7aed324654097fdc5aed3246540e5fda861d7146540e5fd876957146540e5fd8768d7146540e5fd876897146540a7fecc61eaa46540e3fd87616aa46540a7fdc2216aa46540a7fdc85d6aa46540e5fd875d6aa46540e3fd8760aaa46540a7fecc60aaa46540a7fdc85caaa46540a7fdc854aaa46540a7fdc754aaa46540e5fcc754aaa46540e77d7554aaa46540e7ed8254aaa46540e7ed7254aaa46540a7fecc54aaa46540c7fcba6d5875a540f1fd87615735a540f75d53615735a54097fdcb61d535a54097fccb61d535a540d5fdb761d535a540f37d8561d535a540b7ddc361d535a540f5dd7361d535a540f76d522c9535a540f76d522d5825a540f1fd875d5825a540f76d525d5825a54097fccb5cd825a540b3fdc85cd825a540d5fdb75cd825a540f1fd875cd825a540f7cd325cd825a54097fccb54d825a540d77db554d825a540f3dd8354d825a540b7edc254d825a540f76d5254d825a540f5dd7354d725a540f76d5254d725a540d5fcb76e1525a54097fdcb61d525a54097fccb61d525a540d3fdb861d525a540f57d7561d525a540b7edc261d525a540f3ed8261d525a540d5fcb76cd525a540f75d5360d525a540f3ed8260d525a54097fccb5cd525a540b77dc55cd525a540d7ddb35cd525a540f75d535cd525a540f5ed725cd525a540d5fcb76c5525a540b5fdc7aed525a540d5fcb7aed525a54097fdcb60c525a540d3fdb860c525a540d7ddb360c525a54097fdcb61d325a54097fccb61d325a540f5dd7361d325a540f3ed8261d325a54097fdcb615325a54097fdcb5d5325a540d77db5549715a540f5ed72549715a540b7f5c1549715a540f77551549715a540d7ddb34c9715a540f76d525c9515a540f5f5715c9515a540b7ecc26dd315a54097fdcb5d5315a540d5fdb75c9315a540d77db5549315a54097fdcb149315a540b7ddc3149315a540b7f5c1149315a54097fdcb5d5215a54097fdcb5cd215a540b7f5c15cd215a54097fdcb54d215a540f7d5314c9215a54097fccb60a555a54097fccb4ca555a54097fccb54e225a54097fccb956225a540d6fcb66dd814e540d5fdb75d9814e540d6fcb66c9814e54097fccb549814e540f77551549814e540b6fdc6aed814e540d6fcb6aed814e54097fdcb548814e540d5fdb7548814e540d7edb2548814e540f4fd76595714e540f77551595714e540d6fdb6589714e540f4fd76589714e540f7e521589714e540d77db5549714e540f5ed72549714e540b7f5c1549714e540f77551549714e54097fdcb61d614e540d5fdb761d614e54097fdcb5d9514e540f5f5715d9514e540f3f581609514e540f76d525c9514e540f5f5715c9514e540d6fdb6589514e540b77dc5589514e540f67d65589514e54097fdcb608514e540d7edb2608514e54097fdcb5d9214e540 else 0xf6bd86595414a540f6bd76595414a540f73d85595414a540f6bd65589414a540f5bd875c5414a540d7bdb8551214a540d7bdb5551214a540f7ad54589214a540d7bd54aed214a540b7facc61d304a540f5f9875d9304a540f3f987615304a540b7facc615304a540f5f9875d5304a540f6f986595304a540f6f976595304a540f77985595304a540f6f965589304a540f6f8c6605304a540f3f986605304a540b7facc605304a540b7f9c85c5304a540f5f9875c5304a540f5f9765c5304a540f7f181585304a540b7f9c8545304a540f7f181545304a540b7f9c8145304a540a7fecc61eaa4a540a7fdc85daaa4a540e5fd875daaa4a540c7fd876d6aa4a540c7fd766d6aa4a540e3fd87616aa4a540e5fd875d6aa4a540a7fdc7596aa4a540e6fd86596aa4a540e6fd76596aa4a540e77d85596aa4a540e6fd6558aaa4a540c7fd876c6aa4a540c7fd866c6aa4a540c7fd766c6aa4a540c7fd856c6aa4a540e3fd86606aa4a540e5fd875c6aa4a540e5fd765c6aa4a540a7fdc1aaa884a540a7fdc52e9874654097fdc5aed8746540c7fda5aed874654097fdc3aed874654097fdc2aed8746540e3fcca61d8546540d7ddc26cc8546540d7ddc16cc854654097fecc6c88546540d7edc36c88546540d7edc16c88546540d7eecc6c88546540c7fcca6e17546540e5fcca61d7546540e5fd875d9a346540e3fd87615a346540e5fd875d5a346540e6fd86595a346540e6fd76595a346540e77d85595a346540c7fcca6e1734654097fecc6e1734654097fdc8aed734654097fdc5aed734654097fdc2aed734654097fdc7aed634654097fdc5aed634654097fdc2aed634654097fecc6e1534654097fecc6dd534654097fdc8aed534654097fdc7aed534654097fdc2aed5346540a7fecc61da246540e5fd875d9a246540e3fd87615a246540e5fd875d5a246540e6fd86595a246540e6fd76595a246540e77d85595a24654097fdc7aed824654097fdc5aed8246540c7fda5aed824654097fdc3aed824654097fecc6e17246540e6fd766956246540e6fd7668d6246540e6fd6568d6246540e6fd656896246540e7eda56096246540c7fcca6e15246540d5fcc76e1524654097fecc6e1524654097fecc6dd5246540e5fda82dd5246540e5fcb76995246540e77da85d55246540c7fdb868d5246540e5fcb768d5246540c7fdb668d5246540e77d7568d5246540f57cb754d5246540f5ecb76095246540e7eda36095246540e7eda85c95246540e7eda65c95246540e7eda35c9524654097fdc8aed5246540c7fda8aed5246540d5fdc7aed524654097fdc7aed5246540c7fda6aed524654097fdc3aed5246540c7fda3aed524654097fecc6cc524654097fecc6e1324654097fecc6dd3246540d5fcc76d5324654097fecc6d5324654097fdc8aed3246540)) else (if i<6 then (if i<5 then 0x97fdc1aed735a54097fecc6e1535a54097fdc8aed535a54097fdc7aed535a54097fdc2aed535a54097fdc1aed535a54097fdc7aed825a54097fdc5aed825a54097fdc3aed825a540c7fcca6e1525a540d5fcc76e1525a54097fecc6e1525a540f4fcb758d525a540f67d7558d525a540f57cb754d525a540f5ecb7609525a540f6ed635c9525a54097fdc8aed525a540d5fdc7aed525a54097fdc7aed525a54097fdc3aed525a540d6fd63aed525a54097fdc1aed525a540d6fdc66cc525a54097fecc6cc525a54097fecc6e1325a540d5fcc76d5325a54097fecc6d5325a54097fdc8aed325a54097fdc7aed325a54097fdc5aed325a54097fdc1aed325a540f57cc7549515a540f5bcc7549415a540f73d75549415a540f7ad72549415a540b7becc549415a540d7ecc26dd315a54097fecc6dd315a54097fecc6d5315a540d5fcc76d5215a54097fecc6d5215a54097fecc6cd215a540e5fcc754aaa5a540e77d7554aaa5a540e7ed7254aaa5a540a7fecc54aaa5a540e6fda72d9814e54097fdc7aed814e540c7fda7aed814e540d6fdc6aed814e54097fdc6aed814e54097fdc2aed814e540c7fcca6e1714e540d6fcc66e1714e54097fecc6e1714e540e5fcca61d714e54097fecc6dd614e540e7f5a7605614e540f6f4c6605514e540c7fda86c8514e54097fecc6c8514e540c7fcca6d5214e540d5fcc76d5214e54097fecc6d5214e54097fdc6aed214e54097fdc5aed214e540c7fda5aed214e540d77dc86d4214e540e6fcc6606aa4e540a7fecc606aa4e540a7fdc85c6aa4e540e5fd875c6aa4e540e5fd765c6aa4e540a7fdc8586aa4e540a7fdc7586aa4e540e6fd62586aa4e540e7f581586aa4e540e7f581546aa4e540a7fdc2146aa4e540a7fdc5486aa4e540e7f571486aa4e540a7fecc486aa4e540a7fdc12e9874a54097fdc6aed874a54097fdc3aed874a540d7ddc26cc854a540d7ddc16cc854a540f6bd86595544a54097fecc6e1534a540c7fcca6d9534a540d3fcc86d9534a54097fecc6d9534a54097fdc8aed534a54097fdc6aed534a54097fdc5aed824a540d7bd54aed824a540f6bd65551624a540f7ad54609624a540d7bd54aed624a540d7bdb8551524a540d7bdb6551524a540f7ad54609524a540f7ad54589524a54097fecc6e0a14a540e6fda72d9814a540e3fda7619814a540f6bcb6551814a540f3bd86551814a540f3bd54609814a540b7f5c5285814a540c7fda7aed814a54097fdc6aed814a54097fdc5aed814a540d7bd54aed814a54097fdc3aed814a540d7bd546c8814a540e5fda861d714a540e5fda85d9714a540f6bd54589614a540e7f5a7605614a540f7b554605614a540d7bdb8551514a540f7b554605514a540b7becc61d414a540f5bd875d9414a540f3bd87615414a540f5bd875d5414a540 else 0x6d639ab8b5546a6ed469a84b4ec69b6d2f9a50b48468ced0f9a10b41067e6cf599dcb39066e6cd5999cb31c6616cbe9974b2d86576ca49934b24c645ec849900b1d8638ec6798c0b164628ec4d988cb0fc61bec309852b0886106c1c9830b050607ec089802afe85fc6bf197d4af8c5ec6bd19794af0c5ddebb4975aae985cf6b979726ae305c26b7d96ecadbc5b3eb6096b2ad3c5a3eb43967eace0596eb299650ac9058e6b159610ac0457b6aec95c4ab605686ac99584aaec5586aac954aaa78549ea8c9504a9ec539ea6c94caa97852b6a4f9490a90451cea329450a89050fea189422a83450169fb93eea7cc4f5e9e493b4a74c4e5e9c79386a6fc4dbe9b69364a6c44d4e999932aa6504c7e98e9314a6244c3e98692f2a5d44b8696f92dca5784ace95892a8a54c4a8e9509292a50849a69309258a4a0493691f923ca46848669089208a40c47f68f791daa39846f68d791a0a324460e8bd9178a2c845568a6913ea26044b688f911ca22843e687290d6a19c42fe852908aa0f841b682f904aa07840b680f9010a0043fce7f58fdc9f9c3f2e7db8fa89f283dfe7bb8f689ecc3d767ad8f589ea03d1e79f8f3c9e5c3c9678b8f0e9e183c267838efe9dec3bb676f8ed69d903b167558e9c9d1039fe7358e5c9c9c38fe7158e1c9c1c37fe6f88de89bb4372e6de8db49b4c365e6c48d7a9ad835766a78d409a64348e68a8d0699f033a666a8cc69964328e6478c7498b430fe6128c0a97bc2f265dd8ba697182df65b78b6096a42d0e59a8b2096302c3e57d8ae095a42b265578a9a950c29c65318a54947428ae50e8a0893f427964ee89ce938026de4da89a0931825f64b4894e9280249648888fc91e8234e45f88bc9174229644e888890e8217e42b8848907420ae40b880e90001fde3f787e68fa41f263da87a68f301e263ba87608ea41d0e39a87208e181bf637786d48d741aae34886828ce81996325863c8c5c187e30886028c0017c62f185e08bb017562dd85ac8b3c163e2c085728ac815262a0853e8a6c14ce28f85108a1013e627584e889cc138e26484c0897012d625984928908118e22d845888a0113621f8436885c10ae2148420883010261fa83e687980f0e1dd83b287600e861c98390871c0dce1b5836286c00d5e1a4833486400c4618182fa85d80b8e16a82c6857c0aee1538298851409ee1338252847c08a610d8212841408060fc81f083c407660e581c2836806960cb818282e8057e0ab8148827404ae08e810881e8039606b80c88174029604b808880f401ae02e804e807400ae00e800e8000a7fdc52e9875a54097fdc5aed875a54097fdc3aed875a54097fdc2aed875a540e3fcca61d855a540e5fcca61d755a540c7fcca6e1735a54097fecc6e1735a54097fdc8aed735a54097fdc5aed735a54097fdc2aed735a540) else (if i<7 then 0x800203c21dfc0e1207210880780dc481c842240e42112108070348f8682352101ec1a9df180cd070098349088404c436c10bc81ec19013200f1efd070c83888404c710c053b8a301ec1a140f0098883b714887218983381c2c19c0e100f007a070f067038403c00381c341e080080f0960b008436c102c15076010c6d9078884607c4422019a0e01f19076db11080f900780b840dd44341c05c4419a0e02e18c10089108c364203c0c808f352832503701e419180006e03c83230d9080f03220c8c07811d064603c06e83239820cc10060800407843044c420110474211a10840f9084407c14210a10840a80450846842101601f4211e108170b0840b8484200a201f005c211815008a108f06700858338042c19c02100f000e010d60807b008641c442200101e102f80f10ccc11017c046608884801e03c202901e20ed18200f01b88004078400203c2029011d182212002a0f0801400c400a006200500310028018803ba1ee2c360f7100ea42000101c1dfc3626108188b0840c45842062200303110008188800407040020383be35241df0806a42000f831a361805018880c423ba1ee202b0611000000101c18618e20c30463820000080e0c751b0ef968d83dc403817231c0323be518e08077c2000101c10c30461820007b843dc200f4382a19a1c9a9180080e080040707146a4838a158608d484000f4382007a1c100003830c38a006418608e2840b52100101c100080e0e28c71401c0bc743200e200101c10c30402a870430c100101c1000809096182000101c1c5180080e0b0670485833824218600f41218c7003a090c86800f0486438003824300101c100504028275210820cc304ea4028405a1c1a9a9100504091618583381c2c19c0e1041007a070f067038403800381c300a0ac36030b067018583380c2c19c061041003a030c0700070186002038200101c100080e08004048400203946c300101c10008090b01b070580d8382c06c1c120300388870005070600200e200100710008038800401c5175a2d6c5908ae7158a2a8c54c8a5f144a27ac4d88977127a23ac4588877104a1fac3d8875f0eaa1ccc37c86d70d3a198c32086070b9a164c2a0850709ca124c238841f07ca0eac1b8831f05ca0aac12c8237042a076c0d0817f025a03cc05c807f008a002bfe87faeff19fd4bf8c7edefd49f9abf0c7ddefba9f6cbebc7d56fa39f3ebe6c7c9ef8c9f10be047bcef729ed6bd907ae6f559e9cbd1079fef3b9e68bcb47946f249e40bc58785ef079dfabbd87776ee49dbabb64768eeca9d8cbafc75beeb09d52ba8874d6e939d18ba207406e799ce4b9b87336e5c9caab944724ee429c7cb8dc717ee289c48b8687096e089c02b7e86f96deb9bc8b7746ec6dd19b94b70c6ddedb49b5ab68c6cded949b1ab6186c0ed7d9aecb5bc6b5 else (if i<8 then 0x8475380423a9c0211db60108a1b00a6086305004200c5b610062e28a60803040181c0e0e071ee88ea7038581c13a9c0e11d4e0708ea7038476d81c2286c0e100f84e0b038581c1c0e3b611c160708e0b038476d81c201ec0e3b619d480f8b038203c002201e001140f1ee880ae078ea4603c05623a944911d4c0f08078004475213a909db04078200b03c200538203d18018029c10c00c014470407a238281e11c10400c0156086baa100101c629180082388004070400203829c50807b0e0803d868400200e200761c1003b0d0986401c409d509ee84ea4275213a907411d482e88eda0d84000100f100080e080040704002028c0c300101c100080e08004050400201e200100f100080e080040704002028200104711ee84ea511447520aa23a907411d482e88eda0d84002038200101c10008038800404d838600200e25860ac3056180f0408430d03839b608001c200200e20010071003817b1b2149001c0bc40ab30cc6c30010245c51803817c030c0040917146b0d00c202fb2014d4817881866a45352c6c85239a908244d488004070400200ec6c302f007100e023b228c00401c4002026200100710008078800401c400200e200705a1000803880040704002038200101c1022c4131b0d20829041482045100e00088ea4200200e80c301c00111d484e182038002200700110038009e28c01c004400f832238609d484ea42038002201d484000208220311df0371a900128ef84035210018840000008208c30c710618231c10000c40dc63806477ca31c100ef84000003d2088004104400205e38a35241c50ac3046a420007a411009d4205e06e30c38a418608e2840b52100703010e28038178e86401c4002082218627510c321b88004104400202425860800041047146002082218609d4e010871410440186c021011043023873805842400104118618c360108618200202a2182237c0242120c300490ca1c900041044002082218640910008208e28c02601c4002054200101210008038800401c400744421b60801d1108004088401b60030601d0c8018800408871460ae00b444318209d4ac108030c1000618275211c508000408843be10010221017040000c3046083304100102210c104004088400010221c51b62000811080040887146b0410010221c5180081108016888400b444240200122218008018800400c4002006200101e100f040a8078448b38a202a01e106c840a8078405403c201e037152286c8a6d80a4564003c200f01e100780f0818908440868c4200f01e122706c89084038484201c201e04740e1a10807080790380a8607f81c202a01e40e1818e10e07034900c70870381a4806384381c0d2401fc21c0e0692018e10815e07100783269170846a7038004f48b81c1b2340e42112108070348e0c70870381a4 else 0x5d50800820b148c004104400208229c50cea84000201e20010411000820880040504002082200100f1000820b2f8c004104400202820010410b61800820880041044002026c1c300038400401c541c1586a0e1017d900a6a43352c1c200104110178038810411d9146002026260e0800805b010c048200201e16c3001007100382d0800401c400208216c300104110008208800402d808730c1c0209c360108ea700858041003c41c0218008018800400c4006060200100310008018801f064470c13a908178008800c180400204420010031030001880880dd8d86002014200018400400c4048100100314db0410c2002012200100710180400c0c04002006200102210008110800400c400ac442003c1910110008800c004ed86704138208018008800c004470413b609d48401c00405c600600278a3386080480080b8c00c864400203c200101e60e1807818880b82353052200100f12070403f038400201e200101e100080f080040784c52034248622914db314898a43052b8a28295c512148d4886a4200200620030604021cc1201080342b05452298200c110f0400400c406e03e200101e1006840040798386019304204b98260e1cc13070a608030407136c29b600d1006adb086a403458041c023dd11d4e0108ea7))))
def f3077uL30 : PackingT := (651,5,7,15,f3077uL30F)
def f3077uH0_30F (i : Nat) : Nat := 0x680c5041c0134190813b04de664024d046c01020b801520237035e090409700200936101417d845a03de10f00180493078c0aec1a8049009260c5c185027000f007680e204400938084024a914406c0124024c8476015602680b2029a0844052412c03e807fc055816200530764106407982d0092007d800004900932040024900d702e01264112001706f20ea4058011d050006c0248049009340e480c9018c067a0f7824004940680124024d0060092203881c3b081000204080002a0411306043050600300041428c
def f3077uH0_30 (h : Nat) : Option (Nat × Nat) := lookupWord 25 96 7 15 7 4 f3077uH0_30F h
def f3077uL31F (i : Nat) : Nat := (if i<4 then (if i<2 then (if i<1 then 0xe4fda89de6646540e4fda59de6646540e4fda39de6646540e4fda29de6646540f0fe889de664654087fccb6a2554654087fccb68e554654087fccb68a5546540a77dc82ea5546540a77dc32ea5546540a77dc22ea5546540a77ccb6a25546540a77ccb68e5546540a77ccb68a5546540e37da8a225546540e37ccaa225546540e37cbaa225546540e37da3a225546540e37da2a225546540e37eaaa225546540e57da89de5546540e57da39de5546540e57da29de5546540e57eaa9de5546540f17e889de5546540e67da899a5546540e67da399a5546540e67da299a5546540f27e8899a5546540f47e7799a5546540b5ddc72163346540b6ddc62163346540b7cdc22163346540b7d5c12163346540b7d9c02163346540b6ddc614a3346540e3dccaa223346540f1de889de3346540f2de8899a3346540f4de7799a3346540e75cca9563346540f35e889563346540f55e779563346540f65e66956334654087fccb6a2224654087fccb696224654087fccb68e2246540e3eda2a222246540e6eda299a2246540e76da29562246540a7edc82ea2246540a7edc52ea2246540a7edc32ea2246540b5edc72e22246540a7eccb6a22246540a7eccb6962246540b5edc72162246540b6edc62162246540b7cdc32162246540b7e5c12162246540b7e9c02162246540a7eccb68e2246540e3eda8a222246540e3eccaa222246540e3ecbaa222246540e3eda5a222246540e3eda3a222246540e3eeaaa222246540e5eda89de2246540e5eda69de2246540e5eda59de2246540e5eda39de2246540e5eeaa9de2246540f1ee889de2246540e6eda899a2246540e6eda599a2246540e6eda399a2246540f2ee8899a2246540f4ee7799a2246540e76cca9562246540e76cba9562246540e76da89562246540e76da69562246540e76da39562246540e76eaa9562246540f36e889562246540f56e779562246540f66e669562246540e7ccba8ce2246540f3ce888ce2246540f5ce778ce2246540f6ce668ce2246540f74e558ce2246540b5f5c72161146540b6f5c62161146540b7d5c32161146540b7e5c22161146540b7f1c02161146540b6f5c614a1146540e3f5a8a221146540e3f5a7a221146540e3f5a5a221146540e3f5a3a221146540e3f5a2a221146540e5f5a89de1146540e5f5a59de1146540e5f5a39de1146540e5f5a29de1146540f1f6889de1146540e775a59561146540e775a89561146540e775a39561146540e775a29561146540f376889561146540f576779561146540f3d6888ce1146540f5d6778ce1146540f756558ce1146540e7e5a288a1146540e7e5a888a1146540e7e5a588a1146540e7e5a388a1146540f3e68888a1146540f5e67788a1146540f7665588a1146540f7c63388a1146540a6bdc4aaa664e540a7b5c4aaa114e540 else 0x87fdc32ea114a54087fccb6a2114a54087fccb69e114a540c7f4ba606114a540f7d1314c2114a540c3fcbaa22114a540f3b541a22114a540c5fcba9de114a540f5b5419de114a540c77cba956114a540f73541956114a540c7dcba8ce114a540f7a54188a114a540a7f5c82ea114a540a7f5c52ea114a540a7f5c32ea114a540a7f6cc2ea114a540a7f4cb6a2114a540a7f4cb69e114a540a7f4ca61e114a540b6f5c62d6114a540b7e5c22d6114a540b5f5c7216114a540b6f5c6216114a540b7d5c3216114a540b7e5c2216114a540b7f1c0216114a540b7b4cb552114a540a7f4ca54e114a540f7d1534c2114a540a7f5c8aaa114a540a7f5c5aaa114a540a7f4caa22114a540e3f5a8a22114a540e3f4caa22114a540e3f4baa22114a540e3f5a7a22114a540f3b554a22114a540f3f130a22114a540e3f6aaa22114a540e5f4ba9de114a540e5f5a89de114a540f5b5549de114a540f5f1309de114a540e5f6aa9de114a540f1f6889de114a540e6f5a899a114a540e6f5a799a114a540f6b55499a114a540f6f13099a114a540e6f6aa99a114a540f2f68899a114a540f4f67799a114a540a7f4ca956114a540f73554956114a540e774ca956114a540e774ba956114a540e775a8956114a540f77130956114a540e776aa956114a540f37688956114a540f57677956114a540f67666956114a540e7d4ba8ce114a540f3d6888ce114a540f5d6778ce114a540f6d6668ce114a540f756558ce114a540e7e4ba88a114a540e7e5a888a114a540f7a55488a114a540f7e13088a114a540f3e68888a114a540f6e66688a114a540f7665588a114a540f7c63388a114a540c7ddca6cc854654097decc6cc8546540c7edca6c8854654097eecc6c8854654097f6cc6c4854654087fccb61da346540a5fdc7215a346540a6fdc6215a346540a7ddc3215a346540a7edc2215a346540a7f5c1215a346540a7f9c0215a34654087fccb61da246540a5fdc7215a246540a6fdc6215a246540a7ddc3215a246540a7edc2215a246540a7f5c1215a246540a7f9c0215a246540c5fdba2dd524654095fdc7aed5246540c6fda86d8524654096fecc6d85246540c6fdb668c524654096fdc6aed8146540a5fdc7216aa46540a6fdc6216aa46540a7ddc3216aa46540a7edc2216aa46540a7f5c1216aa46540a7f9c0216aa46540a6fdc614aaa4654087fccb69e884654087fccb68e884654087fccb68a8846540a3fdc52ea8846540a3fdc32ea8846540a3fdc22ea8846540a3fccb69e8846540a3fccb68e8846540b2fdc62ca8846540a3fccb68a8846540b2fdc614a884654095fccb54a7746540e1fda8a227746540e1fccaa227746540e1fda3a227746540e1fda2a227746540e1feaaa227746540e2fda7a226646540e2fda3a226646540e2fda2a226646540) else (if i<3 then 0xe3f8ba4c2884a540f3d9534c2884a540f3d9314c2884a540a3fdc5aaa884a540a3fdc1aaa884a540a5fcca58e774a540a5fcca54e774a540a5fcca546774a540a5fcca4c6774a540f5d9534c2774a540f5d9314c2774a540a5fdc8aaa774a540a5fdc5aaa774a540a5fdc1aaa774a540a5fccaa22774a540e1fccaa22774a540f1bd54a22774a540f1bd41a22774a540f1f930a22774a540e1feaaa22774a540a6fcca61e664a540a6fcca54e664a54096fccb606664a540a6fcca546664a540f6d9534c2664a540f6d9314c2664a540a6fdc8aaa664a540a6fdc5aaa664a540a6fdc1aaa664a540e2fda7a22664a540f2bd54a22664a540f2bd41a22664a540f2f930a22664a540e2feaaa22664a540e4fda89de664a540f4bd549de664a540f4bd419de664a540f4f9309de664a540e4feaa9de664a540f0fe889de664a54087fdc82ea554a54087fdc32ea554a54087fdc12ea554a54087fccb69a554a540f759534c2554a540c3fcbaa22554a540f33d54a22554a540c6fcba99a554a540f63d5499a554a540a77dc82ea554a540a77dc32ea554a540a77dc12ea554a540a77ecc2ea554a540a77cca61e554a540a77ccb69a554a540a77cca58e554a540b57dc72c6554a540b57dc7206554a540b73ccb506554a540a77cca4c6554a540f759314c2554a540a77dc8aaa554a540a77dc1aaa554a540a77ccaa22554a540e37ccaa22554a540e37cbaa22554a540f33d41a22554a540f37930a22554a540e37eaaa22554a540e57da69de554a540f53d419de554a540f579309de554a540e57eaa9de554a540f17e889de554a540e67cba99a554a540f63d4199a554a540f6793099a554a540e67eaa99a554a540f27e8899a554a540f47e7799a554a540a7dcca61e334a540b5ddc7216334a540b6ddc6216334a540b7cdc2216334a540b7d5c1216334a540b7d9c0216334a540b5ddc7206334a540a7dcca546334a540a7dccaa22334a540e3dccaa22334a540f1de889de334a540f2de8899a334a540f4de7799a334a540a7dcca956334a540e75cca956334a540f35e88956334a540f55e77956334a540f65e66956334a540b5edc7216224a540b6edc6216224a540b7cdc3216224a540b7e5c1216224a540b7e9c0216224a540b5edc7206224a540f7c9534c2224a540f7c9314c2224a540e3eda8a22224a540e3eccaa22224a540f3ad54a22224a540f3ad41a22224a540f3e930a22224a540e6eda899a224a540f6ad5499a224a540f6ad4199a224a540f6e93099a224a540f2ee8899a224a540f72d54956224a540e76cca956224a540e76da6956224a540f72d41956224a540f76930956224a540f36e88956224a540f66e66956224a540f3ce888ce224a540f6ce668ce224a540f74e558ce224a54087fdc82ea114a54087fdc52ea114a540 else 0xf756558ce115a540f5e67788a115a540f7665588a115a540f7c63388a115a540c6fdba2d9814e54096fdc6aed814e54095fecc6dc814e540c77dca6d4214e540977ecc6d4214e540c7bd766d2aa4e540c7bdb4606aa4e540a5fdc7206aa4e540c7bdb4206aa4e540c7bdb45c6aa4e540c7bdb4586aa4e540c7bdb4546aa4e540c7bdb4146aa4e540c7bdb4486aa4e540a6fdc6086aa4e540a77dc5086aa4e540c7bdb4086aa4e540a7f9c0086aa4e54096fccb606664e540e4feaa9de664e54087fccb69e114e540a7bdc4aaa114e540a7f5c82ea114e540a7f5c52ea114e540a7f5c22ea114e540a7f4cb69e114e540b6f5c62d6114e540b5f5c7216114e540b6f5c6216114e540b7d5c3216114e540b7e5c2216114e540b7f1c0216114e540b6f5c614a114e540e3f4baa22114e540e3f5a7a22114e540e3f6aaa22114e540e5f4ba9de114e540e5f6aa9de114e540f1f6889de114e540e6f5a799a114e540e6f6aa99a114e540f2f68899a114e540f4f67799a114e540e774ba956114e540e776aa956114e540f67666956114e540e7e4ba88a114e540e7e6aa88a114e540f6e66688a114e540f7665588a114e54087fdc52e9874a54087fdc32e9874a54087fdc12e9874a540c7ddca6cc854a540d7d9c06cc854a54097decc6cc854a54097eecc6c8854a540c7f5ca6c4854a540d7b5c46c4854a54097f6cc6c4854a54087fdc82e9634a54087fdc52e9634a54087fdc12e9534a54095fdc7aed524a540c6fdba2d9814a54096fdc6aed814a54095fecc6dc814a540d5bdb7550814a54087fdc82e9514a54087fdc32e9514a540c7f4ba605514a540b5bdc7215414a540b6bdc6215414a540b79dc3215414a540b7adc2215414a540b7b5c1215414a540b7b9c0215414a54087fdc82e9314a54087fdc52e9314a540c7f4ba605314a540f7c5324c5214a54097f9cb215304a540b5f9c7215304a540b6f9c6215304a540b7d9c3215304a540b7e9c2215304a540b7f1c1215304a540f7598554d304a540b7dacc54d304a540f75953549304a540b5f9c7205304a540b7d9c3205304a540a7f8ca545304a540b7d9c3145304a540b7d9c54c5304a540f7d1814c5304a540b7dacc4c5304a540f7d131485304a540a5fdc7216aa4a540a6fdc6216aa4a540a7ddc3216aa4a540a7edc2216aa4a540a7f5c1216aa4a540a7f9c0216aa4a540c7f5b1606aa4a540a5fdc7206aa4a54087fdc52ea884a54087fdc32ea884a54087fdc12ea884a54087fccb69e884a540a3fcca61e884a540c7bcba552884a540c7bcba506884a540c7f8ba4c2884a540a3fdc52ea884a540a3fdc32ea884a540a3fdc12ea884a540a3fecc2ea884a540a3fccb69e884a540e3bcba552884a540a3fcca58e884a540a3fcca546884a540e3bcba506884a540a3fcca4c6884a540)) else (if i<6 then (if i<5 then 0xa04e7de9ea67749d5e7229af665897ce58e95364e8929e4368f163788c1e25a892622087de1c286c61a0863e17e85b615c84fe12284460f4838e0ba827608c81ee05e8136030804dfea7f35fbc7eadf9a7e25f847dcdf627d45f4c7cedf2a7c65efc7b4deb67a95e947a0de7e79b5e5c792de4678d5e24784de0277f5df876add527385c34705dc066fd5be46f4dbc26e95b946e0db726d85b446ccdb226c45af46b5dac66ad5aa46a7da9a6a25a7869cda626945a4068eda3668c5a20683da0a6815a0067bd9de67359b0667d98265c5954650d93e64e593464bd91e6465914643d90a63e58e8635d8c662a589861bd852610583c60ad81a60257f85f9d7d65f157c05ebd7aa5e657885ddd7725db57685d8d75e5c456c45a6d66658c5614580d5f257855d056fd5ae567558c55ed56a553553c54ad51a54254f8539d4ca52e54a8525d47a517544c50ed41250053f04f7d3ce4f253c44efd3ae4e753984e4d3824dc53604d6d3564d153404cbd31e4c653144c3d2fe4bb52e84b8d2d24b052bc4add2b24ab52a84a8d29e4a652944a3d27e49b525c495d252493524847ed1ea467518c45ed13a43b50a0414d0063ee4f6c3c7ced23a14e3837acd9e3544d10327cc5e3134c0c2f5cb8a2cf4afc2aeca9229a4a28258c8b61fc47e01f3c7be1eb479c1e2c77a1da47641d4c74e1d247441cfc73a1cd47301c7c71a1c547101c2c676178454c14ec51e14344fc13ac4da13244c412fc4ba12d44b0127c49a1254490122c47a11d447011ac466115444410cc4160fe43e80f8c3de0f643d40f3c3ca0f143c00e2c3560c543100c2c3060ba42d80b1c2b60a942940a0c2720984244089c216081420007ec1f607c41ec076c1d607441cc071c1c206c41ac069c1a20674198064c18205f417805cc16e05a4164057c15a0554150052c13a04a4118041c0ea03640c8030c0be02e40b4028c09e0264094023c08a01e407401bc06a0194060016c056014404000ec03600c402c009c0220044000c5fdba2dd525a54095fdc7aed525a54095fccb54a775a540a77dc82ea555a540a77dc32ea555a540a77dc22ea555a540e37cbaa22555a540f47d639de555a540f53d419de555a540e57eaa9de555a540f17e889de555a540f1de889de335a540e75cca956335a540f35e88956335a540f55e77956335a540a7edc82ea225a540a7edc52ea225a540a7edc32ea225a540e6ecba58e225a540e3ecbaa22225a540f4ed639de225a540f5ad419de225a540e5eeaa9de225a540f1ee889de225a540e76cca956225a540e76cba956225a540f66d63956225a540f72d41956225a540e76eaa956225a540f36e88956225a540f56e77956225a540e7ccba8ce225a540f3ce888ce225a540f5ce778ce225a540f74e558ce225a540f57677956115a540f5d6778ce115a540 else 0x5001680048388864006443200260e0818a42c04160e0b07058a42c04160e0808a4206020b0105838200000004503602900e002005302f82281b0070010029809c008014600ab04002006400558200100325db0018a400360014020d8005008360014020d80050083304124598214c1066082b0415820e800660824353042d000e80074002435a00222950012c107400241c4432003d000e80074002c1c10000c52160e0800c1c16290b07040060e0818a42c1c10001a0012290800c1c160e08000000000000c1c100c0b07040000017d9158d80a581803cde30105f64563602960e007378c0400c283206e05400e048505505fc36029c06c19302102fe22814e0360c9817f1170d80a701803cc05e0bf88b86c053832605fc45c36029c06003302fe22e1b014e03000980dc0a803000c0041ecc0aa0bf86c05381d832604205fc45029c0ec19301882fe22e1b014e0c9817f1170d80a703801cc0bf88b86c05381c006605fc45c36029c0e001332fb1b3075e2803940bc14b97f8d80ab0a783801f0192078c8a052c1c0145186081e52fd228148051707383b81800c983381d83980dc35e306c19c0ec1cc06e1af18360ce0e60370d78c1706707303b86bc60a83801a006341c0050011e0e60200a0069c3140701140dc0d80a80a406003c03801c01800c008004000066008e06e05404803001e01c00e00c006004002000032e04704503703602a02901800f00e007006003002001000019878c0403c200e1f180f8c046183e301d000818d820000000010dc20000005605403001e01c00e00c006004002000032c02b02401800f00e007006003002001000019601581500c00780700380300180100080000cb3c60243001e20070f8c07c603e301636080000018d820000046e100000d000e80074002435a00221c500168004000000000002800c00401c801400600200e400a5860030010072800023698614c306618330c15860ac3074003a001d00090d680088714004b0c1636080000018d82000000237080000000c6c100000000000001a001d000e80074002038a002d000b1b04000018d820000006360800000000031b040000000210090807ad8e99fa62e947a34e88fa1ee8379fce7df9f2e7b79e8e78f9dee7379bce6af99ae657984e5cf96ee5a7964e57f94ee4f7938e4cf92ee4a7924e47f91ae457910e42f906e4078fce2ef84ae0e77f8df9f7b2dd6770cdacf68ad927608d6ef5aad577510d2af45ed167454d0af3aece7738ccdef36acd67348ccdf31acc272eccb6f2d6cb472cccb1f2c2caf72b8cacf2aecaa72a4ca7f29aca57290ca2f286c8871d4c5bf122c3e70e8c35f08ac187050bfdef92bc86ed4ba4ee6ab966e30b75ed72b496cfcb34ec9eb1a6c40b05ebb2ad06b00aafea8aa986a38a7ae9b6a5d6934a42e8caa256860) else (if i<7 then 0x6e07a0c98bfc8bc53c0c00780491820b2fb22b1b00300294608202001e002fba4bc5bb6ba9b86410b000053e1178c60d0058029c11804015eee00b805c006e08e02001e0ae301004400f005bb8280802200782b817141c6f56ee005c006e08c02e1c22f18014386005382361178c00a1c30029c11804019af22ee00b803c006e090845e3002870c704002600001400400c6421bbfb8bb6db5391db05b0c003a00a9820cc1066082b0419820e80074002435a002d0009102800b400200000000000000000000001903601800e00600200002a401380c003001000007980640d80a406003801800000d00bec8ac6c052c0401e6031f1802e1f8c0401c20bec8ac6c052c1c006602d00d6211f8c041140a401800a084000190e0be08a03201c03c004000054805f04503601901800e00a0000034f2ff1b057805809803999158a583aed800ca06e0c803e31820806202d108c1140d80600180b4000190e04e0320300280040c600001e843701f00206341ee1a3601610e0d0f00b087068646380405d8344c02c19016c1a2201100e108f008807084608a05304207c00c0220000c8804503601800e00600206b00002a4835a1081f00af0d1405407d01c884014a03c753e3000a4c0ef1802e1e0778c0170f06840103bc6007d084d81c753e3002c4c0ec2101f3a9f182818c0778c009c109603a084638606281de3002d50c5c0e02ef183822017002a109c110193c600b405908407cc81c00a842704410082101f00d200ff8c41080b12084e08481de3084202640473dfc37c2102ec02e1af18401b9efe24e1081760170d78c2003cf7f1270dc0bb00b86bc6107be89386e752026017c3400e8c1901fc0ee1af1829ef82361b9d4e10a0d002800a0066ed80f4028014a08e7bf86e05c01802c01600a704902904503601800e00600200002a481380c003001000007980081140d80a406003801800000d203c08a06e06c05405244200e00c006004002000032ed000a24d0d1108d0dc88686860d202644203e4f1808078400c3e301f180d8c0483b4004433a002b180910e800bc60241c4432003221900168007400241da002d00090ce8008887400441c44320032219001680074003a001d000818a42c04160e0834003a00101f090ce800883888640064432002d000e8007400206290b01058382060e0b14858082c1c10001140d803800807c0acc04e01c03000c00400001e705f04503600201800e006000003481581500f01480c00780700380300180100080000cb883a400560014290d80050a43e30121800f100187c603a001f180907680086083a001b180910e80088864005a001d000e8004006020b07040c0416020b070400030105838200034003a001d00090d6800b4002452a002d00090ce800b400200001a00100000d000e80074003a00101e else 0x32fb073015e2803940bc14b97c0ab0a783801f01b80920f18090c0078801c2060e0b010400000009860cc3066182b0c1030705808200000c1c16020800000000000000019158a581aed800ca)))
def f3077uL31 : PackingT := (549,5,7,14,f3077uL31F)
def f3077uH0_31F (i : Nat) : Nat := 0x4ccc81580490092a00341bc03ca04fc29f81b00497333c2de8200049406a82d00248049009201258184bb4d04a0124024e8460093e864024e03940740124024804900920127c06804900920124024c82ae06940ec00ccd9900920124c1628260092012402488a500920125e4c8049704563000248049305a405002480492020012402488440092ccda992c0329067e2cf1db8049f4000124024b013466f42b782080494301ccc80248049107024500248049876a01242000400083020000002040000004000
def f3077uH0_31 (h : Nat) : Option (Nat × Nat) := lookupWord 18 97 7 15 7 4 f3077uH0_31F h
def f3077uH1_31F (i : Nat) : Nat := 0xa00ac0400200a00a17200ae0306600a00a30500a50100a60000aa13109b6370600a00a00a00a00a26800a00a00a00a00a56700a00a00a00a00a60710800a00a000000000
def f3077uH1_31 (h : Nat) : Option (Nat × Nat) := lookupWord 6 43 6 12 4 4 f3077uH1_31F h
def f3077uL33F (i : Nat) : Nat := (if i<4 then (if i<2 then (if i<1 then 0x5cd19503bfec3ac68ca81dff2d56346540effb0ab1a32a077fd7558d19503bfe592c68ca81dff6e15346540eff970a9a32a077fdb754d19503bfec3aa68ca81dff6d95346540effb0ca9a32a077fd7654d19503bfec2aa68ca81dff5955346540effb64a9a32a077fcb254d19503bfed8aa68ca81dffaed5346540effb6ec1232a077fd8760919503bfedb3048ca81dff5d98246540effb6ac1232a077fcb560919503bfec2b048ca81dff5d58246540effacac1232a077fdb360919503bfec1b048ca81dff5cd8246540effac6c1232a077fd5360919503bfed8b048ca81dffaed8246540effaa641232a077fd865c919503bfec2ae48ca81dff5957246540effb06b9232a077fd635c919503bfea9ae48ca81dff61d6246540effb0ab1232a077fd7558919503bfec1ac48ca81dff5cd6246540effaa6b1232a077fd8258919503bfedc2a48ca81dff2e15246540effb6ea9232a077fd8754919503bfedb2a48ca81dff6195246540effaeca9232a077fd8554919503bfeb2aa48ca81dff6cd5246540effb06a9232a077fd7354919503bfeb1aa48ca81dff54d5246540effb04a9232a077fd6254919503bfed8aa48ca81dffaed5246540effb0c29232a077fd8314919503bfeb18a48ca81dff6e13246540eff97099232a077fdb74c919503bfec3a648ca81dff6d93246540effb0c99232a077fd764c919503bfedaa648ca81dff2d53246540effb0a99232a077fc854c919503bfebaa648ca81dff5953246540effb0499232a077fd624c919503bfea92648ca81dff6c53246540effd7699232a077fd8760519503bfec2b028ca81dff5d58146540effb06c0a32a077fd7360519503bfea9b028ca81dff6098146540effaa4c0a32a077fd3260519503bfec2ae28ca81dff60d7146540effaa6b8a32a077fd825c519503bfea92e28ca81dff4c97146540effb0ea8a32a077fd8554519503bfec1aa28ca81dff5cd5146540effaa6a8a32a077fd8254519503bfea92a28ca81dff4c95146540effb0e98a32a077fd854c519503bfe42a628ca81dff5d53146540effb0498a32a077fd524c519503bfec3a428ca81dff6152146540eff90a90a32a077fd7548519503bfec1a428ca81dff5cd2146540effaa690a32a077fd8248519503bfea92428ca81dff4c92146540effaeb44232a077fd73a2119503bfea9d108ca81dff5ca8846540effaa544232a077fd32a2119503bfeb8d108ca81dff5468846540effa6344232a077fd21a2119503bfec34aa8ca81dff60e5546540effac72aa32a077fd8295519503bfeb14aa8ca81dff4ca5546540effb032aa32a077fd3195519503bfe90caa8ca81dff61a2246540effb0b11232a077fc8588919503bfeb2c448ca81dff60e2246540effac711232a077fd5388919503bff444448ca81dff9562246540 else 0x81dff6c5834a540effb0cb9a52a077fd855cd29503bfeb2ae694a81dff6e1634a540effb6eb1a52a077fd8758d29503bfedaac694a81dff615634a540effaeab1a52a077fdb854d29503bfe5c2a694a81dff6dd534a540effb0ea9a52a077fdb654d29503bfec32a694a81dff5d9534a540effb0aa9a52a077fd6554d29503bfed92a694a81dff6c5534a540eff962a9a52a077febb54d29503bfe5ab0494a81dff615824a540effacac1252a077fd8360929503bfea9b0494a81dff615624a540effb06b1252a077fd5358929503bfec32a494a81dff615524a540effacaa9252a077fd8354929503bfea9aa494a81dff619324a540effb0a99252a077fc854c929503bfeb2a6494a81dff61ca14a540effb0a50a52a077fd8760529503bfebb30294a81dff2d5814a540effb0ac0a52a077fd7560529503bfeb2b0294a81dff60d814a540effae6c0a52a077fd6360529503bfea9b0294a81dff609814a540effac4c0a52a077fd5260529503bfe9930294a81dff54c814a540effb0cb8a52a077fd855c529503bfeb2ae294a81dff60d714a540effac6b8a52a077fd535c529503bfec3ac294a81dff615614a540effaeab0a52a077fd8358529503bfeb9ac294a81dff54d614a540effb0ea8a52a077fd8654529503bfebb2a294a81dff615514a540effb06a8a52a077fd7354529503bfeb1aa294a81dff54d514a540effb04a8a52a077fd6254529503bfea92a294a81dff4c9514a540effb0628a52a077fd874c529503bfec326294a81dff5d9314a540effb0a98a52a077fc854c529503bfebaa6294a81dff595314a540effb0c90a52a077fd8548529503bfe42a4294a81dff595214a540effb0690a52a077fd5348529503bfebad1094a81dff5ce884a540effaa744252a077fd52a2129503bfe9951094a81dff286884a540effae344252a077fd51a2129503bfe98d1094a81dff486884a540effb0d2aa52a077fd8395529503bfeb1caa94a81dff60a554a540effac52aa52a077fd3295529503bfec0caa94a81dff4c6554a540effa432aa52a077fd8784529503bfec2c2294a81dff60e114a540effaa708a52a077fe8884529503bfedb30e8ca81dff6d58746540effb66c3a32a077fdb261d19503bfed8b0e8ca81dffaed8746540effb6ec2a32a077fd8761519503bfedb30a8ca81dff5d98546540effb66c2a32a077fdb261519503bfed8b0a8ca81dff6197546540effb0eb2a32a077fd8559519503bfedbb068ca81dff61d8346540effb6cc1a32a077fd7660d19503bfedab068ca81dff6158346540effaeac1a32a077fd6560d19503bfed93068ca81dff6c58346540effb70b9a32a077fcb85cd19503bfedb2e68ca81dff6197346540effb6ab9a32a077fd855cd19503bfeb2ae68ca81dff6c97346540effb62b9a32a077febb) else (if i<3 then 0xab9ad2a077fdb25cd69503bfed8ae6b4a81dffaed735a540effb70a9ad2a077fdb754d69503bfec3aa6b4a81dff615535a540effb64a9ad2a077fcb254d69503bfed8aa6b4a81dffaed535a540effb6ec12d2a077fdb560969503bfe5ab04b4a81dff5d5825a540effb66c12d2a077fd7360969503bfea9b04b4a81dffaed825a540effb0ab92d2a077fd835c969503bfea9ae4b4a81dff6e1525a540effb6ea92d2a077fd8754969503bfec2aa4b4a81dff6cd525a540effb06a92d2a077fd7354969503bfea9aa4b4a81dff609525a540effb62a92d2a077febb54969503bfec18a4b4a81dff6e1325a540effb6e992d2a077fd874c969503bfedaa64b4a81dff2d5325a540effb0a992d2a077fd754c969503bfec1264b4a81dff549325a540effb62992d2a077febb4c969503bfed9ae2b4a81dff54d715a540effaa4b8ad2a077fd325c569503bfed9aa2b4a81dff5cd515a540effaa6a8ad2a077fdb254569503bfeb92a2b4a81dff549515a540effa64a8ad2a077fdb74c569503bfedaa62b4a81dff5d5315a540effb6498ad2a077fd724c569503bfea9262b4a81dff149315a540effb6a90ad2a077fd7548569503bfed9a42b4a81dff5cd215a540effaa690ad2a077fd5248569503bfe99242b4a81dff60e555a540effb052aad2a077fd3295569503bfe98caab4a81dff486555a540effb0b112d2a077fd8388969503bfea9c44b4a81dff546225a540effa63112d2a077fe5588969503bfedbb029ca81dff6d9814e540effaecc0a72a077fdb260539503bfe593029ca81dff549814e540effd76c0a72a077fd5220539503bfedc2e29ca81dff6d9714e540effacab8a72a077fdb25c539503bfeb12e29ca81dff549714e540effb02b8a72a077fd8758539503bfebaac29ca81dff5c9614e540effaa4b0a72a077fd7654539503bfed92a29ca81dff609514e540effae4a8a72a077fd6254539503bfec0aa29ca81dff608514e540effb6c90a72a077fd7648539503bfedaa429ca81dff2d5214e540effb0a90a72a077fd7548539503bfeb2a429ca81dff605214e540effae290a72a077fd5148539503bff5da429ca81dff614214e540effb0f08a72a077fd8584539503bfec14229ca81dff20a114e540effae508a72a077fd5284539503bff444229ca81dff88a114e540eff974c3a52a077fcb161d29503bfec314a94a81dff6dd854a540effb0ec2a52a077fdb661529503bfebb30a94a81dff6cd854a540effb64c2a52a077fdb161529503bfe542ea94a81dff619754a540effb70b2a52a077fdb759529503bfec3aca94a81dff615654a540effb66b2a52a077fdb259529503bfedbb0694a81dff61d834a540effb6cc1a52a077fd7660d29503bfedab0694a81dff615834a540effaeac1a52a077fd6560d29503bfed930694a else 0xe1b646c72d00290e40683877cc0290e4068386d91b180521c80d070d4940521c80d07080290e4068384db9bb69f6c66d5bda6bb43f66f6cadd90fb15b6186c0ad7c9ae775bbeb46d62babbf564ea98d4cfa8db4fd69d4d347a5f74a66910d1a9a2bb43ee84cd0379f7f3d76772ce839c4336a6682cc8d982b2e7657cca5593e7264648cc8cd910320263d3c75b8dc719ae2eec54f8a07128621fc3b186470aae12fc1e7833704e606bc0337fa2fd65f70be697be2f58de54bc31779eed5dd85ba937436e635c8ab8876ff2de05b6eb64f6b82d525a5db41766e6cbed94cb2376352c51d867b0415fbebd9d782aeb95c82b82d6c9ad0558c2afa55b8aaf954d6a7cd4c8a9195142a04d3c2a7234dae997d2fea5b14a729305219a3bb465a8b2d134a20742f28405039a0113f067bd4f499e313bf67664eb19d2d39967254e0e9bd136de6c8cd6b9a493426671cca798c130be5ff4bd8970d2dae5924afe95b12a4652aca2f941327364c3493f923323ce450c870907f200e3e3c78b8e9f1c2236bc69b8cbf188e2f3c5ab8af51526286c4dc89571192219c3f787610da619142db8529093610341b482f104f207ac0b9812701e2018bfd47f30fd19f7a3ea27cccf87dee6bd7b7a68f389e3d3c2877d8ee95daf3b1775b6ea51d2c3a067394e639ca9392171cae279c36b83c7000df3dbc9b74c6e20db25b3bb6256bbcd6b5ab8b5406a1ed3a5a5c349268c2d0959f4b3a266b6cc7d96c329164aac80d8d8b16a6272c3c985b307a607cbfb17cd2f5e5e2ebae97342e0b5b9eb6216a0ad1059beb28d6392c575878b0595fdabca5732adcd59bab1c55c0aae9544aa585422a7294bc29475200a39544f287850629fd53d727884eae9cc5385a6f04d529a0d31e25df4b7296212aba51049d4928d228a41547de8ecd1c6a35c46568b9114ea26c443487a50dc219242c284ed07fa0e4415081dd023200a3f9c7df0fab1f253de87ae0f439e563c4a77d0ed69d713a3e738ce489c5538066ef0dba9b2e35b86a54d271a1d33d866eccbf994e31f862a8c3197fb2f7e5de0b9e16ea2d305944b0515d92b5055b0a9d94f4299c52a0a41144628404f649c91361268c4c289671292248047e48de917622a0447c87190b220ec41148048fc21f223d287870ec71d1639106fe8db61af434cc6810cc618fe31386090bd617342d785910adb153e298c50889ca131c251c48588cf1126215c40d87df0f461d4438506b80ce2187c2ec05910a94140c263847508460f701ca8343060e0b0013c823d040207140bf012c01ca027803100310001dff6d5875a540effb66c3ad2a077fdb261d69503bff5db0eb4a81dff6dd855a540effb66c2ad2a077fdb261569503bfedbb06b4a81dff6d5835a540effaeac1ad2a077fdb260d69503bfedc2e6b4a81dff6d5735a540effb)) else (if i<6 then (if i<5 then 0x8611a1c8381902fbc5280748223ba8720cc1c1ee543801c30bc5202b0c2864ef90c32194390660e14eaa194390660e1421a1c833070efa361ee743801c308d0e41c44217c88650e41983844390660e2361ee54328720cc1c2007006871db100386130c77c80290e41980c41727210ca1c833070c7210ca1c833070a10d0ca1c8330705ca3639c84328720cc1c28b93908650e4198388d8e7210ca1c833070a2f10ca1c838714db0f738bc4328720e1b61ee61788650e4198382e4c2f10ca1c8386d87b985e2194390660e0b930c71788650e4198382e4d6d90e0bc36c01c03190e00705ef1488643582f352443801c17bc522194390660e1c52a1c00e0bde2905c9f44328720cc1cb8a73ba8650e4198387145c9cc32194390660e5c533b630c8650e4198397151b0294a1c00e0bde2b2029684328720cc1cb8a64328720cc1c38a51728650e4198397151b1d0e41cb8a8841498e30c7439072e29a900e018ced8d4a1c839714039803a1c78a130801c179863524014872030b9832501487203419200a4390185ca36832643801c090e1081231c343801c090d0ca1c833048e2950e00702431727d10ca1c833048c2e4eea1943906609190e007024f149084090838a194390660914d4a1c8330490c94eaa1943906609145c8434328720cc1246c7a406390e01200e018d4810e007024638b4810e007024f14c71803803024300e048c318e2003833071e2db62803833072db10ea803833072db1401c198396d883d801c198396d8a3da0c9df8396d8019a0c80a8396d883da0cc1c78b6d805187b4198396d80514658030390660d1c530cb0060720cc1a28cb0060720cc1a38a61960720cc1a014618c32c0e419834714051865a1283306805141681c833068d480330030390660d101681c83306801941681c833068e280330030390660d101681c83306805160cbc5015070411416a1283306805141200303906607141201c83303801941201c8330390c80330240060720cc0e28240390660700a2824039066073c530c028e2240181c833018e2984480303906603144481c8330190c80330890060720cc0628890060720cc0628890390660300328890060720cc062803038618030822803038619e280628820246180300a29df3aa8650e419838714e77d0ca1c833070e298efa194390660e1a931c73be7210ca1c833070c77d0ca1c833071e298639df43284a0cc1c30c61968650d003038714c0b50ca1a00607041181221941c00c0e08230894328180181c29a93e88650e4198386d8e6a4b42194390660e18e39a94328720cc1c46c63528650e419838618c6a45e2194390660e1b639a943284a0cc1c28f643200d0e3b6104604886507003038208c2250ca06006070a7d00521c80d070a1c40521c80d070a6a50e40683886405182180a43901a0 else 0xe512407a0ca1981c01cc2480381e833038a3260f419181e832203e180323c5b6d008c7750c81f8321d8649b680480c010d0c81f80453048640fc190c16da011ceaa1903f0663b5b680470868660c87636c07e011c0f8604436da01146801f8ec886db402303f0ec6d910a0e03f008f1d8efdb64428380fc023a1903c02c0fdb680461788640f1b60170080f9c6c21903cf16db0860170080fa44921903d6d805c0203e70dd00910a0e05c51968640fc19896324c32d0c81f8967146c990c81f896110db0d930cb43207e0cc4b283f03f12cdb22141c603f12d10a0e0ae53708640fc19870325229cdc21903f0661c14dc21903f0661c14dc21903f0661c14dc01f870884807e1c22141c110a0b80fa453530646c981721903f06480b80fc191b243048640f82d832505c8640fc19202e03e71510c19282e03e6d910c1941c603e0b510a0e05c505c8640f41901607cc0b90c81e03f064059823a1903cf140581f832a18e2490c81e832838059802a6280506480580f8c948b084a0580f83e842402c07c1f421201603f08460580fc2105c403f0842b8c0f83e84211082240381e833008a2240381e833008a2260ca1900e07e01184480703d064db402308900e07a0cc02280711207910a0e80461927550cc190f8714c3246807c38a884a77c379a94426390706938d843201c0f3c5452218e2490c80703c8384318ef81e304864832d0ca4b83207ce2981741903e864c1140b01f304884349444a1900e0790114d49f44330643d1b6a3073525a10ca62833460c71cd483f44346107150ca1a00e07a8c08630bc43201c0f1b646d46043204921900e07a8c20e10c74329da0c81f76d460c1202401603f4611082e288943201c0f518404600a07e011c548b460c0140fc02a30400a07e01518201fa308850702e280503f00a8c1023a41121c08e24388843d8c2387b1219006871db102387b38a77c88701506a1a1c8381902fbc5282a48223ba8720cc1c1ee5438884350d0e02a0d4f14886401a1c76c41727550ca1c833070c10d0ca1c8390d87b9adb1b64390721b02a052743803c313c525204328720cc1c38a601e90442e4eea194390660e190e00f0c43a406390ca1c833070c7550ca1c833070a10d0e4198388d87b990e00f0c4301e00d0e3b6221c01e13870842718e180f48221727d10ca1c833070c8700784e18714328720cc1c38a617210d0ca1c833070e2a36421c01e138603c01a1c390401e138c71c52219439070ef8f786c68420fa1b0c38a194390721b0f730b93aa8650e4198390d8e8640503e31d0d8a870078311c210626390c9a92a1c01e0c468650e419838443803c18a3621f44328720cc1c17261727750ca1c833070c8720e4210524a406390ca1c8330711b1d0e00f062f1480281898e432401e00d0e0c0783131c6a4887003) else (if i<7 then 0x40182d182e433066209c5283105a88461040182d78a405c8660cc4124b83040bc16bc50540a4e0b90cc1988240820461cc0284250820461cc02842504b1061cc02842502a0461cc02842504a1040ac39805084c0942081578b0e4c3402842830c0561cc02842508200c04bc520bc4321060cc09281500602462f10c841833024a2f10c841833024b2e0c102f00e025e299901820240240394d4968483104c727531a94329060cc4130c635286509419882535209520841472809109cd48bc4328260c84131860e286520c06882630c5a120c414ea530c05120c068826a4c6181700a483018209a9398604a0591c982404884e6190ca4180d104a8880186076c444400c303b621dd43288a0cc2236c644400c303b6221940c09cc10792a19445066113c5b6c6006180c11df2005445009e2c192a2200612ddb1111003096343288a1104436c500612c415d0ca22833088a15d0ca22833088e29ae29c544400e113b6004737086511419844537086511419844537086511419844537086511419844f14c0b90ca22833088a8880182d78a405c86511419844505c86511419844505c86511419844608c88a1102e76c00c011802a2283300888880180919dd43288a0cc092a22006025e2910c82b01230e28651141981253aa865114198125086865114198126d8c61911003012ed8af151100930c00c0118c3222006024800c0498230c400a88a01419207b00a88a0142238a60e20151140284450cc0151140284477cc61802c02014439001511402844714c01511402844f14d49802a22805088860805c02014443287841ec64c45432403d06440a83508350640bef1480a83508eea5d8331a86c94372210d4343201c353c5202a03eed860640f0c918c93aa8653a4198aa605410841f4150421843833109228d92db636c1a82102a0526442108fa20e221900e109e2900786278a3a408643dc190c4715229c0786210c93ba8652ec198c460dc03c310c3506284231927550ca55833188c10d0ca42833188a03c03862180f03eed863246827489d084a3410ca6a89c7146c9864843485138e2c21303e84303860fa10c0e183f0f677c64a45843038e0f8fa42181c407e9aa10c0e20c907e95610c0e286e0630860706928318426a607069285a06308607069287b0dc91610c0e1b260630860706921f44e81ba10c0e28c93ba97610c0e286a0620a610c0e284206308607043283178b08607069281f843038349018c2181c0b880c6109a981c1a4a07b0d21900e400e07a0cc1a204303d0660d1df00e603d0640985f201e4428380986928bc03d064db43600e617807a0c9b686c04cc2f00f43644283809986c01e83371614807300703d066e282910c600e07a0cdc5053218c3600f419b8b0a409980f5c5052884c720e90c712401c0f41981c512407a0cc0e else 0x48211c49051087b18470f6208e1ece29df22410541a869051086a1a410541a9e2912086278b1d489043147519d54831063a91208628ea348203c270d2080f09c30e286520c19882714c9040784e180f48272101100784e31c7148904078311a4101e0c4686520c1988244820c610829224101e0c5e2900a03146e6390c952080f062301e0c4c71a9224100e18469040386178a40561851ba193be53aa86520c19882548201c308d0ca41833104886520c19882400e184c31df21c84329060cc4129c84831053a90e421948306620952080705ef1489040382f78a44329060cc4138a55e86190ca418320bee29d2080705ef159014b42418837153a950ca41833104e2941882fb8a8841498e30c75e890417dc535201c031d2080705ef14801c17986352430c906034194ea548201c090d2080702434329060cc1238a548201c093c524210248dc61c50ca41833048a7550ca41833048b480c724102401c031a9002f00e049e298e301500e048601c0918631c4007104e44022057433066209c580460ae8660cc4138b008c15d0cc19883008a10)))
def f3077uL33 : PackingT := (477,4,7,15,f3077uL33F)
def f3077uH0_33F (i : Nat) : Nat := (if i<1 then 0x516014580516608000517802b000d1c002d0003c07b80516800da0097408f18009e03700516c0b3f813a0145981fa00599025e8010b805e0145e016c60ad20199400f301b5a09058070c04bc82bba08818266e0700008e0145d89f40145f0275cc7c6005d4022b82a00145d8113007f005160145805168028005160145b00bb20b46809480470819a0145805178095805160145c81e9a065805160145d00c340b3500bf6037a8161c09be8291c008f01f7409a981afc0a16010a60087009b20589020a2c8dd81e48072e801ea053b0075a062a0a11e09e38031c0876002ec09ea02cbe0ad80045e0b0b00900145f80680055805160145a00ff409f805170076e028be055581ab605400516007ce01a100ac80516a02cd811a806de828fc0774820e0145a80ae6059100ce0145881f16075d8289009600517807100516a06f781bec04e005160145d02180145f822ae05a180da0145805164071805160145d81e00145805160145805176027805174081d8175404ca00cc403e081f5c09730145405298056406500516a00b005166093005172c89c023e0145b023a0145c82512083400b64067900c640002018f0090a81b00145b8245803c580d8c070c00a20145d0135400f8051601459826d405cf00bc01458810801458051780531017d0051e00f5802498060e06a00516014580517a038005170011b82abc0502024fa00a90054a0a000517c039e8182e039782160145d82760145f00f68019005160145a01780145b02a80145805160145a00c8e0b4f816b200380516e040805160145f80d760a948a03208a00516014590080e079f0287e010202c8609f302ac204b20268208c1804d6019c0086c08120254802e382526057982122045d029740483025ba01ce812b4077e8249e01b0807b00031024b80aff826240a3002a3a02d4819160a51007f6052480d4c0a4e029b804f80516e07500078a054d8247404c00516c0840051780b1b01ed00760051700aba02252009e31f5c05d8051600452ba2c014580516828480516e0a0982728041880c4014580516400d3022e0145c811e0145805160145805168c7be029c0145f021a0145b0298014580516014580516c016005162006c0024014580517a06e680044088881c9e09820180c0571b1ecc08de0013c05c10098c005c0270405608032c0b04806e608c8001840ae201d3408b280514016801242044001a7a074302bda078c814200008082a07000003e00038040006008381a310088c1c000000c220b1501808000100c00060000422010d804160c0680c120200010000e038100201068040005008082200100202a000780400070500806000d80018080082010130002002050000032001705c04000880c00000001008080000404000201800000e80828000101c0a18020280403028700001 else 0x2049d80e8e041280ef8063400ea404388128e056f01cec07ad80a960042816fc0610829fe018a021f807330235603b5019de02c7018720825804a401dd00a60145801ba0145e81370034f8085a013e31fea043381b3403e90188203cf003b4069682c4405ec0052e01a805162085005168012002b0604658028608e381006032f8014014580517c080f0089803f481f86089f809ce06b082d5804f080380145e0123402ae0007c05fa8264a07fb02a76068c80a5a007000c14020b007c0064f80e2002300)
def f3077uH0_33 (h : Nat) : Option (Nat × Nat) := lookupWord 125 480 9 18 10 4 f3077uH0_33F h
def f3077uL34F (i : Nat) : Nat := (if i<9 then (if i<4 then (if i<2 then (if i<1 then 0x84569503bbb2ac22b4a81df58ce115a540efcc4508ad2a055fdb720539502b7edb0429ca815df6d4214e540aff36010a72a066fda79993950337f554cc9ca81d3f9de664e540cfe97508a72a067f5a7845395033fb554229ca81cfda22114e540ebecef08a72a076f66684539503bbb2ac229ca81df988a114e5408ff974c3a52a055fdb721529502b7edb10a94a815f76cc854a540afdb6442a52a057f5b121529502bfcd810a94a811ff2e9634a5408ff974a9a52a055fdb7205295023fe5d2a294a811ff2e9314a540efb2a698252a077d9314c1295023fedc55494a811ff6d6aa4a5408ffb6355252a047fcbaa21295031fe5d51094a818ff69e884a540e77aa944252a073bd41a21295039fc9851094a818ffaaa884a540cbfb4d3ba52a075bd549dd29503adea0cee94a81d7e4c2774a540cbfd553ba52a071fe889dd2950337ed44cc94a819bf69e664a540ed7aa933252a076bd4199929503b7c984cc94a819bfaaa664a540e5fd1133252a074fe77999295023fe5d4aa94a81dcf552554a540cef9752aa52a0677da695529503b9ea0caa94a81dde4c2554a540cefd552aa52a0737e8895529503abf3bcaa94a81d9f99a554a540e7bd1119a52a075de778cd29503b6f3346694a81dd7956334a540cfdb5111252a067eda688929503bd6aa44494a81deb506224a540efd26111252a073ee8888929503b773344494a81ddb956224a540ef9c6711252a047fcba84529503bdaa0c2294a819fd2ea114a540cfeb5108a52a067f5a784529503bdaaa42294a81dfc4c2114a540cfed5508a52a073f68884529503afb3bc2294a81dbd99a114a540eeecab08a52a077d63384529503bf31142294a8157f6dc8546540adfb6c42a32a057ddb321519502bf6d910a8ca815fd6c48546540aff36042a32a056fdb6149195031fed45108ca818ff2ea8846540c7fb4f44232a063fda3a21195031fed15108ca818ffaaa8846540cbfb513ba32a065fda69dd195032fed1cee8ca8197f68a7746540cbfd553ba32a071fe889dd1950337ed44cc8ca819bf69e6646540cdfb4b33232a066fda39991950337ed14cc8ca81cbfa226646540e9fcef33232a0677cba955195033bed44aa8ca819df68e5546540cefb452aa32a0677eaa955195039bf444aa8ca81d5f9de5546540ecfccd2aa32a073de888cd19503aef3bc668ca81db799a3346540eebcab19a32a067eda2889195033f65d4448ca819fb6a22246540cfdb4d11232a067eda5889195033f6d1c448ca819fbaaa2246540e7dd1111232a075ee7788919503b77334448ca81ddb9562246540ef9c6711232a067f5a8845195033fad3c228ca819fd6961146540cfeb4708a32a067f5a2845195039fb444228ca81d7d9de1146540eeecab08a32a077d63384519503bf3114228ca811ef6d2aa4e540 else 0x81cff2ca8846540e7fae544232a073fd62a21195039fea95108ca81cff14a8846540e7fa6544232a073fd71a21195039fea8d108ca81cff4c68846540e7fa4344232a075fd869dd19503afec2cee8ca81d7f5967746540ebfb073ba32a075fd639dd19503afea9cee8ca81d7f60a7746540ebfac53ba32a075fd529dd19503afe994ee8ca81d7f6067746540ebfaa33ba32a075fd319dd19503afe90cee8ca81d7fa227746540edfb0f33232a076fd8599919503b7ebaccc8ca81dbf60e6646540edfae733232a076fd5399919503b7ec14cc8ca81dbf5ca6646540edfaa533232a076fc5299919503b7e994cc8ca819ff6a25546540eefb0b2aa32a0777d65955195033fed1caa8ca81ddf54e5546540cffb452aa32a0777d5295519503bbea8caa8ca819ffaaa5546540e7fd112aa32a076fe6695519503bbe5c4aa8ca81ddf61e5546540eefb0d2aa32a0777d7695519503bbec1caa8ca81ddf5ce5546540eefac72aa32a0777cb295519503bbec14aa8ca81ddf20a5546540eefae52aa32a0777d6295519503bbe994aa8ca81ddf6065546540eefae32aa32a0777d3195519503bbe90caa8ca81ddfa225546540efbb0f19a32a077dd868cd19503beebb4668ca81df76163346540efb90b19a32a077dd758cd19503beeb2c668ca81df760a3346540efb90519a32a077dd728cd19503beeb14668ca81df754a3346540efb8a519a32a077dd818cd19503beeb8c668ca81df75463346540efba4319a32a077de888cd19503bef2ac668ca819ff6a22246540cffb4d11232a067fda5889195033fed1c448ca81dfb60a2246540efdac511232a077ed5288919503bf6994448ca81dfb4862246540cffd5511232a073fe8888919503b7f334448ca81ddf9562246540efbc6711232a077ecb888919503bf6c3c448ca81dfb61a2246540efdaed11232a077ecb588919503bf6c2c448ca81dfb2162246540efdaeb11232a077ed6588919503bf6c1c448ca81dfb5ce2246540efdac711232a077ed5388919503bf6c0c448ca81dfb5c62246540efdaa311232a077ed3188919503bf7444448ca81dfb9562246540efeb0f08a32a077f58584519503bfa42c228ca81dfd5d61146540efeb0708a32a077f57384519503bfaa9c228ca81dfd60a1146540efe90508a32a077f57284519503bfaa94228ca81dfd14a1146540efea6508a32a077f68884519503bfb2ac228ca81dfd88a1146540e9fac73bad2a075bd419dd695032ff554eeb4a81c7fa22775a540cef9752aad2a0767d6395569503b9ea0caab4a819dfaaa555a540e6fd112aad2a0757e77955695039ef44466b4a81d779de335a540eebcab19ad2a067ecba88969503b76b1c44b4a81deb506225a540cfdd55112d2a073ee8888969503af73bc44b4a81ddb956225a540ef9c67112d2a075f677) else (if i<3 then 0xab2a32a057febb595195033fec3b468ca819ff619a346540cffaecd1a32a067fd8568d195033fe42b468ca819ff5d5a346540cffacad1a32a057febb60d19502bfedc2e68ca81d7f61d7346540affd76b9a32a057fdb858d19502bfedbac68ca81dbf6196346540efbb06b1a32a057febb58d19502bfedc2a68ca815ff6dd5346540affb6ca9a32a0777d8554d19503beec1aa68ca81df75cd5346540affd76a9a32a067fd87689195033fec33448ca819ff5d9a246540cffb0ad1232a067fc85689195033febab448ca819ff595a246540cffb74c1232a067fda8609195039fec3b048ca819ff6958246540cffb46c1232a073fd83609195033fed13048ca815ffaed8246540affb6a41232a067fda520919502bfed99048ca819ff68c8246540affb6241232a057fdb85c9195033fed42e48ca819ff6997246540cffb4ab9232a067fda35c919503afeb9ae48ca815ff6e16246540cffb50b1232a057fdb758919503b7ebb2c48ca819ff6956246540edfacab1232a067fda358919503b7eb1ac48ca819ff6896246540efdb04b1232a057febb589195033fedd2a48ca815ff6e15246540cffb50a9232a057fdb754919503afe5baa48ca815ff6d95246540cffb4ca9232a0777d75549195033fed1aa48ca81ddf54d5246540cffb44a9232a077ed8254919503bf6b92a48ca815ffaed5246540affb7029232a067fda814919502bfedb0a48ca819ff6985246540affb6629232a067fda314919502bfed88a48ca815ff6e13246540affb6e99232a057fdb64c919502bfedaa648ca81df75cd3246540efdb0499232a057febb4c9195033fed3b028ca819ff6958146540cffb46c0a32a067fda2605195039fec13028ca815ffaed8146540affb70b8a32a067fda85c519503afec3ae28ca819ff6957146540cffb46b8a32a067fda25c519503afeb92e28ca815ffaed7146540affb70a8a32a067fda854519502bfedbaa28ca819ff68d5146540cffb44a8a32a0777d5254519503bfac0aa28ca81dfd5c55146540affd76a8a32a057fdb84c519502bfedba628ca815ff6d53146540efba6498a32a077f5814c519503bfaa8a628ca815ffaed3146540affb7090a32a067fda848519502bfedba428ca815ff6d52146540cffb4a90a32a057fdb3485195033fed1a428ca81dfd5c52146540efea6290a32a057febb485195033fec3d548ca819ff616aa46540cff90b55232a067fd75aa9195033fec15548ca819ff20aaa46540cffae555232a067fd52aa9195033fe295548ca819ff69e8846540e7fb0f44232a073fd85a21195033fed1d108ca81cff60e8846540cffb4544232a073fd82a21195039fec0d108ca819ffaaa8846540e7faed44232a073fcb5a21195039febad108ca81cff5968846540e7fae744232a073fd63a21195039fea9d108ca else 0x9503afe544ee94a81d7f61a774a540ebfb0b3ba52a075fd659dd29503afec1cee94a81d7f58e774a540ebfaa73ba52a075fca19dd29503afec0cee94a81d7f206774a540ebfac33ba52a075fd519dd29503afe98cee94a81d7fa22774a540edfb0f33252a076fca599929503b7ec2ccc94a81dbf5d6664a540edfb0733252a076fd7399929503b7ea9ccc94a81dbf60a664a540edfaa533252a076fd3299929503b7ec0ccc94a81dbf5c6664a540edfaa333252a076fd3199929503b7e90ccc94a819ff69a554a540eefb0b2aa52a0777d6595529503bbea9caa94a81ddf54a554a540eefaa32aa52a077bd4195529503bfc984aa94a819ffaaa554a540e7fd112aa52a076fe6695529503bbe5d4aa94a81ddf2e2554a540eef9512aa52a0777d8795529503bbec34aa94a81ddf5da554a540eefb072aa52a0777d7395529503bbeb1caa94a81ddf60a554a540eefac52aa52a0777d3295529503bbe58caa94a81ddf286554a540eefb032aa52a0777c8195529503bbeb8caa94a81ddf586554a540eefa632aa52a0777d2195529503bbf444aa94a81df761e334a540efbb0d19a52a077dd768cd29503beec2c6694a81df7216334a540efbaeb19a52a077dd658cd29503beec146694a81df758a334a540efbaa519a52a077dd818cd29503bee40c6694a81df75c6334a540efbac319a52a077dd518cd29503bee28c6694a81df7486334a540efbd1119a52a077de558cd29503bf6c344494a81dfb616224a540efd90b11252a077ed6588929503bf6c1c4494a81dfb58e224a540efdaa711252a077ed8188929503bf640c4494a81dfb586224a540efdaa311252a077ec5188929503bf698c4494a81dfba22224a540efdcab11252a067fda8845295033fed3c2294a81def552114a540efeb0308a52a077f57184529503bfaa8c2294a81dfd4c6114a540efea4308a52a077f930845295033ff5542294a81cffa22114a540ebfcef08a52a0777e5584529503bef19c2294a81dfb88a114a540efe97508a52a077f4b884529503bfa5442294a81dfd61e114a540efeb0d08a52a077f57684529503bfa5ac2294a81dfd296114a540efeb0b08a52a077f48584529503bfabac2294a81dfd596114a540efeb0708a52a077f57384529503bfab1c2294a81dfd54e114a540efeb0508a52a077f56284529503bfaa942294a81dfd4ca114a540efed1108a52a077f655845295033fe5d30e8ca819ff6a18746540affd76c3a32a067fda761919502bfedc2ec8ca819ff6a17646540ebfb0ebb232a067fd76695195033fedd30a8ca819ff6a18546540e7fb0ec2a32a057febb61519502bfed990a8ca815ff6c88546540affb6242a32a057fdb85d5195033fed42ea8ca81d7f61d7546540cffb50b2a32a057fdb759519503b7ec32ca8ca81dbf5d96546540eefb)) else (if i<6 then (if i<5 then 0xf6e1524a540affb6ca9252a067fda654929503bdeaa2a494a81ddf54d524a540efdb04a9252a077ed6254929502bff5daa494a815ff6e1324a540affb6c99252a057fdb54c929503bf6c126494a81dfb549324a540affd7699252a057fdb828529502bfedb94294a815ff6d4a14a540cffb74c0a52a067fda8605295033fed3b0294a81dbf2d9814a540e7fb0cc0a52a077bd54605295039fec130294a81dfd285814a540affd76c0a52a057fdb7205295033fed390294a815ff6d4814a540ef7aa840a52a057fdb320529502bfed910294a815ff6e1714a540cffb50b8a52a075fd875c529503afebb2e294a81def551714a540affd76b8a52a057fdb8585295033fed42c294a815ff6dd614a540cffb4eb0a52a077bd5458529503b7eb12c294a81dfd605614a540cffb74a8a52a057fdb8545295033fed42a294a815ff6d9514a540eefacaa8a52a077bdb454529503bdeaa2a294a81ddf549514a540efeb02a8a52a077f57154529502bff5daa294a815ff6e0514a540cffb5028a52a057fdb314529502bfed90a294a81def61d414a540ef7b0ca0a52a077bd7650529503bdec2a8294a81def215414a540ef7aeaa0a52a077bd6550529503bdec128294a81def589414a540ef7aa4a0a52a077bd8150529503bdeb8a8294a81def545414a540affb7098a52a057fdb74c529502bfedb26294a815ff6d5314a540efbac698a52a077dd324c529503bfac0a6294a815ffaed314a540affb7090a52a067fda848529502bfedaa4294a81def551214a540affb6690a52a077ed6248529503bf69924294a81def505214a540efea6290a52a057febb48529503bfcc3a6094a81dfe619304a540eff2ec98252a077f9854c129503bfc42a6094a81dfe5d5304a540eff2ca98252a077f9824c129503bfcb126094a81dfe549304a540eff30298252a077f8814c129503bfcb8a6094a81dfe585304a540eff2a298252a077f8514c129503bfc90a6094a819ff61eaa4a540cffb0d55252a067fd76aa9295033fec2d5494a819ff216aa4a540cffaeb55252a067fd65aa9295033fec155494a819ff58aaa4a540cffaa555252a067fd81aa9295033fe40d5494a819ff5c6aa4a540cffac355252a067fd51aa9295033fe28d5494a819ff486aa4a540cffb4f44252a073fd87a21295039fec2d1094a81def552884a540e7fb0744252a073fd82a21295039fec0d1094a81def506884a540eff26144252a067feaaa21295039fe5d51094a81cff5da884a540e7f96b44252a073fca5a21295039febad1094a81cff596884a540e7fae744252a073fd63a21295039fea9d1094a81cff58a884a540e7faa544252a073fd32a21295039fe58d1094a81cff286884a540e7fae344252a073fd61a21295039fea8d1094a81cff146884a540e7fa6344252a073fd21a212 else 0xad2a077de558cd69503b7eb1c44b4a81dfb60a225a540efdaa5112d2a077ed3288969503bdea0c44b4a81dfb486225a540cffd55112d2a073fe8888969503bbf2ac44b4a81df78ce225a540efdb0f112d2a077ecb588969503bf6c2c44b4a81dfb5d6225a540efdb07112d2a077ed7388969503bf6a9c44b4a81dfb5c6225a540efdaa3112d2a077ed3188969503bf72ac44b4a81dfd5d6115a540efeae708ad2a077f55384569503bfab9422b4a81dfd54a115a540efe8a508ad2a077f53284569503bfb2ac22b4a81dfd88a115a540cffb74c0a72a067fda760539503b7e5b3029ca815ffaed814e540affb6e40a72a067fda720539502bfed91029ca815ff6e1714e540ebfb0eb8a72a075fd765c539502bff5dae29ca815ff6e1614e540affb6eb0a72a067fda758539503b7eb12c29ca81dfd605614e540cffb74a8a72a077f58154539503bfab8aa29ca815ffaed514e540affb6428a72a067fdba48539502bfedaa429ca81dfd5c5214e540affd7690a72a057fdb5085395033febb5549ca819ff606aa4e540cff90355272a067fd71aa9395033feb0d549ca819ff546aa4e540cff8a355272a067fd21aa9395033fe10d549ca81dbf5ca664e540edfaa533272a076fc5299939503b7ec0ccc9ca81dbf5c6664e540edfaa333272a076fd21999395033fed3c229ca81dfd606114e540efeae308a72a077f55184539503bfa90c229ca819ffaaa114e540ebfcef08a72a077f4b884539503bfac3c229ca81dfd61a114e540efeaed08a72a077f4b584539503bfac2c229ca81dfd216114e540efeaeb08a72a077f56584539503bfa594229ca81dfd60a114e540efe90508a72a077f57284539503bfab14229ca81dfd54a114e540efe8a508a72a077f68884539503bfb2ac229ca81dfd88a114e540affb6e54252a057fdb52a129502bfed895094a819ff2e9874a540affd76c3a52a067fda761929502bfedc2ec94a819ff6a1764a540ebfb0ebb252a057fdb829529502bfedb14a94a815ff6c4a54a540cffb74c2a52a073fd8761529502bff5db0a94a815ff6cc854a540affb6442a52a057fdb121529503afec3aea94a819ff699754a540affb6eb2a52a076fd8659529503b7ebb2ca94a81ddf615654a540affd76b2a52a077bd8755129503bdec32a894a81def5d9544a540ef7b0aaa252a077bd6555129502bff5db0694a815ff6e1734a540ebfb0eb9a52a057febb5cd29502bfedbac694a81dbf619634a540efbb06b1a52a057febb58d29502bfedc2a694a815ff6dd534a540affb6ca9a52a0777d8554d29503beec1aa694a81df75cd534a540affd76a9a52a077bd54609295039fec1b0494a815ffaed824a540affb70b1252a067fda858929503b7eb2ac494a81def551624a540edfac6b1252a077ed8258929502bff5dac494a815f) else (if i<7 then 0x5e9a2efb174f0b9305bf42db316b60b49459222c1e15d58ace055cc2ac015318a89c53c029ba14ae8a400515c285113fa09dd84e3226b1132a097b04b08251c1265091304786235b1184889d443ac2158106d081183fa61f810f9d07c503ddc1ec80f46078e83c121dd80ed3875d83a481cd20e400716838681c0e0dee86e2c36721ad10d5586964342419ec0ce306628327018e60c4a061342ff617a90bb105c402d7c168d0b2e058ac2bb215870a9a8538c28f614550a0184ef026ea134f099484bb4253612490901046c022d211170857840f01fa80f6c078d03a9c1c3c0dd706d3035a81a300cdc065b031bc183a0bc005bc82d4c16020aa4052e828581372097204a08244011be08a30428820540fde079d03ab01c940dbc068c0322817f80b6e058602a50140c098e0475022780ff4076c0385019980bb0054a025e010b806e802e6012c00728027800c40026000067fcba61d69502bff5db0eb4a81cff61d855a540affd76c2ad2a075fd875d569502bff5db06b4a815ff6e1735a540ebfb0eb9ad2a057febb5cd69503b7ebaac6b4a815ff6e1535a540eefb0aa9ad2a077dd8354d69503beeb9aa6b4a815ffaed535a540e7fb0ec12d2a073fd8360969502bff5db04b4a81d7f5cd725a540edfac6b92d2a067fdba54969502bfedc2a4b4a81d7f2dd525a540eefaeaa92d2a076fd6354969503bbea9aa4b4a81dfb609525a540efdae4a92d2a057febb54969502bfedc0a4b4a815ff6cc525a540edfac6292d2a057fdb114969502bfedc264b4a815ff6d5325a540efbae6992d2a077ed824c969502bff5da64b4a81d7f5c9715a540affd76b8ad2a0777d5254569503bfab8aa2b4a815ffaed515a540ef7aeaa0ad2a077bd7250569503bdea9282b4a81def149415a540affb6e98ad2a057fdb54c569503bee99262b4a815ffaed315a540affb6a90ad2a057fdb348569503bfab8a42b4a81dfd4c5215a540affd7690ad2a067fd75aa9695033feb9554b4a819ff54aaa5a540cff8a5552d2a073fd75a21695039feb9d10b4a81cff54e885a540e7fae5442d2a073fd52a21695039fe29510b4a81cff4ca885a540ebfb0b3bad2a075fd839dd69503afea9ceeb4a81d7f60a775a540ebfaa53bad2a075fd329dd69503afea8ceeb4a81d7f4c6775a540ebfa433bad2a0777d8595569503b7eb1caab4a81ddf54e555a540eefaa52aad2a0777d5195569503bdea0caab4a819ffaaa555a540e7fd112aad2a0777d8795569503bbec1caab4a81ddf5ce555a540eef9652aad2a0777d8295569503bbeb94aab4a81ddf4ca555a540eefae32aad2a0777d3195569503bbe90caab4a81df761e335a540efbb0b19ad2a077dd758cd69503beec1466b4a81df75ca335a540efbaa519ad2a077dc528cd69503beeb8c66b4a81df7546335a540efba4319 else (if i<8 then 0xb43ad8d56aeab55a5a9a2d43969e6b4cd5a53ad20568b6b42a5a022cf4d675ab38759b62cd196640b305596facb11653cb283592eac8dd6422b1eb58e2ac67d6308b148588bac3c561acb0bb58502c1e960beb0395809abfb55f8eafa157bdabd295e48aef35766abac95d18ae6656e92b6b15b0cad55568cab3cd58eaac0d55a6aac9d5602aae655602aa9554feaa595519aa83553cea9c154cdaa5d5529ea92954872a3495158a88654302a115503ea80453ef29ee14f24a76c539da9c554ddea6c95351a99c94c6ca61052f5297114b52a58352aea94dd4a0ca4e0525d2925148dca448520ba8f994754a38451af28ce14624a2ec516328a5543eca16d5077a82f94130a07250262806d3f669f404f8d27bd13d9c9e9d4f36279713c6c9e1b4efaa773d3b529d834eb4275093a229ceb4e62a727d38f29c484e1126ff137ac9ba54dbfa6d91367c9b0d4d52a671132e499204c61a621d303e97ac4b9725b192c6495ca4a8525231274093384968249f9245891f048dfa460d226290ea4846a40c11f908f55477c23a6d1be28d474664a302517428b39456e229fd13d689364446220390f4c871d435aa17d50aac84f94248a10a50740833841682091d03a88161405ba013cffe47f5e3f231f74cfaec7d193e589f150f6d07b003d519e918f3d2798c3c921e348f100785a3c099df88ef20773e3b5a9d9e4ec2275933a4e1cff4e60c725c38ff9c630e21c706437fe1bda0dd926e4b36999b2d4d89a6c0635d49ac54d55a6a5034cd9a398d0fc67c933b099c10cc8865b0328e19220c7d263ad31ad98ba0c4a8620230b718368c0765ff42fd117ce8bd625e492ee0174b0b9b45c932e2096fbcb6f85afe2d4b1693cb41059cc2cb216398b08e57c92bab15adcac72559a2aa995404a95e544729fa94e08a63452bd293014838a30a512828449418ca07a4f9327b693ae09d244e5626d0935ec9aaa4d2f267f13360994e4c81262d930d4981e4bde25dc12e4896d84b46259012be895a84aae253e9295c944c4a0024ed126d0931c4968249b9244491d648c5244f921e490a6482d240391f848f76479523b791cf88e1a46e7231e9185c8bcc453c228b11158884a43f4219f90c6485e642cd215390a0484b642352107907788370419220b610518824040fa20649028c80fa405720189002c7fca3fbf1fcc8fda07e843f111f758fb147d3e3e791f240f8887be23dcb1ed28f5fc7a9c3d1d1e448f00076d83ad81d590ea3074b63a351d020e64472d639451c8f8e3b8719038a21c3e0e1587060380a1bec8decc6f04375c1b9b0dc146dbe36ae1b440d9886c7836161af80d7286b48357e1aac0d4c86a1834e61a600d26868e834431a0e8cfdc67a233ab19c28cd50664632e719500c9e86492321818ee0c680629c310718550c1606064300117e28be24 else 0x21c3464be8d9149c8443868c72120a1cc34448a8d914a21c3454828a53aa21571868c97d22a36443868a97d22a364528659061a3a41443868712722a75c6d8a70761a39c8cbf8db14e0ec3468929055c61a2229cbf12722e36c1d868f97f22e36c528870d1922a2940d2e110e1a325f97096510a49c3464be915034b8443868c97d22a2940c8665c320c3484be91514cb8443868c97e0e60ec0d2e30d1922c1cc1d81a5c61a325983983b034b8c346838887034b8c345493073074b8c345f8bed8080e839b4123a063500f67fd73f4c9f61cf9427b373d549e604f18e77f73b939d6f4e9da7433396f9c8ece38670c737cf9b8d4da9e6cd7360e9ad8cd4fa686333df99ab4cbe66565321e98ba4c45e61a1301b97df4bcd65ddd2e7b97044b7325b212d54967bcb18e580d2bb495904aab6543329bc94afca32e50dd281c93da49cda4e2126ea936249a7a4cdb263c930b497c24b9525a492bf495624a65250c9268492aa4909241c91fb48f16473f2337914c4899e4483221b90fac873e4353218390aec84b241e120ca9052481fa40b12032900647f6e3f551f798fa9c7cb63df91e898f31c78ca3c191d998eb9c737e395d1c888e2bc70c638171be58ddfc6e6636e71b4d8d8e46bda35751a948d3746922344519fc8ce5c666a32e919438c8946252304317778b35458622b77153d8a28c4eca266912b688e54437a2119101987cdc3c761ce70e3786d1c338e18b50b848588c28121323093f8455c20e2100f07aa83b1c1bc20c8d05c882d1415c60a81051a827a4133a0951041481f1c0ef6072f0371817f40b620565028c813340902043501f480e1c067602ef01518095c041601bf00b980444018a007900167ff83fe21fe56fed97f4ebf775fb16fcf77e4d3f09df7aafb8e7da93eb51f4c2f9cd7cad3e345f12af8387bedbdcf1ed7cf64b7aec3d53de9faf4c17a42bd125e81af36379783ca21e3d2f16b787c3c215dfa0ef1b774ebb7cddb00ecf7763cbaeb9d6b8eaf47535ba75dd2b2e8c5743439fa9cf30e725734e3984dcb14e54e726db91cdc842e3c4719838a45c3fae19570a1b83f1c0e6e00b6fdcb7cc1bd7ade4a6ef6b75e9ba3adce16e4d370f5b7aadb6d6d7d36a75b46ad9cd6cbdb644db12ad84e6c0eb5f85af08d71c6b7035a0dac78d60b6aed35545a9bcd4816a2835025a79ad39169aab4c39a5bad2a16917346eda2a6d0e0683c340f1a000cfb967ae33c559dc8ce87670fb36dd9acacd1e667133241983acbd665c232c9d95d6cac56544b280192d8c8f9644e320798f82c77a63a4b1c098d76c6486300b16e98a8ec4ea6257311c9882ac3a26197b0af184a8c22360f3b06558244c0af600dafea17e6abecd5f1caf7197abcbceb5e3c2f015773abb095d50ae91173e4b9535c6aae1057036b7f55bc6add9d6e6cb6fa5)))) else (if i<14 then (if i<11 then (if i<10 then 0x902602f0d241681fc32754fa1a9e41a1b0d27010323aa7d0d4f18e41a1802a424821be9f140f03ec3470920dc1086ef8bed818d2003c07f0d2c6584bc53838649df3700b80b68630586981241b819f8bedb9001e05b869212410fc507c05408e1a383101db202b84404608434fc5f6dc634302e68110ae1100f81604608434fc5f6c0bb8c686704e0521f4013df03df17db06c04207f0d2c2f87a00407835fc5f6cea41081fc34b0be0a42b8440060780e7c5f6c0b810b82c34d0921f037fc53e81b39001e03f869492522a2941c808fa61a3a3640496510ac8c3464528850d0d012214343446885900c2fa4946e8870d1514a024ea88664239c3473aa8866421a22024433210d1111a2164132081151ba21c3444eb8db14e0ec053230d1d22a2941c808fa221c347b6c97d01259442b230d1d14a2143434426e10d0d11a21640306c92510e1a21f4b6d91714e0ec05868f6db2fe29c1d8096461a38370f41aceafb6e400780fe1a49d5442868697d1ba3641c808eae1a3a454049d510a39c3464048850d0d11a2164030529251ba21c3458b39153ae36c1d80b0d1ceae5fc6d83b012c8c34776d97e2ce45c1d80b0d1f22e36c5380a10e1a365fc6d8a701421591868eedb2fe45c5380a10e1a3e5fc8b8db01421c34646c8a5072029908870d1d14a024eb32110a39c34745332110a1a22029908850d1111a1a990c8089d71b629c1d80a6461a3bb6cbf8a707602991868e8a72fe36c1d80a6461a3e5fc6d8a701221991868e1242b852f8a6e01701603d86926e110a1a1a5f49291514a0e371868e9151b22941c8870d192fa364b28856461a3229442868688d10b2018024928dd10e1a2a5fc8b0e71b629c1d868f97e1ce36c538396461a39b8cbf91714e0ec346cbe96722c39c6d83b0d1f2fe45c6d8a510e1a365f8738db14e0e591868f873031d5c327d0d4f20d058693873031f4c3277cea9a9e41a0b0d2b0e6062d1864ea9f4353a0b0d270e02fc32754fa1a9e41a0b0d27031d53e86a79000ac347439818190013aa7d0d4f18e41a0958701e65f0142e4389c8353c80c3682c34c48a8a5031f4443868c92520a1cc34446c96510a49c34548a8d914a06432c830d1d22a364528870d1520a21c343b8a8d914a06443868c90514a064ea8855c61a3dc54be8d914a06432c830d212fa36452884e461a324144386877153ae36c5383b0361a383748a8a5031f44432e30d212fa594429265c61a325f48a81910cb8c3464be91514a06432c825c61a425f48a8a510cb8c3464bf1065c61a22458832e30d10eaa4143986889151b206443868a97d22a3640c8659061a3a5f48a8d910e1a2a41443868716722a75c6d83b0361a39d5cbf8db07606c3468b29055c61a2645c6d8a703421c34678b97f1b629c0d0870d1d20e29c0d0855c61a365fc8b8db034 else 0x8650e236a0044bf77d22dc546d6d8c7206b5361801c820034010cbd0ca1ca0034bf77d22dc546d6a6db0294436380398600720800d004331432871e2d0022194340728012efdc54336d90758e43881ad4d8600720b0d001a01c62107214b001c1c852c0068650e7181a1943940068650e5001a1943940068650e5001a1943940068650e236a004432818c30d0ca1ca00343281a800d0ca1ca003432872800d0ca12a003432871db50022194394006865075001a1940d40068712fd001a1943940068650e5001a1943940068650e500198e43886680110ca1ca0034328711b50022194394006865035001a1943940068650e5001a19438f16801103219a003432871db500221943940068650e5001a1940d400687210a5fa00443908514d0021df48b7151b5b64536a50758e43201a8000a6ddf483714db229b5283ac721900d40005312fddf48b7151b5b635283ac721900d40005352fddf48b7151b5b64536a4c721900d40005350ca1ca003432872800d0ca1c78b400886409500198600c07280100cddfb8b6dad4d8e43803680586541c80cc007072033001c1c80cc00707110c066004432870c30d0ca1ca003432872800d0ca1ca003432870c30d0ca1ca00330c8710cd00221943940068650e236a004432872800d0ca1ca0034328711b500221943940068650e3b6a004432872800d0ca1ca00343283a800d0e25fa0034388a6800d0c81ca003432072800c0e219a003432072800d0c81ca003432072800d0c81ca003432072800d0ca06a003432072800d0c81c78b40088190cd001a1942540068660e5001a198394006071035001a756408e70d113ba2157086889053aa21473868b71714e0ec0c9df0d18eaa41c3434eac811ce1a2277442ae10d1120a754428e70d1722e0ec0c9df0d14eae5fc1d81b016b6c347c8b48314e064ef868cf172fe29c0d80a10eb6c348cbf91703602843adb0d1ce4241c3434eac811ce1a22414ee8855c21a2a414ea8851ce1a2e45c538393be1a29c8cbf8a707602d6d868e8a72fc49c8b83b016b6c348cbf91714e02443adb0d1e20e29c1d81a3beb6c34788383b03477d6d868d10714e068efadb0d1a20e29c1d1df5b61a30490978a43de060ae77cdc02ec40198c161a6e5fc526e0331c805d880c3182c34a05b97c170663906e310186305869597f1481c0cc720dc02bc40618c12adb25f40496710249c3474448670d0de2db6cbf8a703602c418690925111b8c41868a97d1b259c409270d1911219c3434bf9161ce36c5381b1061a43c5cbf0e71b629c0d8830d20dc65fc8b8a703620c347cbe96722c39c6d81b1061a465f4939161ce36c538830d201bdf40f777ee2fb6babc800f01fc34bc04754fa1a9e41a181761a46023e877cea9a9e41a181761a4e022d0754fa1a9d0c0bb0d230760202c754fa1a) else (if i<12 then 0x14da9a3083ac700aa0001401b40c85f48b7165c1a9a3083ac700aa0001401b40c85f48b7165c229b53460c700aa0001401b40c85f48b7165c229b534610758e01540002803741cc1d2e00280a2c1c1ed8380560600200ce0665c1a9838460c760e01440001a80c85708b2e11482ea3083ac700aa0001401b423e1a3bf2e1d4d86838703297c2b845970ea68c20eb1c02a80005006d03297c2b8459708a41751831c02a80005006d03297c658459708a41751841d6380550000a00dd2e1d4c1cc1c014051a0e0cbc1c02b0300100670327160e4b823063b0700d0069032914170299714610758e0154000280360190ae6da0e11831d8380680348194be91417029971460c700aa0001401b00ca5f48a0b814cb8a3083ac700aa0001401b65c41cc1c1324100d01473520705c60e01a00cc6a40e5a9171838068033c1c05b8380560600200ce064e29a9838462074b801440001a80c9df36c6a60e3c5231038c300d006b03277ce29b68384620700d00699710738c005e00028c6380e40e1700340198c721a81c2e006941241ce3020a0700ac0c00401a40c9c53530708c18ec1d01a5c100006b03277d22dc54536a68c20eb1c01a5c50000a00dc064659b63530708c18ec1d0188000358193be714db41c23063b0700d006a03297eefa45b8a6a68c20eb1c01a5c50000a00dc064ef9c536c6a60e11841d0188000358194bf77d22dc54536a68c18e00d2e280005006e038f17070b801a00cc6180e20e80c2e0068033c1c1138384140600200cf105d4c2170d019e2c1cc35c61310610c1c00786838f183bd58830860741c80c00f0d3a9e30a8830860741c80c00f0d3d5e30978aea620c2150402b0d71843c807a1c60e421028035c32220c1c84202b0d3c8e3077bef1620bb68390840380650402b0d71860717900f60e421028035c3211b5dfb6c966d4a21b1c926c300390400680219721943940068650e5001a45b8a8dadb229b52639035dfb0c00e41001a00865e8650e5001a45b8a8dadb229bbf6a510d8e00e61801c820034010cc10ca1ca0034328680e3b6a005b8b6d90cda941d6390e206bbf61801c82c3400680718821943940068650e7181a1943940068650e236a004432872800d0ca1c46d40088650e5001a1940c61868650e5001a1943940068650e3c5a00440c866800d0ca12a003432872800d0ca1ca00343283a800d0ca06a003432872800d0ca1ca0034328711b500221943940068650e236a004432872800d0ca1ca003432872800d0ca1ca00343284a800d0ca1c76d40088650e5001a1941d4006865035001a1c4bf40068650e5001a1943940068650e5001a1943940068650e5001a1943940068650e5001a1943940068650e3c5a00436c8190cd002219425400677d22dc546d6d90758e40d6a6c3003904006802197a194394006 else (if i<13 then 0x480421887b0beeda1b3a9853084e4586006a0800b00832e88b0a610807570005fa419445f853086071c8570005eec19486a88b0da1080700786838c19485f7ab11421c3684303803803002ea60cb22fc36843038e4003c34f560ca42145f88b0860700757010e0ca429236f6c8a415f1841c04f4100ae0001d806522dc5a30018fa06c9054003228248520eb8db1487bc1c722c300a50610be916e2a36b6c6a40306b44320805001a00865e0643087b453c603c80a002199218830e45c6d8a60300a442803217ce4236b6c8a6d4d180272080550000ed032070321c58939145c9b68eb8d8d4e29e30460c7066c1c77c03c060062080090030d9032070e41f4c1c6180300a0021c5417ee403d0548840080ab0c8c52720fa006014004b42214019b900f438f1801e0040558649864382270728200c40001a00c81c0c97145c9b64eb8d8d4e29e30460c707bc1c01e030031040048054322361ee8a51080a002866e4253abb645288405001433721097d1b2213aa02800a19b9080f68d9148140140050cdc8404ecbf8db149c801586910a0321c58926a4c707900e2e620a41e2454523dd109f407a71eef14d498e00e2e6209ce40f7082307897d2282a4420f4c61a248f708240320f122a29e301e41e9c20e2980c3dc5c61a44274be2f2db1c84536a68c01390402a8000760070921e47bc412819173104d4e2923063b0703d486b48bf17db02ae3004f4100ae0001d60640e06438b127228b936c9d71b02a853c608c18ec1c01e03003104004805817a45b8a8d87bdb60528840306c90402b0d21970190b0070efe5f78a9145c9b6c6c0aa14f1823063b0700780c00c410012016c380bf2ffb6c6c0aa14f20c1c01e03682098f170d3ce2c49054638038f71729050906e28294420193ac820158690ca82a82a05f97f1b60e391019e280ac34b05e97eefa45b8a8dadb02931c050034820158690cbc1882fcbf9171b40601586910a40ca5fbbe8dadb0293914600980ad0540003b4ef9a90c20bc36049c8a3dd3ae360d70a70761a704800e0bf2fe363ab0a5e2e0e09986960bc0c81c3bf97ce2c49c8a2e4db6360550a78c11831d838d480780c00c4100120061b20640e1c81738db0718600c02b0d0715864b908d81e829442004055864a410538385c83d76c60e37201b8294420040558640123bf97c5c9b6c6c0a4e400610402b0d2216866b900f41481901e0040558649864382270700650440001a03281c4be717228b936d8d8d4e2980c00c4100120108601400e1dfcbe9145c9b6c6c6a714c0600620800900843038a904d4e2980c3dc800b984290b4070efe5f38b9145c9b6c6c8a60300310400480421804e02597f1b62939002b0d021486102497f228f7c6d8a610a00381c3bf97ce2e451726db1b1a9c530180188200240210c40c85f38b2e1 else 0xd0ca4ba0034328e2800d0cd0012024334006865015001c214bf40068a58c421a00443207a800d0c81ea00303c866800d0c81ea00343207a800c0f22141d400807910a0ea004432079db202a005404866800d0c81ea00303c866800d01219a00302a886800c0f25fa00303c8a58c50021df48b7151b5b64536a68c20eb1d2180121900ae4bf77ce2a36b6c8a6d481690c86401005603201977ee2db635321ac150080a8856864303b6a00443212e800c16a19a003432046800cc100203d400883aefdc5b6d46017486443609207e8c016b1c02e4321900b402c12a8c4026003a31009800e8c4026003a3100910b00201ea310098010c1050ca5f3043433400486522d001a194e940068652ed001a29432608686680090ca6aa0033048a50cd0022194ab4006865215001a194c5400693910d00183e44283a801110a0ea00343297e800d0ca36a003432f1514d00221941d400697e800914b18a0034828730d07b21f40d946103586b8b20a800644819038192e28b936d1d71b1a9c526383de0e30d818018820024038c512ca214932e000a19be870c9714d498e30c2e6209d14a0e40c3de5c001433775011ceed861ef104b17ceac2181d0195c0017bb0653f1432236f6dc810300ad0586815280ca45b8a0a4fa51840d61a415000c8b0c81a83ae363ab83b033c5c349032070e2e4536d8d8c760e30d818411000e2d3aa7d0d4e06007868b422164090320703361900f871031d5f8a7d3db1a9e4000f4161ae0110320b50e11831d838c360620000d412c0c81c0c9716228b936c9d71b02a853c608c18ec1c61b030031040048054362361ee88503003c34866eaa4360f74eb8d8eae0eb0d81b0d242124541c8187bcb8086778a3dc1518e30c2e6209e2c86b3e82e42094ea8f717210480a82cc361ef104a0645cc3631c61821c413c3685200c0087b832688b0a43cc06570005fa419445f85203e032b8002f760ca03544586d48203003c341c60ca5eac450870d833406006005d4c19545f86c03e03003c34f560ca02145f88a03e032b80870650070e2e4536d8d8d4e292d061b0300310400480421781c4bf1145c9b6c6c6a714986c0c00c41001201085e1ec2725f1ef8d9d4e29b0d81b0d421580f03877f2fc451726db1b1a9c5261b030031040048042189c58826a714986c0c4005cc214c411ee6a714986c0c4005cc214841c527d05ce0617186a10a220e29c0c3de5c682c3408503dc5cc4186c6a714986c0c00c41001201085a1b80e25f38b9145c9b6c6d0a4c36060062080090084300b4070efe5f48a2e4db63685261b0300310586a10bcef9c54828da148f730d818800b9842b0d40c52fe451ef8db0361a84293be6a4310314bf9147be3685381b0d021604e06397f1b1d5b5381b0d021480f03877f2f9c5c8a2e4db63685261b030031040))) else (if i<16 then (if i<15 then 0xbf4300181dc61644217ba600208a073c576dc6009a867050854f5421a19a41c600982e7528a41c61640577aa5a41c6009844086581cb221098e0d3c600b013402281cf7ddb2c87530878c016026a045039efbb65910878c01650c04d4004113c576cea5430168434800faa070527708640b02ee3004dc126077180ae14894802271802cee0a1110cd20e300582b82e380181c149dc21902cea78c013704a045039efbb67530878c2c802c04d419024bb686eea610ac8d0c07dc1402c35c61a07a2487a84201c0fc02c34fd38c280f07d8430396401f805869eef18501e8930de1080703f86838f18481e7bef562484386f0840382e805869d4f18681e0f90de10ac80af00b0d3d5e30a03c1f624c2100f06822043e309032b21db3a903c04c05e1a00ea194f7ddb2c87520780980bc3401d43280cbdf76c0796401301786803a86501e78aed9d4c1971d0380ff18481e7be14823bb886e0b80c80c02c02c02b82681e0a4eda0c82e71d0380ff18481e770ea60cb8e81c07f8c200f044032e3a0701fe30703c1c43605208eee21bba90320300b00b00ae09c009efbc576cea40f01f02786803a8659c546d6d914da9443219015dfb04006802196a1948b4006864355001a29b8b6d8d4c86bbf6090d2214a190c540068650d01ea004432181db202a005405716db5dfb5202c06982442869483ae2db6b53609108693a49b8a8dedb06bbbf6a510d8e00e8080fd82c34006807188a19e302432976800d14a19e30343340048652ad001a19485400693910d001a2141d40061b910a0ea0044328da800d0cbc54534008865075001a19404608686680090ca4ba0034328e2800d0cd001202433400688680090ca02a00343340048653a5001a194d54006865215001a194c54006885075001a2141d400686680090ca7676c80a8014e2a0243340088651c5001a19a002443400497e80090ca45a0034334004865355001a194ab4006865315001a4e4434006885075001a194bf4006865e2a29a00443283a800d0c876405400886525d001a19a00207c886800d0ca02a0034bf77d22dc536c88643202b5360800d00432d4321aa800d0c842a0034320c5075002219434079e2d00282d4334006071015dfb8b6a6db00b01a60910a1a5a0ebbf716db22131dc624302e481e0d977d24dc546f6d910d8e05c8080fd82c34006807188c29a30c0070a68c3001a19e30243297f8c0d0cd00121948b40068653a5001a194bb4006865315001a4e4434006885075001a194bf40068651b5001a1941d40068090c9821a19a0024329d9db202a005404866800d0ca4ba0034328e2800d10d001219405400697e80090ca45a0034329d2800d0ca5da0034329aa800cc722943340088652ad001a1948540068652fd001a1946d4006865e2a29a0044329d9db202a00540486680 else 0x80652fddf36c0a66451802680805d0000ecb8a86910b181b0506207b2fe3641d3200b486c3404d497f1b1a98523218c00b02601d3069db1a9190c6005813381acbf8d86c00b00204c03a00d25f38b914db6363538a61080b20004c03b40d1dfcbe71722a363538a610c0e01640009807701a3bf97cdb636453086074c8016400098076a5fc6d8a610c0e19002c098074a1a353086070c801604ce06813c210162480398649c53700781708601600880005843065832cdb01e05c6088042119306523240f1b884202c174193fc546c0f51482be308380980ae0001401b122dc541d218011f40d88668006450600be8dadb0024b288680005432a0c0193e2843e41009db01f42370e80f430645c53838059b800aa452366e2db63532190d221401e80407c0b00b29b843c02c02a214326032078c10641930e60101f401e0be324dc7180ae014293c5485f0936e01721902c01c02d82481e35217c64e453700670700b05ca01815edc02e43501510d8240110be32722e294426e002816485fc8b8db1488930440009807481e0c86da1c8d931c07ce0642586446dc610705700a1493078259df4bf0e71b60e804364640055e5fc1c364dc0c800a61b288664057201903c15c2901f281903c190e2db63526380fa12284441c02cfa005442866dc246f5b61b26380f952fbc5088884058054336e108a46c844434886dc18dc01f02c02c80e0fa5b603e44be9151b02e055c6107013015c0002803601903c190e2c5936d0e41518e03ea05a111072210161b02b82e401903c1100f90c165fc8b83805844302d05c0f51080d282d088884ea82e281e03e05b0d00b29a90d91641c86b03e63523642b81f201903c4601701f281903c754dc60e016608010050e2a0c814adc0294328380b00700b60940472f829442838291b800a059397f22e361126a54318220004c03aa013b6752b234300d3050860d24059b8843069fa15641b8843069ee960100b01b0860d07134027aa1100580d843069d4a2012c801b0860d3d534020170842212012c876cea60c81683402d02f1db2c8753064c101683402d3009efbb6832b214301683402d2181e29b875260a1080d38cb3700b8c142101a605a0b8dc42101a503c714db1a98434800f9c0f0521926d8d4bc584221a9001f501e07e6a610d2003e603c77ce29b68434800f9cc103ecbf9171483fc3408506080a81f04202cb0869001f181e03f084800162819034714db1a903e4620100b20004c03b0efa36b6c8a6d4a1941c00a6400ba0004c03b40c81a3be714db01f01640009807500cbbf6d8d4cc84348858c200a9df38a6d8d481f44202c8001300ebcbeedb14c0219002c09807420e4430086400b026601a05806089201503e8841fe1a026603407c4480102601cc0041140e76cea78c2c8d0ce0a10a800c0ee3004e1) else (if i<17 then 0x440678c01470c015c12d0ca22a003432889e2d0021b640c86680110ca22a00343288a800d0ca22a003432826800d2fddf38a8dadb229b532390358643200802b50ca2276d4008865115001a19445400686404d001819bbf716db5a9b0c88802d00b04a845009800d0ca22304343288a800d0ca22a00343288a800d0ca22304343288a800cc12224334008865115001a194454006865031821a194454006865035001a194454006865115001a19444f16801103219a00344497e800d11229a00344481a800de29b63526080f1008423260ca4649f403e07800c210e30650714db1a903d0840fc19384546e3643d8c9281938a19222c75c6c364c707bc1c01c0f982c04004807188a5944201d010014337d0e0783225fb6d0d88c0d931d838c1602200325a1f5074c840400510a19bba883c174fa25fb6d0d86ce0e19380947540f81ec3508438c1939d584207c0f043832605c07a1081f832548bf14327b641c04f4320200b868152c3206a78a9143ae36c1d8086ce1a501903c717229b6c6c63b070863058088007169d53e86a40381fc05868b4221640a0be717229b6c6c460d480b20004c03a86601e0328081701f286c4eb8d8eae0e19380b0d213aa219908091ce1a4337550078ef87dcbf6da1b1183aa63b07182c0440064b8210d98b391435c293e9839c1602c34b3520dc3ee5f087839c16021b386941a8150420b3914fa60ec056db0d280c81e3bf97ce2e4523063b0708608810d8f15db1a970506a108d93c291b306a10bf42bdd70506a108d9286a3ab06a1087128423ab08422043281e38b914db6362d06a71480703e60b01001201085e0792f9b6c6c364c160220032610a8271df4bf8d86c8c9c0586a10a464e5f36d8d8681a9c5201c0f982c0400480421701e3bf97e1b1a9c5260b0110019308560fb22e2981c7d009b82c0586a10a83103ec8a7d31483fc056db0d021501e3bf97ce2e4507e6a714c0e00e07cc160200240210c03701e4be324e2e4536d8da1480703e60b010012010860078efe5f36d8da14982c0440064c21581e3bf97c649c5c8b0a60700703e60b013b6c35085e1a818a5fc8b8da07013c0586a10a8ef9a90c40c52f8d9c8b8da14e02c34085813818e5f1b38d86842959180b0d021580f03c77f2f8c938b914db6368530380381f305808009008432453322db1a9b04869109c3101e99191714a2107e05809a40d45f9919141fe36c53c600580102601d80640d25f38b9161b1a9c524600590002601da77edb4c84536a50ca0e017400098075837084079efe5f99191514e0e03f60b0161a6a29bbf6da641a9b0486910a00f03fcbf32322e2944263907016026b4bf6d86462901604c039c0d65fc8a2f314f1801600409807501903497e641b6c6d0a48c00b20004c03b00c81a3bf97d1b4c88524600590002601d else (if i<18 then 0x432906800d20a75a003432906800d0ca41a003432906800d0ca12a003432906800d20a3940488680150ca09a003432906800ee298e41c9d6d4d8647386a80250c831a0034320bde2d00221905b400680aefdc596d61ad49824428692066efdc5b1c906c302e4056a6c161a0034038c3a20a75852c00886520d001a414eb400686520d001a1940c618686520d001a194834006865095001a1948280a801120a3940488680150ca09a003432906800d0ca41a003432906800d0ca41a003432906800d0ca4178b40088191ba19a004432905015002219483400686504d001a418428a6801020dc5b53460c720e4ea8e6c35005219483400686417bc5a00443204a800d01041bbf7165b5a9b0c60910a1a5219013400777ee2a19b5283ac724101480ac161aa01619b1053ac066004883019800e20a2180cc00886520d001a19452618686520d001a1948340069053ad001a19483400686520d001a1948280a80110ca41a00302a8e501221a0054828a6800d0c841a003432106800d0c841a003432106800d0c84178b40088191ba19a00443284a800c20c3945340081061ca06a004f8a8d81ea29057c634700ae0001401ac3005f46d6d801259c4140002a1956220c01922ffc5c8a10f14879c0c00e0162076d869e1800c8220c917ce2e4536d0e71b1a9c53c608c00f11c61b031df007008009003058044124dc7180f615de29c2fdb805c06407a4900b60900640487bc8b8a78c1b83040080286658190441912fdc588a6da1ce363538a78c11801e238c360600700800900a98208e12cefa5f8738d9d4e29c4161b0340200ae46e1741e84bcbeea714e0637100802ac0c8223bf97cdb636230238c36060aeb0321d8110644be71722db686c6a714f1823003c47186c0c00e010012015032178111dfcbef1522db686c6a714f1823003c47186c0c00e0100120154be11007a4900a866dc1c1e65f49391714814016818dc00550600060e0fa25fc8b6db14e20c0d869697d22a3605c0ab8c68e015c000280359df3521801682e0d916722839c6c1ae14e20c0d869e6a72fe36c0c15ca064111dfcbe717229b6c6c46047186c0c0b9a064110093bf97f8c11801e23803a063aa6e0c1002200016297c31fc5f6c8a415f18d1c01f80005006c032088efe5f38b127229b68738d81522901e23803c0600700b0d4c2580301397c1ce36c52050e461a500904477f2f9c5893914db439c6c6a714f1823003c4700780c61801c02002400c1600c822cbe8a4e41b8e30050c302e541980d08a0161a7bbc60ef15db3a9832e1a1140600600b1061a00bc61a15ddc02e8440678c066016015c1280cc220afc6081120cc2280d86802bb8e3080321121105705dc60c1c5eabb8845c6007c1a016015c129efbc576cea61141951c01c030030040530d005e30f0ccf21dc02e8 else 0x9070d07b1847083114d4e29e30460c760e30d81a3b8012011d5e1a8eae0ec0cf143be1a0ea80827172298ec1d1d4c36063058088007161d5c1d61b03277c349d4e104e2e453538a63a986c0c5a0c160200240210b820c453538a4c36064ee60b0100120108581ec273a9c5361b03277c0586a10a8078413bf97e22eb616c6a714986c0c60b01001201086148207475873869ea983704138b91614986c0c9dcc160200240210b435031c8abd303602c35085018818e45852bd303602c34085213818e5f3ab6a703602c34085203c209dfcbe71722eb616d0a4c36063058080090084300f6185e2a45c5383ac30770ea90c418722e2980c1df012214007082717229a9c53c608c18ec1d01a3b8012011d5e13b2fe2939180b0d2213a756408e70d5c8286b48bf175b02ae3004d0100be0001d6104e2e45853c608c18ec1d0193b8012009d5b8672082fde997f5b02a853c830700780dae3013c5c3500aa0a817e5fc1c722033c5c05869571590275473868a0c417e5fc8b01b0161a44280c20bf22c29c1c9df0d275404800e0bf2f9d5852f1707602c34a05e064209dfcbe71624e45d6c2d815429e30460c760e35201e03182c0400480186c04139183803277c341c4e048efe5f06e2d8149c800c60b0161a442cb910659020e4ea8e70d58640090338393b9c805c60ca104e2e453538a60327730580800900842d0b4104efe5f38b9175b0b6453018c160200240210bc27012cbf8a4e4602c34085018409645c529de1098038413bf97ce2e45d6c2d8d4e2980c60b0100120108611de20e29c1d008e400587283bf1048c18ec1c15cc3606804004804396441c1c81a3be1a872638a6a4170410ef6a707606c340e5477ce2c4123063b0743930d818172a3bcb8843069ea963bcb8843069e415e2c779710860d16010717908dc17421834e19110420c77d6c2d8d4e2978a61b03402c35085a71620a2930d81a3be1a84288838a5034028ee014109cef9c58826a714c3904a61b0340200240210b63b9df38b1051498ec1d01b0d43954773be71620eb616c6a714c068040048022168410121df14e0e3918681ca03b841c520e6036b6c34885077ce2c413538a48c0bc31d83a030012010e5b1d610c4187300b0d3d5e3088eb10610c39c34f238c1de2c4105508403c7587386b8c2438bc88820de1081405c02a0161a70cb432906800d0ca41a003432906800d0ca41a003432905e2d00220646e86680110ca12a003)))))
def f3077uL34 : PackingT := (1031,4,7,17,f3077uL34F)
def f3077uH0_34F (i : Nat) : Nat := (if i<1 then 0x100b7423e501434073a0280417400a2c028bb90f9822a209d5411700a2d00822a31c028b00a2dd97b203c4c013a0670c1e2a030ac0bb016889994903ff809c70932806a71681821b100f70212806a098fb834dc0143733f6427ad185459bc615f385bde0719015c2b0cb807af043bc1fd80064809a00a2cc07ce0249c24b905a68284596c8028b9b173420700a2c028b468bbc28600a2c4052c0878028bf640f8112e03df00f900a2c028b00a2f998600a2fc01000a2c407400a2f005d107e4028b800ec028b00a2c028bc2415c1cde01e2c25e00a2e5a3400a2c028b00a2c028b00a2ede32b0328028b00a2c028b806fe41ec50860028b00a2c8280e049c028b900ac063100a2d425400a2c004c50a28028b00a2fc25a80958028bf07e8c20d416570022a0293823b009b8028bf0864028be00d0cd2ee006d199600a2c028b00a2e009f00a2f1e4400a2d817ba06de80e10099bc04d00a2f811600a2e80b1bb540028b009b0028b11414c24d00a2cc1d3704b2420500a2c028b00a2c008b00a2e025d00a2d402700a2f01bb80630c02879540c1f190529c0fee037aad275058cc01e104e6061080610028b7047f823380624028b00a2fc0fd3033d408f50214028b00a2c40aa00a2ec16a00a2c028b5077c028b00a2c458fc046f406820510825300a2e402f404c0028bd08b4028b00a2c028b00a2c0043c022741db00a2f81e0309e6890c00a2c404200a2f01a1c09fc4075c0697c11d00a2c028b30464028b00a2e803c00a2c028b00a2c028b00a2c028b00a2c028b00a2c028b5030541d6f053601c800a2c80ab306768593d082c821fb069f80a100a2f025c10938028b1006180ba00a2f5d9670444990727700028b6366a01086b09b013a00a2e41cff0904028bb056c41f2a643d001c4028c416f7011ac1e4c06f00016b664fc025f09de5d1d00a2e023600a2fc0b800a2c028b907e040ccb024740a7204aa11276094a4167504b581e8108dc028b102c8c05ce06a500302533d81a4008080040f1180b0000c0600101c00000010600200c070300100c040100001c0200800000000180100005000020140002c01024040ac030041700403004020001a00001034010500700408000050000300003000020000001403000030000e0140e000080041c0000502801004030100d0080403403000030140002410000010200e018180100800401068060e0010001100801000090680000c000000700402028001000500c0400c0400004020010140000400004070040f008000100100808004000000701005000000400600803018010000300407000070000300001028030000000c000000000408058010000000400000150100e0080500801000000040000c000140100403000000000b0041a014000000d00003004010040b00c07024100800100009 else (if i<2 then 0x3c18f603498176b0994028bcb4f0653720908ed5b904928159502d84276109ccc05681652414000a2c028b06411405f00a2ec087e91b1c1e550240028b505fb82729072c41563060bc26450432c1c3119418170d6654814cdb3f6013f2016881522085081bdf0569c2341063944fc2742c028b80091646a109024193000d880ce3060ec16460250028b70302c129100ddc5bce089a4283534dac1b400a2d819670605015441619c05ba013941a2605ce8045c05aec50761678028b602d6459700a2d024f1023801a3106e8028be76fb590600a2cc0696070701a040857412b803a700ef728d7013cb00170133483f180da00a2f864500a2c028bc014d02202004840ed00a2c0224068f599c0f02a4c27dd68f0028ba02f4028b00a2c028b00a2c028b00a2c028b6097c028bd0924028b00a2e1dc140a25003200a2c028b00a2c028b00a2c028b00a2c028ba062f41c7f0220028ba0428004a00a2c028b203f2c1b1d0634028b00a2c028b60700028b00a2f017200a2d6c22b03a2c0a600a2c028bb02cc028b00a2c028b00a2f01ce00588d98df0642010200a2c026200a2c009700a2e81c4602d0028bb06c8826f00a2c028b00a2ec0c300a2d91000644c028b104f84255e074080dc609825990800a941b8d18d981aa26916010b00a2d80c4d0a045d7bc08324153d07fe006780052017f8071641775031ac1f000a2e40358081bc081e0813412e70886990520965de31c0622427b00943814e3001c028b5096000d3a08b3c0e3734a0028b0b4de024800a2c028b00a2d013700a2c028b00a2dc0f600a2c028b214370126f0228028b00a2c5e3600258823800a2d41daf144041af00a2f823f1013d8047f07d4a57600a2d41c9f0540c24a243f6010900a2ca449606d741d51140e40afc0098c2098052141ee708d7022f10a23410100a2e009b206d801eaf001000408061a4135808884098406adc131e090d81d7701254d106091641e1f07d3020a7842e013d00a2dd19a801fb0616d09a8422eb0800028bb0047802c00a2e41cc00a2c028ba68bfc1d8e08e5c14b607db0175502b3026d608694058907ec028b4036c028bf09d301eb00a2c402000a2d4083a041a802300a2c028b205ea0247c04d8003300a2f457dd1938028b5023140b910077c044e0912c2571018c028b00a2c028be44a1018a00a2c028b1028a41147066c026b163f0028b00a2dc2160078e41de416fd062f3959d80ad00a2d022340582808400a2ea565c0a08028b00a2e460700a2f59c100a2cc05100a2cc23cd23f0028bb78d140cd802fc81e6505a201872072980933792c028b00a2c028b00a2c028b00a2f006100a2c028b00a2c82299b530028b00a2c59bd00a2d01b900a2c402900a2c028b00a2c028b00a2e811e4162e017dca33ec09e00a2c816500a2c028ba06fa4145 else 0x28b2043440b7e07a440f200a2c028b808734d5000a2e81dd507f8028b80294819a00a2c04fd00a2c028b70546815f2141318fdf084fe546118d0028b00a2c028b001b3411300a2dc0bce066519bf8067a013421829009df0744028b30708028bf0403416e20180028b968cf0268009f0090a8074900b000a2e8077f012c8142b05564202e08768125206b58079a05c6813880257423a668d8c0158031f42300844d0228b0584028b70841c269b07b6019f8006a81d410265c180109c641dc2001bc1fcd03924227f098d825b503e0028b806c101155099e427ec085c028b00087022b00a2c028b00a2cc06400a2dc0a800a2cc05450460028b00a2c028ba891ac197200b88208009c0028b00a2c028b00a2e419200663c07bd06140251206b241ae0080c41b300a2d023d00a2c028b90804028b00a2c4179107dd001760650420e266f8416cf09e282113051a817800a1501ef806454149eb116410500a2c028b00a2ec0be00a2c028bb01d8028b068fb5e4500a2fc0eae01f4c16dc07cc028b00a2dd9a100a2dc1a631664028b00a2c028b00a2e808d00a2c19a02091b404100a2e01288b68c801fb055f0195e0894028bb00fb81d9308cb415ed263a8c1f00a2e000800a2e4231d098441e75083f40cb10a1e4055504ca04fbf05f))
def f3077uH0_34 (h : Nat) : Option (Nat × Nat) := lookupWord 236 991 10 18 10 4 f3077uH0_34F h
def f3077uH1_34F (i : Nat) : Nat := (if i<1 then 0x60cf84a96027c017200168c1b1e053f80de060e1c084f047cd9edc023c411e306d6813210474815cd022d4087804df00c88035c98ad677cb01e34074f41d980791815d207580225f04c70051e07780225c158802258085a5caab01e8022520267013cf05df4136d105b0028a00a48411906e519ea0056ec116c0291046ef67cbc5dc2046402256086ac1f786728804b00896c21f6064400fec015945cab0247800d6039440487061481f32048a00bd1079d80cc0089781a1008940225204a00225008959819b03f040cd4024a01c7f71bb81a00779a41c3301b70141b05910103006080152511c54082b086d00c7600afc0fb10612983d3676e40e7d1744c0ef8136e4154101c4c2222777580bee0197c1b6a0060c198e073c810c2135a0127b080f006a9016c40043700001eeb0511804df034e19f0d0252812d000d3c1115038f8482401040213a04e70134f0800016b908378039e082d00d26066fc181e069680f49036cc0d9217c819d10134781a6e0178c00c5046cc09bf02c94046301d480161087ac5d4f0099c1dd803eac1ece0838c21c008944057267b245ee30862c18e1043f0078905ce40214059c419d462b2814a6014081764074540a2807035806112b6c146b056b8102702ee813a0030f4003702b141386060f805f5044041cc5033f0106008944033202f140a380073c0387080bc1fb60721009ad03c4c0d580619418ce179880f08055ec0c4f01bec058a106d4207907a7819e90692c1ffc72b24101562ae841af0438c015008940225008940225103dd4220108540225b042d41d750257443bb0784807cb10d799d4e0048022500895c0d6267bd820fc01d240d1901ec007f80750c18b804c185d00089402255052d41b3401d80225008940225400778118008940225e054dc133908759df1502d002255777c0225a0822817fb05c00225008958408008968168905240225a06ec0225202dcc121561aac02c6006f012ea0542c06950666802770673c0c9361978010407c401cea064f45cef01dc0225d07f21dd301c03000110080000010004080182f0380000441000020542e0680405802004040a00000001028030003f0380801c070081105c3401c00000000180800028010080000801c00028010000006802060060142a0000608c0000824048000200402807078000dc18010040000000016004011900d02401004070246200c040dc0a004000242d0001000005008000181600c0300000020050100001400004000680501c02008010a4000580102c0001c0a030000000406014000010041d000050402b0040d0182e07004000120003a1441c0101f00c4006c000880b000140100c00001010040b0010a41a038000140301804000070081101802000030006700000080020a00016c040004500c0b00402014000040800423 else 0x13e00897411a4018dc49ce014e0108805e0c0a0c03d784de6011c8083700fc01d0102710224601534064e012bc0420001e804cb01e500551082645d9c04a984a8003b00225b0199418800896406b3055b41ed50651c19f1039a80222031ac0d4a17d48067762a040b9702600117e06fac210c03aa410d00897042cb1005c04380425813fb038002257023740ced0007418aa03f7c08600897806ce032d00e2a06885cab0089701f600557817a3034280a7306b6c01ee02c0c1692072f8171703bb986e8127bc1a8c01c9dc19305f601e20672c81fa802b540eb904504006006f3012400895047df022281250089400f80089640245057b003bf71f402250013c0225305b242237009601df91105c032e00d4c1cd3086641ac606d3c0f32005081650089402250089540ba008940225810e6c00b8053a4013d10bbc060902a29dde500d9c20a0089584340627180a560415c0c5005d241900005f4187008940225e06af819a5024200ae3041d01f4a0305c400d0819447f062a9c1afd0376019710806c093b01c040c0b081458108030a8140c0728022500798022500895582c00895c17be0080022500896883aa06ba41616048018a9a01140225307ab40af3008c403c87747c0dcc03db4062705bc0096c050b007340707c13ba0138c1db90761c08590207c21700897800f60602002e507084147f07bf8040a01704195b04d400977002b1dd4b032b99cda0521c160907c8402a502c401bf2101e421100897587d505bb00e4008970011500380225a02cc0225d06ebc09e008969800008960129b14400225d02d800f2e17ac41e8e00020089a02e382141063c44170089641c410649014d106a7403a00897c11cc02ac0225407fb40520089402250089581f03051641049679840df0089645e000894c0e83054641bd5048f40bfc17c741a3a0780c06e711a80225a06ca401a804ae00a6c00bc820410530804900895c12f51196c1dca00080225506aa01e5804b200056036040611002680ff00894022500726020c272044196500f94100962170175008978166f0021418d807e3815900894c044104f580307620745d600894022507215c4ba2057c022500894805d606ddc0b5303840225506e002257007c0225405a9c068005f2c1c5507ac01fd902850487b08859dda00896402d905f845f3607198113008948179e07e4c1589134002258058959f1206260143000c6046b0089402257022a01f500894016d61198407e0089405db0089402250089680da110428019600f7841c203b6c1d20023002250089402255069c0225907571c3d201f7008e8042819d6502a4809dc6054c1b04044940e9c08488059a00dd0126c076a4080a045540aa803e48163e)
def f3077uH1_34 (h : Nat) : Option (Nat × Nat) := lookupWord 222 771 10 18 10 4 f3077uH1_34F h
def f3077uL37F (i : Nat) : Nat := (if i<1 then 0x1a58bf5c76c2c84224d050d202901875f14212e21a38beea80d5c78bdb35210d050d285f0a406ae019f17b64828286942f852e4571e2f6c10b0d41434af14410861a20eb14c39033bf5c433e2f6d905050d31c58725fae219ed9d5c81c8a0a1a5882fa78b901710d1a5f1661c819a9ae219f17b6c828286992fc530357010f8bdb5050d265f1261c8a586ae219f17b6c828286980e40de2971904346ec7faace90f9dae5778cce18f7fadd076bad8cf5cad5374d0d14f3cccd3f2dcc867192c367070be66f26b9b6dfab57ed14b20ec10ae9eb52aa3ea30a746918a1f67f69de66e89896580931e42c8f5e3148a361e885fe0bc8125fb87bd5e6e7775d2e7225c3e6f55b086a7da2c669590a620d7fc5d8569e58d55c254ed47850153744bdd28447cd16c439505e3f34f463c14ece3a5ce563854dac34bccd0314cc082ef4b722c24a96288c9d825e491a22ec870206c7a81d4c6ea19dc61816e4546134c47e10cc3ca0d842f80b2c24e076c19a04740be0104000dff61d695037fd855a540dff5d5695037fd835a540dff5cd695037fd535a540dff609695037fd725a540dff549695037fc525a540dff4c9695037fd715a540dff545695037fd315a540dff485695037fe555a540dff889695037fd764e540dff605395037fc814e540dff5c5395037fd614e540dff545395037fc514e540dff485395037fc214e540dff845395037fca84a540dff61d295037fd864a540dff5d9295037fca54a540dff615295037fc854a540dff5d5295037fd654a540dff60d295037fd734a540dff58d295037fd534a540dff609295037fd624a540dff549295037fd324a540dff285295037fd814a540dff205295037fd714a540dff585295037fd514a540dff145295037fd314a540dff485295037fe884a540dff955295037fe114a540dff61d195037fd8646540dff5d9195037fd8546540dff215195037fd7546540dff595195037fd8346540dff5cd195037fd6346540dff54d195037fd8246540dff209195037fd7246540dff589195037fd5246540dff149195037fd3246540dff605195037fd7146540dff545195037fd3146540dff485195037fe8846540dff955195037fe22465409ff69d695036fd635a540def505695027feaa5a540cffa21695035fe775a540ddf955695037de335a540dfb889695037f6115a5409ff699395027feaa4e540dbf999395037f6114e5409ff6a1295027fda74a5409ff699295037bd544a540def505295037f9304a5409ffaa9295033fe884a540d7f9dd295036fe664a540ddf955295037de334a540dfb889295037f6114a5409ff6a1195027fda7465409ff699195027fda5465409ff68d195027fda2465409ffaa9195033fe8846540d7f9dd195036fe6646540ddf955195037de3346540dfb889195037f61146540 else (if i<2 then 0x2e1a93bf2f924d4c52c14041f8426476c9010c05c34f15fc56e02e0841e60a1a40320f0ecdb072fa35314d900103f0cbbfe2f6d9050cc143538a4570660e149dff15b80b816a1982869a248320f09665bbf2f8720fc33db3ab90190c14350066290fdf4f1444c82866e21a505a0f3bf2f8b21cbaa220336403f0cf8bdb3539050cc1435397c1983871755b86a416a1982869608bbf2fb531483e0b043e2f6c9050cc1434e77e5f0e4896a62963a0e0fc1e0081f058c8ed8132198286a60f432d4c53643050178afa0e39050d0d341e77e5f86582808441c5d5edb20a182e869c0f3be0fcbed4c522bb1d070a50cf8adc05c0b50d0d44490661c070757d2b8865df717b6757207228286a00c882fa78b901710d1c19774417d1c575720720b886940c8d40e0b23abe8eab0d0e40d5c0e30cbbfe2f6cd4e414143540661c81a19755f46a720a0a1a50330e4bf5c433db3ab9039141434b0645975443618b9105f4f15a9c80b8869a0e3e8d4c52c340d5c2d010bbfe2f6c905050d3c4e071df97eb8085c5ed9d5481c8a0a1a687c0e35314b0d0317210be9e2a405c434d0c41c77e5f7558681ab8087c5ed9a948282869e0c8c20e0923abe8d4c3914b915c432eff8bdb640c35050d4c198a40a721f41c72061a8286940cc392f8990cf6ceae40e45050d2c19124bc6a5c82e4417d3c5c81862e21a683217838efc392fb8a24baae45710cf8bdb3539030d41435397c1902871723b66a72061a828696093bf2fb5314b915c043e2f6c9030d41434e3d9a96184c071dff14b8c800a20a1a6196efb0c0e38a5c3ab9001441434b0b5df165d56184c073c52e1a9c800a20a1a73be12352c304226039e29709001441434d77c49225a972003073c52e32061882869a0e432d4c52c34390378afa0e3905050d341c77e5f8658687206ae071757b6c8282869c0e3bf2fb530e4530c814e476d905050d34751642112439868c3af8a900730d1477f14212e01a28823af8a108730d1a2981bc5c8077868ce2cef0cde95b3ab903915c434a16641819a99de19bd3c5adb20ae21a6453034ee10de9e2d6d5c4349126418a5869de19bd3c5adb20ae21a6453030efe2d6d9043470a4061d7c588039868e1144147033e2f6d0d1e296da2281a197d3c5881b886952f87314b051140d0cf8bdb4410d2df40a40eb200277fc5ed821a1a1a58be0176c2c8426443470a6c800875f1421a1839869214bab6478bdb35210d0c0d2402b21b8f17b6086866081a4d9011843e2f6c9050c712437b2286f17b60861a40eb14d90efc050cf8bdb64143434b97e02867b6757203221a436d14d910cbe9e2e41433710d2a5f166c86a602867c5edb20a1a1a5cbf14d9101043e2f6d43434997e298641e808c8edb2086932f87314b0564433e2f6d9050d0d2c367d02901ab877fc5ed821a0a else 0x41715d5c81c81de1a38d420baac340c38f8ad4e403bc34b06677866f4ad9d5c81c8ae21a5082d4c52c340cb478a900ef0d284e10677086f4716b675520722b8869818882eab0d034ee10de9e2d6cd4a415c434e184416a629723c5c81861de1a50333bc337a56ceae40e45710d28199042f105c5125d572277866f4f16b66a72061ab886a52f86e0cc053b8e2e456cd4e40c305d0d34126a62972277086f4f16b648186ae21a68826f0ae3bb8aeae40e41710d284115dd561a060b877f15a9c80b8869820b5314b0d03042128efe2a405c434c024de6a629720bc1dfc5c81862e21a60832fb0d20c0d014ee38bab5b64017434d105a9906299de19bd1c8adb20ae21a6032eec32fa38adb3ab10390dc434b06460089b60e5f46a62961a22819b8865dff17b68818286a7148ae0cc0c3dbbfe2b7017440333050d34490644b089df88a5f0e5b815e19717b6756207218286a40cc531140cfa78a22440dc434a0642d089df97c590e44461a22818576e02e867c5ed9a98818286aa0ccbf1140c38baadc353103050d2c19025df97c490e5a988a29721b8867c5eda206198286a52fc520c8cce437017440c33050d2c2277e5f6a62915d8688a06867c56e02e8821a7f8afa0e21083c0fc3470641e1d5f460a023261977fb6757203221a703314d910cbe9e2b6d9050cdc434b065dd865f46d9d5c80c86e21a50e2eaf6cd48420f03f0d20190786a164757d1d5b218280871865dff17b66a720a1a1a9833013aafa3539050c1743490665f80bb6757203205786921b8320f0842cbab6408821c32fa78adb3539050cdc4352189f46a629b218280968085dff17b648286869e273bf2f992c140410f6ceaa40640a50d343e6a6290fc217d3c56d920a19b8869818bbf2fbab6430501043e2f6cd4a4143434e17c757d1a907a2963a0e60a020fc1677cc8ed8132180b86a65e3520f452c741cc14040b3e86436c0990c05c350361df97c1e0a58e839828083f058c8ed9a904c86))
def f3077uL37 : PackingT := (124,3,7,14,f3077uL37F)
def f3077uH0_37F (i : Nat) : Nat := (if i<1 then 0x281df616300ec00054c2dc4d5da05ce00a98164c09600d6e8299002681a51080e03f7809bc0c4f05f486f403bbc04e702e206f0c0e6c13230459823803bbc0d450d43048b016faf5cb07c0077403ba01dd00ee88607c0fe435e00ee80774008fa00cb0d50843681f8a07ac010807244085805620d7b8015812fc1cef06c580251ad4215ee097c032600720078d0da3819240f2204ca0c3905b601c5c01eb0ecf8721c0a321cd202d605de031080d9d0d9b02bfc360009300350054cc213a002c07fc067541ac215f70d70833a410ae0c100204bd5b80dba172a0d37016581e04011c089f0491c1fda00d20974818cc20941ca5012e024640c0c10e50b0483b2031d409c902fa82b9c1bae0b8f0dde001801d401dd708830248c304a09b90a430655c2cac1b6d004405d0008341a750552836f024a01dd109598161c07c417e2062f8631c22d605be0563012740a02147b0a1b837e4347e0cd5080481de0382e0844011104450049013670381bde5002100c620b380777c009809db03a90199c285c12100ee9806282eae07d10963835c03bb4362e00b382558096c0c3a08db0038814001ddb0ad7059003bb8012b010306859aa9810ab046a020b8000601910be38533438960cf80795065803bae18d307d0077403bb60b000ee9045403ba216f10e9982900233a16696b1c866580dca1b500ee8850403ba01dd00ee8077403ba01ddc0d93849d032e01dd00ee905f403ba436700432811003ba61c000eeb054803bb2117b0834822003bb219b40d6305cd80dfa0cb00ee8077403ba612d00eec031dc325a06c00eee829e00bc01dd81b2c872c41ea61d540890818a42d201dd900b8077403ba002c40b55841d02aa013af040506f942b7a0b4208180776c30601dd00eeb04c003ba00541094383c5405fe0cab07480640016b00a200eee82a382b3612900eeb05a003ba01409034605408234e17100ee8843dc262a094f0cc003cfc15a019a9068f0dc1438be081205ef355703b7c19ed0483801d1ad6c123603e083231edda15cb0ab80774c341e0da00eef800403bae0cc00ee803d003bbc0d300eeb05124279e11d505b68d9b40e5415870dc6864642ac008940294047c82e081791014c05e84400006024030280003c1b020000002c088330000000808074000000000801000060081200c1806c000005300003000020280900c110040f0080202c0000400000000044303c010840f010010fc0a028010000d004040081c044000081f000090400d00801048000000d0000a02c0e0100602031134000140705402080000000d04c080300d00802054000042e0200900450018001400f10c0604001000020280600400028080080006c01024000200c000230181c02000004050100701c490380d0140e05808000320041d00001038000040200c0100402 else 0xa0e8684d1030181bf70e3500b706ed41d2901a507520357a0bf705dc82c7806e036980dbf873c9ac0601a70aa085779ae1ed661055b00c6428a80f7502ac868a0142e18520349847b0267801b70e1b84dc0231016c3045200d40211019f8013302a641c7002e604fcb59000a681c23043d0392c22821d160528854403ba60d2b6b0905da42f0417f4033f05af831601dd10e63852440ca6f55e0ed20432c6b5007e5021884fd86b0203af074486268294e0dc50bd98029c2700083202ea86e7c06683527093300f5029d609e00ee8077403bac027f0951356f0205213d76af581d003ba01dd009f484718091a0a300ee8077403baef6500ee80775406001dd10388077403ba01ddd04d502e803bba00fc014783bbc29f608c00ca6b5700070e14d00eef0587daa420eb003dd039b405601dd307ca807043b9216200eec867003ba014be7b78077701bd612027bd100d941cb000330859075ec1a1a0e1a00fc83dbc1810356a0eb0077441da01ddc01da0518427241a961bdb826583496d5a51aed015d431faf57c09db005341782076b0d8d812ac20bc03240c5601afc326c098103080775c375804fc6b3c808c426a2186d1b5f8382007e8d53706a9839f8166e04670e380774003b20fb1047f8612018440457005d00f)
def f3077uH0_37 (h : Nat) : Option (Nat × Nat) := lookupWord 173 602 10 17 9 4 f3077uH0_37F h
def f3077uH1_37F (i : Nat) : Nat := (if i<2 then (if i<1 then 0xcb10a09b04aee0876015308320d00e800d6d0134b81127030a20041008e1023e303580101c0203f8224703d56014040bee82720080e0101e008d80407a069e0101ec574a82cef0564a0c41004b60265801800027c809054b27d010440ffdc075101f7b0466c010580a3082abf01df401ed81a9380bd40688809ed4086680450057ea0103c1c13037ee02c300730c1dd681e16038f408afc05b583f08044d206c941e658026d00aa007c30016e80c10080e605a4020380407e00ac0101e85b0e82da804d4a0b3105af5813b0005ce272c806883b795042b00bf584e39815c301580101c0203d012e203b80101f40a00016fa76ede0d5c0203b0155604bfc2d26018420366425bd80c18d99e40982b018bc0c68406f1033c31040a0a9fc00d5833d8022800ad141f29039f31390a004545b9c80313052b002a541a6d03e1700dce012cc190b031d803abe00f64009982cd7000b00c95019fd003a2041c80f89014ed82d98031be00cfc46f2099890527406258033e835dc013c408cb5dab8831e016af00cde41df782100067c4052500f4e83e8c0447c02aac59b08847c04d040cb40203f018ba04cd200d300ba2006fd06f5e018a41bb903f430534009ae001bd81ee0080e020500e80000e0040000200c000388000040680e80001200001000006018008010040140680d00401406810004030030210020040181303202c0480501c00403000000064008000020c00a00003000c1402a0000300d8150000080900f0720000400a0a00081c0040000380280200c0000081a074014150170f200c000030020001280001009816022000024008240aa2240502c04e000018020200041182500c0000b8000000000c80605c0040000100a0140b8180040080380500000c0080100203000004000014020070000200000603c0a4010000120443602f00a0000680100800c018020020740f00000000410805002008008160000140100e00e12c0200800e0080283100000800002000040038050100000c811000048000190060380100500c0040001400402401803032004000000540100480106c0000180101404c070070020180080d0000402e00300a00c0082408a0000080900a0900201302603c0200001e0000b80000e02c0000001803812833002114038020160000781500e0fc0b00100c0240001b0040180080b050004028000100600181401a004058000120080080000001c0b0040120ec010000060000280300e02003052006014020010a417c06007004030018030380000800f01607c1700000000c04802000000068070800040000102e09c0080a034008038050620000000704c0300000d0000380b80a00c01c000010000b0018320200b01080601800c1c8000920b813001016020000040341641b8010100680001c0020080083000a0780c802 else 0xa0ae0554aed73c1efe81f5e0246c25ba40c9a000bf76ad40a51c11be8158903f5620bc58c4e42b9306f300c730414f0282a07338093b41df8026d703d980f62802f380cef080460fb701b9d814a004940c72700008039d503a06071b4030182f5b038720ee58585203c8616a4c0e6fc1d6403a5f058b40e83c0ed78299e002c007d0811ea814c500b0a078e001aa837df01f640779416180092807f860d2dc1bb4812a1016aa20d70176db094600b240f9c81a98b35fc0047e0b4a81e73020d70251e0b41c06dc80ba0080e0101d559a981870080e0101d40aa00407f0099c04b00203d02ebe071c0101c0203808680080e0101f81c0700080080e0101c0203d00700080f20903402fa82430080e00329d9b9804070080e0101c0203c02fba07520c0800203b000e0080f60c4700cb80255f05e4a0037c1bf900d0c0095e023c4131d835e7003ac0e5218bf202481032462443c1cf083190080f60aedc1c0bc373903300101f011d488742022ec061b407cf8286807440101c020380407d02d1a07504113804070080f2096b01de882b5a0781407b68089f81c8b024520cac0143d0341b045200e0ec1ac481f132340c0f9240e540281a0426e0744c0f9c83a8d04c500db68182004071b2f6c0f2b85789096c701a4404d640ab18346d03fdc2d00402e004074061e7274b01637803bb05108267c0203a03d5e01f900393805c4b35cb03aec03b00203c035530754e009d41a6683da0080ea10120413b01bd0080e4058ec15e801a930738a0e2dc157c008a307e68036a40458018c8039dc0bc4020380407666960101d59a0882ba266ece0ee141f7c8966b76926068840c460259104718032241f5f0853307ec80c7dc4d7603d10080e0101c58a8c0b6bf012a0101d0069804070080f804ff040480407d111aa04da007aa818e8009280991c19408012204b1008ab1ce54002b400fbc0dc4c1f333093c0161a099f4070802e55016362dd880442816b70680c0db281c4c83a4905b9c02d00203902f03048e6068d009c801f6201c42101a403bb810b2668460b0184ba481cf5167ee0457c0e958021e055b0224a0092501f9a016480bda808fc8307601cec072ec1b4800e62028820e15c079f0317f040ca0f8159a1e8214402f2605b4804838220f017e20bb080f7a01df405c280e4f801e201c2103ac6076c0203e01d960430601f00203a82e90080ea0f5b80a1081b60080e203d8c1891015be020c0101d803d4099be058e62380c0619000710594005d5406ae02c2100f280c604033080dcb611722a1fc17f1006d1611cc04d280b9004074007c6c0c8c1bd804070080e0101d80df00407d00b60101cc1bab0b7e4043f20d1601280040730314e02b440d500407a02a0202940203b80871131fa0dc00203c219ad045bc0a9381b5189c92034a00b8340) else (if i<3 then 0x41660fe00203882287033cc0414016790107502f40101c0203982510080e0101d0130a82aea06600101c0203804070080f2088440dbf820c0008fc0496c0982028fc0019a04580203d81a08639040b900203804070080ea0ae198e6f03c7c07876c0b4c5a5e3026766d3a084880a478335705bc0101c0203e827c603b1809bc4085003ae2076da0807c14180407e02b5405e1c0633b356606ac00b748199480426030222627012290b46306c0608d059b0101b3e01dc209ff5d9f300bc90201c0705409ec00f0803720101d81d0800be802bce0642c1c8004075600ec0ce8c165f8032100af006c6c185302e65072380210020380407e10100101c0203b82f8c01440101fc0d7004070080fe02248173804076055240fef9ca0d3173d76a00101d80cac009460559209bac13000407c04d88054a44ab081661015dc0e544148c0b5050322602610049e998e066a3c2db784a2380aff168fe0a7e80409031be02bb201a7d9a878119415c6809d2818a00407a10d20101c4093780460080e0101f01e26034ec042f408e74120f81e80080ff0b7880319806a0080ec06900203804072035e0101c41d900407404226c37445b19824b0080e6ed100203d00a0f05b660a2a8039d0036276c520469400a80407812fc20d9d01eed01290014280fe4c0f280407c026760f08c56d80407d04f000d2b4070700fd0080e004240203d82d6300a7c2239808800407f07b20101c0203804070080fe02efddb74088b002a360d90020380407204392032f8152d020347357606fd41f7500c7501e242dbb4052682ef401caa0bf3c0c16837c815e4a0268c066803d00080e20e31016480407e66cca0cd9017cf81b44071e0079200347001e10415c05a80203c0244c009c0101d814f4005d804a4e0fa800dd289d30080e0101ec03a80407f07a82066840e0004070080f2c6ac0203b09e0c01a8ec59340540800250572209cc0203804070080e0101f413f080090080e0101c0203d02f7b000d803a4814c3009b0080fc025c81ee101600080e0101e41c90023c405660101d4200a02d7a0401a0ff981b7c82773040980d1e807a5023f307084208441d6d82b0b051d42d77c15ba8953f0208e10178038889e2b0747e08c5817a58387204776ed50c126d012f206c6c0d24420180407206260101c0203933610080f2020e008c00407203712049c059e804076032842754409d00407707a7003e00203804070080f8e5cc0203f31410080e0101dc079409a1e029e6c4370179a80ed8013b203a08010089ca400a9c012344f26003f703c4a0611411ad00282019340c3188099800400343400600067b82d5a007160067011800209a32cae023ac169c31c71036b2029c40b66019950257e0313c0d86825d4004a40a3540160015f90672e0dca4185d8b72807d860ed69c46e0 else 0x1e3381bc0080e0101fc0e20004410265c0af1c158804070080fa02df0160902160080fa0d51c07fa01fd0080f00f26c416e00b30080e0101c0203804070080f2033019aaa80ebf00a30cd1041d88010f10735c0eac0203c8b55e026280867c0124805a0080f4cd3cc1dd98b4f00539ac256017ff01e02028bc0c2701d7803657009be0d8a809c60052d02dc60c17c1b430386f05d4205dd0198c0167216f4000a90180d82a1f05bf20b630055f03385071560267c07188302000fc0035f01ad63b48c04a7601d8c051d006c963952042280bfe03989064d20fd70046f832980768c06af5dac1017c3048d00a0181ace8208d021b40187d8e65021e3b344809598090eb9c9e027900c57c1cbf8236404eac069f01a4302a89001ea044619b4480653033e80a8f419540164306dce2d6d80ffc02253029b80d8400f5902050080e2055e803c603bc013b82e72d01a113b73d059170b73c0cec3371506f00ed2ec127883cb702ec20217c1afbb362553c38ed33413d302be2060640fdc419780296d079fe0a32800550374f769b80ba0c180781dde04e2009c0c027d0323a07fbe04049db0f83e96026f403fbc06cd022e708000e7375c19781fcb072cac65901ed83340005a9a0408c486a0000c01efc0f78c19dd01805014cc2246806c200dd6007202d8ac4096008c1023aa20a3c10d60043d15baa066d4048f828980540e079a006fd83f2366e420c38c168b8ab2121bf68639c0e6c8254c051760c901cd25801fa023dc0cb101d9901410010deed0c4193b017eb02978079c400b9080a900068086d817d6025ed06b800f04c1a1b0333e0138e06a385ad4822c505c520595c148082024056dc20cc40fc701d3c00fee09db41e2b02790080e600a40203b31cb002e6726f141627b08d4005ed46700203802422034c00a480203802853028e60edfc0ddbb33fd025a4088a8103b019c5065dae730c4baa00fa3045e0101ec13ea0b642052e0101ec1d8200b9c07c6a083c01d35813e912c900e2180ac903cd302f64c046c0a7503a78062c006b40203d03fa500c80101e41c6c83f1500e4ae22b400a00407504980101c02039830de16d20101d803580407d0509a060c0203a81c52633d8054fc081f81c90080e0101f40876835050544e0dac81911001b604b9205c40203e8351607a46007380fd83b700080f600c00203d025b6108c6030b00b1480d6702e0ac69080c7f8b48d62d6ce099c14d80407c02860101c01eb80407b05dce0925019a28080903e460b8f001100407a))
def f3077uH1_37 (h : Nat) : Option (Nat × Nat) := lookupWord 414 1440 11 19 11 4 f3077uH1_37F h
def f3077uL40F (i : Nat) : Nat := 0xc0380c0200145241031dc32f4e2ada40b80d2cbe29030880419e2ed8401a517c52c8010678bb69021834a2f8a438065c0678bb69020834bc74998e68001ff46540bfeb4a817fd39502ffa52a05ff46540
def f3077uL40 : PackingT := (5,2,7,9,f3077uL40F)
def f3077uH1_40F (i : Nat) : Nat := 0x27286700f9414c43d48e900f90000d84d88d7025c1a1407b0752090027341e3802104201f003e007cf06d605b019a0e7b0aa4017c71588c70cda07a419206de0dc01f2023807c61c201f003e007cb092a0f803e704000f801f1420807c00f801f003e4846202920c403e007ca0bc6067812807c40c460e00027be700f841801b0f029c0982d9fc30f001b05c014700f807ca09ea19403e007c00f8e045426a03a206e01f2038007c105a4098c11807c00f94e25c44c81ce097616003e102c60b5a11640c782810ac0d9b039807c201601f0c21007c313b601b474580c00f801f003e007c00f921b300ae8776036a0c244fb0e660bfe38e80b807c00f8c1a803e506900f8000cc0d304480a4a17241a007ce1348d94c35e04a20f601f1813881d00f801f101e807c30a9e0fc03e7b1c80dec0ac03e781000f801f281da857d01a01f1004800ef0ec01f003e106350c86d91812007c10a1404ec11002ac04021e0405007cf087a164c3a007c37c201f041aa3e660b6a0bc0396871100f8e7342e807c00f901e6804583900080b0003060102020005070000010002000708020100050204020505020800030402060602070400120211000000000000
def f3077uH1_40 (h : Nat) : Option (Nat × Nat) := lookupWord 50 210 8 15 7 4 f3077uH1_40F h
def f3077uLevels : Nat → PackingT
  | 24 => f3077uL24
  | 27 => f3077uL27
  | 28 => f3077uL28
  | 30 => f3077uL30
  | 31 => f3077uL31
  | 33 => f3077uL33
  | 34 => f3077uL34
  | 37 => f3077uL37
  | 40 => f3077uL40
  | _ => emptyPackingT
def f3077uIdx0 : Nat → Nat → Option (Nat × Nat)
  | 27 => f3077uH0_27
  | 30 => f3077uH0_30
  | 31 => f3077uH0_31
  | 33 => f3077uH0_33
  | 34 => f3077uH0_34
  | 37 => f3077uH0_37
  | _ => fun _ => none
def f3077uIdx1 : Nat → Nat → Option (Nat × Nat)
  | 31 => f3077uH1_31
  | 34 => f3077uH1_34
  | 37 => f3077uH1_37
  | 40 => f3077uH1_40
  | _ => fun _ => none
abbrev bkU := blockU f3077uLevels f3077uIdx0 f3077uIdx1
abbrev bmU (k tm s a b : Nat) := @blockU_merge f3077uLevels f3077uIdx0 f3077uIdx1 k tm s a b
set_option maxHeartbeats 0 in
theorem c24_0 : bkU 8 0 0 2=true:=chunkBlockU (ar:=9) (by decide +kernel)
theorem a24 : bkU 8 0 0 2 = true := c24_0
set_option maxHeartbeats 0 in
theorem c27_0 : bkU 9 0 0 48=true:=cellsBlockU (ar:=10) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c27_48 : bkU 9 0 48 25=true:=cellsBlockU (ar:=10) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
theorem a27 : bkU 9 0 0 73 = true := (bmU 9 0 0 48 25 c27_0 c27_48)
set_option maxHeartbeats 0 in
theorem c28_0 : bkU 9 1 0 10=true:=chunkBlockU (ar:=9) (by decide +kernel)
theorem a28 : bkU 9 1 0 10 = true := c28_0
set_option maxHeartbeats 0 in
theorem c30_0 : bkU 10 0 0 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_48 : bkU 10 0 48 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_96 : bkU 10 0 96 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_144 : bkU 10 0 144 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_192 : bkU 10 0 192 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_240 : bkU 10 0 240 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_288 : bkU 10 0 288 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_336 : bkU 10 0 336 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_384 : bkU 10 0 384 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_432 : bkU 10 0 432 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_480 : bkU 10 0 480 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_528 : bkU 10 0 528 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_576 : bkU 10 0 576 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c30_624 : bkU 10 0 624 27=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
theorem a30 : bkU 10 0 0 651 = true := (bmU 10 0 0 336 315 (bmU 10 0 0 144 192 (bmU 10 0 0 48 96 c30_0 (bmU 10 0 48 48 48 c30_48 c30_96)) (bmU 10 0 144 96 96 (bmU 10 0 144 48 48 c30_144 c30_192) (bmU 10 0 240 48 48 c30_240 c30_288))) (bmU 10 0 336 144 171 (bmU 10 0 336 48 96 c30_336 (bmU 10 0 384 48 48 c30_384 c30_432)) (bmU 10 0 480 96 75 (bmU 10 0 480 48 48 c30_480 c30_528) (bmU 10 0 576 48 27 c30_576 c30_624))))
set_option maxHeartbeats 0 in
theorem c31_0 : bkU 10 1 0 2=true:=chunkBlockU (ar:=9) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c31_2 : bkU 10 1 2 48=true:=cellsBlockU (ar:=10) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c31_50 : bkU 10 1 50 48=true:=cellsBlockU (ar:=10) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c31_98 : bkU 10 1 98 48=true:=cellsBlockU (ar:=10) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c31_146 : bkU 10 1 146 48=true:=cellsBlockU (ar:=10) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c31_194 : bkU 10 1 194 48=true:=cellsBlockU (ar:=10) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c31_242 : bkU 10 1 242 48=true:=cellsBlockU (ar:=10) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c31_290 : bkU 10 1 290 48=true:=cellsBlockU (ar:=10) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c31_338 : bkU 10 1 338 48=true:=cellsBlockU (ar:=10) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c31_386 : bkU 10 1 386 48=true:=cellsBlockU (ar:=10) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c31_434 : bkU 10 1 434 48=true:=cellsBlockU (ar:=10) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c31_482 : bkU 10 1 482 48=true:=cellsBlockU (ar:=10) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c31_530 : bkU 10 1 530 19=true:=cellsBlockU (ar:=10) (d:=1) ⟨kU (by decide +kernel),kU (by decide +kernel)⟩
theorem a31 : bkU 10 1 0 549 = true := (bmU 10 1 0 242 307 (bmU 10 1 0 98 144 (bmU 10 1 0 2 96 c31_0 (bmU 10 1 2 48 48 c31_2 c31_50)) (bmU 10 1 98 48 96 c31_98 (bmU 10 1 146 48 48 c31_146 c31_194))) (bmU 10 1 242 144 163 (bmU 10 1 242 48 96 c31_242 (bmU 10 1 290 48 48 c31_290 c31_338)) (bmU 10 1 386 96 67 (bmU 10 1 386 48 48 c31_386 c31_434) (bmU 10 1 482 48 19 c31_482 c31_530))))
set_option maxHeartbeats 0 in
theorem c33_0 : bkU 11 0 0 48=true:=cellsBlockU (ar:=12) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c33_48 : bkU 11 0 48 48=true:=cellsBlockU (ar:=12) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c33_96 : bkU 11 0 96 48=true:=cellsBlockU (ar:=12) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c33_144 : bkU 11 0 144 48=true:=cellsBlockU (ar:=12) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c33_192 : bkU 11 0 192 48=true:=cellsBlockU (ar:=12) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c33_240 : bkU 11 0 240 48=true:=cellsBlockU (ar:=12) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c33_288 : bkU 11 0 288 48=true:=cellsBlockU (ar:=12) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c33_336 : bkU 11 0 336 48=true:=cellsBlockU (ar:=12) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c33_384 : bkU 11 0 384 48=true:=cellsBlockU (ar:=12) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c33_432 : bkU 11 0 432 45=true:=cellsBlockU (ar:=12) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
theorem a33 : bkU 11 0 0 477 = true := (bmU 11 0 0 240 237 (bmU 11 0 0 96 144 (bmU 11 0 0 48 48 c33_0 c33_48) (bmU 11 0 96 48 96 c33_96 (bmU 11 0 144 48 48 c33_144 c33_192))) (bmU 11 0 240 96 141 (bmU 11 0 240 48 48 c33_240 c33_288) (bmU 11 0 336 48 93 c33_336 (bmU 11 0 384 48 45 c33_384 c33_432))))
set_option maxHeartbeats 0 in
theorem c34_0 : bkU 11 1 0 1=true:=chunkBlockU (ar:=9) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c34_1 : bkU 11 1 1 48=true:=cellsBlockU (ar:=10) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_49 : bkU 11 1 49 48=true:=cellsBlockU (ar:=10) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_97 : bkU 11 1 97 48=true:=cellsBlockU (ar:=10) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_145 : bkU 11 1 145 31=true:=cellsBlockU (ar:=10) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_176 : bkU 11 1 176 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_224 : bkU 11 1 224 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_272 : bkU 11 1 272 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_320 : bkU 11 1 320 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_368 : bkU 11 1 368 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_416 : bkU 11 1 416 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_464 : bkU 11 1 464 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_512 : bkU 11 1 512 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_560 : bkU 11 1 560 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_608 : bkU 11 1 608 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_656 : bkU 11 1 656 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_704 : bkU 11 1 704 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_752 : bkU 11 1 752 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_800 : bkU 11 1 800 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_848 : bkU 11 1 848 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_896 : bkU 11 1 896 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_944 : bkU 11 1 944 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c34_992 : bkU 11 1 992 39=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
theorem a34 : bkU 11 1 0 1031 = true := (bmU 11 1 0 464 567 (bmU 11 1 0 176 288 (bmU 11 1 0 49 127 (bmU 11 1 0 1 48 c34_0 c34_1) (bmU 11 1 49 48 79 c34_49 (bmU 11 1 97 48 31 c34_97 c34_145))) (bmU 11 1 176 144 144 (bmU 11 1 176 48 96 c34_176 (bmU 11 1 224 48 48 c34_224 c34_272)) (bmU 11 1 320 48 96 c34_320 (bmU 11 1 368 48 48 c34_368 c34_416)))) (bmU 11 1 464 288 279 (bmU 11 1 464 144 144 (bmU 11 1 464 48 96 c34_464 (bmU 11 1 512 48 48 c34_512 c34_560)) (bmU 11 1 608 48 96 c34_608 (bmU 11 1 656 48 48 c34_656 c34_704))) (bmU 11 1 752 144 135 (bmU 11 1 752 48 96 c34_752 (bmU 11 1 800 48 48 c34_800 c34_848)) (bmU 11 1 896 48 87 c34_896 (bmU 11 1 944 48 39 c34_944 c34_992)))))
set_option maxHeartbeats 0 in
theorem c37_0 : bkU 12 1 0 42=true:=cellsBlockU (ar:=10) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c37_42 : bkU 12 1 42 48=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
set_option maxHeartbeats 0 in
theorem c37_90 : bkU 12 1 90 34=true:=cellsBlockU (ar:=11) (d:=2) ⟨⟨kU (by decide +kernel),kU (by decide +kernel)⟩,⟨kU (by decide +kernel),kU (by decide +kernel)⟩⟩
theorem a37 : bkU 12 1 0 124 = true := (bmU 12 1 0 42 82 c37_0 (bmU 12 1 42 48 34 c37_42 c37_90))
set_option maxHeartbeats 0 in
theorem c40_0 : bkU 13 1 0 4=true:=chunkBlockU (ar:=10) (by decide +kernel)
set_option maxHeartbeats 0 in
theorem c40_4 : bkU 13 1 4 1=true:=chunkBlockU (ar:=9) (by decide +kernel)
theorem a40 : bkU 13 1 0 5 = true := (bmU 13 1 0 4 1 c40_0 c40_4)
theorem tables3077u : ∀ k ≤ 13, ∀ tm ≤ 1, blockU f3077uLevels f3077uIdx0 f3077uIdx1 k tm 0 (f3077uLevels (3*k+tm)).1 = true := by
  intro k hk tm ht
  interval_cases k <;> interval_cases tm
  · exact (rfl : blockU f3077uLevels f3077uIdx0 f3077uIdx1 0 0 0 0 = true)
  · exact (rfl : blockU f3077uLevels f3077uIdx0 f3077uIdx1 0 1 0 0 = true)
  · exact (rfl : blockU f3077uLevels f3077uIdx0 f3077uIdx1 1 0 0 0 = true)
  · exact (rfl : blockU f3077uLevels f3077uIdx0 f3077uIdx1 1 1 0 0 = true)
  · exact (rfl : blockU f3077uLevels f3077uIdx0 f3077uIdx1 2 0 0 0 = true)
  · exact (rfl : blockU f3077uLevels f3077uIdx0 f3077uIdx1 2 1 0 0 = true)
  · exact (rfl : blockU f3077uLevels f3077uIdx0 f3077uIdx1 3 0 0 0 = true)
  · exact (rfl : blockU f3077uLevels f3077uIdx0 f3077uIdx1 3 1 0 0 = true)
  · exact (rfl : blockU f3077uLevels f3077uIdx0 f3077uIdx1 4 0 0 0 = true)
  · exact (rfl : blockU f3077uLevels f3077uIdx0 f3077uIdx1 4 1 0 0 = true)
  · exact (rfl : blockU f3077uLevels f3077uIdx0 f3077uIdx1 5 0 0 0 = true)
  · exact (rfl : blockU f3077uLevels f3077uIdx0 f3077uIdx1 5 1 0 0 = true)
  · exact (rfl : blockU f3077uLevels f3077uIdx0 f3077uIdx1 6 0 0 0 = true)
  · exact (rfl : blockU f3077uLevels f3077uIdx0 f3077uIdx1 6 1 0 0 = true)
  · exact (rfl : blockU f3077uLevels f3077uIdx0 f3077uIdx1 7 0 0 0 = true)
  · exact (rfl : blockU f3077uLevels f3077uIdx0 f3077uIdx1 7 1 0 0 = true)
  · exact a24
  · exact (rfl : blockU f3077uLevels f3077uIdx0 f3077uIdx1 8 1 0 0 = true)
  · exact a27
  · exact a28
  · exact a30
  · exact a31
  · exact a33
  · exact a34
  · exact (rfl : blockU f3077uLevels f3077uIdx0 f3077uIdx1 12 0 0 0 = true)
  · exact a37
  · exact (rfl : blockU f3077uLevels f3077uIdx0 f3077uIdx1 13 0 0 0 = true)
  · exact a40

def ones3077 : Sig := neg zero
def evalSig3077 (w : List Sig) (p : Fin 26) : Sig :=
  if p.val = 25 then ones3077 else w.getD p.val zero
def gateVal3077 (w : List Sig) (g : Fin 3 × Fin 26 × Fin 26) : Sig :=
  if g.1.val = 0 then bin false (evalSig3077 w g.2.1) (evalSig3077 w g.2.2)
  else if g.1.val = 1 then bin true (evalSig3077 w g.2.1) (evalSig3077 w g.2.2)
  else neg (evalSig3077 w g.2.1)
def exec3077 (gs : List (Fin 3 × Fin 26 × Fin 26)) (w : List Sig) : List Sig :=
  gs.foldl (fun w g => w ++ [gateVal3077 w g]) w

theorem bit_ones3077 (r : Row) : bit r ones3077 = true := by unfold ones3077; rw [bit_neg]; simp [bit, zero]
theorem not_proper_ones3077 : ¬proper ones3077 := by unfold proper ones3077; decide +kernel

theorem bit_evalSig3077 (r : Row) (w : List Sig) (p : Fin 26) :
    bit r (evalSig3077 w p) = if p.val = 25 then true else (w.map (bit r)).getD p.val false := by
  unfold evalSig3077
  split_ifs with h
  · exact bit_ones3077 r
  · exact (b_read r w p.val).symm

theorem bit_gateVal3077 (r : Row) (w : List Sig) (g : Fin 3 × Fin 26 × Fin 26) :
    bit r (gateVal3077 w g) =
      (let rd := fun (x : List Bool) (p : Fin 26) => if p.val = 25 then true else x.getD p.val false
       if g.1.val = 0 then rd (w.map (bit r)) g.2.1 && rd (w.map (bit r)) g.2.2
       else if g.1.val = 1 then rd (w.map (bit r)) g.2.1 || rd (w.map (bit r)) g.2.2
       else !rd (w.map (bit r)) g.2.1) := by
  unfold gateVal3077
  split_ifs <;> simp only [bit_bin, bit_neg, bit_evalSig3077, ite_true, Bool.false_eq_true, ite_false]

theorem exec3077_bits (r : Row) (gs : List (Fin 3 × Fin 26 × Fin 26)) (w : List Sig) :
    (exec3077 gs w).map (bit r) =
      List.foldl (fun (x13 : List Bool) (x14 : Fin 3 × Fin 26 × Fin 26) =>
        let rd := fun (x12 : List Bool) (x13 : Fin 26) => if x13.val = 25 then true else x12.getD x13.val false
        x13 ++ [if x14.1.val = 0 then rd x13 x14.2.1 && rd x13 x14.2.2
                else if x14.1.val = 1 then rd x13 x14.2.1 || rd x13 x14.2.2
                else !rd x13 x14.2.1]) (w.map (bit r)) gs := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [exec3077, List.foldl_cons] at ih ⊢
    rw [ih, List.map_append, List.map_cons, List.map_nil, bit_gateVal3077]

theorem evalSig3077_rep (w : List Sig) (p : Fin 26) : represented w (evalSig3077 w p) := by
  unfold evalSig3077
  split_ifs
  · exact Or.inr not_proper_ones3077
  · exact get_rep w p.val

theorem neg_rep3077 {w a} (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
  by_cases hp : proper a
  · exact Or.inr (Or.inl ⟨a, ha.resolve_right (fun h => h hp), hp, rfl⟩)
  · left; right
    intro hn
    unfold proper at hn hp
    rcases hn with ⟨h1, h2⟩
    apply hp
    refine ⟨fun e => h2 (by rw [e]; decide +kernel), fun e => h1 (by rw [e]; decide +kernel)⟩

theorem gateVal3077_wit (w : List Sig) (g : Fin 3 × Fin 26 × Fin 26) :
    represented w (gateVal3077 w g) ∨ witness w (gateVal3077 w g) := by
  unfold gateVal3077
  split_ifs
  · exact bin_rep false (evalSig3077_rep w g.2.1) (evalSig3077_rep w g.2.2)
  · exact bin_rep true (evalSig3077_rep w g.2.1) (evalSig3077_rep w g.2.2)
  · exact neg_rep3077 (evalSig3077_rep w g.2.1)

theorem extract3077 (gs : List (Fin 3 × Fin 26 × Fin 26)) (w : List Sig) {z : Sig}
    (pz : proper z) (hm : z ∈ exec3077 gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live z k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil =>
    exact ⟨0, 0, {z}, by simp, Live.stop pz, fun a ha => by simpa [exec3077, Finset.mem_singleton.mp ha] using hm⟩
  | cons g gs ih =>
    obtain ⟨k, t, S, hk, run, sub⟩ := ih (w ++ [gateVal3077 w g]) hm
    obtain ⟨k', t', S', hk', run', sub'⟩ := pull_gate run (gateVal3077_wit w g) sub
    exact ⟨k', t', S', by simp; omega, run', sub'⟩

def seed9 : Sig := bin true (inputs.getD 0 zero) (inputs.getD 4 zero)
def w10 (j : Fin 9) : Sig := bin true seed9 (inputs.getD j.val zero)
def fam3077 (j : Fin 9) : List Sig := inputs ++ [seed9, w10 j]

def witTable3077 (j i : Fin 9) : Row × Row :=
  let (a, b) := match j.val, i.val with
    | 2, 2 => (9,13)
    | 3, 3 => (5,13)
    | 6, 6 => (18,82)
    | 7, 7 => (5,133)
    | 8, 8 => (9,265)
    | _, 0 => (16,17)
    | _, 1 => (1,3)
    | _, 2 => (2,6)
    | _, 3 => (4,12)
    | _, 4 => (1,17)
    | _, 5 => (1,33)
    | _, 6 => (2,66)
    | _, 7 => (4,132)
    | _, _ => (8,264)
  (Fin.ofNat 512 a, Fin.ofNat 512 b)

theorem wit3077_ok :
    (List.finRange 9).all (fun j => (List.finRange 9).all (fun i =>
      let p := witTable3077 j i
      (bit p.1 graph != bit p.2 graph) &&
      (fam3077 j).all (fun w => w == inputs.getD i.val zero || bit p.1 w == bit p.2 w))) = true := by
  decide +kernel

theorem inputs_sub_3077 {j k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ fam3077 j) :
    inputs.toFinset ⊆ S := by
  intro v hv
  have hm := List.mem_toFinset.mp hv
  rw [← input_list, List.mem_ofFn] at hm
  obtain ⟨i, rfl⟩ := hm
  have hj := List.all_eq_true.mp wit3077_ok j (List.mem_finRange j)
  have hh := List.all_eq_true.mp hj i (List.mem_finRange i)
  simp only [Bool.and_eq_true, bne_iff_ne] at hh
  have h2' := List.all_eq_true.mp hh.2
  exact raw_required h _ _ sub (witTable3077 j i).1 (witTable3077 j i).2 hh.1
    (fun w hw hn => by
      have ha := h2' w hw
      simp only [Bool.or_eq_true, beq_iff_eq] at ha
      exact ha.resolve_left hn)

def col17 : ColumnInfo := (17, 0, 494, 0, 11)
def pool17 : BoundPool := ⟨subcube 17 0, 11, 0, vars 511⟩

theorem col17_valid : ValidPool (vars 511) graph pool17 := by
  have hgd := geomdead
  simp only [graphValid, Bool.and_eq_true, List.all_eq_true] at hgd
  have hmem : col17 ∈ dead.cols.values := List.contains_iff_mem.mp (by decide +kernel : dead.cols.values.contains col17 = true)
  have hslice := col_sound col17 (boundsBefore known383) (before_sound known383 valid383) (hgd.1.2 col17 hmem)
  have htgt : chartGoal dead.mask = graph := by decide +kernel
  rw [htgt] at hslice
  exact materialize_sound (cs := []) hslice rfl

theorem noSeed9_base : Impossible graph 13 (seed9 :: inputs).toFinset := by
  have heq : choiceVal (0, seed9, seed9) = seed9 := by
    change bin false seed9 seed9 = seed9; unfold bin; exact BitVec.and_self
  have hnd : (choiceVal (0, seed9, seed9) :: inputs).Nodup := by
    rw [heq]; exact of_decide_eq_true (by decide +kernel : decide (seed9 :: inputs).Nodup = true)
  have hcut : scalarPoolCut pool17 13 inputs (0, seed9, seed9) = true := by decide +kernel
  have h := scalarPoolCut_sound col17_valid hnd hcut
  rwa [heq] at h

theorem noSeed9_ext_j (j : Fin 9)
    (heq : choiceVal (0, w10 j, w10 j) = w10 j)
    (hnd0 : decide (w10 j :: seed9 :: inputs).Nodup = true)
    (hcut : scalarPoolCut pool17 13 (seed9 :: inputs) (0, w10 j, w10 j) = true) :
    Impossible graph 13 (w10 j :: seed9 :: inputs).toFinset := by
  have hnd : (choiceVal (0, w10 j, w10 j) :: seed9 :: inputs).Nodup := by
    rw [heq]; exact of_decide_eq_true hnd0
  have h := scalarPoolCut_sound col17_valid hnd hcut
  rwa [heq] at h

theorem noSeed9_ext (j : Fin 9) (hj0 : j.val ≠ 0) (hj4 : j.val ≠ 4) :
    Impossible graph 13 (w10 j :: seed9 :: inputs).toFinset := by
  fin_cases j
  · exact False.elim (hj0 rfl)
  · exact noSeed9_ext_j ⟨1, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact noSeed9_ext_j ⟨2, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact noSeed9_ext_j ⟨3, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact False.elim (hj4 rfl)
  · exact noSeed9_ext_j ⟨5, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact noSeed9_ext_j ⟨6, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact noSeed9_ext_j ⟨7, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · exact noSeed9_ext_j ⟨8, by decide⟩ (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rootU_imp (idx : Nat) (hi : idx < 5) :
    ImpossibleU graph 13 1 (stateSetT f3077uLevels 40 idx).toFinset := by
  have hall := forestU_all f3077uLevels f3077uIdx0 f3077uIdx1 13 (boundsBefore known383)
    (before_sound known383 valid383) geomdead tables3077u 13 (by decide) 1 (by decide) idx hi
  have htgt : targetOf dead = graph := by decide +kernel
  rwa [htgt] at hall

theorem perm1_ok : autoOK graph ((dead.autos.getD 1 []).map swapRows) = true := by decide +kernel

theorem no3077_pos : ImpossibleU graph 13 1 inputs.toFinset := by
  have h := rootU_imp 4 (by decide)
  have hs : sameWords (stateSetT f3077uLevels 40 4) inputs = true := by decide +kernel
  rwa [sameWords_sound hs] at h

theorem no3077_keep0 (j : Fin 9) (hj0 : j.val ≠ 0) (hj4 : j.val ≠ 4) :
    ImpossibleU graph 13 1 (inputs ++ [w10 j]).toFinset := by
  fin_cases j
  · exact False.elim (hj0 rfl)
  · have h := rootU_imp 0 (by decide)
    have hs : sameWords (stateSetT f3077uLevels 40 0) (inputs ++ [w10 ⟨1,by decide⟩]) = true := by decide +kernel
    rwa [sameWords_sound hs] at h
  · have h := rootU_imp 1 (by decide)
    have hs : sameWords (stateSetT f3077uLevels 40 1) (inputs ++ [w10 ⟨2,by decide⟩]) = true := by decide +kernel
    rwa [sameWords_sound hs] at h
  · have h := rootU_imp 2 (by decide)
    have hs : sameWords (stateSetT f3077uLevels 40 2) (inputs ++ [w10 ⟨3,by decide⟩]) = true := by decide +kernel
    rwa [sameWords_sound hs] at h
  · exact False.elim (hj4 rfl)
  · have h := rotate_excludedU (rootU_imp 0 (by decide)) ((dead.autos.getD 1 []).map swapRows) perm1_ok
    have hs : sameWords ((stateSetT f3077uLevels 40 0).map (movedWord ((dead.autos.getD 1 []).map swapRows).reverse)) (inputs ++ [w10 ⟨5,by decide⟩]) = true := by decide +kernel
    rwa [sameWords_sound hs] at h
  · have h := rootU_imp 3 (by decide)
    have hs : sameWords (stateSetT f3077uLevels 40 3) (inputs ++ [w10 ⟨6,by decide⟩]) = true := by decide +kernel
    rwa [sameWords_sound hs] at h
  · have h := rotate_excludedU (rootU_imp 3 (by decide)) ((dead.autos.getD 1 []).map swapRows) perm1_ok
    have hs : sameWords ((stateSetT f3077uLevels 40 3).map (movedWord ((dead.autos.getD 1 []).map swapRows).reverse)) (inputs ++ [w10 ⟨7,by decide⟩]) = true := by decide +kernel
    rwa [sameWords_sound hs] at h
  · have h := rotate_excludedU (rootU_imp 1 (by decide)) ((dead.autos.getD 1 []).map swapRows) perm1_ok
    have hs : sameWords ((stateSetT f3077uLevels 40 1).map (movedWord ((dead.autos.getD 1 []).map swapRows).reverse)) (inputs ++ [w10 ⟨8,by decide⟩]) = true := by decide +kernel
    rwa [sameWords_sound hs] at h

theorem kill3077 {j : Fin 9} {k t S} (hk : k ≤ 13) (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ fam3077 j) : False := by
  have haveIn := inputs_sub_3077 h sub
  by_cases hj0 : j.val = 0
  · have hw : w10 j = seed9 := by
      have : j = ⟨0, by decide⟩ := Fin.ext hj0; subst this; decide +kernel
    by_cases hs : seed9 ∈ S
    · have eqS : S = (seed9 :: inputs).toFinset := by
        apply Finset.Subset.antisymm
        · intro v hv
          have hm := sub v hv
          simp only [fam3077, hw, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hm
          rcases hm with hm | rfl | rfl <;> simp [*]
        · intro v hv
          simp only [List.toFinset_cons, Finset.mem_insert] at hv
          rcases hv with rfl | hv
          · exact hs
          · exact haveIn hv
      exact noSeed9_base k t hk (eqS ▸ h)
    · have eqS : S = inputs.toFinset := by
        apply Finset.Subset.antisymm
        · intro v hv
          have hm := sub v hv
          simp only [fam3077, hw, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hm
          rcases hm with hm | rfl | rfl
          · exact List.mem_toFinset.mpr hm
          · exact False.elim (hs hv)
          · exact False.elim (hs hv)
        · exact haveIn
      exact no3077_pos k t hk (fun h0 => by cases h0) (eqS ▸ h)
  · by_cases hj4 : j.val = 4
    · have hw : w10 j = seed9 := by
        have : j = ⟨4, by decide⟩ := Fin.ext hj4; subst this; decide +kernel
      by_cases hs : seed9 ∈ S
      · have eqS : S = (seed9 :: inputs).toFinset := by
          apply Finset.Subset.antisymm
          · intro v hv
            have hm := sub v hv
            simp only [fam3077, hw, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hm
            rcases hm with hm | rfl | rfl <;> simp [*]
          · intro v hv
            simp only [List.toFinset_cons, Finset.mem_insert] at hv
            rcases hv with rfl | hv
            · exact hs
            · exact haveIn hv
        exact noSeed9_base k t hk (eqS ▸ h)
      · have eqS : S = inputs.toFinset := by
          apply Finset.Subset.antisymm
          · intro v hv
            have hm := sub v hv
            simp only [fam3077, hw, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hm
            rcases hm with hm | rfl | rfl
            · exact List.mem_toFinset.mpr hm
            · exact False.elim (hs hv)
            · exact False.elim (hs hv)
          · exact haveIn
        exact no3077_pos k t hk (fun h0 => by cases h0) (eqS ▸ h)
    · by_cases hs : seed9 ∈ S
      · by_cases hw : w10 j ∈ S
        · have eqS : S = (w10 j :: seed9 :: inputs).toFinset := by
            apply Finset.Subset.antisymm
            · intro v hv
              have hm := sub v hv
              simp only [fam3077, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hm
              rcases hm with hm | rfl | rfl <;> simp [*]
            · intro v hv
              simp only [List.toFinset_cons, Finset.mem_insert] at hv
              rcases hv with rfl | rfl | hv
              · exact hw
              · exact hs
              · exact haveIn hv
          exact noSeed9_ext j hj0 hj4 k t hk (eqS ▸ h)
        · have eqS : S = (seed9 :: inputs).toFinset := by
            apply Finset.Subset.antisymm
            · intro v hv
              have hm := sub v hv
              simp only [fam3077, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hm
              rcases hm with hm | rfl | rfl
              · simp [hm]
              · simp
              · exact False.elim (hw hv)
            · intro v hv
              simp only [List.toFinset_cons, Finset.mem_insert] at hv
              rcases hv with rfl | hv
              · exact hs
              · exact haveIn hv
          exact noSeed9_base k t hk (eqS ▸ h)
      · by_cases hw : w10 j ∈ S
        · have eqS : S = (inputs ++ [w10 j]).toFinset := by
            apply Finset.Subset.antisymm
            · intro v hv
              have hm := sub v hv
              simp only [fam3077, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hm
              rcases hm with hm | rfl | rfl
              · exact List.mem_toFinset.mpr (List.mem_append_left _ hm)
              · exact False.elim (hs hv)
              · exact List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_singleton_self _))
            · intro v hv
              have hm := List.mem_toFinset.mp hv
              simp only [List.mem_append, List.mem_singleton] at hm
              rcases hm with hm | rfl
              · exact haveIn (List.mem_toFinset.mpr hm)
              · exact hw
          exact no3077_keep0 j hj0 hj4 k t hk (fun h0 => by cases h0) (eqS ▸ h)
        · have eqS : S = inputs.toFinset := by
            apply Finset.Subset.antisymm
            · intro v hv
              have hm := sub v hv
              simp only [fam3077, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hm
              rcases hm with hm | rfl | rfl
              · exact List.mem_toFinset.mpr hm
              · exact False.elim (hs hv)
              · exact False.elim (hw hv)
            · exact haveIn
          exact no3077_pos k t hk (fun h0 => by cases h0) (eqS ▸ h)

theorem sample_eq_testBit (r : Row) (i : Fin 9) : sample r i = r.val.testBit i.val := by
  fin_cases i
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem bit_seed9 (r : Row) : bit r seed9 = (sample r 0 || sample r 4) := by
  simp only [seed9, bit_bin, sample, ite_true]; rfl
theorem edge3077_eq (r : Row) :
    ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85].any fun (x14 : ℕ) =>
      r.val.testBit (Fin.ofNat 9 (x14 / 10)).val && r.val.testBit (Fin.ofNat 9 (x14 % 10)).val) = bit r graph := by
  rw [edge_table r]
  unfold edge
  simp only [sample_eq_testBit, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]; rfl

theorem step0_sub (x1 x2 : Fin 26) (h9 : x1.val = 9 ∨ x2.val = 9) (h1 : x1.val ≠ 25) (h2 : x2.val ≠ 25) :
    ∃ j : Fin 9, ∀ v ∈ (inputs ++ [seed9]) ++ [gateVal3077 (inputs ++ [seed9]) ((1 : Fin 3), x1, x2)], v ∈ fam3077 j := by
  have hlen : (inputs ++ [seed9]).length = 10 := by rw [List.length_append, ← input_list, List.length_ofFn]; rfl
  have hget9 : (inputs ++ [seed9]).getD 9 zero = seed9 := by
    have hli : inputs.length = 9 := by rw [← input_list, List.length_ofFn]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hli]
    simp
  have hgv : gateVal3077 (inputs ++ [seed9]) ((1 : Fin 3), x1, x2) =
      bin true (evalSig3077 (inputs ++ [seed9]) x1) (evalSig3077 (inputs ++ [seed9]) x2) := rfl
  have hbin_or : ∀ p : Fin 26, p.val ≠ 25 →
      ∃ j : Fin 9, bin true seed9 (evalSig3077 (inputs ++ [seed9]) p) = w10 j ∨
        bin true seed9 (evalSig3077 (inputs ++ [seed9]) p) = seed9 := by
    intro p hp
    unfold evalSig3077
    rw [if_neg hp]
    by_cases hlt : p.val < 9
    · refine ⟨⟨p.val, hlt⟩, Or.inl ?_⟩
      have hli : inputs.length = 9 := by rw [← input_list, List.length_ofFn]
      have hgp : (inputs ++ [seed9]).getD p.val zero = inputs.getD p.val zero := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
      rw [hgp]; rfl
    · refine ⟨⟨0, by decide⟩, Or.inr ?_⟩
      by_cases h9p : p.val = 9
      · rw [h9p, hget9]; decide +kernel
      · have hge : (inputs ++ [seed9]).length ≤ p.val := by omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
        change bin true seed9 zero = seed9
        decide +kernel
  have hpair : ∃ j : Fin 9, gateVal3077 (inputs ++ [seed9]) ((1 : Fin 3), x1, x2) = w10 j ∨
      gateVal3077 (inputs ++ [seed9]) ((1 : Fin 3), x1, x2) = seed9 := by
    rw [hgv]
    rcases h9 with h9 | h9
    · have he1 : evalSig3077 (inputs ++ [seed9]) x1 = seed9 := by
        unfold evalSig3077; rw [if_neg h1, h9, hget9]
      rw [he1]; exact hbin_or x2 h2
    · have he2 : evalSig3077 (inputs ++ [seed9]) x2 = seed9 := by
        unfold evalSig3077; rw [if_neg h2, h9, hget9]
      rw [he2, bin_comm]; exact hbin_or x1 h1
  obtain ⟨j, hj⟩ := hpair
  refine ⟨j, fun v hv => ?_⟩
  simp only [List.mem_append, List.mem_singleton] at hv
  rcases hv with (hv | rfl) | rfl
  · exact List.mem_append_left _ hv
  · exact List.mem_append_right _ (by simp)
  · rcases hj with hj | hj
    · rw [hj]; exact List.mem_append_right _ (by simp)
    · rw [hj]; exact List.mem_append_right _ (by simp)

theorem main3077 : ∀ (x1 x2 x3 : Fin (26 : ℕ)) (x4 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))),   x4.length ≤ (13 : ℕ) →     ↑x1 = (9 : ℕ) ∨ ↑x2 = (9 : ℕ) →       ↑x1 ≠ (25 : ℕ) →         ↑x2 ≠ (25 : ℕ) →           (∀ x9 < (9 : ℕ), ∃ x11 ∈ x4, ↑x11.2.1 = x9 ∨ ↑x11.2.2 = x9) →             ∃ x10 < (512 : ℕ),               have x11 : Fin (9 : ℕ) → Bool := fun (x11 : Fin (9 : ℕ)) => x10.testBit ↑x11;               have x12 : List Bool → Fin (26 : ℕ) → Bool := fun (x12 : List Bool) (x13 : Fin (26 : ℕ)) => if ↑x13 = (25 : ℕ) then Bool.true else x12.getD (↑x13) Bool.false;               have x13 : List Bool := List.foldl (fun (x13 : List Bool) (x14 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x13 ++ [if ↑x14.1 = (0 : ℕ) then x12 x13 x14.2.1 && x12 x13 x14.2.2 else if ↑x14.1 = (1 : ℕ) then x12 x13 x14.2.1 || x12 x13 x14.2.2 else !x12 x13 x14.2.1]) (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x1, x2) :: x4);               x13.getD (↑x3) Bool.false ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x14 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x14 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x14 % (10 : ℕ))) := by
  intro x1 x2 x3 x4 hlen h9 h1 h2 _
  by_contra hno
  push Not at hno
  let w0 : List Sig := (inputs ++ [seed9]) ++ [gateVal3077 (inputs ++ [seed9]) ((1 : Fin 3), x1, x2)]
  have goalEq : (exec3077 x4 w0).getD x3.val zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro m hm
    let r : Row := ⟨m, hm⟩
    change bit r ((exec3077 x4 w0).getD x3.val zero) = bit r graph
    rw [← b_read, exec3077_bits r x4 w0]
    have hbits0 : (inputs ++ [seed9]).map (bit r) = List.ofFn (fun i : Fin 9 => r.val.testBit i.val) ++ [r.val.testBit 0 || r.val.testBit 4] := by
      simp only [List.map_append, List.map_cons, List.map_nil, bit_seed9]
      rw [← sampled, show sample r = fun i : Fin 9 => r.val.testBit i.val from funext (sample_eq_testBit r)]; rfl
    have hw0 : w0.map (bit r) =
        List.foldl (fun (x13 : List Bool) (x14 : Fin 3 × Fin 26 × Fin 26) =>
          let rd := fun (x12 : List Bool) (x13 : Fin 26) => if x13.val = 25 then true else x12.getD x13.val false
          x13 ++ [if x14.1.val = 0 then rd x13 x14.2.1 && rd x13 x14.2.2
                  else if x14.1.val = 1 then rd x13 x14.2.1 || rd x13 x14.2.2
                  else !rd x13 x14.2.1])
          (List.ofFn (fun i : Fin 9 => r.val.testBit i.val) ++ [r.val.testBit 0 || r.val.testBit 4]) [((1 : Fin 3), x1, x2)] := by
      simp only [w0, List.map_append, List.map_cons, List.map_nil, bit_gateVal3077, List.foldl_cons, List.foldl_nil, hbits0]
    rw [hw0]
    have hx := Classical.byContradiction (hno m hm)
    exact hx.trans (edge3077_eq r)
  have out := get_rep (exec3077 x4 w0) x3.val
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  obtain ⟨k, t, S, hk, run, sub⟩ := extract3077 x4 w0 graph_proper targetIn
  obtain ⟨j, hj⟩ := step0_sub x1 x2 h9 h1 h2
  exact kill3077 (hk.trans hlen) run (fun v hv => hj v (sub v hv))

end PEqualNP.Outside.L_meta_3077

theorem PEqualNP.Outside.L_meta_3077 : ∀ (x1 x2 x3 : Fin (26 : ℕ)) (x4 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))),   x4.length ≤ (13 : ℕ) →     ↑x1 = (9 : ℕ) ∨ ↑x2 = (9 : ℕ) →       ↑x1 ≠ (25 : ℕ) →         ↑x2 ≠ (25 : ℕ) →           (∀ x9 < (9 : ℕ), ∃ x11 ∈ x4, ↑x11.2.1 = x9 ∨ ↑x11.2.2 = x9) →             ∃ x10 < (512 : ℕ),               have x11 : Fin (9 : ℕ) → Bool := fun (x11 : Fin (9 : ℕ)) => x10.testBit ↑x11;               have x12 : List Bool → Fin (26 : ℕ) → Bool := fun (x12 : List Bool) (x13 : Fin (26 : ℕ)) => if ↑x13 = (25 : ℕ) then Bool.true else x12.getD (↑x13) Bool.false;               have x13 : List Bool := List.foldl (fun (x13 : List Bool) (x14 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x13 ++ [if ↑x14.1 = (0 : ℕ) then x12 x13 x14.2.1 && x12 x13 x14.2.2 else if ↑x14.1 = (1 : ℕ) then x12 x13 x14.2.1 || x12 x13 x14.2.2 else !x12 x13 x14.2.1]) (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x1, x2) :: x4);               x13.getD (↑x3) Bool.false ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x14 : ℕ) => x11 (Fin.ofNat (9 : ℕ) (x14 / (10 : ℕ))) && x11 (Fin.ofNat (9 : ℕ) (x14 % (10 : ℕ))) :=
  PEqualNP.Outside.L_meta_3077.main3077
