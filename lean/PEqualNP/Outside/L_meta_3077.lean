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
def deadcolumns : IndexTree ColumnInfo := (.fork 126 (.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(0,1,460,50,8),(0,2,440,69,8),(0,4,369,138,8)]) (.leaf [(0,8,227,276,8),(0,16,486,9,10),(0,32,94,385,8),(0,64,189,258,10)])) (.fork 4 (.leaf [(0,128,347,36,10),(0,256,151,104,8),(1,0,510,0,12),(1,16,486,8,9)]) (.leaf [(2,0,509,0,12),(2,1,460,48,7),(2,4,369,136,7),(2,64,189,256,9)]))) (.fork 8 (.fork 4 (.leaf [(2,128,345,36,7),(4,0,507,0,12),(4,2,440,65,7),(4,8,227,272,7)]) (.leaf [(4,16,482,9,7),(4,128,347,32,9),(5,2,440,64,6),(6,0,505,0,9)])) (.fork 4 (.leaf [(6,16,480,9,6),(6,64,185,256,6),(7,0,504,0,7),(8,0,503,0,12)]) (.leaf [(8,4,369,130,7),(8,16,486,1,9),(8,64,181,258,7),(8,128,339,36,7)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(8,256,151,96,7),(9,0,486,0,8),(9,16,486,0,8),(10,0,501,0,8)]) (.leaf [(10,4,369,128,6),(10,16,484,1,6),(10,64,181,256,6),(12,0,499,0,9)])) (.fork 4 (.leaf [(12,16,482,1,6),(12,64,177,258,6),(12,128,339,32,6),(14,0,497,0,7)]) (.leaf [(14,16,480,1,5),(15,0,480,0,4),(15,16,480,0,4),(16,0,495,0,13)]))) (.fork 8 (.fork 4 (.leaf [(17,0,494,0,11),(19,0,492,0,8),(19,64,172,256,5),(20,8,227,256,6)]) (.leaf [(21,0,490,0,7),(21,2,424,64,5),(21,128,330,32,5),(24,0,487,0,11)])) (.fork 4 (.leaf [(25,0,486,0,8),(27,0,484,0,5),(29,0,482,0,5),(31,0,480,0,4)]) (.leaf [(32,0,479,0,12),(32,1,460,18,7),(32,128,347,4,9),(32,256,151,72,7)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(33,0,478,0,9),(34,1,460,16,6),(34,128,345,4,6)]) (.leaf [(35,0,476,0,7),(35,64,156,256,5),(36,0,347,0,8),(36,128,347,0,8)])) (.fork 4 (.leaf [(38,128,345,0,5),(40,0,471,0,8),(40,16,454,1,6),(40,128,339,4,6)]) (.leaf [(40,256,151,64,6),(41,16,454,0,5),(44,128,339,0,5),(49,0,462,0,8)]))) (.fork 8 (.fork 4 (.leaf [(50,1,460,0,5),(51,0,460,0,5),(53,128,330,0,4),(56,256,135,64,5)]) (.leaf [(64,0,447,0,13),(64,1,396,50,7),(64,2,440,5,7),(64,4,305,138,7)])) (.fork 4 (.leaf [(64,8,163,276,7),(64,32,30,385,7),(64,256,151,40,7),(66,0,445,0,11)]) (.leaf [(66,1,396,48,6),(66,4,305,136,6),(68,2,440,1,6),(68,8,163,272,6)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(69,2,440,0,5),(70,0,441,0,8),(72,4,305,130,6),(72,16,422,1,6)]) (.leaf [(72,256,151,32,6),(74,0,437,0,7),(74,4,305,128,5),(78,0,433,0,5)])) (.fork 4 (.leaf [(80,0,431,0,11),(81,0,430,0,8),(81,2,424,4,5),(83,0,428,0,7)]) (.leaf [(84,8,163,256,5),(85,2,424,0,4),(87,0,424,0,4),(89,0,422,0,5)]))) (.fork 8 (.fork 4 (.leaf [(96,0,415,0,9),(96,1,396,18,6),(96,256,151,8,6),(98,0,413,0,7)]) (.leaf [(98,1,396,16,5),(98,128,281,4,5),(102,128,281,0,4),(104,256,151,0,5)])) (.fork 4 (.leaf [(112,1,396,2,5),(113,0,398,0,5),(114,1,396,0,4),(115,0,396,0,4)]) (.leaf [(120,256,135,0,4),(128,0,383,0,13),(128,1,332,50,7),(128,2,312,69,7)])))))) (.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(128,4,369,10,7),(128,32,94,257,7),(130,0,381,0,9)]) (.leaf [(130,1,332,48,6),(130,4,369,8,6),(130,64,61,256,6),(132,0,379,0,11)])) (.fork 4 (.leaf [(132,2,312,65,6),(132,8,99,272,6),(132,16,354,9,6),(134,0,377,0,8)]) (.leaf [(134,64,57,256,5),(136,0,375,0,9),(136,4,369,2,6),(136,16,358,1,6)]))) (.fork 8 (.fork 4 (.leaf [(136,256,23,96,6),(138,4,369,0,5),(140,0,371,0,8),(140,16,354,1,5)]) (.leaf [(141,16,354,0,4),(144,0,367,0,11),(145,0,366,0,8),(147,0,364,0,5)])) (.fork 4 (.leaf [(153,0,358,0,5),(154,4,353,0,4),(156,0,355,0,7),(157,0,354,0,4)]) (.leaf [(160,0,351,0,11),(160,1,332,18,6),(160,64,29,258,6),(160,256,23,72,6)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(161,16,326,8,5),(162,0,349,0,7),(162,1,332,16,5),(162,64,29,256,5)]) (.leaf [(164,0,347,0,8),(166,0,345,0,5),(168,16,326,1,5),(169,16,326,0,4)])) (.fork 4 (.leaf [(172,0,339,0,5),(177,0,334,0,7),(178,1,332,0,4),(179,0,332,0,4)]) (.leaf [(192,0,319,0,11),(192,2,312,5,6),(192,4,305,10,6),(193,2,312,4,5)]))) (.fork 8 (.fork 4 (.leaf [(194,0,317,0,8),(194,4,305,8,5),(196,2,312,1,5),(197,2,312,0,4)]) (.leaf [(198,0,313,0,7),(200,4,305,2,5),(200,256,23,32,5),(202,4,305,0,4)])) (.fork 4 (.leaf [(224,256,23,8,5),(232,256,23,0,4),(256,0,255,0,12),(256,8,227,20,7)]) (.leaf [(256,16,230,9,7),(256,32,94,129,7),(256,64,189,2,9),(258,0,189,0,8)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(258,64,189,0,8),(260,0,251,0,8),(260,8,227,16,6)]) (.leaf [(260,64,185,2,6),(262,64,185,0,5),(264,0,247,0,9),(264,16,230,1,6)])) (.fork 4 (.leaf [(265,16,230,0,5),(266,64,181,0,5),(268,0,243,0,7),(268,64,177,2,5)]) (.leaf [(270,64,177,0,4),(273,32,78,128,5),(275,64,172,0,4),(276,8,227,0,5)]))) (.fork 8 (.fork 4 (.leaf [(280,0,231,0,8),(288,0,223,0,9),(288,16,198,9,6),(291,64,156,0,4)]) (.leaf [(296,0,215,0,7),(296,16,198,1,5),(297,16,198,0,4),(305,0,206,0,5)])) (.fork 4 (.leaf [(320,0,191,0,11),(320,16,166,9,6),(320,32,30,129,6),(320,128,27,36,6)]) (.leaf [(321,32,30,128,5),(322,0,189,0,8),(324,0,187,0,7),(324,8,163,16,5)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(324,128,27,32,5),(326,0,185,0,5),(328,0,183,0,8),(328,16,166,1,5)]) (.leaf [(329,16,166,0,4),(332,0,179,0,5),(340,8,163,0,4),(344,0,167,0,7)])) (.fork 4 (.leaf [(352,0,159,0,8),(352,128,27,4,5),(356,128,27,0,4),(384,0,127,0,9)]) (.leaf [(384,8,99,20,6),(384,32,94,1,6),(384,64,61,2,6),(386,64,61,0,5)]))) (.fork 8 (.fork 4 (.leaf [(388,8,99,16,5),(388,64,57,2,5),(390,64,57,0,4),(392,0,119,0,6)]) (.leaf [(396,0,115,0,5),(401,32,78,0,4),(404,8,99,0,4),(416,0,95,0,8)])) (.fork 4 (.leaf [(416,64,29,2,5),(418,64,29,0,4),(448,0,63,0,8),(448,32,30,1,5)]) (.leaf [(449,32,30,0,4),(480,0,31,0,7),(484,0,27,0,4),(488,0,23,0,4)])))))))
def deadautos : Array (List Nat) := Array.mk [[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def dead : Forest := ⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,fun _ => emptyPacking,fun _ _ => none⟩
set_option maxHeartbeats 0 in
theorem geomdead : graphValid dead (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=7) ?_⟩,listPieces_all (d:=3) ?_⟩
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
def sameWordsF (a b : List Sig) : Bool := a.length == b.length && a.all (fun x => b.contains x)
lemma sameWordsF_eq {xs ys : List Sig} (hnd : xs.Nodup) (h : sameWordsF xs ys = true) : xs.toFinset = ys.toFinset := by
  simp only [sameWordsF, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h
  have hsub : xs.toFinset ⊆ ys.toFinset := fun x hx => List.mem_toFinset.mpr (h.2 x (List.mem_toFinset.mp hx))
  have hle : ys.toFinset.card ≤ xs.toFinset.card := by
    rw [List.toFinset_card_of_nodup hnd, h.1]; exact List.toFinset_card_le ys
  exact Finset.eq_of_subset_of_card_le hsub hle
def closeChildU2 (pools : List BoundPool) (links : Nat → List (List Sig)) (tag k : Nat)
    (rest : List Sig) (op : Choice) (z : Sig) : Bool :=
  let ws := z :: rest
  (links tag).any (sameWordsF ws) || pools.any (fun p => scalarPoolCut p k rest op)
theorem closeChildU2_sound {raw T pools links tag k tm rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ t xs, xs ∈ links t → ImpossibleU T k tm (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChildU2 pools links tag k rest op (choiceVal op) = true) :
    ImpossibleU T k tm (choiceVal op :: rest).toFinset := by
  simp only [closeChildU2, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨xs, hx, ok⟩ | ⟨p, hp, ok⟩
  · rw [sameWordsF_eq nd ok]; exact lValid _ _ hx
  · exact imp_to_impU (scalarPoolCut_sound (pValid _ hp) nd ok)
def constMask (d : Sig) : List Decor → Nat
  | [] => 0
  | w :: ws => (isMaskedConstant d w.1).toNat + 2 * constMask d ws
lemma constMask_bit (d : Sig) (ws : List Decor) (i : Nat) (hi : i < ws.length) :
    ((constMask d ws >>> i) &&& 1) = (isMaskedConstant d (ws.getD i defaultDecor).1).toNat := by
  induction ws generalizing i with
  | nil => simp at hi
  | cons w ws ih =>
    cases i with
    | zero =>
      simp only [constMask, Nat.shiftRight_zero, List.getD_cons_zero, Nat.and_one_is_mod]
      cases isMaskedConstant d w.1 <;> simp <;> omega
    | succ i =>
      simp only [constMask, List.getD_cons_succ]
      rw [show i + 1 = 1 + i by omega, Nat.shiftRight_add, Nat.shiftRight_one]
      have hdiv : ((isMaskedConstant d w.1).toNat + 2 * constMask d ws) / 2 = constMask d ws := by
        cases isMaskedConstant d w.1 <;> simp <;> omega
      rw [hdiv]
      exact ih i (by simpa using hi)
abbrev QuickPool3 := BoundPool × Nat × Nat × List Sig
def sumPool3_fast (ws : List Decor) (k : Nat) (p : BoundPool) : Option QuickPool3 :=
  let mw := p.wires.map (masked p.domain)
  if !(ws.all (fun w => let m := masked p.domain w.1; m == zero || m == p.domain || mw.any (fun v => v == m))) then none else
  let cm := ws.countP (fun w => isMaskedConstant p.domain w.1)
  if k + p.paid > p.bound + cm then none else
  some (p, cm, constMask p.domain ws, mw)
def fastCost3_val (s : QuickPool3) (k : Nat) (a b : Decor) (z : Sig) (un ka kb : Bool) : Bool :=
  let (p, baseCm, _, mw) := s
  let la := if ka then 0 else (isMaskedConstant p.domain a.1).toNat
  let lb := if un || kb then 0 else (isMaskedConstant p.domain b.1).toNat
  let lhs := k + p.paid
  let rhs := p.bound + (baseCm - la - lb)
  if lhs + 1 < rhs then true
  else if lhs > rhs then false
  else
    let zm := masked p.domain z
    let zc := zm == zero || zm == p.domain
    if lhs == rhs then zc
    else zc || mw.any (fun v => v == zm)
def fastCost3 (s : QuickPool3) (k i j : Nat) (z : Sig) (un ka kb : Bool) : Bool :=
  let (p, baseCm, cmask, mw) := s
  let la := if ka then 0 else (cmask >>> i) &&& 1
  let lb := if un || kb then 0 else (cmask >>> j) &&& 1
  let lhs := k + p.paid
  let rhs := p.bound + (baseCm - la - lb)
  if lhs + 1 < rhs then true
  else if lhs > rhs then false
  else
    let zm := masked p.domain z
    let zc := zm == zero || zm == p.domain
    if lhs == rhs then zc
    else zc || mw.any (fun v => v == zm)
lemma fastCost3_eq {s k ws i j z un ka kb} (hi : i < ws.length) (hj : j < ws.length)
    (hcm : s.2.2.1 = constMask s.1.domain ws) :
    fastCost3 s k i j z un ka kb =
      fastCost3_val s k (ws.getD i defaultDecor) (ws.getD j defaultDecor) z un ka kb := by
  rcases s with ⟨p, baseCm, cmask, mw⟩
  dsimp only at hcm; subst hcm
  dsimp only [fastCost3, fastCost3_val]
  rw [constMask_bit p.domain ws i hi, constMask_bit p.domain ws j hj]
lemma fastCost3_good {p qp k ws a b op ka kb} (ha : a ∈ ws) (hb : b ∈ ws)
    (hsum : sumPool3_fast ws k p = some qp)
    (h : fastCost3_val qp k a b (choiceVal (movedChoice op a b)) (op == 2) ka kb = true) :
    scalarPoolCut p k ((opKeep (op == 2) ka kb a b ws).map Prod.fst) (movedChoice op a b) = true := by
  dsimp only [sumPool3_fast] at hsum
  split at hsum
  · cases hsum
  next hok =>
    have all : ws.all (fun w => availableB p.domain p.wires w.1) = true := by
      cases hall : ws.all (fun w => availableB p.domain p.wires w.1)
      · exfalso; apply hok; change (!ws.all (fun w => availableB p.domain p.wires w.1)) = true; rw [hall]; rfl
      · rfl
    split at hsum
    · cases hsum
    injection hsum with hqp
    subst hqp
    let z := choiceVal (movedChoice op a b)
    let const := fun w : Decor => isMaskedConstant p.domain w.1
    let rest := opKeep (op == 2) ka kb a b ws
    have ck := keptCount const ws a b (op == 2) ka kb
    change ws.countP const - constantLoss const a ka - constantLoss const b ((op == 2) || kb) ≤ rest.countP const at ck
    have hav := List.all_eq_true.mp all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires) = true := by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hm
      exact hav w ((keep_sub ws a b (op == 2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.wires (movedChoice op a b) = true := by
      simp [choiceOK, movedChoice, hav _ ha, hav _ hb]
    dsimp only [rest] at hs
    simp only [scalarPoolCut, hs, opOK, Bool.or_true, Bool.and_true, decide_eq_true_eq,
      List.countP_cons, List.countP_map, Function.comp_def]
    change k + p.paid + (!availableB p.domain p.wires z).toNat <
      p.bound + (rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
    have hla : (if ka then 0 else (isMaskedConstant p.domain a.1).toNat) = constantLoss const a ka := by
      cases ka <;> simp [constantLoss, const]
    have hlb : (if (op == 2) || kb then 0 else (isMaskedConstant p.domain b.1).toNat) = constantLoss const b ((op == 2) || kb) := by
      cases ((op == 2) || kb) <;> simp [constantLoss, const]
    dsimp only [fastCost3_val] at h
    rw [hla, hlb] at h
    set la := constantLoss const a ka
    set lb := constantLoss const b ((op == 2) || kb)
    set lhs := k + p.paid
    set rhs := p.bound + (ws.countP const - la - lb)
    have hzc : (masked p.domain z == zero || masked p.domain z == p.domain) = isMaskedConstant p.domain z := rfl
    have hfree : ((masked p.domain z == zero || masked p.domain z == p.domain) ||
        (p.wires.map (masked p.domain)).any (fun v => v == masked p.domain z)) = availableB p.domain p.wires z := rfl
    split at h
    · cases h1 : availableB p.domain p.wires z <;> cases h2 : isMaskedConstant p.domain z <;> simp_all <;> omega
    · split at h
      · cases h
      · split at h
        · rw [hzc] at h
          have hfa : availableB p.domain p.wires z = true := by
            rw [← hfree, hzc, h]; rfl
          simp [h, hfa]; omega
        · rw [hfree] at h
          cases h2 : isMaskedConstant p.domain z <;> simp_all <;> omega
abbrev NodeContextU :=
  Nat × Nat × Nat × List Decor × CovPair × List BoundPool × List QuickPool3 × LinkFn × LinkFn × List Nat × Nat
def ctxWireU (c : NodeContextU) (i : Nat) : Decor := c.2.2.2.1.getD i defaultDecor
def evalMoveU (c : NodeContextU) (op : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let (cap,tm,n,ws,cov,pools,qpools,l0,l1,_,wsKey) := c
  let un := op == 2
  let len := 1 + (n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len > cap then true else
    let ct := childU tm cap len
    let d := ct == 0
    if (restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1 == z.1) then true else
    if qpools.any (fun qp => fastCost3_val qp (cap-1) a b z.1 un ka kb) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      let links := if d then l0 else l1
      let tag := wsKey - (if ka then 0 else keyWord a.1) - (if un || kb then 0 else keyWord b.1) + keyWord z.1
      closeChildU2 pools links tag (cap-1) rest (movedChoice op a b) z.1
theorem evalMoveU_sound {raw T r s ws} {pools : List BoundPool} {l0 l1 wkeys wsKey cap tm a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op == 2) = false → a ≠ b) (hcap : 0 < cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv0 : ∀ tag xs, xs ∈ l0 tag → ImpossibleU T (cap-1) 0 (List.toFinset xs))
    (lv1 : ∀ tag xs, xs ∈ l1 tag → ImpossibleU T (cap-1) 1 (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMoveU (cap,tm,ws.length,ws,preCov ws,pools,pools.filterMap (sumPool3_fast ws (cap-1)),l0,l1,wkeys,wsKey)
      op a b (movedDecor op a b) ka kb = true) :
    ImpossibleU T (cap-1) (childU tm cap (moveFront ws op a b ka kb).length)
      (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op == 2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm), nd.sublist (sub.map _)⟩
  have val := moved_full op a b
  have fr : ws.any (fun v => v.1 == z.1) = false := by
    apply Bool.eq_false_iff.mpr; intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh ((beq_iff_eq.mp he).symm ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1 + (ws.length - (if ka then 0 else 1) - (if (op == 2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1 :: rest.map Prod.fst).length
    rw [List.length_cons, List.length_map, len_keep _ _ _ _ _ _ ha hb ne, Nat.add_comm 1]
  intro k t hk ht h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k + 1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMoveU at test
  change (if 1 + (ws.length - _ - _) > cap then true else _) = true at test
  rw [leq, if_neg (by omega)] at test
  let ct := childU tm cap child.length
  have ht0 : (ct == 0) = true → t = 0 := fun hct => ht (beq_iff_eq.mp hct)
  have sep := cover_sound h rfl (pair_sep pairs) (ct == 0) ht0
  let d := ct == 0
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op == 2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [← hf, ← g, rz, BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op == 2) ka kb ||| column d z.2) != BitVec.allOnes 768) = false := by
    rw [sep, bne_self_eq_false]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1 == z.1) then true else if _ then true else _) = true at test
  rw [be, pp, fr] at test
  simp only [Bool.false_eq_true, ite_false, Bool.not_true, Bool.false_or] at test
  have nd' : (choiceVal (movedChoice op a b) :: rest.map Prod.fst).Nodup := val ▸ ndc
  have h' : Live T k t (choiceVal (movedChoice op a b) :: rest.map Prod.fst).toFinset := val ▸ h
  by_cases hq : (pools.filterMap (sumPool3_fast ws (cap-1))).any (fun qp => fastCost3_val qp (cap-1) a b z.1 (op == 2) ka kb) = true
  · obtain ⟨qp, hqp, hfc⟩ := List.any_eq_true.mp hq
    obtain ⟨p, hp, hsum⟩ := List.mem_filterMap.mp hqp
    exact scalarPoolCut_sound (pv p hp) nd' (fastCost3_good ha hb hsum (val ▸ hfc)) k t hk h'
  · have hqf : (pools.filterMap (sumPool3_fast ws (cap-1))).any (fun qp => fastCost3_val qp (cap-1) a b z.1 (op == 2) ka kb) = false :=
      Bool.eq_false_iff.mpr hq
    change (if ((pools.filterMap (sumPool3_fast ws (cap-1))).any fun qp => fastCost3_val qp (cap-1) a b z.1 (op == 2) ka kb) = true then true else _) = true at test
    rw [hqf] at test
    simp only [Bool.false_eq_true, ite_false] at test
    by_cases hd : d = true
    · dsimp only [d, ct] at hd; rw [hd] at test; simp only [ite_true] at test
      exact closeChildU2_sound pv lv0 nd' (val ▸ test) k t hk (fun _ => ht0 hd) h'
    · have hdf : d = false := Bool.eq_false_iff.mpr hd
      dsimp only [d, ct] at hdf; rw [hdf] at test; simp only [Bool.false_eq_true, ite_false] at test
      exact closeChildU2_sound pv lv1 nd' (val ▸ test) k t hk (fun h0 => by cases h0) h'
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

theorem nodeU_sound {raw T r s ws} {pools : List BoundPool} {l0 l1 wkeys wsKey cap tm}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv0 : ∀ tag xs, xs ∈ l0 tag → ImpossibleU T (cap-1) 0 (List.toFinset xs))
    (lv1 : ∀ tag xs, xs ∈ l1 tag → ImpossibleU T (cap-1) 1 (List.toFinset xs))
    (checks : cap = 0 ∨ testAllU (cap,tm,ws.length,ws,preCov ws,pools,pools.filterMap (sumPool3_fast ws (cap-1)),l0,l1,wkeys,wsKey) ws = true) :
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
        (test : testPairU (cap,tm,ws.length,ws,preCov ws,pools,pools.filterMap (sumPool3_fast ws (cap-1)),l0,l1,wkeys,wsKey) a b d = true) :
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


abbrev PT := PackingT
def emptyPT : PT := emptyPackingT
def lw0 (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a * sw) sw
  let row := (h / nb + sh) % slots
  let word := packedAt data (nb * sw + row * vw) vw
  some (word &&& ((1 <<< iw) - 1), (word >>> iw) &&& ((1 <<< pw) - 1))
def inS0 : Sig := inputs.getD 0 zero
def inS1 : Sig := inputs.getD 1 zero
def inS2 : Sig := inputs.getD 2 zero
def inS3 : Sig := inputs.getD 3 zero
def inS4 : Sig := inputs.getD 4 zero
def inS5 : Sig := inputs.getD 5 zero
def inS6 : Sig := inputs.getD 6 zero
def inS7 : Sig := inputs.getD 7 zero
def inS8 : Sig := inputs.getD 8 zero
def rotS0 : List Sig := [inS0,inS1,inS2,inS3,inS4,inS5,inS6,inS7,inS8]
def rotS1 : List Sig := [inS0,inS5,inS8,inS3,inS4,inS1,inS7,inS6,inS2]
def rotS2 : List Sig := [inS1,inS0,inS5,inS8,inS6,inS2,inS4,inS7,inS3]
def rotS3 : List Sig := [inS1,inS2,inS3,inS8,inS6,inS0,inS7,inS4,inS5]
def rotS4 : List Sig := [inS2,inS1,inS0,inS5,inS7,inS3,inS6,inS4,inS8]
def rotS5 : List Sig := [inS2,inS3,inS8,inS5,inS7,inS1,inS4,inS6,inS0]
def rotS6 : List Sig := [inS3,inS2,inS1,inS0,inS4,inS8,inS7,inS6,inS5]
def rotS7 : List Sig := [inS3,inS8,inS5,inS0,inS4,inS2,inS6,inS7,inS1]
def rotS8 : List Sig := [inS5,inS0,inS1,inS2,inS7,inS8,inS4,inS6,inS3]
def rotS9 : List Sig := [inS5,inS8,inS3,inS2,inS7,inS0,inS6,inS4,inS1]
def rotS10 : List Sig := [inS8,inS3,inS2,inS1,inS6,inS5,inS4,inS7,inS0]
def rotS11 : List Sig := [inS8,inS5,inS0,inS1,inS6,inS3,inS7,inS4,inS2]
def rotDS : Nat → Option (List Sig)
  | 0 => some rotS0 | 1 => some rotS1 | 2 => some rotS2 | 3 => some rotS3
  | 4 => some rotS4 | 5 => some rotS5 | 6 => some rotS6 | 7 => some rotS7
  | 8 => some rotS8 | 9 => some rotS9 | 10 => some rotS10 | 11 => some rotS11
  | _ => none
lemma rotDS_eq : (List.range 12).all (fun p =>
    match rotDS p, dead.autos[p]? with
    | some xs, some perm => xs == deadSigs.map (movedWord (perm.map swapRows).reverse)
    | _, _ => false) = true := by decide +kernel
lemma rotDS_at (p : Nat) : rotDS p = (dead.autos[p]?).map (fun perm => deadSigs.map (movedWord (perm.map swapRows).reverse)) := by
  by_cases hp : p < 12
  · have h := List.all_eq_true.mp rotDS_eq p (List.mem_range.mpr hp)
    cases h1 : rotDS p <;> cases h2 : dead.autos[p]? <;> simp [h1, h2] at h ⊢
    exact h
  · have h1 : rotDS p = none := by
      unfold rotDS
      match p with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => omega
      | _ + 12 => rfl
    have h2 : dead.autos[p]? = none := Array.getElem?_eq_none (by change deadautos.size ≤ p; have : deadautos.size = 12 := rfl; omega)
    rw [h1, h2]; rfl
lemma decodeSigs_movedWord (ms : List Move) (n bits : Nat) (ws : List Sig) :
    decodeSigs n bits (ws.map (movedWord ms)) = (decodeSigs n bits ws).map (movedWord ms) := by
  induction n generalizing bits ws with
  | zero => rfl
  | succ k ih =>
    simp only [decodeSigs]
    have hget (i : Nat) : (ws.map (movedWord ms)).getD i zero = movedWord ms (ws.getD i zero) := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases ws[i]? with
      | none => exact ((moved_eq_rename ms zero).trans (rename_constants (movedRow ms)).1).symm
      | some x => rfl
    rw [hget, hget]
    have hop : (if ((bits >>> 8) &&& 3) = 2 then neg (movedWord ms (ws.getD (bits &&& 15) zero))
        else bin (((bits >>> 8) &&& 3) == 1) (movedWord ms (ws.getD (bits &&& 15) zero)) (movedWord ms (ws.getD ((bits >>> 4) &&& 15) zero))) =
        movedWord ms (if ((bits >>> 8) &&& 3) = 2 then neg (ws.getD (bits &&& 15) zero)
        else bin (((bits >>> 8) &&& 3) == 1) (ws.getD (bits &&& 15) zero) (ws.getD ((bits >>> 4) &&& 15) zero)) := by
      simp only [moved_eq_rename]; split
      · exact (rename_neg _ _).symm
      · exact (rename_bin _ _ _ _).symm
    rw [hop, ← List.map_singleton, ← List.map_append]
    exact ih (bits >>> 10) _
def stateSetT_base (levels : Nat → PackingT) (slot i : Nat) (base : List Sig) : List Sig :=
  let (_, depth, _, _, data) := levels slot
  let len := 10 * depth
  let width := len + deadSigs.length + depth
  let recp := packedAt data (i * width) width
  let ops := recp &&& ((1 <<< len) - 1)
  selectLive (recp >>> len) (decodeSigs depth ops base)
lemma stateSetT_base_eq (levels : Nat → PackingT) (slot i : Nat) (ms : List Move) :
    stateSetT_base levels slot i (deadSigs.map (movedWord ms)) = (stateSetT levels slot i).map (movedWord ms) := by
  unfold stateSetT_base stateSetT
  rcases levels slot with ⟨num, depth, cw, offw, data⟩
  dsimp only
  rw [decodeSigs_movedWord, selectLive_map]
def linkedSetT (levels : Nat → PackingT) (slot : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (levels slot).1 then none else
    (rotDS pair.2).map (stateSetT_base levels slot pair.1)
theorem linkedSetU_sound (levels : Nat → PackingT) (k tm : Nat)
    (names : ∀ x ∈ dead.autos.toList, autoOK (targetOf dead) (x.map swapRows) = true)
    (earlier : ∀ i < (levels (3*k+tm)).1, ImpossibleU (targetOf dead) k tm (stateSetT levels (3*k+tm) i).toFinset)
    {pair out} (h : linkedSetT levels (3*k+tm) pair = some out) :
    ImpossibleU (targetOf dead) k tm out.toFinset := by
  unfold linkedSetT at h
  split at h
  · cases h
  next valid =>
    rw [rotDS_at] at h
    cases e : dead.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e, Option.map_some, Option.some.injEq] at h
      rw [← h, stateSetT_base_eq]
      exact rotate_excludedU (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))
def contextOfU (levels : Nat → PackingT) (idx0 idx1 : Nat → Nat → Option (Nat × Nat)) (k tm i : Nat) : NodeContextU :=
  let slot := 3 * k + tm
  let raw := deadWires
  let (num, depth, cw, offw, data) := levels slot
  let (ops, bank, ws) := readNodeT levels slot i
  let start := num * (10 * depth + raw.length + depth)
  let c0 := packedAt data (start + i * offw) offw
  let c1 := packedAt data (start + (i + 1) * offw) offw
  let nr := c1 - c0
  let st := start + (num + 1) * offw + c0 * (cw + depth)
  let rules := (getPairs data cw depth nr st).filterMap (fun (a, b) => buildRule dead ops depth bank a b)
  let ls0 := fun tag => ((idx0 slot tag).bind (linkedSetT levels (3*(k-1)))).toList
  let ls1 := fun tag => ((idx1 slot tag).bind (linkedSetT levels (3*(k-1)+1))).toList
  let wkeys := ws.map (fun w => keyWord w.1)
  (k, tm, ws.length, ws, preCov ws, rules, rules.filterMap (sumPool3_fast ws (k-1)), ls0, ls1, wkeys, wkeys.foldl (·+·) 0)
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
  let (cap,tm,n,ws,_,pools,qpools,l0,l1,wkeys,wsKey) := c
  let a := ws.getD i defaultDecor
  let b := ws.getD j defaultDecor
  let un := op == 2
  let len := 1 + (n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  let ct := childU tm cap len
  let z1 := choiceVal (movedChoice op a b)
  if !properB z1 || ws.any (fun v => v.1 == z1) then true else
  if qpools.any (fun qp => fastCost3 qp (cap-1) i j z1 un ka kb) then true else
    let rest := (opKeep un ka kb a b ws).map Prod.fst
    let links := if ct == 0 then l0 else l1
    let tag := wsKey - (if ka then 0 else wkeys.getD i 0) - (if un || kb then 0 else wkeys.getD j 0) + keyWord z1
    closeChildU2 pools links tag (cap-1) rest (movedChoice op a b) z1
theorem fallbackFastU_sound {c i j op ka kb}
    (hi : i < c.2.2.2.1.length) (hj : j < c.2.2.2.1.length)
    (hwk : c.2.2.2.2.2.2.2.2.2.1 = c.2.2.2.1.map (fun w => keyWord w.1))
    (hcm : ∀ qp ∈ c.2.2.2.2.2.2.1, qp.2.2.1 = constMask qp.1.domain c.2.2.2.1)
    (hlen : ¬(1 + (c.2.2.1 - (if ka then 0 else 1) - (if (op == 2) || kb then 0 else 1)) > c.1))
    (h : fallbackFastU c i j op ka kb = true) :
    checkAtU c i j op ka kb = true := by
  rcases c with ⟨cap, tm, n, ws, cov, pools, qpools, l0, l1, wkeys, wsKey⟩
  dsimp only at hi hj hwk hcm hlen
  subst hwk
  dsimp only [checkAtU, evalMoveU, ctxWireU]
  rw [if_neg hlen]
  dsimp only [fallbackFastU] at h
  have hz1 : (movedDecor op (ws.getD i defaultDecor) (ws.getD j defaultDecor)).1 =
      choiceVal (movedChoice op (ws.getD i defaultDecor) (ws.getD j defaultDecor)) :=
    moved_full op _ _
  have hki : (ws.map (fun w => keyWord w.1)).getD i 0 = keyWord (ws.getD i defaultDecor).1 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hi]; rfl
  have hkj : (ws.map (fun w => keyWord w.1)).getD j 0 = keyWord (ws.getD j defaultDecor).1 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hj]; rfl
  have hfc : qpools.any (fun qp => fastCost3 qp (cap-1) i j (choiceVal (movedChoice op (ws.getD i defaultDecor) (ws.getD j defaultDecor))) (op == 2) ka kb) =
      qpools.any (fun qp => fastCost3_val qp (cap-1) (ws.getD i defaultDecor) (ws.getD j defaultDecor) (choiceVal (movedChoice op (ws.getD i defaultDecor) (ws.getD j defaultDecor))) (op == 2) ka kb) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    constructor <;> rintro ⟨qp, hqp, hok⟩ <;> refine ⟨qp, hqp, ?_⟩
    · rwa [← fastCost3_eq hi hj (hcm qp hqp)]
    · rwa [fastCost3_eq hi hj (hcm qp hqp)]
  rw [hfc, hki, hkj] at h
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
    (budget : xs[q].1 = k) (ht : xs[q].2.1 = tm) (arity : xs[q].2.2.1 = n) (hn : xs[q].2.2.2.1.length = n)
    (hwk : xs[q].2.2.2.2.2.2.2.2.2.1 = xs[q].2.2.2.1.map (fun w => keyWord w.1))
    (hcm : ∀ qp ∈ xs[q].2.2.2.2.2.2.1, qp.2.2.1 = constMask qp.1.domain xs[q].2.2.2.1)
    (pass : batchMoveU (makeBatchU k n xs) tm xs i j op ka kb = true) :
    checkAtU xs[q] i j op ka kb = true := by
  let len := 1 + (n - (if ka then 0 else 1) - (if (op == 2) || kb then 0 else 1))
  let d := childU tm k len == 0
  by_cases small : len > k
  · rcases hxq : xs[q] with ⟨cap, tmm, nn, ws, cov, pools, qpools, l0, l1, wkeys, wsKey⟩
    rw [hxq] at budget arity; dsimp only at budget arity; subst budget arity
    dsimp only [checkAtU, evalMoveU, len] at small ⊢; rw [if_pos small]
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
      apply fallbackFastU_sound (hn ▸ hi) (hn ▸ hj) hwk hcm hlenq
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rcases hxq : xs[q] with ⟨cap, tmm, nn, ws, cov0, pools, qpools, l0, l1, wkeys, wsKey⟩
      rw [hxq] at budget ht arity hit; dsimp only at budget ht arity; subst budget ht arity
      dsimp only [checkAtU, evalMoveU, ctxWireU, len] at small ⊢
      rw [if_neg small]
      change (if combFieldU (cap,tmm,nn,ws,cov0,pools,qpools,l0,l1,wkeys,wsKey) d (op == 2) ka kb op i j != BitVec.allOnes 768 then true else _) = true
      rw [if_pos (bne_iff_ne.mpr hit)]
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
    (budget : xs[q].1 = k) (ht : xs[q].2.1 = tm) (arity : xs[q].2.2.1 = n) (hn : xs[q].2.2.2.1.length = n)
    (hwk : xs[q].2.2.2.2.2.2.2.2.2.1 = xs[q].2.2.2.1.map (fun w => keyWord w.1))
    (hcm : ∀ qp ∈ xs[q].2.2.2.2.2.2.1, qp.2.2.1 = constMask qp.1.domain xs[q].2.2.2.1) (js : List Nat)
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
        exact ⟨check hi hi hq budget ht arity hn hwk hcm h1.1, check hi hi hq budget ht arity hn hwk hcm h1.2⟩
      · simp
    refine ⟨⟨hun, ?_⟩, ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j, hj, rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPairU (makeBatchU k n xs) tm xs i j (if d then 1 else 0) = true) :
        testPairU xs[q] (ctxWireU xs[q] i) (ctxWireU xs[q] j) d = true := by
      simp only [batchPairU, Bool.and_eq_true] at pass
      simp only [testPairU, Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget ht arity hn hwk hcm pass.1.1.1, check hi hj' hq budget ht arity hn hwk hcm pass.1.1.2⟩,
        check hi hj' hq budget ht arity hn hwk hcm pass.1.2⟩, check hi hj' hq budget ht arity hn hwk hcm pass.2⟩
    exact ⟨opCheck false both.1, opCheck true both.2⟩
def runBatchU (k tm n : Nat) (xs : List NodeContextU) : Bool :=
  batchRowsU (makeBatchU k n xs) tm xs (List.range n)
theorem runBatchU_at {k tm n} {xs : List NodeContextU} {q} (hq : q < xs.length)
    (hb : xs[q].1 = k) (ht : xs[q].2.1 = tm) (ha : xs[q].2.2.1 = n) (hn : xs[q].2.2.2.1.length = n)
    (hwk : xs[q].2.2.2.2.2.2.2.2.2.1 = xs[q].2.2.2.1.map (fun w => keyWord w.1))
    (hcm : ∀ qp ∈ xs[q].2.2.2.2.2.2.1, qp.2.2.1 = constMask qp.1.domain xs[q].2.2.2.1)
    (pass : runBatchU k tm n xs = true) : testAllU xs[q] xs[q].2.2.2.1 = true := by
  have all := batchRowsU_at k tm n xs hq hb ht ha hn hwk hcm (List.range n) (fun _ => List.mem_range.mp) pass
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
  have hwk : xs[q].2.2.2.2.2.2.2.2.2.1 = xs[q].2.2.2.1.map (fun w => keyWord w.1) := by rw [e]; rfl
  have hcm : ∀ qp ∈ xs[q].2.2.2.2.2.2.1, qp.2.2.1 = constMask qp.1.domain xs[q].2.2.2.1 := by
    rw [e]; intro qp hqp
    dsimp only [contextOfU] at hqp
    obtain ⟨p, _, hsum⟩ := List.mem_filterMap.mp hqp
    dsimp only [sumPool3_fast] at hsum
    split at hsum
    · cases hsum
    split at hsum
    · cases hsum
    injection hsum with heq; subst heq; rfl
  simp only [nodeVerifiedU, Bool.and_eq_true]
  refine ⟨one.2, ?_⟩
  split
  · rfl
  · exact e ▸ runBatchU_at hq hb ht ha hn hwk hcm hrun
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
def uL24F (i : Nat) : Nat := 0x306bdd66d2cc606aa4e540
def uL24 : PT := (1,7,8,1,uL24F)
def uL27F (i : Nat) : Nat := 0x2c1ae02e7529c2e70b9c2e7529cee77b9c40015e06ac52ddccbbbbbbbba9876543332111000000000000000000000008afeebd98dc2a4b4a8194fdc758ebb549695022bfbaf6636a992d2a04d6f75ecc549415a54092feebd98a9554b4a8186fdc669ebb605395022dfbad66370b8a72a0457f75ecc6d5214e540e35eda18cc0d549ca8126fdd6b3181aa9395030f7b696630355272a061ef6d1c85c6aa4e540e2deda30eb8d549ca81c5bdb45d971aa9395038d7b68b12c355272a071ed6d181586aa4e540e3dada302a8d549ca8187bdb471521aa9395038f6b68b8a4355272a044ff762cc6d9534a540c37ee334f5db0294a8196bdc6552bb605295026df3ad6630298252a069fc32981545304a5408afeebd98dc2a48ca8185fdc76a2bb549195030bfb8ed3576a9232a0617f71da3aed52465408afeebd98daa648ca8125fdd7b3152aa919503e2bb0ab9b0ea9ad2a07c5b5d58261d525a540f9a6a9b04c1aa4b4a81f54d535c97354969503e39ae6c130e992d2a0457f75ccb956225a540fa3ab2ae2bb2a29ca81f365526058254539503eacaa4b8ae4a8a72a07d39589715d9214e5408b7eeb197444229ca81f62d545896554929503e2bb0ab9b0ea9a32a07c5b5d58261d5246540f9a6a9b04c1aa48ca81f54d535c97354919503e39ae6c130e99232a0457f75ccb9562246540
def uL27 : PT := (48,6,8,4,uL27F)
def uH0_27F (i : Nat) : Nat := 0x0
def uH0_27 (h : Nat) : Option (Nat × Nat) := lw0 1 1 1 5 1 4 uH0_27F h
def uL28F (i : Nat) : Nat := 0x30b7b8eda10355272a061af719b4086aa4e540c39ee2b6810d549ca8187b9b470021aa939502c97ba9554ef33272a058ed752aaa22114e540b2daea5553bc229ca8166b5d4aaa6684539502ce6ba9554ab08a72a059e9752aa88a114e540
def uL28 : PT := (10,6,8,1,uL28F)
def uL30F (i : Nat) : Nat := (if i<2 then (if i<1 then 0xf6dd6360d624a540b6fdc654d624a540f73d54595524a540f6ed62595524a540f75d5360d524a540f7d93054d524a540b5fdc7215324a540b6fdc6215324a540b7ddc3215324a540b7f5c1215324a540b7f9c0215324a54097fdcb614a14a540f2fd86595814a540f2fd8658d814a540f7d93054d814a540f67d65619514a540f67d655d9514a540c7fcba60d514a540f73d54549514a540f6dd63619314a540c7fcba615314a540f7d930615314a540b5fdc7215314a540b6fdc6215314a540b7ddc3215314a540b7f9c0215314a540b5fdc7215214a540b6fdc6215214a540b7ddc3215214a540b7f9c0215214a540f6ed62595214a540f7d93054d214a540c7fcba58e554a54097fccb60a554a54097fccb606554a540c7fcba616114a540c7fcba60e114a540c7fcba54e114a540c7fcbaa22114a540f1fd875d98546540f37d8561d6546540f1fd876157346540f75d53615734654097fdcb61d5346540d5fdb761d5346540f37d8561d5346540b7ddc361d5346540f5dd7361d5346540f1fd875d98246540b6fdc62d58246540f76d522d58246540f1fd875d58246540f76d525d58246540b3fdc85cd8246540d5fdb75cd8246540f1fd875cd8246540f7cd325cd8246540f3dd8358d8246540d77db554d8246540f3dd8354d8246540b7edc254d8246540f76d5254d8246540f5dd7354d7246540f76d5254d7246540f3ed8261d6246540f3ed8260d6246540d5fcb76e15246540d5fcb72e1524654097fdcb61d524654097fccb61d5246540d3fdb861d5246540f57d7561d5246540b7edc261d5246540f3ed8261d5246540d5fcb76d95246540d5fcb76cd5246540f75d5360d5246540f3ed8260d5246540b77dc55cd5246540d7ddb35cd5246540f75d535cd5246540f5ed725cd524654097fdcb6095246540b5fdc7aed5246540d5fcb7aed524654097fdcb61d3246540f5dd7361d3246540f3ed8261d324654097fdcb615324654097fdcb2153246540b5fdc72153246540b6fdc62153246540b7ddc32153246540b7edc22153246540b7f5c12153246540b7f9c0215324654097fdcb5d53246540f3ed825498146540f3ed824c98146540f1fd876157146540b5fdc76097146540f1fd876097146540f5ed725497146540d5fdb761d5146540f5f57161d5146540f76d526095146540d5fdb761d3146540b5fdc72153146540b6fdc62153146540b7ddc32153146540b7edc22153146540b7f9c02153146540f7cd326093146540f5f57161d2146540b5fdc72152146540b6fdc62152146540b7ddc32152146540b7edc22152146540b7f9c0215214654097fccb54a884654097fccb60a5546540b5fdc72162246540b6fdc62162246540b7ddc32162246540b7edc22162246540b7f9c0216224654097fccba22224654097fccb9562246540 else 0xc7fda3aed524654097fecc6e13246540d5fcc76d5324654097fecc6d53246540e5fda861d7146540e5fd876957146540e5fd8768d7146540e5fd876897146540a7fecc61eaa46540e3fd87616aa46540a7fdc2216aa46540a7fdc85d6aa46540e5fd875d6aa46540e3fd8760aaa46540a7fecc60aaa46540a7fdc85caaa46540a7fdc854aaa46540a7fdc754aaa46540e5fcc754aaa46540e77d7554aaa46540e7ed8254aaa46540e7ed7254aaa46540a7fecc54aaa46540f1fd87615735a540f75d53615735a54097fdcb61d535a540d5fdb761d535a540f37d8561d535a540b7ddc361d535a540f5dd7361d535a540f1fd875d5825a540f76d525d5825a540b3fdc85cd825a540d5fdb75cd825a540f1fd875cd825a540f7cd325cd825a540d77db554d825a540f3dd8354d825a540b7edc254d825a540f76d5254d825a540f5dd7354d725a540f76d5254d725a540d5fcb76e1525a54097fdcb61d525a540d3fdb861d525a540f57d7561d525a540b7edc261d525a540f3ed8261d525a540d5fcb76cd525a540f75d5360d525a540f3ed8260d525a540b77dc55cd525a540d7ddb35cd525a540f75d535cd525a540f5ed725cd525a540d5fcb76c5525a540b5fdc7aed525a540d5fcb7aed525a54097fdcb61d325a540f5dd7361d325a540f3ed8261d325a54097fdcb615325a54097fdcb5d5325a540f5ed72549715a540f76d525c9515a54097fccb956225a540d6fcb66dd814e540d5fdb75d9814e540d6fcb66c9814e54097fccb549814e540f77551549814e540b6fdc6aed814e540d6fcb6aed814e54097fdcb548814e540d5fdb7548814e540d7edb2548814e540f4fd76595714e540f77551595714e540d6fdb6589714e540f4fd76589714e540f7e521589714e540d77db5549714e540f5ed72549714e540b7f5c1549714e540f77551549714e54097fdcb61d614e540d5fdb761d614e54097fdcb5d9514e540f5f5715d9514e540f3f581609514e540f76d525c9514e540f5f5715c9514e540d6fdb6589514e540b77dc5589514e540f67d65589514e54097fdcb608514e540d7edb2608514e54097fdcb5d9214e540f5f5715d9214e54097fdcb615214e54097fdcb5d5214e54097fdcb595214e540f6ed62595214e54097fdcb545214e54097fdcb614214e540d6fdb6614214e540d77db5614214e540d7f9b0614214e54097fccb54a114e54097fccba22114e54097fdcb618a54a540d6fdb6618a54a540f67d655d9854a540f37d8561d654a540f73d54615654a540b7ddc3595834a540f75d53615734a540d77db5615634a540f37d8561d534a54097fdcb619534a540d6fdb6619534a540f7d9305d9534a540a7fcca6c5534a540b6fdc62d5824a540d6fdb6595824a540f6ed62595824a540f3dd8354d824a540f67d65615624a540) else (if i<3 then 0xe5fd875c6aa4e540e5fd765c6aa4e540a7fdc8586aa4e540a7fdc7586aa4e540e6fd62586aa4e540e7f581586aa4e540e7f581546aa4e540a7fdc5486aa4e540e7f571486aa4e54097fdc6aed874a54097fdc3aed874a540d7ddc26cc854a540d7ddc16cc854a540f6bd86595544a540d3fcc86d9534a54097fecc6d9534a54097fdc5aed824a540d7bd54aed824a540f6bd65551624a540f7ad54609624a540d7bd54aed624a540d7bdb8551524a540d7bdb6551524a540f7ad54609524a540f7ad54589524a54097fecc6e0a14a540e6fda72d9814a540e3fda7619814a540f6bcb6551814a540f3bd86551814a540f3bd54609814a540b7f5c5285814a540c7fda7aed814a54097fdc5aed814a540d7bd54aed814a54097fdc3aed814a540e5fda861d714a540f6bd54589614a540e7f5a7605614a540f7b554605614a540d7bdb8551514a540f7b554605514a540b7becc61d414a540f5bd875d9414a540f3bd87615414a540f5bd875d5414a540f6bd86595414a540f6bd76595414a540f73d85595414a540f6bd65589414a540f5bd875c5414a540d7bdb8551214a540d7bdb5551214a540f7ad54589214a540f5f9875d9304a540f3f987615304a540f5f9875d5304a540f6f986595304a540f6f976595304a540f77985595304a540f6f965589304a540f6f8c6605304a540f3f986605304a540b7facc605304a540b7f9c85c5304a540f5f9875c5304a540f7f181585304a540b7f9c8545304a540f7f181545304a540e6fd86596aa4a540e77d85596aa4a540e6fd6558aaa4a540c7fd866c6aa4a540c7fd856c6aa4a540a7fdc1aaa884a54097fdc5aed874654097fdc3aed874654097fdc2aed8746540d7ddc26cc8546540d7ddc16cc854654097fecc6c88546540d7edc36c88546540d7edc16c88546540d7eecc6c88546540e5fd875d9a346540e3fd87615a346540e5fd875d5a346540e6fd86595a346540e6fd76595a346540e77d85595a34654097fecc6e17346540a7fecc61da246540e5fd875d9a246540e3fd87615a246540e5fd875d5a246540e6fd86595a246540e6fd76595a246540e77d85595a24654097fdc7aed824654097fdc5aed8246540c7fda5aed824654097fdc3aed824654097fecc6e17246540e6fd6568d6246540e6fd656896246540e7eda56096246540d5fcc76e1524654097fecc6e1524654097fecc6dd5246540e5fda82dd5246540e5fcb76995246540e77da85d55246540c7fdb868d5246540e5fcb768d5246540c7fdb668d5246540e77d7568d5246540f57cb754d5246540f5ecb76095246540e7eda36095246540e7eda85c95246540e7eda65c95246540e7eda35c9524654097fdc8aed5246540c7fda8aed5246540d5fdc7aed524654097fdc7aed5246540c7fda6aed524654097fdc3aed5246540 else (if i<4 then 0xbd1d480f006231018d06f68a431a024012037a1bda18000a86009a018000006009a1bdac4067743000150c00043101bd823167603003e0dec088002a02000806000058800c00f8030000609b009826c022098078826c0e000409800002600c00000110089cec21731004281007320110122c4385fc2f226f0bc89a0111c270bf85fc2f22691340100000028003061804c186013061804c02000906004400100000040009b66b9a66799a6598e629865f9765b9665895a5494e529465093e4d9324b92647916439063f8f63b8e6378da358ce318be2d8ae298a2278962388a218821e8761b866188561484a1083e0e8360b82a098220781a0480a01801fe7f1fb7e5f77d9f47c5ef7b9ec7a9e97a1e7795e3785e077ddd771da765d7759d4749d1741cf739cd72dca721c6715c2701bf6f9bd6edb96ddb56cdb16bdae6b1aa6a5a7699a5691a3689a167d9d6719b6699966197655936458f6358b6258861984609805f97c5e9785d9755cd715bd6d5b16b5a567595635855f5755b565575555454d525414f5354b5294951d4550d414fd3e4f53c4e9394e5374d9364d5354d5354d1334cd334c9324c5304c1304b92c4ad2a4a52949d274992549123489204751b4651846116451124450f4350c429084210540d013fcfe3f4fd3f0fc3f0fb3e8f93e4f73d8f43ccf33ccf33c8f13c0ee3b4eb3ace939ce5390e2380de370da360d6354d434cd133cce330cb324c7318c4308c1300be2f0bb2e0b52ccb12bcad2b0ab2a8a92a0a6290a12789d2709a26496250932408d22887214832047f1f47b1e4781d8741c8701b86c1a8691a467198661946518c61184611846017c5f17c5d1705c16c5a1685a16458158541485013c4e1344d12c4912449120471184510c400f83c0ec3b0e4370d4330c42f0b42b0a42809c260942408c22084200781d0701b06819060170581505013048100380c02808018040080097fecc6e1735a540d5fcc76e1525a54097fecc6e1525a540f4fcb758d525a540f67d7558d525a540f57cb754d525a540f5ecb7609525a540f6ed635c9525a54097fdc8aed525a540d5fdc7aed525a54097fdc7aed525a54097fdc3aed525a540d6fd63aed525a540d5fcc76d5325a54097fecc6d5325a540f57cc7549515a540f5bcc7549415a540f73d75549415a540f7ad72549415a540b7becc549415a540e5fcc754aaa5a540e77d7554aaa5a540e7ed7254aaa5a540a7fecc54aaa5a540e6fda72d9814e54097fdc7aed814e540c7fda7aed814e540d6fdc6aed814e54097fdc6aed814e54097fdc2aed814e540d6fcc66e1714e54097fecc6e1714e54097fecc6dd614e540e7f5a7605614e540f6f4c6605514e540d5fcc76d5214e54097fecc6d5214e540d77dc86d4214e540e6fcc6606aa4e540a7fecc606aa4e540a7fdc85c6aa4e540 else 0x30000398004002000506852e044a0e4cec52e067000011000407e003806c000c1a0260008004000c07602c3621b1c05e01000471039d81100000bc00080dc00000100002f0002054003004400006d00080040000010004d480de0460008004000c37602601000203700000040a670b38580040000010001c2cea473b00081f0e20033000000003c2cc028012006504d03a807400600006980f828b35261db0ec3421a10a28cec00200000082f26b2015a1dac2c02b30b2198004000033000005400001f040306a616015985cd666a40155a9005509b80b0d89cef01673bc059cef0161b1834e02c0810305a900543420199858b8c1e489739de0685c6897171c25c06870b035e068ea581ac0d1c2c5c6752019e068e7603439d9d480660540060030002001006000007a01e0000050000c30001f0bc004000618000b85ec040011ea4e7673b3ea1ea60d2003000001c0007a93cc9e64fa87a983480c0000030000000800000000d800800005f58840c007535204a0008004000001000000407402200098a539901c01f000404401c01f1708044a0e01126760be99dcced0dd33b9c200c000000002a811000407e003800800001b0000008000002000013000400200001ed0d204f485862006000039de0100040050001cece20030000000800000203e00080018040011c40e7673b0180000e76067000012067631018d0c68090048a3380080ce0001bdac4067604c00112ec62037b0462cec08c0021bd8110005404001019c000b1003381f00ce00003586c40d600200050dc002352a1b800406e00005e0d4800340400080dc0f94370408c2c0803101881cec6f60370000edc06e0000200c4061730b01b800061603700002540a603700000dc0f8b0b01b81f006e000a1bd01286e00c000033c0020000008000fa80330a2d1ec28b35201d8b8d11414517183c80a00330000b8d03881a019207385e33b0198f5083801b1a9006f00806b3dbd068067b7b0a2e0bc06703300d907012fa36d1b0b3346c2cc01980000d6359035ac2c04a41c20d03880d6145061802028a06b012a07000a0d140e010006b81c020009703805040e01000a181c065e013017804c05e01301600002100cc6b241c20d001400c84d002800000a0010018004006001006000437a3a90dee148e7603000001206761)))
def uL30 : PT := (425,5,8,10,uL30F)
def uH0_30F (i : Nat) : Nat := 0x281b080270241707c1d04c0104006060160782b0682621c0e0a41c090210080b094043300f000230302f020190540003428044140b01200c050882a0b82d0000001d548318c2423093460800c0000
def uH0_30 (h : Nat) : Option (Nat × Nat) := lw0 17 53 6 10 6 4 uH0_30F h
def uL31F (i : Nat) : Nat := (if i<3 then (if i<1 then 0xe4fda89de6646540e4fda59de6646540e4fda39de6646540e4fda29de6646540f0fe889de664654087fccb6a2554654087fccb68e554654087fccb68a5546540a77dc82ea5546540a77dc32ea5546540a77dc22ea5546540a77ccb6a25546540a77ccb68e5546540a77ccb68a5546540e37da8a225546540e37ccaa225546540e37cbaa225546540e37da3a225546540e37da2a225546540e37eaaa225546540e57da89de5546540e57da39de5546540e57da29de5546540e57eaa9de5546540f17e889de5546540e67da899a5546540e67da399a5546540e67da299a5546540f27e8899a5546540f47e7799a5546540b5ddc72163346540b6ddc62163346540b7cdc22163346540b7d5c12163346540b7d9c02163346540b6ddc614a3346540e3dccaa223346540f1de889de3346540f2de8899a3346540f4de7799a3346540e75cca9563346540f35e889563346540f55e779563346540f65e66956334654087fccb6a2224654087fccb696224654087fccb68e2246540e3eda2a222246540e6eda299a2246540e76da29562246540a7edc82ea2246540a7edc52ea2246540a7edc32ea2246540b5edc72e22246540a7eccb6a22246540a7eccb6962246540b5edc72162246540b6edc62162246540b7cdc32162246540b7e5c12162246540b7e9c02162246540a7eccb68e2246540e3eda8a222246540e3eccaa222246540e3ecbaa222246540e3eda5a222246540e3eda3a222246540e3eeaaa222246540e5eda89de2246540e5eda69de2246540e5eda59de2246540e5eda39de2246540e5eeaa9de2246540f1ee889de2246540e6eda899a2246540e6eda599a2246540e6eda399a2246540f2ee8899a2246540f4ee7799a2246540e76cca9562246540e76cba9562246540e76da89562246540e76da69562246540e76da39562246540e76eaa9562246540f36e889562246540f56e779562246540f66e669562246540e7ccba8ce2246540f3ce888ce2246540f5ce778ce2246540f6ce668ce2246540f74e558ce2246540b5f5c72161146540b6f5c62161146540b7d5c32161146540b7e5c22161146540b7f1c02161146540b6f5c614a1146540e3f5a8a221146540e3f5a7a221146540e3f5a5a221146540e3f5a3a221146540e3f5a2a221146540e5f5a89de1146540e5f5a59de1146540e5f5a39de1146540e5f5a29de1146540f1f6889de1146540e775a59561146540e775a89561146540e775a39561146540e775a29561146540f376889561146540f576779561146540f3d6888ce1146540f5d6778ce1146540f756558ce1146540e7e5a288a1146540e7e5a888a1146540e7e5a588a1146540e7e5a388a1146540f3e68888a1146540f5e67788a1146540f7665588a1146540f7c63388a1146540a6bdc4aaa664e540a7b5c4aaa114e540 else (if i<2 then 0xf74e558ce224a54087fdc82ea114a54087fdc52ea114a54087fdc32ea114a54087fccb6a2114a54087fccb69e114a540c7f4ba606114a540f7d1314c2114a540c3fcbaa22114a540f3b541a22114a540c5fcba9de114a540f5b5419de114a540c77cba956114a540f73541956114a540c7dcba8ce114a540f7a54188a114a540a7f5c82ea114a540a7f5c52ea114a540a7f5c32ea114a540a7f6cc2ea114a540a7f4cb6a2114a540a7f4cb69e114a540b6f5c62d6114a540b7e5c22d6114a540b5f5c7216114a540b6f5c6216114a540b7d5c3216114a540b7e5c2216114a540b7f1c0216114a540b7b4cb552114a540a7f4ca54e114a540f7d1534c2114a540a7f5c8aaa114a540a7f5c5aaa114a540a7f4caa22114a540e3f5a8a22114a540e3f4caa22114a540e3f4baa22114a540e3f5a7a22114a540f3b554a22114a540f3f130a22114a540e3f6aaa22114a540e5f4ba9de114a540e5f5a89de114a540f5b5549de114a540f5f1309de114a540e5f6aa9de114a540f1f6889de114a540e6f5a899a114a540e6f5a799a114a540f6b55499a114a540f6f13099a114a540e6f6aa99a114a540f2f68899a114a540f4f67799a114a540a7f4ca956114a540f73554956114a540e774ca956114a540e774ba956114a540e775a8956114a540f77130956114a540e776aa956114a540f37688956114a540f57677956114a540f67666956114a540e7d4ba8ce114a540f3d6888ce114a540f5d6778ce114a540f6d6668ce114a540f756558ce114a540e7e4ba88a114a540e7e5a888a114a540f7a55488a114a540f7e13088a114a540f3e68888a114a540f6e66688a114a540f7665588a114a540f7c63388a114a540c7ddca6cc854654097decc6cc8546540c7edca6c8854654097eecc6c8854654097f6cc6c48546540a5fdc7215a346540a6fdc6215a346540a7ddc3215a346540a7edc2215a346540a7f5c1215a346540a7f9c0215a346540a5fdc7215a246540a6fdc6215a246540a7ddc3215a246540a7edc2215a246540a7f5c1215a246540a7f9c0215a246540c5fdba2dd524654095fdc7aed5246540c6fda86d8524654096fecc6d85246540c6fdb668c524654096fdc6aed8146540a5fdc7216aa46540a6fdc6216aa46540a7ddc3216aa46540a7edc2216aa46540a7f5c1216aa46540a7f9c0216aa46540a6fdc614aaa4654087fccb69e884654087fccb68e884654087fccb68a8846540a3fdc52ea8846540a3fdc32ea8846540a3fdc22ea8846540a3fccb69e8846540a3fccb68e8846540b2fdc62ca8846540a3fccb68a8846540b2fdc614a884654095fccb54a7746540e1fda8a227746540e1fccaa227746540e1fda3a227746540e1fda2a227746540e1feaaa227746540e2fda7a226646540e2fda3a226646540e2fda2a226646540 else 0xc7f8ba4c2884a540a3fdc52ea884a540a3fdc32ea884a540a3fdc12ea884a540a3fecc2ea884a540a3fccb69e884a540e3bcba552884a540a3fcca546884a540e3bcba506884a540a3fcca4c6884a540e3f8ba4c2884a540f3d9534c2884a540f3d9314c2884a540a3fdc5aaa884a540a3fdc1aaa884a540a5fcca54e774a540a5fcca4c6774a540f5d9534c2774a540f5d9314c2774a540a5fdc8aaa774a540a5fdc5aaa774a540a5fdc1aaa774a540a5fccaa22774a540e1fccaa22774a540f1bd54a22774a540f1bd41a22774a540f1f930a22774a540e1feaaa22774a540a6fcca54e664a54096fccb606664a540f6d9534c2664a540f6d9314c2664a540a6fdc8aaa664a540a6fdc5aaa664a540a6fdc1aaa664a540e2fda7a22664a540f2bd54a22664a540f2bd41a22664a540f2f930a22664a540e2feaaa22664a540e4fda89de664a540f4bd549de664a540f4bd419de664a540f4f9309de664a540e4feaa9de664a540f0fe889de664a54087fdc82ea554a54087fdc32ea554a54087fdc12ea554a54087fccb69a554a540f759534c2554a540c3fcbaa22554a540f33d54a22554a540c6fcba99a554a540f63d5499a554a540a77dc82ea554a540a77dc32ea554a540a77dc12ea554a540a77ecc2ea554a540a77ccb69a554a540b57dc72c6554a540b57dc7206554a540b73ccb506554a540a77cca4c6554a540f759314c2554a540a77dc8aaa554a540a77dc1aaa554a540a77ccaa22554a540e37ccaa22554a540e37cbaa22554a540f33d41a22554a540f37930a22554a540e37eaaa22554a540e57da69de554a540f53d419de554a540f579309de554a540e57eaa9de554a540f17e889de554a540e67cba99a554a540f63d4199a554a540f6793099a554a540e67eaa99a554a540f27e8899a554a540f47e7799a554a540b5ddc7216334a540b6ddc6216334a540b7cdc2216334a540b7d5c1216334a540b7d9c0216334a540b5ddc7206334a540a7dcca546334a540a7dccaa22334a540e3dccaa22334a540f1de889de334a540f2de8899a334a540f4de7799a334a540a7dcca956334a540e75cca956334a540f35e88956334a540f55e77956334a540f65e66956334a540b5edc7216224a540b6edc6216224a540b7cdc3216224a540b7e5c1216224a540b7e9c0216224a540b5edc7206224a540f7c9534c2224a540f7c9314c2224a540e3eda8a22224a540e3eccaa22224a540f3ad54a22224a540f3ad41a22224a540f3e930a22224a540e6eda899a224a540f6ad5499a224a540f6ad4199a224a540f6e93099a224a540f2ee8899a224a540f72d54956224a540e76cca956224a540e76da6956224a540f72d41956224a540f76930956224a540f36e88956224a540f66e66956224a540f3ce888ce224a540f6ce668ce224a540)) else (if i<4 then 0xf4ed639de225a540f5ad419de225a540e5eeaa9de225a540f1ee889de225a540e76cca956225a540e76cba956225a540f66d63956225a540f72d41956225a540e76eaa956225a540f36e88956225a540f56e77956225a540e7ccba8ce225a540f3ce888ce225a540f5ce778ce225a540f74e558ce225a540f57677956115a540f5d6778ce115a540f756558ce115a540f5e67788a115a540f7665588a115a540f7c63388a115a540c6fdba2d9814e54096fdc6aed814e54095fecc6dc814e540c77dca6d4214e540977ecc6d4214e540c7bd766d2aa4e540c7bdb4606aa4e540a5fdc7206aa4e540c7bdb4206aa4e540c7bdb45c6aa4e540c7bdb4586aa4e540c7bdb4546aa4e540c7bdb4146aa4e540c7bdb4486aa4e540a6fdc6086aa4e540a77dc5086aa4e540c7bdb4086aa4e540a7f9c0086aa4e54096fccb606664e540e4feaa9de664e54087fccb69e114e540a7bdc4aaa114e540a7f5c82ea114e540a7f5c52ea114e540a7f5c22ea114e540a7f4cb69e114e540b6f5c62d6114e540b5f5c7216114e540b6f5c6216114e540b7d5c3216114e540b7e5c2216114e540b7f1c0216114e540b6f5c614a114e540e3f4baa22114e540e3f5a7a22114e540e3f6aaa22114e540e5f4ba9de114e540e5f6aa9de114e540f1f6889de114e540e6f5a799a114e540e6f6aa99a114e540f2f68899a114e540f4f67799a114e540e774ba956114e540e776aa956114e540f67666956114e540e7e4ba88a114e540e7e6aa88a114e540f6e66688a114e540f7665588a114e540c7ddca6cc854a540d7d9c06cc854a54097decc6cc854a54097eecc6c8854a540c7f5ca6c4854a540d7b5c46c4854a54097f6cc6c4854a54087fdc12e9534a54095fdc7aed524a540c6fdba2d9814a54096fdc6aed814a54095fecc6dc814a540d5bdb7550814a54087fdc82e9514a54087fdc32e9514a540c7f4ba605514a540b5bdc7215414a540b6bdc6215414a540b79dc3215414a540b7adc2215414a540b7b5c1215414a540b7b9c0215414a54087fdc82e9314a54087fdc52e9314a540c7f4ba605314a540f7c5324c5214a54097f9cb215304a540b5f9c7215304a540b6f9c6215304a540b7d9c3215304a540b7e9c2215304a540b7f1c1215304a540f7598554d304a540b7dacc54d304a540f75953549304a540b5f9c7205304a540b7d9c3205304a540a7f8ca545304a540b7d9c3145304a540b7d9c54c5304a540f7d1814c5304a540b7dacc4c5304a540f7d131485304a540a5fdc7216aa4a540a6fdc6216aa4a540a7ddc3216aa4a540a7edc2216aa4a540a7f5c1216aa4a540a7f9c0216aa4a540c7f5b1606aa4a540a5fdc7206aa4a54087fdc52ea884a54087fdc32ea884a54087fdc12ea884a54087fccb69e884a540c7bcba552884a540c7bcba506884a540 else (if i<5 then 0x800400330be17e013009804226913480880420d10700080044023069876c1a60d30ed834c1a61db06900843b60d306983401960d02641b7e2e06a028fc5c00104c836c1320db04c836c1320db06682bc16e0a103783501460d405183501460cd05961ec18407206a029196e0b2002822c1cc05f05b04380740afc1802bf060078c1801e3060078c1801e106006b41801e306002d05c81e816a03a05a80e800a003001101080810e20260118a480600281e007803a01e00e8011e2e0011010808404629314880d804c02601089a44dc02000805a002016800805a469002800e62000200160130098042269134004c5262910198a5804c026013008830c0231498a4c526291080841eaf3f93c9e3f1787c3e0eff7fbfdfeff7fbfdeeef73b7dbed767b3d9ecf67b1d7ebf5fafd7ebf5fafd7ebf5fafd7ebf57a5d1e7f3b99c8e370b81beddedf6db4d96bf5badd6eaf51a7d369749a3d1687419fcf6773b9dcee773b9dcee773b9dcee773b9dcee773b9bcce632f95c9e4b218ec662b1387c2e0f017ebe5eaf176ba5c6df6cb4d9ecb63b0d7ebb5aac556a752a75329548a3d1687419fcf677399b4d26530974b2572a9449e4d259248e45208fc7a3b1b8d46631178b452271288c421f0f87436190c85c2a110783416090481c0a0301803fdfcfd7ebf5f6f97bbd5e6f278bc1deee76bb1d6ea74ba1cee672b91c6e271389c2e07037dbcdd6eb75badc6db6db6db6d365b0d76b355a8d369b4da6d369349a4d269345a0cf6733598ca64b2190c76331588c36130582c0602fd7cbd5eaf57abd5eaed72b65a2c960af572b558ab552a550a75329146a250a813e9e4ea71369a4ca612e954a24d249148a45229047a3d1e8e46a31188c45a2d148944a25128843a1d0e8642a150a8542a150a8542a150a8441a09048241209007f3e9f0f6793b9d4e671371b0d4683318cc25f2e168b2572a94ca24f2692c92472290c82401f8f87a3c1d8e872391c0e070381c0e070381b8dc6e371b8d46631180bc5c2d160ac542a150a8542a148a45229148a05028140a04e2612890462211088442211088442210078381c0e070361a0c8602e160a8502612088401e0f0783c1e0f070381c0e070381a0d068341a0d06830180c06030180c06030180c0602c14090401c0c05028140a050201008040201006030180c06030180c0602010080402010080200c5fdba2dd525a54095fdc7aed525a54095fccb54a775a540a77dc82ea555a540a77dc32ea555a540a77dc22ea555a540e37cbaa22555a540f47d639de555a540f53d419de555a540e57eaa9de555a540f17e889de555a540f1de889de335a540e75cca956335a540f35e88956335a540f55e77956335a540a7edc82ea225a540a7edc52ea225a540a7edc32ea225a540e6ecba58e225a540e3ecbaa22225a540 else 0x32dd81608e05d022c08c008f170009834c0b988001400640660d302d834c0b61d82bc0020700770c2c1000db185c081f5373bbc25d490418370168204008072016000c14e00303c000c13e0780670206eb202c01660dc05b83701680101d807841b80b400202d07401bc058008002800800330bc02601089b804226e0101ce072023813bc5c00206a028c084c21f1700e80d605005a306816c0080358c2c03342106781e80720e205c002c0d780bc10e02f04380b025e02f04280bc10e02c09600406281e80a00f105d20700d602a20e023806604ec0d013b03404e40d013b03404ec0d013a0340f2069406a03881a01183cb03404e027010003e40401d206904301c065c0701c501c40e038b008050c02014300805000101430080500000142ea400402f00d405a03e070000c0f403a06902e40f40c406200d01a40050018004008404202201080840420e107083441c20e001000280420e106883841c002001000280461db02d83480401a106883841c0020010002c3b605b069834c3b605b06811e07807981e00740a401e01ac83580420220ec80883b00478b80020042020c2f00840420e1070008001402302d834c0b605b069816c1ac02601089b804226e0110388044026013009804c02051700841a20e1071834c3b605b069834c3b605b068876c0b605b06816a02d07b00b401603903c000405a001016dd48003804000a02c00280b000a02c00280b00411ec00b30b0)))
def uL31 : PT := (532,5,8,9,uL31F)
def uH0_31F (i : Nat) : Nat := 0x1781d0a854059df0542368a4c08400b301e678560505b675e217ccc40024099a10b8123000c430180881f21c2c0ac1909c257806a06807081941881b58304048a0031d100111535010310b000a43
def uH0_31 (h : Nat) : Option (Nat × Nat) := lw0 24 48 6 10 6 4 uH0_31F h
def uH1_31F (i : Nat) : Nat := 0x671308687201000704066663090502000003005088008040
def uH1_31 (h : Nat) : Option (Nat × Nat) := lw0 8 19 5 8 4 4 uH1_31F h
def uL33F (i : Nat) : Nat := (if i<2 then (if i<1 then 0x61519503bfed930a8ca81dff6c58546540effb0cbaa32a077fd8759519503bfec2aca8ca81dff6dd8346540effb0ec1a32a077fd7660d19503bfebab068ca81dff5958346540effb64c1a32a077fdb160d19503bfedc2e68ca81dff6d97346540effb0cb9a32a077fd855cd19503bfeb2ae68ca81dff6c57346540effb0eb1a32a077fd8558d19503bfebaac68ca81dff61d5346540effb6ca9a32a077fd8654d19503bfebb2a68ca81dff5955346540effb64a9a32a077fdb154d19503bfedbb048ca81dff61d8246540effb6cc1232a077fd7660919503bfedab048ca81dff2d58246540effb0ac1232a077fd7560919503bfeb2b048ca81dff6cd8246540effb06c1232a077fd7360919503bfeb1b048ca81dff54d8246540effb62c1232a077febb60919503bfec32e48ca81dff6157246540effacab9232a077fd835c919503bfeb1ae48ca81dff54d7246540effb0eb1232a077fd8558919503bfebaac48ca81dff60d6246540effae6b1232a077fd5358919503bfec12c48ca81dff6e15246540eff970a9232a077fdb754919503bfec3aa48ca81dff6d95246540effb0ca9232a077fd7654919503bfec2aa48ca81dff5955246540effb66a9232a077fd8354919503bfeb9aa48ca81dff58d5246540effaa6a9232a077fd8254919503bfeb12a48ca81dff6c55246540effd76a9232a077fd8614919503bfeb18a48ca81dff6e13246540effb0e99232a077fdb64c919503bfec32648ca81dff5d93246540effb6a99232a077fd854c919503bfe42a648ca81dff5d53246540effaca99232a077fd824c919503bfeb12648ca81dff5493246540effb0ec0a32a077fd8560519503bfebab028ca81dff60d8146540effae6c0a32a077fd5360519503bfec13028ca81dff5498146540effa64c0a32a077fd855c519503bfec1ae28ca81dff54d7146540effb04b8a32a077fd525c519503bfe992e28ca81dff61d5146540effb0aa8a32a077fd8354519503bfeb9aa28ca81dff54d5146540effb04a8a32a077fd5254519503bfe992a28ca81dff61d3146540effb0a98a32a077fc854c519503bfebaa628ca81dff6093146540effaa498a32a077fd8748519503bfec2a428ca81dff2152146540effaea90a32a077fd8348519503bfeb9a428ca81dff54d2146540effb0490a32a077fd5248519503bfebad108ca81dff5ce8846540effae544232a077fd52a2119503bfe995108ca81dff5c68846540effaa344232a077fd31a2119503bfe90d108ca81dff61a5546540effac72aa32a077fd8295519503bfeb14aa8ca81dff4ca5546540effb032aa32a077fd3195519503bfe90caa8ca81dff61a2246540effb0b11232a077fc8588919503bfeb2c448ca81dff60e2246540effac711232a077fd5388919503bff444448ca81dff9562246540 else 0x81dff5d9514e540effb64a8a72a077fd8254539503bfeb92a29ca81dff589514e540effb02a8a72a077fd8214539503bfedb2429ca81dff5d9214e540effb6a90a72a077fd8548539503bfebaa429ca81dff595214e540effb0290a72a077fd7148539503bfea8a429ca81dff614214e540effb0f08a72a077fd8584539503bfec14229ca81dff5ca114e540effaa508a72a077fe8884539503bfe58b0e94a81dff618a54a540effb6ec2a52a077fd8761529503bfedb30a94a81dff5d9854a540effb64c2a52a077fdb161529503bfec32ea94a81dff6e1654a540effb6eb2a52a077fd8759529503bfec2aca94a81dff6cd654a540effb64b2a52a077fdb760d29503bfec3b0694a81dff5d9834a540effaeac1a52a077fd6560d29503bfed930694a81dff6c5834a540effb0cb9a52a077fd855cd29503bfeb2ae694a81dff61d634a540effb6ab1a52a077fd8558d29503bfebaac694a81dff61d534a540effb6ca9a52a077fd8654d29503bfebb2a694a81dff595534a540effb64a9a52a077fdb154d29503bfe5ab0494a81dff615824a540effacac1252a077fd8360929503bfea9b0494a81dff615624a540effb06b1252a077fd5358929503bfec32a494a81dff615524a540effacaa9252a077fd8354929503bfea9aa494a81dff619324a540effb0a99252a077fc854c929503bfeb2a6494a81dff614a14a540effb0ec0a52a077fd7660529503bfe5ab0294a81dff615814a540effaeac0a52a077fd6560529503bfec1b0294a81dff5cd814a540effac6c0a52a077fd5360529503bfec130294a81dff549814a540effa64c0a52a077fd865c529503bfec2ae294a81dff595714a540effb06b8a52a077fd535c529503bfec3ac294a81dff615614a540effaeab0a52a077fd8358529503bfea9ac294a81dff61d514a540effb0ca8a52a077fd7654529503bfec2aa294a81dff60d514a540effae6a8a52a077fd6354529503bfea9aa294a81dff609514a540effaa4a8a52a077fd3254529503bfec3a6294a81dff619314a540effb0a98a52a077fc854c529503bfebaa6294a81dff595314a540effb0c90a52a077fd8548529503bfe42a4294a81dff595214a540effb0690a52a077fd5348529503bfebad1094a81dff5ce884a540effaa544252a077fd32a2129503bfe50d1094a81dff5c6884a540effaa344252a077fd31a2129503bfe90d1094a81dff61a554a540effac72aa52a077fd8295529503bfeb14aa94a81dff4ca554a540effb032aa52a077fd3195529503bfe90caa94a81dff61e114a540effb0b08a52a077fd8384529503bfea9c2294a81dffa22114a540effb6cc3a32a077fdb561d19503bfed9b0e8ca81dff6c98746540effb62c3a32a077febb61d19503bfedbb0a8ca81dff61d8546540effb6cc2a32a077fd76) else (if i<3 then 0x8824418218402008c18218402008cf49e53be764ea9cf39270cde9b93666b4d399f33264cc69873025ecba96f2ce584ad95529e51ca093b2664b49391f23244c869092023ec798e91c234c668c717e2e4588a913e25c478870fe1e43986d0ce174288490860f41c83305e0a41181b02a03c04800ff5fd3f67e6fc1f6bea7d0f95f13de7b6f61ea3d079af29e33c277ceeddbbb3760eb9d63a974ee91d0b9e734e61cb39271ee31c4b86706dfdbe3796eedd1b8b6e6d6d9db23616bad65aab5169ad29a3343680cf59cb37664cbd96b28648c818e31862ac4d8830d612c1d81aff5f6bd978aee5d6b9971adc5b0b4966ac958cb095f2b956cac9572ab54ea894fa9b52ea5148a8d512a0d3fa7b4ee9c937a6a4cc9892fa5b4ac94d2824c49091520a3f4788e11a22f45689d11a2143c86d0ba1241e829032023fa7e4fb9f53e67c4f79eb3d2798f21e13bc770ec9d63a8744e71ca38e710e11c037c6f0dc9b63666c4d61a8348684cf19b32e654c919031c62cc49863065fcbe1792ea5ccb896e2d4598b21602ba568ab9542a2538a51472865009e13826a4c89712b2504949011c2304548910d214414810fe1f63dc798ef1d83a8730e41c23786d8d81aa348670cc19431c620c217e2f45d0b61682c0568aa14e2905089e1382644b89412223c4608910c20c4007d0f61e03a0710dc1ac348660c81842f85c0b21582904d0921182104007a0e81b03205c0ac140260480840e81802804006008008003bfed9b0eb4a81dff6c9855a540effaeac1ad2a077fdb85cd69503bfec2ae6b4a81dff6c5735a540effb0ea9ad2a077fdb254d69503bfed8aa6b4a81dff6d5825a540effaeac12d2a077fd7360969503bfea9b04b4a81dff615725a540effb06b92d2a077fd535c969503bfedc2a4b4a81dff6dd525a540effb0ea92d2a077fd8554969503bfed9aa4b4a81dff60d525a540effae6a92d2a077fd5354969503bfec12a4b4a81dff6c5525a540effd76a92d2a077fd874c969503bfedaa64b4a81dff615325a540effaea992d2a077fd524c969503bfea9ae2b4a81dff549715a540effa64b8ad2a077fd7354569503bfea9aa2b4a81dff5c9515a540effaa4a8ad2a077fd3254569503bfebaa62b4a81dff5c9315a540effaa498ad2a077fd7548569503bfeb9a42b4a81dff54d215a540effaa490ad2a077fd8295569503bfe994aab4a81dff4c6555a540effa432aad2a077fd8588969503bfea9c44b4a81dff956225a540effb6ec0a72a077fdb660539503bfebb3029ca81dff6c9814e540eff964c0a72a077fd5260539503bff5db029ca81dff548814e540effb70b8a72a077fdb65c539503bfeb2ae29ca81dff6c9714e540effac4b8a72a077fd525c539503bfec0ae29ca81dff61d614e540effaeab0a72a077fd7258539503bfea92c29ca else (if i<4 then 0x202d01a01ac0202d01a43481a20e03903181a20e01ac020200748a282186a83582001a8580a282120201a06702001a20e01aa4ba0e021830035a0e021020023a0e02001a019c02617806c02021002ac2019813b1b006811c0e01a879071012811835c0e01181a40e02802001181a40e01a84f81a40e01281a40e03906a81a00740201d40580101a405a0200122681d0011ac86180106408b01a01520e24ca0201a84d01aa4ba0e3bd85c86682801c9661db81d20224020201a04086781a05c82006586281a01d20e08b20201a05e51706b01e06aa0d17182820e019c26801035b33019c26a4b98583786781a02802001181a20e20581d4269bd81a20207581ad1740201a00651740201a00651720d02001a20e51740201a006234803879803877803876003a34e179db9bd8738038798028798043bda348028552348debbd873002a34e1786b04d01883c8380de82bc34a18166001a1816640e1d4a18018c0e41825340e03c8de838063001800971877801a34801971818c0e41807284601884603980094b9db830a180de831030a180de83103088740e05b02407dc0e068a3482b171c0e018824218018c0e03ac0e3bd826001a186178760010760043bda348010552348debbd8730011db82781f20218807300421806e04d1db83c8380de86300106320e41814ba0e030c180300de82441821820e234e179db98805f00106b842818c18072842842839818a1814ba0e04281883021814ba0e1bdc348de82e4348de82e41840202e018c348de82e41840202e01882441820e01882e001434bbd87300105c99da020223bd8508011bd874822bbda348015bda1820206a818a18202055018dbd988073002dbd82ba34bbd82620e061dbdc1821820e2180228465bd830a0201883005182620e5bd99d8730015bd80123483ebbda1861799d98802200121820206a81881d018a0e0630011bdc1301d40e03280101d018c0e01d018c0e3bd82600141301d40e41301d40e41301d40e22901d018c0e06340e032c0e3bd82640e3bd80443480443484d000c34804434846000c349db824000c348044348dec02042c34813808c3484a000dbd84a61780084a000dbd84a1c200884a61784280894be17827800802c18027e17800c18046000c1820e027e17808bbd802c1841801380881c61780081c617800a02000a26800a5301c61780898801c61784281d0009c201d617800a02000a26800a5301d61780080094b81d6178008014183bd80141805c84e04d05c84684641821805c842bbdc1818807305cc1821305c81384a000bbd820202000a1801c16601d61780086a81e234830a0201883ac1818807301e21820201882e02781d20e0dec26a3481c42681d42686aa34808c18218067008c1821820201e008837a022348afc18218008861c1820203081d4182180 else 0x77803bbd873002c33a5345d877801c338728461c22348078248fcc0e3bd826001a34801bbd87300123386e04d43394ba0e43382502420e433872843a3394ba5d82494ba0e3bd8730013bd8508012338228755bd87325dbbd82620e5bdc22a71a5da3382284605182620e07687325dbbd82300119d988022001413074063bbd826001233813c1340e23394bc0e3bd82640e034440024840c070d8835813841035834020846434c07020820407035bbd823407433813834407433c05851834407048011835c073bd81240e188011835c070d88344070d8c0703400bc0b0344073bd823407433a3381e06043381383ba0e012205a3482420700ba0b034207433a33867009c33826009824433a33c02009ba9075800ba906c80085e8551d4ba906080082e81c985a02008bbdda941ba1bc022021db98585e000823402040ba9075800856800a1b841839044000c1b84082e41b822840ba95bd800875c1b87502d41b84d82d41b84282d3bdc0203a02d41b8550203bd823000c1ba1bc0202041b84282041b82e02000086783940206080602f800c0b05500bbbd823000a1bc0b40200bc0205100ba1b80c037ba900b01d000bbd80b01d00080b01d000a0206786741ba1b80607441ba1b86700641ba1b80605f84280604319dc1b823040c1ba1bc0200608a202073819c020798028798043bd87200287c8558a2866bbde17ba9067802c4cc0204d01a87200285a80283781a8748a2da90720029ea03a80ebbd8376178779660019bd877c0e2549d481ac0e25301ac0e237171c0e061617ba9062801c4b81ac0e07d8458a281ac4bc0e05908a0750599ea03a80ea66971c0e03008a05b40e02440e07902806881903ac0e071025171c0e25482402840e03783ac0e3bd819023c0e019023c0e202226801019e178010378199ea00106120e02420e06582500d8358015a9030171a0d035a0e00d8355bd86a8720010199cc8010a281980119dcc25bd86186800dcc2023a0e00117181cd1b00120200116640200101c814019c025a90758043bdc0220201a8d881a037a0205e5a901a185804067da908a20204d07a85e837835da9062a0e5a940584c01a20e03005e8359dbda902420d45e81a20e185a0205e02dbbdc05a0202d82801a01a09320206402dc4040204081a87a8408a2835841828039040c4001a20e44020e08a02484f82d07501ac2cc0)))
def uL33 : PT := (382,4,8,11,uL33F)
def uH0_33F (i : Nat) : Nat := 0x13818604f00d801012a0b50488178130055021030811a07a01500640500d802802c00ba07107382e015c03901c036c14608505983000ae07b01081b813a01101b834c1a406a004031413c04502e01b010e07802c013007401703202281a206801482a813e0bc01883880e6c980708158060082040823c0ca0c404c83300fe0c7003032c07acb103a8120172024013012413601503b809417a00964a00ec02009401680140be0d506b002c00002c02880480960c606a022c1640a605402941c801f00781d01560bf05002dc54e07005d038c1ba04005600cc1c004d047025c0e40b1053826805e08c04232e40ec06b04000ad92a08803e82181bc0630510198194c9602c808805c0be03082d000203e05b0a601b201e052001c03009c073010c1d003f041812818204606b824c08e01a001818819c04105081bc1be0bb00600d407800e06e01b40a605404481e40260c900b00500fc06075a016c0b403200680d00ce01d0480000000002010024815e29f054b27406c0c8066836815a0960050394038052022008c0f80cf06801a404e2a60a1f05070809041400230106014d703801060203050003001600054105044200002b0c080700010a190403010b05001425262a0a0000000400010e052c00000021250631000b0b010f58000200002b00015f02000d0b1e448c01000401300004390002e3001a0a0002002000050027080000000a092c3700000e00
def uH0_33 (h : Nat) : Option (Nat × Nat) := lw0 123 247 8 13 9 4 uH0_33F h
def uL34F (i : Nat) : Nat := (if i<7 then (if i<3 then (if i<1 then 0x88969503be719c44b4a81d7d9de115a540eeecab08ad2a077d63384569503bf311422b4a8157f6dc814e540adfb6c10a72a0577db508539502bfcd80429ca819bf69e664e540cdfd5533272a074fe77999395033fa5d4229ca819fd69e114e540cfed5508a72a073f68884539503afb3bc229ca81dbd99a114e540eeecab08a72a077e62284539502afedb90a94a815bf6d8854a540afbb6642a52a057edb221529502bfad890a94a815fe6c0854a5408ff974a9a52a055fdb7205295023fe5d2a294a811ff2e9314a540efb2a698252a077d9314c1295023fedc55494a811ff6d6aa4a5408ffb6355252a047fcbaa21295031fe5d51094a818ff69e884a540e77aa944252a073bd41a21295039fc9851094a818ffaaa884a540cbfb4d3ba52a075bd549dd29503adea0cee94a81d7e4c2774a540cbfd553ba52a071fe889dd2950337ed44cc94a819bf69e664a540ed7aa933252a076bd4199929503b7c984cc94a819bfaaa664a540e5fd1133252a074fe77999295023fe5d4aa94a81dcf552554a540cef9752aa52a0677da695529503b9ea0caa94a81dde4c2554a540cefd552aa52a0737e8895529503abf3bcaa94a81d9f99a554a540e7bd1119a52a075de778cd29503b6f3346694a81dd7956334a540cfdb5111252a067eda688929503bd6aa44494a81deb506224a540efd26111252a073ee8888929503b773344494a81ddb956224a540ef9c6711252a047fcba84529503bdaa0c2294a819fd2ea114a540cfeb5108a52a067f5a784529503bdaaa42294a81dfc4c2114a540cfed5508a52a073f68884529503afb3bc2294a81dbd99a114a540eeecab08a52a077d63384529503bf31142294a8157f6dc8546540adfb6c42a32a057ddb321519502bf6d910a8ca815fd6c48546540aff36042a32a056fdb6149195031fed45108ca818ff2ea8846540c7fb4f44232a063fda3a21195031fed15108ca818ffaaa8846540cbfb513ba32a065fda69dd195032fed1cee8ca8197f68a7746540cbfd553ba32a071fe889dd1950337ed44cc8ca819bf69e6646540cdfb4b33232a066fda39991950337ed14cc8ca81cbfa226646540e9fcef33232a0677cba955195033bed44aa8ca819df68e5546540cefb452aa32a0677eaa955195039bf444aa8ca81d5f9de5546540ecfccd2aa32a073de888cd19503aef3bc668ca81db799a3346540eebcab19a32a067eda2889195033f65d4448ca819fb6a22246540cfdb4d11232a067eda5889195033f6d1c448ca819fbaaa2246540e7dd1111232a075ee7788919503b77334448ca81ddb9562246540ef9c6711232a067f5a8845195033fad3c228ca819fd6961146540cfeb4708a32a067f5a2845195039fb444228ca81d7d9de1146540eeecab08a32a077d63384519503bf3114228ca811ef6d2aa4e540 else (if i<2 then 0x81cff58e8846540e7faa744232a073fcb2a21195039feb95108ca81cff58a8846540e7faa544232a073fc52a21195039fe995108ca81cff5c68846540e7faa344232a073fd31a21195039fe90d108ca81d7f61a7746540ebfb0b3ba32a075fd659dd19503afec1cee8ca81d7f58e7746540ebfaa73ba32a075fd829dd19503afeb14ee8ca81d7f54a7746540ebfa653ba32a075fd819dd19503afea8cee8ca81d7f4c67746540ebfa433ba32a075fe889dd19503b7ec3ccc8ca81dbf6166646540edfaeb33232a076fd8399919503b7eb9ccc8ca81dbf54e6646540edfb0533232a076fd7299919503b7ea94cc8ca81dbf14a6646540edfa6533232a067fda895519503bbec2caa8ca81ddf5965546540cffb472aa32a0777d53955195033fed14aa8ca81ddf54a5546540eefaa32aa32a067feaa955195039ff444aa8ca81dbf99a5546540eef9712aa32a0777d8795519503bbec34aa8ca81ddf5da5546540eefb072aa32a0777d7395519503bbeb1caa8ca81ddf2ca5546540eefb052aa32a0777c8295519503bbeb94aa8ca81ddf58a5546540eefa652aa32a0777d8195519503bbeb8caa8ca81ddf4c65546540eefa432aa32a0777e8895519503beec3c668ca81df761a3346540efbaed19a32a077dd858cd19503bee42c668ca81df75d63346540efbacb19a32a077dd828cd19503bee414668ca81df75ca3346540efbac519a32a077dd528cd19503bee294668ca81df76063346540efbae319a32a077dd518cd19503bee90c668ca81df7a223346540efbcab19a32a067fda8889195033fed34448ca819ff6962246540cffb4711232a077ed8288919503bf6b14448ca81dfb54a2246540efda6511232a077ed21889195033ff554448ca81cffa222246540edfccd11232a0777e5588919503bef19c448ca81dfb2e22246540efdb0f11232a077ed8688919503bf6bb4448ca81dfb2d62246540efdb0b11232a077ec8588919503bf6bac448ca81dfb5962246540efdb0711232a077ed7388919503bf6b1c448ca81dfb54e2246540efdb0311232a077ed7188919503bf6a8c448ca81dfb4c62246540efdd1111232a077ee5588919503bfac3c228ca81dfd6161146540efe90b08a32a077f57584519503bfac1c228ca81dfd5ce1146540efeaa708a32a077f58284519503bfa414228ca81dfd5ca1146540efeaa508a32a077f45284519503bfa994228ca81dfda221146540efecab08a32a077f62284519503a7eb1ceeb4a81d6f506775a540cbfd553bad2a071fe889dd695033be5d4aab4a81d9f58e555a540ee7a832aad2a0677eaa955695039bf444aab4a81d5f9de555a540e7bd1119ad2a075de778cd69503baf2ac66b4a819fb2ea225a540eddac7112d2a077ad41889695033f755444b4a81cfba22225a540ebdcef112d2a0776e55 else 0xcb2a32a076fd7659519503bbec2aca8ca815ffaed6546540cffb0ed1a32a067fd8668d195033febb3468ca819ff615a346540cff90ad1a32a067fd7568d195033feb2b468ca815ffaed8346540affb70b9a32a075fd875cd19502bff5dae68ca815ff6e16346540affb6eb1a32a076fd8658d19503beec1ac68ca815ffaed6346540affb70a9a32a057fdb754d19502bfedb2a68ca81ddf6155346540efbb06a9a32a077dd7354d19502bff5daa68ca819ff61da246540cffb0cd1232a067fd76689195033fec2b448ca819ff215a246540cffaead1232a067fd65689195033fedd3048ca819ff6a18246540e7fb0ec1232a067fda5609195033fed1b048ca81cff60d8246540cffb44c1232a057febb60919502bfeda9048ca819ff6948246540affb6641232a067fda320919502bfed89048ca815ff6e17246540cffb50b9232a067fda65c9195033fed2ae48ca819ff68d7246540ebfae6b9232a057fdb8589195033fed42c48ca815ff6dd6246540edfaecb1232a067fda558919503b7eb2ac48ca819ff68d6246540edfac6b1232a067fda258919503bf6c12c48ca815ffaed6246540cffb74a9232a057fdb8549195033fed42a48ca815ff6dd5246540ebf96ea9232a057fdb6549195033fed32a48ca81ddf5d55246540cffb46a9232a0777d53549195033fed12a48ca81dfb6095246540efdae4a9232a057febb54919502bfedc0a48ca819ff6a05246540affb6c29232a067fda614919502bfed98a48ca819ff68c5246540affb6229232a057fdb84c919502bfedba648ca815ff6d93246540affb6a99232a077dd734c919503bf6c12648ca815ffaed3246540cffb4ec0a32a067fda5605195033fed1b028ca819ff6898146540e7fb04c0a32a057febb60519502bfedc2e28ca819ff6a17146540ebfb0eb8a32a067fda55c5195033fed1ae28ca819ff6897146540ebfae4b8a32a057febb5c519502bfedc2a28ca819ff6a15146540affb6ea8a32a067fda3545195033fed12a28ca81ddf5495146540efeb02a8a32a077f57154519502bff5daa28ca815ff6e13146540affb6e98a32a057fdb54c519503bee992628ca81dfd6053146540efeaa298a32a057febb4c519502bfedc2428ca819ff6a12146540affb6e90a32a057fdb5485195033fed2a428ca815ff6cd2146540cffb4690a32a077f57148519503bfa98a428ca815ffaed2146540cffb0f55232a067fd85aa9195033fe42d548ca819ff5d6aa46540cffb0555232a067fc82aa9195033feb95548ca819ff54aaa46540cff8a555232a067fda7a21195039fec3d108ca81cff6168846540cffb4744232a073fd83a21195033fed15108ca81cff60a8846540e7fb0344232a067feaaa21195039febb5108ca81cff2d68846540e7faeb44232a073fd65a21195039feb9d108ca)) else (if i<5 then (if i<4 then 0x95039fe28d1094a81cff4c6884a540e7fa4344252a075fca89dd29503afec34ee94a81d7f616774a540ebfacb3ba52a075fd839dd29503afeb1cee94a81d7f54e774a540ebf9433ba52a075fd819dd29503afe40cee94a81d7f586774a540ebfaa33ba52a075fd319dd29503aff444ee94a81dbf61e664a540edf94b33252a076fd8599929503b7ebaccc94a81dbf60e664a540edfae733252a076fd5399929503b7ec14cc94a81dbf54a664a540edfa6533252a076fd8199929503b7eb8ccc94a81dbf546664a540edfa6333252a076fd21999295033fed34aa94a81ddf616554a540eefacb2aa52a0777d5395529503bbea94aa94a81ddf546554a540ef7a832aa52a077f930955295033ff554aa94a81cffa22554a540edfccd2aa52a0777cba95529503bbe5c4aa94a81ddf2a2554a540eefb0f2aa52a0777d8695529503bbebb4aa94a81ddf60e554a540eefae72aa52a0777d6395529503bbec14aa94a81ddf58a554a540eefa652aa52a0777cb195529503bbe50caa94a81ddf606554a540eef9032aa52a0777d7195529503bbeb0caa94a81ddf4c6554a540eefa432aa52a0777e8895529503beec3c6694a81df761a334a540efbaed19a52a077dd858cd29503bee42c6694a81df75d6334a540efbacb19a52a077dd828cd29503beeb146694a81df754a334a540efbb0319a52a077dc818cd29503beeb8c6694a81df7586334a540efbaa319a52a077dc518cd29503bee90c6694a81df7a22334a540efbcab19a52a077ed8688929503bf6c2c4494a81dfb216224a540efdacb11252a077ed8388929503bf6b1c4494a81dfb54e224a540efdb0311252a077ec8188929503bf6b0c4494a81dfb546224a540efd8a311252a077ed3188929503bf74444494a81dfb956224a540cffb5108a52a067fda784529503bdeaa42294a81dfd606114a540efeae308a52a077f55184529503bfa98c2294a81dfd486114a540eff26108a52a067feaa845295039ff4442294a81d7f9de114a540eefcab08a52a077de3384529503bf71142294a81dfd2ea114a540efe97108a52a077f4a884529503bfac3c2294a81dfd61a114a540efeaed08a52a077f4b584529503bfa52c2294a81dfd616114a540efe90b08a52a077f57584529503bfab2c2294a81dfd60e114a540efeae708a52a077f56384529503bfaa9c2294a81dfd60a114a540efeac508a52a077f55284529503bfa9942294a81dfda22114a540efecab08a52a067fda861d19502bff5db0e8ca819ff69d8646540affb70bb232a067fda85d919503afec3aec8ca819ff5d9a546540cffb74c2a32a067fda8615195039fec3b0a8ca815ffaed8546540affb6642a32a057fdb221519502bfed890a8ca815ff6e17546540cffb50baa32a075fd875d5195033fed42ca8ca815ff6dd6546540edfb else 0xf551624a540edfac6b1252a077ed8258929502bff5dac494a815ff6e1524a540affb6ca9252a067fda654929503bdeaa2a494a81ddf54d524a540efdb04a9252a077ed6254929502bff5daa494a815ff6e1324a540affb6c99252a057fdb54c929503bf6c126494a81dfb549324a540affb7050a52a057fdb728529502bfeda94294a819ff6e9814a540cffb50c0a52a067fda760529503b7e5b30294a81cff619814a540ef7aa8c0a52a073fd8260529503bfa50b0294a815ffaed814a540affb6e40a52a067fda720529502bfeda90294a81def550814a540affb6640a52a057fdb220529502bfedc2e294a819ff6a1714a540ebfb0eb8a52a075fd765c529503bdeaa2e294a815ffaed714a540affb70b0a52a067fda858529502bfedbac294a819ff69d614a540ef7aa8b0a52a076fd6258529503bfac0ac294a819ff6e9514a540affb70a8a52a067fda854529502bfedb2a294a81ddf595514a540ef7b68a8a52a077bd5454529503bbea92a294a81dfd605514a540efeae2a8a52a057febb54529502bfedc0a294a819ff6a0514a540affb6628a52a057fdb214529503bdec3a8294a81def619414a540ef7aeca0a52a077bd8550529503bde42a8294a81def5d5414a540ef7acaa0a52a077bd8250529503bdeb128294a81def549414a540ef7b02a0a52a077bd7150529503bdea8a8294a815ff6e1314a540affb6e98a52a057fdb64c529502bfedaa6294a81df758d314a540efba6498a52a077f5814c529502bff5da6294a815ff6e1214a540cffb5090a52a057fdb548529503bdeaa24294a815ff6cd214a540efdac490a52a077ed3248529503bdea0a4294a81dfd4c5214a540affd7690a52a077f9874c129503bfcc326094a81dfe5d9304a540eff30a98252a077f8854c129503bfcbaa6094a81dfe595304a540eff30498252a077f9624c129503bfca926094a81dfe605304a540eff10298252a077f9714c129503bfcb0a6094a81dfe545304a540eff0a298252a077f9214c1295033fec3d5494a819ff61aaa4a540cffaed55252a067fd85aa9295033fe42d5494a819ff5d6aa4a540cffacb55252a067fd82aa9295033feb155494a819ff54aaa4a540cffb0355252a067fc81aa9295033feb8d5494a819ff586aa4a540cffaa355252a067fc51aa9295033fe90d5494a819ff69e884a540e7fb0f44252a073fd85a2129503bdeaa51094a81cff60e884a540e7fb0544252a073fd81a2129503bdea0d1094a81dfe4c2884a540cffd5544252a073fcbaa21295039febb51094a81cff2d6884a540e7f94b44252a073fd75a21295039feb2d1094a81cff5ce884a540e7fac744252a073fd53a21295039feb151094a81cff54a884a540e7fa6544252a073fcb1a21295039fe50d1094a81cff5c6884a540e7fac344252a073fd51a212) else (if i<6 then 0xad2a077dd728cd69503beea9466b4a81df714a335a540efbae319ad2a077dd518cd69503bee90c66b4a81df7956335a540edfac7112d2a077ed8288969503bf6a9444b4a81dfb4ca225a540ef7a83112d2a077ed21889695033ff55444b4a81cffa22225a540eefcab112d2a077de3388969503bf6c3c44b4a81dfb2d6225a540efdb0b112d2a077ed7588969503bf6c1c44b4a81dfb5ce225a540efdaa7112d2a077ed7188969503bf6a8c44b4a81dfb4c6225a540efdcab112d2a077f57584569503bfab9c22b4a81dfd54e115a540efeae508ad2a077f55284569503bfa29422b4a81dfd4ca115a540efecab08ad2a077f622845695033fedd3029ca819ff69d814e540edf96cc0a72a057febb60539502bfedb9029ca819ff69c814e540affb6440a72a057fdb85c539503afec3ae29ca81d7f5d9714e540affd76b8a72a057fdb858539502bfedbac29ca819ff69d614e540edfac4b0a72a077f581585395033fedd2a29ca81dfd605514e540efeae2a8a72a057febb54539502bfed90a29ca819ff6e9214e540affb6a90a72a077f57148539502bff5da429ca815ff6d4214e540cffaed55272a067fd81aa9395033fe40d549ca819ff5c6aa4e540cffac355272a067fd51aa9395033fe28d549ca819ff486aa4e540cff84355272a076fd7299939503b7ea94cc9ca81dbf14a664e540edfb0333272a076fd7199939503b7ea8ccc9ca81dbf486664e540cffb4f08a72a077f58184539503bfab8c229ca81dfd546114e540efea4308a72a067feaa84539503aff3bc229ca81dfd2e2114e540efeb0f08a72a077f58684539503bfabb4229ca81dfd2d6114e540efeb0b08a72a077f48584539503bfabac229ca81dfd596114e540efe96508a72a077f58284539503bfa414229ca81dfd5ca114e540efeac508a72a077f55284539503bfa294229ca81dfda22114e540efecab08a72a077f62284539502bfedb95094a815ff6d4a84a540affb6254252a057febb61d295033fed3b0c94a815ff6e1764a540cffb50bb252a075fd875d929502bfedc14a94a815ff6d8a54a540affb6252a52a067fdba615295039fec3b0a94a815ffaed854a540affb6642a52a057fdb221529502bfed890a94a81d7f61d754a540cffb4cbaa52a057fdb759529503b7ec32ca94a81dbf5d9654a540eefb0ab2a52a057febb59529503bdec3aa894a81def619544a540ef7aecaa252a077bd8555129503bdeb2aa894a815ffaed834a540affb70b9a52a075fd875cd29502bfedbac694a81dbf619634a540efbb06b1a52a057febb58d29502bfedc2a694a815ff6dd534a540affb6ca9a52a0777d8554d29503beec1aa694a81df75cd534a540affd76a9a52a077bd54609295039fec1b0494a815ffaed824a540affb70b1252a067fda858929503b7eb2ac494a81de else 0x61b49b31b21b11b01af1ae1ac9ab1a99a81a71a61a51a49a41a31a19a099f99e99d99c99b99a99999899799699519419319299199098f18d98a98898618398218117f97e97d97b17997897717597417297197096f96e16c96b96a16916816716616516496396316196095f95e95d95c95b95a95995895795695515415315215115014e94d14b94994894714594414213f93d93b13893793613413293092d92a92812712612512412111e11b11811691591311191010f10c9099079051028ff0fb8f88f60f30f00ec8e90e58e28de8da8d70d38cf8cd0ca8c90c80c70c60c40c18c00be8bd8bc0b90b68b50b40b30b20b00ad0aa0a68a58a40a20a10a009e09b89909609489289108f08c88a08888708608388107e87c07987887687487307207106f06d06a06886606406105e85c05985705485204e84d04c04a84904804704584404284104003d83b03903703503383283183082f02d82c82b82902782682502382282101f81e81d01b81a81981881601401301100f80e00c00a00800680580480380280180057febb61d695039fec3b0ab4a815ffaed855a540ebfb0ebaad2a057fdb85cd69503afec3ae6b4a815ffaed735a540edfaeab1ad2a057fdb854d69503bbec2aa6b4a81df760d535a540efbae6a9ad2a057febb54d695039fec3b04b4a81cff60d825a540affd76c12d2a075fd735c969503b7eb1ae4b4a819ff6e9525a540affb70a92d2a075fcb754969503bbebaaa4b4a81dbf58d525a540eefaa6a92d2a077ed8254969503bf6b92a4b4a815ffaed525a540affb70292d2a057fdb314969503b7eb18a4b4a815ff6c4525a540affb70992d2a057fdb54c969503beeb9a64b4a81dfb609325a540affd76992d2a075fd725c569502bff5dae2b4a81ddf549515a540efeae2a8ad2a057febb54569503bdebaa82b4a81def5c9415a540ef7aa4a0ad2a077bc5250569502bfedba62b4a815ff6d5315a540efba6498ad2a057febb4c569502bfedaa42b4a815ff6cd215a540efeae290ad2a077f53148569502bff5da42b4a819ff5d6aa5a540cffae5552d2a067fd52aa9695033fe29554b4a81cff5d6885a540e7fae7442d2a073fd53a21695039feb9510b4a81cff54a885a540e7f8a5442d2a073fd32a2169503afec2ceeb4a81d7f60e775a540ebfaa73bad2a075fd829dd69503afea94eeb4a81d7f4ca775a540ebfaa33bad2a075fd319dd69503afe90ceeb4a81ddf616555a540edfac72aad2a0777d5395569503bbea94aab4a81ddf546555a540ef7a832aad2a067feaa955695039ff444aab4a81ddf61e555a540eefb072aad2a0777d7395569503bbe594aab4a81ddf60a555a540eefae52aad2a0777d3295569503bbeb8caab4a81ddf4c6555a540eefa432aad2a077dd878cd69503beec2c66b4a81df75d6335a540efbb0519))) else (if i<10 then (if i<8 then 0x69068ee8de8ce8be8a689687e86e85e83e82e81e80e7fe7ee7de7c67ae79e78e77e76673e72e7167066de6ce6ae69667e6666566466366266166065f65e65d65be5ae59e58e57e56e55653e52e51e50e4f64d648e44641e3fe3d638e36634630e2d629e28625e23e2261de1c618e15e14e0f60ce09e07605e03600dff5fddfbdf95f7df5df4df2df15efdee5ecdeb5e95e7de65e4de35e0ddfddeddd5dc5dadd9dd85d6dd5dd45d35d1dd0dcfdce5cc5cb5ca5c95c85c65c35c15bd5bbdb95b6db55b2db0daedac5aa5a7da4da35a159f59d59a596d94d91d8ed8cd8b589587d85d82d80d7f57d57ad7757457056e569566d63561d5e55bd59d57555552d4fd4cd4ad49547545542d3fd3e53b539d37d35d33d3152e52c52a527d26524522d1fd1dd1b519d17515513d10d0ed0cd09d075055035004fd4fb4f9cf7cf5cf34f0ceeced4eb4e9ce84e64e2cdf4dd4dbcda4d84d6cd44d24d04cd4ca4c84c6cc44c24c0cbecbc4ba4b84b64b4cb1caf4adcabca94a74a54a2ca0c9ec9dc9bc98c96493c9249048ec8d48bc89c87485c84482c8147f47e47cc7ac78c76c7347146fc6e46bc68c67464c6045e459c57c55c51c4fc4dc4b448c4644444244043d43b438c37435c3343243142fc2dc2b427c27425c24c24423421c20c1fc1ec1e41cc1c41b41ac19418417416415c14c14412c1140fc0ec0dc0cc0c40a408c07c06405c04c03402c014003ff3fe3fd3fcbfb3fabf93f83f6bf5bf53f33f1bf03ef3ee3ecbe9be73e4be3be2be23e0be03df3ddbdcbdbbdabd9bd8bd83d7bd6bd63d43d33d23d13d0bcfbcebcdbccbcbbcabc9bc8bc7bc6bc63c4bc33c23c13c03bfbbebbdbbcbbb3b9bb83b6bb53b43b33b1bafbaebadbac3ab3aa3a8ba7ba4ba2ba039eb9db9c39b39a397b95b94b93b92b9139038fb8e38db8c38ab89b88b88386b85384382b81b80b7fb7eb7db7d37bb7b37a379376b7136f36c36ab68b66b64b61b5fb5d35ab56354b50b4e34bb49b47345343b41b3fb3db3bb3a337b35b3333132e32ab28325b23b2131fb1e31c318b15b12b1030db0c309306b04302b002fdafb2f92f7af5af32f02ed2eb2e92e32e02ddadb2d92d7ad32d0acf2cc2ca2c82c4ac2ac0abf2bd2bb2b8ab72b52b2ab0aaf2a9aa62a2a9f29ba99a97a94291a8f28b28928428127f27d27b278276274a71a6ea6ca69267265262a6025da5b258a57a56254251a4f24da4ba49a48a46a45243241a3fa3da3ca3b239a38236233a31a30a2f22da2ba29a27225222a2021ea1ca1b219a17a15213a11a1020ea0ca0b209206a04a032019ff1fe1fc1fa9f99f71f61f51f41f29f19f09ef9ee1ec9eb9e99e89e79e71e61e59e49e39e21e09df9de9dd9dc1db1d99d89d79d71d69d61d49d39d29d19d09cf9ce9cd9cc9cb1ca1c91c69c51c39c09bf9bd1bb9ba9b81b71b else (if i<9 then 0xa960d444022e17e5bea961dc44210c34c5ec34c5ec5ec34c34c5e84004f822866076034e5be1d85f82004b834e5b82105f82004b834e5be1d85f81e04b83485ea10a22a1ba10e1b45ea22e179d4a039aca1ba6a210a22a1ba10e1de1b25dc58e17e1de1b617c5ec2fb4961b60827c834e1b45ea1ec58e17e1b45ea22858e1782060d60581ae0e1ea05360d68860582060e1ea0536886059660201ea05360d6059ea03205302160d60e01a1ea053688605f1b0061ea05300e00380305b03586801984060d01d1db8a2868834a0e00204f03887a81982100386280e02803181986882380d07903904f87101087904f81a01103907105a01083d81d03881a00e05b01985b81d05681a00e07b8198397a900087c82800e05a01980381a1ea05b019a0d24021ee179ea22ca22a10a1da10a05a10a0d210a0385de17a10cc220581ea10a5ecc21cca10cc2205a1084ba10a034c2210cc261de17a6f25ed491ea20d24c80721085ea22a10a1da109aca10a0d210829203e17a109ea617e0d605a79d3361de17e0d45eac253306b00306883581d1cc8199cca10a6f25e85323da05a10a5ea05a10b1b210a0301ee17a10c1ee0d25e87ce17e5bac260d62c85341ee17e0d605c79b33605a7cc10e05ac227cc10e4ca5ec10f17605a7cc10a1da0d22ccc2210a1da05cc2210a5ecc221da10cc2205a1084ba10e0d25ecc227ce17e0d4c220727ce17e0d605cc227ce17e5be1de2ccc22108038470281ac8199aca10a0d203a79834f1720d27ca10a6a222a10a1da10b1b210a03807617a10e0d40727ce17ac2617e0d27cc5eb4960d27c834a1ee0d40727ce17f1766a64ca10e2961de0d45eac261786361860e1ea05306361860e1ea0530636180241ea05306361860e1ea05360871b0089ea05306321860e1ea053068e0d0af9880de8158532509ea210a03a34a29210a22a29250a1087ca10a0e234a29022a10a5da34a10a6a022a109c2272210a0e234a5de17c22a6f5491ea4ac803250a10a5bcaca10a22a5ba424aca10a5bcaca50a10caca79a10a5bc34a3dc349cca34a08254a10a5ba58a10a7b210a0e234a5de0d42287ce17e6a24785341ea34e0827cc10e6a222c10c0e234e0827cc109c227ca109c2234a1da54a10a5da34a10a7b210a7ca10a0e234a5de0d40a27ce17e0d617a7c9c240a234e0d40a27ce17e6a64ca10a50caca10a5ba0e034a22a5ba424aca10a084aca7ca10caca7ca10a5bc34a3dc34a1ec34a0e434a0a434fbdfa901072c729f28725723f20f1e71b719f17f16714f12f0ff0e70c709f07705f047006fcefaef8ef5ef36f1eed6eb6e96e76e56e36df6dcedb6d86d6ed4ed3ed1ecfece6ccecaec8ec56c36c16be6bbeb9eb7eb5eb3eb26b0eaeeac6ab6aa6a96a86a6ea56a46a36a26a16a069ee9de9ce9ae99e98e97696694e93e92 else 0x89c206900082fa0505b02f80301885800201da5e84881308700206881d04880800206885818801d05808703e85a8390634108180870020008728488181ccc0e065000e6a0de9bd834852c108089880730488dee4c870c0e00206703481d048da958d06121e835da919d85ba0e0585a959da0e0668585a959d866a0e0584180580dec1805819d80e434835a2920d5bd84f8581dbb9dd88003c34dbd85405825bdbd84f858266a0e0c405841805800241804a05800e43485802003720e058617854035802066820058020066a0e05841805819d81805819d81805802141805819d8024348581880020674180581db80241805841803598d01805818d61782f00201241805819d80e4348582290020228158580020c44180359db9bd80e41805825b80200801585861781d05800200801d058188018058188018058017c0801d05839db883bdc0e4348024348693ccc0e41803c0024348523ccc0e4348673c2434816802434848bdbbbdc0e4348673c200243481685bc85a10873218402202218402202485a0204e87987121820e20207b0d8869218402202202234d9ddc221820e065202234a02226a02253229202234a1820e202171a1820e208188202218402202202234bbda18402202226a0221320e3bda18617b1b208617a02234a18402202229202234a1820e26f20e21820e218402202202234a1840220221320e2022349ccb1b1c221840225ba02434a02434a02434a1820e21820e21820e202434a02434bbda02434a02434a1320e22902200ba0505b218402202229202234d88208202068dcc83c21820e5dba020af8720522182021cc818617ddbdc220e21803c418426c18426a18717202218402202202234a02234a1820e21820e26f20e208188202218402202208402202218402202202234a1320e202234bbdb1b208617a1840225ba1840e21840e21840e21840e21840e21840e23740e21840e20840e21840e21840e3bda1840e20840e202234bbda18617a08617a5ba1840e21da1840e1dba1da0203902f848d9da5da34848ddba0203906d04880806701d20e0582184022022020afa182021c201320e0181885dbdcca02234816c182024084180afc1820240841840820e218188202218402202202234a02234a02226a18402202188226a02202253229202234a1820e21820e26f20e21820e202234bbda18617b1b21840225ba18226a0241820241820241820241801820e01820e01820e20241820208b2024183bda0241808b20221320e20241820241801808b20d210a5ea5eaaca10a5da0e234e0d617c22a5e9cca34a0d210a5ea5eaaca10a5da0e234e0d642617a5ee5bea960d24405361de4225ec10e5bea9605a22c10e5bea9605e424109c2234a0d210a5ea5ea34aaca10a5da0e234e1dc47e17a5eea960d605a79e179c265be)) else (if i<12 then (if i<11 then 0x2182022023a940220225ea182022400a2a02234a0e205e17c0225ba73c0e26a40e254c0e266c0e21dc0e24cc0e23740e25be17ba93bda1de17ba925ec0e205c0e24040e22cc0e40e205c0e205e17a5bc0e21db1740e019c02202019c02202019c88202019c02202019a0e26f20e019a0d20e3a940220225e88b2022020af819c0220208b20201520e019c0225b8198a29dbd1701104120e03c5db85e21083a00ca025ea05301685e2021aca020c402140220201120e019985ddba0e20d04b83c019a0201a016d17418517418517418517405a0e01988b185a5b985a02202402202273a6a4022022020d8a26a02202266c02202185a26a0220225323740220226120e24520e031a0e20d20e25be17ba93bda1de17b1b40225bb17226d8800205881805b074c5d88700200081e03487603a816d4906a02a21087307b99d8180138038650588de85b07b8039d4865054c0e07b858229208067059a2958800202281805b60807a03105301860807c8d886960800200097185205f80200080161860e0631ea05300e21805808700080a07a034831015853229000850a0505b0dee0807a03a85300203703786501800281380386505d41e9ea0652181cc86501e802da906500303701883c000c0507c87900207c83487107cc0e058066802000c5886901d80204f87104c80200086e05240840e07c83c63d81800202e8d886919d81860808702e07dc10b9d8de9c207dc1080206707283484881800206f86519d81818840e06521840e0655a906f86500303181887063d81808700200082e86901808700200086d8521dba290181c240e0650dee2918d6420690dee3d99d82e86919d86d8521db81800206d8af85200083907c9c241080200102a07c87007cc0505a00200100087c8690010008023ea05200200083f07c85200140e07c83c06f21805b00202f81805b05d80887603a9c223d85d02005786d21085f21d808a05076071008e4c870a0e59da0506685a05fc5dc0a0870010009db84d05f03485b0168180020089ea1c2069002802000dea04880206881d17184880800206885818801d05825d8870009c201e07600e05b03480405881e857848a5da34848a5b84200203f85784884201e87905800898807284886d81840a00200105186500202f82e06501800205786518805786500286d20e05841840a18806502fa1d80207105841820e0650020360af85a06d80a0015a906500300201885823d86485a25d8870028010008001bd87300e05b034dbda2901f0de857850a108008de87d00e03483005365be0e61802205783005301840a0028011bd80e0655bda5da0e2348088730590535dba5bdbda34857850a10824008e6a052a10ddbdbda0506685a0dea5d9dbe1785d19d87305b04287d0300530028020008000de9cc84583487301688700206d00 else 0x6105a217c0e04b84b1bd9ac828019c108198a285a08a40e01983c06f01a05b5a920d4c220504003d5a906ca22a1083780405e059035a031ac835dbda1dda90a2a10c0581981a05a5a920e03581988a18580405e03584000381a85380385ba1083a08a04f00680206883c0a280c83900201681100206905a00b98581d05a1a901980400e03582804020d00400205385a0404071db82818585a02821da0e04f82800380201a05381980400205183580203182c05a03c01980205a02806ca1083a0a2a1da0e03c01981a05a02c1ac835a3de8820e07c41e8198040029d480e03582120d01f00684fa0e03c0198020390359858390358210200358211cca0e03c01981a04b05d01f41e99d8358a299d84f83580201981a03c0198020069cc9ac86920d0040010025ac85200201106905a18582804b00ac058392c24108068021ac870405c0505a00a806c05869006c0583900205200ac05841052006c05c0e03c40583940504b1ac82f04b3dbbbdc0583940504b05e3ccc0e1ac835c0e0c40358020210200359a90199ccc0e035802019847028019c0e0320359db9bd819c0e0358319ac80e03581980e01a04b40e035819c0e01a05a1a919dc0581a61785a21d80201500b85a1db9bd81a61785a00c8a281681520e01d05a0359ac85a20e0150470068d881681501a21085a01780b81a08b05a40d40e07940d07107040d41085a00dc0d06940d07940e03c04b85380dd1b03c40d065c1084b40e40d03504b40e07004b84b3a939d81a40d28805a410c0d04740e03c40d05a053c0d05a03c40d04f811c0e03c068840c0d202037816c0d045816bbdbac803c0e02806b01ac17c0380300200103587000300205582801a019c17c03c0300200102806901983940e02800380204d028038417c0380300102840e03c00203781984b00200303584b3bd80202801984b3a9019bccc0e03581984f80203601680380204082800300202d03581982040e0358673ac81980202801681981800b835d85a05dea20a069402202073866c0220221da025d480b86906120e019e17a021ea05e205a020d886920e20d06585a0695bda17a0380200bdea069202254c02202226a0220220225323740220224520e06f20e06820e3a93bda1de17b1b202218202240402202202234c0220221820220e205e17a0226a402202266c0220223740220226120e26f20e20d20e2023a940220225e9bda1820220223484f40220220e40225ba73a021d4a02266c0220220225326120e24520e20d20e1ea3bda1de17b1b05ea021aca020d8838c02202031a0e1acc8802121087a866c02202037402202023a0e0199cc8214022025db818205a020af8525dba0e20d04b83c5dbdac819a0e028517426d1742699da5bf172022022738a2a6a4022022548a2a6120e24520e26f20e25be17ba931b) else (if i<13 then 0x3c0e233c0e233c0e233c0e233c0e3bda22c0e20820340e240207233a0720b207233a1dc0e033a0d203453064233a5d8222021c201320e033d9da5e8d881680b2075cca5da33816c33c0825dc33a02408433c0820e233a5da02226a33a5da02253233a5da33a0e233a0e2020d8a33a0720e015207233a26a33c07233c07233c07233c073bda22c07208202407213407434c07434c072290288585a906ca10a22fbd837e1de1b85e02e84287183498580200081b87403b03807701687604000a07185380385ba1083a07600b00201d0711a900400081e01b87583501083a18584f87607583a39d857073034e5b9db803802434c4b85399d80206e81b84e043034e5b99d85701b85f82283486ca1083a65b80904103a034e1b06085a834a5b82005805d01f41ee1b6179db82e02007a99d87304fe5b9db81b8026420c783c01d00b0021ac9cc81681d0561bdc0700200180100081b87485387003a000e1787703a04b81b80207403781d016e5b80202104b83c3d4c1bc10b9dbc23a941bc1084083900241b81680241b85380241b83c00204fc1b83c067040bacc1b81680241b81681b80207603c20224bbbda1bc022021a9226a0221bc0220221bc0220221bc0220220b4022025db85e21083a21ba021aca1bc0220221bc0220200b402202074037a0221b816c1bc1820226621bc02202202271a1bc02202202226a1bc02202185a26a0220225321bc0220220224ba1bc0220220224ba0224ba1bc022023bda1bc02202226a0221ba6621ba26a1ba4b9acbbdc0e02801a08a0021ea01986901d019c0e035c5d81a0040038020795bd82806ca22870019804011803028054a0d20505a85a02c1d482801a00201a81986901ac0e01983c01d019c0e035a3da0d20586705985d8043bd828019e0587c8d886901a6058020011718521db8a285a02100201a03c25d81f1cc82804f03f21087a9db85a81981180302805d0a2c1ee1783a8501ea05a8031d482803581ee1786785b1ea1dbe0d00307c8c783c3ac9ccc0e0280a2c1d87041dbd4c0e0280669cc8690371ccc0e03c63d81980262c8d88690199acc0e02804bc0e02801980205a02800dc0d00e0500700610358301a940307a87061d99d803171c1085a63d81a01988a00200162c8690198020518283a901a019c0d6059db88a04107dc10e3d80de2cd1b06906163d8a299d80e62c86904b80e0281db819c0e62c8680af8525bda1ddac8a2a10e1d86120e05a61d88845be1785a61d91f9ea04b20d06703720505a3db820035837062cc25dbda921d84f8a2a10e1d86f20e05a61d9ea05a0030358af85a1bd866e1785a1db9bd80507204b5bda05d0481da5d84b1cca0e028629019a1086804b84b19d87204b3a941782684b0280178a285a266826c1085a61d86741086f04b1dbc0d266849c1085a61dc0e0 else 0x60d00380e45307705302607a833e0818800206907a85301487a877833c5314bc10a5ed881cc878410a5ee5b99d85d820834848c0d41087a833e4225e86964225e86964225e86965b99d823052033e0585f85d8af85218802507705de4c80e06403380264c85306465b835988020848a0d21087704406c04b0731bd83380041300e45325ee5be0e63382265e81185303587304705320d5bda10a5ee5b835824605852a10860617e0d07d25e87d0118531db83405d03384d63304702281683380205306401300305206400314ba1086400b002034064033e4cc1086465b9bd834605833875852c10e5b835988023048e4c80e064033e1d99d8020488644ac83587700384003407745e835c3399d87a83583380203407ac05c5e85245ecac848c05bbdc5ec108020d8c5e816bbd83399d988405c5e8359bd833c5e83580e405c5e835833c0e405c0703406403398d1bdc5e83581500203406400b18803407700b188007035833802034064433c5e85245dc34848bbdc5dc0e43483380300207a016a02253233a0e233a0e233c5dbbda22c5da0820245da1320e233a5da33a5da33a0e233a5d822c0220221320e233a07233a0e205a0720b207233a5ddc231b067823a0e0222021cc821207060aac852076a0e23383c25dc33c26a33a5da33a5da33a0e208188202233a5da33c0220221320e240207233a0e205a0720b20723))))
def uL34 : PT := (1023,4,8,12,uL34F)
def uH0_34F (i : Nat) : Nat := (if i<1 then 0x58208202b0df8038155090045020e0a6787c2a42042ab77c85202f204a08eb4341b612501980141fa0c202480c8260118018051c5420fc07a0185f0e06a0a983e055c0810363ca8a0e04b062004005618d00735dc6f36c10c105b06cb6d10a1804826c02f7c301e812c15265205581640c100a800c2060f102083a80b6cad75d84380a4d0c08f00800e00587c581442c814a03f80c432a299b1501706be0e601e8c102e807c0b50539af60ec00d020de5019209a069027471309383441140c064d04ec04a12e00e85e82736deb4d862461c0d907d838431c10f06c008c28a17d00dc26832612d07380fc246c990b800a833a11b04e361c11c30c0bc059c2c6050034329417f483035b3fc2c011509918600ec0950bfbaa49462fb0648032e3229b0519b040720f70ac04bc2a031807b014c09e37803900d070e0bd9734951ef216b0a1052c12e1720c583cc2ee09b1adb49815207401c0c9821615f0458468194044050030c27c1a06940600310ca308883502b808d09404282021686bf02cc2c2078357011c0b457d97a06280c415703284f416c05904a018c13c0d60a303e59f200a44dc2c400c2fab0d8c35efca880bdb288212002022b5f026218f08984981d16d400205d426e10807a82c40e6d2b070009de560f205dd87c1da1a606285686520cd18906300480160d403a4336151091024028819a0ca04401be13c0c18085ef41241be342462c12b01b03c033c14d065845ac6e05705b833830801309083bc3220c60b104b00a807118802a822f6490a792682bc04606b9b5027e11c0be029c00004c02f807c000043000033006e0e30d282a032014901f0061af00e40bb03747201960ce06141220d591dcb5095438e0b981545356c5037061c1001a702101a46c889e08306640fc07b04d00440cc16e080055029802905cb4382b6067057860401a1410170064d372cc06f04305fe0090cb8d6403040071002501c10028000081d00000000080000000005018080040304c030300000c0608801000ad0208244c000043b00c0001400408f5070010084404451000b00e00005c0b0001c0e400230560143b0500000404074000700405c1311800018020006f00412010000002b00002010480580001400000020040100020000020240000c000140d00c07030000005d00c0601c00000040001d0240102c000b817000050001c01814044000001e00807018060000000000008100480000000030010002b00000008000040403411000000480202000004161d80c0282b03c100085d10403054120001502c00018081c00c14c2d014031c0050040400c100100d000070b000074050080400c00000080040f05800220020c41900c000100000400074010040039844098000000f00803000002080000804008240300800c0000c02014000080000801 else 0x91885c42ccd2904600000000770b7802da0c0b001e03401c413805a805c26a16503e8a9411011908f84cc09a15d04fb2c65ca19fa44244e4a608915182ac1ca0ee05212a019e10d064027420a08f03c8565a300eb01d83e9a4e02206981d410c02601a83480500ff07f02d03461868c4003c224d2a03783699421a102403702d2d0f0d104102fc12a00f0191ef80bc00a01b410e140193b26c5441980200c2025206005605b6)
def uH0_34 (h : Nat) : Option (Nat × Nat) := lw0 263 530 10 13 9 4 uH0_34F h
def uH1_34F (i : Nat) : Nat := (if i<1 then 0x7d81a260f40c8021c0bb00a0090040c0af03ec0a90341885076c00a106812f00bc1ff03105c505e803103d811815701ca03f816d02a809800d406e0124163018419705840a403b809a00581e0011011e0319dce052c4a8172c08b035c46b080c1d5033800104fc17201a19dc06041a7010c13b10b00b40150092052841105dc04c0334168084816a135000306700d101f803f06a405c01cc1f105f01e505bc15a00301b003fc1ce61a815200f803801c408f03901f96729dc260b0148077c0670235dd506240dc676c1c1073008807bc1ad05d415904d420b1365c6e02f007203b412e01e808303040ae0308060025c5e105e004e0048136773004b04b4185031419d08340e5083c416022805e07b402706a015306ec0df62b05bd04d00fc00ec5e2001405904f412877345c0076846607cc143073c0530501dc9074016e040417003c00866778401007819f670c03a620402c0118120035418800500f501d448206380320828055071814e0420173133c1ee02d812705981dc03745e002e85dd066c1a50068015034c11711b80470120441064c15062ac09c06481b107a41c406d01fd01b001d059447f078c04203a040002a00a202c010b00080f3014041b605417172ac20700b80d610e400f05599c560199df01f402905d819607200b806cc1ba053407c061003d044010a016811607b05c806440fa005c14f046c03702cd9d512702006194202079d8a801c01bf04e450d0409dc002f412a07ec19503641cd770dc8108240a105e401000841a601880ab04c802d04cc182029c024043589c05f81e8031c131050818c02b4158105c19a06d45b904e00de01041e101fc18307e816c064002202d442e12b016200d806472a81fe02f8174079812303bc1a106bdc000744113061c1d661b814c0524121036808c00600f760e00c9001c15e0044056072406506001c212e0074629c00d050415f06359ba017c1aa00ac205061801903600cc05a40e304719e002940ea10d011f014811104e820c074846a02c41d900d043b019817f0571c3d02fc1190009107c0000823000690040000c00004003540803800000000ec030002517cea058110a4020040e0080303c010080000015030051d4010381d0cc00060100702b0400446c5009c0c0bc090002f0580a244016940100c192500b000130340009850000530200003040000000704d0040000c6e0000b2401709c100440c02c0200014140080001409c140000a00c47018020d4140000908c1c0001a0ec1a38c75118a81009a0dcf1000ba069de000ca0301004002008130f0000e00916405000010546c02c070840b00004258270002b2a0130000001c1239c410957e308200dc000284801c46070b52200001826078110c80000002000000b4000743600007188150007426c01014870002700000 else 0x129c5d502781d4077805b026c1091339c8506e04080094211056c00016fc051020402a074c164033c06901dc1ab024408007ac079068007604141f801bd9c002c801b00700f1065003c071404507d40e2000000005441dd004c10604f80a60258210067813c08200a0080418f007c0f804981a3048819903d01b7018c1b90411c7d04dc5e4046806a01e1de1101c20e06d8471027c0f9062807b0690057051011402541f407f0040034980003a417b0660124606416b02b010002e41ac00240db11940ec06c843507dc02306f00fd013408e13719d902080e6043c160081009303adde0062c0ca05f400602dc155002c5ca021012961f409d00e400e01ac146041d9b906f81d760cc2060438487078815d03c80d404741c062a41ae0250085059c154070c02007c05c307a841c045449e0430130030014700cc47d026408907600a3051412b678404f04b1c1966f00cb009804a00c1ca9030c1e40020410039c000000006d072c1bd604083a173c5da0010058055c112084c0e004940e107c805d62a8000071c)
def uH1_34 (h : Nat) : Option (Nat × Nat) := lw0 216 654 10 14 10 4 uH1_34F h
def uL37F (i : Nat) : Nat := (if i<1 then 0x7611ac821035d4ac202100e01a17f52b080861dc1a17b072c23d485f2de0d40b85fd4853184842a4a1dc1a7a90bc34d8484299a5b83d83502ec275285f084534b787702fa95840432de1dc1a8160cfa941c3090be1dc1a17b0bec24210d214a178457a9deeac82116f56410845ef62ec0e06916f0bc08399ab20845b845ef756410c2f19ae12ac821ef6070348bb87706a0877b85ef5210c69835351c242f14d085494697a9dee0e06983535022c2f84229a34cb7877043bdd5904306a6a04585f085c2469ef707034c0a802fe5f8be97bef51e53bf764ea9d0b98724e25c13776d4d85a9b4c67ccd593b1f626c317faf95dab956dad6594b095c2ab544a71492884fa9cd33a614b893d23a3b46889910216414800fa1e73b875ce81c537e6e0d71a4334644c397c2ea5b0b21592a2520a09392624a89111721a4087f8fb1ec3c8760e21b2344638c317e2ec588a81422744c09311e22c4287e0ea1b43205e0aa1382384307e0e41a02f05808c0d81702002801800dff61d695037fd855a540dff5d5695037fd835a540dff5cd695037fd535a540dff609695037fd725a540dff549695037fc525a540dff4c9695037fd715a540dff545695037fd315a540dff485695037fe555a540dff889695037fd764e540dff605395037fc814e540dff5c5395037fd614e540dff545395037fc514e540dff485395037fc214e540dff845395037fca84a540dff61d295037fd864a540dff5d9295037fca54a540dff615295037fc854a540dff5d5295037fd654a540dff60d295037fd734a540dff58d295037fd534a540dff609295037fd624a540dff549295037fd324a540dff285295037fd814a540dff205295037fd714a540dff585295037fd514a540dff145295037fd314a540dff485295037fe884a540dff955295037fe114a540dff61d195037fd8646540dff5d9195037fd8546540dff215195037fd7546540dff595195037fd8346540dff5cd195037fd6346540dff54d195037fd8246540dff209195037fd7246540dff589195037fd5246540dff149195037fd3246540dff605195037fd7146540dff545195037fd3146540dff485195037fe8846540dff955195037fe22465409ff69d695036fd635a540def505695027feaa5a540cffa21695035fe775a540ddf955695037de335a540dfb889695037f6115a5409ff699395027feaa4e540dbf999395037f6114e5409ff6a1295027fda74a5409ff699295037bd544a540def505295037f9304a5409ffaa9295033fe884a540d7f9dd295036fe664a540ddf955295037de334a540dfb889295037f6114a5409ff6a1195027fda7465409ff699195027fda5465409ff68d195027fda2465409ffaa9195033fe8846540d7f9dd195036fe6646540ddf955195037de3346540dfb889195037f61146540 else (if i<2 then 0x8cf8da5e8a696e1ac33d52876ced8d02a9770bc64469708011ccb5986c38c4bc2f842ea5a943b6770418800417b0ddea77b85f0121b0698772104f8041983b034bb7100cee1b80417a0dc1ec2f708dec34c3614f0ee1bc10009dee1b0721c61a5db84206ec405e89f08a0121bb5985e29a1b07896f0406700486c0adcc86976ecec5e84502c0121bc3685e25c3482d96f0ec5f80408025c34cb776f0ed9dc10621013bd8370750d84f8690740d02801c7a80cd9d833834c2c738bd07b0bdea4213081421dc1a008d66c242f842f505a41a7a80f5ac98485f084283a919c1ac0e3990660f419c1a6163345e81cb08f52178a61a506a8840b0081020e3d414d2dc1ac1a8160104ff523090705339907a0ce0d30b7a81ba178bd843611330781850ed9dc0b6b2346c22e30432de2c9451680844bbb7876cec6f3596a5611718b4042edc0d40b61634068f52b0828c108b7876ced858bdc6c0cdea18485e2d21db3b6b38d9ea42f3081ad3309696eedc1dc0b617d4b1b03328a612178b496f0ee2c85b04225fbd850038d6419b52876cec19c1a008c2c5ebd4b090be1086b13f06a4c80476e238688696760ce0d3d417a0d00e0ad28a612178b4835264020727a82d034bb70e41081e83317acef1b5846b2072178a70d6340068041a2e6434cb776f0ed9d822b08d641a0b40430ed9d833016f505ee362be0d0c242f168cec19c0b6163420e58485e349ea3b70668ba05b0b1a1d4a0e5101a21c8534b776f0ed9d8340668ba0d41c13f61047069177068738077a8e12178a6842a4a34804ef7071ea06937a011ccb84838ea4348bb834c4066845038f52178a68d234863004861071ea0a68340126a3848391a4533b70de1481eb10009070deb990d30ed9d830820c4068f7bab2b8c10cb776e28c18310732deeaca97042edc2933b620187bd9bd0381a5db830820c40683991a356451821176cec1800418c115ea42f709086348d000804617bd41a4e120d0049a8e6442c2f8431a5c23b7028011ccc1c37a2bc34bb76f7068024d408ae12178a68431a4088c61a20118815f05629a5bbb7876099cc82bab2a5c10b3b7086f617c1c10a1a5dbb3b6210704fb7b10a1a5db83d7090be0e09f10a1a5dbb3b7080904281c0d2edd8d0147330bc4282b0d30ed9d83062031a0e77b85f0c0693d476f148184106203420e0d18d2299dbc52876cec180c60230be10c697080845e845035dec108bd017dec5e81c0d3dec5d81c0d30ee0877bc6d0bc5ecb7aa502dccb84c6d0be5ea928d32dea940b08b8da17cbd14d1a65bd5287704205da997a0865bd5283502c22c2f97b085c2469ef70705e86908bdec108bdef7d481b8218770421bb5285ef520277b86c1a61dc1017b0de17c04ef70d83483b85e06805bd4b080845ef5208a0841d80bb080845e83bea5611cc82101 else 0x3d073b846f78d876c2f14c2f433c107098d8fcc2f1a42f65bd52816011c263697a29868c3b82031fbd82117a38e5b8a30cec4205b9997aa5cd48210cf54a08310816344685a91472f4108ed17c19e1db3bc6ce1063c2f17b2ddccd5283502c1ec2f97b08634b8496edeea941a816011c204585f2f4534218d32dea9004054c40030c814d0ec135d4733566a92971900858800b7321a20e37b1122f434b848381ac4f8bd0d2ced8800b0d1dec0e02b17a1a59db1a0d0e10158bd0d23465b867aa50418840b))
def uL37 : PT := (124,3,8,11,uL37F)
def uH0_37F (i : Nat) : Nat := 0x5ac00015c02f01f40460b406d812426010806800d023801f03a81b42da00007405f028000a04204d02dc0e601382140ec09609880a42a2150000030027c17207c83c4122000069800011411e79c0054110125058000000000202f80002d415f029828029014a06f83342d208d08285b002ed3506105c41820fc070837416404d08181600fe17a0088141a740b7099031c2ee15d0bd801412a152793bc8c25812e00003cc1880e70a2849c2a612d08600dc0001370030cc02b002e00005301ca02b03c0c9414c156024059c230d2d05d85cc06001069083e813c1660bc041c1b80fe05400500820e4693048004c0eb0a484902f210d0bb0239e8805b79782ac2720080b20cbc0f6d2e09e032c00010407b3d0c00000001283241ae0b80003ce4158080044800028803c08a83d022c03908d8c8815a08200b04ec12402a69a00040cc02f06782f80c801e0a3048414e0420700185a4a08b01f806c0d20a901882bc146d1f01f04081f0d2b03505080f4123093012c1a40b500934a02ae31f06f02e41dc10e03f019c14432c09501c4030155079046822e0ae046017001a174028801001611f01c01000e6d30011038868a0d909982941fe10f04d00b428e122089811810ed2708c81b816602c07483f426c00c02385a003409d01a83c01260d505d038c06616f08e816812e15b037858822007c00001b000010903c850c1d409405505d40420bc0000ce801204f062842c00003b07a8038274019001835009c33102a03dc17a14103b803c10cd3119401480ac0ec080826413010a01d01282bc0d604d85802700c60ac856829a10002600d8040161790836022403200e830c2e00a108a0cd40ba01c03184fc0c409c05f81802560b6047853c086128076820c10202800001a1e4414b012001c000340094800019c03d192004c29c06b0b1841800017d02284bda4013505201d06520fb058827c0b20da077832008816502b83442220000aa0ccc0ca0cc03901c01200ca02a84f5a520204804ca0c210382c2405848361100014080410000320e05808122c0101406020383406001e8100804028000a040480c000205074080c138ac480f0506c2e00050903c02008100e12018501a0700800220000010021808000041b0003c1a0c2488c003f010343e020406cbe1b300000a2d0100844000302c3c200280c00000185008000201444041500028260382c04881b8843c03200080000018704202
def uH0_37 (h : Nat) : Option (Nat × Nat) := lw0 141 447 9 13 9 4 uH0_37F h
def uH1_37F (i : Nat) : Nat := (if i<1 then 0x7430100e804b04bc31f08843840f8c2f40d942fd167c3cf1080186057836009345c90de42ad06e87370d0028205100550aa8043000030e09a806e0f342e400a827700003bb07a02f20a2c04d097402b070c3bd03c83dc064c2ec1de021d086449008701e40a943420c8009a0e7c18000580780ed8220083475d00001420ef800000001920fb405666a429300dc2330b4419e044800009a000008780000dfc58d0fc40250bbdd710f142f805343730084086000016b0dd42d51025b3a67203a50f1000510843a301c416801d03166db45de1b61c32039420e0e583f70868171090c3b1772423b01681e306f004709403530a7024a0000044061432f6d1433b0454000001c1c907603901a102ed029119806380880c70079082c1ac0cc1b5a00b03ac031c07b02c40c602980890cf42a401843c11d9c1db00c83ba16640007d2816f09701c660c834d06a874c04583810a4010c05d81c00d2c4dc066827f09243e21d540e203b83d504ec0c502582f00b1c26d0cead7908a193f00802b901c007702e82c20a541d10c55b630b1811407643f8171c3690fcc0c408183f406f83d100ec1fb07b40c11b6873110500cb1c182eb0504165073c2160460265204ddc702f43e004e43fb057c12510c02c030040060080000b00600000004086004020350120c0028000260040385a0281c00e8010000c80001c01a008018000340541400001c01411aac006014038000000240000c3680080481000006c011140cc0ac028006321180885d0be0041000300a008c28060e2004028010000101105700200c0881b0040c0908fd0000684c0000d29fc040001ec040108010000ec0d00f000005aa80400201c00000004025ad804004014091620fa004040010060000881200e0b40f0030a20241800109200c0d0094040ec090001320140000100408c06001002004d100000003c0700100003c0081a5b407c148032d6000370010100c41a0b4052008a20ad02212c0c91e10c0402300000c5fc14804004020018040140c0008b400a054009560560500b0130040fc001ff0085b81200a008000260041000400089902e6641b00e0220041a8000040080001c4ee0480007201a0781a01001802c010070ea160000000080680a02b024000008106e809415a000060040b000052000089ef03e0280daac0300d40000600802c020050320241502c0fa048012000000541180000009c2801104a008010020da0305980000e0080002d0b00147e026012000008000361f407104076028078060041580780506822c520930100bc028010b8004150020160140005602e1114c0d902e3bc000040d087401a4700809cb3808000010ce00400833c0013e02402c0102d04c2440000d01a21011007020120a3814006000078000d8004000160040500180003012c0f0180021580a9e2 else (if i<2 then 0xa00aa00030c8c33400e1f5b002c37b102821b0c481f305f03ea16742ce09ed8260f481030d50751064033c00240360d8c3780a3807c070815a0b641f10b3c3640af408c049814a0c0012b04cc01806b81e90ff99a207f001303a42ba06e04890ca0140029c31a019805c04d00e30f7804806a6da01d0c4290fbdb60037000d08480b016b01211d001431d041ad07383a80384d8c02cc060028009509f04de0eac2260c5009c04b800a09502530d783aa03ddf700af299a0ca40c204a82a90db83a40bc40d6079413f0d7c73900641570211f510a7c06d0ba83b46dc00a305c801f02340d80e88210084475b671808b07781ee003827e08302f906ed18c091c1110eb43b00854102094877409302cc098801d010837e008c3b207701f5062403300781b1095c2560a05f4218181df0b4c2790c1c0d205842a70e803270e501977ce02e100b8098035c26004a448c0be838704f076d0b701ea033c1a7082a36d0189f730e5c2f70ad824b051c05f090411b0aac1660c240540e381830acc2b204e8160048038a0bd41eb0f2017901d98110c28261035038d624c2220b100f006fc25b9c8828f0c642640ab834c01319c90e30765043c2a2020834311d02348b6c3b305fc1d30a4419b0d8836b03383e703e41a609bc0680fc80580ee25d00f5c2bb0f99c8b09d81e203902d80715f5c08ac56c00d427a062021816580af096830508b80bb08b41d51718245021cd630a3039e178833903786e06d28542042c209174c07d01900920f00283078432e0b983af181c73a030c3d80b6c34f0d5c6ee0ba45c50d9822f027c2a003f42510cd41986cec0aa090800203bc1c70a340151d242af0b0c3ca102074511a05c8178013d04299ca15f03820c902b504a00a903f8001160037a0c183eb04c00ff067c32d0e4430f024c18b0a2043503345da01a407f0fe82e00d4806c0a241ec671430d08e83a910bc74f60802ff07f40cc7cf834a6d6c053041c25f70982850cf832209658891d5015077281cd06742e50fa1f6a065009101ac1360a283380f4c0ec1dc009e02d429e013c11e174400f6cf00f10c31dcb01940ad089401a055446904140340c4c0262b6c10d0cc410605242da08f031e0ff02020e202b701d42c90a19dc80cfc1f000103898ad83c705a436a1bbc2800b002d609cc29a06300c96d2c0d3053c2990e703dd088c0810e85b3909e018701780f406842170b1437c0644337034429d0d540720d683500a598db0145da208203fd00fc02d05b82010a6c3e40e2c37702b0177084c0fb0edc1ca6cf42c87db42940ac43180c8415c01182301d082740040385085032b62300b40b28109046430406d42d46d583c90c44024122c1d40a5c18405183bc08fc11f02145870f6823903a055102840676d401da06c02630ad18910ccc12c03741641d6023d0b else 0xe001828b659620a8414c059c09401e84530c6c37d01641ef06cc0450c943cc01483db02b811d142c21f0f2d90b10481dd624839306040c07d5833205e00bf072c05d0f58159056197110b43860e0c0170ca82a6665039a7d482ee0e602e20c2003d08ddc880b9c03e048c20f04b411005d42277d0c049036c2fe05481fe7d1c00809981270c99b4905c017e04903f00031f46007000626780f808e016d09f424e0d183700bcc01b03a875c023c1e70cb03c3025c0570d9c1b274fc0f50f3856a1da004002c838f014006f03e82ac1d282be01cc207038035d5cc0041047010e14380f30b4013706ac0da0364028026475709d41d702402030520244090024604c9b360f4035608003d47cf419504201ff09783ec1db03c20d3814b067034400c031d07983760b8c3f5044c248020c09d0b042360d2022406942b00d603020dc588b04e036c054c39b03541af000044700440fc6d3c3450e740b800a4399045c3ae0f7c56200882d708a429200c424f00501d006e43a610cc1990db44270139b5c08b017d0dd007e672c0b906599c7046818a6d640120d240a20efd5df02002870e54122063c310123c1311b983920fe598709541010d701c106dc27108142fb1abc3f6069056400e416c0fb80270d6c2b8096009b0c2c1d207e00a5037c06306d81b40bd83e5051418d0730446099c16a15cc1bd02dc15409b075e0ed65ba15c80a808c42bf07d815b058c26b05d017a02f182d00bc4287da1b6c07d02de76a414e15500eb05442320bf01e009c017b0b2c341601df4e6cf82d20b343e165a43d907e826e04f822a0a8c2350d443680ee406a0229b6b05880ed0d643470e9c28406a01c80cd9f5007103030a600c81d8df450f1804a65f036103281f9016d99c068837209a41d609c83e902f80f605580e708100ab0dbc1f2057594f04d42e8023810405cc317034010003980b607dc8dd6d8823e00f01a30b7c1))
def uH1_37 (h : Nat) : Option (Nat × Nat) := lw0 412 1246 11 14 10 4 uH1_37F h
def uL40F (i : Nat) : Nat := 0x5c5baa41d83408017bd85e5e8423496e1d8200586fbd86da905e1096e1d83405ea417b08108760d0206a6f61784234cd2b481001ff46540bfeb4a817fd39502ffa52a05ff46540
def uL40 : PT := (5,2,8,6,uL40F)
def uH1_40F (i : Nat) : Nat := 0x20b60a8310540b22243d830078198160410c211c0803f0261182d03303e0f8260570461c4108061c21d42e86401a0500001a000028378741c60e8058000000600b03d0760802c07302ec2433b616c818c1303513a1e82b0e77c210c290151d0398148e20dc17c3506011a0c40cb9c06400c4f86c0021381c0041d214c0782f0a013c3b0110680301b06d024128120421180002681e01c1442f3670000880006b7ce0000d8000001c03c0000d2268390000000001707909611012828638171b289c0900dc158490121a03281d000d9822827712000203e607201c0e02d0aa0200287703030100010000000506001b000000002a002500000205010c020000080002050b3b030000030600080e052a070b230303000100090504000a010002050000000306470206050305040107
def uH1_40 (h : Nat) : Option (Nat × Nat) := lw0 75 165 8 11 7 4 uH1_40F h
def uL : Nat → PT
  | 24 => uL24
  | 27 => uL27
  | 28 => uL28
  | 30 => uL30
  | 31 => uL31
  | 33 => uL33
  | 34 => uL34
  | 37 => uL37
  | 40 => uL40
  | _ => emptyPT
def uI0 : Nat → Nat → Option (Nat × Nat)
  | 27 => uH0_27
  | 30 => uH0_30
  | 31 => uH0_31
  | 33 => uH0_33
  | 34 => uH0_34
  | 37 => uH0_37
  | _ => fun _ => none
def uI1 : Nat → Nat → Option (Nat × Nat)
  | 31 => uH1_31
  | 34 => uH1_34
  | 37 => uH1_37
  | 40 => uH1_40
  | _ => fun _ => none
abbrev bk := blockU uL uI0 uI1
abbrev bm (k t s a b : Nat) := @blockU_merge uL uI0 uI1 k t s a b
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c24_0 : bk 8 0 0 1=true:=by
 apply cellsBlockU (ar:=9) (d:=0);simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
theorem a24 : bk 8 0 0 1=true:=c24_0
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c27_0 : bk 9 0 0 48=true:=by
 apply cellsBlockU (ar:=10) (d:=2);simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
theorem a27 : bk 9 0 0 48=true:=c27_0
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c28_0 : bk 9 1 0 10=true:=by
 apply cellsBlockU (ar:=9) (d:=0);simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
theorem a28 : bk 9 1 0 10=true:=c28_0
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c30_0 : bk 10 0 0 425=true:=by
 apply cellsBlockU (ar:=11) (d:=6);simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
theorem a30 : bk 10 0 0 425=true:=c30_0
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c31_0 : bk 10 1 0 2=true:=by
 apply cellsBlockU (ar:=9) (d:=0);simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c31_2 : bk 10 1 2 530=true:=by
 apply cellsBlockU (ar:=10) (d:=6);simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
theorem a31 : bk 10 1 0 532=true:=(bm 10 1 0 2 530 c31_0 c31_2)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c33_0 : bk 11 0 0 382=true:=by
 apply cellsBlockU (ar:=12) (d:=5);simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
theorem a33 : bk 11 0 0 382=true:=c33_0
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c34_0 : bk 11 1 0 1=true:=by
 apply cellsBlockU (ar:=9) (d:=0);simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c34_1 : bk 11 1 1 173=true:=by
 apply cellsBlockU (ar:=10) (d:=4);simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c34_174 : bk 11 1 174 768=true:=by
 apply cellsBlockU (ar:=11) (d:=6);simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c34_942 : bk 11 1 942 81=true:=by
 apply cellsBlockU (ar:=11) (d:=3);simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
theorem a34 : bk 11 1 0 1023=true:=(bm 11 1 0 174 849 (bm 11 1 0 1 173 c34_0 c34_1) (bm 11 1 174 768 81 c34_174 c34_942))
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c37_0 : bk 12 1 0 42=true:=by
 apply cellsBlockU (ar:=10) (d:=2);simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c37_42 : bk 12 1 42 82=true:=by
 apply cellsBlockU (ar:=11) (d:=3);simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
theorem a37 : bk 12 1 0 124=true:=(bm 12 1 0 42 82 c37_0 c37_42)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c40_0 : bk 13 1 0 4=true:=by
 apply cellsBlockU (ar:=10) (d:=0);simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
theorem c40_4 : bk 13 1 4 1=true:=by
 apply cellsBlockU (ar:=9) (d:=0);simp only [cellsU,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro
 all_goals decide +kernel
theorem a40 : bk 13 1 0 5=true:=(bm 13 1 0 4 1 c40_0 c40_4)
theorem tabs : ∀ k ≤ 13, ∀ t ≤ 1, bk k t 0 (uL (3*k+t)).1=true:=by
 intro k hk t ht;interval_cases k <;> interval_cases t
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · exact a24
 · rfl
 · exact a27
 · exact a28
 · exact a30
 · exact a31
 · exact a33
 · exact a34
 · rfl
 · exact a37
 · rfl
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
    ImpossibleU graph 13 1 (stateSetT uL 40 idx).toFinset := by
  have hall := forestU_all uL uI0 uI1 13 (boundsBefore known383)
    (before_sound known383 valid383) geomdead tabs 13 (by decide) 1 (by decide) idx hi
  have htgt : targetOf dead = graph := by decide +kernel
  rwa [htgt] at hall

theorem perm1_ok : autoOK graph ((dead.autos.getD 1 []).map swapRows) = true := by decide +kernel

theorem no3077_pos : ImpossibleU graph 13 1 inputs.toFinset := by
  have h := rootU_imp 4 (by decide)
  have hs : sameWords (stateSetT uL 40 4) inputs = true := by decide +kernel
  rwa [sameWords_sound hs] at h

theorem no3077_keep0 (j : Fin 9) (hj0 : j.val ≠ 0) (hj4 : j.val ≠ 4) :
    ImpossibleU graph 13 1 (inputs ++ [w10 j]).toFinset := by
  fin_cases j
  · exact False.elim (hj0 rfl)
  · have h := rootU_imp 0 (by decide)
    have hs : sameWords (stateSetT uL 40 0) (inputs ++ [w10 ⟨1,by decide⟩]) = true := by decide +kernel
    rwa [sameWords_sound hs] at h
  · have h := rootU_imp 1 (by decide)
    have hs : sameWords (stateSetT uL 40 1) (inputs ++ [w10 ⟨2,by decide⟩]) = true := by decide +kernel
    rwa [sameWords_sound hs] at h
  · have h := rootU_imp 2 (by decide)
    have hs : sameWords (stateSetT uL 40 2) (inputs ++ [w10 ⟨3,by decide⟩]) = true := by decide +kernel
    rwa [sameWords_sound hs] at h
  · exact False.elim (hj4 rfl)
  · have h := rotate_excludedU (rootU_imp 0 (by decide)) ((dead.autos.getD 1 []).map swapRows) perm1_ok
    have hs : sameWords ((stateSetT uL 40 0).map (movedWord ((dead.autos.getD 1 []).map swapRows).reverse)) (inputs ++ [w10 ⟨5,by decide⟩]) = true := by decide +kernel
    rwa [sameWords_sound hs] at h
  · have h := rootU_imp 3 (by decide)
    have hs : sameWords (stateSetT uL 40 3) (inputs ++ [w10 ⟨6,by decide⟩]) = true := by decide +kernel
    rwa [sameWords_sound hs] at h
  · have h := rotate_excludedU (rootU_imp 3 (by decide)) ((dead.autos.getD 1 []).map swapRows) perm1_ok
    have hs : sameWords ((stateSetT uL 40 3).map (movedWord ((dead.autos.getD 1 []).map swapRows).reverse)) (inputs ++ [w10 ⟨7,by decide⟩]) = true := by decide +kernel
    rwa [sameWords_sound hs] at h
  · have h := rotate_excludedU (rootU_imp 1 (by decide)) ((dead.autos.getD 1 []).map swapRows) perm1_ok
    have hs : sameWords ((stateSetT uL 40 1).map (movedWord ((dead.autos.getD 1 []).map swapRows).reverse)) (inputs ++ [w10 ⟨8,by decide⟩]) = true := by decide +kernel
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
