import Mathlib
import PEqualNP.Defs

-- Based on pull request 5353 of this repository by odinfree, which does not pass the file rules
-- (LINT: hash sign). Comments were removed and array literals written without the hash sign; the proof is unchanged.
namespace PEqualNP.Outside.L_meta_2149
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
def g15samples : Array (Bits × Bits) := (List.toArray [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)])
def g15columns : IndexTree ColumnInfo := (.leaf [])
def g15autos : Array (List Nat) := (List.toArray [[],[33,48]])
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
def g31samples : Array (Bits × Bits) := (List.toArray [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)])
def g31columns : IndexTree ColumnInfo := (.fork 2 (.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def g31autos : Array (List Nat) := (List.toArray [[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]])
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples : Array (Bits × Bits) := (List.toArray [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)])
def g47columns : IndexTree ColumnInfo := (.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := (List.toArray [[],[83,32]])
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := (List.toArray [(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)])
def g55columns : IndexTree ColumnInfo := (.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := (List.toArray [[],[84]])
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := (List.toArray [(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)])
def g63columns : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := (List.toArray [[],[50,65]])
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := (List.toArray [(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)])
def g111columns : IndexTree ColumnInfo := (.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := (List.toArray [[],[83,32]])
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := (List.toArray [(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)])
def g119columns : IndexTree ColumnInfo := (.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat) := (List.toArray [[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]])
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
def g189samples : Array (Bits × Bits) := (List.toArray [(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)])
def g189columns : IndexTree ColumnInfo := (.fork 4 (.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def g189autos : Array (List Nat) := (List.toArray [[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]])
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples : Array (Bits × Bits) := (List.toArray [(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)])
def g127columns : IndexTree ColumnInfo := (.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat) := (List.toArray [[],[101,66,16]])
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
def g191samples : Array (Bits × Bits) := (List.toArray [(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)])
def g191columns : IndexTree ColumnInfo := (.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (.fork 2 (.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (.fork 9 (.fork 4 (.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (.fork 5 (.fork 2 (.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (.fork 2 (.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def g191autos : Array (List Nat) := (List.toArray [[],[84,115],[117,67,32],[116,83,32]])
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
def g251samples : Array (Bits × Bits) := (List.toArray [(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)])
def g251columns : IndexTree ColumnInfo := (.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := (List.toArray [[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]])
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := (List.toArray [(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)])
def g255columns : IndexTree ColumnInfo := (.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat) := (List.toArray [[],[84,115],[117,67,32],[116,83,32]])
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
def g383samples : Array (Bits × Bits) := (List.toArray [(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)])
def g383columns : IndexTree ColumnInfo := (.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (.fork 3 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (.fork 7 (.fork 3 (.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (.fork 4 (.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (.fork 4 (.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (.fork 7 (.fork 3 (.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (.fork 4 (.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def g383autos : Array (List Nat) := (List.toArray [[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]])
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
def deadsamples : Array (Bits × Bits) := (List.toArray [(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)])
def deadcolumns : IndexTree ColumnInfo := (.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (.fork 4 (.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (.fork 8 (.fork 4 (.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (.fork 4 (.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (.fork 4 (.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (.fork 8 (.fork 4 (.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (.fork 4 (.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (.fork 4 (.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (.fork 8 (.fork 4 (.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (.fork 4 (.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (.fork 4 (.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (.fork 8 (.fork 4 (.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (.fork 4 (.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def deadautos : Array (List Nat) := (List.toArray [[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]])
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
def hashrestrictedl11 (i : Nat) : Nat := (if i<1 then 0xc1b5add011e81124450c3ea5c13b407274e85915c39d0c00d88150e791cb40c5ed0c9bc327aa27eaf919d389c944f96acc45d60131309832800061abc19ca1a4c1d63eea14d209bd4671f0d0b02441110c09b33efc4f51da0000b07025cc9514b49258c00031997106d7b9cd81924a9f310828f818760000e191c99000000000003c6748ccd83f61af88250ca20c7406f80b840f38420000000618f13b1c0566de0000e0c0f76ea068c9f000000000000000b08f84d10dfb9e83925f70bca615e2916002e24fa61bb0372c1d143f64027237829967ee939f3dee31c00000e3f34eb15d470c5b700000003c68d44dc92200014ab7042d2b40002c5ec1ff9a2ec6a9e74800083ceb3624fb000061a6c4ac00059eef16e8007671adcac30eb5bd44cb886a986177d43778cf48a98407230706a6381a2a4e0870d21b38c202425f0cdc306c2712be900000018364000007f2891b2c60fdf0b1a1cd902ce4381890000855c08ef965c0cc21740a2f4a348d6e07a85f392de2e6000149d2d3c000144d5e0630336149c066c3cd9e95ad1b67f882f84c000b65da09869a8f057d379cd3000000002510000140453188564caf59619bc2000369a8000c22253d988b398a005575548da85f7716bc3218e73813c182a76446dd8bf43ba17b6c90096b702db0228032040c0c46358cb8bc47313502614e601de5b0da634c5098b3d23e76a7ce32992c358a4312add05b207d43b38d0dd44437a8171cfed8fee80cc26d4ca95887173c2ca02fb9afe15dc41d44ec075e091c7240149046b82904568723010ba66a4ba894c0456ab1c6db691e07c012216d5cc7716e489624da25f10c3c24324eea150da582970791c75507ab0d0516b857f474403ec610805485443c005e6ceb945c12a7e10e8113db9f2db12a8ca42cb503e6e25842b8da6d070768b8c409b113c3201f6cec1500369116ee5dcc944a3b4074c6b8968081c2034cd1d146a225225e894190a10d356ae8cb006f71f900334282c7f239bf02a25269a27017a59c0128832000041c02040080e1472868001f0095000440200c2e060a23e1e005200c0c055409c08522004856221b00800010195c12050880408001100434080d8d800061a01000260d84c0003100100400038ac1c0a0a0000409080440a022e0282057090000001028000a080007824001401400103284c4e0e0a02c0605000241603010201c1e008006225018000a080180c060509814027800018060a2000002061e00c00010080000161e014000100008cc10010000a01030080002020381c160703000080300002b8040086e0400020041a038003e00000000a000100c001a039241a07000402a7604800063c080001c004301c040f000300200098100600010200a000081000010180c0412060cc0200018040e08050000001068180000 else 0x489ce72c899bc2511f5c1598b925a35b9ae653cb109e5f402873f05291c33b2dd1ba2b6d9035bb923a18bec0ad407ba22110058442b66676ea4108c651182690038402ca031f4d80b491c40a3727d44a979ad13a17254c75e93ff0e4e65eef998f768124661089d034b11a87c7828f51a321333cb64b81be00b2129ac5a0170712a40b400000000001a53445400000001b4502d89885f28e923caf479d40000d3110c58c620001f240000753db8dbc4946fdf181221bd1bf8babcafc094d39843624b4f1bd94788e50000301f27058ba44660001d1c00001cbad8d40001cb7c9a0000112c9496087342b1e5fc000692a7a4184bc0003cb6104800008ce8000836e72b000000004ba957fac930000000000032f1d0c5f23803d80003cc7f335832c00041eb71de067000079ea03d822d80006835233dc7b4000503a49700000c4954b3e03560ee879104993000000ca4c8413189253f4d991d6d9efc5524075090b051280a447e014c0b40002c53d17800000003087800049dcf396a1f60ddc21ce1e00000000c184d3a800010e900000002470685e000000000fce531d04d437148021dfa8eb66e0885a4dcc079f0884aed1f8a07f03f400048a0c17702b26451117000023d544a295bd262b1104c298208b0682f2a90bc6c892731940004027c8c7e48b20da14a721000022af8000a0aba186c8304f34bf3d2f1010999f71ddc1630d934f49b00a6426e20000ba30000346f80002008000286d7464e2870608cd2f4bd0000000000079ba000016f80000000c1b0927000058c90000621f8bdd037d1e733d6e3ba082eb7a822fc11b17a4025122e838d138d3a5455745d7d272283a5b30a161e2fbc083eee308503f1f327572e1d893ab8060bf20f01f2f24f1236696b1c5c011c48ce4cc036ec0165a90e8d530a234e13e83da05241e285f24e4111831e1b51523991c2f327f39d252c456c941f6502004db6000187980000000b0ee948800000005357678ca7800000000c6b8c1c882ea0386539ecf301100000001cc8f1fcd38e83fde75ecf1abe2f41a87118c0000190aeec2f1fa000000020518000e2c9022a2c680007281149409be19b209c000000000006885379cc5500000233e3d1c4249a92102f5834c300000144561000064237b7e00024b30000193794a64558000f061f2c306a10d07278000222619776930d7158ee717e0000000062f800081daa581caffc2419bb1128eda70027a4975bb8ff388e6b8f)
def hashrestrictedl10 (i : Nat) : Nat := 0x3152b8edb964ef3fc0c002b256fa5d1f878a5d56740ea51c00022340dc4b0003eac9d5d400034d790510dc3c33ad4d0068cfa54001d0b28349000000028fd024f40021a241478b668000000001477eb62bc002881a5da7ace99448e01871c5990982c65871cf9d2f86b194c5fc400c91340004a92c29a5821daad648c28861ca11953c15e698c6e253a761981b76a800224763097b968001588202eeaef5917ad12ca0445b0d624b699e17cca2e5869d4db060a6c71f89b576931cd3c481bc45192bcfecad02fcbbce7eb208fc78418c4ec10acc8584024ed827ad8c3689f94815a526513438b200000000034f2c1c91c00197045400023c0018bc002228c8ba964c4003c7f5ae16de0982a13b1cf40912358e097e240012c6831a900002189a4bd0790f1b806700364004104b99f041082101206060007acd0010810466420400010000c0002
def data14 (i : Nat) : Nat := 0x18b6c40344ffd40
def lev14 : Packing := (1,1,7,0,0,0,0,data14)
def idx14 (_ : Nat) : Option (Nat × Nat) := some (0,0)
def data13 (i : Nat) : Nat := 0x240d57a0c89207a322344db4819032271640df209240d5208e40c8208eee49a5008003ff90aa07ff20940ffe29281ffc81503ff8a2a07ff08540
def lev13 : Packing := (6,2,7,0,0,8,0,data13)
def hash13 (i : Nat) : Nat := 0x40a800064
def idx13 (h : Nat) : Option (Nat × Nat) := let a := h % 2
  let sh := packedAt hash13 (a*1) 1
  some (packedAt hash13 (2+((h/2+sh)%11)*3) 3,0)
def data12 (i : Nat) : Nat := (if i < 1 then 0x406a9e8191320354f40c887a190118fb60c8c808c990190190fb60c8c808c9e29be108824c80df1047e29be108824084d51046109aa208c21320411e40640823c80c8104790190208f20320411842640823320411640640823d81eb3352ba68d18e7eb387982ca5e4531a78b0c3ce0bafdb7c0bc4dd4ae4b6eeb56d9daca7612af2d6e2b0354aa8ed39a987496a34d0ca81f3e29d5cdfa6a332496ccab24eb22a8fec71a2f714488bc35a12b04a80ebf71f5ef6479bbbd9d56e6a71eb7f1b8ad7a6abb431982c9e633b0717f2bb85b6acd9626adc548a9194469e24c6a5a923e8fc45da2890d68203fe9f40f4676239f9c48da26ae3409900c3a5e62dc95e0aaa528278933894247421990407b23ac1bf8d4864a2f81658a784e224e11087f83a21a40c0855026210e075832014a08202f80f0046000fff4c885503ffe2221540fff4c485503ffd2121540fff84485503ffe5520940fff54c82503ffd5120940fff4c482503ffe1120940fffa2052503ffd8614940fff60c52503ffd6314940fff60452503ffd6114940fff4c452503ffe1114940fff5d481503ffe5520540fff5cc81503ffd5320540fff5c881503ffd5220540fff14881503ffd3220540fff88881503ffe8814540fff60c51503ffd8214540fff20851503ffd3214540fff88851503ffe8808540fff61421503ffc8508540fff95421503ffd8308540fff54c21502ffda321540dff64c85503fde3321540bff688855037fd9221540ffb88885502ffda121540dff64485503fbd4121540ffd84485503ff93021540bff694825037fd9520940fdf95482503fbd5420940bff68c825037fd9320940ff78cc82502ffda120940dff64482503fbd4120940ffd84482503ff93020940bff6a0525037fd9814940effa2052502ffda614940dff65852503efe6614940bff68c525037fd9314940ff78cc52502ffda114940dff64452503fbd4114940ffd84452503ff93014940bff69c815037fd9720540f7f9dc81502ffda520540dff65481503f7e5520540fef55081502ffda320540dff64c81503fde3320540bff688815037fd9220540ffb88881503ff93020540bff6a0515037fd9814540effa2051502ffda314540dff64c51503fde3314540bff688515037fd9214540ffb88851503ff93014540bff6a0215037fd9808540effa2021502ffda508540dff65421503f7e5508540fef55021502ffda308540dff64c21503fde3308540ffe4c0215027fda921540b7f69c85502efda621540bef69085502fdda321540bfb68885502ff5a121540bfe680855027fda9209409ff6a452502efda614940bef690525027fda920540b7f69c81502fbda4205409ff6a451502fbda4145409ff6a421502bfda808540b7f69c21502efda608540bdf69421502fbda408540bf768c21502ff9a008540 else 0x69482d5bd2322e4034de8e446451a520b56f48c8b905ab7a464460a68b5632110b7a634ea8e239171abd120b20722e3590590395e80f9b1ab2120bd01f2b058d5be6f03e5c80697d2c88c8713590fa4643ed873482c88c8a34be8dc36c90591191f1a1cfb6c82d507cd8d5900f8884c6bb6482d507cac103e65c6422171aae07215c9413aa39438221447755c871468904d8d78a905703916df32e411e35e2e4014570391adf7231a1109e2850344824c8069b7dc8904b903bf6a8e3209473482d5904839e40145ab2094cb904711850905ab209186c80d89049900d3643bf209720b22411bbf646342211a9c80d88704428d290591209069482c890486a9e8190d04465200bad5bd0790c8e905ab7a4644c80d8354f40c8a8cb0d905aa2bde8191d86b56f48c899003e6a9e819151947320b5457bd0323a3890dab7a064560ad5bd23220d36aa402bde8191b201c8d8320f4c68d900d69923491de9641da9bd2c8c68836a6490de88d59063d31a320682232910e28d5e9640d07bd2c8c686826400f9127a1918d1b201c40a46923bd2c838e206a43642357a1982bd2c8c68834a448d5e9640d063ab207d0c80c8a8cf6d900de22590191ddfb22321be8dc640db1ee6406477d1b66e3205dec80c8edb591190c92ed920320322a33db240225903c864763ac88c87db6400f978640646467b61c7200f6c80c8e38a421ed90191582b223218d290089640645755c8c81c537cd9104ee2baae46416fab2209dc5b7e411f8b900e42b9be209919f15321af20b7c571050d4dbf208d321b5d5486df1c4413f8a340823467c515c681ec4130d1208bc5c80df32c412a33e2e402bdbe29082761adf9046348ae340824c80ea354412233903be37daa2099dfb56411848901aa20911948871482d5104cc75ab208f20224d510488ce403882d6a882661ad5904602a44905aa2094f6c80c81048efe401724364082677ec89047900e4640824c8132486c8104ad4d91208d32486c81048492406408244642e48066b204132416448230b9201a6c8104a191e86a8464c80d53d03226406a9e819111a3d0d508c8341aa7a0644c80d53d03226)
def lev12 : Packing := (136,3,7,0,0,13,0,data12)
def hash12 (i : Nat) : Nat := 0x31b93cab80253b308029b800000a8000001914263880bb8d28bc0c329ec025a91635c2221bb9b113ad118fab40bf0209ae03bec12db405893e02872c2abf911e1da792030843afbd171f148423980c9d0797930012a42a22b60480330b1ca13ab21ab71986201b0eb50d9c000f01acaeb785158043108021800b8000189fa6b020a842a3088e41902716af1534a486bdba369a0a3381040008eb708250680704a00001109200b000506540340404b803604d8290000002005f180428402
def idx12 (h : Nat) : Option (Nat × Nat) := let a := h % 45
  let sh := packedAt hash12 (a*7) 7
  some (packedAt hash12 (315+((h/45+sh)%150)*8) 8,0)
def data11 (i : Nat) : Nat := (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x550825023fedd326412819f76a633209408ffb74c8904a067bda9504825033fad4c22412819fe6a530209408ffb74cc0a4a067bda4660525031fed4d10292813bfaeda614940cdfb72d30a4a066fd986985250357f4434c292811ff6e99614940cdfb4ccb0a4a067bda46585250337ed4ccc29281aefa21a414940dd7cccd20a4a047fdba64c5250337ed3326292819ef6919314940cfbb53198a4a06edda68cc525037ced2466292811ff6e99114940cdfb4cc88a4a067bda4644525027dedd282292819ef6a54114940dd7b4ca08a4a067f5a98445250377ad342229281bed6921114940cff352980a4a06ef9a64c0525037dcd226029281bf668d30149409bfd76d3902a065fdb969c815023fedd32e40a8197f69d9720540cf7b48cb902a065fda99dc815023fedd32a40a8197f69d9520540cf7b48ca902a0677da9954815036bed3caa40a81b6f9dda420540de7caad2102a04fbdba550815033ded4aa840a81b6f69d54205408ffb74c9902a065fda764c815033ded232640a819f76a63320540dbbb4f19902a06f9da48cc815023fedd32440a8197f69d9220540cf7b48c9102a067eda9888815036f6d3c4440a81beb6922220540cff35298102a06df9a74c0815037dcd226040a81bf668d30205408ffb74cc0a2a067bda4660515031fed4d1028a81aefa21a4145408ffb74c98a2a067dda98cc515037ced246628a811ff6e99214540cf7b48c90a2a067eda9888515037d6d244428a81bee6913014540dfb346980a2a04bfebb6a0215031fedcb5010a811ff6e99808540c7fb50cc042a067bda4660215025fedd51010a818ff6a68808540cbfb30d3842a069fe8869c2150337ecc34c10a81abfa21a6085409efd76d2842a0677db9694215033becc34a10a81adfa21a508540de7b68d2842a047fdba654215031fed432a10a8197f69d9508540cdfb4cca842a0677da5654215033ded232a10a813df6ea5508540cefb532a842a06b7da8954215036bed3caa10a81b9f69a5508540d77d10d2042a06f3e55690215027dedd2a810a819ef6a55408540d77b50aa042a06dbda75502150375ed32a810a81bcf69554085409fbd76d1842a067ddb968c215033eecc34610a81af7a21a308540cfbb2ad1842a06f5e5568c215037ceaa34610a81bf66c1a3085408ffb74c9842a063fda864c215032fed3b2610a819bf6999308540cefb4ac9842a067bda464c215033eed1b2610a819f76a63308540d7bb5119842a06ddda78cc2150376ed346610a81bd76963308540df3b4919842a067f998680215035fd4434010a819fe655a008540def4aad0042a06fb954680215033fcc9b4010a81bf68cda0085409ff37498042a067f9a94c0215035fcd426010a81b7e69d3008540ddf34c98042a06f79a54c0215037dcd226010a81bf668d3008540 else 0x81bdf6965508540eefb2b2a842a06fbe88690215037dec2b4810a81bef215a408540df7caad2042a05fbebb550215037ded42a810a81def6615408540f77d10aa042a06fbda555021503f9f2aaa810a813ffaeda308540cffb72d1842a04ffcb868c215033fecc34610a81affa21a3085409ff96ad1842a067fd9568c215037bf2ab4610a81bef551a308540dff360d1842a06fdebb68c215037eedc34610a81bf72e1a308540dfbd10d1842a06fddb568c215037ee5ab4610a81bf7615a308540dfb90ad1842a06fde5568c21502bff5db2610a815ff2e19308540cffb50c9842a073fe8864c21502bfe5ab2610a819ff6959308540eefcaac9842a04ffdba60c21502bfedcb0610a819ff6a58308540d7fb50c1842a06dfda760c2150377ed330610a81bdf6958308540df7b48c1842a06fdda360c215027fedd2a610a815ff6e55308540cffb52a9842a06bfda854c215036fed3aa610a81bbf6995308540defb4aa9842a06fbda454c21503f9eaa2a610a81bf768d5308540dfbb5119842a077dd988cc21503def4446610a81bf76963308540efbb2b19842a07f5e558cc21503fceaa46610a81bfea21a008540dff30ad0042a06ff885680215037fd2ab4010a81bfe60da008540dff2a6d0042a05ffabb4c0215037fcdd26010a81bfe6a13008540eff33098042a07bfa884c0215037fcd2a6010a81fde9553008540ff72a898042a07fd9534c0215027ef5db4642a819f76e5a321540dfb360d190aa047fdba64c855032fed3b2642a819bf6999321540cf7b48c990aa067dda364c855033eed4c6642a81b7769e3321540ddbb4d1990aa06f9da48cc855027f75db4442a819fb6e5a221540cfdb26d110aa06fce33688855023fedd32442a8197f69d9221540cdfb4cc910aa067bda4648855033eed1b2442a819fb68992215409fdb751110aa067eda9888855036f6d3c4442a81bbb69a2221540df5b491110aa06fcda3888855027fb5db4242a819fd6e5a121540df6b68d090aa067f593684855037eb19b4242a819fd649a121540dfcc44d090aa047fdba644855032fed3b2242a819bf6999121540cf7b48c890aa067dda3644855033f6d132242a819fd68591215409f7b74a090aa067bda9504855036ded3a8242a81baf6994121540df3b46a090aa06fada2504855037dad0a8242a813fd6ea1121540cfeb530890aa06df5a78448550377ad342242a81bed6921121540dfab470890aa06fe5a2844855033fcc9b4042a81bf68cda021540cff324d010aa06fea22680855033fcc8b4042a81bee505a021540dfe422d010aa04ff9ba4c0855033fcd4a6042a81b7e69d3021540ddf34c9810aa06fb9a44c0855037ecd1a6042a81bfa6893021540dfe3429810aa047fcb56a4825023fe58b52412811ff6e99520940cefb532a904a067bda9) else (if i < 3 then 0xa911102a06feda388881503bf6c9c4440a81ff38ce2220540cffb5311102a06dfda7888815037ded244440a81bfb68a2220540efdb2511102a05ffabb4c0815037fcdd26040a81bfe69d3020540fbf4ee98102a06ff9a54c081503fbd2aa6040a81fee5513020540ffb2a698102a06ff9a24c081503bfcc926040a81ffa88930205409ffd76d40a2a067fdb96a0515027fe5935028a815ffaed9814540cffb50cc0a2a057fcb2660515033fed4d1028a81aff6a28814540e7fb31440a2a06fbe88690515027ff5db4628a819ff6e5a3145409ff970d18a2a067fd9868c515035ff4434628a813ff2c9a314540affd76c98a2a057fcb864c515033fed432628a81cffa219314540aff964c98a2a04ffdba60c51502bfedcb0628a819ff6a58314540df7b48c18a2a06fdda360c515037eed446628a81df76623314540f7bd11198a2a04ffebb688515033fedcb4428a813ff2e1a214540cffb30d10a2a06bfe88688515033fec9b4428a81bf78cda214540affd76c90a2a057fcb8648515033fed432428a81cffa219214540cffb46c90a2a077de33648515033fed132428a813ff6e98214540affb72c10a2a067fda9608515035fed430428a81bef6918214540dfdb44c10a2a04ffdba20851502bfedc90428a819ff6a48214540df7b48410a2a04ffdba4c851502bfedca6428a819ff6a53214540df7b48990a2a06fdda34c8515037f6d444428a81dfb6622214540f7dd11110a2a06feda388851503bf6c9c4428a81ff38ce2214540cffb53110a2a06fbda4888515037f6d144428a81dfb64a2214540bff576980a2a06ff9ba4c0515037fcd426028a81dfe6613014540f7f510980a2a06ff9a24c051503bfcc926028a81ffa88930145409ffd76d4042a067fdb96a0215027fe5ab5010a81affaeda808540d7fb6ad4042a06bfcb56a0215035fed9b5010a815ffaed9808540cffb50cc042a057fcb5660215033fed4d1010a81aff6a28808540e7fb3144042a06dfe8869c2150377f4434c10a813ffaeda508540cffb72d2842a04ffcb8694215033fecc34a10a81affa21a508540df7b68d2842a06f7ebb694215037bedc34a10a81bdf2e1a508540defd10d2842a06f7db369421502bff5db2a10a815ff2e19508540cffb50ca842a073fe88654215033fed2b2a10a813ff6e98508540affb72c2842a067fda9614215035fed430a10a81b7f69d8508540ddfb4cc2842a06f7da5614215027fedd10a10a815ff6e48508540cffb5242842a06bfda821421502efedb90a10a81b7f69c8508540bdfb6c42842a06efda6214215037bed290a10a817ef6d08508540bfbb6642842a05fedb221421502ffad890a10a817fe6c08508540defb512a842a0777d9895421503dbf444aa10a819ff6a65508540d7fb512a842a06dfda79542150377ed34aa10a else 0x25037ded226229281bf768d3114940dfeb42988a4a07fb5414c4525037fad442229281dfd6621114940f7ed11088a4a06ff5a684452503bfacb42229281fbd99a1114940dfeb47088a4a077f59384452503feb19c22292819ff6a61114940ddfb4d088a4a06fbda4844525037fad0c2229281dfd6461114940ff6a83088a4a05ffabb4c0525037fcdd26029281bfe6a13014940eff330980a4a07bfa884c0525037fcd326029281fbe9993014940dff342980a4a07fb9414c052503fec98a6029281ffc84530149409ffd76d3902a06dfebb69c815036fedab4e40a81b7f2d5a720540dbfb66d3902a06dfdb269c815036fe5934e40a815ffaed97205409ffd76d2902a067fdb9694815033fecbb4a40a81b7f9dda520540df7b68d2902a04ffcb269481502bff5db2a40a819ff69d9520540ebfceeca902a067fda565481502bfe5932a40a813ff6e97520540affb72ba902a067fda95d4815036fed3aea40a81bdf69e5520540eefb2f2a902a07d7e77954815033fed4caa40a81b7f69e5520540defb4b2a902a0777d95954815037debab4840a81bef955a420540bf7d76aa102a06fbda755081503bdecbaa840a81f6f9dd5420540df7b4aaa102a07f3e55550815033fecbb4640a81b7f9dda320540cffb2ad1902a06f7e5568c815037deaa34640a815ffaed9320540cffb4ec9902a075fe7764c81502bfe5ab2640a819ff6959320540eefcaac9902a057fcb264c815027fedd2e640a815ff6e57320540cffb52b9902a06dfda75cc81503afecbae640a81bef69173205409ffb74a9902a057fdb954c815033fed4aa640a81b7f69d5320540defb4aa9902a06fbda454c81503f9eaa2a640a81bf768d5320540dfbb4f19902a077dd978cc81503eef3bc6640a81bf76963320540efbb2b19902a07f5e558cc81503fceaa46640a813ffaeda220540cffb72d1102a067fd97688815036ff3bb4440a813ff2d5a220540cffb2ad1102a06f7e55688815037deaa34440a819ff64da220540dfbc66d1102a057febb648815033fed3b2440a81d7f9dd9220540aff96ac9102a067fda564881503bbf2ab2440a81def5519220540cffb46c9102a077de33648815033fed132440a813ff6e97220540affb72b9102a067fda95c8815036fed3ae440a81bef69172205409ffb74a9102a057fdb9548815033fed4aa440a8177f2dd5220540dbfb4ea9102a06f7da5548815037ded22a440a81bfb68952205409ffb7429102a057fdb9148815033fed48a440a81b7f69c5220540bdfb6c29102a05fbdb4148815037ded20a440a813ff6e93220540affb7299102a067fda94c8815036fed3a6440a81bef6913220540dfbb4699102a06feda24c8815037f6d3c4440a81dfb65e2220540fbdcef11102a06feda588881503bf6cac4440a81fdb9562220540ff5a)) else (if i < 6 then (if i < 5 then 0xf6959120940eefcaac8904a067fda364482503bef19b22412819ff68591209409ffb74a8904a057fdb9544825033fed4aa241281bdf6955120940dfeb42a8904a05fbebb50482502fdedaa8241281bef6954120940fe7caaa0904a06fbda350482503fcf19a8241281bef68541209409ffb7498904a057fdb94c4825033fed4a6241281bf768d3120940dfeb4298904a07fb5414c4825037fad2c2241281dfd6561120940feecab08904a07fb554844825037fad1c2241281dfd64e1120940ffac6708904a067fda9844825037fad0c2241281dfd6461120940ff6a8308904a05ffabb4c0825037fcdd26041281bfe6953020940fef4aa98104a07fb9544c082503feca9a6041281bfe6853020940ff728298104a07fd9314c082503ff908a60412813ffaeda814940cffb72d40a4a04ffcb16a052502bff5db30292819ff6a19814940aff962cc0a4a067fda9a20525035fed451029281cff66288149409ffd76d30a4a067fd98698525035ff4434c29281bbfaeda614940ddfb70d30a4a06efcb86985250377f4434c29281bbf6cda614940ddfb62d30a4a06efcb169852502bff5db2c292819ff6a19614940e7fd10cb0a4a04ffdba61852502bfedcb0c292819ff6a58614940ddfb4cc30a4a06efda899852503b7ecc4cc29281ebfa226614940df7d10d20a4a06fbd86690525027ff5db46292819ff6e5a3149409ff970d18a4a067fd9868c525035ff44346292819ff659a314940ddfcccd18a4a04ffcb168c52502bff5db26292815ff2e19314940cffb50c98a4a073fe8864c525033fed332629281dbf9999314940aff962c98a4a04ffdba60c52502bfedcb06292819ff6a58314940d7fb50c18a4a06efda660c525037ded230629281bf768d83149409ffb74b18a4a057fdb958c525033fed4ac629281bbf6996314940edfb2cb18a4a06fbda458c525037eed446629281df76623314940f7bd11198a4a06fdda68cc52503beecb46629281fb799a33149409ffd76d08a4a067fdb9684525027fe5c342292819ff661a114940d7fd10d08a4a067fd966845250377f3334229281bef6d1a114940cffb26d08a4a06fde3368452502bff5db22292815ff2e19114940cffb50c88a4a073fe88644525033fed332229281dbf9999114940cffb46c88a4a077de33644525033fed0b22292813ff6e98114940affb72c08a4a067fda9604525035fed4302292817bf2d98114940ddfb4cc08a4a06fbda4604525037fad0b02292813ff6e96114940affb72b08a4a067fda95845250377ed32c229281bef6916114940bf7d76a08a4a06fbda850452503bdecc28229281eefa214114940df7b4ca08a4a077bd9650452503f5f3328229281bef68d4114940ff3c66a08a4a06fbda1504525027fedd262292815ff6e53114940cffb52988a4a06efda64c45 else 0x842a07ff9854c0215037eed934642a81bf76c5a321540affd76c990aa057fcb264c85502bfe58b2642a813ffaeda221540cffb72d110aa067fd93688855037ef19b4442a813ff2c5a221540dfdd76d110aa06fedb3688855037f6d8b4442a81bfb2c5a221540affd76c910aa067fda364885503bef19b2442a819ff6899221540aff962c910aa04ffdba4c885502bfedca6442a819ff6a53221540dbfb4e9910aa06efda64c8855037ded226442a81bf768d3221540dfdb449910aa06feda388885503bf6c9c4442a81ff38ce2221540cffb531110aa06dfda78888550377ed344442a81bef6922221540dfbb471110aa06feda288885503bf6c944442a813ffaeda121540cffb72d090aa06fbdb4684855033fec9b4242a81bf78cda1215409ff964d090aa067fd92684855037f71134242a81bfdaeda121540dfeb66d090aa06ff5b2684855037fa5934242a81bfd4c9a121540dfec44d090aa057febb644855033fed1b2242a81df78cd9121540aff964c890aa067fda264485503bf71132242a819ff6859121540bf7d76a090aa06fbda350485503fcf19a8242a81bef6894121540ef7b24a090aa07fae22504855037ded0a8242a813ff6e93121540affb729890aa067fda94c4855036fed3a6242a81bbf6993121540df7b489890aa06fdda34c4855037f6d126242a81bfd6853121540ff6a829890aa04ffdba48485502bfedca4242a819ff6a52121540dbfb4e9090aa06efda6484855037ded224242a81bf768d2121540dfdb449090aa06ff5a1484855037fad1c2242a81dfd64e1121540ffac670890aa06ff5a284485503bfac942242a81ff988a1121540cffb530890aa06dfda78448550377ed342242a81bef6921121540dfbb470890aa06feda2844855037fad0c2242a81dfd6461121540ff6a830890aa06ff932680855037fd1134042a81bfe4c5a021540dff242d010aa06ffa1168085502ffd5da6042a81bfe6e93021540dff3449810aa077f9924c085503ff51126042a81bfe6853021540ff72829810aa07fd9314c085503ff908a6042a813ffaeda520940cffb72d2904a04ffcb169482502bff5db2a412819ff6959520940aff962ca904a067fda9954825037bed2caa41281ddf6565520940bf7d76aa104a06fbda555082503f9f2aaa8412819ff655a320940defcaad1904a06fbd5468c82502bff5db26412815ff2d59320940cffb4ac9904a0777e5564c82502bfe58b26412813ff6e95320940affb72a9904a067fda954c825037bed2aa641281fcf5515320940dfbb46a9904a06fdda58cc82503beecac6641281fd79563320940ff3aa919904a04ffebb684825033fedcb42412813ff2d5a120940cffb2ad0904a06f7e55684825037deaa342412819ff64da120940dfbc66d0904a057febb64482502bfe5ab22412819f) else (if i < 7 then 0xbfec9b0229281bff6a16114940dffb46b08a4a07fbd8650452503fdec1a8229281fef58d4114940bff970988a4a06ffda84c452503bfecc26229281bff6993114940effb2c988a4a07fdd634c4525037fed442229281bff68e1114940fff30c980a4a07ff9814c0525037febab4640a81bff955a320540bffd76b9902a06ffdba5cc81502ffedaae640a81bff6957320540effb2ab9902a07fbd545cc81503bfec92e640a81bff69d5320540effb2ea9902a07fdd7354c81502ffe592a640a81bff6d5a220540dffaead1102a06ffe55688815037fed9b4440a81bff5cda220540dffaa6d1102a077fd5364881502ffedaae440a81bff6957220540effb2ab9102a07fbd545c8815037fed1ae440a81dff64d7220540fbfae6b9102a06ffda754881503bfecbaa440a81bff68d5220540effb26a9102a06ffda254881503ff6b92a440a817ff6cc5220540dffb4629102a05ffebb4c8815037fedd26440a817ff6dd3220540dffb4e99102a077fd974c881502ffedaa6440a817ff2d53220540dffb4a99102a077fd954c881503fdeaa26440a81ff75cd3220540dffb4499102a05ffcb5888815037fed2c4440a81dff6562220540ff7aa911102a06ffda388881503ffcb926040a81ffe5493020540dffb66d40a2a06ffdb26a051503bfe5933028a817ff2ca8814540dffb70d18a2a06ffe8868c515037fed934628a817ffaed8314540dffb74c18a2a06ffda860c51502ffe5930628a81bff6e1a214540dffd10d10a2a06ffdb3688515037fec1b4428a81dff60d9214540bffd76c10a2a06ffdba608515037fed430428a81bff68d8214540effb26c10a2a07bfd83608515037fed130428a817ff6cc8214540dffb46410a2a05ffebb4c8515037fedd26428a817ff6e13214540bff970990a2a06ffda84c851503bfecc26428a81bff6893214540ffdb04990a2a05ffcb8888515037fed444428a81dff6622214540dffb47110a2a077fd9388851503ffd4426028a81ffe6093014540fff104980a2a07ffa224c0515037fedab5010a81bff6cda808540bff96b44042a06ffda5a2021503bff4432a10a817ffaed8508540dffb74c2842a077fdb9614215037fed430a10a81dff6618508540dffb4ac2842a077fd9561421502ffed990a10a817ff2e25508540dffb512a842a07fbe8855021503fdec2aa810a81bff6e1a308540dffd10d1842a06ffdb568c215037fec2b4610a81bff215a308540dffcaad1842a077fd8564c21502fff5db0610a81bff6e98308540dffb50c1842a077fd9860c21502ffe5ab0610a81bff6958308540effb2ac1842a07fbd5460c21502fff5daa610a81bff6e95308540bffb70a9842a05ffcb854c215037fed42a610a81dff6615308540dffb4aa9842a077fd9554c21503fbec2aa610a81fef5515308540ffbb06a9 else 0x31bd31b971b5b1b141ad81a9c1a8c1a5b1a2a19f919c819971966191f18ee18a71876182f17f317c2177b176b172416dd16cd1686163f15f815e815d815c81597158715771567155715471516150614f614e614c0149a148a1443141d140d13fd13ed13c71396136513551319130912f912d312c312b3126112511241123111ea11c4119e11781168112c111c10eb10c510b510a510951085105f104f0ffd0fed0fc70fa10f7b0f550f450f350eee0ede0ead0e9d0e8d0e720e620e520e0b0dfb0dd50daf0d890d790d480d380d070cf70ce70cc10c9b0c8b0c7b0c6b0c5b0c4b0c250bff0bef0bc90ba30b720b620b310b210b110aeb0aa40a7e0a370a1109eb09ba097e09580927091708db089f086308320822081207ec07c607a0077a0754072e071e070e06dd06ac067b064a062405f305b705910560053a050904d804c8048c0450041403d803c8039703870361033b031502ef02df029802720236021001df01a3017d0141013100f500b9007d004100310000dffb66d110aa06ffdb168885502fff5da6442a81bff6e93221540dffb449910aa077fd924c885502ffe58a6442a81bff68e2221540bff9631110aa06ffda1888855037fe9934242a81dff4c99121540effc44c890aa07fbd3250485503fdf1128242a817ffaed3121540dffb749890aa05ffcb24c4855037fed126242a81dff6493121540ffba649890aa06ffda14c485503bfec8a6242a81fef5053121540bffd769090aa06ffdba48485503bfedca4242a817ff6cd2121540dffb469090aa077fd93484855037fed124242a81dff6492121540dffb429090aa077fd9148485503fdea0a4242a81ffd4c52121540dffb470890aa05ffcb2844855037fed142242a81ffe4853021540dffcaad1904a05ffcb154c825037ff2ab4241281bff54da120940effaa6c8904a06ffda354482503bfec9aa241281fef54d4120940bff96a98904a06ffda54c482503bfecaa6241281fef5513120940dffb4b08904a077fd9584482503fdeaa42241281bff68e1120940effb2708904a07ffa554c082503ffca8a6041281ffe8453020940dffb6cd40a4a06ffdb36a0525037fed8b50292817ff2c68814940effb26c30a4a05ffdb1618525037fedc34629281bffa21a314940dffb6cd18a4a06ffd8668c525037fed8b46292817ffaed8314940dffb74c18a4a06ffda860c525037fed330629281dff6598314940bffb62c18a4a05ffcb160c52502fff5dac629281bff6e96314940bffb70b18a4a06ffda858c52503bfecc2c629281fbf6196314940ffbb06b18a4a05ffdb158c525037ff4434229281bff619a114940dffb06d08a4a06ffd6368452503bfec332229281dff60d9114940effac6c88a4a06ffda8604525037fed330229281dff6598114940f7fb0cc08a4a06ffda360452503))) else (if i < 12 then (if i < 10 then (if i < 9 then 0xb68ba6873685868486817680767c067b067a067646754672e671e66ed66d266c2668666556645661465d865c865976566652a651a64e964b864a86498647d646d645d6442642763f663d063c06379636963436333630d62dc62cc629062806239622961f861e861a161866155610e60dd60ac60866076605060145fee5fbd5f8c5f5b5f2a5ef95ede5ead5e715e615e305dff5def5da85d8d5d675d2b5cfa5cea5ca35c935c6d5c475c215c115c015bf15bd65bbb5bab5b9b5b8b5b7b5b4a5b195add5acd5abd5aad5a9d5a775a515a155a0559df59cf599e5962593c592c58fb58ca589958685842581157eb57ba578957635732572256fc56ec56b0567456595628561855e755b6558555545539551e550354d254a1549154815450541453f953d3539753875361535152ff52ef52a852985267522b51fa51df51cf51a95199518951635132512250fc50cb50bb508a50595049500d4fe74fd74fb14f8b4f7b4f604f454f354f1a4f0a4eef4eb34e8d4e5c4e4c4e3c4dea4dda4d934d6d4d5d4d214cf04cd54cc54c894c794c484c174bfc4bd64ba54b744b434b124ae14aa54a744a434a334a0d49e749ab4985495f492e48f248c1489b486a482e47fd47cc47bc47804770474a4724470946ee46d346c346b346a34693468346734663463245eb45ba45aa459a458a4564453e452e44fd44ed44b1448b44704434442443e843cd43bd43974371436143304320431042d44298427d426d42314221421141ca41ba41894179416941384112410240f240c140b1409640864060404540353fee3fde3f8c3f7c3f403f303ef43ee43ea83e8d3e673e2b3def3dc93d983d723d413d1b3cea3cb93c933c623c263c163c063bd53bc53bb53ba53b953b853b753b4f3b293b193b093af93ad33a8c3a503a4039f939bd39ad3971394b393b38ff38ce38a83877383b3815380537d43798377d3741370536d436a33693367836683642361135e035ba35733542350634f634af349f346e343d340c33db33aa3384335e332d330732cb329a32743243321d31ec31c631a03159312830f730c6309530853075306530292ff82fc72f962f652f552f242ef32eb72e7b2e602e242df32de32dbd2dad2d872d6c2d5c2d202d102d002cc42cb42c8e2c682c422c1c2bf62bc52b9f2b792b5e2b382b122ad62ac62a952a852a752a442a342a0329d229c22991296b29452914290428de28ad287c286c283b281527ef27be27ae277d27572747272c2711270126e626cb26b02674264e262825f725d125ab259b2575254f250824f824c724b7247b2455242423dd23962386233f22f822e822a122912260222f221f21ee21b2216b213a212a20e3209c208c204520091ff91fc81f971f661f351f041ed31e971e5b1e141de31d9c1d6b1d5b1d141ccd1cbd1c761c2f1bf31be else 0x404123200573203d8412b8e991104748015869590104a084348017069590104b48017069590104b48017069590104b48017069590104a08420b834ac80824aa27aa0ca9e6a9cba9b0a995a985a954a944a934a919a8fea8e3a8c8a8ada892a882a872a857a831a821a811a7f6a7d0a7b5a7a5a795a76fa754a739a71ea70ea6fea6eea6dea6c3a692a682a65ca641a610a600a5cfa5b4a599a573a558a532a522a507a4eca4c6a4a0a47aa454a42ea408a3eda3c7a3aca391a376a35ba34ba33ba32ba310a2dfa2b9a293a278a252a237a21ca1f6a1d0a1c0a1b0a195a185a15fa144a129a10ea0f3a0e3a0bda0a2a092a077a051a036a0109fea9fda9fca9fba9f949f799f539f2d9f129ef79ed19ec19e9b9e6a9e399e089ded9dbc9d8b9d7b9d609d3a9d099cee9cde9cce9ca89c829c679c579c319c009be59bd59baf9b899b589b3d9b0c9ae69ac09ab09a959a6f9a549a2e9a1e9a0399f399e399b29997997199619946992b990598ea98c4989e9878986898589848982d9812980297e797d797bc97a1978697559745971f970496e996ce96be96a3967296579631961695fb95eb95d095aa958f957f95649549952e951394f894dd94c294a79481945b9435941a93f493e493d493b9939e938393739358933d930c92e692cb92a59295927a925f924492349224920991ee91de91ce91b391a3919391839168915891329117910790ec90bb9095907a905f902e90138fed8fd28fb78f918f818f668f4b8f308f158f058edf8ecf8eb48e8e8e7e8e588e3d8e178e078dec8dbb8d8a8d4e8d3e8d2e8cf28ccc8c9b8c8b8c7b8c3f8c038bc78b968b5a8b298b0e8ae88ad88a9c8a6b8a5b8a2a89f989e989b8897c896c895c8941891088d488988867882b87ef87d487a3877d875787268716870686eb86db86aa866e8632860185c5857e854d851c850184f1849484848453843883fc83e1839a83698359833382f782c682b6828582548244821381d7819b816a812e80fd80cc809b806a803980087fcc7f907f807f707f557f457f357f257ee97ead7e717e357df97dbd7d8c7d7c7d6c7d3b7cff7cce7c9d7c617c517c0a7bd97b927b827b517b157aef7adf7aae7a887a787a3c7a0b79fb79bf79af799f798f797479647928791878d1788a787a783e782e781e77e277b177a17770773f770e76fe76e376d376b876877661765175f475e475927535752574e974d9749274827446742b73fa73b37382735c732b72fa72ea72ae72727262721b720071e571a9716d715d712c70fb70d570c570b570a570957085707570657029701970096ff96fe96fb86f666f566f1a6ee96e976e5b6e2a6e1a6dc86da26d926d566d1a6d0a6cce6cbe6cae6c7d6c416c266bf56bc46b9e6b576b266af56ac46a886a4c6a316a0069cf699e696d695d6942692768e) else (if i < 11 then 0x13904d59e80fc19159002e9e93543c832338e9ab3d219100c856af2019215d7a03232d5e403642baf4064603215aa9a06c8575e80c8dc816aaf407e0c8a2182b557a23244645aa3257a23225865aabd119117a2d563488c96196aaf4464405b3567a43224d5e401327a0322cd56401367a0322b2005d3d26a879064671d3567a43227209aa07c2bcf4064670d3567a43220190d1ce40b542baf40646a39c816a8575e80c8c0643471342d50aebd0191a8e7205aa15d7a03232d5e401317a032281908190d1ca42b557a0322d1ca42b557a0322868a334716aaf40646a394856aaf406455ab48026af4064510415aabd11922325825aabd11912c12d55e88c88b557a2324464b04b557a23225825aabd11911900059e93543c832338e9ab3d219126af201b215e7a03233869ab3d219108e7209aa15e7a032311c6433567a0322b829ab3d21912902d50d215d7a03230210d205aa1a42baf40646a34bd034ad50881a0c08421a16a8690aebd0191a902d50d215d7a03235205aa1a42baf40646052100410321e30bd164223201908190821081908190f185e8b21119010840c840c85642324463179322190c1b8421f200de3de6403230f59910c8606420dc20642b21192231ca999146a119254cc8a3508c80643480222c80f20c8a0642084363964232182108190f200154847bac81bc0c8e064206420642036908f75903781919642324463172b21190d6423244630421a401a4222c8064504210d21116403220cb9bf10461242064212420642b7d20a2318190d32e401ae90adf1b2104e0642b7d10a4118d95be904737e20c231cdf8431046064206434c836d215be36420980c842b8680f61048064208421a1208810840c8465f201b2b7c2904130190adf48288c63256fa411adf48288c608421a02b869082404210d215c34041201908190ad5442904735620c23181908210821081908190ad54429046b5520a23182108695aa10463da644411f209901f020900c87902c80f81048064237c2b2120a231bdfe400b990cc808267bf322208deff2005cc866404133df99110460b6644411f200d7320209002f200e53202095efcc888236401b66404120190f20a65485640412f20a65485640412f20a65485640412f200d6b2020900c845485642214823b52b21208ed4ac84823b52b21208e644418463991086208c0c840c869952159010494ca90ac80824a654856404125200dab202090494c8882305d3203d84123df04a0ba640412bdf9911046cc812cc80824753322208d9902599010480b834cc808240321a400b96407b0825a400b96407b0825a400b96407b0825a400b96407b0825032105cb203d84120210d8e5909047639642411d8e59090476396424118210bdfe400ad90cc808267bf322208f901326433202095d4cc88823264c866 else 0x5d704641218af86902d50821c49a08241821cc34ad548242428703e8c10841084348735aa9049c683a08908b4107904321bc31b00fc437c2f7f904890df354209b8d059107164009a44cd50827e3412321c76a83f04a52be1e4002d6a8410e25d0410d2c816a92307e5d044844ae06c0281873e400756aa412e820164643e8252ad544290461cc142d548245aaae1118c0e8735aa90487212087119191d43781292e42214821c4837911871181d0d2b5520908ce820e216c1f9410841084348285aa9049c683a083a083c683a083a0828c9118de1a3244637862243a08248c2090208341805a441ce902d50826a41ae09087c04a5e30100b488135205aa104d48090ed507e094bc603c8034cc81ed104b2187b07c18a90f200d33207b4412f200e732220926471a08830e61a664441251a232113640252a861ec1f064a42b2110a410e24e401a5640f64825d0477c5c8034cc87bf104bc8034cc87bf104a0b78d0720884e413203584420df08720882e3416341c8220c16f1a0e41109c82644410e44991c68220deff200d33222087233209911043913646b82324c81294af857b073a654856404136820a822641ac2213902c84821c88464226c804a40e2b2110a4127200e6b212093902c84823e40b21208f902c84821c88b209904419dfd90484990442ac844287022116471a088319277f8d04422c8e34110677f6471a0884591c68220d6471a08833bfb208c844634094c77f6471a08843beb238d04421dfd91c682210efec86341109c683a083a0821c564221438110bc806c71a0884e403638d04427201b1c682210d4f1a0e411084c8332210c410e240e332210c4124b89910868d034287184236220834293223220e74ca90ac80825d9046422025251a0d1a0e40d066a423422082518240f221be12434825c4c804a5e34115212434825c4c804a5e341990104128c4906904a31a1104128c34cc88823991104128c34cc87bf10481a6644411cc8e341107322208a6471a08831b1c68220c9107b0884641214af8439ac80381e49a0824a421ca902c80884d0410e61a56424126822321ec221010843986959090481a564241186959090461c834ac8482404210d2b21208e902c84821c89a088c8570f2404210e61a564241206959090461a5642411d205909043910108490a41d9009481a5642411f1a0e822422a41a085c683a08908a90682131a2422e401a6640f68825e41322208e6451a0883e403628d044206999110461a66444119230f180480d06b20208691d200d3b235c1210686e3015714816403427180b18d90484220252ec80881a460d66acf486446353d03ccd50881a0c1a26a8690af3d019180c869002e5e8b543c832351a5e81e56a8440d060321a34bd03cad50881a0c08436396aaf44644b1cb557a232202108d89ab3d219)) else (if i < 14 then (if i < 13 then 0x8215241c4052d51bc48cda189089430892380f49c6839fb6e40b540f9b4311907a1f083791922103e40e6b540f8cdb056a8f703e3635ed96aa2103e50e6b540f8c5bf1a03e11085d49094109a44328c80f84420b746407c22110cb1a08807c84708c8806ac8a341c481c7640442420d0b46834681e8b908841bc5dc9083421b80871b054696403d2466a3448454681701f1f1af6d4816a81f2e8623215c3c9010845e71aa403dd6a81f302108695aa07c74816a81f1ec82420f47c683a183a1822e78d0b4313911410f1a0e860e860a3243207c2212c171a03e11088c90c88903e094a2243a182608248c3c60138341ac80641a474802187c2420d0bc602b22900441b4008445914801a118c6c80884841a17640440d23e3011963262085720cb1931042b9064f1a0e415c937c6cf1a08840d11046c8e6f8cb1b3104937e208571919de8564129016f1a0e41109c802b87a1f188d056422138d058d072088310c10afae08c93204a578bed9340d90ae578ba084a089902d0e4420c1193c68390572119de856412910ca1c0e415c83250e0720ae41b3c685a08ac89e2e82121c4321c82212d4f1a0e41109c683a0830668d0570e448390668d072068526446454686c85719d5233ae0ac82529d50d1a05c1c874682486343c57aaf227a0253f1a09218d1f1435cf404a6e3412401b42082521220ae4643c8242bc50821ec2b91e2e82112908570d01107a08241821a1208d919198d052422101084342411b23242904ac82520210fc5a409043913411190ae1e48084215e900d94821c8b4815c072182109210f409461a15c0721f1a0e82242278ba085c683a08908b41058d12114df8d01a78d0de2cdf1960fc71a18d0de2b24e341152191337d99468b901ac209f8d07e2b209becc836841307b0381e47c683b7c8c85707e094a9a06f0c90ae478ba0844a43c802b80b0e2110ba08215c8c84404a44d01489183f268224225be32c1f8d6f8cb1b290484677a15904a45bf72110a4122df39036520916fb1a4463789f179001d4821c8bb7c2b92307e4f8a9051087221c50ab81b21c860a15c0721b1af8aae110872281d5701c867210e04419c82424c822116fdc8442870221464adfe3411087238d044191926437812916f8de442c681a17e281d0d09049a088c87b088404211960a06c868482504210501a1208c0e8684823193c685a08a489e2e82171a0e820e820b1a0f1a0e820e820adf43888c6f116fa680d23678d0de32df63488c6f104487410491841204106835701a02b8da9842bab80d00d09c602c602b921088094a15c2206918410d22a401489083f0685e3011d5f17904410e251ec1f0421824643e8251ad51ec1cc64183f1510a410e24e341d041a35f165c4230e2506bf17db43204a50481a4437c2486900690821f0bc682218248838ed else 0x57a2322f1aa40b557a01f2ed5de848519138d7205aabd00f976fed52421108b557a2324464e40b557a23227205aabd119116aaf446488c89a16aaf44644e400756aaf44645e35c816aaf403e5e341d521641c685c683aa43c682b7fe2a21464110ab56c1268e34110b60be2a68e34110bf150c8f6464094b60be2a68e34110b60be2a68e34110a60b8d01f0884238130410d33567a43227200d33d2190d82cd50d33d21913904d59e90c88e0be2c68a34110a48c3f17db069e304881a196aaf40641a494836a8430d24841a1b8c056a8440d00d08c636a8442420d0bb54220691f1808d8e341c43913900d80f431041d91bd0909320e4550c4c86c07a21020da9e30864390442f1a0e86091908d80e42a3410d73d2644682465e3416353227a06d0d048cc48b646f40e2464139894868d0145e8b203897430481078d2f4a40b20391435ec82461e480842bd2902c80e44de9b209087220685e8b2039138d0490e8616860b1a2422e3537c6f01f24681960f462a42ccb9001f912c68394c89e88e34164007d9906d9e93218d1d9107103f2258d4f49901a11c683b203892128207ca4a43c828d00a5e8b20389b4304052f45909a0919490e8612861124701e938d720590bd03901f306bd904841e910c84403e3590bd00f87222c85e81c80f908c868d6c80f44840f957a00d59146838968d068d2c85e803434123351a24221ec07c5c69645205e807ca467640718d00f4a08421a1642f403e4590bd03401f26c82420f47c683a183a182c683c683a183a183c62c121903e110a2243a182608248c209f8c12206840d34883951a5e8b20341f8c058c6f40dbb209197646f40e41a481a69101fa34bd1640683b18de8037641232ec8de81a40f938c04757b6e401a66471a0e271f01c43e0c41048c843d0c1f01a17db07150c3a83e148107db2c84428c838978d0743045e71a1ea11096db904c81ea110a3d78d085e71a1ea1109c82644321ee4e34378220f900699903df8d07133209910c87b905bf1a03e11083de6471a0884d905d4909410685e41469641770e25d0c5d45c81642321ee4d0c5d49085722c8be88c91193902c84643dc9c683a1adb0adb68617b69910868d0712bf49910ca11904971a0e7eda6a82730270f221be1f6d2189187c271a0c927e8dd66a8de2466e34110412441ec8c84404e52be10f20c83d8f4305643400f21108edb4308810439fb60d2b211917431190f6110808421cc34ac846440e61a47bac8464504210d21cd6423225205908c87b934311926e1a42b941086902c84643dc9b21191232ee40421e341d0c4845a183c683a189089db6861089e3407c22104a85707a31be1e31c80224860d815cdc682504bb8571f1a088905c07c6112433200ae4e3410e3b209094103e52be1f6dc800551a5901c4da182ed8a08f707a42) else (if i < 15 then 0x90e862ea303e13041e35a1842dc21a78d6861869e342d0c4845480398adb686101f0bdfe341c461138d0b8d0422141103d283a187a189088a08bc24233e81cd190c7b84bb845e0439f1a03e3d0c1104112dc01f181fe341106112190890c32103d864484677c3c683481f1e86a400b890938d03d0882e485049c8bc242476c0f440bac101fe344b05c680f82e2432084403e20e5c682b8dd4f1a05d1a09c6b410864843906e2857e343b8ba08908d0e12110520f1a0ae3646757411212b2478ba0846183c680e8cb1f1a0ae1c86ea41771a0e4403a254432c34854e344e341a4390c1726824230e410afc68415ee46821b1a0ae2b900a38d0c3d859002810d909590a68051c6839134105711c803a870632c225417084a82e1095e35a0860744a881471ad043e3432c648c90e8229230e413521e341d0448444850e0865840ea1c11a90d86e342b0da0856190e0ac371a4d01a490703c602b8691873e3420e7c685a088c88c3078d06913dfa41c6834904a869171a2d1a0861a78d0839a1c1186081de3427be1c78d0c0e895171a0e822422e35a0840778d0839a1c10280d22051a084c8341080ea1c107112ba0876184a8691895e35a0860744a881471ad0433be1e341d0448440750e0a9068211df0d86e342b0da0856199071a0d2405161b410defc1c168205148070702e1a0e0839f1a1073e34235210e417bfa085c6b41083907410439a1c121c08720a1c0f1a05c23be1b520bb8d0defc1c141c0f1a0d22a40f7f8d0692025e341a474838d0b8d02e13a9a41c68171017682171a2d1a0861a78d0839a1c152024287066a43c68390b4112111214382e35a0841c821a78d68219df08730d22d040b8908c3906901214383a401a440b890a1c1e820f180d220d33567a43224d50d33d2191091119daa1e41a1483048107900699e9c686c166f8d807e305135419079271a08820f200d33d38d0d8281d0d33567a4322f2003b3567a4322cdf9abc6822128d6d5de84841a157a2d54d048c9aa490896f8d807e3204103a1a56aaf44645d524643d844202108695aabd1191034ad55e88c8808421a56aaf4464403a1a56aaf44645e341d521641c684bd1190d84464e401a57a71a1b05e401a57a71a1b055e8c686c22322680d2bd38d0d82f200d2bd38d0d82ea930c205bc680f84424680ae0f46c680f844181f9aa1a022138d0443040f844171a082de3407c22138d3209ab3d00f978d7209ab3d00f966fbc8e34110807c34cd59e90c8bc6b900699e83600f9b6a9212820d08bd16aa682464d52484441820a28e2d8e40b542baf40648d521a340b48e03d211c2322a34bd16a8682465a3448440a16ad21a38bd0191b6a8442420d0946834680f8341f1aa40b557a01f2ea923215c3c9010856a8695e88c88b5434af4464404215aa1a57a23220285aa1a else 0xef1a101de342d523978d0c0ef1a101d46422431a046083c6ac32680d24304103e1e3407c5aa49089c36a91121864270d0c85aa78d080f84c3041406916a905c4847c68207c24851908171214643d53c68407c3aa43aa434f1a1f1a4d0205daa44075190919040f8519041685900691582e349a01710c306c102ee343e301a44ea78d0718d0430417521c78d072271a0e42243a1849a38d01f181fd0c2d0c4868d0cd4878d01f1121d0c2d0c4858d0ec101fe34303f60b430c0fe862383e35609340c0fd82d0c37531a05a1a8d01f1b828d020e7c6841cf8d0839f1a11820879081f0f1a0d227bf4838d069271a1241a46fd039f1a18950d22e345a3430c34f1a1073464276dc687a8c))))
def lev11 : Packing := (1180,4,7,0,0,16,0,data11)
def hash11 (i : Nat) : Nat := (if i < 1 then 0x4002cc408f613635b2ac4807f0005c8eec001a3000718000000000014bbda5ce23d3d9988c28c9169517f9150f0864770fecfd98a0000013403c4721ed1ab37830838429be1f3148c2b2126e84dd42b6880525a20c36711044ca6d368d2db3b634380d9083d442a4ee1d3e11167249ab55902bd58b93e6b8b652148a81e4f049c111d40c8e5162596955de0c2850bf51583e2060b8fb32554e00053c010500000016c0010391f0001e6001648005440003700015cebe18a192e50ac7b1b37f0f289b35e39e990162db4be8f0848088c68a0004005e2e048580000000183a221505b4d88ce1b6e604a91870c356214265a6f4d2230016c5dc568c04e0ac5f78d7436e41f528e1d0599d488d8badc1bcba00005fa1c82d3ea0013a8003d4258480000004c563b4a3fe001898001467dd95adc3aad0542c3c8d27a0bb000000f14000ab81403cad90576aad1762250bc3f4000004c2c40852b393493c6825757aab09ea1d3b08bc7280052a000a917a3b2978d43e98e4000000002bad5217a148b8f7d8f05f7fd1d9cd97b520a094011a6691e50b00106e156049b8000002082d80000017d45816a7e9a82600011f95a8c648e6510194146e000002070007203eaa689718a2daf20724561193367677935c9987a1e9fa37b0ad210060004e51f15c218838d68a412d606b41d8979028b3813a0c7909c5c48b376c07d5fadf29ce94d330b691054acac11746b876c8253cc89dc8000012002e8819068852b3ab910a900032604b0c0e637c1ea440811691cc989bf0004c63100007c4829680000660abfcf5ac868a20890400e49028a47aad1b3a4023002000082f020540b2f11018d9461e0002ab56300c001101125a2250c834380d02894160b2583874660181c0002000cc0abc001c80a80000080010000904814053100635639e4683f0580000020480292030b07c120702004063f0b844022c0007806ac02094300502d343a000105c12110081016210c8180e0c029e44606050040a0306804000203800000b2e89cc0211380d2e00008b020030000018090301016b0494e4420500034c406010001e0513800000b1303ce61e01020401a4f854040a179184c110801406004a8102ea02a80054200b80c02310512c00000301000091301094060101804af028002a010001018001600408000d8140034020b41ab70000814000101c4200018a046010000008001c82416230516432028b83000d7000841a5a0001404010000810004e01c64000003c14125880c0c01061555c0e0080808dc0200014150200400000e0003e0d1f00402070000800040d80c043200020001302800000c060280404068200000008042c000401020051305802000301016020801010020580c0805038001000010080e000b81404010200402000004802010a0105c08010543a11 else (if i < 2 then 0x190e18be122950c9a277bcf6cbe23d5ba039e1b421b875c2c9575163699f82169cb8dc2b0f022d9066c2d1f6568508383bada08bc507b90d632c913f83c8a696a2a0ba0589ee26004dba0235ee230f03123a22fdbbacd920305fcade2685c02a3a27dcb3d0912e64e449e719975cd021b07134e289728a40371bcd0c3835ada4763d660856107be028652cd83e258ca7dac0006547c4004771b28d002c670002b0002c52d11e00914f5c0109983b40004a000000044aa1ca2663441a00025900000de1125000000f21916f40004d175000000efb9e21e1b4a60e20002997a33946c6f4d03d53e4f9c00108584c8125c515c42e00a800001085601f061092000316000a3c0011e01220070004476125370656d849dccbb0302000698240948a6090204006a8e9b9156e8e1501cb10506a12a9171e6e40e1112e90904f382524768cd1472a68450412c6508a803b536780c1f341f7ba1c9ff87f8e2badf6bf1518cd80b32319526c4325b2c0db5fd28878e0d5bf8927969f8278615522e4ff13f90a9bc3b1a54f91f41d8f03de49a039ac0b64e454c6b2363dd79b016a27094b31a1e90d031033774ef92540c196ac1b2b6e7c6035833803766723d40b2389a511c4d2bd115d2052254dae069168110b9f28781e2918c913273ace9032aa508a4dd185c36c5c4233f30e821d78359492d181a3717064ad3c8d68aa4906496f03c88126c6041647cc780b912a7015a02141125dba50662100e092f17a994e746e18ee68228842a89322430a6982618e09d8d03fdd3a0a2dd235fba879190f99f3aa5f31984e281926974cf9cd48aecd6a0d81150a8832e990f0b12c1214a6cb8300944fac64f19466c0e4d1604b69a8e8c02178051fd730af62317dcf88841a5962735672ca0d183cd84071c21c435ac8797702a864d3ccb167718a85621b22283e8b98b44480fd9ebcf5f619e222a36de15ca2c4c89ef31fac19190799593573c42c8a01238f618d4c8c55ed0dc39abb0d3074c4907284ef4afbc95fd1a8bc2ea1611d1a38de16ef014c03d3fa4e20d9d236e9d87c2ef3b85ac2089757c939b98bc45c068c3aed90c55417afc55ed260f11974d05cc30e491d16a022ca77e99c7194440a6201d09f1d66091f8835f05f5eb86f0a6d84fc42265aa6a02bd936a345fe8501bef106ec96710d8889be837f1b0709045363482619d318c6c0835d0007b07481d806144380aa32076c949e92947b6031d00006392e10c08ec34870771a8dd5e928a8e6701978cf71a000003434fe239849af352001c900a030679d90a50000000041354a00144a406a40088ebeb0009dc00000000e380047000111c0031f1f8435b91f35a2948e20001de000d5b8b4a317999000176001354272fe62df82ba2c86540c8006fa5856d07961c9e9f605a000000c6800000714d21d4000ca else 0xfc0022c80024505214c9409b22cdd3140eb23e4aae10004003323192525dcab5f062f9066017000f44c1b157e4c30001bc4e61ac7389b1127950082632e9d1b504e0d861229a26742d9956a1a82c000220007ecab880800714000001e70d515c003356671d5bb4463e887cb1c9858600000209466f05ce0000009e0eb39709090d8eabc658c616ba8678cde01480051b0fc002d5336e122b0007a0c91690000005721d800000ae54ebad0003ba36aab894c0a19bac5284e8fcb870b1))
def idx11 (h : Nat) : Option (Nat × Nat) := let a := h % 393
  let sh := packedAt hash11 (a*9) 9
  some (packedAt hash11 (3537+((h/393+sh)%1305)*11) 11,0)
def data10 (i : Nat) : Nat := (if i < 13 then (if i < 6 then (if i < 3 then (if i < 1 then 0xc5fdb969d5308540c6fdb96995308540c77db96955308540af3dc46955308540cf3dba5515308540eb3da85515308540ed3da75515308540ee3da65515308540c7ddb968d5308540ef1d5468d5308540a7ddc96a23308540abdecc6a23308540e3ddc96a23308540e3dda86623308540abddcaa223308540e3dda9a223308540eb9da4a223308540e5dd9869e3308540e9de8869e3308540e6dd9869a3308540eade8869a3308540a7ddc96963308540af9dc46963308540af5ecc6963308540e75dc96963308540e75d986963308540eb5e886963308540ef1dc46963308540e3dda86563308540e5dda76563308540e6dda66563308540e75da56563308540af5dca9563308540e75da99563308540eb5da89563308540ed5da79563308540ee5da69563308540ef1da49563308540eb9da85523308540ed9da75523308540ee9da65523308540ef1da55523308540a7facc661a008540a7f8c5661a008540e3f998a21a008540a7facc655a008540a7f8c8655a008540e3fa88655a008540a7f9c9615a0085408ff9cb215a008540a7f9c9215a008540adf9c7215a008540aef9c6215a008540afb9c4215a008540afd9c3215a008540afe9c2215a008540aff1c1215a008540e77998955a008540eb7a88955a008540e77995955a008540afbacc551a008540e7b998551a008540ebba88551a008540ef3a55551a008540a7facc64da008540a7f8c864da008540e3fa8864da008540a7f8c564da008540e77a5564da008540a7f9c960da008540a7f9c954da008540ef395454da008540e7d9988cda008540ebda888cda008540e7d9958cda008540ef5a558cda008540ef99548cda0085408ffacc6e93008540a7f9c96a13008540abfacc6a13008540cbfabb6a13008540e3f9c96a13008540c7f9ba6613008540e3f9a86613008540abf9caa213008540cbf9baa213008540e3f9a9a213008540ebb9a4a213008540cdfabb69d3008540e5f99869d3008540e9fa8869d3008540cefabb6993008540e6f9986993008540eafa886993008540afb9c46953008540af7acc6953008540cf7abb6953008540e779986953008540eb7a886953008540ef39c46953008540ef59c36953008540af79ca9553008540cf79ba9553008540e779a99553008540eb79a89553008540ed79a79553008540ee79a69553008540ef39a49553008540cfb9ba5513008540ebb9a85513008540edb9a75513008540eeb9a65513008540ef39a55513008540afdacc68d3008540cfdabb68d3008540e7d99868d3008540ebda8868d3008540ef5a5568d3008540ef995468d3008540afd9ca54d3008540cfd9ba54d3008540e7d9a954d3008540ebd9a854d3008540edd9a754d3008540eed9a654d3008540ef59a554d3008540ef99a454d3008540ff195454d3008540 else (if i < 2 then 0xabbecc6a15408540cbbebb6a15408540e3bdc96a1540854097bccb6615408540e3bda86615408540abbdcaa215408540cbbdbaa215408540e3bda9a215408540cdbebb69d5408540e5bd9869d5408540e9be8869d5408540cebebb6995408540e6bd986995408540eabe886995408540af3ecc6955408540cf3ebb6955408540e73d986955408540eb3e886955408540cf3dba9555408540e73da99555408540eb3da89555408540ed3da79555408540ee3da6955540854087fccb661a30854087fccb655a308540a7decc6e5a308540c7debb6e5a308540a7dcc86e5a308540a7dcc56e5a308540a7ddc92e1a308540adddc72e1a308540aeddc62e1a308540af5dc52e1a308540af9dc42e1a308540afcdc22e1a308540afd5c12e1a308540afd9c02e1a308540a7decc661a308540a7ddcb661a308540a7dccb661a308540c7debb661a308540a7dcc5661a308540cbdebba21a308540e3ddb9a21a308540e3dd98a21a308540a7ddc92d5a308540af9dc42d5a308540afd9c02d5a308540a7decc655a308540a7ddcb655a308540a7dccb655a308540c7debb655a308540a7dcc8655a308540e3de88655a308540a7ddc9615a3085408fddcb215a308540a7ddc9215a308540adddc7215a308540aeddc6215a308540af9dc4215a308540afcdc2215a308540afd5c1215a308540afd9c0215a308540cf5ebb955a308540e75db9955a308540e75d98955a308540eb5e88955a308540e75d95955a308540af9ecc551a308540cf9ebb551a308540e79d98551a308540eb9e88551a308540ef1db5551a308540ef1e55551a308540afdacc6c1a308540cfdabb6c1a308540e7d9986c1a308540ebda886c1a308540cfd9b56c1a308540ef5a556c1a308540ef99546c1a30854097bdc4aed930854087fccb6a19308540c3fcb86a19308540a3fecc6a19308540c3fdcb6a19308540c3fccb6a19308540c3febb6a19308540c3fcb56a19308540a3fdcaa219308540c3fdbaa219308540e3bda4a219308540c5febb69d9308540c5fcb869d9308540e1fe8869d9308540c5fcb569d9308540c6febb6999308540c6fcb86999308540e2fe886999308540c6fcb5699930854087fccb6959308540c77cb56959308540a77ecc6959308540c77dcb6959308540c77ccb6959308540c77ebb6959308540c77cb86959308540e37e886959308540a77dca9559308540c77dba9559308540e37da89559308540e57da79559308540e67da69559308540e73da49559308540a7decc68d9308540c7debb68d9308540c7dcb868d9308540e3de8868d9308540c7dcb568d9308540e75e5568d930854087fdc96e98308540c3fdb96a18308540c5fdb969d8308540c6fdb96998308540c77db96958308540c7ddb968d830854087fdc96e95308540c3fdb96a15308540 else 0xabddc32d5a808540abf9c02d5a80854087fdcaaed9808540a3fecc6a19808540c3febb6a19808540c3fcb56a19808540a3fdca6628808540e3bda46628808540a5fecc661a708540a5fcc5661a708540e1fd98a21a708540a6fecc661a608540a6fcc5661a608540e2fd98a21a60854087fccb661a508540a77cc5661a508540c7bdb4661a508540a77ecc6e5a508540c77ebb6e5a508540a77cc86e5a508540a77dc92e1a508540ad7dc72e1a508540ae7dc62e1a508540af3dc42e1a508540af5dc32e1a508540af79c02e1a508540a77ecc661a508540a77dcb661a508540a77ccb661a508540c77ebb661a508540cb7ebba21a508540e37db9a21a508540e37d98a21a508540af3ecc6d1a508540cf3ebb6d1a508540e73d986d1a508540eb3e886d1a508540cf3db46cda50854087fccb6a19508540c3fcb86a19508540a3fecc6a19508540c3fdcb6a19508540c3fccb6a19508540c3febb6a19508540a3fdcaa219508540c3fdbaa219508540e3bda4a219508540c5febb69d9508540c5fcb869d9508540e1fe8869d9508540c6febb6999508540c6fcb86999508540e2fe886999508540a77ecc6959508540c77ebb6959508540c77cb86959508540e37e88695950854087fdc96e98508540c3fdb96a18508540c5fdb969d8508540c6fdb96998508540c77db9695850854087fdc96e885085408fbdc46e88508540c3fdb96a08508540c5fda96dc8508540c9fda86dc85085408dfdcb69c8508540c5fdb969c8508540c6fda96d88508540cafda86d88508540ccfda76d885085408efdcb6988508540c6fdb96988508540ccfdb76988508540c77db96948508540cd7db76948508540ce7db66948508540cbbda86d08508540cdbda76d08508540cebda66d08508540cf3da56d08508540c7dda96cc8508540cbdda86cc8508540cddda76cc8508540cedda66cc8508540cf5da56cc8508540c7eda96c88508540cbeda86c88508540cdeda76c88508540ceeda66c88508540cf6da56c88508540c7f5a96c48508540cbf5a86c48508540cdf5a76c48508540cef5a66c48508540cf75a56c48508540c7f9a96c08508540cbf9a86c08508540cdf9a76c08508540cef9a66c08508540cf79a56c08508540ab7ecc6a25508540e37dc96a25508540a77dca6625508540c77dba6625508540e37da86625508540e73da46625508540ab7dcaa225508540cb7dbaa225508540e37da9a225508540e57d9869e5508540e97e8869e5508540e67d9869a5508540ea7e8869a5508540a77dca6565508540e37da86565508540e57da76565508540e67da66565508540e73da46565508540adbdc7215a408540aebdc6215a408540af9dc3215a408540afadc2215a408540afb5c1215a408540afb9c0215a408540eb3e88955a408540a7bdc96a15408540)) else (if i < 4 then 0x87fccb655a220540c7bdb9551a22054087fccb64da220540c7ddb98cda22054087fdcaaed9220540a5fecc69d9220540c5febb69d9220540c5fdba9dd9220540e5bda49dd922054087fccb6959220540a7bdc46959220540c77dba9559220540e57da79559220540e73da4955922054097bccb5519220540e5bda75519220540e5dda78cd922054087fdc96e952205408dfcc76e9522054095fcc76e55220540c5fcb76a552205408dfccb69d5220540c5fdb969d5220540cdbcb7691522054087fdc96e852205408fbdc46e85220540c5fdb969c5220540c6fda96d85220540ccfda76d85220540cdbda76d05220540cebdb6690522054087fdc96e93220540c5fdb969d3220540adeecc69e2220540e7ada465e2220540e5eda99de2220540a7edca6562220540e5eda76562220540e7ada46562220540e76da99562220540ed6da79562220540edae776922220540ef2e556922220540afadca5522220540e7ada95522220540edada75522220540a7edca64e2220540e5eda764e2220540e7ada464e2220540e7cda98ce2220540edcda78ce2220540ef8da48ce2220540a7edca64a2220540e5eda764a2220540e7ada464a2220540adfacc69d3020540cdfabb69d3020540e5f9a99dd3020540edb9a49dd3020540afb9c46953020540e779a99553020540ed79a79553020540ef39a49553020540edb9a75513020540cfdabb68d3020540edda7768d3020540ef5a5568d3020540ef995468d3020540afd9ca54d3020540e7d9a954d3020540edd9a754d3020540ef59a554d3020540ef99a454d3020540ff195454d3020540a7f9c96893020540e5f9a76493020540e7d9a36493020540e7e9a98893020540ede9a78893020540efa9a48893020540efc9a3889302054087fdcaaed9814540a3fdca6628814540e3bda4662881454087fccb661a31454097bdc4aed931454087fccb6a19314540c3fdbaa21931454087fdc96e98314540a7ddc96a23314540e3dda9a223314540eb9da4a22331454087fccb661a21454087fccb64da214540c7ddb98cda21454087fdcaaed921454087fccb6a19214540c3fdbaa219214540e3bda4a21921454087fccb68d921454087fdc96e9821454097dcc36e5821454087fdc96e8821454087fdc96e93214540a7edca6622214540e7ada46622214540e3eda9a222214540ebae886922214540a7edca64e2214540e7cda98ce2214540ef8da48ce2214540a7edca64a2214540e7ada464a2214540ebb9a4a213014540afdacc68d3014540cfdabb68d3014540e7d99868d3014540ebda8868d3014540e7d9a36493014540efa9a48893014540efc9a38893014540a3fecc6e5a808540c3febb6e5a808540a3fcc56e5a808540a3fdc92d5a808540a9fdc72d5a808540aafdc62d5a808540abbdc42d5a808540 else (if i < 5 then 0x87fdc96e93114940c6fdb96993114940afb5c46853114940eeb5a65053114940ef95a35053114940a7f5ca6621114940e7b5a46621114940e3f5a9a221114940aef6cc69a1114940e6f59869a1114940eaf68869a1114940e7b5a465a1114940e6f5a999a1114940ebb6886921114940eeb6666921114940a7f5ca64e1114940e6f5a664e1114940e7b5a464e1114940e7d5a98ce1114940eed5a68ce1114940ef95a48ce1114940a7f5ca6461114940e6f5a66461114940e7b5a46461114940afb5ca5061114940e7b5a95061114940eeb5a65061114940a7f9c96a13014940e3f9a9a213014940ebb9a4a213014940aefacc6993014940cefabb6993014940e6f9986993014940eafa886993014940e6f9a99993014940eeb9a49993014940afdacc68d3014940cfdabb68d3014940e7d99868d3014940ebda8868d3014940eeda6668d3014940afb9c46853014940eeb9a65053014940ef99a35053014940afd9ca4c53014940e7d9a94c53014940eed9a64c53014940ef99a44c53014940efd1a14c53014940ff91414c53014940e7f1a98453014940eef1a68453014940efb1a48453014940efd1a38453014940a5fdc92d5a720540a9fdc82d5a720540acfdc62d5a720540adbdc42d5a720540adddc32d5a720540adedc22d5a720540adf5c12d5a720540adf9c02d5a720540a5fdc92c9a720540a9fdc82c9a720540acfdc62c9a720540ad7dc52c9a720540adbdc42c9a720540adddc32c9a720540adf5c12c9a720540adf9c02c9a72054087fdcaaed972054087fccb65da520540c7bdb465da52054087fccb69d9520540a5fecc69d9520540c5fccb69d9520540c5febb69d9520540c5fdba9dd9520540e5bda49dd9520540ad7ecc69e5520540e73da465e5520540e57da99de5520540a77dca6565520540e57da76565520540e73da46565520540ed3e77955a420540adbecc69d5420540cdbebb69d5420540cdbdba9dd5420540e5bda99dd5420540cf3dba9555420540e73da99555420540ed3da79555420540c5fdb765da32054097bdc4aed932054087fdcb69d932054087fccb69d9320540c5fdb769d9320540a5fecc69d9320540c5fdcb69d9320540c5fccb69d9320540c5febb69d9320540c5fcb569d9320540c5fcb269d9320540c5fdba9dd9320540e5bda49dd932054087fccb6959320540c77dba9559320540e57da79559320540e73da4955932054087fdc96e95320540c5fdb969d5320540af3dc46955320540ed3da75515320540ef1d5468d5320540a7ddc969e3320540addecc69e3320540e5ddc969e3320540e5dda765e3320540e5dda99de3320540ed9da49de3320540a7ddc96963320540af9dc46963320540e5dda76563320540e75da99563320540ed5da79563320540ef1da49563320540ed9da75523320540 else 0xef1d5468d5320940a7ddc96963320940e75da9956332094087fccb655a12094087fccb64da120940c7ddb98cda12094087fccb6959120940c77dba955912094087fdc96e9512094087fccb6a55120940e73da9955412094087fdc96e93120940ef95a35053120940a7f4cb6a61120940a7f4c56a61120940a7f5ca6561120940e775a99561120940e7b5a95521120940a7f5ca64e1120940e7d5a98ce112094087fccb6a61120940a7f5ca6461120940e7b5a95061120940e779a99553020940e7d9a954d3020940ef59a554d3020940ff195454d3020940e7d9a94c53020940efd1a14c53020940ff91414c53020940e7f1a9845302094087fdcaaed9814940a3fdca6628814940e3bda4662881494087fccb661a614940a6fdc92e1a614940acfdc72e1a614940ae7dc52e1a614940aebdc42e1a614940aeddc32e1a614940aeedc22e1a614940aef5c12e1a614940aef9c02e1a614940a6fecc661a614940a6fccb661a614940c6febb661a614940cafebba21a614940e2fd98a21a614940a6fdc92c5a614940aafdc82c5a614940acfdc72c5a614940ae7dc52c5a614940aebdc42c5a614940aeddc32c5a614940aeedc22c5a614940aef9c02c5a61494087fccb6a19614940e3bda4a219614940a6fdca6626614940e6bda46626614940e2fda9a226614940eabe88999a41494087fccb661a31494087fccb659a314940c6fdb6659a31494097bdc4aed931494087fccb6a19314940c3fdbaa219314940e3bda4a21931494087fdcb699931494087fccb6999314940c6fdb66999314940a6fecc6999314940c6fdcb6999314940c6fccb6999314940c6febb6999314940c6fcb86999314940e2fe886999314940c6fcb16999314940c6fdba9999314940e6bda4999931494087fdc96e98314940c6fdb96998314940a7ddc96a23314940e3dda9a223314940eb9da4a223314940a7ddc969a3314940aedecc69a3314940e6ddc969a3314940e6dd9869a3314940eade8869a3314940e6dda665a3314940e6dda999a3314940ee9da499a331494087fccb661a114940c7bdb4661a114940c7bdb4659a11494087fccb64da114940c7ddb98cda114940cf9db48cda11494087fccb6a19114940c3fdbaa219114940e3bda4a219114940a6fecc6999114940c6febb6999114940e2fe886999114940c6fdba9999114940e6bda4999911494087fccb68d9114940e6dda68cd911494087fdc96e981149408efcc66e9811494096fcc66e58114940c6fcb66a581149408efccb6998114940c6fdb96998114940cebcb66918114940a7bdc96a1411494097bccb6614114940cbbdbaa214114940e3bda9a214114940aebecc6994114940cebebb6994114940e6bd986994114940eabe886994114940cebdba9994114940e6bda99994114940ee9da68cd4114940))) else (if i < 9 then (if i < 7 then 0xefd1c068e1121540a7f5ca64e1121540c7f5ba64e1121540e5f5a764e1121540e6f5a664e1121540e7b5a464e1121540e7d5a364e1121540cfd5ba8ce1121540e7d5a98ce1121540edd5a78ce1121540eed5a68ce1121540ef95a48ce1121540afe6cc68a1121540e7e5c968a1121540e7e59368a1121540efc63368a1121540a7f5ca64a1121540c7f5ba64a1121540e5f5a764a1121540e6f5a664a1121540e7b5a464a1121540e7d5a364a1121540e7e5a264a1121540afe5ca88a1121540cfe5ba88a1121540e7e5a988a1121540ede5a788a1121540eee5a688a1121540efa5a488a1121540efc5a388a1121540a7f5ca6461121540e5f5a76461121540e6f5a66461121540e7b5a46461121540e7d5a36461121540e7e5a26461121540afb5ca5061121540e7b5a95061121540edb5a75061121540eeb5a65061121540ef95a35061121540efa5a25061121540a7facc64da021540a7f8c264da021540a7f8c164da021540a7facc649a021540e7da33649a021540a7f8c1649a021540a7f9c94c9a021540e7e993889a021540efca33889a021540e7e992889a021540a7facc645a021540e7da33645a021540a7f8c2645a021540e7ea22645a021540afbacc505a021540ef9a33505a021540e7b992505a021540efaa22505a021540a7f9c94c5a021540efb1414c5a021540a7f9c9485a021540e7f193845a021540efd233845a021540e7f192845a021540efe222845a021540e7f191845a021540efb141845a0215408ffacc6e93021540cdfabb69d3021540cefabb6993021540cfdabb68d3021540a7f9c96893021540afeacc6893021540cfeabb6893021540e7e9c96893021540c7f9ba6493021540e5f9a76493021540e6f9a66493021540e7d9a36493021540e7e9a26493021540afe9ca8893021540cfe9ba8893021540e7e9a98893021540ede9a78893021540eee9a68893021540efa9a48893021540efc9a38893021540afb9c46853021540aff2cc6853021540cff2bb6853021540efb1c46853021540efd1c36853021540e7f1926853021540efe2226853021540cfb9ba5053021540edb9a75053021540eeb9a65053021540ef99a35053021540efa9a25053021540efb1a15053021540afd9ca4c53021540cfd9ba4c53021540e7d9a94c53021540edd9a74c53021540eed9a64c53021540ef99a44c53021540efc9a24c53021540efd1a14c53021540ff91414c53021540aff1ca8453021540cff1ba8453021540e7f1a98453021540edf1a78453021540eef1a68453021540efb1a48453021540efd1a38453021540efe1a28453021540a77ccb6a65520940a77cc16a6552094087fccb6a65520940a77dca6565520940e73da9955542094097bdc4aed932094087fccb6959320940c77dba955932094087fdc96e95320940 else (if i < 8 then 0xe7cda364e2221540cfcdba8ce2221540e7cda98ce2221540edcda78ce2221540eecda68ce2221540ef8da48ce2221540a7edca64a2221540e5eda764a2221540e6eda664a2221540e7ada464a2221540e7cda364a222154087fccb64da121540a7f4c164da121540c7ddb98cda121540cf9db48cda12154087fccb649a121540c7bdb4649a121540a7f4c1649a121540a7f6cc6e5a121540c7f6bb6e5a121540a7f4c26e5a121540afb6cc6d1a121540cfb6bb6d1a121540cfb5b46cda121540a7f6cc64da121540a7f5cb64da121540a7f4cb64da121540c7f6bb64da121540a7f4c264da121540cfd6bb8cda121540e7d5b98cda121540ef95b48cda121540a7f5c92c9a121540adf5c72c9a121540aef5c62c9a121540afb5c42c9a121540afd5c32c9a121540aff1c02c9a121540a7f6cc649a121540a7f5cb649a121540a7f4cb649a121540c7f6bb649a121540e7b5b4649a121540e7d633649a121540a7f5c94c9a121540cfe6bb889a121540e7e5b9889a121540efa5b4889a121540e7e593889a121540efc633889a121540e7e592889a121540c5febb69d9121540c5fcb269d9121540c6febb6999121540c6fcb26999121540a7decc68d9121540c7ddcb68d9121540c7debb68d9121540c7dcb268d9121540e5dda78cd9121540e6dda68cd912154087fccb6899121540c7ecb26899121540a7eecc6899121540c7edcb6899121540c7eccb6899121540c7eebb6899121540e7ce336899121540a7edca8899121540c7edba8899121540e5eda78899121540e6eda68899121540e7ada48899121540e7cda38899121540a7f6cc6859121540c7f6bb6859121540e7d6336859121540c7f4b26859121540e7e6226859121540cdbebb69d4121540cebebb6994121540af9ecc68d4121540cf9ebb68d4121540ef95c168d4121540ef99c068d4121540ed9da78cd4121540ee9da68cd4121540a7bdc96894121540afaecc6894121540cfaebb6894121540e7adc96894121540ef8e33689412154097bccb6494121540e5bda76494121540e6bda66494121540e79da36494121540e7ada26494121540afadca8894121540cfadba8894121540e7ada98894121540edada78894121540eeada68894121540ef8da38894121540afb6cc6854121540cfb6bb6854121540ef96336854121540e7b5926854121540efa622685412154087fdc96e93121540c5fdb969d3121540c6fdb96993121540c7ddb968d3121540c7edb96893121540c7f5b96853121540afb5c46853121540cfb5ba5053121540edb5a75053121540eeb5a65053121540ef95a35053121540efa5a2505312154087fdc96e92121540c5fdb969d2121540c6fdb96992121540c7ddb968d2121540c7edb96892121540c7f5b96852121540afd6cc68e1121540e7d5c968e1121540 else 0xe77da96155308540eb7da86155308540ed7da76155308540ee7da66155308540ef3da46155308540cfbdba5515308540ebbda85515308540edbda75515308540eebda65515308540ef3da55515308540ef3dba5515308540ef3da85515308540cfdebb68d5308540cfddb868d5308540cfdcb868d5308540e7dd9868d5308540e7dd9568d5308540ef5d8568d5308540ef9d5468d53085409fdccb60d5308540afddca60d5308540cfddba60d5308540e7dda960d5308540ebdda860d5308540eddda760d5308540eedda660d5308540ef5da560d5308540ef9da460d5308540ff1d5460d5308540aff8c5a21a008540e7fa88655a008540affacc615a008540e7f9c9615a008540e7f998615a008540e7f995615a008540aff9c3215a008540aff8c8955a008540efba88551a008540efb985551a008540e7f98564da008540affacc60da008540e7f99860da008540aff8c560da008540e7f99560da008540efb95460da008540affacc54da008540aff9c854da008540aff8c854da008540e7f99854da008540e7f99554da008540ef798554da008540efb95454da008540efd98354da008540ebf9c56a13008540ef79c86953008540aff9ca6153008540cff9ba6153008540e7f9a96153008540ebf9a86153008540edf9a76153008540eef9a66153008540ef79a56153008540efb9a46153008540efb9a85513008540efd98568d3008540a7decc6e5a321540a7dcc26e5a321540a7dcc16e5a321540afdacc6c1a321540cfd9b16c1a32154097bdc4aed9321540c5febb69d9321540c5fcb269d9321540c5fcb169d9321540c6febb6999321540c6fcb26999321540c6fcb16999321540c7debb68d9321540c7dcb268d9321540c7dcb168d932154087fccb64da221540a7ecc264da221540c7ddb98cda221540a7eecc6e5a221540c7eebb6e5a221540a7ecc16e5a221540a7eecc64da221540a7edcb64da221540a7eccb64da221540c7eebb64da221540a7ecc164da221540cfcebb8cda221540e7cdb98cda221540a7edc92c5a221540adedc72c5a221540aeedc62c5a221540afadc42c5a221540afcdc32c5a221540afe9c02c5a22154087fdcaaed9221540c5febb69d9221540c5fcb169d9221540c6febb6999221540c6fcb16999221540a7decc68d9221540c7ddcb68d9221540c7debb68d9221540c7dcb168d9221540e7d9c068d9221540e5dda78cd9221540e6dda68cd9221540a7eecc6899221540c7eebb6899221540e7ce336899221540c7ecb1689922154087fdc96e93221540c5fdb969d3221540c6fdb96993221540c7ddb968d3221540c7edb96893221540afcecc68e2221540e7cdc968e2221540efc9c068e2221540a7edca64e2221540c7edba64e2221540e5eda764e2221540e6eda664e2221540e7ada464e2221540)) else (if i < 11 then (if i < 10 then 0xa7fdc9215a308540adfdc7215a308540aefdc6215a308540afbdc4215a308540afddc3215a308540afedc2215a308540aff5c1215a308540aff9c0215a3085408ffccb955a308540afdcc8aeda308540afdcc5aeda308540afdecc6e1a308540afdcc56e1a308540afddc52e1a308540e7ddb8661a308540afdccba21a308540afdcc5a21a308540afdecc6d5a308540afdcc86d5a308540cfddb86d5a308540e7dd986d5a308540afddc82d5a308540e7ddb8655a308540e7de88655a308540e7ddb5655a308540afdecc615a308540afddcb615a308540afdccb615a308540e7ddc9615a308540e7ddb9615a308540e7dd98615a308540ef5db5615a308540e7dd95615a308540afddcb215a308540afdccb955a308540afdcc8955a308540ef9db8551a308540ef9e88551a308540ef9db5551a308540ef9d85551a308540efd9856c1a308540e3fdc56a19308540e77dc8695930854097fccb6159308540a7fdca6159308540c7fdba6159308540e3fda86159308540e5fda76159308540e6fda66159308540e77da56159308540e7bda46159308540e7dd8568d9308540c7fda9aed8308540cfbda4aed83085408ffecc6e983085408ffcc56e98308540cbfebb6a18308540cbfcb56a18308540c7fdba6618308540e3fda86618308540cdfebb69d8308540e5fd9869d8308540cdfcb569d8308540cefebb6998308540e6fd986998308540cefcb569983085408ffccb6958308540a7fdc96958308540c7fdb96958308540cf7cb56958308540afbdc46958308540cf7ccb6958308540cf7ebb6958308540e77dc96958308540e77d986958308540ef3dc4695830854097fccb6558308540c7fdba6558308540e3fda86558308540e5fda76558308540e6fda66558308540e77da56558308540cfbdba5518308540ebbda85518308540edbda75518308540eebda65518308540ef3da55518308540cfdebb68d8308540e7dd9868d8308540cfdcb568d8308540e7dd9568d8308540ef9d5468d83085408ffdcaaed530854097fdc9aed5308540c7fda9aed5308540cf7da5aed5308540cfbda4aed5308540c7fda96e15308540cf7da56e15308540cfbda46e153085408ffdcb6a153085408ffccb6a15308540cbfdb86a15308540cbfcb86a15308540cbfdcb6a15308540cbfccb6a15308540cbfebb6a15308540eb7dc56a15308540ebddc36a1530854097fccb6615308540c7fdba6615308540e3fda86615308540e77da56615308540cdfebb69d5308540cdfdb869d5308540cdfcb869d5308540e5fd9869d5308540cefebb6995308540cefdb86995308540cefcb86995308540e6fd986995308540c7fdba6555308540e3fda86555308540e5fda76555308540e6fda66555308540e77da56555308540af7dca6155308540cf7dba6155308540 else 0xcfddb868d3214540e7dd9868d3214540cfedba6093214540e7eda96093214540ebeda86093214540efada46093214540efcda36093214540c7fcb86a622145408ffccb6a22214540cbfcb86a2221454097fccb6622214540a7fdca6622214540e7bda46622214540cfbcb869222145408ffccb68e2214540a7fdca64e2214540affacc6a13014540aff8c26a13014540efb9a4a213014540efd9a3a213014540affacc6893014540aff8c86893014540e7f9986893014540e7f9a86493014540aff9ca6093014540ebf9a86093014540efb9a46093014540efd9a36093014540efe9a26093014540aff9ca2093014540b7f9c92093014540efb9a42093014540efd9a32093014540efb9a48893014540efd9a388930145408ffcc5aeda808540abfcc5aeda808540abfecc6d5a808540abfdc32d5a808540abfecc6cda808540abfcc56cda808540c7fda8aed9808540cbfcb56a28808540adfcc5a21a708540aefcc5a21a608540af7dc32e1a508540a7fecc6a19508540c7febb6a19508540c7fdb36a19508540e3fecc6a19508540e3fdc56a19508540e3fdc36a1950854097fccba219508540c7fdbaa219508540e3fda8a219508540e77da5a219508540e7bda4a219508540e5fe8869d9508540e6fe8869995085408ffdcaaed850854097fdc9aed8508540c7fda9aed8508540cf7da5aed8508540cfbda4aed8508540a7fdca6e58508540c7fdba6e58508540e3fda86e58508540e77da56e58508540e7bda46e58508540c7fda86e58508540cbfebb6a18508540a7fdca6618508540c7fdba6618508540e3fda86618508540b77cc56618508540e77da56618508540e7bda46618508540cdfebb69d8508540e5fdb969d8508540e5fd9869d8508540cefebb6998508540e6fdb96998508540e6fd986998508540a7fdca6558508540c7fdba6558508540e3fda86558508540e5fda76558508540e6fda66558508540e77da56558508540e7bda46558508540c7fda96cc8508540cbfda86cc8508540cdfda76cc8508540cefda66cc8508540cf7da56cc8508540cfbda46cc8508540cfddca6cc85085408ffccb6a25508540cbfcb86a25508540cbfccb6a25508540cdfcb869e5508540cefcb869a5508540afbecc6a15408540ebbecc6a15408540ebbdc56a15408540ebbdc36a15408540e7bda86615408540cfbdbaa215408540e7bda9a215408540ebbda8a215408540ef3da5a215408540edbe8869d5408540eebe886995408540afbdca6155408540cfbdba6155408540e7bda96155408540ebbda86155408540edbda76155408540eebda66155408540ef3da561554085408ffcc8aeda3085408ffcc5aeda308540a7fcc5661a3085408ffccba21a308540a7fcc8655a3085408ffccb615a308540a7fdc9615a3085408ffdcb215a308540) else (if i < 12 then 0x8ffdca6dd3220540c7fda96dd3220540cdfda76dd3220540cfbda46dd3220540c7fdb969d3220540cdfebb69d3220540cdfdb569d322054097fccb65d3220540c7fdba65d32205408ffdcb69532205408ffccb6953220540a7fdc96953220540c7fdb96953220540cf7db56953220540afbdc4695322054097fccb6553220540c7fdba6553220540e5fda76553220540cfbdba5513220540edbda75513220540e7dd9768d3220540cfddb568d3220540e7dd9568d3220540ef9d5468d3220540afddca5cd3220540e7dda95cd3220540eddda75cd3220540f5dd975cd3220540ef9da45cd3220540e7ed976893220540cfedb56893220540e7ed956893220540efad546893220540efcd736893220540c7fcb56a622205408ffccb6962220540cf7cb5696222054097fccb6562220540a7fdca6562220540e5fda76562220540e7bda46562220540cfbcb56922220540afbdca5522220540e7bda95522220540edbda75522220540edf9c269d3020540efb9546893020540aff9ca5c93020540e7f9a95c93020540edf9a75c93020540efb9a45c93020540efd9a35c93020540aff9ca5493020540e7f9a95493020540edf9a75493020540ef79a55493020540efb9a45493020540efd9a35493020540efe9a254930205408ffcc2aeda814540a7fcc26e5a81454097fdc2aed9814540c7fcb26a19814540a7fdca2c99814540c7fcb26a68814540afbcc2a21a4145408ffcc8aeda3145408ffcc2aeda3145408ffccba21a314540c7fcb26a19314540c7fda9aed8314540cfbda4aed83145408ffecc6e983145408ffcc26e9831454097fcc26e583145408ffcc8aeda214540a7fcc86e5a214540a7fecc661a214540a7fdcb661a214540c7fccb661a214540c7febb661a214540a7fdc2661a2145408ffccba21a214540afecc2a21a214540a7fecc64da214540c7febb64da214540a7fcc864da2145408ffccb60da214540a7fdc960da214540c7fdb960da21454097fccb60d9214540a7fdca60d9214540e7dda360d9214540c7fcb868992145408ffdcaaed821454097fdc9aed82145408ffecc6e98214540c7febb6a58214540cfbebb69182145408ffccb68d821454097fccb64d8214540a7fdca64d8214540c7fdba64d8214540e3fda864d8214540abfdca60d8214540e3fda960d8214540ebbda460d8214540ebdda360d8214540e7ed936898214540ebed836898214540c7fda96cc8214540cfbda46cc82145408ffdcb68c8214540c7fdb968c8214540cfddb368c82145408ffdcaaed3214540c7fda9aed3214540cfbda4aed32145408ffecc6e932145408ffcc86e93214540c7fda96e13214540cfbda46e132145408ffdcb6a132145408ffccb6a13214540a7fdc96a13214540c7fdb96a1321454097fccb6613214540c7fdba6613214540 else 0xafddca58d3114940e7dda958d3114940eedda658d3114940f6dd9658d3114940ef9da458d3114940e7f5986853114940e7f5966853114940efd5636853114940efb5a85053114940eef9c86993014940aff9ca6193014940e7f9a96193014940eef9a66193014940efb9a46193014940efd98668d3014940aff9ca6053014940e7f9a96053014940ebf9a86053014940eef9a66053014940efb9a46053014940efd9a36053014940eff1a16053014940efb9a85053014940adfdc32d5a720540e5fd936c9a720540adfdc32c9a720540a7fcc26e5a520540a7fcc2655a320540a7fdc95d5a320540c7fcb269593205408ffdcaaed732054097fdc9aed7320540c7fda9aed7320540cdfda7aed7320540cfbda4aed73205408ffdcb6957320540a7fdc96957320540e5fd976957320540afbdc4695732054097fccb6557320540c7fdba6557320540e5fda76557320540cfbdba5517320540edbda755173205408ffcc26e9532054097fccb65d5320540c7fdba65d5320540e77d976955320540ef3da75515320540e7dd9768d5320540afddca5cd5320540e7dda95cd5320540eddda75cd5320540f5dd975cd5320540ef5da55cd5320540ef9da45cd5320540ff1d545cd53205408ffcc5aeda220540a7fcc56e5a220540a7fecc655a220540a7fdcb655a220540c7febb655a220540a7fdc3655a220540a7fdc2655a220540a7fdc95d5a220540cfbebb551a220540e7bdb9551a220540e7bd97551a220540a7fcc564da220540e5fd975cda2205408ffccb54da220540c7fdb954da220540ef3d5454da220540c7fcb568d922054097fccb54d9220540a7fdca54d9220540e5fda754d9220540e77da554d9220540e7dda354d9220540c7fcb56899220540e7bd546899220540c7fd936e97220540c7fdb56a57220540e5fd9369d72205408ffdcb6957220540a7fdca6557220540c7fdba6557220540e5fda76557220540e7bda46557220540cfbdb56917220540afbdca5517220540cfbdba5517220540e7bda95517220540edbda75517220540a7fdc968d7220540adfdca5cd7220540cdfdba5cd7220540e5fda95cd7220540edbda45cd7220540c7fd976e95220540e77d976955220540cdfcb768d522054097fccb64d5220540a7fdca64d5220540c7fdba64d5220540e5fda764d5220540e77da564d5220540e7bda464d5220540e7ed976895220540e7ed936895220540afedca5c95220540e7eda95c95220540ededa75c95220540ef6da55c95220540efada45c95220540c7fda96cc5220540cdfda76cc5220540cfbda46cc52205408ffdcb68c5220540c7fdb968c5220540cefdb668c5220540cfbdb468c5220540cfddb368c52205408ffdcaaed3220540c7fda9aed3220540cfbda4aed32205408ffecc6e932205408ffcc56e93220540)))) else (if i < 19 then (if i < 16 then (if i < 14 then 0x8ffcc1aeda814940a7fcc16e5a814940aefcc66c5a814940c7fcb16a19814940c7fcb16a68814940e6fd936e1a614940aefdc32e1a614940aefdc32c5a614940c7fd936e98614940c7fdb16a58614940e6fd936998614940afbcc1a21a414940afbdc1619a4149408ffcc8aeda3149408ffcc1aeda314940a7fcc1661a3149408ffccba21a314940c7febb659a314940e6fdb6659a314940c7fdb9619a314940c7fcb16a19314940c7fda9aed8314940cfbda4aed83149408ffecc6e983149408ffcc16e98314940cbfdb16a183149408ffccb6998314940c7fdb96998314940cefccb6998314940cefebb6998314940cefdb1699831494097fccb6598314940c7fdba6598314940e3fda86598314940e7dd9668d8314940cfddb168d83149408ffdcaaed631494097fdc9aed6314940c7fda9aed6314940cefda6aed6314940cfbda4aed6314940c7fda96e16314940cefda66e16314940cfbda46e163149408ffdcb6a163149408ffccb6a16314940a7fdc96a16314940e6fd966a1631494097fccb6616314940c7fdba6616314940e6fda66616314940aefdca6196314940cefdba6196314940e6fda96196314940eebda46196314940cfddba60d6314940e7dda960d6314940ebdda860d6314940eedda660d6314940f6dd9660d6314940ef9da460d6314940a7fcc86e5a1149408ffccba21a114940aff4c1a21a1149408ffdcb619a114940a7fcc864da1149408ffdcb60da1149408ffccb60da114940a7fdc960da114940c7fdb960da114940cfbdb460da114940aff5c160da1149408ffdcb58da114940c7fdb958da114940e6fd9658da114940cfbdb458da114940a7fdca6199114940c7fdba6199114940e6fda66199114940e7bda46199114940a7fecc68d9114940c7fcb868d911494097fccb60d9114940a7fdca60d9114940e3fda860d9114940e6fda660d9114940e7dda360d9114940a7fdca58d9114940e6fda658d9114940c7fd966e98114940e3fd966a18114940abfdca6198114940e3fda96198114940eafda66198114940ebbd8669181149408ffccb68d8114940cefcb668d811494097fccb64d8114940a7fdca64d8114940c7fdba64d8114940e3fda864d8114940e6fda664d8114940e7bda464d8114940e7f5966858114940ebf5866858114940e7f5936858114940c7fdb96a16114940c7fdb968d6114940afbdca6194114940cfbdba6194114940e7bda96194114940eebda66194114940afbecc68d4114940afbdca60d4114940ebbda860d4114940eebda660d4114940ef9da360d4114940afbdca58d4114940eebda658d41149408ffcc86e931149408ffccb6a13114940a7fdc96a1311494097fccb6613114940c7fdba6613114940e6fd986993114940c7fdba6593114940e7dd9868d3114940e7dd9668d3114940 else (if i < 15 then 0xe7bda46452121540e7dda36452121540e7eda26452121540e7f5a16452121540afbdca5052121540cfbdba5052121540e7bda95052121540edbda75052121540eebda65052121540ef9da35052121540efada25052121540efb5a15052121540aff5ca4c52121540cff5ba4c52121540e7f5a94c52121540edf5a74c52121540eef5a64c52121540efb5a44c52121540efd5a34c52121540efe5a24c52121540c7fcb26a61121540cdfcb269e1121540cefcb269a1121540cfbcb26921121540cfdcb268e11215408ffccb68a1121540cfecb268a1121540cfeccb68a1121540affacc4c9a021540e7f9924c9a021540aff8c14c9a021540aff8c1889a021540e7f932645a021540e7fa22645a021540efb932505a021540efba22505a021540affacc4c5a021540aff8c24c5a021540e7f9924c5a021540efd9324c5a021540e7f9914c5a021540efb9414c5a021540affacc485a021540e7f9c9485a021540aff9c3485a021540e7f993485a021540e7f992485a021540e7f991485a021540efb941485a021540eff131485a021540aff8c2845a021540efe9c16893021540eff1c26853021540efb9a25053021540aff9ca4853021540cff9ba4853021540e7f9a94853021540edf9a74853021540eef9a64853021540efb9a44853021540efd9a34853021540efe9a24853021540eff1a14853021540a7fcc16e5a520940a7fcc1655a320940c7fcb169593209408ffcc16e9532094097fcc16e55320940a7fcc56e5a120940a7fecc655a120940c7febb655a120940cfbebb551a120940a7fecc64da120940c7febb64da120940a7fcc564da1209408ffccb54da120940a7fdc954da120940c7fdb954da120940ef3d5454da120940c7fcb568d912094097fccb54d9120940a7fdca54d9120940e77da554d9120940e7dda354d9120940c7fdb968d5120940cfbdb468d512094097fccb64d5120940a7fdca64d5120940c7fdba64d5120940e77da564d5120940e7f5936855120940afbdca54d4120940ef3da554d4120940ef9da354d41209408ffcc56e931209408ffccb6953120940a7fdc96953120940c7fdb9695312094097fccb6553120940c7fdba6553120940cfbdba5513120940e7dd9568d3120940ef9d5468d3120940e7f5956853120940efb5546853120940efb5a55053120940a7fdca6561120940e7bda95521120940a7fdca64e1120940affacc6953020940aff8c16953020940e7f9a99553020940efb9a55513020940affacc6853020940aff8c56853020940efb9546853020940efd9536853020940aff9ca5453020940e7f9a95453020940ef79a55453020940bfb9c45453020940eff1a15453020940efb9a55053020940ff99535053020940efb9a15053020940efd9a54c53020940ff99544c53020940e7f9a98453020940 else 0xe6fda68899121540e7bda48899121540e7dda38899121540e7eda28899121540e7f5a18899121540e7f5326859121540ef9dc268d4121540ef9dc168d4121540afbecc6894121540efaecc6894121540efadc36894121540efadc16894121540e7bda26494121540afbdca4c94121540edbda74c94121540eebda64c94121540ef9da34c94121540efada24c94121540cfbdba8894121540e7bda98894121540edbda78894121540eebda68894121540ef9da38894121540efada28894121540efb5a18894121540efb53268541215408ffdcaaed312154097fdc9aed3121540c7fda9aed3121540cfbda4aed3121540cff5a1aed3121540cdfebb69d3121540cdfcb269d3121540cefebb6993121540cefcb26993121540cfdebb68d3121540cfdcb268d31215408ffccb6893121540cfecb26893121540cfedcb6893121540cfeccb6893121540cfeebb6893121540efcdc36893121540efe5c1689312154097fccb6493121540c7fdba6493121540e5fda76493121540e6fda66493121540e7dda36493121540e7eda26493121540e7f5a164931215409fdccb4c93121540afddca4c93121540cfddba4c93121540e7dda94c93121540eddda74c93121540eedda64c93121540ef9da44c93121540efcda24c93121540efd5a14c93121540c7fdba6453121540e5fda76453121540e6fda66453121540e7dda36453121540e7eda26453121540e7f5a16453121540cfbdba5053121540edbda75053121540eebda65053121540ef9da35053121540efada25053121540efb5a15053121540efb5ba5053121540efb5a25053121540ff953250531215408ffdcaaed212154097fdc9aed2121540cff5a1aed2121540a7fdca6e52121540c7fdba6e52121540e7bda46e52121540e7eda26e52121540e7f5a16e52121540c7fda26e52121540c7febb6a52121540cdfebb69d2121540e5fdb969d2121540cefebb6992121540e6fdb96992121540cfbebb6912121540c7fda96cd2121540cdfda76cd2121540cefda66cd2121540cfbda46cd2121540cff5a16cd21215408ffdcb68d2121540c7fdb968d2121540cfddb368d2121540cfddcb68d2121540cfdebb68d2121540e7ddc968d2121540e7ddb968d2121540efd5c168d2121540efd9c068d212154097fccb64d2121540a7fdca64d2121540c7fdba64d2121540e5fda764d2121540e6fda664d2121540e7bda464d2121540e7dda364d2121540cfeebb6892121540cfedb36892121540e7ed936892121540a7fdca6492121540c7fdba6492121540e5fda76492121540e6fda66492121540e7bda46492121540e7dda36492121540e7eda26492121540b7f4c16492121540e7f5a16492121540e7f5936852121540a7fdca6452121540c7fdba6452121540e5fda76452121540e6fda66452121540)) else (if i < 17 then 0x13fb13de13cd13bc13ab138e137113541337131a130912f812db12a6128912781267125612511240122f121211f511d811bb119e118d117c116b115a1131111410f710da10bd10a0108310661049104410331022101d100c0ffb0fea0fd90fc80f9f0f8e0f7d0f6c0f5b0f4a0f2d0f1c0ef30ebe0ead0e9c0e8b0e6e0e5d0e400e2f0e1e0e0d0dfc0ddf0dce0dbd0dac0d8f0d7e0d6d0d5c0d4b0d3a0d290d0c0cfb0cde0ccd0cbc0cab0c9a0c890c780c670c560c450c280c170c060bf50be40bd30baa0b8d0b700b530b360b250b080aeb0ace0aa50a940a6b0a420a1909f009c7099e098d0988097709660961095c094b093a09350924091f090e08fd08f808e708d608d108c008af089e088d087c08770872086d08680863085208410830081f080e07d907c807b7079a07890778074f0732071506f806db06be06a10684066706560645063406230612060105f005d305c205b105a0058f057205490520050f04fe04ed04dc04cb04ba04a904980487046a0459043c042b041a040903f803e703ca03b903a8038b037a036903580347032a031902f002d302c202b102a0028f027e026d025c0233020a01e101b8018f017e016d0150013f012e010500e800cb00ba009d00800063004600350000afdecc6c9a321540afdcc16c9a321540afdecc6c5a321540afdcc26c5a321540cfddb26c5a3215408ffcc1aeda221540afecc1aeda221540afeecc6cda221540afecc16cda221540afeecc6c5a221540e7ed936c5a221540afedc32c5a221540c7fda2aed9221540c7fcb168d9221540e7ddc268d9221540e7ddc168d92215408ffdcaaed3221540c7fda9aed3221540cfbda4aed32215408ffecc6e932215408ffcc16e93221540cdfebb69d3221540cdfcb169d3221540cefebb6993221540cefcb16993221540cfdebb68d3221540cfdcb168d3221540cfeebb6893221540cfecb16893221540c7fdba6493221540e5fda76493221540e6fda66493221540e7dda36493221540e7eda26493221540c7fcb16a62221540cdfcb169e2221540cefcb169a2221540cfbcb16922221540cfdcb168e2221540cfecb168a22215408ffccb4c9a121540a7fdc94c9a121540c7fdb94c9a121540cfbdb44c9a121540aff4c14c9a121540e7f5936c9a121540aff5c32c9a121540aff6cc4c9a121540aff4cb4c9a121540e7f5b94c9a121540efb5b44c9a121540e7f5924c9a121540c7fcb268d9121540e7ddc268d9121540e7ddc168d9121540a7fecc6899121540c7febb6899121540c7fdb36899121540e7eecc6899121540e7edc36899121540e7edc1689912154097fccb4c99121540a7fdca4c99121540e5fda74c99121540e6fda64c99121540e7dda34c99121540e7eda24c9912154097fccb8899121540c7fdba8899121540e5fda78899121540 else (if i < 18 then 0x3d573d463d113d003cef3cba3ca93c983c873c763c653c3c3c133c023be53bbc3bab3b8e3b713b3c3b2b3b1a3b153b043adb3ab23a953a843a673a4a3a393a1039ff39ee39dd39cc39c739b639a539943983394e393d392c391b390a38f938e838d738c638b538983887387638653854384338323815380437ff37ee37dd37d837c737b637b137a0379b378a3779376837573746373537243713370236f136e036c336b236a13690367f366e365d364c363b362a360d35f035df35ce35bd35ac359b358a3579355c354b353a35293518350734ea34d934bc349334823471346c3467345634513440343b342a3419340833f733e633e133dc33cb33ba33a933983387337633653354334333323321331032f332e232d132c032af329e328d327c326b325a323d322c320f31fe31e131d031b3317231613150313f312e3111310030e330c630a93080306f3046301d300c2fe32fc62fa92f802f6f2f522f292f182f072ef62ee52ed42eb72ea62e952e902e7f2e7a2e692e582e472e362e252e142e032df22de12dd02dbf2dae2d792d682d572d462d352d242d132cf62ce52cd42cc32cb22ca12c902c7f2c6e2c5d2c402c2f2c062be92bd82bd32bc22bb12bac2b9b2b8a2b792b682b632b5e2b4d2b3c2b2b2b1a2b092af82ae72ad62aa12a902a7f2a6e2a5d2a4c2a3b2a2a2a1929fc29eb29da29c929b829a7298a29612950293f292e291128f428d728ba289d288c286f286a28592854284328322821281c2817280627f527e427d327c227b127a0278f278a278527742763275227412730271f270e26fd26ec26db26ca26b92690267f266e265d264c262f261e260125e425d3259e258d2570255f254e253d252c251b250a24f924e824d724a224912480246f245e24592448243724262415240423f323e223d123c023af239e238d237c236b235a235523442333232e231d230c22fb22ea22d922c822ab229a227d226c225b22322221221021f321d621b9219c217f2162215121402117210620f520e420af209e208d2058204720362025201420031fda1fc91fb81f9b1f7e1f611f441f271f0a1eed1ec41eb31ea21e9d1e8c1e7b1e6a1e591e481e371e0e1dfd1dec1ddb1db21da11d841d731d621d511d341d231d121cf51ce41cd31cc21ca51c941c831c721c491c201bf71bce1bbd1bac1b8f1b721b551b381b1b1afe1ae11ac41aa71a8a1a6d1a501a331a1619f919dc19bf19a219851968194b192e191118f418d718ba189d1880186318461829180c17ef17d217b51798177b175e17591748173717261715170416ff16fa16f516e416df16ce16c916b816a71696168516741657163a161d160015e315c615b515a41593158215711560154f153e152d151c150b14fa14e914d814c714b614a514941483147214611450143f142e141d140c else 0x66fb66ea66cd66bc66b766a66695668466736656664566346623661265f565e465c765b665a565946583657265616550653f652e651d650064ef64de64c164b06493648264716460644364326421640463f363e263d163c063af639e638d637c635f634e633d6320630f62fe62ed62dc62cb62ae629d628c627b626a624d62306213620261f161e061cf61be61ad619c618b617a61696158614761366119610860eb60da60bd60a0609b608a6079606860576046602960185ffb5fea5fcd5fbc5f9f5f8e5f7d5f6c5f5b5f4a5f395f285f175efa5edd5ec05eaf5e9e5e815e645e475e365e255e085df75dda5dc95dac5d8f5d725d555d445d3f5d2e5d1d5d185d135d0e5cfd5cec5cdb5cca5cb95ca85c975c865c755c585c475c365c255c085beb5bce5bbd5ba05b8f5b7e5b615b505b335b165af95adc5acb5aae5a9d5a8c5a6f5a5e5a415a245a0759ea59d959bc599f5976596559545943592658f158d458c358b258955884587358565845583458235812580157cc57bb57aa578d5770575f574e573d57385727570a56ed56d056b35696567956685627561655d555c455b3559655615550553355225511550054cb54ba54a95498547b545e5435540c540753f653e553d453c353b253a15390537f537a53755370536b535a5349533853275316530552f452e352d252c152b0529f528e524d523c522b521a520951ec51cf51b251a15190517f517a51695158513b511e510150e450c750aa508d5064505350425031502050034ffe4fed4fdc4fcb4fc64fb54f984f874f6a4f594f484f2b4f0e4efd4eec4edb4eca4eb94ea84e7f4e6e4e514e404e2f4e1e4e0d4dfc4deb4dda4dc94dac4d9b4d8a4d794d684d574d464d354d0c4cef4cde4ccd4cbc4cab4c9a4c894c784c674c564c454c284c174c064bf54be44bd34bc24bb14ba04b8f4b7e4b6d4b5c4b4b4b2e4b114af44ad74aae4a9d4a804a574a2e49f949d049bf4996496d4944491b48f248ed48dc48cb48ba48a948984887487648654860485b485648514840483b482a48194814480347f247e147d047bf47ae479d47984793478e478947844773476e475d474c473b472a4719470846f746e646d546c446b346a246854674466346224611460045d745c645b545a44587457645654554454345324515450444e744be449544844473446244514440442f441e440d43fc43eb43da43c943b8439b437e436143444327430a42f942e842d742c642b542a4429342824271426042434226420941f841db41be41a141844167414a412d411040ff40e240c540b44097407a40394028401740063ff53fe43fd33fc23fb13fa03f8f3f7e3f6d3f5c3f273f163f053ef43ed73ec63ec13eb03e9f3e8e3e7d3e6c3e5b3e4a3e393e283e0b3dfa3de93dd83dd33dc23db13dac3d9b3d8a3d793d68))) else (if i < 22 then (if i < 20 then 0x8bfb8bea8bd98bc88bb78b9a8b898b788b678b4a8b398b288b0b8afa8ae98ad88ac78ab68aa58a948a838a728a618a508a338a228a118a0089ef89de89cd89bc89ab89a689958984897389628951894c893b892a8919890888f788e688d588c488b388a288918880886f885e884d883c882b881a880987f887e787d687c587b487a3879287818770875f874e873d872c871b870a86f986e886d786ba86a986988693868286718660864f863e862d861c860b85fa85e985d885c785b685a5859485838572856185508527850a84ed84c484b384a284918480846f8446841d840c83ef83de83cd83bc83ab839a839583788367834a832d831c82ff82e282b9829c828b826e825d824c823b822a8219820881f781e681d581c481b381a281918180816f815e814d813c812b811a810980ec80cf80a68095808480738062805d804c803b802a80197ffc7feb7fda7fc97fb87fa77f967f857f747f637f527f417f307f137f027ef17ee07eb77e8e7e717e607e437e327e217e107dff7dee7ddd7dcc7dbb7daa7d997d887d777d667d557d447d337d227d117d007cef7cde7ccd7cbc7cab7c8e7c7d7c6c7c5b7c4a7c397c287c177c127c017bf07bd37bc27ba57b947b777b667b557b447b337b227b057af47ae37ad27ac17ab07a9f7a827a717a607a4f7a3e7a2d7a1c7a0b79fa79e979d879c779b679a579947983797279617950793f792e791d790c78fb78de78cd78bc78ab78a678957884787f786e785d784c783b782a7819780877f777e677bd77ac779b778a77797774775777467729770c76fb76de76c176b0769f768e767d766c765b764a763976287617760675f575e475c775b675a57594758375727561755c754b753a7529751874fb74de74cd74bc74ab749a748974787467745674397428741773fa73e973d873c773b673a57394738f737e736d736873577352734173307313730272f172e072cf72be72a17290727f726e72517240722f721e720d71fc71eb71da71d571c471bf71ae71a971987187717671657154714371327121711070ff70ee70dd70cc70bb70aa70997088707770667055704470337022701170006fef6fde6fcd6fbc6fab6f9a6f7d6f606f4f6f3e6f2d6f1c6f0b6eee6ed16eb46ea36e866e756e646e536e426e256e146e036df26de16dd06dbf6dae6d9d6d8c6d876d766d656d546d436d326d216d106cff6cee6cdd6ccc6cbb6caa6ca56c946c836c7e6c6d6c5c6c4b6c3a6c296c186c076bf66be56bc86bab6b8e6b716b606b436b326b216b106aff6aee6add6acc6abb6aaa6a996a886a776a666a556a446a336a226a116a0069ef69de69cd69bc69ab699a698969786967695669456928691768fa68dd68cc68af689268756858684768366825680867f767da67bd67ac679b678a677967746757673a67296718 else (if i < 21 then 0xc7634d912463fc5a820791b8d5640128ea0820a820b4104006820d41041504105410486420a820d41040e3416820b4105a082d04100000034106c6836341b1a0d8d0646810f32009486521c82089901288d7c39041fb6cc80251e8d022084c81105a340882d1a044128d0128b4681105a340882d1a04416410720839041c820812864683234100102411af8720826521c820e640220819b3200ec6a3599004a3c820e41072083904151a0800848643e301a820e9001a080d03a40068241c0f8c050702e301a820e9001a0bc6035041d20034178c048643e301a820e9001a0bc602e3005804a302e069120e07c6028381f180f8c07c602e301b1802b0251d8c0170128ec600b8094763005c04a3b1802c025184906a0832400682f180f8c05c600b8094605c0d2202e0691010840b81a4405c0d2202e0691017034880843d91d702420d24a609a5f8a5e7a5d6a5d1a5c0a5afa592a581a570a55fa542a531a520a50fa4fea4eda4dca4cba4aea49da480a46fa452a441a424a413a3f6a3e5a3d4a3c3a3b2a3a1a390a37fa36ea35da34ca33ba32aa319a308a2f7a2e6a2d5a2c4a2a7a28aa279a268a24ba23aa229a224a213a1f6a1d9a1c8a1aba19aa189a178a167a156a145a128a117a106a0f5a0e4a0d3a0c2a0b1a094a083a066a055a038a027a016a0059ff49fe39fd29fc19fb09f9f9f8e9f7d9f6c9f5b9f4a9f399f289f179efa9ee99ed89ec79eb69ea59e949e839e729e619e509e3f9e2e9e1d9e009def9dd29dcd9db09d939d829d659d489d2b9d1a9d099cf89cf39ce29cd19ccc9cc79cb69cb19ca09c8f9c7e9c6d9c5c9c4b9c3a9c299c0c9bef9bd29bb59ba49b939b769b659b549b439b329b2d9b1c9b0b9afa9ae99ad89abb9aaa9aa59a949a8f9a729a619a449a279a169a0599f499e399c699a999989987998299659948993799269915990498f398e298c598b498979886987598649853984298319820980f97fe97ed97dc97cb97ba97a997989787977697659754974397329721971096ff96ee96dd96cc96bb96aa9699967c965f964e96319614960395f295e195d095bf95ae959d958c956f955e954d953c951f950e94fd94ec94db94ca94ad949c948b946e945d944c942f9412940193f093df93c293b1939493839366935593389327930a92ed92dc92bf92a2928592749263925292419230921f920291e591d491b7919a918991789167915691519140912f911e910d90fc90eb90da90c990b890a79096908590749057903a9029901890078ff68fe58fd48fc38fb28f958f848f678f628f518f408f2f8f1e8f0d8efc8eeb8eda8ec98eb88ea78e968e858e688e578e3a8e298e188e078df68de58dd48dc38db28da18d908d7f8d6e8d518d348d238d128d018cf08cdf8cce8cbd8cac8c9b8c7e8c6d8c5c8c4b8c3a8c298c0c else 0x21b32462682080c84314228a15c50f8d02b8a32eb7c0fc6b8a1019080c854c81104c380882f1a044158d0128ac680d04032107b044101a08206820b4105a0820054106a08243212190d8d05a082d0416820800d0416820b4105a083e301a820a0e05c602432141c0f8c05c60363005c04a3a820d4106a08206810690341010840b81a4405c0d22021082bf5c090834908643a4006820340a0e07c602e301682083385a082d0410110838f6af5c00b900882d0410190d41040d041009080487208203c101e0b4105a0820221019088704064203216820b410415041682081a082d0416820b8c07c6035041920123178c0548048c4e301f180e4303e8128f20826521332044178d0220bc681104e3404a2f1a044138d0220819c35041a8607d0251a9485a082d041b1a044cc8025219487208363408999004a43290e41040b4225210190e6403d0128f20826be1072044178d0220bc681104e3404a2f1a044138d022081c80945f6d99004a302d0e410419041c820e4106c6826461b1a0e640369918c0c822be1a820fdb5640128c1802a6404a26820b4105a082a6404a255f0d41054c80944abe1a820d41044c80944abe1a82080c86a1aae01f07f6d59004a3ab8ac80251f905640220c06420321532044130e0220bc681105e340882532044130e0220bc681105e340882f1a04412990220bc6811042640882f1a044178d0220ac68094563404a2b1a025158d012898701105e340882f1a044178d0220bc681104c380882f1a044178d0220bc681105e34088221c044178d0220bc681105e340882f1a044110e0220ac6811056340882b1a044158d02208150416820b4105a082d041000150410541040d0416820b4105a082d041d1a034168d01a0b4680d05a340682d1a034128d01a0b20820321d1a0d410548c225219230a0e0506428321a820a9187468350415230e8d07468350415230e8d0506428321d1a0e8d074682022101108028120b20826be132908120220bc680945e3404a2f1a025138d012884802240171a044158d0226640129332011040221c8209948419041c82081202208248094412405c2332025102b83c880443904135f0e4107edb3200947e340882332044178d0220bc681104e3404a2f1a044178d02209c6811040c820e410419041c820d8d0409436341b1acc80251d8d07208212410340f8c040b81a45e30171802e025188803d82200b9008822be1a820d6402208180200a04825290b4105a082d04100502412af86a082a52100502412af86a082a521022089486a0820ae0f2202d08028120957c350416820b4105a082d0416820b4106a08200a048255f0d41054a4350410190d4354103e8eb2011055900882ac804415640220806420ae0f22057079102b83c8819ab20110643216c806d9231d8d3644918ec69b2248)) else (if i < 24 then (if i < 23 then 0x1a04848c89634de924630190d6ad340218ff169a010c7f8b4d00863adfad503f1d6ad340220c1e301f180802852083e301f18090c86c68200000e341000587c60200050a4107c603e3012190f8c06c68200000071a08260833041982090c86608330412190cc106608330419820cc1044880d0460c13020823190c8d67a01a172a426041cdfcd50441b9007c603952111c034165484c1839521b180c8d05004c8452341cd5079167a2191908f3571a010c6e401f180e5487c6022381382080087c603e301f18090c87c603e301d20034123401a0b4800d05a400682520034169001a08a183e301d200f8c07c602e301f18090c87c603e301520034100f81a0b4800d05e301920034149001a0a4800d040d00682920034149001a080b81a4405c0d220210817034880b81a440421069034100f81a0bb541104841a40d0a5041f180e9007c603e3017180f8c07c60350c1202080f05a1828321ec8ef4071017201105a1820321ac8072154304001210090e43040702d0c1019080f050642032106803d12c104864200a1010c840142001e0cc1066083a401021083487b23bd04841a4804210690f6401e89180f9348020ce16860b43040f03f8a1ca0883f1a0c904418db05c681105e3599008831b6080f82209c68110408790c0f8068403c0e4304190c132131c044185cf8d0220fc68110436c171a321178d022086d82172e3408830410b4305a182d0c106430404820241037088876403c80b900882d0c1686080c84088206e1a86081b840f0202804e255f0d43054082d0c1686080c86b20110550c1034306a1820a860d43040d0c1034304024203210190804872182832101c0b4305a18350c151c01f154305a182d0c10120b4304064216c11360adb0407c11051780f825b6080c84408283214190e8d06a1821eea462d1a0a0c850643a3410190d6a83c88864207b246249212103d180285a18200543040d0c1054306a18200a16860b4304006860cc1066082d0c10890cc10660824321d200b8c07c60350c1d20034178c074802e301a860d43040d0350c1a86090c864800d04068101f0341010840b81a44042102e01f1034f6409081e81a174803e3017180b4304cc8094438a1f1a044138d0128bc6811041b3e340ae31c5086cb8d02b8dc68394110638a11c8f1a057183902b89c680944391e340ae31c50b8d02209ae0564094605a1019081906a0820961532025134105a0820682081a082d0416820e4107468350414190a0c8506428321d1a08248444015c11005c80321022082486a082092104b0802812094a42a0c16820b41040882d0416820b410406420ae0f22219086c836c918c1b409455041054105a08206820d41048642d041001a0836341009080c840243904101e0d4106b7c15c0fc0948d041682080f040642d0416820b410403 else 0x642832141c0e8d07468283810df085484ca42124135f0849044843e3405c21210f8d0170bc680b842421f1a02e178d0170bc680b84e340d2209209ef84ea421cbe3423a90f8d0128ac68394412413a90f8d04f7c2002502e178d012880942fbe1b1a332178d041a7c6841241001705c6820d2171a0f8d0170824827be1b1a0d8d040bac6856341f180691017040b82244102e0a0c840b8205c102e081705064205d50424210a1084397c68415210e5f1a12d48419020c810e5f1a1690056a421cbe342d200ad4840b42432102e08d484864205a10e5f1a1290874802e340e421320c9086484324219210b414908ac6824381b1a0d8d06c681c841cbe3420e521c12d4840942438103508028508420e414210a10841c828421072081a841a687043be1069f1a107b041cfc685a400d22002d041c820de10720f8d041a7c684bbe152102e178d041a7c684bbe152102e1015074803a401d200815041c820e414210e900348b4801a45a400d224210816040bac68405d634202eb1a1016040b020d32422f1a0834d0e0977c224205c253221c1490034880b887043521003904084200001c82042112109d4853d83a341c820a0e050703a340d223df0c8d06468205790420e5d1a164159008ea42643904251a0e8d041a746847be132106916415900ac801a44056a342c820f8c034881c820e41f18069121087c601a45e300d22f18069178c0348908420d20e62f18069102783c81a0cc1826041f18081703488443b541e40d08a4406825060a81054880d04a0c1502089101a094182a04102208830404c39be0a407e0684007098104c880d040f6088202f0f8c04c0820013098e0220bc681105e34088271a034178d02209c68110403c18c9521d1aaf40342a8106b5548746abd00d0aa041f18083d8220ab5746abd00d08a041268034178c07c60200e1adf05203f034268d054082032107b044103d8220ab7eb5411075bf5aa07e3000a07c60202814860f8c07c6024321b1a08000038d06618330c1986090c86618204411020f8c05064203c101908810737c130c8410c07ca0061306080686c68207a6462322034166a83c880b43e301306083c602e34101f044178d0220bc681104e340682f1a044138d02208c6407c5f8b8d0086302d0f8c04c8c3e30107b0441000282e341f18080e182a3806825060a8e01a094183e301ad5079128e01a094183e301f18080e044183e301adfad503f1817854700d05e301286080507c603e3014190f8c0400c223803e2d1a0a83074683a301d180e8d0746020d15e9a343068034168d0746820321d1a0e8c0548c3a3411020c918648c28d0068292309430506428321d1a0e8d074683a34100d0e8d0548c3a3410190d6a83c8ab541e455aa0f22ad5079156fd6a81e8c864207b2462b1a6f49231d8d05cc918dbd0) else (if i < 25 then 0x3d4216e10b70a108508421ea10210803d422ea102109af842242001f09af8407c2112102e0a0c85064390c101f0a0c844e4283210b90a0c842e4283212920aaf84470324216860c9085a18217210b908bb86a1833701bb609db042f0212415b6089104864208816860a7b82208864350c10543041c4224210b90a0c85064217210950e8d050c83a341432085c842e421be1024090c84054205c1d2052102e180fca08aa184844a72242b7030b90810842e4227210210a90e900170c2f04e5484607a1921069178c07c603a4014320b8c04008803e24210b4300f8811007c4842104401f134300f8a486c601a47e3405c207b084a82b88c18260c11210a8304338200a14210864850842192121908ac84864226410d9086c8436421b2108608370648422b2a4220570d912acaea8128c364204210d908ac8400421121085484ca4266400a20070a4484198200e11490d8d0503022b2132908a484224283213210691294841b8205c1921b2002e1c90d900170c9a00944a52180ca82103d841c820f610c9090c8436421b2121908390486421b21219086c84864219210c909108488422b21a820ae284488243210570a6c82b89a0824321a820d410432c378a13c508032c2442109502e1110842540b84242109502e109086a08212414210a1084257c68415210c90a108432428421052084af8d081c8222419210839042482432102e0d4104864222419210c9086c68363415490d4106a08243810c9081084324229210210d410a48aa083504121c0816a4205a100058486421b212190ad48486424321b1a0f8c05485c601a47e30141c0a0e05c602005707212108415c1c85e300d22421082b8348bc601a4410c13060805854182d04158609c30437c210c10240a8305084284210eef1a10430441821be181c08028401c20489080384224230c1322005124481308d7c211210050a0c84588202c16820e8d04387c68400a1f1a0d0cd0e0ac6820481122090c840982d04105900488420a82080884212a106909510908687021241421084a84257c6841be14210b8d04077c684124121908388444832421a1c0d41041a4010210840bbe10ea086c8402c243212190aef8409020281f180943054683a341095096f874803a401d200a0e0508420d2141c084a84014284210690a8d07468215213a90f8d07c680b841cbe3423a90a0e056a4275213a90f8d01708bd81cc4a6400a2066097b0398b4682a4211320a0c84f7c1cc40d614190bef85f7c21d410050838841c820e21034105a082d0416820b4107c68243210640832044a420e412190f8d040e341f1a081c6824321b1a090e06c683634121c090c848843e3405c2f1a02e178d0170bc680b844421f1a02e10390477c21ec15df0aef874683a341d1a0e8d041b0283214190e8d074683a341d1a0e8d05 else 0x397c6847041f1a09c304010413820872f8d08e083e3410260f8d0170801c2a041268081704248284214210872f8d0820821cbe3425820872f8d0960821cbe3425820872f8d09608200e1d200e90051a0200e15820ac1056082b0415820ac104248205c14190a0c84608203e1f1a02e1072f8d080b42014171a01f15900541820d1a096c0140947146440cc12d8028129087468222419210c90864842d522422921088e04028370c1b860a0c86e18270c050200a080568d0b468205da342d1a0e8d074682b04100b0e8d074683a3414320a190403428321d1a0e8d074683a34100d0e8d00f88090223214210a108407c3e3415860f8d056183e341586081204618203be3420d8081478d081a400d22111121100f864840b8524205c212102e100b0407c23041000f8408420001084003e10030d8d06c6824641b1a080184034205d634202eb1a1017119080bac68401a100d0834c908848421121109080f840006121908038400c200e1a19a32178d041e341050cd8d0888420d3e342069f1a11108407c203e11210834d19081a7c685e3410140809a01a45e300d22109090c8407c205c102e090c86c680505e34101da3210170401c200e1b1a0d8d048643634100708810407c205c1003080186c68363412190d8d048c82006100d0cc106608330419820cc106608201a101f080f8488436400d22b20069111084c801a456400d225860ac3056182b0c1586080f8461821b010e5d1a143404e0827041321ca9126c0646832341d1a09c304c841a45e3014320802a8d0b46839521069d1a1002b90090c8286413820b9003488e183e300d2201f08348140807c3e300d224210f8c0348bc601a448421f18069178c03489aa407c460413020a810420822041329099918c8922407c48181322014124480f88ca4211210140a0c840a52111c0c9085a182d0c11210b8d044882432101f0b4306a183a341686d1a134368d082a420481219083884054203e1b1a0d4306a19c68550c1a8671a100014243210050f8c04a083a401072084a84aa42e3010690e8d050842d0c03e21210b4300f8ac602242101f080f84484200a1082098104ed82a041582083c87c6810c412a05c2079080f841e42704101f086f84208260410920a495db09248283215020a108508421cbe3420820d43042f0208610bc0872f8d0807c228219210b430ba895d4350c10bef1a108c85084216e14210a10842dc284210b708750486422ea1e86121107a84)))))
def lev10 : Packing := (2118,5,7,0,0,16,0,data10)
def hash10 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x86a9a94aac104b3dfe06340f8f00fa4b2cfc8950a980c02559bcb1d2a08f0d0205d79156c7bd990c25605378a44ed98e9a259948f8211c305580002fc0190fcb1412cda9bad609390001519f95611f084c8b511059e1761fd04251592f491c7383e8eb1071290dd9e3095d1152cda8df612d5081010ba4e99cf588ca806b19ee0a01f19c9fae09c034a30ff50d604da321112b1fd421ca8d091ab028df3ca94c85ebc7e85005c03f40dc84c312041b9947d7fd70d41d670334ca18397e96d5199d7d7f5d386780bd1d08e9cc8d45ff90297858b8154f8cead31c56c4c4a00b24595cc56fdf100a9a078181c1300007610d0181006080401000110380850070706c08020280c040017824be0e0084402001b814007c059c81631028440004050f4640e07108142e200b00a4c002082c2a15814120506020001a0e04004004a808041e201a02e00361f8001f0012c00a6088d802000a0002a0a0002c0075100043e4d058501e05010480809008004000034f017c1018440000028001a040506432010700022060f8000e030504427470c2180a0f050d05c090000012000185094200100048081f00c001f15868680502818029b688618006348200c0600805fe0111004000d0097400aa0815078031586c2c14220540001118200800050001400068c42a05020d8405c00164024b090507a000081008100a0009e114a85816070d0080e382e80c184b028342c00018001220030300a0000800023100034000a03ad8463f010644c0200054000903000002a0108c420a020580402008bc20030000822620181c6c000102846030294400010b00c0000098d000000000c880303008e605000242805048003e0d080503220001600e00058016e00010681000008000c09028b41c160001016110080c080001148000e0c8600a7f2c0d01607048140602020085e000686410070985c2e0703010081d0d14018140381806030980c10370302c1800160100e012913c000402808140a058241e0a0084428360080812000a12c52010000002250300014060187c0243000000002008000209000142400040000c000282000032784858010d82006010003800000082c0a2201014200100074b80b010041c03050000205000001c0002878000200824040e010ac000301008160a0200410770080c4c0701010020f0300808000186038001803c08020280424000200022010000026080d058620001010d0100500000021000402230200c2202048e01400048200007028140200000080e190e00004020000042090a00404020480416070402c181a0608834150181008021f80806040300896000382800070000c24130f004000b040000e0000800000d0482810010080c36020c86806010002402000180000010c0200401050140819028080003010042a03018000000 else 0x42d0180000007f4000b85004c58421dc82d0d7c35d024000001d947253f4000001e2c0002c94c05b5c4034dad4f0400000066174c000e5d1a14880e00017309c4001a05191440de57ec0017e53500019018450e9d412c051000000055dec4e7d6511d433d96903c0715216c03a408dabc9bd759b4c000808001f05795cf08345e1be09598dc00137d22d228ad18243545b0b05eb1415b59b0cb801881c0875e551858e0aa4550001a50dd4f1000094dedc00198c0009246c40007a0000c0448597e0994a9fa9f18060000001715dc4be4f605a0001669fb8000000c200890ed4994511bcaec000ab610c000c149140002dc0fc0016b0001710002011e3cd41db4fc03a80012e0000d0d7b5c95c38000000de18c08c148c6385f800000025967da74905cd05ae0d80214e8001c91214220e755dcc3cd8c9ece04491425f301202386d4099e013b9b540008ac000001d04001bcc47568d061c5d9287b420c7016a1239d503486220d17a03840e8d64b002443058bd0b0abca7846479539580dd695da0092995382be0810a416ce582e5121e44b4104ca61d79620ec4f180951191dcba01dd6849a19747fcdc4bc41117f8a1d8056cc294cb60b125db5dd85801194a104083ed3190210bd0f0c75510b5c7e45057382add6db8d7dd9d438908cc1c2e02b83b5371b907a512d38ce4445cba82e857ddcc2013306187299992f000142932c78c000e70b0df69695f2c83994987995017dd550ddecc22c14c000f38001205f20e9e0d59144d9f341a9d2147575c04145c0807709add35344a05b84ee8aa1e9c0014f579d334e651fcd24314a0c555adc14929c2b4ca54ec2b1435f74524000171a7d000c38cc60b4d794652798091e04a801d174c8d3f00004e4001a9800149c895c0c601ffcd15d24d49a11ef0001b74d956d991200d039db1f78419c70ab97acea0934849754c293d0eb4c48e2ce08f98531310675fe54e1139e157f0000c90000b91e74b294fcbd15f55608693d58d5a393a9ed1208199d74f9116e088a5c909830fc4899f4d8fcbddbf41c83681f4b89594359ea1d4ce8cdd07c0720f25b01bd1da5658d308512441e1e7c0004ec8b54100000eda45a69c188f436034477c5e96dcfa1e38045874b545ec988d3cfe46b8001c4475874d99c4ac469de00007c570994c931b418a4964c5d2e8001064f7ce84be1cb9eda0a8000ecd0d83392c947063c4f9c1d7b15155a5ca51540298559dc0008fca159f0108000001d1c3bc8b0acd9fc08524c53c00000027c000c01ba1dfc0e41bcd54a35b354f1954821c81944570688ad939c9719042ed654b7d5d1c8405da41979c09101d0d8718f5a707d80513f9e8cd8181500896070cfdc3b9819764f797051600c4a59fc0ef41e48cd338494a2917d829bf0a2d5b03f9b28c60f54391bb9549c0550) else (if i < 3 then 0x65d254ec8e4d408401fdc67d1f09b56189a400000096c001a18b6003922482de520788a9864299fa6095b6089d1105817c873c02ce603fc89085c114e54e14000cb00018e4ce118c0012ad01c0016a5cc0c56044af8001cfd129c8c000f64bf930d8cd05087164de28001d9800009c0000020c0000a504c0001361dd4001179b240a0e6d4d039ddf8aaa0e95c41604a0754a9044c7517716f476cdfca9d1689b1bd5634000a85445074864a7df9915013cae4745ec086142cf493485080000010956ed8a92b8f34b380004d51b4f0d23c769599b09c3c394461bec26cf692e5e8513d1f5f0c001a5c6e4168f8587cd70f300000d5a843507197c098d2353e818088497c37d72c99c6d19091e48e1769665bbc1741a5f5011ca8847d7513212516c9e599a9d12021b4886ded4001a2cc70615030001c2052c00000000179862db195f01d4cece40000001ac0cd80019b02a4001a20000f9dce4c3410031c0011a46ca0c9e6480d268dc1485460979170cf6070cac8e5314000975d60d519401d0edc000854000f21efc608024ec0079cb4b70f4c270fbc000000cd4002034dad820bc8000a380020ed3b09f44fd3ac62992de68b8e039985cb1148c9d8857e14bdfa17cd2813c093d89609004a0695e89556e9ff40000014adf6c1d8919e61f8c000000001d599d89f894032c06c00dba44b0ed5eac8800000019ac0020ac0006988bc5389fc0007b05c47140015684153a4bbd124fe8321b79f718a0000d098b522000066800178c0000000000740000015a0000561dac0000000008188dddf50d21047910f9e70b659f909dd8181c6ac8ecd615316306d9165bf94209a86f89698490e46c19d1f1c804a40f080105981e8741fe8fa80ac281d9cf890ac438da0529c6dcbc00061dd19780be973d8d0814611034f159a1d3d4c92d9700810f5087986d54d589a3c478bfcc513a13dc27576c0b8b68cc107958ce800d0c6c87d7a9cd80000006a1b810a9130001e2419c75deecd918d91d99f4000900458ee4001644001e10000e3cb6cea8d4dc69aa5525231054000000001e94e28db4fb608591df559cc000000000435c4c9909c0000cf206c00151c000b49f5c230fd586a058bc00646ed8980006bc9e4c893e164993cd38bb42840000000010415f9fbd4f8f709c9afdeb934d4b48d4b7589030d3d9f65c540c959c440d9c00143c2a1551e79f592b40012020f050c13488d7747d0208ae04d1bc0ff03e1935ff1f45cd58b049dddc44864d2bd5cd7353645487acb1803c001d5c1260a52edbdd9e86807dc0002cce94410001b2000121cf944a4afca24b44ed04e800100ccfc2f1b106f1bb42181857443642a96bdc2c0010cc002055e41939d720dd5917d8784665d30e5158443c145c00a1848111c000521d890c8264000e19c7c001640000ce4000 else (if i < 4 then 0x5dbd3c520d57c781b45f492850441cdbc9c5000186023d6285905d596d72065466c920bb865854cb943b03cc641d28e90ab1b0482841c83cda5a49964af5b695291092949817a55752592f94d5b94d2e03cd6c541ea4945a01b89dd165dc9d28da9cfcc33031a0fd8c99c18acca832a0f5aa9625f394a46319596a982e029ab8589b9c7e0d1048d36d405f7c46de4c4f60020bc379e6daec59e031058fd8a4d9a465114cfac24e025535565e88cc8bd505e0b92a4a68ad41f915c1ed2118f1f80bf15fd494c0d678baca488d054415812807daf5835c58f3d7287c9a4dca146c6e13e42247980cc93a114f6d614adc7489b92dcd1c72c4b9545ce14698f8f59398139740584b78e79ea8de926ccbdfd8f28cd06fd33d60c240e360754b9c4829cf2dda87d4fd1a3427906c04dced5403c95a8889675b515b4e0c7a91356b5de95b95c14e4af1275a78430a550c5e1c36d7b8c4cd69145374b591c55016adce8e68470014005ad1ef8c08e1c9e1a817d1304bb056883025e109fc96983d9d9128a060e88709f240a4d852d1431880f447f92fc9989d97c41fc5a5cf9a92049f9dae4c316d1261a60564a71ded69d84d925691248b34d5c1b06e9859381e81e18ebc2f85f5b3060c2c051c1914388a15e15d4dcd2c55bc23571c38d341688c113bcb98ac0ef1fc5be4f5d4c4228fe19b8694ae8bcc6847882d4f40d994b18887ed50d8103d45d0454b102889cc5cc5bdee8845de4c41a0c9d5df1600450734df1e9135c5f1c75555ac9fcc5a995d358300d882f4d20d196801790a08c5ca88d84e1458d353260e43e429013208e02ddb87781ac9955c9ae1b39309cac1404cce24beccf83f1931b1dbb14551a95e53856e5c245e43c4dbd63869177d53cc68054eedccc7ba0f8ccd71a07cb08489af890d3684bdb7cc182696614199196b94cc71ca750e1acc4041b858cb314d90886498ede0c6dcfb9f28a3ce3985dc283a032476480079db15b703d16c48a47f1ad98c40f05ddd14579c9868d02c625479a59449bfdd645fddd9a085d9aade49fb51c20e1180f75c644b5504bd89f11ac308068bf583c515960009a64a6dfb1aea0cd0f44dc0000004f02055808b87cc001eb5240ee1bd8985ef50c0c801b4340c44ea4ef8ac9ab492c0017d4910645a15aa069d3fcdb178857438018d14107cd5966ce3110d0b9e09a28825098d05fedf1521800005a018ff8000b22064001af0ffd3c8000000d74b4d9201a00020c52a93ec40d61db64761f846706cd571b2c0f5579d446b40019802da01c001c140903dda1dd2c519be989d52c031e35f41300db8118858c98cb940d1891cddc1490fec15ceb9c78928c7c9e8001559ec8ac4001ee4000248250ddd6e14810495ac000374f81c88000001355400df80b00003ae10127d725b3df00e20d28a64c2c8ca0040 else 0x16449990c1505c93285b91b80b51e8efd988b9cdede04000a21e5c7053891c90b5d49a88e0081d085c116f0f1c370215f88fb17bc948534c786a51f963c6057780015ecdc8c940d8711a5477400000144c001015ee0260194445850e109d1a6d62d9c59b42c54a20511ede98cddd01264428001271b6d3cd6f89dc000000001ba8000001c34000001d8d841f90001c61ac5d08841e21da0a08ce8df57494dc7311b01c40013b40a8000001cdd19dbc400106a014c6400000039810d9703c0e486f555d9e)))
def idx10 (h : Nat) : Option (Nat × Nat) := let a := h % 706
  let sh := packedAt hash10 (a*9) 9
  some (packedAt hash10 (6354+((h/706+sh)%2332)*12) 12,0)
def data9 (i : Nat) : Nat := (if i < 1 then 0x42a051bf766bb6998508540b33e6ab30d330a10a8127ddd9b31b568c215021fb9b8dc36ad1842a049f7371986d5a30854093ee6e370cab4610a8127dcdca219568c215024fbbb36630ad1842a049f7371b9615a308540b3ae6ab30c2b4610a812f5cdc6d58568c215039e3b70daaa8d1842a050ff36dc56a19308540a3be6db90d2b2610a8107fcdb7298564c2150307f996d430ac9842a0617f32da76159308540c37e65b4cc2b2610a81877ccb6958564c215028fb9b6c2b46c9842a051df36dc9695830854083fe6e374cab0610a8183fccb6a19560c215030bf996d3b2ac1842a061bf32da66558308540c3be65b4acab0610a8147dcdb655a360c2150297b9b6e1b50a9842a0517f766bb69d5308540a2fe6db30d3aa610a8146fdd9aeda654c215028df9b6cc34ca9842a07ac774da85515308540a3eeecd76d1aa610a8147dcdb661a354c215021fb9b6e5306a9842a062f732da860d5308540c6ee65b4ec1aa610a818edccb6998354c215035e3b94aa306a9842a073c76e95460d5308540f58ed42a8c1aa610a81ed1da75518354c21503dc3b4caa306a9842a049fe37288655a00854093fcecd98c2b4010a816778d566185680215024ff1b8c2b26d0042a049fe3719560da00854093fcecd98a9b4010a8127f8dc66153680215025fb1b8c1aa6d0042a07bc65518354da00854093ceea598dcb4642a8145bdd4aeda764c855028d7ba95db4cc990aa051e7752bb68d932154093d6ea598c9b4442a8127b5d4b3193684855024f69b8da324d090aa06be4705c068d4121540a3d66db92d128242a8185bccb69d92504855030d7996d3324a090aa061e732da36494121540c3d665b44c928242a8147b4db649a1504855024f73a966326d010aa049ee37192505a021540d7c8e2386d0a6042a816f91d4685314c0855035f2394a0a629810aa073e46e9414c53021540f6c8d3a8298a6042a81ee91a6505314c085503df0344a0a629810aa051af752bb6999314940837e6e372d3302292816f91d4685314c052503dd234ca0a62980a4a0516f752bb69d932054082fe6e372d3aa440a816f19d4695534c081503da334eaa2a698102a049cf371986d1a508540a1de6db92d42a810a8183bccb6a198550215028b79b6cc34eaa042a051af36d986995408540a39e6db30d2aa810a81279dd4b31b968c215024f39b8cc2a8d1842a049f6371986c1a308540e78cdaaa8d834610a8143bdd4aeda864c215028b7ba95db4ec9842a051af752bb6999308540a39eea576d2b2610a81479dd4aeda364c215024f71b8cc2a8d0042a049ee752cc64da00854083fc6e374cc26010a81af19c470da54c021502de33a8d2aa698042a06bc67295454d3008540e78cdd2a8a9a6010a81eb19a8551534c021503da334eaa2a698042a07b866995454d3008540 else (if i < 2 then 0x2644855020ff9b6e5264c890aa0617f32da74c99121540c37e65b4c9932242a8187dccb68d32644855030fd996d1264c890aa0617f32da78899121540c37e65b4d1132242a8187dccb68e22644855028fe9b699342c890aa06be5709c168d4121540f3cae8b46c928242a8145fdd9aeda74c4855028dfbb35db4c9890aa051f7766bb68d3121540a7e66db86d126242a8107fdda32d924c4855030fdb4465b249890aa061fd684cb6493121540c2fe65b4ec926242a8186fccb699924c4855030fb996d1b249890aa043f736dca4c93121540c6ee65b4e9926242a818edccb699324c4855031f9996d12649890aa07be174da25053121540b7caed264a0a6242a81cf95ba4c9414c485503db2b4e992829890aa07ba5699325053121540f7c2d1264a0a6242a8145fdd9aeda7484855028dfbb35db4c9090aa051f7766bb68d2121540a3ee6db92d1a4242a8107fcdc6e993484855030bf996d3b269090aa061bf32da664d2121540c3ee65b46c9a4242a8147edd9aeda2484855028fd9b6c9b449090aa0697d305a76492121540d37a60b4cc924242a81a7d4c168d92484855028fe9b6c9b429090aa049fe37132645a02154093fc6e444c8b4042a8127f9d9b3131680855024ff1b8c9262d010aa04bf6371324c5a021540f7c89928298b4042a8127f9d9b3121680855024ff1b8c9a42d010aa059fc34592485a02154093deea598c9b424128107fcdb72553684825020ff9b6e52a6c8904a041ff371ba64d512094083fe6e374caa6241281ef195454da14c082503de334aa9a8298104a07be4551a14c53020940f7c8d2a8298a604128107fcdcaed9668c525020ff9b8dd32cc18a4a041ff768cb6616314940c37ed3196cc2c629281e2dd966a18358c525020ff9b766346c88a4a041ff36dca60d9114940c37e65b4cc1b222928107fcdc6e993604525020ff9b8dd330988a4a051bf36d98699311494093ee6e330d1a6229281e6d59658da14c4525020ff9b8dd32ea9902a049df371976955320540f2aecbb4ab9aa640a816f1dd46957354c815035e3b94aa2e6a9902a07b4769d545cd532054083fe6e576cab4440a8107fcdb72953648815030bf996d3aa6c9102a041ff371ba64d522054083fe6e374cba6440a8107fcdc6e9954c8815030bf996d3b2a99102a0797365d73689322054083feedd98cc34428a8107fcdcaed98688515024f7ba966326d10a2a041ff36dc960da21454083fe6db94c1b2428a8187dccb68d83648515020ffbb366374c10a2a041ff371ba64d821454085fe6db94c1b0428a8107fcdc6e9984c8515028fb9b6cc346990a2a043fb371ba609321454091feecd98dab5010a8143fcdb70da8654215028bf9b74434eca842a051bf36e886999508540a1feecd76d430a10a8145fdd9aeda761421502caf9aacc34ec28 else 0x5c1000008908402c10068524214908424210000000000000000000000000000000000021190847041000042000000000000000089087a401000000000012084e420016842b2130c862421890840000000000000000000000000000000000000000b8200000000000000000000000000000002e08005c100005c1000000000000000210000001080ac3c820800000000000b8200000000005230986431230801431230c48c312308006190c48c2001864206908000000000004420690800000000008840d2130c840d21034840d21034840d21df3bd377eeadcbb836ded6da3b3363ec2d7bae359eaed53a934fe9ad11a0f3f679ce998b2863ec5986b04603bfd7e6fa5efbd5796f05dbbad746e65c7b856f6dc5b3b5d6a6d259fb35656c858bb0d5d2b1550a974e69a52fa554969051ba2d44686507a053f67c4e69a933e654c59812ee5b4b193f236444768c914a2042e8530920fc1a82b04205c06802ff1fbbf27dafa1f1bde7b2f51e7bca78af01ddbb6762eb1d3ba273ae61c9b816f8dddb936d6d0d8daf3596a8d3da5345680ced9b331658c9d9131d630c4d873095eebc9702db5acb115faba56aac155aa6542a714ba925009ed3b2714be9351da364628b113a2243a86109a013f87dcf91ed3d078cef1d938e6d4d19912fe5b4ad9562a24fc969282464447f8fa1ea3c0758e61c23706b8c51662b8548a413e2684a8900fc1b02d04806c0900900093eeecd98d8b4642a8127edd9b31b1688855024fd9b8c9b62d110aa051f7772bb68d9221540a3ee6db82d1b2442a8127f4dc64db2684855024fe9b8dca64d090aa051f776dc268d9121540a3ee6db84d1b2242a8147ecdb70da))
def lev9 : Packing := (228,6,7,0,0,11,0,data9)
def hash9 (i : Nat) : Nat := 0x4609865e9573a6437b0000be88000094c7840017a2bf98004f5cc0b007005d11548030973b9d2841396e001a90837d7871cc45b51036d54b00270000c16bcd9b0072cac2d69a1e380eab1f1b1900a0bdd104ae051d7a5f257fd7133cbae079c9009c00c500005852c8c6379e00a8756f89150c74d03eafb101b362b481618ead004d6392125b2e7c5032aa5770990851ace3478f004433b606e16cdd3403d4bb6431350ade67b27796b8183ab7df4a5316403d6023bc24dbcf00b92ca98a42028ba42b59d955007e3fdae200002f2a6a1ca58d85002d6d48766693496514dc828c56d85a4c000b00ce0f682129c3d2a3a126cb9f874e9169c40da72220d3440800b021c707360c6032a4d52c1ca420024020801c0008022001a30c002000200188082c38b0220409105420402047824c0c6000010080143018120180061444001
def idx9 (h : Nat) : Option (Nat × Nat) := let a := h % 76
  let sh := packedAt hash9 (a*7) 7
  some (packedAt hash9 (532+((h/76+sh)%254)*8) 8,0)
def data8 (i : Nat) : Nat := 0x2a794ec745a36494121540
def lev8 : Packing := (1,7,7,0,0,0,0,data8)
def idx8 (_ : Nat) : Option (Nat × Nat) := some (0,0)
def newLevels : Nat → Packing
  | 14 => lev14
  | 13 => lev13
  | 12 => lev12
  | 11 => lev11
  | 10 => lev10
  | 9 => lev9
  | 8 => lev8
  | _ => emptyPacking
def newIndex : Nat → Nat → Option (Nat × Nat)
  | 15 => idx14
  | 14 => idx13
  | 13 => idx12
  | 12 => idx11
  | 11 => idx10
  | 10 => idx9
  | 9 => idx8
  | _ => fun _ => none
def trial : Forest := ⟨511,15,dead.samples,deadcolumns,deadautos,newLevels,newIndex⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell13x0 : block trial 13 0 6=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem level13 : block trial 13 0 6=true := cell13x0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell12x0 : block trial 12 0 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell12x24 : block trial 12 24 1=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell12x25 : block trial 12 25 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell12x49 : block trial 12 49 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell12x73 : block trial 12 73 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell12x97 : block trial 12 97 24=true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell12x121 : block trial 12 121 15=true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem level12 : block trial 12 0 136=true := (@block_merge trial 12 0 49 87 (@block_merge trial 12 0 24 25 cell12x0 (@block_merge trial 12 24 1 24 cell12x24 cell12x25)) (@block_merge trial 12 49 48 39 (@block_merge trial 12 49 24 24 cell12x49 cell12x73) (@block_merge trial 12 97 24 15 cell12x97 cell12x121)))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x0 : block trial 11 0 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x24 : block trial 11 24 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x48 : block trial 11 48 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x72 : block trial 11 72 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x96 : block trial 11 96 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x120 : block trial 11 120 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x144 : block trial 11 144 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x168 : block trial 11 168 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x192 : block trial 11 192 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x216 : block trial 11 216 14=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x230 : block trial 11 230 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x254 : block trial 11 254 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x278 : block trial 11 278 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x302 : block trial 11 302 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x326 : block trial 11 326 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x350 : block trial 11 350 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x374 : block trial 11 374 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x398 : block trial 11 398 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x422 : block trial 11 422 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x446 : block trial 11 446 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x470 : block trial 11 470 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x494 : block trial 11 494 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x518 : block trial 11 518 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x542 : block trial 11 542 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x566 : block trial 11 566 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x590 : block trial 11 590 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x614 : block trial 11 614 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x638 : block trial 11 638 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x662 : block trial 11 662 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x686 : block trial 11 686 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x710 : block trial 11 710 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x734 : block trial 11 734 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x758 : block trial 11 758 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x782 : block trial 11 782 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x806 : block trial 11 806 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x830 : block trial 11 830 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x854 : block trial 11 854 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x878 : block trial 11 878 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x902 : block trial 11 902 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x926 : block trial 11 926 24=true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x950 : block trial 11 950 24=true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x974 : block trial 11 974 24=true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x998 : block trial 11 998 24=true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x1022 : block trial 11 1022 24=true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x1046 : block trial 11 1046 24=true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x1070 : block trial 11 1070 24=true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x1094 : block trial 11 1094 24=true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x1118 : block trial 11 1118 24=true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x1142 : block trial 11 1142 24=true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell11x1166 : block trial 11 1166 14=true := by
  apply cellsBlock (ar:=12) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem level11 : block trial 11 0 1180=true := (@block_merge trial 11 0 590 590 (@block_merge trial 11 0 278 312 (@block_merge trial 11 0 144 134 (@block_merge trial 11 0 72 72 (@block_merge trial 11 0 24 48 cell11x0 (@block_merge trial 11 24 24 24 cell11x24 cell11x48)) (@block_merge trial 11 72 24 48 cell11x72 (@block_merge trial 11 96 24 24 cell11x96 cell11x120))) (@block_merge trial 11 144 72 62 (@block_merge trial 11 144 24 48 cell11x144 (@block_merge trial 11 168 24 24 cell11x168 cell11x192)) (@block_merge trial 11 216 14 48 cell11x216 (@block_merge trial 11 230 24 24 cell11x230 cell11x254)))) (@block_merge trial 11 278 144 168 (@block_merge trial 11 278 72 72 (@block_merge trial 11 278 24 48 cell11x278 (@block_merge trial 11 302 24 24 cell11x302 cell11x326)) (@block_merge trial 11 350 24 48 cell11x350 (@block_merge trial 11 374 24 24 cell11x374 cell11x398))) (@block_merge trial 11 422 72 96 (@block_merge trial 11 422 24 48 cell11x422 (@block_merge trial 11 446 24 24 cell11x446 cell11x470)) (@block_merge trial 11 494 48 48 (@block_merge trial 11 494 24 24 cell11x494 cell11x518) (@block_merge trial 11 542 24 24 cell11x542 cell11x566))))) (@block_merge trial 11 590 288 302 (@block_merge trial 11 590 144 144 (@block_merge trial 11 590 72 72 (@block_merge trial 11 590 24 48 cell11x590 (@block_merge trial 11 614 24 24 cell11x614 cell11x638)) (@block_merge trial 11 662 24 48 cell11x662 (@block_merge trial 11 686 24 24 cell11x686 cell11x710))) (@block_merge trial 11 734 72 72 (@block_merge trial 11 734 24 48 cell11x734 (@block_merge trial 11 758 24 24 cell11x758 cell11x782)) (@block_merge trial 11 806 24 48 cell11x806 (@block_merge trial 11 830 24 24 cell11x830 cell11x854)))) (@block_merge trial 11 878 144 158 (@block_merge trial 11 878 72 72 (@block_merge trial 11 878 24 48 cell11x878 (@block_merge trial 11 902 24 24 cell11x902 cell11x926)) (@block_merge trial 11 950 24 48 cell11x950 (@block_merge trial 11 974 24 24 cell11x974 cell11x998))) (@block_merge trial 11 1022 72 86 (@block_merge trial 11 1022 24 48 cell11x1022 (@block_merge trial 11 1046 24 24 cell11x1046 cell11x1070)) (@block_merge trial 11 1094 48 38 (@block_merge trial 11 1094 24 24 cell11x1094 cell11x1118) (@block_merge trial 11 1142 24 14 cell11x1142 cell11x1166))))))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x0 : block trial 10 0 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x24 : block trial 10 24 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x48 : block trial 10 48 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x72 : block trial 10 72 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x96 : block trial 10 96 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x120 : block trial 10 120 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x144 : block trial 10 144 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x168 : block trial 10 168 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x192 : block trial 10 192 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x216 : block trial 10 216 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x240 : block trial 10 240 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x264 : block trial 10 264 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x288 : block trial 10 288 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x312 : block trial 10 312 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x336 : block trial 10 336 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x360 : block trial 10 360 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x384 : block trial 10 384 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x408 : block trial 10 408 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x432 : block trial 10 432 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x456 : block trial 10 456 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x480 : block trial 10 480 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x504 : block trial 10 504 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x528 : block trial 10 528 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x552 : block trial 10 552 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x576 : block trial 10 576 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x600 : block trial 10 600 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x624 : block trial 10 624 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x648 : block trial 10 648 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x672 : block trial 10 672 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x696 : block trial 10 696 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x720 : block trial 10 720 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x744 : block trial 10 744 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x768 : block trial 10 768 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x792 : block trial 10 792 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x816 : block trial 10 816 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x840 : block trial 10 840 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x864 : block trial 10 864 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x888 : block trial 10 888 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x912 : block trial 10 912 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x936 : block trial 10 936 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x960 : block trial 10 960 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x984 : block trial 10 984 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1008 : block trial 10 1008 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1032 : block trial 10 1032 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1056 : block trial 10 1056 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1080 : block trial 10 1080 7=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1087 : block trial 10 1087 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1111 : block trial 10 1111 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1135 : block trial 10 1135 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1159 : block trial 10 1159 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1183 : block trial 10 1183 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1207 : block trial 10 1207 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1231 : block trial 10 1231 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1255 : block trial 10 1255 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1279 : block trial 10 1279 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1303 : block trial 10 1303 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1327 : block trial 10 1327 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1351 : block trial 10 1351 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1375 : block trial 10 1375 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1399 : block trial 10 1399 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1423 : block trial 10 1423 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1447 : block trial 10 1447 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1471 : block trial 10 1471 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1495 : block trial 10 1495 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1519 : block trial 10 1519 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1543 : block trial 10 1543 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1567 : block trial 10 1567 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1591 : block trial 10 1591 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1615 : block trial 10 1615 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1639 : block trial 10 1639 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1663 : block trial 10 1663 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1687 : block trial 10 1687 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1711 : block trial 10 1711 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1735 : block trial 10 1735 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1759 : block trial 10 1759 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1783 : block trial 10 1783 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1807 : block trial 10 1807 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1831 : block trial 10 1831 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1855 : block trial 10 1855 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1879 : block trial 10 1879 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1903 : block trial 10 1903 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1927 : block trial 10 1927 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1951 : block trial 10 1951 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1975 : block trial 10 1975 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x1999 : block trial 10 1999 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x2023 : block trial 10 2023 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x2047 : block trial 10 2047 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x2071 : block trial 10 2071 24=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell10x2095 : block trial 10 2095 23=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem level10 : block trial 10 0 2118=true := (@block_merge trial 10 0 1056 1062 (@block_merge trial 10 0 528 528 (@block_merge trial 10 0 264 264 (@block_merge trial 10 0 120 144 (@block_merge trial 10 0 48 72 (@block_merge trial 10 0 24 24 cell10x0 cell10x24) (@block_merge trial 10 48 24 48 cell10x48 (@block_merge trial 10 72 24 24 cell10x72 cell10x96))) (@block_merge trial 10 120 72 72 (@block_merge trial 10 120 24 48 cell10x120 (@block_merge trial 10 144 24 24 cell10x144 cell10x168)) (@block_merge trial 10 192 24 48 cell10x192 (@block_merge trial 10 216 24 24 cell10x216 cell10x240)))) (@block_merge trial 10 264 120 144 (@block_merge trial 10 264 48 72 (@block_merge trial 10 264 24 24 cell10x264 cell10x288) (@block_merge trial 10 312 24 48 cell10x312 (@block_merge trial 10 336 24 24 cell10x336 cell10x360))) (@block_merge trial 10 384 72 72 (@block_merge trial 10 384 24 48 cell10x384 (@block_merge trial 10 408 24 24 cell10x408 cell10x432)) (@block_merge trial 10 456 24 48 cell10x456 (@block_merge trial 10 480 24 24 cell10x480 cell10x504))))) (@block_merge trial 10 528 264 264 (@block_merge trial 10 528 120 144 (@block_merge trial 10 528 48 72 (@block_merge trial 10 528 24 24 cell10x528 cell10x552) (@block_merge trial 10 576 24 48 cell10x576 (@block_merge trial 10 600 24 24 cell10x600 cell10x624))) (@block_merge trial 10 648 72 72 (@block_merge trial 10 648 24 48 cell10x648 (@block_merge trial 10 672 24 24 cell10x672 cell10x696)) (@block_merge trial 10 720 24 48 cell10x720 (@block_merge trial 10 744 24 24 cell10x744 cell10x768)))) (@block_merge trial 10 792 120 144 (@block_merge trial 10 792 48 72 (@block_merge trial 10 792 24 24 cell10x792 cell10x816) (@block_merge trial 10 840 24 48 cell10x840 (@block_merge trial 10 864 24 24 cell10x864 cell10x888))) (@block_merge trial 10 912 72 72 (@block_merge trial 10 912 24 48 cell10x912 (@block_merge trial 10 936 24 24 cell10x936 cell10x960)) (@block_merge trial 10 984 24 48 cell10x984 (@block_merge trial 10 1008 24 24 cell10x1008 cell10x1032)))))) (@block_merge trial 10 1056 511 551 (@block_merge trial 10 1056 247 264 (@block_merge trial 10 1056 103 144 (@block_merge trial 10 1056 31 72 (@block_merge trial 10 1056 24 7 cell10x1056 cell10x1080) (@block_merge trial 10 1087 24 48 cell10x1087 (@block_merge trial 10 1111 24 24 cell10x1111 cell10x1135))) (@block_merge trial 10 1159 72 72 (@block_merge trial 10 1159 24 48 cell10x1159 (@block_merge trial 10 1183 24 24 cell10x1183 cell10x1207)) (@block_merge trial 10 1231 24 48 cell10x1231 (@block_merge trial 10 1255 24 24 cell10x1255 cell10x1279)))) (@block_merge trial 10 1303 120 144 (@block_merge trial 10 1303 48 72 (@block_merge trial 10 1303 24 24 cell10x1303 cell10x1327) (@block_merge trial 10 1351 24 48 cell10x1351 (@block_merge trial 10 1375 24 24 cell10x1375 cell10x1399))) (@block_merge trial 10 1423 72 72 (@block_merge trial 10 1423 24 48 cell10x1423 (@block_merge trial 10 1447 24 24 cell10x1447 cell10x1471)) (@block_merge trial 10 1495 24 48 cell10x1495 (@block_merge trial 10 1519 24 24 cell10x1519 cell10x1543))))) (@block_merge trial 10 1567 264 287 (@block_merge trial 10 1567 120 144 (@block_merge trial 10 1567 48 72 (@block_merge trial 10 1567 24 24 cell10x1567 cell10x1591) (@block_merge trial 10 1615 24 48 cell10x1615 (@block_merge trial 10 1639 24 24 cell10x1639 cell10x1663))) (@block_merge trial 10 1687 72 72 (@block_merge trial 10 1687 24 48 cell10x1687 (@block_merge trial 10 1711 24 24 cell10x1711 cell10x1735)) (@block_merge trial 10 1759 24 48 cell10x1759 (@block_merge trial 10 1783 24 24 cell10x1783 cell10x1807)))) (@block_merge trial 10 1831 144 143 (@block_merge trial 10 1831 72 72 (@block_merge trial 10 1831 24 48 cell10x1831 (@block_merge trial 10 1855 24 24 cell10x1855 cell10x1879)) (@block_merge trial 10 1903 24 48 cell10x1903 (@block_merge trial 10 1927 24 24 cell10x1927 cell10x1951))) (@block_merge trial 10 1975 72 71 (@block_merge trial 10 1975 24 48 cell10x1975 (@block_merge trial 10 1999 24 24 cell10x1999 cell10x2023)) (@block_merge trial 10 2047 24 47 cell10x2047 (@block_merge trial 10 2071 24 23 cell10x2071 cell10x2095)))))))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell9x0 : block trial 9 0 24=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell9x24 : block trial 9 24 24=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell9x48 : block trial 9 48 8=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell9x56 : block trial 9 56 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell9x80 : block trial 9 80 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell9x104 : block trial 9 104 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell9x128 : block trial 9 128 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell9x152 : block trial 9 152 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell9x176 : block trial 9 176 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell9x200 : block trial 9 200 24=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell9x224 : block trial 9 224 4=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem level9 : block trial 9 0 228=true := (@block_merge trial 9 0 104 124 (@block_merge trial 9 0 48 56 (@block_merge trial 9 0 24 24 cell9x0 cell9x24) (@block_merge trial 9 48 8 48 cell9x48 (@block_merge trial 9 56 24 24 cell9x56 cell9x80))) (@block_merge trial 9 104 72 52 (@block_merge trial 9 104 24 48 cell9x104 (@block_merge trial 9 128 24 24 cell9x128 cell9x152)) (@block_merge trial 9 176 24 28 cell9x176 (@block_merge trial 9 200 24 4 cell9x200 cell9x224))))
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cell8x0 : block trial 8 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem level8 : block trial 8 0 1=true := cell8x0
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checkedTrial : checkedTables trial 13 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact level8
  · exact level9
  · exact level10
  · exact level11
  · exact level12
  · exact level13

def roots := inputs ++ [seed]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem oldImpossible : Impossible graph 14 inputs.toFinset :=
  root_index (g := dead) (before_sound known383 valid383) geomdead tablesdead
    (k:=14) (i:=0) (by decide) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem loose {k t S} (run : Live graph k t S) (hk : k ≤ 13) (sub : ∀ a ∈ S, a ∈ roots) : False := by
  have wit : witness inputs seed := by
    right
    exact ⟨true,inputs.getD 0 zero,inputs.getD 4 zero,by decide +kernel,by decide +kernel,
      by unfold proper; decide +kernel,by unfold proper; decide +kernel,by decide +kernel,rfl⟩
  obtain ⟨l,u,V,hl,hr,hs⟩ := pull_gate run (Or.inr wit) sub
  have hs' : ∀ a ∈ V, a ∈ inputs ++ [seed] := fun a ha => List.mem_append_left _ (hs a ha)
  rcases all_roots hr hs' with e | e
  · exact oldImpossible l u (by omega) (e ▸ hr)
  · have hm : seed ∈ V := e.symm ▸ List.mem_toFinset.mpr (List.mem_append_right _ (List.mem_singleton_self _))
    exact (show seed ∉ inputs by decide +kernel) (hs _ hm)

abbrev rootCtx := contextOf trial 14 0
abbrev rootDecor := (readNode trial 14 0).2.2
theorem decRoot : rootDecor.map Prod.fst = roots := by decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checkedPairs : rootDecor.all (fun a => rootDecor.all (fun b => a.1 == b.1 || testPair rootCtx a b false)) = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem children {a b : Sig} (am : a ∈ roots) (bm : b ∈ roots) (hab : a ≠ b)
    (ka kb : Bool) (fr : bin false a b ∉ roots) (pr : proper (bin false a b)) :
    Impossible graph 13 (childTwo roots a b false ka kb).toFinset := by
  rw [← decRoot] at am bm fr ⊢
  obtain ⟨a,aa,rfl⟩ := List.mem_map.mp am
  obtain ⟨b,bb,rfl⟩ := List.mem_map.mp bm
  have nd : (rootDecor.map Prod.fst).Nodup := by rw [decRoot]; decide +kernel
  rw [←binary_front nd aa bb hab]
  have check := List.all_eq_true.mp (List.all_eq_true.mp checkedPairs a aa) b bb
  simp only [Bool.or_eq_true, beq_iff_eq] at check
  have test := check.resolve_left hab
  have geo := geomdead
  change graphValid trial (boundsBefore known383) = true at geo
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geo
  have pairs := chart_pairs geo.1.1.1 geo.1.1.2
  have cols := fun ci hc => col_sound ci (boundsBefore known383) (before_sound known383 valid383) (geo.1.2 ci hc)
  apply evalMove_sound (raw:=vars trial.mask) (T:=targetOf trial) (op:=0) (ka:=ka) (kb:=kb) (pools:=rootCtx.2.2.2.2.1) (links:=rootCtx.2.2.2.2.2) (cap:=14) pairs _ nd aa bb (fun _ e => hab (congrArg Prod.fst e)) (by decide) _ _ pr fr (testPair_at test ka kb)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful trial) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨i,j⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound trial cols h
  · intro tag xs hx
    change xs ∈ ((trial.index 14 tag).bind (linkedSet trial 13)).toList at hx
    have e : ((trial.index 14 tag).bind (linkedSet trial 13))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound trial 13 geo.2
      (forest_all trial 13 _ (before_sound known383 valid383) geomdead checkedTrial 13 le_rfl) h

theorem startAnd {k t U a b} (hk : k ≤ 13) (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hf : bin false a b ∉ insert a (insert b U)) (tail : Live graph k t (insert (bin false a b) U))
    (sub : ∀ v ∈ insert a (insert b U), v ∈ roots) : False := by
  classical
  have full := Live.binary ha hb hab hf tail
  rcases all_roots full sub with he | he
  · exact oldImpossible _ _ (by omega) (he ▸ full)
  have he : roots.toFinset = insert a (insert b U) := he.symm
  have hn : roots.Nodup := by decide +kernel

  have am : a ∈ roots := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bm : b ∈ roots := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have fresh : bin false a b ∉ roots := fun h => hf (he ▸ List.mem_toFinset.mpr h)
  have hz := live_proper tail _ (Finset.mem_insert_self _ _)
  let ka := decide (a ∈ U)
  let kb := decide (b ∈ U)
  let rest := (roots.erase a).erase b
  have er : rest.toFinset = (roots.toFinset.erase a).erase b := by
    rw [show rest=(roots.erase a).erase b by rfl,erase_fin (hn.erase _) b,
      erase_fin hn a]
  have ke : (kept ka a (kept kb b rest)).toFinset = U := by
    rw [kept_fin,kept_fin,er,he]
    ext j
    by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
      by_cases jb : j=b <;> simp [ka,kb,aa,bb,ja,jb,hab,Ne.symm hab]
  have rn : rest.Nodup := (hn.erase _).erase _
  have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
  have br : b ∉ rest := (hn.erase a).not_mem_erase
  have nk := kept_nd kb b rest rn br
  have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
  have nd : (childTwo roots a b false ka kb).Nodup := by
    refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
    intro h
    exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
  have eq : (childTwo roots a b false ka kb).toFinset = insert (bin false a b) U := by
    change (bin false a b::kept ka a (kept kb b rest)).toFinset = _
    simp [ke]
  exact children am bm hab ka kb fresh hz k t hk (eq.symm ▸ tail)

theorem kill {k t S z} (hk : k ≤ 13) (h : Live graph k t S)
    (hz : represented roots z ∨ ∃ a b, a ∈ roots ∧ b ∈ roots ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin false a b)
    (sub : ∀ a ∈ S, a ∈ roots++[z]) : False := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ roots
    · apply loose h hk
      intro v hv
      have hh : v ∈ roots ∨ v=z := by simpa using sub v hv
      exact hh.elim id (fun e => e ▸ hw)
    have hp := live_proper h z hm
    rcases hz with hr | ⟨a,b,ha,hb,pa,pb,hab,eq⟩
    · exact (hr.resolve_left hw) hp
    subst z
    let U := S.erase (bin false a b)
    have ht : Live graph k t (insert (bin false a b) U) := by simpa [U,Finset.insert_erase hm] using h
    have hu : ∀ v ∈ U, v ∈ roots := by
      intro v hv
      obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
      simpa [hne] using sub v hm
    have hs : ∀ v ∈ insert a (insert b U), v ∈ roots := by simpa using And.intro ha (And.intro hb hu)
    exact startAnd hk pa pb hab (fun h => hw (hs _ h)) ht hs
  · apply loose h hk
    intro a ha
    have hn : a ≠ z := fun e => hm (e ▸ ha)
    simpa [hn] using sub a ha

private lemma andRep {w a b}  (ha : represented w a) (hb : represented w b) :
    represented w (bin false a b) ∨ (∃ x y, x ∈ w ∧ y ∈ w ∧ proper x ∧ proper y ∧ x ≠ y ∧ bin false a b = bin false x y) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; simp_all
  · rw [bin_comm]; simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · simp_all
  · simp_all
  by_cases he : a=b
  · subst b; simp_all
  exact Or.inr ⟨a,b,ham,hbm,hap,hbp,he,rfl⟩

theorem andGate (g : Gate) (op : g.op = .and) (hl : g.inputs.length ≤ 2) :
    represented roots (gv roots g) ∨ ∃ a b, a ∈ roots ∧ b ∈ roots ∧ proper a ∧ proper b ∧ a ≠ b ∧ gv roots g = bin false a b := by
  obtain ⟨o,l⟩ := g
  change o = .and at op
  subst o
  cases l with
  | nil => exact Or.inl (Or.inr (fun hp => hp.2 rfl))
  | cons i l =>
    cases l with
    | nil =>
      simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using
        (Or.inl (get_rep roots i) : represented roots (roots.getD i zero) ∨ _)
    | cons j l =>
      cases l with
      | cons _ _ => simp at hl
      | nil => simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using andRep (get_rep roots i) (get_rep roots j)
theorem finish (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 4))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15)
    (second : Option.map Gate.op C.gates[1]? = some GateOp.and) : False := by
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
    cases gs with
    | nil => simp [hgs] at second
    | cons g2 rest =>
      have op : g2.op = .and := by simpa [hgs] using second
      have len : rest.length ≤ 13 := by simp [Circuit.size,hgs] at small; omega
      obtain ⟨k,t,S,hk,run,hs⟩ := extract rest (roots ++ [gv roots g2]) (fun x hx => tailLegal x (by simp [hx])) graph_proper targetIn
      exact kill (hk.trans len) run (andGate g2 op (tailLegal g2 (by simp)).2) hs

end PEqualNP.Outside.L_meta_2149

theorem PEqualNP.Outside.L_meta_2149 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.and → (16 : ℕ) ≤ x1.size := by
  intro C hf hw he hs
  by_contra h
  exact PEqualNP.Outside.L_meta_2149.finish C hf hw he (by omega) hs
