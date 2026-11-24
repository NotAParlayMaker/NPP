import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_4177

namespace Unsigned
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
def seed : Sig := 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 && sample r 1) := by decide +kernel
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
end Unsigned


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The normalization, fork bound, and pair invariant below are adapted from
-- L-meta-2165 by copsrlpond and its predecessor L-meta-1549.


-- The branch-group argument and circuit simplifier are adapted from L_meta_1549.
-- The simplifier tracks the number of non-NOT gates independently of length.

namespace BranchGraph

variable {V : Type*} [DecidableEq V]

def containsEdge (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∃ a ∈ I, ∃ b ∈ I, G.Adj a b

omit [DecidableEq V] in
lemma singleton_no_edge (G : SimpleGraph V) (w : V) : ¬ containsEdge G {w} := by
  rintro ⟨a, ha, b, hb, hab⟩
  rw [Finset.mem_singleton] at ha hb
  subst a
  subst b
  exact G.loopless.irrefl w hab

lemma pair_contains_edge (G : SimpleGraph V) (u w : V) : containsEdge G {u,w} ↔ G.Adj u w := by
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.loopless.irrefl _ hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.loopless.irrefl _ hab).elim
  · intro h
    exact ⟨u, by simp, w, by simp, h⟩

def Independent (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b

section FiniteGraph

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def neighborsAfter (removed : Finset V) (u : V) : Finset V :=
  Finset.univ.filter (fun v => G.Adj u v ∧ v ∉ removed)

lemma neighborsAfter_subset {A B : Finset V} (h : A ⊆ B) (u : V) :
    neighborsAfter G B u ⊆ neighborsAfter G A u := by
  intro v membership
  simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and] at membership ⊢
  exact ⟨membership.1, fun vIn => membership.2 (h vIn)⟩

lemma neighbor_equality_survives {A B : Finset V} (h : A ⊆ B) {u w : V}
    (same : neighborsAfter G A u = neighborsAfter G A w) :
    neighborsAfter G B u = neighborsAfter G B w := by
  have e (v : V) : neighborsAfter G B v = (neighborsAfter G A v).filter (· ∉ B) := by
    ext z
    simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hz => ⟨⟨hz.1, fun zIn => hz.2 (h zIn)⟩, hz.2⟩, fun hz => ⟨hz.1.1, hz.2⟩⟩
  rw [e u, e w, same]

def TwinGroup (removed group : Finset V) : Prop :=
  ∀ u ∈ group, ∀ w ∈ group, (neighborsAfter G removed u).Nonempty →
    (neighborsAfter G removed w).Nonempty → neighborsAfter G removed u = neighborsAfter G removed w

def isolates (removed : Finset V) : Finset V :=
  Finset.univ.filter (fun v => neighborsAfter G removed v = ∅)

def maximalClass (removed : Finset V) (root : V) : Finset V :=
  if root ∉ removed ∧ (neighborsAfter G removed root).Nonempty then
    Finset.univ.filter (fun v => v ∉ removed ∧ neighborsAfter G removed v = neighborsAfter G removed root)
  else ∅

def closeIsolates (removed : Finset V) : Finset V := removed ∪ isolates G removed

def removeClass (removed : Finset V) (root : V) : Finset V :=
  closeIsolates G (removed ∪ maximalClass G removed root)

lemma subset_removeClass (removed : Finset V) (root : V) : removed ⊆ removeClass G removed root := by
  intro u hu
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hu)

lemma isolate_mem_removeClass {removed : Finset V} (root u : V)
    (h : ¬ (neighborsAfter G removed u).Nonempty) : u ∈ removeClass G removed root := by
  have hn : ¬ (neighborsAfter G (removed ∪ maximalClass G removed root) u).Nonempty := by
    intro existsNeighbor
    exact h (existsNeighbor.mono (neighborsAfter_subset G Finset.subset_union_left u))
  have hu : u ∈ isolates G (removed ∪ maximalClass G removed root) := by
    simp [isolates, Finset.not_nonempty_iff_eq_empty.mp hn]
  exact Finset.mem_union_right _ hu

theorem dominates_step [Nonempty V] {A B Q : Finset V} (smaller : A ⊆ B)
    (twins : TwinGroup G A Q) : ∃ root : V, A ∪ Q ⊆ removeClass G B root := by
  classical
  by_cases someActive : ∃ root ∈ Q, root ∉ B ∧ (neighborsAfter G B root).Nonempty
  · obtain ⟨root, rootQ, rootOut, rootLive⟩ := someActive
    refine ⟨root, ?_⟩
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact subset_removeClass G B root (smaller hu)
    by_cases uIn : u ∈ B
    · exact subset_removeClass G B root uIn
    by_cases live : (neighborsAfter G B u).Nonempty
    · have oldU := live.mono (neighborsAfter_subset G smaller u)
      have oldRoot := rootLive.mono (neighborsAfter_subset G smaller root)
      have same := neighbor_equality_survives G smaller (twins u hu root rootQ oldU oldRoot)
      have covered : u ∈ maximalClass G B root := by simp [maximalClass, rootOut, rootLive, uIn, same]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ covered)
    · exact isolate_mem_removeClass G root u live
  · let root : V := Classical.choice inferInstance
    refine ⟨root, ?_⟩
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact subset_removeClass G B root (smaller hu)
    by_cases uIn : u ∈ B
    · exact subset_removeClass G B root uIn
    exact isolate_mem_removeClass G root u (fun live => someActive ⟨u, hu, uIn, live⟩)

lemma retained_after_close {removed : Finset V} {u : V} (out : u ∉ closeIsolates G removed) :
    (neighborsAfter G (closeIsolates G removed) u).Nonempty := by
  have uOut : u ∉ removed := fun h => out (Finset.mem_union_left _ h)
  have old : (neighborsAfter G removed u).Nonempty := by
    by_contra empty
    apply out
    apply Finset.mem_union_right
    simp [isolates, Finset.not_nonempty_iff_eq_empty.mp empty]
  obtain ⟨v, hv⟩ := old
  simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  refine ⟨v, ?_⟩
  simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨hv.1, fun dropped => ?_⟩
  rcases Finset.mem_union.mp dropped with h | h
  · exact hv.2 h
  · have witness : u ∈ neighborsAfter G removed v := by
      simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hv.1.symm, uOut⟩
    have none : neighborsAfter G removed v = ∅ := by simpa [isolates] using h
    rw [none] at witness
    exact Finset.notMem_empty _ witness

lemma closeIsolates_idempotent (removed : Finset V) :
    closeIsolates G (closeIsolates G removed) = closeIsolates G removed := by
  apply Finset.Subset.antisymm
  · intro u hu
    rcases Finset.mem_union.mp hu with already | isolated
    · exact already
    by_contra out
    have live := retained_after_close G out
    have noNeighbors : neighborsAfter G (closeIsolates G removed) u = ∅ := by
      simpa [isolates] using isolated
    simpa [noNeighbors] using live
  · exact Finset.subset_union_left

def TwinSteps : Finset V → List (Finset V) → Prop
  | _, [] => True
  | removed, group :: rest => TwinGroup G removed group ∧ TwinSteps (removed ∪ group) rest

def removedThrough : Finset V → List (Finset V) → Finset V
  | removed, [] => removed
  | removed, group :: rest => removedThrough (removed ∪ group) rest

def ClassSteps : ℕ → Finset V → Finset V → Prop
  | 0, start, finish => finish = start
  | k + 1, start, finish => ∃ root : V, ClassSteps k (removeClass G start root) finish

theorem dominates_steps [Nonempty V] {A B : Finset V} (groups : List (Finset V))
    (smaller : A ⊆ B) (steps : TwinSteps G A groups) :
    ∃ finish : Finset V, ClassSteps G groups.length B finish ∧ removedThrough A groups ⊆ finish := by
  induction groups generalizing A B with
  | nil => exact ⟨B, rfl, smaller⟩
  | cons group rest ih =>
    obtain ⟨twins, next⟩ := steps
    obtain ⟨root, subset⟩ := dominates_step G smaller twins
    obtain ⟨finish, walk, covered⟩ := ih subset next
    exact ⟨finish, ⟨root, walk⟩, covered⟩

def EdgelessAfter (removed : Finset V) : Prop :=
  ∀ u v, u ∉ removed → v ∉ removed → ¬ G.Adj u v

omit [Fintype V] [DecidableRel G.Adj] in
lemma edgeless_mono {A B : Finset V} (subset : A ⊆ B) (noEdges : EdgelessAfter G A) :
    EdgelessAfter G B := by
  intro u v uOut vOut
  exact noEdges u v (fun h => uOut (subset h)) (fun h => vOut (subset h))

lemma closed_edgeless_all {D : Finset V} (noEdges : EdgelessAfter G (closeIsolates G D)) :
    closeIsolates G D = Finset.univ := by
  ext u
  simp only [Finset.mem_univ, iff_true]
  by_contra out
  obtain ⟨v, hv⟩ := retained_after_close G out
  simp only [neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  exact noEdges u v out hv.2 hv.1

lemma classSteps_finish_closed {k : ℕ} {start finish : Finset V} (walk : ClassSteps G k start finish)
    (closed : ∃ D : Finset V, start = closeIsolates G D) : ∃ D : Finset V, finish = closeIsolates G D := by
  induction k generalizing start with
  | zero =>
    change finish = start at walk
    rw [walk]
    exact closed
  | succ k ih =>
    obtain ⟨root, after⟩ := walk
    exact ih after ⟨_, rfl⟩

theorem covering_sequence_reaches_univ [Nonempty V] (groups : List (Finset V))
    (twins : TwinSteps G ∅ groups) (finished : EdgelessAfter G (removedThrough ∅ groups)) :
    ClassSteps G groups.length (closeIsolates G ∅) Finset.univ := by
  obtain ⟨D, steps, subset⟩ := dominates_steps G groups (Finset.empty_subset (closeIsolates G ∅)) twins
  have noEdges := edgeless_mono G subset finished
  obtain ⟨A, hD⟩ := classSteps_finish_closed G steps ⟨∅, rfl⟩
  rw [hD] at noEdges
  rwa [hD, closed_edgeless_all G noEdges] at steps

end FiniteGraph

end BranchGraph

namespace BranchGroupsLean

open BranchGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {m : Nat}

def bucket (label : V → Fin m) (r : Fin m) : Finset V := Finset.univ.filter (fun v => label v = r)

def below (label : V → Fin m) (r : Fin m) : Finset V := Finset.univ.filter (fun v => label v < r)

def coveredBy (label : V → Fin m) (done : List (Fin m)) : Finset V :=
  Finset.univ.filter (fun v => label v ∈ done)

omit [DecidableEq V] in
@[simp] lemma coveredBy_nil (label : V → Fin m) : coveredBy label [] = ∅ := by
  ext v
  simp [coveredBy]

lemma coveredBy_append_singleton (label : V → Fin m) (done : List (Fin m)) (r : Fin m) :
    coveredBy label (done ++ [r]) = coveredBy label done ∪ bucket label r := by
  ext v
  simp [coveredBy, bucket, List.mem_append]

omit [DecidableEq V] in
lemma covered_before_of_sorted (label : V → Fin m) (out : Fin m) (done rest : List (Fin m)) (r : Fin m)
    (sorted : (done ++ r :: rest).Pairwise (· < ·))
    (roots : ∀ v : V, label v = out ∨ label v ∈ done ++ r :: rest)
    (beforeOut : r < out) : coveredBy label done = below label r := by
  have facts := List.pairwise_append.mp sorted
  ext v
  simp only [coveredBy, below, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro member
    exact facts.2.2 _ member r (by simp)
  · intro earlier
    rcases roots v with isOut | member
    · rw [isOut] at earlier
      exact (lt_asymm earlier beforeOut).elim
    rcases List.mem_append.mp member with doneMember | coming
    · exact doneMember
    rcases List.mem_cons.mp coming with atRoot | later
    · exact (ne_of_lt earlier atRoot).elim
    have after := (List.pairwise_cons.mp facts.2.1).1 _ later
    exact (lt_asymm earlier after).elim

section Graph

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem sorted_tail_twin_steps (label : V → Fin m) (out : Fin m) (roots : List (Fin m))
    (sorted : roots.Pairwise (· < ·)) (allRoots : ∀ v : V, label v = out ∨ label v ∈ roots)
    (beforeOut : ∀ r ∈ roots, r < out)
    (twinAt : ∀ r ∈ roots, TwinGroup G (below label r) (bucket label r))
    (done pending : List (Fin m)) (complete : done ++ pending = roots) :
    TwinSteps G (coveredBy label done) (pending.map (bucket label)) := by
  induction pending generalizing done with
  | nil => exact True.intro
  | cons r tail ih =>
    have rMember : r ∈ roots := complete ▸ List.mem_append_right done (by simp : r ∈ r :: tail)
    have prev := covered_before_of_sorted label out done tail r (by simpa only [complete] using sorted)
      (fun v => by simpa only [complete] using allRoots v) (beforeOut r rMember)
    have next := ih (done ++ [r]) (by simpa [List.append_assoc] using complete)
    refine ⟨?_, ?_⟩
    · rw [prev]
      exact twinAt r rMember
    · rwa [coveredBy_append_singleton] at next

lemma removedThrough_coveredBy (label : V → Fin m) (done pending : List (Fin m)) :
    removedThrough (coveredBy label done) (pending.map (bucket label)) = coveredBy label (done ++ pending) := by
  induction pending generalizing done with
  | nil => simp [removedThrough]
  | cons r tail ih =>
    change removedThrough (coveredBy label done ∪ bucket label r) (tail.map (bucket label)) = _
    rw [← coveredBy_append_singleton, ih]
    simp [List.append_assoc]

omit [DecidableRel G.Adj] in
lemma no_edges_after_branches (label : V → Fin m) (out : Fin m) (roots : List (Fin m))
    (allRoots : ∀ v : V, label v = out ∨ label v ∈ roots)
    (outputIndependent : Independent G (bucket label out)) :
    EdgelessAfter G (removedThrough ∅ (roots.map (bucket label))) := by
  rw [← coveredBy_nil label, removedThrough_coveredBy, List.nil_append]
  intro u v uNot vNot
  have hu : label u = out := (allRoots u).resolve_right (by simpa [coveredBy] using uNot)
  have hv : label v = out := (allRoots v).resolve_right (by simpa [coveredBy] using vNot)
  exact outputIndependent u (by simp [bucket, hu]) v (by simp [bucket, hv])

theorem roots_required (label : V → Fin m) (out : Fin m) (branches : Finset (Fin m)) (k : Nat)
    (allRoots : ∀ v : V, label v = out ∨ label v ∈ branches)
    (beforeOut : ∀ r ∈ branches, r < out)
    (twinAt : ∀ r ∈ branches, TwinGroup G (below label r) (bucket label r))
    (outputIndependent : Independent G (bucket label out))
    (required : ∀ groups : List (Finset V), TwinSteps G ∅ groups →
      EdgelessAfter G (removedThrough ∅ groups) → k ≤ groups.length) : k ≤ branches.card := by
  let roots := branches.sort
  have sorted : roots.Pairwise (· < ·) := List.sortedLT_iff_pairwise.mp (Finset.sortedLT_sort branches)
  have covers (v : V) : label v = out ∨ label v ∈ roots := by simpa [roots] using allRoots v
  have early (r) (member : r ∈ roots) : r < out := beforeOut r (by simpa [roots] using member)
  have twins (r) (member : r ∈ roots) : TwinGroup G (below label r) (bucket label r) :=
    twinAt r (by simpa [roots] using member)
  have valid : TwinSteps G ∅ (roots.map (bucket label)) := by
    simpa using sorted_tail_twin_steps G label out roots sorted covers early twins [] roots rfl
  have last := no_edges_after_branches G label out roots covers outputIndependent
  simpa [roots] using required (roots.map (bucket label)) valid last

end Graph

end BranchGroupsLean

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)

def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2


def isNotGate (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false


def opCount (test : GateOp → Bool) (gs : List Gate) : ℕ :=
  gs.countP (fun g => test g.op)

lemma simplify_same_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg

lemma opCount_append (test : GateOp → Bool) (gs hs : List Gate) :
    opCount test (gs ++ hs) = opCount test gs + opCount test hs := by
  simp [opCount]

lemma opCount_cons (test : GateOp → Bool) (g : Gate) (gs : List Gate) :
    opCount test (g :: gs) = opCount test gs + (if test g.op then 1 else 0) := by
  by_cases h : test g.op <;> simp [opCount, h]

lemma simplify_opCount_le (test : GateOp → Bool) (op : GateOp) (m : ℕ) (ins : List Stat) :
    opCount test (simplify op m ins).1.toList ≤ (if test op then 1 else 0) := by
  cases h : (simplify op m ins).1 with
  | none => simp [opCount]
  | some g =>
    have hg : g ∈ (simplify op m ins).1 := by simp [h]
    have he := simplify_same_op op m ins g hg
    simp [h, opCount_cons, opCount, he]

lemma elim_opCount_le (test : GateOp → Bool) (n : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      opCount test (elim n gs acc).2 ≤ opCount test acc.2 + opCount test gs := by
  induction gs with
  | nil => intro acc; simp [elim, opCount]
  | cons g gs ih =>
    intro acc
    change opCount test (elim n gs (elimStep n acc g)).2 ≤ _
    apply (ih (elimStep n acc g)).trans
    simp only [elimStep, opCount_append, opCount_cons]
    have hb := simplify_opCount_le test g.op (n + acc.2.length)
       (g.inputs.map fun i => acc.1.getD i (Stat.const false))
    omega

def nonNotCount (gs : List Gate) : ℕ :=
  gs.countP (fun g => !(isNotGate g.op))

lemma elim_nonNotCount (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    nonNotCount (elim n gs acc).2 ≤ nonNotCount acc.2 + nonNotCount gs :=
  elim_opCount_le (fun op => !(isNotGate op)) n gs acc



end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg

theorem toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h

theorem clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem


def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)

theorem inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩


theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp


theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩


theorem agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno' := hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [hjl, getD_snoc_eq, hl, getD_snoc_eq, e]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj


end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm

theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h

theorem drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      nonNotCount gs' ≤ nonNotCount pre + nonNotCount post ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl (pre ++ g :: post) y o := by
  have hok : ∀ g' ∈ pre ++ g :: post, Ok g' := fun g' hg' => (clean_nok _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre, Ok g' := fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post, Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k → Bool, Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k, [])) :=
    fun y => inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k → Bool, (wiresFrom pre (List.ofFn y)).length = k + pre.length := by
    intro y; rw [length_wiresFrom]; simp
  have hfull : ∀ y : Fin k → Bool, wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)]) := by
    intro y; rw [wiresFrom_append]; rfl
  have hgv : ∀ y : Fin k → Bool, vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false) := by
    intro y
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false = _
    rw [hfull, getD_wiresFrom _ _ _ (by simp [hwl y]), getD_snoc_len _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2) := by
    intro y
    obtain ⟨hl, hi⟩ := inv1 y
    refine ⟨by simp [hl], ?_⟩
    intro a
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).val
        (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y)) = _
    by_cases hal : a = (elim k pre (idStats k, [])).1.length
    · rw [hal, getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨(hS y).1, by rw [(hS y).2, hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)) := by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k, [])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).2.length + 1 ≤ (pre ++ g :: post).length := by
    have h1 : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).2.length
        ≤ (elim k pre (idStats k, [])).2.length + post.length := elim_len k post _
    have h2 : (elim k pre (idStats k, [])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k, [])
    simp only [List.length_append, List.length_cons]
    omega
  have hval : ∀ y : Fin k → Bool,
      ((elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | wire j =>
    refine ⟨_, j, hc3, hlen, ?_, ?_⟩
    · exact (elim_nonNotCount k post _).trans (Nat.add_le_add_right
        (by simpa [nonNotCount] using elim_nonNotCount k pre (idStats k, [])) _)
    · intro y
      have h := hval y
      rw [hst] at h
      exact h

theorem drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧ nonNotCount gs' ≤ nonNotCount (gs.eraseIdx p) ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  rw [List.eraseIdx_append_of_length_le le_rfl, Nat.sub_self, List.eraseIdx_cons_zero]
  have hcount : nonNotCount (pre ++ post) = nonNotCount pre + nonNotCount post := by
    simp [nonNotCount]
  rw [hcount]
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Stat.const false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre, Ok g' :=
    fun g' h => (clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1 := inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1, ?_⟩
  rw [(inv1.2 j).2, heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append, getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom]; simp; omega)]


end CircuitProof

namespace PetersenCutTrace

open PEqualNP.CircuitLowerBounds
open CircuitProof

def avoid {W : Type} (edge : W → W → Prop) (cut : W) (a b : W) : Prop :=
  edge a b ∧ a ≠ cut ∧ b ≠ cut

theorem difference_traces {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut : W) (x y : W → Bool)
    (order : ∀ a b, edge a b → rank a < rank b)
    (localStep : ∀ b, ¬ input b → x b ≠ y b → ∃ a, edge a b ∧ x a ≠ y a)
    (sameCut : x cut = y cut) {out : W} (different : x out ≠ y out) :
    ∃ a, input a ∧ x a ≠ y a ∧ Relation.ReflTransGen (avoid edge cut) a out := by
  classical
  have track : ∀ k b, rank b = k → x b ≠ y b →
      ∃ a, input a ∧ x a ≠ y a ∧ Relation.ReflTransGen (avoid edge cut) a b := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro b hb diff
      by_cases hInput : input b
      · exact ⟨b, hInput, diff, Relation.ReflTransGen.refl⟩
      · obtain ⟨p, hp, dp⟩ := localStep b hInput diff
        have earlier : rank p < k := (order p b hp).trans_eq hb
        obtain ⟨a, ha, da, path⟩ := ih (rank p) earlier p rfl dp
        have pOff : p ≠ cut := by rintro rfl; exact dp sameCut
        have bOff : b ≠ cut := by rintro rfl; exact diff sameCut
        exact ⟨a, ha, da, path.tail ⟨hp, pOff, bOff⟩⟩
  exact track (rank out) out rfl different

theorem cut_agreement {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut out : W) (x y : W → Bool)
    (order : ∀ a b, edge a b → rank a < rank b)
    (localStep : ∀ b, ¬ input b → x b ≠ y b → ∃ a, edge a b ∧ x a ≠ y a)
    (sameCut : x cut = y cut)
    (blocked : ∀ a, input a → x a ≠ y a →
      ¬ Relation.ReflTransGen (avoid edge cut) a out) : x out = y out := by
  by_contra different
  obtain ⟨a, ha, da, reaches⟩ := difference_traces rank input edge cut x y
    order localStep sameCut different
  exact blocked a ha da reaches

theorem unary_factor {A : Type} (w f : A → Bool)
    (h : ∀ x y, w x = w y → f x = f y) :
    ∃ outer : Bool → Bool, ∀ x, outer (w x) = f x := by
  classical
  let outer (b : Bool) := if hb : ∃ a, w a = b then f (Classical.choose hb) else false
  refine ⟨outer, fun x => ?_⟩
  have hx : ∃ a, w a = w x := ⟨x, rfl⟩
  unfold outer
  rw [dite_eq_left hx]
  exact h _ _ (Classical.choose_spec hx)

def inputWire {n : Nat} (gs : List Gate) (v : Fin n) : Fin (n + gs.length) :=
  v.castLE (Nat.le_add_right n gs.length)

def readEdge {n : Nat} (gs : List Gate) (a b : Fin (n + gs.length)) : Prop :=
  ∃ (p : Nat) (g : Gate), gs[p]? = some g ∧ b.val = n + p ∧ a.val ∈ g.inputs

theorem read_order {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    {a b : Fin (n + gs.length)} (edge : readEdge gs a b) : a.val < b.val := by
  obtain ⟨p, g, hpg, hb, ha⟩ := edge
  rw [hb]
  exact (hcl p g hpg).lt _ ha

private theorem gate_difference {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (x y : Fin n → Bool) (b : Fin (n + gs.length)) (notInput : ¬ b.val < n)
    (diff : vl gs x b.val ≠ vl gs y b.val) :
    ∃ a : Fin (n + gs.length), readEdge gs a b ∧ vl gs x a.val ≠ vl gs y a.val := by
  let p := b.val - n
  have hb : b.val = n + p := by dsimp [p]; omega
  have hp : p < gs.length := by have := b.isLt; omega
  let g := gs[p]
  have hpg : gs[p]? = some g := List.getElem?_eq_getElem hp
  have differingRead : ∃ a ∈ g.inputs, vl gs x a ≠ vl gs y a := by
    classical
    by_contra none
    apply diff
    rw [hb]
    exact vl_congr gs hcl x y p g hpg (fun a ha => by
      by_contra da
      exact none ⟨a, ha, da⟩)
  obtain ⟨a, ha, da⟩ := differingRead
  have ha' := (hcl p g hpg).lt a ha
  refine ⟨⟨a, by have := b.isLt; omega⟩, ⟨p, g, hpg, hb, ha⟩, da⟩

theorem circuit_cut_agreement {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (x y : Fin n → Bool)
    (sameCut : vl gs x cut.val = vl gs y cut.val)
    (blocked : ∀ i : Fin n, x i ≠ y i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    vl gs x out.val = vl gs y out.val := by
  apply cut_agreement Fin.val (fun v => v.val < n) (readEdge gs) cut out
    (fun v => vl gs x v.val) (fun v => vl gs y v.val)
  · exact fun _ _ e => read_order hcl e
  · exact gate_difference hcl x y
  · exact sameCut
  · intro a ha diff
    let i : Fin n := ⟨a.val, ha⟩
    have sameWire : inputWire gs i = a := Fin.ext rfl
    have di : x i ≠ y i := by
      rw [vl_input gs x a.val ha, vl_input gs y a.val ha] at diff
      exact diff
    rw [← sameWire]
    exact blocked i di

theorem circuit_cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (blocked : ∀ i : Fin n, group i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    ∃ outer : Bool → Bool, ∀ x : Fin n → Bool, (∀ i, ¬ group i → x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val := by
  let Fiber := {x : Fin n → Bool // ∀ i, ¬ group i → x i = base i}
  obtain ⟨outer, ho⟩ := unary_factor
    (fun x : Fiber => vl gs x.val cut.val) (fun x : Fiber => vl gs x.val out.val) (by
      intro x y sameCut
      apply circuit_cut_agreement hcl cut out x.val y.val sameCut
      intro i diff
      apply blocked i
      by_contra notGroup
      exact diff ((x.property i notGroup).trans (y.property i notGroup).symm))
  exact ⟨outer, fun x agrees => ho ⟨x, agrees⟩⟩

end PetersenCutTrace

namespace CircuitProof.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof

def Dep {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x


structure Least (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop where
  hcl : CleanL m gs
  hev : ∀ x : Fin m → Bool, vl gs x o = f x
  hmin : ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
    nonNotCount gs' ≤ nonNotCount gs → gs.length ≤ gs'.length

def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs

theorem dep_nc {m : ℕ} {f : (Fin m → Bool) → Bool} {p : Fin m} (h : Dep f p) :
    ∃ x y : Fin m → Bool, f x ≠ f y := by
  obtain ⟨x, hx⟩ := h
  exact ⟨_, _, hx⟩

theorem reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q := by
  obtain ⟨g, hg, hw⟩ := h
  exact (hcl q g hg).lt w hw

theorem vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)


theorem clean_with_budget {n : ℕ} {f : (Fin n → Bool) → Bool} (C : Circuit)
    (hfan : FanInTwo C) (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ gs o, CleanL n gs ∧ nonNotCount gs ≤ nonNotCount C.gates ∧ ∀ x, vl gs x o = f x := by
  have hok : ∀ g ∈ C.gates, Ok g := hfan
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]
    rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · simpa [nonNotCount, hacc] using elim_nonNotCount n C.gates (idStats n, [])
    · intro y
      simpa only [hst, Stat.val, vl] using hval y

theorem least_with_budget {n : ℕ} {f : (Fin n → Bool) → Bool} (C : Circuit)
    (hfan : FanInTwo C) (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ gs o, Least n f gs o ∧ nonNotCount gs ≤ nonNotCount C.gates := by
  classical
  let admissible (t : ℕ) := ∃ gs o, CleanL n gs ∧ nonNotCount gs ≤ nonNotCount C.gates ∧
    (∀ x, vl gs x o = f x) ∧ gs.length = t
  obtain ⟨gs, o, clean, count, he⟩ := clean_with_budget C hfan hev hnc
  have existsAdmissible : ∃ t, admissible t := ⟨gs.length, gs, o, clean, count, he, rfl⟩
  obtain ⟨gs', o', hc, hb, he', hl⟩ := Nat.find_spec existsAdmissible
  refine ⟨gs', o', ⟨hc, he', ?_⟩, hb⟩
  intro testGates testOut testClean testEval testCost
  have lower := Nat.find_min' existsAdmissible
    (show admissible testGates.length from
      ⟨testGates, testOut, testClean, testCost.trans hb, testEval, rfl⟩)
  exact hl.trans_le lower


theorem drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o ≠ k + p) (hno : ∀ q, ¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧ nonNotCount gs' ≤ nonNotCount gs ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  have hpos : 0 < k + p := by
    rcases hcl p g hg with ⟨_, j, hj, _⟩ | ⟨_, j, _, hj, _, _⟩ <;> omega
  let g0 : Gate := ⟨GateOp.and, [0, 0]⟩
  let gs' := gs.set p g0
  have hlen : gs'.length = gs.length := by simp [gs']
  have hget_p : gs'[p]? = some g0 := by simp [gs', hp]
  have hget_ne : ∀ r, r ≠ p → gs'[r]? = gs[r]? := by
    intro r hr
    simp [gs', Ne.symm hr]
  have hcl' : CleanL k gs' := by
    intro r g' hr'
    by_cases hrp : r = p
    · subst hrp
      rw [hget_p] at hr'
      cases hr'
      exact Or.inr ⟨Or.inl rfl, 0, 0, hpos, hpos, rfl⟩
    · rw [hget_ne r hrp] at hr'
      exact hcl r g' hr'
  have hagree : ∀ y : Fin k → Bool, ∀ w, w ≠ k + p → vl gs' y w = vl gs y w := by
    intro y w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwk : w < k
      · rw [vl_input gs' y w hwk, vl_input gs y w hwk]
      · obtain ⟨r, rfl⟩ : ∃ r, w = k + r := ⟨w - k, by omega⟩
        have hrp : r ≠ p := fun e => hw (by rw [e])
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
          rw [vl_beyond gs' y _ (by omega), vl_beyond gs y _ (by omega)]
        | some g' =>
          have hr' : gs'[r]? = some g' := by rw [hget_ne r hrp]; exact hr
          rw [vl_gate gs' hcl' y r g' hr', vl_gate gs hcl y r g' hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hno r ⟨g', hr, e ▸ ha⟩)
  have halias : ∀ y : Fin k → Bool, vl gs' y (k + p) = vl gs' y 0 := by
    intro y
    rw [vl_gate gs' hcl' y p g0 hget_p]
    simp [g0, GateOp.eval]
  have hnc' : ∃ y y' : Fin k → Bool, vl gs' y o ≠ vl gs' y' o := by
    obtain ⟨y, y', h⟩ := hnc
    exact ⟨y, y', by rw [hagree y o ho, hagree y' o ho]; exact h⟩
  obtain ⟨gs'', o'', hc'', hl'', hcost, he''⟩ :=
    drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
  have hkeep : nonNotCount (gs'.eraseIdx p) ≤ nonNotCount gs := by
    rw [show gs'.eraseIdx p = gs.eraseIdx p from List.eraseIdx_set_eq]
    exact (List.eraseIdx_sublist gs p).countP_le
  exact ⟨gs'', o'', hc'', by omega, hcost.trans hkeep, fun y => by rw [he'' y, hagree y o ho]⟩

section LocalSection1

variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}

theorem Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) :
    ∃ y y' : Fin m → Bool, vl gs y o ≠ vl gs y' o := by
  obtain ⟨x, y, h⟩ := hnc
  exact ⟨x, y, by rw [L.hev, L.hev]; exact h⟩


theorem Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = vl gs u j := by
  intro hall
  obtain ⟨gs', o', hc', hl', hcost, he'⟩ := drop_alias m gs L.hcl o p j hp hj hall (L.ncv hnc)
  have hcost' : nonNotCount gs' ≤ nonNotCount gs :=
    hcost.trans (List.eraseIdx_sublist gs p).countP_le
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x) hcost'
  omega

theorem Least.live (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (ho : o ≠ m + p) : ∃ q, p < q ∧ Reads gs q (m + p) := by
  by_contra hno
  have hno' : ∀ q, ¬ Reads gs q (m + p) := by
    intro q hq
    by_cases hpq : p < q
    · exact hno ⟨q, hpq, hq⟩
    · have := reads_lt L.hcl hq
      omega
  obtain ⟨gs', o', hc', hl', hcost, he'⟩ := drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x) hcost
  omega

theorem Least.dep_read (L : Least m f gs o) (i : Fin m) (hd : Dep f i)
    (hnc : ∀ b : Bool, ∃ x y : Fin m → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b)) : ∃ q, Reads gs q i := by
  by_contra hno
  have hno' : ∀ g ∈ gs, (i : ℕ) ∉ g.inputs := by
    intro g hg hi
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno ⟨q, g, hq, hi⟩
  have hoi : o ≠ i := by
    intro e
    obtain ⟨x, y, hxy⟩ := hnc false
    apply hxy
    rw [← L.hev, ← L.hev, e, vl_input gs _ i i.isLt, vl_input gs _ i i.isLt]
    simp
  obtain ⟨x, hx⟩ := hd
  apply hx
  rw [← L.hev, ← L.hev]
  refine agree_except i gs _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjm : j < m
  · rw [show (List.ofFn (Function.update x i (!x i))).getD j false
        = Function.update x i (!x i) ⟨j, hjm⟩ from getD_ofFn m _ false ⟨j, hjm⟩,
      show (List.ofFn x).getD j false = x ⟨j, hjm⟩ from getD_ofFn m x false ⟨j, hjm⟩]
    exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

end LocalSection1

end CircuitProof.Readers

namespace CircuitProof.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof

open CircuitProof.Readers

theorem pq2f_nodup {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) {p : ℕ} {g : Gate}
    (hg : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) {a b : ℕ}
    (hin : g.inputs = [a, b]) : a ≠ b := by
  rintro rfl
  have hcl := L.hcl p g hg
  have hlt : a < m + p := by
    rcases hcl with ⟨h1, j, _, h2⟩ | ⟨h1, j, k, hj, hk, h2⟩
    · rw [hin] at h2; simp at h2
    · rw [hin] at h2; simp at h2; omega
  have hp : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  refine L.no_alias hnc p hp a hlt (fun u => ?_)
  rw [vl_gate gs L.hcl u p g hg, hin]
  rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]


end CircuitProof.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open CircuitProof.RunAsm

theorem least_wire_used {n out : Nat} {f : (Fin n → Bool) → Bool} {gs : List Gate}
    (least : Least n f gs out) (nonconstant : ∃ x y, f x ≠ f y)
    (dependent : ∀ v : Fin n, Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool), ∃ x y,
      f (Function.update x v b) ≠ f (Function.update y v b))
    (w : Nat) (amongWires : w < n + gs.length) (notOutput : w ≠ out) :
    ∃ p, Reads gs p w := by
  by_cases isInput : w < n
  · let v : Fin n := ⟨w, isInput⟩
    exact least.dep_read v (dependent v) (stillNonconstant v)
  · let p := w - n
    have wire : w = n + p := by dsimp [p]; omega
    have pLt : p < gs.length := by omega
    have notOut : out ≠ n + p := by omega
    obtain ⟨q, _, read⟩ := least.live nonconstant p pLt notOut
    exact ⟨q, wire.symm ▸ read⟩

theorem least_gate_inputs_nodup {n out : Nat} {f : (Fin n → Bool) → Bool} {gs : List Gate}
    (least : Least n f gs out) (nonconstant : ∃ x y, f x ≠ f y) (g : Gate) (present : g ∈ gs) :
    g.inputs.Nodup := by
  obtain ⟨slot, atSlot⟩ := List.mem_iff_getElem?.mp present
  rcases least.hcl slot g atSlot with ⟨_, a, _, args⟩ | ⟨ops, a, b, _, _, args⟩
  · simp [args]
  · have distinct := pq2f_nodup least nonconstant atSlot ops args
    simp [args, distinct]

theorem least_wire_readers_in_range {n out : Nat} {gs : List Gate}
    {f : (Fin n → Bool) → Bool} (least : Least n f gs out) (nonnull : ∃ x y, f x ≠ f y)
    (dependent : ∀ v : Fin n, Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool), ∃ x y,
      f (Function.update x v b) ≠ f (Function.update y v b))
    (w : Fin (n + gs.length)) (notOutput : w.val ≠ out) :
    ∃ (p : Nat) (g : Gate), gs[p]? = some g ∧ w.val ∈ g.inputs ∧ n + p < n + gs.length := by
  obtain ⟨p, g, hit, reads⟩ := least_wire_used least nonnull dependent stillNonconstant w.val w.isLt notOutput
  have bound := (List.getElem?_eq_some_iff.mp hit).1
  exact ⟨p, g, hit, reads, by omega⟩

namespace PetersenCutTrace

open PEqualNP.CircuitLowerBounds
open CircuitProof CircuitProof.Readers

def predecessors {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) : List (Fin (n + gs.length)) :=
  if gate : n ≤ b.val then
    let slot := b.val - n
    have hs : slot < gs.length := by have := b.isLt; omega
    let g := gs[slot]'hs
    g.inputs.attach.map fun a => ⟨a.val, by
      have atSlot : gs[slot]? = some g := List.getElem?_eq_getElem hs
      have before := (clean slot g atSlot).lt a.val a.property
      omega⟩
  else []

theorem predecessors_values {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (internal : n ≤ b.val) :
    (predecessors clean b).map Fin.val =
      (gs[b.val - n]'(by have := b.isLt; omega)).inputs := by
  simp [predecessors, internal, List.map_map, Function.comp_def]

theorem predecessors_nil_input {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (primary : b.val < n) : predecessors clean b = [] := by
  simp [predecessors, show ¬ n ≤ b.val by omega]

theorem predecessors_val_gate {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) {p : Nat} {g : Gate} (atSlot : gs[p]? = some g) (bWire : b.val = n + p) :
    (predecessors clean b).map Fin.val = g.inputs := by
  have isGate : n ≤ b.val := by omega
  have which : b.val - n = p := by omega
  have located := (List.getElem?_eq_some_iff.mp atSlot).2
  simpa [which, located] using predecessors_values clean b isGate

theorem predecessors_mem {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (a b : Fin (n + gs.length)) : a ∈ predecessors clean b ↔ readEdge gs a b := by
  by_cases internal : n ≤ b.val
  · let slot := b.val - n
    have hs : slot < gs.length := by have := b.isLt; dsimp [slot]; omega
    let g := gs[slot]'hs
    have wire : b.val = n + slot := by dsimp [slot]; omega
    have atSlot : gs[slot]? = some g := List.getElem?_eq_getElem hs
    have valList : (predecessors clean b).map Fin.val = g.inputs :=
      predecessors_values clean b internal
    constructor
    · intro mem
      refine ⟨slot, g, atSlot, wire, ?_⟩
      rw [← valList]
      exact List.mem_map.mpr ⟨a, mem, rfl⟩
    · rintro ⟨q, h, atQ, wireQ, inside⟩
      have same : q = slot := by omega
      subst q
      have gateSame : h = g := Option.some.inj (atQ.symm.trans atSlot)
      subst h
      rw [← valList] at inside
      obtain ⟨a', mem, equal⟩ := List.mem_map.mp inside
      exact (Fin.ext equal : a' = a) ▸ mem
  · have empty : predecessors clean b = [] := by simp [predecessors, internal]
    rw [empty]
    constructor
    · simp
    · rintro ⟨slot, g, _, wire, _⟩
      omega

theorem predecessors_nodup {n out : Nat} {gs : List Gate} {f : (Fin n → Bool) → Bool}
    (least : Least n f gs out) (nonnull : ∃ x y, f x ≠ f y) (b : Fin (n + gs.length)) :
    (predecessors least.hcl b).Nodup := by
  by_cases internal : n ≤ b.val
  · apply List.Nodup.of_map Fin.val
    rw [predecessors_values least.hcl b internal]
    exact PEqualNP.Outside.L_meta_4177.least_gate_inputs_nodup least nonnull _
      (List.getElem_mem (by have := b.isLt; omega))
  · simp [predecessors, internal]

end PetersenCutTrace

namespace PetersenScratch

open PEqualNP.MetaComplexity

def occurrences {n : ℕ} (i : Fin n) : DMFormula n → ℕ
  | .lit k _ => if k = i then 1 else 0
  | .and p q => occurrences i p + occurrences i q
  | .or p q => occurrences i p + occurrences i q

def hasPair {n : ℕ} (i j : Fin n) (p : DMFormula n) : Prop :=
  0 < occurrences i p ∨ 0 < occurrences j p

def pairInput {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (a b : Bool) (k : Fin n) : Bool :=
  if k = i then a else if k = j then b else base k

def pairValue {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n) :
    Bool → Bool → Bool :=
  fun a b => p.eval (pairInput i j base a b)

def binOp (conj : Bool) (a b : Bool) : Bool :=
  if conj then a && b else a || b

noncomputable def combine {n : ℕ} (conj : Bool) (i j : Fin n) (p q : DMFormula n)
    (P Q : Bool → Bool → Bool) : Bool → Bool → Bool := by
  classical
  exact if hasPair i j p then
    if hasPair i j q then fun a b => binOp conj (P a b) (Q a b) else P
    else Q

noncomputable def pairKernel {n : ℕ} (i j : Fin n) : DMFormula n → Bool → Bool → Bool
  | .lit k sign => fun a b =>
    let bit := if k = i then a else if k = j then b else false
    if sign then bit else !bit
  | .and p q => combine true i j p q (pairKernel i j p) (pairKernel i j q)
  | .or p q => combine false i j p q (pairKernel i j p) (pairKernel i j q)

private theorem eval_agree {n : ℕ} (p : DMFormula n) {x y : Fin n → Bool}
    (h : ∀ k, 0 < occurrences k p → x k = y k) : p.eval x = p.eval y := by
  induction p with
  | lit k s =>
    have e := h k (by simp [occurrences])
    simp [DMFormula.eval, e]
  | and p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [occurrences]; omega)),
      ihq (fun k hk => h k (by simp only [occurrences]; omega))]
  | or p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [occurrences]; omega)),
      ihq (fun k hk => h k (by simp only [occurrences]; omega))]

private theorem absent_left {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : occurrences i p = 0) (a a' b : Bool) :
    pairValue i j base p a b = pairValue i j base p a' b := by
  apply eval_agree
  intro k hk
  have ne : k ≠ i := by rintro rfl; omega
  simp [pairInput, ne]

private theorem absent_right {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : occurrences j p = 0) (a b b' : Bool) :
    pairValue i j base p a b = pairValue i j base p a b' := by
  apply eval_agree
  intro k hk
  have ne : k ≠ j := by rintro rfl; omega
  simp [pairInput, ne]

def changes (f : Bool → Bool → Bool) : Prop :=
  ∃ b, f false b ≠ f true b

private theorem changes_left {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b => op (P a b) (Q a b))
    (hQ : ∀ b, Q false b = Q true b) : changes P := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun hp => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hp, hQ])⟩

private theorem changes_right {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b => op (P a b) (Q a b))
    (hP : ∀ b, P false b = P true b) : changes Q := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun hq => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hq, hP])⟩

private theorem constant_pair {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : ¬ hasPair i j p) (a b : Bool) :
    pairValue i j base p a b = pairValue i j base p false false := by
  have hi : occurrences i p = 0 := by
    by_contra e
    exact h (Or.inl (by omega))
  have hj : occurrences j p = 0 := by
    by_contra e
    exact h (Or.inr (by omega))
  exact (absent_left hi a false b).trans (absent_right hj false b false)

private theorem neutral_right (conj c : Bool) (P : Bool → Bool → Bool)
    (h : ∃ a b a' b', binOp conj (P a b) c ≠ binOp conj (P a' b') c) :
    ∀ a b, binOp conj (P a b) c = P a b := by
  cases conj <;> cases c <;> simp [binOp] at h ⊢

private theorem bin_comm (conj a b : Bool) : binOp conj a b = binOp conj b a := by
  cases conj <;> cases a <;> cases b <;> rfl

private theorem combine_stable {n : ℕ} (i j : Fin n) (base : Fin n → Bool)
    (conj : Bool) (p q : DMFormula n)
    (hi : occurrences i p + occurrences i q ≤ 1)
    (hj : occurrences j p + occurrences j q ≤ 1)
    (present : hasPair i j p ∨ hasPair i j q)
    (dep_i : 0 < occurrences i p + occurrences i q →
      changes fun a b => binOp conj (pairValue i j base p a b) (pairValue i j base q a b))
    (dep_j : 0 < occurrences j p + occurrences j q →
      changes fun b a => binOp conj (pairValue i j base p a b) (pairValue i j base q a b))
    (ihp : occurrences i p ≤ 1 → occurrences j p ≤ 1 → hasPair i j p →
      (0 < occurrences i p → changes (pairValue i j base p)) →
      (0 < occurrences j p → changes fun b a => pairValue i j base p a b) →
      ∀ a b, pairValue i j base p a b = pairKernel i j p a b)
    (ihq : occurrences i q ≤ 1 → occurrences j q ≤ 1 → hasPair i j q →
      (0 < occurrences i q → changes (pairValue i j base q)) →
      (0 < occurrences j q → changes fun b a => pairValue i j base q a b) →
      ∀ a b, pairValue i j base q a b = pairKernel i j q a b)
    (a b : Bool) :
    binOp conj (pairValue i j base p a b) (pairValue i j base q a b) =
      combine conj i j p q (pairKernel i j p) (pairKernel i j q) a b := by
  classical
  have pl : hasPair i j p → ∀ a b, pairValue i j base p a b = pairKernel i j p a b := by
    intro hp
    apply ihp (by omega) (by omega) hp
    · intro h
      exact changes_left (dep_i (by omega)) (fun b => absent_left (by omega) false true b)
    · intro h
      exact changes_left (dep_j (by omega)) (fun a => absent_right (by omega) a false true)
  have ql : hasPair i j q → ∀ a b, pairValue i j base q a b = pairKernel i j q a b := by
    intro hq
    apply ihq (by omega) (by omega) hq
    · intro h
      exact changes_right (dep_i (by omega)) (fun b => absent_left (by omega) false true b)
    · intro h
      exact changes_right (dep_j (by omega)) (fun a => absent_right (by omega) a false true)
  have nonconst : ∃ a b a' b',
      binOp conj (pairValue i j base p a b) (pairValue i j base q a b) ≠
        binOp conj (pairValue i j base p a' b') (pairValue i j base q a' b') := by
    unfold hasPair at present
    rcases present with (h | h) | (h | h)
    · obtain ⟨b, h⟩ := dep_i (by omega)
      exact ⟨false, b, true, b, h⟩
    · obtain ⟨a, h⟩ := dep_j (by omega)
      exact ⟨a, false, a, true, h⟩
    · obtain ⟨b, h⟩ := dep_i (by omega)
      exact ⟨false, b, true, b, h⟩
    · obtain ⟨a, h⟩ := dep_j (by omega)
      exact ⟨a, false, a, true, h⟩
  by_cases hp : hasPair i j p
  · by_cases hq : hasPair i j q
    · simp [combine, hp, hq, pl hp, ql hq]
    · rw [constant_pair hq a b]
      have hn := nonconst
      simp_rw [constant_pair hq] at hn
      rw [neutral_right conj _ _ hn a b, pl hp]
      simp [combine, hp, hq]
  · have hq := present.resolve_left hp
    rw [constant_pair hp a b, bin_comm]
    have hn := nonconst
    simp_rw [constant_pair hp, bin_comm conj (pairValue i j base p false false)] at hn
    rw [neutral_right conj _ _ hn a b, ql hq]
    simp [combine, hp]

private theorem stable_pair {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n)
    (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1) (present : hasPair i j p)
    (dep_i : 0 < occurrences i p → changes (pairValue i j base p))
    (dep_j : 0 < occurrences j p → changes fun b a => pairValue i j base p a b) :
    ∀ a b, pairValue i j base p a b = pairKernel i j p a b := by
  induction p with
  | lit k s =>
    intro a b
    by_cases hki : k = i
    · simp [pairValue, pairKernel, DMFormula.eval, pairInput, hki]
    · have hkj : k = j := by
        by_contra h
        simp [hasPair, occurrences, hki, h] at present
      simp [pairValue, pairKernel, DMFormula.eval, pairInput, hkj]
  | and p q ihp ihq =>
    have present' : hasPair i j p ∨ hasPair i j q := by
      unfold hasPair at *
      simp only [occurrences] at present
      omega
    exact combine_stable i j base true p q hi hj present' dep_i dep_j ihp ihq
  | or p q ihp ihq =>
    have present' : hasPair i j p ∨ hasPair i j q := by
      unfold hasPair at *
      simp only [occurrences] at present
      omega
    exact combine_stable i j base false p q hi hj present' dep_i dep_j ihp ihq

theorem fixed_pair_invariant {n : ℕ} (i j : Fin n) (p : DMFormula n)
    (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1)
    (baseA baseO : Fin n → Bool) (outerA outerO : Bool → Bool)
    (hA : ∀ a b, outerA (pairValue i j baseA p a b) = (a && b))
    (hO : ∀ a b, outerO (pairValue i j baseO p a b) = (a || b)) : False := by
  have depAi : changes (pairValue i j baseA p) := by
    refine ⟨true, fun h => ?_⟩
    have e := congrArg outerA h
    rw [hA, hA] at e
    cases e
  have depAj : changes fun b a => pairValue i j baseA p a b := by
    refine ⟨true, fun h => ?_⟩
    have e := congrArg outerA h
    rw [hA, hA] at e
    cases e
  have depOi : changes (pairValue i j baseO p) := by
    refine ⟨false, fun h => ?_⟩
    have e := congrArg outerO h
    rw [hO, hO] at e
    cases e
  have depOj : changes fun b a => pairValue i j baseO p a b := by
    refine ⟨false, fun h => ?_⟩
    have e := congrArg outerO h
    rw [hO, hO] at e
    cases e
  have present : hasPair i j p := by
    left
    by_contra! h
    obtain ⟨b, hb⟩ := depAi
    exact hb (absent_left (by omega) false true b)
  have stableA := stable_pair i j baseA p hi hj present (fun _ => depAi) (fun _ => depAj)
  have stableO := stable_pair i j baseO p hi hj present (fun _ => depOi) (fun _ => depOj)
  simp_rw [stableA] at hA
  simp_rw [stableO] at hO
  have ne : pairKernel i j p false false ≠ pairKernel i j p false true := by
    intro e
    have f := congrArg outerO e
    rw [hO, hO] at f
    cases f
  have zeros := hA false false
  have other := hA false true
  have one := hA true true
  cases hk : pairKernel i j p false false <;>
    cases hl : pairKernel i j p false true <;>
    cases hm : pairKernel i j p true true <;>
    simp_all

noncomputable def edgeValue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Bool := by
  classical
  exact decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)

private theorem edgeValue_true {n : ℕ} {G : SimpleGraph (Fin n)} {x : Fin n → Bool}
    {u v : Fin n} (h : G.Adj u v) (hu : x u = true) (hv : x v = true) :
    edgeValue G x = true := by
  classical
  unfold edgeValue
  exact decide_eq_true ⟨u, v, h, hu, hv⟩

private theorem edgeValue_false_pair {n : ℕ} {G : SimpleGraph (Fin n)} {x : Fin n → Bool}
    {u v : Fin n} (h : ¬ G.Adj u v) (active : ∀ w, x w = true → w = u ∨ w = v) :
    edgeValue G x = false := by
  classical
  unfold edgeValue
  apply decide_eq_false
  rintro ⟨s, t, es, hs, ht⟩
  rcases active s hs with rfl | rfl <;> rcases active t ht with rfl | rfl
  · exact G.irrefl es
  · exact h es
  · exact h es.symm
  · exact G.irrefl es

private theorem edge_pair_and {n : ℕ} {G : SimpleGraph (Fin n)} {i j : Fin n}
    (h : G.Adj i j) (a b : Bool) :
    edgeValue G (pairInput i j (fun _ => false) a b) = (a && b) := by
  cases a <;> cases b
  · apply edgeValue_false_pair (u := i) (v := i) G.irrefl
    intro k hk
    simp [pairInput] at hk
  · apply edgeValue_false_pair (u := j) (v := j) G.irrefl
    intro k hk
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [pairInput, hki, hkj] at hk ⊢
  · apply edgeValue_false_pair (u := i) (v := i) G.irrefl
    intro k hk
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [pairInput, hki, hkj] at hk ⊢
    assumption
  · exact edgeValue_true h (by simp [pairInput]) (by simp [pairInput, h.ne.symm])

private theorem edge_pair_or {n : ℕ} {G : SimpleGraph (Fin n)} {i j u v : Fin n}
    (hij : i ≠ j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u ≠ j) (hvi : v ≠ i) (huv : ¬ G.Adj u v) (a b : Bool) :
    edgeValue G (pairInput i j (fun k => decide (k = u ∨ k = v)) a b) = (a || b) := by
  have hu : pairInput i j (fun k => decide (k = u ∨ k = v)) a b u = true := by
    simp [pairInput, hiu.ne.symm, huj]
  have hv : pairInput i j (fun k => decide (k = u ∨ k = v)) a b v = true := by
    simp [pairInput, hvi, hjv.ne.symm]
  cases a <;> cases b
  · apply edgeValue_false_pair huv
    intro k hk
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp [pairInput, hki, hkj] at hk
    exact hk
  · exact edgeValue_true hjv (by simp [pairInput, hij.symm]) hv
  · exact edgeValue_true hiu (by simp [pairInput]) hu
  · exact edgeValue_true hiu (by simp [pairInput]) hu

theorem adjacent_cut_invariant {n : ℕ} (G : SimpleGraph (Fin n)) (i j u v : Fin n)
    (hij : G.Adj i j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u ≠ j) (hvi : v ≠ i) (huv : ¬ G.Adj u v)
    (p : DMFormula n) (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1)
    (factors : ∀ base : Fin n → Bool, ∃ outer : Bool → Bool, ∀ a b,
      outer (pairValue i j base p a b) = edgeValue G (pairInput i j base a b)) : False := by
  obtain ⟨outerA, ha⟩ := factors (fun _ => false)
  obtain ⟨outerO, ho⟩ := factors (fun k => decide (k = u ∨ k = v))
  exact fixed_pair_invariant i j p hi hj _ _ outerA outerO
    (fun a b => (ha a b).trans (edge_pair_and hij a b))
    (fun a b => (ho a b).trans (edge_pair_or hij.ne hiu hjv huj hvi huv a b))

end PetersenScratch

namespace PetersenCutFormula

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open CircuitProof
open PetersenScratch

def negFormula {n : Nat} : DMFormula n → DMFormula n
  | .lit i sign => .lit i (!sign)
  | .and a b => .or (negFormula a) (negFormula b)
  | .or a b => .and (negFormula a) (negFormula b)

theorem negFormula_eval {n : Nat} (p : DMFormula n) (x : Fin n → Bool) :
    (negFormula p).eval x = !(p.eval x) := by
  induction p with
  | lit i s =>
    cases s <;> cases e : x i <;> simp [negFormula, DMFormula.eval, e]
  | and a b iha ihb =>
    simp only [negFormula, DMFormula.eval, iha, ihb]
    cases a.eval x <;> cases b.eval x <;> rfl
  | or a b iha ihb =>
    simp only [negFormula, DMFormula.eval, iha, ihb]
    cases a.eval x <;> cases b.eval x <;> rfl

theorem negFormula_occurrences {n : Nat} (i : Fin n) (p : DMFormula n) :
    occurrences i (negFormula p) = occurrences i p := by
  induction p with
  | lit i s => rfl
  | and a b iha ihb => simp [negFormula, occurrences, iha, ihb]
  | or a b iha ihb => simp [negFormula, occurrences, iha, ihb]

def wireFormula {n : Nat} (fallback : Fin n) (gs : List Gate) (w : Nat) : DMFormula n :=
  if hw : w < n then
    .lit ⟨w, hw⟩ true
  else
    match gs[w - n]? with
    | none => .lit fallback true
    | some g =>
      match g.op, g.inputs with
      | .not, [a] =>
        if _ha : a < w then negFormula (wireFormula fallback gs a) else .lit fallback true
      | .and, [a, b] =>
        if _ha : a < w then
          if _hb : b < w then .and (wireFormula fallback gs a) (wireFormula fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | .or, [a, b] =>
        if _ha : a < w then
          if _hb : b < w then .or (wireFormula fallback gs a) (wireFormula fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | _, _ => .lit fallback true
termination_by w
decreasing_by all_goals assumption

theorem wireFormula_input {n : Nat} (fallback : Fin n) (gs : List Gate) (i : Fin n) :
    wireFormula fallback gs i.val = .lit i true := by
  rw [wireFormula]
  simp [i.isLt]

private theorem wireFormula_not {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .not)
    (inputs : g.inputs = [a]) (ha : a < n + p) :
    wireFormula fallback gs (n + p) = negFormula (wireFormula fallback gs a) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha]

private theorem wireFormula_and {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .and)
    (inputs : g.inputs = [a, b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .and (wireFormula fallback gs a) (wireFormula fallback gs b) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha, hb]

private theorem wireFormula_or {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .or)
    (inputs : g.inputs = [a, b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .or (wireFormula fallback gs a) (wireFormula fallback gs b) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha, hb]

theorem wireFormula_eval {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (x : Fin n → Bool) (w : Nat) (hw : w < n + gs.length) :
    (wireFormula fallback gs w).eval x = vl gs x w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hi : w < n
    · rw [wireFormula_input fallback gs ⟨w, hi⟩, vl_input gs x w hi]
      rfl
    · obtain ⟨p, rfl⟩ : ∃ p, w = n + p := ⟨w - n, by omega⟩
      have hp : p < gs.length := by omega
      let g := gs[p]
      have hg : gs[p]? = some g := List.getElem?_eq_getElem hp
      rcases hcl p g hg with ⟨op, a, ha, inputs⟩ | ⟨op | op, a, b, ha, hb, inputs⟩
      · rw [wireFormula_not fallback hg op inputs ha, negFormula_eval, ih a ha (by omega),
          vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]
      · rw [wireFormula_and fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega), ih b hb (by omega), vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]
      · rw [wireFormula_or fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega), ih b hb (by omega), vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]

theorem wireFormula_count_input {n : Nat} (fallback : Fin n) (gs : List Gate) (chosen i : Fin n) :
    occurrences chosen (wireFormula fallback gs i.val) = if i = chosen then 1 else 0 := by
  rw [wireFormula_input]
  rfl

theorem wireFormula_count_gate {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (chosen : Fin n) {p : Nat} {g : Gate} (hg : gs[p]? = some g) :
    occurrences chosen (wireFormula fallback gs (n + p)) =
      (g.inputs.map fun a => occurrences chosen (wireFormula fallback gs a)).sum := by
  rcases hcl p g hg with ⟨op, a, ha, inputs⟩ | ⟨op | op, a, b, ha, hb, inputs⟩
  · simp [wireFormula_not fallback hg op inputs ha, inputs, negFormula_occurrences]
  · simp [wireFormula_and fallback hg op inputs ha hb, inputs, occurrences]
  · simp [wireFormula_or fallback hg op inputs ha hb, inputs, occurrences]

theorem wireFormula_count_gate_fin {n : Nat} (fallback chosen : Fin n) {gs : List Gate}
    (hcl : CleanL n gs) {p : Nat} {g : Gate} (hg : gs[p]? = some g)
    {b : Fin (n + gs.length)} (hb : b.val = n + p)
    (parents : List (Fin (n + gs.length))) (parentsVal : parents.map Fin.val = g.inputs) :
    occurrences chosen (wireFormula fallback gs b.val) =
      (parents.map fun a => occurrences chosen (wireFormula fallback gs a.val)).sum := by
  rw [hb, wireFormula_count_gate fallback hcl chosen hg, ← parentsVal, List.map_map]
  rfl

end PetersenCutFormula

namespace PetersenCutIndependent

open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutFormula PetersenCutTrace PetersenScratch

theorem wireFormula_count_input_fin {n : Nat} {gs : List Gate} (fallback chosen : Fin n)
    (a : Fin (n + gs.length)) (ha : a.val < n) :
    occurrences chosen (wireFormula fallback gs a.val) =
      if a = inputWire gs chosen then 1 else 0 := by
  let i : Fin n := ⟨a.val, ha⟩
  have e : i = chosen ↔ a = inputWire gs chosen := by
    constructor
    · intro h
      exact Fin.ext (congrArg (fun k : Fin n => k.val) h)
    · intro h
      exact Fin.ext (congrArg (fun k : Fin (n + gs.length) => k.val) h)
  change occurrences chosen (wireFormula fallback gs i.val) = _
  simp only [wireFormula_count_input, e]

theorem cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (controlled : cut = out ∨ ∀ i : Fin n, group i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    ∃ outer : Bool → Bool, ∀ x : Fin n → Bool, (∀ i, ¬ group i → x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val := by
  rcases controlled with rfl | blocked
  · exact ⟨id, fun _ _ => rfl⟩
  · exact circuit_cut_factors hcl cut out group base blocked

theorem adjacent_cut_excluded {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (G : SimpleGraph (Fin n)) (cut out : Fin (n + gs.length))
    (computes : ∀ x, vl gs x out.val = edgeValue G x)
    (i j u v : Fin n) (hij : G.Adj i j) (hiu : G.Adj i u) (hjv : G.Adj j v)
    (huj : u ≠ j) (hvi : v ≠ i) (huv : ¬ G.Adj u v)
    (hi : occurrences i (wireFormula i gs cut.val) ≤ 1)
    (hj : occurrences j (wireFormula i gs cut.val) ≤ 1)
    (controlled : cut = out ∨ ∀ k : Fin n, (k = i ∨ k = j) →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out) : False := by
  refine adjacent_cut_invariant G i j u v hij hiu hjv huj hvi huv
    (wireFormula i gs cut.val) hi hj (fun base => ?_)
  obtain ⟨f, hf⟩ := cut_factors hcl cut out (fun k => k = i ∨ k = j) base controlled
  refine ⟨f, fun a b => ?_⟩
  have agree : ∀ k, ¬ (k = i ∨ k = j) → pairInput i j base a b k = base k := by
    intro k hk
    simp [pairInput, show k ≠ i from fun e => hk (Or.inl e),
      show k ≠ j from fun e => hk (Or.inr e)]
  unfold pairValue
  rw [wireFormula_eval i hcl _ cut.val cut.isLt]
  exact (hf _ agree).trans (computes _)

end PetersenCutIndependent

namespace FirstBranchRoute

open Relation

variable {m : Nat} (reads : Fin m → Fin m → Prop) (output : Fin m)

def Branches (v : Fin m) : Prop := ∃ a b, reads v a ∧ reads v b ∧ a ≠ b

def Terminal (v : Fin m) : Prop := v = output ∨ Branches reads v

def Follow (v w : Fin m) : Prop := reads v w ∧ ¬ Terminal reads output v

lemma follow_unique {v a b : Fin m} (first : Follow reads output v a) (next : Follow reads output v b) :
    a = b := by
  by_contra separate
  exact first.2 (Or.inr ⟨a, b, first.1, next.1, separate⟩)

variable (forward : ∀ {v w : Fin m}, reads v w → v < w)
variable (live : ∀ v : Fin m, v ≠ output → ∃ w, reads v w)

include forward live in
theorem exists_boundary (v : Fin m) :
    ∃ root : Fin m, Terminal reads output root ∧ ReflTransGen (Follow reads output) v root := by
  let distance (w : Fin m) := m - w.val
  induction v using (measure distance).wf.induction with
  | h v ih =>
    by_cases terminal : Terminal reads output v
    · exact ⟨v, terminal, ReflTransGen.refl⟩
    obtain ⟨next, edge⟩ := live v (fun e => terminal (Or.inl e))
    have increase := forward edge
    have closer : distance next < distance v := by
      dsimp [distance]
      have bounds := next.isLt
      change v.val < next.val at increase
      omega
    obtain ⟨root, stopped, route⟩ := ih next closer
    exact ⟨root, stopped, route.head ⟨edge, terminal⟩⟩

include forward in
theorem boundary_unique {v a b : Fin m} (terminalA : Terminal reads output a)
    (terminalB : Terminal reads output b) (routeA : ReflTransGen (Follow reads output) v a)
    (routeB : ReflTransGen (Follow reads output) v b) : a = b := by
  let distance (w : Fin m) := m - w.val
  induction v using (measure distance).wf.induction generalizing a b with
  | h v ih =>
    rcases routeA.cases_head with h | ⟨next, edge, tailA⟩
    · subst a
      rcases routeB.cases_head with h | ⟨_, edgeB, _⟩
      · exact h
      · exact (edgeB.2 terminalA).elim
    · rcases routeB.cases_head with h | ⟨nextB, edgeB, tailB⟩
      · subst b
        exact (edge.2 terminalB).elim
      have equal := follow_unique reads output edge edgeB
      subst nextB
      have increase := forward edge.1
      have closer : distance next < distance v := by
        dsimp [distance]
        have bounds := next.isLt
        change v.val < next.val at increase
        omega
      exact ih next closer terminalA terminalB tailA tailB

noncomputable def first (v : Fin m) : Fin m :=
  Classical.choose (exists_boundary reads output forward live v)

theorem first_stops (v : Fin m) : Terminal reads output (first reads output forward live v) :=
  (Classical.choose_spec (exists_boundary reads output forward live v)).1

theorem first_path (v : Fin m) : ReflTransGen (Follow reads output) v (first reads output forward live v) :=
  (Classical.choose_spec (exists_boundary reads output forward live v)).2

theorem first_of_terminal {v : Fin m} (stopped : Terminal reads output v) :
    first reads output forward live v = v :=
  boundary_unique reads output forward (first_stops reads output forward live v) stopped
    (first_path reads output forward live v) ReflTransGen.refl

theorem first_of_follows {v w : Fin m} (step : Follow reads output v w) :
    first reads output forward live v = first reads output forward live w :=
  boundary_unique reads output forward (first_stops reads output forward live v)
    (first_stops reads output forward live w) (first_path reads output forward live v)
    ((first_path reads output forward live w).head step)

include forward in
theorem path_forward {v w : Fin m} (route : ReflTransGen reads v w) : v ≤ w := by
  induction route with
  | refl => exact le_rfl
  | tail _ edge ih => exact le_trans ih (le_of_lt (forward edge))

lemma follows_is_read_path {v w : Fin m} (route : ReflTransGen (Follow reads output) v w) :
    ReflTransGen reads v w := by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1

theorem first_forward (v : Fin m) : v ≤ first reads output forward live v :=
  path_forward reads forward (follows_is_read_path reads output (first_path reads output forward live v))

theorem read_before {v w : Fin m} (route : ReflTransGen reads v w)
    (before : w ≤ first reads output forward live v) :
    ReflTransGen (Follow reads output) v w ∧ first reads output forward live w = first reads output forward live v := by
  induction route with
  | refl => exact ⟨ReflTransGen.refl, rfl⟩
  | tail _ edge ih =>
    have predecessorBefore := lt_of_lt_of_le (forward edge) before
    obtain ⟨tracked, label⟩ := ih (le_of_lt predecessorBefore)
    have step : Follow reads output _ _ := ⟨edge, fun stopped => by
      have self := first_of_terminal reads output forward live stopped
      rw [self] at label
      exact (ne_of_lt predecessorBefore) label⟩
    exact ⟨tracked.tail step, (first_of_follows reads output forward live step).symm.trans label⟩

theorem ancestor_first_le {v w : Fin m} (route : ReflTransGen reads v w)
    (stopped : Terminal reads output w) : first reads output forward live v ≤ w := by
  by_contra tooLate
  have earlier := lt_of_not_ge tooLate
  have same := (read_before reads output forward live route (le_of_lt earlier)).2
  rw [first_of_terminal reads output forward live stopped] at same
  exact (ne_of_lt earlier) same

theorem edge_before {v a b : Fin m} (route : ReflTransGen reads v a) (edge : reads a b)
    (bound : b ≤ first reads output forward live v) : Follow reads output a b := by
  have earlier := lt_of_lt_of_le (forward edge) bound
  have same := (read_before reads output forward live route (le_of_lt earlier)).2
  refine ⟨edge, fun stopped => ?_⟩
  rw [first_of_terminal reads output forward live stopped] at same
  exact (ne_of_lt earlier) same

def Avoid (cut v w : Fin m) : Prop := reads v w ∧ v ≠ cut

lemma avoiding_is_read_path (cut : Fin m) {v w : Fin m} (route : ReflTransGen (Avoid reads cut) v w) :
    ReflTransGen reads v w := by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1

theorem avoiding_stays_before {v w : Fin m}
    (route : ReflTransGen (Avoid reads (first reads output forward live v)) v w) :
    w ≤ first reads output forward live v := by
  induction route with
  | refl => exact first_forward reads output forward live v
  | tail prior edge ih =>
    have label := (read_before reads output forward live (avoiding_is_read_path reads _ prior) ih).2
    have earlier := lt_of_le_of_ne ih edge.2
    have following : Follow reads output _ _ := ⟨edge.1, fun terminal => by
      rw [first_of_terminal reads output forward live terminal] at label
      exact (ne_of_lt earlier) label⟩
    have same := (first_of_follows reads output forward live following).symm.trans label
    rw [← same]
    exact first_forward reads output forward live _

theorem no_avoiding_after {v w : Fin m} (after : first reads output forward live v < w) :
    ¬ ReflTransGen (Avoid reads (first reads output forward live v)) v w :=
  fun route => (not_lt_of_ge (avoiding_stays_before reads output forward live route)) after

include forward in
theorem unique_follow_predecessor {source a b goal : Fin m}
    (routeA : ReflTransGen (Follow reads output) source a) (edgeA : Follow reads output a goal)
    (routeB : ReflTransGen (Follow reads output) source b) (edgeB : Follow reads output b goal) : a = b := by
  let distance (w : Fin m) := m - w.val
  induction source using (measure distance).wf.induction generalizing a b with
  | h source ih =>
    rcases routeA.cases_head with aHere | ⟨nextA, stepA, laterA⟩
    · subst a
      rcases routeB.cases_head with bHere | ⟨next, stepB, later⟩
      · exact bHere
      have equal : next = goal := follow_unique reads output stepB edgeA
      subst next
      have increasing := path_forward reads forward (follows_is_read_path reads output later)
      exact (not_lt_of_ge increasing (forward edgeB.1)).elim
    · rcases routeB.cases_head with bHere | ⟨nextB, stepB, laterB⟩
      · subst b
        have equal : nextA = goal := follow_unique reads output stepA edgeB
        subst nextA
        have increasing := path_forward reads forward (follows_is_read_path reads output laterA)
        exact (not_lt_of_ge increasing (forward edgeA.1)).elim
      have equal := follow_unique reads output stepA stepB
      subst nextB
      have increase := forward stepA.1
      have closer : distance nextA < distance source := by
        dsimp [distance]
        have bounds := nextA.isLt
        change source.val < nextA.val at increase
        omega
      exact ih nextA closer laterA edgeA laterB edgeB

theorem unique_predecessor_before {source a b goal : Fin m}
    (bound : goal ≤ first reads output forward live source)
    (routeA : ReflTransGen reads source a) (edgeA : reads a goal)
    (routeB : ReflTransGen reads source b) (edgeB : reads b goal) : a = b := by
  have aBound := le_trans (le_of_lt (forward edgeA)) bound
  have bBound := le_trans (le_of_lt (forward edgeB)) bound
  exact unique_follow_predecessor reads output forward
    (read_before reads output forward live routeA aBound).1
    (edge_before reads output forward live routeA edgeA bound)
    (read_before reads output forward live routeB bBound).1
    (edge_before reads output forward live routeB edgeB bound)

lemma witness_of_positive_sum {α : Type*} (weight : α → Nat) (xs : List α)
    (positive : 0 < (xs.map weight).sum) : ∃ a ∈ xs, 0 < weight a := by
  induction xs with
  | nil => simp at positive
  | cons a rest ih =>
    by_cases h : 0 < weight a
    · exact ⟨a, by simp, h⟩
    have hr : 0 < (rest.map weight).sum := by
      simp only [List.map_cons, List.sum_cons] at positive
      omega
    obtain ⟨b, hb, hbPos⟩ := ih hr
    exact ⟨b, by simp [hb], hbPos⟩

lemma sum_le_one_of_unique_positive {α : Type*} (weight : α → Nat) (xs : List α)
    (distinct : xs.Nodup) (small : ∀ a ∈ xs, weight a ≤ 1)
    (unique : ∀ a ∈ xs, ∀ b ∈ xs, 0 < weight a → 0 < weight b → a = b) :
    (xs.map weight).sum ≤ 1 := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    simp only [List.nodup_cons] at distinct
    simp only [List.map_cons, List.sum_cons]
    by_cases h : weight a = 0
    · rw [h, Nat.zero_add]
      exact ih distinct.2 (fun b hb => small b (by simp [hb]))
        (fun b hb c hc => unique b (by simp [hb]) c (by simp [hc]))
    have restZero : (rest.map weight).sum = 0 := by
      by_contra some
      obtain ⟨b, hb, hbPos⟩ := witness_of_positive_sum weight rest (by omega)
      have equal := unique a (by simp) b (by simp [hb]) (by omega) hbPos
      exact distinct.1 (by simpa [equal] using hb)
    rw [restZero, Nat.add_zero]
    exact small a (by simp)

section Count

variable (parents : Fin m → List (Fin m))
variable (reads_parent : ∀ a b : Fin m, reads a b ↔ a ∈ parents b)
variable (weight : Fin m → Nat) (source : Fin m)
variable (other_weight : ∀ v : Fin m, v ≠ source → weight v = ((parents v).map weight).sum)

include forward reads_parent other_weight in
theorem weight_positive_path {v : Fin m} (positive : 0 < weight v) : ReflTransGen reads source v := by
  revert positive
  induction v using (measure (fun w : Fin m => w.val)).wf.induction with
  | h v ih =>
    intro positive
    by_cases isSource : v = source
    · subst v
      exact ReflTransGen.refl
    rw [other_weight v isSource] at positive
    obtain ⟨a, member, hp⟩ := witness_of_positive_sum weight (parents v) positive
    have edge := (reads_parent a v).mpr member
    have earlier := forward edge
    exact (ih a earlier hp).tail edge

include reads_parent other_weight in
theorem weight_before_le_one (rootWeight : weight source = 1) (distinct : ∀ v, (parents v).Nodup)
    {v : Fin m} (bound : v ≤ first reads output forward live source) : weight v ≤ 1 := by
  revert bound
  induction v using (measure (fun w : Fin m => w.val)).wf.induction with
  | h v ih =>
    intro bound
    by_cases isSource : v = source
    · subst v
      exact le_of_eq rootWeight
    rw [other_weight v isSource]
    apply sum_le_one_of_unique_positive weight (parents v) (distinct v)
    · intro a member
      have earlier := forward ((reads_parent a v).mpr member)
      exact ih a earlier (le_trans (le_of_lt earlier) bound)
    · intro a ma b mb ha hb
      exact unique_predecessor_before reads output forward live bound
        (weight_positive_path reads forward parents reads_parent weight source other_weight ha)
        ((reads_parent a v).mpr ma)
        (weight_positive_path reads forward parents reads_parent weight source other_weight hb)
        ((reads_parent b v).mpr mb)

end Count

end FirstBranchRoute

namespace PetersenFirstGroup

open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutFormula PetersenCutIndependent PetersenCutTrace PetersenScratch

noncomputable def firstInputBoundary {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (i : Fin n) : Fin (n + gs.length) :=
  FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)

noncomputable def firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) : Finset (Fin n) :=
  Finset.univ.filter fun i => firstInputBoundary clean out live i = cut

theorem mem_firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) (i : Fin n) :
    i ∈ firstInputGroup clean out live cut ↔ firstInputBoundary clean out live i = cut := by
  simp [firstInputGroup]

theorem wire_le_output {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (w : Fin (n + gs.length)) : w ≤ out := by
  let last : Fin (n + gs.length) := ⟨n + gs.length - 1, by have := out.isLt; omega⟩
  have top (v : Fin (n + gs.length)) : v ≤ last := by
    change v.val ≤ n + gs.length - 1
    have := v.isLt
    omega
  have lastOut : last = out := by
    by_contra notOutput
    obtain ⟨v, e⟩ := live last notOutput
    exact (not_lt_of_ge (top v)) (read_order clean e)
  exact lastOut ▸ top w

theorem firstInputBoundary_occurrences_le_one {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (fallback chosen : Fin n) :
    occurrences chosen (wireFormula fallback gs (firstInputBoundary clean out live chosen).val)
      ≤ 1 := by
  let weight (a : Fin (n + gs.length)) := occurrences chosen (wireFormula fallback gs a.val)
  have sourcePrimary : (inputWire gs chosen).val < n := chosen.isLt
  have atSource : weight (inputWire gs chosen) = 1 := by
    dsimp [weight]
    rw [wireFormula_count_input_fin fallback chosen _ sourcePrimary, ite_eq_left rfl]
  have otherWeight : ∀ w : Fin (n + gs.length), w ≠ inputWire gs chosen →
      weight w = ((predecessors clean w).map weight).sum := by
    intro w other
    by_cases primary : w.val < n
    · simp [weight, wireFormula_count_input_fin fallback chosen w primary, other,
        predecessors_nil_input clean w primary]
    · let p := w.val - n
      have hp : p < gs.length := by have := w.isLt; dsimp [p]; omega
      have hw : w.val = n + p := by dsimp [p]; omega
      let g := gs[p]
      have atSlot : gs[p]? = some g := List.getElem?_eq_getElem hp
      exact wireFormula_count_gate_fin fallback chosen clean atSlot hw _
        (predecessors_val_gate clean w atSlot hw)
  exact FirstBranchRoute.weight_before_le_one (readEdge gs) out (read_order clean) live
    (predecessors clean) (fun a b => (predecessors_mem clean a b).symm) weight
    (inputWire gs chosen) otherWeight atSource distinct le_rfl

theorem firstInputGroup_controlled {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) :
    cut = out ∨ ∀ k : Fin n, k ∈ firstInputGroup clean out live cut →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out := by
  by_cases terminal : cut = out
  · exact Or.inl terminal
  right
  intro k member path
  have before : cut < out := lt_of_le_of_ne (wire_le_output clean out live cut) terminal
  have firstHere := (mem_firstInputGroup clean out live cut k).mp member
  have after : firstInputBoundary clean out live k < out := by rwa [firstHere]
  have blocked := FirstBranchRoute.no_avoiding_after (readEdge gs) out
    (read_order clean) live after
  apply blocked
  change Relation.ReflTransGen (FirstBranchRoute.Avoid (readEdge gs)
    (firstInputBoundary clean out live k)) (inputWire gs k) out
  rw [firstHere]
  exact Relation.ReflTransGen.mono (fun _ _ e => ⟨e.1, e.2.1⟩) _ _ path

theorem firstInputGroup_independent {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (G : SimpleGraph (Fin n)) (computes : ∀ x, vl gs x out.val = edgeValue G x)
    (witnesses : ∀ i j, G.Adj i j → ∃ u v,
      G.Adj i u ∧ G.Adj j v ∧ u ≠ j ∧ v ≠ i ∧ ¬ G.Adj u v)
    (cut : Fin (n + gs.length)) : BranchGraph.Independent G (firstInputGroup clean out live cut) := by
  intro i iIn j jIn adjacent
  obtain ⟨u, v, hiu, hjv, huj, hvi, huv⟩ := witnesses i j adjacent
  have iFirst := (mem_firstInputGroup clean out live cut i).mp iIn
  have jFirst := (mem_firstInputGroup clean out live cut j).mp jIn
  have iCount := firstInputBoundary_occurrences_le_one clean out live distinct i i
  have jCount := firstInputBoundary_occurrences_le_one clean out live distinct i j
  rw [iFirst] at iCount
  rw [jFirst] at jCount
  refine adjacent_cut_excluded clean G cut out computes i j u v adjacent hiu hjv huj hvi
    huv iCount jCount ?_
  rcases firstInputGroup_controlled clean out live cut with stopped | blocked
  · exact Or.inl stopped
  · exact Or.inr (fun k hk => blocked k (hk.elim (fun h => h.symm ▸ iIn) (fun h => h.symm ▸ jIn)))

end PetersenFirstGroup

namespace PetersenNine

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


abbrev Vertex := Fin 9
abbrev Edges := List (Vertex × Vertex)


def edges : Edges := [(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (5,7), (6,8), (8,5)]

def edgeFun (es : Edges) (x : Vertex → Bool) : Bool :=
  es.any (fun edge => x edge.1 && x edge.2)


lemma noLoops : ∀ e ∈ edges, e.1 ≠ e.2 := by decide

lemma edgeFun_true (es : Edges) (x : Vertex → Bool) :
    edgeFun es x = true ↔ ∃ a b, (a, b) ∈ es ∧ x a = true ∧ x b = true := by
  simp only [edgeFun, List.any_eq_true, Bool.and_eq_true, Prod.exists]


def graph (es : Edges) (noSelf : ∀ e ∈ es, e.1 ≠ e.2) : SimpleGraph Vertex where
  Adj a b := (a, b) ∈ es ∨ (b, a) ∈ es
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨fun v h => h.elim (fun he => noSelf (v, v) he rfl) (fun he => noSelf (v, v) he rfl)⟩

end PetersenNine

namespace PetersenGroupBFS

structure MaskGraph where
  width : Nat
  adjacency : Nat → Nat

def bit (vertex : Nat) : Nat :=
  Nat.shiftLeft 1 vertex

def fullMask (g : MaskGraph) : Nat :=
  bit g.width - 1

def residualNeighbors (g : MaskGraph) (deleted vertex : Nat) : Nat :=
  Nat.land (g.adjacency vertex) (Nat.xor (fullMask g) deleted)

def closeIsolates (g : MaskGraph) (deleted : Nat) : Nat :=
  (List.range g.width).foldl
    (fun mask v => if residualNeighbors g deleted v = 0 then Nat.lor mask (bit v) else mask)
    deleted

def twinClass (g : MaskGraph) (deleted vertex : Nat) : Nat :=
  (List.range g.width).foldl
    (fun mask v => if !(Nat.testBit deleted v) &&
        (residualNeighbors g deleted v == residualNeighbors g deleted vertex)
      then Nat.lor mask (bit v) else mask)
    0

theorem bit_at (v w : Nat) : (bit v).testBit w = decide (v = w) := by
  simp [bit, Nat.shiftLeft_eq, Nat.testBit_two_pow]

theorem full_at (g : MaskGraph) (w : Nat) :
    (fullMask g).testBit w = decide (w < g.width) := by
  simp [fullMask, bit, Nat.shiftLeft_eq]

theorem neighbor_at (g : MaskGraph) (deleted v w : Nat) (hw : w < g.width) :
    (residualNeighbors g deleted v).testBit w =
      ((g.adjacency v).testBit w && !(deleted.testBit w)) := by
  simp [residualNeighbors, Nat.testBit_xor, full_at, hw]

private theorem fold_mask_at (vertices : List Nat) (p : Nat → Prop) [DecidablePred p]
    (initial w : Nat) :
    (vertices.foldl (fun m v => if p v then Nat.lor m (bit v) else m) initial).testBit w =
      (initial.testBit w || (vertices.any fun v => decide (p v) && (v == w))) := by
  induction vertices generalizing initial with
  | nil => simp
  | cons v vertices ih =>
    simp only [List.foldl_cons, List.any_cons]
    rw [ih]
    by_cases h : p v <;> simp [h, bit_at, Bool.or_assoc, Bool.beq_eq_decide_eq]

private theorem any_mask_at (p : Nat → Prop) [DecidablePred p] (n w : Nat) :
    ((List.range n).any fun v => decide (p v) && (v == w)) =
      (decide (w < n) && decide (p w)) := by
  rw [Bool.eq_iff_iff, List.any_eq_true, Bool.and_eq_true]
  simp only [List.mem_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨v, hv, hp, rfl⟩
    exact ⟨hv, hp⟩
  · rintro ⟨hw, hp⟩
    exact ⟨w, hw, hp, rfl⟩

theorem close_at (g : MaskGraph) (deleted w : Nat) :
    (closeIsolates g deleted).testBit w =
      (deleted.testBit w || (decide (w < g.width) && decide (residualNeighbors g deleted w = 0))) := by
  unfold closeIsolates
  rw [fold_mask_at, any_mask_at]

theorem class_at (g : MaskGraph) (deleted v w : Nat) :
    (twinClass g deleted v).testBit w =
      (decide (w < g.width) &&
        (!(deleted.testBit w) && (residualNeighbors g deleted w == residualNeighbors g deleted v))) := by
  unfold twinClass
  rw [fold_mask_at, any_mask_at]
  simp [Bool.beq_eq_decide_eq]

theorem bit_eq_power (width : Nat) : bit width = 2 ^ width := by
  simp [bit, Nat.shiftLeft_eq]

theorem lor_bounded {width a b : Nat} (ha : a < bit width) (hb : b < bit width) :
    Nat.lor a b < bit width := by
  rw [bit_eq_power] at ha hb ⊢
  exact Nat.or_lt_two_pow ha hb

theorem high_false {width m w : Nat} (hm : m < bit width) (hw : width ≤ w) :
    m.testBit w = false := by
  rw [bit_eq_power] at hm
  exact Nat.testBit_lt_two_pow (hm.trans_le (Nat.pow_le_pow_right (by decide) hw))

theorem mask_ext {width a b : Nat} (ha : a < bit width) (hb : b < bit width)
    (same : ∀ w < width, a.testBit w = b.testBit w) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro w
  by_cases hw : w < width
  · exact same w hw
  · rw [high_false ha (Nat.le_of_not_gt hw), high_false hb (Nat.le_of_not_gt hw)]

theorem neighbor_bounded (g : MaskGraph) (deleted v : Nat) (hd : deleted < bit g.width) :
    residualNeighbors g deleted v < bit g.width := by
  rw [bit_eq_power]
  apply Nat.lt_pow_two_of_testBit
  intro w hw
  simp [residualNeighbors, full_at, Nat.not_lt_of_ge hw, high_false hd hw]

theorem close_bounded (g : MaskGraph) (deleted : Nat) (hd : deleted < bit g.width) :
    closeIsolates g deleted < bit g.width := by
  rw [bit_eq_power]
  apply Nat.lt_pow_two_of_testBit
  intro w hw
  simp [close_at, Nat.not_lt_of_ge hw, high_false hd hw]

theorem class_bounded (g : MaskGraph) (deleted v : Nat) :
    twinClass g deleted v < bit g.width := by
  rw [bit_eq_power]
  apply Nat.lt_pow_two_of_testBit
  intro w hw
  simp [class_at, Nat.not_lt_of_ge hw]

def step (g : MaskGraph) (deleted : Nat) : List Nat :=
  deleted :: (List.range g.width).filterMap fun v =>
    if !(Nat.testBit deleted v) && (residualNeighbors g deleted v != 0)
    then some (closeIsolates g (Nat.lor deleted (twinClass g deleted v)))
    else none

def frontier (g : MaskGraph) : Nat → List Nat
  | 0 => [closeIsolates g 0]
  | depth + 1 => ((frontier g depth).flatMap (step g)).eraseDups

theorem advance {g : MaskGraph} {depth deleted next : Nat}
    (hd : deleted ∈ frontier g depth) (hs : next ∈ step g deleted) :
    next ∈ frontier g (depth + 1) := by
  rw [frontier, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨deleted, hd, hs⟩

theorem stay {g : MaskGraph} {depth deleted : Nat} (hd : deleted ∈ frontier g depth) :
    deleted ∈ frontier g (depth + 1) :=
  advance hd (by simp [step])

theorem advance_class {g : MaskGraph} {depth deleted vertex : Nat}
    (hd : deleted ∈ frontier g depth) (hv : vertex < g.width)
    (hlive : Nat.testBit deleted vertex = false)
    (hne : residualNeighbors g deleted vertex ≠ 0) :
    closeIsolates g (Nat.lor deleted (twinClass g deleted vertex)) ∈ frontier g (depth + 1) := by
  apply advance hd
  apply List.mem_cons_of_mem
  rw [List.mem_filterMap]
  refine ⟨vertex, List.mem_range.mpr hv, ?_⟩
  simp [hlive, hne]

def petersenNine : MaskGraph :=
  ⟨9, fun v => (#[50, 69, 138, 276, 9, 385, 258, 36, 104] : Array Nat)[v]?.getD 0⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem petersen_nine_no_four : fullMask petersenNine ∉ frontier petersenNine 4 := by
  decide +kernel

end PetersenGroupBFS

namespace PetersenMaskBridge

open PetersenGroupBFS
open BranchGraph

def decode (g : MaskGraph) (mask : Nat) : Finset (Fin g.width) :=
  Finset.univ.filter (fun v => mask.testBit v.val)

@[simp] lemma mem_decode (g : MaskGraph) (mask : Nat) (v : Fin g.width) :
    v ∈ decode g mask ↔ mask.testBit v.val = true := by
  simp [decode]

@[simp] lemma decode_zero (g : MaskGraph) : decode g 0 = ∅ := by
  ext v
  simp

@[simp] lemma decode_full (g : MaskGraph) : decode g (fullMask g) = Finset.univ := by
  ext v
  simp [full_at, v.isLt]

lemma decode_or (g : MaskGraph) (a b : Nat) :
    decode g (Nat.lor a b) = decode g a ∪ decode g b := by
  ext v
  simp [Bool.or_eq_true]

lemma decode_inj (g : MaskGraph) {a b : Nat} (ha : a < bit g.width) (hb : b < bit g.width)
    (same : decode g a = decode g b) : a = b := by
  apply mask_ext ha hb
  intro w hw
  have hm : (⟨w, hw⟩ : Fin g.width) ∈ decode g a ↔ (⟨w, hw⟩ : Fin g.width) ∈ decode g b := by
    rw [same]
  simp only [mem_decode] at hm
  exact Bool.eq_iff_iff.mpr hm

lemma bit_pos (n : Nat) : 0 < bit n := by
  rw [bit_eq_power]
  exact Nat.two_pow_pos n

lemma full_bounded (g : MaskGraph) : fullMask g < bit g.width := by
  unfold fullMask
  have := bit_pos g.width
  omega

section Graph

variable (g : MaskGraph) (G : SimpleGraph (Fin g.width)) [DecidableRel G.Adj]
variable (adj : ∀ u v : Fin g.width, G.Adj u v ↔ (g.adjacency u.val).testBit v.val = true)

include adj in
lemma decode_neighbors (deleted : Nat) (u : Fin g.width) :
    decode g (residualNeighbors g deleted u.val) = neighborsAfter G (decode g deleted) u := by
  ext v
  cases h : deleted.testBit v.val <;>
    simp [mem_decode, neighborsAfter, neighbor_at g deleted u.val v.val v.isLt, adj, h]

include adj in
lemma residual_zero_iff (deleted : Nat) (bound : deleted < bit g.width) (u : Fin g.width) :
    residualNeighbors g deleted u.val = 0 ↔ neighborsAfter G (decode g deleted) u = ∅ := by
  constructor
  · intro h
    rw [← decode_neighbors g G adj, h, decode_zero]
  · intro h
    apply decode_inj g (neighbor_bounded g deleted u.val bound) (bit_pos g.width)
    rw [decode_neighbors g G adj, h, decode_zero]

include adj in
lemma decode_close (deleted : Nat) (bound : deleted < bit g.width) :
    decode g (PetersenGroupBFS.closeIsolates g deleted) = BranchGraph.closeIsolates G (decode g deleted) := by
  ext v
  simp [close_at, v.isLt, BranchGraph.closeIsolates, isolates, Bool.or_eq_true,
    residual_zero_iff g G adj deleted bound]

include adj in
lemma decode_class (deleted : Nat) (bound : deleted < bit g.width) (root : Fin g.width)
    (outside : root ∉ decode g deleted) (live : (neighborsAfter G (decode g deleted) root).Nonempty) :
    decode g (twinClass g deleted root.val) = maximalClass G (decode g deleted) root := by
  have same (u : Fin g.width) : residualNeighbors g deleted u.val = residualNeighbors g deleted root.val ↔
      neighborsAfter G (decode g deleted) u = neighborsAfter G (decode g deleted) root := by
    rw [← decode_neighbors g G adj deleted u, ← decode_neighbors g G adj deleted root]
    exact ⟨congrArg (decode g), decode_inj g (neighbor_bounded g deleted u.val bound)
      (neighbor_bounded g deleted root.val bound)⟩
  ext v
  cases h : deleted.testBit v.val <;>
    simp [class_at, v.isLt, maximalClass, outside, live, h, same, Bool.beq_eq_decide_eq]

def Represented (depth : Nat) (removed : Finset (Fin g.width)) : Prop :=
  ∃ m, m ∈ frontier g depth ∧ m < bit g.width ∧ decode g m = removed

include adj in
lemma initial_rep : Represented g 0 (BranchGraph.closeIsolates G ∅) := by
  refine ⟨PetersenGroupBFS.closeIsolates g 0, ?_,
    close_bounded g 0 (bit_pos g.width), ?_⟩
  · change PetersenGroupBFS.closeIsolates g 0 ∈ [PetersenGroupBFS.closeIsolates g 0]
    exact List.mem_cons_self
  · rw [decode_close g G adj _ (bit_pos g.width), decode_zero]

include adj in
lemma advance_rep {depth : Nat} {removed : Finset (Fin g.width)} (root : Fin g.width)
    (rep : Represented g depth removed) (closed : BranchGraph.closeIsolates G removed = removed) :
    Represented g (depth + 1) (removeClass G removed root) := by
  obtain ⟨m, hm, bounded, same⟩ := rep
  subst removed
  by_cases active : root ∉ decode g m ∧ (neighborsAfter G (decode g m) root).Nonempty
  · have live : m.testBit root.val = false := by
      cases h : m.testBit root.val
      · rfl
      · exact (active.1 ((mem_decode g m root).mpr h)).elim
    have someNeighbor : residualNeighbors g m root.val ≠ 0 := by
      intro h
      have none := (residual_zero_iff g G adj m bounded root).mp h
      simpa [none] using active.2
    have united := lor_bounded bounded (class_bounded g m root.val)
    refine ⟨PetersenGroupBFS.closeIsolates g (Nat.lor m (twinClass g m root.val)),
      advance_class hm root.isLt live someNeighbor, close_bounded g _ united, ?_⟩
    rw [decode_close g G adj _ united, decode_or, decode_class g G adj m bounded root active.1 active.2,
      removeClass]
  · have sameRemoval : removeClass G (decode g m) root = decode g m := by
      have emptyClass : maximalClass G (decode g m) root = ∅ := ite_eq_right active
      simp only [removeClass, emptyClass, Finset.union_empty, closed]
    exact ⟨m, stay hm, bounded, sameRemoval.symm⟩

include adj in
lemma simulate {count depth : Nat} {start finish : Finset (Fin g.width)}
    (walk : ClassSteps G count start finish) (initial : Represented g depth start)
    (closed : BranchGraph.closeIsolates G start = start) : Represented g (depth + count) finish := by
  induction count generalizing depth start with
  | zero =>
    change finish = start at walk
    simpa only [walk, Nat.add_zero] using initial
  | succ count ih =>
    obtain ⟨root, next⟩ := walk
    have nextClosed : BranchGraph.closeIsolates G (removeClass G start root) = removeClass G start root :=
      closeIsolates_idempotent G _
    have rest := ih next (advance_rep g G adj root initial closed) nextClosed
    simpa only [Nat.add_assoc, Nat.add_comm 1 count] using rest

lemma frontier_up {m k r : Nat} (reached : m ∈ frontier g k) (budget : k ≤ r) : m ∈ frontier g r := by
  induction r with
  | zero =>
    have : k = 0 := by omega
    simpa only [this] using reached
  | succ r ih =>
    by_cases eq : k = r + 1
    · simpa [eq] using reached
    · exact stay (ih (by omega))

include adj in
theorem groups_exceed_budget [Nonempty (Fin g.width)] (k : Nat) (noFinish : fullMask g ∉ frontier g k)
    (groups : List (Finset (Fin g.width))) (twins : TwinSteps G ∅ groups)
    (finished : EdgelessAfter G (removedThrough ∅ groups)) : k < groups.length := by
  by_contra! budget
  have walk := covering_sequence_reaches_univ G groups twins finished
  obtain ⟨m, reached, bound, allGone⟩ :=
    simulate g G adj walk (initial_rep g G adj) (closeIsolates_idempotent G ∅)
  have equal : m = fullMask g := decode_inj g bound (full_bounded g) (by simpa using allGone)
  rw [equal, Nat.zero_add] at reached
  exact noFinish (frontier_up g reached budget)

end Graph

theorem petersen_nine_groups_need_five (G : SimpleGraph (Fin 9)) [DecidableRel G.Adj]
    (adj : ∀ u v : Fin 9, G.Adj u v ↔ (petersenNine.adjacency u.val).testBit v.val = true)
    (groups : List (Finset (Fin 9))) (twins : TwinSteps G ∅ groups)
    (finished : EdgelessAfter G (removedThrough ∅ groups)) : 5 ≤ groups.length :=
  @groups_exceed_budget petersenNine G (inferInstance : DecidableRel G.Adj) adj
    (inferInstance : Nonempty (Fin 9)) 4 petersen_nine_no_four groups twins finished

end PetersenMaskBridge

open PetersenNine

def petersenGraph : SimpleGraph Vertex := graph edges noLoops

def petersenAdjDecidable : DecidableRel petersenGraph.Adj := fun a b =>
  inferInstanceAs (Decidable ((a, b) ∈ edges ∨ (b, a) ∈ edges))

theorem petersen_graph_marked_edges (S : Finset Vertex) :
    edgeFun edges (fun i => decide (i ∈ S)) = true ↔
      BranchGraph.containsEdge petersenGraph S := by
  constructor
  · intro h
    obtain ⟨a, b, edge, ha, hb⟩ := (edgeFun_true edges _).mp h
    exact ⟨a, of_decide_eq_true ha, b, of_decide_eq_true hb, Or.inl edge⟩
  · rintro ⟨a, ha, b, hb, adjacent⟩
    change (a, b) ∈ edges ∨ (b, a) ∈ edges at adjacent
    apply (edgeFun_true edges _).mpr
    rcases adjacent with edge | edge
    · exact ⟨a, b, edge, decide_eq_true ha, decide_eq_true hb⟩
    · exact ⟨b, a, edge, decide_eq_true hb, decide_eq_true ha⟩

theorem petersen_graph_matches_mask :
    ∀ a b : Vertex, petersenGraph.Adj a b ↔
      (PetersenGroupBFS.petersenNine.adjacency a.val).testBit b.val = true := by
  letI : DecidableRel petersenGraph.Adj := petersenAdjDecidable
  decide

theorem petersen_graph_alternate_neighbors :
    ∀ i j : Vertex, petersenGraph.Adj i j →
      ∃ u v, petersenGraph.Adj i u ∧ petersenGraph.Adj j v ∧
        u ≠ j ∧ v ≠ i ∧ ¬ petersenGraph.Adj u v := by
  letI : DecidableRel petersenGraph.Adj := petersenAdjDecidable
  decide


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open scoped BigOperators

def operands (gs : List Gate) : List Nat := gs.flatMap Gate.inputs


def notGateCount (gs : List Gate) : Nat := (gs.filter fun g => isNotGate g.op).length

theorem operand_mem_of_read {gs : List Gate} {slot wire : Nat} (read : Reads gs slot wire) :
    wire ∈ operands gs := by
  obtain ⟨g, gAt, before⟩ := read
  exact List.mem_flatMap.mpr ⟨g, List.mem_iff_getElem?.mpr ⟨slot, gAt⟩, before⟩

theorem two_readers_operand_count {gs : List Gate} {wire p q : Nat}
    (neq : p ≠ q) (first : Reads gs p wire) (second : Reads gs q wire) :
    2 ≤ (operands gs).count wire := by
  induction gs generalizing p q with
  | nil =>
    rcases first with ⟨g, atGate, _⟩
    simp at atGate
  | cons a rest ih =>
    simp only [operands, List.flatMap_cons, List.count_append]
    cases p with
    | zero =>
      cases q with
      | zero => exact (neq rfl).elim
      | succ q =>
        have atA : wire ∈ a.inputs := by simpa [Reads] using first
        have later : Reads rest q wire := by simpa [Reads] using second
        have aPos : 0 < a.inputs.count wire := List.count_pos_iff.mpr atA
        have restPos : 0 < (operands rest).count wire := List.count_pos_iff.mpr (operand_mem_of_read later)
        simp only [operands] at restPos
        omega
    | succ p =>
      cases q with
      | zero =>
        have atA : wire ∈ a.inputs := by simpa [Reads] using second
        have later : Reads rest p wire := by simpa [Reads] using first
        have aPos : 0 < a.inputs.count wire := List.count_pos_iff.mpr atA
        have restPos : 0 < (operands rest).count wire := List.count_pos_iff.mpr (operand_mem_of_read later)
        simp only [operands] at restPos
        omega
      | succ q =>
        have early : Reads rest p wire := by simpa [Reads] using first
        have late : Reads rest q wire := by simpa [Reads] using second
        have different : p ≠ q := fun eq => neq (congrArg Nat.succ eq)
        have count := ih different early late
        simp only [operands] at count
        omega

theorem operands_count_length (gs : List Gate)
    (arity : ∀ g ∈ gs, g.inputs.length + (if isNotGate g.op then 1 else 0) = 2) :
    (operands gs).length + notGateCount gs = 2 * gs.length := by
  induction gs with
  | nil => simp [operands, notGateCount]
  | cons g gs ih =>
    have gArity := arity g (by simp)
    have rest := ih (fun q hq => arity q (List.mem_cons_of_mem _ hq))
    cases h : isNotGate g.op
    · simp [h] at gArity
      simp [operands, notGateCount, h] at rest ⊢
      omega
    · simp [h] at gArity
      simp [operands, notGateCount, h] at rest ⊢
      omega

theorem clean_gate_arity {n : Nat} {gs : List Gate} (h : CleanL n gs) :
    ∀ g ∈ gs, g.inputs.length + (if isNotGate g.op then 1 else 0) = 2 := by
  intro g gMem
  obtain ⟨p, atGate⟩ := List.mem_iff_getElem?.mp gMem
  rcases h p g atGate with ⟨op, a, _, args⟩ | ⟨ops, a, b, _, _, args⟩
  · simp [op, args, isNotGate]
  · rcases ops with op | op <;> simp [op, args, isNotGate]

theorem branch_card_add_wire_card_le_operands (gs : List Gate) (branches : Finset Nat)
    (twice : ∀ w ∈ branches, 2 ≤ (operands gs).count w) :
    branches.card + (operands gs).toFinset.card ≤ (operands gs).length := by
  classical
  let W := (operands gs).toFinset
  have subset : branches ⊆ W := by
    intro w wm
    have t := twice w wm
    exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by omega))
  have aux : (∑ w ∈ W, if w ∈ branches then (1 : Nat) else 0) = branches.card := by
    have same : (∑ w ∈ W, if w ∈ branches then (1 : Nat) else 0) =
        ∑ w ∈ branches, if w ∈ branches then (1 : Nat) else 0 := by
      symm
      apply Finset.sum_subset subset
      intro w _ notBranch
      simp [notBranch]
    rw [same]
    simp
  have total : (∑ w ∈ W, (operands gs).count w) = (operands gs).length :=
    List.sum_toFinset_count_eq_length _
  have bound : (∑ w ∈ W, ((if w ∈ branches then (1 : Nat) else 0) + 1)) ≤
      ∑ w ∈ W, (operands gs).count w := by
    apply Finset.sum_le_sum
    intro w wIn
    by_cases b : w ∈ branches
    · simpa [b] using twice w b
    · have pos : 0 < (operands gs).count w := List.count_pos_iff.mpr (List.mem_toFinset.mp wIn)
      simpa [b] using pos
  rw [Finset.sum_add_distrib, aux, total] at bound
  simpa [W] using bound

theorem branching_budget {n out : Nat} {gs : List Gate} (clean : CleanL n gs)
    (outValid : out < n + gs.length)
    (everyNonoutputUsed : ∀ w < n + gs.length, w ≠ out → ∃ p, Reads gs p w)
    (branches : Finset Nat)
    (twoReaders : ∀ w ∈ branches, ∃ p q, p ≠ q ∧ Reads gs p w ∧ Reads gs q w) :
    branches.card + (n + gs.length - 1) + notGateCount gs ≤ 2 * gs.length := by
  let W := (operands gs).toFinset
  let required := (Finset.range (n + gs.length)).erase out
  have requiredUsed : required ⊆ W := by
    intro w inSet
    have spec := Finset.mem_erase.mp inSet
    obtain ⟨p, read⟩ := everyNonoutputUsed w (Finset.mem_range.mp spec.2) spec.1
    exact List.mem_toFinset.mpr (operand_mem_of_read read)
  have numRequired : required.card = n + gs.length - 1 := by
    change ((Finset.range (n + gs.length)).erase out).card = _
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr outValid), Finset.card_range]
  have twice : ∀ w ∈ branches, 2 ≤ (operands gs).count w := by
    intro w mem
    obtain ⟨p, q, different, pReads, qReads⟩ := twoReaders w mem
    exact two_readers_operand_count different pReads qReads
  have up := branch_card_add_wire_card_le_operands gs branches twice
  have used := Finset.card_le_card requiredUsed
  rw [numRequired] at used
  have total := operands_count_length gs (clean_gate_arity clean)
  change n + gs.length - 1 ≤ (operands gs).toFinset.card at used
  omega


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open PetersenCutTrace

theorem least_read_edge_live {n out : Nat} {gs : List Gate}
    {f : (Fin n → Bool) → Bool} (least : Least n f gs out) (nonnull : ∃ x y, f x ≠ f y)
    (dependent : ∀ v : Fin n, Dep f v)
    (stillNonconstant : ∀ (v : Fin n) (b : Bool), ∃ x y,
      f (Function.update x v b) ≠ f (Function.update y v b))
    (outValid : out < n + gs.length) :
    ∀ w : Fin (n + gs.length), w ≠ (⟨out, outValid⟩ : Fin (n + gs.length)) → ∃ v, readEdge gs w v := by
  intro w notOutput
  have notSame : w.val ≠ out := fun eq => notOutput (Fin.ext eq)
  obtain ⟨p, g, atSlot, reads, bound⟩ :=
    least_wire_readers_in_range least nonnull dependent stillNonconstant w notSame
  exact ⟨⟨n + p, bound⟩, p, g, atSlot, rfl, reads⟩

theorem branch_slots_of_read_edges {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)}
    (fork : FirstBranchRoute.Branches (readEdge gs) w) :
    ∃ p q, p ≠ q ∧ Reads gs p w.val ∧ Reads gs q w.val := by
  obtain ⟨first, next, pRead, qRead, separate⟩ := fork
  obtain ⟨p, g, atP, src, ap⟩ := pRead
  obtain ⟨q, h, atQ, dst, aq⟩ := qRead
  refine ⟨p, q, ?_, ⟨g, atP, ap⟩, ⟨h, atQ, aq⟩⟩
  intro same
  subst q
  exact separate (Fin.ext (src.trans dst.symm))

noncomputable def circuitBranchWires {n : Nat} (gs : List Gate) : Finset (Fin (n + gs.length)) := by
  classical
  exact (Finset.univ).filter fun w => FirstBranchRoute.Branches (readEdge gs) w

theorem in_circuit_branches {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)} :
    w ∈ circuitBranchWires gs ↔ FirstBranchRoute.Branches (readEdge gs) w := by
  classical
  simp [circuitBranchWires]


def classAt {V W : Type} [Fintype V] (label : V → W) [DecidableEq W] (cut : W) : Finset V :=
  Finset.univ.filter fun v => label v = cut

def classesBefore {V W : Type} [Fintype V] (label : V → W) [LinearOrder W] (cut : W) : Finset V :=
  Finset.univ.filter fun v => label v < cut

theorem class_mem {V W : Type} [Fintype V] (label : V → W) [DecidableEq W] (cut : W) (v : V) :
    v ∈ classAt label cut ↔ label v = cut := by
  simp [classAt]

theorem classes_before_mem {V W : Type} [Fintype V] (label : V → W) [LinearOrder W] (cut : W) (v : V) :
    v ∈ classesBefore label cut ↔ label v < cut := by
  simp [classesBefore]

theorem class_twins_of_later_factor {V W : Type} [Fintype V] [DecidableEq V] [LinearOrder W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (label : V → W) (cut : W)
    (independent : BranchGraph.Independent G (classAt label cut))
    (code : Finset V → Bool) (decode : Bool → Finset V → Prop)
    (factors : ∀ I O : Finset V, (∀ i ∈ I, label i = cut) →
      (∀ i ∈ O, cut < label i) → (BranchGraph.containsEdge G (I ∪ O) ↔ decode (code I) O)) :
    BranchGraph.TwinGroup G (classesBefore label cut) (classAt label cut) := by
  intro u uGroup v vGroup uActive vActive
  have later {x y : V} (xGroup : x ∈ classAt label cut) (edge : G.Adj x y)
      (notEarlier : y ∉ classesBefore label cut) : cut < label y := by
    have ne : label y ≠ cut := fun equal =>
      independent x xGroup y ((class_mem label cut y).mpr equal) edge
    have notBefore : ¬ label y < cut := fun h => notEarlier ((classes_before_mem label cut y).mpr h)
    exact lt_of_le_of_ne (le_of_not_gt notBefore) (Ne.symm ne)
  have single (x y : V) (xGroup : x ∈ classAt label cut) (yLater : cut < label y) :
      (G.Adj x y ↔ decode (code {x}) {y}) := by
    have g (i : V) (mem : i ∈ ({x} : Finset V)) : label i = cut := by
      have eq : i = x := Finset.mem_singleton.mp mem
      subst i
      exact (class_mem label cut x).mp xGroup
    have h (i : V) (mem : i ∈ ({y} : Finset V)) : cut < label i := by
      have eq : i = y := Finset.mem_singleton.mp mem
      rwa [eq]
    simpa [BranchGraph.pair_contains_edge] using factors {x} {y} g h
  have cannot (x : V) (xGroup : x ∈ classAt label cut)
      (active : (BranchGraph.neighborsAfter G (classesBefore label cut) x).Nonempty) :
      code {x} ≠ code ∅ := by
    obtain ⟨y, neighbor⟩ := active
    simp only [BranchGraph.neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and] at neighbor
    have yLater := later xGroup neighbor.1 neighbor.2
    have yes := (single x y xGroup yLater).mp neighbor.1
    intro collapse
    rw [collapse] at yes
    have one := (factors ∅ {y} (by simp) (by simpa using yLater)).mpr yes
    exact BranchGraph.singleton_no_edge G y (by simpa using one)
  have a := cannot u uGroup uActive
  have b := cannot v vGroup vActive
  have sameCode : code {u} = code {v} := by
    cases hc : code ∅ <;> cases ha : code {u} <;> cases hb : code {v} <;> simp_all
  ext z
  simp only [BranchGraph.neighborsAfter, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨edge, remains⟩
    have pos := later uGroup edge remains
    refine ⟨(single v z vGroup pos).mpr ?_, remains⟩
    rw [← sameCode]
    exact (single u z uGroup pos).mp edge
  · rintro ⟨edge, remains⟩
    have pos := later vGroup edge remains
    refine ⟨(single u z uGroup pos).mpr ?_, remains⟩
    rw [sameCode]
    exact (single v z vGroup pos).mp edge

namespace PetersenCutTrace

open PEqualNP.CircuitLowerBounds CircuitProof
open Relation

theorem agree_on_input_ancestors {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (x y : Fin n → Bool) (w : Fin (n + gs.length))
    (agrees : ∀ i, ReflTransGen (readEdge gs) (inputWire gs i) w → x i = y i) :
    vl gs x w.val = vl gs y w.val := by
  revert agrees
  induction w using (measure (fun a : Fin (n + gs.length) => a.val)).wf.induction with
  | h w earlier =>
    intro agree
    by_cases input : w.val < n
    · let i : Fin n := ⟨w.val, input⟩
      have name : inputWire gs i = w := Fin.ext rfl
      have atInput : ReflTransGen (readEdge gs) (inputWire gs i) w := by
        simpa only [name] using (ReflTransGen.refl : ReflTransGen (readEdge gs) w w)
      have a := agree i atInput
      simpa only [vl_input gs x w.val input, vl_input gs y w.val input] using a
    · let p := w.val - n
      have pLt : p < gs.length := by have := w.isLt; dsimp [p]; omega
      have gateWire : w.val = n + p := by dsimp [p]; omega
      let g := gs[p]'pLt
      have atGate : gs[p]? = some g := List.getElem?_eq_getElem pLt
      rw [gateWire]
      apply vl_congr gs clean x y p g atGate
      intro a inGate
      have readBefore := (clean p g atGate).lt a inGate
      let wire : Fin (n + gs.length) := ⟨a, by have := w.isLt; omega⟩
      have read : readEdge gs wire w := ⟨p, g, atGate, gateWire, inGate⟩
      apply earlier wire (show wire.val < w.val by change a < w.val; omega)
      intro i path
      exact agree i (path.tail read)

end PetersenCutTrace

open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutTrace Relation

def setInput {n : Nat} (S : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ S)

theorem finite_branch_bit_factor {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ v : Fin (n + gs.length), v ≠ out → ∃ w, readEdge gs v w)
    (cut : Fin (n + gs.length)) (prior : cut ≤ out)
    (terminal : FirstBranchRoute.Terminal (readEdge gs) out cut) :
    let label (i : Fin n) :=
      FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
    ∃ code : Finset (Fin n) → Bool, ∃ decode : Bool → Finset (Fin n) → Prop,
      ∀ I O : Finset (Fin n),
        (∀ i ∈ I, label i = cut) → (∀ i ∈ O, cut < label i) →
        (vl gs (setInput (I ∪ O)) out.val = true ↔ decode (code I) O) := by
  classical
  let label (i : Fin n) :=
    FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
  let code (I : Finset (Fin n)) := vl gs (setInput I) cut.val
  let decode (b : Bool) (O : Finset (Fin n)) :=
    ∃ J : Finset (Fin n), (∀ j ∈ J, label j = cut) ∧ code J = b ∧
      vl gs (setInput (J ∪ O)) out.val = true
  refine ⟨code, decode, ?_⟩
  intro I O groupI afterO
  change (∀ i ∈ I, label i = cut) at groupI
  change (∀ i ∈ O, cut < label i) at afterO
  change (_ ↔ decode (code I) O)
  constructor
  · exact fun yes => ⟨I, groupI, rfl, yes⟩
  · rintro ⟨J, groupJ, sameCode, yes⟩
    have stable (K : Finset (Fin n)) : vl gs (setInput (K ∪ O)) cut.val = code K := by
      apply agree_on_input_ancestors clean
      intro i ancestral
      have limit : label i ≤ cut :=
        FirstBranchRoute.ancestor_first_le (readEdge gs) out (read_order clean) live ancestral terminal
      have absent : i ∉ O := fun mem => (not_lt_of_ge limit) (afterO i mem)
      simp [setInput, absent]
    have sameCut : vl gs (setInput (I ∪ O)) cut.val = vl gs (setInput (J ∪ O)) cut.val :=
      (stable I).trans (sameCode.symm.trans (stable J).symm)
    by_cases atOutput : cut = out
    · rw [atOutput] at sameCut
      exact sameCut.trans yes
    have before : cut < out := lt_of_le_of_ne prior atOutput
    have eq := circuit_cut_agreement clean cut out _ _ sameCut (by
      intro i diff
      have isGroup : label i = cut := by
        by_contra offGroup
        have notI : i ∉ I := fun mem => offGroup (groupI i mem)
        have notJ : i ∉ J := fun mem => offGroup (groupJ i mem)
        exact diff (by simp [setInput, notI, notJ])
      intro bypass
      have groupLabel : FirstBranchRoute.first (readEdge gs) out (read_order clean) live
          (inputWire gs i) = cut := isGroup
      have forbid := FirstBranchRoute.no_avoiding_after (readEdge gs) out (read_order clean) live
        (v := inputWire gs i) (w := out) (by simpa [groupLabel] using before)
      apply forbid
      have weaker : ∀ a b, avoid (readEdge gs) cut a b → FirstBranchRoute.Avoid (readEdge gs) cut a b :=
        fun _ _ h => ⟨h.1, h.2.1⟩
      have convert : ReflTransGen (FirstBranchRoute.Avoid (readEdge gs) cut) (inputWire gs i) out :=
        ReflTransGen.mono weaker _ _ bypass
      simpa only [groupLabel] using convert)
    rwa [eq]

open PEqualNP.CircuitLowerBounds CircuitProof
open PetersenCutTrace

theorem circuit_branch_class_twins {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ v : Fin (n + gs.length), v ≠ out → ∃ w, readEdge gs v w)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (computes : ∀ S : Finset (Fin n), vl gs (setInput S) out.val = true ↔ BranchGraph.containsEdge G S)
    (cut : Fin (n + gs.length)) (prior : cut ≤ out)
    (terminal : FirstBranchRoute.Terminal (readEdge gs) out cut)
    (independent : BranchGraph.Independent G
      (classAt (fun i => FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)) cut)) :
    let label (i : Fin n) := FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
    BranchGraph.TwinGroup G (classesBefore label cut) (classAt label cut) := by
  let label (i : Fin n) := FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)
  obtain ⟨code, decode, factors⟩ := finite_branch_bit_factor clean out live cut prior terminal
  change BranchGraph.TwinGroup G (classesBefore label cut) (classAt label cut)
  exact class_twins_of_later_factor G label cut independent code decode (by
    intro I O group after
    rw [← computes (I ∪ O)]
    exact factors I O group after)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open PetersenCutTrace PetersenFirstGroup

abbrev petersenF := edgeFun edges

private theorem petersen_dependency_samples : ∀ v : Vertex, ∃ w : Vertex,
    petersenF (Function.update (fun i => decide (i = w)) v
      (!(decide (v = w)))) ≠ petersenF (fun i => decide (i = w)) := by
  decide +kernel

theorem petersen_depends (v : Vertex) : Dep petersenF v := by
  obtain ⟨w, hw⟩ := petersen_dependency_samples v
  exact ⟨fun i => decide (i = w), hw⟩

theorem petersen_nonconstant : ∃ x y : Vertex → Bool, petersenF x ≠ petersenF y :=
  dep_nc (petersen_depends 0)

private theorem petersen_cofactor_samples : ∀ (v : Vertex) (b : Bool),
    petersenF (Function.update (fun _ => false) v b) = false ∧
    petersenF (Function.update (fun _ => true) v b) = true := by
  decide +kernel

theorem petersen_restrict_nonconstant (v : Vertex) (b : Bool) :
    ∃ x y, petersenF (Function.update x v b) ≠ petersenF (Function.update y v b) := by
  obtain ⟨no, yes⟩ := petersen_cofactor_samples v b
  exact ⟨fun _ => false, fun _ => true, by rw [no, yes]; decide⟩


lemma petersenF_graph_edges (x : Fin 9 → Bool) : petersenF x = true ↔
    ∃ u v : Fin 9, petersenGraph.Adj u v ∧ x u = true ∧ x v = true := by
  change PetersenNine.edgeFun PetersenNine.edges x = true ↔ _
  rw [PetersenNine.edgeFun_true]
  constructor
  · rintro ⟨a, b, edge, ha, hb⟩
    exact ⟨a, b, Or.inl edge, ha, hb⟩
  · rintro ⟨a, b, adjacent, ha, hb⟩
    change (a, b) ∈ PetersenNine.edges ∨ (b, a) ∈ PetersenNine.edges at adjacent
    rcases adjacent with edge | edge
    · exact ⟨a, b, edge, ha, hb⟩
    · exact ⟨b, a, edge, hb, ha⟩

lemma least_petersen_output_valid {gs : List Gate} {out : Nat} (least : Least 9 petersenF gs out) :
    out < 9 + gs.length := by
  by_contra! after
  obtain ⟨x, y, different⟩ := least.ncv petersen_nonconstant
  exact different ((vl_beyond gs x out after).trans (vl_beyond gs y out after).symm)

theorem least_petersen_five_branches (gs : List Gate) (out : Nat) (least : Least 9 petersenF gs out)
    : 5 ≤ (circuitBranchWires (n := 9) gs).card := by
  classical
  letI : DecidableRel petersenGraph.Adj := petersenAdjDecidable
  have outValid := least_petersen_output_valid least
  let outWire : Fin (9 + gs.length) := ⟨out, outValid⟩
  have live := least_read_edge_live least petersen_nonconstant petersen_depends petersen_restrict_nonconstant outValid
  let label : Fin 9 → Fin (9 + gs.length) := firstInputBoundary least.hcl outWire live
  let branches : Finset (Fin (9 + gs.length)) := circuitBranchWires gs
  have computes (x : Fin 9 → Bool) : vl gs x outWire.val = PetersenScratch.edgeValue petersenGraph x := by
    change vl gs x out = _
    rw [least.hev, Bool.eq_iff_iff, petersenF_graph_edges]
    simp only [PetersenScratch.edgeValue, decide_eq_true_eq]
  have marked (S : Finset (Fin 9)) : vl gs (setInput S) outWire.val = true ↔
      BranchGraph.containsEdge petersenGraph S := by
    change vl gs (setInput S) out = true ↔ _
    rw [least.hev]
    exact petersen_graph_marked_edges S
  have independent (r) : BranchGraph.Independent petersenGraph (BranchGroupsLean.bucket label r) :=
    firstInputGroup_independent least.hcl outWire live (predecessors_nodup least petersen_nonconstant)
      petersenGraph computes petersen_graph_alternate_neighbors r
  have labels (v : Fin 9) : label v = outWire ∨ label v ∈ branches := by
    have stopped := FirstBranchRoute.first_stops (readEdge gs) outWire (read_order least.hcl) live (inputWire gs v)
    rcases stopped with outLabel | fork
    · exact Or.inl outLabel
    · exact Or.inr (in_circuit_branches.mpr fork)
  have before (r) (member : r ∈ branches) : r < outWire := by
    obtain ⟨a, _, path, _, _⟩ := in_circuit_branches.mp member
    exact lt_of_lt_of_le (read_order least.hcl path) (wire_le_output least.hcl outWire live a)
  have twins (r) (member : r ∈ branches) : BranchGraph.TwinGroup petersenGraph
      (BranchGroupsLean.below label r) (BranchGroupsLean.bucket label r) :=
    circuit_branch_class_twins least.hcl outWire live petersenGraph marked r
      (le_of_lt (before r member)) (Or.inr (in_circuit_branches.mp member)) (independent r)
  exact BranchGroupsLean.roots_required petersenGraph label outWire branches 5 labels before twins
    (independent outWire) (PetersenMaskBridge.petersen_nine_groups_need_five petersenGraph petersen_graph_matches_mask)

lemma nonNotCount_add_notCount (gs : List Gate) :
    nonNotCount gs + (gs.filter (fun g => isNotGate g.op)).length = gs.length := by
  rw [← List.countP_eq_length_filter]
  induction gs with
  | nil => simp [nonNotCount]
  | cons g gs ih =>
    simp only [nonNotCount, List.countP_cons, List.length_cons] at ih ⊢
    cases h : isNotGate g.op <;> simp [h] <;> omega

lemma nonNotCount_replace_not (gs : List Gate) (p : ℕ) (hp : p < gs.length)
    (hn : gs[p].op = .not) :
    nonNotCount (gs.set p ⟨.and, []⟩) = nonNotCount gs + 1 := by
  simp [nonNotCount, List.countP_set hp, hn, isNotGate]

lemma nonNotCount_three_not (gs : List Gate) (i j k : Fin gs.length)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : (gs.get i).op = .not) (hj : (gs.get j).op = .not)
    (hk : (gs.get k).op = .not) : nonNotCount gs + 3 ≤ gs.length := by
  let g : Gate := ⟨.and, []⟩
  let gs' := gs.set i.val g
  let gs'' := gs'.set j.val g
  let gs''' := gs''.set k.val g
  have hj' : j.val < gs'.length := by simpa [gs'] using j.isLt
  have hk' : k.val < gs'.length := by simpa [gs'] using k.isLt
  have hk'' : k.val < gs''.length := by simpa [gs''] using hk'
  have cmp_i := nonNotCount_replace_not gs i.val i.isLt hi
  have cmp_j := nonNotCount_replace_not gs' j.val hj' (by
    rw [show gs'[j.val] = gs[j.val] from List.getElem_set_ne (fun h => hij (Fin.ext h)) hj']
    exact hj)
  have cmp_k := nonNotCount_replace_not gs'' k.val hk'' (by
    rw [show gs''[k.val] = gs'[k.val] from List.getElem_set_ne (fun h => hjk (Fin.ext h)) hk'',
        show gs'[k.val] = gs[k.val] from List.getElem_set_ne (fun h => hik (Fin.ext h)) hk']
    exact hk)
  change nonNotCount gs' = nonNotCount gs + 1 at cmp_i
  change nonNotCount gs'' = nonNotCount gs' + 1 at cmp_j
  change nonNotCount gs''' = nonNotCount gs'' + 1 at cmp_k
  have hbound : nonNotCount gs''' ≤ gs.length := by
    simpa [nonNotCount, gs''', gs'', gs', g] using
      (List.countP_le_length (p := fun q : Gate => !(isNotGate q.op)) (l := gs'''))
  omega

theorem petersen_binary_lower (C : Circuit) (hfan : FanInTwo C)
    (he : ∀ x : Vertex → Bool, C.eval (List.ofFn x) = petersenF x) :
    13 ≤ nonNotCount C.gates := by
  obtain ⟨gs, o, least, budget⟩ := least_with_budget C hfan he petersen_nonconstant
  have valid := least_petersen_output_valid least
  have live := least_read_edge_live least petersen_nonconstant petersen_depends
    petersen_restrict_nonconstant valid
  let branches := circuitBranchWires (n := 9) gs
  have branchLower : 5 ≤ branches.card := least_petersen_five_branches gs o least
  have branchBudget := branching_budget least.hcl valid (fun w hw hne => by
      let wire : Fin (9 + gs.length) := ⟨w, hw⟩
      obtain ⟨v, p, g, hg, _, hw'⟩ := live wire (fun h => hne (congrArg Fin.val h))
      exact ⟨p, g, hg, hw'⟩)
    (branches.image Fin.val) (fun w hw => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
      exact branch_slots_of_read_edges (in_circuit_branches.mp hv))
  rw [Finset.card_image_of_injective _ Fin.val_injective] at branchBudget
  have countTotal := nonNotCount_add_notCount gs
  change nonNotCount gs + notGateCount gs = gs.length at countTotal
  omega




open PEqualNP.CircuitLowerBounds CircuitProof CircuitProof.Readers
open PetersenCutTrace PetersenFirstGroup

theorem threeForksOfBudget {gs : List Gate} (clean : CleanL 10 gs)
    (out : Fin (10 + gs.length))
    (live : ∀ w : Fin (10 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (budget : nonNotCount gs ≤ 12) : (circuitBranchWires (n := 10) gs).card ≤ 3 := by
  classical
  let branches := circuitBranchWires (n := 10) gs
  have h := branching_budget clean out.isLt (fun w hw hne => by
      let wire : Fin (10 + gs.length) := ⟨w, hw⟩
      obtain ⟨v,p,g,hg,_,hw'⟩ := live wire (fun e => hne (congrArg Fin.val e))
      exact ⟨p,g,hg,hw'⟩)
    (branches.image Fin.val) (fun w hw => by
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      exact branch_slots_of_read_edges (in_circuit_branches.mp hv))
  rw [Finset.card_image_of_injective _ Fin.val_injective] at h
  have count := nonNotCount_add_notCount gs
  change nonNotCount gs + notGateCount gs = gs.length at count
  change branches.card ≤ 3
  omega

abbrev Orient (s a b : Bool) : Prop := if s then a = true → b = true else b = true → a = true

def Unate {n : Nat} (F : (Fin n → Bool) → Bool) (i : Fin n) : Prop :=
  ∃ s, ∀ x y, (∀ j, j ≠ i → x j = y j) → x i = false → y i = true → Orient s (F x) (F y)

lemma oriKeep : ∀ s a b c d : Bool, Orient s a b → Orient s c d →
    Orient s (a && c) (b && d) ∧ Orient s (a || c) (b || d) := by decide

lemma oriRefl (s a : Bool) : Orient s a a := by cases s <;> simp [Orient]

lemma formulaUnate {n : Nat} (i : Fin n) (p : DMFormula n) :
    PetersenScratch.occurrences i p ≤ 1 → Unate p.eval i := by
  induction p with
  | lit k s =>
    intro _
    by_cases hk : k = i
    · subst k
      refine ⟨s, fun x y _ hx hy => ?_⟩
      cases s <;> simp [DMFormula.eval, Orient, hx, hy]
    · refine ⟨true, fun x y h _ _ => ?_⟩
      rw [show (DMFormula.lit k s).eval x = (DMFormula.lit k s).eval y by simp [DMFormula.eval,h k hk]]
      exact oriRefl _ _
  | and p q ihp ihq | or p q ihp ihq =>
    intro h
    change PetersenScratch.occurrences i p + PetersenScratch.occurrences i q ≤ 1 at h
    have absent (r : DMFormula n) (hr : PetersenScratch.occurrences i r = 0)
        (x y : Fin n → Bool) (hxy : ∀ j, j ≠ i → x j = y j) : r.eval x = r.eval y := by
      apply PetersenScratch.eval_agree
      intro j hj
      exact hxy j (by rintro rfl; omega)
    by_cases hp : PetersenScratch.occurrences i p = 0
    · obtain ⟨s,hs⟩ := ihq (by omega)
      refine ⟨s, fun x y hxy hx hy => ?_⟩
      have h₁ : Orient s (p.eval x) (p.eval y) := by rw [absent p hp x y hxy]; exact oriRefl _ _
      first | exact (oriKeep s _ _ _ _ h₁ (hs x y hxy hx hy)).1 | exact (oriKeep s _ _ _ _ h₁ (hs x y hxy hx hy)).2
    · obtain ⟨s,hs⟩ := ihp (by omega)
      refine ⟨s, fun x y hxy hx hy => ?_⟩
      have h₂ : Orient s (q.eval x) (q.eval y) := by rw [absent q (by omega) x y hxy]; exact oriRefl _ _
      first | exact (oriKeep s _ _ _ _ (hs x y hxy hx hy) h₂).1 | exact (oriKeep s _ _ _ _ (hs x y hxy hx hy) h₂).2

theorem normalizedCuts {n : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (hcard : (circuitBranchWires (n := n) gs).card ≤ 3) :
    ∃ label : Fin n → Fin 4,
      (∀ i j, label i = label j ↔ firstInputBoundary clean out live i = firstInputBoundary clean out live j) ∧
      (∀ i, label i = 3 → firstInputBoundary clean out live i = out) ∧
      (∀ k : Fin 4, ∃ code : (Fin n → Bool) → Bool,
        (∀ i, label i = k → Unate code i) ∧
        (∀ x y, (∀ i, label i ≤ k → x i = y i) → code x = code y) ∧
        (∀ x y, (∀ i, label i ≠ k → x i = y i) → code x = code y → vl gs x out.val = vl gs y out.val)) := by
  classical
  let branches := circuitBranchWires (n := n) gs
  change branches.card ≤ 3 at hcard
  let cuts := insert out branches
  have small : cuts.card ≤ 4 := (Finset.card_insert_le ..).trans (by omega)
  let boundary := firstInputBoundary clean out live
  have mem (i : Fin n) : boundary i ∈ cuts := by
    rcases FirstBranchRoute.first_stops (readEdge gs) out (read_order clean) live (inputWire gs i)
      with ho | hb
    · exact Finset.mem_insert.mpr (Or.inl ho)
    · exact Finset.mem_insert.mpr (Or.inr (in_circuit_branches.mpr hb))
  let embed := (cuts.orderIsoOfFin rfl).symm
  let rank (c : cuts) : Fin 4 :=
    ⟨4 - cuts.card + (embed c).val, by have := (embed c).isLt; omega⟩
  have strict : StrictMono rank := by
    intro c d hcd
    have he := embed.strictMono hcd
    change (embed c).val < (embed d).val at he
    change 4 - cuts.card + (embed c).val < 4 - cuts.card + (embed d).val
    omega
  let loc (i : Fin n) : cuts := ⟨boundary i, mem i⟩
  let label (i : Fin n) := rank (loc i)
  have eqv (i j : Fin n) : label i = label j ↔ boundary i = boundary j := by
    change rank (loc i) = rank (loc j) ↔ (loc i).val = (loc j).val
    rw [strict.injective.eq_iff, Subtype.ext_iff]
  have last (i : Fin n) (h : label i = 3) : boundary i = out := by
    by_contra ne
    let top : cuts := ⟨out, Finset.mem_insert_self ..⟩
    have ht : loc i < top := lt_of_le_of_ne (wire_le_output clean out live _) (fun e => ne (congrArg Subtype.val e))
    have bad := strict ht
    change label i < rank top at bad
    rw [h] at bad
    omega
  refine ⟨label, eqv, last, ?_⟩
  intro k
  by_cases used : ∃ z, label z = k
  · obtain ⟨z, rfl⟩ := used
    let c := boundary z
    have term : FirstBranchRoute.Terminal (readEdge gs) out c :=
      FirstBranchRoute.first_stops (readEdge gs) out (read_order clean) live (inputWire gs z)
    refine ⟨fun x => vl gs x c.val, ?_, ?_, ?_⟩
    · intro i hi
      have e : boundary i = c := (eqv i z).mp hi
      have h := firstInputBoundary_occurrences_le_one clean out live distinct i i
      change PetersenScratch.occurrences i (PetersenCutFormula.wireFormula i gs (boundary i).val) ≤ 1 at h
      rw [e] at h
      have hu := formulaUnate i _ h
      have ev : (PetersenCutFormula.wireFormula i gs c.val).eval = fun x => vl gs x c.val := funext (fun x => PetersenCutFormula.wireFormula_eval i clean x c.val c.isLt)
      rwa [ev] at hu
    · intro x y hxy
      apply agree_on_input_ancestors clean
      intro i path
      apply hxy i
      exact strict.monotone (show loc i ≤ loc z from
        FirstBranchRoute.ancestor_first_le (readEdge gs) out (read_order clean) live path term)
    · intro x y hxy heq
      have blocked := firstInputGroup_controlled clean out live c
      rcases blocked with atOut | apart
      · simpa only [atOut] using heq
      · apply circuit_cut_agreement clean c out x y heq
        intro i hi
        apply apart i
        apply (mem_firstInputGroup clean out live c i).mpr
        exact (eqv i z).mp (by_contra fun ne => hi (hxy i ne))
  · refine ⟨fun _ => false, fun i hi => (used ⟨i,hi⟩).elim, fun _ _ _ => rfl, ?_⟩
    intro x y hxy _
    have : x = y := funext (fun i => hxy i (fun h => used ⟨i,h⟩))
    rw [this]


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Suffix2770

def F (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)

def plug (x : Fin 9 → Bool) (b : Bool) : Fin 10 → Bool := Fin.lastCases b x

lemma plug_list (x : Fin 9 → Bool) (b : Bool) :
    List.ofFn (plug x b) = List.ofFn x ++ [b] := by
  rw [List.ofFn_succ_last]
  simp [plug]
  rfl

end Suffix2770

namespace Finite2770

def target (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

abbrev valid (x : Fin 10 → Bool) : Prop := x 9 = (x 0 || x 2)

def conflicts : List (Fin 10 × Fin 10) :=
  [(0,5),(1,6),(2,3),(3,4),(3,8),(5,7),(5,8),(6,8)]

def row (m : ℕ) (i : Fin 10) : Bool := m.testBit i.val

def cube (i j k : Fin 10) (a b c : ℕ) : Prop :=
  let hi m := Function.update (row m) k true
  (∀ v, v ≠ i → v ≠ j → row a v = row b v ∧ row b v = row c v) ∧
  valid (row a) ∧ valid (row b) ∧ valid (hi a) ∧ valid (hi b) ∧ valid (hi c) ∧
  target (row a) ≠ target (row b) ∧ target (hi a) ≠ target (hi c) ∧ target (hi b) ≠ target (hi c)

def Cut (label : Fin 10 → Fin 4) (t : Fin 4) : Prop :=
  ∃ code : (Fin 10 → Bool) → Bool,
    (∀ x y, (∀ i, label i ≤ t → x i = y i) → code x = code y) ∧
    (∀ x y, valid x → valid y → (∀ i, label i ≠ t → x i = y i) →
      code x = code y → target x = target y)

lemma cubeBound (label : Fin 10 → Fin 4) (cut : ∀ t, t < 3 → Cut label t)
    (i j k : Fin 10) (a b c : ℕ) (hw : cube i j k a b c) :
    label i = label j → label k ≤ label i := by
  intro hh
  by_contra hle
  have hlt : label i < label k := lt_of_not_ge hle
  have h3 : label i < 3 := by omega
  obtain ⟨code, low, high⟩ := cut (label i) h3
  obtain ⟨same, va, vb, vha, vhb, vhc, nab, nac, nbc⟩ := hw
  let hi (m : ℕ) := Function.update (row m) k true
  have aux (m : ℕ) : code (hi m) = code (row m) := by
    apply low
    intro u hu
    have hne : u ≠ k := by
      rintro rfl
      exact (not_le_of_gt hlt) hu
    exact Function.update_of_ne hne _ _
  have off {u} (h : label u ≠ label i) : u ≠ i ∧ u ≠ j := by
    constructor
    · exact fun he => h (he ▸ rfl)
    · exact fun he => h (he ▸ hh.symm)
  have hab : code (row a) ≠ code (row b) := fun e =>
    nab (high _ _ va vb (fun u hu => (same u (off hu).1 (off hu).2).1) e)
  have lift {m n : ℕ} (h : ∀ u, label u ≠ label i → row m u = row n u) :
      ∀ u, label u ≠ label i → hi m u = hi n u := by
    intro u hu
    by_cases eq : u = k
    · subst u; simp [hi]
    · simpa [hi, Function.update_of_ne eq] using h u hu
  have hac : code (row a) ≠ code (row c) := fun e =>
    nac (high _ _ vha vhc (lift (fun u hu => ((same u (off hu).1 (off hu).2).1).trans
      (same u (off hu).1 (off hu).2).2)) ((aux a).trans (e.trans (aux c).symm)))
  have hbc : code (row b) ≠ code (row c) := fun e =>
    nbc (high _ _ vhb vhc (lift (fun u hu => (same u (off hu).1 (off hu).2).2))
      ((aux b).trans (e.trans (aux c).symm)))
  cases ha : code (row a) <;> cases hb : code (row b) <;> cases hc : code (row c) <;> simp_all

def gateFlag (v0 v1 v2 v3 v4 v5 v6 v7 v8 : BitVec 2) : Bool :=
  decide (v0 ≠ v5) &&
  decide (v1 ≠ v6) &&
  decide (v2 ≠ v3) &&
  decide (v3 ≠ v4) &&
  decide (v3 ≠ v8) &&
  decide (v5 ≠ v7) &&
  decide (v5 ≠ v8) &&
  decide (v6 ≠ v8) &&
  decide (v0 = v1 → v4 ≤ v0) &&
  decide (v0 = v1 → v5 ≤ v0) &&
  decide (v0 = v3 → v4 ≤ v0) &&
  decide (v0 = v3 → v5 ≤ v0) &&
  decide (v0 = v4 → v5 ≤ v0) &&
  decide (v0 = v6 → v8 ≤ v0) &&
  decide (v0 = v7 → v5 ≤ v0) &&
  decide (v0 = v8 → v4 ≤ v0) &&
  decide (v0 = v8 → v5 ≤ v0) &&
  decide (v1 = v2 → v3 ≤ v1) &&
  decide (v1 = v3 → v2 ≤ v1) &&
  decide (v1 = v3 → v4 ≤ v1) &&
  decide (v1 = v3 → v6 ≤ v1) &&
  decide (v1 = v3 → v8 ≤ v1) &&
  decide (v1 = v4 → v3 ≤ v1) &&
  decide (v1 = v5 → v0 ≤ v1) &&
  decide (v1 = v5 → v6 ≤ v1) &&
  decide (v1 = v5 → v7 ≤ v1) &&
  decide (v1 = v5 → v8 ≤ v1) &&
  decide (v1 = v7 → v2 ≤ v1) &&
  decide (v1 = v7 → v6 ≤ v1) &&
  decide (v1 = v8 → v3 ≤ v1) &&
  decide (v1 = v8 → v6 ≤ v1) &&
  decide (v2 = v4 → v3 ≤ v2) &&
  decide (v2 = v5 → v3 ≤ v2) &&
  decide (v2 = v5 → v7 ≤ v2) &&
  decide (v2 = v6 → v7 ≤ v2) &&
  decide (v2 = v6 → v8 ≤ v2) &&
  decide (v2 = v7 → v3 ≤ v2) &&
  decide (v2 = v8 → v3 ≤ v2) &&
  decide (v2 = v8 → v6 ≤ v2) &&
  decide (v2 = v8 → v7 ≤ v2) &&
  decide (v3 = v5 → v0 ≤ v3) &&
  decide (v3 = v5 → v2 ≤ v3) &&
  decide (v3 = v5 → v4 ≤ v3) &&
  decide (v3 = v5 → v7 ≤ v3) &&
  decide (v3 = v5 → v8 ≤ v3) &&
  decide (v3 = v6 → v1 ≤ v3) &&
  decide (v3 = v6 → v4 ≤ v3) &&
  decide (v3 = v6 → v8 ≤ v3) &&
  decide (v3 = v7 → v2 ≤ v3) &&
  decide (v3 = v7 → v5 ≤ v3) &&
  decide (v4 = v5 → v0 ≤ v4) &&
  decide (v4 = v5 → v3 ≤ v4) &&
  decide (v4 = v5 → v7 ≤ v4) &&
  decide (v4 = v6 → v3 ≤ v4) &&
  decide (v4 = v6 → v8 ≤ v4) &&
  decide (v4 = v7 → v2 ≤ v4) &&
  decide (v4 = v7 → v3 ≤ v4) &&
  decide (v4 = v8 → v0 ≤ v4) &&
  decide (v4 = v8 → v3 ≤ v4) &&
  decide (v4 = v8 → v6 ≤ v4) &&
  decide (v5 = v6 → v1 ≤ v5) &&
  decide (v5 = v6 → v7 ≤ v5) &&
  decide (v5 = v6 → v8 ≤ v5) &&
  decide (v6 = v7 → v1 ≤ v6) &&
  decide (v6 = v7 → v2 ≤ v6) &&
  decide (v6 = v7 → v5 ≤ v6) &&
  decide (v6 = v7 → v8 ≤ v6) &&
  decide (v7 = v8 → v2 ≤ v7) &&
  decide (v7 = v8 → v5 ≤ v7)

def rankOK (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : BitVec 2) : Prop :=
  v0 = 3 ∧ v1 = 3 ∧ v2 = 3 ∧ v4 = 3 ∧ v7 = 3 ∧ v8 = 3 ∧ (v9 = 3 ∨ v9 = v3 ∨ v9 = v5 ∨ v9 = v6)

def rankNine (v0 v1 v2 v3 v4 v5 v6 v7 v8 : BitVec 2) : Bool := decide (v0 = 3 ∧ v1 = 3 ∧ v2 = 3 ∧ v4 = 3 ∧ v7 = 3 ∧ v8 = 3 ∧ (v3 ≠ v5 ∧ v3 ≠ v6 ∧ v5 ≠ v6 ∧ v3 ≠ 3 ∧ v5 ≠ 3 ∧ v6 ≠ 3))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ck00 : ∀ (v2 v3 v4 v5 v6 v7 v8 : BitVec 2), gateFlag 0 0 v2 v3 v4 v5 v6 v7 v8 = true → rankNine 0 0 v2 v3 v4 v5 v6 v7 v8 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ck01 : ∀ (v2 v3 v4 v5 v6 v7 v8 : BitVec 2), gateFlag 0 1 v2 v3 v4 v5 v6 v7 v8 = true → rankNine 0 1 v2 v3 v4 v5 v6 v7 v8 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ck02 : ∀ (v2 v3 v4 v5 v6 v7 v8 : BitVec 2), gateFlag 0 2 v2 v3 v4 v5 v6 v7 v8 = true → rankNine 0 2 v2 v3 v4 v5 v6 v7 v8 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ck03 : ∀ (v2 v3 v4 v5 v6 v7 v8 : BitVec 2), gateFlag 0 3 v2 v3 v4 v5 v6 v7 v8 = true → rankNine 0 3 v2 v3 v4 v5 v6 v7 v8 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ck10 : ∀ (v2 v3 v4 v5 v6 v7 v8 : BitVec 2), gateFlag 1 0 v2 v3 v4 v5 v6 v7 v8 = true → rankNine 1 0 v2 v3 v4 v5 v6 v7 v8 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ck11 : ∀ (v2 v3 v4 v5 v6 v7 v8 : BitVec 2), gateFlag 1 1 v2 v3 v4 v5 v6 v7 v8 = true → rankNine 1 1 v2 v3 v4 v5 v6 v7 v8 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ck12 : ∀ (v2 v3 v4 v5 v6 v7 v8 : BitVec 2), gateFlag 1 2 v2 v3 v4 v5 v6 v7 v8 = true → rankNine 1 2 v2 v3 v4 v5 v6 v7 v8 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ck13 : ∀ (v2 v3 v4 v5 v6 v7 v8 : BitVec 2), gateFlag 1 3 v2 v3 v4 v5 v6 v7 v8 = true → rankNine 1 3 v2 v3 v4 v5 v6 v7 v8 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ck20 : ∀ (v2 v3 v4 v5 v6 v7 v8 : BitVec 2), gateFlag 2 0 v2 v3 v4 v5 v6 v7 v8 = true → rankNine 2 0 v2 v3 v4 v5 v6 v7 v8 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ck21 : ∀ (v2 v3 v4 v5 v6 v7 v8 : BitVec 2), gateFlag 2 1 v2 v3 v4 v5 v6 v7 v8 = true → rankNine 2 1 v2 v3 v4 v5 v6 v7 v8 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ck22 : ∀ (v2 v3 v4 v5 v6 v7 v8 : BitVec 2), gateFlag 2 2 v2 v3 v4 v5 v6 v7 v8 = true → rankNine 2 2 v2 v3 v4 v5 v6 v7 v8 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ck23 : ∀ (v2 v3 v4 v5 v6 v7 v8 : BitVec 2), gateFlag 2 3 v2 v3 v4 v5 v6 v7 v8 = true → rankNine 2 3 v2 v3 v4 v5 v6 v7 v8 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ck30 : ∀ (v2 v3 v4 v5 v6 v7 v8 : BitVec 2), gateFlag 3 0 v2 v3 v4 v5 v6 v7 v8 = true → rankNine 3 0 v2 v3 v4 v5 v6 v7 v8 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ck31 : ∀ (v2 v3 v4 v5 v6 v7 v8 : BitVec 2), gateFlag 3 1 v2 v3 v4 v5 v6 v7 v8 = true → rankNine 3 1 v2 v3 v4 v5 v6 v7 v8 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ck32 : ∀ (v2 v3 v4 v5 v6 v7 v8 : BitVec 2), gateFlag 3 2 v2 v3 v4 v5 v6 v7 v8 = true → rankNine 3 2 v2 v3 v4 v5 v6 v7 v8 = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ck33 : ∀ (v2 v3 v4 v5 v6 v7 v8 : BitVec 2), gateFlag 3 3 v2 v3 v4 v5 v6 v7 v8 = true → rankNine 3 3 v2 v3 v4 v5 v6 v7 v8 = true := by decide +kernel

lemma checked (v0 v1 v2 v3 v4 v5 v6 v7 v8 : BitVec 2) (h : gateFlag v0 v1 v2 v3 v4 v5 v6 v7 v8 = true) : rankNine v0 v1 v2 v3 v4 v5 v6 v7 v8 = true := by
  have a : v0 = 0 ∨ v0 = 1 ∨ v0 = 2 ∨ v0 = 3 := (by decide : ∀ v : BitVec 2, v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3) v0
  have b : v1 = 0 ∨ v1 = 1 ∨ v1 = 2 ∨ v1 = 3 := (by decide : ∀ v : BitVec 2, v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3) v1
  rcases a with rfl | rfl | rfl | rfl <;> rcases b with rfl | rfl | rfl | rfl
  · exact ck00 _ _ _ _ _ _ _ h
  · exact ck01 _ _ _ _ _ _ _ h
  · exact ck02 _ _ _ _ _ _ _ h
  · exact ck03 _ _ _ _ _ _ _ h
  · exact ck10 _ _ _ _ _ _ _ h
  · exact ck11 _ _ _ _ _ _ _ h
  · exact ck12 _ _ _ _ _ _ _ h
  · exact ck13 _ _ _ _ _ _ _ h
  · exact ck20 _ _ _ _ _ _ _ h
  · exact ck21 _ _ _ _ _ _ _ h
  · exact ck22 _ _ _ _ _ _ _ h
  · exact ck23 _ _ _ _ _ _ _ h
  · exact ck30 _ _ _ _ _ _ _ h
  · exact ck31 _ _ _ _ _ _ _ h
  · exact ck32 _ _ _ _ _ _ _ h
  · exact ck33 _ _ _ _ _ _ _ h

lemma fill : ∀ (a b c d : BitVec 2), a ≠ b → a ≠ c → b ≠ c → a ≠ 3 → b ≠ 3 → c ≠ 3 → d = 3 ∨ d = a ∨ d = b ∨ d = c := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma classify (label : Fin 10 → Fin 4)
    (conf : ∀ e ∈ conflicts, label e.1 ≠ label e.2)
    (cut : ∀ t, t < 3 → Cut label t) :
    label 0 = 3 ∧ label 1 = 3 ∧ label 2 = 3 ∧ label 4 = 3 ∧ label 7 = 3 ∧ label 8 = 3 ∧
      (label 9 = 3 ∨ label 9 = label 3 ∨ label 9 = label 5 ∨ label 9 = label 6) := by
  let f (i : Fin 10) : BitVec 2 := BitVec.ofFin (label i)
  have inj {i j : Fin 10} (h : f i = f j) : label i = label j := congrArg BitVec.toFin h
  have hcf (i j : Fin 10) (hm : (i,j) ∈ conflicts) : f i ≠ f j := fun h => conf (i,j) hm (inj h)
  have hbound (i j k : Fin 10) (a b c : ℕ) (hw : cube i j k a b c) :
      f i = f j → f k ≤ f i := fun h => cubeBound label cut i j k a b c hw (inj h)
  have z0 := hcf 0 5 (by decide)
  have z1 := hcf 1 6 (by decide)
  have z2 := hcf 2 3 (by decide)
  have z3 := hcf 3 4 (by decide)
  have z4 := hcf 3 8 (by decide)
  have z5 := hcf 5 7 (by decide)
  have z6 := hcf 5 8 (by decide)
  have z7 := hcf 6 8 (by decide)
  have z8 := hbound 0 1 4 517 518 516 (by unfold cube valid; decide)
  have z9 := hbound 0 1 5 517 518 516 (by unfold cube valid; decide)
  have z10 := hbound 0 3 4 517 524 516 (by unfold cube valid; decide)
  have z11 := hbound 0 3 5 517 524 516 (by unfold cube valid; decide)
  have z12 := hbound 0 4 5 517 533 516 (by unfold cube valid; decide)
  have z13 := hbound 0 6 8 533 596 532 (by unfold cube valid; decide)
  have z14 := hbound 0 7 5 517 644 516 (by unfold cube valid; decide)
  have z15 := hbound 0 8 4 581 836 580 (by unfold cube valid; decide)
  have z16 := hbound 0 8 5 533 788 532 (by unfold cube valid; decide)
  have z17 := hbound 1 2 3 515 517 513 (by unfold cube valid; decide)
  have z18 := hbound 1 3 2 515 521 513 (by unfold cube valid; decide)
  have z19 := hbound 1 3 4 66 72 64 (by unfold cube valid; decide)
  have z20 := hbound 1 3 6 18 24 16 (by unfold cube valid; decide)
  have z21 := hbound 1 3 8 515 521 513 (by unfold cube valid; decide)
  have z22 := hbound 1 4 3 66 80 64 (by unfold cube valid; decide)
  have z23 := hbound 1 5 0 518 548 516 (by unfold cube valid; decide)
  have z24 := hbound 1 5 6 130 160 128 (by unfold cube valid; decide)
  have z25 := hbound 1 5 7 66 96 64 (by unfold cube valid; decide)
  have z26 := hbound 1 5 8 518 548 516 (by unfold cube valid; decide)
  have z27 := hbound 1 7 2 515 641 513 (by unfold cube valid; decide)
  have z28 := hbound 1 7 6 34 160 32 (by unfold cube valid; decide)
  have z29 := hbound 1 8 3 515 769 513 (by unfold cube valid; decide)
  have z30 := hbound 1 8 6 10 264 8 (by unfold cube valid; decide)
  have z31 := hbound 2 4 3 517 529 513 (by unfold cube valid; decide)
  have z32 := hbound 2 5 3 517 545 513 (by unfold cube valid; decide)
  have z33 := hbound 2 5 7 517 545 513 (by unfold cube valid; decide)
  have z34 := hbound 2 6 7 773 833 769 (by unfold cube valid; decide)
  have z35 := hbound 2 6 8 645 705 641 (by unfold cube valid; decide)
  have z36 := hbound 2 7 3 517 645 513 (by unfold cube valid; decide)
  have z37 := hbound 2 8 3 581 833 577 (by unfold cube valid; decide)
  have z38 := hbound 2 8 6 645 897 641 (by unfold cube valid; decide)
  have z39 := hbound 2 8 7 581 833 577 (by unfold cube valid; decide)
  have z40 := hbound 3 5 0 524 548 516 (by unfold cube valid; decide)
  have z41 := hbound 3 5 2 521 545 513 (by unfold cube valid; decide)
  have z42 := hbound 3 5 4 136 160 128 (by unfold cube valid; decide)
  have z43 := hbound 3 5 7 24 48 16 (by unfold cube valid; decide)
  have z44 := hbound 3 5 8 24 48 16 (by unfold cube valid; decide)
  have z45 := hbound 3 6 1 24 80 16 (by unfold cube valid; decide)
  have z46 := hbound 3 6 4 10 66 2 (by unfold cube valid; decide)
  have z47 := hbound 3 6 8 10 66 2 (by unfold cube valid; decide)
  have z48 := hbound 3 7 2 777 897 769 (by unfold cube valid; decide)
  have z49 := hbound 3 7 5 24 144 16 (by unfold cube valid; decide)
  have z50 := hbound 4 5 0 788 804 772 (by unfold cube valid; decide)
  have z51 := hbound 4 5 3 144 160 128 (by unfold cube valid; decide)
  have z52 := hbound 4 5 7 24 40 8 (by unfold cube valid; decide)
  have z53 := hbound 4 6 3 18 66 2 (by unfold cube valid; decide)
  have z54 := hbound 4 6 8 529 577 513 (by unfold cube valid; decide)
  have z55 := hbound 4 7 2 529 641 513 (by unfold cube valid; decide)
  have z56 := hbound 4 7 3 48 160 32 (by unfold cube valid; decide)
  have z57 := hbound 4 8 0 596 836 580 (by unfold cube valid; decide)
  have z58 := hbound 4 8 3 48 288 32 (by unfold cube valid; decide)
  have z59 := hbound 4 8 6 529 769 513 (by unfold cube valid; decide)
  have z60 := hbound 5 6 1 160 192 128 (by unfold cube valid; decide)
  have z61 := hbound 5 6 7 34 66 2 (by unfold cube valid; decide)
  have z62 := hbound 5 6 8 34 66 2 (by unfold cube valid; decide)
  have z63 := hbound 6 7 1 96 160 32 (by unfold cube valid; decide)
  have z64 := hbound 6 7 2 833 897 769 (by unfold cube valid; decide)
  have z65 := hbound 6 7 5 66 130 2 (by unfold cube valid; decide)
  have z66 := hbound 6 7 8 580 644 516 (by unfold cube valid; decide)
  have z67 := hbound 7 8 2 705 833 577 (by unfold cube valid; decide)
  have z68 := hbound 7 8 5 136 264 8 (by unfold cube valid; decide)
  have flags : gateFlag (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) = true := by
    simp only [gateFlag, Bool.and_eq_true, decide_eq_true_eq]
    repeat' first | assumption | constructor
  have rr := checked (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) flags
  simp only [rankNine, decide_eq_true_eq] at rr
  obtain ⟨a,b,c,d,e,g,h,i,j,k,l,m⟩ := rr
  have lift3 (v : Fin 10) (hv : f v = 3) : label v = 3 := congrArg BitVec.toFin hv
  refine ⟨lift3 _ a,lift3 _ b,lift3 _ c,lift3 _ d,lift3 _ e,lift3 _ g,?_⟩
  rcases fill _ _ _ (f 9) h i j k l m with u | u | u | u
  · exact Or.inl (lift3 _ u)
  · exact Or.inr (Or.inl (inj u))
  · exact Or.inr (Or.inr (Or.inl (inj u)))
  · exact Or.inr (Or.inr (Or.inr (inj u)))

abbrev X := Fin 10 → Bool
def Earlier (i : Fin 10) : Prop := i = 3 ∨ i = 5 ∨ i = 6 ∨ i = 9
def Choice (d : Fin 10) : Prop := d = 3 ∨ d = 5 ∨ d = 6
def anchor (d : Fin 10) (z b : Bool) (i : Fin 10) : Bool := if i = d then b else if i = 9 then z else false
def sample (d : Fin 10) (z b : Bool) : X :=
  row ((if d = 3 then (if z then 516 else 16) else if d = 5 then (if z then 513 else 128) else (if z then 769 else 2))
    + (if b then 2 ^ d.val else 0))
lemma sampleCheck : ∀ d : Fin 10, Choice d → ∀ z : Bool,
    (∀ b, valid (sample d z b)) ∧ target (sample d z false) ≠ target (sample d z true) ∧
    (∀ b i, Earlier i → sample d z b i = anchor d z b i) ∧
    (∀ i, i ≠ d → sample d z false i = sample d z true i) := by
  unfold Choice Earlier valid
  decide +kernel

def Forbid (F : X → Bool) (i j : Fin 10) : Prop :=
  ∀ (a o : X), (∀ u v, F (PetersenScratch.pairInput i j a u v) = (u && v)) →
    (∀ u v, F (PetersenScratch.pairInput i j o u v) = (u || v)) → False

lemma early (F : X → Bool) (ok : ∀ x, valid x → F x = target x)
    (label : Fin 10 → Fin 4) (k : Fin 4) (d : Fin 10) (hd : Choice d)
    (ld : label d = k) (lz : label 9 = k)
    (earlyOnly : ∀ i, label i ≤ k → Earlier i)
    (c : X → Bool) (un : Unate c d)
    (low : ∀ x y : X, (∀ i, label i ≤ k → x i = y i) → c x = c y)
    (high : ∀ x y : X, (∀ i, label i ≠ k → x i = y i) → c x = c y → F x = F y)
    (forbid : Forbid F 0 1) : False := by
  have diff (z : Bool) : c (anchor d z false) ≠ c (anchor d z true) := by
    intro eq
    obtain ⟨good, differs, share, other⟩ := sampleCheck d hd z
    have proj (b : Bool) : c (sample d z b) = c (anchor d z b) :=
      low _ _ (fun i hi => share b i (earlyOnly i hi))
    have e := high (sample d z false) (sample d z true)
      (fun i hi => other i (fun h => hi (h ▸ ld))) ((proj false).trans (eq.trans (proj true).symm))
    exact differs (((ok _ (good false)).symm.trans e).trans (ok _ (good true)))
  obtain ⟨sg, orient⟩ := un
  have ord (z : Bool) := orient (anchor d z false) (anchor d z true)
    (fun i hi => by simp [anchor,hi]) (by simp [anchor]) (by simp [anchor])
  have force : ∀ s a b v w : Bool, a ≠ b → v ≠ w → Orient s a b → Orient s v w → a = v := by decide
  have fixed := force _ _ _ _ _ (diff false) (diff true) (ord false) (ord true)
  have eqZero (z : Bool) : c (anchor d false false) = c (anchor d z false) := by cases z <;> first | rfl | exact fixed
  let setZ (x : X) := Function.update x 9 (x 0 || x 2)
  have bridge (x : X) (zero : ∀ i, Earlier i → x i = false) : F x = target (setZ x) := by
    have dne : d ≠ 9 := by rcases hd with rfl | rfl | rfl <;> decide
    have h1 : c x = c (anchor d false false) := low _ _ (by
      intro i hi
      rw [zero i (earlyOnly i hi)]
      simp [anchor])
    have h2 : c (setZ x) = c (anchor d (x 0 || x 2) false) := low _ _ (by
      intro i hi
      by_cases hz : i = 9
      · subst i; simp [setZ,anchor,Ne.symm dne]
      · simp [setZ,anchor,Function.update_of_ne hz,hz,zero i (earlyOnly i hi)])
    have same := high x (setZ x) (fun i hi => by
      have ne : i ≠ 9 := fun e => hi (e ▸ lz)
      simp [setZ,Function.update_of_ne ne]) (h1.trans ((eqZero _).trans h2.symm))
    exact same.trans (ok _ (by simp [valid,setZ,Function.update_of_ne]))
  apply forbid (row 0) (row 20)
  · intro a b
    rw [bridge _ (by revert a b; unfold Earlier; decide)]
    exact (by decide : ∀ a b : Bool, target (Function.update (PetersenScratch.pairInput 0 1 (row 0) a b) 9
      ((PetersenScratch.pairInput 0 1 (row 0) a b) 0 || (PetersenScratch.pairInput 0 1 (row 0) a b) 2)) = (a && b)) a b
  · intro a b
    rw [bridge _ (by revert a b; unfold Earlier; decide)]
    exact (by decide : ∀ a b : Bool, target (Function.update (PetersenScratch.pairInput 0 1 (row 20) a b) 9
      ((PetersenScratch.pairInput 0 1 (row 20) a b) 0 || (PetersenScratch.pairInput 0 1 (row 20) a b) 2)) = (a || b)) a b


end Finite2770

namespace Conflict2770

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof PetersenCutFormula PetersenCutIndependent PetersenFirstGroup PetersenCutTrace PetersenScratch

def pairs : List (Fin 10 × Fin 10) :=
  [(0,5),(1,6),(2,3),(3,4),(3,8),(5,7),(5,8),(6,8)]

def value (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)

def contexts (e : Fin 10 × Fin 10) : Nat × Nat :=
  match e.1.val, e.2.val with
  | 0, 5 => (516, 788)
  | 1, 6 => (0, 769)
  | 2, 3 => (513, 897)
  | 3, 4 => (0, 517)
  | 3, 8 => (0, 48)
  | 5, 7 => (0, 517)
  | 5, 8 => (0, 136)
  | 6, 8 => (0, 10)
  | _, _ => (0,0)

def bits (v : Nat) (i : Fin 10) := v.testBit i.val

theorem checkedContexts : ∀ e ∈ pairs, ∀ (a b : Bool),
    let xa := pairInput e.1 e.2 (bits (contexts e).1) a b
    let xo := pairInput e.1 e.2 (bits (contexts e).2) a b
    xa 9 = (xa 0 || xa 2) ∧ value xa = (a && b) ∧
      xo 9 = (xo 0 || xo 2) ∧ value xo = (a || b) := by
  decide +kernel

theorem boundaryConflict {gs : List Gate} (clean : CleanL 10 gs)
    (out : Fin (10 + gs.length))
    (live : ∀ w : Fin (10 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (computes : ∀ x : Fin 10 → Bool, x 9 = (x 0 || x 2) → vl gs x out.val = value x)
    (e : Fin 10 × Fin 10) (he : e ∈ pairs) :
    firstInputBoundary clean out live e.1 ≠ firstInputBoundary clean out live e.2 := by
  intro same
  let cut := firstInputBoundary clean out live e.1
  have hi := firstInputBoundary_occurrences_le_one clean out live distinct e.1 e.1
  have hj := firstInputBoundary_occurrences_le_one clean out live distinct e.1 e.2
  rw [← same] at hj
  have controlled : cut = out ∨ ∀ k : Fin 10, (k = e.1 ∨ k = e.2) →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out := by
    rcases firstInputGroup_controlled clean out live cut with h | h
    · exact Or.inl h
    · apply Or.inr
      intro k hk
      apply h
      apply (mem_firstInputGroup clean out live cut k).mpr
      rcases hk with hk | hk
      · rw [hk]
      · rw [hk]
        exact same.symm
  have factor (base : Fin 10 → Bool) : ∃ outer : Bool → Bool, ∀ a b,
      outer (pairValue e.1 e.2 base (wireFormula e.1 gs cut.val) a b) =
        vl gs (pairInput e.1 e.2 base a b) out.val := by
    obtain ⟨outer, ho⟩ := cut_factors clean cut out (fun k => k = e.1 ∨ k = e.2) base controlled
    refine ⟨outer, fun a b => ?_⟩
    unfold pairValue
    rw [wireFormula_eval e.1 clean _ cut.val cut.isLt]
    apply ho
    intro k hk
    simp [pairInput, show k ≠ e.1 from fun h => hk (Or.inl h),
      show k ≠ e.2 from fun h => hk (Or.inr h)]
  obtain ⟨fa, ha⟩ := factor (bits (contexts e).1)
  obtain ⟨fo, ho⟩ := factor (bits (contexts e).2)
  apply fixed_pair_invariant e.1 e.2 (wireFormula e.1 gs cut.val) hi hj _ _ fa fo
  · intro a b
    have h := checkedContexts e he a b
    exact (ha a b).trans ((computes _ h.1).trans h.2.1)
  · intro a b
    have h := checkedContexts e he a b
    exact (ho a b).trans ((computes _ h.2.2.1).trans h.2.2.2)

theorem generalConflict {gs : List Gate} (clean : CleanL 10 gs)
    (out : Fin (10 + gs.length))
    (live : ∀ w : Fin (10 + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (e : Fin 10 × Fin 10)
    (same : firstInputBoundary clean out live e.1 = firstInputBoundary clean out live e.2) :
    Finite2770.Forbid (fun x => vl gs x out.val) e.1 e.2 := by
  intro ctxA ctxO hand hor
  let cut := firstInputBoundary clean out live e.1
  have hi := firstInputBoundary_occurrences_le_one clean out live distinct e.1 e.1
  have hj := firstInputBoundary_occurrences_le_one clean out live distinct e.1 e.2
  rw [← same] at hj
  have controlled : cut = out ∨ ∀ k : Fin 10, (k = e.1 ∨ k = e.2) →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out := by
    rcases firstInputGroup_controlled clean out live cut with h | h
    · exact Or.inl h
    · apply Or.inr
      intro k hk
      apply h
      apply (mem_firstInputGroup clean out live cut k).mpr
      rcases hk with hk | hk
      · rw [hk]
      · rw [hk]
        exact same.symm
  have factor (base : Fin 10 → Bool) : ∃ outer : Bool → Bool, ∀ a b,
      outer (pairValue e.1 e.2 base (wireFormula e.1 gs cut.val) a b) =
        vl gs (pairInput e.1 e.2 base a b) out.val := by
    obtain ⟨outer, ho⟩ := cut_factors clean cut out (fun k => k = e.1 ∨ k = e.2) base controlled
    refine ⟨outer, fun a b => ?_⟩
    unfold pairValue
    rw [wireFormula_eval e.1 clean _ cut.val cut.isLt]
    apply ho
    intro k hk
    simp [pairInput, show k ≠ e.1 from fun h => hk (Or.inl h),
      show k ≠ e.2 from fun h => hk (Or.inr h)]
  obtain ⟨fa, ha⟩ := factor ctxA
  obtain ⟨fo, ho⟩ := factor ctxO
  apply fixed_pair_invariant e.1 e.2 (wireFormula e.1 gs cut.val) hi hj _ _ fa fo
  · intro a b; exact (ha a b).trans (hand a b)
  · intro a b; exact (ho a b).trans (hor a b)

end Conflict2770

open CircuitProof CircuitProof.Readers PetersenCutTrace PetersenFirstGroup

namespace Finite2770

lemma finiteContradiction : ∀ (u105 u107 u121 u512 u514 : Bool),
    (true = true → u107 = true) →
    (true = true → u121 = true) →
    (u512 = true → false = true) →
    ¬ ((false = false ∧ false = false ∧ false = false ∧ true = true) ∧ (false = false ∧ true = true ∧ u105 = true ∧ u121 = true)) →
    ¬ ((u512 = false ∧ false = false ∧ u514 = false ∧ true = true) ∧ (false = false ∧ true = true ∧ true = true ∧ true = true)) →
    ¬ ((false = false ∧ u512 = false ∧ false = false ∧ u514 = true) ∧ (u105 = false ∧ true = true ∧ u107 = true ∧ true = true)) →
    False := by decide

lemma late (F : X → Bool) (ok : ∀ x, valid x → F x = target x)
    (un : Unate F 0) (b04 : Forbid F 0 4) (b12 : Forbid F 1 2) (b19 : Forbid F 1 9) : False := by
  obtain ⟨sg,om⟩ := un
  have orow (a b : ℕ) (off : ∀ j : Fin 10, j ≠ 0 → row a j = row b j)
      (ha : row a 0 = false) (hb : row b 0 = true) := om (row a) (row b) off ha hb
  have up := orow 532 533 (by decide) (by decide) (by decide)
  have v0 : F (row 0) = false := (ok _ (by decide)).trans (by decide)
  have v2 : F (row 2) = false := (ok _ (by decide)).trans (by decide)
  have v104 : F (row 104) = false := (ok _ (by decide)).trans (by decide)
  have v106 : F (row 106) = true := (ok _ (by decide)).trans (by decide)
  have v120 : F (row 120) = true := (ok _ (by decide)).trans (by decide)
  have v513 : F (row 513) = false := (ok _ (by decide)).trans (by decide)
  have v516 : F (row 516) = false := (ok _ (by decide)).trans (by decide)
  have v517 : F (row 517) = false := (ok _ (by decide)).trans (by decide)
  have v518 : F (row 518) = true := (ok _ (by decide)).trans (by decide)
  have v532 : F (row 532) = false := (ok _ (by decide)).trans (by decide)
  have v533 : F (row 533) = true := (ok _ (by decide)).trans (by decide)
  have v617 : F (row 617) = true := (ok _ (by decide)).trans (by decide)
  have v619 : F (row 619) = true := (ok _ (by decide)).trans (by decide)
  have v641 : F (row 641) = false := (ok _ (by decide)).trans (by decide)
  have v643 : F (row 643) = true := (ok _ (by decide)).trans (by decide)
  have v645 : F (row 645) = true := (ok _ (by decide)).trans (by decide)
  have v647 : F (row 647) = true := (ok _ (by decide)).trans (by decide)
  rw [v532,v533] at up
  have pos : sg = true := (by decide : ∀ s : Bool, Orient s false true → s = true) _ up
  subst sg
  have m106 : F (row 106) = true → F (row 107) = true := orow 106 107 (by decide) (by decide) (by decide)
  have m120 : F (row 120) = true → F (row 121) = true := orow 120 121 (by decide) (by decide) (by decide)
  have m512 : F (row 512) = true → F (row 513) = true := orow 512 513 (by decide) (by decide) (by decide)
  have p04 : ¬ ((F (row 516) = false ∧ F (row 532) = false ∧ F (row 517) = false ∧ F (row 533) = true) ∧ (F (row 104) = false ∧ F (row 120) = true ∧ F (row 105) = true ∧ F (row 121) = true)) := by
    rintro ⟨ha,ho⟩
    apply b04 (row 516) (row 104)
    · intro u v; cases u <;> cases v
      · rw [show PetersenScratch.pairInput 0 4 (row 516) false false = row 516 from (by funext t; fin_cases t <;> rfl)]
        exact ha.1
      · rw [show PetersenScratch.pairInput 0 4 (row 516) false true = row 532 from (by funext t; fin_cases t <;> rfl)]
        exact ha.2.1
      · rw [show PetersenScratch.pairInput 0 4 (row 516) true false = row 517 from (by funext t; fin_cases t <;> rfl)]
        exact ha.2.2.1
      · rw [show PetersenScratch.pairInput 0 4 (row 516) true true = row 533 from (by funext t; fin_cases t <;> rfl)]
        exact ha.2.2.2
    · intro u v; cases u <;> cases v
      · rw [show PetersenScratch.pairInput 0 4 (row 104) false false = row 104 from (by funext t; fin_cases t <;> rfl)]
        exact ho.1
      · rw [show PetersenScratch.pairInput 0 4 (row 104) false true = row 120 from (by funext t; fin_cases t <;> rfl)]
        exact ho.2.1
      · rw [show PetersenScratch.pairInput 0 4 (row 104) true false = row 105 from (by funext t; fin_cases t <;> rfl)]
        exact ho.2.2.1
      · rw [show PetersenScratch.pairInput 0 4 (row 104) true true = row 121 from (by funext t; fin_cases t <;> rfl)]
        exact ho.2.2.2
  have p12 : ¬ ((F (row 512) = false ∧ F (row 516) = false ∧ F (row 514) = false ∧ F (row 518) = true) ∧ (F (row 641) = false ∧ F (row 645) = true ∧ F (row 643) = true ∧ F (row 647) = true)) := by
    rintro ⟨ha,ho⟩
    apply b12 (row 512) (row 641)
    · intro u v; cases u <;> cases v
      · rw [show PetersenScratch.pairInput 1 2 (row 512) false false = row 512 from (by funext t; fin_cases t <;> rfl)]
        exact ha.1
      · rw [show PetersenScratch.pairInput 1 2 (row 512) false true = row 516 from (by funext t; fin_cases t <;> rfl)]
        exact ha.2.1
      · rw [show PetersenScratch.pairInput 1 2 (row 512) true false = row 514 from (by funext t; fin_cases t <;> rfl)]
        exact ha.2.2.1
      · rw [show PetersenScratch.pairInput 1 2 (row 512) true true = row 518 from (by funext t; fin_cases t <;> rfl)]
        exact ha.2.2.2
    · intro u v; cases u <;> cases v
      · rw [show PetersenScratch.pairInput 1 2 (row 641) false false = row 641 from (by funext t; fin_cases t <;> rfl)]
        exact ho.1
      · rw [show PetersenScratch.pairInput 1 2 (row 641) false true = row 645 from (by funext t; fin_cases t <;> rfl)]
        exact ho.2.1
      · rw [show PetersenScratch.pairInput 1 2 (row 641) true false = row 643 from (by funext t; fin_cases t <;> rfl)]
        exact ho.2.2.1
      · rw [show PetersenScratch.pairInput 1 2 (row 641) true true = row 647 from (by funext t; fin_cases t <;> rfl)]
        exact ho.2.2.2
  have p19 : ¬ ((F (row 0) = false ∧ F (row 512) = false ∧ F (row 2) = false ∧ F (row 514) = true) ∧ (F (row 105) = false ∧ F (row 617) = true ∧ F (row 107) = true ∧ F (row 619) = true)) := by
    rintro ⟨ha,ho⟩
    apply b19 (row 0) (row 105)
    · intro u v; cases u <;> cases v
      · rw [show PetersenScratch.pairInput 1 9 (row 0) false false = row 0 from (by funext t; fin_cases t <;> rfl)]
        exact ha.1
      · rw [show PetersenScratch.pairInput 1 9 (row 0) false true = row 512 from (by funext t; fin_cases t <;> rfl)]
        exact ha.2.1
      · rw [show PetersenScratch.pairInput 1 9 (row 0) true false = row 2 from (by funext t; fin_cases t <;> rfl)]
        exact ha.2.2.1
      · rw [show PetersenScratch.pairInput 1 9 (row 0) true true = row 514 from (by funext t; fin_cases t <;> rfl)]
        exact ha.2.2.2
    · intro u v; cases u <;> cases v
      · rw [show PetersenScratch.pairInput 1 9 (row 105) false false = row 105 from (by funext t; fin_cases t <;> rfl)]
        exact ho.1
      · rw [show PetersenScratch.pairInput 1 9 (row 105) false true = row 617 from (by funext t; fin_cases t <;> rfl)]
        exact ho.2.1
      · rw [show PetersenScratch.pairInput 1 9 (row 105) true false = row 107 from (by funext t; fin_cases t <;> rfl)]
        exact ho.2.2.1
      · rw [show PetersenScratch.pairInput 1 9 (row 105) true true = row 619 from (by funext t; fin_cases t <;> rfl)]
        exact ho.2.2.2
  apply finiteContradiction (F (row 105)) (F (row 107)) (F (row 121)) (F (row 512)) (F (row 514))
  · simpa only [v106] using m106
  · simpa only [v120] using m120
  · simpa only [v513] using m512
  · simpa only [v516, v532, v517, v533, v104, v120] using p04
  · simpa only [v516, v518, v641, v645, v643, v647] using p12
  · simpa only [v0, v2, v617, v619] using p19

end Finite2770

lemma noSuffix (D : Circuit) (fan : FanInTwo D) (budget : nonNotCount D.gates ≤ 12)
    (agree : ∀ x : Fin 10 → Bool, x 9 = (x 0 || x 2) →
      circuitFun 10 D x = Suffix2770.F (fun i : Fin 9 => x i.castSucc))
    (dep : ∀ i, Dep (circuitFun 10 D) i)
    (still : ∀ (i : Fin 10) (b : Bool), ∃ x y : Fin 10 → Bool,
      circuitFun 10 D (Function.update x i b) ≠ circuitFun 10 D (Function.update y i b)) : False := by
  classical
  have nc := dep_nc (dep 0)
  obtain ⟨gs, o, least, bound⟩ := least_with_budget D fan (fun _ => rfl) nc
  have valid : o < 10 + gs.length := by
    by_contra! h
    obtain ⟨x, y, different⟩ := least.ncv nc
    exact different ((vl_beyond gs x o h).trans (vl_beyond gs y o h).symm)
  let out : Fin (10 + gs.length) := ⟨o, valid⟩
  have live := least_read_edge_live least nc dep still valid
  have branches := threeForksOfBudget least.hcl out live (bound.trans budget)
  have distinct := predecessors_nodup least nc
  obtain ⟨label, locations, last, codes⟩ := normalizedCuts least.hcl out live distinct branches
  let F : Finite2770.X → Bool := fun x => vl gs x out.val
  have computes (x : Fin 10 → Bool) (hx : Finite2770.valid x) :
      F x = Finite2770.target x := (least.hev x).trans (agree x hx)
  have clash (i j : Fin 10) (h : label i = label j) : Finite2770.Forbid F i j :=
    Conflict2770.generalConflict least.hcl out live distinct (i,j) ((locations _ _).mp h)
  obtain ⟨l0,l1,l2,l4,l7,l8,pins⟩ := Finite2770.classify label (fun e he same =>
    Conflict2770.boundaryConflict least.hcl out live distinct computes e he ((locations _ _).mp same)) (by
    intro t _
    obtain ⟨c, _, low, high⟩ := codes t
    refine ⟨c,low,?_⟩
    intro x y hx hy rest same
    exact (computes x hx).symm.trans ((high x y rest same).trans (computes y hy)))
  by_cases z : label 9 = 3
  · have occ := firstInputBoundary_occurrences_le_one least.hcl out live distinct (0 : Fin 10) 0
    rw [last 0 l0] at occ
    have un := formulaUnate 0 _ occ
    have ev : (PetersenCutFormula.wireFormula (0 : Fin 10) gs out.val).eval = F :=
      funext fun x => PetersenCutFormula.wireFormula_eval _ least.hcl x _ out.isLt
    rw [ev] at un
    exact Finite2770.late F computes un (clash _ _ (l0.trans l4.symm))
      (clash _ _ (l1.trans l2.symm)) (clash _ _ (l1.trans z.symm))
  · have pick : ∃ d, Finite2770.Choice d ∧ label d = label 9 := by
      rcases pins with e | e | e | e
      · exact (z e).elim
      · exact ⟨3, Or.inl rfl, e.symm⟩
      · exact ⟨5, Or.inr (Or.inl rfl), e.symm⟩
      · exact ⟨6, Or.inr (Or.inr rfl), e.symm⟩
    obtain ⟨d,hd,ld⟩ := pick
    obtain ⟨code,un,low,high⟩ := codes (label 9)
    apply Finite2770.early F computes label (label 9) d hd ld rfl _ code (un d ld) low high (clash _ _ (l0.trans l1.symm))
    intro i hi
    rcases (by unfold Finite2770.Earlier; decide : ∀ v : Fin 10, Finite2770.Earlier v ∨ v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 4 ∨ v = 7 ∨ v = 8) i with e | e | e | e | e | e | e
    · exact e
    all_goals subst i
    all_goals first | rw [l0] at hi | rw [l1] at hi | rw [l2] at hi | rw [l4] at hi | rw [l7] at hi | rw [l8] at hi
    all_goals omega



namespace AdjacentSeed

open Finite2770
open PetersenScratch

abbrev valid12 (x : Fin 10 → Bool) : Prop := x 9 = (x 1 || x 2)

lemma positiveAt {F : X → Bool} {i : Fin 10} (un : Unate F i)
    {a b : ℕ} (off : ∀ j : Fin 10, j ≠ i → row a j = row b j)
    (ha : row a i = false) (hb : row b i = true)
    (va : F (row a) = false) (vb : F (row b) = true) :
    ∀ (c d : ℕ), (∀ j : Fin 10, j ≠ i → row c j = row d j) →
      row c i = false → row d i = true → F (row c) = true → F (row d) = true := by
  obtain ⟨sg, om⟩ := un
  have h := om (row a) (row b) off ha hb
  rw [va, vb] at h
  have pos : sg = true := (by decide : ∀ s : Bool, Orient s false true → s = true) _ h
  subst sg
  intro c d ho hc hd
  exact om (row c) (row d) ho hc hd

lemma adjacentConflict (F : X → Bool) (ok : ∀ x, valid12 x → F x = target x)
    (un1 : Unate F 1) (un2 : Unate F 2)
    (b12 : Forbid F 1 2) (b03 : Forbid F 0 3) : False := by
  have v16 : F (row 16) = false := (ok _ (by decide)).trans (by decide)
  have v17 : F (row 17) = true := (ok _ (by decide)).trans (by decide)
  have v24 : F (row 24) = true := (ok _ (by decide)).trans (by decide)
  have v25 : F (row 25) = true := (ok _ (by decide)).trans (by decide)
  have v514 : F (row 514) = false := (ok _ (by decide)).trans (by decide)
  have v516 : F (row 516) = false := (ok _ (by decide)).trans (by decide)
  have v517 : F (row 517) = false := (ok _ (by decide)).trans (by decide)
  have v518 : F (row 518) = true := (ok _ (by decide)).trans (by decide)
  have v522 : F (row 522) = false := (ok _ (by decide)).trans (by decide)
  have v523 : F (row 523) = true := (ok _ (by decide)).trans (by decide)
  have v525 : F (row 525) = true := (ok _ (by decide)).trans (by decide)
  have v527 : F (row 527) = true := (ok _ (by decide)).trans (by decide)
  have pos1 := positiveAt un1 (a := 516) (b := 518) (by decide) (by decide) (by decide) v516 v518
  have pos2 := positiveAt un2 (a := 514) (b := 518) (by decide) (by decide) (by decide) v514 v518
  have v512 : F (row 512) = false := by
    cases h : F (row 512)
    · rfl
    · exact Bool.noConfusion ((pos1 512 514 (by decide) (by decide) (by decide) h).symm.trans v514)
  have v513 : F (row 513) = false := by
    cases h : F (row 513)
    · rfl
    · exact Bool.noConfusion ((pos2 513 517 (by decide) (by decide) (by decide) h).symm.trans v517)
  have v520 : F (row 520) = false := by
    cases h : F (row 520)
    · rfl
    · exact Bool.noConfusion ((pos1 520 522 (by decide) (by decide) (by decide) h).symm.trans v522)
  cases v521 : F (row 521)
  · apply b12 (row 512) (row 521)
    · intro u v
      cases u <;> cases v
      · rw [show pairInput 1 2 (row 512) false false = row 512 by funext t; fin_cases t <;> rfl]
        exact v512
      · rw [show pairInput 1 2 (row 512) false true = row 516 by funext t; fin_cases t <;> rfl]
        exact v516
      · rw [show pairInput 1 2 (row 512) true false = row 514 by funext t; fin_cases t <;> rfl]
        exact v514
      · rw [show pairInput 1 2 (row 512) true true = row 518 by funext t; fin_cases t <;> rfl]
        exact v518
    · intro u v
      cases u <;> cases v
      · rw [show pairInput 1 2 (row 521) false false = row 521 by funext t; fin_cases t <;> rfl]
        exact v521
      · rw [show pairInput 1 2 (row 521) false true = row 525 by funext t; fin_cases t <;> rfl]
        exact v525
      · rw [show pairInput 1 2 (row 521) true false = row 523 by funext t; fin_cases t <;> rfl]
        exact v523
      · rw [show pairInput 1 2 (row 521) true true = row 527 by funext t; fin_cases t <;> rfl]
        exact v527
  · apply b03 (row 512) (row 16)
    · intro u v
      cases u <;> cases v
      · rw [show pairInput 0 3 (row 512) false false = row 512 by funext t; fin_cases t <;> rfl]
        exact v512
      · rw [show pairInput 0 3 (row 512) false true = row 520 by funext t; fin_cases t <;> rfl]
        exact v520
      · rw [show pairInput 0 3 (row 512) true false = row 513 by funext t; fin_cases t <;> rfl]
        exact v513
      · rw [show pairInput 0 3 (row 512) true true = row 521 by funext t; fin_cases t <;> rfl]
        exact v521
    · intro u v
      cases u <;> cases v
      · rw [show pairInput 0 3 (row 16) false false = row 16 by funext t; fin_cases t <;> rfl]
        exact v16
      · rw [show pairInput 0 3 (row 16) false true = row 24 by funext t; fin_cases t <;> rfl]
        exact v24
      · rw [show pairInput 0 3 (row 16) true false = row 17 by funext t; fin_cases t <;> rfl]
        exact v17
      · rw [show pairInput 0 3 (row 16) true true = row 25 by funext t; fin_cases t <;> rfl]
        exact v25
end AdjacentSeed

namespace MoveSeed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof

def moveGate (ρ : ℕ → ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map ρ⟩

def bump (i : ℕ) : ℕ := if i < 9 then i else i + 1

def replaceWire (slot i : ℕ) : ℕ :=
  if i = 9 + slot then 9 else bump i

lemma bump_injective : Function.Injective bump := by
  intro i j h
  unfold bump at h
  split_ifs at h <;> omega

lemma bump_ne_nine (i : ℕ) : bump i ≠ 9 := by
  unfold bump
  split <;> omega

lemma replace_injective (slot : ℕ) : Function.Injective (replaceWire slot) := by
  intro i j h
  unfold replaceWire at h
  split_ifs at h
  · omega
  · exact (bump_ne_nine j h.symm).elim
  · exact (bump_ne_nine i h).elim
  · exact bump_injective h

lemma mapped_value (ρ : ℕ → ℕ) (g : Gate) (w u : List Bool)
    (same : ∀ i, w.getD i false = u.getD (ρ i) false) :
    g.op.eval (g.inputs.map fun i => w.getD i false) =
    (moveGate ρ g).op.eval ((moveGate ρ g).inputs.map fun i => u.getD i false) := by
  simp only [moveGate, List.map_map]
  apply congrArg g.op.eval
  apply List.map_congr_left
  intro i _
  exact same i

lemma mapped_run (ρ : ℕ → ℕ) (inj : Function.Injective ρ) (gs : List Gate) (w u : List Bool)
    (same : ∀ i, w.getD i false = u.getD (ρ i) false)
    (next : ∀ j, ρ (w.length + j) = u.length + j) :
    ∀ i, (wiresFrom gs w).getD i false = (wiresFrom (gs.map (moveGate ρ)) u).getD (ρ i) false := by
  induction gs generalizing w u with
  | nil => exact same
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    let v' := (moveGate ρ g).op.eval ((moveGate ρ g).inputs.map fun i => u.getD i false)
    have eq : v = v' := mapped_value ρ g w u same
    have next0 : ρ w.length = u.length := by simpa using next 0
    apply ih (w ++ [v]) (u ++ [v'])
    · intro i
      by_cases h : i = w.length
      · subst i
        rw [next0,getD_snoc_eq,getD_snoc_eq]
        exact eq
      · have h' : ρ i ≠ u.length := fun e => h (inj (e.trans next0.symm))
        rw [getD_snoc_ne _ _ _ _ h,getD_snoc_ne _ _ _ _ h']
        exact same i
    · intro j
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using next (j + 1)

lemma bump_inputs (w : List Bool) (len : w.length = 9) (y : Bool) (i : ℕ) :
    w.getD i false = (w ++ [y]).getD (bump i) false := by
  by_cases hi : i < 9
  · rw [bump, if_pos hi, List.getD_append _ _ _ _ (by omega)]
  · rw [bump, if_neg hi, List.getD_eq_default _ _ (by omega),
      List.getD_eq_default _ _ (by simp; omega)]

def padding : Gate := ⟨.not, []⟩

def withSeed (pre post : List Gate) (out : ℕ) : Circuit :=
  ⟨(pre.map (moveGate bump) ++ [padding]) ++ post.map (moveGate (replaceWire pre.length)),
    replaceWire pre.length out⟩

lemma withSeed_eval (pre post : List Gate) (g : Gate) (out : ℕ)
    (w : List Bool) (len : w.length = 9) (y : Bool)
    (hy : y = g.op.eval (g.inputs.map fun i => (wiresFrom pre w).getD i false)) :
    (Circuit.mk ((pre ++ [g]) ++ post) out).eval w =
    (withSeed pre post out).eval (w ++ [y]) := by
  let a := wiresFrom pre w
  let b := wiresFrom (pre.map (moveGate bump)) (w ++ [y])
  have la : a.length = 9 + pre.length := by simp [a,length_wiresFrom,len]
  have lb : b.length = 10 + pre.length := by simp [b,length_wiresFrom,len]
  have eq (i : ℕ) : a.getD i false = b.getD (bump i) false := by
    apply mapped_run bump bump_injective _ _ _ (bump_inputs w len y)
    intro j
    simp [bump,len] <;> omega
  have ey : b.getD 9 false = y := by
    rw [show b.getD 9 false = (w ++ [y]).getD 9 false from
      getD_wiresFrom _ _ _ (by simp [len])]
    rw [←len,getD_snoc_eq]
  have same (i : ℕ) : (a ++ [y]).getD i false =
      (b ++ [true]).getD (replaceWire pre.length i) false := by
    by_cases hi : i = 9 + pre.length
    · rw [replaceWire,if_pos hi,hi,←la,getD_snoc_eq,
        List.getD_append _ _ _ _ (by omega),ey]
    · have hne : bump i ≠ b.length := by
        unfold bump
        split <;> omega
      rw [replaceWire,if_neg hi,getD_snoc_ne _ _ _ _ (by omega),getD_snoc_ne _ _ _ _ hne]
      exact eq i
  have bound : ∀ j, replaceWire pre.length ((a ++ [y]).length + j) =
      (b ++ [true]).length + j := by
    intro j
    simp only [List.length_append,List.length_singleton,la,lb,replaceWire,bump]
    split_ifs <;> omega
  change (wiresFrom ((pre ++ [g]) ++ post) w).getD out false =
    (wiresFrom ((pre.map (moveGate bump) ++ [padding]) ++ post.map (moveGate (replaceWire pre.length)))
      (w ++ [y])).getD (replaceWire pre.length out) false
  simp only [wiresFrom_append]
  change (wiresFrom post (a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)])).getD out false =
    (wiresFrom (post.map (moveGate (replaceWire pre.length))) (b ++ [true])).getD _ false
  rw [←hy]
  exact mapped_run _ (replace_injective _) _ _ _ same bound out

lemma moved_ok (ρ : ℕ → ℕ) (g : Gate) (h : Ok g) : Ok (moveGate ρ g) := by
  simpa [Ok,moveGate] using h

lemma withSeed_fan (pre post : List Gate) (g : Gate) (out : ℕ)
    (h : FanInTwo ⟨(pre ++ [g]) ++ post,out⟩) : FanInTwo (withSeed pre post out) := by
  intro q hq
  change q ∈ (pre.map (moveGate bump) ++ [padding]) ++ post.map (moveGate (replaceWire pre.length)) at hq
  rcases List.mem_append.mp hq with hq | hq
  · rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
      exact moved_ok _ _ (h a (by simp [ha]))
    · obtain rfl : q = padding := List.mem_singleton.mp hq
      simp [padding]
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
    exact moved_ok _ _ (h a (by simp [ha]))

lemma moved_count (ρ : ℕ → ℕ) (gs : List Gate) :
    nonNotCount (gs.map (moveGate ρ)) = nonNotCount gs := by
  simp [nonNotCount,Function.comp_def,moveGate]


lemma withSeed_count (pre post : List Gate) (g : Gate) (out : ℕ)
    (hg : g.op ≠ .not) : nonNotCount (withSeed pre post out).gates + 1 =
      nonNotCount ((pre ++ [g]) ++ post) := by
  have hn : isNotGate g.op = false := by cases e : g.op <;> simp_all [isNotGate]
  have append (a b : List Gate) : nonNotCount (a ++ b) = nonNotCount a + nonNotCount b := by simp [nonNotCount]
  have pad : nonNotCount [padding] = 0 := rfl
  have singleton : nonNotCount [g] = 1 := by simp [nonNotCount,List.countP_cons,hn]
  change nonNotCount ((pre.map (moveGate bump) ++ [padding]) ++ post.map (moveGate (replaceWire pre.length))) + 1 = _
  simp only [append,moved_count,pad,singleton] <;> omega

end MoveSeed

namespace SeedRanks

open PetersenScratch
open Finite2770

abbrev Seed := Fin 9 × Fin 9 × Fin 3
abbrev Rule := Fin 10 × Fin 10 × Fin 10 × ℕ × ℕ × ℕ

def seedValue (seed : Seed) (x : Fin 9 → Bool) : Bool :=
  let a := x seed.1
  let b := x seed.2.1
  if seed.2.2 = 0 then a && b else if seed.2.2 = 1 then a || b else (!a) && b

def valid (seed : Seed) (x : X) : Bool := x 9 == seedValue seed (fun j => x j.castSucc)

def pairOK (s : Seed) (i j : Fin 10) (a o : ℕ) : Prop :=
  ∀ u v : Bool,
    let x := pairInput i j (row a) u v
    let y := pairInput i j (row o) u v
    valid s x = true ∧ target x = (u && v) ∧ valid s y = true ∧ target y = (u || v)

def cube (s : Seed) (i j k : Fin 10) (a b c : ℕ) : Prop :=
  let hi m := Function.update (row m) k true
  (∀ v, v ≠ i → v ≠ j → row a v = row b v ∧ row b v = row c v) ∧
  valid s (row a) = true ∧ valid s (row b) = true ∧ valid s (hi a) = true ∧
  valid s (hi b) = true ∧ valid s (hi c) = true ∧ target (row a) ≠ target (row b) ∧
  target (hi a) ≠ target (hi c) ∧ target (hi b) ≠ target (hi c)

def Cut (s : Seed) (label : Fin 10 → Fin 4) (t : Fin 4) : Prop :=
  ∃ code : X → Bool,
    (∀ x y, (∀ i, label i ≤ t → x i = y i) → code x = code y) ∧
    (∀ x y, valid s x = true → valid s y = true → (∀ i, label i ≠ t → x i = y i) →
      code x = code y → target x = target y)
lemma cubeBound (s : Seed) (label : Fin 10 → Fin 4) (cut : ∀ t, t < 3 → Cut s label t)
    (i j k : Fin 10) (a b c : ℕ) (hw : cube s i j k a b c) :
    label i = label j → label k ≤ label i := by
  intro hh
  by_contra hle
  have hlt : label i < label k := lt_of_not_ge hle
  have h3 : label i < 3 := by omega
  obtain ⟨code, low, high⟩ := cut (label i) h3
  obtain ⟨same, va, vb, vha, vhb, vhc, nab, nac, nbc⟩ := hw
  let hi (m : ℕ) := Function.update (row m) k true
  have aux (m : ℕ) : code (hi m) = code (row m) := by
    apply low
    intro u hu
    have hne : u ≠ k := by
      rintro rfl
      exact (not_le_of_gt hlt) hu
    exact Function.update_of_ne hne _ _
  have off {u} (h : label u ≠ label i) : u ≠ i ∧ u ≠ j := by
    constructor
    · exact fun he => h (he ▸ rfl)
    · exact fun he => h (he ▸ hh.symm)
  have hab : code (row a) ≠ code (row b) := fun e =>
    nab (high _ _ va vb (fun u hu => (same u (off hu).1 (off hu).2).1) e)
  have lift {m n : ℕ} (h : ∀ u, label u ≠ label i → row m u = row n u) :
      ∀ u, label u ≠ label i → hi m u = hi n u := by
    intro u hu
    by_cases eq : u = k
    · subst u; simp [hi]
    · simpa [hi, Function.update_of_ne eq] using h u hu
  have hac : code (row a) ≠ code (row c) := fun e =>
    nac (high _ _ vha vhc (lift (fun u hu => ((same u (off hu).1 (off hu).2).1).trans
      (same u (off hu).1 (off hu).2).2)) ((aux a).trans (e.trans (aux c).symm)))
  have hbc : code (row b) ≠ code (row c) := fun e =>
    nbc (high _ _ vhb vhc (lift (fun u hu => (same u (off hu).1 (off hu).2).2))
      ((aux b).trans (e.trans (aux c).symm)))
  cases ha : code (row a) <;> cases hb : code (row b) <;> cases hc : code (row c) <;> simp_all

def ruleOK (s : Seed) : Rule → Bool
  | (i,j,k,a,b,c) => if k = 9 then
      letI : Decidable (pairOK s i j a b) := by unfold pairOK; infer_instance
      decide (pairOK s i j a b)
    else
      letI : Decidable (cube s i j k a b c) := by unfold cube; infer_instance
      decide (cube s i j k a b c)

def Holds (label : Fin 10 → Fin 4) : Rule → Prop
  | (i,j,k,_,_,_) => if k = 9 then label i ≠ label j else label i = label j → label k ≤ label i

lemma rule_sound {s : Seed} (F : X → Bool) (ok : ∀ x, valid s x = true → F x = target x)
    (label : Fin 10 → Fin 4) (clash : ∀ i j, label i = label j → Forbid F i j)
    (cut : ∀ t, t < 3 → Cut s label t) (r : Rule) (good : ruleOK s r = true) : Holds label r := by
  rcases r with ⟨i,j,k,a,b,c⟩
  by_cases hk : k = 9
  · simp only [Holds,hk,if_true]
    intro same
    letI : Decidable (pairOK s i j a b) := by unfold pairOK; infer_instance
    have h : pairOK s i j a b := of_decide_eq_true (by simpa only [ruleOK,hk,if_true] using good)
    apply clash i j same (row a) (row b)
    · intro u v
      exact (ok _ (h u v).1).trans (h u v).2.1
    · intro u v
      exact (ok _ (h u v).2.2.1).trans (h u v).2.2.2
  · simp only [Holds,hk,if_false]
    apply cubeBound s label cut i j k a b c
    letI : Decidable (cube s i j k a b c) := by unfold cube; infer_instance
    exact of_decide_eq_true (by simpa only [ruleOK,hk,if_false] using good)

def violation (xs : List (Fin 4)) : Rule → Bool
  | (i,j,k,_,_,_) =>
    decide (i.val < xs.length) && decide (j.val < xs.length) &&
    (xs.getD i.val 0 == xs.getD j.val 0) &&
    (k == 9 || (decide (k.val < xs.length) && decide (xs.getD i.val 0 < xs.getD k.val 0)))

def Matches (xs : List (Fin 4)) (label : Fin 10 → Fin 4) : Prop :=
  ∀ i : Fin 10, i.val < xs.length → xs.getD i.val 0 = label i

lemma violation_false {xs : List (Fin 4)} {label : Fin 10 → Fin 4} (hm : Matches xs label)
    (r : Rule) (h : Holds label r) : violation xs r = false := by
  rcases r with ⟨i,j,k,a,b,c⟩
  cases e : violation xs (i,j,k,a,b,c)
  · rfl
  · exfalso
    simp only [violation,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,Bool.or_eq_true] at e
    obtain ⟨⟨⟨hi,hj⟩,eq⟩,hk⟩ := e
    rw [hm _ hi,hm _ hj] at eq
    rcases hk with hk | ⟨hk,lt⟩
    · simpa [Holds,hk,eq] using h
    · rw [hm _ hi,hm _ hk] at lt
      by_cases hz : k = 9
      · simpa [Holds,hz,eq] using h
      · exact (not_lt_of_ge ((show label i = label j → label k ≤ label i by
          simpa only [Holds,if_neg hz] using h) eq)) lt

def enumerate (rules : List Rule) (endTest : List (Fin 4) → Bool) : ℕ → List (Fin 4) → Bool
  | 0, xs => rules.any (violation xs) || endTest xs
  | n + 1, xs => rules.any (violation xs) ||
    (enumerate rules endTest n (xs ++ [0]) && enumerate rules endTest n (xs ++ [1]) &&
     enumerate rules endTest n (xs ++ [2]) && enumerate rules endTest n (xs ++ [3]))

lemma enumerate_sound (rules : List Rule) (endTest : List (Fin 4) → Bool)
    (label : Fin 10 → Fin 4) (good : ∀ r ∈ rules, Holds label r)
    (n : ℕ) (xs : List (Fin 4)) (len : xs.length + n = 9)
    (hm : Matches xs label) (checked : enumerate rules endTest n xs = true) :
    ∃ full, full.length = 9 ∧ Matches full label ∧ endTest full = true := by
  have noViolation (ys : List (Fin 4)) (matched : Matches ys label) : rules.any (violation ys) = false := by
    apply List.any_eq_false.mpr
    intro r hr
    simp [violation_false matched r (good r hr)]
  induction n generalizing xs with
  | zero =>
    exact ⟨xs,by omega,hm,by simpa [enumerate,noViolation xs hm] using checked⟩
  | succ n ih =>
    have hl : xs.length < 10 := by omega
    let idx : Fin 10 := ⟨xs.length,hl⟩
    have hm' : Matches (xs ++ [label idx]) label := by
      intro i hi
      by_cases he : i.val = xs.length
      · have eq : i = idx := Fin.ext he
        rw [he,CircuitProof.getD_snoc_eq,eq]
      · rw [CircuitProof.getD_snoc_ne _ _ _ _ he]
        apply hm
        simp at hi
        omega
    have hchild := checked
    simp only [enumerate,noViolation xs hm,Bool.false_or,Bool.and_eq_true] at hchild
    apply ih (xs ++ [label idx]) (by simp; omega) hm'
    have flags : label idx = 0 ∨ label idx = 1 ∨ label idx = 2 ∨ label idx = 3 := (by decide : ∀ a : Fin 4, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3) _
    rcases flags with hval | hval | hval | hval <;> rw [hval]
    · exact hchild.1.1.1
    · exact hchild.1.1.2
    · exact hchild.1.2
    · exact hchild.2

def lastFour (xs : List (Fin 4)) : Bool :=
  xs.getD 0 0 == 3 && xs.getD 1 0 == 3 && xs.getD 2 0 == 3 && xs.getD 3 0 == 3

def witnesses : Fin 19 → List Rule
  | 0 => [(0,4,9,0,40,0),(0,5,9,0,144,0),(1,2,9,0,72,0),(1,6,9,0,260,0),(2,3,9,0,18,0),(2,7,9,0,34,0),(3,4,9,0,5,0),(3,8,9,0,36,0),(5,8,9,0,9,0),(6,8,9,0,10,0),(5,7,9,0,5,0),(2,4,0,132,144,128),(0,7,2,17,144,16),(5,6,7,34,66,2),(1,7,5,66,192,64),(0,8,4,65,320,64),(4,7,0,20,132,4),(0,6,4,257,320,256),(4,5,0,24,40,8),(4,8,6,17,257,1),(0,3,4,5,12,4),(3,5,8,9,33,1),(3,6,8,10,66,2),(4,6,3,18,66,2),(1,4,3,66,80,64),(3,7,5,24,144,16),(7,8,5,132,260,4),(2,8,3,6,258,2),(2,5,7,5,33,1),(4,8,3,17,257,1),(0,2,4,129,132,128),(1,3,2,18,24,16),(1,5,2,258,288,256)]
  | 1 => [(0,4,9,0,40,0),(0,5,9,0,144,0),(2,3,9,0,144,0),(2,7,9,0,40,0),(3,4,9,0,5,0),(3,8,9,0,36,0),(5,8,9,0,9,0),(5,7,9,0,5,0),(6,8,9,0,522,0),(0,7,2,17,144,16),(2,4,0,132,144,128),(3,6,4,522,578,514),(4,7,3,48,160,32),(4,5,7,24,40,8),(3,5,7,24,48,16),(2,5,7,5,33,1),(3,7,5,24,144,16),(7,8,5,132,260,4),(2,8,3,36,288,32),(0,3,2,33,40,32),(4,8,3,17,257,1),(0,8,4,65,320,64),(5,6,8,33,65,1),(6,7,8,68,132,4),(0,6,4,257,320,256),(2,6,7,260,320,256),(4,6,0,272,320,256),(4,7,0,20,132,4),(4,8,0,80,320,64),(0,7,4,5,132,4),(3,6,8,12,68,4)]
  | 2 => [(0,1,9,0,80,0),(0,4,9,0,10,0),(0,5,9,0,130,0),(1,2,9,0,72,0),(1,6,9,0,257,0),(2,3,9,0,18,0),(3,4,9,0,257,0),(2,7,9,0,34,0),(5,7,9,0,260,0),(3,8,9,0,36,0),(5,8,9,0,9,0),(6,8,9,0,10,0),(0,6,1,17,80,16),(1,4,0,10,24,8),(0,8,1,9,264,8),(1,3,0,258,264,256),(0,3,4,3,10,2),(2,4,3,6,18,2),(0,2,4,129,132,128),(1,8,2,34,288,32),(5,6,8,33,65,1),(4,8,6,17,257,1),(1,5,8,6,36,4),(2,8,5,6,258,2),(4,5,0,24,40,8),(3,5,8,9,33,1),(2,5,1,260,288,256),(7,8,5,132,260,4),(0,8,4,65,320,64),(0,7,5,3,130,2),(0,2,1,9,12,8),(3,7,2,24,144,16),(1,5,0,66,96,64)]
  | 3 => [(0,1,9,0,80,0),(0,4,9,0,10,0),(0,5,9,0,130,0),(1,6,9,0,257,0),(2,3,9,1,385,0),(3,4,9,0,5,0),(3,8,9,0,48,0),(5,8,9,0,9,0),(6,8,9,0,10,0),(5,7,9,0,5,0),(1,4,0,10,24,8),(0,3,1,257,264,256),(0,8,1,9,264,8),(3,5,8,9,33,1),(1,8,3,3,257,1),(4,8,3,17,257,1),(1,3,0,258,264,256),(0,6,4,257,320,256),(3,6,8,10,66,2),(4,6,3,18,66,2),(1,5,6,130,160,128),(4,5,0,24,40,8),(5,6,8,33,65,1),(7,8,5,136,264,8),(0,7,5,3,130,2),(1,7,5,66,192,64),(3,7,4,40,160,32),(4,7,5,24,136,8),(3,5,4,136,160,128),(1,5,0,66,96,64),(0,8,3,3,258,2)]
  | 4 => [(0,1,9,0,20,0),(0,5,9,0,130,0),(1,2,9,0,72,0),(1,6,9,0,257,0),(2,3,9,0,18,0),(2,7,9,0,34,0),(5,7,9,0,5,0),(3,8,9,0,36,0),(6,8,9,0,10,0),(5,8,9,0,65,0),(0,2,1,17,20,16),(1,3,2,18,24,16),(1,8,2,34,288,32),(2,5,1,260,288,256),(1,5,0,6,36,4),(0,7,5,3,130,2),(1,7,5,66,192,64),(3,5,7,24,48,16),(0,3,1,257,264,256),(2,8,3,6,258,2),(0,8,5,3,258,2),(5,6,8,33,65,1),(7,8,5,132,260,4),(3,6,8,10,66,2),(2,6,7,260,320,256),(0,6,1,17,80,16),(1,8,6,3,257,1),(2,5,7,5,33,1),(3,5,8,12,36,4),(0,7,2,17,144,16)]
  | 5 => [(0,1,9,520,616,0),(0,5,9,520,650,0),(1,2,9,0,192,0),(1,6,9,0,260,0),(2,3,9,513,897,0),(2,7,9,0,34,0),(5,7,9,0,260,0),(3,8,9,513,581,0),(6,8,9,0,34,0),(5,8,9,0,192,0),(0,2,1,521,524,520),(1,3,2,515,521,513),(1,8,0,522,776,520),(2,5,1,260,288,256),(0,7,5,523,650,522),(1,5,0,586,616,584),(1,7,2,34,160,32),(2,8,7,68,320,64),(3,6,8,525,581,517),(2,6,7,260,320,256),(0,8,5,521,776,520),(7,8,6,132,260,4),(5,6,8,34,66,2),(0,6,1,553,616,552),(6,7,2,320,384,256),(1,8,2,34,288,32),(2,5,0,524,552,520),(2,6,1,132,192,128)]
  | 6 => [(0,1,9,0,20,0),(0,5,9,0,130,0),(1,2,9,0,9,0),(1,6,9,0,257,0),(2,3,9,1,385,0),(2,7,9,0,34,0),(5,7,9,0,5,0),(3,8,9,1,69,0),(6,8,9,0,34,0),(5,8,9,0,9,0),(0,2,1,17,20,16),(1,3,2,3,9,1),(1,8,2,34,288,32),(2,5,1,260,288,256),(1,5,0,6,36,4),(0,7,5,3,130,2),(1,7,5,66,192,64),(5,6,7,34,66,2),(0,6,1,17,80,16),(2,6,1,132,192,128),(2,8,6,132,384,128),(6,7,2,320,384,256),(7,8,6,132,260,4),(0,8,6,17,272,16),(3,5,8,9,33,1),(3,6,8,13,69,5),(3,7,2,265,385,257),(1,8,3,3,257,1),(2,5,3,5,33,1),(2,6,7,260,320,256),(0,8,5,3,258,2),(1,7,2,3,129,1)]
  | 7 => [(0,1,9,0,36,0),(0,5,9,0,130,0),(1,2,9,0,9,0),(1,6,9,0,257,0),(2,3,9,0,18,0),(2,7,9,0,34,0),(5,7,9,0,5,0),(3,8,9,0,36,0),(6,8,9,0,10,0),(5,8,9,0,9,0),(0,2,1,9,12,8),(1,3,0,258,264,256),(1,8,0,10,264,8),(0,7,5,3,130,2),(3,6,8,10,66,2),(0,8,3,3,258,2),(2,6,8,132,192,128),(2,8,3,6,258,2),(7,8,6,132,260,4),(0,6,1,33,96,32),(0,3,8,3,10,2),(1,7,2,3,129,1),(1,5,0,6,36,4),(2,5,7,5,33,1),(3,5,2,9,33,1),(3,7,2,24,144,16),(1,3,2,3,9,1)]
  | 8 => [(1,2,9,0,72,0),(1,6,9,0,260,0),(2,3,9,0,258,0),(2,7,9,0,34,0),(3,8,9,0,36,0),(6,8,9,0,10,0),(5,7,9,0,260,0),(5,8,9,0,136,0),(1,7,2,34,160,32),(2,5,1,260,288,256),(2,8,1,36,288,32),(3,5,8,12,36,4),(1,8,5,6,260,4),(7,8,5,132,260,4),(1,5,2,258,288,256),(2,6,7,260,320,256),(3,7,2,40,160,32),(1,3,2,66,72,64),(5,6,7,34,66,2),(3,6,8,10,66,2),(2,8,3,6,258,2),(1,7,6,34,160,32),(6,7,1,96,160,32),(1,5,6,130,160,128),(2,5,3,517,545,513),(2,6,1,12,72,8),(1,8,3,515,769,513),(3,7,5,536,656,528)]
  | 9 => [(0,1,9,0,36,0),(0,5,9,0,130,0),(1,2,9,0,9,0),(1,6,9,0,257,0),(2,3,9,0,258,0),(2,7,9,0,34,0),(5,7,9,0,5,0),(3,8,9,0,36,0),(6,8,9,0,10,0),(5,8,9,0,9,0),(0,2,1,9,12,8),(1,3,0,258,264,256),(1,8,0,10,264,8),(0,7,5,3,130,2),(3,6,8,10,66,2),(0,8,3,3,258,2),(2,6,8,132,192,128),(2,8,3,6,258,2),(7,8,6,132,260,4),(0,6,1,33,96,32),(0,3,8,3,10,2),(1,7,2,3,129,1),(1,5,0,6,36,4),(2,5,7,5,33,1),(3,5,2,9,33,1),(3,7,2,40,160,32),(1,3,2,3,9,1)]
  | 10 => [(0,1,9,0,20,0),(0,4,9,0,10,0),(0,5,9,0,130,0),(1,2,9,0,9,0),(1,6,9,0,260,0),(2,3,9,0,18,0),(3,4,9,0,5,0),(2,7,9,0,34,0),(5,7,9,0,5,0),(3,8,9,0,36,0),(5,8,9,0,9,0),(6,8,9,0,10,0),(0,6,1,17,80,16),(1,4,0,6,20,4),(0,8,1,9,264,8),(1,3,0,258,264,256),(0,3,4,3,10,2),(2,4,0,132,144,128),(0,2,4,129,132,128),(1,8,2,34,288,32),(4,8,3,17,257,1),(5,6,8,34,66,2),(1,5,2,258,288,256),(4,6,3,18,66,2),(3,6,4,10,66,2),(4,5,3,144,160,128),(3,5,4,136,160,128),(2,8,5,6,258,2),(1,7,6,34,160,32),(0,7,2,17,144,16),(1,8,3,3,257,1),(1,3,2,3,9,1),(0,8,5,3,258,2)]
  | 11 => [(0,4,9,576,616,0),(0,5,9,576,720,0),(1,2,9,0,521,0),(2,3,9,0,18,0),(2,7,9,0,34,0),(3,4,9,0,517,0),(3,8,9,0,36,0),(5,8,9,0,136,0),(5,7,9,0,260,0),(0,7,2,593,720,592),(2,4,0,708,720,704),(1,3,4,578,584,576),(4,7,3,48,160,32),(4,5,7,24,40,8),(3,5,7,24,48,16),(2,5,7,6,34,2),(3,7,5,24,144,16),(7,8,5,132,260,4),(2,8,3,6,258,2),(0,3,2,609,616,608),(4,8,3,48,288,32),(0,8,4,577,832,576),(1,5,8,6,36,4),(1,7,2,34,160,32),(0,2,4,705,708,704),(3,5,8,12,36,4),(3,7,2,24,144,16),(0,3,4,581,588,580),(2,8,1,36,288,32),(4,7,0,596,708,580),(1,3,2,18,24,16)]
  | 12 => [(0,1,9,0,20,0),(0,4,9,0,10,0),(0,5,9,0,130,0),(1,2,9,0,9,0),(2,3,9,0,18,0),(3,4,9,0,5,0),(2,7,9,0,34,0),(5,7,9,0,5,0),(3,8,9,0,36,0),(5,8,9,0,9,0),(0,7,2,17,144,16),(2,4,0,132,144,128),(0,2,1,9,12,8),(1,4,0,6,20,4),(1,3,2,3,9,1),(0,3,4,3,10,2),(2,5,3,5,33,1),(1,7,2,3,129,1),(2,8,3,6,258,2),(0,8,1,9,264,8),(1,5,0,6,36,4),(3,7,2,24,144,16),(3,5,8,9,33,1),(4,7,3,48,160,32),(4,5,7,24,40,8),(0,7,5,3,130,2),(1,8,3,3,257,1),(2,5,1,260,288,256),(2,4,3,5,17,1),(1,3,0,258,264,256)]
  | 13 => [(0,4,9,0,40,0),(3,4,9,0,257,0),(0,5,9,0,144,0),(3,8,9,0,48,0),(5,8,9,0,9,0),(5,7,9,0,517,0),(6,8,9,0,522,0),(0,7,4,517,644,516),(5,6,7,546,578,514),(7,8,5,136,264,8),(4,5,7,24,40,8),(3,5,8,9,33,1),(0,8,5,9,264,8),(4,8,0,80,320,64),(0,3,8,515,522,514),(3,7,4,40,160,32),(4,7,3,48,160,32),(4,6,0,272,320,256),(0,6,4,257,320,256),(3,6,8,24,80,16),(6,7,5,578,642,514),(1,8,6,518,772,516),(2,8,3,518,770,514),(1,5,0,518,548,516),(1,4,0,518,532,516),(4,8,3,17,257,1),(0,3,4,33,40,32),(0,8,6,17,272,16),(3,5,7,24,48,16),(0,7,5,17,144,16),(2,4,3,518,530,514),(5,6,8,33,65,1),(2,5,1,772,804,768),(4,5,0,24,40,8)]
  | 14 => [(1,2,9,0,72,0),(1,6,9,0,260,0),(2,3,9,0,18,0),(2,7,9,0,34,0),(3,8,9,0,36,0),(6,8,9,0,10,0),(5,7,9,0,260,0),(5,8,9,0,136,0),(1,7,2,34,160,32),(2,5,1,260,288,256),(2,8,1,36,288,32),(3,5,8,12,36,4),(1,8,5,6,260,4),(7,8,5,132,260,4),(1,5,2,258,288,256),(2,6,7,260,320,256),(3,7,2,24,144,16),(1,3,2,18,24,16),(5,6,7,34,66,2),(3,6,8,10,66,2),(2,8,3,6,258,2),(1,7,6,34,160,32),(6,7,1,96,160,32),(1,5,6,130,160,128),(2,5,3,517,545,513),(2,6,1,12,72,8),(1,8,3,515,769,513),(3,7,5,24,144,16)]
  | 15 => [(0,4,9,0,40,0),(0,5,9,0,144,0),(1,2,9,16,208,0),(1,6,9,16,276,0),(2,3,9,0,18,0),(2,7,9,0,40,0),(3,4,9,0,5,0),(3,8,9,0,36,0),(5,8,9,0,9,0),(6,8,9,0,50,0),(5,7,9,0,5,0),(2,4,0,132,144,128),(0,7,2,17,144,16),(5,6,7,50,82,18),(1,7,5,82,208,80),(0,8,4,65,320,64),(4,7,0,20,132,4),(0,6,4,257,320,256),(1,4,0,20,22,4),(0,3,4,5,12,4),(4,5,0,24,40,8),(3,5,7,24,48,16),(4,8,3,17,257,1),(3,7,4,40,160,32),(2,5,7,5,33,1),(7,8,5,132,260,4),(2,8,3,36,288,32),(0,2,4,129,132,128),(3,5,8,9,33,1),(3,7,2,24,144,16),(0,7,4,5,132,4)]
  | 16 => [(0,1,9,0,20,0),(0,4,9,0,10,0),(0,5,9,0,130,0),(1,2,9,0,9,0),(1,6,9,0,257,0),(2,3,9,0,18,0),(3,4,9,0,5,0),(2,7,9,0,34,0),(5,7,9,0,5,0),(3,8,9,0,36,0),(5,8,9,0,9,0),(6,8,9,0,10,0),(0,6,1,33,96,32),(1,4,0,6,20,4),(0,8,1,9,264,8),(1,3,0,258,264,256),(0,3,4,3,10,2),(2,4,0,132,144,128),(0,2,4,129,132,128),(1,8,2,34,288,32),(4,8,3,17,257,1),(5,6,8,33,65,1),(1,5,2,258,288,256),(4,6,3,18,66,2),(3,6,8,10,66,2),(2,8,6,132,384,128),(3,5,4,136,160,128),(1,8,3,3,257,1),(0,8,5,3,258,2),(1,3,2,3,9,1),(0,3,1,257,264,256)]
  | 17 => [(0,1,9,0,36,0),(0,4,9,576,616,0),(0,5,9,0,130,0),(1,2,9,0,9,0),(1,6,9,528,788,0),(2,3,9,0,258,0),(3,4,9,576,581,0),(2,7,9,0,34,0),(5,7,9,0,5,0),(3,8,9,0,36,0),(5,8,9,0,9,0),(6,8,9,528,562,0),(0,6,1,529,592,528),(1,4,0,578,592,576),(0,8,1,9,264,8),(1,3,0,258,264,256),(0,3,4,581,588,580),(2,4,0,708,720,704),(0,2,4,705,708,704),(1,8,2,34,288,32),(4,8,3,592,832,576),(5,6,8,562,594,530),(1,5,2,258,288,256),(2,8,5,6,258,2),(4,5,3,720,736,704),(3,5,8,9,33,1),(2,5,1,260,288,256),(0,8,4,577,832,576),(7,8,5,132,260,4),(0,7,2,529,656,528),(3,6,8,536,592,528),(0,2,1,9,12,8),(1,3,2,3,9,1)]
  | _ => [(0,1,9,0,20,0),(0,4,9,0,10,0),(0,5,9,0,130,0),(1,2,9,0,9,0),(1,6,9,16,276,0),(2,3,9,0,18,0),(3,4,9,0,5,0),(2,7,9,0,34,0),(5,7,9,0,5,0),(3,8,9,0,36,0),(5,8,9,0,9,0),(6,8,9,16,50,0),(0,6,1,17,80,16),(1,4,0,6,20,4),(0,8,1,9,264,8),(1,3,0,258,264,256),(0,3,4,3,10,2),(2,4,0,132,144,128),(0,2,4,129,132,128),(1,8,2,34,288,32),(4,8,3,17,257,1),(5,6,8,50,82,18),(1,5,2,258,288,256),(4,6,3,18,82,2),(3,6,8,24,80,16),(2,8,6,148,400,144),(3,5,4,136,160,128),(1,8,3,3,257,1),(0,8,5,3,258,2),(1,3,2,3,9,1),(0,3,1,257,264,256)]

def representative : Fin 19 → Seed
  | 0 => (0,1,0)
  | 1 => (0,1,2)
  | 2 => (0,2,0)
  | 3 => (0,2,2)
  | 4 => (0,3,0)
  | 5 => (0,3,1)
  | 6 => (0,3,2)
  | 7 => (0,4,0)
  | 8 => (0,4,1)
  | 9 => (0,4,2)
  | 10 => (0,6,0)
  | 11 => (0,6,1)
  | 12 => (0,6,2)
  | 13 => (1,2,1)
  | 14 => (4,0,2)
  | 15 => (4,1,2)
  | 16 => (4,6,0)
  | 17 => (4,6,1)
  | _ => (4,6,2)


def position (q : Fin 19) (v : Fin 10) : Fin 10 := (![![0,8,6,2,1,4,7,5,3,9],![6,8,0,3,5,2,7,1,4,9],![0,1,4,3,2,5,7,8,6,9],![0,1,8,3,2,5,6,7,4,9],![0,1,2,5,8,3,7,4,6,9],![0,1,2,7,8,3,6,4,5,9],![0,1,2,7,8,3,5,4,6,9],![0,1,2,3,8,7,5,6,4,9],![7,5,0,1,8,3,6,4,2,9],![0,1,2,3,8,7,5,6,4,9],![0,1,3,4,2,6,7,8,5,9],![0,7,3,2,1,5,8,4,6,9],![0,1,2,4,3,6,8,5,7,9],![0,7,8,3,4,1,6,5,2,9],![7,5,0,1,8,3,6,4,2,9],![0,7,6,2,1,4,8,5,3,9],![0,1,4,3,2,7,6,8,5,9],![0,1,2,4,3,6,7,8,5,9],![0,1,4,3,2,7,6,8,5,9]] q) v

def vertex (q : Fin 19) (p : Fin 10) : Fin 10 := (![![0,4,3,8,5,7,2,6,1,9],![2,7,5,3,8,4,0,6,1,9],![0,1,4,3,2,5,8,6,7,9],![0,1,4,3,8,5,6,7,2,9],![0,1,2,5,7,3,8,6,4,9],![0,1,2,5,7,8,6,3,4,9],![0,1,2,5,7,6,8,3,4,9],![0,1,2,3,8,6,7,5,4,9],![2,3,8,5,7,1,6,0,4,9],![0,1,2,3,8,6,7,5,4,9],![0,1,4,2,3,8,5,6,7,9],![0,4,3,2,7,5,8,1,6,9],![0,1,2,4,3,7,5,8,6,9],![0,5,8,3,4,7,6,1,2,9],![2,3,8,5,7,1,6,0,4,9],![0,4,3,8,5,7,2,1,6,9],![0,1,4,3,2,8,6,5,7,9],![0,1,2,4,3,8,5,6,7,9],![0,1,4,3,2,8,6,5,7,9]] q) p

lemma order_ok : ∀ (q : Fin 19) (v : Fin 10), vertex q (position q v) = v ∧
    (position q v = 9 ↔ v = 9) := by decide +kernel

def inOrder (q : Fin 19) : Rule → Rule
  | (i,j,k,a,b,c) => (position q i,position q j,position q k,a,b,c)

def fastRules (q : Fin 19) := (witnesses q).map (inOrder q)

lemma holds_inOrder (q : Fin 19) (label : Fin 10 → Fin 4) (r : Rule)
    (h : Holds label r) : Holds (fun p => label (vertex q p)) (inOrder q r) := by
  rcases r with ⟨i,j,k,a,b,c⟩
  simp only [inOrder,Holds,(order_ok q k).2,(order_ok q i).1,(order_ok q j).1,
    (order_ok q k).1] at h ⊢
  exact h

def lastFast (q : Fin 19) (xs : List (Fin 4)) : Bool :=
  xs.getD (position q 0).val 0 == 3 && xs.getD (position q 1).val 0 == 3 &&
  xs.getD (position q 2).val 0 == 3 && xs.getD (position q 3).val 0 == 3

def allowed (i : Fin 19) (xs : List (Fin 4)) := (i == 13) && lastFast i xs

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma geometry0 : (witnesses 0).all (ruleOK (representative 0)) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma exclude0 : enumerate (fastRules 0) (allowed 0) 9 [] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma geometry1 : (witnesses 1).all (ruleOK (representative 1)) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma exclude1 : enumerate (fastRules 1) (allowed 1) 9 [] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma geometry2 : (witnesses 2).all (ruleOK (representative 2)) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma exclude2 : enumerate (fastRules 2) (allowed 2) 9 [] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma geometry3 : (witnesses 3).all (ruleOK (representative 3)) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma exclude3 : enumerate (fastRules 3) (allowed 3) 9 [] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma geometry4 : (witnesses 4).all (ruleOK (representative 4)) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma exclude4 : enumerate (fastRules 4) (allowed 4) 9 [] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma geometry5 : (witnesses 5).all (ruleOK (representative 5)) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma exclude5 : enumerate (fastRules 5) (allowed 5) 9 [] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma geometry6 : (witnesses 6).all (ruleOK (representative 6)) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma exclude6 : enumerate (fastRules 6) (allowed 6) 9 [] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma geometry7 : (witnesses 7).all (ruleOK (representative 7)) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma exclude7 : enumerate (fastRules 7) (allowed 7) 9 [] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma geometry8 : (witnesses 8).all (ruleOK (representative 8)) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma exclude8 : enumerate (fastRules 8) (allowed 8) 9 [] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma geometry9 : (witnesses 9).all (ruleOK (representative 9)) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma exclude9 : enumerate (fastRules 9) (allowed 9) 9 [] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma geometry10 : (witnesses 10).all (ruleOK (representative 10)) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma exclude10 : enumerate (fastRules 10) (allowed 10) 9 [] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma geometry11 : (witnesses 11).all (ruleOK (representative 11)) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma exclude11 : enumerate (fastRules 11) (allowed 11) 9 [] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma geometry12 : (witnesses 12).all (ruleOK (representative 12)) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma exclude12 : enumerate (fastRules 12) (allowed 12) 9 [] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma geometry13 : (witnesses 13).all (ruleOK (representative 13)) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma exclude13 : enumerate (fastRules 13) (allowed 13) 9 [] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma geometry14 : (witnesses 14).all (ruleOK (representative 14)) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma exclude14 : enumerate (fastRules 14) (allowed 14) 9 [] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma geometry15 : (witnesses 15).all (ruleOK (representative 15)) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma exclude15 : enumerate (fastRules 15) (allowed 15) 9 [] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma geometry16 : (witnesses 16).all (ruleOK (representative 16)) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma exclude16 : enumerate (fastRules 16) (allowed 16) 9 [] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma geometry17 : (witnesses 17).all (ruleOK (representative 17)) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma exclude17 : enumerate (fastRules 17) (allowed 17) 9 [] = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma geometry18 : (witnesses 18).all (ruleOK (representative 18)) = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma exclude18 : enumerate (fastRules 18) (allowed 18) 9 [] = true := by decide +kernel

lemma geometry (i : Fin 19) : (witnesses i).all (ruleOK (representative i)) = true := by
  fin_cases i
  · exact geometry0
  · exact geometry1
  · exact geometry2
  · exact geometry3
  · exact geometry4
  · exact geometry5
  · exact geometry6
  · exact geometry7
  · exact geometry8
  · exact geometry9
  · exact geometry10
  · exact geometry11
  · exact geometry12
  · exact geometry13
  · exact geometry14
  · exact geometry15
  · exact geometry16
  · exact geometry17
  · exact geometry18

lemma excluded (i : Fin 19) : enumerate (fastRules i) (allowed i) 9 [] = true := by
  fin_cases i
  · exact exclude0
  · exact exclude1
  · exact exclude2
  · exact exclude3
  · exact exclude4
  · exact exclude5
  · exact exclude6
  · exact exclude7
  · exact exclude8
  · exact exclude9
  · exact exclude10
  · exact exclude11
  · exact exclude12
  · exact exclude13
  · exact exclude14
  · exact exclude15
  · exact exclude16
  · exact exclude17
  · exact exclude18

lemma input_read {m o : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} (L : Least m f gs o) (i : Fin m) (hd : Dep f i)
    (hoi : o ≠ i) : ∃ q, Reads gs q i := by
  by_contra hno
  have hno' : ∀ g ∈ gs, (i : ℕ) ∉ g.inputs := by
    intro g hg hi
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno ⟨q, g, hq, hi⟩
  obtain ⟨x, hx⟩ := hd
  apply hx
  rw [← L.hev, ← L.hev]
  refine agree_except i gs _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjm : j < m
  · rw [show (List.ofFn (Function.update x i (!x i))).getD j false
        = Function.update x i (!x i) ⟨j, hjm⟩ from getD_ofFn m _ false ⟨j, hjm⟩,
      show (List.ofFn x).getD j false = x ⟨j, hjm⟩ from getD_ofFn m x false ⟨j, hjm⟩]
    exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma live_from_inputs {n o : ℕ} {f : (Fin n → Bool) → Bool} {gs : List Gate}
    (least : Least n f gs o) (nc : ∃ x y, f x ≠ f y) (dep : ∀ i, Dep f i)
    (vo : o < n + gs.length) : ∀ w : Fin (n + gs.length), w ≠ ⟨o,vo⟩ → ∃ v, readEdge gs w v := by
  intro w ne
  have neq : o ≠ w.val := fun e => ne (Fin.ext e.symm)
  have read : ∃ q, Reads gs q w.val := by
    by_cases h : w.val < n
    · exact input_read least ⟨w.val,h⟩ (dep _) neq
    · let p := w.val - n
      have eq : n + p = w.val := by dsimp [p]; omega
      have hlt : p < gs.length := by have := w.isLt; omega
      obtain ⟨q,_,r⟩ := least.live nc p hlt (by simpa only [eq] using neq)
      exact ⟨q,eq ▸ r⟩
  obtain ⟨q,g,hg,hread⟩ := read
  have hq : q < gs.length := (List.getElem?_eq_some_iff.mp hg).1
  exact ⟨⟨n+q,by omega⟩,q,g,hg,rfl,hread⟩

lemma noRepresentative (idx : Fin 19) (D : Circuit) (fan : FanInTwo D)
    (budget : nonNotCount D.gates ≤ 12)
    (agree : ∀ x : X, valid (representative idx) x = true → circuitFun 10 D x = target x)
    (dep : ∀ i, Dep (circuitFun 10 D) i) : False := by
  classical
  have nc := dep_nc (dep 0)
  obtain ⟨gs, o, least, bound⟩ := least_with_budget D fan (fun _ => rfl) nc
  have outValid : o < 10 + gs.length := by
    by_contra! h
    obtain ⟨x,y,different⟩ := least.ncv nc
    exact different ((vl_beyond gs x o h).trans (vl_beyond gs y o h).symm)
  let out : Fin (10 + gs.length) := ⟨o,outValid⟩
  have live := live_from_inputs least nc dep outValid
  have branches := threeForksOfBudget least.hcl out live (bound.trans budget)
  have distinct := predecessors_nodup least nc
  obtain ⟨label,locations,last,codes⟩ := normalizedCuts least.hcl out live distinct branches
  let F : X → Bool := fun x => vl gs x out.val
  have computes (x : X) (hx : valid (representative idx) x = true) :
      F x = target x := (least.hev x).trans (agree x hx)
  have clash (i j : Fin 10) (h : label i = label j) : Forbid F i j :=
    Conflict2770.generalConflict least.hcl out live distinct (i,j) ((locations _ _).mp h)
  have cut (t : Fin 4) (_ : t < 3) : Cut (representative idx) label t := by
    obtain ⟨c,_,lo,hi⟩ := codes t
    refine ⟨c,lo,?_⟩
    intro x y hx hy off same
    exact (computes x hx).symm.trans ((hi x y off same).trans (computes y hy))
  have spec (r : Rule) (hr : r ∈ witnesses idx) : Holds label r :=
    rule_sound F computes label clash cut r (List.all_eq_true.mp (geometry idx) r hr)
  let reordered : Fin 10 → Fin 4 := fun v => label (vertex idx v)
  have fa (r : Rule) (hr : r ∈ fastRules idx) : Holds reordered r := by
    change r ∈ (witnesses idx).map (inOrder idx) at hr
    obtain ⟨v,hv,eq⟩ := List.mem_map.mp hr
    rw [←eq]
    exact holds_inOrder idx label v (spec v hv)
  obtain ⟨full,len,hm,test⟩ := enumerate_sound (fastRules idx) (allowed idx) reordered fa 9 []
    (by decide) (fun i h => by simp at h) (excluded idx)
  simp only [allowed,Bool.and_eq_true,beq_iff_eq] at test
  obtain ⟨rfl,ht⟩ := test
  have atV (v : Fin 10) (hv : (position 13 v).val < 9) :
      full.getD (position 13 v).val 0 = label v := by
    have eq := hm (position 13 v) (by omega)
    exact eq.trans (congrArg label (order_ok 13 v).1)
  have l0 : label 0 = 3 ∧ label 1 = 3 ∧ label 2 = 3 ∧ label 3 = 3 := by
    simp only [lastFast,Bool.and_eq_true,beq_iff_eq] at ht
    exact ⟨(atV 0 (by decide)).symm.trans ht.1.1.1,(atV 1 (by decide)).symm.trans ht.1.1.2,
      (atV 2 (by decide)).symm.trans ht.1.2,(atV 3 (by decide)).symm.trans ht.2⟩
  obtain ⟨h0,h1,h2,h3⟩ := l0
  have un (i : Fin 10) (h : label i = 3) : Unate F i := by
    have occ := firstInputBoundary_occurrences_le_one least.hcl out live distinct i i
    rw [last i h] at occ
    have u := formulaUnate i _ occ
    have eq : (PetersenCutFormula.wireFormula i gs out.val).eval = F :=
      funext fun x => PetersenCutFormula.wireFormula_eval _ least.hcl x _ out.isLt
    rwa [eq] at u
  apply AdjacentSeed.adjacentConflict F _ (un 1 h1) (un 2 h2)
    (clash _ _ (h1.trans h2.symm)) (clash _ _ (h0.trans h3.symm))
  intro x hx
  exact computes x (by simpa [representative,valid,seedValue,AdjacentSeed.valid12] using hx)

end SeedRanks

namespace Relabel

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof MoveSeed

def renameWire {n : ℕ} (σ : Fin n → Fin n) (pin : Fin n) (flip : Bool) (i : ℕ) : ℕ :=
  if hi : i < n then if flip = true ∧ σ ⟨i,hi⟩ = pin then n else (σ ⟨i,hi⟩).val else i + 1

def input {n : ℕ} (σ : Fin n → Fin n) (pin : Fin n) (flip : Bool) (x : Fin n → Bool) (i : Fin n) : Bool :=
  if flip = true ∧ σ i = pin then !(x pin) else x (σ i)

def circuit {n : ℕ} (σ : Fin n → Fin n) (pin : Fin n) (flip : Bool) (C : Circuit) : Circuit :=
  let ρ := renameWire σ pin flip
  ⟨⟨.not,[pin.val]⟩ :: C.gates.map (moveGate ρ),ρ C.output⟩

lemma inject {n : ℕ} {σ : Fin n → Fin n} (inj : Function.Injective σ)
    (pin : Fin n) (flip : Bool) : Function.Injective (renameWire σ pin flip) := by
  intro i j h
  by_cases hi : i < n
  · by_cases hj : j < n
    · simp only [renameWire,dif_pos hi,dif_pos hj] at h
      split_ifs at h with h1 h2
      · exact congrArg Fin.val (inj (h1.2.trans h2.2.symm))
      · have := (σ ⟨j,hj⟩).isLt; omega
      · have := (σ ⟨i,hi⟩).isLt; omega
      · exact congrArg Fin.val (inj (Fin.ext h))
    · simp only [renameWire,dif_pos hi,dif_neg hj] at h
      have := (σ ⟨i,hi⟩).isLt
      split at h <;> omega
  · by_cases hj : j < n
    · simp only [renameWire,dif_neg hi,dif_pos hj] at h
      have := (σ ⟨j,hj⟩).isLt
      split at h <;> omega
    · simpa [renameWire,hi,hj] using h

lemma eval {n : ℕ} (σ : Fin n → Fin n) (inj : Function.Injective σ)
    (pin : Fin n) (flip : Bool) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n (circuit σ pin flip C) x = circuitFun n C (input σ pin flip x) := by
  let w := List.ofFn (input σ pin flip x)
  let u := List.ofFn x ++ [!(x pin)]
  have ulen : u.length = n + 1 := by simp [u]
  have same (i : ℕ) : w.getD i false = u.getD (renameWire σ pin flip i) false := by
    by_cases h : i < n
    · simp only [renameWire,dif_pos h]
      split_ifs with hf
      · have eq : (List.ofFn x ++ [!(x pin)]).getD n false = !(x pin) := by
          simpa using getD_snoc_eq (List.ofFn x) (!(x pin)) false
        rw [show u.getD n false = _ from eq]
        simp [w,List.getD_eq_getElem?_getD,List.getElem?_ofFn,h,input,hf]
      · rw [show u.getD (σ ⟨i,h⟩).val false = (List.ofFn x).getD (σ ⟨i,h⟩).val false from
          List.getD_append _ _ _ _ (by simpa using (σ ⟨i,h⟩).isLt)]
        simp [w,List.getD_eq_getElem?_getD,List.getElem?_ofFn,h,input,hf]
    · rw [renameWire,dif_neg h,List.getD_eq_default _ _ (by simp [w];omega),
        List.getD_eq_default _ _ (by omega)]
  have next (j : ℕ) : renameWire σ pin flip (w.length+j) = u.length+j := by
    simp only [w,List.length_ofFn,ulen,renameWire]
    split_ifs <;> omega
  have start : (List.ofFn x).getD pin.val false = x pin := by
    simp [List.getD_eq_getElem?_getD,List.getElem?_ofFn,pin.isLt]
  have run := (mapped_run _ (inject inj pin flip) C.gates w u same next C.output).symm
  change (wiresFrom (C.gates.map _) ((List.ofFn x) ++ [!((List.ofFn x).getD pin.val false)])).getD _ false = _
  rw [start]
  exact run

lemma fan {n : ℕ} (σ : Fin n → Fin n) (pin : Fin n) (flip : Bool) (C : Circuit)
    (h : FanInTwo C) : FanInTwo (circuit σ pin flip C) := by
  intro g hg
  change g ∈ Gate.mk .not [pin.val] :: C.gates.map _ at hg
  rcases List.mem_cons.mp hg with rfl | hg
  · simp
  · obtain ⟨q,hq,eq⟩ := List.mem_map.mp hg
    rw [←eq]
    exact moved_ok _ _ (h q hq)

lemma count {n : ℕ} (σ : Fin n → Fin n) (pin : Fin n) (flip : Bool) (C : Circuit) :
    nonNotCount (circuit σ pin flip C).gates = nonNotCount C.gates := by
  simpa [circuit,nonNotCount,List.countP_cons,isNotGate] using moved_count (renameWire σ pin flip) C.gates

end Relabel

namespace FirstGate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Unsigned SeedRanks

abbrev Code := Fin 20 × Fin 12 × Bool

def seed (i : Fin 20) : Seed :=
  if h : i.val < 19 then representative ⟨i.val,h⟩ else (0,2,1)

def inverse (i : Fin 12) : Fin 12 := ![0,1,2,8,4,11,6,7,3,9,10,5] i

def permute (i : Fin 12) (j : Fin 9) : Fin 9 := (![![0,1,2,3,4,5,6,7,8],![0,5,8,3,4,1,7,6,2],![1,0,5,8,6,2,4,7,3],![1,2,3,8,6,0,7,4,5],![2,1,0,5,7,3,6,4,8],![2,3,8,5,7,1,4,6,0],![3,2,1,0,4,8,7,6,5],![3,8,5,0,4,2,6,7,1],![5,0,1,2,7,8,4,6,3],![5,8,3,2,7,0,6,4,1],![8,3,2,1,6,5,4,7,0],![8,5,0,1,6,3,7,4,2]] i) j

lemma inverse_ok : ∀ (i : Fin 12) (j : Fin 9), permute (inverse i) (permute i j) = j ∧
    permute i (permute (inverse i) j) = j := by decide +kernel

def asOld (c : Code) (x : Fin 9 → Bool) (i : Fin 9) : Bool := x (permute (inverse c.2.1) i)

def inTen (c : Code) : Fin 10 → Fin 10 :=
  Fin.lastCases 9 (fun j => (permute (inverse c.2.1) j).castSucc)

lemma inTen_inj (c : Code) : Function.Injective (inTen c) := by
  rcases c with ⟨s,p,b⟩
  exact (by decide +kernel : ∀ (p : Fin 12) (i j : Fin 10),
    inTen ((0 : Fin 20),p,false) i = inTen ((0 : Fin 20),p,false) j → i = j) p

def form (c : Code) (x : Fin 9 → Bool) : Bool :=
  c.2.2 != seedValue (seed c.1) (fun j => x (permute c.2.1 j))

def signature (c : Code) : Sig :=
  let s := seed c.1
  let a := inputs.getD (permute c.2.1 s.1).val zero
  let b := inputs.getD (permute c.2.1 s.2.1).val zero
  let v := if s.2.2 = 0 then bin false a b else if s.2.2 = 1 then bin true a b else bin false (neg a) b
  if c.2.2 then neg v else v

lemma sig_bits (c : Code) (r : Row) : bit r (signature c) = form c (sample r) := by
  rcases c with ⟨i,p,b⟩
  cases b <;> simp only [signature,form,seedValue,sample] <;> split_ifs <;> simp_all [Unsigned.bit_neg,Unsigned.bit_bin]

def lits : List Sig := zero :: one :: inputs ++ inputs.map neg

lemma not_target : Unsigned.graph ∉ lits := by decide +kernel

lemma neg_checked : lits.all (fun a => lits.contains (neg a)) = true := by decide +kernel

lemma neg_mem {a : Sig} (h : a ∈ lits) : neg a ∈ lits := by
  exact List.contains_iff_mem.mp (List.all_eq_true.mp neg_checked a h)


def literalAt (i : Fin 20) : Sig := lits.getD i.val zero

lemma index_of_literal {a : Sig} (ha : a ∈ lits) : ∃ i : Fin 20, literalAt i = a := by
  obtain ⟨k,hk,rfl⟩ := List.mem_iff_getElem.mp ha
  have len : lits.length = 20 := by decide +kernel
  let i : Fin 20 := ⟨k,by omega⟩
  refine ⟨i,?_⟩
  simpa [literalAt,i,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk]

def witnessWord : Nat := 0x20f1f5eb54273b82c741f431df4cca7d19f2c0000bdcdacaec158baef34138b0a65c4aa90965e00000000083c7c0000c3e7d72d1c1e6dfb1558b25ef0f79c2e6f7a000036fb874d8367ba96dc9c35893dc247780000000005eb570f9f00002071bc0e65ff177cc455ac578c25db64dced8000099dfb63b497df2536e6ed52436c00000000009ced72d181c6c000080c647fd734a046bcd01cf45e2ab0ba2ff3200002d7302b96932a026960362800000000082c77079bc0e660319000016acd7dc4deb0d54b066b76ddecb6bb098da8000072d72577492da1b35000000000007d0dfb157fc5c7fd75ab34000005cfc6fcf309e45a26b9cb2fb2e2d95abae400000462427951229c0000000001df4d62c97cc44d2817dc4c173f000000f3918f24ba52acb82df2850a62eb2a1288800000f8809250000000000329f5ef0f56b146bcd7ac346fcf03ce4000000d054a94b8c9aaadc2c932d3242a938421e00000321c00000000019f2de70b78c24073d54b04c27918f24034100000be4abcc8adb201486aa2d84ea40a2480e8600000000000000000026f7a76d905e2a9add85a262e9494a942f92800008f419a8bc9d04a3904a103ba43a3e1939432000000000bdcd80000dcedac2e8ddecae72cacb82e326bcc8a3d06000033d86682e335828a3f190b0873da14f2000000000b2bb36fb800002ff32daec2fb2eb7ca2aadcb6c81a8bccf61800008d40b31808b3fa20f8622b210f0000000000158b9d36099df8000098da8b65650a60b24c1486a7412682e23502000023100eb0f90068e60d27802000000000bbcd367bad8ed2d73000002bae4bacaad324a8b623904cd60b31808c4000000662d224fa863d180a8000000000138b25b7297df0ae5a72d70000012888aa4e4ea42840e8a3f22cfeeb0f998b4000027c0ae70d8f06000000000029971c35894db932a095dd0462400000421e28923a43a642c220f8401a224fa9f02800009c01b90300000000004aa924f706ed509a5892da09e540f88000000e860f864873d988ace60d218f4e70da70060000280000000000002597a477890db036286cd41229c24940321c000039432853ca10f09e00980a83c1839030a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def directCode (i j : Fin 20) (d : Bool) : Code :=
  let entry := (i.val * 20 + j.val) * 2 + (if d then 1 else 0)
  let v := (witnessWord >>> (9 * entry)) &&& 511
  (Fin.ofNat 20 (v / 24),Fin.ofNat 12 (v / 2 % 12),v % 2 == 1)

def directOK (i j : Fin 20) (d : Bool) : Bool :=
  let v := bin d (literalAt i) (literalAt j)
  lits.contains v || (signature (directCode i j d) == v)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma direct_checked : ∀ (i j : Fin 20) (d : Bool), directOK i j d = true := by decide +kernel

lemma classify_gate (w : List Sig) (inside : ∀ a ∈ w, a ∈ lits) (g : Gate)
    (legal : CircuitProof.Ok g) (fresh : gv w g ∉ lits) :
    g.op ≠ .not ∧ ∃ c : Code, signature c = gv w g := by
  have rep {a : Sig} (h : represented w a) : a ∈ lits := by
    rcases Unsigned.operand_cases h with rfl | rfl | ⟨ha,_⟩
    · decide +kernel
    · decide +kernel
    · exact inside a ha
  have zn : zero ∈ lits := by decide +kernel
  constructor
  · intro hn
    apply fresh
    rw [gv,hn]
    apply neg_mem
    cases he : g.inputs with
    | nil => exact zn
    | cons i l => exact rep (Unsigned.get_rep w i)
  · rcases Unsigned.gate_rep w g legal with rh | ⟨a,ha,_,eq⟩ | ⟨d,a,b,ha,hb,_,_,_,eq⟩
    · exact (fresh (rep rh)).elim
    · exact (fresh (by simpa only [eq] using neg_mem (inside _ ha))).elim
    · obtain ⟨i,hi⟩ := index_of_literal (inside _ ha)
      obtain ⟨j,hj⟩ := index_of_literal (inside _ hb)
      have pick := direct_checked i j d
      simp only [directOK,hi,hj,←eq,Bool.or_eq_true,List.contains_iff_mem,beq_iff_eq] at pick
      exact ⟨directCode i j d,pick.resolve_left fresh⟩

lemma first (gs : List Gate) : ∀ (w : List Sig), (∀ a ∈ w, a ∈ lits) →
    (∀ g ∈ gs, CircuitProof.Ok g) → Unsigned.graph ∈ execute gs w →
    ∃ pre g post c, gs = (pre ++ [g]) ++ post ∧ g.op ≠ .not ∧ signature c = gv (execute pre w) g := by
  induction gs with
  | nil =>
    intro w inside legal hit
    exact (not_target (inside _ hit)).elim
  | cons g gs ih =>
    intro w inside legal hit
    by_cases hd : gv w g ∈ lits
    · obtain ⟨pre,q,post,c,eq,hn,hs⟩ := ih (w ++ [gv w g]) (fun a ha => by
        rcases List.mem_append.mp ha with h | h
        · exact inside _ h
        · have e := List.mem_singleton.mp h
          simpa only [e] using hd)
        (fun q hq => legal _ (List.mem_cons_of_mem _ hq)) hit
      exact ⟨g :: pre,q,post,c,by simp [eq],hn,hs⟩
    · obtain ⟨hn,c,hc⟩ := classify_gate w inside g (legal _ List.mem_cons_self) hd
      exact ⟨[],g,gs,c,rfl,hn,hc⟩

lemma sample_surjective (x : Fin 9 → Bool) : ∃ r : Row, sample r = x := by
  let v := BitVec.ofBoolListLE (List.ofFn x)
  let r : Row := v.toFin.cast (by simp [v,List.length_ofFn])
  refine ⟨r,?_⟩
  funext j
  rw [sample,input_coords]
  change (BitVec.ofBoolListLE (List.ofFn x)).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]

lemma actual_value (pre : List Gate) (g : Gate) (c : Code) (legal : ∀ q ∈ pre, CircuitProof.Ok q)
    (hg : CircuitProof.Ok g) (sig : signature c = gv (execute pre inputs) g) (x : Fin 9 → Bool) :
    form c x = g.op.eval (g.inputs.map fun i => (CircuitProof.wiresFrom pre (List.ofFn x)).getD i false) := by
  obtain ⟨r,rfl⟩ := sample_surjective x
  rw [←sig_bits,sig,Unsigned.run_bit r g _ hg.1,Unsigned.execute_bits pre r inputs (fun q hq => (legal q hq).1),sampled]
  rfl

set_option maxRecDepth 20000 in
lemma honest_first (C : Circuit) (fan : FanInTwo C) (correct : circuitFun 9 C = edge) :
    ∃ pre g post c, C.gates = (pre ++ [g]) ++ post ∧ g.op ≠ .not ∧
      ∀ x : Fin 9 → Bool, form c x = g.op.eval (g.inputs.map fun i =>
        (CircuitProof.wiresFrom pre (List.ofFn x)).getD i false) := by
  have eq : (execute C.gates inputs).getD C.output zero = Unsigned.graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C fan C.output r).trans ((congrFun correct (sample r)).trans (edge_table r).symm)
  have h := Unsigned.get_rep (execute C.gates inputs) C.output
  rw [eq] at h
  have hit := h.resolve_right (fun hn => hn graph_proper)
  have init (a : Sig) (ha : a ∈ inputs) : a ∈ lits := by
    simp only [lits,List.mem_cons,List.mem_append]
    tauto
  obtain ⟨pre,g,post,c,hgs,hn,hc⟩ := first C.gates inputs init fan hit
  refine ⟨pre,g,post,c,hgs,hn,actual_value pre g c (fun q hq => fan _ ?_) (fan _ ?_) hc⟩
  · rw [hgs]; simp [hq]
  · rw [hgs]; simp
end FirstGate

namespace Suffix

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers PetersenNine
open FirstGate SeedRanks Finite2770

lemma plug_last (x : Fin 9 → Bool) (b : Bool) : Suffix2770.plug x b 9 = b := by
  change Fin.lastCases (motive := fun _ => Bool) b x (Fin.last 9) = b
  exact Fin.lastCases_last

lemma plug_cast (x : Fin 9 → Bool) (b : Bool) (j : Fin 9) : Suffix2770.plug x b j.castSucc = x j := by
  simp [Suffix2770.plug]

lemma dep_of_pair {n : ℕ} {H : (Fin n → Bool) → Bool} {i : Fin n}
    (hd : ∃ p q : Fin n → Bool, (∀ j, j ≠ i → p j = q j) ∧ H p ≠ H q) : Dep H i := by
  obtain ⟨p,q,ha,hf⟩ := hd
  have ne : p i ≠ q i := by
    intro hp
    have eq : p = q := funext (fun j => by
      by_cases h : j = i
      · simpa only [h] using hp
      · exact ha j h)
    exact hf (congrArg H eq)
  have hi : (!p i) = q i := by cases hp : p i <;> cases hq : q i <;> simp_all
  have up : Function.update p i (!p i) = q := by
    funext j
    by_cases h : j = i
    · simpa only [h, Function.update_self] using hi
    · simpa only [Function.update_of_ne h] using ha j h
  exact ⟨p, by simpa only [up] using hf.symm⟩



def embed (s : Seed) (x : Fin 9 → Bool) : X := Suffix2770.plug x (seedValue s x)

def before (q : Fin 20) (i : Fin 9) : ℕ := (![![16,4,2,4,1,1,2,4,8],![16,1,2,4,1,1,2,4,8],![2,1,2,4,1,1,2,4,8],![2,1,9,4,1,1,2,4,8],![2,1,2,4,1,1,2,4,8],![10,1,2,5,1,1,2,4,8],![2,1,2,5,1,1,2,4,8],![2,1,2,4,8,1,2,4,8],![16,1,2,4,1,1,2,4,8],![2,1,2,4,1,1,2,4,8],![2,1,2,4,1,1,2,4,8],![80,1,2,4,1,1,257,4,8],![2,1,2,4,1,1,257,4,8],![2,4,2,4,1,1,2,4,8],![16,1,2,4,8,1,2,4,8],![2,20,2,4,1,1,2,4,8],![2,1,2,4,1,1,2,4,8],![2,1,2,4,65,1,18,4,8],![2,1,2,4,1,1,18,4,8],![20,1,9,4,1,1,2,4,8]] q) i
def noRow (q : Fin 20) (i : Fin 10) (b : Bool) : ℕ := if b then (![![1,2,4,8,16,32,64,128,256,0],![1,514,4,8,16,32,64,128,256,514],![1,2,4,8,16,32,64,128,256,517],![1,2,5,8,16,32,64,128,256,516],![1,2,4,8,16,32,64,128,256,521],![513,2,4,520,16,32,64,128,256,513],![1,2,4,9,16,32,64,128,256,520],![1,2,4,8,16,32,64,128,256,0],![513,2,4,8,528,32,64,128,256,513],![1,2,4,8,528,32,64,128,256,528],![1,2,4,8,16,32,64,128,256,577],![513,2,4,8,16,32,576,128,256,513],![1,2,4,8,16,32,65,128,256,576],![1,514,516,8,16,32,64,128,256,514],![513,2,4,8,16,32,64,128,256,513],![1,18,4,8,16,32,64,128,256,514],![1,2,4,8,16,32,64,128,256,592],![1,2,4,8,528,32,576,128,256,528],![1,2,4,8,16,32,80,128,256,576],![513,2,516,8,16,32,64,128,256,513]] q) i else (![![0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0],![0,0,0,0,0,0,0,0,0,0]] q) i
def yesRow (q : Fin 20) (i : Fin 10) (b : Bool) : ℕ := if b then (![![13,6,6,12,17,33,66,132,262,515],![3,3,7,11,17,33,67,131,259,518],![3,3,6,11,17,33,66,131,259,519],![3,3,7,11,17,33,66,131,259,518],![3,3,6,12,17,33,66,131,259,523],![515,6,6,523,22,38,66,132,262,515],![3,3,6,11,17,33,66,131,259,524],![3,3,6,11,22,33,66,131,259,529],![515,6,6,12,529,38,66,132,262,515],![3,3,6,11,17,33,66,131,259,534],![3,3,6,11,17,33,66,131,259,579],![515,6,6,12,22,38,578,132,262,515],![3,3,6,11,17,33,67,131,259,578],![17,515,518,24,17,33,81,145,264,515],![17,6,6,12,17,38,66,132,262,515],![13,19,12,12,17,33,76,132,264,515],![3,3,6,11,17,33,66,131,259,593],![3,3,6,11,529,33,578,131,259,529],![3,3,6,11,17,33,81,131,259,578],![515,26,518,24,24,56,66,152,264,515]] q) i else (![![6,12,17,6,6,6,6,6,6,6],![12,12,3,3,3,3,3,3,3,3],![6,12,3,3,3,3,3,3,3,3],![24,13,3,3,3,3,3,3,3,3],![6,12,3,3,3,3,3,3,3,3],![6,132,66,6,6,6,6,6,6,6],![6,13,3,3,3,3,3,3,3,3],![6,12,3,3,3,3,3,3,3,3],![6,12,66,6,6,6,6,6,6,6],![6,12,3,3,3,3,3,3,3,3],![6,12,3,3,3,3,3,3,3,3],![6,12,24,6,6,6,6,6,6,6],![6,12,3,3,3,3,3,3,3,3],![24,17,17,17,33,17,17,17,17,17],![6,12,17,6,6,6,6,6,6,6],![12,12,17,17,12,12,12,12,12,12],![6,12,3,3,3,3,3,3,3,3],![6,12,3,3,3,3,3,3,3,3],![6,12,3,3,3,3,3,3,3,3],![24,24,24,66,66,24,24,24,24,24]] q) i

def raw (m : ℕ) (i : Fin 9) := m.testBit i.val

set_option maxHeartbeats 0 in
lemma rawPairs : ∀ (q : Fin 20) (i : Fin 9),
    let s := seed q
    let a := embed s (raw (before q i))
    let b := embed s (raw (before q i + 2 ^ i.val))
    SeedRanks.valid s a = true ∧ SeedRanks.valid s b = true ∧
    (∀ j : Fin 10, j ≠ i.castSucc → a j = b j) ∧ target a ≠ target b := by decide +kernel

set_option maxHeartbeats 0 in
lemma cofactorPairs : ∀ (q : Fin 20) (i : Fin 10) (b : Bool), q = 19 →
    let s := seed q
    let a := row (noRow q i b)
    let z := row (yesRow q i b)
    SeedRanks.valid s a = true ∧ SeedRanks.valid s z = true ∧ a i = b ∧ z i = b ∧ target a ≠ target z := by decide +kernel

lemma lower13 (C : Circuit) (fan : FanInTwo C) (correct : circuitFun 9 C = Unsigned.edge) :
    13 ≤ nonNotCount C.gates := by
  apply petersen_binary_lower C fan
  intro x
  have hx := congrFun correct x
  simpa only [circuitFun,Unsigned.edge,petersenF,edgeFun,edges,List.any_cons,List.any_nil,
    Bool.or_false,Bool.or_assoc] using hx

lemma impossible (q : Fin 20) (D : Circuit) (fan : FanInTwo D)
    (budget : nonNotCount D.gates ≤ 12)
    (agree : ∀ x : X, SeedRanks.valid (seed q) x = true → circuitFun 10 D x = target x) : False := by
  let H := circuitFun 10 D
  have dp (i : Fin 10) : Dep H i := by
    by_cases ht : i.val < 9
    · let v : Fin 9 := ⟨i.val,ht⟩
      have he : i = v.castSucc := Fin.ext rfl
      rw [he]
      obtain ⟨ha,hb,off,ne⟩ := rawPairs q v
      apply dep_of_pair
      refine ⟨_,_,off,?_⟩
      rw [show H = circuitFun 10 D from rfl,agree _ ha,agree _ hb]
      exact ne
    · have he : i = 9 := Fin.ext (by have := i.isLt; change i.val = 9; omega)
      subst i
      by_contra noDep
      have same (a b : X) (off : ∀ j : Fin 10, j ≠ 9 → a j = b j) : H a = H b := by
        by_contra ne
        exact noDep (dep_of_pair ⟨a,b,off,ne⟩)
      let E : Circuit := ⟨⟨.not,[0]⟩ :: D.gates,D.output⟩
      have ef : FanInTwo E := by
        intro g hg
        change g ∈ Gate.mk .not [0] :: D.gates at hg
        rcases List.mem_cons.mp hg with rfl | h
        · simp
        · exact fan _ h
      have ec (x : Fin 9 → Bool) : circuitFun 9 E x = Unsigned.edge x := by
        let a := Suffix2770.plug x (!(x 0))
        let b := embed (seed q) x
        have eq := same a b (fun j => by
          refine Fin.lastCases ?_ (fun k => ?_) j
          · exact fun h => (h rfl).elim
          · simp [a,b,embed,Suffix2770.plug])
        have va : SeedRanks.valid (seed q) b = true := by
          simp [SeedRanks.valid,b,embed,plug_last,plug_cast]
        have t : target b = Unsigned.edge x := by
          change Unsigned.edge (fun j : Fin 9 => Suffix2770.plug x (seedValue (seed q) x) j.castSucc) = Unsigned.edge x
          simp only [plug_cast]
        have sem : circuitFun 9 E x = H a := by
          change (wiresFrom D.gates (List.ofFn x ++ [!((List.ofFn x).getD 0 false)])).getD D.output false =
            (wiresFrom D.gates (List.ofFn (Suffix2770.plug x (!(x 0))))).getD D.output false
          rw [Suffix2770.plug_list]
          simp [List.getD_eq_getElem?_getD]
        exact sem.trans (eq.trans ((agree b va).trans t))
      have low := lower13 E ef (funext ec)
      have cnt : nonNotCount E.gates = nonNotCount D.gates := by
        simp [E,nonNotCount,List.countP_cons,isNotGate]
      omega
  have still (hq : q = 19) (i : Fin 10) (b : Bool) : ∃ x y : X, H (Function.update x i b) ≠ H (Function.update y i b) := by
    let a := row (noRow q i b)
    let z := row (yesRow q i b)
    obtain ⟨va,vz,ha,hz,ne⟩ := cofactorPairs q i b hq
    have ea : Function.update a i b = a := ha ▸ Function.update_eq_self _ _
    have ez : Function.update z i b = z := hz ▸ Function.update_eq_self _ _
    refine ⟨a,z,?_⟩
    rw [ea,ez,show H = circuitFun 10 D from rfl,agree a va,agree z vz]
    exact ne
  by_cases h : q.val < 19
  · let idx : Fin 19 := ⟨q.val,h⟩
    apply noRepresentative idx D fan budget _ dp
    simpa [seed,h,idx] using agree
  · have he : q = 19 := Fin.ext (by have := q.isLt; change q.val = 19; omega)
    subst q
    apply noSuffix D fan budget _ dp (still rfl)
    intro x hx
    exact agree x (by simpa [SeedRanks.valid,seed,seedValue] using hx)

lemma project_raw (c : Code) (x : X) (j : Fin 9) :
    Relabel.input (inTen c) 9 c.2.2 x j.castSucc = x (permute (inverse c.2.1) j).castSucc := by
  have neq : (permute (inverse c.2.1) j).castSucc ≠ (9 : Fin 10) := by
    intro e
    have eq := congrArg Fin.val e
    change (permute (inverse c.2.1) j).val = 9 at eq
    have := (permute (inverse c.2.1) j).isLt
    omega
  simp [Relabel.input,inTen,neq]

lemma project_extra (c : Code) (x : X) :
    Relabel.input (inTen c) 9 c.2.2 x 9 = (c.2.2 != x 9) := by
  have last : inTen c 9 = 9 := by
    change Fin.lastCases (motive := fun _ => Fin 10) 9 (fun j => (permute (inverse c.2.1) j).castSucc) (Fin.last 9) = 9
    exact Fin.lastCases_last
  unfold Relabel.input
  rw [last]
  cases c.2.2 <;> cases x 9 <;> decide

set_option maxHeartbeats 0 in
lemma graphSym : ∀ (p : Fin 12) (r : Unsigned.Row),
    Unsigned.edge (fun j => Unsigned.sample r (permute (inverse p) j)) = Unsigned.edge (Unsigned.sample r) := by decide +kernel

lemma sym_on (c : Code) (x : X) : Unsigned.edge (fun i : Fin 9 =>
    Relabel.input (inTen c) 9 c.2.2 x i.castSucc) = target x := by
  simp_rw [project_raw]
  let a := fun j : Fin 9 => x j.castSucc
  change Unsigned.edge (fun j => a (permute (inverse c.2.1) j)) = Unsigned.edge a
  obtain ⟨r,hr⟩ := sample_surjective a
  rw [←hr]
  exact graphSym c.2.1 r

lemma small_impossible (C : Circuit) (fan : FanInTwo C) (budget : nonNotCount C.gates ≤ 13)
    (correct : circuitFun 9 C = Unsigned.edge) : False := by
  obtain ⟨pre,g,post,c,eq,non,formval⟩ := honest_first C fan correct
  let A := MoveSeed.withSeed pre post C.output
  let D := Relabel.circuit (inTen c) 9 c.2.2 A
  have af : FanInTwo A := MoveSeed.withSeed_fan pre post g C.output (by simpa only [←eq] using fan)
  have df : FanInTwo D := Relabel.fan _ _ _ _ af
  have ct := MoveSeed.withSeed_count pre post g C.output non
  have dc : nonNotCount D.gates = nonNotCount A.gates := Relabel.count _ _ _ _
  have ab : nonNotCount A.gates ≤ 12 := by change nonNotCount (MoveSeed.withSeed pre post C.output).gates ≤ 12; rw [eq] at budget; omega
  apply impossible c.1 D df ((by omega : nonNotCount D.gates ≤ 12))
  intro x hx
  let a := Relabel.input (inTen c) 9 c.2.2 x
  let old := fun j : Fin 9 => a j.castSucc
  have hp : (fun j => old (permute c.2.1 j)) = fun j : Fin 9 => x j.castSucc := by
    funext j
    change Relabel.input _ _ _ x (permute c.2.1 j).castSucc = _
    rw [project_raw,(inverse_ok _ _).1]
  have hy : a 9 = form c old := by
    have hx' : x 9 = seedValue (seed c.1) (fun j => x j.castSucc) := beq_iff_eq.mp hx
    change Relabel.input _ _ _ x 9 = _
    rw [project_extra,form,hp,← hx']
  have packed : Suffix2770.plug old (a 9) = a := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · exact plug_last old (a 9)
    · simp [Suffix2770.plug,old]
  have hu : List.ofFn a = List.ofFn old ++ [a 9] :=
    (congrArg (fun f : Fin 10 → Bool => List.ofFn f) packed).symm.trans (Suffix2770.plug_list old (a 9))
  have evalA := MoveSeed.withSeed_eval pre post g C.output (List.ofFn old) (by simp) (a 9) (hy.trans (formval old))
  have cele : (Circuit.mk ((pre ++ [g]) ++ post) C.output) = C := by rw [←eq]
  rw [cele] at evalA
  have step : circuitFun 10 A a = circuitFun 9 C old := by
    change A.eval (List.ofFn a) = C.eval (List.ofFn old)
    rw [hu]
    exact evalA.symm
  exact (Relabel.eval _ (inTen_inj c) _ _ A x).trans (step.trans ((congrFun correct old).trans (sym_on c x)))

end Suffix

namespace Monotone
open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w _ i hi

lemma foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply getD_ge_len
  rw [foldl_step_len]
  exact hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) :=
        getD_append_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma wires_gate_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have h := foldl_step_gate C.gates (List.ofFn x) j g hj
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

lemma wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn x) w (by simp [hw]), ofFn_getD_lt]

lemma wires_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    (C.wires (List.ofFn x)).getD w false = false := by
  rw [wires_eq_foldl]
  exact foldl_step_getD_ge C.gates (List.ofFn x) w (by simp [hw])

lemma gateOp_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f1 f2 : ℕ → Bool) (hle : ∀ i ∈ l, f1 i = true → f2 i = true) :
    op.eval (l.map f1) = true → op.eval (l.map f2) = true := by
  rcases hop with rfl | rfl
  · intro h
    change (l.map f1).all id = true at h
    change (l.map f2).all id = true
    rw [List.all_eq_true] at h ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hle i hi (h _ (List.mem_map_of_mem hi))
  · intro h
    change (l.map f1).any id = true at h
    change (l.map f2).any id = true
    rw [List.any_eq_true] at h ⊢
    obtain ⟨b, hb, hbt⟩ := h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨f2 i, List.mem_map_of_mem hi, hle i hi hbt⟩

lemma wires_mono {n : ℕ} (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ u, x u = true → y u = true) :
    ∀ w : ℕ, (C.wires (List.ofFn x)).getD w false = true → (C.wires (List.ofFn y)).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw1 : w < n
    · rw [wires_input C x w hw1, wires_input C y w hw1]
      exact hxy ⟨w, hw1⟩
    · by_cases hw2 : n + C.gates.length ≤ w
      · rw [wires_oob C x w hw2]
        intro h; exact absurd h (by decide)
      · have hjlt : w - n < C.gates.length := by omega
        set j := w - n
        have hwj : w = n + j := by omega
        have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
        have hgop : (C.gates[j]'hjlt).op = GateOp.and ∨ (C.gates[j]'hjlt).op = GateOp.or := by
          simpa using (hmono _ (List.mem_of_getElem? hg)).1
        rw [hwj, wires_gate_ofFn C x j _ hg, wires_gate_ofFn C y j _ hg]
        apply gateOp_mono _ hgop
        intro i _ hi
        by_cases hilt : i < n + j
        · simp only [hilt, ↓reduceIte] at hi ⊢
          exact ih i (by omega) hi
        · simp only [hilt, ↓reduceIte] at hi
          exact absurd hi (by decide)

end Monotone

namespace Finish

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof

def toggled (b : Bool) (x : Fin 9 → Bool) (i : Fin 9) : Bool :=
  if i = 0 then b != x 0 else x i

lemma main (C : Circuit) (fan : FanInTwo C) (small : C.size ≤ 14)
    (correct : ∀ x : Fin 9 → Bool, circuitFun 9 C (toggled true x) = Unsigned.edge x) : False := by
  have aNot : ∃ g ∈ C.gates, g.op = .not := by
    by_contra! none
    have monotone : Monotone2 C := by
      intro g hg
      obtain ⟨basis,pins⟩ := fan g hg
      refine ⟨?_,pins⟩
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at basis ⊢
      exact basis.elim Or.inl (fun h => Or.inr (h.resolve_right (none g hg)))
    have inc : ∀ i, toggled true (Suffix.raw 3) i = true → toggled true (Suffix.raw 2) i = true := by decide
    have up := Monotone.wires_mono C monotone _ _ inc C.output
    have yes : circuitFun 9 C (toggled true (Suffix.raw 3)) = true := (correct _).trans (by decide)
    have no : circuitFun 9 C (toggled true (Suffix.raw 2)) = false := (correct _).trans (by decide)
    exact Bool.noConfusion ((up yes).symm.trans no)
  obtain ⟨g,hg,hn⟩ := aNot
  have strict : nonNotCount C.gates < C.gates.length := by
    rw [nonNotCount,List.countP_eq_length_filter]
    apply List.length_filter_lt_length_iff_exists.mpr
    exact ⟨g,hg,by simp [isNotGate,hn]⟩
  let D := Relabel.circuit (fun i : Fin 9 => i) 0 true C
  have df : FanInTwo D := Relabel.fan _ _ _ _ fan
  have count : nonNotCount D.gates = nonNotCount C.gates := Relabel.count _ _ _ _
  apply Suffix.small_impossible D df (by change C.gates.length ≤ 14 at small; omega)
  funext x
  rw [show circuitFun 9 D x = _ from Relabel.eval (fun i : Fin 9 => i) (fun _ _ h => h) 0 true C x]
  have eq : Relabel.input (fun i : Fin 9 => i) 0 true x = toggled true x := by
    funext i
    by_cases h : i = 0
    · subst i; cases hv : x 0 <;> simp [Relabel.input,toggled,hv]
    · simp [Relabel.input,toggled,h]
  rw [eq,correct]

end Finish

end PEqualNP.Outside.L_meta_4177

theorem PEqualNP.Outside.L_meta_4177 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4.inputs.contains (0 : ℕ)) x1.gates).length = (1 : ℕ) → (¬∃ x5 ∈ x1.gates, (0 : ℕ) ∈ x5.inputs ∧ x5.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ (x6 : Fin (9 : ℕ) → Bool), (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x7 : Fin (9 : ℕ)) => if x7 = (0 : Fin (9 : ℕ)) then Bool.true != x6 (0 : Fin (9 : ℕ)) else x6 x7) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro C fan small _ _
  by_contra! h
  exact PEqualNP.Outside.L_meta_4177.Finish.main C fan small h
