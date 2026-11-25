import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_14502.Model
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
theorem getRep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (getRep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (getRep w i) (getRep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (getRep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

theorem extractPlan {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

theorem bRead (i) (w : List Sig) (j : Nat) :
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
  simp only [bRead]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

theorem exeBits (gs : List Gate) (i) (w : List Sig)
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
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
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
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
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

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
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

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
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
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

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
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

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

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
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
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
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



def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
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
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

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

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
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

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

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

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
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

def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)

theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
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
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
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
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
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

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires ∧ True

theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (restrictRows f)) := by
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
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)

theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 152
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 152 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 152 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 152 → Row) (x : Decor) := x.2 = pairSig r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]

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
    decodeBank k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
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
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 152) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 152) (j : Fin 9) :
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
  ((n*n % 2305843009213693951)*(n+7)+971*n) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Bool
def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)
def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)
theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 152 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
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
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem node_sound {u raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)


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
theorem rotate_excluded {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible u T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
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
  exact hi k hk run

def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


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


end PEqualNP.Outside.L_meta_14502.Model

namespace PEqualNP.Outside.L_meta_14502
open PEqualNP.Outside.L_meta_14502.Model
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Atlas := Nat × List Decor × Sig × (Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → Nat) × (Nat → Nat → Nat)

def top (g : Atlas) := g.1
def first (g : Atlas) := g.2.1
def target (g : Atlas) := g.2.2.1
def count (g : Atlas) := g.2.2.2.1
def record (g : Atlas) := g.2.2.2.2.1
def tip (g : Atlas) := g.2.2.2.2.2.1
def locate (g : Atlas) := g.2.2.2.2.2.2
def items (g : Atlas) (k i : Nat) : List Decor :=
  let d := top g-k
  let v := record g k i
  selectLive (v >>> (10*d)) (decodeBank d v (first g))
def vals (g : Atlas) (k i : Nat) := (items g k i).map Prod.fst
def roots (g : Atlas) := (first g).map Prod.fst

def SB : Nat := 5

def tips (raw : List Sig) (v : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let b := v % 256
    (b/36,raw.getD (b/6 % 6) zero,raw.getD (b % 6) zero)::tips raw (v >>> 8) n

def deadTest (raw : List Sig) (ws : List Sig) (k hint : Nat) : Bool :=
  let j := min ((hint % 8)-1) 5
  let d := neg (raw.getD j zero)
  let cs := tips raw (hint >>> 6) (hint/8 % 8)
  (makePool true d raw cs).any (fun pool => poolCut true d SB k cs.length pool ws)

def mirrorSteps : List Move := []

def variant (g : Atlas) (code : Nat) (ws : List Sig) : List Sig :=
  if code % 2 == 1 && autoOK (target g) mirrorSteps then ws.map (movedWord mirrorSteps.reverse) else ws

theorem variant_ok {g k ws} (h : Impossible true (target g) k (List.toFinset ws)) (code : Nat) :
    Impossible true (target g) k (variant g code ws).toFinset := by
  unfold variant
  split
  next e =>
    simp only [Bool.and_eq_true] at e
    exact rotate_excluded h _ e.2
  next => exact h

def links (g : Atlas) (k tag : Nat) : List (List Sig) :=
  let code := locate g k tag
  let row := code / 2
  if row < count g k then [variant g code (vals g k row)] else []

def checkRow (g : Atlas) (k i : Nat) : Bool :=
  let ws := items g k i
  let vs := ws.map Prod.fst
  let h := tip g k i
  decide vs.Nodup && !vs.contains (target g) &&
    (if h != 0 then deadTest (roots g) vs k h else
      testAll (k,ws.length,ws,preCov true ws,[],links g (k-1)) ws)

def Ready (g : Atlas) (r s : Fin 152 → Row) :=
  properPairs (target g) r s ∧ (∀ a ∈ first g, faithful r s a) ∧
    ∀ k i, i < count g k → tip g k i ≠ 0 →
      Slice true (roots g) (target g) (neg ((roots g).getD (min ((tip g k i % 8)-1) 5) zero)) SB

theorem checked {g : Atlas} {r s} (ready : Ready g r s) (k : Nat)
    (good : ∀ l ≤ k, ∀ i < count g l, checkRow g l i = true) :
    ∀ i < count g k, Impossible true (target g) k (vals g k i).toFinset := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hi
    have h := good k (by omega) i hi
    simp only [checkRow,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not] at h
    by_cases hn : tip g k i = 0
    · simp only [hn,bne_self_eq_false, Bool.false_eq_true,ite_false] at h
      by_cases hk : k=0
      · subst k
        intro n cap run
        have : n=0 := by omega
        subst n
        have hm : target g ∈ (vals g 0 i).toFinset := run.1 ▸ Finset.mem_singleton_self _
        exact h.1.2 (List.mem_toFinset.mp hm)
      apply node_sound (raw:=roots g) ready.1 _ h.1.1 h.1.2 _ _ h.2
      · intro a ha
        exact decode_faithful _ _ _ _ _ ready.2.1 _ ((selectLive_sub _ _).subset ha)
      · simp
      · intro tag xs hx
        simp only [links] at hx
        split at hx
        next le =>
          obtain rfl := List.mem_singleton.mp hx
          exact variant_ok (ih (k-1) (by omega) (fun l hl => good l (by omega)) _ le) _
        next => simp at hx
    · simp only [bne_iff_ne.mpr hn, ite_true] at h
      have test := h.2
      simp only [deadTest,Option.any_eq_true] at test
      obtain ⟨bank,he,hc⟩ := test
      exact poolCut_sound (ready.2.2 k i hi hn) _ he h.1.1 hc

def segment (test : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => test (start+n) && segment test start n

theorem segmentRange {test start n} (h : segment test start n=true) (i : Nat)
    (lo : start ≤ i) (hi : i<start+n) : test i=true := by
  induction n with
  | zero => exact False.elim (Nat.not_lt_of_ge lo hi)
  | succ n ih =>
    simp only [segment,Bool.and_eq_true] at h
    by_cases eq : i=start+n
    · exact eq.symm ▸ h.1
    · exact ih h.2 (lt_of_le_of_ne (Nat.le_of_lt_succ hi) eq)

def blockOK (g : Atlas) (k start n : Nat) := segment (checkRow g k) start n

theorem block_range {g k a n} (h : blockOK g k a n=true) (i : Nat)
    (lo : a ≤ i) (hi : i<a+n) : checkRow g k i=true := segmentRange h i lo hi

def Interval (g : Atlas) (k start n : Nat) := ∀ i : Nat, start ≤ i → i < start+n → checkRow g k i=true
theorem concat {g k a m n} (x : Interval g k a m) (y : Interval g k (a+m) n) :
    Interval g k a (m+n) := by
  intro i lo hi
  by_cases mid : i<a+m
  · exact x i lo mid
  · exact y i (Nat.le_of_not_gt mid) (Nat.add_assoc a m n ▸ hi)

end PEqualNP.Outside.L_meta_14502

namespace PEqualNP.Outside.L_meta_14502
open PEqualNP.Outside.L_meta_14502.Model
def s0K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x46020a80ef995d32be6374c6f185c30
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x11003009541cca350b318d420c2550430
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (i*4) 4
  | 3 => packedAt s0K3 (i*15) 15
  | 2 => packedAt s0K2 (i*26) 26
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (5+((h/1+packedAt s0K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s0K3 (96+((h/2+packedAt s0K3 (90+(h % 2)*3) 3) % 8)*4) 4
  | 2 => packedAt s0K2 (108+((h/1+packedAt s0K2 (104+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 2 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 3 => 0x76fe1fcff03fce3c
  | 5 => 0x78ffe00fffc00fc0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa010010012080045
  | 2 => 0x1224284484922512
  | 3 => 0x941501921248a28
  | 5 => 0x7851aae4986af80
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 46 s0Pos s0Neg, 0xfcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0fcccfcccfcc0fcc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_14502
namespace PEqualNP.Outside.L_meta_14502
open PEqualNP.Outside.L_meta_14502.Model
def s1K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x10a801820002f995d32be6374c6f185c30
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x10c209541cca350b318d420c2550430
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (i*4) 4
  | 3 => packedAt s1K3 (i*15) 15
  | 2 => packedAt s1K2 (i*26) 26
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (5+((h/1+packedAt s1K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s1K3 (98+((h/2+packedAt s1K3 (90+(h % 2)*4) 4) % 9)*4) 4
  | 2 => packedAt s1K2 (107+((h/1+packedAt s1K2 (104+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff7fcfc7ff8f3cf
  | 2 => 0xffffffffffffffffffffffedf99f3f8e3f3d33
  | 3 => 0x76fe1fcff03fce3c
  | 4 => 0x78ffe00fffc00fc0
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010010012080045
  | 2 => 0x1224284484922512
  | 3 => 0x941501921248a28
  | 4 => 0x7851aae4986af80
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 29 s1Pos s1Neg, 0xfaaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0faaafaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_14502
namespace PEqualNP.Outside.L_meta_14502
open PEqualNP.Outside.L_meta_14502.Model
def s2K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (6+((h/1+packedAt s2K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xf83f87c7fffe1fe1fc3f0fe0c3fff87f4dc3cf
  | 1 => 0xffc7fff83c3fe1fe1fc3f0fffc383f87b27d33
  | 3 => 0xfff807ffc03ffe3fe003ff00ffc03ff8c38e3c
  | 4 => 0x7ffffc0003ffffc0000ffffc000fc0fc0
  | 5 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xa0008411010200048050124004a082404c045
  | 1 => 0x10810080804402020440104244109102101512
  | 3 => 0xa11255120aa9106ca222aa08aa812650c30a28
  | 4 => 0x85b56624aa0d54b736a88812f3258312f80f80
  | 5 => 0xc626443733319939db33cc9c22060464efe000
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeeeeecceeaaee88eeeeeecceeaaee88eeeeeecceeaaee88eeeeeecceeaaee88eeeeeecceeaaee88eeeeeecceeaaee88eeeeeecceeaaee88eeeeeecceeaaee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_14502
namespace PEqualNP.Outside.L_meta_14502
open PEqualNP.Outside.L_meta_14502.Model
def s3K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (6+((h/1+packedAt s3K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf83f87c7fffe1fe1fc3f0fe0c3fff87f4dc3cf
  | 1 => 0xffc7fff83c3fe1fe1fc3f0fffc383f87b27d33
  | 2 => 0xfff807ffc03ffe3fe003ff00ffc03ff8c38e3c
  | 4 => 0x7ffffc0003ffffc0000ffffc000fc0fc0
  | 5 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xa0008411010200048050124004a082404c045
  | 1 => 0x10810080804402020440104244109102101512
  | 2 => 0xa11255120aa9106ca222aa08aa812650c30a28
  | 4 => 0x85b56624aa0d54b736a88812f3258312f80f80
  | 5 => 0xc626443733319939db33cc9c22060464efe000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeeeeececeaeae8e8eeeeececeaeae8e8eeeeececeaeae8e8eeeeececeaeae8e8eeeeececeaeae8e8eeeeececeaeae8e8eeeeececeaeae8e8eeeeececeaeae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_14502
namespace PEqualNP.Outside.L_meta_14502
open PEqualNP.Outside.L_meta_14502.Model
def s4K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (i*5) 5
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (6+((h/1+packedAt s4K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xc3cf1f8f8f1e38fc7e718f8fc071cfcf8dc0cf
  | 1 => 0xfc0fe7f3ffe03f1f8f81f1f1ff81f1f1927333
  | 2 => 0xfff007fc0fffc01ff1fe01fe03fe01fe638c3c
  | 3 => 0xfffff8000fffffe001fffe0003fffe007c0fc0
  | 5 => 0xfffffffff000000001fffffffc0000007ff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x406140a011045108801082824810444504c045
  | 1 => 0x4020100020080201000101080808080001112
  | 2 => 0x888092012448025002a2012411240128230428
  | 3 => 0x1104004a489020012545240022492800580a80
  | 5 => 0xe228d46b00dd349a49f9c9c9380c2c2d7fe000
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xfeecfeecfee8fee8feecfeecfee8fee8feecfeecfee8fee8feecfeecfee8fee8feecfeecfee8fee8feecfeecfee8fee8feecfeecfee8fee8feecfeecfee8fee8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_14502
namespace PEqualNP.Outside.L_meta_14502
open PEqualNP.Outside.L_meta_14502.Model
def s5K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s5K4 (i*5) 5
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s5K4 (6+((h/1+packedAt s5K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xc3cf3f9fff0e38fc7e318f8ffc71c7c784f0cf
  | 1 => 0xfc0fc7e38ff03f1f8fc1f1f1c381f9f99b4333
  | 2 => 0xfff007fc0fffc01ff1fe01fe03fe01fe638c3c
  | 3 => 0xfffff8000fffffe001fffe0003fffe007c0fc0
  | 4 => 0xfffffffff000000001fffffffc0000007ff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x410080010041008000020240104040001045
  | 1 => 0x44221108122090281040909088809091094112
  | 2 => 0x8880a201244402500292012411240124228428
  | 3 => 0x11040052488820012525240022492400540a80
  | 4 => 0xe228b45b00ed349a49f9c9c9380c34357fe000
  | _ => 0
def s5Atlas : Atlas := ⟨4,rawDecor 31 s5Pos s5Neg, 0xfeeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_14502
namespace PEqualNP.Outside.L_meta_14502
open PEqualNP.Outside.L_meta_14502.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x1f034b040044003b0e00241a0d4511020009432b3100470036002c120c3a4800140000222e002a1700301e000b420a354119002146201600130f1c27291805333e1040061d00280734383c392508492f01261b3f4a15372d233d320206080880000007042800b0070480001c50b0020009007fd5001fe54007f55001fc54007fd4c017f53007f94c01fd53005f54c01fc53007fd0c01bf43007f90c01fd43006f50c01fc43007fd48017f52007f94801fd52005f54801fc52007fd0801bf42007f90801fd42006f50801fc42007fcc801fe32007f4c801fc32007fd4401fe51005f94401fd51007f144017c51007fd0401bf41007f90401fd41006f50401fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc21007fd40017f50007f94001fd50005f54001fc50007fd0001fe40006f90001fd40007f10001bc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x84000df94420006f8a210003bf4108001dea084002bf98020016fea01000b7d5008005df2004002ef10020017de401000bfa2008005f69004003fe4802000dfecb880077f65c40033fb2e2006bf99710005facb88006fc65c4003be32e20019f1971000dfec988016fe64c4003df3262000af99310005fac988007bd64c40015eb262001bf1931000dfec788012fe63c40017eb1e2001bf18f10006fea7880037d53c4001dfa1e2000ef50f1000dfec58800efe62c40017eb162001bf18b10006fea5880037d52c4001dfa162000ef50b1000efca3880077c51c4003dfa0e2001fd9071000f7a8388003f541c4001daa0e2001fd8c710007ea6388007f621c4001fa90e2000dfd4310006faa18800bbe40c4005de2062002bfd9610035fccb0800b7e65840013f32c2000bf59610016facb080027d65840057e32c2002bfd92100177ec90800abf648400b7f3242000bf59210015f8c90800bbc64840055e3242002bfd8e10025fcc708002fd63840057e31c2000dfd4e10006faa708003bf4384001dea1c2002bfd8a1001dfcc508002fd62840057e3142000dfd4a10006faa508003bf4284001dea142000bf5861000efca3080077c5184001dfa0c2000ef50610015fcc10800b7f5084005fd2842002df54210007f2a108003795084005df2042002ef10210017f46108003f93084005fd1042000fe48210017ee2108007fb10840017fb2a2000dfd9510004feca8801afe65440017eb2a2006bf19510006f8ca880027c65440017fb222000efd91100057ec888016fe64440017eb222005bf1911000778c888002bc64440017fb1a2004bf98d10005fac688012fc6344001bfa9a2000df54d100077e8688003bd43440017fb122003bf98910005fac48800efc6244001bfa922000df549100077e8488003bd4244003bf28a2001df145100077e8288003f64144001dea0a2000fd505100076a8288003f63144001fa98a2000fd88510007ea42880037f5044001fd2822000df54110007f2a088003795044005df2022002ef10110007f46088003f93044001fd1022000fe4811000ff6208800bf610440057fb282006bf99410016fcca080027e65040017eb282002df59410004faca0800afc65040057fb202005bf990100177cc808002be64040017eb202002ef590100057ac80800afc64040057fb182004bf98c10017bcc608002de63040017eb182002f758c10005bac60800afc6304001bfa982000df54c100077e8608003bd43040057fb102003bf98810017dcc408002ee62040017eb102002fb58810005dac40800afc6204001bfa902000df548100077e8408003bd42040037f3082001df9441000ef8a208007bf4104003dea082002bf98010016fea00800b7d5004005df2002002ef10010017ee200800bfa1004005fa8802001fe44010
  | 1 => 0xb7d650c0013eb286002bf19430015fec818016fe640c005df3206000af99030005fac81800bbd640c0015eb206002bf19030025fcc6180137f530c009bea986004efd0c300277a861800efe620c005f73106000bb98830005fac41800bed620c00176b106000dfd4830006faa418003bf420c001dea106001bf98430017ecc218002f6610c0017eb086002fd58430005eac2180037e510c001be2886000efd04300077a821800afe600c005bfa806002df540300177c801800bbc400c005ef9806002fe8c030017ba6018013f9300c0077fb2e4006bf9972001efccb900027e65c80017eb2e4003df59720004facb9000efc65c80077fb264005bf9932001f7cc990002be64c80017eb264003ef593200057ac99000efc64c80077fb1e4004bf98f20005fac79000efc63c8001bfa9e4000df54f200077e8790003bd43c8007bfa964003df54b2001f7e859000fee42c8007dea164000fb50b200075a859000fee32c8001f69964001bf98720005fac3900037e51c8001be28e4000efd07200077a839000fef21c8001f690e4000dfd4320006faa19000bbe40c8005de2064002bfd9620035fccb1000b7e65880013f32c4000bf59620016facb100027d65880057e32c4002bfd92200177ec91000abf648800b7f3244000bf59220015f8c91000bbc64880055e3244002bfd8e20025fcc710002fd63880057e31c4000dfd4e20006faa710003bf4388001dea1c4000bf58a20006fea5100037d5288001dfa144000ef50a2000dfcc310002fd6188001bf28c4000df146200077e8310003bd41880057f3044002dfd4220016faa11000bbe4088005de2044002fe8c220007f2611000bef2088007fd9044000bfd9520035fcca900037e65480013f32a4000bf59520006faca900027d654800d7e32a4000bfd91200077ec890002bf644800b7f3224000bf5912002df8c890003bc64480015e3224000bfd8d20025fcc690002fd63480097e31a4000dfd4d20006faa690003bf4348001dea1a4000dfd4920006faa490003bf4248001f72124000ef50920007da8490003ad4248001f71924000fb4c920005fec290006fc6148001bf28a4000df145200077e8290003bd4148001f790a4000fb48520006fea0900037d5048005df2024002ef10120007f46090003f93048007fd9024002fb88120015feca1001afe6508005bf32840009f99420005faca1000b7d65080013eb284002bf19420015fec810016fe6408005df3204000af99020005fac81000bbd64080015eb204002bf19020015fec610012fe6308005ef3184000b798c20005fac61000bdd63080016eb184002bf18c20006fea6100037d5308001dfa184000ef50c2001dfcc41000f7f5208007bea904003efd082001f7a8410006fe6108005fb3084000bd98420005fac21000bf561080017ab
  | 2 => 0x4000dfcc22000bf661100017b3088000bf58440017eac220002f56110001bf2888000df1444002f7e8220003be4110001dea088005ef10440015fcc02000b7f5010005bea808002efd0040017f4802000bbd401000bfca008002efd94400177cca2000b3e6510005deb288002cf5944001778ca2000bbf6310005df3188002e798c400177ac620002bd6310005ceb188000a758c4001778c620003bf53100019fa988000ef94c400077aa6200033d5310001de2988002efd88400177cc42000bae6210005deb108000af588400175ac420002ad6210005de3108000efd48400067ea420003be5210001dea908000cf5484000778a420003bf3210001df1908000ef4c84000778642000bbf6110005df3088002ed984400177ac220002bd6110005dab088000ad5844001778c220003bf5110001df2888000cf944400077aa220003bc51100019e2888000efcc4400077c6220003bd3110001de1888000efc84400077c4220003bd2110001de1088002ef980400157cc02000bba6010005dfa808002cfd40400177ca02000bbd50100059ea808002ef14040025fecb9801afe65cc009bf32e60009f99730005facb980137d65cc0013eb2e6004bf19730025fec998016fe64cc009df3266000af99330005fac998013bd64cc0015eb266004bf19330026fea7980137d53cc009dfa1e6004f790f300277a8798003dd43cc001cea1e6003bf98b30005fac5980037f52cc001bea966000efd0b300077a8598013df32cc001ee9966001bf98730005fac3980037e51cc001be28e6000efd07300077a8398013df31cc001ee98e6000dfd4330006faa19800bbe40cc005de2066002bfd9630035fccb1800b7e658c0013f32c6000bf59630016facb180027d658c0057e32c6002bfd92300177ec91800abf648c00b7f3246000bf59230015f8c91800bbc648c0055e3246000bf58e30006fea7180037d538c001dfa1c6000ef50e3001dfcc518002fd628c001bfa946000df54a300077e8518003bd428c0037f30c6000bf58630006fca3180037c518c001dfa0c6000ef50630015fcc11800b7f508c005bea846002ef9023001778811800bdf308c009fd9846000bfd9530035fcca980037e654c0013f32a6000bf59530006faca980027d654c00d7e32a6000bfd91300077ec898002bf644c00b7f3226000bf5913002df8c898003bc644c0015e3226000dfd4d30006faa698003bf434c001ef21a6000ef50d30007ba86980039d434c0017fb126003bf18930006fea4980037d524c001dfa126000ef50930007be6498003dd324c0017fb0a6001bf18530006fca2980037c514c001dfa0a6000ef50530007be6298003dd314c001bfa826000df541300177c809800bbc404c009fd9826002f78c130015feca1801afe650c005bf32860009f99430005faca1800
  | 3 => 0xe98aa000df0c550006fe42a80037e2154001be90aa000df08550006fec0a80037b605400d7f328a0009f9945002dfcc828002fd64140097f318a000bf58c50036fea6280037d5314001dfa18a000ef50c5001dfcc428002fd621400dbfa90a000df548500077e8428003bd42140037f308a000bf58450006fca22801b7c5114001dfa08a000ef50450015fcc02800b7f5014005fd280a002df54050037f2a028016ff65d000d7f32e8000bf5974002df8cba0012fe63d00017eb1e8000dfd4f40006faa7a0017bf43d0001dea1e8003bf98b40005fac5a00037f52d0001bea968005efd0b400077a85a0006fe61d00017eb0e8000df94740006f8a3a0017bf41d0001dea0e8000dfd4340006faa1a000aff659000d7f32c8002df99640004fccb20002fd6590005beb2c80009f59640015f8cb20002fd6490001dfaa48000ef952400077aa920003bc54900097f31c8000bf58e40006fea7200037d5390001dfa1c8000ef90e400077a8720003bc43900077f3148000bf58a40006fea5200037d5290001dfa148000ef90a400077a8520003bc42900037f30c8000bf58640006fca3200037c5190001dfa0c8000ef906400077a8320003bc41900057f3048002dfd4240016faa12000bbf409000bfda048002efd96400177ccb2000b3e6590005deb2c8002cf5964001778cb2000bbf6390005df31c8002ef58e400057ac72000bbc6390001dfa9c8000cfd4e400077ca720003bd53900019ea9c8000ef14e400177ec52000bbe6290005deb148000af58a4001778c520003bf52900019fa948000ef94a400077aa5200033d5290001de2948000efcca400077c6520003bd3290001de1948002efd86400177cc32000bbd61900015eb0c8002ef186400077ea320003be51900019f28c8000ef5464000778a3200033c5190001df98c8000ef8c6400077a6320003bc3190001df90c8000ef886400077a4320003bc21900055f3048002efd42400167ea12000bbe5090005dea848002cf5424001778a120002ff655000d7f32a8000bf59540035f8caa0002ff63500097e31a8000dfd4d40006faa6a0003bf4350001dea1a8000bfd894001df8c4a00037f5250001bea928000efd09400077a84a0002ff61500037e30a8000df94540006f8a2a0003bf4150001dea0a8000dfd4140006faa0a0017fb4050005df2028002bfd9440035fcca2000b7e65100013f3288000bf59440016faca200027d65100057e3288005bf990400077ea820017be5410001deaa08005ef15040025fcc62000bde63100016f3188000bf58c40017bac620002dd6310001bfa988000df54c4002f7e8620003be4310001dea188005ef10c4001dfcc42000bee6210001773108000bf58840017dac420002ed6210001bfa908000df5484002f7e8420003be4210001dea108005ef108
  | 4 => 0x807de63084016f3184200bf58c2100fbac610802dd63084037e3184200dfd4c21006faa610803bf4308401dea184203bf9882101efea41080f7d5208407dfa104203ef5082100dfcc2108077e5108403be2884201efd042100f7a8210807ef2108403fb1084201fb4842101fea421080afe6008403fd3004200be98021005fac010807f960084017cb004205bf993500377cc9a8002be64d40017eb26a006ef593500057ac9a801b7f54d4001bf2a6a000df55350036f8a9a8012fe63d40017eb1ea006dfd4f50006fca7a80037d53d400dbe29ea000efd0f500077a87a800efe62d40017eb16a006dfd4b50006fca5a80037d52d400dbe296a000efd0b500077a85a8006fe61d40017eb0ea006dfd4750006fca3a80037d51d400dbe28ea000efd07500077a83a801b7f64d4001bf326a000cf99350006fac9a80033d64d400dbe326a006dfd8f50006fcc7a80037d63d40013eb1ea006df18f50006fe87a80033f43d4001bf21ea000df50f500067a87a80037c43d400dbfb16a000df98b50006fac5a80027d62d400dbe316a000dfd0b500067e85a80037e42d4001bea16a000cf50b50006f885a80037f32d4001bf196a000df4cb50006f865a801b7f61d4001bf30ea0019f98750006fac3a801b7c61d4001bfa0ea000cfd0750006fc83a80037d41d40019ea0ea000df10750006fe63a80037e31d4001be98ea000df0c750006fe43a80037e21d4001be90ea000df08750005facb280027d659400b7f324a000bf59250025fcc728002fd6394001bfa9ca000df54e500077e8728003bd43940077f314a000bf58a50006fea5280037d5294001dfa14a000ef50a5000dfcc328002fd6194001bf28ca000df146500077e8328003bd41940057f304a002dfd4250037f6a128002ff6454001dfb22a000afd915002df8c8a8003bc64540015e322a000dfd5150006fca8a80037d5454001be2a2a000bfd8d50025f8c6a80037f5354001bf29aa000df54d50006f8a6a8003bf4354001dea1aa000bfd895001df8c4a80037f5254001bf292a000df54950006f8a4a8003bf4254001dea12a000bfd855000df8c2a80037f5154001bf28aa000df54550006f8a2a8003bf4154001dea0aa006fed4150016fca0a80037f64540019fb22a000df99150006fac8a80037c64540019e322a000dfd8d50004fec6a80037e6354001beb1aa000df18d50006fe86a80033f4354001bf21aa000df50d500067a86a80037c4354001bfb12a0009fd8950006fcc4a80037d6254001be312a000dfd09500067e84a80037e4254001bea12a000cf50950006f884a80037f3254001bf192a000df4c950006f864a80037f6154001bf30aa000df58550006f8c2a80067c6154001bfa0aa000cfd0550006fc82a80037d41540019ea0aa000df10550006fe62a80037e3154001b
  | 5 => 0x9531005faca9881afc654c401be32a62009f19531005fec898816fe644c401df3226200af99131005fac898803bd644c4015eb226205bf19131006fea698803de534c401bea9a6200f754d31006baa698803bf434c401dea1a6200bfd893101df8c4988037f524c401bea926200efd09310077a8498803df324c401ee9926201df9453100ef8a298803bf414c401dea0a6204fdcc53100fbc6298802ff604c4057e3026201bfd9431035fcca188077e650c4013f3286200bf5943100efaca188027d650c4037e3286201bfd903102dfcc818807be640c4015f3206200bf5903100f7ac818802bd640c4037e3206204bf98c31026fea6188137d530c409dfa186204ef50c3101dfcc418807ee620c401773106200bf5883100fdac418802ed620c401bfa906200df548310077e8418803bd420c4037f3086201df9443100ef8a218807bf410c403dea086201f7cc43100fec6218807dd310c409fa9886202bf9803100ff4c018802fa600c4017eb006201fe58031005f2c01880eff65c840d7f32e4203df99721004fccb90802fd65c8407beb2e42009f5972101df8cb9080eff64c840b7f3264203ef993210057cc990802fd64c8407deb264200af5932101df8c99080eff63c84097f31e4200bf58f2101df8c7908037f53c8401bea9e4200efd0f210077a879080f7f52c8407f72964203df54b21007daa5908036d52c8407dfa164203ef50b2101fdc6590803ed32c8403bf28e4201df147210077e8390803bd41c84057f3064200bf5832100dfecb108077f65884033fb2c4206bf99621005facb10806fc6588403be32c42019f1962100dfec910816fe6488403df3244200af99221005fac910807bd64884015eb244201bf1922100dfec710812fe63884017eb1c4201bf18e21006fea7108037d5388401dfa1c4200ef50e21005fac5108037f5288401bea944200efd0a210077a8510806fe6188403bf28c4201df1462100f7e8310807bd4188403fb18c4200fd4c62100fde431080ff721884057f3044200bf58221005feca908037f65484013fb2a4206bf99521005faca9081afc6548401be32a42009f19521005fec890816fe6448401df3224200af99121005fac890803bd64484015eb224205bf19121005fec690812fe63484017eb1a4204bf18d21006fea6908037d5348401dfa1a4200ef50d21006fea490803ee5248401bea924200fb54921006daa490803bf4248401dea124200fb8c921007da64908077e5148403be28a4200efd05210077a8290803f63148401fa98a4203fdc852100fdc4290802ff60484057e3024201bfd9421035fcca108077e65084013f3284200bf5942100efaca108027d65084037e3284201bfd902102dfcc810807be64084015f3204200bf5902100f7ac810802bd64084037e3204201bfd8c21025fcc610
  | 6 => 0x1df1968200ef4cb410077865a0803bf51d0403df28e8201cf947410077aa3a0807bc51d04039e28e8205efd83410077cc1a080abe60d0401deb068205ef1834100dfecb2081afe65904017eb2c8201bf19641005fac920802bd64904097f31c8200bf58e41006fea7208037d5390401dfa1c8200ef50e4101dfcc520802fd6290401bfa948200df54a410077e8520803bd42904037f30c8201df9464100ef8a320807bf419040bfba0c8202bf98241005fac120802ff6550401bfb2a82009fd9541035fccaa0802fd655040d7e32a8200df19541004f8caa0803bf5450401df2a28200ef5514100778a8a0802ff63504097e31a8200dfd4d41006faa6a0803bf4350401df21a8200ef50d410077886a0802ff62504077e3128200dfd4941006faa4a0803bf4250401df2128200ef509410077884a08077e5150403be28a8205fdd054100f7c82a0802ff60504057e3028200efd95410067ecaa0803be6550401deb2a8200ef1954100678caa0803bf63504015fb1a8200ef98d410077ac6a0803bc6350401dfa9a8200cfd4d410077ca6a0803bd53504019ea9a8200ef14d410077ec4a0802bf6250401df3128200ef5894100778c4a0803bf52504019fa928200ef949410077aa4a08033d5250401de2928200efcc9410077c64a0803bd3250401de1928200efd85410076ec2a0803bf5150403df28a8201cf945410077aa2a0807bc51504039e28a8200efd81410077cc0a0803bd6050401de3028202af1814100dfeca2081afe65104017eb288201bf1944102dfcc820802be64104097f3188200bf58c41006fea6208037d531040bdfa188200ef50c4101dfcc420802fd6210401bfa908200df5484102f7e8420803bd42104037f3088201df9444100ef8a220807bf4110403fb2088201ef5044102fea822080afe60104017eb008204bfd9731035fccb988137e65cc4013f32e6200bf59731026facb988027d65cc4097e32e6204bfd933102dfcc998813be64cc4015f3266200bf593310277ac998802bd64cc4097e3266204dfd4f31027bca7988137d53cc401eea9e6200d754f310277e8798813bd43cc4077f3166200bf58b31006fea5988037d52cc401dfa166200ef50b31027be6598803dd32cc403bf28e6201df147310077e8398803bd41cc4057f3066200bf5833100dfecb188077f658c4033fb2c6206bf99631005facb18806fc658c403be32c62019f1963100dfec918816fe648c403df3246200af99231005fac918807bd648c4015eb246201bf19231005fac7188037f538c401bea9c6200efd0e310077a871880efe628c4017eb146200dfd4a31006faa518803bf428c401dea146201bf9863100efca3188077c518c403dfa0c6201ef5063100fbe6318813f7318c4057f3046200bf58231005feca988037f654c4013fb2a6206bf9
  | 7 => 0x288037d5294401be294a200efd0a510077a8528806fe6194403bfa8ca206fdd4651015fcc128802fd6094403bfb24a201df9925100e7cc9288077d64944039eb24a201df1925100efec7288077e6394403beb1ca2009f58e5100ef8c7288037f43944019fa1ca200df90e51006fa87288033d4394401be21ca201dfd8a5100efcc5288077d62944013eb14a201df18a51006fe85288033f4294401bf214a200df50a510067a85288037c4294401bf994a200df8ca51006fa65288037c32944033f30ca201dfd825100efcc1288077d60944013eb04a201df18251005fec8a8816fc64544017fb1aa204bf18d51006fea6a88037d5354401dfa1aa200ef50d51005fec4a880efc6254401bfa92a200df549510077e84a8803bd425440dfba8aa201df94551005fec0a880afc605440d7f328a205bf9905100f7cc828802be64144017eb20a201ef590510057ac82881b7f5414401bf2a0a200df55051036f8a828812fe6314403ef318a200b798c51005fac628807dd63144016eb18a206dfd4c51006fca6288037d531440dbe298a200efd0c510077a862880efe6214403f7310a200bb98851005fac428807ed621440176b10a206dfd4851006fca4288037d521440dbe290a200efd08510077a8428806fe6114403bfa88a201fd9445100efaa22881bf551144057f300a201fe98051005f4c028802fd6014403fcb00a200be5805100efec8288077e64144039f320a201df5905100e7ac8288077c6414403bfb18a201df98c5100ebcc6288077d63144013eb18a201d758c51004bac6288077c6314401bfa18a200cfd0c51006fc86288037d43144019ea18a200df10c5100efec4288077e6214403b7310a201df58851004fac4288076d621440136b10a201df18851006fe84288033f4214401bf210a200df508510067a84288037c4214401bf990a200df8c851006fa64288037c3214403bf308a2019f9845100eecc2288077f6014403bf300a201de9805100efac0288027d6014403bcb00a2009e5805100ef8c028816ff65d040d7f32e8205df99741004fccba0802fd65d040bbeb2e82009f5974102df8cba0803bf54d040bdf2a68200ef5534102f78a9a0812fe63d04017eb1e8200dfd4f41006faa7a0817bf43d0401df21e8200ef50f4102f7887a080efe62d04017eb168200dfd4b41006faa5a0817bf42d0401df2168200ef50b4102f7885a08077e51d0403be28e8202bf98341005fac1a0817bf65d0401df32e8200cf997410077acba08033d65d040bde32e8205efd8f410077cc7a0803bd63d04015eb1e8205ef18f410077ea7a08033f53d0401df29e8200ef54f410067aa7a0803bc53d040bdfb168200ef98b410077ac5a0802bd62d040bde3168200efd4b410067ea5a0803be52d0401dea968200cf54b4100778a5a0803bf32d040
  | 8 => 0xfd4d420077ca6a1003bd53508019ea9a8400ef14d420077ec4a1003af6250801dfa928400cfd494201f7ca4a1003bd52508019ea928403ef149420077ec2a1002bf6150801df30a8400ef5854200778c2a1003bf6050801df3028400ef5814200778c0a100abc60508077fb288406bf9944201efcca210027e65108017eb288403df59442004faca2100efc651080b7f3208400af99042025fcc621002fd6310801bfa988400df54c4202f7e8621003bd43108077f3108403dfd484201efaa42100fbf4210807f72108403ef5084202fda8421006fe61108017eb088402bf98042005fac021012ff65cc80d7f32e6404df99732004fccb99002fd65cc809beb2e64009f59732025f8cb99012ff64cc80b7f3266404ef993320057cc999002fd64cc809deb266400af59332025f8c9990137f53cc809bea9e6404efd0f320277a87990037f52cc801bea966400efd0b320077a8599006fe61cc8017eb0e6402bf98332005fac19900eff658c80d7f32c6403df99632004fccb19002fd658c807beb2c64009f5963201df8cb1900eff648c80b7f3246403ef992320057cc919002fd648c807deb246400af5923201df8c919002fd638c801bfa9c6400df54e320077e8719003bd438c8077f3146403dfd4a3201efaa51900fbf428c807dea146403f7cca32027de6519006fe618c8017eb0c6402bf98232005fac119002ff654c80d7f32a6400df99532004fcca99002fd654c801beb2a64009f59532035f8ca99002ff644c80b7f3226400ef991320057cc899002fd644c801deb226400af5913202df8c8990037f534c801bea9a6400efd0d320077a86990037f524c801bea926400efd09320077a8499013ef324c807ef1926400bfd853200df8c299002ff604c8057e3026403bfd9432035fcca1900f7e650c8013f3286400bf5943201efaca190027d650c8077e3286403bfd903202dfcc81900fbe640c8015f3206400bf5903201f7ac819002bd640c8077e3206404bf98c32026fea6190137d530c809dfa186404ef50c3201dfcc41900f7f520c807bea906403efd083201f7a841900fdf320c807f71906403f74c832027da6419003cd320c8037f3086403fd98432005ecc219002fd610c807fab086400bd58432015fcc01900ffa600c8017d3006400bf5803201ff2c019002f9600c80b7f326a200bf59351025fcc7a8802fd63d440dbfa9ea200df54f510077e87a8803bd43d44077f316a200bf58b51036fea5a88037d52d4401dfa16a200ef50b51015fcc1a8802fd60d44017eb2ca205bf9925100f7cc928802be64944017eb24a201ef592510057ac9288037f5494401bf2a4a200df55251006f8a928812fe63944017eb1ca200dfd4e51006fca7288037d5394401be29ca200efd0e510077a872880efe62944017eb14a200dfd4a51006fca5
  | 9 => 0x8013eb1ea406df18f52006fe87a90033f43d4801bf21ea400df50f520067a87a90037c43d480dbfb0ea400df9875200cfcc3a90037d61d480dbe30ea406dfd8352006fcc1a90037d60d48013eb06a406df18352005facb290027d659480b7f324a403ef992520057cc929002fd6494807deb24a400af59252025fcc729002fd6394801bfa9ca400df54e520077e8729003bd43948077f314a403dfd4a52037dea529006fe61948017eb0ca402bf98252005fac129002ff645480b7e322a400dfd5152006fca8a90037d5454801be2a2a400bfd8d52025f8c6a90037f5354801bf29aa400df54d52006f8a6a9003bf4354801dea1aa406fbd495201efca4a9002ff61548037e30aa400bfd8152015f8c0a90037f6454801bf322a400df59152006f8c8a90037f63548013fb1aa400df98d52006fac6a90037c6354801bfa1aa400cfd0d52006fc86a90037d43548019ea1aa400df10d52006fec4a90036f6254801bfb0aa400df98552006fac2a90037c61548033e30aa400dfd8152004fec0a90037e6054801beb02a400df18152035fcca290027e651480b7f320a403ef990520057cc829002fd6414807deb20a400af59052025fcc629002fd631480dbfa98a400df54c520077e8629003bd43148077f310a403dfd485201fdca42900f7d521480df6a90a401bf98452005fac22900afe60148017eb00a405bfd9742035fccba1002fd65d080b7e32e8400efd534202f7ca9a1003bd54d080bde2a68404bf98f42005fac7a10037f53d0801bea9e8405efd0f420077c87a1003bd43d080bde21e8400dfd4b42006faa5a1006fe61d08017eb0e8402bf98342005fac1a1017bf65d0801df32e8400ef5974202f78cba1017bf63d0801df31e8400ef58f420057ac7a1017bc63d0801dfa9e8400cfd4f420077ca7a1003bd53d08019ea9e8400ef14f420077ea5a10033f52d0807df2968400ef54b420067aa5a100fbc52d080bdfb0e8400ef987420077ac3a1002bd61d080bde30e8405efd83420077cc1a100abe60d0801deb068405ef1834201dfecb2101afe6590807bf32c84009f99642005facb2100f7d65908013eb2c8403bf19642005fac921002bd64908097f31c8400bf58e42006fea7210037d5390801dfa1c8400ef50e4201dfcc52100f7f5290807bea948403efd0a4202fde8521006fe61908017eb0c8402bf98242005fac121002ff655080d7f32a8400bf59542035f8caa1003bf5450801df2a28400ef5514200778a8a1002ff63508097e31a8400dfd4d42006faa6a1003bf4350801df21a8400ef50d420077886a10037f5250801bea928405fbd094201f7c84a1002ff61508037e30a8400bfd8142015f8c0a1003bf6550801df32a8400ef5954200778caa1003bf63508015fb1a8400ef98d420077ac6a1003bc6350801dfa9a8400c
  | 10 => 0xc929802fd6494c09deb24a600af59253025fcc7298137f5394c0defa9ca603bf98a53005fac529806fe6194c017eb0ca602bf98253005fac129802ff6454c0b7e322a600dfd5153006fca8a98037d5454c01be2a2a606f7d4d53026fca6a9802ff6254c077e312a600bfd855300df8c2a9802ff6054c057e302a600dfd9153006fcc8a98037d6454c01be322a600dfd8d53006bec6a98037f6254c013fb12a600df98953006fac4a98037c6254c01bfb0aa600df98553006fac2a98037c6154c033e30aa600dfd8153004fec0a98037e6054c01beb02a600df18153035fcca298027e6514c0b7f320a604ef990530057cc829802fd6414c09deb20a600af59053025fcc6298137f5314c09ef298a604df54c53037baa62980efe6214c017eb10a601bf98453005fac22980afe6014c017eb00a605bfd9743035fccba1802fd65d0c0b7e32e8600efd534302f7ca9a1803bd54d0c0bde2a68600dfd4f43006faa7a180efe62d0c017eb168601bf98743005fac3a180afe60d0c017eb068605efd97430077ccba1803bd65d0c0bde32e8600efd4f430067ea7a1813be53d0c01dea9e8600cf54f4302778a7a1817bf62d0c01df3168600ef58b430057ac5a1817bc62d0c0bdfb0e8600ef987430077ac3a1802bd61d0c0bde30e8605efd83430077cc1a180abe60d0c01deb068605ef18343025fecb2181afe6590c09bf32c86009f99643005facb218137d6590c013eb2c8604bf19643005fac921802bd6490c097f31c8604dfd4e43026faa721813bf4390c0befa1c8603bf98a43005fac521806fe6190c017eb0c8602bf98243005fac121802ff6550c0d7f32a8600bf59543035f8caa1803bf5450c01df2a28600ef5514300778a8a18037f5350c01bea9a8605f7d0d430277c86a1802ff6250c077e3128600bfd854300df8c2a1802ff6050c057e3028600efd95430077ccaa1803bd6550c01de32a8600efd8d430073ec6a1803bf5350c019fa9a8604ef94d430077aa6a18033d5350c09de29a8600efd89430057ec4a1803be6250c01deb128600ef189430077ec2a1802bf6150c01df30a8600ef5854300778c2a1803bf6050c01df3028600ef5814300778c0a180abc6050c097fb288606bf99443026fcca218027e6510c017eb288604df59443004faca21812fc6510c0b7f3208600af99043025fcc6218137f5310c09bea988604efd0c43027bc8621813bd4310c0beea188603bf98843005fac421806fe6110c017eb088602bf98043005fac021816fe64d48017eb26a406dfd5352006fca9a90037d54d480dbe2a6a404bf98f52005fac7a901b7f53d4801bf29ea400df54f52036f8a7a9003bf43d4801dea1ea401bf98752005fac3a900afe60d48017eb06a406dfd9352006fcc9a90037d64d480dbe326a406dfd8f52006fcc7a90037d63d4
  | 11 => 0x2000803c00000c0008000000003000000c000000000000000000200200000000010000018008001000000000000a0000068000001000000c004000004000400000c00000000080010060000006002000000c00e003000800c004000000801c008002000800000c000000000000e0100000000000000001000400000100000000020060000004002001000000000000200100000060030000000014010000000800800500100000040070090000008000000800c006000004000c0040070000004002001001000000000b00080040000020000000008004003000000600000580040020050000004000000002000400a000000000000800200080000000000000004000000000800000e003000000400000a000800000000000200300000000008000002000000000000a0000000014002001000800000000200000040040000000000000000000000001c0020000000000001000000000200200100000020020000000000006001002000000100000000000070040004000000000000000000400180040020000000004006006000000000a00000180000000000000004000000000000800400100000000080000010000002000003001800000000280080100000028000002003000000000400000680000000000018004000000000000000400200080000080010010010000000000000000400700000040000000008004000000000000c00800000180000040000000004000003000000000400000180040120040010000000003001800000200300280080040020008018008000002003000200100100240040010058038000000000801c0080010008000000000005000000000300080140060010000004000000000000000000000c000c00000500100000220010000030000004025fcc7aa002fd63d50077f316a800bf58b5400dfcc3aa002fd61d50057f306a800bf58354005facb2a016fe649500bbfaa4a806efd52540067ea92a012fe63950017eb1ca803bf98a54005fac52a006fe61950017eb0ca802bf98254005fac12a01bbf545500bbf2a2a800bfd8d54025f8c6aa002ff62550077e312a800bfd855400df8c2aa002ff60550057e302a806bf9945402dfcc82a0177f541500bdf2a0a805df550540377aa82a012fe63150017eb18a803bf98854005fac42a006fe61150017eb08a802bf98054005fac02a016fe64d4c017eb26a606dfd5353006fca9a98037d54d4c0dbe2a6a603bf98b53005fac5a9806fe61d4c017eb0ea602bf98353005fac1a981b7f64d4c01bf326a600df59353036f8c9a981b7f62d4c01bf316a600df58b53004fac5a981b7c62d4c0dbfb0ea600df9875300cfcc3a98037d61d4c0dbe30ea606dfd8353006fcc1a98037d60d4c013eb06a606df18353005facb298027d6594c0b7f324a604ef992530057c
  | 12 => 0x5d12e802a6d80000ac8e020003c18f24f2400011c0000ddc31c00000000009d33cf0000000000000000000000000020c8fb40724e7a5acfd22ea2780b606184794779aac9e417505b8cc4b3458600019dd2ca6fd315000000000000000000000000000000cc67a91149d7c0003aa19c1970498000499000000004f00005a53020002299ef8e400080209b0129400042692500000003f800000000e90001d20a0600027c002532a2ef2958e687a62bb104a31d046891000000000000044f0000f480000000a580004163310034e1c24635e1020cf69721ab0e3800000000000000007b400023e84144510000f305d64dc1511dd8000000334000043690800020c0b500001da00012ea44c02c0000efa00040a80000007d800012411120000898000c8a7f616b14c40083fc00000000004da48e166000044d2a58000002004800001a00000000000000000010004004004003000000a00000000000060010008014000001000800c00800000000000100030008000018000003800c0060100000024004004000804c0000010038000000000000000000600800080080020000038008004000000000800000000780180000000028004000000000001400000100000240020010070000000005001800000000100080000040000000000000004000000c00000c000801000000100080000000050000004004000001000c0000010008000002000003000c0020020000000000003000000000000a00180000020030000004002007000800000200200380000000000008000000000000800800a000000800c004001003000800000300080180040000010010000000002000400000400a80000020000060000000000000000400200000000040000000028010000000000000000000000080000020080000004000000000801400200700100200020000020000002001000000c00000b0000014000002000000400c0000020000000000000000000000400500000120020038018000001000803400000100400000000050018004004005001000000000300180000000000000008000000001800c000000000800400000000100040020030028000014000000800c00e00900180040000000010000000000000000400200000000080000030008008012000002804800200100000000000000000018004008001800000800000000140020030018018000000001800800000100200100000190028004000001000002000000200100000020010020008000003000000c0000000010004000002001800c000004001800c00800100080180000000000008002000001000001600000480000020010020018000001002000c00600200180340000000008000000003000000000000000000100000000000010002001001803000000300100000020060008004002
  | 13 => 0x8000000000042051e31043e0218dd492b301210c0000003e880000001cc0d48000000000455927cafa69000007bc4de0000000000a3c958000130c0000000000000000465000830800000000000000b864314f9f0c0008b400000000009b60b9800000000000000000000000000000ed413d0409bbd1800000001da4c3e393144800000000047f0c5c00070800023100004633ad8000d2c2f62a30000000000000000000000000000000004a70000000b820001a300000000b04908000da80003260000a1c0001e89c18000000000000000000000020a40000000000000fbe1780b28a040000002bc80007c2000000000000033f25980000008091dd00000000004b509200000001c10000000000000000000090413b800092400010700000000000f0943d09e70a00020282da26906980010a200006b994c7e8821061800000019a0000000bc000000000008328c91bca1b00006d61ec043cdcc0001a9000000000000000003ea0cb43f158c0005a13ce000000017a00004e060a9cc00017780006a300000000001553f203c80000000000000000000387800000000000000000000000441fec00000000000001ce55c000000000000000000000001d10270000f60000000000000026b0000df437e10a00000000007d700c1d6000079300022640000000000000ea42552100904ef20f000000012527000f88000566000346800000000015f00000005fc000000014e3ef20a8000000000000000000035743d800126c0004b3a4351825a2000000000000033388d4f8a000254000000071600000003b69b000015088129ab1a504c86321090001b08000000000000000000000005c00004d11fc800034e000000000000000000000000001640f800013a40000000000000000000000115000041ba4091fa000000129400000039b00011ae4c448b11dc3aa95f06089591da0004ae8000d5e65100000000005bf0000d7c0001bb4a28d54ae831319a9b540000004ae000000000033c162c000000000000000059b0000f2000022a000000128040224280008da665000023400000000000000000003a30398bee000263800004c567000081000004500017e40007fa0000000e387cc00000012fc0000000f6ccae2c728614d01045943049b109360db03c88e46cc37c35b19080000100000000000000000000000053b479808050e711000000000080525f800000070937f00012b420c3ab25b00c44d400002c400000000000008480000000000000000000177507a00000017a5072557000089447805400020b4f025c500020e800081d0000000cfe23200d0ea4a441e6045942020891100000000003c000000000000000000000000000000000038a16f08380000000004cf8fe000000000000008b0000000000045668c0000000c145370000000000808
  | 14 => 0xd44310ac0004d6015002ca8e00000000008e2000116000000045f21d089800000000022f40005100001a38f04000000052400000000000000000af00000010ac000000000000093b00a000000097c0000000ea60002e7800002421d0719d0c0000000000f74cb20002da000000000000000000005f8338a0580000002801718000000000000017e000299800000052a00000000000000c88000fd00000000000000000000000000000000017a800041d0000000f120000e72638ccc21426413c5314000000175000000000000007ca9ce0000d10c3a85d0af0a70cde02800021e08a000021f94984e212a47100000006c632700012f400000016b09d600000000010dc00000000000000000002480df07c1300992cb1e00010280000000003550decd9c1582a9000000003209f000000000000010a8dba00046ea60061e0000268a94ee06282271d00d0e6ca1dc9e5800061616aa1d8d92000124800000034b00003e80360c449311a4f30434000000000000000009980001a800002d000000000000000000000000000000000000158517c000000000000000015b00002e20004a70000000000000000027231800000000000002f31c8845a00000000000008ea07016bcf0873402922e530e67412e8c0cb540000c38000fd600000000000000000001a0000000000000000000000001d680003d027f189c000852205800000000048614a08384f434f80000000001e39f6c000000000000082456a15a18cc8c82942d9846c0000002088000000000266000000061a00019cc51a0000001880000000000000134a000000000000026400007f000000018300009f2000000000011e00040580000000001ae000000000000000000000003f0a10055e00000015a000000038a8000c706d00d71d800004263160474cc81ec0ab19512702bc28d0b4400000035d9388b720001db8000d1244024c8b1115400000008000009cd00000000000003090000000000000000000095b07c11c8000000289800000000046c10c89f84930000ab400000019e000022a13f000000000000001880003a0000000000000020d0000e5000000000000000009193c8800129800000000000000e43a201b464400021100006e00004de94b02b630000009d80000001a8000076200300000009b2000000000000000000000000000550000db47764b2283848800047a31b25e4d7a9390000000e3600009d800000000000000000000000000000b48000000000000000035d000000010e1938f9cf1800030809683ce52f395800133c9972379ce81d441016f0000e92000000000104a0000fa0000000000000000025c00017c0000000000000000068e9182c2204c00000000000000000000000000000000340800000075900007a480000021c19d520a13a3570ad4d1035e3528de
  | 15 => 0x48fa00025f000000000000005ed36e00000010300000f92dd0000ffc9b3309800000039c33e000073a39500000000008ff000066000022400000011e200031d270c00011e0001e00af60003d387180000aa000000000018812f0000c0a5a700000000000000000490b60000000000040200000e00f8000538000084000000000000000000003e8157800084622400000006ec000265000068400015e800000045e00012927b200006500000000000ca0ede000000000072e00000004980004cb0001adc00022e1b3800000000032aa354440785000000074a06113093bcd44934216800012c0000000000574000000000073e14d000000049e6f63bf00000005703ea0000c441343a10000f6a5814280464a046c84170ccc31a91700000005f205a0b500008aa75100003f43264363ea8704f2a0694e2823095807b0000000af83292b992b4c1670717d89082cc6441ed274009092e1f18b98e7a7fd27a800000000027d1ac8dc00000000000000000000000000000000006bc0000002f90000be00bb00000000006850000f34da20000000000000000396000000060000021d417c03000000008520003e300011ac000000000000000026f80000000001c180000000000000000152901000000000000000000000000000000000000000000000106200000000000000002fa000000046834910f4000000000000000e00039c0000000532000000000000047400006860002e0005d0c400000000000000000000000c1a53c0439cc80006f0000000000039600000000003f600024f0f4a00000000085e25390171cb400000014a94704305532ac26892aa0cc1411a440009ae0001f28000000000000000040a000000000097145395b80002a10000000396000000016400000017e9b1d01c3fe40c000000000017600b00000003fb80003fe3851d300000006d73a788ec3200004a180011765710002130a307171b40dd80000002b002d800018a17f0000000047079a155078000000000000000036f9390000000000171ce160002469a85262000326a5f53383e400016f800000036d88f8e268730629a781ba5b700023d400000000000012268ce42200003d000026300000009af0e380005e6000000000000000000013380000f100027283705211720000836000000000000000000000000000000000000a6037f00012f000000042f0a380000000001bd400069c245a39400000000004b11c20000000000d580002230d6c00000000009d00000003678000ef626d000000000086f0000c34aec2d900000010d220728f80000000000000000d4835d000000000000043e80013041ea36f084400068f32408a028c000008800000000036591f800000000018d400000000000000009522bfa214892739000000000038103f83180009560000b409466a
  | 16 => 0x7e5214111ca5a04603300000000001ea964d1080000a400000000003350000b6403905117fc0008e4000012c0000003c380010e27941519a648822dd0cb18c428e0de00008c000000019500000009903458a18e7c67e0000e1c4961e0000237c00000000000000008f81df00000008bf000000019c000260000028000042f9acc7d203400000000000c70a900000000004cb0000df8308000000000000031480000800000000000dd038b26d800000000000000000008341c52204000000000186c744117000000000047b0000aace3200000000000003ed2e81ed821631e4d3000000000000023dc00000041d86f4b00000000233c57032f1220000e6609d0d180000000000f900000000000001edd0c228b0001424b9274a000000124e92f00703acab200049f06c007a0002d59bc83125e200000001e80700001d2c0003204a80b492e818b0000000000000000000053a000071000113e00002981cc0001ab3979c14446000000000000028c00000001586cc00000000008ec3bf92540002903d52584b240000000d0138c00034e8000cd2000000000000097722509c058423a0000000a2a49744e8994000000443800000000018081a80000003f38568000000000000000000000000008b400045b00011d600014f0c5039e56927089ecbaa14a000000047a00038604000000004df0f780000004548000d0c000000000066800000007940009b40121a60e4a00000000009dc00015f80000000000000dc800000000000000000000000000000623000000000056504b84586fc0000000e840002790640000aba00000000007d85ad0000000fc0000000065c0000001530000000179000000063a00039400000447312eb079030287f02500e135a3f243004c4000000123a5080000002ce94b800000000000000002bd00019c8000000000000050a2e031a047073c00001d80000000000001aa400058200020cc000417371025000000000000000003d9217099c3fa721000000019a9a94650000c3219231680002205c20000000000000153921c0000003b18000c2223f0000384e3a000000000086667044009440001f600003f0a7e64a2cb00000000003cb84c0c9e0763f180000000000001f4c00000000015506f00003b880009821aa00013cceb80000f59c48bbe00000000004d42db00025cc00000000000000000000001d98a8600000000009ca0001d802612580000000000c2a5a500000000004180fc00000000001968000000000237000112a00000000000000000000000000000000000000008e191800066e00000018e400000000000000000002570c580001dc23e0000000000000132476a0003de1f20000000000000063400f45c1b0c1b8000000000000081e00000000001e200000005ee5171c6897c95e0000bf95
  | 17 => 0x2f505413543b80002306474c880002d089b22280003361c2000000000025700000001120000000000b2e8ae1d025210221fa3948e9c0007301f580000007ba41124b40000000000000000778000000000059900000000000000000000000427000051417000036d0000000898000000000000032900000000000000f2c7121631a08be930889031b870000000047c8000000000000025523a0ff422800000059f0000d6000043c006000000044b3cf91d89a400000000005ce0000002220c8c5233ff8000000000000209800000000002690f4000000000000000000012d4000000000000096c0ef0001d380a023427f887927e3a30a5a5fcdc65ce11995b463e3920b11b140005bd1a8894d01e9c700001f00007181361d9cfe200000026802b27a2120000000045d0680678000000000000121e0002a223f000000000000000000004bd8fc069c0ed1a780011a40000000000fda0000000064000000055800000075d00001580001370000000392000000000093429b2f280005b40000000c980005d744b1fd0000841000119876c4733d881d06d683800000000004ec00000009c689a10d00000000ec000157cf9e72e2f4000000088314180001b000021280009aa0004c480000007fc00000000000003020ce800000005080000000004c6a49017a297000071000002537380008428011c420646dc7e6000000000000047312204162a82f880000000002e59034aac45c0000084970000202000000081f14995bc0002cc2681eb03188b500021b4bd68dc2ee000000000037f8f800000004d380000004e80002160ba248f2fd907c95600033ea590ae474c04f1a5c3788921ac981c26c0490829c4110401e0e1a6e4ee41b52530b250940fe24e973403e18009e08c4ac8000000000000000042d00005300000000000000000000037ce080000000000dee000000000136406715897480000000000ffc33890e000153c000000000225cc6400008d0c5400043b36ca30938230a1a600000e23544b194a459a03c1d401f40004a040d0000b869ac00007eca405b500005f48bc29a0002234af0998000000000000024623b87360a81f500000008da3d30000f66000109a55071800027b82b40008a52dd8000000000000134c44200000000010000000000000000000000254ce7663b086047ceea0001d615dc0006e900000000f00000000000ee600028a00005d07f92310b5c00083517726a82ba4911390000a0820238a000000011400022cc0000002018000b1028a2b600004b20d12fa80000009070000000146000000000000000026b9fa800000044a000000000008326200005fa49512a464269500000003c619f0c28000f560001608e4514069b2c612a892c48e3dc83240ea62f00000012d200042400002c07500000000cc064000000000000
  | 18 => 0x4c600000000000001d941d074700011c075c4dd49e9624a0a50d00000000000004b10000ed061c00026ec0000000000000000437000000000000000000000000002a2a34c000000000160c00032400013d90b6000000000044402d468a15122809f3f61a9834c00012295200000003f7024c00083f0000000000000466142c5fe33e18d86e40000001928000000000345000059c54a00000010d44a10000ee0bb294f0d8800000046b270073425e0360002314000000000000000000022ca2c400017c00000000000000000000fb23f33c68d093467c4000000000058a00000002e80604b700001ee33b3e59c9c00051b0001a4c90600030198200be5a609280000000d9276a2844fe000000000000000000000000000000000000000143453000000053618100002b800000000000000001251d50000000203000000055b3ee1884cd62c526500000001761e90000204444000206caaa73f42e00000000001ef80000009bf19b000025a000000247cf7e09000000000000000000c481a86fa2830980308000000000034800000024246c600000000003ae8a31d59db53629930a216342dc4311e28fd419467a2d70bf07ac15420a24d46ee19930c000118c0000001e40a6a00000000000000000000f9800000033680010e4000000000000000000000002660912cf000000000000e8000dc80003f100012b22e900000000000000000000000000000000000000000000000003530159e640002cb0000f70bde00000000001366e51e79af86de20f1340e60b98000117a2905ca0cf0e9205c2ce9bc4781ef40000853c58000f0c34d000000000000002f03d400000000000004a41b620791a830c4810ef9a680000a61f70ae533400001a80000000002360000000077000000122a000000000000000000000012140000001c9800000000000010c600000010047945f60ec1784c4a77416e00005320004b78000ba600032b000029e1611c81f581a421906d000000060c28b000000057500000011164fb00000011b69c43370000000000000000000000000022b40000000c100006e215000021ac0004d80eb000000033946ca28915e36a000000096842f00000000000000d625048a42431520ff416a92333c86e8f9245408080cc0000000001ac00000001b00e1036466c000035800000000000000000000000000000000000000000000000000000005bc0001f3528c80c2731b34ec858516f8000000000022000000000030a00007842364e48000df298b0001769296000000209cfa45400890720ff08141501ad08ae0004e10d900003ce30300000000830000000cb000000000000000000000000be600000000005e40d5000000007e62b18894e836800020700003ba00000000000000000000000a9a0004d0a34036e4350000ec8c600b20001
  | 19 => 0xda40000000000000000380412000000000643300000000004c9000105050a000000000000000000009bc4b700002710b2587000244000000004224c0000000000000000000032f80001802b00000000f1c04340680dc0001da481a238d7e000000201042e0001991bc4b704e74080e1888630b43227200fc5a9000000000002305980000000000000000ebc4ea00000012003c400016c400a0000002350a2200047922280008490000000000000369906800000013f1c6805e0002c702b80000000d0000104063c000000046e00000000002400000000848ec2000000000129a06b3dc110800000010b00004ea47400014f4dd626317a18f840687400000007860000000dd00000000000d209000002ce10f933a5a30001db06d824e2580960b2282b0ab93140001414cd94940002c0031800002c2b70000f880007a00000000a48983258a4cc00000000000007e23ad4238e9068a8ba0000000d6a0004c78d94000000245239d2d0806000000000000032d000120c00000000000000000c180000000002f691fc0a26a0171000102400000012e40004a44cc98fc0000003f900000000000d1000090c0003aba42c37c8f64161df02a69a82bf1538b94349026224d236000000069400000019599780008c3000022825688c32e800000021f3d78000f9c000000000055800047a1e290e00000000e647a80002610000000000000000000089c000000000000000015880003bd000000000012805c96540006b841b000058c20600000000006174bb1b4835a00000010e5288000148800099e60f49b8eccc3c0004b800007d09c02e200008c200000011800002aa0000000b6c512000000000000000007b40000001de00002d63c1465800000000045b9598fde2ae014800000000020f00001320ee0000000000802000000065c000000000000081c00006380000000000a000000002ff1cd467a7bb37a1c9000091e1d780000009b84d200012ae0000000000000000000133400015f3d18001244273000000109c375000000000042349d1890594702354000000048900007cc0008cd00007f800000024f016c0009600000000000000000000000085302b8000d824844a895301f6000000096c3668e30a884845865a01441eb40004053fa8c105ea2d424c0248e5445b000000000000000000000005ee0000000000475000000000000000980004f48de0000b8c0d00003c4000000070d0000000ab4000000178cc5c000000049cf8e11138f9eb80000000001b8400027d00000004102273b10000aa279d3a283943ee73c3bb81bc21a2544019d34bfa28400024a0f1e53e000077828419523c19840000003bd000080e63d00009e00009ba00000002fc000000000000000000000000000000001c788260001b120bc0002502f3809c4f80000000000000
  | 20 => 0x1030501f7429887919626d53a2000000000000007a45911582527552c80000000641000048c0000000000000000000000000000074100000000006a700000010ae21500000e90ca0004701fcc0002620001a50ed62ed052201c00097800007640009cb00013a40000000e980000002f00000000f8000035c9bb51f600037da19c0000002f606840001d40000c24aa095e05e12ec0000803ef0efcde61ee4890000f501ca0bb976107c91a1871e849fa65b02e80000dc0003818b200003c624e0000000000000000000084b33b000000000000000000000000000000a0218f28c87e449a0a52180000f3400000000000000004478b4c00000012e0000f3600000012080006490000dcc0003d700023200002a91fba2c124a84239b85386608e92f210b00000000360000000000137261800046722785b00000000000028db80002e403d859e76e28e994052456b25106740007c200000012da52731325980840000000194d623fb1b08000d0417243426140005db2a48fe8000000000000060e064000000000000000022b000000010e00005c238f000251ce4660e1ad0000000683000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x9754c11000799434c110007b1414c110007d1314c110005797588110007b1418811000cf87648110005797548110007a94248110007b14148110007e121481100047d73994100047d729941000c7e719941000c7c719941000e3f419941000e3d41994100163e40994100163c40994100047f73594100047f725941000c7e715941000c7c715941000e3f415941000e3d41594100147f70594100147d70594100163e40594100163c40594100167a105941000e791059410004bd7399010004bd729901000e3e519901000e3c5199010014be7099010014bc70990100163f50990100163d5099010004bf7359010004bf725901000cbf715901000cbd715901000e3e515901000e3c5159010014be7059010014bc70590100163f50590100163d5059010016b71059010016b510590100265e7598c100265d7598c100269e7498c100269d7498c1000e5e5198c1000e5c5198c1000e9f4198c1000e9d4198c100165f5098c100165d5098c100169e4098c100169c4098c100065e7558c100065d7558c100069e7458c100069d7458c1000e5e5158c1000e5c5158c1000e9f4158c1000e9d4158c100165f5058c100165d5058c100169e4058c100169c4058c10016d71058c10016da1058c10016d51058c1000ed91058c100347f76d4c100047d76d4c100063e64d4c100063d64d4c100265e63d4c100065d63d4c100047f7654c100047d7654c100063e6454c100063d6454c100265e6354c100065d6354c1002cbf76d0c10004bd76d0c100063e65d0c100063d65d0c100269e63d0c100069d63d0c10004bf7650c10004bd7650c100063e6550c100063d6550c100269e6350c100069d6350c1001e6e759881001e6d759881001eae749881001ead74988100066f53988100066d5398810006af4398810006ad439881000e6e519881000e6c519881000eaf419881000ead41988100166f50988100166d5098810016ae4098810016ac40988100066e75588100066d7558810006ae7458810006ad74588100066f53588100066d5358810006af4358810006ad435881000e6e515881000e6c515881000eaf415881000ead41588100166f50588100166d5058810016ae4058810016ac4058810016e71058810016ea1058810016e5105881000ee910588100347f76d48100047d76d48100063e64d48100063d64d48100065e63d48100065d63d481001e6e62d48100066d62d48100047f76548100047d76548100063e64548100063d64548100065e63548100065d635481001e6e62548100066d625481002cbf76d0810004bd76d08100063e65d08100063d65d08100069e63d08100069d63d081001eae62d0810006ad62d0810004bf7650810004bd76508100063e65508100063d65508100069e63508100069d635081001eae6250810006ad6250810
  | 1 => 0x95100047d72d95100563e40d95100563c40d9510004bf745951002cbc74595100047e76195100047d73195100047d721951000c7e711951000c7c711951003679701951004e3e401951004e3c401951002cbe76d91100063f65d91100063c65d9110004bd73d9110004bd72d91100463e51d91100463c51d91100047f75591100347c7559110004be76191100063f65191100063c6519110004bd7319110004bd721911002eb5711911003e3e511911003e3c5119110014be7019110014bc70191100047f7558d100347c7558d10004bf7458d1002cbc7458d10004ef7258d1001cec7258d100047e76d4d100347c76d4d100063f64d4d100063c64d4d100057970d4d100047e7654d100047c7654d100063f6454d100063c6454d10004be76d0d1002cbc76d0d100063f65d0d100063c65d0d10005b571d0d10004be7650d10004bc7650d100063f6550d100063c6550d100047f75589100347c7558910004bf745891002cbc7458910004df7358910024dc73589100047e76d49100347c76d49100063f64d49100063c64d49100057970d49100047e76549100047c76549100063f64549100063c6454910004be76d091002cbc76d09100063f65d09100063c65d0910005b571d0910004be7650910004bc76509100063f65509100063c6550910014be76d05100063f65d05100063c65d0510015ba70d0510005b5749051002eb46490510014bc76505100063f65505100063c655051000f36515051000f345150510015b87050510014f4765051002eb77650510015b47650510006b47650510014b47650510007377550510007347550510007376550510007346550510005b77350510007375350510007355350510005b77250510007375250510007355250510007b37050510015b67050510015b47050510007b0705051000eb7605051000fb36050510005b5748c510014f4764c510005b5744c51000755534c510005b57488510014f47648510005b5744851000765524851000c7e76d41100063f64d41100063c64d411000d7671d41100073541d4110005797594110036786594110007b1419411000c7c76541100063f64541100063c645411000d7471541100073541541100173a405411001738405411000cf87654110007b141541100367b765411000d78765411000678765411000c7876541100073b74541100073874541100073b64541100073864541100057b73541100073b43541100073943541100057b72541100073b425411000739425411000773715411000d7a715411000d7871541100077071541100167b61541100177361541100073b415411000772415411000739415411000771415411000731415411000772315411000771315411000772215411000771215411000579758c110007b1418c11000cf8764c1100057
  | 2 => 0x6b5615042002e3e759931002e3d7599310004bd7399310004bd729931000eb6719931000e3e519931000e3c51993100047f75593100347c75593100063f75593100063c7559310004bf7359310004bf725931000e3e515931000e3c51593100047f7558f100347c7558f1000c7e76d4f1000c7c76d4f100063e64d4f100063d64d4f1000c7e7654f1000c7c7654f100063e6454f100063d6454f100265e6354f100065d6354f1002cbf76d0f10004bd76d0f100963f65d0f100963c65d0f10005b571d0f10004bf7650f10004bd7650f1008e3f6550f1008e3c6550f100047f7558b100347c7558b1000c7e76d4b1000c7c76d4b100063e64d4b100063d64d4b1000c7e7654b1000c7c7654b100063e6454b100063d6454b1001e6e6254b100066d6254b1002cbf76d0b10004bd76d0b100863f65d0b100863c65d0b10005b571d0b10004bf7650b10004bd7650b1007e3f6550b1007e3c6550b1002eb6645071000db77650710006b7765071000737755071000734755071000f37655071000f346550710005b77350710007375350710007355350710005b77250710007375250710007355250710015b67050710015b47050710005b5744c71000755534c710005b574487100076552487100063e64d43100063d64d431000d7671d43100073541d43100063e64543100063d645431000d7471543100073541543100363e74996100363d74996100047d73996100047d72996100167a70996100163e40996100163c4099610004bf745961002cbc74596100063f74596100063c74596100047f73596100047f72596100163e40596100163c4059610004bf7458e1002cbc7458e100347f76d4e100047d76d4e100763f64d4e100763c64d4e100057970d4e100047f7654e100047d7654e1006e3f6454e1006e3c6454e10014be76d0e10014bc76d0e100063e65d0e100063d65d0e10014be7650e10014bc7650e100063e6550e100063d6550e100269e6350e100069d6350e10004bf7458a1002cbc7458a100347f76d4a100047d76d4a100663f64d4a100663c64d4a100057970d4a100047f7654a100047d7654a1005e3f6454a1005e3c6454a10014be76d0a10014bc76d0a100063e65d0a100063d65d0a10014be7650a10014bc7650a100063e6550a100063d6550a1001eae6250a10006ad6250a100063e65d06100063d65d0610015ba70d06100063e65506100063d6550610015b870506100367a65542100157b76542100067b76542100073b74542100073874542100173b64542100173864542100057b73542100073b43542100073943542100057b72542100073b425421000739425421000d7a715421000d7871542100073b415421000739415421000579754c21000799434c210005797548210007a942482100347e76d95100047d73d
  | 3 => 0xf76541200047d76541200063f64541200063c64541200056f72541200072d4254120017682054120007a9428c12001cf8764c12000799434c120007a9424c120007c9324c1200047d739942001e3f429942001e3d429942000c7e71994200163e40994200163c40994200047f735942001c7f725942001c7d725942001e3f425942001e3d425942000c7c71594200163e40594200163c4059420004bd739902001e3f529902001e3d5299020004bd7199020014be7099020014bc70990200163f50990200163d5099020004bf735902001cbf725902001cbd725902001e3f525902001e3d5259020004bf7159020014be7059020014bc70590200163f50590200163d5059020016af2059020016ad20590200265e7598c200265d7598c200269e7498c200269d7498c2001e5f5298c2001e5d5298c2001e9f4298c2001e9d4298c200165f5098c200165d5098c200169e4098c200169c4098c200065e7558c200065d7558c200069e7458c200069d7458c2001e5f5258c2001e5d5258c2001e9f4258c2001e9d4258c200165f5058c200165d5058c200169e4058c200169c4058c20016cf2058c20016da2058c20016cd2058c2001ed92058c200347f76d4c200047d76d4c200063e64d4c200063d64d4c200265e63d4c200065d63d4c200056d72d4c200047f7654c200047d7654c200063e6454c200063d6454c200265e6354c200065d6354c2002cbf76d0c20004bd76d0c200063e65d0c200063d65d0c200269e63d0c200069d63d0c20004bf7650c20004bd7650c200063e6550c200063d6550c200269e6350c200069d6350c2000e77759842000e74759842000eb6749842000eb57498420006775398420006755398420006b74398420006b5439842001e77529842001e75529842001eb7429842001eb54298420016775098420016755098420016b64098420016b440984200047f75584200347c7558420006777558420006747558420006b67458420006b57458420006775358420006755358420006b74358420006b5435842001e77525842001e75525842001eb7425842001eb54258420016775058420016755058420016b64058420016b44058420016e72058420016f22058420016e5205842001ef1205842000c7f76944200047d76944200063e64944200063d64944200065e63944200065d639442000e76619442000675619442000c7f76144200047d76144200063e64144200063d64144200055d73144200065e63144200065d63144200056d721442000e76611442000675611442000579701442002cbf76d0420004bd76d04200063e65d04200063d65d04200069e63d04200069d63d042000eb661d0420006b561d0420004bf7650420004bd76504200063e65504200063d65504200069e63504200069d635042000eb66150420
  | 4 => 0xa200063e6550a200063d6550a20015b87050a200047f75586200347c7558620004bf745862002cbc745862000c7f76946200047d76946200563f64946200563c649462000579709462000c7f76146200047d761462004e3f641462004e3c64146200055d73146200056d7214620005797014620014be76d06200063e65d06200063d65d0620014bc76506200063e65506200063d655062000eb66150620006b5615062000799434c2200055d73995200363e74995200363d74995200365e73995200047d73995200365d73995200045d73995200047d72995200366d729952000c7e71995200047d70995200367970995200663e40995200663c4099520004bf745952002cbc74595200063f74595200063c74595200047f73595200047f72595200066f725952000c7c71595200047f70595200067b705952005e3e405952005e3c40595200347e75d91200047d75d912002cbe76d91200063e65d91200063d65d91200063e75d91200063d75d9120004bd73d9120004bd71d9120004be76191200063e65191200063d651912002e3e751912002e3d7519120004bd731912002ead7219120004bd71191200347e75d8d200047d75d8d20004bf7458d2002cbc7458d200347f76d4d200047d76d4d200063f64d4d200063c64d4d200047f7654d200047d7654d200063f6454d200063c6454d200065f6354d200265c6354d20004be76d0d2002cbc76d0d200063e65d0d200063d65d0d20005ad72d0d20004be7650d20004bc7650d200063e6550d200063d6550d200063f64d49200063c64d49200057970d49200063f64549200063c64549200057b705492001f682054920014be76d09200063e65d09200063d65d0920015ba70d092001fa820d0920005ad749092002eac6490920014bc76509200063e65509200063d65509200072f52509200072d5250920015b87050920014ec7650920015e8705092002eaf7650920015ac7650920006ac7650920014ac76509200072e65509200072d6550920005af73509200072f53509200072d5350920005af7150920007ab7050920015ae7050920015ac7050920007a87050920015a8705092001eaf605092001fab6050920005ad748c920014ec764c920005ad744c920026cc634c9200347e75d85200047d75d85200047d76945200063f64945200063c64945200056d72945200072d42945200057970945200047d76145200063f64145200063c64145200055d73145200056d72145200072d4214520005797014520004be76d052002cbc76d05200063e65d05200063d65d0520005ad72d0520004be7650520004bc76505200063e65505200063d65505200066d65c8520005ad74c8520014ec76485200066d6548520005ad74485200063f64d41200063c64d41200056d72d41200072d42d41200347
  | 5 => 0x16d73058430016f23058430016d53058430026f1305843000c7f76944300047d76944300063e64944300063d64944300066e62944300066d629443000e76619443000675619443000c7f76144300047d76144300063e64144300063d64144300055d73144300056d72144300066e62144300066d621443000e76611443000675611443000579701443002cbf76d0430004bd76d04300063e65d04300063d65d0430006ae62d0430006ad62d043000eb661d0430006b561d0430004bf7650430004bd76504300063e65504300063d6550430006ae6250430006ad625043000eb66150430006b561504300047d739972001e3f429972001e3d429972000c7e71997200663e40997200663c40997200047f735972001e3f425972001e3d425972000c7c715972001e6f215972005e3e405972005e3c4059720004bd739932001eae729932001e3f529932001e3d5299320004bd7199320004bf735932001e3f525932001e3d5259320004bf71593200347f76d4f200047d76d4f200063e64d4f200063d64d4f200047f7654f200047d7654f200063e6454f200063d6454f2002cbf76d0f20004bd76d0f200063e65d0f200063d65d0f20005ad72d0f20004bf7650f20004bd7650f200063e6550f200063d6550f2002eae6450b2001daf7650b20006af7650b2001f2e6550b2001f2d6550b20005af7350b200072f5350b200072d5350b20005af7150b20015ae7050b20015ac7050b20005ad744cb2001ecc634cb200047f75587200347c755872000c7f76947200047d76947200063e64947200063d64947200056d72947200072d429472000c7f76147200047d76147200063e64147200063d64147200055d73147200056d72147200072d421472000579701472002cbf76d0720004bd76d07200063e65d07200063d65d0720005ad72d0720004bf7650720004bd76507200063e65507200063d65507200066d6548720005ad74487200063e64d43200063d64d43200056d72d43200072d42d43200063e64543200063d64543200056f72543200072d42543200363e74996200363d74996200047d739962000c7e71996200163e40996200163c4099620004bf745962002cbc74596200063f74596200063c74596200047f735962000c7c71596200163e40596200163c40596200167a1059620004bf7458e2002cbc7458e200347f76d4e200047d76d4e200763f64d4e200763c64d4e200056d72d4e200047f7654e200047d7654e2006e3f6454e2006e3c6454e20014be76d0e20014bc76d0e200063e65d0e200063d65d0e20014be7650e20014bc7650e200063e6550e200063d6550e200269e6350e200069d6350e200663f64d4a200663c64d4a200057970d4a2005e3f6454a2005e3c6454a200057b7054a200063e65d0a200063d65d0a20015ba70d
  | 6 => 0xd65d09300059d73d0930004be7650930004bc76509300063e65509300063d65509300059d74cc930014dc764c9300059d744c93001ecc624c9300347e75d85300047d75d85300047d76945300063f64945300063c64945300055d73945300071d43945300057970945300047d76145300063f64145300063c64145300055d73145300071d43145300056d7214530005797014530004be76d053002cbc76d05300063e65d05300063d65d05300059d73d0530004be7650530004bc76505300063e65505300063d65505300065d65cc5300059d74cc530014dc764c5300065d654c5300059d744c5300063f64d41300063c64d41300055d73d41300071d43d41300347f76541300047d76541300063f64541300063c64541300055f73541300071d43541300175830541300263f43994300263d43994300047d729943000c7e71994300163e40994300163c40994300247f73594300247d73594300263f43594300263d43594300047f725943000c7c71594300163e40594300163c40594300263f53990300263d5399030004bd7299030004bd7199030014be7099030014bc70990300163f50990300163d5099030024bf7359030024bd73590300263f53590300263d5359030004bf7259030004bf7159030014be7059030014bc70590300163f50590300163d50590300169f30590300169d305903001e6e759883001e6d759883001eae749883001ead74988300266f53988300266d5398830026af4398830026ad43988300166f50988300166d5098830016ae4098830016ac40988300066e75588300066d7558830006ae7458830006ad74588300266f53588300266d5358830026af4358830026ad43588300166f50588300166d5058830016ae4058830016ac4058830016cf3058830016ea3058830016cd3058830026e930588300347f76d48300047d76d48300063e64d48300063d64d48300055d73d483001e6e62d48300066d62d48300047f76548300047d76548300063e64548300063d645483001e6e62548300066d625483002cbf76d0830004bd76d08300063e65d08300063d65d083001eae62d0830006ad62d0830004bf7650830004bd76508300063e65508300063d655083001eae6250830006ad625083000e77759843000e74759843000eb6749843000eb57498430026775398430026755398430026b74398430026b54398430006775298430006755298430006b74298430006b54298430016775098430016755098430016b64098430016b440984300047f75584300347c7558430006777558430006747558430006b67458430006b57458430026775358430026755358430026b74358430026b54358430006775258430006755258430006b74258430006b54258430016775058430016755058430016b64058430016b44058430
  | 7 => 0x43300071d43d43300063e64543300063d64543300055f73543300071d43543300363e74996300363d74996300047d729963000c7e71996300163e40996300163c4099630004bf745963002cbc74596300063f74596300063c74596300047f725963000c7c71596300163e40596300163c40596300167a10596300763f64d4e300763c64d4e300057970d4e3006e3f6454e3006e3c6454e300057b7054e300063e65d0e300063d65d0e30015ba70d0e300063e6550e300063d6550e30015b87050e30004bf7458a3002cbc7458a300347f76d4a300047d76d4a300663f64d4a300663c64d4a300055d73d4a300047f7654a300047d7654a3005e3f6454a3005e3c6454a30014be76d0a300063e65d0a300063d65d0a30014bc7650a300063e6550a300063d6550a3001eae6250a30006ad6250a300047f75586300347c7558630004bf745863002cbc745863000c7f76946300047d76946300563f64946300563c649463000579709463000c7f76146300047d761463004e3f641463004e3c64146300055d73146300056d7214630005797014630014be76d06300063e65d06300063d65d0630014bc76506300063e65506300063d655063000eb66150630006b561506300056d72995300363e74995300363d74995300047d73995300365d73995300366e72995300047d72995300366d72995300046d729953000c7e71995300047d70995300367970995300763e40995300763c4099530004bf745953002cbc74595300063f74595300063c74595300047f73595300065f73595300047f725953000c7c71595300047f70595300067b705953006e3e405953006e3c40595300347e75d91300047d75d913002cbe76d91300063e65d91300063d65d91300063e75d91300063d75d9130004bd72d9130004bd71d9130004be76191300063e65191300063d651913002e3e751913002e3d751913002e9d7319130004bd7219130004bd71191300063f64d4d300063c64d4d300057970d4d300063f6454d300063c6454d300057b7054d30027583054d30014be76d0d300063e65d0d300063d65d0d30015ba70d0d300279830d0d300059d7490d3002e9c6490d30014bc7650d300063e6550d300063d6550d300071f5350d300071d5350d30015b87050d30014dc7650d30015d87050d3002e9f7650d300159c7650d300069c7650d300149c7650d300071e6550d300071d6550d300059f7250d300059f7150d300079b7050d300159e7050d300159c7050d30007987050d30015987050d300269f6050d300279b6050d300347e75d89300047d75d89300047d76d49300063f64d49300063c64d49300071d43d49300047f76549300063f64549300063c64549300071d43549300066f625493001e6c6254930004be76d093002cbc76d09300063e65d09300063
  | 8 => 0x4f1d63144400061d631444003f2e72144400053d721444003f2d72144400052d721444004f2e62144400063d621444004f2d62144400062d62144400553e711444003f36711444004e3f611444004f36611444003e3d611444004f35611444000635611444004d3f701444004f3a701444004d3d701444003f39701444000539701444004e3e601444004f3a6014440014be76cc440004bd76cc4400053e75cc4400053d75cc4400069d63cc4400071d53cc440006ad62cc440006b561cc440014be768c440004bd768c44003d3f758c44003d3c758c4400069d638c440006ad628c440006b5618c440004bd764c4400053f754c4400053c754c4400069d634c4400071d534c440006ad624c440006b5614c440014be760c440004bd760c4400053e750c4400053d750c4400069d630c440005ae720c440005ad720c440006ad620c440006b5610c440015ba700c440005b9700c440014be76c8440004bd76c84400053e75c84400053d75c84400069d63c8440006ad62c84400072d52c8440006b561c8440014be7688440004bd768844003d3f758844003d3c75884400069d6388440006ad6288440006b56188440004bd76484400053f75484400053c75484400069d6348440006ad62484400072d5248440006b56148440014be7608440004bd76084400053e75084400053d75084400059e73084400059d73084400069d6308440006ad6208440006b56108440015ba7008440005b970084400263f43997300263d43997300047d729973000c7e71997300763e40997300763c40997300263f43597300263d43597300047f725973000c7c71597300265f315973006e3e405973006e3c40597300269e73993300263f53993300263d5399330004bd7299330004bd71993300263f53593300263d5359330004bf7259330004bf715933002e9e6450f300259f7650f300069f7650f300271e6550f300271d6550f300059f7250f300059f7150f300159e7050f300159c7050f300347f76d4b300047d76d4b300063e64d4b300063d64d4b300071d43d4b300047f7654b300047d7654b300063e6454b300063d6454b300071d4354b3002cbf76d0b30004bd76d0b300063e65d0b300063d65d0b300059d73d0b30004bf7650b30004bd7650b300063e6550b300063d6550b300059d744cb300047f75587300347c755873000c7f76947300047d76947300063e64947300063d64947300055d73947300071d439473000c7f76147300047d76147300063e64147300063d64147300055d73147300071d43147300056d721473000579701473002cbf76d0730004bd76d07300063e65d07300063d65d07300059d73d0730004bf7650730004bd76507300063e65507300063d65507300065d654c7300059d744c7300063e64d43300063d64d43300055d73d
  | 9 => 0xd6354840006ad625484005d3f765484005d3d76548400053f735484005f1e63548400063d635484005f1d63548400061d63548400072f725484005f2e62548400063d625484005f2d62548400062d625484003d3c715484005f36615484005f35615484005d3f705484005e3e605484005f3a6054840014be7614840004bd76148400653e75148400069d6314840006ad6214840014be76cc840004bd76cc8400053e75cc8400053d75cc8400069d63cc840006ad62cc840014be768c840004bd768c8400053e758c8400053d758c8400069d638c840006ad628c840004bd764c8400053e754c8400053d754c8400069d634c840006ad624c840014be760c840004bd760c8400053e750c8400053d750c8400069d630c840006ad620c8400078d320c840005b6710c840005b5710c840015ba700c840005b9700c8400063f75584400063c7558440004bf73584400063f53584400063d5358440004bf72584400063f52584400063d5258440016b771584400163f50584400163d5058440016b61058440016b41058440006b77558440006377558440006b67558440006b57558440006b47558440006347558440006b77358440006b67358440006b57358440006b47358440006b75358440006375358440006b65358440006b55358440006355358440006b45358440006b77258440006b67258440006b57258440006b47258440006b75258440006375258440006b65258440006b55258440006355258440006b45258440006b73258440006b63258440006b53258440006b43258440016b77058440016b67058440016b47058440016b75058440016375058440016b65058440016b55058440016355058440016b45058440016b73058440016b63058440016b53058440016b43058440016b72058440016b62058440016b52058440016b420584400069d63d4440006ad62d4440006b561d4440014be7694440004bd76944400069d6394440006ad6294440006b561944400553f76944400563e76944400553d769444003e3d76944400043d76944400053d73944400571e63944400063d63944400571d63944400061d63944400053d72944400572e62944400063d62944400572d62944400062d629444004d3e71944400563f619444005736619444003e3d61944400573561944400063561944400553f70944400553d70944400563e60944400573a60944400069d6354440006ad6254440006b56154440014be7614440004bd76144400059e73144400059d73144400069d6314440005ae7214440005ad7214440006ad6214440006b56114440015ba7014440005b9701444004d3f761444004e3e761444004d3d761444003e3d76144400043d761444003f1e73144400053d731444003f1d73144400051d731444004f1e63144400063d6314440
  | 10 => 0x44400066d621444000e766114440006756114440005797014440004bd76904400069d6390440006ad6290440006b561904400053f75504400053c75504400063e65504400063d65504400069e63504400069d6350440006ae6250440006ad625044000eb661504400063e7558c400063d7558c400169f7358c40004bf7258c40004bf7158c400163f5058c400163d5058c400169e3058c400169c3058c400069f7558c400069e7558c400061e7558c400069d7558c400061d7558c400069c7558c400069f7258c400069e7258c400069d7258c400069c7258c400069f7158c400069e7158c400069d7158c400069c7158c400169f7058c400169e7058c400169c7058c400169f5058c400161f5058c400169e5058c400169d5058c400161d5058c400169c5058c400169f2058c400169e2058c400169d2058c400169c2058c400169f1058c400169e1058c400169d1058c400169c1058c400069d63d4c400753f76d4c400753d76d4c400771e63d4c400063d63d4c400771d63d4c400061d63d4c400053d72d4c400772e62d4c400772d62d4c4003d3e71d4c400773661d4c400773561d4c400753d70d4c400763e60d4c400773a60d4c40014be7694c40004bd7694c4006d3d7594c400069d6394c400069d6354c4006d3f7654c4006d3d7654c400071f7354c4006f1e6354c400063d6354c4006f1d6354c400061d6354c400053f7254c4006f2e6254c4006f2d6254c4003d3c7154c4006f366154c4006f356154c4006d3f7054c4006e3e6054c4006f3a6054c40014be7614c40004bd7614c400753e7514c400069d6314c400063e75588400063d7558840004bf73588400063f53588400063d5358840016af7258840004bf71588400163f50588400163d5058840016ae2058840016ac2058840006af7558840006ae75588400062e7558840006ad75588400062d7558840006ac7558840006af7358840006ae7358840006ad7358840006ac7358840006af53588400062f5358840006ae5358840006ad53588400062d5358840006ac5358840006af7158840006ae7158840006ad7158840006ac7158840016af7058840016ae7058840016ac7058840016af50588400162f5058840016ae5058840016ad50588400162d5058840016ac5058840016af3058840016ae3058840016ad3058840016ac3058840016af1058840016ae1058840016ad1058840016ac10588400069d63d4840006ad62d48400653f76d48400653d76d48400053d73d48400671e63d48400063d63d48400671d63d48400061d63d48400672e62d48400063d62d48400672d62d48400062d62d484003d3e71d48400673661d48400673561d48400653d70d48400663e60d48400673a60d4840014be7694840004bd769484005d3d75948400069d6394840006ad62948400069
  | 11 => 0x2e3f41994400163e40994400163c409944002cbc745944002e3c74594400047f735944002e3f43594400047f725944002e3f425944000c7c715944002e3f41594400163e40594400163c40594400063d65d50400363e65550400265e7598c400265d7598c4002e9f4298c4002e9f4198c400165f5098c400165d5098c400169e4098c400169c4098c4002e9f4358c4002e9c4358c400065e7558c400065d7558c4002e9e7458c400069f5458c4002e9e5458c400069d5458c4002e9c5458c4002e9f4258c4002e9c4258c4002e9f4158c4002e9c4158c400165f5058c400165d5058c400169f4058c400169e4058c400169d4058c400169c4058c400347f76d4c400047d76d4c400265e63d4c400065d63d4c400047f7654c400047d7654c400265e6354c400065d6354c40004bd7690c400053e7590c400053d7590c400069d6390c400063e6550c400063d6550c400269e6350c4001e6e759884001e6d75988400066f53988400066d539884002eaf4398840006ad439884002eaf41988400166f50988400166d5098840016ae4098840016ac409884002eaf425884002eac42588400066e75588400066d755884002eae7458840006af545884002eae5458840006ad545884002eac54588400066f53588400066d535884002eaf4358840006ae4358840006ad435884002eac435884002eaf415884002eac41588400166f50588400166d5058840016af4058840016ae4058840016ad4058840016ac40588400347f76d48400047d76d48400065e63d48400065d63d484001e6e62d48400066d62d48400047f76548400047d76548400065e63548400065d635484001e6e62548400066d6254840004bd76908400053e75908400053d75908400069d6390840006ad62908400063e65508400063d65508400069e63508400069d635084001eae625084000e77759844000e74759844000677539844000675539844002eb74398440006b5439844000677529844000675529844002eb74298440006b54298440016775098440016755098440016b64098440016b440984400047f75584400347c755844002eb7415844002eb4415844000677755844000674755844002eb67458440006b7545844002eb65458440006b5545844002eb4545844000677535844000675535844002eb74358440006b64358440006b5435844002eb4435844000677525844000675525844002eb74258440006b64258440006b5425844002eb44258440016775058440016755058440016b74058440016b64058440016b54058440016b4405844000c7f76944400047d76944400065e63944400065d63944400066e62944400066d629444000e76619444000675619444000c7f76144400047d76144400055d73144400065e63144400065d63144400056d72144400066e621
  | 12 => 0xd62d4a400453e71d4a400653d70d4a40014be7694a40004bd7694a4005d3f7654a4005d3d7654a400053f7354a400063d6354a400072f7254a400063d6254a400453c7154a4005d3f7054a40014be7614a40004bd7614a40014be76cca40004bd76cca400053e75cca400053d75cca400069d63cca40014be768ca40004bd768ca400053e758ca400053d758ca40006ad628ca40004bd764ca400053e754ca400053d754ca400069d634ca40006ad624ca40014be760ca40004bd760ca400053e750ca400053d750ca400078d320ca40005b6710ca40005b5710ca40015ba700ca40005b9700ca400063f75586400063c7558640004bf73586400063f53586400063d5358640004bf72586400063f52586400063d5258640016b771586400163f50586400163d5058640016b61058640016b41058640014be7694640004bd76946400553f76946400563e76946400553d76946400463d76946400043d76946400053d73946400063d63946400053d72946400063d62946400563f61946400463d61946400553f70946400553d7094640014be7614640004bd76146400059e73146400059d7314640005ae7214640005ad7214640015ba7014640005b9701464004d3f761464004e3e761464004d3d76146400463d76146400043d76146400471e73146400053d73146400471d73146400051d73146400063d63146400472e72146400053d72146400472d72146400052d72146400063d621464004736711464004e3f61146400463d611464004d3f701464004f3a701464004d3d7014640047397014640005397014640014be76cc640004bd76cc6400053e75cc6400053d75cc6400069d63cc6400071d53cc640014be768c640004bd768c6400453f758c6400453c758c640006b5618c640004bd764c6400053f754c6400053c754c6400069d634c6400071d534c640006b5614c640014be760c640004bd760c6400053e750c6400053d750c640005ae720c640005ad720c640015ba700c640005b9700c640014be76c8640004bd76c86400053e75c86400053d75c8640006ad62c86400072d52c8640014be7688640004bd76886400453f75886400453c7588640006b56188640004bd76486400053f75486400053c7548640006ad62486400072d5248640006b56148640014be7608640004bd76086400053e75086400053d75086400059e73086400059d7308640015ba7008640005b97008640004bf7459540004be76d0d40014bc7650d400069f6350d40004be76d0940014bc7650940006af62509400347e75d85400047d75d85400055d73145400056d7214540005797014540004be76d0540014bc7650540006b761505400163f64d41400163f645414002e3e74994400047d739944002e3f43994400047d729944002e3f429944000c7e7199440
  | 13 => 0x85500053e74085500053d74085500055e73085500055d73085500157a70085500057970085500053e74d81500053d74d81500063f64d81500063c64d81500173a40d81500173840d81500373a74d81500373974d81500073b64d81500073864d81500073b43d81500073943d81500073b42d81500073942d81500057971d81500073b41d81500073941d81500363e74994500363d74994500367970994500365f5358c500047f7654c500063e65d0c500063e6550c500269e6350c500069d6350c500366f52588500047f76548500063e65d08500063e655085001eae6250850006ad62508500047d76944500063e65d04500063e655045000eb66150450006b5615045002e9f4358f4002eaf4258b400047f75587400347c755874002eb741587400055d73147400056d72147400057970147400163e64d43400163e64543400173a40543400363d74996400047d73996400047d729964000c7e71996400163e40996400163c40996400063f74596400047f73596400047f725964000c7c71596400163e40596400163c40596400063d65d5240015ba70d5240005b970d52400363e6595240034bf7655240015b870552400063d65152400347f76d4e400047d76d4e400047f7654e400047d7654e400063e65d0e400063d65d0e400053e7590e400053d7590e40015ba7090e40024bf7650e400063e6550e400063d6550e400269e6350e400069d6350e40015b87050e400053e7510e400053d7510e400347f76d4a400047d76d4a400047f7654a400047d7654a400063e65d0a400063d65d0a400053e7590a400053d7590a40015ba7090a4001cbf7650a400063e6550a400063d6550a4001eae6250a40006ad6250a40015b87050a400053e7510a400053d7510a400047f75586400347c755864000c7f76946400047d769464000c7f76146400047d76146400055d73146400056d72146400057970146400053e75d06400053d75d06400063e65d06400063d65d0640015ba709064000cbf76506400053f75506400053c75506400063e65506400063d655064000eb66150640006b56150640015b870506400063e7558e400063d7558e400169f7358e40004bf7258e40004bf7158e400163f5058e400163d5058e400169e3058e400169c3058e400753f76d4e400753d76d4e400063d63d4e400053d72d4e400453e71d4e400753d70d4e40014be7694e40004bd7694e4006d3f7654e4006d3d7654e400071f7354e400063d6354e400053f7254e400453c7154e4006d3f7054e40014be7614e40004bd7614e400063e7558a400063d7558a40004bf7358a400063f5358a400063d5358a40016af7258a40004bf7158a400163f5058a400163d5058a40016ae2058a40016ac2058a400653f76d4a400653d76d4a400053d73d4a400063d63d4a400063
  | 14 => 0x153c70d0d500047e7690d500047d7690d500053d7490d500053e7650d500053c7650d500071f7350d500063f6350d500053f7250d500053f7150d5008e3c6150d500153e7050d500153c7050d500047e7610d500047d7610d500053e7410d500063f64d89500063c64d89500063f74d89500063c74d89500047d73d89500063f43d89500063d43d895000c7e71d89500663e40d89500663c40d89500053e74989500053d74989500057970989500053f74589500053c74589500063f64589500063c64589500057b70589500053e74189500053d74189500053e76d09500053c76d09500053d73d09500063f63d09500063f62d09500053d71d09500863c61d09500153e70d09500153c70d09500047e76909500047d76909500053d74909500053e76509500053c76509500053f73509500063f63509500072f72509500063f62509500053f715095007e3c61509500153e70509500153c70509500047e76109500047d76109500053e74109500047e76cc9500047d76cc9500053e74cc9500053d74cc9500047e768c9500047d768c9500053e748c9500053d748c9500047e764c9500053e744c9500053d744c9500047e760c9500047d760c9500053e740c9500053d740c9500074d320c95000576710c95000575710c9500157a700c95000579700c9500053e74985500053d74985500063f64985500063c64985500057970985500053f74585500053c74585500057b70585500053e74185500053d74185500063f64185500063c64185500055e73185500055d73185500056e72185500056d721855000e7661185500047e76d05500047d76d05500053e76d05500063e76d05500043e76d05500063d76d05500053c76d05500053d73d05500063f63d05500053d72d05500063f62d055000e3e61d055000e3c61d05500153e70d05500153c70d05500053d74905500157a70905500057970905500047f76505500047c76505500063f76505500053e76505500053c76505500063c76505500043c76505500053f73505500063f63505500053f72505500063f625055000737715055000e3e615055000e3c61505500153e70505500153c70505500053e74105500157a70105500057970105500047e76cc5500047d76cc5500053e74cc5500053d74cc55000c7c768c5500053e748c5500053d748c5500157a708c55000579708c5500047f764c5500047c764c5500053e744c5500053d744c5500047e760c5500047d760c5500053e740c5500053d740c5500056e720c5500056d720c5500157a700c55000579700c5500047e76c85500047d76c85500053e74c85500053d74c855000c7c76885500053e74885500053d74885500157a70885500057970885500047f76485500047c76485500053e74485500053d74485500047e76085500047d760
  | 15 => 0xf76507500043f76507500053d76507500063c76507500053f73507500063d63507500053f72507500063d625075000737715075000e3e615075000e3c61507500153e70507500153c70507500347e76cc7500047d76cc7500053e74cc7500053d74cc7500065d63cc75000c7f768c7500053e748c7500053d748c7500047f764c7500347c764c7500053e744c7500053d744c7500065d634c7500347e760c7500047d760c7500053e740c7500053d740c7500056e720c7500056d720c7500157a700c75000579700c7500347e76c87500047d76c87500053e74c87500053d74c87500066d62c875000c7f76887500053e74887500053d74887500047f76487500347c76487500053e74487500053d74487500066d62487500347e76087500047d76087500053e74087500053d74087500055e73087500055d73087500157a70087500057970087500247f7654e500065d6354e500269e6350e500069d6350e5001c7f7654a500066d6254a5001eae6250a50006ad6250a5000e7661946500055d73146500056d721465000579701465000eb66150650006b56150650004bd73d9150004bd72d9150004bd71d9150004bd7319150004bd7219150004bd711915002e3c64d51500147e76951500063f64951500147c76551500063f64151500063f64d4d500063c64d4d500147e7694d500053e7494d500053d7494d500147c7654d500063f6454d500063c6454d500065f6354d500047e7614d500053e7414d500053d7414d50004be76d0d5002cbc76d0d50004be7650d50004bc7650d500063f64d49500063c64d49500147e76949500053e74949500053d74949500147c76549500063f64549500063c64549500066f62549500047e76149500053e74149500053d7414950004be76d095002cbc76d0950004be7650950004bc76509500047e76d45500147e76945500053e74945500053d74945500063f64945500063c649455000e7461945500157a70945500147c76545500053e74145500053d74145500063f64145500063c64145500055e73145500055d73145500056e72145500056d72145500157a7014550004be76d055002cbc76d0550004be7650550004bc76505500053d73d91500053d72d91500053d71d91500053e74991500063f64991500057970991500057b70591500053e76191500063e76191500053d73191500053d72191500053d71191500063f64d8d500063c64d8d500063f74d8d500063c74d8d500047d72d8d5000c7e71d8d500763e40d8d500763c40d8d500053e7498d500053d7498d50005797098d500053f7458d500053c7458d500063f6458d500063c6458d500057b7058d500053e7418d500053d7418d500053e76d0d500053c76d0d500063f63d0d500053d72d0d500053d71d0d500963c61d0d500153e70d0d50
  | 16 => 0x93500363f5399350004bd72993500363f5299350004bd71993500363c51993500147c7559350004bf73593500363f5359350004bf72593500363f5259350004bf71593500363c51593500063d649535002e3e64553500147c7558f500365f5358f500053e7494f500053d7494f500063e6454f500063d6454f5002cbf76d0f50004bd76d0f50004bf7650f50004bd7650f500147c7558b500366f5258b500053e7494b500053d7494b500063e6454b500063d6454b5002cbf76d0b50004bd76d0b50004bf7650b50004bd7650b500147c75587500053e74947500053d74947500063e64947500063d649475002cbf76d0750004bd76d0750004bf7650750004bd76507500363f64993500053d73993500363f63993500053d72993500363f62993500053d71993500363c61993500063f76593500053f73593500363f63593500053f72593500363f62593500053f71593500363c61593500053e7498f500053d7498f500063e6458f500063d6458f500063e7458f500063d7458f500047f7258f5000c7c7158f5006e3e4058f5006e3c4058f500053f76d0f500053d76d0f500063d63d0f500053d72d0f500053d71d0f500963e61d0f500153e70d0f500153c70d0f500347e7690f500047d7690f500053f7650f500053d7650f500071f7350f500063d6350f500053f7250f500053f7150f5008e3e6150f500153e7050f500153c7050f500347e7610f500047d7610f500053e7498b500053d7498b500063e6458b500063d6458b500063e7458b500063d7458b500047f7358b500063f4358b500063d4358b5000c7c7158b5005e3e4058b5005e3c4058b500053f76d0b500053d76d0b500053d73d0b500063d63d0b500063d62d0b500053d71d0b500863e61d0b500153e70d0b500153c70d0b500347e7690b500047d7690b500053f7650b500053d7650b500053f7350b500063d6350b500072f7250b500063d6250b500053f7150b5007e3e6150b500153e7050b500153c7050b500347e7610b500047d7610b500347e76ccb500047d76ccb500053e74ccb500053d74ccb500066d62ccb500347e768cb500047d768cb500053e748cb500053d748cb500065d638cb500047d764cb500053e744cb500053d744cb500347e760cb500047d760cb500053e740cb500053d740cb500065d630cb500066d620cb500074d320cb5000576710cb5000575710cb500157a700cb5000579700cb500053e74987500053d74987500063e64987500063d649875000e7461987500347e76d07500047d76d07500053f76d07500063e76d07500053d76d07500063d76d07500043d76d07500053d73d07500063d63d07500053d72d07500063d62d075000e3e61d075000e3c61d07500153e70d07500153c70d07500047f76507500347c76507500053f76507500063
  | 17 => 0xde471549210366f765492100d6c76549210066c765492100c6c76549210072e64549210072d64549210056f73549210072f43549210072d435492100767715492100d6e715492100d6c715492100764715492100d64715492101e6f615492101f6761549210056f70549210063f65d09210063c65d09210072d52d0921005b571d09210063f65509210063c65509210072d5250921005b7715092101fa421509210056d758c92100cec764c9210056d754c921026cc634c9210063f65d05210063c65d0521005ad72d05210072d52d052102cbf7650521004bd76505210063f65505210063c6550521005af72505210072d525052100fa4215052100765528c52101cf4764c52100755534c52100765524c521007c5324c52102cbe74d8121004bd74d81210047d739942101e3f429942101e3d429942100c7e719942100c7c719942100e3f419942100e3d41994210047d70994210047f735942101e3f425942101e3d425942100c7e715942100c7c715942100e3f415942100e3d415942100e6f215942100e6d21594210047f7059421004bd739902101e3f529902101e3d529902100e3e519902100e3c5199021014be7099021004bf735902101e3f525902101e3d525902100e3e515902100e3c5159021014bc70590210265e7598c210265d7598c210269e7498c210269d7498c2101e5f5298c2101e5d5298c2101e9f4298c2101e9d4298c2100e5e5198c2100e5c5198c2100e9f4198c2100e9d4198c210065e7558c210065d7558c210069e7458c210069d7458c2101e5f5258c2101e5d5258c2101e9f4258c2101e9d4258c2100e5e5158c2100e5c5158c2100e9f4158c2100e9d4158c2100ecf2158c2100ed62158c2100ecd2158c2101ed52158c210347f76d4c210047d76d4c210063e64d4c210063d64d4c210265e63d4c210065d63d4c210047f7654c210047d7654c210063e6454c210063d6454c210265e6354c210065d6354c2102cbf76d0c21004bd76d0c210063e65d0c210063d65d0c210269e63d0c210069d63d0c21005ad72d0c21004bf7650c21004bd7650c210063e6550c210063d6550c210269e6350c210069d6350c210167a7598021016797598021016bb7498021016b874980210067b5398021006795398021006bb4398021006b9439802101e7b529802101e79529802101ebb429802101eb9429802100e7a519802100e78519802100ebb419802100eb94198021004bf745802102cbc74580210067a7558021006797558021006bb7458021006b874580210067b5358021006795358021006bb4358021006b9435802101e7b525802101e79525802101ebb425802101eb9425802100e7a515802100e78515802100ebb415802100eb9415802100eeb215802100ef2215802100ee9215802101ef12158021004bd739
  | 18 => 0xf76d4f210047d76d4f210063e64d4f210063d64d4f210056d72d4f210047f7654f210047d7654f210063e6454f210063d6454f2102cbf76d0f21004bd76d0f210063e65d0f210063d65d0f21004bf7650f21004bd7650f210063e6550f210063d6550f210366e6554b2101d6f7654b210066f7654b2101f2e6454b2101f2d6454b210056f7354b210072f4354b210072d4354b2100d6e7154b2100d6c7154b210056f7054b210056d754cb2101ecc634cb210063e65d07210063d65d0721005ad72d07210072d52d07210063e65507210063d6550721005af72507210072d5250721004bf745832102cbc745832102e3e759922102e3d7599221004bd739922100e3e519922100e3c5199221014be70992210047f75592210347c75592210063f75592210063c7559221004bf735922100e3e515922100e3c5159221014bc705922100eb710592210047f7558e210347c7558e2100c7e76d4e2100c7c76d4e210063e64d4e210063d64d4e2100c7e7654e2100c7c7654e210063e6454e210063d6454e210265e6354e210065d6354e2102cbf76d0e21004bd76d0e210963f65d0e210963c65d0e21005ad72d0e21004bf7650e21004bd7650e2108e3f6550e2108e3c6550e210063e64d4a210063d64d4a2100d7671d4a210063e6454a210063d6454a2100d747154a210863f65d0a210863c65d0a21005b571d0a2107e3f6550a2107e3c6550a21005b77150a2100755534c6210047f75582210347c7558221004bf745822102cbc745822102cbe74d9521004bd74d95210347e76d95210063e74d95210063d74d95210047d73d95210047d70d95210047e76195210363e74195210363d74195210047d73195210366d72195210047d70195210063f65991210063c65991210059d739912102e3e759912102e3d759912102e9e7399121004bd739912102e9d73991210049d7399121004bd729912102ead7299121004bd719912102eb571991210863e51991210863c5199121014be70991210047f75591210347c75591210063f65591210063c65591210063f75591210063c7559121004bf7359121004bf7259121006af7259121004bf7159121006b7715912107e3e515912107e3c5159121014bc705912102cbe74d8d21004bd74d8d210047f7558d210347c7558d210047e76d4d210347c76d4d210063e64d4d210063d64d4d210056d72d4d210047e7654d210047c7654d210063e6454d210063d6454d2102cbf76d0d21004bd76d0d210063f65d0d210063c65d0d21004bf7650d21004bd7650d210063f6550d210063c6550d210069f6350d210269c6350d2100c7e76d49210063e64d49210063d64d492100d7671d492101f6421d49210056d75949210366c659492100c7c76549210063e64549210063d645492100d74715492100cec7654921
  | 19 => 0x4931004bd76d09310063f65d09310063c65d09310071d53d0931004bf76509310063f65509310063c65509310071d5350931006af625093101eac62509310055d75cc93100cdc764c9310055d754c93101ecc624c9310063f65d05310063c65d05310059d73d05310071d53d053102cbf7650531004bd76505310063f65505310063c65505310059f73505310071d535053100f94315053102cbe74d8131004bd74d81310263f43994310263d43994310047d729943100c7e719943100c7c719943100e3f419943100e3d41994310047d70994310263f43594310263d43594310047f725943100c7e715943100c7c715943100e3f415943100e3d415943100e5f315943100e5d31594310047f70594310263f53990310263d5399031004bd729903100e3e519903100e3c5199031014be70990310263f53590310263d5359031004bf725903100e3e515903100e3c5159031014bc705903101e6e759883101e6d759883101eae749883101ead74988310266f53988310266d5398831026af4398831026ad439883100e6e519883100e6c519883100eaf419883100ead41988310066e75588310066d7558831006ae7458831006ad74588310266f53588310266d5358831026af4358831026ad435883100e6e515883100e6c515883100eaf415883100ead415883100ecf315883100ee6315883100ecd3158831026e531588310347f76d48310047d76d48310063e64d48310063d64d483101e6e62d48310066d62d48310047f76548310047d76548310063e64548310063d645483101e6e62548310066d625483102cbf76d0831004bd76d08310063e65d08310063d65d08310059d73d083101eae62d0831006ad62d0831004bf7650831004bd76508310063e65508310063d655083101eae6250831006ad62508310167a7598031016797598031016bb7498031016b874980310267b5398031026795398031026bb4398031026b943980310067b5298031006795298031006bb4298031006b9429803100e7a519803100e78519803100ebb419803100eb94198031004bf745803102cbc74580310067a7558031006797558031006bb7458031006b874580310267b5358031026795358031026bb4358031026b943580310067b5258031006795258031006bb4258031006b9425803100e7a515803100e78515803100ebb415803100eb9415803100edb315803100ef2315803100ed93158031026f131580310047d739972101e6e729972101e3f429972101e3d42997210047d70997210047f735972101e3f425972101e3d42597210047f7059721004bd739932101e3f529932101e3d52993210863e51993210863c5199321014be7099321004bf735932101e3f525932101e3d525932107e3e515932107e3c5159321014bc705932101eaf20593210347
  | 20 => 0x347f76d4b310047d76d4b310063e64d4b310063d64d4b310055d73d4b310047f7654b310047d7654b310063e6454b310063d6454b3102cbf76d0b31004bd76d0b310063e65d0b310063d65d0b310071d53d0b31004bf7650b31004bd7650b310063e6550b310063d6550b310071d5350b310055d754cb310063e65d07310063d65d07310059d73d07310071d53d07310063e65507310063d65507310059f73507310071d5350731004bf745833102cbc745833102e3e759923102e3d7599231004bd729923100e3e519923100e3c5199231014be70992310047f75592310347c75592310063f75592310063c7559231004bf725923100e3e515923100e3c5159231014bc705923100eb710592310063e64d4e310063d64d4e3100d7671d4e310063e6454e310063d6454e3100d747154e310963f65d0e310963c65d0e31005b571d0e3108e3f6550e3108e3c6550e31005b77150e310047f7558a310347c7558a3100c7e76d4a310063e64d4a310063d64d4a3100c7c7654a310063e6454a310063d6454a3101e6e6254a310066d6254a3102cbf76d0a31004bd76d0a310863f65d0a310863c65d0a310059d73d0a31004bf7650a31004bd7650a3107e3f6550a3107e3c6550a310047f75582310347c7558231004bf745823102cbc745823102cbe74d9531004bd74d95310347e76d95310063e74d95310063d74d95310047d72d95310047d70d95310047e76195310363e74195310363d74195310365d73195310047d72195310047d70195310063f65991310063c6599131005ad729913102e3e759913102e3d7599131004bd739913102e9d739913102eae7299131004bd729913102ead7299131004ad7299131004bd719913102eb571991310963e51991310963c5199131014be70991310047f75591310347c75591310063f65591310063c65591310063f75591310063c7559131004bf73591310069f7359131004bf7259131004bf7159131006b7715913108e3e515913108e3c5159131014bc705913100c7e76d4d310063e64d4d310063d64d4d3100d7671d4d310275431d4d310055d7594d310365c6594d3100c7c7654d310063e6454d310063d6454d3100d747154d3100cdc7654d3100dd47154d310365f7654d3100d5c7654d310065c7654d3100c5c7654d310071e6454d310071d6454d310055f7254d31007577154d3100d5e7154d3100d5c7154d31007547154d3100d547154d310265f6154d31027576154d310055f7054d310063f65d0d310063c65d0d310071d53d0d31005b571d0d310063f6550d310063c6550d310071d5350d31005b77150d31027943150d3102cbe74d8931004bd74d89310047e76d49310347c76d49310063e64d49310063d64d49310055d73d49310047e76549310047c76549310063e64549310063d645
  | 21 => 0xe7518d410053d7518d410053e76d4d410053c76d4d410063f63d4d410053d72d4d4100d3e71d4d4100d3c71d4d410053d70d4d410763c60d4d41004be7694d41004bd7694d410053d7594d410053e7654d410053c7654d410071f7354d410063f6354d410053f7254d4100d3e7154d4100d3c7154d410053f7054d4106e3c6054d41004be7614d41004bd7614d410053e7514d410063f65d89410063c65d89410063f75d89410063c75d8941004bd73d89410063f53d89410063d53d89410863e51d89410863c51d8941014be70d89410053e75989410053d7598941005b571989410053f75589410053c75589410063f65589410063c6558941005b771589410053e75189410053d75189410053e76d49410053c76d49410053d73d49410063f63d49410063f62d494100d3e71d494100d3c71d49410053d70d49410663c60d4941004be7694941004bd76949410053d75949410053e76549410053c76549410053f73549410063f63549410072f72549410063f625494100d3e715494100d3c71549410053f705494105e3c6054941004be7614941004bd76149410053e7514941004be76cc941004bd76cc9410053e75cc9410053d75cc941004be768c941004bd768c9410053e758c9410053d758c941004be764c9410053e754c9410053d754c941004be760c941004bd760c9410053e750c9410053d750c9410078d320c94100db6710c941005b5710c941005ba700c941005b9700c9410053e75d85410053d75d85410063f65d85410063c65d854100f3651d854100f3451d854102f3675d854102f3575d85410073765d85410073465d85410073753d85410073553d85410073752d85410073552d8541005b570d854100d3e75d454100f3651d454100d3f75545410053e75981410053d75981410063f65981410063c65981410053f75581410053c75581410053e75181410053d75181410063f65181410063c65181410059e73181410059d7318141005ae7218141005ad7218141016ba601814102e3e759904102e3d759904102eb5719904100e3e519904100e3c519904102e9f4358c410063e64d4c410063e6454c410265e6354c410065d6354c41004bf7650c4102eaf42588410063e64d48410063e645484101e6e62548410066d6254841004bf76508410265e73997310263f43997310263d43997310047d72997310047d70997310263f43597310263d43597310047f72597310047f70597310263f53993310263d5399331004bd72993310963e51993310963c5199331014be70993310263f53593310263d5359331004bf725933108e3e515933108e3c5159331014bc70593310269f30593310365e6554f310255f7654f310065f7654f310271e6454f310271d6454f310055f7254f3100d5e7154f3100d5c7154f310055f7054f31
  | 22 => 0x8f4108e3c5158f41014bc7058f410053f76d4f410053d76d4f410063d63d4f410053d72d4f4100d3e71d4f4100d3c71d4f410053d70d4f410763e60d4f4102cbe7694f41004bd7694f410053f7654f410053d7654f410071f7354f410063d6354f410053f7254f4100d3e7154f4100d3c7154f410053f7054f4106e3e6054f4102cbe7614f41004bd7614f410053e7598b410053d7598b410063e6558b410063d6558b410063e7558b410063d7558b41004bf7358b410063f5358b410063d5358b4107e3e5158b4107e3c5158b41014bc7058b410053f76d4b410053d76d4b410053d73d4b410063d63d4b410063d62d4b4100d3e71d4b4100d3c71d4b410053d70d4b410663e60d4b4102cbe7694b41004bd7694b410053f7654b410053d7654b410053f7354b410063d6354b410072f7254b410063d6254b4100d3e7154b4100d3c7154b410053f7054b4105e3e6054b4102cbe7614b41004bd7614b4102cbe76ccb41004bd76ccb410053e75ccb410053d75ccb41006ad62ccb4102cbe768cb41004bd768cb410053e758cb410053d758cb410069d638cb41004bd764cb410053e754cb410053d754cb4102cbe760cb41004bd760cb410053e750cb410053d750cb410069d630cb41006ad620cb410078d320cb4100db6710cb41005b5710cb41005ba700cb41005b9700cb410053e75983410053d75983410063e65983410063d6598341016b860983410265e6354e410065d6354e41024bf7650e410069d6350e4101e6e6254a410066d6254a4101cbf7650a41006ad6250a410347e76d95410063d74d95410047d73d95410047d72d95410047d70d95410047e76195410363d74195410047d73195410047d72195410047d701954100cbe76d51410063f65d51410363c659514100cbc76551410063f65151410047e76d4d410347c76d4d410047e7654d410047c7654d410063f65d0d410063c65d0d4100cbe7690d410053e7590d410053d7590d4100cbc7650d410063f6550d410063c6550d410069f6350d41004be7610d410053e7510d410053d7510d410047e76d49410347c76d49410047e76549410047c76549410063f65d09410063c65d094100cbe76909410053e75909410053d759094100cbc76509410063f65509410063c6550941006af6250941004be76109410053e75109410053d75109410053d73d95410053d72d95410053d70d95410053e75995410063f6599541005b57199541005b771595410053e76195410063e76195410053d73195410053d72195410053d70195410063f65d8d410063c65d8d410063f75d8d410063c75d8d41004bd72d8d410963e51d8d410963c51d8d41014be70d8d410053e7598d410053d7598d41005b57198d410053f7558d410053c7558d410063f6558d410063c6558d41005b77158d410053
  | 23 => 0x7d3f765085107d3d76508510053f735085107f1e63508510063d635085107f1d63508510061d63508510072f725085107f2e62508510063d625085107f2d62508510062d625085107d3f715085107e3e615085107f36615085104d3c705085107f3a605085107f39605085100c7e76108510047d76108510853e74108510065d63108510066d621085100c7e76cc8510047d76cc8510053e74cc8510053d74cc8510065d63cc8510066d62cc85100c7e768c8510047d768c8510053e748c8510053d748c8510065d638c8510066d628c8510047d764c8510053e744c8510053d744c8510065d634c8510066d624c85100c7e760c8510047d760c8510053e740c8510053d740c8510065d630c8510066d620c8510074d320c85100d76710c85100575710c8510057a700c85100579700c8510063f74580510063c74580510047f73580510063f43580510063d43580510047f72580510063f42580510063d425805100e3f415805100e3d415805100e7b705805100e7b105805100e7810580510067b74580510063b74580510067a74580510067974580510067874580510063874580510067b73580510067a73580510067973580510067873580510067b43580510063b43580510067a43580510067943580510063943580510067843580510067b72580510067a72580510067972580510067872580510067b42580510063b42580510067a42580510067942580510063942580510067842580510067b32580510067a325805100679325805100678325805100e7b715805100e7a715805100e78715805100e7b415805100e3b415805100e7a415805100e79415805100e39415805100e78415805100e7b315805100e7a315805100e79315805100e78315805100e7b215805100e7a215805100e79215805100e78215805102e3e74997410047d739974102e3f43997410047d729974102e3f42997410047d709974102e3c409974100cbc745974102e3c74597410047f735974102e3f43597410047f725974102e3f42597410047f705974102e3c40597410063d65d53410363e655534100cbc7458f4102e9f4358f410347f76d4f410047d76d4f410047f7654f410047d7654f410053e7590f410053d7590f410063e6550f410063d6550f4100cbc7458b4102eaf4258b410347f76d4b410047d76d4b410047f7654b410047d7654b410053e7590b410053d7590b410063e6550b410063d6550b4100cbc745834102e3f65997410053d739974102e3f63997410053d729974102e3f62997410053d709974102e3c60997410063f76597410053f735974102e3f63597410053f725974102e3f62597410053f705974102e3c60597410053e7598f410053d7598f410063e6558f410063d6558f410063e7558f410063d7558f41004bf7258f4108e3e515
  | 24 => 0x95358051036785358051006bb4358051006b943580510367b52580510067a5258051006795258051036785258051006bb4258051006b9425805100e7b515805100e7a515805100e79515805100e78515805100ebb415805100eb941580510063e7458c510063d7458c5100e5f7358c510047f7258c5100e3f4158c5100e3d4158c5100e5e3158c5100e5c3158c510047f7058c510065f7458c510065e7458c510061e7458c510065d7458c510061d7458c510065c7458c510065f7258c510065e7258c510065d7258c510065c7258c5100e5f7158c5100e5e7158c5100e5c7158c5100e5f4158c5100e1f4158c5100e5e4158c5100e5d4158c5100e1d4158c5100e5c4158c5100e5f2158c5100e5e2158c5100e5d2158c5100e5c2158c510065f7058c510065e7058c510065d7058c510065c7058c5100e5f1058c5100e5e1058c5100e5d1058c5100e5c1058c510065d63d0c510953f76d0c510953d76d0c510971e63d0c510063d63d0c510971d63d0c510061d63d0c510053d72d0c510972e62d0c510972d62d0c510953d71d0c510963e61d0c510973661d0c5104d3e70d0c510973a60d0c510973960d0c5100c7e7690c510047d7690c5108d3d7490c510065d6390c510065d6350c5108d3f7650c5108d3d7650c510071f7350c5108f1e6350c510063d6350c5108f1d6350c510061d6350c510053f7250c5108f2e6250c5108f2d6250c5108d3f7150c5108e3e6150c5108f366150c5104d3c7050c5108f3a6050c5108f396050c5100c7e7610c510047d7610c510953e7410c510065d6310c510063e74588510063d74588510047f73588510063f43588510063d435885100e6f725885100e3f415885100e3d415885100e6e215885100e6c21588510047f70588510066f74588510066e74588510062e74588510066d74588510062d74588510066c74588510066f73588510066e73588510066d73588510066c73588510066f43588510062f43588510066e43588510066d43588510062d43588510066c435885100e6f715885100e6e715885100e6c715885100e6f415885100e2f415885100e6e415885100e6d415885100e2d415885100e6c415885100e6f315885100e6e315885100e6d315885100e6c31588510066f70588510066e70588510066d70588510066c705885100e6f105885100e6e105885100e6d105885100e6c10588510065d63d08510066d62d08510853f76d08510853d76d08510053d73d08510871e63d08510063d63d08510871d63d08510061d63d08510872e62d08510063d62d08510872d62d08510062d62d08510853d71d08510863e61d08510873661d085104d3e70d08510873a60d08510873960d085100c7e76908510047d769085107d3d74908510065d63908510066d62908510065d63508510066d6250851
  | 25 => 0xca510053d740ca510074d320ca5100d76710ca5100575710ca510057a700ca5100579700ca510063f74582510063c74582510047f73582510063f43582510063d43582510047f72582510063f42582510063d425825100e3f415825100e3d415825100e7b705825100e7b105825100e7810582510047e76d4d5100c7c7654d510065f6354d510047e76d495100c7c76549510066f625495102cbe74d8151004bd74d8151004bd73990510363f5399051004bd72990510363f529905100e3e519905100e3c5199051014be70990510363f5099051004bf73590510363f5359051004bf72590510363f525905100e3e515905100e3c5159051014bc70590510363f50590510063d649505102e3e64550510269e7498c510269d7498c510365f5298c5100e5e5198c5100e5c5198c5100e9f4198c5100e9d4198c510365f5098c510365f5358c510365c5358c510365e7558c510069e7458c510069d7458c510365f5458c510065e5458c510065d5458c510365c5458c510365f5258c510365c5258c5100e5f5158c5100e5e5158c5100e5d5158c5100e5c5158c5100e9f4158c5100e9d4158c510365f5058c510365c5058c510047d7694c510053e7494c510053d7494c510065d6394c510063e6454c510063d6454c510265e6354c5102cbf76d0c51004bd76d0c510269e63d0c510069d63d0c51004bf7650c51004bd7650c510269e6350c510069d6350c5101eae749885101ead74988510366f53988510066d5398851006af4398851006ad439885100e6e519885100e6c519885100eaf419885100ead41988510366f50988510366f52588510366c52588510366e7558851006ae7458851006ad74588510366f54588510066e54588510066d54588510366c54588510366f53588510066e53588510066d53588510366c5358851006af4358851006ad435885100e6f515885100e6e515885100e6d515885100e6c515885100eaf415885100ead41588510366f50588510366c50588510047d76948510053e74948510053d74948510065d63948510066d62948510063e64548510063d64548510065e63548510065d635485101e6e625485102cbf76d0851004bd76d08510069e63d08510069d63d085101eae62d0851006ad62d0851004bf7650851004bd76508510069e63508510069d635085101eae6250851006ad6250851016bb7498051016b874980510367b5398051006795398051006bb4398051006b943980510367b5298051006795298051006bb4298051006b9429805100e7a519805100e78519805100ebb419805100eb94198051004bf745805102cbc74580510367b50580510367850580510367a7558051006bb7458051006b874580510367b54580510067a54580510067954580510367854580510367b53580510067a53580510067
  | 26 => 0x1eb7425843201eb5425843201ed7325843201ee6325843201ed53258432026e53258432006c532584320167a7598032016797598032016bb7498032016b874980320267b5398032026795398032026bb4398032026b9439803201e7b529803201e79529803201ebb429803201eb94298032004bf745803202cbc7458032006cd32580320067a7558032006797558032006bb7458032006b874580320267b5358032026795358032026bb4358032026b9435803201e7b525803201e79525803201ebb425803201eb9425803201edb325803201eea325803201ed93258032026e93258032006c932580320365f5358f510366f5258b51004bf745835102cbc74583510367b5058351004bd7399251004bd729925100e3e519925100e3c5199251014be7099251004bf7359251004bf725925100e3e515925100e3c5159251014bc705925102e3e64d52510063d649525100d76719525100575719525102c7f765525100d7471552510063d64152510063e64d4e510063d64d4e510053e7494e510053d7494e5100d767194e510247f7654e510063e6454e510063d6454e510265e6354e510065d6354e5100d747154e510053e7414e510053d7414e5102cbf76d0e51004bd76d0e51004bf7650e51004bd7650e510063e64d4a510063d64d4a510053e7494a510053d7494a5100d767194a5101c7f7654a510063e6454a510063d6454a5101e6e6254a510066d6254a5100d747154a510053e7414a510053d7414a5102cbf76d0a51004bd76d0a51004bf7650a51004bd7650a51004bf745825102cbc74582510063e7458e510063d7458e5100e5f7358e510047f7258e5100e3f4158e5100e3d4158e5100e5e3158e5100e5c3158e510047f7058e510953f76d0e510953d76d0e510063d63d0e510053d72d0e510953d71d0e510553e70d0e5100c7e7690e510047d7690e5108d3f7650e5108d3d7650e510071f7350e510063d6350e510053f7250e5108d3f7150e510553c7050e5100c7e7610e510047d7610e510063e7458a510063d7458a510047f7358a510063f4358a510063d4358a5100e6f7258a5100e3f4158a5100e3d4158a5100e6e2158a5100e6c2158a510047f7058a510853f76d0a510853d76d0a510053d73d0a510063d63d0a510063d62d0a510853d71d0a510553e70d0a5100c7e7690a510047d7690a5107d3f7650a5107d3d7650a510053f7350a510063d6350a510072f7250a510063d6250a5107d3f7150a510553c7050a5100c7e7610a510047d7610a5100c7e76cca510047d76cca510053e74cca510053d74cca510065d63cca5100c7e768ca510047d768ca510053e748ca510053d748ca510066d628ca510047d764ca510053e744ca510053d744ca510065d634ca510066d624ca5100c7e760ca510047d760ca510053e740
  | 27 => 0xf425963201e3d425963200c7c715963201e6f21596320047f705963201e3f529923201e3d5299232004bd7199232014be709923201e3f525923201e3d5259232004bf7159232014bc705923201eaf205923201ecc3258e320063e64d4e320063d64d4e320056d72d4e320063e6454e320063d6454e320056f7254e320063e65d0e320063d65d0e32005ad72d0e320063e6550e320063d6550e320071d5350e32005af7250e320047f75586320347c7558632004bf745823202cbc745823202cbe74d9532004bd74d95320047d73995320365d73995320047d72995320366d729953200c7e71995320047d70995320047f73595320065f73595320047f72595320066f725953200c7c71595320047f70595320347e75d91320047d75d91320063e65991320063d6599132004bd739913202e9d7399132004bd729913202ead7299132004bd7199132014be70991320063e65591320063d6559132004bf73591320069f7359132004bf7259132006af7259132004bf7159132014bc70591320063e64d4d320063d64d4d320056d72d4d320274c32d4d320063e6454d320063d6454d320056f7254d320274c3254d320063e65d0d320063d65d0d32005ad72d0d320278c32d0d320063e6550d320063d6550d32005af7250d320278c3250d320063e64d49320063d64d49320055d73d493201f4c32d49320347f76549320047d76549320063e64549320063d64549320055f735493201f4c32549320063e65d09320063d65d09320059d73d093201f8c32d093202cbf7650932004bd76509320063e65509320063d65509320059f735093201f8c32509320347e75d85320047d75d853202cbe74d8532004bd74d85320347e75d81320047d75d813202cbe74d8132004bd74d81320263f43994320263d439943201e3f429943201e3d429943200c7e71994320047d70994320263f43594320263d435943201e3f425943201e3d425943200c7c71594320047f70594320263f53990320263d539903201e3f529903201e3d5299032004bd7199032014be70990320263f53590320263d535903201e3f525903201e3d5259032004bf7159032014bc705903201dcf764c832006cf764c8320074e754c8320074d754c83201f4e654c83201f4d654c8320078e744c8320078d744c83201f8e644c83201f8d644c83201fc6614c83201fc5614c83201fca604c83201fc9604c83200e77759843200e74759843200eb6749843200eb57498432026775398432026755398432026b74398432026b5439843201e77529843201e75529843201eb7429843201eb542984320047f75584320347c7558432006cd3258432006777558432006747558432006b67458432006b57458432026775358432026755358432026b74358432026b5435843201e77525843201e755258432
  | 28 => 0xe420063e6550e420063d6550e420069d6350e420047f75586420347c755864201cbe76d51420063f65d514201dae72d51420363e659514201cbc76551420056d72d4d4201cbe7690d420053e7590d420053d7590d4201cbc7650d420069f6350d42004be7610d420053e7510d420053d7510d4201f2c42549420347e75d85420047d75d85420063f6599542005ad7299542005af7259542004bd71d8d42014be70d8d420053e7598d420053d7598d42005ad7298d42005af7258d420053e7518d420053d7518d4201dae72d4d42005ad72d4d420063f63d4d420072e72d4d420053d72d4d420072d72d4d420052d72d4d4207d3e71d4d420053d70d4d420763c60d4d42004be7694d42004bd7694d420053d7594d420071f7354d420063f6354d420053f7254d4207d3c7154d420053f7054d4206e3c6054d42004be7614d42004bd7614d420053e7514d420072f53d89420072d53d8942005ad70d894201f2e52d49420053d73d49420063f63d494201d3d72d49420072f62d494207d3e71d49420053d70d49420663c60d494201f2f20d49420053f73549420063f635494201d3f72549420072f72549420072f625494201f2c325494207d3c715494201f2f21549420053f705494205e3c605494201f2f20549420053e75d85420053d75d85420063e75d85420063d75d8542004bd73d85420063f53d85420063d53d85420063f52d85420063d52d8542014be70d85420053f75585420053c75585420053e75981420053d75981420053e75181420053d75181420059e73181420059d7318142005b67118142005b57118142016ba60181420047d739944202e3f439944201e3f429944201e3d429944200c7e719944202e3f41994420047d709944202e3c40994420047f735944202e3f435944201e3f425944201e3d425944200c7c715944202e3f41594420047f705944202e3c405944202ead729904201e3f529904201e3d529904202e9f4358c420347f76d4c420047d76d4c420063e64d4c420047f7654c420047d7654c420063e6454c42004bf7650c420063e6550c420063d6550c420047f75584420347c755844202eb741584420263f43997320263d439973200c7e71997320047d70997320263f43597320263d435973200c7c71597320265f31597320047f70597320263f53993320263d5399332004bd7199332014be70993320263f53593320263d5359332004bf7159332014bc70593320269f30593320063e64d4b320063d64d4b320055d73d4b320063e6454b320063d6454b320055f7354b320063e65d0b320063d65d0b320059d73d0b320063e6550b320063d6550b320059f7350b320072d5250b320047f75587320347c7558732004bf745833202cbc745833201e3f429963201e3d429963200c7e71996320047d709963201e3
  | 29 => 0x53d7414d52005ad72d0d5202cbe74d8152004bd74d81520063f64991520056d72991520056f725915200c7e71d8d520047d70d8d520053e7498d520053d7498d520056d7298d520056f7258d520053e7418d520053d7418d5201d6e72d0d520056d72d0d520063f63d0d520072e72d0d520053d72d0d520072d72d0d520052d72d0d520053d71d0d520963c61d0d5205d3e70d0d520047e7690d520047d7690d520053d7490d520071f7350d520063f6350d520053f7250d520053f7150d5208e3c6150d5205d3c7050d520047e7610d520047d7610d520053e7410d520072f43d89520072d43d89520056d71d89520053e74985520053d74985520053e74185520053d74185520055e73185520055d731855200e7661185520057a70185520057970185520053e74d81520053d74d81520063e74d81520063d74d81520047d73d81520063f43d81520063d43d815200c7e71d81520053f74581520053c74581520366d7299452004bd73990520363f539905201e3f529905201e3d5299052004bd71990520363c5199052014be70990520363f5099052004bf73590520363f535905201e3f525905201e3d5259052004bf71590520363c5159052014bc70590520363f50590520365f5358c520047f7654c520063e6454c520063d6454c5202cbf76d0c52004bd76d0c520063e65d0c52004bf7650c52004bd7650c520063e6550c52004bf745805202cbc74580520367b505805201cbc745974202e3f65d534201cbc7458f4202e9f4358f420265e6354f420065d6354f420053e7590f420053d7590f4201f2e4254b420047f75587420347c755874201cbc745874202eb7415874201cbc745834202e3f65997420053e7598f420053d7598f42004bf7158f42014bc7058f420063d63d4f420053d72d4f420853e71d4f420053d70d4f420763e60d4f4202cbe7694f42004bd7694f420069d6394f420069d6354f420071f7354f420071e6354f420063d6354f420071d6354f420061d6354f420053f7254f420853c7154f420053f7054f4206e3e6054f4202cbe7614f42004bd7614f420053d73d4b420063d63d4b420853e71d4b420053d70d4b420663e60d4b420053f7354b420063d6354b420072f7254b420853c7154b4201f2f2154b420053f7054b4205e3e6054b420053f75587420053c75587420063f75587420063c7558742004bf73587420063f53587420063d53587420063f52587420063d5258742014bc70587420053e75983420053d7598342016b860983420047d739964201e3f429964201e3d429964200c7e71996420047d70996420047f735964201e3f425964201e3d425964200c7c71596420047f70596420347f76d4e420047d76d4e420056d72d4e420047f7654e420047d7654e420063e65d0e420063d65d0e42024bf765
  | 30 => 0xf43996430263d43996430047d729964300c7e71996430047d70996430263f43596430263d43596430047f725964300c7c71596430047f70596430047f75586430347c7558643024be76d51430063f65d51430363e6595143024bc76551430347e75d85430047d75d85430063f65995430059d73995430059f73595430059d70d8d430271e53d4d430253d73d4d430071f63d4d430053d72d4d4308d3e71d4d430053d70d4d430763c60d4d430271f30d4d430253f7354d430071f7354d430071f6354d430053f7254d430271c3254d4308d3c7154d430271f3154d430053f7054d4306e3c6054d430271f3054d430063f53d89430063d53d8943004bd71d8943014be70d89430053e75989430053d75989430053e75189430053d75189430053e75d85430053d75d85430063e75d85430063d75d85430063f53d85430063d53d8543004bd72d8543014be70d85430053f75585430053c75585430053e75981430053d75981430053e75181430053d7518143005ae7218143005ad7218143005b67118143005b57118143016ba60181430263f43994430263d43994430047d729944302e3f429944300c7e719944302e3f41994430047d709944302e3c40994430263f43594430263d43594430047f725944302e3f425944300c7c715944302e3f41594430047f705944302e3c405944302e9d73990430263f53990430263d539904302eaf42588430047f75584430347c755844302eb7415844301c7c755935201c7c7558f520365f5358f520053e7494f520053d7494f520269e6350f520069d6350f5201c7c755875201c7c7558352004bf745835202cbc74583520367b50583520363f64993520053e7498f520053d7498f5200c7c7158f520047f7058f520063d63d0f520053d72d0f520053d71d0f520963e61d0f520653e70d0f520347e7690f520047d7690f520065d6390f520065d6350f520071f7350f520071e6350f520063d6350f520071d6350f520061d6350f520053f7250f520053f7150f5208e3e6150f520653c7050f520347e7610f520047d7610f520053e74987520053d749875200e7461987520053f74583520053c74583520063f74583520063c74583520047f73583520063f43583520063d435835200c7c7158352004bd739925201e3f529925201e3d5299252004bd7199252014be7099252004bf735925201e3f525925201e3d5259252004bf7159252014bc70592520063e64d4e520063d64d4e520247f7654e520063e6454e520063d6454e520065d6354e5202cbf76d0e52004bd76d0e52005ad72d0e52004bf7650e52004bd7650e52004bf745825202cbc745825201c7e76951520063f649515201c7c765515201c7e7694d520053e7494d520053d7494d5201c7c7654d520065f6354d520047e7614d520053e7414d52
  | 31 => 0x8001000c00100040020018004000800000040010000000000000000080020014005000000000080010014000000000000080000000000000000100040040004004000c0040028001000000100040000004000000000000000010000002002c000000800100000040030006000c000000000000000060004002000800000080010018000000000000100000000002001800000000000365f5358f540366f5258b5402c7c75587540367b505835402d3d76d52540363d76d52540053d73d52540053d72d52540063f5458e5402e9f4358e540063f5458a5402eaf4258a5402eb7415865402cbc74582540365f5358c5402e9f4358c540366f525885402eaf425885402eb741584540367b50580540247c75593530247c7558b530366f5258b530247c75587530247c7558353004bf745835302cbc74583530367b50583530363f64993530053e7498b530053d7498b5300c7c7158b530047f7058b530053e74987530053d749875300e7461987530053f74583530053c74583530063f74583530063c74583530047f725835300c7c71583530263f53992530263d5399253004bd7299253004bd7199253014be70992530263f53592530263d5359253004bf7259253004bf7159253014bc7059253004bf745825302cbc74582530247e76951530063f64951530247c765515302cbe74d8153004bd74d81530063f64991530055d73991530055f73591530055d71d8d5300c7e71d89530047d70d89530053e74989530053d74989530053e74189530053d74189530053e74985530053d74985530053e74185530053d74185530056e72185530056d721855300e7661185530057a70185530057970185530053e74d81530053d74d81530063e74d81530063d74d81530047d72d815300c7e71d81530053f74581530053c74581530365d73994530263f53990530263d5399053004bd72990530363f5299053004bd71990530363c5199053014be70990530363f50990530263f53590530263d5359053004bf72590530363f5259053004bf71590530363c5159053014bc70590530363f50590530366f5258853004bf745805302cbc74580530367b5058053024bc745974302e3f65d53430271e4354f43024bc7458b4302eaf4258b430047f75587430347c7558743024bc745874302eb74158743024bc745834302e3f65997430053d72d4f430953e71d4f430053d70d4f430763e60d4f430071f7354f430053f7254f430953c7154f430271f3154f430053f7054f4306e3e6054f430053e7598b430053d7598b430063f5358b430063d5358b43004bf7158b43014bc7058b430053f75587430053c75587430063f75587430063c75587430063f53587430063d5358743004bf7258743014bc70587430053e75983430053d7598343016b860983430263
  | 32 => 0x2000800b000000200240000000000000000b00000010000001000400000300020030000001000900000050000001000800400000000000000000000300000000000001000400300000000010007000000200000040008000000000400140000004002001400a0000000000c00000040000000006000800100000030000004000400100040000004000001000100000000004000001400400280010014006000c003001400500080000000001000000000000000004000000001100040010018002000800200240010000000000c00800140030004000000c0000000000000400000000000000006000400400000020000000000800000140040044004000000800040090000004000800000000030008000000400000100000000002000c0000004001000400200040000000000002c0050008000000800200040010020003000000000340020010000000000200080030000000000000000040000000001000000400000000000001001000200080020000004000800600000010000000000800600080000000001000000000040030000004000000200080050000000000400100040010000005001c001000c00700000010000000001800400040000000010000000000000010008001001c0060000006002000000040010004006001000200040030000001002c0000004008000c000000000100000030010001000800000100000000000000400200000020008000001c00400000030000005000000600000000004003000400100000000004000001400700000000008002000800300000000000000000000600080010004011001000000000020000000002800000000000008004000000500200000004003000800000080000018002000000500040010000002000000a00000010004000000400300000000010002000400100000010000008001800100000000000002000c000000000300000020014003001000300000000010000002c0010000000001c0050004003000800000080010000000000000000040010000000000800000040030004003000c000001c003000000000000010004000000000100100070000000000400100000010000000000c00300140000000002000400000000000000000000000000000010000000000000000080000000000000000000080080014003000000000000020000002000000400000040000000000000800180020004008001400000040030000002000000000000030000003000800000080000000008000000c00000000000003000000700000040000000000400300040040000000000c0050004000001000600000030000007000400600040030030001001800100040000000001000000000000020000002000c000002400200000000000001000000000040040000000000000a0000
  | 33 => 0x400700080050000000000000100240020038000000400000000000004003000000000000000018000000c0020000000000800000180060004001001000200100000004001000c00600000000004002000000000000010018000002400200000000010000000000100000000020000000000000000020000002002c0040004000000000100040140000001000c00100000010004000000400400040030030007000000000200070030000001c000000000f00140000004002000000200000020000005000800200100010000001000000200000000000003000000300040000008000001c000000c0030008006000c0010014000002000000100010028001000000e0000000000400000040000000001000800000280030008005000000a000c0050004000000800300000000004004000000000000010004000000c002000000000080000020000003c0030004001002c0020000000000c0000004001001400200040020000000000c00200000010008002000c00000000000004000000000000000010000000001c00800040000000000000000100080060018002000400200000080000000000400900000000000000000800300080000004009000000000000010000000000400100000000010005000400000000000008001000400200000000008001000000000080000004000001c000002c0000000006000800200000050000004000000000000000020000000800300000010018000000400100100060008006000c0060000003000c002000400100000010008002000c004000000000300030000000000c0030000000000400700040000004000001400000300000004001000000200080050008000000800100000010000001001c0020000002000000000080010000002001000000100000000003001800000000040004002000c0020000002000c0040004003001c0030010000001000100000020004000000c003000800100040000000000000c00000000090004003001000100040000000000000000000080030004000001c003000000000000000014000000000000000000004002000c00100100020024000001c001000000100000010000002000000700000040004006000800700100000000000000c0040008000000400200140000004002001c000000000300080000000000000c002000000f0010000000000400000010000000001c0000000000000c001000800100140040004005000000100000150000000001c0030010003000000000080000014000000800400040020014002000000800080010000003001400000100060000000001400000080070004006000000000000010004001000000100180030000003000000000040020008002001800000000000000000000800c00040020004008000c00400040030004001
  | 34 => 0xa92620704d18d144ef84aa97ca4040000000000024c0000000000000000013ac000000000008ec00000000000000000000000025c60000001000c0000000000000000e002000000080000004001000c001001400000180000000003001000100000030000000000c000000000700000050008000000000000340000000006001000200040010004002000000600040040008001000400900140000008000000000c0008001001400000040010000000000400000100010004006001c001000c00100040000000006003800000000000014001000c004000800500000000014000000c0000028000001c00000040030004002000c0000000001000c00000080030000002001c001000c0020000000000c00000080030000000001000000080020000000000000200000030000009000800c0000000000c00000040010000004000c002000c000000000400280000000008000800d0000003000400200000000000000001400000000030008000000800200180040000001000000600000030004000000000000440000004000000000300000000000006000000500000000004000000c00700000040000002000000700240030000001000c003000000b000000000000000000001000400200000030004000000c003000c0020004003000800200000000000003000000000000040010000000c0020008003000000000000040000001000400100000000004000002400000000040000003000400500000030004001000800200040090010002000c000000400200040010000001000400000000000008003000800100000010000001000800100000000000000000800100000010008002000000100100000004000000c00000000030004000000800100040080000001000000200000010008001000000400000010010008000800d000c00600100010004002000000100040010000009000c004000c002000c0000030001000400a000000100000000000000000000b000000000040010000001000c001000c00000040010004002002c001000400600040000000000000400000000010014000000400600100010004000000000000300010004003000400900080020000000000000600000010008002000000600000000008002000c003000000000080050030000000800000040000010003000000200000020014001000400b00000000008003001000400000090000000000c0000008003000c0040000000000800400040010000007000c0000000002000000800240030000000000000a0000005000000100040030034000000400500080020024000000400400400060004000000000000140010000004000000300000010008001000000000040000000006000000500000030000000000400000040070000000000000000000040000000000
  | 35 => 0x1ea21b08000a8681540f30e5236a9f6a3ef192800000001c580007c300005df80000001b7e0000000000170c0b780004b800000001962000000095f0dc8000204200020884af901c413800000000000000000000000000000000000000000000034117e26b28000a0c00007b50000000000000000000000e9e00026dc20b11c6306800019d23e2000212c5cc85ba00000004c000000000fea29280009bc80000000000000000000000000000000000000000000007361e38381864c8cc84b0305a46a7050000000000000000000001a1e000272063800004a700006cb1ab80000000225800000017c62d9261a34e12944ac9de66910000504000000000000000b0400027760910000000000052f290c00000009bb000000000000000000065800000000004a280000001018000175292f00008060000000037a00000003490000000000000000006c1800091d8000000105200000000000100000239a5cc1a1c94e2a083d003a22770268000000000000000000d562bb997a000000093a271600627d639b0b701971ba43e89dac5b8800053200000000000000000000000000001e1003c800011423e6000000025580006b080000000000000151c00000000000000000156c0001b4e0000266000088000000007a5000021e8c3a000000000018c21f40000654184a000000000000003c01b288fd86860000c600001dd000025c400000000181b1a55aa5d298f007600000000000d4a8a500000e802fe000000026d80000000000000000000000006811bba6a229b098aa42c9cf8e5800016f600000003a00dfc4c4000000000003bc80003d0800000021980fd8000a5e8fc20000000000000000000000000000a83800065089f400000008c2999c153800000024100988f6a00018f800000000000000000002c4e3982e6ce23a400000ec0000000000000000000006598e349a48000a7226d02f380007358dae53380008021fce0000000000000000019c400000008880000000151a000000000004928058000637210265c800002e15de00020e68dc1b720000000000000000002c229a8000606000011288ea8368000380a09c00023de000011400027dc528800000000000000f045c2800000016bc00016148b31c7000000007e201c28779efa00000000000000000000000000000000000000256e46f00002bd800000029be0000000138127c57600003220000335131666c8bba87c239000015da000279c867800023c116a00009640001e8c63b1fe83ee166600000000000000381192200010d200000f800000007b803ea3500000000083299898240639e9633ca176000000000007ac3d700000001e2e00006408b0934e000205e4d588f600000009258000000000000000000000750000000025d1b42000000026d18066c880d
  | 36 => 0x16c8a762de22f02e5213845e249c00000000000a040000000127a32c17700008b580007be229a742000041807c8727a2367e01f3678f97ba00000003ac800000000000001fe2831a9180001790000000000000000000000000224a00009060000000982000062b800000019d80000000000027e00000000000db000023380001feca1780000000000000283476580004f6010c5c509b866a9c66000265a5f6a1f20b00000452866081d258c91590b04a480006be857c16780004519b3c07ca970437282252e0f2276c800030481fc53f079240d926a0cda36c00000003b600000001f401f717601e2800027903ce000231627f086e00000003d820c00001c8c00017c8000000000000000001f3e000000000026ea000000000000000000e1e00014f462c81f864d0058000000023a00000000dc4000000050a8000579a40600000000000f3aa1e883000016a852e80009720000a3683f80001d6042f0580411000000000003e800000000000000000073f00005b119f600000000002a600000000000142c00000007a48fb2a4c985000011fe00000009c123044b11d88000000021fa8f60049cb00310000000000089c9c960000000000000027200004591870000000000024622d880b481829662f8059a2c3251e39f25467ac169c0001b4600000000000af00000000142964c00000005d5800000017160000baa1d996a091493280028bb246a1b6644ea2560001e3642084626fe800024f27e800010329f6196400009040000000679800000005ae000130c00000000cca6ce16809de39c04e800000001e590de0e901b214a07e8017250e51006a23c7800000000000002866000000000000000000b3a48f8af83db800018c0000000000000000000001d2c00000000002860000000000000000f716c80001d4e0002702460998a0001222a0b800000000000000000000000000000004ec21160000e780001e86a2e853a000123005ea85a0000420123a9e88799b9c9f280006218000000000000019fc0000f02000000000000001830000a160cc423726e86b1826c6bc824661583d00ba80001b700007830000000000000014321fe800000015629e192245bc80003c826ae3d50ff81b2143e917a22e0791f2a7379c4047c8000a7da0e800025669c400009ec9780745877a9a597685c10aac1b89df60000b845b4217a30e0000069a83a05e158800000001c80000000163c000025a00019ca5a7800000029c00000000000000000000004a0263818f989000000000000000000274e1609de485487bc15294c256e0020000000000029ca000068c000000000000d80000000000000000003b2889036c00000000000000000001e00017b20000cbc00000005dda96e00000004fe0f449c9000000000000000000a0a16c01c080000000000000000000
  | 37 => 0xf4248656521e000000002c600008630000000171800014447b01bbc9f000003b4000000000003e79ace4e2a67e3f114f0101217e4f5819800000000000000000008e00026ba000000000000000000000000000000017846030000000000000000000000000476a7ba000180a856800000000003018000064800000002ae2d18d4c961905665a004e9ed179e1250b5a1cc0f82672000063f00007f9038a000000000002a64eb800000000000001b6800000001e88000000000015400000000000000000087a000005385e853a00001ba9c1a0000000000000047a00001d1000000009222398cc61f1875c000000000000000000000000000000024e4000152c060213c4d680001d300002150b8c000000036180003a293ee4f80b6a00024f457027a60000000000000000019a800015c40002192000000000000001b2a9060c5236e0001e184770000000165400021d0000000066d0000729800000018021d498ee90d866800000006280000263289c5dd04f2a03a71a00015dc0001474a699dda0fea9fa00005d03ce00000000000552125c4f200000bd000008c111a6ac17aa000000000000001bd1cce00000009ff000000000000000f8699e000000000008f911c200015c200011be64c80006688000000080a9fe000000010382d58474000257600000000000000000000000010f200000000001d620002132000024000000006b980003161572780876819c00ac8bd822ea211fee3ea80006ab80007d6800000000000000228000000000000000000000560800011b00000000000512a2dca710362a5f08cc5f0800096b95ec674000000000000000000000000000029fe00011ca000000000024c4000026079b000082016e60000000000000000000000000000000289800000001dc80000000f9c00000000000000000000000007864c900002be96961b502249c7000009aa32e58b06bc0a4800000000001e3057277c800003308346a694d23f91fa64c880000000704000000029b9a5c8d31c60a7b914c8ec000000026e6000000000000000001a32000000000000000000000038800010e153291b80001b600000000ff007e8d2a3cd22c8000000010f800081000007999ce00000a8209c8a600001d840001bfe000000004ea1e407da318000000019e00000000b8a8fd000000000000000000767a29600018408a7800000012500000000000000000000001b596fa61d9bec000000095280009eb86b84af00007c60000000247a0000000000221a514126c0000000000000000000004848000000000000000000000ade617000000003820000000584000064d8000000000000021c60000a1283b223a00000fa0ef00000000000742800000000007ff0000000000000000007ef09d6561a99820e00003cd8000000152000015a80000000a3200
  | 38 => 0x16180008ae1334a0516e49348a747d11120000248a49d968053f8d5e74e9d1a0000000000000000007cc8b380000001d9400024d491c1f0a000000059b800069f80000000000a92a42a57d023280a1c084e60d980000d7e82a8ccc64302a45ef96327c00000000000000026028d4059278c800014e00006e20000000000000000003ba93589791a281ba0000000220c0000000000000051e19e045204345c20f2e736a666a7f000000000006d593486c713c000012cca96a47c0000a5681b1fb4a090fb685a0000000000000017f80000000000000031f9b821941d1000000007ed842a000000064f97fe00019b83dc00000000a32000263400000007e090d06b100008e307788e7059c85e00007f980001aca548000060e46591765cd1aa675b800000007769359f4822f80000000000000131c0000ea400000004d980000000000000116800006122ec1f6c3d9867a8cd0d8800000000001fc621394462c48000000000000000000000000a41058e00000000000000a5828ac0000ea26b600000001f04000069677480001ac1a2c9550b5c507a40c997a090000175e0000000000000097d87f80000000000275218c8000a1e00000000000000000000004e400016cc00000000000000000000000005840598c2e518000000012660001ca486a000026fa83690d0000000000000010949ac0000040800000000001938a9a775a99c0000e6e90b972e0000000000000004f1d040000000a0c80000000000000082a00004ac0000000000209600008b682b10c655e274200023862628000121a7220108000000165870a1418329993c000110060489d28c0258a9420c640169bc800000000000000000079071a0290000000000000009fc800000000001e200322181cb602f2656828937691206f60000d0a000226213516c615e8f4e0001b247f628b8a538000a28992c05c800000000000002a0000012dca3a81c6822800004a95109851db663394ee7bf03a642115927df000000027d2641023e443232a4e88000349a7aa00000008ef80000000128154961c108a6c000020660002030641a98e3e3a9d04d11da442719ea8ba0000000000000000000d90000356107a0002580000000000000002e80770a53000000000001d58000000000071280080000000000000079010e007616e0178030c000000097000000000000000000000000007aea55625300000000000a1380004be228a000000043a1c8e0000000174800000005088420c5a00026824f400009a70000000000000000000000000000000081280000001bf000000004dc00000000000000000000000000000000000075e00000000001e2a37c800000003e44dc95d20001b2a59d800000000000000000000000000018de2e3a53a1cb139281e9b18000127e9a3800000027e400000008
  | 39 => 0x4160654012800005d0146370000051714b600007b400000000000022000000066b04309db1a829a6800028680001158000000000000000008041c164ce800000000000000000a68000072b05f20b6102e0001c7a0000000a3a24424c78500000046699406f286100007b41cc00001e280000000000000072f8e86000000054d94686258000000000053d80000000000033800033591fa661800000000000000000137196e9540e66429122a00029ea00000000000c360000000000174a0000db87cf1742a478eca7170a4e847000000000006c524447c49cae5e487a8018a43a83e8000000231e0000cf6957a5be4009bc45810000000000079a02fc000000081a9910000192400000000000000000000000000009991746469a04c0001a1687700000000000194800000000004559eda0000000000000000029b2000000000000006a480000000000000000000021f877b9e7e00000000000000000000000000000000000a1b000000000000000000026800000004e26c2008c0000bec0000a425ba293400000000000000169a7e031e00009221b40749166c50e13ba267834693397002e6a36636591369a1a2342f582040000000484000085f04a03e1072a2b092f2207907673c1a0c84b9e6417380006d28000000128ca8d0000000000052f8d8c0001e6e00000008d3971a00000009f88000529000000015aa90f1c2c67f9b322c400004048c20343000074a000000029ce50818a80000a3000000000000de641407e60000000000294800011420608000000000000000008980000872000000000005ca800053c9c820001b020001fa20af97d200000003f603343d28000755a342000024e64e0000a99031c55d15cc6439ece7e6000001400000001e1a00000000000150000000067c058a000000099c000057f1900000247e3f400005938cf0000000000016ec00000005ad2a16000010856b02340000e7220394584030b7a00000009a620ea9848610829004608aa4c05a0a92e0001e00000299e00006fa0001b900000000000062e0002258000253400014428b000000000000000000000000004398000a8c80007a09842468947e81380000000918000000000009d44ba8000000000066300000000aaa000000000000000000000000201c0000000136800000000002081ba63b8071a0000000000000042380000008000000206429e95e8000000058221fe4429434873978618900002aa1c2e00005be0000b169c280000001c9800011381bc000026900000000000a4b1e7c00000005ac80007ef800000002b430f00000001ac001906d09a8000000000000c98000000000048b000094c0e840879e48000000000008b05e0965e0dd9d42000000000014da000000000000003df800000002f0421800000002945ef0000a02083696980000000
  | 40 => 0x25d6a280b4c821231217c1d8031a818a000034a6e59d26a8300002269c940001a548ee9c3667300000000014000200600003742350000000163800005766ada68428984d23ec00000000e90000078420618be0000000000080c000000000000002fd238e0000000000000000000000000000000040a0000c7c000000000000006e1800000029428ef000000002c46079c421e995ea0748a9258781b40992206000266a0549b3a9af80000001c3c427800000000008001dde0000ce676629ac105032c00009840002022000043699f00001b3800000000000000000566000053a90d461807e2817238a00000006c580005a19fae65b000000024ee0000000339261e0002790592800000000000000000000000049e0316613211e0000000000000000020f879c80000000000000255c0000000000000073300000000000000288600000000000000000000000021ea37519de4390000000000066900000000cc8000000044121280908000000000000000000000be61bf00006f9800000020d476e994a3d6079e000166a04d0bac000007844ba3ae8ac1600000000000000000000826a70a1ba7f4872868a80000000be2424000000017f42a5a3280000440000073a000000066f00000000000a25800079404067de82ac62e88ca4448e8c574000000000007828d4200000000000000000000000000007ec15a40000000000000087e942600021664c3940000020520001fd00000000070000000000000000000107a51a0000000000000000000000c01acc000000000017c400023ce36fa746a319de2a5183fc764903405a0af4611182271a80004e5039c00000009f780001e800002a89114000000037b18fe00000000000000000000091d1240000000000000008c20cb40001f1a0b70000000182c4168690830a842000000000006f84fc0000000000018a00003699e52960a6301258e3800000003a3807c000000021200009db8000a7b2240000000000000000000000000156e000069a0000000000000000000000000000548a74c000131400013640c28000000000059c800000000000000000000207238804c6000218800000001d08bbe00026e202c80000000000a8e800033b8000386a23e23409e6000209a000211400000000000000000014a1c480009e0a1800001dca36f2a6a05594b24930000454933688025061c408b4079800067884d800000000000000000000000000009dd0000000000095f8a681bf99f21a61c1e147982a96c2302000000096c80004be8000000080839a0a90862820600015ca0759c0e0000bc4000161a00000000000000000000000023c22318be483311f0044111661b0d0819f80002b20bd20002922422102c7b7a222000017600015180000ca0941187482327f400000008759804000227a77080004098000
  | 41 => 0x23eb00e4000000000000000000000359a9d40001d4c9de9bb800001a806da27071f962800022a6608053c000000000000000001d4600000005ac000000016a40001d76988000078e80006268000000274416b0000000025e000000011e800017780008560a6200002e44e78000000218200000000002482268000022903200000000000000032b800000016a64f48000000000050a000016900006db876400000000000000000044800000000001546000154a89080007d70000323000000000008968000a759a8a53e9d6827697ca89a088200019540000d9a7b100009e01e8e36283969ee164832e0a3a64b828e01b9feaa221a7828388de000000000000000000000000298a135845a76080000001cb200000009b1213a14704b20000e4295e1c6400012d4a5a000000026480001e441f68000436a3cc000000000001d439f9f7000000009bf895400000001658c5e0000000000137c12923c020900000000a9445f800000010a00000000a2a000000029e6a6d800000022bc0000000000046e0001508a0700001851e76000165242a00007880cfa4ab07fea4502e8a5611b2000000000000000000000000000000018ea0000dde000000000005c44bda5de49919809510af202a8000000146e2041a203f89b303f529f417a85401d880920b986800000000000000000000006bc120400006ba0ef93e669d29860359abe5ea0e4a2d40b5844180000001b447fe28fa00000003c18000000000000000007c98cfc00000006a800000000000000000000000000001926000000000000006dea67600000009a005022e219d283d1a7a0000a38000034e00000000a8a2020000000322a74075400009038bf078200000000000a6100001dd0000000000000000000000000000000000000000000000000000000019b600011ce8ad2a6e21c8000000036a75c0d5c2b8809800024140000fca1b922b600000005ba800000000004510ca89df9e1223c8aa6126854200009ac6a784426a595ee9ff80002a61e4c8b50de838e8fc00371bd08581f02332a2f29f190042051576a892a0297b80000ec0dd02b1000070180006ef8eb8a7c0000787800035aa568000013200012460001a18000000000020ca00000000000000000000000000002700000000000000000000000000159175c9548000859162025124289398c6e00005240000000914294a7bb8000000000000000003de80000001c0c000000000026d88728000000000030c0000000000020f20460001f7200000000000c4482600000000000000063a000000000005908be80007c40b86a81270800000004c20000518989863d89ec16e00480a7800043a8f4600000000002900769819c27c80008ec8000524000000003844981e22a3319481da980e9961f428339fa00cb91b876196f0921228c064
  | 42 => 0x680005400aeaa350000000000052b8000000000000000000000000000000093c23f000000000000000123092a61483d200000000000000000000016a000000024f683c2a70000000000020b439180000478000000000032880002c005fe91c8b4440c15f6970837898d800000021e224a0000a7716ac6be107027e91988e5000069800001b8000000000000002170000000000000001f100000001f1c000000013d9470000000009e11d886b800000000000000a200001eb600023b66e780000001dc822f000000000000000000000239e66fa660000281a18d860a7851a506d693c29d5a4d8a9091b604100003272284313919e74e00007c3a9300002a407bd12a200d1ac84820622053296ca0609909b580000000000a3399d448f00004b01d4a4310be80001d0665188065a4000025ea16e993888c6e3028617e8000000000036e800038600005d308ac00027882fe11343a58000000000000000000001f940001e5a0001e167d480002bb03520000000000000075900000000000000000000018c894880000000000000000000021a064600006238fd23100000000011205ba59ea9100008a2272a8898c340000000a64213051d841a0001826876107e0b1800000003720000000000187e4d3269403d000004820766d61aac00018da51a8454a71800000000009d787d87f7994c0fd0c1c0000bd0000000000019c259e234aa141f54000086c000025c9ce18d470600000001b620001d4400029206e004be0001c520000140000000032f800044700008e080009e4800000015e40001b4c58980004328000000000000000000001e586429f245bd0e2a00019a60000000000291c0001c4c655800000000000001c76000000000000000000a483c6000073e0490a2f01ba000196a95c9fac453800033e0000000000098b982825c0eda3c980007cb94840001ce2000000000025a400000001e0a5e8000000000000000000222049007a0001612243800000016d8927800004c23968f11c5600000000001f5800026a67a0264a0000000245000076e00008188b72a1905ca0001ee29fe89cc6458000014a8ee000000000000009341ad600020a0000020e00005222ff000000000000000f7871b8b2e3a9800092b000000010aa2f000009d5068e000280027a98b80000e4800000005ad800002b8c4623d0000000000000000009ad99ba00010660002a3e5910fcc000000000018b49d8925600017b88f5000076f000038f800071d1eb27080000000000000013c600002a0066a1bc83c800000014c46fa14cca059a0e12a20547240d0e50200006bd000012b8000000023647ba6c69638000000000000000005c38f6c00014ca28880000d2072400001da41c800000000001288ad0000000000000000001c880001a34000000094527ea8f2000000013e
  | 43 => 0x528f1a8a4047000052d1a380000000a6ea6ac17b101a0f98b4e9a4045c000000072288948278000771206854500004b4998e00022fc27e02b208620b80588c4a0000000a8f0df400015020000000000000000000006c1295a000000000000000000000000000061f0f30a18968401a932c9d69952a8891cc00000000000b1c00000000000310000000000005c80001c9a82180000000000000000000028e6158270039000003b11ca0000000029b136e51784f83be8000000021a000000000000000001bf63e5957c24404889f208400000f920000000000168c0000fda30786884490340000000000000000000000000193000003545832320000296a0000000a0180000001b0c0000000000000000023840000000000000055795c60000000000000088580000001b1000003de76c000042d84c011f8000000088e0000000118093e867000097e92d043e80820000b36000265c000056a000000000026b8991800000000000000bea00000000000000000171e00000005090bb89f980000000000653a68c171853472180000000000000000093b223800000000001cee000000034d13fe0001f8c50b925200000000000000a24a77800000000000000739876e4f523a07b591ec000000000017b400000008a9100a59c02b600104d02cc16d200012ee36b0000000000000000d08fb8da256b8514578905c0002714000162425e0c260000000000053e00006040000ef65f981ae29310c204da84800000005ff17368cc0000238262400006d26568000561219693e80b00000000000000095c000000000007af88e40000f280001cd200000000000000555800000000000000000000041600000003e000000000000000000014600007fc800057e00005e5800043580000001d7200023f8389000000000000fb0000000027a1160e5c000000000007f200000000000000000118e00000000000000523a094000000000007386cd000000000000002352000000076698bc0000000000016c18f000001c00fc0000cb695680000418bfa00000003b900001bb0000000000000002966c79a8e000000020480000000000000000000003680000b984b202e25838000000000000000008d600001589bdc647a0a80000000912800070080002d98cce67680002fb80002458fba3108000000176e0000000000000000000000000000000000047a8000000000000000000af1538a448000052000000005e4000239200000000000e546040bb430f80002ea075a00006b4a5580000ae800046702b000000000000a7c50ea490920118a770231ca6aa6da33fa49a266800054e987a2e8a4ea8dd2266057800000026f841d17f6a8493c4582a00a7318000000031200000000002a364150e64000000000000004c1800000012d80000000a12800075b0408000289025
  | 44 => 0x17a60bd80000001ef000000000001bb602219f400000000000000149869e86f9ca2a4f8000458a43201a000095b1d9c0b30000000000039e8000000000080d00408141d7e15699d661c800000006b63b580000000000605800000014d8834800056e8000000000062d9be20000000000000000000002df8000000000021e00000002870000048a732800000024920001a4e000000092b8000a6008f815e08021ff268a2dd20ae45d04e67162306000018c6cd81a2a20800060223980001e9a0001dea0001ee800000000000000000000000000000001b8e1d800000c600007a800000000000000230e00000000001eaca898c5000000005a3800000007f4a6d02ca3ae800018600000c69b8a000165a00000003b50000000000000025240001b74000000000017e80000000000225c0281422323a9e05590000515853221d1bde55a234400022440001a4600000000000000000000000026aa00000000000000000000070c092400021240000fc6000241c0000000000000000000007db95d483780009b4a60432629100000f520001ea80001ce8000162a0001e6a9588000000097c3a680000001a420000000000000000003d869880002b70aa400000000000000000228600000000000000000037e4d8800000000e696a0c18575930200000000000000950a7f61c600000000746000000000000000000000525800006f9a3e986117067023b40000a7e4e328fe11e00008e98000000097600000000000000000135200000000000000a7c80000000000631000000000000001ad02d211c000000001ee8000000084c0000000000000000009c400019e4000000068880006f600000001a3a38a0000000000000000000001c54000000000000007dd1c6c393257a8160e3c52280e8000000081b8a44000000000000000d780240000000000124a0e31d6a549a26a00025200000000000207c000252800000000000a2a97291f8000079c000000073a800000000000000000000000000000006a1800000000001960000790a6326b8800084f800054b9bf44818000000000006b094a0000000809800092c80001fb80009e900003fb80000000000a0b0000000000000007b2000008000024b400011fc41305b078100000000000000000059900000002044000000068000000001188000000000000000001a7054321343870bcc97f8588320a9889af1046265000000000001d3a5dc4988ae8a498ede0000000000000066800000000eee2df00000000000000000000000007ab8b8000000000b38000000081a0000000000000000021cc0000000000049c00018a4303000000028be000062000000002ef0000000000086d0000000000000027a0000113c0348000000000000000000000000000000000012f40000000000000000000000001f7e0571a
  | 45 => 0x6e32c00005f780002fc995c0000000000000000000000000000000227c000013e0002a0a000000000013960e50e2c000000022e0280000000000000000002212000000060000001818480000000051e89a82ca97ac619000000000004498000734000000008008c6a03623680000000e5a7738000000132a99a0726875270e554800069c8a9c106116e145916c00025f43c306e6568154e929a748000000000028aa00000000000e2e0002902000035a74ca3ac0000000000000047900fe92a000000000000000000000000000012b80a6000000003b63d69e6269a89360000bfe2da000057c0000000000067380001d21dd8000000097f000026e80003b70000463000012e000065f9ae4262039829911de8708c480000000537025685ca2de00000000b68bb60000000000099c4288000a1a000000013aa8bf8000176800000000009b5000083d8000000183e117800000011d0405a0c830004cc198a44e9ac85569238a0c47d8000005800012118e46d480001c00000000139c00010fe187000000000000000000056262800017f0000205a00005d89a79e9e4421f5e96b05e687d8d501d2977c5fc892c49ba73c2cf00004a38000000000000011e600014d4000042896511b496d000000011c409b9a569cc9a30000115e5918000000000000000000000a72000000000000003d91f140001bc6000000038c800047887f640a27c2465061a35a27b6401803a0001dfa88b00009498684358800000014d62c993e466b9f9662080006faa03e29606be000240a000000000000000000d90000000059a119224d0a02524a37c00029526cb865a87b13606a0000055107547de000000000000000000000277200000000000000995186200028c06fe2640851276433a1a76000259c00018e870f80000000000195a6ee5f58ece214a4c883122280000ea87a6191a49e800000000000000000094000000008fa0001e7a9e59a0600000000001cba000047c55e8ace0001d58000000000000000e48e62000191200010f82dd9f9e38da7ec00000000000d226359c1040880005cb00006bf922ea3c2a660000000000000000000001919dcc000000078b0000a64800000000002db0ba47f800003a0800000000000000000137800000000000000000000000082e92b00000000000000000000000000126000000000000004d416da000000000018f458b80004f3800050d80000000000a250000000079a114891e752000000000000000000000000000005f60000c22512141c1999b1234ca90e1cd9b9400013dc9eb02120000000000000095380000000d6c7d3800097389c648807ec088000031998e698380001f78c329e38402504800023600000000c800001dae0001ec8000000089f8000000000000003b4000000000000007d800004050000a1526cc0
  | 46 => 0x9dc00000001e703278000015000000000006fb80000001fa4344000000000000000000246aa1c00000000000000000000030a0000497800068f09967f20ca42c0989e0001a1400000009c9943c00025e600016b80000000746050e8b28000000000000000001b300000000000000000000024de0000000000000000000000000000000000098e9baa20a041ca2313a427b819428d298c000070c00000006998000a378000a691ff635c1c04000000000003c40000000000220a6ac80002429d3c3c91354388800000024c6a5f9b7000000006ff21b800011228ae959e0000000000000000015a61e900000000000000000013ea92a3781ee6000000080a823828707d2a50066c000000000000000001d12a8b203a00004ca0f50000000000000012a4a2c000000000ba43b8dca000000000011aa00024f88688ab27ee9650717a33658f950402513680001ff00000ef058e8d3a000000000000005019aa888380000fa18e200003fea1d8a5c33b2810000000000000003cb136c00000003ab0a0000000000000e98a14835c00000000000000000288000000000001854000235e00000009458000771800067a000043300000000000000000060e98b000028c438c000000003e0000000094300000618000a8b8d282b98000a730000a98985e00020d815d27500001f620002032000167e96e8000474800000000000000000a650a18000208e4299990000000000016d600000000000000000252e270800000000007392a743a500007958000928800000000003d3000000000004ea192aa388000000117c000058c8480000908252a000000000000000000000000000000017c04a100000ae0000000039080b136a00000004408c02968000094f80000000000843800000000003b8800051b0000a7e0e600001c3200000004a9800000000004021c7862126880001c80000057e5e900000ce80000000000000076c8fa0000000000000021aa27fa4ba00000006fc8000000287200000000ca00006c39e3c00013fa0000000000000000009f60000304374804c8640000000000074aa38077b17e0000000000007aa00000001c70000000000000000000000000000087000024b06b700004f3000042d18cc26f00001e610ba09f129e00000009329daa7c800000000b14000000000024cc3898f8a00008502a793ca2ce1da87e2893041a146400000d4031800049a0b4a0eb807293f9f9c4b90000478029c0000000950000056425bc000000000023a27b188d60001c38a4f00009800000242000023f80000000b1a993056e60e000000010620c08ee8334138848700000000000000000000000000000000000000000018d20000000559892ea4a000000000000001078961000000013b2a37000095a8f2a0001048337800040a973800000004c1000000f9
  | 47 => 0x83f9e9c000000000000000000000000286e0c18ce2702800021a021498284fc10c800087ba564000000085080000000dda3608d600000000422a0ee00026163ab80000b40000211a8d25f380005689bc200004120000000000000000000000000000a2d295c00000000000386a9a121e00005f493f0ebc000000000002fa00000000000000046000000000000000000000000009d000000000000000ada000012c78180008a8800000012a81908000000000021880007b7158e70ea03c0000c703f5800000000000002122727205600000009ce85460001de8000275c00000000001d2e000028c0948000000083a000000000022d2207285655500000000000000000000000003cf12f01260b424f680000001c460928000000137e00000005722360294800087f00000000000000000054f00000000000000000000000000000000000000000002f8a171c12000134a0000000538978e032190835d25cc3c42a7200000005668c683ea00000000c100bb096e9c1a156120873c0000000000000033700000000000000159c0001f90000000000019945c80000000000000007d6000000000000000002458000120202f80000000000a078bf61709bca0000000000297200015be000185a0000000a45800000013f4404103c1cb8fe02a80ed23638000000000000000000f58000000000097a800000021000000dfe000055400018a2000123aa8e1bb40f000004108000a3817a200000000000b0800020249660000000106a000000000000009bd00a602d8000000174e37d80005e2a0be00d8df0254207e3df17946ba9a900000000000000050c287e0001aba00000007ea09aa4c9833872f0000000055c000072200014a600020d600010e20000170a1300009fba26e000188c9d800007c880000000ae021583f09c78000000191400000000000000000000000000006f31c1c00000000000d200001466000012e9f30c5c75d00005de17d8000000000007ca97824640001b6a49c0cac3028000581931a0000b3e5268000000000000021621911098113a67a0a294d01b19722000000049d0000000000000000000000b9c73d087689b00000001a483ed00007ff9a10906800000000007599498000000000015bc2819a6e0000000000000000000005de9d000002838156120021628a60001eca80481e8853005e000000000000000001eaa5ed89400002a502e40000000272e21a80000000c6c00013b87e3800000029547ea8ab65a8915c5cf0a868938000000000000016ca0000d368448bae00a8476000228292d8d301f0976419ba1a63ff0000a1110f4000000077c00008bb26a4000000000000000000000000214000000000001ba2a5d29e200000005d89486000131834b000000027346d70db20000000000147c00000000001d0e
  | 48 => 0x24a09c229b0800000000002788f76515203800013b472d0000a3080000001892911a33a00022920001a6ca840000000000000000000000000000000000000000000822315941400023fe00013de0001a120000fde4e9800000008a600000000000ef84de1740000000000000000000000000000065820a6251810a475920c0000000276221c403aa067f5299a2cd1a6400000000000e442f080000000dc20000506318800000000000001cdc86b000028f8000000020000000004a5800095300008d900000001b642d01b26a6f0000000191c15127686f3a4be7eca16c045a8123770000000253c54d214884100000001020a4e1de000028460000000000165600000002110000000085e000000000000000001b9200000005c90000485800000000003e9829a5ab800000e120a0cf945a000000000009b28a8000014b8000000248c7a20a40000000000018ac65e00000000e740000000157800000024220000000000148c4850000000000058080003459ba000000000000d6e99c9f4a8d180000000000962000099b000000000000000980180949c100000000000000000000a5e00006609bb200000001c29a940b801842739846000093a59f144e00000000000000a65870800008b25dc18faa4e95fa224800000000000000c4c00011a43ac1d4000000005ec0b9e0bb838000002aa0000000000000091982101e3800000000000000000000224c384800008580000000c900000000000000050106ee00000000000de436780005501866000046800004246161fca9a889ae1ab00000000d3e0000f0a96e0672a46a5584b3a9369b2a53227280004868db6000000069600000000000000000045e957e1298000909a8ae000210a00000003f3951673d891200000001c38000000064a0000000938a79a00005485379d7a56d80000001024000000000000003149a0293c8ff4113096866c0acc00000002f68f886db1b600e3a4b8000000013f80000b48b9200002d4a2ca76688c000082c9a8c74813904bb094e6a607b076400c207394aa17325e22b28f90192125816505c00f2008456327ce2ad000000018c643f000000010d800000000000000000000000180000c91f680000000000000031500000001f560001f0800000001f9000000000000000cb200000005e680002a105368860d800000000000000023493ec520a72c789000088200003aa80000000b523568ffa000000000000007c5800000000000000000000000043d800024e000042b80000000a5a000000010e8fa4180225427c1dbe000000009c000096880000000a8a000000000000000000000a3c80003b980000001f3000000000000000000000007100440000efe0000000a9b0d9c0950000000000090780000001c4e263832200000000002a5800011280c3a4c20000000092
  | 49 => 0x11860000000373a2d00e680000000eec000215c07b009e2b0000083700005d4028200000000000ff200013862c3989c0001726000000000022a83c700009751242000084a00006ae2580b3200023240001e607b4a36a8d026e407b8f5e885251872e088a5b70a804b78dee0780db40001a0800021d23c4800076303f25f4054c0000000000000061a80001c500007210da86b7800046b96920000000000000030b00000001b5467e084200000000000000000000056298947af06da0000ad400004f400010922242536a3900000000cc254c000000000008f70000000000000005b63ad00000000f980002512000286a000227672a800070003b800022c429780000001452a9d80000001cec6c829760fb806673e80000000a2c000000066205ee87013ea7939b0a8b99a68003000000000007431f320f2800000003885ce81ca00022aa6f906825561a8471411329131d1c8dd808a90c153e9b7834254a80000000ecc940000000000001a280000001d1e8b680005d98000928245c7f00000a4200005f500007bf80000000e0000005102320000a8a1fc2000000000000005f900004478f16000000000000003730000622800000000000000000000137a00003da07f885ca0a8caa34b80000000d5251ca2f86c028d0000000000000000158000000000000000000000000103800000000000000000000283e000000049227360000000000000086d80000000780000000014300005db097255700000000000000000002416ba000077e37e00000002082230000054a000056585e29060000000000000009b000000008918288000112ca8a8cd86eb22043460b2ca97a14e47225f06ea227842300008a4000000019980001aec02895ce4b5a28086c80005e8000000029622278a1e44627be5fb00000000000000271200000000000000000000000000005e300c000000003ff9a2e711000000006a0506a354000000000000007e48734000000000012e2000000000022ee7a408641df02a848383081cc800000027bc1f81da074500003c38000000131268d8d448769dd45251b5000f1c34756800000001a40000000000000000005fca608aba00000000000000264a2d8000000011c861628a0a0813b04ba0000ab8000000083400000001f344a81d34000000000000003011ab48840000000000070a8000000259a000200e52b000000000006890000a2698aa590a43e0000000000129a00000000001f66000036ea031d5ca0800000000000910215459e89528bd039e64ea002340000000003e200025aa00010000d40d12228800000008a800023d87310afe4268000043a19a93800000000626a3b1e7807320fc0b580000000f8c334968a07a8fae009800010b00000000000000000000000000001158000000000000002f200007ad00004fa236
  | 50 => 0xc88b1999617510c83b180007b0811a089800000028b6000001c5ca018830a80000000000000000000000000001ef22ca000000000002a3212a8de2a462f78000000115a3a48000000000061208c200000005c7000000003ba000000000012c600000000000a2448d2758321109601d00007b900008031aee2f5000000010ec0000fec248000000000000001f1e63c8aae52225b600000000000c945c4a232000000000010ce00006c4000194400000000378000000123800026fa460278c9e8895e00000004860d9432681642521f502b58202148265200025d033a9f0697e1aaa7b600000000f3e0001f84000000e0000f680001c485e629d223390f0716a80a1a911302999f280000d1e00000003038b0600000002d5000000000003b21b5e000000000000000000000900958000000000001a1a00000000001fd69c3000000000000000ebe0001ae020faa5c78d000000000008ee0d06000065e00000000291e8465d26266b50000861800061a197600408e25530000395a00460c8e4e899106c00028044cc1c26000000000000000000000000000083880008d5800000000000000000630000069f0000000000000005b41660dfa0001f4c5af800000027f00000ce085a9b7c000000074faa3008280002169160361000082f000019f278a2270000000000000000000328000000263e0001fc400000005cf8000000106400023aa219800000025ec71880006578000000201a7d1800006f0bca3b021740000f5648a202e00012aa7ce09320000000a3f000000000000000c922840c7600000006e600001eb80000001d544a18000000000031c80001e50000000000000001e2000279e00000000000000a6884c45fe80000000000942a21e000111019d9bd284181b000000000002a549091dfe6d210b800000000000000000161845400000000000000133c00014b047d23d63d2140a812144c000002800000007b3062c7ee00ea0000c140000b221ef8000000000014b00000000000000000011c00007e19e265541be0000099818e00007bd800046c151e000207800013f60000cda0000504000000021f0000000000000001d08dc8d3c0000dd6762800000000000000000321800000000009910000000000074d92ae6501aa46f508860000b5e22e80000000000000129012d1992964800000000005b3912a000006c58d8000000000000000000000bdc0000000000025800025740001cc200007ea0000000000000039d80003e6800067e80000000000000000000000009bc0000000000000000008f4800005f8e5e4d080007ddaa184e096ee0002252468233c000000000000000000d7c8941ff49cc09e000013b6797066a00000000001616000000000000005a68000988a7985e218800000000000288a2b1800000000000000000000000000
  | 51 => 0x790000000000008e9e8a0ea84469290a88000251c8faa248a1d27288a38f50520000000000ee2c78bd8000000060c00000d98000000000044380008380000000000078c123200004ce00022ae0002a4e4e1235c0000000000000000005124e000000000efc000088899d00000000000000046400000003821afc00000000678000000001a00000000001bc000000005c08ba61d0000000000000000b6e4d79e1c4078000000000026180001f511844dd073e0000d7a1fc00006480d1c182000000000001c7a8f80000000000000014a800000028022408000000000013a9a400000000000075800000000000000000000000005aa76380000000000000000000012720001b3e75e000000023220001fdc76d0000000090000000000002388000000067b8000000000028286de629800000023f20000a78000000068980002a382c8364817c000000000000005030000000000000000000d10ad200000008638000000290a0001bd60001e463f200000000c7a00001aa22b800000000004cb82f200000006669744000000000000008fe8000000000069680008ac96220000000000124e13228403c5155a4ce25da3efa3e0000043c000225e0000b9669785bc000000042c8000000000000000000001c2463c0fe80000000000000040e9226000000000000002e0800094b0000000163400000000000000000000018d27c400000008ff0000466890c3fd800000020b0000000000013fc000149e2ac03c6000096c5bf041006800002f1a4120f080000000cf400000000002a1e4fc800067b260c39aa8260000d728c4000000014020720e0c417995817e034c35911ac3c69d305c4175a56c800000009a60001cfe000000061b80000000000000000061e26068ea000023ba30c0258000000000022100000000a5400000006050000000000089d00003dd0da0667800072a00006ba15600002438607154200000008a627a8000095c91680004ad80008b9241600000000000000000000000000000001b9a00006920000000000000000000000001d7c00029de3408000000000000028d6000000096593400001e5e260836020b8e9c2470000a2394f8000289e412800000009e835d8a506408000000219400000007f694a825600000000a2e00001de491000000000005d20dd8000000091b0000000000088a800000000000000000459833c8de8000000000000016f88ab032a00000002b6000000000000001af686c14c07ae1154976125a00016603858cba2af8d780000804634183606e03708542a205dc9bb0a3d1dfca0f0c967cb23142858ef422807065d50ec25fb84c208315fe9f4007e00028ca000150639421183c20b0a91e27940001570000000056d000025a8000000000000006a60001c720001b7800001420000000371a2e038404f065f26
  | 52 => 0x5708d2000061397ea59d14e0a930000000009c754a6e053199c6000000000001f09e100001ed9758000000000016d485180007a99abc12d80008081ffa09d970691503a80000000636000000000000000d465f7287c92a8ea015b07c096404bc0000000000214a87d19dc2918000000295e00025028c98000000151200001dc37883ac6b480006a7002e505800000027da45ca3ca000000068289d0000000066100000000356000000000000004b68000450000017581443d8862a000000046e80000000000000000035200001aa8000000277c59000000000ae405810c00001e746a88b24000261c11100f06b6a7d465c1236109a4084b988982599df48b89298410125444f80000000dea5f3042e24988c47f31e0e302000011aa4dc0002a48000096200000003f9800000001f453926f60001cc813ba642795000000000000870000000000000000000001f9aa851524000000000000000000000918000031d000050392c23a20000000000000016884e80000857800000007ce000000000000004cf800008f2560000130a5da8284000000000000001aa1c7c0000f940000000849800000000003538e0e0001d020001a4a75786c000000002508000000266e38280003ad8000869000022a80009d2a6a8a5916de00000000000000a36237e4bf80009da80304ad00008cf8000a7600005e7020826880000000f720c7965c4640000598800015a12fc000229c47529a8000000000014a03cca9b8000053077e00008f6a6b438516c2000223c000061e00012ca56c0b2010322ea038292400000000000afc2af0da400000004ae8000000000000000000000b60000240080503586e1022c000000053b00000218000632935c04e000000000005428000000000000000000000a3687100000000000807800000015f200026108fb163000029da0001da27489bda8390000000000000000007d910ac7bb1888000235aa6b80005782510146981a92516fe23f236800000003f705a29bf00004cc869400000000001ddc00022be7a90a70159a0b673c80000000000199103e0001b76a95a94428512e800000000000d5400010be000000000012884e680000cc262c00024da4c818340000a3c60f00006eb800003d869c00000a841f00004ef00009c600000000122543800025f94e60000000000000084d9e4a6930cc0000015a91a0c249ec037c7ce800000000001ee016a0001c9200000005eb9cd4a949eea5aa969882480000001080000211a843000000000008440816a5416940000d1aa
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x83e87d91504800107d0e322a09000a8b21942541200159440284a8240029a88750a30480015310ca1a60900026a21d424c12001e643b2649824000b89844c9304800185ac8b96a6100031358d72d4c200052ac18eab084000a6582d4d61080030db04bb0a21000217e1973144200060f322e62884000c1d645cc51080038acc2b98a2100021761e63144200042ec3ac62884000c2e645c8510800185ac8b90a2100031398d721442000626b1ae42884001c66615c851080018aae6b08a210003195c961144200061d322e02884000c39645c051080018b4c6b80a2100031658d701442000e3930ae02884000c71615c051080030b90eb1aa7880061b21d6254b1000d2a432a698e2001a648654921c400107b0f326a1880020fe1d64d43100049bc3a83a86200083e8799150c40010790eb22a1880024d21d41543100144e43ac6a1c20028ac87589428400107b0f32e83080020fe1d65d06100041f43ccaa0c200083c8759541840012750fa0aa1080024e21d41542100154c432869842002aa88650920840030f10cb86a6880028760c6454d100145a432e3a1a2000a1d8319543440030f10cb86a4880028b60864549100145a432e3a122000a2d8219542440051690cba482880030d1db75505100061a3b0eaa0a2000b31801d54144015868edb2a82880270d1d865505100761a3b6a6a0a2000b3180d4d414401b868eca9a82880330d1db525051000598c06a4a0a200bc347654941440016630a38282880034c1d47050510005c8c18e0a0a2000ba1821c141440051690cba2628800295219534c5100145a432e890a2000a6486549214400126f0ea0ea08800a8d21941d41100159840283a822001878865d650440012690ea0aa08800a8d2194154110004d843a82a822000c3876dd15044001870ec3a2a088002cc60474541100461c3b6c8a822007c38761915044025870eda1aa088002cc607435411008e1c3b286a822010c3876d09504400166303a12a08803f0e1d9425411000598c20e2a822000d30741c550440016a30638aa088002d860871541100049d43e82a822001c3876d055044003a60e3a0aa088002cc61241541100049c43a82a822001c387650550440012e10ea0aa0880034ce1d41541100059943a82a822000b30875055044001a610ea0aa0880024c21d41541100159943282a822002b30865055044003a64eca0aa0880074c1d9415411000599c1a82a822000d3373505504400166704a0aa0880034cdc9415411000598c2462a822000b31844c550440016630910aa088002cc611215411000698baa831822001878865d530440015310ca1a60880034c5d5414c110006a8baa629822000b91844c53044001a62eaa0c40880061e219754811000554432849022000d31755052044001ac2ea90a4088002e86112148110
  | 1 => 0x90eb2a629800695205654c5300144e432e898a6002998805d1314c00107b0fb26a0980020f61c64d41300150e43287a826002b188050f504c00107d0fb22a0980020fa1c64541300150e43286a826002b188050d504c00183ac8b9ea418003135cd62d483000532c10eab086000a5583d49610c0030bb06bb0a2180030799173144300060eb22e62886001c56615cc510c0010df0cb90a2180030b991721443000616b22e42886001c66615c8510c0010db0f310a218003135ce621443000436c3ac42886000c4d73588510c0018aae6b08a218003195c961144300061d322e02886000c39645c0510c0018d4c4b80a2180031a589701443000e3930ae02886000c71615c0510c00143b07322a7900030b59572d0f200050ec1ccaa1e4000a2d86d4d42c800183cc8b98a39000307591731472000617322e428e4000c2d645c851c800185aeca10a390003435cd42147200061d322e028e4000c39645c051c8001a5284b80a39000699205654872003437c32e5a9c4000c2f645cb53880051390eb1a871000307d9173146200060e322e628c4000c2f645c85188001858c8b90a3100270ed91701462004e1c322e028c400083d87997418800107f0eb2e83100020fa1e65506200041e43acaa0c4002a988650d308800183d08b9cca900030761173995200060f202e732a4000c1c405ce654800143b0732ec8900020f61e65191200050ec1cca322400083f8759464480030e902bb2a69001a17a1f6354d200050ec1ccba1a40028ac865cb434800185acab96869000a6a20172d0d200050ec1ccaa1a4000a1d8399742480051590cba484900028760e6550920066163b6a4a12400cd2870d494248017858eca92849002f4a1c15250920066163b4caa124000b0d8399542480016530132a84900334a1c2655092005e163b2caa124000b2b805954248017a50e0b2a84900028b61b5350920076163b6a6a12400ed2870d4d424801b858eca9a84900374a1c15350920014d543ee0a124000b89831c1424800174302382849000a6a201748c92001456432e899240029a8805d132480010bf06bb4a2900020f61f64945200041ec38c928a400aa2c8650a514801565100a14a2900034a50970945200041ec3ec828a400083d87190514800183ec8b98a29000307191731452000617b22e428a4000c2c645c851480134590ca10a2900030b5d9421452000686b9a8428a4009b28805085148001876c8b80a2900030e191701452000694a12e028a400083d87997414800143b0732e82900020fe1d65d0520014d4402e5a0a400083e87995414800143b0732a82900020f21d6550520014d4402e990a400186c8759521480034c902b2a429000a2b2197448520014d4402e890a400083d87d93504800107b0e326a09000a8b21942d41200159440285a824000
  | 2 => 0xd700c44000654b12e01888000cb1615c0311000183ceab1e4220003075d563c8440006173aac59088000c2d7558b211000185aeca9642200038358d52c84400061b3aac39088000c35755872110001c4aa4b0e422000307dd563884400060e3aac71088000c2f7558a2110001858eab14422001f0ddd5618844003e1a3aac3108800083d86dd5211000107b0c3aa422000307dd563484400060e3aac69088000c2f755892110001858eab12422001e4b21d524844000616bb2a49088000e0d63549211000f64902a9242200030ddd561484400061a3aac29088000e2552585211000113b0d398422000227e1d63084400044ec3ac61088000c1e7558c211000183aeab18422000b269c16308440006173aac41088000c2d75588211000191ce6b104220003235cd620844001655382c41088000c3675584211000186aeab084220003259cd61084400064ab9ac21088002cb2705842110001932c6b8042200032a589700844000658b0ae01088000c1d7650f52cc00145b05322a5980030759573d0b3000516c14caa166000c1e645cc51cc00183ac8b98a398003075d9431473000617322e428e6000c2d645c851cc001a1a86b90a3980030e99170147300061cb22e028e6000d19435c051cc0034a902b2a639800307d9173d4a300060fb22e628c6000c1c645cc518c00185ec8b90a3180030b191721463004e1db22e028c6009c38645c0518c00107b0f32e83180020fe1d65d06300041f43ccaa0c600083c87595418c00185d08b94ca980030b611729953000617202e532a6000c2c405ca654c00145b0532ec8980020f61e651913000516c14ca322600083f87594644c00145b0532e869800a272197490d3000516c14caa1a600ec1c76d4d434c01da30e1a9a8698037071d95350d3006e8c382a6a1a600ec1c76995434c00161b0532a8698002c66026550d300768c384caa1a600dc1c76595434c00163700b2a8698037461c16550d30014cd43ee0a1a6000b89821c1434c0017230238286980328721943d49300060ebb287a92600cb188050f524c0174390ca1aa49802ec6201435493000516c14cba126000c1d655cf424c00533100b9e84980028b60a6550930014cc402e9992600289c865d1324c00533100ba264980021be0976945300041ec3ec928a600083d87192514c0154390ca1ca29802ac620143945300068ca1ae128a600083d87d90514c00107b0e320a29800307d9173145300060e322e628a6009a1c8650c514c00183aeca18a298026c6201431453000617b22e428a6000c2c645c8514c001a1a86b90a2980030ed9170145300061c322e028a6000d19435c0514c00107b0f32e82980028b60a65d05300041fc3acba0a6002998805cf414c00107d0f32a82980028b60a65505300041e43acaa0a6002998805d3314c0030b
  | 3 => 0xc288800083f825d8511000185d04bb0a2200030b609761444003e1b40aec2888009c35815d8511001387500bb0a22001f0e60176144400048fc32e62888000c1e865cc511000123b0cb98a22000307619731444000687312e62888000d0d625cc511000f83ec2b98a22001f45985731444003e0eb0ae62888000d15615cc511001183cc0b98a2200034698173144400041ec3ac62888000c1d7358c511000143f0eb18a22000307a1d63144400050ec3ac62888000c1d8758c511000103b0eb18a220003839c9631444000706b92c62888000e167158c511001383ee0b18a220027869c1631444004e0eb82c62888000e197058c511000183ac6b90a2200024be19721444000617432e4288800092d865c8511000185b0cb90a2200034398d721444000616b1ae42888000d0d635c8511000181ac6b90a22001f0bd85721444003e9330ae42888007c2d615c85110001a4ac2b90a2200230b981721444000695302e4288800083d87588511000183ae6b10a2200030b5c9621444000517c3ac42888000c2e87588511000145b0eb10a2200030b61d621444000416c3ac42888000e0e73588511000185ae6b10a220003835cd621444000606b9ac42888000e2671588511001385ee0b10a2200278a9c1621444004e16b82c42888000e2970588511000f46f0eb08a22002b0de1d611444003f0b39ac22888000c3573584511000fc2ae6b08a220003055cd611444003f13392c22888000c3572584511000fc4ae4b08a220003095c9611444004e1bb82c22888009e3270584511001386ae0b08a22001f8c5c1611444004c9dc32e02888008c3b865c05110013a34c6b80a2200030e58d701444004e8cb1ae02888000c19635c05110013a54c4b80a2200030e589701444004e94b12e02888000c29625c05110013876c2b80a2200274c985701444003e1cb0ae02888009d31615c05110001862c2b80a220003079d563cc4400060ebaac79888000c1d7654f311000185ceab1662200030b5d562cc44000706a9ac59888000c3675587311000186aeab0e62200038554d61cc4400060fbaac71888000c1c7558e311000185eeab1462200030b1d5628c44003e1bbaac31888007c3475586311000107b0dbaa62200020f618754c4400060fbaac69888000c1c7558d311000f2390ea9a6220003075d9534c44003d8a40aa69888000c2f755893110001858eab1262200038354d624c4400061bbaac29888000c34755853110001c2aa6b0a6220003079d5630c4400060ebaac61888002c9a7058c311000115b0d39062200032358e720c44000646b1ae418880008af87588311000115b0eb1062200030b9d5620c44000616baac41888002caa70588311000186ceab0862200030d5d5610c44000653392c21888000ca5725843110005964e0b0862200032658
  | 4 => 0x21000194ac4b886420003614c9710c8400064cb1ae01908000ca9625c03210001b1264b8064200028760c755844000516c10eab088007a3681d4d611000f46902a9ac22001e8da07525844003d1a40aa4b088000a3583dd5611000146b05baac2200268da1675584400054b418eab088000a95831d5611000154d043aac220002a9608755844001559400eab08800aa36871d5611000186d0e3aac22000385a0c75584400051ac18eab088000e15831d5611000142b063aac22000389a0875584400051ac10eab088000e25821d5611000144b043aac2200278ca00755844000718c00eab088000a36859cd611000146b0b39ac2200028de1573584400051a42ae6b088000a36851cd611000146b0a39ac220002a9a08735844000552c10e6b088002ab2801cd611000146d0fa9ac2200028d21f53584400051ac16a6b08800ea3780d4d611001d46b01a9ac2200028da1d53584400051a43aa6b088000e178354d6110001c2ce6a9ac220003855cd53584400051bc12a6b08800da378054d611001b46b00a9ac2200028da1672584400051ac2ce4b088000a37855c961100014690ab92c2200028da1472584400051ac28e4b088000a96831c9611000152b06392c22000aaca0072584400051b43ea4b088000a3487d49611000146b07a92c2200328de0352584400651ac06a4b088000a368754961100014690ea92c2200028de0d525844000713c12a4b088000e26725496110001c4ae4a92c22002e8de01525844005d1ac02a4b088000a3685cc9611000146b0b992c2200028da1632584400051ac2c64b088000a36854c9611000146b0a992c2200022da1c32584400045ac3864b088000a36850c9611000146b0a192c220003a14c832584400155940064b088000ab1800c9611001386ceab0ea22001f0d14576944400041fc1aed288800083f825da511000f86d02bb4a22002b0d60576944400041ec3ac72888000c1d7358e511000183d0eb1ca2200030761d63944400560fb82c7288800ac1d7058e511000183ac6b94a2200020f61d629444000616b92c52888000c2e8758a511000185b0eb14a2200030b5cd629444005617b82c5288800ac2d7058a511000f46f0eb0ca2200270de1d61944400061ab9ac32888000c3572586511001586ee0b0ca22002b0d5c161944400561bbaac2a888007c36515d8511000113b0d398a22000227e1d63144400044ec3ac62888002c9a7058c511000115b0d390a2200032358e721444000646b1ae428880008af87588511000115b0eb10a220003239cd621444000646b9ac42888002caa70588511000192ce6b08a220003255cd611444000653392c22888000ca5725845110005964e0b08a2200032658d701444000654b12e02888000cb1615c0511000107f06bb0a22000307a0d76144400060ec1ae
  | 5 => 0x3155cd611444000632b92c22888000c5a635c051100018b2c6b80a2200031a989701444000634b12e02888001c72615c051100018e2c2b80a2200020fa1e65504400041e43acaa088000c1f7558d4110001838eab1a82200030bdd56250440006163aac4a08800da1d839d5631001d43f06baac6200028760a7558c400050f40ceab188000c1f875d5631000143f04baac620002872057558c400050f42ee4b188000a1d85dc9631000143d0b392c620002876167258c400050f428e4b188000a1d851c9631000191ae4392c620002a5a047258c400054ac08e4b188002a9a801c9631000143d0bb8ac620002876177158c400060ebaee2b188000a1f855c563100014390ab8ac620003075d57158c400050f428e2b188000a1d851c5631000151d0438ac620002a36087158c400154d400e2b188000c1e7158f531001d83ae0b1ea6200030758d72d4c400760f43ac6a98800dc1d8758d531000143f02b1aa620003071c56354c4006e0fb82c6a988000c1d63dc9531001745b053aac4200328be09755884000516c16a6b108000a2f8254d621000145b073aac4200028ba06755884000617c3aeab108000a2f835d5621000145902baac4200028ba17735884000516c2ee6b108000a2e859cd621000145b0b39ac4200028ba14735884000516c28e6b108000c8d731cd621000154d0239ac420002a9604735884001555400e6b108000a2f87d4d621000145b0fa9ac4200028ba07535884007517c06a6b10800ea2d80d4d621000145f0ea9ac4200028b61d535884000707c1aa6b108000a2c8154d621001b45f00a9ac4200368b60153588400051742ee2b108000a2d85dc5621000185aebb8ac4200028be1571588400051642ae2b108000c2d755c5621000145d0a38ac4200028b614715884000547418e2b108000a8d831c562100055550038ac420003075cd63d48400060f43ac7a908000c1d8758f521000183ce2b1ea42003307dc163d48400660eb82c7a908000c2d7358b521000185ce2b16a4200330b5c162d48400060fb9ac6a908000c1e8758d521000183b0eb1aa420003071c5635484005e0fb82c6a90800bc1d7058d5210001c1ac7b92a4200330ba1d625484005e16c3ac4a908000c2f73589521000145f02b12a4200030b1c5625484005e17b82c4a908000c1e7558f321000183aeab1e64200030b9d562cc84000616baac59908000c1e7558e321000183aeab1c64200030b9d5628c84000616baac51908000939809d5321000183ceab1a6420003075d5634c840006173aac49908000c2d75589321000183ceab186420003075d5630c8400164d382c61908000c2e75588321000185aeab10642000b2a9c1620c84000546c32641908000c8d764c8321000116b0d38864200032558e710c84000652b14e21908000c95635c43
  | 6 => 0x41fc32e890ea001a648158921d400143b06326a6a80028b60864d49500060fb22e628aa000c1c645cc515400185ec8b90a2a80030b19172145500050ec1ee9b1aa000a1d831d3635400145b043a6c6a80024b60876d0d500041e432e3a1aa00083e86dc5435400145b05ba6c4a80028760c74d895000516c10e9b12a000c1d7350f625400123b063b684a80020f21971d095000516c16c6a12a00083e86dc5425400527100ba264a8003514c9710c950006a4992e0192a000c1f645cc6154001838c8b98c2a80030bd91721855000616322e430aa00083d839db415400107b053b682a80020fe1f63d05500041fc3ec5a0aa00083e869d9415400107b063b282a80020f60876505500041e43ec6a0aa00083c87d89415400107d0d3a082a80020fa1a748c5500041e432e918aa00083e869d1315400125b053a262a80020f219744c5500041f434e910aa00083c865d2215400107d0d3a242a80024760e74485500041e432e890aa00283d87d93605400507b0e326c0a80020f61e65d04500041f43ccaa08a009c3a645c051d0005930e0b1a872000b2a1c16250a4004e1c202ec28c8000939809d7419000107b0f32e83200020fe1d65d064006d0ec1ceab1c8000a2d829d5639001d43f06baac7200028760e7558a4005d16c14eab14800ca2f825d5629000183ee6a9ac5200028be096354a4000646bb2641948000d85325c43290001b1264b8065200020fe0d76946400041fc12ed28c800083d8758e519000183ae6b1ca3200020f61d629464000616b92c528c800083f835d8519000107f04bb0a3200270ea0176146400461cc02ec28c8000c1e865cc519000183b0cb98a32002307d8573146400460eb0ae628c800083d8758c519000183ae6b18a3200030ba19721464000616c32e428c8000c2d635c8519001185ec2b90a3200230b58572146400041ec3ac428c8000c1d73588519000185ae4b10a3200264ee19701464003e1dc32e028c8000c39635c05190001872c4b80a3200270ed8570146400461cb0ae028c80008af825d9319000107b0dbaa63200020f618754c6400458a40aa698c8000e1553585319000113f06bb243200020f61b75486400041ec30ea90c8008b24815492190001c4aa4b0a43200270ed9170145400060f3aac72188000c1d7558e431000145d0b21ac4200028b61643588400060f3aac72108000c1d7558e421000185ceab1484200030b5d562908400052ac18eab088000a65821d5611000146d0b21ac2200028d61643584400051b42c84b088000a3585909611001387480bb0a22000217e19731444000e2b30ae6288800085d8798c51100010bb0eb18a2200021be1972144400062731ae42888000c4d635c851100038ccc2b90a2200021b61e621444000626b9cc4288800086d87588511000189ae6b10a22
  | 7 => 0x1471591534c4032ad0fb8aa698802d16087154d31005a8c00e2a9a6212a1c8654f434c42562902a9e86988034554d71d0d3108d0e432a6a1a6211b148154d434c401a2aa7b8a86988028b60a64d49310060eb22e7a926201954815cf524c40145b05322a4988428721953d09310060ebb2a7a126210b148154f424c41f4390ca9a849883ec5205535093100caa40aeb992620185c865d5324c4032a902baa64988020f61f65d05310041ec38cba0a6201a1c8654f414c40362902a9e82988020fa1f65505310041f438caa0a6201a1c8654d414c40362902a9a82988030759573d083100646b9ac5a106200aa9821d1600c40153307a12c0188030b59172d4f210050ec1cc8a9e4200a1d8399543c840145b0da1aa5908061721d6354e2102c57c32e5a1c4200c2f655cb43884034a90ca9a631080307d9573991210060e32ae73224200c1e855ce644840183b0ab9cc8908030794573991210060e28ae7322420083e87d95644840107d0e32ac8908028760e64d4d2100c36432e5a9a4200c2d645cb53484032c902b96a6908028760e6454d210145c402eca1a420589e87d8d434840143b07326a4908028760e6454921086163b4c8a924200b0d839915248421a48e3322a49083f0b1d9645492107e9238ac8a924200a2d86d0d5248425858eda1aa49084b491c7435492108e163b286a924211d247150d52484032cd0fb8aa490802d160c7154921005b0c00e2a924210a2c8654b424842164902a9684908034954971d092107d16432a4a12420fb24815494248401a4aa5b8a849080659205758c92100c36432ea9924201964815d5324840107b0fb2e82908020f61c65d052100d16432a5a0a4201b248154b414840107d0fb2a82908020fa1c655052100d16432a4a0a4201b248154941484032c90ea94629080295219534c521004b243aa498a4203cc4764c9314840168b0a99262908030b59572d0c2100646b1ae5a184200a99831d1600840155305a1ac0108028760e6454f5000516c14c8a96a000a358199251d400143b073a2c7a800287e0d7458f500041fc32e3a1ea00083d86dc543d400145b053a2c5a80028be097458b5000516c1686b16a000a2f8250d62d400183ae6b1e85a80020fe1971d0b500060fb9ac6a16a00083d86dc542d400149b0c99065a80031558d710cb5000632b12e2196a000d45325c432d40018b2c6b8065a80031a589700cb50006a4992e0196a000a358199261d400107f06bb683a80020fe0976d07500041ec3ac7a0ea00083d8758b41d400107b07bb283a80020f60b76507500041f43ac6a0ea00083e8758941d400107b0d3a463a80020fe19748c7500041ec34e898ea00092d829d131d400107f0cba263a800695205634c7500041ec34e910ea00083f865d221d400107b0d3a243a80024760e74487500
  | 8 => 0x63a2c0288029aa08745805100534c10e8b00a201a72811d160144114750e3a2c0288030ea1c74580510070d418e8b00a200a39831d16014401c33063a2c0288028660c745805100715410e8b00a200a39821d16014401c53043a2c0288028a608745805103f19408e8b00a200e31811d160144014750939ac0288028e61273580510051dc22e6b00a200a38845cd60144014750839ac0288028e610735805100535410e6b00a200a69821cd60144034e50239ac0288028ea1f43580510051c43e86b00a200a3982d0d601442547703a1ac02884a8e60743580510051d43a86b00a200a388750d6014401c3706a1ac028803869cd43580510070cb9a86b00a200a3b8250d601442347702a1ac0288468e60543580510051d424e4b00a200a39849c9601440147708b92c0288028e21172580510051d420e4b00a200a39841c960144014b506392c0288029660c725805100d39408e4b00a200a3a87d0960144014710fa12c0288028e60f42580510851dc0e84b00a210a3981d0960144014750ea12c0288028e21d42580510051dc1a84b00a200e2b825096014401c54e4a12c0288038a5c9425805107d1dc0a84b00a20fa3981509601440147509992c0288028e61332580510051d42464b00a200a39848c9601440147508992c0288028e61132580510043d43864b00a200879870c9601440147508192c0288028e61032580510072499064b00a201a72810c960144014e302192c0288028760e6550f4100516c14caa168200a1d839d563d040143f06baac7a08020fe1970d4f410041ec36e0a9e8200a2d829d562d040145f04baac5a08028b60b5358b4100517c12a6b168200c1d7358f52d040107f0cb86a5a080307dcd6354b410041ec36e0a968200a8d864c832d040192ac6b8865a080329589710cb41006c2992e21968200c99635c032d0401952c4b8065a0803624c9700cb410051cc04cb3068200a1d83197435040145b0432e84a08028760f75d8d410050ec18ebb1a8200a2d821d7635040125b043b6a6a08020f21970d4d410041f436e0a9a8200a2d82dd7625040143b063aec4a08028b60875d89410060eb9aa7b12820091d831db52504010790cb86a4a08028b60b63549410041f436e0a928201934815d53250401b0a64b8864a0803624c9700c94100c1ec3ecbb0a820183d87197615040183ecab98c0a080307195731814100617b2ae43028200c2c655c8605040183ac8b9ea5988028b60a6454b310060ebb2a7a166200a2d8299542cc40183ecab9e85188030bd9572991310061632ae53226200c2e855ca644c40185b0ab94c8988030b94572991310061628ae5322620083e87d95644c40107d0e32ac8988028b60a64d4d3100516c14c8a9a6212c1c76991534c40161b05322a69884b451c66454d3108e0e3b2c8a9a6211d
  | 9 => 0x7458c510050ec14e8b18a200a1e809d1631440183f0eba2c62880287e097458c510050e402e8b18a200a1e84dc9631440143b09b92c62880287a127258c510050ec24e4b18a200a1e841c9631440143b08392c628803135c87258c5100d2b408e4b18a200a5a801c963144014b300392c62880287a137058c510050ec26e0b18a200c1d74dc1631440143f08b82c628802872117058c510060eba2e0b18a200a1e841c1631440143b08382c62880293a087058c5100526c10e0b18a201a56811c1631442583ae2b1e8628803079c163d0c510060eb1ae5a18a212c1e8758d431442383b0eb1a862884707dc56350c510050fc02c6a18a200c1c7058d431440183ac7b92862883e8b60a745885108517c12e8b10a200a2d82d0d621440145f04a1ac4288028b60e745885100517404e8b10a200c2f875d1621440145f06ba2c4288028b201745885100517426e6b10a200a2d84dcd621440145d0939ac4288028b612735885100517420e6b10a200a2d841cd621440189ae639ac42880699a04735885100535400e6b10a200a69801cd621440145f0fa1ac4288028b61f435885109517c0e86b10a212a2d81d0d621440145d01a1ac4288028be1d435885100516c3a86b10a200e0f8350d621442345f02a1ac4288468b60543588510051640286b10a200a2e84dc1621440145b09b82c4288030b5d3705885100517c22e0b10a200a2c845c1621440185ae8b82c4288028ba10705885100516c20e0b10a200a4e831c1621440149b06382c42880699a0470588510060eb9ac7a10a200c1e8758f421440183b0eb1e842884307dc563d08510860eb8ac7a10a200c1e7058f421440185ae6b1684288430b5c562d085100617382c5a10a200c1f7358d421440183d0eb1a84288030761d635085107e0fb8ac6a10a20fc1d7158d4214401838e0b1a84288038358f72508510861743ac4a10a20fc2d87589421440185ee6b12842883f0bdc5625085100517c02c4a10a200c2c70589421440183ce8b1e6428803075d163cc851006173a2c5990a200c2d7458b321440183ce8b1c6428803075d1638c851006173a2c5190a200c2d7458a321440126b033a26428803079d1634c8510060eba2c6990a200c2e74589321440185ae8b126428803079d1630c8510060eba2c6190a201c567158c321440185ce8b1064288030b5d1620c85100e3338ac4190a200a4d864c8321440189aec99064288031558d710c85100632b12e2190a200d45325c432144010f30d38064288031658e700c85100634b14e0190a200c59635c032144018d2c4b806428803524c9700c8510050ec18e8b00a200a2d821d1601441347501a1ac0288268e201435805104d1d40684b00a209a3880509601440147307ba2c0288028e60b745805103d1d424e8b00a200a5a831d160144014b3
  | 10 => 0x100100601b00300500000801101f01701e00900300100900700100a00000700100000200000000300c00700000000b00700500700200a00b00100000500100900200100300200200000a00100500600100000002100e00f00200900500600200600c00100400000100100000700000300c00000000100200b00000a00100300101400100201500100001000600300400300000500100b00a00000300400300000000000100a00600000200100201b00a00000101400000100800300200400200000400100f00000f00000200800c0020040000000040000010000010040010010010080090050050ec1ea8b1ca800a2d82d51629500125b043a2c1a98028760c745835300516c10e8b06a600a1d839d36054c0145b05a9ac5a18024b60875587430050ec18eab0e8600a2d821d561d0c0143b073aec2a180287e016350f520060e382c6a1ea400c1d63dc943d480183ac7b8a87a90024760c74583520050ec18e8b06a400a2d821d160d481947100a1ac1a90024b60a7418d5200617b1ae5a1aa40092f815cb4354801858c2b9686a904b0d18571d0d5200516c14e9b02a400a2d82d0f605480143b07322a62900287e056354f420060e38ac6a9e8400c1d63dc953d080183ac7b82a7a1003075cd63d4b420048ec18eab0e8400a1d831d561d080145b043aac3a10428d205535874200496c14ea31a8400c2f635cb535080125f00b96a6a10030b18172d4d420761c302e1a9a8400a2d829d7615080145b05a9ec2a10028760e6550c420060eb22e7a966400c1d655cf42cc80185ac8b96a7190030b59572d0e3200616b22e5a9a6400a1d83991534c80185acab9686990028760e6550d320060eb22e7a926400a2d82991524c80183acab9e84990028b60a655093200526c34ea9906400a4f865d5320c80151b0d3a26419002a3e19744c83200686baae89906400a71801d5610c801c8d0a992c21900391615325843200723baa64b086400e44754c9610c801d0d08992c219003a16113258432007433a264b086400e85744c9610c801563023a2c01900392a15325803200724c2a64b006400e4a754c9600c801c92ea992c019003a2a11325803200744c2264b006400e8b744c9600c801d10e8992c019007151c56354e5100e3238ac4a94a211a1d839d1639440145b053a2c72884a87e0d7458e510050ec1ce8b14a20fa2d829d1629442145f04ba2c52880307dcd4358a5100517c12c6a14a200c4d764c83294401a8a64b886528803524c9700ca510060f3a2c7298a200c1d7458e531440145d0929ac4288028b61253588510060f3a2c7290a200c1d7458e521440185ce8b14a4288030b5d162948510054cc18e8b00a200aa9821d160144014750929ac0288028e61253580510051d424a4b00a200a3984949601442343b073a2c62884a87e0d
  | 11 => 0x98cb0e1b40000009a8000a3a846b1c0002d6a426be98000000087a0000001c20000f4000a0800000012a0000000000000000000008540001160060000000044128d40ba4240003980000007ca70e1e00489ee2c20005149fc3507ac0000440000aa0007c000000086eac00002d42320002bc57e1568f63ba0000003e07b8a90b56b06b585660007c6000a1e00000080eb9452c3a64ae01c99e4482e64368987581282ec000a18ab82000002fa69a3c06f69fa00000065200082a00018c4a00000ae00000056c4109a000000014e8fe9cc00059e00012000051e8be0d64c606e0000000000002c6b6400000063a00000000000000052200000031625a000000a340000004764aa44679c90000000047cb3c52007c3541aeb1800017043262c00000006871cb3825c95a9c471e3fe00000078c30429400000047a000000468a5e308000000a9a37000068c0000000001a200010c1e238e0000c019c000b340000e06584b42ba608488038b2a1dca7a0006e28743ea75e2460000008f2680000000000000000b16386000000000a9c000828928000afe28e478abe83615a7a6392b8481000063e0000002d07243ee3f00000e62880000001324dc0000002065c800057868e00054a4d60007f6b2810e194b8ab3a00029e856a6400000e0005245649d800085200090a6888500000008160000000004d2aeeb3e00a2e401400100700500d00100d00601000600000400100000e00300000600900000700000300400101500d00300800700300400000300600200600000000600200002000d00800501200100000001800000101500100000100200000300700500200000100100000300100300500200b00000000100300302000000000b00000d00100000000400500301600100200100000000000500000100000200300000400a01400100102000000700100000900200300700000500001501000300000000300900300a00100000500000000100200000400200400000000002e00401a00100400100300100b00101300a00200400600100000200300700e00501800100700300300400000a00200d00c00100000000000100401200000001600f00101900200100200300100000300000000000500100700300200400400500100a00100500200100400d00000401a00b01100000000f00500700100200900000000f00400403e00000601000000100500000000100400400000001400000100c00500600300800400000000500900100800300000200400000000200100000300100200a00700100000000000001800000000200100000000101a00201e00000000200c00500000100e00100000100000000600300600100000000200100100200000300001100300300900001300a002001004000000000000000011000003006002001001000007006
  | 12 => 0x90c9ec4e28860000000003a47f45707189be000b120000002ea678b620000000001da0009700004ac000000a2e8e800000000000072e92a44000000000000002a00091242c8663dc75c00042a0a200000000084aadc8403f817a526b2e3066b6b6089c4860726dc8a60000005cc000ad47be8de2e25d4590462a86464a1255c4148626544da8d27882787042026120de0a89384ee7229e026228008e5ba000ba00180004c8000000b4c67e66c7fe97458e7c4056ae27e489a61816a0009dc80077458c7341de42622e00061a24c0000009584c0000000000000000b988aa0001be69438400072829a00000080c00027e23437e742aa8902ab00000001fe5b49e84665be9b654e00000043a1b80105e4404152b7cb76334a200006e658a43497a06c9d057662291c7022044ea70a6306bc8f876c0ee7480be5c0aea6ee8fc4b835816c9a2a0681c0000006ea0005ec000000000000000000a5c44401400025400036245800064269661c0000005fc51c70c76e0009d68e056e0005b21f09440dc08483a7fc4985b013021ca3e19a00040800087e0007ce00000084e07424e670a5876a3e28d80000000b89d4000000000000b900002a26b28e20000000000000002c44e0b9c2c848a22a9182b40000002e0146ad23d4786ac86baa8c9caaf40002e800000000078e3d2340b267665424a26281864f074423c00075058039e0ce5b861e760b6851a36466826818e0bcb8e0003960007a050c81a2fe0008c4000000000aa0000000180a6aa7400004a74e7b2142b460008067f06c65380003808fa0002862267cc00076832a00071a0000009c009627a7b6b5aaca6408801f40009ce58800000000031eb4e000000ba400000000007e0261980006ae0006b8000000a24000000000000872abca1c3be58696a17e5d645c6449bc00050259c000000b7a4f80009e2000000a140003de00000077a164b6c8ec6860620000e47d47805607ba2cc02c2c0000b74672908614000b1403c40e17491e6e80005e80d20007768780001265a0000876530028aec16000025609a000b809b46a0360baa0000000000008044840000000007e2ac20000f807a9667c20fc00053400021445088c00035600089e3ae1ec6467ae86a9f60004c40f60000000000000001a0000000000b720007c833e00090e000af654c49eade9204706c28dc1003668f06025e276205461694600000057a0000003903ce0001620005de0000009822d88ac3428b600000023a4425ae6507365182da070b400088821660808080401c06a6a826de978a4ab446aa0923e61e4b420463b20007107708a87d22a4b7820a5d800c60e584a9463c0002664fe906accb020000006241a61222b260432e1c89c83b60001240000000009b0b86000000000000000a9800000013a5980000001ac0000000
  | 13 => 0x580000004b2088b240000007546762aab48b3695c00028a0007aa31c28c0001f8b2c1ba00040a09818a06a6b0aa614c300a8e0009f40320000009e66907dea724ba8c0000b5c00037c0002202a840073a65641697c798a468ea8940004b011200011c7e000057ca001fcada4e60000005a66ca9483fa8b82fc3e4b10034b966e06981ca0004028ee2a66f24fa6e40000000008b0b92000188a6c4cc36c1509561c436e3b44e868a332a26a781842085da34c3460c67bc000634118ab69fe3c88a4a3200098e0b27a800000000000037a0000000008ce8682300d0052b5000000063800000000098a13c2440007b072c3d07dc0005060005562169c6000094a168f40000da00017c91411e33608200000026430c97eb52102a700ca0000000000007f8af078a7306d6016000318660992000438b08000a2865c000b6e8b26d86106cc1384a481275aaf811a904178b2289250400033c00000084c0009244f248ca4005e0e2b7e46a2be5ca86426e00024a540352a626f05160004c21ce00038a0000000000000000003b00002507d6afa92e5a85ee0000000000002ac35a0005aca3869e0000000a00760003d652a99499a3f264e9260004fc73ea4e984ba64ca45a9688306d20008c60002f08bcab42f664a8c26260a673859a2f8aa2aac5ea0005d000094a6c41b242e00074c0f06ac25260a88a8340000000000008ba0000006fc04c49c4d47ea00029c000218000a4c00095280a8d685800079400091a00071600000000000000025e0000000009f87d09aeae80000000000000004a81b69981a4a7c5329766c80ac13e1100005f85c60009f0314720b0499c41e1d82580ecb9e932af2418134a682383a29a634a46e0b60602120007ec45643e8208e679e8263287fa3ca0001e64f603000035e3440003ac19e82e9540200009ea2922284943026ce6d4a6e39c00000030ea363f46820001a89a404e000000000260790a7e0005fa0000000003ec67400000000085a00085e0004d8a6000000000000073c000a841f60000000001bc42037841c0008e496064c0004900fa792176422a56936a8080220c0005946c052e23e10a000a10000000a929ac500000b54b8200000000000092cb8c21aa5a8962ee5521905288cc00065a596000000a2c2768185c27261d06a8ae04524300648c8664000000000000b000000005920009ba000aae550000a040ea824000b1a0004727a42dc0000000001080b03888222905c40000000002700000000000000003729860004b69d2ba20007b4990684000ace8b44742b862e2ca5fe2ce91638c5f449aae63fc6f43d809c0000000000003940421e83c453c65e15c33801a7724be74605c620ae4870106148aaa324a765aa97294c01e0c47e800055424234e00000093e62a4bc7640004ec7e6b4a9c200009e15800
  | 14 => 0x7126fe5360002f4012890a0a00000000000000056a60027269c74a0000009e455e2368487d81aa9f257491011400000000044a77e0000000000000000001ea0002244540000028420005f21f286081eb20000428ba83121543e893c0001d45b6a504a68ae44e000bae46c03e0009340228321720000c2000000000a485465f000066e00094250ab6a5dc3c22b0aa43bc16eb3244c14a53e0000cc7da08c8a2a9e60c1fa3749b8930a300a454432000000050e6360002a034800082c7ee8d027427c94054894e0008140000008ca0b41ee5f600000095000000005a39a000000000000330382000a3c000bac66a72a6621042480009645ce87c5726ec83832622c000b705084806a4066b66a0c5d2000706000a8a3c60006f80000000000000005bc7406fa41a0001400000000000004607f228473296e43c00000077ca1a4d0700ab20c80007823f6b9a03a0000000003a0000000368000000000a22182000ac40008a0000a881b000055867a4ce482000b1e12e15e0002d26b488e0000f247e29631a510a2a0d43102b62980000004e46d00000000000fe53aa6649677828208a086b0c7a2240b0a5a42220000000000000e800079a95e692b305a2000000000000a0200086c5827960000003a820eaba8886062f20d800000021000014400000000000000019200000067c0001c632c00000000000000055a37600098836a7840007080780000005e60000004de00035c0001d6050492000756000000ad802400000051200021e0000008440000000008da00040c0000000001960000002ae00000000066648e40616800093a33a00000000000056288400032299602e30a632ad66da000648b8809013600083c000a52b5e96c3cc3da26c1cca0e0005e026a1d2ac66a2752000afc71445e0003aa962a549aa000ad00004f49b29de85ca965682de83e0000000003b812c036000000000000000a440000009229da
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x1a813260032584400040b64b835d8511000101d93e0976144400060360e825d8511000180e8360976144400060360d825d8511000140d92a19731444000605985865cc511000180d86989731444000603e19625cc511000180d86589731444000701985625cc511000181786585731444000605619615cc5110001c0662585731444000701589615cc511000140d92a1d6314440006069c18758c511000180d879c9631444000603e1d7258c511000180d875c96314440007029c17258c511000181b875c163144400060661d7058c5110001c0a725c16314440007025c97058c511000140d93a19721444000609985865c8511000180d8698d721444000603e19635c8511000180d8658d721444000701985635c8511000182786585721444000609619615c85110001c066358572144400070158d615c8511000140d93a1d62144400060a9c187588511000180d879cd621444000603e1d73588511000180d875cd6214440007029c173588511000182b875c162144400060a61d705885110001c0a735c16214440007025cd70588511000140d921d5638c440005066407558e311000102d981d5628c4400050a6407558a3110001814815d9534c4400058124553589311000f4149754d614c440004076607558e2110001419901d563884400050364c7558a2110001429901d5628844000609205765492110001a048158d524844003d0925d52585211000140d92191731463000505644645cc518c00102d98191721463000509644645c8518c00102d98101729953000509644405ca654c00180c7660a6550d30006421c182995434c001818805d943d493000407660645cc514c001818805d9431453000503259435c8514c0015089050d721453004d06259435c0514c00101d98191731462000505644645cc518800140d93191721462000509644645c8518800101d98101739952000505644405ce654800180c7660e6550920006421c18399542480018287061b53509200040b660645c85148001828805d9421452000603219735085148001908805cd421452004d0a259425c0514800518897611324c120014a2259844c930480011309760353505100044c25d80d4941440019107560c7050510006481d5821c141440011309760743541100044c25d81d0950440019107460c7154110006481d1821c5504400113297a1d41541100544ca588750550440131309621d41541100044c64c8750550440011319221d41541100044c26373505504400113098dc941541100044c25d848c550440011309761131541100044c25d8488550440011309761121541100044c261755063044001130985d5414c11000d14259754c5304400529096611314c1100044c261755062044001130985d5414811000d182597548520440052a0966112148110
  | 1 => 0x2005036487158d53d0801419901c56354f420050364c605cb53508014259118172d4d4200590640754c9610c801a0585611325843200682615844c9600c801681911d1325803200483648805d16314401849726007258c5100506241745c1631440140d921c16350c51005056447058d431440120d932017458851006125cd801cd621440102d972014358851004896448050d6214401428905d17058851004076607058d4214401415911c163508510050364c705894214401425911c16250851005056467458d3214401425919d1624c85100511659325c43214401449964c9700c85100684a05831d16014401a0983a08745805100682a0d821d16014401a0983608745805100688a05821d16014401a128360474580510068460d811d16014401a2282604745805100688609811d160144012299221f435805104c8c64487d0d60144012299221d435805104c8c6448750d6014401218985cd43580510060621d7350d60144012199321f425805104c8c64487d0960144012199321d425805104c8c644875096014401228985c942580510060a21d72509601440123191a1132580510061261d320c96014401a4132604325805100521659325c432d0401489964c9700cb410040b648865c3535040101d9321970d49410040b660515ca644c401429901457299131006031d982991534c4019047160a6454d31006052057654f424c40101d98145739912100506640515ce644840180c7660e6454921006411c58399152484018247161b435492100c5125d854c9314840324496615324c52100511659325c432d4001449964c9700cb500040b64b835db41d400101d93e0976d07500040b648865c7435400101d9321971d09500040b64887d8d415400101d9321f62505500040be498758e519000101f9361d629464000483648815d56310001885726047258c4000505245755c5631000140d921c56354c40005066407158d531000120d932057558840006215cd811cd621000102d9720553588400048a6408154d6210001424915d57158840004076607158d5210001419901c563548400050364c715895210001429901c56254840005066427558d3210001429909d5624c84000521659325c43210001489964c9700c84000684a01831d56110001a0583a08755844000681a0d821d56110001a0583608755844000688a01821d56110001a128360075584400068460d801d56110001a2282600755844000688609801d561100012259221f535844003c8c64087d4d61100012259221d535844003c8c6408754d6110001214985cd53584400060521d7354d61100012159321f525844003c8c64087d4961100012159321d525844003c8c640875496110001224985c952584400060921d72549611000123190a1532584400062161d320c96110
  | 2 => 0xda00000000600001f0d6001980000b22238000b70000000c92680000004f80000007200092d5430010e002734c6a0000001680000250820010a3800000019c003130081260002000ac964ba45180036060440d1b801468a21000b27200070009d170000000000017c980002c000500001420000000000000000000013054246a000e80083001f400004dae4560172a094a00042bdb60066868e2000a1e0a6000485da2bd0000000000032c000000001625f0015d980000001660022800004c002ec00000000000000000000000039c00004c8014c00000003c000000000000000140b500001160c0000124000000000885f949d4232d8007c30010019c0000000c4b6520000000618580054678b55c3832205c6ed2d1200000000000000001fda8c00000170000e800003600000005500000004600000000000000000000000008500000dcde00001ac43540ecf27b07801d0b03f00000000000000001e80000000004c7295000004e0000000005125b10ea0000000000000000005e003b178c1002a400901f8f080d9160000080003411a00070005200001cc00006d000000000278000012aad344a0391cdedd568000ce26e384000031801449c2e000007a5d000a00000000e81f00398000a00001ae00000d00000000011e000000000003b80000c6193098ec534890e00075b60000000000000000000c2662e8000058342a800001500000000000000890006c5e000037c0000000014e4f0000000000804508ca0000000000000000d232ba558c83b06400280100200030081001000080200000041201040140601000180e06000040003000000800000040003000000003008000403008100203010080200040040002008080200000040000028040a0d0080000060180c0000000140202005036487058d43d4801415911c16350f520050364c615cb43548014299018572d0d5
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x744800091585445cd962aa011406007001a680004e84600541918038488800e4c50f58613105a04020002c2083c94fa9320c0b071c400044104b3870001204d1120ba2e0b18a20090268c905d170588510050134443ae6a1ac028802809a321d725096014401082d48e2c14c8a9a6200a406807160a6454d3100500b4440aeca9e8498802811a02057654f424c401082d48e2c1cc8a924200a406807160e645492100500b4638b0da1aa490802821a01c586d0d5248401202d1122baae2b18800090168c915d5715884000500b4443ae6a9ac220002805a321d725496110001402d1102bb2a69888000a04680815d9534c44000440b5048aa6b126220002601a0245535893110001402d1902bb2a49088000a08680815d9524844000440b5240ac6a924220002a01a0205635492110001084d48e0c14caa1a6000a406847060a6550d3000501344402eca1ea498002811a12017650f524c001404d1100bb28628a6000a04684805d943145300042135048286b90a298002501a1241435c8514c001084d48e0c1ccaa124000a406847060e6550920005013463830da9a8490002821a11c186d4d4248001404d1900bb28428a4000a08684805d9421452000421352402e6a10a290002901a1201735085148001090d112ec06a6a0a200084468c976035250510004243444bb03a1aa088002111a325d81d095044001090d1131b9a82a82200084468c98dc94154110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x1
  | 3 => 0x3
  | 4 => 0x4
  | 5 => 0x5
  | 6 => 0x6
  | 7 => 0x10a
  | 8 => 0x130a
  | 9 => 0x2c9
  | 10 => 0x14c9
  | 11 => 0xd49
  | 12 => 0x1a09
  | 13 => 0xec9
  | 14 => 0x1a49
  | 15 => 0xd0a
  | 16 => 0x188a
  | 17 => 0xe8a
  | 18 => 0x18ca
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 76
  | 6 => 2516
  | 5 => 5436
  | 4 => 1496
  | 3 => 238
  | 2 => 46
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (i*15) 6
  | 7 => packedAt gbK7 (i*26) 17
  | 6 => packedAt gbK6 (i*37) 28
  | 5 => packedAt gbK5 (i*48) 39
  | 4 => packedAt gbK4 (i*59) 50
  | 3 => packedAt gbK3 (i*70) 61
  | 2 => packedAt gbK2 (i*81) 72
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 8 => gbHint (packedAt gbK8 (i*15+6) 9)
  | 7 => gbHint (packedAt gbK7 (i*26+17) 9)
  | 6 => gbHint (packedAt gbK6 (i*37+28) 9)
  | 5 => gbHint (packedAt gbK5 (i*48+39) 9)
  | 4 => gbHint (packedAt gbK4 (i*59+50) 9)
  | 3 => gbHint (packedAt gbK3 (i*70+61) 9)
  | 2 => gbHint (packedAt gbK2 (i*81+72) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (16+((h/1+packedAt gbK8 (15+(h % 1)*1) 1) % 2)*1) 1
  | 7 => packedAt gbK7 (2151+((h/25+packedAt gbK7 (1976+(h % 25)*7) 7) % 92)*8) 8
  | 6 => packedAt gbK6 (103986+((h/838+packedAt gbK6 (93092+(h % 838)*13) 13) % 4862)*13) 13
  | 5 => packedAt gbK5 (286296+((h/1812+packedAt gbK5 (260928+(h % 1812)*14) 14) % 10505)*14) 14
  | 4 => packedAt gbK4 (94240+((h/498+packedAt gbK4 (88264+(h % 498)*12) 12) % 2172)*12) 12
  | 3 => packedAt gbK3 (17371+((h/79+packedAt gbK3 (16660+(h % 79)*9) 9) % 502)*9) 9
  | 2 => packedAt gbK2 (3816+((h/15+packedAt gbK2 (3726+(h % 15)*6) 6) % 56)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xc3f0fe00c187e1fff1c1c3f87f14c6e04f0cf
  | 1 => 0xfc3f0fff01f87e1c0e01fc3f872b0939b4333
  | 2 => 0xf003ff007fe007fe00ffe003ff8cc31c638c3c
  | 3 => 0xfffc00007ffff80000fffffc000f03e07c0fc0
  | 4 => 0x7fffffffff000000000ffc007ff000
  | 5 => 0xffffffff8000000000000000000fffff800000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x4050122000008025004041082400426001045
  | 1 => 0x401041100882208220088110201000894112
  | 2 => 0x9002aa0425200554044940026504c118228428
  | 3 => 0x2aa800084a55500008929328000b02c0540a80
  | 4 => 0x822088117f9e67992e00c188312ff8007fe000
  | 5 => 0xcf33cc9e0304411030030230464fefff000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xfeeefeecfeeafee8feeefeecfeeafee8feeefeecfeeafee8feeefeecfeeafee8feeefeecfeeafee8feeefeecfeeafee8feeefeecfeeafee8feeefeecfeeafee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_14502
namespace PEqualNP.Outside.L_meta_14502
open PEqualNP.Outside.L_meta_14502.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 4 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 6 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 1 := bs0_4_0
theorem alls0 : ∀ k ≤ 4, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 6 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 1 := bs1_4_0
theorem alls1 : ∀ k ≤ 4, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 1 := bs2_4_0
theorem alls2 : ∀ k ≤ 4, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1 := bs3_4_0
theorem alls3 : ∀ k ≤ 4, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1 := bs4_4_0
theorem alls4 : ∀ k ≤ 4, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 1 := bs5_4_0
theorem alls5 : ∀ k ≤ 4, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_32 : Interval gbAtlas 2 32 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 46 := (concat bgb_2_0 bgb_2_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_64 : Interval gbAtlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_96 : Interval gbAtlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_128 : Interval gbAtlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_160 : Interval gbAtlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_192 : Interval gbAtlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_224 : Interval gbAtlas 3 224 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 238 := (concat (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 bgb_3_96)) (concat (concat bgb_3_128 bgb_3_160) (concat bgb_3_192 bgb_3_224)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_128 : Interval gbAtlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_160 : Interval gbAtlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_192 : Interval gbAtlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_224 : Interval gbAtlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_256 : Interval gbAtlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_288 : Interval gbAtlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_320 : Interval gbAtlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_352 : Interval gbAtlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_384 : Interval gbAtlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_416 : Interval gbAtlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_448 : Interval gbAtlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_480 : Interval gbAtlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_512 : Interval gbAtlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_544 : Interval gbAtlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_576 : Interval gbAtlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_608 : Interval gbAtlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_640 : Interval gbAtlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_672 : Interval gbAtlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_704 : Interval gbAtlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_736 : Interval gbAtlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_768 : Interval gbAtlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_800 : Interval gbAtlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_832 : Interval gbAtlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_864 : Interval gbAtlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_896 : Interval gbAtlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_928 : Interval gbAtlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_960 : Interval gbAtlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_992 : Interval gbAtlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1024 : Interval gbAtlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1056 : Interval gbAtlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1088 : Interval gbAtlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1120 : Interval gbAtlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1152 : Interval gbAtlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1184 : Interval gbAtlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1216 : Interval gbAtlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1248 : Interval gbAtlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1280 : Interval gbAtlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1312 : Interval gbAtlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1344 : Interval gbAtlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1376 : Interval gbAtlas 4 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1408 : Interval gbAtlas 4 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1440 : Interval gbAtlas 4 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1472 : Interval gbAtlas 4 1472 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 1496 := (concat (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128))) (concat (concat bgb_4_160 (concat bgb_4_192 bgb_4_224)) (concat bgb_4_256 (concat bgb_4_288 bgb_4_320)))) (concat (concat (concat bgb_4_352 (concat bgb_4_384 bgb_4_416)) (concat bgb_4_448 (concat bgb_4_480 bgb_4_512))) (concat (concat bgb_4_544 (concat bgb_4_576 bgb_4_608)) (concat bgb_4_640 (concat bgb_4_672 bgb_4_704))))) (concat (concat (concat (concat bgb_4_736 (concat bgb_4_768 bgb_4_800)) (concat bgb_4_832 (concat bgb_4_864 bgb_4_896))) (concat (concat bgb_4_928 (concat bgb_4_960 bgb_4_992)) (concat bgb_4_1024 (concat bgb_4_1056 bgb_4_1088)))) (concat (concat (concat bgb_4_1120 (concat bgb_4_1152 bgb_4_1184)) (concat bgb_4_1216 (concat bgb_4_1248 bgb_4_1280))) (concat (concat bgb_4_1312 (concat bgb_4_1344 bgb_4_1376)) (concat bgb_4_1408 (concat bgb_4_1440 bgb_4_1472))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_0 : Interval gbAtlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_32 : Interval gbAtlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_64 : Interval gbAtlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_96 : Interval gbAtlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_128 : Interval gbAtlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_160 : Interval gbAtlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_192 : Interval gbAtlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_224 : Interval gbAtlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_256 : Interval gbAtlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_288 : Interval gbAtlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_320 : Interval gbAtlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_352 : Interval gbAtlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_384 : Interval gbAtlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_416 : Interval gbAtlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_448 : Interval gbAtlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_480 : Interval gbAtlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_512 : Interval gbAtlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_544 : Interval gbAtlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_576 : Interval gbAtlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_608 : Interval gbAtlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_640 : Interval gbAtlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_672 : Interval gbAtlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_704 : Interval gbAtlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_736 : Interval gbAtlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_768 : Interval gbAtlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_800 : Interval gbAtlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_832 : Interval gbAtlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_864 : Interval gbAtlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_896 : Interval gbAtlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_928 : Interval gbAtlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_960 : Interval gbAtlas 5 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_992 : Interval gbAtlas 5 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1024 : Interval gbAtlas 5 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1056 : Interval gbAtlas 5 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1088 : Interval gbAtlas 5 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1120 : Interval gbAtlas 5 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1152 : Interval gbAtlas 5 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1184 : Interval gbAtlas 5 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1216 : Interval gbAtlas 5 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1248 : Interval gbAtlas 5 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1280 : Interval gbAtlas 5 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1312 : Interval gbAtlas 5 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1344 : Interval gbAtlas 5 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1376 : Interval gbAtlas 5 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1408 : Interval gbAtlas 5 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1440 : Interval gbAtlas 5 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1472 : Interval gbAtlas 5 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1504 : Interval gbAtlas 5 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1536 : Interval gbAtlas 5 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1568 : Interval gbAtlas 5 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1600 : Interval gbAtlas 5 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1632 : Interval gbAtlas 5 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1664 : Interval gbAtlas 5 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1696 : Interval gbAtlas 5 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1728 : Interval gbAtlas 5 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1760 : Interval gbAtlas 5 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1792 : Interval gbAtlas 5 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1824 : Interval gbAtlas 5 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1856 : Interval gbAtlas 5 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1888 : Interval gbAtlas 5 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1920 : Interval gbAtlas 5 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1952 : Interval gbAtlas 5 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1984 : Interval gbAtlas 5 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2016 : Interval gbAtlas 5 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2048 : Interval gbAtlas 5 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2080 : Interval gbAtlas 5 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2112 : Interval gbAtlas 5 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2144 : Interval gbAtlas 5 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2176 : Interval gbAtlas 5 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2208 : Interval gbAtlas 5 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2240 : Interval gbAtlas 5 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2272 : Interval gbAtlas 5 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2304 : Interval gbAtlas 5 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2336 : Interval gbAtlas 5 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2368 : Interval gbAtlas 5 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2400 : Interval gbAtlas 5 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2432 : Interval gbAtlas 5 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2464 : Interval gbAtlas 5 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2496 : Interval gbAtlas 5 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2528 : Interval gbAtlas 5 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2560 : Interval gbAtlas 5 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2592 : Interval gbAtlas 5 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2624 : Interval gbAtlas 5 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2656 : Interval gbAtlas 5 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2688 : Interval gbAtlas 5 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2720 : Interval gbAtlas 5 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2752 : Interval gbAtlas 5 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2784 : Interval gbAtlas 5 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2816 : Interval gbAtlas 5 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2848 : Interval gbAtlas 5 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2880 : Interval gbAtlas 5 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2912 : Interval gbAtlas 5 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2944 : Interval gbAtlas 5 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2976 : Interval gbAtlas 5 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3008 : Interval gbAtlas 5 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3040 : Interval gbAtlas 5 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3072 : Interval gbAtlas 5 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3104 : Interval gbAtlas 5 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3136 : Interval gbAtlas 5 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3168 : Interval gbAtlas 5 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3200 : Interval gbAtlas 5 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3232 : Interval gbAtlas 5 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3264 : Interval gbAtlas 5 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3296 : Interval gbAtlas 5 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3328 : Interval gbAtlas 5 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3360 : Interval gbAtlas 5 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3392 : Interval gbAtlas 5 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3424 : Interval gbAtlas 5 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3456 : Interval gbAtlas 5 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3488 : Interval gbAtlas 5 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3520 : Interval gbAtlas 5 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3552 : Interval gbAtlas 5 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3584 : Interval gbAtlas 5 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3616 : Interval gbAtlas 5 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3648 : Interval gbAtlas 5 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3680 : Interval gbAtlas 5 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3712 : Interval gbAtlas 5 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3744 : Interval gbAtlas 5 3744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3776 : Interval gbAtlas 5 3776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3808 : Interval gbAtlas 5 3808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3840 : Interval gbAtlas 5 3840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3872 : Interval gbAtlas 5 3872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3904 : Interval gbAtlas 5 3904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3936 : Interval gbAtlas 5 3936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3968 : Interval gbAtlas 5 3968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4000 : Interval gbAtlas 5 4000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4032 : Interval gbAtlas 5 4032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4064 : Interval gbAtlas 5 4064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4096 : Interval gbAtlas 5 4096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4128 : Interval gbAtlas 5 4128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4160 : Interval gbAtlas 5 4160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4192 : Interval gbAtlas 5 4192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4224 : Interval gbAtlas 5 4224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4256 : Interval gbAtlas 5 4256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4288 : Interval gbAtlas 5 4288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4320 : Interval gbAtlas 5 4320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4352 : Interval gbAtlas 5 4352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4384 : Interval gbAtlas 5 4384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4416 : Interval gbAtlas 5 4416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4448 : Interval gbAtlas 5 4448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4480 : Interval gbAtlas 5 4480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4512 : Interval gbAtlas 5 4512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4544 : Interval gbAtlas 5 4544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4576 : Interval gbAtlas 5 4576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4608 : Interval gbAtlas 5 4608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4640 : Interval gbAtlas 5 4640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4672 : Interval gbAtlas 5 4672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4704 : Interval gbAtlas 5 4704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4736 : Interval gbAtlas 5 4736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4768 : Interval gbAtlas 5 4768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4800 : Interval gbAtlas 5 4800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4832 : Interval gbAtlas 5 4832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4864 : Interval gbAtlas 5 4864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4896 : Interval gbAtlas 5 4896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4928 : Interval gbAtlas 5 4928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4960 : Interval gbAtlas 5 4960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4992 : Interval gbAtlas 5 4992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5024 : Interval gbAtlas 5 5024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5056 : Interval gbAtlas 5 5056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5088 : Interval gbAtlas 5 5088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5120 : Interval gbAtlas 5 5120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5152 : Interval gbAtlas 5 5152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5184 : Interval gbAtlas 5 5184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5216 : Interval gbAtlas 5 5216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5248 : Interval gbAtlas 5 5248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5280 : Interval gbAtlas 5 5280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5312 : Interval gbAtlas 5 5312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5344 : Interval gbAtlas 5 5344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5376 : Interval gbAtlas 5 5376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5408 : Interval gbAtlas 5 5408 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 5436 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)) (concat bgb_5_576 (concat bgb_5_608 bgb_5_640))))) (concat (concat (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 (concat bgb_5_768 bgb_5_800))) (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 (concat bgb_5_928 bgb_5_960)))) (concat (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120))) (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312)))))) (concat (concat (concat (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472))) (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632)))) (concat (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 (concat bgb_5_1760 bgb_5_1792))) (concat (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888)) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984))))) (concat (concat (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144))) (concat (concat bgb_5_2176 (concat bgb_5_2208 bgb_5_2240)) (concat bgb_5_2272 (concat bgb_5_2304 bgb_5_2336)))) (concat (concat (concat bgb_5_2368 bgb_5_2400) (concat bgb_5_2432 (concat bgb_5_2464 bgb_5_2496))) (concat (concat bgb_5_2528 (concat bgb_5_2560 bgb_5_2592)) (concat bgb_5_2624 (concat bgb_5_2656 bgb_5_2688))))))) (concat (concat (concat (concat (concat (concat bgb_5_2720 bgb_5_2752) (concat bgb_5_2784 (concat bgb_5_2816 bgb_5_2848))) (concat (concat bgb_5_2880 bgb_5_2912) (concat bgb_5_2944 (concat bgb_5_2976 bgb_5_3008)))) (concat (concat (concat bgb_5_3040 bgb_5_3072) (concat bgb_5_3104 (concat bgb_5_3136 bgb_5_3168))) (concat (concat bgb_5_3200 (concat bgb_5_3232 bgb_5_3264)) (concat bgb_5_3296 (concat bgb_5_3328 bgb_5_3360))))) (concat (concat (concat (concat bgb_5_3392 bgb_5_3424) (concat bgb_5_3456 (concat bgb_5_3488 bgb_5_3520))) (concat (concat bgb_5_3552 bgb_5_3584) (concat bgb_5_3616 (concat bgb_5_3648 bgb_5_3680)))) (concat (concat (concat bgb_5_3712 bgb_5_3744) (concat bgb_5_3776 (concat bgb_5_3808 bgb_5_3840))) (concat (concat bgb_5_3872 (concat bgb_5_3904 bgb_5_3936)) (concat bgb_5_3968 (concat bgb_5_4000 bgb_5_4032)))))) (concat (concat (concat (concat (concat bgb_5_4064 bgb_5_4096) (concat bgb_5_4128 (concat bgb_5_4160 bgb_5_4192))) (concat (concat bgb_5_4224 bgb_5_4256) (concat bgb_5_4288 (concat bgb_5_4320 bgb_5_4352)))) (concat (concat (concat bgb_5_4384 bgb_5_4416) (concat bgb_5_4448 (concat bgb_5_4480 bgb_5_4512))) (concat (concat bgb_5_4544 (concat bgb_5_4576 bgb_5_4608)) (concat bgb_5_4640 (concat bgb_5_4672 bgb_5_4704))))) (concat (concat (concat (concat bgb_5_4736 bgb_5_4768) (concat bgb_5_4800 (concat bgb_5_4832 bgb_5_4864))) (concat (concat bgb_5_4896 (concat bgb_5_4928 bgb_5_4960)) (concat bgb_5_4992 (concat bgb_5_5024 bgb_5_5056)))) (concat (concat (concat bgb_5_5088 bgb_5_5120) (concat bgb_5_5152 (concat bgb_5_5184 bgb_5_5216))) (concat (concat bgb_5_5248 (concat bgb_5_5280 bgb_5_5312)) (concat bgb_5_5344 (concat bgb_5_5376 bgb_5_5408))))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_0 : Interval gbAtlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_32 : Interval gbAtlas 6 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_64 : Interval gbAtlas 6 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_96 : Interval gbAtlas 6 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_128 : Interval gbAtlas 6 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_160 : Interval gbAtlas 6 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_192 : Interval gbAtlas 6 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_224 : Interval gbAtlas 6 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_256 : Interval gbAtlas 6 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_288 : Interval gbAtlas 6 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_320 : Interval gbAtlas 6 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_352 : Interval gbAtlas 6 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_384 : Interval gbAtlas 6 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_416 : Interval gbAtlas 6 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_448 : Interval gbAtlas 6 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_480 : Interval gbAtlas 6 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_512 : Interval gbAtlas 6 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_544 : Interval gbAtlas 6 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_576 : Interval gbAtlas 6 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_608 : Interval gbAtlas 6 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_640 : Interval gbAtlas 6 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_672 : Interval gbAtlas 6 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_704 : Interval gbAtlas 6 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_736 : Interval gbAtlas 6 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_768 : Interval gbAtlas 6 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_800 : Interval gbAtlas 6 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_832 : Interval gbAtlas 6 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_864 : Interval gbAtlas 6 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_896 : Interval gbAtlas 6 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_928 : Interval gbAtlas 6 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_960 : Interval gbAtlas 6 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_992 : Interval gbAtlas 6 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1024 : Interval gbAtlas 6 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1056 : Interval gbAtlas 6 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1088 : Interval gbAtlas 6 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1120 : Interval gbAtlas 6 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1152 : Interval gbAtlas 6 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1184 : Interval gbAtlas 6 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1216 : Interval gbAtlas 6 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1248 : Interval gbAtlas 6 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1280 : Interval gbAtlas 6 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1312 : Interval gbAtlas 6 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1344 : Interval gbAtlas 6 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1376 : Interval gbAtlas 6 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1408 : Interval gbAtlas 6 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1440 : Interval gbAtlas 6 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1472 : Interval gbAtlas 6 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1504 : Interval gbAtlas 6 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1536 : Interval gbAtlas 6 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1568 : Interval gbAtlas 6 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1600 : Interval gbAtlas 6 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1632 : Interval gbAtlas 6 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1664 : Interval gbAtlas 6 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1696 : Interval gbAtlas 6 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1728 : Interval gbAtlas 6 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1760 : Interval gbAtlas 6 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1792 : Interval gbAtlas 6 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1824 : Interval gbAtlas 6 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1856 : Interval gbAtlas 6 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1888 : Interval gbAtlas 6 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1920 : Interval gbAtlas 6 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1952 : Interval gbAtlas 6 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1984 : Interval gbAtlas 6 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2016 : Interval gbAtlas 6 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2048 : Interval gbAtlas 6 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2080 : Interval gbAtlas 6 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2112 : Interval gbAtlas 6 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2144 : Interval gbAtlas 6 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2176 : Interval gbAtlas 6 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2208 : Interval gbAtlas 6 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2240 : Interval gbAtlas 6 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2272 : Interval gbAtlas 6 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2304 : Interval gbAtlas 6 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2336 : Interval gbAtlas 6 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2368 : Interval gbAtlas 6 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2400 : Interval gbAtlas 6 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2432 : Interval gbAtlas 6 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2464 : Interval gbAtlas 6 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2496 : Interval gbAtlas 6 2496 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2516 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 (concat bgb_6_384 bgb_6_416))) (concat (concat bgb_6_448 bgb_6_480) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))))) (concat (concat (concat (concat bgb_6_608 bgb_6_640) (concat bgb_6_672 (concat bgb_6_704 bgb_6_736))) (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)))) (concat (concat (concat bgb_6_928 bgb_6_960) (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056))) (concat (concat bgb_6_1088 bgb_6_1120) (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)))))) (concat (concat (concat (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376))) (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 (concat bgb_6_1504 bgb_6_1536)))) (concat (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 (concat bgb_6_1664 bgb_6_1696))) (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856))))) (concat (concat (concat (concat bgb_6_1888 bgb_6_1920) (concat bgb_6_1952 (concat bgb_6_1984 bgb_6_2016))) (concat (concat bgb_6_2048 bgb_6_2080) (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176)))) (concat (concat (concat bgb_6_2208 bgb_6_2240) (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336))) (concat (concat bgb_6_2368 bgb_6_2400) (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 76 := (concat bgb_7_0 (concat bgb_7_32 bgb_7_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 1 := bgb_8_0
theorem allgb : ∀ k ≤ 8, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact allgb_2 i (by omega) hi
  · exact allgb_3 i (by omega) hi
  · exact allgb_4 i (by omega) hi
  · exact allgb_5 i (by omega) hi
  · exact allgb_6 i (by omega) hi
  · exact allgb_7 i (by omega) hi
  · exact allgb_8 i (by omega) hi
def Complete (g : Atlas) := ∀ k ≤ top g, ∀ i < count g k, checkRow g k i = true
theorem frozen {g : Atlas} {p n} (ready : Ready g p n) (complete : Complete g)
    (atRoot : vals g (top g) 0 = roots g) (row : 0 < count g (top g))
    (xs : List (Sig × Row × Row)) (pr : proper (target g))
    (test : checkEssential (target g) (roots g) xs=true) (names : xs.map Prod.fst=roots g) :
    Lower true (roots g) (target g) (top g+1) := by
  apply lower_impossible pr (essential_plain test).1 (essential_plain test).2
  · intro a ha
    exact essential_ok test a (List.mem_toFinset.mpr (names ▸ ha))
  · rw [←atRoot]
    exact checked ready _ complete 0 row

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 5 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 5 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) SB) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 2 zero,inputs.getD 6 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 3 zero,inputs.getD 7 zero,inputs.getD 1 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xfffffffffffffffffffffeecfffffee8feeefeeefeeafeeafeeefeecfeeafee8fffffffffffffffffffffeecfffffee8feeefeeefeeafeeafeeefeecfeeafee8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 11 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) SB :=
    slice_correct (ms:=fixRows 17 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) SB :=
    slice_correct (ms:=fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) SB :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) SB :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have s4 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 4 zero)) SB :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have s5 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 5 zero)) SB :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have allCuts : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) SB := by
    intro v
    fin_cases v
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
  have low := boundgb certgb allCuts
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,16,144)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,16,144)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def sample7 (r : Row) (i : Fin 8) := bit r (fullRoots.getD i.val zero)
theorem table7 : ∀ r, posted (sample7 r) = bit r fullWord := by decide +kernel
theorem raw7 : List.ofFn (fun i : Fin 8 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
theorem eval7 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs fullRoots).getD o zero=fullWord := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample7 r) = fullRoots.map (bit r) := by rw [←raw7,List.map_ofFn]; rfl
  rw [←bRead,exeBits gs r fullRoots (fun g hg => (legal g hg).1),←e]
  exact (h (sample7 r)).trans (table7 r)
theorem binaryLower (low : Lower true fullRoots fullWord 11)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 11 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval7 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_14502.Model.Repr at out
  rw [nrm_id (by decide +kernel : bit 0 fullWord=false)] at out
  obtain ⟨k,S,hk,run,sub⟩ := extractPlan gs fullRoots legal (by simp) pg (out.resolve_right (fun h => h pg))
  rw [nrm_map (by decide +kernel : fullRoots.all plainWord=true)] at sub
  have rr := list_run run S.toList (Finset.nodup_toList _) (Finset.toList_toFinset _)
  have supplied : supply true (fullRoots.map observe) (S.toList.map observe) := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨q,B,hr,hit,hq⟩ := contraction (observe_proper pg) rr _ Reach.start supplied
  have bound := low q B hr hit
  omega

def mono : List Gate := [⟨.or,[3,7]⟩,⟨.and,[8,6]⟩,⟨.or,[0,4]⟩,⟨.or,[6,7]⟩,⟨.and,[10,11]⟩,⟨.or,[1,2]⟩,⟨.or,[5,7]⟩,⟨.and,[13,14]⟩,⟨.and,[0,4]⟩,⟨.or,[9,12]⟩,⟨.or,[17,15]⟩,⟨.or,[18,16]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,19⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o legal _ correct
  by_cases clean : ∀ g ∈ gs, g.op ≠ GateOp.not
  · refine ⟨gs,o,?_,Nat.le_refl _,correct⟩
    intro g hg
    obtain ⟨op,len⟩ := legal g hg
    exact ⟨op.elim Or.inl (fun h => Or.inr (h.resolve_right (clean g hg))),len⟩
  · push Not at clean
    obtain ⟨a,ha,hop⟩ := clean
    have lo := binaryLower low gs o (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using legal) correct
    have less : gs.countP (fun g => !isNot g) < gs.length := by
      by_contra! bad
      have e := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length bad) a ha
      simp [isNot,hop] at e
    exact ⟨mono,19,monoShape,by change 12 ≤ gs.length; omega,monoEval⟩
end PEqualNP.Outside.L_meta_14502

open PEqualNP.Outside.L_meta_14502 in
theorem PEqualNP.Outside.L_meta_14502 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
