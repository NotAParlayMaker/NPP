import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_11878.Model
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
  (n*(n+971)) % 2305843009213693951
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


end PEqualNP.Outside.L_meta_11878.Model

namespace PEqualNP.Outside.L_meta_11878
open PEqualNP.Outside.L_meta_11878.Model
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

def SB : Nat := 4

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

end PEqualNP.Outside.L_meta_11878

namespace PEqualNP.Outside.L_meta_11878
open PEqualNP.Outside.L_meta_11878.Model
def s0K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (6+((h/1+packedAt s0K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x3f83f07ff07ff8787c1e1f03c7fc07ff3243cf
  | 2 => 0xc003ff83fffc1f807fffe003f87fff803f8cfc
  | 3 => 0xfffffffc007fffff801fffffff8007ffc3ff0f
  | 4 => 0x3ffffff801fffffe00003fffff801fc0ff0
  | 5 => 0xfffc000000001ffffffffffc00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x856713288cab182c1f0b192144e454d53241c5
  | 2 => 0x9329251924412a8025372848c829350c17845c
  | 3 => 0xa004010611001908004421a9100a228409e0a
  | 4 => 0x2c528a42481a555d4a4010932652c031e80ba0
  | 5 => 0x30630c638e639e6673999ce004630441bf6000
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xfff0ff00fcf0cc00fff0ff00fcf0cc00fff0ff00fcf0cc00fff0ff00fcf0cc00fff0ff00fcf0cc00fff0ff00fcf0cc00fff0ff00fcf0cc00fff0ff00fcf0cc00, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_11878
namespace PEqualNP.Outside.L_meta_11878
open PEqualNP.Outside.L_meta_11878.Model
def s1K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (i*5) 5
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (6+((h/1+packedAt s1K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfe1f1fc7fe3ffe1c71f8e07c7e0fffe19327f
  | 2 => 0xf1fe01ff87fc78fe07e3f007f8ff0e1e663d93
  | 3 => 0x1fffe3ff8007f1ff803fff8ff000fe187ce1c
  | 4 => 0xfe00003fffff801ffffc0000fffff001f80fe0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x80280204210420008105024101204308091025
  | 2 => 0x2840a4891240c10a02229092484a0454262492
  | 3 => 0x6484609010c910264800a430d20628c4824e18
  | 4 => 0x441549224480125554480120a494a081d00b40
  | 5 => 0x8919810367126499a79349c40018c1197db000
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xfffaffa0fafaaaa0fffaffa0fafaaaa0fffaffa0fafaaaa0fffaffa0fafaaaa0fffaffa0fafaaaa0fffaffa0fafaaaa0fffaffa0fafaaaa0fffaffa0fafaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_11878
namespace PEqualNP.Outside.L_meta_11878
open PEqualNP.Outside.L_meta_11878.Model
def s2K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (6+((h/1+packedAt s2K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xf83c3fc7fffe1fe1c3ff0e0fc3fff87f1d33cf
  | 1 => 0xffc03ff87c3fe3fe03c3f00ffc783f8f923d33
  | 3 => 0xffffc7ff803ffc3ffc03fff0ff803ff0e3ce3c
  | 4 => 0x7ffffc0003ffffc0000ffffc000fc0fc0
  | 5 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xa0040421010200080850241008a0844051045
  | 1 => 0x909294912265062a2162908a6450950a922512
  | 3 => 0x21080100088800444400242089012220204a28
  | 4 => 0x85ab36254a0d4ab76a688128f2658322f80f80
  | 5 => 0xc632243673319339b3b3c9cc2046044cdfb000
  | _ => 0
def s2Atlas : Atlas := ⟨3,rawDecor 59 s2Pos s2Neg, 0xffaaff88eeaaee88ffaaff88eeaaee88ffaaff88eeaaee88ffaaff88eeaaee88ffaaff88eeaaee88ffaaff88eeaaee88ffaaff88eeaaee88ffaaff88eeaaee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_11878
namespace PEqualNP.Outside.L_meta_11878
open PEqualNP.Outside.L_meta_11878.Model
def s3K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (i*4) 4
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (5+((h/1+packedAt s3K3 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff73ffc71fff0ff
  | 1 => 0xffffffffffffffffffffffeaf8333f81ce7c93
  | 2 => 0x73ffc3cffe0f8f1c
  | 4 => 0x7cfffc0ffff00fe0
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa010400010420025
  | 1 => 0x1526a64c8ca56c92
  | 2 => 0xc42281524092518
  | 4 => 0x38402aa49204ac0
  | _ => 0
def s3Atlas : Atlas := ⟨3,rawDecor 23 s3Pos s3Neg, 0xfafaa8a8fafaa8a8fafaa8a8fafaa8a8fafaa8a8fafaa8a8fafaa8a8fafaa8a8fafaa8a8fafaa8a8fafaa8a8fafaa8a8fafaa8a8fafaa8a8fafaa8a8fafaa8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_11878
namespace PEqualNP.Outside.L_meta_11878
open PEqualNP.Outside.L_meta_11878.Model
def s4K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s4K3 (i*5) 5
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s4K3 (6+((h/1+packedAt s4K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x3c3fffc7fc3fffe1c30e0fffc3f0ffff09f27f
  | 1 => 0xc03c3ff87fc7c3fe03f00f0ffc7f1e0f913d93
  | 2 => 0x3fc7ff8007fc3ffc000ff0ff801ff0e1ce1c
  | 3 => 0xffc007fffff8003ffffff000ffffe000fe0fe0
  | 5 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x440042204100008102421100908284085025
  | 1 => 0x928a94914a0a262a2290858a642a142a912492
  | 2 => 0xab11b5251a94a277648129a8e9065962e18e18
  | 3 => 0x8010200100088844824200092444040220b40
  | 5 => 0x3222243663273339b3c9cecc2008918cddf000
  | _ => 0
def s4Atlas : Atlas := ⟨3,rawDecor 47 s4Pos s4Neg, 0xffa8ffa8eea8eea8ffa8ffa8eea8eea8ffa8ffa8eea8eea8ffa8ffa8eea8eea8ffa8ffa8eea8eea8ffa8ffa8eea8eea8ffa8ffa8eea8eea8ffa8ffa8eea8eea8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_11878
namespace PEqualNP.Outside.L_meta_11878
open PEqualNP.Outside.L_meta_11878.Model
def s5K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s5K3 (i*5) 5
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s5K3 (6+((h/1+packedAt s5K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1e3f8f8ffc7f8fff0c63e383fc7e0fff08727f
  | 1 => 0x1fc7f00e3f8ff1c7f07c7c038f8ff1c7364d93
  | 2 => 0xe007fff03ff001f8ff807ffc0ff001f8c78e1c
  | 3 => 0xfff800003ffffe00ffff80000ffffe00f80fe0
  | 4 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x2008010040010000000808080120040001025
  | 1 => 0xc4a1052449250308502464292484a096164492
  | 2 => 0x4192230490232481348029180d206532428e18
  | 3 => 0x9106a49224a0092ad4900504a494c20e80b40
  | 4 => 0x90244c08034c4924ca72526260018804bd6000
  | _ => 0
def s5Atlas : Atlas := ⟨3,rawDecor 31 s5Pos s5Neg, 0xfefaeea8fefaeea8fefaeea8fefaeea8fefaeea8fefaeea8fefaeea8fefaeea8fefaeea8fefaeea8fefaeea8fefaeea8fefaeea8fefaeea8fefaeea8fefaeea8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_11878
namespace PEqualNP.Outside.L_meta_11878
open PEqualNP.Outside.L_meta_11878.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x4600005e48006800100018000056000000302200241a000000000000160e3242000064003e0060000000007a4a5226005a000040000400800062003800005c0c282a6e3600000000000000500008120000000000000000820000007c003c3a0000060200000000000000002c660000001c766a542078341e0a744c4e4470002e007200146c580000000000007e000000000000010000010000030000000a0806000000000700000200007fd5001fe54007f55001fc54007fd4c01fe53005f94c01fd53007f14c017c53007fd0c01fe43007f50c01fc43007fd4801fe52007f54801fc52007fd0801fe42007f50801fc42007fcc801fe32007f4c801fc32007fd44017f51007f94401fd51005f54401fc51007fd0401fe41007f50401fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc21007fd40017f50007f94001fd50005f54001fc50007fd0001fe40007f50001fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x224000af19120005fec690002fe63480017eb1a4000bf18d20006fca6900037c5348001f72124000fb50920007dc6490003ed32480017fb0a4000bf18520006fea2900037d5148001f790a4000fb48520006fea0900037d5048001fd2024000fe50120007f64090003ee20480017fb284000bf99420006fcca100027e65080017eb284000df59420004faca10002fc65080017fb204000bf990200077cc810002be64080017eb204000ef590200057ac810002fc64080017fb184000bf98c20007bcc610002de63080017eb184000f758c20005bac610002fc6308001bf2984000df14c20005fcc410003ef4208001f62104000bf98420007ecc210002f661080017eb084000fd58420005eac2100037f5108001bea884000bf98020006fea0100037d5008001f79004000fe88020007da4010003f920080017fb2e2000bf99710006fccb880027e65c40017eb2e2000df59710004facb88002fc65c40017fb262000bf99310005fac988002fc64c40017fb1e2000bf98f10005fac788002fc63c4001bf29e2000df14f10005fec588002fe62c40017eb162000bf18b10006fea3880037d51c4001fb20e2000fd50710007ec6388003f531c4001fb10e2000fd48710006fea1880037d50c40017fb2c2000bf99610006fccb080027e65840017eb2c2000df59610004facb08002fc65840017fb242000bf99210005fac908002fc64840017fb1c2000bf98e10005fac708002fc6384001bf29c2000df14e10005fec508002fe62840017eb142000bf18a10005fac3080037f5184001fb28c2000df54610007eaa308003755184001fb98c2000fd0c610005fcc1080037f5084001bea842000fe8c210007f26108003f71084001fd8842000bfd9510005fcca880037e65440013f32a2000bf59510006faca880027d65440017e32a2000bfd9110005fcc888002fd64440017e3222000bfd8d10005fcc688002fd63440017e31a2000df94d10006f8a688002ff62440017f3122000bf58910005f8c4880037f5144001bea8a2000fd90510007ea8288003f63144001fa98a2000fd88510007ea42880037f5044001bea822000fe8c110007f26088003fb1044001fb0822000bfd9410005fcca080037e65040013f3282000bf59410006faca080027d65040017e3282000bfd9010005fcc808003be64040015f3202000bf590100077ac808002bd64040017e3202000bfd8c10005fcc608003de63040016f3182000bf58c10007bac608002dd63040017e3182000df94c10006f8a608002ff62040017f3102000fb98810005dcc408002fd6204001f6b102000bb58810005f8c408002fe6104001bfa882000fd94410006faa208003f55104001baa882000fdcc410007e86208002fe6004001bfa802000df54010007ee2008003fa1004001fa8802000fe44010
  | 1 => 0x3ed621000176b108000ef90840007788420002fe6110001fb3088000bd98440005fac220003f561100017ab088000dfd4440006faa220002fe6010001bfa808000df540400077e8020003fa4010001dea008000fe50040005fecb980077f65cc0013fb2e6000bf99730005facb98002fc65cc003be32e60009f19730005fec998002fe64cc0017eb266000bf1933000efca7980077c53cc001ef21e6000f750f30005fcc598002fd62cc001ef9966000f74cb30005fcc398002fd61cc001bfa8e6000df54730007be6398003dd31cc001bfa866000df54330005fecb18002fe658c001bf32c60009f99630005facb180037d658c0013eb2c6000bf19630005fec918002fe648c0017eb246000bf19230005fac7180037e538c001be29c6000bf98a30005fac518002fe618c0017eb0c6000dfd4630006faa318002fe608c001bfa846000fe94230006faa118003f9508c001bca846000f7cc230007f66118002ff654c001bfb2a60009fd9530005fcca98002fd654c0017e32a6000df19530004f8ca98002ff644c0017f3226000bf59130005f8c8980037e534c001be29a6000f790d30007ba8698002ff624c0017e3126000f7cc930007ba6498002ff614c001fbb0a6000bdd8530005f8c298003f4614c0017a30a6000dfd4530006faa298003df314c001ee98a6000dfd4130007f4a0980037d504c001fca826000de54130007f66098003de304c0017fb286000bf99430006fcca180027e650c0017eb286000df59430004faca18002fc650c0017fb206000bf990300077cc818002be640c0017eb206000ef590300057ac818002fc640c0017f3186001df94c3000ef8a618002fe620c001f73106000bb98830005fac418003ed620c00176b106000bf98430007ecc218002f6610c0017eb086000fd58430005eac2180037f510c001bea886000bf98030006fea0180037d500c001ef9806000fe8c030007ba6018003f9300c0017fb2e4000bf99720005facb90002fc65c80017fb264000bf99320005fac990002fc64c80017fb1e4000bf98f20005fac790002fc63c8001bf29e4000df14f20007dc8590003ed42c8001f71964000fb4cb20005fcc390002fd61c8001bfa8e4000df54720007de4390003ed21c8001bfa864000df54320005fecb10002fe6588001bf32c40009f99620005facb100037d65880013eb2c4000bf19620005fec910002fe64880017eb244000bf19220005fec710002fe63880017eb1c4000bf18e20006fca7100037c53880017eb144000fbd0a20007d88510002fe61880017eb0c4000dfd4620006faa310002fe6088001bfa844000df54220007f48110003f94088001f79044000fec8220005feca90002fe65480017eb2a4000bf19520005fec890003bf64480015fb224000bf99120005fac890002fc6448001de3
  | 2 => 0x50006ecc3a80037d61d40013eb0ea000dd58750004eac3a80037c61d4001bfa0ea000df90750006fa83a80037c41d4001bf98ea000df8c750006fa63a80037c31d4001bf90ea000df88750006fa43a80037c21d40017eb2ca0009f59650005fcc928002fd64940017f31ca000bf58e50006fca7280037c53940017f314a000bf58a50005fcc328002fd6194001bfa8ca000df54650005fcc1280037f5094001fda84a000bfd9150005f8c8a80037f5454001bf2a2a000df55150006f8a8a8002ff63540017e31aa000dfd4d50006fca6a80037d5354001be29aa000bfd8950005f8c4a80037f5254001bf292a000df54950006f8a4a8002ff61540017e30aa000dfd4550006fca2a80037d5154001be28aa000fed4150006fca0a80037f6454001bf322a000df59150006f8c8a80037f6354001bf31aa000df58d50006f8c6a80027c6354001bfa1aa000df90d50006fa86a80037c4354001bfb12a000df98950006fac4a80037c6254001bfa12a000df90950006fa84a80037c4254001bf992a000df8c950006fa64a80037c3254001bfb0aa0009fd8550006fcc2a80037d6154001be30aa000dfd0550006fc82a80037d4154001be20aa000dfcc550006fc62a80037d3154001be18aa000dfc8550006fc42a80037d2154001be10aa000dfd8150006f6c0a8002fe65140013f328a000bf99050005fac828002fe63140017eb18a000df94c50006f8a628002fe62140017eb10a000bf98450005fac2280037f5114001bea88a000bf98050006fea028003fa5014001bea80a000fe54050005fecba0002fe65d00017eb2e8000bf19740005fcc7a0002fd63d0001bf29e8000df14f400077e87a0003bd43d00017f3168000bf58b400077e85a0003bd42d00017f30e8000bf58740006fea3a00037d51d0001dfa0e8000ef50740006fea1a00037d50d00017fb2c8000bf99640006fccb200027e65900017eb2c8000df59640004facb20002fc65900017eb248000bf98e40005fac7200037e5390001be29c8000bf98a40005fac520003be4290001de2148000bf98640005fac3200037f5190001bea8c8000bf98240006fea1200037d5090001dfa048000fed0240005fecaa0002fe65500017eb2a8000bf19540005fec6a0002fc6350001bf29a8000df14d400077e86a0003bd43500017fb128000fbd8940005dec4a0002fc6250001f63128000bb189400077e84a0003bd42500017fb0a8000bf18540006fea2a00037d5150001dfa0a8000ef50540006fea0a00037d5050001fda028000ef90140005feca20002fe6510001bf32880009f99440005faca200037d65100013eb288000bf19440005fcc820002fe6310001ef3188000b798c40005fac620003dd63100016eb188000df94c40006f8a620002fe6210001f73108000bb98840005fac42000
  | 3 => 0xfa8a6200fd94531006faa298803f5514c401baa8a6200fdcc531007bc6298802ff604c4017e3026200bfd9431005fcca188037e650c4013f3286200bf59431006faca188027d650c4017e3286200bfd9031005fcc818803be640c4015f3206200bf590310077ac818802bd640c4017e3206200bf98c3100efca6188077c530c4017f3106200fb98831005dcc418802fd620c401f6b106200bb58831005fcc2188037f510c401bea886200fd90431007ea8218803df310c401fb1886200f74c431007ea6218802fe600c401fd3006200be98031005fac018803f9600c4017cb006200bfd9721005fccb90802fd65c84017e32e4200bfd9321005fcc990802fd64c84017e3264200bfd8f21005fcc790802fd63c84017e31e4200df94f21006f8a790803ef42c8401f62164200fb8cb21007da65908037f51c8401bea8e4200bf98321005fac190802ff65884017f32c4200df99621004fccb10802fd6588401beb2c42009f59621005f8cb10802ff64884017f3244200ef992210057cc910802fd6488401deb244200af59221005f8c910802ff63884017f31c4200bf58e21005f8c7108037e5388401be29c4200bf58a21005fcc3108037f5188401fb28c4200df54621007eaa310803755188401fb20c4200fd50621007ee6310803f43188401f790c4200fdc8621005fcc110802fd60884017fb2a4200bf99521005faca90802fc65484017fb224200bf99121005fac890802fc64484017fb1a4200bf98d21005fac690802fc6348401bf29a4200df14d21007de8490803ec4248401f71924200fb4c921006fea290803f65148401bea8a4200fd54521006eaa290803f64148401faa0a4200fdcc521007e86290803f72148401f710a4200bfd8121005f8c090802ff65084017f3284200df99421004fcca10802fd6508401beb2842009f59421005f8ca10802ff64084017f3204200bf59021005f8c810802ff63084017f3184200bf58c21005f8c6108037e5308401be2984200bf98821005fcc2108037f5108401bea884200fbc8421007ec4210803ed2108401fa9084200bf98021005fac010802fe64d40017eb26a000dfd5350006fca9a80037d54d4001be2a6a000bf98f50005fac7a80037f53d4001bf29ea000df54f50006f8a7a8002fe62d40017eb16a000dfd4b50006fca5a80037d52d4001be296a000bf98750007ecc3a8002f661d40017eb0ea000fd58750005eac3a80037f51d4001bf28ea000df54750006f8a3a80037f64d4001bf326a000df59350006f8c9a80037f63d4001bf31ea0009f98f50006fac7a80037c63d4001bfa1ea000df90f50006fa87a80037c43d4001bfb16a000df98b50006fac5a80037c62d4001bfa16a000df90b50006fa85a80037c42d4001bf996a000df8cb50006fa65a80037c32d4001bfb0ea000df987
  | 4 => 0x8037e5354401bea9aa200df14d51005fec4a8802fc6254401bfa92a200df94951006faa4a88037c5254401fba8aa200df94551005fec0a8802fc6054401bfb22a200df99151006fac8a88037c6454401bfb1aa200df98d51006fac6a88037c63544013e31aa200dfd0d51006fc86a88037d4354401be21aa200dfd8951006fcc4a88037d6254401be312a200dfd0951006fc84a88037d4254401be212a200dfcc951006fc64a88037d3254401be192a200dfd8551006eec2a88037f60544013fb02a200df98151006fac0a88037c60544017f328a2009f99451005fcc828802fd64144017f318a200bf58c51006fca6288037c53144017f310a200bf58851005fcc2288037f5114401fb288a200df54451007eaa228802fe60144017eb00a200bfd9741005fccba0802fd65d04017e32e8200bf98f41005fac7a08037e53d0401be29e8200efd0f410077a87a0802fe62d04017eb168200ef90b410077885a08037f51d0401bea8e8200bf98341005fac1a0802ff65904017f32c8200df99641004fccb20802fd6590401beb2c82009f59641005f8cb20802fd64904017f31c8200bf58e41006fca7208037c53904017f3148200fb98a41005dcc520802fd6290401f6b148200bb58a41005fcc3208037f5190401fb28c8200df54641007eaa320803755190401dfa0c8200fdd0641005fcc120802fd60904017fb2a8200bf99541005facaa0802fc65504017fb1a8200bf18d41006fca6a08037c5350401dfa1a8200ef50d41005fec4a0802fc6250401df2128200ef10941006fea2a0803f65150401bea8a8200fd54541006eaa2a0803f74150401df20a8200bfd8141005f8c0a0802ff65104017f3288200df99441004fcca20802fd6510401beb2882009f59441005f8ca20802fe64104017f3188200bf58c41006fca6208037c53104017f3108200bf58841005fcc2208037f5110401bea888200efd0441007ec8220803bd4110401faa088200bf98041005fac020802ff65cc403bfb2e62009fd9731005fccb98802fd65cc4017e32e6201df19731004f8cb98802ff64cc4017f3266200bf59331005f8c9988077e53cc403be29e6200bf98b31005fac5988037f51cc401bea8e6200fd90731007ea8398802fe60cc4017eb066200bfd9631005fccb188037e658c4013f32c6200bf59631006facb188027d658c4017e32c6200bfd9231005fcc918802fd648c4017e3246200bf58e31006fca7188037c538c4017f3146200bf58a31005fcc3188037f518c401fb28c6200df54631007eaa31880375518c401ef98c6200fdcc631005fcc118802fd608c4017fb2a6200dfd9531004feca98802fe654c4017eb2a6200bf19531006f8ca988027c654c4017fb226200bf99131005fac898802fc644c401bf29a6200df14d31005fec498802fc624c401b
  | 5 => 0x8242005fecaa1002fe65508017eb2a8400bf19542005fec6a1002fc6350801bf29a8400df14d42007de84a1003be42508017fb0a8400bf18542005fec0a1002fc60508017fb288400bf99442006fcca210027e65108017eb288400df59442004faca21002fc65108017f3208400bf98c42007bcc621002de63108017eb188400f758c42005bac6210037e5310801be2988400efd0c420077a8621002fe6210801dfa108400fb908420077a8421003ed4210801d6a108400bf98442007ecc221002f661108017eb088400fd58442005eac221002fe6010801fd3008400be98042005fac021003f960108017cb008400bfd9732005fccb99002fd65cc8017e32e6400bfd9332005fcc999003be64cc8015f3266400bf593320077ac999002bd64cc8017e3266401df94f3200ef8a799003de43cc801eea1e6400bf98732005fac399002fe60cc8017eb066400bfd9632005fccb190037e658c8013f32c6400bf59632006facb190027d658c8017e32c6400bfd9232005fcc919002fd648c8017e3246400bf58e32006fca7190037c538c8017f3146400fb94a32007daa519003ef428c801f62146400f7cca32007de6519002fe618c801fb30c6400bd98632005fac319003f5618c8017ab0c6400bf98232005fac119002ff654c801bfb2a64009fd9532005fcca99002fd654c8017e32a6400df19532004f8ca99002ff644c8017f3226400bf59132005f8c8990037e534c801be29a6400f790d32007ba8699003ee524c801f6a926400fbd0932007d88499003ef324c801ef1926400bfd8532005f8c299002ff604c8017e3026400bfd9432005fcca19002fd650c8017e3286400bfd9032005fcc819002fd640c8017e3206400bf98c3200efca6190077c530c8017f3106400f7cc832007dc6419003dd320c801f69906400bf98432005fac219002fe600c8017eb006400bf99351005fac9a88037f54d4401bf2a6a200df55351006f8a9a8802fe63d44017eb1ea200dfd4f51006fca7a88037d53d4401be29ea200bf98b51005fac5a88037f52d4401bf296a200df54b51006f8a5a8802fe60d44017eb06a200dfd9351006fcc9a88037d64d4401be326a200dfd8f51006fcc7a88027e63d4401beb1ea200df18f51006fe87a88037e43d4401bea1ea200df10f51006fec5a88037e62d4401beb16a200df18b51006fe85a88037e42d4401bea16a200df10b51006fe65a88037e32d4401be996a200df0cb51006fec1a88037e60d4401beb06a2009f58351006f8c1a8802fd65944013eb2ca200bf99251005fac928802fe63944017eb1ca200df94e51006f8a728802fe62944017eb14a200bf98651006fea328803f751944017f304a200bf58251005fec8a8802fc6454401bfaa2a200df95151006faa8a88037c54544017fb1aa200bf18d51006fea6a8
  | 6 => 0x1ef298a600df54c53007baa629802fe6214c01f7310a600bb98853005fac429803ed6214c0176b10a600bf98453007ecc229802f66114c017eb08a600fd58453005eac229802fe6014c01fd300a600be98053005fac029803f96014c017cb00a601dfd9053006fcc8298033e6414c01beb20a600cf5905300ef8c8298077e6314c013f318a600d798c5300efec4298037e6214c01b7310a600df58853006dac4298077c6214c03bfb08a600df98453006ecc2298037d6114c013eb08a600dd58453004eac2298077c6114c03bfb00a600df98053006f4c0298037d6014c013eb00a600de58053004f2c0298077c6014c017fb2e8600bf99743006fccba18027e65d0c017eb2e8600df59743004facba1802fc65d0c01df2a68600ef55343006fca7a18037c53d0c017f3168600bf58b43005fcc3a1803f661d0c017b30e8600bf58743007eac3a1802f561d0c017f3068600bf58343005fecb21802fe6590c017eb2c8600bf19643005fac921802fe6390c03bf29c8601df14e430077e8721803df4390c017f3148600fb98a43005dcc521802fd6290c01f6b148600bb58a43005fcc321802fd6190c017f3048600bf58243005fecaa18037f6550c013fb2a8600bf99543005facaa1802fc6550c01be32a86009f195430077ca8a1803bd5450c01bf29a8600df14d43007be86a1803be4350c017fb128600bf18943005fec2a1802fc6150c017fb028600bf18143005feca21802fe6510c017eb288600bf19443005fcc821802fe6310c03bf2988601df14c430077e8621803de4310c01dea188600f750c43005fcc421802fd6210c017f3088600bf58443005fcc021802fd6010c017f326a400bf59352006fea9a90037d54d48017f31ea400bf58f52006fca7a90037c53d48017f30ea400bf58752005fcc1a9002fd60d48017eb2ca400bf99252005fac929002fe63948017eb1ca400df94e52006f8a729002fe6294801bfa94a400fbd4a52005fcc329002fd61948017f304a400bf58252005fec8a9002fc6454801bfaa2a400df55152005fec6a9002fc6354801bf29aa400df14d52007dea4a90037e52548017fb0aa400bf18552005fec0a9002fc60548017f328a400bf99052005fac829002fe63148017eb18a400df94c52006f8a629002fe6214801bfa90a400fb94852006faa429003ed52148017f308a400fd98452005ecc229002fd6114801fab08a400bd58452005fcc029002fd60148017fb2e8400bf99742005facba1002fc65d08017f31e8400bf58f42006fca7a10037c53d08017f30e8400bf58742005fcc1a1002fd60d08017fb2c8400bf99642005facb21002fc65908017eb248400bf98e42005fac7210037e5390801be29c8400efd0e420077a8721002fe6290801dfa148400fbd0a42005fcc321002fd61908017f3048400bf5
  | 7 => 0x200200201401400000200401800602000001600a00a00400200000c00000400000600000e00000000600000000000200000400000600600000000200002000200000601400000000400000400400000001a00000000200a00a01000400e02800000000000000000000800000000801e00000401800000600401600000600000000200000400200000000000400000600400800000000200a00000200800200001800000600200000200e00000800000a00200a00000000a00400000200602002000000000800600400a00001e01000c00c00000000200001a00000000400200200400400000400000000e01200e00200200000400c01000200000400000c00000000c00400000000200400000000400000200601800001c01800200600600000000000000200600400805400200400000000600600000800200200000000000000200001a00c00200c00600000000800200400200001a00200000000000200000a00200000e01000c00000400c01200000200000200000000000e00800802a00200002c00200200000601a00401400000a00200600c00000200001a00801c00000400000000800400200a00000e00600002200400e00000401800200200600000400000400200000000a00000000000200001000400401e00800400400000000400800400000800400000bf98f54005fac7aa002fe62d50017eb16a800bf98754005fac3aa002fe60d50017eb06a800bf59654005fcc92a0037f5495001dfaa4a800cfd5254005fcc72a002fd63950017f314a800bf58a54005fcc32a002fd61950017f304a800bf582540077ea8aa0037e54550017fb1aa800bf18d54005fec4aa002fc62550017fb0aa800bf18554005fec0aa002fc60550017f328a800bf99054006fea82a003be5415001beaa0a800ef55054005fcc62a002fd63150017f310a800bf58854005fcc22a003f661150017b308a800bf58454007eac22a002f561150017f300a800bf58054005fcc9a9802fd64d4c017f316a600bf58b53005fcc3a9802fd61d4c017f306a600bf58353005facb29802fe6494c017eb24a600dfd5253006fca9298037d5494c01be2a4a600bf98e53006fea729803df5394c017f314a600bf58a53005fcc329802fd6194c017f304a600bf5825300efec9298037e6494c01beb24a601df19253004fcc7298077f6294c01bf314a600df58a5300ef8c5298077f6194c01bf30ca600df58653004fac3298077c6194c03bfb04a600df98253006fac1298027d6094c03be304a600bfd9153005f8c8a9803df5354c01bf29aa600bfd8953005f8c4a9802ff6154c017e30aa600bfd8153005f8c0a9802fe6514c017f320a600ef990530057cc829802fd6414c01deb20a600af59053006fea8298037e5414c01beaa0a600df15053005fcc6298037f5314c0
  | 8 => 0x56e80011dc4a522800062c001130000d40d3800091c9600000bc0000016680004d17a474cecca886445490bc0001b8ef0000d983705f56400001a912807d724c700000000001d4000000000000f20e4d01d0e4fc57941c10f4b59380e188a46f900c0000000005c000026d1b000000107958000000000024ced87c91c53900013f0dc48d0adc0002bd5e400000000153800000c9d40014900000000015907580010200019359747cd5a4fec0014540015fcf840001f0f48260050888a0cb182fc0015940c48bd9b8aa8000eb400141c000d8c0003dca210040000000002e8000130c743317bc00058c00180099872c0012900000000019c4de4554dd8c1c00102c0b0c8c000018a400015c5578000000000df4000000000000b200008e40014bd240000000d6d2a4000000000868b7114d16c0000000000010747ec5897e4c512a8000f50a900009192c5031328239248a140002f435835077c0007ac0000002ad5f05d13a400000120d6f52c00000000000000016d09c9090001864fb00000000000005b80011e40017c85c464c92008178d8204646b50649f8fd4000000aac37d5e8a049ccae00000004e00000016a95e19a494c22000000000001c000ed400000177cc0000172060d5741c497c000334b852b0c4536c000ff4001570bbc00000000086400146456867400000093c0016550f800018c000001920418008000b04000e48000000e7400000133c4e46bc6f08e8000398814c8839061c00000071400081c0000000018546a40004400005200005a000000000000137894400157c7944f4c5d5ec0000000000006a80000016a40000000000000000a400000000027d5a1370d8400000101994c00110438c0006b8c48a680000000000017cc000000000000000000cc00003d95980000008e19f4828000000000ad80000019ec000000000000fa98c00007a000000200001600000e00000401600600600801800000c00400400801400a00001000e00600a01600002c00000000000e00c01000000200202600000a00000400000000000200400000000000000600200800400000600000600600a00000000000600200201800200a00200000a00600401400800600800400400000400000400a00000000000200000000200200200200800000a01201200600600801c01200400400c01000200000600000200601e02c00400201e00600000000000800000400e00001000200000200200200c00c00a00a00c00200001400201601800000000000600000200400000800001001400000800201000000401800c00600200400201400400000200600200000a00000c00000600000000400400200e01400a00a00400000000000800a00e00602200600400800200a00000000000200200000000000000000000000600400000e01200401000600c0
  | 9 => 0x7fc5c922016ca000000001c80000011d83681fc2e4ad02147347b40009400005b4000000b44c6174998013d7712680017417f40009a4414000000000c18000000000000000d0422c000000000000000c11a009944980012788600004004504482657dc99cbed17c0018907080019d9884fa00856ac5d4e7c0017b51180012851f40000000009100000000000012a11bc98c6080014f4000cec7a57c4000acc0013dc0000009380016b4f5c0d0001970074000000000000000d5581c0001f8b485bc00000000000000031800000149c094000e411fcc4c00151842cbe0e6400010ce85964fa52b45dd88d9414a93f41b158c7494c80000000018d400000043c668000000000000000000000fac0018d13ed308b6106000000000000000144c184d186480012bcf3d1893d0e98b6400015400000000000000000000031c000d3448000196051c0000012d800000126125d2f4cd90018506e4001400000000ba80007e40000000000000000016e000000000158400000000032d67c0000003613449b0514b3c4b4651939270000000df01390398a059d9a889cb4012d5c993c8cc570000000000fbc000b510fc2301b42dc000ccc00000161c000b140000000000010a4f880000017a034c00044c9d93b94d88ed26cc2c001674000000ca90d55ac1bc1747281ecc245f0d2d4357d9878a495042cc0003fc0003397c0000f90fe4824001280000000b819d00000000014390700000000000000011b998495175968186c0c800045d3d4e01111149830001684a307609e14d41e46c9351664324d009b4000cb40018cc0b869000158868400000106c0ed4ec0014d191820800171cc9cf9d6fc15c6b110c3ecdb00c0d758f43a00018e05907d58140004d97753057f8a612dc3c80000000000005f800000000014c001638fe8af800037800000107c0005947191240004ac000e3000000087948d74c1f4534d287d83b44fc3f93c800165c028000000000000000e4488d70800000000000110800000135d618000000bd0000a2c00155820400000081800000030979c000044000000000000000d0c738e156c4d6000112c934000000000a2800018972c000d70000000001460ab8001968f385400ad09c2780000010dc4e83bc7dcead9dd9e0e24628000908e1d1e82900014882f10340010a8001480000524dccc04aa1614000244ae547cac00ccedc980e68000984b0c000b38da4c948583ac50852c0000000009d13a80113b197cd4457c4c843400000000000000000000000133049c00054c9c4afc00035c8c8ea139c6808040000007854694c4898a5d8dc00006c00069c064d1ca718b46796d81080014b10ec0007f0000af4408000a99560e2855cc398289fc6d49293608fcb98001140000000000000001185470ee0001500915474000d900017000f822
  | 10 => 0x105a4f81101250380280140fc8614500de836495963c848240000f40030a08000000564168b6ce50000518d5082152c43880d174000ab4c5800111c8f0000bd80000017d0ea8000be83d1340001730001608001908000dbc000b8ce3c57563084c0018348c108d860001084fb85acbc40019045fc0000019d4001760000cf0e605110d80015d54f0001894000f0942d2e442404cd14180f00000dfd6dc00090400165827000000144505cb343f5274001429944d644cd565955900474f944440011140018ac6d000000000169c0000002c00000014980009309798a400002070d3385d800000000184d5691ed1b4ae80015097ec4300007d023c578764ba06c14e4300bc000000000129527d5d9530a85008000d940000000d9755744000000a8c8094945980002ed96c000a956f8d3118c6359e8cd55b00000000017345cc0005440000000000000013596716900003412081506a00004f010531087000031180ce117aca180017800009741dc00000000000000175c7f4000000058000f780010d000047882ca6c7bc0f400089466000064076c000e5d9780000000000000006f40000012e82d150c4f97380018f98b85800018c800000000171400028800000017800000000000119887d414e70000744000b552b8f051c0000f2d8f0fc0dac0e00000012ec0000000000000fc000f6cea448c0010b8000000ee40000000000000000007c461873d86984468953d7507400000000340f119425caecb9c198b5c79cd091ad840000b4c00000063c000ca4bdcfe1430000884e2c1a5264090000000000000fd00000000002a01188a80003294259a0bac000efc00000000130cd7cb117696480000019c11e04c4000ee800000143cc848b4d5c0015c06116340000000009acbfc000000f25510000000cb0b0896d2cc000f60cf50551ccda18bc4bc0000004545a91d54400001e8f597b96200009000014dc00132c000db53e8f289640011519fc00000160000114580446c000c20000001224f64ac9398000000000b1c0002540007207c00017e0dc800140c0011a40000000000018800000008dc0000010294e00000000013c4000000000710070000000f1492cebd998eb151d300774000cc830562c111544e5497000000009c000c78f70c9904c0003e80009e866c0000002107f8000000000604000000000ff11540000003f0ec80009900000000000000000000000000019b517071c274e8c298000a44b687991a0f744703b12388f80009a00000015219ad2fc40545883c00172800121c6ed2f80000000000000000018587e80008d83b800138c160ef9524000b7c0000000000000000000053640010e00009f45e41d80000000000000008d55bc0000880008a12190951d00dd6980004290105390141a07542a8000000000c098b00019b1550d25
  | 11 => 0x17880000013b556c000001099650000f98f1c000f312f00007000000010c07a82d8d80cf8c810c8000cb84b00000003cc17ca24f34df9914bc800068cdd00004eccad52876894825000166c0000019880000000013a00003e4790698e216780003440000004c0001484000da9604000001899958cd180808c00038400013400053d2d42c4670000000144469048ba46acb0113c0000013fc0009b90ac000bb43c4000cc40000015488540015d0000000000530000000000d3c0007e0000000000024000b94a399f0f183153140000018e439c0006e8000120000001318000bcc0000002b4c3000033c164e80a788b82b8800f1073178583889129d408b744612c8e0d13582c000125214000000dc0048c640000000000000000016c898924c000ce4840e08000001088000d9c9e4a8000067d354000c7c060ef4000b30620320fd96894c070400000045820d4100794797100001956b0a5590c420bf44840000010c40011a8000000000100000ad409800000000000000000000077000000000000095c000000000000c35554db80004b8000a9d6ec000e38000000001395420ec4ddd1650cc830001059204a644d53c00a1798694a3d4f803c0014a4ff8aa40000004a0924eed87d0a13ad31c6fc000e89644d780000019500013850407fd1200d545c0015405ed92cb9118146c0006cd2302342e00000000015a90e863000176415800040c0000000000000005580000000000000b42c8f6800137564c7883c0000f559cc000e788c40000000009ed9c8000a34c555b86582941e168c83937d024ce0750dd41cc48800000000090c0010f00008500018888acb24eb87b8b2932400084460000078d3e4d48fb4000000d581ac3a8001388ed0a58000000c40000834a4c000e045519f8000000001534000000ac4874000ce82b00000000000000000000017e960d7d4e956cd6100000012980012d11f800113825800154c0016d4b79871418040505514001158ffd15c0012443d4528001790f0c0000000000558ed6e465cec170c7258255cc6dc00005c4a9449044000001234000bb8000c3c0a9948001050000cfd83c880b898494fcbf0ab00016bc6c46240000019bd3491c8f4598d924000bf817122c9a80014e86e1288038e9030c0e99957f01911f1874000248000e5976c11cf8c86c000a10001910f4d3213d80005e93f8d8800000021c00000028c00000000011400103d3bcc14d21190268780388c29991450000d4d4a12540000685b03480006d875d95cbb18d80000018c40010819e400119c3958a89f0a500017b16946554b400189c0016a00000016b8001168000decc9041d404e9cf7c000001930000af00002a43a4000000c6d7a99295f40000000000000013cc0000000000000000000015b40e517800047d73c36ccdc001660000410d
  | 12 => 0x9dd2e0de09c00001489bc3e001400128c2f955c0016243548b1210218128c0d8e80002840018fca1c0000018107b0000b2d99cd680000000006380000010b4c680000000008f4000584000968000001718000000000000000000000000000abd0b000185cbe400000050cfdc5600008100000016296f0201704000e6c02c000490000374954e3400000000000133559ca74cbc00191c000a7c664000fccbd520116077829d4b82d400125885d4cc0000015f80015dc4dc0018196c00005e019c000ca177822923c00056c0000000001d000000106800000134d4ac0000012ad3680013e000049400
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe75190100047d7519010004be7419010004de7319010004dd7319010004ee7219010004ed7219010004f671190100047e75d8c100047d75d8c10004be74d8c10004bd74d8c10004ee72d8c10004ed72d8c10004dd7698c100065e6598c100065d6598c100069e6498c100069d6498c1000e5f7598c1000e5c7598c100047f7558c100047c7558c100065e6558c100065d6558c100069e6458c100069d6458c100065f7558c100065c7558c10006d47158c100047e7518c100047d7518c10004be7418c10004bd7418c10004de7318c10004ee7218c10004ed7218c10004f67118c10004fa7018c1000c7f7694c100047d7694c100063e6494c100063d6494c1000e5e6394c100065d6394c1000c7f7614c100047d7614c100063e6414c100063d6414c1000e5e6314c100065d6314c10005757114c10005797014c100047e75d88100047d75d8810004be74d8810004bd74d8810004de73d8810004dd73d8810004ed76988100066e65988100066d6598810006ae6498810006ad6498810006ce6398810006cd63988100066e53988100066c53988100066e65588100066d6558810006ae6458810006ad6458810006ce6358810006cd63588100066e53588100066c53588100047e75188100047d7518810004be7418810004bd7418810004de7318810004dd7318810004ee7218810004f671188100047e75984100047d75984100047d76d44100063e64d44100063d64d44100065e63d44100065d63d44100066e62d44100066d62d4410004f57694410005757594410006b56494410006d56394410006e562944100047f76544100063e64544100063d64544100065e63544100065d63544100066e62544100066d6254410006766554410006b56454410006d56354410006e56254410005777654410006777654410006776454410007366454410006756454410007356454410006356454410005747354410006776354410007566354410006756354410007556354410006556354410006776254410007666254410006756254410007656254410006656254410005777054410004f576cc4100057775cc410006b564cc410006d563cc410006e562cc410004f5760c41000575750c410006b5640c410006d5630c410006e5620c410005f1700c4100047e75980100047d75980100067551980100047d76d40100063e64d40100063d64d40100065e63d40100065d63d40100066e62d40100066d62d40100057571d40100047f76540100063e64540100063d64540100065e63540100065d63540100066e62540100066d62540100057575c4010006b564c4010006d563c4010006e562c4010004f97684010006d96384010007715184010004f77644010005757544010006b56444010006d56344010006e56244010004fb7644010006d96344010
  | 1 => 0x961000c7c73596100047e75d92100047d75d9210004ef7259210004ec72592100047e75192100047d7519210004de7319210004dd7319210004ee7219210004ed72192100047e75d8e100047d75d8e100047f7558e100047c7558e100047e7518e100047d7518e10004be7418e10004bd7418e10004ee7218e10004ed7218e1000c7f7694e100047d7694e10005797094e1000c7f7614e100047d7614e10005757114e10005797014e100047e75d8a100047d75d8a10004bf7458a10004bc7458a100047e7518a100047d7518a10004be7418a10004bd7418a10004de7318a10004dd7318a100057970d46100067665946100057b70546100067776546100067476546100067764546100067564546100057473546100067763546100067563546100067762546100067562546100057770546100077370546100077070546100057775cc61000575750c610005f1700c6100057571d421000679658c21000771518c21000679654c210005f0714c21000771514c210007d3314c2100057575c4210004f5719951000c7e73995100047d71995100067571995100047571995100047d7099510006797099510004df7359510004dc73595100055c73595100065f735951000c7c73595100065c73595100045c73595100047f71595100067771595100047f70595100067b70595100047e75d91100047d75d9110004ef7259110004ec72591100047e75191100047d75191100047e75d8d100047d75d8d100047f7558d100047c7558d10004f77158d100047e7518d100047d7518d10004be7418d10004bd7418d10004ee7218d10004ed7218d1000c7f7694d100047d7694d10005757194d10005797094d1000c7f7614d100047d7614d100065f6314d1000e5c6314d10005757114d10005797014d100047e75d89100047d75d8910004bf7458910004bc74589100047e75189100047d75189100057970d45100057b7054510006756590510005e57290510004f47650510006756550510004f6768c51000675658c510004f4764c51000675654c510006756588510005b57488510004f476485100067565485100057571d41100047f76541100047d765411000577715411000679658c110004f8764c11000679654c110007d1314c110006756584110004be74d9410004bd74d9410004de73d9410004dd73d9410004ee72d9410004ed72d94100047d769941000c7e739941000676719941000c7c73594100047f71594100047d71594100047f70594100047d70594100047e7519410004be7419410004bd7419410004de7319410004dd7319410004ee7219410004ed72194100047e75d90100047d75d9010004de73d9010004dd73d9010004ee72d9010004ed72d9010004bd76990100063e65990100063d65990100063e65590100063d65590100047
  | 2 => 0x6ac72590200047e75190200047d7519020004be7419020004de7319020004dd7319020004ee7219020004f67119020004f57119020004fa70190200047e75d8c200047d75d8c20004be74d8c20004bd74d8c20004f671d8c20004f571d8c20004dd7698c200065e6598c200065d6598c200069e6498c200069d6498c2000e5f7598c2000e5c7598c200047f7558c200047c7558c200065e6558c200065d6558c200069e6458c200069d6458c200065f7558c200065c7558c200047e7518c200047d7518c20004be7418c20004bd7418c20004de7318c20004ee7218c20004f67118c20004f57118c2000c7f7694c200047d7694c200063e6494c200063d6494c2000e5e6394c200065d6394c2000c7f7614c200047d7614c200063e6414c200063d6414c2000e5e6314c200065d6314c20005757114c20005797014c20004ed76d0820006ad64d0820006cd63d0820004ed7610820006ad6410820006cd6310820005e970108200047e75984200047d7598420006766598420006756598420006b66498420006b56498420006d66398420006d56398420006767598420006757598420006765398420006745398420006766558420006756558420006b66458420006b56458420006d66358420006d56358420006767558420006757558420006765358420006745358420006e74258420006e442584200047f76d44200047d76d44200063e64d44200063d64d44200065e63d44200065d63d44200067661d44200067561d44200047f76544200047d76544200063e64544200063d64544200065e63544200065d63544200067661544200067561544200047e75980200047d75980200047d76d40200063e64d40200063d64d40200065e63d40200065d63d40200057571d40200067661d40200067561d40200047f76540200063e64540200063d64540200065e63540200065d6354020006766154020006756154020006ad64c8020006cd63c8020006e561c8020006b96488020004ef7648020005ac7448020006ad6448020006cd6348020006e56148020004fb7648020006b9644802000c7e739971000c7c73597100047e75d93100047d75d9310004ee72d9310004ed72d93100047e75193100047d75193100047e75d8f100047d75d8f100047f7558f100047c7558f100047e7518f100047d7518f10004be7418f10004bd7418f10004ee7218f10004ed7218f1000c7f7694f100047d7694f10005757194f1000c7f7614f100047d7614f10005757114f10005797014f100047e75d8b100047d75d8b10004be74d8b10004bd74d8b100047e7518b100047d7518b10006756590710005e5729071000675655071000675658c71000675654c710006756588710005b574887100067565487100057571d431000577715431000c7e739961000675719
  | 3 => 0xe75193200047d7519320004de7319320004dd7319320004f67119320004f571193200047e75d8f200047d75d8f20004f671d8f20004f571d8f20004be7498f20004bd7498f200047f7558f200047c7558f20005757114f20005797014f20006ac6450b20005e5718cb200047e75987200047d7598720004be7498720004bd74987200067661547200067561547200076551487200057571d4320004f67199620004f5719962000575719962000c7e73996200067671996200047d719962000675719962000475719962000c7c73596200047f71596200047e75d92200047d75d92200047e75192200047d7519220004de7319220004dd7319220004f67119220004f571192200047e75d8e200047d75d8e200047f7558e200047c7558e20004f77158e20004f47158e200047e7518e200047d7518e20004be7418e20004bd7418e20004f67118e20004f57118e2000c7f7694e200047d7694e2000c7f7614e200047d7614e20005757114e20005797014e20006af6410a20005e97010a200047e75986200047d75986200047f76d46200047d76d46200047f76546200047d76546200057571d4220007a84290220005e87250220007ab4250220004be7499520004bd7499520004f67199520004f57199520004bf7459520004bc7459520004be7499120004ef72591200047e75191200047d7519120004de7319120004dd7319120004f67119120004f57119120004be76191200063e75191200063d75191200069e73191200069d7319120006ad7219120006b67119120006b57119120006b970191200047e75d8d200047d75d8d20004be7498d20004bd7498d200047f7558d200047c7558d20004bf7458d20004bc7458d20004f77158d20004f47158d200063f6494d200063c6494d200063f6414d200063c6414d20005757114d20005797014d20004ee7690920006ac6490920004ec7650920006ac6450920006ac648c920005e5718c920004ec764c920006ac644c9200047e75185200047d75185200063f64d45200063c64d45200063f64545200063c6454520006776154520006746154520006ac64c8520006ac64485200076551485200063f64d41200063c64d41200057571d41200063f64541200063c6454120006b86490120007aa4290120004f87650120007a94250120006ac6488120004be74d9420004bd74d9420004de73d9420004dd73d9420004f671d9420004f571d94200047d769942000c7e73994200047d719942000c7c73594200047f71594200047e7519420004be7419420004bd7419420004de7319420004dd7319420004f67119420004f571194200047e75d90200047d75d9020004de73d9020004dd73d9020004f671d9020004f571d9020004bd76990200063e65990200063d65990200063e65590200063d6559020
  | 4 => 0x8530006e57218530006f170185300047e76d45300047c76d45300067761d45300067461d45300057970d45300047e76545300047c7654530006776154530006746154530006d461cc53000755514c5300047e76d41300055e73d41300057571d41300067761d41300067461d41300057975941300067865941300047c76541300055c7354130006776154130006746154130004f876541300067b76541300057876541300067876541300047876541300075b735413000d7873541300075873541300075a43541300075943541300075b32541300075932541300057b71541300077361541300077061541300075b315413000759315413000d7b75cc13000759508c130004be74d9430004bd74d9430004ee72d9430004ed72d9430004f671d9430004f571d94300047d769943000c7e73994300047d719943000c7c73594300047f71594300047e7519430004be7419430004bd7419430004ee7219430004ed7219430004f67119430004f57119430004fa70194300047e75d90300047d75d9030004ee72d9030004ed72d9030004f671d9030004f571d9030004bd76990300063e65990300063d659903000e3e539903000e3c53990300063e65590300063d655903000e3e535903000e3c53590300047e75190300047d7519030004be7419030004de7319030004ee7219030004ed7219030004f67119030004f5711903000c7f7598c3000c7c7598c300066e65988300066d6598830006ae6498830006ad649883000e6e539883000e6c53988300066e65588300066d6558830006ae6458830006ad645883000e6e535883000e6c53588300047e75984300047d7598430006766598430006756598430006b66498430006b56498430006e66298430006e5629843000676759843000675759843000e76539843000e745398430006766558430006756558430006b66458430006b56458430006e66258430006e5625843000676755843000675755843000e76535843000e7453584300047f76d44300047d76d44300063e64d44300063d64d44300066e62d44300066d62d44300067661d44300067561d44300047f76544300047d76544300063e64544300063d645443000d5c73544300066e62544300066d62544300067661544300067561544300047e75980300047d75980300047d76d40300063e64d40300063d64d40300066e62d40300066d62d40300057571d40300067661d40300067561d40300047f76540300063e64540300063d64540300066e62540300066d62540300067661540300067561540300067a60540300069d64cc030006cd62cc030006d561cc03000679658c030006f1618c030004df764c0300069d644c030006cd624c030006d5614c030004fb764c03000679654c030006f1614c030004f67119720004f571197200047
  | 5 => 0x67661d44400067561d44400047f76544400047d76544400065e63544400065d63544400066e62544400066d62544400067661544400067561544400047e75980400047d75980400047d76d40400065e63d40400065d63d40400066e62d40400066d62d40400057571d40400067661d40400067561d40400047f76540400065e63540400065d63540400066e62540400066d62540400067661540400067561540400069d63d0040006ad62d0040006b561d0040006e96290040004bf76500400069d6350040005ac7250040006ad6250040006b56150040004fb7650040006e9625004000e5e73d97300047d71d973000e7970d9730004be7419730004bd7419730004ee7219730004ed7219730004f67119730004f5711973000e3e741973000e3d741973000e5e731973000e6e721973000e6d721973000e7671197300047d711973000e75711973000475711973000e797019730004ee72d9330004ed72d93300047e75993300047d7599330004f67199330004f571993300047f75593300047c7559330005cd7290f300047e7598b300047d7598b30004f67198b30004f57198b300047f7558b300047c7558b300059d74ccb300047e75987300047d75987300047f75587300047c755873000c7e76d473000c7c765473000676615473000675615473000755514c73000d5e73d43300057571d433000d5c7354330004f67199630004f571996300057571996300067671996300047d71996300067571996300047571996300067a70996300047f71596300047e75d92300047d75d9230004ef7259230004ec72592300047e75192300047d7519230004ee7219230004ed7219230004f67119230004f57119230005757114e30005797014e30004bf7458a30004bc7458a300047e75986300047d75986300047f76d46300047d76d46300057970d46300047f76546300047d76546300055c73546300057571d42300067a65542300057b76542300067b765423000d7873542300057b715423000d7b75cc2300047d71d95300047e7599530004f67199530004f57199530004f77159530004f471595300047e761953000c7e731953000c7c73195300047d71195300067970195300047e75991300047d7599130004f67199130004f571991300047f75591300047c7559130004ef7259130004ec7259130004f77159130004f471591300047e7694d300047e7614d30005757114d30005cd7290d30004dc7650d300059d74cc9300067765d85300067465d85300067775d85300067475d85300067653d85300067453d85300047e75185300047d7518530004be7418530004bd7418530004ee7218530004ed7218530006776518530006746518530006767518530006757518530006b67418530006b57418530006765318530006745318530006e6721
  | 6 => 0xe7298740004ed72987400067661547400067561547400073551507400057571d4340004f67199640004f5719964000575719964000c7e73996400067671996400047d719964000675719964000475719964000c7c73596400047f71596400047f7558e400047c7558e40004f77158e40004f47158e4000c7f7694e400047d7694e4000c7f7614e400047d7614e40005757114e40005797014e40005b97010a400047e75986400047d75986400047f76d46400047d76d46400047f76546400047d76546400057571d42400073950d0240004ee7299540004ed7299540004f67199540004f57199540004ef7259540004ec72595400047e75d8d400047d75d8d40005757114d40005797014d40005b571d0d400066e53d89400066c53d89400047e75189400047d7518940004de7318940004dd7318940004f67118940004f571189400066e75189400066d7518940006ce7318940006cd73189400066e53189400066c5318940006af4318940006ad4318940006e67118940006e57118940006e97018940004be76d0940006ac62d0940006ac62509400047e75185400047d75185400066f62d45400066c62d45400066f62545400066c6254540006776154540006746154540006ac62d0540006ac62505400073551505400066f62d41400066c62d41400057571d41400066f62541400066c6254140006ac6290140004de73d9440004dd73d9440004ee72d9440004ed72d9440004f671d9440004f571d94400047d769944000c7e73994400047d719944000c7c73594400047f71594400047e7519440004de7319440004dd7319440004ee7219440004ed7219440004f67119440004f571194400065e6598c400065d6598c4000e5f7598c4000e5c7598c400047f7558c400047c7558c400065e6558c400065d6558c400065f7558c400065c7558c4000c7f7694c400047d7694c4000e5e6394c400065d6394c4000c7f7614c400047d7614c4000e5e6314c400065d6314c40005757114c40005797014c400066e65988400066d6598840006ce6398840006cd63988400066e53988400066c53988400066e65588400066d6558840006ce6358840006cd63588400066e53588400066c5358840004bd76908400069d6390840006ad62908400069d6310840006ad6210840005b970108400047e75984400047d7598440006766598440006756598440006d66398440006d56398440006e66298440006e56298440006767598440006757598440006765398440006745398440006766558440006756558440006d66358440006d56358440006e66258440006e56258440006767558440006757558440006765358440006745358440006b64258440006b442584400047f76d44400047d76d44400065e63d44400065d63d44400066e62d44400066d62d4440
  | 7 => 0x87500067561887500067561487500047e76087500047d760875000675610875000e5e6394e50005757114e50005797014e500067561546500057571d4250004f67119150004f571191500063f6495150005767115150005757115150004be7418d50004bd7418d50004ee7218d50004ed7218d50004f67118d50004f57118d500047e76d4d5000e5c6394d500057a7094d500053e7414d500053d7414d500056e7214d500056d7214d50005767114d50005757114d500057a7014d50004f67118950004f571189500066f62949500057671149500057571149500067761545500067461545500047e76145500063f64991500057970991500056f72591500056c72591500057b7059150005767119150005757119150005797098d50005777158d50005747158d500057b7058d500053e7418d500053d7418d500056e7218d500056d7218d50005767118d50005757118d5000e3e7418d5000e3d7418d5000e6e7218d5000e6d7218d5000e767118d500047d7118d5000e757118d50004757118d5000e797018d500047e76d0d500047d76d0d500057671d0d500057571d0d500056e7290d500056d7290d500057a7090d50005797090d500047f7650d500047c7650d500057a7010d50005797010d500066f62989500057970989500053f74589500053c74589500057b70589500057671189500057571189500047e76109500047d76109500055e73109500055d73109500072d42109500057671109500057571109500057a70109500057970109500053e74cc9500053d74cc9500057a70cc9500057970cc9500047e768c9500047d768c95000576718c95000575718c9500047f764c9500047c764c9500057a700c95000579700c95000c7e73d85500057970985500055f73585500055c73585500057b70585500067561185500047e76905500047d76905500056e72905500056d72905500047e76105500047d761055000c7c76cc5500067761cc5500057a70cc5500057970cc5500047e768c5500047d768c5500065c638c5500047f764c5500047c764c5500047e760c5500047d760c5500053e740c5500053d740c55000e5c630c5500056e720c5500056d720c55000677610c5500057a700c55000579700c5500047e76885500047d76885500053e74885500053d74885500047e76085500047d76085500057671d81500057571d81500057973d81500077271d81500077171d81500067671994500067571994500047d7694c5000e5e6314c50005757114c50005797014c500067561d44500047f76544500057571d40500047f7654050004fb76540500067a6554050004f67119740004f57119740004ee7298f40004ed7298f400047f7558f400047c7558f40005757114f40005797014f40005b571d0f400047e75987400047d7598740004e
  | 8 => 0x6756588421004ef7648421007655148421004f776484210067565484210047e75980210047d75980210063e64d53500057671153500057571153500057a70153500053e7414f500053d7414f5000e5e6314f500056e7214f500056d7214f50005767114f50005757114f500066e62d4b50005767114b50005757114b500067653987500067453987500067675587500067754587500067654587500067554587500067454587500067753587500067653587500067553587500067453587500067752587500067652587500067552587500067452587500067561d47500067561947500067661547500067561147500056e72d93500056d72d93500057671d93500057571d93500057970d93500063f64993500057671193500057571193500057970193500057671d8f500057571d8f500057970d8f500047d7198f500053e7418f500053d7418f500056e7218f500056d7218f50005767118f50005757118f50005797018f500047e76d0f500047d76d0f500057671d0f500057571d0f500056e7290f500056d7290f500047f7650f500047c7650f500053e74d8b500053d74d8b500057671d8b500057571d8b500057970d8b500066f6298b50005767118b50005757118b50005797018b500047e7610b500047d7610b500055e7310b500055d7310b500072d4210b50005767110b50005757110b500057a7010b50005797010b500053e74ccb500053d74ccb500047e768cb500047d768cb5000576718cb5000575718cb500047f764cb500047c764cb500057970d875000676639875000674639875000c7c73587500067776587500067764587500067664587500067564587500067464587500067763587500067663587500067563587500067463587500067762587500067662587500067562587500067462587500067774587500067674587500067574587500067474587500067773587500067673587500067573587500067473587500067743587500067643587500067543587500067443587500067772587500067672587500067572587500067472587500067742587500067642587500067542587500067442587500067732587500067632587500067532587500067432587500067770587500067570587500067561187500057970187500067561d07500047e76907500047d76907500056e72907500056d72907500067561907500067561507500047e76107500047d761075000675611075000c7f76cc7500067561cc7500047e768c7500047d768c75000675618c7500047f764c7500047c764c75000675614c7500047e760c7500047d760c7500053e740c7500053d740c7500056e720c7500056d720c75000675610c7500057a700c75000579700c7500067561c87500047e76887500047d76887500053e74887500053d748
  | 9 => 0xd6410b21005cd7310b21005e97010b210047e75983210047d7598321004be74d9621004bd74d962100c7e73996210067671996210047d709962100c7c73596210047f7059621004be7419621004bd74196210047e75d92210047d75d92210063e65992210063d6599221006b671992210063e65592210063d65592210047e75192210047d75192210047e75d8e210047d75d8e21004be74d8e21004bd74d8e210047f7558e210047c7558e210047e7518e210047d7518e21004be7418e21004bd7418e21004fa7018e21004f97018e2100c7f7694e210047d7694e210063e6494e210063d6494e2100c7f7614e210047d7614e210063e6414e210063d6414e21005757114e21005797014e210063e64d46210063d64d4621006b564946210063e64546210063d6454621006766554621006b56454621005777654621006777654621006776454621007366454621006756454621007356454621006356454621005747354621006776354621006756354621005777054621005757590621006756590621006756550621006b664506210057775cc621006b564cc62100575750c621005b5740c621006b5640c621005f1700c621006ae64c86210047e75982210047d75982210067551982210047e75191210047d75191210047e75d8d210047d75d8d21004be7498d21004bd7498d210047f7558d210047c7558d21005757114d21005797014d21004ee76d0921006ad6410921005cd7310921005e67110921005e97010921005e6718c921004ec764c921005757594521004f47654521006777654521006747654521006776454521006756454521005747354521006776354521006756354521007677254521007647254521007674254521007644254521007663254521007653254521005777054521005757590521005e67290521004f47650521007a44250521004f676cc5210057775cc52100575750c521005b5740c521005e6720c521005f1700c521005ae74885210076551885210047e75181210047d7518121004be7418121004bd7418121004de7318121004dd73181210067551181210047d769942100c7e73994210047d709942100c7c73594210047f70594210047e7519421004f671194210047e75d90210047d75d9021004ee72d90210047e75190210047d7519021004de7319021004dd7319021004f67119021004fa7019021004f970190210047e75d8c210047d75d8c21004f671d8c210047f7558c210047c7558c210047e7518c210047d7518c21004be7418c21004bd7418c21004ee7218c21004fa7018c21004f97018c2100c7f7694c210047d7694c2100c7f7614c210047d7614c21005757114c21005797014c210047e75984210047d7598421004be7498421004bd74984210047d76d44210047f7654421006766154421
  | 10 => 0x9131004f571991310047f75591310047c75591310047e7694d310047e7614d31005797014d31004be74d8931004bd74d89310047e76d45310055e73d45310057575945310067465945310047c76545310055c7354531004f47654531005d4735453100677765453100574765453100674765453100474765453100677645453100675645453100757735453100d74735453100754735453100554735453100677625453100577705453100d7775cc53100755518c5310047e75181310047d7518131004be7418131004bd7418131004ee7218131004ed7218131006755118131004be74d9431004bd74d9431004ee72d9431004ed72d9431004fa70d9431004f970d94310047d769943100c7e73994310047d709943100c7c73594310047f70594310047e7519431004be7419431004bd7419431004ee7219431004ed7219431004f67119431004fa7019431004f970194310047e75d90310047d75d9031004ee72d9031004ed72d9031004fa70d9031004f970d9031004bd76990310063e65990310063d659903100e3e539903100e3c5399031006b671990310063e65590310063d655903100e3e535903100e3c53590310047e75190310047d7519031004be7419031004ee7219031004ed7219031004fa7019031004f9701903100c7f7598c3100c7c7598c310066e65988310066d6598831006ae6498831006ad649883100e6e539883100e6c5398831006e671988310066e65588310066d6558831006ae6458831006ad645883100e6e535883100e6c53588310047e75984310047d75984310047d76d44310063e64d44310063d64d44310066e62d44310066d62d44310047f76544310063e64544310063d64544310066e62544310066d6254431006766154431004f57690431006756590431005e57290431006e56290431006756550431006b66450431006e5625043100675658c431004df764c43100757514c431004f7764c43100675654c43100f54534c4310047e75980310047d75980310067a6598031006796598031006ba6498031006b96498031006ea6298031006e962980310067a759803100679759803100e7a539803100e7853980310067b51980310067951980310067a6558031006796558031006ba6458031006b96458031006ea6258031006e962580310067a755803100679755803100e7a535803100e7853580310067b5158031006795158031006f24158031006f14158031006db3158031006f23158031006d93158031006f13158031004de73d9721004dd73d97210047e75193210047d7519321004de7319321004dd7319321004fa7019321004f970193210047e75d8f210047d75d8f21004be7498f21004bd7498f210047f7558f210047c7558f2100e5e6314f210065d6314f21005757114f21005797014f21006a
  | 11 => 0x47f7059641004ee7219641004ed72196410047f7558e410047c7558e4100c7f7694e410047d7694e4100c7f7614e410047d7614e41005757114e41005797014e410066e6598a410066d6598a410066e5398a410066c5398a41006e67198a410066e6558a410066d6558a410066e5358a410066c5358a410066e62d46410066d62d4641006e562946410066e62546410066d6254641006766554641006e56254641005777654641006777654641005747354641006756354641007666254641006756254641007656254641006656254641005777054641006ae62d06410073551d06410047e75982410047d75982410067551982410047e75d8d410047d75d8d41005757114d41005797014d41005b671d0d410047e75189410047d75189410059d7310941005b67110941005b97010941005757594541004f47654541006777654541006747654541007377454541007347454541005747354541006776354541007374354541007354354541006776254541007364254541007344254541005777054541005ae72905410073551905410047e75181410047d7518141004de7318141004dd7318141004ee7218141004ed72181410067551181410047d769944100c7e73994410047d709944100c7c73594410047f70594410047e7519441004f671194410047f7558c410047c7558c4100c7f7694c410047d7694c4100c7f7614c410047d7614c41005757114c41005797014c410047e75984410047d75984410047d76d44410047f7654441006766154441006756590441004bf7650441007355150441004f776504410067565504410047e75980410047d759804100e5e73d973100e7571d97310047d70d9731004be7419731004bd7419731004ee7219731004ed7219731004fa7019731004f9701973100e3e741973100e3d741973100e5e731973100e6e721973100e6d721973100e75711973100e7a70197310047d701973100e797019731004797019731004ee72d9331004ed72d93310047e75993310047d75993310047f75593310047c75593310047e7598b310047d7598b310047f7558b310047c7558b3100d5e73d473100d5c7354731006776590731005e572907310067765507310047e75983310047d75983310047f75583310047c75583310067671996310047d70996310047f70596310047e75d92310047d75d9231004ee72d9231004ed72d92310047e75192310047d7519231005757114e31005797014e3100676655463100577765463100677765463100677645463100675645463100d74735463100675625463100577705463100d7775cc6310047e75982310047d75982310067551982310047d70d95310047e75995310047e76195310067571195310047d7019531004ee72d9131004ed72d91310047e75991310047d759
  | 12 => 0xe7214f510056d7214f510057a7014f51005797014f51005767114b510057571d93510063f64993510057571193510057571d8f510047d7098f510053e7418f510053d7418f510056e7218f510056d7218f51005757118f510057a7018f51005797018f510047e76d0f510047d76d0f510057671d0f510057571d0f510056e7290f510056d7290f510047f7650f510047c7650f510057571d8b51005757118b510047e7610b510047d7610b510055e7310b510055d7310b510072d4210b51005767110b51005757110b510057a7010b51005797010b510053e74ccb510053d74ccb510047e768cb510047d768cb5100576718cb5100575718cb510047f764cb510047c764cb5100c7c735835100e5e6394e51005757114e51005797014e510063f6495151005767195151005767115151004be7418d51004bd7418d51004ee7218d51004ed7218d51004fa7018d51004f97018d510047e76d4d5100e5c6394d51005767194d510053e7414d510053d7414d510056e7214d510056d7214d51005767114d510057a7014d51005797014d510057671949510057671149510063f64991510055e73991510055d7399151005757199151005777159151005757198d51005777158d510053e7418d510053d7418d510056e7218d510056d7218d510057a7018d51005797018d5100e3e7418d5100e3d7418d5100e6e7218d5100e6d7218d5100e757118d5100e7a7018d510047d7018d5100e797018d51004797018d510047e76d0d510047d76d0d510057671d0d510057571d0d5100e5c6390d510056e7290d510056d7290d51005767190d51005757190d510047f7650d510047c7650d510065c6350d51005767110d51005757110d510055e73989510055d73989510057571989510057771589510057671d09510057571d09510057671909510057571909510047e76109510047d76109510055e73109510055d73109510072d42109510057671109510057571109510057a70109510057970109510053e74cc9510053d74cc95100e5c63cc9510057671cc9510057571cc9510047e768c9510047d768c95100576718c95100575718c9510047f764c9510047c764c9510065c634c95100576710c95100575710c9510057574d85510057573d85510057572d85510057670d855100c7e73d81510055f73581510055c73581510047d7694c5100e5e6314c51005757114c51005797014c510047f7654451004f77654451006766554451004de73d9741004dd73d9741004ee7298f41004ed7298f410047f7558f410047c7558f4100e5e6314f410065d6314f41005757114f41005797014f410059d7310b41006ad6210b41005b97010b410047e75983410047d7598341004ee72d9641004ed72d964100c7e73996410067671996410047d709964100c7c7359641
  | 13 => 0x80420067a5398042006785398042006ad42580420067a6558042006796558042006da6358042006d96358042007a94258042006f26158042006f161580420067a75580420067975580420067a5358042006785358042006bb4358042006b94358042006bb4258042006ea4258042006b94258042006e94258042006a94258042004be74d9732004bd74d9732004be7419732004bd7419732004f67119732004f57119732004fa7019732004f970197320047e75993320047d7599332004f67199332004f571993320063e75993320063d75993320069e739933200e3e539933200e3c5399332006b67199332006b5719933200e3e535933200e3c53593320069e6450f320047e75987320047d75987320047e75983320047d7598332004f671d9632004f571d96320066e72996320047d71996320047d70996320047f71596320047f7059632004f67119632004f571196320047e75d92320047d75d9232004f671d9232004f571d92320047e75192320047d7519232004f67119232004f57119232004fa7019232004f97019232005757114e32005797014e320066e6554a320056d7510a32006ad6410a32005e57110a32005e97010a32005ae74cca3200f4e53cca320047e75986320047d7598632004be7498632004bd7498632006766598632006756598632006767598632006757598632006b67498632006b57498632006765398632006745398632006766558632006756558632006767558632006757558632006765358632006745358632006e74258632006e442586320047e75982320047d75982320047d71d95320047d70d95320047e7599532004f67119532004f571195320047e76195320057571195320066d72195320067671195320047d71195320067571195320047571195320047d70195320047e75991320047d7599132004f67199132004f571991320047f75591320047c75591320047e7694d320047e7614d32005757114d32005797014d32005ce7290d32004dc7650d320066c6594932004ec7654932004ee76d09320056d7510932006ad6410932005ce73109320078d4310932005e57110932005e97010932005ae74cc9320047e75185320047d75185320047e75181320047d7518132004be7418132004bd7418132004f67118132004f57118132004be7419432004bd7419432004ee7219432004f67119432004f57119432004fa7019432004f97019432004ee72d90320047e75190320047d7519032004de7319032004f67119032004f57119032004fa7019032004f97019032004be7498c32004bd7498c320047e75988320047d7598832004df764c832004ef764c8320047e75984320047d75984320047e75980320047d75980320063e64d53510057671153510053e7414f510053d7414f5100e5e6314f510056
  | 14 => 0x47e75990430047d7599043004bf7650c43004df7650c430047e75984430047d75984430047e75980430047d75980430063e64d53520053d7414f5200e5e6314f520056e7214f52005757114f52005797014f52004be7498e52004bd7498e5200e5e6394e520065d6394e520056d7294e520056d7214e52005757114e52005797014e52004f67119152004f5711915200e5c6394d520053d7414d520056e7214d52005757114d52005797014d5200e5e6314c52005757114c52005797014c520047f7654852004ef7654852006765398452006745398452006767558452006765358452006745358452006775258452006755258452004f67119742004f571197420047f7558f420047c7558f42005757114f42005797014f420047e75987420047d75987420047e75983420047d7598342004f67119642004f571196420047f7558e420047c7558e42005757114e42005797014e42005b571d0e420047e75986420047d75986420047e75982420047d7598242004f67119542004f571195420047e75d8d420047d75d8d42004f671d8d42004f571d8d42005757114d42005797014d420047e75185420047d75185420047e75181420047d7518142004de7318142004dd7318142004f67118142004f57118142004de73d9442004dd73d9442004f671d9442004f571d9442004fa70d9442004f970d94420047d769944200c7e73994420047d71994420047d709944200c7c73594420047f71594420047f70594420047e7519442004de7319442004dd7319442004f67119442004f57119442004fa7019442004f970194420065e6598c420065d6598c4200e5f7598c4200e5c7598c42006ce7298c420047f7558c420047c7558c420065e6558c420065d6558c420065f7558c420065c7558c4200c7f7694c420047d7694c4200e5e6394c420065d6394c4200c7f7614c420047d7614c4200e5e6314c420065d6314c42005757114c42005797014c420063d65d0c42005ad72d0c42005b571d0c420063d6550c420069e6350c42005ad7490842004bf7650842004ef7650842005af7650842006af76508420072e65508420072d6550842005af73508420078e63508420078d63508420072e53508420072c5350842005af7150842005ac70508420047e75984420047d7598442006766598442006756598442006d66398442006d56398442007a54298442006767598442006757598442006765398442006745398442006766558442006756558442006d66358442006d56358442007a54258442006767558442006757558442006765358442006745358442006b74358442006b543584420047e75980420047d75980420067a6598042006796598042006da6398042006d96398042007a94298042006f26198042006f161980420067a759804200679759
  | 15 => 0x4325845300677705845300676705845300675705845300674705845300e77305845300e74305845300675619805300d79769805300f3a649805300f39649805300e7a639805300f5a639805300f6a629805300f69629805300e7b619805300f72619805300679619805300f7161980530067161980530063e64580530063d64580530066e62580530066d625805300676615805300675615805300e7860580530047f715805300e7b305805300e78305805300d7b76580530067b765805300e7b64580530067a645805300f3a64580530063a645805300679645805300f39645805300639645805300e78645805300e7a635805300f5a635805300e7b62580530067a625805300f6a62580530066a625805300679625805300f69625805300669625805300e78625805300e7b61580530067a615805300f72615805300672615805300679615805300f71615805300671615805300e7861580530067b74580530067a745805300679745805300678745805300e7a735805300e7a435805300e7843580530067b72580530067a725805300679725805300678725805300e7b325805300e7832580530067b71580530067a715805300679715805300678715805300e7b315805300e783158053004f671d9743004f571d97430063e74997430047d71997430047d70997430047f71597430047f7059743004f67119743004f571197430063e65953430063e6555343005757114f43005797014f430047e75987430047d7598743004ee7298743004ed7298743006766598743006756598743006767598743006757598743006765398743006745398743006e67298743006e572987430067665587430067565587430067675587430067575587430067653587430067453587430047e75983430047d7598343004ee72d9643004ed72d9643004ee7219643004ed7219643004f67119643004f57119643004fa7019643004f9701964300f1e53d0e430047e7598a430047d7598a43004f67198a43004f57198a430066e7598a430066d7598a4300e6e5398a4300e6c5398a43006af4398a43006e67198a43006e57198a4300e6e5358a4300e6c5358a430047e75986430047d75986430047e75982430047d75982430047d71d95430047d70d95430047e7599543004f67119543004f571195430047e76195430057571195430063d74195430067671195430047d71195430067571195430047571195430047d70195430063c6595143004bc76551430047e7694d430047e7614d43005757114d43005797014d43005ae7290d430047e75185430047d75185430047e75181430047d7518143004ee7218143004ed7218143004f67118143004f57118143004be7419443004ee7219443004ed7219443004f67119443004f57119443004fa7019443004f97019443
  | 16 => 0x89540063e65950540047f7655054004bf7655054006767558454006775458454006755458454004f67199253004f571992530063d649525300d5e73952530055d739525300d5c7355253005767115253005757115253004f67198a53004f57198a53004f77158253004f4715825300576719925300575719925300e3c6459253005767198a53005757198a5300e6c6258a5300e77619865300e77315865300e7431586530047f705865300e7b60982530057771582530057471582530047f715825300677715825300477715825300674715825300e7b305825300e7830582530063e64d505300d5e73d50530063d64950530063e645505300d5e73150530057671150530057571150530047f7654c53004df7654c53006ae6498853006ad6498853006ae6458853006ad64588530066f54588530066d5458853006b66498453006b56498453006e66298453006e56298453006b66458453006b56458453006e66258453006e56258453006767558453006775458453006765458453006755458453006745458453006775358453006755358453006ba6498053006b96498053006ea6298053006e96298053006f26198053006f16198053006ba6458053006b96458053006ea6258053006e96258053006f26158053006f161580530067a75580530067b54580530067a54580530067954580530067854580530067b535805300679535805300e3f649905300d3d769905300e3e639905300e3f619905300e3f609905300d3f76590530063f765905300e3e635905300e3f625905300e3f615905300e3f605905300e5e7398c5300f1e6498c5300f1d6498c5300e6f629885300d6d769885300f2e649885300f2d649885300e6e639885300f4e639885300e6f619885300e6f60988530063d645885300d6f76588530066f765885300e6f645885300f2e64588530066d645885300f2d64588530062d645885300e6e635885300f4e635885300e6f615885300e6f605885300d75769845300f36649845300f35649845300e76639845300f56639845300f66629845300f65629845300e7760984530063e64584530063d64584530066e62584530066d625845300e74615845300e77315845300e7431584530047f705845300d77765845300677765845300e77645845300676645845300f36645845300636645845300675645845300f35645845300635645845300e74645845300e76635845300f56635845300e77625845300676625845300f66625845300666625845300675625845300f65625845300665625845300e74625845300e77605845300e74605845300677745845300676745845300675745845300674745845300e76735845300e76435845300e74435845300677725845300676725845300675725845300674725845300e77325845300e7
  | 17 => 0x200100000101701400000000400000000000300900300100501100400701700f00301b00200800000501d00400000201000401801e00000500000b00600100c00200501403e02f00000e01500500000400000100001001100000b01900301000000401800000200300000501c00a01400900001500100001800f00300301c00100500800005500b01600400500600001e00200000e00f00200600e00100000100100200500700600600900600000001b00d00000000a00203701700b00600400600300200700200400700000e00900100b00600600d00000a00200100301b00800200001d00801c00000100b00004400300a00000b00700300100001b01100000b00300500d00100000300b06300501000d00d00700000d00700000a00203705100000700001900100f00001600000200400100501a00000c06100b00002500300000100000401f00001c00000801900401300600702300501304900600100100000000500300000100301400300001000100e00600300000a00600000100300200002b00d00102b00000000100700201000700500100b00601300e00400c00400700000000402800300400000400400100e01802900202100100100300700100f00400000600d00000100100000300500300e00a00200400100101f00000301000000102100a00200300102600100101301b01600200000000100000200202100000901200301207300200101e00300900100701401801500d00f01900e00000100300100f01000400201700e03e00e00300000000000000901200400c00800000000703900000000100800400700300300101300000200000400600202800c01700100e00100000100001000300000000400200200900000600700300600600000000000600100b01900a00001000700900100e00000c01300000100700000600000700200300000001600200900200401400300000100403f00b00400400100000500001c00500700100000400006900002200000100100000700600000900300000c00001103c01400900100d00100001100000000600e00500600300000000100400700b00000000000401301900100401300600300100002803700704600000100f00300100701900500000000101700100a00700b01c00b01500000000c01200000100300000700000503100000500500100700a00600000300001900100c04100300000000d00200300800401100900900200700200200d00d00a01100000e00e00000500200000000000000000400200a00600300000c00b01500000100500000000b00d00100300d00000100300400c00d00600100001000000100100a00202c00500004900000200303002701c00f0020070070030000000053d76d52540063d76d5254004ee7298e54004ed7298e54004f67118954004f5711
  | 18 => 0xc3e4000000001650b482479eac000aac39f80b80ae6ec19525481729e2186260c58a81d360a86c000a42127a3b48ae15053780010d80b61750144e3c12a4c9957540a4ac3540ffc78201719492ecefc30f303a79941800d118991092288e585856c73691a3740ea825827f2ec28241de75214096151b83710c700002d24b1104811943455c4ca900504a86d43801c561c9c34ef89a944200044998fcd524825099eb49400003320da81986342038fe8d426050000000f000000001d10f14a1c0000a940004701d800181e669200000012be37042aa99d1485b536c23295ae19c21d09040002f5000000000011d1ae000000044d3e6297137e4f71e193e400010b33ca10000000905b8000af023c28512a53100000000ac83a8592296000003092744b800000073b30b1b4d496ada137800066a97234b8b355424040000ed0f421ea3f08500fba01312aa9740007ec00005bcf4600000029d4a0eb5351a22d40000000b70000e420a456a0000a80aaf0002270faa2df00001940006af45e1fc02f429c2361f6d2600212f180000005600688d452fc0004aa090caac46224800752dc4664e715b525c9744b29fad6287f3000125c4465412cca1ac1789f73ed0768e0847d01ca4ac2489171cc9cf0102a550759cb0c48298072958c5bc00040d0554f0e00017e0b092c81bb512992c27c0001c60d5000035624680000000004fd800114e6cf3cbad60b9600003105f4e9c3cd00015680aa9db14d8000616a3d21a97a54586d44bd2ab800000048d800016401e00700701500100900200500a01c00100001900a00400c00601100900e00201b00500500e00000800101800000400201200700000000000000000801b01700000000300300e00100200902400b01e05b00600100300300100200200100800000902e00e00600100b01f00200201303f00300b00200500200002800301f00200c00300000000000100000901700e00f00001500e00501b00b00100900402100200200300500b04c00001b02000200300800300600100100400500100202100600b01500102000600100000100600600000700000200700700200002600001500300102000500400200200d01202100400300201c01100000d02700800100000000302800300200000500800700001100000401000300501500300101200100100001900000800b00000f02200600700400c00300000102b01b00f00000000100100200000401400b00200703900000000000200700002100400500100300001900003e00000400000d00c00801400c00700000400600000300100500304500900400500000100000c00300100801000000003400700300b00500000300000000800b00900500e01c00001302e00100300300200e00400300600000100100d000001016000000000001001018005005
  | 19 => 0x2e50d842fc0d0503a528ec2adb134971d5e21ce2e8abb130073908d91103e69b02210430cdc8992ed2d0d0024683279324b209532a7994486c1952eba06031663534c23301000bb33b2a403660004d3038143c5a3486a978f74b4d51ca9a8970a590d59bcc5789b457b89853825c633ea268184000490a2a02560003f2133111e00007813b87aa12049784eceb483139480010fa00009e2c4c0003741158c046de2a800007648b00c44db991d07083608411a54645642b58b553a0a3102d80006905b026c9ecc51e3fd073a524e863a54aa9a1041824a0d7aaf446ea363229040f3c07b3921b103423af54c17587ea00029c9a2c23028512c15fd5ba00031f00000001f841417bc5e60002fba83c7f87602e114f4a46aed24d060c000650051a35400000019b1338a0091d0002b10746adf4be885c6ce1290002c0122a02b16c99b01103ee3a61e68340b220fc83d40e432102491e066038151c1ed4a7c23d26c195959aa7d04fa4604dc2f10000ba000003e23e000064a0000e61ed959e06101680015c045132f80000006ae41a26a0b3c0003a6800000074f000000044e0000001b08a9c00014f800169645c0001e040001aa000000000000000009f800045a54200015802fd1f5162c00008b4ec08b8c300004cba9d029c56c4018dccc042763c32124e1e47747391fcda40b11c39ba4472ab35300cfc136ab443301ac32c9de30e9fb884426d50ca97d3f40de0e5aa8c0003b731e0d7cde86aa0e526acafc7ea17c0281166386131800086e00037b9a88d58202388153400013410e1d180ee5fe56503d8f4453f5a91ec524c67f55d019d27c0001f5a3f155608612f8d0504e3e54ba800100e1715400c9d0987400001b8d24887200018801f46b347200008fc8d13d70ef50ec4e11e216c4c5828b02596a4b5640b442a254bda20054586350ee32f06c115479625c43aab88420496020154d45646519312f946a3d01a794640ec6ab2420ae14ca3312290f315140a70480cf081203844c000141a0a653d0000cfc01b3a8177d67c7013fb91d0e0e175000000000034b000000000000000000000000003c604107c65b950a800077420e25c89e44bab0f0001f2c5b02420ae13f8cf69be03c1ce80000420e99cc80007fe4de0000bf856700014800001350001ad8ceea0a36527147e684801899c40002263ae9c481b275c42dab54a4a528092a68088a53837b0f08a8e57318a949cdc2725588162510039048a1484e5ab3f56c16740000004c29b54bb8a005460000542b34000099c0005b4340a0ccb9000013d00014f0503135800000082b1fa0000c100e60e2256c4ca9311778c64dc849217326404100000619f8800000033400016380051bf92fc1ae2aa00007884e001f00019d12a000000000000006c53472b64000b0538300013ca0fe0001d20
  | 20 => 0xcc410327e9b811a82f223a87980008ec0909ae43d85e742e22f54d20004e4064164600043d94880006b13ef0000e4652b00000010d046e47593c0fe83240001b5953281b0ff97891fa000000000105a0004cc15e870a00000000c07520000001c6800078b4a410c4ef447b31d93085c65ac3c1863cb6e5351561a9898e1e90d60c48a0c75b3d3a95c000aef563858435a1eb00025688c614a0002998f480004c780006aaaee221a34c0004984e3a47c0dc0001900560b1c1d61121058c0004c27d827059678259aa3e469aa761a29f243ba2a63461c8169c93d0001ddcb9c7172dd917820c73d04d069d1e66993688c08c7a9a33250000abc4a20001bd400051600007540000000ba0b0051070a2182ce800000055397c4a1c268098a8f8a6849f54380012b061237ca150a64000146800082290c0002cb48be5090001810f2400000000007423172f9a5b1160b2700d024c0828881f884993768512d108505a6518219a2184f060b3978f7482e4cb42b80d455c6153bb000033a5573bca16043400044e825027e36242b021506a1644b423140006db530866471600048f2110dbc08c00020009ea69018e800000000000028a000005312994400140000be03393ea0004ee800139e0001da8000168a922aa86483dc000207110400000000000000006950000000c9c6484dd1608f523a632aa9b83c24082d91ac153698d2fc18b94409361400b105c48e23c4a6489ac1fa0598d093669f305093915c83051178020c3c66f24d9edc00e515230047c39a48019f18240009d4099907806c2b50418f6556a4bd000066d28645400001c08781ba3fea03880ca401bba80475c00e32a13c934445b10f16cc0003b94d906c80000bf520a1e4000b1e48423a4f4c27c2a41b709fe82c1b7111cbe06064d3aaa4d14b3824a97d4246000000096933400007d99950522661e280012049f24c62b988ba0004da80006f2a500c126511360000e01db4c5019a5888d9400043e35688c163e3b600008185724fa59d92f0ca66210000e500481c516b956c000000000000000021b4088720000acc12715d4002060365a81121200c5950000cdaae80000178de00004eb80000009e1000000000000000008816a8000000000009e00000025086500aa481947120c0000e112851566dd27480012c606445c04650328e600000004e65793ac84e12ae9f00152b8c9a264934499007e4a0b2859ed0f7090006a0324d70ae9320961ca741654f60000076187000000000015a39ba304756941239813404a9a14fc248caf67a038e9264e501304822b3916c40f0478bd93c056a28f874402446f55babac42c3693732ac03f60ec3fc9bb50dc1103f02bd000000040a85c048c53b32e800d214726346a4b47d25041881f58790b0658e85640a01b04cf977538c28e37f85447d82cf
  | 21 => 0x7000000026400452780004585460290d247a435a11d8db420448e1c7110168c4c43be873d08e5eb22780000003a24fca9dcd460a245623bd21e6a745f1124804a0e03509d0fb23534108a4c2ec61700006d08f48f755f27090267e706d19312d65080b38248ef81892921a505d848615ba7a4cc002203e95287ae5434e013741e4b5047b088544e2a32af83586a45e816e8e011be05d19d1c7cd0432e5a38690cf854c4cf1fbca9221926788e8f5eac52a20c5086818c1d6aaa000071452a06f4c22a4527e0da105e9dc0e305c8be844c53914a496e2d600007240000000000d280000000838000c5239753f1dcd0c22920ae8f68000b4930d00000008605369af130413d191979813a0342b726f542e31c2ec96a8e2a0ba0000efc00061042500009540002321c6517481053121cd2f239534daad80000002602a14ba46cd00025649d652a26fa0b85a0a1831106e4b1a28651f9f7d0de29d07a000038e8a94c09ca91443962e2800000061c2a91fe8d681a252d0e240002964e9800000027100000000005af0000a24cea21536720700003b83c7922c5fcaf81229b40d0620f3dc818c9b61b752702f530883d4690d3930c55814206603b89a947a124d66200008e017c6c80004ceaaeced861309422dc0000002d21014ece64610513c400069f4870ba43e02da35babcc956000000253c54851d0000f8965672b1708a412ac5761cea8f000076601eaa5079c00048280000003b31451204e220003eb94480001970160d80b4c87f59022e44a844e2b4100c3ec5d018d0eb0bbc52e00013b46fa51e0138c587f00000000000f54b4449a93bc3b01e4000198426c5ad53d9d94a2884e26f0000e7ca9525b075d2444a72b123fd2c479431b23c8ba6b0c126877c71e892315a3a812e0a82be8fdc5445311ac853c0000f142f8525554251000000071aa3343296f8f0a1f135a92e87fc75f000160008a6e741010f426e1e323b08d07f23373989af40285ec3bd80008da3e10a10000dfc4d32e6000003c77005487a0562b253a4831c0009ae40914980004485588eecf8e25e0c213d0e822523862b9d4c800000011180001a63bf80000007694890000b9e0001bf000000000059eac8443a00000000cc30a53c1a327687a800005721400007a800003e53c82ab3c697555f4000000000094600000003200f45a702ca134b8000012400000004f857928b918e3c946d24e00e800053584b55faa2a00025740004323a511a806e9713cf996c00087c54992cd0f45953870ce11807934468cac2c47425a5000165ea4a199a44527e566512233cebc4c50721cd420a82400010810bc0482451c6c3b68141cf24dc0004e63268d110baafc4e59a44d002f752686b915c00000000010b200011489000007c13f400003fc8622cd00013c683b00000800b001637799c
  | 22 => 0x200006fa406ab2109ead331d00002445c139c07c86805db3f68000000853148ac6151e0003c20e0859094c4789a780005e43f19274626af019ea5c07b82eb443aac837017f0330c608349ef40b8e0c0948c444fad6911891c30caab498c97822507b4a1e256538a4e4b3e22d000098007e7d40190e4cbdc98721706a496068f5aaa020a6000000004340007345118af800060f000050cd928222dd0001102af654424b019e00055f8000a5e5c42b884682f093446ba3194040c60000d6000087e54e000046a6fd274202812c0005818d5cb1e0002b9000122c0002c18becea69402a10444eb0ae11cc06a015ea141bd8c18b186732ea17a83ce7d35168c7c000ad153603b827481f3b412a08f236b18f23b82d610a34b000149298e48384051146691058c247486392dc21914fe3be167130c2008b11e78d7878c10f0471bac6f83d852da644bc296000e2724cce0e32c32b18a260294808000000a2f000164c4b660302183555d4b2c3de1aec0006014ce27ac1708fe59b0f9cffe00050fa5782984ad44a25a800020316091c96ac5f20fe9f14f801f7119a29827200000020e40004c805610e4c6200052997d8000000000000108c89155280006ba0b0509034ccb2af50002a587cc00015380014e07622f28e488386be5a0a9a13140003661dd4470a8602b0294e009d206e080464401100003fc7d00003ce1e213d42590c403f000039100016b891063221290e146e89e46ca2593b25a14218cb0c5a30055e2a98ef08d01f018355ca74532b8110300b57399a3e92960ad0000000000b260001b000eaa8e238a90d36c83a0c9a3c0cf05bd0000000fcc7cd0000000b144134b380000002750421db9312a46583a74494a00038688484d815e3e781fcfd22c91c515bca221e015794cc6a09e84d5055885641d14a032c53412e32c1f94ddc0001968bb45f4b4043499e84fa0004fe98514f83035a880000047512c40000eaea3057c8000ee869a26d000000004e00002640000000c300000000005130d8ca6e65255c00003787bb3b598bd2c22cc2968c10b2cade18892c919c1a35980548000705511092400023627180009d8a5849000014065ff3d817f45fe1151b924e92b80e20b529215820000979b0c00059c000023400043b54d00013ac88905f0000a0a97c3e71fc8ede5e0000092c0007712ba2c5c5c80001599bec0000000002b0928eb5912b92787109b10000000d405a52fc8cc85a23391b61da845097b0a5914078e00010c00003bc5845a29c891bc6fc154a958e967c21cd1a741ba14856581b468e3e43d92c90aa2a814c598cc00021348ca6e0e129ad25a8740c1c6f1471800058692a210a874000a444a208340001ef000121ce8e4ea36b91591f08aa5822108b363d600006d40001411e99eb137259741313542d07fb15d23755040f
  | 23 => 0x66867215b0150f9481e1320208f8c2770ca2c049ce80538115a529a65a1842b0c36c69c56b25d966e71611fa3353aa88428d036c4e43c0457952c2e69103e1a9ccb8680928da6912164292fd0af458e1441fd99ac5a80000b1abf837e0002358dd80e6a060a2a4a51ca00045dac48e067fc2de13411462f44f88001422b2e00027d01da9f622c80007bc5a00079b9485e756055906d4986bf36380002120000002728eaaac9005808c18a517541a4ed4761c34b7a19c00016c3ee06f907e1b12ac8e700006633181a9124a565112855c2f20150bd8000b2257c093845161a42645098dc53c554074a4ccfa243f0a38b6c5f288b1e89f48df008758a898843e3f621201a0114aff12209ecb02afb013069508a5024b4a8411903b10000940ae000000000000000983e808c904668820c1e5819450d00000015127911d0236c33c97f2a2907c0006ea50412983f809e20915dc5400102db120c5a419148983a8c7042c4cd96505dc799233aa446b67be0899ef400006c46b0a5c0000e8474135c0f2205000000000042a1ed8478b5016d1438000cb82ad0e900004548c33128001604000257800117eb4c59c80015725360001fd840879d1efa7f8a024d404a92d00004ca1a1a0dcc8460c3e21e4098284b000053421c0004d78a6507c39f47aacf00006d958d0170e604142cc186cac25bf06001f83024e04d61828f4a0b5431a03c2cc65e15d9fe10d437a00007050f0a295290c3953c2c600000016840004701a9548e0000000000aa000024612b91048c95a79a180000000141fd41226df53c80e963618a46c1a14c4c93c51d0dd54c6623266925118480215a1b68e6c4893351c4c5601770aa00015b8841000251400000038400012a2a9f070ac24c5400025207d00000000f2800022428340b20305e07544b69a4c1123a742d2944d745c91de1c708c24f312380007947f120a80000009963cc0afc0002e7585000139a00014123ecec80002138000f2a5fb0002a9119600000000000004853b9057d34ab324fe1b191648063330000e5c0000000000d6400008b0ea11200004f703484226430fa9d8d3886271f7aa88832000000266484619f4f38000e309664528cecf904e554b854c000307405a4c80f82ca0000a540008710001b21140000000037c4449ed45a000051814600010b45caa9d186a5dc0003ed22583e0de434c58c80f12e60000001030f7e6e24a727fc5b800000027309a449c594937000001940220c91c23f05469f609c492850b000115aad2415173507806f41800000004f62299e38636aa0000000000040a00001a4f360000178e101fa0c11bc25190e8b333438000e1616002d2c5840ead0000214819a0000001c9c47c117000000076430a126000081a0000000b806cc4280239430000000441ac
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xca87650940480010eb023aac610002956047558c200043bc32e22984000c36645c4530800186ac8b88a6100071598d7114c200062ab1ae22984000c3a645c05308001872c8b80a6100071698d7014c200062cb1ae02984000ca9645c04208001992c6b8084100021d61c539842000538c00a730840008758714d61080014e30029ac210002b860042584200061b322e3a804000c35645c750080018acc6b8ea0100031558d71d40200043ac3cc3a8040008758758750080011590eb224010003231d16348020006523a2c2900400187b865c053c40018cacab9483880069520d654c7100061ab2ae910e2001877865c453840014cf04b22a3080021d6187354610004b8c00e6a8c2000c5473d8d518400146f08b12a308002d420d518c210004b843aa29842001c1e841cd654400383b0839aca8800713a08735951000e26c10e6b2a2001c55811cd65440038b30039aca88003151cf71595100043ac0cebb222000875819d763440010ef02bb4a68800315d8d7114d100062db1ae029a2000875819d762440014a906b2c82880031959572905100052a41acaa0a20008778759631440034a906b2c62880061d21d654c51000d2a41aca98a2000a5483596214400186acaba442880029520d654851000c2e41aeca822001a588359630440030f10eb2a608800394595314c1100052a41acb0822000a55851c563040030eb02bb0a6080061e6017614c100061b322e22982000c35645c453040038acc6b88a6080031558d7114c100061d322e02982000c39645c053040038b4c6b80a6080031658d7014c1000532c08a73102000a698014e62040014cb0229ac4080029a60053588100052ac1ec8a882000a6582d91510400146b0d322a2080030ddd964544100061ab20e6a882000971801cd510400146b09b1aa2080029960b63544100052ac34c6a882000e156498d51040010e90eb1aa208003151cd63544100062bbb2c6a882000e166458d5104001c2ac8b1aa2080031521d63544100051ac26c4a882000a5583d8951040014cb0d312a20800389592625441000722b1cc4a882000c67765895104001c4cc8b12a2080038959162544100072331ac4a882000e456358951040018c8e6b12a2080030d59370544100062ab1ee0a882000c6562dc151040010eb0dbae62080030ddd564cc4100062bbaac79882000c677558b310400186aeab206208003155d5630c41000632baac41882000cb1645c031040019a2c6b80620800338589700c4100043ac0aeda802000c36645c7500400186ac8b8ea0080031598d71d40100062ab1ae3a802000c66625c750040018cac4b8ea0080030d5d564c40100062abaac78802000c657558b1004001ca2c6a8c20080021de197544010004aa41aea8802000c357559110040018aaeab1a2008003195d56244010
  | 1 => 0xd06212c3a80029560c425875000712a1084b0ea000a728010961d40014e300212c3a80028da1332587500051ac2664b0ea000876878c961d40010eb0f192c3a800295e0d70587500052a41ae0b0ea000c667258641d40018cae4b0c83a80069520d614c7500061b3a2c218ea000c357458431d40018cce4b0863a8003195c9610c75000638b0ce018ea000c71615c031d400186ce8b0c43a80030d5d1618875000e2b982e231aa001c72305c463540038e260b88c6a80021d6047650d5000694a12e0212a000875811d932540014a906b08c2a800295604638c55000e2c31ae018aa000c73615c031540038acc6b88a6280021d6047558f4000532c14c2a8e8000877815da53900030b906bb2a3200021d60675d8d4000532c08a7b128000a698014f625000189aeab98c4a00021b61c531894000532c08a63128000a698014c625000154b03a18c4a0003315cd711894000664b9ae03128000ce1715c06250001c48c4a8a82a000319d8971d414000632312e3a828000875811d563100014ab023aac6200021de197114c4000e2b31ae22988000c55635c453100038b4c6b80a6200031658d7014c4000532c08a73108000a698014e62100014cb0229ac4200029a60053588400064cb1ae021080008758714e61100014e30029cc2200021d61c535844000538c00a6b088000ab18010961100018acc6b8ea0200031558d71d404000633312e3a808000c65625c750100010eb0f30ea0200021d61d61d404000646b18e4a008000ca47258540100010eb023aac9980021d6047558b3000d2a432a298e6000c71719c2658c0010eb033aec918002566007354630004b8c0eeca846000a71801d7614c0010ed0e29ec2980030d5d5741853000632baae430a6000ca5745c8614c001962e8b80c298003385c970185300051ac20c2a8a6000a6582185514c0014a90ca8a62980021d21971d41300043ac38c3a826000955811cd504c0018a8e630aa098002c66107354130005a4c10e6a826000b51811cd504c0016930521aa098002c66133254130006383b6c2a826000c7076185504c001aa6e398aa0980069520d755843000e0e39ac8a886001c4c73589510c0038a8e6b0aa2180030d99171d40300061ab22e3a806000c66625c7500c0018cac4b8ea0180021d61e61d40300043ac3ac3a806000875811d563c800146b0930aa3900021d60675d92200043ac0cebb1c4000877815da5388001956c8b8085100061720d7654620004d543e84a044000c1d755cc644800192ae6b88c890003265cd701912000654b92e03224000cb1715c064480010eb033aec6900020f61c6414d200061bb22e229a4000c34645c45348001876c8b80a6900030e1917014d2000652322e31924000e2464545214800186ec8b8ea0900030d19171d412000555434852024000
  | 2 => 0xd7114f4100e2d31ae029e8200c59635c053d0401952c4b8085a0802996045398a4100534c00a73148200a658114d62904014d30029ac5208025c60073546410043a43ac6a8c8200c547358d51904018c8e6b12a3208031958b7054641004b8c00e6a8a820093687d0d5150401a28e6a1aa2a08024da1c42545410058ac1884a8a8200b31801095150401a4ce4a8c82a0803155cd511814100632b92a23028200c377654541104018cecab9483988029960b645463100ea818ae029a6200959801cd514c4013a30039aa2988029960b64545310043a43ac8a8a6200b51801cd514c4012ad0c39aa29880715a18735453100e8b420e6a8a6201d15841cd514c4018aec839aa29880315590735453100ea3410e6a8a6201d45821cd514c403aa50039aa29880255600735453100ea8c00e6a8a6200951801cd514c40146b09b12a298803151cf62545310043b436e0a8a6200c3574544604c4014a906a88c098803195c9511813100632b2ae52086200a5586d45310c4034a906b2a62188069620d755803100570c1482b006200e53514c5600c403ca0a698ac0188071598d7114f210062ab1ae229e4201c5a635c053c84018b2c6b80a7908032a5917010b210061b322e229c4200c35645c45388401874c8b80a7108030e5917014e210061ab20e6a8c4200971801cd518840146b09b1aa3108021d21d63546210062a39ac6a8c4200c3564dc1518840186eeab2663108030d5d5640c62100658b22e018c4200ca9645c042484012e30039aa2908021d21d63545210062a39ac6a8a4200a6686d0951484012cd0e212a290803895904254521005a2c1884a8a4200b618010951484012cd0f192a290803511cd3254521005c2c1884a0a4200ba1801094148401a4ce8a8c42908030d5d151181210062ab9aa23024200a358498551084010eb0d388a9a80021d61a7114f500043ac34e2296a0008758714e61d400146d0829ac3a80028d610535875000533410a6b0ea000a658214d61d40010eb033b687a80021d61a71d0f500043ac08eca1ea000875819d842d40010eb0d38885a80034a5097010b500043ac0ced196a000875869c632d40010eb023b265a80029c600639875000533416c8b0ea000a6582d9161d40010ed0fb1ac3a80028da1063587500051ac20c6b0ea000a668218d61d40014cb0431ac3a80029c60063587500051b426c4b0ea000a3584d8961d40014cd05ba2c3a80029960b74587500052b41ce8b0ea000a55839d161d400146d0839ac3a80028d61073587500062ab98e6b0ea000a66821cd61d40014cb0439ac3a80029c60073587500043b43e86b0ea00087587d0d61d40014cd0521ac3a80029960a43587500051b426e4b0ea000a3584dc961d40014ad07392c3a80029560e72587500043b43884b0ea0008758710961d40014a
  | 3 => 0xab00a600a71819d56014c034b5062a2c0298029ca04545805300538c08a8b00a600a6682dd16114c014cb05ba2c22980695a0e74584530051b426e4b08a600a3584dc96114c034ad07392c2298069520d70584530051b420e0b08a600a35841c16114c034ad06382c22980299a08705845300532c10e0b08a600a6b825d16014c014d104ba2c02980696a0c745805300535410e8b00a600a69821d16014c014e5023a2c0298029c60474580530051dc22e4b00a600a38845c96014c0147508392c0298028e610725805300d2d418e4b00a600a72811c96014c014e302392c0298069620d71580530051d420e2b00a600a39841c56014c034b50638ac0298029aa08715805300534c10e2b00a60087581dc165d0c014e30029cc3a1803195d5729874300538c00a6b0e8600875819d660d0c010eb033acc1218021de0570d95430061aba2e232a8600875819da5350c010eb033acc0218071698d7014c520043ac38a7308a400a718014e61148014e30029ac2290021d6047558f420043ac0ceb3068400875811d563908010eb033acc1210021d60770594420043ac08eab188400879801d563108014ab023aac621002966007558c420043bc32e22988401c56635c453108018aac6b88a6210021ee197014c4200e2d31ae02988400c59635c0531080185eecb2a842100269607735084200706b2ac6a108400a2d8614d421080164b0229a8421002ca6005350842004c6c18e0a1084009a5811c142108010eb0e29cc2210029c600539844200742b1a84b0884008758714d61108014e30029ac2210021d606759804200538c0ceb30084008798714e60108014e30229cc021002aa20142580420071532a84b008400e29655096010801d14c6a12c021003a258d425804200750a14c2b008400ea14258560108014e3033aac0210021e61c535804200538c08a6b008400aa982d0d601080156303a1ac021002aa21d4258042007153aa84b008400e2975509601080155706a12c0210038a94d42580420071429a84b008400aab8150960108010eb033acc1990021d607705963200654b22e02146400c35755d2618c8014e30029cc3190029c600535863200570c0084b0c6400875819d6608c8010ef02b86ca99003195c971195320043ac08eab226400875819da534c801a1aeaa1884990036150d711093200654b22e02126400d89435c0424c8010eb033acc0190034a5097010b5100e2a31ae331aa201c5a435c063544038b664b80c6a88031ce057018d510063840ae031aa201c5b315c063544038e462b80c6a88071c4c57018d51004b2c14e3a1aa201c4c635ca43544038a8c6b8c86a8802966006350d5100694a12e0212a201c1c635d332544038a8c6b8e64a88024d612718c9510052cc00c6992a201c5a635c053144038acc6b88a7a08031558
  | 4 => 0x4e00052400010392001048b800030000106178334000831f2230a08cb0480009aa040000010507200000000000000000000000002144690215c00000225300000651b141a0000e9ed00017c768000006ac580461b40000000000000000000104000001d70000000000029e51c000002c20d1070732c8000000c8000000a880037c2ec0019600000000000000000e08003900d8002080000000017d27003cf88001de764000000000003f80040a000d690e2f838cb80003b605c338004480005f8810002640002f00000000007442000f50000b0000000001387dc27a2b0ea83c0a0000000010c000000000000c61e8130508001b2000ab0000f20009280000000005000000000001e7000000000000000000000012c0000000002c000e80230000011190045e1241287d3763b814000334018000ba26c0000017b02673c001760fc80c00000000324000000c068cc78370ae1c0869861584b0c805e1720000011f29c00000000208760000922ce0ac9194c1f8000dc8000f000000000000000000000007a46c00d0000008a8930001a84712f2fc60444000000000000003ea8081912d1a80a4740550de3b0992150005fc0000039a4dc181683a830c0004a0003fc00000452000000003325d4000000008441117905c478000cc0a6308001c63942d0910000002610c80e2146b8229130a44a04b9653ac000480000006888d80000025075a120400a87c0003b8158ca0be1aa2d45790b3522440000000000000192386000db00022c7e4ad8000a8870420000ca2cc00000000000001ce000638b31843e6000000000000c41d80000000037000000000000002d600068000000000000000000000002100000000000000001130001d21ecfb0000000005300008802cfa0f500078c000000cc588000ea3505c8000000002800005d0004c0841fd318000001e632a4304da2e3e0000001c00000004000c23800000000354768000002f04a4e600040e000288001e60010b9a027a274b61ee08411c000000000e84d1cb0900240017700000002002028000000400002008080000200000000040080800800020000600802800010060100e0300002002018000080000018000020380c000100000a04800000040101201010000020100e02800000100000800000000000000201000008000380a000000000200000000020300201000000060000201802000000280401802000020001200002000040200000002010040000c000000080000802000000000400812000000000a010000100a008000000602802018020100001802088060080a00808000020180002800000040580000800030020000000006000040000600000020060100200008000021d61a711505300f0729ac8b10a601e1a535916014c03c94a6b12c0298079494d61580530053940ce
  | 5 => 0x82ccb800000000000d623a000000000007fc000001ec000c281e3fc000710001ca00000059000540341330005809d9fa220000000000004fc5200045a00000000000578a201f000000df8952680000004b086794ce0001467a0001df00000000148000304780d10001f0ee8003a2000ad19e00023d001eb07c7100008a0d8880c49f82e2818269b7112000de8a225454838800000000000000da1a515000000534000003225b4000000005bc0000043a674908c415055c0002743e070a98fe378000000de16c6e0558a70324c4c1000000000001fc2f400c6787a0040fc0219b0b41dc2d9e40804680014b40278095800000188808001620000000000061c7b88b18e00000012450000afa0c1f4000000412b8000d20e0000190568a5000888548aa3580000013a0008b083874000554001a723000000000000878001af0006e8000002ba1d8e10000720006e1b33a4000029b006660c0009f228000c6800000754000001a64b8000003e40f0001de00021c0000000000000000000000001a1000000c580027241400000000550c50e72860008780042849c8b9a6000000308000007140003d0000007213c1e20011802d000448000261be18c0d8fb17a0006b8002800010d159000000000d21c2398b98003a689cda801070528819463f6000b70000006c8358f23d8660b500000000000000000314ac05c23200000000000000088b7000000000ce33e000001b43c48407e800000000000000300000d0004260006d8003260001a8002d2020000000007840a8864365d0c40002844909f1a51ba858591630004984f050000444848000000001600038e000a29ef2400
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x14347c0054a2400000004002a6462100780221e748801a000000000d9c06400002c5c5921c00c204c09193001000000292000000000001c0000c040820108082000220101000001289932014258042004a86448050960108012899321d4258042004a8644875096010801621919d54258042004a86478350960108014299714d425804200588644535096010801431942057018d5100518648815c06354401451901cd635464100518640735895190401511901cd43545410051164b641cd514c40185096600735453100614d91801cd514c4018516460073545310060561073d89514c401451901cf6254531006055d083544604c401844835c951181310060c591801cd5188401451901cd6354621005146407358d5148401a2164600425452100550640734c95148401851736007358750006885098010961d4001451901cf6354610004946588354630840014449359572905100050524d655d2214400345097595314c1100060c591801cd51040014519021d635441000518640735895104001414935d56444010004152617558d1004001444935d56244010
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x16100005023484b30039aa298802841a2259801cd514c401420d16c8c00e6a8a6200c04611901cf6254531
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 66
  | 6 => 1665
  | 5 => 2907
  | 4 => 561
  | 3 => 39
  | 2 => 4
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
  | 7 => packedAt gbK7 (1892+((h/22+packedAt gbK7 (1716+(h % 22)*8) 8) % 151)*8) 8
  | 6 => packedAt gbK6 (68265+((h/555+packedAt gbK6 (61605+(h % 555)*12) 12) % 2658)*12) 12
  | 5 => packedAt gbK5 (151164+((h/969+packedAt gbK5 (139536+(h % 969)*12) 12) % 3489)*13) 13
  | 4 => packedAt gbK4 (34969+((h/187+packedAt gbK4 (33099+(h % 187)*10) 10) % 985)*11) 11
  | 3 => packedAt gbK3 (2821+((h/13+packedAt gbK3 (2730+(h % 13)*7) 7) % 67)*7) 7
  | 2 => packedAt gbK2 (327+((h/1+packedAt gbK2 (324+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x1c07ffc3187c1c07ff0fc0ffffc0709f08727f
  | 1 => 0xe00787fc1f8fe00783f1ff0f07e64913364d93
  | 2 => 0x7f83fe00ffff803fe000ff8078e1cc78e1c
  | 3 => 0xfff8003ffff0000003fffff000380fe0f80fe0
  | 4 => 0x3ffffffffffc000000003ff000fff000
  | 5 => 0xffffffc00000000000000000003fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x441084000100400a002408142001085001025
  | 1 => 0x2082c6940c8f20550990aa0a15a64912164492
  | 2 => 0x114d20d2005493003a4062cb0828e18428e18
  | 3 => 0x4830002b512000a01249146020080220e80b40
  | 4 => 0x22004329e4a92c658001840013d6000bd6000
  | 5 => 0x93c767000403030460802088c637fddf000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xfffaffa8fefaeea8fffaffa8fefaeea8fffaffa8fefaeea8fffaffa8fefaeea8fffaffa8fefaeea8fffaffa8fefaeea8fffaffa8fefaeea8fffaffa8fefaeea8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_11878
namespace PEqualNP.Outside.L_meta_11878
open PEqualNP.Outside.L_meta_11878.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 1 := bs0_3_0
theorem alls0 : ∀ k ≤ 3, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 1 := bs1_3_0
theorem alls1 : ∀ k ≤ 3, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 1 := bs2_3_0
theorem alls2 : ∀ k ≤ 3, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 1 := bs3_3_0
theorem alls3 : ∀ k ≤ 3, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 1 := bs4_3_0
theorem alls4 : ∀ k ≤ 3, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 1 := bs5_3_0
theorem alls5 : ∀ k ≤ 3, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 4 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 39 := (concat bgb_3_0 bgb_3_32)
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
theorem bgb_4_544 : Interval gbAtlas 4 544 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 561 := (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 (concat bgb_4_224 bgb_4_256)))) (concat (concat (concat bgb_4_288 bgb_4_320) (concat bgb_4_352 bgb_4_384)) (concat (concat bgb_4_416 bgb_4_448) (concat bgb_4_480 (concat bgb_4_512 bgb_4_544)))))
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
theorem bgb_5_2880 : Interval gbAtlas 5 2880 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2907 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 (concat bgb_5_448 bgb_5_480))) (concat (concat bgb_5_512 (concat bgb_5_544 bgb_5_576)) (concat bgb_5_608 (concat bgb_5_640 bgb_5_672))))) (concat (concat (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832))) (concat (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)))) (concat (concat (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)) (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216))) (concat (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312)) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)))))) (concat (concat (concat (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568))) (concat (concat bgb_5_1600 (concat bgb_5_1632 bgb_5_1664)) (concat bgb_5_1696 (concat bgb_5_1728 bgb_5_1760)))) (concat (concat (concat bgb_5_1792 (concat bgb_5_1824 bgb_5_1856)) (concat bgb_5_1888 (concat bgb_5_1920 bgb_5_1952))) (concat (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048)) (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144))))) (concat (concat (concat (concat bgb_5_2176 bgb_5_2208) (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304))) (concat (concat bgb_5_2336 (concat bgb_5_2368 bgb_5_2400)) (concat bgb_5_2432 (concat bgb_5_2464 bgb_5_2496)))) (concat (concat (concat bgb_5_2528 (concat bgb_5_2560 bgb_5_2592)) (concat bgb_5_2624 (concat bgb_5_2656 bgb_5_2688))) (concat (concat bgb_5_2720 (concat bgb_5_2752 bgb_5_2784)) (concat bgb_5_2816 (concat bgb_5_2848 bgb_5_2880)))))))
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
theorem bgb_6_1664 : Interval gbAtlas 6 1664 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1665 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))) (concat (concat bgb_6_608 (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 bgb_6_800))))) (concat (concat (concat (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992))) (concat (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216)))) (concat (concat (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312)) (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 bgb_6_1440))) (concat (concat bgb_6_1472 (concat bgb_6_1504 bgb_6_1536)) (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 66 := (concat bgb_7_0 (concat bgb_7_32 bgb_7_64))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 16, 20),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 4 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 4 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 4 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 4 := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 2 zero,inputs.getD 1 zero,inputs.getD 5 zero,inputs.getD 4 zero,inputs.getD 3 zero,inputs.getD 6 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xfffffffffefefefefffaffa8fefaeea8fffffffffefefefefffaffa8fefaeea8fffffffffefefefefffaffa8fefaeea8fffffffffefefefefffaffa8fefaeea8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) SB :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) SB :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) SB :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) SB :=
    slice_correct (ms:=fixRows 40 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
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
  have lift := lift_ok (u:=true) (ms:=fixRows 64 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 7 → Bool) := decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def sample7 (r : Row) (i : Fin 7) := bit r (fullRoots.getD i.val zero)
theorem table7 : ∀ r, posted (sample7 r) = bit r fullWord := by decide +kernel
theorem raw7 : List.ofFn (fun i : Fin 7 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
theorem eval7 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs fullRoots).getD o zero=fullWord := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample7 r) = fullRoots.map (bit r) := by rw [←raw7,List.map_ofFn]; rfl
  rw [←bRead,exeBits gs r fullRoots (fun g hg => (legal g hg).1),←e]
  exact (h (sample7 r)).trans (table7 r)
theorem binaryLower (low : Lower true fullRoots fullWord 10)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 10 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval7 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_11878.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.or,[7,3]⟩,⟨.and,[8,6]⟩,⟨.or,[1,2]⟩,⟨.or,[10,6]⟩,⟨.or,[4,5]⟩,⟨.and,[11,12]⟩,⟨.or,[3,5]⟩,⟨.and,[0,14]⟩,⟨.or,[9,13]⟩,⟨.or,[16,15]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,17⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
    exact ⟨mono,17,monoShape,by change 11 ≤ gs.length; omega,monoEval⟩
end PEqualNP.Outside.L_meta_11878

open PEqualNP.Outside.L_meta_11878 in
theorem PEqualNP.Outside.L_meta_11878 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
