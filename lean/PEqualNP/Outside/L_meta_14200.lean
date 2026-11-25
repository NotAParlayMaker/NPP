import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_14200.Model
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


end PEqualNP.Outside.L_meta_14200.Model

namespace PEqualNP.Outside.L_meta_14200
open PEqualNP.Outside.L_meta_14200.Model
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

end PEqualNP.Outside.L_meta_14200

namespace PEqualNP.Outside.L_meta_14200
open PEqualNP.Outside.L_meta_14200.Model
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
  | 1 => 0xe0fff07c1ffff8783fe1e07fc3c0fffeb3333f
  | 2 => 0xffff801fffff803ffe007ffc00ffff3c3c3f
  | 3 => 0xff03ffffe07c1fffc1ffff83ffff0701cfcfcc
  | 4 => 0x3ffffff801ffffe000003fffff801f00ff0
  | 5 => 0xfffc000000001ffffffffffc00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x892913212529083a0aa12525424a4954931315
  | 2 => 0x5252241a4a52138415520a4aa41492a92c2c2a
  | 3 => 0x401841080300208840644300c886040c05454c
  | 4 => 0x9ce38a53101b5d56a61110633338e031f00ab0
  | 5 => 0x18830c639c639e6739999c702220c0c1fab000
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xffc0ffc0ffc0c0c0ffc0ffc0ffc0c0c0ffc0ffc0ffc0c0c0ffc0ffc0ffc0c0c0ffc0ffc0ffc0c0c0ffc0ffc0ffc0c0c0ffc0ffc0ffc0c0c0ffc0ffc0ffc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_14200
namespace PEqualNP.Outside.L_meta_14200
open PEqualNP.Outside.L_meta_14200.Model
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
  | 0 => 0xffc787ffc787ffff087fc387fc387fff9870ff
  | 2 => 0xc7f80787f807871ff070fc078fc078e7d64c93
  | 3 => 0x7fff807fff807e1ff80fff80fff80f8678f1c
  | 4 => 0xf8000007fffff801ffff00000fffff00780fe0
  | 5 => 0xfffffff800000001fffffffff00000007ff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x40400800400800000001008080080820001025
  | 2 => 0xb493534c93534e317438e4352e435257564c92
  | 3 => 0x1010111010110021080491004910091028518
  | 4 => 0x1434666626444255ad5a20444b266602780ac0
  | 5 => 0x2626444434666499ce6cb266620444047d6000
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xffaaffaaffaaaaa0ffaaffaaffaaaaa0ffaaffaaffaaaaa0ffaaffaaffaaaaa0ffaaffaaffaaaaa0ffaaffaaffaaaaa0ffaaffaaffaaaaa0ffaaffaaffaaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_14200
namespace PEqualNP.Outside.L_meta_14200
open PEqualNP.Outside.L_meta_14200.Model
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
  | 0 => 0xffc787ffc787ffff087fc387fc387fff9870ff
  | 1 => 0xc7f80787f807871ff070fc078fc078e7d64c93
  | 3 => 0x7fff807fff807e1ff80fff80fff80f8678f1c
  | 4 => 0xf8000007fffff801ffff00000fffff00780fe0
  | 5 => 0xfffffff800000001fffffffff00000007ff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x40400800400800000001008080080820001025
  | 1 => 0xb493534c93534e317438e4352e435257564c92
  | 3 => 0x1010111010110021080491004910091028518
  | 4 => 0x1434666626444255ad5a20444b266602780ac0
  | 5 => 0x2626444434666499ce6cb266620444047d6000
  | _ => 0
def s2Atlas : Atlas := ⟨3,rawDecor 59 s2Pos s2Neg, 0xffaaffaaffaaaa88ffaaffaaffaaaa88ffaaffaaffaaaa88ffaaffaaffaaaa88ffaaffaaffaaaa88ffaaffaaffaaaa88ffaaffaaffaaaa88ffaaffaaffaaaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_14200
namespace PEqualNP.Outside.L_meta_14200
open PEqualNP.Outside.L_meta_14200.Model
def s3K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s3K3 (6+((h/1+packedAt s3K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x87ffff0ffffc1ff83ffe0fffc1fffc1f9cf3cf
  | 1 => 0xf8783ff0f07fe1ffc707f0f0fe1e1fe3eb4d33
  | 2 => 0xff803fff007ffe1ff807ff00ffe01ffc738e3c
  | 4 => 0x3fffff80001ffff80000ffffe0007c0fc0
  | 5 => 0xffffc0000000001fffffffff000000007ff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x80000100000020000008011000220400001045
  | 1 => 0x1212522244a90309434290a252144943294512
  | 2 => 0x2124a4442952103298852a04a5409298528a28
  | 4 => 0x7557388aac1b555cedd18888f999c0c97c0f80
  | 5 => 0x466630ecce63999f36e7ccce311103127fe000
  | _ => 0
def s3Atlas : Atlas := ⟨3,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeaeaeae8e8eaeaeaeaeaeae8e8eaeaeaeaeaeae8e8eaeaeaeaeaeae8e8eaeaeaeaeaeae8e8eaeaeaeaeaeae8e8eaeaeaeaeaeae8e8eaeaeaeaeaeae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_14200
namespace PEqualNP.Outside.L_meta_14200
open PEqualNP.Outside.L_meta_14200.Model
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
  | 0 => 0x1e3e3c7ffc7ffe3f0c63831ffc7ff83f00f3cf
  | 1 => 0x1fc03f8e3f8e3fc7f07c03e38f8e3fc7334d33
  | 2 => 0xe0003ff03ff03ff8ff8003fc0ff03ff8c38e3c
  | 3 => 0xffffc0003fffc000fffffc000fffc000fc0fc0
  | 5 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x2004400040000400000800480120800001045
  | 1 => 0xc4148944492854085064292124849286314512
  | 2 => 0x1a912289244a801ac80524849212530c28a28
  | 3 => 0x488c032520240c92352918000e498192540f80
  | 5 => 0x9130204803493124ca52639260000624abe000
  | _ => 0
def s4Atlas : Atlas := ⟨3,rawDecor 47 s4Pos s4Neg, 0xffeaffeaeae8eae8ffeaffeaeae8eae8ffeaffeaeae8eae8ffeaffeaeae8eae8ffeaffeaeae8eae8ffeaffeaeae8eae8ffeaffeaeae8eae8ffeaffeaeae8eae8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_14200
namespace PEqualNP.Outside.L_meta_14200
open PEqualNP.Outside.L_meta_14200.Model
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
  | 0 => 0x1e3e3c7ffc7ffe3f0c63831ffc7ff83f00f3cf
  | 1 => 0x1fc03f8e3f8e3fc7f07c03e38f8e3fc7334d33
  | 2 => 0xe0003ff03ff03ff8ff8003fc0ff03ff8c38e3c
  | 3 => 0xffffc0003fffc000fffffc000fffc000fc0fc0
  | 4 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x2004400040000400000800480120800001045
  | 1 => 0xc4148944492854085064292124849286314512
  | 2 => 0x1a912289244a801ac80524849212530c28a28
  | 3 => 0x488c032520240c92352918000e498192540f80
  | 4 => 0x9130204803493124ca52639260000624abe000
  | _ => 0
def s5Atlas : Atlas := ⟨3,rawDecor 31 s5Pos s5Neg, 0xffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_14200
namespace PEqualNP.Outside.L_meta_14200
open PEqualNP.Outside.L_meta_14200.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x10a00424c82c40ecd86c980064b448548c7490f0f8e0cc809cb000c000d40000b8703000440000080000346800208400e4bc6014003800fc28e8787c00f4001c008800d094005c00a500184c000ca8005850acdcc43c3000300001030000108000c0801008892120801ff54005fd5001fe54006f95001fd54005f55001bd54004f55001fc54007fd4c01fe53007f54c01fc53007fd0c01fe43007f50c01fc43007fd4801fe52007f54801fc52007fd0801fe42007f50801fc42007fcc801fe32007f4c801fc32007fd4401fe51007f54401fc51007fd0401fe41007f50401fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc21007fd4001fe50007f54001fc50007fd0001fe40007f50001fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc4000fb88620007d84310002fe6088001f79044000fec8220005feca90002fe65480017eb2a4000bf19520005fec890002fe64480017eb224000bf19120006fea890003be5448001beaa24000ef551200067aa890002ff63480017f31a4000bf58d20005f8c690003ee5248001f6a924000fb90920007da8490003ee3248001f69924000bfd8520007eec290002f761480017e30a4000fd18520005e8c290003ef2148001f690a4000fec8120007dc4090002ff65080017f3284000df99420004fcca10002fd6508001beb2840009f59420005f8ca10002ff64080017f3204000ef990200057cc810002fd6408001deb204000af59020005f8c8100037f5408001df2a04000df550200077aa8100033d54080017fb184000bf98c20007bcc610002de63080017eb184000f758c20005bac610002fc63080017f3104000bf98420007ecc210002f661080017eb084000fd58420005eac210003ee2108001f61084000bf98020007de4010003fa2008001f69004000fe48020005fecb88002fe65c40017eb2e2000bf19710005fec988002fe64c40017eb262000bf19310006fea988003be54c4001beaa62000ef553100067aa988002ff63c40017f31e2000bf58f10005f8c788002ff62c40017f3162000bf58b10005f8c588003f651c4001faa8e2000fd90710007ea8388003f631c4001fa98e2000fd88710007ea4388002ff65840017f32c2000bf59610005f8cb08002ff64840017f3242000bf59210005f8c9080037f5484001df2a42000df552100077aa9080033d54840017fb1c2000bf98e10005fac708002fc63840017fb142000bf98a10005fac508002fc62840017eb0c2000fdc8610007e84308002fe6084001fd1042000fe48210007ee2108003fb10840017fb2a2000bf99510005faca88002fc65440017fb222000bf99110005fac888002fc6444001bfaa22000ef95110006faa888003bd54440019eaa22000bfd8d10005fcc688002fd63440017e31a2000bfd8910007dec488002ef62440017f3122000bf58910005f8c488003ec6244001763122000fd94510007eaa288003f64144001faa0a2000fd8c510007ea6288003f62144001fa90a2000fe88110007f24088003fb1044001fb0822000bfd9410005fcca080037e65040013f3282000bf59410006faca080027d65040017e3282000bfd9010005fcc808003be64040015f3202000bf590100077ac808002bd64040017e3202000dfd50100077ca8080037d5404001deaa02000cf55010005fec608002fe6304001ef3182000b798c10005fac608003dd63040016eb182000bf18c10005fec408002fe6204001f73102000bb98810005fac408003ed620400176b102000bf18810005fcc208003f72104001fa1082000bf98010007ee2008003fa1004001fa8802000fe44010
  | 1 => 0x3bf4250001dea128000bfd8540005f8c2a0003bf4150001dea0a8000fed01400077c80a0002ff65100017f3288000df99440004fcca20002fd6510001beb2880009f59440005f8ca20002fe6410001bfaa08000ef95040006faa820003bd54100019eaa08000bf98c40007bcc620002de63100017eb188000f758c40005bac620003be4310001de2188000bf98840007dcc420002ee62100017eb108000fb58840005dac420002fe6110001fb3088000bd98440005fac220003f561100017ab088000bf980400077e8020003fa4010001dea008000fe50040005fecb98002fe65cc0017eb2e6000bf19730005fec998002fe64cc0017eb266000bf19330006fea998003be54cc001beaa66000ef553300067aa998003de53cc001eea9e6000f790f30007ba8798002fe62cc0017eb166000f7ccb30007ba6598002fe61cc0017eb0e6000f7cc730007ba6398002ff658c0017f32c6000bf59630005f8cb18002ff648c0017f3246000bf59230005f8c9180037f548c001df2a46000df552300077aa9180033d548c0017eb1c6000bf98a30005fac518002fe618c0017eb0c6000bf98230007f4a118003f9508c001fd2046000fe50230007be6118003fb308c0017fb2a6000dfd9530004feca98002fe654c0017eb2a6000bf19530006f8ca980027c654c0017fb226000efd91300057ec898002fe644c0017eb226000bf1913000778c898002bc644c001bfaa26000ef95130006faa898003bd544c0019eaa26000f794d30007baa698003de434c001eea1a6000bfd8930005f8c498003df324c001ee9926000bfd8530005f8c298003df314c001ee98a6000fe94130007f2a098003fa404c001fca026000fecc130007bc6098002ff650c0017f3286000df99430004fcca18002fd650c001beb2860009f59430005f8ca18002ff640c0017f3206000ef990300057cc818002fd640c001deb206000af59030005f8c8180037f540c001df2a06000df550300077aa8180033d540c0017f3186000bf98830007dcc418002ee620c0017eb106000fb58830005dac418002fe610c001fb3086000bd98430005fac218003f5610c0017ab086000bf98030007be6018003fa300c001ee9806000fe4c030005fecb90002fe65c80017eb2e4000bf19720005fec990002fe64c80017eb264000bf19320006fea990003be54c8001beaa64000ef553200067aa990002ff63c80017f31e4000bf58f20005f8c790003ee52c8001f6a964000fb90b20007da8590003ee32c8001f69964000bf98720005fac390003ef21c8001f690e4000bfd9620005fccb10002fd65880017e32c4000bfd9220005fcc910002fd64880017e3244000dfd52200077ca9100037d5488001deaa44000cf55220005fec710002fe63880017eb1c4000bf18e20005fac510002fe61880017eb
  | 2 => 0x21005fac690802fc6348401fb90a4200fb88521005fec090802fc60484017fb284200bf99421006fcca108027e65084017eb284200df59421004faca10802fc65084017fb204200bf990210077cc810802be64084017eb204200ef590210057ac810802fc6408401bfaa04200ef95021006faa810803bd54084019eaa04200bfd8c21005fcc610803de63084016f3184200bf58c21007bac610802dd63084017e3184200bf98821007dca410803ed5208401f72104200fb50821007dc6410803ed32084017f3084200fd94421007eaa210803f64108401faa084200fd8c421007ea6210803ef2108401fb1084200fb48421007ea4210803e521084017f3004200fe98021005f4c010802fd6008401fcb004200be58021005fcc9a8003be64d40015f326a000bf593500077ac9a8002bd64d4001bfaa6a000ef95350006faa9a8003bd54d40019eaa6a000bf98f50005fac7a80037f53d4001bea9ea000bf98b50005fac5a80037f52d4001bea96a000bf98750005fac3a80037f51d4001bea8ea000bf59650005fcc928002fd6494001bfaa4a000ef95250006faa928003bd54940019eaa4a000bf98e50005fac7280037e5394001be29ca000bf98a50005fac528002fe61940017eb0ca000bf98250006fea128003fb50940017fb22a000bf19150006fea8a8003be5454001beaa2a000ef551500067aa8a8002ff63540017e31aa000dfd4d50006faa6a8002ff62540017e312a000dfd4950006faa4a8002ff61540017e30aa000dfd4550006faa2a8003fb5054001bf282a000bf99450005fcc828003be64140015f320a000bf590500077ac828002bd6414001bfaa0a000ef95050006faa828003bd54140019eaa0a000bf98c50007bcc628002de63140017eb18a000f758c50005bac6280037e5314001be298a000bf98850007dcc428002ee62140017eb10a000fb58850005dac428002fe6114001fb308a000bd98450005fac228003f561140017ab08a000bf98050006fea028003fa5014001bea80a000fe54050005fecba0002fe65d0001bf32e80009f99740005facba00037d65d00013eb2e8000bf19740006fea9a0003be54d0001beaa68000ef553400067aa9a0002fe63d00017eb1e8000efd0f400077a87a0002fe62d00017eb168000efd0b400077a85a0002fe61d00017eb0e8000efd07400077a83a0002ff65900017f32c8000bf59640005f8cb20002fd6490001bfaa48000ef95240006faa920003bd54900019eaa48000bf98e40005fac720003be4390001de21c8000bf98a40005fac520002fe61900017eb0c8000bf982400077e8120003fb40900017fb2a8000bf99540005facaa0002fc6550001bfaa28000ef95140006faa8a0003bd54500019eaa28000bfd8d40005f8c6a0003bf4350001dea1a8000bfd8940005f8c4a000
  | 3 => 0xba0c8200bf98241005fac120802ff65504017f32a8200bf59541005f8caa08037f5450401df2a28200df551410077aa8a08033d54504017fb1a8200bf18d410077c86a0803bc43504017fb128200bf189410077e84a0803bd4250401fba0a8200ef90541005fec0a0802fc60504017fb288200bf99441006fcca208027e65104017eb288200df59441004faca20802fc65104017f3208200dfd50410077ca8208037d5410401deaa08200cf55041005fcc620802fd63104017f3108200bf58841005fcc220803bf4110401fb2088200ef50441007ea8220802fe60104017eb008200bfd9731005fccb98802fd65cc4017e32e6200bfd9331005fcc998802fd64cc4017e3266200dfd53310077ca9988037d54cc401deaa66200cf55331005fcc598803ee62cc401773166200bf58b31007dac598802ed62cc401ef9966200f74cb31005fcc198802fd60cc4017fb2c6200bf99631006fccb188027e658c4017eb2c6200df59631004facb18802fc658c4017fb246200bf992310077cc918802be648c4017eb246200ef592310057ac918802fc648c401bfaa46200ef95231006faa918803bd548c4019eaa46200bf58e31005fcc518802fd628c4017f30c6200fd94631007eaa318803f6418c401faa0c6200f7cc631007ee6318802fe608c4017eb046200bfd9531005fcca98802fd654c4017e32a6200bfd9131005fcc898802fd644c4017e3226200dfd51310077ca8988037d544c401deaa26200cf55131005fec498802fc624c401ef9926200f74c931007eca298803f5514c401fb20a6200fd50531007ee6298803de314c4017fb026200bf18131005feca18802fe650c4017eb286200bf19431005fec818802fe640c4017eb206200bf19031006fea818803be540c401beaa06200ef550310067aa818802fe630c4017f3106200bf58831005fcc218803df310c401fb1886200f74c431007ea6218802fe600c4017eb006200bfd9721005fccb90802fd65c84017e32e4200bfd9321005fcc990802fd64c84017e3264200dfd53210077ca9908037d54c8401deaa64200cf55321005fec790802fe63c84017eb1e4200bf18f21007eca390803f551c8401fb20e4200fd50721007ec6390803f531c84017f3064200bf58321005fecb10802fe65884017eb2c4200bf19621005fec910802fe64884017eb244200bf19221006fea910803be5488401beaa44200ef552210067aa910802ff63884017f31c4200bf58e21005f8c710802fd6288401f72944200fb54a21007dc8510803ed4288401f71944200fb4ca21005fcc310803ef2188401fb90c4200bf98221005fac110802ff65484017f32a4200bf59521005f8ca90802ff64484017f3224200bf59121005f8c8908037f5448401df2a24200df551210077aa8908033d54484017fb1a4200bf98d
  | 4 => 0x2fd64cc8017e3266400dfd53320077ca9990037d54cc801deaa66400cf55332005fcc399003f661cc8017b30e6400bf58732007eac399002f561cc8017f3066400bf58332005fecb19002fe658c801bf32c64009f99632005facb190037d658c8013eb2c6400bf19632005fec919002fe648c801df3246400af99232005fac919003bd648c8015eb246400bf19232006fea919003be548c801beaa46400ef552320067aa919002fd638c8017f3146400fb94a32007daa519003ee428c801f6a146400f7cca32007de6519002fe618c8017eb0c6400bf98232005fac119002ff654c8017f32a6400bf59532005f8ca99002ff644c8017f3226400bf59132005f8c8990037f544c801df2a26400df551320077aa8990033d544c801f72926400fb54932007dc8499003ed424c801f79926400f78c932005fec299002fc614c8017fb026400bf18132005feca19002fe650c8017eb286400bf19432005fec819002fe640c8017eb206400bf19032006fea819003be540c801beaa06400ef550320067aa819002fe630c8017f3106400f7cc832007dc6419003dd320c801f69906400bf98432005fac219002fe600c8017eb006400bf993510077cc9a8802be64d44017eb26a200ef593510057ac9a88037f54d4401df2a6a200df553510077aa9a88033d54d44017f31ea200bf58f51006fca7a88037c53d44017f316a200fb98b51005dcc5a8802fd62d4401f6b16a200bb58b51006fea5a88037d52d44017f306a200bf58351005facb28802fe64944017eb24a200dfd52510077ca9288037d5494401deaa4a200cf55251005fcc728802fd63944017f314a200bf58a51005fcc3288037f5194401fba8ca200bf98251005fac128802ff64544017e322a200dfd51510077ca8a88037d5454401deaa2a200cf55151005fec6a8802fc6354401bf29aa200df14d51005fec4a8802fc6254401bfa92a200df54951007eea2a88037e51544017fb02a200bf18151005fcca28802fe6414401df320a200af99051005fac828803bd64144015eb20a200dfd50510077ca8288037d5414401deaa0a200cf55051005fcc628802fd63144017f310a200bf58851005fcc2288037f5114401fb288a200df54451007eaa228802fe60144017eb00a200bfd9741005fccba08037e65d04013f32e8200bf59741006facba08027d65d04017e32e8200dfd53410077ca9a08037d54d0401deaa68200cf55341005fcc7a0802fd63d0401df21e8200ef10f41005fcc5a0803ee62d0401773168200bf58b41007dac5a0802ed62d0401dfa168200ef50b41005fcc1a0802fd60d04017fb2c8200bf99641005facb20802fc65904017eb248200dfd52410077ca9208037d5490401deaa48200cf55241005fcc720802fd63904017f3148200bf58a41005fcc320803bf4190401f
  | 5 => 0x51430077aa8a18033d5450c01efa1a8600ef90d43005fec4a1802fc6250c017fb0a8600bf18543005fec0a1802fc6050c017fb288600bf99443006fcca218027e6510c017eb288600df59443004faca21802fc6510c017f3208600dfd50430077ca8218037d5410c01deaa08600cf55043005fcc621803bf4310c01ef2188600ef50c43007ba8621802fe6210c01f73108600bb98843005fac421803ed6210c0176b108600bf98443007ecc221802f66110c017eb088600fd58443005eac221802fe6010c01fd3008600be98043005fac021803f96010c017cb008600bf993520077cc9a9002be64d48017eb26a400ef593520057ac9a90037f54d4801df2a6a400df553520077aa9a90033d54d48017f31ea400bf58f52006fca7a90037c53d48017f30ea400fd98752005ecc3a9002fd61d4801fab0ea400bd58752005fcc1a9002fd60d48017eb2ca400bf99252005fac9290037f5494801df2a4a400df552520077aa9290033d54948017f31ca400bf58e52005fcc5290037f5294801f7a94a400bf98652005fac329002fe60948017eb04a400bfd9152005f8c8a90037f5454801df2a2a400df551520077aa8a90033d54548017fb1aa400bf18d52006fca6a90037c5354801f7a92a400df94952005fec2a9002fc61548017fb02a400bf18152005fcca29002fe6414801df320a400af99052005fac829003bd64148015eb20a400dfd50520077ca8290037d5414801deaa0a400cf55052005fcc629002fd63148017f310a400dfd4852007dca4290037d5214801f6a90a400bf98452005fac229002fe60148017eb00a400bfd9742005fccba10037e65d08013f32e8400bf59742006facba10027d65d08017e32e8400dfd53420077ca9a10037d54d0801deaa68400cf55342005fcc7a1002fd63d0801df21e8400ef10f42005fcc3a1003f661d08017b30e8400bf58742007eac3a1002f561d08017f3068400bf58342005fecb21002fe65908017eb2c8400bf19642005fac9210037f5490801df2a48400df552420077aa9210033d54908017f31c8400bf58e42005fcc521003bf4290801f7a148400bf98642005fac321002fe60908017eb048400bfd9542005fccaa1002fd65508017e32a8400dfd51420077ca8a10037d5450801deaa28400cf55142005fec6a1002fc6350801df21a8400ef10d42007de84a1003be42508017fb0a8400bf18542005fec0a1002fc60508017fb288400bf99442006fcca210027e65108017eb288400df59442004faca21002fc65108017f3208400dfd50420077ca8210037d5410801deaa08400cf55042005fcc621002fd63108017f3108400efd0842007dc8421003bd4210801f6a108400bf98442005fac221002fe60108017eb008400bfd9732005fccb99002fd65cc8017e32e6400bfd9332005fcc999
  | 6 => 0x1deb1ca800ef18e540077ec52a003be6295001deb14a800ef18a540077ec32a003be6195001deb0ca800ef186540077ec12a003be6095001deb04a800ef182540077ea8aa0037e54550017fb1aa800bf18d54005fec4aa002fc62550017fb0aa800bf18554005fec0aa002fc6055001bfb22a800cfd9154006fec6aa0037e6355001beb1aa800df18d54006fec4aa0037e6255001beb12a800df18954006fec2aa0037e6155001beb0aa800df18554006fec0aa0037e6055001beb02a800df181540077ecaaa0033f6555001dfb1aa800ef98d540077ac6aa003bc6355001dfb12a800ef989540077ac4aa003bc6255001dfb0aa800ef985540077ac2aa003bc6155001dfb02a800ef981540077ac0aa003bc60550019fb1aa800cf98d540067ac6aa0033c63550019fb12a800cf989540067ac4aa0033c62550019fb0aa800cf985540067ac2aa0033c61550019fb02a800cf981540067ac0aa0033c60550017f328a8009f99454005fcc82a002be6415001bfaa0a800ef95054006faa82a003bd54150019eaa0a800bf98c54005fac62a002fe62150017eb10a800bf98454005fac22a002fe60150017eb00a800bf993530077cc9a9802be64d4c017eb26a600ef593530057ac9a98037f54d4c01df2a6a600df553530077aa9a98033d54d4c017f316a600bf58b53005fcc3a9802fd61d4c017f306a600bf58353005facb29802fe6494c017eb24a600dfd52530077ca9298037d5494c01deaa4a600cf55253005fcc7298037f5394c01efa9ca600bf98a53005fac529802fe6194c017eb0ca600bf98253005fac129802ff6454c017e322a600dfd51530077ca8a98037d5454c01deaa2a600cf55153007bea6a98037e5354c017fb12a600bf18953005fec2a9802fc6154c017fb02a600bf18153005fcca29802fe6414c01df320a600af99053005fac829803bd6414c015eb20a600dfd50530077ca8298037d5414c01deaa0a600cf55053005fcc6298037f5314c01ef298a600df54c53007baa629802fe6214c01f7310a600bb98853005fac429803ed6214c0176b10a600bf98453007ecc229802f66114c017eb08a600fd58453005eac229802fe6014c01fd300a600be98053005fac029803f96014c017cb00a600bfd9743005fccba18037e65d0c013f32e8600bf59743006facba18027d65d0c017e32e8600dfd53430077ca9a18037d54d0c01deaa68600cf55343005fcc5a1802fd62d0c017f30e8600bf58743005fcc1a1802fd60d0c017fb2c8600bf99643005facb21802fc6590c017eb248600dfd52430077ca9218037d5490c01deaa48600cf55243005fcc721803bf4390c01efa1c8600bf98a43005fac521802fe6190c017eb0c8600bf98243005fac121802ff6550c017f32a8600bf59543005f8caa18037f5450c01df2a28600df5
  | 7 => 0x709d286814811abca82009a34e3bc000588a1c0000000007de000a5075073a714ba600000000c00000a00000100000000300400800000100001f00200a00300300800600d00301801300000600000500000600a00000000200500300400800800400400000100b00805903800f00b00d00200100000300100d04d00900000300101700100300200800100200d00000400800000302e00900406c00100100b00000301900000000900000000000200100000300300300200000000500300000000000000500200100300000300601100600c02500300100000201601700300200500100700600900b00c00000100400001400000604100300200100400d00200100700100e00200500201000500000c00100000b00000100100000000100500000d01200200600200000000800002800000b00000000300800201000000701700000400202801100700800501600001e00000300000004500300000000a00000700300000000100300100302100100000206b00000000300000000700a00000d00c00400400e00200200000100400101500701200000000200600000101100300100a00000900400000500000000001000000000800400100700500000900500000000900100000000200800201000000200300000f00000100b00100d00300000200d01400500300001b00500a00200400000200100400900f00000800300d01200000101400301300200301701d00600000600301f00100000200400901800000000700000300400000400400c00200600100100800000d00300701e00000001300003300200700300100c00000100000f00400202c00400201d00700200900401600000200100001800100400201900200200000000100200200c00100600100000000402201b0a000400000d00f01d00500000100800400200f00400600400200500000200100b00000000000802400800500200201000900000300600002d00a00100000900200300000000000800c01500100500200400c00000000900000d00000100201800000300201200300f00000000700b00202600000000000300000300001e00000800105800100c00000300200c01002100000100500000203e00001200003f00600900400000400300100500000000000000400600a005fcc7aa002fd63d50017f316a800bf58b54005fcc3aa002fd61d50017f306a800bf58354006fec7aa0037e63d5001beb1ea800df18f54006fec5aa0037e62d5001beb16a800df18b54006fec3aa0037e61d5001beb0ea800df18754006fec1aa0037e60d5001beb06a800df18354005facb2a0027d65950017f324a800dfd52540077ea92a0033f54950017f31ca800bf58e54005fcc52a002fd62950017f30ca800bf58654005fcc12a002fd60950015eb2ca8008f596540077ec72a003be639500
  | 8 => 0xb08c52a3a1e47bc000000bd22f82646060004d8c4800000060cb4e0008361e20002786425000000000ee8ec90e0005d4000854066000000000c240000a28d690ab586b255e81a4f64ac2568c8712b5067e1ee4bc3561eaa7c61e10a0c69aa0005c42bc42811c00069c67c82266c3ba0c85fa3641082c86dc3760002e258e3fa5aa74c0000000009a2b0057aa4c22c8b86648241d621627212496067275e0aea5a5a2c2e4168c2200c0689a9d46325f8ae267429e20e00070620a0da87a4360d60f40005de96420200068a0d20001740863c653689c5a451674a1a0000000b3e5ee6a0794b92000b6c02ea0417228c0002501b46b896c53858c0828fa4c6a727d0c6017c28e1b8a7482e408b2c0003981863b62d4a0e67a0007b48fc4faac80fa1827708b283038e3d249c22eaf8adc600000c5c7eab8a0aca466ea8940004b2452becc1a51e5ce42e9029ce8f6bbe6fe3f2262648000000354b5a06c11062e30c12a1987781200003c400042233ca38ab45304468888a4b8849019a9a49187dc000000000be20007e40003e6000c3e18e084b48932000b2837800038abac000000316bd09f49686cca8a69439600061c000a94000000000000000b7c6ba1e80002240009b624400010e04e4040e4ae08661ba000000000748312ad25080003acaf2a560008dea82128000c361527589fc1f431468ca3cc0c3ae212c382faa580586be4768d225c000a8410000057623a0004bac62000420000102b74000c647565920000260005803260a0000000c2800036ab7671a776000000000000000aca6da0000001686c20240000000008bc0000e206a82a6f84063c20001e6aea330000942000aec000ae60184380007340009800000008ae0449460009b00004822a61c4000000000000a1000000078442c0000000009dc000000000000658a1a00000000087cbb40009349c67ee944982ba083e000000324bd818cc468e6c209c87420289f6abc2f62e450e3d099451c76a95a93e0000002d2000be879091690c0007a25900008060004f400045ec1e1c081c040000230000aa200035c7be1f00006ec7e6668b3a29c0004f80000002a865eb5ec180d0176aa4618218aac8ac64aa6c0003620002104de9e800000011ea3681e5c600079a00080e00000026a0007da00099a6d40000000005b22662ec652b9600088c2ba00000000082600000039c30a3eca3e000ace0c00000007c69f20005060008120000e82fc6ee630856c1c1f6bf2b9a2942420000000002ea9fe00058444c000b240005e81fc000bee0007689285602328a21388641b20004b800038800055691e9ea52c772b2224813a1e00000642dc9d018876696a57492062a2cc1568963e031e2707b000032cb12b4a01e072730850c569308b007a4681ae2ac34c09221a1465ea344b140002540009
  | 9 => 0x818c1095e0b4000c3c8403de3e20009fa5e49cabfeb8c0001d0000000000a060004ec000526a126f6000000296180bea080410000000000000000000000000000000000622a64a520003be0003aa892540ab01788e46c837c33456a7107a0472542aba000060328c3441a23643ca80000000a24aa60000000000000de5866d6bb68d42580000000fea426ca68e6d8b7260a00059c00000092e000bda0008e8bba000a900000002da4e2004000c025220009500005ae0000d40007800007f0c4407850a4d20005f0332524bdec4a29898a000000000000c0074eae83060aa1227a46aa33a2de61476c962310acc5489060b26c669a0ba50400000080c6e00006541b000024c00015a9da012b62000c14c16b0e2ce00048e84eb384aa00033e2380009c40001ec6e22d000092227eb94000000000000000000000000afe000b1e4c000031a72200000087400056676400000003c3ca7865feb162f473e38c1b65540080009de000a8ea327d814a5280000000003a0a667d6aa0a28a342a46163508528e01183f44ae2602801f87e28d00989ee81086e37e48444235e7d29c2c2c5ccaae64c03683ac2600061255c07e55813c0021325100005329f035854c70823e0004e800024094064e2867fc6f25683dca089380003840001ce8088600000002ca00056463a8d8862a7a3860003f0000000184bc600000000037a214b4200000000000057031c0000000009263e800000085c0002b0000000572bfc6e4a62000000000ae40006a82f276200026800091c69e000000000000798c08000000b708c666e0004ca25a61a8b6c5017a394b1000044ebc201a37450200036e000a680008f2bbc7ce000608be64b469068400014448c5d697a94e6d2b861be47c00c878c0a89034abe092a7f29e604828265c47e97c626b2a02c0009ac30420c494bf02b21aa000b8442a0004c4030000b26bb00008a80f80002e8ad85e600002a1c81a2338bd478a0000b6000000b36954000b5c458ac03d64be9d60008002d62f0a78c664a8b6e320a980000009ba99600078c000000000a2e00080245a000000b6600077e02000046c0b80521d400000005000e0008844d60009749e00005f4000c3a12c000a5c61085821c24e7600003fc2ee000000ade00000000016c5441140009103a4518000194a0a5622888ce4180000001c6000000000000000000936000000000b2e2b80000000000004748e2000000948a7046609e92c478a0200001600046a1580000002aa95ca1877c1fa700bb80000000006284e415444470c2fe6a6886000000638bdc70e5b83c0bf4620972068000000c54348a4e8a634616a48a8ea96ea442d878239a72c116b466c000672a046c6c7aa98c8441a87460ceb3000015ea6a08ebaeab64a208c0bc9c07ac160c585f603a2220002beb800008aa01
  | 10 => 0x3ce50c3d800077a86a1cc00000093c0cc1caa1400a3369f80883da3e4b6016e6bc9ec0e6096b0a79ead095832a4f205629a52e23c000b1aa2a5dc10c5bc0003924960002e0000c6aa5e78e6788ee06e74438245c40a80404a460c0e85e000a962060005d840e38071e8f45a8a60640b32876462252bc43c849a8a02e656eb0c01cc309e219200068869641279200049e53ca4081400099c1d280a6e87b25127f82924547c841e94a000000000000000000000b20ba272000090047a14294ca1e43a6ac834000b1c3429663a60003005b40beada99862c66663cb9c7f479c30234098460ea920d859e402ac2a8c000000000000014978000000000a486c45b0000000c686deabe0009520945461900001342280004a4000704000b828ba2ae00000019e1645945bab34b900000004a600000000024a4ea14e00036c1de00000003e000c2a00000043eb520007887ae91a09072e7fe0000000700002a05c8b064560dc0003608ca13e000aaa7e08460001a635a000000796000904a7e05e0001403b2702c4c5eca168da04c6b000084c0007ca0008806d08cc000000000a880000e07ba6b60000004b04a00005504ccb68bf600009c6465ca07c7c26a240c5e2106b40514636992578130872838b7aaf05a60ca05a4c84346ceb9871c87e6348f01269b81509763ea4e00624b60a81bc2c60761da41c1f2b3c6e68c067686c9a02a273605c4d04dca2040051a680318ab8752022c12828220582c040f020484836830855a5c015c596bb27743b817e5fcbd65b65c26a489e042c6e88a170b6a83ca4a1667186f098857e32eab28c46f44fc53a2b47a86628167285d09cca9c60237229000008abaa3d43cc000c5a8320eab8e4fe00059aa0c60476e2748fe208bceb440a44ee63e6820008420000002c25d2c5e424afc0008b4000aa80006603224ce98ea9e4507c427c0b07549a6b4c4261d85ac5be18aba83a2bcc234ac64982c00006980009a8000c320009ae1ac7e812e0000000000000c422a3b40007fa39e00026c00000011219c0f691200000090800005427a000000000470000b7ea266560004da5da00000000000000000000000000000067000000022600000000052a00075a4321a41fe2b6990af60000000000000005a0a00624a9a36689875c0c20000000f200093a7f69b400000065a3b00009d8534000bfa000afaaf46aea862767cc28a57c0009249be54a53e6fa0ecbf86866b43f8b78ac44c2a224e644a8821048f87266fc07482c4141c2b646927389e4b183903f699e136956a763a88be1620009b249270a14c7ec58a7163fe650a54370352c421dc724b9e56c46e2467407a65f225e4d49bc73c284c4064466a7b8bc0aee88e732a2c7b646421eb5685a43084a0380fc48854e5e0520598196c22000ad4000986be40a6b02486
  | 11 => 0x2c4a6e0009147c0c4e480b04a3003287097e4f0000b5444026eba43ee034000000bc87d400000030e552448ad68dc0
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe72d9010004ed72d90100047e75990100047d7599010004bd76990100053d75990100063e65990100063d65990100063e7599010004bd75990100063d75990100043d75990100063e65590100063d6559010004bf75590100063e75590100063d75590100047e75190100047d7519010004be7419010004de7319010004dd7319010004ee7219010004ed7219010004f671190100047f76d50100047d76d50100063e64d50100063d64d5010004bf7695010004bd76950100053d75950100063e65950100063d65950100047f76550100047d76550100063f64550100063e64550100063d64550100063c6455010004bf7655010004bd76550100063f65550100063e65550100063d65550100063c65550100053f76550100063f76550100043f76550100063e76550100053d76550100063d76550100043d76550100063c76550100047e75d8c100047d75d8c10004be74d8c10004bd74d8c100063d54d8c10004ee72d8c10004ed72d8c100063d5498c10004dd7698c100065e6598c100065d6598c100069e6498c100069d6498c100071d5498c100065f5498c100069e5498c100065d5498c100069d5498c100061d5498c100063d5458c100065e6558c100065d6558c100069e6458c100069d6458c100071d5458c100065f5458c100069e5458c100065d5458c100069d5458c100061d5458c100047e7518c100047d7518c10004be7418c10004bd7418c100063d5418c10004de7318c10004ee7218c10004ed7218c10004f67118c100047e75d88100047d75d8810004be74d8810004bd74d88100063d54d8810004de73d8810004dd73d88100063d5498810004ed76988100066e65988100066d6598810006ae6498810006ad64988100072d5498810006ce6398810006cd63988100066f5498810006ae54988100066d5498810006ad54988100062d54988100063d54588100066e65588100066d6558810006ae6458810006ad64588100072d5458810006ce6358810006cd63588100066f5458810006ae54588100066d5458810006ad54588100062d5458810006e471588100047e75188100047d7518810004be7418810004bd74188100063d5418810004de7318810004dd7318810004ee7218810004f67118810004fa70188100063d5498410004f576c84100067565c8410006b564c84100073554c8410006d563c8410006e562c8410004f57608410006756508410006b56408410007355408410006d56308410006e56208410005f170084100063d54980100067565c4010006b564c40100073554c4010006d563c4010006e562c4010004f97684010007395484010006e96284010004f77644010006756544010006b56444010007355444010006d56344010005e47244010006e56244010004fb7644010007395444010006e96244010
  | 1 => 0x8e100047f7558e100047c7558e10004bf7458e10004bc7458e100063d5458e100047e7518e100047d7518e10004be7418e10004bd7418e100063d5418e10004ee7218e10004ed7218e100063d54d8a100063d5498a100063d5458a100047e7518a100047d7518a10004be7418a10004bd7418a100063d5418a10004de7318a10004dd7318a100073554c8610007355408610006e76208610005f17008610007395488210007e02188210007395448210005f07148210007e321482100073554c42100073954c4210004be7499510004bd7499510004ee7299510004ed7299510004ef7259510004ec7259510004be7419510004bd74195100047e75991100047d7599110004ee7299110004ed7299110004ef7259110004ec72591100047e75191100047d75191100053d75951100063f64551100063e64551100063d64551100063c64551100063f65551100063e65551100063d65551100063c65551100063f76551100063e76551100063d76551100063c76551100073671551100073571551100063d54d8d100063d5498d10004ee7298d10004ed7298d100047f7558d100047c7558d10004bf7458d10004bc7458d100063d5458d10004ef7258d10004ec7258d100063d5418d100063d54d89100072d54d89100066f54d8910006ae54d89100066d54d8910006ad54d89100062d54d89100063d5498910004ee72989100063d5458910004f771589100047e75189100047d7518910004be7418910004bd74189100063d5418910004de7318910004dd7318910004ee76189100072d54189100066e75189100066d7518910006ae7418910006ad74189100066f5418910006ae54189100066d5418910006ad54189100062d5418910006ce7318910006cd7318910006e57118910006e97018910007355494510006e46294510004f47654510007355454510006e46254510007355490510006e46290510004f47650510007355450510006e4625051000575758c510005b5748c51000735548c510006e4628c510004f4764c51000735544c510006e4624c510004f67688510007355488510006e46288510004f47648510007355448510006e46248510007395488110006e86288110007e22188110004f87648110007395448110007e121481100073954c4110007355484110006e46284110004be74d9410004bd74d9410004de73d9410004dd73d9410004ee72d9410004ed72d9410004be7499410004bd74994100047d76994100053d74994100063e74994100047d74994100063d74994100043d74994100047f74594100063e74594100063d74594100047e7519410004be7419410004bd7419410004de7319410004dd7319410004ee7219410004ed7219410004f671194100047e75d90100047d75d9010004de73d9010004dd73d9010004e
  | 2 => 0x69d6498c200071d5498c200065f5498c200069e5498c200065d5498c200069d5498c200061d5498c200063d5458c200065e6558c200065d6558c200069e6458c200069d6458c200071d5458c200065f5458c200069e5458c200065d5458c200069d5458c200061d5458c200047e7518c200047d7518c20004be7418c20004bd7418c200063d5418c20004de7318c20004ee7218c20004f67118c20004f57118c200063d54988200063d5498420006766598420006756598420006b66498420006b56498420007355498420006d66398420006d56398420006775498420006b65498420006755498420006b554984200063554984200063d5458420006766558420006756558420006b66458420006b56458420007355458420006d66358420006d56358420006775458420006b65458420006755458420006b55458420006355458420004ed76884200066d6588420006ad64884200072d5488420006cd6388420006e561884200066d6508420006ad64084200072d5408420006cd6308420006e56108420005e970084200063d54980200066d65c8020006ad64c80200072d54c8020006cd63c8020006e561c8020007395488020006f16188020004ef76480200066d6548020006ad64480200072d5448020006cd6348020005e47148020006e56148020004fb7648020007395448020006f16148020004be7499710004bd7499710004ee7299710004ed7299710004be7419710004bd74197100047e75993100047d7599310004ee7299310004ed72993100047e75193100047d75193100063f64553100063e64553100063d64553100063c64553100063f65553100063e65553100063d65553100063c65553100063f76553100063e76553100063d76553100063c76553100073671553100073571553100047e75d8f100047d75d8f10004be74d8f10004bd74d8f100063d54d8f100063d5498f10004ee7298f10004ed7298f100063d5458f100063d5418f100063d54d8b100063d5498b100063d5458b100047e7518b100047d7518b10004be7418b10004bd7418b100063d5418b10004de7318b10004dd7318b1000735549471000735545471000735549071000735545071000575758c710005b5748c71000735548c71000735544c710007355488710007355448710006e46248710004be7499610004bd7499610004be7419610004bd7419610004de7319610004dd7319610004ee7219610004ed72196100047e75992100047d75992100047e75192100047d7519210004de7319210004dd7319210004ee7219210004ed72192100063f64552100063e64552100063d64552100063c64552100063f65552100063e65552100063d65552100063c65552100063f76552100063e76552100063d76552100063c76552100063d54d8e100063d549
  | 3 => 0xd64551200063c64551200063f65551200063e65551200063d65551200063c65551200063f76551200063e76551200063d76551200063c76551200072e72551200072d72551200063d54d8d200063d5498d20004f67198d20004f57198d200047f7558d200047c7558d20004bf7458d20004bc7458d200063d5458d20004f77158d20004f47158d200063d5418d200072d5494920004ec76549200072d54549200072d5490920004ec76509200072d54509200056d758c920005ad748c9200072d548c920004ec764c9200072d544c9200063d54d85200073554d85200067754d8520006b654d85200067554d8520006b554d85200063554d85200047e75185200047d7518520004be7418520004bd74185200063d5418520004de7318520004dd7318520007355418520006767518520006757518520006b67418520006b57418520006775418520006b65418520006755418520006b55418520006355418520006d67318520006d57318520006e65218520006e55218520006e64218520006e54218520006e63218520006e53218520006f17018520004ee76c85200072d54c8520006e461c85200072d5448520006e461485200073954c81200072d5488120006e46188120004be74d9420004bd74d9420004de73d9420004dd73d9420004f671d9420004f571d9420004be7499420004bd74994200047d76994200053d74994200063e74994200047d74994200063d74994200043d74994200047f74594200063e74594200063d74594200047e7519420004be7419420004bd7419420004de7319420004dd7319420004ee7219420004f67119420004f571194200047e75d90200047d75d9020004de73d9020004dd73d9020004f671d9020004f571d90200047e75990200047d7599020004bd76990200053d75990200063e65990200063d65990200063e7599020004bd75990200063d75990200043d75990200063e65590200063d6559020004bf75590200063e75590200063d75590200047e75190200047d7519020004be7419020004de7319020004dd7319020004ee7219020004f67119020004f571190200047f76d50200047d76d50200063e64d50200063d64d5020004bf7695020004bd76950200053d75950200063e65950200063d65950200047f76550200047d76550200063f64550200063e64550200063d64550200063c6455020004bf7655020004bd76550200063f65550200063e65550200063d65550200063c65550200053f76550200063f76550200043f76550200063e76550200053d76550200063d76550200043d76550200063c76550200047e75d8c200047d75d8c20004be74d8c20004bd74d8c200063d54d8c20004f671d8c20004f571d8c200063d5498c20004dd7698c200065e6598c200065d6598c200069e6498c20
  | 4 => 0x88300066d6558830006ae6458830006ad64588300072d54588300066f5458830006ae54588300066d5458830006ad54588300062d54588300063d5498430006766598430006756598430006b66498430006b56498430007355498430006e66298430006e56298430006775498430006b65498430006755498430006b554984300063554984300063d5458430006766558430006756558430006b66458430006b56458430007355458430006e66258430006e56258430006775458430006b65458430006755458430006b554584300063554584300063d54980300065d65cc0300069d64cc0300071d54cc030006cd62cc030006d561cc03000679658c030006b9648c03000739548c030004df764c0300065d654c0300069d644c0300071d544c030006cd624c030006d5614c030004fb764c03000679654c030006b9644c03000739544c030004be7499720004bd7499720004f67199720004f57199720004be7419720004bd74197200047e75993200047d7599320004f67199320004f571993200047e75193200047d75193200063f64553200063e64553200063d64553200063c64553200063f65553200063e65553200063d65553200063c65553200063f76553200063e76553200063d76553200063c76553200072e72553200072d72553200047e75d8f200047d75d8f20004be74d8f20004bd74d8f200063d54d8f200063d5498f20004f67198f20004f57198f200063d5458f200063d5418f200072d5494b200072d5454b200072d5490b200072d5450b200056d758cb20005ad748cb200072d548cb200072d544cb200063d54987200063d54587200072d54c87200072d5448720004be7499620004bd7499620004be7419620004bd7419620004de7319620004dd7319620004f67119620004f571196200047e75992200047d75992200047e75192200047d7519220004de7319220004dd7319220004f67119220004f571192200063f64552200063e64552200063d64552200063c64552200063f65552200063e65552200063d65552200063c65552200063f76552200063e76552200063d76552200063c76552200063d54d8e200063d5498e200047f7558e200047c7558e20004bf7458e20004bc7458e200063d5458e200047e7518e200047d7518e20004be7418e20004bd7418e200063d5418e20004f67118e20004f57118e200063d54986200063d54586200072d54886200072d5408620005e970086200072d54c82200073954c8220004be7499520004bd7499520004f67199520004f57199520004f77159520004f47159520004be7419520004bd74195200047e75991200047d7599120004f67199120004f57199120004f77159120004f471591200047e75191200047d75191200053d75951200063f64551200063e64551200063
  | 5 => 0x6ae7219130006ad7219130006b67119130006b57119130006b970191300047e76d51300047c76d51300063f64d51300063c64d5130004be7695130004bc76951300053d75951300063f65951300063c65951300047e76551300047c76551300063f64551300063e64551300063d64551300063c6455130004be7655130004bc76551300063f65551300063e65551300063d65551300063c65551300063f76551300053e76551300063e76551300043e76551300063d76551300053c76551300063c76551300043c76551300071e73551300071d73551300073a70551300073970551300065c6594d300071d5494d30004dc7654d300071d5454d300069c6490d300071d5490d30004dc7650d300071d5450d300063d54d89300063d54189300071d54cc930005d571cc9300071d544c9300063d54d85300063d54185300071d54cc530005cd72cc5300071d544c5300067865941300073954941300075a5394130004f87654130007395454130007595354130006b864901300073954901300079a4390130004f876501300073954501300079943501300073954cc1300071d548c130004be74d9430004bd74d9430004ee72d9430004ed72d9430004f671d9430004f571d9430004be7499430004bd74994300047d76994300053d74994300063e74994300047d74994300063d74994300043d74994300047f74594300063e74594300063d74594300047e7519430004be7419430004bd7419430004de7319430004ee7219430004ed7219430004f67119430004f57119430004fa70194300047e75d90300047d75d9030004ee72d9030004ed72d9030004f671d9030004f571d90300047e75990300047d7599030004bd76990300053d75990300063e65990300063d65990300063e7599030004bd75990300063d75990300043d75990300063e65590300063d6559030004bf75590300063e75590300063d75590300047e75190300047d7519030004be7419030004de7319030004ee7219030004ed7219030004f67119030004f57119030004fa70190300047f76d50300047d76d50300063e64d50300063d64d5030004bf7695030004bd76950300053d75950300063e65950300063d65950300047f76550300047d76550300063f64550300063e64550300063d64550300063c6455030004bf7655030004bd76550300063f65550300063e65550300063d65550300063c65550300053f76550300063f76550300043f76550300063e76550300053d76550300063d76550300043d76550300063c76550300071f73550300071c73550300063d5498c300063d54988300066e65988300066d6598830006ae6498830006ad64988300072d54988300066f5498830006ae54988300066d5498830006ad54988300062d54988300063d54588300066e655
  | 6 => 0x75458440006b65458440006755458440006b55458440006355458440006b64358440006b443584400063d54980400053d75d00400063d65d00400069d63d0040006ad62d0040006b561d0040007395490040006d96390040004bf76500400063d65500400069d6350040006ad6250040006b56150040004fb7650040006d96350040004be7499730004bd7499730004be7419730004bd7419730004ee7219730004ed7219730004f67119730004f571197300047e75993300047d75993300047e75193300047d7519330004ee7219330004ed7219330004f67119330004f571193300063f64553300063e64553300063d64553300063c64553300063f65553300063e65553300063d65553300063c65553300063f76553300063e76553300063d76553300063c76553300071e73553300071d73553300071d5494f300071d5454f300071d5490f300071d5450f300047e7598b300047d7598b30004be7498b30004bd7498b300063d5498b300063d5458b300071d54ccb30005d571ccb300071d544cb300047e75987300047d7598730004be7498730004bd74987300063d54987300063d54587300071d54cc730005cd72cc7300071d544c730004be7499630004bd7499630004be7419630004bd7419630004ee7219630004ed7219630004f67119630004f571196300047e75992300047d75992300047e75192300047d7519230004ee7219230004ed7219230004f67119230004f571192300063f64552300063e64552300063d64552300063c64552300063f65552300063e65552300063d65552300063c65552300063f76552300063e76552300063d76552300063c76552300071f73552300071c73552300073a70552300073970552300063d5498a300063d5458a30004f77158a30004f47158a300063d54986300063d5458630004ef7258630004ec72586300073954942300073954542300073954902300073954502300071d54cc2300073954cc2300063f74d95300047d74d95300063c74d95300047e7599530004be7499530004bd7499530004bf7459530004bc7459530004be7419530004bd7419530004ee7219530004ed7219530004f67119530004f571195300047e76195300053d74195300063e74195300047d74195300063d74195300043d74195300065d73195300066e72195300066d72195300067671195300067571195300067970195300063f65d91300063c65d91300063f75d9130004bd75d91300063c75d91300047e75991300047d7599130004be74991300047f75591300047c75591300047e75191300047d7519130004ee7219130004ed7219130004f67119130004f57119130004be76191300053d75191300063f65191300063c65191300063e7519130004bd75191300063d75191300043d75191300069d7319130
  | 7 => 0x9640004dd7319640004ee7219640004ed7219640004f67119640004f571196400063e65552400063d65552400063f76552400063c76552400073b70552400073870552400063d5498e400047f7558e400047c7558e400063d5458e400053d7510e40005b97010e400063d5498a400063d5458a40004f77158a40004f47158a400063d54986400063d5458640004ef7258640004ec72586400053d75d02400073954d0240004bd7499540004df7359540004dc7359540004be74195400053d7595140004bc76551400063f65551400063c65551400063f76551400063e76551400063d76551400063c76551400073b70551400073870551400063d54d8d400047e7518d400047d7518d400063d5418d40004ee7218d40004ed7218d40004f67118d40004f57118d40004be76d0d400053d75d0d400063d54d89400047e75189400047d75189400063d54189400053d75d0940005b571d09400063d54d85400047e75185400047d75185400063d54185400053d75d0540005ad72d05400073954d0140004de73d9440004dd73d9440004ee72d9440004ed72d9440004f671d9440004f571d94400047d76994400063e7499440004bd74594400047f74594400063e74594400047d74594400043d74594400047e7519440004be7419440004de7319440004dd7319440004ee7219440004ed7219440004f67119440004f571194400047e75990400047d75990400047d76d5040004bd76950400053d75950400063e65950400063d65950400047f76550400063e64550400063f65550400063e65550400063d65550400063c65550400053f76550400063f76550400063d5498c400065e6598c400065d6598c400071d5498c400065f5498c400069e5498c400065d5498c400069d5498c400061d5498c400063d5458c400065e6558c400065d6558c400071d5458c400065f5458c400069e5458c400065d5458c400069d5458c400061d5458c40004bd7690c400063d6590c400069d6390c400053d7510c400063d6510c400069d6310c40005b97010c400063d54988400066e65988400066d65988400072d5498840006ce6398840006cd63988400066f5498840006ae54988400066d5498840006ad54988400062d54988400063d54588400066e65588400066d65588400072d5458840006ce6358840006cd63588400066f5458840006ae54588400066d5458840006ad54588400062d5458840006ae4358840006ac43588400063d5498440006766598440006756598440007355498440006d66398440006d56398440006e66298440006e56298440006775498440006b65498440006755498440006b554984400063554984400063d5458440006766558440006756558440007355458440006d66358440006d56358440006e66258440006e562584400067
  | 8 => 0x63d5458e500053d7414e50005797014e500063d5498a500063d5458a50004f77158a50004f47158a500063d54986500063d5458650004ef7258650004ec72586500053d74d42500073954d42500053d75951500063f64551500063c64551500073b70551500073870551500063d54d8d50004be7418d50004bd7418d500063d5418d50004ee7218d50004ed7218d50004f67118d50004f57118d500047e76d4d500053d74d4d500063d54d8950004be7418950004bd74189500063d54189500053d74d49500057571d49500063d54d8550004be7418550004bd74185500063d54185500053d74d45500056d72d45500073954d41500063e75590500063e64d50500063d64d5050004bd76950500053d75950500063e6455050004bf76550500063e65550500053f76550500063f76550500063d5498c500069e6498c500069d6498c500071d5498c500065f5498c500069e5498c500065d5498c500069d5498c500061d5498c500063d5458c500069e6458c500069d6458c500071d5458c500065f5458c500069e5458c500065d5458c500069d5458c500061d5458c500047d7694c500063d6494c500065d6394c500053d7414c500063d6414c500065d6314c50005797014c500063d5498850006ae6498850006ad64988500072d5498850006ce6398850006cd63988500066f5498850006ae54988500066d5498850006ad54988500062d54988500063d5458850006ae6458850006ad64588500072d5458850006ce6358850006cd63588500066f5458850006ae54588500066d5458850006ad54588500062d54588500066e53588500066c53588500063d5498450006b66498450006b56498450007355498450006d66398450006d56398450006e66298450006e56298450006775498450006b65498450006755498450006b554984500063554984500063d5458450006b66458450006b56458450007355458450006d66358450006d56358450006e66258450006e56258450006775458450006b65458450006755458450006b554584500063554584500067653584500067453584500063d54980500053d74d40500063d64d40500065d63d40500066d62d40500067561d4050007395494050006d963940500047f76540500063d64540500065d63540500066d6254050006756154050004fb7654050006d963540500063e74997400063e74597400063e65953400063d65953400063f65553400063e65553400063d65553400063c65553400053f76553400063f76553400063d5498f400063d5458f400053d75d0f400063d65d0f400063d6550f400063d5498b400063d5458b400053d75d0b400063d65d0b40005b571d0b400063d6550b400063d54987400063d54587400053d75d07400063d65d0740005ad72d07400063d6550740004de731
  | 9 => 0xf5458c210069e5458c210065d5458c210069d5458c210061d5458c210047e7518c210047d7518c21004be7418c21004bd7418c210063d5418c21004de7318c21004fa7018c21004f97018c210063d5498821004ed76948210072d5494821006cd6394821005e571948210066e65548210072d5454821006cd6354821004ed76908210072d5490821006cd6390821005e57190821006ae64508210072d5450821006cd6350821004ed768c8210056d758c8210066d658c821005ad748c821006ad648c8210072d548c821005e5718c8210066d654c821006ad644c8210072d544c821006ce634c8210063d5498421004f57694421007355494421006d56394421005e57294421006766554421007355454421006d56354421007655254421004f57690421007355490421006d56390421005e57290421006b66450421007355450421006d56350421007a54250421004f5768c42100575758c42100675658c421005b5748c421006b5648c42100735548c421005e5728c42100675654c421006b5644c42100735544c421006d6634c421007c5324c4210072d54c8421007355488421005e57288421004ef76484210072d5448421004f77648421007355448421005e77648421006e77648421005e77548421005e57548421007666548421007656548421005e77448421005e57448421007a66448421007a56448421007675448421007a65448421007655448421007a55448421007255448421005e77348421005e57348421007c66348421007c56348421005e470484210063d54980210067a6598021006796598021006ba6498021006b96498021007395498021006da6398021006d96398021007e121980210067b5498021006ba5498021006795498021006b954980210063954980210063d5458021006e521580210067a6558021006796558021006ba6458021006b96458021007395458021006da6358021006d96358021007e121580210067b5458021006ba5458021006795458021006b95458021006395458021006ea5258021006e95258021006ea4258021006e94258021006ea3258021006e93258021006f25158021006f15158021006f24158021006f14158021006f23158021006f13158021006eb2158021006f22158021006e92158021006f12158021006e121580210063e75593500063e64d53500063d64d53500063e64553500053f76553500063f76553500063d5498f500063d5458f500053d74d4f500063d64d4f500063d6454f500063d5498b500063d5458b500053d74d4b500063d64d4b500057571d4b500063d6454b500063d54987500063d54587500053d74d47500063d64d47500056d72d47500063d64547500063e64552500063d64552500073b70552500073870552500063d5498e50004bf7458e50004bc7458e50
  | 10 => 0xa210072d5450a210056d758ca21005ad748ca210072d548ca210072d544ca210072d54c86210073554c86210063d54982210063d5458221004be7499521004bd7499521004ed7299521004f57199521004be7419521004bd74195210047e75991210047d7599121004ed7299121004f571991210047e75191210047d75191210053d75951210063f64551210063e64551210063d64551210063c64551210063f65551210063e65551210063d65551210063c65551210063f76551210063e76551210063d76551210063c76551210047e75d8d210047d75d8d21004be74d8d21004bd74d8d210063d54d8d210063d5498d21004ed7298d21004f57198d210063d5458d210063d5418d210073554c85210072d54885210063d54d81210047e75181210047d7518121004be7418121004bd74181210063d5418121004de7318121004dd7318121004be74d9421004bd74d9421004de73d9421004dd73d9421004fa70d9421004f970d9421004be7499421004bd74994210047d76994210053d74994210063e74994210047d74994210063d74994210043d74994210066e72994210067671994210047f74594210063e74594210063d74594210047e7519421004be7419421004bd7419421004de7319421004dd7319421004fa7019421004f970194210047e75d90210047d75d9021004de73d9021004dd73d9021004fa70d9021004f970d90210047e75990210047d7599021004bd76990210053d75990210063e65990210063d65990210063e7599021004bd75990210063d75990210043d7599021006ae7299021006b671990210063e65590210063d6559021004bf75590210063e75590210063d75590210047e75190210047d7519021004be7419021004de7319021004dd7319021004fa7019021004f970190210047f76d50210047d76d50210063e64d50210063d64d5021004bf7695021004bd76950210053d75950210063e65950210063d65950210047f76550210047d76550210063f64550210063e64550210063d64550210063c6455021004bf7655021004bd76550210063f65550210063e65550210063d65550210063c65550210053f76550210063f76550210043f76550210063e76550210053d76550210063d76550210043d76550210063c76550210072e72550210072d72550210073671550210073571550210047e75d8c210047d75d8c21004be74d8c21004bd74d8c210063d54d8c21004fa70d8c21004f970d8c210063d5498c21004dd7698c210065e6598c210065d6598c210069e6498c210069d6498c210071d5498c210065f5498c210069e5498c210065d5498c210069d5498c210061d5498c21006ce7298c21006d67198c210063d5458c210065e6558c210065d6558c210069e6458c210069d6458c210071d5458c210065
  | 11 => 0x4be7499531004bd7499531004ee7299531004ed7299531004be7419531004bd74195310047e75991310047d7599131004ee7299131004ed72991310047e75191310047d75191310053d75951310063f64551310063e64551310063d64551310063c64551310063f65551310063e65551310063d65551310063c65551310063f76551310063e76551310063d76551310063c76551310071f73551310071c73551310073671551310073571551310063d54d89310063d54189310071d54cc931005d671cc9310071d544c931007355494531004f47654531007355454531007355490531004f476505310073554505310073554cc531005e672cc5310071d548c5310063d54d81310047e75181310047d7518131004be7418131004bd74181310063d5418131004ee7218131004ed7218131004be7499431004bd7499431004be7419431004bd7419431004ee7219431004ed7219431004f67119431004fa7019431004f970194310047e75990310047d75990310047e75190310047d7519031004ee7219031004ed7219031004f67119031004fa7019031004f970190310053d75950310063f64550310063e64550310063d64550310063c64550310063f65550310063e65550310063d65550310063c65550310063f76550310063e76550310063d76550310063c76550310063d5498c310063d54988310063d54588310047e75984310047d7598431004be7498431004bd74984310063d54984310071d54cc43100735548c431004df764c4310071d544c431004f7764c43100735544c4310063d54980310063d5458031004be7499721004bd7499721004be7419721004bd74197210047e75993210047d75993210047e75193210047d75193210063f64553210063e64553210063d64553210063c64553210063f65553210063e65553210063d65553210063c65553210063f76553210063e76553210063d76553210063c76553210073671553210073571553210047e75d8f210047d75d8f21004be74d8f21004bd74d8f210063d54d8f210063d5498f210063d5458f210063d5418f2100735549472100735545472100735549072100735545072100575758c721005b5748c72100735548c72100735544c7210063d54983210063d5458321004be7499621004bd7499621004be7419621004bd74196210047e75992210047d75992210047e75192210047d75192210063f64552210063e64552210063d64552210063c64552210063f65552210063e65552210063d65552210063c65552210063f76552210063e76552210063d76552210063c76552210072e72552210072d72552210047e75d8e210047d75d8e21004be74d8e21004bd74d8e210063d54d8e210063d5498e210063d5458e210063d5418e210072d5494a210072d5454a210072d549
  | 12 => 0xd76950410053d75950410063e65950410063d65950410047f76550410063e64550410063f65550410063e65550410063d65550410063c65550410053f76550410063f76550410063d5498c410063d5458c410063d54988410063d54588410063d54984410053d75d04410063d65d0441007355490441004bf76504410063d6550441004f776504410063d54980410063d5458041004ee72d9731004ed72d9731004be7499731004bd7499731004be7419731004bd7419731004ee7219731004ed7219731004fa7019731004f97019731004ee72d9331004ed72d93310047e75993310047d75993310047e75193310047d7519331004ee7219331004ed7219331004fa7019331004f970193310063f64553310063e64553310063d64553310063c64553310063f65553310063e65553310063d65553310063c65553310063f76553310063e76553310063d76553310063c76553310071f73553310071c73553310047e7598b310047d7598b31004be7498b31004bd7498b310063d5498b310072d5498b310066e7598b310066d7598b31006ae7498b31006ad7498b310066f5498b31006ae5498b310066d5498b31006ad5498b310062d5498b310063d5458b310072d5458b310066f5458b31006ae5458b310066d5458b31006ad5458b310062d5458b310071d54ccb310071d544cb31006ce624cb310063d54983310063d5458331004be74d9631004bd74d9631004be7499631004bd7499631004ee7299631004ed72996310053d74996310063e74996310047d74996310063d74996310043d74996310066e72996310066d72996310067671996310047f74596310063e74596310063d7459631004be7419631004bd74196310047e75d92310047d75d92310047e75992310047d7599231004ee7299231004ed72992310053d75992310063e65992310063d65992310063e7599231004bd75992310063d75992310043d7599231006ae7299231006ad7299231006b671992310063e65592310063d6559231004bf75592310063e75592310063d75592310047e75192310047d75192310047f76d52310047d76d52310063e64d52310063d64d5231004bf7695231004bd76952310063e65952310063d65952310047f76552310047d76552310063f64552310063e64552310063d64552310063c6455231004bf7655231004bd76552310063f65552310063e65552310063d65552310063c65552310053f76552310063f76552310043f76552310063e76552310053d76552310063d76552310043d76552310063c76552310073671552310073571552310063d5498a310063d5458a31007355494631006766554631007355454631007355490631006b664506310073554506310071d54cc6310073554cc631005e672cc6310063d54982310063d5458231
  | 13 => 0x8e510063d5498a510063d5458a510053d74d46510073554d4651005e672d46510063d54982510063d54582510053d75951510063f64551510063c6455151007377155151007347155151004be74d8d51004bd74d8d510063d54d8d510063d5418d510053d7414d510056d7214d51005767114d51005797014d510063d54d8951004be7418951004bd74189510063d54189510053d74d49510057671d49510073554d4551005e672d45510063d54d8151004be7418151004bd74181510063d5418151004de7318151004dd7318151004ee7218151004ed72181510063e75590510063e64d50510063d64d5051004bd76950510053d75950510063e6455051004bf76550510063e65550510053f76550510063f76550510063d5498c510063d5458c510063d54988510063d54588510063d54984510053d74d44510063d64d44510073554944510047f76544510063d6454451004f776544510063d54980510063d5458051004ee72d9741004ed72d97410063e74997410063e7459741004ee7219741004ed72197410063e65953410063d65953410063f65553410063e65553410063d65553410063c65553410053f76553410063f76553410063d5498f410063d5458f410063d6590f410053d7510f410063d6510f41005ad7210f41005b97010f410063d5498b410066e6598b410066d6598b410072d5498b410066f5498b41006ae5498b410066d5498b41006ad5498b410062d5498b410063d5458b410066e6558b410066d6558b410072d5458b410066f5458b41006ae5458b410066d5458b41006ad5458b410062d5458b41006ae4358b41006ac4358b410053d75d0b410063d65d0b410063d6550b41006ae6250b410063d54983410063d5458341004de73d9641004dd73d96410063e65552410063d65552410063f76552410063c76552410073771552410073471552410063d5498e41004ee7298e41004ed7298e410063d5458e410063d5498a410063d5458a410053d75d06410073554d0641005e672d06410063d54982410063d5458241004bd7499541004ee7299541004ed72995410053d7595141004bc76551410063f65551410063c65551410063f76551410063e76551410063d76551410063c76551410073771551410073471551410047e75d8d410047d75d8d410063d54d8d410063d5418d410053d7510d41005ad7210d41005b67110d41005b97010d410063d54d89410047e75189410047d75189410063d54189410053d75d0941005b671d09410073554d0541005e672d05410063d54d81410047e75181410047d75181410063d5418141004de7318141004dd7318141004ee7218141004ed72181410047d76994410063e74994410063e74594410047e7519441004be74194410047e75990410047d75990410047d76d5041004b
  | 14 => 0x4bf7655232004bd76552320063f65552320063e65552320063d65552320063c65552320053f76552320063f76552320043f76552320063e76552320053d76552320063d76552320043d76552320063c76552320072e72552320072d72552320072d5494a320066e6554a320072d5454a320072d5490a32006ae6450a320072d5450a320071d54cca320072d54cca32005e671cca320063d54986320063d54586320063d54982320063d5458232004be7499532004bd7499532004f67199532004f57199532004be7419532004bd74195320047e75991320047d7599132004f67199132004f571991320047e75191320047d75191320053d75951320063f64551320063e64551320063d64551320063c64551320063f65551320063e65551320063d65551320063c65551320063f76551320063e76551320063d76551320063c76551320071f73551320071c73551320072e72551320072d72551320072d5494932004ec76549320072d54549320072d5490932004ec76509320072d54509320072d54cc932005e671cc9320071d548c9320063d54d85320063d54185320063d54d81320047e75181320047d7518132004be7418132004bd74181320063d5418132004f67118132004f57118132004be7499432004bd7499432004be7419432004bd7419432004ee7219432004f67119432004f57119432004fa7019432004f970194320047e75990320047d75990320047e75190320047d7519032004ee7219032004f67119032004f57119032004fa7019032004f970190320053d75950320063f64550320063e64550320063d64550320063c64550320063f65550320063e65550320063d65550320063c65550320063f76550320063e76550320063d76550320063c76550320063d5498c320047e75988320047d7598832004be7498832004bd74988320063d54988320071d54cc8320072d548c832004df764c8320071d544c832004ef764c8320072d544c8320063d54984320063d54584320063d54980320063d54580320063e75593510063e64d53510063d64d53510063e64553510053f76553510063f76553510063d5498f510063d5458f510063d6494f510053d7414f510063d6414f510056d7214f51005797014f510063d5498b51006ae6498b51006ad6498b510072d5498b510066f5498b51006ae5498b510066d5498b51006ad5498b510062d5498b510063d5458b51006ae6458b51006ad6458b510072d5458b510066f5458b51006ae5458b510066d5458b51006ad5458b510062d5458b510066e5358b510066c5358b510053d74d4b510063d64d4b510063d6454b510066e6254b510063d54983510063d54583510063e64552510063d64552510073771552510073471552510063d5498e51004ee7298e51004ed7298e510063d545
  | 15 => 0xf72551420072c72551420047e75d8d420047d75d8d420063d54d8d420063d5418d420053d7510d42005ae7210d42005b57110d42005b97010d420072d54d0942005e671d09420063d54d85420047e75185420047d75185420063d54185420063d54d81420047e75181420047d75181420063d5418142004de7318142004dd7318142004f67118142004f571181420047d76994420063e74994420063e74594420047e7519442004be74194420047e75990420047d75990420047d76d5042004bd76950420053d75950420063e65950420063d65950420047f76550420063e64550420063f65550420063e65550420063d65550420063c65550420053f76550420063f76550420063d5498c420063d5458c420063d54988420053d75d08420063d65d08420072d5490842004bf76508420063d6550842004ef76508420063d54984420063d54584420063d54980420063d5458042004f671d9732004f571d9732004be7499732004bd7499732004be7419732004bd7419732004f67119732004f57119732004fa7019732004f97019732004f671d9332004f571d93320047e75993320047d75993320047e75193320047d7519332004f67119332004f57119332004fa7019332004f970193320063f64553320063e64553320063d64553320063c64553320063f65553320063e65553320063d65553320063c65553320063f76553320063e76553320063d76553320063c76553320071f73553320071c73553320047e75987320047d7598732004be7498732004bd74987320063d5498732007355498732006767598732006757598732006b67498732006b57498732006775498732006b65498732006755498732006b554987320063554987320063d5458732007355458732006775458732006b65458732006755458732006b554587320063554587320063d54983320063d5458332004be74d9632004bd74d9632004be7499632004bd7499632004f67199632004f571996320053d74996320063e74996320047d74996320063d74996320043d74996320066e72996320067671996320067571996320047f74596320063e74596320063d7459632004be7419632004bd74196320047e75d92320047d75d92320047e75992320047d7599232004f67199232004f571992320053d75992320063e65992320063d65992320063e7599232004bd75992320063d75992320043d7599232006ae7299232006b67199232006b571992320063e65592320063d6559232004bf75592320063e75592320063d75592320047e75192320047d75192320047f76d52320047d76d52320063e64d52320063d64d5232004bf7695232004bd76952320063e65952320063d65952320047f76552320047d76552320063f64552320063e64552320063d64552320063c6455232
  | 16 => 0x53520053f76553520063f76553520063d5498f520063d5458f520063d6494f520053d7414f520063d6414f520056e7214f52005757114f52005797014f520063d5498752006b66498752006b56498752007355498752006775498752006b65498752006755498752006b554987520063554987520063d5458752006b66458752006b56458752007355458752006775458752006b65458752006755458752006b554587520063554587520067653587520067453587520063d54983520063d54583520063e64552520063d64552520072f72552520072c72552520063d5498e52004f67198e52004f57198e520063d5458e520053d74d4a520072d54d4a52005e671d4a520063d54986520063d54586520063d54982520063d54582520053d75951520063f64551520063c64551520072f72551520072c7255152004be74d8d52004bd74d8d520063d54d8d520063d5418d520053d7414d520056e7214d52005757114d52005797014d520072d54d4952005e671d49520063d54d8552004be7418552004bd74185520063d54185520063d54d8152004be7418152004bd74181520063d5418152004de7318152004dd7318152004f67118152004f571181520063e75590520063e64d50520063d64d5052004bd76950520053d75950520063e6455052004bf76550520063e65550520053f76550520063f76550520063d5498c520063d5458c520063d54988520053d74d48520063d64d48520072d54948520047f76548520063d6454852004ef76548520063d54984520063d54584520063d54980520063d5458052004f671d9742004f571d97420063e74997420063e7459742004f67119742004f571197420063e65953420063d65953420063f65553420063e65553420063d65553420063c65553420053f76553420063f76553420063d5498f420063d5458f420063d6590f420053d7510f420063d6510f42005b57110f42005b97010f420063d5498742006766598742006756598742007355498742006775498742006b65498742006755498742006b554987420063554987420063d5458742006766558742006756558742007355458742006775458742006b65458742006755458742006b55458742006355458742006b64358742006b443587420063d54983420063d5458342004de73d9642004dd73d96420063e65552420063d65552420063f76552420063c76552420072f72552420072c72552420063d5498e42004f67198e42004f57198e420063d5458e420053d75d0a420072d54d0a42005e671d0a420063d54986420063d54586420063d54982420063d5458242004bd7499542004f67199542004f571995420053d7595142004bc76551420063f65551420063c65551420063f76551420063e76551420063d76551420063c76551420072
  | 17 => 0x63d5458343004ee7219643004ed7219643004f67119643004f57119643004fa7019643004f970196430063e65552430063d65552430063f76552430063c76552430071f73552430071c73552430053d75d0e430071d54d0e430047e7598a430047d7598a430063d5498a430063d5458a430047e75986430047d75986430063d54986430063d54586430063d54982430047f75582430047c75582430063d5458243004bd74995430053d7595143004bc76551430063f65551430063c65551430059c73551430063f76551430063e76551430063d76551430063c76551430071f73551430071c73551430071d54d0d430063d54d8943004f671d8943004f571d89430063d54189430063d54d8543004ee72d8543004ed72d85430063d54185430063d54d81430047e75181430047d75181430063d5418143004ee7218143004ed7218143004f67118143004f57118143004ee72d9443004ed72d9443004f671d9443004f571d9443004fa70d9443004f970d94430047d76994430063e74994430063e74594430047e7519443004be7419443004ee7219443004ed7219443004f67119443004f57119443004fa7019443004f970194430047e75990430047d75990430047d76d5043004bd76950430053d75950430063e65950430063d65950430059d73950430047f76550430063e64550430063f65550430063e65550430063d65550430063c65550430053f76550430063f76550430063d5498c430053d75d0c430063d65d0c430071d5490c43004bf7650c430063d6550c43004df7650c430071f5450c430063d54988430066e65988430066d65988430072d54988430066f5498843006ae54988430066d5498843006ad54988430062d54988430063d54588430066e65588430066d65588430072d54588430066f5458843006ae54588430066d5458843006ad54588430062d54588430063d5498443006766598443006756598443007355498443006e66298443006e56298443006775498443006b65498443006755498443006b554984430063554984430063d5458443006766558443006756558443007355458443006e66258443006e56258443006775458443006b65458443006755458443006b554584430063554584430063d54980430067a6598043006796598043007395498043006ea6298043006e96298043006f26198043006f161980430067b5498043006ba5498043006795498043006b954980430063954980430063d54580430067a6558043006796558043007395458043006ea6258043006e96258043006f26158043006f161580430067b5458043006ba5458043006795458043006b95458043006395458043006bb4358043006da4358043006b94358043006d943580430063e75593520063e64d53520063d64d53520063e645
  | 18 => 0xe6455054004bf76550540063e65550540053f76550540063f76550540043f76550540063d5498c540063d5458c540063d54988540063d54588540063d54984540063d54584540063d54980540063d54580540063e75593530063e64d53530063d64d53530063e64553530053f76553530063f76553530063d5498b530063d5458b530063d54987530063d54587530063d54983530063d54583530063e64552530063d64552530071f73552530071c73552530053d74d4e530071d54d4e53004be7498a53004bd7498a530063d5498a530063d5458a53004be7498653004bd74986530063d54986530063d54586530063d5498253004bf7458253004bc74582530063d54582530053d75951530063f64551530063c64551530055c73551530071f73551530071c73551530071d54d4d530063d54d8953004f671d8953004f571d89530063d54189530063d54d8553004ee72d8553004ed72d85530063d54185530063d54d8153004be7418153004bd74181530063d5418153004ee7218153004ed7218153004f67118153004f571181530063e75590530063e64d50530063d64d50530055d73d5053004bd76950530053d75950530063e6455053004bf76550530063e65550530053f76550530063f76550530063d5498c530053d74d4c530063d64d4c530071d5494c530047f7654c530063d6454c53004df7654c530071e5454c530063d5498853006ae6498853006ad64988530072d54988530066f5498853006ae54988530066d5498853006ad54988530062d54988530063d5458853006ae6458853006ad64588530072d54588530066f5458853006ae54588530066d5458853006ad54588530062d54588530063d5498453006b66498453006b56498453007355498453006e66298453006e56298453006775498453006b65498453006755498453006b554984530063554984530063d5458453006b66458453006b56458453007355458453006e66258453006e56258453006775458453006b65458453006755458453006b554584530063554584530063d5498053006ba6498053006b96498053007395498053006ea6298053006e96298053006f26198053006f161980530067b5498053006ba5498053006795498053006b954980530063954980530063d5458053006ba6458053006b96458053007395458053006ea6258053006e96258053006f26158053006f161580530067b5458053006ba5458053006795458053006b954580530063954580530067b5358053006da5358053006795358053006d953580530063e74997430063e74597430063e65953430063d65953430063f65553430063e65553430063d65553430063c65553430053f76553430063f76553430063d5498b430063d5458b430063d54987430063d54587430063d5498343
  | 19 => 0x8d540073a7018d540053a7018d540053d7018d54007397018d54005397018d540053e73d89540053d73d89540063e63d89540063c63d89540053e71d89540073671d89540053671d89540053d71d89540073571d89540053571d89540053e70d89540053d70d89540053e73989540071e73989540051e73989540053d73989540071d73989540051d73989540053e72989540063f62989540072f62989540053e71989540053d71989540053e70989540053d70989540053f73589540053c73589540063e63589540063c63589540072f62589540063e62589540053f71589540053c71589540053f70589540053c70589540053e76189540053e73189540053d73189540063f62189540072e62189540063d62189540072d62189540053e71189540053d71189540053e70189540053d70189540053e73d85540053d73d85540063e63d85540063c63d85540053e72d85540072e72d85540052e72d85540053d72d85540072d72d85540052d72d85540063f62d85540063d62d85540053e70d85540053d70d85540053e73985540071e73985540051e73985540053d73985540071d73985540051d73985540053e72985540053d72985540053e71985540063f61985540073761985540053e70985540053d70985540053f73585540053c73585540063e63585540063c63585540053f72585540053c72585540063f62585540063d62585540073761585540063e61585540053f70585540053c70585540053e76185540053e73185540053d73185540053e72185540053d72185540063f61185540073661185540063d61185540073561185540053e70185540053d70185540053e73d81540053d73d81540063f63d81540063d63d81540053e72d81540053d72d81540063f62d81540063d62d81540053e71d81540053d71d81540063f61d81540063d61d81540053e73981540053d73981540063e63981540063c63981540053e72981540053d72981540053e71981540053d71981540053e70981540063f60981540073b60981540053f73581540071f73581540051f73581540053c73581540071c73581540051c73581540063f63581540063d63581540053f72581540053c72581540063f62581540063d62581540053f71581540053c71581540063f61581540063d61581540073b60581540063e60581540053e76181540053e73181540071e73181540051e73181540053d73181540071d73181540051d73181540063e63181540063c63181540053e72181540072e72181540052e72181540053d72181540072d72181540052d72181540053e71181540073671181540053671181540053d71181540073571181540053571181540063f60181540073a60181540063d60181540073960181540053d75950540063e65950540047f76550540063
  | 20 => 0x38008002000000000000600800d80000020060018068000006003000000c00300100040060040000000000005000003802600600600100040000008000002013001000400000200000140000000008000002000004000c0060000065d6318f540056e7218f540056d7218f54005767118f54005757118f540057a7018f54005797018f540057671d8b540057571d8b540056e72d87540056d72d87540055e73183540055d73183540056e72183540056d72183540057671183540057571183540053d76d52540063d76d52540069d6318e54005ae7218e54005ad7218e54005b67118e54005b57118e54005ba7018e54005b97018e54005b671d8a54005b571d8a54005ae72d8654005ad72d86540059e73182540059d7318254005ae7218254005ad7218254005b67118254005b57118254004ee7218d54004ed7218d54004f67118d54004f57118d54004fa7018d54004f97018d54004f671d8954004f571d8954004ee72d8554004ed72d8554004de7318154004dd7318154004ee7218154004ed7218154004f67118154004f571181540053e73d91540053d73d91540053e72d91540053d72d91540053e71d91540053d71d91540053e70d91540053d70d91540065d6318d540056e7218d540056d7218d54005767118d54005757118d540057a7018d54005797018d540057671d89540057571d89540055e73989540055d73989540056e72d85540056d72d85540055e73985540055d73985540055f73581540055c73581540055e73181540055d73181540056e72181540056d72181540057671181540057571181540053e73d95540053d73d95540053e72d95540053d72d95540053e71d95540053d71d95540053e70d95540053d70d95540069d6318d54005ae7218d54005ad7218d54005b67118d54005b57118d54005ba7018d54005b97018d54005b671d8954005b571d89540059e73989540059d7398954005ae72d8554005ad72d85540059e73985540059d73985540059f73581540059c73581540059e73181540059d7318154005ae7218154005ad7218154005b67118154005b571181540053e72d8d540053d72d8d540053e71d8d540053d71d8d540053e70d8d540053d70d8d540053e7398d540063f6398d540071f6398d540053e7298d540053d7298d540053e7198d540053d7198d540053e7098d540053d7098d540071f6358d540063e6358d540053f7258d540053c7258d540053f7158d540053c7158d540053f7058d540053c7058d540053e7618d540063f6318d540071e6318d540063d6318d540071d6318d540061d6318d540053e7218d540072e7218d540052e7218d540053d7218d540072d7218d540052d7218d540053e7118d54007367118d54005367118d540053d7118d54007357118d54005357118d540053e701
  | 21 => 0x5000000000c000000801001e00001480040000050018044004004001000000800700000000140030018034000000000000000800b00000040000000010010000008000801001400c004000800000b001800400001d008005802200b001802c000001000004c014002002800000000000400380000000028000004004002806c0440010010000000007000000400e004000000001400d0058024002000001800c01000a0030000010004000000000200300380000020000020014000001000000400e002000000000e001000000000e01800000000000000000008002000002804404a000001008800200f007000001400000000000120300078000000000000000c01202d000001000e0010088024004000001000001a00000000000100000020030000001000800000c002004801c0100030000038000004001002800e000000000c00000100400540040000028010014000000001c000000000802c00000600000100100000108000000000001800c006000002000800200400080000000030000000010000001001400000100080080080050038004000000000000c0040000008018014000000801c01000200a000400800900380000000010020000006001003000000000d00080280080050028004000006000001800400000080100040000020004004001000002c01a001000000400000000480400000000058008000000009005000c0040028000000002000000c01200100480040000040000000000000002000400200200b801804000700180100000000008010000002000000000a001001000400c003000802401600b003000000000200500200120010000044002008000001c0020000048004000002002000001000c0018008008007001002c006002004800001400200080340000000030004006002007002400000c0000004004008000000c00200700080180000030018024002000001800c00200000080000120000008000006005001800000200200000180020050020000000000001000401c013002800001200000c000801000700a0008006000000000000000200c8008014007003800400000100180000040040030000000000002801c00400e0000008000004001800003400000100040040020000008000009002000c000006002801000200100180240000000010000000001000000800a00a000001800a003000000c004000001000400600000080040060020008018002005000000c000003007002401a000000000c01a0020000008006003002800800000a0010018018001000004801e0000038000008000000001000200000000100380020090004006005000800000000000c8000028004018000000a00e000800400200900a8034000011000000000000000100380020020010000000000000801800000400
  | 22 => 0xcf41d25885ce8204aba87599a000000000000055f000000166e000245a878000b1d18917c99c86b80001df8b2ed711c0b35426ebf568600014a823011b000088a0006e4138800033b16b800059c0000000000d92bab16a1da832c5c13179f181d24006d434bd41c9ce65d8fd87167f3000000000055b33d0ea59c22080bb0000000db54a1a6c800000039c84613ac07833b24255de33e55780000005434e5aff8000cf4636214d94220062c80011443a2000096000016838b253d50cc865089f392e600002e84100000000002ac8002003003001a000004000c00c008000004801600600000000020000000000006000000800c02c0020018000018006000000001c00000080380140020008000000001000800000e000000000c000001001000000a005006000000200300000000000100040008004000001000000000a0020018000002000000000c0000018000016004000001801800000400040080020010018004001000000000200000180340000030030010004003003000800000000200000000000010060006008002804c004018006800401c0000010010000002003000000000f000800000c004000001c01c000003009c01e001000801c0060070078000002003000000003a01e00b800000000000080000000020000000000000001003000800100100000000000000018002004005001000200c004800c00200100480000040040010000024003000000c000000000000000c0060000008000000001800c01200100800080000000000004002000000004401c0080070000008003000000400600400100380000070000008000001000802000400000000000020000000008020000005000400000500080080040040008000002000000000c00c00400180000000060030008008005000000800e003003000000000000000040040010088010018000004803c0020000008008000000003801c000005000801000201c0000058018007006800000400000080000040020000010022002000000c0000010000000004007000000c00c0070050008004000001002c008002003002800000700280440060030000004006006000003400800100280000000090048014002000000000c0120040008034000000006000800000b0008000000000000000000200000500200020060020004000001000000403800000100080000010030000002000005000c01800e001000000800d00000640060000060000008000000000402c0070000030002003004800001400b007800c002006002800c008000000000000a000002800c03a005002800400000100000040020020068000004000003000000201100200000700020010000004007006800c002003009805c00000100100080000000008050002002000001000400600c801000400100a80000
  | 23 => 0x1707fe0000000000bd80000000fccd2430c0fe800114c00054d0e19a2a2c500332640b06cd000000080c0f74619c300005cd055adc4000b060000001460000000000172cc3d6830000000b910ae8c7c0000c600025e16005e53288929020201220283159c7312d393e0a0aafa23c204cf0a2cf66f9909558cc01f69ff48b600000025d4bf02602320000a1843f0001fe0dd200023b8ba83b443412a333000011f0000000ce6a730000000000aee40c22c1614564000000000000019800000003af09280000001b66068b0c0000000001e383683c80000000aea45248c20580005680e7b0a4000b7f00000600000001820000996af614a09a04700000000f340000003cb000012a130574a4849003a400000000005b20e38000c60a396c10c2c6d073c68736dc98826a00029402660d71e28000250aff23e000000000008d0000000a36241000000000046f8000000920000254000092b000000109a26f395800000034332d14b8e7a8f90dc00014fa0002729281362585000321d0e8000000261d6eaaaa000372800077500000014ea000000377c0000001e50a59bccdb2000137c3d67a857b80010020006dd966cbacc0a657000165a11b2bca1fd0dc72c2ab193413498242300013148394de8a24aa26f4334945c4c400016c800000086200000000005cf230b4d411857e66500000008c907709d800079f47d8d848f2000399ad804cc00023500018960000000000000a494188000f4c00000000000000000bb96747f600022fb7758e01f266490481a2029000000107ec9300026509ec12a47b0884f647c458c256197eb435b1800188c7620b60f786b400063a254c00000000000000000000000000dbadc602f0000d6078a00b80000007f009080013ec00011707d8000000301806400074415e2c85b2a60239b85600ac46311227e4b94b9e00000009ba2914540a9502821b00000019060000fd0afd61600038ca4b40000970cb8d282a8c6934e800178c0006c6198045abdd5378001a58cee000199d1b243263c32d4b22a8210724d17328195e40888378b8e6bd0fc453e0003f8800000095a07dacd5538a9f00000004ce0002f1a284e8e1e500018fcca8c0c5ee1a1cde67860000000d2a57017327000006d402f8cc5710bd343400015620000000ec54d047b32c8b956a8000000085013024817e849859a1c02a6a5a8f8417211e302cdf2a9e26d0f110104f00a38c7885e18834bb184abab743e3815da5017337d800114000043a800017e0000002a4083a000000004400000000015b54680004ec800000017067391342c03e548f2cf4a1c792566b610000c8400003d09dadce00017a11c619469b1a3cd5a7ed28400013e000053886453720000001f70db8ce500000019364ab00000014be00016d80015cc08200015ec5683400000fa19fcd
  | 24 => 0xfd559ab6556c0002f504800000000b8800000060a44f2f7c000b5e000000076467441e80000001361ed8000690a76184043145c64b00028a408e86c0002935b688ea62f99792900000b09b784f263656931108de6ea12630084fa8f425eb155b5651310b0d48e5a1fb5428d606963d85720000a708c458112cce140000002e4800000000022140001e00001a6d156036372000191400050421393780000002f8c00060813734e0df869c06980019e05b83549ca571eb0464a8000c98af053da28c1d64a43ef06699409ae32000b01aa0000a3000042200014606d5bdc00006f800162e9f73d880010e41c54760000eac95643c1ac830a6612b70b599a00e000019bd72e0000209f1400057200007790361990000000bea75a00e11f5224d3239f346cbd23d76bb943d5ca6384a08bc867236332901dd4c8d83604906c000000000000108831b00012280007c34178001bb400057028bdaac0006de800000000000000000000c74331ee1b460000001c900004a26f52d598f24760000000a7c00016993aca96858000000000000053a2a3cb0e05b454b020000626044212c4bab7c4910a2db74d790be80002243d000035d84b22806a215a87040001a08000d30000000000155c000446ab4479c0002b3a768b320000000000dfe1526b093f19aed876b7942c71c761013075d69c2ae2221dd80000000002af037a9394ae2fe8000000000000000000000000000000000000000000000023055da7e0343dd2ed0648aa5000000130054c4a13791a568830001770eda9d20000f68792446038a911bb037d0002a90b10dbf12b2e150f65d95e735749c089c00008ed9f400000000f1430ab00001e6c0d6946000276c000645319a1280003b51818000aa06d13af30183e06bc5dba66cc3041a0c5913c000a460a7b290af8000225064919c954000000000014041b000102400030b80000006e6563000000018700000000cebec5a0800000038c25d97388d60002c100001b4c510e80c2814e0004e300011c05d800030040007df00000007400001e300014443cb5c0000140e00000000010a4000000103400000000001346be0006f49bc96460000000fa8b4a5480b700000702f60000cb496c7300000db048a0010001c0835e96c3239f981863a85ac09910ca9aa6402d7400046260d3779824ab938800000001b00002724000b0922880000003ac000123c7ba13140e310c84ed0518b8a68aae5f73369da005e0000cc2d1800075d00015140e629c68e8000274c8549900007b83990000000000d802b623cce0a3ba3d3b2c06aed4f4170c9cf981784a50bc561800000035a98ecc324cb96c000000000010d400000000009787c283000005945ea0000000001b8e000000179c000454000000000049a00021c40e00000001a2967600055d80000000000003
  | 25 => 0x8471168a6e183076c4928553bd9a955f84e106211c561eded1549fa000000000000017d08fc0000000000cb72d480004a02ab00022050ac8864cd3650e4458967b8001a44dc300017cd536000521304c000a37000032000097f0003274000c180f0ae0c0006db0001284e120000000000c9cdd340100e83aace069180006fcd850002d300000f600000017e000000028a000000000007fc25200000000000000004032c54ff661e3b38e217a446e00000000000001c800000009a122095d958e3f0616b1c4b986ed54b15a48d223100006804c2c584f400000001a50000000000ad55e3991947ac1936d1618e0e0002dd00004aa97700004f4000cad0d980000000000102b0442e90d000083cf323566a680007a40a243020140009fc1b6a08892e00000031780007eb3cbb54c0000005d31af800000000012d0b966562488a5430851410580012b242361c2b5885c8876b72fed0babb9000024069e5806f3aa440000000000000000525000367c0000000002fa96c200041900019de00010c8dac0000001c18a6c7f20513b7954c05a0796898000870b570002ca41b27a34ff8000000be03ba00000005c004e800158868947b8944d28b2c3dd8e24f7ed9b5d3b18d88e0cf66c1d386b6209300a238564de23be0f1d22e53d1c7a6a0b503b61848e4417472614f10a9b14059115985800020d0002ae12046235a980017643a100000000000000000000d4c50751c1e1c0008b700032044e63e96c88000f584730002b3c0000002d080006388bd5b925559bc97b0000000000d99284a2ed54c94d00007980000003361cd8d085596792e69bb64944199f542f899112fa7e81cc15538700012480960002960000be200018f541600063f8001a8a0004820b20caabcb579294d0fa5c32d9b428d7455a11f9b88000bd100285780000aa00032cc000bad25780000000420ec08f885ab4a46ba4b991c1501d307d02680004b20de52a27d6613aa059fa00019498c51fe00020a80008ba4ad2d61e101e2af85ac8001b420fe00013b8ffe7f9281a4c16200004712cf8d5c50060b00014ee3f22741a04b8461f0000000ca00004021a18a74aa006ea6cc56c98f63702254341ea00010140000000000000fb23600bf86ed0a2d6c000284881065d000054c90ed6927c80000007495dfaf505b8086290000000000000035a00002bd39a80013ba6c00000c880003a500014646ce0006afa18c122c303ec33713b804365c8001b8a00005da6b14360000002fdcb0600001590e80249f2119176c000a41316ae0826a000667b409656ca65e697bc4b45d50000ee4a461220002c140004e300000e4000000000000006acd330900000000003c10a600000000002f2800000000013600006a04e5049000030f61dad114c043b59882e0e829ab2528000000000363084c000
  | 26 => 0x314176a91c000d8e00002391bc00036800000007b7236aaa58a81cd18c2a841c400035511fd44aba44b89c70000ba0138a02c8ce00025725100ec0000000ce80001d900005917280002cf9024000ac51fd15818d40000000001a2e0004d780013a2aca00030980009b0627800083e00000000000009e000000008ae0002cd0001a3e000000043400035e0001fe80004a9000000106a000000090c0003e315380000005b9639b42d1fa0000588000d0ac103f3930193ed0014337355923010003540c3a74c2df096c000d040d89f34342418308800144284c00020e00003740000a402ce72e14723606dc00b1690000b5400000005b422c00000000015466900000ab000000000000007ccc1462e8d19622b6d31701b915c4ec07c0000e74000445b220c1c00003f222508600029a2c0ce365552950000000a881682c653b058457c80002d643d00023a09e894e00000000001142a200013988cc37c28b1b960000a0800000000000000000000006562da40009930000001a7a48c000000067074d617350877e3922f70fdccc4cba00000016e0b66000000000082b43e00000003d400033e00000004f6890964cb1a36629140000000800000000a63299ae1875c55c0003261788ce203e80016be00001e8a808a69951100000ffc000096a50000000000000000000005aab6417ca71457124580000005dc000000000043f25240000006a0000000000061c8c8c0008f567e2b5c000c45460a4a40002c61ac84780000000000001742354000000000000000000000000000000001726d4a53fa8e8dc07a259503a17a05e11160001a249e600020a589257762d1b4d97c000000081c0000000000001214757000000047a6056ac8001736535000162984600000015f4000000000000000025723a000000000000012dce246ca362830073c72103e27c400068842d0001a6800010c0d308844025cc2d8815e8a50001bf924a0006d11a9c00000048c80017c20244108de93fa117639000000006d000194cf920000182cbcc6ea02176000168e000675000030253b0290000000d780001c74000a1c00000003729f400000000000e33d28000ad632c000000119a53900004240002f90000000000bc2000289cd32c1100000000000002eea4cc000bbd3888f6400090f000000000000044502d400000000022100000000518000000bda6a4aba0f0654a54a8c80bbc45036224e934c2702392d6d0580000000000000da617f00003520000000001934d752cf338c77601b02a0001580b7d0001350bf8d9a68e000014a0003120001a4000000019f4000bd729e0eddae6a0d3b709fc0009d700034849d249d2690000000bee00000017809525868000000000000000000000027300000000002e490649380002e8800000000062d9bc169600002ab5b400000042f
  | 27 => 0xf85e8d8697a00000005420000002ddd8da6f5224041537600000000000000000002a740000000002594b1800008887a00000000000001738c8b3c7a4204a61d3000024cafe000403a944000ac816c277c178a3e17f80003120003fa17101b0d4638688780000720002a480007aa0422329bb83e40001aa00009d3000270400000014ea7946d4d5717d30845c6021097a24c3be000000005890c5f600000006ec0004141b2000070b2a0000000085e6be058cbf41d100000011280001e88564000a4b0001acc000350658a70d666de15c606b5b700d60000001ba40003b80001a10793303800000036f00d0a8921c79e0002f24000000663a9b56265a3040800000000000029880000000001cec000b2058a296565006528f213c00e77d1720c849a6d113dc926101c13b498b70866ad66501977db3a63b26b90a458ebed00013bc00000053800015860000000000d2c00060382c906e54e13c3358000c1b000072524600066313a8000a8b0000000574d8f00000001a404e01f800044ca195a6b0011b44d000009d000096e00028400001ca00013e86f680925fa30000009b0000a64b5c0002d1343463abbe24f107891a9c735da35430c7ae000000189843e047800113e00030012c05706ee6550000782355696b0cd8fc00027908e97124a65498678f127f764928186d262a1f622a9b663c3195062879eadb33f000135a00000000006e6a43127ae11806c9468b10cc00004b3160001baa4f12ce2a000000002dd80000768b23c8a99c00010f0000001b4800033d8001b720000002664b5a90065900019fe235101b0f829479d2e9800164a9e400000004a479c5d48c4000070f2261b6163c41360b80000000005840d995a8d580000000000a7a378b4c00000004b6a3e05084c95469c0c06400003000005a200046e0000000ca525c8e716d4b7a2821fbceb018e459890497c4c70501f6875415122f000000014b4c6800115a000000000000000000000000000004ada5a00009e9000295d0764b56189ab016c05c1cfb36848e6ce51d800000019b0000000b8e0000001fd40006142360001a0e00000010281e66660002afc00000000007040006c22cc078d89476521883e8bfa08b00000000000006c90000450cb84e79928cb864f314000001e00059c1d4405ca5210faab4000718502800000056f6020000000b3f511a39c00000000030f0cf000035b00000000000000d355b40000000000eaa85b000000000020600026e000000000036a40007e40000f5524e000573ad4509000000015e0000def0000000c3200050a1ed00006b14f7000000000000000000000004fa80014c2a5e45d2f045960003a436c019800061026248c06770002eccfd83c04dfafd898200354c30957e89e36072bc51849764859b958c841c0859c5cb1c2af6e8aa50ba
  | 28 => 0x547ee4fda7b00000005b233d83a87b0000000000000000013300000004dd13200005311a3a9711a488f000000028637c16f30d80000002dfa824066b3400000015eabaf181000000000058e1c000000001b20000000b36000355000000000000000000003d9877000000043b800075abbb3759bbc0004c54b0101cbe0c7a0001c209263370d12bac03cd4b42090dc3065010001aac50474f174a39005457313e000038cd5e30483504885b543983d4000b6e51e00001bc6cb5bc3104000000000000000000000028cc00000014ba124dee00056609ec0001bf00030a1ae48b96759871b62cfb40f83e4e969664768000a049061ca0000ce07806a618a4eb8deb3c5aa5cc860000001f28000b5000026194aa00032f9d98e545c56c689017fa67504c8d38c56b1262b346076085c6df1ce1996b680d319941de5b400018e4f1853057e94606e4000189a74000000032d9ad134ea4a6b204c9bb22f42af0810ee68031da01a468a27e1ae0130ef030768484094000000002b8c000de000000000001490d1800000056217c0000000ab55fc9a880000004d218189700000002b2da8604a00034940009286d6a374e2699c036261517800e38d34f94bad654c580000008b55838000fc00003a300000000000001fa800062019e08710ecd880000c54acc27263a800161cd633a13090e4000c000110d2dec37062b4e4b4052d000000064ad86415337431a0db5eb34e949c9f311c821573e01d2328af82b61f745890a02f240b2470b052fc9373d481a82d276b4860e100000005328fd573a43611b8f588568802c92b843007500e584b992229239a1088ec655438304f1ba8a6a28fa674700c1f56987a59883703940188a24bff62104fd89a7c00e1a16519095f662aa31a9c332351ab7819a7543f08000b5640e47d22600008fe2fcb70000000000000000004a741382500000006b02c6dbaec820000a4d5562b900030549aa00013618f00009153b4a0d0e46000554000195e0000001334a8400000016f00008913c68000878000000000000000060eb258c20beb0caa4689ee365000007c0000006bf80000000000000cb9758a265912d3c0000002ff800000000000014c80009ef03d8000c9000000000000000001b89c9cfca6e8617aad0b4839800035540006fa335905917e79447711d4000b6b0002d9d5069614e40000d1cb483ea1dc8e4ac7c00032a41581106a38000f0252f29230d512c4de5972d0151c000000000076616a0838021a34000654000000000057980000000000fc00000000006d78000000798000000000015c3e9b0e8000b52000000180a8d00341240fae41705a266103ad263410000cc6108313ab60b5e28100202f456600000004742020004db246db0217540d17b50e0683089a35042a4f313a8001880000151b4ed8c400049
  | 29 => 0x6100000004ac44ca03c39027a52dab749328cf00005140000cb0c99b9d602641011000000000062709b4a140002418000dbebfc0001f7435c00000000000005f10a4184c0000000001ff0000300408b7b13bcb8700012a1b3086f2c817ec0000276290fad664de300012545e60004c200000000003e080000005814ba00005b406655f22d80009a000024f842000068f16f4f783364c7146c00000059c9e8072e14c0000000ef40006880bdc0002b75bb0000f7cd9e000000000010a22b0d88014000000033800000047929f00000135b9b40c000c6000028800000003401dc400051a00018346ee0000001698000a6600000009a20000000b8400050d30a814181e0d00728d096d80004000e5400009e00034505f642519400017780534f3b2ac000000693939c00000063580000009b50001868fc694b03a02a4000000000000000000011180005de9eb0b102f8f6c00032b81200000001c98000a4e00069e2ec4000000397800000084246b293d8ca0001de1b580003a327209708b08c61873404e8093b5c584e0fa0d246d02100a4c3be6ad16c41ce70110294a11e2d7424f9ae4000cd22908f315144ca15ab6d90d2000369229d3020003f11afc8d060c2a79308f2a0006ce1c548b27f62a32fe18d07430f880001e4319126800185800000027103ce0001f39168598d896448000000b5c000154850ab6f3ad8cf400000000015840001e40002fc83500005ef112441842c576a82800051c4ae80000000000cf9eacbfcb7b00027152f20000818fe0ec000000024f515e000000000184447e6ae0001a549690ee80011ca913000053400019c154214000000000035ec00057a00017687565d20002695238cb66150228b90d8b1ef8000b2800000000000006e100014fc48c68d00004542560000000001a661ac4ea03b1148000000247c000000651258c10e9903322ee9b8200049c2ed87fa0000000000a3a00034d121000000040ab23400000000013700009fe01401100000006a900000008d35d28000d6e00004180000004213e90000000bcc060a3c18f600000037a107c94c40f0184000080449000176a7cf00aaf6043439b4809b3cef200021c800143e0402ca80003dadae1450c582de06344413f94f20ad31103f05766342f20000baec9c59e336c6661ec34586ac9fa6910000001760a5a00014400008e90df0a3c00027700000005be0006cb0001480b495e7800000000000022400000000000000a2a0004930c34000d6b00019c5a523531648094ac65112c7b3b57144ce4d4a8c89b24fb0e7356c7c40dc37193d52e48cb51880006560000002578000c1e62bab7cc1e2eb41280015fc0002830ac00003d33f932f0daa00062831214ac89740608cc00098c000323c0000371dc1e8400020263b80000003fc53f1d7ce3e8825ad0e689
  | 30 => 0x35437545c00018ce0000002b700000004979d4c0000002238ba0194bd50000000ba89be4cb02983fcdaa45f28a95d47e958b37943a42b11829eb40200a125e1af474e0754308000b6e0b90000630f5e60b31d05386880a81de82c1306be6027800122040300a15940002dd1148c6871a0b303f86c8f34ca34838d458384ba132a81027c35d1c500000000ae27f8000e7e2e00ba000141e6790000000b6c00048e800854c5eb00000000000005a125140009b400003c00008ac00035f8a520000d23364f9600031ab5f433a0000afaa88e3c8db105000034e1393a933c578a0643ed99b90a800000000000003341093588b2c127188b0d00009364fc048c0002690000001b2e000193000050e87937b33a03f28c70002af49acd2e2518001228000000016800000000017809b6af44cf314c00026b1c3b5052f8c975c0800154e000000000174447a000000099e0005360000d3cd0f17700011185365159b1c8ccb8d2ba30fd754b3a00014ad13658b11297887dc00031f2858e08ad00c836f00006210002b0999c17e0048001a9015631299f156e40f00000000000b701f00010d4000000000082279022e1ed4284a6b411b7302880002c98b1197ac6f39900000006ec21033442b434911a2f6cce4bc34052bed08ea4820a1ef421cc7d1ff24b03ea1662490b88e94000011a93031e22715201252fa5371e108a8a2c3856e828b5986b65000093920a6c1473327865eaec240b59c00061b4e6800000000059818c99cc9e2436a78436e0000001138000000000000118a0000000a218ccd705bf23459ea40435080005060000f983900f40000468f800007a43b626dc000817160000000064932c0cfc388b2750099a000028d0000464a820002a4a59c000b790001bf40009a31f7800072c992679930d426b1f00023ac0004892b88708bcc77f435800000000041e01bca8e0000000bc0124000018800144889d00007581480000002fbd46a6442c680003745c64068000000dac1ce8000be86af000112d1de00053903a800000000021917468263acb64d3100006640de1a6212c0001f4400000055d32317500456eb087538400d15512c8d4874550ba40c4c696b0c1000108a00044d000000068c00007b800087a00019a94f094735a9220000c2b24daeb926a17b06127a8f900006f8000090a5220000b297c8b4549524f01dacb40000bf0000dc40000000000bd93bbb3519f20002060000000be900033a400009c3b227550ce000083027c8e082d544b724000da70002fc533e7880002a1019267f21232408020ff34f92586fe55800035440000000000b090ae0005ca87f1a3200050a8fd19d842669b9810daeda5349a9a455a4304d1104000000029600005aaca744a800000000048880000009705c8092d98245536caa1d47ebe741223843984b16
  | 31 => 0x26307bd64800000000017e622f070aa640001e20000000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xcc9735c062440019c2e2b80c4880038955062945100061a3b2a8a8a2000e25541895144001c4aa831482880030d1d9545051000712aa0c4a0a20009358755231440018caea3146288003295d0628c51000712aa0c518a2000c34765513144001c4aa831262880030d9d9548851000712aa0c510a2000c34765512144001c4aa831242880038a550628811000571434431022000f21548862044001870ecaa24088003381d9214811000790aa2429022000e255418a104400107d0fb22a80800287a0f64550100050ec1ec8aa02000a2e82d91540400145b05b22a8080020fa1c64550100050f418c8aa02000a1d83191540400145d04322a8080028b60864550100051b408c8aa0200083e87d95540400143d07b2aa8080028760f655501000517416caaa02000a2d82d95540400107d0e32aa80800287a0c65550100050ec18caaa02000a2e82195540400145b0432aa8080028da0465550100041ec3cecaa02000a1e839d9540400143b073b2a8080028ba0a765501000516c14ecaa0200083e871d9540400143d063b2a8080028760c765501000517410ecaa02000a2d821d9540400146d023b2a8080020f61275d8c100041ec2ce9b18200083f87553630400107b0eaa6c6080030b55272d8c1000616aa2e5b182000a1d84996630400143b0b324c60800287e195498c100050ec32a93182000a1d84995630400143b0b322c60800287e195458c100050ec32a8b182000a1d85951630400107b093a8c6080020f6167418c100041fc3aa8318200083d87550630400183aa9398c6080030b5527218c1000616aa2e43182000c35549c4630400107b093aec4080020f61674d88100041fc3aa9b10200083d87553620400183aa939ec4080030755173d881000516c24cb3102000a2d85992620400145f0caa4c4080028b619549881000706aa4c73102000e0d5458e620400145b0932ac4080028b616645881000517c32a8b102000a2d865516204001c1aa931ac40800383551635881000516c2ca8b102000e25541c5620400107b093a8c4080020f61674188100041fc3aa8310200083d87550620400183aa9398c40800307551731881000616aa4e43102000c35549c46204001872a9380c4080028d61954c84100061abb2a99082000e155458f2104001c4aa8b1642080028d61954084100061abb2a81082000e155458c2104001c4aa8b1042080031c595700841000658b22e01082000d31545c021040019a2c6b8042080033858970084100051ac32a98802000e155458f1004001c4aa8b1620080030e5d9548401000714aa2c50802000a3586551100400186eecaa2200800385551634401000632b28e48802000ca5641c91004001a4aa839220080033158c72440100047243ac48802000e25545891004001876ecaa220080038a5516244010
  | 1 => 0xaa8b1cc2100028d61265584200051ac2cc8b084000a3786551610800146b0caa2c2100038555263584200070aaa2c6b084000a2d86552210800185aecaa4421000383551638842000712aa2c31084000a2d865502108001c1aa8b18421000389551610842000634b2ae01084000ca9645c02108001a52a8b8042100033258d700842000516c32a99004000e0d5458f2008001c4aa8b0e40100038c551618802000516c32a89004000c2f765512008001c1aa8b1a401000319594714802000652b20e29004000d25541c5200800198ac638a40100038955161480200061dbb2a89004000e3154585200800145d05322a9880028b60a645531000517414caaa62000a2d8299554c400145d05bb2a9880028b60b76553100050f41cecaa62000a1d839d954c400162b0738aa9880020f61275d8f100041ec2ce9b1e200083f8755363c400107b0eaa6c7880030b5527298f1000616aa2e531e200083d849d462c400107b0b3a0c5880020fe1d5418b100041ec3aa83162000c1d549cc62c400183aa8b98c5880024d61d548c71000712aa0c490e2000a1e83191548400143b06322a9080028ba08645521000516c10c8aa42000a1e83195548400143b0632aa9080028ba08655521000516c10caaa42000a1f835d9548400143906bb2a90800287a0c76552100050ec18ecaa42000a2e821d9548400145b043b2a9080020f6107558e100041ec28e8b1c200083e8755163840010790eaa2c7080020f6127518e100041ec2ce831c200083f87550638400107b0eaa0c7080030b5527218e1000616aa2e431c200083d849d4628400107b0b3a0c5080020fe1d5418a100041ec3aa83142000c1d549cc628400183aa8b98c50800389553620861000698aa2e010c2000ce3625c02184001e42a810c41080034c5507148210004f143e429042000f2154c85208400145d05322a8880028b60a645511000517c12c8aa22000a2c82591544400145d0532aa8880028b60a655511000517c12caaa22000a2c82595544400145d05bb2a8880028b60b76551100050fc1aecaa22000a1c835d9544400145f04bb2a8880028b20976551100058ac1ce2aa22000a34865c5544400185aa9394c6880030b5517298d100041ec20eab1a200083d851d1634400107d0eaa2c6880020f21d5458d1000616aa6e4b1a2000c2d541c9634400186aa9b8ac4880020f61275189100041ec2ce8312200083f87550624400107b0eaa0c4880030755273189100060eaa2e63122000c2e76550624400145b093a8c4880028b616741891000516c2ca83122000a2f87550624400145b0eaa0c48800389a05541891000712c0aa83122000e0d549cc624400189aeab98c488003235d1731891000706aa2e63122000e25545c462440018d2eab80c4880032a5d1701891000714aa2e03122000
  | 2 => 0x465552200050fc1aecaa44000a1c835d9548800143d063b2a9100028760c76552200051b408ecaa44000a35811d9548800107b083aac7100020f6147458e200041f43aa8b1c400083c87551638800107b093a8c7100020f6167418e200041fc3aa831c400083d87550638800186aa9388c7100030d5517118e2000694aa2e010c4000a3681991544800146b03322a8900028de0564551200051a40ac8aa24000a3681995544800146b0332aa8900028de0565551200051a40acaaa24000a3681dd9544800146b03bb2a89000287e0d76551200050e41aecaa24000a37815d9544800146902bb2a890002c360e725512000516432e4aa24000c35549c6634800186aa8b8cc6900020f6107558d200041ec28e8b1a400083e8755163480010790eaa2c6900030d5537158d200061aaa0e2b1a4000c2c765515248001858ecaa284900024b61d548c920006163b2a8992400083d849d4614800107b0b3a0c2900020fe1d54185200041ec3aa830a4000c1d549cc614800183aa8b98c2900028d61275185200051ac2ce830a4000a3787550614800146b0eaa0c29000389a09541852000712c12a830a4000e15549cc61480018aaeab98c290003255d173185200070aaa2e630a4000e25549486148001c4aa8a90c29000389552421852000712aa28430a4000a65858c8614800154b09190c29000389552321852000712aa26430a4000c71755c06148001962e8b80c2900038c551701852000668b9ae030a4000c2e765532148001c4aa830e429000389550614852000712aa0c3102400083e87d91540800143d07b22a8100028760f64550200051b40ec8aa04000a3581d91540800107d0e322a81000287a0c64550200050ec18c8aa04000a2e82191540800146d02322a8100028d60464550200041f43ecaaa04000a1e83d95540800143b07b2aa8100028da0765550200051ac0ecaaa0400083e87195540800143d0632aa8100028760c655502000517410caaa04000a3681195540800146b0232aa8100020f61e76550200050f41cecaa04000a1d839d9540800146d033b2a8100028d60676550200041f438ecaa04000a1e831d9540800143b063b2a8100028ba0876550200051b408ecaa04000a35811d9540800107b093aec6100020f61674d8c200041fc3aa9b18400083d87553630800186aa938ec6100030d55171d8c200050ec24cb3184000a1d85992630800143f0caa4c610002876195498c200050ec24cab184000a1d85991630800143f0caa2c610002876195458c200050ec2ca8b18400083d849d4630800107b0b3a0c6100020fe1d5418c200041ec3aa83184000c1d549cc630800185aa9390c6100030d5527118c200061aaa2e23184000a3584996610800146b0b324c2100028de1954984200051ac32a93084000e155498e6108001c2
  | 3 => 0xaaa2600083e869d9544c00143f06bb2a8980020fa18765513000517410ecaa26000a2d821d9544c00146d023b2a8980028d60476551300060ec18ecaa26000c2e821d9544c00185b043b2a8980030da0476551300061ac08ecaa26000c39801d9544c00143d0d39aa898003071da73551300050e432e6aa26000c1c765cd544c001870ed382a898003469ce70551300051c432e0aa26000d19735c1544c0014390caa4a698002872195454d300060e3b2a8a9a6000a1c86552434c0014390caa28698003071d95450d300050e432a99926000d15545c7324c0014390caa264980028721954cc53000686aa2e598a6000a1c86551314c0014710caa4a0980030e1d954541300051c432a92026000c3876551404c0014390caa460980020fa1f645503000517416c8aa06000a2d82d91540c00146d03b22a8180028d60764550300041f438c8aa06000a1e83191540c00145d04322a8180028b60864550300051b408c8aa06000a3581191540c00147500322a8180020fa1f655503000517416caaa06000a2d82d95540c00146d03b2aa8180028d60765550300041f438caaa06000a1e83195540c00145d0432aa8180028b60865550300051b408caaa06000a3581195540c0014750032aa8180020f61e765503000517414ecaa06000a2d829d9540c00146d033b2a8180028d60676550300060e41aecaa0600083e871d9540c00143d063b2a8180028ba08765503000516c10ecaa06000a36811d9540c00146b023b2a8180028ea0076550300050ec36e6aa06000c1d76dcd540c00143b0c39aa818003075d873550300058cc00e6aa06000a2d84996620c00145b0b324c4180028be19549883000516c32a93106000a2d84995620c00145b0b322c4180028be19545883000516c32a8b106000e0f83551620c001c1906aa2c4180028d61265984300051ac2cc93086000a3786552610c00146b0caa4c21800389552629843000712aa2c53086000a3584995610c00146b0b322c2180028de1954584300051ac32a8b086000e2554989610c001c4aa8b12c21800385e0d54584300070a41aa8b086000a1d86553300c001c1aa8b1660180038555161cc0300051cc32a9180600091c87551300c00143b0caa2601800307dd9544c03000706aa2c49806000e1554585300c0014730caa260180030edd9544c0300051b40cc8aa64000a358199154c800146d0332aa9900028d60665553200051b40eecaa64000a3581dd954c800143d073b2a9900028760e765532000586c1ce4aa6400083d849d763c800107b0b3a6c7900020fe1d54d8f200041ec3aa9b1e4000c35549c663c800186aa8b8cc7900024b61d548cb200050f418c8aa44000a1d83191548800146d02322a9100028d60464552200050f418caaa44000a1d83195548800146d0232aa9100028d60
  | 4 => 0x1400185ae8b16a0280030d5d161d40500070caa2c7280a000a1d839d165d000145b053a2cba00028d60674597400041f438caaa68000c35655c742d000185acab9683a000287a0c76552400050ec18ecaa48000a2e821d9549000145b043b2a9200028da0476552400051ac08ecaa48000b19831c1549000186aa9b8ac5200030d5507158a4000616aa6e4b0c8000c2d541c9619000163306382a8a00030b5527218d4000616aa2e431a8000c35549c4635000186aa8b88c6a000287a0f65550400050ec1ecaaa08000a2e82d95541000145b05b2aa8200028da0765550400051ac0ecaaa0800083e87195541000143d0632aa8200028760c655504000517410caaa08000a2d82195541000146d0232aa8200028d60465550400050fc32a8b188000c1d7558c4310001872cab80862000383552639884000706aa2c73108000a2f865516210001c1aa931ac42000383551635884000516c2886b108000aa98010d6210001c2aa931cc22000385551639844000712aa4c53088000e255458a611000146f0caa2c2200038555263584400070aaa2c6b088000e25549896110001c4aa8b12c2200028d614435844000558c0086b088000c1d7558f401000185aeab1680200030d5d561d00400070caa2c72008000a2e8219154cc00145b04322a9980028da0464553300051ac08c8aa66000a2e8219554cc00145b0432aa9980028da0465553300051ac08caaa66000a2e821d954cc00145b043b2a9980028da0476553300051ac08ecaa66000c1c765cd54cc00107b093acc5980020f6167498b300041fc3aa9316600083d8755262cc001a2aa8b8e65980020f61275987300041ec2ce930e600083f8755261cc00107b0eaa4c3980034355172cc73000517410c8aa46000a2d82191548c00146d02322a9180028d604645523000517410caaa46000a2d82195548c00146d0232aa9180028d604655523000517410ecaa46000a2d821d9548c00146d023b2a9180028d60476552300060f3b0e6aa46000b19801cd548c001a30e7382a918002c620d70552300068db9ae0aa46000c3554dc5628c00186aa838ac5180030b553725863000616aa0e4b0c6000c1d745cc654c00185ae9390ca980030b5d172195300061aba4e232a6000c35745c4654c0018cae4b88ca980030e5d170195300062cb9ae032a6000c69725c0654c0018e2e2b80ca98003075d5731913000616bace43226000c2d755c8644c00186aeb388c8980030d5d5711913000652b92e23226000c39755c0644c001932e6b80c8980032a5c9701913000658b8ae0322600083e87991544c0010790eb22a8980028ba08645513000516c10c8aa26000a3681191544c00146b02322a8980020fa1e65551300041e43acaaa26000a2e82195544c00145b0432aa8980028da0465551300051ac08c
  | 5 => 0x8028d619548c4210061abb2a91884200d25545ca310840146b0caa2621080385552634c42100722b2a649884200e85644c93108401e0aa899262108030bdd954484210061bbb2a89084200b2584995210840164b0b3224210802c9616544842100693ba2a89084200d25745512108401a4eeaaa24210803495d554484210069343aa89084200d2587551210840164f0caa24210802c9619544842100693bb2a89084200e277655121084012cb0bb9a421080269613734842100692aa6e69084200d25545cd2108401e0aa931a421080391595634842100742b22c69084200f055458d21084012cb0a382421080269610704842100692aa0e090842009c5831c121084014730932cc0108028e61664980210051dc32a93004200a39865526008401c32a931cc01080386551639802100790aa2433004200e255448560084015c10090ac0108028e61265580210051cc2cc8b004200a3b8655160084014730caa2c0108038655263580210070caa2c6b004200e62654856008401cc2ca90ac010803a8991215802100750b2242b004200f21544856008401d84c690ac010803b058d215802100715412a8b004200e29825516008401c6502aa2c0108038c605545802100714aa4a4b004200ae1819496008401c52a8a92c0108038a552425802100570c0c84b004200e295450960084014d30b192c010802aa612325802100714aa464b004200ae1818c96008401c52a8992c0108038c552515802100570c14a2b004200e31545456008401cc2a4a8ac0108038c552415802100570c1482b004200e31545056008401d4284a0ac0108029c616315802100558c2462b004200e31548c560084015c30518ac0108038c55131580210076099262b004200e2954c856008401c62a910ac0108038a551215802100718aa242b004200ae08748560084015c70a90ac010802b8615215802100571c2242b004200ae1844856008401cc6a890ac010803a8951215802100730aa242b004200ea1544856008401c42a890ac010802b8e0d215802100570c1a42b004200a1d839d564d400145b053aac9a80028d60675593500061ab22e3a96a000c2d645cb51d400163306382a9280030d5537158a500061aaa0e2b14a000c2d54dc9619400185aa8392c328002c660c705515000616aa4e431aa000c2d545c8635400186aa9388c6a80030d5517118d500050fc32a8b18a000c1d7458c5314001872c8b80a62800383552639885000706aa2c7310a000a2f865516214001c1aa931ac42800383551635885000516c20a6b10a000a698014d6214001c2aa931cc22800385551639845000712aa4c5308a000e255458a611400146f0caa2c2280038555263584500070aaa2c6b08a000e25549896114001c4aa8b12c2280028d610535845000538c00a6b08a000c1d7458f5
  | 6 => 0x61bbb2a89886200a1e839d954c840143b073b2a990802c560e71553210041ec24ebb1e420083d859d363c840107f0eaa6c7908020f61d54d8f210049ac3aa918e4200a1e839d9548840143b073b2a910802c360e72552210041ec24ebb1c420083d859d3638840107f0eaa6c7108020f61d54d8e2100496c3aa91944200a2d82991544840146b03322a8908028b60a65551210051ac0ccaaa24200a2d82dd9544840146b03bb2a89080287a0e76551210050ec1cecaa2420083d849d7634840107b0b3a6c6908020fe1d54d8d210041ec3aa9b1a4200c2d545ca634840186aa8b8cc6908020f61275181210041ec2ce8302420083f87550604840107b0eaa0c0908030755273181210060eaa2e63024200c2d749ca650840186ae938cca108030b5d672990210061abace3320420083e87d91540840143d07b22a8108028760f64550210051d406c8aa04200a3980d91540840107d0e322a81080287a0c64550210050ec18c8aa04200a3a80191540840147300322a8108020fa1f65550210050f41ecaaa04200a1d83d95540840147501b2aa8108028e60365550210041f438caaa04200a1e83195540840143b0632aa8108028ea0065550210051cc00caaa04200c2e82dd9540840186d03bb2a8108020f61e76550210050f41cecaa04200a1d839d95408401475013b2a8108028e60276550210041f438ecaa04200a1e831d9540840143b063b2a8108028ea0076550210051cc00ecaa04200a2d869c9540840161b07392a810802c9606725502100617bb2e4aa04200a35869c5540840162b0738aa810802c960a71550210061bbb2e2aa04200d25725c5540840107b093aec6108020f61674d8c210041fc3aa9b18420083d875536308401872a9386c6108030e55170d8c210050ec24cb3184200a1d85992630840143f0caa4c610802876195498c2100706aa4e53184200e15549c6630840143b0932ac610802876166458c210050fc32a8b184200a1d86551630840143b0b2a2c61080383a095458c2100706c12a8b184200e16815516308401c2b02aa2c6108020f6127518c210041ec2ce8318420083f87550630840107b0eaa0c610803075527318c210061caa4e03184200c39545c0630840185aecaa4a41080383551639482100692aa2e32904200a2f865515208401c1aa8b1aa4108030b5d9549082100706aa2c72104200d25545c6420840145f0caa2841080383551635082100496c3aa91904200a2d86552320840185aecaa4641080349551718c82100516c32a89904200e0d5498d320840186aecaa4a21080385551639442100692aa2e52884200a37865515108401c2aa8b1aa2108039158d52544210061abb2a92084200e155458e4108401a4aa8b9482108028de1954504210070aaa2c6a084200e8563509410840126b0eaa4621
  | 7 => 0x3d87552620c80183eecaa264190030bdd9544c83200616b22e429ea200c39645c053d440145b0829ac5a88029a6005358b5100593416e2aa4a200c2d549ca639440185aa8b94c7288034955272d465100593416e2aa2a200d25549cb515440183aa9398c0a880307551731815100616aa4e4302a200c2d545c8605440145d05b2aa9a08028b60b65553410041f438caaa68200a2e8219554d040145b0432aa9a08030b5957210f410061cb2ae021e8200a2d8510d62d04015530021ac5a0802c9a0b715524100616aa4e531c8200c2d545ca6390401a4aa939683208028ba0b765514100516c16ecaa28200b2682dc55450401a4aa939682a08030755273181410060eaa2e63028200c2d549c8605040185aa8b90c0a08020fa1c655504100517416c8aa66200a2d82d9154cc40145d04322a9988028b60864553310051d400c8aa66200a398019154cc40145d05b2aa9988028b60b655533100517410caaa66200a2d8219554cc4014750032aa9988028e600655533100517414ecaa66200a2d829d954cc40145d043b2a9988028b60876553310051d400ecaa66200a39801d954cc40183aec39aa998802c360873553310058cc00e6aa6620083d849d662cc40107b0b3a4c5988020fe1d5498b310041ec3aa93166200a2d849d662cc40145b0b3a4c5988028be1d5498b3100516c3aa93166200e0f8355162cc401c1906aa2c59880383552624cb3100616ba4e532c6200c2d745ca658c40186ae938ccb188030b5d6729923100616baae53246200c35759c6648c40145d05322a9188028b60a64552310041f438c8aa46200a2e82995548c40145b0532aa9188020fa1c655523100517416ecaa46200a2d82dd9548c40185d05bb2a9188030b60b76552310061b40eecaa46200c37765c5548c40146f0caa2a3188028de1954506310050fc32a998c6200d25549cb318c40145d05322a8988028b60a645513100517414caaa26200a2d82995544c40145d05bb2a8988028b60b76551310050f436e6aa26200c1d761cd544c40161b0439aa898802c5a0473551310058cc00e6aa26200b16839c5544c4014690cb8aa898803451cd71551310068aaa4e39926200c3476551514c401868ecaa282988034955272cc5310048fc3aa918a620083d849d4604c40107b0b3a0c0988020fe1d54181310041ec3aa83026200c2d549c8604c40185aa8b90c0988028ba08645503100516c10c8aa06200a3681191540c40147500322a8188028e600645503100517410caaa06200a2d82195540c40146d0232aa8188028ea0065550310051cc00caaa06200a1e839d9540c40145d043b2a8188028b60876550310051b408ecaa06200a3a801d9540c401473003b2a8188020f61275984310041ec2ce9308620083f87552610c40107b0eaa4c21880307dd9544c4310
  | 8 => 0xa930ac0218038c55161580430054cc1ca8b008600a3985d0d6010c01c32a921ac02180386d51435804300616b24e429ea400c35645c453d4801872c8b80a7a90028d610535875200538c00a6b0ea400b2681dc9549480186aa938cc7290030d5517198e5200692aa4e3a94a400b2681dc95454801a4aa938ea4a90030755273181520060eaa2e6302a400c35549c4605480186aa8b88c0a90028da0765553420051ac0ecaaa6840083e8719554d080146d0232aa9a10028d60465553420061ab2ae221e8400c39655c043d080146b0a21ac3a1002ac60043587420059340ee4aa48400c35549c6639080186aa8b8cc7210034955271d0a420051b40eecaa28400a3581dd9545080164d03b92a8a10034955271d09420060eaa4e63028400c1d545cc605080186aa9388c0a10030d55171181420041f438caaa08400a3681d9154cc80146b03b22a9990028da0464553320051ac08c8aa66400a3a8019154cc80147300322a9990028da0765553320051ac0ecaaa66400a368119554cc80146b0232aa9990028ea0065553320051cc00caaa66400a36819d954cc80146b033b2a9990028da0476553320051ac08ecaa66400a3a801d954cc801473003b2a999003075d873553320058ac08e6aa66400b19801cd54cc80107b093acc3990020f61674987320041fc3aa930e640083d8755261cc80146b093acc3990028d61674987320051bc3aa930e6400a358755261cc801c2f06aa2c3990038520d545873200616ba4e532c6400c35749c6658c80186ae8b8ccb190030b5d672992320061abace33246400c35755c6648c80146d03322a9190028d60664552320041f438c8aa46400a3681995548c80146b0332aa9190020fa1c65552320051b40eecaa46400a3581dd9548c80185d05bb2a9190030da0776552320061ac0eecaa46400c2f765c9548c80145f0caa2a5190028be195450a320050fc32a99946400d25549c7328c80146d03322a8990028d60664551320051b40ccaaa26400a3581995544c80146d03bb2a8990028d60776551320050f436e6aa26400c1d761cd544c80161d0439aa899002c560473551320058cc00e6aa26400b0e839c9544c8014590cb92a899003431cd7255132006163b2a8a926400c2c76551424c801a4aa938e649900247e1d548c9320041ec24ea302640083d859d0604c80107f0eaa0c0990020f61d54181320061aaa4e23026400c35545c4604c80145d04322a8190028da0464550320051ac08c8aa06400a3a80191540c80147300322a8190028ba0865550320051b408caaa06400a3581195540c8014750032aa8190028e60065550320050f41cecaa06400a2e821d9540c80146d023b2a8190028d60476550320051d400ecaa06400a39801d9540c80107b093acc4190020f61674988320041fc3aa931064008
  | 9 => 0x72d81540048ec1ce5b02a800a3581d8b605500123d0738ec0aa0024760e71d815400516c16c3b02a800a398018e605500126f02b94c0aa0024d205729815400497c12e3302a80092c825c6605500125d0439ac0aa0024b60873581540049b408e6b02a800935811cd6055001a1d0439ac0aa0034360873581540068b408e6b02a800d15811cd6055001a330039ac0aa0020fa1f63581540060e39ec6b02a800c1c7358d6055001838e7b12c0aa0028d60762581540060e39ac4b02a800c1c73d85605500145b05b0ac0aa003071cd61581540060e39cc0b02a80083d8798c605500183ae7318c0aa003075cc63181540051cc00c6302a800d0e739c86055001a1ae7390c0aa003439cd721815400686b9ae4302a800c2e635c86055001858c6b90c0aa003459ce71181540068ab9ce2302a800d26729c46055001a4ae5388c0aa003459cd71181540068ab9ae2302a800d26725c46055001a4ae4b88c0aa0030d98d71181540061a31ae2302a800c1d73d80605500185ae5b00c0aa0030d5c760181540068cb9cc0302a80083f87580605500143906b00c0aa003075cd601815400616b92c0302a800c357158060550012770eb00c0aa003465cd60181540041ec3ccb2a0a800a39809d564d4c016330039aa9298025660073551530058cc00e6aa2a600c35549c76254c0186aa8b8ec4a98030b55272d855300616aa2e5b0aa600c2d549c86054c0185aa8b90c0a98030d55271181530061aaa2e2302a600c1d645cf5414c0143b0d2a2a62980389552629845300712aa2c5308a600e25549896114c01c4aa8b12c2298038a552629805300714aa2c5300a600e31549866014c01c62a8b0cc0298028ee19545805300714aa4c4b00a600e29545896014c01c62a930ac0298038c55161580530052cc1ea8b00a600a3984d4d6014c01c32a929ac0298038695153580530051cc04e8b2e860083e8719554d0c0145d043b2a9218028b60876552430051b408ecaa48600a35811d95490c01475003b2a9218028e60076552430058cc00e6aa48600999801cd5450c0183aec39aa8a1802c660073551430061aaa4e3b128600c35545c76250c0185aa9396c2a18030b55172d854300616aa4e43028600c2d545c86050c0186aa9388c0a18030d55171181430060eb2ae72a08600a2e82d955410c0145b05b2aa8218028da0765550430051ac0ecaaa08600a3a80d955410c0147301b2aa8218020fa1c655504300517410caaa08600a2d821955410c0146d0232aa8218028d60465550430051d400caaa08600a39801955410c0143b0daa2862180389552629844300712aa2c53088600e25549896110c01c4aa8b12c2218038a552629804300714aa2c53008600e31549866010c01c62a8b0cc0218028ee19545804300714aa4c4b008600e29545896010c01c62
  | 10 => 0x300800200000c0b00601e03c060000100101080a0340040a0040000941a800000000000000720200880102a008038010000640380707e0880200501001c0580000609c0081202c0480000105802402804014000000010060040000004002c0300000200c050020060000882400e0300300200602c0f81801c00800082018000010000300240000400e0300e0020480000080003000c0580300607800000002090038040020000180400000006020000008048030000001200800600c0000900014806006034098078080360200300100e008018060120180f81605a0500501205002c0300000c00c080000020300180701e0740002500c0180084f07202c0280000000004802000000170030000040400a0040002b00700002002000000028018000062cb1ae031ea800c99635c063950018b2c6b80c6aa0032658d7018d540049b40ee4b1aa80093581dc9635500125d05b8ac6aa0024b60b7158d5400497410e0b1aa80092d821c1635500126d02382c6aa0024d6047058d540041fc3ac631aa80091f8758c635500143f0eb18c6aa00307e1d6318d540050fc12c631aa800a1f8158c635500143900b18c6aa0038358e7218d5400706b1ae431aa800e15639c46355001a4ce5388c6aa003495ca7118d540070ab1ae231aa800d26725c46355001a4ae4b88c6aa0038658e7018d5400695394e031aa800d29729c06355001a64e3380c6aa0034c5c67018d540060eb1ae031aa800e19635c06355001a54e4b80c6aa0034a5c97018d540069938ae031aa800d31715c06355001876c6b80c6aa0034698d7018d540061cb1ae031aa800d19635c06355001832c6b80c6aa003075cc63d89540051ac08c7b12a800a398018f625500123d0738ec4aa0024760e71d89540068b41ce3b12a800d15839c7625500186cc6b8ec4aa0030d18d71d89540049b40ce7312a800935819ce6255001a1d0539cc4aa00345a0673989540068ac0ce7312a800c1e73d8a625500164d03b14c4aa0028ba0863589540051ac08c6b12a800a398018d625500164d03b12c4aa00287a0e62589540048f418e0b12a80091d831c1625500126d02382c4aa0024d60470589540041fc3ac4312a80092f87588625500183ae631ec2aa0028b60863d85540051cc00c7b0aa80091e839cb615500123b07396c2aa00343a0e72d855400686c1ce5b0aa800c2e635cb6155001858c6b96c2aa0030b9c962d855400497414e730aa80092d829ce6155001a1d0539cc2aa0034360a73985540068b40ce730aa800c1e73d86615500164d05b0cc2aa0028b60863585540051b408c6b0aa800a398018d615500146d03b12c2aa002c9a0b61585540050f41cc2b0aa80091e831c1615500123b06382c2aa0024ba08705855400496c10e0b0aa80083f87584615500126f0eb08c2aa00247a0e
  | 11 => 0x2a09d67f425a5d42e09668704da81a2fca301e079a5e49dc00055888cb289a0000b561829940000003d84c0000980938a5263a0a0a5c0000009be0008c00000000000001e6618b3800029c76e44a24a000a4e0006764c880a49654a68230059e282af20c6b5c000a7c1905a49407fa0863d042e4f00781bc7cc25c93214600618e450a36360a2880e48036ca8ab1a9f693688ab3089c5b85509024fe172a7897e66c2722ce7be28472eaa46025da15463c74e97c85092293e9c47689982620005180000bc11c29000062a6cc8722782140002da8666ba9de86870a0c2244a1e494abc00071234238e0000000b002eaee2081443d60008e27e4596000008a985d839e48c47a67a6fe20e0000002be6ea4006466f491a37a5f8b547c00004cc3c6460b1e71c11e70e00047200085c7285fa0f44661cca244786c80485e284496c84c210ab69f21a018c6aa3a071e25235200e9ba206ae289809216817e2e68aa4860b68f04e414821c3a80001c423852a7f80000200ce0005de0122b40008089a4000000b0637e9e24d0804194b58b66322710482a6c51451c10e0845aa5f47ce55412e1d63dc9c0a327488a8ab8180930536b8659487a42c00003049213669ab90000b0a2582c046e6d60645e643820228aa148c43ee4229a8000b7400000008809673600056c0a4af854467e3781a604260e29816202cafe6ac690a3c37c83084a1b88ac5666a611054012204a4ea4e070821616443038a9ea76669c33e0dcb8887c3f27ba1e23109447a67460329601c28b629ea62af01605168402d26e241283831aa6414c798a0a01824e9d42a88529843763cc4ba50a1ec05a7162302683080000b83b212c704814aaa4287c26746ce0006042d80000340000101300a00402806006000068010000100400001a0002080208e0000481d004044020000020240282501800c020000000000400800800c0000101a0540680a080148008000000640680102200400032008000060060260000603b0000100006501e0240080000400c1b8010040000a800000000070020000000000b01600c0100201a0540080701e0040080c00c00c000040000000000500004000803000000020080020380b000004040008050000440601000a0000100c004060000000000240180101c0040000200a0080081300c04c0001202e000038110020c40000000201c01000012018048030000740f0100680100682301c01c000220220100000102000802801000010000000000000702202e014090090000cc018010140700380b0100081680d00202c01000002000070010060080600303201400016000004008060260000080a0020c002004014000030000221400881201400c010110420000180000002c0000102810c028110020000000b0000000881800400c0500100e01403016006
  | 12 => 0x5f024891408c22c0004160005ee87426a0004681de7f604c21a11a9e07d69502ea8fa83c4bc9a22ca0002662ec1b61e41ae5be63800043a000000254a26842000a1057c53a0000005c8000ab061e5b6a905ba654a486d41320005c6b2265e00074255a73e7c83183c8156b9666aabeae48809820ec84ea443b046c41e54682093a72a0fab2015a00023a27c27a2a421e0542d02d680000000031696a9aea824fcb606861da0000003baa3a4b4720a4c5249bc0e26fc6005740501848b28f81be3aa954620446072b4e72cac00da7645c22744ce00020097a6e02647725c425e98c28c0360e46b2634b101c842a14094251283409e8e8b50b8e9e41005d23aca860000000005d049a000acea087e20001763360d400081c7feb649b09cc3b619c7c405e38c0e800000047c06c64e7bcb72a762328842500c43fa1f463e41079c79e8f400000052c9b2000000000b0c4a076c49e2b21b43800f08bc3447225ae27eb16b4873a5f61b0972b7857aa889ec61067c57e2125566401886f6b086a44e84522866ec1968a4614b3e00004e3e09860a62465ce0007aaa2a4d6824968a5630400032a81000065800074c0005a6b042204e61980de3ec1c06844c43f04f28287069100269e8000470000a0c34609a9da70c0000c0aba6bc5dc87640c65c10405600002a4ac9e64a4a120002f80b26808dc88695a6786a2a4a88235a0aa1265e84086a080cb3c612578134b6ca9633c75a2e25ca3de3301181d41ee22e204862458000b4600008a85600056e30a00000000090e424ae6000000a5e000a1a0000004340002180000007a446a31e45e7561fe68a74a606000a5400000000085a3289700001700000ca1e85103921b23be5709d09240000008d26526d000000055c9d20000009fa00000044290a00000000085e000ae809c00059a4aa0007e623c326a021f03da000a505526b00002d48223e40008183948587a884883a000000b366c4000588000582b7c34c62632400007e568b8423eacc964226b127449b68c83c20000000000008ee2ac5985a25ec0cc0d03f40006b66fa00a5069341420005d694c41c1080006de0006ca00045aa2ca06000000a180002f2000b9293c0ba1780000004ae124afaa5800001409400000041400095e000000aec4069ac00000068e3a682a0007a095c854000af60000004983380000000008360109786483346da01e642aa2aa67acb320a80007d80000008d40000002c6a2200091208087e4be000a34ad2000b2c8d888800020c0660000006e626c1a899201c8d0522a402e800003c0001381ac30200000051e8ba30e92c14e0000000eea165e07780000d68ca2b66220007246ee3403988062224d85b000000097600000029412850088e76015e28e000826b1c00053c00000006a00058e5a005206ea707340002f031200
  | 13 => 0x6366082c82b800014a20a47e00049c8c20e6a7a54e3ea3503e6aae0000007b60007a2a5a44e00044800040a89e0aca1c23699e7840000000000ae0003b4794520b6e3bc1747764d46289520d2b2a58c3e2000a7e8e061a9287021308f66a8ade6d28a07923540000003fc3681a48c616a8a215213c796696b425484ca7da86a16c0f665a956ad418a8169580fc390a20b8a58a0b40006dc7b250c974714698ada584b2482c77e000b7e0000008928ec54c6600000820000009c2ae0a7200089a0007d007644064cb706e8b5e4ee6c01d27904fab7651a00000048a2a6a800c813e73c564af402435e8de29a16e43c17a3640002560008eaa6e6660002c458639a18604650e53432c83207035899a0000007820f21ce000aac52ea740001ea5ac6640440003567803b8040000b4000054276a9ee03a2de0e041a94e7884880004deb3a6ae00033200c904ac23d48129883a408e0000000000fe7589d886e31c5087007fc2e473856aa4698a224754a0e07c000a9cb4c40e3fe82e10a000374a9a1669fc12061c78c7507ae90c0007e815092e000668630650306000b6a0008e633a732a8c5c00000009c60002a219e4186f02cc2fe9aa3f60001c6432b7a060000576590a2e48e96e8947864a60009a62344d28bea008ce4740001d000009860a0008a600019a8aeb0eb344ec1dc1aa0000000000000005024e21ca846ac4b9c05c2aeb183d242043662c6947dc3623e89206169088786c253894a6f20026443967ee0f883e63275291e5cc9460000584b800053291c296a924c6000a0499c32e34815c00007a77cb02314a6ab980be000ac61f61122b0000a9430c2923ae00034a7de1ba7404262887eca3e0000008feb144640009960007caaca00010c3ca68c00053e8645806623a226e64a55e27659c9268da4566249ce090372b003ce2ee1fc6c65300a27f08e45f26700005b426098eafc3c447669e2aa03e77446236e3202fa80256078a17c1144547b877a860ab2730000b8c3842805fea4272678e62e4b643eaa822a6b835c0000000000740685ea81e3886881d8b4a7d412a4a875e49045ca845a8022656b9aa9e2f69f806289666e9b40001fa918444962b9439c2dc4dc9b875c6f824c8d69c8b26b9ead69f036a4a2adc000102a667621167ea240a3834e000b80004ac80002c2504526ab40000008cc4b26d8000028ad80005921580009486be572000aea000000b8222860c0006723f80008b401a8fc3704f6aa05bc0000382f49fe44c13a9006e4b5a6927d29060004840009ca7e07c6b44106000000a680d84b09f41f84040000006b438636671a2422ba0161921f2916402990034000b620007b07b48f2b685b20eaa8e92a4c2b2e4f486c000562b527f20001a22bc4f87180000007705fc3825288b8890ad0a608b00003c0000270000
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x14189058d7018d540070258e725c06355001c09635c97018d540070458e715c06355001c11635c57018d5400506261635c0635500141b9258d7018d5400506e45635c063550018197360063d89540050c640635c762550018197360063d85540050a640635cb615500190582604735815400642609801cd6055001911816007358154006051cd81d89605500180c7360b61581540050a640635c860550014319018d71181540060320d725806055001814835c56018154006065d9801cd54cc8016119020d5458732006065d9801cd544c801505911cd725513200542640735c9544c801819766007355331005826408355162cc40181976600735513100541648735c5544c401511901cd71551310068160981551630840160596551324c4210054164e875512108401125985537348421005816595458d210840112598550704842100641551831c12108401261952012158021004a8650804856008401a21542012158021004b064c8048560084016219499521580210058865664485600840162396551215802100588659544856008401e015498d21580210078055163485600840160993a0954580210058864682551600840161193a0554580210058864a815516008401a2182605545802100688551819496008401a215460642580210048a661548c96008401a2154606325802100688551829456008401a215460a41580210048c661548c56008401a215460a315802100780551324c560084012619521d2158021004a86508748560084012c19321d215802100688e11544856008401a2184551215802100688e15544856008401a2185551215802100688a61544856008401a219855121580210068821d54485600840126195e0d2158021004a8653834856008401a2154e0d21580210068855183485600840181a76600735523000446a63735c1548c0018258260476551300060660d801d9544c0018298260076551300060c605801d9544c00141a969ce705513000606219735c1544c0014149655171cc93000503259545cb314c0018197660073550300058264083551620c0016119020d54584300040725d86551300c00140c97551624c0300050525d54585300c00160593a0954185200050565d545cc61480012259855232185200050c65d545c06148001c11545cd70185200050a659545c02108001c095458d700842000509659541c52008001c055458c714802000708553625c021840019228755321482100058164e81550624400140d9755173189100050a65d545c06244001c09545cd701891000708551715c0624400142597550628c51000688a19548862044001c207655121481100050c659545c02104001c115458d700841000708551625c0210400142596550724401000701551631c91004001824875516244010
  | 1 => 0xd0801e820000000050a2c6001c000e02b67290e80048003000c41440580000d460b0986eaa7e7a0a5ae4b836620000d8960000000044001ac2005ca60000160000eaa89cf20c2c74286600aee64e00061038b4268cd2b2c0ece01242ac9200007c3af00000da000004dc18d6000000000064ba22523e00000000009abe86320846000024c834cc005ea40068eee24c6a783c4a6c948a0000000056002e9e008ece00ca2070a02a0088847600de00bc00540701050202040103000001040f0001000e0400000802000001020004030000030501010611010201004856478258c635500120d92e056318d54004836488058c6355001215912016318d540070158d725c46355
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x3209474810b014c000401a52000481344482c6b80c6aa002411a1241635c06355001204d1130b1ae031aa8009046849858d7018d5400482343c92c6b80c6aa002409a2e45635c06355001110d4aa840242b004200c80551932012158021005403474c2a890ac010802221a921d544856008401500d190eaa242b0042008886a554e0d2158021
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 65
  | 6 => 1592
  | 5 => 3569
  | 4 => 1488
  | 3 => 122
  | 2 => 12
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
  | 7 => packedAt gbK7 (1837+((h/21+packedAt gbK7 (1690+(h % 21)*7) 7) % 86)*8) 8
  | 6 => packedAt gbK6 (65264+((h/530+packedAt gbK6 (58904+(h % 530)*12) 12) % 2102)*12) 12
  | 5 => packedAt gbK5 (186769+((h/1189+packedAt gbK5 (171312+(h % 1189)*13) 13) % 5182)*13) 13
  | 4 => packedAt gbK4 (93248+((h/496+packedAt gbK4 (87792+(h % 496)*11) 11) % 1786)*12) 12
  | 3 => packedAt gbK3 (8860+((h/40+packedAt gbK3 (8540+(h % 40)*8) 8) % 177)*8) 8
  | 2 => packedAt gbK2 (992+((h/4+packedAt gbK2 (972+(h % 4)*5) 5) % 17)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xe060fff0c30e060fffc7ff80ff0700f00f3cf
  | 1 => 0xf007f0f0f03f007f0f0f8e3ff0f5a334334d33
  | 2 => 0x7ff00ffc0007ff00ff03fff09cc38c38e3c
  | 3 => 0xfff80000ffffff80000fffc0000e0fc0fc0fc0
  | 4 => 0xfffffffffff00000000ff000fff000
  | 5 => 0xffffffff0000000000000000000fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x2000110000020001100120800000001001045
  | 1 => 0x905290a2503905290a248492a0e4a314314512
  | 2 => 0xa52a04ae400a52a04921254e094c28c28a28
  | 3 => 0x2430000034924300000e498062200540540f80
  | 4 => 0x81018888cb2c9c7ccce00001844ff000abe000
  | 5 => 0xc9c7ccce0208101888800006088ffabe000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xffeaffeaffeaeae8ffeaffeaffeaeae8ffeaffeaffeaeae8ffeaffeaffeaeae8ffeaffeaffeaeae8ffeaffeaffeaeae8ffeaffeaffeaeae8ffeaffeaffeaeae8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_14200
namespace PEqualNP.Outside.L_meta_14200
open PEqualNP.Outside.L_meta_14200.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bgb_2_0 : Interval gbAtlas 2 0 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 12 := bgb_2_0
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
theorem bgb_3_96 : Interval gbAtlas 3 96 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 122 := (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 bgb_3_96))
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
theorem bgb_4_1472 : Interval gbAtlas 4 1472 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 1488 := (concat (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128))) (concat (concat bgb_4_160 (concat bgb_4_192 bgb_4_224)) (concat bgb_4_256 (concat bgb_4_288 bgb_4_320)))) (concat (concat (concat bgb_4_352 (concat bgb_4_384 bgb_4_416)) (concat bgb_4_448 (concat bgb_4_480 bgb_4_512))) (concat (concat bgb_4_544 (concat bgb_4_576 bgb_4_608)) (concat bgb_4_640 (concat bgb_4_672 bgb_4_704))))) (concat (concat (concat (concat bgb_4_736 (concat bgb_4_768 bgb_4_800)) (concat bgb_4_832 (concat bgb_4_864 bgb_4_896))) (concat (concat bgb_4_928 (concat bgb_4_960 bgb_4_992)) (concat bgb_4_1024 (concat bgb_4_1056 bgb_4_1088)))) (concat (concat (concat bgb_4_1120 (concat bgb_4_1152 bgb_4_1184)) (concat bgb_4_1216 (concat bgb_4_1248 bgb_4_1280))) (concat (concat bgb_4_1312 (concat bgb_4_1344 bgb_4_1376)) (concat bgb_4_1408 (concat bgb_4_1440 bgb_4_1472))))))
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
theorem bgb_5_3552 : Interval gbAtlas 5 3552 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3569 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)) (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 bgb_5_416)))) (concat (concat (concat bgb_5_448 (concat bgb_5_480 bgb_5_512)) (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640))) (concat (concat bgb_5_672 (concat bgb_5_704 bgb_5_736)) (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 bgb_5_864))))) (concat (concat (concat (concat bgb_5_896 (concat bgb_5_928 bgb_5_960)) (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)) (concat (concat bgb_5_1216 bgb_5_1248) (concat bgb_5_1280 bgb_5_1312)))) (concat (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536))) (concat (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632)) (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 bgb_5_1760)))))) (concat (concat (concat (concat (concat bgb_5_1792 (concat bgb_5_1824 bgb_5_1856)) (concat (concat bgb_5_1888 bgb_5_1920) (concat bgb_5_1952 bgb_5_1984))) (concat (concat bgb_5_2016 (concat bgb_5_2048 bgb_5_2080)) (concat (concat bgb_5_2112 bgb_5_2144) (concat bgb_5_2176 bgb_5_2208)))) (concat (concat (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304)) (concat (concat bgb_5_2336 bgb_5_2368) (concat bgb_5_2400 bgb_5_2432))) (concat (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528)) (concat (concat bgb_5_2560 bgb_5_2592) (concat bgb_5_2624 bgb_5_2656))))) (concat (concat (concat (concat bgb_5_2688 (concat bgb_5_2720 bgb_5_2752)) (concat (concat bgb_5_2784 bgb_5_2816) (concat bgb_5_2848 bgb_5_2880))) (concat (concat bgb_5_2912 (concat bgb_5_2944 bgb_5_2976)) (concat (concat bgb_5_3008 bgb_5_3040) (concat bgb_5_3072 bgb_5_3104)))) (concat (concat (concat bgb_5_3136 (concat bgb_5_3168 bgb_5_3200)) (concat (concat bgb_5_3232 bgb_5_3264) (concat bgb_5_3296 bgb_5_3328))) (concat (concat bgb_5_3360 (concat bgb_5_3392 bgb_5_3424)) (concat (concat bgb_5_3456 bgb_5_3488) (concat bgb_5_3520 bgb_5_3552)))))))
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
theorem bgb_6_1568 : Interval gbAtlas 6 1568 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1592 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768))))) (concat (concat (concat (concat bgb_6_800 (concat bgb_6_832 bgb_6_864)) (concat bgb_6_896 (concat bgb_6_928 bgb_6_960))) (concat (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)))) (concat (concat (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)) (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344))) (concat (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 65 := (concat bgb_7_0 (concat bgb_7_32 bgb_7_64))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 16, 24),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 4 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 4 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 4 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 6 zero,inputs.getD 2 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 7 zero,inputs.getD 1 zero,inputs.getD 3 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xffffffffffffffffffeaffeaffeaeae8ffeeffeeffeeeeeeffeaffeaffeaeae8ffffffffffffffffffeaffeaffeaeae8ffeeffeeffeeeeeeffeaffeaffeaeae8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 11 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) SB :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) SB :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
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
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,64,192)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,64,192)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_14200.Model.Repr at out
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

def mono : List Gate := [⟨.or,[5,6]⟩,⟨.and,[8,7]⟩,⟨.or,[2,3]⟩,⟨.or,[6,7]⟩,⟨.and,[10,11]⟩,⟨.or,[0,1]⟩,⟨.or,[5,7]⟩,⟨.and,[13,14]⟩,⟨.and,[0,4]⟩,⟨.or,[9,12]⟩,⟨.or,[17,15]⟩,⟨.or,[18,16]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,19⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_14200

open PEqualNP.Outside.L_meta_14200 in
theorem PEqualNP.Outside.L_meta_14200 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
