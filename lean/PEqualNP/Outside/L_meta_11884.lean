import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_11884.Model
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


end PEqualNP.Outside.L_meta_11884.Model

namespace PEqualNP.Outside.L_meta_11884
open PEqualNP.Outside.L_meta_11884.Model
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

end PEqualNP.Outside.L_meta_11884

namespace PEqualNP.Outside.L_meta_11884
open PEqualNP.Outside.L_meta_11884.Model
def s0K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (i*4) 4
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (5+((h/1+packedAt s0K3 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffdaf1333c71ce7c93
  | 3 => 0xffffffffffffffffffffffeffe3fff81fff0ff
  | 4 => 0x73ffc3cffe0f8f1c
  | 5 => 0x7cfffc0ffff00fe0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa51c664c1c636c91
  | 3 => 0x1020800080840026
  | 4 => 0xc44281524092518
  | 5 => 0x38802aa49204ac0
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 58 s0Pos s0Neg, 0xffffff00ff00cc00ffffff00ff00cc00ffffff00ff00cc00ffffff00ff00cc00ffffff00ff00cc00ffffff00ff00cc00ffffff00ff00cc00ffffff00ff00cc00, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_11884
namespace PEqualNP.Outside.L_meta_11884
open PEqualNP.Outside.L_meta_11884.Model
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
  | 0 => 0xc38f1e3fc78fffe31e3838e1f8e1fffe61327f
  | 2 => 0xfc0fe03ff80ff8fc1fc03f01ff01f87f863c73
  | 3 => 0xfffc3fff0ff1fe0003ffe3ffe3f8007cf9c
  | 4 => 0xfff00003ffff001fffffc0003fffc001f80fe0
  | 5 => 0xfffffffc0000001fffffffffc0000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x70118850541450030a0a902850284e28611225
  | 2 => 0x8b2254a8a32aa11c14452914a9149155862c52
  | 3 => 0x84404090102002420000a440a442104024498
  | 4 => 0x11004932120032494691800034990218a80b60
  | 5 => 0x22089000244cc492992634990000046155b000
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xffffffa0ffa0aaa0ffffffa0ffa0aaa0ffffffa0ffa0aaa0ffffffa0ffa0aaa0ffffffa0ffa0aaa0ffffffa0ffa0aaa0ffffffa0ffa0aaa0ffffffa0ffa0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_11884
namespace PEqualNP.Outside.L_meta_11884
open PEqualNP.Outside.L_meta_11884.Model
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
  | 0 => 0x78e3c71fc71fe3f31e3831c7c71f8ff3134cf
  | 1 => 0x7f03f81ff81ffc7c1fc03e07f81ff1fc238f3
  | 3 => 0xf8003ffe3ffe3ff8fe0003ff8ffe3fe003cf3c
  | 4 => 0xffffc0003fffc000fffffc000fffc000fc0fc0
  | 5 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x50e046228542944030a0a905141448ca311445
  | 1 => 0xa10c89450a252808c144522228889614c22892
  | 3 => 0x11000100000010200004801202000004128
  | 4 => 0x32240129a1200c92546918000e4d0246540ec0
  | 5 => 0xc44822400249b124a992639340000498abb000
  | _ => 0
def s2Atlas : Atlas := ⟨3,rawDecor 59 s2Pos s2Neg, 0xffffff88ff88ee88ffffff88ff88ee88ffffff88ff88ee88ffffff88ff88ee88ffffff88ff88ee88ffffff88ff88ee88ffffff88ff88ee88ffffff88ff88ee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_11884
namespace PEqualNP.Outside.L_meta_11884
open PEqualNP.Outside.L_meta_11884.Model
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
  | 0 => 0xffffffffffff83c1e0e03fffffffffe067fff
  | 1 => 0xf83ff07ff83ffc01ff003c3fc3fe07f984e73
  | 2 => 0xffc1ff83ffc1fffe00003fc3fc3ff81e0739c
  | 4 => 0xf0001fffc0001ffffffffc003ffc0001ff83e0
  | 5 => 0xffffe00000001fffffffffffc0000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x10908142090000140a02488448442a280614a5
  | 1 => 0xa549523492569ac295509162962b4155984a52
  | 2 => 0xc62a5491a452bd6aa141226a26a39505e06318
  | 4 => 0x843188210718c98cc66438003b310618aa83e0
  | 5 => 0x84210c6386316331989c3b300021861557c00
  | _ => 0
def s3Atlas : Atlas := ⟨3,rawDecor 55 s3Pos s3Neg, 0xffffa8a8a8a8a8a8ffffa8a8a8a8a8a8ffffa8a8a8a8a8a8ffffa8a8a8a8a8a8ffffa8a8a8a8a8a8ffffa8a8a8a8a8a8ffffa8a8a8a8a8a8ffffa8a8a8a8a8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_11884
namespace PEqualNP.Outside.L_meta_11884
open PEqualNP.Outside.L_meta_11884.Model
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
end PEqualNP.Outside.L_meta_11884
namespace PEqualNP.Outside.L_meta_11884
open PEqualNP.Outside.L_meta_11884.Model
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
  | 0 => 0x3c3fffc7fc3fffe1c30e0fffc3f0ffff09f27f
  | 1 => 0xc03c3ff87fc7c3fe03f00f0ffc7f1e0f913d93
  | 2 => 0x3fc7ff8007fc3ffc000ff0ff801ff0e1ce1c
  | 3 => 0xffc007fffff8003ffffff000ffffe000fe0fe0
  | 4 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x440042204100008102421100908284085025
  | 1 => 0x928a94914a0a262a2290858a642a142a912492
  | 2 => 0xab11b5251a94a277648129a8e9065962e18e18
  | 3 => 0x8010200100088844824200092444040220b40
  | 4 => 0x3222243663273339b3c9cecc2008918cddf000
  | _ => 0
def s5Atlas : Atlas := ⟨3,rawDecor 31 s5Pos s5Neg, 0xffa8eea8ffa8eea8ffa8eea8ffa8eea8ffa8eea8ffa8eea8ffa8eea8ffa8eea8ffa8eea8ffa8eea8ffa8eea8ffa8eea8ffa8eea8ffa8eea8ffa8eea8ffa8eea8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_11884
namespace PEqualNP.Outside.L_meta_11884
open PEqualNP.Outside.L_meta_11884.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x482600000042108000825e6400000000000e74403a3000004a000000000000002e007a00007600000000066e58004c0000020000000078005668366000001200000000000000341e5018000000000000000066000022006c207e002a2816005c3200000000000000004e460c0000000a00000000002c0000000000000000080000005a3c3e2400141c543804000000004400000000007c00526a000000000000001a62707200040002000801000000000200020002000002010300007fd5001fe54007f55001fc54007fd4c01fe53007f54c01fc53007fd0c01fe43007f50c01fc43007fd4801fe52007f54801fc52007fd0801fe42007f50801fc42007fcc801fe32007b8c801fd32007b4c801fc32007fd4401fe51007f54401fc51007fd0401fe41007f50401fc41007fcc401fe31007f4c401fc31007fc8401ef21007f88401fd21007b48401fc21007fd4001fe50007f54001fc50007fd0001fe40007f50001fc40007fcc001fe30007f4c001fc30007fc8001fe20007b88001fd20007f08001ec20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x284000fb99420006dcca10003ed6508001b6b284001fb1942000fdec810003ee6408001d73204000fb590200075ac810007ec6408001f7aa04000fb95020007daa810003ec5408003f7b184000bbd8c20007dcc610003ce6308001f6b184000bb58c200079ac610002cd6308003f63184000fbd4c20007dca610003ed5308001f62984000fbd0c20007dc8610003ed4308001f62184001fbd8420007dcc210003e66108001f6b084000bb58420007cac210002e56108003f63084000fbd4420007dca210003ed5108001f62884000fbd0420007dc8210003ed4108001f62084000fbcc420007dc6210003ed3108001f61884001fb98020005dcc010003ea6008001f7a804001fb94020007daa010007ec5008001f7a004001fb90020007da8010007ec4008001f79804001fb8c020007da6010007ec30080017fb2e2000bf99710005facb88002fc65c40017fb262000bf99310005fac988002fc64c40017fb1e2000bf98f10005fac788002fc63c40017fb162000bf98b10007dcc588002ee62c40017eb162000fb58b10005dac588002fc62c4001f71962000fb4cb10007ec6388003f531c4001f790e2000fd88710007da4388003f521c4001f290e2000fb88310007d84188002ff65840017f32c2000bf59610005f8cb08002ff64840017f3242000bf59210005f8c908002ff63840017f31c2000bf58e10005f8c708002ff6284003f7b142000bbd8a10005fcc508002fd62840017e3142001fb18a10005d8c508003ee3284001f69942000bf58610007eca308003f55184001fb20c2000fd50610007ee6308003f43184001f790c2000fb48610005fcc108003fa3084001fc9842001fb8821000fd84108003f71084001fd8842000bfd9510005fcca88002fd65440017e32a2000bfd9110005fcc888002fd64440017e3222000bfd8d10005fcc688002fd63440017e31a2000bfd8910007dec488002ef62440017f3122000bf58910005f8c488003ec6244001763122000fb8c910007da6488003f63144001fa98a2000fbc8510007ec4288003ed2144001fa90a2000f948510007f46088003f93044001f71022000fb08110007f62088003f610440017fb282000bf99410006fcca080027e65040017eb282000df59410004faca08002fc65040017fb202000bf990100077cc808002be64040017eb202000ef590100057ac808002fc64040017fb182000bf98c10007bcc608002de63040017eb182000f758c10005bac608002fc63040017fb102000bf98810007dcc408002ee62040017eb102000fb58810005dac408002fc6204001f71902000fb4c810005fcc208003f65104001faa882000fd90410007ea8208003f73104001fa1882000fbc8410007da4208002fe6004003f71002001fb08010007ee2008003fa1004001fa8802000fe44010
  | 1 => 0x3f9404c001fd9826000f78c130005feca18002fe650c001bf32860009f99430005faca180037d650c0013eb286000bf19430005fec818002fe640c001df3206000af99030005fac818003bd640c0015eb206000bf19030005fcc618002fe620c001f73106000bb98830005fac418003ed620c00176b106000fb8c830007da6418002fe610c001fb3086000bd98430005fac218003f5610c0017ab086000fbc8430007da4218002fe600c001ef9806000fe8c030007ba6018003f9300c0017fb2e4000bf99720005facb90002fc65c80017fb264000bf99320005fac990002fc64c80017fb1e4000bf98f20005fac790002fc63c8001f71964000fb4cb20005fcc390002fd61c8001f790e4000fb48720005fecb10002fe65880017eb2c4000bf19620005fec910002fe64880017eb244000bf19220005fec710002fe63880017eb1c4000bf18e20005fac510003ef5288001f72944000fb54a20007d8a510003ef4288001f72144000fb50a20007d88510003ef3288001f71944000fb4ca20007d86510002fe61880017eb0c4000fbc8620007dc4310003ed2188001f610c4000bf98220007de4110003fb2088003f7b2c4000fb99620007dacb10007ec6588003f7b244000fb99220007dac910007ec6488001f7aa44000fb95220007daa910003ec5488003f7b1c4000bbd8e20007dcc710003ed638800176b1c4001fb18e20007dea710003ee5388001f6a9c4000fb14e20007de8710003ee4388001f6a1c4000fb10e2000fdec310003ee6188001f6b0c4000bb5862000fd8c310003ef5188001f728c4000fb54620007d8a310003ef4188001f720c4000fb50620007d88310003ef3188001f718c4000fb4c620007d86310002ee6088001f7a844001fb94220007daa110007ec5088001f7a044001fb90220007da8110007ec4088001f79844001fb8c220007da6110007ec30880017fb2a4000bf99520005faca90002fc65480017fb224000bf99120005fac890002fc64480017fb1a4000bf98d20005fac690002fc6348001f71924000fb4c920005fec290002fc6148001f790a4000fb48520007f64090003ee20480017fb284000bf99420006fcca100027e65080017eb284000df59420004faca10002fc65080017fb204000bf990200077cc810002be64080017eb204000ef590200057ac810002fc64080017fb184000bf98c20007bcc610002de63080017eb184000f758c20005bac610002fc63080017f3104000fbd4820007dca410003ed5208001f62904000fbd0820007dc8410003ed4208001f62104000fbcc820007dc6410003ed3208001f61904000bf98420007ecc210002f661080017eb084000fd58420005eac210003ef2108001f71084000fb48420007d84210002fe6008001f79004000fe88020007da4010003f92008003f7b
  | 2 => 0x50005dec4a8002fc6254001f6312a000bb18950006fea4a80037d5254001f7192a000fb4c950005fec2a8002fc6154001bfa8aa000df54550007de42a8003ed2154001fda82a000df94150005fcca28002fe64140017eb20a000bf98c50005fac628002fe62140017eb10a000fb8c850007da6428002fe61140017eb08a000fbc8450007da4228002fe6014001bfa80a000fe94050006faa028003f950140017fb2e8000bf99740005facba0002fc65d0001dfaa68000ef15340005fcc7a0002fd63d0001dfa1e8000ef50f40005fcc5a0003ee62d0001773168000bf58b40007dac5a0002ed62d0001dfa168000ef50b40007dc65a0003ed32d00017f30e8000fd98740005ecc3a0002fd61d0001fab0e8000bd587400077e83a0003bd41d0001f790e8000fb48740005fecb20002fe6590001bf32c80009f99640005facb200037d65900013eb2c8000bf19640005fac920002fe63900017eb1c8000bf98a40005fac520003ee3290001f69948000bf98640005fac320003ef2190001f690c8000bf98240007f4a120003f95090001dfa048000fed0240005fecaa0002fe65500017eb2a8000bf195400077ea8a0003bc54500017fb1a8000bf18d400077e86a0003bd43500017fb128000fbd8940005dec4a0002fc6250001f63128000bb189400077e84a0003bd4250001f71928000fb4c940005fec2a0002fc6150001dfa0a8000ef50540007de42a0003ed2150001fd2828000fe54140007f680a0003be40500017fb288000bf99440005faca20002fc65100017f3208000bf98c40005fac620002fe62100017eb108000fb8c840007da6420002fe61100017eb088000fbc8440007da4220002fe6010001dfa008000fe900400077a8020003f940100017fb2e6000bf99730005facb98002fc65cc0017fb266000bf99330005fac998002fc64cc0017f3166000fb98b30005dcc598002fd62cc001f6b166000bb58b30007be6598003ee32cc001ee9966000fb4cb300079a6598002fe61cc0017eb0e6000f7cc730007ba6398003ef21cc001f690e6000bfd9630005fccb18002fd658c0017e32c6000bfd9230005fcc918002fd648c0017e3246000bf58e3000fdec518002fe628c0017eb146001fb18a30007dc6518003ed328c0017f30c6000bf58630007de4318003ed218c0017f3046000fe94230007f2a118003fa408c001fca046000f7cc230007f66118002ff654c0017f32a6000bf59530005f8ca98002ff644c0017f3226000bf59130005f8c898002ff624c001f7b126000bbd8930005f8c498003ec624c001763126000f7cc930007dc6498003dd324c001f69926000f34c930005fec298003f7614c0017bb0a6000bf18530007e8c298002f4614c001ef98a6000f74c530007de4298003ed214c001fd2826000fe54130007f4809800
  | 3 => 0x731e4200fb58f21005dac790803ec63c8401f7a9e4200fb94f21007daa790803ec53c8401f7a1e4200fb90f21007da8790803ec43c8401f7a8e4200fb94721007daa390803ec51c8401f7a0e4200fb90721007da8390803ec41c8401f798e4200fb8c721007da6390803ec31c8401f7b064200fb98321005dcc190803ed60c8401f63064200bfd9621005fccb10802fd65884017e32c4200bfd9221005fcc910802fd64884017e3244200bfd8e21005fcc710802fd63884017e31c4200bf58a21005dac510803ee3288401f69944200bf98621007eca310803f55188401fb20c4200fd50621007ee6310803f43188401f790c4200fdc8621005fcc110802fd60884017fb2a4200bf99521005faca90802fc65484017fb224200bf99121005fac890802fc64484017fb1a4200bf98d21005fac690802fc6348401f7a924200fb94921007daa490803ec5248401f7a124200fb90921007da8490803ec4248401f79924200fb8c921007da6490803ec3248401fb28a4200fd54521007ec8290803f54148401fb98a4200fd0c521007ee4290803ee21484017fb024200bf18121007deca90803ee6548401f6b2a4200fb19521007dec890803ee6448401f6b224200fb19121007dea890803ee5448401f6aa24200fb15121007dec690802ef6348401f731a4200fb58d21005dac690803ec6348401f7a9a4200fb94d21007daa690803ec5348401f7a1a4200fb90d21007da8690803ec4348401f7b0a4200f9d8521007dea290803ee5148401f328a4200fb54521007caa290803ec5148401f7a0a4200fb90521007cc8290803ed4148401f2a0a4200fb10521007de6290803e73148401f718a4200fb4c521007d86290803e43148401f7b024200fb98121007dac090803ec6048401763024200bfd9421005fcca10802fd65084017e3284200bfd9021005fcc810802fd64084017e3204200bfd8c21005fcc610802fd63084017e3184200bf98821005dcc410803ee3208401f69904200bf98421007de4210803f62108401f69084200fd48421005fcc010802fd60084017f326a000bf59350006fca9a80037c54d40017f31ea000bf58f50006fea7a80037d53d40017f316a000fb98b50005dcc5a8002fd62d4001f6b16a000bb58b50006fea5a80037d52d4001f7196a000fb4cb50005fcc3a8003f661d40017b30ea000bf58750007eac3a8002f561d4001bfa8ea000df54750007de43a8003ed21d40017eb2ca000bf992500077cc928002be64940017eb24a000ef592500057ac928002fe63940017eb1ca000bf98a50005fac528003ee3294001f6994a000bf98650005fac328003ef2194001f690ca000bf98250006fea128003fb50940017fb22a000bf19150006fca8a80037c54540017fb1aa000bf18d50006fea6a80037d53540017fb12a000fbd89
  | 4 => 0x803bc54d04017f31e8200bf58f410077e87a0803bd43d04017f3168200bf58b41007dc65a0803ed32d04017f3068200bf58341005fecb20802fe6590401bf32c82009f99641005facb208037d65904013eb2c8200bf19641005fac920802fe63904017eb1c8200bf98a41007dcc520802ee62904017eb148200fb58a41005dac520803ee3290401f69948200bf98641007eca320803f55190401dfa0c8200fdd0641005fcc120802fd60904017fb2a8200bf99541005facaa0802fc6550401dfaa28200ef15141005fec6a0802fc6350401dfa1a8200ef50d41005fec4a0802fc6250401f71928200fb4c941007eca2a0803f55150401fba0a8200ef90541005fec0a0802fc60504017fb288200bf99441005faca20802fc65104017f3208200bf98c41005fac620802fe6210401f73108200bb98841005fac420803ed621040176b108200fb8c841007da6420802fe6110401dfa088200fd904410077a8220803f541104017f3008200bf58041005fecb98802fe65cc4017eb2e6200bf19731005fec998802fe64cc4017eb266200bf19331005fcc598803ee62cc401773166200bf58b31007dac598802ed62cc401f71966200fb4cb31005fcc198802fd60cc4017fb2c6200bf99631005facb18802fc658c4017fb246200bf99231005fac918802fc648c4017eb1c6200bf98a31007dcc518802ee628c4017eb146200fb58a31005dac518803ee328c401f69946200bf98631007eca318803f5518c401fb20c6200fd50631007be6318803f7318c4017f3046200bf58231005feca98802fe654c4017eb2a6200bf19531005fec898802fe644c4017eb226200bf19131005fec498803ee624c401f6b126200bf18931007dc6498803ed324c401fb28a6200fd54531007ec8298803f5414c401fb98a6200f78c531005fec098802fc604c4017fb286200bf99431006fcca188027e650c4017eb286200df59431004faca18802fc650c4017fb206200bf990310077cc818802be640c4017eb206200ef590310057ac818802fc640c4017f3186200bf98831007dcc418802ee620c4017eb106200fb58831005dac418803ee320c401f69906200bf98431007be6218803f6310c401ee9886200fd4c431005fcc018803fa600c4017d3006200bf58031007f2c018802f9600c4017fb2e4200bf99721005facb90802fc65c84017fb264200bf99321005fac990802fc64c84017fb1e4200bf98f21005fac790802fc63c8401f7a964200fb94b21007daa590803ec52c8401f7a164200fb90b21007da8590803ec42c8401f79964200fb8cb21007da6590803ec32c84017f3064200bf58321007decb90803ee65c8401f6b2e4200fb19721007dec990803ee64c8401f6b264200fb19321007dea990803ee54c8401f6aa64200fb15321007dec790802ef63c8401f
  | 5 => 0x9732005f8cb99002ff64cc8017f3266400bf59332005f8c999002fe61cc8017eb0e6400bf98332005fac199002ff658c8017f32c6400bf59632005f8cb19002ff648c8017f3246400bf59232005f8c919002fd638c8017f3146400fbd4a32007dca519003ed528c801f62946400fbd0a32007dc8519003ed428c801f62146400f7cca32007de6519002fe618c801fb30c6400bd98632005fac319003f5618c8017ab0c6400bf98232005fac119003ef658c801f732c6400fb59632007d8cb19003ef648c801f73246400fb59232007d8c919003ef548c801f72a46400fb55232007d8a919002ed638c801f7a9c6400fb94e32007daa719003ec538c801f7a1c6400fb90e32007da8719003ec438c801f7b0c6400fb98632007ccc319003ed618c80176b0c6400f958632005cac319003ec618c801f7b046400fb98232005dcc119003ed608c801f63046400bfd9532005fcca99002fd654c8017e32a6400bfd9132005fcc899002fd644c8017e3226400fbd4932007dca499003ed524c801f62926400fbd0932007dc8499003ed424c801f62126400fbcc932007bc6499002ff614c8017e30a6400bfd8132005f8c099003ef654c801f732a6400fb59532007d8ca99003ef644c801f73226400fb59132007d8c899003ef544c801f72a26400fb55132007d8a899003ef634c801e7b1a6400fbd4d32007dca699003ed534c801f629a6400fbd0d32007dc8699003ed434c801f621a6400fbd8532005dec299003ee614c801f6b0a6400fb18532007dec099003ee604c801f6b026400fb18132005d8c099002ff650c8017f3286400bf59432005f8ca19002ff640c8017f3206400bf59032005f8c819002fe630c8017f3106400bb98832007be6419003ee320c801ee9906400fb4c832005fcc219002fd610c8017f3006400bf58032005fcc9a8802fd64d4401bf2a6a200df15351005fcc7a8802fd63d4401bfa9ea200df54f51005fcc5a8802fd62d4401f7196a200fb4cb51005fcc1a8802fd60d44017eb2ca200bf992510077cc928802be64944017eb24a200ef592510057ac928802fe63944017eb1ca200bf98a51007dcc528802ee62944017eb14a200fb58a51005dac528803ee3294401f6994a200bf98651006fea328803f751944017f304a200bf58251005fec8a8802fc6454401bf2a2a200df15151005fec6a8802fc6354401bfa9aa200df54d51005fec4a8802fc6254401f7192a200fb4c951007eea2a88037e51544017fb02a200bf18151005fcca28802fe64144017eb20a200bf98c51005fac628802fe6214401f7310a200bb98851005fac428803ed621440176b10a200fb8c851007da6428802fe6114401bfa88a200fd94451006faa228803f551144017f300a200bf58051005fecba0802fe65d04017eb2e8200bf197410077ea9a0
  | 6 => 0x17f318a600dfd4c53007bca6298037d5314c01eea98a600bf98853007dcc429802ee6214c017eb10a600fb58853005dac429802fe6114c01fb308a600bd98453005fac229803f56114c017ab08a600bf98053007f4c029802fa6014c017eb00a600fe58053005f2c029802ff65d0c017f32e8600bf59743005f8cba1803be54d0c01deaa68600bf98b43005fac5a1802fe61d0c017eb0e8600bf98343005fac1a1802ff6590c017f32c8600bf59643005f8cb21802fd6490c01dfaa48600ef15243005fcc721803de5390c01eea9c8600efd0e43007be8721802fe6290c01f73148600bb98a43005fac521803ed6290c0176b148600bf98643005fac321802fe6090c017eb048600bfd9543006fecaa18027f6550c017f32a8600bf59543005f8caa18037c6550c013e32a8600ef951430077aa8a1803de5350c01eea9a8600f7d0d430077c86a1802ff6250c017e3128600bfd8543005f8c2a1802ff6050c017e3028600bfd9443005fcca218037e6510c013f3288600bf59443006faca218027d6510c017e3288600bf990430077ea821803bc5410c017f3188600efd0c43007bc8621803bd4310c01eea188600bf98843007dcc421802ee6210c017eb108600fb58843005dac421802fe6110c01fb3088600bd98443005fac221803f56110c017ab088600bf98043007f4c021802fa6010c017eb008600fe58043005f2c021802fe64d48017eb26a400bf98f52005fac7a9002fe61d48017eb0ea400bf98352005fac1a9002fd65948017f324a400bf59252005fcc729002fd63948017f314a400dfd4a52007dea529002fe61948017eb0ca400bf98252005fac129002ff64548017e322a400bfd8d52005f8c6a9003ef5254801bf292a400bfd8552005f8c2a9002ff60548017e302a400bf99452005fcc829002fd64148017f318a400bf58c52005fcc4290037f5214801f7290a400df54852007daa429002fe6114801fb308a400bd98452005fac229003f561148017ab08a400bf98052005fac029002ff65d08017f32e8400bf59742005f8cba1002fe63d08017eb1e8400bf98742005fac3a1002fe60d08017eb068400bfd9642005fccb21002fd65908017e32c8400bf59242005fcc721002fd63908017f3148400fb94a42007daa521003bf4290801f7a148400bf98642005fac321002fe60908017eb048400bfd9542005fccaa1002fd65508017e32a8400bfd8d42005f8c6a1003ee5250801f6a928400fbd09420077c84a1002ff61508017e30a8400bfd8142005f8c0a1002ff65108017f3288400bf59442005f8ca21002fe64108017f3188400bf58c42005fcc421003bf4210801f72108400ef50842007da8421002fe6110801fb3088400bd98442005fac221003f561108017ab088400bf98042005fac021002ff65cc8017f32e6400bf5
  | 7 => 0x400600000000400000e00000200200000601202c00002000602200c00c01200000c00401202a00e00001e00200600000201200e00200000200000200601200c00000202200a00200400c00200c00c00600800000a00200202000a01000000c01401000600000600400000400202403a00000000000600600000e01002c00a00e00400400000201803200200400600400002200000002202600000e00800001200200000000000403600602800600800000000000200000e00e02a01c00400800000200000000003000600000000e00600001a00000002600c03000800000600e00000401000402a00000002a05c00200200a00001a00401202400000600001001600000a00201200600200a00c00e00a00200200200200004400a01400202400400400000a00600000000a00000c04601800803200400001000002400200001400200200200400000a06600200000e00a00003800a00201400400200000a00400e00000000400000200000c00800003e00202e00000004a02200000400800401802800400000000e00a00200001a00000000600200400401400001000e00000200000000e01c00200400e00001800600600001c00200c01200601801800a00000000a00400e00200400000a02c00c01608c00402a01e00800600200400200601005800600200001400000400bf98f54005fac7aa002fe62d50017eb16a800bf98754005fac3aa002fe60d50017eb06a800bf59654005fcc92a0037f5495001dfaa4a800cfd5254005fcc72a002fd63950017f314a800bf58a54005fcc32a002fd61950017f304a800bf582540077ea8aa0037e54550017fb1aa800bf18d54005fec4aa002fc62550017fb0aa800bf18554005fec0aa002fc60550017f328a800bf99054006fea82a003be5415001beaa0a800ef550540067aa82a002fe6315001ef318a800b798c54005fac62a003dd63150016eb18a800bf98854007dcc42a002ee62150017eb10a800fb58854005dac42a002fe6115001fb308a800bd98454005fac22a003f561150017ab08a800bf98054007f4c02a002fa60150017eb00a800fe58054005f2c02a002fe64d4c017eb26a600dfd5353006faa9a9802fe62d4c017eb16a600bf98753005fac3a9802fe60d4c017eb06a600bf59653005fcc929802fd6494c01bf2a4a600df15253005fcc7298037f5394c01efa9ca600bf98a53007dcc529802ee6294c017eb14a600fb58a53005dac529802fe6194c017eb0ca600bf98253005fac129802ff6454c01dfb22a600afd9153005f8c8a9803bc6454c015e322a600dfd5153006faa8a9803df5354c01bf29aa600bfd8953005f8c4a9802ff6154c017e30aa600bfd8153005f8c0a9802fe6514c017f320a600ef990530057cc829802fd6414c01deb20a600af59053006fca8298037c5414c0
  | 8 => 0xa95881550d70e7d8dc0000018840012413d11207dcbbd5690983786bc5356287112b96c4dcc510000b758ed3bc4d8cac96cbc404c000000624c6c1441d00006551e96c83ac76895549400000011c00097047536c49c001688000000000d0c0b962cde18257f89bd058334e44924000000000c4d8d51e5260c00ec97c4a0cca42e45e53d807810d7fd7083e0fd43ec000000e48118fec000338c3cc14fb4ffc72c80d498788c490885d92bcc640c8e2916d634f68ff40003c48c19485a4b84000b9c56074982c95c6c00b19ac45432c001638000be925c0000000005c0544fd8000408000c5400037cb60ff11040006a15c8000000520000960000c74fd076d2f400000099cdbcc8566d96cbfc6056406cd92487cabca9035957d70069822d588cf15006d599c5a181072438596830801ca184340015902d47a4ff94680000000000009e9908000000000314000000715818000864eb13e903c0000019005988e0d9d0115ac8a8940b24dc1990accf804895c15807e939cb54000c58cf57d48b95d818d0f42c8e00ea0109318b34d4c2e830ca38bd8878dac00000084d7a93780004e44680287d4fac65082d26ca48694a592d99a48302f977c0000006b95217952a96099393059841f1539754af4dd06d16e0d1446c10578138c56cd30cd43192647619d14f49a1980658ee58008ed685648e6d01cf5c20104d88cfe576c1c42410d8000148ced1a15a40008dc98000000119c0dc000741200e354a0b9922c000214000000cdc3d0d540000000001cd6c0f74001584cc0e38ebcd413499c8874bc013c00000152c000578c991ac00020d8b58e81e00003f1384000e0cbc8000000690c2881d67c00065cb18dc43d45c8310c8c16d0d548875c8687650b00015f4548080000e8000011450c2114140003f400147c9d0000000e080000000000000000000012310340001f800600601801c00000200601000e01401200e00600c01e00000401c00201a00000403202000800000200601600200200a00000401000000000801a01801202000200000600001600200001200201400600002800000000000000400000000a02000600002800000e01800000a00204800000000403400000000e00002a00001e00000200404200e02800005000000000000200200403607400201600a01600000401401401c00000e00000000e00000401400000000000e01400000000000000000a00202200602200e00800000e00c00000601600c02200e00001a00800002c02200004401803200a04200c00c00200001400400c00000401801000000c00000600e00200000c00800a00001400401c00400600c00000400600000e00c00801400e00400000200000003600200a01402800200000800a00200c00200000000000c00200201400400000c0040000120020040000000
  | 9 => 0x60c0016112980007f12d03642dd4ec000f2cef0920b3c0891e0ed40000018d07a14796e4f94000000870e90cc55100000017f4000680001560000418bb0e5cc400009091cc000000dfc08400110c83400092c3980000d4000000000001340ca8001870000000e853a0af0db0000000000000000cd8000f2951c00137c02d0404500ed9719cd0e0000ae42fd6984e9290600001029138b7d874a9d748a5c89d7b57351556ac29cd3c16425191467c1011d153c5581a003cc1ca701e427c4111840017b800043800000060c5f400070400000000000000180cbac0004140f93b07cc9d59ed7440000cc00080400000112c0014bc0000012780008099992a0b4d5e90b45651450151b0adc0006f193ce1400115d484000000000000a0959c0000014e86405400fd90c000bf0c202955d04f4c0d130f0c2200e40000a87e4bd53517911919d40016a486d3886d9740000f8c9504049914c5128000000000000e30df0d1d98cd3569c3a53f92c15309190f17c96015cd9303cc61cd643fc0681612159dc1b9598fb92254b4ab838054cf18ddd9fc48d2080010442f0d5000106800000155c28172d8b08e84dd4ac0000009c40000948f000000040190459571157563cf7c480c340009b45700058940000005cc7287a8000000cb40000000006e8000da941c000000a601980004bc00183d4018e1784ac000000041c00184417964c8f91d456920434d030fc4000c958c8cfc3755b40003e4d8497535c0001544200487c0000cb80002f40000001100012383e8c240b40002b16a86fc0000000500000010a4a44000590f0463c0000007fd17000178971909480000019400026cd6d320001834ef87380bc2a00010745189e1244d019b4e9502d9c13947717983a823911061807c0011f800043c0e0000e68000000000f106dd71c0010e8001541630000000e200015a83300000388440000004ad3e04842180000006ed2802e0a40969434e3c32923ce4c8d83bcdb85d40f529c6281b17a14d4948f5524d20c3d96040011405d19f00540000000017582994e40000006788813380000000000003056f06b4000fa94d00011f0000cd0e1c50107d0c96fd2e48b4eec0004c40001415087200000016d9960814c7c8286340007808112292c4df59200012f03b971462023c00000127d42c1209cc0000008bc0012fd4a8355614180aa00012e19500008c98bc001210001644fe0bf597c0017c0001858000001150e748b000070d2b50185b565cb0509c0019e4d900000012c800047d314000e700004b00000016702bc0004fd7b00000000001382057e0000000d48a84bb40001b4608001918f255e514d7a40009ed9bc0004703500001ec0000013d436c00169066c00113c00000092945cc78f646b0000b000013b89c800000182185cc69270a158f400156d6b000
  | 10 => 0xc173c78d8fc9f8e047186c83003917510c0ae821d5d403409d1795f93712594c0340270000d994cd554440000001288c108fd05c0019640000007c57bc2c4000000000000000000fc80000001e8b280000007009650b80019e0000eb89aca80a748998e4da4b211251c93758b8638a6c00176800001931028589c000d5c64d07800077954d92c2d148c000b780210d083800177962000158c000cf86f4fe8001284d75160f0855c000ae00100580014e00017ac7f49580005f80000010ccfa181d0a93ac1bc71c32591c6c5220ad88ccba53b4b5d4f19a0900bed424000ad412853cd8d51442c1c07445f0f410646a8aac85038c0009f40a42440013907d80014b000108c2ed8f02b9855109694f2039d978279070a3d5c5544001680000185100000000001898000000ccccb0000001994000000001295428b702749301587c90209140004b8938e64afc00000000000000058c0018085810f980400079473c000000b155793589c19880000000004c16d4000e88840000000000000000000001860000001354001838000000000e40f34508000000c5c93c5b15a0d7ce1825845c4cd8415f0a00000000b2c2a80003dc0000000004d4000ad0000000d2994c6a43b4f01889654000000ed866036091cc08d08aa87ed8a0bcd06c090fc16a000111c6757709a40011181502699b80005a80740010a051cf985554b8000ea91a98657214586f84a0000f89534a1c000588c60b445501dcdf80998280012189fd9292497309dcd256ed6bd3e4494e98000000000001704dd40000f000170c000478000000000eccaa44eca2140800000144544cea56f99c40000d19a8ee81a86e47b51884b50bc2d93688489b0ca0d454fd404d94f84ef4b80c2c4f879ce581a435d344b8cc80b6c7ac2c0cbd650c18e551fcf90aec6710c475806498c24d4a400144888801423068d1800000004c921d0ac668000b312ec431660000000d687351b4001570001360001559328458ce4c9c00079814c3a0a7d2557e53240013352d53005851954c87bc8d00004440000000000000000016cc40c188f38d595bc0015fc0444e0648994024ec40000014184a9090000da0000b5978d17c0017dc000c517ed54800140d0600000000002cc688371048d38130d104a4a655959f56749887b0be01c8f44efd5e0860b692512e8388a34ce85747552b09e50851340000000016b489000000118d149814f70174041830de41fd85132c0d8664000f58818a8d9f8000b940c400000033d84815c000d883f87f95180000000000014200005c40006ac5e98a52a424885d6584d00002342b4b640c098594459d3cca2d760b51774b487093c8ab419c9451ed198b885dd958000000bb8001080000a2408cdd98cc498000f6028c0007d0c89410000ee0000684e8c00000161c0a02298f946d
  | 11 => 0x1678854000000000f14000d200011dd28cb900013a462cb1d9555b16640708c40ac504f305ad50d0fc8ac3b0000000000910e9c0004480e9470000b093fcce025c8a09d96191d91f400069c74d940f6d438ac4a11975868a5134d0e4000e7883ceb4f480017f0000001725504be59100300000005fd4dd2dc57cba8525440000001330c39454d2c00143c0008e400138000000c464999564000000169005a00000821490905668a4c000000000000001398d196d0a7931d4817657d94f85287309356dd5ec0007519357291b90244f0429364fa53ed1156b8614001474dc800000005d8ac2607b81d4fbd74c31d87c6e17397e82256e851586c784cc8000f3c8f56f412503800077d5284619e979c0008258a8bf80010ec0012acb10000000008644000000bdc000f4d9d8edc8944919b013545162568d1c4538320f9cec13f0530000f50264001878a680006103493081f400184d234e600001701d8ba18c18913dc000f782880009f18d8f1ced0c44d053c01911a400000000149d33d8c494c000254bd00005b89b8a9806175ca547903950092cca0497cfb14311c052ca88af8209158290a317d036930cd60000fdd275054000eacc70c908d44250dcd78e2c0007e05e05bd00cd81524e50858a2812d3c47752f8b388a49a82a417cb0d1743c8001269169460000000000000000000000884e102ad5b89780000000010513a8dec1ac000344ab1000e24ac8db400000000090cc31164b4000000195c5ec0014d91bc06c63088d4657ccc0444d3f55dcfccde83
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe7319410004dd7319410004ee7219410004ed72194100047e75d90100047d75d9010004de73d9010004dd73d9010004ee72d9010004ed72d9010004bd76990100063e65990100063d6599010006b6719901000eae209901000eac20990100063e65590100063d655901000eae205901000eac20590100047e75190100047d7519010004be7419010004de7319010004dd7319010004ee7219010004ed72190100047e75d8c100047d75d8c10004be74d8c10004bd74d8c10004ee72d8c10004ed72d8c10004ee7298c10004ed7298c10004dd7698c100065e6598c100065d6598c100069e6498c100069d6498c10006ce7298c10006cd7298c1000ece2098c1000ecc2098c100065e6558c100065d6558c100069e6458c100069d6458c10006ce7258c10006cd7258c10006d47158c1000ece2058c1000ecc2058c100047e7518c100047d7518c10004be7418c10004bd7418c10004de7318c10004ee7218c10004ed7218c10004f67118c10004fa7018c100047e75d88100047d75d8810004be74d8810004bd74d8810004de73d8810004dd73d8810004ed76988100066e65988100066d6598810006ae6498810006ad6498810006ce6398810006cd6398810004ed739881000cee70988100066e65588100066d6558810006ae6458810006ad6458810006ce6358810006cd6358810004ef7358810004ef7158810004ed715881000cec70588100047e75188100047d7518810004be7418810004bd7418810004de7318810004dd7318810004ee7218810004f67118810004ef768c810004ed768c8100066e658c8100066d658c810006ae648c810006ad648c810006ce638c810006cd638c810005e5718c810004ef764c810004ed764c8100066e654c8100066d654c810006ae644c810006ad644c810006ce634c810006cd634c810005e7714c81000de8704c810004ee7298410004ed7298410004f57694410005b57494410006b56494410006d56394410006e56294410006766554410006b56454410006d56354410006e56254410004f57690410005757590410006756590410006d56390410006e56290410006756550410006b66450410006d56350410006e56250410004f576cc410006d563cc410006e562cc410004f5760c41000575750c410005b5740c410006d5630c410006e5620c410005f1700c410004ed76c84100066e65c84100066d65c8410006ae64c8410006ad64c8410006ce63c8410006cd63c8410004ef76484100066e65484100066d6548410006ae6448410006ad6448410006ce6348410006cd6348410006e6614841000cef729801000cec7298010006d563c4010006e562c4010004f97684010006d96384010004f77644010006d56344010006e5624401000fe02044010004fb7644010006d96344010007e32144010
  | 1 => 0xcb10005e5728c710006e66248710005e77648710006e77648710006e76548710006e56548710006e76448710006e56448710005e77348710005e57348710006e66348710006e4634871000de47048710005cd7308310005e57108310004be74d9610004bd74d9610004ee7299610004ed7299610004ef7259610004ec72596100047e75d92100047d75d9210004ee7299210004ed7299210004ef7259210004ec7259210004ee7298e10004ed7298e10004ef7258e10004ec7258e100047e7518e100047d7518e10004be7418e10004bd7418e10004ee7218e10004ed7218e10004ed73d8a1000ee571d8a1000eea70d8a100047e7518a100047d7518a10004be7418a10004bd7418a10004de7318a10004dd7318a1000e6e7518a1000e6d7518a1000eae7418a1000ead7418a1000ece7318a10004ed7318a1000ecd7318a10004cd7318a1000ee57118a1000eea7018a1000cee768ca1000cec768ca10005e5718ca1000cee764ca1000cec764ca10006ce634ca10006cd634ca10005e7714ca10005b57494610006e76294610006e76254610005757590610006e76290610006e76250610006e762cc61000575750c610005b5740c610006e7620c610005f1700c61000dea70c861000de87048610007c9324c210005f0714c210007d3314c21000ee762c4210004be74d9510004bd74d9510004ee7299510004ed7299510004f57199510004ef7259510004ec72595100047e75d91100047d75d9110004ee7299110004ed7299110004f57199110004ef7259110004ec7259110004ee7298d10004ed7298d10004ef7258d10004ec7258d10004f77158d100047e7518d100047d7518d10004be7418d10004bd7418d10004ee7218d10004ed7218d10004ed73d8910004ee7298910004ee7618910004ed7318910006e5711891000cee701891000cec7018910004ee768c910004ec768c910005e5718c910004ee764c910004ec764c910004f6768c510005e5728c510004f4764c510004ee76c8510005ea70c8510005e57288510006e46288510004ec7648510005e87048510004f47648510005f07048510006e77648510006e47648510004e47648510006e76548510006e56548510006e76448510006e56448510005e77348510005e57348510006e66348510006e46348510007e3704851000de47048510007e07048510005e07048510007e1218c110004f8764c110007c9324c110007d1314c110007e1214c110004ee7688110004ee7608110005cd7308110005e57108110007e121c411000de77284110004be74d9410004bd74d9410004de73d9410004dd73d9410004ee72d9410004ed72d94100047d769941000676719941000e6e209941000e6c209941000e6e205941000e6c20594100047e7519410004be7419410004bd7419410004d
  | 2 => 0xee4655842000ee76458420006e6645842000fa66458420006a66458420006e5645842000fa56458420006a5645842000ee4645842000ee76358420006e6635842000fc66358420006c66358420006e5635842000fc56358420006c5635842000ee4635842000ee66058420006e77558420006e67558420006e57558420006e47558420006e77458420006e67458420006e57458420006e47458420006e75458420006e65458420006e55458420006e45458420006e77358420006e67358420006e57358420006e47358420006e75358420006e65358420006e55358420006e45358420006e74358420006e64358420006e54358420006e4435842000ee6705842000ee4705842000ee6505842000ee4505842000ee6405842000ee4405842000ee6305842000ee43058420006cd63d4420006e561d442000dea70d4420005e970d442000cee7694420004ed7694420005ae7494420005ad7494420006cd6394420006e56194420006cd6354420006e5615442000cee7614420004ed7614420006cd6314420006e56114420006cd63d0420006e561d042000dea70d0420005e970d042000cee7690420004ed76904200056e75904200056d7590420006cd6390420006e56190420006cd6350420006e5615042000cee7610420004ed7610420006cd6310420006e5611042000cee76cc420004ed76cc420006cd63cc420006e561cc42000cee768c420004ed768c420006cd638c420006e5618c420004ed764c420006cd634c420006e5614c420005eb704c42000de8704c42000cee760c420004ed760c4200056e750c4200056d750c420005ae740c420005ad740c420006cd630c420006e5610c42000dea700c420005e9700c42000cef7398020004ed739802000eea709802000f6a659802000f69659802000faa649802000fa9649802000fca639802000fc9639802000fe2619802000fe16198020004ed76d4020006cd63d4020005e671d4020005e571d4020006e561d4020004ef7654020006cd6354020006e56154020004ed76d0020006cd63d0020005e671d0020005e571d0020006e561d0020004ef7650020006cd6350020006e56150020004ed76cc020006cd63cc020006e561cc020004ef764c020006cd634c020005e7714c020005e4714c020006e5614c020004be74d9710004bd74d9710004ee72d9710004ed72d9710004ee7219710004ed72197100047e75d93100047d75d9310004ee72d9310004ed72d9310004ee7219310004ed7219310004ee72d8f10004ed72d8f10004ee7298f10004ed7298f100047e7518f100047d7518f10004be7418f10004bd7418f10004ee7218f10004ed7218f10004ed7398b10006e67198b10004ef7358b10004ef768cb10004ed768cb10005e5718cb10004ef764cb10004ed764cb10005e8704
  | 3 => 0xf76594200066f765942000e6f645942000e6f635942000e6f615942000e6e605942000dad769902000f2e659902000f2d659902000eaf639902000eaf619902000eae60990200066d655902000daf7659020006af765902000eaf655902000f2e6559020006ad655902000f2d65590200062d655902000eaf635902000eaf615902000eae60590200072f549502000cee7615020004ed76150200072d5415020005ce7315020005cd7315020005e67115020005e5711502000dea7015020005e9701502000e6e75d8c2000e6d75d8c2000eae74d8c2000ead74d8c2000ee671d8c20004ed71d8c2000ee571d8c20004e571d8c2000cee70d8c2000eea70d8c20004ed7698c2000dcd7698c20004cd7698c2000f4e6598c2000f4d6598c2000f8e6498c2000f8d6498c2000ecf6198c2000ece6098c200066e6558c200066d6558c20006ae6458c20006ad6458c2000ecc6358c2000cef7358c2000ecf7358c20004ef7158c2000cec7058c2000ece3058c2000ecc3058c2000dcf7658c20006cf7658c2000ecf6558c20006ce6558c2000f4e6558c200064e6558c20006cd6558c2000f4d6558c200064d6558c2000ecc6558c2000ecf6458c20006ce6458c2000f8e6458c200068e6458c20006cd6458c2000f8d6458c200068d6458c2000ecc6458c2000ecf6158c2000ecc6158c2000ece6058c20006cf7558c20006ce7558c20006cd7558c20006cc7558c20006cf7458c20006ce7458c20006cd7458c20006cc7458c20006cf5458c20006ce5458c20006cd5458c20006cc5458c20006cf7158c20006ce7158c20006cd7158c20006cc7158c2000ece7058c2000ecc7058c2000ece5058c2000ecc5058c2000ece4058c2000ecc4058c2000ece1058c2000ecc1058c20006cd63d4c2000cee7694c20004ed7694c20006cd6394c20005af7454c20005ac7454c20006cd6354c2000cee7614c20004ed7614c20005ae7414c20005ad7414c20006cd6314c20005e67114c20005e57114c2000dea7014c20005e97014c20006cd63d0c2000cee7690c20004ed7690c20006cd6390c200056f7550c200056c7550c20006cd6350c2000cee7610c20004ed7610c200056e7510c200056d7510c20006cd6310c20005e67110c20005e57110c2000dea7010c20005e97010c20006cd639842000de5769842000f66659842000f65659842000fa6649842000fa5649842000ee7639842000fc66398420006e5639842000fc56398420006c5639842000ee660984200066e65584200066d6558420006ae6458420006ad6458420006ce6358420006cd635842000ee46158420004ef735842000ee6105842000ee4105842000de77658420006e7765842000ee76558420006e6655842000f666558420006666558420006e5655842000f656558420006656558420
  | 4 => 0x8520006e76148520004be74d9420004bd74d9420004de73d9420004dd73d9420004f671d9420004f571d94200047d76994200066e72994200066c72594200047e7519420004be7419420004bd7419420004de7319420004dd7319420004f67119420004f571194200047e75d90200047d75d9020004de73d9020004dd73d9020004f671d9020004f571d9020004bd76990200063e65990200063d6599020006ae72990200063e65590200063d6559020006ac72590200047e75190200047d7519020004be7419020004de7319020004dd7319020004f67119020004f571190200047e75d8c200047d75d8c20004be74d8c20004bd74d8c20004f671d8c20004f571d8c20004dd7698c200065e6598c200065d6598c200069e6498c200069d6498c20006ce7298c20004ed7258c200065e6558c200065d6558c200069e6458c200069d6458c20006ce7258c20006cc7258c200047e7518c200047d7518c20004be7418c20004bd7418c20004de7318c20004ee7218c20004f67118c20004f57118c200066d65d4820006cd63d4820004ed7694820006ad6494820006cd639482000dea70948200066e6554820006ad6454820006cd6354820004ed7614820006cd6314820005e67114820005e5711482000dea7014820006ad64d0820006cd63d0820004ed76908200066d6590820006cd639082000dea70908200066d6550820006ae6450820006cd6350820004ed7610820006cd6310820005e67110820005e5711082000dea7010820004ed76cc820006cd63cc820004ed768c8200066e658c8200066d658c820006ae648c820006ad648c820006cd638c820005e6718c820005e5718c82000dea708c8200066e654c8200066d654c820006ae644c820006ad644c820006ce634c820006cd634c820004ed760c820006cd630c82000dea700c820006766598420006756598420006b66498420006b56498420006d66398420006d56398420006e63298420006e53298420006766558420006756558420006b66458420006b56458420006d66358420006d56358420006e67258420006e75258420006e65258420006e55258420006e45258420006e74258420006e64258420006e54258420006e44258420006e73258420006e63258420006e53258420006e432584200066e65c84200066d65c8420006ae64c8420006ad64c8420006ce63c8420006cd63c8420006e561c842000dea70c8420004ed7688420006cd6388420006e561884200066e65484200066d6548420006ae6448420006ad6448420006ce6348420006cd6348420006e66148420006cd6308420006e5610842000dea7008420006cd63c8020006e561c8020004ef7648020006cd6348020006e56148020004fb764802000d6d769942000e6f639942000e6f619942000e6e609942000d6
  | 5 => 0x66d6548430006ae6448430006ad6448430006e66148430006e5614843000de87048430006cd62cc030006d561cc03000679658c030006b9648c030006f1618c030004df764c030006cd624c030006d5614c030004fb764c03000679654c030006b9644c030006f1614c030004f67119720004f57119720004f67119320004f57119320004f671d8f20004f571d8f20006cd638cb20005e5718cb20006cf634cb20006e561c8720004be74d9620004bd74d9620004f67199620004f571996200047e75d92200047d75d9220004f67199220004f57199220004f77158e20004f47158e200047e7518e200047d7518e20004be7418e20004bd7418e20004f67118e20004f57118e2000dea70d4a2000de87054a20005e67114a20005e57114a2000dea70d0a2000de87050a20005e67110a20005e57110a2000dea70cca20005e6718ca20005e5718ca20006ce634ca20006cd634ca2000de8704ca2000dea7088620006e66148620006e5614862000de87048620005e67199620005e57199620005e67199220005e571992200072f549522000cee7615220004ed76152200072d5415220005ce7315220005cd7315220005e67115220005e5711522000dea7015220005e97015220004ed71d8e2000eea70d8e2000ecf6398e20005e77158e20005e47158e2000ecf7358e20004ef7158e20006e77158e20004e77158e20006e47158e2000ece3058e2000ecc3058e2000cee7694e20004ed7694e20005af7454e20005ac7454e2000cee7614e20004ed7614e20005ae7414e20005ad7414e20005e67114e20005e57114e2000dea7014e20005e97014e2000cee7690e20004ed7690e200056f7550e200056c7550e2000cee7610e20004ed7610e200056e7510e200056d7510e20005e67110e20005e57110e2000dea7010e20005e97010e2000ee76198620004ef735862000ee6105862000ee4105862000cee7694620004ed7694620005ae7494620005ad749462000cee7614620004ed761462000cee7690620004ed76906200056e75906200056d759062000cee7610620004ed761062000cee76cc620004ed76cc620006cd63cc62000cee768c620004ed768c620006e5618c620004ed764c620006cd634c620006e5614c62000cee760c620004ed760c6200056e750c6200056d750c620005ae740c620005ad740c62000dea700c620005e9700c620005e671d4220005e571d4220005e671d0220005e571d022000ecf63cc22000ecf634c220005e7714c220005e4714c220004ed7299520004f67199520004f57199520004ef7259520004ed7299120004f67199120004f57199120004ef7259120004ed7298d20004ef7258d20004f77158d20004f47158d20004ee7218d20004ee768c920005e5718c920004ec764c920006cf634c920004ee76c
  | 6 => 0x77159530004f47159530004ee7299130004ed7299130004f67199130004f571991300047f75591300047c7559130004ef7259130004ec7259130004f77159130004f47159130004ed71d8930004ed7118930006cc62cc930005cd738c930005e5718c930005ea708c930005e8704c930005cf714c930007cb704c93000dcc704c930007c8704c930006e762d8530006e462d8530007c532d8530006e772d8530006e472d8530006e632d8530006e532d85300047e75185300047d7518530004be7418530004bd7418530004ee7218530004ed7218530006e76218530006e46218530007c53218530006767518530006757518530006b67418530006b57418530006e67218530006e57218530006e63218530006e53218530006f17018530005cd72cc530006d461cc530004ee76c8530004ec76c8530005cd73c8530006e761c8530006e461c8530004ee7648530004ec7648530005cd7348530006e76148530006e46148530007c73148530005b97494130007c93294130004f87654130007c93254130005797590130007c93290130004f87650130007c93250130007c932cc130004be74d9430004bd74d9430004ee72d9430004ed72d9430004f671d9430004f571d94300047d769943000e6e209943000e6c209943000e6e205943000e6c20594300047e7519430004be7419430004bd7419430004ee7219430004ed7219430004f67119430004f57119430004fa70194300047e75d90300047d75d9030004ee72d9030004ed72d9030004f671d9030004f571d9030004bd76990300063e65990300063d659903000eae209903000eac20990300063e65590300063d655903000eae205903000eac20590300047e75190300047d7519030004be7419030004ee7219030004ed7219030004f67119030004f57119030004fa70190300066e65988300066d6598830006ae6498830006ad6498830004ed71988300066e65588300066d6558830006ae6458830006ad6458830004ef7158830004ed768c8300066e658c8300066d658c830006ae648c830006ad648c830005e5718c830004ef764c8300066e654c8300066d654c830006ae644c830006ad644c830006ce634c830004ee7298430004ed7298430006766598430006756598430006b66498430006b56498430006e66298430006e56298430006e67298430006e57298430006e63298430006e5329843000ee6209843000ee42098430006766558430006756558430006b66458430006b56458430006e66258430006e56258430006e67258430006e57258430006e63258430006e5325843000ee6205843000ee42058430004ef76c8430004ed76c84300066e65c84300066d65c8430006ae64c8430006ad64c8430006e661c8430006e561c8430004ef7648430004ed76484300066e6548430
  | 7 => 0xca400066d658ca40005e5718ca400066e654ca400066d654ca40006ce634ca40006cd634ca40004ee7298640004ed72986400066e65c86400066d65c86400066e65486400066d6548640006e66148640006e5614864000de870486400067a65542400063e65d0240004ee7299540004ed7299540004f67199540004f57199540004ef7259540004ec7259540004be76d51400063f65d5140005ba70d51400063d65151400059d7315140005ad7215140005b57115140005ba70151400047e7518d400047d7518d40004ee7218d40004ed7218d40004f67118d40004f57118d400053c7550d40004ed73d8940004ed71d8940004f67118940004f57118940005e57118940004ed7318940006e67118940004ed7118940006e57118940004e57118940006ac62d0940004ee768c940004ec768c940005e5718c940004ee764c940004ec764c940004ee7218540004ed7218540006b46150540004ee76c8540004ec76c8540004ee7648540004ec7648540007a54148540005e87048540005ba7494140004f876541400073854541400053e7590140004be74d9440004de7319440004dd7319440004ee7219440004ed7219440004f67119440004f57119440004fa7019440004ee7298c40004ed7298c40005e5718c840006ce634c840006cd634c840004ee7298440004ed7298440006e66148440006e561484400047e75980400047d7598040004bf7650040004fb7650040004ee72d9730004ed72d9730004bf7459730004bc7459730004be7419730004bd7419730004ee7219730004ed7219730004f67119730004f57119730004ee72d9330004ed72d93300047f75593300047c75593300047e75193300047d7519330004ee7219330004ed7219330004f67119330004f57119330004f67198b30004f57198b30005e57198b30006e67198b30004ed7198b30006e57198b30004e57198b30004ef7158b30005e5718cb30006ce624cb30005cf764cb30006cf764cb30005cf714cb3000dcc704cb30004ee7298730004ed7298730005cd72cc730004ef76c8730004ed76c8730005cd73c8730004ef7648730004ed7648730005cd7348730007c73148730005e87048730004be74d9630004bd74d9630004ee7299630004ed7299630004f67199630004f57199630004ef7259630004ec72596300047e75d92300047d75d9230004ee7299230004ed7299230004f67199230004f57199230004ef7259230004ec7259230005e5718ca3000dea708ca3000de8704ca30004ee7298630004ed7298630004ef7258630004ec725863000cee76c863000cec7648630006e66148630006e56148630005b97494230005797590230004ee7299530004ed7299530004f67199530004f57199530004bf7459530004bc7459530004ef7259530004ec7259530004f
  | 8 => 0x6e57258750006e63258750006e53258750006766154750004ef76c8750004ed76c8750006e661c8750006e561c8750004ef7648750004ed7648750006e66148750006e56148750007655148750004ee7299250004ed7299250004f67199250004f57199250006ae7299250006ad7299250006b67199250006b57199250006ba709925000eae209925000eac209925000eae205925000eac2059250004ee7298e50004ed7298e50006ae648ca50006ad648ca50005e5718ca50006ae644ca50006ad644ca50006ce634ca50006cd634ca50004ee7298650004ed7298650006ae64c8650006ad64c8650006ae6448650006ad6448650006e66148650006e5614865000de870486500063e64d42500063f64951500057a70951500055d73151500056d72151500057571151500057a7015150004be7418d50004bd7418d50004ee7218d50004ed7218d50004f67118d50004f57118d500053c7454d50004ed73d8950004ed71d8950004f67118950004f57118950005e57118950004ed7318950006e67118950004ed7118950006e57118950004e571189500066c62d4950004ee768c950004ec768c950005e5718c950004ee764c950004ec764c950004ee7218550004ed7218550006746154550004ee76c8550004ec76c8550004ee7648550004ec7648550007655148550005e870485500053e7494150004ee7298c50004ed7298c50005e5718c850006ce634c850006cd634c850004ee7298450004ed7298450006e66148450006e561484500047f7654050004fb7654050004ee72d9740004ed72d9740004f671d9740004f571d9740004de7319740004dd7319740004ee7219740004ed7219740004f67119740004f571197400063d65153400059d7315340005ad7215340005b57115340005ba7015340004ee7298f40004ed7298f400053c7550f40004ed7398b40004ed7198b40004ef7358b40004ef7158b40006ae6250b40004ef768cb40004ed768cb40005e5718cb40004ef764cb40004ed764cb400047e75987400047d7598740004ee7298740004ed7298740006e66298740006e56298740006767598740006757598740006e67298740006e57298740006e63298740006e53298740006e66258740006e56258740006b75458740006b45458740006b74358740006b54358740006e67258740006e57258740006e63258740006e53258740006b66150740004ef76c8740004ed76c8740006e661c8740006e561c8740004ef7648740004ed7648740006e66148740006e56148740007a54148740004ee7299640004ed7299640004f67199640004f571996400066e72996400066d72996400067671996400067571996400067a709964000e6e209964000e6c209964000e6e205964000e6c2059640004ee7298e40004ed7298e400066e658
  | 9 => 0x56354521007675354521007655354521005e77054521004ee7614521005e67114521007655114521004ee76905210056e75905210056d7590521005e67690521006e67690521005e77590521007667590521005e57590521007657590521005657590521005e57490521005e67390521006e76390521006e56390521005e57090521005e67650521005e47650521005e77550521005e57550521007a77450521007a76450521007a46450521007a75450521007a45450521005e47350521006e76350521006e56350521007a74350521007a54350521005e77050521004ee7610521005e67110521007a54110521004ee76cc521006cf63cc521005e676cc521006e676cc521004e676cc521005e476cc521005e775cc521005e575cc521005e774cc521005e574cc521006e763cc521007c763cc521006e563cc521007c463cc521005e570cc521004ee768c521005e6718c521004ed764c521006cf634c521004ee760c5210056e750c5210056d750c521005ae740c521005ad740c521005ea700c521005e9700c521005e6760c521006e6760c521005e7750c52100766750c521005e5750c52100765750c52100565750c521005e7740c521007a6740c521005e5740c521007a5740c521005a5740c521005e6730c521007c6730c521006e7630c521006e5630c521007e2700c521005e5700c521007e1700c521005e1700c5210056e75181210056d7518121005ae7418121005ad7418121005ce7318121005cd731812100e6e751812100e6d751812100eae741812100ead741812100ece7318121004ed731812100ecd7318121004cd7318121006e65118121006e55118121006e64118121006e54118121006e73118121006e43118121004be74d9421004bd74d9421004ee72d9421004ee7219421004f671194210047e75d90210047d75d9021004ee72d9021004ee7219021004f67119021004ee72d8c21004f671d8c210047e7518c210047d7518c21004be7418c21004bd7418c21004ee7218c21004fa7018c21004f97018c21004ed7398821004ef768c821004ed768c821006cd638c821005e5718c821004ef764c821004ef7648421004f77648421006e662484210063d64153500055d73153500056d72153500057571153500057a7015350004ee7298f50004ed7298f500053c7454f50004ed7398b50004ed7198b50004ef7358b50004ef7158b500066e6254b50004ef768cb50004ed768cb50005e5718cb50004ef764cb50004ed764cb50004be7498750004bd7498750004ee7298750004ed7298750006e66298750006e56298750006b67498750006b57498750006e67298750006e57298750006e63298750006e53298750006e66258750006e56258750006765458750006745458750006775358750006755358750006e67258750
  | 10 => 0x47210056e75907210056d7590721006cd63cc721006cd634c7210056e750c7210056d750c721005ae740c721005ad740c721005ea700c721005e9700c721004ed73983210056e75183210056d7518321005ae7418321005ad7418321005ce7318321005cd7318321004be74d9621004bd74d96210047e75d92210047d75d92210047e7518e210047d7518e21004be7418e21004bd7418e21004fa7018e21004f97018e21005e5718ca21006cd634ca21005b57494621005757590621005e672cc62100575750c621005b5740c621005f1700c621004fa7099521004f97099521004fa7099121004f97099121004ed7298d21004fb7058d21004f87058d21004ee76d4921005e671d4921004ec7654921005e67114921004ee76d0921005e671d0921004ec7650921005e67110921004ee76cc921005e6718c921004ec764c921006cf634c921005e4714c921004ee760c921005b57494521005e67294521004f47654521005757590521005e67290521004f47650521004f676cc52100575750c521005b5740c521005e6720c521005f1700c5210047e75181210047d7518121004be7418121004bd7418121004de7318121004dd7318121005e57199521005ea7099521005e97099521005e77159521005e57199121005ea7099121005e97099121005e77159121005e671d5121005e571d51210072f5495121005e67195121005e57195121004ee7615121004ed76151210072d5415121005ce7315121005cd7315121005e67115121005e57115121005ea7015121005e97015121006e571d8d2100cee70d8d21005e57198d21005e77158d21005eb7058d21005e87058d21006cf7358d21004ef7158d21006e77158d21006eb7058d2100cec7058d21006e87058d21004e87058d21004ee7618d21005e671d4d21005e571d4d21004ee7694d21004ed7694d21005af7454d21005ac7454d21005e77154d21005e47154d21004ee7614d21004ed7614d21005ae7414d21005ad7414d21005e67114d21005e57114d21005ea7014d21005e97014d21005e671d0d21005e571d0d21004ee7690d21004ed7690d210056f7550d210056c7550d21005e77150d21005e47150d21004ee7610d21004ed7610d210056e7510d210056d7510d21005e67110d21005e57110d21005ea7010d21005e97010d21005e575d8521005e574d8521005e673d8521005e570d8521004ee7694521005ae7494521005ad7494521007675194521005e67694521006e67694521005e57594521007a67494521005e57494521007a57494521005a57494521005e67394521006e76394521006e56394521005e57094521005e67654521005e47654521007677554521007676554521007646554521005e77454521007665454521007645454521005e47354521006e76354521006e
  | 11 => 0x6e56294631006e56254631005757590631006e56290631006e56250631006e562cc631004ef7258231004ec7258231004ee72d9531004ed72d9531004bf7459531004bc7459531004ee7219531004ed7219531004ee72d9131004ed72d91310047f75591310047c7559131004ee7219131004ed7219131005e87058931005e5718c931005e7714c931005b57494531004f47654531005757590531004f47650531004ee72d8131004ed72d81310047e75181310047d7518131004be7418131004bd7418131004ee7218131004ed7218131004be74d9431004bd74d9431004ee72d9431004ed72d9431004fa70d9431004f970d94310047d76994310047e7519431004be7419431004bd7419431004ee7219431004ed7219431004f67119431004fa7019431004f970194310047e75d90310047d75d9031004ee72d9031004ed72d9031004fa70d9031004f970d9031004bd76990310063e65990310063d65990310063e65590310063d65590310047e75190310047d7519031004be7419031004ee7219031004ed7219031004f67119031004fa7019031004f970190310066e65988310066d6598831006ae6498831006ad6498831006e6719883100cee70988310066e65588310066d6558831006ae6458831006ad645883100cec7058831004ed768c8310066e658c8310066d658c831006ae648c831006ad648c831005e5718c831004ef764c8310066e654c8310066d654c831006ae644c831006ad644c83100675658c431006b5648c431005e5728c431004df764c431004f7764c43100675654c431006b5644c4310067a6598031006796598031006ba6498031006b96498031006ea6298031006e9629803100eeb729803100ee87298031006ea3298031006e93298031004ef7258031004ec72580310067a6558031006796558031006ba6458031006b96458031006ea6258031006e96258031006eb7258031006e87258031006ea3258031006e93258031006db3158031006f23158031006d93158031006f13158031006cd638cb21005e571d9721005e57119721005e571d9321005e571193210072f5495321004ee7615321004ed76153210072d5415321005ce7315321005cd7315321005e67115321005e57115321005ea7015321005e97015321005e571d8f21006e571d8f2100cee70d8f21006cf7358f2100cec7058f21005e57118f21004ee7694f21004ed7694f21005af7454f21005ac7454f21004ee7614f21004ed7614f21005ae7414f21005ad7414f21005e67114f21005e57114f21005ea7014f21005e97014f21004ee7690f21004ed7690f210056f7550f210056c7550f21004ee7610f21004ed7610f210056e7510f210056d7510f21005e67110f21005e57110f21005ea7010f21005e97010f21005ae7494721005ad749
  | 12 => 0xe7218d51004ed7218d51004fa7018d51004f97018d510053c7454d51005e5718c9510053e7494551004ee72d8151004ed72d8151004ee7298c51004ed7298c51004ed739885100cee7098851004ef735885100cec7058851004ef768c851004ed768c851005e5718c851004ef764c851004ed764c851006e562944510047f7654451004f77654451006e56254451004ef7258051004ec7258051004de7319741004dd7319741004ee7219741004ed7219741004fa7019741004f970197410063d65153410059d7315341005b67115341005b97015341004ee7298f41004ed7298f410053c7550f41005e5718cb410047e75983410047d7598341004ef7258341004ec7258341004ee72d9641004ed72d9641006767199641004ee7219641004ed7219641004ee7298e41004ed7298e410066e6598a410066d6598a41004ed7398a41006e67198a4100cee7098a410066e6558a410066d6558a41004ef7358a4100cec7058a41004ef768ca41004ed768ca410066e658ca410066d658ca41005e5718ca41004ef764ca41004ed764ca410066e654ca410066d654ca41005e57294641006e56294641006766554641006e562546410063e65d0641004ef7258241004ec7258241004ee7219541004ed7219541004be76d51410063f65d5141005b671d51410063d65151410059d7315141005b67115141005b970151410047e7518d410047d7518d41004ee7218d41004ed7218d41004fa7018d41004f97018d410053c7550d41005e5718c941005b67494541005e57294541004f476545410073454545410053e7590541004ee72d8141004ed72d8141004be74d9441004ee72d9441004ed72d9441004de7319441004dd7319441004ee7219441004ed7219441004f67119441004fa7019441004f97019441004ee7298c41004ed7298c41004ed739884100cee7098841004ef735884100cec7058841004ef768c841004ed768c841005e5718c841004ef764c841004ed764c8410047e75984410047d7598441006e56290441004bf7650441004f77650441006e56250441004ef7258041004ec7258041004ee72d9731004ed72d9731004bf7459731004bc7459731004be7419731004bd7419731004ee7219731004ed7219731004fa7019731004f97019731004ee72d9331004ed72d93310047f75593310047c75593310047e75193310047d7519331004ee7219331004ed7219331004fa7019331004f97019331006e57198b3100cee7098b3100cec7058b31004ef7258331004ec7258331004be74d9631004bd74d9631004ee72d9631004ed72d9631004ee7219631004ed72196310047e75d92310047d75d9231004ee72d9231004ed72d9231004ee7219231004ed721923100cee7098a3100cec7058a31005e5718ca31005e7714ca31005b57494631
  | 13 => 0x8232005e571d8232006e561d8232006e66198232006e56198232004ed7198232006e561582320056e75182320056d7518232005ae7418232005ad7418232005e67118232005e57118232006e66118232006e56118232004bf7459532004bc7459532004f67119532004f571195320047f75591320047c7559132004f67119132004f57119132004ee76d4932004ec7654932005e67114932005e57114932004ee76d0932004ec7650932005e67110932005e571109320047e75181320047d7518132004be7418132004bd7418132004f67118132004f57118132005cd7399532005af7459532005ac7459532005cf7359532005e67119532005e57119532005cd73991320056f75591320056c7559132005cf7359132005e67119132005e571191320072f5495132004ee7615132004ed76151320072d5415132005ce7315132005cd7315132005e67115132005e57115132005ea7015132005e97015132005e671d8d32005e571d8d32007c671d8d32007c571d8d32005cd70d8d32004ee7694d32005af7454d32005ac7454d32004ee7614d32005ae7414d32005ad7414d32005e67114d32005e57114d32005ea7014d32005e97014d32004ee7690d320056f7550d320056c7550d32004ee7610d320056e7510d320056d7510d32005e67110d32005e57110d32005ea7010d32005e97010d3200cee70d8532005eb7058532005e87058532006e56118532005e77158132005e471581320056e75181320056d7518132005ae7418132005ad7418132005e67118132005e5711813200e6e751813200e6d751813200eae741813200ead741813200ee67118132004ed711813200ee57118132004e57118132004ee72d9432004be7419432004bd7419432004ee7219432004f67119432004f57119432004fa7019432004f97019432004ee72d90320047e75190320047d7519032004ee7219032004f67119032004f57119032004fa7019032004f97019032006e67198832006e57198832005e5718c832004df764c832006ce624c832004ef764c8320063d64153510055d7315351005767115351005797015351004ee7298f51004ed7298f510053c7454f51005e5718cb51004be7498351004bd7498351004ef7258351004ec7258351006b67199251004ee7298e51004ed7298e51006ae6498a51006ad6498a51004ed7398a51006e67198a5100cee7098a51006ae6458a51006ad6458a51004ef7358a5100cec7058a51004ef768ca51004ed768ca51006ae648ca51006ad648ca51005e5718ca51004ef764ca51004ed764ca51006ae644ca51006ad644ca510063e64d4651004ef7258251004ec7258251004ee7219151004ed72191510063f64951510057671951510055d7315151005767115151005797015151004be7418d51004bd7418d51004e
  | 14 => 0x6f1619804300eeb729804300ee87298043004ef7258043004ec72580430067a6558043006796558043006ea6258043006e96258043006f26158043006f16158043006bb5458043006b85458043006bb4358043006b94358043006eb7258043006e87258043004be7498352004bd7498352004f67119152004f571191520047f7654852004ef7654852006e67258452006e65258452006e55258452004de7319742004dd7319742004f67119742004f57119742004fa7019742004f970197420047e75983420047d7598342004f67119642004f57119642004f67119542004f57119542004ec7654942004f671d9442004f571d9442004de7319442004dd7319442004ee7219442004f67119442004f57119442004fa7019442004f97019442004bf7650842004ef7650842006e67258442006e64258442006e54258442004be7419732004bd7419732004f67119732004f57119732004fa7019732004f970197320047e75193320047d7519332004f67119332004f57119332004fa7019332004f97019332004be74d9632004bd74d9632004f671d9632004f571d9632004f67119632004f571196320047e75d92320047d75d9232004f671d9232004f571d9232004f67119232004f57119232005ce7314a32005e67114a32005e57114a32005e67110a32005e57110a32006e67258632006e75258632006e65258632006e55258632006e45258632006e74258632006e64258632006e54258632006e44258632006e73258632005ae74d9632005ad74d9632005cd73d9632005e671d9632005e571d9632005cd7319632005e67119632005e571196320056e75d92320056d75d9232005cd73d9232005e671d9232005e571d9232005cd7319232005e67119232005e571192320072f5495232004ee7615232004ed76152320072d5415232005ce7315232005cd7315232005e67115232005e57115232005ea7015232005e97015232005af7454e32005ac7454e32005ae7414e32005ad7414e32005e67114e32005e57114e32005ea7014e32005e97014e320056f7550e320056c7550e320056e7510e320056d7510e32005e67110e32005e57110e32005ea7010e32005e97010e3200cec7058632006e77658632006e76558632006e66558632006e56558632006e46558632006e76458632006e66458632006e56458632006e46458632006e77558632006e67558632006e57558632006e47558632006e77458632006e67458632006e57458632006e47458632006e75458632006e65458632006e55458632006e45458632006e57358632006e75358632006e65358632006e55358632006e45358632006e74358632006e64358632006e54358632006e44358632006e77058632006e67058632006e57058632006e47058632006e56118632005e671d
  | 15 => 0x67298453006e57298453006b66458453006b56458453006e66258453006e56258453006765458453006745458453006775358453006755358453006e67258453006e57258453006ba6498053006b96498053006ea6298053006e96298053006f26198053006f1619805300eeb729805300ee87298053004ef7258053004ec7258053006ba6458053006b96458053006ea6258053006e96258053006f26158053006f161580530067a54580530067854580530067b5358053006795358053006eb7258053006e87258053004ee7219743004ed7219743004f67119743004f57119743004fa7019743004f970197430063e65953430063c65553430047e75987430047d7598743004ee7298743004ed72987430047e75983430047d7598343004ef7258343004ec7258343004ee72d9643004ed72d9643004ee7219643004ed7219643004f67119643004f57119643004fa7019643004f970196430063d65d52430059d73d52430063f65152430059d73152430071c5494e430059c7454e430071f5454e43004f67198a43004f57198a43005e57198a43006e67198a43004ed7198a43006e57198a43004e57198a4300cee7098a43004ef7158a4300cec7058a43004ee7298643004ed7298643004ef7258243004ec7258243004f77158243004f471582430047e7599543004bf7459543004ee7219543004ed7219543004f67119543004f57119543004fa7019543004f970195430047e76195430063d74195430065d73195430066e72195430066d72195430067671195430067571195430067a7019543006797019543004be76951430063c6595143004bc76551430063c65551430065c6594d430071e5494d43004dc7654d430071d5454d430063c6590d43004ee7218543004ed7218543004ee72d8143004ed72d8143004ee72d9443004ed72d9443004f671d9443004f571d9443004fa70d9443004f970d94430047d76994430063c74594430047e7519443004be7419443004de7319443004ee7219443004ed7219443004f67119443004f57119443004fa7019443004f97019443004bd76d50430063d65d5043004bd76150430063d65150430059d73150430063d65d0c430065d6590c43004bf7650c430053c7550c430063d6550c43004df7650c430065d6550c430066e65988430066d6598843004ed719884300cee70988430066e65588430066d6558843004ef715884300cec7058843004ee7298443004ed7298443006766598443006756598443006e66298443006e56298443006e67298443006e57298443006766558443006756558443006e66258443006e56258443006b75458443006b45458443006b74358443006b54358443006e67258443006e572584430067a6598043006796598043006ea6298043006e96298043006f26198043
  | 16 => 0x8754004ef7258354004ec72583540053d76d52540063d76d5254004ee7298e54004ed7298e54004ee7298654004ed7298654004ef7258254004ec7258254004ee7218d54004ed7218d54004f67118d54004f57118d54004fa7018d54004f97018d54004f67118954004f57118954004ee7218554004ed7218554004ee72d8154004ed72d8154004f671d8154004f571d81540053d75950540063e65950540047f7655054004bf76550540053f76550540063f76550540043f76550540053c73550540053f71550540053f7055054004ee7298c54004ed7298c540071d5498c54006ce7298c54006cd7298c540063d5458c540071d5458c540065f5458c540069e5458c540065d5458c540069d5458c540061d5458c54006ce7258c54006cd7258c540072d5498854006ce6398854006cd6398854004ed7398854004ed719885400cee70988540072d5458854006ce6358854006cd6358854004ef7358854004ef715885400cec7058854004ee7298454004ed7298454007355498454006d66398454006d56398454006e66298454006e56298454006e67298454006e57298454007355458454006d66358454006d56358454006e66258454006e56258454006e67258454006e57258454007395498054006da6398054006d96398054006ea6298054006e96298054006f26198054006f1619805400eeb729805400ee87298054004ef7258054004ec7258054007395458054006da6358054006d96358054006ea6258054006e96258054006f26158054006f16158054006eb7258054006e872580540063e64d5353004be7498753004bd7498753004ee7298753004ed7298753004be7498353004bd7498353004ef7258353004ec72583530063d64952530055d73952530055d7315253004f67198a53004f57198a53005e57198a53006e67198a53004ed7198a53006e57198a53004e57198a5300cee7098a53004ef7158a5300cec7058a53004ee7298653004ed7298653004ef7258253004ec7258253004f77158253004f47158253004ee7219153004ed7219153004f67119153004f57119153004fa7019153004f970191530069d7319153006ae7219153006ad7219153006b67119153006b57119153006ba7019153006b970191530047e76d51530063c64d51530063c64551530063c6494d53004ee7218553004ed7218553004ee72d8153004ed72d81530047d76950530063d64950530063d64150530055d73150530063d64d4c530069d6494c530047f7654c530053c7454c530063d6454c53004df7654c530069d6454c53006ae6498853006ad6498853004ed719885300cee7098853006ae6458853006ad6458853004ef715885300cec7058853004ee7298453004ed7298453006b66498453006b56498453006e66298453006e56298453006e
  | 17 => 0x203b00000c00000900700000c00800300f00000304300100300000100000100f00601c00800000100101000900b00c00000300101900200500000500000200300100000601503301b01600800000100100200400200000600100100100400100200000c00000e00000400000400600000700400000b00700000200300000000500300000402100200000202501500000800100000002a00000300000400b00200000d00100500b00000000300900000200600500100000000701700100100a00601a00600601200000200000000501400200100300300600000103500500b00000500000100a02300000001c00300300001f01200000502400400000000500200000b00d00000700000000301100100c00000200600200203e00100300200000300000400000000000000000000400300001d00e00100500201400e00000000000100200300800100300200000100700400d00002001700302000200100400500101300000402700000600801700101000300800100700700101700c00000000b02101200400c00102100000500000a00400100100300400e00400000502300900000000000100200a01100500700500101200800100400100f00000100100a00600200f00600900201901e01c00500000200000000100300000000000200303400104d01200000101300100600200300103b00e00000400500000100100100100000900000001a00200000100701600901100200201300602100500000300300401c01200c00200701a00b00000200100e00500000000500200003500300000600500000100200500200100700300d00900100000200700000400400000300300000103b00100000000000000300100100400a00200000300000b00200500000000700f00000201002300101a00000800600100f00100101000200501d00100000d00200601000000000100000000000800100000100300600f00600100100000100003300100200a00300602600100402c00600d00a00500100900b00000500200900000000000100100100300000000200200000700600100200400100000400200b01700500800200900100600102a00900000100600200301500a00100800d01100000001800000600000702e00500101200100800600100000506200500200100200400200600000000f00000c00300100100801500002300300100800000200701800d00502e00100400000101d00003300001700000400100c00400500c00000400900000000400200a00100200700a00100100401200000800400000300001d00b001008001003000002009004000010019000000000000007001002000003000011001002004007002000004005000000001008000001003005001003024004005000004ee7298f54004ed7298f54004ee7298754004ed729
  | 18 => 0x89701ba558892920c87322c22246200002e0a3ec5d60003b7891800000048b00001685fc2af842c00066654c05100000004ac850400000000000013787ef394a2988cc7243d50a849e68b934d1dfcfdc00000000011742100001bc88e400000b0000000000000207800000000029e4d54544437a50523a2360000000f6046500025981b8afe00021ac5700002a800000006a00000b300008fa5789cb84e490c20f20dd0020004d200000003240000ef406a3ab314000000000024ead2900e00016287fc00000030e00001e60002c6ac00e46b3e50283a4cd200028d907031a2aa0001060acc47153a0000c3000021700014002f238f800000000046d0e500004ec0000fdd4706804bc17c80000003a880000003610001fc86e45e607ca8f07f029f15410a80002a94312508dac4b936ca18c0000001650668cf4adf3a99a2805a72738180000007391be93e8a38000548ad484c200040117f44d0b0e3422b1458648f07d9614e0848e0002c50efa65e07d283c76c000532a8fc0001220108000c489db2e204301ce8e137681a449aa3a1c2800000000000000007382f7061019d6a00002a3930000000052c00000006dc00021f86ca7382038af426c6df0b98b510401a944129080004021630d789f85f52112b8938600026325285045263d9994c9ac87644d0000cdc38600017d94ae88d28c00000de46e0180000572af02338000dc43044b729692ec4952e705340003110000000b9800050513e434e8c111698f4a860ec0002818324a97000264434215647e91d4a487f715923f12c600300100200000300000000200700100200300400701c01601300000202200b03200000100500a01202000100b00700100100500100500a00d00504300000600400000100100200802200400000b00500500101200001900000900000000000000100000000500a00000000000003900400200000200000600400200600000100a00500000700300101a00701603400100300500700000200100700001900000200000400400f03600100200400300000400201600c00100f01600f00401c00100a00500000300600001000300b00f00400000600600300200000900800100700100000301200000100300000400200100100100202900000000201400200100400000100e01000000300400801000200000000100700300100100000200200100000e00e00d00000000000300800000100200000700a00300e01e00901300100000100f00500101401a00200000100100600000000e00f00003500300300000f03700100300200000100100a00700600900100200000000900300c00e00000900800200000500200000500300001101600000000000100300000000000000100000100000400900200000204e00400100b00200a02a01800200100300c00b000001
  | 19 => 0x40511594e3434c3fd133c2724a011a9880e7c977014a8cd02a4843520c552208cf4f30bb079a9d12bdac7c00036b28093fd51499c18e981c7f600032208dc6f251656d000054e0001b780010442c900000000007a854d8264e0a4e71088000d1e2e850c97b0ce28cb1e49f6c79c00000023d8d169134e1286c0000002a017ec0001300001764bb86ac13813400000004688e7400000000021180000000000834054aaa28f164071e7435932790a329e35aa8f454e0799339896837c9c90ee00d00009055292bc8880000326a75c00062c08c04c800036055984f15789a550e21f0d2a5675a402e53b800d57da11d13683d0000000000240077067d69a598000088c0008c80e024dc0005921ed00013caa0836187ecba622a01e00009a43a01528a340000000002b3c9d28311bf1c988fe00023b0db8f7e0000000001648000187a980dc6000237800000000042980006e888e5219c6525e00000023cc4ae00000000000003d400000000002de4440e90000a84000000000005937d0ba413a91807b04a01c89ca0000000cb800000022415b00d0000105000050d32a8f6d5743d356a80009a626e3feaccc1ac00018c9ff9616b291072a0535e6c81a215c07260003c495dc16e63639b012c6d26cf3d900008124c129014b8adc8083fcaabceda2fc5700001672aea3d4a3713ea3eb099a1701660a04d096391a46790002b3044c0011e61719538a6700028dd0cc0000001a405960804c181b4c601215192b2829638d536000099c0cd57b26c518ea9a0001344000a632df29fcee81f632d0e38000b58379a534000b11547936c000b3430680001580413869e3800006100023dc6349960000000e4a0a80fb9e28cc6ab20651d2c85029615f15204ee10d205800118cab72ab0ec85d47c943282413f41d41cb2ab4ad485808c800015495646da6185e87e83d70138dcc4924cc845948220a5748ea0c108950eb14196306761078f602a6a6157d0be48623531f9ab9c6540000d42970396000000175d3360003b22494a602f1075ad18000b02261a9dd310000000206400048d25721080000003749330000a4b59aa54c7042624de979032669d0f729440009ab00000000008744099dc95d03e041f90e4390ad70030d2d2fa1e83b098383026bd00000000004a50000cb52684e224a2d5c000142000000159600000018e80007c400004180000002cb000074c7672df8b2024e00022d9e85494b27401a7ccc1896903a93941805f90baa1fc5280084d70b38a72045142a6745882e600016d85227500e5000000000000000004748d85091f2940e7930000de0ed600000000002beb04000000000028e3fe022000062600018f809e9240000000bba12b30b80000000000000da000061e20c9d681c60005281324aba49900002d8ebaa6418f0000f4c21f3e29a9
  | 20 => 0x811d80003941f451ac1fc19d80000009d31c6000105825d00000006c400a0c1162c0004770e1a408b8435a26b86a80000003010000000a290000e00f8c000000110c19e00049697940007d05600000c84b0545fa8d004400000004443825ca1900db000000035d287d05c2b10b800805b22444e79ca80004cb3611c307fc0005929ffc69e00003c0000000760000242c000a9353780000000003bc00011c4a1318904f8412601145108cbee36758b000093e0000d000000007c72520c2c0009df270814800008b4a218b474a683011800082c9c052b00005a28875501848dd42f602b093ce888293c90ee0d3e8a74d02824e04a8335124ac0000004f5acf0f18000000000000000005a8bb40000000002cc82c07421002a8951a2120002b194223631c821512ca9b4207272055a0002be800115c535000154c9b43f508802540007f32ef8000e9033600009bc60c00043487c000000000000010d4000035000000019619308840005863cf1314ce000026a8000e7600025588788f00002e81c0000000052c8a5cc729ea00000015dcaa1437073c3beb2b346800000092700000014e688b36080010a40122ccaa640003f1130000139c17f1df00400000000000e68e4464500001cc3f425b44e913861000032d95fcc066dd47599a8384000265100c00057a4b417c537c621000026c6d496f0001ac4f682ab44c953805c84959b968c44a6a521d8000f78650126156159aa3b16d1a512c244124d89087e000000012b03a60001582a9c842aeb00011f49e20000000000e1e33f0ac800000044b2f3800074605f0000000c34af84c4a39c0001b50000bf51380004590278cc00b250a800018a3570f518b931c0000f9960532402f00015909505db4e08fb40006b51a2aa8c0000000000000ad63434a29b5c000000000047136a000389000167a70e28a000000097a000000068c000000000000000037c800038e6af3052bcc88e000081800103400000001c80006220002a140002ee0001b4cdbc8173c30001646513399164c000872000000000000000000005ba00023a04b8000a7b0df80000008392441a444765101fc80001bc76c27ba9004300004fc2bd000081d0001a04b780003682cb42da99a3bc881c0006b600006dd0a05425341dc010c9723c805508260552b7a4e16586643f1a244f102f54381d5d00c00008e858923200008aa1840001fd12f1044c686b80000ef029e8321f11f943c001f32387e000000000014540001350000000bde1d54dda5440000004a3a1e921a000000000000000043210f40000000b30000000af52731bf4000000000203c32893c1d9a8f40003a7595293cbc42884718a70c5e5940f19af915e82725392d03305091e324f838c8750a8874411c1b155f29387140ae08d084ce5691204a17796ac95b42b825d1261b
  | 21 => 0xdb1a420341a600045ba6a46840004be023c6743d515b80fceea82832780013c4afd2850000fd83af01e8000c201682780008d3c0003dc80009122e0190a0e86f87114889e704cc794385801c3e215559409a87060001e123c00000000ab80000000000e680000003d60000000ad25a618b19ac7d205c02d000000029803b000000000009a28313ee0fd0f08000000000000011d39684d0002b0400073d4368000a5a0004d808cc38828f0b909500000000001aec0008ad34425fcdf825c01919d020880503d1cc12b07591d80d3814e32f19aa878e627c13558868b703aa0ac15503489673230c28dd65d503e8e106788ca23686bc96664a45081ec2c6ab431aa9f4a4e1f247ca1f55c2370369014486438830482bc8d044a42f94f8f0a28358e22f4a220982b11b1d69c1d738d944958669c0671e051aa9d52ff80e874297348500cc4e617e06c87d16889ee29a0d000f22e148f00601b6064499859c0c42c201c843895234948b8f7c02855a19390b424c0003e9a1ec0006163ae0b9c00000042f0a1c75867f39e03200006561678e04000a8e1f38000000b510e7042854000051200009c654b3eb08f54428c3191ab6495a43c0001b909846c91a809c4ae24c7014000056ca3e0000a048b897427e86153ce2790000000c3a147442a1b000000039600001aeb3112700013fe0000001948000ab5000010c0002032b60000eac3fd3150ddc00059e03307300002a258a8b6c8844aa4a782e03ea074091a10429271e2ab913cb8a05420308c909e9a832890c04288785860e654600e82318d581223c049125d4dec15c19622789003b73022c1884a2d70ed097c0004bd0cd9ae4f3ead6315a4052d493d0fc8c5c24800023d06aca7e0000002218cca00019c2bbcf0e8e004388f000000005f862c0908bc5021d508481a3065903463ea3149413d0ae40e50d701181b0aa930daae05a40003ec00000000a52769144b5e7954c3a2583bca490002b102803d74520000000000000000000000046117b955c7bb3e79d145c45ae00001340004de25f88fc7c6000000125c000000000140cdea00000000005200000002a3000000013a0000d7811200000000000003dbaa00b0e52c36501c060a8365132230c928ac2d58ec4392ad345289e90ee9405521e68f1e75520916dd1fca5534384ec32a1b03cb14bd36ca3634ba4a478a01906a00004c677100015e45b0a6a2872524bc20173e5960c06e66f42b08a4202a3924286112285001ac223c8189a23b4248c28c0003a6000115483c17f9db8ff01e544214c91027af408964401298d12390cc4a201123e2a54de06cd2770c1c0006330188000a346b34c08a780008ea22c8d981b414840522c022e7a022a8c940004a200028b951624813685ad68494c083a47cd8c0000522280fe016c00000015ba54950708
  | 22 => 0xa52000368aad845eb011608cf400011b18695a0fba8943bd11500001b80768d1d6607b82aa800077490359780101ea09f1baa27d1e87ed5691e6c89a6c00001f980000004260000000000000031c00010002f137c4f89f400000000000003ed000000000000000000004260001f0885e00000000001e20003efa4fce12000383800000070a31f8cc8a7020c42019dc0000001cb8000d184562cf800099a9bf002921ca180001cc1e0952800052f88ad3ec46a0f5a098fc8b360c40f9523667549708b95586e751514084084600969930a9a7214eead2530a51720aad0ca9818600009f443600044c03991a81504d385dd6802af180a3b93bc32b2b685a94c40004d600e14bc573000299886e9d6561024cbb04b7000000000054610a99640005a90e81d047222530000694cba00000011100006e85261984c960002040a6800000054b0c880005b5000000118800059d9a6c000a5d4f4a0a8b7a7ab31180004a44b63368000b4006e0000000000000000000095e12c53e000146a0000000000b800001b21f340a05eb451015c0007c029da2f8ff660b48224d83d82a63788c0c000804000264066881800000013d000000002f8ecc9152d282c0a4a3142c208c4a0899500028400000000000ed0000afc0a180015b6a6e13488582260e200009646045360000000a0a528000000000000045d9e6000000000000007d484b1899f81366000396a4e442e0003be00004864b501f0a2d4d69351dd80011fe4b03a691ad20e227291800093893b517800130000e45580013c200000000000008430000ca000000000002680001290160000b123ee0bc09915500002ca9bec00000017c00012a055145a000000077b12b15812b812a198016c3b00000000764ddc6bf09d11196329cc5890eb8000392000000000000000029e07d0ae352d9e0c0000d123f000000097b00013609ea00057610d4a3eb4100005d00009a31bf987c00071c298a30029880e0b89a8d5ca61337620950b20820e2a2e0b920ff4eca1a05c642b543293557e42c09b8fd85b807c13c109cdc275f0000f40546000512a6980008e8140000116c00034c82704ea4d917805a418c4fb50111e53140f73620030a7896d2a5169c5be1453149690fd29082591a1472a4dc55da65d05667d341124c7169d02f408648d8ad42ac99e11da45f0978000800063433a08400063b39028607c200013da34067282d36a0d54b687582bb15f92ae791114202cdfe8f2389995c790b53029a91c1fc20646faa745a011e3591ed95cc3dd000000000035c046200109019d38427348704364e38c012be4054cf1f9c5aa00000020f949000000012e804e00058187480d60dd2481cdc15a0c10000d6c712b0a41da67d0f21830ad8940a6629258689b0fd410822400005fc29b1fa1a2415620114aa0d13f26
  | 23 => 0x521124800140690049500012744702ae107c1761e744ba91559c3ef050aaf441600033382351de26505300000009302d08000d527ce0c81cd47942222451da96404e02e9000083a5f8534800000000000025680000000362a98f740004c227f55a2b1e516828d5b88350248e88fea00040d9e7478880c02628040005e902510f800000017d220c2040001f21bd16707b155c8000d9c27f03f8fc8dca00001d800050c5bb3542b9102453a00012f0000a54000092d65c0003a518553169200ee966c5086374d916b49a837307c1f5c1869c62d8228c00067b00000000002b40000000000000334000000026b0bea5c50208d34d51c594a64eb3f08001088000000000010a0004aa81614587013471d88b580833c580014e24f636a91484aa3fc57b95790a217a0001d94c320002051c7400001a000120c3b663c2d111250e2b2127f00001746cc00005bc65c0000000000cd800000023300000004a70af000089200003853f8000506ad2d6986270000000aa4a201a0a31400021d0de80001e00000db2b40f087764f8a498ba23312c103801146c53b4880869aa460a7190161054143025e40ee15e59128a00001b201b06291bc5e3543943cdf04dd46e96707727f400001808c89ec10e14a93de31b3ea90043226ad25313a00006d8388122c04a0000001e5cbac59a3af0ca461800022d0000852b4f25da82c9420003218b94548af92e1856905e00000024c51e200000d80008d20000620001028000084a058f9066200015148a67140001040000000000000000063239797c017a48100000000000003de85840000003a026e00000003d6800000002638c05d85320002c52c695bc43f31284500000000f1243cf467a23ee0000ae83541561ac000055b32c207c97c50700002480001e90dc983ce2e4f22fa1ccd3742b3000000143407158480000007b50000b58344000000108087417c000000000044c2958d7c00040f00000000005da07a0f1cd4e0003d297cd510a7623da51810225858d8000f860000000f64000000000000109400006483bc2f245d4f6a888000000496148800094b0000c6144e6480000000e9e00000000014ea8b100013a80000000002a7d674000000000000092102204f5556a7a0000a4c37800000022a000000013385b83da13100015f00000004c7800000049646c95e11c849e1bb16e8084a722c6000030e0002e4105cba80004730e7c56a003422890567e0002cb997c9307d93778000db42241aca174000970009800115200041800712d619c000158d21256106a800053a00047a85294887be33f22000006e000027608c200016980013b40002f6800066615229b8000e746fe1c380012ba0001722578c000001b880000006f700026600004824f800000000bc4990054d0c6b713b19c88bc17b1461268ca80002640
  | 24 => 0x9c17a921c5a85648d7538a000020264c3de5b31b686b02ca85a3658000000b4558e90681d47f60000f480002c034906380000000000000b1ea174b120e079e00008fa6dd2fc0003b9a2d53c069338300000003a92721a580480002ba9eb12384f85448bcd5fe7520079ab87b805d33e23256a800000000000000000000000000aed00012c441009600000000000003e900012860001e09310c627e2552aa08c7033e50e8d288365c720216748e65cf0cca580d687eb1cf0d4531830e0b20c71328b470cb807519aa16563aa4888a77e0ff14f45743bf1e184fc5f69821fd162086807e5640dec7d818050a0814e2a73f3209d2466e0002e59939520457285a9b4c221e41449d6c0002ef058843c1f83521bd0b342baa234d686b4460b134271d3810851d00012443cc5fa1638c2491823e0901600c0a9fe40e00010b60a9000000001618f00000001a400003280793e491a58813bd2a4000515a08c76a000350ac1c0000001ef26e400000028427ed06600000003312900003bb9e353a89d22a7a0252a80894671e9161e5e000029f81e40000928000b62ab030a17f91f00003b191884704a342a9cd075a3cb0001a6162e8e900008d055c0000d300008a01894451f780000004122a787fe1050159d183765b9000173457e39b4b200005768b3116000031800046b8678b647a700025b000000000000000000003a38f984fc7803f8a710fa82390d9837c48a8e503400000004862d51f30c0c
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xaa78454d610800154908a9ac21000239a1c535842000472c38a6b084000aa68414d610800154b0829ac210006b8a00535842000570c00a6b084000a678550d61080014c90aa1ac21000239a1c435842000472c3886b084000a668510d61080014cb0a21ac210006b8a00435842000570c0086b084001cca7058f5108001992c6b86a2100033858570d4420006473a2c72884000c8d7458e510800194ce8b0ca210003295d1619442000e65382c7a084000cc9635c341080019c2c2b868210003139d5639042000626baac72084000c667558641080018caeab0c82100033258f704c42000670b0ee09884000c4e7558c310800189aeab186210003239d1630c42000646ba2c61884001cca7058c31080018cceab086210003195d5610c420006533a2c21884000ca57458431080039c4e0b0862100033258d700c42000670b0ae01884000cc5639c7500800198ac6b8ea01000239e1d61d402000472c3ac3a804000cc5639c7400800198ac6b8e801000239e1d61d002000472c3ac3a0040018cd835db300800198ac7b8a60100033158c714c0200047343ac298040008e48758530080013c3023826588002a9613654871000532c2ec890e20019e0805cd21c40011cd0f31a438800299614634871000552c20c690e20018cc8758d328400194ae9b14a308003195d7629061000472c3ec418c2000c6575d88318400194ae9b10630800338d89700c610005e1c0a6498420008e7815cf62440031c90cb8c648800678201718c91000cf0402e518a20009c9831c121440013a3063824288002a961365485100047243aca90a2000a6585d9121440011c90eb22428800239a1b734851000c72432e690a20019e0805cd21440011cd0f31a428800299614634851000552c20c690a2000bc1831c121440013c50c382428800738a18704851000eb1428e090a2001d61851c121440019c6ca382428800338594704851000ed1420e090a2001da1841c121440019c6c8382428800338590704851000ee1418e090a20009e1831c12144003b830638242880027060c704851000671318e090a2000ce0631c121440033c10e90c60880027821d214c110006703b2429822000bc18348530440031cb033b4408800770041730811000d64402e4b182000a55851c5630400152b0838ac60800239605768c8100063332ae31902000c65655c6320400194cc8b8c640800329591718c8100066331ae31902000cc5635c632040031d100bb26408007321c1634c81000472c36e29902000cc563dc5320400192ae8b1ca208003295d162944100062abaac72082000c657558a41040018aaeab186208003255d1630c41000632baac41882000ca57458831040019a2c6b80620800338589700c41000f60102c68802001ae08058910040015c30d90a2008003b058f2144010
  | 1 => 0xb03396c99800271607764cb3000ce4402e690e60009c9831c121cc001b8662382439800239604725963000472c08e4b2460008e4865c6324c0013c3023826498002d2614704c930005c4c20e09926000bc1811c1324c00158b06396c2980030d5d5741853000632baae430a6000ca5745c8614c0011cb0f190c298002b8201321853000670b92e030a60018cc865cd214c0014cb0a30a4298002a96106148530006623b66290a6000d89744ca504c001a92ea994809800319995718c83000632b2ae31906000ca6645c6320c00194ac8b8c6418006b8201725843000472c3c64b086001c6870595210c003950e0b224218007381c1614843000e70382c290c400092f875505488001a1aa8b98a91000239e057694e2000473c0aed21c4000a65811c96508003c5440b2ac810002a9604725902000562c0ce53184001e4a205956308003d1440b22c610002b1a067258c2000562c0ce4b184001cca7058c52080011cb0d388a4100033158e711482000662b1ae22904001cca7058c42080011cb0d38884100033158e711082000662b1ae221040008e5869c6320800198ac738c641000319995718c82000632b2ae31904000ca6645c6320800194ac8b8c64100033158d718c82000472c3c653084001ec22058d61080035c500192c210007329c1630842000497c3aa82a04000c2d76550540800119b0d398a81000343551731502000472c34e22a04000a8f845d5630800151908baac610002a3a107558c2000546c20eab184000ac6811d5630800158b023aac610006b2a007558c2000527c2ae8b184000a4c855d1630800149d0a3a2c610002936147458c2000563408e8b184000ac5811d16308003595003a2c61000383d525458c2000467438a8b1840008cd871516308001c1aa82a2c610002b1a045458c2000562c08a8b184001aca801516308001593002a2c610006b22017158c2000527428e2b184000a4d851c5630800151d0838ac610002a36107158c2000d65400e2b1840008ad861d1530800191ee8b1aa610003231d16354c20006473a2c62984000c8d7458c5308003994e0b18a6100023961a7114c2000662b1ce22984000cc5635c45308001992c6b80a6100021b6187550c2000627baac6a184000c4c7558d430800189ceab188610003135d56310c2000e65382c621840008e5869c4430800198ac738886100033158d7110c2000664b1ae02184000aa684dd5610800154b09baac210006b8a0275584200053342ee8b084000a6585dd161080035c5013a2c21000389d52545842000473438a8b0840008e5871516108001c4aa82a2c210002b1a0c545842000562c18a8b084001ae28015161080015c3002a2c210006b8201735842000533428e6b084000a65851cd610800154d0839ac210002a9610735842000d71400e6b084000
  | 2 => 0x3639452100652ba2c728a4200ae08058e514840164d09baaa29080349dd2545452100533430a8a8a4200b458315151484016c3002a2a290802696107354521004f0c00e6a8a4200ae08058d514840164908a9aa29080259e1d511452100472c3ec720a4200c6575d8e41484018caeab1c8290802b820163905210059342ee8a0a42009a687d514148401a4eebaa28290802a9a18545052100692ba8a8a0a4200b85831514148401743002a28290802596147350521004f0c00e6a0a4200ae08058d41484016490aa1a829080259616711052100473436eb98a42009a7845d731484011cd0dba6629080259e1574cc52100570402c798a42009a584dd431484013c301ba862908025961e750c521006333b2ea18a420096585dd031484013c301ba062908026961e740c52100692bace818a4200ca6765d03148401a4ceaba06290803495d5740c52100632baec618a4200ca574d8c31484011cf0eb186290803195d5630c52100652ba2c618a4200ae08058c3148401ac2eb3806290803685d2700c521006713b2e018a4200d62755c03148401ac2eab806290803689d1700c521006d0ba2e018a4200dc2735c031484019c10cb80629080338d8d700c52100670b1ae018a4200cc7815cc604840198902b98c09080732201731812100e65282e63024201cca405cc604840398e20b98c09080732841731812100e62882e63024200aa584944604840198ae7288c090802b8602511812100662b9aa23024200a6585904604840198ae7208c090802b8602411812100662b9a8230242008e587cc4604840198ae7988c09080299614311812100552c20623024200cc5730c460484015c300188c09080307591731535000472c0ce531ea0008e581dcd62d40011cb03bb465a800239e19718cb5000652ba2e530ea0008e5878ca61d40014ab062a2c3a80028d211535875000472c3c64b0ea000aa58498521d40018ceeca8a43a8002396067298e5000653322e3194a000ca5645c63294003950e0b224328007381c1614865000473c0ae7b12a0008e5811da32540011cb023b264a8003191d95148550004e4c18e090aa000d61511c121540011cb03394c62800307595731534000472c0ce531e80008e581dcd62d00011cb03bb465a000239e19718cb4000632baae530e80008e5878ca61d000152b062a2c3a00028d215435874000472c3c64b0e8000a658598521d000194eeca0a43a0002396067298e400063332ae31948000c65655c632900038d0e0b2a4320007381c1614864000472c08e4b2a800083f87594545000183acab98a8a000239e0573d894000472c08ed19280008e5811d93250001948eca0a42a00027260c7048540006d0a08e090a8000b19831515050001653042a2a0a0002cc604545414000472c0ce531880008e5819cb65cc0011c
  | 3 => 0x9300a800e195458e601500119b06392c02a0023960472580540051dc32a8b00a800e195458d6015001c52a8b12c02a0038c551615805400564c18e4b00a800ae1811c960150011cb02392c1a9803255cd71191530064cb9ae0322a600ca9725c06454c01962e2b80c8a98023960672d81530052ac18a8b08a600a348454d6114c011cb02392c0298029660c54580530051c422a6b00a600ae1811c96014c0107d0e32aa9a180239604725834300472c0ce5b2c860083d87d945490c0183ecab98a92180247a1f5454e430060eba2e632a8600c55735c46550c018b2e6b80caa18031a5c9701954300638b8ae032a8600a1e869525350c01838ecaa2a6a18023960672d81430060eb2ae62a0860083c875954310c0152b062a2c2218028d215435844300472c08e4b008600a99831516010c014710aa1ac021802b8604725804300472c34e229464008e5869c4428c8011cb033b0a9190024be1d541523200686aa2e62a464008e5869c4548c80154d09b2ac319002a961365586320053342ec8b0c6400a6585d91618c80154d09baac319002a9613755863200571404eab0c6400ae1809d5618c8014cd0bba2c31900299617745863200571404e8b0c6400ae1809d1618c801c4ea92a2c31900239a1c545863200472c38a8b0c6400e2554151618c80158d062a2c319002b160c545863200571400a8b0c6400ae180151618c8015c700b9ac319002b8201735863200553c22a6b0c6400aa48454d618c80154d0829ac319002a9610535863200571400a6b0c6400ae18014d618c8014cf0aa1ac3190029921543586320053342886b0c6400a658510d618c8015c50021ac319002b8600435863200533428e0b0c6400a65851c1618c80154d08382c319002a9610705863200562c18e0b0c6400ce1701c1618c8011cb0f308c119003199d5611823200632baac23046400ca674584608c80194ae8b08c1190024be1d541513200686aa2e62a264008e5819da534c8011cb033b48699002b8201611853200e63982e23026401ce2305c4604c80398a60b88c09900307591731535100653322e3194a200ca5645c6329440183acab98a9a080319995718ca4100632b2ae3194820083f87594545040183acab98a8a0802c560c545454100598c00a8a8a8200ca57458a518c4018caeab14831880319995718c83100632b2ae31906200ca6645c6320c40194ac8b8c641880319595728c43100652b22e51886200ae1818ca600c4015c303192c018802b860a315803100497c3aa82a64200d0d545cc54c840125f0eaa0a89080343551731512100671b88e0b1a4201c6a851c163484038d30a382c6908072aa107058d2100e54c20e0b1a4201ce1811c1634840134b0938ea6908063a2017694d21004b2c2ce3a1a42018e8805da43484011cb0fb1ca290803295d
  | 4 => 0xde9892b28b5129ac022678812052a87081409d2185405100023a040000000003fc000002346ac000800009106510b1e2000000bd1660000011c29088800108000000680d6056308689310004bca922f2d08110b08a1bc000000000004900014f0001740009a1d6000050ac138000fc8834821f0002283f60005b9610f64a40223b1c2124000002f60008c8240e24f0cb04047e7d80000000000055157000671099d13a0000cfa3a2ee7f8000b11521b800078146130239da11e0001e09f000504f28000e416ce20dc18875cb280f2c0788291304808083a0002968f4f42362ec000e31b6000144380d719c7cce18220747840013f4561e49023241668003800000000001a82f24d4002030003807b1f22fe0342f0000000d50900037c65c000762a20009300025487c000001e6064ee000000004e580019e4b8000002841342b80024249c0700007a79c000c500000000000000018000dd2bc0000001f0006101d800000000e71cf0004145d80000009c8a8964606044ba331920011383237831c001a937240cb68000000e5009b02b4000000000fa691051af000000000890004f8280a136439ceb18700030c000001781d431a430008dc9409311c2644300010e000002060002907c9d5000000e48b03cc361108000004504616c3823f4a5000000438001ad000000002233fa000001372f86000008b0d006c8523e1a857c3b8af1026d10e8ea1be3c8958be3625a4f601837e8a507092052850000341a632cc78001c6524b100031000071000000000150f70008d48f8b600006008000000000a0001a02c0d0040601009000080400000404000050041f0000803c120000f0000102c0001c0100025008020c40200c02000020000202c000040305006064000000c0042d0000102812000090400001400098040000002c030440604001000010000a0000000c020040003005018000140400402028050281c0080003000018000140900c00000060040d0080200800018190100201c0000c01008040000200839000020200100c01000000000100005148030280300c00010020000101c1301801048010000f0040300800014000100801401030050000302c020181102c02000060281f05402024030180400472c0ce531ea8008e5811c960d50011cb03394c72a0023960472582540041ec3ccb2a0a800935811cd54150012730039aa82a0024d607705505400472c0ce5318a800a1f86552631500158b03394c62a0028720d5458c540050fc32a8b18a800a1c87551631500143f02aa2c62a00287e015458c5400706aa4e4b18a800ac5819c96315001c1aa8b92c62a0028be19549885400706aa2c7310a800a2f865516215001c1aa8b1ac42a0023960773588540051bc32a9308a800e155458e611500146f0caa2c22a0038555163584540051dc32a
  | 5 => 0x8092522c000530001b46ecb89b34585e05d1eb2fa7c0278163d2320838e938e0007f1ed40e7f00016748e7c410000000000469ca00000024033000000308000000007a17e0184c87710f3c05a8ea20f3ee3550e02f3b6244a30172b08b82223c1501641b91b2cc774a18c627a8e03f94736e6440a21e0b8078ca8130cc0b48220c0002d401800000000b198b1ea6690c80021a001001d32f47900119d3f42e4c181d27077c270000da734ae9102e8000c6841324844a016e0de7d4000e629c3346905f000000001b5000651080c13204e4231823147bc35955398000000002c866cdc00b3f0158000940000004c0ec00a0011892d2e06880022a0000000007a0003a000060448394002083fe26cf50fa10a0000010005c1b06d9122ea854fa0422984d0e2a3428a098c29440fc278440ab180114d28821640f89621b34c0c40e18c31c1283203f3323e0d19860b42b82a1ba274880a9a390865bc660f0434418b995c2ac85cd3922168280000ef0706a8538a510848c482461b20248c14d04a000000693a4000001e3000154001d93bc0012106244c860ec00000008ce400022e000001ae2223b4898b82666841b0ad3301ccb906541a0c02c15b00014c000000002fc00000058049049c01f60209d815034084338fc3dc0008f16b00012cc989548a0008486a1c84d8
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x60000d00280224a1cd9c0048b80320498046a0d0054000000055480001800e400108030080003a0120018247900a000113e00f26082ca000020016009c000000400101020000000002070004012159120d5458c54004866408355163150012159121d5458c540048664087551631500121591e015458c5400681551819c963150012279855054586320068155183151618c8018c1835c07058632006285d08058e514840186175201639052100449e617515141484019057560c5450521006185d48058c31484018a174201630c52100511654815cc6048401485942057318121006216117394460484018c1736025118121006116157390460484018c173602411812100611615730c46048401885845cc3118121006305cd800c460484019418354470485500066060d411c121500011c198cc4704873000483e6154151630800180d875505458c2000489e61541516108001a055460c545842000528653651c1214400146195d90704851000630259831c121440018c36560c704851000630595831c121440018c36460c704851000630591831c121440018c18398c704851000438660631c121440014619518c704851000528650631c121440031c09760d214c110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x1a04000050834a4b3063824288002881a4259831c12144001440d26cac18e090a2000a106976460c7048510
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 66
  | 6 => 1665
  | 5 => 2905
  | 4 => 584
  | 3 => 43
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
  | 7 => packedAt gbK7 (1892+((h/22+packedAt gbK7 (1716+(h % 22)*8) 8) % 166)*8) 8
  | 6 => packedAt gbK6 (68265+((h/555+packedAt gbK6 (61605+(h % 555)*12) 12) % 2198)*12) 12
  | 5 => packedAt gbK5 (151056+((h/968+packedAt gbK5 (139440+(h % 968)*12) 12) % 3835)*13) 13
  | 4 => packedAt gbK4 (36396+((h/194+packedAt gbK4 (34456+(h % 194)*10) 10) % 771)*11) 11
  | 3 => packedAt gbK3 (3108+((h/14+packedAt gbK3 (3010+(h % 14)*7) 7) % 74)*7) 7
  | 2 => packedAt gbK2 (327+((h/1+packedAt gbK2 (324+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x30e0fff870c383fff07e0fffffc0c09f09f27f
  | 1 => 0x3f00f0ff80fc03c3ff8ff0f80ff30913913d93
  | 2 => 0xc000ff0fff0003fc3ff000fff03c0e1ce1ce1c
  | 3 => 0xffff000ffffffc003fffff0000000fe0fe0fe0
  | 4 => 0xfffffffffc0000000003ff000fff000
  | 5 => 0xfffffff00000000000000000003fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x102421102040908440120c0a8500c085085025
  | 1 => 0x290858aa88a421629c85a0d02ab30912912492
  | 2 => 0x48129a8dd9204a6a3d2062e560bc0e18e18e18
  | 3 => 0x82420001120908002248420040000220220b40
  | 4 => 0xe6cf273b30400844183155000ddf000
  | 5 => 0x3c9cecc000000000080108860c2aaddf000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xffffffa8ffa8eea8ffffffa8ffa8eea8ffffffa8ffa8eea8ffffffa8ffa8eea8ffffffa8ffa8eea8ffffffa8ffa8eea8ffffffa8ffa8eea8ffffffa8ffa8eea8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_11884
namespace PEqualNP.Outside.L_meta_11884
open PEqualNP.Outside.L_meta_11884.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bgb_3_32 : Interval gbAtlas 3 32 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 43 := (concat bgb_3_0 bgb_3_32)
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
theorem bgb_4_576 : Interval gbAtlas 4 576 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 584 := (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 (concat bgb_4_224 bgb_4_256)))) (concat (concat (concat bgb_4_288 bgb_4_320) (concat bgb_4_352 (concat bgb_4_384 bgb_4_416))) (concat (concat bgb_4_448 bgb_4_480) (concat bgb_4_512 (concat bgb_4_544 bgb_4_576)))))
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
theorem bgb_5_2880 : Interval gbAtlas 5 2880 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2905 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 (concat bgb_5_448 bgb_5_480))) (concat (concat bgb_5_512 (concat bgb_5_544 bgb_5_576)) (concat bgb_5_608 (concat bgb_5_640 bgb_5_672))))) (concat (concat (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832))) (concat (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)))) (concat (concat (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)) (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216))) (concat (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312)) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)))))) (concat (concat (concat (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568))) (concat (concat bgb_5_1600 (concat bgb_5_1632 bgb_5_1664)) (concat bgb_5_1696 (concat bgb_5_1728 bgb_5_1760)))) (concat (concat (concat bgb_5_1792 (concat bgb_5_1824 bgb_5_1856)) (concat bgb_5_1888 (concat bgb_5_1920 bgb_5_1952))) (concat (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048)) (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144))))) (concat (concat (concat (concat bgb_5_2176 bgb_5_2208) (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304))) (concat (concat bgb_5_2336 (concat bgb_5_2368 bgb_5_2400)) (concat bgb_5_2432 (concat bgb_5_2464 bgb_5_2496)))) (concat (concat (concat bgb_5_2528 (concat bgb_5_2560 bgb_5_2592)) (concat bgb_5_2624 (concat bgb_5_2656 bgb_5_2688))) (concat (concat bgb_5_2720 (concat bgb_5_2752 bgb_5_2784)) (concat bgb_5_2816 (concat bgb_5_2848 bgb_5_2880)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 4 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 4 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 32, 48),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 8, 24)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) SB) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 4 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 5 zero,inputs.getD 0 zero,inputs.getD 6 zero,inputs.getD 3 zero]
def fullWord : Sig := 0xfffffffefffffefeffffffa8ffa8eea8fffffffefffffefeffffffa8ffa8eea8fffffffefffffefeffffffa8ffa8eea8fffffffefffffefeffffffa8ffa8eea8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) SB :=
    slice_correct (ms:=fixRows 5 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
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
  have lift := lift_ok (u:=true) (ms:=fixRows 64 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 7 → Bool) := decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_11884.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.or,[7,4]⟩,⟨.or,[5,6]⟩,⟨.and,[8,9]⟩,⟨.or,[1,2]⟩,⟨.or,[4,5]⟩,⟨.and,[11,12]⟩,⟨.or,[0,6]⟩,⟨.and,[14,3]⟩,⟨.or,[10,13]⟩,⟨.or,[16,15]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,17⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_11884

open PEqualNP.Outside.L_meta_11884 in
theorem PEqualNP.Outside.L_meta_11884 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
