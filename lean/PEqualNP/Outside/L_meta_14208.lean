import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_14208.Model
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


end PEqualNP.Outside.L_meta_14208.Model

namespace PEqualNP.Outside.L_meta_14208
open PEqualNP.Outside.L_meta_14208.Model
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

end PEqualNP.Outside.L_meta_14208

namespace PEqualNP.Outside.L_meta_14208
open PEqualNP.Outside.L_meta_14208.Model
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
  | 2 => 0xffffffffffffffffffffffeffe3fff81fff0ff
  | 4 => 0x73ffc3cffe0f8f1c
  | 5 => 0x7cfffc0ffff00fe0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffa51c664c1c636c91
  | 2 => 0x1020800080840026
  | 4 => 0xc44281524092518
  | 5 => 0x38802aa49204ac0
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 54 s0Pos s0Neg, 0xfffff0f0f0f0c0c0fffff0f0f0f0c0c0fffff0f0f0f0c0c0fffff0f0f0f0c0c0fffff0f0f0f0c0c0fffff0f0f0f0c0c0fffff0f0f0f0c0c0fffff0f0f0f0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_14208
namespace PEqualNP.Outside.L_meta_14208
open PEqualNP.Outside.L_meta_14208.Model
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
  | 0 => 0x38f1fe3c7f8ffe3c63838fc38fc3ffe61c39f
  | 2 => 0xfc0fe1fff87ff8fc07c03f1fff1ff81e067cf3
  | 3 => 0xffe03ff80ff1ff8003fe03fe03fe1878f1c
  | 4 => 0xfff00003ffff001fffffc0003fffc001f80fe0
  | 5 => 0xfffffffc0000001fffffffffc0000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x5011888452415001460a902510250a9860c185
  | 2 => 0x8220440811001040040090889089044021432
  | 3 => 0xab4455492532a03e88052a42aa42a545870e18
  | 4 => 0x3100589210203248d291800034930188a80bc0
  | 5 => 0xc20881002644c493252634930000061155e000
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xfffffaf0faf0aaa0fffffaf0faf0aaa0fffffaf0faf0aaa0fffffaf0faf0aaa0fffffaf0faf0aaa0fffffaf0faf0aaa0fffffaf0faf0aaa0fffffaf0faf0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_14208
namespace PEqualNP.Outside.L_meta_14208
open PEqualNP.Outside.L_meta_14208.Model
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
  | 0 => 0xffffffffffff83c1e0e03fffffffffe067fff
  | 1 => 0xf83ff07ff83ffc01ff003c3fc3fe07f984e73
  | 3 => 0xffc1ff83ffc1fffe00003fc3fc3ff81e0739c
  | 4 => 0xf0001fffc0001ffffffffc003ffc0001ff83e0
  | 5 => 0xffffe00000001fffffffffffc0000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x10908142090000140a02488448442a280614a5
  | 1 => 0xa549523492569ac295509162962b4155984a52
  | 3 => 0xc62a5491a452bd6aa141226a26a39505e06318
  | 4 => 0x843188210718c98cc66438003b310618aa83e0
  | 5 => 0x84210c6386316331989c3b300021861557c00
  | _ => 0
def s2Atlas : Atlas := ⟨3,rawDecor 59 s2Pos s2Neg, 0xffffaa88aa88aa88ffffaa88aa88aa88ffffaa88aa88aa88ffffaa88aa88aa88ffffaa88aa88aa88ffffaa88aa88aa88ffffaa88aa88aa88ffffaa88aa88aa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_14208
namespace PEqualNP.Outside.L_meta_14208
open PEqualNP.Outside.L_meta_14208.Model
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
  | 0 => 0x78e3c71fc71fe3f31e3831c7c71f8ff3134cf
  | 1 => 0x7f03f81ff81ffc7c1fc03e07f81ff1fc238f3
  | 2 => 0xf8003ffe3ffe3ff8fe0003ff8ffe3fe003cf3c
  | 4 => 0xffffc0003fffc000fffffc000fffc000fc0fc0
  | 5 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x50e046228542944030a0a905141448ca311445
  | 1 => 0xa10c89450a252808c144522228889614c22892
  | 2 => 0x11000100000010200004801202000004128
  | 4 => 0x32240129a1200c92546918000e4d0246540ec0
  | 5 => 0xc44822400249b124a992639340000498abb000
  | _ => 0
def s3Atlas : Atlas := ⟨3,rawDecor 55 s3Pos s3Neg, 0xfffff8f8f8f8e8e8fffff8f8f8f8e8e8fffff8f8f8f8e8e8fffff8f8f8f8e8e8fffff8f8f8f8e8e8fffff8f8f8f8e8e8fffff8f8f8f8e8e8fffff8f8f8f8e8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_14208
namespace PEqualNP.Outside.L_meta_14208
open PEqualNP.Outside.L_meta_14208.Model
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
  | 0 => 0xf83c3fc7fffe1fe1c3ff0e0fc3fff87f1d33cf
  | 1 => 0xffc03ff87c3fe3fe03c3f00ffc783f8f923d33
  | 2 => 0xffffc7ff803ffc3ffc03fff0ff803ff0e3ce3c
  | 3 => 0x7ffffc0003ffffc0000ffffc000fc0fc0
  | 5 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xa0040421010200080850241008a0844051045
  | 1 => 0x909294912265062a2162908a6450950a922512
  | 2 => 0x21080100088800444400242089012220204a28
  | 3 => 0x85ab36254a0d4ab76a688128f2658322f80f80
  | 5 => 0xc632243673319339b3b3c9cc2046044cdfb000
  | _ => 0
def s4Atlas : Atlas := ⟨3,rawDecor 47 s4Pos s4Neg, 0xfaf8faf8eae8eae8faf8faf8eae8eae8faf8faf8eae8eae8faf8faf8eae8eae8faf8faf8eae8eae8faf8faf8eae8eae8faf8faf8eae8eae8faf8faf8eae8eae8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_14208
namespace PEqualNP.Outside.L_meta_14208
open PEqualNP.Outside.L_meta_14208.Model
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
  | 0 => 0xf83c3fc7fffe1fe1c3ff0e0fc3fff87f1d33cf
  | 1 => 0xffc03ff87c3fe3fe03c3f00ffc783f8f923d33
  | 2 => 0xffffc7ff803ffc3ffc03fff0ff803ff0e3ce3c
  | 3 => 0x7ffffc0003ffffc0000ffffc000fc0fc0
  | 4 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xa0040421010200080850241008a0844051045
  | 1 => 0x909294912265062a2162908a6450950a922512
  | 2 => 0x21080100088800444400242089012220204a28
  | 3 => 0x85ab36254a0d4ab76a688128f2658322f80f80
  | 4 => 0xc632243673319339b3b3c9cc2046044cdfb000
  | _ => 0
def s5Atlas : Atlas := ⟨3,rawDecor 31 s5Pos s5Neg, 0xfaf8eae8faf8eae8faf8eae8faf8eae8faf8eae8faf8eae8faf8eae8faf8eae8faf8eae8faf8eae8faf8eae8faf8eae8faf8eae8faf8eae8faf8eae8faf8eae8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_14208
namespace PEqualNP.Outside.L_meta_14208
open PEqualNP.Outside.L_meta_14208.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x1e1400041b8700000c880499001b0a189f80181a80878d050b1f1583000014800c12801300150e839d000000138a9181800d8586979a0e1c80001c00061700000000089e8000209080000b80029982000000101200110f00201609001d810f8016800000000009800781020c1000208001100c300000c0020004200007fd5001fe54007f55001fc54007fd4c01fe53007f54c01fc53007fd0c01fe43007f50c01fc43007fd4801fe52007f54801fc52007fd0801fe42007f50801fc42007fcc801df32007f8c801fd3200774c801fc32007fd4401fe51007f54401fc51007fd0401fe41007f50401fc41007fcc401df31007f8c401fd3100774c401fc31007fc8401fe21007f48401fc21007fd4001fe50007f54001fc50007fd0001fe40007f50001fc40007fcc001fe3000778c001fd30007f0c001dc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x1a4000f718d20005b8c690003df3248001f71924000f74c920007da6490003cd32480017fb0a4000fdd8520005eec290002fc6148001fa30a4000bd18520007be6290003dd3148001f790a4000fb48520007f4a090003f95048001fd2024000fe50120007bc6090003dc3048001fd9024000fb88120005feca10002fe6508001bf32840009f99420005faca100037d65080013eb284000bf19420005fec810002fe6408001df3204000af99020005fac810003bd64080015eb204000bf19020005fec610002fe6308001ef3184000b798c20005fac610003dd63080016eb184000bf18c20005fcc410003df3208001ee9904000bf98420007ecc210002f661080017eb084000fd58420005eac210003df3108001ee9884000bf9802000fbc6010007dc3008001f79004000fe88020007da4010003f920080017fb2e2000bf99710005facb88002fc65c40017fb262000bf99310005fac988002fc64c40017fb1e2000bf98f10007bcc788002de63c40017eb1e2000f758f10005bac788002fc63c40017fb162000bf98b10005fac588002fc62c4001ef9962000f74cb10007be6388003f631c4001ee98e2000fd4c710007aa6388003f621c4001fa90e2000f78c310007b86188002ff65840017f32c2000bf59610005f8cb08002ff64840017f3242000bf59210005f8c908002ff6384003efb1c2000b7d8e10005fcc708002fd63840017e31c2001f718e10005b8c708002ff62840017f3142000bf58a10005f8c508003df3284001ee9942000bf58610007eca308003f55184001fb20c2000fd50610007be6308003dd3184001fb90c2000fd08610005fcc108007de3084003ee1842000fe88210007f24108003f71084001fd8842000bfd9510005fcca88002fd65440017e32a2000bfd9110005fcc888002fd64440017e3222000bfd8d10007bec688002df63440017f31a2000bf58d10005f8c688003dc63440016e31a2000bfd8910005fcc488002fd62440017e3122000f7cc910007ba6488003df3144001fb18a2000f74c510007ea6288003d53144001fb10a2000fd48510007bc6088003dc3044001fd1022000fe48110007f62088003f610440017fb282000bf99410006fcca080027e65040017eb282000df59410004faca08002fc65040017fb202000bf990100077cc808002be64040017eb202000ef590100057ac808002fc64040017fb182000bf98c10007bcc608002de63040017eb182000f758c10005bac608002fc63040017fb102000bf98810007dcc408002ee62040017eb102000fb58810005dac408002fc6204001ef9902000f74c810005fcc208003f65104001faa882000fd90410007ea8208003df3104001ee9882000fdc8410007e84208002fe6004003ef1802001f70c010007ee2008003fa1004001fa8802000fe44010
  | 1 => 0x3de418c001eea0c6000f710630007be4318003de218c001ee90c6000f708630005bcc118003df508c003ef2846000f75423000fb8a118003df408c003ef2046000f75023000fb88118002ff654c0017f32a6000bf59530005f8ca98002ff644c0017f3226000bf59130005f8c898002ff624c0017e3126000f7cc930007ba6498002ff614c0017e30a6000f7cc530007ba6298003fb304c001ef1826000bfd9430005fcca180037e650c0013f3286000bf59430006faca180027d650c0017e3286000bfd9030005fcc818003be640c0015f3206000bf590300077ac818002bd640c0017e3206000bf98c30007bea618003de530c001eea986000f714c30007be8618003de430c001eea186000f710c30005fcc418003ee620c001773106000bf58830007dac418002ed620c001ef9906000f78c830007ba6418003dc320c0017f3086000fd98430005ecc218002fd610c001fab086000bd58430007be6218003de310c001ee9886000f70c430005fcc018003df300c001fd1806000f74c030007f26018007df650c001ef3286000d799430007baca180035d650c003ee3286001f7d9030007bcc8180039e640c001eeb206000e75903000fb8c818003df540c001ef2a06000f755030007b8a818007df620c001ef3106000f398830007bac418002dd620c001e6b106000b35883000fb8c418003df520c001ef2906000f754830007b8a418003df420c001ef2106000f750830007b88418007df610c001ef3086000f598430007bac218002dd610c001eab086000b55843000fb8c218003df510c001ef2886000f754430007b8a218003df410c001ef2086000f750430007b88218003df210c001ef1086000f748430007b84218007de600c0016f3006000f698030007bea018007de500c001eea806001f714030007be8018007de400c001eea006001f710030005fecb90002fe65c80017eb2e4000bf19720005fec990002fe64c80017eb264000bf19320005fec790002fe63c8001ef31e4000b798f20005fac790003dd63c80016eb1e4000bf18f20007be6590003ee32c8001ee9964000fb4cb200079a6590002fe61c80017eb0e4000f7cc720007ba6390003ef21c8001f690e4000f78c320007b86190002ff65880017f32c4000bf59620005f8cb10002ff64880017f3244000bf59220005f8c910002ff6388003efb1c4000b7d8e20005fcc710002fd63880017e31c4001f718e20005b8c710002fd6288001ef9944000f74ca20005fcc310002fd6188001ef98c4000f74c620005fcc110003fa5088001fca844000fe90220007f28110007de3088003ee1844000fbc8220007f64110002ff65480017f32a4000bf59520005f8ca90002ff64480017f3224000bf59120005f8c890002ff6348001efb1a4000b7d8d20005fcc690002fd63480017e3
  | 2 => 0x50006fea6a80037d53540017fb12a000bf18950006fea4a80037d5254001ef992a000f74c950005fec2a8002fc6154001bfa8aa000df54550007be62a8003dd3154001fda82a000df94150005fcca28002fe64140017eb20a000bf98c50005fac628002fe62140017eb10a000f7cc850007ba6428002fe61140017eb08a000f7cc450007ba6228002fe6014001bfa80a000fe94050006faa028003f950140017fb2e8000bf99740005facba0002fc65d0001dfaa68000ef15340005fcc7a0003de63d00016f31e8000bf58f40007bac7a0002dd63d0001dfa1e8000ef50f40005fcc5a0002fd62d0001dfa168000ef50b40007be65a0003dd32d00017f30e8000fd98740005ecc3a0002fd61d0001fab0e8000bd587400077e83a0003bd41d0001ef98e8000f74c740005fecb20002fe6590001bf32c80009f99640005facb200037d65900013eb2c8000bf19640005fac920002fe63900017eb1c8000bf98a40005fac520003df3290001ee9948000bf98640005fac320003df3190001ee98c8000bf98240007f4a120003f95090001dfa048000fed0240005fecaa0002fe65500017eb2a8000bf195400077ea8a0003bc54500017fb1a8000f7d8d40005bec6a0002fc6350001ee31a8000b718d400077e86a0003bd43500017fb128000bf189400077e84a0003bd4250001ef9928000f74c940005fec2a0002fc6150001dfa0a8000ef50540007be62a0003dd3150001fd2828000fe54140007f680a0003be40500017fb288000bf99440005faca20002fc65100017f3208000bf98c40005fac620002fe62100017eb108000f7cc840007ba6420002fe61100017eb088000f7cc440007ba6220002fe6010001dfa008000fe900400077a8020003f940100017fb2e6000bf99730005facb98002fc65cc0017fb266000bf99330005fac998002fc64cc0017f3166000bf58b30007be6598003dd32cc0017f30e6000bf58730007be6398003dd31cc0017fb2c6000bf99630005facb18002fc658c0017fb246000bf99230005fac918002fc648c0017eb1c6000f7d4e30007bca718003dd538c001ee29c6000f7d0e30007bc8718003dd438c001ee21c6000bf98a30005fac518003df328c001ef1946000f74ca30007b86518002fe618c0017eb0c6000f7cc630007bc6318003dd318c001ee18c6000bf98230007be6118003fb308c003efb2c6000f799630007bacb18007dc658c003efb246000f799230007bac918007dc648c001efaa46000f795230007baa918003dc548c003efb146000f798a30007bac518002dd628c003ee3146000f7d4a30007bca518003dd528c001ee2946000f7d0a30007bc8518003dd428c001ee2146001f7d8630007bcc318003dd618c0016eb0c6001f718630007bea318003de518c001eea8c6000f714630007be831800
  | 3 => 0xfa8a6200f794531007aca298803dd514c401eaa8a6200f714531007be8298803de414c401eb20a6200f750531007aa8298803dc414c401efb026200f798131007bac098803dc604c4016e3026200bfd9431005fcca18802fd650c4017e3286200bfd9031005fcc818802fd640c4017e3206200bf98c31005bcc618802fe620c4017eb106200f7cc831007ba6418802fe610c401ef9886200fd8c431007ba6218803f5310c4017f3006200bf58031005fecb90802fe65c84017eb2e4200bf19721005fec990802fe64c84017eb264200bf19321005fec790802fe63c8401ef31e4200b798f21005fac790803dd63c84016eb1e4200bf18f21007be6590803dd32c8401ef98e4200fd8c721007ba6390803f531c8401ea98e4200bf98321005fac190802ff65884017f32c4200bf59621005f8cb10802ff64884017f3244200bf59221005f8c910802ff63884017f31c4200f798e21005bcc710802fd6388401eeb1c4200b758e21005f8c710802fd6288401ef9944200f74ca21005fcc310803f65188401faa8c4200fd90621007ea8310803df3188401ee98c4200fbc8621007ee4310802fe60884017eb044200bfd9521005fcca90802fd65484017e32a4200bfd9121005fcc890802fd64484017e3224200bfd8d21005fcc690803de63484016f31a4200bf58d21007bac690802dd63484017e31a4200f7cc921007ba6490803f65148401faa8a4200fd90521007ea8290803df3148401ee98a4200fdc8521007dc4290802ff60484017e3024200bfd9421005fcca108037e65084013f3284200bf59421006faca108027d65084017e3284200bfd9021005fcc810803be64084015f3204200bf590210077ac810802bd64084017e3204200bfd8c21005fcc610803de63084016f3184200bf58c21007bac610802dd63084017e3184200bf98821007be6410803dd32084017f3084200f7cc421007ec6210803dd3108401fa9884200f54c421007de4210803f62108401f69084200fd48421005fcc010803fa60084017d3004200bf58021007f2c010802f960084017f326a000bf59350006fca9a80037c54d40017f31ea000f798f50005bcc7a8002fd63d4001eeb1ea000b758f50006fea7a80037d53d40017f316a000bf58b50006fea5a80037d52d4001ef996a000f74cb50005fcc3a8003f661d40017b30ea000bf58750007eac3a8002f561d4001bfa8ea000df54750007be63a8003dd31d40017eb2ca000bf992500077cc928002be64940017eb24a000ef592500057ac928002fe63940017eb1ca000bf98a50005fac528003df3294001ee994a000bf98650005fac328003df3194001ee98ca000bf98250006fea128003fb50940017fb22a000bf19150006fca8a80037c54540017fb1aa000f7d8d50005bec6a8002fc6354001ee31aa000b718d
  | 4 => 0x803bc54d04017f31e8200bf58f41005fcc5a0802fd62d0401dfa168200ef50b41007be65a0803dd32d04017f3068200bf58341005fecb20802fe6590401bf32c82009f99641005facb208037d65904013eb2c8200bf19641005fac920802fe6390401ef31c8200b798e41005fac720803dd63904016eb1c8200bf98a41005fac520803df3290401ee9948200bf98641007eca320803f55190401dfa0c8200fdd0641005fcc120802fd60904017fb2a8200bf99541005facaa0802fc6550401dfaa28200ef15141005fec6a0802fc63504017fb128200bf189410077e84a0803bd4250401ef9928200f74c941007eca2a0803f55150401fba0a8200ef90541005fec0a0802fc60504017fb288200bf99441005faca20802fc65104017f3208200bf98c41007bcc620802de63104017eb188200f758c41005bac620802fe62104017eb108200f7cc841007ba6420802fe6110401dfa088200fd904410077a8220803f541104017f3008200bf58041005fecb98802fe65cc4017eb2e6200bf19731005fec998802fe64cc4017eb266200bf19331007bea798803de53cc401eea9e6200f714f31007be8798803de43cc401eea1e6200f710f31005fcc598802fd62cc401ef9966200f78cb31007ba6598803dc32cc4017f3066200bf58331007becb98803de65cc401eeb2e6200f719731007bec998803de64cc401eeb266200f719331007bea998803de54cc401eeaa66200f715331007bec598803de62cc401eeb166200b758b31007b8c598803df52cc401ef2966200f754b31007b8a598803df42cc401ef2166200f750b31007b88598803df51cc401ef28e6200f754731007b8a398803df41cc401ef20e6200f750731007b88398803df60cc401ef3066200b798331007bac198803dc60cc4017fb2c6200bf99631005facb18802fc658c4017fb246200bf99231005fac918802fc648c4017eb1c6200b758e31005fcc518802fd628c401ef9946200f74ca31005fcc318803f6518c401faa8c6200fd90631007ea8318803df318c401fb98c6200bf98231005fac118802ff654c4017f32a6200bf59531005f8ca98802ff644c4017f3226200bf59131005f8c898803df534c401ef29a6200f754d31007b8a698803df434c401ef21a6200f750d31007b88698802ff624c4017e3126200f7cc931007bc6498803dd324c401ee1926200fd94531007eaa298803f6414c401faa0a6200fdcc531007bc6298802ff604c4017e3026200f7d9531007bcca98803dd654c401ee32a6200f7d9131007bcc898803dd644c401ee3226200f7d5131007bca898803dd544c401ee2a26200f7d8931005bec498803de624c401eeb126200f718931007bea498803de524c401eea926200f714931007be8498803de424c401eea126200f710931007bec298803d7614c401e
  | 5 => 0x9732005f8cb99002ff64cc8017f3266400bf59332005f8c999003df53cc801ef29e6400f754f32007b8a799003df43cc801ef21e6400f750f32007b88799002fe61cc801fb30e6400bd98732005fac399003f561cc8017ab0e6400bf98332005fac199003df65cc801ef32e6400f759732007b8cb99003df64cc801ef3266400f759332007b8c999003df54cc801ef2a66400f755332007b8a999003df52cc801ef2966400f754b32007b8a599003df42cc801ef2166400f750b32007b88599003df61cc801ef30e6400f598732007bac399002dd61cc801eab0e6400b558732007b8c399003df60cc801ef3066400b798332007bac199003dc60cc8017fb2c6400bf99632005facb19002fc658c8017fb246400bf99232005fac919002fc648c8017eb1c6400b758e32005fcc519003df328c801f79946400bf98632005fac319002fe608c8017eb046400bfd9532005fcca99002fd654c8017e32a6400bfd9132005fcc899002fd644c8017e3226400f7d4d32007bca699003dd534c801ee29a6400f7d0d32007bc8699003dd434c801ee21a6400fbcc932007bc6499002ff614c8017e30a6400bfd8132005f8c099003df654c801ef32a6400f759532007b8ca99003df644c801ef3226400f759132007b8c899003df544c801ef2a26400f755132007b8a899003df624c801e7b126400f7d4932007bca499003dd524c801ee2926400f7d0932007bc8499003dd424c801ee2126400f7d8532005bec299003de614c801eeb0a6400f718532007bec099003de604c801eeb026400f718132005b8c099002ff650c8017f3286400bf59432005f8ca19002ff640c8017f3206400bf59032005f8c819002fe630c8016f3186400bf98832007be6419003ee320c801ee9906400fb4c832005fcc219002fd610c8017f3006400bf58032005fcc9a8802fd64d4401bf2a6a200df15351005fcc7a8802fd63d44017f316a200bf58b51006fea5a88037d52d4401ef996a200f74cb51005fcc1a8802fd60d44017eb2ca200bf992510077cc928802be64944017eb24a200ef592510057ac928802fe6394401ef31ca200b798e51005fac728803dd63944016eb1ca200bf98a51005fac528803df3294401ee994a200bf98651006fea328803f751944017f304a200bf58251005fec8a8802fc6454401bf2a2a200df15151005fec6a8802fc63544017fb12a200bf18951006fea4a88037d5254401ef992a200f74c951007eea2a88037e51544017fb02a200bf18151005fcca28802fe64144017eb20a200bf98c51007bcc628802de63144017eb18a200f758c51005bac628802fe62144017eb10a200f7cc851007ba6428802fe6114401bfa88a200fd94451006faa228803f551144017f300a200bf58051005fecba0802fe65d04017eb2e8200bf197410077ea9a0
  | 6 => 0x17eb168600bf98743005fac3a1802fe60d0c017eb068600bfd9643005fccb21802fd6590c017e32c8600bf59243005fcc721803de5390c01eea9c8600efd0e43007be8721802fe6290c017eb148600bf98643005fac321802fe6090c017eb048600bfd9543005fccaa1802fd6550c017e32a8600f794d43007baa6a1803df4350c01df21a8600bfd8943005f8c4a1802ff6150c017e30a8600bfd8143005f8c0a1802ff6510c017f3288600bf59443005f8ca21802fe6410c017f3188600efd0c43007bc8621803bd4310c01eea188600bf98843005fac421802fe6110c01fb3088600bd98443005fac221803f56110c017ab088600bf98043005fac021802fe64d48017eb26a400dfd5352006faa9a9002fe63d48017eb1ea400bf98752005fac3a9002fe60d48017eb06a400bf59652005fcc929002fd6494801bf2a4a400df15252005fcc729003de63948016f31ca400bf58e52007bac729002dd63948017f314a400dfd4a52007dea529002fe61948017eb0ca400bf98252005fac129002ff6454801dfb22a400afd9152005f8c8a9003bc64548015e322a400dfd5152006faa8a9002ff63548017e31aa400fbd4952006fca4a9002ff61548017e30aa400bfd8152005f8c0a9002fe65148017f320a400ef990520057cc829002fd6414801deb20a400af59052006fca8290037c54148017f318a400f798c52005bcc629002fd6314801eeb18a400b758c52005fcc4290037f5214801f7290a400df54852007daa429002fe6114801fb308a400bd98452005fac229003f561148017ab08a400bf98052007f4c029002fa60148017eb00a400fe58052005f2c029002ff65d08017f32e8400bf59742005f8cba1003be54d0801deaa68400bf98f42005fac7a1002fe61d08017eb0e8400bf98342005fac1a1002ff65908017f32c8400bf59642005f8cb21002fd6490801dfaa48400ef15242005fcc721003de63908016f31c8400bf58e42007bac721002dd63908017f3148400fb94a42007daa521003bf4290801f7a148400bf98642005fac321002fe60908017eb048400bfd9542006fecaa10027f65508017f32a8400bf59542005f8caa10037c65508013e32a8400ef951420077aa8a1002ff63508017e31a8400fb94942007daa4a1003ef4250801df2128400bfd8542005f8c2a1002ff60508017e3028400bfd9442005fcca210037e65108013f3288400bf59442006faca210027d65108017e3288400bf990420077ea821003bc54108017f3188400f798c42005bcc621002fd6310801eeb188400b758c42005fcc421003bf4210801f72108400ef50842007da8421002fe6110801fb3088400bd98442005fac221003f561108017ab088400bf98042007f4c021002fa60108017eb008400fe58042005f2c021002ff65cc8017f32e6400bf5
  | 7 => 0x502a0a81080d0020f0008090040100b8050100200004900a0100100000003c02800014000038030160140b00400c004038010040040000b02600c030040001500500607a004000070ca01c0180900a0140a04100000402000004008008170220d4010030020000101900601c078040000000381d02c004000060000300000300c0140100101200001807026000020020080340000000e0140380600002c0000100c0000080500c00c0202004e010008030100800300200a00c0003500006c238250100180282700a018000050040180a8000000000900004a014090030200080080400000002801000080018060000180100000201c06801000028000000160800100900a0080b81601c0000481300a0180d80001a00000800006034030090060000680300202c0080a0320200000001c0000280a00802002023002060020140060040000a00603801000012000018060040000000000a0000000501401c0180d0020040080801000006800000004028030bc0040580505c0100281100c0201680100008c0281f00204c018000040000e0000000c40080400c074000030000100882300e000008000020000c8000060040400000200c0500000000004803000008010030060380000b024000018000080340402100a0000180e03401003808010008000050400000180d03800bf98f54005fac7aa002fe62d50017eb16a800bf98754005fac3aa002fe60d50017eb06a800bf59654005fcc92a0037f5495001dfaa4a800cfd5254005fcc72a002fd63950017f314a800bf58a54005fcc32a002fd61950017f304a800bf582540077ea8aa0037e54550017fb1aa800bf18d54005fec4aa002fc62550017fb0aa800bf18554005fec0aa002fc60550017f328a800bf99054006fea82a003be5415001beaa0a800ef550540067aa82a002fe6315001ef318a800b798c54005fac62a003dd63150016eb18a800bf98854007dcc42a002ee62150017eb10a800fb58854005dac42a002fe6115001fb308a800bd98454005fac22a003f561150017ab08a800bf98054007f4c02a002fa60150017eb00a800fe58054005f2c02a002fe64d4c017eb26a600bf98b53005fac5a9802fe61d4c017eb0ea600bf98353005fac1a9802fd6594c017f324a600bf59253005fcc7298037f5394c01efa9ca600bf98a53005fac529802fe6194c017eb0ca600bf98253005fac129802ff6454c017e322a600f7d4d53006fca6a9802ff6254c017e312a600bfd8553005f8c2a9802ff6054c017e302a600bf99453005fcc829802fd6414c017f318a600dfd4c53007bca6298037d5314c01eea98a600bf98853005fac429802fe6114c01fb308a600bd98453005fac229803f56114c017ab08a600bf98053005fac029802ff65d0c017f32e8600bf59743005f8cba1802fe62d0c0
  | 8 => 0x33119f2091760331889b322ca438678c7091206ad38001e700002c0000308c41f20000541e4a3a91a081a1001f150a6332d0b92f7a30109945a01a821b5006b320002670000ff04b0002152450000001220db8f50649ad21a0dcab80b02f400219a95520d80010080030da0380010f0b1a5eb0a8792c1b39897944a5bb3aac492100029b21a89508d00000005127e00003e8868001f091c8260e28002c78000000002920002e78162650000000002fb14ea430000000000001a50000ea8000dd333a678ed07e0000002b41dc18ba0f2939bd92b1498820c482f3291a008ea16316aa62a113d1ceaa7979a5aa52a950c68b10360f18a3ad022d8030d42d233a146ad12118ee2449b81cd1f38d48e02af0ae3388ef2dc0232900f101c18f89004d89c33924018da788bc83c89b1a799297029432231027511c0f3a3ba38acb1af28683387297a3380b59528d010625e2cc25b1e129a08c2e9a31175b111778e1a5800030f0001311ea829266219046a2914fa070528e88319d00591c18d718829eaad33e99009c9378b0b192bba599c000191f9b59dab021d1902967108a2e05e0ad19c91097da5c3279ac8b70830fcab5a73a49047257800000254ab313731b9160002620d61d328c8000002b2aefaeb16c27b2ae80016aa40a4a01300030a037b122c632e30d1cb92a2cd8cd8df0e616106b1bf107b351b6af394a20c9c70b69aa8bb1d20dfa771f3132a3280093c84a0a30cd0e81b90d0b062010f031d233adf1970001d618ea8d24880017c84b92b9331b1a4980007c0748fd80010b31e9fd26ca80224b130fa8aa17097c04780000000009595880f00008700000000000015587700026480011e32d80000015d8ba0f680000008a8000681298178eb000117a260001ef8641948000002be0429a58ea0000a700000000015432face88629f23e90b8fc0a2894a37b24af097a9121411360000a9abc16897b1de10128999130124689f20ea0587b09e8b49341a421e126035adb03532680032aa989a8a0c17f86d0dc18c0410a78cb2a680d2c90d58000030000000400000801c0a001000060140040000100180f00a0580003700a02c03008000028018080040080400000e0200080301400400001002004078020160140000b006028000010020980280200a0280b00200a03c048000000100000000401c0188101c00001803044018010140b80180002500200c0300000400c0000606600c080010020b813807014000000050000080000a08400809801002000000090020b4040070160140080b00003c0680004402c0e00200e0000000000a0000e02702000c1000c04c034250060000280282d00a03c018000000880080002a014040090000040281b004004060020000640100403a0080481402801c000090000000303c0640400000500400c0900
  | 9 => 0x9fa1751930088138000782bd2a08001b084f1d40ac1519e096091b1bc8e38182459f129081d00012a92500000608819bb378702282adabdb208000000000000000000000002112e100000027403bac112e00028293c1f5a7f95d28d8002bb33624b8001be1380002d6ae2a8e04980f9e42968620ffa3f9392e098307330b86a24710a00000aac5acb9e5aa01abb1f33fa13afd05fb3e0000000a032c963979189a130092f181700000014f00011a8142e916d17e0998d51268f08000002b7334b068e780010820d210abf11d15999fa8398b26fb0333c87f0c98000389630002fe00490fb098000ca0002c00a482895c0c81348c583423d15b2f702d800000000143a4e8f9909122b038001490000001eb0001ed80000005ea1b00000000014c2911d991827182fa9cb21a8093b9da16e0e207088919e32e9e7ace12927bafa04e99396605691f2890002572e69730000000001c20011198001f78000001dc800000140a020000000f2024084b2f1cab0fb1e1321cf00719d0481fa9b38000e11a4a0b18d0b631aad9a0998aa69a3521c0909530c905c263ac89118000002ee1b606da539ce199b1980019daaa0002501c7a5c8488000c506121f8c32550eb800169a218000e92611720001cb2721df0000001510000000000001171de86ba1c921af20001bc0001fc1e20000002278001978000001319d69433332b8aab953a6d8002659b710513fa6a00021e8000740001fd8001fe889a0500a0e528e9c48000bf1c40000b30c8a6e2f80f798f01034020e20f8fd0d7b30a2e9fca078001c99f5010893000220a9c2148b79649e294c9168601000f80e71ab199287044120a810a89cc9e812587782117724123d9ecaec2dda4a9042da9839d386f15913f2b015e8ab8ce0000000002a580d8da92c1a6139a0b87baf9000314277a198fe2fea9f86e04c03680025f21f05f22332b8000000002f5a289bb0690960beb259110f307c83827d2d89db2693262ca843a72b238a60e3057186a6b1a1000260a36a91ae8b1c9cc22a1af90eaa41669951ad9a6a5905ba888889f99070c113b2712d5b0080004cab692d0e0a4d08103d00008ba2b0000000000148c1875ab18af8e4a2ba2220311323991005c9ba2a99bf9472e026a81188db340a82169b00918001f830b23700010c0ba92783a9baad51828000003082d82060be331a34a35b05914173a2f00018500000009a1018f61df80b00831a19c0002ba258a51af88000000001601388000d20000000561a1800002a042a480008f1248a431f87a1f624180000016b800189266ab08000502340d91a2041930aa880007e9cf93013a80017686c8d68fb0000000002a2301a3c83023f1c3b302e48001c8ae5a7a82e90e1338a586091d8000878003079651ee000000285000022855880912a30ac500025a00
  | 10 => 0xe52fc0001b788e0712f10f40b50000de2e50b3800154aac82a07d1c830707da2c14b02aae22330001a094601e1d729798124e2758320d894520a8209fe1ddae3a9d1f69a8009a6d33d92f18a332844a428ce95a9c327c96b2238c61b292e9641c5a4c1d49ea29a97185d0fe8ad8a50530b8268b1896805aab23368d327302b8f7118a6eaed0220ecb2c00024b03115e000185a84aff850aff2520000af07627000032404917d0a10f882cb3c0001eb9ac2f021880e06607995f22d0000fa00000024600023208516fa440000bba2980009da79b0289226f22700021bac823811ea5d21286580028a0000298f918e2f50000000752619c6a1d14d84a94d0992b11922478000251d580009716e8cf91ba8f27c1b4b118002558002cf1740de97f05780530c9571e1b35a508db0e5a749c90000002c40c0a9d90496f0cc95a2ea9ffadba8195b97b9230000002f980016a00022022a8000003298ed9918000120c22b79242ca2cd14286e9238738278001bd105a9480000030ea8b0000000000002a1839a1d92d8002e71dd0002a81aa0c38ec00009880bb162212780002c9b090000000d3a5130032a0f48002769a92d40272ef16cb210d2800051ad9115a83174a7f06188fadca6b90689a8c29e631c2ba89e17e845a7a296190b1282b2761b123e0d11619148582fc956a4f31b0189f8ab48a697832819ea8c0b42c208a0539a99e001293694a80023600000000000005b1f1aa730c043315ad1b201d89dbabc8002ac20895c9ff05d8259e990caf62878000f5a8fb289d280030e0000000420000002b98000000bd94e0169f2abfac69b89e68192ab2e830880031783e1581282fd984b10ac0a17297215adf97880e8722229a72561b4187915046231a530668d9a99a861ca0269d901519a2ee89f95f8390e686c204845305141a92902034b14afb9981400f290d31380c99b16786fa251f70b29819c62843232d28cc0bc01f94829324f863b04172a682a91bb8aa9a28159ae23b1e324d81b9800dd8002d4a9e1a39c13272980a23229d52a28002420d83252e40000000002d700018400003b18ca3c1c2aea0980bd0eeb3b9272242b3aeb81992c85483f082a6432b33d0fb9350d18000371d81ef1989c080003d80000000000000000004fa14182000186000000142103ac70e98520001d08000000b200023a13e82e2faa392001be8cf27d8110001d7a8aad789692013a03a19611385a270a7e8589ed2e62a500006993d9e8a2681a0650001e93170631d1285a791690002f2acf83f95209d16d80029b8002ecaf490ab15162aa301cae1b0481b2f30842b52080c78001712008002e32dd0a094780587fade1f92179a3023804024a0a33b2c29ae9578002628da00021208b2d30ae9e3a5f98082184d1c500007ab18000071800000195800000000092
  | 11 => 0x2af935ada28b9cda5d8ef8002259288002c380003c2482ae0000ab1941f00202541658000789441488002990000b980381a8cb876aaa800093ad0a180bf8002602c30400c02f6800080062ade9b99190ac80000006a90dacc80000000000000024caed8000000000281501622be8b888c9ec2880838408859b20001f401e832a6c0e431db3700004e1fb0550a900013e00780015600000012f8002a380014b9968000a182d20281da95b3f22f9fb859ab91f4a568688ca8002b609400c1ee98706709bad61031
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe7319410004dd7319410004ee7219410004ed72194100047e75d90100047d75d9010004de73d9010004dd73d9010004ee72d9010004ed72d9010004bd76990100063e65990100063d6599010006b6719901000e9e309901000e9c30990100063e65590100063d655901000e9e305901000e9c30590100047e75190100047d7519010004be7419010004de7319010004dd7319010004ee7219010004ed72190100047e75d8c100047d75d8c10004be74d8c10004bd74d8c10004ee72d8c10004ed72d8c10004dd7698c100065e6598c100065d6598c100069e6498c100069d6498c10004dd7298c1000cde7098c100065e6558c100065d6558c100069e6458c100069d6458c10004df7258c10004df7158c10004dd7158c1000cdc7058c100047e7518c100047d7518c10004be7418c10004bd7418c10004de7318c10004ee7218c10004ed7218c10004f67118c100047e75d88100047d75d8810004be74d8810004bd74d8810004de73d8810004dd73d8810004de7398810004dd7398810004ed76988100066e65988100066d6598810006ae6498810006ad6498810006ce6398810006cd6398810006ce7398810006cd739881000ece309881000ecc30988100066e65588100066d6558810006ae6458810006ad6458810006ce6358810006cd6358810006ce7358810006cd7358810006e4715881000ece305881000ecc30588100047e75188100047d7518810004be7418810004bd7418810004de7318810004dd7318810004ee7218810004f67118810004fa7018810004df76cc810004dd76cc8100065e65cc8100065d65cc8100069e64cc8100069d64cc810006ce62cc810006cd62cc810005d571cc810004df764c810004dd764c8100065e654c8100065d654c8100069e644c8100069d644c810006ce624c810006cd624c810005d7714c81000dd8704c810004de7398410004dd7398410004f57694410005b57494410006b56494410006d56394410006e56294410006766554410006b56454410006d56354410006e56254410004f57690410005757590410006756590410006d56390410006e56290410006756550410006b66450410006d56350410006e56250410004dd76cc4100065e65cc4100065d65cc4100069e64cc4100069d64cc410006ce62cc410006cd62cc410004df764c4100065e654c4100065d654c4100069e644c4100069d644c410006ce624c410006cd624c410006d6614c410004f576c8410006d563c8410006e562c8410004f57608410005757508410005b57408410006d56308410006e56208410005f1700841000cdf739801000cdc7398010006d563c4010006e562c4010004f97684010006e96284010004f77644010006d56344010006e5624401000fd03044010004fb7644010006e96244010007d33144010
  | 1 => 0xcb10006d6634c710005d7764c710006d7764c710006d7654c710006d5654c710006d7644c710006d5644c710005d7724c710006d6624c710006d4624c71000dd4704c710005d57388710005d57348710005cd720c310005d5710c310004be74d9610004bd74d9610004de7399610004dd7399610004df7359610004dc73596100047e75d92100047d75d9210004de7399210004dd7399210004df7359210004dc7359210004dd72d8e1000ed571d8e1000eda70d8e100047e7518e100047d7518e10004be7418e10004bd7418e10004ee7218e10004ed7218e1000e5e7518e1000e5d7518e1000e9e7418e1000e9d7418e1000ece7218e10004dd7218e1000ecd7218e10004cd7218e1000ed57118e1000eda7018e10004de7398a10004dd7398a10004df7358a10004dc7358a100047e7518a100047d7518a10004be7418a10004bd7418a10004de7318a10004dd7318a1000cde76cca1000cdc76cca10005d571cca1000cde764ca1000cdc764ca10006ce624ca10006cd624ca10005d7714ca10005b57494610006d76394610006d76354610005757590610006d76390610006d7635061000dda70cc61000dd8704c610006d763c8610005757508610005b57408610006d76308610005f17008610007c93248210005f07148210007e3214821000ed763c4210004be74d9510004bd74d9510004de7399510004dd7399510004f57199510004df7359510004dc73595100047e75d91100047d75d9110004de7399110004dd7399110004f57199110004df7359110004dc7359110004dd72d8d10004de7398d10004de7618d10004dd7218d10006d57118d1000cde7018d1000cdc7018d10004de7398910004dd7398910004df7358910004dc7358910004f771589100047e75189100047d7518910004be7418910004bd7418910004de7318910004dd7318910004de76cc910004dc76cc910005d571cc910004de764c910004dc764c910004de76cc510005da70cc510005d5738c510006d4638c510004dc764c510005d8704c510004f4764c510005f0704c510006d7764c510006d4764c510004d4764c510006d7654c510006d5654c510006d7644c510006d5644c510005d7724c510006d6624c510006d4624c510007d3704c51000dd4704c510007d0704c510005d0704c510004f67688510005d57388510004f47648510005d57348510004de768c110004de760c110005cd720c110005d5710c110007d13188110004f87648110007c93248110007d13148110007e12148110007d131c411000dd77384110004be74d9410004bd74d9410004de73d9410004dd73d9410004ee72d9410004ed72d94100047d769941000676719941000e5e309941000e5c309941000e5e305941000e5c30594100047e7519410004be7419410004bd7419410004d
  | 2 => 0x4de73d9420004dd73d9420004f671d9420004f571d94200047d769942000e5e309942000e5c309942000e5e305942000e5c30594200047e7519420004be7419420004bd7419420004de7319420004dd7319420004f67119420004f57119420004fa70194200047e75d90200047d75d9020004de73d9020004dd73d9020004f671d9020004f571d9020004bd76990200063e65990200063d659902000e9e309902000e9c30990200063e65590200063d655902000e9e305902000e9c30590200047e75190200047d7519020004be7419020004de7319020004dd7319020004f67119020004f57119020004fa70190200047e75d8c200047d75d8c20004be74d8c20004bd74d8c20004f671d8c20004f571d8c20004dd7698c200065e6598c200065d6598c200069e6498c200069d6498c20004dd7198c2000cde7098c200065e6558c200065d6558c200069e6458c200069d6458c20004df7258c20004dd7258c20004df7158c2000cdc7058c200047e7518c200047d7518c20004be7418c20004bd7418c20004de7318c20004ee7218c20004f67118c20004f57118c20004de7398820004dd7398820004dd76cc8200065e65cc8200065d65cc8200069e64cc8200069d64cc820005d571cc820004df764c8200065e654c8200065d654c8200069e644c8200069d644c820006ce624c820004de7398420004dd7398420006766598420006756598420006b66498420006b56498420006d66398420006d56398420006d67398420006d57398420006d73298420006d5329842000ed6309842000ed43098420006766558420006756558420006b66458420006b56458420006d66358420006d56358420006d67358420006d57358420006d73258420006d5325842000ed6305842000ed43058420004df76cc420004dd76cc4200065e65cc4200065d65cc4200069e64cc4200069d64cc420006d661cc420006d561cc420004df764c420004dd764c4200065e654c4200065d654c4200069e644c4200069d644c420006d6614c420006d5614c42000dd8704c42000cdf739802000cdc7398020006cd63c8020006e561c8020006796588020006b96488020006f16188020004ef7648020006cd6348020006e56148020004fb7648020006796548020006b96448020006f16148020004be74d9710004bd74d9710004de73d9710004dd73d9710004de7319710004dd73197100047e75d93100047d75d9310004de73d9310004dd73d9310004de7319310004dd7319310004dd7298f10006d67198f10004df7258f10004de73d8b10004dd73d8b10004de7398b10004dd7398b100047e7518b100047d7518b10004be7418b10004bd7418b10004de7318b10004dd7318b10004df76ccb10004dd76ccb10005d571ccb10004df764cb10004dd764cb10005d8704
  | 3 => 0xf7158f20005d571ccb20006ce634cb20005cf764cb20006cf764cb20005cf714cb2000dcc704cb20004de7398720004dd7398720004df76cc720004dd76cc720005cd72cc720004df764c720004dd764c720005d8704c720005cd73c8720007c531c8720005cd7348720005cd720c320005d5710c320004be74d9620004bd74d9620004de7399620004dd7399620004f67199620004f57199620004df7359620004dc73596200047e75d92200047d75d9220004de7399220004dd7399220004f67199220004f57199220004df7359220004dc735922000ecd72d8e20004dd71d8e2000eda70d8e200047e7518e200047d7518e20004be7418e20004bd7418e20004f67118e20004f57118e2000e5e7518e2000e5d7518e2000e9e7418e2000e9d7418e2000ecd7218e2000ed67118e20004dd7118e2000ed57118e20004d57118e2000eda7018e20005d571cca2000dda70cca2000dd8704ca20004de7398620004dd7398620004df7358620004dc735862000cde76cc62000cdc764c620006d6614c620006d5614c620005b9749422000579759022000ecf63c8220004de7399520004dd7399520004f67199520004f57199520004bf7459520004bc7459520004df7359520004dc7359520004f77159520004f47159520004de7399120004dd7399120004f67199120004f571991200047f75591200047c7559120004df7359120004dc7359120004f77159120004f47159120004dd71d8d20004de7398d20004f67198d20004f57198d20004f77158d20004f47158d20004de7618d20006cd7218d20004dd7118d20004de76cc920005d571cc920005da70cc920005cd738c920006cc638c920004dc764c920005d8704c920004ec764c920006cf764c920006cc764c920004cc764c920005cf714c920007cb704c92000dcc704c920007c8704c920006d763d8520006d463d8520007c532d8520006d773d8520006d473d8520006d732d8520006d532d85200047e75185200047d7518520004be7418520004bd7418520004de7318520004dd7318520006d76318520006d46318520007c53218520006767518520006757518520006b67418520006b57418520006d67318520006d57318520006d73218520006d53218520006f17018520004de76cc520004dc76cc520005cd72cc520006d761cc520006d461cc520004de764c520004dc764c520006d7614c520006d4614c520005cd73c8520006e461c8520007c531c8520005cd7348520005b97494120007c93294120004f87654120007c93254120005797590120007c93290120004f87650120007c93250120004de768c120006d7618c120006d4618c120004de760c120005cd720c120005d5710c120006d7610c120006d4610c120007c932c812000dcf7388120004be74d9420004bd74d9420
  | 4 => 0x8430004df725843000ed6105843000ed4105843000dd77658430006d7765843000ed76558430006d6655843000f566558430006566558430006d5655843000f55655843000655655843000ed4655843000ed76458430006d6645843000f966458430006966458430006d5645843000f95645843000695645843000ed4645843000ed76258430006d6625843000fc66258430006c66258430006d5625843000fc56258430006c5625843000ed4625843000ed66058430006d77558430006d67558430006d57558430006d47558430006d77458430006d67458430006d57458430006d47458430006d75458430006d65458430006d55458430006d45458430006d77258430006d67258430006d57258430006d47258430006d75258430006d65258430006d55258430006d45258430006d74258430006d64258430006d54258430006d4425843000ed6705843000ed4705843000ed6505843000ed4505843000ed6405843000ed4405843000ed6205843000ed42058430006cd62d4430006d561d443000dda70d4430005d970d443000cde7694430004dd76944300059e74944300059d7494430006cd6294430006d56194430006cd6254430006d5615443000cde7614430004dd7614430006cd6214430006d56114430006cd62d0430006d561d043000dda70d0430005d970d043000cde7690430004dd76904300055e75904300055d7590430006cd6290430006d56190430006cd6250430006d5615043000cde7610430004dd7610430006cd6210430006d5611043000cde76c8430004dd76c8430006cd62c8430006d561c843000cde7688430004dd7688430006cd6288430006d56188430004dd7648430006cd6248430006d56148430005db704843000dd8704843000cde7608430004dd76084300055e75084300055d75084300059e74084300059d7408430006cd6208430006d5610843000dda7008430005d9700843000eda709803000f5a659803000f59659803000f9a649803000f99649803000fca629803000fc9629803000fd2619803000fd16198030004dd76d4030006cd62d4030005d671d4030005d571d4030006d561d4030004df7654030006cd6254030006d56154030004dd76d0030006cd62d0030005d671d0030005d571d0030006d561d0030004df7650030006cd6250030006d56150030004de73d9720004dd73d9720004bf7459720004bc7459720004be7419720004bd7419720004de7319720004dd7319720004f67119720004f57119720004de73d9320004dd73d93200047f75593200047c75593200047e75193200047d7519320004de7319320004dd7319320004f67119320004f57119320004f67198f20004f57198f20005d57198f20006ce7298f20006d67198f20004dd7198f20006d57198f20004d57198f20004d
  | 5 => 0x6ce62cc430006cd62cc430006d561cc43000dda70cc430004dd768c430006cd628c430006d5618c4300065e654c4300065d654c4300069e644c4300069d644c430006ce624c430006cd624c430006d6614c430006cd620c430006d5610c43000dda700c430006cd62cc030006d561cc030004df764c030006cd624c030006d5614c030004fb764c03000d5d769943000e5f629943000e5f619943000e5e609943000d5f76594300065f765943000e5f645943000e5f625943000e5f615943000e5e605943000d9d769903000f1e659903000f1d659903000e9f629903000e9f619903000e9e60990300065d655903000d9f76590300069f765903000e9f655903000f1e65590300069d655903000f1d65590300061d655903000e9f625903000e9f615903000e9e60590300071f549503000cde7615030004dd76150300071d5415030005ce7215030005cd7215030005d67115030005d5711503000dda7015030005d9701503000dcd769883000f4e659883000f4d659883000f8e649883000f8d649883000ecf619883000ece60988300065e65588300065d65588300069e64588300069d645883000ecc6258830004df715883000ece205883000ecc205883000dcf7658830006cf765883000ecf6558830006ce655883000f4e65588300064e6558830006cd655883000f4d65588300064d655883000ecc655883000ecf6458830006ce645883000f8e64588300068e6458830006cd645883000f8d64588300068d645883000ecc645883000ecf615883000ecc615883000ece6058830006cf7558830006ce7558830006cd7558830006cc7558830006cf7458830006ce7458830006cd7458830006cc7458830006cf5458830006ce5458830006cd5458830006cc5458830006cf7158830006ce7158830006cd7158830006cc715883000ece705883000ecc705883000ece505883000ecc505883000ece405883000ecc405883000ece105883000ecc1058830006cd62d483000cde7694830004dd7694830006cd62948300059f74548300059c7454830006cd625483000cde7614830004dd76148300059e74148300059d7414830006cd6214830005d67114830005d5711483000dda7014830005d97014830006cd62d083000cde7690830004dd7690830006cd62908300055f75508300055c7550830006cd625083000cde7610830004dd76108300055e75108300055d7510830006cd6210830005d67110830005d5711083000dda7010830005d97010830006cd629843000dd5769843000f56659843000f55659843000f96649843000f95649843000ed7629843000fc66298430006d5629843000fc56298430006c5629843000ed660984300065e65584300065d65584300069e64584300069d6458430006ce6258430006cd625843000ed4615
  | 6 => 0x76198630004df725863000ed6105863000ed4105863000cde7694630004dd76946300059e74946300059d749463000cde7614630004dd761463000cde7690630004dd76906300055e75906300055d759063000cde7610630004dd761063000cde76c8630004dd76c8630006cd62c863000cde7688630004dd7688630006d56188630004dd7648630006cd6248630006d5614863000cde7608630004dd76086300055e75086300055d75086300059e74086300059d740863000dda7008630005d97008630005d671d4230005d571d4230005d671d0230005d571d0230004dd7399530004f67199530004f57199530004df7359530004dd7399130004f67199130004f57199130004df7359130004de76cc930005d571cc930006cf624c930004de76cc530006d7614c530004be74d9430004bd74d9430004ee72d9430004ed72d9430004f671d9430004f571d94300047d76994300065e73994300065c73594300047e7519430004be7419430004bd7419430004ee7219430004ed7219430004f67119430004f571194300047e75d90300047d75d9030004ee72d9030004ed72d9030004f671d9030004f571d9030004bd76990300063e65990300063d65990300069e73990300063e65590300063d65590300069c73590300047e75190300047d7519030004be7419030004ee7219030004ed7219030004f67119030004f571190300065d65d4c30004dd7694c300069d6494c3000dda7094c300065e6554c300069d6454c30004dd7614c30005d67114c30005d57114c3000dda7014c300069d64d0c30004dd7690c300065d6590c3000dda7090c300065d6550c300069e6450c30004dd7610c30005d67110c30005d57110c3000dda7010c300066e65988300066d6598830006ae6498830006ad64988300066e65588300066d6558830006ae6458830006ad6458830006ce7358830006cf5358830006ce5358830006cd5358830006cc5358830006cf4358830006ce4358830006cd4358830006cc43588300065e65cc8300065d65cc8300069e64cc8300069d64cc830006cd62cc830005d671cc830005d571cc83000dda70cc830004dd768c830006cd628c8300065e654c8300065d654c8300069e644c8300069d644c830006ce624c830006cd620c83000dda700c830006766598430006756598430006b66498430006b56498430006e66298430006e56298430006d73298430006d53298430006766558430006756558430006b66458430006b56458430006e66258430006e56258430006d67358430006d75358430006d65358430006d55358430006d45358430006d74358430006d64358430006d54358430006d44358430006d73258430006d63258430006d53258430006d432584300065e65cc4300065d65cc4300069e64cc4300069d64cc430
  | 7 => 0xca400065d65cca40005d571cca400065e654ca400065d654ca40006ce624ca40006cd624ca40004de7398640004dd73986400065e65cc6400065d65cc6400065e654c6400065d654c640006d6614c640006d5614c64000dd8704c6400067a65542400063e65d0240004de7399540004dd7399540004f67199540004f57199540004df7359540004dc7359540004be76d51400063f65d5140005ba70d51400063d65151400059d7315140005ad7215140005b57115140005ba7015140004dd72d8d40004dd71d8d40004f67118d40004f57118d40005d57118d40004dd7218d40006d67118d40004dd7118d40006d57118d40004d57118d400069c63d0d400047e75189400047d7518940004de7318940004dd7318940004f67118940004f571189400053c7550940004de76cc940004dc76cc940005d571cc940004de764c940004dc764c940004de7318540004dd7318540006b46150540004de76cc540004dc76cc540004de764c540004dc764c54000795414c540005d8704c540005ba7494140004f876541400073854541400053e7590140004be74d9440004de7319440004dd7319440004ee7219440004ed7219440004f67119440004f57119440004fa7019440004de7398840004dd7398840005d571cc840006ce624c840006cd624c840004de7398440004dd7398440006d6614c440006d5614c4400047e75980400047d7598040004bf7650040004fb7650040004f67119730004f57119730004f67119330004f57119330006cd62ccb30005d571ccb30006d561cc730004be74d9630004bd74d9630004f67199630004f571996300047e75d92300047d75d9230004f67199230004f5719923000dda70d4e3000dd87054e30005d67114e30005d57114e3000dda70d0e3000dd87050e30005d67110e30005d57110e30004f77158a30004f47158a30005d671cca30005d571cca3000dda708ca30006ce624ca30006cd624ca3000dd8704ca3000dda708c630006d6614c630006d5614c63000dd8704c630005d67199630005d57199630005d67199230005d571992300071f549523000cde7615230004dd76152300071d5415230005ce7215230005cd7215230005d67115230005d5711523000dda7015230005d9701523000ecf6298a30005d77158a30005d47158a30004df7158a30006d77158a30004d77158a30006d47158a3000ece2058a3000ecc2058a3000cde7694a30004dd7694a300059f7454a300059c7454a3000cde7614a30004dd7614a300059e7414a300059d7414a30005d67114a30005d57114a3000dda7014a30005d97014a3000cde7690a30004dd7690a300055f7550a300055c7550a3000cde7610a30004dd7610a300055e7510a300055d7510a30005d67110a30005d57110a3000dda7010a30005d97010a3000ed
  | 8 => 0x6755258750006d73258750006d53258750006766154750004df76cc750004dd76cc750006d661cc750006d561cc750004df764c750004dd764c750006d6614c750006d5614c75000755514c750004de7399250004dd7399250004f67199250004f571992500069e73992500069d7399250006b67199250006b57199250006ba709925000e9e309925000e9c309925000e9e305925000e9c3059250004de7398a50004dd7398a500069e64cca500069d64cca50005d571cca500069e644ca500069d644ca50006ce624ca50006cd624ca50004de7398650004dd73986500069e64cc6500069d64cc6500069e644c6500069d644c650006d6614c650006d5614c65000dd8704c6500063e64d42500063f64951500057a70951500055d73151500056d72151500057571151500057a7015150004dd72d8d50004dd71d8d50004f67118d50004f57118d50005d57118d50004dd7218d50006d67118d50004dd7118d50006d57118d50004d57118d500065c63d4d50004be7418950004bd7418950004de7318950004dd7318950004f67118950004f571189500053c7454950004de76cc950004dc76cc950005d571cc950004de764c950004dc764c950004de7318550004dd7318550006746154550004de76cc550004dc76cc550004de764c550004dc764c55000755514c550005d8704c5500053e7494150004de7398850004dd7398850005d571cc850006ce624c850006cd624c850004de7398450004dd7398450006d6614c450006d5614c4500047f7654050004fb7654050004de73d9740004dd73d9740004f671d9740004f571d9740004de7319740004dd7319740004ee7219740004ed7219740004f67119740004f571197400063d65153400059d7315340005ad7215340005b57115340005ba7015340004dd7298f40004dd7198f40004df7258f40004df7158f400069e6350f40004de7398b40004dd7398b400053c7550b40004df76ccb40004dd76ccb40005d571ccb40004df764cb40004dd764cb400047e75987400047d7598740004de7398740004dd7398740006d66398740006d56398740006767598740006757598740006d67398740006d57398740006d73298740006d53298740006d66358740006d56358740006b75458740006b45458740006d67358740006d57358740006b74258740006b54258740006d73258740006d53258740006b66150740004df76cc740004dd76cc740006d661cc740006d561cc740004df764c740004dd764c740006d6614c740006d5614c74000795414c740004de7399640004dd7399640004f67199640004f571996400065e73996400065d73996400067671996400067571996400067a709964000e5e309964000e5c309964000e5e305964000e5c3059640004de7398a40004dd7398a400065e65c
  | 9 => 0xe73d9021004dd73d9021004fa70d9021004f970d9021004bd76990210063e65990210063d65990210063e65590210063d65590210047e75190210047d7519021004be7419021004de7319021004dd7319021004f67119021004fa7019021004f970190210047e75d8c210047d75d8c21004be74d8c21004bd74d8c21004fa70d8c21004f970d8c21004dd7698c210065e6598c210065d6598c210069e6498c210069d6498c21006d67198c2100cde7098c210065e6558c210065d6558c210069e6458c210069d6458c2100cdc7058c210047e7518c210047d7518c21004be7418c21004bd7418c21004de7318c21004fa7018c21004f97018c21004de7398821004dd7398821004dd76cc8210065e65cc8210065d65cc8210069e64cc8210069d64cc821005d571cc821004df764c8210065e654c8210065d654c8210069e644c8210069d644c821004de7398421004dd7398421004dd76cc4210065e65cc4210065d65cc4210069e64cc4210069d64cc421004f5768c42100675658c421006b5648c421005d5738c421004df764c4210065e654c4210065d654c4210069e644c4210069d644c42100675654c421006b5644c421006d6634c421005d7764c421006d7764c421006d7654c42100756654c421006d5654c42100755654c42100655654c421006d7644c42100796644c421006d5644c42100795644c42100695644c421005d7724c421006d6624c421005d4704c421007c531c8421006756588421006b56488421005d57388421004ef7648421004f77648421006756548421006b56448421005d573484210067a6598021006796598021006ba6498021006b96498021006da6398021006d96398021007d1319802100edb739802100ed87398021006db3298021006d93298021006db3198021006d93198021004df7358021004dc7358021006d531580210067a6558021006796558021006ba6458021006b96458021006da6358021006d96358021007d13158021006db7358021006d87358021006db3258021006d93258021006db3158021006f23158021006d93158021006f13158021006d13158021006eb2158021006f22158021006e92158021006f121580210063d64153500055d73153500056d72153500057571153500057a7015350004dd7298f50004dd7198f50004df7258f50004df7158f500065e6354f50004de7398b50004dd7398b500053c7454b50004df76ccb50004dd76ccb50005d571ccb50004df764cb50004dd764cb50004be7498750004bd7498750004de7398750004dd7398750006d66398750006d56398750006b67498750006b57498750006d67398750006d57398750006d73298750006d53298750006d66358750006d56358750006765458750006745458750006d67358750006d57358750006775258750
  | 10 => 0x5310079541105310055e75181310055d75181310059e74181310059d7418131005ce7218131005cd721813100e5e751813100e5d751813100e9e741813100e9d741813100ece7218131004dd721813100ecd7218131004cd7218131006d65118131006d55118131006d64118131006d54118131004be74d9431004bd74d9431004de73d9431004de7319431004f671194310047e75d90310047d75d9031004de73d9031004de7319031004f67119031006cd62cc831005d571cc831004df764c831004df764c431004f7764c431006d6634c431004de73d9721004dd73d9721004bf7459721004bc7459721004be7419721004bd7419721004de7319721004dd7319721004fa7019721004f97019721004de73d9321004dd73d93210047f75593210047c75593210047e75193210047d7519321004de7319321004dd7319321004fa7019321004f97019321006d57198f2100cde7098f2100cdc7058f21005cd72cc721006d6638c721005cf724c721005d7764c721006d7764c721006d4764c721006d7654c721006d5654c721006d7644c721006d5644c721005d7724c721007c7724c721007c4724c721005d4704c721004df7358321004dc7358321006d53158321004be74d9621004bd74d9621004de73d9621004dd73d9621004de7319621004dd73196210047e75d92210047d75d9221004de73d9221004dd73d9221004de7319221004dd731922100cde7098e2100cdc7058e21005d571cca21005d7714ca21005b57494621006d56394621006d56354621005757590621006d56390621006d56350621006d563c8621004df7358221004dc7358221004de73d9521004dd73d9521004bf7459521004bc7459521004de7319521004dd7319521004de73d9121004dd73d91210047f75591210047c7559121004de7319121004dd7319121004f57198d21004dd7298d21006cd7298d21004dd7198d21006d57198d21004d57198d2100cde7098d21004fb7058d21004f87058d21005d87058d21004df7258d21006cf7258d21004df7158d21006d77158d21006db7058d2100cdc7058d21006d87058d21004d87058d21005d571cc921005d7714c921005b57494521006d56394521004f47654521006d56354521005757590521006d56390521004f47650521006d56350521005cd72cc521004df764c521004dd764c521005cf724c521006d563c8521004de73d8121004dd73d81210047e75181210047d7518121004be7418121004bd7418121004de7318121004dd7318121004be74d9421004bd74d9421004de73d9421004dd73d9421004fa70d9421004f970d94210047d76994210047e7519421004be7419421004bd7419421004de7319421004dd7319421004f67119421004fa7019421004f970194210047e75d90210047d75d9021004d
  | 11 => 0x59e74947310059d74947310055e75907310055d7590731004dd72983310055e75183310055d75183310059e74183310059d7418331005ce7218331005cd7218331004be74d9631004bd74d96310047e75d92310047d75d9231005d571cca31006cd624ca31005b57494631005757590631004fa7099531004f97099531004fa7099131004f97099131004de76d4d31005d671d4d31004dc7654d31005d67114d31004de76d0d31005d671d0d31004dc7650d31005d67110d31005d671cc931006cf624c931005d4714c931004de760c931005b57494531005d67394531004f47654531005757590531005d67390531004f476505310047e75181310047d7518131004be7418131004bd7418131004ee7218131004ed7218131005d57199531005da7099531005d97099531005d77159531005d57199131005da7099131005d97099131005d77159131005d671d5131005d571d51310071f5495131005d67195131005d57195131004de7615131004dd76151310071d5415131005ce7215131005cd7215131005d67115131005d57115131005da7015131005d97015131006d571d893100cde70d8931005d57198931005d77158931005db7058931005d87058931005d671d4931005d571d4931004de7694931004dd76949310059f74549310059c7454931005d77154931005d47154931004de7614931004dd76149310059e74149310059d7414931005d67114931005d57114931005da7014931005d97014931005d671d0931005d571d0931004de7690931004dd76909310055f75509310055c7550931005d77150931005d47150931004de7610931004dd76109310055e75109310055d7510931005d67110931005d57110931005da7010931005d97010931005d575d8531005d574d8531005d672d8531005d570d8531004de76945310059e74945310059d7494531007575194531005d67694531006d67694531005d57594531007967494531005d57494531007957494531005957494531005d67294531006d76294531005d57094531005d67654531005d47654531007577554531007576554531007546554531005d77454531007565454531007545454531005d47254531006d76254531007575254531007555254531005d77054531004de7614531005d67114531007555114531004de76905310055e75905310055d7590531005d67690531006d67690531005d77590531007567590531005d57590531007557590531005557590531005d57490531005d67290531006d76290531005d57090531005d67650531005d47650531005d77550531005d57550531007977450531007976450531007946450531007975450531007945450531005d47250531006d76250531007974250531007954250531005d77050531004de7610531005d6711
  | 12 => 0xe7318951004dd7318951004fa7018951004f970189510053c7454951005d571cc9510053e7494551004de73d8151004dd73d8151004dd7298c5100cde7098c51004df7258c5100cdc7058c51004de7398851004dd7398851004df76cc851004dd76cc851005d571cc851004df764c851004dd764c851006d563944510047f7654451004f77654451006d56354451004df7358051004dc7358051004de7319741004dd7319741004ee7219741004ed7219741004fa7019741004f970197410063d6515341005ad7215341005b67115341005b97015341004de7398b41004dd7398b410053c7550b41005d571ccb410047e75983410047d7598341004df7358341004dc7358341004de73d9641004dd73d9641006767199641004de7319641004dd73196410065e6598e410065d6598e41004dd7298e41006d67198e4100cde7098e410065e6558e410065d6558e41004df7258e4100cdc7058e41004de7398a41004dd7398a41004df76cca41004dd76cca410065e65cca410065d65cca41005d571cca41004df764ca41004dd764ca410065e654ca410065d654ca41005d57394641006d56394641006766554641006d563546410063e65d0641004df7358241004dc7358241004de7319541004dd7319541004be76d51410063f65d5141005b671d51410063d6515141005ad7215141005b67115141005b970151410047e75189410047d7518941004de7318941004dd7318941004fa7018941004f970189410053c7550941005d571cc941005b67494541005d57394541004f476545410073454545410053e7590541004de73d8141004dd73d8141004be74d9441004de73d9441004dd73d9441004de7319441004dd7319441004ee7219441004ed7219441004f67119441004fa7019441004f97019441004dd7298c4100cde7098c41004df7258c4100cdc7058c41004de7398841004dd7398841004df76cc841004dd76cc841005d571cc841004df764c841004dd764c8410047e75984410047d7598441006d56390441004bf7650441004f77650441006d56350441004df7358041004dc7358041006cd62ccb31005d571d9731005d57119731005d571d9331005d571193310071f5495331004de7615331004dd76153310071d5415331005ce7215331005cd7215331005d67115331005d57115331005da7015331005d97015331005d571d8b3100cdc7058b31005d57118b31004de7694b31004dd7694b310059f7454b310059c7454b31004de7614b31004dd7614b310059e7414b310059d7414b31005d67114b31005d57114b31005da7014b31005d97014b31004de7690b31004dd7690b310055f7550b310055c7550b31004de7610b31004dd7610b310055e7510b310055d7510b31005d67110b31005d57110b31005da7010b31005d97010b31
  | 13 => 0x8332006d56118332004be7419632004bd7419632004f67119632004f57119632004fa7019632004f970196320047e75192320047d7519232004f67119232004f57119232004fa7019232004f97019232005d571cca32004bf7459532004bc7459532004f67119532004f571195320047f75591320047c7559132004f67119132004f57119132004de76d4d32004dc7654d32005d67114d32005d57114d32004de76d0d32004dc7650d32005d67110d32005d57110d320047e75181320047d7518132004be7418132004bd7418132004f67118132004f57118132005cd72995320059f74595320059c7459532005cf7259532005d67119532005d57119532005cd72991320055f75591320055c7559132005cf7259132005d67119132005d571191320071f5495132004de7615132004dd76151320071d5415132005ce7215132005cd7215132005d67115132005d57115132005da7015132005d97015132005d671d8932005d571d8932007c671d8932007c571d8932005cd70d8932004de76949320059f74549320059c7454932004de76149320059e74149320059d7414932005d67114932005d57114932005da7014932005d97014932004de76909320055f75509320055c7550932004de76109320055e75109320055d7510932005d67110932005d57110932005da7010932005d9701093200cde70d8532005db7058532005d87058532006d56118532005d77158132005d471581320055e75181320055d75181320059e74181320059d7418132005d67118132005d5711813200e5e751813200e5d751813200e9e741813200e9d741813200ed67118132004dd711813200ed57118132004d57118132004de73d9432004be7419432004bd7419432004de7319432004f67119432004f57119432004fa7019432004f97019432004de73d90320047e75190320047d7519032004de7319032004f67119032004f57119032004fa7019032004f97019032006d67198c32006d57198c32005d571cc832004df764c832004ef764c832006ce634c8320063d64153510056d7215351005767115351005797015351004de7398b51004dd7398b510053c7454b51005d571ccb51004be7498351004bd7498351004df7358351004dc7358351006b671992510069e6498e510069d6498e51004dd7298e51006d67198e5100cde7098e510069e6458e510069d6458e51004df7258e5100cdc7058e51004de7398a51004dd7398a51004df76cca51004dd76cca510069e64cca510069d64cca51005d571cca51004df764ca51004dd764ca510069e644ca510069d644ca510063e64d4651004df7358251004dc7358251004de7319151004dd73191510063f64951510057671951510056d7215151005767115151005797015151004be7418951004bd7418951004d
  | 14 => 0x4dd7198c4200cde7098c420065e6558c420065d6558c42004df7158c4200cdc7058c420063d65d08420066d6590842004bf76508420053c75508420063d6550842004ef76508420066d6550842004de7398442004dd7398442006766598442006756598442006d66398442006d56398442006d67398442006d57398442006766558442006756558442006d66358442006d56358442006b75458442006b45458442006d67358442006d57358442006b74258442006b542584420067a6598042006796598042006da6398042006d96398042006f26198042006f1619804200edb739804200ed87398042004df7358042004dc73580420067a6558042006796558042006da6358042006d96358042006f26158042006f16158042006bb5458042006b85458042006db7358042006d87358042006bb4258042006b94258042004be74d9732004bd74d9732004f671d9732004f571d9732004f67119732004f571197320047e75d93320047d75d9332004f671d9332004f571d9332004f67119332004f57119332005ce7214f32005d67114f32005d57114f32005d67110f32005d57110f32006d67358732006d75358732006d65358732006d55358732006d45358732006d74358732006d64358732006d54358732006d443587320059e74d97320059d74d9732005cd72d9732005d671d9732005d571d9732005cd7219732005d67119732005d571197320055e75d93320055d75d9332005cd72d9332005d671d9332005d571d9332005cd7219332005d67119332005d571193320071f5495332004de7615332004dd76153320071d5415332005ce7215332005cd7215332005d67115332005d57115332005da7015332005d970153320059f7454b320059c7454b320059e7414b320059d7414b32005d67114b32005d57114b32005da7014b32005d97014b320055f7550b320055c7550b320055e7510b320055d7510b32005d67110b32005d57110b32005da7010b32005d97010b3200cdc7058732006d77658732006d76558732006d66558732006d56558732006d46558732006d76458732006d66458732006d56458732006d46458732006d77558732006d67558732006d57558732006d47558732006d77458732006d67458732006d57458732006d47458732006d75458732006d65458732006d55458732006d45458732006d57258732006d75258732006d65258732006d55258732006d45258732006d74258732006d64258732006d54258732006d44258732006d77058732006d67058732006d57058732006d47058732006d56118732005d671d8332005d571d8332006d561d8332006d66198332006d56198332004dd7198332006d561583320055e75183320055d75183320059e74183320059d7418332005d67118332005d57118332006d6611
  | 15 => 0x57119152006ba7019152006b970191520047e76d51520063c64d51520063c64551520063c6494952004de7318552004dd7318552004de73d8152004dd73d81520047d76950520063d64950520063d64150520056d72150520069e6498c520069d6498c52004dd7198c5200cde7098c520069e6458c520069d6458c52004df7158c5200cdc7058c520063d64d4852006ad64948520047f76548520053c74548520063d6454852004ef7654852006ad6454852004de7398452004dd7398452006b66498452006b56498452006d66398452006d56398452006d67398452006d57398452006b66458452006b56458452006d66358452006d56358452006765458452006745458452006d67358452006d57358452006775258452006755258452006ba6498052006b96498052006da6398052006d96398052006f26198052006f1619805200edb739805200ed87398052004df7358052004dc7358052006ba6458052006b96458052006da6358052006d96358052006f26158052006f161580520067a5458052006785458052006db7358052006d873580520067b5258052006795258052004de7319742004dd7319742004f67119742004f57119742004fa7019742004f970197420063e65953420063c65553420047e75987420047d7598742004de7398742004dd73987420047e75983420047d7598342004df7358342004dc7358342004de73d9642004dd73d9642004de7319642004dd7319642004f67119642004f57119642004fa7019642004f970196420063d65d5242005ad72d52420063f6515242005ad7215242004f67198e42004f57198e42005d57198e42006d67198e42004dd7198e42006d57198e42004d57198e4200cde7098e42004df7158e4200cdc7058e420072c5494a42005ac7454a420072f5454a42004de7398642004dd7398642004df7358242004dc7358242004f77158242004f471582420047e7599542004bf7459542004de7319542004dd7319542004f67119542004f57119542004fa7019542004f970195420047e76195420063d74195420065e73195420065d73195420066d72195420067671195420067571195420067a7019542006797019542004be76951420063c6595142004bc76551420063c65551420066c65949420072e5494942004ec76549420072d54549420063c6590942004de7318542004dd7318542004de73d8142004dd73d8142004de73d9442004dd73d9442004f671d9442004f571d9442004fa70d9442004f970d94420047d76994420063c74594420047e7519442004be7419442004de7319442004dd7319442004ee7219442004f67119442004f57119442004fa7019442004f97019442004bd76d50420063d65d5042004bd76150420063d6515042005ad72150420065e6598c420065d6598c42
  | 16 => 0x8754004df7358354004dc73583540053d76d52540063d76d5254004de7398a54004dd7398a54004de7398654004dd7398654004df7358254004dc7358254004f67118d54004f57118d54004de7318954004dd7318954004f67118954004f57118954004fa7018954004f97018954004de7318554004dd7318554004de73d8154004dd73d8154004f671d8154004f571d81540053d75950540063e65950540047f7655054004bf76550540053f76550540063f76550540043f76550540053c72550540053f71550540053f70550540071d5498c54004dd7298c54004dd7198c5400cde7098c540071d5458c54004df7258c54004df7158c5400cdc7058c54004de7398854004dd73988540072d5498854006ce6398854006cd6398854006ce7398854006cd73988540063d54588540072d5458854006ce6358854006cd63588540066f5458854006ae54588540066d5458854006ad54588540062d5458854006ce7358854006cd7358854004de7398454004dd7398454007355498454006d66398454006d56398454006e66298454006e56298454006d67398454006d57398454007355458454006d66358454006d56358454006e66258454006e56258454006d67358454006d57358454007395498054006da6398054006d96398054006ea6298054006e96298054006f26198054006f1619805400edb739805400ed87398054004df7358054004dc7358054007395458054006da6358054006d96358054006ea6258054006e96258054006f26158054006f16158054006db7358054006d87358054004be7498353004bd7498353004f67119153004f571191530047f7654c53004df7654c53006d67358453006d65358453006d55358453004ee7219743004ed7219743004f67119743004f57119743004fa7019743004f970197430047e75983430047d7598343004f67119643004f57119643004f67119543004f57119543004dc7654d43004f671d9443004f571d9443004de7319443004ee7219443004ed7219443004f67119443004f57119443004fa7019443004f97019443004bf7650c43004df7650c43006d67358443006d64358443006d543584430063e64d5352004be7498752004bd7498752004de7398752004dd7398752004be7498352004bd7498352004df7358352004dc73583520063d64952520056d72952520056d7215252004f67198e52004f57198e52005d57198e52006d67198e52004dd7198e52006d57198e52004d57198e5200cde7098e52004df7158e5200cdc7058e52004de7398652004dd7398652004df7358252004dc7358252004f77158252004f47158252004de7319152004dd7319152004f67119152004f57119152004fa7019152004f970191520069e73191520069d7319152006ad7219152006b67119152006b
  | 17 => 0xb00000000000300300100000900100200000100600200100200303f00101600100801800e00102f00000d00400700100900000900000001400002a00d00205000700700200600b00001300100000500200400900701c00100400100a01200c00700300b02f00500400500300600100000100400001c00100000000000000200800c01501301200001700100300e00500100300400300200600200001b00000300500400a00300100500600000f00300600b00101800000000800000601801702500800000102000100700200e00b05801c00701800201002100d01600503d01a00100400101100000401200000501400400d00200600300400000700500000400100200405202000a00200e00200d00d02001a00500f01300f00400100100100f00300800300300000d00700000000500400f04401100500100402400800000400000300100300000c00400902800200000000001300300300300a00200002000f04900000401100100000000001004300700100e00000000500100001a00b00000e01b01400402400d00b00c00702700000001b00100500900000201400500d00700800a00a00100101700700701100000100100000100d00300700000000700000500000800901504102500000000400000204002901800f00500b02d00000003200100101500300900101700600f00300000000300002700600800000200000000d02e01400d00a00f06700100201e00100400400f00000005900000001700100100000e00700000300f00100000100100000400100000201800000100000100000800100400600200000d00702d00000000500a01500f01b00400600303f00100000000200600a00405300d00000001900d00000001501000400a00700000000400100b00801104200e00900500400c01400000100000b00000000401300803100000f00000000900000305500500300300101f00000800801200700b00800204f00300200800d00200000000001800502800200200f00300900000d00600a00100800000603000000000700000000000200200200700301a02900500000101700200005c00403200601001000100301e01b00100000600200103702c02900b00601300000800200102a04800100300100000001800003300c00e00502501a01a00200200a00000000600501001a00c00000100401100100000900900800600300600706900f00300200100000000000200000100200400801201500000002d00600700b00000000900200c00200000c00300400000101500901f00000100000102001000000302b00000500e00202700300100000f00100d01601300700700400300a01d00600e02800d00600700900300100200000700301004e00301e00c00a00301e006002004de7398b54004dd7398b54004de7398754004dd739
  | 18 => 0x54a2aa16f11f295814b122487233849f1058140616453a02cb8c6a556b06b10145df00013e4a48953512a2f058a00000000004320004338000000881000216901000000000007fe18e0000000bc69dd5640ed4b2e57e5788000000b12000000117c00002c997d12484d5ac107d1107f02be99f559c7570621b6094e49026680b005a81a1791e1c1fe47d448a0588c68133211690cec84e086abd077e4c647b1a5863626856316d0a923cc4f22654f1c4a936b91dd55c7d756f15dd5665e60a920e8600580348018cd1273e245957d2b23ec2e01bf8a602ac070106100c3e327e0b9840c94822d26c54682501521640e740d84c4199cc48aff2501354174a0644d16056806e8130a0880f43334841ca94005d8191141965a92b0ec91b42403b915f8ec83cc64706690ccf2c31e10f800101c3d0540a30489c97152dac3914861154e000000000008e0e6ce287af402074966e000202155c0002a02fd0000aa600046f926800000014427b06de9041ab28c923e56c12ca4f07e44f62a79744ea0af51d00000000b045589438ae000000026a818430149d9894df608852603240000650000000b988d718980000009fe20a1d14e56b1b2f721ecb366a657313bca9ca234f913780f616f4f1a7d802811e269a4e0a88000480875140e22b13e0000000129000000008e44c122000161a0bd50d82f800000043f24591b01c24cd1a6d39265540e9a30abc38a2fa9a50a008691e40228acc92f2269b65344b1756102850d69c52e7ad295f0132575110c55a4df30c06546d4b3004aa7d511e0030000020000000e700300800b00300901500000200900800100002100000200103b00100000000000b00100100300f00201602902e0150650020000010b300001005101900101d00900000000d02c00900000700000400100000000b01300300a00100501100201500201f00000200300200b00102500300401300500c00000100600000000103902e00601100000101d01200601500700f00701b00001300001400200000101000a00000200000701100100601100000000000100300100601600100602600000200002d00300100100900000100300700000100400300000000400300100300900100000000600003700200001d00300200500900902700000000500100200400f00001900d00000000200000502a00f00000b00300900400600501400f00100300e00300000200000400100800300900301400300000a00c00001400201a01500800200000a00000c00501e00d00500500000000c02e02200600400000f00703400201a02d00200902400600200300400000000000004300004100101400000000f00400f00002500000300000000500100800000e01a00b01200f01802100400100402800200c009002005001001001005000000002000000
  | 19 => 0xa5240a4800015430c80001f258418ca32c89000018509d152690242518e0df2ab50899d115dc0fe59b1140b0600000000000180001f126b963c9b70dc048d21e7112b0000037e3760040cd457c19d2e1abecf4e7ed4570a1d12a0000e001054c445c4c300008800a3187000000093517b1fd00006405010000000925344206019e1903cc81dc00000000012641ca00026b945473a0f70412c74582b3927984150366fc4a284cc0c84270f6a85824ca222fe2324ea86a220d8e6404648c1b40000cac01f36e8000eba26e4b109dc4f272019a1164000263000082c0005290001ec53326341bd93c00008b8117256c35c35332b969800014f3e7016cca6a1c224956c0001f33180000000000045a1d9596a805349c084140000002d344ec58a05a2898d7c4241b89b4d284af716d804836c7e900019cd21400047b9a5c0008823b223c80000000080000b7a4dd000031cb522564d5821c5900000970558f7a57f088094c4ae17c2d00b0137410b5290a9566400002306f4000483000000048e4aa51a9ac03ba00000000002d445f0000780ab20003118ebd0ee4a346b25ad63e22531500005fc3ab2d980012ea4820000174000187000000000020c17a80000003103721e206e65fe1f4030c17200053e2cb872c7250000d40af4adc0a89a0491e40304d28e8cba90b0330dd52c8ab83eea9b087c25100c97a54583f12811304a688db4e682b00a640719622713a09d604f0ec46d8182159800006a3dc03923cc7c0a5337297d13b228552b2b4497e0005a48000c982910a103ccbeea594a00f50cd800016a83c800000000027bd2a09ee2ca800132cab0000159ca8000000000005704ac2f780014ce8211750d700008c000010ec00000053b29555e44c84399f6d0322b952b8edc7ac6ce49e84a8ec63870002bd94bc8e2310a2d000052d56f9024000a11282200d3fe6040198000d2262e0af1088b0475932920a847c5e142c89315889b643e16b812448404480011288573d801e161e2703542600ddc38601d87c90208ef3fbac60bb628c37b213135e3c103e80014b8486355a8b8aea9150fa1d2c2805ec17b89d4fd600006aa314000a8311e91a062a8f85578980a347344ed077007e00006d92555580e80000685518593286843065c17706e2ae92d80d200e9c8548e297001868ce8c3a71ef036568600033d02705c0ae4000000099e5b0200ac649963024630bd0a0200034c01554969db4d4955449e88d54b198c0003bb1f79fc89f6a9b11a23500000003bd89ac50684b26d00001983e13c69ab9088000369181800059d207230c00003727ea48c79e0003ef9cb954860009813100006c90cf8000000947532000000086d0002860c3ab3527919903f60ae00020e0ef400000000001f453b10e03f005409019d000048049d4e627380685b83e8000
  | 20 => 0x33426840001ea2f8000137c6f83651aa8d0a0005a620986c68c4350167129a01e0000000fb40003e299c85960002328000d1431f0000000d8a0544191ec8c9400059792cd08a3bd450079469c08120c9ce0e1c0e1053809043caeb000004cd0430800000004504790fe0b480440000c6105485e0004378a549c46e72381d98390a981f800000008ec15b826c93e866469ab514dc27a53c04e400038e0000f1c0000001740000e386134f6981ca0e2a80000c980145b20630990b84b0a09123b43a60001ba1c004404915070b6528c71d1b023fc39e0003dd24e40000000001bfc0002d106a000000000000008e8000000417115cfce3f80872af55d80004ce938c4ba13f3a12580e2a52f2dca7815a60002409fb035266a17f9f0cbca00025ca8a517e00000026295fa91c00004240b82fa368180854e6f045b0b352886eb34f83b8d80a5821900bc5a86f51290ea86880005198000f82a1700012bc426a030001c24bb227b00029ed10835f0388c105c63eb0000808d667fd55a0a246c200608daa2000011a2bb11503487d40000000f3c11d0e302650be92400000005e67410000ad82dc61a3ce8000c7c39234f0000a0a0005459834dc617229f9e603ec51e5908f14b6e72900000012c677609c1a1915866f1c895404907c91d80e8ca280002e69bf40007ee0000a694d0000000000000015b2c722143384a1307a16c15a5104c99cc4ee875b03e210409c4282e2855c00006b1818000a5042d26708211423a930f820cc2033c209800079a5de455a218df44711708e05626b24222aca95920a430b800022ea3b0002c8088e6c32d29c4147c0000978c5c000b4b32c9f8c47e2ce56e82ac000030137888cadcb334f411613883d1147125166200407da5dcc7227f3b3a7a423225839120483f07a92899ed85e2a2b2d11b200000001508f0c0009bf4b9283400075f1fb06d400081f2499a6800000054ca0f49b05683c90000000000000000000007e0000724be418135ca83000098d04c000000000040100551d63804719cb50a0000527000104e2b200018d55087ef25f10747a64663e5000043000012f079c0005ca35b8fd02cc0000002370ac6516379a2982f4191237837c0009b24fe0fb8000703585a41cb6a69349b102d2f8453243ad48eaa1655609220000ae1327875d24079f1a7800121832a4868e889daa9e0c313712820005702b8960ab4f0c5a570bfe5722730420da817436121e51e2a9734c9b301d20b51cf94610228d01c22d549d83a816ea2a11ba5880c502a1068a2f38b10d1678afc154940d5982153c585290fe83c23080005684c04f0a120f4853803c9e412e800f060809c074aab3f02644c766a72490db81cc56d1328000eca66e430000020c2eb34e259d2f60002d880007923784b28de4d0e3372b109713168b
  | 21 => 0xd52469d251c2abf21829ad0ac34000021b16006a4290800012e39a19404c400045e16629d429846000000014020000bf8388cc4007562800164c5423822014000000240182c00086a44719500004e02eb8c9068c2370000ad472815a588000000091450a000147a16b4b9a52ccf838527d1258ce238b52294e800070716980c54ee00055907e842c80d2661e294da000202a5d919e2b04102030000aa13b897592d00ec33c08c057669200029101ac4422c29eb40001ca00000000000b146100011cab23000253841c00041a98c4a5666000019993ce74c0308e0ceb0000000046065e0514d685414488da302acb087eae55a40000b3e0742cc80002769d53dc18788c48801459854a2e22f12a9978fb80963732750bf615c4e3ad1d30a0a55668754c9cb0c09587c0e6c51d19900005b036600000010a42900df131426c0004b782fcc520325488000fc86c44cda1900009bd0000fb47b067423980004fa2bc4000000efc2c20351d80222000411800150e29d36fa1006b646b407a6253780580ff84a060c4a83f1034011c60311380000009332a90000494af93701f94c1855c23c22a8ff03090ef000064a9bb0bf0d14f562333b62a1809a0004738000f4400005980000008cc3df9e5c0eab460bc9684a8e817354904560259a44396793f213a1f28000000551356267c000645113185050422d23706585c88290821e048b66610002aec10c2213458b5905a40c07b2288dbc5a801327d0c4c2f00928cc47588b14ca05d4e7ea3939b9f8431a71745ba72ce4c55a0cf0000000000000000000000000005b51bc33644f015c2aa000000081400056419e8d5089e1470251cec9a440233d99dcbda0293ff89250dc23c59f8d950123982951504bc074d1338c5025829f0e71ea8bd4a1549a10f461a14e0c1a87456272342a9c9c0000004702a4095c6a157694f40000da4178eb8a6a1124188e700009135051dbc0007ac0000c3c00033b2c795747a455821b8dc009e70c3f880ac2860002db23a01e27f53c18000da2000383000169c33f0000390618a420001f3c4489030b186a0720622046070567474707806cc3c400020b99a4c9070f0000b9c36e2723329ad494c751000000126200000000000000002f419686b21d1067265ca447de0b616b073ca490a214c846278400000002e2320375214450ca1941c9e4cd000490bc1b68000b2209f136492e04502911f870400000000011fa0003d98000dda0c53ec80000005bb16385880000003b69650000ac325dabcc8e89c82b78f651143690c4250c69847f5479eec4e284f50f136cf5c65c1a893915b662d4d40e84c884f11d212c94860391330e200e00dd12daba06902fd4aba11d4fa9b40348d5ce7a61c1db007119a00059a1c7c0c401810480f947e0000001fe80b406d0000cb400091e58190
  | 22 => 0x22933c3ce000039d36689f31921d0de2ad040a00000005690002401676ad54c911a432467902b24410020000000968846aa80262a14f2a0000000000000a9256383bc00000000007f45deb151a4a1c40001b24938f084f000b43414f88f81ba55387a498e85e4e12b294d49290421b8919c93a53a0518e4838c0d0069544e2425a082bc20200d111121559ea504bf0000ddea5f431a25c63aa202208000f502073009e44e583771bea8dd62888c1a5a1246c411509080000004210da15580000003280f5c3be476049a524196a732b088e081e3bc2cc1a34ad415f2e42add2122412b2800028a1af21719f93f63e7000078d5d28bd4b69f5825a21404002a945097f4c7172c00000052a000000000048c9c692a40000000c2cd825ad2230810840000025a9987b423500000000003fc010a91962241013f2608e78498464053565018540f275d46c73236d800000046c5aa0000a3800027a8000ed0a514f80dc8a165483d02698bce2bd0002a80f12b0705d9e3c7ee54500010e8fa20b7157800093c3b40f2049d41eb1a3f422a400008549302e115a1612b8a468f720a90211238a320000001a749d29060651634f0008d5091c0433432951080003b64290280ef906e0003fe2ce09e8a1f54e9aeccb61ef0001de5416341000231c9362110002438bf200000013dd55a0f400000000003521aa800154a4354ae8950eac24300026e498631835685251601800000c1cd2a3c000123f1260b0600000010b000000014cd12010a00000000000000000aa86f838d00013b8ebc00031b10a8f280004e915192dc15336780000000002878000000000573800058c0000071b194de3ad25e80456127a1174a9e49c29ac40e132400037a00000000009ca5519e08122aaa14a1624efa0001090f6c8a23ba3a426d4ff236d317800000042c1d300009a06f70000834ff61d052517402d2a71432a1840006a30002d1408823604e92b49d67b700087b0dacaa206413e0d5e23917697553caaa60001ae800011409a247504847a27500002e0426326939400073031e80011a2ad24a883011762d70002c09308000000000000074a4bc068800000038514240904e7315a22d27e7051fa9df0a403fb0d8017d3067c41c98000b2ca3c0d506f00000a60001b846420173ec16451303b3544a5680000001e31d011a40004a61a116ae03d168149889671308780000005c43bf8000594af03ba9e8c00026229b07a08141894ec0650000ad91fd1a3cd9617d00d9bb068e18438da9fc978b27034255108c32717117ccb9c77801c0ff83328d957182888e41ee2d5a8153e60002291ccc0002102fe838d45ab5017e21e126489600024b496c97007695e41ae0000fb847c7d49690eb1f980dc4fe1a6acf8b5e00049ba224e6a0000000e94d8e63300000591d295532c17895728
  | 23 => 0x11906e4ba640d4889d7116a5a729c83a963852721c06b413e7be577892d10641e30405200ce4d454aa2cd0e001a54705d8c586b11af2398daab513a792c082431c47216f81a626c4d224b15285230b419d439a23b56d13a0bec18f09e98281fa07f0bd96fc53629c3140d28f96198532859145426a3209848ae68f0416134507c0eb25c12dc646389012a598500ad727f886c32645d5a21c211ea10042e162c0405dc12f8df82789a71a1971c96a0003c31d0c0001a736680000d847500000002ba8ea2be277016c2de2dd1cbd412ac03b802c80006b41760000c12b2b0002980a9a4c214980a0f6a99826b14b880c1cb53f041ca225a31519f344527520d885612c297939417e0bba0000000000a6e56b3230a347fa2a200000005ca00022200000000004bd29852360000001ae00001f502020ac000a0441280000004ab145245c00031154d0000f3833e4e7a84d3402cf164a3280789e6385a69466064b14087600006bc31f9f4d3704ba3de0ce48ac0002529ad83f29fa039a28d0f4922081a7a8f8c22c40a83d4f0aafe000132800077335ea294ae87121ca9f300eca1a0e1a52949e0001f49a0d5783f92c62d586ce21a2e09f2156c005000214c78894f48c2968c781da39cac5800051f2988becca20000001790de4000000093416000000000011e863a4e30000f18a4d16fa7ac00035a0301da800061b07c0be4838408000000000000044e9c780005aa258a1d4f680000000d083c221743e99ac856245539000055676b42198392ac1603b911911264a41618f7d1f64b4218a7c43987f65380a982b21c741d9f48656a7a18908013a271904a119c22c9fd2e91094b9283f4fb9d8420404335f87c48aa1fe44d8b70a1075a139aca54ba54c3369ac92bc1a609b8b10e1aa411e58c6948097d3f50fcd164b3d4c08000c4071800005cd132a8a00000000007691368be062ca9f2929d4caf01bb29e24a000041a50400005740bc02f2a340008ee2860e5c000000000000000000010e989c000a8214c270cf84921584241538298c4af8d907c89a3157210938029e177071106052c3b1146d47064345ca67006c22a2bd852d3208284038dfd46098f06890d81bc7d516d12888d491255f0a3c2480092c917ac8948330002788000649554880c53274e37a1b704d21eb1eaa74ca960001f30000edc0001078a100007fe57d1e9968400023d859c71e0000000000eee5f13cd2d4c000a312c319fd3f03583d2a1510e40000e28f740008af3748f291fc68e3f9927060a7c056c1448a1406f50810f106c13533824a83563b847d25a94c69de1b589393607c73cd80002825da10080b800008f123150d64a9df0cda61d0c485d0cb80006ba000000175000058731b800125c0000001
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xcca70588210c0018aceab084218003155d561084300064b3a2c21086000c9574584210c0039a4e0b08421800332589700843000668b0ae01086000cc5629c7500c00198ac4b8ea01800235e1d61d40300046ac3ac3a806000cc5629c7400c00198ac4b8e801800235e1d61d00300046ac3ac3a0060008d5819cf65c80011ab0339ec990003319c97198f20004e2c0eec99640009c9821c131c80017810098e43900067220173487200046ac08e6b2c40008d5811cd64880011a90cb8e649000274604704c920005a4c28e09924000b89841c13248001783023826490002b160873d85200061abaae830a4000c55755cc614800192ae8b98c2900023561f3218520005684026430a4000cd1735c061480014ab0a30a6290002a5610614c520005624326390a40018cc865cd2148001b12e8994a090003525d5329012000c66c14ed18240008d787d84304800198ae5b0860900023561c610c12000662b90c21824000c56655c732080018aacab8e64100032599171cc8200064ab22e39904001ad0805cd61080011ab0f992c210007161c1654c42000e4c382c89884001cd07058531080013a3023826588002a5613654c7100052ac2ec898e20008d68798931c40014ab0a3126388002a5610624c71000ce8402e690e20018cc87589328400192ae9b1ca308003155d763906100046ac3ec610c2000c5575d8c218400192ae9b18430800334d8d7008610005e1c0a6490420008d7815cb63440031a90cb8e64880067420171cc910004e4c10e098a20009e1821c1314400152b09b2a62880023521d654c5100052ac2ec898a20008d48759131440011ad0db92628800235a1e624c5100052ac28c498a2000a9584189314400178304382628800274a18704c51000e69430e098a2001d52851c13144003aa30a382628800334d94704c51000668b28e098a2001d92841c13144003b2308382628800334d90704c51000668b20e098a2001dc2821c131440013a304382628800770608704c510004e0c10e098a2000cd2621c131440019a0c4382628800674201738851000c6a432e690a20019d0805cd21440031ab033b4608800770041720c11000ce843a6310220009d0874c520440019a0ec98a4088002f060d214811000d64402e6b102000a65851c5620400154b0838ac4080023560576cc8100062b32ae39902000c55655c7320400192cc8b8e64080032559171cc81000663312e39902000cc5625c732040031b100bb26408007321c1624c8100046ac36e29902000cc562dc5320400192ae8b1ca208003295d162944100062abaac72082000c657558a41040018aaeab184208003255d1630841000632baac41082000ca57458821040019a2c6b80420800338589700841000d68402c68802001ec03058910040015a30d98a2008003b058b3144010
  | 1 => 0xf0eaa0a9180034355172152300046bc0aed29460008d7815da428c0014ab0239aca18007868c165590300054ac08e6b2060008d5869c4530c0011ab0d3888618007928c1655883000f45182c8b106000ac6819cd620c00158b0339ac418002b1a04535883000562c08a6b106001aca8014d620c00158d0221ac418002b1604435883000d6540086b1060008d5869c7320c00198ac538e64180031599571cc8300062ab2ae39906000c96645c7320c00192ac8b8e64180033158971cc8300046ac3e653086001ec230589610c0035a500192c218007329c1620c4300048fc3aa82a06000c1d76550540c00119b0d390a8180034355172150300046ac34e22a06000a8f845d5620c00151908baac418002a3a10755883000546c20eab106000ac6811d5620c00158b023aac418006b2a00755883000527c2ae8b106000a4c855d1620c00149d0a3a2c41800293614745883000563408e8b106000ac5811d1620c003595003a2c41800383d52545883000467438a8b1060008cd87151620c001c1aa82a2c418002b1a04545883000562c08a8b106001aca80151620c001593002a2c418006b2201715883000527428e2b106000a4d851c5620c00151d0838ac418002a3610715883000d65400e2b10600089d861d1520c00191ee8b12a418003231d16254830006473a2c42906000c8d74588520c003994e0b10a4180023561a711483000662b14e22906000cc5625c4520c001992c4b80a41800217618755083000627baac4a106000c4c75589420c00189ceab108418003135d5621083000e65382c421060008d5869c4420c00198ac5388841800331589711083000664b12e02106000a9684dd5610c00152b09baac218006b4a0275584300052b42ee8b086000a5585dd1610c0035a5013a2c21800385d5254584300046b438a8b0860008d587151610c001c2aa82a2c218002b1a08545843000562c10a8b086001ad280151610c0015a3002a2c218006b420172584300052b428e4b086000a55851c9610c00152d08392c218002a5610725843000d69400e4b086000a9784549610c00152908a92c21800235a1c52584300046ac38a4b086000a9684149610c00152b08292c218006b4a00525843000568c00a4b086000a5785509610c0014a90aa12c21800235a1c42584300046ac3884b086000a5685109610c0014ab0a212c218006b4a00425843000568c0084b086001cca7058b510c001992c4b86a2180033458570d4430006473a2c52886000c8d7458a510c00192ce8b0ca218003255d1619443000e65382c5a086000cc9625c3410c0019a2c2b868218003139d5629043000626baac52086000c5675586410c0018aaeab0c82180033258b704843000668b0ee09086000c4e75588210c00189aeab104218003239d1620843000646ba2c41086001
  | 2 => 0x85450531005c8c00a8a0a6200955851c9414c4013a3003928298802c52154250531004aac2ce220a6200cc7815c8604c40198902b90c09880732941721813100e65202e43026201cc7105c8604c40399420b90c0988073144172181310054ac24a23026200cc572944604c4015a301288c098803315c951181310052ac2c823026200cc572904604c4015a301208c098803315c941181310054bc22ca98e4200a578559131c84011ab0c382639080271608704c7210064aba2c728c4200c557558e41884011ab0339eca908023560673d912100669b88e0b1a4201c5a851c163484038b30a382c69080726a107058d2100e4cc20e0b1a4201cc9821c163484039a302382c690803255d1639452100568402c728a4200ad08058d51484018aaeab1c8290802b4201639052100568402c6a0a4200ad08058f21484018accab8e64108031559571cc8210064b322e39904200c95645c7320840152b09b2a6210802b4603654c4210052ac34ca9884200c577659531084014ab0bb226210802b4603644c4210054ac34c89884200e1565991310840192eecb22621080385995644c4210070ab2ac89884200c5565dc9310840192ac9b92621080315594704c4210064ab20e098842009c5821c131084018aacab9c42108032559173884210046bc32e69084200c55655cd210840192ac8b9a421080274201734842100728b2a633004200e91644c660084015a303994c010802b4201315802100569c3262b004200e52654c56008401ca2ca98ac010803a4991315802100748b2262b004200ad181cc960084015a10e98ac010802b4e0931580210076098e42b004200ad18388560084015a30690ac0108030b59172153500046ac0ee4b1ea0008d5819ce62d40011ab03bb665a800235e1971ccb500064aba2e730ea0008d587cca61d40014cb042a2c3a80028d21152587500046ac3e64b0ea000a958498531d40018aeeca8a63a8002356067398a500064b322e3994a000c95645c73294003930e0b226328007341c1614c6500046bc0ae5b1aa0008d5811db32540011ab023b264a8003151d9514c550004e4c10e098aa000d51511c131540011ab0339cc4280030b59572153400046ac0ee4b1e80008d5819ce62d00011ab03bb665a000235e1971ccb400062abaae730e80008d587cca61d000154b042a2c3a00028d21542587400046ac3e64b0e8000a558598531d000192eeca0a63a0002356067398a400062b32ae39948000c55655c732900038b0e0b2a6320007341c1614c6400046ac08e6b2a800083f87594545000185acab90a8a000235e0572d8d400046ac08ed99280008d5811d93250001928eca0a62a000272608704c540006c8a08e098a8000b19831515050001653042a2a0a0002cc60454541400046ac0ce73108001cd070585318c00123
  | 3 => 0x9300a800e295458a601500119b0439ac02a0023560473580540051dc32a8b00a800e195458d6015001c52a8b12c02a0038c551615805400564c10e6b00a800ad1811cd60150011ab0239ac1a9003295c971191520064cb9ae0322a400ca9725c06454801962e2b80c8a90023560673d815200532c10a8b08a400a348454961148011ab0239ac0290029a608545805200568c08e6b00a400a3884549601480107d0e32aa9a10023560473583420046ac0ce7b2c840083d87d94549080185ecab90a9210024ba1f5454a4200616ba2e432a8400c65725c465508018b2e6b80caa10031a5c9701954200638b8ae032a8400a2e869525250801858ecaa2a4a10023560673d814200616b2ae42a0840083c87595421080154b042a2c2210028d21542584420046ac08e6b008400aa98215160108015a30239ac0210028e21542580420046ac34e229e64008d5869c443cc8011ab033b0a99900247e1d541533200686aa2e42a664008d5869c454cc80152d09b2ac399002a561365587320052b42ec8b0e6400a5585d9161cc80152d09baac399002a5613755873200569404eab0e6400ad1809d561cc8014ad0bba2c39900295617745873200569404e8b0e6400ad1809d161cc801c2ea92a2c39900235a1c54587320046ac38a8b0e6400e155415161cc80158d042a2c399002b1608545873200569400a8b0e6400ad18015161cc8015a700b92c399002b420172587320054bc22a4b0e6400a948454961cc80152d08292c399002a5610525873200569400a4b0e6400ad18014961cc8014af0aa12c3990029521542587320052b42884b0e6400a558510961cc8015a500212c399002b460042587320052b428e0b0e6400a55851c161cc80152d08382c399002a5610705873200562c10e0b0e6400cd1701c161cc8011ab0f308c199003159d561183320062abaac23066400c967458460cc80192ae8b08c19900247e1d541513200686aa2e42a264008d5819da524c8011ab033b48499002b4201611853200e63902e23026401cd2205c4604c80398a40b88c0990030b59172153510064b322e3994a200c95645c7329440185acab90a9a08031599571cca410062ab2ae3994820083f87594545040185acab90a8a0802c9608545454100598c00a8a8a820091f8755054cc401a1aa8b90a99880247e1d541513100686aa2e42a26200995849c7524c4031b100bb4a4988025561671d093100c6c402ed21262008d587d8a514c40192ae9b14a298802c5a1375545310068bba4a8a8a6200a5686151514c40168b042a2a298802d46005454531004cac20e4a8a62009d1801c9514c40162908a92a29880255e1d51145310046ac3ec520a6200c5575d8a414c40162d0bba2829880265a1f54505310068bbaea8a0a6200a9686151414c401a2aea2a28298802e160
  | 4 => 0x5720c000000000b700088c668003fa0009d8004524fcdd0b53701044c821350000000004547d87d1c90005d0bd81e0247b4001ea170318b983f0006e400000000000fa8000000001e01c3a6001011974140000000036a741088fe36e280da000000000000002346b8000000002a51a017000000000000d2000701e81ea78c001c3000000b100000081c001be470000fd1d212a000069e6354628bb0000305191387e18670434240486678040aa3d26a45e9354240b10f8c0476608e298d2e2198e6a2507a4c8641633266510482d34a37c1d0353de7c0531d915e8383e00017491c00000000000f0073000000bc02e01615cff0f120c09119800168460000000004b80295a00060468800000000f60003461ac318002a21d8e71a7378000c78560003f0000000000241f0002b0425098003946ec001e127c3cc000002c8910770a72225a0918f023a820b81343ba654000160a2000001eb0f653c000300000000002f0007b8650003c84ac000824024a8008000f0000000000000000015b24c3600003b00000032853278068000fd0003fc001cc04a000200000000000015c000000ab1c6290000002150b84b4eb0ec00043c6a00e0e261cf29b6094000519de3186800001f40a4f4e5960158684f9136044600cb0bf1ac67c4f88a4340000000000000000000000000000be000000768000008c81009d0008f8868001ae0003e85a0aa2c5228a12a6428c2836000618000000000006214e3fe4100023624a47000000062238002222ce0011400044c000920f60003acb697f1d20180004c0100c0000803058030040602c0100c1300c00000020080200804004020040003001030040000000c140000101c0300006024020000a0180001400000170180501c040140200c02014030200003000000010040100800010000180302400004030200100001000000000f010110000500401048030000201002000050100600001000000200000001000030000701c05000100000201000000140000200000010060980600804000060000901402000000140b024010080000003020030040200802004000080300000000000000000c000040501004000010000100003004080140200801004020000200800008000046ac0ce7316a8008d5811cd60d50011ab0339cc52a0023560473582540041ec3ccb2a0a800935811c9541500127300392a82a0024d60770550540050fc32a9318a800a1f8655163150011ab03b92c62a00235606739885400517c32a9310a800ac5819ce621500145904aa2c42a0028be19545885400706aa4c6b10a800e0d5458d62150014590eaa2c42a0028be05545885400517c02a8b10a800e0d549cd621500158b0339ac42a0038355173588540051bc32a9308a800e255458a611500146f0caa2c22a0038955162584540051dc32a
  | 5 => 0x2a0e20f73561b4001612be8bc99800428000001d8000000911903ae001109f435a674a20c24161247a000128500078c908a8b84b9cf0d80001c9ac1606c0590001344e8598da23e768aa800364000459af45a1e40000034800006000000000000422d61dcaa1414582950b0062065a4321d10044e083862210064241df0000000000018a8909c8440000001196a000000000000540004f1281bc24cbb8003ee8651e0840006251a83429436ccda3a4002b42300a096000c18cf4720000ea3f2ae4a4020611f68782601040c3904688500000077852284384000000b0770000002de1c00023d0005b80388c0520000000046e1d4000000000004e1432264784800000000000000000001080f90006cc000000860000004719849c00060000224d89c71aa0001301b0007880016533287009a0f33486c000dd09c26cbd00000017c000004820003d17e2b20007c0002323941c1211c60dc00000000648808281445f4198001243640a00000062c0a8001cc698000000002600016c18e179210002000007394b2a02182806a00009ccc0111a4134be1371c41b88117519c2ecb30000b2574019d40000000010e1820008590c42e258000003f27e000000000340de8913aa000001fc20a514f88b622c0ac8b8002406200000038446c419c01a676c7921d2f2000002201d419ca49fb26232c400e80b60c88914d0001bc001720ba2208a98417280c000000002f00012c1b88605200031c51c00000102440af0873e60000019c3441c90200022879c3a0ab00013c000000a87211812f0000004795248c00000000298834c89bf0004c1158000fe8c4
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x19000022114000003c003850018e9c0048d800004000003c00000507000001100000002a16340002c01409527ca83009530048086002061000260139a0044ba3100014205000008502004020008012259120954588540048a6408255162150012259121d54588540048a64087551621500122591e01545885400681551819cd6215001217985505458732006815518215161cc8018c1825c0705873200445e6175151414c40190575608545053100511654815c8604c4014859420572181310062161172944604c4018c17260251181310061161572904604c4018c1726024118131006245d08058e514840185175201639052100611595821c1310840188564608704c42100614594805cd2108401891642017348421004b0648874c5600840194182544704c55000660609411c1315000120f9855054588300060361d54151620c0012179855054584300068155182151610c0011c19720131c872000524653651c1314400145195d90704c51000630259821c131440018c365608704c51000630595821c131440018c364608704c51000630591821c131440018c182988704c51000434660621c1314400145195188704c51000524650621c131440031c09760d2148110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x305000050834a4b3043826288002881a4259821c13144001440d26cac10e098a2000a1069764608704c510
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
  | 7 => packedAt gbK7 (1870+((h/22+packedAt gbK7 (1716+(h % 22)*7) 7) % 105)*8) 8
  | 6 => packedAt gbK6 (67710+((h/555+packedAt gbK6 (61605+(h % 555)*11) 11) % 1999)*12) 12
  | 5 => packedAt gbK5 (151056+((h/968+packedAt gbK5 (139440+(h % 968)*12) 12) % 3487)*13) 13
  | 4 => packedAt gbK4 (36396+((h/194+packedAt gbK4 (34456+(h % 194)*10) 10) % 848)*11) 11
  | 3 => packedAt gbK3 (3108+((h/14+packedAt gbK3 (3010+(h % 14)*7) 7) % 74)*7) 7
  | 2 => packedAt gbK2 (327+((h/1+packedAt gbK2 (324+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3ff0e0f870ffc383f07fffe0ffc0c1d31d33cf
  | 1 => 0x3c3f00ff80f0fc03ff8f80ff0ff30923923d33
  | 2 => 0xc03fff0fff00fffc3ff000fff0000e3ce3ce3c
  | 3 => 0xffc0000fffff00003fffff00003c0fc0fc0fc0
  | 4 => 0xfffffffffc0000000003ff000fff000
  | 5 => 0xfffffff00000000000000000003fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x8502410202140904010a820c500c051051045
  | 1 => 0x162908aa8858a4229c8d025a0ab30922922512
  | 2 => 0x40024201110009082120048420000204204a28
  | 3 => 0xa688128dda9a204a3e4e560620bc0f80f80f80
  | 4 => 0xe6cecf2730404180843155000dfb000
  | 5 => 0x3b3c9cc000000000080860108c2aadfb000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xfffffaf8faf8eae8fffffaf8faf8eae8fffffaf8faf8eae8fffffaf8faf8eae8fffffaf8faf8eae8fffffaf8faf8eae8fffffaf8faf8eae8fffffaf8faf8eae8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_14208
namespace PEqualNP.Outside.L_meta_14208
open PEqualNP.Outside.L_meta_14208.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 4 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 32, 48),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 4 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 4 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 4 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 4, 20)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) SB) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 2 zero,inputs.getD 6 zero,inputs.getD 7 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero,inputs.getD 1 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xfffffefefefeeeeefffffefefefeeeeefffffefefefeeeeefffffaf8faf8eae8fffffefefefeeeeefffffefefefeeeeefffffefefefeeeeefffffaf8faf8eae8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 11 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) SB :=
    slice_correct (ms:=fixRows 9 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
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
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_14208.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,6]⟩,⟨.and,[8,7]⟩,⟨.or,[0,1]⟩,⟨.or,[10,2]⟩,⟨.or,[6,7]⟩,⟨.and,[11,12]⟩,⟨.or,[0,4]⟩,⟨.and,[14,5]⟩,⟨.and,[0,4]⟩,⟨.or,[9,13]⟩,⟨.or,[17,15]⟩,⟨.or,[18,16]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,19⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 11) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_14208

open PEqualNP.Outside.L_meta_14208 in
theorem PEqualNP.Outside.L_meta_14208 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 0, 7, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
