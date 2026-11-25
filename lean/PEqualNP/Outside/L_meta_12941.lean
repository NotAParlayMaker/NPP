import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12941.Model
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


end PEqualNP.Outside.L_meta_12941.Model

namespace PEqualNP.Outside.L_meta_12941
open PEqualNP.Outside.L_meta_12941.Model
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

def SB : Nat := 7

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

end PEqualNP.Outside.L_meta_12941

namespace PEqualNP.Outside.L_meta_12941
open PEqualNP.Outside.L_meta_12941.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x841fe41083fa82107f10420ff98841fe31083fa62107f0c420ff90841fe21083dc42107f48420fe10841ec21082fca0107fd0020ff20041fd40083f880107fcc020ff18041fd30083f860107fc8020f790041fe20083f440107f48020f690041f920083fea9885fd5310ff2a6217e54c43faa9885f55310fe2a6217c54c43fea7885fd4f10ff29e217e53c43faa7885f54f10fe29e217c53c43fe87887f90f10fea1e21fc43c43fea5885fd4b10ff296217e52c43faa5885f54b10fe296217c52c43fe85887f90b10fea1621fc42c43fe65887f8cb10fe99621fc32c43fe83887f90710fea0e21fc41c43fe63887f8c710fe98e21fc31c43fe43887f88710fe90e21fc21c43fe81887f90310fea0621fc40c43fe61887f8c310fe98621fc30c43fe41887f88310fe90621fc20c43fea9085fd5210ff2a4217e54843faa9085f55210fe2a4217c54843fea7085fd4e10ff29c217e53843faa7085f54e10fe29c217c53843fe87087f90e10fea1c21fc43843fea5085fd4a10ff294217e52843faa5085f54a10fe294217c52843fe85087f90a10fea1421fc42843fe65087f8ca10fe99421fc32842faa3087fd0610ff20c21fd41843f883087fcc610ff18c21fd31843f863087fc8610fb90c21fe21843fa43087f08610fa10c217e50843fe81087f90210fea0421fc40843fe61087f8c210fe98421fc30843fe41087f88210fe90421fc20843fe21087dc4210fd88421ff54442fea8886fd51109faa221fe54442fca8887f55110beaa221fc54442f8a8886f151109e2a221ff53442fea68877d4d10afa9a21fe53442fca6887f54d10bea9a21fc53442f8a6887714d10ae29a21ff43443fc86887f50d10fe21a21ff52442fea4887bd4910b7a9221fe52442fca4887f54910bea9221fc52442f8a4887b14910b629221ff42443fc84887f50910fe21221ff32443fc64887f4c910fe19221ff41443fc82887f50510fe20a21ff31443fc62887f4c510fe18a21ff21443fc42887f48510fe10a21ff40443fc80887f50110fe20221ff30443fc60887f4c110fe18221ff20443fc40887f48110fe10221ff10443f620887f84110fb08221ff54042fea8087f95010bf2a021fd54042faa8087f15010be2a021ff53042fea6087f94c10bf29821fd53042faa6087f14c10be29821ff43043fc86087f50c10fe21821ff52042fea4087f94810bf29021fd52042faa4087f14810be29021ff42043fc84087f50810fe21021ff32043fc64087f4c810fe190217e51043fe82087f90410fea0821fc41043fe62087f8c410fe98821fc31043fe42087dc8410ff10821fd21043f842087d08410bf28021ff40043fc80087f50010fe20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xf414c3fc82987f50530fe20a61ff314c3fc62987f4c530fe18a61ff214c3fc42987f48530fe10a61ff404c3fc80987f50130fe20261ff304c3f660987f8c130ef18261ff540c2fea8187f95030bf2a061fd540c2faa8187f15030be2a0617e530c3fe86187f90c30ef21861fd430c3ba86187f10c30ffa9061fe520c2fca4187f54830bea9061fc520c3fe84187f90830fea1061fc420c3fe64187f8c830ef19061fd320c3f86418770c830ffa8861fe510c2fca2187f54430bea8861fc510c3fe82187f90430fea0861fc410c3fe62187f8c430ef18861fd310c3f86218770c430ff90861fe210c3fa42187f08430bf28061ff400c3fc80187f50030fe20061ff300c3be60187f8c030fd18061fd300c3ba60187e4c030ffaa6417f54c83fca9905f95320feaa6417d54c83f8a9905f15320ffa9e417f53c83fca7905f94f20fea9e417d53c83f8a7905f14f20ffa1e41fe43c83fa87907f10f20ffa1641fe42c83fa85907f10b20ff99641fe32c83fa65907f0cb20ffa8e41fe51c82fca3907f54720bea8e41fc51c83fe83907f90720fea0e41fc41c83fe63907f8c720fe98e41fc31c83fe43907f88720fe90e41fc21c83fe81907f90320fea0641fc40c83fe61907f8c320fe98641fc30c83fea9105fd5220ff2a4417e54883faa9105f55220fe2a4417c54883fea7105fd4e20ff29c417e53883faa7105f54e20fe29c417c53883fe87107f90e20fea1c41fc43882faa5107fd0a20ff21441fd42883f885107fcca20ff19441fd32883f865107fd4620ff28c417e51883faa3105f54620fe28c41ff41883fc83107f50620fe20c41ff31883fc63107f4c620fe18c41ff21883fc43107b88620fe90c41fc21883d843105f94220ffa0441fe40883fa81107f10220ff98441fe30883fa61107f0c220ff90441ef20883f641107fd5120bfaa241bf544827ea8907f95120bf2a241fd54482faa8907f15120be2a241bc5448278a8907fd4d20bfa9a41df53482bea6907f94d20bf29a41fd53482faa6907f14d20be29a41dc53482b8a6907fd0d20ff21a41fd43483f886907fd0920ff21241fd42483f884907fcc920ff19241fd32483f864907fd4520bfa8a41f751482eea2907f94520fea8a41fc51482f8a2907d14520ba28a41ff41483fc82907f50520fe20a41ff31483fc62907f4c520fe18a41ff21483fc42907f48520fe10a41ff40483fc80907f50120fe20241ff30483fc60907f4c120fe18241ff20483f640907f88120f710241ff54082fea8107f95020bf2a041fd54082faa8107f15020be2a041ff53082fea6107f94c20bf29841fd53082faa6107f14c20be29841ff43083fc86107f50c20fe218417e52083fe84107f90820fea1041fc42083fe64107f8c820fe99041fc32083fea2107f94420bf28841fd51082faa2107f14420ffa0
  | 2 => 0x3fe43a07f88740fe90e81fc21d02faa9207fd4e40ff29c817e53903faa7205f54e40fe29c81ff439037e87207f90e40fea1c81bd43903f887207fd4a40ff294817e52903faa5205f54a40fe29481ff42903fc85206f90a40fea1481fc429037885207fcca40ff19481fd32903f865207fd4640ff28c817e51903faa3205f54640fe28c81ff41903fc83206f90640fea0c81fc419037883207fcc640ff18c81fd31903f863207fc8640ff10c81fd21903f843205f94240ffa0481bf40903f681207fd4d40bfa9a81fe53503faa6a07f14d40be29a81ff43503fc86a07f50d40fe21a81ff52502fea4a07f94940fea9281fc52502f8a4a07fd0940ff21281fd42503f884a07fcc940ff19281fd32503f864a07fd4540bfa8a81fe51503faa2a07f14540be28a81ff41503fc82a07f50540fe20a81ff31503fc62a07f4c540fe18a81ff21503fc42a07f48540fe10a81ff40503f680a07f90140df202817e54103fea6207f94c40bf29881fd53102faa6207f14c40ffa1881bf43103fc86207f50c40dea1881fc43103fea4207f94840bf29081fd52102faa4207f14840ffa1081fe421037c84207f50840fe21081bc42103fe64207f8c840fe99081fc32103fea2207f94440bf28881fd51102faa2207f14440ffa0881fe411037c82207f50440fe20881bc41103fe62207f8c440fe98881fc31103fe42207f88440fe90881fc21102fca0207fd0040dfa0081fe40103f480207f50040dea0081f940103fea9985fd5330ff2a6617e54cc37ca9984f95330feaa6617d54cc37aa9984f55330fe2a6617c54cc3fe87987f90f30fea1e61fc43cc3fea5987f94b30bf29661fd52cc2faa5987f14b30ffa1661fe42cc3fa85987f10b30ff99661fe32cc3fa65987f0cb30ffa8e61fe51cc2fca3987f54730bea8e61fc51cc3fe83987f90730fea0e61fc41cc3fe63987f8c730fe98e61fc31cc3fe43987f88730fe90e61fc21cc3fe81987f90330fea0661fc40cc3fea9185fd5230ff2a4617e548c3faa9185f55230fe2a4617c548c2faa7187fd0e30ff21c61de438c3fa87187750e30fe21c61ff528c3fca5185f94a30fea94617d528c3f8a5187fd0a30ff21461fd428c3f885187fcca30ff19461de328c3fa65187f0ca30ee19461ff518c3fca3185f94630fea8c617d518c3f8a3187fd0630ff20c61fd418c3f883187fcc630ff18c61de318c3fa63187f0c630ee18c61ff218c3fc43187f48630fe10c617e508c3fe81187f90230fea0461fc408c3fe611877cc230fd98461ff544c2fea8987f95130bf2a261fd544c2faa8987f15130be2a261ff434c3fc86987f50d30fe21a61ff524c2fea4987f94930fea9261fc524c2f8a4987fd0930ff21261fd424c3f884987fcc930ff19261fd324c3f864987fd4530bfa8a61fe514c3faa2987f14530be28a61f
  | 3 => 0xa498ff54931fe292637c524c7fe8498ff90931fea1263fc424c7fe6498ff8c931fe99263fc324c7fe8298ff90531fea0a63fc414c7fe6298fdcc531ff18a63de314c7fea098dfd4131ff28263fd504c7f8a098df14131ffaa0637f540c7fca818df95031df2a0633e540c7faa818df55031deaa0633d540c7f8a818df15031bf29863ff430c7fc8618ff50c31fe21863ff520c7fca418df94831fea90637d520c7f8a418ffd0831ff21063fd420c7f88418ffcc831ff19063fd320c7f86418df94431ffa0863fe410c7fa8218ff10431ff98863df310c7fc6218fd8c431fe98863dd310c7ea6218ffd4031ff280637e500c7faa018df54031fe28063ff54c86fea990ff95321bf2a643fd54c86faa990ff15321be2a643ff53c86fea790ff94f21bf29e43fd53c86faa790ff14f21be29e43ff43c87fc8790ff50f21fe21e43ff42c87fc8590ff50b21fe21643ff32c87fc6590ff4cb21fe19643ff41c87fc8390ff50721fe20e43ff31c87fc6390ff4c721fe18e43ff50c87fca190df94321fea86437d50c87f8a190ffd5221bfaa443fe54886fca910ff55221beaa443fc54886f8a910ffd4e21bfa9c43fe53886fca710ff54e21bea9c43fc53886f8a710ffd0e21ff21c43fd43887f88710df54a21ffa1443fe42887fa8510ff10a21ff99443fe32887fa6510ff0ca21bf28c43ff41887fc8310ff50621fe20c43ff31887fc6310ff4c621fe18c43ff21887de4310fdc8621ffa8443fe50886fca110ff54221bea8443fc50887fea890dfd5121ff2a2437e54487faa890df55121fe2a2437c54487fea690dfd4d21ff29a437e53487faa690df54d21fe29a437c53487fe8690ff90d21fea1a43fc43487fe8490ff90921fea1243fc42487fe6490ff8c921fe99243fc32487fe8290ff90521fea0a43fc41487fe6290ff8c521fe98a43fc31487fe4290fdc8521ff10a43ee21487fea090dfd4121ff28243fd50487f8a090df14121ffaa0437f54087fca810df95021feaa0437d54087f8a810df15021ffa98437f53087fca610df94c21fea98437d53087f8a610df14c21ffa1843fe43087fa8610ff10c21bf29043ff42087fc8410ff50821fe21043ff32087fc6410ff4c821fe190437e51087fe8210ff90421fea0843fc41087fe6210ff8c421fe98843fc31087fe4210fbc8421ff10843f621087fa4210fb48421fa90843e521087fea010ff94021bf28043fd50086faa010ff14021ffa9e81fe53d02fca7a07794f40af29e81fd53d02faa7a07754f40aea9e81fc53d03fe87a07f90f40fea1e81fc43d03fea5a07f94b40bf29681fd52d02faa5a07f14b40ffa1681fe42d03fa85a07f10b40ff99681fe32d03fa65a07f0cb40ffa8e81fe51d02fca3a07f54740bea8e81fc51d03fe83a07f90740fea0e81fc41d03fe63a07f8c740fe98e81fc31d
  | 4 => 0x7f10d32ffa1265fe424cbfa84997f10932ff99265ef324cbfc6499778c932ffa8a657f514cbfca2997f54532fe28a657c514cbfea0995fd4132ff28265fd504cbf8a0995f14132ffaa0657f540cbfca8195f95032df2a0653e540cbfaa8195f55032deaa0653d540cbf8a8195f15032bf29865ff430cbfc86197f50c32fe218657e520cbfe84197f90832fea1065fc420cbfe641977cc832ff19065ee320cbfa6419774c832f699065ff510cbfca2195f94432fea88657d510cbf8a2197fd4032ff280657e500cbfaa0195f54032fe28065ff53d07fca7a0df94f41fea9e837d53d07f8a7a0ffd0f41dfa1e83fe43d07fa87a0ef50f41fe21e83ff52d07fca5a0df94b41fea96837d52d07f8a5a0ffd0b41ff21683fd42d07f885a0ffccb41ff19683fd32d07f865a0ffd4341ff286837e50d07faa1a0df54341fe286837d54907fea720ff94e41bf29c83fd53906faa720ff14e41ffa1c83fe43907fa8720ff10e41ffa9483fe52906fca520ff54a41bea9483fc52907fe8520ff90a41fea1483fc42907fe6520ff8ca41fe99483fc32906fca320ffd0641dfa0c83f741907fea120ff94241bf28483fd50906faa120ff14241ffa9a837f53507fca6a0ff54d41fe29a837c53507fe86a0efd0d41ff21a83fd435077a86a0ff10d41ffa92837f52507fca4a0ff54941fe292837c52507fe84a0ff90941fea1283fc42507fe64a0ff8c941fe99283fc32507fe82a0fdd0541ff20a83be41507fea0a0dfd4141ff28283fd50507f8a0a0df14141bf2a083ff53107fca620df94c41ef298835e53107faa620df54c41eea98835d53107f8a620ffd0c41ff21883fd43107f88620ffd4841ff290837e52107faa420df54841fe29083ff42107fc8420ff50841fe21083ff32107fc6420ff4c841fe190837e51107fe8220efd0441ff20883f641107fa8220ef50441faa0883ff50107fca020df94041fea80837d50107f8a020ffd5331bfaa663fe54cc6fca998ff55331beaa663fc54cc6f8a998ffd0f31ff21e63de43cc7fa8798f750f31fe21e63ff52cc7fca598df94b31fea96637d52cc7f8a598ffd0b31ff21663fd42cc7f88598ffccb31ff19663fd32cc7f86598ffd0731ff20e63fd41cc7f88398ffd4331ff286637e50cc7faa198df54331fe28663ff548c6fea918ff95231bf2a463fd548c6faa918ff15231be2a4637d538c7fe8718ff90e31fea1c63fc438c7fea518ff94a31bf29463fd528c6faa518ff14a31ffa1463fe428c7fa8518ff10a31ff99463fe328c7fa6518ff0ca31bf28c63ff418c7fc8318ff50631fe20c63ff318c7be6318fdcc631ffa8463fe508c6fca118ff54231bea8463fc508c7fea898dfd5131ff2a2637e544c7faa898df55131fe2a2637c544c7fe8698ff90d31ef21a63fd434c7ba8698ff10d31ffa92637f524c7fc
  | 5 => 0x3c00000000000c00005400400000000001403c00401801000000402c01001803c00803c05000001400000000000401801c00000001400000400801801000001801000000000c00401c00000bfea5a1ff94b43bf29687fd52d0efaa5a1ff14b43ffa8e87fe51d0efca3a1ff54743bea8e87fc51d0ffea1a1ff94343bf28687fd50d0efaa1a1ff14343beaa4877e5390ffe8721efd0e43efa1c87ff5290ffca521df94a43fea94877d5290ff8a521ffd4643ff28c877e5190ffaa321df54643fe28c87ff5090ffca121df94243fea84877d5090ff8a121ffd0d43efa1a87fe4350f7c86a1ffd4943bfa9287fe5250ffaa4a1ff14943be29287ff5150efea2a1ff94543fea8a87fc5150ef8a2a1ffd4143bfa8287fe5050ffaa0a1ff14143be282877e5410efca621ffd0c43dfa1887fe4310fbc8621ff50c43dea1887dd4310f3a8621ffd4843ff290877e5210ffaa421df54843fe29087ff5110ffca221df94443fea88877d5110ff8a221ffd4043ff280877e5010ffaa021df54043fe28087ff53d0bfca7a15f94f42fea9e857d53d0bf8a7a17fd0f42dfa1e85fe43d0bfa87a16f50f42fe21e85ff51d0bfca3a15f94742fea8e857d51d0bf8a3a17fd4342ff286857e50d0bfaa1a15f54342fe286857d5490bfea7217f94e42bf29c85fd5390afaa7217f14e42ffa1c85fe4390bfa87217f10e42bf29485ff4290b7e85217bd0a42ffa8c85fe5190afca3217f54642bea8c85fc5190bfea1217f94242bf28485fd5090afaa1217f14242ffa9a857f5350bfca6a17f54d42fe29a857c5350bfe86a16fd0d42ff21a85fd4350b7a86a17f10d42ffa1285ef4250bfc84a16f90942ffa8a857f5150bfca2a17f54542fe28a857c5150bfea0a15fd4142ff28285fd5050bf8a0a15f14142bf2a085ff5310bfca6215f94c42ef298855e5310bfaa6215f54c42eea98855d5310bf8a6217fd0c42ff21885fd4310bf886215f94842ffa1085bf4210bfc84217b90842fea1085bd4210bda84217fd4442ff288857e5110bfaa2215f54442fe28885ff5010bfca0215f94042fea80857d5010bf8a0217fd5332bfaa665fe54ccafca9997f55332beaa665fc54ccaf8a9997fd0f32ff21e65de43ccbfa87997750f32fe21e65ff42ccbfc85997f50b32fe21665ff51ccbfca3995f94732fea8e657d51ccbf8a3997fd4332ff286657e50ccbfaa1995f54332fe28665ff548cafea9197f95232bf2a465fd548cafaa9197f15232be2a4657d538cbfe87197f90e32fea1c65fc438cafca5197fd0a32ff21465fd428cbf885197fcca32ef99465ef328cbfea3197f94632bf28c65fd518cafaa3197f14632ffa8465fe508cafca1197f54232bea8465fc508cbfea8995fd5132ff2a2657e544cbfaa8995f55132fe2a2657c544cbfe86997f90d32ef21a65fd434cbba8699
  | 6 => 0x8c0000002e7808aa633d1ad2f30fe05086d0101eb0b09fe23d0001c936228222e2cfb258428871cca4135ab6e34713f9aeb0b1e28e298c99a827994335982a0001e21514112034428c81296016e259b711a818f3448003808000df94e0c3a8700000008c86da7aa260002438000398ea80400014f0000b019f9448002bf988b7080000001080000022d9380281fe95fa558b1b6f0070e6000241b3c0000ae28900020a86293a8888000000f1a9e25d81e8000cc96100015d80036c19b0a721e000330800000224800000400c00000402c00402403c04802803002c01402000006c02800000000000c00000400c01c00400000000800000400401000003000401400000400000404c00000800000001001000403000800000400404000c00800000c0240c800000401001401003000000000c00000400000c01000c00c00002000801c0000000380140200280080080b801402000c00005803000c00000800000c01000001c00000000c00000000801c00408c00404402800000400400000000000000000c00801407c00000000801401005001800000400400000000401c00000000401c04400000400403c00007c01401000000000400404000000001400801000800402803400800000003000001803400c00c00000803403402803802c00000403c06c00c00001800405c01c01800800000801c00400000005001c00c00c00400400400802001801800400000000000801c01c00000407800000000000000401400000800003000401c00400000c00000c01400000400002c00404c0d001400000000002000000003c00003400400000c00c01000800002c01400400002800000c00000000000c00401800801c00000800400400c03802000401c01000400400000c00800003001401003801405804000402800000800000c05c00400c00800003800000802802801400c01002c00800803405001800c01405800800803800000800800400001400800001000401800000800000c00000001801400000001002c00000000000001801803801000000003402801000808800400000c01c01c00000000c0000380280040040040000000a800000400c02c03400001800000000000400400001403c00000400c06405000000000401c01001c01004805000401403400000c00400800001400001000000c06400800000400400003401801803400c00001c00001404c01002801800400801000003800400802000000000000000000400000001000400403000000400000c00002000402400c00000800000000000400000400800803404c09c00005001800800000c00000804c01801c00000400002000c01000000400c00800001c0040000a000000801001c00400c00003000000c00006001800400000001c01800003400401401802c0280000340040000
  | 7 => 0x490001ee21b8b800032c00023119115002181f8eb83f3432c500000316caeb0000718000000001cea3c15a093000343a8780c0001fa07322e8002ec2ad80000028880120400002c06fb5e8d701aa7800006080019180000000000000000000003900000002d91d00000000000005d02a1c824a9a680397d99e0920000000002548001141a38a20f71070000000eeb36adb0cd0001570940001f6a5908f00000023b9b29008000000000003120002ee0002068000562f8b8223a00030bae580000000033e8b6a7e8000002f522221f8002519b7a1203b13b8000000002bc00000000000013f0000003588002ac9ab02110b0002b40002848002a2a9a8000ae80025fa070b491327691dada8001b322a34f80017b348b67a3e2ba1fba67aa815e3508fd80d8002711640000002050e026887e1e78000490bb80022f80000018823000029b9822638fb23d8da8c70d51980002cb9691a31292e18db8000003768003100e899ba931878000000001422eba52b1a9e18001499c08b5356a9e8359922e10ad000017800347a69800218800120874a6600013000180005c964b329549e08001dc80036a2c4af98422991ba13e14f82f33111a05427a00a8000002a9800000000289a183021728000000002298000000b90002018000ac9409958000869e30142db8002f614a095b8002224680013b02027e2322f70002df2d38000000dd121986a6c0f60002450000000138001a1135a0100000036b0000001db9f48f3ae087b88ba3680000017a8ff2750000000002448002ed275a950001a080037d1252fa87c0d68000fc8fc1a78000001d91dd800303ab728e3200000002200000cda179d680000013213101d9e21542e3059b3528b87a800103a9626a25e8c690f9d10e0a56aa735b1da175911a34102800099200863072b399cb00003500000000000035100000002d06501337537c8558a3aa392120a1bf11e0ce2fcaef27c26bae735c11f23ab69230a4420fac689e84c9719f58001a013d0f334c106000000000000000000093800207b2b12e0002c017200000027283e2900000000000e70000000002a596c0b8a0590b92280000000030180035b80013994d0000000003458002880c413a1e48002789b0a1d8ce800000000000136a9c1902d200004d000000000036800077b4111b91127da8580016eb3b34d930a831c997900000000013781818100000034a90680000003219c00025ca6485e8002f81b69f20000001d5000237a82abb0000000740001d5800228225b6604d8d18002f02a537729412d89b8a2b5d02e86c98633e1750a60e3a721de9b4a762b3b11b2332a979a1486aac1adfb191ad9390438270adb599d20001713403220660fd00015500015d2a1867ab68cb095101ab28ba98180016800014aacaad580034b2a30000002ac217000
  | 8 => 0x2ae68000000000000000002b205a0000362d92c8a351a4a5a9eea969ea1558001848e7908a94863a2915684bb61805b1e17a10c9c4084193b3d8658cf11b0002c60b392aa1f36b9e9931b810580ba0f5b2535510e80004e90a0002d021d1659bd9a9163279844800000124b238cc00000000032c80033fa361ce1d40000000c58000a7a74000015a0980000000000000600012a00033c8000003638b780013cb01064000290af907000004e00007623f12b948ae8aa42c707c9c612800035d8000000d4000000261a8134682a8309c0000000316249125ac300019d0000781e9099b792a00002b7b5398400018fb79ae50973000c183288f890aa6b582e91c5a0e0091f818c2f186b81c31422f3081c7195266965076a6b0a894c9892fe10303f95caffafba399022e206ea998c2ac10260000f289c313afa2c42c814b8bf8002b08000290002d71f30000c921c0313758002d98000000002d300000004a24797000015b88a00000980035f99c8ca2ba800000066a8b00021900000037b09786e00002388e0000b981680013881b36800016780000037a18aa048001af157a318a40000e4110b030288000000000cbade2580000e6b129b59dd2f5a4b2921a7014afc2023780f500037e80015c03794b0000002ca00000031980008da2c2c58002458371bd25a14c00024e2719a1800180000000331b0080000000000000000012d37d8000001a50002a92501d30e5b130b200018e0fba28a8f18d2af00008115b0002dc00000037c34e8000002588c50d01e62e3961a338000110000000f08000002e42140001ac8000000830dcb420000002e98003170002bd9c8892a650588160440000000001f119db418e9b629b98a321a9011de34c91621b00031b14680f9e8ad80c88d991a8d21f00000d49d78002fd9b904f0bd0879fdabd00012423b0af8c10c984090db051a897f8000001f600020629584780024080005915f01999a2c0905a0301a1e698b043251069b20a03a6e804b048000d3a4a1a580033f0002499908001361a6046acd1f88f880000005328a16ab6c8bc8d5851add0d080000033228da1380000016d12b03a00000034d15600000028396a31d2cc94397782080000000000000010e0000000001b80f200036f8000002bcb72104994b4a253a7700232b9fd2ae9510528829a2a2533400f1b5221b383829171d1b6680000030c06f0c487d017054b2e30435780015084f9cc24019995a8000689c68000000000000000000000000000001db0000770b70002dcb3b9f298e8bc02985f1100000000000000000001f7000000000000000000031acc0891698eb1332e4a9f00000000000000000000000000000008e8002158720c08000000002d8ab535e00021000000031fa8509b3738dc35200024e80027d00025082c9e027f12ca6a8003
  | 9 => 0x242ad2d6aa2351a8624fa4db348a906221182f9cfa9a000145235996afb29d8862f2b280000003462550001c28003429af80b32fa5784b00026c89600001c8000ff8f40000000bb0ee29b32480030d9bc80030d28d00000000d00007b2601fb0080000988002cb19603800000026126f0000001688000d636700000000000000024c0000000000001979220f90000b280031e80020b9dc081aef800210945a5323800000000000000000032d8000ab02280026426d1621b220c10a8000003181121e58000da08394e8000f48002561cb9239eb8ec8250db0002b580008000035f0000550913148e834bb530000000000002571ec2ab91827300000000000017e9da8000001ecadd83cad486b1478d303d8ab8000000002d6356128aab000115b3612ea808002790ec377800000337041000112825b500df3302b98a0b269091f797685f8003698480002b88000000001b600030a00032733a1338de9051f380000000021300000029f800000000000000208800226b719e50000ac3818520001870470003090000001271ab80000000031f0001ca10829824800034812f1c392305b8002fd0a580e9cf2aab742c980030c9fc8000000000000001ef07380028e8001c200000031ba4200023f90405b2978002c780025d0c819911c26587d8a989f02e1bc0003158001ca800189a6234e0af3168001260de0003728000000001aa00015e80017cae280000005d80030f17709480000008a80000000001d00000028a9c100000000022bac3a0e8498000000000000fe8001370000000002209528710000000002198000000001ba953abe2ed9433688001be00025e176000142b08800000000000360a7b21105a8002970000798001f182b80030e00011c913b059ed0231738c024c8a6a0c85e3700000150000000002029c183413eae60792671f0b22ad4337a093099709589748918bd9a200ca460000001fa98a32f000185800000374a1e800227ac92cd96b03389daa100021c80031a2deb2780008800019700000022706a00032906734f0000000000000000a48aa80000000035595809d27797e0002f2153333000000000000000000216a6e1930000000c79b18ed0f68000001518002a78000000000f002481b8000789d71c33659be8f810000000009a9bf8000e32c20002d0a609e39660120c60002aa2b82e8359239286a12ac292f8d10458001a40d89ff833000307000307b17a471cd0000bf0b425b93db54a0dab3000180a0f00024331d90980017319f09c889b2132ea48aa88002ae0dd9bb80000e0003529639168500be9fc07ea5b1d88000001d9ad18aa183b6316f97435a16f0051b13408ef8c211523e857b262d29aa998a211471178d918b8ed8ea2918000f135c8cfa9390d1078001278001268850000c32330f780014900000028413
  | 10 => 0x5c08d0000000001403642f68002989e80e50000822910708069442ea0002d1159aa48000000002542229ac000000000000315306ae0364ad50001d600014602b37f2f48001e40b60ca941ab01d38a510f00000000000022d0000002b11ef8000000690000d80000002f40001d80000e92bf000090114ada1d48ef24d0463730189b400037e360270b3aaecb1c8001e70000e116d8000002cf0faa238000e180024f0000001df18303e9f912c167080a7018da7fa5f0fa1b00000000000648000000001cdb7a80000037fb7880285130a87a03d00005700011eb02a1a15929280036a8002ff08590c0000a1800000281978aeea6d8008002f3b241c48610348002630a10002f0838861b4506829caa0919a8c00000027b84c0000b329d0000001c78000000d789e2520000000000001b888480011900000028020b17f1f416280027c92980000027480000026f80031c0000000e480000000000000000000000000000000000003a8f980000037b9352ea8002b60000000000b5b650000000450000001852afb572ce8002f7b3923894836e856b0fb28b2d1b39bb1348000000002682be8000000002738000758001ae0d28000002372692629c5000354333a2301f22a87f17c1d0800166848a5c3299188a80300982b90003062160002b18001d280007f80000000000006c06031100037600030e8be00022c80023c83bb188001f500000009680036103c1d000020817b807826b6d19280000016bace20d0e20b12328001e11ff36da2400001184009f89a1342d797d349afea2b0a008b17800024280016084a93c24b9ed800041a3480000000011fb10a8f99e8000002b49a99f9b218750190001b71df80000b80a05394dabb9523389ea8002f100032a
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x5320427c654c810d794d320435d534c810db949320436d524c810bdd8532042f4614c810bed8132042f8604c8109fd94320427e650c8109f594320427c650c810af99032042bd640c8109f992510427d64944109f98e510427d63944109f98a510427d62944109f597410427f65904109f596410433e5490410cf55241042fa6090410be582410427f65504109fd94410427d6510410cf950410433d5410410b798c41042dd6310410be98041042f960104109f597310427f658c4109f596310435e538c410d754e31042fa608c410be582310427f654c4109fd94310427d650c410af99031042bd640c410d794c310435d530c410be98031042f9600c4109f59721042f565c8410dd597210437752c8410dd54b21042f560c84109fd96210427d6588410db94a210436d5288410bd98621042fa6088410be582210427f65484109fd94210427d6508410db948210436d5208410f948421042fa6008410be580210437565084109d59421042f66208410f998821043775208410f994821043755208410f954821043655208410fc98021042f56008410fc58021042f160084109f992500427d64940109f98e500427d63940109f98a500427d62940109f58650043772194010dd086500427d65d0010b798f40042dd63d00109fd96400427d6590010cf952400433d5490010bd98640042f561900109fd95400427f65100109f994400427d65100109f194400433e5410010cf55040042f66110010bd584400427d65cc010af99330042bd64cc0109fd96300427d658c010d794e300435d538c010bd98630042f5618c0109fd95300427f650c0109f994300427d650c0109f194300435e530c010d754c30042f6610c010bd584300427d65c80109fd96200427d6588010db94a200436d5288010bd98620042f56188010f9086200427f6548010afd9120042bc6448010b7d8d20042dc6348010bdd8520042f461480109fd94200427e65080109f594200427c6508010db948200436d5208010bd98420042f56108010f9084200437565c4010bd98b10042f462c4010bd58610043765184010be596100437965840109e59610042f96184010de94610043f25184010fcc8610043f021840109fd9510042bf6444010af19110042df6344010b718d10042ef6244010bb18910042f76544010ddd9510042776544010edd9110043b46444010f5d8d10043d46344010f9d8910042f66244010bd18910043e46244010b918910042f76044010dd94110043f34044010fc10110043f33044010fc0c110043f22044010fc48110042fb6544010ded95100427b6544010eed9110043b86444010f6d8d10043d86344010fad8910043e86244010bed8510043f36144010de94510043f25144010fcd0510043f04144010fccc510043f03144010fc88510043f12144010
  | 1 => 0x427d63d50109f98b540427d62d50109f987540437661d50109f983540437a60d50109f596540433f54950109f98e540427d63950109f98a540427d6295010cfd91540427f63550109f18d540427f62550109f189540427f61550109f585540427f60550109f581540433d5415010b798c54042dd6315010bb98854042ed62150109f990540433e64150109f98c540435e63150109798c540427d6315010d758c540425d63150109f988540436e62150109b988540427d6215010db588540426d62150109f984540437661150109f980540437a60150109f993530427d64d4c109f98b530427d62d4c109f987530437661d4c109f983530437a60d4c109f596530435f5394c109f992530427d6494c109f98a530427d6294c109fd91530427c6454c10d7d8d530427f6254c109f189530427f6154c109f585530427f6054c109f58153042be6414c10af590530435d5314c10bb98853042ed6214c109f990530433e6414c108f990530427d6414c10cf590530423d6414c109f98c530435e6314c109f988530436e6214c109b988530427d6214c10db588530426d6214c109f98453043766114c109f980530437a6014c109fd97430427e65d0c109f597430427c65d0c10cf953430433d54d0c109fd96430427e6590c109f596430427c6590c10d794e430435d5390c109fd95430427e6550c109f595430427c6550c10cf951430433d5450c10d794d430435d5350c10bdd8543042f46150c10bed8143042f86050c109fd94430427e6510c109f594430427c6510c10e750c430427e64d48109f593520427e63d48109f58f520427e61d4810dd987520427e60d4810de983520427d6594810dbd4a520427e64948109f592520427e63948109f58e520427f64548109f191520427f63548109f18d520436f62548109fd85520427d6154810dd185520427f60548109f58152042be6414810af59052042de6314810b758c520436d52148109f990520433e64148108f990520427d6414810cf590520423d64148109f98c520435e63148109798c520427d6314810d758c520425d63148109f988520436e62148109f984520437661148109f980520437a60148109fd97420427e65d08109f597420427c65d0810cf953420433d54d0810bd98742042f561d08109fd96420427e65908109f596420427c6590810db94a420436d52908109fd95420427e65508109f595420427c6550810cf951420433d5450810db949420436d5250810bdd8542042f46150810bed8142042f860508109fd94420427e65108109f594420427c6510810b798c42042dd63108109fd97320427e65cc8109f597320427c65cc810d794f320435d53cc810bd98732042f561cc8109fd96320427e658c8109f596320427c658c810db94a320436d528c8109fd95320427e654c8109f59
  | 2 => 0x5410510b798c41442dd6310510d7d4c414435c5310510dbd48414436c5210510ed504414427e65cc510cfd53314433c54cc510d7d4f314435c53cc510dbd4b314436c52cc510be98331442f960cc5109f996314433f548c510cf152314435f538c510d714e314436f528c510db14a314427c654c510cfd51314433c544c510d7d4d314435c534c510dbd49314436c524c510bed8131442f8604c5109f99431442be640c510af590314433f540c510cf150314435f530c510d714c314436f520c510db14831443d5310c5109f997214433f54c8510cf153214435f53c8510d714f214436f52c8510db14b21442fa60c8510be583214427e6588510cfd52214433c5488510d7d4e214435c5388510dbd4a214436c52885109f195214433f5448510cf151214435f5348510d714d214436f5248510db14921442fb6048510be181214427e6508510cfd50214433c5408510d7d4c214435c5308510dbd48214436c5208510f9484214427e65d0110cfd53404433c54d0110b798f40442dd63d0110d7d4f404435c53d0110dbd4b404436c52d0110bd98740442f561d01109f996404433f5490110cf152404435f5390110d714e404436f5290110db14a404427f65501109f595404427c6550110cfd51404433c5450110d7d4d404435c5350110dbd49404436c5250110bdd8540442f461501109f994404433f5410110cf150404435f5310110d714c404436f5210110db148404427e65cc110af99330442bd64cc110cfd53304433c54cc110d7d4f304435c53cc110dbd4b304436c52cc110bd98730442f561cc1109f996304433f548c110cf152304435f538c110d714e304436f528c110db14a304427f654c1109f595304427c654c110cfd51304433c544c110d7d4d304435c534c110dbd49304436c524c110bdd8530442f4614c1109f994304433f540c110cf150304435f530c110d714c304436f520c110db148304427e65c8110cfd53204433c54c8110d7d4f204435c53c8110dbd4b204436c52c8110bd98720442f561c81109f996204433f5488110cf152204435f5388110d714e204436f5288110db14a204427f65481109f595204427c6548110afd9120442bc6448110cfd51204433c5448110b7d8d20442dc6348110d7d4d204435c5348110dbd49204436c5248110bdd8520442f461481109f994204433f5408110cf150204435f5308110d714c204436f5208110db14820443e92008110cfd53104433c54c4110d7d4f104435c53c4110dbd4b104436c52c4110eed5310443b854c4110f6d4f10443d853c4110fad4b10443e852c4110cfd52104433c5484110d7d4e104435c5384110dbd4a104436c5284110edd5210443b45484110f5d4e10443d45384110f9d4a10443765284110dd14a10443e45284110d914a10443f350841109f98f540
  | 3 => 0x910dbd4a524427e6494910cf992524423e64949109f592524433d64949108f592524427e6394910d798e524425e63949109f58e524435d63949109758e524427e62949109b98a524427d6194910dd586524427d6094910de58252442bf6454910af191524433f5454910cf15152442df6354910b718d524435f5354910d714d524427f6454910cfd91524423f64549109f191524433c64549108f191524427f6354910d7d8d524425f63549109f18d524435c63549109718d524436f62549109fd85524437761549109dd85524427f6054910ded81524427e6514910cfd50524433c5414910d7d4c524435c5314910db548524427e64149109f590524427e63149109f58c524436e62149109f984524427c61149109f980524427c6014910bb994524436e65149109b994524436f5414910ebd50524432f5414910db950524436d5414910db15052443ac5414910cb150524436f5314910f3d4c524434f5314910db94c524436d5314910db14c52443cc5314910d314c524436f6414910db990524436d6414910db190524436f6314910db98c524436d6314910db18c524436f4314910db90c524436d4314910db10c524436f6114910db584524436f6014910db580524436d10149109fd97424427e65d09109f597424427c65d0910cfd53424433c54d0910d7d4f424435c53d0910dbd4b424436c52d09109fd96424427e65909109f596424427c6590910cfd52424433c5490910d7d4e424435c5390910dbd4a424436c52909109fd95424427e65509109f595424427c6550910cfd51424433c5450910d7d4d424435c5350910dbd49424436c52509109fd94424427e65109109f594424427c6510910cfd50424433c5410910b798c42442dd6310910d7d4c424435c5310910dbd48424436c5210910bd98442442f56110910be98042442f960109109fd97324427e65cc9109f597324427c65cc910cfd53324433c54cc910d7d4f324435c53cc910dbd4b324436c52cc9109fd96324427e658c9109f596324427c658c910cfd52324433c548c910d7d4e324435c538c910dbd4a324436c528c9109fd95324427e654c9109f595324427c654c910cfd51324433c544c910d7d4d324435c534c910dbd49324436c524c9109fd94324427e650c9109f594324427c650c910af99032442bd640c910cfd50324433c540c910d7d4c324435c530c910dbd48324436c520c910bd98432442f5610c910be98032442f9600c9109f997414433f54d0510cf153414435f53d0510d714f414436f52d0510db14b41442fa60d0510be583414427e6590510cfd52414433c5490510d7d4e414435c5390510dbd4a414436c52905109f195414433f5450510cf151414435f5350510d714d414436f5250510db14941442fb6050510be181414427e6510510cfd50414433c
  | 4 => 0xf988544427d62151109f984544427c61151109f980544427c6015110af994544433e65151108f994544433f6315110cf98c544433d6315110cf18c544433f6215110cf988544433d6215110cf188544433f6115110cf584544433f6015110cf580544433d1015110cfd53534433c54d4d109f993534427d64d4d109f98b534427d62d4d10d7d53534439f54d4d10c7d53534435e54d4d10d7553534435c54d4d10e7153534431c54d4d10d7d93534435e64d4d10d7593534435c64d4d10d7d8b534435e62d4d10d758b534435c62d4d10d7d87534435d61d4d10d7d83534435d60d4d10af99253442bd6494d10cfd52534433c5494d10d7d4e53442ee6294d10bb58a534427e6494d10cf992534423e6494d109f592534433d6494d108f592534427e6394d109798e534427e6294d10db98a534426e6294d109f58a534436d6294d109b58a534427d6194d10dd586534427d6094d10de58253442bf6454d10af191534433f5454d10cf15153442ef6254d10bb189534427f6454d10cfd91534423f6454d109f191534433c6454d108f191534435f6354d109fd89534436f6254d109bd89534427c6254d10db189534426c6254d109fd8553443776154d109fd81534437b6054d109f994534433f5414d10cf150534435d5314d109f990534427d6414d10d798c534427e6214d109f588534427e6114d109f184534427e6014d109f18053442de6514d10d7994534425e6514d10d7d50534439f5414d10c7d50534435e5414d10d7550534435c5414d10e7150534431c5414d10d7d90534435e6414d10d7590534435c6414d10d7d88534435e6214d10d7588534435c6214d10d7d84534435d6114d10d7d80534435d6014d10d7440534427f65d0d109f997434427d65d0d109f197434433f54d0d10cf153434435f53d0d10d714f434427f6590d109f996434427d6590d109f196434433f5490d10cf152434435f5390d10d714e434427f6550d109f995434427d6550d109f195434433f5450d10cf151434435f5350d10d714d434427f6510d109f994434427d6510d109f194434433f5410d10cf150434435f5310d10d714c434439d4310d10bd98443442f56110d10cfd53524433c54d4910d7d4f524435c53d49109f993524427d64d49109f98f524427d63d4910dbd5352443af54d4910cbd53524436e54d4910db553524436c54d4910eb153524432c54d4910dbd4f52443cf53d4910d3d4f524436e53d4910db54f524436c53d4910f314f524434c53d4910dbd93524436e64d4910db593524436c64d4910dbd8f524436e63d4910db58f524436c63d4910dbd0f524436e43d4910db50f524436c43d4910dbd87524436d61d4910dbd83524436d60d4910af99252442bd6494910cfd52524433c5494910b798e52442dd6394910d7d4e524435c5394
  | 5 => 0x528437a6014a109fd97428427e65d0a109f597428427c65d0a10bd98742842f561d0a109fd96428427e6590a109f596428427c6590a109fd95428427e6550a109f595428427c6550a10bdd8542842f46150a109fd94428427e6510a109f594428427c6510a10b798c42842dd6310a10be98042842f96010a109fd97328427e65cca109f597328427c65cca10bd98732842f561cca109fd96328427e658ca109f596328427c658ca109fd95328427e654ca109f595328427c654ca10bdd8532842f4614ca109fd94328427e650ca109f594328427c650ca10af99032842bd640ca10be98032842f9600ca10cf953418433d54d0610be98341842f960d0610cfd52418433c5490610cf951418433d5450610bed8141842f86050610cfd50418433c5410610b798c41842dd6310610d794f318435d53cc610be98331842f960cc610d7d4e318435c538c610d794d318435d534c610bed8131842f8604c610af99031842bd640c610d7d4c318435c530c610db94b218436d52c8610be98321842f960c8610dd597218437752c8610f994b218437552c8610f954b21843f260c8610bd58321843f160c8610dbd4a218436c5288610db949218436d5248610bed8121842f86048610dbd48218436c5208610f948421842f56508610dd59421843e66208610ddd4821843e75208610d9d4821843755208610f914821842f56008610b798f40842dd63d0210cf952408433d5490210bd98640842f56190210cf950408433d5410210bd98440842f56110210af99330842bd64cc210d794e308435d538c210bd98630842f5618c210d794c308435d530c210bd98430842f5610c210db94a208436d5288210bd98620842f56188210f908620842bf6448210af19120842df6348210b718d20842f76148210bd185208436e5208210db54820842f66108210bd58420843e42108210fa48020842f565c4210dd59710842f662c4210bd18b10842f965c4210de597108427e63d51109f58f544427e62d51109f58b544433f63d5110cf98f544433d63d5110cf18f544433f62d5110cf98b544433d62d5110cf18b544433f61d5110cf587544433f60d5110cf583544433f5495110b798e54442dd6395110bb98a54442ed62951109f992544423e64951109f98e544435e63951109798e544427d6395110d758e544425d63951109f98a544436e62951109b98a544427d6295110db58a544426d62951109f586544437561951109f58254443796095110b7d8d54442dc6355110bbd8954442ec6255110cfd91544427f6355110d7d8d544425f63551109f18d544435c63551109718d544427f6255110dbd89544426f62551109f189544436c62551109b189544427f6155110ddd85544427f6055110ded81544427e6515110cf550544433e64151109f98c544427d63151109
  | 6 => 0x2de6310b10b758c42c42f66110b10bd58442c427f65ccb109f99732c427d65ccb109f19732c427f658cb109f99632c427d658cb109f19632c435e538cb10d754e32c427f654cb109f99532c427d654cb109f19532c42fb604cb10be18132c427f650cb109f99432c427d650cb109f19432c42be640cb10af59032c435e530cb10d754c32c42f6610cb10bd58432c433e5490710cf55241c42fa6090710be58241c433e5410710cf55041c42de6310710b758c41c43b54110710be98041c42f96010710d794e31c435d538c710be98231c42f9608c710af99031c42bd640c710d794c31c435d530c710f54c431c42fa600c710be58031c436e5288710db54a21c42fa6088710be58221c436e5208710db54821c43e52108710be98021c42f96008710cf95340c433d54d0310b798f40c42dd63d0310bd98740c42f561d0310cfd5240c433c5490310cf95140c433d5450310bdd8540c42f46150310cfd5040c433c5410310af99330c42bd64cc310d794f30c435d53cc310bd98730c42f561cc310d7d4e30c435c538c310d794d30c435d534c310bdd8530c42f4614c310d7d4c30c435c530c310db94b20c436d52c8310bd98720c42f561c8310dbd4a20c436c5288310afd9120c42bc6448310b7d8d20c42dc6348310db94920c436d5248310bdd8520c42f46148310dbd4820c436c52083109f98f548427d63d52109f98b548427d62d5210dd587548437a60d5210cfd5254842de6395210b758e548427e6395210d798e548425e63952109f58e548435d63952109758e548427e62952109f58a548433f64552109fd8d548427c63552109fd89548427c6255210cf550548433e64152109f98c548427d63152109f988548427d6215210dd584548437a60152109f993538427d64d4e109f98b538427d62d4e10dd587538437a60d4e10af99253842bd6494e10d7d4e538427e6494e10cf992538423e6494e109f592538433d6494e108f592538427e6294e109f58a538427f6454e109f191538435f6354e109fd89538427c6254e10d754c538427e6414e109f590538435e6314e109f988538427d6214e10dd584538437a6014e109fd97438427e65d0e109f597438427c65d0e10cfd53438433c54d0e109fd96438427e6590e109f596438427c6590e10d7d4e438435c5390e109fd95438427e6550e109f595438427c6550e10cfd51438433c5450e10d7d4d438435c5350e10bdd8543842f46150e109fd94438427e6510e109f594438427c6510e10e750c438427e64d4a109f593528427e63d4a109f58f528437561d4a10de983528436f5294a109f992528427d6494a109f98e528427d6394a109fd91528427c6454a109fd8d528427c6354a10dbd8952843776154a10db548528427e6414a109f590528427e6314a109f58c528436e6214a10dd584
  | 7 => 0x5cc020af99330082bd64cc0209fd96300827d658c020d794e300835d538c020bb98a30082ed628c0209fd95300827f650c0209f994300827d650c0209f194300835e530c020d754c30082ee620c020bb58830082ee61c8020bb58a200836e5288020be58a200837a5288020fa94a20083ea2188020fa086200827f6548020afd9120082bc6448020b7d8d20082dc6348020bdd8520082f46148020bbd95200836f65480209bd9520083af6448020eb19120083cf6348020f318d20083e76148020bb18520083e46148020b918520082ef6048020db94120083eb4048020fa10120083eb3048020fa0c120082fb6548020ded95200827b6548020eed9120083b86448020f6d8d20083d86348020bed8920083eb6248020de94920083ea5248020fad0920083e84248020facc920083e83248020fcd8520083f06148020fac8520083e921480209f98f54c427d63d53109f98b54c427d62d5310dd98754c437960d5310cfd5254c427e63953109f58e54c427e62953109f58a54c433f64553109fd8d54c427c63553109fd8954c427c6255310cf55054c42de6315310b758c54c433e64153109f98c54c435e63153109798c54c427d6315310d758c54c425d63153109f98854c427d6215310dd98454c437960153109f99353c427d64d4f109f98b53c427d62d4f10dd98753c437960d4f10d7d4e53c427e6494f109f59253c427e6294f109f58a53c427f6454f109f19153c435f6354f109fd8953c427c6254f10af99053c42bd6414f10d754c53c427e6414f10cf99053c423e6414f109f59053c433d6414f108f59053c435e6314f109f98853c427d6214f10dd98453c43796014f109fd9743c427e65d0f109f59743c427c65d0f10cf95343c433d54d0f109fd9643c427e6590f109f59643c427c6590f10d794e43c435d5390f109fd9543c427e6550f109f59543c427c6550f10cf95143c433d5450f10d794d43c435d5350f10bed8143c42f86050f109fd9443c427e6510f109f59443c427c6510f10e750c43c42f66110f10bd58443c42be64d4b10af59352c42de63d4b10b758f52c427e64d4b10cf99352c423e64d4b109f59352c433d64d4b108f59352c427e63d4b10d798f52c425e63d4b109f58f52c435d63d4b109758f52c437661d4b10de58352c436f5294b109f99252c427d6494b109f98e52c427d6394b109fd9152c427c6454b109fd8d52c427c6354b10dbd8952c436d5214b109f99052c427d6414b109f98c52c427d6314b10db98852c43766114b10de58052c427f65d0b109f99742c427d65d0b109f19742c427f6590b109f99642c427d6590b109f19642c433e5490b10cf55242c427f6550b109f99542c427d6550b109f19542c42fb6050b10be18142c427f6510b109f99442c427d6510b109f19442c433e5410b10cf55042c4
  | 8 => 0x209fd91530827c6454c20d7d8d530827f6254c209f589530827f6154c209f18553082be6414c20af590530835d5314c20bd98453082f56114c209f990530833e6414c208f990530827d6414c20cf590530823d6414c209f98c530835e6314c209f988530836e6214c209f98453083766114c209d984530827d6114c20dd58453082756114c209f980530837a6014c209fd97430827e65d0c209f597430827c65d0c20cf953430833d54d0c209fd96430827e6590c209f596430827c6590c20d794e430835d5390c209fd95430827e6550c209f595430827c6550c20cf951430833d5450c20d794d430835d5350c20bbd8943082ec6250c20bed8143082f86050c209fd94430827e6510c209f594430827c6510c20e750c430827e64948209f592520827e63948209f58e520827d65d08209fd96420827d6590820cf952420833d5490820be98242082f960908209fd95420827f65108209f594420833e5410820cf55042082de6310820b758c42082fa6010820be580420827d65cc8209fd96320827d658c820d794e320835d538c820be98232082f9608c8209fd95320827f650c8209f59432082be640c820af590320835e530c820d754c32082fa600c820be580320837751944209f992510827d64944209f98e510827d63944209fd91510827c64544209fd8d510827c6354420af99051082bd6414420b798c51082dd6314420dd544510827f65d04209f997410827d65d0420cf953410833d54d0420bb98b41082ed62d04209fd96410827e65904209f59641083765190420dd546410827f65504209f595410827c6550420cf951410833d5450420bbd8941082ec6250420dd94541083755150420bed8141082f860504209fd94410827e65104209f59441082de6310420b758c410827f65cc4209f997310827d65cc420d794f310835d53cc420bb98b31082ed62cc4209fd96310827e658c4209f5963108376518c420dd546310827f654c4209f595310827c654c420d794d310835d534c420bbd8931082ec624c420dd9453108375514c420bed8131082f8604c4209fd94310827e650c4209f59431082be640c420af590310837651c8420dd54721082fa60c8420be583210827d6588420bb596210836d6588420bb986210836d5188420bb582210827f6548420dd94421083755108420f948421082fa6008420be58021082ee6108420f998421083e65108420db54421083e55108420d954421083ea6008420bb58021083e96008420ba580210827e64940209f592500827e63940209f58e500836e2194020db086500827d65d0020b798f40082dd63d00209fd96400827d6590020cf952400833d5490020bb98a40082ed62900209fd95400827f65100209f994400827d65100209f194400833e5410020cf55040082ee6210020bb588400827d6
  | 9 => 0xd52314833c548c520d7d4e314835c538c520ddd463148374518c5209fd95314827e654c5209f195314833f544c520cf151314835f534c520d714d3148377514c520dd145314827e650c5209f594314827c650c520af99031482bd640c520cfd50314833c540c520d7d4c314835c530c520bb98831482ed620c520ddd443148374510c520be98031482f9600c5209f997214833f54c8520cf153214835f53c8520d714f214837451c8520cfd52214833c5488520d7d4e214835c5388520ddd4621483745188520be98221482f96088520cfd51214833c5448520d7d4d214835c5348520ddd4521483745148520bed8121482f860485209f994214833f5408520cf150214835f5308520d714c21483775108520f9484214827e65d0120cfd53404833c54d0120b798f40482dd63d0120d7d4f404835c53d0120bb98b40482ed62d0120ddd47404837451d01209f996404833f5490120cf152404835f5390120d714e40483775190120dd146404827f65501209f595404827c6550120cfd51404833c5450120d7d4d404835c5350120bbd8940482ec6250120ddd45404837451501209f994404833f5410120cf150404835f5310120d714c40483775110120dd144404827e65cc120af99330482bd64cc120cfd53304833c54cc120d7d4f304835c53cc120bb98b30482ed62cc120ddd47304837451cc1209f996304833f548c120cf152304835f538c120d714e3048377518c120dd146304827f654c1209f595304827c654c120cfd51304833c544c120d7d4d304835c534c120bbd8930482ec624c120ddd453048374514c1209f994304833f540c120cf150304835f530c120d714c3048377510c120dd144304833f54c8120cf153204835f53c8120d714f204837751c8120dd14720483bb54c8120ee15320483db53c8120f614f20483f351c8120fc147204833f5488120cf152204835f5388120d714e20483775188120dd14620483af5488120eb15220483cf5388120f314e20483e75188120db14620483e45188120d914620483eb50881209f98f540827d63d50209f98b540836e62d50209f987540827d61d50209f983540837a60d50209f596540833f54950209f98e540827d63950209f986540827d6195020cfd91540827f63550209f18d540827f62550209f589540827f61550209f185540833d5415020b798c54082dd6315020bd98454082f561150209f990540833e64150209f98c540835e63150209798c540827d6315020d758c540825d63150209f988540836e62150209f984540837661150209d984540827d6115020dd584540827561150209f980540837a60150209f993530827d64d4c209f98b530836e62d4c209f987530827d61d4c209f983530837a60d4c209f596530835f5394c209f992530827d6494c209f986530827d6194c
  | 10 => 0x24833f5490920cf152424835f5390920d714e424827c6550920cfd51424833c5450920d7d4d424835c5350920bed8142482f860509209f994424833f5410920cf15042482de6310920b758c424835f5310920d714c42483ad42109209f997324833f54cc920cf153324835f53cc920d714f32482fa60cc920be583324827e658c920cfd52324833c548c920d7d4e324835c538c9209f195324833f544c920cf151324835f534c920d714d32482fb604c920be181324827e650c920af99032482bd640c920cfd50324833c540c920d7d4c324835c530c920f34c8324833f54d4520cf153514835f53d4520d714f514827e64d45209f593514827e63d45209f58f514837754d4520edd53514833754d4520dd953514837554d4520dd15351483b454d4520cd153514837753d4520f5d4f514835753d4520dd94f514837553d4520dd14f51483d453d4520d514f514837764d4520dd993514837564d4520dd193514837763d4520dd98f514837563d4520dd18f514837743d4520dd90f514837543d4520dd10f514837762d4520ddd0b514837642d4520dd50b514837442d4520ddccb514837632d4520dd4cb514837432d4520ddd83514837560d4520af99251482bd6494520cfd52514833c5494520b798e51482dd6394520d7d4e514835c5394520ddd4651482bf6454520af191514833f5454520cf15151482df6354520b718d514835f5354520d714d514833f5414520cf150514835f5314520d714c514837551145209f990514827d64145209f98c514827d6314520bd99451483766514520ddd5051483b75414520cdd5051483765414520dd55051483745414520ed15051483345414520ddd4c51483d75314520d5d4c51483765314520dd54c51483745314520f514c51483545314520ddd9051483766414520dd59051483746414520ddd8c51483766314520dd58c51483746314520ddd0c51483764314520dd50c51483744314520ddd8851483774214520dd90851483754214520dd10851483773214520dd8c851483753214520dd0c851483776014520dd580514837520145209f997414827d65d05209f197414833f54d0520cf153414835f53d0520d714f414837751d0520dd147414827e65905209f596414827c6590520cfd52414833c5490520d7d4e414835c5390520ddd46414837451905209fd95414827e65505209f195414833f5450520cf151414835f5350520d714d41483775150520dd145414827e65105209f594414827c6510520cfd50414833c5410520b798c41482dd6310520d7d4c414835c5310520bb98841482ed6210520ddd4441483745110520be98041482f960105209f997314827d65cc5209f197314833f54cc520cf153314835f53cc520d714f314837751cc520dd147314827e658c5209f596314827c658c520cf
  | 11 => 0x7e64951208f992544827e6395120d798e544825e63951209f58e544835d63951209758e544827d6295120db58a544827e6195120dd986544827661951209f586544837561951209d586544827d6095120de58254482df6355120b718d54482f76155120bd185544833f64551209fd8d544835f635512097d8d544827c6355120d718d544825c63551209fd89544836f62551209fd85544837761551209dd85544827c6155120dd185544827461551209fd81544837b60551209f994544833d5415120cf990544827e63151209f58c544827e62151209f188544827e61151209f58454482be6515120cf994544823e6515120cfd8c544833e6315120cf58c544833c6315120cfd88544833d6215120cfd84544833e6115120cf584544833c6115120cfd80544833d6015120cf480544833f54d4d20cf153534827e64d4d209f593534827e61d4d209f587534835f54d4d20e7d53534831f54d4d20d7953534835d54d4d20d7153534839c54d4d20c7153534835f64d4d20d7993534835d64d4d20d7193534835f62d4d20d758b534835f61d4d20d7987534835d61d4d20d7187534835f60d4d20d758353482be6494d20af592534833f5494d20cf152534835f5394d20bd98653482f56194d209f992534833e6494d208f992534827d6494d20cf592534823d6494d209f98e534825e6394d209f58a534836d6294d209f98653483766194d209d986534827d6194d20dd58653482756194d209f58253483796094d20afd9153482bc6454d20cfd51534833c5454d20bdd8553482f46154d209fd91534833f6454d208fd91534827c6454d20cf191534823c6454d20d7d8d534827f6254d20dbd89534827f6154d20ddd8553482776154d209f18553483746154d209d185534827f6054d20ded81534827e6514d20cfd50534833c5414d20d754c534827e6414d209f590534835e6314d209f988534827c6214d209f984534827d6114d20b7994534835e6514d2097994534835f5414d20e7d50534831f5414d20d7950534835d5414d20d7150534839c5414d20c7150534835f6414d20d7990534835d6414d20d7190534835f6214d20d7588534835f6114d20d7984534835d6114d20d7184534835f6014d20d7580534835d2014d209fd97434827e65d0d209f597434827c65d0d20cfd53434833c54d0d20d7d4f434835c53d0d209fd96434827e6590d209f596434827c6590d20cfd52434833c5490d20d7d4e434835c5390d209fd95434827e6550d209f595434827c6550d20cfd51434833c5450d20d7d4d434835c5350d209fd94434827e6510d209f594434827c6510d20cfd50434833c5410d20d7d4c434835c5310d20e750c43482ee6210d20bb588434827e65d0920cfd53424833c54d0920d7d4f424835c53d0920be98342482f960d09209f9964
  | 12 => 0x552209fd8d548827c63552209fd85548827c6155220cf550548833e64152209f98c548827d6315220db588548827e61152209f584548837a60152209f993538827d64d4e20db58b538827e61d4e209f587538837a60d4e20af99253882bd6494e20d7d4e538827e6494e20cf992538823e6494e209f592538833d6494e208f592538827e6194e209f586538827f6454e209f191538835f6354e209fd85538827c6154e20d754c538827e6414e209f590538835e6314e20db588538827e6114e209f584538837a6014e209fd97438827e65d0e209f597438827c65d0e20cfd53438833c54d0e209fd96438827e6590e209f596438827c6590e20d7d4e438835c5390e209fd95438827e6550e209f595438827c6550e20cfd51438833c5450e20d7d4d438835c5350e20bbd8943882ec6250e209fd94438827e6510e209f594438827c6510e20e750c438833e54d0a20cf55342882fa60d0a20be583428833f5490a20cf152428833e5450a20cf55142882fb6050a20be181428833f5410a20cf15042882de6310a20b758c428835e53cca20d754f32882fa60cca20be583328835f538ca20d714e328835e534ca20d754d32882fb604ca20be18132882be640ca20af590328835f530ca20d714c328837751946209f992518827d64946209f98e518827d63946209fd91518827c64546209fd8d518827c6354620dd544518827f65d06209f997418827d65d0620bb98b41882ed62d06209fd96418827e65906209f596418827f65506209f595418827c6550620bbd8941882ec62506209fd94418827e65106209f59441882de6310620b758c41882fa6010620be580418827f65cc6209f997318827d65cc620bb98b31882ed62cc6209fd96318827e658c6209f596318827f654c6209f595318827c654c620bbd8931882ec624c6209fd94318827e650c6209f59431882be640c620af59031882fa600c620be58031883765188620dd54621882fa6088620be58221883e65188620db54621883e55188620fa98221882ed6088620fa58221883765148620dd54521882fb6048620be18121883e52108620bb594218836d6508620f998421883e75108620db54421883e45108620bb58021882de63d0220b758f408833e5490220cf55240882ee6290220bb58a408833e5410220cf55040882ee6210220bb58840882be64cc220af593308835e538c220d754e30882ee628c220bb58a308835e530c220d754c30882ee620c220bb58830882ed65c8220db59720882ee61c8220be597208837965c82209f98f544827d63d51209f987544827d61d5120cfd8f544833e63d5120cf58f544833c63d5120cfd8b544833d62d5120cfd87544833e61d5120cf587544833c61d5120cfd83544833d60d5120cfd5254482de6395120b758e54482f66195120bd58654482
  | 13 => 0x9f58e54c827e61953209f58654c833f64553209fd8d54c827c63553209fd8554c827c6155320cf55054c82de6315320b758c54c833e64153209f98c54c835e63153209798c54c827d6315320d758c54c825d6315320db98854c827e61153209f58454c837960153209f99353c827d64d4f20db98b53c827e61d4f209f58753c837960d4f20d7d4e53c827e6494f209f59253c827e6194f209f58653c827f6454f209f19153c835f6354f209fd8553c827c6154f20af99053c82bd6414f20d754c53c827e6414f20cf99053c823e6414f209f59053c833d6414f208f59053c835e6314f20db98853c827e6114f209f58453c83796014f209fd9743c827e65d0f209f59743c827c65d0f20cf95343c833d54d0f209fd9643c827e6590f209f59643c827c6590f20d794e43c835d5390f209fd9543c827e6550f209f59543c827c6550f20cf95143c833d5450f20d794d43c835d5350f20bed8143c82f86050f209fd9443c827e6510f209f59443c827c6510f20e750c43c82ee6210f20bb58843c833e5490b20cf55242c82fa6090b20be58242c833e5410b20cf55042c82de6310b20b758c42c83ad4210b20be98042c82f96010b20d794e32c835d538cb20be98232c82f9608cb20af99032c82bd640cb20d794c32c835d530cb20f34c832c82fa600cb20be58032c82be64d4720af59351c82de63d4720b758f51c837751947209f99251c827d64947209f98e51c827d63947209fd9151c827c64547209fd8d51c827c6354720dd54451c827f65d07209f99741c827d65d07209fd9641c827e65907209f59641c833e5490720cf55241c827f65507209f59541c827c6550720bed8141c82f860507209fd9441c827e65107209f59441c833e5410720cf55041c82de6310720b758c41c82ee6210720bb58841c827f65cc7209f99731c827d65cc7209fd9631c827e658c7209f59631c835e538c720d754e31c827f654c7209f59531c827c654c720bed8131c82f8604c7209fd9431c827e650c7209f59431c82be640c720af59031c835e530c720d754c31c82ee620c720bb58831c837651c8720dd54721c82fa60c8720be58321c83765108720dd54421c83e52108720be98021c82f96008720cf95340c833d54d0320b798f40c82dd63d0320bb98b40c82ed62d0320cfd5240c833c5490320cf95140c833d5450320bbd8940c82ec6250320cfd5040c833c5410320af99330c82bd64cc320d794f30c835d53cc320bb98b30c82ed62cc320d7d4e30c835c538c320d794d30c835d534c320bbd8930c82ec624c320d7d4c30c835c530c3209f98f548827d63d5220db58b548827e61d52209f587548837a60d5220cfd5254882de6395220b758e548827e6395220d798e548825e63952209f58e548835d63952209758e548827e61952209f586548833f64
  | 14 => 0x8a320c35d528c830b7986320c2dd608c8309fd95320c2be640c830af590320c36e520c830db548320c2fa600c830be580320c2df640c830e7990320c2dd640c830e7590320c29d640c830b7988320c3ce620c830f3948320c35d520c830f3548320c34d520c830b7984320c3da600c830b7580320c3d9600c830ddd46510c27e64944309f592510c27e62944309f58a510c27f64544309f191510c35e4354430d750d510c27f62544309f189510c2be6414430af590510c2ee6214430bb588510c37551144309fd97410c27e65d04309f597410c33e54d0430cf553410c2de63d0430b758f410c39d43d04309fd96410c27e65904309f596410c3765190430dd546410c27f65504309f595410c27c6550430cf951410c33d5450430b7d8d410c2dc6350430e750d410c3765150430dd545410c2fb6050430be181410c27f65104309f994410c27d6510430b798c410c2dd6310430dd947310c37551cc430be983310c2f960cc4309f596310c2dd658c430d7596310c2df648c430b7592310c2de628c430b7986310c35d518c430b7582310c27f654c430af990310c2bd640c430dd944310c375510c430be980310c2f9600c430b7d90310c39e640c430b7590310c39d640c430a7590310c2de620c430b7984310c3d6610c430f5944310c35d510c430f5544310c355510c430f6980310c2dd600c430f6580310c27f65c84309f997210c27d65c8430b798f210c2dd63c8430db94b210c36d52c84309fd96210c27e65884309f596210c2de6388430b758e210c3765188430dd546210c27f65484309f595210c27c6548430b7d8d210c2dc6348430db949210c36d5248430dd945210c3755148430bed81210c2f860484309fd94210c27e65084309f594210c2df6308430b718c210c3e521084309f992500c27d6494030d790e500c35d4394030d78ca500c35c3294030d78c6500c35c31940309f597400c2de63d0030b758f400c27f65900309f596400c33e5490030cf552400c2de6390030b758e400c39d43900309fd95400c27f65100309f994400c27d65100309f194400c33e5410030cf550400c2de6310030b758c400c39d4310030ee500400c2be64cc030af593300c2df64cc030e7993300c2dd64cc030e7593300c29d64cc030b798b300c2de61cc030b758e300c35e538c030be58e300c37a538c030f694e300c3da438c030f650e300c3da328c030f60ca300c3da318c030f60c6300c27f654c030b7d95300c35f654c03097d95300c2df644c030b7591300c2dc624c030b7185300c2df604c030d7941300c3db404c030f6101300c2fb654c030ded95300c27b654c030bed8d300c3db634c030de94d300c3da534c030f6d0d300c3d8434c0309f98f54c827d63d5320db98b54c827e61d53209f58754c837960d5320cfd5254c827e639532
  | 15 => 0x4c27e65cc530ddd46314c374518c530be982314c2f9608c530ddd45314c374514c530bed81314c2f8604c5309f994314c2be640c530af590314c3d5310c5309f997214c27d65c85309f197214c37751c8530dd147214c27e65885309f596214c27c6588530dbd4a214c36c52885309fd95214c27e65485309f195214c27e65085309f594214c27c6508530b798c214c2dd6308530dbd48214c36c5208530ddd44214c3745108530f9484214c2fa6008530be580214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d01309f996404c33e5490130cf552404c27f65501309f595404c27c6550130cfd51404c33c5450130b7d8d404c2dc63501309f994404c33e5410130cf550404c2be64cc130af593304c3ba64cc130ee593304c35f548c130d7552304c35c528c130d7146304c3db508c1309f98f540c35e63d50309f98b540c27d62d50309f987540c27d61d50309f983540c37a60d50309f596540c33f5495030d798e540c27e62950309f58a540c27e61950309f586540c33f64550309fd8d540c27d63550309fd89540c27c62550309fd85540c27c6155030cf550540c2ee6215030bb588540c2f66115030bd584540c27e6415030cf990540c27e6315030d798c540c27e6215030db988540c26e62150309f588540c36d62150309b588540c27e6115030dd984540c27661150309f584540c37561150309d584540c27e6015030de980540c27e6494c30cf992530c23e6494c309f592530c33d6494c308f592530c27d65d0c30cfd53430c33c54d0c309fd96430c27d6590c30cf952430c33d5490c30be982430c2f96090c30d7596430c25d6590c30b7592430c35e5490c30e7952430c39d5490c30d7152430c2de6290c30b7986430c3da6090c30b7582430c3d96090c30b6582430c27f6550c30cfd51430c33c5450c30b7d95430c35f6550c30e7d91430c39f5450c30d7951430c35c5450c30e7151430c31c5450c30b7189430c2dc6150c30b7d81430c27f6510c309f594430c33e5410c30cf550430c2de6310c30e750c430c2fa6010c30be580430c36f52948309f992520c27d64948309f986520c27d61948309fd91520c27c6454830d790d520c35d43548309fd85520c27c6154830af990520c2bd6414830db548520c2f66114830bd584520c27f65d08309f997420c27d65d0830cf953420c33d54d0830b798f420c2dd63d0830e750f420c27f65908309f996420c27d6590830db94a420c36d52908309fd95420c27d65508309f195420c33e5450830cf551420c2df6350830b718d420c39d4350830db949420c36d5250830bed81420c2f860508309fd94420c27e65108309f594420c2de6310830b758c420c36e52cc830db54b320c2fa60cc830be583320c27d658c830b7596320c35d658c830b7d92320c2dd648c830b79
  | 16 => 0x6518c630d7546318c3d5518c630f6982318c2dd608c630f6582318c376514c630dd545318c2fb604c630be181318c2be640c630af590318c2dd650c630d7594318c2df640c630e7990318c2dd640c630e7590318c29d640c630b7988318c3d6610c630d7544318c2dd600c6309fd97218c27e65c86309f597218c2de63c8630b758f218c27f65886309f996218c27d6588630b798e218c2dd63886309fd95218c27d65486309f195218c2df6348630b718d218c27f65086309f994218c27d6508630b7d8c218c2dc6308630f9484218c2fa6008630be580218c2de63d0230b758f408c33e5490230cf552408c2de6390230b758e408c39d4390230cf950408c33d5410230b798c408c2dd6310230e750c408c2be64cc230af593308c2dd65cc230d7597308c2df64cc230e7993308c2dd64cc230e7593308c29d64cc230b798b308c2de61cc230be597308c37965cc230ee993308c3b964cc2309f98b544c27d62d51309f987544c27d61d5130cfd52544c27e64951309f58e544c35d63951309758e544c27e62951309f58a544c27e61951309f586544c27d6095130de582544c2ef6255130bb189544c2f76155130bd185544c33f64551309fd8d544c35f63551309fd89544c36f62551309bd89544c27c6255130db189544c26c62551309fd85544c37761551309dd85544c27c6155130dd185544c27461551309fd81544c37b60551309f994544c33d5415130cf990544c27e63151309f18c544c27e62151309f588544c27e61151309f584544c27e65d0d30cfd53434c33c54d0d30be983434c2f960d0d309f996434c27c6550d30cfd51434c33c5450d30bed81434c2f86050d309f994434c39d4310d309f993524c27d64d49309f987524c27d61d4930dbd4a524c2bf6454930af191524c2f76154930bd185524c36d52149309f990524c27d64149309f984524c27d61149309f997424c27d65d09309f197424c36f52d0930db14b424c27e65909309f596424c27c6590930cfd52424c33c54909309fd95424c27e65509309f195424c27e65109309f594424c27c6510930cfd50424c33c5410930b798c424c2dd6310930dbd48424c36c52109309f997324c36f528c930db14a324c2fa608c930be582324c36f524c930db149324c2fb604c930be181324c27e650c930af990324c2bd640c930f34c8324c27e64d45309f593514c27e62d45309f58b514c3775194530afd91514c2bc6454530bbd89514c2ec6254530dd544514c27e64145309f590514c27e62145309f588514c27e65d05309f597414c27c65d0530ddd47414c37451d05309f996414c27d65905309f196414c33f5490530cf152414c27f65505309f995414c27c65505309f994414c27d65105309f194414c33f5410530cf150414c2de6310530b758c414c3775110530dd14441
  | 17 => 0xc730be98331cc2f960cc730cf95231cc33d548c730cf95131cc33d544c730af99031cc2bd640c730cf95031cc33d540c730dd94431cc375510c730f54c431cc2fa600c730be58031cc27f65c87309f99721cc27d65c8730cf95321cc33d54c8730dd94721cc37551c87309fd9621cc27e65887309f59621cc33e5488730cf55221cc36e5288730db54a21cc27f65487309f59521cc27c6548730cf95121cc33d5448730bed8121cc2f860487309fd9421cc27e65087309f59421cc33e5408730cf55021cc2de6308730b758c21cc36e5208730db54821cc3765108730dd54421cc3e52108730cf95340cc33d54d0330b798f40cc2dd63d0330cf95240cc33d5490330cf95140cc33d5450330b7d8d40cc2dc6350330cf95040cc33d5410330ee50040cc35d63d52309f98b548c27d62d52309f987548c27d61d5230de983548c33f5495230d758e548c27e62952309f58a548c27e61952309f586548c33f64552309fd89548c27c62552309fd85548c27c6155230cf550548c33e6415230d758c548c27e62152309f588548c27e61152309f584548c37a6015230cf953438c33d54d0e30be983438c2f960d0e30b7596438c35d6590e30d7952438c35c5490e30b798a438c2de6190e30b7582438c33e5450e30cf551438c2fb6050e30be181438c35f6550e30e7d91438c35e5450e30e7951438c31e5450e30e7551438c35c5450e30b7189438c2dc6150e30b7d81438c3db6050e30f6181438c39d4310e30dbd4a528c27e6494a309f592528c27e6194a309f586528c27f6454a309f191528c35e4354a30d750d528c27f6154a309f185528c36d5214a309fd97428c27e65d0a309f597428c2de63d0a30b758f428c39d43d0a309fd96428c27e6590a309f596428c27f6550a309f595428c27c6550a30b7d8d428c2dc6350a30e750d428c27f6510a309f994428c27d6510a30b798c428c2dd6310a30db94a328c36d528ca30be982328c2f9608ca30b7d92328c2dd648ca30f394a328c35d528ca30f354a328c2de618ca30f6982328c2dd608ca30f6582328c36e524ca30db549328c2fb604ca30be181328c2be640ca30af590328c2dd650ca30d7594328c2df640ca30e7990328c2dd640ca30e7590328c29d640ca30f3988328c35d520ca30b7984328c2dd600ca30ddd46518c27e64946309f592518c27e62946309f58a518c27f64546309f191518c35e4354630d750d518c27f62546309f189518c37551146309fd97418c27e65d06309f597418c2de63d0630b758f418c39d43d06309fd96418c27e65906309f596418c27f65506309f595418c27c6550630b7d8d418c2dc6350630e750d418c27f65106309f994418c27d6510630b798c418c2dd6310630dd946318c375518c630be982318c2f9608c630b7d92318c2dd648c630b798a318c3d
  | 18 => 0xe798f40102bd63d0040e758f401029d63d0040af98b40102be61d0040af592401033e5490040be592401037a5490040ee95240103bb4390040ee50e40103ba4290040ee10a40103ba4190040ee106401027f6550040afd95401033f65500408fd9540102bf6350040af18940102bc6150040afd81401033e5050040bed95401037b65500409ed9540102fb6450040eed91401037a5450040ee95140103ba4350040ee10d401035e63d53309f98b54cc27d62d53309f98754cc27d61d5330de58354cc33f54953309f98a54cc27d62953309f98654cc27d6195330cf98e54cc33c6395330cfd8a54cc33e6295330cf58a54cc33c6295330cfd8654cc33e6195330cf58654cc33c6195330cfd8254cc33d6095330cfd9154cc27f62553309f18954cc27f61553309f18554cc33f6555330cf98d54cc33c6355330cfd8954cc33e6255330cf58954cc33c6255330cfd8554cc33e6155330cf58554cc33c6155330cfd8154cc33d6055330cf55054cc33e6415330d798c54cc27e62153309f58854cc27e61153309f58454cc3796015330cf95343cc33d54d0f30cf95243cc33d5490f30be98243cc2f96090f30cf95143cc33d5450f30cf95043cc33d5410f30e750c43cc2fa6010f30be58043cc2be64d4b30af59352cc33e54d4b30cf55352cc2f661d4b30bd58752cc33e5494b30cf55252cc36f5294b309f99252cc27d6494b309f98652cc27d6194b30cf95152cc33d5454b309fd9152cc27c6454b309fd8552cc27c6154b30af99052cc2bd6414b30cf95052cc33d5414b30db54852cc27f65d0b309f99742cc27d65d0b30cf95342cc33d54d0b309fd9642cc27e6590b309f59642cc33e5490b30cf55242cc27f6550b309f59542cc27c6550b30cf95142cc33d5450b30bed8142cc2f86050b309fd9442cc27e6510b309f59442cc33e5410b30cf55042cc2de6310b30b758c42cc33e54ccb30cf55332cc36e52ccb30db54b32cc2fa60ccb30be58332cc33e548cb30cf55232cc33e544cb30cf55132cc2be640cb30af59032cc33e540cb30cf55032cc36e520cb30db54832cc3cd320cb30be98032cc2f9600cb30af99351cc2bd64d4730cf95351cc33d54d4730bb98b51cc2ed62d4730cf95251cc33d5494730ddd4651cc27e64947309f59251cc27e62947309f58a51cc33e5454730cf55151cc27f64547309f19151cc27f62547309f18951cc2be6414730af59051cc33e5414730cf55051cc37551147309fd9741cc27e65d07309f59741cc33e54d0730cf55341cc27f65907309f99641cc27d6590730cf95241cc33d54907309fd9541cc27d65507309f19541cc33e5450730cf55141cc2fb6050730be18141cc27f65107309f99441cc27d6510730cf95041cc33d5410730b798c41cc2dd6310730cf95331cc33d54cc730dd94731cc37551c
  | 19 => 0x5431033f6550c40e7d8d431039f5350c40cf94d431039c5350c40af18943102bc6150c40afd8143102be6410c40d794c431035d5310c40e750c43102fa6010c40be580431036f52948409f98e521027d63948409f986521027d61948409fd8d521027c6354840cfd0d521033d43548409fd85521027c6154840b798c52102dd6314840db54852102f66114840bd584521036e52d0840db54b42102fa60d0840be583421027d6590840af596421033d6590840af58e42102be6290840cf54a42102be6190840af582421027f6550840b798c42102dd6310840db948421036d5210840be98042102f96010840e798c42102bd6310840e758c421029d6310840af98842103ae6210840eb948421033d5210840eb548421032d5210840af98442103ba6010840af58042103b960108409fd97321027e65cc8409f59732102be64cc840af593321035e53cc840d754f321039d43cc8409fd96321027e658c8409f59632102bf648c840af192321036e528c840db54a321027f654c8409f595321027c654c840afd9132102bc644c840d794d321035d534c840e750d321036e524c840db54932102fb604c840be181321027f650c8409f994321027d650c840af99032102bd640c840ddd46511027e63944409f58e511027e62944409f58a511027f63544409f18d511033f4354440cf50d511027f62544409f18951102de6314440b758c51102ee6214440bb58851103755114440dd947411037551d0440be98341102f960d04409f59641102bd6590440cf59641102bd6390440af98a41102be6190440cf54641102bd60904409fd9541102de6310440b758c41103765110440dd54441102fa6010440be580411039e6310440af58c411039d6310440a758c41102be6210440af98441103b66110440ed944411033d5110440ed54441103355110440ee98041102bd6010440ee580411027f65cc4409f997311027d65cc440af99331102bd64cc440d794f311035d53cc440e750f311027f658c4409f996311027d658c440afd9231102bc648c440dd9463110375518c4409fd95311027d654c4409f19531102bf644c440af191311035e534c440d754d311039d434c440dd9453110375514c440bed8131102f8604c4409fd94311027e650c4409f59431102be640c440af590311027f65c84409f997211027d65c8440af99321102bd64c8440db94b211036d52c84409fd96211027e65884409f59621102be6488440af59221103765188440dd546211027f65484409f595211027c6548440afd9121102bc6448440db949211036d5248440dd94521103755148440bed8121102f860484409fd94211027e65084409f59421102bf6408440af19021103e52108440cfd0e501033d4394040cf90a501033c4294040cf906501033c4194040b798f40102dd63d0040
  | 20 => 0x27f65486409f595219027c6548640afd9121902bc64486409fd94219027e65086409f59421902bf6408640af19021903e52108640be98021902f96008640b798f40902dd63d0240af597409033d65d0240e798f40902bd63d0240e758f409029d63d0240af98b40902be61d0240be597409037965d0240f698f40903d963d02409f98b535027d62d4d409f987535027d61d4d40d7d4e53502ef6254d40bb18953502f76154d40bd185535035d5314d409f988535027d6214d409f984535027d6114d409f997435035f5390d40d714e43502fa6090d40be582435035f5350d40d714d43502fb6050d40be181435027e6510d40e750c435027e63d49409f58f525027e61d49409f587525036f5294940b7d8d52502dc6354940bdd8552502f46154940db548525027e63149409f58c525027e61149409f584525027e65d0940dbd4a425036c5290940be98242502f96090940dbd49425036c5250940bed8142502f860509409f99442502de6310940b758c42503ad42109409f997325027d65cc9409f197325036f52cc940db14b325027e658c9409f596325027c658c940d7d4e325035c538c9409fd95325027e654c9409f195325027e650c9409f594325027c650c940af99032502bd640c940d7d4c325035c530c940dbd48325036c520c9409f98f515027d63d45409f98b515027d62d4540ddd4651502df6354540b718d51502ef6254540bb189515037551145409f98c515027d63145409f988515027d62145409f99741503775190540dd14641502fa6090540be58241503775150540dd14541502fb6050540be181415027e6510540b798c41502dd6310540ed504415027e65cc5409f597315027c65cc540ddd47315037451cc5409f996315027d658c5409f196315035f538c540d714e315027f654c5409f995315027c654c5409f994315027d650c5409f19431502be640c540af590315035f530c540d714c3150377510c540dd144315027e65c85409f597215027c65c8540ddd47215037451c85409f996215027d65885409f196215036f5288540db14a215027f65485409f995215027c65485409f994215027d65085409f19421502be6408540af590215036f5208540db14821503775108540dd14421503e52108540be98021502f96008540b798f40502dd63d0140f698f40503d963d0140cfd4e405033c5290140cf14640503bb5090140d798e541035d6395040d7d4e531027e6294c409f58a531027e6194c409f586531027f6254c409f189531027f6154c409f185531035d5314c40bb98853102ed6214c40bd98453102f56114c40d794f431035d53d0c40be98343102f960d0c40cf94f431039e53d0c40e754f43102be62d0c40af98743103ba60d0c40af58343103b960d0c40ae583431027d6590c40af592431027f6550c40afd9
  | 21 => 0x654c7409f59531d027c654c740d794d31d035d534c740bed8131d02f8604c7409fd9431d027e650c7409f59431d02be640c740af59031d035e530c740d754c31d027f65c87409f99721d027d65c8740d794f21d035d53c8740dd94721d037551c87409fd9621d027e65887409f59621d035e5388740d754e21d036e5288740db54a21d027f65487409f59521d027c6548740d794d21d035d5348740bed8121d02f860487409fd9421d027e65087409f59421d02be6408740af59021d035e5308740d754c21d036e5208740db54821d03765108740dd54421d03e52108740d7d4e539027e6294e409f58a539027e6194e409f586539027f6254e409f189539027f6154e409f185539035d5314e40af597439033d65d0e40cf94f43902be62d0e40af98743902bd60d0e40d794e439035d5390e40be98243902f96090e40d794d439035d5350e40bed8143902f86050e40e7d8d439033e5350e40e794d439031e5350e40e754d43902bc6250e40af18543902bf6050e40eed8143903b86050e40e750c439036f5294a409f98e529027d6394a409f986529027d6194a409fd8d529027c6354a40cfd0d529033d4354a409fd85529027c6154a40db548529036e5290a40db54a42902fa6090a40be58242902bd6390a40eb94a429033d5290a40eb54a42902be6190a40ee98242902bd6090a40ee582429036e5250a40db54942902fb6050a40be18142902de6310a40b758c42902bd6510a40cf594429039e6310a40af58c429039d6310a40a758c42903ae6210a40cf54842902be6110a40af580429027f65cca409f997329027d65cca40af99332902bd64cca40e750f329027f658ca409f996329027d658ca40afd9232902bc648ca409fd95329027d654ca409f19532902bf644ca40af191329039d434ca409fd94329027e650ca409f59432902be640ca40af590329037751946409f98e519027d63946409f98a519027d62946409fd8d519027c6354640cfd0d519033d43546409fd89519027c6254640dd54451903765190640dd54641902fa6090640be58241902bd6390640af98a41903b65190640cf54641903b55190640ee98241902bd6090640ee58241903765150640dd54541902fb6050640be18141902de6310640b758c41902bd6510640cf594419039e6310640af58c419039d6310640a758c41902be6210640ed984419033d5110640af580419027f65cc6409f997319027d65cc640af99331902bd64cc640e750f319027f658c6409f996319027d658c640afd9231902bc648c6409fd95319027d654c6409f19531902bf644c640af191319039d434c6409fd94319027e650c6409f59431902be640c640af590319027f65c86409f997219027d65c8640af99321902bd64c86409fd96219027e65886409f59621902be6488640af592219
  | 22 => 0x421f9d5121087e65448421f955121087e45448421f9d8d21087e66348421f958d21087e46348421f9d4d21087e65348421f954d21087e45348421f9d0d21087e64348421f950d21087e44348421f9d8121087e66048421f958121087e46048421b918121087e521d4021f9486500877b50940219f992500867d64940219f98e500867d6394021afd9150086bc6454021b7d8d50086dc6354021f9485500867f6454021cfd91500863f64540219f191500873c64540218f191500867f6354021d7d8d500865f63540219f18d500875c63540219718d50086be6414021af59050086de6314021b758c50087e52114021de540500875f5394f409f98a53d027d6294f409f98653d027d6194f40d719253d035f6294f40d798a53d035d6294f40d718a53d035f6194f40d798653d035d6194f40d718653d035f6094f40d758253d027f6254f409f18953d027f6154f409f18553d035f6554f40d799153d035f6254f40d798953d035d6254f40d718953d035f6154f40d798553d035d6154f40d718553d035f6054f40d758153d035d5314f40d794f43d035d53d0f40be98343d02f960d0f40d754e43d035e5350f40d794c43d035d5310f40e750c43d02fa6010f40be58043d02de63d4b40b758f52d035e53d4b40d754f52d02f661d4b40bd58752d035e5394b40d754e52d036f5294b409f98e52d027d6394b409f98652d027d6194b40d794d52d035d5354b409fd8d52d027c6354b409fd8552d027c6154b40b798c52d02dd6314b40d794c52d035d5314b40db54852d035e53d0b40d754f42d036e52d0b40db54b42d02fa60d0b40be58342d035e5390b40d754e42d035e5350b40d754d42d02de6310b40b758c42d035e5310b40d754c42d036e5210b40db54842d03ad4210b40be98042d02f96010b409fd9732d027e65ccb409f59732d035e53ccb40d754f32d027f658cb409f99632d027d658cb40d794e32d035d538cb409fd9532d027d654cb409f19532d035e534cb40d754d32d02fb604cb40be18132d027f650cb409f99432d027d650cb40af99032d02bd640cb40d794c32d035d530cb40b798f51d02dd63d4740d794f51d035d53d4740bb98b51d02ed62d4740d794e51d035d5394740ddd4651d027e63947409f58e51d027e62947409f58a51d035e5354740d754d51d027f63547409f18d51d027f62547409f18951d02de6314740b758c51d035e5314740d754c51d03755114740d794f41d035d53d0740dd94741d037551d0740be98341d02f960d0740d794e41d035d5390740d794d41d035d5350740b798c41d02dd6310740d794c41d035d5310740dd94441d03755110740ed50441d02fa6010740be58041d027f65cc7409f99731d027d65cc740d794f31d035d53cc7409fd9631d027e658c7409f59631d035e538c740d754e31d027f
  | 23 => 0x798c540865e63150219f58c540875d63150219758c540867e6215021db988540867e6115021dd984540867e6015021de980540867a60150219f580540877960150219e580540867e64d4c219f593530867e62d4c21db98b530867e61d4c21dd987530867e60d4c219f583530867d6594c21d7d4e530867e6494c219f592530867e6094c219f582530867f6454c219f191530875f6354c219fd81530867c6054c21af99053086bd6414c21d754c53086fa6014c21be580530867e6414c21cf990530863e6414c219f590530873d6414c218f590530867e6314c21d798c530867e6214c21db988530867e6114c21dd984530867e6014c21de980530867a6014c219f58053087796014c219e580530867f65d0c219f997430867d65d0c219f197430873e54d0c21cf553430867f6590c219f996430867d6590c219f196430875e5390c21d754e430867f6550c219f995430867d6550c219f195430873e5450c21cf551430875e5350c21d754d43086ef6250c21bb18943086f76150c21bd185430867f6510c219f994430867d6510c219f194430879d4310c21bb98843086ed6210c21bd98443086f56110c219f992520867d64948219f98e520867d63948219f597420867f65908219f596420873e5490821cf55242086f66190821bd586420867f65508219fd94420867d6510821cf950420873d5410821b798c42086dd6310821eb50842086f66110821bd584420867d65cc8219fd96320867d658c821d794e320875d538c821bd98632086f5618c8219fd95320867f650c8219f59432086be640c821af590320875e530c821d754c32087cd320c821bd98432086f5610c8219f992510867d64944219f98e510867d63944219f597410867f65904219f596410873e5490421cf55241086ee6290421bb58a410867f65504219fd94410867e65104219f594410867c6510421cf950410873d5410421b798c41086dd6310421bb98841086ed6210421ed504410867d65cc4219fd96310867d658c421d794e310875d538c421bb98a31086ed628c4219fd95310867f650c4219f994310867d650c4219f19431086be640c421af590310875e530c421d754c31086ee620c421bb58831087d5310c421bb98321086ed6288421db94a21086f56288421b958a21087765288421f994a21086f660884219fd9521086ef6548421dbd95210866f6548421bbd85210876e5148421f9d0521087e64148421f950521087e44148421f9cc521087e63148421f94c521087e43148421bb18121086f76548421ddd9521086776548421bdd8921087e76248421dd94921087e65248421f9d0921087e64248421f950921087e44248421f9cc921087e63248421f94c921087e43248421bd18121087e76548421b9d9521087676548421f9d9121087e66448421f959121087e46448
  | 24 => 0x544873f64551219fd8d544875f635512197d8d544867c6355121d718d544865c63551219fd89544876f62551219fd85544877761551219fd81544877b60551219ed81544867c6055121de181544867860551219f994544873d5415121b798c54486dd6315121cf990544867e6315121d798c544865e63151219f58c544875d63151219758c544867e60151219f580544867e64d4d219f593534867e60d4d219f583534875f5394d219f992534867d6494d219f98e534867d6294d21db58a534867d6194d21dd586534867e6094d219f58253486bf6454d21af19153486fb6054d21be181534867f6454d21cfd91534863f6454d219f191534873c6454d218f191534875f6354d219fd89534876f6254d219fd8553487776154d219fd81534877b6054d219ed81534867c6054d21de18153486786054d219f99453486be6414d21af590534875d5314d219f990534873e6414d218f990534867d6414d21cf590534863d6414d21d798c534867e6014d219f580534867f65d0d219f997434867d65d0d219f197434873e54d0d21cf553434875f53d0d21d714f434867f6590d219f996434867d6590d219f196434873f5490d21cf152434875e5390d21d754e434867f6550d219f995434867d6550d219f195434873e5450d21cf551434875e5350d21d754d434867f6510d219f994434867d6510d219f194434873f5410d21cf150434875f5310d21d714c434879d4310d219f997424873f54d0921cf15342486f661d0921bd587424867e65909219f195424873f5450921cf15142486f76150921bd185424867e6510921b798c42486dd63109219f997324875f53cc921d714f32486f661cc921bd587324867e658c9219f195324875f534c921d714d32486f7614c921bd185324867e650c921af99032486bd640c9219f997414873f54d0521cf15341486ee62d0521bb58b414867e65905219fd95414867d65505219f195414873f5450521cf15141486ef6250521bb189414867e6510521b798c41486dd63105219f997314875f53cc521d714f31486ee62cc521bb58b314867e658c5219fd95314867d654c5219f195314875f534c521d714d31486ef624c521bb189314867e650c521af99031486bd640c521f9d46214867e64d41219f593504867e63d41219f58f504877b5094121afd9150486bc6454121b7d8d50486dc6354121de540504867e64141219f590504867e63141219f58c50487772114121db884504867e63d50219f58f540867e62d5021db98b540867e61d5021dd987540867e60d50219f583540867d6595021cfd52540867e63950219f58e540867e60950219f582540873f64550219fd8d540867c63550219fd81540867c6055021cf55054086de6315021b758c54086fa6015021be580540867e6415021cf990540867e6315021d
  | 25 => 0x6f56110b21d794e32c875d538cb21bd98632c86f5618cb21af99032c86bd640cb21d794c32c875d530cb21bd98432c86f5610cb21cf95341c873d54d0721bb98b41c86ed62d0721cf95141c873d5450721bbd8941c86ec6250721b798c41c86dd6310721ed50441c875e53cc721d754f31c86ee62cc721bb58b31c875e534c721d754d31c86ef624c721bb18931c86be640c721af59031c87d5310c721af99350c86bd64d4321b798f50c86dd63d4321ded4250c867e64943219f59250c867e63943219f58e50c867f64543219f19150c867f63543219f18d50c877950143219f98f548867d63d5221db58b548877661d52219f983548867d60d5221cfd52548867e63952219f58e548867e60952219f582548873f64552219fd8d548867c63552219fd81548867c6055221cf55054886de6315221b758c548873e64152219f98c548875e63152219798c548867d6315221d758c548865d6315221db588548877661152219f980548867d60152219f993538867d64d4e21db58b538877661d4e219f983538867d60d4e21d7d4e538867e6494e219f592538867e6094e219f582538867f6454e219f191538875f6354e219fd81538867c6054e21af99053886bd6414e21d754c538867e6414e21cf990538863e6414e219f590538873d6414e218f590538875e6314e21db58853887766114e219f980538867d6014e219fd97438867e65d0e219f597438867c65d0e21cf953438873d54d0e219fd96438867e6590e219f596438867c6590e21d794e438875d5390e219fd95438867e6550e219f595438867c6550e21cf951438873d5450e21d794d438875d5350e21bbd8943886ec6250e219fd94438867e6510e219f594438867c6510e21e750c43886ee6210e21bb588438873e54d0a21cf55342886f661d0a21bd587428873e5450a21cf55142886f76150a21bd18542886de6310a21b758c42887ad4210a21d794f328875d53cca21bd98732886f561cca21d794d328875d534ca21bdd8532886f4614ca21af99032886bd640ca21f34c8328873e5490621cf55241886ee6290621bb58a418873e5410621cf55041886de6310621b758c41886ee6210621bb588418875e538c621d754e31886ee628c621bb58a31886be640c621af590318875e530c621d754c31886ee620c621bb58831886ed65c8621db59721886ee60c8621bd597218877565c8621af99350886bd64d4221b798f50886dd63d4221ded42508867e64942219f592508867e63942219f58e508877721942219fd91508867c64542219fd8d508867c6354221de540508867e63d51219f58f544867e60d51219f583544873f54951219f992544867e63951219f58e544867d6295121db58a544867d6195121dd586544867e60951219f58254486df6355121b718d54486fb6055121be181
  | 26 => 0x410831cf550420c6de6310831b758c420c73e54cc831cf553320c76e52cc831db54b320c6f661cc831bd587320c67d658c831cf952320c73d548c8319fd95320c73e544c831cf551320c6be640c831af590320c73e540c831cf550320c76e520c831db548320c7cd320c831bd984320c6f5610c8319f992510c67d64944319f597410c73e54d0431cf553410c67f65904319f596410c73e5490431cf552410c6de6390431b758e410c67f6550431cf951410c73d54504319fd94410c67e65104319f594410c67c6510431cf950410c73d5410431b798c410c6dd6310431ed504410c73e54cc431cf553310c75f54cc431e7953310c75d54cc431e7553310c71d54cc431b7983310c73e548c431cf552310c6dd638c431d794e310c7b6548c431ed552310c6f5638c431dd94e310c7d6538c4319fd95310c73e544c431cf551310c6df654c431d7d95310c65f654c431d7d51310c79e544c431d7551310c79d544c431c7551310c6df614c431d7945310c7d7414c431f5105310c6dc604c431bdd95310c777654c4319dd95310c7b6544c431ed551310c6f7634c431f5d8d310c776534c431f594d310c7d7434c431f510d310c7d6324c431f50c9310c6be64d4031af593500c73e54d4031cf553500c73e5494031cf552500c77b50940319f992500c67d64940319f98a500c67d6294031cf951500c73d54540319fd91500c67c64540319fd89500c67c6254031af990500c6bd6414031cf950500c73d5414031bb988500c6ed6214031de540500c67e63d53219f58f54c876e62d5321dd58754c867e60d53219f58354c873f54953219f98e54c867d63953219f98254c867d6095321cfd9154c867f63553219f18d54c867f60553219f18154c873d5415321b798c54c86dd6315321cf99054c867e6315321d798c54c865e63153219f58c54c875d63153219758c54c876e6215321dd58454c867e60153219f58054c867e64d4f219f59353c876e62d4f21dd58753c867e60d4f219f58353c875f5394f219f99253c867d6494f219f98253c867d6094f219fd9153c867c6454f21d7d8d53c867f6054f219f18153c86be6414f21af59053c875d5314f219f99053c873e6414f218f99053c867d6414f21cf59053c863d6414f21d798c53c876e6214f21dd58453c867e6014f219f58053c867f65d0f219f99743c867d65d0f219f19743c873e54d0f21cf55343c867f6590f219f99643c867d6590f219f19643c875e5390f21d754e43c867f6550f219f99543c867d6550f219f19543c873e5450f21cf55143c875e5350f21d754d43c86f76150f21bd18543c867f6510f219f99443c867d6510f219f19443c879d4310f21bd98443c86f56110f21cf95242c873d5490b21bd98642c86f56190b21cf95042c873d5410b21b798c42c86dd6310b21bd98442c8
  | 27 => 0x31be181524c76d52149319f990524c67d64149319f980524c67d60149319f997424c67d65d09319f197424c6de63d0931b758f424c79d43d0931dbd4b424c76c52d0931bd987424c6f561d09319f996424c67d65909319f196424c73f5490931cf152424c67f65509319f995424c67c6550931e750d424c67e65109319f594424c67c6510931cfd50424c73c5410931b798c424c6dd6310931dbd48424c76c52109319f997324c76f528c931db14a324c6f6618c931bd586324c76f524c931db149324c6f7614c931bd185324c67e650c931af990324c6bd640c9319f997414c73f54d0531cf153414c6de63d0531b758f414c79d43d05319f996414c67f65505319f595414c67c6550531cfd51414c73c5450531b7d8d414c6dc6350531e750d414c67e6510531b798c414c6dd6310531f590f314c7d543cc531b7d92314c6dd648c531f5d46314c67e64d41319f593504c67e62d41319f58b504c77b5094131afd91504c6bc6454131bbd89504c6ec6254131de540504c67e64141319f590504c75e4314131d750c504c67e62141319f588504c75e31141319f98f540c75e63d50319f98b540c67d62d50319f987540c77661d50319f983540c67d60d50319f596540c73f54950319f98a540c67d62950319f982540c67d60950318f596540c73e6395031cf18e540c73f6295031cf98a540c73d6295031cf18a540c73e6195031cf186540c73f6095031cf982540c73d6095031cf182540c73f64550319fd89540c67c62550319fd81540c67c6055031cfd95540c73e6355031cf18d540c73f6255031cf989540c73d6255031cf189540c73e6155031cf185540c73c3155031cfd81540c73e6055031cf581540c73c6055031af990540c73d54150319f990540c73e64150318f990540c67e6315031d798c540c65e63150319f988540c67d62150319f984540c77661150319f980540c67d60150319f992530c67d6494c319f597430c73e54d0c31cf553430c67f6590c319f596430c73e5490c31cf552430c75e5390c31bd986430c6f56190c319fd95430c73e5450c31cf551430c75e5350c319fd94430c67d6510c31cf950430c73d5410c31e750c430c6f66110c31bd584430c6be64d4831af593520c73e54d4831cf553520c73e5494831cf552520c76f52948319f992520c67d64948319f982520c67d6094831cf951520c73d54548319fd91520c67c64548319fd81520c67c6054831af990520c6bd6414831cf950520c73d5414831db548520c6fa6014831be580520c67f65d08319f997420c67d65d0831cf953420c73d54d08319fd96420c67e65908319f596420c73e5490831cf552420c67f65508319f595420c67c6550831cf951420c73d5450831b7d8d420c6dc6350831bdd85420c6f461508319fd94420c67e65108319f594420c73e5
  | 28 => 0x95141cc73d5450731b7d8d41cc6dc6350731e750d41cc6de6310731b758c41cc7b54110731af99350cc6bd64d4331bb98b50cc6ed62d4331ded4250cc67e64943319f59250cc75e4394331d750e50cc67e62943319f58a50cc67f64543319f19150cc67f62543319f18950cc7795014331d758f548c67e62d52319f58b548c77661d52319f983548c67d60d5231cfd52548c67e62952319f58a548c67e60952319f582548c73f64552319fd89548c67c62552319fd81548c67c6055231cf550548c73e6415231d758c548c67e62152319f588548c77661152319f980548c67d6015231cf953438c73d54d0e31bd987438c6f561d0e31cf951438c73d5450e31bdd85438c6f46150e31e750c438c76f5294a319f992528c67d6494a319f982528c67d6094a319fd91528c67c6454a319fd81528c67c6054a31db548528c67f65d0a319f997428c67d65d0a31bd987428c6f561d0a319fd96428c67e6590a319f596428c67f6550a319f595428c67c6550a31b7d8d428c6dc6350a319fd94428c67e6510a319f594428c6de6310a31b758c428c76e528ca31db54a328c6f6618ca31bd586328c76e524ca31db549328c6f7614ca31bd185328c6be640ca31af590328c7cd320ca31cfd53418c73c54d0631cf952418c73d5490631b798e418c6dd6390631cfd51418c73c5450631cf950418c73d5410631b798c418c6dd6310631b7597318c75d65cc631d7d53318c75d54cc631b7983318c6f565cc631dd597318c77b50942319f992508c67d64942319f98a508c67d6294231afd91508c6bc64542319fd91508c73f64542318fd91508c67c6454231cf191508c63c64542319fd89508c67c6254231de540508c67e62d51319f58b544c67e60d51319f583544c73f54951319f992544c67d6395131d758e544c67e62951319f58a544c67d6195131dd586544c67e60951319f582544c6ef6255131bb189544c6fb6055131be181544c73f64551319fd8d544c75f63551319fd89544c76f62551319bd89544c67c6255131db189544c66c62551319fd85544c77761551319fd81544c77b60551319ed81544c67c6055131de181544c67860551319f994544c73d5415131cf990544c75d63151319f988544c67d62151319f980544c67d60151319f997434c73f54d0d31cf153434c6f661d0d31bd587434c67e6590d31b7996434c75e6590d31b7592434c75e5490d31d7152434c6de6190d319f195434c73f5450d31cf151434c6f76150d31bd185434c75c6550d3197195434c79f6450d31e7d51434c75e5450d31d7151434c79c5450d31c7151434c7d76150d31b7185434c7d46150d31b5185434c67e6510d31b798c434c79d4310d319f993524c67d64d4931d790f524c75d43d49319f983524c67d60d4931dbd4a524c6bf6454931af191524c6fb60549
  | 29 => 0x21076e5210841db54842107ad4210841bd98442106f561108419fd97321067e65cc8419f597321075e53cc841d754f321067f658c8419f996321067d658c841d794e321075d538c8419fd95321067d654c8419f19532106bf644c841af191321075e534c841d754d32106f7614c841bd185321067f650c8419f994321067d650c841af99032106bd640c841d794c321075d530c841d794f411075d53d0441e794f411073d53d0441e754f411071d53d0441af98341106bd6490441cf952411075e5390441d754e41106f56490441dd95241107b65490441f594e41107d553904419fd95411075e5350441d754d41106bf6550441cfd95411063f6550441e794d411073d5350441e754d411071d5350441afd85411073e5150441af18141106f76550441ddd9541106776550441bdd9141107b76450441dd95141107b65450441f594d41107d55350441ed90d41107b44350441ed90941107b44250441b798f50106dd63d4041d794f501075d53d4041d794e501075d5394041ded42501067e63940419f58e501067e62940419f58a501075e5354041d754d501067f63540419f18d501067f62540419f18950106de6314041b758c501075e5314041d754c50106ee6214041bb58850107795014041d798f54cc67e62d53319f58b54cc77561d53319f98354cc67d60d5331cfd5254cc75e63953319f98a54cc67d62953319f98254cc67d6095331cfd9154cc67f62553319f18954cc67f60553319f18154cc73d5415331bb98854cc6ed6215331cf99054cc75e63153319f98854cc76e62153319b98854cc67d6215331db58854cc66d6215331dd58454cc67e60153319f58054cc73f54d0f31cf15343cc73e5490f31cf55243cc6f66190f31bd58643cc75d6590f31d795243cc79e5490f31e755243cc75c5490f31b798643cc7d66190f31f558643cc73f5450f31cf15143cc6df6550f31d7d9543cc79f6450f31e7d5143cc75e5450f31d715143cc79c5450f31c715143cc6dc6150f31cf95043cc73d5410f31e750c43cc6f66110f31bd58443cc76f5294b319f99252cc67d6494b319f98252cc67d6094b319fd9152cc67c6454b31d790d52cc75d4354b319fd8152cc67c6054b31af99052cc6bd6414b31db54852cc67f65d0b319f99742cc67d65d0b31cf95342cc73d54d0b31b798f42cc6dd63d0b31e750f42cc67f6590b319f99642cc67d6590b31db94a42cc76d5290b319fd9542cc67d6550b319f19542cc73e5450b31cf55142cc79d4350b31db94942cc76d5250b31bdd8542cc6f46150b319fd9442cc67e6510b319f59442cc6de6310b31b758c42cc76e52ccb31db54b32cc6f661ccb31bd58732cc6be640cb31af59032cc76e520cb31db54832cc6f6610cb31bd58432cc73e54d0731cf55341cc6de63d0731b758f41cc79d43d0731cf
  | 30 => 0x7f6354241d7d8d509065f63542419f18d509075c63542419718d509067f62542419f189509077950142419f98b535067d62d4d419f983535067d60d4d41d7d4e53506ef6254d41bb18953506fb6054d41be181535075d5314d419f988535067d6214d419f980535067d6014d419f99743506be65d0d41cf997435073c53d0d41af98743506bd6490d41d7d4e435075c5390d41bd98643506f56190d41d7d4d435075c5350d41bdd8543506f46150d41e7d8d435079f5350d41cf14d435079c5350d41c714d43507b76150d41af18543507b46150d41ad185435067e6510d41af990435079d4310d419f98f525067d63d4941cfd0f525073d43d49419f983525067d60d4941dbd4a52506df6354941b718d52506fb6054941be181525076d52149419f98c525067d63149419f980525067d60149419f997425076f5290941db14a42506f66190941bd586425076f5250941db14942506f76150941bd185425067e6510941b798c42506dd63109419f997325067d65cc9419f19732506be64cc941af593325079d43cc941dbd4b325076c52cc941bd98732506f561cc9419f996325067d658c9419f196325075f538c941d714e325067f654c9419f995325067c654c941e750d325067e650c9419f594325067c650c941af99032506bd640c941d7d4c325075c530c941dbd48325076c520c941edd0f41507b543d0541af58e41507b751905419f98f505067d63d41419f98b505067d62d4141ded4250506df6354141b718d50506ef6254141bb189505077950141419f98c505067d6314141cfd0c505073d43141419f988505067d6214141cf904505075f5394c419f98a531067d6294c419f982531067d6094c41d7192531075f6294c41d798a531075d6294c41d718a531075e6194c41d7186531075f6094c41d7982531075d6094c41d7182531067f6254c419f189531067f6054c419f181531075f6554c41d7991531075f6254c41d7989531075d6254c41d7189531075e6154c41d7185531075c4154c41d7d81531075e6054c41d7581531075c6054c41b798c531075d5314c41cf953431075e53d0c41d754f43106f661d0c41bd587431067d6590c41d754e431067f6550c41cf951431075e5350c41d794c431075d5310c41e750c43106f66110c41bd58443106de63d4841b758f521075e53d4841d754f521075e5394841d754e521076f52948419f98e521067d63948419f982521067d6094841d794d521075d53548419fd8d521067c63548419fd81521067c6054841b798c52106dd6314841d794c521075d5314841db54852106fa6014841be580521075e53d0841d754f421076e52d0841db54b42106f661d0841bd587421067d6590841d794e421075d53908419fd95421075e5350841d754d42106de6310841b758c421075e5310841d754c4
  | 31 => 0x94432ddd46510ca7e64944329f592510ca7e60944329f582510cb3e5454432cf551510ca7f64544329f191510ca7f60544329f181510cabe6414432af590510cb3e5414432cf550510cb755114432be980510caf96014432af993500cabd64d4032cf953500cb3d54d4032cf952500cb3d5494032ded42500ca7e64940329f592500ca7e61940329f586500cb3e5454032cf551500ca7f64540329f191500ca7f61540329f185500cabe6414032af590500cb3e5414032cf550500caf66114032bd584500cb795014032d7d4e53d067e6294f419f58a53d067e6094f419f58253d067f6254f419f18953d067f6054f419f18153d075d5314f41bb98853d06ed6214f41d794f43d075d53d0f41bd98743d06f561d0f41cf94f43d079e53d0f41e754f43d06be61d0f41ed98743d07b561d0f41afd9543d073f6550f41e7d8d43d079f5350f41cf94d43d079c5350f41af18543d075e5310f41d754c43d079d4310f41bd98443d06f56110f41dbd4a52d067e6394b419f58e52d067e6094b419f58252d067f6354b419f18d52d073f4354b41cf50d52d067f6054b419f18152d06de6314b41b758c52d076d5214b41db94b42d076d52d0b41bd98742d06f561d0b41b798c42d06dd6310b41db94842d076d5210b41bd98442d06f56110b419fd9732d067e65ccb419f59732d06be64ccb41af59332d075e53ccb41d754f32d079d43ccb419fd9632d067e658cb419f59632d076e528cb41db54a32d067f654cb419f59532d067c654cb41d794d32d075d534cb41e750d32d076e524cb41db54932d06f7614cb41bd18532d067f650cb419f99432d067d650cb41af99032d06bd640cb41b798f50d06dd63d4341bb98b50d06ed62d4341ded4250d067e63943419f58e50d073f4394341cf50e50d067e62943419f58a50d067f63543419f18d50d067f62543419f18950d07795014341d7d4e539067e6294e419f58a539067e6094e419f582539067f6254e419f189539067f6054e419f181539075d5314e41d794e439075d5390e41bd98643906f56190e41d794d439075d5350e41bdd8543906f46150e41e750c439076f5294a419f98e529067d6394a419f982529067d6094a419fd8d529067c6354a419fd81529067c6054a41db548529076e5290a41db54a42906f66190a41bd586429076e5250a41db54942906f76150a41bd18542906de6310a41b758c42907ad4210a419fd97329067e65cca419f59732906f661cca41bd587329067f658ca419f996329067d658ca419fd95329067d654ca419f19532906bf644ca41af191329067f650ca419f994329067d650ca41af99032906bd640ca41af597419073d65d0641cf54f41906be60d0641bd597419077565d0641ded42509067e63942419f58e509067e62942419f58a50906df6354241b718d50906
  | 32 => 0x2b3189434ca7e6510d32b798c434cb9d4310d329f997424cb3f54d0932cf153424cade63d0932b758f424cb9d43d09329f996424ca7f65509329f595424ca7c6550932cfd51424cb3c5450932b7d8d424cadc6350932e750d424ca7e6510932b798c424cadd6310932f390f324cbcd43cc932b7d92324cadd648c932f3d4a324ca7e64d45329f593514cb5e43d4532d750f514ca7e60d45329f583514cb775194532afd91514cabc6454532bed81514caf86054532dd544514ca7e64145329f590514ca7e60145329f580514ca7e64d41329f593504ca7e61d41329f587504cb7b5094132afd91504cabc6454132bdd85504caf46154132de540504ca7e64141329f590504cb5e4314132d750c504cb5e32141329f984504ca7d61141329f98f540cb5e63d50329f98b540cb6e62d50329f987540ca7d61d50329f983540ca7d60d50329f596540cb3f54950329f986540ca7d61950329f982540ca7d60950328f596540cb3e6395032cf18e540cb3e6295032cf18a540cb3f6195032cf986540cb3d6195032cf186540cb3f6095032cf982540cb3d6095032cf182540cb3f64550329fd85540ca7c61550329fd81540ca7c6055032cfd95540cb3e6355032cf18d540cb3e6255032cf189540cb3c3255032cfd85540cb3e6155032cf585540cb3c6155032cfd81540cb3e6055032cf581540cb3c6055032af990540cb3d54150329f990540cb3e64150328f990540ca7e6315032d798c540ca5e63150329f988540cb6e62150329f984540ca7d61150329f980540ca7d60150329f992530ca7d6494c329f597430cb3e54d0c32cf553430ca7f6590c329f596430cb3e5490c32cf552430cb5e5390c32bb98a430caed6290c329fd95430cb3e5450c32cf551430cb5e5350c329fd94430ca7d6510c32cf950430cb3d5410c32e750c430caee6210c32bb588430ca7e64948329f592520ca7d65d0832cf953420cb3d54d08329fd96420ca7d6590832cf952420cb3d5490832b798e420cadd63908329fd95420cb3e5450832cf551420ca7f65108329f994420ca7d65108329f194420cb3e5410832cf550420cade6310832b758c420cbad4210832cf953320cb3d54cc832d7d53320cb9e54cc832d7553320cb9d54cc832c7553320cade60cc832cf952320cb3d548c832b758e320cb5e538c832eb952320cbad548c832bb58e320cb6e538c832f394e320ca7f654c832cf951320cb3d544c832b7d95320cb5f654c83297d95320cb5f544c832e7951320cb5d544c832e7551320cb1d544c832b7d89320cb5e524c832f3d09320cbcc424c832b7181320caef654c832dbd95320ca6f654c832eb951320cbad544c832bbd8d320cbcf634c832db94d320cbce534c832f3d0d320cbcc434c832af993510cabd64d4432cf953510cb3d54d4432cf952510cb3d54
  | 33 => 0x9643ccb5e5490f32e795243ccb9d5490f32d715243ccade6290f32f398a43ccbcd6290f32cfd5143ccb3c5450f32b7d9543ccb5f6550f32e7d9143ccb9f5450f32d795143ccb5c5450f32e715143ccb1c5450f32b718943ccb3e5410f32cf55043ccb9d4310f32bb98843ccaed6210f32cf95342ccb3d54d0b32b798f42ccadd63d0b32e750f42ccb3e5450b32cf55142ccadf6350b32b718d42ccb9d4350b32b798c42ccadd6310b32eb50842ccb7751947329f99251cca7d64947329f98251cca7d60947329fd9151cca7c6454732d790d51ccb5d43547329fd8151cca7c6054732af99051ccabd6414732dd54451ccabe64d4332af59350ccaf661d4332bd58750ccb7b50943329f99250cca7d6494332d790e50ccb5d43943329f98650cca7d61943329fd9150cca7c64543329fd8550cca7c6154332de54050ccb5d63d5232db98b548ca7e61d52329f587548ca7e60d52329f583548cb3f54952329f986548ca7d61952329f982548ca7d6095232cfd91548ca7f61552329f185548ca7f60552329f181548cb3d5415232cf990548cb5d6315232db988548ca7e61152329f584548ca7e60152329f580548cb3e54d0e32cf553438caee62d0e32bb58b438cb3e5450e32cf551438caef6250e32bb189438cb9d4310e32cfd53428cb3c54d0a32cf952428cb3d5490a32b798e428cadd6390a32cfd51428cb3c5450a32cf950428cb3d5410a32b798c428cadd6310a32b7597328cb5d65cca32d7d53328cb5d54cca32b7983328caed65cca32db597328cb7751946329f992518ca7d64946329f982518ca7d60946329fd91518ca7c64546329fd81518ca7c6054632dd544518cb7b50942329f992508ca7d64942329f986508ca7d6194232afd91508cabc64542329fd91508cb3f64542328fd91508ca7c6454232cf191508ca3c64542329fd85508ca7c6154232de540508ca7e61d51329f587544ca7e60d51329f583544cb3f54951329f992544ca7d6395132d758e544ca7d6295132db58a544ca7e61951329f586544ca7e60951329f582544caf76155132bd185544cafb6055132be181544cb3f64551329fd8d544cb5f63551329fd89544cb6f62551329fd85544cb7761551329dd85544ca7c6155132dd185544ca7461551329fd81544cb7b60551329ed81544ca7c6055132de181544ca7860551329f994544cb3d5415132cf990544cb5d63151329f984544ca7d61151329f980544ca7d60151329f997434cb3f54d0d32cf153434caee62d0d32bb58b434ca7e6590d32b7996434cb5e6590d32b7592434cb5e5490d32d7152434cade6290d329f195434cb3f5450d32cf151434caef6250d32bb189434cb5c6550d3297195434cb9f6450d32e7d51434cb5e5450d32d7151434cb9c5450d32c7151434cbcf6250d32b7189434cbcc6250d3
  | 34 => 0x50a7e6510d42af9904350b9d4310d42ebd0f4250bad43d0942af58e4250baf52909429f98f5150a7d63d4542cfd0f5150b3d43d45429f9835150a7d60d4542ddd465150adf6354542b718d5150afb6054542be1815150b7551145429f98c5150a7d63145429f9805150a7d60145429f98f5050a7d63d41429f9875050a7d61d4142ded425050adf6354142b718d5050af76154142bd1855050b7950141429f98c5050a7d6314142cfd0c5050b3d4314142cf9085050a7e61141429f5845050b5f5394c429f9865310a7d6194c429f9825310a7d6094c42d71925310b5e6294c42d718a5310b5f6194c42d79865310b5d6194c42d71865310b5f6094c42d79825310b5d6094c42d71825310a7f6154c429f1855310a7f6054c429f1815310b5f6554c42d79915310b5e6254c42d71895310b5c4254c42d7d855310b5e6154c42d75855310b5c6154c42d7d815310b5e6054c42d75815310b5c6054c42b798c5310b5d5314c42cf9534310b5e53d0c42d754f4310aee62d0c42bb58b4310a7d6590c42d754e4310a7f6550c42cf9514310b5e5350c42d794c4310b5d5310c42e750c4310aee6210c42bb5884310b5e53d0842d754f4210b9e53d0842cf54f4210b9d53d0842c754f4210abe60d0842af5924210b3e5490842d794e4210b5d5390842bb5924210b6e5490842eb9524210bce5390842f354e4210a7f6550842d794d4210b5d5350842afd954210b3f65508428fd954210b9e5350842cf54d4210b9d5350842c754d4210abf6250842cf9494210abc6050842bbd954210b6f65508429bd954210aef6450842ebd914210b6e5450842eb9514210bce5350842f354d4210bae4350842eb10d4210ade63d4442b758f5110b5e53d4442d754f5110b5e5394442d754e5110b7751944429f98e5110a7d63944429f9825110a7d6094442d794d5110b5d53544429fd8d5110a7c63544429fd815110a7c6054442b798c5110add6314442d794c5110b5d5314442dd5445110afa6014442be5805110ade63d4042b758f5010b5e53d4042d754f5010b5e5394042d754e5010b7b50940429f98e5010a7d63940429f9865010a7d6194042d794d5010b5d53540429fd8d5010a7c63540429fd855010a7c6154042b798c5010add6314042d794c5010b5d5314042bd9845010af56114042de5405010b5e63d5332db58b54cca7e61d53329f58754cca7e60d53329f58354ccb3f5495332d798e54cca7e61953329f58654cca7e60953329f58254ccb3f64553329fd8554cca7c61553329fd8154cca7c6055332cf55054ccaf66115332bd58454ccb3e6415332d798c54ccb6d62153329f98454ccb7661153329d98454cca7d6115332dd58454cca7561153329f98054cca7d6015332cfd5343ccb3c54d0f32cf95243ccb3d5490f32bb98a43ccaed6290f32d75
  | 35 => 0x661d4843bd5875210f9d4394843dbd4a5210e7e61948439f5865210e7e60948439f5825210f9d4354843cfd0d5210f5e4354843cf50d5210f5d4354843c750d5210e7f61548439f1855210e7f60548439f1815210f9d4314843db5485210f9d43d4443bb98b5110eed62d4443e750e5110f7751944439f98a5110e7d62944439f9825110e7d6094443e750d5110f3f4354443d790d5110f3d4354443d750d5110f1d43544439fd895110e7c62544439fd815110e7c6054443e750c5110f755114443e750f5010f9d4394043ded425010f3f4394043d790e5010f3d4394043d750e5010f1d43940439f98a5010e7d62940439f9865010e7d6194043e750d5010e7f62540439f1895010e7f61540439f1855010f9d4314043bb9885010eed6214043bd9845010ef56114043de5405010f5f5394f429f98653d0a7d6194f429f98253d0a7d6094f429fd8553d0a7c6154f429fd8153d0a7c6054f42d754c53d0af66114f42bd58453d0b5e53d0f42d754f43d0aee62d0f42bb58b43d0b3e53d0f42e794f43d0b9d53d0f42af98b43d0bae62d0f42eb58b43d0abf6550f42cfd9543d0b9f6350f42e7d4d43d0b3e5350f42e714d43d0abc6250f42d794c43d0b5d5310f42e750c43d0aee6210f42bb58843d0b7751947429f98e51d0a7d63947429f98251d0a7d60947429fd8d51d0a7c6354742cfd0d51d0b3d43547429fd8151d0a7c6054742b798c51d0add6314742dd54451d0ade63d4342b758f50d0af661d4342bd58750d0b7b50943429f98e50d0a7d6394342cfd0e50d0b3d43943429f98650d0a7d61943429fd8d50d0a7c63543429fd8550d0a7c6154342de54050d0b5f5394e429f9865390a7d6194e429f9825390a7d6094e429fd855390a7c6154e429fd815390a7c6054e42d754c5390b5e5390e42d754e4390aee6290e42bb58a4390b5e5350e42d754d4390aef6250e42bb1894390b9d4310e42af5974290b3d65d0a42cf54f4290abe60d0a42bb5974290b6d65d0a42ddd465190a7e63946429f58e5190a7e60946429f5825190a7f63546429f18d5190a7f60546429f1815190b755114642ded425090a7e63942429f58e5090a7e61942429f5865090adf6354242b718d5090a7f6354242d7d8d5090a5f63542429f18d5090b5c63542429718d5090a7f61542429f1855090b7950142429f9875350a7d61d4d429f9835350a7d60d4d42d7d4e5350af76154d42bd1855350afb6054d42be1815350b5d5314d429f9845350a7d6114d429f9805350a7d6014d429f9974350abe65d0d42cf9974350b3c53d0d42af98b4350abd6490d42d7d4e4350b5c5390d42bb98a4350aed6290d42d7d4d4350b5c5350d42bbd894350aec6250d42e7d8d4350b9f5350d42cf14d4350b9c5350d42c714d4350baf6250d42af1894350bac6250d42ab18943
  | 36 => 0x1c001003c0090014004001c000000400b000c0000008014000001900040190028000000400a002c00d00040000000000003000a000800b00e800700080000020000001002000000050000001000800a0010009000c0110038000000800400700090008003001000500140060060000001000100040010004005000000000000000034002000000e00080020004027001c00300040010008000000c002001000300080020000000000800400280040004003000000e00000190000001000000200040010008000001801e00040030000001000000200140000020005000000900040010008002001000300200050008000000800b000800100080000008000000c00000140060010002000001d000400e00b80010000005004c0060000004001800300136f5294b439f98652d0e7d6194b439f98252d0e7d6094b439fd8552d0e7c6154b439fd8152d0e7c6054b43db54852d0f7751947439f98a51d0e7d62947439f98251d0e7d60947439fd8951d0e7c62547439fd8151d0e7c6054743dd54451d0f7b50943439f98a50d0e7d62943439f98650d0e7d61943439fd8950d0e7c62543439fd8550d0e7c6154343de54050d0ebd65d0e43cf5974390edd65d0e43d75974390edd62d0e43b75874390ede60d0e43dbd4a5290e7e6194a439f5865290e7e6094a439f5825290f3f4354a439fd855290e7c6154a439fd815290e7c6054a43db5485290f7751946439f98a5190e7d62946439f9825190e7d6094643cfd0d5190e7f62546439f1895190e7f60546439f1815190f755114643ded425090f3f43942439f98a5090e7d62942439f9865090e7d61942439fd895090e7c62542439fd855090e7c6154243de5405090edd62d0d43b75874350ede60d0d43e7d4e4350ebd6290d43af5864350ebe6090d439f9875250e7d61d49439f9835250e7d60d4943dbd4a5250ef76154943bd1855250efb6054943be1815250f6d52149439f9845250e7d61149439f9805250e7d60149439f98b5150e7d62d45439f9835150e7d60d4543ddd465150eef6254543bb1895150efb6054543be1815150f7551145439f9885150e7d62145439f9805150e7d60145439f98b5050e7d62d41439f9875050e7d61d4143ded425050eef6254143bb1895050ef76154143bd1855050f7950141439f9885050e7d62141439f9845050e7d6114143af5924310f3e5490c43b75924310e9d6490c43d79524310f9e5490c439fd954310ebf6550c43cfd954310e3f6550c43afd8d4310f3e5350c43b7d954310f5f6550c4397d954310edf6450c43e7d914310f5e5450c43e79514310f9f6550c43a7d954310f1f6550c43e7d894310f9e6250c43e75894310f9c6250c43e7d854310f9e6150c43e75854310f9c6150c43e7d814310f9e6050c43e75814310f9c6050c43e750f5210ef
  | 37 => 0x40000044003003000200100080004001001000000200110018015000801300000010004000000001a0028001008401a00240040010015000c01000240000000000000c00e0010000001c007000c008000000c000c000001c000000002c001000000bc0070018003005c00000140000028000001400b002800400080000000007000c000000c00100400010004000000400100040040004026000400000000120000000000c001000800100000000014001000000000000030058000007400000080000014003000c00000040160004005000000100000090000003000c00500000010000000004c01c00ac0000004003002401500680010000005000000b002000c0004001000802a000000000040000000003003c003002c000002800b0004004002c00000180000018000002000100000000044006001400d0000004003c00d000800800100090014005000c000000000100000060000000002c01d0008002000c007006800b001c0000098003000000c0000001001c00200600000014004000000a0014005005000300000040024001000400300240020024000001c00b00000000024000004800a00040010034002000c004001c0030008003003c002000800900580020000000000c0030004006001c00600000030008012000000e001c01f000400c0000008000800c000c00d000000e00000010004015000000300100000008019000c015000800600000010000001000c01e004000100440000028000001c00600000000010001002c002000c016000c000003000100000020030010002800100380080020002002c01100000310000000000000a000001400000120058000001000600080030004000000400500040170000016004000500080000004000000400200000000004000003400400000020018003001000c00180000010002003c00a00000130000000000402a00000060010002001800000180030018001000c001000c004002c00f005400000300000004006001400300e800500140010000000000801b00080120004036006000000a4015000000000100010000009003c0110008000002c0000000005000c000000800c0010003002400700100000038003000800b0028004006000200040040000008001005a00000020000005001000100280090000005000401100180010004003000000000040090000000002c0010008003001000000140000004001001000000840070034000001c02d00040000104000001000500000020008000000400100140050028008001400900000000000003009800400040070004003001000000000020000002001c00500000050000000000c00200000000058001000c0090004001000000800e00040014002000c01600000000034007000001f00000000098007001800300000020
  | 38 => 0x80000004001000800b000c003002000400000050000000007c00000080000010010000c000007c00200080020118000006c0150008006003c00300180040014000000c001000c00000000110000002000400200040000078005003001800040040050003000000f000801100000000014006003c008001000a00040020000003000000000100130008008000000000080000000007001800f00040000020000000800300000000000006004c0010000001006c01300100000000002000c0020008004000000a000400800040010008000000000700000220020000004000000a400300080010024002000003800080050014003000402d001800b00200020000000000801900040030018000000c015000c00400000050000000000001b000400000000060004001002400800000060014002001802d0018006000000e002000200000020000002000400200000040008008002400000080010018006003800200080000000013003c0000028004000000c000000c004402000080000010006004c0000010000000c0000000004000400100080030000002001000a0004000002c00a004401300000000004004000c000004400000080020014000008400200140000000005000401d0000000003c00500100000000002001c00e00200070090009000400100140010000008000400000000020000000000000100000090024003000000b000000b004800000080000000011000c002000c0000018003002c00200080010028007002000100000040004000002800c002c0080008000000000e000400800040000000000003c002000c002003000200000170030001000c00600040000018000000000000080030004001002000000200090000003000000b0014001000800400080000000000000c002000c000000000200000000000008000000400000150018013003400100140000014001000000c0000000002c000000400300000090000000001c000000000c000000000000010008001000000c003800200080000014009005c0120004011004000700080050008006004400d000800100000080008000001c006002800c00300000000004002001100240020010000000003e0000016000c0040088006004c006001400000000000000002000c00000000000004000003c0010000000000c00100000010000005000c001003400a0014000005801a000000a008400100000010010007000000600080020004009000800600040030000000000400800080020000001000c002001000b000000c00280050004000002400000000010008006000000b01b8002001000600300150010000001400c002c00000180000000000006c000000c0020018001000000c00280120008001001c00000000000030006000000d0018010001000a00180010000
  | 39 => 0x4002001400100040050000001000000c001000400040040004001002000000400050004003000c004002c00300bc01500080000008004000000800000000028000003400e000400200200080008004003000600040000024003001400000040010048000001c00a002c00300200070000005000800000140020004001000c00100080030018012000400900000020014039000c00600040060018004001001300000030008005000000100040030004001000c00000000000018003000000000000000060000001800200040080028001003c002000400a0000000000000000000010004000001800000080000004009000401400200000028000003c018000800b000000e0018000003c00f002c002000c0020048000000000000000000000000000c0000004004001c0010014000009c00000100030000004000c00600000000004001000800100000150000004001400300000000000002001000c000000200100000010001000000200b800000000000000013001c00400200000018000003000f001c00f00080050028034000400f0000009000800a004801100580170060002000c001000400700040010084004003c00a000800f0000005001400000000080004001000c011000400d004002c0050003001c039000000000200020030001001400000140000004023002400200000000000002000000000100020000006001400000100080000008000c0000004006000800300100140018001000c0080008012001400000000000070002006000e00300000008003000400000c80010008003000000b000000000000010018000000000100040040004000000000b000000400400000000005002c00300200250008010000001c0008001008400300080000020001003000100000020000000002c00100000010004000001c00f001c0030000000002400100080000010002000002a0038013000c000003c008000001b00480050000009000800000880030054001002400000040200000015000c00b0000000000c00000d4008000c0010024000002000100000010034000000000200000000050016000801200100000000004000400b001000e00000000014006004c000000c0020000007000400d0000003001400500040030000000000400b000400200040010058000008000c00080140014000000c0010024005000001e00000040014018003000d0000008005c000000000c00080000008001002800000e80030008001000400a000400000000010000008009000500080010000005000000000240190004005000000100040000008000001c0100060007001000a00200020014000001400200740020000005000c0030024006003400100040170018000001000a000800000000000000001000400000340000008007001400b0004007
  | 40 => 0x3001c004000c0160008006006c00500000010034000001400000140010010007000c0000010001000000a00380090004001004800200480050000011000400a00000040034004000000c000000000840050024001002000000040000004001002c0010004001001400d00040060014007000c002001c0000008000000c0010004039000400000cc002003c008002800c00140050008015002000c006c002000c00b00840000034000000800100000080000003000c003000c01800000080048011000003d0000026000400100580140008020001c00000140010038024002c00d0008003002800400040270000005001001200440000048014002400d0030000002c00900080020004001004c0080000000001000100a8000000400f000000500000020000000000c0380010003000c0060014002000c0010004000000800c00080030028007000000000300040008001000c0030008001000001400f00010008000000000a002401400040010014001000400200080000000001000c00b0000009000001f000400c0060001000000000080000028001000c001000000c000000500000020024002000c006000000a000000000040070000006000c003000000400000010010008001001a003800400000000000007000c0020018003000000500140000000033001000300080060010001000000e00180050000001000000900180000018000007c0040000002000c00a0000001000c000000400000340060008026002000f002c00b001c013001c02700100060000002003800d0070000007c00000280110008000001800000e8002000000200800000080004000000000100000000000006c004000c00100400090038017001000700080050004015000400c00000170004003004c00d00780000004000000400000180020000003001000100700160038002007c000002c00300140000004000000c00000040050000006000800200000050018006008c003000800000200040000005000000c0000000001000c0048000000000000100000000006001c0010000002001400000000050010004000000100080120048007001400100540000030004000000200000020054015000000000080000030000000401a000400a000400c000c00100000000018000002000000640080030007000c00000000050004000000c01e0004004000800600380110008003002c0300008000000c00000200010000008001000100040190000002002c00d000801400180000008005008c001000c00900000010000000000000000080030004006000000700880090004008000000200040030004000001400300000100018000004c00400040020000003001001c000000100100000004005002c000002802c00600040004000000c014000401f00100030028009000
  | 41 => 0x43d920000000bd213c077f0e10eeca518061b3d014c000000031f80000000484856400024600001664a69afd2bf79ddc0000faa037bdc453a1214687986284d362a19518e0d591c123641a5a207099400034ac7e99574ed213802af0bb60002bce00025b22ed1e7667a04e0ce281361182f2a000186671e000069f0046bc00000ed2bdce01c16741c536609ba357aea02d527d109ea1c8a09a737b32a0001a36688877860c2e7a06087ce682b600111af9043b80000d00000000000000003688f300e8ed60c5c00007ee5e9adb0e7f000010c020618c800034d80001400a1e6e987209ed9db606e3a9c0002eaa7d00000ae9240000000006d3800050db30edcf2e68cec96be88998fa46e000033e0dca6a2266670f21746ada1e600000000002c2073a034a89600007682572f22b8b22db280e0001afaf658000edb9e7000000000002e88130b50c90cabe651288448f21f48f0a361ce4e1a2603d14dea24274ef26a04a8b62a60a4189143a0844eec28000000000000000001ccaa9e78480001f4a6aa00000000003336d23814200026d200036de0002c4495680ce2a40000c1436145ee00000002c3c38d8026bc419182ab0e724b88942000000013d80001e19cd0a7a000006500000002ee075d0000241aeb6c7f8000000360ac240000000000000000008bb800000000004933dc05748de00002c5200003c245c88c4751a9b81f3000025a80009810000000068a0b68f9cc2a9bfe4ef8000f69b376a29103200005d6279b8843d5b280ea53c7caa100000000000e54304816bb804000000000000005b18a4e61f00007960000cee2394e7b08c683a1fd88d7b69c225800076500009f4800029100008691af000022f42aa94bc80f00009db0000471adcc0000054000000000018f41fa99fa7b485f85da25980003d6429c1c9a0000c922510000637800006b00004ad34b4ba680000000000ae10000269800000035840003c6ed7980000001d8482a0000000000002d894a7c40000bf880003be80000000e3ae1200001a43230d882668c98b8e20001bc650304daea10e028d2000000000000001810e3a800028f1c320000c820002bde0001cb0d9723d0000000d0008003008400100000020000000000400200040020004000004c000000800000040000000021001400300040080000023004000b006801a000000000000000000006002c0030000003000800100000100000001000c008000000000540000000016000000700000070014001000400900000050000003006c03f001800900240180004007000001d006c0010000001004400c000000900080040000001002c00100000000024002000000700000100014001003000200140000000000004000b00b80010018000002000b002c00b0030003001c004000400000000000000000000400
  | 42 => 0x260003074018b7ac90bbda04382caa0070ae60000000b20299e80ab5f05ba9a94ca102fa63e2de0ea6a69036000003b12f0a000193a7b307e4c0fa8c80000b3600030962a100007bb283617780d8d57102400000000960704429800015e0000a090aa0afe15c2bddbd44daaa0a405514a6d23258802e16e2c7cb5fa00012d65173756db53b90e741f600001d320a811d80001206f1c2bd2aa03a6c8391ccee5f8ad49df83368460ef601280006c4000063305c8312b04c00000009a01434be8800090c3b8c0000470dfc9eb84dab69000002509f7037636a338483e396ccf320c8998a40a022a4ce00014d00000000e9380000578000c950670120366cc0d907400035a2309b63c7eaae187f91e5e0000d060001a8e000242a9e6225eb70985acb0263cc5cba6801d80000003c900000000c0c96e40003c8600034a65bcb0fc758b06eb678000b2502fe0000000000188ceff25e40000000f4500009098b8eebf8f021ab00000003ae885a90b03a7b8ce2a18ea2e18a3f4b6e8148a00a9fe59c148652225aa192b9421481720cd712207783d900001178a7113ca00012843a2000075900006e435a6e41ba409308000c383d02d4d000000036be1113cf06ee053c0003db20000000e5d00008e68326984a222449189c000000088abb7ae14aa3a0001162ad3832aeb79bea8b7000034c1a040000e42667000077c09c02b2978e000000000033ee0002c3ad5f23b6000329e0000000c32000082491e2c08862ee502a462e63800082a2722eb8000832800039a0000000017eef39bc8480055c000066673a9b8c5453a2c88506f227e8e9a26a15b67332ee2767296c79f18e2a1604bc6309c4a764b0baa220fdeb9225bc25f0a0c6e3aedc38b963c44b969071b381abc80a98c769bacc7d080431c94ead70241239384a27953aa6357a6e6dd421ee514b7426d7a8f02411154bdaa1ba44f80000000a20278bd2241300006dd800000004f400000003dcaf6cb59000081780004462bf40003874479332854da4bc6aa839a4f4b4c4818b21665815629a92a0a7e8361004600000001d1207907dac4c399e7e209124baa1fc0000000725b8a2e801fbe63a9ee2e9a80000000000184911c98d91386740000d09b4f4000363416200008fc98508109334000031200005acf2d0000436800000029ea048000081a2d461f2087000000009f5a32803100005af0000c7c0000b5880005ad992ebc38000c68000084bb50ee52a9b4da0000016f96c2b54015a014800000000000001852000006e3cc93f040e067caf300001420e60d63ac120000b1c840b9f800031960001d0a426b1a800000002a514ca60580004a425600ba295e4689b425562b46b60b5580df1f9e53596d49a18f84423955a00000000000000bbd35de0000000e1ab33400000007d38000f22337e35
  | 43 => 0x2703f61230dfc44d2bb29fc938c18f049686cad3c8430000000091cb7a0000a38bb264643a4c3498000c5a00000002ee62098fccefe388093a0ae8eb29f3aa070c940c5800000019927a1bbc8cbab6ae0002a4a000000059b8910e8988a0e3e00000001ed0709294c9dab3b64e72428c50918a4d7000049a800074b9596cc79d804b5007251115465bc0000cdcac060001b1a5f3376e13101a28de0000af637988e13844c00b90e0021b5a4af8000000164c00038f44b107d40240b0c0d68000a7e33f0842148ab83800098aa7a800000007d70000000000086380009170f86dde86c0000000036bbdae26c180c000221800006da29780002898bb000000006e21e6618580000000000f5720b400020ee6cc0016042293000027da0000f40cb222bc0000000a1f8000583a57a00006146890000e0eaec4c40114ab6396c80a4af4600000000000000000352e7e60000000244000027feb050f34908800023b0000c1f8e0c93586a84fb3afa4bb1f7ef073d16d6e26822322ac6af5b12a0002928ee4800060d2c7ee2d9a92000110a0002f3248f91740a73332d12005c6242cc852c3506db822eca4c8798655b4be170aba8674b624d36bb222d2ac9e8640be6be733fef12202c308acd0119a1ac1feab582bf351cf093456dc4240e2ab90ae76f999a76300002c592a09a989b22ae04b007809de43b2c6a60ab70af192e7c11e80009fa26440501a1a4d2305cbbe967acf9943215132006570000c0ab5a0297329666c800021805e873e97fe3b18000e2414a0c9bab86a958fc01f808180d91f0eb8690fc238830200026baf01adf832c0188dc33b881b8285265600000003d5af44a3e4c138d08d760000000000000033aa80d000000000000001a2a00001e848dafc20000000c1e28a200033fc6822064e3f2ea8000000013a17f079f82aed82000000000004ac000078c9586917b92a82e8ed8a5f191c2c01f92072a0ec00027128f38ec2eb5853a56b2b48000000000000000000000000000051f889a00000001948000514000000000000000d760000916ea780006d98a7e00000e6a5cb0ac000069a000049210e0000a298000cc4bad8f61ab0c169bdb8c1a800040a8000000000027d952a74900000000000000000038c9f7c0000000bea000011db170000000000000006552b500000000e4538fe5c9bbcac2c1b2c6d29ffad139094e7d80000003a78aae31fc21ba2a40002d6800000004f71c8e59601ccd41000000000000000000278336a00000000000000c8906f48838000667a9e6ba31ae0b9d8000000343829a1dba17eadd691298bee4d9878ec21318bdd38da0a1b6eecc9aca6a448d528348152000000025389349511b1c494340a87d2f3ca1b19b85a3b3e04f898f6e02800023521b0435b38c1d599eca36182eb3a2ba65f48000cb919
  | 44 => 0x54011ca4fce75b0240ce800000017e09340000331800002faec20ee00003e9babcd6000005350776e611fb49fb3b1c120a29c1903b1216c395800007420002ae2000054ebfdae6e00000002c68ee200000000001ff225da340181a7de55daed0f4900002758386b4812d23cc20ac2b7223c4592fd6d9630ce000221e05c00601a7b20c2a9b1b037400000000000000000000029cca3580005f194f438f8000adc028ad6d00ba0001e52dc200007fa88ca9f31c7e00000000001b380000bce00000007dcb1a600000007f1800031d8592d14bbd4000097804d00000001fa803230ea102038e00029e4e2e1a3862e0ba821e24ac00017ba16c80003ba2dc080a0000a4b0be47938608713174e9191eb49fd927a54896388ab899e45a388ea923222000018a99186f8417835ca4608341dfb632cf7ba5ade427e2221add2edf217a00028fa25934aa91d00000658000d9c287cc4d34ec5bf80000001ba497c0fd8b13ac2218e000000013160003a14eaa8000000000000003f2b4600000000000e1b877041b37d2bc9bd32e97195e9ada60a2d6b9ee61d2818d9380006660450000081e0001652aa6800000000000002620d8698a8000000052ab2cce6c0c1eabe1d4c2018000be9b88a000081a59a80000002a7e4920db8000216094f106e75f2dc4000239ebb03176ee181900000000e72905ab5e0000000234c5ef233802b000045130d000000008122bc8ae533e2c8e8e66a55930c0000000500345c4963b649a5bdc6c0a1564e0300009bb94a801a1a640518a180538a2c000000005d1f900002564ae7a2e47c18458c6505120002396ab496567c0112c613aea4dacb3d4f1e800064c1f261b3000000000009720000dce283e0000f220000a9ac86000081ca5c2dfb883a76e0000a4e800023331ee34c8000b47800000017820c51766a438000a520cea3a2800000000000002c70b170000000311600020b80f7a5d2dfab5ca07180000279e28ca0a30ae279884a180000000134400017e272d9c383529034e5c14be9780eb48aa8c50ce3b972576872e12b826a60caf309c58cc09448af2dc99d40aca9ede97525a4f4715105b12f5a0df916a5abb04253c3934bee121ed9f253eb0bac32be2074486f88461973d30ec9159ac60211c85b0358cc52172a77a0440000000bafa098a888554b0438780bbb6fe383ae501b21b067010a5688738962a00d56c9e2a984de38d87cfb1a4b77af78316980af5b3b68aafb5bca3b9b54df627b8bd03458ece9f78b858ba4ee3b2a80000000713a9e20000000097800074b00001e598aed07a15a8f687d60001986000166005c871e7d92424c95810a7b81044a7400000001f8cd2a00000002d36101b220392998aa1a0852bda2cca0e503508849d82d119b584fe84ccda18d3c8cf8000aad10e639eacd8b008000e
  | 45 => 0xb2339ced2b8be289286dc4b8000000000000000cc2ddb00009ba8000c350bbc00000004f31300a682c74425b9565a680006ad163e85fa5c4c7b02d0c0b00009bf800000028226cd9c4200028e694eb2be82280007d19ac2c80875c5ab12022c28000527b34ce458276000237a0000a0e1a71a107a3bcfe44824c0b311d161d7ab1412a2bb800000780001a9c22a800000033049083988830acf674c0ae20000000235800004b33488da800000000004fa1680d88876a5fc8000410239000015bc9bdb054e0dae808a080000000000000000000000fa00000000000000ecb8000df1800022c2b5600027548ad17322143b14825196ced598bc2c3a1944d883ea7038fc847c313e9520546ad4ad988e1a9e0ad10610caba670c5d2f6e7c703ae9e8b2f0c62242c0000000e4ca950b6ab1380001f4aeeb3bbad4d8000d391be616e89707edb24e33200000000c303ae8422a1902cc652816400016d65738440091013e59c800048316ce0002cfa000292e0e12f3e673ad00b500000b7680009ca07b6976800000000009c63590ae59bbcb382e4468fb8a0671bd609b80a0a9931a8c479a136e5323e27f22924ddd141acfb0d12e1593247942ffa00000009760000bf01eda000000081e991a420162a3148000f67a4fa8c39d3ce31bcb0b953bf068bb904950a324ec38590d018000b9fa334ca4000081f8d224d980006790c0ec798410d48800000022d494cb3422462fbc4a919bcf6281da2f6315e043345ef27272cd81a74c39d96264ff0000125000013b83fe3ca00000002d0ac0016f49d1981a0b7b33c1bb9a4e0000dde45b800030f81582c9880862ca910a1d80000193aaeacb8c4c13c32140000000beb000000000000000000000027210f80001f722c00c9391edf898ec00038d2000000000032600003c98000000057820b2e9cbcb60000000ba402b09d8150a2fea5ec88921a0a0200000001f1200000007e2ae5cf23100e5e68f460000000a0b2fa08eb910c91413047cd94800443c266bc800016a2dcaf068000000244ea6ab46e31389320001ae6000000032f1a2000000005e10000ac38f76da6158e769996e0000de67c231de000004ebd096fa02a0ce60000334f4b1b5c1d6000000014b4ab0153e7790000e118dee9678cb80000fbc4518f3800039d46850000007b5400001840f06000019232a62a49786588045600000007383b1a0003ca600021c0c1c8000000000007e0ffc166b19aa51b066000000000029b656635ce0000000000000041fb2f80000000b5680006a931fa0002b5cb40928ca3286780000feab5a800000036e24fdaf4400003dc00015307aeab361c38576f02bd06bec25d648f20ae000000086580000001fe80001f34d3c2e965d2800085e2244829ab6e172946ce3412deca52a2e0fb304a30d087e7d4113a4c79
  | 46 => 0x1778830058a000160c36735863c300003230000000000089e8f42b293d7e96321c607d98e83690000000114cd4f3b1678213bc4deb618542225463c0b66333b54a5b333941e39976a2c15027a6017a4faa3705b03058b390c78498b7cc65f18041aeae5898fa4b2039371e7c7b094bfa8ff80d12acce4096661e20efce4f808c526368ec9281a4d609bd6e6390467723b343f8acecc3c93d4cc6948c641971a72201500001d26a3727aaafe8f2aee980002d380000000000626000016736369fe1bce5fa32645a19994e693aec21eb3d840e9b4c0001e2653e332c0000000980b830e35306411b00003a800360000fce2d48ed6e2b800094bb47c33d0000a961bca22094560000000b633d52dcb000043d00000001a78d6ab0a09f006d02bd8b80e3d983e00038bca259fa2000000000000000001394ef635f40002dd4eaf8000f70af1400000000000e14be32eba0cf800048900000000000a209b6203d8000db9800050600002d42bbc94928a8b872b8c4b03b0c77886a06d90000e699f7473b1dd200015ba14893f2597800000003cc70815706dca70cf6a82344c42084038937280dad9cb7a8000992398ace20000000000072631aa6cb98ba0002676ab2000000000000002c920000000d3f01d8389bb5a6d8129c8c026f000021c8c9ea92aa6a3a6e4a23d0e00000000003c9e8cc06e44c693640003a1e9d9a56ca693954efd800088dac9c892272032b8000c4d8cfe808800038b24e6255389403e2c40000000000000008042ecabc68000683000001d000000000001a1072ac89b36095bb518cada36c5a28000c419f28d0500003f5013259f0000ed384200000000368127229b2b2000005369a1065e99400008df37a28ceb35ef6d283079580fe14b34285620e6215587ba00012ac37e96b81e40beabe60000ac880000000000267301016790eaaa700000003d4678400000000000e88000000030680003a2e0001e920000000000000000000005650000055ba8c0000000ec40000f31225274e86ca9929bd870abb760000000b9988a40001ee4a2d0ed43ed0a40cf6a9ce502000060f1d660a900003f0a2e85f124b6000040e69f8c680e5bdca000000000000005492e7000025b05b280000000000f63000056820fa6171f24bba00000ff17720319dfa00011d68db80000003016b02b2cacbf3d848f580008f980005c8a700bd5000039d06c4a1ba1cc0002b82000241a29c8830f348bf281bbcf600000225fb33dc3e33424dd6000000018da0000a30bcd189a00026d82038d4400014f69fc02eccbf800077a1d760000000ac033c49e08a3219d00009890c2c00003e460e0000b5805f6178353848ca76400038708b49cc2c4b80004bfab90c520ad80000000d0d0bac76c29be6d4a3140edab28292a2b86fcaeea828a736b4715c4000343a
  | 47 => 0xc22db20889b13c400011b600000000001dc2e61ba82da300000000502000000087e80000000000877a25a73480000000ab4a94121a8d81ed4b4ca586a5d18c800000000000ffebfc80002d82dd80000000681af1c17480008eea7069f2a59600036441f100000000eec45380005df074c0000fec00026b00001520a81000039221482dea884df38d68e8a2de65289920ee0b0a67540000000000000016e00002d70000346cde08000f740000dca2e040000000000000056007b00000000ba280000000000b598000000000042d01b40000000e0bba8e094863000001120d52e22ab5016c63f28dedf6bd28c3a082a00039f0bef80000ea8aba46a227600009b80e88000af935e00000000000000000017e496695ca00000002b18000b4c2ea6a279bfc0000000d4c1ed6ce0a4980000000c27000000000000002444000000000011be000000065ebd188a38348e68000054680003220eb8e128598e8a91024dd0000000000000037f6553b5766a58000000000000000001a2119ad898bb80001466cbc8000135b9c000000000000000000000000000000002652121a55e0000000eeb80000001ebc00000003181d3835700000000000aeb979000000003a323ee000335a35b20d8000212864ab39c8b33a644b699400000ea47438000000000000028e40003a860001e60ca68000caf3ac0ceb800006824c40000000000269200000000000000c8a95b800017648dd31c41f624960000000001b4bc3b9a20a317b2c27892600b33800068e9e948c40aec3f680000000d6600016d02b4b13c15b370e4d8300c1b9ada8000095600000002f4a8d2c3934d2000097edb706d28b9acd23bcb834835affc90e147a7372436000023e02bb39e7a00000669965c782a49ebbc130eb178000cc92e6a6ceaace0419c1c99783ca12a9aee40c00c23258000000000084eb3804ae00004f185a486a099acab3692a658a020003640c42366e0b89950d5bb2ee319000000015d858034cc8738c380002b62aa98000a4f8d383cb0d9a38011ac0001a5c4db9ce243004fe2562df4b0d14e0ce58000000080c0000000040a35259b2f2e58620580000c180002854143125a0000000228b2060003a904820000000293cd0c97d40003ac4e3980000000000295300400000000000000000359e254a00a48721b6765967e0eebb7e01f0c481d88e98d2cb466dab36a88379b6a0000000d6a0000546282810a0000204221697ea408505b28e38f291e94c33f81a005263c72e72000321c35faaa8d7a10b6e0c90d865abb62000293427d32520002abab1400000000000c3e90060ad0d5a80bb1d48c68b9a000000023e1c4000010e2b2f8e22505012e31b9792c21a7449bb1afef30800000000005239cf40663d3e00034306a637880000000df2876e57d00007db0000d6f8000000
  | 48 => 0x6c29401092a06babaf5c000075f948227b8040b6e1ac0c35851c0000bb23af800054cb5ae85980006291aae5fe1cfc000000000000004a680007c300008a4a4040003d5067c04ced5d190e00005f0000229487c95de4a00000000363acc583703718000d832228a8800001a580005d238cad2e000000015380000000b441a00a2b9d8a29e2bfcac48000000266086f36560f9a1445a88c62b57a8e0d3c800008225de2c8215c00017dcf35800034b0000000096860517cacce90f259400000001cba5e7000000026340ef1ec6000223a67700000003850219a8aa5eaad72e7ab67ed7b8000a6e8ca00000000000383eba480b22872feccec00000002af678d3b526df95ee0001e42dada17cab58ce8f6a038000000000002120d3b8bd41811e1e9e7849e5d52f2cc670000000000047f2d74e0b17b08232fdc000176c6af088e00014dccc21f6ee5b96b4e44344c1bf24eed152574e6f89a43b40d48c5b919246b8000efd0bba0002be2b7f89f2eae2a62a301c5436521640001c0a35319fe9131d06e7c94640a21114163139e2641ef8a718daa6cf02423bab6f28dd97c2cb5b3a0da203c40000000000187e000203e6dd15d65a809b60001876dba852e00000000001c8c6e7b5c6d5c3d780000000000317a0002ae80002d160001baa8943824c9da8206c627fa5439adc0f48000be09e2c1e08b240001d2800ea278000000003280000e7355e2fbadaeeb516ec49197a003c0000336acb4002b4a264a324841400000001b98809000057fa85aa5611589733ca46c0b3d2ad50f1a80e8f6a000000083739f400037de38726a29ad115a000000072f2d7600000000001bd279101a8bab182c8441cc47f82f22b16800000004b6160310a135175a1a1ae4ae0a800000000003451b0e6ae215e8e92aaef1aa9404228b7ed10014c1b18e12161ba7ca76824873d98c6e181e2a46700343e83b705290aeee3e89d253ea51cf3690b800000000000cfc6358c0831b01240000000c0bb7b097d20ea0000000beaa84e0003caac439cd40000000000284cb1b845298325fc4ec8a16f3d239c000112adb08000481363e97380421a6020e00011c2f1d09880002e5ab260000f2b9c185eb8212dbea6d60001abe0002c9ad6e80000000a5abf8000022524b0277232e0001fd217d186ac632154159a94a9e4259c2919ade56d090000000000000000000000000000000f60000000367a00000008aa19360000000000000015c9ac65f780004040b402d1198c4a29ce6c0c07be0f000000003da2a0cb48aab8132ace4000000000000001f626238b4c3c18000ac1989600036bae608488864b1400001ac835b9c90000289c94100008e280000002ddc9030e8481300002c61cfe85591361828fb000000006f71e22b979e841c015f00002592376abc02661ae2310873
  | 49 => 0xc604128a09169314c2fa31c0000766de009bac97b9c68a20d9618e860000000008fb35c21fd32b0a56ba58e8622205613bf20003bfe000265c51a3b6aa3e03a4c2d178896db6d200032f6c641e2ebbf35326c514ac9818dcc7bf964e9e521d8a3d250cebc8000f300d64eca96da00010421d2bcbcc9b115c67d1fb00253d0047c82102a782b88d421a2045a308d468360f6d917a95daabcc3090aad5b00003c78000e1d80002f5b9b4cb19b700000000000056000028165fd25fe000000000035e2c34a0b69f1000000000007ee93aa00035023f28000cce39fe993800037d25b8659baf4c839e6a8bc3a1a5c21f2c9b7ac185ce22ba995bbb457ab6f847e1ffc30092b687d99d44af1526c27b8144be3dcc805014a4d494c0824115e98204e4146a67223789d4d51ba30f6220cc7aa357840b2fd4222badc9e594fc96fa98cf4da2b053134648f7a7bc6760296265b720230b4684ca05ea5d3383ca123d8e353836a4e4ab5a0002e6cbbe1326b5108640000000004ae20641056e1068d4273e2642e83a358ce9b8985ce94c60000000f58bbcc821b1ea10d0000aeea34ac1100000001edc2933cde0001cb404a08e837c396ac20161a77180809b30000b6800000000000bf1955cc6daf28dd88938b433af06080000b3f9caa8a7b818b4f80000001c0000023bc0001a58c58969c0001e1ad11041c0003ceaf46ad2ac3880000001aea00000000000558a8f8000dc4a5a6709a00e3260f52081122600000000000000000000000000009d7049c00000009b90bc421700007299c2e46e80006c48000b1b04c8513b826da8322c2d5050ebcd95c8a863d0cdc73aa0d6da5f80d33a5094d00000000000bed20e2a458a1a321000007380004630b88b918000e2d0000000000076b10d2000000000008dae0a066284f8000f338000aed80000000306d20b0407eb19a0d32a446000076ce42040abf607e89109f3863cbccaf158462463943a6c7800070a3760996924417680003a180009b2aed6564939a440343c0fe24a07f6b98000026ac3ef9ff0c3b18a6f393ccce109fde5f213ac851b1c67dc0eaea7710200000aa20001da4f601de6b28bb0488d1a5268f0000f2e98600000ba280c084a4949bde0003566b8ab8deb12a3188e308bc2241f7a86d0a280571166ee52a06390317c5e909ec0000000ed98000cf0bbb000027ce0001802831a4da00036bcc149924690bc2a00016220003650dc52a2800033f26df1c920003c54d16857a7fb9494df10ebc00007108b880a45338d0e68b0980441a994c8a33ac6408000cb48de2a70a14a0000ee002881e63792d7e064a056571963600032342cb08f60003734f3e0fb69ee9a7600017d6a58189e66900000a33b2019a313aee710bc2e82568b5f3cd89dd18228a635a4a999a4af350122e3c1f52367bd3800
  | 50 => 0x373c42eb91e3c00016a8a468000ecd8bc800000008d8ad860000200798b364000000041a04be3440ffa67000000001be21b58f506fd20528cf1dd00002eaef530000000026600007a469d08021f8bc0c000000000a8fe83da0000000373e5a314e600013c2f4f33306b3b1ae00033a80000000000375e04380007f0009600036c600026c81c1a2e013e2f9a3b90e5e8071a301ff2c680002aaa000094ce840000ce683527328000a4e0a880001e022058000b28000050400003ab154a4c493705dd000006c2f8ad628f2666b3c38ac9b95e4a4a470aa83d4e49c330673c93d6691bbc46cabbe4d219b94835397a248bb78000062216d3418bb3019e0cf2f0cb1e9e9e0000ca68c09568000028465a0000d510000000000020b0000137387a000271e0003c2caf680006ac8d6ab3d162c9fa971e00037ba0000000a8d9ff80001bee00013b86723c603eb3c44dfe005647732325419c9e000134e258000087f800083daade0000000179a4f2f4e98686fa2a8ee6abc0840a3d7af3b0d6095281bae82afe630eaeec00016b28608c74bf380000debc96f012986cc8949c87a0000d75074034a000017901ec00000007ba800000012aa160b8a6f040000000232acf000008411d8e3c5267800027c29e980000002eb00003c8400000000000b580000000847800000022d69a2157e7da3744000283820813460003900731800055bbd72bc7a812375ab8a684891a7923d5850e020c47119523f5800037020268a1851000039280000a1082c0000c0ea95277604e200f00000f1800050f000006f934c5f015343863128061132224f80000001ca800032981c600006fe80005320000b2e926e946a268bd38ac22e31d10437800099b9a624442baa000380233c872623c1ae85a232d4a481e9a36fb1d6000106288fa208d4b04325a9920e6951d52b4a349e2300a346a0263291f88980000b2ef1420d05b9a74a2f826b20000000a2182f2ed0251423a841870b1916f002b783102b680003cdc00000003be1736075800096d00007561fa402600009d88ade9ce00004959180d398b62454924ef5da84a0000000a640000be53354e08090c2c796dca9f39c4aa182560d393b0dd339666ed3c0e9cd2eb81302ede03a85fc875184637d8736c60870a5013ab0ab705e21d3a9229428088c5907c08c7b1e2c7db74656880006dbb2b81913b506863a020002616c1b250e47d8af0e95aff00000000bec800004e391a098923ad2580000000000f509f18f16325c25e90860000000000000000000002c880000002cda1940000a9091b23d12ed46b28000000000043095e2678b8f2bd78000c18b88813aabc423800007be8dba0000000000000000000007b60000000255c273a8ea0002fb68ffa80ce6cbcbe0b9a00018b05d870182646732992e77990c0001ea27a2ad
  | 51 => 0x346200000002422610000225c000000090e9894000000000000000000000a19800000014702c50000dcd829871880003df1492000000000000003d327f424a000023f061a4f7b09aa9734c249a2c1a75ab6e8707b694000322ebfb8000aa29f3c4a5b33e09e8000c84809adb10000a87aeeeabe8000345b9b60003a4a14fa894f0c8442afbad14aa40874a26af160003812000095c3058ac05a5ae86d7d8000e07251675080002a91ee86e1a3fc0ed0000e5700005efbaa896e80008770000000137e00026f80003b1e0003bc21242a70c0e23b03aa00000000000034000087b177095637ec187bd4ade18000c1eb25a40611f4a408000b5ba06ccef822ae9e888054f143e4a0b8bebb1843cf1339e03aca2f2e6a1d54f19a4ba38d0f6ce20b892f1b0e1ef17040400021067ac1c56e6e1d6800019c21f40d207f13014d6580007fd00b0899000000035ea78580fc117bc4000017060002d04df0879e0f580002e28416a11ae12d64aaf2ebd8000000165433e800034bb508000000016e351200b271a13c90a29eb800000032a432c86342ceb018cdd177a721a73a8ccb89a7ffa6fc839a9f616115821d52a7a3d998fe00022be0002ea2559a0604721942060000000007f830836f498b82c200013e6000000065d001a0000000f4135acd280000000330000000002a3b00edc88bfc7bdb31899f8a6a0972f9600000007182bb40b2341600005aae872c42eb4800000000002e193581340784195a372616000036d159e5a500003ceb66ac30208e741107aab1043a24815aae64947c54b94122fe00005faaf849e91a161a300504468000445800000024a63dba546000000044cb78c29eb6d66b1310c0750d72799073e036ad2424b0e0a171a4547173a62c209db200000000000000396846a0000000937b66276a31140de1d9ef5bbd68d180f78d8388d074aaf60662008400029ac00c9dde807800084ca528000047e00007ca6eb8000d92ab1cc4800000000d844c20ada6e69bb66c000005cd165a0000c12a3b00004f600008e89d1c2e133983fc2804cc8288cc40a80604a892a351bc6821624a4a2f2cc0a7d2aa25bf35fc2b9359c4b3978c99d32ec347963061232da74dabbe4271cacc7a268e0000000acc3672acf34d80002c8ed5aa4a2536aa964231c08340306071d88e410a8bc66c2093abfe2df2ee28aa86340280b46b31cd8e00005402cde00028be40325701b516d8d93102672500002f402fc11201f064d0ab0581995a2fb227e17c800055c90cece882680dcb6766a280000000c10c1f08f2850000018f81e299e94b80000000c9a8edeca707ecbd2a4483c01a8656a00004829a329212e606a689405510ad67c2b7bea8c3c5e32a299c811b79c3e43a0c9ec000041592769e818563d3ab60c8d8628afa00000000ed21cc101ce
  | 52 => 0x93c2ec840db6fc8ee000000039bc000000062080000000000b032b66dd211e83d8bad0b2a334adcb8000ba3800015c170416db6ec5690000deb8000df000007ef04740000d7a000273cf148fe6dcc357e06b80000000000000000000000000001692ef893763b327fc229873af6fa78cd3d89fed1fa1e26f0a9c09afb2e04e19f94ded0000a1e805800000000000000000155eb6d986e717b4ce2c096789fb8000d632d08c06a00632436c819834d06a098c412c80009b3a742db30eb06ef9bec145a7561e8a466e7e98b0b4ebb609ed1c80861800000000004769728d8a000066ebdb0e4c34b67161516d5225a20e99fe20000ff20198000413865a0f52a82a1c027e000000000000001eb10e80003d3400020f027e055264e198e0000000766326800008ce4180000c5a8e1aac09064dd9067e360966819da3e8978958c06f221ad039752000032800000008140c32dc090ac1f980005ed280a0000e940003b000000000c999e40000327e668a75e7c8126c00024bea4db3408b3871ac02b8064e98fba6e0173e83fb7069bd1a4c14e00a6ee9000030a24c800000004e8185ee21bae0d1a8392be02ee45ddb9c23239e0c1ca1bf85d08000346048e6153a160003b6c00004988b2809276437e0ae680008831acc216ae9c544a6580002e820000000f0b96aa96138c400a2c8af139222a9486b0d91a2fa36db2702e09a905d60e386ea1740893bbd68901ad6addb1c20002708c702e26ad080000003d947229bb231e8000a89bc124f38000374b37aa6ca15800000000001e460003816cfe80001a53a086b6ba546e127becf900000003cb251e1e82000060e0000000d9900009719c3e534a8acb6b000000000000002cb200000001ce3ca00003c8ee56922e00035d2e8124eab60214233ba01a7d508eec3c0e54e1f2c54736a2fc424030cb650d8c0000000d668000efab8aae5497d8292184a62195dc1d4800051aa9f2a200d8e56c1a727578000257ad8440f00008439e9070da9440001fe694780189e380000003868da7b18eb2c0000b6f80000002cb89499aa286b80000002aa400005a04a893d00000000a95134ada0a9d2c52bd2655a8b0639e0ae0ea89a84bc180000000000933336600000009cf9dbc0002b38b3f2a38569925e1529c70273000077f80003d939bad77000075c800083d3020d4814407bc3528816ba12f663bc6c24b62ced7a3ca07090d40001dece2300005a630463b2a3f01a924683e89f801712d4ca110dec580b77e0351fb207794eecdb324211a12662490eaaa89029abb69198000175e0000000ecc92a63ec800000000380001a5e67980008741c524ac9824b4ba91cd3e847cc319022399269809e0000b8b80000000000385b81eb4d00000c2948429bae14eca16d20002d6c0002fbacae8000000334400000000000
  | 53 => 0x800001f86feb353ab22bfbafc3d7a0800002a88c2d824e7861b22efb800000000008a5a3acb7d9eae0002d26180b61200008ae4162274de6800037a1d1a0000000000000000019f80001f8e9dea9260002752940984c00000000002cac3d816e8000000003300000003310e64000082a80000000000b12000032011ea0000000e76abd027c00008f4a8da86209b460728ce0002556ddf27e6d9e2202000000000038ee8e817daa9921d2deaac869e6ad4264b36f049e211a66a805a3f490a4898b53ed268000000000003b154c4172bc6eb6bca239582ea79b26d0000290030119d60000000b6c8000391800000036680003c2200017a80002ed2093392041a8000dae029e00017f6000045ac8f9cbe44f15beb31a200c7429bcbce89bc9740000acc80007aa80000fd00000000000bd98682063800000020040879f9c516ab1801794e4a100f9e069800095980000003516361945450a80001d68986000000000000008a800000000000000237ef389f6a000115000037187140000bd8a5a030019eed9080000001a340f81ee66fc2f725eb0000ad927c830918c057e00002da0ba6ab2864e0002a2ac7394c28449d4e0000000028000000004ac000000007a80002f09ec25d13a8ac331442abc0000f0fa38800039d8137833200000008281e1cb2103b2d8120182fa0af8bce1c1a46f34766f13b9e8768f480000b7c1d18658a8b2198000230c00032d825bb3ce204ab3e78e8d049040550d7ca4d85470e244aa1c7c2520000000000000000000002cee7fb31040000e30b8d0caa3bb842e000398c0003288e7996de2719af439a9fae17380000000f4ad7b00000002a5a00000000472a1c0861ec80003490c47ba92633898e0a514223dd2afe2cc0000a8cb9c8ca4ab3a05ab07633495fc7f2b30c19ea6380000000d7104c6bbd99ea0e434f85c2ad56c5b2488979b4787050000ec608541dd044a45f0000368abf2000000076d3ce60000b343d700000b700000000000000379e00037e80002e1ee133aea986011a9eb021400000000000c449f6354c8d08000bebb948cbd0bc06329bf61863bbedd50000b308000e7a3ac840f8000000277200037f045b2e9e1293c4a0e620768ab00009dc2786ca8800072bbc8041db0a40001b2008c00004f69d08eab01fe00000005d700007a20df8000130a6deb2fa3388cb677320383e22a1426294485cf1c1695e228058e9fc2f009b3e3383d2e00000003708fc603036caced0000a6bb732d723dd417517b2a17897423d392c29f2b7446a99a82dd10be00010dc000006a000000000009cae4924ca69000004e61d5a00032de0000000a9c84fa461a9ca0cc19f6000000047f9e78e998000a189b6c0001354000090e5f9a3c62d22c08b843bb8efe8000d0d80000af3cb8927308c19cad4e000267c4580000
  | 54 => 0xd553056a859756362970065e07b2d5a00005c58d7c1091dca5e51bda7cb81683a731acb0b0fc4e948000a7211969208cd400002160632c7c0e08e5208a05bc00011481453d56b09852a7c52ce6a411fd46778000aac00d2239abecbf2a8d087c00005c380000000000743000096b00005c0b3ea0001b34640000073223800000e8e79328261f78000a050b6aa31a5800003b54a7c0000aa500007e58000c5380009e4b79200000000001b92000191004034ba6d1058eb18800065fb72400030e6b4480000000a04e1f8000cb88f18104979639b8000000143000037f40000000dc580000000bcc567205c8fe107040bb12c00016169eca0120001e96000127e189af641003cfa71a00000003c34000000066100000002cdca24a6264bca4a8e90b7a0d3f91ee91f399835606beac208d8b0f9098da68e90ee691708403b300000000de50000c51800029820dab741426e303c7e4a632dc8670d2a0002b40b7f32e8672ab8e866971c55f026e3c90800ac69ce4d070002bd581b61ad98a00a89182628800074d318400001fad0480001b8b42231fb73aa1a80006da35e4be91c64b3ca8f607cb752ea600003cf11267d31df418d8e28601aa1ac47000069400009b08edcdda00001dcb2460000000080800000000000003488000000000000000000000cd1889ed6537a4000030e0599e4a000365a00001ee32d2c9077a800081a8cd600023ea863344295f0000dff9004bd6390cd568000000000000032aac4904540a424f8db638a80d180000001fceb62aaee29d891e444aab65360a0699a83749dd8000000000032f800066c1bd033612fa0001dda00000000001286000000000038c2eef00007758ff67a71b049b8b30a77531d80001216388399adda82f09c93bc0b8f3ba8000226a90083da8be0b76000328adb3a8cc9230224b20921057a0000ab087b4405152875e854871100e052c83ee4cc24163d63c624aeb05a7403ce0b331ad29b6bc46a1e14200ce10ca825ada2c2a0e50639b3bc6a7b7e42988fe00ec30b298e962e582822c92d0e58b0aa90cb8c8000000000079a0c660001a700003d9c1b6000041f0f5aaeb1df6000000096b826cadf8c5600037d6b931460d251428a171da2af700000e2145e0002210cb40dfe62b34b02ad9ea6665a8100001088b991cd69c519bec0993f8ca3000000000009d039a2d001e380000000eb3800000000003b024c6e81800069bb186b79096cee00000d0121a6474000031c2a348458a7497b9fd00001238000216eb9d000069a80000c415c04691efc0000594e390a2a4c704ba2f72942ba620780003c366e2989215009264f20ea60d7957826310c636c855acf591fa288ad900001e06d4e80008b788a8358800076696a49900000c441800de386241b78e7c00000004b4066e7a31ab0915b370b1d
  | 55 => 0x2a128678eceed1152cd0b9e7215a9b240d898644edb0347a81ba2a689bcc950181892aaa684e587c66e5884234fb8084972d2c75e00001e833f4708b85c0002664000000068a2150224b20a0003150a570000ead83ce80c845c4cb1bc067f0dd8bac95f22a2b204a45386ccc082203c5b78a2bd1446dc029ee157b6d04cba998c17ad5498c0c06b13178088e3a3cd5c8b2ae9fbcf2642b24046528fc5073bdeba13550c07827c0c8acf8b15a9764ce0c8a8cd9b0caf528e838a88843e5133a0670828e3a318a91483e276b9c84495142c37132cecad0506f0f1970d7fa3c29e0269c22b0000ecb11cc648800042a2aecbdf00bc9f81c10da29f9a1990c46a35086c7ac99624ee8b960c23ba2a0aa70e7e134106998f8aab4041e9df093c9ae2c4608cba3679d1a7ad4ab0702102a760002c3601308b2000399c14a07480c7070ca9b937cae20e6c9e21cc0f3b91308f809625988a12a809ebe2d90b6e70e8c6a9cc2478cda380e610800094880006922f7a8d592404b18000122917e3648000000246c0001eac0000000a30abf024da1142d0800000000000002ce288c8000412079c00000008ea00000000000a3faa749538f929a780000b394240001388d37172ae1cb8642d19f580000c7c0002fdab6936304fb84ec103296855e813a00009e4a82298e0002ffeae8802e86a9c7a547a4061ef3cac340b4ea91b95e400030dc9cbae5685303fad378fd05cb372a20f315416891ec8f50000872b40806a8000d030c54adab13285d97ee52418d20000000e2e86bc000296a00000002a5922a342a2602a30fae092a62c78812f4a6010fea590000e448afa000092e000060c5c400000000f36000000094e1be40000aea397296600023126d22b0400021c200513e4bbc92c204f141e00000488d91342893385a0000000acd000000000006ec0000000262802700000003b3ebe7b866000142e000000057d8000bb380001a9800000000000000000000188a39c0f8028d8000ac4000000000820000000000000002a8000000023a0001990000337c0000000ea90000ef680000ad800077c884ebf1084c9553c82f4793e0000024641c8000170000000000000001d4ab802e080000000c469ad411900003c400000000000000276807f10d0be1b0ae11b80000000902c733560bc9338648c36a4603abfe22e03a8096800060da70a90d0000c32800020d940688c0b3e11e0cc482080000000eda00028346a8133c728bc14000232caba8bf0000000092012f660200000002326f5f29544e124768bd9ca483399da43e80000002c3823f8ca4d08000060798ee407800000036a60fa0ac8b828000a0b8000de13484000321e3cf977e0711676f6b000000024906b93286bdf9f028bf8b08ed1938a78fa7d400000002ac84b492189662272bb062009aaad7a29
  | 56 => 0xa88f00000d998000e4b93b40000414d0a86f04b6222e0aea9d800025820000000000000094831c8b893ab4cb11cee69b218ada5bcc800022c876a84020002b6c8baba381a3800030a857e00004d8a2e172400027020001d22327949600002c09392de249d021ccd580000000ad00510000a7f11a66608e92f598000e473562b071b782de1d708da00004049bbaa2c831e0702622555ae060b1b23c34d30a22028c1c924af048a8b7404152c78b2f106681c000000000000000cca562800000039460003500695abe08f70e9601ea97ab8c0dd4c36b1ca747b960e1000b4c9d2e40290b602ea58792ebe1ff63289eca770135ee35877ac222316c9f243cddc80000000d98000349cd8b9750c51056864f261cb0389c8c049f5a3c3823c000228acdbba32acb3358d00a20600000000002cae1ab800048d1870e5d8318a2ead06d759d20db000008d39afc00000005798b72a9b1c9c803111e4001f220f21294d7434803e680000000f9600000000000a2e73c0000d6c0000000000059210b26aebc728f623f61f08fee478000e0aa0d88a539e0e1eb909e8a12138e428086b25a758f6e800033916ba00037b6cfdb7967971df8813a130b35924a000054c00000000001b40eb08000dc687800000000b8e80002ca00008712e384db072cc6f1e7a08981dc7198000141056200014620fc2a44a5f80008810010941a72adec9356e7314b68a9a09c3c831d28b689e842e8c1471ab4a4ad308248feb83889c0000346a988c9425dce9810088ed0a3e000161e9053aee2232346bf2278a46800000000b3cd50800065194589c13cd05d180000e302e4aa4ab980001604190bd40000394e9629eee58919ae2d79cd897a038a5c490f8e4e822e7d5800078c0000d1c00007570a245e788be21f000021dac040003a88000164a00000009af2f9209d062a59091220c100006d400ee8d130d83dc170c20e000000000001a88d7030b8a82ac93964ae726f207203a0e0423665a135cc95436b44b2054200035520003b061658000b1998262e78accd920574d878ef440080001be97144bc07feb64a75a000000094221623b21a0293b268a0b135987bc9612ee824d41e9b1be3fd27d03812a6a00016403f9000065119080000abe000252ca62b85ec780708b2d8fdc0b2bd1022d3178cde2dbc761b6a2c2f019a77bba741ba9760500aa787ad8ace954940a000324485c1912d55b9aeaf080003cbaa0ea00086200026d400011087801812b05a9b00012c726e8000006c8b92ab991ce30daa4c0003c924b900005130dbc647800045d9d44e5a07b8f692e360002ff4299a97884aa4b8ef7090a234b1b8047ba3a0000cdeba510c80000000b528c58b3c0bde2f2bb424d0024018701781ac933e00000000003d0878514727622304000343e00000000003766294af7000
  | 57 => 0xe92472ef99082a842fe40001ec0dd2bb729b1938e854abea2ef87f205bb1122ce06ecee580001e6a4e2cd4b03cc58000000000004ba140e99500000001c0c7e08000a42800000034c6000000070c00000000e448f10c1a5a0acea0d58484b5639dc9728cba6f80b125741f66e51382208e07aa755876000000000003c1eb0a0d78b833a7053ca3be5f42c6400028b6c2280000003098000085e78db70404990f000000003c20160e8900000acbdbc174110ed12a494b7bb0f883807023bc1fdc805a53637201d069a0000d0689ae000296ecb99f168600000907ad7ad978fb80000c0ad6c8000000375c75828560000000baf365272e09d0462000032b1a1c899b75a5333be8cfa08140000000276800058709300001542cee8366e163492f429f5e7b3961400034e086e1646000315a91a800034e80000002da687597b6c3d3a5e000238e19b3b38000057c8ea883eac784d2e8f800021a086af5a80007cc9e5ab220e7ebd30000000000000000008918000e29000057b0a58a801e046b63c3a000334e1da01d2000000052e88dc00009d8369895a00016f6ade919e0002b0aedd33c82709fccd429c3485a1948937300667c80442221c5ad3a00002611d182ff9f864e080004c826c0000028e01b1b260001ec42088ccc0001c48000022254303be000000042126142608000173000028e00002dc3a4458421e03d522b2611172ed1c800090fb7d0f2a3922efb09aca1d31e417b9cb2e3228989c431266aa37a662a9552f31800056c836e000000023eb084c07222c8d51af804c2b1697cadf000027845fe8000e58b7dc95a8000b0c0cdcf74800000021f814cb0de0003210a109c72e6500002cc8f0a71182d8c6e82be2e5000000011d25c600000ab0000000112800025900eb316622e95480000000ee100004ffa5940001aa60003854da106aa000000054136da000000089093a85730000dff2f120003a46dea000082f9d480000f7e000000000020f20001dceec08000c2e11420b8000000036b0d478000bc2127c1fda27c00c00000000000000107800000009be82d296a00000000000000104af4aaea00000000a75b3ca000000060eae3e30f077c1bd9d14e658236802160898387946912decf4810f6848a98200038cca5880000002e2833d98d400034c00b502540000426f5d032ed0b00004da1c7400024fe00002d69161b324e43c5af520e4c9c9a6a8df5017cae833509dbb32ee8d2a5ee92314cc46156c0003c160aab1b2e380114000128ea611bd4cd880002e700006451634def00000002e2c4bbb74e35d1964ad2834264f86e8000000018808728223ae24b305346981260d1e8b5c9d20eb66bb11c00e780000001ef40000000e498000000235c1c7032c33b1d6eb98800000030ee264800087a895000014ae000000084298b60000f
  | 58 => 0xf30ca812dc0000db083f2a0c3de8000adc8b1000012e62850716d3237c8a23842c0bd15d400019b47d080006390b5600000d61c924e000000003773d820001264808169e00019c45ac315274fb9e26e0a83ab003a22c9314e200034e2b091ea4b160436bd4b3c6000315851d00001e30000000155000026a09e7000082f0dac477ac60a66bb5c0239798000031a37a800013f0bdab488000a5c25f600000000002dc8000000000000000003b98d7e10c4000285063606b4d9d09fca7e80000002562d4980008c811b400000009a6a2b6ae0100addda81e51da0744eb96f837ca28c819b2b2d769560ed33d5475b28c49f1849a149235a6370fa40001d02350066a00039e41e29b281cd00001c4a52a720976a0000000dbd8000853a6ae0001b9cc678000b93ad0ee5e3d5ed4400006c2ac1e00000006d5800000000000001dc43738000000069200023a671bb4d66ab082e6d1b08e0080e06ce9212626880007ee0cf0eb1a58edfe80006600000f3a0000000000000000001fc17a245000000001ca0ef80000000248a000000000018b40000a3a8b1b1dce74ab9253b173021591b01d90000bd40c9a5ff2a400000000eedba764c185dcb73a26e4a7994e00013360000000132800057eaf189c73c94653064ce13adfa000251084b2184000287200004b8ef480000000000c86b6164fd39ac09810cc000000000003000001fd6000097200331b40003654000000089580003c131220001e6e00030c4b65a6c4aa33b3cd1d1f1abb61302ef42efe00000000001184be38000800b8eca22aae47dd8baa4908a0864c87a8a7b0f984bf0b90321a5ea9269016a0f101abc0aaacdf984a6f1e0000987ad88e5f00004ab986cbfa00000000000ab6a29a83117ce251bdc8c9ca124c5582f838200002120646bf4351447509a00868c0cbf322d0142a13caaca7e48c1800058a044cabd24f60000000000275092ba8f20001052700a7223551590a8f02704cc89be00014feb6d000051b803e0001f2a923a4d2147ae5266d8a505e2bcfca7500006222e78000149a9a518729071f044d6b25800022c2000323800000000002bca00000000000000b808d0c0a08a9c3473c764410f8e4b2a39217b0000ab600009063d9a9b712280db122c00000000000000000319200038b00002e4200034d40003acc9cc8000000000003711ca00000000002eb40000a00299268c5bb86b88e080000002d4899b354ec688000adf1762afd8000e2b36e405d80000000000c021632d6203d03e082f633425c0271261a3c495ae0000000327000017f99721b399e06c5bbaa455a322ddc00f28b113a25db8000e4621e4abf182854e8b04d140000000000000001f40000000d2613508150bf6ce4a90891884a0058a09e00000000003ae60000d24b4e20408ecb93c1d437b8c3d88324
  | 59 => 0x12188e6315c0000000555000000000004390000c66000095f8ac4f082d5c81f317e93d254cf0c0320c3f82a66bd987a91e8efe1463524a93ad9a4280e800000000bd71ad09de0bf4683b77813996440091
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x846e721944304236b90ca218211d9c46510c10c3ecaa18860861d6550c430422f398c8a9021175cc645481087ce831aa40843d7418d520421fba2c0a90210f1d160548108bee6b02a40845c735815204237bb2a4290218b5915214810c9ac6a90a40861e6498c520430eb24c629021879916314810c3ac8b18a40862d649885204326b1cc4290218d5926114810caac7308a40863964980520432cb1cc029021179cc65d08108bae632e8408475759874204278b84c3a1021179cc65908108bae632c840845f73595420422e39acaa1021179cc65508108bae632a840847575185420431aaa0c2a10219954861508108f2ea302840866952181420422f39eca21021175cf65108108bce6328840845d73194420423b388ca210211e9c0651081087ce832e640843d74197320423abacc3990213c5c261cc81087ce832c640843d74196320421fba2ca990210f1d1654c81087ce832a640843d74195320423aba8c2990219554c614c810ccaa430a6408479751813204334a90c0990210f9d3650c81087ae9b28640843e74194320421eba0ca190211d9c4650c8108f4e0328640845e73d94410422eb9eca20821879516310410c3aa8b18820843e74d94310421eba6ca1882187592530c410c3ac8a98620843e74d96210421eba6cb10821179cf65884108bae7b2c42086695298221042b2b8aa410821595d66208410acaeb29042084777654821042b3bb2a41082199dd952084108eeeab0042084f3755802104339baac010821acdd16008410d60e8b0042086d373580210436839ac010821179ce64940108bae7324a00843e7498e500421eba4c7280210fdd16194010878e8b0ca00845f73586500422e39ac3280211bdc961940108d8e4b0ca00863554986400422f398ca20021175cc65100108dce4328800846d72194400432aa9cc3180210f9d0650c01087ae8328600846e721943004236b90ca180219954a6188010acaea10c40086676508620042f0b8043100211ddc7654801087ce8328400843d74194200422f398ca10021175cc6508010acaea108400866565084200423aba8c5880211d5da51840108f2ed28c200863765d91100431bb28c88802195d976344010caeca31a20086946418d1004333b2ec4880211d5d662440109cce53122008667651891004353b20c488021a91906244010d8ec631220086c4631891004370b80c4880219918a5044010ba4e7a0220086e062d01100437031080880216c9d33044010dc0c598220086e0620c1100437031440880213c1d92044010b60e890220085d073481100431db2ec8880218ed946444010cb6cbb1a200865b6518d100434c320c6880219ad976244010cd6ca31220086a8641891004364318c488021b818b61440108f4ed28a20085d27310510042d93a062880213c9da2144010
  | 1 => 0x404430faa4c7a02218715263d01108b8eab1e808861f5458f404430e2a2c7a022117ddb53d01108baeda9e808845f7614f404422ebb0a7a02219398f52d0110c9ac7a96808864e6314b4044326b18a5a02218d15261d0110cc8a530e808866452587404422f39ecaa0221175cf65501108dce5b2a808846d72d95404422fb9acaa0221171cd65501108dee4b2a808846c72595404432a29ec2a02219914b6150110c6ea830a8088654531854044332290c2a02210f9d664cc110878eab26608843f76d53304421ebb6a9982210fdd854cc11087aec2a6608861e64d4f304430eb26a7982218799053cc110c3ac829e608862e64d4b3044316b26a5982218b99052cc110c5ac82966088654539873044332294c3982219914961cc11087ce9b2a608843d74d953044237396ca982211b5cb654c11087ee8b2a608843c745953044237b92ca982211b1c9654c110c68a9b0a608866452d85304431a2a0c29822195d4c614c110cc8a430a6088664529872044332292c3902210f9d3654811087ae9b2a408845e73d95204422eb9eca902210fdd16548110878e8b2a408845f73595204422e39aca902210f9d7644811087cea322408843e76d51204421e3b6a8902210f9d85448110878ec2a2408845e75d8d204430faa6c6902218715363481108bcea31a408861f5418d204430e2a0c690221179db53481108b8eda9a408861f64d4d204430e326a690221179d853481108b8ec29a408861f6414d204430e320a6902218bd935248110c58c9a92408864f63d49204432631ea4902218bd905248110c58c8292408864f631492044326318a4902218dd536148110c68a9b0a408865753d85204432a29ec2902219914b6148110c6ea830a408863454185204432ba98c2902219514c6148110ccea430a40886645218520442b43aa4010221ca1512008110e90a690040887185414f10443942a0a588221d214c52c4110e28a829c20887275414a10443922a0a508221d1d4c5284110e88a6294208845e73189540422eb98c4aa021179cf60550108bae7b02a80843f76550540430eaa2c62a0218b5516215010c3cc8b18a80864e639885404326b1cc42a0218b9916215010c9cc6b10a80864d63588540432ab1cc22a0219958a6115010cd2c5300a80843e74189530421eba0c4a98210f9d36054c1087ae9b02a60845f7654c530430eb22a6298219354d6214c10c3ac9318a60862e649885304316b24c4298218b9916214c10c5ac8b10a60864e63588530431ab24c2298219958a6114c10cd2c5300a60846e721974304236b90cba18211b9c86590c108dae432c860846f725954304236392caa18211b9c86550c108dae432a860851c73551430428e3a2a6a18211d5d46150c10c6aa830a860865553185430423cba8c0a18218e5506050c10cb2a630286
  | 2 => 0xa6292211bdd95314910a5ee8a98a48852c7454c5244327328a629221c3d505314910e18a8298a48854e7319052442a6b98c829221595c46414910ad2e0320a48852e7418c5244296ba0c629221595c46314910ad2e0318a48870d4310c52442b33888629221595c44314910a5ee8b00a48852c7458052442a7b9ac029221531cd6014910a5ee8880a48852c7444052442a7b9a2029221531cd10149108bce7b2e848845d73d97424423ab8ecba122117dcd65d09108b8e6b2e848845e73d96424422eb9ecb2122117dcd65909108b8e6b2c848845e73d95424422eb9ecaa122117dcd65509108b8e6b2a848847771595424423db82caa1221179cf65109108bae7b28848845f73594424422e39aca21221179cc65109108bae6328848845e7598c424430faa4c6212218715263109108b8eab18848861f5458c424430e2a2c62122117ddb53109108baeda98848845f7614c424422ebb0a6212219398f5210910c9ac7a90848864e631484244326b18a4212218d1526110910cc8a53088488474755844244332292c2212218e1526010910cd0a5300848847875580424421f3a6cb992210f5d365cc9108eae3b2e648843f74597324421e3a2cb992210f9d3658c91087ae9b2c648843f74596324421e3a2cb192210f9d3654c91087ae9b2a648843f74595324421e3a2ca992211ddc5654c9108f6e0b2a648843e74d94324421eba6ca192210fdd1650c910878e8b28648843e74194324421eba0ca192210f9d6640c910878eab20648843f76d50324421ebb6a8192210fdd8540c91087aec2a0648861e64d4c324430eb26a61922187990530c910c3ac8298648862e64d483244316b26a4192218b990520c910c5ac82906488654539843244332294c2192211d1d5610c910cc8a4b086488658539803244334294c0192211e1d5600c910c70a9306828865853d814144334296c0a0a218ed506050510cb0a6302828866852181414430faa4c620a21871526310510c3ea8b18828861c5458c414422fbb6a620a21175db53105108beec298828845d7614c414432731ea420a219358f5210510c9cc6290828864d63148414429a3aa8220a21a558d4110510e28a6a0882887245250441442d83828220a219614e60cc510c70a9b02628866852d81314431c2a0c098a2196d4c604c510cd0a4302628843f76d50314421ebb6a818a210fdd8540c51087aec2a0628861e64d4c314430eb26a618a2187990530c510c3ac8298628862e64d483144316b26a418a218b990520c510c5ac82906288554754c4314434ab226218a21c5151310c510e88a498862885d0704c43144334294c190a218e1536048510cb0a7b02428863854181214432c298c090a219ad486048510ac8ea90842887275448421443922a24210a21d1d4d2108510e88a6908428845e7598f
  | 3 => 0xdb5454d1087cec2a2a68862f54d8953443162a6c4a9a218bd506254d10c58a8312a68861f64d8d534430e326c6a9a218bd936254d10c58c9b12a68864f63d895344317b20c4a9a218b1906254d10c9ec6312a68863464d855344332316c2a9a218e1936054d10cd0c5b02a68845f7654c534428fba2a629a21471d15314d10a9ee4a98a68854c7254c534428f3a4c629a21475d26314d10a9ce5318a68854d7298c534421f3a0c229a210f5d06114d10c3ccbaa0a68845d7695053442a7394a829a21535ca5414d108beecaa0a68854f7255053442a6392a829a21879945414d10c3ac8320a68855571190534428f3a0c429a21475d06214d10aaae2310a68855970188534428f3a6c029a21475d36014d10a3ee8880a68851c744405344237396cba1a211b5cb65d0d108dee4b2e868846c725974344237396cb21a211b5cb6590d108dee4b2c868846c725964344237396caa1a211b5cb6550d108dee4b2a868846c72595434423bb8acaa1a211edc16550d10a3ce7aa2868851e74d4d4344237396ca21a211b5cb6510d108dee4b28868846c72594434428eb98a821a21475d05310d10a3ceaa18868851c7550c434430f32a8621a21871954310d10c68a9308868865453984434423a3aac221a21a550d6110d109e0e0b08868845e73993524422eb9cc9a92210f9d263d491087ae931ea48854e7395352442a6b9ca9a922153dcd54d4910a98e6aa6a48870f54d4f52443862a6a7a92214b9d253d4910a5ae929ea48852f7454f52442963a2a7a9221c3d5053d4910e18a829ea48854e7399352442a6b9cc9a92214b9d263d4910a5ae931ea48870d4310f52442973a6c1a92214b5d360d4910a9ce7b06a48854d73d83524430faa4c729221871526394910c3ea8b1ca48861c5458e524430f326a729221875935394910c3cc829ca48861d6414e5244317326a5292218b5935294910c9cc7a94a48864d63d4a524430f324c729221875926394910c3cc8b1ca48861d6458e524421f3b6a8a92210f9d85454910c3ea9b1aa48861c54d8d524430faa0c6a92218715063549108bceda9aa48861f64d4d524430e326a6a9221179d85354910c3ec829aa48861c6414d524430fb26c6a9221871936354910c3ec831aa48861c6418d5244317b26c4a92218b1936254910c9ec7b12a48864c63d89524431bb26c2a92218d1936154910caec7b0aa48865463d85524431c326c0a92219618f60549108deeca90a48852f7454852442963a2a42922153dcd5214910a98e6a90a48852e749885244296ba4c429221539ce6214910a9ae7310a48862e65d505244236bb4a829221539ce5414910a9ae72a0a48846f7655052442a7b9aa829221531cd5414910c5cca2a0a48864e65d4c5244387aa6a629221c315353149108daed298a48852e7494c5244296ba4
  | 4 => 0x3ac9298658854d7294c32c430eb22a619621879516310710c3aa8b1883886956350441c430eb24a618e2187591530c710d2ac8988638866a5258021c430f2a2c7a06218755163d0310a3ae62a4818843e7695140c421ebb6a820621475cc5410310c3ac929e618861d6454f30c428eba0a718621179da534c3108baeda98618851d7414c30c42373b4a490621999486148310ccaa430a418846d76d4820c4338b0cc1aa42187d51639521087eecaa0a90851d739905484338b0cc1a9c21875935394e108beeca98a70851d7498c5384237394caa1c211b5ca6550e10a3ce7aa2870851e74d4d438431baa0c2a1c2195d4c6150e108dce4328870846d72194438430f32a8621c21871954310e108bce7326a50845d73993528421f3a4c7a94210f5d263d4a108deeca90a50867161980528422f39ecba1421175cf65d0a108bce732a850845d73995428422f39eca21421175cf6510a108bce6328850845d73194428421f3a6cb994210f5d365cca1087ce932a650843d74995328421f3a6ca194210f5d3650ca1087ce8328650843d74194328428eb9ca9a0c210f9da5450610a3ae72a2830843d76d50418430faa2c620c21871516310610a3ae929e630845e7694d318428eba4a698c21175db530c610c3ac9a98630861d6414c31842373b4a490c211b5db52086108eaeda9043084e576d4821842f1386a410c21595db5208610ccaeda90430876270d4821842f1380a410c21475ce5490210a3ae72a0810863654584408428eba4a718421475d2530c210caca6b0861086665258420842f0b804210421781c520082108bce7316a88845d7398b544430fb1cc7aa221479ce62d5110a3ae7316a88851f73583544428e39ac1aa22187d526395110c3ea8b1ca88862f5498a5444317aa2c52a2219398e6295110c9ac7314a88864e6358a5444326b1ac52a221999896195110c3ec9b1aa88861f6418d5444317b26c4aa22193d8f6255110c98c7b12a88862f641895444327b18c4aa2219318c6255110ca8c7b0aa88866462d85544432c31ec0aa2219a18b605511087eecaa0a88851f73550544428e39aa82a2214bdc95415110a58e4aa0a88851e73990544428eb9cc82a2214b9ca6415110a5ae5320a88845e73184544422eb98c22a2218758c6315110a6ae2318a88851e73188544428eb98c42a2214d5c46215110a72e0310a88851e73d80544428eb9ec02a2210f9d262d4d1087ae9316a68854e7295353442a6b94a9a9a2153dc954d4d10a98e4aa6a68861f64993534428f3a4c5a9a21475d262d4d10a3ee8b06a68851c74583534430f326a729a21875935394d10c5ea9314a68862c5498a5344327a9cc529a218bd516294d10c58a8b14a68864f5358a5344317324c529a218b5926294d10c5cc8b14a68862d6458a5344333312c329a210f9
  | 5 => 0x63664584530831ab22c2298419598d6114c20cccc4b08a61067161980530823b388cba18411d5c465d0c208ece232c861047571196430823bb8acaa18411d1c56550c208ece232a861047571195430828e39aa8a1841471d15350c208daea312861062d541894308326a98c4a18411e5d46050c20c72a83028610659531814308237390ca218411d9c46510c208eae2328861061f6550c430830eb2a8621841179cf65108208bae7b28841061e5458c420830eaa2c6210410f9d3650c82087ae9b28641061d6494c320830eb22a619041179cc64544208bae6322a21043e7418d510821eba0c6a88411ddd95114420c6ac8a88a210655635445108274b84c5a084117dcd65504208b8e6b2a821045e73195410822eb98caa08418b5506250420cc8c4a8a821067151181410822f39eca20841175cf65104209d2e1316621043f74595310821e3a2ca988410f9d0654c42087ae832a621064d531893108332312a2988419c544604c42087ce9b28621043d74d9431082b2bacc21084159dd95108420cceeca8842104eb755802108335baac010841aadd16008420d50e8b0042106cb73580210836439ac010841179ce64940208bae7324a01043e7498e500821eba4c7280418b55262900208bce6328801045d731944008326a9cc5180410f9d0650c02087ae8328601046d7694a200823cbb4a5100418bd976448020c5eca322401064f65d8d2008327b28c690041a31906348020ccecbb0a4010667651852008353b20c290041a91906148020d8ec630a40106c4631852008370b80c290041729cf4048020dc0c3a0240106e06110120082d53a66090041b81873048020dc0c2182401063b65d91200831db28c89004196d976348020cb6ca31a40106986418d20082e539884900416a9d03248020ce6cbb0a4010673651852008358320c290041b418c6148020dc6c430a40104ea76c85200833930ac1aa6210fdd95415310c3aa8b18a98861e6458c54c433930ac1a9e2117dd95314f10c3ac8a98a78861d6498c53c4237394caa1e211b5ca6550f10a38e6aa2878851c7454d43c4237396ca21e211b5cb6510f10c3ecaa18878861d6550c43c434aa1ac221e218799263d4b10c3ac931ea58861e6458f52c430eb22c7a96218d99261d4b10c6ac930ea5886566398752c432ab1cc3a9621179cc6454b108bae6322a58843e7418d52c421eba0c6a96211bdd95214b10ce4c2b00a58845e7319742c422eb98cba1621179ce6590b108bae732c858845e7399542c422eb9ccaa1621179cf6510b108bae7b28858845e7319442c422eb98ca216214b5ca5410b10c3ca8b18858861d5458c42c421f3a0cb996210f5d065ccb1087ce932c658843d7499632c421f3a4ca996210f5d2654cb1087ce9b28658843d74d9432c421f3a0ca196210f5d0650cb10c
  | 6 => 0x1482ab3988428a41555cc4214520e4a84210a290573704c851482b83826428a414d9d03214520a6ae8190a290745320c8514829bba2c028a414d1d16014520aaee6b00a29055473580514829bba24028a414d1d12014520aaee6900a29055473480514822fb9acba0a41171cd65d05208bee6b2c829045c73596414822f39ecaa0a41175cf65505208bee6b28829045c73594414822f398ca20a41175cc65105208bceb318829061f5498c414830e2a4c620a41171d56310520c3ea8b18829061c5458c414822fbb6a620a41175db53105208beec298829045d7614c41483162a4c420a419598f5110520caac7a88829065663144414832ab18a220a41999885110520ccac4288829063854980414833828cc020a410fdd165cc520878e8b2e629043f74596314821e3a2cb18a410f9d3654c52087ae9b2a629043f74594314821e3a2ca18a410f9d0650c52087ae8328629043e75990314821e3aac818a410fddb540c52087aedaa0629043f76150314821ebb0a818a4187993530c520c3ac9a98629061e6414c314830eb20a618a419314e620c520c6cc9a88629063564d44314831b320a218a418d590510c520cccc4288629066562144314832c29cc018a419c146600c520ce0a3304429063854d81214832c29ec090a418e1506048520cb0a63024290673511812148393aa24210a41c91512108520e8ea6908429074453484214822f3acc7a024187d5263d0120c38a931e809045c7558f404830faa2c7a02418715163d01208beeda9e809045d76d4f404822fbb0a7a0241175d853d0120c58a9316809065663d47404832ab1ea3a02419598c51d0120caac628e8090666621474048332b10a3a0241179cf65501208bae7b2a809045f73595404822e39acaa02419314f6250120c5ea8312809064c531894048333b10a2a024199188515012087ceb326609043c75593304821fbb6a9982410f5db54cc12087eec2a6609043d76153304830f326a7982418759353cc120c3cc829e609061d6414f304832629cc5982418d99351cc120c6ac9a8e609063664147304831ab20a3982419998851cc120ccac428e609043e74d95304821eba6ca982410fdd1654c120878e8b2a609062c54d8930483162a0c49824193d4c624c120ccec428a609066462145304838c2a0a790241cc15051c8120ea0a628e409070c5414e2048393aa0a310241c91505188120e8ea628c409074453146204822f398c2aa041175cc615502087eecaa0a81061d5458c540831aaa2c22a041879916315020c9ac7310a81065663984540832ab1cc22a0418d9916115020cacc6b08a810655635845408333312c22a0419c586601502087ce830aa61043d74185530822fbb2a629841875915314c20caaa6b08a61061d6498c5308316b24c4298418d9926114c20c6ac9308a61
  | 7 => 0x829a4155dc55414d20aa8e2aa0a69061e65150534830eb20c829a41535c86414d20a3ce8308a69051d7418453482a6b90c229a41565c06114d20a3ce9b00a69051d74d80534828fba24029a41471d12014d208ece3b2e869047571d97434823bb8acba1a411d1c565d0d208ece3b2c869047571d96434823bb8acb21a411d1c56590d208ece3b2a869047571d954348237b92caa1a411ddc56550d208e8e2b2a869047b70595434828f39ea8a1a41479d35350d208ece3b28869047571d94434823bb8aca21a411d1c56510d20a3ae62a0869051d7414c434828f3aa8621a41471d54310d20c3ccaa18869061c6550c43483162a4c421a419314e6210d208d8eab10869068d435884348274382c421a418e15260d0920cb0a7b02849063b54181424832c298c0a124187d526310920c38a9318849061f5458c424830e2a2c62124117ddb53109208baeda98849045f7614c424822ebb0a6212414b1d54210920d1ac6a10849070c5350842482d438284212419614e60cc920c70a9b02649063854181324832da98c0992410fddb540c92087aedaa0649043f76150324821ebb0a81924187993530c920c3ac9a98649061e6414c324830eb20a619241531d5320c920d1ac8990649070c544c832482e43826419241179ce64d45208bae7326a29043e7498f514821eba4c7a8a41559ce54d4520aaae72a6a2905577355351482aa39aa9a8a41c5d5353d4520e28a9a9ea2905367494f514829aba4a7a8a414ddd153d4520a68e8a9ea2907175414f514838a2a0a7a8a41559ce64d4520aaae7326a2905367498f514829aba4c7a8a41c550c43d4520aace6216a2905557310b514829b3a065a8a414d5d032d4520a6ce9b06a29053574d8351482ab39ec1a8a41555cf60d4520c3ea931ca29061c5498e514830faa2c728a41871516394520c3cc9a9ca29061d64d4e514830f320a728a41875905394520c6cc9a8ca29063564d46514832b31ea328a419558f519452087cedaa2a29043e76151514830faa6c6a8a41871536354520c3ea831aa29061c5418d514822f3b6a6a8a4187d935354520c38c9a9aa29045e7614d514830fb20a6a8a418719053545208eeeca88a29053774544514829a3a2a228a4155dcd5114520aa8e6a88a29063665d50514823abb4a828a41559ce5414520aaae72a0a2904777655051482abb9aa828a41551cd5414520c6cca2a0a29065665d4c514838baa6a628a41c515353145208eaed298a2905367494c514829aba4a628a411ddd95314520a6ee8a98a2905347454c514832b328a628a41c5d505314520e28a8298a2905567319051482aab98c828a41595c86414520ae2e0320a2905367418c514829aba0c628a41595c86314520ae2e0318a2907154310c51482b33908628a41595c84314520ae6e0a10a290570705085
  | 8 => 0x2530c720aaae3298639061d6454c31c830f2a2c7a06418755163d0320a3ae62a4819043e7695140c821ebb6a820641475cc5410320c3ac929e619061d6454f30c828eba0a718641179da534c3208baeda98619051d7414c30c8334b14c1aa44187d51639522087eecaa0a91051d739905488334b14c1a9c41875935394e208beeca98a71051d7498c538823b38ccaa1c411d5c66550e20a3ce7aa2871051e74d4d4388317aa0c4a1c4193d4c6250e208ece2328871047571194438830f32a8621c41871954310e20a3ae72a6851043e76951428828eb9ca8a14410f5db5410a20c3ea8b18851061c5458c428828eba4a799441179da534ca20a3ae929a651045d76d4c328830eb26a61944187590530ca208eeeca88a31045e73d97418822eb9ecba0c41179cf65106208bae7b28831043e74d97318821eba6cb98c410f9d3650c62087ae9b2863104e576d4421882f1386a210c41789c05108620a3ae72a4811051d7395040883172a2c420441475d2538c220a3ae9298611064e53588308822f39cc3aa241175ce61d5120c3ec731ea89051e73987544828eb9cc3aa24147dcd60d5120a38e6b06a89061f5498e544830faa2c72a2418dd526195120c6ea8b0ca89065663986544832ab1cc32a2419958a6195120cacc6b0ca89065563586544830fb26c6aa24187d906355120c98c7b12a89063764d85544832bb1ec2aa2419518f6155120c6ec830aa89065763185544832a318c2aa24199d886155120cb0c7b02a89067061d81544821fbb2a82a24147dcd5415120a38e6aa0a89053771550544829a38aa82a241479ce6415120a3ae7320a89053671990544829ab8cc82a241179cc62151208bae6310a89061d6318c5448296b90c62a241479cc6115120a3ae6308a89052d72184544829cb80c22a241479cf6015120a3ae7b00a89043e74987534821eba4c3a9a41559c654d4d20aaae32a6a6905577155353482aa38aa9a9a4187d9264d4d20a3ce930ea69051d74987534828fba2c1a9a41471d160d4d20c3cc9a9ca69061d64d4e534831baa4c329a418d1526194d20caea730ca69063754586534831a2a2c329a4195d4d6194d20c6cc930ca690635649865348332b14c329a418d9916194d20c6ac8b0ca69043e76d51534821f3b0a8a9a418dd536154d20c68a9b0aa69063754185534831a2a0c2a9a4187d936354d20c38c9b1aa69062c64d89534831bb26c2a9a418d1936154d20caec7b0aa69063764185534831a320c2a9a4195d8c6154d20ccec430aa69063864d81534833830ec0a9a4117dd95314d20a3ee8a98a69051c7454c53482abb8aa629a41551c55314d20a3ce9318a69051d7498c53482ab38cc629a41555c66314d2087ce8310a69043d74188534830f32ea829a41175da5414d20aace32a0a69055571950534822fbb2a
  | 9 => 0xae42a2861853571151430c2cd386a8a1861179d85450c30a9ae42a2861855571151430c24f3b0a8a1861635c85450c30b2ae22a2861851e76151430c30f3b0a8a1861c39c85450c30a3ae42a2861870d72151430c286b90a8a1861c59c45450c30a3ae22a2861871571151430c28ab88a8a1861479c05450c30e34e02a2861843f76550430c28eb9aa821861a650e6010c30c38c8a1aa41854c7250d520c237bb2a4290618b5915214830ccaa4b08a41847771595420c23a38acaa10611d9c465508308eae232a841861d5418d420c30e32a86a1061631c94350830c98c6a92841870d43549420c34ca18c0a10619a54860508309b6e0b24641849f74582320c316b24a4190618b591520c8309b2e1b20641849d76990320c2a6bacc419061a3592520c830c3ac8a90641868d64548320c2a7bb2a41906193dd9520c830c9ec8a90641870e64548320c326b22a419061c3591520c830c1ac8a90641869964980320c34d322c019061871914354430aa8e2a1aa21847776544510c31ab22a2288619958951144308dee4b2a821846c72595410c237390caa08611b5c86550430c3aa831a821861c6550d410c2ca38a86a08619518d5150430e2a86a8a821869943181410c338a88c0a086136dc1648c43093ee8b04621863564944310c31ab22a218861365c3640c43093aed320621855575984310c34ab24a21886187591510c430d2ac8a88621855776544310c32bbb2a21886195d91510c430e2cc8a88621865564544310c38ab22a21886185591510c430d32c9300621869a64580310c21fba2ca908610f1d1654843087ce832a421843d74195210c24eba0c6908619318d5248430ac8e2a92421865463545210c2b2392a290861175d7630843093ae831842184d97018c210c333b2a4210861995952108430bc0e0908421861e6450e500c28eba06528061475d03194030c3aa931c801861c6550c400c22ebb4a718061475d2538c0308f2ed29c60185997494e300c2ccba06518061665d0318c0308beeab2260184cc72591300c26a38ac898061275d3604c0309b4eda02601869964101300c2cd3a4a698061369d8434c030cd4c4b06a99043f7655054c830eaa2c62a641879916315320cd4c4b06a79045f7654c53c830eb22a629e41875926314f208ece332a87904757199543c828e39aa8a1e41471d15350f208ece3b28879047571d9443c830fb2a8621e41875954310f20d1a86b10879061e5458c42c830eaa2c621641a358d4210b20c3ac9298659061d6454c32c8346b226419641179cc64547208bae6322a39043e7418d51c821eba0c6a8e411ddd951147208bce732c839045d7399641c822f39eca20e41175cf6510720a6ae32a0839061e5458c41c830eaa2c620e410f9d2658c72087ae932c639043e74d9431c821eba6ca18e418759
  | 10 => 0x52d7295042cc30eaa4c621661879516310b30c3aa8b18859843d7599032cc21fbaac8196610f5da540cb3087eecaa0659870e544c832cc3172a4c5a8e618b55262d4730c5ca8b16a39862d5458b51cc2b3396a328e610f5da541473087eecaa0a3984777654451cc29a38aa8a0e618e5506050730a6ae32a0839861d5498c41cc30f2a2c620e6187551631073087aeb320639843f7559031cc21ebb4a818e610fdd9540c730e2ca8988639843e7499721cc21eba4cb90e610f9d2658873087ae932c439843e7419521cc21eba0ca90e618e9536048730c74a8302439843e7499421cc21eba4ca10e61875526308730c3aa8b1843985657194821cc2b2b94a210e6159dd52108730acaea90843987265448421cc392aa24210e61781c12108730c3aa931e819861e5458f40cc30eaa2c7a0661875536350330c3aa831a819865963983548c21fbb2a82a4618e5506050e308bced2a2871851e76951438c30f3b4a8a1c61475ca5450e30a3ae32a2871846f76548528c23b38ecba14611d5c765d0a30c3ecaa1e851861f6550d428c2c639286a146127dd1608ca30c3acab20651861d64548328c23bbb2a228c611b9cb65d06308dae5b2e831861f6550f418c30fb2a86a0c61651c5435063093ee8b04631861d65590318c30eb22a218c610f9d365c863087ae9b2e431843e74d96218c21eba6cb10c61275d0634863093ae831843184d97018c218c26c39ac010c6166dc14390230c3ca8b18811861d65993308c30eb2ac9984618e59664cc230c72cab26611862f64189544c327b18c4aa26199d8b6155130cc8c5b0aa89863764185544c32bb18c2aa26199d886155130cc8c430aa89866862d81544c33830ec0aa2610fdd95415130a58e4aa0a89853471550544c31c2a2c1a1a61879954310d308deeca90a49852c74548524c2b238aa4292611ddc565109308e8e2b28849861f5458c424c30e2a2c6212619358f52109308eeeca88a29853474544514c2b2392a228a611bdc965105308d8e4b28829861f5458c414c30e2a2c620a619558f511053087ee8b28429843c74594214c21f3a0ca10a610f5d065085308bceb318429856571148214c2b2b90a210a61599d52108530ac8ea908429866852580214c33828ac010a6187d5163d0130c38a8b1e809851d73952404c296392a9202614d1c5549013087cec2a2809851d73950404c29cb84a8202610fdd95410130a58e4aa0809853471550404c2a6392a918261551c5548c13087eecaa0a81862d54588540c31aaa2c22a0618b9916215030c9cc6b10a81866662984540c332b14c22a0618d9916115030cacc6b08a81866662584540c332b12c22a0614b5c854d0c30a6ae22a6861854d72152430c2aab88a92186117dd56090c309b6eab04861865b75582430c28f39ea8a18610f9d85450c30a5
  | 11 => 0x9022fbb2a629a81531c95314d40aa8e2a98a6a061e6550c4350237bb2a429281531cd5214940ac8e2a90a4a047771594325023a38aca1928187593530c940c3ac829864a062d64d48325023bbb2a228a81551cd5114540ac8e4a88a2a046f725943150236392ca18a8187593530c540c3ac829862a063564d44315022fb9aca10a81171cd65085408bce632842a045d73194215021f3acc810a81595c45208540acae428842a05667548421502b23aa4210a819a1496008540ce0a2b0042a045f7654c5310326a9ac4298819554d6114c40976eab06862063b7558343102cd386a6a1881279d85350c40b1ae429a86205957114d431034ca1cc0218818718d4354840a58e4a1aa42046f765485210326b1aa429081995496114840976e0b1c842049f735824210326b1ca4210819358d5210840a5aeb310842068d63948421030eb1aa421081a358d5210840a5eeca90842062f76548421038731aa4210818b58d5210840e1ac6a90842060d63548421034cb1cc021081a698d6010840972e0324642062c6454a321023bb8aca990811d1c5654c8408ece232a642047571195321030e322a699081271d9434c840c38caa1a642058c7250d3210316322a499081c350d524c840d3286302642066952181321030e31a86a88814d1c543544408eeeca88a220655635445110332b12a2288812edc1639044093ee6b04822065563944411032ab1aa2208814d5d66110440d2ac7288822061d63544411034ab1aa2208814ddd95110440c6eeca88822071663544411031ab1aa220881c558d5110440c2ac6a88822069963980411034d31ac0208812e5c0648c440c68c8a8c622046f725953110236392ca988811b9c8654c4408dae432a622061c6454d311024e3b2869888187195434c440b28e2a1a622063464545311038aa1aa298881a650c604c440ce2a2302622045f73595211022e39aca90881179cc65484408bae632a422049d731912110316322a490881591c55248440c68c8a8a422056472545211021ebaec810881275cc6408440972e03204220667654842110332b2a4210881781c12108440a3ae6214a02051d73106501021ebb4a9200811e5da5490040b32e72a480205997310a40102ccb988320081669ce5450040974ec21a802065a6358354cc297390c72a6614b5c86395330a6ce231ca9985357118e54cc28f398c52a6618b5886295330a3ce630ca9986356118654cc29db82c4aa661479cc6255330c5ac4312a99853b7058554cc28f398c2aa6618d5846155330a5ee4b02a99852c7258154cc29bb8ac0aa6614d1c5605533087eecaa0a9986395498243cc31d2a4c021e618d95261d4b30c6aa930ea5986365458752cc31aaa2c3a9661599c75294b3087aed2a0a59843f7655052cc237bb2a4296614b1c95450b30c72a83028598
  | 12 => 0x90843595d66348421aceeab1a4210da77458d21086d23a2c69084378dc16348421bc0e0b1a4210da67418d21086d2ba0c690843b158c63484219cceda9a4210ce67614d21086d33a0a690843695d05348421bc4e029a4210de17014d2108673bb28690843391d943484219ccec21a4210ce57610d21087c2a188690843595d66048421aceeab024210da77458121086d23a2c09084371dcd6048421b88e6b024210ce77648750086723b24328043781c121940218bce7324a010c5d73992500861f3a4c7280430f5d263940219c8ec90aa010ea764485500875232242a8043b1d8d2154021d88c690aa010de070485500871cb80c8a804387d936354021c38c9b1aa010e1f6418d500870e320c6a8043965c063540219ceec908a010ea6644845008752b224228043b198d2114021d8ac6908a010c7b76540500871cb22a0280439658d5014021ec242a80a010d4e7219253d02a6b90c929e81559c46494f40aaae2324a7a051e7418a53d0326b10c529e81479d06194f40caac230ca7a055b7058953d028f3a0c4a9e81935886254f40ab6e0b0aa7a051e7418553d032ab08c2a9e8153dc96054f40a98e4b02a7a05577158153d02aa38ac0a9e8117dd95314f40cb2a730687a065a5398043d032b29cc3a96819554e61d4b40caca6b0ea5a06555358752d02b338ea529681175da5314b408beeca98a5a046f7654852d022ebacc62168117dd56310b408baed29885a045f7654c42d038729a8421681531c9534cb40cb2a630265a061d6494c32d02a6b94a61968187991530cb40c3ac8a9865a064e5398b51d0326a9cc5a8e819394d62d4740c9aa6b16a3a056672d4651d022ebb4a628e8117dd953147408eeeca88a3a045d7598c41d022fbaac620e81175da53107408beeca9883a07165350441d02aa38aa698e819654c604c740c3ac929863a05557194c31d030f322a618e8187591530c7408bce732e43a045d7399721d022f39ccb10e81175ce65887408bce632a43a045d7319521d032d29ec090e819694c60487408bce732843a045d7399421d030f322a610e81875915308740acae329043a05657294421d02b3baa4210e81595d52108740e8ca690843a07455348421d02f03824210e8117dd95314e40a3ced29a872061e7694d439028eb94a6a1c81475c65350e408deeca90a52049f73582429030eb2ac6214818758d5210a408ece3b2e652047571d97329030fb2a879948187d95434ca40b18e4a1a652047776544519024fb9ac120c81875956310640c3ac6a88832046e72d973190236b96cb98c8187d9543cc640c3ecaa1a63205947150d319022f39ecb90c81175cf65c86408bce7b2c432045d73d96219024eb98c890c81275cc6408640972e032043204b874580219030eb2cc7a04818759563d0240cb2cb31e81206596558f40
  | 13 => 0x6054d218beeca98a690d1c7454c534870eb22a629a43561c15314d21c38e6b20a690e1d6498c534863d386cba1a431e5c365d0d21a38e6aa68690d3870553434868eba0a7a1a431e9c36590d218f2e1b2c8690d1d73152434868e3a2a721a43561c15390d218dee4b2a8690c7771595434863db82caa1a431e1c16550d2187ced2a28690c3c76551434868e39aa8a1a434e1c15450d218bced29a8690c5c7654d434868e3a2a6a1a43561c15350d218dae5b288690c7571d94434863db82ca21a431e1c16510d2187ce83288690c5e73194434861ebb6a821a43475cc5410d218baeda988690d1d7414c434868f3aa8621a43471d54310d21c3ecaa188690e1d6550c434868eb98a9a12438d15161d0921a3ae62a28490d1d7414f324872a29ac399243475d0534c921a3ae62a68290e2c5458b414862fb9acaa0a43171cd6550521a3ae62a28290d1d7414f314872629ac598a430fdd1654c521878e8b2a6290d1d7414d314863dbb2a0282434e1d15014121ab0e6a80a090c5f73583540862e39ac1aa0430fdd95415021c3aa8b18a810e3954580540870f322c62a0439698e6015021cb2c7300a810e3a64580540872d31ac02a0439658d6015021cd4c4b00a810e7261580540861fba2c1a98430f1d160d4c218beeca98a610e1d6454c530872ca9ac029843875926314c21c74c9300a610e3964980530871d322c0298438e5916014c21cb4c6b00a610e6a62580530873930ac0298431e9c065d0c218f2e032e8610c7a70196430863cb80cb218431edc16550c218f0e0b2a8610c7a70195430863cb80caa1843471cd5450c21a38e8a9a8610c6d751894308716aa0c4a18439354c6250c219cae23128610c7575185430871aaa0c2a18439554c6150c219cae430a8610c7a70194430863cb80ca2184387d954310c21c3acaa188610c6d759884308672b8cc421843a350d6210c218eaeb3088610ce572984430874aa1ac221843179cf65108218bae7b288410e1e5458c420870eaa2c621043a358d421082187ce9b286410c3d74d94320870eb24a61904387591530c821d1ac89906410c5e73d94410862eb9eca20843179cc65104218bae63288210e1e5458c410870eaa2c620843a558d411042187ce9b286210c3d74d94310861f3a0ca188430f5d0650c421c3ac92986210e1d6454c310874ab2262188431b5da52884218eaed2944210dc67310521086e2b988290843699d03148421b4ae818a4210dc67310921086e2b988490843699d03248421b4ae81924210e6575d952108673386ca90843999db6548421acaeb3224210d677559121086e3b9ac890843711cd6448421bc6e0b224210de0705912108752b20c890843719cc6448421b8ae63224210ce676d5121086733b0a890843719cc5448421b8ae62a24210de27015121086f0b80a8
  | 14 => 0xcaa188618e1d6550c430c71b2a2c2218630fdd16094831878e8b04a418c3d76950520c61fbb2a8290631bdd95214831c74a9300a418e3954980520c71d2a2c0290638e5516014831cd2a4b00a418c7b70595420c63c382caa10634b1c95450831c3aa9b1a8418e1d5418d420c71aaa6c2a10638d5506150831a5ae52a08418e1d5498c420c66ab8cc621063879516310831c3aa8b188418e3554987320c71aaa2c3990630f5d6640c83187eeab206418c3d76950320c61fbb2a819063c3951320c831c3aa931c8218c5f7558e410c70eaa2c720863875526310431c3ca8b188218e1d5458c410c71ab2a82208638755260cc4318baed29c6218c757694e310c62f3b6a898863475d6544c431c3ecb2a26218e1f65551310c78a38aa89886387553614c431e2aa9a0a6218d5575105310c70eaa0c0988638dd96544c431c6ecaaa26218f155494d310c6aabae8698863659d0324c43187ee8b14a018c3c7458a500c61ebb4a8280630fdd95414031c5ca9310a018e2d54988500c7172a2c4280638b55162140318f6eca80a018e6962540500c733312c3aa643179cf60553218bae7b02a990c3f7655054c870eaa2c62a643879916315321c9ac7310a990e666258454c8733312c3a9e430f9d36054f2187ae9b02a790c5f7654c53c870eb22a629e43875926314f21c5ac9310a790e666258453c863d384caa1e431e5c26550f21a38e6aa28790d1c7454d43c870fb2a8621e43875954310f21d2a86b088790e1e5458c42c870eaa2c62164387592530cb21c3ac8a986590e2d5418941c874ab1a8220e439354c624c721d2ac89886390c5e7399250c862eb9cc9286430f9d2639432187ae931ca190c7b7654050c8732b14c3aa443179cf60552218bae7b02a910c3f76550548870eaa2c62a443879916315221caac7308a910e65629845488732b14c3a9c430f9d36054e2187ae9b02a710c5f7654c538870eb22a629c43875926314e21c6ac9308a710e6562984538863d384caa1c431e5c26550e21a38e6aa28710d1c7454d438870fb2a8621c43875954310e21d1a86b108710e35541854288746b1a84214439554c614ca21d1ac89906510e1e5458c418870eaa2c620c4387592530c621c3ac8a986310c5e73992508862eb9cc9284430f9d2639422187ae931ca110c7b76540508862fb9ac1aa243171cd60d5121c3ec831aa890e4c63d89544872a31ec2aa24396d8f6055121cb0c7b02a890e3b64181544872db18c0aa2439618c6055121cd6c4302a890e7361181544861fbb2a82a243471cd5415121a70e0aa0a890e1d5458c544870f322c62a2430fdd160d4d21878e8b06a690e1d73191534870e326c6a9a438b1936254d21c68c9b0aa690e3b64d81534871c326c0a9a438ed906054d21c70c8302a690e5b631815348735b10c0a9a439cd84
  | 15 => 0x5d7694c521062fbb2a6290831bdd95214841cb4a7300a420e5953980521072d29ac0290839654d6014841cd2a4b00a420e5553987421072aa9ac3a1083175d663108418beeab188420c5d7694c421062fbb2a621083c394d42108418f6e0b2a6420c7870595321070fb22a69908387191534c841a98e4a9a6420e5553d85321072aa98c2990832d5c6640c841c3ac92986420d4d7294c321070f322a61908387591530c841c3aa73068220c3d76952411063abb4a92088387d965350441c3ecaa9a8220f147154d411070ea98c0a088395d965350441caecaa9a8220f165454d411069abac86a0883659cc42504418bee6b14a020c5c7358a501062ebb4a62808317dd95314041c9ca7310a020e4d53988501072729ac4280839354d62140418f6eca80a020e6962540501072b31ac3aa6630fdd95415331c5aa8b10a998e2e6458854cc72731ac42a663999896115331a5ae42a68798d4d7215243cc61f3b0a8a1e634b5c85450f31b2ae3aa28798c5e7615143cc6a6b90a8a1e63279d85450f31b1ae42a28798d1e7615143cc70f3b0a8a1e63c39c85450f31a3ae42a28798f0d7215143cc686b90a8a1e63c55c45450f31a3ce02a28798c3f7655043cc74aa1ac221e630fdd16094b31878e8b04a598e1c6450d52cc637bb2a4296638b5915214b31c38caa1a8598f0d4354942cc74aa1ec2a16638b592520cb31c5ac8a906598e1d5418d41cc6ca38a86a0e63a558d4110731c3cc8a1ca198c7b7654050cc72ab1cc3aa4630fdd95415231c6aa830a8718c6f76548528c61f3b0a8a0c630fdd95410631c3ca8b188318e1d5458c418c63dbb2a0284638bd906255131c9ec6312a898e6462d85544c735b16c0aa2639a18b6055131c76c8302a898e5b63181544c735b10c0aa2639a1886055131ce6c2302a898c3f76550544c696392a82a2634e1c15415131c68a8b0e8698d1e75d91434c68f3a4a8a1a63179d85450d31a3cec2a28698e1e76151434c68eb90a8a1a63479c05450d319acea30a8698e5675185434c637bb2a4292634b1d15214931ad0e0a90a498c3f74580524c61e3a2c0292638719543d0931e1a87a968498e9543587424c70e32a86a12631edc165109318f0e0b288498e1f5458c424c70e2a2c621263351c56310931c9ac7a908498e4d63148424c70e2a2c7a0a63471d543d0531b28e2a1e8298d1c7550d414c70e32a86a0a63651c543505318f6eca80a098d3874540504c6b4392a028263551c5431413187ee8b10a098c3c74588504c697390c72a0634b5c86395031a3ce6314a818e2d6218a540c68f39ec12a063471cd6255031a68e2b12a818d3b70589540c69c382c4aa063479cc6255031c5ac4312a818d1e73d81540c68e39ac0aa0634bdc96055031a58e4b02a818d3471581540c61fbb2a82a0638d5516190c31c3e
  | 16 => 0xca9a38aa82a2654e1c15415132c58a8b16869951e75d91434ca8f3a4a8a1a65179d85450d32a3cec2a2869961e76151434ca8eb88a8a1a65479c05450d3299cea312869964e75189434cb0e2a2c7a1265471d543d0932b18e4a1e849951c7550d424cb0e32a86a1265631c943509328eeeca88a29953474544514cab8382a228a650fdd16014532878e8b00a29947b76540504ca9c3a2a0282655c1c55014132a98e4a18a09943f74584504ca1e3a2c2282654d9c46395032a6ae231ca81951e73186540cb1ab08c32a065479cf6095032a38e6b0aa81952c72585540ca9db82c2aa0654e1c16155032a3ce630aa81963561185540ca8f39ec0aa065471cd6055032a58e4b02a81953771581540ca9a38ac0aa0650fdd95415032c5aa8b14861961f6550c430cb0eb2a86218658b9516210c32c3aa931c841945f7558e420cb0eaa2c721065875526310832c3ca8b18841961d5458c420cb16b2a84210658755260cc8328baed29c641946d7694e320ca2f3b6a899065475d6544c832c3ecb2a2641961f65551320cb86392a89906587553624c832e1aa9a12641954d75109320cb0eaa0c0990658bd96544c832c5ecaaa2641970d5494d320caa6bae86990650fdd16094432878e8b04a21943d76950510ca1fbb2a8288651ddd95114432c74a9300a21963954980510cb1d2a2c0288658e5516014432ce2a2b00a21943f74586500ca1e3a2c3280650f5da541403287eecaa0a01963654984500cb1aaa4c2280658d9516114032c6aa8b08a01947b76540500cb38b0aa02806517dd95314f41c9aa6b10a7a0d9571d4d43d064f3b0a6a1e83635c85350f41d2a86b0887a0c5f7358252d062e39ac1296838718d4354b418deeca90a5a0e4d6354852d0726b1ca4216839358d5210b41c38caa1a65a0f0d4354932d074aa1ec2996838798d43943418f6eca80a1a0c5f7654c5390637bb2a4294831edd950142418beeca98a6a0d4c7254c53506ac382a629a83479d76350d41a3cec29a86a0e1e7614d435068eb90a6a1a83479c05350d4196cea30a86a0e36751854350637bb2a429283531cd5214941ad0e0a90a4a0c5f73580525062e39ac0292838719543cc941e1a87a9664a0e9543587325070e32a86992831edc1650c9418f0e0b2864a0cb471590325070eb26a61928387590530c941c5ac9a9064a0e2d64148325063dbb2a028283561cd5014141ad0e4a80a0a0d347150c505062fb9ac428283171cd6214141a9ce4324a620d4d72192531068f3a0c529883935886294c41a3ce9b04a620d1c7458953106aa38ac4a988356dc16254c41ab0e0b12a620d1e741895310726b10c4a9883479d36054c41a38e8b02a620d4f7258153106a6392c0a9883551c56054c418beeca98a620e5553587431072b29ac22188317dcd60948418b8e6b04a420c
  | 17 => 0x888787dd94354443c38eca1aa221f177150d5110f8a38a86a88878750f6254443c3a86302a221c9f7650c5110e3bbb2a22888727dd943d4043c3eeca1ca021e1c7650e5010f8db828728087c61c14394043c3a86b14a021c777158a5010e3a38ac5280878750d61940438dee4b0ca021c6c725865010e4fbb28628087a350e6214043d1a86b10a021e95439845010f4aa1ac2280871edd950140438beeca98a7a16555358453d0ac6b96a6a1e85279d85350f42b2ae229a87a168d4358843d0a2fb9ac128e85171cd6094742c38c6a1aa3a14777654451d0b2ab1aa228e858798d43943428f6eca80a1a145f7654c5390a3bbb2a228c851edd950142428beeca98a6a15547154c5350aac382a629a85479d76350d42a3cec29a86a161e7614d4350a8eb88a6a1a85479c05350d4295cea31286a162e751894350a3bbb2a228a85551cd5114542ae0e0a88a2a145f735805150a2e39ac028a851edd95014142ab0e6a80a0a1570715405050a96392862828517dcd61141428b8e6b08a0a1556711925310aaab88c929885479d06194c42caac230ca62151e74d825310a8e3a2c2a9885531c96154c42ab6e0b0aa621558705855310a8f3a0c2a9885955846154c42a3ce9b02a62151c745815310aa6392c0a988555dc56054c42aa8e2b02a62145f7654c5310b26a9ac5a18859394d6210c42c3aa7306842143d769524210a36bb4a92108587d965350842c3ecaa9a842170c7254d4210b0ea98c0a108593d965350842c9ecaa9a842170e5454d4210a96bac86a108517dcd60944428b8e6b04a22145d7694c5110a2fbb2a6288851ddd95114442cb4a7300a221659539805110b2d29ac0288859654d6014442ce2a2b00a22145f735865010a2e39ac328085175da53140428beeca98a021656539845010b2aa9cc2280859594d6114042caaa6b08a02147b765405010b38b0aa0280859398d62d533287eecaa0a9996355458454ccb32b14c22a6658d9916115332cacc6b08a9995357115343ccaaab88a921e650f9d85450f32a6ae22a2879958d72d5143cca2f3b0a8a1e65555c45450f3293cec2a287995957115143cca8f3b0a8a1e65879d85450f32e1ae42a287997167115143cca8eb88a8a1e65c55c45450f32a2ae22a2879951e7015143cca1fbb2a821e65a350d6210f32c3aa831a859958c7250d42ccb46b1a84216650fdd16094732878e8b04a39961c6450d51cca3bbb2a228e658d5915114732c3cc8a1ca19947b7654050ccb26b1cc5aa4650fdd95415232c5aa8312871943e76151428ca1fbb2a821465879516310a32c3aa8b18851947776544518ca3dbb2a0284658dd906155132caec630aa89966762185544cb39b0ec0aa2659c1876055132c76c8302a89965b63181544cb35b10c0aa2659cd846055132ce0c2302a89943f76550544
  | 18 => 0xc00000000000000080000060010004000000001800200200180040040010008014002000006000000400200680040000040008004000001001000801a00400000040000010000008002003001800000000000000000060010040000006001000000800400700500080020010000008004001006800800e00500000000000020008000002001000802c00000200100000020000000004000002002000c000000000000800200100180000060040078018000001000000000000100080000080000010004004004000001c0080000008018002002001000000000000000040020040000008000003000800800c00000000180040040010004000003001800000200300000000020010000008002007000000400000000000040040000018008004000000000800200200080280060030020000000000002000000000200080140000000000004000004000000000000000000000080000010008000000000000800000300000000000020008004000000002000400400300400000000000010004002003000000401200100080000080000018000000000001800001a0000000000004001006000c00a00000080000020010000000000001000800000000100080080040020008008010001001800000a0010000000002000004800000c0000010000002006000000801e0030030014002003003000400000700000000160000010000002001002000001c0020008004002001000000c00a00a00080180020000000004008000000801c000000000000c00400b00000080060000000010002001001001c004005000801c000007000000c0020020010000000000000000c00200e00700040060008deeca90a5a1c777654451d0e3dbb2a0286871bdd95214a438eeeca88a321c7b765405090e37bb2a429287591c55214943ad0e0a90a4a1c77715805250e3a38ac0292871ddd95114543ac8e4a88a2a1d70705445150e37b92c028a871b1c960145438f6eca80a0a1d68725405050eb838aa0282871ddc562141438e8e2b10a0a1c6f725845050e36392c2282870f5da5490c438baed2a48621e1d75d954310f0f3b6caa1887475cb6550c43a3ae3b2a8621d1e70d954310e8ebacc4a188747dd56250c43b2ee2b128621d94715894310ecdb82c4a1887661c16250c43d1ac43128621d1d759854310e8fbaac2a188763dc96150c43b18e4b0a8621d9b705854310ecc382c2a1887a55846150c43a3aeb3028621d1f755814310ec7b92c0a1887631c96050c43b2ee2b028621d94715814310f4cb00c0a188727dd943d4843d2a8730ea421e95435875210eb338ea52908787dd94354843c38eca1aa421f0f7250d5210f8639286a90878750f6154843c3a86302a421c9f7650c5210e37bb2a42908727dd943d4443d1a87316a221e8d4358b5110eb3396a32
  | 19 => 0x20000000003000001000e0020000000000002000800c0000010028004004000000000000a005000000000600000000100000020008000002000000000000a00200280000000000000000006000000800400a000001800c00200c00000140080010068000002000000000000000200380100020000010008000000002000000000500000000020030000000006000006001400000100000000040020000010000000000000000400200000100000000000004002000000800000000000100000000000000000008002000000800200000100180060010010000004003000000c000002000000000200600800000040000010000000000000000000200000080000060010008000000000000000000000300200280020030008000000001000000001c0010008004000000000800000400000000280000000030000000000001000800e001000000800e0020000000000000000001c0040060060000000000001001000400100880040000010008004000001000000c000003000002000c000001002801800000000000000040020000002001000000c0040030000000008005000801c002000003800c0060090000004002004004800c00600000080040060010000010000009000800800000700180040060020008004002000001800800800100080340020030008004006004000002000600000100000000030038000008000000001c00200000100000000020000000002000004000400400000200000000040000000000006000000401200000180000000000060000004000001000000000100000080060020008000002007000000800200000000000060000000004000000002800000000000000080040000000000008000001001401000000080040040000008000000003000000400000600000040000030018000000000000000000000200100000000080010000004000000800801400100000180020010018010000002001800400400000280000000090008000004005004801000000400100000140000000000000001002800400e00000000040060020000030004001000000c000001002000000a0000000004000001000000c00000100000100020000008000000000000000000000a000000000600000000040000000018004000004000000000000000000080020030030008012008002000000600000280000020000008008000003001000400000600000140020000000000000000003800000c00100000000000020008000000000003000400800000000100020020038004000000000000c0100000000004004004000000400600300280000000000008000000007002000001400300300080040080008004000002000803c00000100080040000010000018002002000000c002005000000000000100180000020030000
  | 20 => 0x5e0000000000005400066012c80013527f5471978c9344ae25e12c8000aae0000000e3e00046700000000005b8800026a4851fb0000cb80000001fac000b6544400000000003a080000000002fa80000000000000e580002a508b99180000000000fad6c6184331a6cd2081f203ea87166aa9f59280000003250001ef845c9860000a64dc0000000000012600000000007320000001cc4fc000014e0d147c812233081080000002198001794a430002cac00000019d00000000000000001738b3f0000b2000095c5d1800000032b0830eb80000991ab83b80000000559b88486bd81e4a60c00044f3408bfce261750000000000b0109c0000000a0700011354120002ef29e035c0001b59754f2c1df000289400000000000000000001fb8ab9690000000000006a1e439100600000000b8206cac60001c010605f000000005c40004163f1ab44ff8ac6000000000000029c000000000000000000001e7543291c000a22000000153600011900000be000356874cae63313e5800128e1130002ce009e944000046800000000000000000000000f080000000000000000be03f8a2592460004ca800000000000000000002c400017202400000000001434000284000171000015b8188aea00000005ccf567483128a9ccba2c1374800013e000000000000000018aafa05d809b02c2a4063a0000000000ede8b6000118ce9879d21180007e85334daab14000aab0000eecc6000000025c40000002e780012e004400014b4d8ca7700013d44fa04c0000f480000005cd00015dc000000000010800000026c161c0000002f7d3702943ac80000005e600000000001880001cac8e000045e800170a00050815100000001bfa17c00000000020dc6fc00014e83a8e9e04b17e83456527550000000efa0000bc80000000e50000000000441000000051e0005db80011d600000021e16540003d40000fe60000a5af2045a00000c800000000000019a40000570002014000000000098c000000000000016e0002eb000000009500000005c8a91000000033845200000000008a1000000000083e0670000902a76000169c00070a000000000000000000000000004ee000000000024c293400051c5b91e4943c52037b80003cc00008e0000000000000236c000000000106c00000000000012a400000007440001b900000000005a000000000000000002f00c6800016100011ba70d000000047e8942ae2a207a60005ab9e2c4b61db3c62504c982904f8800000000047b94bc0000f40000000000b2156500002620004bd0000e160000002710ab00000002bc42be3b351e80005f4000388a78c01c70928b0898e04000255131565a0000340040b3617d4c580000700b42418000672362000111c0020020004000000006803400400400000000020050000000000
  | 21 => 0x33a4300000000b5400000000000005ca00000000000000000000000a7a00000000000004b28000000551000131c2ee3490000e50cfe87f0d4000000000028f8d90f06000528800000038b000000085a00005e0c8040c0004dc80012862160000000a787f027800014000000000000c56659000288000000000000010962d5044254400027a1898cd00006b0000000000046b0e1ac61104835493183000025a3a903416fcb3600011a47302a4297059508a0a23871640000000000123d5766af09b000000000000000000003cd00024654fc65f2a52efc0008f90a70000e9c000000000169e000000000132400000000000000000002330f907bf3d814e8120a0303d0000a8622025f1bbc0009d13d100009904f70f7895800000000000000000000001ad80000000002c3c6e819307800012400000000e6c00000057aa82c57c000000263167c000000000000000000000012640000000000000000000000000000000000002ba11033c80000001ce23c15840000000000981714000000000000021a46980000004130000000aca00006b00000000000000000000aa71e08000d30bc303795d0a8400000000006be00049a000000068a0000000000000000000057600040d00014e483912b9a8c25600000007091a00004b415a5290000000184c000000497800000000000000005700000b029acf62bb40000000bba0000000afc000000000114c8b07e600000000b62b310094458062d62012c095c200045489b800045c09983d400005e00000000000002649a844cc6873fca279484a6904ea30926a0000d18000b7212400000015de372000201000000000000000000005be80000480004b200dc000b973d98000fa8ab73fd800000086156608e07d250051381b4dca7bb5151f848de9c00c380007dc78100004a45f68004750000000000000094d3980000001ce09fc76d000000000000040480012de00005ea4a8000000000246ca723d91d323d14721ab5c026641006265232e7c43c31f426000007a0074ef80013380001ff822d45ab4016a000000000000000006e60000000000000611166800049c77c4082aa14622810000c2128c72548fab788d88952cd20397d600000011fc000a6a0001d5051846a0001ce978c5280002aa94928b51b82a3000000000000009a6000196000131e6443db0fe0000000000193c8b20c400fa5cc288000000127448c00000000000009750000000000000000000000000000000015e8764487800000061a5e5872c3ba99111c97e80000000000f543280000298000000a8d0001e180005e75a18f30000000000000180400000023a40000001d080014700004c9a2a81c079e024266000000020e17c16fe9662c2a49c60202f01307f0b3c2aa1ad1c6c0000cd0000a245c600001380000000000000000000a2e
  | 22 => 0xe3a08d37f80000009b20001d10000000000000000093c01600000005135250000000147261a4e490ea9e36510c400000000000000000000a424a46ba18b0db9eb918200018211f08a8b1f217ae889d25961f18d489144cd0000000040000286157c00061e43e08955f89dd02913a81e61fb1d0155c9e494d11e019800026a26891944948423b507013de06113b0000000b5910590753920003e980009c0000000000000000038c000000000000000000004a3037192c0000000000000000ad23e3a4950de0004038f2c00000013e2704d5001d58d80016ee00026e800000000030209ac00037b0000d2cdc800051a0000b3a89024f82c00000000a100000006840002fe03f200000000000003510549e94abc00000007640000d821d2f695b488d2090164c840000001b306445144099d7400000000001740008800000000000acf00000000000000000000000b8400000000009a82722b5400092d29b800118eb8c000003484a25257512a56882e014a9e44ec40000000c680000000000bd80000004fa000000094f0000000000000000000000000000000000000000bb000105000000021cc00000000002813f40000000000ec20000001e140000000e80501742a5520710440000001c21884a360005b52f6cc2e000471220d5fca3339194a800019231400006200000000000faa5712c98000a0c9225be00000000000000000ba00000000000c3e0000000350000000000000000027f00000000006e80000001770000000000000097400013652840000000908f360330000000000000000219072096100000014986a202d13696be26700000000000000002da172200030c800000000000000005a40000000ba000002d0600bf0000b490fa80000c000060080010e85ee000000022800002b063400065e3dc8000c0c0df00021601b40002de151c00033615e80009fe0001eb8000000000000000000048d3fd18dc0000002f48000f109b4116000000000000016a48e200000000000000002ae80016580005e48de92b21e9000000000000000000013b60003f40000000b1700000009c4a8b1fc974c0004c600000000006c4396000000000025300000000001b1800054400041b000175800000000000008271098834e3487e5cd8000000000000000054000017380000002fe00000000000001e89b6450e53b30e227c00010121417354020003bf00014466dd3c00000d7400045f212000035e0000000e2c7420000298000000000000000011e542a8f014e0000002b6c19e6bf0000c64fb40000001384000000000050c00000000010340268bc4408f7d514000252800000050e00000000000003ae1b4c07832a00000002da58c000000143e9cb000056088c8f000000015d067c4c20fe88645990001d5c00000000008acf9a000000000
  | 23 => 0x169800000000000009bc0000000000000000199130a000000122c2682192ab00000009e0293800151217f0000bb800000000000000000004031a000000002e2000161ab1c5bd2ab4d040004d180000006fd0000840000000000190c000000000059c40a0635259e54000366000000896a0000000cb40000000000000000000000000069a00000000010a879f00004840006d43f60f74a7e000000000000028500000000000001bca5d86debd92f00570af0a82157800000000000000013f000000000000000004c52550bf800000014c8000000104000114800002e00000003c3000000105200000000002368533dc00000002ea31e841c65200000003ad73c4ab0000000b5ab5d1660ef43dc60100000000001ad07312117403b04989cb80002970f09654dd651d0002b9800000000000012b684000000014605d8398000000000000005040009242f400000000000002b04e420001779a34000000118abe000039e3658000cd0a19163233545842600025a4000000485000021eb513a39de81042044a2800000045e4c49bc0fee92c1060000eb63550be2d295780004d7000000099000000015c871e00000000000000660000b4638227305c800000000015e48943c000000017c80000001e2513200000012b4000ac0000284c0000f85241424e4e00001d042952e0000110000000000000163c000000000000168c87d00000009e234e457000000000000000000006b70000a78d800002fc80013002ac4079bd97021c84ca0e1977665621b0f203666472f603ec59c0fa000176400008c0008000c6cb3d4b7000140c74d000177c0000001cf8000ed04b806996d40009504fc80011e4000457800000000013100000004d503e000000000000027a902c00047288a89185d75d200512aa00044796ac8d0b7854397944da7bc33987114ac7e5283a6ed5a000008712380000002b7055d19218100000006f03122cf80011d041000026f800059200029d40f00510002698000000000000000000028200016da0004328000522a635940000c78912000000000079905da47849200059723180000fd29605980000005f100000000000000d4000000000000008b40000001951016717000000027600000005d16d827b00000000002f91a18000c1e00057f800177a0002e080013d60005b314692b012a00013496e601b0001a7562c0000000000000000000055800044429e8eac0000000c8a22c1149a053323fc000000000000147e4cf0a88cec8806293e026353ae6bd2d800000001f700009b0f408c349f0000da00000000000000000000037800000000010d10f658606d907c60468b107ab081820002a627d97dc0a110a0e7514665800000009383a925a0000000000000000163c0000000000016000000000000034100027dc00000000000013b000
  | 24 => 0x1550fa0000000000000000000000002f4887387a73414a00019b800046a0004cd8000000886101a7a00006910002238fb032442e80000000000000000df6bb63fe9ebc0e082142a91cc000a935718f38000119558000170e03e00000000002454cf27b42bc84a435a1c45727a11aca6c4d1e0004e1000129c7ef60023ec0000005e880003d62f72a80000000000000000000000000007fc0e47d75780b680000000001a540005b64d29bccc360971a200015b05702f68000000000000000000000000005bc00094b00015fc0000005420000ed673f00000000004bd193acbc04a0000000000000000000116c00000039c87540003bc1a315a0ebc8460000000342b085b4814031e9d3000000000096b0eb82b4f0e9a72a0239cceeb143e3000061a77f0000c3d4567a62ed000000000000000016a86e308682e90c64671e7805d4c09e619f0000f840005ad9b980000000000000000b611ee0ed80940002818fc80d200038c882400000000000000ce00000000000005fd09b9a70b809570000000000000000000000000054b0e5c0006d20d900011085830000000000000000230000000009e025800000019800000000005b20000c62bcd16f00000000002a9144000000002300000000000002dd0000000000000000000000000015fa9f20000000000000000102400063800027b0c580000000001668b19567061849e8b700000000004f900000000001de077a4ad7d4000000000000000000000015b20001090a3440053e0000000f300003b48e90000000000000175c15500001c4bb80003359d5800000000000000000000e9000000056436495bc00014f00011d000094c000159c0000001b390b89943e10000000000004406000000010b0000000000be300000000000005142d780000ae000000175e0005b3ae4971a00000000000005b700007280000000001f30000000000000120c6450000ed08ec3e209817fc000639000000000074602700000002a600000000000000d8ac149329d629080000000002e480000009212371d440000001f796ecef097e00016380001984c413bcf9c19b2b3000000069f00000000004d01f9ab1c1386d71c08000000000506010c0000003460ea8000000126071800056a58e800000000009e8000dbc06500000000000000f880006ca0004db80000000001df8000dea00000006f400000000000007bc33500002a957e0310000f2927a5ce21206c080625d0c829ec9367ed3049fe108e14d1542be861c368265a720000000000000000000000000000007a400000004aaa625fd00016dc0000001eb0000a7349f80005a094a4541b080008894af129c6fa36000000000005bd00000001a46cf0f98000000000000000000084f00012488543e70001f640000000001ac8b1263f33322c89a8be92c000
  | 25 => 0x11200010b68ef015000113a0003892d580000cb0000000000b320001e5c6dc535078a09516815910d8d3c4760000001514b664940000ad80001830000000d0600000000000003ac000000067e000000286c000000451000020000000014d80000002670000b744ed0001d000000000000ca0c92000000000000062d00000002a80005b106580000003ba0000000776039a90400000000000000000002a71448ee20000f6000000000001c80005b8a1640689000008683ac11ed6140004d6000000096a0001e4c000ba509780002124fc3190a58d6699a38410f43b8a36261271833e7d60000c78fd400000029840000000001bf8b3074918d937cfba75a1d282c8e7c00022b045416c9f03ef1288ba25bf0001190e4c5b1000000086eba834da608c0a3213c106a907800036a80000000004e386bd3a000034f133176600000020f4000902591906544231600000016b8ac300000000001e5347000000000000000000000005fd94880003d0118000071a2cb3629e9c000a8131197f86460000001028ab466500026fce8a251499800000000000020080000004f0aab00000001518000e28000141ac91730bef000000000000000006d91706120000000000b701d7a8d49e83fe09d2c2425ab9d0000000000ae2549000175a00035aaa3c78ca5f54e80000006a600026bc0002f51c70104bc2aeb000000000000031100000000000610b99528000052000171e0000000000000000000000169a000000000110a00006297d16a00000000000000000000000000000000003249c65ea32894a40d60005e71ffc0001a700012011884a82d11791220000564a9400001cf0001b70be40000001f0c0000000000000000bd54dd1e340005b400000000000000000000000a68000000017e00000000000000833a98000cfa91a00000011f400000000016009ab50400000005971c3800041c0001b500007720002b6a57c00000042480009668fe0001748000000295800121aa3a33907040000000001414b840000000000000a5a0000000edc0000001aa80d8000000000000036c1221fb8a8c0745fa0000000000000271400000000000000001163b300007b61044fe0ac80000000002398000b45197192000069915a0000bee00030a91dd3ea27340500000001023dd000000000004a0001452b6b0002c9d4c8000111a7fcb5caf34788000e2a7dc480802517263a42b1ec88ba000000000000000049700012c47675de17ac7ca0001a38000000000000111400000056b800146e51e000228000014521e000160c6d10000000000000000000000086d0002fdc0000004ae8000122b9500012c40008d2000000109a14a000101418c0e924a8000fd257a00000014ce63e43100001c80000000000b500000190a1800000039780000000005fc80008100
  | 26 => 0x8010000000f1400000000000000000002ef8dce07b000000033400000000008c065a00000014f2000000171902400022f996c000000325181c00000000023e00000000200000000aa64de8a484384d7329180cc485f80641c0c0001a457620d15320004ff12440007000000000bc43da0000000000690000000050401121a912427e5480002a892f275f00020795a6be503c972d1180000002c895f21f636400005d662a000294c00058d1ac233d2ee734250940400060018580017e40000000000c660002410000000b7b00000012b40005372044bb600042ba0c40000004ed0000000000000000000066e0000001500000000267400085e00000008fc0ca00015557aeb3114713e0a16a02097000120a5b8221165153000000019ec00061405caea4000b5a0001f6d5622930000000948000000000000000000000005940000560000606a0f00000017160003b00000000b7900000000000000000000000ae70000a8400000000011540000000002d4d0d48e12c894d0560000000000000000048b0444d4e00000000000000000000000000bba4642b800009d90428001754000000000000013e23d1c14b4c11f0000000000000000000059e32f0000000000000000000000000036680005340000000a2800000000e0ea000000000019d80000005272cc0de2b8e0002e4cf923ad00028ed5be76c3bb8d4c264af236f80000003184be10883f00000000000000000000058c0003fb015800000000052f06546140000001a140000000000ddc7e272a0719ff874ea0544b821d704000000226114a8d40002abc0000000000000d26b0b007800000000000024004ea00033c00013f6000006000105e000000000000000010ea91400087500000000000000000000000a9a0000000000bf6000092000016b0001524000b8303f0000000a2f0000000000000000000133e2331dd20ac000bd45f823f400000000000010b838a55b000037c9c30001de42a683a50ea5b56660002df2dd51240004e900000000000000000000000489a4c000000000023cc00026456a00005a20000001e50f5437100016b000089b1c2885c78e51832ba228b168ac13c0db567444307c903c00000016d9a24df418a4c380017c2a1800010f94a873541d80000000000ad2098b4a3545ac07240000003a800000000000470f5800000000000017d88bb0002cdc82800001729bc4524f30002c1c0002c5000000000030600000004be40b260800000000007093d80000004338e8800000000000000008fc00000000000dd00023d40000d9000000015ebd6000000039a8325620000d9c000011ad380004bb00001fc0001bc1038000000000000000153800005c293cdb0000000005800000000000000000000000000c20000093ab2108200021c8000cfc00000000000ec8600000
  | 27 => 0x478000000a7400029c0000000000245c0000000000001414b1319e80000001fd000000000000000000d0a32a584b92d0853e18c0000000112b89559994ce940005ff8000000aa95aa8584aa65880b200009b800035c000119497b00027546ea0003969f880000000d48c9800000040183dc2d086c23c9a493c4000293000029800021da1dc8a00001e215640005a10000fb13d20000000000ee00000001ea408e00000d04a000000000000000008f620209500009151dc1d2c0000003f9000000081d000106883c030310103167633c132af487a800004f00005c42770149828000000000000058e00008c1b68bf64b90000000d2c949170800000000000000015b82f0416000174e4ba30711c94082e55cb00000004eb000000000064d37a00010602ed0a305f80000000ff1f15622000000000027200a3440e540000000000664e020003271af1798ae9000000000063500000000009ce57b9ab8374000576ac0c00000000000006b600000000011ae000200000000000000000000000000000000fce3e843319b14b850f51f000000000035600000000000001dec000000000000168e9ca27429fc00000039e80010b4bb10000e8c0004b01df20541da2b100000000006ab43b2344000bdd55a8000000000000000000031c00019400008df000061400000036b0000000a71000094043e22700000000003330002c3004200000000010b200000000000000000000000000b9400015040c89531fe800000090e00029b400000000029f4000000000000024a0001f80000e40000485ac40bec0000000e24000221000000000000000000000001f000012180000000000000cde49e0000e201b85f15a5800000057c06b800042a8235ee158000000000003540000000000000000bb207f91217206db5ccaf98802a5900000012fa0004391018c8266d352800000033252d8bcc0009400000bd000000048ea0b960862f000000000042045980005105c300002680000005bb2050000000484092c00000000000000008ad1db88f4f1c0000000c240000000000ba400060846580004fc0001f000000004db483800000000001da55884e8c5000000000049300000000006ec000000055a00000000007da69a0000b0c00008139e00000000005b780014222d9000000000000030c0000000000000000000005540c2d800000000000000000000000000000000013780006f80000b4aae800000000025e0c3a93700000014800000000000000000285000000000000000000000000000000000000000000000000000000003009185da86814babb058911d44c2af613920900000005d32750000000566aa550f4bc13da1c1000000000000000000004888000ae49fd0000000b045770000000000000522245000000000000000003380000000000
  | 28 => 0x2b7400066200000013ca20a1b4800000000000014540002d70352c543040000000000000ae55dc871ce6e1fa00003f8d52000000078d7da0004772b2c5e400000000000006c31ec0c309800001bb000144c2222bb00000004d800000000000000000001542000000000000000000012589ac10834328380002ba0f10000df200041c000048e00015e000087e7242981bb525042b248000113400000000000000000000000050aa40bd80000006400001628f466a446e0000000728000000069815227e85249dc43800018b80000000000a10536000000000000031455a11381863110d2800071818e0001f2855644c50a1198e2054d089265902e0000000000000833000000000000000000000006be43715ac46824100000008c4000086000175600000000000000000000000b8e00000000000002744558000000000000273c0007bd4b38ff020a87900000007341a63c2000000000005a80007cc1d8214a40c7386c137e00000000000790d580000004b1800000000000009a046e00000000003b496c00006d420624d12e068800054f0000b0000000000026845520000000000000bc400000003685172308b6040400000000000003003e08000000000404285c000000000000000083f000000000000012f00fc00067a000000114c0000001dc800057e000000000030700000000006b14c080000000001a1000000027900017cc000000000000151c3c50002d040005240000000000000000000000000000000000000000961ad00000003b981d40008da3dba5fcb4882036380000006975f3800117470c11b279d564bcf2d7aae5424b2046c000000082a4720fd40004bf0000000000bc50002ff40000002738d00a044ec38380000006f800000000000004d526d895e0000000000516000000112c00000000000000007901348474000bc2000000045e3ea5290000000000438000000000000027b882e59c3fa000010c41500015897f88523e902c400074300000000000000002fc400078f00000010d2ad600011440060a31a42f7800000000000000008e015a88441240000001f440000000002af9122000000000142a4b60000000a46000552a1443d0000000000167248946ca378ce09de01b000072600000000009f462727285a83a893655c0e481501cc5e980000009601c792b0e0c0060002a813c80000f01d8c0008a747603f11262280ad80004e200059e0000c1600000000000000f6000000000000000020880000002be800091093a2c385b14d8bf335012dc0000004d224256a4000000295c0004074d10000a1a00048e00000ee0e81d9289085800000000000000c70dc1f7c000000071000000077500008e800000002a00000006550000000e529f3182999c0006f239b1d951dab1a0000000376bd004c
  | 29 => 0xa0000000000b98a7c00006fd0a0000000000000001254193781d80000000b7c0008d500018089400002ad87a91380e73fb161017c6ee0001f3c53000045880000000000000000000bfe00000000001f400000000003b113819c509c5b2000000000000000000000000000001714ce82dd57d88f82c400000000000004972bd80004b00004860b4c00000000000000000001c1800164c0000229b84e64000000000157a0005c300001668b035c800000000049d908400000000000000000002620000000000421849800093800000000000001b098ecad80000000000f340000c48a003ac0000001cec00046d0001f90000000000000062e0000268bc40001ed00020709f671c0d60000c1a000000000000000000018585927ad41680000000004c705400000002988000000000000000000000000000000000000cf0000000000000115ca9684400000000000000000000a4a66a55180002dc0000040d7000000000000000009ad0249f1076a0000001ba800000000f1aec000a650000e4503200033a800032e21800011f4000000000000000000000000000000005069ccd32ebc70000000f6a123000207d4640000001e700000000001a517ea0000e280000000002ea00011ac5ef45f960400034a000000000
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x56294043c0d43dc96194043a50805846154c42c0e765c85450f32d05729c45450f32a30805846155032a48805886254c41a0d8694d4210841c0d645ca530c841a1581991530c841915859cc4250441c16765c45450f31d06725c45450f31a28805886255031c15545c66310831a0d829516310831a0d86951320c831915859d0324c431a18805516315121c19641c15314d21a0d82d954310d21a1581d954310d2181c875954310d21a18805954310d21a158315161d0921a158414d61cc921a0d8315162d0521a0d8414d62cc521a84835906448421aa0805906448421c85645cc6448421a848458c6348421c857458c6348421ac08058c63484218e0805d84348421a848650c4348421c857650c4348421ca0641c12154021cc0631c12154021e21644855014021e41634855014021a0d8694d4210b40c0d645ca530cb40a158694d4110740c15645c6530c740d42531c12108740a1581d9543cca40a0d82d9543cc640a1581195434c840a888250c604c840e0943548604c840a0d82195434c440a908150c604c440e1143544604c440a0d831915248440a15831915148440a0d829516310b30a0d86951320cb30a15819516310730a1586951310c730d22541c12108730a1581d9543d0a30a0d82d9543d0630d05729c45450c30d06725c45450c30d05725c45450c30c1a769c05450c30a15811954350830a888250c6050830e09435486050830a0d821954350430a908150c6050430e11435446050430a0d8418d5248430a158418d5148430a8882590404c030a9081590404c030a1581d954310f20a15819516310720c15645c6530c720a15811954310e20a0d839516210220a0d8494d620c220c0d635c86315120c0d645c86414d20a0c8550d6210d20c0c7550d6210d20c89431c16210d20c0c7558d4210920a0d8614d4210920c89631c14210920d08531c14210920c0c75591320c920a0d86151320c920c89641c1320c920d08541c1320c920d05435c84314520960805c84314520d05735084214520b20805084214520d05744c83214520b40804c83214520c88741cd6008420aa0845c06148020ac0835c06148020cc2731874048020ca2741873048020a0d82d954310f10a0d829516310b10c0d645ca530cb10a0d821954310e10a15839516110210a158494d610c210c15635c46315110c15645c46414d10a148550d6110d10c147550d6110d10c91431c16110d10d05435c44314910960805c44314910c147558d4110510a158614d4110510e05631494110510c91631c14110510d10531c14110510d20521c14110510c1475591310c510a1586151310c510e0564149310c510c91641c1310c510d10541c1310c510d40521c1310c510c90741cd6008410aa0845c06244010ac0835c06244010cc27318b4044010ca27418b3044010
  | 1 => 0x33800000000000d84d290b4480a420a0e610049f91c4b3422cdc8038854ee0706a351226149e4ba63391000c2c1a8f08c4911a3114213f91030252995098131d87894043b088d2372403036411d1ac0681311c120203011cb6122b9641e660003910453c0e0fa1a2114400390f8007a6d2c0c404011b0009e3300178640000050f400280bc9c0000000be7500000163e4120cac000005cde000c9550a00000fc68003e000c200170010c05139a83a0008870f600158211e74329690e3015190b8000b00086090a2d01020036020b110000040602010f034803020000001d11010015040000010204120e02060307050205002d0305917815cb6550c4390f825c76550c43a84815886250c43a88805886250c43a84825846150c43a90805846150c43a88825806050c43a90815806050c43c1543dc
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x16d00066701207818a1040000087414201005a40482c8b98c890843881742016318d2108610930bb28621a4210d202417650c4348421a044aa86382c421a414099614c70508424828132c2a0e0990649064050c805c84314520c80b9900a108428a4190174201320c8514828212aa18e0b08868864050c805c44314910a08cb0a63828220a21c016314870504414428232c2a0e09886288700590521c1310c510
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 40
  | 6 => 1798
  | 5 => 7915
  | 4 => 3076
  | 3 => 145
  | 2 => 16
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (i*5) 5
  | 7 => packedAt gbK7 (i*16) 16
  | 6 => packedAt gbK6 (i*27) 27
  | 5 => packedAt gbK5 (i*38) 38
  | 4 => packedAt gbK4 (i*49) 49
  | 3 => packedAt gbK3 (i*60) 60
  | 2 => packedAt gbK2 (i*71) 71
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (6+((h/1+packedAt gbK8 (5+(h % 1)*1) 1) % 2)*1) 1
  | 7 => packedAt gbK7 (718+((h/13+packedAt gbK7 (640+(h % 13)*6) 6) % 49)*7) 7
  | 6 => packedAt gbK6 (55734+((h/599+packedAt gbK6 (48546+(h % 599)*12) 12) % 2610)*12) 12
  | 5 => packedAt gbK5 (337702+((h/2638+packedAt gbK5 (300770+(h % 2638)*14) 14) % 10448)*14) 14
  | 4 => packedAt gbK4 (164049+((h/1025+packedAt gbK4 (150724+(h % 1025)*13) 13) % 5944)*13) 13
  | 3 => packedAt gbK3 (9084+((h/48+packedAt gbK3 (8700+(h % 48)*8) 8) % 175)*9) 9
  | 2 => packedAt gbK2 (1161+((h/5+packedAt gbK2 (1136+(h % 5)*5) 5) % 24)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xe03ffffc07fffff03fffff83fff07ff3e3f1ff
  | 1 => 0xffc07ffff80fffffc0fc1ffc3fff87fd1c7e3f
  | 2 => 0xffff80fffff01fffff001fffc3fff87e1f8fc7
  | 3 => 0xffffffe03fffffe00003ffff8fe00ff8
  | 4 => 0xffffff000000003ffffffffffc00000ffff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x29850a04712244800b2c258044b0089061b0db
  | 1 => 0x4293144890e48912c0550aa4295485250c562d
  | 2 => 0x850a26912241d2255502134a8269504a168b46
  | 3 => 0x162c58e2448903b9a69b4062238e660fa00db0
  | 4 => 0x183060c3870e1c3e38e39c73300c440fdb6000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xeae8e880eae8e880eae8e880eae8e880eae8e880eae8e880eae8e880eae8e880eae8e880eae8e880eae8e880eae8e880eae8e880eae8e880eae8e880eae8e880, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12941
namespace PEqualNP.Outside.L_meta_12941
open PEqualNP.Outside.L_meta_12941.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 16 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_96 : Interval gbAtlas 3 96 49 := block_range (n:=49) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 145 := (concat bgb_3_0 bgb_3_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_192 : Interval gbAtlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_288 : Interval gbAtlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_384 : Interval gbAtlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_480 : Interval gbAtlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_576 : Interval gbAtlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_672 : Interval gbAtlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_768 : Interval gbAtlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_864 : Interval gbAtlas 4 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_960 : Interval gbAtlas 4 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1056 : Interval gbAtlas 4 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1152 : Interval gbAtlas 4 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1248 : Interval gbAtlas 4 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1344 : Interval gbAtlas 4 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1440 : Interval gbAtlas 4 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1536 : Interval gbAtlas 4 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1632 : Interval gbAtlas 4 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1728 : Interval gbAtlas 4 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1824 : Interval gbAtlas 4 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1920 : Interval gbAtlas 4 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2016 : Interval gbAtlas 4 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2112 : Interval gbAtlas 4 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2208 : Interval gbAtlas 4 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2304 : Interval gbAtlas 4 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2400 : Interval gbAtlas 4 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2496 : Interval gbAtlas 4 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2592 : Interval gbAtlas 4 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2688 : Interval gbAtlas 4 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2784 : Interval gbAtlas 4 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2880 : Interval gbAtlas 4 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2976 : Interval gbAtlas 4 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3072 : Interval gbAtlas 4 3072 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 3076 := (concat (concat (concat (concat (concat bgb_4_0 bgb_4_96) (concat bgb_4_192 bgb_4_288)) (concat (concat bgb_4_384 bgb_4_480) (concat bgb_4_576 bgb_4_672))) (concat (concat (concat bgb_4_768 bgb_4_864) (concat bgb_4_960 bgb_4_1056)) (concat (concat bgb_4_1152 bgb_4_1248) (concat bgb_4_1344 bgb_4_1440)))) (concat (concat (concat (concat bgb_4_1536 bgb_4_1632) (concat bgb_4_1728 bgb_4_1824)) (concat (concat bgb_4_1920 bgb_4_2016) (concat bgb_4_2112 bgb_4_2208))) (concat (concat (concat bgb_4_2304 bgb_4_2400) (concat bgb_4_2496 bgb_4_2592)) (concat (concat bgb_4_2688 bgb_4_2784) (concat bgb_4_2880 (concat bgb_4_2976 bgb_4_3072))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_0 : Interval gbAtlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_96 : Interval gbAtlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_192 : Interval gbAtlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_288 : Interval gbAtlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_384 : Interval gbAtlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_480 : Interval gbAtlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_576 : Interval gbAtlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_672 : Interval gbAtlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_768 : Interval gbAtlas 5 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_864 : Interval gbAtlas 5 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_960 : Interval gbAtlas 5 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1056 : Interval gbAtlas 5 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1152 : Interval gbAtlas 5 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1248 : Interval gbAtlas 5 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1344 : Interval gbAtlas 5 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1440 : Interval gbAtlas 5 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1536 : Interval gbAtlas 5 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1632 : Interval gbAtlas 5 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1728 : Interval gbAtlas 5 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1824 : Interval gbAtlas 5 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1920 : Interval gbAtlas 5 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2016 : Interval gbAtlas 5 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2112 : Interval gbAtlas 5 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2208 : Interval gbAtlas 5 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2304 : Interval gbAtlas 5 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2400 : Interval gbAtlas 5 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2496 : Interval gbAtlas 5 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2592 : Interval gbAtlas 5 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2688 : Interval gbAtlas 5 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2784 : Interval gbAtlas 5 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2880 : Interval gbAtlas 5 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2976 : Interval gbAtlas 5 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3072 : Interval gbAtlas 5 3072 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3168 : Interval gbAtlas 5 3168 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3264 : Interval gbAtlas 5 3264 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3360 : Interval gbAtlas 5 3360 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3456 : Interval gbAtlas 5 3456 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3552 : Interval gbAtlas 5 3552 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3648 : Interval gbAtlas 5 3648 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3744 : Interval gbAtlas 5 3744 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3840 : Interval gbAtlas 5 3840 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3936 : Interval gbAtlas 5 3936 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4032 : Interval gbAtlas 5 4032 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4128 : Interval gbAtlas 5 4128 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4224 : Interval gbAtlas 5 4224 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4320 : Interval gbAtlas 5 4320 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4416 : Interval gbAtlas 5 4416 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4512 : Interval gbAtlas 5 4512 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4608 : Interval gbAtlas 5 4608 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4704 : Interval gbAtlas 5 4704 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4800 : Interval gbAtlas 5 4800 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4896 : Interval gbAtlas 5 4896 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4992 : Interval gbAtlas 5 4992 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5088 : Interval gbAtlas 5 5088 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5184 : Interval gbAtlas 5 5184 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5280 : Interval gbAtlas 5 5280 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5376 : Interval gbAtlas 5 5376 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5472 : Interval gbAtlas 5 5472 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5568 : Interval gbAtlas 5 5568 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5664 : Interval gbAtlas 5 5664 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5760 : Interval gbAtlas 5 5760 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5856 : Interval gbAtlas 5 5856 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5952 : Interval gbAtlas 5 5952 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6048 : Interval gbAtlas 5 6048 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6144 : Interval gbAtlas 5 6144 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6240 : Interval gbAtlas 5 6240 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6336 : Interval gbAtlas 5 6336 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6432 : Interval gbAtlas 5 6432 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6528 : Interval gbAtlas 5 6528 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6624 : Interval gbAtlas 5 6624 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6720 : Interval gbAtlas 5 6720 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6816 : Interval gbAtlas 5 6816 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6912 : Interval gbAtlas 5 6912 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7008 : Interval gbAtlas 5 7008 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7104 : Interval gbAtlas 5 7104 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7200 : Interval gbAtlas 5 7200 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7296 : Interval gbAtlas 5 7296 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7392 : Interval gbAtlas 5 7392 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7488 : Interval gbAtlas 5 7488 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7584 : Interval gbAtlas 5 7584 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7680 : Interval gbAtlas 5 7680 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7776 : Interval gbAtlas 5 7776 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7872 : Interval gbAtlas 5 7872 43 := block_range (n:=43) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 7915 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384))) (concat (concat bgb_5_480 bgb_5_576) (concat bgb_5_672 (concat bgb_5_768 bgb_5_864)))) (concat (concat (concat bgb_5_960 bgb_5_1056) (concat bgb_5_1152 (concat bgb_5_1248 bgb_5_1344))) (concat (concat bgb_5_1440 bgb_5_1536) (concat bgb_5_1632 (concat bgb_5_1728 bgb_5_1824))))) (concat (concat (concat (concat bgb_5_1920 bgb_5_2016) (concat bgb_5_2112 (concat bgb_5_2208 bgb_5_2304))) (concat (concat bgb_5_2400 bgb_5_2496) (concat bgb_5_2592 (concat bgb_5_2688 bgb_5_2784)))) (concat (concat (concat bgb_5_2880 bgb_5_2976) (concat bgb_5_3072 (concat bgb_5_3168 bgb_5_3264))) (concat (concat bgb_5_3360 (concat bgb_5_3456 bgb_5_3552)) (concat bgb_5_3648 (concat bgb_5_3744 bgb_5_3840)))))) (concat (concat (concat (concat (concat bgb_5_3936 bgb_5_4032) (concat bgb_5_4128 (concat bgb_5_4224 bgb_5_4320))) (concat (concat bgb_5_4416 bgb_5_4512) (concat bgb_5_4608 (concat bgb_5_4704 bgb_5_4800)))) (concat (concat (concat bgb_5_4896 bgb_5_4992) (concat bgb_5_5088 (concat bgb_5_5184 bgb_5_5280))) (concat (concat bgb_5_5376 (concat bgb_5_5472 bgb_5_5568)) (concat bgb_5_5664 (concat bgb_5_5760 bgb_5_5856))))) (concat (concat (concat (concat bgb_5_5952 bgb_5_6048) (concat bgb_5_6144 (concat bgb_5_6240 bgb_5_6336))) (concat (concat bgb_5_6432 bgb_5_6528) (concat bgb_5_6624 (concat bgb_5_6720 bgb_5_6816)))) (concat (concat (concat bgb_5_6912 bgb_5_7008) (concat bgb_5_7104 (concat bgb_5_7200 bgb_5_7296))) (concat (concat bgb_5_7392 (concat bgb_5_7488 bgb_5_7584)) (concat bgb_5_7680 (concat bgb_5_7776 bgb_5_7872)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_0 : Interval gbAtlas 6 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_96 : Interval gbAtlas 6 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_192 : Interval gbAtlas 6 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_288 : Interval gbAtlas 6 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_384 : Interval gbAtlas 6 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_480 : Interval gbAtlas 6 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_576 : Interval gbAtlas 6 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_672 : Interval gbAtlas 6 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_768 : Interval gbAtlas 6 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_864 : Interval gbAtlas 6 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_960 : Interval gbAtlas 6 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1056 : Interval gbAtlas 6 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1152 : Interval gbAtlas 6 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1248 : Interval gbAtlas 6 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1344 : Interval gbAtlas 6 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1440 : Interval gbAtlas 6 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1536 : Interval gbAtlas 6 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1632 : Interval gbAtlas 6 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1728 : Interval gbAtlas 6 1728 70 := block_range (n:=70) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1798 := (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 bgb_6_288)) (concat (concat bgb_6_384 bgb_6_480) (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)))) (concat (concat (concat bgb_6_864 bgb_6_960) (concat bgb_6_1056 (concat bgb_6_1152 bgb_6_1248))) (concat (concat bgb_6_1344 bgb_6_1440) (concat bgb_6_1536 (concat bgb_6_1632 bgb_6_1728)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 40 := block_range (n:=40) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 40 := bgb_7_0
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

theorem boundgb (cert : Complete gbAtlas) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 5 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xeae8e880aa888800eae8e880aa888800eae8e880aa888800eae8e880aa888800eae8e880aa888800eae8e880aa888800eae8e880aa888800eae8e880aa888800
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 0 32) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,7,39)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,7,39)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3937069192 * 2 ^ 32 + 3901259776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def sample6 (r : Row) (i : Fin 6) := bit r (fullRoots.getD i.val zero)
theorem table6 : ∀ r, posted (sample6 r) = bit r fullWord := by decide +kernel
theorem raw6 : List.ofFn (fun i : Fin 6 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
theorem eval6 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs fullRoots).getD o zero=fullWord := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample6 r) = fullRoots.map (bit r) := by rw [←raw6,List.map_ofFn]; rfl
  rw [←bRead,exeBits gs r fullRoots (fun g hg => (legal g hg).1),←e]
  exact (h (sample6 r)).trans (table6 r)
theorem binaryLower (low : Lower true fullRoots fullWord 10)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 10 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval6 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_12941.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,4]⟩,⟨.or,[0,1]⟩,⟨.or,[1,4]⟩,⟨.and,[0,8]⟩,⟨.and,[2,3]⟩,⟨.or,[9,10]⟩,⟨.and,[9,10]⟩,⟨.or,[6,12]⟩,⟨.or,[5,13]⟩,⟨.and,[11,14]⟩,⟨.and,[7,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3937069192 * 2 ^ 32 + 3901259776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3937069192 * 2 ^ 32 + 3901259776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hs
  obtain ⟨⟨gs, o⟩, legal, hsize, correct⟩ := hs
  by_cases clean : ∀ g ∈ gs, g.op ≠ GateOp.not
  · refine ⟨⟨gs, o⟩, ?_, hsize, correct⟩
    intro g hg
    obtain ⟨op, len⟩ := legal g hg
    refine ⟨?_, len⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op ⊢
    exact op.elim Or.inl (fun h => Or.inr (h.resolve_right (clean g hg)))
  · push Not at clean
    obtain ⟨a, ha, hop⟩ := clean
    have lo := binaryLower low gs o legal (fun x => correct x)
    have less : gs.countP (fun g => !isNot g) < gs.length := by
      by_contra! bad
      have e := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length bad) a ha
      simp [isNot, hop] at e
    refine ⟨⟨mono, 16⟩, monoShape, ?_, fun x => monoEval x⟩
    change mono.length ≤ s
    have hm : mono.length = 11 := rfl
    change gs.length ≤ s at hsize
    omega
end PEqualNP.Outside.L_meta_12941

open PEqualNP.Outside.L_meta_12941 in
theorem PEqualNP.Outside.L_meta_12941 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3937069192 * 2 ^ 32 + 3901259776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3937069192 * 2 ^ 32 + 3901259776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
