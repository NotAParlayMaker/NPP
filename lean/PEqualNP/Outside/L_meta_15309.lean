import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_15309.Model
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


end PEqualNP.Outside.L_meta_15309.Model

namespace PEqualNP.Outside.L_meta_15309
open PEqualNP.Outside.L_meta_15309.Model
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

def SBf (j : Nat) : Nat := [2, 3, 4, 5, 5, 7].getD j 0

def tips (raw : List Sig) (v : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let b := v % 256
    (b/36,raw.getD (b/6 % 6) zero,raw.getD (b % 6) zero)::tips raw (v >>> 8) n

def deadTest (raw : List Sig) (ws : List Sig) (k hint : Nat) : Bool :=
  let j := min ((hint % 8)-1) 5
  let d := neg (raw.getD j zero)
  let cs := tips raw (hint >>> 6) (hint/8 % 8)
  (makePool true d raw cs).any (fun pool => poolCut true d (SBf j) k cs.length pool ws)

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
      Slice true (roots g) (target g) (neg ((roots g).getD (min ((tip g k i % 8)-1) 5) zero)) (SBf (min ((tip g k i % 8)-1) 5))

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

end PEqualNP.Outside.L_meta_15309

namespace PEqualNP.Outside.L_meta_15309
open PEqualNP.Outside.L_meta_15309.Model
def s0K1 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 1 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 1 => packedAt s0K1 (i*3) 3
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 1 => packedAt s0K1 (4+((h/1+packedAt s0K1 (3+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffffffffffffffffffffffffffffff
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffff8b
  | 2 => 0xffffffffffffffffffffffffffffffffffff95
  | 3 => 0x26
  | _ => 0
def s0Atlas : Atlas := ⟨1,rawDecor 14 s0Pos s0Neg, 0xc000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_15309
namespace PEqualNP.Outside.L_meta_15309
open PEqualNP.Outside.L_meta_15309.Model
def s1K2 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s1K2 (i*4) 4
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s1K2 (5+((h/1+packedAt s1K2 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffdf0ffc1fc7
  | 4 => 0xffffffffffffffffffffffffffffffffffffff
  | 5 => 0x6ff0ffe0f8
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffff81222d295b
  | 2 => 0xffffffffffffffffffffffffffffa2e4571ac5
  | 4 => 0x4489a54ae
  | 5 => 0x188ee398f0
  | _ => 0
def s1Atlas : Atlas := ⟨2,rawDecor 53 s1Pos s1Neg, 0xaaaa0000a0a00000aaaa0000a0a00000aaaa0000a0a00000aaaa0000a0a00000aaaa0000a0a00000aaaa0000a0a00000aaaa0000a0a00000aaaa0000a0a00000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_15309
namespace PEqualNP.Outside.L_meta_15309
open PEqualNP.Outside.L_meta_15309.Model
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
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0x1fffffe00ff807fffffffe03f803fffffc71ff
  | 3 => 0x1ffffffff00007fffffffffc0003ffffff81ff
  | 4 => 0xe0f87ffffffff803fe01fffffffc07f007fe38
  | 5 => 0xff007ffffffffffc0001fffffffff80007ffc0
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x2100964924830646224362c59b458b6c9b6db
  | 1 => 0xa42212bd849552a9a548db02aa92ad5b54716d
  | 3 => 0xc84424c92ec6a4d2c9916d560523366da781b6
  | 4 => 0x9e86c711c8e4c6e3111d8f9b363a0781c6da38
  | 5 => 0x10f7781e0f070703e1e1f1e3c7c3c40e076dc0
  | _ => 0
def s2Atlas : Atlas := ⟨3,rawDecor 59 s2Pos s2Neg, 0xaaaa880088008800aaaa880088008800aaaa880088008800aaaa880088008800aaaa880088008800aaaa880088008800aaaa880088008800aaaa880088008800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_15309
namespace PEqualNP.Outside.L_meta_15309
open PEqualNP.Outside.L_meta_15309.Model
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
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0x3fff007f807fffc03fff80fe01fff80ff9c7c7
  | 2 => 0xffffff80007fffffffffff0001fffffffe07ff
  | 4 => 0xc3ffffffff807fffc03ffffffe03fff00ff8f8
  | 5 => 0x3ffffffffff8000003ffffffffc00000fff00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x4b249083048c4484868b166a2c5a9692db5b
  | 1 => 0x5095ec25552d34a3a91bc0aaa956a98ba9c5c5
  | 2 => 0x212649746a4a5929322d5581419b372d4e06ae
  | 4 => 0x36388e464c6c623223b1e6cd8d03c5c18d68f0
  | 5 => 0xbbc0f07870707c3c3c3e78f1f1e2060e0fb700
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xaaaa8080a0a08080aaaa8080a0a08080aaaa8080a0a08080aaaa8080a0a08080aaaa8080a0a08080aaaa8080a0a08080aaaa8080a0a08080aaaa8080a0a08080, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_15309
namespace PEqualNP.Outside.L_meta_15309
open PEqualNP.Outside.L_meta_15309.Model
def s4K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x10a01800280ef18dc31dc43b087d887810
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x8800310c421d031043808410
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (i*4) 4
  | 3 => packedAt s4K3 (i*15) 15
  | 2 => packedAt s4K2 (i*26) 26
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (5+((h/1+packedAt s4K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s4K3 (98+((h/2+packedAt s4K3 (90+(h % 2)*4) 4) % 9)*4) 4
  | 2 => packedAt s4K2 (81+((h/1+packedAt s4K2 (78+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffbf0fffc3fe3f
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffdff0fffc3fc7
  | 3 => 0xefff0fffc3f8
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffff41e222e2661b
  | 1 => 0xffffffffffffffffffffffffff0224454488ed
  | 2 => 0x244e89aa3346
  | 3 => 0x1888ee3323b0
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 15 s4Pos s4Neg, 0xc880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880c880, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_15309
namespace PEqualNP.Outside.L_meta_15309
open PEqualNP.Outside.L_meta_15309.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x12012953450b0c3c84006403d12b580411c307cda9229d20d2e8c71900417805400580101c00a004ce925a9970506114000024410d00b6800000001810c0ff43fe43fd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xfc202e3409c2487009e8346234864964e2fa040e00001d8d4002601836613e208ca4527800b800001b8fe7500060008301960561529000b437001dcba2f000143a8526910860d391f83813208b10042181bcd600001ec002400024000015000f0792b98c9004190806216360ec8e363203ca200200440002430001846380e0fa670580000002517868171e8786654301d0b62d3888c3e28280a4443e1a9b4000e2c8210800299544c251e0e8720a10850ac7324998000c010018040100012e1d00060007000104010916080401000f110103010000040305000f0102000a0804012613bb28e877551d0e7ca5214f546429f284853e5210b5ca4214f544429f280853e54cca7aa9994fd51329e2a26577514cae8a2995ed4132bc282655e53d06baa7a0e794f41cea9e833e52d067ca1a0cf55241afa9a835c53506dea4a0db14941bda828378505073ea6a0e714d41d7a92833c5250758a4a0cb14941dba8a83bb5050678a0a0ee141419c282833e541076a8398cf952319eaa4639e548c73aa918e790a31ce214635e518c73e8318e7506319f2a0633d540c76a8218e795031ceaa0639e420c7388418d794431eb288639f410c7ac8218e750431eaa086395410c67ea990cf15321af29e435d53c87a86390cf952219eaa443ac428867ea890cf15121afa9a435c53486f6a090de141219f2a0433d54087588410f50c4219f294813d519033c6320670c6409f284813e521027aa220678c440ce188813e5010374a0204f953309eaa6613f544c278a8985bd4930b62926177514c2e8a2984f953209eaa6413e548827aa9104fd51209e2a2415f53482b8a6905dd4520ba28a413f5408278a8105794c20aea9841e9200827ca9884f55310dc206213f5484278a9085794e10aea9c21d4318427ea8884f15110afa9a215c53442dea4885b149109f2a0213d54043a862086e10010
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x65000700ac813549c00e00996803c1058038c47a14a80f89006400a2a34d180a446015c00d86520002444c0916588ce9710080285e1401030020440550406800cb8e1815110b0f5314941c314c525069663d4541ca14b505071b5314141c614c505072b5214141ca14850506a46250731ac18141cc68c6250631a6181418c6a46250431ac181410c6956110831a5592510c61d65d0431a5592410c61f6550431a3189410c6986050431b1189410c6d06050431a5d95410c7176550431e1d89410c6946250431e1189410c6846250431e4d81410c6946050431e4181410c69060504318e98354c8717540c7218b5944208715540c421e1108310862c6254440c5544311023561150209518553082c86348020b8185200822e62d5210c5d503184315540c4108e59440043903110010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x114000000330507200201241c16110831d00c5b028218e8362181410c740310c0a0863449c3540c721a0aea2106210d04725443110283396a818c21845943110010
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 136
  | 3 => 50
  | 2 => 9
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | 3 => packedAt s5K3 (i*38) 38
  | 2 => packedAt s5K2 (i*49) 49
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (864+((h/16+packedAt s5K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s5K4 (4032+((h/45+packedAt s5K4 (3672+(h % 45)*8) 8) % 164)*9) 9
  | 3 => packedAt s5K3 (1996+((h/16+packedAt s5K3 (1900+(h % 16)*6) 6) % 61)*7) 7
  | 2 => packedAt s5K2 (453+((h/3+packedAt s5K2 (441+(h % 3)*4) 4) % 14)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x7ffffffffe03ffffc0ffffffff01fff1ffe3f
  | 1 => 0xf80fffe03ffffffffff03ffc03ffffffe3e3ff
  | 2 => 0xfff01fffffffc07fffffc0ffffffe03ffc7fc7
  | 3 => 0xffffe0003fffff80ffffff0003ffffc0ff83f8
  | 4 => 0xffffffffc0000000fffffffffc000000fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x411125228a2389122c02cb2d54b10e590dae1b
  | 1 => 0xf0448499644922458b01554c15634b262e0ed
  | 2 => 0x522d1185248907489555409a9a6b422cb45746
  | 3 => 0x64499d163912240ee669a603138d9b08df03b0
  | 4 => 0x878e1e183e1c3870fb8e38e3e00e1c30fbf800
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xe8a0c880e8a0c880e8a0c880e8a0c880e8a0c880e8a0c880e8a0c880e8a0c880e8a0c880e8a0c880e8a0c880e8a0c880e8a0c880e8a0c880e8a0c880e8a0c880, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_15309
namespace PEqualNP.Outside.L_meta_15309
open PEqualNP.Outside.L_meta_15309.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x9ca50c1c98143104f400dc3c38c010480078940c046500580114685484a80000002800b0ec00b4bcf02cd88834208cd4004000446000c508a000e0007c81107000e808ac4c905c0024d0c8fc7418e4f86cb850cc480070030612000058004087970000081004829600ffd5003fe54005f95003fd5400ff150037c5400ffd4c03fe5300ff54c03fc53007fd0c01fe43007f50c01fc4300ffd48037f5200ff94803fd52005f54803fc52007fd0801fe42007f50801fc42007fcc801fe32007f4c801fc3200ffd4403fe5100ff54403fc51007fd0401fe41007f50401fc41007fcc401fe3100778c401fd31007f0c401dc31007fc8401fe21007f48401fc2100ffd4003fe50005f94003fd5000ff140037c50007fd0001fe40006f90001fd40007f10001bc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x1a4000f718d20005b8c69002f7f5248001bea924000bfd8520007eec290002f761480017e30a4000fd18520005e8c290003de3148001ee18a4000df9412005ef8a090003be4048001de2024000fec8120007dc4090022ff65080037f3284008df9942000cfcca10022fd6508001beb2840009f5942000df8ca10002ff640800d7f3204000bf59020035f8c8100037e5408011be2a04000bfd8c2002dfcc610003de63080016f3184000bf58c20007bac610002dd630800b7e318400abf98820046fea4100037d5208001f79904000fb0c820005fcc210002fd6108001ef1884000f70c420007dc4210003ec21080137f3004000df94020046f8a010003be4008001de2004000fbc8020007f44010003ed2008001fc9004000fa48020025fecb88006fe65c4009bf32e20019f99710025facb880037d65c40013eb2e2001bf19710005fec98801afe64c4001df3262000af99310005fac988003bd64c40015eb262006bf19310006fca9880137c54c40017fb1e2005bf98f10005fac788016fc63c40017fb162000bf98b10005fac588002fc62c4009bfa962000df54b10007bc6388003dc31c4001bf2862004df14310007f68188003be40c4001de2062000fe1031000770818800eff65840037f32c2003bf5961000df8cb08002ff648400d7f3242000bf59210035f8c9080037e5484007be2a42000bfd8e1002dfcc708003de63840016f31c2000bf58e10007bac708002dd638400b7e31c2000bfd8a10005fcc508002fd62840017e3142003dfd4a10006faa50801efd6184001fb98c2000f78c610007b86308003f43184001ea18c2000fdc8610007e8430800afe6084001bf2842003df142100077c8108003bc4084001fb8842000fec421003dfeca880037f65440013fb2a2001bf9951003dfaca88006fc654400fbe32a20019f19510005fec888003bf64440015fb222006bf99110005fac88801afc6444001de3222000af19110006fca88801f7c54440017fb1a2000f7d8d10005bec688016fe63440017eb1a2005bf18d10007b8c688002dc63440017fb122000fbd8910005dec488002fe62440017eb122000bf18910007d8c488002ec624400fbfa922000df54910007bc6288003dc3144001bf2822007df141100077c8088003bc4044001fd8822000fd84110015feca08006fe65040057eb282001bf19410005fec80801afe64040017eb202006bf19010006fca80800b7c54040017fb182005bf98c10005fac608016fc63040017fb102000bf98810005fac408002fc6204005bfa902000df54810025fcc208003f73104001ef1882000f70c410007e86208003d43104001fb9082000fd0841001dfcc0080037e5004005be2802000fed00100077c8008003bc4004001fc2002000ee10010007ee2008003fa1004001fa8802000fe44010
  | 1 => 0x77e65cc0033f32e600fbf5973002efacb980027d65cc00b7e32e6005bfd9330035fcc998017be64cc0015f3266000bf5933002f7ac998002bd64cc00b7e3266000df9533007ef8a998002fe62cc0017eb16600fdfd4b30006faa598017df32cc001ee9966000bf98730005fac398003de31cc00bee18e6000df9433007ef8a198003be40cc001de206600dbfd963000dfccb18036fd658c0037e32c6000bfd9230035fcc918002fd648c00d7e3246000df9523006ef8a91803afd638c0017f3146000bf58a3006efea5180037d528c001ef1946000f70ca30005fcc318002fd618c001ef18c6000f70c63002dfcc1180037e508c01bbe2846000ef90230007788118003df308c00bfd984600ebfd9530006feca980027f654c0037f32a600ebf5953000df8ca9803b7c654c0033e32a6000bfd91300077ec898002bf644c00d7f3226000bf59130035f8c898003bc644c0015e3226000df95130076f8a898002ff624c001f7b126000bbd8930005f8c498003ec624c00176312600edfd4930006faa498003df324c001ee9926000bfd8530007eec298002f7614c0017e30a6000fd18530005e8c298003de314c001ee18a6000df94130076f8a098003be404c001de2026005fecc130007bc6098016ff650c0037f328600cbf5943002df8ca18016ff640c00d7f3206000bf5903002df8c8180037e540c019be2a06005bf98c30005fcc418002fd620c019bfa906000df54830007bc6418017dc320c0017f3086000bf58430007bc6218017dc310c01b7f3006000df94030066f8a018003be400c001de2006005f7cc03002ff46018003dd300c00bfc980600abfd972000dfccb9002b7e65c80033f32e400abf59720006facb900027d65c80037e32e4000bfd9320035fcc990003be64c80015f3264000bf593200077ac990002bd64c800d7e3264000df95320056f8a990002ff63c800b7f31e4000bf58f2002df8c79002b7f52c8001bea964000bf98720005fac390003de31c8001ee18e4000df94320056f8a190003be40c8001de2064009bfd9620006fecb100027f65880037f32c4009bf5962000df8cb100277c65880033e32c4000bfd9220035fcc910002fd648800d7e3244000df9522004ef8a910002ff638800b7f31c4000bf58e2002df8c71002efd6288013bfa944000df54a20007de6510003ec32880017f30c4000bf58620007bc6310003dc3188001f710c4000fb08620045fcc1100037e5088013be2844000ef90220007788110003ef2088001fd904400bbfd9520006feca900027f65480037f32a400bbf5952000df8ca9002f7c65480033e32a4000bfd91200077ec890002bf644800d7f3224000bf59120035f8c890003bc64480015e3224000df9512005ef8a890002ff6348001efb1a4000b7d8d2002dfcc690002fd634800b7e3
  | 2 => 0x4000cfccb20046fd6590001beb2c80009f5964000df8cb2004afd6490023dfaa48006df9524008f7ca9200033e5490023deaa48006df1524008f78a9200473c549000b7f31c8000bf58e400077e8720003be4390001dea1c8000ef10e40005fcc520002fd6290023bfa948000df54a400077e8520003be4290001dea148000ef10a40005fcc320002fd6190001dfa0c8000ef906400077a8320003bc4190001ef18c8000f70c640035fcc1200037e5090023be2848000efd0240037f68120047bf6590023df32c8011cf9964008f7acb200033d6590023de32c8000efd8e400077cc720003bd6390001de31c8011efd4e4008f7ca720047bd5390023de29c8000efd8a400077cc520003bd6290001de3148011efd4a4008e7ea520047be5290023dea948000cf54a4008f78a520003bf3290001df1948000ef4ca40007786520003bf6190001df30c8000ef5864000778c320047bf5190023df28c8011ef5464008f78a320003bf3190001df18c8000e78c6400077a6320003bc3190001ce18c8000efc86400077c4320003bd2190001de10c8010af9824008f7ea120047be50900019f2848011ef5424008f78a1200473c50900257fb2a8000dfd9540004fecaa0006fe65500257eb2a8001bf19540096f8caa00067c655000dbf2a28006df15140005fec6a0016fc63500017fb128000bf18940096fea4a00037d52500017fb0a8000bf18540007bc62a0003dc3150001bf2828012df14140037f680a0003be405000d7fb288006dfd9440034feca20006fe65100217eb288006bf19440036f8ca2001a7c651000d7f3208010efd5040036fca82001bbe541000d9f2a08010ef55040036f8a82001bbc541000d9e2a08005bf98c40005fac62001bbf4310001df2188000ef50c40037788620002fe62100017eb108010dfd4840006faa42001bbf4210001df2108000ef50840037788420002fe61100017eb088006efd04400077c8220003bd411000dde2088000f78c440007b86220046fe6010001bf2808010df140400377e802001bfa4010001dea008006fe500400377eca2001b3f6510021df3288010ef5944003778ca2001b3c651000ddfb188000ef98c400077ac62001bbc6310021dfa988010ef94c400877aa620043bc531000ddfb108000ef988400077ac42001bbc6210021dfa908010cfd48400877ca420043bd52100019ea908010ef148400077e6420003be3210001de9908000ef0c8400377ec220003be6110001deb088006ef184400877ea220043be5110021dea888010ef144400077e6220003be3110001cf1888000ef4c4400077862200039c3110001df9088000ef884400077a4220003bc2110001df3008011af9804000774c020043bf5010021df2808000cf940400877aa020043bc50100219e2808005bfd973000dfccb9801
  | 3 => 0xf2886218f7544310c7b8a218803df410c401ef2086200f590431007ba8218803d5410c401ee2086205f7d8031007bcc018803dd600c40bee3006218f7d40310c7bca018863dd500c431ee2806218d7140310b5fecb90806fe65c842dbf32e42019f997210b5facb908037d65c84013eb2e4201bf19721005fec99081afe64c84017eb264206bf19321006fca99085b7c54c84017fb1e4205bf98f21007bcc790802de63c84017eb1e4200f758f21005bac790816fc63c842dbfa964200df54b21007ee6390803de31c8401ee18e4200fd0c721007a86390802fe60c84017eb064216df143210adfecb10806fe658842b7eb2c4201bf19621005fec91081afe64884017eb244206bf19221006fca9108577c54884017fb1c4205bf98e21005fac710816fc638842f7eb144215dfd4a210afdca5108037d528842bf6a944200db54a21007de8510803ec42884297f30c4200f78c621007b86310803ef2188401fb90c4200bf98221005fac1108577c508842f7fb2a4201bf995210bdfaca90806fc65484017fb224206bf99121005fac89081afc6448401bf2a24217df15121005fec690803df63484016fb1a4205bf98d21005fac690816fc6348401ee31a4200b718d210befea4908037d5248401ef18a4200f70c521007ee4290803ee21484017fb024200bf181210bef8a090852ff65084037f3284214df9942100cfcca10852fd6508401beb2842009f5942100df8ca10802ff640840d7f3204200ef990210057cc810802fd6408401deb204200af59021035f8c8108037e5408429be2a04200bfd8c2102dfcc610802fd630840b7e3184216bf988210a6fea410853ee5208401bea904214fb54821006daa410803ef4208401f62104215bf98421007ee6210803de3108401ee1884200fd0c421007a86210803ef2108401fb1084200fb48421007ea4210802fe60084017eb004214df14021006fec9280037e649400d3f324a000df59250006f8c9280037f6394001bf31ca000df58e50006f8c7280037f4394001bf21ca000df50e50006f887280037f6294001bf314a000df58a50004fac5280037c6294001bfa14a000df90a50006fa85280037c4294001bf994a000df8ca50006fa65280037c3294001bfb0ca000df98650006fac3280037c6194001bfa0ca000df90650006fa83280037c4194001bf98ca000df8c650006bc63280037d3194001be18ca000d70c650006fe43280037e2194001be90ca000df0865000efcc1280067e6094003bd304a006bfd974000dfccba001b7e65d00033f32e8013bf59740036facba00027d65d000d7e32e8006df95340036f8a9a0016fe63d00017eb1e8000bf98b40005fac5a004f7f52d0001bea968000bf98740005fac3a0003de31d0001ee18e8000df9434009ef8a1a0046ff65900037f32c8011df996
  | 4 => 0x802f8605043dbe2828206bfd944100dfcca20872fd651040d7e3288206bf99041036fca82081b7c541040b7f3188200bf58c41005fcc420802fd6210439bfa908200df548410edfcc22081bbf411040dfb2088200ef50441037ea8220802fe60104017eb00821cdf1404102dfecb98806fe65cc4377eb2e6205bf1973102dfec99881afe64cc4017eb266205bf19331006fca99886f7c54cc4017f3166200bf58b310defea5988037d52cc401fb20e6200fd50731005fcc198802fd60cc437be2866219bfd963100dfccb18866fd658c4037e32c6200bfd9231035fcc918802fd648c40d7e3246200df952310cef8a91886afd638c433efa9c6219f794e310cfbaa718867dc538c401efa1c6200f790e31007ba8718803dc438c4017f3146200bf58a310cefea5188037d528c401ef9946200f78ca31007ba6518803dc328c40b7f30c6200f7cc63102fee6318802fe608c4017eb046219df142310cfbecb18867de658c433eeb2c6219f719631007bec918803de648c401eeb246200f7192310cfbea918867de548c401af2a46219f7552310cfb8a9188675c548c401efb146200f798a31007bac518803dc628c433efa946219d7d4a310cfbca518867dd528c401aea946219f714a31007be8518803de428c401eea146200f710a310c5bcc318867df518c433ef28c6219f7546310cfb8a318803df418c401ef20c6200f750631007b88318803df608c401ef3046200f758231007b8c118867df508c433ef2846219f7542310cfb8a1188675c508c4357fb2a6201bf995310d5faca98806fc654c4017fb226206bf99131005fac89881afc644c401bf2a2621adf15131005fec498802fc624c435bfa926200df5493102fee6298803de314c4017fb026200bf181310d6f8a098816ff650c4037f3286205df9943100cfcca18862fd650c40bbeb2862009f5943102df8ca18816ff640c40d7f3206205ef990310057cc818802fd640c40bdeb206200af5903102df8c8188037e540c431be2a06205bf98c310c7bea618817de530c431eea986205f714c31007be8618817de430c401eea186205f710c31005fcc418802fd620c431bfa906200df5483102fbe6418803de320c401ee9906205f70c8310cdfcc218803f6410c401faa086205f7cc43102fec6218803dd310c40bfa9886200bf98031005fac0188637c500c40befb286218f7994310c6bcca18863dd650c401aeb286205f71943102fbec818803de640c401cf3206200f7590310073ac818817dc640c431efaa06218f795031006bca818863dd540c431ee2a06218d71503102fbec418803de620c401eeb106205f7188310c7bea4188635f520c431ef2906218f754831006baa418863dc520c401efa106200f790831007ba8418803dc420c401ef3086219b798431007acc218863df510c431e
  | 5 => 0x954200cf8caa101b7e545080dbe2a28400bfd8d4202df8c6a109b7f5250801bea928406fbd09420077c84a1002ff61508017e30a8400bfd8142005f8c0a109b7c505080d7fb288401bf99442036fcca210067e65108497eb288406df59442004faca2101afc651080d7f3208424efd5042036fca82101b7c541080dde2a08406cf1504202dfcc621002fd631084b7f3108424dfd4842006faa42101bbf421080df72108400ef50842037da8421002fe61108017eb088400bf98042005fac0210937c501080b7fb2e6401bf9973211dfacb99016fc65cc80b7fb266406bf99332005fac999016fc64cc801bf2a66423df1533211efea5990037d52cc8017f30e6400bf58732005fcc199002fd60cc847be2866421bfd963200dfccb190877e658c8033f32c6421bf59632006facb190027d658c8037e32c6400bfd9232035fcc919002fd648c80d7e3246400df9523210ef8a91908afd638c80b7f3146421dfd4a32006faa519003df328c80bf79946400bf98632005fac319002fe608c8017eb046421df14232115feca99006fe654c8457eb2a6401bf19532005fec89901afe644c8017eb226406bf19132006fca89908b7c544c845bfa926400df5493202fde6499003de324c8017fb0a6400fdd8532005eec299002fc614c801fa30a6400bd18532005fec099002fc604c845be2826405bfd943200dfcca190177e650c8033f3286420bf5943202efaca190027d650c80b7e3286405bfd9032035fcc819002fd640c80b7e3206400df95032106f8a819016fe630c8437f3106420dfd4832006faa419017df320c80bf71906400f74c83202fda6419002fe610c8017eb086400bf98032005fac0190837c500c80d7fb2e8201bf997410fdfacba081afc65d043fdfaa68206df95341036f8a9a081bbc54d040d9e2a68205bf98f41037bcc7a0802de63d04017eb1e8206f758f41005bac7a081bbf43d0401dea1e8200bf98b41005fac5a087f7f52d0401bea968206efd0b410077a85a0802fe60d04017eb06821fdf143410edfecb20806fe659043bbf32c82019f996410edfacb208037d65904013eb2c8201bf196410f5fac92081b7e549040dbe2a48205bf98e41005fac720802fe62904017eb14821ddfd4a41006faa52081afe6190401dfa0c8206fdd0641005fcc120802fd609043bbe284821ebfd9541006fecaa08027f65504037f32a821ebf5954100df8caa087b7c65504033e32a821eefd5141036fca8a081b7c545043dde2a2821ecf15141005fec6a0803df63504016fb1a8205bf18d41007b8c6a0802dc6350401dfa1a8200ef50d41005fec4a0803ef625040177b128200bf18941007d8c4a0802ec625043dbfa928200df549410077e84a0803bd425040dfba0a8200ef90541005fec0a0803fb60504017db028200bf18141007f0c0a0
  | 6 => 0xc00200000600200201800e00000800200001e00000600c00401200400000200200001000800200e00000a00800400001200800000000000e00401400200000000000000800000200000800a00000001601c00000e03e00402800001800200002a00001a00800000400000200200e00201000000000000800600001601200201000c02200000001400800202200000a00000200e00400c00000402800002000000800400200800000400801000000000600000200000000a00400000006df99254034fcc92a01b3e649500dbfb1ca806df98e54036fac72a01b7c639500dbfb14a806df98a54036fac52a0027d629500dbe314a806dfd8654036fcc32a01b7d619500dbe30ca806dfd8254036fcc12a0027e609500dbeb04a806df18254035fecba1806fe65d0c577eb2e8606bf19743036fca9a181b7c54d0c017f3168600bf58b4315efea5a1802fe61d0c0dfb30e8600bd98743005fac3a181bf561d0c017ab0e8600bf98343005fac1a18af7c50d0c0b7fb2c8601bf9964302efccb218067e6590c557eb2c8605df59643004facb21816fc6590c537eb248606df95243036f8a921816fe6390c0bdfa1c8606f7d0e43005fcc521802fd6290c55bfa948600bf98643005fac321802fe6090c017eb04862adf1424314dfecaa18037f6550c013fb2a8601bf9954314dfacaa1806fc6550c53be32a86019f19543036fca8a181b7c5450c0defa1a8605ef90d43005fec4a1802fc6250c53bfa928600bfd8543005f8c2a1802ff6050c017e3028629df1414302dfeca21806fe6510c517eb288605bf19443035fcc82181b7e5410c0dbe2a08605bf98c4302f7e8621817de4310c0bdea188606f750c43005fcc421802fd6210c51bfa908600bf98443005fac221802fe6010c017eb008628df14043006fec8a90033f6454801bf322a400df59152006f8c8a901a7c64548019e322a4008f19152006fec6a90037e6354801beb1aa400df18d52006fe86a90037e4354801bea1aa400df10d5200efec4a90067f6254803b7b12a400dfd8552006fcc2a90037d6154801be30aa400dfd8152006fcc0a90037d6054801be302a4009f18152035fecba101b7f65d080d3fb2e8401bf9974213dfacba101afc65d080dbe32e84069f19742036fca9a101b7c54d080b7f31e8400bf58f4213efea5a10037d52d08017f30e8400bf58742005fcc1a1002fd60d084fbe2868425bfd964200dfccb210977e65908033f32c8425bf59642006facb210027d65908037e32c8426bf5924212f7ea92101b7e549080dbe2a48425ef1524212e78a921016fe63908017eb1c8406bf98a4212efea5210037d5290801dfa148406fbd0a42005fcc321002fd61908017f3048400bf5824212ef8a12109aff6550801bfb2a84009fd954200dfccaa109afd65508037e32a8426df1
  | 7 => 0xd08ca4000000f6952166859cad8000aa89a4000000cac00000038c4f095cc554b07fc000a2c230b453c1594114d700002dd6852995b44f8000404000b9c51c000000000000fc4f28000b982b4c8c000704238a080a810556800149000060c000739375284144000001760000000000cf000130cda454d700001505360f44c2c2f87110b168c1400005d52b4000001180000a7040941d32894800158ca74fcd5a05c8514da127890c000f84000534b506300015e47890381b0e083b90e87e0d40000aa4124c4975c280eb4d44000aac0014dcbc00000000016e4bf40000005a8000024bd00000014a96452e12ec3340004996a4000b1081d78c3b05f54815f860532458906400000008c001621655788000000b2400074d4f94f08dd4c0e9d6b81f4b48dc946c000000050b04ce800081830d72cc18e5c0d11940000000000000009c126cad0e740008fc35cbf8b1d4f4bd4000004000ba4f94e947b4020b38770cf496c0000012c400162c1ac000000000a14000794e480000000000000004f40005b95345440000008480000004800000004c00bd2191600000001e03b4f74c3800151002c6246980009a01100005296bd388d34000000d8ca9c00000000000095800000a00400000000000001000400001000a00001c03a00400800200c00000200800001000001a00200200200201000400800600600200600000601000600801200800c00200000400000600400000001a00000c01600400000600601800600200800400400000400000000000400400400a00000e00200000200200200000600800200200000801200000000600200400200200001400600600400001e00200000001200600000a01000000000000000200000400400000000000000e00001000e00600200001a00a00a00000e00000200000000000400000000600400000002000000400000200800800000000000201200200c00c00200400202600200200000000000000601401200201a00800000000200600200000200000200400000000000000400c01800c01c00200400a01000000a00400200e00000400e00000000000000200200000200000000600000000000a00000000e00400200800000200000600000200200000000000200001801a05e00002200200200600200c00000200200001800a00600e01e02000403c00200800600000600200001000001e00001000201600201200000000c01600000800200000000200001400000200600000a00000000a00e00001a00000800200200000000200000800000200200800c00a00200001800001400a00200000000a00a00400400200c00c01800000000400000000401200000600400601000600400400200000400a004006000046002000000000012000014004004000012000004002002008000
  | 8 => 0x4000000b5400118c0007ac000b2915ceb8b7c55c0008a8578000000de80000000000009314e41214c8f5c000ce0af4a10000d2cd7c00000000000000052400000042cb9400133c88d574068e805c068c00000173c0016280000000000008710711b8000ed40000000000000000008640010900015b00009ac0006780003787c83c8e58000000b400012340015b80013e4000000000ff40016d51c49544a96345e80000f44000007500006cc000001779098000000000000a194bc000000bfc0000009b8cd09f0000000554000c4549447d5980000006608a4000000000c74c64184380d908d12d86acf0d5e9570000929718e3c2ec095138d690d411d660d544611312944c9210a90e782b07847f01b539c3dd488c24ae80002a10881ccdc0000000000000fb9398258cb4dfc4e8644a514596cc0000d472c328044fe40011086007a47f885d528ef4a887b06b800176c0000016f10940014a4ddc000e3800147024d4a007d51882c001664d890c80011180000009b4e0400000000000101c000b180000000000000000008e8e90804000d1894125d5a81c0744000c580000000cc22ccf84bc0002d00584384b8000a8c05c00148d09c0014d01500000000000000000f091cbd86742993ec000000960000b5800000045d1f8f011d81ecebd258000000768d117495f400000000000108d0240008348b0bcc000000304b3c000fe05ec0013440000e400000143480c0000005100008a00000000009680000000000000004400000000003acb00c00d3112494c000a5c03cdc4000000f4000079073c2f40000000000000000003fcfd400123000000165c0013dc0000000b4000e4c000000000000d0c8800b8af0000000001074618de4d9c4b0f905dc000ac0620488a1c4311780000009440000000000000000000004acbe00000005d0001358000c04ed80001616c11152dd0ec0000015dd1a90580000011bc00000000161d2053d80000008245980000011e935d75577ca48fa06f48840d80000007c41e49e0000001085638000000e406e520c18c1480004cd6b17706883417283441dc28c608f7c59462c0000000a00ac2957593e0ca87307743a89246108f94856ec3080901950400006580c8b346b06344e4000000204dd84dc0014e06c03a0000208049060000000000df4128fb0c311980000016800013a121400000000000000000000000145c00000000077c000444bf0000760000000e845496d09c45b124d030df822000010864ce4400000131c5005083c000107d320fdccc4000c5c000e240013513543390cc0000008ad5600000005580000000000002240007a800111c000a0000154c00093970800000056c0008380000000000001f0234000e50000000000d48b141f83a4154fad74c9fc0000000017349bd420abc00000157c2f00000
  | 9 => 0x201544000690398f380003651c8ed089c0000000002c48280000014d8000000810965584001000ab80015d5614e1d0fd0511e000000000000000043d49c65c00106c000f08dd48c42113a4001558c500002a9740a98bbc0000000016dc4fd65940052cf1000160c00015d2fc0000000000006a05b4bad2bc0e80001fc0000012754780009c80080017391480000000000009d1764000001390000bc8000000520a6560569066cf489e92384d897cac8010b090c08796b4e14e64000000000c11440ee0001154260274c088513780000000000002915400010ad2a43505701c45742bc038c98d790bc6690783943ec060000000724000934000d05268000000000000da80016d929c000000000844000000000db0f9d410000000314000000f88000000aec00150ccc8edcec87d8000000000cbc0000006f86bc9980011dc5e0000000000f040001340006290286ec000000000fb40013940000014ac6d827c0014cc000e2d1f4000000a6d3ac2700000015f037c00136c000000000000778330becc3cad45680000005c54b960800165116853c31d2b8000000100000000c4000000000163c0000009ec001228a85688a3164015800000000000000000000000034c000f342cc5a564800000000044c0015c49207e4b7098c0007ed7154253d40000000006d400075800000000117c000b30000034001694df0028040b6910d1847b924058c5bca38ff02b81a4d60000000001314454d84000ef80000007c142d774b803000011f00001882e0e8cd293e92d07492f0c14000000db800000000000159c504b60001254908000fe94693d15493c4268001744000000001430000000c84000d65340d5c000bc40000011acf6d591250bb80000e0640000000000f4d71d1b071400000000140c000000ab02540000004482fc0013a80000008d40000140009f846c000b84000ee800000001cb88000000000c700013b4000fc928813119d2f83542486c53b00004180010f014c0004845806e856439d200000000000000000000a80450dad3656980000006d01800005f000000084c2643755e000000000104c00004c00110463cc814640c51100000003e80fd5140000015543f87a0734000e0c0781c8000000000000ae4d200006540013f8a4d44c250000000000084afcca03c4000a954515d0000ecc000434dbc854001768eec00000122400061c0000000012ad0f94ed5646a48b4000000244560b4c0001a80005cc000d3cfa40008e4000000eb00000013fd4750a8efc00071cc90e188bc0003cd6fcc28e6126006441c368000dd00004b40015395080005404c41e800099c0015ac4240001d00009d553c1d83e0680970f6089115086c0886840005ac5fd55c000a40214000018b209189dd710bb0814000178990310e983840dc1a03bc8b800000126
  | 10 => 0x9c874e54000590c6c3884a4e68ec000d208348000000000001144000000000000000ee53f035800000000113d5bc4117200000011580001bcf2c00128d2e4001600664000000e88ea0fa83900007e820cfbc0000016acbe51ec001170a3cf2169d3487bca7d448190468a20a448d88c80984580000007dc000000e7c2c0fc07090d8ea823d0d16e116c09cf1956c8f13195c15ec67c7800000009d812d2700000000f800000007083050c240000000fecc1c64800147c9853705f92e80000005380002840016e93cd6a0e6cf64228370584b9089449c69d5fd70cb6c8993102e89817914182d91b4f241b8d80000000000d3800000076c000000de00000009b138c000000000000000000ec400164c2d48003f51290a400000143c0016f55c930075c0011a4138cb0000000000000000000718a04764000000000360b785500000000000000006dc0016750b52c8000001381438000000000b0d0b8000000000001244cec00026ccd400000123d188000000000f580000006f10e05e4000000c350c41187d0f5102d2c00000005a0000b648893080000000007549cc4903d532c00140942966c0006a8ce500c00145400036c464a7886144485821cf7898842122d0e4001730cfc000000b8c670001784dcd6a8168fd151ca54000000974d1caa083cf1c4e105c7f429c6fc000000000b5c218000ae00002890147980000000000012b08c0000000000000cb80000000000000000010a040d19167c000f540000000008e0b2c000c20000994f30dec2c80300000000010440000000012a8001498c940a448c000c4d62400087cd14f980003f000031800000000000000000100400000000000000000103d3f4ba8c9d2208200013c8000000c880011a008000129000000137c0000011d492c13c0000008f40010540000012cc000c690114fd5249156f8be913534c1754146c8b74054e704ec0004d4ef1334000000000000000000d00000e294040000009f56700003d8320000d6d0dca255a478c7d50187cc0003d04295cd384000e20000a602a40000004791e4ffcd50ff8adcd4c000d240ed248c0d1cc79c0002ac00019903400000000000121c001330cc00000014c4840000979618f8c4a0000f711c00000000000b1141008001020bdd2a0acc70d068000f811fc614d94000bb54b40015780000016c8000ead16510112c5d8f1400152d724000ccc4d0e11550000000ba0ab40000000000000000c006c001588000a348cd049120000000cdc638000000e000000000012f4000000000a580745300000000000000000000004949101713b82e4001530000000f3c1640000012d417c000a286b400000041400033c93c000000000001280a69630740000000000000fd80014e8700000001500ea40000008ec000728001460000d59305174000001750
  | 11 => 0xc7d3693bc10cd7457c900808471080474518e357046e09e4000650000e31610324a0d58069578027967825caf88691d114cc78904c610f56c495127c16c3e472032d5d81d5338db4000ac49a8cd8d980000014d41
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe5418d100065c5418d100065f5218d100ccde7118d1002cdc7118d100065c5018d1000c7c75d89100066f52d89100066f65d89100066c65d8910006af64d8910006ac64d8910006cf63d8910006cc63d89100066f75d89100066c75d89100066e54d89100066c54d89100066c50d891000c7e75989100047d7598910034be7498910004bd749891002cde7398910004dd7398910004ee72989100047f755891000c7c7558910004bf7458910034bc7458910004df735891002cdc7358910004f7715891000c7e75189100047d75189100066f5218910004ee76189100066f65189100066c6518910006af6418910006ac6418910006cf6318910006cc63189100066e75189100066d75189100066e54189100066c54189100066c50189100047e76549100047c76549100053c74549100063f64549100063c64549100065f63549100065c63549100066f62549100066c6254910004de768c5100065f658c5100ce5c658c5100069f648c5100069c648c510006cf628c510006cc628c510004de760c5100065f650c5100c65c650c5100069f640c5100069c640c510006cf620c510006cc620c5100247e76941100063f64941100063c64941100065f63941100065c63941100066f62941100066c6294110004be76901100063f659011008e3c65901100069f63901100069c6390110006af6290110006ac6290110004be76101100063f65101100863c65101100069f63101100069c6310110006af6210110006ac6210110006b864c4110006d46384110006e4628411000c7e75d90100047d75d90100047f755901000c7c75590100063c545901000c7e75988100047d7598810004df735881002cdc735881000c7e75188100047d7518810034be7418810004bd741881002cde7318810004dd73188100053c7454810005787054810195d6718c410004f5760c410006d6760c410006d5760c41018756750c41000755750c41000796740c41000795740c410006d7640c410006d5640c41000756540c41018754540c410006d6620c410006d4620c41018757520c41000755520c410007d2700c410007d1700c41018ed6600c41018754500c410005d673c8410004f57608410007655208410007543194010007d031d001000794319001017dba70900100079431100100073a501001016f385010010004f976100101773a5410010177385410010007d03110010006ba7610010006b976100101773b751001017738751001016f3b5210010007395210010007b27110010007b17110010166ba6110010007b331100100079a3110010007983110010007b03110010007903110010007b32110010007b02110010007b040c401002cf97684010007d03184010004f77644010005d47344010005e47244010007725044010004fb7644010005b87444010
  | 1 => 0x8b10004dd73d8b1000c7e7598b100047d7598b1002cde7398b10004dd7398b1000c7e7558b1000c7e7518b100047d7518b10034be7418b10004bd7418b100047f7654b100047d7654b100053c7454b100063e6454b100063d6454b10005787054b100ce5e658c7100065d658c7100069e648c7100069d648c7100c65e650c7100065d650c7100069e640c7100069d640c71003c7d76943100063e64943100063d649431008e3e65903100063d65903100863e65103100063d65103100073a5010310167385010310006b9641031019f3a541031019f385410310005b97610310006b9761031019f3b751031019f3875103101673a65103100073965103101673b52103100073952103100079a311031000798311031000c7e75d92100047d75d92100063c54d921002cde73d9210004dd73d9210004ee72d9210004ed72d92100047f755921000c7c7559210004dd7698e1002e5e7598e1002e5d7598e1002e9e7498e1002e9d7498e100065e5498e100065c5498e100065f5298e100065c5098e1002cdf7658e100065e5458e100065c5458e100065f5258e10006d77158e100065c5058e1002cde73d8a10004dd73d8a1000c7e7598a100047d7598a10034be7498a10004bd7498a1000c7e7518a100047d7518a1002cde7318a10004dd7318a100053c7454a100065e6354a100065d6354a100066e6254a100066d6254a10006d5630c610005d5760c610006d5760c61018f56750c61000755750c61000796740c61000795740c610006d7640c610006d5640c61000756540c61018f54540c610006d6620c610006d4620c61018f57520c61000755520c61018f54500c610005d673c8610006d663c8610006d663086100076552086100065e63942100065d63942100075431942100069e63902100069d63902100079431902100069e63102100069d631021000794311021000c7e76d95100347e74d95100047d72d951000c7e70d951000c7c70d951000c7e75d91100047d75d91100063c54d9110034be76d91100063f65d91100063c65d91100063e75d91100063d75d91100063f52d91100063c50d91100047f755911000c7c7559110004df735911002cdc7359110004ef7259110004ec7259110004fb7059110004be76191100063f65191100063c65191100363f75191100363c75191100063f521911008cbe7019110034bc70191100063c50191100047e76951100347c76951100063f64951100363c649511002cde76d8d100065f65d8d100065c65d8d100069f64d8d100069c64d8d100065e54d8d100065c54d8d100065f52d8d100065c50d8d100047f7558d1000c7c7558d10004bf7458d10034bc7458d10004ef7258d10004ec7258d10004f77158d10004de7618d100065f6518d100065c6518d100069f6418d100069c6418d100065
  | 2 => 0x69f640c5200069c640c520006d7610c520006d4610c5200547e76941200063f64941200063c64941200065f63941200065c6394120006776194120006746194120004be76901200063f659012008e3c65901200069f63901200069c6390120006b76190120006b46190120004be76101200063f65101200863c65101200069f63101200069c6310120006b76110120006b46110120006cc6388120006e4618812000c7f76594200053c74594200063f74594200347c74594200063c74594200343c745942000c7f725942000c7d72594200447c705942000c7e75d90200047d75d90200063c54d902002cde73d9020004dd73d90200047f755902000c7c75590200347f76950200047d769502000c7e75d8c200047d75d8c20004dd7698c200065e6598c200065d6598c200065e5498c200065c5498c200065f5298c20004de7198c200065c5098c20004f77158c20004f47158c2002cdf7658c200065e6558c200065d6558c20005d47158c200065e5458c200065c5458c20006cc7258c200065f5258c20006d77158c20004dc7158c20006d47158c20004d47158c200065c5058c200547f76548200053c74548200065e63548200065d6354820006cd63cc820004ed760c820005e9700c820004df735842002cdc7358420004df768c420004dd768c4200ce5e658c4200065d658c42002cdf760c420004dd760c4200c65e650c4200065d650c4200066d65884200066d6508420007c43108420005e9700842004c7f769402000c7d76940200065e63940200065d63940200056d729402008e3e65900200063d65900200069e63900200069d63900200863e65100200063d65100200069e63100200069d63100201ade97288020004ef7648020005cc7348020005e471480200076a50480201a7685048020007aa4048020007a84048020004fb76480201a76b5248020007695248020005eb7648020006eb76480200076b75480201a76875480201a76a6548020007696548020007ab7448020007a874480200076a54480201a7685448020007cb7348020007c87348020007ca6348020007c96348020007e37148020007e07148020007ca3148020007c8314802000c7f76597100347c74597100047f725971000c7e75d93100047d75d9310004bd76993100063e65993100063d65993100363f75993100363c75993100063f52993100063c50993100047f755931000c7c75593100063c5459310034bf76593100063e65593100063d65593100063f75593100063c75593100063f5259310006bb70593100063c50593100347f76953100047d76953100363e64953100063d649531000c7e75d8f100047d75d8f10034be74d8f10004bd74d8f10004ee72d8f10004ed72d8f1000c7e75d8b100047d75d8b10034be74d8b10004bd74d8b1002cde73d
  | 3 => 0x571d8f200447f7654b200053c7454b200063e6454b200063d6454b20004df735872002cdc73587200ce5e658c7200065d658c7200069e648c7200069d648c7200c65e650c7200065d650c7200069e640c7200069d640c720006d6610c720006d5610c72005c7d76943200063e64943200063d649432008e3e65903200063d65903200863e65103200063d65103200053e74d96200347e74d96200063e74d96200343e74d96200063d74d96200066d72d96200067a70d962000c7e75d92200047d75d92200047f755922000c7c75592200063c54592200047e76952200347c7695220004f671d8e20004f571d8e200047f7558e2000c7c7558e200053c7454a20005787054a2000c7e75986200047d7598620034be7498620004bd74986200047f755862000c7c7558620004df735862002cdc73586200065f658c6200ce5c658c6200065f650c6200c65c650c620006d6610c620006d5610c6200066f65886200066f6508620007c4310862000c7e76942200056d72942200063f659022008e3c65902200063f65102200863c651022000c7e76d95200347e74d952005c7d72d952000c7e75d91200047d75d91200063c54d9120034be76d91200063f65d91200063c65d91200063e75d91200063d75d91200063f52d91200063c50d91200047f755912000c7c7559120004df735912002cdc7359120004f77159120004f47159120004be76191200063f65191200063c65191200363f75191200363c75191200063f52191200063c50191200047e76951200347c76951200063f64951200363c649512002cde76d8d200065f65d8d200065c65d8d200069f64d8d200069c64d8d200065e54d8d200065c54d8d200065f52d8d20004de71d8d200065c50d8d200047f7558d2000c7c7558d20004bf7458d20034bc7458d20004ef7258d20004f77158d20004f47158d20004de7618d200065f6518d200065c6518d200069f6418d200069c6418d200065e5418d200065c5418d200065f5218d20004de7118d200065c5018d2000c7c76549200053c74549200063f64549200063c64549200065f63549200065c635492000578705492002cde73d8520004dd73d85200067765d85200067465d8520006b764d8520006b464d8520006d763d8520006d463d85200067654d85200067454d8520006d673d8520006d573d85200067752d85200067552d85200067450d8520006776518520006746518520006b76418520006b46418520006d76318520006d46318520006765418520006745418520006d77318520006d47318520006775218520006755218520006745018520004de768c520004dc768c5200065f658c5200ce5c658c5200069f648c5200069c648c520006d7618c520006d4618c520004de760c52002cdc760c5200065f650c5200c65c650c520
  | 4 => 0x91300063c54d9130034be76d91300063f65d91300063c65d91300063e75d91300063d75d91300063f52d91300063c50d91300047f755913000c7c7559130004ef7259130004ec7259130004f77159130004f47159130004be76191300063f65191300063c65191300363f75191300363c75191300063f52191300063c50191300047e76951300347c76951300063f64951300363c649513000c7c75d89300066f52d89300066f65d89300066c65d8930006af64d8930006ac64d89300066f75d89300066c75d89300066e54d89300066c54d89300066c50d893000c7e75189300047d75189300066f52189300066f65189300066c6518930006af6418930006ac64189300066e75189300066d75189300066e54189300066c54189300066c50189300047e76549300047c76549300053c74549300063f64549300063c64549300066f62549300066c6254930004de76cc930006cc62cc930006cc624c930005d4714c930005d8704c9300067765d85300067465d8530006b764d8530006b464d8530006e762d8530006e462d85300067654d85300067454d85300067752d85300067552d85300067450d8530006776518530006746518530006b76418530006b46418530006e76218530006e46218530006765418530006745418530006d77318530006775218530006755218530006d73218530006d532185300067450185300065f658c5300ce5c658c5300069f648c5300069c648c530006cf628c530006cc628c530006d4618c530005da708c5300065f650c5300c65c650c5300069f640c5300069c640c530006cf620c530006cc620c530006d7610c53007c7e76941300063f64941300063c64941300066f62941300066c6294130006776194130006746194130004be76901300063f659013008e3c6590130006af6290130006ac6290130006b76190130006b46190130004be76101300063f65101300863c6510130006af6210130006ac6210130006b76110130006b46110130006cc628c130006d4618c1300047f755903000c7c755903000c7e75988300047d7598830004f77158830004f471588300053c74548300066e62548300066d6254830005787054830004dd768c83002ed43198430004df764c030005cc724c030005d4714c0300075a504c03000798404c03000c7f76597200347c745972000c7e75d93200047d75d9320004bd76993200063e65993200063d65993200363f75993200363c75993200063f52993200063c50993200047f755932000c7c75593200063c5459320034bf76593200063e65593200063d65593200063f75593200063c75593200063f52593200063c50593200347f76953200047d76953200363e64953200063d649532000c7e75d8f200047d75d8f20034be74d8f20004bd74d8f20004f671d8f20004f
  | 5 => 0x53f75500400853c75500400853e7598c400053d7598c400053f7558c400853c7558c400853e75988400053d75988400363c65988400053f75588400853c75588400063f76548400353e76548400353c76548400063c76548400343c76548400853f72548400872f72548400072e62548400072d62548400053c705484008e3e60548400853e758c8400053d758c840005b7714c840005b4714c840005bb704c840005b8704c8400853e750c8400053d750c840005ba700c840005b9700c8400853e75984400053d75984400053f75584400853c75584400363c65584400059f73584400059c7358440005af7258440005ac7258440005ba70cc440005b970cc4401f71f658c4401f71c658c4401df1f528c4400071d528c4401ed9e718c4401e69e608c4401df1c508c440005bb704c440005b8704c440034be760c440004bd760c4400853e750c4400053d750c4400069e760c4400069d760c4401bf1e750c4400071d750c4401d71f650c4401d71c650c4401bf1f520c4400071d520c4401cd9e710c44000796710c44000796610c44000795610c4401c69e600c4401bf1c500c4400853e75c84400053d75c84400059e73c84400059d73c84400079431c8440005ba70c8440005b970c84400072d52884400059f73484400059c7348440005bb7048440005b87048440034be7608440004bd76084400853e75084400053d75084400072d52084400079431084400853e75980400053d75980400363f65980400363c65980401b73850980401b73a75980400073975980400373b65980400373865980401b73b5298040007395298040005ba71980400079a31980400079831980400353e76940400353c76940400053d72940400071e31940400071c31940400853e70940400873a709404008e3e60940400073a60940400347c74597300047f725973002e5c31597300363f75993300363c75993300063f529933002e9c31993300063c50993300047f755933000c7c75593300063c54593300063f75593300063c75593300063f525933002e9c31593300063c50593300347f76953300047d76953300363e64953300063d649533000c7e7598b300047d7598b3000c7e7558b300047f7654b300047d7654b300053c7454b300063e6454b300063d6454b30005787054b30005d4714cb3002ed4319873002ed431587300ce5e658c7300065d658c7300069e648c7300069d648c7300747d76943300063e64943300063d649433008e3e65903300063d65903300863e65103300063d651033000c7e75d92300047d75d92300047f755923000c7c755923000c7e7598a300047d7598a300053c7454a3000c7e75986300047d7598630034be7498630004bd7498630006d6618c63000c7e76d95300347e74d95300047d72d953000c7e75d91300047d75d
  | 6 => 0xe75d8e400053d75d8e40005ba70d8e40005b77158e40005b47158e4008d3e7518e400053d7518e40005ae7218e40005ad7218e40005ba7018e4008d3e75d8a400053d75d8a40005ba70d8a4008d3e7598a400053d7598a400063e6598a4008d3e7558a4008d3e7518a400053d7518a400063e6518a400059e7318a400059d7318a40005ba7018a400053f7654a400063f7654a400043f7654a400053d7654a400063c7654a4008d3f7254a4008f2f7254a400053c7054a400863e6054a4008d3e758ca400053d758ca40005b7714ca40005b4714ca4008d3e750ca400053d750ca4008d3e75d86400053d75d86400063e65d86400059e73d86400059d73d8640005ae72d8640005ad72d8640005ba70d86400063e65586400059f73586400059c735864008d3e75186400053d7518640005ba70186401e71e658c6400071d658c6401e71f528c6400071d528c6401e71c508c640004be760c640004bd760c64008d3e750c6400053d750c6400069e760c6400069d760c6401c71e750c6400071d750c6401c71e650c6400071d650c6401c71f520c6400071d520c64000796710c64000797610c64000794610c6401c71c500c64008d3e75c86400053d75c86400059e73c86400059d73c86400079431c86400072d52886400059f73486400059c7348640004be7608640004bd760864008d3e75086400053d75086400072d520864000794310864008d3d76942400053d72942400071e31942400071c319424008d3e709424008f3a70942400863e609424000c7e76d95400347e74d95400347c74d95400047d72d954000c7c75d894000c7e75189400047d75189400047e76549400047c76549400353c745494002cde73d8540004dd73d85400065f658c5400ce5c658c5400065f650c5400c65c650c540006d7610c540006d4610c54009c7e76941400063f659014008e3c65901400047f7558c4000c7c7558c400853e7590c400053d7590c400053f7550c400853c7550c4000c7e75988400047d75988400363c54988400047f755884000c7c75588400347c76548400353e74548400353c74548400066e62548400066d62548400853e75908400053d75908400363c65908400053f75508400853c755084000c7e75984400047d75984400047f755844000c7c75584400363c5458440004df735844002cdc7358440004ef7258440004ec72584400853e75904400053d75904400053f75504400853c75504400363c65504400059f73504400059c7350440005af7250440005ac7250440005bb70504401f65f658c4401f65c658c4401f71e548c4401f71c548c4401d65f650c4401d65c650c4401d71e540c4401d71c540c440006d6610c440006d5610c44000796410c44000795410c4400347e76940400347c76940400353e7494040004bf7650040
  | 7 => 0xe500053e74d8a500053d74d8a500457a70d8a500347c7458a500055e7318a500055d7318a5004d7a7018a500347f76d0a500047e7690a500047d7690a500363e6490a500047f7650a500047c7650a500047e7610a500047d7610a500363e6410a500047e768ca500047d768ca5000577714ca5000574714ca500047e760ca500047d760ca500055e73d86500055d73d86500157a70d86500055f73586500055c73586500056f72586500056c72586500053e74186500053d741865001d7a70186500363e64d06500055e73d06500055d73d06500047e76906500047d76906500047f76506500047c76506500363e64506500055f73506500055c73506500056f72506500056c72506500057b70506500057870506501f65e648c6500065d628c6500c55e718c6500ce5e608c6500cf5a608c6500047e760c6500047d760c6500053e740c6500053d740c6500065e760c6500065d760c6500071e740c6500071d740c6501d65e640c6500065d620c6500cd5e710c65000756710c65000756410c65000755410c6500c65e600c6500c75a600c6500047e76c86500047d76c86500055e73c86500055d73c86500075431c86500055f73486500055c73486500047e76086500047d76086500053e74086500053d74086500075431086500347c74597400047f72597400363c405974000c7e7598b400047d7598b4000c7e7558b400047f7654b400047d7654b400353c7454b40004df735874002cdc73587400ce5e658c7400065d658c7400c65e650c7400065d650c740006d6610c740006d5610c7400947d769434000c7f76596400353e74596400353c745964008e3f745964008e3c74596400047f72596400347c705964008e3e40596400053d76952400363d76952400053d72952400363e60952400373a6095240004f77158e40004f47158e40005b671d0e40005b571d0e4008d3e7590e400053d7590e4002cbf7650e400053f7550e4008d3c7550e4000c7e7598a400047d7598a400063c5498a4000c7e7558a400047f7654a400047d7654a400353c7454a400353f75d0a400353c75d0a4008d3e7590a400053d7590a4012e3e6590a400053f7550a4008d3c7550a4008d3e7510a400053d7510a401263e6510a400063c5458640004df735864002cdc73586400fe3e65d06400059e73d06400059d73d064008d3e75906400053d75906400053f755064008d3c75506400f63e65506400059f73506400059c7350640005af7250640005ac72506400ce5e658c6400065d658c6400071e548c6401e71c548c6400c65e650c6400065d650c6400071e540c6401c71c540c64000796410c64000795410c6400347d76942400353e749424008d3e75d02400053d75d02400073a50d024008d3f765964008e3f76596400053f725964008d3c705964008d3
  | 8 => 0x7677154a21007647154a210056c7054a2121d6f75d0a210056d7510a2121f2c5410a210074d528c6210074d520c6210056d75c862102cde7398221004dd73982210047f755822100c7c7558221004bf7458221034bc745822100c7e75d91210047d75d91210063c54d91210047f755912100c7c7559121004df735912102cdc7359121004ef7259121004fb7059121004f8705912102cde76d8d210065e54d8d210065c54d8d210065f52d8d210065c50d8d21004f77158d21004de7618d2102e5e7518d2102e5d7518d210065e5418d210065c5418d210065f5218d210065c5018d210053c74549210065f63549210065c6354921004de768c521004de760c521006d463c852100c7e75d81210047d75d8121034be74d8121004bd74d81210067850d812100678501812100c7f76594210a56d72594210347c74594210047c705942100c7e75d90210047d75d9021004bd76990210063e65990210063d65990210363f75990210363c75990210063f5299021004be70990210063c50990210047f755902100c7c75590210063c5459021034bf76590210063e65590210063d65590210063f75590210063c7559021006ac72590210063f5259021004bc70590210063c50590210347f76950210047d76950210363e64950210063d649502100c7e75d8c210047d75d8c21034be74d8c21004bd74d8c210b47f76548210053c74548210063e64548210063d64548210056f76548210b66f76548210072f74548212156c74548210072c74548210052c74548210072e64548210072d64548210ae6e61548210056c70548212156f75d0821006ad64d0821004ed76108210056d75108212172c5410821006b564cc4210076552cc4210ce5e658c4210065d658c4210069e648c4210069d648c4210074d528c42120dd6718c4210c65e650c4210065d650c4210069e640c4210069d640c4210074d520c421004f5760c421006b5640c42100765520c421006d6760c421006d5760c4211ff56750c42100755750c4211ff56650c42100755650c42100796740c42100795740c421006d7640c42100796640c421006d5640c42100795640c42100695640c42100756540c4211ff54540c421007c6720c421007c5720c421206d6620c4211ff57520c4211ffc6520c42100755520c4211ffc5520c42100745520c421007c7420c421007c4420c4211ff54500c4210056d75c8421007c431c8421007655288421004ef7648421004f77648421005d4734842100c7c7598021006d431980210047f755802100c7c7558021004bf7458021034bc7458021004df735802102cdc73580210857a70d92500363e64192500063d641925008d7a70192500657a70d8e5006d7a7018e500057671d0e500057571d0e500047e7690e500047d7690e500047f7650e500047c765
  | 9 => 0x571d08310c55e75908310055d759083124f1c54908310055f75508310c55c7550831005d77150831005d471508310c55e75108310055d75108311d71c5410831005d67110831005d571108310ce5e65984310065d65984310069e64984310069d649843102f56659843102f556598431005d5749843102f96649843102f956498431007565498431247545498431005d67298431247575298431007555298431005d67098431247545098431004dd76d04311d71c54d04310c55e75904310055d7590431005d77690431005d5769043123756759043100755759043123756659043100755659043123dd574904310079664904310079564904311d75654904311d7545490431005d67290431237575290431007555290431005d67090431237545090431004df76504310055f75504310c55c755043122f1c5450431005cf7250431005cc7250431005db7050431005d87050431005d77650431006d7765043100757755043122f54755043122f56655043100755655043100797745043100796645043100795645043122f9754504311d75654504311d754545043122f94545043122f145450431007c77250431005d47250431007c47250431005c4725043122f575250431007555250431007974250431007954250431007d37050431005d47050431007d07050431005d0705043122f545050431225d671104310079541104310c55c75980310055f75580310c55c75580310059f74580310059c7458031005cf7258031005cc725803102ed8605803100c7f76597210053c74597210063f74597210347c74597210063c74597210343c74597210047c705972100c7e75d93210047d75d93210063c54d932102cde73d9321004dd73d9321004fa70d9321004f970d93210047f755932100c7c75593210347f76953210047d769532100c7e75d8f210047d75d8f21004dd7698f210065e6598f210065d6598f210065e5498f210065c5498f210065f5298f210065c5098f2102cdf7658f210065e6558f210065d6558f210065e5458f210065c5458f210065f5258f21006d77158f210065c5058f210a47f7654b210053c7454b210065e6354b210065d6354b210ce5e658c7210065d658c7210c65e650c7210065d650c721006d5630c721005d5760c721006d5760c72120756750c72100755750c72120756650c72100755650c72100796740c72100795740c721006d7640c721006d5640c72100756540c72120754540c72120757520c72100755520c72120754500c72100c7c7598321006d431983210047f755832100c7c7558321004bf7458321034bc745832100c7e75d92210047d75d92210047f755922100c7c75592210063c54592210053c7454a2100e6f7654a2100e6c7654a210072f7454a2121d6c7454a210072c7454a210052c7454a21
  | 10 => 0xa311f55c75d0a310cd5e7590a310055d7590a3125f1c5490a310055f7550a310cd5c7550a310cd5e7510a310055d7510a311f71c5410a311f71c54d06310cd5e75906310055d75906310055f75506310cd5c75506312571c5450631005cf7250631005cc7250631005db7050631005d870506310cd5e75d82310055d75d82310059e74d82310059d74d8231005ce72d8231005cd72d8231006db60982310055f75582310cd5c75582310059f74582310059c745823100c7e75d91310047d75d91310047f755913100c7c7559131004df7359131004ef7259131004ec7259131004fb7059131004f8705913100c7e75189310047d75189310053c74549310066f62549310066c625493100c7e75d81310047d75d8131034be74d8131004bd74d81310347c74594310c65f735943102e5c73594310047f725943102e5c31594310047c70594310363f75990310363c759903102e9e73990310063f5299031036b67199031004be70990310063c50990310047f755903100c7c75590310063c545903102cdc73590310063f75590310063c755903102e9c73590310063f5259031004bc70590310063c50590310347f76950310047d76950310363e64950310063d64950310069d64d0c31005d571d0c310055f7550c310c55c7550c310369e6450c3100c7e75988310047d759883100c7e755883102ecc32588310047f76548310047d76548310053c74548310063e64548310063d64548310c55e758c8310055d758c831005d7714c831034f57690431036b6645043122f345450431005d77350431007974350431007954350431005e47250431005f07050431004df764c43100c7c75980310047f755803100c7c7558031004bf7458031034bc7458031004ef7258031004ec725803102ed8305803102d5f76594310c65f76594311d55c74594310055f72594310055c70594311d55c75990311d71c549903102d9d76990311d71f75990311d71c759903102f1e659903102f1d65990310071f52990310079671990310059e70990310071c50990310055f75590310c55c75590310071c545903102d9f76590310069f76590310071f75590310071c755903102f1e655903102f1d65590310071f52590310079671590310059c70590310071c50590311d55f76950310055d76950311d55e74950311d71e74950311d71e64950310071d64950310055d72950311d75671950311d75571950311f65e61950310055e70950310c55e75988310055d75988310c55e755883102ecc62588310055f76548310055d76548310071f74548311d55c74548310071c74548310051c74548310071e64548310071d64548310c55f72548310c74f72548310075771548310075471548310ce5e61548310055c70548311d55f75d08311d55c75d0831005d671d0831005d
  | 11 => 0x65c50d8d410065f6518d410065c6518d410071c5418d411d65e5418d411d65c5418d410065f5218d410065c5018d4102e9c63d0d41005b671d0d4102cbc7650d410f53c7550d41005b47150d4100c7c75d89410066f52d89410066f65d89410066c65d89410072c54d8941006cf63d8941006cc63d89410066f75d89410066c75d894121e6e54d894121e6c54d89410066c50d894100c7e75189410047d75189410063c54189410066f52189410066f65189410066c65189410072c5418941006cf6318941006cc63189410066e75189410066d7518941006af54189412166e54189412166c5418941006ac54189410062c54189410066c50189410047e76549410047c76549410353c74549410065f63549410065c63549410066f62549410066c62549410353c75d0941006ac62d09410f53c7550941006ac62509410f53e759054100c7e75d81410047d75d81410067850d81410067b65d81410067865d81410073854d8141006db63d8141006d863d8141006eb62d8141006e862d81410067a75d81410067975d814119e7a54d814119e7854d81410067b52d81410067952d814100c7c75181410063c54181410067850181410067b6518141006786518141007385418141006db6318141006d86318141006eb6218141006e862181410067b7518141006787518141006bb7418141006bb54181411767a5418141176785418141006b85418141006385418141006bb4318141006b943181410067b5218141006795218141006bb4218141006b94218141006ba411814100c7e75988410047d75988410353c7454841004bf7650441005b87050441036b840980410047f755804100c7c75580410047f755933100c7c755933100c7e7598b310047d7598b310053c7454b310066e6254b310066d6254b31034f77650731267345450731005e47250731005f070507310047f755833100c7c7558331004bf7458331034bc745833100c7e75d92310047d75d92310047f755923100c7c75592310063c54592310cd5e7590e310055d7590e31034df7650e310055f7550e310cd5c7550e3100c7e7598a310047d7598a310053c7454a310cd5e758ca310055d758ca31006ce624ca310cd5e750ca310055d750ca310047f755823100c7c7558231004bf7458231034bc74582310cd5e75d92310055d75d9231005d671d92311f71c54992310055f75592310cd5c75592310071c5459231005d671192311f55e74952311f71e74952310055d72952311d65e61952310055e7095231005d671d8a310cd5e7598a310055d7598a31006cf6298a310cd5e7518a310055d7518a310059e7418a310059d7418a31005d67118a310071f7454a311f55c7454a310071c7454a310051c7454a310cd5f7254a310cf4f7254a310c65e6154a310055c7054a311f55f75d
  | 12 => 0xc755824200c7e76d95420347d72d95420047e70d95420347c76549420353c745494212e3c659094202cde73d8542004dd73d854200c7e75d81420047d75d814200c7c75181421263f74594420347e74594420347c74594420363c74594420343c74594420047c70594420363c405944212c7f76548420353c7454842004bf76508421253c75508420072d52508420363c5458442004df735844202cdc735844200c7c75980420363c5498042036b840980420047f755804200c7c75580420047f755933200c7c75593320063c54593320053c7454b3202ed4319873202ed431587320047f755833200c7c7558332004bf7458332034bc745833200c7f76596320347c74596320047c705963200c7e75d92320047d75d92320047f755923200c7c75592320347f76952320047d76952321047f7654a320053c7454a320074d52cca3200c7c75982320047f755823200c7c7558232004bf7458232034bc745823200c7e75d91320047d75d91320063c54d91320047f755913200c7c7559132004f77159132004f47159132004fb7059132004f870591320053c74549320067654d85320067454d85320067752d85320067552d85320067450d853200c7e75185320047d7518532034be7418532004bd7418532006767518532006757518532006b67418532006b57418532006765418532006745418532006d77318532006775218532006755218532006d6321853200674501853200c7e75d81320047d75d8132034be74d8132004bd74d81320067850d81320067850181320347c745943202e5c31594320047c70594320047f755903200c7c75590320347f76950320047d769503210c7f76548320053c7454832004df764c8320074d524c832005d4714c83202ed4319843200c7c75980320047f755803200c7c7558032004bf7458032034bc7458032004f77158032004f4715803202e5e7598f4102e5d7598f410365e5498f410365c5498f410065f5298f41036d64198f41036d54198f410065c5098f410369c4098f410365e5458f410365c5458f410065f5258f410065c5058f410369c4058f410fd3c7550f4102e9e6350f4100c7e7598b410047d7598b410363c5498b410353c7454b410065e6354b410065d6354b410066e6254b410066d6254b410fd3c7550b410363c5498341036b840983410047f755834100c7c7558341036b8405834100c7f76596410047f72596410047c705964100c7e7598a410047d7598a4100c7e7558a410047f7654a410047d7654a410353c7454a410fe3e65d064100c7c75982410047f755824100c7c755824100c7e76d95410353e74d95410f63e74d95410f63d74d95410047d72d95410047e70d95410065f65d8d410065c65d8d410071c54d8d411f65e54d8d411f65c54d8d410065f52d8d41006d571d8d41
  | 13 => 0x8743006767598743006757598743036765498743036745498743006d77398743036d64398743036d54398743006775298743006745098743036b44098743036765458743036745458743006775258743006745058743036b44058743036b840983430047f755834300c7c755834302cbc74583430047f725964302e5c31596430047c705964300c7e7598a430047d7598a4300c7e7558a4302ed4319864302cdc735864300c7c75982430047f755824300c7c755824300c7e76d95430047d72d95430047e70d954300c7c75d894300c7e75189430047d751894300c7e75d81430047d75d814300c7c751814300c7e75988430047d759884302ed4319844302ed43158443036b840980430047f755804300c7c755804312e3f62d915212f2f62d91520053e70d91521253e74991520063f64991521356d729915213d6f72591520363e64191520063d641915212d3e76191520063e76191521263f62191521272f62191520053e70191520363f73191520363e73191520363d73191520363c73191520363f72191520363d72191520363f71191520363e71191520363d71191520363c71191520363f70191520363e70191520043e70191520363d70191520363c70191520063c64d8d520053e7498d520053d7498d520063c6498d521156d7298d520053f7458d520053c7458d520063c6458d5211d6f7258d52005777158d52005747158d520057b7058d52005787058d520063c6418d520363c64d0d520056e72d0d520056d72d0d520057671d0d520057571d0d520047e7690d520047d7690d520363c6490d520047f7650d520047c7650d520363c6450d520363c6410d520063c64d85520055e73d85520055d73d85520053e74985520053d74985520063c64985520bd6d72985520053f74585520053c74585520063c64585520055f73585520055c73585520ad6f72585520057b70585520057870585520063c64185520053e74d81520053d74d81520063c64d81520053e74981520053d74981520063f64981520063c649815205d6d72981520053f74581520053c74581520063c64581520055f73581520055c735815204d6f72581520057771581520057471581520063f64181520063c64181520063f74181520347e74181520063c74181520047f7558f4200c7c7558f420347c7654b420353c7454b4200c7e75987420047d75987420047f755874200c7c7558742004df735874202cdc735874200c7e75983420047d7598342036b840983420047f755834200c7c755834200c7f76596420353c745964212e3f745964212e3c74596420047c7059642004f77158e42004f47158e421247f7654a420353c7454a420353c75d0a420072d52d0a420063c5458642004df735864202cdc735864200c7c75982420063c54982420047f755824200c7
  | 14 => 0x4000000000400000000080020020050000004001000000800600800000140000110000004002005002801000600100000240000000000000008000001000c0060010000010000004001000000200000000040020010010004000001000800000000100280240020100000008002001000000000c001000001000000f003000c0000000010004000000000800000200500380080020080010010000000000800000400000280000000010028014000000000003c002000001000c00800a00080000040070030008000004000000000a0070000008000000001800801600200000040000010020000000001002800400201000000000000020008008000000000000c000006000801c012001000801c004003000000800200b003800400000300080000000020010018000007000000000200000d000000e01200180000000020008008000001000000c00600100000000000020000004000001001001c00a0000008004020000000000801400400080000000040040000004007000004000600400000040020020018004002000000800400e0000008010000013000001000a001000000000000600180080080050058000000003001000c00000000000080100000010000004000000000001800300080000000020028004000001001800400c000000000000000000000040080010000000002000001000c000000000000000a005000000c01e0000008000010000003000000a00900000000000000000000000008001800000000000000000000000010008000000000801c006000000801801400500000000020000000000002000001001001a000000000400a00300080280040000028000006000001801000800f0008004004002004000000200400080040060050010020000000000000400000200000100260000000000004005000000000000600000040000010008004002009001000800000000080140020000008004008001000800c0000020000008000001005000c000000004800001e00d00080380000010000000000002000800001a0000010000000000000801c0040000000000000000001000c00000e00500040000060008000000000005000c008006000800c002004000000c01e000002800801400800000000040000000024000000002000000200400080000000040018000000000000001800000200480000020000000000008000002000800a00000280200040010000000002006000000000600b001000000a00000280000000010347c7458a540366f7258a540366f4258a540366c4258a540047c7058a540363c4058a540347e74982540363c74982540047d72982540367a70982540367b40982540363c409825403678409825403638409825400c7e7598b430047d7598b4300c7e75987430047d759874302cbe749
  | 15 => 0x22f43ac0000001e4000093b0000000caa02b26c0000ff6000000000000012000023000000000a810903b80000df09a46e60002f821d80000a60a78b5c5268a7000094c2a82e326e87bc25a00000b18140000000000a080000000000000000000032957c61e00000000000b0898000000000000009d955903c0001af14e02cc5e03fe000000000044b1c4800047024c15b4f2a46409b800000070c00017980000002db80000001eb341a590a560000000000ebe00000003e4f729550002340cf267143710e86623a51910e8800000003e88040000000001d6cc680000001b5925a7c02552000d5015500000100000000000000000305000152400063e42980001921bb0000000aee000162a37800000046100000000683610a94a426c134a00000000001f105384dc803068932465468b156a178dee670340000000038c000000094400012e9f3cbe63ae43300000000002f7800018263900000000000000000000e9e46a00000000ba0002ea000000000000000000000000002384df20000002154b464f94649d180002f21a880000000000d480006347b540200001f43a70601ea496c0c210a842058623c3559024a2e7a500794583b20002fe8e4cd601c31362234f3a52c00000000005153b60a9c91a61008900011d200010e02410140351b700012be55b0001e300c40002d60000e1264b3c880f046632d1a6248d0ac5e829f18dc00072d00005f09328d42ae0000c6400022c80006e047a16fa484a1202f00000007ae0002c30000b8a38f2e20000b960000308e008941fc15600000000000000e540000002ce20a40008950000000000000095a05c7a40000001bb870800042300000000004560268cc4171122800000000000000040010000000002001000800000600200200000060000000004006000000801800200100180040000020000000002003004801000000000000000360040000008000000000800c000000000800400400300000000000010008000000000000000400400000100080100060018000000000003800401800b000000800000200000040000080020004004004003000400e0020000014002002000000c000001004000c0040010000014000001001000c002002001000400e0010000014000000000800c00000000000000000000018000000000000000800000d002000001c005000004000600400000000080020020008026000000001000c001000001400c000000000400400d0000000002000000003c00200100080000000000008004000004003800c0060000008000000002000801c00c0000008018004007000000001e0010018000002000000001000a00300000000000000000000002002000000800000100380040040010020008000005005800800000000480080000000000020000003000000000
  | 16 => 0x9850e3552ac800000049443f9a8c92056545c00000000003a60000f1a00048791f8cd630d4471060ee664600b92308165af20700000000ed05c00000000001dd800029884946680000000002b9927400077e0af000023a0f207f80000000000000000000000000000000095220b80000005050000000d9e38d000000068695b0a516880000001bf00008b6000285000000000000000007288df1dc80000000002d7116830894e42c86bd15a73642d92d0784000174218c2ac03a00016e00003d5117232c0005ad0f31d10dd46d51970000dc600000000011b07df00016643be032000000025e00000000000000000000000000000000000113469d41e1a640009040b9a41c3aa909316156800000022e82c00000000000dacd0a3f813e8000976000000000000000008b1bbca7e5b10030000f120000001ac90860000c9a3b400000000000000001bf00022040920001508d7c1fa40318d80006fa6dc0000abc55c4f621601c400000000000012322880000e4000000018f80000000001b7a58c00020e00000000002f835380000000000000f143c65580000b042d400000011440008dc3748000dc20001ed19203700003889754000958183887c000434000000000073d2841dec7382d50001e58e6601b000000000000032c000000000000002a884235409f20b000036a00010f0b3627a3792100d769152e89b2c4204e314202912243fd36c88fc000000000259c266000000000000000002a21304c4000000255013660d0000000f9400000000000008242db0ad80001430000000000285134000000024227900000006a91751f1400000000007d80000000000000000313000000000000000f072000000000022980007bb000000094605f15d04a844e20644f01e400009430000000004d0277800122c5e70000000000000000000000000011d074c2fc00020f8bf099642a25821d4c4e44823e163cc6c2e94811a68d2a00039a80008b000002300000c800000023f00003920001a0400000023f8000bf400036c0000000000000056c00084400000000000001ac13901f800000000000000000000000eac3cb085194000087400000000000001a68000000799000000000000017010dc0000000000ad40000000f2a344322882000000000086d00000006d2000278096c0007ef00024c80ce6f400000005c4000152000000046815b88d000000046a9fc46ee2514498f900000004678000b4c56c1ae800000080e00015d800000030786a80002ff49d0f280cc00000000000004660002288f5a3320001a6c000696000000086a2612cf0408000000000000124e1cb0000000d040000000000d74924000000068e92e00000b80003ec4b100000000001a980000001e00001fd520070700000001ee000000058479a0003d40000000831000173800000
  | 17 => 0x3e10000000d920002f61de00000003d880000002f7000221cc32000000251000095d1e880000000000d20000da84a81d080000003bd301000000000000000012029350000000fd600015a00000002353f800000000e711b20a80000000af800068c0001cea5792180003e405b000032c32e92c80005f62661f9c530000000000097a821000222c0001a03238000cd451d47505e80000002910a3c4a8000133a1dc6b63ab13f800000056f00000000000000001e800005b929000843d40000000000000000000118c0003a90000a38e5856b0e49c34be40000491404c160152082220000000000000000083900000002462fb41c000106a000000000000061a00024f83788fa392000000000000000005c80001d30000000000000092800029400005c00008be47a00007ba00016505e4ffa260398000000000027a9818000000000000000033c2458ee00000003fc9de874870a2b080000000000000b6ce1095c0000cfcd6e0004859394f4403d000000000000000000010ae000047800000000000000000000000000000000000000000094a5332ff9e0000000000005900000000001ea8a965cf2799da10280000fc800065688a00009c0e765ea40aa08000069e0000000ca653700000000000b40001d2d1d6000000000082449e17700000001d831d800000012510e94780004be3528000bf60002f28ea0296000333951858e5be000158c30a5dd376021c0000023b90000cec00011d93dc8340000000a0c8de0000cc800000070b000000000000039710ac1d87472920000f58000206000100a0002ba800021c5790000000eb200027ea290d2268802aa0250023e91c50978e0857c00000000000000000a2ccfa705000041c00000000018582ce000469000072e2bc06a85ec0007292860000d680001460000dda5723db0858000217429023400050b47991ed21c36827d244451451400000012528e749b00011620001f1a4990de000000147c7fc8790638fdcae070f3db800076479f0001ba064800000000000000002448f0485c0000001c687fe000000000075e4920000000000762000000000000038113ec93678b00000004ac50d49c8f200000002c708886e21452e400000007643a0000000000000008c4000788000000000000000022a800078f00014987040001fd0c280006d3000000000000012384e000080c318800000081a36f0000f7c2460002528000000000000000008b2da8f380001de0000000ec2000264042cd6a000096151c00000000024612680000001d800000000000001234617051800006e8250fe9c5c57a0000000c8400000000000007460003ef000000000d000224800075a00000000000001a58000000000439225c4aa0000000ae00004ee1160000000000403882914a6be2c40cd00000000000f
  | 18 => 0x6a000010424a80000004271b200004540000000ee80000002bf00004463150000000e7e2243af00001724d100e1bc45da26b1fa800000029532797246380003dd0000aae00000003d42529132a500000007d500008bc0245543cd0d5c000000000000000000035b049800000000025047540002670000fcc8f600000000002f10000000000000027800000022823b1968c9813931f80000006543c180b44040df00000000000004a402140001f22d39610afa86442400d00000001931a8016400000000008140001df026057292c0000efcf824db0000000c6a00000010500000000000000cfc405000000000000000000000003180440a980e062d24080000000000000000000000000000000083d218193800000008b80000002750000000000000434000084a0002d5836433684f000239920c0003e80000382485000000000000000000002ba000000000000000000002dcae88fb00019d10a20000000000000000000000000000000012984cc00028780004220cb1ef83c02da608000214036e0000000340eb800000000000000003738000000309000000020c73100010cc00000000012dc1ae4ae0f4907529a13c0000000b8227e2f71a906847cd41407887da38b27f9138226000330a33000000000000002a282d000000031c8e445080002ca00048e218453a49602606500002fe062920c9228bc1928000876000336800000027946700000005bf004800000000016a1e780005432de80000a092b3180e380002e60001c845565673151690a000303cd9d391ca26d000033d11224337d05d014400026d05188a011547ea034000000000000000093d075128037447430f17085527bc000000000013139c00003943c7000000102000000000000000002ae9e106240003b880004187b80f607841ba38340900004c685d302000041e85f21325840000520000000ed289c0000001096000000000000049f000191000000046e80009bc0e301184fc6f67e51fe014c17c0001b9000000000000000000006f300000000000003e607b400000020c800078c304000000000021b00000000002760001d41056000000000002800000013a800a1fe15111085d62bb49402a00003592c2800000000000000000002d344800000000001f3800038e7412d50de85fa00016f0bd0be274d19180008be6e03ed0668b688543fb00009b87e80001f180004c30000000d1220838095e84800b63d205111b43b648422bc40e0001809ab891c84238e000000000002000007980003ba8000f8e00000000000000e509a00011ea00000000010101cc0000524000669000000068a26f0cc000000000000020e800018b00000000004283551f80e468a800000000000002588000000884000009800000025600011d000000000000002b10f39b4434c59a29491b03ae0
  | 19 => 0x243800028000000000000001ff00000000004a91001a4060000041f1abc4325a5000252c0006240000000a3801d11e91f436a0001a9101cfa40002628d88cf876740e02951186ca436000115c0ee00000002ee7850e880003205313c101dc0000000000a8090868f1b3953c0004c40000000000000000160c2e46e544880008887e100000004307c90000000fd47d8000000123a0000880000b8e4612c51f8c89e07642517340000000001b140000000fd95807803d83a298611a63d911c18ac05404b0000f50fda00029680007ca0002238750e3c56e2e6162400088300006a00004b300010bc19a0001b6004000000000004680000000e91c9c0000002a008a40000003071d5474000000017f83800002a8000066c1c400000009720000000b200004201ba09f05ac00015f8000000512000000000000045b14c0ef89300001fe894200000000000001dd0000464a7204a00013b52362480b40000a34000000250d1de52516e00000000000f4000000000003980000001cf0000000c520d24911554f1c4d232895e05e689400000002ec46b028a540cc80000001de45880000000000000000363000082a00000000009d65f900000000000ae0001384f3005c21f800000059d0001afc0003ad2af050488087300006c40008b519e97a400000000000000000000000e6108e00034e236c00090334c0df09043393d9164400007c03a854cca40363be8000000684000000049615800000001e273a000206c0b660305880010221c60221d506a0706000000000000044e80000007fe00020cc00051b06989a90046cc24d1a4ced616f0000a44000000324800000024f000220000056936d19fd19468c00000000008b01778f10ff0000000000000000000000000000db35e80000002650000d050c40000001c4061800036180000000000000c78000000000000031800000007e800000026b800000000000006e40000003898a244281633218aa8cee29b31318bd06e76f2cf9e9c0004083b317dc0000000000b44000000226000000087c359840c5b289f1f719282ea000000013408a18600000008e27424382564312749000000036c00018e9534f660000000d684646d70000b9c36403f29e0b3cd0c2cc27c23e400008c46201ecbc60001408000cdc74821b23f8cca00b485000000020d4641ddc4b05db0002018b764e632f800093800000000000004cf000000000000022598940000001fc8b38bea71b3df948cd1c8bf16d14d839c7ff30496800fc79c000000000067a19980000000990001af0000000000000000000027100000001950000b1904476a01d98501a80001ed800000000000021700004132fe00000661b00000000550000274848861639b28c8000dcc00000003ec00000000009ed10a7af000000000058b0001e1d23c0000621
  | 20 => 0xf58c460000001964a0c00000022eca260000000fa05007ae3bf800035c0000001fcc8e635c024000000000003680000000002168b60b520630d120c84420000000cd4cde0000001b1c7f60000000b2447c00000000002dc5e200000000001602ed131cb6637542d00000001781c3800000063a00000000000003c08244ec639a000195c26c00000000000000000c000000000000001b400007704179c6062c9490001844fe41ab084863c0004570000000000000000000000063c000187026068d1819bac3e221a23c8000dea0a733014e8c8433a399184802610043391551e293840784b8cac5ca03a15fc8a6000000000000006c000000000010c00c80000003b332280002740cc1a513b000000014b0b00000271000000000000024b80008d20002000000000544159a50000000000002803c80000000000000000040855c00044946080c400054800000000003ea06d11807d600001212ac00000024791e07a008416589044120080000000000000000216000000037f827c8440003a9000000000000000000d232f36e8000000000435254400000037200000000000001ead2ac00039409cc4923b10378e200005de00009300000bc00014b8ba486000000001900002148ec0e94000000238c8089470c193f07c02e100003600008b71f89a1c97e0004b00b080fe8b900000000000000038000bda00000000001760002cc253c8a88d93ea0000a820003da00000004c248b98cc00073935c021800200000004045f40ca1a200000000000d68ed433a597000000000052700003380004d600008dd13640d282000000000034b81e097400000024fc49a82718a0c085a40001b094d408648a000068c000000000000000000000023c80006cd4638001166000000000029038627380000000002290bd8000716000000007c3b44b295a000000000000000000af000000037a000000000000000049b80000000003e100000008f004b8e581c44860fa00a00006a204f08112980d63eb800034e3281bc11707125d621c0000a9830630f8879032147233a51411c0a128800008864390ac806800000000007143241110000000000000054a1380000003fa21140003914a311b8fa20002dd0000460792000111400076d0000000bc256440f80000001b43621dd8cf65f4000000000004707a00000000000001354112000000000094e00000013a000000043580000000000161658eba63800013c4d6211b1290a64b266214269cbc8e40001b0000017a0000000000b8034900000010f66a600009d02285663491e844264d904b16484c829e303908d2207ec1c095444ae62006e0740a5e3103a186b025000000000005ea0002e9847c6765030209f0c0e43bc2401a8400000000000000000000000000000000000000097800001280000008ee3959134546
  | 21 => 0x200006f208c1c20e048f9be00001812ec9350a7658d2c811880000002c00dfc7ec00005d0200e6822b087817800000000000012cc00000025080000000000000b180f636f8be4b860000cb881409c0000001cf8000673190053401c0003e5849cdf8000000228d04c0001b1847000083622b0000000338000000000025f0001a7c4e400025c10587583b702b065800029f000009cdc47d900000000f40000001d5c8380ac0111db870a3ef2a9a19499a41b2e80bc0c0262243f196c0c040f1939cdc00009c47015c44b400041d882c0000003600f3c8ca0e900014f4b783f02a70a3498262e0000b4061c00005592d453418a000000000000000000000000b549e17610f460a001800000029c27000000001182c080002a4000000255c0005d738e8ca4a68220326a450cbc5b23ed8708bd6000000000115651100001a80000000001bf433e54233a80000004463d80f0c00000017600000003d30000000000105000000012600000000e442408a0002218000000309857000000049500001c8000010003073e0000b4986ca1c0003f1000017e0003f21f751d86ad41f800080200026f977c0300000ed03ac1f02900f81c0d1c41870001f5866e66304e9bc000000000000003420003ac1e1911e6fb000000000082e000000000016220f10080000003ba007c00072a00000011fe00025683bcb0400028c0318c8000000000000006ce27f07d4f2e2250000d951ac042000210400000000000000005b000005fc0ae751000000106892518ca1f400000004a8ac8da42440000b7400000000000000000002fc0000e7800015f24cc01472200021a487a17d0799548f4c46d3de84f426443e3061fdc94853247b800015a259482800000000000005080000001cca0580007152b11c8000071f08680000000000f980000003f219f204c0000000000000dfc000220934c00000001c000000005908f1ab0a0e7c40000000e4a308000000000000039312bc3f00000000398000000014816834a00046193d00000003640000ea64c623b9b6d2405281bc9d940006414630000cd800000004d4000348000000000000000000007bc2b02b50000fa6000000197082234e00000000008a000006081868b20000000bc8000000076c00059540e800000000024413280007e930ea314bb88ba0cf0b94792871333000000025c00000000000000000c5c00006b00020c07e6000000161d1f00000ad18a000057b2188000a8a000000000000045e1270a184f02260000dd800000045a2060b8c0830001a28ce416b1fa0d3c1d070e0e682cc0006151a00a5c31a700000124c00000000000000001243f70670e3292f2d08000cf071400000000003dc00000000001b3000000000036600024c400008203719a0c7a52a00022640000fe00889408ea7dc0001e8c3dc000000
  | 22 => 0x31000000000000000001491f391523110000b343ee6f62ca00006ac000000000073c000000140866000026000012a678a405800080c00000000000008d700000000008781b6a56886400000009dc472793116880c00090d0909e50d7
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xcc4621c5324c00146908a96c2980028d21152185300066830ce118a6000c2c74989520c001858e8b12a41800299205625483000634b10e0a906000d8872101300c001b20e2202601801a0f21e6454b200041e43ac8a96400683f875d3658806b8d2e5386cb1001a0fa1375586201f50f426cb18c403aa1e84d94318800152b09308631010e8ba13658862021517426ca10c4000e47650c4218800d07b0fb2c8110002936085418d200041f430e8a92402483e87d91524800d0790e322a490003071d363549200060e3a0c6a924000c58631c1524800146908a96c2900029960854185200051a422a430a4000a7080548614800d07d0fba2ca100023520573d90200050e422cb3184000a1c8459563080018acca38ac610003155947158c2000662390e2b184000c56851c563080018ab0a38ac61000325a107158c200064ac20e2b184000c56541c563080018a8a838ac61000315d487158c2000526c10a0b184000c54711416308001838e931aa410003071d163548200052a40ac6a90403ea1c84596310807543908b28621010e8b211658842021516422ca1084000e45650c421080014a902b1ca0100020fe1d65900200054a40ac7200400683c87594400800152902b188010003521407348020006b0280e29004000d88731012008001b40e22024010002ca211524802000594422ca9004000d48751cd2008001b10e839a4010002f02056348020006b03a8e29004000da0741c520080015930c18a40100cf0e10176953100341e422eb316200683c845d952c400107b0c3a2a58801a0f21e6454b100041e43ac8a9620339388754840c4001858a9396c90801a0f2117518a100060e3a4c6a942000c1c7458d5284001858e9312a5080030b1d16254a100070a2a6c818c2000ac682d90318400152b093106308002c5211520c61000723312a418c2000b24845482184001c8cc6a9043080028ba1375d89100341e422ea3122000a2c845d4624400d07d093b2a4880020fa1874549100041f43ec8a92200683c871915244001838e9b1aa488003071d06354910006163a6c4a922000c2c74189524400d07908bacc408002e4201740c4100070a2a2c818820008d587188310400152b083106208002c5211520c410005a8402a41882000b90845c0310400164908a904208002d8201520841026f88280622002000f1031940400405d870a8bb08008003345d83110010277892a062200204ef10540c4400405d870eabb080080ba4e21d5210010005c841ae22002000ba0825c4400409f7250318880080026c61c3110010006c9438622002000d91870c44004001d24ec1888008003a45d8311001026f89428622002000f11850c4400409de26ea188800813bc41d4311001026f89a90622002000f11520c44004001725079088008003c85482110010
  | 1 => 0x908a9063908930bdd87454a2100497400e8a944200d24741c5528840161908a946310802c3211520c62121c96422eb90c4200c1c74d8d5248401838e831aa4908030b1d4725902100516c10a0b20420683c8799152084010790eb22a41090b49a04745482121692c08e8a904243c2e611d1520840125d003a2a41090a4b21e64548210049643ac8a904242c2c545d8420848525908ba88410802c921152cc42100586422a51884200b0c84548310840164908a906210802a5612760c4211fda2c12ca1884200a95869d0310840152b0d320621080385151640c4210070b32ac81884200e1565590310840152f0eb206210802a561d640c4210070bc2ac81884200e14855903108401c2ceab206210803855d5640c42100742412c81884200e1752590310840152900b20621080385141640c4210052ac34a81884200e1564950310840168b0b390621090295e19520c4210058a422a41884200e1564548310840168f0ea906210802d161d520c421005a3c32a41884240e47865483108401e0f08a906210942d1211520c42100782422a41884200b04845483108401e0ce8a906210803c15d1520c42100783322a41884200f0564548310840168900a906210942d1e17420c42100742b26841884200ac586108310840168b0a2106210943c1150420c42121496422eb9084200d45750c7210840164908a94421090b0b99072506501761d320e0a0ca03ae1664504319400168904a086328002d4201410c6500341f424ed90ca000d15740c4219400145b042a4c5200920fe197510a4000617328e4a0c8045e1665504319000170904a0863200028b60a6598a40004ca40ae6314800083e871d9529000185ccb396c3200030e99670d86400050fc32a518c8000a1f865483190001c2ccbb086320002e1a0b610c640005c9406c218c8000b9280184319000107f0cbae43200028be19528864000517c32a410c8000c96760c42190001e0aa4188432001a0f2107654940036163a4c4a90800686c875895210085858a8392c22010b0b19472504401d70a2a2c21888000ac4825843110075c28caa086220002e1209410c440036163b4c4a90800692c87589521000136102b8064200024e201759844021616328e4b08803ea1c8654a311000183aecba862200ea87219520c4401d70a32ac21888000b8482584311000d0790cbae4220003640c670c844021d16432a51088042a2c86548211000185aeca904220003255d8310844000782a90621088006938805d6601000d2730f304a02001a0f2117598b300341e422eca96600083d861d152cc00d0790f322a5980020f21d6454b3000517426ebb12600683c845d4624c00145908ba8c49801a0fa1276549300041f430e8a92600083e87d91524c00d0790e322a4980030b1d36254930006163a0c4a926000
  | 2 => 0x854181410070c2a6c63028200e185418c6050401c50a9b10c0a08038a15062181410051d42ee83028200a3a871506050401473042a0c0a0802aca0743181410051c42a863028200ab08150c605045d47108a90c0a08ba8e21742181410051c42a843028200a3a859046050401858e9312a5988030b1d16254b31006922a0e4a0e6200d30541c141cc40d07908bacc5188fb4610270952311f48e422eb3146200ac681d8a628c40123d003a2a5188034315072506310068c2a0e0a0c6200c2c74d89524c401858e8312a49881a0f21175988310341e422eca906200878805d9520c40107b0c3a2a41881a0f21e64548310041e43ac8a906245b148550d410c401a48a839282188034c1507050431006c9a18e0a086200d91431c1410c40143b0da92c8188028761850590311d60f322ed2a0623ad18409c2540c47523908bacc4188ea472117654831004ac402eca90620091d861d1520c475a2d023a2a4188eb4560474548311f60f308e8a90620091e801d1520c4752390f322a4188024721d64548310068a3a6e2a906200d14741c5520c47523908ba884188eb4515171108310068a2a2e93086200b148454a610c475838a8bb68218803255d96490431004abc3aa5208623ab148454a410c47d838a9bb282188034315072504310068c2a0e0a086200d1454dd9410c47dc28a9bb282188eac5a1375504311d58a422caa086245b1685dd1410c4756290b322821880325dd9645043122d8a42ac8a086200f0454dc9410c401a28a8392821880351d487250431006a3ba8e4a086200d44751c9410c401e08a8392821880351a147250431006a2c28e4a086200d46651c9410c401a8aca3928218803619907250431006c2b20e4a086200d87541c9410c4a5a8ca8392821894b511507250431006c22a0e4a086200d04541c9410c401a88a039282188025521d52504311d58a422a4a086200d4472549410c4756290ba128218803611cb425043122d8a42a84a086200d8472509410c401e20a9b828218803701cb70504310068a2a0e0a086200d50501c1410c401aa6ea3828218803541d47050431006c9ba0e0a086200f10541c1410c401b86e43828218803701c87050431006a9c28e0a086200d50851c1410c401aa4ca3828218803545947050431006c9c20e0a086200d92641c1410c401b22c8382821880364d50705043128ea92a0e0a086251d50541c1410c401b20a83828218803441507050431006a9a90e0a086200d51521c1410c401b26843828218803645087050431005c840282208620683e87dd165c8401870a9386c990802872116598f210050e422cab1e4200c1c7498d52c8401838e8b1aa5908fa87211658c7211d50e422ca18e4200b148459431c8401c28a9b206390802b4a03640c7210052ac34a818e423fa578654831c840162
  | 3 => 0x7194d00000660007053c1bc9417d3702c5c6304f388d0474b266400140267596f0fc4a279b2001a854c4626c77000f26fce6000000005a000005712c064004a57f00000294004680067d1951000001cc2b50f624790e800001c900183648004ed68280ff090ae000f0001632a821000000005e000000013f23800154685450236800600002840018ccd00000000c23548107d2369db02c0122a56b0698b63cdb000002f51200186001351ad2a001540d8c5651a0575a4078042889753915514de7548829849000001ec0010ce5000000ecb66543c000000000006d7a0000000000274002dd5f418b900064001be0c4000017c001cd0010c0000f32800684440002a001706a400344025ec4d46c00040004e00052400438ee261967000052c004980044c003c55000000000000002e00000000e46d8d600120001b4000ec00000000005902d68800318390017e2703800000018005a9720012e491c76b15b00000001881ccb34c158000000a07174db3348001a576000232f0ea33d213cd400acbf5c4006f569000002b09f31c000013919c000007855c000005200000816008020001603000030000180200032068020001a05014078020002a040040000c03000000000700c0081a00008000000100206020038020280200006078000a0020080a0000c020280383e0001400000028040800404000020000182400004018080001e008100000001814000120d0000580209800028000000e000000000e008040001600800050000000a0180201002068080400206802068140000000000000000680200800008040b0100000000802028000003601800008000082004814000029960a75987430041fc3ac8322a406c3a809c06454801868c9b8ac6a90030d1907158d520061c326e0b1aa400c38641c1635480d858c939686a901b0d19271d0d520361a322e3a1aa400c1c649cf6154801838c8b9ec2a914f0bdc864585520060e326e6b0aa400c1c641cd6154801870c9b82c2a90030e19070585520051d400c9b02a40083e871916054801838c9b9ac0a90030719073581520061a326e2b02a400c34641c5605480147501ba0c0a90028ea0074181520051d400a9304840692c87549421080185eeca9284210028d21152d85320045c402e830a6400a65829d4614c80156100ba0c2990028d211521853200532c10a030a6400a6982140604c80189eeca926419002c3211524c832006a2a90e29906406c1c7498d52d040d838e8b1aa5a081b0b1d26254b41036163a2c4a968200a2d821506250401c18a9b18c4a080383150631894100516c38a83128200a2e80150625047d838e9b1aa4a08eb071d0635494121e163a6c4a928242c2c741895250485858ea31684a08030b1d46250941007142a0c5b028233a388454b6050401475002a0c0a08028ea1
  | 4 => 0x72000000e0558cb00000320e700000000003e40000047000004796e0008323546180f70000014caf000840007200000000dd3517945dd128cd7028fa444163f8154d909000000018a000fd00000669d01b800000004c8cc569733bceb218f400c074885d0458e6b8bb2adab64c22564911019c49d3100082738e9224e8589473f0180c81772c664593a29103080935794a6ed755dc00000000b000000620d47a249ad1fcb86e83d024d3230d841c1c1f50a6f07c4613d00000001d822c00750c1605d204c9015800434c407457001c20012b000e3001335059b5988a00000268c91a8b4640b56152d50d4f0000000041001a300045001cf0002f000002016c000006bd48410590000d1d155131c30000000000000006c4001b5a55d014000f600000000001d400120a86990861c016e52525870001ca75d9e0010103000580000cc005b4b1000000017d0011f0391c23d973b5aa300be3e0654013463437608003709537d6521c00000a7000003850502167549c4715780016142c54001282e8276dc0050861138426d47616c056e184000fb3380030c001f800215103d430160346754c0a53e1b0d92644b64451094004bc00000000f91400000
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x1605008d068800001721908b9b801b1c8026000000030022000000000012800a83801aa7001da508801580000002858014801f00000016802399018212001e800f040c11138b001a00000980002000000004800a208c860f98001300001e0000000018a400000000210780001f8e000e99800000000026a300001d24918000000000000d9415010700000017a822800925a79c001000000000400000000080c042c0408000804000014000004040404000000100150494548714c83200544255431c1410c40141596153765043100541648541c9410c4a550494594725043100541255641c9410c40150598150725043129541e58541c9410c40150596150725043100541a40541c9410c4a5904841c952504312964121472d09410c401904851c942504310074015072dc1410c40151290150705043100544a57741c1410c40151297150705043100740153721c1410c401d00541c8705043128d44251651c1410c40151295e10705043100544255641c1410c40151298150705043128d44e58541c1410c40151196150705043100544648541c1410c4a351094548705043128d44257421c1410c4015109550870504310068415280d9031c848502c9760850590210044965c8454831084012909061d640c4210058164a755903108401a0485209640c421005816485059031084a130494616720c421004852616454831084a13049461d520c421004d024187548310840130597211520c421004c1a408454831084a1304989d1520c4210058165a745483108401304985d1520c421284c126264548310840130498591520c421296811518610831084a130494614420c42128541251750c721084a5a0664209410c65028e84990805043194001a0665209410c6400068199682d843190001a1265a03610c64000581e59520c421900a5a0454209610c440296811948250431100a5a0465209610c4402140b2617654821100a1604965483108440007015d9520c4211000182474205625483000518245621c1520c0a160694d9431086200049224182150634800126090608541852000505251651c5630800144592a147158c2000524241841c56308001845821c45058c20006051d08158d52080a16049459431084200068115282d903184001a0484989520c610006812126354821840a3c10545d8311001028f041d5760c440040019118761431100102754425d520c440040a9520975482110010
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x10008142204a86485059031084a11025432d3a2a418842509012a5765483108440
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x6
  | 2 => 0x4e
  | 3 => 0x124e
  | 4 => 0x138e
  | 5 => 0x4
  | 6 => 0x5
  | 7 => 0x94e
  | 8 => 0x8e
  | 9 => 0x128e
  | 10 => 0x150e
  | 11 => 0x98e
  | 12 => 0xce
  | 13 => 0x12ce
  | 14 => 0x9ce
  | 15 => 0x168e
  | 16 => 0x10e
  | 17 => 0x130e
  | 18 => 0xa0e
  | 19 => 0x180e
  | 20 => 0x20e
  | 21 => 0x140e
  | 22 => 0x154e
  | 23 => 0xb0e
  | 24 => 0x24e
  | 25 => 0x144e
  | 26 => 0xb4e
  | 27 => 0x16ce
  | 28 => 0x28e
  | 29 => 0x148e
  | 30 => 0xb8e
  | 31 => 0x184e
  | 32 => 0x3ce
  | 33 => 0x15ce
  | 34 => 0xcce
  | 35 => 0x170e
  | 36 => 0x40e
  | 37 => 0x160e
  | 38 => 0xd0e
  | 39 => 0x188e
  | 40 => 0x58e
  | 41 => 0xe8e
  | 42 => 0x178e
  | 43 => 0x18ce
  | 44 => 0x11396
  | 45 => 0x10056
  | 46 => 0x4d
  | 47 => 0x4116
  | 48 => 0x24056
  | 49 => 0x25256
  | 50 => 0x4256
  | 51 => 0x138d
  | 52 => 0x98096
  | 53 => 0x8996
  | 54 => 0x130116
  | 55 => 0x24116
  | 56 => 0x25316
  | 57 => 0x11456
  | 58 => 0x24d
  | 59 => 0x144116
  | 60 => 0x145316
  | 61 => 0x10256
  | 62 => 0x144d
  | 63 => 0x24216
  | 64 => 0x25556
  | 65 => 0x20256
  | 66 => 0x20d
  | 67 => 0x140d
  | 68 => 0x25496
  | 69 => 0xb8256
  | 70 => 0x148256
  | 71 => 0x24b96
  | 72 => 0x144256
  | 73 => 0x160256
  | 74 => 0xb9456
  | 75 => 0x161456
  | 76 => 0xb96d6
  | 77 => 0x241005e
  | 78 => 0x24055
  | 79 => 0x100425e
  | 80 => 0x24215
  | 81 => 0x4255
  | 82 => 0x20255
  | 83 => 0x41416
  | 84 => 0x20055
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 70
  | 6 => 1509
  | 5 => 2408
  | 4 => 473
  | 3 => 81
  | 2 => 3
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
  | 7 => packedAt gbK7 (1981+((h/23+packedAt gbK7 (1820+(h % 23)*7) 7) % 85)*8) 8
  | 6 => packedAt gbK6 (61869+((h/503+packedAt gbK6 (55833+(h % 503)*12) 12) % 2410)*12) 12
  | 5 => packedAt gbK5 (126010+((h/802+packedAt gbK5 (115584+(h % 802)*13) 13) % 4229)*13) 13
  | 4 => packedAt gbK4 (29477+((h/157+packedAt gbK4 (27907+(h % 157)*10) 10) % 686)*10) 10
  | 3 => packedAt gbK3 (5886+((h/27+packedAt gbK3 (5670+(h % 27)*8) 8) % 154)*8) 8
  | 2 => packedAt gbK2 (246+((h/1+packedAt gbK2 (243+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7ffffe00fffffffffe007ffff1fffe3f1ffe3f
  | 1 => 0xffffffff00fffc00fffffffffe44e3ffe3e3ff
  | 2 => 0x807fffffff01ffffffff801fff8703c7fc7fc7
  | 3 => 0xff807ffffffe0000ffffffe00ff803f8ff83f8
  | 4 => 0x7fffffffffff000000000ffffc00fffc00
  | 5 => 0xffff800000000000000000000fffffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x25a596004b162d559604372d90996e1b0dae1b
  | 1 => 0xcacaaccb00ab54302ad8da572644e0ed62e0ed
  | 2 => 0xa0734b55d5019ba6cd6d011acb870346b45746
  | 3 => 0x732073a6e6cc00c4f1b66d808df803b0df03b0
  | 4 => 0x40407df8b8f1e2f800380e030f6eb400fbf800
  | 5 => 0x7c7c01c0c081030081c0701c0ff7dbff000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xeaaac880e8a0c880eaaac880e8a0c880eaaac880e8a0c880eaaac880e8a0c880eaaac880e8a0c880eaaac880e8a0c880eaaac880e8a0c880eaaac880e8a0c880, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_15309
namespace PEqualNP.Outside.L_meta_15309
open PEqualNP.Outside.L_meta_15309.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_1_0 : Interval s0Atlas 1 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_1 : Interval s0Atlas 1 0 1 := bs0_1_0
theorem alls0 : ∀ k ≤ 1, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_1 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 1 := bs1_2_0
theorem alls1 : ∀ k ≤ 2, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
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
theorem bs4_2_0 : Interval s4Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 3 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 6 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1 := bs4_4_0
theorem alls4 : ∀ k ≤ 4, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 9 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 50 := (concat bs5_3_0 bs5_3_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_32 : Interval s5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_64 : Interval s5Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_96 : Interval s5Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_128 : Interval s5Atlas 4 128 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 136 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 48 := (concat bs5_5_0 bs5_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1 := bs5_6_0
theorem alls5 : ∀ k ≤ 6, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_2 i (by omega) hi
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 3 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_64 : Interval gbAtlas 3 64 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 81 := (concat bgb_3_0 (concat bgb_3_32 bgb_3_64))
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
theorem bgb_4_448 : Interval gbAtlas 4 448 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 473 := (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat (concat bgb_4_224 bgb_4_256) (concat bgb_4_288 bgb_4_320)) (concat (concat bgb_4_352 bgb_4_384) (concat bgb_4_416 bgb_4_448))))
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
theorem bgb_5_2400 : Interval gbAtlas 5 2400 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2408 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 (concat bgb_5_384 bgb_5_416))) (concat (concat bgb_5_448 bgb_5_480) (concat bgb_5_512 (concat bgb_5_544 bgb_5_576))))) (concat (concat (concat (concat bgb_5_608 bgb_5_640) (concat bgb_5_672 bgb_5_704)) (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 (concat bgb_5_832 bgb_5_864)))) (concat (concat (concat bgb_5_896 bgb_5_928) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024))) (concat (concat bgb_5_1056 bgb_5_1088) (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)))))) (concat (concat (concat (concat (concat bgb_5_1216 bgb_5_1248) (concat bgb_5_1280 bgb_5_1312)) (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472)))) (concat (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632))) (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 (concat bgb_5_1760 bgb_5_1792))))) (concat (concat (concat (concat bgb_5_1824 bgb_5_1856) (concat bgb_5_1888 bgb_5_1920)) (concat (concat bgb_5_1952 bgb_5_1984) (concat bgb_5_2016 (concat bgb_5_2048 bgb_5_2080)))) (concat (concat (concat bgb_5_2112 bgb_5_2144) (concat bgb_5_2176 (concat bgb_5_2208 bgb_5_2240))) (concat (concat bgb_5_2272 bgb_5_2304) (concat bgb_5_2336 (concat bgb_5_2368 bgb_5_2400)))))))
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
theorem bgb_6_1504 : Interval gbAtlas 6 1504 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1509 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat bgb_6_672 (concat bgb_6_704 bgb_6_736))))) (concat (concat (concat (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928))) (concat (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)))) (concat (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312))) (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat bgb_6_1440 (concat bgb_6_1472 bgb_6_1504))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 70 := (concat bgb_7_0 (concat bgb_7_32 bgb_7_64))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 2 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 3 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 2 zero, 17, 21),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 4 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeaaac880e8a0c880eaaac880e8a0c880eaaac880e8a0c880eaaac880e8a0c880eaaac880e8a0c880eaaac880e8a0c880eaaac880e8a0c880eaaac880e8a0c880
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 9 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 49 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 10 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) (SBf 3) :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have s4 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 4 zero)) (SBf 4) :=
    slice_correct (ms:=fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have s5 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 5 zero)) (SBf 5) :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have allCuts : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val) := by
    intro v
    fin_cases v
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
  have low := boundgb certgb allCuts
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3937060992 * 2 ^ 32 + 3902851200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
theorem binaryLower (low : Lower true fullRoots fullWord 9)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 9 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval6 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_15309.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,3]⟩,⟨.or,[0,2]⟩,⟨.and,[6,7]⟩,⟨.or,[2,3]⟩,⟨.or,[2,5]⟩,⟨.and,[0,4]⟩,⟨.and,[8,9]⟩,⟨.and,[1,12]⟩,⟨.and,[10,11]⟩,⟨.or,[13,14]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,15⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 9) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3937060992 * 2 ^ 32 + 3902851200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3937060992 * 2 ^ 32 + 3902851200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
    refine ⟨⟨mono, 15⟩, monoShape, ?_, fun x => monoEval x⟩
    change mono.length ≤ s
    have hm : mono.length = 10 := rfl
    change gs.length ≤ s at hsize
    omega
end PEqualNP.Outside.L_meta_15309

open PEqualNP.Outside.L_meta_15309 in
theorem PEqualNP.Outside.L_meta_15309 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3937060992 * 2 ^ 32 + 3902851200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3937060992 * 2 ^ 32 + 3902851200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
