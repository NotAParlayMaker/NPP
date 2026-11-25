import Mathlib
import PEqualNP.Defs

-- The signed circuit and cofactor lemmas follow L_meta_10802, L_meta_1674, and L_meta_670.
-- The live circuit search in those files follows L_meta_1667, Apache-2.0.
namespace PEqualNP.Outside.L_meta_10648
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 128
def zero : Sig := 0
def one : Sig := BitVec.allOnes 128
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

def bit (i : Fin 128) (a : Sig) : Bool := a.getLsbD i.val
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
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

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

private lemma extract {u target} (gs : List Gate) (w : List Sig)
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


abbrev Row := Fin 128
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


def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩


def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000]
def vars (m : Nat) : List Sig :=
  (List.range 7).filterMap fun i => if m.testBit i then some (inputs.getD i zero) else none

def vertex (m i : Nat) : Sig := if m.testBit i then inputs.getD i zero else zero

def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) |||
    (x 1 &&& x 6) ||| (x 3 &&& x 6) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) |||
    (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 4 &&& x 5)

def graph : Sig := graphGoal 127

theorem graph_proper : proper graph := by
  unfold proper
  decide +kernel

def target (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

def smallCircuit : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [7, 8]⟩,
    ⟨.and, [0, 2]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [11, 12]⟩,
    ⟨.or, [1, 3]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [14, 15]⟩,
    ⟨.and, [1, 3]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [13, 18]⟩], 19⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl, by decide⟩ | exact ⟨Or.inr rfl, by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 7 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 13 := rfl

theorem noNotReuse {gates : List Gate} (fit : ∀ g ∈ gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (h : ∀ g ∈ gates, g.op ≠ GateOp.not) :
    ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨ops,arity⟩ := fit g hg
  refine ⟨?_,arity⟩
  rcases ops with a | b | c
  · exact Or.inl a
  · exact Or.inr b
  · exact (h g hg c).elim


def sevenInputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc,
  0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00,
  0xffff0000ffff0000ffff0000ffff0000, 0xffffffffffffffff0000000000000000,
  0xffffffff00000000ffffffff00000000]
def sampleSeven (r : Row) (i : Fin 7) : Bool := bit r (sevenInputs.getD i.val zero)
theorem sevenList : List.ofFn (fun i : Fin 7 => sevenInputs.getD i.val zero) = sevenInputs := rfl
theorem sevenSampled (r : Row) : List.ofFn (sampleSeven r) = sevenInputs.map (bit r) := by
  rw [←sevenList,List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem sevenTable : ∀ r : Row, bit r graph = target (sampleSeven r) := by decide +kernel

theorem sevenEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates sevenInputs).getD i zero) =
      (C.wires (List.ofFn (sampleSeven r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sevenSampled]
  rfl

def lowRow (i : Fin 7) : Row := Fin.ofNat 128 (1 <<< ([2,3,0,1,0,1,0] : List Nat).getD i.val 0)
def highRow (i : Fin 7) : Row := Fin.ofNat 128 ((1 <<< ([0,1,2,3,4,6,5] : List Nat).getD i.val 0) ||| (1 <<< (lowRow i).val.log2))

set_option maxHeartbeats 1000000 in
theorem allSevenRequired :
    (∀ i : Fin 7, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 7, i ≠ j →
      bit (lowRow i) (sevenInputs.getD j.val zero) =
      bit (highRow i) (sevenInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k sevenInputs.toFinset := by
  have goalEq : (execute C.gates sevenInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (sevenEval C legal C.output r).trans ((computes (sampleSeven r)).trans (sevenTable r).symm)
  have out := get_rep (u:=true) (execute C.gates sevenInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates sevenInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : sevenInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ sevenInputs) : ∃ i : Fin 7, sevenInputs.getD i.val zero = a := by
    rw [←sevenList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = sevenInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run sevenInputs (sevenInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allSevenRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allSevenRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩

theorem replaceShort
    (lower : Impossible true graph 11 sevenInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 7 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 7 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 13 ≤ gates.length
  · exact ⟨smallCircuit.gates,smallCircuit.output,witnessMonotone,(by simpa only [witnessSize] using big),witnessCorrect⟩
  by_cases mono : ∀ g ∈ gates, g.op ≠ GateOp.not
  · exact ⟨gates,o,noNotReuse fit mono,Nat.le_refl _,correct⟩
  push Not at mono
  obtain ⟨g,hg,hop⟩ := mono
  have lt : gates.countP (fun q => !isNot q) < gates.length := by
    rcases Nat.lt_or_ge (gates.countP (fun q => !isNot q)) gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot,hop] at eq
  have legal : PEqualNP.MetaComplexity.FanInTwo (Circuit.mk gates o) := by
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using fit g hg
  obtain ⟨k,hk,run⟩ := physicalSigned (Circuit.mk gates o) legal correct
  change k ≤ gates.countP (fun q => !isNot q) at hk
  exact (lower k (by omega) run).elim


abbrev CutBank := Sig × Nat × Nat × List Sig

def initialCut (raw : List Sig) (desc : Sig × Nat) : CutBank :=
  (desc.1, desc.2, 0, raw)

def cutAvailable (c : CutBank) (a : Sig) : Bool :=
  let (d, _, _, pool) := c
  let m := masked d a
  m == zero || m == d || pool.any (fun b => masked d b == m)

theorem original_available {c : CutBank} {a : Sig} (h : cutAvailable c a = true) :
    availableB true c.1 c.2.2.2 a = true := by
  obtain ⟨d, l, p, bank⟩ := c
  simp only [cutAvailable, availableB, List.any_map, Function.comp_def] at h ⊢
  rw [h]
  rfl

def growBank (c : CutBank) (op : Choice) : CutBank :=
  if cutAvailable c (choiceVal op) then c else
    (c.1, c.2.1, c.2.2.1 + 1, choiceVal op :: c.2.2.2)

def enoughSaving (cap : Nat) (ws : List Sig) (c : CutBank) : Bool :=
  cap + c.2.2.1 < c.2.1 + ws.countP (isMaskedConstant c.1)

def BankSound (T : Sig) (c : CutBank) (ws : List Sig) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.1 = true) ∧ ¬ Constant (restrictRows f (observe T)) ∧
    (∀ q out, Reach true (roots.map observe) q out →
      Available true out (restrictRows f (observe T)) → c.2.1 ≤ q) ∧
    Reach true (roots.map observe) c.2.2.1 bank ∧
    poolSupply true f bank c.2.2.2 ∧ ∀ a ∈ ws, cutAvailable c a = true

theorem cutAvailable_mem (c : CutBank) (a : Sig) (h : a ∈ c.2.2.2) :
    cutAvailable c a = true := by
  unfold cutAvailable
  simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
  right
  exact ⟨a, h, rfl⟩

theorem cutAvailable_cons {a v : Sig} {d : Sig} {l p : Nat} {ws : List Sig}
    (h : cutAvailable (d,l,p,ws) a = true) :
    cutAvailable (d,l,p+1,v::ws) a = true := by
  simp only [cutAvailable, Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at h ⊢
  rcases h with h | ⟨b,hb,he⟩
  · exact Or.inl h
  · exact Or.inr ⟨b, by simp [hb], he⟩

theorem initial_sound {T d L raw} (h : Slice true raw T d L) :
    BankSound T (initialCut raw (d,L)) raw := by
  obtain ⟨f, roots, dom, sup, nc, lo⟩ := h
  exact ⟨f, roots, roots.map observe, dom, nc, lo, Reach.start, sup,
    fun a ha => cutAvailable_mem _ a ha⟩

theorem grow_sound {T c ws} (h : BankSound T c ws)
    {d : Nat} (hd : d < 4) {a b : Sig} (ha : a ∈ ws) (hb : b ∈ ws)
    {rest : List Sig} (hr : rest ⊆ ws) :
    BankSound T (growBank c (d,a,b)) (bin d a b :: rest) := by
  obtain ⟨delta,L,paid,pool⟩ := c
  obtain ⟨f, roots, bank, dom, nc, lo, reach, known, haveFront⟩ := h
  unfold growBank
  by_cases ex : cutAvailable (delta,L,paid,pool) (bin d a b) = true
  · simp only [choiceVal, ex, ite_true]
    exact ⟨f,roots,bank,dom,nc,lo,reach,known,fun v hv =>
      (List.mem_cons.mp hv).elim (fun e => e.symm ▸ ex)
        (fun hm => haveFront v (hr hm))⟩
  · have ok : choiceOK true delta pool (d,a,b) = true := by
      simp only [choiceOK, Bool.and_eq_true]
      exact ⟨by simp [allowedB, hd], original_available (haveFront a ha),
        original_available (haveFront b hb)⟩
    obtain ⟨next, kn, available⟩ := pay_choice dom reach known (d,a,b) ok
    simp only [choiceVal, ex, if_false]
    refine ⟨f, roots, next, dom, nc, lo, kn, available, ?_⟩
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hm
    · exact cutAvailable_mem _ _ (by simp)
    · exact cutAvailable_cons (haveFront _ (hr hm))

theorem saving_sound {T c ws cap} (h : BankSound T c ws) (nd : ws.Nodup)
    (ok : enoughSaving cap ws c = true) : Impossible true T cap ws.toFinset := by
  intro k hk run
  obtain ⟨f, roots, bank, dom, nc, lo, reach, known, haveFront⟩ := h
  have all : supply true bank ((ws.map observe).map (restrictRows f)) := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hv
    exact availableB_sound dom known (original_available (haveFront b hb))
  have b := projected_bound f (list_run run ws nd rfl) nc reach all lo
  have m := count_constants dom ws
  simp only [enoughSaving, decide_eq_true_eq] at ok
  omega

abbrev Decor (w : Nat) := Sig × BitVec w × BitVec w

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn

theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]

def mark {n : Nat} (r s : Fin n → Row) (a : Sig) : Decor n := (a, ofRows r a, ofRows s a)

def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b

def dbin {n : Nat} (d : Nat) (x y : Decor n) : Decor n :=
  (bin d x.1 y.1, bv d x.2.1 y.2.1, bv d x.2.2 y.2.2)

theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin, ← ofRows_bit r a ⟨j,hj⟩, ← ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]

theorem dbin_mark {n : Nat} (r s : Fin n → Row) (d : Nat) (a b : Sig) :
    dbin d (mark r s a) (mark r s b) = mark r s (bin d a b) := by
  simp [dbin, mark, ofRows_bin]

def coverage {n : Nat} : List (Decor n) → BitVec n
  | [] => 0
  | a :: ws => (a.2.1 ^^^ a.2.2) ||| coverage ws

theorem coverage_correct {n : Nat} (r s : Fin n → Row) (ws : List Sig) :
    coverage (ws.map (mark r s)) = covered false (fun a => (ofRows r a, ofRows s a)) ws := by
  induction ws with
  | nil => rfl
  | cons a ws ih => simp [coverage, covered, column, mark, ih]

def allPairs {α : Type} : List α → List (α × α)
  | [] => []
  | a :: rest => rest.map (fun b => (a,b)) ++ allPairs rest

theorem mem_allPairs {α : Type} {a b : α} {ws : List α}
    (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    (a,b) ∈ allPairs ws ∨ (b,a) ∈ allPairs ws := by
  induction ws with
  | nil => simp at ha
  | cons c ws ih =>
    rcases List.mem_cons.mp ha with e | ha'
    · subst c
      have h := (List.mem_cons.mp hb).resolve_left (Ne.symm hne)
      exact Or.inl (List.mem_append_left _ (List.mem_map.mpr ⟨b,h,rfl⟩))
    · rcases List.mem_cons.mp hb with e | hb'
      · subst c
        exact Or.inr (List.mem_append_left _ (List.mem_map.mpr ⟨a,ha',rfl⟩))
      · exact (ih ha' hb').imp (List.mem_append_right _) (List.mem_append_right _)

def remaining {n : Nat} (ws : List (Decor n)) (a b : Sig) (ka kb : Bool) : List (Decor n) :=
  ws.filter (fun w => (ka || w.1 != a) && (kb || w.1 != b))

theorem remaining_sub {n : Nat} (ws : List (Decor n)) (a b : Sig) (ka kb : Bool) :
    ((remaining ws a b ka kb).map Prod.fst).Sublist (ws.map Prod.fst) :=
  List.filter_sublist.map _

theorem remaining_set {n : Nat} (ws : List (Decor n)) {a b : Sig} (ka kb : Bool)
    (nd : (ws.map Prod.fst).Nodup) (ne : a ≠ b) (ha : a ∈ ws.map Prod.fst)
    (hb : b ∈ ws.map Prod.fst) :
    ((remaining ws a b ka kb).map Prod.fst).toFinset =
      (kept ka a (kept kb b (((ws.map Prod.fst).erase a).erase b))).toFinset := by
  ext v
  have e : v ∈ (remaining ws a b ka kb).map Prod.fst ↔
      v ∈ ws.map Prod.fst ∧ (ka = true ∨ v ≠ a) ∧ (kb = true ∨ v ≠ b) := by
    simp only [remaining, List.mem_map, List.mem_filter, Bool.and_eq_true, Bool.or_eq_true,
      bne_iff_ne]
    constructor
    · rintro ⟨w,⟨hw,hwa,hwb⟩,rfl⟩
      exact ⟨⟨w,hw,rfl⟩,hwa,hwb⟩
    · rintro ⟨⟨w,hw,rfl⟩,hwa,hwb⟩
      exact ⟨w,⟨hw,hwa,hwb⟩,rfl⟩
  have ers := ((nd.erase a).mem_erase_iff (a := v) (b := b))
  have ero := (nd.mem_erase_iff (a := v) (b := a))
  cases ka <;> cases kb <;> simp [List.mem_toFinset,e,kept,ers,ero] <;> grind

def moves {n : Nat} (ws : List (Decor n)) : List (Decor n × Decor n × Nat × Bool × Bool) :=
  (allPairs ws).flatMap fun (a,b) =>
    [0,1,2,3].flatMap fun d => [(a,b,d,false,false),(a,b,d,true,false),
      (a,b,d,false,true),(a,b,d,true,true)]

theorem mem_moves {n : Nat} {ws : List (Decor n)} {a b : Decor n} {d : Nat}
    (p : (a,b) ∈ allPairs ws) (hd : d < 4) (ka kb : Bool) :
    (a,b,d,ka,kb) ∈ moves ws := by
  unfold moves
  apply List.mem_flatMap.mpr
  refine ⟨(a,b),p,List.mem_flatMap.mpr ⟨d,?_,?_⟩⟩
  · interval_cases d <;> simp
  · cases ka <;> cases kb <;> simp

theorem map_mark_fst {n : Nat} (r s : Fin n → Row) (ws : List Sig) :
    (ws.map (mark r s)).map Prod.fst = ws := by
  induction ws with
  | nil => rfl
  | cons x ws ih => simp only [List.map_cons, mark, ih]

theorem remaining_mark {n : Nat} (r s : Fin n → Row) (ws : List Sig)
    (a b : Sig) (ka kb : Bool) :
    let rest := remaining (ws.map (mark r s)) a b ka kb
    rest = (rest.map Prod.fst).map (mark r s) := by
  dsimp only
  simp only [remaining, List.filter_map, map_mark_fst]

noncomputable def forceNat {β : Type} (n : Nat) (f : Nat → β) : β :=
  Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n

theorem forceNat_eq {β : Type} (n : Nat) (f : Nat → β) : forceNat n f = f n := by
  cases n <;> rfl

noncomputable def withWord {w : Nat} {β : Type} (a : BitVec w) (f : BitVec w → β) : β :=
  forceNat a.toNat (fun n => f (BitVec.ofNat w n))

theorem withWord_eq {w : Nat} {β : Type} (a : BitVec w) (f : BitVec w → β) :
    withWord a f = f a := by
  simp [withWord, forceNat_eq]

noncomputable def withDecor {n : Nat} {β : Type} (a : Decor n) (f : Decor n → β) : β :=
  withWord a.1 fun u => withWord a.2.1 fun v => withWord a.2.2 fun w => f (u,v,w)

theorem withDecor_eq {n : Nat} {β : Type} (a : Decor n) (f : Decor n → β) :
    withDecor a f = f a := by
  obtain ⟨a,b,c⟩ := a
  simp only [withDecor, withWord_eq]

def addValue (c : CutBank) (z : Sig) : CutBank :=
  if cutAvailable c z then c else (c.1, c.2.1, c.2.2.1 + 1, z :: c.2.2.2)

noncomputable def verify {n : Nat} (T : Sig) (link : Nat → List Sig → Bool) (floor : Nat) :
    Nat → List CutBank → List (Decor n) → Bool
  | k, cuts, ws =>
    let raw := ws.map Prod.fst
    if ws.length > k+1 then true else
    if coverage ws != BitVec.allOnes n then true else
    if cuts.any (enoughSaving k raw) then true else
    if link k raw then true else
    if k < floor then false else
    if raw.contains T then false else
    match k with
    | 0 => true
    | r+1 => (moves ws).all fun (a,b,d,ka,kb) =>
      withDecor (dbin d a b) fun z =>
        if z.1 == zero || z.1 == one || raw.contains z.1 then true else
        let rest := remaining ws a.1 b.1 ka kb
        let cols := cuts.map (fun c => addValue c z.1)
        verify T link floor r cols (z :: rest)

noncomputable def certify {n : Nat} (T : Sig) : Nat → List CutBank → List (Decor n) → Bool :=
  verify T (fun _ _ => false) 0

set_option maxHeartbeats 0 in
theorem verify_sound {n : Nat} {T : Sig} {r s : Fin n → Row}
    (sep : ∀ i : Fin n, bit (r i) T = true ∧ bit (s i) T = false)
    (link : Nat → List Sig → Bool) (floor : Nat)
    (linkOk : ∀ k ws, link k ws = true → Impossible true T k ws.toFinset)
    (cap : Nat) (cuts : List CutBank) (ws : List Sig) (nd : ws.Nodup)
    (valid : ∀ c ∈ cuts, BankSound T c ws)
    (check : verify T link floor cap cuts (ws.map (mark r s)) = true) :
    Impossible true T cap ws.toFinset := by
  induction cap generalizing ws cuts with
  | zero =>
    unfold verify at check
    simp only [map_mark_fst, List.length_map] at check
    split at check
    · rename_i big
      intro k hk run
      have b := live_size run
      rw [List.toFinset_card_of_nodup nd] at b
      omega
    split at check
    · rename_i fail
      intro k hk run
      have b := cover_required run (show Sep T n r s (fun a => (ofRows r a,ofRows s a))
        from ⟨sep,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩)
      exact (bne_iff_ne.mp fail) ((coverage_correct r s ws).trans b)
    split at check
    · rename_i saved
      obtain ⟨c,hc,hcut⟩ := List.any_eq_true.mp saved
      exact saving_sound (valid _ hc) nd hcut
    split at check
    · rename_i closed
      exact linkOk _ _ closed
    split at check
    · contradiction
    split at check
    · contradiction
    · rename_i absent
      intro k hk run
      have e : k=0 := by omega
      subst e
      exact absent (by simp [← List.mem_toFinset, run.1])
  | succ cap ih =>
    unfold verify at check
    simp only [map_mark_fst, List.length_map] at check
    split at check
    · rename_i big
      intro k hk run
      have b := live_size run
      rw [List.toFinset_card_of_nodup nd] at b
      omega
    split at check
    · rename_i fail
      intro k hk run
      have b := cover_required run (show Sep T n r s (fun a => (ofRows r a,ofRows s a))
        from ⟨sep,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩)
      exact (bne_iff_ne.mp fail) ((coverage_correct r s ws).trans b)
    split at check
    · rename_i saved
      obtain ⟨c,hc,hcut⟩ := List.any_eq_true.mp saved
      exact saving_sound (valid _ hc) nd hcut
    split at check
    · rename_i closed
      exact linkOk _ _ closed
    split at check
    · contradiction
    split at check
    · contradiction
    rename_i noGoal
    apply enum_step nd (by simpa using noGoal)
    intro a ha b hb d hd ka kb ne fresh pro len
    let va := mark r s a
    let vb := mark r s b
    let input := ws.map (mark r s)
    have fa : va ∈ input := List.mem_map_of_mem ha
    have fb : vb ∈ input := List.mem_map_of_mem hb
    have hne : va ≠ vb := fun e => ne (congrArg Prod.fst e)
    have hm : input.map Prod.fst = ws := map_mark_fst r s ws
    have consume (a b : Sig) (ha : a ∈ ws) (hb : b ∈ ws)
        (d : Nat) (hd : d < 4) (ka kb : Bool) (ne : a ≠ b)
        (fresh : bin d a b ∉ ws) (pro : proper (bin d a b))
        (step : (mark r s a,mark r s b,d,ka,kb) ∈ moves input) :
        Impossible true T cap (childTwo ws a b d ka kb).toFinset := by
      let rest := remaining input a b ka kb
      let raw := rest.map Prod.fst
      have hrs : raw.Sublist ws := by rw [← hm]; exact remaining_sub input a b ka kb
      let next := bin d a b :: raw
      have nnd : next.Nodup := List.nodup_cons.mpr ⟨fun hh => fresh (hrs.subset hh), nd.sublist hrs⟩
      let cols := cuts.map (fun c => growBank c (d,a,b))
      have nv : ∀ c ∈ cols, BankSound T c next := by
        intro c hc
        obtain ⟨old,oldmem,rfl⟩ := List.mem_map.mp hc
        exact grow_sound (valid _ oldmem) hd ha hb hrs.subset
      have nextMarked : rest = raw.map (mark r s) := remaining_mark r s ws a b ka kb
      have stepCheck := List.all_eq_true.mp check _ step
      simp only [withDecor_eq] at stepCheck
      change (if bin d a b == zero || bin d a b == one || ws.contains (bin d a b)
        then true else verify T link floor cap cols (dbin d (mark r s a) (mark r s b) :: rest)) = true at stepCheck
      have absent : ws.contains (bin d a b) = false := by simpa using fresh
      have h0 : (bin d a b == zero) = false := Bool.eq_false_iff.mpr (by simpa using pro.1)
      have h1 : (bin d a b == one) = false := Bool.eq_false_iff.mpr (by simpa using pro.2)
      simp only [h0, h1, Bool.false_or, absent, Bool.false_eq_true, ite_false, dbin_mark,
        nextMarked] at stepCheck
      have eq : next.toFinset = (childTwo ws a b d ka kb).toFinset := by
        have ht := remaining_set input ka kb (hm.symm ▸ nd) ne (hm.symm ▸ ha) (hm.symm ▸ hb)
        simp only [hm] at ht
        simp only [next, childTwo, List.toFinset_cons]
        congr 1
      rw [← eq]
      apply ih cols next nnd nv
      exact stepCheck
    have hfour : d < 4 := by rcases hd with hd | ⟨_,hd⟩ <;> omega
    rcases mem_allPairs fa fb hne with first | second
    · exact consume a b ha hb d hfour ka kb ne fresh pro (mem_moves first hfour ka kb)
    · have oflip := (flip_flip hd).1
      have f4 : flipOp d < 4 := by rcases oflip with h | ⟨_,h⟩ <;> omega
      have hz := bin_flip hd a b
      have h := consume b a hb ha (flipOp d) f4 kb ka (Ne.symm ne)
        (hz ▸ fresh) (hz ▸ pro) (mem_moves second f4 kb ka)
      have eq : (childTwo ws a b d ka kb).toFinset =
          (childTwo ws b a (flipOp d) kb ka).toFinset := by
        simp only [childTwo, ← hz, List.toFinset_cons, kept_fin, erase_fin (nd.erase _), erase_fin nd]
        rw [Finset.erase_right_comm]
        ext x
        cases ka <;> cases kb <;> simp <;> tauto
      exact eq.symm ▸ h


theorem certify_sound {n : Nat} {T : Sig} {r s : Fin n → Row}
    (sep : ∀ i : Fin n, bit (r i) T = true ∧ bit (s i) T = false)
    (cap : Nat) (cuts : List CutBank) (ws : List Sig) (nd : ws.Nodup)
    (valid : ∀ c ∈ cuts, BankSound T c ws)
    (check : certify T cap cuts (ws.map (mark r s)) = true) :
    Impossible true T cap ws.toFinset :=
  verify_sound sep _ 0 (fun _ _ h => Bool.noConfusion h) cap cuts ws nd valid check

def domain (m : Nat) : Sig :=
  (vars (127 ^^^ m)).foldl (fun x a => x &&& ~~~a) one

def rowProject (m : Nat) (r : Row) : Row := Fin.ofNat 128 (r.val &&& m)

def sliceCheck (raw m : Nat) : Bool :=
  let f := rowProject m
  (rename f (graphGoal raw) == graphGoal m) &&
    decide (∀ r : Row, bit (f r) (domain m) = true) &&
    (vars raw).all (fun a => freeWord (vars m) (rename f a)) &&
    (graphGoal m != zero && graphGoal m != one)

theorem build_slice {raw m L} (h : sliceCheck raw m = true)
    (lo : Lower true (vars m) (graphGoal m) L) :
    Slice true (vars raw) (graphGoal raw) (domain m) L := by
  simp only [sliceCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    bne_iff_ne, List.all_eq_true] at h
  obtain ⟨⟨⟨targetEq,dom⟩,inputs⟩,properG⟩ := h
  let f := rowProject m
  have eq : restrictRows f (observe (graphGoal raw)) = observe (graphGoal m) :=
    (observe_rename _ _).symm.trans (congrArg observe targetEq)
  refine ⟨f, vars m, dom, fun a ha => ?_, eq ▸ observe_proper properG, eq ▸ lo⟩
  rw [← observe_rename]
  exact freeWord_ok (inputs _ ha)

def graphEdges : List (Nat × Nat) :=
  [(0,2),(1,3),(0,4),(2,4),(1,6),(3,6),(0,5),(1,5),(2,5),(3,5),(4,5)]

def companion (m i : Nat) : Nat :=
  ((List.range 7).find? fun j =>
    m.testBit j && (graphEdges.contains (i,j) || graphEdges.contains (j,i))).getD 0

def essentialEntry (m i : Nat) : Sig × Row × Row :=
  let low := 1 <<< companion m i
  (inputs.getD i zero, Fin.ofNat 128 (low ||| (1 <<< i)), Fin.ofNat 128 low)

def essentialEntries (m : Nat) : List (Sig × Row × Row) :=
  ((List.range 7).filter (fun i => m.testBit i)).map (essentialEntry m)

def supportCheck (m : Nat) : Bool :=
  let es := essentialEntries m
  es.map Prod.fst == vars m &&
    es.all (fun a => witnessB (graphGoal m) (vars m) a.1 a.2)

theorem support_ok {m} (ok : supportCheck m = true) :
    ∀ a ∈ vars m, Essential (graphGoal m) (vars m) a := by
  simp only [supportCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  intro a ha
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp (ok.1 ▸ ha)
  exact witnessB_sound (ok.2 _ hv)

theorem countLower {m} (p : proper (graphGoal m)) (t : plainWord (graphGoal m) = true)
    (r : (vars m).all plainWord = true) (ok : supportCheck m = true) :
    Lower true (vars m) (graphGoal m) ((vars m).toFinset.card - 1) := by
  intro k bank run out
  obtain ⟨i,S,le,h,sub⟩ := reach_live p t r run out
  have inc : (vars m).toFinset ⊆ S := by
    intro a ha
    obtain ⟨x,y,hd,hs⟩ := support_ok ok _ (List.mem_toFinset.mp ha)
    exact raw_required h (vars m) a sub x y hd hs
  have n := Finset.card_le_card inc
  have l := live_size h
  omega

def trimCheck (raw m : Nat) (singles : List Sig) : Bool :=
  sliceCheck raw m &&
    singles.all (fun a => ((vars raw).contains a && isMaskedConstant (domain m) a))

theorem trimLower {raw m L singles} (has : supportCheck raw = true)
    (check : trimCheck raw m singles = true) (hp : proper (graphGoal raw))
    (hn : plainWord (graphGoal raw) = true) (hr : (vars raw).all plainWord = true)
    (hg : proper (graphGoal m)) (lower : Lower true (vars m) (graphGoal m) L) :
    Lower true (vars raw) (graphGoal raw) (L+singles.toFinset.card) := by
  simp only [trimCheck, Bool.and_eq_true, List.all_eq_true, List.contains_eq_mem,
    decide_eq_true_eq] at check
  simp only [sliceCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    bne_iff_ne, List.all_eq_true] at check
  obtain ⟨⟨⟨outEq,dom⟩,rootEq⟩,properG⟩ := check.1
  apply lower_slice hp hn hr hg (rowProject m) outEq _
    singles.toFinset (L:=L) _ _ lower
  · intro a ha
    exact freeWord_ok (rootEq a ha)
  · intro a ha
    exact support_ok has a (check.2 a (List.mem_toFinset.mp ha)).1
  · intro a ha
    obtain hz | ho := by
      simpa only [isMaskedConstant, Bool.or_eq_true, beq_iff_eq] using
        (check.2 a (List.mem_toFinset.mp ha)).2
    all_goals rw [observe_rename]
    · exact ⟨false, masked_zero dom hz⟩
    · exact ⟨true, masked_one dom ho⟩

theorem unusedLower {raw m L} (h : sliceCheck raw m = true)
    (hp : proper (graphGoal raw))
    (hn : plainWord (graphGoal raw) = true) (hr : (vars raw).all plainWord = true)
    (hg : proper (graphGoal m)) (lower : Lower true (vars m) (graphGoal m) L) :
    Lower true (vars raw) (graphGoal raw) L := by
  simp only [sliceCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne,
    List.all_eq_true] at h
  obtain ⟨⟨⟨outEq,dom⟩,rootEq⟩,properG⟩ := h
  simpa using lower_slice hp hn hr hg (rowProject m) outEq
    (fun a ha => freeWord_ok (rootEq a ha))
    ∅ (by simp) (by simp) L lower

def initialCuts (m : Nat) (bs : List (Nat × Nat)) : List CutBank :=
  bs.map (fun (inner, L) => initialCut (vars m) (domain inner,L))

theorem initialCuts_sound {m bs} (hc : bs.all (fun p => sliceCheck m p.1) = true)
    (hl : ∀ p ∈ bs, Lower true (vars p.1) (graphGoal p.1) p.2) :
    ∀ c ∈ initialCuts m bs, BankSound (graphGoal m) c (vars m) := by
  intro c hc'
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hc'
  exact initial_sound (build_slice (List.all_eq_true.mp hc p hp) (hl p hp))

theorem exactFromCert {m cap n : Nat} {r s : Fin n → Row} {bs : List (Nat × Nat)}
    (p : proper (graphGoal m)) (t : plainWord (graphGoal m) = true)
    (pr : (vars m).all plainWord = true) (ess : supportCheck m = true)
    (sep : ∀ i : Fin n, bit (r i) (graphGoal m) = true ∧ bit (s i) (graphGoal m) = false)
    (nd : (vars m).Nodup) (hc : bs.all (fun p => sliceCheck m p.1) = true)
    (hl : ∀ p ∈ bs, Lower true (vars p.1) (graphGoal p.1) p.2)
    (chk : certify (graphGoal m) cap (initialCuts m bs) ((vars m).map (mark r s)) = true) :
    Lower true (vars m) (graphGoal m) (cap+1) :=
  lower_impossible p t pr (support_ok ess)
    (certify_sound sep cap (initialCuts m bs) (vars m) nd (initialCuts_sound hc hl) chk)

abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 128-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(128-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 128 (128-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 128-d.val <;> simp [shifted,h,r.isLt]

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

def swapMove (a b : Nat) : Move :=
  let x := inputs.getD a zero
  let y := inputs.getD b zero
  (x &&& ~~~y, ~~~x &&& y, Fin.ofNat 128 ((1 <<< b) - (1 <<< a)))

def wordPerm (swaps : List (Nat × Nat)) (a : Sig) :=
  movedWord (swaps.map fun (i,j) => swapMove i j) a

def validPerm (T : Sig) (swaps : List (Nat × Nat)) : Bool :=
  let ms := swaps.map fun (i,j) => swapMove i j
  wordPerm swaps T == T &&
    decide (∀ i : Row, movedRow ms (movedRow ms.reverse i) = i)

theorem perm_excludes {T cap} {xs ys : List Sig} {swaps} (ok : validPerm T swaps = true)
    (eq : (xs.map (wordPerm swaps)).toFinset = ys.toFinset)
    (known : Impossible true T cap ys.toFinset) : Impossible true T cap xs.toFinset := by
  let ms := swaps.map fun (i,j) => swapMove i j
  simp only [validPerm, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
  have onto : Function.Surjective (movedRow ms) := fun r => ⟨movedRow ms.reverse r, ok.2 r⟩
  intro k hk run
  have h := live_rename run (movedRow ms) onto
  have targetEq : rename (movedRow ms) T = T :=
    (moved_eq_rename _ _).symm.trans ok.1
  have setEq : xs.toFinset.image (rename (movedRow ms)) = ys.toFinset := by
    rw [← eq]
    ext a
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_map, wordPerm, moved_eq_rename, ms]
  rw [targetEq,setEq] at h
  exact known k hk h

def selectFront {α : Type} (mask : Nat) : List α → List α
  | [] => []
  | a :: ws =>
    if mask.testBit 0 then a :: selectFront (mask >>> 1) ws else selectFront (mask >>> 1) ws

theorem selectFront_sub {α : Type} (m : Nat) (ws : List α) :
    (selectFront m ws).Sublist ws := by
  induction ws generalizing m with
  | nil => exact .slnil
  | cons a ws ih =>
    unfold selectFront
    split
    · exact .cons_cons _ (ih _)
    · exact .cons _ (ih _)

def gateCode (code : Nat) : Nat × Nat × Nat :=
  (code &&& 15, (code >>> 4) &&& 15, (code >>> 8) &&& 3)

noncomputable def replay {n : Nat} :
    Nat → Nat → List CutBank → List (Decor n) → List CutBank × List (Decor n)
  | 0, _, cs, ws => (cs, ws)
  | depth+1, code, cs, ws =>
    let (i,j,d) := gateCode code
    match ws[i]?, ws[j]? with
    | some a, some b =>
      withDecor (dbin d a b) fun z =>
        replay depth (code >>> 10) (cs.map (fun c => addValue c z.1)) (ws ++ [z])
    | _, _ => (cs,ws)

theorem decode_gate_mode (code : Nat) : (gateCode code).2.2 < 4 := by
  have h := Nat.and_lt_two_pow (x := code >>> 8) (n := 2) (y := 3) (by decide)
  exact h

theorem replay_sound {n : Nat} {T : Sig} {r s : Fin n → Row} (depth code : Nat)
    (xs : List Sig) (cs : List CutBank) (hc : ∀ c ∈ cs, BankSound T c xs) :
    let result := replay depth code cs (xs.map (mark r s))
    result.2 = (result.2.map Prod.fst).map (mark r s) ∧
      ∀ c ∈ result.1, BankSound T c (result.2.map Prod.fst) := by
  induction depth generalizing code xs cs with
  | zero => simpa only [replay, map_mark_fst, true_and] using hc
  | succ depth ih =>
    simp only [replay]
    revert hc
    generalize hg : gateCode code = gate
    obtain ⟨i,j,d⟩ := gate
    simp only
    cases h1 : xs[i]? <;> cases h2 : xs[j]? <;>
      simp only [List.getElem?_map, h1, h2, Option.map_some, Option.map_none]
    all_goals intro hc
    all_goals try (simpa only [map_mark_fst, true_and] using hc)
    rename_i a b
    rw [withDecor_eq,dbin_mark]
    simp only [← List.map_append, ← List.map_singleton]
    apply ih
    intro c hm
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hm
    have hd : d < 4 := by simpa [hg] using decode_gate_mode code
    have hgo := grow_sound (hc _ hq) hd (List.mem_of_getElem? h1) (List.mem_of_getElem? h2)
      (rest := xs) (fun _ h => h)
    obtain ⟨f,roots,bank,dom,nc,lo,reach,sup,liq⟩ := hgo
    refine ⟨f,roots,bank,dom,nc,lo,reach,sup,fun z hz => ?_⟩
    apply liq
    simpa only [List.mem_append,List.map_cons,List.map_nil,List.mem_singleton,List.mem_cons,
      List.not_mem_nil,false_or,or_comm] using hz

-- Each record gives a circuit prefix and selects its live wires.
-- The index proposes a row and a permutation. The checker compares the wire sets.
abbrev Certificates := (Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat) × (Nat → Nat → Nat) × List (List (Nat × Nat)) × (Nat → Nat → Nat)

def Certificates.count (c : Certificates) (k : Nat) := c.1 k
def Certificates.rows (c : Certificates) (k j : Nat) := c.2.1 k j
def Certificates.slots (c : Certificates) (k : Nat) := c.2.2.1 k
def Certificates.index (c : Certificates) (k j : Nat) := c.2.2.2.1 k j
def Certificates.perms (c : Certificates) := c.2.2.2.2.1
def Certificates.filters (c : Certificates) (k j : Nat) := c.2.2.2.2.2 k j

def unpack (width : Nat) (word : Nat → Nat) (i : Nat) : Nat :=
  (word (i / 64) >>> ((i % 64) * width)) &&& ((1 <<< width) - 1)

noncomputable def decodeNode {n : Nat} (C : Certificates) (top k i : Nat)
    (raw : List (Decor n)) (cuts : List CutBank) : List CutBank × List (Decor n) :=
  let data := unpack 128 (C.rows k) i
  let active := selectFront (unpack 64 (C.filters k) i) cuts
  let result := replay (top-k) (data >>> 16) active raw
  (result.1, selectFront (data &&& 65535) result.2)

theorem selectFront_map {α β : Type} (f : α → β) (m : Nat) (xs : List α) :
    selectFront m (xs.map f) = (selectFront m xs).map f := by
  induction xs generalizing m with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons, selectFront]
    split <;> simp only [List.map_cons, ih]

theorem decode_sound {n : Nat} {T : Sig} {r s : Fin n → Row}
    (C : Certificates) (top k i : Nat) (xs : List Sig) (cs : List CutBank)
    (hc : ∀ c ∈ cs, BankSound T c xs) :
    let result := decodeNode C top k i (xs.map (mark r s)) cs
    result.2 = (result.2.map Prod.fst).map (mark r s) ∧
      ∀ c ∈ result.1, BankSound T c (result.2.map Prod.fst) := by
  dsimp only [decodeNode]
  let data := unpack 128 (C.rows k) i
  let active := selectFront (unpack 64 (C.filters k) i) cs
  have valid : ∀ c ∈ active, BankSound T c xs :=
    fun c h => hc c ((selectFront_sub _ _).subset h)
  have hs := replay_sound (r:=r) (s:=s) (top-k) (data >>> 16) xs active valid
  generalize hq : replay (top-k) (data >>> 16) active (xs.map (mark r s)) = state at hs ⊢
  obtain ⟨faith,sound⟩ := hs
  constructor
  · calc
      _ = selectFront (data &&& 65535) ((state.2.map Prod.fst).map (mark r s)) :=
        congrArg (selectFront (data &&& 65535)) faith
      _ = _ := by simp only [selectFront_map]; rfl
  · intro c hc'
    obtain ⟨f,roots,bank,dom,nc,lo,reach,sup,front⟩ := sound c hc'
    refine ⟨f,roots,bank,dom,nc,lo,reach,sup,fun a ha => front a ?_⟩
    exact ((selectFront_sub (data &&& 65535) state.2).map Prod.fst).subset ha

noncomputable def frontWords {n : Nat} (C : Certificates) (top k i : Nat) (raw : List (Decor n)) :
    List Sig :=
  (decodeNode C top k i raw []).2.map Prod.fst

theorem replay_same {n} (depth code : Nat) (cs ds : List CutBank) (ws : List (Decor n)) :
    (replay depth code cs ws).2 = (replay depth code ds ws).2 := by
  induction depth generalizing code cs ds ws with
  | zero => rfl
  | succ depth ih =>
    simp only [replay]
    generalize he : gateCode code = gate
    obtain ⟨i,j,d⟩ := gate
    dsimp only
    cases h1 : ws[i]? <;> cases h2 : ws[j]? <;> simp only [h1,h2]
    all_goals try rfl
    simp only [withDecor_eq]
    exact ih _ _ _ _

theorem frontWords_decode {n} (C : Certificates) (top k i : Nat) (raw : List (Decor n))
    (cs : List CutBank) :
    frontWords C top k i raw = (decodeNode C top k i raw cs).2.map Prod.fst := by
  unfold frontWords decodeNode
  simp only
  rw [replay_same (ds:=selectFront (unpack 64 (C.filters k) i) cs)]

def keysAgree (as bs : List Sig) : Bool :=
  as.all bs.contains && bs.all as.contains

theorem keysAgree_ok {as bs : List Sig} (ok : keysAgree as bs = true) :
    as.toFinset = bs.toFinset := by
  simp only [keysAgree, Bool.and_eq_true, List.all_eq_true,List.contains_eq_mem,
    decide_eq_true_eq] at ok
  ext x
  simp only [List.mem_toFinset]
  exact ⟨ok.1 x,ok.2 x⟩

def hashSig (a : Sig) : Nat :=
  let p := (a.toNat &&& 18446744073709551615) % 2305843009213693951
  (p * (p + 971)) % 2305843009213693951

def hashFront (xs : List Sig) (width : Nat) : Nat := (xs.map hashSig).sum % width

noncomputable def probe {n : Nat} (C : Certificates) (top k : Nat) (raw : List (Decor n))
    (xs : List Sig) (offset : Nat) : Nat → Bool
  | 0 => false
  | gas+1 =>
    let entry := unpack 16 (C.index k) (offset % C.slots k)
    if entry == 0 then false else
    let pair := entry - 1
    let idx := pair / 32
    let sw := pair % 32
    let perm := C.perms.getD sw []
    if idx < C.count k && sw < C.perms.length &&
        keysAgree (xs.map (wordPerm perm)) (frontWords C top k idx raw)
    then true else
      probe C top k raw xs (offset+1) gas

theorem probe_sound {n : Nat} {T : Sig} {C : Certificates} {top k : Nat} {raw : List (Decor n)}
    (perms : ∀ p ∈ C.perms, validPerm T p = true)
    (prior : ∀ i < C.count k, Impossible true T k (frontWords C top k i raw).toFinset)
    (xs : List Sig) (offset gas : Nat)
    (ok : probe C top k raw xs offset gas = true) :
    Impossible true T k xs.toFinset := by
  induction gas generalizing offset with
  | zero => exact Bool.noConfusion ok
  | succ gas ih =>
    unfold probe at ok
    dsimp only at ok
    split at ok
    · exact Bool.noConfusion ok
    split at ok
    · rename_i ok'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ok'
      let e := unpack 16 (C.index k) (offset % C.slots k) - 1
      have ind : e / 32 < C.count k := ok'.1.1
      have sw : e % 32 < C.perms.length := ok'.1.2
      apply perm_excludes (known := prior _ ind) (eq := keysAgree_ok ok'.2)
      apply perms
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem sw]
      exact List.getElem_mem _
    · exact ih _ ok

noncomputable def betweenLayers {n : Nat} (C : Certificates) (top level : Nat)
    (raw : List (Decor n)) (k : Nat) (xs : List Sig) :=
  (k+1 == level) &&
    probe C top k raw xs (hashFront xs (C.slots k)) 64

noncomputable def testNode {n : Nat} (C : Certificates) (top level i : Nat)
    (T : Sig) (raw : List (Decor n)) (cs : List CutBank) : Bool :=
  let (cuts,ws) := decodeNode C top level i raw cs
  decide (ws.map Prod.fst).Nodup &&
    verify T (betweenLayers C top level raw) level level cuts ws

set_option maxHeartbeats 0 in
theorem checked_tables {n top : Nat} {C : Certificates} {T : Sig} {r s : Fin n → Row}
    {raw : List (Decor n)} {xs : List Sig} {cs : List CutBank}
    (marked : raw = xs.map (mark r s))
    (sep : ∀ i : Fin n, bit (r i) T = true ∧ bit (s i) T = false)
    (cutsOk : ∀ c ∈ cs, BankSound T c xs)
    (permsOk : C.perms.all (validPerm T) = true)
    (checked : ∀ k ≤ top, ∀ i < C.count k, testNode C top k i T raw cs = true) :
    ∀ k ≤ top, ∀ i < C.count k, Impossible true T k (frontWords C top k i raw).toFinset := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro le i hi
    have chk := checked k le i hi
    simp only [testNode,Bool.and_eq_true,decide_eq_true_eq] at chk
    rw [frontWords_decode (cs:=cs)]
    obtain ⟨hMark,hKnown⟩ := marked ▸ decode_sound C top k i xs cs cutsOk
    refine verify_sound sep (betweenLayers C top k raw) k ?_ k _ _ chk.1 hKnown ?_
    · intro o ws ok
      simp only [betweenLayers,Bool.and_eq_true,beq_iff_eq] at ok
      have before : o < k := by omega
      exact probe_sound (List.all_eq_true.mp permsOk)
        (ih o before (by omega)) _ _ _ ok.2
    · rw [← hMark]
      exact chk.2

noncomputable def testBlock {n : Nat} (C : Certificates) (top k start len : Nat)
    (T : Sig) (raw : List (Decor n)) (cs : List CutBank) : Bool :=
  ((List.range len).map (start + ·)).all (fun i => testNode C top k i T raw cs)

theorem testBlock_at {n top k start len : Nat} {C : Certificates} {T : Sig}
    {raw : List (Decor n)} {cs : List CutBank}
    (ok : testBlock C top k start len T raw cs = true) (i : Nat)
    (ge : start ≤ i) (lt : i < start + len) :
    testNode C top k i T raw cs = true := by
  apply List.all_eq_true.mp ok
  apply List.mem_map.mpr
  exact ⟨i-start,List.mem_range.mpr (by omega),by omega⟩

theorem testBlock_join {n top k start a b : Nat} {C : Certificates} {T : Sig}
    {raw : List (Decor n)} {cs : List CutBank}
    (left : testBlock C top k start a T raw cs = true)
    (right : testBlock C top k (start+a) b T raw cs = true) :
    testBlock C top k start (a+b) T raw cs = true := by
  apply List.all_eq_true.mpr
  intro i hi
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  have hj' := List.mem_range.mp hj
  by_cases h : j < a
  · exact testBlock_at left _ (by omega) (by omega)
  · exact testBlock_at right _ (by omega) (by omega)

theorem low5 : Lower true (vars 5) (graphGoal 5) 1 := by
  exact countLower (m := 5) (by unfold proper; decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)


set_option maxHeartbeats 0 in
theorem low7 : Lower true (vars 7) (graphGoal 7) 1 := by
  exact unusedLower (m := 5) (by decide +kernel) (by unfold proper; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low5


theorem low10 : Lower true (vars 10) (graphGoal 10) 1 := by
  exact countLower (m := 10) (by unfold proper; decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)


set_option maxHeartbeats 0 in
theorem low11 : Lower true (vars 11) (graphGoal 11) 1 := by
  exact unusedLower (m := 10) (by decide +kernel) (by unfold proper; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low10


set_option maxHeartbeats 0 in
theorem low13 : Lower true (vars 13) (graphGoal 13) 1 := by
  exact unusedLower (m := 5) (by decide +kernel) (by unfold proper; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low5


set_option maxHeartbeats 0 in
theorem low14 : Lower true (vars 14) (graphGoal 14) 1 := by
  exact unusedLower (m := 10) (by decide +kernel) (by unfold proper; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low10


theorem low15 : Lower true (vars 15) (graphGoal 15) 3 := by
  exact countLower (m := 15) (by unfold proper; decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)


theorem low17 : Lower true (vars 17) (graphGoal 17) 1 := by
  exact countLower (m := 17) (by unfold proper; decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)


set_option maxHeartbeats 0 in
theorem low19 : Lower true (vars 19) (graphGoal 19) 1 := by
  exact unusedLower (m := 17) (by decide +kernel) (by unfold proper; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low17


theorem low20 : Lower true (vars 20) (graphGoal 20) 1 := by
  exact countLower (m := 20) (by unfold proper; decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)


def pos21 : Array Row := #[5, 5, 5, 5, 17, 17, 17, 17, 20, 20, 20, 20, 21, 21, 21, 21]
def negRows21 : Array Row := #[0, 1, 4, 16, 0, 1, 4, 16, 0, 1, 4, 16, 0, 1, 4, 16]
def left21 (i : Fin 16) : Row := pos21[i.val]?.getD 5
def right21 (i : Fin 16) : Row := negRows21[i.val]?.getD 0
def raw21 : List (Decor 16) := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xf0ff, 0x2222), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff0f, 0x4444), (0xffff0000ffff0000ffff0000ffff0000, 0xfff0, 0x8888)]
def bounds21 : List (Nat × Nat) := [(5, 1), (17, 1), (20, 1)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sep21 : ∀ i : Fin 16, bit (left21 i) (graphGoal 21) = true ∧ bit (right21 i) (graphGoal 21) = false := by
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mark21 : raw21 = (vars 21).map (mark left21 right21) := by
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check21 : certify (graphGoal 21) 3 (initialCuts 21 bounds21) raw21 = true := by
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low21 : Lower true (vars 21) (graphGoal 21) 4 := by
  refine exactFromCert (m := 21) (cap := 3) (bs := bounds21)
    (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sep21
    (by decide +kernel) (by decide +kernel) ?_ ?_
  · intro a ha
    simp only [bounds21, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact low5
    · exact low17
    · exact low20
  · rw [← mark21]
    exact check21


set_option maxHeartbeats 0 in
theorem low22 : Lower true (vars 22) (graphGoal 22) 1 := by
  exact unusedLower (m := 20) (by decide +kernel) (by unfold proper; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low20


set_option maxHeartbeats 0 in
theorem low23 : Lower true (vars 23) (graphGoal 23) 4 := by
  exact unusedLower (m := 21) (by decide +kernel) (by unfold proper; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low21


set_option maxHeartbeats 0 in
theorem low25 : Lower true (vars 25) (graphGoal 25) 1 := by
  exact unusedLower (m := 17) (by decide +kernel) (by unfold proper; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low17


set_option maxHeartbeats 0 in
theorem low26 : Lower true (vars 26) (graphGoal 26) 1 := by
  exact unusedLower (m := 10) (by decide +kernel) (by unfold proper; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low10


theorem low27 : Lower true (vars 27) (graphGoal 27) 3 := by
  exact countLower (m := 27) (by unfold proper; decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)


set_option maxHeartbeats 0 in
theorem low28 : Lower true (vars 28) (graphGoal 28) 1 := by
  exact unusedLower (m := 20) (by decide +kernel) (by unfold proper; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low20


set_option maxHeartbeats 0 in
theorem low29 : Lower true (vars 29) (graphGoal 29) 4 := by
  exact unusedLower (m := 21) (by decide +kernel) (by unfold proper; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low21


theorem low30 : Lower true (vars 30) (graphGoal 30) 3 := by
  exact countLower (m := 30) (by unfold proper; decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)


set_option maxHeartbeats 0 in
theorem low31 : Lower true (vars 31) (graphGoal 31) 6 := by
  exact trimLower (m := 21) (singles := [0xcccccccccccccccccccccccccccccccc, 0xff00ff00ff00ff00ff00ff00ff00ff00])
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low21


theorem low33 : Lower true (vars 33) (graphGoal 33) 1 := by
  exact countLower (m := 33) (by unfold proper; decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)


theorem low34 : Lower true (vars 34) (graphGoal 34) 1 := by
  exact countLower (m := 34) (by unfold proper; decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)


theorem low35 : Lower true (vars 35) (graphGoal 35) 2 := by
  exact countLower (m := 35) (by unfold proper; decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)


theorem low36 : Lower true (vars 36) (graphGoal 36) 1 := by
  exact countLower (m := 36) (by unfold proper; decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)


def pos37 : Array Row := #[5, 5, 5, 5, 33, 33, 33, 33, 36, 36, 36, 36, 37, 37, 37, 37]
def negRows37 : Array Row := #[0, 1, 4, 32, 0, 1, 4, 32, 0, 1, 4, 32, 0, 1, 4, 32]
def left37 (i : Fin 16) : Row := pos37[i.val]?.getD 5
def right37 (i : Fin 16) : Row := negRows37[i.val]?.getD 0
def raw37 : List (Decor 16) := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xf0ff, 0x2222), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff0f, 0x4444), (0xffffffff00000000ffffffff00000000, 0xfff0, 0x8888)]
def bounds37 : List (Nat × Nat) := [(5, 1), (33, 1), (36, 1)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sep37 : ∀ i : Fin 16, bit (left37 i) (graphGoal 37) = true ∧ bit (right37 i) (graphGoal 37) = false := by
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mark37 : raw37 = (vars 37).map (mark left37 right37) := by
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check37 : certify (graphGoal 37) 3 (initialCuts 37 bounds37) raw37 = true := by
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low37 : Lower true (vars 37) (graphGoal 37) 4 := by
  refine exactFromCert (m := 37) (cap := 3) (bs := bounds37)
    (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sep37
    (by decide +kernel) (by decide +kernel) ?_ ?_
  · intro a ha
    simp only [bounds37, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact low5
    · exact low33
    · exact low36
  · rw [← mark37]
    exact check37


theorem low38 : Lower true (vars 38) (graphGoal 38) 2 := by
  exact countLower (m := 38) (by unfold proper; decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)


set_option maxHeartbeats 0 in
theorem low39 : Lower true (vars 39) (graphGoal 39) 5 := by
  exact trimLower (m := 37) (singles := [0xcccccccccccccccccccccccccccccccc])
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low37


theorem low40 : Lower true (vars 40) (graphGoal 40) 1 := by
  exact countLower (m := 40) (by unfold proper; decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)


theorem low41 : Lower true (vars 41) (graphGoal 41) 2 := by
  exact countLower (m := 41) (by unfold proper; decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)


def pos42 : Array Row := #[10, 10, 10, 10, 34, 34, 34, 34, 40, 40, 40, 40, 42, 42, 42, 42]
def negRows42 : Array Row := #[0, 2, 8, 32, 0, 2, 8, 32, 0, 2, 8, 32, 0, 2, 8, 32]
def left42 (i : Fin 16) : Row := pos42[i.val]?.getD 10
def right42 (i : Fin 16) : Row := negRows42[i.val]?.getD 0
def raw42 : List (Decor 16) := [(0xcccccccccccccccccccccccccccccccc, 0xf0ff, 0x2222), (0xff00ff00ff00ff00ff00ff00ff00ff00, 0xff0f, 0x4444), (0xffffffff00000000ffffffff00000000, 0xfff0, 0x8888)]
def bounds42 : List (Nat × Nat) := [(10, 1), (34, 1), (40, 1)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sep42 : ∀ i : Fin 16, bit (left42 i) (graphGoal 42) = true ∧ bit (right42 i) (graphGoal 42) = false := by
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mark42 : raw42 = (vars 42).map (mark left42 right42) := by
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check42 : certify (graphGoal 42) 3 (initialCuts 42 bounds42) raw42 = true := by
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42 : Lower true (vars 42) (graphGoal 42) 4 := by
  refine exactFromCert (m := 42) (cap := 3) (bs := bounds42)
    (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sep42
    (by decide +kernel) (by decide +kernel) ?_ ?_
  · intro a ha
    simp only [bounds42, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact low10
    · exact low34
    · exact low40
  · rw [← mark42]
    exact check42


set_option maxHeartbeats 0 in
theorem low43 : Lower true (vars 43) (graphGoal 43) 5 := by
  exact trimLower (m := 42) (singles := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa])
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low42


theorem low44 : Lower true (vars 44) (graphGoal 44) 2 := by
  exact countLower (m := 44) (by unfold proper; decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)


set_option maxHeartbeats 0 in
theorem low45 : Lower true (vars 45) (graphGoal 45) 5 := by
  exact trimLower (m := 37) (singles := [0xff00ff00ff00ff00ff00ff00ff00ff00])
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low37


set_option maxHeartbeats 0 in
theorem low46 : Lower true (vars 46) (graphGoal 46) 5 := by
  exact trimLower (m := 42) (singles := [0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0])
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low42


def pos47 : Array Row := #[5, 5, 7, 7, 10, 11, 11, 13, 13, 14, 14, 33, 33, 33, 34, 35, 36, 36, 38, 40, 40, 41, 44]
def negRows47 : Array Row := #[1, 6, 3, 6, 2, 3, 9, 9, 12, 6, 12, 0, 1, 32, 32, 3, 6, 32, 6, 9, 32, 9, 12]
def left47 (i : Fin 23) : Row := pos47[i.val]?.getD 5
def right47 (i : Fin 23) : Row := negRows47[i.val]?.getD 0
def raw47 : List (Decor 23) := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0x20b9ef, 0x2890e5), (0xcccccccccccccccccccccccccccccccc, 0x4c67c, 0x5823e), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0x47078f, 0x45070a), (0xff00ff00ff00ff00ff00ff00ff00ff00, 0x7807f0, 0x6805c0), (0xffffffff00000000ffffffff00000000, 0x7ff800, 0x126000)]
def bounds47 : List (Nat × Nat) := [(39, 5), (43, 5), (45, 5), (46, 5), (37, 4), (42, 4), (15, 3), (35, 2), (38, 2), (41, 2), (44, 2), (5, 1), (7, 1), (10, 1), (11, 1), (13, 1), (14, 1), (33, 1), (34, 1), (36, 1), (40, 1)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sep47 : ∀ i : Fin 23, bit (left47 i) (graphGoal 47) = true ∧ bit (right47 i) (graphGoal 47) = false := by
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mark47 : raw47 = (vars 47).map (mark left47 right47) := by
  decide +kernel
def count47 : Nat → Nat
  | 4 => 3
  | 5 => 10
  | 6 => 3
  | 7 => 1
  | _ => 0

def rowWords47 : Nat → Nat → Nat
  | 4, 0 => 0x2364574000970000000000000000000022651510009b0000000000000000000012611510009b
  | 5, 0 => 0x45740005f0000000000000000000000089540007b0000000000000000000000089540005b0000000000000000000000085540005f0000000000000000000000081540007e0000000000000000000000050110007e00000000000000000000000d1510005f0000000000000000000000091510005f0000000000000000000000051510005f0000000000000000000000011510005f
  | 6, 0 => 0x340003f0000000000000000000000000140003f0000000000000000000000000110003f
  | 7, 0 => 0x1f
  | _, _ => 0

def slotCount47 : Nat → Nat
  | 4 => 64
  | 5 => 128
  | 6 => 32
  | 7 => 2
  | _ => 0

def indexWords47 : Nat → Nat → Nat
  | 4, 0 => 0x5000300020043002500410001004200000045000000000000000000000000000000000000000000000008000000000022000000000000000000070048004700440046000400000006000000280021000000240000000000000000000000000000002300000000000000000000002700000000000000000000000000000026
  | 5, 0 => 0xa1000001260081012200c70006000000c6000000000000000000c8006100a700000000008300660000000000000121004100000000000000000000000000a3000000000084000000000000002100000000000000000000000000000000000000820044002200000026000000000088000001270124
  | 5, 1 => 0xe100000086000000000000000000000046012800c500c400c30062000000000107010300c200e50000012501010000000000000000000000000000000000000000000000000024000400000042008500e700000000010500000000000000a50000000000020000000000c10001000000000000012300e300640087
  | 6, 0 => 0x60000004300020000000400270000000000000000000000000045000000000000004100230000002100010025000000470000000000000000
  | 7, 0 => 0x1
  | _, _ => 0

def perms47 : List (List (Nat × Nat)) := [[], [(1, 3)], [(0, 1), (2, 3)], [(0, 1), (0, 2), (0, 3)], [(0, 2)], [(0, 2), (1, 3)], [(0, 3), (0, 2), (0, 1)], [(0, 3), (1, 2)]]

def filter47 : Nat → Nat → Nat
  | 5, 0 => 0x10000000000000000200000000000000000000000000000000000000000000002000000000000000240000000000000000000000000000000000000000000000300000000000000030
  | 6, 0 => 0x3000000000000000300000000000000030
  | 7, 0 => 0x30
  | _, _ => 0

def proof47 : Certificates := (count47, rowWords47, slotCount47, indexWords47, perms47, filter47)

def roots47 : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffffffff00000000ffffffff00000000]

def cuts47 : List CutBank := [(0xff000000ff, 5, 0, roots47),
  (0xf0f00000f0f, 5, 0, roots47),
  (0x333300003333, 5, 0, roots47),
  (0x555500005555, 5, 0, roots47),
  (0x3300000033, 4, 0, roots47),
  (0x50500000505, 4, 0, roots47),
  (0xffff, 3, 0, roots47),
  (0xf0000000f, 2, 0, roots47),
  (0x5500000055, 2, 0, roots47),
  (0x30300000303, 2, 0, roots47),
  (0x111100001111, 2, 0, roots47),
  (0x33, 1, 0, roots47),
  (0xff, 1, 0, roots47),
  (0x505, 1, 0, roots47),
  (0xf0f, 1, 0, roots47),
  (0x3333, 1, 0, roots47),
  (0x5555, 1, 0, roots47),
  (0x300000003, 1, 0, roots47),
  (0x500000005, 1, 0, roots47),
  (0x1100000011, 1, 0, roots47),
  (0x10100000101, 1, 0, roots47)]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cutsEq47 : cuts47 = initialCuts 47 bounds47 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check47l4p0 : testBlock proof47 7 4 0 3 (graphGoal 47) raw47 cuts47 = true := by
  decide +kernel

theorem layer47k4 : testBlock proof47 7 4 0 3 (graphGoal 47) raw47 cuts47 = true :=
  check47l4p0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check47l5p0 : testBlock proof47 7 5 0 8 (graphGoal 47) raw47 cuts47 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check47l5p8 : testBlock proof47 7 5 8 2 (graphGoal 47) raw47 cuts47 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check47l5r0n10 : testBlock proof47 7 5 0 10 (graphGoal 47) raw47 cuts47 = true :=
  testBlock_join (start := 0) (a := 8) (b := 2) check47l5p0 check47l5p8

theorem layer47k5 : testBlock proof47 7 5 0 10 (graphGoal 47) raw47 cuts47 = true :=
  check47l5r0n10

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check47l6p0 : testBlock proof47 7 6 0 3 (graphGoal 47) raw47 cuts47 = true := by
  decide +kernel

theorem layer47k6 : testBlock proof47 7 6 0 3 (graphGoal 47) raw47 cuts47 = true :=
  check47l6p0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check47l7p0 : testBlock proof47 7 7 0 1 (graphGoal 47) raw47 cuts47 = true := by
  decide +kernel

theorem layer47k7 : testBlock proof47 7 7 0 1 (graphGoal 47) raw47 cuts47 = true :=
  check47l7p0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables47 : ∀ k ≤ 7, ∀ i < proof47.count k,
    testNode proof47 7 k i (graphGoal 47) raw47 cuts47 = true := by
  intro k hk i hi
  interval_cases k
  · simp [Certificates.count, proof47, count47] at hi
  · simp [Certificates.count, proof47, count47] at hi
  · simp [Certificates.count, proof47, count47] at hi
  · simp [Certificates.count, proof47, count47] at hi
  · exact testBlock_at layer47k4 i (Nat.zero_le _) hi
  · exact testBlock_at layer47k5 i (Nat.zero_le _) hi
  · exact testBlock_at layer47k6 i (Nat.zero_le _) hi
  · exact testBlock_at layer47k7 i (Nat.zero_le _) hi


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (vars 47) (graphGoal 47) 8 := by
  apply lower_impossible (by unfold proper; decide +kernel) (by decide +kernel)
    (by decide +kernel) (support_ok (by decide +kernel))
  have cutsOk : ∀ c ∈ cuts47, BankSound (graphGoal 47) c (vars 47) := by
    rw [cutsEq47]
    apply initialCuts_sound (hc := by decide +kernel)
    intro a ha
    simp only [bounds47, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact low39
    · exact low43
    · exact low45
    · exact low46
    · exact low37
    · exact low42
    · exact low15
    · exact low35
    · exact low38
    · exact low41
    · exact low44
    · exact low5
    · exact low7
    · exact low10
    · exact low11
    · exact low13
    · exact low14
    · exact low33
    · exact low34
    · exact low36
    · exact low40
  have h := checked_tables mark47 sep47 cutsOk (by decide +kernel) tables47
  have hroot := h 7 (Nat.le_refl _) 0 (by decide +kernel)
  have eq : frontWords proof47 7 7 0 raw47 = vars 47 := by decide +kernel
  simpa only [eq] using hroot

theorem low48 : Lower true (vars 48) (graphGoal 48) 1 := by
  exact countLower (m := 48) (by unfold proper; decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)


def pos49 : Array Row := #[17, 17, 17, 17, 33, 33, 33, 33, 48, 48, 48, 48, 49, 49, 49, 49]
def negRows49 : Array Row := #[0, 1, 16, 32, 0, 1, 16, 32, 0, 1, 16, 32, 0, 1, 16, 32]
def left49 (i : Fin 16) : Row := pos49[i.val]?.getD 17
def right49 (i : Fin 16) : Row := negRows49[i.val]?.getD 0
def raw49 : List (Decor 16) := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xf0ff, 0x2222), (0xffff0000ffff0000ffff0000ffff0000, 0xff0f, 0x4444), (0xffffffff00000000ffffffff00000000, 0xfff0, 0x8888)]
def bounds49 : List (Nat × Nat) := [(17, 1), (33, 1), (48, 1)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sep49 : ∀ i : Fin 16, bit (left49 i) (graphGoal 49) = true ∧ bit (right49 i) (graphGoal 49) = false := by
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mark49 : raw49 = (vars 49).map (mark left49 right49) := by
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check49 : certify (graphGoal 49) 3 (initialCuts 49 bounds49) raw49 = true := by
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low49 : Lower true (vars 49) (graphGoal 49) 4 := by
  refine exactFromCert (m := 49) (cap := 3) (bs := bounds49)
    (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sep49
    (by decide +kernel) (by decide +kernel) ?_ ?_
  · intro a ha
    simp only [bounds49, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact low17
    · exact low33
    · exact low48
  · rw [← mark49]
    exact check49


theorem low50 : Lower true (vars 50) (graphGoal 50) 2 := by
  exact countLower (m := 50) (by unfold proper; decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)


set_option maxHeartbeats 0 in
theorem low51 : Lower true (vars 51) (graphGoal 51) 5 := by
  exact trimLower (m := 49) (singles := [0xcccccccccccccccccccccccccccccccc])
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low49


def pos52 : Array Row := #[20, 20, 20, 20, 36, 36, 36, 36, 48, 48, 48, 48, 52, 52, 52, 52]
def negRows52 : Array Row := #[0, 4, 16, 32, 0, 4, 16, 32, 0, 4, 16, 32, 0, 4, 16, 32]
def left52 (i : Fin 16) : Row := pos52[i.val]?.getD 20
def right52 (i : Fin 16) : Row := negRows52[i.val]?.getD 0
def raw52 : List (Decor 16) := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xf0ff, 0x2222), (0xffff0000ffff0000ffff0000ffff0000, 0xff0f, 0x4444), (0xffffffff00000000ffffffff00000000, 0xfff0, 0x8888)]
def bounds52 : List (Nat × Nat) := [(20, 1), (36, 1), (48, 1)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sep52 : ∀ i : Fin 16, bit (left52 i) (graphGoal 52) = true ∧ bit (right52 i) (graphGoal 52) = false := by
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mark52 : raw52 = (vars 52).map (mark left52 right52) := by
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check52 : certify (graphGoal 52) 3 (initialCuts 52 bounds52) raw52 = true := by
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low52 : Lower true (vars 52) (graphGoal 52) 4 := by
  refine exactFromCert (m := 52) (cap := 3) (bs := bounds52)
    (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) sep52
    (by decide +kernel) (by decide +kernel) ?_ ?_
  · intro a ha
    simp only [bounds52, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact low20
    · exact low36
    · exact low48
  · rw [← mark52]
    exact check52


def pos53 : Array Row := #[5, 5, 17, 17, 20, 20, 33, 33, 36, 36, 48, 48]
def negRows53 : Array Row := #[1, 4, 1, 16, 4, 16, 1, 32, 4, 32, 16, 32]
def left53 (i : Fin 12) : Row := pos53[i.val]?.getD 5
def right53 (i : Fin 12) : Row := negRows53[i.val]?.getD 0
def raw53 : List (Decor 12) := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcf, 0x45), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0x333, 0x112), (0xffff0000ffff0000ffff0000ffff0000, 0xc3c, 0x428), (0xffffffff00000000ffffffff00000000, 0xfc0, 0xa80)]
def bounds53 : List (Nat × Nat) := [(21, 4), (37, 4), (49, 4), (52, 4), (5, 1), (17, 1), (20, 1), (33, 1), (36, 1), (48, 1)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sep53 : ∀ i : Fin 12, bit (left53 i) (graphGoal 53) = true ∧ bit (right53 i) (graphGoal 53) = false := by
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mark53 : raw53 = (vars 53).map (mark left53 right53) := by
  decide +kernel
def count53 : Nat → Nat
  | 3 => 3
  | 4 => 3
  | 5 => 1
  | 6 => 1
  | _ => 0

def rowWords53 : Nat → Nat → Nat
  | 3, 0 => 0x1214811000780000000000000000000023549110004700000000000000000000035491100047
  | 4, 0 => 0x48110003e0000000000000000000000089110002f0000000000000000000000049110002f
  | 5, 0 => 0x110001f
  | 6, 0 => 0xf
  | _, _ => 0

def slotCount53 : Nat → Nat
  | 3 => 32
  | 4 => 64
  | 5 => 16
  | 6 => 2
  | _ => 0

def indexWords53 : Nat → Nat → Nat
  | 3, 0 => 0x41004200000022002100240000000000040000000000000000002a000000000000000000000000004a000a0001000000000000000000000000000000020044
  | 4, 0 => 0x420000002500040022000a002c000000540047004400010056000000000000004e00480000000200500000002a0031000000000000000000210000004a00290032000000000000000000000000002b00000026000000000000000000000000000000000000000000240000000000410000004d00530000000000230000
  | 5, 0 => 0x10000000000050011000b000000000000000000030000000000090000
  | 6, 0 => 0x10000
  | _, _ => 0

def perms53 : List (List (Nat × Nat)) := [[], [(4, 5)], [(2, 4)], [(2, 4), (2, 5)], [(2, 5), (2, 4)], [(2, 5)], [(0, 2)], [(0, 2), (4, 5)], [(0, 2), (0, 4)], [(0, 2), (0, 4), (0, 5)], [(0, 2), (0, 5), (0, 4)], [(0, 2), (0, 5)], [(0, 4), (0, 2)], [(0, 4), (0, 5), (0, 2)], [(0, 4)], [(0, 4), (0, 5)], [(0, 4), (2, 5)], [(0, 4), (0, 2), (0, 5)], [(0, 5), (0, 4), (0, 2)], [(0, 5), (0, 2)], [(0, 5), (0, 4)], [(0, 5)], [(0, 5), (0, 2), (0, 4)], [(0, 5), (2, 4)]]

def filter53 : Nat → Nat → Nat
  | 3, 0 => 0x600000000000000000000000000000000
  | 4, 0 => 0x600000000000000000000000000000000
  | 5, 0 => 0xf
  | 6, 0 => 0xf
  | _, _ => 0

def proof53 : Certificates := (count53, rowWords53, slotCount53, indexWords53, perms53, filter53)

def roots53 : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000]

def cuts53 : List CutBank := [(0x330033, 4, 0, roots53),
  (0x3300000033, 4, 0, roots53),
  (0x3000300030003, 4, 0, roots53),
  (0x11001100110011, 4, 0, roots53),
  (0x33, 1, 0, roots53),
  (0x30003, 1, 0, roots53),
  (0x110011, 1, 0, roots53),
  (0x300000003, 1, 0, roots53),
  (0x1100000011, 1, 0, roots53),
  (0x1000100010001, 1, 0, roots53)]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cutsEq53 : cuts53 = initialCuts 53 bounds53 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check53l3p0 : testBlock proof53 6 3 0 3 (graphGoal 53) raw53 cuts53 = true := by
  decide +kernel

theorem layer53k3 : testBlock proof53 6 3 0 3 (graphGoal 53) raw53 cuts53 = true :=
  check53l3p0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check53l4p0 : testBlock proof53 6 4 0 3 (graphGoal 53) raw53 cuts53 = true := by
  decide +kernel

theorem layer53k4 : testBlock proof53 6 4 0 3 (graphGoal 53) raw53 cuts53 = true :=
  check53l4p0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check53l5p0 : testBlock proof53 6 5 0 1 (graphGoal 53) raw53 cuts53 = true := by
  decide +kernel

theorem layer53k5 : testBlock proof53 6 5 0 1 (graphGoal 53) raw53 cuts53 = true :=
  check53l5p0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check53l6p0 : testBlock proof53 6 6 0 1 (graphGoal 53) raw53 cuts53 = true := by
  decide +kernel

theorem layer53k6 : testBlock proof53 6 6 0 1 (graphGoal 53) raw53 cuts53 = true :=
  check53l6p0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables53 : ∀ k ≤ 6, ∀ i < proof53.count k,
    testNode proof53 6 k i (graphGoal 53) raw53 cuts53 = true := by
  intro k hk i hi
  interval_cases k
  · simp [Certificates.count, proof53, count53] at hi
  · simp [Certificates.count, proof53, count53] at hi
  · simp [Certificates.count, proof53, count53] at hi
  · exact testBlock_at layer53k3 i (Nat.zero_le _) hi
  · exact testBlock_at layer53k4 i (Nat.zero_le _) hi
  · exact testBlock_at layer53k5 i (Nat.zero_le _) hi
  · exact testBlock_at layer53k6 i (Nat.zero_le _) hi


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low53 : Lower true (vars 53) (graphGoal 53) 7 := by
  apply lower_impossible (by unfold proper; decide +kernel) (by decide +kernel)
    (by decide +kernel) (support_ok (by decide +kernel))
  have cutsOk : ∀ c ∈ cuts53, BankSound (graphGoal 53) c (vars 53) := by
    rw [cutsEq53]
    apply initialCuts_sound (hc := by decide +kernel)
    intro a ha
    simp only [bounds53, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact low21
    · exact low37
    · exact low49
    · exact low52
    · exact low5
    · exact low17
    · exact low20
    · exact low33
    · exact low36
    · exact low48
  have h := checked_tables mark53 sep53 cutsOk (by decide +kernel) tables53
  have hroot := h 6 (Nat.le_refl _) 0 (by decide +kernel)
  have eq : frontWords proof53 6 6 0 raw53 = vars 53 := by decide +kernel
  simpa only [eq] using hroot

set_option maxHeartbeats 0 in
theorem low54 : Lower true (vars 54) (graphGoal 54) 5 := by
  exact trimLower (m := 52) (singles := [0xcccccccccccccccccccccccccccccccc])
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low52


set_option maxHeartbeats 0 in
theorem low55 : Lower true (vars 55) (graphGoal 55) 8 := by
  exact trimLower (m := 53) (singles := [0xcccccccccccccccccccccccccccccccc])
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low53


theorem low56 : Lower true (vars 56) (graphGoal 56) 2 := by
  exact countLower (m := 56) (by unfold proper; decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)


set_option maxHeartbeats 0 in
theorem low57 : Lower true (vars 57) (graphGoal 57) 5 := by
  exact trimLower (m := 49) (singles := [0xff00ff00ff00ff00ff00ff00ff00ff00])
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low49


set_option maxHeartbeats 0 in
theorem low58 : Lower true (vars 58) (graphGoal 58) 5 := by
  exact trimLower (m := 42) (singles := [0xffff0000ffff0000ffff0000ffff0000])
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low42


def pos59 : Array Row := #[10, 10, 10, 11, 11, 17, 19, 19, 25, 25, 26, 26, 33, 33, 34, 35, 40, 40, 40, 41, 48, 48, 50]
def negRows59 : Array Row := #[2, 8, 9, 3, 9, 1, 3, 18, 9, 24, 18, 24, 0, 32, 32, 3, 8, 9, 32, 9, 18, 32, 18]
def left59 (i : Fin 23) : Row := pos59[i.val]?.getD 10
def right59 (i : Fin 23) : Row := negRows59[i.val]?.getD 0
def raw59 : List (Decor 23) := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0x8b3f8, 0xa817c), (0xcccccccccccccccccccccccccccccccc, 0x40ccdf, 0x5084c9), (0xff00ff00ff00ff00ff00ff00ff00ff00, 0xf0f1f, 0xb0b16), (0xffff0000ffff0000ffff0000ffff0000, 0x700fe0, 0x500e80), (0xffffffff00000000ffffffff00000000, 0x7ff000, 0x246000)]
def bounds59 : List (Nat × Nat) := [(43, 5), (51, 5), (57, 5), (58, 5), (42, 4), (49, 4), (27, 3), (35, 2), (41, 2), (50, 2), (56, 2), (10, 1), (11, 1), (17, 1), (19, 1), (25, 1), (26, 1), (33, 1), (34, 1), (40, 1), (48, 1)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sep59 : ∀ i : Fin 23, bit (left59 i) (graphGoal 59) = true ∧ bit (right59 i) (graphGoal 59) = false := by
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mark59 : raw59 = (vars 59).map (mark left59 right59) := by
  decide +kernel
def count59 : Nat → Nat
  | 4 => 3
  | 5 => 10
  | 6 => 3
  | 7 => 1
  | _ => 0

def rowWords59 : Nat → Nat → Nat
  | 4, 0 => 0x22645740009b0000000000000000000022651510009b0000000000000000000012611510009b
  | 5, 0 => 0x45740005f000000000000000000000008d5400077000000000000000000000008d54000570000000000000000000000085540005f0000000000000000000000081540007e0000000000000000000000050110007e00000000000000000000000d1510005f0000000000000000000000091510005f0000000000000000000000051510005f0000000000000000000000011510005f
  | 6, 0 => 0x340003f0000000000000000000000000140003f0000000000000000000000000110003f
  | 7, 0 => 0x1f
  | _, _ => 0

def slotCount59 : Nat → Nat
  | 4 => 64
  | 5 => 128
  | 6 => 32
  | 7 => 2
  | _ => 0

def indexWords59 : Nat → Nat → Nat
  | 4, 0 => 0x27002600070003000500210000000000240000002800220000000000000023000000000000000000000000000100000047004100250042000000000000000000000000004500430000000000000048000000080000000000460044000000000000000200000000000000000006000400000000
  | 5, 0 => 0x21000001070000000000a70000000000000000012700820022000000c40000000000000000000001250000000000000000008700e70044000000000000000000000000000000c30062000000000105010300c200000000000000000064000000c800000000000000c7000000000000000000000000
  | 5, 1 => 0x42000000e500000000000000000000000000000000000000020024000000c100010000012600000124012300e30085000000000128012200e100a100c6008100260006000400c50084000000000000000000000000006100a500000088008300660046000000860121004100000000000000000101000000a30000
  | 6, 0 => 0x20000002700250000000000000004000000000000000000000000004100230000002100010047000000450000000000000000000000000006000000000043
  | 7, 0 => 0x1
  | _, _ => 0

def perms59 : List (List (Nat × Nat)) := [[], [(1, 3)], [(0, 1), (3, 4)], [(0, 1), (0, 4), (0, 3)], [(0, 3), (0, 4), (0, 1)], [(0, 3), (1, 4)], [(0, 4)], [(0, 4), (1, 3)]]

def filter59 : Nat → Nat → Nat
  | 5, 0 => 0x20000000000000000100000000000000000000000000000000000000000000001000000000000000140000000000000000000000000000000000000000000000300000000000000030
  | 6, 0 => 0x3000000000000000300000000000000030
  | 7, 0 => 0x30
  | _, _ => 0

def proof59 : Certificates := (count59, rowWords59, slotCount59, indexWords59, perms59, filter59)

def roots59 : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000]

def cuts59 : List CutBank := [(0xf0f00000f0f, 5, 0, roots59),
  (0xf000f000f000f, 5, 0, roots59),
  (0x303030303030303, 5, 0, roots59),
  (0x505050505050505, 5, 0, roots59),
  (0x50500000505, 4, 0, roots59),
  (0x3000300030003, 4, 0, roots59),
  (0xf0f0f0f, 3, 0, roots59),
  (0xf0000000f, 2, 0, roots59),
  (0x30300000303, 2, 0, roots59),
  (0x5000500050005, 2, 0, roots59),
  (0x101010101010101, 2, 0, roots59),
  (0x505, 1, 0, roots59),
  (0xf0f, 1, 0, roots59),
  (0x30003, 1, 0, roots59),
  (0xf000f, 1, 0, roots59),
  (0x3030303, 1, 0, roots59),
  (0x5050505, 1, 0, roots59),
  (0x300000003, 1, 0, roots59),
  (0x500000005, 1, 0, roots59),
  (0x10100000101, 1, 0, roots59),
  (0x1000100010001, 1, 0, roots59)]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cutsEq59 : cuts59 = initialCuts 59 bounds59 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check59l4p0 : testBlock proof59 7 4 0 3 (graphGoal 59) raw59 cuts59 = true := by
  decide +kernel

theorem layer59k4 : testBlock proof59 7 4 0 3 (graphGoal 59) raw59 cuts59 = true :=
  check59l4p0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check59l5p0 : testBlock proof59 7 5 0 8 (graphGoal 59) raw59 cuts59 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check59l5p8 : testBlock proof59 7 5 8 2 (graphGoal 59) raw59 cuts59 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check59l5r0n10 : testBlock proof59 7 5 0 10 (graphGoal 59) raw59 cuts59 = true :=
  testBlock_join (start := 0) (a := 8) (b := 2) check59l5p0 check59l5p8

theorem layer59k5 : testBlock proof59 7 5 0 10 (graphGoal 59) raw59 cuts59 = true :=
  check59l5r0n10

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check59l6p0 : testBlock proof59 7 6 0 3 (graphGoal 59) raw59 cuts59 = true := by
  decide +kernel

theorem layer59k6 : testBlock proof59 7 6 0 3 (graphGoal 59) raw59 cuts59 = true :=
  check59l6p0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check59l7p0 : testBlock proof59 7 7 0 1 (graphGoal 59) raw59 cuts59 = true := by
  decide +kernel

theorem layer59k7 : testBlock proof59 7 7 0 1 (graphGoal 59) raw59 cuts59 = true :=
  check59l7p0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables59 : ∀ k ≤ 7, ∀ i < proof59.count k,
    testNode proof59 7 k i (graphGoal 59) raw59 cuts59 = true := by
  intro k hk i hi
  interval_cases k
  · simp [Certificates.count, proof59, count59] at hi
  · simp [Certificates.count, proof59, count59] at hi
  · simp [Certificates.count, proof59, count59] at hi
  · simp [Certificates.count, proof59, count59] at hi
  · exact testBlock_at layer59k4 i (Nat.zero_le _) hi
  · exact testBlock_at layer59k5 i (Nat.zero_le _) hi
  · exact testBlock_at layer59k6 i (Nat.zero_le _) hi
  · exact testBlock_at layer59k7 i (Nat.zero_le _) hi


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (vars 59) (graphGoal 59) 8 := by
  apply lower_impossible (by unfold proper; decide +kernel) (by decide +kernel)
    (by decide +kernel) (support_ok (by decide +kernel))
  have cutsOk : ∀ c ∈ cuts59, BankSound (graphGoal 59) c (vars 59) := by
    rw [cutsEq59]
    apply initialCuts_sound (hc := by decide +kernel)
    intro a ha
    simp only [bounds59, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact low43
    · exact low51
    · exact low57
    · exact low58
    · exact low42
    · exact low49
    · exact low27
    · exact low35
    · exact low41
    · exact low50
    · exact low56
    · exact low10
    · exact low11
    · exact low17
    · exact low19
    · exact low25
    · exact low26
    · exact low33
    · exact low34
    · exact low40
    · exact low48
  have h := checked_tables mark59 sep59 cutsOk (by decide +kernel) tables59
  have hroot := h 7 (Nat.le_refl _) 0 (by decide +kernel)
  have eq : frontWords proof59 7 7 0 raw59 = vars 59 := by decide +kernel
  simpa only [eq] using hroot

set_option maxHeartbeats 0 in
theorem low60 : Lower true (vars 60) (graphGoal 60) 5 := by
  exact trimLower (m := 52) (singles := [0xff00ff00ff00ff00ff00ff00ff00ff00])
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low52


set_option maxHeartbeats 0 in
theorem low61 : Lower true (vars 61) (graphGoal 61) 8 := by
  exact trimLower (m := 53) (singles := [0xff00ff00ff00ff00ff00ff00ff00ff00])
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) low53


def pos62 : Array Row := #[10, 10, 14, 14, 20, 22, 22, 26, 26, 28, 28, 34, 34, 34, 36, 38, 40, 40, 44, 48, 48, 50, 56]
def negRows62 : Array Row := #[2, 12, 6, 12, 4, 6, 18, 18, 24, 12, 24, 0, 2, 32, 32, 6, 12, 32, 12, 18, 32, 18, 24]
def left62 (i : Fin 23) : Row := pos62[i.val]?.getD 10
def right62 (i : Fin 23) : Row := negRows62[i.val]?.getD 0
def raw62 : List (Decor 23) := [(0xcccccccccccccccccccccccccccccccc, 0x20b9ef, 0x2890e5), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0x4c67c, 0x5823e), (0xff00ff00ff00ff00ff00ff00ff00ff00, 0x47078f, 0x45070a), (0xffff0000ffff0000ffff0000ffff0000, 0x7807f0, 0x6805c0), (0xffffffff00000000ffffffff00000000, 0x7ff800, 0x126000)]
def bounds62 : List (Nat × Nat) := [(46, 5), (54, 5), (58, 5), (60, 5), (42, 4), (52, 4), (30, 3), (38, 2), (44, 2), (50, 2), (56, 2), (10, 1), (14, 1), (20, 1), (22, 1), (26, 1), (28, 1), (34, 1), (36, 1), (40, 1), (48, 1)]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sep62 : ∀ i : Fin 23, bit (left62 i) (graphGoal 62) = true ∧ bit (right62 i) (graphGoal 62) = false := by
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mark62 : raw62 = (vars 62).map (mark left62 right62) := by
  decide +kernel
def count62 : Nat → Nat
  | 4 => 3
  | 5 => 10
  | 6 => 3
  | 7 => 1
  | _ => 0

def rowWords62 : Nat → Nat → Nat
  | 4, 0 => 0x2364574000970000000000000000000022651510009b0000000000000000000012611510009b
  | 5, 0 => 0x45740005f0000000000000000000000089540007b0000000000000000000000089540005b0000000000000000000000085540005f0000000000000000000000081540007e0000000000000000000000050110007e00000000000000000000000d1510005f0000000000000000000000091510005f0000000000000000000000051510005f0000000000000000000000011510005f
  | 6, 0 => 0x340003f0000000000000000000000000140003f0000000000000000000000000110003f
  | 7, 0 => 0x1f
  | _, _ => 0

def slotCount62 : Nat → Nat
  | 4 => 64
  | 5 => 128
  | 6 => 32
  | 7 => 2
  | _ => 0

def indexWords62 : Nat → Nat → Nat
  | 4, 0 => 0x260000000000000046000000000000002800000000000000000000000000000047000000430000000000000000000000000000000000480023000600050000000000000000000000000000000000000000000000440001000000000007004500250024002100410022000800000004000200030000000000270042
  | 5, 0 => 0x2200000000000000000126000000000122006100e1000001030000000001280107012400c60026000600020004008200c40000000000000000000000c500a50000008800660064004600000086000000e700000000000000000000000000a10000000000810000000000000000000000000000000000a70000000000000000
  | 5, 1 => 0x1270041000000c200240000000000850000000001210000000000000087008400000042000000000000004401250000000000c300c10000000001050101000000000000000001230062000000c800000000000000c70000000000000000000000210001000000e3008300e500000000000000000000000000a3000000000000
  | 6, 0 => 0x210000000000470023000000450000000000000000000000000006000400000041000000270001002500000000000000020000000000430000000000000000
  | 7, 0 => 0x10000
  | _, _ => 0

def perms62 : List (List (Nat × Nat)) := [[], [(2, 4)], [(1, 2), (3, 4)], [(1, 2), (1, 3), (1, 4)], [(1, 3)], [(1, 3), (2, 4)], [(1, 4), (1, 3), (1, 2)], [(1, 4), (2, 3)]]

def filter62 : Nat → Nat → Nat
  | 5, 0 => 0x10000000000000000200000000000000000000000000000000000000000000002000000000000000240000000000000000000000000000000000000000000000300000000000000030
  | 6, 0 => 0x3000000000000000300000000000000030
  | 7, 0 => 0x30
  | _, _ => 0

def proof62 : Certificates := (count62, rowWords62, slotCount62, indexWords62, perms62, filter62)

def roots62 : List Sig := [0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000]

def cuts62 : List CutBank := [(0x555500005555, 5, 0, roots62),
  (0x55005500550055, 5, 0, roots62),
  (0x505050505050505, 5, 0, roots62),
  (0x1111111111111111, 5, 0, roots62),
  (0x50500000505, 4, 0, roots62),
  (0x11001100110011, 4, 0, roots62),
  (0x55555555, 3, 0, roots62),
  (0x5500000055, 2, 0, roots62),
  (0x111100001111, 2, 0, roots62),
  (0x5000500050005, 2, 0, roots62),
  (0x101010101010101, 2, 0, roots62),
  (0x505, 1, 0, roots62),
  (0x5555, 1, 0, roots62),
  (0x110011, 1, 0, roots62),
  (0x550055, 1, 0, roots62),
  (0x5050505, 1, 0, roots62),
  (0x11111111, 1, 0, roots62),
  (0x500000005, 1, 0, roots62),
  (0x1100000011, 1, 0, roots62),
  (0x10100000101, 1, 0, roots62),
  (0x1000100010001, 1, 0, roots62)]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cutsEq62 : cuts62 = initialCuts 62 bounds62 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check62l4p0 : testBlock proof62 7 4 0 3 (graphGoal 62) raw62 cuts62 = true := by
  decide +kernel

theorem layer62k4 : testBlock proof62 7 4 0 3 (graphGoal 62) raw62 cuts62 = true :=
  check62l4p0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check62l5p0 : testBlock proof62 7 5 0 8 (graphGoal 62) raw62 cuts62 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check62l5p8 : testBlock proof62 7 5 8 2 (graphGoal 62) raw62 cuts62 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check62l5r0n10 : testBlock proof62 7 5 0 10 (graphGoal 62) raw62 cuts62 = true :=
  testBlock_join (start := 0) (a := 8) (b := 2) check62l5p0 check62l5p8

theorem layer62k5 : testBlock proof62 7 5 0 10 (graphGoal 62) raw62 cuts62 = true :=
  check62l5r0n10

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check62l6p0 : testBlock proof62 7 6 0 3 (graphGoal 62) raw62 cuts62 = true := by
  decide +kernel

theorem layer62k6 : testBlock proof62 7 6 0 3 (graphGoal 62) raw62 cuts62 = true :=
  check62l6p0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check62l7p0 : testBlock proof62 7 7 0 1 (graphGoal 62) raw62 cuts62 = true := by
  decide +kernel

theorem layer62k7 : testBlock proof62 7 7 0 1 (graphGoal 62) raw62 cuts62 = true :=
  check62l7p0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables62 : ∀ k ≤ 7, ∀ i < proof62.count k,
    testNode proof62 7 k i (graphGoal 62) raw62 cuts62 = true := by
  intro k hk i hi
  interval_cases k
  · simp [Certificates.count, proof62, count62] at hi
  · simp [Certificates.count, proof62, count62] at hi
  · simp [Certificates.count, proof62, count62] at hi
  · simp [Certificates.count, proof62, count62] at hi
  · exact testBlock_at layer62k4 i (Nat.zero_le _) hi
  · exact testBlock_at layer62k5 i (Nat.zero_le _) hi
  · exact testBlock_at layer62k6 i (Nat.zero_le _) hi
  · exact testBlock_at layer62k7 i (Nat.zero_le _) hi


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low62 : Lower true (vars 62) (graphGoal 62) 8 := by
  apply lower_impossible (by unfold proper; decide +kernel) (by decide +kernel)
    (by decide +kernel) (support_ok (by decide +kernel))
  have cutsOk : ∀ c ∈ cuts62, BankSound (graphGoal 62) c (vars 62) := by
    rw [cutsEq62]
    apply initialCuts_sound (hc := by decide +kernel)
    intro a ha
    simp only [bounds62, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact low46
    · exact low54
    · exact low58
    · exact low60
    · exact low42
    · exact low52
    · exact low30
    · exact low38
    · exact low44
    · exact low50
    · exact low56
    · exact low10
    · exact low14
    · exact low20
    · exact low22
    · exact low26
    · exact low28
    · exact low34
    · exact low36
    · exact low40
    · exact low48
  have h := checked_tables mark62 sep62 cutsOk (by decide +kernel) tables62
  have hroot := h 7 (Nat.le_refl _) 0 (by decide +kernel)
  have eq : frontWords proof62 7 7 0 raw62 = vars 62 := by decide +kernel
  simpa only [eq] using hroot

def pos63 : Array Row := #[5, 5, 5, 5, 5, 7, 7, 7, 7, 10, 10, 10, 10, 11, 11, 11, 11, 13, 13, 14, 14, 14, 17, 17, 17, 17, 19, 19, 19, 20, 20, 20, 20, 20, 21, 21, 22, 22, 22, 23, 25, 25, 26, 26, 28, 28, 29, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 35, 35, 36, 36, 36, 37, 37, 37, 37, 38, 40, 40, 40, 40, 40, 40, 41, 42, 44, 46, 48, 48, 48, 48, 48, 48, 48, 49, 49, 49, 50, 50, 52, 52, 53, 56, 60]

def negRows63 : Array Row := #[0, 3, 6, 9, 32, 1, 3, 4, 6, 2, 8, 9, 24, 2, 3, 8, 9, 9, 12, 2, 6, 12, 0, 4, 16, 32, 1, 3, 18, 4, 6, 16, 18, 32, 1, 32, 6, 16, 18, 18, 9, 24, 18, 24, 12, 24, 12, 0, 1, 3, 16, 32, 0, 2, 3, 6, 32, 1, 3, 1, 6, 32, 0, 1, 4, 32, 6, 0, 8, 9, 12, 24, 32, 9, 32, 12, 12, 0, 1, 4, 16, 18, 24, 32, 1, 16, 32, 18, 32, 16, 32, 32, 24, 12]

def left63 (i : Fin 94) : Row := pos63[i.val]?.getD 5

def right63 (i : Fin 94) : Row := negRows63[i.val]?.getD 0

def raw63 : List (Decor 94) := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0x8700203c60fc38c1fc7e1ff, 0x1042208e4301040c03486a), (0xcccccccccccccccccccccccccccccccc, 0x180140407f00cf01c39ffe0, 0x82000414e204d158186346), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0x2e001807f80070ffe03e01ff, 0x200098451080501060b40184), (0xff00ff00ff00ff00ff00ff00ff00ff00, 0x30001ff800007f00003ffe00, 0x30041af000007b0000279c08), (0xffff0000ffff0000ffff0000ffff0000, 0x3fffe00000007fffffc00000, 0x12a7008000042ee191001000), (0xffffffff00000000ffffffff00000000, 0x3fffffffffff800000000000, 0xd4805022108000a02000010)]

def bounds63 : List (Nat × Nat) := [(47, 8), (55, 8), (59, 8), (61, 8), (62, 8), (53, 7), (31, 6), (39, 5), (43, 5), (45, 5), (46, 5), (51, 5), (54, 5), (57, 5), (58, 5), (60, 5), (21, 4), (23, 4), (29, 4), (37, 4), (42, 4), (49, 4), (52, 4), (15, 3), (27, 3), (30, 3), (35, 2), (38, 2), (41, 2), (44, 2), (50, 2), (56, 2), (5, 1), (7, 1), (10, 1), (11, 1), (13, 1), (14, 1), (17, 1), (19, 1), (20, 1), (22, 1), (25, 1), (26, 1), (28, 1), (33, 1), (34, 1), (36, 1), (40, 1), (48, 1)]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem sep63 : ∀ i : Fin 94, bit (left63 i) (graphGoal 63) = true ∧ bit (right63 i) (graphGoal 63) = false := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem mark63 : raw63 = (vars 63).map (mark left63 right63) := by
  decide +kernel

def count63 : Nat → Nat
  | 4 => 2
  | 5 => 122
  | 6 => 549
  | 7 => 316
  | 8 => 55
  | 9 => 6
  | 10 => 1
  | _ => 0

def rowWords63 : Nat → Nat → Nat
  | 4, 0 => 0x549391a217541200c9200000000000005453916147499100c15
  | 5, 0 => 0x1091611791920043e0000000000000001545495051920078a0000000000000001525435751920071a000000000000000239463575192004370000000000000001525413785920073200000000000000015254137859200712000000000000000109d6137859200536000000000000000219561378592005350000000000000001491613785920052700000000000000011916137859200535000000000000000109161378592005360000000000000001505205745920064e0000000000000001565205745920060f0000000000000001524205745920065a0000000000000002395a24754910043700000000000000028945c6754910043d0000000000000001181a15254110069c0000000000000000695495154110059c0000000000000002488dd275591006270000000000000000488dd275591006270000000000000002095212715910053a0000000000000002395a35750910043700000000000000015454a0750910074a000000000000000189d5a0750910043e00000000000000013915a0750910053600000000000000012915a0750910053a00000000000000018915a0750910043e0000000000000002895436750910043e000000000000000129d51504851005d80000000000000001529e1504851007580000000000000001521e1504851007580000000000000002295515089910059a0000000000000001545414189910078c0000000000000001545414789910070e000000000000000139161478991004370000000000000001091614789910043e0000000000000002395a3574991004370000000000000001505205749910064e0000000000000001514e0574991006550000000000000002395e354499100437000000000000000129d515049910059a000000000000000152545504991007980000000000000001521e15049910071a0000000000000000495625749910042f000000000000000239562574991004370000000000000002488e1574991006270000000000000000488e1574991006270000000000000000488215749910062e00000000000000028955c5749910041f0000000000000001505205749910068e0000000000000001514e0574991006950000000000000001524205749910069a0000000000000001545414149910078c000000000000000152541414991007980000000000000003545424749910070e0000000000000001525424749910071a000000000000000139162474991004370000000000000001091624749910043e0000000000000001525414749910071a000000000000000239561474991004370000000000000002095614749910043e0000000000000001511614749910061d000000000000000139161474991004370000000000000001091614749910043e
  | 5, 1 => 0x2394624749b5004370000000000000001528e1178995006530000000000000001544a24789950068b000000000000000239462074995004760000000000000002488dd264595006270000000000000000488dd264595006270000000000000002295512781950055a0000000000000001549212781950064e0000000000000002394626755120043700000000000000004882167d4520062e0000000000000002495a2375452005270000000000000000495a2375452005270000000000000002495a2175452004ad0000000000000001898df675452004370000000000000002488dd675452006270000000000000000488dd675452006270000000000000003898dd67545200437000000000000000129921545412005ca0000000000000001528e1515412006d200000000000000015454a4754120074a00000000000000024954a4754120056a00000000000000024954a4754120074a0000000000000001529a14754120069a00000000000000015491e2754120074a0000000000000002475222754120066a0000000000000001521a21754120069a0000000000000001391a2175412004b60000000000000001528e1175412006d200000000000000015254147d5920071a0000000000000002495e35195920042f0000000000000002288224755920066a00000000000000023946247559200437000000000000000228822475592006aa00000000000000023954647559200527000000000000000239462475592005270000000000000002395444755920052700000000000000038991d1755920042f00000000000000038911d1755920042f0000000000000003791211755920042f0000000000000002478e1175592006270000000000000000478e1175592006270000000000000000478211755920062e0000000000000001549e15250120074a0000000000000001529215750120074a0000000000000001529a15750120071a000000000000000189d45425012004ea000000000000000239545425012005e20000000000000002795614250120066a000000000000000239463549192004a7000000000000000129d515091920078a0000000000000003545495091920078a0000000000000001529215091920078a0000000000000001529e15091920071a0000000000000001525435791920071a000000000000000239463579192004370000000000000001525411791920071a0000000000000002395611791920043700000000000000013916117919200437
  | 6, 0 => 0x549504991003ba0000000000000000005495049910039a000000000000000000545504991003bc0000000000000000001e15049910033e000000000000000000463574991002bd000000000000000000423574991002be0000000000000000005235749910023f0000000000000000005465749910039d0000000000000000005425749910039e000000000000000000d5e5749910031f0000000000000000005625749910023f0000000000000000005225749910023f000000000000000000921574991002af000000000000000000121574991002af0000000000000000008e1574991002b7000000000000000000861574991002bd000000000000000000821574991002be0000000000000000009615749910031f0000000000000000009215749910023f0000000000000000009215749910032f0000000000000000009215749910022f0000000000000000001215749910032f0000000000000000001215749910022f0000000000000000008e1574991003370000000000000000008e1574991002370000000000000000008615749910033d0000000000000000008215749910033e0000000000000000005445749910039d0000000000000000005405749910039e00000000000000000055c5749910031f000000000000000000d20574991002af000000000000000000520574991002af0000000000000000004e0574991002b7000000000000000000460574991002bd000000000000000000420574991002be000000000000000000de05749910023f000000000000000000d205749910022f0000000000000000005205749910023f0000000000000000005205749910022f0000000000000000004e0574991002370000000000000000004605749910023d0000000000000000004205749910023e000000000000000000551414991003ad000000000000000000541414991003bc00000000000000000095d4149910033d00000000000000000055d4149910033d000000000000000000961414991002bd000000000000000000561414991002bd000000000000000000506474991003ad000000000000000000d524749910032f0000000000000000005464749910033d0000000000000000005424749910033e000000000000000000d624749910023f0000000000000000009624749910023f0000000000000000005624749910023f0000000000000000001624749910023f000000000000000000821474991002be0000000000000000005454749910033d0000000000000000005414749910033e000000000000000000d614749910023f0000000000000000009614749910023f0000000000000000005614749910023f0000000000000000001614749910023f0000000000000000008214749910033e
  | 6, 1 => 0x8215748510037c0000000000000000009a15748510033d000000000000000000463548991002bd000000000000000000423548991002be0000000000000000005e35489910023f0000000000000000008a1548991002bb0000000000000000009e15489910023f000000000000000000921518991002bd0000000000000000008e1518991003b5000000000000000000d515089910039e0000000000000000005515089910039e000000000000000000545508991003bc0000000000000000009e15089910033e0000000000000000005235789910023f0000000000000000009215789910023f000000000000000000551418991003ad000000000000000000541418991003bc00000000000000000055d4189910033d000000000000000000961418991002bd000000000000000000561418991002bd0000000000000000005514789910032f0000000000000000005454789910033d0000000000000000005414789910033e000000000000000000d614789910023f0000000000000000009614789910023f0000000000000000005614789910023f0000000000000000001614789910023f000000000000000000549504991003da000000000000000000463564991002bd000000000000000000423564991002be0000000000000000008e1564991002b70000000000000000004635749910027d0000000000000000004235749910027e0000000000000000005a35749910023f0000000000000000005465749910035d0000000000000000005425749910035e000000000000000000d5a5749910031f00000000000000000055a5749910031f0000000000000000009215749910026f0000000000000000001215749910026f0000000000000000008e1574991002770000000000000000008615749910027d0000000000000000008215749910027e0000000000000000009a15749910023f0000000000000000005445749910035d0000000000000000005405749910035e0000000000000000005585749910031f000000000000000000d205749910026f0000000000000000005205749910026f0000000000000000004e0574991002770000000000000000004605749910027d0000000000000000004205749910027e0000000000000000005064749910036d0000000000000000008214749910027e000000000000000000463544991002bd000000000000000000423544991002be000000000000000000de35449910023f0000000000000000005e35449910023f0000000000000000009e15449910023f0000000000000000001e15449910023f000000000000000000921514991002bd0000000000000000008e1514991003b5000000000000000000d515049910039e0000000000000000005515049910039e
  | 6, 2 => 0x5222755910023f000000000000000000921275591002af000000000000000000121275591002af0000000000000000008dd275591003370000000000000000008e1275591002b7000000000000000000861275591002bd000000000000000000821275591002be0000000000000000008de175591003b50000000000000000004a2175591002bd0000000000000000009212715910023f0000000000000000009212715910033b0000000000000000005212715910033b000000000000000000551525091003cb0000000000000000009e15150910027d000000000000000000549505091003da0000000000000000004a3565091002bb0000000000000000005e35650910023f0000000000000000005e25650910023f0000000000000000008e1565091002b70000000000000000009e15650910023f0000000000000000004e0565091002b70000000000000000004a0565091002bb0000000000000000005e05650910023f0000000000000000005435750910035e0000000000000000004635750910027d0000000000000000004235750910027e000000000000000000da35750910023f0000000000000000005a35750910023f0000000000000000005415750910035e0000000000000000008215750910027e000000000000000000da15750910023f0000000000000000009a15750910023f0000000000000000001a15750910023f00000000000000000054a0750910037a0000000000000000005460750910037c000000000000000000d5a0750910033e00000000000000000015a0750910033e0000000000000000005620750910027e0000000000000000005476750910033d0000000000000000005436750910033e000000000000000000d636750910023f0000000000000000005636750910023f000000000000000000423544851002fc000000000000000000de35448510027d0000000000000000005e35448510027d000000000000000000de15448510027d000000000000000000d51504851003dc000000000000000000551504851003dc000000000000000000549504851003f8000000000000000000549504851003d80000000000000000009e15048510037c0000000000000000001e15048510037c0000000000000000004a3574851002f9000000000000000000423574851002fc0000000000000000005a3574851002bd0000000000000000005425748510037c0000000000000000005625748510027d0000000000000000005225748510027d0000000000000000008e1574851002f5000000000000000000821574851002fc0000000000000000009a1574851002bd0000000000000000005415748510037c0000000000000000009215748510027d0000000000000000008e157485100375
  | 6, 3 => 0x86107d4910037c00000000000000000052367d4910023f0000000000000000008e167d4910027700000000000000000086167d4910027d00000000000000000092167d4910023f0000000000000000008e167d491003370000000000000000008e167d4910023700000000000000000086167d4910033d000000000000000000423545491002de0000000000000000004624754910027d000000000000000000da24754910023f0000000000000000005a24754910023f0000000000000000001a24754910023f0000000000000000005636754910029f0000000000000000005636754910023f0000000000000000005236754910023f0000000000000000004626754910027d0000000000000000004226754910027e0000000000000000005226754910023f0000000000000000004626754910033d0000000000000000004226754910033e0000000000000000009616754910029f000000000000000000921675491002af000000000000000000121675491002af0000000000000000008e1675491002b700000000000000000045c6754910033d0000000000000000005206754910023f0000000000000000001a1525451002bd0000000000000000005222754510027d0000000000000000008dd275451003750000000000000000008e1275451002f5000000000000000000821275451002fc0000000000000000009a1275451002bd000000000000000000523525411002de0000000000000000001a1525411002be000000000000000000921525411002de000000000000000000461525411003dc0000000000000000009a15254110039e0000000000000000001a15254110039e000000000000000000549515411003dc00000000000000000054a275411003da0000000000000000001a2275411002be000000000000000000921275411002ee000000000000000000121275411002ee000000000000000000861275411002fc0000000000000000009a1275411002be000000000000000000d4a175411003dc00000000000000000054a175411003dc0000000000000000004a2175411002fc00000000000000000092127d5910023f0000000000000000008e1579591003370000000000000000008e1579591002370000000000000000008a15795910023f0000000000000000008615795910033d0000000000000000005492795910033b0000000000000000009212795910023f000000000000000000462375591003750000000000000000008de175591003750000000000000000004a21755910027d00000000000000000054a375591003370000000000000000008a2375591003370000000000000000004a2375591003370000000000000000008de2755910033700000000000000000054a2755910033b
  | 6, 4 => 0x463549192002af000000000000000000423549192003ae0000000000000000005e35491920032f000000000000000000423519192002be0000000000000000005e35191920023f000000000000000000921519192002af0000000000000000008e1519192002b70000000000000000009e15191920023f000000000000000000d51509192003ae000000000000000000d515091920038e000000000000000000549509192003ba0000000000000000005495091920039a000000000000000000921509192003ae0000000000000000009e15091920033e0000000000000000005435791920033e0000000000000000004635791920023f0000000000000000004235791920033e000000000000000000d515791920032f0000000000000000009215791920032f0000000000000000008615791920023f0000000000000000005451791920033d0000000000000000005411791920033e000000000000000000d611791920023f0000000000000000009611791920023f0000000000000000005611791920023f0000000000000000001611791920023f000000000000000000423515192002be0000000000000000005e35151920023f0000000000000000008e1515192002b70000000000000000009e15151920023f000000000000000000549505192003ba0000000000000000005495051920039a0000000000000000005435751920033e0000000000000000004635751920023f0000000000000000004235751920033e0000000000000000008615751920023f0000000000000000008215751920033e0000000000000000008215751920023e000000000000000000549508592003ba0000000000000000005495085920039a00000000000000000054137859200336000000000000000000d6137859200337000000000000000000961378592003370000000000000000005613785920033700000000000000000016137859200337000000000000000000549504592003da000000000000000000423564592002be000000000000000000921564592002af0000000000000000004235745920027e0000000000000000005a35745920023f0000000000000000005425745920035e000000000000000000d5a5745920031f00000000000000000055a5745920031f0000000000000000009215745920026f0000000000000000008e1574592002770000000000000000008215745920027e0000000000000000005405745920035e0000000000000000005585745920031f0000000000000000005205745920026f0000000000000000004e0574592002770000000000000000004205745920027e000000000000000000da147d4910023f0000000000000000009a147d4910023f0000000000000000001a147d4910023f
  | 6, 5 => 0x51d07d5920033e0000000000000000005e35195920023f0000000000000000008e1519592002b70000000000000000008615795920023f0000000000000000008215795920033e0000000000000000005451795920033d0000000000000000008224755920036e0000000000000000009a24755920032f0000000000000000005a24755920032f00000000000000000091e0755920036e00000000000000000089e0755920037a00000000000000000091e6755920032f0000000000000000009215455920038f000000000000000000de35155920023f0000000000000000008e1515592002b70000000000000000005524755920038f0000000000000000005524755920032f0000000000000000004624755920023f0000000000000000001624755920038f000000000000000000822475592003ae000000000000000000d464755920032f0000000000000000005464755920032f0000000000000000008624755920032f0000000000000000004624755920032f000000000000000000821475592002be000000000000000000de0475592002af000000000000000000d444755920032f0000000000000000005444755920032f00000000000000000091e1755920032f00000000000000000011e1755920032f0000000000000000005461755920033d0000000000000000005221755920023f00000000000000000091d1755920032f00000000000000000011d1755920032f000000000000000000921175592002af000000000000000000121175592002af0000000000000000008e1175592002b7000000000000000000821175592002be000000000000000000d520755920039e0000000000000000005520755920039e00000000000000000091e075592003ae00000000000000000011e075592003ae00000000000000000011e0755920032e000000000000000000522075592002be00000000000000000089e075592003ba0000000000000000009e15015920033e0000000000000000009e15015920023e0000000000000000005414715920032e0000000000000000005411715920033c000000000000000000551525012003ea000000000000000000551525012003ca000000000000000000521525012003ea0000000000000000009e15250120037a0000000000000000004a3515012002fa0000000000000000005e35150120027e0000000000000000008e1515012002f60000000000000000005495750120037a0000000000000000005495750120035a0000000000000000009215750120036e0000000000000000008a15750120037a0000000000000000009a15750120033e000000000000000000d45425012003ea000000000000000000545425012003ea000000000000000000561425012002ea
  | 6, 6 => 0x12167d4520032f00000000000000000012167d4520022f00000000000000000082167d4520033e000000000000000000d2067d4520022f00000000000000000052067d4520022f0000000000000000004e067d452002370000000000000000005a24754520023f000000000000000000da2375452003370000000000000000005a237545200337000000000000000000422175452002fc0000000000000000005a2175452002bd0000000000000000005636754520029f0000000000000000008df675452003370000000000000000004e3675452002b70000000000000000005636754520023f0000000000000000004e3675452002370000000000000000004226754520027e0000000000000000005226754520023f0000000000000000009616754520029f000000000000000000921675452002af000000000000000000121675452002af0000000000000000008dd675452003370000000000000000008e1675452002b70000000000000000004a3545412002fa0000000000000000004a3545412003da0000000000000000004a3545412002da000000000000000000921545412003ce0000000000000000004a1545412003da0000000000000000009a15454120039e000000000000000000d51525412003da000000000000000000551525412003da00000000000000000054b515412003da0000000000000000004a3515412002fa000000000000000000549515412003da0000000000000000008e1515412002f6000000000000000000552475412003ce00000000000000000054a475412003da0000000000000000005524754120036e00000000000000000054a4754120037a00000000000000000054a4754120035a0000000000000000008a24754120037a000000000000000000549475412003da0000000000000000008a1475412002fa0000000000000000009a1475412002be000000000000000000d52275412003da000000000000000000552275412003da00000000000000000091e2754120037a00000000000000000051e2754120037a000000000000000000522275412002fa00000000000000000054a175412003da0000000000000000001a2175412002be000000000000000000549175412003da0000000000000000008e1175412002f60000000000000000008a1175412002fa00000000000000000054950d592003da0000000000000000008e117d5920027700000000000000000049d07d5920037a00000000000000000054907d5920037a00000000000000000055150d5920039e00000000000000000054950d5920039a00000000000000000054147d5920033e00000000000000000086147d5920023f0000000000000000008e117d5920023700000000000000000055107d5920039e
  | 6, 7 => 0x8614789950023f0000000000000000008e1178995002b70000000000000000009211789950023f0000000000000000008e1178995003370000000000000000008e1178995002370000000000000000005524649950038f0000000000000000005524749950034f0000000000000000001624749950034f0000000000000000008224749950036e00000000000000000011e2749950036b00000000000000000091e0749950036e00000000000000000011e0749950036e000000000000000000d520749950035e0000000000000000005520749950035e0000000000000000005220749950027e00000000000000000089a0749950037a0000000000000000004620749950027e000000000000000000921268595002af000000000000000000121268595002af0000000000000000008992785950033b0000000000000000008212785950027e000000000000000000462278595002bd0000000000000000005452785950033d0000000000000000009212785950023f000000000000000000de35245950025f000000000000000000d4a3745950035700000000000000000054a374595003570000000000000000008de26459500337000000000000000000921264595002af000000000000000000121264595002af0000000000000000008dd2645950033700000000000000000054a2745950035b000000000000000000921528195002de00000000000000000054a268195003da000000000000000000921268195002ee000000000000000000121268195002ee0000000000000000005512781950035e0000000000000000009212781950027e0000000000000000008992781950037a0000000000000000008e117d5120027700000000000000000049d07d5120037a0000000000000000008a107d5120037a00000000000000000086167d5120023f00000000000000000082167d5120033e000000000000000000422475512002ee0000000000000000005a2475512002af0000000000000000004221755120027e0000000000000000005a21755120023f00000000000000000049d0755120037a0000000000000000004626755120023f0000000000000000004226755120033e000000000000000000821675512002be0000000000000000009a147d4520023f00000000000000000049d07d4520037a00000000000000000092107d4520027e0000000000000000008a107d4520037a00000000000000000056367d4520023f00000000000000000092167d4520026f00000000000000000082167d4520027e00000000000000000092167d452002af00000000000000000012167d452002af00000000000000000092167d4520023f00000000000000000092167d4520032f00000000000000000092167d4520022f
  | 6, 8 => 0x5222741b51023f0000000000000000009212741b5102af0000000000000000001212741b5102af0000000000000000008212741b5102be00000000000000000049d078d95103370000000000000000008a1078d95102b70000000000000000008a10785951027d0000000000000000009212781951023f000000000000000000862374195103750000000000000000008e1264195102b70000000000000000008da274195103370000000000000000008da174195103b50000000000000000008de174195103750000000000000000004624749b50023f0000000000000000008a14749b5002bb0000000000000000008214749b5002be0000000000000000005221749b50023f0000000000000000008e11749b5002b700000000000000000082147d495002de00000000000000000082147d4950035e00000000000000000054a375455003570000000000000000004a3548995002db000000000000000000821528995003da00000000000000000054a4689950039b0000000000000000005494789950035b0000000000000000008214789950027e0000000000000000005491789950035b0000000000000000008e11789950027700000000000000000054a078995003da0000000000000000004a3548995002bb0000000000000000004a35489950039b0000000000000000008a1548995002bb0000000000000000008a15489950039b0000000000000000004a3518995002bb0000000000000000008e1518995002b70000000000000000005524789950038f0000000000000000004a2478995002bb
  | 7, 0 => 0x2275591001bf0000000000000000000022755910013f000000000000000000001275591001bf000000000000000000002175591001bd000000000000000000001371591001370000000000000000000032715910013b0000000000000000000012715910013f0000000000000000000012715910013b000000000000000000001525091001fb000000000000000000001515091001fd000000000000000000001505091001fe000000000000000000003565091001bf000000000000000000002565091001bf000000000000000000001565091001bf000000000000000000000565091001bf0000000000000000000035750910017f0000000000000000000015750910017f0000000000000000000020750910017e0000000000000000000036750910013f000000000000000000003544851001fd000000000000000000001544851001fd000000000000000000001504851001fc000000000000000000003574851001fd0000000000000000000025748510017d000000000000000000001574851001fd0000000000000000000015748510017d000000000000000000003548991001bf000000000000000000001548991001bf000000000000000000001518991001bd000000000000000000001508991001be0000000000000000000035789910013f0000000000000000000015789910013f000000000000000000001418991001bd0000000000000000000014789910013f000000000000000000001524991001fb000000000000000000001514991001fd000000000000000000001504991001fe000000000000000000003564991001bf000000000000000000001564991001bf0000000000000000000035749910017f0000000000000000000025749910017f0000000000000000000015749910017f0000000000000000000005749910017f000000000000000000001414991001fd000000000000000000001464991001bf0000000000000000000024749910017f0000000000000000000014749910017f000000000000000000003544991001bf000000000000000000001544991001bf000000000000000000001514991001bd000000000000000000001504991001be000000000000000000003574991001bf0000000000000000000035749910013f000000000000000000002574991001bf0000000000000000000025749910013f000000000000000000001574991001bf0000000000000000000015749910013f000000000000000000000574991001bf0000000000000000000005749910013f000000000000000000001414991001bd000000000000000000002474991001bf0000000000000000000024749910013f000000000000000000001474991001bf0000000000000000000014749910013f
  | 7, 1 => 0x35791920013f0000000000000000000015791920013f0000000000000000000011791920013f000000000000000000003515192001bf000000000000000000001515192001bf000000000000000000001505192001be0000000000000000000035751920013f0000000000000000000015751920013f000000000000000000001508592001be0000000000000000000035785920013f0000000000000000000015785920013f00000000000000000000137859200137000000000000000000001514592001fd000000000000000000001504592001fe000000000000000000003564592001bf000000000000000000001564592001bf0000000000000000000035745920017f0000000000000000000025745920017f0000000000000000000015745920017f0000000000000000000005745920017f00000000000000000000147d4910017f00000000000000000000117d4910017d00000000000000000000107d4910017e00000000000000000000367d4910013f00000000000000000000167d4910017f00000000000000000000167d4910013f000000000000000000003545491001df000000000000000000001545491001df0000000000000000000024754910017f000000000000000000001175491001fd000000000000000000003675491001bf0000000000000000000036754910013f0000000000000000000026754910017f000000000000000000002675491001bf0000000000000000000026754910013f000000000000000000001675491001bf000000000000000000000675491001bf0000000000000000000006754910013f000000000000000000001525451001fd000000000000000000002375451001f50000000000000000000022754510017d000000000000000000001275451001fd000000000000000000003525411001de000000000000000000001525411001fe000000000000000000001525411001de000000000000000000001515411001fc000000000000000000002275411001fe000000000000000000001275411001fe000000000000000000002175411001fc00000000000000000000127d5910017f00000000000000000000117d5910017d00000000000000000000107d5910017e00000000000000000000127d5910013f000000000000000000001529591001bf0000000000000000000015795910013f0000000000000000000012795910013f000000000000000000002375591001f7000000000000000000002375591001770000000000000000000022755910017f000000000000000000002175591001fd0000000000000000000021755910017d000000000000000000001525591001bf000000000000000000002375591001b700000000000000000000237559100137
  | 7, 2 => 0x1525412001da000000000000000000003515412001fe000000000000000000001515412001fe000000000000000000002475412001fe0000000000000000000024754120017e000000000000000000001475412001fe000000000000000000002275412001fa000000000000000000002175412001fe000000000000000000001175412001fe00000000000000000000150d592001fe00000000000000000000117d5920017f00000000000000000000107d592001fe00000000000000000000107d5920017e00000000000000000000354d5920019f00000000000000000000154d592001bf00000000000000000000154d5920019f00000000000000000000150d592001be00000000000000000000147d592001bf00000000000000000000147d5920013f00000000000000000000117d5920013f00000000000000000000107d592001be000000000000000000003519592001bf000000000000000000001519592001bf0000000000000000000015795920013f0000000000000000000011795920013f000000000000000000002475592001ef0000000000000000000024755920016f0000000000000000000021755920017f000000000000000000002075592001fe0000000000000000000020755920017e000000000000000000002675592001bf000000000000000000003545592001bf0000000000000000000035455920019f000000000000000000001545592001bf0000000000000000000015455920019f000000000000000000003515592001bf000000000000000000001515592001bf000000000000000000002475592001bf0000000000000000000024755920013f000000000000000000002475592001af0000000000000000000024755920012f000000000000000000001475592001bf000000000000000000000475592001af0000000000000000000004755920012f000000000000000000002175592001bf0000000000000000000021755920013f000000000000000000001175592001bf000000000000000000002075592001be000000000000000000001501592001be0000000000000000000035715920013f0000000000000000000034715920012f0000000000000000000014715920012f0000000000000000000031715920013d0000000000000000000011715920013f0000000000000000000011715920013d000000000000000000001525012001fa000000000000000000003515012001fe000000000000000000001515012001fe0000000000000000000015750120017e000000000000000000001425012001ea000000000000000000003549192001af000000000000000000003519192001bf000000000000000000001519192001bf000000000000000000001509192001be
  | 7, 3 => 0x474995001ef0000000000000000000004749950016f000000000000000000002274995001fb0000000000000000000021749950017f000000000000000000002074995001fe0000000000000000000020749950017e000000000000000000003528595001df000000000000000000001528595001df000000000000000000001518595001fd000000000000000000002268595001bf000000000000000000001268595001bf0000000000000000000012785950017f000000000000000000001528595001bf000000000000000000001518595001bd000000000000000000002278595001bf000000000000000000001278595001bf0000000000000000000012785950013f000000000000000000003524595001df000000000000000000001524595001df000000000000000000002374595001f700000000000000000000237459500177000000000000000000002264595001bf000000000000000000001264595001bf0000000000000000000022745950017f000000000000000000002174595001fd000000000000000000001528195001de000000000000000000002268195001fe000000000000000000001268195001fe0000000000000000000012781950017e00000000000000000000117d5120017f00000000000000000000107d512001fe00000000000000000000107d5120017e00000000000000000000167d512001bf00000000000000000000167d5120013f000000000000000000002475512001ef0000000000000000000021755120017f000000000000000000001075512001fe000000000000000000002675512001bf0000000000000000000026755120013f000000000000000000001675512001bf00000000000000000000147d4520017f00000000000000000000107d452001fe00000000000000000000107d4520017e00000000000000000000367d452001bf00000000000000000000367d4520013f00000000000000000000167d4520017f00000000000000000000167d452001bf00000000000000000000167d4520013f00000000000000000000067d4520013f0000000000000000000024754520017f000000000000000000002375452001f700000000000000000000237545200177000000000000000000002175452001fd000000000000000000003675452001bf0000000000000000000036754520013f0000000000000000000026754520017f0000000000000000000026754520013f000000000000000000001675452001bf0000000000000000000006754520013f000000000000000000003545412001fe000000000000000000003545412001de000000000000000000001545412001fe000000000000000000001545412001de000000000000000000001525412001fa
  | 7, 4 => 0x12641b5101bf0000000000000000000022741b51017f0000000000000000000022741b5101bf0000000000000000000022741b51013f0000000000000000000012741b5101bf000000000000000000001078d95101b70000000000000000000010785951017d0000000000000000000012781951013f000000000000000000002364195101b7000000000000000000002374195101f700000000000000000000237419510177000000000000000000001264195101bf0000000000000000000022741951017f000000000000000000002174195101fd0000000000000000000014649b5001bf0000000000000000000024749b50017f0000000000000000000035449b50019f0000000000000000000024749b5001bf0000000000000000000024749b50013f0000000000000000000014749b5001bf0000000000000000000021749b5001bf0000000000000000000021749b50013f0000000000000000000011749b5001bf0000000000000000000023745b50013700000000000000000000147d4950017f00000000000000000000147d495001df00000000000000000000147d4950015f000000000000000000003545495001df000000000000000000001545495001df00000000000000000000152d455001df00000000000000000000127d4550017f000000000000000000001525455001df00000000000000000000237545500177000000000000000000003548995001df000000000000000000001548995001df000000000000000000001528995001fb000000000000000000001528995001db000000000000000000002468995001bf0000000000000000000014789950017f0000000000000000000011789950017f000000000000000000002078995001fe000000000000000000003548995001bf0000000000000000000035489950019f000000000000000000001548995001bf0000000000000000000015489950019f000000000000000000003518995001bf000000000000000000001518995001bf000000000000000000002478995001bf000000000000000000001478995001bf0000000000000000000014789950013f000000000000000000002178995001bf000000000000000000001178995001bf0000000000000000000011789950013f000000000000000000003544995001df000000000000000000001544995001df000000000000000000002464995001bf000000000000000000001464995001bf0000000000000000000024749950017f000000000000000000002474995001ef0000000000000000000024749950016f
  | 8, 0 => 0x41b5100ff0000000000000000000000041b5100bf000000000000000000000008d95100f7000000000000000000000008d95100b7000000000000000000000008595100fd000000000000000000000008195100bf000000000000000000000004195100ff00000000000000000000000d4b5000df0000000000000000000000049b5000ff0000000000000000000000049b5000bf0000000000000000000000045b5000bf00000000000000000000000d495000ff00000000000000000000000d495000df000000000000000000000005495000ff000000000000000000000005495000df00000000000000000000000d455000ff000000000000000000000005455000ff000000000000000000000008995000ff000000000000000000000008995000bf000000000000000000000004995000ff000000000000000000000008595000ff000000000000000000000008595000bf000000000000000000000004595000ff000000000000000000000008195000fe00000000000000000000000d512000ff000000000000000000000005512000ff00000000000000000000000d452000ff000000000000000000000005452000ff000000000000000000000005412000fe00000000000000000000000d592000ff00000000000000000000000d592000bf000000000000000000000009592000bf000000000000000000000005592000ff000000000000000000000005592000bf000000000000000000000001592000bf000000000000000000000005012000fe000000000000000000000009192000bf000000000000000000000005192000bf000000000000000000000008592000bf000000000000000000000004592000ff00000000000000000000000d491000ff000000000000000000000005491000ff000000000000000000000005451000fd000000000000000000000005411000fe00000000000000000000000d591000ff00000000000000000000000d591000bf000000000000000000000009591000bf000000000000000000000005591000ff000000000000000000000005591000bf000000000000000000000001591000bf000000000000000000000005091000ff000000000000000000000004851000fd000000000000000000000008991000bf000000000000000000000004991000ff000000000000000000000004991000bf
  | 9, 0 => 0x351007f0000000000000000000000000151007f0000000000000000000000000350007f0000000000000000000000000150007f0000000000000000000000000120007f0000000000000000000000000110007f
  | 10, 0 => 0x3f
  | _, _ => 0

def slotCount63 : Nat → Nat
  | 4 => 32
  | 5 => 2048
  | 6 => 16384
  | 7 => 8192
  | 8 => 1024
  | 9 => 64
  | 10 => 2
  | _ => 0

def indexWords63 : Nat → Nat → Nat
  | 4, 0 => 0x24000100000000000000000000000000000000002900230021000000260000000000220028002c0000002b000000250000000000000000002a002700030000
  | 5, 0 => 0x409000000000647000000000000000000000c210000000000000000000000000000000000000000000007e100000000060802e6044a040300000ce80c0b058a0aa300000000000005a2000007e702ac04060e2301420584000000000821050504450444040c000000000487000005c10000000000000000000001e4
  | 5, 1 => 0xda30000000000000000000000000000000000000be306a200000746066200000000000000000f060000000002a9060600000dc1000000000e0100000003000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000076400000523000006640000000005eb
  | 5, 2 => 0xe2000900e10021000000000b01000009ea0000000000a20000000004c7000000000187000003a300000000000000000804032c0000086300000000000000000f24000000000881000000000be50a61050b000000000be4000004250000000000000f270ec1046805880b8301620a0800000f020000000006490d640c030000
  | 5, 3 => 0xd410000000000000000000000000000000000c605e7000009810000070306c1000000000000000000000ea8068204a700000000000000000000000002a500000c020000028100000000000000000000000000000000000000000701000000000b0401c100c30000000000000000000000000ea20c050b820802068403aa036a
  | 5, 4 => 0x2a40f0c00000000060a0000000000000d660c0100000000020800000ce40000000000000bc20866018100a10d8100a402ab0000056c04cc000008a9098b000000000348028309450000000000000000020609e500610000000001020b8608c600000000000000000621000005ca03c90000000000000ba1000000000ea30000
  | 5, 5 => 0xb42000b0cc1000000000a28000000000000000000000e210000000000000000000002620ecc0000000000000000044200c40000000000000000000004830bc80d4400000000000004a1000002430882050902aa02660000018200000d6809a90ea500000000000000000e0403e10dc800000ec80d240ac1064b018a040b04e1
  | 5, 6 => 0x2a2000000000000000006c606aa034100000de4000002a30987000000000be70000000007e80543038702e5074402020000000000000000000007680d2208ca000000a30246000003820000000000000585030602ec0426032b0b48084307a206ac05cc00000e830c420b2106c808c5058306a6072804050646044300000000
  | 5, 7 => 0x92805c405e400000000000700000f04068b00000aa4000000000000000000000000042b000005630000000000c20aa801a3000000000708000000000000000000000e8a0602000000000000000000000e8500000000000000000e8c072c0b8105a6004306010000000000000be80a2406a9040203e70169008303ea
  | 5, 8 => 0x3ca01a203470ec9000000000000000000000000098504670e0a000005890000042208610762000000000000000008e10228000500000eca0689000007610000094a00000000068a05680000000000000a84062600000de200000000000000000de3000000000000000000000d830b660c2607a100000000000000000000
  | 5, 9 => 0xe46058c01c502a601880f280f2100000000000000000000000000000000000000000302018c03e400000000000000000a0702070702060c00a609890507000002c400000ec40000000000000a09000003450f0b0000000004c2000000000c8507040b030c81068101e200000ea10da404070366036500000000000005c90000
  | 5, 10 => 0x92303680000000000000000000000000000000000000c0c0000000009a20da20000000000000000084606410e060000016300000000000006ab000006050a0c06c4000000000000000001cc00000ee500000905000005a8068601e6062802e8058103c7000000000000000000ca03a502e4000005450a48038c000002eb
  | 5, 11 => 0xb2600000f0300000000000000000000000000000000038600000e0c0000000008620a88062c012c000000000000000000000000000000000eaa000004e900000000000000000ce105c5010100000eac00a80d430ac30a0600000000000000000ae40c890e81000000000000000004210388000000000c090000000000000000
  | 5, 12 => 0xf2307a60000000000000ee20f0100000e4500000000000000000000062a0000032400000da8066603c80286016a0c0403c3000000000bc300000000060b01e30342000000000143000000000000084400000ac202c30529042704c40d05000001c80a0b0000068300000000000006440000000000000be207480c620c0804e7
  | 5, 13 => 0x8c9000000230f2600000000000000000bc509c5000006a700000c2505690000000003030000000003a603ec0000000006e8012800000000000005a90e8407060bca000000000000000000000000000000000e0b0f250bcc00000dc60bec02c80d46020c00c8000000000d0a00000000050300000000016c
  | 5, 14 => 0x4890e05000001c400e3000000000168000005ab000000000226000000000000000000000ecb01e102e1012a000004e302a700690000000000000961016603e9048502e702c600000000006b0a83000000000a22000000000ea70d2100000742048b000008a10822062906420000004100000000000001a6074101c3
  | 5, 15 => 0x68500000da10185000000000000000005210e410c060aa205cb056b04cb0000000000000000000000000000000000000a810e28058600000000076302c103a90565000000000dc3054b0b88088601210be10000000003630103000000000000000000000000000000000d610000072b0501000007e90124
  | 5, 16 => 0x5620000000008a20beb000003e200000000000008640000046300000f2b0000024806a3056a0000000000000000000000000ba60b2209aa0000000000000126036c000000000f2a0e87058701860e2200000000000000000000040a00000000000000000ea90e4a09c20ca108aa0841032805a3044904080eab0369
  | 5, 17 => 0x7eb03890c8204c100000e610441000005470000020a0000098300e80ce300000bc90e2604c90bc1030406220726046a0000000000c70bcb034900000000000000000000000005a500000aa102040cc203ac00000167000000000000000000000000000000000000000000000000000007e20000000000000d0606e10424018b
  | 5, 18 => 0x72400000000000006870d820a41094600000000000000000ec70ba209e606c3016101ca01a1000000000ac40000000000000e820e080bea05c70a8202090c2a000000000000000009e90000000000000205000000000901058b00c5000006e200000000000000cb00000ee10000000003250b4400000ca205ac000000000000
  | 5, 19 => 0x22106a500000000000003e5012b0000000004230f22000001cb00000000026101480ec500000000000000000000000000000dc20000000000000000036400010081000000000806000000000a0501460326000000000d88000000000000000000000000000000000ae6060401230000000000000ee60000000006e300000000
  | 5, 20 => 0x743020300000000028208a50c4a00000de60d2603c60000000009630000032301c700000000000004ca0000000000000000090a014101c600000cc503eb000000000000000004480384000000000000000000000cca09ca04c5000000000d010301000000000c2206a4036b00000ac6000000000000060905e605c600000e49
  | 5, 21 => 0x64800000361000000000f0706450000000000000000012200000a26064c0566052700000000000000000be6056704c807220466046502680000000000000d42000000000000000000000000000005a1042802e2000000000d630c0a02e900c1000000000000034c0000000000000000000000000e090a210a03
  | 5, 22 => 0x7ec052b0000056400000000000000000000000003830bc7000000000000000000000ae307e407e30727000000000ee904620000000000000000000004690e86068c05e304460362024402e30108000003210000000000000000000002880000000003e60ae1092200000000080100000000000000000e03012509a600000000
  | 5, 23 => 0x4640c410000040100000000046b000001a8000000000924032a0000000000000a66000000000b62000003c400000a4400000b4309c608c1000000000000000000000000022200000000000000000000000000000000000000000de80c66062500000000000000000000000000cc0b84000001440b41038a0c6109a509a1
  | 5, 24 => 0xc45092604eb0164000003a8000000000eea03810cc6042a0a0a00000c8a00000000000000000000000000000000000000000000000000000000000009060000000000000000000000000000044b02a100e40dc40000000000000b060688000000000000000005e905aa0000000000000184000000000949062400000603
  | 5, 25 => 0x1e800000aa6034602010224012700000a46000002a804e500000000000000000000000000000b610000006505e205c2056100000da600000d280000000000000165000000000000000000000a4300000d840106000006e600000cc909c903a40189000000000e6a0e6603c5064305250000000000000000000000000000
  | 5, 26 => 0x1830a01066100000000000003ab01c2032900000ae800000000064a000000000ea6012906680322080305e504c600000000000000000000000000000ac8000000000000054100000e4205e100000000000005a70000000008230263000000000d6200000ce607c10000000000000e070000000000000000
  | 5, 27 => 0x54900000000000004a5000000000000000008e60e02000003a703270000000008080000000000000582000008420000000000000000000000000000034b07230a23022300000000000000000000000004a900000000000000000f0500000000000000000828000003430067000000000000000000000000000000000848072a
  | 5, 28 => 0x8e20000000000000e69000000000b0200000000000005a403c1000000000000000000000ec30000000002ea0ec2000003e800000000000000000f09048100000bc6034a0627000000000308086800000ec60a620e240826076605c805e803cb000000000f0a000000000242000000000000000000000c460623042c000007ea
  | 5, 29 => 0xd860f2c044c094206630367060704040000000003e3016b09e206c200000000000007e5000000000000000000000000000000000000000000000a020104046106e4000000000000000000000e620385000000000000000000000000090205c303c203cc06a800000000000000000d48090900000000034400000000000004c3
  | 5, 30 => 0x62b038b0000000000000000000000000a420f080000000000000000000000000f29000000000000072900000b46028400000b0801a40a0400000000000000000000026400000ce204a30000006305ea04290000000000000000046c000000000000000000000000000000000921000000000000000000000000000000000ea4
  | 5, 31 => 0x78300000c49094100000000000000000d23000009e106a1000000000c2901c90e890e880d020ca60c070be902c20bc40781072507210d090c86000005ec0e8b00e60e6500000000000004ab08c2000000000000000009c107e60447000000c903a203a1000000000ae2000002410de10000020b0a8608a60824
  | 6, 0 => 0x10850000000000001e01182a0000000000000000000019cb43e82be31aa137aa1e211ca812c1022201220ee10000000000003bea00000cc100000000000000003d6837a81c2729e80000000000000000000000000000000000000000000000000000124b0bc50000000000002aa9200a0000000000001ee9000000000000
  | 6, 1 => 0x2a2000000000000000000000000000000000000000000000000000026e1182911210f66000000000000000000000000000000000000000000000000192c00001ea200000000110600001943000000000000000000000000000009cb0000000020e200000000000000001e06000000000000
  | 6, 2 => 0x2bc31a810b0542e7190b0e210ce137080000000000002d89142101421a0a0000000000000000000000000000182b000000000000000003e30000000000000000000009e515cb000000000000000000000000000000000000140500001a450000000000000000000000000000000000000f6b
  | 6, 3 => 0x39c4292324a718e93d4c000000001c89000041850000184400000000000000000b260000000000002aa1206100001145000041060000000000002dc20000000000000000000000003ce7000000000000000000000a072c2100000a0800000000000000000000000000000000000000000000000000000000000000000000
  | 6, 4 => 0x8e40000000007c1436227611b631789140b0000000000000c07000000000000302400000000000000000000000037841fcb00000000000000000f22000033ab000019210000000035221769000000000000000000000000000000001d821961000000000000186c00000000446b11812563000000001166000000001dea0aec
  | 6, 5 => 0x3086000000000000000041210000416a000000000000000000000000000000000000000000000000000007240000258317a608e60546000011c80000000000000000000000000000000036c300000000000000000000000027280000000000000000000000000000000000000000000000000000000000000a4700000000
  | 6, 6 => 0x2c9000015471ee52c23000022e800001e6700000000000000000000000000000000000012070000000000002922000000000000000000000000000000000000000000000000222400000000000000000000000000000fa800004448222b000000000000000007ac00000000000000000000076200001f450000000000000d42
  | 6, 7 => 0x19e30000000000000000000000000000000000000000000000000000000000000000000000000000442a0000000000002c22174900001e041721000000000000000027a60d4100003be21ce12d06000000003f0a0000000000000000000000000000000000000000000035050000000000000000000037a2154c
  | 6, 8 => 0xea000037420000000029290bea0000000000000000000000000000000000000000000000000000000000002b822b4227841d090aac180900000a4a3365000035431fa63c090e0c43a5294500003cc80000000000000000230820e3426c000000000b8c0a050000000000000000000000000000000000000000000000000000
  | 6, 9 => 0x7c400003205090b000000000000000000000000324500000000000000000000000000000000000000000000000006c600000000000000000000000000001ac400000426000000000000000000000000000000002a460000000000000000000000001f410ecb00001ecb0000000000000000
  | 6, 10 => 0x28a21fc328c10b6620450b643d631e08184100003de7000031a94081000006c4434c3bc60000000000001de213c1108409c209233fa500003c2b3046188b0000000000000000154300003cab0000000000000000000000000000000017010000000000000000000000002ce1236122031b0b3cec000000000000000000000000
  | 6, 11 => 0xd060000000000000f87000000000000000019cc10c10dc60000000039c100000000000010e10246000000001c87000000000000096c3c4431ea2bc4000000000000000000000000000000000000000000001ec90000000003a600000e490000000000000000426822823c8c3e49344140a128c5
  | 6, 12 => 0xb810000000012060e4b44693524176b160c406a110700000000000000000000000027870000000027042821000000000000000000003886272219ca000000000000000000002ca4000000000d63000000000000000000000000000000000000000000000c650000000000003964000007a70000000000000000
  | 6, 13 => 0x22e30b25080900000000000000001ce7000000000d66000000000000000022e5000000000a4b0000000016a91c46000000000000000030620000000000000000000000001ea10000000000000000000028ea00000000000005a40000342632ca0000000000001de40000000000000000000001a3000000001cc61c8600000000
  | 6, 14 => 0x3080000000000000f6500000000000000003d67000000003aa30000000000000000000000000000000000000000000000000000000000000000444416630000100100000000000000000000000000000000000000000000000000000000360800001ae10000000002c2000000003b620000000000000beb0000000018a1298a
  | 6, 15 => 0x9ec2ce6000000000000200b346122423f29000000001d67106a000011a9000000000000000000000000112500004009276200000000000000000000000000000000000003c60000000000000da2000013290000000000000000000036a100000000000000000000000000000ae300000f0c0000000000001b493fca09850000
  | 6, 16 => 0xfea1ecc000000000000000000001dc70000000000000000000000000000000000000000000000003d080d24000000000e02000000000000420100000000000000000b0a16030000000000000000000000000000000000001fe935c1278a000000000000000000000000142910620000000000000000000032812de22861
  | 6, 17 => 0x2842903000000003d6b0000000000000000000022c122861c0b0bab000000004303000000000000000000000000000000000000000027ca0ae83f4a3e422b0200000000000000000000000000000000000000000a6100000000390100000000000000000000000000000000000000000000000000000000
  | 6, 18 => 0x3a41b4b00003786000000000000000000000000000000003926304112a4000000000000000000000000000000000000000010a83186000000000000000000003da2000000000bc900000000000000000000000000000000000011e4000000000000000000000d650be10000442b0000186100003d8116ca0000
  | 6, 19 => 0x1f8600001a02000003a30000000000002183000000000000000016a216a600003ce506210000160a0000000000000000000000000000000012870000000000001f240000000000000000000000000000000000000000000000000000000000000000000009a5000000000000000000001e660000000000000000000000000000
  | 6, 20 => 0x3eaa33a6000031c900000000000000000000000000000000000000000000000000000000000000000000294914c1000000000000000000000000000000002b4925e521621d49000014e900000000000000003c020000000000000000000000000000114b00002ca800001f2b00000000000000000000000000004063130b3dea
  | 6, 21 => 0x414235e113873e41000000000000000025481083000021a70e88000000001688312619a9000044063e6a39c60000000018a20000000000000000000020c11d87000000002a020000000000001ac2000000000000000000000000000000000000000000000f210000000000000000000022660000000000000000000000000000
  | 6, 22 => 0x27e221e304c3362800000000000015e70000000000000000000000000000000015420000000000000000000000000000402931671ca506841de70000000000002d040000000036a8000000000000000000000000000000002c680000000000000000000000000000000000000000000000000000080a19290000000000001b83
  | 6, 23 => 0x43ea0000000000000000000000000000000000000000000000003a851ec42341000000000000000000000000000000000000378100000000000000003baa0000000000000000000032010000000000000d0700003241276800000000000000001d880000128928c90000000000000000000000000000000000000000
  | 6, 24 => 0x28a909681cea00000000000019e70000338913c6000010a500000000000000000b090f0a0000000000000000000000000000000000000000000018273101000018830000000000003d85000000003f453d040000000042880462000036820000110400001ca30000000000000000000000000000000000000000000031e90000
  | 6, 25 => 0x1a8b0a690000000000002646000000000000000000000000000000001d6c212100003c422bc2000000000000000043ca0000000000eb00000000000008840a220442000000000000172804a83b6a000033e133c32124000000001cca00000000000016cb000040443c8233492a222508070110262fa42b66
  | 6, 26 => 0x2e610da50000000000000ca40000000000001ca20000000000000000000000000000000000000000000000000000000000000000000000000000000000003164000014a33fe2000000000000000000000000000000002e48406b31c5394600000000370600001a230000372213a300003ccc0000
  | 6, 27 => 0x2be4000037460e440c2200000000000000001ccb00000000000014010744000000000000000000000000000000003f05428600000c6400000000000000000000000000000000000000000000000000000000156b00000000000000000000000000000000000012ac000000000282430125c100000f0500000000000031a30000
  | 6, 28 => 0xd6200002d64000000000000294200003fa300000000000000000000000000000000000000000000000014c73648000000000000000018690000000000000000000000000000000010c50e650dc20e24000000000000000010e5024200003fc913630000000000000000000000000000000043420c8c0000000000003c64
  | 6, 29 => 0x881000000000000000000000000000013e1000000000000000030c60000000015c30000000000003922000000000f44000000000e0317e600000faa0000000009e800000000000040c50000000000001e8b00000000000000000000146500001da61bc71fe30000000000000000000000001f8a00000000000000000988
  | 6, 30 => 0x3624000000000000000041a10000000000000000000000000000114c000020880000000000000000000000000000000000000000000001e10000000000004281000000001d690000000043e919470000000000000000000012e90ec40000000000000000000000000000000035ea000040493fc400000000000000000000
  | 6, 31 => 0x346212030000000000000000000043050000000007840000000000001d81080c000000000000000000001f0c00000000246316a700000000000031040000000000000000000000000000000000003a4100000000000000000000000039230000000000000000000000000000000000000000000000000000446411a3392b31cb
  | 6, 32 => 0x17e1000000000000034301633828000008610000000000000a8c3b0100000a481b8800000a82000018860221000043c8000000000000000043c606032f410000000000001a4c0842000000003d0b1361000000000d81000000000000000000000e070000
  | 6, 33 => 0x6640000000000001129000000000000000020690000000000001a8c000000000000000000000000000024c3176100000000000000000acc0000000000000000000000000000000000000b4605c604aa000000000969000000000000000016c138a700001a6c1bac09840464000000000000000039080000
  | 6, 34 => 0x3dc2000000000000000000003788000000000be8020408c1000000001887080b000000000441000003c8000038630000406c0000000000002f42000000003d260000000003a7000000001e610000000038030000000007230000000000000000000000000000000000000000000000000000000034ea00231d270ea71d470000
  | 6, 35 => 0x1daa00003fa10000000000001b260000000000001ec10f03306500000000000000000000010100003fc84346000000000000000044810da3444c33620000000000002e8200003aa2000000002947000000000000000001e60b231de60000000000001bcb0d670000000000000000000000000000000000000000000000000000
  | 6, 36 => 0x6c20000000000003d6900000c4100000000000007861e620000000000003dc722440000000032e50aa9000041091b6a0000218619a317840000000000000000000000000000000000001e850c8500000000000000000b890000000004c1000000001ac60000000000004062000000001fc4000000001ba6
  | 6, 37 => 0x384819e50000000000000000000000000000000000000000000019e8000004e2000000000000000000000000000036e30fa9000024e20000000000002f0100000000000000000000064400000000000007a3000043291142000018a400001ca71c221002000000000000126500000000000000000000000000000000
  | 6, 38 => 0x138b00003da735ec15e90e8c0bc304a700000dea00000000000000003d2300003cc900000000000010c601c8000000000000000008880000048800003cc100000000000009c10000000043c10f070000000000002522000029e7000000002b4342c62d483c6c3f68000015eb0da73ee1
  | 6, 39 => 0x1fcc000038460000000034a9372103242e81000000001c013d431624000000000000000016c400000000000000000000000013e30000000000000000000017c205820de9000000000000000000001ac317e803630000290503680000000000000000254400000000000026410eeb00000000122a11c33dc6304322e11d060c49
  | 6, 40 => 0x2062000000000000000000000000000000000000000000000c6a0000000000000000000000000000000000000000128b0000000000000000000000000000000000000747000000000000000000003ac52723262a0000000000000000000000000000108208830e2900000000000000000000000000000000000000000000
  | 6, 41 => 0x2cb000000000be40000000000000de200000000000000000000000000000000000000000000000000000000000000000c6b000000000c883e01000000000000000000001c4b00003ee93d87000000000000000000003e862ac607a6000000000000000000001fc100000fc3000000000000000000000000000000000000
  | 6, 42 => 0x1e280000000011a11f8b1f481d8b1e4806a810ac000042e51f6b0ca9000000000000000000003f81000000000000192824a9110900003c490ac62c821aab00000000000000000000000000001dec0d050000000000000a290000000000003c622be200000000000000000000116c000000000000000000000000
  | 6, 43 => 0x3de3000000001aeb000000000000000000000b8a278b0b87000000000000000000000000000000000000000000000000000000000000000000001f8100000ce900002ec900000000000000000000000000000000000000000000000008e800000000000000000000000000000000000000000f4a000000001725000000000000
  | 6, 44 => 0x7000000000000000000004465000000000000000033861de900000000000000000000000000000000000000000000000000000000000000000000326600000000000000000000000000000000000000000000000000000000000000000000000042e60aaa0000000000001744104204c4000017a72b41000000001b621b02
  | 6, 45 => 0x1a410000000000000000000000000000000000000000000000000000000000000000000037c200000000000038880000000000000000040600000f280000000000003f880000000000000000190c0000428b000000001c080fe80000000000002aa200000000000041e100000000000010e6274200000000000000000b621c69
  | 6, 46 => 0xa66396300000ee2000000000e2c0000000000002ba41d2b00000000000000002b250000000000000000000000000000000000000000000042e100003f84000000000000000009670000000000000000000000000000408600000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 6, 47 => 0x43c70000000040432c460000294b000009c300003c810000000000000000000000000000000041690000000000000ea80e0b0000000000001d02184611a80a441f2300000a2700000000000006c1000033e30dc7000021a30000000000000ac8
  | 6, 48 => 0x10e302480000000000000000000028660000000000000000000003c43aa800000000000000000000000000001d0800000000000000003d66266114ab0000000000000000000000000000000039e200001d6100000000000000003489000000000000000000000000000000001188000005e700000b241ba14445184206e50000
  | 6, 49 => 0x440400000000000000000000000000000000000000000000000000000945000000004483000000000000000033a70000000000000000000000000000000000000000000000000000000000003ee52d0800001a040000000035e4438310c30dc80b6500000000000000003d050e86
  | 6, 50 => 0x3ca536c60e48000000003141000000000000000000000000000003042243000000000000000000000000000000003f8b000000000000000041822a89352140c623813c4a1f6334ca018a2c862b841d0b39210000000033290000000032a9110a0000000033690000000000000000000000000000
  | 6, 51 => 0x8260000110c0f8a00000000000000000000000037440000000000000000000000000000000000000000000000000000000029090b040000000000004347000000000000000000000000000011e60000000000000000000000001e6500e700000000000000001e8a11432a4100001369000000000000000000000000
  | 6, 52 => 0x42ea00000000000000000000000000000000000000000000228100000000000000000000000043a23826000000000000204700000000190a00000000000000000000000000000000000000000000000000000000000033e80000000033450c010000000043870000000000000000000000001baa108900002181000000000000
  | 6, 53 => 0x21a500000000000000003f2100001a4900000000000000000000000018660000434b000000000000000000000be200000f840000412700000000000004e80d44000005e8000000000000000000000000000000000000000000001c881cc8000000000000412a0000000000000000000000000000000013a90000000000000000
  | 6, 54 => 0x15250000000000001c470c06000000000000010400000000000000000000000000001da500000000000028820000000000000000168c0000000000000000000000000000000000000000000011c20000000012a9260320e60000000000000d220a8900000000000000000000090700000000148b0e410ca10000398a2ce90000
  | 6, 55 => 0x1ac10c09000000000000000000000000000000003fcc440200000000000000000000000000003d060d21000000000000304200000000000000000906000000000000230400000000000000002e260000316608c80000000000004206000000000000000000000000000000001d05154a000000000000198900000000
  | 6, 56 => 0x1f0503a9000000000000000021c200000ea3000000000000000000000a840cab00000000000000000000000000000000000000000b020aa242ca0000000000000000000000000000000000003b86358217e917c9144700000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 6, 57 => 0x336100000000000000000000000000000000000000001e41000000e11a4b0a621544000012cb00000000000000000000386400000000000000001b6910ab000000000000000000000000000000001cc2078c1c820000000033a2000004a1000000000000314421a400000000000000000000000000000000000000003da4
  | 6, 58 => 0xacb3d4a18eb0000000000003d8600000000000000000000000000000000000000000000000000000000000000001a6b0000000000000000000000001963000000002b210000000000003b0200000000000000000000000000000000000000000000000000000000000000000a8b4165000000001862000000000000
  | 6, 59 => 0x16270f0900000ec60000000000000000446a0000000000000000196200000daa00001a8400000000000000004021000000000000000000003c6503821d6b00000000000000001d42180200000000000027430000000000003c692d4200000000
  | 6, 60 => 0x40651fea0000000026010000000000001a0b3de919c100000000000000000000000000000000000000002a25000000000000228400003be54126000000001b8b00001ae50000000017a500001385150b0000000028230000000000000000000000000000000000000000000000000000000000000000000000000000
  | 6, 61 => 0x15650000000000000000000017a80548000000000000000000000000010600001be72e24000002c142040e473c2208283a08000000000ca7000000003ca20d0a0000000000000000000000003c452fa1124400003d6524c817c616610586018b12a500002fe10dc3000000002d21000000000000000030610000000000000000
  | 6, 62 => 0x1fac09a4000000000000000000000000000000000000046a10e8000000001a2900000000000000003de10000000000000000000043cc000000003fe84368178c10610000000000001cac08660fa40000000000000000162c404c0000000030a20000000000003cc400000000000000000000000000000cec000030e6
  | 6, 63 => 0xde100000000000000000000000000000f4b18631aa70783000000000000000000000000000019ec0000000000000000000000000000000026a600000000000000000000000029e3000000000000000000000d0107a9000000000000000000000f8600000000000000000000074a00000000428739c30f4500003d451f4b1847
  | 6, 64 => 0x1ea90000000000003f062da60f8b212200000000000000000000000000000000000000000eac00000f6800000000106b0000380231ab3941262237a90c2603a20000000000000000000018ac000000000000
  | 6, 65 => 0x1689000000001a870000000000001767000000000000000000000000000000000000000000000000292400000000000000000000000000000a410328000022e400000fec0000000000002dc30000000002433d0934e900000000000031881c490000344209083ac2000000000000096209830000000002c800000000
  | 6, 66 => 0x3fa916870000000043650386000000000000000000001d4618060000000000000000412420a4000000000000000025c200000000000037a6000000000000000000000000000000002e4100000000000000000000000000000000000023211d251d4538a11ac83b26000016ab00000000000000000000000000000000
  | 6, 67 => 0x7c63528176c000000000000000031ac000000000b6b186a0000000000003006000000001fc9000000002f25118200000000000000003f42000000000000000008640000000000000000000000000b4405c404ab0000000000003d2a16ea09260a670000196600000000000016e70000448b00001a61
  | 6, 68 => 0x2a29000000000000000000000000206b194900001b8100000000000000003a2800000000000000000000000000000000000000000000000000000000000034a600000000000007a4000000000000000000000000000000000000000043e3000042a13d2935260d0b2d23176a16e901890ac5
  | 6, 69 => 0x29210a46048417eb0b6943ab000000000000000000000000000000003fe4000000000000106900000000000000002c4200000d88000000001e8900000000000000003723000000000000000000002b48180c0000000000000000000021283c0c06244344000000000000000000000000000000003d03000000000000288a0000
  | 6, 70 => 0x10a70000000000001fa80000000000000000000000000c4c00000000000000000000000006460000000000002948000000003a860000000000000000000000000000000000000000316a00000000000000000000000000000000000000000764324219c700a70000144900002b6100000f060000000010a600001269438b1826
  | 6, 71 => 0x3a66000000000000000000000000000000000000098a0000000000000000000000000000000000000000000000000000000000000000000017c50b45000000000000118b000000000000000039a11e682f830000000000001a620000000000000000000000001feb000000001ae400000000000000000000184b
  | 6, 72 => 0x25030ce4006303830000000000000ce8000000000143000000000c870d2a000000003a02000000000000000000000000000035a82a2a172c0b4c00000f2c000025ea000000000000000000000000000000001c03000000001f680000000043230b2a00001e0c0000000000000000000000000000
  | 6, 73 => 0x2fc6108600000000000000000000326a210c3f410000000000000000000000000000000000000000000000000e85392500003dc4306a2ec6286a000021ac1888000000000000346a00000000000000000fca000000003f6206e1000000000000000000000000000000000fa5000005a30000412b00000000000000000000
  | 6, 74 => 0xfa60000416200000000000038aa0000000033a3218400001b670a2804482106316100001bcc00000000000000000000000000001c040fe4000000000000000000000000000033221b0902a3314a0000170700000000000000000000000025c60e62000038a43884000000000000000000002d24390b
  | 6, 75 => 0x1ac90000000029e9000000000000268211840000000000000000000000003289120400000000000000000f26000000003ec13b89202922c300000000000000000000000000000000000000000000000000000000000000000000000000000000000000003faa00000fe500000000000000000000000000000000000000001821
  | 6, 76 => 0x18e143c30000000000000e050000000000000000000000000000000000004423028c00000000000036e6000000000000000000003aa6000000000000000000000000000000001a2c000003460000028a000008070000000002e200000000000000000000000029c12982000039e6000042c2256408a40000348a13ca1aa40000
  | 6, 77 => 0xa2b00000000000000000000000000001d8400000000000039281ee300000000000000002669000000000481434a07c80000000000000b6a000020840ac3000009ac00c1084825e6000000000000000000001507000000000000000031c71a0100000000000041460000112a000000000000000000003d024284
  | 6, 78 => 0x43a82b2a0000000000004166000000003fac3dca2ce523653feb000009210000000000000000000000000000000000000000256600000000000007410000000000000000434938661e821ea500000000000000000000000000002aea31aa0000000000000000000000000000000000000000000000000000
  | 6, 79 => 0x16e800000000000000000000000000000000000000000000000000000000000000000000000000000000000038a50000128100000000000000000000000000000000000000000000000000001604000000000000120921a100003f460f2907a500000000000039290423000000001f820000000000000000
  | 6, 80 => 0x428c3e8a0467000000002068210400003506000000000000000000000000000000000763086300000000000000000d0c0000000000000000314b31210000000000000000022300001e880000000000000ea1000000000000000000000000000000000000000000000000000000001f29
  | 6, 81 => 0x3f8c0f250005000000000000000000000000000000000000000000000b8b00000000000000000000000000000000000000003542000000000000000000000000316900000000000000003ce400000000000000000000000000003e2220a82a8200003c8b00000a6c00000000418900000000000000000000000000000000
  | 6, 82 => 0x1fc7000000000000000000000000000000000000000000000000000000000000000000000c4616c5000000001021000030210000000000002966104402a100001c281008000000001b041b640266000000000ba6000000000000124100001c6b00002c482b641ceb04a30aab3f493e462b060000000000000000
  | 6, 83 => 0x36c725680000336a000000000000000000000000000032253ec22ac92ea2000004e10000000000000000224643e60000000000000000000000000000000000000000000000001205000000000ae43b8a3b4200000501000000000000244100000000000000000000000000000000000000000000000002280000000000000000
  | 6, 84 => 0x330500000000000000000000000000000000000000000000000000000000000000000000000000003fa4000000000000000000000000116b000021e100000c041a25000016490000000020e830ca000000000000000000000000000001a100003a2700000a64000000000000332a0000000040e1
  | 6, 85 => 0xb4700000000036200001f2100000000000000000000000000000000000000000000000000000000000000000b632f2a00002a260000000022631d2400000000000011030000000000000000000000000000000000000000000000000000000000003ea10fe700000000000040a2000000000000000000000000000000000000
  | 6, 86 => 0x13eb000000003fec0000000038e621c808860000000036460000000019a7178800000000000000004225000021e8000000000000000000002e431622000000000000000039a506860bc10000000000000000000000000000000000000b6806c8000000002c624285000000000000000000000000000039a21a6717c7
  | 6, 87 => 0x14e3000000000000406700002ea600000000000000000000000000000c020000000000000000062200000000000000000000000017e23905162b158b00001f470000000000003f83000000000000000000000000000000003e8100003c2300000000000000000000000000000000000016410d6b000000000000340600000000
  | 6, 88 => 0xc8900000000000000003dcc256100001d280000000020c60822000002610000000033e408a800002ec20000332600003509000015450000000000000000000000000000000300000000000000000000108b000018c316e100000000000000000000000000001ba31d0300003a29000000000000
  | 6, 89 => 0x30a60000152300001c6c1066000024260e671fe80000000000000dc90000000000003c260e6600003b293146056221a600003ca61208090a11aa0d8b00000000000000000eab0fcc00000000366100001b4c0000000000000000000000000000000019c50000000000003e290000000000000000000000000000000000001d04
  | 6, 90 => 0x9a80000000000002f0606020000000000000b6100000000000000000000000000000000000000000c2c000000000000140300000000000000000000000000002da1280921eb000000001ccc0aa60000000036c420491b2c00000000410a2c843c4b000000000000000013c43fc73dc820eb03440648
  | 6, 91 => 0x2fc300003ca700000000000000004045000000000000000000000000000000000000000000000000000000000000000000001bc800000000000005e300000000000000000000000025490000000000001602000012eb12680000000000003d0100004401000000003a22000000001f0100000000412538c20000
  | 6, 92 => 0x1003000000000000000000000bc70000114640a52de126e900000000000000000000408500000000000038a837e80000000000001c680f6c1eea0000390c00000000000023450de80000000000000000000000000000000000000000000000001a6400003ba900000000000000001d891c050000
  | 6, 93 => 0x412c00000000000000000000000000000000000000000d83000000000000000018c9034101610000000000000000000000003bc919c8000000000000000021e600001ea636e122250000000000002dc422480da40000000007020000000010a900001c2c0000000000000000222a00000000000000000000000000000000
  | 6, 94 => 0x3c0138232ee1000000000000000015810c840000112c0000000000001d26204c13e70a680000000000e30000000032c1000000001f690000000000000000000000000000000000000000078a00000000000000000000000000000000000000000000000000000000000039a9000000000000000000000000
  | 6, 95 => 0x44610000000000000000000016e2000000000000000000000f2a000000000000000000001dab0000000000000000000000001f610000000000a300000000000000000000000000003a69000006e80000000000000000000000000000000032a528850000000000002666000000000000000000000000
  | 6, 96 => 0x332100000000000000000000442c10e9124c000000001bc50000000018c5000000000000000000000000000000003d6c00000000000000003fa7316810492b861d0a1ca4122b0d8700000688390600000000000031e1000000003841000014c50000000000000000
  | 6, 97 => 0x3c4c2c881167000000000000000000001aea000007820000000000000000000000000000000000001f4a0000000000000000000000001d8a0000000000000000000000000000000034e22c28174c0d890000000000000000000000000000000000000000000000001186022600002e6200004381000000000000302800000000
  | 6, 98 => 0x1f2a1e24112700000000000000003da61e4406a400001ba4000000000000000000001b2403ac41c103e10eea000000001924296a0000000041050000000000000000000005ea00001deb0000000000000000000000000000000000000000000000003b2a0000000008e2000000000000000006ea0000000037c3000000000000
  | 6, 99 => 0x1b8603060000000000000000000031852c440000000000003d25270200000000000000000000000000000000396600000000000000000000000000000000000000000000000000000000000000000000000000000c86000000000000090c000018a608e1000000000000000000000000000044410bc8000010050000
  | 6, 100 => 0x3ceb00000000198300001a2600000000000000000ec50000000000000000000000000000000000000a8a0465000000000000000000001e450000000000000000000000a5000000002ae91882000008a100001b8a00003ce91a4a1f6c0000000000000000000017a3000000000000174604c600000000
  | 6, 101 => 0x1dac00000000310300003626000000000000222300000000000019c400000000000000000000000000003e2a0000000008030000000000000000000025461da8000000000000016400000000190700000000000004e6000013c9000000001b0143270000000000000000000006e44147000000002048000000000ec900000000
  | 6, 102 => 0x40ca2e66074c222c28050f420000000000000000000029a500000000000009e1000000000000000000000000000000000000046c0000378200000000000021e900000000000035e7000000001da4000000003763000000000000000000000000000000000c25000020e917c80588
  | 6, 103 => 0x1105000000000000000000000000000000003ce823e50000000000002025000000000000000020050000000022c600000000000000000000000000000000000000002a0526020ec20000000000000000000024e8000000000000000000000a230000000000000000096b1e811b4100000b01000000000000000000000000
  | 6, 104 => 0x19030ce600000000014100000da615e50000000021c6000000000000000000000000000000000168186b000020810000000000000322000000000000108100000000000007a1294a20021fa40000000023220000000011620e610000000000000000000000000000000037610000000000000000000000000000000000000000
  | 6, 105 => 0x3c670a4200000ba72b8815c51d0c00000000000000000000000000002fea0000000000000000000000000000000000000000000000001ba21122000038681285000001c61b222a8100001a2700000000000000000000184a05a100000b86000000001b211263000000003fcb3d21314310cb0c6125010ce2006103811e2a0c29
  | 6, 106 => 0x1f28000000000000000019231ac5000000001dcc0989000000003c6b2d441eeb23a9000000000000000044820000000000001c8b20e5000000003c2c188c00001a0300000000000000003cac0000000000000825000000000a86000000003b613e451a8200001dc80000000030a504631b0c00000000000040263a6a
  | 6, 107 => 0x42ec0000000020a30000000000000000200810c21607000000000e63000032aa2042000000000000000000000000000000000000000000001fe2000000000000000000000000000028892de62ce2000000001eac000000003f2a3ee62d8600000000000035e9000000000185000000000000000000000000000000000000
  | 6, 108 => 0x3ba10000000000002a4207c3120112e3000000001443000000001b8400000000000000000000000000003a250a01000000000000000000000000102c4484000000000000000000000000000000000000000000000000000000003a243c4700000000000000000000
  | 6, 109 => 0x1569000000001f64000026c51ce3000019690000000000000000000042220aa8000000002a060000000016a100001d6600000000000028a5082400000000000000000000338500003b030000334a0dec28aa00000000000000001b2a3961338a18a30000000000000be6000000001283196a3808000000004001
  | 6, 110 => 0x1acb000000000aca00003b8100000000112600000000000000000000000001c41669000000000000000004040ea400000c6700001a6a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003be9202c00003d4100000000000000000eec
  | 6, 111 => 0x3f8700000000000034a51ec7000000000e46000000000000000000002545000000000a0b00000000000000000000000000000000000007e21487000000000000000000000000000000000000000000000000000015e136ca03660000000029c900000000000000000000000000000000000042e83501380601c1000000000000
  | 6, 112 => 0x39430bc40000000000000000000000000000000000001922000031080000000003ab0000000000003d223c662be600000000076100000000000013c743ac0000000000001f2c000000000000000000000000000000000000000000000000328a00000000000000000000000000000000000000000000000009022d8500000000
  | 6, 113 => 0x1c420000000000000000000000000000000000001381000000001e2c354800000000202816ac000000000000104700000000000000000000000000000000000018ab000000000000000000003f630d8a00000000018800000000000000001e2202c600000000000000001e4206a219eb43890000
  | 6, 114 => 0x28e61dcb0da10c2800002724000000000000000000000000000017e400000000000010c900000000000000001286000000000000000032ea306936cc000000000000000038420000000000000000000000000000000043a70b21000000001b290c480000000000001e6a00000000000000000000
  | 6, 115 => 0x43610000000000001c252e86000011c10000000000003a81122c000036e8208600000dac00000000000032a6302200000000000000000000000000000000000000000a6a0000000000000000000000000b840000000000000000436b000000000000000024220ae500000000000000000f01000000000000
  | 6, 116 => 0x2303000000000000000000000000000000000000000023261365000000000000000000000000000015a30000000000000000000015030000000000000000214200001c2a00002c64000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 6, 117 => 0x1ae217ec000000000000000000000000000000002aa6000000000e0800000000000000000000000001c200000000000000000000000002e60000000000000000000029e50000000000000000000000003a8a1aa80000000000000000000021260ca630c929ea00000000
  | 6, 118 => 0x11ac00001b65000000000000420300000000028b0000000000003ca10000000020c826e60000000000000000000000000000000037e600004364178b00ec000000000000000000000000314221a21c650000000000000000414100000000000000000000000000002e2100000000000042e400000000000000000000
  | 6, 119 => 0x1609000000000000000000001c430dcc00000000432541450000168600001164000043aa18cb00000000000006e700000000000000000000000000000000000009a100000000000000000000000000000000106800000000000000000000000000000000000000000000000000000000000000004429000000000000
  | 6, 120 => 0x1b4800000000000032292f66000000001ce40000000022620743000000003ae20c82000000000000000000000000350200000c450000092800000000000019040dca0ba5000000000000000000003b653fc2000000000000000000000000000000000000000000000000000000000000360600000d6c0000000000000fc1
  | 6, 121 => 0x1fa70bc21f84176314a91a2800000000000000000000000000000000000000000000000000003e4a000000000000000000000000000000000000000003e40000000000002b621ce900000000000000001ee800000000000000000000000000000000000000000000000000001a48000000000000440837c4
  | 6, 122 => 0xdc50000000000000000000000002c24174b22832746000022ea1aa208a600000000000000000000000000000000000032e10000000000003d833e89240100000000000000000000000036c926ca2a0900002604000000003bc1000001e300000000340800000000000000000f0b00001cc100001fa2000000000000
  | 6, 123 => 0x3c060000000000000000000000000000000000000000144500000000016600000000000000000000000000000000000000000000000000000000000000000000000000000000000034020c0a000033a800000000000000000000000000001aaa3147000000000000000000000000000000000f4c1282
  | 6, 124 => 0x1c8327c900000000000000000000000038c815ab09e400000000000005e4000000000000000028c20000000000000000000000000000102231e60000000000001ee100000000000000000000000000000000000000000f080a030000000000000000000000000000000000000000000010282b4a0a2521661d4a0000
  | 6, 125 => 0x965000000000000000000000000046100003b210000278937a10c030000000000000000000000a13ac1000000e400000000000017450749444a36cb10630000110b00000000000000000000000026c200000000000000000000392c000000000000046938a3000000000d290000000000000000000000000d450000
  | 6, 126 => 0x2e8000000000000000000001102000038c6134900000f82000000000000000000000000000000000000000029ec146900000000000000000000000000000000000000000000066600000000000031a2000000000fe903c20000294c2043000000003c85000009220a870000000000000000000003aa00000000
  | 6, 127 => 0x3d2c16ec00000000000000000000000036212d61000000000000000000004467000042aa0901000000002f4327e60000000000000000000000003fc500000000000007e1000000000000000000000000000033e92f8600003aa12026142b0bc6000000001fe61625000000000000000000000000000000000000
  | 6, 128 => 0x3e822ac2206600000000000000000000000000000000000000002a01000000000a8509a700000e2300000ce30000000000002d030000142301440000000000000b070000000000000000000000003bc500000000000000000000000000002123174700000000000000002009000000000000028911e80000
  | 6, 129 => 0x1d4300003f6709e73f6937042ca118e70000000000000000000000000e8a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004343078940460000000000000000000000000000148500000000000000003d44000031452fa623e1000000001da100000000
  | 6, 130 => 0x3d640000000000000000000000003da9388108c423280e6817a21722054204a23c281fc2000000000000000000003ca800000000000000000000000000001909000000001307000000000000000000002926000000001f8300001822000000000000000000000000000000000000066800000f47000000000000000000001d23
  | 6, 131 => 0x20e10f8c1e8c23a51b2b0a2a0000000013a50000000000000000000000000000000008210000000000000000000000003001000000001ae80000354120a230a127c109c6000000000000178300001aa52681000000000000000000000000000000000000000000000000426737a4
  | 6, 132 => 0x286900000000000000001d85000034690000090400000000436a3d4729e40b0c00000ae6000000000000000000000000000042890000000000000000000000000000000000000000404b01810000000007e4000000c3000000001067000039aa000000000000000000001fa3000000002e460000000000000000000000000000
  | 6, 133 => 0x46b0000386100000000000027e800000000000000000000000000002006000018010000000013210000000000001c4800002862190500000000000030c100000000000039e124c1298128e528e10000000000001a853485348134213a610000000043ec400500000000000000000000000000001e6c000022ec000000000000
  | 6, 134 => 0x30200003902000000000000000000000dcb00000000000022a400002fc100000000000000000000000000000000000030260c6c0000000000003fc600002c630000000000000000426a00000000074b000000000000000033e60000000000000000000000000000000000000000000010c423830000000011080000
  | 6, 135 => 0x2182042225a600003269000000000000000000001b0500001e4900003b4500001c841cc40000000009c400000000000000001ec200000000000031a400000000000000000000180700000000000000001f0700000000000000001f0b0000000000000000000026c100000000000032e60000000000000000
  | 6, 136 => 0x3f660000000000000000000013c2000000000000000015c700003fe5000000000aa30000000000000c812c431e4700000000000000000000000000000000000000001e6400000000000008460000000000000000000000000000000000000000000000000000000000000000000007a800000000
  | 6, 137 => 0x3ac900000000000000000000000000000000000000000000000000000000000000003b4600000000000000002b44180b00000000000000003c0b0ae938043e05000000000000000000000000000000000000000000003b22000000000000000000000000000034a10000190100000000000000000000254122e20f4800000000
  | 6, 138 => 0xaa4000000000000000000000000000000000000000020223c2918890000000000003daa000010cc3ca9020300000000000000000000000030810000000000000000000000000000000000000000000000003082202a00000000000000000000000000003ec62aca000000001849000000000704
  | 6, 139 => 0x292c000036040000000043a3424105a2094300000000000000000000000000001b0312c906623663000010271e050000000010a40000000000001e630000356614c912c51e2517aa02640126000000000cc53c8a35c800000000124737a50000000000000000000000003ea9120a1a431be20fc2
  | 6, 140 => 0x3dab00000fa200000000000013830000000034e5000000003e0238a60ac934c52a620c230000000000000000000041c225260000000012270eca000014a70000000000000000000000001a690000000020240000418100000000000000000000000038a2254b0000000000000000000000000000
  | 6, 141 => 0x7220000000000000000000000000000000000000000000000000000000000001dc4000000000000290700000924000000000000000006e2000000000000098c00000000000000000000000000000000180500000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 6, 142 => 0x48300000000390400000000000000000000000000000000436300003a06000012610a060b4205c204a90000000000003ce229e100000000000000000000000000000000000000000000310200000000000022020000408200000000000000000000000000000000000000000000000000000000000017c30b430000
  | 6, 143 => 0x16e41727178a000000000fc9000000000000000000000000000000000000000043c2000000003f8a00000e4500003d420000000000000ca51d8300000000000000003265000000000b8500001fc80000000000000000000000002fe200000000000000000000000000002fe91c090ba918650c4a000000000000000000000000
  | 6, 144 => 0x164b0000000000000000140706e30000000000000000000000000000000000001505000000000000000043e7000000000000000000000000098600000000324600000000000000003fe60000000000000000000000002f222d260000000000001ea41ca11567000000001065000000003748000000000ee6000000004366
  | 6, 145 => 0xb4b00002708000000000000000000000000000000000982118a000000000000200c0000336612e70000366228e937643683000000000bec342232c900000000000000003ea22ae2000000000000000010e2078100000000000011a6000000001b2300000a4c00000000000000000000000000000000000008c2000000001483
  | 6, 146 => 0x414c0000000000001ee428ca000000002dc6000000000000000000000000000000000000000000000000000000000000448c000000003187000000000000000000000241000028a600000000000000000000000000000000000000000b0800000000000000003ce30000154b398105e50000000035a42ba81d2c172b
  | 6, 147 => 0xd252b29000000003c84000000000000172604a60000000000000000000000000000000011650000000000000000356217a900000000000016471eca0000032600000cac000000000000000000003dc9000000000000000000000000000020c40a8100000000000000000000000033aa25e2000000003de80000000000000000
  | 6, 148 => 0x9a6000043c90745000000003dac00000000000000000000000000000000000000000000000018680000000000000000000000000000000031e2214300000000086200001ec81c2100000000000000001367000000000000000000000000000000000000254c
  | 6, 149 => 0x2cea00000000000040893da83de23f2500000000000000004149108c00000000000000000000000000000000000038e12483000000000000000000000000164500000000000000000000000013a700000000000010c836c1000000000000000000000d4b00000000000000003c03000000000000000000000000000000000000
  | 6, 150 => 0x1521020600000000000000002b8300000ca20c4200000000000000001c0a0baa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000031061fe400000000000000000000218800000ae70000000000000000000035e60000000000000000398916c8
  | 6, 151 => 0x2ba61d2a1c630000080632a2000000000000000000000000000040e537a711c40000000012ab000000003b252528000024810000000000000b8800000000000000000000000000003cea18a71de30000000000000000000005a8000019450a4300000000000000000000000000000000000000001d0100000000000000000000
  | 6, 152 => 0x1ba90000000000000000000000000000000000003f022f8125812da241aa152b00000000000000000000000000000000000029461c61000000000000000000003c2500003b6600000000000000003a4227410000000033c62f21318a00000000000000000000000000000ba40000000000000000000021050000000000000000
  | 6, 153 => 0x20c3000000003d88000000000000290b00000000000000000000000000000000000000001a2237ac00000000000000000000000000001ea800000000000000001643000000001b07000000000000000000000000000000000000000000000000000000000000000041a500000fac000000000000000000000000000000000000
  | 6, 154 => 0x160b0e2b000000000000000000000e22000017c4058400000000000021e503421acc0000000000000000000000000000000000000402000000003944260600000000000000000000000024a100000000000000000000000033eb00003644000000003cca000000000000170500000000000000000000000012220000
  | 6, 155 => 0x2ea119250f490f63000000000000000000003e6100000000000000000000000000000000000000000000000000000000000039c200000000428a00001441000000001b82000000000000000000000000000000003a2a14e10000000000000000000000000000000000000000
  | 6, 156 => 0x41220d4c00000000000000000000000000001a0c0000000016e60000000027010000000000000000000000000000000000002fe50d610000000000000f89000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 6, 157 => 0x1f27000000001d6231a1000000000000000036c810450000000000002e280000000000000000420839c8188131840000000000000000000000003dcb07080000200432e200001b4a000000000000000000000000000005a6000001a600002fc80000000000003de53843000041a232612f8200000000
  | 6, 158 => 0x1c8a1bc62726000000002a8a000000000000000000001f4c41861de80000000000000000000000000d860000000018c7000037e30000000000000000000034040000000000000000210b000000001d630000228800000721000017a40544000000001da90000000033a93d48000000000000000021ab00210000000000000000
  | 6, 159 => 0x302300000000000000000000000000000000000000000000000000000000000000003a030000000000000ea643c5000033a400000000000035a23162266a17290b492f0200000000000000000000000036a33c682be80000000000000000000020c2000000000000296500000000000000000000000000000000000000000000
  | 6, 160 => 0xe9000000000000000000000000000000001be9000000000000406800000000208300001628000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001ce2000000000000000000000000
  | 6, 161 => 0xbca00000de7000000003de412a32f88000020820000000000000000414b000000000000000008081aca11e30000000000000000210800000e4a000000000000000000000000000000002dc13cc300000000094b036400000ee40000000000000000314c0fa1000000001dca0000000000000000
  | 6, 162 => 0x41612d6304010000068101210000192b0ccc24e10cc60cc206a10041000000003a011a0916c903010000000024e6204a0000000000000000114800000000000000000000000000000000000000000000000022010000000000000000000000000000000000001d211d4100001e4a1f020000000000000fe100003c6327440000
  | 6, 163 => 0x1c071fe7194b000000000000000000000000000000000000000000002fa33c860000000000000000000000000000428300000000000000000000000000000641000036a21c67000000000000000000000000000020a6078515010000000000000e6442c530a92781220422c41c020fe20000000000000f02
  | 6, 164 => 0x168a000000000e01000000000000000000000000000021c10000000012e502e30ee3000042490000000000000000000031c23f262e060000130918a505230000000000000000000035e2078b000038c42706200318a8100b0e421dc20000000000000000000000003c430000000000004321000000000000
  | 6, 165 => 0x32300000be30000000000000000000000000000000000000000000000000000122300000000178500000000192700000000000000000000000000000000000000000000000000000000000033820000000000000000000000000000000000000000000016c306060000000000000000000026292ca30d27312200000000
  | 6, 166 => 0x2c04000000000000000000000000000000000000252307680000000000000000000000000000402200000000000000001b270000000018e50000000019c20000126b00003ccb0000000022eb1ec61041000000830000000000000000000000001dc300000000000000000000000000000000198500000000000000000000
  | 6, 167 => 0x184817e5000043cb00003be600000ec70000000013030c8a01030000000030482e4200003ec90c4300000000000000000000000043a43f650d23100907aa1ce50963000000000000000036680000184c0000000000003c870f2b00000000000000000ee735a6172a0b4a00000000000000000000
  | 6, 168 => 0x2b05000037c820a1122600000000000000000000000000000421000019e142e200000000000000000ee5000009660000000000000000000000000000000000000000000036412226000000000000390700003401000000000000000044420ac1000000000000000000000000000043e40da915873f8500000000000000000000
  | 6, 169 => 0xc210000000000001d65000000000000000000000000000042654226354424c41f87114404860b2b16230000184500000000000000000000000000003ea5000000000e040000000000000ae2402500000e093446160500000000000007ab0000000000000000000000002f65264a1f2508020000000000003dc1
  | 6, 170 => 0x36881e4c0e2a000000000000000000000000000000000000000000000000000000001bab33e231a610ec0000000000003c8300000000000000000000000000002eca0b271b0a10a20000000000003dec000000000000104c262600004428000000002f480e430ca30000000000000000
  | 6, 171 => 0x1a660000000000000000000000000000000000003202000000003182264200e200000000000000000000000000000c240000000029013e8500000000000000000000000000000000296900000000000000000000000038c100000000000000000000128842642f69000000000000000000003da100000000000000001cab0fcb
  | 6, 172 => 0xb2c00000000350a0000000000000000204b00000000000000001765000005262b630000000008a302243c462bc61e090ac2000012a6000000000000000000000d28000000000000000000e633e50000000000000000000000000000000000000000000000000000000000000000000032c6
  | 6, 173 => 0x320a000000000000000000000000324a00000000106c000000000000000000000000000000003fea00000000000000000000000000000deb000000000d040000000000000000000000000000000000002ba21d29000000000000000000000000000000000000000000000b0b000000000000000000000a650000
  | 6, 174 => 0xba200000000000001a20000000000000000000000000000000042a2000000000000000000000000000000090000104600001e290661000000001b661b0616a4000000000000000000000000000000000000078700000000000000000841000000000000000000000000000000000000000000000000298900000000
  | 6, 175 => 0x448700001ce81be300000000000000000000000000003b4a00000000000000003e262a86000000001e0703a5418a202b19c6000000000000000000003d46000012c71e2713430be9012801a800000cc700004245000000001a890000000000e800000000000024c60000000000000000000000000a4900000000
  | 6, 176 => 0x1f0337c60000000011e20000144b0000000000003be11ec300000000000000000000000000003968120b32e9000000000000000011630000000000001a6825880000000000000000000019e20000000000000000000000000000000000003c61000000000000000042a509a9000000000000000039862cc216c2
  | 6, 177 => 0x232400000000000000000000000000000000220616a8000000001007000000000000000000000000000025e90766000000000000000000000000000000001683000000003b6912a2126200000000000017a13d2b16eb000010a3000000000000000000000000000000000000000022641a88000000000000
  | 6, 178 => 0x1bc30000000000000000000009e62b0a368442c13563400640421f4300000000000003e8000000000000000000002fa200000000000000000f2400003aca0000000000000000016200000000000028860000000000003c411a2a38ab000000003f610000000000000000000022282063082a0000000000000000000041a90000
  | 6, 179 => 0x13c51123000000000000000000000000000000001fa903c100000000190842e90000000000001867000000000000000000001cc500000d4a000000000000000000000000000000000000000000001de13e0900000000000000000000000006040000000000000000000000000000000014a500003e250000000000000000
  | 6, 180 => 0x522000000000000000021ea196800002f610000000000002023000000002b0100000000000000000000072803881b2500000000214120ea1d4818080e4c0000000000000000000012840000000000001e0a00000000000000000000000000000186000000003a2c114a1ca9000036220000000000000000
  | 6, 181 => 0x130100000000000000000000000000000000000000000000070300001bc400000000000000000000000000002065000000000000000000000000000000003d6a000000000ea9000024a300000000000000000000000000001b8700000000000000002d660000000010aa00002fe600000000000000000000
  | 6, 182 => 0x3fa61a2400003fc300000f230000198b0000000014a100000000000000000000000013cc0000000009c7000000000000000044660000000000000000000036a400000000000000000000000000000000000023c30000000019c9052835eb0000000000000000184300000000000000000000438500000000000000000000
  | 6, 183 => 0x20211f0a0000000000004463000000000000020819a117820ea2000042a9330910e4000000000000000000000000000000000000430b170b000000000000000000000000000000000000000000000000000000000000000000003ec50000000000001be80fc80000000000003a2b42e30000000000001a8a000000000000
  | 6, 184 => 0x3e200001e0b11c60000000000000000000000000000000000000000000000000de300000000000000001aa6000044271bc900003c2409ab000010640000000000003ca4000000001a0500000000000000001c290000000028a1000017430000000000000000338111ab0000000000000000000000000000
  | 6, 185 => 0x202000000000000166700000000000000000000000000000a0900000000190612e1000035e800000000000000000000000000000000000000000001000000000000000000000000000000002584000000004102000024610000000000000f670000000000000000000000000000000000000000000000000000
  | 6, 186 => 0x10230000000000003d890000000000000e8100003f6a000000000000446243a10268000000003e690f830000000000001243000000000000000000000000000000003d820000298500000000148900000b280000000000000000000000000000000004e3102b0000000000000000000000000000000000000000000000000000
  | 6, 187 => 0x3b04180300000000000000000000000000000000000000002ec5082c0000000000000000000000003f01384400000000000042eb0000000000000000414400000000000022080000000000001b6b2041000000002d2200001347000000002f841a420000000000000000000000001b4200000000000000000000000000000000
  | 6, 188 => 0x1cc7000000000000000000002dc81ee60000000000002d020000000033c231890000000000000000000000000000000000000000000017c10b41000000000000000000000000000000000000000000000000000000000000000000000a630000000000000000000000000000
  | 6, 189 => 0x23c1000008040000000000000000000000000000000000001e034486000000000000000012660829000000002582000000001e2312c301240b29000000000000000029280cc31141000000000aa1000000000000000000002fc40000000000001768050840e60000000032a12881000000000000
  | 6, 190 => 0x2cc0000000000000000000024c2000011490000000000000000000022610000000000000000000000000000000000000ec300000000000032c500000000000031e5000000000000000007e6000000000000000035c3278c000017660506000000000000000000000000278317640504118908a2000000000b8300003d49
  | 6, 191 => 0x36660000300211a5000000000000160600000000000000001aa91f8c300900000000000000000000000000000000000027a20000000000000000000000003f0900000caa000000000000000044470000000000000000000000000000392a2a490000000000001f49000000000000000000000000000000003ac6000000000000
  | 6, 192 => 0x1c26100600000000000015a5000036640000000000002ba3216300000000000000000c6900000000206704660000250413270000000000003c070000000000000000000000000000000000000000000013e9000000003eea0f431048000000000000000000001b081b68000000000000000018c100000000182419e4
  | 6, 193 => 0xe0a000024e3168b0b48068305c8012304ac1ee20cc80cc40c8306a30043000000000000000000003c270fe30000000000000000000000000ac400000000000009810000000000001ae900000000000040c90000000000000000000000003e622b2200002d41000022a30000
  | 6, 194 => 0x170300000000000000003724054301022a4a00000000000000001e840000000000000de431a5000000000000000000000000000034aa00003e0a00000000000000000000000000000000000000000000244300000000000000000000000000000000000000004047356100000000000009c500000000000011852721
  | 6, 195 => 0xa451dc100000000000000000000196c000000001f670000000000000000000000000000000000000000000000000000000000000000000000001ee71941000000000000000000000000000037e2376800000000000000000000000000003cc20000000000000000000000002c810000000042213a82358634a2158517ca0feb
  | 6, 196 => 0x3d62000041230000000000000000000044241c060fe600000000000000002d81000000000000000000000000356817ac0000000000000000000000002b45000000000000000044261c8500000000000000ab0000000000000fab00002649000000000f27000000001b43000000001f6500000000000000000000000000000000
  | 6, 197 => 0x4430000000034e600001dc600000000000000000000000000000000000000000000000000000000000000000d6843a9000000000000316300000000000000001a6500000000000000000000000000000000000000000000000038a900000000000019ab222700000000000000000000000000001f4626860000000000000000
  | 6, 198 => 0x31a81ae61de500001faa00000000000000000000000000000000000021e7000000000c44000000000000000000000000200100003c05000027e11fe100000000000026a20000000000000000316c25620000000000000000000000000000000000000000000000000000000000002547
  | 6, 199 => 0x33c8318c1c6219ea1f66000000000000000008c30000000022c2000043eb09ca230100000000000000000ee90000116a00000000000000000000000000002ec100000000000000000000000000002f2600000000000000000000000033e7000000000000000000000000000000001eec3ba50000000000000000000000000000
  | 6, 200 => 0x31c600000000000000000f85000019e90000000000000000000000000d82436900000000352300000263000000000000000000001fa500000000000000000000000000000000000022a218aa2a6100000000000000001c0c0bac000000000d85000000000000000007e800000000000033ea
  | 6, 201 => 0x3d272f2900002c080000360100000000000000000000000000000000360300000000000000000000000000003ae6000000000000000000000000000040410000000000000000000000000000000008e33b8500003ee22d820aea18a900000000000000000000000000000000
  | 6, 202 => 0x1d8600002944000022410000000043a60000000000003482000000000000000000003e21000000000000000025a20000000031833b410000000000000000000000000e6c0000446805eb0000000000000000000000004263000000000000000000000000000000000000000036860e6900000000102406eb00000000
  | 6, 203 => 0x17e7000000000000000000000000000000000000426900002e44104300000000000000000000000000000000000000000000000000000000340322a639823766314830661c240ec8100428412cc621a8000041e2000034660000000000000000000033a500003862000031c40000000000000000042800000000
  | 6, 204 => 0x3fe707060aeb00000000000000000000000000000000000021e225e10000000000003c880000000037e400000000000042c913230000448900001aec000000000000000003c300001ca6124809e90000000000001c4a0d43000000000000000000000643334202c40287000000000000000000000000000011870b0614630000
  | 6, 205 => 0xc0b0000000000000000292a00000000000000000000000000000000000004030000020100000a6b0000000000000000000000000000000000000000000000000000000000001ba7000000001a070000000000000000000000000000358135a100000000000000000000000000001f420000000000000000000000003b49
  | 6, 206 => 0x1871b8c0f8800003cc50d08000000000000000000000000000000000de50000206c3f6b000000000000000000000000000002880000000012aa00000000000000000000000000000000124605630905000000001d642107000000000000000002860000000000000000000000000000000000000bcb0000000000000000
  | 6, 207 => 0x13cb000009a2000000003d613302000000000000000000000000000000000000000021021e8300000000000000000000000000003dc3000000000000000000000000000000000000000000003325000031490000000000000000000000000000000000000000000000000000000019871bea000000002d28000000000000
  | 6, 208 => 0x41e500000000000000000000448a00000000000000000000000000004488000000000000000000001f060000000000000000424200000000128c08820000000000000000000000000000200732c20000000000000000000000000000000000000000000000000000000041010000000000002ee20c05
  | 6, 209 => 0x2c0100000000000043c428011b890000000000000000000004a529a115093da3000000000000000031c10bcc0c0c00000000394206c316850a2c08430000000000003c89000000000e6a0000316b000000000000276600000000000035e544250000000000000c2a000000000000430700000000
  | 6, 210 => 0x1c30000000021ec00001e4b0000000000000949000000000000000000000000000000000000000000001f08000000000000000020ec0000156100000000082b000000000000000000000000000000000000000000e50000000000000000406400000000082700000f8127c51aa300000000
  | 6, 211 => 0x132b3a650000000000000000000000000000000000002786000016cc0000000000000000000000000000000000000000162a0d84000000000000000000001a4400000000000000003d8400001b440000000036a60000000000000000000000000000000000000000000000003d8b1e6b0a0a43450000000000000000000016c6
  | 6, 212 => 0x5e60000000010a100000000000025a10000000000002cc11be60fc623690000000000000000000000002e01264500000000000000000000000000000ac700004246000000000000000000000000000000000000000002850000000000000000112b0cea00000000000023a11a8315490000000000000000000000001d220000
  | 6, 213 => 0xec100000de6000000000000382200002b81000000000000000000000000000000000000000000000ba8000000003a0400000000000000000000000000000000000000004261000013c80000000000003b080000000000000000000000000d2b0000000000000000000000000000000000000000000000000000000000000000
  | 6, 214 => 0x152900000000000000000000000000000000000000000000000029620000000000003985000000003d28098716c700000000000000000000000000000000000000002aaa100c00000000000000000000000000000000000000000000000034c63b82000000000000000000000000000000000000000000000000000000000000
  | 6, 215 => 0x36430000404a2c6116e300000000000000002ee600000000000021aa0000000000001264120c000000000f410000000000000000000000000000182c000000000000000000000000108a00002e220ae10000000042022b4b21641d4b0000000000000000000000003c0400000000000000002c06000000000000000000000000
  | 6, 216 => 0x1a2b00000000000000001b47000031810000000000000000000000000000050324ab430917090000400a0000000000000000000040e913250d8c000041e90c8b0184162132092d682f620000000000000000324900000000000030aa210a116900000000000000000000000000000000
  | 6, 217 => 0x3f89146700000000000015480000000000002f6a41280000000040c1000000001da70a02330a1fa1000000000000000000000000000000000000166b000000003fe300000000000000000000062800001d8c09aa1225000020440000000000000000000000000000000000000000
  | 6, 218 => 0x40c2000000000000000000000000000044033d0c0000000000000000030300002961174804c80000000000000000000000000000000000000000000007a200000000000000003a620fc50000000000000000000000000000000000002662000000000000000030c200000000000000002c4100000000
  | 6, 219 => 0x448513c30000000000000000000000000000374332260000000000000000000000000000000037010000000021090000000000000000000000000000000014e70000000013e51ba50000000000001b450000000000000000000021a93c482bc800000ee8056400000000000000000c6200000000000011a40000
  | 6, 220 => 0x3d0736420d2c000000000000000000000000000000000000000000000000358335a300000ba1000035460be700000000158300000000000000000000126c000000002e23000000000000000000000ecc3c210000000000000000000000000000000000000000000000003a260000000000000000000027630000000015630000
  | 6, 221 => 0x390900000000000000001608192a0fa305ec000033ec3d0a000000000000000000000000000038820000000000000d4617e300003fe100000000436c09cc06ec000000000000000000000000000000000000000000000b22000000000000000000003824000000000000000000000000000000000000000000000000
  | 6, 222 => 0x334100000000000000000000000000000000000000000000000022c8000000003d240000000000000000052400002027000000000000000000000000390a000000001481000000000568000000000000000000000000000000000000000000000000000000000000000000001341000000003306394834c9000016e5
  | 6, 223 => 0x1bca16aa00000e8b000000000000000000000000000000000000000021c3000000001ce60000000000001fec00000000000000000000000000001b611ae300002a21000001e4000000001caa24063ce13cc60000000000000000000025431884000000000b820000422a00000182000000001a06000000000c0800000ea5
  | 6, 224 => 0x21611427014800000000000000000000000000000da80000000018e3182817ea01e816840000000000000000000000000000000000000000000000000000000000002d0111a229410000000000000000000000000000000000000fa700000000000000003fa21bec000000000000000000000000000000000000000000000000
  | 6, 225 => 0x62300002be1000000000000000000003bc20000000000000000000000000e87000000001bc100000000000000000000000036e20000000000000000000000000000000000000000000000000000000000000000422900000000000000001f4437830000000029c529860e27000000000000136b1c8c0ce70000000000002ba1
  | 6, 226 => 0x32138830000000000000ba300000000000030051147000011280cc900000000000000000000000000001fab000000001d6810eb000000a900000000000027a1000000000000000000003d8c000023493deb000000000000000026c91c64104b102a09612f44262500000000000000000000000000000000000000000000
  | 6, 227 => 0x74202ca000006e60000000000000000000000000000000000000d6a0000000000000000000000000000254a1c23000000003f6c000000000000000000000000000000000521000000000000414816811b6c15e300810000000000000dab00003f820000000000000d4700001f6a000000000000000000000541000000000000
  | 6, 228 => 0x434115c903a8000000000000000019e600000000000000000000060100000805000000000000160100000000000033a11bc200000000000000002b0905660aa7000000000000000000000000000000000000000000000000000000000000408a2bc1162636814143
  | 6, 229 => 0x23e90000000014c340020000000000001aac2665000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000028300000000000000003801000000000000000000000000000004080000428200000000000000000000000000000000000022a8000000000000
  | 6, 230 => 0x20640000000000003821064205e2000032820000000000003ba20e8910250000000000000000000000000000000000000000000000003a2134860000026200000000000000000000000012453b06000000000000330100000000000000000c66000000000000000000000000000000000000000000000000000000000000
  | 6, 231 => 0x2a800000000074600000000000000000000000037024048446c000000000000000000000000000000000000000002a61161094709032fa80000000000000000000000000000000000000000000035e3158907e300000000000000000000000000000000000029e2426200000000
  | 6, 232 => 0x426b0000000003610000000000003fe90000000000000000000000000000000000000000000000000000000037c1000000000000000000000000000000001ec5000026e5000038c30468000000002ae501831a630000000000000000000000000000000000000482000000000d490424
  | 6, 233 => 0x2764000019810000000015a70000000000000c4b00002c26174a0000000000000000402a00000000000029eb00002788000033c1000000001781358417cb1eab0000134b0000000000000000000000000000000000000000000000002ca2146b226800003f222e022b680e821cec0000000000001f2636c50000000000000000
  | 6, 234 => 0x9c80000000000000000000000000000000000000000000009c9432b00000000000000003c2a188a292700000000074800000c683caa00000d480b6710870d0200000000000000000000120200002ac50000000000000000000000000000000000000000000036c20f62000000000000000037e10000000002e40000
  | 6, 235 => 0x43e200000000000044221389000000002a0a1dc510ea01081a460000000000000000000000001b46000000000000000000000000124a000000000000000000000000104a000000000000082300000000000000000000000000000000000000001be5000037ab0000000000000000000000000000000000000000
  | 6, 236 => 0x17ab000000000000000000000000162900001183000000003588058305c317cc0000000000000000000000000e281967000000000000000000000000000000004367000000000000000000001e0200000000000000000000000033c4318b0000000009e227e40000000002c31c41000000000000000000000000000000000000
  | 6, 237 => 0x22e9000000000000230200000000000000000000000000002b4c21681d4c000000001c66000000003c08278209640281000000003165178700000000000000003ea610882ae60000000000000000000000000000000000000000000043e50000000000000000000016a511010e6b0000096a0000000000003564
  | 6, 238 => 0x196b0000000000000000000000000000000000000000000000001f88100a424a000000002b4628430561180a12a1086800000000000000003c0a0000000000000000000000000000000011e100001fc5000000000000000000002148058105c124a53e662b261ea70000000022a100000000
  | 6, 239 => 0x3e650000000000000000000000000000126a21e419c300000000000000000000000000000000000035c202c5000000000000000000000000000000000000000027c6232301e21305018c000000000f610000000000000000372639241dc90e060000000000003aa40000000000000000000000003f6420e70fc70000
  | 6, 240 => 0xa21000000000000000000001ac70000000000003ae10000000000002d43000010ca112400000000000031ca000000000000000000000000000012a700000000304408440eaa00000000000000000000000000000dc10a8300002a4500000000000010c70dc4000000000000000000001da310e702443eca00000000
  | 6, 241 => 0x2a850000000000000000000000000000000040ea3dc53ca31eaa222200000000000007260000000041ea00000aa5000022290000000000001c4c000000002506000000000000000000000000000000000000000000000000000000000000000000000000000000002ca600000000
  | 6, 242 => 0x1c2b0000000000000000000000002c830ccb00003221252405e900000000000000001f040000000040660000000000000e26196500000000000000000000174112210000000006e900000000000000000d0312490000000000000000000000000000000000000000000040e200003286000000000000000000000000
  | 6, 243 => 0x1f8900002ae10000000018641029000000000000000002e12c66000037a300003da5206a0000000013a1334600000000444b0000176205020000000014e500000000000000000000000000000000172300000000000000000000000000000000000000000000000000000000000000000000000000000000000000001cc90000
  | 6, 244 => 0x24210f6a00000000000000000000000026ea13ab0000000039a629a90000000034e122e73741000007880000322a392734c100000d26000000000000000000001a86000000000000000000000000000000000000000000000000000b000000000000000000000f0400000be5000000001a08214600000000000000000000
  | 6, 245 => 0x21440000000000000000000032620000000038ac00000a0c000000000000000000000000000000001fe5172404a40000122800000000000000000000000000000000182500000000000000000000000000000000000000000000000000000000000000000000000027e320e400000e8407c21ea3118c090900000000
  | 6, 246 => 0x42a6190238e20f6929e6292b21c40c2727850000000000004421328530e206082865174204c2000000000000000034651e4300000000000000000000000000002542000000003c6a2d461f220000000009eb0000000000000000000041e62943000000001cc33ce60c470a040663000000003206000014cb2ac1000000000000
  | 6, 247 => 0x2fc23cc727c22aa500000000000000003fc1000026e2000037030000000025020000000000000000000000000000000000000a88444300000000000000000000000000000000000035c6000000000d640000000014eb09ea0000000000000000000000000000000000001ba828e20000000000000d0900001b28000000000000
  | 6, 248 => 0x128a000000000000000000001e691b8502a4240200000000000000000e831c6a00002c02000000004446098b00003fab0000300a28c61be40fc4000000000000000000000000000000000000258600000000000031c31d070000000000000000000000000000
  | 6, 249 => 0x15270000000000000000000000000000000000001e87000020462d6200002f4618851beb15a100002103000005e11e2b09a30000000000003de6000000002d8a0000000033ac414a0000000000000b033d4b00000f4600000000000000000000000000000000000000000000000012a80000396200000ca8000000001ae70000
  | 6, 250 => 0x12420000000000000000000009e30000000000000000000000003fa82b47168214613d8a31cc02c7000000000000000000000000000000000000000000000000000000000000000000000348000000000000000000000000000000004449230600000b6c0000000000000000000000000000000000003f860cca000000000000
  | 6, 251 => 0xf640000000031c81926142501460000274800000000000000003e062a66000036e4000000004348000041c625210000000000000000000000000000000000000000000006822621000000001f8512240000000000000000000000000000000000000000000000001fca43e10000000000000000000000000000000000000000
  | 6, 252 => 0x15a9000000000000000000000000000000001a21000027031c45000000001f62000000000000000016a3292508c6000022e600000c630ceb000000000000000000003ba600000000000000000000000000000000260800000000000041291e260000000026c6000000001e46182306a600000e25000000000000000035c40ce5
  | 6, 253 => 0x1409000000000000000000000000000000002c03080100003903000000001be10000362326a1000003a1000000000c2b000000004266000000000000000000000000000000000000094100000000000024e40000000000001665000000000000000001a400000000000000000000000000000000000000000000000000000000
  | 6, 254 => 0x11a70d690000000015c1122900000000000000000000000000001546116800003a231345000000000000000000001d6a000000001c4400000000000000000000000004e400000000000000000000000019640000000000000000360230e100000000406100003bca126741a630c534c203843a4622211d4418040a26044603e6
  | 6, 255 => 0x1da200001c8100000000000000000000000000000000000000000000000021011a4700000000000000000000000037620000000000000000000031a7062615411f091fc63728000000000000000000000a24044440691e8600003a890000000000000000000000003222000019a51786
  | 7, 0 => 0x5a70000222500000000000000000000000000c415e6064100000b25000000000000000000000ba50401000000000000000000000a6806850000000000000c03000000000000000000000082054824ac000000001b8400000000000000000000000000000cc5000000000000000000000000000000000ae6000000000000
  | 7, 1 => 0x9290000000000000000000000000000000000000000072200000422000000000000000000001fea03610000000000000000000018c10000000000001e0c228b000000000000000000001c8207830eec07a300000000000000000000000000000000000000000000000009050000000000000000
  | 7, 2 => 0x9010601000000001d470000000000000000000000001ea300000000000000001d670000052900000c0100000000000000000000000000000000000000000000000000000000000000000000216a0000000000000000030702250000000000000000000000000000000000000000046a00000000000000000000000000000000
  | 7, 3 => 0x4ab000010a10000000000000000000000001821000000000000000003060000000020a2202200000000000000001561000000000000000000000000000015e1000000000000000002aa0000000000000000000000000000000000000000000003050000000000000ee800000000000002ec0000000000000000
  | 7, 4 => 0xb2b0000000000000000000019840000000026251aaa0ae816c90000000001a400000000000000000000000000000000000000001a61050800000000000000000000000000000e4b00000064000024c20000226900002046134607c10000000000000000000000000000000000000000188103651661028200000000
  | 7, 5 => 0x2202056600000000000000000000000021ac1d4c1c21000000000cea0000000000000b071c010000000000001ca600001ae20000000000000000058326e900000e8818010000000008cb0000000000000a0322a11d2b1364084b000000000000000023841dab190215e2072b00000000000000000000
  | 7, 6 => 0x70200000000000000000000096100000000000000000547156202c80000000000000000000000000000000000001569000000000000000001c8000004ec000000000000000000000000000000001ac318e40d04000021c10aa81a26184a174a0000252504e4000000001e651de200000000000024ea00000000000000000000
  | 7, 7 => 0x8a1000000001cc60000000000000000000009c3000000000000000000000000000000000000000000000da30000000006e400000000000000000000000000000000000010e700000162000004aa000000001fc612a60a21000000000000000000000000000000000000034c000020eb00000000
  | 7, 8 => 0x1da50000268500000000204900000000000001e20000000000000000000000000000000000001466000000000beb2162000002ab00001e050000000000001f61000002e500002025000019441441000000000000000026a1094a25260947000019a8000000000ae9090b0000184617c500000000216512c10000
  | 7, 9 => 0x96700000bc9000000000000172500000000000000000000000006050000000021a70be60000000000000000000000001861000000000000000000000000000000000000000007e206e320e3000000000000000000000000000000000000000024a305c10d05000026860000000000000245000000000000
  | 7, 10 => 0x18a1030200000000000017e100000907000000000000000000001e640000000000000e4200000000000000001022032300001ec501c30000000009c1000000001fe500000000000000000000000000001d870000000000000000000000000000000000001de70000000000000000000000000000000000000000000000000ca2
  | 7, 11 => 0x228c00000000000010aa0da600000da2000000000ac61a64182a0c420b220000000015860a2b000010e3000004c1038a00000000000000000000000000241d8118a60000000021e20000000000000000000004050507000000000000000000000000126104ea00000000000000000000000000000000000000000000
  | 7, 12 => 0x5a3000004e300000d490000000000000000000000000000000000000000000025e4000003c3000000000000000000000527000000000000000017860000000000000fa400000000000026e40000184200000000000000001e0400000e810000000000000000000000000000000000000000024b0000000002ac000000000000
  | 7, 13 => 0xd2b0000000000000000096b00001eaa1e6a06630000030c000000000bcb1f0a00000000026b00000be400000b05000018260000000000000000000000000000000000000000000000000000000016e6270300001fa60000000014830a8404e80000000000000000000000000000000000000000172200000000000000000000
  | 7, 14 => 0x2a400000000000000001f841264000000000000000000000dc3000000000000000016ca234223810000000000000000000000000000000000000000000000001322000000000000000000000000000000001f270000000000000000000000000000000000000000070900001d03000000000000000000000000000000000000
  | 7, 15 => 0x13c10000000000000000000000000000000000001aa9000019420000000000000000000025011e0a25c3000000000000000021890000000000000000000000000000000000000000000008a3000000000000000000000000000000000000000009c414e600001d02000000000000000003e20000000000000000148600000000
  | 7, 16 => 0x4e601e6000000000000000000000000228208a80000000000000000204500000000000000000000000000000000000016c602e800001e09224600000e23000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001d89000000000000000000001b01
  | 7, 17 => 0x210608a500001d44000018220000000017890000000026880000210422c902630000000000001a44000000000000000025a520ec00000d2c00000000000000000fc224610000000000000000000004c200000000000017aa16ea000018e320e7000000000000000000000000000000000000000000000000000000000000
  | 7, 18 => 0x21c40c2b000000000000000000000a64000000000d63000015440000000000000000000005440000000000000244000003c50000000000000b2700000e470cc90d4208ac000000000000000017a300000000000027040000000000000000000000000000200a000000000000000000000000
  | 7, 19 => 0xc8900000000000000000000000008eb000000000e610000000010eb000000000000000000001986074400680000000000000000000000000fc60000000018e8000000000000000019a40ba12085022b000000000000000017a600000000000000000000000000000d23
  | 7, 20 => 0x24e9000000000000000000000022000021ca00000000000000000000000000001dcc00000000000000000000000005210d240000000000000000000000000000000000000000000020e61aa705ab0fa8000000000468138200000000000000000000000023c2246200000000000000000000000009e10000000000000000
  | 7, 21 => 0x20050000000000000000000025a90000000000000000000000000000262914010fc108290000000000000000000015010f0100000000000000000000000013a12109000000000d640000000000000000000000000d4c0b41000000000b870a0200000000122100000000026100000000000000000000036c0000000000000000
  | 7, 22 => 0x24210ea80645000003ac1bc20be100000000000000000000000000000000000000000000000000000000000000000000000000000863094502c32641024a0843000000000000000000000000000000000000000000000e680000000005e526840d6703260106000000000c85054900000000276300001f41000022260000
  | 7, 23 => 0xd6600001eac1e6c000022c100000000000000001f0c00000000000000000a8512e6000000000000000000000000000000000000000000000000048200000000176900001a2813881f891721000000000000000023c8000000000785044a0000000000001ce10eeb0000000000000000000000001de80000000000000000
  | 7, 24 => 0x1ec20dc4000000000000000000000000000012410000000021c500000000000000000486000000000000000004830000000000000aa400000000000000000000000016e40000000000000000000000000000000000000000000000000bca0000000026c1000023a9000000001fc500000000000000000000
  | 7, 25 => 0x1fe92442000009c8000000000000000000002422000022a60223000006e8000000000000000002a80c6800000000000000000000000000000e26000017c40b490f830000000000000aeb00000000000005c50000000000001ea80000000000000000000000001f0800000000
  | 7, 26 => 0x1f830000000000000745000000000bc208c900001a88000019c100000000000014c1000000000000000000001aa4000001e806690000000000000cac00000000000000000000000000000000000000000000000000000000000000000000000025e200000000000000000000000000000000000000000be9000000000000
  | 7, 27 => 0x1ac50000032a0000000000000ca5000000000000000000000000000000000d43000000000000000000000000000020e105220000028c00000000000002c6000003c2000006a716a600000000000024e200001ae40000000003080000000013e1000000000000000005a10000000000000000000000000000052c048700000000
  | 7, 28 => 0xb6603c11c26000000000000000000000000000000000000000000000000000000000000000000000000000000000ceb000024aa0000000024c300000000000000000000000026c317a916e900000e22000004c521a91d490000000000000a251f8c000000000000000024c507e60000000000000000
  | 7, 29 => 0x1622000003e300000000000000000000000000000000000002e300000000000000002367000000000000000001e400a102c70000000000000000000000001e610000154300000000000000000000000003a500000000000000000a651d2700001f0300000000000000000000102600001ac200000000124200001e45
  | 7, 30 => 0xea4000000000000000000000000000000000000000000001f2800001ac80000000000000000000000000000000000000ce60000000000001982000000000000000000000000000008e5178207870000000004a300001eeb1ceb1745000000000000000021280000000000001666000000000ec20d6b000000000d0b0000
  | 7, 31 => 0x4e5000016c21be100000000096600000000272200001bc1000000000000218200000000248502830b670ce500a6000000000e44000025811fc212a2144200000c4a1702000000000000000026e11dc3000000000000000000000000156a068100000c2a00001de402e9172900000000000000000000
  | 7, 32 => 0x1889000000000000000000002249000004a7000000000000036a234902270000000000000000000000000bac000000000000000000000ba200001f4a000000000000000003e700001a230000044b0000000000001d070000000000001b8100001b8800001d4204611c8105430be50cec000000000000
  | 7, 33 => 0x1a81000000000000058600000cca000000000000000025e600001248072100000000000000000000000000000000000000001682000000000000000000000000000005230b4c000016892748210b03a3000017c1000000001e2a000000001a8302a10000000024871dcb190411e5000006c10000000000000000000000000a29
  | 7, 34 => 0x27230021000000000000254609a700e1000000001ba2254900000000000000000000000006a30000000014e403aa03a81e250b4607a40000000000000000000002430000000000000000000015a10000188a0000000000001aca25c100000000000004470de200000000104300a30000000000000000
  | 7, 35 => 0x13630000000020e51e4b0bc3078b00000000000000000000000001810000000000000000000000001ee300000000000000000000000003c7000000000000038900001602000025c90000000023a600000000000000000d290d4b072a000000000000000000000765000000000c0900000000000019080e282562032201020000
  | 7, 36 => 0x1dc50a8c0a0c0000000000001ea50000074805a9000002e70000158100001a010000112307240424084100000000000000000000000000000000000008230000000000000c61000000000000036800000000000000000000000000000000000000000000000021850000000018860be20000000018a300000000000000000000
  | 7, 37 => 0x34500001a43000000000000000000000000000023021f6900000000000000000000000010c50fe200000000000000000000000000000000000000000000000003e1270208480b8800000b2a00001e4700000000000007270000000000000000
  | 7, 38 => 0xd2a0000174600000000000000000cc30ae700000e84000002ea0000028700000000000016e200000000000000000000000000000000000002c11869000000000000000022290163000000001f21000000000000000000001d0500000000000000000000000008050000000015c600000000
  | 7, 39 => 0x7690000000003e400000000000000000000000003e90000186a01c60000272400000000000000000000000000000000000000000000000000000d0114a60c460b260ee500000000248b0000000000000000000000001e240000000000000000000000000000000000000000046c00000000000003ea00000000000000000000
  | 7, 40 => 0x16850d0300000000274b0e0200000000000000000000000000000fe60e2100000000000000000000000022aa088900000000000000001d4320211d48116303670000000019a104880000000014a1258209490000000019c6210800000249000019e3000000000000000000000000000000001ee10000
  | 7, 41 => 0x7040000000000000000000002a900000000000000000000000010c10de109a326630000000000001866006103240104000001c40000000000000000000000000000024724a221c3000000000000000000000000000019c8068b000000000000000000000000000000000000000000001205000002880000000001410000
  | 7, 42 => 0xb4b094c090804080000050903c8000000000000092700e81aa100000000000000000000000000001901000000000e4520e800000000206904cc1fe11b6913c613c20a6c23e120aa20a920290aa1098700000000016400000000000000001b83270900000000000024a50000000000000000034b000000000000000000000000
  | 7, 43 => 0x1f6200000000000000000000000000000000000000000000000005e300000000000000000e4300000c83000000001009000000000000000000000000000005640000042a00000000000000000000000000000000000000000000000017c70000000012090000000024c41b62000022e208c7000000000000000004e1
  | 7, 44 => 0x1707020600000000000000001e851e660000072300000000000025c709a10000000000000000000000000000000000000000000024a1000000001f6600000000000000000000000000000000000000000000000000000000000000000000000000002466000000000000000000000a410000000000000000000000000000
  | 7, 45 => 0x10811ea91e6903eb000000000000000000001f090d260000000000000000000000000000000000002326000000000b6500001cc200001ae61dc10000000024c600000000000000000000000000000000000000001ac900000000000000001c0622a200000000000004c600000000000000001c4600000000
  | 7, 46 => 0xdc1168a152809482086000000000000000000000c28232500000000000000000000000000000000000000000000000000000a450000040900000000000000000000000000001eca0000000000000000000000000000000000000000000000000c6700000d0c214a0000000000000cab0d460000000000000000000000000000
  | 7, 47 => 0xd4a048100002145000000000000000000000caa0000000025211d2612260b8a000000000000000000001da6000000000000000000000000000000000466000000001ec10000000000000000000004070000000000000d86000000000000000000000000000021a800000000000000001a66000000000000270a000000000000
  | 7, 48 => 0x4c3000021a20a4b000000000000000022a900000000000015220d4700002041000027470000000000000000000000000000000000000000028a0000000000000000000000000000000000001c44000026e6000000000000000000000000258a04890000000000000000252a16c5240100001ec600002002198313a613a21302
  | 7, 49 => 0x18a400000000000000000000054a000024460000000000000000000000002426094310c900000000000000000000000000002141092b0000148800000000000025060000000000001d690ca30000000009e302cb09ab0000000000001d6b0542000000000000000000000000000019220e2400000ec60000032100000000
  | 7, 50 => 0x178114261f86042112662643000000001aac09630000000000001e0b00000000000008e70046000000001d85000000001e270000000000000000050a000000000000000007a80000000000000000000000000000000000000ee425cb000000000000000000000ca60000000000000b240c44000000000000000000000000
  | 7, 51 => 0x32900000000000000000000000000000000054600000000000000000000000000000000000000000000000000000000000000000000000026e200000d690000000027641c48000020c200000000000000000000000000000000196800000bc423ab0000000000001381000000002566
  | 7, 52 => 0x7c800001201000000000000000006e704a6042b00000000000017650c27000001282345000000000000000000000c080b4a0000000000000000000000000c49000000000a08050c00000000000000000000000026e80000226200000c23000018060ea20000000012230a01
  | 7, 53 => 0x144a0000270614e10000256a1ae104a10000000000000000094200001f8b22421d2a13660c22084a0629000004440000000023861dc61daa26ea000000000000000000000000000000000000000005cb00000000000000000000270500000000000000000000000000000000
  | 7, 54 => 0x80b000000000000000000000000000000000000000000001d41000008850208000000000000000021491d2412240b8b0a0500000000000000001da40000000022840000000027210c2121810c4b0ba906e2000000000000000000000000000000000000000000000000000020010000
  | 7, 55 => 0x1de605241e6b0000000000000000000000001f0b148200000821000002c40d44000004c4000000000000000000001da7000000000000000000000e66000004eb06c91a24138417a20f61000000002365052623c417260c6b276606ab00000000000000000c0c060b000000000000000000000000000000000000080900000000
  | 7, 56 => 0x4430acc0625000000001a020000000000000000000011440ce70ba40000000000001e2c00000000000003692522000000000000000000001d631ecc268a000000000202000000000000000000000000000000000000000000000000000000000000000000000000000000001fc1036b06e10000000014e221cc1eab
  | 7, 57 => 0x15c200000000000000000000000000000000000008c300000000126311e90728042800000000000000c6000017e600000000000000000000000000000000000000000000000000000000000000000000000001820aa500000000000026081e6718c807ac0b280c4806ec00000000000000000000000000000000
  | 7, 58 => 0x19660000000000001fe6212900000000000000000000000005031e8c1e830000000003630000000026cb00000da8000000000000000007c3000000000000000011e10000000000000000102409640a8a0a0a00000000068300000000000000000000000000000bab0000000000a40000000000000000
  | 7, 59 => 0xa82000000000000000021c700000000000000000000000000002701000000000000000000000000000000000000000000001c860000152107c20000000000000000000008e1000000000000000000000000000000000000012200000000124400000000048c0c0200000000000000000000000000002222000000000000
  | 7, 60 => 0x2a5000000000000000001aa00000000000000000d250000000000000000000000000000000000000000000000000000000000000000000000000000000024a62082000007e80000000000000000232100000000000000000000000000000000000000000000000000001dc41c22032500000000000016e80000000018820000
  | 7, 61 => 0x14222301000000000000000000001aab000000001e8709680000000000000000000023630000070500001ec71d610e0400440000000000a816a319c300001ea20000040318a826811f2a1f021ba60e0308ab0b4300001ca90000066b000009460000000011ea0000000020e20c260000000026e700000000250a000000000000
  | 7, 62 => 0x70802a61c2a02e2000007a2000000000000000000000d48000004c801a6000000000000000000000000000000000000000000000000000003a4000000000000212a0a860000000023a119a3238300000000000000000d02052521c61d0c024c0000196400000000272819460000000000000000100a0000000007e41546
  | 7, 63 => 0x10060000000000000000000000000a6a00000000000000000000000001c2000000000000000024c91d8b000000000000274c0000000000001ec4000000000000000000000ac90ac30000016800001f051c66000000000c410c0b09c6000008a224491ee91ce9000000000000000011e60ce805280000
  | 7, 64 => 0x17ac16ec00000000000000000000000000000000000000000000000000000ee100000000000000000000000000000000000000000000000000000000000000001142000000000000000000000000000000001dec0000000000000a4700000000000026a71c6a19e4102100000000000000000d0624c800000000000014e3
  | 7, 65 => 0xa2400000000000000000000000000000000000000000000000000000d210a2603a7000000000000000000e300000000000000001862000000000a62000000000d6100000000034200000000000000000000000000000000000000000000000000000000000000001c2900000000000000000000070c00000000
  | 7, 66 => 0x12600000000000017a8000000000c06000000000000000007610000274200000000000000000000000000000000000000000000000026890b6400000000034a000000000000000000000000226500000000000000001a2102c5000024e40000234100000000000000000000000000000000
  | 7, 67 => 0xa6600000000000000000e4107cc0000000000000000000000000000212317060c470ae5000019e80000000000000000000016e516e3000000000781000022e100000ca9000023a20000000000000000000003820d2200000000000000000000000025e80000000000001f2207c600000000000000000000000000000000
  | 7, 68 => 0x4e7000000000000000000000000014422870000000000001e491d2219230789122200030b890000208100000000000000001da2000000000000000017c30fa3000000000000000000000e6404a80042000000000dc80000000000001b460000000000000000000000000d6200000000000000000000000000001e6300000000
  | 7, 69 => 0x1469196217040000000000000ce40000000000000000000000001aa3000000000000202a000000000000028b00000647248300000000000000000a2c000000000d6c08c5000000000000000000000000000001e300000000000000000000262b1e01082b0be30b290000000000000de4000000000000000000000b210a8b0a0b
  | 7, 70 => 0x74c1b660bc10000000000000000000000000000000002291002000000000000000000000000000001ac00000000000014060a83044600000000240620ca110600000000000024ab21210962060700000000000000000000000000001fc9000000000aea00000ac4000000a20000000000000000
  | 7, 71 => 0x2286000000000000000006c5000000000000064900000000000000000000000000000000000004292749000018e6000000000000000000000000000021a109cc06c300001f2c0000000000000965000000001e210d091243000000001e0600000aa2000000000881038604a20000000000000000072900000000000000000000
  | 7, 72 => 0xb610000000025e324e31c41012300000000000000000000000000000000000000000000000026210000000008a7000000000000000000000d451ae800000000000001a800000bea212700001aa60000000015820000000000001ac100000000000000000465030a00000000000000000b44000024e602420000
  | 7, 73 => 0x26010000246909c2000015a6000008690000000000c31f2900000c6c0000000021860aa602a21981230506232346000011620000000000000000168109e9000000000000218a0000000016c1104200000000000017a50000000020651b0212c607a7000000000b6200000000000020a500000000226124eb000003ca00000000
  | 7, 74 => 0x94b0000232a00000000000000001ce5000000000000000014c20000000000001e8817621102008300000000000000000000000017010ec105c9000000000a6b00000aca00000000000000000000000000001dc20000000000000000000000000000000000000000000000000000000005620000000000000000000000000000
  | 7, 75 => 0xb4721ab1d4b00000000000000000000212c1282000025ea07ea00000248000000000000000000000000000000000000000000000000116107e5000000000000000000000000000000002006130600000000000000000000000000000000000000000000174226820aec00000203220a2089000000000661204a
  | 7, 76 => 0x178a000000000000000000001f230000000010281e020000006600860000000000001a620e4a0c69000006a902eb25e91e071a861101060907e9274a000001a7056100001f8500001a84000000000c6400001122210a076300000000000000000000070b0000000000001b220284000019e217ab13e60a6316eb
  | 7, 77 => 0x1fca274300000000000000000000000000000000000000000000000000000000114801c1000000000000000000000ee9062100000000000000000000258900432727254a23c100000000000000002529000000000d8800001b8203e500000204000000000000000000000ac8000000000088000000000000000000000000
  | 7, 78 => 0x21030000000000000000000020c50000000000000b420000000000000000000009c900000000000000000000000000000000000003280108000000000e460000000006ea0000000004620000000004840000000000000000000000001584000000000000000000000000000000000000018300000ccb0000000000000000
  | 7, 79 => 0x18c30000000024e700000000000000000000000000000d4108450000260218c207a9000000000000000000002542000000000000000000000c25000000001341000024290000000000000341000000000667000000000000000024a9268b1c0a00000000000022e50000000000000000080700000de800000000000000000000
  | 7, 80 => 0x8aa00000000216900000000000000000d070000000000000000000000001ee513260000000021ea000000000e630000000000000000000000000000000000000000000004410000000000000000000000000000000000000000000024c1000000000000000000000000000017ca1e430000
  | 7, 81 => 0x74711a6074b000000001f49000017c6000000001588000000000bc7000016e1000000000000000000000000000008a9000026610ccc0ae300000000000000000000000026ec23a800000000000023a506a103810000000000000000000025e50000000000000000000000000000000000000000000000000000000000000000
  | 7, 82 => 0x16260000000000000000000000000000274405e70081166a000000000000000000000c87000023091fa926c900000dc6000003272745176a05680000000026830a430000000000000000000006eb000000000501000000000000000025ec034307ec00001e8105810000000000000000000007e102460b09000000001d041ce7
  | 7, 83 => 0x1f2b1e89000000000000000000000000000003a90000000000001a421dc700000000264b128600000be80545000000000000000000000000000000000000116400000000000000000000000008a4000000002746000003ab0000226a0000000019431642212b000000001e8a02e41be60000
  | 7, 84 => 0x1c621ce31ac700000000000000000d8402c9000011e201a900000000130109830000000000000000172a0ee70000000000000000000000000d6800000000110a000003e61c25000000000000000000001e411c050bc50a87048b00001e0306031d4523a30bcc00000000000000000000000023061f6a00000000000000000000
  | 7, 85 => 0x5c7000000000000000000000000000000000000000003cb0e011d29136208490000000000000000000023821da91f881268076b00000000000000000000032c00001d2326a500002561000000000000000010c70000000000000b6c07a60000038c14460000
  | 7, 86 => 0x12a11a081506000000000000000000000827200900000000000000000000248100001c8a000000000000000000000000000002810000042c0b8100000cc10000000000000e4c1a2200000000000000000000088313830448000000000000000021aa1d4a0dc200001ec3148400000000
  | 7, 87 => 0x9850000000000001ea71d010000000000000000000000000000000000000000000000000000000000000000000000000000000000001741194122851e2900000000000000000000000023611906000000000000000000000000000000000000000004ac19030000000000000000000000000000000000000000000000000000
  | 7, 88 => 0x176600001c020000098900000000000000001ee70a27000000000000000000001dea0000000000000000000000000000000016060a2300000ca703a200000000000018020f49000006271f420148120200000000000000000000000022e90e4800000000000000000000000000000000000000000485
  | 7, 89 => 0x21a500000749000000000b4500000000000000000a6700001e8200000000000000001d65120a00000000000003640d65000022e606c7000000000000214200001de900000000000010c3000000001e08000000000000000000000000000000000000000027410000000000000000000000000000000000000000000000000000
  | 7, 90 => 0x21c90000000000000000000000000a2a03e8260618c607aa0d6a0000000000000000000000000000000024e800000000248900000000000000000000000016620e6205e1000005c300000000000016690c8104640a890a09034926a9000000001a680f45000026870000244a068714020aac0be70000000024020ce120c92545
  | 7, 91 => 0x104600000000000000000000000000000fa2000000000000000000000000000000000000000000000000000019e6000000000000000000000000000000000000000018a200001f2500000ca4000000001ac4116600000000000000001c421421058414c617c900000000000000000000
  | 7, 92 => 0xc660146000000000000000000000000000000000cc700000000000000001f651ca2000026650000000000000000000000000000000000000000000000000000000000000000000009cb0000090a12e20000000003a6000000001ea1000000000000000025410000000000001cca000000000000268c000000000000
  | 7, 93 => 0x17e2000000001c0900000000046300000000000004a5000026450865000006650000000000000000000000c101e10000000000000000262700000000000026ab00000000000000000000000003cc000000000000000008440b840000000000000000000000000000132110620000000006e600002283
  | 7, 94 => 0x6a500000000000000000000000000000000148100000726042600000000000000000000000000000000000000000000000000001d2812280b8c000000000000000000001da800000000000000000000000022880000000000000c4c1aa80366000000000000000000000000000000000000
  | 7, 95 => 0x2ca000000001e6804a9000000000a6900000000000000001a0300000000000000000000000013e20000000000000000000000001b6a00000383000000001926000000000000000000000000000000001761000000000000000000000000000009e50000000000000c6a04450000000023220000000000000000
  | 7, 96 => 0xc07000000000000000000000d820000000000002708000000000000000000000fe104c9000021a41a630000000000000000000000000000000000000000152419280000000000000000000000000000000000000000046b0467000000000ec30000000000000000000000000ca10000000000001ca5000000000000
  | 7, 97 => 0x16a800000000000011050000000024cc00000000000021c810cb0000256900000000000000c800000000000021010000000000000000154800001cc500000000000000000000000000000000
  | 7, 98 => 0x904040410051565000000011e28272b092300e40000000000000101000000000000000020e400000000000000000000000017a104cb0000000008a6038800000000000000000000266900000000000012e10000000000000000000002e600000000000000002126000020421342000000000000000000000000000000000000
  | 7, 99 => 0x7061f04000000000000000000000000000000000000016100001ae3000000000000000009ca000009eb216620a600000000000022a50d8126c7062b0000000000001d2100000000000016650000000000001bc60201000000000000000000000000220100000000000024451ec816a21621034801880cc80000000025e1
  | 7, 100 => 0xb2c00000000000008030000000011680000000000000000000018e10000000001a500000bc600000c4300000baa00000000000000000000000000001281236b0000000000000000000004e9016600000ae2000000001e6210e50ec4028900000000000000001dc805eb050200001ea400000fa6086b0000
  | 7, 101 => 0x11810ae1000000000ea609c700000000000000000000210c1ac600000000000001a300000000000000000000000000000000000000000000000000000000000000000423000000000000000000000000000000000000212227610000000000001d2c1368084c0000264724a423aa23881dac074100001dca1b651845074a
  | 7, 102 => 0x234a0000000000000d0800000000000010610000000000001cc109c5000000000000000000000000000000000000000025a11a480aab038702210a040000000005050000000000000000000000000000000000000f21000000000000000000000000000019c4000000000000000000001ea60000000000000000000021461f06
  | 7, 103 => 0x1141000000000000000000000000000000000000000015c10000000000000000000006e900000000000000000000000000000000000000000000000000000000000000001d0a03010000000000000000000000000000000000000000000000000000000000000000044c17a40f6304690347224a0000000000001de300000000
  | 7, 104 => 0x224100001ba1000000000000000000001a0600000000000024ca0da121e10ee211c104270000000000000000000016010000000000000000000010e109811d08002800001fa500000000000000000000000003a10000000000001785270b000000001d090000000000000000000000000b6a0000000000000d830000
  | 7, 105 => 0x15e908010000000000000000000000000000000000000000000000000000000011a11f240000000000410000170a01ab000000001146000000000000000025850000146a0000000000000903010319630000210720611b0612c207461d0b0000000000000000212420a100000000000000000000000016a401210000040a
  | 7, 106 => 0x96900000000000000000c2c0000000000001885000016a100001a4100000000250510a500000000000000000000000018252603156614e800000000000000000000000027621c610d2811c21f450ac118e20ba6000000000000000015e5000000000000000000001a82000000000000000011240000
  | 7, 107 => 0x4ca00001f26000000000000000000000000000000001e860000000009a500000d0a0c0a25860000000000000b8208420000000000000b2321251e23000000000000048a00000000152300000000000000000309000000000000000000000000000000000000
  | 7, 108 => 0x5410000000000000000000000000000000002e10000000007c7222a0000000000001044000000000000002300001f810742000000000000000023a700000000000026e50de30000000000002102000024a8118607070000028600000000000000001e8b000000000000
  | 7, 109 => 0xee305a50000000024650000000007c9000000001109000000000000000003ec0000000000000000000008c100000000000000000000000000000000000000000000000000000000000000000000000002410000000001420000000000000000000000000000000000000385000007ca0000000000000b69
  | 7, 110 => 0x20c1094107cb00000000194800000000000000000ca80000000002670000000000000000000000000000058800001d25000000000000000022210000000000000000000000000000164100000fa10e820689000000000000000000000000000000000000000000000000000000000000000000000000
  | 7, 111 => 0xc4501a200000000000024e510230000000000000000000000480000000021c2000000001da31b4107010e4900000000000000001542000000000000000000000aaa000000000000000000000000000000000000000022810000026900000000000000000000000000000000000000000bec1465000000000000
  | 7, 112 => 0xcc40b630acb0000000000000e06000000000000000000000000000000000000000000001f82126200000a2207a11b26014323c30000000000000000000000000000000010e900000000000000000000000000000000000018650ba30000000000000000000000000000000000002707000000000b6804c70ac2000000000000
  | 7, 113 => 0xbc800000000000000000b01000000000000000000000000000000000000000000002667040c1deb0c6500000000000000000000098b00000000000026eb23a41dc9000000000000000000000000246a00002604220919c2184917490344208a18c407ab0a4909020402070a1961170301842329092100e2000000000000
  | 7, 114 => 0x15a20000000000001e840000086700000000000000000000000006430000000007c5000009a900000000000000000000228a000000000000088b0000000014491f070000000016e70000000002850000000019a600000000000000000000000000000000000000000000
  | 7, 115 => 0x1e2600000000112100000000000000000000000024cb170c00000000000000000000000000000362000019e1000000000f410000114300001acc0000000024250000000000002623230a1faa1ca10eea10a60e83000017cc072c0000000000001fe2146203c60a070000000000000000
  | 7, 116 => 0x52a0000000000000000000002c21709000000000000000000001ec90000000016460000000000002206000000000000264900000000000000000000000013610000138607e7000009e707430000000023c600000000000000000de611a20000000000000000
  | 7, 117 => 0x25c50000000003c400000aa700000000000000000000000000000c630000000022050b4800000000000000000000000000000000000022890000000000000000000000001126076700000000000000000000000026e31b2100630b830a811066000004e200000000000025090ee600000000000017c800000000
  | 7, 118 => 0x2a30000000000000000242a10a91a0415020000000027290c2918291d06170800000000000021e9000000001f011c8900000725000000000000000008460b86000000000b850000000000000000000000000062000000000000000000000000000000000ce917c20f81000000000000000000000000000026c5000000000000
  | 7, 119 => 0xa060000000000000000000015830ba8000000001c430000064b10a2054b0000000000000000000000000000000000000000000000000000000006cb000021a321611caa0084000014a2000000000000000000000000000000000000
  | 7, 120 => 0x22c51f4612060000192100000000030b000022ea0000000000000000000000000000000000000000000000001a46000000000000000000001c65094400000000266b0000000000000c2426a3032b0000000000000000000000001c69000000001d830b0b06e500000000000020ea038b000000c200000000
  | 7, 121 => 0x192400000000000017050cc20000000000001e2b00001988000000001d460582000000000000000000001f8a0000040b00001b8600000000272c08e90000000000000000000008e305e90d2700000000000000000000086102cc0000000000001de50ec800000000000000000000000000000000000000000000000017a7096c
  | 7, 122 => 0xac51f8723ac000000000000000000000000000000000000000014610a6100001182070300000000000000000000000000000e08000024a700000000000000000000000000000000000025021c850887000000000000154100001686244100000000000000001be207e30000000000000000000000000000000021e6
  | 7, 123 => 0x2105000000000000000000000c0500000aa9000000000000000000000000000007a50000000000000ce30aa300000000272a0000000000000000000000000000000000000000000022450000000000000000000000000909000000000000030300000000000021e50000276820e90e8600000000000000000c620a88000025e7
  | 7, 124 => 0x26000000000000000000001e2200000000000000000000000000001fa1000000000000000000002725144525650000000000000000000024e100000000000000000000000000000000000000000000000000000000000009060449040600001001000024c71cc90425092500e600000000000000000000000000000000
  | 7, 125 => 0xc040000000001a1000000000000000000001da10000050b00000000000000000ae40ea300000000000000000da4000000000000000000000ce200000000050403c9000000000000000000000000000000000000272600000000000025eb026507eb19a200000000000000000000000000000000000000000000000000000000
  | 7, 126 => 0x202615ea270c1128000010410000000000001fa200000000000024ec00000000170b00000000000000001ecb044200000b6b0b0300001de11aa5054c0c8b038408471acb00000ac7226600000186000007c40000000000001b6118410a28000017cb0000000000000000236921cb0ba70124000000000000000002a7000004a4
  | 7, 127 => 0x90c00000000096a000005060ea10346000000000000000000001b4205630000000020c61aa20000000000000000000000000000000021a6000000000000000000000000000000000000000011c600000000124615260304000000000cc60000000000000000052b00000000000000000000104808250000
  | 8, 0 => 0x1e30000000000000000056a0000048600000000000000000000000000000167004b004705ca000000000000060902e606a7000005aa0000000000000000000000000423038600000000058500000000000000000000000000000000000000000000000000000000000000000000000000eb000000000501
  | 8, 1 => 0xc90000000000000000014b000004aa000000000000000000000000036602c2020803a2058b0161000000cb0000018900000000000002410000000000000000000001cb01810368016b0603018b052603c20522046901a2046a00000000000006c7000000000000002a05c600c1000000000000
  | 8, 2 => 0x3e900000000058900280163010500c3000001a700000000054900000000000001c6000000000000000003c600000000034a0025000000000000000001a4042500000000000006810000000000000000000000000000000001c50482000000660000000000000000000000000000000002e2000000610000000000000000
  | 8, 3 => 0x3410042000000000000000000000000000000000000066100000000000000000000000000000206000005830000038803a1000000000000000000000000000006430000000000000000012b000000000000000000000000000000000001020300000000000000000000000001410000000002690000
  | 8, 4 => 0x1cc0000000000000000000000000000062900000000000001e4000000000401004800e10000000000000109044900000000010700000000000000000000000004a60346000000000000000000000000000004e1042b000004e500000000000000000000000000000000000000000000016504430000000000000000
  | 8, 5 => 0x20100000000000004a2000000000000000000000000000000000000000001250000000000e90000000000000000058702a100410000000004c104c5042700000000000000000000002c000000000000000001ab006301ac000000000000000004c3000004c70000000200000145032200000000000000000000000000000046
  | 8, 6 => 0x56201c200270008000000000000000002a202a60021000000e70000026505020000050601c901e800000169000003a60381008102c60000000005650403062500620000000000000000000000000000054a00000000000000000000000001a50000000000000000000000000000000004450000000000000000000000000000
  | 8, 7 => 0x3e5000004a90000000000830361006400000000000000e300000000018300000000000000000000008b0000004a0000062b03630204004c000000000000000004e3000004e7048a0000000000000000010b000000000000000000000000000000000000000000000000000000000000000000000000000005a50566
  | 8, 8 => 0x29000000000000000000000000000000000000048100220000000006a30342022105c90301000000000000000000000000000005a90000000005e20000000006210000002b06830000000000000000000000000129000000000000000001c4000000000000000006c500000000000000000000000000000000000000000000
  | 8, 9 => 0x8700040000000005c200a3000000000000042100000000000000000000038300000000000000000000000000000000000000000000062301a8000000000000000000000000000000000000000000000000000006c30000000003c10461000004650000060700000000044701e1000000000000000000000000000000000000
  | 8, 10 => 0x30000000000000000000000000000060500c7000000000000000006a5004400000000000001a9034501aa000000000000000000000000000004620521012301a10466000000000000000000000000000003020000000001ca05c505a20429000000000000000000000000056101c10000066302820000000000000000
  | 8, 11 => 0x4cb0242040b0000000000000000000000000000000000000000000001a3000000000000000005e100000000000000000000000002c1000000e50000000000000000000003820000062701c300000000000000000147048500000101000000000000000006c1000006410000000000000000000000000261000004e90000
  | 8, 12 => 0x1a60089000000000000000000000000000002e1000000000000000000000000000000000000036200000026000000000049000000000000000000000000054204a105460000000000000000000003640000000000000000000004c90409000000000000000000000000014900c5000005e60000000000000000054500000000
  | 8, 13 => 0x202000000000000000000000000000000a1000006ab05a60000000006a10000000000000000000003e10349004500000489028600ab00a700000000044100000000000000000000000000850000000000000000000005810569000600000000000006c90000000000000000000001850000000000000000000001e60000
  | 8, 14 => 0x4a500680024000001c700000000000000000187000000000000000000000000044b032100000000000003840000000000000000000000000000000004070000024606cb0000000000000000000000000000000000000000000000000043000004eb0000000000a500000103000000000000000000000000
  | 8, 15 => 0x1e20000060b00000000002300000000000000000000000006a904050000060100000000000000000281054100000000000005a100a9000000000000000000000000000000000121014300000000000001270306000001c8000005c100000000000000000000000000000000000000000000032600000000000000000000
  | 9, 0 => 0x2600000000008100610000004100010045000000a3000000000000000000000000000b0000000000a100000083000500490000000000000000000000000065000000000000000000000000000000000069000000000000000000000000000000000000000700210000000300000000000000000000000000090022
  | 10, 0 => 0x10000
  | _, _ => 0

def perms63 : List (List (Nat × Nat)) := [[], [(2, 4)], [(1, 3)], [(1, 3), (2, 4)], [(0, 2)], [(0, 2), (0, 4)], [(0, 2), (1, 3)], [(0, 2), (0, 4), (1, 3)], [(0, 4), (0, 2)], [(0, 4)], [(0, 4), (0, 2), (1, 3)], [(0, 4), (1, 3)]]

def filter63 : Nat → Nat → Nat
  | 4, 0 => 0x20
  | 5, 0 => 0x2000000000000100200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000
  | 5, 1 => 0x20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000004000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000010000000000000000500000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 6, 0 => 0x10008000000000001e02000000000000100200000000000000000000000000000002000000000000000040000000000000000000000000000000000000000000080000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000400000000000000040000000000000000000000000000002100000000000000000000000000000020000000000000000100000000000000020000000000000000000000000000002000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100140000000000010000000000000001000000000000000100040000000000000000000000000000000000000000000000000000000000000021000000000000000000000000001000200000000000000000000000000000000000000000000000200000000000000000000000000000000100000000000000000000000000000000000000000010002000000000000000010000000000100020000000000000000000000000000000000000000000000000000000000000002000000000001000200000000000000001
  | 6, 1 => 0x2000000000000000300000000000000020000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000002000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000008000000000000000002000000000000000000000000000000004000000000000000000000000000000000000000000500000000000000000c000000000000000002400000000000000040000000000000000000000000000002000000000000000040000000000000020000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000040000000000000004000000000000000000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000000000004000000000000000000000000000000010000000000010020000000000001000000000000000000000000000000000020000000000000000000000000001000000000000000000000000000000001000200000000000000000000000000000000
  | 6, 2 => 0x1000000000000002000000000000000240000000000200000000000000000002000000000000000200000000000000004000000000000002000000000000000200000000000000001000000000000000000000000000000110000000000100000000000000000001000000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000100000000000000110000000000008001000000000000001100000000000000000000000000000030000000000000000800000000000000000000000000000020000000000000001000000000000000080000000000000018000000000000000000000000000000100000000000000000000000000000003000000000000000000000000000000010000000000000000000000000000000200000000000000000000000000000800000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000300000000000000000000000000000000400000000000000000000000000000004000000000000003000000000000000000000000000000012
  | 6, 3 => 0x4000000000000000000000000000000020000000000010000000000000000002000000000000000000000000000000030000000000000000000000000000000200000000000000010000000000000000400000000000000000000000000000000000000000000002000000000000000040000000000000000000000000000002000000000000000040000000000000004000000000000000000000000000000000000000000000000000000000000002000000000000000100000000000010020000000000000000000000000002000100000000000010000000000000000002000000000000000300000000000000000000000000001001000000000000000000000000000010030000000000001000000000000000000100000000000010020000000000001000000000000000000000000000000000008000000000000000c00000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000200000000000000004000000000000000000000000000000020000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004
  | 6, 4 => 0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000010000000000000000000000000000000100000000000000000000100000000000000000000000000004000000000000000002000000000000000010000000000100000000000000000000000000000000000000000000000004020000000000000000000000000000000010000000000000000000000000000002000000000001000200000000000100000000000000000000000000000000000000000000000000000000000000010000000000000001000000000000000100000000000000000002000000000000000010000000000000000000000000000000100000000000000000000000000010000000000000011002000000000001000000000000000000008000000000000000000000000000000080000000000100008000000000000e000000000000000000800000000000000000000000000000004000000000010000000000000000080000000000000000000000000000000000400000000000000040000000000000004000000000000000400000000000000000000000000000000000000000001000400000000000000040000000000000004000000000000000000000000000000000000000000010010
  | 6, 5 => 0x40000000000010000000000000000000000000000000000000000000000010000000000000000000200000000000004000000000000010000000000000000000000000000000000004000000000000000400000000000000000000000000000001000000000000000000000000000000000000000000000001000000000000000100000000000000200000000000100000000000000010000000000000000000000000000000000020000000000000000000000000000000200000000000000001000000000000000100000000000000000000000000000020000000000000000000000000000000000000000000000020000000000000000000000000000000200000000000000020000000000000000900000000000000010000000000000000000000000000000400000000000000010000000000000001000000000010000000000000000000010000000000000001000000000000000100000000000000000000000000000000000000000000004000000000001000400000000000100040000000000010000000000000001000000000000000100000000000000010000000000000001000000000000000000004000000000000000500000000000000040000000000100000000000000000000400000000001000000000000000000004000000000010000500000000000000250000000000100000
  | 6, 6 => 0x100000000000000040000000000000000000000000000004000000000000000400000000000000000000000000000000000000000000000000000000000000020000000000000002000000000000000040000000000000000000000000000002000000000000000000000000000000000000000000000000400000000000000000000000000000004000000000000002000000000000000200000000000000000000000000000002000000000001000400000000000000040000000000010004000000000000000400000000000000010000000000000000000000000000000440000000000100000000000000000004400000000000000140000000000010024000000000000000400000000000000000000000000100000000000000010000000000000000000100000000000100000000000000000000400000000001000000000000000100000000000000000000400000000000004000000000000000010000000000000000400000000001000000000000000100000000000000001000400000000000000000000000000018024000000000000000400000000000080040000000000004000000000000000000400000000000000040000000000000010000000000000004000000000000140000000000000000040000000000000000000000000000100000000000000000040
  | 6, 7 => 0x2000000000000000400000000000000010000000000000001000000000000000000000000001000000000000000000004000000000000000400000000000000040000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000080000000000000020000000000000002000000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000002000000000000000240000000000000000000000000001000000000000000000000000000000000004000000000000000400000000000000040000000000000000000000000000000000000000000000040000000000000005000000000010004000000000000000040000000000000000000000000000000100000000001000400000000000000001000000000000000400000000000000010000000000100000000000000000002000000000000000040000000000000000000000000000000400000000000000140000000000000004000000000000000400000000001000000000000000000004000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000020
  | 6, 8 => 0x1000000000000000000000000000000040000000000000004000000000000000400000000000000000000000000000020000000000000000000000000004000000000000000400004000000000000000000000000004000000000000000000020000000000000002000000000000000010000000000000000000000000000000000000000000000000000000000000004000000000000004000000000000000040000000000000040000000000000000400000000000000000000000000000000000000000000000400000000000100000000000000000000000000000000000400000000000000010000000000000000000000000000000100000000000000010000000000000004000000000000000000000000000000000000000000000001
  | 7, 0 => 0x24000000000000803500000000000000240000000000018020000000000001001500000000001100000000000000010015000000000001001100000000001000000000000000000031000000000010000900000000001100110000000000108001000000000010002100000000001080210000000000010018000000000000001800000000001000200000000000500008000000000010000000000000000000040000000000402024000000000000001000000000002080100000000000210010000000000001203000000000000180000000000000108000000000000041000400000000004100040000000000010015000000000050000400000000005000000000000000500000000000000000e0000000000000406000000000000000e000000000000001000400000000000100240000000000000000000000000000e00400000000000000200000000000410004000000000010a00000000000001000000000000000100000000000000010000000000000001100080000000000000009000000000021c034000000000001e02400000000000100000000000000010015000000000001e01c0000000000100034000000000001002000000000000000350000000000010034000000000011003400000000003080200000000000100000000000000010002000000000001000000000000000100020
  | 7, 1 => 0x10002000000000001000200000000000100020000000000010000000000000001000200000000000100000000000000010002000000000001000200000000000110020000000000011000000000000001000200000000000100008000000000000e024000000000000e0000000000000010008000000000011000c0000000000000004000000000000e00c000000000011002400000000001100240000000000000009000000000001003400000000000100140000000000410005000000000001000000000000001100040000000000000004000000000010000000000000000000090000000000012030000000000000000000000000004000050000000000000000000000000001800c00000000000080350000000000008020000000000000001c00000000005100140000000000010020000000000041000000000000000140040000000000012030000000000001c0040000000000010008000000000001803400000000000180200000000000010018000000000000400c000000000000802000000000000000040000000000410000000000000001801000000000000100150000000000000004000000000001000d000000000040000500000000000180000000000000018035000000000001000400000000004100000000000000008020000000000000802400000000000180250000000000018035
  | 7, 2 => 0x10003400000000000080440000000000010024000000000010000400000000001000040000000000100000000000000000400400000000000100040000000000018024000000000000400000000000000000240000000000004000000000000010001000000000001000400000000000100040000000000010004000000000000140040000000000100040000000000011000000000000000100350000000000010004000000000000000000000000000000200000000000100020000000000010002000000000001000040000000000004034000000000001000c000000000010000000000000001000100000000000100004000000000010000000000000001000000000000000100000000000000010000000000000000000000000000000004020000000000010001400000000001000200000000000100034000000000010003400000000001000000000000000100020000000000010002000000000000000080000000000100034000000000000002000000000001000040000000000110010000000000011000000000000001100000000000000110000000000000010002000000000001100000000000000110000000000000010000000000000001000050000000000000025000000000010000000000000001000250000000000100000000000000010000000000000001000200000000000100000
  | 7, 3 => 0x10000000000000001000200000000000004000000000000000000c00000000000040040000000000000015000000000001000000000000000100140000000000010020000000000000000c0000000000002000000000000000000c000000000000201400000000000100200000000000000004000000000000000400000000001000340000000000010000000000000001802400000000000180080000000000010035000000000000202000000000000000240000000000018004000000000001802000000000000140040000000000000010000000000000400400000000000100140000000000110025000000000010004000000000001000400000000000100000000000000010002000000000001000440000000000100004000000000010000000000000001000040000000000100024000000000010000000000000001000050000000000000054000000000000007400000000000000000000000000100020000000000010004400000000000040000000000000100034000000000011003400000000001100050000000000010024000000000001001d000000000000006400000000000000200000000000100020000000000000000400000000000100150000000000004020000000000011000000000000001000400000000000100040000000000010000000000000001000000000000000100074
  | 7, 4 => 0x1400000000000000140000000000000044000000000000007500000000000000040000000000010015000000000001003000000000000100110000000000410005000000000001800000000000000180150000000000000034000000000000003400000000000180200000000000100040000000000010000000000000001100000000000000000041000000000010002000000000001000000000000000010000000000000001001500000000000100000000000000010015000000000010004000000000001000400000000000100040000000000010004000000000001000000000000000000044000000000000805400000000000100240000000000010015000000000010004000000000001000010000000000000054000000000000001400000000001000010000000000100001000000000001802400000000000000140000000000100000000000000010000000000000001000010000000000100001000000000000800400000000000100300000000000000001000000000000000100000000001000210000000000000008000000000000002000000000000080350000000000100000000000000010000000000000001000040000000000100000000000000010001400000000001000040000000000100034
  | 8, 0 => 0x1001500000000000000750000000000010017000000000001001d00000000000100350000000000010015000000000001803500000000001100140000000000110014000000000011001400000000000100350000000000110014000000000011001400000000001100340000000000100034000000000001801500000000000100350000000000000035000000000010003500000000001000340000000000010035000000000001003500000000000180350000000000010015000000000010006500000000001000250000000000100075000000000011003500000000001000340000000000100024000000000011003400000000001000200000000000100034000000000010003400000000001100340000000000100025000000000010002000000000001000200000000000100020000000000010a024000000000011801c000000000011803400000000004100350000000000018035000000000041000500000000000100150000000000410005000000000041001d000000000001803500000000000100350000000000108031000000000070003400000000005000040000000000502004000000000010a034
  | 9, 0 => 0x7500000000000100350000000000010035000000000000003500000000001000350000000000008035
  | 10, 0 => 0x35
  | _, _ => 0

def proof63 : Certificates := (count63, rowWords63, slotCount63, indexWords63, perms63, filter63)

def roots63 : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000]

def cuts63 : List CutBank := [(0xffff0000ffff, 8, 0, roots63),
  (0xff00ff00ff00ff, 8, 0, roots63),
  (0xf0f0f0f0f0f0f0f, 8, 0, roots63),
  (0x3333333333333333, 8, 0, roots63),
  (0x5555555555555555, 8, 0, roots63),
  (0x33003300330033, 7, 0, roots63),
  (0xffffffff, 6, 0, roots63),
  (0xff000000ff, 5, 0, roots63),
  (0xf0f00000f0f, 5, 0, roots63),
  (0x333300003333, 5, 0, roots63),
  (0x555500005555, 5, 0, roots63),
  (0xf000f000f000f, 5, 0, roots63),
  (0x55005500550055, 5, 0, roots63),
  (0x303030303030303, 5, 0, roots63),
  (0x505050505050505, 5, 0, roots63),
  (0x1111111111111111, 5, 0, roots63),
  (0x330033, 4, 0, roots63),
  (0xff00ff, 4, 0, roots63),
  (0x33333333, 4, 0, roots63),
  (0x3300000033, 4, 0, roots63),
  (0x50500000505, 4, 0, roots63),
  (0x3000300030003, 4, 0, roots63),
  (0x11001100110011, 4, 0, roots63),
  (0xffff, 3, 0, roots63),
  (0xf0f0f0f, 3, 0, roots63),
  (0x55555555, 3, 0, roots63),
  (0xf0000000f, 2, 0, roots63),
  (0x5500000055, 2, 0, roots63),
  (0x30300000303, 2, 0, roots63),
  (0x111100001111, 2, 0, roots63),
  (0x5000500050005, 2, 0, roots63),
  (0x101010101010101, 2, 0, roots63),
  (0x33, 1, 0, roots63),
  (0xff, 1, 0, roots63),
  (0x505, 1, 0, roots63),
  (0xf0f, 1, 0, roots63),
  (0x3333, 1, 0, roots63),
  (0x5555, 1, 0, roots63),
  (0x30003, 1, 0, roots63),
  (0xf000f, 1, 0, roots63),
  (0x110011, 1, 0, roots63),
  (0x550055, 1, 0, roots63),
  (0x3030303, 1, 0, roots63),
  (0x5050505, 1, 0, roots63),
  (0x11111111, 1, 0, roots63),
  (0x300000003, 1, 0, roots63),
  (0x500000005, 1, 0, roots63),
  (0x1100000011, 1, 0, roots63),
  (0x10100000101, 1, 0, roots63),
  (0x1000100010001, 1, 0, roots63)]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cutsEq63 : cuts63 = initialCuts 63 bounds63 := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l4p0 : testBlock proof63 10 4 0 2 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

theorem layer63k4 : testBlock proof63 10 4 0 2 (graphGoal 63) raw63 cuts63 = true :=
  check63l4p0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5p0 : testBlock proof63 10 5 0 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5p6 : testBlock proof63 10 5 6 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5p12 : testBlock proof63 10 5 12 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5p18 : testBlock proof63 10 5 18 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5p24 : testBlock proof63 10 5 24 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5p30 : testBlock proof63 10 5 30 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5p36 : testBlock proof63 10 5 36 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5p42 : testBlock proof63 10 5 42 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5p48 : testBlock proof63 10 5 48 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5p54 : testBlock proof63 10 5 54 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5p60 : testBlock proof63 10 5 60 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5p66 : testBlock proof63 10 5 66 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5p72 : testBlock proof63 10 5 72 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5p78 : testBlock proof63 10 5 78 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5p84 : testBlock proof63 10 5 84 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5p90 : testBlock proof63 10 5 90 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5p96 : testBlock proof63 10 5 96 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5p102 : testBlock proof63 10 5 102 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5p108 : testBlock proof63 10 5 108 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5p114 : testBlock proof63 10 5 114 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5p120 : testBlock proof63 10 5 120 2 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5r0n12 : testBlock proof63 10 5 0 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 0) (a := 6) (b := 6) check63l5p0 check63l5p6

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5r12n12 : testBlock proof63 10 5 12 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 12) (a := 6) (b := 6) check63l5p12 check63l5p18

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5r24n12 : testBlock proof63 10 5 24 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 24) (a := 6) (b := 6) check63l5p24 check63l5p30

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5r36n12 : testBlock proof63 10 5 36 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 36) (a := 6) (b := 6) check63l5p36 check63l5p42

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5r48n12 : testBlock proof63 10 5 48 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 48) (a := 6) (b := 6) check63l5p48 check63l5p54

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5r60n12 : testBlock proof63 10 5 60 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 60) (a := 6) (b := 6) check63l5p60 check63l5p66

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5r72n12 : testBlock proof63 10 5 72 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 72) (a := 6) (b := 6) check63l5p72 check63l5p78

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5r84n12 : testBlock proof63 10 5 84 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 84) (a := 6) (b := 6) check63l5p84 check63l5p90

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5r96n12 : testBlock proof63 10 5 96 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 96) (a := 6) (b := 6) check63l5p96 check63l5p102

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5r108n12 : testBlock proof63 10 5 108 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 108) (a := 6) (b := 6) check63l5p108 check63l5p114

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5r0n24 : testBlock proof63 10 5 0 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 0) (a := 12) (b := 12) check63l5r0n12 check63l5r12n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5r24n24 : testBlock proof63 10 5 24 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 24) (a := 12) (b := 12) check63l5r24n12 check63l5r36n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5r48n24 : testBlock proof63 10 5 48 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 48) (a := 12) (b := 12) check63l5r48n12 check63l5r60n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5r72n24 : testBlock proof63 10 5 72 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 72) (a := 12) (b := 12) check63l5r72n12 check63l5r84n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5r96n24 : testBlock proof63 10 5 96 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 96) (a := 12) (b := 12) check63l5r96n12 check63l5r108n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5r0n48 : testBlock proof63 10 5 0 48 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 0) (a := 24) (b := 24) check63l5r0n24 check63l5r24n24

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5r48n48 : testBlock proof63 10 5 48 48 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 48) (a := 24) (b := 24) check63l5r48n24 check63l5r72n24

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5r96n26 : testBlock proof63 10 5 96 26 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 96) (a := 24) (b := 2) check63l5r96n24 check63l5p120

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5r0n96 : testBlock proof63 10 5 0 96 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 0) (a := 48) (b := 48) check63l5r0n48 check63l5r48n48

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l5r0n122 : testBlock proof63 10 5 0 122 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 0) (a := 96) (b := 26) check63l5r0n96 check63l5r96n26

theorem layer63k5 : testBlock proof63 10 5 0 122 (graphGoal 63) raw63 cuts63 = true :=
  check63l5r0n122

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p0 : testBlock proof63 10 6 0 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p6 : testBlock proof63 10 6 6 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p12 : testBlock proof63 10 6 12 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p18 : testBlock proof63 10 6 18 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p24 : testBlock proof63 10 6 24 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p30 : testBlock proof63 10 6 30 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p36 : testBlock proof63 10 6 36 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p42 : testBlock proof63 10 6 42 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p48 : testBlock proof63 10 6 48 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p54 : testBlock proof63 10 6 54 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p60 : testBlock proof63 10 6 60 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p66 : testBlock proof63 10 6 66 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p72 : testBlock proof63 10 6 72 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p78 : testBlock proof63 10 6 78 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p84 : testBlock proof63 10 6 84 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p90 : testBlock proof63 10 6 90 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p96 : testBlock proof63 10 6 96 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p102 : testBlock proof63 10 6 102 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p108 : testBlock proof63 10 6 108 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p114 : testBlock proof63 10 6 114 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p120 : testBlock proof63 10 6 120 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p126 : testBlock proof63 10 6 126 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p132 : testBlock proof63 10 6 132 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p138 : testBlock proof63 10 6 138 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p144 : testBlock proof63 10 6 144 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p150 : testBlock proof63 10 6 150 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p156 : testBlock proof63 10 6 156 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p162 : testBlock proof63 10 6 162 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p168 : testBlock proof63 10 6 168 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p174 : testBlock proof63 10 6 174 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p180 : testBlock proof63 10 6 180 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p186 : testBlock proof63 10 6 186 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p192 : testBlock proof63 10 6 192 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p198 : testBlock proof63 10 6 198 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p204 : testBlock proof63 10 6 204 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p210 : testBlock proof63 10 6 210 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p216 : testBlock proof63 10 6 216 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p222 : testBlock proof63 10 6 222 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p228 : testBlock proof63 10 6 228 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p234 : testBlock proof63 10 6 234 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p240 : testBlock proof63 10 6 240 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p246 : testBlock proof63 10 6 246 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p252 : testBlock proof63 10 6 252 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p258 : testBlock proof63 10 6 258 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p264 : testBlock proof63 10 6 264 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p270 : testBlock proof63 10 6 270 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p276 : testBlock proof63 10 6 276 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p282 : testBlock proof63 10 6 282 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p288 : testBlock proof63 10 6 288 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p294 : testBlock proof63 10 6 294 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p300 : testBlock proof63 10 6 300 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p306 : testBlock proof63 10 6 306 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p312 : testBlock proof63 10 6 312 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p318 : testBlock proof63 10 6 318 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p324 : testBlock proof63 10 6 324 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p330 : testBlock proof63 10 6 330 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p336 : testBlock proof63 10 6 336 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p342 : testBlock proof63 10 6 342 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p348 : testBlock proof63 10 6 348 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p354 : testBlock proof63 10 6 354 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p360 : testBlock proof63 10 6 360 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p366 : testBlock proof63 10 6 366 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p372 : testBlock proof63 10 6 372 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p378 : testBlock proof63 10 6 378 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p384 : testBlock proof63 10 6 384 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p390 : testBlock proof63 10 6 390 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p396 : testBlock proof63 10 6 396 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p402 : testBlock proof63 10 6 402 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p408 : testBlock proof63 10 6 408 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p414 : testBlock proof63 10 6 414 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p420 : testBlock proof63 10 6 420 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p426 : testBlock proof63 10 6 426 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p432 : testBlock proof63 10 6 432 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p438 : testBlock proof63 10 6 438 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p444 : testBlock proof63 10 6 444 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p450 : testBlock proof63 10 6 450 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p456 : testBlock proof63 10 6 456 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p462 : testBlock proof63 10 6 462 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p468 : testBlock proof63 10 6 468 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p474 : testBlock proof63 10 6 474 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p480 : testBlock proof63 10 6 480 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p486 : testBlock proof63 10 6 486 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p492 : testBlock proof63 10 6 492 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p498 : testBlock proof63 10 6 498 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p504 : testBlock proof63 10 6 504 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p510 : testBlock proof63 10 6 510 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p516 : testBlock proof63 10 6 516 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p522 : testBlock proof63 10 6 522 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p528 : testBlock proof63 10 6 528 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p534 : testBlock proof63 10 6 534 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p540 : testBlock proof63 10 6 540 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6p546 : testBlock proof63 10 6 546 3 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r0n12 : testBlock proof63 10 6 0 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 0) (a := 6) (b := 6) check63l6p0 check63l6p6

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r12n12 : testBlock proof63 10 6 12 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 12) (a := 6) (b := 6) check63l6p12 check63l6p18

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r24n12 : testBlock proof63 10 6 24 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 24) (a := 6) (b := 6) check63l6p24 check63l6p30

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r36n12 : testBlock proof63 10 6 36 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 36) (a := 6) (b := 6) check63l6p36 check63l6p42

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r48n12 : testBlock proof63 10 6 48 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 48) (a := 6) (b := 6) check63l6p48 check63l6p54

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r60n12 : testBlock proof63 10 6 60 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 60) (a := 6) (b := 6) check63l6p60 check63l6p66

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r72n12 : testBlock proof63 10 6 72 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 72) (a := 6) (b := 6) check63l6p72 check63l6p78

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r84n12 : testBlock proof63 10 6 84 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 84) (a := 6) (b := 6) check63l6p84 check63l6p90

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r96n12 : testBlock proof63 10 6 96 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 96) (a := 6) (b := 6) check63l6p96 check63l6p102

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r108n12 : testBlock proof63 10 6 108 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 108) (a := 6) (b := 6) check63l6p108 check63l6p114

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r120n12 : testBlock proof63 10 6 120 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 120) (a := 6) (b := 6) check63l6p120 check63l6p126

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r132n12 : testBlock proof63 10 6 132 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 132) (a := 6) (b := 6) check63l6p132 check63l6p138

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r144n12 : testBlock proof63 10 6 144 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 144) (a := 6) (b := 6) check63l6p144 check63l6p150

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r156n12 : testBlock proof63 10 6 156 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 156) (a := 6) (b := 6) check63l6p156 check63l6p162

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r168n12 : testBlock proof63 10 6 168 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 168) (a := 6) (b := 6) check63l6p168 check63l6p174

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r180n12 : testBlock proof63 10 6 180 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 180) (a := 6) (b := 6) check63l6p180 check63l6p186

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r192n12 : testBlock proof63 10 6 192 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 192) (a := 6) (b := 6) check63l6p192 check63l6p198

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r204n12 : testBlock proof63 10 6 204 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 204) (a := 6) (b := 6) check63l6p204 check63l6p210

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r216n12 : testBlock proof63 10 6 216 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 216) (a := 6) (b := 6) check63l6p216 check63l6p222

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r228n12 : testBlock proof63 10 6 228 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 228) (a := 6) (b := 6) check63l6p228 check63l6p234

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r240n12 : testBlock proof63 10 6 240 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 240) (a := 6) (b := 6) check63l6p240 check63l6p246

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r252n12 : testBlock proof63 10 6 252 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 252) (a := 6) (b := 6) check63l6p252 check63l6p258

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r264n12 : testBlock proof63 10 6 264 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 264) (a := 6) (b := 6) check63l6p264 check63l6p270

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r276n12 : testBlock proof63 10 6 276 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 276) (a := 6) (b := 6) check63l6p276 check63l6p282

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r288n12 : testBlock proof63 10 6 288 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 288) (a := 6) (b := 6) check63l6p288 check63l6p294

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r300n12 : testBlock proof63 10 6 300 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 300) (a := 6) (b := 6) check63l6p300 check63l6p306

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r312n12 : testBlock proof63 10 6 312 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 312) (a := 6) (b := 6) check63l6p312 check63l6p318

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r324n12 : testBlock proof63 10 6 324 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 324) (a := 6) (b := 6) check63l6p324 check63l6p330

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r336n12 : testBlock proof63 10 6 336 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 336) (a := 6) (b := 6) check63l6p336 check63l6p342

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r348n12 : testBlock proof63 10 6 348 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 348) (a := 6) (b := 6) check63l6p348 check63l6p354

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r360n12 : testBlock proof63 10 6 360 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 360) (a := 6) (b := 6) check63l6p360 check63l6p366

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r372n12 : testBlock proof63 10 6 372 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 372) (a := 6) (b := 6) check63l6p372 check63l6p378

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r384n12 : testBlock proof63 10 6 384 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 384) (a := 6) (b := 6) check63l6p384 check63l6p390

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r396n12 : testBlock proof63 10 6 396 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 396) (a := 6) (b := 6) check63l6p396 check63l6p402

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r408n12 : testBlock proof63 10 6 408 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 408) (a := 6) (b := 6) check63l6p408 check63l6p414

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r420n12 : testBlock proof63 10 6 420 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 420) (a := 6) (b := 6) check63l6p420 check63l6p426

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r432n12 : testBlock proof63 10 6 432 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 432) (a := 6) (b := 6) check63l6p432 check63l6p438

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r444n12 : testBlock proof63 10 6 444 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 444) (a := 6) (b := 6) check63l6p444 check63l6p450

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r456n12 : testBlock proof63 10 6 456 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 456) (a := 6) (b := 6) check63l6p456 check63l6p462

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r468n12 : testBlock proof63 10 6 468 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 468) (a := 6) (b := 6) check63l6p468 check63l6p474

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r480n12 : testBlock proof63 10 6 480 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 480) (a := 6) (b := 6) check63l6p480 check63l6p486

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r492n12 : testBlock proof63 10 6 492 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 492) (a := 6) (b := 6) check63l6p492 check63l6p498

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r504n12 : testBlock proof63 10 6 504 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 504) (a := 6) (b := 6) check63l6p504 check63l6p510

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r516n12 : testBlock proof63 10 6 516 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 516) (a := 6) (b := 6) check63l6p516 check63l6p522

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r528n12 : testBlock proof63 10 6 528 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 528) (a := 6) (b := 6) check63l6p528 check63l6p534

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r540n9 : testBlock proof63 10 6 540 9 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 540) (a := 6) (b := 3) check63l6p540 check63l6p546

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r0n24 : testBlock proof63 10 6 0 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 0) (a := 12) (b := 12) check63l6r0n12 check63l6r12n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r24n24 : testBlock proof63 10 6 24 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 24) (a := 12) (b := 12) check63l6r24n12 check63l6r36n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r48n24 : testBlock proof63 10 6 48 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 48) (a := 12) (b := 12) check63l6r48n12 check63l6r60n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r72n24 : testBlock proof63 10 6 72 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 72) (a := 12) (b := 12) check63l6r72n12 check63l6r84n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r96n24 : testBlock proof63 10 6 96 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 96) (a := 12) (b := 12) check63l6r96n12 check63l6r108n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r120n24 : testBlock proof63 10 6 120 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 120) (a := 12) (b := 12) check63l6r120n12 check63l6r132n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r144n24 : testBlock proof63 10 6 144 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 144) (a := 12) (b := 12) check63l6r144n12 check63l6r156n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r168n24 : testBlock proof63 10 6 168 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 168) (a := 12) (b := 12) check63l6r168n12 check63l6r180n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r192n24 : testBlock proof63 10 6 192 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 192) (a := 12) (b := 12) check63l6r192n12 check63l6r204n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r216n24 : testBlock proof63 10 6 216 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 216) (a := 12) (b := 12) check63l6r216n12 check63l6r228n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r240n24 : testBlock proof63 10 6 240 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 240) (a := 12) (b := 12) check63l6r240n12 check63l6r252n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r264n24 : testBlock proof63 10 6 264 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 264) (a := 12) (b := 12) check63l6r264n12 check63l6r276n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r288n24 : testBlock proof63 10 6 288 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 288) (a := 12) (b := 12) check63l6r288n12 check63l6r300n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r312n24 : testBlock proof63 10 6 312 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 312) (a := 12) (b := 12) check63l6r312n12 check63l6r324n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r336n24 : testBlock proof63 10 6 336 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 336) (a := 12) (b := 12) check63l6r336n12 check63l6r348n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r360n24 : testBlock proof63 10 6 360 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 360) (a := 12) (b := 12) check63l6r360n12 check63l6r372n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r384n24 : testBlock proof63 10 6 384 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 384) (a := 12) (b := 12) check63l6r384n12 check63l6r396n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r408n24 : testBlock proof63 10 6 408 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 408) (a := 12) (b := 12) check63l6r408n12 check63l6r420n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r432n24 : testBlock proof63 10 6 432 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 432) (a := 12) (b := 12) check63l6r432n12 check63l6r444n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r456n24 : testBlock proof63 10 6 456 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 456) (a := 12) (b := 12) check63l6r456n12 check63l6r468n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r480n24 : testBlock proof63 10 6 480 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 480) (a := 12) (b := 12) check63l6r480n12 check63l6r492n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r504n24 : testBlock proof63 10 6 504 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 504) (a := 12) (b := 12) check63l6r504n12 check63l6r516n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r528n21 : testBlock proof63 10 6 528 21 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 528) (a := 12) (b := 9) check63l6r528n12 check63l6r540n9

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r0n48 : testBlock proof63 10 6 0 48 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 0) (a := 24) (b := 24) check63l6r0n24 check63l6r24n24

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r48n48 : testBlock proof63 10 6 48 48 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 48) (a := 24) (b := 24) check63l6r48n24 check63l6r72n24

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r96n48 : testBlock proof63 10 6 96 48 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 96) (a := 24) (b := 24) check63l6r96n24 check63l6r120n24

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r144n48 : testBlock proof63 10 6 144 48 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 144) (a := 24) (b := 24) check63l6r144n24 check63l6r168n24

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r192n48 : testBlock proof63 10 6 192 48 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 192) (a := 24) (b := 24) check63l6r192n24 check63l6r216n24

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r240n48 : testBlock proof63 10 6 240 48 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 240) (a := 24) (b := 24) check63l6r240n24 check63l6r264n24

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r288n48 : testBlock proof63 10 6 288 48 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 288) (a := 24) (b := 24) check63l6r288n24 check63l6r312n24

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r336n48 : testBlock proof63 10 6 336 48 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 336) (a := 24) (b := 24) check63l6r336n24 check63l6r360n24

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r384n48 : testBlock proof63 10 6 384 48 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 384) (a := 24) (b := 24) check63l6r384n24 check63l6r408n24

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r432n48 : testBlock proof63 10 6 432 48 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 432) (a := 24) (b := 24) check63l6r432n24 check63l6r456n24

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r480n48 : testBlock proof63 10 6 480 48 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 480) (a := 24) (b := 24) check63l6r480n24 check63l6r504n24

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r0n96 : testBlock proof63 10 6 0 96 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 0) (a := 48) (b := 48) check63l6r0n48 check63l6r48n48

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r96n96 : testBlock proof63 10 6 96 96 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 96) (a := 48) (b := 48) check63l6r96n48 check63l6r144n48

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r192n96 : testBlock proof63 10 6 192 96 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 192) (a := 48) (b := 48) check63l6r192n48 check63l6r240n48

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r288n96 : testBlock proof63 10 6 288 96 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 288) (a := 48) (b := 48) check63l6r288n48 check63l6r336n48

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r384n96 : testBlock proof63 10 6 384 96 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 384) (a := 48) (b := 48) check63l6r384n48 check63l6r432n48

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r480n69 : testBlock proof63 10 6 480 69 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 480) (a := 48) (b := 21) check63l6r480n48 check63l6r528n21

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r0n192 : testBlock proof63 10 6 0 192 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 0) (a := 96) (b := 96) check63l6r0n96 check63l6r96n96

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r192n192 : testBlock proof63 10 6 192 192 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 192) (a := 96) (b := 96) check63l6r192n96 check63l6r288n96

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r384n165 : testBlock proof63 10 6 384 165 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 384) (a := 96) (b := 69) check63l6r384n96 check63l6r480n69

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r0n384 : testBlock proof63 10 6 0 384 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 0) (a := 192) (b := 192) check63l6r0n192 check63l6r192n192

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l6r0n549 : testBlock proof63 10 6 0 549 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 0) (a := 384) (b := 165) check63l6r0n384 check63l6r384n165

theorem layer63k6 : testBlock proof63 10 6 0 549 (graphGoal 63) raw63 cuts63 = true :=
  check63l6r0n549

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p0 : testBlock proof63 10 7 0 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p6 : testBlock proof63 10 7 6 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p12 : testBlock proof63 10 7 12 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p18 : testBlock proof63 10 7 18 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p24 : testBlock proof63 10 7 24 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p30 : testBlock proof63 10 7 30 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p36 : testBlock proof63 10 7 36 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p42 : testBlock proof63 10 7 42 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p48 : testBlock proof63 10 7 48 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p54 : testBlock proof63 10 7 54 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p60 : testBlock proof63 10 7 60 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p66 : testBlock proof63 10 7 66 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p72 : testBlock proof63 10 7 72 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p78 : testBlock proof63 10 7 78 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p84 : testBlock proof63 10 7 84 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p90 : testBlock proof63 10 7 90 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p96 : testBlock proof63 10 7 96 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p102 : testBlock proof63 10 7 102 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p108 : testBlock proof63 10 7 108 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p114 : testBlock proof63 10 7 114 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p120 : testBlock proof63 10 7 120 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p126 : testBlock proof63 10 7 126 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p132 : testBlock proof63 10 7 132 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p138 : testBlock proof63 10 7 138 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p144 : testBlock proof63 10 7 144 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p150 : testBlock proof63 10 7 150 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p156 : testBlock proof63 10 7 156 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p162 : testBlock proof63 10 7 162 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p168 : testBlock proof63 10 7 168 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p174 : testBlock proof63 10 7 174 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p180 : testBlock proof63 10 7 180 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p186 : testBlock proof63 10 7 186 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p192 : testBlock proof63 10 7 192 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p198 : testBlock proof63 10 7 198 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p204 : testBlock proof63 10 7 204 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p210 : testBlock proof63 10 7 210 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p216 : testBlock proof63 10 7 216 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p222 : testBlock proof63 10 7 222 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p228 : testBlock proof63 10 7 228 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p234 : testBlock proof63 10 7 234 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p240 : testBlock proof63 10 7 240 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p246 : testBlock proof63 10 7 246 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p252 : testBlock proof63 10 7 252 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p258 : testBlock proof63 10 7 258 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p264 : testBlock proof63 10 7 264 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p270 : testBlock proof63 10 7 270 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p276 : testBlock proof63 10 7 276 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p282 : testBlock proof63 10 7 282 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p288 : testBlock proof63 10 7 288 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p294 : testBlock proof63 10 7 294 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p300 : testBlock proof63 10 7 300 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p306 : testBlock proof63 10 7 306 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7p312 : testBlock proof63 10 7 312 4 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r0n12 : testBlock proof63 10 7 0 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 0) (a := 6) (b := 6) check63l7p0 check63l7p6

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r12n12 : testBlock proof63 10 7 12 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 12) (a := 6) (b := 6) check63l7p12 check63l7p18

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r24n12 : testBlock proof63 10 7 24 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 24) (a := 6) (b := 6) check63l7p24 check63l7p30

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r36n12 : testBlock proof63 10 7 36 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 36) (a := 6) (b := 6) check63l7p36 check63l7p42

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r48n12 : testBlock proof63 10 7 48 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 48) (a := 6) (b := 6) check63l7p48 check63l7p54

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r60n12 : testBlock proof63 10 7 60 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 60) (a := 6) (b := 6) check63l7p60 check63l7p66

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r72n12 : testBlock proof63 10 7 72 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 72) (a := 6) (b := 6) check63l7p72 check63l7p78

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r84n12 : testBlock proof63 10 7 84 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 84) (a := 6) (b := 6) check63l7p84 check63l7p90

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r96n12 : testBlock proof63 10 7 96 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 96) (a := 6) (b := 6) check63l7p96 check63l7p102

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r108n12 : testBlock proof63 10 7 108 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 108) (a := 6) (b := 6) check63l7p108 check63l7p114

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r120n12 : testBlock proof63 10 7 120 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 120) (a := 6) (b := 6) check63l7p120 check63l7p126

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r132n12 : testBlock proof63 10 7 132 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 132) (a := 6) (b := 6) check63l7p132 check63l7p138

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r144n12 : testBlock proof63 10 7 144 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 144) (a := 6) (b := 6) check63l7p144 check63l7p150

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r156n12 : testBlock proof63 10 7 156 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 156) (a := 6) (b := 6) check63l7p156 check63l7p162

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r168n12 : testBlock proof63 10 7 168 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 168) (a := 6) (b := 6) check63l7p168 check63l7p174

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r180n12 : testBlock proof63 10 7 180 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 180) (a := 6) (b := 6) check63l7p180 check63l7p186

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r192n12 : testBlock proof63 10 7 192 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 192) (a := 6) (b := 6) check63l7p192 check63l7p198

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r204n12 : testBlock proof63 10 7 204 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 204) (a := 6) (b := 6) check63l7p204 check63l7p210

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r216n12 : testBlock proof63 10 7 216 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 216) (a := 6) (b := 6) check63l7p216 check63l7p222

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r228n12 : testBlock proof63 10 7 228 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 228) (a := 6) (b := 6) check63l7p228 check63l7p234

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r240n12 : testBlock proof63 10 7 240 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 240) (a := 6) (b := 6) check63l7p240 check63l7p246

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r252n12 : testBlock proof63 10 7 252 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 252) (a := 6) (b := 6) check63l7p252 check63l7p258

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r264n12 : testBlock proof63 10 7 264 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 264) (a := 6) (b := 6) check63l7p264 check63l7p270

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r276n12 : testBlock proof63 10 7 276 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 276) (a := 6) (b := 6) check63l7p276 check63l7p282

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r288n12 : testBlock proof63 10 7 288 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 288) (a := 6) (b := 6) check63l7p288 check63l7p294

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r300n12 : testBlock proof63 10 7 300 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 300) (a := 6) (b := 6) check63l7p300 check63l7p306

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r0n24 : testBlock proof63 10 7 0 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 0) (a := 12) (b := 12) check63l7r0n12 check63l7r12n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r24n24 : testBlock proof63 10 7 24 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 24) (a := 12) (b := 12) check63l7r24n12 check63l7r36n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r48n24 : testBlock proof63 10 7 48 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 48) (a := 12) (b := 12) check63l7r48n12 check63l7r60n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r72n24 : testBlock proof63 10 7 72 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 72) (a := 12) (b := 12) check63l7r72n12 check63l7r84n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r96n24 : testBlock proof63 10 7 96 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 96) (a := 12) (b := 12) check63l7r96n12 check63l7r108n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r120n24 : testBlock proof63 10 7 120 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 120) (a := 12) (b := 12) check63l7r120n12 check63l7r132n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r144n24 : testBlock proof63 10 7 144 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 144) (a := 12) (b := 12) check63l7r144n12 check63l7r156n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r168n24 : testBlock proof63 10 7 168 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 168) (a := 12) (b := 12) check63l7r168n12 check63l7r180n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r192n24 : testBlock proof63 10 7 192 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 192) (a := 12) (b := 12) check63l7r192n12 check63l7r204n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r216n24 : testBlock proof63 10 7 216 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 216) (a := 12) (b := 12) check63l7r216n12 check63l7r228n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r240n24 : testBlock proof63 10 7 240 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 240) (a := 12) (b := 12) check63l7r240n12 check63l7r252n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r264n24 : testBlock proof63 10 7 264 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 264) (a := 12) (b := 12) check63l7r264n12 check63l7r276n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r288n24 : testBlock proof63 10 7 288 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 288) (a := 12) (b := 12) check63l7r288n12 check63l7r300n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r0n48 : testBlock proof63 10 7 0 48 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 0) (a := 24) (b := 24) check63l7r0n24 check63l7r24n24

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r48n48 : testBlock proof63 10 7 48 48 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 48) (a := 24) (b := 24) check63l7r48n24 check63l7r72n24

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r96n48 : testBlock proof63 10 7 96 48 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 96) (a := 24) (b := 24) check63l7r96n24 check63l7r120n24

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r144n48 : testBlock proof63 10 7 144 48 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 144) (a := 24) (b := 24) check63l7r144n24 check63l7r168n24

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r192n48 : testBlock proof63 10 7 192 48 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 192) (a := 24) (b := 24) check63l7r192n24 check63l7r216n24

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r240n48 : testBlock proof63 10 7 240 48 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 240) (a := 24) (b := 24) check63l7r240n24 check63l7r264n24

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r288n28 : testBlock proof63 10 7 288 28 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 288) (a := 24) (b := 4) check63l7r288n24 check63l7p312

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r0n96 : testBlock proof63 10 7 0 96 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 0) (a := 48) (b := 48) check63l7r0n48 check63l7r48n48

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r96n96 : testBlock proof63 10 7 96 96 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 96) (a := 48) (b := 48) check63l7r96n48 check63l7r144n48

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r192n96 : testBlock proof63 10 7 192 96 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 192) (a := 48) (b := 48) check63l7r192n48 check63l7r240n48

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r0n192 : testBlock proof63 10 7 0 192 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 0) (a := 96) (b := 96) check63l7r0n96 check63l7r96n96

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r192n124 : testBlock proof63 10 7 192 124 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 192) (a := 96) (b := 28) check63l7r192n96 check63l7r288n28

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l7r0n316 : testBlock proof63 10 7 0 316 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 0) (a := 192) (b := 124) check63l7r0n192 check63l7r192n124

theorem layer63k7 : testBlock proof63 10 7 0 316 (graphGoal 63) raw63 cuts63 = true :=
  check63l7r0n316

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l8p0 : testBlock proof63 10 8 0 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l8p6 : testBlock proof63 10 8 6 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l8p12 : testBlock proof63 10 8 12 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l8p18 : testBlock proof63 10 8 18 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l8p24 : testBlock proof63 10 8 24 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l8p30 : testBlock proof63 10 8 30 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l8p36 : testBlock proof63 10 8 36 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l8p42 : testBlock proof63 10 8 42 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l8p48 : testBlock proof63 10 8 48 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l8p54 : testBlock proof63 10 8 54 1 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l8r0n12 : testBlock proof63 10 8 0 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 0) (a := 6) (b := 6) check63l8p0 check63l8p6

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l8r12n12 : testBlock proof63 10 8 12 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 12) (a := 6) (b := 6) check63l8p12 check63l8p18

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l8r24n12 : testBlock proof63 10 8 24 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 24) (a := 6) (b := 6) check63l8p24 check63l8p30

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l8r36n12 : testBlock proof63 10 8 36 12 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 36) (a := 6) (b := 6) check63l8p36 check63l8p42

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l8r48n7 : testBlock proof63 10 8 48 7 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 48) (a := 6) (b := 1) check63l8p48 check63l8p54

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l8r0n24 : testBlock proof63 10 8 0 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 0) (a := 12) (b := 12) check63l8r0n12 check63l8r12n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l8r24n24 : testBlock proof63 10 8 24 24 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 24) (a := 12) (b := 12) check63l8r24n12 check63l8r36n12

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l8r0n48 : testBlock proof63 10 8 0 48 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 0) (a := 24) (b := 24) check63l8r0n24 check63l8r24n24

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l8r0n55 : testBlock proof63 10 8 0 55 (graphGoal 63) raw63 cuts63 = true :=
  testBlock_join (start := 0) (a := 48) (b := 7) check63l8r0n48 check63l8r48n7

theorem layer63k8 : testBlock proof63 10 8 0 55 (graphGoal 63) raw63 cuts63 = true :=
  check63l8r0n55

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l9p0 : testBlock proof63 10 9 0 6 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

theorem layer63k9 : testBlock proof63 10 9 0 6 (graphGoal 63) raw63 cuts63 = true :=
  check63l9p0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem check63l10p0 : testBlock proof63 10 10 0 1 (graphGoal 63) raw63 cuts63 = true := by
  decide +kernel

theorem layer63k10 : testBlock proof63 10 10 0 1 (graphGoal 63) raw63 cuts63 = true :=
  check63l10p0

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables63 : ∀ k ≤ 10, ∀ i < proof63.count k,
    testNode proof63 10 k i (graphGoal 63) raw63 cuts63 = true := by
  intro k hk i hi
  interval_cases k
  · simp [Certificates.count, proof63, count63] at hi
  · simp [Certificates.count, proof63, count63] at hi
  · simp [Certificates.count, proof63, count63] at hi
  · simp [Certificates.count, proof63, count63] at hi
  · exact testBlock_at layer63k4 i (Nat.zero_le _) hi
  · exact testBlock_at layer63k5 i (Nat.zero_le _) hi
  · exact testBlock_at layer63k6 i (Nat.zero_le _) hi
  · exact testBlock_at layer63k7 i (Nat.zero_le _) hi
  · exact testBlock_at layer63k8 i (Nat.zero_le _) hi
  · exact testBlock_at layer63k9 i (Nat.zero_le _) hi
  · exact testBlock_at layer63k10 i (Nat.zero_le _) hi


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (vars 63) (graphGoal 63) 11 := by
  apply lower_impossible (by unfold proper; decide +kernel) (by decide +kernel)
    (by decide +kernel) (support_ok (by decide +kernel))
  have cutsOk : ∀ c ∈ cuts63, BankSound (graphGoal 63) c (vars 63) := by
    rw [cutsEq63]
    apply initialCuts_sound (hc := by decide +kernel)
    intro a ha
    simp only [bounds63, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact low47
    · exact low55
    · exact low59
    · exact low61
    · exact low62
    · exact low53
    · exact low31
    · exact low39
    · exact low43
    · exact low45
    · exact low46
    · exact low51
    · exact low54
    · exact low57
    · exact low58
    · exact low60
    · exact low21
    · exact low23
    · exact low29
    · exact low37
    · exact low42
    · exact low49
    · exact low52
    · exact low15
    · exact low27
    · exact low30
    · exact low35
    · exact low38
    · exact low41
    · exact low44
    · exact low50
    · exact low56
    · exact low5
    · exact low7
    · exact low10
    · exact low11
    · exact low13
    · exact low14
    · exact low17
    · exact low19
    · exact low20
    · exact low22
    · exact low25
    · exact low26
    · exact low28
    · exact low33
    · exact low34
    · exact low36
    · exact low40
    · exact low48
  have h := checked_tables mark63 sep63 cutsOk (by decide +kernel) tables63
  have hroot := h 10 (Nat.le_refl _) 0 (by decide +kernel)
  have eq : frontWords proof63 10 10 0 raw63 = vars 63 := by decide +kernel
  simpa only [eq] using hroot


-- The truth table places input 5 in coordinate 6. Fixing it to false gives mask 63.
theorem forbidShort : Impossible true graph 11 sevenInputs.toFinset := by
  have slice := build_slice (raw := 127) (m := 63) (by decide +kernel) low63
  have fit : poolCut true (domain 63) 11 11 0 (vars 127) (vars 127) = true := by
    decide +kernel
  have h := poolCut_sound slice [] rfl (by decide +kernel) fit
  have eq : (vars 127).toFinset = sevenInputs.toFinset := by decide +kernel
  rwa [eq] at h

end PEqualNP.Outside.L_meta_10648

theorem PEqualNP.Outside.L_meta_10648 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 2, 4, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact PEqualNP.Outside.L_meta_10648.replaceShort
    PEqualNP.Outside.L_meta_10648.forbidShort gates o fit correct
