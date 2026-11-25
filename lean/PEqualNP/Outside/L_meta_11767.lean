import PEqualNP.Defs

-- The live-set and restriction lemmas follow L-meta-10554, L-meta-10802, L-meta-1674, L-meta-670 and L-meta-1667.
namespace PEqualNP.Outside.L_meta_11767
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


-- Natural-number words, and a search table checked level by level.
def W (a : Nat) : Sig := BitVec.ofNat 128 a
def full : Nat := 0xffffffffffffffffffffffffffffffff
def xN : Nat → Nat
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000
  | _ => 0xffffffffffffffff0000000000000000
def nb (o a b : Nat) : Nat :=
  bif Nat.beq o 0 then Nat.land a b else bif Nat.beq o 1 then Nat.lor a b else
    bif Nat.beq o 2 then Nat.xor a (Nat.land a b) else Nat.xor b (Nat.land a b)
theorem bit_W (r : Row) (a : Nat) : bit r (W a) = a.testBit r.val := by
  unfold bit W
  rw [BitVec.getLsbD_ofNat]
  simp [r.isLt]
theorem tb_land (a b i : Nat) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) := Nat.testBit_and ..
theorem tb_lor (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) := Nat.testBit_or ..
theorem tb_xor (a b i : Nat) : (Nat.xor a b).testBit i = (a.testBit i ^^ b.testBit i) := Nat.testBit_xor ..
theorem nbeq {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h
theorem W_nb (o a b : Nat) : W (nb o a b) = bin o (W a) (W b) := by
  apply bit_ext
  intro r
  rw [bit_bin,bit_W,bit_W,bit_W]
  by_cases h0 : o = 0
  · subst h0
    exact tb_land a b _
  by_cases h1 : o = 1
  · subst h1
    exact tb_lor a b _
  by_cases h2 : o = 2
  · subst h2
    change (Nat.xor a (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
  · unfold nb
    rw [nbeq h0,nbeq h1,nbeq h2,if_neg h0,if_neg h1,if_neg h2]
    change (Nat.xor b (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
theorem bin_four (o : Nat) : ∃ e, e < 4 ∧ ∀ a b, bin o a b = bin e a b := by
  by_cases h : o < 4
  · exact ⟨o,h,fun _ _ => rfl⟩
  · refine ⟨3,by omega,fun a b => ?_⟩
    have h0 : o ≠ 0 := by omega
    have h1 : o ≠ 1 := by omega
    have h2 : o ≠ 2 := by omega
    simp [bin,h0,h1,h2]
theorem W_zero : W 0 = zero := rfl
theorem W_full : W full = one := by
  apply bit_ext
  intro r
  rw [bit_W,bit_one]
  revert r
  decide +kernel
theorem W_inj {a b : Nat} (ha : a < 2^128) (hb : b < 2^128) (h : W a = W b) : a = b := by
  have := congrArg BitVec.toNat h
  simpa only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using this

def rootsW (R : List Nat) : List Sig := R.map fun i => W (xN i)
def LowN (R : List Nat) (T L : Nat) : Prop := Lower true (rootsW R) (W T) L
abbrev SliceD := Nat × Nat × List Nat
def SliceN (R : List Nat) (T : Nat) (s : SliceD) : Prop :=
  Slice true (rootsW R) (W T) (W s.1) s.2.1 ∧ ∀ v ∈ s.2.2, v ∈ R

def baseOK (T : Nat) (R : List Nat) (E : List (Nat × Nat × Nat)) : Bool :=
  decide (T < 2^128) && !(T.testBit 0) && (E.map Prod.fst == R) && !R.isEmpty && decide (rootsW R).Nodup &&
  R.all (fun i => !((xN i).testBit 0)) &&
  E.all (fun e => decide (e.2.1 < 128) && decide (e.2.2 < 128) && (T.testBit e.2.1 != T.testBit e.2.2) &&
    R.all (fun i => i == e.1 || (xN i).testBit e.2.1 == (xN i).testBit e.2.2))

structure BaseP (T : Nat) (R : List Nat) : Prop where
  lt : T < 2^128
  plain : plainWord (W T) = true
  nodup : (rootsW R).Nodup
  plainR : (rootsW R).all plainWord = true
  ess : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a
  prop : proper (W T)

theorem baseOK_ok {T R E} (h : baseOK T R E = true) : BaseP T R := by
  simp only [baseOK,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hT,h0⟩,hE⟩,hne⟩,nd⟩,pr⟩,he⟩ := h
  have ess : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rw [←hE] at hi
    obtain ⟨e,hem,rfl⟩ := List.mem_map.mp hi
    obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := he e hem
    refine ⟨⟨e.2.1,h1⟩,⟨e.2.2,h2⟩,?_,?_⟩
    · rw [bit_W,bit_W]
      simpa using h3
    · intro v hv hne
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
      rw [bit_W,bit_W]
      have := h4 j hj
      simp only [Bool.or_eq_true,beq_iff_eq] at this
      rcases this with rfl | this
      · exact absurd rfl hne
      · exact this
  refine ⟨hT,?_,nd,?_,ess,?_⟩
  · have : bit 0 (W T) = false := (bit_W 0 T).trans h0
    simp [plainWord,this]
  · rw [List.all_eq_true]
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    have : bit 0 (W (xN i)) = false := (bit_W 0 _).trans (by simpa using pr i hi)
    simp [plainWord,this]
  · cases R with
    | nil => simp at hne
    | cons i R =>
      obtain ⟨r,s,hd,_⟩ := ess (W (xN i)) (by simp [rootsW])
      constructor
      · intro hh
        rw [hh,bit_zero,bit_zero] at hd
        exact hd rfl
      · intro hh
        rw [hh,bit_one,bit_one] at hd
        exact hd rfl

theorem lowOf {T R E K} (hB : baseOK T R E = true) (h : Impossible true (W T) K (rootsW R).toFinset) :
    LowN R T (K+1) := by
  have b := baseOK_ok hB
  exact lower_impossible b.prop b.plain b.plainR b.ess h
theorem lowCount {T R E K} (hB : baseOK T R E = true) (h : K + 2 ≤ R.length) : LowN R T (K+1) := by
  apply lowOf hB
  intro k hk run
  have b := baseOK_ok hB
  have := live_size run
  rw [List.toFinset_card_of_nodup b.nodup,rootsW,List.length_map] at this
  omega

def rowOf : List Nat → Nat → Nat → Nat
  | [],w,_ => w
  | v::vs,w,r => rowOf vs (w + ((r % 2) <<< v)) (r / 2)
def sliceChk (R : List Nat) (T : Nat) (R' : List Nat) (G d : Nat) (vs : List Nat) (w : Nat) : Bool :=
  vs.all (fun v => R.contains v) &&
  (List.range 128).all (fun r => let q := rowOf vs w r
    Nat.blt q 128 && d.testBit q && (T.testBit q == G.testBit r)) &&
  R.all (fun i => (List.range 128).all (fun r => !((xN i).testBit (rowOf vs w r))) ||
    (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r)) ||
    R'.any (fun j => (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r) == (xN j).testBit r)))

theorem mkSlice {R T E R' G E' d L vs w} (_hB : baseOK T R E = true) (hB' : baseOK G R' E' = true)
    (hL : LowN R' G L) (h : sliceChk R T R' G d vs w = true) : SliceN R T (d,L,vs) := by
  have b' := baseOK_ok hB'
  simp only [sliceChk,Bool.and_eq_true,List.all_eq_true,List.mem_range,Bool.or_eq_true,beq_iff_eq,
    Bool.not_eq_true',List.any_eq_true,Nat.blt_eq,List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨⟨hv,hr⟩,hR⟩ := h
  let f : Row → Row := fun r => ⟨rowOf vs w r.val,(hr r.val r.isLt).1.1⟩
  have fe (r : Row) (a : Nat) : bit (f r) (W a) = a.testBit (rowOf vs w r.val) := bit_W _ _
  have obs : restrictRows f (observe (W T)) = observe (W G) := by
    funext r
    change bit (f r) (W T) = bit r (W G)
    rw [fe,bit_W]
    exact (hr r.val r.isLt).2
  refine ⟨⟨f,rootsW R',?_,?_,?_,?_⟩,hv⟩
  · intro r
    rw [fe]
    exact (hr r.val r.isLt).1.2
  · intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rcases hR i hi with (h | h) | ⟨j,hj,h⟩
    · refine Or.inr (Or.inl ⟨false,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · refine Or.inr (Or.inl ⟨true,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · have e : restrictRows f (observe (W (xN i))) = observe (W (xN j)) := by
        funext r
        exact (fe r _).trans ((h r.val r.isLt).trans (bit_W r _).symm)
      rw [e]
      exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hj))
  · rw [obs]
    exact observe_proper b'.prop
  · rw [obs]
    exact hL

def av (d : Nat) (P : List Nat) (v : Nat) : Bool :=
  let m := Nat.land v d
  Nat.beq m 0 || Nat.beq m d || P.any (fun x => Nat.beq x m || Nat.beq x (Nat.xor d m))
def cn (d v : Nat) : Nat :=
  let m := Nat.land v d
  bif Nat.beq m 0 || Nat.beq m d then 1 else 0
def sumc (d : Nat) : List Nat → Nat
  | [] => 0
  | v::l => Nat.add (cn d v) (sumc d l)
def mkPool (P : List Nat) : List (Nat × Nat × Nat) → List Nat
  | [] => P
  | c::cs => mkPool (P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)]) cs
def initPool (d : Nat) (vs : List Nat) : List Nat := vs.map fun v => Nat.land (xN v) d

abbrev RF (f : Row → Row) (v : Nat) : Wire Row := restrictRows f (observe (W v))
def PS (f : Row → Row) (bank : List (Wire Row)) (P : List Nat) : Prop :=
  ∀ v ∈ P, Available true bank (RF f v)
theorem rf_apply (f : Row → Row) (v : Nat) (r : Row) : RF f v r = v.testBit (f r).val := bit_W _ _
theorem rf_land {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) :
    RF f (Nat.land v d) = RF f v := by
  funext r
  have h := dom r
  rw [bit_W] at h
  rw [rf_apply,rf_apply]
  have : (Nat.land v d).testBit (f r).val = (v.testBit (f r).val && d.testBit (f r).val) := Nat.testBit_and ..
  rw [this,h,Bool.and_true]
theorem rf_zero {f : Row → Row} : RF f 0 = fun _ => false := by
  funext r
  rw [rf_apply]
  exact Nat.zero_testBit _
theorem rf_dom {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) : RF f d = fun _ => true := by
  funext r
  exact dom r
theorem rf_xor {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (m : Nat) :
    RF f (Nat.xor d m) = inv (RF f m) := by
  funext r
  have h := dom r
  rw [bit_W] at h
  change RF f (Nat.xor d m) r = !(RF f m r)
  rw [rf_apply,rf_apply]
  have : (Nat.xor d m).testBit (f r).val = ((d.testBit (f r).val) ^^ (m.testBit (f r).val)) := Nat.testBit_xor ..
  rw [this,h,Bool.true_xor]
theorem cn_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) : cn d v ≤ cost (RF f v) := by
  change (bif (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d) then 1 else 0) ≤ _
  cases h : (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d)
  · exact Nat.zero_le _
  · have c : Constant (RF f v) := by
      rw [←rf_land dom v]
      rw [Bool.or_eq_true] at h
      rcases h with h | h
      · rw [Nat.eq_of_beq_eq_true h,rf_zero]
        exact ⟨false,rfl⟩
      · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
        exact ⟨true,rfl⟩
    rw [cost,if_pos c]
    exact Nat.le_refl 1
theorem av_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) {bank P v} (hP : PS f bank P)
    (h : av d P v = true) : Available true bank (RF f v) := by
  simp only [av,Bool.or_eq_true,List.any_eq_true] at h
  rw [←rf_land dom v]
  rcases h with (h | h) | ⟨x,hx,h | h⟩
  · rw [Nat.eq_of_beq_eq_true h,rf_zero]
    exact Or.inr (Or.inl ⟨false,rfl⟩)
  · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
    exact Or.inr (Or.inl ⟨true,rfl⟩)
  · rw [←Nat.eq_of_beq_eq_true h]
    exact hP x hx
  · have e := hP x hx
    rw [Nat.eq_of_beq_eq_true h,rf_xor dom] at e
    have e' := avail_inv rfl e
    rwa [inv_inv'] at e'
theorem rf_nb (f : Row → Row) (o a b : Nat) : RF f (nb o a b) = comb o (RF f a) (RF f b) := by
  unfold RF
  rw [W_nb,obs_bin,restrict_comb]
theorem pay_nb {f : Row → Row} {roots bank p P} (o a b : Nat) (hr : Reach true roots p bank) (hP : PS f bank P)
    (ha : Available true bank (RF f a)) (hb : Available true bank (RF f b)) :
    ∃ next, Reach true roots (p+1) next ∧ PS f next P ∧ Available true next (RF f (nb o a b)) ∧
      ∀ v, Available true bank v → Available true next v := by
  obtain ⟨e,he,heq⟩ := bin_four o
  have hn : RF f (nb o a b) = comb e (RF f a) (RF f b) := by
    unfold RF
    rw [W_nb,heq,obs_bin,restrict_comb]
  obtain ⟨op,x,y,e1,hx,hy,_,_⟩ := comb_prime (d:=e) (Or.inr ⟨rfl,he⟩) ha hb
  refine ⟨_,Reach.two op hr hx hy,fun v hv => available_cons _ (hP v hv),?_,fun v hv => available_cons _ hv⟩
  rw [hn,e1]
  exact Or.inl (by simp)
theorem getD_ps {f : Row → Row} {bank P} (hP : PS f bank P) (i : Nat) : Available true bank (RF f (P.getD i 0)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : P[i]? with
  | none => exact Or.inr (Or.inl ⟨false,rf_zero⟩)
  | some a => exact hP a (List.mem_of_getElem? h)
theorem mkPool_ok {f : Row → Row} {roots} (cs : List (Nat × Nat × Nat)) {bank p P} (hr : Reach true roots p bank)
    (hP : PS f bank P) : ∃ next, Reach true roots (p+cs.length) next ∧ PS f next (mkPool P cs) := by
  induction cs generalizing bank p P with
  | nil => exact ⟨bank,hr,hP⟩
  | cons c cs ih =>
    obtain ⟨next,h1,h2,h3,_⟩ := pay_nb c.1 _ _ hr hP (getD_ps hP c.2.1) (getD_ps hP c.2.2)
    have : PS f next (P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)]) := by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact h2 v hv
      · rw [List.mem_singleton.mp hv]
        exact h3
    obtain ⟨out,o1,o2⟩ := ih h1 this
    exact ⟨out,by rw [List.length_cons,show p+(cs.length+1) = p+1+cs.length by omega]; exact o1,o2⟩

abbrev CutV := Nat × Nat × Nat × List Nat
def keepB (d : Nat) (P : List Nat) (ka : Bool) (a : Nat) : Bool := bif ka then av d P a else true
def keepC (d : Nat) (ka : Bool) (a : Nat) : Nat := bif ka then cn d a else 0
def cutEval (k : Nat) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (c : CutV) : Bool :=
  rest.all (av c.1 c.2.2.2) && keepB c.1 c.2.2.2 ka a && keepB c.1 c.2.2.2 kb b &&
  (bif av c.1 c.2.2.2 z then
    Nat.blt (Nat.add k c.2.2.1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b))))
  else av c.1 c.2.2.2 a && av c.1 c.2.2.2 b &&
    Nat.blt (Nat.add (Nat.add k c.2.2.1) 1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b)))))
def sepEval (rest : List Nat) (a b z : Nat) (ka kb : Bool) (p : Nat × Nat) : Bool :=
  let e := fun v => (Nat.testBit v p.1 == Nat.testBit v p.2)
  e z && (!ka || e a) && (!kb || e b) && rest.all e
def sepOK (T : Nat) (p : Nat × Nat) : Bool := Nat.blt p.1 128 && Nat.blt p.2 128 && (T.testBit p.1 != T.testBit p.2)

def kidW (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Sig :=
  W z :: kept ka (W a) (kept kb (W b) (rest.map W))
theorem sumc_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (l : List Nat) :
    sumc d l ≤ mass (l.map (RF f)) := by
  induction l with
  | nil => simp [sumc]
  | cons v l ih =>
    rw [List.map_cons,mass_cons]
    exact Nat.add_le_add (cn_ok dom v) ih
theorem mass_keep {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (ka : Bool) (a : Nat) (l : List (Wire Row)) :
    keepC d ka a + mass l ≤ mass (kept ka (RF f a) l) := by
  cases ka
  · simp [keepC,kept]
  · rw [kept,if_pos rfl,mass_cons]
    exact Nat.add_le_add_right (cn_ok dom a) _
theorem kid_map (f : Row → Row) (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidW rest a b z ka kb).map observe).map (restrictRows f) =
      RF f z :: kept ka (RF f a) (kept kb (RF f b) (rest.map (RF f))) := by
  cases ka <;> cases kb <;> simp [kidW,kept,List.map_map,Function.comp_def,RF]

def CutP (R : List Nat) (T : Nat) (c : CutV) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)), (∀ r, bit (f r) (W c.1) = true) ∧
    ¬Constant (restrictRows f (observe (W T))) ∧ Reach true (roots.map observe) c.2.2.1 bank ∧ PS f bank c.2.2.2 ∧
    ∀ p bank, Reach true (roots.map observe) p bank → Available true bank (restrictRows f (observe (W T))) → c.2.1 ≤ p

theorem cut_sound {R T c k rest a b o ka kb} (hc : CutP R T c)
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : cutEval k rest a b (nb o a b) ka kb c = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  obtain ⟨f,roots,bank,dom,nc,hr,hP,lo⟩ := hc
  simp only [cutEval,Bool.and_eq_true,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have key : ∃ q bank', Reach true (roots.map observe) q bank' ∧ PS f bank' c.2.2.2 ∧ Available true bank' (RF f (nb o a b)) ∧
      k + q < c.2.1 + ((sumc c.1 rest + cn c.1 (nb o a b)) + (keepC c.1 ka a + keepC c.1 kb b)) := by
    cases hz : av c.1 c.2.2.2 (nb o a b)
    · rw [hz,cond_false,Bool.and_eq_true,Bool.and_eq_true,Nat.blt_eq] at h4
      obtain ⟨next,n1,n2,n3,_⟩ := pay_nb o a b hr hP (av_ok dom hP h4.1.1) (av_ok dom hP h4.1.2)
      refine ⟨_,next,n1,n2,n3,?_⟩
      have := h4.2
      exact this
    · rw [hz,cond_true,Nat.blt_eq] at h4
      exact ⟨_,bank,hr,hP,av_ok dom hP hz,h4⟩
  obtain ⟨q,bank',r1,r2,r3,r4⟩ := key
  intro k' hk run
  have supp : supply true bank' (((kidW rest a b (nb o a b) ka kb).map observe).map (restrictRows f)) := by
    rw [kid_map]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact r3
    have kb' : ∀ v ∈ kept kb (RF f b) (rest.map (RF f)), Available true bank' v := by
      intro v hv
      cases kb
      · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
        exact av_ok dom r2 (h1 x hx)
      · rcases List.mem_cons.mp hv with rfl | hv
        · exact av_ok dom r2 h3
        · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
          exact av_ok dom r2 (h1 x hx)
    cases ka
    · exact kb' v hv
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact av_ok dom r2 h2
      · exact kb' v hv
  have bound := projected_bound f (list_run run _ nd rfl) nc r1 supp lo
  rw [kid_map,mass_cons] at bound
  have m1 := mass_keep dom ka a (kept kb (RF f b) (rest.map (RF f)))
  have m2 := mass_keep dom kb b (rest.map (RF f))
  have m3 := sumc_ok dom rest
  have m4 := cn_ok dom (nb o a b)
  omega

theorem sep_sound {T k rest a b o ka kb p} (hT : sepOK T p = true)
    (h : sepEval rest a b (nb o a b) ka kb p = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  simp only [sepOK,Bool.and_eq_true,Nat.blt_eq,bne_iff_ne] at hT
  obtain ⟨⟨p1,p2⟩,hd⟩ := hT
  simp only [sepEval,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',beq_iff_eq,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  intro k' _ run
  obtain ⟨v,hv,hne⟩ := live_row_difference run (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W,bit_W]; exact hd)
  apply hne
  rw [List.mem_toFinset] at hv
  rcases List.mem_cons.mp hv with rfl | hv
  · rw [bit_W,bit_W]; exact h1
  rcases mem_kept hv with rfl | hv'
  · cases ka
    · cases kb
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        rw [←e,bit_W,bit_W]; exact h4 x hx
      · rcases List.mem_cons.mp hv with e | hv
        · rw [e,bit_W,bit_W]; exact h3.resolve_left (by simp)
        · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
          rw [←e,bit_W,bit_W]; exact h4 x hx
    · rw [bit_W,bit_W]; exact h2.resolve_left (by simp)
  · cases kb
    · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv'
      rw [←e,bit_W,bit_W]; exact h4 x hx
    · rcases List.mem_cons.mp hv' with e | hv
      · rw [e,bit_W,bit_W]; exact h3.resolve_left (by simp)
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        rw [←e,bit_W,bit_W]; exact h4 x hx

abbrev StD := List Nat × List (Nat × List (Nat × Nat × Nat)) × List (Nat × Nat) × List (List Nat)
def dupD (l : List StD) : List StD := l.map fun st => (st.1.map (Nat.mul 0x10000000000000001),st.2)
def picks : List Nat → List (Nat × List Nat)
  | [] => []
  | x::xs => (x,xs) :: (picks xs).map fun p => (p.1,x::p.2)
def pairs : List Nat → List (Nat × Nat × List Nat)
  | [] => []
  | x::xs => ((picks xs).map fun p => (x,p.1,p.2)) ++ (pairs xs).map fun p => (p.1,p.2.1,x::p.2.2)
theorem picks_ok {l : List Nat} {a : Nat} (h : a ∈ l) : ∃ p ∈ picks l, p.1 = a ∧ (a::p.2).Perm l := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨(a,xs),by simp [picks],rfl,List.Perm.refl _⟩
    · obtain ⟨p,hp,rfl,q⟩ := ih h
      refine ⟨(p.1,x::p.2),?_,rfl,?_⟩
      · simp only [picks,List.mem_cons,List.mem_map]
        exact Or.inr ⟨p,hp,rfl⟩
      · exact (List.Perm.swap x p.1 p.2).trans (q.cons x)
theorem pairs_ok {l : List Nat} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    ∃ p ∈ pairs l, (p.1::p.2.1::p.2.2).Perm l ∧ ((p.1 = a ∧ p.2.1 = b) ∨ (p.1 = b ∧ p.2.1 = a)) := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    have first (c : Nat) (hc : c ∈ xs) : ∃ p ∈ pairs (x::xs), (p.1::p.2.1::p.2.2).Perm (x::xs) ∧ p.1 = x ∧ p.2.1 = c := by
      obtain ⟨p,hp,rfl,q⟩ := picks_ok hc
      refine ⟨(x,p.1,p.2),?_,q.cons x,rfl,rfl⟩
      simp only [pairs,List.mem_append,List.mem_map]
      exact Or.inl ⟨p,hp,rfl⟩
    rcases List.mem_cons.mp ha with rfl | ha2
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact absurd rfl hab
      · obtain ⟨p,h1,h2,h3,h4⟩ := first b hb
        exact ⟨p,h1,h2,Or.inl ⟨h3,h4⟩⟩
    · rcases List.mem_cons.mp hb with e | hb
      · subst e
        obtain ⟨p,h1,h2,h3,h4⟩ := first a ha2
        exact ⟨p,h1,h2,Or.inr ⟨h3,h4⟩⟩
      · obtain ⟨p,hp,q,e⟩ := ih ha2 hb
        refine ⟨(p.1,p.2.1,x::p.2.2),?_,?_,e⟩
        · simp only [pairs,List.mem_append,List.mem_map]
          exact Or.inr ⟨p,hp,rfl⟩
        · exact ((List.Perm.swap x p.2.1 p.2.2).cons p.1).trans ((List.Perm.swap x p.1 _).trans (q.cons x))

def mem1 (z : Nat) (l : List Nat) : Bool := l.any fun x => Nat.beq x z
def beqL : List Nat → List Nat → Bool
  | [],[] => true
  | x::xs,y::ys => Nat.beq x y && beqL xs ys
  | _,_ => false
theorem beqL_ok {a b : List Nat} (h : beqL a b = true) : a = b := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons => simp [beqL] at h
  | cons x xs ih => cases b with
    | nil => simp [beqL] at h
    | cons y ys =>
      simp only [beqL,Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1,ih h.2]
def ins (z : Nat) : List Nat → List Nat
  | [] => [z]
  | x::xs => bif Nat.ble z x then z::x::xs else x :: ins z xs
theorem mem_ins {z v : Nat} {l : List Nat} : v ∈ ins z l ↔ v = z ∨ v ∈ l := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih =>
    unfold ins
    cases Nat.ble z x
    · simp only [cond_false,List.mem_cons,ih]
      tauto
    · simp
def kidN (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Nat :=
  ins z (bif ka then ins a (bif kb then ins b rest else rest) else bif kb then ins b rest else rest)
theorem kid_fin (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidN rest a b z ka kb).map W).toFinset = (kidW rest a b z ka kb).toFinset := by
  ext v
  cases ka <;> cases kb <;> simp [kidN,kidW,kept,mem_ins] <;> aesop

def keeps : List (Bool × Bool) := [(true,true),(true,false),(false,true),(false,false)]
def bl (b : Bool) : Nat := bif b then 1 else 0
def mkCut (Z : List SliceD) (c : Nat × List (Nat × Nat × Nat)) : CutV :=
  let s := Z.getD c.1 (0,0,[])
  (s.1,s.2.1,c.2.length,mkPool (initPool s.1 s.2.2) c.2)
def hintOK (k : Nat) (cuts : List CutV) (seps : List (Nat × Nat)) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (i : Nat) : Bool :=
  bif Nat.blt i 1000 then (match cuts[i]? with
    | some c => cutEval k rest a b z ka kb c
    | none => false)
  else (match seps[i-1000]? with
    | some q => sepEval rest a b z ka kb q
    | none => false)
def kidOK (k : Nat) (next : List (List Nat)) (cuts : List CutV) (seps : List (Nat × Nat)) (rest : List Nat) (hints : List Nat)
    (a b z : Nat) (kk : Bool × Bool) : Bool :=
  Nat.blt k (Nat.add (Nat.add rest.length (Nat.add (bl kk.1) (bl kk.2))) 0) ||
  hints.any (hintOK k cuts seps rest a b z kk.1 kk.2) ||
  next.any (beqL (kidN rest a b z kk.1 kk.2))
def pairOK (k : Nat) (next : List (List Nat)) (cuts : List CutV) (seps : List (Nat × Nat)) (s : List Nat)
    (p : Nat × Nat × List Nat) (hints : List Nat) : Bool :=
  [0,1,2,3].all fun o =>
    let z := nb o p.1 p.2.1
    mem1 z s || Nat.beq z 0 || Nat.beq z full ||
      keeps.all (kidOK k next cuts seps p.2.2 hints p.1 p.2.1 z)
def allZip (f : Nat × Nat × List Nat → List Nat → Bool) : List (Nat × Nat × List Nat) → List (List Nat) → Bool
  | [],_ => true
  | p::ps,[] => f p [] && allZip f ps []
  | p::ps,h::hs => f p h && allZip f ps hs
theorem allZip_ok {f ps hs} (h : allZip f ps hs = true) : ∀ p ∈ ps, ∃ x, f p x = true := by
  induction ps generalizing hs with
  | nil => intro p hp; cases hp
  | cons q ps ih =>
    intro p hp
    cases hs with
    | nil =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
    | cons x hs =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
def asc : List Nat → Bool
  | [] => true
  | [x] => Nat.blt x (2^128)
  | x::y::l => Nat.blt x y && asc (y::l)
theorem asc_ok {l : List Nat} (h : asc l = true) : l.Pairwise (· < ·) ∧ ∀ x ∈ l, x < 2^128 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    cases l with
    | nil =>
      simp only [asc,Nat.blt_eq] at h
      simpa using h
    | cons y l =>
      simp only [asc,Bool.and_eq_true,Nat.blt_eq] at h
      obtain ⟨i1,i2⟩ := ih h.2
      have hy := List.pairwise_cons.mp i1
      refine ⟨List.pairwise_cons.mpr ⟨?_,i1⟩,?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1
        · exact h.1.trans (hy.1 v hv)
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1.trans (i2 y (by simp))
        · exact i2 v hv
theorem asc_nodup {l : List Nat} (h : asc l = true) : l.Nodup ∧ (l.map W).Nodup := by
  obtain ⟨h1,h2⟩ := asc_ok h
  have nd : l.Nodup := h1.imp (fun h => Nat.ne_of_lt h)
  refine ⟨nd,?_⟩
  refine nd.map_on ?_
  intro x hx y hy e
  exact W_inj (h2 x hx) (h2 y hy) e
def stOK (T : Nat) (Z : List SliceD) (k : Nat) (next : List (List Nat)) (st : StD) : Bool :=
  asc st.1 && !(mem1 T st.1) && st.2.2.1.all (sepOK T) && st.2.1.all (fun c => Nat.blt c.1 Z.length) &&
  allZip (pairOK k next (st.2.1.map (mkCut Z)) st.2.2.1 st.1) (pairs st.1) st.2.2.2
def levelOK (T : Nat) (Z : List SliceD) (k : Nat) (next : List (List Nat)) (D : List StD) : Bool :=
  D.all (stOK T Z k next)
def LevelN (R : List Nat) (T k : Nat) (D : List StD) : Prop :=
  ∀ st ∈ D, Impossible true (W T) k (st.1.map W).toFinset

theorem stStep {R T E Z k next st} (hB : baseOK T R E = true) (hZ : ∀ s ∈ Z, SliceN R T s)
    (hn : ∀ s ∈ next, Impossible true (W T) k (s.map W).toFinset)
    (h : stOK T Z k next st = true) : Impossible true (W T) (k+1) (st.1.map W).toFinset := by
  have b := baseOK_ok hB
  simp only [stOK,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨⟨ha,hT⟩,hs⟩,hcut⟩,hz⟩ := h
  obtain ⟨nd,ndW⟩ := asc_nodup ha
  have lt := (asc_ok ha).2
  have hTm : W T ∉ st.1.map W := by
    intro hm
    obtain ⟨x,hx,e⟩ := List.mem_map.mp hm
    have := W_inj (lt x hx) b.lt e
    subst this
    have : mem1 x st.1 = true := List.any_eq_true.mpr ⟨x,hx,Nat.beq_refl x⟩
    rw [hT] at this
    exact Bool.noConfusion this
  have good : ∀ c ∈ st.2.1.map (mkCut Z), CutP R T c := by
    intro c hc
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
    have hi : q.1 < Z.length := by simpa only [Nat.blt_eq] using hcut q hq
    have hm : Z.getD q.1 (0,0,[]) ∈ Z := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
      exact List.getElem_mem hi
    obtain ⟨⟨f,roots,dom,base,nc,lo⟩,hv⟩ := hZ _ hm
    have ps : PS f (roots.map observe) (initPool (Z.getD q.1 (0,0,[])).1 (Z.getD q.1 (0,0,[])).2.2) := by
      intro v hv'
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv'
      rw [rf_land dom]
      exact base _ (List.mem_map_of_mem (hv j hj))
    obtain ⟨bank,b1,b2⟩ := mkPool_ok q.2 (Reach.start (u:=true) (roots:=roots.map observe)) ps
    refine ⟨f,roots,bank,dom,nc,?_,b2,lo⟩
    simpa [mkCut] using b1
  apply enum_step ndW hTm
  intro a' ha' b' hb' d hd ka kb hab fresh hprop hlen
  obtain ⟨a,ham,rfl⟩ := List.mem_map.mp ha'
  obtain ⟨c,hcm,rfl⟩ := List.mem_map.mp hb'
  have hac : a ≠ c := fun h => hab (by rw [h])
  have hd4 : d < 4 := by
    rcases hd with h | ⟨_,h⟩ <;> omega
  obtain ⟨p,hp,perm,ho⟩ := pairs_ok ham hcm hac
  obtain ⟨x,hx⟩ := allZip_ok hz p hp
  -- one unordered pair serves both orders
  have core : ∀ (o : Nat) (ja jb : Bool), o < 4 → W (nb o p.1 p.2.1) = bin d (W a) (W c) →
      (p.2.2.length + (bl ja + bl jb) ≤ k) →
      Impossible true (W T) k (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).toFinset := by
    intro o ja jb ho4 hW hl
    have hf := List.all_eq_true.mp hx o (by
      have : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by omega
      simpa using this)
    simp only [Bool.or_eq_true] at hf
    have pm (v : Nat) : v ∈ st.1 ↔ v = p.1 ∨ v = p.2.1 ∨ v ∈ p.2.2 := by
      rw [←perm.mem_iff]
      simp
    rcases hf with ((hf | hf) | hf) | hf
    · exfalso
      obtain ⟨y,hy,e⟩ := List.any_eq_true.mp hf
      apply fresh
      rw [←hW,←Nat.eq_of_beq_eq_true e]
      exact List.mem_map_of_mem hy
    · exfalso
      apply hprop.1
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      rfl
    · exfalso
      apply hprop.2
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      exact W_full
    have hk := List.all_eq_true.mp hf (ja,jb) (by cases ja <;> cases jb <;> simp [keeps])
    simp only [kidOK,Bool.or_eq_true] at hk
    have ndp : ((p.1::p.2.1::p.2.2).map W).Nodup := (perm.map W).nodup_iff.mpr ndW
    simp only [List.map_cons,List.nodup_cons,List.mem_cons,not_or] at ndp
    have nk : (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).Nodup := by
      have n1 := kept_nd jb (W p.2.1) _ ndp.2.2 ndp.2.1
      have n2 : W p.1 ∉ kept jb (W p.2.1) (p.2.2.map W) := by
        cases jb
        · exact ndp.1.2
        · simp only [kept,if_true,List.mem_cons,not_or]
          exact ndp.1
      refine List.nodup_cons.mpr ⟨?_,kept_nd ja _ _ n1 n2⟩
      intro hm
      apply fresh
      rw [←hW]
      have sub : W (nb o p.1 p.2.1) ∈ (p.1::p.2.1::p.2.2).map W := by
        rcases mem_kept hm with h | h
        · rw [h]; simp
        · rcases mem_kept h with h | h
          · rw [h]; simp
          · simp [h]
      exact (perm.map W).mem_iff.mp sub
    rcases hk with (hk | hk) | hk
    · exfalso
      rw [Nat.blt_eq] at hk
      have : k < p.2.2.length + (bl ja + bl jb) + 0 := hk
      omega
    · obtain ⟨i,_,hi⟩ := List.any_eq_true.mp hk
      unfold hintOK at hi
      cases hb : Nat.blt i 1000
      · rw [hb,cond_false] at hi
        cases hg : st.2.2.1[i-1000]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact sep_sound (hs q (List.mem_of_getElem? hg)) hi
      · rw [hb,cond_true] at hi
        cases hg : (st.2.1.map (mkCut Z))[i]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact cut_sound (good q (List.mem_of_getElem? hg)) nk hi
    · obtain ⟨s,hs',e⟩ := List.any_eq_true.mp hk
      rw [←kid_fin]
      rw [beqL_ok e]
      exact hn s hs'
  have rp : (((st.1.map W).erase (W a)).erase (W c)).Perm (p.2.2.map W) := by
    have e : (W a :: W c :: p.2.2.map W).Perm (st.1.map W) := by
      rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact perm.map W
      · exact (List.Perm.swap _ _ _).trans (perm.map W)
    have e1 := e.erase (W a)
    rw [List.erase_cons_head] at e1
    have e2 := e1.erase (W c)
    rw [List.erase_cons_head] at e2
    exact e2.symm
  have lenr : (((st.1.map W).erase (W a)).erase (W c)).length = p.2.2.length := by
    rw [rp.length_eq,List.length_map]
  have fits : p.2.2.length + (bl ka + bl kb) ≤ k := by
    have h := hlen
    unfold childTwo at h
    cases ka <;> cases kb <;> simp [kept,lenr] at h <;> simp [bl] <;> omega
  rw [Nat.add_sub_cancel]
  rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have r := core d ka kb hd4 (W_nb _ _ _) fits
    have e : (childTwo (st.1.map W) (W p.1) (W p.2.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb d p.1 p.2.1) ka kb).toFinset := by
      unfold childTwo kidW
      rw [W_nb]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff]
    rw [e]
    exact r
  · have hfl := flip_flip hd
    have f4 : flipOp d < 4 := by
      rcases hfl.1 with h | ⟨_,h⟩ <;> omega
    have r := core (flipOp d) kb ka f4 (by rw [W_nb]; exact (bin_flip hd _ _).symm) (by omega)
    have e : (childTwo (st.1.map W) (W p.2.1) (W p.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb (flipOp d) p.1 p.2.1) kb ka).toFinset := by
      unfold childTwo kidW
      rw [W_nb,bin_flip hd]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff] <;> tauto
    rw [e]
    exact r

theorem levelStep {R T E Z k D' D} (hB : baseOK T R E = true) (hZ : ∀ s ∈ Z, SliceN R T s)
    (hI : LevelN R T k D') (h : levelOK T Z k (D'.map Prod.fst) D = true) : LevelN R T (k+1) D := by
  intro st hst
  refine stStep hB hZ ?_ (List.all_eq_true.mp h st hst)
  intro s hs
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  exact hI q hq
theorem chunks {T : Nat} {Z : List SliceD} {k : Nat} {next : List (List Nat)} (c : Nat) (D : List StD) (n : Nat) (hc : 0 < c)
    (hl : Nat.ble D.length (n*c) = true)
    (h : ∀ i, i < n → levelOK T Z k next ((D.drop (i*c)).take c) = true) : levelOK T Z k next D = true := by
  rw [levelOK,List.all_eq_true]
  intro x hx
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hx
  have hl' := Nat.le_of_ble_eq_true hl
  have hi : j / c < n := by
    rw [Nat.div_lt_iff_lt_mul hc]
    omega
  refine List.all_eq_true.mp (h _ hi) _ ?_
  have hm : j / c * c + j % c = j := by rw [Nat.mul_comm]; exact Nat.div_add_mod j c
  have hmod := Nat.mod_lt j hc
  refine List.mem_of_getElem? (i := j % c) ?_
  rw [List.getElem?_take_of_lt hmod,List.getElem?_drop,hm]
  exact List.getElem?_eq_getElem hj
theorem lowSearch {R T E K D} (hB : baseOK T R E = true) (hI : LevelN R T K D)
    (h : (D.map Prod.fst).contains (R.map xN) = true) : LowN R T (K+1) := by
  apply lowOf hB
  simp only [List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨q,hq,e⟩ := List.mem_map.mp h
  have := hI q hq
  rw [e] at this
  simpa only [rootsW,List.map_map,Function.comp_def] using this


def target (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[
    ⟨.or, [1, 6]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.or, [0, 3]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.and, [0, 3]⟩,
    ⟨.and, [10, 5]⟩,
    ⟨.and, [11, 9]⟩,
    ⟨.and, [8, 7]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [16, 14]⟩,
    ⟨.or, [17, 15]⟩], 18⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 7 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 12 := rfl

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



def p2_8T : Nat := 0x88888888888888888888888888888888
def p2_8R : List Nat := [0, 1]
def p2_8E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3)]
theorem p2_8B : baseOK p2_8T p2_8R p2_8E = true := by decide +kernel
theorem p2_8L : LowN p2_8R p2_8T 1 := lowCount p2_8B (by decide +kernel)
def p2_eT : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def p2_eR : List Nat := [0, 1]
def p2_eE : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2)]
theorem p2_eB : baseOK p2_eT p2_eR p2_eE = true := by decide +kernel
theorem p2_eL : LowN p2_eR p2_eT 1 := lowCount p2_eB (by decide +kernel)
def p3_e8T : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def p3_e8R : List Nat := [0, 1, 2]
def p3_e8E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem p3_e8B : baseOK p3_e8T p3_e8R p3_e8E = true := by decide +kernel
theorem p3_e8S0 : SliceN p3_e8R p3_e8T (0x33333333333333333333333333333333,1,[0, 2]) := mkSlice (w:=0) p3_e8B p2_8B p2_8L (by decide +kernel)
theorem p3_e8S1 : SliceN p3_e8R p3_e8T (0x55555555555555555555555555555555,1,[1, 2]) := mkSlice (w:=0) p3_e8B p2_8B p2_8L (by decide +kernel)
theorem p3_e8S2 : SliceN p3_e8R p3_e8T (0xcccccccccccccccccccccccccccccccc,1,[0, 2]) := mkSlice (w:=2) p3_e8B p2_eB p2_eL (by decide +kernel)
theorem p3_e8S3 : SliceN p3_e8R p3_e8T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,1,[1, 2]) := mkSlice (w:=1) p3_e8B p2_eB p2_eL (by decide +kernel)
theorem p3_e8S4 : SliceN p3_e8R p3_e8T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,1,[0, 1]) := mkSlice (w:=0) p3_e8B p2_8B p2_8L (by decide +kernel)
theorem p3_e8S5 : SliceN p3_e8R p3_e8T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,1,[0, 1]) := mkSlice (w:=4) p3_e8B p2_eB p2_eL (by decide +kernel)
def p3_e8Z : List SliceD := [(0x33333333333333333333333333333333,1,[0, 2]),(0x55555555555555555555555555555555,1,[1, 2]),(0xcccccccccccccccccccccccccccccccc,1,[0, 2]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,1,[1, 2]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,1,[0, 1]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,1,[0, 1])]
theorem p3_e8Y : ∀ s ∈ p3_e8Z, SliceN p3_e8R p3_e8T s := by
  unfold p3_e8Z
  simp only [List.forall_mem_cons]
  exact ⟨p3_e8S0,p3_e8S1,p3_e8S2,p3_e8S3,p3_e8S4,p3_e8S5,by simp⟩
def p3_e8D3 : List StD := dupD [
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0],[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])],[(4,5),(1,3),(0,3),(2,3),(2,6),(1,5)],[[0,1,1000,2,3,1001,1002],[4,1,1003,5,3,1000],[4,0,1001,5,2,1004,1005]])]
def p3_e8D2 : List StD := []
theorem p3_e8I2 : LevelN p3_e8R p3_e8T 2 p3_e8D2 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p3_e8C3x0 : levelOK p3_e8T p3_e8Z 2 (p3_e8D2.map Prod.fst) ((p3_e8D3.drop (0*8)).take 8) = true := by decide +kernel
theorem p3_e8I3 : LevelN p3_e8R p3_e8T 3 p3_e8D3 := levelStep p3_e8B p3_e8Y p3_e8I2 (chunks 8 p3_e8D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p3_e8C3x0
  ))
theorem p3_e8L : LowN p3_e8R p3_e8T 4 := lowSearch p3_e8B p3_e8I3 (by decide +kernel)
def p3_eaT : Nat := 0xeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaea
def p3_eaR : List Nat := [0, 1, 2]
def p3_eaE : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6)]
theorem p3_eaB : baseOK p3_eaT p3_eaR p3_eaE = true := by decide +kernel
theorem p3_eaL : LowN p3_eaR p3_eaT 2 := lowCount p3_eaB (by decide +kernel)
def p3_a8T : Nat := 0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8
def p3_a8R : List Nat := [0, 1, 2]
def p3_a8E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem p3_a8B : baseOK p3_a8T p3_a8R p3_a8E = true := by decide +kernel
theorem p3_a8L : LowN p3_a8R p3_a8T 2 := lowCount p3_a8B (by decide +kernel)
def p4_eac8T : Nat := 0xeac8eac8eac8eac8eac8eac8eac8eac8
def p4_eac8R : List Nat := [0, 1, 2, 3]
def p4_eac8E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9)]
theorem p4_eac8B : baseOK p4_eac8T p4_eac8R p4_eac8E = true := by decide +kernel
theorem p4_eac8S0 : SliceN p4_eac8R p4_eac8T (0x3030303030303030303030303030303,1,[0, 3]) := mkSlice (w:=0) p4_eac8B p2_8B p2_8L (by decide +kernel)
theorem p4_eac8S1 : SliceN p4_eac8R p4_eac8T (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,1,[1, 3]) := mkSlice (w:=1) p4_eac8B p2_eB p2_eL (by decide +kernel)
theorem p4_eac8S2 : SliceN p4_eac8R p4_eac8T (0x550055005500550055005500550055,1,[1, 2]) := mkSlice (w:=0) p4_eac8B p2_8B p2_8L (by decide +kernel)
theorem p4_eac8S3 : SliceN p4_eac8R p4_eac8T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,2,[1, 0, 3]) := mkSlice (w:=4) p4_eac8B p3_eaB p3_eaL (by decide +kernel)
theorem p4_eac8S4 : SliceN p4_eac8R p4_eac8T (0xff00ff00ff00ff00ff00ff00ff00ff,2,[1, 0, 2]) := mkSlice (w:=0) p4_eac8B p3_a8B p3_a8L (by decide +kernel)
theorem p4_eac8S5 : SliceN p4_eac8R p4_eac8T (0xff00ff00ff00ff00ff00ff00ff00ff00,2,[0, 1, 2]) := mkSlice (w:=8) p4_eac8B p3_eaB p3_eaL (by decide +kernel)
def p4_eac8Z : List SliceD := [(0x3030303030303030303030303030303,1,[0, 3]),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,1,[1, 3]),(0x550055005500550055005500550055,1,[1, 2]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,2,[1, 0, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff,2,[1, 0, 2]),(0xff00ff00ff00ff00ff00ff00ff00ff00,2,[0, 1, 2])]
theorem p4_eac8Y : ∀ s ∈ p4_eac8Z, SliceN p4_eac8R p4_eac8T s := by
  unfold p4_eac8Z
  simp only [List.forall_mem_cons]
  exact ⟨p4_eac8S0,p4_eac8S1,p4_eac8S2,p4_eac8S3,p4_eac8S4,p4_eac8S5,by simp⟩
def p4_eac8D3 : List StD := dupD [
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00],[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])],[],[[0,1,2],[0,3],[4,1,5],[1,3],[0,5,2],[0,3]])]
def p4_eac8D2 : List StD := []
theorem p4_eac8I2 : LevelN p4_eac8R p4_eac8T 2 p4_eac8D2 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4_eac8C3x0 : levelOK p4_eac8T p4_eac8Z 2 (p4_eac8D2.map Prod.fst) ((p4_eac8D3.drop (0*8)).take 8) = true := by decide +kernel
theorem p4_eac8I3 : LevelN p4_eac8R p4_eac8T 3 p4_eac8D3 := levelStep p4_eac8B p4_eac8Y p4_eac8I2 (chunks 8 p4_eac8D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p4_eac8C3x0
  ))
theorem p4_eac8L : LowN p4_eac8R p4_eac8T 4 := lowSearch p4_eac8B p4_eac8I3 (by decide +kernel)
def p4_eae8T : Nat := 0xeae8eae8eae8eae8eae8eae8eae8eae8
def p4_eae8R : List Nat := [0, 1, 2, 3]
def p4_eae8E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p4_eae8B : baseOK p4_eae8T p4_eae8R p4_eae8E = true := by decide +kernel
theorem p4_eae8S0 : SliceN p4_eae8R p4_eae8T (0xff00ff00ff00ff00ff00ff00ff00ff,4,[0, 1, 2]) := mkSlice (w:=0) p4_eae8B p3_e8B p3_e8L (by decide +kernel)
def p4_eae8Z : List SliceD := [(0xff00ff00ff00ff00ff00ff00ff00ff,4,[0, 1, 2])]
theorem p4_eae8Y : ∀ s ∈ p4_eae8Z, SliceN p4_eae8R p4_eae8T s := by
  unfold p4_eae8Z
  simp only [List.forall_mem_cons]
  exact ⟨p4_eae8S0,by simp⟩
def p4_eae8D4 : List StD := dupD [
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00],[(0,[])],[],[[0],[0],[0],[0],[0],[0]])]
def p4_eae8D3 : List StD := []
theorem p4_eae8I3 : LevelN p4_eae8R p4_eae8T 3 p4_eae8D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4_eae8C4x0 : levelOK p4_eae8T p4_eae8Z 3 (p4_eae8D3.map Prod.fst) ((p4_eae8D4.drop (0*8)).take 8) = true := by decide +kernel
theorem p4_eae8I4 : LevelN p4_eae8R p4_eae8T 4 p4_eae8D4 := levelStep p4_eae8B p4_eae8Y p4_eae8I3 (chunks 8 p4_eae8D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p4_eae8C4x0
  ))
theorem p4_eae8L : LowN p4_eae8R p4_eae8T 5 := lowSearch p4_eae8B p4_eae8I4 (by decide +kernel)
def p4_feeaT : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeea
def p4_feeaR : List Nat := [0, 1, 2, 3]
def p4_feeaE : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,2,10)]
theorem p4_feeaB : baseOK p4_feeaT p4_feeaR p4_feeaE = true := by decide +kernel
theorem p4_feeaS0 : SliceN p4_feeaR p4_feeaT (0x55555555555555555555555555555555,4,[1, 2, 3]) := mkSlice (w:=0) p4_feeaB p3_e8B p3_e8L (by decide +kernel)
def p4_feeaZ : List SliceD := [(0x55555555555555555555555555555555,4,[1, 2, 3])]
theorem p4_feeaY : ∀ s ∈ p4_feeaZ, SliceN p4_feeaR p4_feeaT s := by
  unfold p4_feeaZ
  simp only [List.forall_mem_cons]
  exact ⟨p4_feeaS0,by simp⟩
def p4_feeaD4 : List StD := dupD [
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00],[(0,[])],[],[[0],[0],[0],[0],[0],[0]])]
def p4_feeaD3 : List StD := []
theorem p4_feeaI3 : LevelN p4_feeaR p4_feeaT 3 p4_feeaD3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4_feeaC4x0 : levelOK p4_feeaT p4_feeaZ 3 (p4_feeaD3.map Prod.fst) ((p4_feeaD4.drop (0*8)).take 8) = true := by decide +kernel
theorem p4_feeaI4 : LevelN p4_feeaR p4_feeaT 4 p4_feeaD4 := levelStep p4_feeaB p4_feeaY p4_feeaI3 (chunks 8 p4_feeaD4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p4_feeaC4x0
  ))
theorem p4_feeaL : LowN p4_feeaR p4_feeaT 5 := lowSearch p4_feeaB p4_feeaI4 (by decide +kernel)
def p3_feT : Nat := 0xfefefefefefefefefefefefefefefefe
def p3_feR : List Nat := [0, 1, 2]
def p3_feE : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4)]
theorem p3_feB : baseOK p3_feT p3_feR p3_feE = true := by decide +kernel
theorem p3_feL : LowN p3_feR p3_feT 2 := lowCount p3_feB (by decide +kernel)
def p4_eac0T : Nat := 0xeac0eac0eac0eac0eac0eac0eac0eac0
def p4_eac0R : List Nat := [0, 1, 2, 3]
def p4_eac0E : List (Nat × Nat × Nat) := [(0,8,9),(1,4,6),(2,2,6),(3,1,9)]
theorem p4_eac0B : baseOK p4_eac0T p4_eac0R p4_eac0E = true := by decide +kernel
theorem p4_eac0L : LowN p4_eac0R p4_eac0T 3 := lowCount p4_eac0B (by decide +kernel)
def p4_feeeT : Nat := 0xfeeefeeefeeefeeefeeefeeefeeefeee
def p4_feeeR : List Nat := [0, 1, 2, 3]
def p4_feeeE : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,8,12),(3,4,12)]
theorem p4_feeeB : baseOK p4_feeeT p4_feeeR p4_feeeE = true := by decide +kernel
theorem p4_feeeL : LowN p4_feeeR p4_feeeT 3 := lowCount p4_feeeB (by decide +kernel)
def p5_feeafcc8T : Nat := 0xfeeafcc8feeafcc8feeafcc8feeafcc8
def p5_feeafcc8R : List Nat := [0, 1, 2, 3, 4]
def p5_feeafcc8E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,2,10),(4,1,17)]
theorem p5_feeafcc8B : baseOK p5_feeafcc8T p5_feeafcc8R p5_feeafcc8E = true := by decide +kernel
theorem p5_feeafcc8S0 : SliceN p5_feeafcc8R p5_feeafcc8T (0x5555000055550000555500005555,4,[1, 2, 3]) := mkSlice (w:=0) p5_feeafcc8B p3_e8B p3_e8L (by decide +kernel)
theorem p5_feeafcc8S1 : SliceN p5_feeafcc8R p5_feeafcc8T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3, 4]) := mkSlice (w:=0) p5_feeafcc8B p4_eac8B p4_eac8L (by decide +kernel)
theorem p5_feeafcc8S2 : SliceN p5_feeafcc8R p5_feeafcc8T (0xff00ff00ff00ff00ff00ff00ff00ff,4,[0, 1, 2, 4]) := mkSlice (w:=0) p5_feeafcc8B p4_eac8B p4_eac8L (by decide +kernel)
theorem p5_feeafcc8S3 : SliceN p5_feeafcc8R p5_feeafcc8T (0xffff0000ffff0000ffff0000ffff,5,[1, 2, 3, 0]) := mkSlice (w:=0) p5_feeafcc8B p4_eae8B p4_eae8L (by decide +kernel)
theorem p5_feeafcc8S4 : SliceN p5_feeafcc8R p5_feeafcc8T (0xffff0000ffff0000ffff0000ffff0000,5,[0, 1, 2, 3]) := mkSlice (w:=16) p5_feeafcc8B p4_feeaB p4_feeaL (by decide +kernel)
theorem p5_feeafcc8S5 : SliceN p5_feeafcc8R p5_feeafcc8T (0xcccc0000cccc0000cccc0000cccc,2,[0, 2, 3]) := mkSlice (w:=2) p5_feeafcc8B p3_feB p3_feL (by decide +kernel)
theorem p5_feeafcc8S6 : SliceN p5_feeafcc8R p5_feeafcc8T (0x30303030303030303030303030303030,2,[3, 0, 4]) := mkSlice (w:=4) p5_feeafcc8B p3_eaB p3_eaL (by decide +kernel)
theorem p5_feeafcc8S7 : SliceN p5_feeafcc8R p5_feeafcc8T (0x30003000300030003000300030003,1,[0, 4]) := mkSlice (w:=0) p5_feeafcc8B p2_8B p2_8L (by decide +kernel)
theorem p5_feeafcc8S8 : SliceN p5_feeafcc8R p5_feeafcc8T (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,2,[1, 3, 4]) := mkSlice (w:=5) p5_feeafcc8B p3_feB p3_feL (by decide +kernel)
theorem p5_feeafcc8S9 : SliceN p5_feeafcc8R p5_feeafcc8T (0xc0c00000c0c00000c0c00000c0c,1,[0, 3]) := mkSlice (w:=2) p5_feeafcc8B p2_eB p2_eL (by decide +kernel)
theorem p5_feeafcc8S10 : SliceN p5_feeafcc8R p5_feeafcc8T (0x33333333333333333333333333333333,3,[0, 2, 3, 4]) := mkSlice (w:=0) p5_feeafcc8B p4_eac0B p4_eac0L (by decide +kernel)
theorem p5_feeafcc8S11 : SliceN p5_feeafcc8R p5_feeafcc8T (0xaa00aa00aa00aa00aa00aa00aa00aa00,2,[1, 2, 4]) := mkSlice (w:=9) p5_feeafcc8B p3_feB p3_feL (by decide +kernel)
theorem p5_feeafcc8S12 : SliceN p5_feeafcc8R p5_feeafcc8T (0xff00ff00ff00ff00ff00ff00ff00ff00,3,[1, 2, 0, 4]) := mkSlice (w:=8) p5_feeafcc8B p4_feeeB p4_feeeL (by decide +kernel)
theorem p5_feeafcc8S13 : SliceN p5_feeafcc8R p5_feeafcc8T (0x33003300330033003300330033003300,2,[2, 0, 4]) := mkSlice (w:=8) p5_feeafcc8B p3_eaB p3_eaL (by decide +kernel)
theorem p5_feeafcc8S14 : SliceN p5_feeafcc8R p5_feeafcc8T (0xcc000000cc000000cc000000cc,1,[0, 2]) := mkSlice (w:=2) p5_feeafcc8B p2_eB p2_eL (by decide +kernel)
theorem p5_feeafcc8S15 : SliceN p5_feeafcc8R p5_feeafcc8T (0xf000f000f000f000f000f000f000f,2,[0, 1, 4]) := mkSlice (w:=0) p5_feeafcc8B p3_a8B p3_a8L (by decide +kernel)
theorem p5_feeafcc8S16 : SliceN p5_feeafcc8R p5_feeafcc8T (0xcccc0000cccc0000cccc0000cccc0000,2,[0, 2, 3]) := mkSlice (w:=18) p5_feeafcc8B p3_feB p3_feL (by decide +kernel)
theorem p5_feeafcc8S17 : SliceN p5_feeafcc8R p5_feeafcc8T (0xf0f00000f0f00000f0f00000f0f00000,2,[0, 1, 3]) := mkSlice (w:=20) p5_feeafcc8B p3_feB p3_feL (by decide +kernel)
theorem p5_feeafcc8S18 : SliceN p5_feeafcc8R p5_feeafcc8T (0x5050000050500000505000005050,1,[1, 3]) := mkSlice (w:=4) p5_feeafcc8B p2_eB p2_eL (by decide +kernel)
theorem p5_feeafcc8S19 : SliceN p5_feeafcc8R p5_feeafcc8T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,3,[1, 4, 3, 2]) := mkSlice (w:=1) p5_feeafcc8B p4_feeeB p4_feeeL (by decide +kernel)
def p5_feeafcc8Z : List SliceD := [(0x5555000055550000555500005555,4,[1, 2, 3]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff,4,[0, 1, 2, 4]),(0xffff0000ffff0000ffff0000ffff,5,[1, 2, 3, 0]),(0xffff0000ffff0000ffff0000ffff0000,5,[0, 1, 2, 3]),(0xcccc0000cccc0000cccc0000cccc,2,[0, 2, 3]),(0x30303030303030303030303030303030,2,[3, 0, 4]),(0x30003000300030003000300030003,1,[0, 4]),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0,2,[1, 3, 4]),(0xc0c00000c0c00000c0c00000c0c,1,[0, 3]),(0x33333333333333333333333333333333,3,[0, 2, 3, 4]),(0xaa00aa00aa00aa00aa00aa00aa00aa00,2,[1, 2, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff00,3,[1, 2, 0, 4]),(0x33003300330033003300330033003300,2,[2, 0, 4]),(0xcc000000cc000000cc000000cc,1,[0, 2]),(0xf000f000f000f000f000f000f000f,2,[0, 1, 4]),(0xcccc0000cccc0000cccc0000cccc0000,2,[0, 2, 3]),(0xf0f00000f0f00000f0f00000f0f00000,2,[0, 1, 3]),(0x5050000050500000505000005050,1,[1, 3]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,3,[1, 4, 3, 2])]
theorem p5_feeafcc8Y : ∀ s ∈ p5_feeafcc8Z, SliceN p5_feeafcc8R p5_feeafcc8T s := by
  unfold p5_feeafcc8Z
  simp only [List.forall_mem_cons]
  exact ⟨p5_feeafcc8S0,p5_feeafcc8S1,p5_feeafcc8S2,p5_feeafcc8S3,p5_feeafcc8S4,p5_feeafcc8S5,p5_feeafcc8S6,p5_feeafcc8S7,p5_feeafcc8S8,p5_feeafcc8S9,p5_feeafcc8S10,p5_feeafcc8S11,p5_feeafcc8S12,p5_feeafcc8S13,p5_feeafcc8S14,p5_feeafcc8S15,p5_feeafcc8S16,p5_feeafcc8S17,p5_feeafcc8S18,p5_feeafcc8S19,by simp⟩
def p5_feeafcc8D6 : List StD := dupD [
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[]),(1,[]),(2,[]),(3,[]),(4,[])],[(2,3),(16,17),(20,21),(24,25),(8,12),(4,6),(2,6),(4,12),(8,10),(2,10)],[[0,1000,1001],[0,1002,1,1000],[0,1003,2,1000],[0,3,4],[1,1004,1005,1006],[2,1007,1008,1009],[0,4],[1,2,1006,1004,1007],[0,4],[0,4]])]
def p5_feeafcc8D5 : List StD := dupD [
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[(1,0,1)]),(5,[]),(6,[]),(1,[]),(7,[]),(8,[]),(4,[(1,1,2)]),(3,[(2,0,1)]),(2,[])],[],[[0,1,2],[0,2,3],[0,1,4],[0,5],[1,5,6],[3,5],[3],[2,1],[0,6],[7],[3,2],[0,2,3],[8,1],[0,2,4],[0,6]]),
 ([0xc0c0c0c0c0c0c0c,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[]),(9,[]),(10,[]),(3,[(0,0,1)]),(3,[(1,0,1)]),(4,[]),(6,[]),(0,[(2,0,1)]),(8,[]),(4,[(2,1,2)]),(1,[])],[],[[0,1,2],[3],[4],[2,1],[0,5],[2,1],[1,6],[7,8],[1,8,9],[2,8,10],[2,1],[2,9,7],[1,6],[7,6,9],[1,9]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffccffccffcc,0xffff0000ffff0000],[(0,[(1,0,2)]),(5,[]),(7,[]),(11,[]),(12,[]),(4,[(1,1,3)]),(13,[]),(2,[]),(1,[]),(3,[(2,0,2)])],[],[[0,1,2],[0,3],[0,4,2],[0,1,2],[1,3,5],[6,1],[7,3],[7],[0,5],[7,3],[8,1],[0,5],[9],[0,3,2],[0,3,2]]),
 ([0xcc00cc00cc00cc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[]),(14,[]),(6,[]),(3,[(0,0,2)]),(1,[]),(10,[]),(3,[(1,0,2)]),(4,[]),(0,[(2,0,2)]),(7,[]),(12,[]),(4,[(2,1,3)]),(2,[])],[],[[0,1,2],[3],[4,1,5],[6],[0,7],[2,1],[8,2,9],[1,10],[1,11],[5,1],[2,10,12],[2,11,8],[1,2,10],[1,2,9],[8,10,9]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfff0fff0fff0fff0,0xffff0000ffff0000],[(0,[(1,1,2)]),(8,[]),(6,[]),(1,[]),(7,[]),(3,[(1,1,2)]),(4,[(1,2,3)]),(12,[]),(2,[]),(15,[])],[],[[0,1],[0,2,3],[0,1],[0,2,4],[5,1,6],[3,1],[2,7,8],[9,1],[0,6],[3,1],[8],[0,1,3],[3],[0,6],[0,1,4]])]
def p5_feeafcc8D4 : List StD := dupD [
 ([0xfc00fc00fc00fc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000],[(0,[]),(8,[]),(3,[(2,0,2)]),(1,[]),(3,[(0,0,2)]),(4,[]),(7,[]),(5,[]),(6,[]),(16,[]),(1,[(2,1,2)]),(17,[]),(18,[])],[],[[0,1],[2,3,4],[3,1],[0,5],[6,1,7],[6,8],[7,1,9],[10,1],[6,11,12],[6,1]]),
 ([0xf0c0f0c0f0c0f0c,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000],[(7,[]),(19,[]),(0,[]),(3,[(2,0,1)]),(5,[]),(3,[(0,0,1)]),(3,[(3,1,2)]),(12,[]),(3,[(0,1,2)]),(4,[]),(8,[]),(17,[]),(6,[]),(18,[])],[],[[0,1,2],[3,4,5],[6,7,8],[0,9,2],[0,4],[0,7],[4,10,11],[12,4],[0,11,13],[0,7]])]
def p5_feeafcc8D3 : List StD := []
theorem p5_feeafcc8I3 : LevelN p5_feeafcc8R p5_feeafcc8T 3 p5_feeafcc8D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_feeafcc8C4x0 : levelOK p5_feeafcc8T p5_feeafcc8Z 3 (p5_feeafcc8D3.map Prod.fst) ((p5_feeafcc8D4.drop (0*8)).take 8) = true := by decide +kernel
theorem p5_feeafcc8I4 : LevelN p5_feeafcc8R p5_feeafcc8T 4 p5_feeafcc8D4 := levelStep p5_feeafcc8B p5_feeafcc8Y p5_feeafcc8I3 (chunks 8 p5_feeafcc8D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_feeafcc8C4x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_feeafcc8C5x0 : levelOK p5_feeafcc8T p5_feeafcc8Z 4 (p5_feeafcc8D4.map Prod.fst) ((p5_feeafcc8D5.drop (0*8)).take 8) = true := by decide +kernel
theorem p5_feeafcc8I5 : LevelN p5_feeafcc8R p5_feeafcc8T 5 p5_feeafcc8D5 := levelStep p5_feeafcc8B p5_feeafcc8Y p5_feeafcc8I4 (chunks 8 p5_feeafcc8D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_feeafcc8C5x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_feeafcc8C6x0 : levelOK p5_feeafcc8T p5_feeafcc8Z 5 (p5_feeafcc8D5.map Prod.fst) ((p5_feeafcc8D6.drop (0*8)).take 8) = true := by decide +kernel
theorem p5_feeafcc8I6 : LevelN p5_feeafcc8R p5_feeafcc8T 6 p5_feeafcc8D6 := levelStep p5_feeafcc8B p5_feeafcc8Y p5_feeafcc8I5 (chunks 8 p5_feeafcc8D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_feeafcc8C6x0
  ))
theorem p5_feeafcc8L : LowN p5_feeafcc8R p5_feeafcc8T 7 := lowSearch p5_feeafcc8B p5_feeafcc8I6 (by decide +kernel)
def p4_eee8T : Nat := 0xeee8eee8eee8eee8eee8eee8eee8eee8
def p4_eee8R : List Nat := [0, 1, 2, 3]
def p4_eee8E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p4_eee8B : baseOK p4_eee8T p4_eee8R p4_eee8E = true := by decide +kernel
theorem p4_eee8S0 : SliceN p4_eee8R p4_eee8T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3]) := mkSlice (w:=0) p4_eee8B p3_e8B p3_e8L (by decide +kernel)
def p4_eee8Z : List SliceD := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3])]
theorem p4_eee8Y : ∀ s ∈ p4_eee8Z, SliceN p4_eee8R p4_eee8T s := by
  unfold p4_eee8Z
  simp only [List.forall_mem_cons]
  exact ⟨p4_eee8S0,by simp⟩
def p4_eee8D4 : List StD := dupD [
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00],[(0,[])],[],[[0],[0],[0],[0],[0],[0]])]
def p4_eee8D3 : List StD := []
theorem p4_eee8I3 : LevelN p4_eee8R p4_eee8T 3 p4_eee8D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4_eee8C4x0 : levelOK p4_eee8T p4_eee8Z 3 (p4_eee8D3.map Prod.fst) ((p4_eee8D4.drop (0*8)).take 8) = true := by decide +kernel
theorem p4_eee8I4 : LevelN p4_eee8R p4_eee8T 4 p4_eee8D4 := levelStep p4_eee8B p4_eee8Y p4_eee8I3 (chunks 8 p4_eee8D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p4_eee8C4x0
  ))
theorem p4_eee8L : LowN p4_eee8R p4_eee8T 5 := lowSearch p4_eee8B p4_eee8I4 (by decide +kernel)
def p5_feeafce8T : Nat := 0xfeeafce8feeafce8feeafce8feeafce8
def p5_feeafce8R : List Nat := [0, 1, 2, 3, 4]
def p5_feeafce8E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,2,10),(4,1,17)]
theorem p5_feeafce8B : baseOK p5_feeafce8T p5_feeafce8R p5_feeafce8E = true := by decide +kernel
theorem p5_feeafce8S0 : SliceN p5_feeafce8R p5_feeafce8T (0x33333333333333333333333333333333,4,[0, 2, 3, 4]) := mkSlice (w:=0) p5_feeafce8B p4_eac8B p4_eac8L (by decide +kernel)
theorem p5_feeafce8S1 : SliceN p5_feeafce8R p5_feeafce8T (0x5555000055550000555500005555,4,[1, 2, 3]) := mkSlice (w:=0) p5_feeafce8B p3_e8B p3_e8L (by decide +kernel)
theorem p5_feeafce8S2 : SliceN p5_feeafce8R p5_feeafce8T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3, 4]) := mkSlice (w:=0) p5_feeafce8B p4_eac8B p4_eac8L (by decide +kernel)
theorem p5_feeafce8S3 : SliceN p5_feeafce8R p5_feeafce8T (0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]) := mkSlice (w:=0) p5_feeafce8B p4_eae8B p4_eae8L (by decide +kernel)
theorem p5_feeafce8S4 : SliceN p5_feeafce8R p5_feeafce8T (0xffff0000ffff0000ffff0000ffff,5,[1, 2, 0, 3]) := mkSlice (w:=0) p5_feeafce8B p4_eee8B p4_eee8L (by decide +kernel)
theorem p5_feeafce8S5 : SliceN p5_feeafce8R p5_feeafce8T (0xffff0000ffff0000ffff0000ffff0000,5,[0, 1, 2, 3]) := mkSlice (w:=16) p5_feeafce8B p4_feeaB p4_feeaL (by decide +kernel)
theorem p5_feeafce8S6 : SliceN p5_feeafce8R p5_feeafce8T (0xcccc0000cccc0000cccc0000cccc,2,[0, 2, 3]) := mkSlice (w:=2) p5_feeafce8B p3_feB p3_feL (by decide +kernel)
theorem p5_feeafce8S7 : SliceN p5_feeafce8R p5_feeafce8T (0xf0f00000f0f00000f0f00000f0f0,2,[0, 1, 3]) := mkSlice (w:=4) p5_feeafce8B p3_feB p3_feL (by decide +kernel)
theorem p5_feeafce8S8 : SliceN p5_feeafce8R p5_feeafce8T (0x30003000300030003000300030003,1,[0, 4]) := mkSlice (w:=0) p5_feeafce8B p2_8B p2_8L (by decide +kernel)
theorem p5_feeafce8S9 : SliceN p5_feeafce8R p5_feeafce8T (0x3000300030003000300030003000300,1,[0, 4]) := mkSlice (w:=8) p5_feeafce8B p2_8B p2_8L (by decide +kernel)
theorem p5_feeafce8S10 : SliceN p5_feeafce8R p5_feeafce8T (0xcc000000cc000000cc000000cc,1,[0, 2]) := mkSlice (w:=2) p5_feeafce8B p2_eB p2_eL (by decide +kernel)
theorem p5_feeafce8S11 : SliceN p5_feeafce8R p5_feeafce8T (0xff00ff00ff00ff00ff00ff00ff00ff00,3,[1, 2, 0, 4]) := mkSlice (w:=8) p5_feeafce8B p4_feeeB p4_feeeL (by decide +kernel)
theorem p5_feeafce8S12 : SliceN p5_feeafce8R p5_feeafce8T (0xaa00aa00aa00aa00aa00aa00aa00aa00,2,[1, 2, 4]) := mkSlice (w:=9) p5_feeafce8B p3_feB p3_feL (by decide +kernel)
theorem p5_feeafce8S13 : SliceN p5_feeafce8R p5_feeafce8T (0xcccc0000cccc0000cccc0000cccc0000,2,[0, 2, 3]) := mkSlice (w:=18) p5_feeafce8B p3_feB p3_feL (by decide +kernel)
theorem p5_feeafce8S14 : SliceN p5_feeafce8R p5_feeafce8T (0xf0f00000f0f00000f0f00000f0f00000,2,[0, 1, 3]) := mkSlice (w:=20) p5_feeafce8B p3_feB p3_feL (by decide +kernel)
def p5_feeafce8Z : List SliceD := [(0x33333333333333333333333333333333,4,[0, 2, 3, 4]),(0x5555000055550000555500005555,4,[1, 2, 3]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]),(0xffff0000ffff0000ffff0000ffff,5,[1, 2, 0, 3]),(0xffff0000ffff0000ffff0000ffff0000,5,[0, 1, 2, 3]),(0xcccc0000cccc0000cccc0000cccc,2,[0, 2, 3]),(0xf0f00000f0f00000f0f00000f0f0,2,[0, 1, 3]),(0x30003000300030003000300030003,1,[0, 4]),(0x3000300030003000300030003000300,1,[0, 4]),(0xcc000000cc000000cc000000cc,1,[0, 2]),(0xff00ff00ff00ff00ff00ff00ff00ff00,3,[1, 2, 0, 4]),(0xaa00aa00aa00aa00aa00aa00aa00aa00,2,[1, 2, 4]),(0xcccc0000cccc0000cccc0000cccc0000,2,[0, 2, 3]),(0xf0f00000f0f00000f0f00000f0f00000,2,[0, 1, 3])]
theorem p5_feeafce8Y : ∀ s ∈ p5_feeafce8Z, SliceN p5_feeafce8R p5_feeafce8T s := by
  unfold p5_feeafce8Z
  simp only [List.forall_mem_cons]
  exact ⟨p5_feeafce8S0,p5_feeafce8S1,p5_feeafce8S2,p5_feeafce8S3,p5_feeafce8S4,p5_feeafce8S5,p5_feeafce8S6,p5_feeafce8S7,p5_feeafce8S8,p5_feeafce8S9,p5_feeafce8S10,p5_feeafce8S11,p5_feeafce8S12,p5_feeafce8S13,p5_feeafce8S14,by simp⟩
def p5_feeafce8D6 : List StD := dupD [
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])],[(2,3),(0,3),(4,5),(17,24),(1,3),(4,6),(2,6),(2,10),(0,10),(4,12)],[[0,1,1000,1001],[1,1002,2,1000],[1,3,1003],[1,4,5],[0,2,1004,1005,1006],[0,3,1007,1008],[0,1,5],[2,3,1009,1007],[1,5],[1,3,5]])]
def p5_feeafce8D5 : List StD := dupD [
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[]),(6,[]),(2,[]),(7,[]),(1,[]),(8,[]),(9,[]),(5,[(1,1,2)]),(3,[])],[],[[0,1],[2,3],[4,1,5],[5,6],[1,7],[0,1],[2],[0,1],[0,7,3],[0],[2,3],[1,7],[8,1],[4,7],[1,6,5]])]
def p5_feeafce8D4 : List StD := dupD [
 ([0xfc00fc00fc00fc,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000],[(1,[]),(10,[]),(11,[]),(3,[(1,1,2)]),(5,[]),(0,[(2,1,2)]),(2,[(2,1,2)]),(7,[]),(12,[]),(13,[]),(14,[])],[],[[0,1,2],[2,3],[2,1],[0,4],[5,1],[6,7],[1,8,9],[5,1],[5,10,7],[1,9]])]
def p5_feeafce8D3 : List StD := []
theorem p5_feeafce8I3 : LevelN p5_feeafce8R p5_feeafce8T 3 p5_feeafce8D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_feeafce8C4x0 : levelOK p5_feeafce8T p5_feeafce8Z 3 (p5_feeafce8D3.map Prod.fst) ((p5_feeafce8D4.drop (0*8)).take 8) = true := by decide +kernel
theorem p5_feeafce8I4 : LevelN p5_feeafce8R p5_feeafce8T 4 p5_feeafce8D4 := levelStep p5_feeafce8B p5_feeafce8Y p5_feeafce8I3 (chunks 8 p5_feeafce8D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_feeafce8C4x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_feeafce8C5x0 : levelOK p5_feeafce8T p5_feeafce8Z 4 (p5_feeafce8D4.map Prod.fst) ((p5_feeafce8D5.drop (0*8)).take 8) = true := by decide +kernel
theorem p5_feeafce8I5 : LevelN p5_feeafce8R p5_feeafce8T 5 p5_feeafce8D5 := levelStep p5_feeafce8B p5_feeafce8Y p5_feeafce8I4 (chunks 8 p5_feeafce8D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_feeafce8C5x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_feeafce8C6x0 : levelOK p5_feeafce8T p5_feeafce8Z 5 (p5_feeafce8D5.map Prod.fst) ((p5_feeafce8D6.drop (0*8)).take 8) = true := by decide +kernel
theorem p5_feeafce8I6 : LevelN p5_feeafce8R p5_feeafce8T 6 p5_feeafce8D6 := levelStep p5_feeafce8B p5_feeafce8Y p5_feeafce8I5 (chunks 8 p5_feeafce8D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_feeafce8C6x0
  ))
theorem p5_feeafce8L : LowN p5_feeafce8R p5_feeafce8T 7 := lowSearch p5_feeafce8B p5_feeafce8I6 (by decide +kernel)
def p4_fffeT : Nat := 0xfffefffefffefffefffefffefffefffe
def p4_fffeR : List Nat := [0, 1, 2, 3]
def p4_fffeE : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4),(3,0,8)]
theorem p4_fffeB : baseOK p4_fffeT p4_fffeR p4_fffeE = true := by decide +kernel
theorem p4_fffeL : LowN p4_fffeR p4_fffeT 3 := lowCount p4_fffeB (by decide +kernel)
def p5_feeefaa8T : Nat := 0xfeeefaa8feeefaa8feeefaa8feeefaa8
def p5_feeefaa8R : List Nat := [0, 1, 2, 3, 4]
def p5_feeefaa8E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17)]
theorem p5_feeefaa8B : baseOK p5_feeefaa8T p5_feeefaa8R p5_feeefaa8E = true := by decide +kernel
theorem p5_feeefaa8S0 : SliceN p5_feeefaa8R p5_feeefaa8T (0x33333333333333333333333333333333,5,[0, 2, 3, 4]) := mkSlice (w:=0) p5_feeefaa8B p4_eae8B p4_eae8L (by decide +kernel)
theorem p5_feeefaa8S1 : SliceN p5_feeefaa8R p5_feeefaa8T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 4, 3]) := mkSlice (w:=0) p5_feeefaa8B p4_eae8B p4_eae8L (by decide +kernel)
theorem p5_feeefaa8S2 : SliceN p5_feeefaa8R p5_feeefaa8T (0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 4, 2]) := mkSlice (w:=0) p5_feeefaa8B p4_eae8B p4_eae8L (by decide +kernel)
theorem p5_feeefaa8S3 : SliceN p5_feeefaa8R p5_feeefaa8T (0xffff0000ffff0000ffff0000ffff,5,[0, 2, 3, 1]) := mkSlice (w:=0) p5_feeefaa8B p4_eae8B p4_eae8L (by decide +kernel)
theorem p5_feeefaa8S4 : SliceN p5_feeefaa8R p5_feeefaa8T (0x3333000033330000333300003333,4,[0, 2, 3]) := mkSlice (w:=0) p5_feeefaa8B p3_e8B p3_e8L (by decide +kernel)
theorem p5_feeefaa8S5 : SliceN p5_feeefaa8R p5_feeefaa8T (0xf000f000f000f000f000f000f000f,4,[0, 1, 4]) := mkSlice (w:=0) p5_feeefaa8B p3_e8B p3_e8L (by decide +kernel)
theorem p5_feeefaa8S6 : SliceN p5_feeefaa8R p5_feeefaa8T (0x44444444444444444444444444444444,2,[4, 3, 2]) := mkSlice (w:=2) p5_feeefaa8B p3_eaB p3_eaL (by decide +kernel)
theorem p5_feeefaa8S7 : SliceN p5_feeefaa8R p5_feeefaa8T (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0,2,[0, 3, 4]) := mkSlice (w:=6) p5_feeefaa8B p3_feB p3_feL (by decide +kernel)
theorem p5_feeefaa8S8 : SliceN p5_feeefaa8R p5_feeefaa8T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,3,[1, 2, 3, 4]) := mkSlice (w:=1) p5_feeefaa8B p4_fffeB p4_fffeL (by decide +kernel)
theorem p5_feeefaa8S9 : SliceN p5_feeefaa8R p5_feeefaa8T (0xcc00cc00cc00cc00cc00cc00cc00cc00,2,[0, 2, 4]) := mkSlice (w:=10) p5_feeefaa8B p3_feB p3_feL (by decide +kernel)
theorem p5_feeefaa8S10 : SliceN p5_feeefaa8R p5_feeefaa8T (0x1111000011110000111100001111,1,[2, 3]) := mkSlice (w:=0) p5_feeefaa8B p2_8B p2_8L (by decide +kernel)
theorem p5_feeefaa8S11 : SliceN p5_feeefaa8R p5_feeefaa8T (0x55555555555555555555555555555555,3,[1, 2, 3, 4]) := mkSlice (w:=0) p5_feeefaa8B p4_eac0B p4_eac0L (by decide +kernel)
theorem p5_feeefaa8S12 : SliceN p5_feeefaa8R p5_feeefaa8T (0x22222222222222222222222222222222,2,[2, 3, 4]) := mkSlice (w:=1) p5_feeefaa8B p3_feB p3_feL (by decide +kernel)
theorem p5_feeefaa8S13 : SliceN p5_feeefaa8R p5_feeefaa8T (0x50505050505050505050505050505050,2,[3, 1, 4]) := mkSlice (w:=4) p5_feeefaa8B p3_eaB p3_eaL (by decide +kernel)
theorem p5_feeefaa8S14 : SliceN p5_feeefaa8R p5_feeefaa8T (0x55005500550055005500550055005500,2,[2, 1, 4]) := mkSlice (w:=8) p5_feeefaa8B p3_eaB p3_eaL (by decide +kernel)
theorem p5_feeefaa8S15 : SliceN p5_feeefaa8R p5_feeefaa8T (0xf0f00000f0f00000f0f00000f0f00000,2,[0, 1, 3]) := mkSlice (w:=20) p5_feeefaa8B p3_feB p3_feL (by decide +kernel)
theorem p5_feeefaa8S16 : SliceN p5_feeefaa8R p5_feeefaa8T (0x50005000500050005000500050005,1,[1, 4]) := mkSlice (w:=0) p5_feeefaa8B p2_8B p2_8L (by decide +kernel)
theorem p5_feeefaa8S17 : SliceN p5_feeefaa8R p5_feeefaa8T (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,2,[1, 3, 4]) := mkSlice (w:=1) p5_feeefaa8B p3_feB p3_feL (by decide +kernel)
theorem p5_feeefaa8S18 : SliceN p5_feeefaa8R p5_feeefaa8T (0x55550000555500005555000055550000,2,[1, 2, 3]) := mkSlice (w:=16) p5_feeefaa8B p3_eaB p3_eaL (by decide +kernel)
theorem p5_feeefaa8S19 : SliceN p5_feeefaa8R p5_feeefaa8T (0xff000000ff000000ff000000ff000000,2,[0, 1, 2]) := mkSlice (w:=24) p5_feeefaa8B p3_feB p3_feL (by decide +kernel)
theorem p5_feeefaa8S20 : SliceN p5_feeefaa8R p5_feeefaa8T (0xaa00aa00aa00aa00aa00aa00aa00aa,2,[1, 2, 4]) := mkSlice (w:=1) p5_feeefaa8B p3_feB p3_feL (by decide +kernel)
theorem p5_feeefaa8S21 : SliceN p5_feeefaa8R p5_feeefaa8T (0xaaaa0000aaaa0000aaaa0000aaaa,2,[1, 2, 3]) := mkSlice (w:=1) p5_feeefaa8B p3_feB p3_feL (by decide +kernel)
theorem p5_feeefaa8S22 : SliceN p5_feeefaa8R p5_feeefaa8T (0x3030303030303030303030303030303,2,[0, 3, 4]) := mkSlice (w:=0) p5_feeefaa8B p3_a8B p3_a8L (by decide +kernel)
theorem p5_feeefaa8S23 : SliceN p5_feeefaa8R p5_feeefaa8T (0x2020202020202020202020202020202,1,[3, 4]) := mkSlice (w:=1) p5_feeefaa8B p2_eB p2_eL (by decide +kernel)
theorem p5_feeefaa8S24 : SliceN p5_feeefaa8R p5_feeefaa8T (0x220022002200220022002200220022,1,[2, 4]) := mkSlice (w:=1) p5_feeefaa8B p2_eB p2_eL (by decide +kernel)
theorem p5_feeefaa8S25 : SliceN p5_feeefaa8R p5_feeefaa8T (0x330033003300330033003300330033,2,[0, 2, 4]) := mkSlice (w:=0) p5_feeefaa8B p3_a8B p3_a8L (by decide +kernel)
theorem p5_feeefaa8S26 : SliceN p5_feeefaa8R p5_feeefaa8T (0xa0a00000a0a00000a0a00000a0a,1,[1, 3]) := mkSlice (w:=1) p5_feeefaa8B p2_eB p2_eL (by decide +kernel)
theorem p5_feeefaa8S27 : SliceN p5_feeefaa8R p5_feeefaa8T (0xf0f00000f0f00000f0f00000f0f,2,[0, 1, 3]) := mkSlice (w:=0) p5_feeefaa8B p3_a8B p3_a8L (by decide +kernel)
theorem p5_feeefaa8S28 : SliceN p5_feeefaa8R p5_feeefaa8T (0xaa000000aa000000aa000000aa,1,[1, 2]) := mkSlice (w:=1) p5_feeefaa8B p2_eB p2_eL (by decide +kernel)
theorem p5_feeefaa8S29 : SliceN p5_feeefaa8R p5_feeefaa8T (0xff000000ff000000ff000000ff,2,[0, 1, 2]) := mkSlice (w:=0) p5_feeefaa8B p3_a8B p3_a8L (by decide +kernel)
theorem p5_feeefaa8S30 : SliceN p5_feeefaa8R p5_feeefaa8T (0xc000c000c000c000c000c000c000c,1,[0, 4]) := mkSlice (w:=2) p5_feeefaa8B p2_eB p2_eL (by decide +kernel)
theorem p5_feeefaa8S31 : SliceN p5_feeefaa8R p5_feeefaa8T (0x3030000030300000303000003030,1,[0, 3]) := mkSlice (w:=4) p5_feeefaa8B p2_eB p2_eL (by decide +kernel)
theorem p5_feeefaa8S32 : SliceN p5_feeefaa8R p5_feeefaa8T (0x44004400440044004400440044004400,1,[2, 4]) := mkSlice (w:=10) p5_feeefaa8B p2_eB p2_eL (by decide +kernel)
theorem p5_feeefaa8S33 : SliceN p5_feeefaa8R p5_feeefaa8T (0x40404040404040404040404040404040,1,[3, 4]) := mkSlice (w:=6) p5_feeefaa8B p2_eB p2_eL (by decide +kernel)
def p5_feeefaa8Z : List SliceD := [(0x33333333333333333333333333333333,5,[0, 2, 3, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 4, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 4, 2]),(0xffff0000ffff0000ffff0000ffff,5,[0, 2, 3, 1]),(0x3333000033330000333300003333,4,[0, 2, 3]),(0xf000f000f000f000f000f000f000f,4,[0, 1, 4]),(0x44444444444444444444444444444444,2,[4, 3, 2]),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0,2,[0, 3, 4]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,3,[1, 2, 3, 4]),(0xcc00cc00cc00cc00cc00cc00cc00cc00,2,[0, 2, 4]),(0x1111000011110000111100001111,1,[2, 3]),(0x55555555555555555555555555555555,3,[1, 2, 3, 4]),(0x22222222222222222222222222222222,2,[2, 3, 4]),(0x50505050505050505050505050505050,2,[3, 1, 4]),(0x55005500550055005500550055005500,2,[2, 1, 4]),(0xf0f00000f0f00000f0f00000f0f00000,2,[0, 1, 3]),(0x50005000500050005000500050005,1,[1, 4]),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,2,[1, 3, 4]),(0x55550000555500005555000055550000,2,[1, 2, 3]),(0xff000000ff000000ff000000ff000000,2,[0, 1, 2]),(0xaa00aa00aa00aa00aa00aa00aa00aa,2,[1, 2, 4]),(0xaaaa0000aaaa0000aaaa0000aaaa,2,[1, 2, 3]),(0x3030303030303030303030303030303,2,[0, 3, 4]),(0x2020202020202020202020202020202,1,[3, 4]),(0x220022002200220022002200220022,1,[2, 4]),(0x330033003300330033003300330033,2,[0, 2, 4]),(0xa0a00000a0a00000a0a00000a0a,1,[1, 3]),(0xf0f00000f0f00000f0f00000f0f,2,[0, 1, 3]),(0xaa000000aa000000aa000000aa,1,[1, 2]),(0xff000000ff000000ff000000ff,2,[0, 1, 2]),(0xc000c000c000c000c000c000c000c,1,[0, 4]),(0x3030000030300000303000003030,1,[0, 3]),(0x44004400440044004400440044004400,1,[2, 4]),(0x40404040404040404040404040404040,1,[3, 4])]
theorem p5_feeefaa8Y : ∀ s ∈ p5_feeefaa8Z, SliceN p5_feeefaa8R p5_feeefaa8T s := by
  unfold p5_feeefaa8Z
  simp only [List.forall_mem_cons]
  exact ⟨p5_feeefaa8S0,p5_feeefaa8S1,p5_feeefaa8S2,p5_feeefaa8S3,p5_feeefaa8S4,p5_feeefaa8S5,p5_feeefaa8S6,p5_feeefaa8S7,p5_feeefaa8S8,p5_feeefaa8S9,p5_feeefaa8S10,p5_feeefaa8S11,p5_feeefaa8S12,p5_feeefaa8S13,p5_feeefaa8S14,p5_feeefaa8S15,p5_feeefaa8S16,p5_feeefaa8S17,p5_feeefaa8S18,p5_feeefaa8S19,p5_feeefaa8S20,p5_feeefaa8S21,p5_feeefaa8S22,p5_feeefaa8S23,p5_feeefaa8S24,p5_feeefaa8S25,p5_feeefaa8S26,p5_feeefaa8S27,p5_feeefaa8S28,p5_feeefaa8S29,p5_feeefaa8S30,p5_feeefaa8S31,p5_feeefaa8S32,p5_feeefaa8S33,by simp⟩
def p5_feeefaa8D7 : List StD := dupD [
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])],[(16,18),(2,3),(1,3),(8,12),(4,5),(1,5),(4,12),(8,9),(1,9),(2,18),(16,17),(1,17),(20,22),(10,14),(24,26),(6,14),(24,28),(6,22),(20,28),(10,26)],[[0,1000,1001,1002],[1,1003,1004,1005],[2,1006,1007,1008],[3,1009,1010,1011],[0,1,1000,1012,1013],[0,2,1000,1014,1015],[0,3,1002,4,1000,1009],[1,2,1005,5,1003,1006],[1,3,1003,1016,1017],[2,3,1006,1018,1019]])]
def p5_feeefaa8D6 : List StD := dupD [
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[]),(5,[(1,0,1)]),(6,[]),(7,[]),(8,[]),(9,[]),(3,[(1,0,3)]),(4,[]),(10,[]),(5,[]),(2,[(1,0,1)]),(1,[(1,0,1)])],[(2,3),(1,5),(2,7),(1,9),(2,11),(1,17),(2,18),(16,18),(10,14),(6,14),(8,12),(4,12),(6,18),(10,18)],[[0,1000],[0],[1,2,1000,3,4,1001,1002],[1,2,1000,5,4,1003,1004],[6,2,7,4,1005,1006],[0,1007],[0,1008,1],[0,1009,1],[0,7,1006],[1,8,9,2,1001,1010],[1,8,9,2,1003,1011],[6,7,2,1005],[10,11,1001,5,3,1008],[6,1,7,3,1012,1005],[6,1,7,5,1013,1005]]),
 ([0x2222222222222222,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[]),(5,[]),(11,[]),(12,[]),(3,[]),(4,[]),(5,[(2,0,1)]),(7,[]),(9,[]),(13,[]),(14,[]),(2,[(2,0,1)]),(1,[(2,0,1)])],[(1,3),(1,5),(8,12),(1,9),(4,12),(1,17),(2,18),(2,3),(10,12),(8,14),(6,12),(4,14),(6,18),(10,18)],[[0],[0,1000],[1,2,3,1001,1002],[1,2,3,1003,1004],[4,2,5,3,1005,1006],[0,1007],[6,2,1002,7,3,1001],[6,2,1004,8,3,1003],[5,3,1005,2,1006],[0,9,1008,6,1009],[0,10,1010,6,1011],[0,5,1006],[11,12,1001,8,7,1002],[5,7,1012,6,1005],[5,8,1013,6,1005]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[(1,0,1)]),(13,[]),(7,[]),(8,[]),(5,[]),(3,[(1,0,1)]),(15,[]),(16,[]),(0,[]),(1,[]),(3,[])],[(4,5),(1,3),(4,7),(1,9),(4,12),(1,17),(2,18),(20,22),(16,18),(6,12),(8,12),(6,22),(10,18)],[[0,1,1000,2,3,1001,1002],[4,1000],[4],[4,3,1003,1,1004],[5,1,1000,6,3,1005,1006],[4,1007,0],[7,0,8,1,1001,1008],[4,2,1009,0,1003],[5,0,1001,6,2,1006,1005],[4,1010],[4,9,1004],[4,1011,5],[4,1,1003],[5,7,10,1,1005,1006],[4,6,1012,5,1003]]),
 ([0xa0a0a0a0a0a0a0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(1,[]),(0,[]),(13,[]),(17,[]),(5,[]),(3,[]),(0,[(2,0,1)]),(7,[]),(3,[(2,0,1)]),(15,[]),(6,[]),(18,[])],[(1,3),(16,18),(1,5),(1,9),(4,12),(1,17),(2,18),(4,5),(10,12),(8,12),(6,12),(6,18),(10,18)],[[0],[1,2,3,1000,1001],[0,1002],[4,3,1003,2,1004],[5,2,3,1005,1006],[6,2,1001,7,3,1000],[0,1007],[4,3,1003,2,1004],[8,2,1006,9,3,1005],[0,10,1008,6,1009],[4,7,1010,6,1003],[8,6,1000,9,7,1001],[0,4,1004],[0,11,1011,8,1009],[4,9,1012,8,1003]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffaaffaaffaaffaa,0xffff0000ffff0000],[(0,[(1,0,2)]),(14,[]),(9,[]),(8,[]),(5,[]),(3,[(1,0,2)]),(19,[]),(16,[]),(0,[]),(2,[]),(3,[])],[(8,9),(1,3),(8,11),(1,5),(8,12),(1,17),(2,18),(10,12),(24,26),(16,18),(6,18),(4,12),(10,26)],[[0,1,1000,2,3,1001,1002],[4,3,1003,1,1004],[4,1000],[4],[5,1,1000,6,3,1005,1006],[4,2,1007,0,1003],[4,1008,0],[7,0,8,1,1001,1009],[5,0,1001,6,2,1006,1005],[4,9,1004],[4,1,1003],[4,6,1010,5,1003],[4,1011],[4,1012,5],[5,7,10,1,1005,1006]]),
 ([0xaa00aa00aa00aa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(5,[]),(0,[]),(13,[]),(20,[]),(9,[]),(3,[]),(0,[(2,0,2)]),(6,[]),(3,[(2,0,2)]),(19,[]),(2,[]),(18,[])],[(1,3),(16,18),(1,5),(8,12),(1,9),(1,17),(2,18),(8,9),(10,12),(6,12),(4,12),(6,18),(10,18)],[[0],[1,2,3,1000,1001],[0,3,1002,4,1003],[0,1004],[5,2,3,1005,1006],[6,2,1001,4,3,1000],[0,3,1002,7,1003],[0,1007],[8,2,1006,9,3,1005],[0,4,1008,6,1002],[0,7,1009,6,1010],[8,6,1000,9,4,1001],[0,10,1003],[0,9,1011,8,1002],[0,11,1012,8,1010]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffaaaaffffaaaa],[(0,[(1,0,3)]),(18,[]),(4,[]),(8,[]),(5,[(1,0,2)]),(15,[]),(19,[]),(3,[]),(2,[(1,0,2)]),(1,[(1,0,2)]),(10,[]),(5,[])],[(1,3),(16,18),(8,12),(1,5),(4,12),(1,9),(16,17),(10,12),(6,12),(24,28),(20,28),(2,18)],[[0,1,2,3,1000,1001],[4,1,1002,5,3,1003],[4,1,1004,6,3,1005],[2,1006],[2],[2,5,1007,4,1000],[2,6,1008,4,1000],[2,7,1001],[2,1,1000],[8,9,1003,6,5,1002],[2,1009,4],[10,4,11,1,1003,1002],[2,1010,4],[10,4,11,1,1005,1004],[2,1011]]),
 ([0xaaaa0000aaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(3,[]),(0,[]),(13,[]),(4,[]),(21,[]),(5,[]),(18,[]),(5,[(2,0,2)]),(15,[]),(19,[]),(2,[(2,0,2)]),(1,[(2,0,2)]),(14,[])],[(1,3),(16,18),(1,5),(8,12),(1,9),(4,12),(1,17),(16,17),(10,12),(6,12),(6,18),(2,18),(10,18)],[[0],[1,2,3,4,1000,1001],[5,6,4,1002,1003],[5,2,4,1004,1005],[0,1006],[3,4,1000,2,1001],[7,6,1003,8,4,1002],[7,2,1005,9,4,1004],[0,1007],[3,2,1008,7,1000],[3,9,1009,7,1000],[0,3,1001],[10,11,1002,9,2,1003],[0,2,1010,7,1011],[0,12,1012,7,1011]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[]),(13,[]),(5,[]),(6,[]),(22,[]),(15,[]),(23,[]),(3,[(1,1,3)]),(4,[]),(1,[])],[(2,3),(4,5),(8,9),(1,17),(0,17),(6,12),(2,18),(4,12),(6,18),(1,9),(10,18)],[[0,1000,1],[2,1001,3],[4,1002,5,1000],[2,6,1002,1],[7,1,8,6,1003,1004],[0,2],[2],[0,2,1005],[0,5,1006,7],[0],[2,9,1007],[2,8,1008],[2,1,1007,4,1009],[7,4,8,1,1006,1003],[2,5,1010,7,8]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffccffccffcc,0xffff0000ffff0000],[(0,[]),(14,[]),(5,[]),(24,[]),(6,[]),(25,[]),(19,[]),(3,[(1,2,3)]),(4,[]),(2,[])],[(2,3),(1,5),(0,5),(8,9),(4,5),(1,17),(0,17),(10,12),(2,18),(8,12),(6,18),(10,18)],[[0,1000,1],[2,3,1001,1,1002],[2,1003,4],[5,1004,6,1000],[7,1,8,3,1005,1006],[0,2,1007],[0,2],[2],[0,6,1008,7],[2,9,1009],[2,1,1009,3,1001],[2,6,1010,7,8],[0],[2,8,1011],[7,3,8,1,1008,1005]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffff0f0fffff0f0],[(0,[(1,1,3)]),(4,[]),(26,[]),(13,[]),(5,[]),(18,[]),(27,[]),(19,[]),(3,[]),(1,[])],[(1,3),(0,3),(4,5),(1,9),(0,9),(16,17),(2,3),(18,20),(6,12),(16,18),(4,12),(12,20)],[[0,1,2,1000,3,1001],[4,1002,5],[4,2,1003,3,1004],[1,1005,3],[6,1006,7,1002],[1,3,1007,2,4],[1,4,1008],[1,8,1009],[1,3,1009,2,1000],[4,9,1010],[1,4],[1],[1,4,1011],[2,4,3,1010,1003],[4]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffff00ffffff00],[(0,[(1,2,3)]),(4,[]),(28,[]),(18,[]),(5,[]),(14,[]),(29,[]),(19,[]),(3,[]),(2,[])],[(1,3),(0,3),(1,5),(0,5),(8,9),(16,17),(2,3),(10,12),(18,24),(16,18),(8,12),(12,24)],[[0,1,2,1000,3,1001],[4,2,1002,3,1003],[4,1004,3],[1,1005,5],[6,1006,7,1004],[1,4,1007],[1,4,1008],[1,8,1009],[1,3,1009,2,1000],[2,4,9,1010],[1,4,1011],[2,4,3,1010,1002],[1,4],[1],[4]])]
def p5_feeefaa8D5 : List StD := dupD [
 ([0x2222222222222222,0xaaaaaaaaaaaaaaaa,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[]),(5,[(1,0,1)]),(24,[]),(18,[]),(23,[]),(3,[(1,0,3)]),(14,[]),(5,[(2,0,1)]),(13,[]),(3,[(2,0,3)])],[],[[0],[0],[1,2,3],[1,4,3],[5,2,6],[0],[3,2],[3,4],[6,2],[7,2,8],[7,4,6],[9,2,3],[2,6],[4,3,8],[2,3,6]]),
 ([0xaaaaaaaaaaaaaaaa,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[]),(5,[(1,0,1)]),(7,[]),(8,[]),(23,[]),(13,[]),(3,[(1,1,3)]),(15,[]),(9,[])],[(9,10),(4,12)],[[0],[1,2],[1000,2,3],[1,4,5],[5,4],[1,5],[1,5],[1,2,1001],[6,2,7],[0],[4,2],[1,2],[1,2,4],[4,2],[1,8]]),
 ([0xaaaaaaaaaaaaaaaa,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffccffccffccffcc,0xffff0000ffff0000],[(0,[]),(5,[(1,0,1)]),(7,[]),(9,[]),(8,[]),(14,[]),(24,[]),(3,[(1,2,3)]),(19,[])],[(5,6),(8,12)],[[0],[1,2],[1,3],[1000,2,4],[5,6],[1,3,1001],[1,2,5],[1,5],[7,2,8],[6,2,3],[1,3,6],[1,2],[0],[1,3],[6,2]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfefefefefefefefe,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[(1,0,1)]),(5,[(1,0,1)]),(13,[]),(7,[]),(0,[(3,0,1)]),(8,[]),(5,[(2,0,1)]),(0,[(2,0,1)]),(24,[]),(9,[]),(3,[])],[],[[0,1,2],[1,0,3],[4],[1,5,2],[2,5],[0,2,1],[6],[0,3],[0,3],[7],[8,2,9],[1,2],[1,2],[10,2],[1,9]]),
 ([0xe0e0e0e0e0e0e0e,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[(2,0,1)]),(0,[(0,0,1)]),(5,[(1,0,1)]),(5,[(2,0,1)]),(0,[(1,0,1)]),(23,[]),(13,[]),(7,[]),(15,[]),(4,[(2,0,1)])],[],[[0,1],[0,2,3],[4],[2,5,6],[6,5],[0,2,6],[2,7],[2,5,6],[6,5],[0,6,2],[0,7],[0,7],[5,6],[2,6],[2,8,9]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffeeffeeffeeffee,0xffff0000ffff0000],[(0,[(1,0,2)]),(5,[(1,0,1)]),(7,[]),(9,[]),(0,[(3,0,2)]),(4,[(1,0,2)]),(23,[]),(14,[]),(5,[(2,0,1)]),(0,[(2,0,2)])],[],[[0,1,2],[1,2],[1,0,3],[4],[5,6,7],[0,3],[0,2],[8],[0,2],[6,2],[1,3],[1,2],[9],[1,3],[5,2]]),
 ([0xee00ee00ee00ee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[(2,0,2)]),(0,[(0,0,2)]),(5,[(1,0,1)]),(5,[(2,0,1)]),(24,[]),(9,[]),(0,[(1,0,2)]),(14,[]),(19,[]),(4,[(2,0,2)])],[],[[0,1],[0,2,3],[2,4,5],[6],[5,4],[0,2,5],[2,4,7],[2,5],[7,4],[0,5],[0,7,2],[0,5],[4,5],[2,8,9],[2,5]]),
 ([0xeeee0000eeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xeeeeeeeeeeeeeeee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00],[(0,[(2,0,3)]),(0,[(0,0,3)]),(9,[]),(5,[(1,0,1)]),(7,[]),(6,[]),(24,[]),(23,[]),(18,[]),(10,[])],[],[[0,1],[0,2],[1],[3,4],[3,2],[0,2],[0],[5,4,6],[5,2,7],[8],[0,2],[0,4],[9,2],[9,4],[6,2]]),
 ([0xeeee0000eeee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00],[(0,[(2,0,3)]),(0,[(0,0,3)]),(4,[]),(21,[]),(18,[]),(14,[]),(5,[]),(7,[]),(30,[]),(9,[]),(15,[]),(26,[]),(19,[]),(20,[])],[(1,3),(1,5),(8,12),(1,9),(4,12),(2,3),(10,14),(6,14)],[[0,1,2],[0,3,1000,4,5],[6,4,7,3,1001,1002],[6,4,5,3,1003,1004],[0,3,1000,4,1005],[8,4,1002,7,3,1001],[8,4,1004,9,3,1003],[0,10,1006,11],[0,12,1007,13],[13,11,1001,9,7,1002]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xf2f2f2f2f2f2f2f2,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[(1,0,1)]),(7,[]),(5,[(2,0,1)]),(23,[]),(13,[]),(0,[(2,0,1)]),(4,[]),(30,[]),(15,[]),(4,[(1,0,1)])],[],[[0,1],[2,0,1],[0,2],[2,3,4],[4,3],[0,4,2],[0,4,2],[0,1],[0,1],[5],[3,1],[2,1],[2,1],[6,1,7],[2,8,9]]),
 ([0x202020202020202,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[(0,0,1)]),(5,[(1,0,1)]),(0,[(1,0,1)]),(23,[]),(7,[]),(0,[(2,0,1)]),(5,[(2,0,1)]),(9,[]),(4,[(2,0,1)]),(15,[])],[],[[0],[1],[2],[1,3,4],[4,3],[5,4],[6,4],[6,3,7],[8,3,9],[5,7],[3,4],[3,4],[3,4],[3,4],[6,7]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff22ff22ff22ff22,0xffff0000ffff0000],[(0,[(1,0,2)]),(9,[]),(5,[(2,0,1)]),(24,[]),(14,[]),(19,[]),(4,[(1,0,2)]),(0,[(2,0,2)]),(30,[])],[],[[0,1],[2,3,4],[2,0,1],[0,2],[4,3],[0,1],[0,4,2],[0,4,2],[0,1],[3,1],[2,1],[2,5,6],[7],[2,1],[6,1,8]]),
 ([0x22002200220022,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[(0,0,2)]),(5,[(1,0,1)]),(24,[]),(9,[]),(0,[(1,0,2)]),(0,[(2,0,2)]),(5,[(2,0,1)]),(14,[]),(19,[]),(4,[(2,0,2)])],[],[[0],[1],[1,2,3],[4],[3,2],[5,3],[6,2,7],[6,3],[7,2],[2,3],[5,7,6],[2,3],[2,3],[6,8,9],[2,3]]),
 ([0xa0a0a0a0a0a0a0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000],[(5,[]),(0,[(1,0,1)]),(26,[]),(14,[]),(15,[]),(23,[]),(18,[]),(0,[(2,0,1)]),(6,[]),(4,[(2,0,1)])],[],[[0],[1,2,3],[0],[0,2,4],[3,5],[3,2],[0],[0,2,6],[3,4,5],[7,2,8],[0,3],[2,4],[0,2,3],[9,5,6],[0,3]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafafafafafafafa,0xfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[(1,0,1)]),(7,[]),(0,[(3,0,1)]),(24,[]),(5,[]),(23,[]),(6,[]),(9,[]),(4,[]),(15,[]),(4,[(1,0,1)])],[(17,20),(2,18)],[[0,1],[2],[1000,1,3],[4,5,6],[6,3],[0,6],[4],[0,1],[0,1],[0,6],[4,1,7],[8,1,1001],[3,1,5],[5,1],[3,9,10]]),
 ([0x3232323232323232,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[]),(0,[(1,0,1)]),(0,[(3,0,1)]),(5,[(1,0,1)]),(0,[(2,0,1)]),(23,[]),(6,[]),(9,[]),(5,[(2,0,1)]),(24,[]),(7,[])],[],[[0,1,2],[3],[0,1,4],[3,5,6],[6,5],[1,7],[6,1,8],[6,5],[6,5],[1,6],[1,6],[1,6],[5,7,9],[5,10],[8,7]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafafafafafafafa,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffff0f0fffff0f0],[(4,[(1,0,1)]),(7,[]),(5,[]),(26,[]),(18,[]),(15,[]),(24,[]),(19,[])],[(3,6),(16,18)],[[0,1],[2],[2,3,4],[0,5],[1000,1,6],[0,3,1001],[0,1],[3,1,4],[0,4,3],[2,1,7],[0,1,4],[0,4],[0,4],[2,1,3],[2]]),
 ([0xfa00fa00fa00fa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfafafafafafafafa,0xffff0000ffff0000],[(5,[]),(0,[(1,0,1)]),(7,[]),(4,[(1,0,1)]),(24,[]),(15,[]),(13,[]),(26,[]),(16,[]),(14,[])],[],[[0],[1,2],[0,2],[0],[3,4,5],[6,2,7],[0,2],[0],[6,4],[0,5],[8,5],[4,2],[9],[0,2],[8,2]]),
 ([0xfa00fa00fa00fa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000],[(0,[(2,0,2)]),(5,[]),(14,[]),(7,[]),(20,[]),(18,[]),(4,[]),(31,[]),(15,[]),(9,[]),(24,[]),(26,[]),(19,[]),(21,[])],[(1,3),(6,12),(1,5),(1,17),(2,18),(4,5),(4,7),(2,12),(12,16)],[[0,1],[0,2,3,4,1000,1001],[1,4,1002,2,5],[6,2,5,4,1003,1004],[7,2,1005,3,4,1000,1006],[1,4,1002,2,1005],[7,2,1004,8,4,1003],[1,9,1007,10,1002],[11,10,1000,8,3,1004,1003],[1,12,1008,13,1002]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xfffffafafffffafa],[(4,[(1,0,1)]),(26,[]),(7,[]),(5,[(1,0,2)]),(19,[]),(5,[(3,0,2)]),(15,[]),(4,[(2,0,1)]),(5,[(2,0,2)])],[],[[0,1,2],[3,0,2],[3,1,4],[0,3,4],[5],[0,6,1],[0,2],[1,2,4],[0,1],[1,2],[0,2,3],[7],[0,6],[3,1],[8]]),
 ([0xfafa0000fafa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[(2,0,3)]),(5,[]),(0,[(0,0,3)]),(26,[]),(15,[]),(4,[(1,0,1)]),(4,[(2,0,1)]),(5,[(1,0,2)]),(18,[]),(5,[(2,0,2)]),(19,[])],[],[[0,1,2],[0,3,4],[1,5,6],[1,3,4],[7],[5,3,8],[8,4,9],[8,3],[5,4],[3,4],[5,10,9],[3,4],[3,4],[5,8],[3,4]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xcececececececece,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[(2,0,1)]),(5,[(1,0,1)]),(7,[]),(26,[]),(9,[]),(4,[(2,0,1)]),(23,[]),(6,[]),(5,[(2,0,1)]),(10,[])],[],[[0,1,2],[0,1],[1,2],[1,3,4],[5,6,7],[8],[0,4],[0,2],[0,2],[0,4],[1,2,9],[5,2],[3,2],[1,2],[1,4]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffff0a0affff0a0a],[(4,[(2,0,1)]),(26,[]),(18,[]),(15,[]),(5,[(1,0,2)]),(19,[]),(10,[]),(5,[(2,0,2)])],[],[[0,1,2],[2,3,4],[2,1],[0,3],[0,3],[0,3,1],[0,5,4],[1,2],[0,1],[1,3],[0,2],[0,2],[0,2],[4,1,6],[7]]),
 ([0xa0a00000a0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(5,[(0,0,2)]),(0,[]),(26,[]),(19,[]),(4,[(1,0,1)]),(10,[]),(5,[(1,0,2)]),(4,[(2,0,1)]),(18,[]),(15,[]),(5,[(2,0,2)])],[],[[0],[1,2,3],[4],[0,2,5],[6],[7,2,8],[5,9,10],[5,2],[7,3],[2,9],[5,3,10],[2,3],[2,3,9],[5,3],[2,8]]),
 ([0xaa00aa00aa00aa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffaaffaaffaaffaa,0xffff0000ffff0000],[(5,[]),(0,[(1,0,2)]),(20,[]),(18,[]),(4,[(1,0,2)]),(9,[]),(6,[]),(10,[]),(26,[]),(13,[])],[],[[0],[1,2,3],[0,2,3],[0],[4,2,5],[3,2],[0,2,3],[0],[6,2],[0,5,7],[7,2,6],[8,3],[0,2,9],[0,3,7],[7,2,3]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffaaffaaffaaffaa,0xffccffccffccffcc,0xffff0000ffff0000],[(0,[(1,0,2)]),(9,[]),(5,[]),(24,[]),(6,[]),(26,[]),(7,[]),(19,[]),(4,[(1,0,2)])],[(17,24),(2,18)],[[0,1],[2,3,4],[2],[1000,1,5],[4,3],[0,1],[0,4],[2],[0,1],[2,1,6],[2,1,3],[2,7,8],[0,4],[8,1,1001],[3,1]]),
 ([0x3322332233223322,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[]),(0,[(1,0,2)]),(0,[(3,0,2)]),(26,[]),(5,[]),(24,[]),(9,[]),(0,[(2,0,2)]),(5,[(2,0,1)]),(6,[]),(7,[])],[],[[0,1,2],[3],[4,5,6],[0,1,7],[6,5],[1,6],[8,5,9],[8,1,6],[9,5],[1,6],[1,9],[1,6],[5,6],[8,10],[5,6]]),
 ([0xf0a0f0a0f0a0f0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffaaffaaffaaffaa,0xffff0000ffff0000],[(5,[]),(0,[(1,0,2)]),(9,[]),(4,[(1,0,2)]),(19,[]),(14,[]),(26,[]),(24,[]),(16,[]),(13,[])],[],[[0],[1,2],[0,2],[0],[3,4],[5,2,6],[0,2],[0],[5,4,7],[0,4],[8,4],[6,2,4],[9],[0,2],[8,2]]),
 ([0xf0a0f0a0f0a0f0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[(2,0,1)]),(5,[]),(13,[]),(9,[]),(26,[]),(6,[]),(4,[]),(19,[]),(23,[]),(31,[]),(7,[]),(15,[])],[(1,3),(10,12),(1,9),(1,17),(2,18),(0,5),(0,7),(8,9),(2,12),(12,16)],[[0,1],[0,2,3,4,1000,1001],[1,4,1002,2,5],[6,2,7,8,1003,1004],[9,2,1005,3,4,1000,1006],[1,4,1002,2,1007],[9,2,1004,7,8,1003],[1,10,1008,8,1002],[4,8,1000,7,3,1004,1003],[1,11,1009,4,1002]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffaaffaaffaaffaa,0xffff0000ffff0000,0xffffff00ffffff00],[(4,[(1,0,2)]),(26,[]),(9,[]),(5,[]),(21,[]),(14,[]),(19,[]),(28,[]),(15,[])],[(3,10),(16,18)],[[0,1,2],[3,4,5],[3],[0,6],[1000,2,1],[0,2],[0,1,1001],[1,2,6],[0,5,7],[3,2,8],[0,6],[1,2,7],[0,2,8],[0,8],[3]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffaaffffffaa],[(4,[(1,0,2)]),(26,[]),(9,[]),(5,[(1,0,2)]),(15,[]),(5,[(3,0,2)]),(19,[]),(4,[(2,0,2)]),(5,[(2,0,2)])],[],[[0,1,2],[3,4],[3,0,2],[0,3,4],[5],[0,2],[0,6,3],[1,2,4],[0,1],[1,2,4],[0,6],[3,2],[0,2,3],[7],[8]]),
 ([0xffaa0000ffaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[(2,0,3)]),(5,[]),(0,[(0,0,3)]),(26,[]),(19,[]),(21,[]),(4,[(2,0,2)]),(5,[(1,0,2)]),(4,[(1,0,2)]),(16,[]),(5,[(2,0,2)]),(15,[])],[],[[0,1,2],[0,3,4],[1,5,4],[1,3,6],[7],[8,3,9],[10,5,11],[10,3,4],[8,4],[3,11],[8,4,9],[3,4],[3,4,11],[5,4],[3,11]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xcceecceecceeccee,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[(2,0,2)]),(5,[(1,0,1)]),(9,[]),(7,[]),(4,[(2,0,2)]),(24,[]),(6,[]),(5,[(2,0,1)]),(10,[])],[],[[0,1,2],[0,1],[1,3],[1,2],[4,5,6],[7],[0,2],[0,3],[0,2],[1,2,8],[0,3],[4,2],[5,2],[1,3],[1,2]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffff00aaffff00aa],[(4,[(2,0,2)]),(28,[]),(18,[]),(19,[]),(5,[(1,0,2)]),(15,[]),(10,[]),(5,[(2,0,2)])],[],[[0,1,2],[2,1],[2,3,4],[0,3],[0,3],[0,5,4],[0,3,1],[1,2],[0,1],[1,3],[0,2],[4,1,6],[0,2],[0,2],[7]]),
 ([0xaa000000aa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(5,[(0,0,2)]),(0,[]),(28,[]),(15,[]),(19,[]),(4,[(1,0,2)]),(5,[(1,0,2)]),(4,[(2,0,2)]),(9,[]),(5,[(2,0,2)])],[],[[0],[1,2,3],[0,2,4],[5],[6],[7,2,8],[9,2,3],[9,4],[7,3],[7,3,8],[2,4],[2,3],[2,3,4],[2,4],[7,3]]),
 ([0xaaaa0000aaaa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa],[(4,[]),(28,[]),(19,[]),(5,[(1,0,2)]),(26,[]),(15,[]),(18,[]),(6,[]),(5,[(2,0,2)]),(10,[])],[],[[0],[0,1,2],[2,1],[3,4,5],[0],[0,1,6],[6,1],[6,2,4],[0],[0,5,4],[0,2,1],[0,1,7],[1,2],[8,1,9],[8,4,9]]),
 ([0x3333222233332222,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffaaaaffffaaaa],[(4,[]),(5,[(1,0,2)]),(15,[]),(19,[]),(10,[]),(28,[]),(26,[]),(6,[])],[],[[0],[1,2],[1,3],[0,2],[0],[4,2,5],[4,3,6],[0,2],[0],[5,2,3],[0,3],[4,3],[0,2],[4,2],[7]]),
 ([0x3333222233332222,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[]),(4,[]),(5,[]),(10,[]),(15,[]),(24,[]),(19,[]),(23,[]),(6,[]),(16,[]),(30,[]),(7,[]),(9,[])],[(1,5),(8,12),(1,9),(4,12),(1,17),(16,17),(4,18),(8,18)],[[0,1],[2,3,4,5,1000,1001],[2,3,6,7,1002,1003],[0,1,5,1004,8,9],[10,3,1001,4,5,1000],[10,3,1003,6,7,1002],[1,5,1004,8,1005],[5,7,1000,6,4,1001],[1,11,1006,7,1004],[1,12,1007,5,1004]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xfffff0f0fffff0f0],[(4,[]),(26,[]),(18,[]),(15,[]),(5,[(1,0,2)]),(24,[]),(19,[]),(7,[])],[(9,24),(4,12)],[[0,1,2],[2,3,4],[2,1],[0],[1000,3,5],[0,3,1],[0,6,4],[0,1,7],[0,2,1],[1,3],[4,2,7],[0],[4,1,1001],[1,2],[4,7]]),
 ([0xf0f0a0a0f0f0a0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[(2,0,1)]),(5,[(1,0,2)]),(5,[(3,0,2)]),(26,[]),(15,[]),(19,[]),(5,[(2,0,2)]),(4,[(2,0,1)]),(7,[]),(10,[])],[],[[0,1,2],[0,3,4],[5],[1,3,4],[1,6],[7,3,8],[1,4],[1,3,9],[7,1,4],[1,4],[1,8,7],[3,4],[3,4],[1,8],[1,4,3]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaaaaffffaaaa,0xffffff00ffffff00],[(4,[]),(28,[]),(18,[]),(19,[]),(5,[(1,0,2)]),(24,[]),(15,[]),(9,[])],[(5,20),(8,12)],[[0,1,2],[2,1],[2,3,4],[0],[1000,3,5],[0,6,4],[0,3,1],[0,1,7],[0,2,1],[1,3],[4,1,1001],[1,2],[4,2,7],[0],[4,7]]),
 ([0xff00aa00ff00aa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[(2,0,2)]),(5,[(1,0,2)]),(5,[(3,0,2)]),(28,[]),(19,[]),(4,[(1,0,2)]),(5,[(2,0,2)]),(4,[(2,0,2)]),(9,[]),(10,[])],[],[[0,1,2],[0,3,4],[1,3,4],[5],[1,6],[7,3,8],[1,3,9],[1,4],[7,1,4],[1,8,7],[1,4],[3,4],[3,4],[1,4,3],[1,8]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xf0f0fafaf0f0fafa,0xff00ff00ff00ff00,0xffff0000ffff0000],[(4,[(1,0,1)]),(28,[]),(7,[]),(5,[(2,0,2)]),(26,[]),(13,[]),(15,[]),(16,[]),(4,[(2,0,1)])],[],[[0,1,2],[3,0,2],[0,3],[3,4,5],[0,6],[0,5,3],[0,1,7],[0,2],[1,2,6],[8],[1,2,4],[0,2,3],[3,2],[0,2,3],[0,6]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xff00ffaaff00ffaa,0xffff0000ffff0000],[(4,[(1,0,2)]),(28,[]),(16,[]),(5,[(2,0,2)]),(14,[]),(9,[]),(19,[]),(4,[(2,0,2)])],[],[[0,1,2],[3,1,4],[3,0,5],[0,3],[0,6],[0,5],[0,4,1],[0,1,2],[1,5,6],[1,4],[3,1],[0,6],[7],[0,4,2],[0,4,2]]),
 ([0xa8a8a8a8a8a8a8a8,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[(2,0,1)]),(5,[]),(10,[]),(4,[]),(16,[]),(0,[(0,0,1)]),(5,[(0,0,1)]),(23,[]),(13,[]),(14,[]),(18,[]),(6,[])],[(9,10),(17,20)],[[0],[0,1],[1,0],[1,2],[3,4],[4,1000,5],[2,1001,6],[2,7],[4,7],[2,8,4],[2,9,4],[5,10,11],[7,8],[2,8,4],[2,9,4]]),
 ([0x5454545454545454,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[(1,0,1)]),(5,[]),(6,[]),(23,[]),(0,[(3,0,1)]),(28,[]),(13,[]),(4,[(3,0,1)]),(32,[]),(5,[(3,0,1)])],[],[[0],[0,1],[1,0],[1,2,3],[3,2],[4,5,6],[2,5],[2,3],[2,3],[4,2],[3,2],[3,2],[3,6],[3,6],[7,8,9]]),
 ([0xaa88aa88aa88aa88,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[(2,0,2)]),(5,[]),(6,[]),(4,[]),(0,[(0,0,2)]),(16,[]),(24,[]),(5,[(0,0,1)]),(13,[]),(14,[])],[(5,6),(17,24)],[[0],[0,1],[1,2],[1,0],[2,3],[4,1000,5],[2,6],[2,1001,7],[2,6],[4,2],[4,2],[4,2],[6,8,9],[5,8],[5,9]]),
 ([0x5544554455445544,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[(1,0,2)]),(5,[]),(14,[]),(28,[]),(4,[]),(23,[]),(5,[(3,0,1)]),(6,[]),(0,[(3,0,2)]),(33,[])],[],[[0],[0,1],[1,2,3],[1,0],[4,2,5],[2,3],[2,3],[6,5,7],[2,5],[6,7,8],[3,2],[3,7,5],[3,2],[3,9,5],[6,2]]),
 ([0xaaaaa0a0aaaaa0a0,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(5,[(2,0,2)]),(0,[]),(14,[]),(4,[]),(6,[]),(26,[]),(5,[(0,0,2)]),(4,[(0,0,1)]),(18,[]),(13,[])],[(3,6),(9,24)],[[0],[1,2],[0,3],[0,4],[2,0,3],[2,5],[2,1000,6],[4,5],[2,1001,7],[5,4,7],[6,2],[5,4,8],[5,2,9],[6,8,7],[5,2,6]]),
 ([0x5555505055555050,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(5,[(1,0,2)]),(0,[]),(13,[]),(28,[]),(4,[]),(23,[]),(5,[(3,0,2)]),(18,[]),(33,[]),(4,[(3,0,1)])],[],[[0],[1,2,3],[0,4],[0,2,5],[4,0],[2,3],[6,3,7],[2,5],[2,5],[6,2],[3,8,5],[3,7],[3,2,5],[3,2,5],[6,7,9]]),
 ([0xaaaaaa00aaaaaa00,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(4,[(2,0,2)]),(18,[]),(5,[]),(28,[]),(5,[(0,0,2)]),(13,[]),(4,[(0,0,2)]),(6,[]),(14,[])],[(3,10),(5,20)],[[0],[0,1],[1,2],[1,0,2],[0,2],[1,3],[1,3],[1,1000,4],[4,1001,5,6],[4,5],[3,7,6],[3,1],[3,5,8],[3,1],[4,1,6]]),
 ([0x5555550055555500,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(5,[(1,0,2)]),(0,[]),(14,[]),(28,[]),(4,[]),(5,[(3,0,2)]),(23,[]),(18,[]),(32,[]),(4,[(3,0,2)])],[],[[0],[1,2,3],[0,2,3],[0,4],[4,0],[2,3],[2,3],[5,6,7],[2,6],[5,8,9],[3,2],[3,7],[3,2],[3,7],[5,2]])]
def p5_feeefaa8D4 : List StD := dupD [
 ([0xfe00fe00fe00fe,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000],[(0,[(2,0,2)]),(5,[(1,0,1)]),(5,[(3,0,1)]),(5,[(2,0,1)]),(28,[]),(14,[]),(18,[]),(4,[]),(23,[]),(6,[]),(13,[])],[],[[0,1,2],[0,1,3],[1,4,5],[5,6,7],[5,1,4],[1,4,5],[5,8],[1,9,10],[4,9,8],[1,10]]),
 ([0xfefe0000fefe,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00],[(0,[(2,0,3)]),(4,[(1,0,1)]),(4,[(3,0,1)]),(6,[]),(4,[(2,0,1)]),(5,[]),(14,[]),(5,[(1,0,1),(3,2,3)]),(13,[]),(23,[])],[],[[0,1,2],[0,3],[1,4],[5,6],[1,7,8],[3,1,7],[3,9],[1,3],[1,3],[9,8]]),
 ([0xf0e0f0e0f0e0f0e,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[(2,0,1)]),(5,[(1,0,1)]),(5,[(3,0,1)]),(5,[(2,0,1)]),(23,[]),(13,[]),(28,[]),(14,[]),(6,[])],[],[[0,1,2],[0,1,3],[1,4,5],[5,4],[5,1,6],[1,4,5],[5,4],[1,7],[4,8],[1,7]]),
 ([0xffee0000ffee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00],[(0,[(2,0,3)]),(23,[]),(0,[(0,0,3)]),(6,[]),(13,[]),(0,[(2,2,3)]),(14,[]),(0,[(0,2,3)]),(5,[(1,0,1),(3,2,3)]),(28,[]),(4,[(1,0,2)])],[],[[0,1,2],[0,3],[1,4],[5,6,7],[6,8,9],[3,9],[3,1],[8,3,10],[1,3],[1,6,9]]),
 ([0xf200f200f200f2,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000],[(0,[(2,0,2)]),(5,[]),(0,[(0,0,2)]),(6,[]),(4,[]),(18,[]),(14,[]),(9,[]),(31,[]),(5,[(2,0,1)]),(23,[]),(13,[])],[],[[0,1,2],[0,3],[1,3],[4,5],[6,7,8],[6,8,9],[6,10],[9,7,11],[10,7],[9,11]]),
 ([0xf020f020f020f02,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[(2,0,1)]),(5,[]),(0,[(0,0,1)]),(5,[(1,0,1)]),(5,[(2,0,1)]),(6,[]),(4,[]),(23,[]),(13,[]),(9,[]),(31,[]),(14,[])],[],[[0,1,2],[0,3,4],[1,5],[6,7,8],[8,9,10],[4,7,8],[8,7],[4,11],[7,9],[4,9]]),
 ([0x3333323233333232,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[]),(31,[]),(9,[]),(13,[]),(6,[]),(23,[]),(28,[]),(18,[])],[],[[0,1,2],[0,3],[4,1],[0,5,2],[4,1,6],[3,2,5],[1,5,3],[5,1],[5,3],[1,2,7]]),
 ([0xff00fa00ff00fa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000],[(0,[(2,0,2)]),(23,[]),(0,[(0,0,2)]),(6,[]),(13,[]),(0,[(3,2,3)]),(18,[]),(0,[(0,2,3)]),(9,[]),(28,[]),(5,[(1,0,2)])],[],[[0,1,2],[0,3],[1,4],[5,6,7],[4,8,9],[6,9],[4,1],[10,4],[1,6,8],[1,4]]),
 ([0xcece0000cece,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00],[(13,[]),(0,[]),(18,[]),(9,[]),(5,[]),(31,[]),(30,[]),(4,[(2,0,1)]),(6,[]),(23,[])],[],[[0,1],[1,0],[1,0],[2,3,4],[2,3,5],[2,5,6],[2,3,6],[7,3],[5,8],[9,3,5]]),
 ([0x3333020233330202,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(9,[]),(0,[(1,0,3)]),(5,[(0,0,1)]),(13,[]),(23,[]),(6,[]),(31,[]),(30,[]),(18,[]),(4,[(2,0,1)])],[],[[0,1,2],[0,3,2],[2,4,5],[0,3,1],[5,6,7],[5,0,4],[5,4],[4,0,6],[4,8,9],[6,0,7]]),
 ([0x3333332233333322,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[]),(4,[(1,0,2)]),(4,[(3,0,2)]),(6,[]),(13,[]),(5,[]),(18,[]),(28,[]),(23,[]),(9,[])],[],[[0,1,2],[3,4,5],[0,1,3],[0,6],[3,7],[3,1,8],[1,8,3],[7,9],[1,6],[1,6]]),
 ([0xf0f0f0a0f0f0f0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[(2,0,1)]),(28,[]),(0,[(0,0,1)]),(6,[]),(23,[]),(13,[]),(14,[]),(18,[]),(5,[(1,0,2)])],[],[[0,1,2],[0,3],[1,4,5],[1,4,5],[5,1],[5,4],[5,4],[1,6],[1,7],[8,6]]),
 ([0xccee0000ccee,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00],[(13,[]),(0,[]),(18,[]),(5,[]),(14,[]),(5,[(1,0,1),(3,2,3)]),(28,[]),(9,[]),(4,[(2,0,2)]),(6,[])],[],[[0,1],[1,0],[2,0,3],[1,4],[2,5,6],[2,6],[2,7,5],[5,7,8],[5,9,8],[6,7]]),
 ([0x3333002233330022,0xaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(18,[]),(0,[(1,0,3)]),(0,[(3,0,3)]),(5,[]),(13,[]),(4,[(1,0,2)]),(4,[(2,0,2)]),(28,[]),(9,[]),(30,[]),(5,[(1,0,2),(3,1,3)]),(6,[])],[],[[0,1,2],[3,4],[3,5,6],[1,0],[0,7],[0,8,9],[6,10,11],[7,8],[6,0],[6,0]]),
 ([0xf000fa00f000fa,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffff0000ffff0000],[(4,[(2,0,2)]),(5,[]),(5,[(0,0,2)]),(28,[]),(6,[]),(5,[(1,0,2)]),(5,[(2,0,2)]),(13,[]),(14,[]),(19,[]),(31,[])],[],[[0,1,2],[0,3,4],[1,3,4],[0,5,6],[7,3],[6,3,8],[7,9,10],[6,7],[3,9],[3,7,6]]),
 ([0xf000f0a0f000f0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xff00ff00ff00ff00,0xffff0000ffff0000],[(5,[(2,0,2)]),(5,[(0,0,2)]),(0,[]),(6,[]),(5,[(1,0,2)]),(14,[]),(28,[]),(4,[(1,0,2),(3,1,3)]),(13,[]),(19,[])],[],[[0,1],[2,3],[0,3],[0,4],[5,6],[0,7,8],[5,9,7],[0,5],[6,9],[0,5]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffa8ffa8ffa8ffa8,0xffff0000ffff0000],[(13,[]),(9,[]),(22,[]),(6,[]),(0,[(3,0,2)]),(19,[]),(23,[]),(5,[(0,0,1)]),(4,[]),(18,[])],[(17,20)],[[0,1,2],[2,1000,3],[0,1,4],[0,5,6],[7,0],[2,3],[2,1],[2,0],[2,0],[8,1,9]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffa8a8ffffa8a8],[(13,[]),(4,[(0,0,1)]),(15,[]),(22,[]),(19,[]),(23,[]),(6,[]),(5,[]),(9,[])],[(9,10)],[[0,1000,1],[1,2,3],[0,4,5],[0,1],[1,0,6],[1,4,6],[1,2,6],[3,0],[1,3],[7,2,8]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfaf8faf8faf8faf8,0xff00ff00ff00ff00,0xffff0000ffff0000],[(13,[]),(7,[]),(31,[]),(6,[]),(0,[(3,0,1)]),(5,[(0,0,1)]),(15,[]),(24,[]),(0,[(2,1,2)]),(4,[]),(19,[])],[(17,24)],[[0,1,2],[3,1,4],[0,1000,5],[0,6,2],[4,0,3],[2,1],[7,1],[5,0,8],[9,0,10],[2,6]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffffaa88ffffaa88],[(5,[(0,0,1),(1,2,3)]),(13,[]),(4,[(0,0,2)]),(15,[]),(19,[]),(5,[(3,1,2)]),(24,[])],[(5,6)],[[0,1000,1,2],[0,3],[0,4],[1,2],[0,1],[0,4],[2,3,5],[6,1,4],[0,1],[0,2]]),
 ([0xaaaaaaaaaaaaaaaa,0xeeeeececeeeeecec,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(13,[]),(0,[]),(4,[(0,0,1)]),(7,[]),(30,[]),(9,[]),(5,[]),(19,[]),(26,[])],[(9,24)],[[0,1],[2,3,4],[0,5,4],[0,1000,2],[2,5],[6,3,7],[2,3,7],[8,0],[2,0,4],[2,5,4]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xffaaffa0ffaaffa0,0xffff0000ffff0000],[(13,[]),(9,[]),(26,[]),(5,[(0,0,2)]),(6,[]),(19,[]),(27,[]),(0,[])],[(3,6)],[[0,1,2],[3,1000,4],[0,1,2],[0,5,6],[2,0],[7,4],[2,1,5],[2,0],[3,0],[2,1,3]]),
 ([0xaaaaaaaaaaaaaaaa,0xeeeeeecceeeeeecc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(13,[]),(0,[]),(6,[]),(7,[]),(30,[]),(9,[]),(4,[(0,0,2)]),(5,[]),(5,[(2,1,2)]),(28,[])],[(5,20)],[[0,1],[2,3,4],[0,5,4],[0,1000,6],[7,0],[6,2],[6,2,8],[9,0,5],[4,0],[4,5]]),
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xfafafaf0fafafaf0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(13,[]),(7,[]),(28,[]),(5,[(0,0,2)]),(15,[]),(31,[]),(0,[]),(9,[])],[(3,10)],[[0,1,2],[3,1],[0,1000,3],[0,4,5],[6,0,7],[2,1,5],[2,1,4],[2,0,7],[2,0,3],[3,4,5]])]
def p5_feeefaa8D3 : List StD := []
theorem p5_feeefaa8I3 : LevelN p5_feeefaa8R p5_feeefaa8T 3 p5_feeefaa8D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_feeefaa8C4x0 : levelOK p5_feeefaa8T p5_feeefaa8Z 3 (p5_feeefaa8D3.map Prod.fst) ((p5_feeefaa8D4.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_feeefaa8C4x1 : levelOK p5_feeefaa8T p5_feeefaa8Z 3 (p5_feeefaa8D3.map Prod.fst) ((p5_feeefaa8D4.drop (1*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_feeefaa8C4x2 : levelOK p5_feeefaa8T p5_feeefaa8Z 3 (p5_feeefaa8D3.map Prod.fst) ((p5_feeefaa8D4.drop (2*8)).take 8) = true := by decide +kernel
theorem p5_feeefaa8I4 : LevelN p5_feeefaa8R p5_feeefaa8T 4 p5_feeefaa8D4 := levelStep p5_feeefaa8B p5_feeefaa8Y p5_feeefaa8I3 (chunks 8 p5_feeefaa8D4 3 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_feeefaa8C4x0
  · exact p5_feeefaa8C4x1
  · exact p5_feeefaa8C4x2
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_feeefaa8C5x0 : levelOK p5_feeefaa8T p5_feeefaa8Z 4 (p5_feeefaa8D4.map Prod.fst) ((p5_feeefaa8D5.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_feeefaa8C5x1 : levelOK p5_feeefaa8T p5_feeefaa8Z 4 (p5_feeefaa8D4.map Prod.fst) ((p5_feeefaa8D5.drop (1*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_feeefaa8C5x2 : levelOK p5_feeefaa8T p5_feeefaa8Z 4 (p5_feeefaa8D4.map Prod.fst) ((p5_feeefaa8D5.drop (2*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_feeefaa8C5x3 : levelOK p5_feeefaa8T p5_feeefaa8Z 4 (p5_feeefaa8D4.map Prod.fst) ((p5_feeefaa8D5.drop (3*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_feeefaa8C5x4 : levelOK p5_feeefaa8T p5_feeefaa8Z 4 (p5_feeefaa8D4.map Prod.fst) ((p5_feeefaa8D5.drop (4*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_feeefaa8C5x5 : levelOK p5_feeefaa8T p5_feeefaa8Z 4 (p5_feeefaa8D4.map Prod.fst) ((p5_feeefaa8D5.drop (5*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_feeefaa8C5x6 : levelOK p5_feeefaa8T p5_feeefaa8Z 4 (p5_feeefaa8D4.map Prod.fst) ((p5_feeefaa8D5.drop (6*8)).take 8) = true := by decide +kernel
theorem p5_feeefaa8I5 : LevelN p5_feeefaa8R p5_feeefaa8T 5 p5_feeefaa8D5 := levelStep p5_feeefaa8B p5_feeefaa8Y p5_feeefaa8I4 (chunks 8 p5_feeefaa8D5 7 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_feeefaa8C5x0
  · exact p5_feeefaa8C5x1
  · exact p5_feeefaa8C5x2
  · exact p5_feeefaa8C5x3
  · exact p5_feeefaa8C5x4
  · exact p5_feeefaa8C5x5
  · exact p5_feeefaa8C5x6
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_feeefaa8C6x0 : levelOK p5_feeefaa8T p5_feeefaa8Z 5 (p5_feeefaa8D5.map Prod.fst) ((p5_feeefaa8D6.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_feeefaa8C6x1 : levelOK p5_feeefaa8T p5_feeefaa8Z 5 (p5_feeefaa8D5.map Prod.fst) ((p5_feeefaa8D6.drop (1*8)).take 8) = true := by decide +kernel
theorem p5_feeefaa8I6 : LevelN p5_feeefaa8R p5_feeefaa8T 6 p5_feeefaa8D6 := levelStep p5_feeefaa8B p5_feeefaa8Y p5_feeefaa8I5 (chunks 8 p5_feeefaa8D6 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_feeefaa8C6x0
  · exact p5_feeefaa8C6x1
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_feeefaa8C7x0 : levelOK p5_feeefaa8T p5_feeefaa8Z 6 (p5_feeefaa8D6.map Prod.fst) ((p5_feeefaa8D7.drop (0*8)).take 8) = true := by decide +kernel
theorem p5_feeefaa8I7 : LevelN p5_feeefaa8R p5_feeefaa8T 7 p5_feeefaa8D7 := levelStep p5_feeefaa8B p5_feeefaa8Y p5_feeefaa8I6 (chunks 8 p5_feeefaa8D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_feeefaa8C7x0
  ))
theorem p5_feeefaa8L : LowN p5_feeefaa8R p5_feeefaa8T 8 := lowSearch p5_feeefaa8B p5_feeefaa8I7 (by decide +kernel)
def p5_feeefae8T : Nat := 0xfeeefae8feeefae8feeefae8feeefae8
def p5_feeefae8R : List Nat := [0, 1, 2, 3, 4]
def p5_feeefae8E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17)]
theorem p5_feeefae8B : baseOK p5_feeefae8T p5_feeefae8R p5_feeefae8E = true := by decide +kernel
theorem p5_feeefae8S0 : SliceN p5_feeefae8R p5_feeefae8T (0x33333333333333333333333333333333,5,[0, 2, 3, 4]) := mkSlice (w:=0) p5_feeefae8B p4_eae8B p4_eae8L (by decide +kernel)
theorem p5_feeefae8S1 : SliceN p5_feeefae8R p5_feeefae8T (0x55555555555555555555555555555555,4,[1, 2, 3, 4]) := mkSlice (w:=0) p5_feeefae8B p4_eac8B p4_eac8L (by decide +kernel)
theorem p5_feeefae8S2 : SliceN p5_feeefae8R p5_feeefae8T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 4, 3]) := mkSlice (w:=0) p5_feeefae8B p4_eae8B p4_eae8L (by decide +kernel)
theorem p5_feeefae8S3 : SliceN p5_feeefae8R p5_feeefae8T (0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]) := mkSlice (w:=0) p5_feeefae8B p4_eee8B p4_eee8L (by decide +kernel)
theorem p5_feeefae8S4 : SliceN p5_feeefae8R p5_feeefae8T (0xffff0000ffff0000ffff0000ffff,5,[0, 2, 1, 3]) := mkSlice (w:=0) p5_feeefae8B p4_eee8B p4_eee8L (by decide +kernel)
def p5_feeefae8Z : List SliceD := [(0x33333333333333333333333333333333,5,[0, 2, 3, 4]),(0x55555555555555555555555555555555,4,[1, 2, 3, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 4, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]),(0xffff0000ffff0000ffff0000ffff,5,[0, 2, 1, 3])]
theorem p5_feeefae8Y : ∀ s ∈ p5_feeefae8Z, SliceN p5_feeefae8R p5_feeefae8T s := by
  unfold p5_feeefae8Z
  simp only [List.forall_mem_cons]
  exact ⟨p5_feeefae8S0,p5_feeefae8S1,p5_feeefae8S2,p5_feeefae8S3,p5_feeefae8S4,by simp⟩
def p5_feeefae8D6 : List StD := dupD [
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[]),(1,[]),(2,[]),(3,[]),(4,[])],[(1,3),(0,3),(1,5),(0,5),(1,9),(0,9),(1,17),(0,17),(2,6),(18,24),(2,18),(6,10),(12,24),(10,18)],[[0,1000,1,1001],[1,2,1002,1003],[1,3,1004,1005],[1,4,1006,1007],[0,2,1008],[0,3,1009],[0,4,1010],[2,3,1011],[2,4,1012],[3,4,1013]])]
def p5_feeefae8D5 : List StD := []
theorem p5_feeefae8I5 : LevelN p5_feeefae8R p5_feeefae8T 5 p5_feeefae8D5 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_feeefae8C6x0 : levelOK p5_feeefae8T p5_feeefae8Z 5 (p5_feeefae8D5.map Prod.fst) ((p5_feeefae8D6.drop (0*8)).take 8) = true := by decide +kernel
theorem p5_feeefae8I6 : LevelN p5_feeefae8R p5_feeefae8T 6 p5_feeefae8D6 := levelStep p5_feeefae8B p5_feeefae8Y p5_feeefae8I5 (chunks 8 p5_feeefae8D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_feeefae8C6x0
  ))
theorem p5_feeefae8L : LowN p5_feeefae8R p5_feeefae8T 7 := lowSearch p5_feeefae8B p5_feeefae8I6 (by decide +kernel)
def p6_feeefeeafeeefcc0T : Nat := 0xfeeefeeafeeefcc0feeefeeafeeefcc0
def p6_feeefeeafeeefcc0R : List Nat := [0, 1, 2, 3, 4, 5]
def p6_feeefeeafeeefcc0E : List (Nat × Nat × Nat) := [(0,16,17),(1,4,6),(2,2,6),(3,2,10),(4,1,17),(5,1,33)]
theorem p6_feeefeeafeeefcc0B : baseOK p6_feeefeeafeeefcc0T p6_feeefeeafeeefcc0R p6_feeefeeafeeefcc0E = true := by decide +kernel
theorem p6_feeefeeafeeefcc0S0 : SliceN p6_feeefeeafeeefcc0R p6_feeefeeafeeefcc0T (0xffffffff00000000ffffffff,7,[4, 1, 2, 3, 0]) := mkSlice (w:=0) p6_feeefeeafeeefcc0B p5_feeafcc8B p5_feeafcc8L (by decide +kernel)
def p6_feeefeeafeeefcc0Z : List SliceD := [(0xffffffff00000000ffffffff,7,[4, 1, 2, 3, 0])]
theorem p6_feeefeeafeeefcc0Y : ∀ s ∈ p6_feeefeeafeeefcc0Z, SliceN p6_feeefeeafeeefcc0R p6_feeefeeafeeefcc0T s := by
  unfold p6_feeefeeafeeefcc0Z
  simp only [List.forall_mem_cons]
  exact ⟨p6_feeefeeafeeefcc0S0,by simp⟩
def p6_feeefeeafeeefcc0D7 : List StD := dupD [
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0,[])],[],[[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]])]
def p6_feeefeeafeeefcc0D6 : List StD := []
theorem p6_feeefeeafeeefcc0I6 : LevelN p6_feeefeeafeeefcc0R p6_feeefeeafeeefcc0T 6 p6_feeefeeafeeefcc0D6 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p6_feeefeeafeeefcc0C7x0 : levelOK p6_feeefeeafeeefcc0T p6_feeefeeafeeefcc0Z 6 (p6_feeefeeafeeefcc0D6.map Prod.fst) ((p6_feeefeeafeeefcc0D7.drop (0*8)).take 8) = true := by decide +kernel
theorem p6_feeefeeafeeefcc0I7 : LevelN p6_feeefeeafeeefcc0R p6_feeefeeafeeefcc0T 7 p6_feeefeeafeeefcc0D7 := levelStep p6_feeefeeafeeefcc0B p6_feeefeeafeeefcc0Y p6_feeefeeafeeefcc0I6 (chunks 8 p6_feeefeeafeeefcc0D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p6_feeefeeafeeefcc0C7x0
  ))
theorem p6_feeefeeafeeefcc0L : LowN p6_feeefeeafeeefcc0R p6_feeefeeafeeefcc0T 8 := lowSearch p6_feeefeeafeeefcc0B p6_feeefeeafeeefcc0I7 (by decide +kernel)
def p6_feeefeeafeeefcc8T : Nat := 0xfeeefeeafeeefcc8feeefeeafeeefcc8
def p6_feeefeeafeeefcc8R : List Nat := [0, 1, 2, 3, 4, 5]
def p6_feeefeeafeeefcc8E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,2,10),(4,1,17),(5,1,33)]
theorem p6_feeefeeafeeefcc8B : baseOK p6_feeefeeafeeefcc8T p6_feeefeeafeeefcc8R p6_feeefeeafeeefcc8E = true := by decide +kernel
theorem p6_feeefeeafeeefcc8S0 : SliceN p6_feeefeeafeeefcc8R p6_feeefeeafeeefcc8T (0xffffffff00000000ffffffff,8,[1, 0, 2, 3, 4]) := mkSlice (w:=0) p6_feeefeeafeeefcc8B p5_feeefaa8B p5_feeefaa8L (by decide +kernel)
def p6_feeefeeafeeefcc8Z : List SliceD := [(0xffffffff00000000ffffffff,8,[1, 0, 2, 3, 4])]
theorem p6_feeefeeafeeefcc8Y : ∀ s ∈ p6_feeefeeafeeefcc8Z, SliceN p6_feeefeeafeeefcc8R p6_feeefeeafeeefcc8T s := by
  unfold p6_feeefeeafeeefcc8Z
  simp only [List.forall_mem_cons]
  exact ⟨p6_feeefeeafeeefcc8S0,by simp⟩
def p6_feeefeeafeeefcc8D8 : List StD := dupD [
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0,[])],[],[[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]])]
def p6_feeefeeafeeefcc8D7 : List StD := []
theorem p6_feeefeeafeeefcc8I7 : LevelN p6_feeefeeafeeefcc8R p6_feeefeeafeeefcc8T 7 p6_feeefeeafeeefcc8D7 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p6_feeefeeafeeefcc8C8x0 : levelOK p6_feeefeeafeeefcc8T p6_feeefeeafeeefcc8Z 7 (p6_feeefeeafeeefcc8D7.map Prod.fst) ((p6_feeefeeafeeefcc8D8.drop (0*8)).take 8) = true := by decide +kernel
theorem p6_feeefeeafeeefcc8I8 : LevelN p6_feeefeeafeeefcc8R p6_feeefeeafeeefcc8T 8 p6_feeefeeafeeefcc8D8 := levelStep p6_feeefeeafeeefcc8B p6_feeefeeafeeefcc8Y p6_feeefeeafeeefcc8I7 (chunks 8 p6_feeefeeafeeefcc8D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p6_feeefeeafeeefcc8C8x0
  ))
theorem p6_feeefeeafeeefcc8L : LowN p6_feeefeeafeeefcc8R p6_feeefeeafeeefcc8T 9 := lowSearch p6_feeefeeafeeefcc8B p6_feeefeeafeeefcc8I8 (by decide +kernel)
def p5_fefefeeaT : Nat := 0xfefefeeafefefeeafefefeeafefefeea
def p5_fefefeeaR : List Nat := [0, 1, 2, 3, 4]
def p5_fefefeeaE : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,2,10),(4,2,18)]
theorem p5_fefefeeaB : baseOK p5_fefefeeaT p5_fefefeeaR p5_fefefeeaE = true := by decide +kernel
theorem p5_fefefeeaS0 : SliceN p5_fefefeeaR p5_fefefeeaT (0x55555555555555555555555555555555,5,[1, 2, 3, 4]) := mkSlice (w:=0) p5_fefefeeaB p4_eee8B p4_eee8L (by decide +kernel)
def p5_fefefeeaZ : List SliceD := [(0x55555555555555555555555555555555,5,[1, 2, 3, 4])]
theorem p5_fefefeeaY : ∀ s ∈ p5_fefefeeaZ, SliceN p5_fefefeeaR p5_fefefeeaT s := by
  unfold p5_fefefeeaZ
  simp only [List.forall_mem_cons]
  exact ⟨p5_fefefeeaS0,by simp⟩
def p5_fefefeeaD5 : List StD := dupD [
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[])],[],[[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]])]
def p5_fefefeeaD4 : List StD := []
theorem p5_fefefeeaI4 : LevelN p5_fefefeeaR p5_fefefeeaT 4 p5_fefefeeaD4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_fefefeeaC5x0 : levelOK p5_fefefeeaT p5_fefefeeaZ 4 (p5_fefefeeaD4.map Prod.fst) ((p5_fefefeeaD5.drop (0*8)).take 8) = true := by decide +kernel
theorem p5_fefefeeaI5 : LevelN p5_fefefeeaR p5_fefefeeaT 5 p5_fefefeeaD5 := levelStep p5_fefefeeaB p5_fefefeeaY p5_fefefeeaI4 (chunks 8 p5_fefefeeaD5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_fefefeeaC5x0
  ))
theorem p5_fefefeeaL : LowN p5_fefefeeaR p5_fefefeeaT 6 := lowSearch p5_fefefeeaB p5_fefefeeaI5 (by decide +kernel)
def p6_fffefffefffefeeeT : Nat := 0xfffefffefffefeeefffefffefffefeee
def p6_fffefffefffefeeeR : List Nat := [0, 1, 2, 3, 4, 5]
def p6_fffefffefffefeeeE : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,8,12),(3,4,12),(4,4,20),(5,4,36)]
theorem p6_fffefffefffefeeeB : baseOK p6_fffefffefffefeeeT p6_fffefffefffefeeeR p6_fffefffefffefeeeE = true := by decide +kernel
theorem p6_fffefffefffefeeeS0 : SliceN p6_fffefffefffefeeeR p6_fffefffefffefeeeT (0x55555555555555555555555555555555,6,[1, 2, 3, 4, 5]) := mkSlice (w:=0) p6_fffefffefffefeeeB p5_fefefeeaB p5_fefefeeaL (by decide +kernel)
def p6_fffefffefffefeeeZ : List SliceD := [(0x55555555555555555555555555555555,6,[1, 2, 3, 4, 5])]
theorem p6_fffefffefffefeeeY : ∀ s ∈ p6_fffefffefffefeeeZ, SliceN p6_fffefffefffefeeeR p6_fffefffefffefeeeT s := by
  unfold p6_fffefffefffefeeeZ
  simp only [List.forall_mem_cons]
  exact ⟨p6_fffefffefffefeeeS0,by simp⟩
def p6_fffefffefffefeeeD6 : List StD := dupD [
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0,[])],[],[[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]])]
def p6_fffefffefffefeeeD5 : List StD := []
theorem p6_fffefffefffefeeeI5 : LevelN p6_fffefffefffefeeeR p6_fffefffefffefeeeT 5 p6_fffefffefffefeeeD5 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p6_fffefffefffefeeeC6x0 : levelOK p6_fffefffefffefeeeT p6_fffefffefffefeeeZ 5 (p6_fffefffefffefeeeD5.map Prod.fst) ((p6_fffefffefffefeeeD6.drop (0*8)).take 8) = true := by decide +kernel
theorem p6_fffefffefffefeeeI6 : LevelN p6_fffefffefffefeeeR p6_fffefffefffefeeeT 6 p6_fffefffefffefeeeD6 := levelStep p6_fffefffefffefeeeB p6_fffefffefffefeeeY p6_fffefffefffefeeeI5 (chunks 8 p6_fffefffefffefeeeD6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p6_fffefffefffefeeeC6x0
  ))
theorem p6_fffefffefffefeeeL : LowN p6_fffefffefffefeeeR p6_fffefffefffefeeeT 7 := lowSearch p6_fffefffefffefeeeB p6_fffefffefffefeeeI6 (by decide +kernel)
def p5_feeafcc0T : Nat := 0xfeeafcc0feeafcc0feeafcc0feeafcc0
def p5_feeafcc0R : List Nat := [0, 1, 2, 3, 4]
def p5_feeafcc0E : List (Nat × Nat × Nat) := [(0,16,17),(1,4,6),(2,2,6),(3,2,10),(4,1,17)]
theorem p5_feeafcc0B : baseOK p5_feeafcc0T p5_feeafcc0R p5_feeafcc0E = true := by decide +kernel
theorem p5_feeafcc0S0 : SliceN p5_feeafcc0R p5_feeafcc0T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,5,[4, 2, 3, 1]) := mkSlice (w:=1) p5_feeafcc0B p4_feeaB p4_feeaL (by decide +kernel)
def p5_feeafcc0Z : List SliceD := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,5,[4, 2, 3, 1])]
theorem p5_feeafcc0Y : ∀ s ∈ p5_feeafcc0Z, SliceN p5_feeafcc0R p5_feeafcc0T s := by
  unfold p5_feeafcc0Z
  simp only [List.forall_mem_cons]
  exact ⟨p5_feeafcc0S0,by simp⟩
def p5_feeafcc0D5 : List StD := dupD [
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[])],[],[[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]])]
def p5_feeafcc0D4 : List StD := []
theorem p5_feeafcc0I4 : LevelN p5_feeafcc0R p5_feeafcc0T 4 p5_feeafcc0D4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_feeafcc0C5x0 : levelOK p5_feeafcc0T p5_feeafcc0Z 4 (p5_feeafcc0D4.map Prod.fst) ((p5_feeafcc0D5.drop (0*8)).take 8) = true := by decide +kernel
theorem p5_feeafcc0I5 : LevelN p5_feeafcc0R p5_feeafcc0T 5 p5_feeafcc0D5 := levelStep p5_feeafcc0B p5_feeafcc0Y p5_feeafcc0I4 (chunks 8 p5_feeafcc0D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_feeafcc0C5x0
  ))
theorem p5_feeafcc0L : LowN p5_feeafcc0R p5_feeafcc0T 6 := lowSearch p5_feeafcc0B p5_feeafcc0I5 (by decide +kernel)
def p6_feeefeeefeeef888T : Nat := 0xfeeefeeefeeef888feeefeeefeeef888
def p6_feeefeeefeeef888R : List Nat := [0, 1, 2, 3, 4, 5]
def p6_feeefeeefeeef888E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,8,12),(3,4,12),(4,1,17),(5,1,33)]
theorem p6_feeefeeefeeef888B : baseOK p6_feeefeeefeeef888T p6_feeefeeefeeef888R p6_feeefeeefeeef888E = true := by decide +kernel
theorem p6_feeefeeefeeef888S0 : SliceN p6_feeefeeefeeef888R p6_feeefeeefeeef888T (0xffff0000ffff0000ffff0000ffff,6,[2, 1, 0, 5, 3]) := mkSlice (w:=0) p6_feeefeeefeeef888B p5_feeafcc0B p5_feeafcc0L (by decide +kernel)
def p6_feeefeeefeeef888Z : List SliceD := [(0xffff0000ffff0000ffff0000ffff,6,[2, 1, 0, 5, 3])]
theorem p6_feeefeeefeeef888Y : ∀ s ∈ p6_feeefeeefeeef888Z, SliceN p6_feeefeeefeeef888R p6_feeefeeefeeef888T s := by
  unfold p6_feeefeeefeeef888Z
  simp only [List.forall_mem_cons]
  exact ⟨p6_feeefeeefeeef888S0,by simp⟩
def p6_feeefeeefeeef888D6 : List StD := dupD [
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0,[])],[],[[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]])]
def p6_feeefeeefeeef888D5 : List StD := []
theorem p6_feeefeeefeeef888I5 : LevelN p6_feeefeeefeeef888R p6_feeefeeefeeef888T 5 p6_feeefeeefeeef888D5 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p6_feeefeeefeeef888C6x0 : levelOK p6_feeefeeefeeef888T p6_feeefeeefeeef888Z 5 (p6_feeefeeefeeef888D5.map Prod.fst) ((p6_feeefeeefeeef888D6.drop (0*8)).take 8) = true := by decide +kernel
theorem p6_feeefeeefeeef888I6 : LevelN p6_feeefeeefeeef888R p6_feeefeeefeeef888T 6 p6_feeefeeefeeef888D6 := levelStep p6_feeefeeefeeef888B p6_feeefeeefeeef888Y p6_feeefeeefeeef888I5 (chunks 8 p6_feeefeeefeeef888D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p6_feeefeeefeeef888C6x0
  ))
theorem p6_feeefeeefeeef888L : LowN p6_feeefeeefeeef888R p6_feeefeeefeeef888T 7 := lowSearch p6_feeefeeefeeef888B p6_feeefeeefeeef888I6 (by decide +kernel)
def p5_fffefeeeT : Nat := 0xfffefeeefffefeeefffefeeefffefeee
def p5_fffefeeeR : List Nat := [0, 1, 2, 3, 4]
def p5_fffefeeeE : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,8,12),(3,4,12),(4,4,20)]
theorem p5_fffefeeeB : baseOK p5_fffefeeeT p5_fffefeeeR p5_fffefeeeE = true := by decide +kernel
theorem p5_fffefeeeS0 : SliceN p5_fffefeeeR p5_fffefeeeT (0x55555555555555555555555555555555,5,[1, 2, 3, 4]) := mkSlice (w:=0) p5_fffefeeeB p4_feeaB p4_feeaL (by decide +kernel)
def p5_fffefeeeZ : List SliceD := [(0x55555555555555555555555555555555,5,[1, 2, 3, 4])]
theorem p5_fffefeeeY : ∀ s ∈ p5_fffefeeeZ, SliceN p5_fffefeeeR p5_fffefeeeT s := by
  unfold p5_fffefeeeZ
  simp only [List.forall_mem_cons]
  exact ⟨p5_fffefeeeS0,by simp⟩
def p5_fffefeeeD5 : List StD := dupD [
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[])],[],[[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]])]
def p5_fffefeeeD4 : List StD := []
theorem p5_fffefeeeI4 : LevelN p5_fffefeeeR p5_fffefeeeT 4 p5_fffefeeeD4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_fffefeeeC5x0 : levelOK p5_fffefeeeT p5_fffefeeeZ 4 (p5_fffefeeeD4.map Prod.fst) ((p5_fffefeeeD5.drop (0*8)).take 8) = true := by decide +kernel
theorem p5_fffefeeeI5 : LevelN p5_fffefeeeR p5_fffefeeeT 5 p5_fffefeeeD5 := levelStep p5_fffefeeeB p5_fffefeeeY p5_fffefeeeI4 (chunks 8 p5_fffefeeeD5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_fffefeeeC5x0
  ))
theorem p5_fffefeeeL : LowN p5_fffefeeeR p5_fffefeeeT 6 := lowSearch p5_fffefeeeB p5_fffefeeeI5 (by decide +kernel)
def p5_eeeaece8T : Nat := 0xeeeaece8eeeaece8eeeaece8eeeaece8
def p5_eeeaece8R : List Nat := [0, 1, 2, 3, 4]
def p5_eeeaece8E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,2,10),(4,1,17)]
theorem p5_eeeaece8B : baseOK p5_eeeaece8T p5_eeeaece8R p5_eeeaece8E = true := by decide +kernel
theorem p5_eeeaece8S0 : SliceN p5_eeeaece8R p5_eeeaece8T (0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]) := mkSlice (w:=0) p5_eeeaece8B p4_eae8B p4_eae8L (by decide +kernel)
def p5_eeeaece8Z : List SliceD := [(0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4])]
theorem p5_eeeaece8Y : ∀ s ∈ p5_eeeaece8Z, SliceN p5_eeeaece8R p5_eeeaece8T s := by
  unfold p5_eeeaece8Z
  simp only [List.forall_mem_cons]
  exact ⟨p5_eeeaece8S0,by simp⟩
def p5_eeeaece8D5 : List StD := dupD [
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[])],[],[[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]])]
def p5_eeeaece8D4 : List StD := []
theorem p5_eeeaece8I4 : LevelN p5_eeeaece8R p5_eeeaece8T 4 p5_eeeaece8D4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_eeeaece8C5x0 : levelOK p5_eeeaece8T p5_eeeaece8Z 4 (p5_eeeaece8D4.map Prod.fst) ((p5_eeeaece8D5.drop (0*8)).take 8) = true := by decide +kernel
theorem p5_eeeaece8I5 : LevelN p5_eeeaece8R p5_eeeaece8T 5 p5_eeeaece8D5 := levelStep p5_eeeaece8B p5_eeeaece8Y p5_eeeaece8I4 (chunks 8 p5_eeeaece8D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_eeeaece8C5x0
  ))
theorem p5_eeeaece8L : LowN p5_eeeaece8R p5_eeeaece8T 6 := lowSearch p5_eeeaece8B p5_eeeaece8I5 (by decide +kernel)
def p6_fffffffefffefffeT : Nat := 0xfffffffefffefffefffffffefffefffe
def p6_fffffffefffefffeR : List Nat := [0, 1, 2, 3, 4, 5]
def p6_fffffffefffefffeE : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4),(3,0,8),(4,32,48),(5,16,48)]
theorem p6_fffffffefffefffeB : baseOK p6_fffffffefffefffeT p6_fffffffefffefffeR p6_fffffffefffefffeE = true := by decide +kernel
theorem p6_fffffffefffefffeL : LowN p6_fffffffefffefffeR p6_fffffffefffefffeT 5 := lowCount p6_fffffffefffefffeB (by decide +kernel)
def p5_eaeaeac0T : Nat := 0xeaeaeac0eaeaeac0eaeaeac0eaeaeac0
def p5_eaeaeac0R : List Nat := [0, 1, 2, 3, 4]
def p5_eaeaeac0E : List (Nat × Nat × Nat) := [(0,8,9),(1,4,6),(2,2,6),(3,1,9),(4,1,17)]
theorem p5_eaeaeac0B : baseOK p5_eaeaeac0T p5_eaeaeac0R p5_eaeaeac0E = true := by decide +kernel
theorem p5_eaeaeac0L : LowN p5_eaeaeac0R p5_eaeaeac0T 4 := lowCount p5_eaeaeac0B (by decide +kernel)
def p5_feeefeeaT : Nat := 0xfeeefeeafeeefeeafeeefeeafeeefeea
def p5_feeefeeaR : List Nat := [0, 1, 2, 3, 4]
def p5_feeefeeaE : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,2,10),(4,2,18)]
theorem p5_feeefeeaB : baseOK p5_feeefeeaT p5_feeefeeaR p5_feeefeeaE = true := by decide +kernel
theorem p5_feeefeeaS0 : SliceN p5_feeefeeaR p5_feeefeeaT (0x55555555555555555555555555555555,5,[1, 2, 3, 4]) := mkSlice (w:=0) p5_feeefeeaB p4_eae8B p4_eae8L (by decide +kernel)
def p5_feeefeeaZ : List SliceD := [(0x55555555555555555555555555555555,5,[1, 2, 3, 4])]
theorem p5_feeefeeaY : ∀ s ∈ p5_feeefeeaZ, SliceN p5_feeefeeaR p5_feeefeeaT s := by
  unfold p5_feeefeeaZ
  simp only [List.forall_mem_cons]
  exact ⟨p5_feeefeeaS0,by simp⟩
def p5_feeefeeaD5 : List StD := dupD [
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000],[(0,[])],[],[[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]])]
def p5_feeefeeaD4 : List StD := []
theorem p5_feeefeeaI4 : LevelN p5_feeefeeaR p5_feeefeeaT 4 p5_feeefeeaD4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_feeefeeaC5x0 : levelOK p5_feeefeeaT p5_feeefeeaZ 4 (p5_feeefeeaD4.map Prod.fst) ((p5_feeefeeaD5.drop (0*8)).take 8) = true := by decide +kernel
theorem p5_feeefeeaI5 : LevelN p5_feeefeeaR p5_feeefeeaT 5 p5_feeefeeaD5 := levelStep p5_feeefeeaB p5_feeefeeaY p5_feeefeeaI4 (chunks 8 p5_feeefeeaD5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_feeefeeaC5x0
  ))
theorem p5_feeefeeaL : LowN p5_feeefeeaR p5_feeefeeaT 6 := lowSearch p5_feeefeeaB p5_feeefeeaI5 (by decide +kernel)
def p6_fffefefefffefeeeT : Nat := 0xfffefefefffefeeefffefefefffefeee
def p6_fffefefefffefeeeR : List Nat := [0, 1, 2, 3, 4, 5]
def p6_fffefefefffefeeeE : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,8,12),(3,4,12),(4,4,20),(5,4,36)]
theorem p6_fffefefefffefeeeB : baseOK p6_fffefefefffefeeeT p6_fffefefefffefeeeR p6_fffefefefffefeeeE = true := by decide +kernel
theorem p6_fffefefefffefeeeS0 : SliceN p6_fffefefefffefeeeR p6_fffefefefffefeeeT (0x55555555555555555555555555555555,6,[1, 2, 3, 4, 5]) := mkSlice (w:=0) p6_fffefefefffefeeeB p5_feeefeeaB p5_feeefeeaL (by decide +kernel)
def p6_fffefefefffefeeeZ : List SliceD := [(0x55555555555555555555555555555555,6,[1, 2, 3, 4, 5])]
theorem p6_fffefefefffefeeeY : ∀ s ∈ p6_fffefefefffefeeeZ, SliceN p6_fffefefefffefeeeR p6_fffefefefffefeeeT s := by
  unfold p6_fffefefefffefeeeZ
  simp only [List.forall_mem_cons]
  exact ⟨p6_fffefefefffefeeeS0,by simp⟩
def p6_fffefefefffefeeeD6 : List StD := dupD [
 ([0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000],[(0,[])],[],[[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]])]
def p6_fffefefefffefeeeD5 : List StD := []
theorem p6_fffefefefffefeeeI5 : LevelN p6_fffefefefffefeeeR p6_fffefefefffefeeeT 5 p6_fffefefefffefeeeD5 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p6_fffefefefffefeeeC6x0 : levelOK p6_fffefefefffefeeeT p6_fffefefefffefeeeZ 5 (p6_fffefefefffefeeeD5.map Prod.fst) ((p6_fffefefefffefeeeD6.drop (0*8)).take 8) = true := by decide +kernel
theorem p6_fffefefefffefeeeI6 : LevelN p6_fffefefefffefeeeR p6_fffefefefffefeeeT 6 p6_fffefefefffefeeeD6 := levelStep p6_fffefefefffefeeeB p6_fffefefefffefeeeY p6_fffefefefffefeeeI5 (chunks 8 p6_fffefefefffefeeeD6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p6_fffefefefffefeeeC6x0
  ))
theorem p6_fffefefefffefeeeL : LowN p6_fffefefefffefeeeR p6_fffefefefffefeeeT 7 := lowSearch p6_fffefefefffefeeeB p6_fffefefefffefeeeI6 (by decide +kernel)
def p5_fffefefeT : Nat := 0xfffefefefffefefefffefefefffefefe
def p5_fffefefeR : List Nat := [0, 1, 2, 3, 4]
def p5_fffefefeE : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4),(3,16,24),(4,8,24)]
theorem p5_fffefefeB : baseOK p5_fffefefeT p5_fffefefeR p5_fffefefeE = true := by decide +kernel
theorem p5_fffefefeL : LowN p5_fffefefeR p5_fffefefeT 4 := lowCount p5_fffefefeB (by decide +kernel)
def p5_fffffffeT : Nat := 0xfffffffefffffffefffffffefffffffe
def p5_fffffffeR : List Nat := [0, 1, 2, 3, 4]
def p5_fffffffeE : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4),(3,0,8),(4,0,16)]
theorem p5_fffffffeB : baseOK p5_fffffffeT p5_fffffffeR p5_fffffffeE = true := by decide +kernel
theorem p5_fffffffeL : LowN p5_fffffffeR p5_fffffffeT 4 := lowCount p5_fffffffeB (by decide +kernel)
def p4_eeeaT : Nat := 0xeeeaeeeaeeeaeeeaeeeaeeeaeeeaeeea
def p4_eeeaR : List Nat := [0, 1, 2, 3]
def p4_eeeaE : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,2,10)]
theorem p4_eeeaB : baseOK p4_eeeaT p4_eeeaR p4_eeeaE = true := by decide +kernel
theorem p4_eeeaL : LowN p4_eeeaR p4_eeeaT 3 := lowCount p4_eeeaB (by decide +kernel)
def ptopT : Nat := 0xfffffffffffffefcfffeffeefefcaa00
def ptopR : List Nat := [0, 1, 2, 3, 4, 5, 6]
def ptopE : List (Nat × Nat × Nat) := [(0,8,9),(1,16,18),(2,16,20),(3,1,9),(4,2,18),(5,1,33),(6,2,66)]
theorem ptopB : baseOK ptopT ptopR ptopE = true := by decide +kernel
theorem ptopS0 : SliceN ptopR ptopT (0x11111111111111111111111111111111,7,[5, 6, 4, 2, 3]) := mkSlice (w:=0) ptopB p5_feeafcc8B p5_feeafcc8L (by decide +kernel)
theorem ptopS1 : SliceN ptopR ptopT (0x3030303030303030303030303030303,7,[6, 5, 3, 0, 4]) := mkSlice (w:=0) ptopB p5_feeafcc8B p5_feeafcc8L (by decide +kernel)
theorem ptopS2 : SliceN ptopR ptopT (0x5050505050505050505050505050505,7,[5, 1, 6, 4, 3]) := mkSlice (w:=0) ptopB p5_feeafce8B p5_feeafce8L (by decide +kernel)
theorem ptopS3 : SliceN ptopR ptopT (0xf0f00000f0f00000f0f00000f0f,8,[5, 1, 3, 0, 6]) := mkSlice (w:=0) ptopB p5_feeefaa8B p5_feeefaa8L (by decide +kernel)
theorem ptopS4 : SliceN ptopR ptopT (0x330033003300330033003300330033,7,[5, 6, 4, 2, 0]) := mkSlice (w:=0) ptopB p5_feeafcc8B p5_feeafcc8L (by decide +kernel)
theorem ptopS5 : SliceN ptopR ptopT (0x550055005500550055005500550055,7,[6, 4, 1, 5, 2]) := mkSlice (w:=0) ptopB p5_feeefae8B p5_feeefae8L (by decide +kernel)
theorem ptopS6 : SliceN ptopR ptopT (0xffffffffffffffff,8,[4, 5, 3, 0, 1, 2]) := mkSlice (w:=0) ptopB p6_feeefeeafeeefcc0B p6_feeefeeafeeefcc0L (by decide +kernel)
theorem ptopS7 : SliceN ptopR ptopT (0xffff0000ffff0000ffff0000ffff,9,[6, 5, 3, 0, 1, 2]) := mkSlice (w:=0) ptopB p6_feeefeeafeeefcc8B p6_feeefeeafeeefcc8L (by decide +kernel)
theorem ptopS8 : SliceN ptopR ptopT (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,7,[3, 5, 4, 6, 2, 1]) := mkSlice (w:=1) ptopB p6_fffefffefffefeeeB p6_fffefffefffefeeeL (by decide +kernel)
theorem ptopS9 : SliceN ptopR ptopT (0x550055000000000055005500,5,[4, 6, 1, 2]) := mkSlice (w:=8) ptopB p4_eee8B p4_eee8L (by decide +kernel)
theorem ptopS10 : SliceN ptopR ptopT (0xaaaaaaaa00000000aaaaaaaa,6,[3, 4, 6, 2, 1]) := mkSlice (w:=1) ptopB p5_fefefeeaB p5_fefefeeaL (by decide +kernel)
theorem ptopS11 : SliceN ptopR ptopT (0xffffffff00000000ffffffff,7,[4, 6, 3, 0, 2, 1]) := mkSlice (w:=0) ptopB p6_feeefeeefeeef888B p6_feeefeeefeeef888L (by decide +kernel)
theorem ptopS12 : SliceN ptopR ptopT (0x333333330000000033333333,6,[0, 2, 4, 6, 3]) := mkSlice (w:=0) ptopB p5_feeafcc0B p5_feeafcc0L (by decide +kernel)
theorem ptopS13 : SliceN ptopR ptopT (0x222222220000000022222222,5,[3, 2, 4, 6]) := mkSlice (w:=1) ptopB p4_feeaB p4_feeaL (by decide +kernel)
theorem ptopS14 : SliceN ptopR ptopT (0x330033000000000033003300,5,[0, 2, 4, 6]) := mkSlice (w:=8) ptopB p4_feeaB p4_feeaL (by decide +kernel)
theorem ptopS15 : SliceN ptopR ptopT (0x5500550000000000550055,5,[4, 6, 1, 2]) := mkSlice (w:=0) ptopB p4_eee8B p4_eee8L (by decide +kernel)
theorem ptopS16 : SliceN ptopR ptopT (0x3030303030303030,5,[4, 3, 0, 5]) := mkSlice (w:=4) ptopB p4_feeaB p4_feeaL (by decide +kernel)
theorem ptopS17 : SliceN ptopR ptopT (0x3333000033330000,5,[2, 0, 3, 5]) := mkSlice (w:=16) ptopB p4_feeaB p4_feeaL (by decide +kernel)
theorem ptopS18 : SliceN ptopR ptopT (0xaa00aa0000000000aa00aa,5,[4, 6, 1, 2]) := mkSlice (w:=1) ptopB p4_eee8B p4_eee8L (by decide +kernel)
theorem ptopS19 : SliceN ptopR ptopT (0xff00ff00ff00ff00ff00ff00ff00ff00,7,[0, 5, 4, 6, 1, 2]) := mkSlice (w:=8) ptopB p6_fffefffefffefeeeB p6_fffefffefffefeeeL (by decide +kernel)
theorem ptopS20 : SliceN ptopR ptopT (0xf000f000f000f000f000f000f000f,7,[5, 1, 6, 4, 0]) := mkSlice (w:=0) ptopB p5_feeafce8B p5_feeafce8L (by decide +kernel)
theorem ptopS21 : SliceN ptopR ptopT (0xffff0000ffff0000,6,[1, 2, 0, 3, 5]) := mkSlice (w:=16) ptopB p5_fffefeeeB p5_fffefeeeL (by decide +kernel)
theorem ptopS22 : SliceN ptopR ptopT (0x5555000055550000555500005555,6,[5, 6, 1, 2, 3]) := mkSlice (w:=0) ptopB p5_eeeaece8B p5_eeeaece8L (by decide +kernel)
theorem ptopS23 : SliceN ptopR ptopT (0xffffffffffffffff0000000000000000,5,[1, 2, 4, 5, 0, 3]) := mkSlice (w:=64) ptopB p6_fffffffefffefffeB p6_fffffffefffefffeL (by decide +kernel)
theorem ptopS24 : SliceN ptopR ptopT (0xffffffff,4,[4, 3, 0, 1, 2]) := mkSlice (w:=0) ptopB p5_eaeaeac0B p5_eaeaeac0L (by decide +kernel)
theorem ptopS25 : SliceN ptopR ptopT (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,7,[4, 6, 5, 0, 3, 1]) := mkSlice (w:=4) ptopB p6_fffefefefffefeeeB p6_fffefefefffefeeeL (by decide +kernel)
theorem ptopS26 : SliceN ptopR ptopT (0x55550000000000005555000000000000,3,[1, 2, 3, 6]) := mkSlice (w:=48) ptopB p4_fffeB p4_fffeL (by decide +kernel)
theorem ptopS27 : SliceN ptopR ptopT (0xffffffff0000000000000000,4,[1, 2, 4, 3, 0]) := mkSlice (w:=64) ptopB p5_fffefefeB p5_fffefefeL (by decide +kernel)
theorem ptopS28 : SliceN ptopR ptopT (0xf0f0f0f000000000f0f0f0f000000000,4,[0, 1, 3, 4, 6]) := mkSlice (w:=36) ptopB p5_fffffffeB p5_fffffffeL (by decide +kernel)
theorem ptopS29 : SliceN ptopR ptopT (0xf0f0f0f0f0f0f0f,7,[1, 5, 3, 0, 4]) := mkSlice (w:=0) ptopB p5_feeafcc8B p5_feeafcc8L (by decide +kernel)
theorem ptopS30 : SliceN ptopR ptopT (0x3333000033330000333300003333,7,[6, 5, 3, 0, 2]) := mkSlice (w:=0) ptopB p5_feeafcc8B p5_feeafcc8L (by decide +kernel)
theorem ptopS31 : SliceN ptopR ptopT (0xff000000ff000000ff000000ff,6,[5, 6, 1, 2, 0]) := mkSlice (w:=0) ptopB p5_eeeaece8B p5_eeeaece8L (by decide +kernel)
theorem ptopS32 : SliceN ptopR ptopT (0xff00000000000000ff000000000000,3,[0, 1, 2, 6]) := mkSlice (w:=48) ptopB p4_fffeB p4_fffeL (by decide +kernel)
theorem ptopS33 : SliceN ptopR ptopT (0xaaaaaaaaaaaaaaaa0000000000000000,4,[1, 2, 3, 4, 5]) := mkSlice (w:=65) ptopB p5_fffffffeB p5_fffffffeL (by decide +kernel)
theorem ptopS34 : SliceN ptopR ptopT (0x55555555000000005555555500000000,4,[1, 3, 6, 4, 2]) := mkSlice (w:=32) ptopB p5_fffefefeB p5_fffefefeL (by decide +kernel)
theorem ptopS35 : SliceN ptopR ptopT (0xff00ff00ff00ff000000000000000000,4,[0, 1, 2, 4, 5]) := mkSlice (w:=72) ptopB p5_fffffffeB p5_fffffffeL (by decide +kernel)
theorem ptopS36 : SliceN ptopR ptopT (0xff00ff0000000000ff00ff00000000,4,[0, 1, 6, 4, 2]) := mkSlice (w:=32) ptopB p5_fffefefeB p5_fffefefeL (by decide +kernel)
theorem ptopS37 : SliceN ptopR ptopT (0xaaaaaaaa,3,[3, 4, 1, 2]) := mkSlice (w:=1) ptopB p4_eeeaB p4_eeeaL (by decide +kernel)
theorem ptopS38 : SliceN ptopR ptopT (0x550055,2,[4, 2, 1]) := mkSlice (w:=0) ptopB p3_a8B p3_a8L (by decide +kernel)
theorem ptopS39 : SliceN ptopR ptopT (0x33333333000000003333333300000000,4,[0, 3, 6, 4, 2]) := mkSlice (w:=32) ptopB p5_fffefefeB p5_fffefefeL (by decide +kernel)
theorem ptopS40 : SliceN ptopR ptopT (0xff00ff00,3,[0, 4, 2, 1]) := mkSlice (w:=8) ptopB p4_eeeaB p4_eeeaL (by decide +kernel)
theorem ptopS41 : SliceN ptopR ptopT (0xffff0000,3,[1, 2, 0, 3]) := mkSlice (w:=16) ptopB p4_feeeB p4_feeeL (by decide +kernel)
theorem ptopS42 : SliceN ptopR ptopT (0x33333333333333330000000000000000,4,[2, 4, 5, 0, 3]) := mkSlice (w:=64) ptopB p5_fffefefeB p5_fffefefeL (by decide +kernel)
def ptopZ : List SliceD := [(0x11111111111111111111111111111111,7,[5, 6, 4, 2, 3]),(0x3030303030303030303030303030303,7,[6, 5, 3, 0, 4]),(0x5050505050505050505050505050505,7,[5, 1, 6, 4, 3]),(0xf0f00000f0f00000f0f00000f0f,8,[5, 1, 3, 0, 6]),(0x330033003300330033003300330033,7,[5, 6, 4, 2, 0]),(0x550055005500550055005500550055,7,[6, 4, 1, 5, 2]),(0xffffffffffffffff,8,[4, 5, 3, 0, 1, 2]),(0xffff0000ffff0000ffff0000ffff,9,[6, 5, 3, 0, 1, 2]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,7,[3, 5, 4, 6, 2, 1]),(0x550055000000000055005500,5,[4, 6, 1, 2]),(0xaaaaaaaa00000000aaaaaaaa,6,[3, 4, 6, 2, 1]),(0xffffffff00000000ffffffff,7,[4, 6, 3, 0, 2, 1]),(0x333333330000000033333333,6,[0, 2, 4, 6, 3]),(0x222222220000000022222222,5,[3, 2, 4, 6]),(0x330033000000000033003300,5,[0, 2, 4, 6]),(0x5500550000000000550055,5,[4, 6, 1, 2]),(0x3030303030303030,5,[4, 3, 0, 5]),(0x3333000033330000,5,[2, 0, 3, 5]),(0xaa00aa0000000000aa00aa,5,[4, 6, 1, 2]),(0xff00ff00ff00ff00ff00ff00ff00ff00,7,[0, 5, 4, 6, 1, 2]),(0xf000f000f000f000f000f000f000f,7,[5, 1, 6, 4, 0]),(0xffff0000ffff0000,6,[1, 2, 0, 3, 5]),(0x5555000055550000555500005555,6,[5, 6, 1, 2, 3]),(0xffffffffffffffff0000000000000000,5,[1, 2, 4, 5, 0, 3]),(0xffffffff,4,[4, 3, 0, 1, 2]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,7,[4, 6, 5, 0, 3, 1]),(0x55550000000000005555000000000000,3,[1, 2, 3, 6]),(0xffffffff0000000000000000,4,[1, 2, 4, 3, 0]),(0xf0f0f0f000000000f0f0f0f000000000,4,[0, 1, 3, 4, 6]),(0xf0f0f0f0f0f0f0f,7,[1, 5, 3, 0, 4]),(0x3333000033330000333300003333,7,[6, 5, 3, 0, 2]),(0xff000000ff000000ff000000ff,6,[5, 6, 1, 2, 0]),(0xff00000000000000ff000000000000,3,[0, 1, 2, 6]),(0xaaaaaaaaaaaaaaaa0000000000000000,4,[1, 2, 3, 4, 5]),(0x55555555000000005555555500000000,4,[1, 3, 6, 4, 2]),(0xff00ff00ff00ff000000000000000000,4,[0, 1, 2, 4, 5]),(0xff00ff0000000000ff00ff00000000,4,[0, 1, 6, 4, 2]),(0xaaaaaaaa,3,[3, 4, 1, 2]),(0x550055,2,[4, 2, 1]),(0x33333333000000003333333300000000,4,[0, 3, 6, 4, 2]),(0xff00ff00,3,[0, 4, 2, 1]),(0xffff0000,3,[1, 2, 0, 3]),(0x33333333333333330000000000000000,4,[2, 4, 5, 0, 3])]
theorem ptopY : ∀ s ∈ ptopZ, SliceN ptopR ptopT s := by
  unfold ptopZ
  simp only [List.forall_mem_cons]
  exact ⟨ptopS0,ptopS1,ptopS2,ptopS3,ptopS4,ptopS5,ptopS6,ptopS7,ptopS8,ptopS9,ptopS10,ptopS11,ptopS12,ptopS13,ptopS14,ptopS15,ptopS16,ptopS17,ptopS18,ptopS19,ptopS20,ptopS21,ptopS22,ptopS23,ptopS24,ptopS25,ptopS26,ptopS27,ptopS28,ptopS29,ptopS30,ptopS31,ptopS32,ptopS33,ptopS34,ptopS35,ptopS36,ptopS37,ptopS38,ptopS39,ptopS40,ptopS41,ptopS42,by simp⟩
def ptopD10 : List StD := [
 ([0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000],[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[])],[(8,9),(10,11),(17,19),(17,21),(8,13),(32,33),(1,9),(3,19),(2,18),(1,33),(72,73),(3,67),(34,36),(24,26),(3,11),(32,34),(2,34),(64,66),(24,28),(48,52),(64,68),(10,26),(32,40),(8,40),(65,73),(10,74),(36,52),(64,80),(64,96),(32,96)],[[0,1,2,1000,1001,1002],[0,1,3,1003,1004],[0,4,1005,5,1000,1006],[0,3,1007,1008],[0,1000,1005,1009],[0,6,1000,1010,1011],[0,2,3,1012,1003],[0,5,1002,4,1013,1014],[0,3,1007,1002],[0,1002,1015,1016],[0,6,1002,1017,1011],[1,3,1018,4,1003],[1,3,7,1003],[1,3,1019,1003],[1,3,1020,6,1003],[3,1021,4,1007],[4,1006,1022,1023],[4,6,1006,1024,1025],[3,1026,1007],[3,1027,6,1007],[6,1011,1028,1029]])]
def ptopD9 : List StD := [
 ([0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffaaaaaaaaffffffffaaaaaaaa,0xffffffffffffffff0000000000000000],[(0,[]),(5,[]),(8,[]),(7,[(2,1,3)]),(3,[(1,0,3)]),(9,[]),(6,[(1,1,3)]),(7,[(1,1,3)]),(2,[]),(10,[])],[(34,36),(2,18),(3,33),(64,66),(16,18),(6,18),(5,33),(64,68),(16,20),(32,40),(17,33),(64,80),(65,97),(1,33)],[[0,1,2],[0,2],[0,1,2],[0,2],[0,2],[0,2,3],[0,2],[0,4,1000],[0,1,5],[0,4,1001],[0,5,1002],[0,2,5],[0,1003,6,1004],[1,4,5],[4,7,1005,8],[4,5,1006],[2,4,5],[4,1007,6,1008],[1,4,5],[1,5,1009,9],[1,2],[1,5],[4,5,1010],[2,3,4,5],[4,1011,6,1001],[0],[5,1012,6,1013],[2,5]]),
 ([0x55555555000000005555555500000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000],[(2,[]),(8,[]),(7,[(1,1,3)]),(0,[]),(5,[]),(7,[(2,1,3)]),(6,[]),(9,[]),(6,[(2,1,3)]),(11,[])],[(32,34),(48,52),(32,40),(36,52),(32,96),(34,36),(2,18),(64,66),(64,68),(64,80),(65,97)],[[0,1,2],[1,3,1000],[0,1,1001],[1,4,1002],[1,5,1003],[0],[1,1004,6],[0,1],[0,3,1],[0,1],[0,1],[0,1],[0,1],[0,3,1005],[3,4,7],[3,5,1006],[3,7,1000],[3,1007,8,1000],[0,4,7],[0,5,1001],[0,7,1001],[0,1008,8,1001],[4,5,7],[4,7,1002,9],[4,7],[5,7,1003],[5,1009,8,1003],[7,1010,8,1004]]),
 ([0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xffffffffffffffffaaaaaaaaaaaaaaaa],[(2,[]),(0,[]),(8,[]),(7,[(2,0,3)]),(5,[]),(7,[(1,0,3)]),(10,[]),(6,[])],[(34,36),(3,9),(2,18),(3,33),(64,66),(16,18),(5,9),(6,18),(5,33),(7,67),(16,20),(9,17),(10,34),(9,65),(32,40),(17,33),(64,80),(33,65),(2,34)],[[0,1,2],[0,1,2],[0,2],[0,2],[0,2],[0,2],[0,2,3],[0,1,1000],[1,4,1001],[1,5,1002],[1,6,1003],[1,7,1004],[1,2,1005],[0,4,1006],[0,5,1007],[0,6,1008],[0,7,1009],[0,2,1010],[4,5,1011],[4,6,1012],[4,7,1013],[2,4,1014],[5,6,1015],[5,7,1016],[2,3,5,1002],[6,7,1017],[2,6,1018],[0]]),
 ([0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000],[(0,[]),(4,[]),(1,[]),(7,[(1,4,5)]),(12,[]),(6,[(1,4,5)]),(7,[(3,4,5)]),(6,[])],[(10,11),(3,18),(32,33),(72,73),(3,11),(2,18),(34,36),(2,34),(2,66),(48,52),(64,68),(9,17),(32,40),(65,73),(36,52),(64,80),(64,96),(32,96)],[[0,1,1000],[0,2,1000],[0,1,1000],[0,3,1001],[0,1002,4,1000],[0,1003,5,1000],[0,2,6],[0,1,1004],[0,3,1005],[0,1006,1007],[0,1008,5],[1,2,1004],[2,3,1005],[2,1009,4,1007],[2,1010,5,7],[1,3,1011],[1,1012,4,1004],[1,1013,5,1004],[3,1014,4,1005],[3,1015,5,1005],[4,5,1007,1016,1017]]),
 ([0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffccccccccffffffffcccccccc,0xffffffffffffffff0000000000000000],[(0,[]),(4,[]),(1,[]),(13,[]),(12,[]),(3,[(1,0,1)]),(7,[(2,1,4)]),(6,[(1,1,4)]),(14,[]),(7,[(1,1,4)])],[(10,11),(32,33),(34,36),(3,11),(2,18),(2,34),(2,66),(6,18),(6,34),(48,52),(64,68),(10,34),(36,52),(64,80),(32,96)],[[0,1,1000],[0,2,3],[0,1,3],[0,3],[0,3,1001,4],[0,3,1000,4],[0,3],[0,2,1002,5],[0,1,1003],[0,5,1004],[0,3,1005],[0,3,6],[0,1006,7],[1,2,8],[2,5,1007,9],[2,3,1008],[2,3,1009],[2,1010,7,1009],[1,5,8],[1,3,1011],[1,3,1003],[1,8],[3,5,1012],[3,5,1004],[5,1013,7,1004],[0],[3,1014,7],[3,1006,7]]),
 ([0x33333333000000003333333300000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000],[(0,[]),(12,[]),(7,[(1,1,4)]),(1,[]),(4,[]),(7,[(2,1,4)]),(6,[]),(10,[]),(9,[]),(3,[(2,0,1)]),(15,[]),(6,[(2,1,4)])],[(32,33),(48,52),(32,40),(36,52),(32,96),(2,18),(2,34),(64,66),(16,18),(64,68),(64,80)],[[0,1,1000],[0,1,2],[1,3,1001],[1,4,1002],[1,5,1003],[0],[1,1004,6],[0,1,7,8],[0,3,7],[0,4,7],[0,5,7],[0,1,1000],[0,7],[0,3,9],[0,4,8,10],[0,5,1005],[0,1,1006],[0,1007,11,1008],[3,4,8],[3,5,1001],[1,3,1001],[3,1009,11,1001],[4,5,8],[1,4,1002],[4,8],[1,5,1003],[5,1010,11,1003],[1,1004,11]]),
 ([0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xffffffffffffffffcccccccccccccccc],[(4,[]),(0,[]),(3,[(1,1,4)]),(16,[]),(17,[]),(12,[]),(6,[]),(7,[(1,0,4)])],[(10,11),(32,33),(3,66),(3,11),(2,18),(2,34),(64,66),(6,66),(64,68),(32,40),(10,66),(64,80),(64,96)],[[0,1,1000],[1,2,3],[0,1,1000],[1,2,4],[1,1001,5,1000],[1,3,1002],[1,3,1000],[0,2],[0,1,1003],[0,2,1004],[0,1005,1006],[0,3,6],[0,3,6],[0,2,3],[2,7,3,4],[2,3],[2,3,1007,4],[2,3,1008,4],[0,2,4],[0,1009,5,1003],[0,3,1010],[0,3,1003],[2,4],[2,3,1011],[2,3,1004],[3,1012,5],[3,1005,5],[0]]),
 ([0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffff00ff00ffffffffff00ff00,0xffffffffffffffff0000000000000000],[(12,[]),(4,[]),(10,[]),(18,[]),(9,[]),(19,[]),(5,[]),(14,[]),(3,[(1,0,2)]),(6,[(1,1,2)]),(7,[(1,1,2)]),(20,[])],[(32,33),(34,36),(2,18),(32,34),(64,66),(6,18),(12,40),(64,68),(16,20),(24,40),(64,80),(72,104),(8,40)],[[0,1,2,3,4],[3,4],[1,2,5],[3,4],[0,3,6,1000,7],[3,6,5],[3,4],[0,1,8,1001],[0,1,3,4],[0,1,8,1002],[0,1,3,1003],[0,1,3,4],[0,1,1004,9,1003],[1,4],[8,10,1005,11],[0,3,8,1006],[3,4],[8,1007,9,1008],[1,4],[0,1,5],[0],[1,4],[0,3,8,1009],[3,4],[8,1010,9,1002],[1],[0,3,1011,9,1012],[3,4]]),
 ([0xff00ff0000000000ff00ff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000],[(12,[]),(10,[]),(3,[(2,0,2)]),(7,[(1,1,2)]),(7,[(0,1,2)]),(6,[]),(9,[]),(4,[]),(19,[]),(20,[]),(6,[(2,1,2)]),(7,[(2,1,2)])],[(32,33),(32,34),(48,52),(36,52),(32,96),(34,36),(2,18),(64,66),(64,68),(64,80),(72,104)],[[0,1,1000],[0,1,1001],[0,2,1002],[0,3],[0,2,1003],[0,4],[0,1004,5],[0,1,6],[1,2,6],[1,6,7,8],[1,2,6],[0,1,1000],[1,6],[0,2,1005],[0,6,9],[0,2,1006],[0,1,1001],[0,1007,10,1001],[2,6,7],[2,9,1002,11],[0,2,1002],[2,1008,10,1002],[2,6,7],[0,6,8,7],[6,7],[0,2,1003],[2,1009,10,1003],[0,1010,10,1004]]),
 ([0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xffffffffffffffffff00ff00ff00ff00],[(4,[]),(9,[]),(20,[]),(19,[]),(7,[(1,0,2)]),(5,[]),(6,[])],[(9,10),(9,12),(3,18),(1,33),(9,72),(32,33),(34,36),(2,18),(3,33),(64,66),(16,18),(6,18),(5,33),(64,68),(16,20),(17,33),(64,80),(40,72)],[[0,1,1000],[1,2,1001],[0,1,3],[1,4,1002],[1,5,1003],[1,6,1004],[1,5,3,1005],[0,2,1006],[0,2,1],[0,4,1007],[0,1,1008],[0,6,1009],[0,1,1010],[0,1],[2,4,1011],[1,2,1012],[2,6,1013],[1,2,1014],[0,1],[0,1,3],[0,1],[0,1,6],[1,4,1015],[4,6,1016],[1,4,1007],[1,6,1017],[1,1003,3],[0]]),
 ([0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffff00000000],[(4,[(1,0,1)]),(5,[(1,0,3)]),(10,[]),(20,[(1,0,2)]),(3,[(1,0,4)]),(0,[(1,0,1)]),(14,[]),(6,[]),(9,[]),(7,[(1,0,1)])],[(8,9),(10,11),(9,12),(8,13),(32,33),(3,18),(2,18),(65,97),(72,73),(34,36),(16,20),(1,9),(3,11),(0,18),(32,34),(16,18),(64,66),(5,9),(48,52),(64,68),(9,17),(32,40),(72,104),(65,73),(36,52),(64,80)],[[0,1,1000,2,1001],[1,3,4,2,1002,1003],[0,5,1004,1,6,2,1000],[1,4,2,1005,1006],[1,6,1000,2,1004,1007],[1,7,2,1008],[1,1000,2,1004],[0,3,4,1009,1010],[0,1,5,1011,8,1012],[0,4,1006,1013],[0,2,1007,6,1014,1015],[0,7,1016],[0,1015,1014],[0,4,6,1017,1010],[3,4,9,1010],[2,3,4,1018,1010],[3,4,7,1019],[3,4,1018,1010],[0,4,6,1020,1006],[0,2,1007,6,1021,1022],[0,7,6,1023],[0,1011,6,1021],[2,4,1024,1006],[4,7,1025],[4,1024,1006],[2,7,1007],[7],[2]]),
 ([0xffffffff00000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000],[(5,[(3,0,3)]),(9,[]),(5,[]),(14,[]),(3,[(2,0,4)]),(10,[]),(7,[(0,0,1)]),(7,[(1,0,1)]),(12,[]),(15,[]),(6,[]),(7,[(3,0,1)])],[(32,33),(32,34),(48,52),(32,40),(36,52),(34,36),(2,18),(2,66),(6,66),(16,80),(64,96)],[[0,1,2,1000,3],[1,3,1001],[1,4,1002],[0,1,2,1003,5],[1,4,1004],[1,6],[1,7],[0,1,3,5],[0,1,4,5],[0,1,1000,3],[0,1,4,5],[0,1,3,1000],[0,1,5],[3,4,1005],[0,3,8,1,9],[3,4,1006],[1,3,1001],[3,10,1007],[0,4,1,9],[4,11,1002],[1,4,1002],[4,10,1008],[0,4,1,9],[0,1,5,1003],[0,9,1],[1,4,1004],[4,10,1009],[1,10,1010]])]
def ptopD8 : List StD := [
 ([0xff00ff00aa00aa00ff00ff00aa00aa,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000],[(5,[]),(9,[]),(10,[]),(14,[]),(18,[]),(7,[(1,1,3),(3,2,6)]),(2,[(2,0,4)]),(0,[(2,0,4)])],[(34,36),(2,18),(3,33),(64,66),(16,18),(6,18),(5,33),(64,68),(16,20),(17,33),(64,80),(65,97),(1,33)],[[0,1,2],[1,3,4],[1,4],[1,4],[0],[1,4],[0,2],[0,2],[0,2],[0,1,5,3],[0,2],[3,6,1000],[3,5,1001],[1,3,1002,7],[3,1003,1004],[5,6,1005],[1,6,1006],[6,1007,1008],[1,5,1009],[5,1010,1001],[1,1011,1012]]),
 ([0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xffffffffffffffff5555555500000000],[(5,[(1,0,3)]),(10,[]),(0,[(1,0,1)]),(8,[]),(2,[(1,0,2)]),(9,[]),(21,[(3,2,4)]),(22,[(1,0,1)]),(6,[(2,1,3)]),(23,[]),(24,[]),(25,[]),(26,[]),(7,[]),(21,[])],[(34,36),(2,18),(3,33),(64,66),(16,18),(6,18),(0,20),(5,33),(64,68),(32,40),(17,33),(1,33),(64,80)],[[0,1],[0,1],[0,2,1],[0,1],[0,1,3],[0,1],[0,1],[2,4,1000],[0,2,5],[2,6,1001,7],[1,2,1002],[2,8,1003],[2,9,1003,10,1004],[0,4,5],[4,6,1005,7,1006],[1,4,1007],[4,8,1008],[4,9,11,10],[0,5],[0,1,1009],[0,5],[0,5],[1,6,1010,7,1011],[8,12,1012,7],[10,7,13,9,6,14],[1,0,6,8],[0,6],[1]]),
 ([0x33333333000000003333333300000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000],[(5,[(1,2,4),(3,2,3)]),(9,[(1,2,3)]),(5,[(1,2,4)]),(14,[]),(7,[(1,4,5),(1,1,6)]),(2,[]),(10,[(1,3,4)]),(7,[(1,4,5),(2,1,4)]),(7,[(1,4,5),(0,1,4)]),(6,[(1,4,5)]),(0,[]),(4,[]),(25,[(2,2,5)]),(1,[]),(27,[]),(6,[(2,1,4)]),(6,[(2,1,4),(1,4,5)])],[(32,33),(32,40),(36,50),(32,96),(2,18),(2,34),(2,66),(36,52),(64,80)],[[0,1,2,1000,3],[1,4,5],[0,1,2,1001,6],[1,7,1002],[1,8],[1,1003,9],[0,1,6],[0,1,10,3,6],[0,1,6],[0,1,3,1000],[0,1,6],[0,11,1],[7,12,1004,13],[1,12,1005,13],[13,14,1006,15],[0,7,1,11],[0,1,6,1001],[0,11,1],[1,7,1007],[7,1008,16,1004],[1,1003,16]]),
 ([0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xffffffffffffffffcccccccccccccccc],[(5,[(1,0,2),(1,2,4)]),(0,[]),(25,[(1,1,5)]),(16,[]),(1,[]),(4,[]),(7,[(1,4,5),(1,0,4)]),(17,[]),(14,[]),(7,[(1,0,4),(1,5,6)]),(12,[])],[(1,9),(32,33),(8,9),(3,66),(10,11),(32,40),(10,66),(3,11),(64,80),(64,96),(34,36)],[[0,1,2,3,4],[0,1,5,1000],[0,1,6,7],[0,1,1001,8,1002],[0,1,3,1003],[0,1,3,1004],[0,3,4],[3,4],[3,4],[3,4,9,7],[3,4,9,7],[0,5,6,7],[0,5,1005,10,1000],[0,3,5,1006],[0,3,5,1007],[6,7],[3,6,1008],[3,6,1008],[3,1009,8],[3,1010,8,1009],[1]]),
 ([0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffff00000000],[(0,[(1,0,1)]),(4,[(1,0,1)]),(25,[(1,1,2)]),(10,[]),(1,[(1,0,1)]),(14,[]),(7,[(1,4,5),(1,0,1)]),(17,[]),(13,[]),(7,[(1,0,1),(3,4,5)]),(6,[(1,4,5)]),(28,[]),(16,[])],[(10,11),(32,33),(3,11),(2,18),(34,36),(64,68),(32,40),(64,80)],[[0,1,1000],[0,2,3,4],[0,1,5],[0,6,7],[0,5,1001],[0,7,8],[0,8],[4,9],[0,1,1002],[0,6,1003],[0,5,1004],[0,7,10],[0,11,1004],[1,2,5],[4,6,7],[3,4,5,12],[4,7,1005],[4,12],[1,5],[1,5,1006,8],[1,5],[1,5],[5,6,7],[6,7,1007,10],[6,7],[5,7],[7],[5]]),
 ([0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffccccccccffffffffcccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffcccccccccccccccc],[(1,[]),(0,[]),(16,[]),(14,[]),(4,[]),(7,[(1,1,4),(1,0,4)]),(17,[]),(13,[]),(7,[(1,1,4),(1,0,6)]),(7,[(1,0,4),(1,1,6)])],[(32,33),(6,66),(34,36),(10,34),(3,11),(64,80)],[[0,1,2],[1,3,4],[1,5,6],[1,3,1000],[1,3,1000],[1,2,7],[1,2,7],[0,2],[0,2],[0,2],[0,2],[0,2,1001,6],[0,2,1002,6],[4,3],[3,4,1003,7],[3,4,1004,7],[2,3,4],[2,3,4],[3,5,6],[3,5,6],[2,5,1005],[2,5,1005],[0],[2,3],[2,3,8],[2,3,9],[2,3,8],[0]]),
 ([0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffccccccccffffffffcccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffff00000000],[(4,[(1,0,1)]),(0,[(1,0,1)]),(16,[]),(13,[]),(14,[]),(3,[(1,0,1),(1,0,4)]),(7,[(1,0,1),(2,1,4)]),(6,[(1,1,4)]),(7,[(1,1,4),(1,0,1)]),(17,[])],[(10,11),(34,36),(3,11),(2,18),(2,34),(64,68),(64,80)],[[0,1,1000],[1,2,3],[0,1,3],[1,3],[1,3,1000,4],[1,2,3],[1,3],[0,2,1001,5],[0,1,1002],[0,5,1003],[3,6],[0,2,7],[0,7,1004],[0,2,4],[5,8,2,9],[3,2,5],[2,5,1005,7],[5,2],[0,4],[0,3,1002],[0,2,4],[0,4],[3,5,9],[2,5,1006],[5,9],[2,0,3],[0,2],[3]]),
 ([0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffcccccccc],[(4,[(1,0,1)]),(13,[]),(16,[]),(0,[(1,0,1)]),(14,[]),(29,[(1,0,1)]),(17,[]),(7,[(1,0,4),(1,1,6)]),(6,[(2,1,4)]),(1,[(1,0,1)])],[(10,11),(32,33),(34,36),(3,11),(2,18),(2,34),(6,66),(10,34),(64,80)],[[0,1,1000],[2,1,3],[0,1,3],[3,1],[1,3,1001,4],[2,1,3],[3,1],[0,2,1002,5],[0,1,1003],[0,6,1004],[0,1,5,1005],[0,2,7,5],[0,8],[0,2,4],[5,2],[1,2,5],[2,6,1006,9],[5,2],[0,4],[0,1,1007],[0,2,4],[0,4],[1,6,7],[2,6,1008],[7,6],[1,0,2],[2],[1]]),
 ([0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xffffffffffffffff3333333300000000],[(4,[(1,0,1)]),(0,[(1,0,1)]),(10,[]),(9,[]),(14,[]),(16,[]),(29,[(3,0,1)]),(15,[]),(17,[]),(23,[]),(6,[(1,1,4)]),(30,[(1,0,1)])],[(32,33),(2,18),(2,34),(64,66),(64,68),(10,34),(64,80)],[[0,1,2,3],[1,2],[0,1,2],[1,2],[1,2,1000,4],[1,2],[1,2],[0,5,6],[0,1,3,7],[0,8,1001],[0,2,1002],[0,5,1003,6],[0,9,10,6],[0,3],[6,5],[2,5,6],[5,8,1004],[6,5],[0,3],[0,2,1005],[0,3],[0,3],[2,8,11],[5,8,1006],[11,8],[2,0,5],[0,5],[2]]),
 ([0x33333333000000003333333300000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffff00000000],[(14,[]),(0,[(1,0,1)]),(7,[(1,0,1),(1,1,4)]),(16,[]),(29,[]),(4,[(1,0,1)]),(10,[]),(7,[(1,0,1),(2,1,4)]),(17,[]),(9,[]),(29,[(3,0,1)]),(15,[]),(27,[])],[(32,33),(32,40),(2,18),(34,64),(2,34),(64,68),(64,80)],[[0,1,1000],[0,2],[0,3,4],[0,5,1001,6],[0,7,8],[0,1,3],[3],[0,1,6,9],[1,3,6],[0,1,5],[1,6],[1,3,6],[1,6],[0,3,10],[0,1,9,11],[0,7,1002],[0,3,1003,10],[0,12,1004,10],[0,3,5],[7,3,8],[3,8,1005],[10,3],[5,0],[3,0,5],[5,0],[3,7,1006],[7,8],[0]]),
 ([0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffffcccccccccccccccc,0xffffffffffffffffffffffff00000000],[(17,[]),(10,[(1,2,4)]),(15,[(1,1,2)]),(29,[]),(16,[]),(14,[]),(4,[(1,0,1)]),(7,[(1,0,4),(1,0,1)]),(0,[(1,0,1)]),(10,[]),(13,[]),(23,[]),(7,[(1,0,4),(1,1,6)])],[(10,11),(32,33),(3,11),(2,18),(34,64),(2,66),(64,68),(32,40)],[[0,1,1000,2],[3,1,4],[5,6],[0,2,7],[5,8,1001],[0,1,9,2,8],[8,10],[0,3],[0,5,1002],[0,4,1003],[0,5,1004],[0,3],[0,11,12,1005],[2,3,4],[0,3,4],[1,3,4],[0,3,1006],[3,4],[0,2,6,5],[1,5,6,1007,10],[0,5,6],[6,5],[1,0,5,7],[0,4,1003],[7,0],[0,5,6],[0],[0,5]]),
 ([0x55555555550055005555555555005500,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000],[(14,[]),(10,[]),(9,[]),(7,[(0,2,3)]),(4,[]),(20,[(2,0,4)]),(31,[(2,0,4)]),(4,[(2,0,4)]),(7,[(1,1,2),(3,3,6)])],[(34,36),(16,18),(0,18),(2,33),(64,66),(16,20),(0,20),(4,33),(64,68),(16,33),(64,80),(2,18),(64,97),(0,33)],[[0,1,2],[1,2],[0,1,3],[1,2],[0,1,4],[1,2],[0,5,1000],[0,5,2],[0,1001,6,1002],[0,1,1003,7],[0,1004,1001],[0,5,7],[5,1005,6,1006],[0,5,1007],[5,1008,1005],[0,5],[0,1,8,5],[0,5],[0,8,1009],[6,8,1010,1011],[0,1012,1013]]),
 ([0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xffffffffffffffff00ff00ff00000000],[(14,[]),(10,[]),(9,[]),(4,[(1,0,1)]),(29,[(2,1,2)]),(13,[]),(20,[(1,0,2)]),(21,[(3,3,4)]),(31,[(1,0,1)]),(23,[]),(24,[]),(6,[(2,1,2)]),(16,[]),(19,[]),(32,[]),(7,[]),(17,[])],[(32,33),(34,36),(2,18),(32,34),(64,66),(16,18),(6,18),(0,20),(12,40),(64,68),(24,40),(8,40),(64,80)],[[0,1,2],[2,1],[0,1,3],[2,1],[0,1,1000],[2,1],[2,1],[0,4,1001],[0,5,2,6],[0,7,1002,8],[0,1,1003],[0,4,1004],[0,9,1003,10,1005],[0,3],[4,7,1006,8,1007],[0,4,1008],[4,6,1009,11],[4,9,12,10],[3,0],[0,1,13,3],[3,0],[3,0],[0,7,1010,8,1011],[4,14,1012,8],[10,8,15,9,7,16],[0,3,4],[0,3,4],[0]]),
 ([0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffff00000000,0xffffffffffffffffffffffffcccccccc],[(4,[(1,0,1)]),(33,[]),(34,[]),(14,[]),(0,[(1,0,1)]),(13,[]),(28,[]),(29,[(1,0,1)]),(35,[]),(36,[]),(32,[]),(7,[(1,0,1),(1,4,6)]),(27,[]),(7,[(1,0,1),(3,4,6)]),(17,[]),(16,[])],[],[[0,1,2],[2,1],[0,1,2],[2,1],[3,1,4],[2,5],[4,5],[4,5],[0,6,7],[4,8,9],[0,10,11],[0,2,12],[0,1,7],[0],[13],[0,3],[7,6],[3,2],[14,1],[7,1,15],[7,1,15],[0,3],[0,2,5],[0,1,3],[0,1,3],[0,1,3],[3,2],[7,1],[11,1,14],[11,1,14],[3,2],[7],[14],[3],[3],[0]]),
 ([0x33333333333333333333333300000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffff00000000],[(0,[(1,0,1)]),(10,[]),(7,[(1,0,1),(1,4,6)]),(29,[]),(16,[]),(4,[(1,0,1)]),(14,[]),(17,[]),(37,[]),(38,[]),(39,[]),(13,[]),(29,[(3,0,1)]),(40,[]),(41,[]),(7,[(1,0,1),(3,4,6)]),(42,[])],[],[[0,1],[2],[3,4],[5,6],[2,7],[0,3],[0,1],[0],[4,8,9],[0,4,8],[0,6,5],[0,7,8],[0,10,6],[0,11],[0,10,11],[0,12],[0,13,9],[0,14,15],[0,8],[0,8],[0],[5,4,6],[12,4],[6,4,10],[7,16],[8,4,10],[5,6],[5,10,8],[4,6,5],[5,6],[6,7,10],[4,16],[8,7,10],[4,6],[4],[6]]),
 ([0x33333333333333333333333300000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000],[(13,[]),(0,[(1,0,1)]),(29,[(1,0,1)]),(29,[(3,0,1)]),(16,[]),(4,[]),(4,[(1,0,1)]),(14,[]),(7,[]),(30,[(1,0,1)]),(17,[]),(1,[(1,0,1)])],[(9,10),(8,11),(32,33),(3,9),(1,11),(2,18),(2,34),(2,66),(6,66),(10,34),(64,80)],[[0,1],[0,2],[2,3,4],[5,6,7],[8,9,10],[0,1,3],[0],[0,4,1000,1001],[1,0],[1,0],[1,0],[0,1,1002,7],[1,0],[0,3],[0,6,1003,1004],[0,9,1005],[0,1,1006],[0,3,1007],[3,4],[3,4],[0,3,4],[3,10,1008,11],[6,7],[0,6,1009],[3,6,7],[0,9,10],[3,9,1010],[0,1,3]])]
def ptopD7 : List StD := [
 ([0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xffffffffffffffff3333333300000000],[(16,[]),(13,[]),(0,[(1,0,1)]),(14,[]),(4,[(1,0,1)]),(17,[]),(1,[(1,0,1)]),(23,[]),(30,[(1,0,1)])],[(32,33),(10,34),(64,80)],[[0,1,2],[2,1],[2,1],[1,2,1000,3],[0,1,2],[2,1],[3,0,4],[5,0,6],[1,0,6],[0,5,7],[6,0],[4,3],[1,3,1001,4],[0,3,4],[4,3],[1,5,8],[0,5,1002],[8,5],[0,1,2],[0],[1]]),
 ([0x33333333000000003333333300000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffff00000000],[(13,[]),(14,[]),(7,[(1,0,1),(1,4,5),(1,1,7)]),(1,[(1,0,1)]),(7,[(1,4,5),(1,0,1),(2,1,4)]),(17,[]),(0,[(1,0,1)]),(4,[(1,0,1)]),(27,[]),(29,[(3,0,1)])],[(32,33),(32,40),(64,80)],[[0,1,1000],[0,2,3],[0,1,1001],[0,4,5],[0,3,5],[5],[3,0,6],[1,0,6],[4,0,5],[5,0,6],[6,0],[1,3,7],[3,4,5],[3,5,8],[3,8,9],[4,1,5],[5,1,7],[7,1],[4,5,1002,9],[4,5],[0]]),
 ([0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffffcccccccccccccccc,0xffffffffffffffffffffffff00000000],[(1,[(1,0,1)]),(0,[(1,0,1)]),(13,[]),(14,[]),(4,[(1,0,1)]),(7,[(1,0,4),(1,0,1),(1,4,5)]),(17,[]),(16,[]),(29,[])],[(32,33),(32,40),(2,18)],[[0,1,2],[1,2],[1,2],[1,2,1000,3],[1,2],[1,2],[0,3,4],[0,5,6],[0,2,7],[0,6,8],[0,7],[4,3],[2,3,1001],[4,3],[4,3],[2,5,6],[5,6,1002,7],[5,6],[2,0,6],[6],[0,2]]),
 ([0x33333333333333333333333300000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffff00000000],[(0,[(1,0,1)]),(13,[]),(1,[(1,0,1)]),(29,[(1,0,1)]),(29,[(3,0,1)]),(4,[(1,0,1)]),(14,[]),(7,[(1,4,5),(1,0,1)]),(17,[]),(28,[]),(16,[]),(42,[]),(30,[(1,0,1)])],[],[[0,1],[2,3,4],[5,6],[7,8],[0,3],[0,1],[0],[0,1],[0,1],[0,1],[0,9,6],[0,1],[0,1],[2,6,5],[2,8,9],[1,10,2],[2,9],[2,10],[5,6],[1,9],[4,6,5],[5,6],[1,8,9],[4,11],[12,8],[1,4],[4],[1]]),
 ([0x33333333333333333333333300000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000],[(0,[]),(0,[(1,0,1)]),(13,[]),(29,[]),(29,[(3,0,1)]),(29,[(1,0,1)]),(16,[]),(4,[]),(4,[(1,0,1)]),(14,[]),(7,[(1,4,5)]),(30,[(1,0,1)]),(17,[]),(1,[(1,0,1)])],[(32,33),(2,66),(10,34),(64,80)],[[0,1,2],[3,4,5,6],[7,8,9],[10,11,12],[0,1,2,4],[0,1,2],[1,2],[1,2],[1,2],[1,2,1000,9],[1,2],[8,6,9],[11,6,12],[2,6,13],[4,6,1001,13],[8,9],[2,8,1002],[4,8,9],[2,11,12],[4,11,1003],[2,1,4]]),
 ([0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffccccccccffffffffcccccccc,0xffffffffffffffffcccccccccccccccc,0xffffffffffffffffffffffff00000000],[(29,[(1,0,1)]),(0,[(1,0,1)]),(16,[]),(4,[(1,0,1)]),(14,[]),(7,[(1,1,4),(1,0,4),(1,0,1)]),(17,[]),(33,[]),(13,[]),(28,[]),(35,[]),(32,[])],[],[[0,1,2],[1,3,4],[1,5,6],[1,4,7],[1,2,8],[1,8],[0,2],[0,2],[0,2],[0,2,9],[0,2],[3,4],[3,4,10],[2,3,4],[3,4],[4,5,6],[2,5,11],[5,6],[0,2,4],[0,1],[1,4]]),
 ([0x33333333333333333333333300000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffffccccccccffffffffcccccccc,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffff00000000],[(0,[(1,0,1)]),(13,[]),(29,[(1,0,1)]),(28,[]),(4,[(1,0,1)]),(14,[]),(7,[(1,1,4),(1,0,1)]),(17,[]),(7,[(1,1,4),(1,0,1),(3,4,7)]),(16,[]),(29,[(3,0,1)]),(1,[(1,0,1)]),(32,[])],[],[[0,1],[2,3],[4,5],[6,7],[0,2],[0,1],[0],[0,1],[0,1],[0,1],[0,3,5],[0,1],[0,1],[4,3,5],[8,3,7],[1,9,10],[7,3,11],[11,9],[4,5],[1,3],[4,5],[4,3,5],[1,3],[8,12],[8,3,7],[1,0,3],[0,7],[1]]),
 ([0x33333333333333333333333300000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000,0xffffffffffffffffffffffffcccccccc],[(0,[(1,0,1)]),(13,[]),(29,[(1,0,1)]),(16,[]),(4,[(1,0,1)]),(14,[]),(30,[(1,0,1)]),(17,[]),(28,[]),(29,[(3,0,1),(1,0,1)]),(1,[(1,0,1)]),(27,[])],[],[[0,1],[2,3],[4,5],[6,7],[0,2],[0,1],[0],[0,1],[0,1],[0,1],[0,8,5],[0,1],[0,1],[4,3,5],[6,3,7],[1,3,9],[7,8,10],[9,3],[4,5],[1,8],[3,5,4],[4,5],[1,7,6],[3,11],[6,7],[1,0,3],[3],[1]]),
 ([0x33333333333333333333333300000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000,0xffffffffffffffffcccccccccccccccc,0xffffffffffffffffffffffff00000000],[(0,[(1,0,1)]),(13,[]),(29,[]),(16,[]),(4,[(1,0,1)]),(14,[]),(7,[(1,0,4),(1,0,1)]),(17,[]),(33,[]),(7,[(1,0,4),(1,0,1),(3,4,7)]),(29,[(3,0,1)]),(35,[])],[],[[0,1],[2,3],[4,5],[6,7],[0,2],[0,1],[0],[0,1],[0,1],[0,1],[0,8],[0,1],[0,1],[4,3,5],[9,3,7],[1,3,10],[7,8],[10,3],[4,5],[1,11,4],[3,5,4],[4,5],[1,7,9],[3,8],[9,7],[1,0,3],[3],[0,1]])]
def ptopD6 : List StD := []
theorem ptopI6 : LevelN ptopR ptopT 6 ptopD6 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC7x0 : levelOK ptopT ptopZ 6 (ptopD6.map Prod.fst) ((ptopD7.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC7x1 : levelOK ptopT ptopZ 6 (ptopD6.map Prod.fst) ((ptopD7.drop (1*8)).take 8) = true := by decide +kernel
theorem ptopI7 : LevelN ptopR ptopT 7 ptopD7 := levelStep ptopB ptopY ptopI6 (chunks 8 ptopD7 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC7x0
  · exact ptopC7x1
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x0 : levelOK ptopT ptopZ 7 (ptopD7.map Prod.fst) ((ptopD8.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x1 : levelOK ptopT ptopZ 7 (ptopD7.map Prod.fst) ((ptopD8.drop (1*8)).take 8) = true := by decide +kernel
theorem ptopI8 : LevelN ptopR ptopT 8 ptopD8 := levelStep ptopB ptopY ptopI7 (chunks 8 ptopD8 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC8x0
  · exact ptopC8x1
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC9x0 : levelOK ptopT ptopZ 8 (ptopD8.map Prod.fst) ((ptopD9.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC9x1 : levelOK ptopT ptopZ 8 (ptopD8.map Prod.fst) ((ptopD9.drop (1*8)).take 8) = true := by decide +kernel
theorem ptopI9 : LevelN ptopR ptopT 9 ptopD9 := levelStep ptopB ptopY ptopI8 (chunks 8 ptopD9 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC9x0
  · exact ptopC9x1
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC10x0 : levelOK ptopT ptopZ 9 (ptopD9.map Prod.fst) ((ptopD10.drop (0*8)).take 8) = true := by decide +kernel
theorem ptopI10 : LevelN ptopR ptopT 10 ptopD10 := levelStep ptopB ptopY ptopI9 (chunks 8 ptopD10 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC10x0
  ))
theorem ptopL : LowN ptopR ptopT 11 := lowSearch ptopB ptopI10 (by decide +kernel)

def sevenInputs : List Sig := rootsW [0,1,2,3,4,5,6]
def graph : Sig := W ptopT
theorem graph_proper : proper graph := (baseOK_ok ptopB).prop
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


def lowRow (i : Fin 7) : Row := Fin.ofNat 128 (([8, 16, 16, 1, 2, 1, 2] : List Nat).getD i.val 0)
def highRow (i : Fin 7) : Row := Fin.ofNat 128 ((1 <<< i.val) ||| (([8, 16, 16, 1, 2, 1, 2] : List Nat).getD i.val 0))

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
    (lower : Impossible true graph 10 sevenInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 7 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 7 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 12 ≤ gates.length
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


theorem excludes : Impossible true graph 10 sevenInputs.toFinset := by
  intro k small run
  have steps := list_run run sevenInputs (by decide +kernel) rfl
  obtain ⟨q, bank, built, hit, limit⟩ := contraction (observe_proper graph_proper)
    steps (sevenInputs.map observe) Reach.start (fun _ h => Or.inl h)
  have bound := ptopL q bank built hit
  omega

end PEqualNP.Outside.L_meta_11767

theorem PEqualNP.Outside.L_meta_11767 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact PEqualNP.Outside.L_meta_11767.replaceShort PEqualNP.Outside.L_meta_11767.excludes gates o fit correct
