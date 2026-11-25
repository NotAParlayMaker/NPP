import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16935_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace ForestCore


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

theorem restoreInput {α : Type} [DecidableEq α] (U : Finset α) (a : α) :
    (if a ∈ U then insert a (U.erase a) else U.erase a) = U := by
  by_cases ha : a ∈ U
  · rw [if_pos ha, Finset.insert_erase ha]
  · rw [if_neg ha, Finset.erase_eq_of_notMem ha]

theorem restoreInputs {α : Type} [DecidableEq α] (U : Finset α) (a b : α) (hab : a ≠ b) :
    let s := (U.erase a).erase b
    let t := if b ∈ U then insert b s else s
    (if a ∈ U then insert a t else t) = U := by
  have member : b ∈ U.erase a ↔ b ∈ U := by
    rw [Finset.mem_erase]
    exact ⟨And.right, fun h => ⟨Ne.symm hab, h⟩⟩
  have inner : (if b ∈ U then insert b ((U.erase a).erase b) else (U.erase a).erase b) = U.erase a := by
    by_cases hb : b ∈ U
    · rw [if_pos hb, Finset.insert_erase (member.mpr hb)]
    · rw [if_neg hb, Finset.erase_eq_of_notMem (fun h => hb (member.mp h))]
  dsimp only
  rw [inner]
  exact restoreInput U a

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
      rw [kept_fin, kept_fin, er]
      simpa only [ka, kb, decide_eq_true_eq] using restoreInputs U a b hab
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
      rw [kept_fin, kept_fin, er, he, Finset.erase_insert_eq_erase,
        Finset.erase_insert_of_ne (Ne.symm hab), Finset.erase_insert_eq_erase]
      simpa only [ka, kb, decide_eq_true_eq] using restoreInputs U a b hab
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

end ForestCore

open ForestCore

private def packedWords : List Nat → Nat
  | [] => 0
  | w :: rest => w + (packedWords rest <<< 64)

private def twice (v : Nat) : Sig := BitVec.ofNat 512 (v + (v <<< 256))

private abbrev sampleWidth : Nat := 47

private def negSample (i : Fin sampleWidth) : Row := ⟨32 + i.val, by
  have h : i.val < 47 := i.isLt
  omega⟩

private def posSample (i : Fin sampleWidth) : Row := ⟨32 + sampleWidth + i.val, by
  have h : i.val < 47 := i.isLt
  change 32 + 47 + i.val < 512
  omega⟩

private def columns (w : Sig) : BitVec sampleWidth × BitVec sampleWidth :=
  (BitVec.ofNat sampleWidth (w.toNat >>> (32 + sampleWidth)),
    BitVec.ofNat sampleWidth (w.toNat >>> 32))

private def goalFive : Sig := twice (packedWords [0xeac8e888, 0x3fffffffffff8000])

private def inputFive (i : Fin 5) : Sig :=
  (![ twice (packedWords [0x9248aa99aaaaaaaa, 0xffe0301ffff8874]), twice (packedWords [0x2c951526cccccccc, 0x3203fffe03ffa509]), twice (packedWords [0xc966d9d4f0f0f0f0, 0x3c03fcfffcc05a4e]), twice (packedWords [0x11bb6668ff00ff00, 0x3ffc00ffff007793]), twice (packedWords [0xe7c38070ffff0000, 0x3fffff0000007fe7]) ] : Fin 5 → Sig) i

private def rootsFive : List Sig := List.ofFn inputFive

set_option maxRecDepth 20000 in
private theorem sampleSep : Sep goalFive sampleWidth posSample negSample columns := by
  refine ⟨by decide +kernel, ?_⟩
  intro w i
  simp [columns, posSample, negSample, bit, BitVec.getLsbD_ofNat,
    BitVec.getLsbD, Nat.testBit_shiftRight, i.isLt, Nat.add_comm, Nat.add_left_comm]

private def clear (ws : List Sig) : Bool :=
  covered false columns ws == BitVec.allOnes sampleWidth

private theorem clear_required {k : Nat} {ws : List Sig}
    (h : Live true goalFive k ws.toFinset) : clear ws = true := by
  have good := cover_required h sampleSep
  simpa [clear] using good

private def fld (v w i : Nat) : Nat := (v >>> (w * i)) &&& (2 ^ w - 1)

private def bsr (read : Nat → Nat) (h : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if lo + 1 < hi then
      if read ((lo + hi) / 2) ≤ h then bsr read h fuel ((lo + hi) / 2) hi
      else bsr read h fuel lo ((lo + hi) / 2)
    else lo

private def wireHash (w : Sig) : Nat :=
  ((w.toNat % 4294967296 + 317) ^ 3 % 11400714819323198549) + 1

private def stateHash (ws : List Sig) : Nat := (ws.map wireHash).sum % 4294967291

private def proofCount : Nat → Nat
  | 2 => 4
  | 3 => 41
  | 4 => 665
  | 5 => 676
  | 6 => 40
  | 7 => 1
  | _ => 0

private def stateWidth : Nat → Nat
  | 2 => 34
  | 3 => 44
  | 4 => 54
  | 5 => 64
  | 6 => 64
  | 7 => 54
  | _ => 0

private def hashBlocks : Nat → Nat → Nat
  | 2, 0 => (packedWords [0x52f922e027452244, 0xc8fa1aea65ea6c74])
  | 3, 0 => (packedWords [0x812094a0353336d, 0x23ce7d470f665da4, 0x2ae14dc0288bddaa, 0x301967f32b28df07, 0x4c1af554323736f8, 0x50aa96344c769770, 0x5c5e235358570741, 0x776eb7a46b3fcbd7, 0x7d6782bd799d01e4, 0x849e93e47f260517, 0x8cb4540388b1912c, 0x9a2af9529471030e, 0xa44701649c5dddf9, 0xbf0570dab633a3b7, 0xcda40541cbfad747, 0xd3136296d2bb94f1, 0xd53aa673d3bf05df, 0xd63eb03fd624e0a6, 0xe778d229e06f5d80, 0xf8842b0ff37d3512, 0xfbaf90e2])
  | 4, 0 => (packedWords [0x9ca9d90075a167, 0xe6885300a849a7, 0x173bc0001457bc0, 0x310509702319716, 0x368ff950316841a, 0x3dc1a8b03ab59ce, 0x530ea260438f4a3, 0x597c3b6055938bb, 0x5a760f805a2405c, 0x5f4fa1505d9adbf, 0x679db9b063181ea, 0x6dd25330688d905, 0x7278b7706f0c43e, 0x74519ca07341823, 0x7deeee00791f648, 0x843b8e6082ad855, 0x8ea117d0876ed40, 0x9abe7d5095ccf93, 0x9f224ba09e930f4, 0xa6683bc0a15d3f4, 0xb3a93790b058bb0, 0xb94f0260b74f8ce, 0xc1e599f0bf8aec5, 0xce7195a0c92f586, 0xe16b7130d55f2cc, 0xe6c66b90e3d7099, 0xedff4ed0e6f8260, 0xf81f1f10f40f2f7, 0xfc475ba0fc441be, 0x105810c210504a05, 0x114810e510a847af, 0x121a80cf11a9a1f3])
  | 4, 1 => (packedWords [0x129f41d81296ec40, 0x13768dc01331958d, 0x147cbcf913f21917, 0x1560809114ac00df, 0x15948db9158240b6, 0x169803691625d36b, 0x1711f43b16d3c1f5, 0x1808c55b17e664e5, 0x182f44a6182141c0, 0x19a32617197bb962, 0x19f1b99a19d3651c, 0x1a7244f01a1ee087, 0x1aba1bc81aa12b77, 0x1bc147b71ba831cb, 0x1c3b8f731c2bf53c, 0x1c7da0db1c6a7d05, 0x1d5d3b651d3cb0d1, 0x1e0d9e491d7b34c4, 0x1f717e0e1f3b260d, 0x209fe2f5204da5ce, 0x2125ea91211ba760, 0x21924acd217fa049, 0x2272887b21a27334, 0x2339ecbf22a9a4bb, 0x236d7361236a4b84, 0x241cfb2a23de5377, 0x252aa89424c097cb, 0x2574f9f82532a912, 0x2698ed5126708c5d, 0x273d217326ce35ca, 0x27c6ebfd27872dab, 0x280182732800b5b2])
  | 4, 2 => (packedWords [0x2896b2642802f6e5, 0x294cde3528c486b3, 0x29d10fb5294e05b0, 0x2bb68ece2b851206, 0x2c6737142c118dc9, 0x2cc6eb242cb65085, 0x2db09c8e2d046e52, 0x2ea8b1712dd72d2c, 0x2f59ee892f27f6bb, 0x30d9edcf30a3341d, 0x334dbfb232081d54, 0x3473e809343d824a, 0x34ecfe11349f78f7, 0x35e0a64d35511437, 0x368d105a36886b3a, 0x36ea762736de1890, 0x377d64fc375f6b0b, 0x3857e37237bae24b, 0x38c9e5973859f198, 0x3ac0271938efeb8a, 0x3b181e6a3ac4fbaf, 0x3baddb543b88739c, 0x3c9ebae43bbca39a, 0x3ce343633cd6ea7b, 0x3d48d5de3d341626, 0x3e0ded0d3d87af99, 0x3ef3ef483e55be06, 0x3f7421f63f1aec60, 0x3fc0fe103f9eb8a0, 0x4059177e3ffaffc0, 0x4065a7ba406282a3, 0x40ba089040700021])
  | 4, 3 => (packedWords [0x41aca8734108647f, 0x41d8960741cba8cc, 0x43f4502f4290a251, 0x4591f839449ff378, 0x461099324593f733, 0x471f500c46bb6fef, 0x475d9be4471f9dd8, 0x4ab664734995561c, 0x4b95e58a4ab9e1d6, 0x4c1996d44bb40a51, 0x4cb4a6c74c892b04, 0x4d61da174d03a416, 0x4de4815a4dc6db3d, 0x4ee0f7414ea3e6ed, 0x5010741d4f182773, 0x507bfbae503c7faa, 0x50f6228f5092bda8, 0x51a818be519b3e44, 0x520ac64e51dea085, 0x545c3b7c53f12807, 0x550cde4f54cfbb1d, 0x5557974355116473, 0x55e6cace55b7a781, 0x56562c0756289f72, 0x575b2ef056db2702, 0x587cea0d57fe0e15, 0x58d762e258ce3aa9, 0x5949011d59288d56, 0x5a178b6a59850030, 0x5a9424a45a1f7c67, 0x5ba837b65ab7be51, 0x5c1092315bf5ba5c])
  | 4, 4 => (packedWords [0x5cc7026d5c6b3c2e, 0x5d365e835cdc045c, 0x5d63656f5d4cb789, 0x5e3c6ad55e244f13, 0x5eae6b375e968df6, 0x5f01f2945ed8300b, 0x5f8f75875f037abb, 0x60eec92260a883c3, 0x615e2a5b6152fbcd, 0x63116d4d61ef38c5, 0x64019bde63399ec5, 0x64a3074e649e39c8, 0x655c93b564c81592, 0x65c623e565950b09, 0x6680888666257832, 0x6970997a674b60fd, 0x6a407dab6a0e8d5c, 0x6aeded086ac004bf, 0x6d882d5b6d72e153, 0x6e31c7f56e074593, 0x6ee513886e6bbb3b, 0x6f66f7c56eeab927, 0x70b8a0c76fd008e0, 0x710a38f270d2403a, 0x713c4ffe7135ca59, 0x71f91de671a8a934, 0x72c467897250ec2e, 0x73bc24d6739a64c7, 0x74700fb2740cae53, 0x755d83fb7486b988, 0x7662d2cf763468e7, 0x77215f537682fb5b])
  | 4, 5 => (packedWords [0x7818037b7721e758, 0x786a6b0b782b9e43, 0x792ecc8078fd6b56, 0x79b61754793c5256, 0x7acbf2c17a802edf, 0x7b8112d57b6c3190, 0x7ca8ac737c0a651f, 0x7cf349797ce9014c, 0x7dfe2ad37d4fc6cc, 0x7e685dff7e15ee1a, 0x7f35bdb57efb7aec, 0x7ff9bdfc7f36036c, 0x806fbfec801c3034, 0x816a9d28816803ff, 0x8266444b82129779, 0x8323522182d6aab1, 0x8408926483eb80ba, 0x85a857b184707842, 0x865d1cba865b5735, 0x87fef2e38796afbc, 0x8915126c8850ebc8, 0x8927be2189200fff, 0x893a23b08931e3fc, 0x89758351896c58aa, 0x8a18cf5b8983e514, 0x8aaedfc48a6d9259, 0x8b13ff3f8ac43fc7, 0x8b80d5d38b71d14e, 0x8cd7846e8cbeffa2, 0x8f7c42a28d5f8260, 0x8fee7a148fe9ff7f, 0x902044bd8ff19ad6])
  | 4, 6 => (packedWords [0x91ae276a90466345, 0x93fcb55493786b0e, 0x94054ef89403ce8b, 0x944ce93f943a4e02, 0x971d47ec95a2265a, 0x97c2665a973dec93, 0x983d8b9397fe4aab, 0x9971df1398a0ae10, 0x99d88e9c99d106cb, 0x9a0cfedf99f149e9, 0x9c4871539c1a08f9, 0x9cea71339c64e372, 0x9d560f849cf4822b, 0x9d6511589d61e07c, 0x9e9404539d918d4c, 0x9f4ccbb89f38a72e, 0x9fb83e1e9f8354ae, 0xa0e550c3a0149683, 0xa18de883a16620c3, 0xa273c5d2a21ee21e, 0xa2dc3b98a2cad8ea, 0xa309690aa2e0efb5, 0xa329c645a32598e0, 0xa4718c18a38579ef, 0xa542be36a4f2c29a, 0xa6f4eb69a69c07a3, 0xa77a75e9a73dc156, 0xa7ec1615a7e40cd2, 0xa827e61aa7ef2904, 0xa8409f5aa82fef80, 0xa8920214a85e3446, 0xa941ce75a8d2bcd7])
  | 4, 7 => (packedWords [0xa98f4f2fa9751320, 0xaa988dcaaa4aa252, 0xaad5b7d7aab1659b, 0xab622ca1aad7e136, 0xac95a13eab91c5e6, 0xac99a56bac9855d6, 0xace8413cace5797e, 0xad97aa2cacea5e11, 0xae274328ae0977ad, 0xafb7e20fae909676, 0xb07fcdddb010c727, 0xb0a95465b085a20c, 0xb22fbc48b1231126, 0xb29f1079b271ba37, 0xb34fc013b337bb2e, 0xb4d159fcb3d0b692, 0xb516f76eb50d5f6b, 0xb7a23f18b6fd4753, 0xb7ecd5c9b7d7de53, 0xb85045b9b7f02c09, 0xb9654d85b8e3089d, 0xb9dc4651b9d90ad6, 0xba9fb585b9f8e6c6, 0xbae58791babb3df6, 0xbc243b58bb9984bf, 0xbc78d2babc58e98d, 0xbd45f0f6bcee43bd, 0xbd57224abd566616, 0xbd93cbc0bd6b0bc6, 0xbe2da087bdc2e331, 0xbf229a7bbef966f2, 0xc0237a0ebf7903b5])
  | 4, 8 => (packedWords [0xc124abffc047f9c8, 0xc1baeed4c18af67a, 0xc300eb09c1e3516d, 0xc401807ac3743418, 0xc562960ac4b6f169, 0xc6c8bdf6c5ae97ab, 0xc7157862c7156d3e, 0xc8bec9b6c7f075dd, 0xc8fcaf2ec8ed59ab, 0xc94cebd6c9308dc6, 0xc97c23e8c957029a, 0xca5fffedc9c68f2f, 0xcb6f8315cb10cc4d, 0xcca46d73cb9ec5c7, 0xcf39ff0dcd3f10e7, 0xcfa8297fcf859766, 0xcfd96bcfcfc6ed05, 0xd03c170acff911f8, 0xd0c5ad3ed091130d, 0xd10712bad0fbce8b, 0xd1dfd3b7d15aab76, 0xd2ae2af8d21eb6d8, 0xd2bb94f1d2b315ba, 0xd3136296d2d051fb, 0xd4c935cdd3da2fc1, 0xd63758aad4dd712b, 0xd7d63cd7d676e50e, 0xd82c3eb8d82b2197, 0xd883c29ad83959ce, 0xd978992dd8bb88ad, 0xd9fb9192d9ec4457, 0xdae90078d9fd317a])
  | 4, 9 => (packedWords [0xdbcf216cdb88b4df, 0xdc868fc6dc7fb75b, 0xdd9067fddd2dbb1b, 0xdf83a3e6def11792, 0xdfdf3cfcdfa8ca45, 0xe0ba1cf5dffca37f, 0xe18316bfe1157e3d, 0xe27ba29fe27564e0, 0xe50b7ddde40d787d, 0xe59ebd64e5181d94, 0xe5ed12b8e5e472c8, 0xe687c52ae625939a, 0xe750366de6a41166, 0xe810f3d6e791f251, 0xe8b2abfae836f37c, 0xe925015fe91f7a4b, 0xe9c37615e9875bf1, 0xeab5b282ea120844, 0xec350618ec2c6c4b, 0xecc2ad20ec8d1cae, 0xecce4876ecc567af, 0xed9b5bf2ed7c23df, 0xedc7df24edc6f065, 0xee487051ee033374, 0xeef4139aeebf4d21, 0xef699dedeefaac18, 0xf173bdfaf0c3fe7b, 0xf283f43ff177fcb6, 0xf379c2c7f31da24c, 0xf3db36b3f3daf7a9, 0xf48e9a17f44ca9be, 0xf549ccfdf4a47ece])
  | 4, 10 => (packedWords [0xf5fc1722f5c81e61, 0xf676e470f60af416, 0xf6ab1c12f69f0d49, 0xf76f78ccf6dcaaad, 0xf7baf2c9f7b766bd, 0xf87d5637f80cf1d2, 0xfb356a9cf89682ef, 0xfbb7188ffbb4c17d, 0xfccc48acfc2dc7fb, 0xfd18a463fd0fe682, 0xfd7ff471fd6832c8, 0xffdfa2b2fefd76a7, 0xffee4363])
  | 5, 0 => (packedWords [0xd446fd00bf0792, 0x178b6be00d8c979, 0x1ab4ed90198bfd4, 0x386550d026ce0b4, 0x3e3e9f603897121, 0x438f4a3042e2f51, 0x454383f044da53d, 0x4def28004648cfd, 0x4f5a57b04e4bc24, 0x5a04fc00597c3b6, 0x6730ae2063181ea, 0x6aa86930688d905, 0x7516e4007278b77, 0x8b463650828ebb6, 0x9ad2bd30930d627, 0xae8400909e930f4, 0xba2c20a0b0f22d1, 0xbf258e40bde192e, 0xc7d1ad40c4420e3, 0xd2718f90ce8791f, 0xe2d99480db046e0, 0xe6c66b90e3d7099, 0xeab78040e9f9d81, 0xf569a640f40f2f7, 0x105fff140f8299fb, 0x1094a0781076a947, 0x1136d78210b1dc7e, 0x11e35bc011e1ae3f, 0x1296ec4012369340, 0x13a4dc0713965d99, 0x13b0f5cb13a52674, 0x1408a99b13e2c26e])
  | 5, 1 => (packedWords [0x14d9158f144ffd31, 0x154594c5150dbcca, 0x163540a61568226a, 0x16c01cf61650205d, 0x17133faa16edd72c, 0x17b90679177243b2, 0x18c77bb21804c18f, 0x19c34db61999a4a2, 0x1abc026119d3651c, 0x1b111c7a1ad8ceeb, 0x1ba725261b7b79cc, 0x1d9b83f31ce35249, 0x1eed08401dfec9f0, 0x20c50e7820715483, 0x20f9e41b20e6f309, 0x213f6239213c11b0, 0x21bb5da7216f59e3, 0x21e6486221cb4167, 0x22e0e5cc22c802c2, 0x2316c5bf22e5a0ec, 0x23f478f9236d7361, 0x256084ff241cfb2a, 0x260b5bbc25f9343c, 0x2659b933262ea2a3, 0x273509a42662c7eb, 0x2806f09527ffd08d, 0x297d4dc128d4cb8c, 0x2a080200298062bd, 0x2b2e5b932afdf653, 0x2d1232212b53998f, 0x2e42a8dc2db15ab6, 0x2f8ea3252f8a3734])
  | 5, 2 => (packedWords [0x2ff2727f2fd0cd8f, 0x309d493c30271578, 0x314625b530b4dec5, 0x32081d5431681904, 0x3340f63132127159, 0x3473e80933bc8aa3, 0x34aafa34349f78f7, 0x35a49a81354f518b, 0x36413a7735ec2e47, 0x381e267637ebcc7b, 0x38d188203877580a, 0x3a04cded394f0b61, 0x3a87a9913a4db59d, 0x3aa57c413a8fbdd8, 0x3baddb543b52ea59, 0x3beb1b3b3baf346e, 0x3c1b979c3c068d12, 0x3d1a6fad3c2f871c, 0x3d46c4a33d3fa4e6, 0x3df9098d3d48d5de, 0x400d626d3e1d3cc1, 0x4037dc85400feaaf, 0x40fc0c8b406977c8, 0x4186c917410b67cd, 0x41b94a2041952ada, 0x4280dec841fe91e6, 0x42bffdd242b013f6, 0x449ff37842cc91a8, 0x44c6b06744b3e042, 0x44e515b044cade3a, 0x45eb14bf45c4b5c7, 0x471f9dd84654ee34])
  | 5, 3 => (packedWords [0x482e678b475d9be4, 0x48f6f7a448438667, 0x4a709ce04a2f4c00, 0x4ad6b9274aac85b2, 0x4bb40a514b854bcf, 0x4c6239094c575640, 0x4ccf84504c8f5e13, 0x4d8272d24ced2c8b, 0x4e412a254e078918, 0x4f96b6924ed83621, 0x50cc8020504622ee, 0x51e9740451a818be, 0x52ad79a352050584, 0x5360ade25338e469, 0x54d0ee5453c8b640, 0x55b349815596b5d2, 0x5626b0a055dc9bac, 0x5690d2d0566f4421, 0x56ba9dc956ae0fce, 0x56e6324556d4ccbe, 0x587cea0d5837a771, 0x58d762e258952dcc, 0x5937f60558df3ca6, 0x5a1b1e2b59cde723, 0x5b06b76c5a4ec973, 0x5b9d146c5b8ac1f5, 0x5c59e68f5c15bf09, 0x5cf806145cf32d4a, 0x5d6d14955d3e0bc5, 0x5e244f135d8ed539, 0x5f037abb5ef40199, 0x5fa75fa45f749c68])
  | 5, 4 => (packedWords [0x602fd9946026fc8b, 0x60850fcb606f1764, 0x61f199a460d95fbf, 0x62c8d803620abaf3, 0x6538cc8263c0640f, 0x65c7c50a65950b09, 0x6645427765f4605f, 0x66a7a633669fcf8b, 0x6863a95e6830e630, 0x68c944ef6896e7d2, 0x6aab5c9f69ba4750, 0x6b5480dc6ad99a26, 0x6cb916f66bd0f66d, 0x6cefd8816cdfe0ed, 0x6e52518f6e492061, 0x6f0e078e6ee51388, 0x714e738b6f97ca68, 0x7206195a71cdcce5, 0x7207a4e37206bf81, 0x726b03aa7221f452, 0x72dca75b7290cd99, 0x73b42e49738f10a9, 0x743949ee74083300, 0x7662d2cf75a04bce, 0x76da50b076bd5f25, 0x77bcf7857738dacd, 0x784b97fb77d47116, 0x7937ed1478667852, 0x796274eb79463b2b, 0x7b024409798d8707, 0x7b9d9a217b7480d5, 0x7bcdeac17bad1ac6])
  | 5, 5 => (packedWords [0x7c01f79a7be64c1e, 0x7c24610f7c08559f, 0x7cf349797ce9014c, 0x7df7ceed7df5e8b6, 0x7e61b9f67df9e071, 0x7e9e460e7e87bcca, 0x7eb3b17d7e9f86f1, 0x7ecb569e7eb4f1ed, 0x7efb7aec7ee588ef, 0x8089ce1a7ff95ad2, 0x81041e2180bd37c7, 0x81e55e9e816803ff, 0x8345c673821f33f5, 0x83bf2f3c83b76183, 0x83faa66683c177e5, 0x841ed09f84089264, 0x8471fecf8437239d, 0x85a857b18475393a, 0x866bbc5385e1d8cf, 0x86c76e76867ab7e9, 0x870c9cce86f82632, 0x87eab66187d8d5be, 0x883a422f87fca747, 0x885a4c2688596f7d, 0x8a654fce8a5f3aa0, 0x8aa96fc28a8f24c0, 0x8baa45c48b5c9b9e, 0x8cbeffa28c07ef0e, 0x8d5f82608d4cf39c, 0x8dc027508dbfe580, 0x8e5857c38e536565, 0x8f00da288e5f89ff])
  | 5, 6 => (packedWords [0x9002bf3a8f565d23, 0x909fe45890466345, 0x914abb15914950db, 0x91adfed0919a09c2, 0x92b576a2920d77f5, 0x94ce54ed93a6d434, 0x95953dc495347967, 0x962aa0ee95a2265a, 0x972ee11e96a71717, 0x975d3e98974af23a, 0x97de401497af235e, 0x9919ea489841ff8d, 0x99d88e9c9954f765, 0x9c1a08f99aa161cc, 0x9ca5b4119c3f20ff, 0x9cfb50f09cc3b6ac, 0x9f371b7c9d5deb70, 0xa04053ad9fd05eee, 0xa09c0b6da0773dd0, 0xa16b5978a0e297f4, 0xa225e923a1c8f3af, 0xa27d1168a27bffe0, 0xa2d16af8a2868b35, 0xa4718c18a35d85cf, 0xa5acf0cba50cc635, 0xa632c304a622284d, 0xa796b108a67c413a, 0xa92e6c54a8c27712, 0xaa631ff0aa1755e2, 0xaa8d558faa6e1756, 0xaaa68947aa988dca, 0xab422172aad0bf80])
  | 5, 7 => (packedWords [0xac770132ab857eb6, 0xace5797eac85a4d4, 0xad2588c4ad01bef0, 0xae1c098cadaa24d8, 0xae66a762ae200f30, 0xaef8d638aea6f72c, 0xaf457bb2af4180b5, 0xb0b6a699b053a799, 0xb1231126b112a7f7, 0xb193054fb141510c, 0xb2341286b20ea410, 0xb34fc013b2999a34, 0xb47ce1f6b3bec7d5, 0xb59f82c8b4f5b803, 0xb60873bab5a56e32, 0xb6d3f309b651c1bd, 0xb716fbc5b6fa4b4a, 0xb8adef9ab86ee31d, 0xb9622319b949f7a8, 0xb978edc8b9756044, 0xb9dc4651b9cc58be, 0xbabb3df6ba405fca, 0xbd46323bbc4bf139, 0xbd57224abd4a3902, 0xbdb0dae7bd683074, 0xbe298282bdf108f8, 0xbe42c7abbe41035f, 0xbeee6af4be5959fd, 0xbf4abc42bf219a7b, 0xc047f9c8bfc6a258, 0xc08c84dcc06657c5, 0xc16e1554c0c4a7b8])
  | 5, 8 => (packedWords [0xc231817cc1e3516d, 0xc37ba310c249b799, 0xc3add593c3ab34b8, 0xc3eb0449c3e7db0f, 0xc4c83819c401807a, 0xc5752664c540b1e6, 0xc65ba8ecc5bb48ed, 0xc7156d3ec6c483a7, 0xc72fe13cc71cd5c1, 0xc83688cfc7787906, 0xc8d2f0dfc8c9f7de, 0xc940d624c8e6823e, 0xcacbb673c9b78ea3, 0xcb566ab2cb503469, 0xcbfad400cbe31465, 0xcd1e664bcd00059c, 0xcd3f10e7cd2e7595, 0xcdad6b94cd5e387b, 0xce56ce4acdf78e9d, 0xceffc368cee2ce6b, 0xcfa8297fcf5067cb, 0xcffb3e88cfd841ad, 0xd036bf95d003d3b2, 0xd0fbce8bd091130d, 0xd2141928d10712ba, 0xd26b2de3d21eb6d8, 0xd2cb6189d28cb4ff, 0xd2effa4cd2cb636b, 0xd51b124dd342f859, 0xd6ab7c17d57431c5, 0xd7ddaaa3d73f9a71, 0xd83d9fd1d8367389])
  | 5, 9 => (packedWords [0xd8dde12cd883b4aa, 0xd9dc521dd96336ef, 0xda855669da156a88, 0xdbc7bf41dbba4e17, 0xdd2dbb1bdcad6cfa, 0xdd9abc20dd428be0, 0xde309760dddebfc9, 0xdf1e0686de9e9f8c, 0xdfac0006df7bd4fe, 0xe0709cc9dfb7c4ba, 0xe16e71b5e0ba1cf5, 0xe20e0942e187e0e4, 0xe4f31e39e3b46a82, 0xe52663ade51743e9, 0xe58ee50ee58a8799, 0xe93f3aace87db0bb, 0xe99d0924e993b5c9, 0xea387ca4e9cdfe2f, 0xea956718ea6d10db, 0xeb77423feab5b282, 0xec1d2f10ec025d3f, 0xec350618ec2e7707, 0xec5c8f96ec559e47, 0xed5792baece82c4c, 0xee26c682edc6f065, 0xee5e6218ee487051, 0xef14d065eef0f017, 0xf08148dbef172b73, 0xf1a87b25f18205fa, 0xf26a22f3f1b961cb, 0xf3011898f2e9d7a6, 0xf379c2c7f327c0be])
  | 5, 10 => (packedWords [0xf4bc4899f48c8b87, 0xf5960fb0f56115f4, 0xf67dc3bcf674d05e, 0xf751c93df6f1ec67, 0xf77bc91cf76f78cc, 0xf80b148af7eef8b0, 0xf8fd6b77f8757135, 0xf9c4a9f4f9b3e86c, 0xfa48e414f9e54ef5, 0xfa7d382efa653ecb, 0xfb6bba69fb36b7cc, 0xfba6114bfb9248e7, 0xfbedd688fbcdb9c3, 0xfca5baaffc98ad45, 0xfcf8c55ffcf3b631, 0xfdb17725fda33dfa, 0xfed54b41fdc07549, 0xff31db73ff0d2052])
  | 6, 0 => (packedWords [0x1ba7252604e4bc24, 0x2316c5bf22e5a0ec, 0x2db15ab6298062bd, 0x3a8fbdd82fd0cd8f, 0x44c6b0673aa57c41, 0x4c8f5e1345c4b5c7, 0x52ad79a34ced2c8b, 0x59cde72353c8b640, 0x6e4920615a4ec973, 0x71cdcce56f97ca68, 0x7290cd997206195a, 0x7866785272dca75b, 0x83c177e57ecb569e, 0x909fe4588e536565, 0x97af235e914abb15, 0xa796b108a35d85cf, 0xb053a799aa6e1756, 0xcd2e7595be42c7ab, 0xd96336efceffc368, 0xf3011898f1a87b25])
  | 7, 0 => 0x43f4502f
  | _, _ => 0

private def packedBlocks : Nat → Nat → Nat
  | 2, 0 => (packedWords [0x556444dc2559113, 0x156444dda5591137, 0x76])
  | 3, 0 => (packedWords [0x591148c5e1559114, 0xc5a85a11147559a5, 0x9114911a35590348, 0x20e444a94809c755, 0x1147cd9555911491, 0xa85590246f99a559, 0x148b995559114911, 0x2444a949d6024f91, 0x4809e161156496a0, 0x4f9114981a8558d0, 0x9d5a8559034911fc, 0x58d047cd90559114, 0x19be559114875a85, 0x9114875905591147, 0x9d555911496a024f, 0x20487dc855911477, 0xa8559114809e1559, 0x148c5c8559114879, 0x8559034912024f11, 0x48c1a8559114981a, 0x444a94809e055911, 0x911a8558d0491202])
  | 3, 1 => (packedWords [0xf911491191558d04, 0x9c6444a9499e024, 0x4a94911b4558d048, 0x1a3559114911bf44, 0x11487de15591147f, 0xa85590348c5a8615, 0x9bd])
  | 4, 0 => (packedWords [0xd6026a156444ce5, 0x59115912196a1563, 0x6556445675809e45, 0x99e559115912026, 0x12024f9111b16448, 0xd6446a156444fc59, 0x4945912025591134, 0x91125d644759a844, 0x9111f0745911a855, 0x1a85f5562c960255, 0x62e809a855911591, 0xd05942026a156445, 0x6c10d6446a156444, 0xa855900591156444, 0x26a156445644809, 0xf36698b55911593a, 0x85809a8559144455, 0x64456446a15630c3, 0x8559115912026615, 0x1558c30e1644809c, 0x473da85591159119, 0x5809a85591138964, 0x25967d809e155911, 0x1a8195911a853511, 0x5594c44560255911, 0x6a1564442a5809e1, 0x912026a181445602])
  | 4, 1 => (packedWords [0x716026a156444535, 0xc385809a8559110, 0x59110596446d1563, 0x9a8559115809a85, 0x9c87195644566f8, 0x56446a1564444758, 0x4545912026955644, 0x1564456448093344, 0x9564cd115809d06a, 0x20262d3e44565a80, 0x62e809a8558c5591, 0x1b5912256a156445, 0x563e96448093e444, 0x56444225911a85fd, 0x26a17b4456316a1, 0x26a156444195912, 0x7599e026a1564456, 0x6445602659564442, 0x8559035809a86015, 0xe559111b1644809a, 0x16a156445085809d, 0x59d5a85591125963, 0x371644809a655911, 0x3303859120255911, 0x5ad564456446a156, 0x6a15644474591202, 0x9120274d3344561f])
  | 4, 2 => (packedWords [0x45644759a8559115, 0x5868594a026a1564, 0xa15645d6446a1112, 0xa168531115912026, 0xa1564445312d6026, 0xd6446a15640c3e56, 0x81b5911a8559111f, 0xd56445602559111d, 0x11128c9d5875a862, 0x9a8585564456026a, 0x6026a1564442b580, 0x645912376a156445, 0x110e964480962444, 0x56444645911a8559, 0x56a156445675809, 0x448093e4445e5912, 0x45809de62d564456, 0x6445644809112446, 0x6444b85809e16695, 0x35591137d6026a15, 0x2779564441b5911d, 0x592da8558c30e160, 0x3d636809a855911, 0x558fa56a1563f8c8, 0x6a156445644891a8, 0x809a355911587df3, 0x8d6026a156445672])
  | 4, 3 => (packedWords [0xd60271911244645, 0x78385875a8559111, 0x59113e96446a1564, 0x39a8559115981a85, 0x11fc791564456538, 0x56026b9a85591159, 0x9115912027715644, 0x156445676809a855, 0x156444745911f76a, 0x2346a1564456316a, 0x6446a15644450598, 0x275809a855911075, 0x56445602559111c8, 0xa8559115912026cd, 0x2a6a1563e963f809, 0x44809a8558c75912, 0x15912246a1564456, 0x11d16446a1564651, 0x8559115952025591, 0x6a1564456447eda, 0x56a1564443859120, 0x598e0274d5644567, 0x4456446a156340c3, 0x24464587e1d6a156, 0x69d564456446fd11, 0x6a1564447c591202, 0x7f1a855911321602])
  | 4, 4 => (packedWords [0x45666809a8559115, 0x44a358ae026a1564, 0xa9334456026a1564, 0x9a8559115912027, 0x12016a1564456628, 0xd62e6a18b5591159, 0x9115911e15591111, 0x9111b16317cda855, 0x5a8558fa58ea0255, 0x9a85591107d64476, 0x6026a1563203b575, 0x1459120b6a156445, 0x111b15fc6a156444, 0xa85591159120e559, 0x2559111b9645809, 0x24dd11274145912, 0x15912226a1564456, 0x110d644809a35591, 0x128c1458b9a85591, 0x26a1112516026a11, 0x26a15647d1159120, 0x5912026a15634d60, 0x516026a156444ad, 0x559115809a84449f, 0x62d5640d63a8098b, 0x809a8444a95911a8, 0x911fc55911191644])
  | 4, 5 => (packedWords [0x4567580956444bb5, 0x447b59c6026a1564, 0xa1564156026a1564, 0x95a8559115912026, 0x120e62d564456027, 0x9644809e25591159, 0x8b25911c85591111, 0x8f3321644809a85b, 0x171559115809a855, 0x202559111e16026a, 0x665809a855911591, 0x115912025d556445, 0x564456445f573559, 0x564ed11596a02791, 0x2559111a9644809, 0x44759a84f9115912, 0x35911a35591112d6, 0xf1916446a15640c4, 0x12a4915912024449, 0x64446c1216448091, 0x47fda85591159115, 0x5912025591136564, 0x4456448097455911, 0x37cda5809a855930, 0x5591108964455911, 0x809d1559115875a8, 0x809a855911079644])
  | 4, 6 => (packedWords [0x45602721564444b5, 0x591158ba02659564, 0xa1112dd644809b95, 0x9a84fd115912026, 0x12026a1564456448, 0xd644809915591159, 0x9115912246a15630, 0x15644566b809e155, 0x1565311159f5fc6a, 0x202559111c55fc6a, 0x644809b455911591, 0x485809c66a156445, 0x111b164462d56444, 0xa855911591210559, 0xd66a156445647809, 0x44809a8558c55779, 0xa580956444921d16, 0x640d66380956444d, 0x8559115912026595, 0x8558d00e16318b9a, 0x26a187559115911a, 0x5912026a15344560, 0x4456026a1112501f, 0x444a55911a85592c, 0x5591112d6026a156, 0x6a156444395935a8, 0x809a8558ea321644])
  | 4, 7 => (packedWords [0xd560274d56444e25, 0x60885912026a1112, 0xa156445644809a83, 0x933444f85911bf6, 0xe6026a1564456448, 0x16026a1564447e59, 0x418596a025591119, 0x91133d6026a15644, 0xda8559115809a855, 0x1b75591110d5c66f, 0x5a85591113022591, 0xbb58ba02559111c9, 0x110896447f156444, 0xa85590758b9a8559, 0xa855911259644809, 0x67809564cd115981, 0x1592e026a1564456, 0x13595fc6a19a5591, 0x1559115809a85591, 0x6444ac06d64b8099, 0x4809a85590e58095, 0x5912027515644564, 0x89644809a85588d, 0x444fa56a15644453, 0x6d15644566f6a156, 0x809ef444a9592e02, 0x809a85591108d644])
  | 4, 8 => (packedWords [0x2d6446a15b4443e5, 0x591156a156515111, 0xa139445644809e35, 0x21564441b5912026, 0x12336a1564456027, 0x56026a1564441f59, 0x4a659be346a15644, 0xd56445644809a844, 0x9a85591159e20268, 0x9a86815644566980, 0x644809a82c888580, 0x415912026a156335, 0x31c96445cd56444, 0x5644474591202559, 0xa855903089675809, 0x70809a8559115911, 0x15809a8559110556, 0x60f96026a1564491, 0x3559115911a8444a, 0x85594340d60260d7, 0x26a184559085911a, 0x5912026555644560, 0x441644809e155911, 0x244645912026a156, 0x6a16044560259d11, 0x87da855911591202, 0x809db6a156445672])
  | 4, 9 => (packedWords [0x7d6446a156525115, 0x58d8598da8559113, 0xf511245644809a85, 0x79a8444945912026, 0x122474d564456027, 0x56606a1564443859, 0x9115912026c15644, 0x13e4456446d18b55, 0x9564447c5912026a, 0x9a85111127564480, 0x644809e855911580, 0x615809a35591103d, 0x795596026a156444, 0xa857d115912026a1, 0x26a156445644809, 0x4480966444645886, 0x159120e444911916, 0xc4456448c9a85591, 0x6444bb5809a85591, 0x268d5644565a8095, 0x4809a8444d859d60, 0x5911a85591112964, 0x3e96026b1564441b, 0x444435911a855948, 0x4447406d6446d156, 0x55911388da580956, 0x9ca316a156445602])
  | 4, 10 => (packedWords [0x456448093e444915, 0x44465809a8625564, 0x59111156446a1564, 0xda8559115911a85, 0x1202559111e56027, 0xd644809a8558ce59, 0x9115809a85591129, 0x9112f5644809b155, 0xd564441959120255, 0x1ba6a1564456025c, 0x5a8559113104b591, 0x1159120255911195, 0x5644564487da8559, 0x11274145809de6a1, 0xa85d956445602721, 0x73809a8559115911, 0xf58fa026a1564456, 0x64456026a1563200, 0x8559115912026f15, 0x85591503d64480da, 0x47f156444745809a, 0x5912024cd112a564, 0x12d6448099655911, 0x44424562d5644474, 0x6a15640d6026a156, 0x68d56444fa59f644, 0x6a1835f556445644])
  | 4, 11 => (packedWords [0xf9642809a8559115, 0x59115911a8444960, 0xa15644566b7f1a85, 0xd1a35591159d6026, 0x12026a1562396448, 0x96446a156444ab59, 0x9115809a85591109, 0x91107d6026a15646, 0x956444af5809a84f, 0x2026595631564480, 0x644809a255911591, 0x115912186a156445, 0x330d667809e4559, 0x563b0c35911a8559, 0xc8559113216446a1, 0x26eda8559115809, 0xf59120264d564456, 0xe2ed644809564447, 0x855911591202558e, 0x26a1564456027f5a, 0x48c5a85591159b20, 0x5912025594144564, 0xe1644809d355911, 0x444715981a8558c3, 0x559110516448c556, 0x6a156444405809c8, 0x912026a155445644])
  | 4, 12 => (packedWords [0x2d6026a167559115, 0x44da59d5a8559111, 0xbd3e445644891564, 0xa9a8558d05912027, 0xbda8559112596448, 0x55a855911388df59, 0x4725986026a15644, 0x9364456448095644, 0x9113d07459120255, 0xa024449119160255, 0x6448097344488596, 0x1159120271156445, 0x56445644809a4559, 0xa8559115972026a1, 0x26a15644564488d, 0xa85f5564441958ea, 0x15911a8559113f55, 0x309d644839a85591, 0x6545115809a85590, 0x8559163e96026a15, 0x380911244645911a, 0x5809a35591127565, 0x1216448095631472, 0x559115911a844494, 0x77956445644811a8, 0x80956444c05809e1, 0x809a8444eb275644])
  | 4, 13 => (packedWords [0x4560e719a8559115, 0x444b5911fc669564, 0x5911191602785564, 0xa15644486599e025, 0x21a8559110896446, 0x56026a156444d758, 0x9115911c86f95644, 0x4ed2596448098f55, 0xda3559115911a844, 0x9a8559110416447c, 0x602725a855911580, 0x1159de026a156445, 0x56445644809b2559, 0xa8559115911fc6a1, 0x2559111dd67b809, 0x26a156481085912, 0x156a183559111056, 0x64456446a1564445, 0x84f9115911c06a15, 0x85591115d602779a, 0x4559111fc6c5809a, 0x59f6027215644564, 0x2c96026a15644452, 0x559115912026a0d8, 0x55911355657809a8, 0x72156531115809a8, 0x809a855911379602])
  | 4, 14 => (packedWords [0x456027e9a8559115, 0x591159e21f6a1564, 0x5911265644809ab5, 0xa156444385911a85, 0x92026a15644566f6, 0x1644809a8444a359, 0x85e5912026a15646, 0x1564456448095648, 0x9564447a5912116a, 0x2026a15634164480, 0x6446a15644448591, 0xa05911a8558fa0c9, 0x54445644809a8444, 0x56444a659ca026a1, 0x31655564456446a1, 0x26a1563300f5912, 0x85809f16a1564456, 0x64756446d1564444, 0x630c385912026a15, 0x26a17755961d6a15, 0x4809735591159120, 0x5809a8559110a164, 0x896446a17e55911, 0x4446f5809a355911, 0x5591136964480956, 0x8099055911591202, 0x809a856556445644])
  | 4, 15 => (packedWords [0x4560268d56445085, 0x441459122c6a1564, 0xa5564456026a1574, 0x55a8559115912026, 0x9a8558ce03d6447, 0x561f6a1563200f58, 0x88859120274d3e44, 0x156445644809a84a, 0x9111fc4359e2316a, 0x2025593744564455, 0x644809562ec60591, 0x145912026a15632d, 0x564456026a111274, 0x564440f5809c8669, 0xa35591125961f6a1, 0x2785564441b5911, 0x256a156444d10896, 0x108964462d564447, 0x85591156a15d5591, 0x855911201663891a, 0x9809a8559115809a, 0x5912025f13344564, 0x4455a85591110419, 0x5591159120a6a156, 0x6a156445644825a8, 0x809d25591159121b, 0x99e02559112ed644])
  | 4, 16 => (packedWords [0x456026a156444295, 0x44e058e9a862d564, 0x59110856446a1564, 0x9a8559115809a85, 0x12025cd113a565a8, 0x16026a156444e159, 0x8435809a8559112a, 0x156445644559111c, 0x9111f01b5912026e, 0x9a3559111d160255, 0x653809a855911580, 0x1156a1564444807d, 0x5644564480997559, 0x56444435809a85a5, 0x7d559111a963a6a1, 0x26a164559115911, 0x45809a84449d19d6, 0xf245644809112a46, 0x6444d2591202444e, 0x26a1564456026a15, 0x46a1564449859660, 0x58c5a85591103d64, 0x271620809a855911, 0x559115912026a111, 0x55933445660809a8, 0x809a85590359d602, 0x911a85f55644562e])
  | 4, 17 => (packedWords [0x45640809a8559115, 0x95115956026a1564, 0x991106d644809a85, 0x591112c225809564, 0x120274d112455a85, 0xd6026a1564442759, 0x9115911a85591137, 0x91303d6027cda355, 0x9562ec5e5809a855, 0x1d76a15644564480, 0x244809564d511591, 0x38500244809112a5, 0x5634124468d56444, 0x56444e45002446a1, 0xbf6a1564456446a1, 0x448095644469594d, 0xa591a026a1564456, 0x11216756a156444f, 0x6444175911a84f91, 0x85591122d6026a15, 0x46a17d558e95809a, 0x5809a85591139564, 0x4456026a15631427, 0x4446c5911e175556, 0x6a15644560271956, 0x6a1564445359d634, 0x911fe6a156445644])
  | 4, 18 => (packedWords [0x4564480956444db5, 0x44a2591202649564, 0x5921445644809a84, 0x9a8559115912025, 0x6a026a1564456638, 0x95fc6a1564444b58, 0x911591202558d317, 0x1564456448097255, 0x9a8559115911be6a, 0x1a8559113f965e80, 0x6076a15644422591, 0x1156a18d5591112d, 0x56445678912024f9, 0x8b559115922026a1, 0xc65591106d602719, 0x44809a8559045809, 0x859b6026a1564456, 0x64455de6a1564444, 0x85591159120d6a15, 0x2721564456757f1a, 0x48095634cbb59ae0, 0x5891a85591138964, 0x445656809a855911, 0x4449d59120256133, 0x444a625961f6a156, 0x6a156491115911a8, 0x809e155911321644])
  | 4, 19 => (packedWords [0x45638809a8559115, 0x59115912126a1564, 0x59112f9668809a85, 0x7d564446f5912025, 0x11a85591113d6448, 0x56026a1564441159, 0x9115912026a95644, 0x46a10564487d9055, 0x9a852d1159115644, 0x9a85591138d64480, 0x644809ef4cd11580, 0x1159120e559111c9, 0x564456447f1564cd, 0x56444dd5876026a1, 0x2645564456446a1, 0x278556444145876, 0xa5912246a15640d6, 0x644560260d564446, 0x6428bb5876026d15, 0x26a1564356448095, 0x4799a85591159ae0, 0x5911a85591110564, 0x44564480956444bc, 0x4441b5912026a140, 0x559111996026bd56, 0x6a1564a111591202, 0x911a85591b0e1602])
  | 4, 20 => (packedWords [0x456026a1564447d5, 0x444e585e026a1564, 0xa1564456446a1564, 0x93e444f2593e026, 0x122a6a15640d6448, 0x55a85591f30c3859, 0x4145809a860d5644, 0x9111d16026a15a44, 0x1564449d58098c55, 0x9e76a1564456316a, 0x6026a17855911580, 0xa957f1a85591106d, 0x111cd64480956444, 0xa855911591202559, 0xa8558ce32164a809, 0x26a185531115809, 0x5809a8559112916, 0x10896446a1563e8d, 0x855911587da85591, 0x6a1564456446a18, 0xf6a156445085911f, 0x21])
  | 5, 0 => (packedWords [0x912026a156444bf6, 0x912026a156444586, 0x912027e1a8559116, 0x9f6447cda8559116, 0x912026a156444f56, 0x912026bda8559116, 0x912026a1564448a6, 0x912026a133444e96, 0x92e44809a8559116, 0x912026a156444d66, 0x912026a156444626, 0x22e809a8559115, 0x912026a1564a9116, 0x912026a156445096, 0x91202559112ec5e6, 0x912026a186444e96, 0x9122a809a8559116, 0x9122f809a8559116, 0x244559111b0435, 0x912026a19c559116, 0x2446a15630c385, 0x912026a1564442f6, 0x244809c8559115, 0x91202791a8558bb6, 0x2026a156444e25, 0x809a855911320746, 0x912026a166559116, 0x912027a9a8559116, 0x912026a1564441f6, 0x912026a1564c9116, 0x26f809a8559115, 0x912026a1564c5116])
  | 5, 1 => (packedWords [0x9fe44809a8559116, 0x912026a156444ee6, 0x911a8559113a4df6, 0x9120277da8559116, 0x912026a1563c85e6, 0x912026a156541116, 0x912026a156444c96, 0x809a8559111d0146, 0x9ae026a1564440f6, 0x91202765a8559116, 0x2026a156444195, 0x267809a8559115, 0x912026a194559116, 0x809a8669564449d6, 0x244809a8559035, 0x911a8559113f8c86, 0x912026a156444f76, 0x911a8559110e0226, 0x912026a1564f5116, 0x912027bda8444916, 0x912026a156444376, 0x9f6026a156444226, 0x809a85594c444226, 0x809f36a156444c86, 0x91214809a8559116, 0x244759a8559115, 0x91202791a8444946, 0x911a855943444386, 0x9f6026a156445086, 0x912026a156549116, 0x9ca026a1564444b6, 0x912026a184559116])
  | 5, 2 => (packedWords [0x809a85594c445086, 0x912026a156444f96, 0x9120f809a8559116, 0x912026a173559116, 0x912026a156444d16, 0x912026a15d559116, 0x91202559111d06c6, 0x912027bd564cd116, 0x9e2448099a559116, 0x912026a15e559116, 0x912026a156444da6, 0x809f36a156444146, 0x98e026a156444e96, 0x9120255911420be6, 0x912026a156444846, 0x912026a156444086, 0x24480911244645, 0x9f6446a156444966, 0x912026a1564440e6, 0x912026a156444c46, 0x912026a156444926, 0x9e244809a8559116, 0x91202721564449d6, 0x912026a1564446d6, 0x912026a1564dd116, 0x912026a156444c26, 0x9120262d56444746, 0x91213809a8559116, 0x912026a156444126, 0x982026a156444c36, 0x912026a156444066, 0x912026a156444556])
  | 5, 3 => (packedWords [0x91202559111d01b6, 0x912026d5a8559116, 0x911a85591130c966, 0x912026a156444d46, 0x912026a156444496, 0x912026a156444766, 0x912026a1564443e6, 0x91202791a8559116, 0x2448a9a8558fa5, 0x809a866956444226, 0x244891a8559115, 0x9f6026a156444746, 0x912026d9a8559116, 0x809a85594c444746, 0x91216809a8559116, 0x9122a809a8558c36, 0x809a866956445086, 0x912026a186558b26, 0x91202779a8559116, 0x912026a156445066, 0x912026a1434443e6, 0x912026a1564200f6, 0x912026a1564444b6, 0x912026a1563200f6, 0x91227809a8559116, 0x912026fda8559116, 0x9120279156444916, 0x912026a156511116, 0x912026a1564440f6, 0x96a026a156444916, 0x912026a16e559116, 0x912026a16f559116])
  | 5, 4 => (packedWords [0x912026a156444f26, 0x9f6027cda8559116, 0x9ca026a1564441b6, 0x809f36a156531116, 0x9d644809a8559116, 0x912026a156444f86, 0x9f6446a156444386, 0x244809a3559115, 0x8d22e809a8559116, 0x912026a156489116, 0x912026a18e559116, 0x244809a8444945, 0x2026a15647d115, 0x91229809a8559116, 0x912026a1564445c6, 0x912026a156444b46, 0x91202669564446c6, 0x912026a1562ec5e6, 0x912026a156444ba6, 0x809a866956444746, 0x911a85591130c386, 0x9be026a15650d116, 0x912026a156444a16, 0x91207809a8559116, 0x9ae026a1564449d6, 0x912026a156444606, 0x912026a156444646, 0x912026a1564446c6, 0x912026a167559116, 0x24480956444785, 0x912026a1564443c6, 0x91202775a8559116])
  | 5, 5 => (packedWords [0x912026a182559116, 0x91228809a8559116, 0x912026a156444316, 0x91234809a8559036, 0x912026a156444906, 0x809e46a1564441f6, 0x244809564446a5, 0x809c66a156444646, 0x91215809a8559116, 0x912026698b559116, 0xa0244809a8559116, 0x912026a17a559116, 0x91202729a8559116, 0x97e44809a8559116, 0x91202669564441b6, 0x912026a156445036, 0x912026a156444ec6, 0x912026a156444ed6, 0x809a8559113a4e26, 0x912026a156444636, 0x809f36a19a559116, 0x912026a19d559116, 0x9120255911244646, 0x24480991559115, 0x809a8559113c8d66, 0x912026a18b559116, 0x912026a1564450d6, 0x9123a809a8559116, 0x912026a1564441b6, 0x912026a156444306, 0x912026a163559116, 0x244809b4559115])
  | 5, 6 => (packedWords [0x202719a8559115, 0x912027bde4559116, 0x911bf6a156444646, 0x912026a1564e1116, 0x912026a1564a5116, 0x9120272da8559116, 0x9122d809a8559116, 0x912026a156444006, 0x9ba44809a8559116, 0x244809a8558c55, 0x912026a1564442c6, 0x912026a156444016, 0x912026a156444436, 0x912026a15653d116, 0x9123d809a8559116, 0x912026a156444756, 0x91202791a84f9116, 0x912026a156444026, 0x912026a156444be6, 0x9ae026a156444226, 0x912026a156529116, 0x911a862d564444b6, 0x2446fda8559115, 0x912027bda84cd116, 0x9ae026a156445086, 0x912026a1564445e6, 0x912026a156444446, 0x912026a156444346, 0x912026a156444886, 0x9123c809a8559116, 0x912027c9a8559116, 0x9122a6a156444fa6])
  | 5, 7 => (packedWords [0x912026a156481116, 0x9e2026a1564444b6, 0x9121f809a8559116, 0x912026a157559116, 0x912026a156444816, 0x912026a156444e76, 0x912026a156521116, 0x96244809a8559116, 0x912026a156444c16, 0x24b809a8559115, 0x911a85591112c436, 0x2026a156444d65, 0x912026a1564446b6, 0x912348a9a8559116, 0x912026a156444bb6, 0x912026a1564b5116, 0x912026a1564449d6, 0x912027b5a8559116, 0x9ea44809a8559116, 0x912026a156444356, 0x809e4779a8559116, 0x912026a1563a4886, 0x9ca026a156444c86, 0x912026a156444eb6, 0x912026a1564450f6, 0x912026a156444946, 0x912026a1112583e6, 0x2026a1564441f5, 0x912246a156444e96, 0x244809a82c8885, 0x91206809a8559116, 0x912027bd56444646])
  | 5, 8 => (packedWords [0x912026a1564e9116, 0x9120261973559116, 0x912027a5a8559116, 0x912026a156444b96, 0x912026b5a8559116, 0x911a862d564446c6, 0x91202559112ec916, 0x9ca026a156444146, 0x9ae026a156444746, 0x9e244809564cd116, 0x244809e1559115, 0x912026a111274146, 0x912027e5a8559116, 0x91231809a8559116, 0x912026a156444f46, 0x912026a156444ac6, 0x809a85591112c0f6, 0x912026a156444806, 0x876026a156444386, 0x912026a156444fb6, 0x911a8559111b0436, 0x91202721a8559116, 0x9121c809a8559116, 0x912026a156444296, 0x912026a1564d1116, 0x912026a156444046, 0x912026a1564441a6, 0x96a44809a8559116, 0x912026a156444fa6, 0x9ae027cda8559116, 0x244809a84f9115, 0x912026a156444a86])
  | 5, 9 => (packedWords [0x912026a156444226, 0x912026a156444f16, 0x91234809a8559116, 0x912026a156445086, 0x912026a1564450a6, 0x912026a1a1559116, 0x94e44809a8559116, 0x9e2026a1564441b6, 0x912026a156444c86, 0x912026a15650d116, 0x912026a156455116, 0x911a8559113e83e6, 0x91202731a8559116, 0x9123d6a18b559116, 0x9120e809a8559116, 0x202559111d01b5, 0x912026a156444e86, 0x912026a1563e8e96, 0x912346a1564443e6, 0x91234809a850d116, 0x912026a156444ca6, 0x98244809a8559116, 0x912026a156444146, 0x912026a16c559116, 0x912026a156444ff6, 0x9120255933444f26, 0x91234809a8558c56, 0x9f672809a8559116, 0x912026a15649d116, 0x911a85591112c226, 0x9ca026a156531116, 0x912026a19f559116])
  | 5, 10 => (packedWords [0x912026a156444336, 0x9123d6a156444436, 0x912026a156444276, 0x9e2447f1a8559116, 0x24487da8559115, 0x202779a8559115, 0x912026a111244646, 0x912027f1a8559116, 0x912026a156444c56, 0x912026a156459116, 0x912026a156444aa6, 0x912026a156445016, 0x912026a156444956, 0x9f644809a3559116, 0x911a86197d559116, 0x912026a156444e96, 0x912027bd56444bb6, 0x2026a1563200f5, 0x912026a15b559116, 0x912026a18d559116, 0x912026a156444b66, 0x9d244809a8559116, 0x24480996559115, 0x912026b1a8559116, 0x912026a18a559116, 0x912026a156444f66, 0x93244809a8559116, 0x912026a185559116, 0x912026a156444746, 0x912026a156444b16, 0x2446a1112583e5, 0x912026a156444996])
  | 5, 11 => (packedWords [0x91202559334446c6, 0x912026a170559116, 0x809a85591106c0f6, 0x275809a8559115, 0x912026a1564b9116, 0x912026a156444486, 0x9d6026a18b559116, 0x912026a15646d116, 0x912026a156444676, 0x912026a1564449e6, 0x91239809a8559116, 0x912026a1564442e6, 0x912026a1562c8886, 0x98e44809a8559116, 0x9f64480956444786, 0x809a85591f444c36, 0x9123b809a8559116, 0x912026dda8559116, 0x912027b1a8559116, 0x912026a1564443f6, 0x912026a156444836, 0x912026f5a8559116, 0x911e46a156444486, 0x2448c5a8559115, 0x91226809a8559116, 0x244809d3559115, 0x9ca026a19a559116, 0x9aa44809a8559116, 0x912027cda8559116, 0x9120262d564cd116, 0x912026a156444326, 0x9122a6a156444966])
  | 5, 12 => (packedWords [0x91202559334441b6, 0x912026a1564445d6, 0x2026a167559115, 0x9f644809a8559116, 0x912026a1112c8886, 0x912026a156531116, 0x912026a1564440b6, 0x91210809a8559116, 0x912026a156444f06, 0x9120e6a156444646, 0x9120278556445086, 0x809a8559112744b6, 0x912026a156444136, 0x911a862d56444fa6, 0x24480956444725, 0x912026a1a3559116, 0x9e244809e4559116, 0x912026a111244886, 0x912026a15a559116, 0x96e44809a8559116, 0x912026a156444c36, 0x912026a1564f9116, 0x912026a156444936, 0x912346a18b559116, 0x9121d809a8559116, 0x23a809a8559115, 0x912026a168559116, 0x244839a8559115, 0x91202559334445e6, 0x9f6446a1564444b6, 0x912026a14c444146, 0x912026a17c559116])
  | 5, 13 => (packedWords [0x911a8559113e8436, 0x9e2026a156444c86, 0x912026a156444786, 0x912026a1563a4c36, 0x912026a1564449a6, 0x94644809a8559116, 0x912346a156444436, 0x912026a1564446a6, 0x912026a156444e66, 0x912026a156444cc6, 0x912026a183559116, 0x912026a1563e8b26, 0x911a861956444416, 0x8f63a809a8559116, 0x912026a19a559116, 0x2447f1a8559115, 0x9e2026a156444146, 0x9122a6a156444386, 0x912026a156535116, 0x912026a156444ae6, 0x809a861983559116, 0x912026a156444966, 0x912026a191559116, 0x912026a17d559116, 0x809a85591112c226, 0x912026a156444b36, 0x912026a156444b26, 0x912026a156444df6, 0x2446a156444995, 0x912026a1564443d6, 0x9120279156444f26, 0x912026d1a8559116])
  | 5, 14 => (packedWords [0x9121f6a156444c86, 0x91234809a8444966, 0x809a8559114204b6, 0x2446a156444485, 0x911a8559112583e6, 0x91202739a8559116, 0x912027d5a8559116, 0x91241809a8559116, 0x9e24480956444646, 0x912026a162559116, 0x912026a1564444c6, 0x912026a156479116, 0x9123480996559116, 0x9122e809a8559116, 0x912026a156444916, 0x912026a1564445b6, 0x809a8559112741b6, 0x24480973559115, 0x809a8559113200f6, 0x912026a16a559116, 0x912026a156444686, 0x912026a156444e26, 0x912026a156444566, 0x24480956444da5, 0x912026a156444876, 0x91202735a8559116, 0x9be44809a8559116, 0x911f36a18b559116, 0x91202791564446c6, 0x912026a156444256, 0x912026a1563e8386, 0x912026a1564445f6])
  | 5, 15 => (packedWords [0x912026a15c559116, 0x809a8559110500f6, 0x912026a156444206, 0x91219809a8559116, 0x912026a156444196, 0x9ca6b809a8559116, 0x912026a156509116, 0x99e44809a8559116, 0x912026a156444426, 0x244809564dd115, 0x912026a156444fe6, 0x2026a111274145, 0x912026a1113a4b26, 0x9f678809a8559116, 0x809a861956444196, 0x2026a156444805, 0x911f36a156444436, 0x94e026a156444646, 0x9e2026a156531116, 0x809a862d56444806, 0x809a8559111d04b6, 0x912026a156444386, 0x912026a1564448c6, 0x9120264556444386, 0x912026a156495116, 0x912026a133444646, 0x912027918b559116, 0x2026a156444295, 0x911a8559113e8226, 0x912026a1564444d6, 0x91202791564441b6, 0x912026d156444386])
  | 5, 16 => (packedWords [0x25a809a8559115, 0x912026a1113a4916, 0x91202559113c8646, 0x9123480956444726, 0x911a855943444fa6, 0x911a8559110f8386, 0x9e2446a1564444f6, 0x912346a156444226, 0x2026a156444a85, 0x912026a156444896, 0x912026a1564ad116, 0x912026a15644d116, 0x912026a1564444f6, 0x809a8559110881b6, 0x9ca44809a84449d6, 0x253809a8559115, 0x912026a18c559116, 0x912346a15650d116, 0x912026a158559116, 0x9120274d56444e96, 0x809a8559114201b6, 0x809f36a1564444b6, 0x912026a1564440d6, 0x8f6026a156444296, 0x91202785a8559116, 0x9ae44809a8559086, 0x912026a156444596, 0x9ae44809a8558c86, 0x912026a15630cb26, 0x912026a19b559116, 0x912026a156444416, 0x91202559111b0646])
  | 5, 17 => (packedWords [0x912027bda8559116, 0x260809a8559115, 0x9e24480956444bb6, 0x91202791564445e6, 0x912026a1564450b6, 0x912027d9a8559116, 0x911a862d56444966, 0x9ae44809a8559116, 0x9f6026a1564440f6, 0x2446a17d559115, 0x91202715a8559116, 0x809a85594c4440f6, 0x9e2026a19a559116, 0x91202559374449d6, 0x1a85591112c225, 0x2026a156444275, 0x2446a156444df5, 0x91243809a8559116, 0x244809562ec5e5, 0x912026a156444826, 0x97644809a8559116, 0x92e026a156444386, 0x912026a1564440c6, 0x912026a156444096, 0x912026a156444c66, 0x912027d1a8559116, 0x912026a1564449f6, 0x911a855911258436, 0x9120262d56444646, 0x912026a1564440a6, 0x912026a156539116, 0x91202559111901b6])
  | 5, 18 => (packedWords [0x912026a133444886, 0x912026a1564449b6, 0x9ca44809a8559116, 0x912026a186444886, 0x912316a156531116, 0x809a8559111d01b6, 0x912026a1564443b6, 0x912026a156444b06, 0x91202791a8558f26, 0x263809a8559115, 0x912026a1564442d6, 0x912026a156499116, 0x809a8559113209d6, 0x912026a156444036, 0x912027b9a8559116, 0x91202559111b0436, 0x9123d809564446c6, 0x912026a15647d116, 0x912026a15630c386, 0x911f36a156444226, 0x2446a156444fe5, 0x9f6446a156444fa6, 0x91202559113c8bb6, 0x809a8669564440f6, 0x809a855911274146, 0x9f6448d1a8559116, 0x809f36a1564441b6, 0x91202559111905e6, 0x912026a196559116, 0x911a862d56444386, 0x911a8559113e8c36, 0x9120262d56444436])
  | 5, 19 => (packedWords [0x912026a1564445a6, 0x9123d8098b559116, 0x912026a156444f36, 0x912026a156444ef6, 0x912026a156444546, 0x912026a156444076, 0x24480956444be5, 0x912026a156444706, 0x912346a156444c36, 0x91202759a8559116, 0x912026a156551116, 0x2446a1564444f5, 0x91202619564446a6, 0x91202559112ec6c6, 0x912026a16d559116, 0x911a85591110c386, 0x244809ef4cd115, 0x91202559113a4da6, 0x21d809a8559115, 0x912026a17f559116, 0x912026a156444856, 0x912026a1564bd116, 0x93644809a8559116, 0x9120c809a8559116, 0x9120274da8559116, 0x912026a1564cd116, 0x911e4759a8559116, 0x91202719a8559116, 0x809a855943444a86, 0x912026a186559116, 0x809a855911320226, 0x2446a156444415])
  | 5, 20 => (packedWords [0x95244809a8559116, 0x912026a15648d116, 0x912027ada8559116, 0x809a855911420c86, 0x9fa44809a8559116, 0x9120262d56444bb6, 0x912026a1564450c6, 0x9e24480956444746, 0x2026a183559115, 0x91202559112ec1b6, 0x911a85594c444996, 0x912026a156519116, 0x912026a15651d116, 0x809a855911088146, 0x911a855911258226, 0x912026a156444726, 0x9120255933444916, 0x99e026a156444f26, 0x912026a156444366, 0x91208809a8559116, 0x9f244809a8559116, 0x809a855911420146, 0x912026a186558e96, 0x9e26b809a8559116, 0x912026a156515116, 0x9f6026a1564449d6, 0x809a85594c4449d6, 0x809a859d56444916, 0x9122a809a8558fa6, 0x911a855943444966, 0x91224809a8559116, 0x912026a156444056])
  | 5, 21 => (packedWords [0x9ca44809a8531116, 0x8d2026a156444276, 0x912026a1564448f6, 0x912026a156444ea6])
  | 6, 0 => (packedWords [0x9122a809a8559116, 0x9e244809a8559116, 0x912026a1564443e6, 0x91202791a8559116, 0x912026a1564444b6, 0x912026a1564440f6, 0x912026a156444f26, 0x912026a156444646, 0x912026a1564446c6, 0x912026a18b559116, 0x912026a1564441b6, 0x912026a156444436, 0x9123d809a8559116, 0x912026a1564445e6, 0x912026a156444886, 0x912026a156444bb6, 0x912026a1564449d6, 0x912026a156444fa6, 0x912026a156444226, 0x91234809a8559116, 0x912026a156445086, 0x912026a156444c86, 0x912026a15650d116, 0x912026a156444146, 0x912026a156444e96, 0x912026a156444746, 0x912027cda8559116, 0x9f644809a8559116, 0x912026a156531116, 0x912026a156444c36, 0x912026a19a559116, 0x912026a156444966])
  | 6, 1 => (packedWords [0x912026a156444b26, 0x912026a156444916, 0x912026a156444386, 0x912027bda8559116, 0x9ae44809a8559116, 0x9ca44809a8559116, 0x912026a1564cd116, 0x912026a186559116])
  | 7, 0 => 0x244809a8559115
  | _, _ => 0

private def wordBlocks : Nat → Nat
  | 0 => (packedWords [0x881000000aa, 0xff8000, 0x201044180000033, 0x3fe002, 0x808041984000000f, 0x28000000000c0000, 0x4040208824000028, 0xc000000000cfe00, 0x10040200000c, 0xc000000000033f80, 0x404060982000003, 0x222000000000c000, 0x1010082a8900002, 0xc0c00000001fc000, 0x8122000000, 0x7f000])
  | 1 => (packedWords [0x1028620800003300, 0x1fc000010, 0x205054180001111, 0x3f80000002, 0x8082451040000505, 0xfe0000000, 0xc11000000154, 0x88000003f8000000, 0x88, 0x280000000003ff80, 0x220000028, 0xa0000000007f3000, 0x10100822080000a, 0xaaa80000001ff000, 0x404020aa240002, 0x7fffe])
  | 2 => (packedWords [0x180c3b8f0000aaee, 0x80000001ffff8018, 0x6030ee340002abe, 0x7fffe006, 0x8080411040000c0c, 0xfe00c0000, 0x401000000330, 0xcc000003f80c0000, 0x8081415060000cc, 0xb3800000fe03ff80, 0x606070dc3c00033, 0xfcc000003f80ffe0, 0x18181c370e0000c, 0xaba800000fe03ff8, 0x606030ee340003, 0x3fffffe])
  | 3 => (packedWords [0x181c370e0000eecc, 0x800000ffffff8018, 0x6070fe3c0003bbb, 0x3fffffe006, 0x2040000000f00, 0xc000000fffc00000, 0x20209166100003c3, 0xf2000003fff30000, 0x18182c7b8d0000f2, 0xfc000000fffcc000, 0x6060b1ee300003c, 0xaf0000003fff3000, 0x18182c7b8c0000f, 0xebe800000ffffc00, 0x6060b1ee340003, 0x3fffffe])
  | 4 => (packedWords [0x8345d860000fcfc, 0x800000ffffff8008, 0x60f1fe3c0003fbf, 0x3fffffe006, 0x103866080000ff0, 0x1000000ffff00001, 0x6060f1dc380003fd, 0x50000003fffc0000, 0x18183c770c0000ff, 0xea800000ffff0000, 0x4040e1ba240003f, 0xfc0000003fffffe0, 0x18183c770c0000f, 0xff3000000ffffc00, 0x6060f1dc380003, 0x3fffffe])
  | 5 => (packedWords [0x183c7f8f0000ffee, 0xffffff8018, 0x60f1fe300003ffc, 0xa000003ffff00006, 0x8183c7f8d0000fff, 0xf000000ffffff801, 0x6060f1fe380003ff, 0xa000003fffffe00, 0x2002000001000a00, 0x300000300003f80, 0x9000000800300, 0xc0000fe0, 0x2026000000000f0, 0x88000030000000, 0x2192090222440088])
  | 6 => (packedWords [0xc040889000300030, 0x844, 0x30902004000cc000, 0x4000000000000219, 0x82c0411060044004, 0x40001fc000000000, 0x2120104410014001, 0x7f000000000, 0x64000000005500, 0x220001fc00000000, 0x2200, 0xa000080c0003fe0, 0x8448040889000a00, 0x2000000c00, 0x21920902004002a8, 0x80c000000])
  | 7 => (packedWords [0x8240889100aa00aa, 0x8002030000ff8864, 0x22912665c02a803b, 0xa00080c0003fe21b, 0xc8a44999500aa00f, 0xa8002030000ff886, 0xd24922aa6402aaaa, 0xc000080c07fffe21, 0x80804110400c000, 0x3fc0000c000, 0x9000000003300, 0xcc000ffc0000000, 0x82c04110600cc0, 0x3330003ff0000ff8, 0x20b05054180333, 0xffff80ffe])
  | 8 => (packedWords [0x8a44999500ea00ea, 0x8003ff0000ff886c, 0x2b912665c03b803b, 0xffc0003fe21b, 0x4c040801000f0000, 0xc0003fc000000084, 0x332112665003c003, 0xf0000ff000030021, 0x4cc864d99400f0f0, 0x3c8003fcfffcc008, 0x1b32912665403c80, 0xf0000ff00003002, 0x86cca44999400f30, 0x3c0003fc0000c00, 0x21b32912665003e8, 0xffc000300])
  | 9 => (packedWords [0xca44999500fa00fa, 0x3ff0000ff886c, 0x3b112665803f003f, 0xe000ffc0003fe213, 0xcee44999700fe00f, 0x3ff0000ff886, 0x939902004003fc00, 0xaa000ffc00000021, 0x64e640889100ff00, 0x330003ff0000ff88, 0x1b3b912445803fc0, 0xee000ffc0003fe2, 0x86cee44999700ff0, 0x3c0003ff0000ff8, 0x21b3b912665003fc, 0xffc000300])
  | 10 => (packedWords [0xee44999500ff00fa, 0x3ff0000ff886c, 0x3b912665803fc03f, 0xa000ffc0003fe21b, 0x4f648aa9900ffaaa, 0x3ff01ffff887, 0xd3d9e3986003fffc, 0x2000ffffffc0021, 0x3012082209020202, 0xc001fc0000000000, 0x240402088200c000, 0x7f0000000000, 0xa00200000003030, 0x1fc000000000, 0x2393990200400ffc, 0x7fffc000000])
  | 11 => (packedWords [0x2491042204040404, 0x2501, 0x4024410801400140, 0x960, 0x1248100200505000, 0x2000000000000258, 0x202020, 0x8000c000cfe00, 0x10100822080a000a, 0x3fc0000030000, 0x800800000028280, 0xa0a0ff00c0000000, 0x30120822090a0a0, 0xaaa83fc0300033f8, 0xc04820aa24282a, 0xff00c07fffe])
  | 12 => (packedWords [0x9248aa990aaa0aaa, 0x3fe030003ff8874, 0x3990200402bfc000, 0xffffc000000219, 0x1009104200c000c0, 0x20000000300250, 0x492040080303000, 0xc08000c00000094, 0x1249104220c0c0c, 0x8382000300033fa5, 0x444d26498ac30303, 0xf0c08000c000cfe9, 0x5113499262a0c0c0, 0x33302000300033fa, 0x9424b25454983033, 0x8000ff80ffe])
  | 13 => (packedWords [0x2c9515260ccc0ccc, 0x203ff0003ffa509, 0x4d26498a83830383, 0xe0ff00c000cfe944, 0x13699262b0e0e0e0, 0x3fc0300033fa53, 0x4020400803c0000, 0xff00000000096, 0x91109926280f000f, 0xc003fc0000030025, 0x64442e598a03c03f, 0xf040ff003fffc009, 0x5913499262a0f040, 0x3c003fc000003002, 0x9644d26498a03c14, 0xff000000c00])
  | 14 => (packedWords [0x129926290f0a0f0a, 0x3fc0300033fa5b1, 0x4d26498a03c303c0, 0xc0ff00c000c00964, 0x13499262a0f0c0f0, 0x383fc0300033fa59, 0xc4da6498ac3c383c, 0xff00c000cfe96, 0xa1268100200f0f00, 0x8283fc0300000025, 0x6c4da2488a43c3c2, 0xc0c0ff00c000cfe9, 0x5a1269104220f0f0, 0x38383fc0300033fa, 0x96c4da6498ac3c3c, 0xff00c000cfe])
  | 15 => (packedWords [0x369926280f0f0f00, 0x83fc0300030025b1, 0x4da6498a43c3c3c2, 0xc0ff00c000cfe96c, 0x13699262a0f0f0f0, 0x303fc0300033fa5b, 0xa4ba5454983c3f33, 0xf00ff00ff80ffe96, 0xa92ea559a40f0ff0, 0x3fc03fffcc025, 0x6859a0400803d7c0, 0xff7fc0000009, 0x5a1268100200fcf0, 0x3fc03ffff0000002, 0xb7776376fef03fc0, 0xffff0000f00])
  | 16 => (packedWords [0xe6c180300fff0000, 0x3ffff0000002de5, 0x9048901004040404, 0x1480, 0x2012240401100110, 0x528, 0x904080100444400, 0x200000000000014a, 0x4480408890202020, 0x800c000001fc0008, 0x404020882088008, 0xf0037f00007f0000, 0x10103866082200f, 0xdfc00ffff000, 0x2192090200408888, 0x37f000000000])
  | 17 => (packedWords [0x9248aa9922222222, 0x8dfc0001fc000874, 0x24922aa64888aaaa, 0xa37f00007fffe21d, 0x49248aa9922aa22a, 0xdfe0301fcff887, 0x93990200408bfc00, 0x2a37fffc00000021, 0x749248aa992a2a2a, 0xaa8ffc0301ff3f88, 0x1d24922aa64a8aaa, 0xaaa3ff00c07fffe2, 0x8749248aa992aaa2, 0xc000ffe0301ffff8, 0x480804890100c000, 0x30000007f001])
  | 18 => (packedWords [0xc142805030300000, 0xc00000000005a46, 0xb058b2340c0c0c0c, 0x30000007f001691, 0xec966d9d43030f0f, 0xc0c0000fffcc05a4, 0x3b259b6750c3c0c3, 0x32300ff007f30169, 0x76d36aead9323232, 0xdfc0001fc005a, 0xa0804080100cc000, 0x30037f0000000014, 0x292112a624833003, 0xdc00dfc0001fc005, 0x4a4844e99920cc01, 0x37f003fff001])
  | 19 => (packedWords [0x112a62483300f300, 0xdfc00fffc005292, 0x844e99920cc03fc0, 0x237f003fffc014a4, 0x6936aead93322332, 0xc0dfc0001fc005af, 0x5b45abab60ccc0cc, 0x3237f00007f0016b, 0xf6d36aead9333233, 0xdfc0001fc005a, 0xb9b0d0a0140cccc0, 0x22237f0000000016, 0xaf6d34aaad933332, 0xc0c0dfc0001fc005, 0x6b9b0d8b2340cccc, 0x37f00007f001])
  | 20 => (packedWords [0xd36aead933333232, 0xdfc0001fc005af6, 0xb4dab8960cccccc0, 0x237f00007f0016bd, 0x6d36aead93333332, 0x30dfc0001fc005af, 0xbb2d5a5558cccf33, 0xf037f003f80fff6b, 0xeecb66d9d43333f0, 0xdfc00fffcc05a, 0xb9b9d0a0140cddc0, 0x3cc37f7f00000016, 0x29a3d2e734e33cc3, 0xdffff01fcffd, 0x6b9b0d0a0140cfcc, 0x37fff0000001])
  | 21 => (packedWords [0xe742805033ff0000, 0xdffff0000005ae6, 0xf97cf33c8f0f0f0f, 0x38000c07fcfffd1, 0x311bb66683f003f0, 0xffc0001ff00779, 0x4c46ed99a0fc03fc, 0x3ff003fffc01de, 0xe7e7c380703f3f00, 0xffc030000007f, 0xf9f9f0e01c0fffc0, 0x403ffffc000001f, 0x80804110440404, 0xc3c3001fcfe00000, 0x20209166110103, 0xc007f3fff300])
  | 22 => (packedWords [0x91042044004400, 0x300000fe00002501, 0x4920400811110000, 0x4c007f0000000940, 0x92c9515264444444, 0x33001fcfe0000250, 0x24b2545499111333, 0xccc007f3f80ffe94, 0x92c95152644cc44, 0x333003fffe00ffa5, 0x424b254549913333, 0xc4cc00ffff80ffe9, 0x5092c9515264c4c4, 0x3333201fffe033fa, 0x9424b25454993331, 0xc80ffff80ffe])
  | 23 => (packedWords [0x268100204f4f0000, 0x33fdff00000025a1, 0x8048901014001400, 0xc00003f80001480, 0x2410200405050000, 0x43001fc000000520, 0x2924994511414141, 0x70c007f3f8000148, 0xa492659c4505070, 0x143001fcfffc0052, 0x829249945114143c, 0xf0c007f3fff0014, 0x20a492659c45050f, 0x43c3001fcfffcc05, 0x693b259b675143c1, 0xc00ff3f80301])
  | 24 => (packedWords [0xc966d9d450f0f0f0, 0x3003fcfffcc05a4e, 0xdb6dd55995151515, 0xc007f3f80001dc2, 0x3018300605500000, 0x300000000000778, 0xc06cd1181540154, 0xc00003f80001de, 0x9311bb66685500ff, 0x51300000ffff0077, 0xe2cb6dd559955115, 0x550c007f3f80001d, 0x78b49b7556455505, 0x5553001fcfe00007, 0xde2db6dd55995551, 0xc007f3f80001])
  | 25 => (packedWords [0x6583006055550000, 0x3001fc0000007783, 0xdb65c55995555111, 0xc007f3f80001de2, 0xb6da751645555505, 0x53001fcfe0000778, 0x2db6dd5599555551, 0xc007f3f80001de, 0x8365b34460555555, 0x513001fcfe000077, 0xe2db6dd559955555, 0xaaac007f3f80001d, 0x793758b2ae95555a, 0xfc03001fc01fffff, 0xde4dd6ed99a15557, 0xc007f3fffc01])
  | 26 => (packedWords [0x83f3ccf155aa55aa, 0x300203fe00ffffe7, 0xf9f0e01c157fc000, 0xc00ffc000001ff9, 0x3678300605757000, 0x6b1fdfc00000077a, 0xe96cb9cd35696969, 0xcff7fff80cff48, 0x9311bb66685f005f, 0x33fc00fe030077, 0xe0d960c01817d540, 0xcff7f0000001d, 0x7a3678300605f5f0, 0x33fdff0000007, 0xff9f9f0e01c17ffc, 0xcffffc000001])
  | 27 => (packedWords [0xbeddbfbf66666666, 0x3dfdfcfffc002d7d, 0x924994511c141c14, 0xf007f3fff001482, 0xec966d9d47070707, 0xc3c01fcfffc005a4, 0x3b259b6751c1c3c3, 0xf0f007f3fff30169, 0x4ec966d9d470f070, 0xc03c03fcfffcc05a, 0xa4844a98921cc01c, 0xf7f003fff0014, 0xae6c342805073730, 0xdc03dfdfc0000005, 0xde4c46ed99a1dc01, 0xf7f003fff001])
  | 28 => (packedWords [0x11bb66687700ff00, 0x3dfc00ffff007793, 0xd960c0181dd54000, 0xf7f7f0000001de0, 0x7e7c380707777000, 0x3dfdfc0000007fe, 0x9f9f0e01c1dffc00, 0xf7fffc000001ff, 0x9311bb66687f007f, 0x3ffc00ffff0077, 0xf9f9f0e01c1fdfc0, 0x80fff7fc000001f, 0x80808, 0x2000002000000c00, 0x22002, 0x80000000c00])
  | 29 => (packedWords [0x88880000, 0x202030000000000, 0x22222222, 0xa08080c000ffe000, 0x10082a898888aaa, 0x302020301ffff801, 0x202050541a222333, 0xaa08080ff80ffe00, 0x648240889188aa88, 0x330202030003ff88, 0x20b010441a23322, 0xa8a080ffc000ffe0, 0x30120822098a8a8, 0x32303fe030003ff8, 0x94049244108a3232, 0x8080c000ffe])
  | 30 => (packedWords [0xa000a000, 0xc000001fc000000, 0x2010200428280000, 0x300800000000211, 0x480408890a0a0a0a, 0xa8c020001fcc0084, 0x524122aa668282aa, 0xf030080007fffe21, 0x4c8864d994a0a0f0, 0x2a8c0200fffcc008, 0x1920902224682aa8, 0xf030080c07f3fe2, 0x84cc8449994a0f0a, 0x8a88c03fc01fcc00, 0x21d24922aa668a8a, 0x37f80007f300])
  | 31 => (packedWords [0x80408890a8a8a8a8, 0xe020301ffff8844, 0x2a800000, 0x3ff000000000000, 0x10082208aa00aa0, 0xa8ffc0001ff00001, 0x404020aa26a802aa, 0x3ff00007fffe00, 0x1010182608aa00ee, 0x800ffc00ffff0000, 0x4040a18822a803e, 0xf003ff003fffc000, 0x1010386608aa00f, 0xa828ffc00ffff000, 0xc048208826a82a, 0x3ff00c07fcfe])
  | 32 => (packedWords [0x12082a89aa0aaaaa, 0x8ffc0301ffff8030, 0x24922aa66a88aa88, 0x43ff00007fc0021d, 0x83c0c330eaa44aa4, 0x20ffdfc01ff00001, 0x4040208822aa22aa, 0xaa3ff80c07fffe00, 0x1010082a89aa88aa, 0xa28ffe0301ffff80, 0xc048208826aa2aa, 0xaa03ff80c07fffe0, 0x8549048aa98aaa0a, 0xaaa0ffe0001ffc00, 0x21524122aa62aaa2, 0x3ff80c07fffe])
  | 33 => (packedWords [0x82408010aaaa0000, 0x8ffe030000000864, 0x209022246aaa802a, 0xa3ff80c0003fe219, 0x49248a219aaaa0a0, 0x88ffe0300033f887, 0xd24922aa66aaa888, 0x883ff80c07f00021, 0x6482408010aaaa88, 0x280ffe030003ff88, 0x19209022242aaaa8, 0x8a83ff80c07f3002, 0x86482408890aaaaa, 0xa800ffe0301ffff8, 0x21d249228862aaaa, 0x3ff80c07fc00])
  | 34 => (packedWords [0x9248a218aaaaaa88, 0x8ffe0301ffff8874, 0x24922aa66aaaaaaa, 0xc3ff80c07fffe21d, 0xc8a549516aaaaccc, 0xb8ffe03fe03ff886, 0xf26972fe7eaaabbb, 0xf03ff80ffffffe21, 0x6c8a64d994aaaaf0, 0xbe8ffe03fffcc008, 0x1f269b3ee76aaabe, 0xfaa3ff80ffffffe2, 0x8749278ee99aaaaf, 0xaae8ffe03ffffff8, 0x21d34922aa66aaea, 0x3ff80c07fffe])
  | 35 => (packedWords [0xd248aa99aabbaaaa, 0xffe0301ffff8874, 0xf030cc3aab32ab3, 0x3ffffc07fffe006, 0x4a6408010aaee000, 0xb8fffff000000086, 0xf2f932ee7eabbaab, 0x3ffffc07fffe21, 0x64c2408010aafa00, 0xaa8fffff00000008, 0x1d34922aa66abeaa, 0xafa3ffffc07fffe2, 0x87cda4cbb9daafaa, 0xfffff01ffff8, 0x219399020042abfc, 0x3ffffc000000])
  | 36 => (packedWords [0xf648aa99aaffaaaa, 0xfffff01ffff8874, 0x6934632cab2b2b2b, 0xe38080c07fffeb51, 0x5b6d9aebbaeaeaea, 0xffe0301ffffad7, 0x44426498a2bc02bc, 0x3ff00007fc0096, 0x9110b96628af00ff, 0xea8ffc00ffff0025, 0x7d64b66bae6beaab, 0x3ff80c07fffeb, 0xde5a6c18030afaf0, 0xaaa8ffe030000002, 0xb7d6db26aae6bebe, 0x3ff80c07fffe])
  | 37 => (packedWords [0xe6c18030afff0000, 0xfffff0000002de5, 0xb058b2342c2c2c2c, 0xa30080007f301691, 0x6d36aead9bababab, 0xffe0301ffffda7, 0x4844a98922ec02ec, 0x3ff00007fc014a, 0x92113a6648bb00ff, 0xea8ffc00ffff0052, 0xbda4dabab66eeaae, 0x3ff80c07ffff6, 0xae6c3428050bbbb0, 0xaaa8ffe030000005, 0x6bdb4d2aab66eeee, 0x3ff80c07ffff])
  | 38 => (packedWords [0xe7428050bbff0000, 0xfffff0000005ae6, 0x30003000, 0xc00003f80000000, 0xc0c0000, 0x3003fc000000000, 0x2020104413030303, 0xccc00ff3f8030000, 0x808141506c0c0cc, 0x383003fcfe03ff80, 0x202010661303038, 0xc0c00ff3fff3000, 0x808245104c0c0f, 0xc3c3003fcfffcc00, 0x20209166130303, 0xc00ff3fff300])
  | 39 => (packedWords [0x2c041106c0ccc0cc, 0x3003fffe00ff8008, 0xb050541b0333333, 0xc00ffff80ffe002, 0xcc8449994c0f0c0f, 0xc3003fcfe00c0084, 0x332193665303c3c3, 0xc2c00ff3fff30021, 0x381a0c330dc2c2c2, 0x3131fffcfe00c000, 0x424b254549b13131, 0x8c8c00ff3f803009, 0x808041104c8c8c, 0x3333203fffe03ff8, 0x202050541b2323, 0xc80ffff80ffe])
  | 40 => (packedWords [0x2c041106c8ccc8cc, 0xb203fffe03ff8008, 0x6830cc372b2b2b2, 0xcffffff80ffe00e, 0x100810020cc00000, 0x320000000000250, 0x402441083300330, 0xccc80003f80c0094, 0x908951526cc00cc, 0xc0320000fe03ffa5, 0x44442e598a33003f, 0xc0cc80003fffc009, 0x50124910422cc0cc, 0x311320003fe033fa, 0x9424b254549b3113, 0xc807f3f80c00])
  | 41 => (packedWords [0x910420cc88cc88, 0xb20203fe03ffa501, 0x60b4632c732ab32a, 0xc8080ff80ffeb59, 0x908951524ccc0ccc, 0x23203fcfe03c0250, 0x2422545493332333, 0xc80ffff80ffe94, 0x124810020cccc00, 0x333203ff00000025, 0x424b214449b33300, 0xc0cc80ffc0003fe9, 0x50124910422cccc0, 0x1113203ff00033fa, 0x9424b254549b3331, 0xc80ffff80000])
  | 42 => (packedWords [0x24810020cccc8888, 0xb203ff0003ffa501, 0x4d224aaa73332aaa, 0xc80ffc07fffe944, 0x92c851124ccccc0c, 0x23203fffe00c0250, 0x24b2144493333323, 0xc80ffff80ffe94, 0x124910420cccccc, 0x223203fffe030025, 0x4049244108333333, 0xcccc80ffff80ffe9, 0x5092c951526ccccc, 0xbbbb203fffe03ffa, 0x9464f274febf3333, 0xc80ffffffffe])
  | 43 => (packedWords [0x2cb55da6ccccfcfc, 0x3203ffffffffa509, 0x4d2e598a33333fc0, 0xcc80ffffffc00944, 0x93cbd772eccccffc, 0xbb203ffffffffa51, 0xb6bb5676df33bb33, 0xfcc80ffff80ffeb5, 0x4decd59db6ccfccc, 0x3203fffe03ffad, 0x5979b0600c333fc0, 0xcccc80ffc000000b, 0xd6deed59536ccffc, 0x3733203fffe03ffa, 0x9624b254549b3733, 0xc80ffff80ffe])
  | 44 => (packedWords [0x2c951526cdcdcccc, 0x3203fffe03ffa589, 0x49a0400833b38000, 0xecffffc000000948, 0x93e9d372fcececec, 0x33fffffe03ffa53, 0x44426498a33c033c, 0xcff003f80c0096, 0x8124810020cfcc00, 0x3333ffff00000025, 0x624b254549b3f333, 0xfcccffffff80ffe9, 0x5993c9d372ecfccc, 0x33fffffe03ffa, 0x96849a0400833f3c, 0xcffffc000000])
  | 45 => (packedWords [0x2e951526cfcfcccc, 0x33fffffe03ffa5a9, 0x79b0600c33ffc000, 0xcffffc000000b79, 0xa49265144d0d0d0d, 0xc3003fcfe00c0520, 0x29249967134343c3, 0xdcc00ff3fff30148, 0xb6db75566dcdcdc, 0x403203fffe03fff7, 0xe0c06cd118374037, 0xdccc80003f80c01d, 0x78b2db75566ddccd, 0x3203fffe03fff, 0xde0d960c01837774, 0xc80ffc000001])
  | 46 => (packedWords [0x6d971566ddddcccc, 0x3203fffe03fff78b, 0xd9e0c01837f7c000, 0xcffffc000001de8, 0x808041104e0c0e0c, 0x83c03fcfffcc0000, 0x3221126653838383, 0xf0f00ff3fff30021, 0x4c8864d994e0e0f0, 0x3c3c03fcfffcc008, 0x1332112665383c38, 0xa00f00ff3fff3002, 0x1010082208ea00e, 0xaaabffc00ffff000, 0x21d24922aa67aaab, 0xfff80ffffffe])
  | 47 => (packedWords [0x82408010eaea0000, 0xbfffff0000000864, 0x24922aa67abaaaaa, 0xafffffc07fffe21d, 0xc9a4cbb9deaeaeae, 0x33fffffffffff887, 0x24b254549bb333b3, 0xecf80ffffffffe94, 0x4dacd59db6ececec, 0x803e03ffffffffad, 0x444426498a3b803b, 0xf00fff003fffc009, 0x51110b96628ee00f, 0xbaabffc00ffff002, 0xb5d64b66bae7baab, 0xfff80ffffffe])
  | 48 => (packedWords [0x24810020eecc0000, 0x3fffff0000002501, 0x4b254549bbb33333, 0xcfffffff80ffe942, 0x93c9d372eeecceec, 0x3fffffffffffa51, 0x969b0600c3bbb800, 0xaafffffc000000b5, 0x75b6c9aab9eeeeaa, 0x333fffff01ffffad, 0x5b6bb5654dbbbbb3, 0xeeefffffff80ffeb, 0xd7dbeddbfbfeeeee, 0x3fffffffffffa, 0xb5979b0600c3bbfc, 0xfffffc000000])
  | 49 => (packedWords [0x10992628ef00ef00, 0x3ffc00ffff002591, 0x69b0600c3bfbc000, 0xfffffc000000b79, 0x201020040f000000, 0x3c0000000000520, 0x804890103c003c0, 0xf0f00003fff00148, 0xa092659c4f000f0, 0xc03c0000fffcc052, 0x84844e99923c003f, 0x30f00003fffc014, 0xa46c162c8d0f030f, 0xc103c0000fffc005, 0x482824994513c103, 0xf007f3fff001])
  | 50 => (packedWords [0x41224040f050f000, 0x3c01fcfffc005202, 0x924994513c143c14, 0xf007f3fff001482, 0xa492659c4f050f0f, 0xc3c01fcfffcc0520, 0x3b259b6753c1c3c1, 0xa0f007f3fff00169, 0x468162c8d0f0a0f0, 0x3c0200fffcc05a, 0x80804890103c303c, 0xc0f00ff3fff0014, 0x20a09265144f0c0f, 0xc3c3c03fcfffcc05, 0x482824996713c303, 0xf00ff3fff301])
  | 51 => (packedWords [0x49265144f0d0f0d0, 0x3c03fcfffcc0520a, 0xa259b6753c383c38, 0xf00ff3fff301693, 0x6c1428050f0f0000, 0xc3c03fc0000005a4, 0x3b251a6753c3c003, 0x30f00ff000030169, 0x46c162c8d0f0f030, 0x143c03fc01fc005a, 0x93b259b4553c3c14, 0x70f00ff3f800016, 0xa4ec966d9d4f0f07, 0x8283c03fcfffc005, 0x691b050a2343c3c2, 0xf00ff007f301])
  | 52 => (packedWords [0xd14aaad9f0f0aaaa, 0x3c03fc01ffffda56, 0xb251a4553c3c3030, 0xf00ff3f80301693, 0xec94699d4f0f0e0e, 0x3c03fcfffcc05a4, 0x1b058b0143c3c3c0, 0x30f00ff3fff00169, 0x46c162c8d0f0f0f0, 0x143c03fcfffc005a, 0x93b259b4553c3c3c, 0xa0f00ff3fff0016, 0xa46c162c8d0f0f0f, 0xc303c03fcfffcc05, 0x693b259b4553c3c3, 0xf00ff3fff301])
  | 53 => (packedWords [0xc966d9d4f0f0f0f0, 0xbc03fcfffcc05a4e, 0xb259b6757c3c3c3e, 0xcf00ff3fff3ff693, 0xec966d9d6f0f0f0f, 0xe3c03fcfffcffda4, 0x3b259b6753c3c3e3, 0xfaf00ff3ffffff69, 0x5ed96efbddf0f0fa, 0x3f3c03fcffffffda, 0x93b25db775bc3c3f, 0xf00f00ff3ffffff6, 0xa56d17ae658f0f0f, 0xffc3c03fcffff005, 0x697b65fbff73c3c3, 0xf00ff3ffff01])
  | 54 => (packedWords [0xcb66d9d5f0f2f0f2, 0x3c03fcfffcc05a6e, 0xb2d9b6753c3cfc3c, 0x8f00ff3fff30169b, 0xec966d9d4f0f8f0f, 0xc3c03fffffcffda4, 0xbb2d9b6753c3ebc3, 0xfaf00ffffff30169, 0x6ecb66d9d5f0faf0, 0x3f3c03fffffcffda, 0x93bb59b675bc3f3c, 0xf00ffffff3ff6, 0xa66e7428050f0ff0, 0xc3c3c03ff0000005, 0x69bbbd9b6753c3ff, 0xf00ffffff301])
  | 55 => (packedWords [0xc966d9d4f1f0f1f0, 0x3c03fcfffcc05ace, 0xb259b6753c7c7c3c, 0xf00ff3fff3016b3, 0x2112a6248f200f20, 0x3dfc00fffc00521, 0x9b0d0a0143cbc800, 0xf0f7fff000000169, 0x6ecb66d9d4f2f2f0, 0xbcbdfffcfffcc05a, 0x9fb6dbbef77cbcbc, 0xf7fff3fff3016, 0x28201224040f300f, 0xcc03dfc00fffc005, 0x4a4844a98923cc03, 0xf7f003fff001])
  | 56 => (packedWords [0x113a6648f300ff00, 0x3dfc00ffff005292, 0x904890103cd47c00, 0xf7f7f3fff0014a0, 0x201224040f3c0f00, 0x3dfffcfffc00528, 0x1b050a0143cfc000, 0xf0f7fff00000016b, 0xcec966d9d4f3f0f0, 0xfc3dfffcfffcc05a, 0xb7b65bbef73cfc3c, 0xf7fff3fff3016, 0xae6c3428050f3f30, 0xc003dfffc0000005, 0x6b9b0d8b0143cfcf, 0xf7fff3fff001])
  | 57 => (packedWords [0xcb66d9d4f3f3f0f0, 0x3dfffcfffcc05aee, 0xb9d0a0143cffc000, 0x4f7fffc0000016b9, 0xfedf7ddf6f4f4f4f, 0x3c03fcfffcc07f4, 0xc06cd1183d403d4, 0xf0f00003fff001de, 0xcfc9f7ddf4f5f0f5, 0x3c03fcfffcc07f, 0xf1f970e01c3d7d40, 0xf0f00ff0000001f, 0xfcfede7d9f4f5f5f, 0xdc03c03fcfffcc07, 0xde4c46ed99a3dc03, 0xf7f003fff001])
  | 58 => (packedWords [0xe7c38070f7f70000, 0x3dfffc0000007fe7, 0xb259b6753e3c3e3c, 0xf80ff3ffff01693, 0xec966d9d4f8f8f0f, 0xe3e03fffffcc05a4, 0x3b259b6753e3e3e3, 0xfaf80fffffffff69, 0x6ecb66d9d5f8faf8, 0x3e03ffffffffda, 0x80804890103e803c, 0xa00fff003fff0014, 0x212112a6248fa00f, 0xfc03ffc00ffff005, 0x484844e99923e803, 0xfff003fffc01])
  | 59 => (packedWords [0x41224040fa50f000, 0xbffdfcfffc005202, 0xa4dabab67eaabeaa, 0xfff80fffffff69d, 0x201224040fac8f00, 0x3ffffffffc00520, 0x1b050a0143ebc000, 0xf0fffff000000169, 0x4ec966d9d4faf0f0, 0xbc3ffffcfffcc05a, 0x97b65bbef73ebc3e, 0xfffff3ffff016, 0xa66c3428050fafa0, 0xaaabfffff0000005, 0x69db4d2aab67ebea, 0xfffffc07ffff])
  | 60 => (packedWords [0xc362c050fafaf000, 0x3ffffffffc005a66, 0xb2d9b6753ebebc3c, 0xafffffffff30169b, 0xecb66d9d5fafaf0f, 0xe3ffffffffcffda6, 0xbb2d9b6753ebebe3, 0xfaffffffffffff69, 0x7edb6efbddfafafa, 0x3fffffffffffda, 0x99b9d0a0143ebfc0, 0xb00fffffc0000016, 0x292112a6248fb00f, 0x3ffc00ffff005, 0x6b9b0d0a0143efec, 0xfffffc000001])
  | 61 => (packedWords [0xcb66d9d4fbfbf0f0, 0x3ffffffffcc05aee, 0xc06cd1183f003f00, 0xcf80003fffc01dc0, 0xb2db75566fcccfcc, 0xc3e03fffffffff70, 0x3f27df77d3f3c3f3, 0xf80ff3ffff01fd, 0x47e5c38070fcfc00, 0x333e03ff0000007f, 0xd3fb75e55dbf3f33, 0xf0f80ffff80ffff, 0xf4fede7d9f4fcfcf, 0xf3f3e03fffffcc07, 0xfd3fb7df77dbf3f3, 0xf80fffffffff])
  | 62 => (packedWords [0x11bb6668fe00fe00, 0x3ffc00ffff007713, 0xf9f0e01c3fbf8000, 0xefffffc000001fd9, 0xffffffffffefefef, 0x3fffffffffffff7, 0xc060c0183fc0000, 0xfff000000001de, 0x93119b2668ff000f, 0xc03ffc0000030077, 0xe4c46ad89a3fc00c, 0x500fff00007f001d, 0x78301b34460ff005, 0xdc03ffc00fe00007, 0xde4c46ed99a3fc01, 0xfff003fff001])
  | 63 => (packedWords [0x118b2268ff00aa00, 0x3ffc0001ff007793, 0xc064c1183fc03300, 0xcfff003f80c01de0, 0xb09971566ff00ccc, 0x3ffc00fe03fff78, 0x4c466c99a3fc03b8, 0xfff003fffc01de, 0x8301a34060ff00f0, 0x3c3ffc00fffc0077, 0xe2c269d6793fc03c, 0x300fff003fff301d, 0x79311ab6268ff00f, 0xd403ffc00fffc007, 0xde0c06cd1183fc03, 0xfff003fff001])
  | 64 => (packedWords [0x11ab6268ff00fa00, 0x3ffc00ffff007793, 0xc06cd1183fc03f00, 0xfff003fffc01de0, 0x311bb6668ff00ff0, 0x2bffc00ffff00779, 0x4c46ed99a7fc03fc, 0xcfff003fffcffde, 0x9311bb666aff00ff, 0xe23ffc00ffff3ff7, 0xe4c46ed99a3fc03f, 0xfaafff003ffffffd, 0x79311bb6ee9ff00f, 0xff33ffc00fffffff, 0xde6c66fdddbbfc03, 0xfff003ffffff])
  | 65 => (packedWords [0x19bf7fecff00fff0, 0x3ffc00ffffc0779b, 0xcd6ed99abfc13fc1, 0xfff003fffc01de4, 0x335bb6668ff05ff0, 0x23ffc00ffff00779, 0x4c46ed99a3fc23fc, 0xafff00ffffcffde, 0xb313bb6669ff0aff, 0xc03ffc03ffff3ff7, 0xe4cd6ed99a3fc33f, 0xf0cfff00ffffc01d, 0x79335bb666aff0cf, 0x3ffc03ffff3ff, 0xde8c9e0c0183fc3c, 0xfff00c000001])
  | 66 => (packedWords [0x37bb6668ff0fff00, 0x3ffc03ffff0077b3, 0xd46ed99a3fc43fc4, 0xfff003fffc01de4, 0x351bb6668ff11ff0, 0x8bffc00ffff00779, 0xde4fefbbe7fc8bfc, 0x30fff003fffc01ff, 0xd7d1fbeef8ff30ff, 0x3ffc00ffff007f, 0xf9f0f0e01c3fccc0, 0xf00fff000000001f, 0xff7d3fbe678ff33f, 0x3ffc00ffff007, 0xde0c960c0183fd10, 0xfff7f0000001])
  | 67 => (packedWords [0x35bb6668ff44ff00, 0x3ffdfcffff007793, 0xcf6fdddbbfd13fd1, 0xfff7f3fffc01de6, 0x341830060ff50000, 0x3ffdfc000000778, 0x4d46ed99a3fd43fc, 0x50fff7f3fffc01de, 0x9b59bf776cff50ff, 0x3ffdfcffff0077, 0xe0d960c0183fd540, 0xfff7f0000001d, 0x78365a34060ff55f, 0xfc03ffdfcfffc007, 0xde4dd6ed99a3fd57, 0xfff7f3fffc01])
  | 68 => (packedWords [0x67830060ff5f0000, 0x3ffdff00000077a3, 0xf9f0e01c3fddc000, 0xfff7f0000001ff9, 0x311bb6668ff80ff8, 0x3ffe00ffffc0779, 0x4c46ed99a3fe23fc, 0x88fff80ffffc01de, 0x9311bb6668ff88ff, 0xe33ffe03fffffff7, 0xe4cd6ed99abfe33f, 0xfa0fff80fffffffd, 0xfd791fbeef8ffa0f, 0x3ffe00ffffc07, 0xff9e0f0e01c3fea8, 0xfff80c000001])
  | 69 => (packedWords [0x93cbaaf9ffaaaaaa, 0x3ffe0301fffffff7, 0xe4fef99e3feabfc0, 0xafff80ffffc01ffd, 0x793fbeef9ffaaffa, 0x3ffe03fffffffff, 0xc060c0183ff0000, 0xfffff0000001de, 0x9311bb6668ffc0ff, 0xf03ffffcffff0077, 0xe6c66fdddb3ff03f, 0xfffff3ffff01d, 0x78325830060ffcc0, 0x3333fffff0000007, 0xde2cb65c559bff33, 0xfffffff80fff])
  | 70 => (packedWords [0x25a34060ffccf000, 0x3ffffffffc007783, 0xcd6ed99a3ff33fc0, 0xcfffffffffc01de4, 0x335bb666affccff0, 0x23fffffffff3ff79, 0x4cd6ed99a3ff33fe, 0xccffffffffffffde, 0x9b3dbf776effccff, 0x3ffffffffffff7, 0xe8c9e0c0183ff3c0, 0xfffffc000001d, 0x78365830060ffdd0, 0xfc03fffff0000007, 0xde4dd6ed99a3ff77, 0xfffffffffc01])
  | 71 => (packedWords [0xa7c38070ffee0000, 0xbfffff0000007fe7, 0xeffffffffffbbffb, 0xfffffffffffffff, 0x7c1c38070fff0000, 0xc3ffffc0000007fc, 0x3f279f67d3ffc3c3, 0xfffff3fff301ff, 0xd7d1fbe678fff0ff, 0xfc3ffffcffff007f, 0xf7f67fffff3ffc3f, 0xfffff3ffff01f, 0xfe7c3c38070fff30, 0x3ffffc0000007, 0xff1f970e01c3ffd4, 0xfffff0000001])
  | 72 => (packedWords [0xc3c38070fffa0000, 0xbfffff0000007fe7, 0xf6ffffff7ffebffe, 0xfffffffffffffff, 0x7e5c38070fffc000, 0xf3fffff0000007fc, 0x7ff7fffffbfff3ff, 0xffffffffffffff, 0xe7e7c38070ffff00, 0x2bfffff0000007f, 0xf9f9f0e01c7fffc0, 0xcfffffc0000fff, 0xfe7e7c38072ffff0, 0x8bfffff00003ff, 0xff9f9f0e23c7fffc, 0xfffffc000001])
  | 73 => (packedWords [0xe7c388f0ffff0030, 0x3fffff0000007fe7, 0xf9f0e01c3fffc022, 0xfffffc0003ffff9, 0x7e7c388f0ffff00a, 0xabfffff0000c07fe, 0x9f9f0e23c7fffc02, 0xccfffffc0003ffff, 0xefefc79176ffff00, 0x3c3fffff0000ffff, 0xfbfbf1e67d3fffc0, 0x404fffffc000301f, 0xfe7e7d38472ffff0, 0x1403fffff0000007, 0xff9f9f4e11c3fffc, 0xfffffc000001])
  | 74 => (packedWords [0xe7c38070ffff0808, 0xbfffff00033fffe7, 0xfdf2e89e7fffc282, 0xfffffc000cffffd, 0x7e7d38470ffff0c0, 0x33fffff0003007fe, 0x9f9f4e11cbfffc30, 0xfffffc000cffff, 0xf7f7dba678ffff0f, 0x43fffff0003007f, 0xf9f9f8f01c3fffc4, 0x100fffffc000001f, 0xfe7e7e3c070ffff1, 0x8083fffff0000007, 0xff9f9f0e23c3fffc, 0xfffffc07f001])
  | 75 => (packedWords [0xf7cbaaf9ffff2222, 0x3fffff01fc007ff7, 0xf9f8f01c3fffcc00, 0xfffffc07f001ff9, 0x7e7e3c8f0ffff303, 0x3fffff01fc007fe, 0xdfdfaf89e3fffccc, 0xfffffc07f001ff, 0xe7e7d38470ffff44, 0x113ffffffe00007f, 0xfbfbf5e55dbfffd1, 0xfffffff80001f, 0xfe7e7e3c070ffff5, 0x4143ffffffe00007, 0xffbfbf9f45d3fffd, 0xfffffff80001])
  | 76 => (packedWords [0xe7f3c470ffff5500, 0x3ffffffe00007fe7, 0xf9f0e01c3fffe020, 0xfffffc000301ff9, 0x7e7c38070ffff880, 0x23fffff0003007fe, 0x9f9f0e01c3fffe22, 0xaafffffc000fffff, 0xe7e7c388f1ffff88, 0x233fffff0003ffff, 0xf9f9f4e11cbfffe3, 0xfffffc000ffff, 0xfe7e7c38070ffffa, 0x8283fffff01fc007, 0xff9f9f0e23c3fffe, 0xfffffc07f301])
  | 77 => (packedWords [0xe7c388f1ffffa0aa, 0x3fffff01fcffffe7, 0xf9f0e23c3fffea2a, 0xfffffc07ffffff9, 0x7f7cba278ffffaa0, 0xabfffff01ff007ff, 0xdfdf2eabe7fffeaa, 0xb0fffffc07ffffff, 0xe7e7e3c8f0ffffb0, 0x3fffff01fcc07f, 0xf9f9f0e01c3ffff0, 0xc0fffffff80001f, 0xfefefc79174ffffc, 0x3003ffffffe00c07, 0xff9f9f4e11c3ffff, 0xfffffff80c01])
  | 78 => (packedWords [0xe7d38472ffffcc0c, 0x3ffffffe033fffe7, 0xf9f4e11c3ffff322, 0xcfffffff80fffff9, 0xfefd79576ffffccc, 0x3ffffffe03ffffe, 0x9f9fcf11c3ffff74, 0xeefffffff80c01ff, 0xffffdfbfffffffee, 0x3fffffffffffff, 0xf9f9f8f01c3ffffc, 0x30fffffffff001f, 0xfe7e7e3c8f0fffff, 0xc283ffffffffc007, 0xff9f9f8f23c3ffff, 0xfffffffff301])
  | 79 => (packedWords [0xefe7d9f4fffff0f0, 0x3ffffffffcc07fef, 0xf9fcf11c3ffffd40, 0xafffffffff001ff9, 0xfffeffbfdfffffaf, 0x3ffffffffffffff, 0x9f9fcf11c3fffff0, 0xfcfffffffffc01ff, 0xefeff7ddf6fffffc, 0xc03fffffffffffff, 0xfdfdfef99e3fffff, 0xfaafffffffffc01f, 0xff7f7fbeef9fffff, 0xff33ffffffffffff, 0xffffffffddfbffff, 0xffffffffffff])
  | 80 => (packedWords [0xfffffffcfffffff0, 0x3fffffffffc07fff])
  | _ => 0

private def wordAt (i : Nat) : Sig := twice (fld (wordBlocks (i / 8)) 126 (i % 8))

private def unpack : Nat → Nat → List Sig
  | 0, _ => []
  | n + 1, ws => wordAt (fld ws 10 0) :: unpack n (ws >>> 10)

private def states (s i : Nat) : List Sig :=
  let word := fld (packedBlocks s (i / 32)) (stateWidth s) (i % 32)
  unpack (word &&& 15) (word >>> 4)


private def index (s : Nat) (ws : List Sig) : Nat :=
  bsr (fun i => fld (hashBlocks s (i / 64)) 32 (i % 64)) (stateHash ws)
    16 0 (proofCount s)

private def found (s : Nat) (ws : List Sig) : Bool :=
  decide (index s ws < proofCount s) && ws.isPerm (states s (index s ws))

private theorem found_ok {s : Nat} {ws : List Sig} (h : found s ws = true) :
    index s ws < proofCount s ∧ ws.toFinset = (states s (index s ws)).toFinset := by
  rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at h
  obtain ⟨lt, perm⟩ := h
  refine ⟨lt, ?_⟩
  ext w
  simp only [List.mem_toFinset]
  exact perm.mem_iff

private def checkChild (s : Nat) (ws : List Sig) (a b : Sig)
    (d : Nat) (ka kb : Bool) : Bool :=
  let out := bin d a b
  if a ≠ b ∧ out ∉ ws ∧ out ≠ zero ∧ out ≠ one then
    let zs := childTwo ws a b d ka kb
    if zs.length ≤ s then !clear zs || found (s - 1) zs else true
  else true

private def flags : List Bool := [false, true]

private def ops : List Nat := [0, 1, 2, 3]

private def checkedState (s i : Nat) : Bool :=
  let ws := states s i
  decide (ws.Nodup ∧ goalFive ∉ ws) &&
    ws.all (fun a => ws.all (fun b => ops.all (fun d =>
      flags.all (fun ka => flags.all (fun kb => checkChild s ws a b d ka kb)))))

private def span (f : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => f i && span f n (i + 1)

private theorem span_ok {f n o} (h : span f n o = true) :
    ∀ i, o ≤ i → i < o + n → f i = true := by
  induction n generalizing o with
  | zero => omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)

private theorem span_join {f a o b} (ha : span f a o = true) (hb : span f b (o + a) = true) :
    span f (a + b) o = true := by
  induction a generalizing o with
  | zero => simpa using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add, span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb)⟩

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span2_0 : span (checkedState 2) 4 0 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span2 : span (checkedState 2) 4 0 = true :=
  span2_0

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span3_0 : span (checkedState 3) 41 0 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span3 : span (checkedState 3) 41 0 = true :=
  span3_0

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span4_0 : span (checkedState 4) 48 0 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span4_48 : span (checkedState 4) 48 48 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span4_96 : span (checkedState 4) 48 96 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span4_144 : span (checkedState 4) 48 144 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span4_192 : span (checkedState 4) 48 192 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span4_240 : span (checkedState 4) 48 240 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span4_288 : span (checkedState 4) 48 288 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span4_336 : span (checkedState 4) 48 336 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span4_384 : span (checkedState 4) 48 384 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span4_432 : span (checkedState 4) 48 432 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span4_480 : span (checkedState 4) 48 480 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span4_528 : span (checkedState 4) 48 528 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span4_576 : span (checkedState 4) 48 576 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span4_624 : span (checkedState 4) 41 624 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span4 : span (checkedState 4) 665 0 = true :=
  (span_join (span_join (span_join span4_0 (span_join span4_48 span4_96)) (span_join (span_join span4_144 span4_192) (span_join span4_240 span4_288))) (span_join (span_join span4_336 (span_join span4_384 span4_432)) (span_join (span_join span4_480 span4_528) (span_join span4_576 span4_624))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span5_0 : span (checkedState 5) 48 0 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span5_48 : span (checkedState 5) 48 48 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span5_96 : span (checkedState 5) 48 96 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span5_144 : span (checkedState 5) 48 144 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span5_192 : span (checkedState 5) 48 192 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span5_240 : span (checkedState 5) 48 240 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span5_288 : span (checkedState 5) 48 288 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span5_336 : span (checkedState 5) 48 336 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span5_384 : span (checkedState 5) 48 384 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span5_432 : span (checkedState 5) 48 432 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span5_480 : span (checkedState 5) 48 480 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span5_528 : span (checkedState 5) 48 528 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span5_576 : span (checkedState 5) 48 576 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span5_624 : span (checkedState 5) 48 624 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span5_672 : span (checkedState 5) 4 672 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span5 : span (checkedState 5) 676 0 = true :=
  (span_join (span_join (span_join span5_0 (span_join span5_48 span5_96)) (span_join (span_join span5_144 span5_192) (span_join span5_240 span5_288))) (span_join (span_join (span_join span5_336 span5_384) (span_join span5_432 span5_480)) (span_join (span_join span5_528 span5_576) (span_join span5_624 span5_672))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span6_0 : span (checkedState 6) 40 0 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span6 : span (checkedState 6) 40 0 = true :=
  span6_0

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span7_0 : span (checkedState 7) 1 0 = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem span7 : span (checkedState 7) 1 0 = true :=
  span7_0

private theorem checked (s : Nat) (hs : s ≤ 7) :
    ∀ i < proofCount s, checkedState s i = true := by
  intro i hi
  interval_cases s
  · simp [proofCount] at hi
  · simp [proofCount] at hi
  · exact span_ok span2 i (Nat.zero_le i) (by simpa [proofCount] using hi)
  · exact span_ok span3 i (Nat.zero_le i) (by simpa [proofCount] using hi)
  · exact span_ok span4 i (Nat.zero_le i) (by simpa [proofCount] using hi)
  · exact span_ok span5 i (Nat.zero_le i) (by simpa [proofCount] using hi)
  · exact span_ok span6 i (Nat.zero_le i) (by simpa [proofCount] using hi)
  · exact span_ok span7 i (Nat.zero_le i) (by simpa [proofCount] using hi)

private theorem nodesImpossible (s : Nat) (hs : s ≤ 7) (i : Nat)
    (hi : i < proofCount s) : Impossible true goalFive s (states s i).toFinset := by
  induction s using Nat.strong_induction_on generalizing i with
  | ind s ih =>
    have ok := checked s hs i hi
    rw [checkedState, Bool.and_eq_true, decide_eq_true_eq] at ok
    apply enum_step ok.1.1 ok.1.2
    intro a ha b hb d hd ka kb diff fresh properOut short
    have dSmall := (allowed_four hd)
    have dIn : d ∈ ops := by
      rcases dSmall with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
    have kaIn : ka ∈ flags := by cases ka <;> decide
    have kbIn : kb ∈ flags := by cases kb <;> decide
    have foundChild := List.all_eq_true.mp
      (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp
        (List.all_eq_true.mp ok.2 a ha) b hb) d dIn) ka kaIn) kb kbIn
    have split : clear (childTwo (states s i) a b d ka kb) = false ∨
        found (s - 1) (childTwo (states s i) a b d ka kb) = true := by
      simpa [checkChild, diff, fresh, properOut.1, properOut.2, short, Bool.or_eq_true] using foundChild
    rcases split with noCover | link
    · intro k hk run
      rw [clear_required run] at noCover
      exact Bool.noConfusion noCover
    · obtain ⟨lt, eq⟩ := found_ok link
      rw [eq]
      have openSlot : s ≠ 0 := by
        intro empty
        subst s
        change i < 0 at hi
        omega
      exact ih (s - 1) (by omega) (by omega) _ lt

private theorem rootImpossible : Impossible true goalFive 7 rootsFive.toFinset := by
  have root : found 7 rootsFive = true := by decide +kernel
  obtain ⟨lt, eq⟩ := found_ok root
  rw [eq]
  exact nodesImpossible 7 (by decide) _ lt

private def witnesses (i : Fin 5) : Row × Row :=
  (![ (2, 3), (1, 3), (9, 13), (5, 13), (6, 22) ] : Fin 5 → Row × Row) i

set_option maxRecDepth 20000 in
private theorem lowerFive : Lower true rootsFive goalFive 8 := by
  apply lower_impossible (L := 7) (by unfold proper; decide +kernel)
    (by decide +kernel) (by decide +kernel) _ rootImpossible
  intro a ha
  rw [rootsFive] at ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  have diff : ∀ j : Fin 5, bit (witnesses j).1 goalFive ≠ bit (witnesses j).2 goalFive := by
    decide +kernel
  have same : ∀ j k : Fin 5, inputFive k ≠ inputFive j →
      bit (witnesses j).1 (inputFive k) = bit (witnesses j).2 (inputFive k) := by
    decide +kernel
  refine ⟨(witnesses i).1, (witnesses i).2, diff i, ?_⟩
  intro v hv vn
  rw [rootsFive] at hv
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
  exact same i j vn

private def sixthInput : Sig := BitVec.ofNat 512 (((2 ^ 256 : Nat) - 1) <<< 256)

private def inputSix (i : Fin 6) : Sig :=
  (![sixthInput, inputFive 0, inputFive 1, inputFive 2, inputFive 3, inputFive 4] : Fin 6 → Sig) i

private def rootsSix : List Sig := List.ofFn inputSix

private def codedSix : Sig := BitVec.ofNat 512 (packedWords [0xeac8e888, 0x3fffffffffff8000, 0x0, 0x0, 0xeff7ddf6fffffcfc, 0x3fffffffffffffef])

private def fixed : Finset Sig := {inputSix 0}

private def trimRow (r : Row) : Row := Fin.ofNat 512 (r.val &&& 255)

private def targetSix (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4277074666 * 2 ^ 32 + 4276153056)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem wholeBoundSix : Lower true rootsSix codedSix 9 := by
  have count : 8 + fixed.card = 9 := by decide +kernel
  rw [← count]
  refine lower_slice (T := codedSix) (G := goalFive) (roots := rootsSix)
    (other := rootsFive) (by unfold proper; decide +kernel) (by decide +kernel)
    (by decide +kernel) (by unfold proper; decide +kernel) trimRow (by decide +kernel)
    ?_ fixed ?_ ?_ 8 lowerFive
  · intro a ha
    rw [rootsSix] at ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    have h : ∀ i : Fin 6, rename trimRow (inputSix i) =
        if i = 0 then zero else inputSix i := by decide +kernel
    rw [h]
    by_cases e : j = 0
    · simp only [e, if_true]
      exact Or.inr (Or.inl ⟨false, funext bit_zero⟩)
    · rw [if_neg e]
      have among : ∀ i : Fin 6, i ≠ 0 → inputSix i ∈ rootsFive := by decide +kernel
      exact Or.inl (List.mem_map_of_mem (among j e))
  · intro a ha
    simp only [fixed, Finset.mem_singleton] at ha
    subst a
    refine ⟨2, 258, by decide +kernel, ?_⟩
    have h : ∀ i : Fin 6, inputSix i ≠ inputSix 0 →
        bit 2 (inputSix i) = bit 258 (inputSix i) := by decide +kernel
    intro v hv hn
    rw [rootsSix] at hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    exact h i hn
  · intro a ha
    simp only [fixed, Finset.mem_singleton] at ha
    subst a
    rw [show rename trimRow (inputSix 0) = zero by decide +kernel]
    exact ⟨false, funext bit_zero⟩



def sampleInputSix (r : Row) (i : Fin 6) : Bool := bit r (inputSix i)

theorem sampledInputSix (r : Row) : List.ofFn (sampleInputSix r) =
    rootsSix.map (bit r) := by
  rw [rootsSix, List.map_ofFn]
  rfl

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem sampleCorrectSix : ∀ r : Row, bit r codedSix = targetSix (sampleInputSix r) := by
  decide +kernel

def signedNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

theorem binaryLowerSix (C : Circuit) (fit : FanInTwo C)
    (comp : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = targetSix x) :
    9 ≤ C.gates.countP (fun g => !signedNot g) := by
  have goalEq : (execute C.gates rootsSix).getD C.output zero = codedSix := by
    apply bit_ext
    intro r
    rw [← b_read, execute_bits _ _ _ (fun g hg => (fit g hg).1), ← sampledInputSix]
    exact (comp (sampleInputSix r)).trans (sampleCorrectSix r).symm
  have out := get_rep (u := true) (execute C.gates rootsSix) C.output
  rw [goalEq] at out
  unfold ForestCore.Repr at out
  have pg : bit 0 codedSix = false := by decide +kernel
  rw [nrm_id pg] at out
  have properGoal : proper codedSix := by unfold proper; decide +kernel
  obtain ⟨k, S, hk, run, sub⟩ := extract (u := true) C.gates rootsSix fit (by simp) properGoal
    (out.resolve_right (fun h => h properGoal))
  change k ≤ C.gates.countP (fun g => !signedNot g) at hk
  rw [nrm_map (by decide +kernel : rootsSix.all plainWord = true)] at sub
  have step := list_run run S.toList (Finset.nodup_toList _) (by simp)
  have ready : supply true (rootsSix.map observe) (S.toList.map observe) := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨q, bank, reach, hit, paid⟩ := contraction (observe_proper properGoal) step _ Reach.start ready
  have lower := wholeBoundSix q bank reach hit
  omega


def witness : Circuit := ⟨[
  ⟨.or, [0, 1]⟩,
  ⟨.and, [2, 3]⟩,
  ⟨.or, [0, 4]⟩,
  ⟨.or, [3, 5]⟩,
  ⟨.or, [5, 6]⟩,
  ⟨.and, [2, 10]⟩,
  ⟨.or, [6, 7]⟩,
  ⟨.and, [9, 8]⟩,
  ⟨.or, [11, 13]⟩,
  ⟨.and, [12, 14]⟩
], 15⟩

theorem witnessBasis : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = targetSix x := by
  decide +kernel

end PEqualNP.Outside.L_meta_16935_aux

open PEqualNP.Outside.L_meta_16935_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_16935 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4276153056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4276153056) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s h
  obtain ⟨C, fan, bound, computes⟩ := h
  by_cases hnot : ∃ g ∈ C.gates, g.op = GateOp.not
  · have paid := binaryLowerSix C fan computes
    obtain ⟨g, hg, hop⟩ := hnot
    have extra : C.gates.countP (fun t => !signedNot t) < C.gates.length := by
      by_contra! large
      have allNot := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length large) g hg
      simp [signedNot, hop] at allNot
    have hw : witness.size = 10 := rfl
    change C.gates.length ≤ s at bound
    exact ⟨witness, witnessBasis, by omega, witnessCorrect⟩
  · refine ⟨C, ?_, bound, computes⟩
    intro g hg
    obtain ⟨ops, len⟩ := fan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ops ⊢
    exact ⟨ops.imp_right (fun h => h.resolve_right fun hn => hnot ⟨g, hg, hn⟩), len⟩
