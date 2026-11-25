import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_13621
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev Sig := BitVec 64
def zero : Sig := 0
def one : Sig := BitVec.allOnes 64
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

def bit (i : Fin 64) (a : Sig) : Bool := a.getLsbD i.val
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

abbrev Row := Fin 64

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

def truth (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4008372968 * 2 ^ 32 + 4008372960)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def candidate : Circuit :=
  ⟨[⟨.and, [1, 5]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [7, 8]⟩,
     ⟨.and, [0, 9]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [2, 11]⟩,
     ⟨.and, [1, 12]⟩, ⟨.or, [10, 13]⟩], 14⟩

theorem witnessSize : candidate.size = 9 := rfl

theorem witnessMonotone : Monotone2 candidate := by
  unfold Monotone2
  simp [candidate]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem witnessComputes : ∀ x : Fin 6 → Bool, candidate.eval (List.ofFn x) = truth x := by
  decide +kernel

def goal : Sig := 0xeeeaeae8eeeaeae0

def inputs : List Sig :=
  [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

def sample (r : Row) (i : Fin 6) : Bool := bit r (inputs.getD i.val zero)

theorem inputsOfFn : List.ofFn (fun i : Fin 6 => inputs.getD i.val zero) = inputs := rfl

theorem sampleList (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [← inputsOfFn, List.map_ofFn]
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem goalTable : ∀ r : Row, bit r goal = truth (sample r) := by decide +kernel

def lowRow (i : Fin 6) : Row := ([4,4,1,1,1,3] : List Row).getD i.val 0
def highRow (i : Fin 6) : Row := Fin.ofNat 64 ((lowRow i).val ||| (1 <<< i.val))

set_option maxHeartbeats 1000000 in
theorem essential :
    (∀ i : Fin 6, bit (lowRow i) goal ≠ bit (highRow i) goal) ∧
    (∀ i j : Fin 6, i ≠ j →
      bit (lowRow i) (inputs.getD j.val zero) = bit (highRow i) (inputs.getD j.val zero)) := by
  decide +kernel

def retain (ws : List Sig) (a b : Sig) (ka kb : Bool) : List Sig :=
  ws.filter (fun x => (x != a || ka) && (x != b || kb))

def successors (ws : List Sig) (cost : ℕ) : List (List Sig) :=
  ws.flatMap fun a => ws.flatMap fun b =>
    if a.toNat < b.toNat then
      [0, 1, 2, 3].flatMap fun d =>
        let c := bin d a b
        if c == zero || c == one || ws.contains c then [] else
        [(false, false), (true, false), (false, true), (true, true)].filterMap fun (ka, kb) =>
          let next := c :: retain ws a b ka kb
          if next.length ≤ cost then some next else none
    else []

lemma retain_membership {ws : List Sig} {a b : Sig} {U : Finset Sig} (hne : a ≠ b)
    (hws : ws.toFinset = insert a (insert b U)) (x : Sig) :
    x ∈ retain ws a b (decide (a ∈ U)) (decide (b ∈ U)) ↔ x ∈ U := by
  have hin : x ∈ ws ↔ x = a ∨ x = b ∨ x ∈ U := by
    rw [← List.mem_toFinset, hws]
    simp
  simp only [retain, List.mem_filter, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq]
  by_cases e : x = a
  · subst x
    simp [hin, hne]
  · by_cases f : x = b
    · subst x
      simp [hin, e]
    · simp [hin, e, f]

lemma ordered_child {ws : List Sig} {a b : Sig} {U : Finset Sig} {d cap : ℕ}
    (order : a.toNat < b.toNat) (hd : allowed true d)
    (hws : ws.toFinset = insert a (insert b U)) (nodup : ws.Nodup)
    (hc : bin d a b ∉ insert a (insert b U)) (hp : proper (bin d a b))
    (limit : (insert (bin d a b) U).card ≤ cap) :
    ∃ next ∈ successors ws cap, next.Nodup ∧ next.toFinset = insert (bin d a b) U := by
  let filtered := retain ws a b (decide (a ∈ U)) (decide (b ∈ U))
  let c := bin d a b
  have hne : a ≠ b := fun he => (Nat.lt_irrefl _) (he ▸ order)
  have mem (x : Sig) : x ∈ filtered ↔ x ∈ U := retain_membership hne hws x
  have hf : c ∉ ws := by
    rw [← List.mem_toFinset, hws]
    exact hc
  have nond : (c :: filtered).Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, nodup.filter _⟩
    intro ch
    exact hc (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ((mem c).mp ch)))
  have hset : (c :: filtered).toFinset = insert c U := by
    ext x
    simp [mem x]
  have le : (c :: filtered).length ≤ cap := by
    rw [← List.toFinset_card_of_nodup nond, hset]
    exact limit
  refine ⟨c :: filtered, ?_, nond, hset⟩
  have ha : a ∈ ws := List.mem_toFinset.mp (hws.symm ▸ Finset.mem_insert_self _ _)
  have hb : b ∈ ws := List.mem_toFinset.mp (hws.symm ▸
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have dd : d ∈ ([0, 1, 2, 3] : List ℕ) := by
    rcases allowed_four hd with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
  unfold successors
  apply List.mem_flatMap.mpr
  refine ⟨a, ha, List.mem_flatMap.mpr ⟨b, hb, ?_⟩⟩
  rw [ite_eq_left order]
  apply List.mem_flatMap.mpr
  refine ⟨d, dd, ?_⟩
  change c :: filtered ∈
    (if c == zero || c == one || ws.contains c then [] else
      [(false, false), (true, false), (false, true), (true, true)].filterMap
        (fun (ka, kb) => if (c :: retain ws a b ka kb).length ≤ cap then
          some (c :: retain ws a b ka kb) else none))
  have good : (c == zero || c == one || ws.contains c) = false := by
    simp [c, hp.1, hp.2, show bin d a b ∉ ws from hf]
  simp only [good, Bool.false_eq_true, ↓reduceIte]
  apply List.mem_filterMap.mpr
  refine ⟨(decide (a ∈ U), decide (b ∈ U)), ?_, ?_⟩
  · cases decide (a ∈ U) <;> cases decide (b ∈ U) <;> simp
  · exact ite_eq_left le

lemma actual_child {ws : List Sig} {a b : Sig} {U : Finset Sig} {d cap : ℕ}
    (ne : a ≠ b) (hd : allowed true d)
    (hws : ws.toFinset = insert a (insert b U)) (nodup : ws.Nodup)
    (hc : bin d a b ∉ insert a (insert b U)) (hp : proper (bin d a b))
    (limit : (insert (bin d a b) U).card ≤ cap) :
    ∃ next ∈ successors ws cap, next.Nodup ∧ next.toFinset = insert (bin d a b) U := by
  by_cases order : a.toNat < b.toNat
  · exact ordered_child order hd hws nodup hc hp limit
  have diff : a.toNat ≠ b.toNat := fun eq => ne (BitVec.eq_of_toNat_eq eq)
  have alt : b.toNat < a.toNat := by omega
  have flip := bin_flip hd a b
  rw [flip] at hc hp limit ⊢
  rw [Finset.insert_comm] at hws hc
  exact ordered_child alt (flip_flip hd).1 hws nodup hc hp limit

lemma goal_eval (C : Circuit) (legal : FanInTwo C)
    (correct : ∀ x, C.eval (List.ofFn x) = truth x) :
    (execute C.gates inputs).getD C.output zero = goal := by
  apply bit_ext
  intro r
  rw [← b_read, execute_bits _ _ _ (fun g hg => (legal g hg).1), ← sampleList]
  change C.eval (List.ofFn (sample r)) = bit r goal
  exact (correct (sample r)).trans (goalTable r).symm

theorem physical (C : Circuit) (legal : FanInTwo C)
    (correct : ∀ x, C.eval (List.ofFn x) = truth x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true goal k inputs.toFinset := by
  have out := get_rep (u := true) (execute C.gates inputs) C.output
  rw [goal_eval C legal correct] at out
  unfold Repr at out
  rw [nrm_id (show bit 0 goal = false by decide)] at out
  have prop : proper goal := by unfold proper; decide
  obtain ⟨k, S, hk, run, sub⟩ := extract (u := true) C.gates inputs legal (by simp) prop
    (out.resolve_right (fun h => h prop))
  rw [show inputs.map (nrm true) = inputs by decide +kernel] at sub
  have pos (a : Sig) (ha : a ∈ inputs) : ∃ i : Fin 6, inputs.getD i.val zero = a := by
    rw [← inputsOfFn] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = inputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i, rfl⟩ := pos a (List.mem_toFinset.mp ha)
      apply raw_required run inputs (inputs.getD i.val zero) sub (lowRow i) (highRow i) (essential.1 i)
      intro v hv hn
      obtain ⟨j, rfl⟩ := pos v hv
      apply essential.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k, hk, eq ▸ run⟩

def positiveRow (code : ℕ) : Row := Fin.ofNat 64 (code % 64)
def negativeRow (code : ℕ) : Row := Fin.ofNat 64 (code / 64)

def recordedConflict (T : Sig) (ws : List Sig) (code : ℕ) : Bool :=
  let r := positiveRow code
  let s := negativeRow code
  (bit r T != bit s T) && ws.all (fun v => bit r v == bit s v)

def certifies (T : Sig) : ℕ → List Sig → List ℕ → Option (List ℕ)
  | _, _, [] => none
  | 0, _, 0 :: _ => none
  | k + 1, ws, 0 :: data =>
      if ws.contains T then none
      else (successors ws (k + 1)).foldlM (fun rem next => certifies T k next rem) data
  | _, ws, (code + 1) :: data =>
      if recordedConflict T ws code then some data else none

lemma cert_fold_mem {α β : Type} {test : β → α → Option β}
    {xs : List α} {init out : β} (success : xs.foldlM test init = some out)
    {x : α} (mem : x ∈ xs) : ∃ i o, test i x = some o := by
  induction xs generalizing init with
  | nil => simp at mem
  | cons y ys ih =>
    simp only [List.foldlM_cons] at success
    rcases eq : test init y with _ | rest
    · simp [eq] at success
    rcases List.mem_cons.mp mem with rfl | tail
    · exact ⟨init, rest, eq⟩
    · apply ih (init := rest) _ tail
      simpa [eq] using success

lemma recordedConflict_excludes {T : Sig} {k : ℕ} {S : Finset Sig} {ws : List Sig} {c : ℕ}
    (run : Live true T k S) (hws : ws.toFinset = S)
    (record : recordedConflict T ws c = true) : False := by
  unfold recordedConflict at record
  have parts := Bool.and_eq_true_iff.mp record
  have diff := bne_iff_ne.mp parts.1
  obtain ⟨v, hv, hn⟩ := live_row_difference run diff
  have mem : v ∈ ws := List.mem_toFinset.mp (hws.symm ▸ hv)
  exact hn (beq_iff_eq.mp (List.all_eq_true.mp parts.2 v mem))

lemma proper_certificate {T : Sig} {cap k : ℕ} {S : Finset Sig}
    (run : Live true T k S) (limit : k ≤ cap)
    {ws : List Sig} (hws : ws.toFinset = S) (nodup : ws.Nodup)
    {data residual : List ℕ} (check : certifies T cap ws data = some residual) : False := by
  induction run using Live.ind generalizing cap ws data residual with
  | stop hp =>
    have hT : T ∈ ws := List.mem_toFinset.mp (hws.symm ▸ Finset.mem_singleton_self _)
    cases data with
    | nil =>
      cases cap <;> simp [certifies] at check
    | cons code data =>
      cases code with
      | zero =>
        cases cap <;> simp [certifies, hT] at check
      | succ code =>
        have hit : recordedConflict T ws code = true := by
          cases cap <;> by_contra! hn <;> simp [certifies, hn] at check
        exact recordedConflict_excludes (Live.stop hp) hws hit
  | @binary k U a b d hd ha hb hne hf tail ih =>
    cases cap with
    | zero => omega
    | succ cap =>
      cases data with
      | nil => simp [certifies] at check
      | cons code data =>
        cases code with
        | zero =>
          have hT : T ∉ ws := by
            intro mem
            simp [certifies, mem] at check
          have checkedTail : (successors ws (cap + 1)).foldlM
              (fun rem next => certifies T cap next rem) data = some residual := by
            simpa [certifies, hT] using check
          have hp := live_proper tail (bin d a b) (Finset.mem_insert_self _ _)
          obtain ⟨next, mem, nextNodup, nextSet⟩ :=
            actual_child hne hd hws nodup hf hp ((live_size tail).trans (by omega))
          obtain ⟨i, o, witness⟩ := cert_fold_mem checkedTail mem
          exact ih (by omega) nextSet nextNodup witness
        | succ code =>
          have hit : recordedConflict T ws code = true := by
            by_contra! hn
            simp [certifies, hn] at check
          exact recordedConflict_excludes (Live.binary hd ha hb hne hf tail) hws hit

def cases0 : List (List Sig) := ((successors inputs 7).drop 0).take 19

set_option maxRecDepth 12000 in
def data0 : List ℕ :=
  [3902, 3903, 3902, 0, 2732, 2148, 2150, 200, 2150, 200, 2154, 204, 2154, 204, 2162, 212, 2162, 212, 0, 684, 100, 200, 0, 200, 647,
   204, 200, 200, 1159, 212, 200, 652, 199, 655, 652, 1822, 650, 1823, 1822, 1302, 1814, 1310, 1302, 782, 1806, 798, 782, 70, 198, 70,
   72, 1303, 1815, 1311, 1303, 783, 1807, 799, 783, 204, 667, 212, 204, 200, 228, 204, 0, 204, 667, 212, 204, 1172, 204, 1179, 1172,
   1822, 650, 1823, 1822, 652, 1818, 655, 652, 652, 1806, 667, 652, 74, 202, 74, 76, 1563, 1819, 1567, 1563, 783, 1807, 799, 783, 200,
   647, 204, 200, 655, 1159, 667, 655, 204, 228, 212, 0, 652, 212, 667, 652, 1822, 1170, 1823, 1822, 1172, 1818, 1175, 1172, 1172, 1814,
   1179, 1172, 82, 210, 82, 84, 1563, 1819, 1567, 1563, 1303, 1815, 1311, 1303, 200, 1159, 212, 200, 1175, 647, 1179, 1175, 204, 667, 212,
   204, 212, 228, 1822, 650, 1823, 1822, 652, 199, 655, 652, 1172, 204, 1179, 1172, 652, 212, 667, 652, 70, 198, 70, 72, 74, 202,
   74, 76, 82, 210, 82, 84, 200, 647, 204, 200, 200, 1159, 212, 200, 204, 667, 212, 204, 228, 0, 652, 0, 70, 1819, 70,
   100, 74, 1815, 74, 100, 82, 1807, 82, 100, 1822, 650, 1823, 1822, 655, 1818, 655, 684, 1179, 676, 1179, 1204, 667, 1188, 667, 684,
   1175, 647, 1179, 1175, 655, 1159, 667, 655, 74, 667, 155, 155, 228, 200, 70, 200, 228, 204, 74, 204, 228, 212, 82, 212, 1822,
   650, 1823, 1822, 655, 200, 655, 200, 1179, 204, 1179, 204, 667, 212, 667, 212, 70, 200, 70, 200, 74, 204, 74, 204, 82, 212,
   82, 212, 200, 647, 204, 200, 200, 1159, 212, 200, 204, 667, 212, 204, 228, 2730, 3903, 3902, 2735, 200, 2735, 200, 3259, 204, 3259,
   204, 2747, 212, 2747, 212, 1822, 228, 1854, 228, 2150, 200, 2150, 200, 2154, 204, 2154, 204, 2162, 212, 2162, 212, 1823, 228, 1855, 228,
   200, 2727, 204, 200, 200, 3239, 212, 200, 200, 2118, 228, 200, 204, 2747, 212, 204, 204, 2122, 228, 204, 212, 2130, 228, 212, 2730,
   2148, 2732, 0, 0, 200, 2727, 204, 200, 200, 3239, 212, 200, 200, 2118, 228, 200, 2732, 199, 2735, 2732, 3642, 2730, 3643, 3642, 3252,
   2724, 3259, 3252, 2732, 3236, 2747, 2732, 652, 2700, 684, 652, 2148, 198, 2150, 2148, 2148, 202, 2154, 2148, 2148, 210, 2162, 2148, 1563, 228,
   100, 100, 204, 2747, 212, 204, 204, 2122, 228, 204, 212, 2130, 228, 212, 200, 0, 2735, 2732, 199, 2732, 2150, 2148, 198, 2148, 200,
   204, 2727, 200, 200, 212, 3239, 200, 200, 228, 2118, 200, 2730, 2730, 2732, 2148, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 652, 2700,
   684, 652, 2148, 202, 2154, 2148, 2148, 210, 2162, 2148, 1567, 228, 100, 100, 204, 2747, 212, 204, 204, 2122, 228, 204, 212, 2130, 228,
   212, 200, 0, 200, 2727, 200, 204, 204, 2747, 212, 204, 204, 2122, 228, 204, 3252, 2724, 3259, 3252, 2730, 2730, 2732, 3382, 2732, 199,
   2735, 2732, 2732, 3236, 2747, 2732, 652, 2700, 684, 652, 2148, 202, 2154, 2148, 2148, 2735, 2150, 2735, 2148, 2747, 2162, 2747, 1303, 228, 100,
   100, 2735, 3239, 2747, 2735, 655, 2703, 687, 655, 667, 2715, 699, 667, 204, 0, 3259, 3252, 2724, 3252, 2154, 2148, 202, 2148, 204, 200,
   2727, 200, 204, 212, 2747, 204, 204, 228, 2122, 204, 3250, 3250, 3252, 2148, 3252, 199, 3255, 3252, 2212, 3236, 2228, 2212, 1172, 3220, 1204,
   1172, 2148, 198, 2150, 2148, 2148, 210, 2162, 2148, 1311, 228, 100, 100, 200, 3239, 212, 200, 200, 2118, 228, 200, 212, 2130, 228, 212,
   204, 0, 200, 3239, 200, 212, 204, 2747, 204, 212, 212, 2130, 228, 212, 2732, 3236, 2747, 2732, 3250, 3250, 3252, 2862, 3252, 199, 3255,
   3252, 3252, 2724, 3259, 3252, 1172, 3220, 1204, 1172, 2148, 210, 2162, 2148, 2148, 3255, 2150, 3255, 2148, 3259, 2154, 3259, 783, 228, 100, 100,
   3255, 2727, 3259, 3255, 1175, 3223, 1207, 1175, 1179, 3227, 1211, 1179, 212, 0, 2747, 2732, 3236, 2732, 2162, 2148, 210, 2148, 212, 200, 3239,
   200, 212, 204, 2747, 204, 212, 228, 2130, 212, 2730, 2730, 2732, 2148, 2732, 199, 2735, 2732, 2212, 2724, 2220, 2212, 652, 2700, 684, 652,
   2148, 198, 2150, 2148, 2148, 202, 2154, 2148, 799, 228, 100, 100, 200, 2727, 204, 200, 200, 2118, 228, 200, 204, 2122, 228, 204, 212,
   0, 200, 2118, 200, 228, 204, 2122, 204, 228, 212, 2130, 212, 228, 652, 2700, 684, 652, 2730, 2730, 2732, 2148, 2732, 2150, 2735, 2732,
   3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 1823, 228, 100, 100, 2148, 2735, 2150, 2148, 2148, 3259, 2154, 2148, 2148, 2747, 2162, 2148, 2150,
   2727, 2154, 2150, 2150, 3239, 2162, 2150, 2154, 2747, 2162, 2154, 228, 0, 684, 652, 2700, 652, 100, 100, 228, 1823, 228, 200, 2118, 200,
   228, 204, 2122, 204, 228, 212, 2130, 212, 650, 650, 652, 1854, 652, 199, 655, 652, 1172, 204, 1179, 1172, 652, 212, 667, 652, 70,
   198, 70, 72, 74, 202, 74, 76, 82, 210, 82, 84, 200, 647, 204, 200, 200, 1159, 212, 200, 204, 667, 212, 204, 228, 3902,
   2730, 2732, 2148, 2732, 199, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 652, 2700, 684, 652, 3903, 2148, 198, 2150, 2148, 2148,
   202, 2154, 2148, 2148, 210, 2162, 2148, 0, 1855, 70, 2703, 70, 100, 74, 3227, 74, 100, 82, 2715, 82, 100, 1563, 2735, 1567, 2735,
   1303, 3259, 1311, 3259, 783, 2747, 799, 2747, 650, 2698, 684, 650, 1822, 2732, 70, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732,
   3255, 2727, 3259, 3255, 2735, 3239, 2747, 2735, 74, 2747, 2235, 2235, 228, 100, 100, 200, 2727, 204, 200, 200, 3239, 212, 200, 200, 2118,
   228, 200, 204, 2747, 212, 204, 204, 2122, 228, 204, 212, 2130, 228, 212, 3903, 3903, 2732, 0, 3902, 2148, 200, 2150, 200, 2150, 204,
   2154, 204, 2154, 212, 2162, 212, 2162, 228, 0, 652, 2700, 684, 652, 3870, 2698, 3903, 3870, 2732, 3866, 2735, 2732, 3252, 2724, 3259, 3252,
   2732, 3236, 2747, 2732, 1823, 100, 100, 228, 70, 3899, 70, 100, 74, 3895, 74, 100, 82, 3887, 82, 100, 200, 70, 228, 200, 70,
   2727, 74, 70, 70, 3239, 82, 70, 204, 74, 228, 204, 74, 2747, 82, 74, 212, 82, 228, 212, 228, 0, 200, 2703, 200, 228,
   204, 3227, 204, 228, 212, 2715, 212, 228, 652, 2700, 684, 652, 3903, 2732, 3903, 3904, 2732, 199, 2735, 2732, 3252, 2724, 3259, 3252, 2732,
   3236, 2747, 2732, 1823, 228, 100, 100, 3643, 3899, 3647, 3643, 3383, 3895, 3391, 3383, 2863, 3887, 2879, 2863, 3255, 2727, 3259, 3255, 2735, 3239,
   2747, 2735, 204, 2747, 2235, 2235, 3903, 2732, 3904, 2732, 2150, 2735, 2150, 3252, 2154, 3259, 2154, 2732, 2162, 2747, 2162, 652, 2700, 684, 652,
   2150, 200, 2150, 200, 2154, 204, 2154, 204, 2162, 212, 2162, 212, 1823, 228, 1855, 228, 2150, 2727, 2154, 2150, 2150, 3239, 2162, 2150, 70,
   2118, 102, 70, 2154, 2747, 2162, 2154, 74, 2122, 106, 74, 82, 2130, 114, 82, 3902, 2148, 3902, 0, 2732, 3903, 200, 2735, 200, 2735,
   204, 3259, 204, 3259, 212, 2747, 212, 2747, 228, 0, 652, 652, 684, 228, 3871, 682, 3871, 3902, 655, 3898, 655, 684, 1179, 676, 1179,
   1204, 667, 1188, 667, 684, 0, 70, 1819, 70, 100, 74, 1815, 74, 100, 82, 1807, 82, 100, 1822, 650, 1823, 1822, 655, 1818, 655,
   684, 1179, 676, 1179, 1204, 667, 1188, 667, 684, 1175, 647, 1179, 1175, 655, 1159, 667, 655, 74, 667, 155, 155, 228, 100, 100, 2148,
   3867, 2150, 2148, 2148, 3863, 2154, 2148, 2148, 3855, 2162, 2148, 200, 2118, 228, 200, 2150, 647, 2154, 2150, 2150, 1159, 2162, 2150, 204, 2122,
   228, 204, 2154, 667, 2162, 2154, 212, 2130, 228, 212, 228, 0, 1823, 228, 100, 100, 200, 2118, 200, 228, 204, 2122, 204, 228, 212,
   2130, 212, 228, 652, 228, 684, 652, 3902, 2148, 3904, 3902, 3642, 3898, 3646, 3642, 3382, 3894, 3390, 3382, 2862, 3886, 2878, 2862, 2148, 198,
   2150, 2148, 2148, 202, 2154, 2148, 2148, 210, 2162, 2148, 2150, 647, 2154, 2150, 2150, 1159, 2162, 2150, 2154, 667, 2162, 2154, 3902, 2148, 3904,
   2735, 200, 2735, 200, 3259, 204, 3259, 204, 2747, 212, 2747, 212, 1822, 228, 1854, 228, 2148, 2735, 2150, 2735, 2148, 3259, 2154, 3259, 2148,
   2747, 2162, 2747, 0, 655, 2703, 655, 687, 1179, 3227, 1179, 1211, 667, 2715, 667, 699, 100, 0, 70, 1819, 70, 100, 74, 1815, 74,
   100, 82, 1807, 82, 100, 1822, 650, 1823, 1822, 655, 1818, 655, 684, 1179, 676, 1179, 1204, 667, 1188, 667, 684, 1175, 647, 1179, 1175,
   655, 1159, 667, 655, 74, 667, 155, 155, 100, 1823, 2732, 70, 2735, 70, 2735, 74, 3259, 74, 3259, 82, 2747, 82, 2747, 1822, 100,
   1856, 1822, 2735, 1818, 2735, 1562, 3259, 1814, 3259, 1302, 2747, 1806, 2747, 782, 3255, 2727, 3259, 3255, 2735, 3239, 2747, 2735, 74, 2747, 2235,
   2235, 228, 100, 100, 3255, 2727, 3259, 3255, 2735, 3239, 2747, 2735, 655, 2703, 687, 655, 204, 2747, 2235, 2235, 1179, 3227, 1211, 1179, 667,
   2715, 699, 667, 2732, 2735, 2732]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem proof0 : cases0.foldlM (fun rem next => certifies goal 6 next rem) data0 = some [] := by
  decide +kernel

def cases1 : List (List Sig) := ((successors inputs 7).drop 19).take 12

set_option maxRecDepth 12000 in
def data1 : List ℕ :=
  [0, 3902, 2148, 0, 2148, 198, 2150, 2148, 2148, 202, 2154, 2148, 2148, 210, 2162, 2148, 1823, 228, 100, 100, 3903, 2730, 3902, 3902, 2732,
   198, 2734, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 652, 2700, 684, 652, 198, 2727, 204, 198, 198, 3239, 212, 198, 198, 2703,
   228, 198, 204, 2747, 212, 204, 204, 3227, 228, 204, 212, 2715, 228, 212, 2148, 0, 3902, 2730, 3902, 3903, 2148, 198, 2150, 2148, 2148,
   202, 2154, 2148, 2148, 210, 2162, 2148, 1823, 228, 100, 100, 2732, 199, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 652, 2700,
   684, 652, 204, 2727, 204, 3255, 212, 3239, 212, 2735, 228, 2703, 228, 655, 204, 2747, 212, 204, 204, 3227, 228, 204, 212, 2715, 228,
   212, 200, 204, 0, 204, 2747, 212, 204, 204, 2122, 228, 204, 3252, 2724, 3259, 3252, 3894, 2730, 3896, 3894, 2732, 3894, 2728, 2728, 2732,
   3878, 2747, 2732, 652, 2700, 684, 652, 2148, 202, 2154, 2148, 3643, 3899, 3647, 3643, 2863, 3887, 2879, 2863, 1823, 3871, 1855, 1823, 204, 2727,
   200, 200, 2735, 3239, 2747, 2735, 655, 2703, 687, 655, 667, 2715, 699, 667, 204, 0, 3252, 2724, 3252, 3259, 2148, 202, 2148, 2154, 200,
   2727, 200, 204, 204, 2747, 212, 204, 204, 2122, 228, 204, 3903, 2730, 3903, 3642, 2732, 3898, 2735, 2732, 2732, 3626, 2747, 2732, 652, 2700,
   684, 652, 3643, 3899, 3647, 3643, 2863, 3887, 2879, 2863, 1823, 3871, 1855, 1823, 2735, 3239, 2747, 2735, 655, 2703, 687, 655, 667, 2715, 699,
   667, 212, 0, 212, 2130, 228, 212, 2732, 3236, 2747, 2732, 3886, 3250, 3888, 3886, 3252, 3886, 3240, 3240, 3252, 3878, 3259, 3252, 1172, 3220,
   1204, 1172, 2148, 210, 2162, 2148, 3643, 3899, 3647, 3643, 3383, 3895, 3391, 3383, 1823, 3871, 1855, 1823, 212, 3239, 200, 200, 3255, 2727, 3259,
   3255, 1175, 3223, 1207, 1175, 204, 2747, 212, 204, 1179, 3227, 1211, 1179, 212, 0, 2732, 3236, 2732, 2747, 2148, 210, 2148, 2162, 200, 3239,
   200, 212, 204, 2747, 204, 212, 212, 2130, 228, 212, 3903, 3250, 3903, 3642, 3252, 3898, 3255, 3252, 3252, 3634, 3259, 3252, 1172, 3220, 1204,
   1172, 3643, 3899, 3647, 3643, 3383, 3895, 3391, 3383, 1823, 3871, 1855, 1823, 3255, 2727, 3259, 3255, 1175, 3223, 1207, 1175, 1179, 3227, 1211, 1179,
   228, 0, 652, 2700, 684, 652, 3870, 2730, 3872, 3870, 2732, 3870, 2704, 2704, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 1823, 228, 100,
   100, 2118, 3899, 2118, 2120, 2148, 3895, 2154, 2148, 2148, 3887, 2162, 2148, 228, 2118, 200, 200, 2118, 2727, 2126, 2118, 2118, 3239, 2134, 2118,
   204, 2122, 228, 204, 2154, 2747, 2162, 2154, 212, 2130, 228, 212, 228, 0, 652, 2700, 652, 684, 1823, 228, 100, 100, 200, 2118, 200,
   228, 204, 2122, 204, 228, 212, 2130, 212, 228, 3903, 2730, 3903, 3642, 2732, 3898, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732,
   2148, 3899, 3647, 2148, 2148, 3895, 2154, 2148, 2148, 3887, 2162, 2148, 2154, 2727, 2154, 3255, 2162, 3239, 2162, 2735, 2154, 2747, 2162, 2154, 3903,
   2730, 3903, 3642, 199, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 652, 2700, 684, 652, 2148, 3899, 3647, 2148, 2148, 202, 2154,
   2148, 2148, 210, 2162, 2148, 1823, 228, 100, 100, 204, 2727, 204, 3255, 212, 3239, 212, 2735, 228, 2703, 228, 655, 204, 2747, 212, 204,
   204, 2122, 228, 204, 212, 2130, 228, 212, 199, 200, 3902, 0, 3259, 204, 3259, 204, 2747, 212, 2747, 212, 0, 204, 2122, 204, 228,
   212, 2130, 212, 228, 652, 228, 684, 652, 3902, 2148, 3903, 3902, 3898, 3898, 3902, 2150, 3382, 3894, 3390, 3382, 2862, 3886, 2878, 2862, 1823,
   228, 100, 100, 2148, 3903, 2150, 2148, 2148, 3895, 2154, 2148, 2148, 3887, 2162, 2148, 200, 2118, 228, 200, 2150, 647, 2154, 2150, 2150, 1159,
   2162, 2150, 2154, 667, 2162, 2154, 228, 0, 684, 228, 652, 652, 100, 100, 228, 1823, 228, 200, 2118, 200, 228, 204, 2122, 204, 228,
   212, 2130, 212, 1822, 682, 1823, 1822, 199, 199, 1822, 200, 1302, 204, 1310, 204, 782, 212, 798, 212, 70, 198, 70, 72, 74, 202,
   74, 76, 82, 210, 82, 84, 200, 679, 204, 200, 200, 1191, 212, 200, 204, 667, 212, 204, 228, 2732, 3902, 2148, 3903, 3902, 199,
   3902, 200, 3382, 204, 3390, 204, 2862, 212, 2878, 212, 1822, 228, 1854, 228, 3643, 2148, 2148, 3643, 2148, 198, 2150, 2148, 2148, 202, 2154,
   2148, 2148, 210, 2162, 2148, 1823, 228, 100, 100, 2735, 200, 0, 200, 2747, 212, 200, 200, 2118, 228, 200, 3259, 200, 3255, 200, 2727,
   212, 2743, 2727, 647, 2695, 679, 647, 199, 199, 3382, 200, 2728, 3382, 2148, 3383, 3382, 2342, 3366, 2358, 2342, 1302, 3350, 1334, 1302, 2148,
   198, 2150, 2148, 3387, 3383, 3383, 3639, 2343, 3367, 2359, 2343, 1303, 3351, 1335, 1303, 667, 2715, 699, 667, 204, 200, 200, 0, 200, 2118,
   228, 200, 2747, 200, 2735, 200, 3239, 204, 3247, 3239, 1159, 3207, 1191, 1159, 199, 199, 2862, 200, 3240, 2862, 2148, 2863, 2862, 2342, 2854,
   2350, 2342, 782, 2830, 814, 782, 2148, 198, 2150, 2148, 2875, 2863, 2863, 3631, 2343, 2855, 2351, 2343, 783, 2831, 815, 783, 200, 2747, 200,
   204, 1179, 3227, 1211, 1179, 212, 200, 200, 2118, 228, 200, 204, 2747, 212, 204, 204, 2122, 228, 204, 212, 2130, 228, 212, 2735, 2735,
   3902, 0, 2732, 3903, 2148, 3903, 2148, 200, 3259, 204, 3259, 204, 2747, 212, 2747, 212, 0, 684, 1823, 228, 100, 100, 2118, 204, 2122,
   204, 228, 212, 2130, 212, 228, 1822, 2148, 1823, 2148, 652, 199, 655, 652, 1172, 2154, 1179, 2154, 652, 2162, 667, 2162, 2148, 198, 70,
   2148, 2148, 202, 2154, 2148, 2148, 210, 2162, 2148, 2154, 647, 2154, 200, 2162, 1159, 2162, 200, 2154, 667, 2162, 2154, 228, 0, 652, 100,
   100, 228, 0, 70, 1819, 70, 72, 74, 1815, 74, 100, 82, 1807, 82, 100, 1822, 650, 1823, 1822, 655, 1818, 655, 656, 1179, 676,
   1179, 1204, 667, 1188, 667, 684, 1175, 647, 1179, 1175, 655, 1159, 667, 655, 74, 667, 155, 155, 200, 228, 204, 2122, 204, 228, 212,
   2130, 212, 1822, 682, 1823, 1822, 655, 1822, 655, 656, 1179, 204, 1179, 204, 667, 212, 667, 212, 2118, 1819, 2118, 2120, 74, 202, 74,
   76, 82, 210, 82, 84, 204, 647, 204, 2118, 212, 1159, 212, 2118, 204, 667, 212, 204, 228, 3902, 2148, 3903, 2148, 2735, 3902, 2736,
   3259, 204, 3259, 204, 2747, 212, 2747, 212, 1822, 228, 1854, 228, 2148, 3899, 3647, 2148, 2148, 202, 2154, 2148, 2148, 210, 2162, 2148, 1823,
   228, 100, 100, 204, 2727, 204, 3255, 212, 3239, 212, 2735, 228, 2703, 228, 655, 204, 2747, 212, 204, 204, 2122, 228, 204, 212, 2130,
   228, 212, 2732, 200, 2732]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem proof1 : cases1.foldlM (fun rem next => certifies goal 6 next rem) data1 = some [] := by
  decide +kernel

def cases2 : List (List Sig) := ((successors inputs 7).drop 31).take 12

set_option maxRecDepth 12000 in
def data2 : List ℕ :=
  [0, 3902, 2148, 3903, 2148, 3903, 2735, 204, 0, 204, 2747, 212, 204, 204, 2122, 228, 204, 3252, 2724, 3259, 3252, 3383, 2730, 3383, 3390,
   2727, 3386, 2727, 2732, 2732, 3374, 2747, 2732, 652, 2700, 684, 652, 2148, 202, 2154, 2148, 3387, 3383, 3383, 3639, 2343, 3367, 2359, 2343, 1303,
   3351, 1335, 1303, 200, 2727, 204, 200, 2727, 0, 647, 2695, 679, 647, 200, 2727, 200, 204, 1159, 3207, 1191, 1159, 2727, 2346, 2727, 2732,
   3239, 2342, 3239, 3240, 2343, 3238, 2343, 2350, 270, 2318, 302, 270, 2148, 2343, 2343, 2599, 2148, 2343, 2343, 3111, 263, 2311, 295, 263, 2743,
   2727, 647, 2695, 679, 647, 667, 2715, 699, 667, 204, 0, 2148, 202, 2148, 2154, 200, 2727, 200, 204, 204, 2747, 212, 204, 204, 2122,
   228, 204, 3252, 2724, 3259, 3252, 3642, 2730, 3643, 3642, 2732, 199, 2736, 2732, 2732, 3626, 2747, 2732, 652, 2700, 684, 652, 3643, 198, 2150,
   3643, 2148, 2747, 2619, 2619, 1563, 3611, 1595, 1563, 2747, 3239, 2747, 200, 200, 2118, 228, 200, 667, 2715, 699, 667, 212, 0, 212, 2130,
   228, 212, 2732, 3236, 2747, 2732, 2863, 3250, 2863, 2878, 3239, 2874, 3239, 3252, 3252, 2870, 3259, 3252, 1172, 3220, 1204, 1172, 2148, 210, 2162,
   2148, 2875, 2863, 2863, 3631, 2343, 2855, 2351, 2343, 783, 2831, 815, 783, 200, 3239, 212, 200, 3239, 0, 200, 2727, 212, 200, 1159, 3207,
   1191, 1159, 647, 2695, 679, 647, 3239, 2354, 3239, 3252, 2727, 2342, 2727, 2728, 2343, 2726, 2343, 2358, 278, 2326, 310, 278, 2148, 2343, 2343,
   3111, 2148, 2343, 2343, 2599, 263, 2311, 295, 263, 3247, 3239, 1159, 3207, 1191, 1159, 204, 2747, 212, 204, 1179, 3227, 1211, 1179, 212, 0,
   2148, 210, 2148, 2162, 200, 3239, 200, 212, 204, 2747, 204, 212, 212, 2130, 228, 212, 2732, 3236, 2747, 2732, 3642, 3250, 3643, 3642, 3252,
   199, 3256, 3252, 3252, 3634, 3259, 3252, 1172, 3220, 1204, 1172, 3643, 198, 2150, 3643, 2148, 3259, 3131, 3131, 1563, 3611, 1595, 1563, 3259, 2727,
   3259, 200, 200, 2118, 228, 200, 1179, 3227, 1211, 1179, 228, 0, 652, 2700, 684, 652, 1823, 2730, 1823, 1854, 2703, 1850, 2703, 2732, 3252,
   2724, 3259, 3252, 2732, 3236, 2747, 2732, 1563, 228, 100, 100, 2148, 1823, 2150, 2148, 2148, 1815, 2154, 2148, 2148, 1807, 2162, 2148, 200, 2118,
   228, 200, 2150, 2695, 2154, 2150, 2150, 3207, 2162, 2150, 204, 2122, 228, 204, 2154, 2747, 2162, 2154, 212, 2130, 228, 212, 228, 0, 1823,
   228, 100, 100, 200, 2118, 200, 228, 204, 2122, 204, 228, 212, 2130, 212, 228, 652, 2700, 684, 652, 3642, 2730, 3643, 3642, 2732, 2150,
   2736, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 2148, 198, 2150, 2148, 2148, 3259, 2154, 2148, 2148, 2747, 2162, 2148, 2150, 647, 2154,
   2150, 2150, 1159, 2162, 2150, 2154, 2747, 2162, 2154, 3903, 2730, 3903, 3642, 2732, 200, 2736, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 652,
   2700, 684, 652, 2148, 3903, 3903, 2148, 3383, 3895, 3391, 3383, 2863, 3887, 2879, 2863, 1823, 3871, 1855, 1823, 200, 0, 200, 2747, 212, 200,
   200, 2118, 228, 200, 3255, 3382, 3387, 3383, 3639, 3383, 2727, 0, 647, 2695, 679, 647, 200, 2727, 212, 200, 1159, 3207, 1191, 1159, 2727,
   2342, 2727, 2728, 3239, 2354, 3239, 3252, 2343, 3250, 2343, 2358, 278, 2326, 310, 278, 2148, 2343, 2343, 2599, 2148, 2343, 2343, 3111, 263, 2311,
   295, 263, 2743, 2727, 647, 2695, 679, 647, 3252, 2724, 3256, 3252, 3383, 2726, 3383, 3638, 2728, 3622, 2744, 2728, 648, 2696, 680, 648, 2148,
   3383, 3383, 2148, 2343, 3367, 2359, 2343, 1303, 3351, 1335, 1303, 667, 2715, 699, 667, 204, 200, 200, 0, 200, 2118, 228, 200, 2735, 2862,
   2875, 2863, 3631, 2863, 3239, 0, 200, 2727, 200, 204, 1159, 3207, 1191, 1159, 647, 2695, 679, 647, 3239, 2342, 3239, 3240, 2727, 2346, 2727,
   2732, 2343, 2730, 2343, 2350, 270, 2318, 302, 270, 2148, 2343, 2343, 3111, 2148, 2343, 2343, 2599, 263, 2311, 295, 263, 3247, 3239, 1159, 3207,
   1191, 1159, 2732, 3236, 2736, 2732, 2863, 3238, 2863, 3630, 3240, 3622, 3248, 3240, 1160, 3208, 1192, 1160, 2148, 2863, 2863, 2148, 2343, 2855, 2351,
   2343, 783, 2831, 815, 783, 200, 2747, 200, 204, 1179, 3227, 1211, 1179, 212, 200, 200, 2118, 228, 200, 204, 2747, 212, 204, 204, 2122,
   228, 204, 212, 2130, 228, 212, 3252, 3259, 3252, 0, 2732, 2148, 0, 2148, 198, 2150, 2148, 2148, 202, 2154, 2148, 2148, 210, 2162, 2148,
   1823, 228, 100, 100, 3903, 2730, 3902, 3902, 2730, 199, 2734, 2730, 3252, 2724, 3258, 3252, 2730, 3236, 2746, 2730, 650, 2698, 682, 650, 200,
   2727, 202, 200, 200, 3239, 212, 200, 200, 2703, 228, 200, 202, 2747, 212, 202, 202, 3227, 228, 202, 212, 2715, 228, 212, 2148, 0,
   3902, 2730, 3902, 3903, 2148, 198, 2150, 2148, 2148, 202, 2154, 2148, 2148, 210, 2162, 2148, 1823, 228, 100, 100, 2735, 199, 2735, 3252, 3252,
   2724, 3259, 3252, 2747, 3236, 2747, 2212, 1172, 3220, 1204, 1172, 200, 2727, 3259, 200, 200, 3239, 212, 200, 200, 2703, 228, 200, 212, 2747,
   212, 2235, 228, 3227, 228, 1179, 212, 2715, 228, 212, 200, 0, 200, 2727, 204, 200, 200, 3239, 212, 200, 200, 2118, 228, 200, 2735,
   199, 2732, 2732, 3898, 3250, 3900, 3898, 3382, 3894, 3386, 3382, 2858, 3882, 2874, 2858, 1818, 3866, 1850, 1818, 2148, 198, 2150, 2148, 3383, 3895,
   3391, 3383, 2863, 3887, 2879, 2863, 1823, 3871, 1855, 1823, 212, 2747, 212, 2235, 228, 3227, 228, 1179, 212, 2130, 228, 212, 200, 0, 2732,
   199, 2732, 2735, 2148, 198, 2148, 2150, 200, 2727, 204, 200, 200, 3239, 212, 200, 200, 2118, 228, 200, 3903, 2730, 3903, 3382, 3382, 3894,
   3259, 3382, 2342, 3366, 2358, 2342, 1302, 3350, 1334, 1302, 3383, 3895, 3391, 3383, 2863, 3887, 2879, 2863, 1823, 3871, 1855, 1823, 204, 2747, 212,
   204, 204, 2122, 228, 204, 212, 2130, 228, 212, 204, 212, 0, 212, 2130, 228, 212, 2747, 3236, 2732, 2732, 3886, 3250, 3888, 3886, 3252,
   3882, 3255, 3252, 3252, 3886, 3244, 3244, 1172, 3220, 1204, 1172, 2148, 210, 2162, 2148, 3643, 3899, 3647, 3643, 3383, 3895, 3391, 3383, 1823, 3871,
   1855, 1823, 200, 3239, 212, 200, 3255, 2727, 3259, 3255, 1175, 3223, 1207, 1175, 212, 2747, 204, 204, 1179, 3227, 1211, 1179, 212, 0, 2732,
   3236, 2732, 2747, 2148, 210, 2148, 2162, 200, 3239, 200, 212, 204, 2747, 204, 212, 212, 2130, 228, 212, 3903, 3250, 3903, 3382, 3252, 3378,
   3255, 3252, 3252, 3894, 3259, 3252, 1172, 3220, 1204, 1172, 3643, 3899, 3647, 3643, 3383, 3895, 3391, 3383, 1823, 3871, 1855, 1823, 3255, 2727, 3259,
   3255, 1175, 3223, 1207, 1175, 1179, 3227, 1211, 1179, 228, 0, 1172, 2700, 652, 652, 3870, 2698, 3872, 3870, 2700, 3866, 2704, 2700, 3252, 2700,
   3228, 3228, 2700, 3236, 2716, 2700, 1823, 228, 100, 100, 2148, 3899, 2150, 2148, 2122, 3895, 2122, 2124, 2148, 3887, 2162, 2148, 200, 2118, 228,
   200, 2122, 2727, 2122, 2126, 2150, 3239, 2162, 2150, 228, 2122, 204, 204, 2122, 2747, 2138, 2122, 212, 2130, 228, 212, 228, 0, 652, 2700,
   652, 1204, 1823, 228, 100, 100, 200, 2118, 200, 228, 204, 2122, 204, 228, 212, 2130, 212, 228, 3903, 3250, 3903, 3382, 2735, 3378, 2735,
   3252, 3252, 2724, 3259, 3252, 2747, 3236, 2747, 2212, 2148, 3899, 2150, 2148, 2148, 3895, 3391, 2148, 2148, 3887, 2162, 2148, 2150, 2727, 3259, 2150,
   2150, 3239, 2162, 2150, 2162, 2747, 2162, 2235, 3903, 3250, 3903, 3382, 2735, 199, 2735, 3252, 2724, 3259, 3252, 2747, 3236, 2747, 2212, 1172, 3220,
   1204, 1172, 2148, 198, 2150, 2148, 2148, 3895, 3391, 2148, 2148, 210, 2162, 2148, 1823, 228, 100, 100, 200, 2727, 3259, 200, 200, 3239, 212,
   200, 200, 2118, 228, 200, 212, 2747, 212, 2235, 228, 3227, 228, 1179, 212, 2130, 228, 212, 2724, 204, 2732, 0, 0, 212, 2130, 228,
   212, 2732, 212, 2747, 2732, 3902, 2730, 3903, 3902, 3642, 3898, 3646, 3642, 3894, 3894, 3902, 2212, 1822, 3870, 1854, 1822, 2148, 210, 2162, 2148,
   3643, 3899, 3647, 3643, 2148, 3903, 3903, 2148, 1823, 3871, 1855, 1823, 200, 0, 200, 2118, 228, 200, 2732, 199, 2735, 2732, 2862, 2730, 2863,
   2862, 2342, 2854, 2350, 2342, 782, 2830, 814, 782, 2148, 198, 2150, 2148, 2343, 2855, 2351, 2343, 783, 2831, 815, 783, 200, 2727, 200, 204,
   204, 2122, 228, 204, 212, 200, 200, 2727, 204, 200, 200, 2118, 228, 200, 204, 2747, 212, 204, 204, 2122, 228, 204, 212, 0, 2747,
   2732, 2212, 2732, 2162, 2148, 210, 2148, 212, 200, 2215, 200, 212, 204, 2235, 204, 212, 228, 2130, 212, 2862, 2730, 2863, 2862, 2732, 200,
   2735, 2732, 2724, 2724, 2732, 204, 652, 2700, 684, 652, 2148, 198, 2150, 2148, 2148, 202, 2154, 2148, 783, 228, 100, 100, 200, 2735, 204,
   200, 200, 2118, 228, 200, 204, 2122, 228, 204, 212, 0, 212, 2130, 212, 228, 652, 2700, 684, 652, 3902, 2730, 3903, 3902, 2732, 3898,
   2735, 2732, 2724, 2724, 2732, 2154, 2732, 3886, 2747, 2732, 1823, 228, 100, 100, 2148, 3899, 2150, 2148, 2148, 3903, 2154, 2148, 2148, 3887, 2162,
   2148, 200, 2118, 228, 200, 2150, 2735, 2154, 2150, 2150, 1159, 2162, 2150, 204, 2122, 228, 204, 2154, 2747, 2162, 2154, 228, 0, 684, 652,
   2700, 652, 100, 100, 228, 1823, 228, 200, 2118, 200, 228, 204, 2122, 204, 228, 212, 2130, 212, 1822, 650, 1823, 1822, 652, 200, 655,
   652, 1814, 204, 652, 204, 652, 212, 667, 652, 70, 198, 70, 72, 74, 202, 74, 76, 82, 210, 82, 84, 200, 655, 204, 200,
   200, 1159, 212, 200, 204, 667, 212, 204, 228, 3252, 3902, 2730, 3903, 3902, 2732, 200, 2735, 2732, 2724, 2732, 204, 2732, 212, 2747, 2732,
   652, 2700, 684, 652, 3383, 2148, 2148, 3383, 2148, 198, 2150, 2148, 2148, 202, 2154, 2148, 2148, 210, 2162, 2148, 1823, 228, 100, 100, 3255,
   200, 200, 3255, 200, 2735, 204, 200, 200, 3239, 212, 200, 200, 2118, 228, 200, 3259, 204, 2747, 212, 204, 204, 2122, 228, 204, 212,
   2130, 228, 212, 3259, 3259, 2732]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem proof2 : cases2.foldlM (fun rem next => certifies goal 6 next rem) data2 = some [] := by
  decide +kernel

def cases3 : List (List Sig) := ((successors inputs 7).drop 43).take 20

set_option maxRecDepth 12000 in
def data3 : List ℕ :=
  [0, 3252, 3903, 2148, 3903, 2148, 2735, 200, 2735, 200, 204, 2747, 212, 2747, 212, 0, 1204, 1823, 228, 100, 100, 200, 2118, 200, 228,
   2122, 212, 2130, 212, 228, 1822, 2148, 1823, 2148, 652, 2150, 655, 2150, 1172, 204, 1179, 1172, 652, 2162, 667, 2162, 2148, 198, 2150, 2148,
   2148, 202, 74, 2148, 2148, 210, 2162, 2148, 2150, 647, 204, 2150, 2150, 1159, 2162, 2150, 2162, 667, 2162, 204, 228, 0, 1172, 100, 100,
   228, 0, 70, 1819, 70, 100, 74, 1815, 74, 76, 82, 1807, 82, 100, 1822, 650, 1823, 1822, 652, 1818, 655, 652, 1179, 652, 1179,
   1180, 652, 1188, 667, 652, 1175, 647, 1179, 1175, 655, 1159, 667, 655, 74, 667, 155, 155, 228, 200, 2118, 200, 204, 228, 212, 2130,
   212, 1822, 650, 1823, 1822, 652, 200, 655, 200, 1179, 652, 1179, 1180, 652, 212, 667, 212, 70, 198, 70, 72, 2122, 1815, 2122, 2124,
   82, 210, 82, 84, 200, 647, 2122, 200, 200, 1159, 212, 200, 212, 667, 212, 2122, 228, 3902, 2148, 3903, 2148, 2732, 200, 2735, 200,
   3259, 2732, 3260, 2732, 212, 2747, 212, 652, 228, 684, 228, 2148, 198, 2150, 2148, 2148, 3895, 3391, 2148, 2148, 210, 2162, 2148, 1823, 228,
   100, 100, 200, 2727, 3259, 200, 200, 3239, 212, 200, 200, 2118, 228, 200, 212, 2747, 212, 2235, 228, 3227, 228, 1179, 212, 2130, 228,
   212, 3252, 204, 3252, 0, 2732, 2148, 3903, 2148, 3903, 200, 2735, 200, 2735, 3259, 212, 2747, 212, 2747, 228, 0, 652, 652, 684, 1172,
   1823, 682, 1823, 1854, 655, 1850, 655, 684, 3227, 676, 3227, 3252, 667, 3236, 667, 684, 1303, 228, 100, 100, 2148, 1819, 2150, 2148, 2148,
   1823, 2154, 2148, 2148, 1807, 2162, 2148, 200, 2118, 228, 200, 2150, 655, 2154, 2150, 2150, 3239, 2162, 2150, 204, 2122, 228, 204, 2154, 667,
   2162, 2154, 212, 2130, 228, 212, 228, 0, 1823, 228, 100, 100, 200, 2118, 200, 228, 204, 2122, 204, 228, 212, 2130, 212, 228, 652,
   3220, 684, 652, 3382, 3250, 3383, 3382, 3252, 3378, 3255, 3252, 3252, 2154, 3260, 3252, 2212, 3236, 2228, 2212, 2148, 3255, 2150, 2148, 2148, 202,
   2154, 2148, 2148, 3367, 2162, 2148, 2150, 647, 2154, 2150, 2150, 3239, 2162, 2150, 2154, 667, 2162, 2154, 3903, 3250, 3903, 3382, 2735, 199, 2735,
   3252, 3252, 204, 3260, 2747, 3236, 2747, 2212, 1172, 3220, 1204, 1172, 3643, 3899, 3647, 3643, 2148, 3903, 3903, 2148, 2863, 3887, 2879, 2863, 1823,
   3871, 1855, 1823, 200, 2735, 2735, 200, 2735, 3239, 2747, 2735, 655, 2703, 687, 655, 204, 2747, 212, 2747, 204, 2122, 228, 204, 667, 2715,
   699, 667, 2732, 2747, 2732, 0, 3252, 2148, 0, 2148, 198, 2150, 2148, 2148, 202, 2154, 2148, 2148, 210, 2162, 2148, 1823, 228, 100, 100,
   3903, 2730, 3902, 3902, 2732, 199, 2735, 2732, 3250, 2724, 3258, 3250, 2732, 3236, 2746, 2732, 652, 2700, 684, 652, 200, 2727, 204, 200, 200,
   3239, 210, 200, 200, 2703, 228, 200, 204, 2747, 210, 204, 204, 3227, 228, 204, 210, 2715, 228, 210, 2148, 0, 3902, 2730, 3902, 3903,
   2148, 198, 2150, 2148, 2148, 202, 2154, 2148, 2148, 210, 2162, 2148, 1823, 228, 100, 100, 2732, 199, 2735, 2732, 3259, 2724, 3259, 2212, 2732,
   3236, 2747, 2732, 652, 2700, 684, 652, 200, 2727, 204, 200, 200, 3239, 2747, 200, 200, 2703, 228, 200, 204, 2747, 2235, 204, 204, 3227,
   228, 204, 228, 2715, 228, 667, 200, 0, 200, 2727, 204, 200, 200, 3239, 212, 200, 200, 2118, 228, 200, 2732, 199, 2735, 2732, 3898,
   2730, 3900, 3898, 3378, 3890, 3386, 3378, 2862, 3886, 2874, 2862, 1818, 3866, 1850, 1818, 2148, 198, 2150, 2148, 3383, 3895, 3391, 3383, 2863, 3887,
   2879, 2863, 1823, 3871, 1855, 1823, 204, 2747, 2235, 204, 204, 2122, 228, 204, 228, 2715, 228, 667, 200, 0, 2732, 199, 2732, 2735, 2148,
   198, 2148, 2150, 200, 2727, 204, 200, 200, 3239, 212, 200, 200, 2118, 228, 200, 3903, 2730, 3903, 2862, 2342, 2854, 2350, 2342, 2862, 3886,
   2747, 2862, 782, 2830, 814, 782, 3383, 3895, 3391, 3383, 2863, 3887, 2879, 2863, 1823, 3871, 1855, 1823, 204, 2747, 212, 204, 204, 2122, 228,
   204, 212, 2130, 228, 212, 204, 0, 204, 2747, 212, 204, 204, 2122, 228, 204, 3259, 2724, 3252, 3252, 3894, 2730, 3896, 3894, 2732, 3890,
   2735, 2732, 2732, 3886, 2740, 2732, 652, 2700, 684, 652, 2148, 202, 2154, 2148, 3643, 3899, 3647, 3643, 2863, 3887, 2879, 2863, 1823, 3871, 1855,
   1823, 200, 2727, 204, 200, 2735, 3239, 2747, 2735, 655, 2703, 687, 655, 667, 2715, 699, 667, 204, 0, 3252, 2724, 3252, 3259, 2148, 202,
   2148, 2154, 200, 2727, 200, 204, 204, 2747, 212, 204, 204, 2122, 228, 204, 3903, 2730, 3903, 2862, 2732, 2858, 2735, 2732, 2732, 3886, 2747,
   2732, 652, 2700, 684, 652, 3643, 3899, 3647, 3643, 2863, 3887, 2879, 2863, 1823, 3871, 1855, 1823, 2735, 3239, 2747, 2735, 655, 2703, 687, 655,
   667, 2715, 699, 667, 212, 228, 0, 652, 2700, 684, 652, 3870, 2730, 3872, 3870, 2732, 3866, 2735, 2732, 3220, 2724, 3228, 3220, 2732, 3220,
   2716, 2716, 1823, 228, 100, 100, 2148, 3899, 2150, 2148, 2148, 3895, 2154, 2148, 2130, 3887, 2130, 2132, 200, 2118, 228, 200, 2150, 2727, 2154,
   2150, 2130, 3239, 2130, 2134, 204, 2122, 228, 204, 2130, 2747, 2130, 2138, 228, 2130, 212, 212, 228, 0, 652, 2700, 652, 684, 1823, 228,
   100, 100, 200, 2118, 200, 228, 204, 2122, 204, 228, 212, 2130, 212, 228, 3903, 2730, 3903, 2862, 2732, 2858, 2735, 2732, 3259, 2724, 3259,
   2212, 2732, 3236, 2747, 2732, 2148, 3899, 2150, 2148, 2148, 3895, 2154, 2148, 2148, 3887, 2879, 2148, 2150, 2727, 2154, 2150, 2150, 3239, 2747, 2150,
   2154, 2747, 2235, 2154, 3903, 2730, 3903, 2862, 2732, 199, 2735, 2732, 3259, 2724, 3259, 2212, 3236, 2747, 2732, 652, 2700, 684, 652, 2148, 198,
   2150, 2148, 2148, 202, 2154, 2148, 2148, 3887, 2879, 2148, 1823, 228, 100, 100, 200, 2727, 204, 200, 200, 3239, 2747, 200, 200, 2118, 228,
   200, 204, 2747, 2235, 204, 204, 2122, 228, 204, 228, 2715, 228, 667, 3236, 212, 3252, 0, 0, 652, 3220, 684, 652, 3902, 3250, 3903,
   3902, 3252, 3898, 3255, 3252, 3252, 3894, 3259, 3252, 3236, 3236, 3252, 2162, 1823, 228, 100, 100, 2148, 3899, 2150, 2148, 2148, 3895, 2154, 2148,
   2148, 3903, 2162, 2148, 200, 2118, 228, 200, 2150, 647, 2154, 2150, 2150, 3255, 2162, 2150, 204, 2122, 228, 204, 2154, 3259, 2162, 2154, 212,
   2130, 228, 212, 228, 0, 684, 1172, 652, 652, 100, 100, 228, 1823, 228, 200, 2118, 200, 228, 204, 2122, 204, 228, 212, 2130, 212,
   1822, 1170, 1823, 1822, 1172, 200, 1175, 1172, 1172, 204, 1179, 1172, 1806, 212, 1172, 212, 70, 198, 70, 72, 74, 202, 74, 76, 82,
   210, 82, 84, 200, 647, 204, 200, 200, 1175, 212, 200, 204, 1179, 212, 204, 228, 2732, 3902, 3250, 3903, 3902, 3252, 200, 3255, 3252,
   3252, 204, 3259, 3252, 3236, 3252, 212, 1172, 3220, 1204, 1172, 2863, 2148, 2148, 2863, 2148, 198, 2150, 2148, 2148, 202, 2154, 2148, 2148, 210,
   2162, 2148, 1823, 228, 100, 100, 2735, 200, 200, 2735, 200, 2727, 204, 200, 200, 3255, 212, 200, 200, 2118, 228, 200, 0, 204, 3259,
   212, 204, 204, 2122, 228, 204, 3252, 204, 3259, 3252, 3902, 3250, 3903, 3902, 3642, 3898, 3646, 3642, 3886, 3886, 3902, 2212, 1822, 3870, 1854,
   1822, 2148, 202, 2154, 2148, 3643, 3899, 3647, 3643, 2148, 3903, 3903, 2148, 1823, 3871, 1855, 1823, 200, 0, 200, 3239, 212, 200, 200, 2118,
   228, 200, 3252, 199, 3255, 3252, 3382, 3250, 3383, 3382, 2342, 3366, 2358, 2342, 1302, 3350, 1334, 1302, 2148, 198, 2150, 2148, 2343, 3367, 2359,
   2343, 1303, 3351, 1335, 1303, 212, 2130, 228, 212, 204, 200, 200, 3239, 212, 200, 200, 2118, 228, 200, 212, 2130, 228, 212, 204, 204,
   0, 3259, 3252, 2212, 3252, 2154, 2148, 202, 2148, 204, 200, 2215, 200, 204, 212, 2235, 204, 204, 228, 2122, 204, 3382, 3250, 3383, 3382,
   3252, 200, 3255, 3252, 3236, 3236, 3252, 212, 1172, 3220, 1204, 1172, 2148, 198, 2150, 2148, 2148, 210, 2162, 2148, 1303, 228, 100, 100, 200,
   3255, 212, 200, 200, 2118, 228, 200, 212, 2130, 228, 212, 204, 3259, 212, 204, 204, 2122, 228, 204, 2747, 212, 2130, 228, 212, 2747,
   2747, 3252, 0, 2732, 3903, 2148, 3903, 2148, 2735, 200, 2735, 200, 3259, 204, 3259, 204, 212, 0, 684, 1823, 228, 100, 100, 200, 2118,
   200, 228, 204, 2122, 204, 228, 2130, 1822, 2148, 1823, 2148, 652, 2150, 655, 2150, 1172, 2154, 1179, 2154, 652, 212, 667, 652, 2148, 198,
   2150, 2148, 2148, 202, 2154, 2148, 2148, 210, 82, 2148, 2150, 647, 2154, 2150, 2150, 1159, 212, 2150, 2154, 667, 212, 2154, 228, 0, 652,
   100, 100, 228, 0, 70, 1819, 70, 100, 74, 1815, 74, 100, 82, 1807, 82, 84, 1822, 650, 1823, 1822, 655, 1818, 655, 684, 1172,
   676, 1179, 1172, 667, 1172, 667, 668, 1175, 647, 1179, 1175, 655, 1159, 667, 655, 74, 667, 155, 155, 228, 200, 2118, 200, 228, 204,
   2122, 204, 212, 1822, 682, 1823, 1822, 655, 200, 655, 200, 1172, 204, 1179, 204, 667, 1172, 667, 668, 70, 198, 70, 72, 74, 202,
   74, 76, 2130, 1807, 2130, 2132, 200, 647, 204, 200, 200, 1159, 2130, 200, 204, 667, 2130, 204, 228, 3902, 2148, 3903, 2148, 2735, 200,
   2735, 200, 3252, 204, 3259, 204, 2747, 3252, 2748, 1172, 228, 1204, 228, 2148, 198, 2150, 2148, 2148, 202, 2154, 2148, 2148, 3887, 2879, 2148,
   1823, 228, 100, 100, 200, 2727, 204, 200, 200, 3239, 2747, 200, 200, 2118, 228, 200, 204, 2747, 2235, 204, 204, 2122, 228, 204, 228,
   2715, 228, 667, 2732, 212, 2732]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem proof3 : cases3.foldlM (fun rem next => certifies goal 6 next rem) data3 = some [] := by
  decide +kernel

def cases4 : List (List Sig) := ((successors inputs 7).drop 63).take 8

set_option maxRecDepth 12000 in
def data4 : List ℕ :=
  [0, 3252, 2148, 3903, 2148, 3903, 200, 3255, 200, 3255, 204, 3259, 204, 3259, 2747, 228, 0, 652, 2700, 684, 652, 1823, 2730, 1823, 1854,
   2732, 1850, 2735, 2732, 1179, 2724, 1179, 1204, 2715, 1188, 2715, 2732, 783, 228, 100, 100, 2148, 1819, 2150, 2148, 2148, 1815, 2154, 2148, 2148,
   1823, 2162, 2148, 200, 2118, 228, 200, 2150, 2727, 2154, 2150, 2150, 1175, 2162, 2150, 204, 2122, 228, 204, 2154, 1179, 2162, 2154, 212, 2130,
   228, 212, 228, 0, 1823, 228, 100, 100, 200, 2118, 200, 228, 204, 2122, 204, 228, 212, 2130, 212, 228, 652, 2700, 684, 652, 2862,
   2730, 2863, 2862, 2732, 2858, 2735, 2732, 2212, 2724, 2220, 2212, 2732, 2162, 2748, 2732, 2148, 2735, 2150, 2148, 2148, 2855, 2154, 2148, 2148, 210,
   2162, 2148, 2150, 2727, 2154, 2150, 2150, 1159, 2162, 2150, 2154, 667, 2162, 2154, 3903, 2730, 3903, 2862, 3255, 199, 3255, 2732, 3259, 2724, 3259,
   2212, 2732, 212, 2748, 652, 2700, 684, 652, 3643, 3899, 3647, 3643, 3383, 3895, 3391, 3383, 2148, 3903, 3903, 2148, 1823, 3871, 1855, 1823, 3255,
   2727, 3259, 3255, 200, 3255, 3255, 200, 1175, 3223, 1207, 1175, 204, 3259, 3259, 204, 1179, 3227, 1211, 1179, 212, 2130, 228, 212, 652, 0,
   684, 0, 228, 2148, 650, 2148, 1822, 2150, 199, 2150, 652, 2154, 204, 2154, 1172, 2162, 212, 2162, 652, 1823, 682, 1823, 1854, 200, 1850,
   200, 684, 204, 676, 204, 1204, 212, 1188, 212, 684, 70, 198, 70, 72, 74, 202, 74, 76, 82, 210, 82, 84, 200, 647, 204,
   200, 200, 1159, 212, 200, 204, 667, 212, 204, 0, 652, 100, 100, 228, 0, 70, 1819, 70, 100, 74, 1815, 74, 100, 82, 1807,
   82, 100, 1822, 650, 1823, 1822, 655, 1818, 655, 684, 1179, 676, 1179, 1204, 667, 1188, 667, 684, 1175, 647, 1179, 1175, 655, 1159, 667,
   655, 74, 667, 155, 155, 228, 200, 2118, 200, 228, 204, 2122, 204, 228, 212, 2130, 212, 1823, 682, 1823, 1854, 655, 200, 655, 200,
   1179, 204, 1179, 204, 667, 212, 667, 212, 70, 198, 70, 72, 74, 202, 74, 76, 82, 210, 82, 84, 200, 647, 204, 200, 200,
   1159, 212, 200, 204, 667, 212, 204, 1823, 1823, 0, 684, 100, 200, 0, 200, 647, 204, 200, 200, 1159, 212, 200, 652, 199, 655,
   652, 1822, 650, 1823, 1822, 1302, 1814, 1310, 1302, 782, 1806, 798, 782, 70, 198, 70, 72, 1303, 1815, 1311, 1303, 783, 1807, 799, 783,
   204, 667, 212, 204, 200, 228, 204, 0, 204, 667, 212, 204, 1172, 204, 1179, 1172, 1822, 650, 1823, 1822, 652, 1818, 655, 652, 652,
   1806, 667, 652, 74, 202, 74, 76, 1563, 1819, 1567, 1563, 783, 1807, 799, 783, 200, 647, 204, 200, 655, 1159, 667, 655, 204, 228,
   212, 0, 652, 212, 667, 652, 1822, 1170, 1823, 1822, 1172, 1818, 1175, 1172, 1172, 1814, 1179, 1172, 82, 210, 82, 84, 1563, 1819, 1567,
   1563, 1303, 1815, 1311, 1303, 200, 1159, 212, 200, 1175, 647, 1179, 1175, 204, 667, 212, 204, 212, 228, 1822, 650, 1823, 1822, 652, 199,
   655, 652, 1172, 204, 1179, 1172, 652, 212, 667, 652, 70, 198, 70, 72, 74, 202, 74, 76, 82, 210, 82, 84, 200, 647, 204,
   200, 200, 1159, 212, 200, 204, 667, 212, 204, 228, 2148, 228, 100, 1823, 228, 100, 2148, 0, 684, 652, 228, 652, 1823, 228, 200,
   70, 200, 228, 204, 74, 204, 228, 212, 82, 212, 1822, 652, 652, 1822, 652, 199, 655, 652, 1172, 204, 1179, 1172, 652, 212, 667,
   652, 70, 200, 70, 200, 74, 204, 74, 204, 82, 212, 82, 212, 200, 647, 204, 200, 200, 1159, 212, 200, 204, 667, 212, 204,
   200, 200, 228, 2118, 2150, 0, 204, 2122, 204, 228, 212, 2130, 212, 228, 652, 228, 684, 652, 1822, 2148, 1823, 1822, 1850, 1822, 1822,
   2118, 1302, 1814, 1310, 1302, 782, 1806, 798, 782, 1563, 228, 100, 100, 2118, 1823, 2118, 2120, 2148, 1815, 2154, 2148, 2148, 1807, 2162, 2148,
   200, 2118, 0, 2118, 667, 2134, 2118, 204, 2118, 200, 200, 647, 2130, 663, 647, 1330, 1302, 1302, 2118, 647, 1302, 647, 648, 1302, 650,
   1303, 1302, 262, 1286, 278, 262, 2118, 1303, 2118, 2120, 1307, 1303, 1303, 1559, 263, 1287, 279, 263, 2126, 2118, 2118, 0, 212, 2118, 200,
   200, 1159, 2122, 1167, 1159, 810, 782, 782, 2118, 1159, 782, 1159, 1160, 782, 1170, 783, 782, 262, 774, 270, 262, 2118, 783, 2118, 2120,
   795, 783, 783, 1551, 263, 775, 271, 263, 2118, 667, 2118, 2126, 2134, 2118, 2154, 667, 2162, 2154, 200, 200, 0, 684, 1823, 228, 100,
   100, 2118, 204, 2122, 204, 228, 212, 2130, 212, 228, 1822, 2148, 1823, 2148, 652, 199, 655, 652, 1172, 2154, 1179, 2154, 652, 2162, 667,
   2162, 2148, 198, 70, 2148, 2148, 202, 2154, 2148, 2148, 210, 2162, 2148, 2154, 647, 2154, 200, 2162, 1159, 2162, 200, 2154, 667, 2162, 2154,
   228, 2150, 228, 204, 204, 228, 2122, 2154, 0, 212, 2130, 212, 228, 1172, 652, 652, 1172, 1822, 650, 1823, 1822, 652, 1818, 655, 652,
   676, 652, 652, 2122, 652, 1806, 667, 652, 1303, 228, 100, 100, 2148, 1819, 2150, 2148, 2122, 1823, 2122, 2124, 2148, 1807, 2162, 2148, 200,
   2118, 228, 200, 2122, 655, 2122, 2126, 2150, 1159, 2162, 2150, 204, 2122, 667, 2138, 2122, 204, 204, 0, 1204, 1823, 228, 100, 100, 200,
   2118, 200, 228, 2122, 212, 2130, 212, 228, 1822, 2148, 1823, 2148, 652, 2150, 655, 2150, 1172, 204, 1179, 1172, 652, 2162, 667, 2162, 2148,
   198, 2150, 2148, 2148, 202, 74, 2148, 2148, 210, 2162, 2148, 2150, 647, 204, 2150, 2150, 1159, 2162, 2150, 2162, 667, 2162, 204, 228, 2154,
   228, 212, 212, 228, 2130, 2162, 0, 652, 1172, 684, 652, 1822, 1170, 1823, 1822, 1172, 1818, 1175, 1172, 1172, 1814, 1179, 1172, 1188, 1172,
   1172, 2130, 783, 228, 100, 100, 2148, 1819, 2150, 2148, 2148, 1815, 2154, 2148, 2130, 1823, 2130, 2132, 200, 2118, 228, 200, 2150, 647, 2154,
   2150, 2130, 1175, 2130, 2134, 204, 2122, 228, 204, 2130, 1179, 2130, 2138, 212, 212, 212, 0, 684, 1823, 228, 100, 100, 200, 2118, 200,
   228, 204, 2122, 204, 228, 2130, 1822, 2148, 1823, 2148, 652, 2150, 655, 2150, 1172, 2154, 1179, 2154, 652, 212, 667, 652, 2148, 198, 2150,
   2148, 2148, 202, 2154, 2148, 2148, 210, 82, 2148, 2150, 647, 2154, 2150, 2150, 1159, 212, 2150, 2154, 667, 212, 2154, 228, 2162, 228, 1822,
   1823, 1822, 2148, 2148, 652, 1823, 1823, 652, 2148, 2148, 1822, 652, 655, 652, 2150, 2150, 1822, 655, 655, 1822, 2150, 2150, 652, 1172, 1179,
   1172, 2154, 2154, 652, 1179, 1179, 652, 2154, 2154, 1172, 652, 667, 652, 2162, 2162, 1172, 667, 667, 1172, 2162, 2162, 652, 2148, 2150, 2148,
   198, 200, 1823, 2150, 2150, 1823, 2148, 200, 2148, 2148, 2154, 2148, 202, 204, 1823, 2154, 2154, 1823, 2148, 204, 2148, 2148, 2162, 2148, 210,
   212, 1823, 2162, 2162, 1823, 2148, 212, 2148, 2150, 2154, 2150, 647, 0, 2154, 667, 2162, 2154, 204, 2122, 204, 228, 684, 1303, 228, 1303,
   100, 647, 0, 204, 2118, 200, 200, 647, 2130, 663, 647, 2118, 667, 2134, 2118, 647, 1302, 647, 648, 1330, 1302, 1302, 2118, 1302, 2148,
   1303, 1302, 262, 1286, 278, 262, 1307, 1303, 1303, 1559, 2118, 1303, 2118, 2120, 263, 1287, 279, 263, 647, 228, 667, 2130, 667, 228, 1172,
   2154, 1179, 2154, 1302, 650, 1303, 1302, 647, 1302, 647, 648, 652, 1286, 667, 652, 2148, 202, 2154, 2148, 1307, 1303, 1303, 1559, 263, 1287,
   279, 263, 2150, 647, 0, 2154, 647, 2150, 2150, 647, 2130, 647, 228, 1159, 2122, 1159, 228, 294, 263, 228, 263, 100, 647, 262, 647,
   648, 1159, 262, 1159, 1160, 262, 1170, 263, 262, 2148, 263, 263, 519, 2148, 263, 263, 1031, 663, 647, 655, 2154, 2154, 655, 2150, 0,
   204, 2122, 228, 204, 1172, 2154, 2154, 1179, 2148, 202, 2148, 2154, 647, 2154, 667, 2162, 2154, 684, 1563, 228, 1563, 100, 200, 2118, 200,
   228, 667, 2130, 667, 228, 1562, 650, 1563, 1562, 652, 2150, 1175, 652, 652, 1546, 667, 652, 1563, 198, 2150, 1563, 2148, 667, 539, 539,
   667, 1159, 667, 2150, 2150, 2150, 2162, 2150, 1159, 0, 212, 2130, 212, 228, 1204, 783, 228, 783, 100, 1159, 0, 212, 2118, 200, 200,
   1159, 2122, 1167, 1159, 1159, 782, 1159, 1160, 810, 782, 782, 2118, 782, 2148, 783, 782, 262, 774, 270, 262, 795, 783, 783, 1551, 2118,
   783, 2118, 2120, 263, 775, 271, 263, 2118, 667, 2118, 2126, 1159, 228, 1179, 2122, 1179, 228, 652, 2162, 667, 2162, 782, 1170, 783, 782,
   1159, 782, 1159, 1160, 1172, 774, 1179, 1172, 2148, 210, 2162, 2148, 795, 783, 783, 1551, 263, 775, 271, 263, 2150, 1159, 0, 2154, 647,
   2150, 2150, 1159, 2122, 1159, 228, 647, 2130, 647, 228, 294, 263, 228, 263, 100, 1159, 262, 1159, 1160, 647, 262, 647, 648, 262, 650,
   263, 262, 2148, 263, 263, 1031, 2148, 263, 263, 519, 1167, 1159, 2154, 667, 2162, 2154, 1175, 2162, 2162, 1175, 2150, 0, 212, 2130, 228,
   212, 652, 2162, 2162, 667, 2148, 210, 2148, 2162, 1159, 2154, 667, 2154, 2162, 1204, 1563, 228, 1563, 100, 200, 2118, 200, 228, 1179, 2122,
   1179, 228, 1562, 1170, 1563, 1562, 1172, 2150, 655, 1172, 1172, 1554, 1179, 1172, 1563, 198, 2150, 1563, 2148, 1179, 1051, 1051, 1179, 647, 1179,
   2150, 2150, 2154, 2162, 2154, 667, 667, 1179, 2162, 2162, 1179, 2154, 667, 2154, 652, 0, 2732, 3903, 2148, 3903, 2148, 200, 2150, 200, 2150,
   204, 2154, 204, 2154, 212, 2162, 212, 2162, 228, 3903, 2148, 3903, 2148, 2735, 2150, 2735, 2150, 3259, 2154, 3259, 2154, 2747, 2162, 2747, 2162,
   2700, 0, 228, 2148, 650, 2148, 1822, 2150, 199, 2150, 652, 2154, 204, 2154, 1172, 2162, 212, 2162, 652, 1823, 682, 1823, 1854, 200, 1850,
   200, 684, 204, 676, 204, 1204, 212, 1188, 212, 684, 70, 198, 70, 72, 74, 202, 74, 76, 82, 210, 82, 84, 200, 647, 204,
   200, 200, 1159, 212, 200, 204, 667, 212, 204, 652, 2148, 198, 2150, 2148, 2148, 202, 2154, 2148, 2148, 210, 2162, 2148, 1823, 2148, 2148,
   1823, 2150, 2727, 2154, 2150, 2150, 3239, 2162, 2150, 200, 2150, 2150, 200, 2154, 2747, 2162, 2154, 204, 2154, 2154, 204, 212, 2162, 2162, 212,
   2700, 228, 2732]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem proof4 : cases4.foldlM (fun rem next => certifies goal 6 next rem) data4 = some [] := by
  decide +kernel

def cases5 : List (List Sig) := ((successors inputs 7).drop 71).take 2

set_option maxRecDepth 12000 in
def data5 : List ℕ :=
  [0, 652, 3902, 2730, 3903, 3902, 2732, 200, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 2700, 2732, 228, 1823, 2148, 2148, 1823,
   2148, 198, 2150, 2148, 2148, 202, 2154, 2148, 2148, 210, 2162, 2148, 1823, 228, 100, 100, 655, 200, 200, 655, 200, 2727, 204, 200, 200,
   3239, 212, 200, 200, 2118, 228, 200, 1179, 204, 204, 1179, 204, 2747, 212, 204, 204, 2122, 228, 204, 667, 212, 212, 667, 212, 2130,
   228, 212, 0, 652, 100, 100, 228, 0, 70, 1819, 70, 100, 74, 1815, 74, 100, 82, 1807, 82, 100, 1822, 650, 1823, 1822, 655,
   1818, 655, 684, 1179, 676, 1179, 1204, 667, 1188, 667, 684, 1175, 647, 1179, 1175, 655, 1159, 667, 655, 74, 667, 155, 155, 228, 200,
   2118, 200, 228, 204, 2122, 204, 228, 212, 2130, 212, 1823, 682, 1823, 1854, 655, 200, 655, 200, 1179, 204, 1179, 204, 667, 212, 667,
   212, 70, 198, 70, 72, 74, 202, 74, 76, 82, 210, 82, 84, 200, 647, 204, 200, 200, 1159, 212, 200, 204, 667, 212, 204,
   684]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem proof5 : cases5.foldlM (fun rem next => certifies goal 6 next rem) data5 = some [] := by
  decide +kernel

def cases6 : List (List Sig) := ((successors inputs 7).drop 73).take 1

set_option maxRecDepth 12000 in
def data6 : List ℕ :=
  [0, 652, 0, 1823, 682, 1823, 1854, 200, 1850, 200, 684, 204, 676, 204, 1204, 212, 1188, 212, 684, 228, 2148, 650, 2148, 1822, 2150,
   199, 2150, 652, 2154, 204, 2154, 1172, 2162, 212, 2162, 652, 2148, 198, 2150, 2148, 2148, 202, 2154, 2148, 2148, 210, 2162, 2148, 2150, 647,
   2154, 2150, 2150, 1159, 2162, 2150, 2154, 667, 2162, 2154, 0, 684, 1823, 228, 100, 100, 200, 2118, 200, 228, 204, 2122, 204, 228, 212,
   2130, 212, 228, 1822, 2148, 1823, 2148, 652, 2150, 655, 2150, 1172, 2154, 1179, 2154, 652, 2162, 667, 2162, 2148, 198, 2150, 2148, 2148, 202,
   2154, 2148, 2148, 210, 2162, 2148, 2150, 647, 2154, 2150, 2150, 1159, 2162, 2150, 2154, 667, 2162, 2154, 100, 2148, 0, 652, 0, 70, 1819,
   70, 100, 74, 1815, 74, 100, 82, 1807, 82, 100, 1822, 650, 1823, 1822, 655, 1818, 655, 684, 1179, 676, 1179, 1204, 667, 1188, 667,
   684, 1175, 647, 1179, 1175, 655, 1159, 667, 655, 74, 667, 155, 155, 228, 200, 70, 200, 228, 204, 74, 204, 228, 212, 82, 212,
   1822, 650, 1823, 1822, 655, 200, 655, 200, 1179, 204, 1179, 204, 667, 212, 667, 212, 70, 200, 70, 200, 74, 204, 74, 204, 82,
   212, 82, 212, 200, 647, 204, 200, 200, 1159, 212, 200, 204, 667, 212, 204, 100, 0, 2148, 70, 2150, 70, 2148, 74, 2154, 74,
   2148, 82, 2162, 82, 0, 70, 1819, 70, 100, 74, 1815, 74, 100, 82, 1807, 82, 100, 1822, 650, 1823, 1822, 655, 1818, 655, 684,
   1179, 676, 1179, 1204, 667, 1188, 667, 684, 1175, 647, 1179, 1175, 655, 1159, 667, 655, 74, 667, 155, 155, 650, 100, 70, 655, 70,
   100, 74, 1179, 74, 100, 82, 667, 82, 1823, 682, 1823, 1854, 655, 70, 655, 70, 1179, 74, 1179, 74, 667, 82, 667, 82, 70,
   647, 74, 70, 70, 1159, 82, 70, 74, 667, 82, 74, 228, 228, 2148, 228, 0, 70, 70, 100, 1819, 655, 1823, 70, 70, 1823,
   100, 655, 100, 74, 74, 100, 1815, 1179, 1823, 74, 74, 1823, 100, 1179, 100, 82, 82, 100, 1807, 667, 1823, 82, 82, 1823, 100,
   667, 100, 1822, 1823, 1822, 650, 100, 684, 1823, 1823, 684, 1822, 100, 1822, 655, 655, 684, 1818, 70, 1822, 655, 655, 1822, 684, 70,
   684, 1179, 1179, 1204, 676, 74, 684, 1179, 1179, 684, 1204, 74, 1204, 667, 667, 684, 1188, 82, 1204, 667, 667, 1204, 684, 82, 684,
   1175, 1179, 1175, 647, 0, 74, 667, 155, 155, 74, 1303, 74, 100, 1307, 1303, 1303, 1559, 263, 1287, 279, 263, 1179, 676, 1179, 1204,
   1302, 650, 1303, 1302, 647, 1302, 647, 680, 667, 1286, 667, 684, 1175, 647, 0, 74, 647, 135, 135, 82, 263, 263, 519, 74, 263,
   263, 1031, 647, 262, 647, 680, 1159, 262, 1159, 1192, 262, 1170, 263, 262, 663, 647, 655, 1179, 1179, 655, 1175, 0, 74, 1179, 100,
   74, 1179, 676, 1204, 1179, 647, 74, 667, 155, 155, 1563, 1175, 70, 1563, 82, 667, 539, 539, 1562, 650, 1563, 1562, 684, 1298, 1175,
   684, 667, 1546, 667, 684, 667, 1159, 667, 135, 1175, 655, 667, 655, 1159, 0, 82, 783, 82, 100, 795, 783, 783, 1551, 263, 775,
   271, 263, 667, 1188, 667, 684, 782, 1170, 783, 782, 1159, 782, 1159, 1192, 1179, 774, 1179, 1204, 655, 1159, 0, 74, 647, 135, 135,
   74, 263, 263, 1031, 82, 263, 263, 519, 1159, 262, 1159, 1192, 647, 262, 647, 680, 262, 650, 263, 262, 1167, 1159, 74, 667, 155,
   155, 1175, 667, 667, 1175, 655, 0, 82, 667, 100, 82, 667, 1188, 684, 667, 1159, 74, 667, 155, 155, 1563, 655, 70, 1563, 74,
   1179, 1051, 1051, 1562, 1170, 1563, 1562, 1204, 778, 655, 1204, 1179, 1554, 1179, 1204, 1179, 647, 1179, 135, 655, 74, 82, 74, 667, 667,
   1179, 155, 82, 1179, 155, 667, 74, 0, 70, 1819, 70, 2148, 74, 1815, 74, 2148, 82, 1807, 82, 2148, 100, 1822, 655, 70, 655,
   70, 1179, 74, 1179, 74, 667, 82, 667, 82, 1823, 682, 1823, 1854, 655, 70, 655, 684, 1179, 676, 1179, 1204, 667, 1188, 667, 684,
   1175, 647, 1179, 1175, 655, 1159, 667, 655, 74, 667, 155, 155, 0, 100, 200, 655, 200, 228, 204, 1179, 204, 228, 212, 667, 212,
   228, 652, 652, 684, 228, 1822, 684, 684, 1822, 655, 200, 655, 684, 1179, 676, 1179, 1204, 667, 1188, 667, 684, 70, 655, 70, 655,
   74, 1179, 74, 1179, 82, 667, 82, 667, 1175, 647, 1179, 1175, 655, 1159, 667, 655, 204, 667, 155, 155, 228, 2150, 228, 200, 200,
   0, 228, 204, 2122, 204, 228, 212, 2130, 212, 684, 228, 652, 652, 1822, 682, 1823, 1822, 199, 199, 1822, 200, 1302, 204, 1310, 204,
   782, 212, 798, 212, 100, 100, 1823, 228, 70, 198, 70, 72, 74, 202, 74, 76, 82, 210, 82, 84, 2118, 200, 0, 200, 667,
   212, 200, 228, 200, 2118, 200, 647, 212, 663, 647, 199, 199, 1302, 200, 647, 1302, 647, 648, 1302, 682, 1303, 1302, 262, 1286, 278,
   262, 70, 198, 70, 72, 1307, 1303, 1303, 1559, 263, 1287, 279, 263, 204, 200, 200, 0, 228, 200, 2118, 200, 1159, 204, 1167, 1159,
   199, 199, 782, 200, 1159, 782, 1159, 1160, 782, 1202, 783, 782, 262, 774, 270, 262, 70, 198, 70, 72, 795, 783, 783, 1551, 263,
   775, 271, 263, 200, 667, 200, 204, 212, 200, 204, 667, 212, 204, 2118, 2150, 0, 652, 100, 100, 228, 0, 70, 1819, 70, 72,
   74, 1815, 74, 100, 82, 1807, 82, 100, 1822, 650, 1823, 1822, 655, 1818, 655, 656, 1179, 676, 1179, 1204, 667, 1188, 667, 684, 1175,
   647, 1179, 1175, 655, 1159, 667, 655, 74, 667, 155, 155, 200, 228, 204, 2122, 204, 228, 212, 2130, 212, 1822, 682, 1823, 1822, 655,
   1822, 655, 656, 1179, 204, 1179, 204, 667, 212, 667, 212, 2118, 1819, 2118, 2120, 74, 202, 74, 76, 82, 210, 82, 84, 204, 647,
   204, 2118, 212, 1159, 212, 2118, 204, 667, 212, 204, 200, 200, 228, 228, 2154, 228, 204, 204, 0, 228, 212, 2130, 212, 1204, 652,
   652, 1172, 1822, 650, 1823, 1822, 652, 200, 655, 652, 1814, 204, 652, 204, 652, 212, 667, 652, 100, 100, 1823, 228, 70, 198, 70,
   72, 74, 202, 74, 76, 82, 210, 82, 84, 228, 200, 200, 2118, 200, 655, 204, 200, 200, 1159, 212, 200, 2122, 204, 667, 212,
   204, 2122, 2154, 0, 1172, 100, 100, 228, 0, 70, 1819, 70, 100, 74, 1815, 74, 76, 82, 1807, 82, 100, 1822, 650, 1823, 1822,
   652, 1818, 655, 652, 1179, 652, 1179, 1180, 652, 1188, 667, 652, 1175, 647, 1179, 1175, 655, 1159, 667, 655, 74, 667, 155, 155, 228,
   200, 2118, 200, 204, 228, 212, 2130, 212, 1822, 650, 1823, 1822, 652, 200, 655, 200, 1179, 652, 1179, 1180, 652, 212, 667, 212, 70,
   198, 70, 72, 2122, 1815, 2122, 2124, 82, 210, 82, 84, 200, 647, 2122, 200, 200, 1159, 212, 200, 212, 667, 212, 2122, 204, 204,
   228, 228, 2162, 228, 212, 212, 0, 684, 1172, 652, 652, 1822, 1170, 1823, 1822, 1172, 200, 1175, 1172, 1172, 204, 1179, 1172, 1806, 212,
   1172, 212, 100, 100, 1823, 228, 70, 198, 70, 72, 74, 202, 74, 76, 82, 210, 82, 84, 228, 200, 200, 2118, 200, 647, 204,
   200, 200, 1175, 212, 200, 228, 204, 204, 2122, 204, 1179, 212, 204, 2130, 2130, 2162, 0, 652, 100, 100, 228, 0, 70, 1819, 70,
   100, 74, 1815, 74, 100, 82, 1807, 82, 84, 1822, 650, 1823, 1822, 655, 1818, 655, 684, 1172, 676, 1179, 1172, 667, 1172, 667, 668,
   1175, 647, 1179, 1175, 655, 1159, 667, 655, 74, 667, 155, 155, 228, 200, 2118, 200, 228, 204, 2122, 204, 212, 1822, 682, 1823, 1822,
   655, 200, 655, 200, 1172, 204, 1179, 204, 667, 1172, 667, 668, 70, 198, 70, 72, 74, 202, 74, 76, 2130, 1807, 2130, 2132, 200,
   647, 204, 200, 200, 1159, 2130, 200, 204, 667, 2130, 204, 212, 212, 228, 1823, 1823, 1854, 682, 2148, 684, 1823, 1823, 684, 1854, 2148,
   1854, 655, 655, 684, 200, 200, 1854, 655, 655, 1854, 200, 200, 684, 1179, 1179, 1204, 204, 204, 684, 1179, 1179, 684, 204, 204, 1204,
   667, 667, 684, 212, 212, 1204, 667, 667, 1204, 212, 212, 684, 70, 70, 2148, 198, 200, 1823, 70, 70, 1823, 72, 200, 2148, 74,
   74, 2148, 202, 204, 1823, 74, 74, 1823, 76, 204, 2148, 82, 82, 2148, 210, 212, 1823, 82, 82, 1823, 84, 212, 2148, 200, 204,
   200, 647, 0, 204, 667, 212, 204, 228, 204, 2122, 204, 652, 1303, 100, 1303, 0, 74, 1303, 74, 100, 1307, 1303, 1303, 1559, 263,
   1287, 279, 263, 74, 667, 155, 155, 1302, 650, 1303, 1302, 1179, 676, 1179, 1204, 647, 1302, 647, 680, 667, 1188, 667, 684, 1175, 647,
   0, 82, 263, 263, 519, 74, 263, 263, 1031, 74, 647, 135, 135, 647, 1188, 647, 680, 262, 1170, 263, 262, 1159, 262, 1159, 1192,
   663, 647, 647, 0, 228, 200, 2118, 200, 647, 212, 663, 647, 200, 667, 212, 200, 647, 1302, 647, 648, 199, 199, 1302, 200, 1302,
   682, 1303, 1302, 262, 1286, 278, 262, 1307, 1303, 1303, 1559, 70, 198, 70, 72, 263, 1287, 279, 263, 647, 228, 667, 212, 667, 212,
   1179, 204, 1179, 204, 1303, 682, 1303, 1334, 647, 1334, 647, 680, 667, 1318, 667, 684, 74, 202, 74, 76, 1307, 1303, 1303, 1559, 263,
   1287, 279, 263, 200, 647, 0, 204, 647, 200, 200, 647, 212, 647, 212, 1159, 204, 1159, 204, 262, 263, 100, 263, 0, 82, 263,
   263, 519, 74, 263, 263, 1031, 74, 647, 135, 135, 262, 1170, 263, 262, 647, 1188, 647, 680, 1159, 676, 1159, 1192, 647, 294, 647,
   680, 1159, 294, 1159, 1192, 263, 1202, 263, 294, 82, 263, 263, 519, 74, 263, 263, 1031, 663, 647, 655, 204, 204, 655, 200, 0,
   1179, 204, 204, 1179, 74, 202, 76, 74, 647, 204, 667, 212, 204, 228, 204, 2122, 204, 652, 1563, 100, 1563, 0, 1563, 1175, 70,
   1563, 82, 667, 539, 539, 74, 1179, 100, 74, 1179, 676, 1204, 1179, 647, 74, 667, 155, 155, 1562, 650, 1563, 1562, 684, 1298, 1175,
   684, 667, 1188, 667, 684, 667, 1159, 667, 135, 228, 200, 2118, 200, 667, 212, 667, 212, 1563, 682, 1563, 1594, 684, 200, 1175, 684,
   667, 1578, 667, 684, 1563, 198, 70, 1563, 82, 667, 539, 539, 667, 1159, 667, 200, 200, 200, 212, 200, 1159, 0, 228, 212, 2130,
   212, 1172, 783, 100, 783, 0, 82, 783, 82, 100, 795, 783, 783, 1551, 263, 775, 271, 263, 782, 1170, 783, 782, 667, 1188, 667,
   684, 1159, 782, 1159, 1192, 1179, 676, 1179, 1204, 655, 1159, 0, 74, 647, 135, 135, 74, 263, 263, 1031, 82, 263, 263, 519, 1159,
   676, 1159, 1192, 262, 650, 263, 262, 647, 262, 647, 680, 1167, 1159, 74, 667, 155, 155, 1159, 0, 228, 200, 2118, 200, 1159, 204,
   1167, 1159, 1159, 782, 1159, 1160, 199, 199, 782, 200, 782, 1202, 783, 782, 262, 774, 270, 262, 795, 783, 783, 1551, 70, 198, 70,
   72, 263, 775, 271, 263, 200, 667, 200, 204, 1159, 228, 1179, 204, 1179, 204, 667, 212, 667, 212, 783, 1202, 783, 814, 1159, 814,
   1159, 1192, 1179, 806, 1179, 1204, 82, 210, 82, 84, 795, 783, 783, 1551, 263, 775, 271, 263, 200, 1159, 0, 204, 647, 200, 200,
   1159, 204, 1159, 204, 647, 212, 647, 212, 262, 263, 100, 263, 0, 74, 263, 263, 1031, 82, 263, 263, 519, 74, 647, 135, 135,
   262, 650, 263, 262, 1159, 676, 1159, 1192, 647, 1188, 647, 680, 1159, 294, 1159, 1192, 647, 294, 647, 680, 263, 682, 263, 294, 74,
   263, 263, 1031, 82, 263, 263, 519, 1167, 1159, 204, 667, 212, 204, 1175, 212, 212, 1175, 200, 0, 667, 212, 212, 667, 82, 210,
   84, 82, 1159, 204, 667, 204, 212, 228, 212, 2130, 212, 1172, 1563, 100, 1563, 0, 1563, 655, 70, 1563, 74, 1179, 1051, 1051, 82,
   667, 100, 82, 667, 1188, 684, 667, 1159, 74, 667, 155, 155, 1562, 1170, 1563, 1562, 1204, 778, 655, 1204, 1179, 676, 1179, 1204, 1179,
   647, 1179, 135, 228, 200, 2118, 200, 1179, 204, 1179, 204, 1563, 1202, 1563, 1594, 1204, 200, 655, 1204, 1179, 1586, 1179, 1204, 1563, 198,
   70, 1563, 74, 1179, 1051, 1051, 1179, 647, 1179, 200, 200, 204, 212, 204, 667, 667, 1179, 212, 212, 1179, 204, 667, 204]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem proof6 : cases6.foldlM (fun rem next => certifies goal 6 next rem) data6 = some [] := by
  decide +kernel

def cases7 : List (List Sig) := ((successors inputs 7).drop 74).take 17

set_option maxRecDepth 12000 in
def data7 : List ℕ :=
  [2732, 0, 652, 2148, 0, 2148, 70, 2150, 2148, 2148, 74, 2154, 2148, 2148, 82, 2162, 2148, 1823, 100, 2148, 100, 3902, 2730, 3903, 3902,
   2732, 70, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 650, 2698, 684, 650, 70, 2727, 74, 70, 70, 3239, 82, 70, 70,
   2703, 100, 70, 74, 2747, 82, 74, 74, 3227, 100, 74, 82, 2715, 100, 82, 2148, 0, 2148, 3899, 2150, 2148, 2148, 3895, 2154, 2148,
   2148, 3887, 2162, 2148, 1823, 2148, 100, 100, 3902, 2730, 3903, 3902, 2732, 3898, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 1822,
   2732, 684, 684, 3255, 2727, 3259, 3255, 2735, 3239, 2747, 2735, 655, 2703, 687, 655, 2154, 2747, 2235, 2235, 1179, 3227, 1211, 1179, 667, 2715,
   699, 667, 2150, 200, 2150, 200, 2154, 204, 2154, 204, 2162, 212, 2162, 212, 228, 3902, 2730, 3903, 3902, 2732, 200, 2735, 200, 3252, 204,
   3259, 204, 2732, 212, 2747, 212, 0, 1823, 682, 1823, 1854, 200, 1850, 200, 684, 204, 676, 204, 1204, 212, 1188, 212, 684, 228, 2148,
   650, 2148, 1822, 2150, 199, 2150, 652, 2154, 204, 2154, 1172, 2162, 212, 2162, 652, 2148, 198, 2150, 2148, 2148, 202, 2154, 2148, 2148, 210,
   2162, 2148, 2150, 647, 2154, 2150, 2150, 1159, 2162, 2150, 2154, 667, 2162, 2154, 2732, 684, 70, 198, 70, 72, 74, 202, 74, 76, 82,
   210, 82, 84, 1823, 2148, 2148, 1823, 200, 2727, 204, 200, 200, 3239, 212, 200, 200, 2150, 2150, 200, 204, 2747, 212, 204, 204, 2154,
   2154, 204, 212, 2162, 2162, 212, 652, 228, 652, 0, 2732, 2148, 3903, 2148, 3903, 200, 2735, 200, 2735, 204, 3259, 204, 3259, 212, 2747,
   212, 2747, 0, 684, 1823, 228, 100, 100, 200, 2118, 200, 228, 204, 2122, 204, 228, 212, 2130, 212, 228, 1822, 2148, 1823, 2148, 652,
   2150, 655, 2150, 1172, 2154, 1179, 2154, 652, 2162, 667, 2162, 2148, 198, 2150, 2148, 2148, 202, 2154, 2148, 2148, 210, 2162, 2148, 2150, 647,
   2154, 2150, 2150, 1159, 2162, 2150, 2154, 667, 2162, 2154, 3903, 650, 3903, 1822, 2735, 199, 2735, 652, 3259, 204, 3259, 1172, 2747, 212, 2747,
   652, 652, 228, 684, 3643, 3899, 3647, 3643, 3383, 3895, 3391, 3383, 2863, 3887, 2879, 2863, 1823, 3903, 3903, 100, 3255, 2727, 3259, 3255, 2735,
   3239, 2747, 2735, 200, 2735, 2735, 200, 204, 2747, 2235, 2235, 204, 3259, 3259, 204, 212, 2747, 2747, 212, 2148, 2150, 2148, 0, 3903, 200,
   204, 0, 204, 2747, 212, 204, 204, 2122, 228, 204, 3252, 2724, 3259, 3252, 3895, 2730, 3895, 3896, 2727, 3898, 2727, 2728, 2732, 3886, 2747,
   2732, 652, 2700, 684, 652, 2148, 202, 2154, 2148, 3643, 3895, 3639, 3639, 2855, 3879, 2871, 2855, 1815, 3863, 1847, 1815, 204, 2727, 200, 200,
   2727, 0, 647, 2695, 679, 647, 204, 2727, 200, 200, 1159, 3207, 1191, 1159, 2727, 2858, 2727, 2728, 3239, 2854, 3239, 3240, 2855, 3238, 2855,
   2856, 782, 2830, 814, 782, 2148, 2727, 2599, 2599, 2148, 2855, 2343, 2343, 775, 2823, 807, 775, 2743, 2727, 647, 2695, 679, 647, 667, 2715,
   699, 667, 204, 0, 3252, 2724, 3252, 3259, 2148, 202, 2148, 2154, 200, 2727, 200, 204, 204, 2747, 212, 204, 204, 2122, 228, 204, 3902,
   2730, 3643, 3902, 2732, 3898, 3646, 2732, 2732, 3886, 2747, 2732, 652, 2700, 684, 652, 3643, 3899, 2150, 3643, 2148, 2747, 2619, 2619, 1563, 3611,
   1595, 1563, 2747, 3239, 2747, 200, 200, 2118, 228, 200, 667, 2715, 699, 667, 212, 0, 212, 2130, 228, 212, 2732, 3236, 2747, 2732, 3887,
   3250, 3887, 3888, 3239, 3898, 3239, 3240, 3252, 3894, 3259, 3252, 1172, 3220, 1204, 1172, 2148, 210, 2162, 2148, 3643, 3887, 3631, 3631, 3367, 3879,
   3375, 3367, 1807, 3855, 1839, 1807, 212, 3239, 200, 200, 3239, 0, 204, 2727, 200, 200, 1159, 3207, 1191, 1159, 647, 2695, 679, 647, 3239,
   3378, 3239, 3240, 2727, 3366, 2727, 2728, 3367, 2726, 3367, 3368, 1302, 3350, 1334, 1302, 2148, 3239, 3111, 3111, 2148, 2727, 2343, 2343, 1287, 3335,
   1319, 1287, 3247, 3239, 1159, 3207, 1191, 1159, 204, 2747, 212, 204, 1179, 3227, 1211, 1179, 212, 0, 2732, 3236, 2732, 2747, 2148, 210, 2148,
   2162, 200, 3239, 200, 212, 204, 2747, 204, 212, 212, 2130, 228, 212, 3902, 3250, 3643, 3902, 3252, 3898, 3646, 3252, 3252, 3894, 3259, 3252,
   1172, 3220, 1204, 1172, 3643, 3899, 2150, 3643, 2148, 3259, 3131, 3131, 1563, 3611, 1595, 1563, 3259, 2727, 3259, 200, 200, 2118, 228, 200, 1179,
   3227, 1211, 1179, 228, 0, 652, 2700, 684, 652, 3871, 2730, 3871, 3872, 2703, 3898, 2703, 2704, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732,
   1563, 228, 100, 100, 2148, 3871, 2120, 2120, 2148, 3863, 2154, 2148, 2148, 3855, 2162, 2148, 228, 2118, 200, 200, 2150, 2695, 2154, 2150, 2150,
   3207, 2162, 2150, 204, 2122, 228, 204, 2154, 2747, 2162, 2154, 212, 2130, 228, 212, 228, 0, 652, 2700, 652, 684, 1823, 228, 100, 100,
   200, 2118, 200, 228, 204, 2122, 204, 228, 212, 2130, 212, 228, 3902, 2730, 3643, 3902, 2732, 3898, 3646, 2732, 3252, 2724, 3259, 3252, 2732,
   3236, 2747, 2732, 2148, 3899, 2150, 2148, 2148, 3259, 2154, 2148, 2148, 2747, 2162, 2148, 2150, 647, 2154, 2150, 2150, 1159, 2162, 2150, 2154, 2747,
   2162, 2154, 2732, 0, 2732, 199, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 652, 2700, 684, 652, 3902, 2730, 3902, 3903, 2148,
   198, 2150, 2148, 2148, 202, 2154, 2148, 2148, 210, 2162, 2148, 1563, 228, 100, 100, 199, 0, 199, 2747, 212, 199, 199, 2118, 228, 199,
   3252, 2724, 3255, 3252, 2727, 3366, 2743, 2727, 647, 2695, 679, 647, 2148, 198, 2150, 2148, 3382, 2726, 3382, 3383, 2148, 2747, 2363, 2363, 1307,
   3355, 1339, 1307, 667, 2715, 699, 667, 204, 199, 199, 0, 199, 2118, 228, 199, 2732, 3236, 2735, 2732, 3239, 2854, 3247, 3239, 1159, 3207,
   1191, 1159, 2148, 198, 2150, 2148, 2862, 3238, 2862, 2863, 2148, 2875, 2363, 2363, 795, 2843, 827, 795, 199, 2747, 199, 204, 1179, 3227, 1211,
   1179, 212, 199, 199, 2118, 228, 199, 204, 2747, 212, 204, 204, 2122, 228, 204, 212, 2130, 228, 212, 0, 3902, 2730, 3903, 3902, 2732,
   199, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 652, 2700, 684, 652, 2148, 198, 2150, 2148, 2148, 202, 2154, 2148, 2148, 210,
   2162, 2148, 1823, 228, 100, 100, 204, 2727, 204, 2150, 212, 3239, 212, 2150, 228, 2118, 228, 70, 204, 2747, 212, 204, 204, 2122, 228,
   204, 212, 2130, 228, 212, 2732, 3902, 2730, 3643, 3902, 2732, 3898, 3646, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 652, 2700, 684,
   652, 198, 2150, 2148, 2148, 202, 2154, 2148, 2148, 210, 2162, 2148, 1563, 228, 100, 100, 204, 0, 204, 2747, 212, 204, 204, 2118, 228,
   204, 200, 3383, 2727, 0, 647, 2695, 679, 647, 204, 2727, 200, 200, 1159, 3207, 1191, 1159, 2727, 3366, 2727, 2728, 3239, 3378, 3239, 3240,
   3367, 3250, 3367, 3368, 1302, 3350, 1334, 1302, 2148, 2727, 2343, 2343, 2148, 3239, 3111, 3111, 1287, 3335, 1319, 1287, 2743, 2727, 647, 2695, 679,
   647, 3252, 2724, 3259, 3252, 2727, 0, 3252, 2724, 3255, 3252, 2727, 3366, 2743, 2727, 647, 2695, 679, 647, 199, 2747, 212, 199, 199, 2118,
   228, 199, 3382, 2726, 3382, 3383, 2148, 198, 2150, 2148, 2148, 210, 2162, 2148, 1307, 228, 100, 100, 212, 2130, 228, 212, 2727, 2728, 3382,
   2726, 3387, 3382, 2732, 3366, 2747, 2732, 652, 2700, 684, 652, 2148, 198, 2150, 2148, 2148, 2747, 2363, 2363, 1307, 3355, 1339, 1307, 667, 2715,
   699, 667, 204, 2150, 212, 0, 212, 2118, 228, 212, 200, 2863, 3239, 0, 204, 2727, 200, 200, 1159, 3207, 1191, 1159, 647, 2695, 679,
   647, 3239, 2854, 3239, 3240, 2727, 2858, 2727, 2728, 2855, 2730, 2855, 2856, 782, 2830, 814, 782, 2148, 2855, 2343, 2343, 2148, 2727, 2599, 2599,
   775, 2823, 807, 775, 3247, 3239, 1159, 3207, 1191, 1159, 2732, 3236, 2747, 2732, 3239, 0, 2732, 3236, 2735, 2732, 3239, 2854, 3247, 3239, 1159,
   3207, 1191, 1159, 199, 2118, 228, 199, 2862, 3238, 2862, 2863, 2148, 198, 2150, 2148, 2148, 202, 2154, 2148, 795, 228, 100, 100, 199, 2747,
   199, 204, 204, 2122, 228, 204, 3239, 3240, 2862, 3238, 2875, 2862, 3252, 2854, 3259, 3252, 1172, 3220, 1204, 1172, 2148, 198, 2150, 2148, 2148,
   2875, 2363, 2363, 795, 2843, 827, 795, 204, 2747, 212, 204, 1179, 3227, 1211, 1179, 212, 2150, 228, 2118, 228, 70, 204, 2747, 212, 204,
   204, 2122, 228, 204, 212, 2130, 228, 212, 198, 200, 3903, 0, 2154, 204, 2154, 204, 2162, 212, 2162, 212, 0, 204, 3227, 204, 228,
   212, 2715, 212, 228, 652, 2700, 684, 652, 3902, 2732, 3903, 3902, 2732, 3902, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 1823,
   228, 100, 100, 3899, 3899, 3903, 2735, 3383, 3895, 3391, 3383, 2863, 3887, 2879, 2863, 200, 2703, 228, 200, 3255, 2727, 3259, 3255, 2735, 3239,
   2747, 2735, 204, 2747, 2235, 2235, 228, 0, 684, 652, 2700, 652, 100, 228, 100, 1823, 228, 200, 70, 200, 228, 204, 74, 204, 228,
   212, 82, 212, 1822, 652, 1823, 1822, 652, 199, 655, 652, 1172, 204, 1179, 1172, 652, 212, 667, 652, 198, 198, 1823, 200, 1303, 204,
   1311, 204, 783, 212, 799, 212, 200, 647, 204, 200, 200, 1159, 212, 200, 204, 667, 212, 204, 228, 3642, 2732, 2732, 3642, 3902, 2732,
   3903, 3902, 2732, 199, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 652, 2700, 684, 652, 2148, 198, 3903, 200, 3383, 204, 3391,
   204, 2863, 212, 2879, 212, 1823, 228, 1855, 228, 2150, 200, 2727, 204, 200, 200, 3239, 212, 200, 200, 2703, 228, 200, 204, 2747, 212,
   204, 204, 3227, 228, 204, 212, 2715, 228, 212, 2150, 2150, 3903]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem proof7 : cases7.foldlM (fun rem next => certifies goal 6 next rem) data7 = some [] := by
  decide +kernel

def cases8 : List (List Sig) := ((successors inputs 7).drop 91).take 20

set_option maxRecDepth 12000 in
def data8 : List ℕ :=
  [0, 3902, 2732, 3902, 2732, 2148, 200, 2154, 204, 2154, 204, 2162, 212, 2162, 212, 0, 652, 2700, 652, 684, 100, 2703, 204, 3227, 204,
   228, 212, 2715, 212, 228, 1822, 2732, 2732, 1822, 2732, 199, 655, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 70, 198, 70, 72,
   74, 3259, 74, 3259, 82, 2747, 82, 2747, 3259, 647, 3259, 200, 2747, 1159, 2747, 200, 204, 2747, 2235, 2235, 228, 0, 684, 652, 2700,
   652, 1563, 200, 228, 204, 74, 204, 228, 212, 82, 212, 1822, 652, 652, 1822, 652, 1818, 2703, 652, 1172, 204, 1179, 1172, 652, 212,
   667, 652, 70, 1823, 70, 72, 74, 204, 74, 204, 82, 212, 82, 212, 204, 2695, 204, 70, 212, 3207, 212, 70, 204, 667, 212,
   204, 228, 3902, 2732, 2732, 3902, 2732, 3898, 3646, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 652, 2700, 684, 652, 2150, 3903, 2152,
   2154, 204, 2154, 204, 2162, 212, 2162, 212, 1823, 228, 1855, 228, 204, 0, 204, 2747, 212, 204, 204, 3227, 228, 204, 200, 200, 2150,
   204, 2727, 2728, 3382, 2727, 3387, 2727, 2743, 2162, 2727, 647, 679, 2695, 647, 3252, 2724, 3259, 3252, 3382, 2732, 2732, 3382, 2732, 3366, 2747,
   2732, 652, 2700, 684, 652, 2150, 204, 2150, 204, 2343, 2747, 2359, 2747, 1303, 3351, 1335, 1303, 667, 2715, 699, 667, 204, 2150, 212, 0,
   212, 2715, 228, 212, 200, 200, 2150, 212, 3239, 3240, 2862, 3239, 2875, 3239, 3247, 2154, 3239, 1159, 1191, 3207, 1159, 2732, 3236, 2747, 2732,
   2862, 3252, 3252, 2862, 3252, 2854, 3259, 3252, 1172, 3220, 1204, 1172, 2150, 212, 2150, 212, 2343, 3259, 2351, 3259, 783, 2831, 815, 783, 204,
   2747, 212, 204, 1179, 3227, 1211, 1179, 212, 2150, 228, 2118, 228, 70, 204, 2747, 212, 204, 204, 3227, 228, 204, 212, 2715, 228, 212,
   2148, 200, 2148, 0, 2732, 3902, 2732, 3902, 3903, 2150, 204, 0, 204, 2747, 212, 204, 204, 2122, 228, 204, 3252, 2724, 3259, 3252, 3382,
   2730, 3391, 3382, 2732, 3382, 2735, 2732, 2732, 3366, 2747, 2732, 652, 2700, 684, 652, 2148, 202, 2154, 2148, 3387, 3387, 3391, 3643, 2351, 3375,
   2367, 2351, 1311, 3359, 1343, 1311, 200, 2727, 204, 200, 2735, 3239, 2747, 2735, 655, 2703, 687, 655, 667, 2715, 699, 667, 204, 0, 200,
   2727, 200, 204, 204, 2747, 212, 204, 204, 2122, 228, 204, 3252, 2724, 3259, 3252, 3642, 2730, 3643, 3642, 2732, 199, 2735, 2732, 2732, 3626,
   2747, 2732, 652, 2700, 684, 652, 2148, 202, 2154, 2148, 3643, 2735, 3647, 3643, 2148, 2747, 2619, 2619, 1563, 3611, 1595, 1563, 2735, 3239, 2747,
   2735, 655, 2703, 687, 655, 667, 2715, 699, 667, 212, 0, 212, 2130, 228, 212, 2732, 3236, 2747, 2732, 2862, 3250, 2879, 2862, 3252, 2862,
   3255, 3252, 3252, 2854, 3259, 3252, 1172, 3220, 1204, 1172, 2148, 210, 2162, 2148, 2875, 2875, 2879, 3643, 2359, 2871, 2367, 2359, 799, 2847, 831,
   799, 200, 3239, 212, 200, 3255, 2727, 3259, 3255, 1175, 3223, 1207, 1175, 204, 2747, 212, 204, 1179, 3227, 1211, 1179, 212, 0, 200, 3239,
   200, 212, 204, 2747, 204, 212, 212, 2130, 228, 212, 2732, 3236, 2747, 2732, 3642, 3250, 3643, 3642, 3252, 199, 3255, 3252, 3252, 3634, 3259,
   3252, 1172, 3220, 1204, 1172, 2148, 210, 2162, 2148, 3643, 3255, 3647, 3643, 2148, 3259, 3131, 3131, 1563, 3611, 1595, 1563, 3255, 2727, 3259, 3255,
   1175, 3223, 1207, 1175, 1179, 3227, 1211, 1179, 228, 0, 652, 2700, 684, 652, 1822, 2730, 1855, 1822, 2732, 1822, 2735, 2732, 3252, 2724, 3259,
   3252, 2732, 3236, 2747, 2732, 1823, 228, 100, 100, 2118, 1851, 2118, 2148, 2148, 1847, 2154, 2148, 2148, 1839, 2162, 2148, 200, 2118, 228, 200,
   2118, 2727, 2126, 2118, 2118, 3239, 2134, 2118, 204, 2122, 228, 204, 2154, 2747, 2162, 2154, 212, 2130, 228, 212, 228, 0, 200, 2118, 200,
   228, 204, 2122, 204, 228, 212, 2130, 212, 228, 652, 2700, 684, 652, 3642, 2730, 3643, 3642, 2732, 199, 2735, 2732, 3252, 2724, 3259, 3252,
   2732, 3236, 2747, 2732, 1823, 228, 100, 100, 2148, 2735, 2152, 2148, 2148, 3259, 2154, 2148, 2148, 2747, 2162, 2148, 2154, 2727, 2154, 3255, 2162,
   3239, 2162, 2735, 2154, 2747, 2162, 2154, 3902, 2730, 3643, 3902, 2732, 3902, 3902, 2732, 3382, 3894, 3390, 3382, 2862, 3886, 2878, 2862, 1822, 3870,
   1854, 1822, 2148, 200, 2152, 2148, 202, 2154, 2148, 2148, 210, 2162, 2148, 1563, 228, 100, 100, 200, 2727, 204, 200, 200, 3239, 212, 200,
   200, 2703, 228, 200, 204, 2747, 212, 204, 204, 2122, 228, 204, 212, 2130, 228, 212, 2148, 2154, 2148, 0, 3903, 200, 2735, 200, 2735,
   204, 212, 2747, 212, 2747, 228, 0, 1172, 652, 652, 1172, 3871, 652, 3871, 3872, 652, 3898, 655, 652, 3227, 652, 3227, 3228, 652, 3236,
   667, 652, 1303, 228, 100, 100, 2148, 3867, 2150, 2148, 2148, 3871, 2124, 2124, 2148, 3855, 2162, 2148, 200, 2118, 228, 200, 2150, 655, 2154,
   2150, 2150, 3239, 2162, 2150, 228, 2122, 204, 204, 2154, 667, 2162, 2154, 212, 2130, 228, 212, 228, 0, 652, 3220, 652, 1204, 1823, 228,
   100, 100, 200, 2118, 200, 228, 204, 2122, 204, 228, 212, 2130, 212, 228, 3902, 3250, 3383, 3902, 3252, 3898, 3255, 3252, 3252, 3894, 3390,
   3252, 2212, 3236, 2228, 2212, 2148, 3255, 2150, 2148, 2148, 3895, 2154, 2148, 2148, 3367, 2162, 2148, 2150, 647, 2154, 2150, 2150, 3239, 2162, 2150,
   2154, 667, 2162, 2154, 3252, 2732, 2732, 3252, 3902, 2732, 2732, 3902, 2732, 199, 2735, 2732, 3252, 2732, 2732, 3252, 2732, 3236, 2747, 2732, 652,
   2700, 684, 652, 2148, 2735, 2150, 2735, 202, 2154, 2148, 2148, 2747, 2162, 2747, 1303, 228, 100, 100, 200, 2735, 2735, 200, 2735, 3239, 2747,
   2735, 655, 2703, 687, 655, 212, 2747, 212, 2747, 228, 2122, 228, 74, 667, 2715, 699, 667, 202, 204, 3903, 0, 2162, 212, 2162, 212,
   0, 212, 2715, 212, 228, 652, 2700, 684, 652, 3902, 2730, 3903, 3902, 2732, 3898, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732,
   1823, 228, 100, 100, 3643, 3899, 3647, 3643, 3895, 3895, 3903, 3259, 2863, 3887, 2879, 2863, 200, 2703, 228, 200, 3255, 2727, 3259, 3255, 2735,
   3239, 2747, 2735, 204, 3227, 228, 204, 204, 2747, 2235, 2235, 228, 0, 684, 652, 2700, 652, 100, 228, 100, 1823, 228, 200, 70, 200,
   228, 204, 74, 204, 228, 212, 82, 212, 1822, 650, 1823, 1822, 652, 199, 655, 652, 1172, 204, 1179, 1172, 652, 212, 667, 652, 1563,
   200, 1567, 200, 202, 202, 1823, 204, 783, 212, 799, 212, 200, 647, 204, 200, 200, 1159, 212, 200, 204, 667, 212, 204, 228, 3382,
   2732, 2732, 3382, 3902, 2730, 3903, 3902, 2732, 199, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 652, 2700, 684, 652, 2148, 3643,
   200, 3647, 200, 202, 3903, 204, 2863, 212, 2879, 212, 1823, 228, 1855, 228, 2150, 200, 200, 2150, 200, 2727, 204, 200, 200, 3239, 212,
   200, 200, 2703, 228, 200, 2154, 204, 2747, 212, 204, 204, 3227, 228, 204, 212, 2715, 228, 212, 2154, 2154, 3903, 0, 2732, 3252, 2732,
   3252, 2148, 2150, 200, 2150, 200, 204, 2162, 212, 2162, 212, 0, 652, 3220, 652, 1204, 100, 200, 3223, 200, 228, 3227, 212, 0, 652,
   212, 667, 652, 1822, 1170, 1823, 1822, 1172, 1818, 1175, 1172, 1172, 1814, 1179, 1172, 82, 210, 82, 84, 1563, 1819, 1567, 1563, 1303, 1815,
   1311, 1303, 200, 1159, 212, 200, 1175, 647, 1179, 1175, 204, 667, 212, 204, 212, 228, 1822, 3252, 3252, 1822, 3252, 199, 3255, 3252, 3252,
   204, 1179, 3252, 2212, 3236, 2228, 2212, 70, 3255, 70, 3255, 74, 202, 74, 76, 82, 210, 82, 84, 3255, 647, 204, 3255, 2215, 3239,
   2231, 2215, 204, 667, 212, 204, 228, 0, 652, 1172, 652, 1172, 1303, 228, 200, 70, 200, 204, 228, 212, 82, 212, 1822, 1172, 1172,
   1822, 1172, 199, 1175, 1172, 1172, 652, 3227, 1172, 652, 212, 148, 148, 70, 200, 70, 200, 74, 1823, 74, 76, 82, 212, 82, 212,
   200, 655, 74, 200, 200, 1159, 212, 200, 212, 667, 212, 74, 228, 3902, 3252, 3252, 3902, 3252, 199, 3255, 3252, 3252, 2732, 2732, 3252,
   2212, 3236, 2228, 2212, 1172, 3220, 1204, 1172, 2150, 200, 2150, 200, 2154, 3903, 2156, 2162, 212, 2162, 212, 1823, 228, 1855, 228, 200, 2735,
   2154, 200, 200, 3239, 212, 200, 200, 3223, 228, 200, 212, 2747, 212, 2154, 228, 2122, 228, 74, 212, 2130, 228, 212, 2148, 204, 2148]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem proof8 : cases8.foldlM (fun rem next => certifies goal 6 next rem) data8 = some [] := by
  decide +kernel

def cases9 : List (List Sig) := ((successors inputs 7).drop 111).take 18

set_option maxRecDepth 12000 in
def data9 : List ℕ :=
  [0, 2732, 3902, 2732, 3902, 3903, 200, 0, 200, 2727, 204, 200, 200, 3239, 212, 200, 200, 2118, 228, 200, 2732, 199, 2735, 2732, 3642,
   2732, 3647, 3642, 3382, 3638, 3386, 3382, 2602, 3626, 2618, 2602, 1562, 3610, 1594, 1562, 2148, 198, 2150, 2148, 3383, 3639, 3391, 3383, 2607, 3631,
   2623, 2607, 1567, 3615, 1599, 1567, 204, 2747, 212, 204, 204, 3227, 228, 204, 212, 2130, 228, 212, 200, 0, 2148, 198, 2148, 2150, 200,
   2727, 204, 200, 200, 3239, 212, 200, 200, 2118, 228, 200, 2732, 199, 2735, 2732, 3382, 2730, 3383, 3382, 3382, 2724, 3259, 3382, 2342, 3366,
   2358, 2342, 1302, 3350, 1334, 1302, 3383, 202, 3391, 3383, 2343, 3367, 2359, 2343, 1303, 3351, 1335, 1303, 204, 2747, 212, 204, 204, 2122, 228,
   204, 212, 2130, 228, 212, 2154, 212, 0, 212, 2130, 228, 212, 2732, 3236, 2747, 2732, 2862, 3250, 2879, 2862, 3252, 2858, 3255, 3252, 3252,
   2862, 3259, 3252, 1172, 3220, 1204, 1172, 2148, 210, 2162, 2148, 2619, 2875, 2623, 2619, 2871, 2871, 2879, 3383, 799, 2847, 831, 799, 200, 3239,
   212, 200, 3255, 2727, 3259, 3255, 1175, 3223, 1207, 1175, 204, 2747, 212, 204, 1179, 3227, 1211, 1179, 212, 0, 200, 3239, 200, 212, 204,
   2747, 204, 212, 212, 2130, 228, 212, 2732, 3236, 2747, 2732, 3382, 3250, 3383, 3382, 3252, 3378, 3255, 3252, 3252, 2724, 3259, 3252, 1172, 3220,
   1204, 1172, 2148, 210, 2162, 2148, 2148, 3255, 3127, 3127, 3383, 3259, 3391, 3383, 1303, 3351, 1335, 1303, 3255, 2727, 3259, 3255, 1175, 3223, 1207,
   1175, 1179, 3227, 1211, 1179, 228, 0, 652, 2700, 684, 652, 1822, 2698, 1855, 1822, 2732, 1818, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236,
   2747, 2732, 1823, 228, 100, 100, 2148, 1851, 2150, 2148, 2122, 1847, 2122, 2148, 2148, 1839, 2162, 2148, 200, 2118, 228, 200, 2122, 2727, 2122,
   2126, 2150, 3239, 2162, 2150, 204, 2122, 228, 204, 2122, 2747, 2138, 2122, 212, 2130, 228, 212, 228, 0, 200, 2118, 200, 228, 204, 2122,
   204, 228, 212, 2130, 212, 228, 652, 2700, 684, 652, 3382, 2732, 3383, 3382, 2732, 3378, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747,
   2732, 1823, 228, 100, 100, 2148, 2735, 2150, 2148, 2148, 3259, 2156, 2148, 2148, 3367, 2162, 2148, 2150, 2727, 3259, 2150, 2150, 3239, 2162, 2150,
   2162, 2747, 2162, 2235, 3902, 2732, 3383, 3902, 3642, 3898, 3646, 3642, 3252, 3902, 3902, 3252, 2862, 3886, 2878, 2862, 1822, 3870, 1854, 1822, 2148,
   198, 2150, 2148, 2148, 204, 2156, 2148, 210, 2162, 2148, 1303, 228, 100, 100, 200, 2727, 204, 200, 200, 3239, 212, 200, 200, 2118, 228,
   200, 204, 2747, 212, 204, 204, 3227, 228, 204, 212, 2130, 228, 212, 2148, 2162, 2148, 0, 3903, 200, 3255, 200, 3255, 204, 3259, 204,
   3259, 212, 228, 0, 652, 2700, 684, 652, 3871, 2730, 3871, 3872, 2732, 3898, 2735, 2732, 1172, 2724, 1179, 1172, 2715, 1172, 2715, 2716, 783,
   228, 100, 100, 2148, 3867, 2150, 2148, 2148, 3863, 2154, 2148, 2148, 3871, 2132, 2132, 200, 2118, 228, 200, 2150, 2727, 2154, 2150, 2150, 1175,
   2162, 2150, 204, 2122, 228, 204, 2154, 1179, 2162, 2154, 228, 2130, 212, 212, 228, 0, 652, 2700, 652, 684, 1823, 228, 100, 100, 200,
   2118, 200, 228, 204, 2122, 204, 228, 212, 2130, 212, 228, 3902, 2730, 2863, 3902, 2732, 3898, 2735, 2732, 2212, 2724, 2220, 2212, 2732, 3886,
   2878, 2732, 2148, 2735, 2150, 2148, 2148, 2855, 2154, 2148, 2148, 3887, 2162, 2148, 2150, 2727, 2154, 2150, 2150, 1159, 2162, 2150, 2154, 667, 2162,
   2154, 2732, 3252, 3252, 2732, 3902, 3252, 3252, 3902, 3252, 199, 3255, 3252, 3252, 2724, 3259, 3252, 2732, 3252, 3252, 2732, 1172, 3220, 1204, 1172,
   2148, 3255, 2150, 3255, 2148, 3259, 2154, 3259, 210, 2162, 2148, 783, 228, 100, 100, 3255, 2727, 3259, 3255, 200, 3255, 3255, 200, 1175, 3223,
   1207, 1175, 204, 3259, 3259, 204, 1179, 3227, 1211, 1179, 228, 2130, 228, 82, 210, 212, 3903, 0, 0, 652, 2700, 684, 652, 3902, 2732,
   3903, 3902, 2732, 3898, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 1823, 228, 100, 100, 3643, 3899, 3647, 3643, 3383, 3895, 3391,
   3383, 3887, 3887, 3903, 2747, 200, 2703, 228, 200, 3255, 2727, 3259, 3255, 2735, 3239, 2747, 2735, 204, 3227, 228, 204, 204, 2747, 2235, 2235,
   212, 2715, 228, 212, 228, 0, 684, 652, 2700, 652, 100, 228, 100, 1823, 228, 200, 70, 200, 228, 204, 74, 204, 228, 212, 82,
   212, 1822, 652, 1823, 1822, 652, 199, 655, 652, 1172, 204, 1179, 1172, 652, 212, 667, 652, 1563, 200, 1567, 200, 1303, 204, 1311, 204,
   210, 210, 1823, 212, 200, 647, 204, 200, 200, 1159, 212, 200, 204, 667, 212, 204, 228, 2862, 2732, 2732, 2862, 3902, 2732, 3903, 3902,
   2732, 199, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 652, 2700, 684, 652, 2148, 3643, 200, 3647, 200, 3383, 204, 3391, 204,
   210, 3903, 212, 1823, 228, 1855, 228, 2150, 200, 200, 2150, 200, 2727, 204, 200, 200, 3239, 212, 200, 200, 2703, 228, 200, 2154, 204,
   204, 2154, 204, 2747, 212, 204, 204, 3227, 228, 204, 2162, 212, 2715, 228, 212, 2162, 2162, 3903, 0, 3252, 2732, 3252, 2732, 2148, 2150,
   200, 2150, 200, 2154, 204, 2154, 204, 212, 0, 652, 2700, 652, 684, 100, 200, 2703, 200, 228, 204, 0, 204, 667, 212, 204, 1172,
   204, 1179, 1172, 1822, 650, 1823, 1822, 652, 1818, 655, 652, 652, 1806, 667, 652, 74, 202, 74, 76, 1563, 1819, 1567, 1563, 783, 1807,
   799, 783, 200, 647, 204, 200, 655, 1159, 667, 655, 204, 228, 2715, 1822, 2732, 2732, 1822, 2732, 199, 2735, 2732, 2212, 2724, 2220, 2212,
   2732, 212, 667, 2732, 70, 2735, 70, 2735, 74, 202, 74, 76, 82, 210, 82, 84, 2215, 2727, 2223, 2215, 2735, 1159, 212, 2735, 204,
   667, 212, 204, 228, 0, 684, 652, 2700, 652, 783, 228, 200, 70, 200, 228, 204, 74, 204, 212, 1822, 652, 652, 1822, 652, 199,
   655, 652, 1172, 204, 140, 140, 652, 1172, 2715, 652, 70, 200, 70, 200, 74, 204, 74, 204, 82, 1823, 82, 84, 200, 647, 204,
   200, 200, 1175, 82, 200, 204, 1179, 82, 204, 228, 3902, 2732, 2732, 3902, 2732, 199, 2735, 2732, 2212, 2724, 2220, 2212, 2732, 3252, 3252,
   2732, 652, 2700, 684, 652, 2150, 200, 2150, 200, 2154, 204, 2154, 204, 2162, 3903, 2164, 1823, 228, 1855, 228, 200, 2727, 204, 200, 200,
   3255, 2162, 200, 200, 2703, 228, 200, 204, 3259, 2162, 204, 204, 2122, 228, 204, 228, 2130, 228, 82, 2148, 212, 2148, 0, 2732, 3902,
   2732, 3902, 3903, 200, 0, 200, 2727, 204, 200, 200, 3239, 212, 200, 200, 2118, 228, 200, 2732, 199, 2735, 2732, 3642, 2730, 3647, 3642,
   3122, 3634, 3130, 3122, 2862, 3630, 2874, 2862, 1562, 3610, 1594, 1562, 2148, 198, 2150, 2148, 3127, 3639, 3135, 3127, 2863, 3631, 2879, 2863, 1567,
   3615, 1599, 1567, 204, 2747, 212, 204, 204, 2122, 228, 204, 212, 2715, 228, 212, 200, 0, 2148, 198, 2148, 2150, 200, 2727, 204, 200,
   200, 3239, 212, 200, 200, 2118, 228, 200, 2732, 199, 2735, 2732, 2862, 2730, 2863, 2862, 2342, 2854, 2350, 2342, 2862, 3236, 2747, 2862, 782,
   2830, 814, 782, 2343, 2855, 2351, 2343, 2863, 210, 2879, 2863, 783, 2831, 815, 783, 204, 2747, 212, 204, 204, 2122, 228, 204, 212, 2130,
   228, 212, 204, 0, 204, 2747, 212, 204, 204, 2122, 228, 204, 3252, 2724, 3259, 3252, 3382, 2730, 3391, 3382, 2732, 3378, 2735, 2732, 2732,
   3374, 2747, 2732, 652, 2700, 684, 652, 2148, 202, 2154, 2148, 3131, 3387, 3135, 3131, 2863, 3375, 2879, 2863, 1311, 3359, 1343, 1311, 200, 2727,
   204, 200, 2735, 3239, 2747, 2735, 655, 2703, 687, 655, 667, 2715, 699, 667, 204, 0, 2148, 202, 2148, 2154, 200, 2727, 200, 204, 204,
   2747, 212, 204, 204, 2122, 228, 204, 3252, 2724, 3259, 3252, 2862, 2730, 2863, 2862, 2732, 2858, 2735, 2732, 2732, 3236, 2747, 2732, 652, 2700,
   684, 652, 2148, 2735, 2607, 2607, 2863, 2747, 2879, 2863, 783, 2831, 815, 783, 2735, 3239, 2747, 2735, 655, 2703, 687, 655, 667, 2715, 699,
   667, 2162, 228, 0, 652, 2700, 684, 652, 1822, 2730, 1855, 1822, 2732, 1818, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 1823,
   228, 100, 100, 2148, 1851, 2150, 2148, 2148, 1847, 2154, 2148, 2130, 1839, 2130, 2148, 200, 2118, 228, 200, 2150, 2727, 2154, 2150, 2130, 3239,
   2130, 2134, 204, 2122, 228, 204, 2130, 2747, 2130, 2138, 212, 2130, 228, 212, 228, 0, 200, 2118, 200, 228, 204, 2122, 204, 228, 212,
   2130, 212, 228, 652, 2700, 684, 652, 2862, 2730, 2863, 2862, 2732, 2858, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 1823, 228,
   100, 100, 2148, 2735, 2150, 2148, 2148, 2855, 2154, 2148, 2148, 2747, 2164, 2148, 2150, 2727, 2154, 2150, 2150, 3239, 2747, 2150, 2154, 2747, 2235,
   2154, 3902, 2730, 2863, 3902, 3642, 3898, 3646, 3642, 3382, 3894, 3390, 3382, 2732, 3902, 3902, 2732, 1822, 3870, 1854, 1822, 2148, 198, 2150, 2148,
   2148, 202, 2154, 2148, 2148, 212, 2164, 783, 228, 100, 100, 200, 2727, 204, 200, 200, 3239, 212, 200, 200, 2118, 228, 200, 204, 2747,
   212, 204, 204, 2122, 228, 204, 212, 2715, 228, 212, 1823]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem proof9 : cases9.foldlM (fun rem next => certifies goal 6 next rem) data9 = some [] := by
  decide +kernel

def cases10 : List (List Sig) := ((successors inputs 7).drop 129).take 8

set_option maxRecDepth 12000 in
def data10 : List ℕ :=
  [0, 100, 0, 228, 2732, 650, 2732, 1823, 2735, 198, 2735, 72, 3259, 202, 3259, 76, 2747, 210, 2747, 84, 200, 1851, 200, 100, 204,
   1847, 204, 100, 212, 1839, 212, 100, 652, 2698, 1855, 652, 652, 199, 655, 652, 1172, 204, 1179, 1172, 652, 212, 667, 652, 200, 647,
   204, 200, 200, 1159, 212, 200, 204, 667, 212, 204, 0, 684, 652, 2700, 652, 1823, 228, 200, 70, 200, 228, 204, 74, 204, 228,
   212, 82, 212, 1822, 652, 652, 1822, 652, 199, 655, 652, 1172, 204, 1179, 1172, 652, 212, 667, 652, 70, 200, 70, 200, 74, 204,
   74, 204, 82, 212, 82, 212, 200, 647, 204, 200, 200, 1159, 212, 200, 204, 667, 212, 204, 200, 200, 228, 2703, 2735, 0, 204,
   3227, 204, 228, 212, 2715, 212, 228, 652, 2700, 684, 652, 1822, 2732, 1823, 1822, 2703, 1822, 2703, 2704, 3252, 2724, 3259, 3252, 2732, 3236,
   2747, 2732, 1563, 228, 100, 100, 1851, 1823, 1823, 2703, 1303, 1815, 1311, 1303, 783, 1807, 799, 783, 200, 3223, 2695, 3231, 3223, 2703, 3207,
   2719, 2703, 204, 2747, 2235, 2235, 200, 200, 0, 652, 2700, 652, 684, 100, 2703, 204, 3227, 204, 228, 212, 2715, 212, 228, 1822, 2732,
   2732, 1822, 2732, 199, 655, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 70, 198, 70, 72, 74, 3259, 74, 3259, 82, 2747, 82,
   2747, 3259, 647, 3259, 200, 2747, 1159, 2747, 200, 204, 2747, 2235, 2235, 228, 2735, 228, 204, 204, 228, 3227, 3259, 0, 212, 667, 212,
   228, 1172, 652, 652, 1172, 1822, 650, 1823, 1822, 652, 1818, 655, 652, 3227, 652, 3227, 3228, 652, 3236, 667, 652, 1303, 228, 100, 100,
   1563, 1819, 1567, 1563, 1847, 1823, 1823, 3227, 783, 1807, 799, 783, 200, 655, 228, 200, 3227, 655, 3227, 3231, 655, 3239, 667, 655, 204,
   212, 667, 2203, 667, 204, 204, 0, 652, 3220, 652, 1204, 100, 200, 3223, 200, 228, 3227, 212, 0, 652, 212, 667, 652, 1822, 1170,
   1823, 1822, 1172, 1818, 1175, 1172, 1172, 1814, 1179, 1172, 82, 210, 82, 84, 1563, 1819, 1567, 1563, 1303, 1815, 1311, 1303, 200, 1159, 212,
   200, 1175, 647, 1179, 1175, 204, 667, 212, 204, 212, 228, 1822, 3252, 3252, 1822, 3252, 199, 3255, 3252, 3252, 204, 1179, 3252, 2212, 3236,
   2228, 2212, 70, 3255, 70, 3255, 74, 202, 74, 76, 82, 210, 82, 84, 3255, 647, 204, 3255, 2215, 3239, 2231, 2215, 204, 667, 212,
   204, 228, 3259, 228, 212, 212, 228, 2715, 2747, 0, 652, 2700, 684, 652, 1822, 2732, 1823, 1822, 2732, 1818, 2735, 2732, 1172, 2724, 1179,
   1172, 2715, 1172, 2715, 2716, 783, 228, 100, 100, 1563, 1819, 1567, 1563, 1303, 1815, 1311, 1303, 1839, 1823, 1823, 2715, 200, 2703, 228, 200,
   1175, 2727, 1179, 1175, 2715, 1175, 2715, 2719, 204, 1179, 228, 204, 204, 1179, 1179, 2203, 212, 212, 212, 0, 652, 2700, 652, 684, 100,
   200, 2703, 200, 228, 204, 0, 204, 667, 212, 204, 1172, 204, 1179, 1172, 1822, 650, 1823, 1822, 652, 1818, 655, 652, 652, 1806, 667,
   652, 74, 202, 74, 76, 1563, 1819, 1567, 1563, 783, 1807, 799, 783, 200, 647, 204, 200, 655, 1159, 667, 655, 204, 228, 2715, 1822,
   2732, 2732, 1822, 2732, 199, 2735, 2732, 2212, 2724, 2220, 2212, 2732, 212, 667, 2732, 70, 2735, 70, 2735, 74, 202, 74, 76, 82, 210,
   82, 84, 2215, 2727, 2223, 2215, 2735, 1159, 212, 2735, 204, 667, 212, 204, 228, 2747, 228, 652, 0, 684, 100, 200, 0, 200, 647,
   204, 200, 200, 1159, 212, 200, 652, 199, 655, 652, 1822, 650, 1823, 1822, 1302, 1814, 1310, 1302, 782, 1806, 798, 782, 70, 198, 70,
   72, 1303, 1815, 1311, 1303, 783, 1807, 799, 783, 204, 667, 212, 204, 200, 228, 204, 0, 204, 667, 212, 204, 1172, 204, 1179, 1172,
   1822, 650, 1823, 1822, 652, 1818, 655, 652, 652, 1806, 667, 652, 74, 202, 74, 76, 1563, 1819, 1567, 1563, 783, 1807, 799, 783, 200,
   647, 204, 200, 655, 1159, 667, 655, 204, 228, 212, 0, 652, 212, 667, 652, 1822, 1170, 1823, 1822, 1172, 1818, 1175, 1172, 1172, 1814,
   1179, 1172, 82, 210, 82, 84, 1563, 1819, 1567, 1563, 1303, 1815, 1311, 1303, 200, 1159, 212, 200, 1175, 647, 1179, 1175, 204, 667, 212,
   204, 212, 228, 1822, 650, 1823, 1822, 652, 199, 655, 652, 1172, 204, 1179, 1172, 652, 212, 667, 652, 70, 198, 70, 72, 74, 202,
   74, 76, 82, 210, 82, 84, 200, 647, 204, 200, 200, 1159, 212, 200, 204, 667, 212, 204, 652, 2700, 228, 2732, 684, 0, 652,
   100, 100, 228, 0, 70, 1819, 70, 100, 74, 1815, 74, 100, 82, 1807, 82, 100, 1822, 650, 1823, 1822, 655, 1818, 655, 684, 1179,
   676, 1179, 1204, 667, 1188, 667, 684, 1175, 647, 1179, 1175, 655, 1159, 667, 655, 74, 667, 155, 155, 228, 200, 655, 200, 228, 204,
   1179, 204, 228, 212, 667, 212, 1823, 684, 1823, 1856, 655, 200, 655, 200, 1179, 204, 1179, 204, 667, 212, 667, 212, 70, 198, 70,
   72, 74, 202, 74, 76, 82, 210, 82, 84, 200, 647, 204, 200, 200, 1159, 212, 200, 204, 667, 212, 204, 2732, 652, 228, 652,
   1822, 1823, 1822, 2732, 0, 1563, 2735, 1567, 2735, 1303, 3259, 1311, 3259, 783, 2747, 799, 2747, 1855, 70, 2703, 70, 100, 74, 3227, 74,
   100, 82, 2715, 82, 100, 1822, 650, 2698, 684, 650, 2732, 70, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 3255, 2727, 3259,
   3255, 2735, 3239, 2747, 2735, 74, 2747, 2235, 2235, 2732, 2732, 1823, 2732, 1822, 0, 100, 0, 70, 1819, 70, 100, 74, 1815, 74, 100,
   82, 1807, 82, 100, 1822, 650, 1823, 1822, 655, 1818, 655, 684, 1179, 676, 1179, 1204, 667, 1188, 667, 684, 1175, 647, 1179, 1175, 655,
   1159, 667, 655, 74, 667, 155, 155, 100, 1823, 2732, 70, 2735, 70, 2735, 74, 3259, 74, 3259, 82, 2747, 82, 2747, 655, 2703, 655,
   687, 1179, 3227, 1179, 1211, 667, 2715, 667, 699, 1822, 100, 1856, 1822, 2735, 1818, 2735, 1562, 3259, 1814, 3259, 1302, 2747, 1806, 2747, 782,
   3255, 2727, 3259, 3255, 2735, 3239, 2747, 2735, 74, 2747, 2235, 2235, 1822, 2732, 2735, 2732, 199, 200, 1822, 2735, 2735, 1822, 2732, 200, 2732,
   3252, 3259, 3252, 2724, 204, 2732, 3259, 3259, 2732, 3252, 204, 3252, 2732, 2747, 2732, 3236, 212, 3252, 2747, 2747, 3252, 2732, 212, 2732, 70,
   70, 1563, 2735, 2735, 1823, 70, 70, 1823, 2735, 2735, 1563, 74, 74, 1303, 3259, 3259, 1823, 74, 74, 1823, 3259, 3259, 1303, 82, 82,
   783, 2747, 2747, 1823, 82, 82, 1823, 2747, 2747, 783, 3255, 3259, 3255, 2727, 0, 204, 2747, 2235, 2235, 204, 3227, 204, 228, 1335, 647,
   2695, 647, 679, 667, 2715, 667, 699, 3252, 2724, 3259, 3252, 652, 2700, 684, 652, 1302, 2732, 2732, 1302, 2727, 1302, 2727, 2728, 2732, 1286,
   2747, 2732, 74, 3259, 74, 3259, 1307, 2727, 1303, 2727, 263, 2747, 279, 2747, 3255, 2727, 0, 204, 2727, 2215, 2215, 647, 2695, 647, 679,
   1159, 3207, 1159, 1191, 295, 2727, 262, 2727, 2728, 3239, 262, 3239, 3240, 262, 3220, 1204, 262, 262, 3252, 263, 262, 82, 2727, 263, 2727,
   74, 3239, 263, 3239, 2743, 2727, 2735, 3259, 3259, 2735, 3255, 0, 204, 3227, 228, 204, 3252, 2724, 3252, 3259, 74, 3259, 3259, 74, 2727,
   204, 2747, 2235, 2235, 1595, 200, 3223, 200, 228, 667, 2715, 667, 699, 652, 2700, 684, 652, 1562, 2732, 2732, 1562, 2732, 199, 3255, 2732,
   2732, 1546, 2747, 2732, 1563, 3255, 70, 1563, 82, 2747, 539, 2747, 2747, 3239, 2747, 2215, 3255, 2735, 2747, 2735, 3239, 0, 212, 2715, 212,
   228, 815, 1159, 3207, 1159, 1191, 1179, 3227, 1179, 1211, 2732, 3236, 2747, 2732, 1172, 3220, 1204, 1172, 782, 3252, 3252, 782, 3239, 782, 3239,
   3240, 3252, 774, 3259, 3252, 82, 2747, 82, 2747, 795, 3239, 783, 3239, 263, 3259, 271, 3259, 2735, 3239, 0, 204, 2727, 2215, 2215, 1159,
   3207, 1159, 1191, 647, 2695, 647, 679, 295, 3239, 262, 3239, 3240, 2727, 262, 2727, 2728, 262, 2700, 684, 262, 262, 2732, 263, 262, 74,
   3239, 263, 3239, 82, 2727, 263, 2727, 3247, 3239, 204, 2747, 2235, 2235, 3255, 2747, 2747, 3255, 2735, 0, 212, 2715, 228, 212, 2732, 3236,
   2732, 2747, 82, 2747, 2747, 82, 3239, 204, 2747, 2235, 2235, 1595, 200, 2703, 200, 228, 1179, 3227, 1179, 1211, 1172, 3220, 1204, 1172, 1562,
   3252, 3252, 1562, 3252, 199, 2735, 3252, 3252, 1554, 3259, 3252, 1563, 2735, 70, 1563, 74, 3259, 1051, 3259, 3259, 2727, 3259, 2215, 2735, 204,
   212, 204, 2747, 2747, 3259, 2235, 212, 3259, 2235, 2747, 204, 1823, 0, 2148, 200, 2735, 200, 2735, 204, 3259, 204, 3259, 212, 2747, 212,
   2747, 228, 652, 2732, 2732, 652, 3902, 2732, 2732, 3902, 2732, 199, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 652, 2732, 2732,
   652, 2150, 2735, 2150, 2735, 2154, 3259, 2154, 3259, 2162, 2747, 2162, 2747, 3871, 0, 228, 2732, 650, 2732, 1823, 2735, 198, 2735, 72, 3259,
   202, 3259, 76, 2747, 210, 2747, 84, 200, 1851, 200, 100, 204, 1847, 204, 100, 212, 1839, 212, 100, 652, 2698, 1855, 652, 652, 199,
   655, 652, 1172, 204, 1179, 1172, 652, 212, 667, 652, 200, 647, 204, 200, 200, 1159, 212, 200, 204, 667, 212, 204, 1823, 3255, 2727,
   3259, 3255, 2735, 3239, 2747, 2735, 200, 2735, 2735, 200, 204, 2747, 2235, 2235, 204, 3259, 3259, 204, 212, 2747, 2747, 212, 228, 228, 2148,
   0, 1822, 2732, 2732, 1822, 3902, 2730, 3903, 3902, 2732, 199, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 652, 2700, 684, 652,
   1823, 2148, 200, 2150, 2148, 2148, 204, 2154, 2148, 2148, 212, 2162, 2148, 3871, 2148, 228, 70, 200, 200, 70, 200, 2727, 204, 200, 200,
   3239, 212, 200, 200, 2150, 228, 200, 74, 204, 204, 74, 204, 2747, 212, 204, 204, 2154, 228, 204, 82, 212, 212, 82, 212, 2162,
   228, 212, 0, 684, 652, 2700, 652, 1823, 228, 200, 70, 200, 228, 204, 74, 204, 228, 212, 82, 212, 1822, 652, 652, 1822, 652,
   199, 655, 652, 1172, 204, 1179, 1172, 652, 212, 667, 652, 70, 200, 70, 200, 74, 204, 74, 204, 82, 212, 82, 212, 200, 647,
   204, 200, 200, 1159, 212, 200, 204, 667, 212, 204, 100]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem proof10 : cases10.foldlM (fun rem next => certifies goal 6 next rem) data10 = some [] := by
  decide +kernel

def cases11 : List (List Sig) := ((successors inputs 7).drop 137).take 10

set_option maxRecDepth 12000 in
def data11 : List ℕ :=
  [0, 684, 2732, 0, 652, 0, 70, 1819, 70, 100, 74, 1815, 74, 100, 82, 1807, 82, 100, 1822, 650, 1823, 1822, 655, 1818, 655,
   684, 1179, 676, 1179, 1204, 667, 1188, 667, 684, 1175, 647, 1179, 1175, 655, 1159, 667, 655, 74, 667, 155, 155, 228, 200, 70, 200,
   228, 204, 74, 204, 228, 212, 82, 212, 1822, 650, 1823, 1822, 655, 200, 655, 200, 1179, 204, 1179, 204, 667, 212, 667, 212, 70,
   200, 70, 200, 74, 204, 74, 204, 82, 212, 82, 212, 200, 647, 204, 200, 200, 1159, 212, 200, 204, 667, 212, 204, 652, 652,
   228, 2700, 2732, 228, 652, 652, 0, 684, 1823, 100, 228, 100, 200, 70, 200, 228, 204, 74, 204, 228, 212, 82, 212, 228, 1823,
   100, 1823, 100, 652, 70, 655, 70, 1172, 74, 1179, 74, 652, 82, 667, 82, 70, 200, 70, 100, 74, 204, 74, 100, 82, 212,
   82, 100, 70, 647, 74, 70, 70, 1159, 82, 70, 74, 667, 82, 74, 1823, 0, 200, 1851, 200, 100, 204, 1847, 204, 100, 212,
   1839, 212, 100, 228, 2732, 650, 2732, 1823, 2735, 198, 2735, 72, 3259, 202, 3259, 76, 2747, 210, 2747, 84, 652, 2698, 1855, 652, 2732,
   199, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 3255, 2727, 3259, 3255, 2735, 3239, 2747, 2735, 204, 2747, 2235, 2235, 0, 100,
   200, 2703, 200, 228, 204, 3227, 204, 228, 212, 2715, 212, 228, 652, 2700, 684, 652, 1822, 2732, 2732, 1822, 2732, 199, 2735, 2732, 3252,
   2724, 3259, 3252, 2732, 3236, 2747, 2732, 70, 2735, 70, 2735, 74, 3259, 74, 3259, 82, 2747, 82, 2747, 3255, 2727, 3259, 3255, 2735, 3239,
   2747, 2735, 204, 2747, 2235, 2235, 228, 70, 228, 200, 200, 0, 228, 204, 74, 204, 228, 212, 82, 212, 684, 652, 652, 2700, 1822,
   652, 1823, 1822, 652, 199, 655, 652, 1172, 204, 1179, 1172, 652, 212, 667, 652, 100, 228, 1823, 100, 198, 198, 1823, 200, 1303, 204,
   1311, 204, 783, 212, 799, 212, 70, 200, 647, 204, 200, 200, 1159, 212, 200, 204, 667, 212, 204, 70, 70, 0, 684, 652, 2700,
   652, 1563, 200, 228, 204, 74, 204, 228, 212, 82, 212, 1822, 652, 652, 1822, 652, 1818, 2703, 652, 1172, 204, 1179, 1172, 652, 212,
   667, 652, 70, 1823, 70, 72, 74, 204, 74, 204, 82, 212, 82, 212, 204, 2695, 204, 70, 212, 3207, 212, 70, 204, 667, 212,
   204, 200, 200, 228, 228, 74, 228, 204, 204, 0, 228, 212, 82, 212, 1204, 652, 652, 3220, 1822, 650, 1823, 1822, 652, 199, 655,
   652, 1172, 204, 1179, 1172, 652, 212, 667, 652, 100, 228, 1823, 100, 1563, 200, 1567, 200, 202, 202, 1823, 204, 783, 212, 799, 212,
   228, 200, 200, 70, 200, 647, 204, 200, 200, 1159, 212, 200, 74, 204, 667, 212, 204, 74, 74, 0, 652, 1172, 652, 1172, 1303,
   228, 200, 70, 200, 204, 228, 212, 82, 212, 1822, 1172, 1172, 1822, 1172, 199, 1175, 1172, 1172, 652, 3227, 1172, 652, 212, 148, 148,
   70, 200, 70, 200, 74, 1823, 74, 76, 82, 212, 82, 212, 200, 655, 74, 200, 200, 1159, 212, 200, 212, 667, 212, 74, 204,
   204, 228, 228, 82, 228, 212, 212, 0, 684, 652, 652, 2700, 1822, 652, 1823, 1822, 652, 199, 655, 652, 1172, 204, 1179, 1172, 652,
   212, 667, 652, 100, 228, 1823, 100, 1563, 200, 1567, 200, 1303, 204, 1311, 204, 210, 210, 1823, 212, 228, 200, 200, 70, 200, 647,
   204, 200, 200, 1159, 212, 200, 228, 204, 204, 74, 204, 667, 212, 204, 82, 82, 82, 0, 684, 652, 2700, 652, 783, 228, 200,
   70, 200, 228, 204, 74, 204, 212, 1822, 652, 652, 1822, 652, 199, 655, 652, 1172, 204, 140, 140, 652, 1172, 2715, 652, 70, 200,
   70, 200, 74, 204, 74, 204, 82, 1823, 82, 84, 200, 647, 204, 200, 200, 1175, 82, 200, 204, 1179, 82, 204, 212, 212, 228,
   1822, 1855, 1822, 652, 100, 652, 652, 1855, 652, 1822, 100, 1822, 652, 655, 652, 199, 200, 1822, 655, 655, 1822, 652, 200, 652, 1172,
   1179, 1172, 204, 204, 652, 1179, 1179, 652, 1172, 204, 1172, 652, 667, 652, 212, 212, 1172, 667, 667, 1172, 652, 212, 652, 70, 70,
   100, 200, 200, 1855, 70, 70, 1855, 200, 200, 100, 74, 74, 100, 204, 204, 1855, 74, 74, 1855, 204, 204, 100, 82, 82, 100,
   212, 212, 1855, 82, 82, 1855, 212, 212, 100, 200, 204, 200, 647, 0, 204, 667, 212, 204, 228, 204, 74, 204, 684, 652, 2700,
   652, 1303, 679, 647, 2695, 647, 699, 667, 2715, 667, 1172, 204, 1179, 1172, 1302, 652, 652, 1302, 647, 1302, 647, 648, 652, 1286, 667,
   652, 74, 204, 74, 204, 1339, 647, 1335, 647, 295, 667, 311, 667, 200, 647, 0, 204, 647, 200, 200, 679, 647, 2695, 647, 1191,
   1159, 3207, 1159, 262, 1172, 262, 1172, 263, 647, 262, 647, 648, 1159, 262, 1159, 1160, 262, 1172, 295, 262, 82, 647, 295, 647, 74,
   1159, 295, 1159, 663, 647, 655, 204, 204, 655, 200, 0, 1172, 204, 1172, 1179, 74, 204, 204, 74, 647, 204, 667, 212, 204, 228,
   204, 74, 204, 684, 652, 2700, 652, 1563, 228, 200, 70, 200, 699, 667, 2715, 667, 1562, 652, 652, 1562, 652, 199, 1175, 652, 652,
   1546, 667, 652, 1595, 200, 70, 1595, 82, 667, 571, 667, 667, 1159, 667, 200, 200, 200, 212, 200, 1159, 0, 228, 212, 82, 212,
   1204, 1172, 3220, 1172, 783, 1191, 1159, 3207, 1159, 1211, 1179, 3227, 1179, 652, 212, 667, 652, 782, 1172, 1172, 782, 1159, 782, 1159, 1160,
   1172, 774, 1179, 1172, 82, 212, 82, 212, 827, 1159, 815, 1159, 295, 1179, 303, 1179, 200, 1159, 0, 204, 647, 200, 200, 1191, 1159,
   3207, 1159, 679, 647, 2695, 647, 262, 652, 262, 652, 263, 1159, 262, 1159, 1160, 647, 262, 647, 648, 262, 652, 295, 262, 74, 1159,
   295, 1159, 82, 647, 295, 647, 1167, 1159, 204, 667, 212, 204, 1175, 212, 212, 1175, 200, 0, 652, 212, 652, 667, 82, 212, 212,
   82, 1159, 204, 667, 204, 212, 228, 212, 82, 212, 1204, 1172, 3220, 1172, 1563, 228, 200, 70, 200, 1211, 1179, 3227, 1179, 1562, 1172,
   1172, 1562, 1172, 199, 655, 1172, 1172, 1554, 1179, 1172, 1595, 200, 70, 1595, 74, 1179, 1083, 1179, 1179, 647, 1179, 200, 200, 204, 212,
   204, 667, 667, 1179, 212, 212, 1179, 204, 667, 204, 2148, 0, 2732, 652, 2732, 652, 1823, 2150, 200, 2150, 200, 2154, 204, 2154, 204,
   2162, 212, 2162, 212, 228, 3902, 652, 652, 3902, 652, 199, 655, 652, 1172, 204, 1179, 1172, 652, 212, 667, 652, 652, 2732, 2732, 652,
   2148, 200, 2150, 200, 2148, 204, 2154, 204, 2148, 212, 2162, 212, 0, 200, 1851, 200, 100, 204, 1847, 204, 100, 212, 1839, 212, 100,
   228, 2732, 650, 2732, 1823, 2735, 198, 2735, 72, 3259, 202, 3259, 76, 2747, 210, 2747, 84, 652, 2698, 1855, 652, 2732, 199, 2735, 2732,
   3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 3255, 2727, 3259, 3255, 2735, 3239, 2747, 2735, 204, 2747, 2235, 2235, 2148, 100, 200, 647, 204,
   200, 200, 1159, 212, 200, 200, 2118, 102, 200, 204, 667, 212, 204, 204, 2122, 106, 204, 212, 2130, 114, 212, 100, 228, 1823, 0,
   2732, 3902, 2732, 3902, 2148, 200, 2150, 200, 2150, 204, 2154, 204, 2154, 212, 2162, 212, 2162, 0, 100, 200, 2703, 200, 228, 204, 3227,
   204, 228, 212, 2715, 212, 228, 652, 2700, 684, 652, 1822, 2732, 2732, 1822, 2732, 199, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747,
   2732, 70, 2735, 70, 2735, 74, 3259, 74, 3259, 82, 2747, 82, 2747, 3255, 2727, 3259, 3255, 2735, 3239, 2747, 2735, 204, 2747, 2235, 2235,
   3902, 2732, 1823, 3902, 3642, 3898, 3646, 3642, 3382, 3894, 3390, 3382, 2862, 3886, 2878, 2862, 652, 3902, 3902, 652, 2150, 198, 2150, 72, 2154,
   202, 2154, 76, 2162, 210, 2162, 84, 1823, 228, 100, 2150, 2727, 2154, 2150, 2150, 3239, 2162, 2150, 200, 2150, 2150, 200, 2154, 2747, 2162,
   2154, 204, 2154, 2154, 204, 212, 2162, 2162, 212, 200, 204, 200]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem proof11 : cases11.foldlM (fun rem next => certifies goal 6 next rem) data11 = some [] := by
  decide +kernel

def cases12 : List (List Sig) := ((successors inputs 7).drop 147).take 2

set_option maxRecDepth 12000 in
def data12 : List ℕ :=
  [0, 2735, 0, 3252, 2724, 3252, 3259, 2148, 202, 2148, 2154, 2727, 204, 2747, 212, 204, 204, 2122, 228, 204, 3642, 2730, 3643, 3642, 2732,
   199, 3255, 2732, 2732, 3626, 2747, 2732, 652, 2700, 684, 652, 3643, 198, 2150, 3643, 2148, 2747, 2619, 2619, 1563, 3611, 1595, 1563, 2747, 3239,
   2747, 200, 200, 2118, 228, 200, 667, 2715, 699, 667, 212, 0, 212, 2130, 228, 212, 2732, 3236, 2747, 2732, 2862, 3250, 2863, 2862, 3252,
   2862, 3255, 3252, 3252, 2862, 3259, 3252, 1172, 3220, 1204, 1172, 2148, 210, 2162, 2148, 2875, 2863, 2863, 3631, 2871, 2863, 2863, 3375, 783, 2831,
   815, 783, 200, 3239, 212, 200, 3255, 2727, 3247, 3247, 1175, 3223, 1207, 1175, 204, 2747, 212, 204, 1179, 3227, 1211, 1179, 212, 0, 2732,
   3236, 2732, 2747, 2148, 210, 2148, 2162, 200, 3239, 200, 212, 204, 2747, 204, 212, 212, 2130, 228, 212, 3382, 3250, 3383, 3382, 3252, 3378,
   3255, 3252, 3252, 3634, 3259, 3252, 1172, 3220, 1204, 1172, 3643, 3255, 3127, 3643, 3383, 3259, 3131, 3383, 1303, 3351, 1335, 1303, 3255, 2727, 3259,
   3255, 1175, 3223, 1207, 1175, 1179, 3227, 1211, 1179, 228, 0, 652, 2700, 684, 652, 1822, 2730, 1823, 1822, 2703, 1822, 2703, 2704, 3252, 2724,
   3259, 3252, 2732, 3236, 2747, 2732, 1303, 228, 100, 100, 2148, 1823, 2150, 2148, 2148, 1823, 2154, 2148, 2148, 1807, 2162, 2148, 200, 2118, 228,
   200, 2150, 2703, 2126, 2126, 2150, 3239, 2162, 2150, 204, 2122, 228, 204, 2154, 2747, 2162, 2154, 212, 2130, 228, 212, 228, 0, 652, 2700,
   652, 684, 1823, 228, 100, 100, 200, 2118, 200, 228, 204, 2122, 204, 228, 212, 2130, 212, 228, 3382, 2730, 3383, 3382, 2732, 3378, 3255,
   2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 2148, 3255, 2150, 2148, 2148, 3259, 2154, 2148, 2148, 3367, 2162, 2148, 2150, 2727, 2154, 2150,
   2150, 3239, 2162, 2150, 2154, 2747, 2162, 2154, 2732, 3902, 3902, 2732, 3902, 2730, 3903, 3902, 2732, 3902, 3902, 2732, 3252, 3902, 3902, 3252, 2862,
   3886, 2878, 2862, 1822, 3870, 1854, 1822, 2148, 3903, 3903, 2148, 2148, 3903, 3903, 2148, 2148, 3903, 3903, 2148, 2863, 3887, 2879, 2863, 1823, 3871,
   1855, 1823, 2727, 204, 200, 200, 3239, 212, 200, 200, 2118, 228, 200, 204, 2747, 212, 204, 204, 2122, 228, 204, 212, 2130, 228, 212,
   2727]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem proof12 : cases12.foldlM (fun rem next => certifies goal 6 next rem) data12 = some [] := by
  decide +kernel

def cases13 : List (List Sig) := ((successors inputs 7).drop 149).take 1

set_option maxRecDepth 12000 in
def data13 : List ℕ :=
  [0, 204, 212, 204, 2747, 2747, 3259, 212, 212, 3259, 204, 2747, 204, 204, 228, 204, 2122, 0, 204, 2122, 667, 2138, 2122, 1172, 652,
   652, 1172, 3227, 652, 3227, 3228, 1302, 650, 1303, 1302, 647, 1302, 647, 648, 652, 1286, 667, 652, 0, 74, 1303, 74, 76, 1307, 1303,
   1303, 1559, 263, 1287, 279, 263, 74, 667, 2203, 667, 1302, 650, 1303, 1302, 3227, 652, 3227, 3228, 647, 1302, 647, 648, 652, 3236, 667,
   652, 3223, 647, 0, 82, 263, 263, 519, 74, 263, 263, 1031, 74, 647, 2183, 647, 647, 3236, 647, 648, 262, 3218, 263, 262, 3207,
   262, 3207, 3208, 663, 647, 1303, 1303, 100, 2122, 1303, 2122, 2124, 1307, 1303, 1303, 1559, 263, 1287, 279, 263, 0, 200, 2118, 200, 204,
   647, 648, 1302, 647, 1303, 1559, 1303, 1307, 647, 663, 212, 647, 2122, 667, 2138, 2122, 3227, 652, 3227, 3228, 1562, 650, 1563, 1562, 652,
   1546, 667, 652, 2122, 1563, 2122, 2124, 2148, 667, 539, 539, 2118, 647, 0, 212, 647, 647, 212, 2122, 647, 2118, 2118, 1159, 647, 262,
   647, 648, 1172, 262, 262, 1172, 3207, 262, 3207, 3208, 262, 3250, 263, 262, 2148, 263, 263, 519, 0, 82, 263, 263, 519, 74, 263,
   263, 1031, 74, 647, 2183, 647, 262, 3218, 263, 262, 647, 3236, 647, 648, 3207, 652, 3207, 3208, 263, 263, 100, 2122, 263, 263, 3079,
   663, 647, 212, 667, 667, 212, 2154, 228, 228, 2154, 204, 0, 2122, 652, 3220, 652, 1204, 1303, 228, 1303, 100, 0, 204, 2118, 200,
   200, 647, 2130, 663, 647, 2118, 3207, 2134, 2118, 647, 1302, 647, 648, 3223, 1302, 3223, 3224, 1302, 3250, 1303, 1302, 262, 1286, 278, 262,
   1307, 1303, 1303, 1559, 2118, 1303, 2118, 2120, 263, 1287, 279, 263, 667, 2130, 667, 228, 2162, 667, 2162, 204, 3252, 204, 1179, 3252, 3122,
   3250, 3124, 3122, 3252, 1302, 647, 3252, 2212, 3236, 2228, 2212, 2148, 202, 74, 2148, 2148, 1303, 1303, 2148, 2148, 1287, 2162, 2148, 200, 2162,
   0, 647, 2130, 647, 228, 3207, 262, 3220, 262, 1204, 263, 228, 263, 100, 2162, 647, 2162, 200, 2212, 3236, 2228, 2212, 3252, 262, 1159,
   3252, 3122, 3250, 3124, 3122, 2148, 263, 2162, 2148, 2148, 263, 263, 1031, 2162, 647, 204, 3252, 3259, 3252, 2724, 204, 2732, 3259, 3259, 2732,
   3252, 204, 3252, 3382, 3383, 3382, 2730, 2148, 2732, 3383, 3383, 2732, 3382, 2148, 3382, 2727, 2727, 2732, 3382, 0, 3259, 200, 3255, 200, 2727,
   212, 2743, 2727, 647, 2695, 679, 647, 200, 2747, 212, 200, 200, 2118, 228, 200, 2728, 199, 199, 3382, 200, 3382, 2148, 3383, 3382, 2342,
   3366, 2358, 2342, 1302, 3350, 1334, 1302, 3387, 3383, 3383, 3639, 2148, 198, 2150, 2148, 2343, 3367, 2359, 2343, 1303, 3351, 1335, 1303, 212, 2130,
   228, 212, 3382, 2727, 2727, 3382, 2728, 0, 3255, 3382, 3387, 3383, 3639, 3383, 2727, 0, 647, 2695, 679, 647, 200, 2727, 212, 200, 1159,
   3207, 1191, 1159, 2727, 2342, 2727, 2728, 3239, 2354, 3239, 3252, 2343, 3250, 2343, 2358, 278, 2326, 310, 278, 2148, 2343, 2343, 2599, 2148, 2343,
   2343, 3111, 263, 2311, 295, 263, 2743, 2727, 647, 2695, 679, 647, 200, 2747, 212, 200, 200, 2118, 228, 200, 3252, 2724, 3256, 3252, 3383,
   2726, 3383, 3638, 2728, 3622, 2744, 2728, 648, 2696, 680, 648, 2148, 3383, 3383, 2148, 2343, 3367, 2359, 2343, 1303, 3351, 1335, 1303, 667, 2715,
   699, 667, 2732, 2732, 2747, 2732, 3366, 212, 3382, 2747, 2747, 3382, 2732, 212, 2732, 652, 0, 204, 2122, 204, 228, 684, 1303, 228, 1303,
   100, 647, 0, 204, 2118, 200, 200, 647, 2130, 663, 647, 2118, 667, 2134, 2118, 647, 1302, 647, 648, 1330, 1302, 1302, 2118, 1302, 2148,
   1303, 1302, 262, 1286, 278, 262, 1307, 1303, 1303, 1559, 2118, 1303, 2118, 2120, 263, 1287, 279, 263, 647, 228, 667, 2130, 667, 228, 2154,
   667, 2162, 2154, 1172, 2154, 1179, 2154, 1302, 2148, 1303, 2148, 647, 1302, 647, 648, 652, 2162, 667, 2162, 2148, 202, 2154, 2148, 2148, 1303,
   1303, 2148, 2148, 1287, 2162, 2148, 2150, 2162, 0, 647, 2130, 647, 228, 1159, 2122, 1159, 228, 294, 263, 228, 263, 100, 2154, 647, 2150,
   2150, 647, 2162, 647, 2162, 1159, 262, 1159, 1160, 262, 1170, 263, 262, 2148, 263, 2162, 2148, 2148, 263, 263, 1031, 2162, 647, 652, 2700,
   228, 2732, 684, 0, 228, 204, 2122, 204, 652, 1303, 100, 1303, 0, 74, 1303, 74, 100, 1307, 1303, 1303, 1559, 263, 1287, 279, 263,
   74, 667, 155, 155, 1302, 650, 1303, 1302, 1179, 676, 1179, 1204, 647, 1302, 647, 680, 667, 1188, 667, 684, 1175, 647, 0, 82, 263,
   263, 519, 74, 263, 263, 1031, 74, 647, 135, 135, 647, 1188, 647, 680, 262, 1170, 263, 262, 1159, 262, 1159, 1192, 663, 647, 647,
   0, 228, 200, 2118, 200, 647, 212, 663, 647, 200, 667, 212, 200, 647, 1302, 647, 648, 199, 199, 1302, 200, 1302, 682, 1303, 1302,
   262, 1286, 278, 262, 1307, 1303, 1303, 1559, 70, 198, 70, 72, 263, 1287, 279, 263, 647, 228, 667, 212, 667, 212, 204, 667, 212,
   204, 1179, 204, 1179, 204, 1303, 682, 1303, 1334, 647, 1334, 647, 680, 667, 212, 667, 212, 74, 202, 74, 76, 1307, 1303, 1303, 1559,
   82, 210, 82, 84, 200, 212, 0, 647, 212, 647, 212, 1159, 204, 1159, 204, 262, 263, 100, 263, 0, 82, 263, 263, 519, 74,
   263, 263, 1031, 74, 647, 135, 135, 262, 1170, 263, 262, 647, 1188, 647, 680, 1159, 676, 1159, 1192, 204, 647, 200, 200, 647, 212,
   647, 212, 1159, 294, 1159, 1192, 263, 1202, 263, 294, 82, 210, 82, 84, 74, 263, 263, 1031, 212, 647, 2732, 652, 228, 652, 2148,
   2154, 2148, 202, 204, 3383, 2154, 2154, 3383, 2148, 204, 2148, 3387, 0, 200, 3383, 2727, 0, 647, 2695, 679, 647, 204, 2727, 200, 200,
   1159, 3207, 1191, 1159, 2727, 3366, 2727, 2728, 3239, 3378, 3239, 3240, 3367, 3250, 3367, 3368, 1302, 3350, 1334, 1302, 2148, 2727, 2343, 2343, 2148,
   3239, 3111, 3111, 1287, 3335, 1319, 1287, 2743, 2727, 647, 2695, 679, 647, 204, 2747, 212, 204, 204, 2118, 228, 204, 2727, 0, 3252, 2724,
   3255, 3252, 2727, 3366, 2743, 2727, 647, 2695, 679, 647, 199, 2747, 212, 199, 199, 2118, 228, 199, 3382, 2726, 3382, 3383, 2148, 198, 2150,
   2148, 2148, 210, 2162, 2148, 1307, 228, 100, 100, 212, 2130, 228, 212, 2727, 2728, 3252, 2724, 3259, 3252, 3382, 2726, 3387, 3382, 2732, 3366,
   2747, 2732, 652, 2700, 684, 652, 2148, 198, 2150, 2148, 2148, 2747, 2363, 2363, 1307, 3355, 1339, 1307, 667, 2715, 699, 667, 3643, 3383, 2727,
   3383, 3383, 0, 200, 200, 2150, 204, 2727, 2728, 3382, 2727, 3387, 2727, 2743, 2162, 2727, 647, 679, 2695, 647, 204, 2747, 212, 204, 204,
   3227, 228, 204, 3252, 2724, 3259, 3252, 3382, 2732, 2732, 3382, 2732, 3236, 2747, 2732, 652, 2700, 684, 652, 2150, 204, 2150, 204, 2343, 2747,
   2359, 2747, 1303, 228, 1335, 228, 667, 2715, 699, 667, 3383, 3639, 2727, 3643, 2343, 2162, 2343, 3367, 2747, 3383, 2359, 2162, 3383, 2343, 2747,
   2343, 1303, 0, 204, 3227, 204, 228, 1335, 647, 2695, 647, 679, 667, 2715, 667, 699, 204, 2747, 2235, 2235, 652, 2700, 684, 652, 3252,
   2724, 3259, 3252, 1302, 2732, 2732, 1302, 2727, 1302, 2727, 2728, 2732, 3236, 2747, 2732, 74, 3259, 74, 3259, 1307, 2727, 1303, 2727, 263, 2747,
   279, 2747, 3255, 2727, 0, 647, 2695, 647, 679, 1159, 3207, 1159, 1191, 295, 204, 2727, 2215, 2215, 2727, 3236, 2727, 2728, 262, 3220, 1204,
   262, 3239, 262, 3239, 3240, 262, 3252, 3252, 262, 82, 2727, 263, 2727, 74, 3239, 263, 3239, 2743, 2727, 1303, 3351, 228, 3383, 1335, 0,
   228, 204, 74, 204, 684, 652, 2700, 652, 1303, 679, 647, 2695, 647, 699, 667, 2715, 667, 204, 667, 212, 204, 1172, 204, 1179, 1172,
   1302, 652, 652, 1302, 647, 1302, 647, 648, 652, 212, 667, 652, 74, 204, 74, 204, 1339, 647, 1335, 647, 295, 667, 311, 667, 200,
   647, 0, 679, 647, 2695, 647, 1191, 1159, 3207, 1159, 262, 1172, 262, 1172, 263, 204, 647, 200, 200, 647, 212, 647, 648, 1159, 262,
   1159, 1160, 262, 1172, 1172, 262, 82, 647, 295, 647, 74, 1159, 295, 1159, 663, 647, 3383, 1303, 228, 1303, 200, 0, 3252, 2724, 3252,
   3259, 2148, 202, 2148, 2154, 2727, 204, 2747, 212, 204, 204, 2122, 228, 204, 3642, 2730, 3643, 3642, 2732, 199, 3255, 2732, 2732, 3626, 2747,
   2732, 652, 2700, 684, 652, 3643, 198, 2150, 3643, 2148, 2747, 2619, 2619, 1563, 3611, 1595, 1563, 2747, 3239, 2747, 200, 200, 2118, 228, 200,
   667, 2715, 699, 667, 0, 204, 2727, 2728, 3382, 2727, 3383, 3639, 3383, 3387, 2727, 2743, 212, 2727, 647, 679, 2695, 647, 200, 2747, 212,
   2747, 200, 2118, 228, 200, 3252, 2732, 2732, 3252, 3642, 2730, 3643, 3642, 2732, 3626, 2747, 2732, 652, 2700, 684, 652, 2148, 3643, 3643, 2148,
   2343, 2747, 2619, 2619, 1563, 3611, 1595, 1563, 667, 2715, 699, 667, 2727, 2747, 2727, 0, 647, 228, 647, 2695, 0, 647, 204, 1159, 1159,
   204, 2130, 1159, 2118, 2118, 652, 262, 262, 652, 2695, 262, 2695, 2696, 1159, 262, 1159, 1160, 262, 1170, 263, 262, 0, 82, 263, 263,
   519, 74, 263, 263, 1031, 74, 1159, 1159, 2183, 262, 1170, 263, 262, 2695, 1172, 2695, 2696, 1159, 2724, 1159, 1160, 263, 263, 100, 2130,
   263, 263, 2567, 2148, 263, 263, 1031, 2727, 679, 228, 2727, 647, 0, 2695, 1159, 2122, 1159, 228, 262, 2700, 262, 684, 263, 228, 263,
   100, 2154, 647, 200, 2154, 2732, 262, 647, 2732, 2212, 2724, 2220, 2212, 2602, 2730, 2604, 2602, 2148, 263, 263, 2148, 2148, 263, 2154, 2148,
   647, 204, 212, 204, 2727, 2727, 3239, 200, 212, 3239, 200, 2727, 204, 1159, 228, 1159, 3207, 0, 212, 647, 647, 212, 1159, 2122, 647,
   2118, 2118, 1172, 262, 262, 1172, 647, 262, 647, 648, 3207, 262, 3207, 3208, 262, 3250, 263, 262, 0, 82, 263, 263, 519, 74, 263,
   263, 1031, 74, 647, 2183, 647, 262, 3218, 263, 262, 647, 3236, 647, 648, 3207, 652, 3207, 3208, 263, 263, 100, 2148, 263, 263, 519,
   2122, 263, 263, 3079, 3239, 1191, 228, 3239, 1159, 0, 647, 2130, 647, 228, 3207, 262, 3220, 262, 1204, 263, 228, 263, 100, 2162, 647,
   2162, 200, 2212, 3236, 2228, 2212, 3252, 262, 1159, 3252, 3122, 3250, 3124, 3122, 2148, 263, 2162, 2148, 2148, 263, 263, 2148, 1159, 2727, 2727,
   2732, 2342, 212, 2342, 2727, 2727, 2342, 2728, 212, 2732, 3239, 3239, 3252, 2342, 204, 2342, 3239, 3239, 2342, 3240, 204, 3252, 2342, 2343, 2342,
   3250, 2148, 3252, 2343, 2343, 3252, 2342, 2148, 2342, 262, 0, 647, 2130, 647, 228, 1159, 2122, 1159, 228, 294, 263, 228, 263, 100, 2154,
   647, 2150, 2150, 647, 2162, 647, 2162, 1159, 2154, 1159, 2154, 262, 2148, 263, 2148, 2148, 263, 2162, 2148, 2148, 263, 2154, 2148, 262, 2310,
   228, 2342, 294, 0, 647, 212, 647, 212, 1159, 204, 1159, 204, 262, 263, 100, 263, 0, 82, 263, 263, 519, 74, 263, 263, 1031,
   74, 647, 135, 135, 262, 1170, 263, 262, 647, 1188, 647, 680, 1159, 676, 1159, 1192, 204, 647, 200, 200, 647, 212, 647, 212, 1159,
   204, 1159, 204, 263, 1202, 263, 294, 82, 210, 82, 84, 74, 202, 74, 76, 2342, 262, 228, 262, 2148, 2162, 2148, 2343, 2727, 2343,
   2343, 2162, 2343, 2599, 2727, 2148, 2148, 2154, 2148, 2343, 3239, 2343, 2343, 2154, 2343, 3111, 3239, 2148, 263, 0, 647, 2695, 647, 679, 1159,
   3207, 1159, 1191, 295, 204, 2727, 2215, 2215, 262, 3220, 1204, 262, 2727, 3236, 2727, 2728, 3239, 2724, 3239, 3240, 262, 3252, 3252, 262, 82,
   2727, 263, 2727, 74, 3239, 263, 3239, 263, 2311, 228, 2343, 295, 0, 679, 647, 2695, 647, 1191, 1159, 3207, 1159, 262, 1172, 262, 1172,
   263, 204, 647, 200, 200, 647, 212, 647, 648, 1159, 204, 1159, 1160, 262, 1172, 1172, 262, 82, 647, 295, 647, 74, 1159, 295, 1159,
   2343, 263, 228, 263, 0, 667, 2715, 699, 667, 204, 2747, 212, 204, 1179, 3227, 1211, 1179, 2732, 2342, 2747, 2732, 3252, 2342, 3259, 3252,
   2342, 3250, 2343, 2342, 2362, 2342, 2342, 3622, 262, 2310, 294, 262, 2148, 2343, 2343, 2619, 2148, 2343, 2343, 3131, 2363, 2343, 2343, 3623, 263,
   2311, 295, 263, 2727, 3239, 228, 0, 667, 2695, 647, 647, 1179, 3207, 1159, 1159, 2154, 2695, 2118, 2118, 282, 262, 262, 1542, 2695, 262,
   2695, 2696, 3207, 262, 3207, 3208, 262, 3250, 263, 262, 283, 263, 263, 1543, 2148, 263, 263, 2567, 2148, 263, 263, 3079, 228, 0, 647,
   2695, 647, 699, 1159, 3207, 1159, 1211, 262, 3590, 262, 314, 263, 3591, 263, 315, 2154, 2747, 2162, 2154, 2732, 3626, 2747, 2732, 3252, 3634,
   3259, 3252, 3642, 3250, 3643, 3642, 2148, 2747, 2619, 2619, 2148, 3259, 3131, 3131, 0, 647, 2695, 679, 647, 204, 3255, 200, 200, 3239, 3239,
   3255, 204, 1175, 3223, 1207, 1175, 2727, 3382, 2727, 2728, 3252, 3378, 3255, 3252, 3382, 3250, 3383, 3382, 2342, 3366, 2358, 2342, 1302, 3350, 1334,
   1302, 2148, 3383, 3383, 2599, 2148, 3255, 3127, 3127, 2343, 3367, 2359, 2343, 1303, 3351, 1335, 1303, 2743, 228, 0, 647, 2695, 663, 647, 1159,
   1159, 1175, 204, 2130, 1175, 2130, 2134, 262, 1286, 278, 262, 2711, 1302, 2711, 2712, 1172, 1298, 1175, 1172, 1302, 1170, 1303, 1302, 263, 1287,
   279, 263, 2130, 1303, 1303, 2583, 2148, 1175, 1047, 1047, 228, 0, 647, 2695, 647, 679, 1159, 2122, 1159, 1191, 262, 2310, 262, 294, 263,
   2311, 263, 295, 2154, 2727, 2150, 2150, 2727, 2342, 2727, 2728, 2212, 2342, 2342, 2212, 2342, 2730, 2343, 2342, 2148, 2343, 2343, 2599, 2148, 2343,
   2343, 2148, 2743, 2747, 0, 200, 2727, 2342, 2728, 2727, 3383, 2343, 3383, 2343, 0, 647, 2695, 679, 647, 204, 2727, 200, 200, 1159, 3207,
   1191, 1159, 2727, 2342, 2727, 2728, 3239, 2342, 3239, 3240, 2342, 3250, 2343, 2342, 262, 2310, 294, 262, 2148, 2343, 2343, 2599, 2148, 2343, 2343,
   3111, 263, 2311, 295, 263, 647, 2695, 679, 647, 204, 2743, 212, 204, 204, 2122, 228, 204, 3252, 2342, 2342, 3252, 2342, 2730, 2343, 2342,
   2342, 3370, 2743, 2342, 262, 2310, 294, 262, 2148, 2343, 2343, 2148, 2343, 2743, 2615, 2343, 263, 2311, 295, 263, 663, 2711, 695, 663, 2727,
   0, 204, 2747, 204, 212, 2732, 3626, 2732, 2747, 2343, 2747, 2343, 2619, 0, 647, 2695, 679, 647, 204, 2727, 200, 200, 1159, 3207, 1191,
   1159, 2727, 2342, 2727, 2728, 3239, 2342, 3239, 3240, 2342, 3250, 2343, 2342, 262, 2310, 294, 262, 2148, 2343, 2343, 2599, 2148, 2343, 2343, 3111,
   263, 2311, 295, 263, 667, 2715, 699, 667, 1179, 3227, 1211, 1179, 3252, 3634, 3259, 3252, 3642, 3250, 3643, 3642, 3642, 2342, 2727, 3642, 1562,
   3610, 1594, 1562, 2148, 3259, 3131, 3131, 3643, 2343, 2343, 3643, 1563, 3611, 1595, 1563, 200, 647, 2695, 679, 647, 2727, 647, 228, 647, 2695,
   0, 204, 2122, 228, 204, 2154, 2747, 2162, 2154, 652, 2700, 684, 652, 3252, 2724, 3259, 3252, 1302, 2730, 1303, 1302, 2695, 1302, 2695, 2696,
   2732, 1286, 2747, 2732, 1563, 1303, 1303, 1563, 2148, 1303, 2154, 2148, 1339, 1303, 1303, 3607, 263, 1287, 279, 263, 647, 2118, 2695, 0, 667,
   2695, 647, 647, 2154, 2695, 2118, 2118, 1179, 3207, 1159, 1159, 2695, 262, 2695, 2696, 282, 262, 262, 1542, 3207, 262, 3207, 3208, 262, 3250,
   263, 262, 2148, 263, 263, 2567, 283, 263, 263, 1543, 2148, 263, 263, 3079, 2711, 2695, 667, 2715, 699, 667, 2727, 679, 228, 2727, 647,
   0, 204, 2122, 204, 228, 652, 2700, 652, 684, 1303, 3611, 1303, 1595, 2695, 667, 2715, 667, 699, 2154, 2747, 2162, 2154, 3252, 2724, 3259,
   3252, 3642, 2730, 3643, 3642, 2732, 1302, 647, 2732, 2732, 3626, 2747, 2732, 2148, 3259, 2154, 2148, 3643, 1303, 1303, 3643, 2148, 2747, 2619, 2619,
   200, 2747, 0, 647, 2695, 647, 699, 1159, 3207, 1159, 1211, 262, 3590, 262, 314, 263, 3591, 263, 315, 2154, 2747, 2162, 2154, 2732, 3626,
   2747, 2732, 3252, 3634, 3259, 3252, 3642, 3250, 3643, 3642, 2148, 2747, 2619, 2619, 2148, 3259, 3131, 3131, 2747, 647, 647, 667, 228, 667, 2715,
   0, 204, 2122, 228, 204, 2130, 1179, 2130, 2138, 652, 2700, 684, 652, 1172, 2724, 1179, 1172, 1302, 2730, 1303, 1302, 2727, 1302, 2727, 2728,
   2715, 1302, 2715, 2716, 263, 1303, 1303, 263, 2148, 1303, 2154, 2148, 1307, 1303, 1303, 1559, 1319, 1303, 1303, 2327, 647, 2695, 679, 647, 2150,
   2715, 0, 647, 2695, 663, 647, 2130, 1175, 2130, 2134, 1159, 1159, 1175, 204, 2711, 1302, 2711, 2712, 262, 1286, 278, 262, 1172, 1298, 1175,
   1172, 1302, 1170, 1303, 1302, 2130, 1303, 1303, 2583, 263, 1287, 279, 263, 2148, 1175, 1047, 1047, 2711, 2711, 667, 2747, 699, 228, 2747, 667,
   0, 204, 2122, 204, 228, 652, 2700, 652, 684, 1303, 2311, 1303, 295, 647, 2695, 647, 679, 2715, 2154, 667, 212, 2154, 2212, 2724, 2220,
   2212, 2342, 2730, 2343, 2342, 2727, 2342, 2727, 2728, 2732, 1286, 667, 2732, 2148, 2343, 2154, 2148, 2148, 2343, 2343, 2599, 2343, 1287, 279, 2343,
   2150, 2727, 0, 647, 2695, 647, 679, 1159, 2122, 1159, 1191, 262, 2310, 262, 294, 263, 2311, 263, 295, 2154, 2727, 2150, 2150, 2727, 2342,
   2727, 2728, 1159, 2342, 2342, 1160, 2342, 1170, 2343, 2342, 2148, 2343, 2343, 2599, 2148, 2343, 2343, 1031, 663, 2727, 667]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem proof13 : cases13.foldlM (fun rem next => certifies goal 6 next rem) data13 = some [] := by
  decide +kernel

def cases14 : List (List Sig) := ((successors inputs 7).drop 150).take 7

set_option maxRecDepth 12000 in
def data14 : List ℕ :=
  [2735, 0, 212, 2747, 212, 2747, 228, 0, 1172, 652, 652, 1172, 1822, 650, 1823, 1822, 652, 1818, 655, 652, 3227, 652, 3227, 3228, 652,
   3236, 667, 652, 0, 70, 1819, 70, 72, 74, 1815, 74, 76, 82, 1807, 82, 100, 1822, 650, 1823, 1822, 652, 1818, 655, 652, 3227,
   652, 3227, 3228, 652, 3236, 667, 652, 3223, 647, 3227, 3223, 655, 3207, 667, 655, 74, 667, 2203, 667, 228, 100, 100, 2118, 1819, 2118,
   2120, 2122, 1815, 2122, 2124, 2148, 1807, 2162, 2148, 200, 2118, 647, 2122, 2118, 2118, 3207, 2134, 2118, 204, 2122, 667, 2138, 2122, 212, 2130,
   228, 212, 228, 0, 652, 3220, 652, 1204, 1823, 228, 100, 100, 2118, 2122, 212, 2130, 212, 228, 3122, 3250, 3124, 3122, 3252, 199, 655,
   3252, 3252, 204, 1179, 3252, 2212, 3236, 2228, 2212, 2148, 198, 70, 2148, 2148, 202, 74, 2148, 2148, 210, 2162, 2148, 200, 647, 204, 200,
   2162, 1159, 2162, 200, 2162, 667, 2162, 204, 3252, 2732, 2732, 3252, 3902, 2730, 3903, 3902, 2732, 3898, 2735, 2732, 3382, 2732, 2732, 3382, 2732,
   3886, 2747, 2732, 652, 2700, 684, 652, 2148, 3903, 3903, 2148, 3643, 3899, 3647, 3643, 3383, 3895, 3391, 3383, 2863, 3887, 2879, 2863, 1823, 3871,
   1855, 1823, 200, 2727, 2735, 0, 204, 2727, 2728, 3382, 2727, 3383, 3639, 3383, 3387, 2727, 2743, 212, 2727, 647, 679, 2695, 647, 200, 2747,
   212, 2747, 200, 2118, 228, 200, 3252, 2732, 2732, 3252, 3642, 2730, 3643, 3642, 2732, 3626, 2747, 2732, 652, 2700, 684, 652, 2148, 3643, 3643,
   2148, 2343, 2747, 2619, 2619, 1563, 3611, 1595, 1563, 667, 2715, 699, 667, 2735, 0, 655, 2703, 687, 655, 212, 2735, 200, 200, 1159, 3207,
   1191, 1159, 2732, 2858, 2735, 2732, 3239, 2862, 3239, 3240, 2862, 3250, 2863, 2862, 2342, 2854, 2350, 2342, 782, 2830, 814, 782, 2148, 2735, 2607,
   2607, 2148, 2863, 2863, 3111, 2343, 2855, 2351, 2343, 783, 2831, 815, 783, 2727, 2727, 212, 2735, 3247, 228, 0, 647, 647, 655, 212, 1159,
   3207, 1167, 1159, 2122, 655, 2126, 2122, 262, 774, 270, 262, 652, 778, 655, 652, 3215, 782, 3215, 3216, 782, 3250, 783, 782, 263, 775,
   271, 263, 2148, 655, 527, 527, 2122, 783, 783, 3087, 228, 0, 647, 2130, 647, 679, 1159, 3207, 1159, 1191, 262, 2310, 262, 294, 263,
   2311, 263, 295, 2162, 3239, 2150, 2150, 2212, 2342, 2342, 2212, 3239, 2342, 3239, 3240, 2342, 3250, 2343, 2342, 2148, 2343, 2343, 2148, 2148, 2343,
   2343, 3111, 2747, 2735, 655, 2703, 687, 655, 204, 212, 2747, 212, 2747, 228, 0, 228, 2122, 204, 204, 2122, 667, 2138, 2122, 1302, 652,
   652, 1302, 3227, 652, 3227, 3228, 1822, 650, 1823, 1822, 652, 1818, 655, 652, 652, 1806, 667, 652, 1303, 1815, 1311, 1303, 2122, 1823, 2122,
   2124, 1563, 1819, 1567, 1563, 783, 1807, 799, 783, 647, 647, 655, 0, 200, 2118, 200, 204, 647, 648, 1302, 647, 1303, 1559, 1303, 1307,
   647, 663, 212, 647, 2122, 667, 2138, 2122, 3227, 652, 3227, 3228, 1562, 650, 1563, 1562, 652, 1546, 667, 652, 2122, 1563, 2122, 2124, 2148,
   667, 539, 539, 2126, 655, 0, 647, 647, 655, 212, 2122, 655, 2126, 2122, 1159, 3207, 1167, 1159, 652, 778, 655, 652, 262, 774, 270,
   262, 3215, 782, 3215, 3216, 782, 3250, 783, 782, 2148, 655, 527, 527, 263, 775, 271, 263, 2122, 783, 783, 3087, 667, 655, 212, 667,
   667, 212, 228, 0, 204, 2122, 204, 228, 652, 3350, 652, 1334, 1303, 3351, 1303, 1335, 647, 0, 204, 2118, 200, 200, 647, 2130, 663,
   647, 2118, 3207, 2134, 2118, 647, 1302, 647, 648, 3223, 1302, 3223, 3224, 1302, 3250, 1303, 1302, 262, 1286, 278, 262, 1307, 1303, 1303, 1559,
   2118, 1303, 2118, 2120, 263, 1287, 279, 263, 647, 679, 667, 2130, 667, 228, 2162, 667, 2162, 204, 3252, 3382, 3382, 3252, 3382, 3250, 3383,
   3382, 3252, 3382, 3382, 3252, 2342, 3366, 2358, 2342, 2148, 3383, 3383, 2148, 2148, 3383, 3383, 2148, 2343, 3367, 2359, 2343, 2150, 2162, 0, 647,
   2130, 647, 679, 1159, 3207, 1159, 1191, 262, 2310, 262, 294, 263, 2311, 263, 295, 2162, 3239, 2150, 2150, 2212, 2342, 2342, 2212, 3239, 2342,
   3239, 3240, 2342, 3250, 2343, 2342, 2148, 2343, 2343, 2148, 2148, 2343, 2343, 3111, 2162, 647, 667, 2715, 699, 667, 204, 204, 2735, 0, 2732,
   3382, 2732, 3382, 2148, 3383, 2148, 3383, 200, 0, 204, 2747, 212, 204, 204, 2122, 228, 204, 3252, 2724, 3259, 3252, 3382, 2730, 3383, 3382,
   2727, 3382, 2727, 2728, 2732, 3366, 2747, 2732, 652, 2700, 684, 652, 2148, 202, 2154, 2148, 3387, 3383, 3383, 3639, 2343, 3367, 2359, 2343, 1303,
   3351, 1335, 1303, 200, 2727, 0, 647, 2695, 679, 647, 204, 2727, 200, 200, 1159, 3207, 1191, 1159, 2727, 2342, 2727, 2728, 3239, 2342, 3239,
   3240, 2342, 3250, 2343, 2342, 262, 2310, 294, 262, 2148, 2343, 2343, 2599, 2148, 2343, 2343, 3111, 263, 2311, 295, 263, 2743, 2727, 647, 2695,
   679, 647, 667, 2715, 699, 667, 212, 0, 212, 2130, 228, 212, 2732, 3236, 2747, 2732, 3902, 3250, 3903, 3902, 3239, 3898, 3239, 3240, 3252,
   3878, 3259, 3252, 1172, 3220, 1204, 1172, 2148, 210, 2162, 2148, 3643, 3899, 3647, 3643, 2343, 3879, 2367, 2343, 1823, 3871, 1855, 1823, 212, 3239,
   200, 200, 3239, 2735, 3259, 3239, 1159, 3207, 1191, 1159, 204, 2747, 212, 204, 1179, 3227, 1211, 1179, 212, 0, 212, 2130, 228, 212, 2732,
   3236, 2747, 2732, 3902, 3250, 3903, 3902, 3252, 3898, 3646, 3252, 3252, 3902, 3259, 3252, 1172, 3220, 1204, 1172, 2148, 210, 2162, 2148, 3643, 3899,
   3647, 3643, 2148, 3903, 3903, 3131, 1823, 3871, 1855, 1823, 200, 3239, 212, 200, 3259, 2727, 3259, 3263, 200, 2118, 228, 200, 204, 2747, 212,
   204, 1179, 3227, 1211, 1179, 228, 0, 652, 2700, 684, 652, 3902, 2730, 3903, 3902, 2732, 3898, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236,
   2747, 2732, 1823, 228, 100, 100, 2118, 3899, 2118, 2120, 2148, 3863, 2154, 2148, 2148, 3887, 2162, 2148, 228, 2118, 200, 200, 2118, 2695, 2154,
   2118, 2118, 3207, 2134, 2118, 204, 2122, 228, 204, 2154, 2747, 2162, 2154, 212, 2130, 228, 212, 228, 0, 212, 2130, 212, 228, 652, 2700,
   684, 652, 3902, 2730, 3903, 3902, 2732, 3898, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 1823, 228, 100, 100, 2148, 3899, 3647,
   2148, 2148, 3903, 2154, 2148, 2148, 3887, 2162, 2148, 200, 2118, 228, 200, 2154, 2735, 2154, 2158, 2162, 1159, 2162, 2735, 204, 2122, 228, 204,
   2154, 2747, 2162, 2154, 3382, 2730, 3383, 3382, 2732, 3382, 3382, 2732, 3382, 2724, 3259, 3382, 2342, 3366, 2358, 2342, 1302, 3350, 1334, 1302, 2148,
   3383, 3383, 2148, 3383, 202, 2154, 3383, 2343, 3367, 2359, 2343, 1303, 3351, 1335, 1303, 204, 2735, 208, 212, 0, 212, 2130, 228, 212, 200,
   3239, 2342, 3240, 3239, 2863, 2343, 2863, 2343, 0, 204, 2727, 200, 200, 1159, 3207, 1191, 1159, 647, 2695, 679, 647, 3239, 2342, 3239, 3240,
   2727, 2342, 2727, 2728, 2342, 2730, 2343, 2342, 262, 2310, 294, 262, 2148, 2343, 2343, 3111, 2148, 2343, 2343, 2599, 263, 2311, 295, 263, 1159,
   3207, 1191, 1159, 2732, 2342, 2342, 2732, 2342, 3250, 2343, 2342, 2342, 2862, 3247, 2342, 262, 2310, 294, 262, 2148, 2343, 2343, 2148, 2343, 2863,
   2863, 2343, 263, 2311, 295, 263, 204, 2735, 208, 204, 1167, 3215, 1199, 1167, 212, 2735, 228, 2703, 228, 655, 204, 2747, 212, 204, 204,
   2122, 228, 204, 212, 2130, 228, 212, 200]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem proof14 : cases14.foldlM (fun rem next => certifies goal 6 next rem) data14 = some [] := by
  decide +kernel

def cases15 : List (List Sig) := ((successors inputs 7).drop 157).take 6

set_option maxRecDepth 12000 in
def data15 : List ℕ :=
  [0, 3252, 3252, 3259, 2724, 2732, 204, 3252, 3252, 204, 3259, 2732, 3259, 2148, 2148, 2154, 202, 3643, 204, 2148, 2148, 204, 2154, 3643, 2154,
   2727, 0, 200, 2747, 212, 2747, 200, 2118, 228, 200, 204, 2727, 2728, 3382, 2727, 3383, 3639, 3383, 3387, 2727, 2743, 212, 2727, 647, 679,
   2695, 647, 3252, 2732, 2732, 3252, 3642, 2730, 3643, 3642, 2732, 3626, 2747, 2732, 652, 2700, 684, 652, 2148, 3643, 3643, 2148, 2343, 2747, 2619,
   2619, 1563, 3611, 1595, 1563, 667, 2715, 699, 667, 0, 204, 2747, 212, 204, 204, 2122, 228, 204, 3252, 2724, 3259, 3252, 3382, 2730, 3383,
   3382, 2727, 3382, 2727, 2728, 2732, 3366, 2747, 2732, 652, 2700, 684, 652, 2148, 202, 2154, 2148, 3387, 3383, 3383, 3639, 2343, 3367, 2359, 2343,
   1303, 3351, 1335, 1303, 200, 2727, 0, 647, 2695, 679, 647, 204, 2727, 200, 200, 1159, 3207, 1191, 1159, 2727, 2342, 2727, 2728, 3239, 2342,
   3239, 3240, 2342, 3250, 2343, 2342, 262, 2310, 294, 262, 2148, 2343, 2343, 2599, 2148, 2343, 2343, 3111, 263, 2311, 295, 263, 2743, 2727, 647,
   2695, 679, 647, 667, 2715, 699, 667, 204, 212, 204, 2747, 2747, 3259, 212, 212, 3259, 204, 2747, 204, 204, 228, 204, 2122, 0, 204,
   3227, 652, 3228, 3227, 2122, 1563, 2124, 2122, 679, 2122, 667, 2138, 2122, 1172, 652, 652, 1172, 1562, 650, 1563, 1562, 652, 3378, 3255, 652,
   652, 1546, 667, 652, 1303, 1563, 1563, 100, 1563, 3255, 2150, 1563, 2148, 667, 539, 539, 200, 2118, 228, 200, 667, 3239, 667, 2150, 212,
   667, 667, 212, 2154, 228, 228, 2154, 204, 0, 667, 2130, 667, 228, 2122, 3252, 204, 3252, 1179, 2148, 202, 2148, 74, 647, 2162, 667,
   2162, 204, 652, 3220, 1204, 652, 3382, 3250, 3383, 3382, 3252, 3378, 3255, 3252, 2212, 3236, 2228, 2212, 1563, 228, 100, 1563, 2148, 3255, 2150,
   2148, 2148, 3367, 2162, 2148, 200, 2118, 228, 200, 2150, 3239, 2162, 2150, 204, 3642, 3643, 3642, 2730, 2148, 2732, 3643, 3643, 2732, 3642, 2148,
   3642, 2732, 3255, 2732, 199, 200, 3382, 3255, 3255, 3382, 2732, 200, 2732, 2732, 2747, 2732, 3626, 212, 3642, 2747, 2747, 3642, 2732, 212, 2732,
   652, 0, 684, 1563, 228, 1563, 100, 200, 2118, 200, 228, 667, 2130, 667, 228, 204, 2122, 228, 204, 1172, 2154, 2154, 1179, 2148, 202,
   2148, 2154, 647, 2154, 667, 2162, 2154, 1562, 2148, 1563, 2148, 652, 2150, 1175, 2150, 652, 2162, 667, 2162, 2148, 198, 2150, 2148, 2148, 667,
   2162, 2148, 2150, 1159, 2162, 2150, 652, 2700, 228, 2732, 684, 0, 228, 204, 2122, 204, 652, 1563, 100, 1563, 0, 1563, 1175, 70, 1563,
   82, 667, 539, 539, 74, 1179, 100, 74, 1179, 676, 1204, 1179, 647, 74, 667, 155, 155, 1562, 650, 1563, 1562, 684, 1298, 1175, 684,
   667, 1188, 667, 684, 667, 1159, 667, 135, 228, 200, 2118, 200, 667, 212, 667, 212, 1179, 204, 204, 1179, 74, 202, 76, 74, 647,
   204, 667, 212, 204, 1563, 682, 1563, 1594, 684, 200, 1175, 200, 667, 212, 667, 212, 70, 198, 70, 72, 82, 210, 82, 84, 200,
   1159, 212, 200, 2732, 652, 228, 652, 3643, 2150, 3643, 198, 200, 3383, 2150, 2150, 3383, 3643, 200, 3643, 2148, 2162, 2148, 2747, 2747, 3643,
   2619, 2162, 3643, 2619, 2747, 2148, 1563, 0, 1595, 200, 3223, 200, 228, 667, 2715, 667, 699, 204, 3227, 228, 204, 3252, 2724, 3252, 3259,
   74, 3259, 3259, 74, 2727, 204, 2747, 2235, 2235, 652, 2700, 684, 652, 1562, 2732, 2732, 1562, 2732, 199, 3255, 2732, 2732, 3236, 2747, 2732,
   1563, 3255, 70, 3255, 82, 2747, 539, 2747, 2747, 3239, 2747, 2215, 1563, 3611, 228, 3643, 1595, 0, 228, 204, 74, 204, 684, 652, 2700,
   652, 1563, 228, 200, 70, 200, 699, 667, 2715, 667, 1172, 204, 1172, 1179, 74, 204, 204, 74, 647, 204, 667, 212, 204, 1562, 652,
   652, 1562, 652, 199, 1175, 652, 652, 212, 667, 652, 1595, 200, 70, 200, 82, 667, 571, 667, 667, 1159, 667, 200, 3643, 1563, 228,
   1563, 2747, 2747, 200, 3239, 0, 667, 2715, 699, 667, 204, 2747, 212, 204, 3252, 3634, 3252, 3259, 2343, 3259, 2343, 3131, 0, 204, 2727,
   200, 200, 1159, 3207, 1191, 1159, 647, 2695, 679, 647, 3239, 2342, 3239, 3240, 2727, 2342, 2727, 2728, 2342, 2730, 2343, 2342, 262, 2310, 294,
   262, 2148, 2343, 2343, 3111, 2148, 2343, 2343, 2599, 263, 2311, 295, 263, 1179, 3227, 1211, 1179, 2732, 3626, 2747, 2732, 3642, 3250, 3643, 3642,
   3642, 2342, 3239, 3642, 1562, 3610, 1594, 1562, 2148, 2747, 2619, 2619, 3643, 2343, 2343, 3643, 1563, 3611, 1595, 1563, 200, 1159, 3207, 1191, 1159,
   3255, 2747, 2747, 3255, 200, 0, 2732, 3626, 2732, 2747, 2148, 2747, 2619, 2619, 3239, 667, 2715, 699, 667, 204, 2747, 212, 204, 3252, 3634,
   3252, 3259, 2148, 3259, 3131, 3131, 2727, 1179, 3227, 1211, 1179, 3642, 3250, 3643, 3642, 3642, 199, 2215, 3642, 1562, 3610, 1594, 1562, 3643, 198,
   2150, 3643, 1563, 3611, 1595, 1563, 200, 2118, 228, 200, 200, 200, 228, 200, 2118, 0, 204, 2122, 228, 204, 3252, 2724, 3252, 3259, 2148,
   3259, 2148, 2154, 2695, 2154, 2747, 2162, 2154, 652, 2700, 684, 652, 3642, 2730, 3643, 3642, 2732, 1302, 3223, 2732, 2732, 3626, 2747, 2732, 1563,
   3611, 1595, 1563, 3643, 1303, 2118, 3643, 2148, 2747, 2619, 2619, 200, 2747, 3207, 2747, 2118, 667, 2715, 699, 667, 2150, 228, 228, 2150, 200,
   0, 652, 2700, 652, 684, 1563, 3611, 1563, 1595, 2118, 667, 2715, 667, 699, 204, 2122, 228, 204, 3252, 2724, 3252, 3259, 2148, 3259, 2148,
   2154, 647, 2154, 2747, 2162, 2154, 3642, 2730, 3643, 3642, 2732, 199, 1175, 2732, 2732, 3626, 2747, 2732, 3643, 198, 70, 3643, 2148, 2747, 2619,
   2619, 2747, 1159, 2747, 200, 200, 667, 228, 667, 2715, 0, 204, 2122, 228, 204, 1172, 2724, 1172, 1179, 2148, 1179, 2148, 2154, 2727, 2130,
   1179, 2130, 2138, 652, 2700, 684, 652, 1562, 2730, 1563, 1562, 2732, 1298, 1175, 2732, 2715, 1562, 2715, 2716, 263, 1563, 1563, 100, 1563, 1175,
   2150, 1563, 2130, 1563, 1563, 2587, 200, 2118, 228, 200, 2715, 1175, 2715, 2134, 667, 2747, 699, 228, 2747, 667, 0, 204, 2122, 204, 228,
   652, 2700, 652, 684, 1563, 228, 1563, 100, 200, 2118, 200, 228, 2715, 2212, 2724, 2212, 2220, 2148, 202, 2148, 2154, 2727, 2154, 667, 212,
   2154, 2602, 2730, 2604, 2602, 2732, 2150, 2215, 2732, 2732, 1546, 667, 2732, 2148, 2215, 2150, 2148, 2148, 667, 539, 2148, 2150, 1159, 667, 2150,
   667, 200, 0, 3252, 2732, 3252, 2732, 2148, 3643, 2148, 3643, 2735, 204, 212, 2747, 212, 2747, 228, 0, 1172, 652, 652, 1172, 3902, 650,
   3903, 3902, 652, 3866, 687, 652, 3227, 652, 3227, 3228, 652, 3236, 667, 652, 1823, 228, 100, 100, 2148, 3867, 2150, 2148, 2122, 3895, 2122,
   2124, 2148, 3887, 2162, 2148, 200, 2118, 228, 200, 2122, 679, 2122, 2150, 2150, 3239, 2162, 2150, 228, 2122, 204, 204, 2122, 667, 2138, 2122,
   212, 2130, 228, 212, 228, 0, 204, 2122, 204, 228, 212, 2130, 212, 228, 652, 3220, 1204, 652, 3902, 3250, 3903, 3902, 3252, 3902, 3255,
   3252, 3252, 3894, 3390, 3252, 2212, 3236, 2228, 2212, 1823, 228, 100, 100, 2148, 3903, 2150, 2148, 2148, 3895, 3391, 2148, 2148, 3887, 2162, 2148,
   200, 2118, 228, 200, 2150, 647, 2158, 2150, 2150, 3239, 2162, 2150, 2162, 667, 2162, 204, 3642, 2730, 3643, 3642, 2732, 199, 3255, 2732, 3252,
   2732, 2732, 3252, 2732, 3626, 2747, 2732, 652, 2700, 684, 652, 3643, 198, 2150, 3643, 2148, 3643, 3643, 2148, 2148, 2747, 2619, 2619, 1563, 3611,
   1595, 1563, 200, 0, 200, 2747, 212, 2747, 200, 2118, 228, 200, 204, 2727, 2728, 3382, 2727, 3383, 3639, 3383, 3387, 2727, 2743, 212, 2727,
   647, 679, 2695, 647, 3252, 2732, 2732, 3252, 3642, 2730, 3643, 3642, 2732, 3626, 2747, 2732, 652, 2700, 684, 652, 2148, 3643, 3643, 2148, 2343,
   2747, 2619, 2619, 1563, 3611, 1595, 1563, 667, 2715, 699, 667, 208, 2747, 3239, 2747, 200, 200, 2118, 228, 200, 212, 2747, 212, 2747, 228,
   0, 204, 3227, 652, 3228, 3227, 2122, 1563, 2124, 2122, 655, 2122, 667, 2138, 2122, 1172, 652, 652, 1172, 1562, 650, 1563, 1562, 652, 1822,
   3231, 652, 652, 1546, 667, 652, 1303, 1563, 1563, 100, 1563, 1823, 2126, 1563, 2148, 667, 539, 539, 200, 2118, 208, 200, 667, 3215, 667,
   2126, 212, 667, 667, 212, 228, 0, 2122, 652, 3220, 652, 1204, 1563, 228, 1563, 100, 200, 2118, 200, 228, 667, 2130, 667, 228, 3252,
   204, 3252, 1179, 2148, 202, 2148, 74, 647, 2162, 667, 2162, 204, 3382, 3250, 3383, 3382, 3252, 3378, 3255, 3252, 2212, 3236, 2228, 2212, 2148,
   3255, 2150, 2148, 2148, 3367, 2162, 2148, 2150, 3239, 2162, 2150, 667, 2715, 699, 667, 200, 212, 200]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem proof15 : cases15.foldlM (fun rem next => certifies goal 6 next rem) data15 = some [] := by
  decide +kernel

def cases16 : List (List Sig) := ((successors inputs 7).drop 163).take 2

set_option maxRecDepth 12000 in
def data16 : List ℕ :=
  [0, 3255, 204, 0, 204, 2747, 212, 204, 204, 2122, 228, 204, 3252, 2724, 3259, 3252, 3382, 2730, 3383, 3382, 2732, 3382, 2735, 2732, 2732,
   3374, 2747, 2732, 652, 2700, 684, 652, 2148, 202, 2154, 2148, 3387, 3383, 3383, 3639, 2863, 3375, 2871, 2863, 1303, 3351, 1335, 1303, 200, 2727,
   204, 200, 2735, 3239, 2743, 2735, 655, 2703, 687, 655, 667, 2715, 699, 667, 204, 0, 3252, 2724, 3252, 3259, 2148, 202, 2148, 2154, 200,
   2727, 200, 204, 204, 2747, 212, 204, 204, 2122, 228, 204, 2862, 2730, 2863, 2862, 2732, 2858, 2735, 2732, 2732, 3626, 2747, 2732, 652, 2700,
   684, 652, 3643, 2735, 2607, 3643, 2863, 2747, 2619, 2863, 783, 2831, 815, 783, 2735, 3239, 2747, 2735, 655, 2703, 687, 655, 667, 2715, 699,
   667, 0, 2732, 3236, 2732, 2747, 2148, 210, 2148, 2162, 3239, 204, 2747, 204, 212, 212, 2130, 228, 212, 3642, 3250, 3643, 3642, 3252, 199,
   2735, 3252, 3252, 3634, 3259, 3252, 1172, 3220, 1204, 1172, 3643, 198, 2150, 3643, 2148, 3259, 3131, 3131, 1563, 3611, 1595, 1563, 3259, 2727, 3259,
   200, 200, 2118, 228, 200, 1179, 3227, 1211, 1179, 228, 0, 652, 2700, 684, 652, 1822, 2730, 1823, 1822, 2732, 1822, 2735, 2732, 3252, 2724,
   3259, 3252, 2732, 3236, 2747, 2732, 783, 228, 100, 100, 2148, 1823, 2150, 2148, 2148, 1815, 2154, 2148, 2148, 1823, 2162, 2148, 200, 2118, 228,
   200, 2150, 2727, 2154, 2150, 2150, 3223, 2134, 2134, 204, 2122, 228, 204, 2154, 2747, 2162, 2154, 212, 2130, 228, 212, 228, 0, 652, 2700,
   652, 684, 1823, 228, 100, 100, 200, 2118, 200, 228, 204, 2122, 204, 228, 212, 2130, 212, 228, 2862, 2730, 2863, 2862, 2732, 2858, 2735,
   2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 2148, 2735, 2150, 2148, 2148, 2855, 2154, 2148, 2148, 2747, 2162, 2148, 2150, 2727, 2154, 2150,
   2150, 3239, 2162, 2150, 2154, 2747, 2162, 2154, 2732, 3902, 3902, 2732, 3902, 2730, 3903, 3902, 2732, 3902, 3902, 2732, 3382, 3894, 3390, 3382, 2732,
   3902, 3902, 2732, 1822, 3870, 1854, 1822, 2148, 3903, 3903, 2148, 2148, 3903, 3903, 2148, 3383, 3895, 3391, 3383, 2148, 3903, 3903, 2148, 1823, 3871,
   1855, 1823, 200, 2727, 204, 200, 3239, 212, 200, 200, 2118, 228, 200, 204, 2747, 212, 204, 204, 2122, 228, 204, 212, 2130, 228, 212,
   3239]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem proof16 : cases16.foldlM (fun rem next => certifies goal 6 next rem) data16 = some [] := by
  decide +kernel

def cases17 : List (List Sig) := ((successors inputs 7).drop 165).take 1

set_option maxRecDepth 12000 in
def data17 : List ℕ :=
  [0, 212, 228, 212, 2130, 0, 212, 652, 1172, 1172, 652, 2715, 1172, 2715, 2716, 782, 1170, 783, 782, 1159, 782, 1159, 1160, 1172, 774,
   1179, 1172, 0, 82, 783, 82, 84, 795, 783, 783, 1551, 263, 775, 271, 263, 782, 1170, 783, 782, 2715, 1172, 2715, 2716, 1159, 782,
   1159, 1160, 1172, 2724, 1179, 1172, 2703, 1159, 0, 74, 1159, 1159, 2183, 74, 263, 263, 1031, 82, 263, 263, 519, 1159, 2724, 1159, 1160,
   262, 2698, 263, 262, 2695, 262, 2695, 2696, 1167, 1159, 74, 1179, 1179, 2203, 783, 783, 100, 2130, 783, 2130, 2132, 795, 783, 783, 1551,
   263, 775, 271, 263, 0, 200, 2118, 200, 212, 1159, 1160, 782, 1159, 783, 1551, 783, 795, 1159, 1167, 204, 1159, 2715, 1172, 2715, 2716,
   1562, 1170, 1563, 1562, 1172, 1554, 1179, 1172, 2130, 1563, 2130, 2132, 2148, 1179, 1051, 1051, 2130, 1179, 2130, 2138, 2118, 1159, 0, 204, 1159,
   1159, 204, 2130, 1159, 2118, 2118, 647, 1159, 262, 1159, 1160, 652, 262, 262, 652, 2695, 262, 2695, 2696, 262, 2730, 263, 262, 2148, 263,
   263, 1031, 0, 74, 263, 263, 1031, 82, 263, 263, 519, 74, 1159, 1159, 2183, 262, 2698, 263, 262, 1159, 2724, 1159, 1160, 2695, 1172,
   2695, 2696, 263, 263, 100, 2130, 263, 263, 2567, 1167, 1159, 204, 1179, 1179, 204, 2130, 1179, 2130, 2138, 2162, 228, 228, 2162, 212, 0,
   2130, 1172, 2700, 1172, 684, 783, 228, 783, 100, 0, 212, 2118, 200, 200, 1159, 2122, 1167, 1159, 1159, 782, 1159, 1160, 2703, 782, 2703,
   2704, 782, 2730, 783, 782, 262, 774, 270, 262, 795, 783, 783, 1551, 2118, 783, 2118, 2120, 263, 775, 271, 263, 2118, 2695, 2118, 2126,
   1179, 2122, 1179, 228, 2732, 212, 667, 2732, 2602, 2730, 2604, 2602, 2732, 782, 1159, 2732, 2212, 2724, 2220, 2212, 2148, 210, 82, 2148, 2148,
   783, 783, 2148, 2148, 775, 2154, 2148, 200, 2154, 0, 2154, 647, 200, 2154, 1159, 2122, 1159, 228, 2695, 262, 2700, 262, 684, 263, 228,
   263, 100, 2212, 2724, 2220, 2212, 2732, 262, 647, 2732, 2602, 2730, 2604, 2602, 2148, 263, 2154, 2148, 2148, 263, 263, 519, 2154, 1159, 2154,
   667, 212, 2154, 212, 2732, 2747, 2732, 3236, 212, 3252, 2747, 2747, 3252, 2732, 212, 2732, 2862, 2863, 2862, 3250, 2148, 3252, 2863, 2863, 3252,
   2862, 2148, 2862, 3239, 3239, 3252, 2862, 0, 2747, 200, 2735, 200, 3239, 204, 3247, 3239, 1159, 3207, 1191, 1159, 200, 2118, 228, 200, 3240,
   199, 199, 2862, 200, 2862, 2148, 2863, 2862, 2342, 2854, 2350, 2342, 782, 2830, 814, 782, 2875, 2863, 2863, 3631, 2148, 198, 2150, 2148, 2343,
   2855, 2351, 2343, 783, 2831, 815, 783, 200, 2747, 200, 204, 204, 2122, 228, 204, 2862, 3239, 3239, 2862, 3240, 0, 2735, 2862, 2875, 2863,
   3631, 2863, 3239, 0, 200, 2727, 200, 204, 1159, 3207, 1191, 1159, 647, 2695, 679, 647, 3239, 2342, 3239, 3240, 2727, 2346, 2727, 2732, 2343,
   2730, 2343, 2350, 270, 2318, 302, 270, 2148, 2343, 2343, 3111, 2148, 2343, 2343, 2599, 263, 2311, 295, 263, 3247, 3239, 1159, 3207, 1191, 1159,
   200, 2118, 228, 200, 2732, 3236, 2736, 2732, 2863, 3238, 2863, 3630, 3240, 3622, 3248, 3240, 1160, 3208, 1192, 1160, 2148, 2863, 2863, 2148, 2343,
   2855, 2351, 2343, 783, 2831, 815, 783, 200, 2747, 200, 204, 1179, 3227, 1211, 1179, 3252, 3252, 3259, 3252, 2854, 204, 2862, 3259, 3259, 2862,
   3252, 204, 3252, 1172, 0, 212, 2130, 212, 228, 1204, 783, 228, 783, 100, 1159, 0, 212, 2118, 200, 200, 1159, 2122, 1167, 1159, 1159,
   782, 1159, 1160, 810, 782, 782, 2118, 782, 2148, 783, 782, 262, 774, 270, 262, 795, 783, 783, 1551, 2118, 783, 2118, 2120, 263, 775,
   271, 263, 2118, 667, 2118, 2126, 1159, 228, 1179, 2122, 1179, 228, 652, 2162, 667, 2162, 782, 2148, 783, 2148, 1159, 782, 1159, 1160, 1172,
   2154, 1179, 2154, 2148, 210, 2162, 2148, 2148, 783, 783, 2148, 2148, 775, 2154, 2148, 2150, 2154, 0, 2154, 647, 2150, 2150, 1159, 2122, 1159,
   228, 647, 2130, 647, 228, 294, 263, 228, 263, 100, 1159, 2154, 1159, 2154, 647, 262, 647, 648, 262, 650, 263, 262, 2148, 263, 2154,
   2148, 2148, 263, 263, 519, 2154, 1159, 2154, 667, 2162, 2154, 1172, 3220, 228, 3252, 1204, 0, 228, 212, 2130, 212, 1172, 783, 100, 783,
   0, 82, 783, 82, 100, 795, 783, 783, 1551, 263, 775, 271, 263, 782, 1170, 783, 782, 667, 1188, 667, 684, 1159, 782, 1159, 1192,
   1179, 676, 1179, 1204, 655, 1159, 0, 74, 647, 135, 135, 74, 263, 263, 1031, 82, 263, 263, 519, 1159, 676, 1159, 1192, 262, 650,
   263, 262, 647, 262, 647, 680, 1167, 1159, 74, 667, 155, 155, 1159, 0, 228, 200, 2118, 200, 1159, 204, 1167, 1159, 1159, 782, 1159,
   1160, 199, 199, 782, 200, 782, 1202, 783, 782, 262, 774, 270, 262, 795, 783, 783, 1551, 70, 198, 70, 72, 263, 775, 271, 263,
   200, 667, 200, 204, 1159, 228, 1179, 204, 1179, 204, 667, 212, 667, 212, 783, 1202, 783, 814, 1159, 814, 1159, 1192, 1179, 204, 1179,
   204, 82, 210, 82, 84, 795, 783, 783, 1551, 74, 202, 74, 76, 200, 204, 0, 204, 647, 200, 200, 1159, 204, 1159, 204, 647,
   212, 647, 212, 262, 263, 100, 263, 0, 74, 263, 263, 1031, 82, 263, 263, 519, 74, 647, 135, 135, 262, 650, 263, 262, 1159,
   676, 1159, 1192, 647, 1188, 647, 680, 1159, 204, 1159, 204, 647, 294, 647, 680, 263, 682, 263, 294, 74, 202, 74, 76, 82, 263,
   263, 519, 204, 1159, 204, 667, 212, 204, 3252, 1172, 228, 1172, 2148, 2162, 2148, 210, 212, 2863, 2162, 2162, 2863, 2148, 212, 2148, 2875,
   0, 200, 2863, 3239, 0, 204, 2727, 200, 200, 1159, 3207, 1191, 1159, 647, 2695, 679, 647, 3239, 2854, 3239, 3240, 2727, 2858, 2727, 2728,
   2855, 2730, 2855, 2856, 782, 2830, 814, 782, 2148, 2855, 2343, 2343, 2148, 2727, 2599, 2599, 775, 2823, 807, 775, 3247, 3239, 1159, 3207, 1191,
   1159, 212, 2118, 228, 212, 3239, 0, 2732, 3236, 2735, 2732, 3239, 2854, 3247, 3239, 1159, 3207, 1191, 1159, 199, 2118, 228, 199, 2862, 3238,
   2862, 2863, 2148, 198, 2150, 2148, 2148, 202, 2154, 2148, 795, 228, 100, 100, 199, 2747, 199, 204, 204, 2122, 228, 204, 3239, 3240, 2732,
   3236, 2747, 2732, 2862, 3238, 2875, 2862, 3252, 2854, 3259, 3252, 1172, 3220, 1204, 1172, 2148, 198, 2150, 2148, 2148, 2875, 2363, 2363, 795, 2843,
   827, 795, 204, 2747, 212, 204, 1179, 3227, 1211, 1179, 3643, 2863, 3239, 2863, 2863, 0, 200, 200, 2150, 212, 3239, 3240, 2862, 3239, 2875,
   3239, 3247, 2154, 3239, 1159, 1191, 3207, 1159, 212, 2715, 228, 212, 2732, 3236, 2747, 2732, 2862, 3252, 3252, 2862, 3252, 2724, 3259, 3252, 1172,
   3220, 1204, 1172, 2150, 212, 2150, 212, 2343, 3259, 2351, 3259, 783, 228, 815, 228, 204, 2747, 212, 204, 1179, 3227, 1211, 1179, 2863, 3631,
   3239, 3643, 2343, 2154, 2343, 2855, 3259, 2863, 2351, 2154, 2863, 2343, 3259, 2343, 783, 0, 212, 2715, 212, 228, 815, 1159, 3207, 1159, 1191,
   1179, 3227, 1179, 1211, 1172, 3220, 1204, 1172, 2732, 3236, 2747, 2732, 782, 3252, 3252, 782, 3239, 782, 3239, 3240, 3252, 2724, 3259, 3252, 82,
   2747, 82, 2747, 795, 3239, 783, 3239, 263, 3259, 271, 3259, 2735, 3239, 0, 204, 2727, 2215, 2215, 1159, 3207, 1159, 1191, 647, 2695, 647,
   679, 295, 3239, 2724, 3239, 3240, 262, 2700, 684, 262, 2727, 262, 2727, 2728, 262, 2732, 2732, 262, 74, 3239, 263, 3239, 82, 2727, 263,
   2727, 3247, 3239, 204, 2747, 2235, 2235, 783, 2831, 228, 2863, 815, 0, 228, 212, 82, 212, 1204, 1172, 3220, 1172, 783, 1191, 1159, 3207,
   1159, 1211, 1179, 3227, 1179, 652, 212, 667, 652, 782, 1172, 1172, 782, 1159, 782, 1159, 1160, 1172, 204, 1179, 1172, 82, 212, 82, 212,
   827, 1159, 815, 1159, 295, 1179, 303, 1179, 200, 1159, 0, 204, 647, 200, 200, 1191, 1159, 3207, 1159, 679, 647, 2695, 647, 262, 652,
   262, 652, 263, 1159, 204, 1159, 1160, 647, 262, 647, 648, 262, 652, 652, 262, 74, 1159, 295, 1159, 82, 647, 295, 647, 1167, 1159,
   204, 667, 212, 204, 2863, 783, 228, 783, 200, 0, 2732, 3236, 2732, 2747, 2148, 210, 2148, 2162, 3239, 204, 2747, 204, 212, 212, 2130,
   228, 212, 3642, 3250, 3643, 3642, 3252, 199, 2735, 3252, 3252, 3634, 3259, 3252, 1172, 3220, 1204, 1172, 3643, 198, 2150, 3643, 2148, 3259, 3131,
   3131, 1563, 3611, 1595, 1563, 3259, 2727, 3259, 200, 200, 2118, 228, 200, 1179, 3227, 1211, 1179, 0, 212, 3239, 3240, 2862, 3239, 2863, 3631,
   2863, 2875, 3239, 3247, 204, 3239, 1159, 1191, 3207, 1159, 200, 2118, 228, 200, 2732, 3252, 3252, 2732, 3642, 3250, 3643, 3642, 3252, 3634, 3259,
   3252, 1172, 3220, 1204, 1172, 2148, 3643, 3643, 2148, 2343, 3259, 3131, 3131, 1563, 3611, 1595, 1563, 200, 3259, 3259, 204, 1179, 3227, 1211, 1179,
   3239, 3259, 3239, 0, 204, 212, 204, 2727, 2727, 3239, 200, 212, 3239, 200, 2727, 204, 1159, 228, 1159, 3207, 0, 1159, 2122, 647, 2118,
   2118, 212, 647, 647, 212, 1172, 262, 262, 1172, 3207, 262, 3207, 3208, 647, 262, 647, 648, 262, 650, 263, 262, 0, 74, 263, 263,
   1031, 82, 263, 263, 519, 74, 647, 2183, 647, 262, 650, 263, 262, 3207, 652, 3207, 3208, 647, 3236, 647, 648, 263, 263, 100, 2122,
   263, 263, 3079, 2148, 263, 263, 519, 3239, 1191, 228, 3239, 1159, 0, 3207, 647, 2130, 647, 228, 262, 3220, 262, 1204, 263, 228, 263,
   100, 2162, 647, 2162, 200, 3252, 262, 1159, 3252, 2212, 3236, 2228, 2212, 3122, 3250, 3124, 3122, 2148, 263, 263, 2148, 2148, 263, 2162, 2148,
   1159, 647, 228, 647, 2695, 0, 204, 1159, 1159, 204, 2130, 1159, 2118, 2118, 647, 652, 262, 262, 652, 1159, 262, 1159, 1160, 2695, 262,
   2695, 2696, 262, 2730, 263, 262, 0, 74, 263, 263, 1031, 82, 263, 263, 519, 74, 1159, 1159, 2183, 262, 2698, 263, 262, 1159, 2724,
   1159, 1160, 2695, 1172, 2695, 2696, 263, 263, 100, 2148, 263, 263, 1031, 2130, 263, 263, 2567, 2727, 679, 228, 2727, 647, 0, 1159, 2122,
   1159, 228, 2695, 262, 2700, 262, 684, 263, 228, 263, 100, 2154, 647, 200, 2154, 2212, 2724, 2220, 2212, 2732, 262, 647, 2732, 2602, 2730,
   2604, 2602, 2148, 263, 2154, 2148, 2148, 263, 263, 2148, 647, 3239, 3239, 3252, 2342, 204, 2342, 3239, 3239, 2342, 3240, 204, 3252, 2727, 2727,
   2732, 2342, 212, 2342, 2727, 2727, 2342, 2728, 212, 2732, 2342, 2343, 2342, 2730, 2148, 2732, 2343, 2343, 2732, 2342, 2148, 2342, 262, 0, 1159,
   2122, 1159, 228, 647, 2130, 647, 228, 294, 263, 228, 263, 100, 2154, 647, 2150, 2150, 1159, 2154, 1159, 2154, 647, 2162, 647, 2162, 262,
   2148, 263, 2148, 2148, 263, 2154, 2148, 2148, 263, 2162, 2148, 262, 2310, 228, 2342, 294, 0, 1159, 204, 1159, 204, 647, 212, 647, 212,
   262, 263, 100, 263, 0, 74, 263, 263, 1031, 82, 263, 263, 519, 74, 647, 135, 135, 262, 650, 263, 262, 1159, 676, 1159, 1192,
   647, 1188, 647, 680, 204, 647, 200, 200, 1159, 204, 1159, 204, 647, 212, 647, 212, 263, 682, 263, 294, 74, 202, 74, 76, 82,
   210, 82, 84, 2342, 262, 228, 262, 2148, 2154, 2148, 2343, 3239, 2343, 2343, 2154, 2343, 3111, 3239, 2148, 2148, 2162, 2148, 2343, 2727, 2343,
   2343, 2162, 2343, 2599, 2727, 2148, 263, 0, 1159, 3207, 1159, 1191, 647, 2695, 647, 679, 295, 204, 2727, 2215, 2215, 262, 2700, 684, 262,
   3239, 2724, 3239, 3240, 2727, 3236, 2727, 2728, 262, 2732, 2732, 262, 74, 3239, 263, 3239, 82, 2727, 263, 2727, 263, 2311, 228, 2343, 295,
   0, 1191, 1159, 3207, 1159, 679, 647, 2695, 647, 262, 652, 262, 652, 263, 204, 647, 200, 200, 1159, 204, 1159, 1160, 647, 212, 647,
   648, 262, 652, 652, 262, 74, 1159, 295, 1159, 82, 647, 295, 647, 2343, 263, 228, 263, 0, 204, 2747, 212, 204, 1179, 3227, 1211,
   1179, 667, 2715, 699, 667, 3252, 2342, 3259, 3252, 2732, 2342, 2747, 2732, 2342, 2730, 2343, 2342, 2362, 2342, 2342, 3622, 262, 2310, 294, 262,
   2148, 2343, 2343, 3131, 2148, 2343, 2343, 2619, 2363, 2343, 2343, 3623, 263, 2311, 295, 263, 3239, 2727, 228, 0, 1179, 3207, 1159, 1159, 2154,
   2695, 2118, 2118, 667, 2695, 647, 647, 282, 262, 262, 1542, 3207, 262, 3207, 3208, 2695, 262, 2695, 2696, 262, 2730, 263, 262, 283, 263,
   263, 1543, 2148, 263, 263, 3079, 2148, 263, 263, 2567, 228, 0, 1159, 3207, 1159, 1211, 647, 2695, 647, 699, 262, 3590, 262, 314, 263,
   3591, 263, 315, 2154, 2747, 2162, 2154, 3252, 3634, 3259, 3252, 2732, 3626, 2747, 2732, 3642, 2730, 3643, 3642, 2148, 3259, 3131, 3131, 2148, 2747,
   2619, 2619, 0, 212, 2735, 200, 200, 1159, 3207, 1191, 1159, 655, 2703, 687, 655, 3239, 2862, 3239, 3240, 2732, 2858, 2735, 2732, 2862, 2730,
   2863, 2862, 2342, 2854, 2350, 2342, 782, 2830, 814, 782, 2148, 2863, 2863, 3111, 2148, 2735, 2607, 2607, 2343, 2855, 2351, 2343, 783, 2831, 815,
   783, 3247, 2727, 2727, 212, 2735, 228, 0, 1159, 3207, 1167, 1159, 2122, 655, 2126, 2122, 647, 647, 655, 212, 262, 774, 270, 262, 3215,
   782, 3215, 3216, 652, 778, 655, 652, 782, 650, 783, 782, 263, 775, 271, 263, 2122, 783, 783, 3087, 2148, 655, 527, 527, 228, 0,
   1159, 3207, 1159, 1191, 647, 2130, 647, 679, 262, 2310, 262, 294, 263, 2311, 263, 295, 2162, 3239, 2150, 2150, 3239, 2342, 3239, 3240, 2212,
   2342, 2342, 2212, 2342, 3250, 2343, 2342, 2148, 2343, 2343, 3111, 2148, 2343, 2343, 2148, 3247, 3259, 0, 200, 3239, 2342, 3240, 3239, 2863, 2343,
   2863, 2343, 0, 204, 2727, 200, 200, 1159, 3207, 1191, 1159, 647, 2695, 679, 647, 3239, 2342, 3239, 3240, 2727, 2342, 2727, 2728, 2342, 2730,
   2343, 2342, 262, 2310, 294, 262, 2148, 2343, 2343, 3111, 2148, 2343, 2343, 2599, 263, 2311, 295, 263, 1159, 3207, 1191, 1159, 212, 2130, 228,
   212, 2732, 2342, 2342, 2732, 2342, 3250, 2343, 2342, 2342, 2862, 3247, 2342, 262, 2310, 294, 262, 2148, 2343, 2343, 2148, 2343, 2863, 2863, 2343,
   263, 2311, 295, 263, 204, 2735, 208, 204, 1167, 3215, 1199, 1167, 3239, 0, 204, 2747, 212, 204, 3252, 3634, 3252, 3259, 2343, 3259, 2343,
   3131, 0, 204, 2727, 200, 200, 1159, 3207, 1191, 1159, 647, 2695, 679, 647, 3239, 2342, 3239, 3240, 2727, 2342, 2727, 2728, 2342, 2730, 2343,
   2342, 262, 2310, 294, 262, 2148, 2343, 2343, 3111, 2148, 2343, 2343, 2599, 263, 2311, 295, 263, 1179, 3227, 1211, 1179, 667, 2715, 699, 667,
   2732, 3626, 2747, 2732, 3642, 2730, 3643, 3642, 3642, 2342, 3239, 3642, 1562, 3610, 1594, 1562, 2148, 2747, 2619, 2619, 3643, 2343, 2343, 3643, 1563,
   3611, 1595, 1563, 200, 1159, 3207, 1191, 1159, 3239, 1159, 228, 1159, 3207, 0, 212, 2130, 228, 212, 1172, 3220, 1204, 1172, 2732, 3236, 2747,
   2732, 782, 3250, 783, 782, 3207, 782, 3207, 3208, 3252, 774, 3259, 3252, 1563, 783, 783, 1563, 2148, 783, 2162, 2148, 827, 783, 783, 3599,
   263, 775, 271, 263, 1159, 2118, 3207, 0, 1179, 3207, 1159, 1159, 2154, 2695, 2118, 2118, 667, 2695, 647, 647, 3207, 262, 3207, 3208, 282,
   262, 262, 1542, 2695, 262, 2695, 2696, 262, 2730, 263, 262, 2148, 263, 263, 3079, 283, 263, 263, 1543, 2148, 263, 263, 2567, 3215, 3207,
   1179, 3227, 1211, 1179, 2154, 2747, 2162, 2154, 3239, 1191, 228, 3239, 1159, 0, 212, 2130, 212, 228, 1172, 3220, 1172, 1204, 783, 3611, 783,
   1595, 3207, 1179, 3227, 1179, 1211, 2732, 3236, 2747, 2732, 3642, 3250, 3643, 3642, 3252, 782, 1159, 3252, 3252, 3634, 3259, 3252, 2148, 2747, 2162,
   2148, 3643, 783, 783, 3643, 2148, 3259, 3131, 3131, 200, 3259, 0, 2154, 2747, 2162, 2154, 1159, 3207, 1159, 1211, 647, 2695, 647, 699, 262,
   3590, 262, 314, 263, 3591, 263, 315, 3252, 3634, 3259, 3252, 2732, 3626, 2747, 2732, 3642, 2730, 3643, 3642, 2148, 3259, 3131, 3131, 2148, 2747,
   2619, 2619, 3259, 1159, 2154, 2747, 2162, 2154, 1159, 204, 212, 204, 2747, 2747, 3259, 212, 212, 3259, 204, 2747, 204, 1179, 228, 1179, 3227,
   0, 212, 2130, 228, 212, 1172, 3220, 1204, 1172, 652, 3236, 667, 652, 782, 3250, 783, 782, 3239, 782, 3239, 3240, 3227, 782, 3227, 3228,
   263, 783, 783, 263, 2148, 783, 2162, 2148, 795, 783, 783, 1551, 807, 783, 783, 2319, 1159, 3207, 1191, 1159, 2150, 3227, 0, 1159, 3207,
   1167, 1159, 2122, 655, 2126, 2122, 647, 647, 655, 212, 3215, 782, 3215, 3216, 262, 774, 270, 262, 652, 778, 655, 652, 782, 650, 783,
   782, 2122, 783, 783, 3087, 263, 775, 271, 263, 2148, 655, 527, 527, 3215, 3215, 1179, 2122, 667, 2138, 2122, 3259, 1211, 228, 3259, 1179,
   0, 212, 2130, 212, 228, 1172, 3220, 1172, 1204, 783, 2311, 783, 295, 1159, 3207, 1159, 1191, 3227, 2212, 3236, 2228, 2212, 2342, 3250, 2343,
   2342, 3239, 2342, 3239, 3240, 3252, 774, 1179, 3252, 2148, 2343, 2162, 2148, 2148, 2343, 2343, 3111, 2343, 775, 271, 2343, 2150, 3239, 0, 2162,
   3239, 2150, 2150, 1159, 3207, 1159, 1191, 647, 2130, 647, 679, 262, 2310, 262, 294, 263, 2311, 263, 295, 3239, 2342, 3239, 3240, 647, 2342,
   2342, 648, 2342, 650, 2343, 2342, 2148, 2343, 2343, 3111, 2148, 2343, 2343, 519, 1167, 3239, 2162, 667, 2162, 204, 1179]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem proof17 : cases17.foldlM (fun rem next => certifies goal 6 next rem) data17 = some [] := by
  decide +kernel

def cases18 : List (List Sig) := ((successors inputs 7).drop 166).take 7

set_option maxRecDepth 12000 in
def data18 : List ℕ :=
  [3255, 0, 228, 0, 652, 2700, 684, 652, 1822, 2730, 1823, 1822, 2703, 1818, 2703, 2704, 1172, 2724, 1179, 1172, 2715, 1172, 2715, 2716, 0,
   70, 1819, 70, 72, 74, 1815, 74, 100, 82, 1807, 82, 84, 1822, 2698, 1823, 1822, 2703, 1818, 2703, 2704, 1172, 2724, 1179, 1172, 2715,
   1172, 2715, 2716, 1175, 2695, 1179, 1175, 2703, 1159, 2715, 2703, 74, 1179, 1179, 2203, 228, 100, 100, 2118, 1819, 2118, 2120, 2148, 1815, 2154,
   2148, 2130, 1807, 2130, 2132, 200, 2118, 2695, 2126, 2118, 2118, 1159, 2130, 2118, 204, 2122, 228, 204, 2130, 1179, 2130, 2138, 212, 228, 0,
   652, 2700, 652, 684, 1823, 228, 100, 100, 2118, 204, 2122, 204, 228, 2130, 2602, 2730, 2604, 2602, 2732, 199, 655, 2732, 2212, 2724, 2220,
   2212, 2732, 212, 667, 2732, 2148, 198, 70, 2148, 2148, 202, 2154, 2148, 2148, 210, 82, 2148, 2154, 647, 2154, 200, 200, 1159, 212, 200,
   2154, 667, 212, 2154, 2732, 3252, 3252, 2732, 3902, 3250, 3903, 3902, 3252, 3898, 3255, 3252, 3252, 3894, 3259, 3252, 2862, 3252, 3252, 2862, 1172,
   3220, 1204, 1172, 2148, 3903, 3903, 2148, 3643, 3899, 3647, 3643, 3383, 3895, 3391, 3383, 2863, 3887, 2879, 2863, 1823, 3871, 1855, 1823, 200, 3255,
   0, 204, 3255, 200, 200, 3239, 3239, 3255, 204, 1175, 3223, 1207, 1175, 647, 2695, 679, 647, 3252, 3378, 3255, 3252, 2727, 3382, 2727, 2728,
   3382, 2730, 3383, 3382, 2342, 3366, 2358, 2342, 1302, 3350, 1334, 1302, 2148, 3255, 3127, 3127, 2148, 3383, 3383, 2599, 2343, 3367, 2359, 2343, 1303,
   3351, 1335, 1303, 2743, 228, 0, 1159, 1159, 1175, 204, 2130, 1175, 2130, 2134, 647, 2695, 663, 647, 262, 1286, 278, 262, 1172, 1298, 1175,
   1172, 2711, 1302, 2711, 2712, 1302, 2730, 1303, 1302, 263, 1287, 279, 263, 2148, 1175, 1047, 1047, 2130, 1303, 1303, 2583, 228, 0, 1159, 2122,
   1159, 1191, 647, 2695, 647, 679, 262, 2310, 262, 294, 263, 2311, 263, 295, 2154, 2727, 2150, 2150, 2212, 2342, 2342, 2212, 2727, 2342, 2727,
   2728, 2342, 2730, 2343, 2342, 2148, 2343, 2343, 2148, 2148, 2343, 2343, 2599, 3259, 3255, 3239, 3255, 0, 212, 3239, 3240, 2862, 3239, 2863, 3631,
   2863, 2875, 3239, 3247, 204, 3239, 1159, 1191, 3207, 1159, 200, 2118, 228, 200, 2732, 3252, 3252, 2732, 3642, 3250, 3643, 3642, 3252, 3634, 3259,
   3252, 1172, 3220, 1204, 1172, 2148, 3643, 3643, 2148, 2343, 3259, 3131, 3131, 1563, 3611, 1595, 1563, 200, 3259, 3259, 204, 1179, 3227, 1211, 1179,
   1175, 3223, 1207, 1175, 204, 3259, 3259, 204, 204, 3259, 3259, 204, 1179, 3227, 1211, 1179, 212, 228, 0, 228, 2130, 212, 212, 782, 1172,
   1172, 782, 2715, 1172, 2715, 2716, 1822, 1170, 1823, 1822, 1172, 1818, 1175, 1172, 1172, 1814, 1179, 1172, 783, 1807, 799, 783, 2130, 1823, 2130,
   2132, 1563, 1819, 1567, 1563, 1303, 1815, 1311, 1303, 1159, 1159, 1175, 0, 200, 2118, 200, 212, 1159, 1160, 782, 1159, 783, 1551, 783, 795,
   1159, 1167, 204, 1159, 2715, 1172, 2715, 2716, 1562, 1170, 1563, 1562, 1172, 1554, 1179, 1172, 2130, 1563, 2130, 2132, 2148, 1179, 1051, 1051, 2130,
   1179, 2130, 2138, 2134, 1175, 0, 1159, 1159, 1175, 204, 2130, 1175, 2130, 2134, 647, 2695, 663, 647, 1172, 1298, 1175, 1172, 262, 1286, 278,
   262, 2711, 1302, 2711, 2712, 1302, 2730, 1303, 1302, 2148, 1175, 1047, 1047, 263, 1287, 279, 263, 2130, 1303, 1303, 2583, 1179, 1175, 204, 1179,
   1179, 204, 2130, 1179, 2130, 2138, 228, 0, 212, 2130, 212, 228, 1172, 2830, 1172, 814, 783, 2831, 783, 815, 1159, 0, 212, 2118, 200,
   200, 1159, 2122, 1167, 1159, 1159, 782, 1159, 1160, 2703, 782, 2703, 2704, 782, 2730, 783, 782, 262, 774, 270, 262, 795, 783, 783, 1551,
   2118, 783, 2118, 2120, 263, 775, 271, 263, 2118, 2695, 2118, 2126, 1159, 1191, 1179, 2122, 1179, 228, 2732, 2862, 2862, 2732, 2862, 2730, 2863,
   2862, 2732, 2862, 2862, 2732, 2342, 2854, 2350, 2342, 2148, 2863, 2863, 2148, 2148, 2863, 2863, 2148, 2343, 2855, 2351, 2343, 2150, 2154, 0, 2154,
   2727, 2150, 2150, 1159, 2122, 1159, 1191, 647, 2695, 647, 679, 262, 2310, 262, 294, 263, 2311, 263, 295, 2212, 2342, 2342, 2212, 2727, 2342,
   2727, 2728, 2342, 2730, 2343, 2342, 2148, 2343, 2343, 2148, 2148, 2343, 2343, 2599, 2154, 1159, 2154, 667, 212, 2154, 212, 212, 3255, 0, 2732,
   2862, 2732, 2862, 2148, 2863, 2148, 2863, 200, 204, 0, 204, 2747, 212, 204, 204, 2122, 228, 204, 3252, 2724, 3259, 3252, 3902, 2730, 3903,
   3902, 2727, 3898, 2727, 2728, 2732, 3878, 2747, 2732, 652, 2700, 684, 652, 2148, 202, 2154, 2148, 3643, 3899, 3647, 3643, 2343, 3879, 2367, 2343,
   1823, 3871, 1855, 1823, 204, 2727, 200, 200, 2727, 3255, 2747, 2727, 647, 2695, 679, 647, 667, 2715, 699, 667, 204, 0, 204, 2747, 212,
   204, 204, 2122, 228, 204, 3252, 2724, 3259, 3252, 3902, 2730, 3903, 3902, 2732, 3898, 3646, 2732, 2732, 3902, 2747, 2732, 652, 2700, 684, 652,
   2148, 202, 2154, 2148, 3643, 3899, 3647, 3643, 2148, 3903, 3903, 2619, 1823, 3871, 1855, 1823, 200, 2727, 204, 200, 2747, 3239, 2747, 2751, 200,
   2118, 228, 200, 667, 2715, 699, 667, 0, 212, 2130, 228, 212, 2732, 3236, 2747, 2732, 2862, 3250, 2863, 2862, 3239, 2862, 3239, 3240, 3252,
   2854, 3259, 3252, 1172, 3220, 1204, 1172, 2148, 210, 2162, 2148, 2875, 2863, 2863, 3631, 2343, 2855, 2351, 2343, 783, 2831, 815, 783, 200, 3239,
   0, 204, 2727, 200, 200, 1159, 3207, 1191, 1159, 647, 2695, 679, 647, 3239, 2342, 3239, 3240, 2727, 2342, 2727, 2728, 2342, 2730, 2343, 2342,
   262, 2310, 294, 262, 2148, 2343, 2343, 3111, 2148, 2343, 2343, 2599, 263, 2311, 295, 263, 3247, 3239, 1159, 3207, 1191, 1159, 204, 2747, 212,
   204, 1179, 3227, 1211, 1179, 228, 0, 652, 2700, 684, 652, 3902, 2730, 3903, 3902, 2703, 3898, 2703, 2704, 3252, 2724, 3259, 3252, 2732, 3236,
   2747, 2732, 1823, 228, 100, 100, 2118, 3899, 2118, 2120, 2148, 3895, 2154, 2148, 2148, 3855, 2162, 2148, 228, 2118, 200, 200, 2118, 2695, 2126,
   2118, 2118, 3207, 2162, 2118, 204, 2122, 228, 204, 2154, 2747, 2162, 2154, 212, 2130, 228, 212, 228, 0, 652, 2700, 684, 652, 3902, 2730,
   3903, 3902, 2732, 3898, 3255, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 1823, 228, 100, 100, 2148, 3899, 3647, 2148, 2148, 3895, 2154,
   2148, 2148, 3903, 2162, 2148, 200, 2118, 228, 200, 2154, 647, 2154, 3255, 2162, 3255, 2162, 2166, 204, 2122, 228, 204, 2154, 2747, 2162, 2154,
   212, 2130, 228, 212, 2862, 2730, 2863, 2862, 2732, 2862, 2862, 2732, 2342, 2854, 2350, 2342, 2862, 3236, 2747, 2862, 782, 2830, 814, 782, 2148,
   2863, 2863, 2148, 2343, 2855, 2351, 2343, 2863, 210, 2162, 2863, 783, 2831, 815, 783, 204, 0, 204, 2743, 212, 204, 204, 2122, 228, 204,
   200, 2727, 2342, 2728, 2727, 3383, 2343, 3383, 2343, 0, 647, 2695, 679, 647, 204, 2727, 200, 200, 1159, 3207, 1191, 1159, 2727, 2342, 2727,
   2728, 3239, 2342, 3239, 3240, 2342, 3250, 2343, 2342, 262, 2310, 294, 262, 2148, 2343, 2343, 2599, 2148, 2343, 2343, 3111, 263, 2311, 295, 263,
   647, 2695, 679, 647, 3252, 2342, 2342, 3252, 2342, 2730, 2343, 2342, 2342, 3370, 2743, 2342, 262, 2310, 294, 262, 2148, 2343, 2343, 2148, 2343,
   2743, 2615, 2343, 263, 2311, 295, 263, 663, 2711, 695, 663, 204, 3255, 212, 3255, 216, 228, 3223, 228, 1175, 204, 2747, 212, 204, 204,
   2122, 228, 204, 212, 2130, 228, 212, 200]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem proof18 : cases18.foldlM (fun rem next => certifies goal 6 next rem) data18 = some [] := by
  decide +kernel

def cases19 : List (List Sig) := ((successors inputs 7).drop 173).take 6

set_option maxRecDepth 12000 in
def data19 : List ℕ :=
  [0, 2732, 2732, 2747, 3236, 3252, 212, 2732, 2732, 212, 2747, 3252, 2747, 2148, 2148, 2162, 210, 3643, 212, 2148, 2148, 212, 2162, 3643, 2162,
   3239, 0, 200, 2118, 228, 200, 212, 3239, 3240, 2862, 3239, 2863, 3631, 2863, 2875, 3239, 3247, 204, 3239, 1159, 1191, 3207, 1159, 2732, 3252,
   3252, 2732, 3642, 3250, 3643, 3642, 3252, 3634, 3259, 3252, 1172, 3220, 1204, 1172, 2148, 3643, 3643, 2148, 2343, 3259, 3131, 3131, 1563, 3611, 1595,
   1563, 200, 3259, 3259, 204, 1179, 3227, 1211, 1179, 0, 212, 2130, 228, 212, 2732, 3236, 2747, 2732, 2862, 3250, 2863, 2862, 3239, 2862, 3239,
   3240, 3252, 2854, 3259, 3252, 1172, 3220, 1204, 1172, 2148, 210, 2162, 2148, 2875, 2863, 2863, 3631, 2343, 2855, 2351, 2343, 783, 2831, 815, 783,
   200, 3239, 0, 204, 2727, 200, 200, 1159, 3207, 1191, 1159, 647, 2695, 679, 647, 3239, 2342, 3239, 3240, 2727, 2342, 2727, 2728, 2342, 2730,
   2343, 2342, 262, 2310, 294, 262, 2148, 2343, 2343, 3111, 2148, 2343, 2343, 2599, 263, 2311, 295, 263, 3247, 3239, 1159, 3207, 1191, 1159, 204,
   2747, 212, 204, 1179, 3227, 1211, 1179, 204, 204, 212, 2747, 3259, 2747, 204, 204, 2747, 212, 3259, 212, 212, 228, 212, 2130, 0, 212,
   2715, 1172, 2716, 2715, 2130, 1563, 2132, 2130, 1191, 2130, 1179, 2138, 2130, 652, 1172, 1172, 652, 1562, 1170, 1563, 1562, 1172, 2858, 2735, 1172,
   1172, 1554, 1179, 1172, 783, 1563, 1563, 100, 1563, 2735, 2150, 1563, 2148, 1179, 1051, 1051, 200, 2118, 228, 200, 1179, 2727, 1179, 2150, 204,
   1179, 1179, 204, 2162, 228, 228, 2162, 212, 0, 1179, 2122, 1179, 228, 2130, 2732, 212, 2732, 667, 2148, 210, 2148, 82, 1159, 2154, 667,
   2154, 212, 1172, 2700, 684, 1172, 2862, 2730, 2863, 2862, 2732, 2858, 2735, 2732, 2212, 2724, 2220, 2212, 1563, 228, 100, 1563, 2148, 2735, 2150,
   2148, 2148, 2855, 2154, 2148, 200, 2118, 228, 200, 2150, 2727, 2154, 2150, 212, 3642, 3643, 3642, 3250, 2148, 3252, 3643, 3643, 3252, 3642, 2148,
   3642, 3252, 2735, 3252, 199, 200, 2862, 2735, 2735, 2862, 3252, 200, 3252, 3252, 3259, 3252, 3634, 204, 3642, 3259, 3259, 3642, 3252, 204, 3252,
   1172, 0, 1204, 1563, 228, 1563, 100, 200, 2118, 200, 228, 1179, 2122, 1179, 228, 212, 2130, 228, 212, 652, 2162, 2162, 667, 2148, 210,
   2148, 2162, 1159, 2154, 667, 2154, 2162, 1562, 2148, 1563, 2148, 1172, 2150, 655, 2150, 1172, 2154, 1179, 2154, 2148, 198, 2150, 2148, 2148, 1179,
   2154, 2148, 2150, 647, 2154, 2150, 1172, 3220, 228, 3252, 1204, 0, 228, 212, 2130, 212, 1172, 1563, 100, 1563, 0, 1563, 655, 70, 1563,
   74, 1179, 1051, 1051, 82, 667, 100, 82, 667, 1188, 684, 667, 1159, 74, 667, 155, 155, 1562, 1170, 1563, 1562, 1204, 778, 655, 1204,
   1179, 676, 1179, 1204, 1179, 647, 1179, 135, 228, 200, 2118, 200, 1179, 204, 1179, 204, 667, 212, 212, 667, 82, 210, 84, 82, 1159,
   204, 667, 204, 212, 1563, 1202, 1563, 1594, 1204, 200, 655, 200, 1179, 204, 1179, 204, 70, 198, 70, 72, 74, 202, 74, 76, 200,
   647, 204, 200, 3252, 1172, 228, 1172, 3643, 2150, 3643, 198, 200, 2863, 2150, 2150, 2863, 3643, 200, 3643, 2148, 2154, 2148, 3259, 3259, 3643,
   3131, 2154, 3643, 3131, 3259, 2148, 1563, 0, 1595, 200, 2703, 200, 228, 1179, 3227, 1179, 1211, 212, 2715, 228, 212, 2732, 3236, 2732, 2747,
   82, 2747, 2747, 82, 3239, 204, 2747, 2235, 2235, 1172, 3220, 1204, 1172, 1562, 3252, 3252, 1562, 3252, 199, 2735, 3252, 3252, 2724, 3259, 3252,
   1563, 2735, 70, 2735, 74, 3259, 1051, 3259, 3259, 2727, 3259, 2215, 1563, 3611, 228, 3643, 1595, 0, 228, 212, 82, 212, 1204, 1172, 3220,
   1172, 1563, 228, 200, 70, 200, 1211, 1179, 3227, 1179, 652, 212, 652, 667, 82, 212, 212, 82, 1159, 204, 667, 204, 212, 1562, 1172,
   1172, 1562, 1172, 199, 655, 1172, 1172, 204, 1179, 1172, 1595, 200, 70, 200, 74, 1179, 1083, 1179, 1179, 647, 1179, 200, 3643, 1563, 228,
   1563, 3259, 3259, 200, 2727, 0, 1179, 3227, 1211, 1179, 204, 2747, 204, 212, 2732, 3626, 2732, 2747, 2343, 2747, 2343, 2619, 0, 647, 2695,
   679, 647, 204, 2727, 200, 200, 1159, 3207, 1191, 1159, 2727, 2342, 2727, 2728, 3239, 2342, 3239, 3240, 2342, 3250, 2343, 2342, 262, 2310, 294,
   262, 2148, 2343, 2343, 2599, 2148, 2343, 2343, 3111, 263, 2311, 295, 263, 667, 2715, 699, 667, 3252, 3634, 3259, 3252, 3642, 2730, 3643, 3642,
   3642, 2342, 2727, 3642, 1562, 3610, 1594, 1562, 2148, 3259, 3131, 3131, 3643, 2343, 2343, 3643, 1563, 3611, 1595, 1563, 200, 647, 2695, 679, 647,
   2735, 3259, 3259, 2735, 200, 0, 204, 2747, 212, 204, 3252, 3634, 3252, 3259, 2148, 3259, 3131, 3131, 2727, 1179, 3227, 1211, 1179, 2732, 3626,
   2732, 2747, 2148, 2747, 2619, 2619, 3239, 667, 2715, 699, 667, 3642, 2730, 3643, 3642, 3642, 199, 2215, 3642, 1562, 3610, 1594, 1562, 3643, 198,
   2150, 3643, 1563, 3611, 1595, 1563, 200, 2118, 228, 200, 200, 200, 228, 200, 2118, 0, 212, 2130, 228, 212, 2732, 3236, 2732, 2747, 2148,
   2747, 2148, 2162, 3207, 2154, 2747, 2154, 2162, 1172, 3220, 1204, 1172, 3642, 3250, 3643, 3642, 3252, 782, 2703, 3252, 3252, 3634, 3259, 3252, 1563,
   3611, 1595, 1563, 3643, 783, 2118, 3643, 2148, 3259, 3131, 3131, 200, 3259, 2695, 3259, 2118, 1179, 3227, 1211, 1179, 2150, 228, 228, 2150, 200,
   0, 1172, 3220, 1172, 1204, 1563, 3611, 1563, 1595, 2118, 1179, 3227, 1179, 1211, 212, 2130, 228, 212, 2732, 3236, 2732, 2747, 2148, 2747, 2148,
   2162, 1159, 2154, 2747, 2154, 2162, 3642, 3250, 3643, 3642, 3252, 199, 655, 3252, 3252, 3634, 3259, 3252, 3643, 198, 70, 3643, 2148, 3259, 3131,
   3131, 3259, 647, 3259, 200, 200, 1179, 228, 1179, 3227, 0, 212, 2130, 228, 212, 652, 3236, 652, 667, 2148, 667, 2148, 2162, 3239, 2122,
   667, 2122, 2138, 1172, 3220, 1204, 1172, 1562, 3250, 1563, 1562, 3252, 778, 655, 3252, 3227, 1562, 3227, 3228, 263, 1563, 1563, 100, 1563, 655,
   2150, 1563, 2122, 1563, 1563, 3099, 200, 2118, 228, 200, 3227, 655, 3227, 2126, 1179, 3259, 1211, 228, 3259, 1179, 0, 212, 2130, 212, 228,
   1172, 3220, 1172, 1204, 1563, 228, 1563, 100, 200, 2118, 200, 228, 3227, 2212, 3236, 2212, 2228, 2148, 210, 2148, 2162, 3239, 2162, 667, 204,
   2162, 3122, 3250, 3124, 3122, 3252, 2150, 2215, 3252, 3252, 1554, 1179, 3252, 2148, 2215, 2150, 2148, 2148, 1179, 1051, 2148, 2150, 647, 1179, 2150,
   1179, 200, 0, 2732, 3252, 2732, 3252, 2148, 3643, 2148, 3643, 3255, 204, 3259, 204, 3259, 212, 228, 0, 652, 2700, 684, 652, 3902, 2730,
   3903, 3902, 2732, 3866, 2735, 2732, 1172, 2724, 1179, 1172, 2715, 1172, 2715, 2716, 1823, 228, 100, 100, 2148, 3867, 2150, 2148, 2148, 3895, 2154,
   2148, 2130, 3887, 2130, 2132, 200, 2118, 228, 200, 2150, 2727, 2154, 2150, 2130, 1191, 2130, 2150, 204, 2122, 228, 204, 2130, 1179, 2130, 2138,
   228, 2130, 212, 212, 228, 0, 204, 2122, 204, 228, 212, 2130, 212, 228, 652, 2700, 684, 652, 3902, 2730, 3903, 3902, 2732, 3902, 2735,
   2732, 2212, 2724, 2220, 2212, 2732, 3886, 2878, 2732, 1823, 228, 100, 100, 2148, 3903, 2150, 2148, 2148, 3895, 2154, 2148, 2148, 3887, 2879, 2148,
   200, 2118, 228, 200, 2150, 2727, 2154, 2150, 2150, 1159, 2166, 2150, 2154, 667, 212, 2154, 3642, 3250, 3643, 3642, 3252, 199, 2735, 3252, 3252,
   3634, 3259, 3252, 2732, 3252, 3252, 2732, 1172, 3220, 1204, 1172, 3643, 198, 2150, 3643, 2148, 3259, 3131, 3131, 2148, 3643, 3643, 2148, 1563, 3611,
   1595, 1563, 3259, 2727, 3259, 200, 200, 0, 200, 2118, 228, 200, 212, 3239, 3240, 2862, 3239, 2863, 3631, 2863, 2875, 3239, 3247, 204, 3239,
   1159, 1191, 3207, 1159, 2732, 3252, 3252, 2732, 3642, 3250, 3643, 3642, 3252, 3634, 3259, 3252, 1172, 3220, 1204, 1172, 2148, 3643, 3643, 2148, 2343,
   3259, 3131, 3131, 1563, 3611, 1595, 1563, 200, 3259, 3259, 204, 1179, 3227, 1211, 1179, 216, 200, 2118, 228, 200, 204, 3259, 3259, 204, 1179,
   3227, 1211, 1179, 228, 0, 212, 2715, 1172, 2716, 2715, 2130, 1563, 2132, 2130, 1175, 2130, 1179, 2138, 2130, 652, 1172, 1172, 652, 1562, 1170,
   1563, 1562, 1172, 1822, 2719, 1172, 1172, 1554, 1179, 1172, 783, 1563, 1563, 100, 1563, 1823, 2134, 1563, 2148, 1179, 1051, 1051, 200, 2118, 216,
   200, 1179, 2711, 1179, 2134, 204, 1179, 1179, 204, 228, 0, 2130, 1172, 2700, 1172, 684, 1563, 228, 1563, 100, 200, 2118, 200, 228, 1179,
   2122, 1179, 228, 2732, 212, 2732, 667, 2148, 210, 2148, 82, 1159, 2154, 667, 2154, 212, 2862, 2730, 2863, 2862, 2732, 2858, 2735, 2732, 2212,
   2724, 2220, 2212, 2148, 2735, 2150, 2148, 2148, 2855, 2154, 2148, 2150, 2727, 2154, 2150, 200, 228, 200]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem proof19 : cases19.foldlM (fun rem next => certifies goal 6 next rem) data19 = some [] := by
  decide +kernel

def cases20 : List (List Sig) := ((successors inputs 7).drop 179).take 8

set_option maxRecDepth 12000 in
def data20 : List ℕ :=
  [0, 2150, 204, 0, 204, 2747, 212, 204, 204, 2122, 228, 204, 3252, 2724, 3259, 3252, 3382, 2730, 3383, 3382, 2727, 3382, 2727, 2728, 2732,
   3366, 2747, 2732, 652, 2700, 684, 652, 2148, 202, 2154, 2148, 3387, 3383, 3383, 3639, 2343, 3367, 2359, 2343, 1823, 3359, 1847, 1823, 200, 2727,
   204, 200, 2727, 1159, 2743, 2727, 655, 2703, 679, 655, 667, 2715, 699, 667, 204, 0, 3252, 2724, 3252, 3259, 2148, 202, 2148, 2154, 200,
   2727, 200, 204, 204, 2747, 212, 204, 204, 2122, 228, 204, 1822, 2730, 1823, 1822, 2732, 1818, 655, 2732, 2732, 1806, 2747, 2732, 652, 2700,
   684, 652, 3643, 1819, 1567, 3643, 783, 1807, 799, 783, 1823, 3611, 1595, 1823, 2747, 3239, 2747, 655, 655, 2703, 228, 655, 667, 2715, 699,
   667, 212, 0, 212, 2130, 228, 212, 2732, 3236, 2747, 2732, 2862, 3250, 2863, 2862, 3239, 2862, 3239, 3240, 3252, 2854, 3259, 3252, 1172, 3220,
   1204, 1172, 2148, 210, 2162, 2148, 2875, 2863, 2863, 3631, 2343, 2855, 2351, 2343, 1823, 2847, 1839, 1823, 200, 3239, 212, 200, 3239, 647, 3247,
   3239, 1175, 3223, 1191, 1175, 204, 2747, 212, 204, 1179, 3227, 1211, 1179, 212, 0, 2732, 3236, 2732, 2747, 2148, 210, 2148, 2162, 200, 3239,
   200, 212, 204, 2747, 204, 212, 212, 2130, 228, 212, 1822, 3250, 1823, 1822, 3252, 1818, 1175, 3252, 3252, 1814, 3259, 3252, 1172, 3220, 1204,
   1172, 3643, 1819, 1567, 3643, 1303, 1815, 1311, 1303, 1823, 3611, 1595, 1823, 3259, 2727, 3259, 1175, 1175, 3223, 228, 1175, 1179, 3227, 1211, 1179,
   0, 652, 2700, 652, 684, 1823, 228, 100, 100, 2118, 204, 2122, 204, 228, 212, 2130, 212, 228, 3642, 2730, 3643, 3642, 2732, 199, 655,
   2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 2148, 198, 70, 2148, 2148, 3259, 2154, 2148, 2148, 2747, 2162, 2148, 2154, 647, 2154, 200,
   2162, 1159, 2162, 200, 2154, 2747, 2162, 2154, 2732, 3902, 3902, 2732, 3902, 2730, 3903, 3902, 2732, 3902, 3902, 2732, 3382, 3894, 3390, 3382, 2862,
   3886, 2878, 2862, 652, 3902, 3902, 652, 2148, 3903, 3903, 2148, 2148, 3903, 3903, 2148, 3383, 3895, 3391, 3383, 2863, 3887, 2879, 2863, 1823, 3903,
   3903, 100, 200, 647, 204, 200, 200, 1159, 212, 200, 2118, 228, 200, 204, 2747, 212, 204, 204, 2122, 228, 204, 212, 2130, 228, 212,
   2118, 0, 652, 0, 684, 1823, 228, 100, 100, 228, 2118, 200, 200, 204, 2122, 204, 228, 212, 2130, 212, 228, 1823, 2148, 1823, 2148,
   652, 2118, 655, 2118, 1172, 2154, 1179, 2154, 652, 2162, 667, 2162, 2118, 1819, 2118, 2120, 2148, 202, 2154, 2148, 2148, 210, 2162, 2148, 2118,
   647, 2126, 2118, 2118, 1159, 2134, 2118, 2154, 667, 2162, 2154, 652, 2700, 228, 2732, 684, 0, 652, 100, 100, 228, 0, 70, 1819, 70,
   72, 74, 1815, 74, 100, 82, 1807, 82, 100, 1822, 650, 1823, 1822, 655, 1818, 655, 656, 1179, 676, 1179, 1204, 667, 1188, 667, 684,
   1175, 647, 1179, 1175, 655, 1159, 667, 655, 74, 667, 155, 155, 200, 228, 204, 2122, 204, 228, 212, 2130, 212, 1822, 682, 1823, 1822,
   655, 1822, 655, 656, 1179, 204, 1179, 204, 667, 212, 667, 212, 2118, 1819, 2118, 2120, 74, 202, 74, 76, 82, 210, 82, 84, 204,
   647, 204, 2118, 212, 1159, 212, 2118, 204, 667, 212, 204, 2732, 652, 228, 652, 1822, 1823, 1822, 2730, 2148, 2732, 1823, 1823, 2732, 1822,
   2148, 1822, 2703, 2703, 2732, 1822, 2118, 1822, 2703, 2703, 1822, 2704, 2118, 2732, 3252, 3259, 3252, 2724, 2154, 2732, 3259, 3259, 2732, 3252, 2154,
   3252, 2732, 2747, 2732, 3236, 2162, 3252, 2747, 2747, 3252, 2732, 2162, 2732, 1563, 0, 100, 228, 2703, 200, 200, 204, 3227, 204, 228, 212,
   2715, 212, 228, 652, 2700, 684, 652, 1822, 2732, 2732, 1822, 2703, 1818, 2703, 2704, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 70, 2703,
   70, 2703, 74, 3259, 74, 3259, 82, 2747, 82, 2747, 3223, 2695, 3231, 3223, 2703, 3207, 2719, 2703, 204, 2747, 2235, 2235, 1563, 228, 228,
   2148, 100, 0, 684, 652, 2700, 652, 1563, 200, 228, 204, 74, 204, 228, 212, 82, 212, 1822, 652, 652, 1822, 652, 1818, 2703, 652,
   1172, 204, 1179, 1172, 652, 212, 667, 652, 70, 1823, 70, 72, 74, 204, 74, 204, 82, 212, 82, 212, 204, 2695, 204, 70, 212,
   3207, 212, 70, 204, 667, 212, 204, 2148, 100, 228, 1563, 2118, 2118, 2148, 1823, 2703, 1823, 2118, 2118, 1823, 2120, 2703, 2148, 2148, 2154,
   2148, 1815, 3259, 1823, 2154, 2154, 1823, 2148, 3259, 2148, 2148, 2162, 2148, 1807, 2747, 1823, 2162, 2162, 1823, 2148, 2747, 2148, 200, 0, 652,
   2700, 652, 684, 1823, 228, 100, 100, 2118, 204, 2122, 204, 228, 212, 2130, 212, 228, 3642, 2730, 3643, 3642, 2732, 199, 655, 2732, 3252,
   2724, 3259, 3252, 2732, 3236, 2747, 2732, 2148, 198, 70, 2148, 2148, 3259, 2154, 2148, 2148, 2747, 2162, 2148, 2154, 647, 2154, 200, 2162, 1159,
   2162, 200, 2154, 2747, 2162, 2154, 0, 228, 2703, 2704, 1822, 2703, 2118, 2120, 1823, 2118, 2118, 2126, 2695, 2118, 2118, 2134, 3207, 2118, 652,
   2732, 2732, 652, 3642, 2730, 3643, 3642, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 70, 2148, 2148, 72, 2148, 3259, 2154, 2148, 2148, 2747,
   2162, 2148, 200, 2154, 2154, 204, 2154, 2747, 2162, 2154, 200, 2162, 2162, 212, 2118, 2154, 2118, 2695, 0, 204, 2122, 228, 204, 2154, 2747,
   2162, 2154, 3252, 2724, 3259, 3252, 652, 2700, 684, 652, 1302, 2730, 1303, 1302, 2695, 1302, 2695, 2696, 2732, 1286, 2747, 2732, 2148, 1303, 2154,
   2148, 1563, 1303, 1303, 1563, 1339, 1303, 1303, 3607, 263, 1287, 279, 263, 2118, 647, 2695, 0, 667, 2695, 647, 647, 2154, 2695, 2118, 2118,
   1179, 3207, 1159, 1159, 2695, 262, 2695, 2696, 3207, 262, 3207, 3208, 282, 262, 262, 1542, 262, 3250, 263, 262, 2148, 263, 263, 2567, 2148,
   263, 263, 3079, 283, 263, 263, 1543, 2711, 2695, 667, 2715, 699, 667, 2703, 2126, 2154, 2703, 2118, 0, 204, 2122, 228, 204, 3252, 2724,
   3252, 3259, 2148, 3259, 2148, 2154, 2695, 2154, 2747, 2162, 2154, 652, 2700, 684, 652, 3642, 2730, 3643, 3642, 2732, 1302, 3223, 2732, 2732, 3626,
   2747, 2732, 1563, 3611, 1595, 1563, 3643, 1303, 2118, 3643, 2148, 2747, 2619, 2619, 200, 2747, 3207, 2747, 2118, 667, 2715, 699, 667, 2118, 2118,
   2162, 2118, 3207, 0, 212, 2130, 228, 212, 2732, 3236, 2747, 2732, 1172, 3220, 1204, 1172, 782, 3250, 783, 782, 3207, 782, 3207, 3208, 3252,
   774, 3259, 3252, 2148, 783, 2162, 2148, 1563, 783, 783, 1563, 827, 783, 783, 3599, 263, 775, 271, 263, 2118, 1159, 3207, 0, 2154, 2695,
   2118, 2118, 1179, 3207, 1159, 1159, 667, 2695, 647, 647, 3207, 262, 3207, 3208, 2695, 262, 2695, 2696, 282, 262, 262, 1542, 262, 2730, 263,
   262, 2148, 263, 263, 3079, 2148, 263, 263, 2567, 283, 263, 263, 1543, 3215, 3207, 2154, 2747, 2162, 2154, 1179, 3227, 1211, 1179, 3223, 2134,
   2162, 3223, 2118, 0, 212, 2130, 228, 212, 2732, 3236, 2732, 2747, 2148, 2747, 2148, 2162, 3207, 2154, 2747, 2154, 2162, 1172, 3220, 1204, 1172,
   3642, 3250, 3643, 3642, 3252, 782, 2703, 3252, 3252, 3634, 3259, 3252, 1563, 3611, 1595, 1563, 3643, 783, 2118, 3643, 2148, 3259, 3131, 3131, 200,
   3259, 2695, 3259, 2118, 1179, 3227, 1211, 1179, 2118, 204, 228, 204, 2122, 0, 1172, 652, 652, 1172, 1822, 650, 1823, 1822, 652, 1818, 655,
   652, 3227, 652, 3227, 3228, 652, 3236, 667, 652, 0, 70, 1819, 70, 72, 74, 1815, 74, 76, 82, 1807, 82, 100, 1822, 650, 1823,
   1822, 652, 1818, 655, 652, 3227, 652, 3227, 3228, 652, 3236, 667, 652, 3223, 647, 3227, 3223, 655, 3207, 667, 655, 74, 667, 2203, 667,
   228, 100, 100, 2118, 1819, 2118, 2120, 2122, 1815, 2122, 2124, 2148, 1807, 2162, 2148, 200, 2118, 647, 2122, 2118, 2118, 3207, 2134, 2118, 204,
   2122, 667, 2138, 2122, 212, 2130, 228, 212, 2154, 228, 228, 2154, 204, 0, 652, 3220, 652, 1204, 1823, 228, 100, 100, 228, 2118, 200,
   200, 2122, 212, 2130, 212, 228, 1302, 3250, 1303, 1302, 3223, 1302, 3223, 3224, 3252, 204, 1179, 3252, 2212, 3236, 2228, 2212, 2118, 1303, 2118,
   2120, 2148, 202, 74, 2148, 2148, 1287, 2162, 2148, 2118, 655, 204, 2118, 2118, 3207, 2134, 2118, 2162, 667, 2162, 204, 204, 2154, 2162, 2154,
   2747, 2747, 3259, 2162, 2162, 3259, 2154, 2747, 2154, 212, 228, 212, 2130, 0, 652, 2700, 684, 652, 1822, 2730, 1823, 1822, 2703, 1818, 2703,
   2704, 1172, 2724, 1179, 1172, 2715, 1172, 2715, 2716, 0, 70, 1819, 70, 72, 74, 1815, 74, 100, 82, 1807, 82, 84, 1822, 2698, 1823,
   1822, 2703, 1818, 2703, 2704, 1172, 2724, 1179, 1172, 2715, 1172, 2715, 2716, 1175, 2695, 1179, 1175, 2703, 1159, 2715, 2703, 74, 1179, 1179, 2203,
   228, 100, 100, 2118, 1819, 2118, 2120, 2148, 1815, 2154, 2148, 2130, 1807, 2130, 2132, 200, 2118, 2695, 2126, 2118, 2118, 1159, 2130, 2118, 204,
   2122, 228, 204, 2130, 1179, 2130, 2138, 212, 2162, 228, 228, 2162, 212, 0, 652, 2700, 652, 684, 1823, 228, 100, 100, 228, 2118, 200,
   200, 204, 2122, 204, 228, 2130, 782, 2730, 783, 782, 2703, 782, 2703, 2704, 2212, 2724, 2220, 2212, 2732, 212, 667, 2732, 2118, 783, 2118,
   2120, 2148, 775, 2154, 2148, 2148, 210, 82, 2148, 2118, 2695, 2126, 2118, 2118, 1175, 212, 2118, 2154, 667, 212, 2154, 212, 2150, 0, 652,
   2732, 2732, 652, 3902, 2730, 3903, 3902, 2732, 3898, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 1822, 2732, 2732, 1822, 1563, 2148,
   2148, 1563, 2148, 3899, 2150, 2148, 2148, 3895, 2154, 2148, 2148, 3887, 2162, 2148, 1823, 2148, 2148, 1823, 200, 2150, 2727, 2154, 2150, 2150, 3239,
   2162, 2150, 2118, 2150, 0, 228, 2703, 2704, 1822, 2703, 2118, 2120, 1823, 2118, 2118, 2126, 2695, 2118, 2118, 2134, 3207, 2118, 652, 2732, 2732,
   652, 3642, 2730, 3643, 3642, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 70, 2148, 2148, 72, 2148, 3259, 2154, 2148, 2148, 2747, 2162, 2148,
   200, 2154, 2154, 204, 2154, 2747, 2162, 2154, 200, 2162, 2162, 212, 204, 2154, 2154, 204, 2154, 2747, 2162, 2154, 204, 2154, 2154, 204, 212,
   2162, 2162, 212, 212, 2162, 2162, 212, 228, 228, 228, 2150]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem proof20 : cases20.foldlM (fun rem next => certifies goal 6 next rem) data20 = some [] := by
  decide +kernel

def cases21 : List (List Sig) := ((successors inputs 7).drop 187).take 8

set_option maxRecDepth 12000 in
def data21 : List ℕ :=
  [0, 2732, 1822, 2732, 1822, 2148, 1823, 2148, 1823, 200, 204, 0, 204, 2747, 212, 204, 204, 2122, 228, 204, 3252, 2724, 3259, 3252, 3902,
   2730, 3903, 3902, 2732, 3898, 2735, 2732, 2732, 3886, 2747, 2732, 652, 2700, 684, 652, 2148, 202, 2154, 2148, 3643, 3899, 3647, 3643, 2863, 3887,
   2879, 2863, 1303, 3863, 1343, 1303, 204, 2727, 200, 200, 2735, 3239, 2747, 2735, 647, 2695, 687, 647, 667, 2715, 699, 667, 204, 0, 204,
   2747, 212, 204, 204, 2122, 228, 204, 3252, 2724, 3259, 3252, 3902, 2730, 3903, 3902, 2732, 3898, 2735, 2732, 2732, 3886, 2747, 2732, 652, 2700,
   684, 652, 2148, 202, 2154, 2148, 3643, 3899, 3647, 3643, 2863, 3887, 2879, 2863, 1563, 3903, 3903, 1563, 200, 2727, 204, 200, 2735, 3239, 2747,
   2735, 200, 2735, 687, 687, 667, 2715, 699, 667, 212, 0, 212, 2130, 228, 212, 2732, 3236, 2747, 2732, 3902, 3250, 3903, 3902, 3252, 3898,
   3255, 3252, 3252, 3894, 3259, 3252, 1172, 3220, 1204, 1172, 2148, 210, 2162, 2148, 3643, 3899, 3647, 3643, 3383, 3895, 3391, 3383, 783, 3855, 831,
   783, 212, 3239, 200, 200, 3255, 2727, 3259, 3255, 1159, 3207, 1207, 1159, 204, 2747, 212, 204, 1179, 3227, 1211, 1179, 212, 0, 212, 2130,
   228, 212, 2732, 3236, 2747, 2732, 3902, 3250, 3903, 3902, 3252, 3898, 3255, 3252, 3252, 3894, 3259, 3252, 1172, 3220, 1204, 1172, 2148, 210, 2162,
   2148, 3643, 3899, 3647, 3643, 3383, 3895, 3391, 3383, 1563, 3903, 3903, 1563, 200, 3239, 212, 200, 3255, 2727, 3259, 3255, 200, 3255, 1207, 1207,
   204, 2747, 212, 204, 1179, 3227, 1211, 1179, 0, 652, 2700, 684, 652, 1822, 2730, 1823, 1822, 2703, 1822, 2703, 2704, 3252, 2724, 3259, 3252,
   2732, 3236, 2747, 2732, 1563, 228, 100, 100, 2118, 1823, 2118, 2120, 2148, 1815, 2154, 2148, 2148, 1807, 2162, 2148, 200, 2118, 2695, 2126, 2118,
   2118, 3207, 2134, 2118, 204, 2122, 228, 204, 2154, 2747, 2162, 2154, 212, 2130, 228, 212, 1822, 2730, 1823, 1822, 2732, 1822, 1822, 2732, 1302,
   1814, 1310, 1302, 782, 1806, 798, 782, 1822, 2700, 684, 1822, 2148, 1823, 1823, 2148, 1303, 1815, 1311, 1303, 783, 1807, 799, 783, 1823, 228,
   100, 1823, 204, 2727, 204, 2150, 212, 3239, 212, 2150, 228, 2150, 232, 204, 2747, 212, 204, 204, 2122, 228, 204, 212, 2130, 228, 212,
   200, 0, 652, 652, 0, 684, 1823, 228, 100, 100, 2118, 204, 2122, 204, 228, 212, 2130, 212, 228, 1822, 2148, 1823, 2148, 652, 199,
   655, 652, 1172, 2154, 1179, 2154, 652, 2162, 667, 2162, 2148, 198, 70, 2148, 2148, 202, 2154, 2148, 2148, 210, 2162, 2148, 2154, 647, 2154,
   200, 2162, 1159, 2162, 200, 2154, 667, 2162, 2154, 2700, 2732, 228, 652, 652, 228, 684, 2732, 0, 652, 100, 100, 228, 0, 1822, 650,
   1822, 1823, 70, 1819, 70, 100, 74, 1815, 74, 100, 82, 1807, 82, 100, 655, 1818, 655, 684, 1179, 676, 1179, 1204, 667, 1188, 667,
   684, 1175, 647, 1179, 1175, 655, 1159, 667, 655, 74, 667, 155, 155, 228, 200, 2118, 200, 228, 204, 2122, 204, 228, 212, 2130, 212,
   1823, 682, 1823, 1594, 655, 200, 655, 200, 1179, 204, 1179, 204, 667, 212, 667, 212, 70, 198, 70, 72, 74, 202, 74, 76, 82,
   210, 82, 84, 200, 647, 204, 200, 200, 1159, 212, 200, 204, 667, 212, 204, 1823, 1823, 0, 652, 2700, 652, 684, 100, 2703, 204,
   3227, 204, 228, 212, 2715, 212, 228, 1822, 2732, 2732, 1822, 2732, 199, 655, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 70, 198,
   70, 72, 74, 3259, 74, 3259, 82, 2747, 82, 2747, 3259, 647, 3259, 200, 2747, 1159, 2747, 200, 204, 2747, 2235, 2235, 228, 2148, 228,
   100, 1823, 228, 100, 2148, 0, 1823, 228, 200, 70, 200, 228, 204, 74, 204, 228, 212, 82, 212, 684, 652, 652, 2700, 1822, 652,
   652, 1822, 652, 199, 655, 652, 1172, 204, 1179, 1172, 652, 212, 667, 652, 70, 200, 70, 200, 74, 204, 74, 204, 82, 212, 82,
   212, 200, 647, 204, 200, 200, 1159, 212, 200, 204, 667, 212, 204, 2118, 0, 228, 2703, 2704, 1822, 2703, 2118, 2120, 1823, 2118, 2118,
   2126, 2695, 2118, 2118, 2134, 3207, 2118, 652, 2732, 2732, 652, 3642, 2730, 3643, 3642, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 70, 2148,
   2148, 72, 2148, 3259, 2154, 2148, 2148, 2747, 2162, 2148, 200, 2154, 2154, 204, 2154, 2747, 2162, 2154, 200, 2162, 2162, 212, 0, 652, 2700,
   684, 652, 1822, 2730, 1823, 1822, 2703, 1822, 2703, 2704, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 1563, 228, 100, 100, 2118, 1823, 2118,
   2120, 2148, 1815, 2154, 2148, 2148, 1807, 2162, 2148, 200, 2118, 2695, 2126, 2118, 2118, 3207, 2134, 2118, 204, 2122, 228, 204, 2154, 2747, 2162,
   2154, 212, 2130, 228, 212, 204, 204, 228, 2122, 2154, 0, 212, 2130, 212, 228, 1172, 652, 652, 1172, 1822, 650, 1823, 1822, 652, 1818,
   655, 652, 3227, 652, 3227, 3228, 652, 3236, 667, 652, 1303, 228, 100, 100, 2148, 1819, 1567, 2148, 2122, 1823, 2122, 2124, 2148, 1807, 2162,
   2148, 200, 2118, 228, 200, 2122, 655, 2122, 2126, 2162, 1159, 2162, 655, 204, 2122, 667, 2138, 2122, 204, 204, 0, 652, 3220, 652, 1204,
   1823, 228, 100, 100, 2118, 2122, 212, 2130, 212, 228, 3122, 3250, 3124, 3122, 3252, 199, 655, 3252, 3252, 204, 1179, 3252, 2212, 3236, 2228,
   2212, 2148, 198, 70, 2148, 2148, 202, 74, 2148, 2148, 210, 2162, 2148, 200, 647, 204, 200, 2162, 1159, 2162, 200, 2162, 667, 2162, 204,
   228, 2154, 228, 212, 212, 228, 2130, 2162, 0, 652, 2700, 684, 652, 1822, 2730, 1823, 1822, 2732, 1818, 1175, 2732, 1172, 2724, 1179, 1172,
   2715, 1172, 2715, 2716, 783, 228, 100, 100, 2148, 1819, 1567, 2148, 2148, 1815, 2154, 2148, 2130, 1823, 2130, 2132, 200, 2118, 228, 200, 2154,
   647, 2154, 1175, 2130, 1175, 2130, 2134, 204, 2122, 228, 204, 2130, 1179, 2130, 2138, 212, 212, 212, 0, 652, 2700, 652, 684, 1823, 228,
   100, 100, 2118, 204, 2122, 204, 228, 2130, 2602, 2730, 2604, 2602, 2732, 199, 655, 2732, 2212, 2724, 2220, 2212, 2732, 212, 667, 2732, 2148,
   198, 70, 2148, 2148, 202, 2154, 2148, 2148, 210, 82, 2148, 2154, 647, 2154, 200, 200, 1159, 212, 200, 2154, 667, 212, 2154, 228, 2162,
   228, 3642, 3643, 3642, 2730, 2148, 2732, 3643, 3643, 2732, 3642, 2148, 3642, 2732, 655, 2732, 199, 200, 1822, 655, 655, 1822, 2732, 200, 2732,
   3252, 3259, 3252, 2724, 2154, 2732, 3259, 3259, 2732, 3252, 2154, 3252, 2732, 2747, 2732, 3236, 2162, 3252, 2747, 2747, 3252, 2732, 2162, 2732, 2148,
   70, 2148, 198, 200, 1823, 70, 70, 1823, 2148, 200, 2148, 2148, 2154, 2148, 3259, 3259, 3643, 2154, 2154, 3643, 2148, 3259, 2148, 2148, 2162,
   2148, 2747, 2747, 3643, 2162, 2162, 3643, 2148, 2747, 2148, 2154, 2154, 200, 647, 0, 2154, 2747, 2162, 2154, 204, 2122, 204, 228, 652, 2700,
   652, 684, 1303, 3611, 1303, 1595, 2695, 667, 2715, 667, 699, 3252, 2724, 3259, 3252, 3642, 2730, 3643, 3642, 2732, 1302, 647, 2732, 2732, 3626,
   2747, 2732, 2148, 3259, 2154, 2148, 3643, 1303, 1303, 3643, 263, 2747, 2619, 2619, 200, 2747, 0, 2154, 2747, 2162, 2154, 647, 2695, 647, 699,
   1159, 3207, 1159, 1211, 262, 3590, 262, 314, 263, 3591, 263, 315, 2732, 3626, 2747, 2732, 3252, 3634, 3259, 3252, 3642, 3250, 3643, 3642, 2148,
   2747, 2619, 2619, 2148, 3259, 3131, 3131, 2747, 647, 655, 2154, 2154, 655, 200, 0, 204, 2122, 228, 204, 3252, 2724, 3252, 3259, 2148, 3259,
   2148, 2154, 647, 2154, 2747, 2162, 2154, 652, 2700, 652, 684, 1563, 3611, 1563, 1595, 2118, 667, 2715, 667, 699, 3642, 2730, 3643, 3642, 2732,
   199, 1175, 2732, 2732, 3626, 2747, 2732, 3643, 198, 70, 3643, 2148, 2747, 2619, 2619, 2747, 1159, 2747, 200, 200, 2162, 2162, 200, 1159, 0,
   212, 2130, 212, 228, 1172, 3220, 1172, 1204, 783, 3611, 783, 1595, 3207, 1179, 3227, 1179, 1211, 2732, 3236, 2747, 2732, 3642, 3250, 3643, 3642,
   3252, 782, 1159, 3252, 3252, 3634, 3259, 3252, 2148, 2747, 2162, 2148, 3643, 783, 783, 3643, 263, 3259, 3131, 3131, 200, 3259, 0, 2154, 2747,
   2162, 2154, 1159, 3207, 1159, 1211, 647, 2695, 647, 699, 262, 3590, 262, 314, 263, 3591, 263, 315, 3252, 3634, 3259, 3252, 2732, 3626, 2747,
   2732, 3642, 2730, 3643, 3642, 2148, 3259, 3131, 3131, 2148, 2747, 2619, 2619, 3259, 1159, 2154, 2747, 2162, 2154, 1175, 2162, 2162, 1175, 200, 0,
   212, 2130, 228, 212, 2732, 3236, 2732, 2747, 2148, 2747, 2148, 2162, 1159, 2154, 2747, 2154, 2162, 1172, 3220, 1172, 1204, 1563, 3611, 1563, 1595,
   2118, 1179, 3227, 1179, 1211, 3642, 3250, 3643, 3642, 3252, 199, 655, 3252, 3252, 3634, 3259, 3252, 3643, 198, 70, 3643, 2148, 3259, 3131, 3131,
   3259, 647, 3259, 200, 200, 2154, 2162, 2154, 2747, 2747, 3259, 2162, 2162, 3259, 2154, 2747, 2154, 200, 0, 652, 2732, 652, 2732, 3903, 2148,
   3903, 2148, 2150, 204, 2154, 204, 2154, 212, 2162, 212, 2162, 228, 3642, 2730, 3643, 3642, 2732, 199, 655, 2732, 3252, 2724, 3259, 3252, 2732,
   3236, 2747, 2732, 652, 2732, 2732, 652, 2148, 198, 70, 2148, 2148, 3259, 2154, 2148, 2148, 2747, 2162, 2148, 1823, 2148, 2148, 1823, 2154, 647,
   2154, 200, 2162, 1159, 2162, 200, 200, 0, 228, 2703, 2704, 1822, 2703, 2118, 2120, 1823, 2118, 2118, 2126, 2695, 2118, 2118, 2134, 3207, 2118,
   652, 2732, 2732, 652, 3642, 2730, 3643, 3642, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 70, 2148, 2148, 72, 2148, 3259, 2154, 2148, 2148,
   2747, 2162, 2148, 200, 2154, 2154, 204, 2154, 2747, 2162, 2154, 200, 2162, 2162, 212, 232, 2154, 2747, 2162, 2154, 204, 2154, 2154, 204, 212,
   2162, 2162, 212, 204, 212, 204]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem proof21 : cases21.foldlM (fun rem next => certifies goal 6 next rem) data21 = some [] := by
  decide +kernel

def cases22 : List (List Sig) := ((successors inputs 7).drop 195).take 18

set_option maxRecDepth 12000 in
def data22 : List ℕ :=
  [0, 3259, 2747, 228, 0, 652, 2700, 684, 652, 1822, 2730, 1823, 1822, 2732, 1818, 2735, 2732, 3227, 2724, 3227, 3228, 2715, 3236, 2715, 2716,
   783, 228, 100, 100, 2148, 1819, 2150, 2148, 2148, 1823, 2154, 2148, 2148, 1823, 2162, 2148, 200, 2118, 228, 200, 2150, 2727, 2154, 2150, 2150,
   3239, 2162, 2150, 204, 2122, 228, 204, 2154, 2715, 2138, 2138, 212, 2130, 228, 212, 228, 0, 652, 2700, 652, 684, 1823, 228, 100, 100,
   200, 2118, 200, 228, 204, 2122, 204, 228, 212, 2130, 212, 228, 2862, 2730, 2863, 2862, 2732, 2858, 2735, 2732, 3252, 2724, 2220, 3252, 2732,
   3236, 2228, 2732, 2148, 2735, 2150, 2148, 2148, 2855, 2154, 2148, 2148, 3367, 2162, 2148, 2150, 2727, 2154, 2150, 2150, 3239, 2162, 2150, 2154, 667,
   2162, 2154, 2732, 3902, 3902, 2732, 3902, 2730, 3903, 3902, 3642, 3898, 3646, 3642, 3252, 3902, 3902, 3252, 2732, 3902, 3902, 2732, 1822, 3870, 1854,
   1822, 2148, 3903, 3903, 2148, 3643, 3899, 3647, 3643, 2148, 3903, 3903, 2148, 2148, 3903, 3903, 2148, 1823, 3871, 1855, 1823, 200, 0, 200, 3239,
   212, 200, 200, 2118, 228, 200, 2732, 199, 2735, 2732, 3642, 2730, 3643, 3642, 3382, 3638, 3386, 3382, 2862, 3630, 2874, 2862, 1562, 3610, 1594,
   1562, 2148, 198, 2150, 2148, 3383, 3639, 3387, 3383, 2863, 3631, 2875, 2863, 1563, 3611, 1595, 1563, 200, 2727, 200, 204, 204, 0, 204, 2122,
   228, 204, 200, 2727, 204, 200, 655, 2703, 687, 655, 2342, 2854, 2350, 2342, 2732, 2858, 2735, 2732, 2862, 2730, 2863, 2862, 782, 2830, 814,
   782, 2343, 2855, 2351, 2343, 2148, 2735, 2607, 2607, 783, 2831, 815, 783, 212, 204, 204, 2122, 228, 204, 212, 2130, 228, 212, 0, 2732,
   199, 2732, 2735, 2148, 198, 2148, 2150, 200, 2727, 204, 200, 200, 3239, 212, 200, 200, 2118, 228, 200, 2862, 2730, 2863, 2862, 3382, 2854,
   2350, 3382, 2862, 3366, 2358, 2862, 782, 2830, 814, 782, 3383, 2855, 2351, 3383, 2863, 3367, 2359, 2863, 783, 2831, 815, 783, 204, 2747, 212,
   204, 204, 2122, 228, 204, 212, 2130, 228, 212, 200, 200, 2727, 204, 200, 200, 3239, 212, 200, 200, 2118, 228, 200, 0, 204, 2122,
   228, 204, 220, 667, 2715, 699, 667, 2212, 3902, 3902, 2212, 2732, 3886, 2747, 2732, 3902, 2730, 3903, 3902, 3642, 3898, 3646, 3642, 1822, 3870,
   1854, 1822, 2148, 3903, 3903, 2148, 2863, 3887, 2879, 2863, 3643, 3899, 3647, 3643, 1823, 3871, 1855, 1823, 200, 2727, 204, 200, 2735, 0, 200,
   2727, 204, 200, 655, 2703, 687, 655, 204, 2122, 228, 204, 2732, 2858, 2735, 2732, 2342, 2854, 2350, 2342, 2862, 2730, 2863, 2862, 782, 2830,
   814, 782, 2148, 2735, 2607, 2607, 2343, 2855, 2351, 2343, 783, 2831, 815, 783, 2747, 2735, 655, 2703, 687, 655, 212, 204, 204, 2122, 228,
   204, 212, 2130, 228, 212, 2747, 2747, 3259, 0, 228, 0, 262, 652, 652, 164, 1822, 650, 1823, 1822, 652, 1818, 655, 652, 1172, 652,
   1179, 1172, 652, 1172, 667, 652, 263, 228, 100, 100, 2148, 1819, 2150, 2148, 2122, 1815, 2122, 2124, 2130, 1807, 2130, 2132, 200, 2118, 228,
   200, 2122, 655, 2122, 2126, 2130, 1175, 2130, 2134, 204, 2122, 667, 2130, 2122, 212, 228, 0, 652, 228, 652, 164, 1823, 228, 100, 100,
   200, 2118, 200, 228, 2122, 2130, 2342, 2148, 2343, 2342, 2212, 2150, 2215, 2212, 2212, 204, 1179, 2212, 2212, 212, 667, 2212, 2148, 2215, 2150,
   2148, 2148, 202, 74, 2148, 2148, 210, 82, 2148, 2150, 647, 204, 2150, 2150, 1159, 212, 2150, 204, 667, 212, 204, 2212, 2732, 2732, 2212,
   3902, 2730, 3903, 3902, 2732, 3898, 2735, 2732, 3252, 2732, 3259, 3252, 2732, 3252, 2747, 2732, 652, 2700, 684, 652, 2148, 3903, 3903, 2148, 3643,
   3899, 3647, 3643, 3383, 3895, 3391, 3383, 2863, 3887, 2879, 2863, 1823, 3871, 1855, 1823, 200, 2735, 2735, 200, 3255, 2735, 3259, 3255, 2735, 3255,
   2747, 2735, 655, 2703, 687, 655, 204, 0, 220, 667, 2715, 699, 667, 204, 2122, 228, 204, 2732, 3886, 2747, 2732, 2212, 3902, 3902, 2212,
   3902, 2730, 3903, 3902, 3642, 3898, 3646, 3642, 1822, 3870, 1854, 1822, 2863, 3887, 2879, 2863, 2148, 3903, 3903, 2148, 3643, 3899, 3647, 3643, 1823,
   3871, 1855, 1823, 2735, 0, 200, 2727, 204, 200, 655, 2703, 687, 655, 204, 2122, 228, 204, 2732, 2858, 2735, 2732, 2342, 2854, 2350, 2342,
   2862, 2730, 2863, 2862, 782, 2830, 814, 782, 2148, 2735, 2607, 2607, 2343, 2855, 2351, 2343, 783, 2831, 815, 783, 2747, 2735, 200, 2727, 204,
   200, 655, 2703, 687, 655, 3259, 2747, 1179, 3227, 1211, 1179, 212, 667, 2715, 699, 667, 212, 212, 3259, 0, 3252, 2732, 3252, 2732, 2148,
   2863, 2148, 2863, 200, 2735, 200, 2735, 204, 2747, 228, 0, 1172, 652, 652, 1172, 3902, 650, 3903, 3902, 652, 3898, 655, 652, 3252, 652,
   3259, 3252, 652, 3236, 699, 652, 1823, 228, 100, 100, 2148, 3899, 2150, 2148, 2122, 3895, 2122, 2124, 2148, 3855, 2162, 2148, 200, 2118, 228,
   200, 2122, 655, 2122, 2126, 2150, 3239, 2162, 2150, 228, 2122, 204, 204, 2122, 699, 2162, 2122, 212, 2130, 228, 212, 228, 0, 652, 3220,
   1204, 652, 3902, 3250, 3903, 3902, 3252, 3898, 3255, 3252, 3252, 3894, 3259, 3252, 2212, 3236, 2228, 2212, 1823, 228, 100, 100, 2148, 3899, 2150,
   2148, 2148, 3895, 3391, 2148, 2148, 3903, 2162, 2148, 200, 2118, 228, 200, 2150, 647, 3259, 2150, 2150, 3239, 2162, 2150, 204, 2122, 228, 204,
   2162, 3259, 2162, 2170, 212, 2130, 228, 212, 2862, 2730, 2863, 2862, 2732, 2858, 2735, 2732, 3252, 2732, 2732, 3252, 2732, 3236, 2228, 2732, 652,
   2700, 684, 652, 2148, 2735, 2607, 2607, 2148, 2863, 2863, 2148, 2863, 210, 2162, 2863, 783, 2831, 815, 783, 200, 2735, 2735, 200, 2735, 3239,
   212, 2735, 655, 2703, 687, 655, 212, 3259, 220, 228, 3227, 228, 1179, 212, 2130, 228, 212, 204, 2747, 204, 0, 2732, 3252, 2732, 3252,
   2148, 3383, 2148, 3383, 200, 3255, 200, 3255, 3259, 212, 228, 0, 652, 2700, 684, 652, 3902, 2730, 3903, 3902, 2732, 3898, 2735, 2732, 1172,
   2724, 1211, 1172, 2732, 1172, 2747, 2732, 1823, 228, 100, 100, 2148, 3899, 2150, 2148, 2148, 3863, 2154, 2148, 2130, 3887, 2130, 2132, 200, 2118,
   228, 200, 2150, 2727, 2154, 2150, 2130, 1175, 2130, 2134, 204, 2122, 228, 204, 2130, 1211, 2130, 2154, 228, 2130, 212, 212, 228, 0, 212,
   2130, 212, 228, 652, 2700, 684, 652, 3902, 2730, 3903, 3902, 2732, 3898, 2735, 2732, 2212, 2724, 2220, 2212, 2732, 3886, 2747, 2732, 1823, 228,
   100, 100, 2148, 3899, 2150, 2148, 2148, 3903, 2154, 2148, 2148, 3887, 2879, 2148, 200, 2118, 228, 200, 2150, 2727, 2154, 2150, 2150, 1159, 2747,
   2150, 204, 2122, 228, 204, 2154, 2747, 2170, 2154, 3382, 3250, 3383, 3382, 3252, 3378, 3255, 3252, 3252, 2724, 2220, 3252, 2732, 3252, 3252, 2732,
   1172, 3220, 1204, 1172, 2148, 3255, 3127, 3127, 3383, 202, 2154, 3383, 2148, 3383, 3383, 2148, 1303, 3351, 1335, 1303, 3255, 2727, 204, 3255, 200,
   3255, 3255, 200, 1175, 3223, 1207, 1175, 204, 2747, 220, 204, 2122, 228, 204, 228, 2715, 228, 667, 204, 228, 204, 0, 2154, 212, 2747,
   212, 2747, 0, 652, 3220, 652, 1204, 1823, 228, 100, 100, 200, 2118, 200, 228, 2122, 212, 2130, 212, 228, 3382, 3250, 3383, 3382, 3252,
   3378, 3255, 3252, 3252, 204, 1179, 3252, 2212, 3236, 2228, 2212, 2148, 3255, 2150, 2148, 2148, 202, 74, 2148, 2148, 3367, 2162, 2148, 2150, 647,
   204, 2150, 2150, 3239, 2162, 2150, 2162, 667, 2162, 204, 652, 2732, 2732, 652, 3902, 2730, 3903, 3902, 2732, 3898, 2735, 2732, 3252, 2732, 2732,
   3252, 2732, 3886, 2747, 2732, 652, 2732, 2732, 652, 2148, 3903, 3903, 2148, 3643, 3899, 3647, 3643, 2148, 3903, 3903, 2148, 2863, 3887, 2879, 2863,
   1823, 3903, 3903, 100, 200, 2735, 2735, 200, 200, 2735, 2735, 200, 2735, 3239, 2747, 2735, 200, 2735, 2735, 200, 204, 2747, 212, 2747, 2122,
   228, 204, 212, 2747, 2747, 212, 2122]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem proof22 : cases22.foldlM (fun rem next => certifies goal 6 next rem) data22 = some [] := by
  decide +kernel

def cases23 : List (List Sig) := ((successors inputs 7).drop 213).take 8

set_option maxRecDepth 12000 in
def data23 : List ℕ :=
  [0, 1172, 0, 652, 1823, 228, 100, 100, 200, 2118, 200, 228, 228, 2122, 204, 204, 212, 2130, 212, 228, 1823, 2148, 1823, 2148, 655,
   2150, 655, 2150, 1172, 2122, 1179, 2122, 667, 2162, 667, 2162, 2148, 198, 2150, 2148, 2122, 1815, 2122, 2124, 2148, 210, 2162, 2148, 2122, 647,
   2122, 2126, 2150, 1159, 2162, 2150, 2122, 667, 2138, 2122, 1172, 652, 228, 652, 652, 0, 1172, 100, 100, 228, 0, 70, 1819, 70, 100,
   74, 1815, 74, 76, 82, 1807, 82, 100, 1822, 650, 1823, 1822, 652, 1818, 655, 652, 1179, 652, 1179, 1180, 652, 1188, 667, 652, 1175,
   647, 1179, 1175, 655, 1159, 667, 655, 74, 667, 155, 155, 228, 200, 2118, 200, 204, 228, 212, 2130, 212, 1822, 650, 1823, 1822, 652,
   200, 655, 200, 1179, 652, 1179, 1180, 652, 212, 667, 212, 70, 198, 70, 72, 2122, 1815, 2122, 2124, 82, 210, 82, 84, 200, 647,
   2122, 200, 200, 1159, 212, 200, 212, 667, 212, 2122, 652, 1172, 228, 1172, 1822, 1823, 1822, 650, 2148, 652, 1823, 1823, 652, 1822, 2148,
   1822, 652, 655, 652, 1818, 2150, 1822, 655, 655, 1822, 652, 2150, 652, 3227, 3227, 3252, 652, 2122, 652, 3227, 3227, 652, 3228, 2122, 3252,
   652, 667, 652, 3236, 2162, 3252, 667, 667, 3252, 652, 2162, 652, 1303, 0, 100, 200, 655, 200, 228, 228, 3227, 204, 204, 212, 667,
   212, 228, 1172, 652, 652, 1172, 1822, 652, 652, 1822, 652, 199, 655, 652, 3227, 652, 3227, 3228, 652, 3236, 667, 652, 70, 655, 70,
   655, 74, 3227, 74, 3227, 82, 667, 82, 667, 3227, 655, 3227, 3231, 655, 3239, 667, 655, 212, 667, 2203, 667, 1303, 228, 228, 2148,
   100, 0, 652, 1172, 652, 1172, 1303, 228, 200, 70, 200, 204, 228, 212, 82, 212, 1822, 1172, 1172, 1822, 1172, 199, 1175, 1172, 1172,
   652, 3227, 1172, 652, 212, 148, 148, 70, 200, 70, 200, 74, 1823, 74, 76, 82, 212, 82, 212, 200, 655, 74, 200, 200, 1159,
   212, 200, 212, 667, 212, 74, 2148, 100, 228, 1303, 2148, 2150, 2148, 1819, 655, 1823, 2150, 2150, 1823, 2148, 655, 2148, 2122, 2122, 2148,
   1823, 3227, 1823, 2122, 2122, 1823, 2124, 3227, 2148, 2148, 2162, 2148, 1807, 667, 1823, 2162, 2162, 1823, 2148, 667, 2148, 200, 228, 200, 2118,
   0, 1172, 652, 652, 1172, 1822, 650, 1823, 1822, 652, 1818, 655, 652, 3227, 652, 3227, 3228, 652, 3236, 667, 652, 0, 70, 1819, 70,
   72, 74, 1815, 74, 76, 82, 1807, 82, 100, 1822, 650, 1823, 1822, 652, 1818, 655, 652, 3227, 652, 3227, 3228, 652, 3236, 667, 652,
   3223, 647, 3227, 3223, 655, 3207, 667, 655, 74, 667, 2203, 667, 228, 100, 100, 2118, 1819, 2118, 2120, 2122, 1815, 2122, 2124, 2148, 1807,
   2162, 2148, 200, 2118, 647, 2122, 2118, 2118, 3207, 2134, 2118, 204, 2122, 667, 2138, 2122, 212, 2130, 228, 212, 2150, 228, 228, 2150, 200,
   0, 1172, 652, 1172, 652, 1823, 228, 100, 100, 2118, 228, 2122, 204, 204, 212, 2130, 212, 228, 1562, 650, 1563, 1562, 652, 199, 1175,
   652, 3227, 652, 3227, 3228, 652, 3236, 667, 652, 2148, 198, 70, 2148, 2122, 1563, 2122, 2124, 2148, 667, 2162, 2148, 2122, 0, 2122, 667,
   2138, 2122, 200, 2118, 200, 204, 647, 648, 1302, 647, 1303, 1559, 1303, 1307, 647, 663, 212, 647, 3227, 652, 3227, 3228, 1562, 650, 1563,
   1562, 652, 1546, 667, 652, 2122, 1563, 2122, 2124, 263, 667, 539, 539, 2122, 200, 2162, 1159, 2162, 200, 2122, 667, 2138, 2122, 200, 2122,
   2122, 2150, 655, 0, 228, 2122, 204, 204, 2122, 667, 2138, 2122, 3227, 652, 3227, 3228, 1302, 652, 652, 1302, 1822, 650, 1823, 1822, 652,
   1818, 655, 652, 652, 1806, 667, 652, 2122, 1823, 2122, 2124, 1303, 1815, 1311, 1303, 1563, 1819, 1567, 1563, 783, 1807, 799, 783, 2126, 647,
   647, 655, 0, 200, 2118, 200, 204, 647, 648, 1302, 647, 1303, 1559, 1303, 1307, 647, 663, 212, 647, 2122, 667, 2138, 2122, 3227, 652,
   3227, 3228, 1562, 650, 1563, 1562, 652, 1546, 667, 652, 2122, 1563, 2122, 2124, 2148, 667, 539, 539, 655, 0, 647, 647, 655, 212, 2122,
   655, 2126, 2122, 1159, 3207, 1167, 1159, 652, 778, 655, 652, 3215, 782, 3215, 3216, 262, 774, 270, 262, 782, 3250, 783, 782, 2148, 655,
   527, 527, 2122, 783, 783, 3087, 263, 775, 271, 263, 667, 655, 212, 667, 667, 212, 655, 2122, 2122, 655, 2126, 0, 204, 3227, 652,
   3228, 3227, 2122, 1563, 2124, 2122, 655, 2122, 667, 2138, 2122, 1172, 652, 652, 1172, 1562, 650, 1563, 1562, 652, 1822, 3231, 652, 652, 1546,
   667, 652, 1303, 1563, 1563, 100, 1563, 1823, 2126, 1563, 2148, 667, 539, 539, 200, 2118, 208, 200, 667, 3215, 667, 2126, 212, 667, 667,
   212, 2150, 2150, 2162, 2150, 3239, 0, 212, 2130, 228, 212, 652, 3236, 667, 652, 1172, 3220, 1204, 1172, 782, 3250, 783, 782, 3239, 782,
   3239, 3240, 3227, 782, 3227, 3228, 2148, 783, 2162, 2148, 263, 783, 783, 263, 795, 783, 783, 1551, 807, 783, 783, 2319, 2150, 1159, 3207,
   1191, 1159, 3227, 0, 2122, 655, 2126, 2122, 1159, 3207, 1167, 1159, 647, 647, 655, 212, 3215, 782, 3215, 3216, 652, 778, 655, 652, 262,
   774, 270, 262, 782, 650, 783, 782, 2122, 783, 783, 3087, 2148, 655, 527, 527, 263, 775, 271, 263, 3215, 3215, 2122, 667, 2138, 2122,
   1179, 3255, 2162, 2162, 3255, 2150, 0, 212, 2130, 228, 212, 652, 3236, 652, 667, 2148, 667, 2148, 2162, 3239, 2122, 667, 2122, 2138, 1172,
   3220, 1204, 1172, 1562, 3250, 1563, 1562, 3252, 778, 655, 3252, 3227, 1562, 3227, 3228, 263, 1563, 1563, 100, 1563, 655, 2150, 1563, 2122, 1563,
   1563, 3099, 200, 2118, 228, 200, 3227, 655, 3227, 2126, 1179, 2150, 204, 0, 652, 3220, 652, 1204, 1823, 228, 100, 100, 200, 2118, 200,
   228, 2122, 212, 2130, 212, 228, 3382, 3250, 3383, 3382, 3252, 3378, 3255, 3252, 3252, 204, 1179, 3252, 2212, 3236, 2228, 2212, 2148, 3255, 2150,
   2148, 2148, 202, 74, 2148, 2148, 3367, 2162, 2148, 2150, 647, 204, 2150, 2150, 3239, 2162, 2150, 2162, 667, 2162, 204, 0, 228, 3227, 3228,
   652, 3227, 2122, 2124, 1823, 2122, 2122, 2126, 655, 2122, 2122, 2138, 667, 2122, 1172, 3252, 3252, 1172, 3382, 3250, 3383, 3382, 3252, 3378, 3255,
   3252, 2212, 3236, 2228, 2212, 74, 2148, 2148, 76, 2148, 3255, 2150, 2148, 2148, 3367, 2162, 2148, 200, 2150, 2150, 200, 2150, 3239, 2162, 2150,
   204, 2162, 2162, 212, 2122, 2162, 2122, 667, 667, 3227, 2138, 2162, 3227, 2122, 667, 2122, 212, 228, 212, 2130, 0, 262, 652, 652, 164,
   1822, 650, 1823, 1822, 652, 1818, 655, 652, 1172, 652, 1179, 1172, 652, 1172, 667, 652, 263, 228, 100, 100, 2148, 1819, 2150, 2148, 2122,
   1815, 2122, 2124, 2130, 1807, 2130, 2132, 200, 2118, 228, 200, 2122, 655, 2122, 2126, 2130, 1175, 2130, 2134, 204, 2122, 667, 2130, 2122, 212,
   2162, 228, 228, 2162, 212, 0, 1172, 652, 1172, 652, 1823, 228, 100, 100, 200, 2118, 200, 228, 228, 2122, 204, 204, 2130, 782, 650,
   783, 782, 652, 778, 655, 652, 676, 652, 652, 2188, 652, 212, 148, 652, 2148, 655, 2150, 2148, 2122, 783, 2122, 2124, 2148, 210, 82,
   2148, 2122, 655, 2122, 2126, 2150, 1159, 212, 2150, 2122, 1179, 212, 2122, 212, 2154, 0, 1172, 2732, 2732, 1172, 3902, 2730, 3903, 3902, 2732,
   3898, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 652, 2700, 684, 652, 1303, 2148, 2148, 1303, 2148, 3899, 2150, 2148, 2148, 3895,
   2154, 2148, 2148, 3887, 2162, 2148, 1823, 2148, 2148, 1823, 200, 2150, 2150, 200, 2150, 2727, 2154, 2150, 2150, 3239, 2162, 2150, 655, 2150, 2150,
   655, 204, 2154, 2747, 2162, 2154, 2122, 2154, 0, 228, 3227, 3228, 652, 3227, 2122, 2124, 1823, 2122, 2122, 2126, 655, 2122, 2122, 2138, 667,
   2122, 1172, 3252, 3252, 1172, 3382, 3250, 3383, 3382, 3252, 3378, 3255, 3252, 2212, 3236, 2228, 2212, 74, 2148, 2148, 76, 2148, 3255, 2150, 2148,
   2148, 3367, 2162, 2148, 200, 2150, 2150, 200, 2150, 3239, 2162, 2150, 204, 2162, 2162, 212, 212, 2162, 2162, 212, 667, 2162, 2162, 667, 228,
   228, 228, 2154, 0, 2732, 652, 2732, 652, 2148, 1823, 2148, 1823, 200, 655, 200, 655, 204, 212, 667, 212, 667, 0, 1172, 652, 652,
   1172, 1822, 650, 1823, 1822, 652, 1818, 655, 652, 3227, 652, 3227, 3228, 652, 3236, 667, 652, 1303, 228, 100, 100, 2148, 1819, 2150, 2148,
   2122, 1823, 2122, 2124, 2148, 1807, 2162, 2148, 200, 2118, 228, 200, 2122, 655, 2122, 2126, 2150, 3239, 2162, 2150, 204, 2122, 667, 2138, 2122,
   212, 2130, 228, 212, 1822, 650, 1823, 1822, 652, 1818, 655, 652, 3252, 652, 652, 3252, 652, 1806, 667, 652, 652, 2732, 2732, 652, 1563,
   1819, 1567, 1563, 2148, 1823, 1823, 2148, 783, 1807, 799, 783, 1823, 228, 100, 1823, 200, 655, 655, 200, 655, 3239, 667, 655, 655, 2118,
   228, 655, 212, 667, 212, 667, 228, 2154, 236, 667, 2130, 228, 667, 204]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem proof23 : cases23.foldlM (fun rem next => certifies goal 6 next rem) data23 = some [] := by
  decide +kernel

def cases24 : List (List Sig) := ((successors inputs 7).drop 221).take 8

set_option maxRecDepth 12000 in
def data24 : List ℕ :=
  [0, 652, 652, 0, 1204, 1823, 228, 100, 100, 200, 2118, 200, 228, 2122, 212, 2130, 212, 228, 1822, 2148, 1823, 2148, 652, 2150, 655,
   2150, 1172, 204, 1179, 1172, 652, 2162, 667, 2162, 2148, 198, 2150, 2148, 2148, 202, 74, 2148, 2148, 210, 2162, 2148, 2150, 647, 204, 2150,
   2150, 1159, 2162, 2150, 2162, 667, 2162, 204, 3220, 3252, 228, 652, 652, 228, 1204, 3252, 0, 652, 100, 100, 228, 0, 1822, 650, 1822,
   1823, 70, 1819, 70, 100, 74, 1815, 74, 100, 82, 1807, 82, 100, 655, 1818, 655, 1204, 1179, 676, 1179, 1204, 667, 1188, 667, 164,
   1175, 647, 1179, 1175, 655, 1159, 667, 655, 74, 667, 155, 155, 228, 200, 2118, 200, 228, 204, 2122, 204, 228, 212, 2130, 212, 1823,
   1202, 1823, 1334, 655, 200, 655, 200, 1179, 204, 1179, 204, 667, 212, 667, 212, 70, 198, 70, 72, 74, 202, 74, 76, 82, 210,
   82, 84, 200, 647, 204, 200, 200, 1159, 212, 200, 204, 667, 212, 204, 1823, 1823, 0, 652, 3220, 652, 1204, 100, 200, 3223, 200,
   228, 3227, 212, 0, 652, 212, 667, 652, 1822, 1170, 1823, 1822, 1172, 1818, 1175, 1172, 1172, 1814, 1179, 1172, 82, 210, 82, 84, 1563,
   1819, 1567, 1563, 1303, 1815, 1311, 1303, 200, 1159, 212, 200, 1175, 647, 1179, 1175, 204, 667, 212, 204, 212, 228, 1822, 3252, 3252, 1822,
   3252, 199, 3255, 3252, 3252, 204, 1179, 3252, 2212, 3236, 2228, 2212, 70, 3255, 70, 3255, 74, 202, 74, 76, 82, 210, 82, 84, 3255,
   647, 204, 3255, 2215, 3239, 2231, 2215, 204, 667, 212, 204, 228, 2148, 228, 100, 1823, 228, 100, 2148, 0, 1823, 228, 200, 70, 200,
   228, 204, 74, 204, 228, 212, 82, 212, 1204, 652, 652, 3220, 1822, 652, 652, 1822, 652, 199, 655, 652, 1172, 204, 1179, 1172, 652,
   212, 667, 652, 70, 200, 70, 200, 74, 204, 74, 204, 82, 212, 82, 212, 200, 647, 204, 200, 200, 1159, 212, 200, 204, 667,
   212, 204, 200, 200, 228, 2118, 2150, 0, 204, 2122, 204, 228, 212, 2130, 212, 228, 652, 3220, 1204, 652, 1822, 3250, 1823, 1822, 3223,
   1822, 3223, 3224, 3252, 1814, 1310, 3252, 2212, 3236, 2228, 2212, 1563, 228, 100, 100, 2118, 1823, 2118, 2120, 2148, 1815, 1311, 2148, 2148, 1807,
   2162, 2148, 200, 2118, 0, 2118, 3207, 2134, 2118, 204, 2118, 200, 200, 647, 2130, 663, 647, 3223, 1302, 3223, 3224, 647, 1302, 647, 648,
   1302, 650, 1303, 1302, 262, 1286, 278, 262, 2118, 1303, 2118, 2120, 1307, 1303, 1303, 1559, 263, 1287, 279, 263, 2126, 2118, 2118, 3207, 2134,
   2118, 2162, 667, 2162, 204, 200, 200, 0, 652, 3220, 652, 1204, 1823, 228, 100, 100, 2118, 2122, 212, 2130, 212, 228, 3122, 3250, 3124,
   3122, 3252, 199, 655, 3252, 3252, 204, 1179, 3252, 2212, 3236, 2228, 2212, 2148, 198, 70, 2148, 2148, 202, 74, 2148, 2148, 210, 2162, 2148,
   200, 647, 204, 200, 2162, 1159, 2162, 200, 2162, 667, 2162, 204, 228, 2150, 228, 2122, 0, 228, 3227, 3228, 652, 3227, 2122, 2124, 1823,
   2122, 2122, 2126, 655, 2122, 2122, 2138, 667, 2122, 1172, 3252, 3252, 1172, 3382, 3250, 3383, 3382, 3252, 3378, 3255, 3252, 2212, 3236, 2228, 2212,
   74, 2148, 2148, 76, 2148, 3255, 2150, 2148, 2148, 3367, 2162, 2148, 200, 2150, 2150, 200, 2150, 3239, 2162, 2150, 204, 2162, 2162, 212, 0,
   1172, 652, 652, 1172, 1822, 650, 1823, 1822, 652, 1818, 655, 652, 3227, 652, 3227, 3228, 652, 3236, 667, 652, 1303, 228, 100, 100, 2148,
   1819, 2150, 2148, 2122, 1823, 2122, 2124, 2148, 1807, 2162, 2148, 200, 2118, 228, 200, 2122, 655, 2122, 2126, 2150, 3239, 2162, 2150, 204, 2122,
   667, 2138, 2122, 212, 2130, 228, 212, 212, 212, 228, 2130, 2162, 0, 652, 1172, 1172, 652, 1822, 1170, 1823, 1822, 1172, 1818, 1175, 1172,
   1172, 1814, 1179, 1172, 1188, 1172, 1172, 2196, 783, 228, 100, 100, 2148, 1819, 2150, 2148, 2148, 1815, 1311, 2148, 2130, 1823, 2130, 2132, 200,
   2118, 228, 200, 2150, 647, 1179, 2150, 2130, 1175, 2130, 2134, 204, 2122, 228, 204, 2130, 1179, 2130, 2138, 212, 212, 212, 0, 652, 228,
   652, 164, 1823, 228, 100, 100, 200, 2118, 200, 228, 2122, 2130, 2342, 2148, 2343, 2342, 2212, 2150, 2215, 2212, 2212, 204, 1179, 2212, 2212,
   212, 667, 2212, 2148, 2215, 2150, 2148, 2148, 202, 74, 2148, 2148, 210, 82, 2148, 2150, 647, 204, 2150, 2150, 1159, 212, 2150, 204, 667,
   212, 204, 228, 2162, 228, 3382, 3383, 3382, 3250, 2148, 3252, 3383, 3383, 3252, 3382, 2148, 3382, 3252, 3255, 3252, 3378, 2150, 3382, 3255, 3255,
   3382, 3252, 2150, 3252, 3252, 1179, 3252, 204, 204, 652, 1179, 1179, 652, 3252, 204, 3252, 2212, 667, 2212, 3236, 2162, 3252, 2228, 667, 3252,
   2212, 2162, 2212, 2148, 2150, 2148, 3255, 3255, 3383, 2150, 2150, 3383, 2148, 3255, 2148, 2148, 74, 2148, 202, 204, 1823, 74, 74, 1823, 2148,
   204, 2148, 2148, 2162, 2148, 3367, 212, 3383, 2162, 2162, 3383, 2148, 212, 2148, 2150, 204, 2150, 647, 0, 2162, 667, 2162, 204, 204, 2122,
   204, 228, 652, 3350, 652, 1334, 1303, 3351, 1303, 1335, 647, 0, 204, 2118, 200, 200, 647, 2130, 663, 647, 2118, 3207, 2134, 2118, 647,
   1302, 647, 648, 3223, 1302, 3223, 3224, 1302, 3250, 1303, 1302, 262, 1286, 278, 262, 1307, 1303, 1303, 1559, 2118, 1303, 2118, 2120, 263, 1287,
   279, 263, 647, 679, 667, 2130, 667, 228, 3252, 3382, 3382, 3252, 3382, 650, 3383, 3382, 647, 3382, 3382, 648, 2342, 3366, 2358, 2342, 2148,
   3383, 3383, 2148, 1307, 3383, 3383, 1559, 2343, 3367, 2359, 2343, 2150, 647, 0, 2162, 3239, 2150, 2150, 647, 2130, 647, 679, 1159, 3207, 1159,
   1191, 262, 2310, 262, 294, 263, 2311, 263, 295, 647, 2342, 2342, 648, 3239, 2342, 3239, 3240, 2342, 3250, 2343, 2342, 2148, 2343, 2343, 519,
   2148, 2343, 2343, 3111, 663, 647, 655, 204, 204, 655, 2150, 0, 3252, 204, 3252, 1179, 2148, 202, 2148, 74, 647, 2162, 667, 2162, 204,
   2122, 652, 3220, 652, 1204, 1563, 228, 1563, 100, 200, 2118, 200, 228, 667, 2130, 667, 228, 1562, 650, 1563, 1562, 652, 3378, 3255, 652,
   652, 1546, 667, 652, 1563, 3255, 2150, 1563, 2148, 667, 539, 539, 667, 3239, 667, 2150, 2150, 2150, 2162, 2150, 3239, 0, 212, 2130, 212,
   228, 1172, 3220, 1172, 1204, 783, 2311, 783, 295, 1159, 3207, 1159, 1191, 3227, 2212, 3236, 2228, 2212, 2342, 3250, 2343, 2342, 3239, 2342, 3239,
   3240, 3252, 774, 1179, 3252, 2148, 2343, 2162, 2148, 795, 2343, 2343, 3111, 2343, 775, 271, 2343, 2150, 3239, 0, 2162, 3239, 2150, 2150, 1159,
   3207, 1159, 1191, 647, 2130, 647, 679, 262, 2310, 262, 294, 263, 2311, 263, 295, 3239, 2342, 3239, 3240, 647, 2342, 2342, 648, 2342, 650,
   2343, 2342, 2148, 2343, 2343, 3111, 2148, 2343, 2343, 519, 1167, 3239, 2162, 667, 2162, 204, 3255, 2162, 2162, 3255, 2150, 0, 2212, 3236, 2212,
   2228, 2148, 210, 2148, 2162, 3239, 2162, 667, 204, 2162, 212, 2130, 212, 228, 1172, 3220, 1172, 1204, 1563, 228, 1563, 100, 200, 2118, 200,
   228, 3227, 3122, 3250, 3124, 3122, 3252, 2150, 2215, 3252, 3252, 1554, 1179, 3252, 1563, 2215, 2150, 1563, 2148, 1179, 1051, 1051, 1179, 647, 1179,
   2150, 2150, 2162, 2162, 204, 667, 667, 1179, 2162, 2162, 1179, 204, 667, 204, 204, 0, 2732, 3252, 2732, 3252, 3903, 2148, 3903, 2148, 200,
   2150, 200, 2150, 2154, 212, 2162, 212, 2162, 228, 3382, 3250, 3383, 3382, 3252, 3378, 3255, 3252, 3252, 2732, 1179, 3252, 2212, 3236, 2228, 2212,
   652, 3252, 3252, 652, 2148, 3255, 2150, 2148, 2148, 202, 74, 2148, 2148, 3367, 2162, 2148, 1823, 2148, 2148, 1823, 2150, 2735, 204, 2150, 2150,
   3239, 2162, 2150, 200, 2150, 2150, 200, 2162, 2747, 2162, 204, 204, 0, 228, 3227, 3228, 652, 3227, 2122, 2124, 1823, 2122, 2122, 2126, 655,
   2122, 2122, 2138, 667, 2122, 1172, 3252, 3252, 1172, 3382, 3250, 3383, 3382, 3252, 3378, 3255, 3252, 2212, 3236, 2228, 2212, 74, 2148, 2148, 76,
   2148, 3255, 2150, 2148, 2148, 3367, 2162, 2148, 200, 2150, 2150, 200, 2150, 3239, 2162, 2150, 204, 2162, 2162, 212, 236, 212, 2162, 2162, 212,
   212, 228, 212, 0, 2162, 0, 652, 2700, 652, 684, 1823, 228, 100, 100, 200, 2118, 200, 228, 204, 2122, 204, 228, 2130, 2862, 2730,
   2863, 2862, 2732, 2858, 2735, 2732, 2212, 2724, 2220, 2212, 2732, 212, 667, 2732, 2148, 2735, 2150, 2148, 2148, 2855, 2154, 2148, 2148, 210, 82,
   2148, 2150, 2727, 2154, 2150, 2150, 1159, 212, 2150, 2154, 667, 212, 2154, 2732, 3252, 3252, 2732, 3902, 3250, 3903, 3902, 3252, 3898, 3255, 3252,
   3252, 3894, 3259, 3252, 2732, 3252, 3252, 2732, 652, 3252, 3252, 652, 2148, 3903, 3903, 2148, 3643, 3899, 3647, 3643, 3383, 3895, 3391, 3383, 2148,
   3903, 3903, 2148, 1823, 3903, 3903, 100, 200, 3255, 3255, 200, 3255, 2727, 3259, 3255, 200, 3255, 3255, 200, 200, 3255, 3255, 200, 204, 3259,
   3259, 204, 204, 3259, 3259, 204, 204, 3259, 3259, 204, 2130, 228, 212, 2130]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem proof24 : cases24.foldlM (fun rem next => certifies goal 6 next rem) data24 = some [] := by
  decide +kernel

def cases25 : List (List Sig) := ((successors inputs 7).drop 229).take 8

set_option maxRecDepth 12000 in
def data25 : List ℕ :=
  [0, 652, 0, 684, 1823, 228, 100, 100, 200, 2118, 200, 228, 204, 2122, 204, 228, 228, 2130, 212, 212, 1823, 2148, 1823, 2148, 652,
   2150, 655, 2150, 1179, 2154, 1179, 2154, 652, 2130, 667, 2130, 2148, 198, 2150, 2148, 2148, 202, 2154, 2148, 2130, 1807, 2130, 2132, 2150, 647,
   2154, 2150, 2130, 1159, 2130, 2134, 2130, 667, 2130, 2138, 652, 2700, 228, 2732, 684, 0, 652, 100, 100, 228, 0, 70, 1819, 70, 100,
   74, 1815, 74, 100, 82, 1807, 82, 84, 1822, 650, 1823, 1822, 655, 1818, 655, 684, 1172, 676, 1179, 1172, 667, 1172, 667, 668, 1175,
   647, 1179, 1175, 655, 1159, 667, 655, 74, 667, 155, 155, 228, 200, 2118, 200, 228, 204, 2122, 204, 212, 1822, 682, 1823, 1822, 655,
   200, 655, 200, 1172, 204, 1179, 204, 667, 1172, 667, 668, 70, 198, 70, 72, 74, 202, 74, 76, 2130, 1807, 2130, 2132, 200, 647,
   204, 200, 200, 1159, 2130, 200, 204, 667, 2130, 204, 2732, 652, 228, 652, 1822, 1823, 1822, 2730, 2148, 2732, 1823, 1823, 2732, 1822, 2148,
   1822, 2732, 2735, 2732, 1818, 2150, 1822, 2735, 2735, 1822, 2732, 2150, 2732, 1172, 1179, 1172, 2724, 2154, 2732, 1179, 1179, 2732, 1172, 2154, 1172,
   2715, 2715, 2732, 1172, 2130, 1172, 2715, 2715, 1172, 2716, 2130, 2732, 783, 0, 100, 200, 2703, 200, 228, 204, 1179, 204, 228, 228, 2715,
   212, 212, 652, 2700, 684, 652, 1822, 2732, 2732, 1822, 2732, 199, 2735, 2732, 1172, 2724, 1179, 1172, 2715, 1172, 2715, 2716, 70, 2735, 70,
   2735, 74, 1179, 74, 1179, 82, 2715, 82, 2715, 1175, 2727, 1179, 1175, 2715, 1175, 2715, 2719, 204, 1179, 1179, 2203, 783, 228, 228, 2148,
   100, 0, 684, 652, 2700, 652, 783, 228, 200, 70, 200, 228, 204, 74, 204, 212, 1822, 652, 652, 1822, 652, 199, 655, 652, 1172,
   204, 140, 140, 652, 1172, 2715, 652, 70, 200, 70, 200, 74, 204, 74, 204, 82, 1823, 82, 84, 200, 647, 204, 200, 200, 1175,
   82, 200, 204, 1179, 82, 204, 2148, 100, 228, 783, 2148, 2150, 2148, 1819, 2735, 1823, 2150, 2150, 1823, 2148, 2735, 2148, 2148, 2154, 2148,
   1815, 1179, 1823, 2154, 2154, 1823, 2148, 1179, 2148, 2130, 2130, 2148, 1823, 2715, 1823, 2130, 2130, 1823, 2132, 2715, 2148, 200, 228, 200, 2118,
   0, 652, 2700, 684, 652, 1822, 2730, 1823, 1822, 2703, 1818, 2703, 2704, 1172, 2724, 1179, 1172, 2715, 1172, 2715, 2716, 0, 70, 1819, 70,
   72, 74, 1815, 74, 100, 82, 1807, 82, 84, 1822, 2698, 1823, 1822, 2703, 1818, 2703, 2704, 1172, 2724, 1179, 1172, 2715, 1172, 2715, 2716,
   1175, 2695, 1179, 1175, 2703, 1159, 2715, 2703, 74, 1179, 1179, 2203, 228, 100, 100, 2118, 1819, 2118, 2120, 2148, 1815, 2154, 2148, 2130, 1807,
   2130, 2132, 200, 2118, 2695, 2126, 2118, 2118, 1159, 2130, 2118, 204, 2122, 228, 204, 2130, 1179, 2130, 2138, 212, 2150, 228, 228, 2150, 200,
   0, 652, 2700, 652, 684, 1823, 228, 100, 100, 2118, 204, 2122, 204, 228, 228, 2130, 212, 212, 1562, 2730, 1563, 1562, 2732, 199, 655,
   2732, 1172, 2724, 1179, 1172, 2715, 1172, 2715, 2716, 2148, 198, 70, 2148, 2148, 1179, 2154, 2148, 2130, 1563, 2130, 2132, 2154, 647, 2154, 200,
   2130, 0, 200, 2118, 200, 212, 1159, 1160, 782, 1159, 783, 1551, 783, 795, 1159, 1167, 204, 1159, 2715, 1172, 2715, 2716, 1562, 1170, 1563,
   1562, 1172, 1554, 1179, 1172, 2130, 1563, 2130, 2132, 263, 1179, 1051, 1051, 2130, 1179, 2130, 2138, 2130, 200, 2130, 1179, 2130, 2138, 200, 2150,
   2154, 2150, 2727, 0, 204, 2122, 228, 204, 2130, 1179, 2130, 2138, 1172, 2724, 1179, 1172, 652, 2700, 684, 652, 1302, 2730, 1303, 1302, 2727,
   1302, 2727, 2728, 2715, 1302, 2715, 2716, 2148, 1303, 2154, 2148, 263, 1303, 1303, 263, 1307, 1303, 1303, 1559, 1319, 1303, 1303, 2327, 2150, 647,
   2695, 679, 647, 2715, 0, 647, 2695, 663, 647, 2130, 1175, 2130, 2134, 1159, 1159, 1175, 204, 2711, 1302, 2711, 2712, 1172, 1298, 1175, 1172,
   262, 1286, 278, 262, 1302, 1170, 1303, 1302, 2130, 1303, 1303, 2583, 2148, 1175, 1047, 1047, 263, 1287, 279, 263, 2711, 2711, 667, 2735, 2154,
   2154, 2735, 2150, 0, 204, 2122, 228, 204, 1172, 2724, 1172, 1179, 2148, 1179, 2148, 2154, 2727, 2130, 1179, 2130, 2138, 652, 2700, 684, 652,
   1562, 2730, 1563, 1562, 2732, 1298, 1175, 2732, 2715, 1562, 2715, 2716, 263, 1563, 1563, 100, 1563, 1175, 2150, 1563, 2130, 1563, 1563, 2587, 200,
   2118, 228, 200, 2715, 1175, 2715, 2134, 667, 2150, 2130, 2130, 2150, 1175, 0, 228, 2130, 212, 212, 2715, 1172, 2715, 2716, 782, 1172, 1172,
   782, 1822, 1170, 1823, 1822, 1172, 1818, 1175, 1172, 1172, 1814, 1179, 1172, 2130, 1823, 2130, 2132, 783, 1807, 799, 783, 1563, 1819, 1567, 1563,
   1303, 1815, 1311, 1303, 2134, 1159, 1159, 1175, 0, 200, 2118, 200, 212, 1159, 1160, 782, 1159, 783, 1551, 783, 795, 1159, 1167, 204, 1159,
   2715, 1172, 2715, 2716, 1562, 1170, 1563, 1562, 1172, 1554, 1179, 1172, 2130, 1563, 2130, 2132, 2148, 1179, 1051, 1051, 2130, 1179, 2130, 2138, 1175,
   0, 2130, 1175, 2130, 2134, 1159, 1159, 1175, 204, 647, 2695, 663, 647, 1172, 1298, 1175, 1172, 2711, 1302, 2711, 2712, 262, 1286, 278, 262,
   1302, 2730, 1303, 1302, 2148, 1175, 1047, 1047, 2130, 1303, 1303, 2583, 263, 1287, 279, 263, 1179, 1175, 2130, 1179, 2130, 2138, 204, 1179, 1179,
   204, 1175, 2130, 2130, 1175, 2134, 0, 212, 2715, 1172, 2716, 2715, 2130, 1563, 2132, 2130, 1175, 2130, 1179, 2138, 2130, 652, 1172, 1172, 652,
   1562, 1170, 1563, 1562, 1172, 1822, 2719, 1172, 1172, 1554, 1179, 1172, 783, 1563, 1563, 100, 1563, 1823, 2134, 1563, 2148, 1179, 1051, 1051, 200,
   2118, 216, 200, 1179, 2711, 1179, 2134, 204, 1179, 1179, 204, 2150, 204, 228, 204, 2122, 0, 262, 652, 652, 164, 1822, 650, 1823, 1822,
   652, 1818, 655, 652, 1172, 652, 1179, 1172, 652, 1172, 667, 652, 263, 228, 100, 100, 2148, 1819, 2150, 2148, 2122, 1815, 2122, 2124, 2130,
   1807, 2130, 2132, 200, 2118, 228, 200, 2122, 655, 2122, 2126, 2130, 1175, 2130, 2134, 204, 2122, 667, 2130, 2122, 212, 2154, 228, 228, 2154,
   204, 0, 652, 1172, 652, 1172, 1823, 228, 100, 100, 200, 2118, 200, 228, 2122, 228, 2130, 212, 212, 1302, 1170, 1303, 1302, 1172, 1298,
   1175, 1172, 1172, 204, 140, 1172, 1188, 1172, 1172, 2196, 2148, 1175, 2150, 2148, 2148, 202, 74, 2148, 2130, 1303, 2130, 2132, 2150, 647, 204,
   2150, 2130, 1175, 2130, 2134, 2130, 667, 2130, 204, 204, 2130, 2130, 2154, 1179, 2715, 1179, 2130, 2130, 1179, 2138, 2715, 2154, 212, 0, 652,
   2700, 652, 684, 1823, 228, 100, 100, 200, 2118, 200, 228, 204, 2122, 204, 228, 2130, 2862, 2730, 2863, 2862, 2732, 2858, 2735, 2732, 2212,
   2724, 2220, 2212, 2732, 212, 667, 2732, 2148, 2735, 2150, 2148, 2148, 2855, 2154, 2148, 2148, 210, 82, 2148, 2150, 2727, 2154, 2150, 2150, 1159,
   212, 2150, 2154, 667, 212, 2154, 0, 228, 2715, 2716, 1172, 2715, 2130, 2132, 1823, 2130, 2130, 2134, 1175, 2130, 2130, 2138, 1179, 2130, 652,
   2732, 2732, 652, 2862, 2730, 2863, 2862, 2732, 2858, 2735, 2732, 2212, 2724, 2220, 2212, 82, 2148, 2148, 84, 2148, 2735, 2150, 2148, 2148, 2855,
   2154, 2148, 200, 2150, 2150, 200, 2150, 2727, 2154, 2150, 204, 2154, 2154, 204, 2162, 0, 652, 2732, 2732, 652, 3902, 2730, 3903, 3902, 2732,
   3898, 2735, 2732, 3252, 2724, 3259, 3252, 2732, 3236, 2747, 2732, 1172, 2732, 2732, 1172, 783, 2148, 2148, 783, 2148, 3899, 2150, 2148, 2148, 3895,
   2154, 2148, 2148, 3887, 2162, 2148, 1823, 2148, 2148, 1823, 200, 2150, 2150, 200, 2150, 2727, 2154, 2150, 2150, 3239, 2162, 2150, 1175, 2150, 2150,
   1175, 204, 2154, 2154, 204, 2154, 2747, 2162, 2154, 1179, 2154, 2154, 1179, 212, 2130, 2162, 0, 228, 2715, 2716, 1172, 2715, 2130, 2132, 1823,
   2130, 2130, 2134, 1175, 2130, 2130, 2138, 1179, 2130, 652, 2732, 2732, 652, 2862, 2730, 2863, 2862, 2732, 2858, 2735, 2732, 2212, 2724, 2220, 2212,
   82, 2148, 2148, 84, 2148, 2735, 2150, 2148, 2148, 2855, 2154, 2148, 200, 2150, 2150, 200, 2150, 2727, 2154, 2150, 204, 2154, 2154, 204, 228,
   228, 228, 2162, 0, 2732, 1172, 2732, 1172, 2148, 1823, 2148, 1823, 200, 1175, 200, 1175, 204, 1179, 204, 1179, 212, 0, 652, 2700, 684,
   652, 1822, 2730, 1823, 1822, 2732, 1818, 2735, 2732, 1172, 2724, 1179, 1172, 2715, 1172, 2715, 2716, 783, 228, 100, 100, 2148, 1819, 2150, 2148,
   2148, 1815, 2154, 2148, 2130, 1823, 2130, 2132, 200, 2118, 228, 200, 2150, 2727, 2154, 2150, 2130, 1175, 2130, 2134, 204, 2122, 228, 204, 2130,
   1179, 2130, 2138, 212, 1822, 1170, 1823, 1822, 1172, 1818, 1175, 1172, 1172, 1814, 1179, 1172, 2732, 1172, 1172, 2732, 1172, 2700, 684, 1172, 1563,
   1819, 1567, 1563, 1303, 1815, 1311, 1303, 2148, 1823, 1823, 2148, 1823, 228, 100, 1823, 1175, 2727, 1179, 1175, 200, 1175, 1175, 200, 1175, 2118,
   228, 1175, 204, 1179, 1179, 204, 1179, 2122, 228, 1179, 228, 2162, 244, 212]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem proof25 : cases25.foldlM (fun rem next => certifies goal 6 next rem) data25 = some [] := by
  decide +kernel

def cases26 : List (List Sig) := ((successors inputs 7).drop 237).take 3

set_option maxRecDepth 12000 in
def data26 : List ℕ :=
  [0, 652, 652, 0, 684, 1823, 228, 100, 100, 200, 2118, 200, 228, 204, 2122, 204, 228, 2130, 1822, 2148, 1823, 2148, 652, 2150, 655,
   2150, 1172, 2154, 1179, 2154, 652, 212, 667, 652, 2148, 198, 2150, 2148, 2148, 202, 2154, 2148, 2148, 210, 82, 2148, 2150, 647, 2154, 2150,
   2150, 1159, 212, 2150, 2154, 667, 212, 2154, 2700, 2732, 228, 652, 652, 228, 684, 2732, 0, 652, 100, 100, 228, 0, 1822, 650, 1822,
   1823, 70, 1819, 70, 100, 74, 1815, 74, 100, 82, 1807, 82, 100, 655, 1818, 655, 684, 1179, 676, 1179, 164, 667, 1188, 667, 684,
   1175, 647, 1179, 1175, 655, 1159, 667, 655, 74, 667, 155, 155, 228, 200, 2118, 200, 228, 204, 2122, 204, 228, 212, 2130, 212, 1823,
   682, 1823, 814, 655, 200, 655, 200, 1179, 204, 1179, 204, 667, 212, 667, 212, 70, 198, 70, 72, 74, 202, 74, 76, 82, 210,
   82, 84, 200, 647, 204, 200, 200, 1159, 212, 200, 204, 667, 212, 204, 1823, 1823, 0, 652, 2700, 652, 684, 100, 200, 2703, 200,
   228, 204, 0, 204, 667, 212, 204, 1172, 204, 1179, 1172, 1822, 650, 1823, 1822, 652, 1818, 655, 652, 652, 1806, 667, 652, 74, 202,
   74, 76, 1563, 1819, 1567, 1563, 783, 1807, 799, 783, 200, 647, 204, 200, 655, 1159, 667, 655, 204, 228, 2715, 1822, 2732, 2732, 1822,
   2732, 199, 2735, 2732, 2212, 2724, 2220, 2212, 2732, 212, 667, 2732, 70, 2735, 70, 2735, 74, 202, 74, 76, 82, 210, 82, 84, 2215,
   2727, 2223, 2215, 2735, 1159, 212, 2735, 204, 667, 212, 204, 228, 2148, 228, 100, 1823, 228, 100, 2148, 0, 1823, 228, 200, 70, 200,
   228, 204, 74, 204, 228, 212, 82, 212, 684, 652, 652, 2700, 1822, 652, 652, 1822, 652, 199, 655, 652, 1172, 204, 1179, 1172, 652,
   212, 667, 652, 70, 200, 70, 200, 74, 204, 74, 204, 82, 212, 82, 212, 200, 647, 204, 200, 200, 1159, 212, 200, 204, 667,
   212, 204, 200, 200, 228, 2118, 2150, 0, 204, 2122, 204, 228, 212, 2130, 212, 228, 652, 2700, 684, 652, 1822, 2730, 1823, 1822, 2703,
   1822, 2703, 2704, 2212, 2724, 2220, 2212, 2732, 1806, 798, 2732, 1563, 228, 100, 100, 2118, 1823, 2118, 2120, 2148, 1815, 2154, 2148, 2148, 1807,
   799, 2148, 200, 2118, 2695, 2126, 2118, 2118, 0, 212, 2118, 200, 200, 1159, 2122, 1167, 1159, 2703, 782, 2703, 2704, 1159, 782, 1159, 1160,
   782, 1170, 783, 782, 262, 774, 270, 262, 2118, 783, 2118, 2120, 795, 783, 783, 1551, 263, 775, 271, 263, 2118, 2695, 2118, 2126, 2134,
   2118, 2154, 667, 212, 2154, 200, 200, 0, 652, 2700, 652, 684, 1823, 228, 100, 100, 2118, 204, 2122, 204, 228, 2130, 2602, 2730, 2604,
   2602, 2732, 199, 655, 2732, 2212, 2724, 2220, 2212, 2732, 212, 667, 2732, 2148, 198, 70, 2148, 2148, 202, 2154, 2148, 2148, 210, 82, 2148,
   2154, 647, 2154, 200, 200, 1159, 212, 200, 2154, 667, 212, 2154, 228, 2150, 228, 204, 204, 228, 2122, 2154, 0, 212, 2130, 212, 228,
   1172, 652, 652, 1172, 1822, 650, 1823, 1822, 652, 1818, 655, 652, 676, 652, 652, 2188, 652, 1806, 667, 652, 1303, 228, 100, 100, 2148,
   1819, 2150, 2148, 2122, 1823, 2122, 2124, 2148, 1807, 799, 2148, 200, 2118, 228, 200, 2122, 655, 2122, 2126, 2150, 1159, 667, 2150, 204, 2122,
   667, 2138, 2122, 204, 204, 0, 652, 228, 652, 164, 1823, 228, 100, 100, 200, 2118, 200, 228, 2122, 2130, 2342, 2148, 2343, 2342, 2212,
   2150, 2215, 2212, 2212, 204, 1179, 2212, 2212, 212, 667, 2212, 2148, 2215, 2150, 2148, 2148, 202, 74, 2148, 2148, 210, 82, 2148, 2150, 647,
   204, 2150, 2150, 1159, 212, 2150, 204, 667, 212, 204, 228, 2154, 228, 2130, 0, 228, 2715, 2716, 1172, 2715, 2130, 2132, 1823, 2130, 2130,
   2134, 1175, 2130, 2130, 2138, 1179, 2130, 652, 2732, 2732, 652, 2862, 2730, 2863, 2862, 2732, 2858, 2735, 2732, 2212, 2724, 2220, 2212, 82, 2148,
   2148, 84, 2148, 2735, 2150, 2148, 2148, 2855, 2154, 2148, 200, 2150, 2150, 200, 2150, 2727, 2154, 2150, 204, 2154, 2154, 204, 0, 652, 2700,
   684, 652, 1822, 2730, 1823, 1822, 2732, 1818, 2735, 2732, 1172, 2724, 1179, 1172, 2715, 1172, 2715, 2716, 783, 228, 100, 100, 2148, 1819, 2150,
   2148, 2148, 1815, 2154, 2148, 2130, 1823, 2130, 2132, 200, 2118, 228, 200, 2150, 2727, 2154, 2150, 2130, 1175, 2130, 2134, 204, 2122, 228, 204,
   2130, 1179, 2130, 2138, 212, 2862, 2863, 2862, 2730, 2148, 2732, 2863, 2863, 2732, 2862, 2148, 2862, 2732, 2735, 2732, 2858, 2150, 2862, 2735, 2735,
   2862, 2732, 2150, 2732, 2212, 1179, 2212, 2724, 2154, 2732, 2220, 1179, 2732, 2212, 2154, 2212, 2732, 667, 2732, 212, 212, 1172, 667, 667, 1172,
   2732, 212, 2732, 2148, 2150, 2148, 2735, 2735, 2863, 2150, 2150, 2863, 2148, 2735, 2148, 2148, 2154, 2148, 2855, 204, 2863, 2154, 2154, 2863, 2148,
   204, 2148, 2148, 82, 2148, 210, 212, 1823, 82, 82, 1823, 2148, 212, 2148, 2150, 2154, 2150, 2727, 0, 2154, 667, 212, 2154, 204, 2122,
   204, 228, 652, 2700, 652, 684, 1303, 2311, 1303, 295, 647, 2695, 647, 679, 2715, 2212, 2724, 2220, 2212, 2342, 2730, 2343, 2342, 2727, 2342,
   2727, 2728, 2732, 1286, 667, 2732, 2148, 2343, 2154, 2148, 1307, 2343, 2343, 2599, 2343, 1287, 279, 2343, 2150, 2727, 0, 2154, 2727, 2150, 2150,
   647, 2695, 647, 679, 1159, 2122, 1159, 1191, 262, 2310, 262, 294, 263, 2311, 263, 295, 2727, 2342, 2727, 2728, 1159, 2342, 2342, 1160, 2342,
   1170, 2343, 2342, 2148, 2343, 2343, 2599, 2148, 2343, 2343, 1031, 663, 2727, 2735, 2154, 2154, 2735, 2150, 0, 2212, 2724, 2212, 2220, 2148, 202,
   2148, 2154, 2727, 2154, 667, 212, 2154, 204, 2122, 204, 228, 652, 2700, 652, 684, 1563, 228, 1563, 100, 200, 2118, 200, 228, 2715, 2602,
   2730, 2604, 2602, 2732, 2150, 2215, 2732, 2732, 1546, 667, 2732, 1563, 2215, 2150, 1563, 2148, 667, 539, 539, 667, 1159, 667, 2150, 2150, 2150,
   212, 2150, 1159, 0, 212, 2130, 212, 228, 1172, 2830, 1172, 814, 783, 2831, 783, 815, 1159, 0, 212, 2118, 200, 200, 1159, 2122, 1167,
   1159, 1159, 782, 1159, 1160, 2703, 782, 2703, 2704, 782, 2730, 783, 782, 262, 774, 270, 262, 795, 783, 783, 1551, 2118, 783, 2118, 2120,
   263, 775, 271, 263, 2118, 2695, 2118, 2126, 1159, 1191, 1179, 2122, 1179, 228, 2732, 2862, 2862, 2732, 2862, 1170, 2863, 2862, 1159, 2862, 2862,
   1160, 2342, 2854, 2350, 2342, 2148, 2863, 2863, 2148, 795, 2863, 2863, 1551, 2343, 2855, 2351, 2343, 2150, 1159, 0, 2154, 2727, 2150, 2150, 1159,
   2122, 1159, 1191, 647, 2695, 647, 679, 262, 2310, 262, 294, 263, 2311, 263, 295, 1159, 2342, 2342, 1160, 2727, 2342, 2727, 2728, 2342, 2730,
   2343, 2342, 2148, 2343, 2343, 1031, 2148, 2343, 2343, 2599, 1167, 1159, 2154, 667, 212, 2154, 1175, 212, 212, 1175, 2150, 0, 2732, 212, 2732,
   667, 2148, 210, 2148, 82, 1159, 2154, 667, 2154, 212, 2130, 1172, 2700, 1172, 684, 1563, 228, 1563, 100, 200, 2118, 200, 228, 1179, 2122,
   1179, 228, 1562, 1170, 1563, 1562, 1172, 2858, 2735, 1172, 1172, 1554, 1179, 1172, 1563, 2735, 2150, 1563, 2148, 1179, 1051, 1051, 1179, 2727, 1179,
   2150, 2150, 2154, 212, 2154, 667, 667, 1179, 212, 212, 1179, 2154, 667, 2154, 212, 0, 652, 2732, 652, 2732, 3903, 2148, 3903, 2148, 200,
   2150, 200, 2150, 204, 2154, 204, 2154, 2162, 228, 2862, 2730, 2863, 2862, 2732, 2858, 2735, 2732, 2212, 2724, 2220, 2212, 2732, 3252, 667, 2732,
   652, 2732, 2732, 652, 2148, 2735, 2150, 2148, 2148, 2855, 2154, 2148, 2148, 210, 82, 2148, 1823, 2148, 2148, 1823, 2150, 2727, 2154, 2150, 2150,
   3255, 212, 2150, 200, 2150, 2150, 200, 2154, 3259, 212, 2154, 204, 2154, 2154, 204, 212, 0, 228, 2715, 2716, 1172, 2715, 2130, 2132, 1823,
   2130, 2130, 2134, 1175, 2130, 2130, 2138, 1179, 2130, 652, 2732, 2732, 652, 2862, 2730, 2863, 2862, 2732, 2858, 2735, 2732, 2212, 2724, 2220, 2212,
   82, 2148, 2148, 84, 2148, 2735, 2150, 2148, 2148, 2855, 2154, 2148, 200, 2150, 2150, 200, 2150, 2727, 2154, 2150, 204, 2154, 2154, 204, 244]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem proof26 : cases26.foldlM (fun rem next => certifies goal 6 next rem) data26 = some [] := by
  decide +kernel

def allCases : List (List (List Sig)) := [cases0, cases1, cases2, cases3, cases4, cases5, cases6, cases7, cases8, cases9, cases10, cases11, cases12, cases13, cases14, cases15, cases16, cases17, cases18, cases19, cases20, cases21, cases22, cases23, cases24, cases25, cases26]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem covers : allCases.flatten = successors inputs 7 := by decide +kernel

lemma certsCover {next : List Sig} (h : next ∈ successors inputs 7) :
    ∃ i o, certifies goal 6 next i = some o := by
  rw [← covers] at h
  obtain ⟨block, member, into⟩ := List.mem_flatten.mp h
  simp only [allCases, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cert_fold_mem proof0 into
  · exact cert_fold_mem proof1 into
  · exact cert_fold_mem proof2 into
  · exact cert_fold_mem proof3 into
  · exact cert_fold_mem proof4 into
  · exact cert_fold_mem proof5 into
  · exact cert_fold_mem proof6 into
  · exact cert_fold_mem proof7 into
  · exact cert_fold_mem proof8 into
  · exact cert_fold_mem proof9 into
  · exact cert_fold_mem proof10 into
  · exact cert_fold_mem proof11 into
  · exact cert_fold_mem proof12 into
  · exact cert_fold_mem proof13 into
  · exact cert_fold_mem proof14 into
  · exact cert_fold_mem proof15 into
  · exact cert_fold_mem proof16 into
  · exact cert_fold_mem proof17 into
  · exact cert_fold_mem proof18 into
  · exact cert_fold_mem proof19 into
  · exact cert_fold_mem proof20 into
  · exact cert_fold_mem proof21 into
  · exact cert_fold_mem proof22 into
  · exact cert_fold_mem proof23 into
  · exact cert_fold_mem proof24 into
  · exact cert_fold_mem proof25 into
  · exact cert_fold_mem proof26 into

theorem no_short_run (k : ℕ) (limit : k ≤ 7) (run : Live true goal k inputs.toFinset) : False := by
  cases k with
  | zero =>
    have hit : goal ∈ inputs.toFinset := run.1.symm ▸ Finset.mem_singleton_self _
    exact (show goal ∉ inputs.toFinset by decide +kernel) hit
  | succ k =>
    obtain ⟨U, a, b, d, hd, root, ha, hb, hne, hf, tail⟩ := run
    have hp := live_proper tail (bin d a b) (Finset.mem_insert_self _ _)
    obtain ⟨next, hm, hn, hs⟩ :=
      actual_child hne hd root (by decide : inputs.Nodup) hf hp ((live_size tail).trans limit)
    obtain ⟨i, o, checked⟩ := certsCover hm
    exact proper_certificate tail (by omega) hs hn checked

theorem sizeWithNot (C : Circuit) (legal : FanInTwo C)
    (correct : ∀ x, C.eval (List.ofFn x) = truth x)
    (hasNot : ∃ g ∈ C.gates, g.op = GateOp.not) : 9 ≤ C.size := by
  obtain ⟨g, mem, op⟩ := hasNot
  have strict : C.gates.countP (fun g => !isNot g) < C.size := by
    change C.gates.countP (fun g => !isNot g) < C.gates.length
    rw [List.countP_eq_length_filter]
    exact List.length_filter_lt_length_iff_exists.mpr ⟨g, mem, by simp [isNot, op]⟩
  obtain ⟨k, bound, run⟩ := physical C legal correct
  by_contra! small
  exact no_short_run k (by omega) run

theorem replacement (s : ℕ) (fit : HasCircuitSize 6 truth s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn x) = truth x := by
  obtain ⟨C, legal, up, correct⟩ := fit
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · exact ⟨candidate, witnessMonotone,
      by simpa only [witnessSize] using (sizeWithNot C legal correct hasNot).trans up,
      witnessComputes⟩
  · refine ⟨C, ?_, up, correct⟩
    intro g hg
    obtain ⟨op, arity⟩ := legal g hg
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    change (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun e => (hasNot ⟨g, hg, e⟩).elim)), arity⟩

end PEqualNP.Outside.L_meta_13621

theorem PEqualNP.Outside.L_meta_13621 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4008372960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 4008372960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact PEqualNP.Outside.L_meta_13621.replacement
