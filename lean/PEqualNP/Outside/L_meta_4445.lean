import PEqualNP.Defs

-- Parent circuit lower bound by Choi113, project pull request 7480, Apache-2.0.
namespace PEqualNP.Outside.L_meta_4445_aux.Parent
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

inductive Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | stop (hp : proper target) : Live target 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
      Live target (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
      Live target (k+1) t (insert a (insert b U))

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩


def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

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
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
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

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

inductive Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | start : Reach roots 0 roots
  | one {p bank a} : Reach roots p bank → Available bank a →
      Reach roots (p+1) (inv a :: bank)
  | two {p bank a b} (op : Bool) : Reach roots p bank → Available bank a →
      Available bank b → Reach roots (p+1) (combine op a b :: bank)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

inductive Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | stop : Run goal 0 [goal]
  | perm {s xs zs} : xs.Perm zs → Run goal s xs → Run goal s zs
  | one {s a rest} (save : Bool) : Run goal s (inv a :: kept save a rest) →
      Run goal (s+1) (a::rest)
  | two {s a b rest} (op ka kb : Bool) :
      Run goal s (combine op a b :: kept ka a (kept kb b rest)) →
      Run goal (s+1) (a::b::rest)

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v := by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr

theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
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

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
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

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
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

theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r
  cases d <;> exact bit_bin _ _ _ _

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
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
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]

theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z

theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (hs : ∀ a ∈ S, a ∈ z::w) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm

theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ha ih =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩

theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S, k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs

theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def seed : Sig := 0x0ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 4 || sample r 6) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed_nonzero : seed ≠ zero := by decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

theorem exec_extends (gs : List Gate) (ws : List Sig) : ∃ l, execute gs ws = ws ++ l := by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩

def absentMask (i : Fin 9) : Nat := [16,4,2,4,65,1,18,4,8].getD i.val 0
def absentRow (i : Fin 9) : Row := Fin.ofNat 512 (absentMask i)
def presentRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| absentMask i)

theorem seed_witness : ∀ i : Fin 9,
    (bit (absentRow i) graph != bit (presentRow i) graph) &&
    ((inputs++[seed]).all fun w => w == inputs.getD i.val zero ||
      bit (absentRow i) w == bit (presentRow i) w) = true := by decide +kernel

theorem all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[seed]) :
    S=inputs.toFinset ∨ S=(inputs++[seed]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := seed_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (absentRow i) (presentRow i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : seed ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hseed)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx := sub w hw
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hseed hw)) needed

theorem initial_live (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y 6))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t, k ≤ 14 ∧ (Live graph k t inputs.toFinset ∨ Live graph k t (inputs++[seed]).toFinset) := by
  have headEq : (execute C.gates inputs).getD 9 zero = seed := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (seed_table r).symm)
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have out := get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  cases hgs : C.gates with
  | nil =>
    rw [hgs] at headEq
    exact False.elim (seed_nonzero headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g = seed := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = seed at headEq
      obtain ⟨l,hl⟩ := exec_extends gs (inputs++[gv inputs g])
      rw [hl] at headEq
      exact headEq
    rw [hgs] at targetIn
    change graph ∈ execute gs (inputs++[gv inputs g]) at targetIn
    rw [eq0] at targetIn
    have tailLegal : ∀ gate ∈ gs, gate.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ gate.inputs.length≤2 := by
      intro gate hg
      apply legal
      rw [hgs]
      exact List.mem_cons_of_mem _ hg
    obtain ⟨k,t,S,hk,run,hs⟩ := extract gs _ tailLegal graph_proper targetIn
    have len : gs.length+1 ≤ 15 := by simpa [Circuit.size,hgs] using small
    refine ⟨k,t,by omega,?_⟩
    rcases all_roots run hs with h | h
    · exact Or.inl (h ▸ run)
    · exact Or.inr (h ▸ run)


def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_neg (f : Row → Row) (a : Sig) : rename f (neg a) = neg (rename f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a)) = bit ⟨j,hj⟩ (neg (rename f a))
  rw [bit_rename,bit_neg,bit_neg,bit_rename]
theorem rename_bin (f : Row → Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b)) = bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename,bit_bin,bit_bin,bit_rename,bit_rename]
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
theorem live_rename {T k t S} (h : Live T k t S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p

def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live hp h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v := by
    have avail : Available ([] : List (Wire Row)) (observe v) := Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv

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

theorem lower_slice {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pT hh ha
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
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)) := by
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



def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k t hk h
  generalize he : ws.toFinset = S at h
  cases h with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      have nk := kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne,rest]
    have sc := (live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail =>
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
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)

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

theorem cover_sound {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → t=0) :
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

theorem cover_required {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  intro hh
  have eq := of_decide_eq_true hh
  have bound := (live_size h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega



def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m)

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

def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available bank (restrictRows f (observe a))

theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a = true) : Available bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,masked_zero dom hz⟩
  · exact Or.inr ⟨true,masked_one dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1 && (c.1==2 || availableB d pool c.2.2)

theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q+1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  have ok : availableB d pool c.2.1 = true ∧ (c.1==2 || availableB d pool c.2.2) = true := by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha := availableB_sound dom hs ok.1
  let z := restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank) := by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2 = true := by simpa [unary] using ok.2
      have hz' := Reach.two (c.1==1) hp ha (availableB_sound dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w) = combine b (restrictRows f v) (restrictRows f w) := by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact available_cons _ (hs _ hm)

def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none

theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q+cs.length) next ∧ poolSupply f next result := by
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

def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB d pool)

theorem poolCut_sound {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws = true) :
    Impossible T cap ws.toFinset := by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)) := by
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
theorem freeWord_ok {roots w} (ok : freeWord roots w = true) :
    Available (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L := by
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
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)

theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := (live_size run).2
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT properG _ eq supp _ (essential_ok ok.1.2) _ L low
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
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
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

def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {m hints L} (h : assertSize m hints L = true) :
    Lower (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m

def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (vars q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


structure BoundPool where
  domain : Sig
  bound : Nat
  paid : Nat
  wires : List Sig

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires ∧ True

theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa using hr,hs,trivial⟩

theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB c.domain c.wires a = true)
    (buy : if paid then choiceOK c.domain c.wires choice = true
       else availableB c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible T k (choiceVal choice :: rest).toFinset := by
  intro t num ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n out)
      (zs : poolSupply f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply out ((ws.map observe).map (restrictRows f)) := by
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
    · have avail := availableB_sound dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : availableB c.domain c.wires a = true := known _ hm
        have point : ∀ u ∈ c.wires, Available out (restrictRows f (observe u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact availableB_sound dom point ha
      · exact Or.inr con

def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires)) && (!extra || choiceOK c.domain c.wires op)

theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {raw T d L cs c} (slice : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 768
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 768 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 768 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 768 → Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b) = if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
theorem faithful_neg {r s x} (h : faithful r s x) : faithful r s (dneg x) := by
  change x.2 = _ at h
  simp only [faithful,dneg,pairSig,ofRows_neg, h]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]

def codeDecor (op : Nat) (x y : Decor) := if op=2 then dneg x else dbin (op==1) x y
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
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
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
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get base _)
      · exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
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

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
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

def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op)

theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Cov
def preCov (ws : List Decor) : CovPair := (coverage false ws,coverage true ws)
def getCov (c : CovPair) (d : Bool) := if d then c.2 else c.1
theorem get_preCov (ws) (d : Bool) : getCov (preCov ws) d = coverage d ws := by cases d <;> rfl
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb

theorem rest_coverage {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un=false → a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb := by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact cover_one d a ha ka

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws := by
  cases un
  · exact (delOne_sub _ _ _).trans (delOne_sub _ _ _)
  · exact delOne_sub _ _ _
theorem len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un=false → a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un || kb then 0 else 1) := by
  cases un
  · have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]

def movedDecor (op : Nat) (a b : Decor) := codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)
theorem moved_full (op) (a b : Decor) :
    (movedDecor op a b).1 = choiceVal (movedChoice op a b) := by
  by_cases h : op=2
  · simp [movedDecor,codeDecor,h,dneg,choiceVal,movedChoice]
  · cases hh : op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,choiceVal,movedChoice]
theorem moved_faithful {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b) := by
  unfold movedDecor codeDecor
  split
  · exact faithful_neg ha
  · exact faithful_bin _ ha hb

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h hk ndc (pair_sep pairs)
  have ce : cap-1+1=cap := by omega
  rw [ce] at sep
  let d := child.length==cap
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  have deq : decide (child.length=cap) = (child.length==cap) := by by_cases he : child.length=cap <;> simp [he]
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 768 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768) = false := by simp [sep]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  have val := moved_full op a b
  change z.1 = _ at val
  change Live T k t child.toFinset at h
  have nd' := ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact closeChild_sound pv lv nd' test k t hk h


def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  evalMove ctx 2 a a z false false && evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false && testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_unary {ctx ws} (h : testAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalMove ctx 2 a a (movedDecor 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPair ctx a b d=true ∨ testPair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
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
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (un=true ∨ v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  cases un <;> simp only [opKeep,Bool.false_eq_true,ite_false,ite_true,delTwo,List.mem_map,
    mem_delone wn,mem_delone dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (unique_value nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem unary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a : Decor} (ha : a∈ws)
    (keep : Bool) :
    (moveFront ws 2 a a keep keep).toFinset = (childOne (ws.map Prod.fst) a.1 keep).toFinset := by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha ha,keep_mem,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv := List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a d kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto

theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    cases h
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links) a b d = true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (testPair_at test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh


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
theorem rotate_excluded {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk h
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
  exact hi k t hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh)%slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


inductive IndexTree (α : Type) where
  | leaf (items : List α)
  | fork (pivot : Nat) (left right : IndexTree α)
def IndexTree.read {α} : IndexTree α → Nat → Option α
  | .leaf xs,i => xs[i]?
  | .fork pivot a b,i => if i<pivot then a.read i else b.read (i-pivot)
def IndexTree.values {α} : IndexTree α → List α
  | .leaf xs => xs
  | .fork _ a b => a.values ++ b.values
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values := by
  induction tree generalizing i with
  | leaf xs => exact List.mem_of_getElem? e
  | fork pivot a b ia ib =>
    simp only [IndexTree.read] at e
    split at e
    · exact List.mem_append_left _ (ia e)
    · exact List.mem_append_right _ (ib e)

structure Forest where
  mask : Nat
  cap : Nat
  samples : Nat → Bits × Bits
  cols : IndexTree ColumnInfo
  autos : Array (List Nat)
  levels : Nat → Packing
  index : Nat → Nat → Option (Nat × Nat)

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws

theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a :=
  raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)








def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) := liftGoal m v

theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val :=
  bit_liftGoal m v i










theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 768) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
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

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (g.cols.read_mem e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    cases h
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h


def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (vars g.mask) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known [] := by simp [Known]
def lanePlace (v : Nat) (upper : Nat) := 2^769*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
theorem broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat = combineLanes (fun _ => a) xs := by
  induction xs with
  | nil => simp [units,combineLanes]
  | cons v xs ih => simp only [List.length_cons,units,combineLanes,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]

def fullMarks (r packed : Nat) := ((packed+r) >>> 768) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i := by omega
      have ge : ¬769*(i+1)<769 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 768 = (a==BitVec.allOnes 768) := by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^768-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769 := by omega
      have di : 769*(i+1)+768-769=769*i+768 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)


abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
theorem top_xor (a : Bits) : BitVec.allOnes 768 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 768).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs := by
  by_cases un : op=2
  · simp only [packedOp,un,ite_true,packedSig,broadcast,lanes_xor,top_xor,movedDecor,codeDecor,dneg]
  · by_cases one : op=1 <;> simp [packedOp,un,one,packedSig,lanes_or,lanes_and,movedDecor,codeDecor,dbin]

def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (un ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) un ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) un ka kb) xs := by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 769) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (masked p.domain)).any (fun v => v==m)
theorem available_mask (p : BoundPool) (x : Sig) :
    availableB p.domain p.wires x = availableMasked p (masked p.domain x) := rfl

def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un || kb) ≤
    (opKeep un ka kb a b ws).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  cases un <;> simp only [opKeep,delTwo,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [constantLoss]; omega

abbrev QuickPool := BoundPool × Nat × Bool
def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p := s.1
  let un := op==2
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := choiceVal (movedChoice op a b)
  let zm := masked p.domain z
  let zc := isMaskedConstant p.domain z
  let cm := s.2.1 - constantLoss const a ka - constantLoss const b (un || kb) + zc.toNat
  let free := zc || zm==masked p.domain a.1 || zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)

theorem fastCost_good {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws)
    (h : fastCost (summarizePool ws p) k a b op ka kb=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true := by
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let free := isMaskedConstant p.domain z || masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest := opKeep (op==2) ka kb a b ws
  have ck := keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2) || kb) ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB p.domain p.wires w.1)=true
  · have hav := List.all_eq_true.mp all
    have ready : free=true → availableB p.domain p.wires z=true := by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have extra : (!availableB p.domain p.wires z).toNat ≤ (!free).toNat := by
      cases hf : free <;> cases he : availableB p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires)=true := by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact hav w ((keep_sub ws a b (op==2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.wires (movedChoice op a b)=true := by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b ((op==2)||kb)+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h

def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)

theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have closed := fastCost_good (mem _ hi) (mem _ hj) ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (contextWire c i) (contextWire c j) c.2.2.1).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl

def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length ∧ j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1 yes.2 h
    next => contradiction
  · exact h
def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then true else
    let d := len==k
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs

theorem batchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  let d := len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((opKeep (op==2) ka kb (contextWire xs[q] i) (contextWire xs[q] j) xs[q].2.2.1).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,len,d,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := if d then packedCov (fun c : NodeContext => c.2.2.2.1.2) xs
            else packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r*(BitVec.allOnes 768).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 768
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := batchMove b xs i j op
  f false false && f true false && f false true && f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false && batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0 && batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow b xs i js && batchRows b xs js

theorem batchRows_at (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMove_at k n xs
    refine ⟨⟨⟨check hi hi hq budget arity allRows.1.1.1,check hi hi hq budget arity allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true := by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,check hi hj' hq budget arity pass.1.1.2⟩,
        check hi hj' hq budget arity pass.1.2⟩,check hi hj' hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩

def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls)


def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : IndexTree ColumnInfo := (.leaf [])
def g15autos : Array (List Nat) := #[[],[33,48]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
def key31l6 (i : Nat) : Nat := 0x820007028af371d000003180048302e380000000003819155875690d58000003d
def g31d5 (i : Nat) : Nat := 0x84001e90fd02fd01fa00
def g31l5 : Packing := (3,1,3,0,4,4,0,g31d5)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,2,4,0,0,g31d6)
def g31samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : IndexTree ColumnInfo := (.fork 2 (.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def g31autos : Array (List Nat) := #[[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : IndexTree ColumnInfo := (.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo := (.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := (.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat) := #[[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat → Packing
  | _ => emptyPacking
def g119index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest := ⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index⟩
def key189l7 (i : Nat) : Nat := 0xa81337040d4b600002948880000590cc33d41450272020001b1
def g189d6 (i : Nat) : Nat := 0x82000f487f40bfa03fa00
def g189l6 : Packing := (3,1,3,0,4,4,0,g189d6)
def g189d7 (i : Nat) : Nat := 0x1f5859bf
def g189l7 : Packing := (1,0,3,2,4,0,0,g189d7)
def g189samples : Array (Bits × Bits) := #[(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : IndexTree ColumnInfo := (.fork 4 (.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def g189autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples : Array (Bits × Bits) := #[(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : IndexTree ColumnInfo := (.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat) := #[[],[101,66,16]]
def g127levels : Nat → Packing
  | _ => emptyPacking
def g127index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest := ⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,g127index⟩
def key191l10 (i : Nat) : Nat := 0xa2d43b28d7001ab368009df79a6668d8a485480048c00a24000002900046192841e000000005078511fa7b8000001d8000000000050332001c2200008044
def key191l9 (i : Nat) : Nat := 0xb5d65558d2140ea31b806b286019a820212fb2e35aa613228a5a077246e6fc20ca1a41bb2d080a9c3e39f318874648000323b01b537426ceae26842215792e4b19e71cc72290229e7cad73d5f333056000d205f83e366a30000000d49821b1f1088000bb771a5c8c0000000000eb0000e0cb6ac6bec3c000c1b800347e18451880000012040006004d1cd8e0000001866e151a0000282800081e2a5e9518b100010bc00000030815564ae0000000000000ba722a1a34000000e6c5a954a6f09e6780014941d61a7112de27d595e7f09e40be3dc9678ab0bf3d70002c438a3dd4912345fe50900b4e481ecbbcceb07786be83e621d46430465b9b583a98309000098f882ae3a444b1d707c001bdad01b2c800179a0001f6d90464c82da1658b094500004b589e042e51604dd58429e06b90ff614389938aaeb6d12bb049522a72f25c09129e0463116174d50c3960b150c0a182d435d81d03dcbc0b346f3525916e494182a5649d22c9002ab560902d0004c5bd2828ce425700001e0842090d9c2ec56f6a2934aac61902201440c3800d7464005040d9808000b00120008008026140608781000c78f2e086830a0c98000580830000a023a002141e004000c001040a00380
def key191l8 (i : Nat) : Nat := 0x18cd14b25011e7225b26001876a3412158c6fc726c2320d6e3243bdd05603f1613ebb0007f7c604089b00125f5892200bf9421800b5e245039f1cf3cb8436d7f2000047800310000002025492575bf0012c00000042000001b8021c00800c01d000c080081
def key191l7 (i : Nat) : Nat := 0x2c
def g191d6 (i : Nat) : Nat := 0x47d6448788a00
def g191l6 : Packing := (1,4,6,0,2,0,0,g191d6)
def g191d7 (i : Nat) : Nat := 0x1021aae2c480c58812165850610304200048200685020d100000000000200100000fce5cec0b2a49f918c877974664f4a45403b36312c2722140f0a0500fd51548d13edd3641903fd51544d03fe92540d02df57305d02ff10305d02df4179dd02bf5819dd02df5819dd029fd819dd02df5155cd019fe885c901fe92440901ff114409019fc8788a009bd849dd039f5819dd02ed6668ce11f56558ce119f47840a11f3a5591200eda668ce00f5a558ce00bb9841ca00fca3388a00fb24484600fd23384600fe22284600
def g191l7 : Packing := (28,3,6,0,2,8,0,g191d7)
def g191d8 (i : Nat) : Nat := 0x850910304081c2440c0e2128f09183458e0d563c424bf1e12406128b1c7846402045834a31022c1244b4112285081c2449f022410c0418818084041a2060210127868c180849614f082043003c28008103c00a001050011a0c10d03085c404064a2030a0610180108a409488504804aab1e40a0610805408d7f063c2499716b62841c098f1800a084818401971629005810a08556544b736241080077f04053c18a8a2824181120efe78c80844603045000e102828008e8b070510443840106263000efe5858a100024042202241d09811e292070e043021810a5c588002801000c0052e2c5001418110006003021810c08516144821810a085042001810afc7897e3c49e14f0a7850604482184f83a8258107f37d67c179c77f77274572070b6f66e16cc6bf6aa69568066b64e63962c61f61a60d5f85e35ce5b95ac59758256d55053b50e4f94d44bf4a247d45843b4264113e43d73ca3b53a039338635934432f3122d52c02b328e27925c24f22a21d1f81db1be1b11a419718217516815b14e13912c11710a0fd0f00e30d60c10b40a709a08d08007305e04903c02f02200d000ffa4c91ffd0548ffe93227ff41513ffa4c81ffd1640ffe83207ff49503ffa2a81ffd0540ffea2a05ff4d502ffae6817fd2340bfe89a05ff40d02ffa2e817fe7740bfe9b203ff51501ffa6a80ffd24407fe91a03ff5cd01ffa0680ffd72407fe81203ff4da00ffa47007fd13803fe89401ff88a00bfceea2dfe774d6febb247f74d923bfcee91dfd7644efebaa27fd45513bfcee89fdd2344efebb207f74d903bfaea81fdd3540eff3ba07f744d03fba4d19fdd168cfee83467f749633fba2b19fdd058cefeb9a05fe40d02fbc66817f41740aff3ba057f5cc02fbc66015fd7100afeba203fd45101f7c8880dfd73407ef19a037f5c901ff20480dfe77407faa2c23fd4d611fea4708ff503847fa81423fd00a11ff209007be44803fc81c01f78ce00ff205007f901803fb08c01fe4da00ff28b007f935803fc92401fe45200ff247007f913803fc89401fe1ca00ff445006de668cfaf2ac67f58ce11f7489007da33803f511401fc84600
def g191l8 : Packing := (100,2,6,5,2,12,0,g191d8)
def g191d9 (i : Nat) : Nat := 0x180327c7c11a70600f8f1304b1c05f0c3c541303017c38f1204e0ef8f13040180df9e0e080325463418a006077cbcf0238c0ef961b3c041381be3e0900df9e30006fcf825f86eb1755933dd9099319085000ff517fd35ff48ffd13ff40ffd02ff00bfd01ff803de33fd847fa00
def g191l9 : Packing := (12,1,6,7,2,9,0,g191d9)
def g191d10 (i : Nat) : Nat := 0x1f3c11ff
def g191l10 : Packing := (1,0,6,4,2,0,0,g191d10)
def g191samples : Array (Bits × Bits) := #[(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]
def g191columns : IndexTree ColumnInfo := (.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (.fork 2 (.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (.fork 9 (.fork 4 (.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (.fork 5 (.fork 2 (.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (.fork 2 (.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def g191autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g191levels : Nat → Packing
  | 6 => g191l6
  | 7 => g191l7
  | 8 => g191l8
  | 9 => g191l9
  | 10 => g191l10
  | _ => emptyPacking
def g191index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 3 0 6 0 2 (key191l7)
  | 8 => lookupWord 17 64 6 11 5 2 (key191l8)
  | 9 => lookupWord 68 242 7 13 7 2 (key191l9)
  | 10 => lookupWord 9 46 4 10 4 2 (key191l10)
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
def g251samples : Array (Bits × Bits) := #[(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : IndexTree ColumnInfo := (.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := (.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat → Packing
  | _ => emptyPacking
def g255index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,g255index⟩
def key383l12 (i : Nat) : Nat := 0xf8400002630000023000000000000000000b83d5688000000000341000030000000000814000015d0000000210344000018d003b10000000000e080000000e70005c3803500091000000000008
def key383l11 (i : Nat) : Nat := 0x404c001fd7a0dd080d1200990f207c017043e0ac430a491c9aec7438f32422a414035a0e000e6f384202824e3e5491f317a0090ee161490000d0e481ce32000c4b9104c1860ad6100030920000000003c06000000722ae38f1200000035c780290bd08d23d219503209024ec0512fd44dc0985ef07266b48508d728f004824e9809324688ad260642ee33843c9e425582082c2260138002f8f81ac0c0002216a57414583e222000012800202204f00400024f34c01300e78608380c041012080080846040
def key383l10 (i : Nat) : Nat := 0x8a7028008f8208641c25de616202731427f0aa3ea6a9bc18603a40bac46606be46000184a7c7d25a0000000b98af69a264a6b01ac3b3a21709000001146294f5b28f5117b2b2368000000119a0000000503689a2858e10b056a96282c8039064ce4000005a1824c4b68b4a1ca0160003a96c1c5108908a005faaaa16a13000042ba8544116a040004b6aa18802880c23178071841517e2559911705a04117c6495c00000000085d314e242a96a0880000a01fc56687256502c84968668866a1180000003d68390f815a1fa922000012b8020000c2a6caf0234475dcf201fa032887c28e092c47a60725df80221bc02a000007a61e192100d1c1f61f683d817642e40874ab202e012c0cd05141d60b104cb094626909c0000000c0e573a858d7326a6285e00010ac0007468e22e50bc16f60921b5c8f41249001273800322800110cb04e0005728622182280ff076809bc29a93800081a596455d1053c0607cc3a5870000108081400524002801c04219100c0821c60cc13c0c2030a201001e00285000001f020030024000800c08280
def key383l9 (i : Nat) : Nat := 0x6977b1303806491384c288005f480044300b4273a470aef249bb09d0238c000000000000000603688ce51876813ab9e6c881d7b37687df408050502a181c84000606800000000000000424bbbaa9612800409100800346576b8a520800702905aa985610b9a10486080010008502020c0020a18085
def g383d8 (i : Nat) : Nat := 0x7c610014028800000000000000302080140040000000a09b827d78736e69645f5a55504b4637322d1e19140f0a0500cef45d94a2103afbaa93760801f7445d0744d03aaf69017618038fb68a9960d01ad76949760c01af34a89760c01af64289760c01adb6943760801aeb69037608018fb6683760801af94683760801afa42837608018ef690988ce009fcaa9190de009fa68a9944e009deaa99504e009deaa99520e009ee690988ce00be6690178ce00be6690918ce00be6690988ce00bf84a83784600bbc6989384600f749de3384600
def g383l8 : Packing := (25,4,6,0,3,8,0,g383d8)
def g383d9 (i : Nat) : Nat := 0x2dd0028c0601f18c02041010022160ac183c0004580028bb3c71c058816e807460680741c30700441602883bd0180c08009e92a09189248391a905315048c4c0a178c440a1c344e20480c5e3ec8c4124f1f67a1c70097c7d918050801b86cae3f18d8123489e81e3f187030392c68303e84a0683078305e30e0607e38f83c60f060a511f174250341f8c5e031010ee21078c3c161c0cee22050c28801004142c00504800c7c3000f402160a08ae97100120112003c70a082689408970b120030209083000c003000838e14007c610001c70838e1020020212004000023e3ec8cb8e14489e2f1a14a23e23d15c47a2b88f457115cca2f195c5e3ecf438e4f9debbcbf80ec1d2799709dd3b93626add2d9db38e63c8786afd5e3b876b2cad6ca75446864ec9992b24646c8990d60abf57bcf1dd3b7e6bccf98f3075e0b6565abd55ea85452734dc95d24a3b45a858ff9f13c6754e39b9356698cc18a2f85dcb916d2be568a61472724d08e918226438650b3138214370570800a4005ff65c1840f7fa2f442077fd9720d01dfe9bd1080dffa6537006ffd329bc017fd9704e009fe44a2e81ddf6541840f7ea300c2077bd94a2103ddeca51081cff6468840ffb20e89a07fd41844d03def4422681cff6241700f5fa2ec3007afc1761803d7e8cb0c01cff65d8100f7ea2ec08073fe99604039fe44a6e80cff65d834067fd32c1a03bdd8320d019fec4a0680cff64e884067fb121b8033fd9760c01dee9bb0600ef70dd830067fd32c1803bdd9760c01dee4bb0600ef7a65830077da6ec1003bec37608019fe44a6f005ef65037802fda521bc017f5190de00bfc8486f004ff22513802efb2a09c017f90904e00bfccba07007f644d03803fb20719c013fc988ce00bfcc9a03007fc406118027f93108c017f8894de00bfd4ca6f005fe46437802ff32e89c01ff11744e00bfc44a27005fea6513802ff32e09c017f99720e00fec89907005fe64483803fb26f19c01fd9138ce00bfc4c467007f645e33803fb02f19c01fd8918ce00fec4c467005fe64c81803fb46640c01ff11384600fed19c23005fe26211803fe26f08c01ff03784600ff849c23007fc8ce11803fe13108c013bd94a210397f4cb0c01cf7a6583006f73281bc017e9290de00bf88c86f005de65413802ef32a41c01fd23384600
def g383l9 : Packing := (91,3,6,5,3,11,0,g383d9)
def g383d10 (i : Nat) : Nat := 0xb1c029771ece80316e3a8b78f40771ca00d1002da03a69a8d16d01d28d4d3292968b98ba7f8c288f4271a30301042b0c2ce3d9d0c753d16f1a58de8639cbb8c715c8d44b554a1a9a3e0a89a12200921586544f91de7c3c6840c59058fc73e70a427a578082339c40459aa8af185209a7d34148d4cb55354aae60605689f215010071ece816c5e382c02c0800b78f67401b1c150a01655c62e06083462ae3d9d02d06c70541505820071ece801e380c14030a8b4a07c8d48497c63f8e66a4b4202e31fc73a14025b571ece863a00201e95c8d50005c7b3a084978e980d957652718d2b8da90a038f655cc3ed026a4b80d9d0683120b8d0ca07c4503e24b0080e3d9d0c73a100400171ece863a2041f8deb9e05d31c9dc29ad59e194d8397a571169d5a94d53c132d2591c5050edce08cf4b60acc9f89047f075c62859452044c3f83242b025c208114003ff45d03ffd1840fff06103ffe8840fff44d03ffd1700fff05c03ffd37407ff60d01ffc83407ff40d01ffe88407ff4dc01ffc37007ff4de00ffc37803ff44e00ffc13803ff8ce00ffe11802ffa2103fdd1340eff60403bfd83406ffa2101bfd83007fe40e00ff901803fe4de00ff837803fe44e00ff813803fe20e00ffa33803fe20600ffa11802bf61803bdd83006fb60801fda33803fc84600
def g383l10 : Packing := (41,2,6,7,3,12,0,g383d10)
def g383d11 (i : Nat) : Nat := 0x540b1d9a02e3804632e686a85e3b342382008507c4a8582c71cf98063b342397069da95ca003fe81ffc03ffa03ff007ff007fa00
def g383l11 : Packing := (6,1,6,6,3,8,0,g383d11)
def g383d12 (i : Nat) : Nat := 0x11b280e4ff
def g383l12 : Packing := (1,0,6,3,3,0,0,g383d12)
def g383samples : Array (Bits × Bits) := #[(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]
def g383columns : IndexTree ColumnInfo := (.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (.fork 3 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (.fork 7 (.fork 3 (.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (.fork 4 (.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (.fork 4 (.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (.fork 7 (.fork 3 (.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (.fork 4 (.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def g383autos : Array (List Nat) := #[[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
def g383levels : Nat → Packing
  | 8 => g383l8
  | 9 => g383l9
  | 10 => g383l10
  | 11 => g383l11
  | 12 => g383l12
  | _ => emptyPacking
def g383index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 17 68 7 12 5 3 (key383l9)
  | 10 => lookupWord 57 200 7 14 7 3 (key383l10)
  | 11 => lookupWord 30 108 6 13 6 3 (key383l11)
  | 12 => lookupWord 6 61 1 10 3 3 (key383l12)
  | _ => fun _ => none
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3 : Lower (vars 3) (graphGoal 3) 1 := size_of (hints:=1) (by decide +kernel)
def maps3 : List (Nat × List Nat) := []
def known3 := extendKnown [] 1 maps3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3 : Known known3 := extendKnown_ok baseKnown low3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 2 := size_of (hints:=257) (by decide +kernel)
def maps7 : List (Nat × List Nat) := []
def known7 := extendKnown known3 2 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7 := extendKnown_ok valid3 low7 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom15 : graphValid g15 (boundsBefore known7) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s15_3_0 : block g15 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl15_3 : block g15 3 0 1 = true := s15_3_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact bl15_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower (vars 15) (graphGoal 15) 4 :=
  lower_forest (g:=g15) (i:=0) (hints:=8449) (before_sound known7 valid7) geom15 tables15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat) := [(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def known15 := extendKnown known7 4 maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known known15 := extendKnown_ok valid7 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45 : Lower (vars 45) (graphGoal 45) 3 := size_of (hints:=8965) (by decide +kernel)
def maps45 : List (Nat × List Nat) := []
def known45 := extendKnown known15 3 maps45
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid45 : Known known45 := extendKnown_ok valid15 low45 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low51 : Lower (vars 51) (graphGoal 51) 3 := size_of (hints:=1) (by decide +kernel)
def maps51 : List (Nat × List Nat) := []
def known51 := extendKnown known45 3 maps51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid51 : Known known51 := extendKnown_ok valid45 low51 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known51) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_5 : block g31 5 0 3 = true := (@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_6_0 : block g31 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_6 : block g31 6 0 1 = true := s31_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact (rfl : block g31 4 0 0 = true)
  · exact bl31_5
  · exact bl31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower (vars 31) (graphGoal 31) 7 :=
  lower_forest (g:=g31) (i:=0) (hints:=8449) (before_sound known51 valid51) geom31 tables31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat) := [(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def known31 := extendKnown known51 7 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31 := extendKnown_ok valid51 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 5 :=
  lower_discard (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (before_sound known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat) := [(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47 := extendKnown known31 5 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47 := extendKnown_ok valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 5 :=
  lower_discard (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (before_sound known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat) := [(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55 := extendKnown known47 5 maps55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known known55 := extendKnown_ok valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_discard (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (before_sound known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat) := [(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63 := extendKnown known55 8 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63 := extendKnown_ok valid55 low63 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom111 : graphValid g111 (boundsBefore known63) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s111_6_0 : block g111 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl111_6 : block g111 6 0 1 = true := s111_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact bl111_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower (vars 111) (graphGoal 111) 7 :=
  lower_forest (g:=g111) (i:=0) (hints:=16785665) (before_sound known63 valid63) geom111 tables111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111 : List (Nat × List Nat) := [(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def known111 := extendKnown known63 7 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111 := extendKnown_ok valid63 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  lower_discard (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (before_sound known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat) := [(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119 := extendKnown known111 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119 := extendKnown_ok valid111 low119 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom189 : graphValid g189 (boundsBefore known119) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_0 : block g189 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_6 : block g189 6 0 3 = true := (@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_7_0 : block g189 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_7 : block g189 7 0 1 = true := s189_7_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact (rfl : block g189 5 0 0 = true)
  · exact bl189_6
  · exact bl189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower (vars 189) (graphGoal 189) 8 :=
  lower_forest (g:=g189) (i:=0) (hints:=536879876) (before_sound known119 valid119) geom189 tables189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps189 : List (Nat × List Nat) := [(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def known189 := extendKnown known119 8 maps189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known known189 := extendKnown_ok valid119 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 5 := size_of (hints:=1366507616) (by decide +kernel)
def maps250 : List (Nat × List Nat) := []
def known250 := extendKnown known189 5 maps250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid250 : Known known250 := extendKnown_ok valid189 low250 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  lower_discard (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (before_sound known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat) := [(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127 := extendKnown known250 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127 := extendKnown_ok valid250 low127 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom191 : graphValid g191 (boundsBefore known127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_6_0 : block g191 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_6 : block g191 6 0 1 = true := s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_0 : block g191 7 0 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_7 : block g191 7 0 28 = true := (@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_0 : block g191 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_8 : block g191 8 0 100 = true := (@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_0 : block g191 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_9 : block g191 9 0 12 = true := (@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_10 : block g191 10 0 1 = true := s191_10_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact bl191_6
  · exact bl191_7
  · exact bl191_8
  · exact bl191_9
  · exact bl191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower (vars 191) (graphGoal 191) 11 :=
  lower_forest (g:=g191) (i:=0) (hints:=536879361) (before_sound known127 valid127) geom191 tables191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191 : List (Nat × List Nat) := [(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def known191 := extendKnown known127 11 maps191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known known191 := extendKnown_ok valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 8 :=
  lower_discard (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (before_sound known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat) := [(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251 := extendKnown known191 8 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251 := extendKnown_ok valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 12 :=
  lower_discard (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (before_sound known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255 := extendKnown known251 12 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok valid251 low255 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom383 : graphValid g383 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_0 : block g383 8 0 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : block g383 8 23 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_8 : block g383 8 0 25 = true := (@block_merge g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_0 : block g383 9 0 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : block g383 9 84 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_9 : block g383 9 0 91 = true := (@block_merge g383 9 0 84 7 (@block_merge g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_0 : block g383 10 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : block g383 10 5 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_10 : block g383 10 0 41 = true := (@block_merge g383 10 0 21 20 (@block_merge g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_0 : block g383 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : block g383 11 1 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_11 : block g383 11 0 6 = true := (@block_merge g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_12_0 : block g383 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_12 : block g383 12 0 1 = true := s383_12_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g383 0 0 0 = true)
  · exact (rfl : block g383 1 0 0 = true)
  · exact (rfl : block g383 2 0 0 = true)
  · exact (rfl : block g383 3 0 0 = true)
  · exact (rfl : block g383 4 0 0 = true)
  · exact (rfl : block g383 5 0 0 = true)
  · exact (rfl : block g383 6 0 0 = true)
  · exact (rfl : block g383 7 0 0 = true)
  · exact bl383_8
  · exact bl383_9
  · exact bl383_10
  · exact bl383_11
  · exact bl383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower (vars 383) (graphGoal 383) 13 :=
  lower_forest (g:=g383) (i:=0) (hints:=12901687553) (before_sound known255 valid255) geom383 tables383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat) := [(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383 := extendKnown known255 13 maps383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known known383 := extendKnown_ok valid255 low383 (by decide +kernel)
def hashdeadl14 (i : Nat) : Nat := 0x4592c8500000000002800049a6c68a83340e9800000aa00684000000054a001bcc7001e180000682000000000000001d46a1840000003a00000001c
def hashdeadl13 (i : Nat) : Nat := 0x301a0007b2f00e0aa2992094818000e2e0000000269e056438000000000d33e40e4a200074d00000000000003b10001e0240a9bd45d962582900000000000001430001e1400000fc03b84a000614e69108a1108000810000d04c9d0000000408800000160f24180010b9d040003080001e0c000000000001997f401183740ee12000000000080d312c00102c00000000012070000000001d35000308c000a4c0001b30000000cb3800183000070f0000001abcc008002c8cc133000000000000000000000020b000000064ec0a00000f8000cc5000105d8204160001a38001c1c467309c000000a7700000016de30f80000008380b08e000d3001
def hashdeadl12 (i : Nat) : Nat := (if i<1 then 0x7b02c3200425d610a000042a0327300000000106b33757005e04600006037d811679d009461963480703e1077f067f2582384275d80a540a20109b59b4006305d00000000ab6dfb0bf59ec084c806986b30597776440b146b100c50a956520000878e0000747c463e108bc029e7600000395ef090d06800000000f0550000d0b1e4af00000000f324d141840ca4380000000051505017000067300000e779907b0000e77730641201ea62a089a48ff0924111e9a7a041b2a180aee462f29d9b47b01eb0427030e02a5973605b9086f08d5081d04bb014363000006038c0b6d110106cc731308e0023a07fb1305601ba1839b4c088a10b88011043e427e75a600831464016903d3ba52b1ec095000ec050b011b0730478f11a0000755e331ef63db004a00a000069a91680e225f60f90092a9d0000764650a40000c591f95ac03baa33c5a1283d11871a6d2772c01c1057280f201f5012328b908232a5505e000fe02b507cf0809817c267c05c9528506d997696872194b206264030ad402d007d586d7228701d30605840f67838625a51443ce034d47ed45f704cb08730a1794e1252000070330000b56f0000b0b4000000000000a842e047609d406ae26b67b08a4de12aa0a34019000000000000b664342c50b50000c0af924dc9aa401870366002b26d00000000841e0000000060986614000000000000783ae10d980ee051d0ab4022a615808f0000a0832619a148d81500007000e007d616b032d01b483f163f00104028276b2015141030631049a027580cd0a7a05ab977802fb09ff07a97899053b0a80816e83be0790a1b809b8b460a4f0000178b0000847be03cf139a1170000b07850b3605408416262696b908af0aa7b1f5b446070d024601a42492101d496f4b4e035922127ab0000e18600008284831c00440000f031500310656013b071b045b25b4113766b5b4c6b0800008291b4888a50000000000000e38b0000225eb04d807230618425c0b097ae226f809e00000000f00d93480485e88728040000b11c3039204e9432711f445c905f004a300b97ada05680211292f09a7b1a696f3106704f19748066703f00000204d074ba20a118f025458794596091a06f000065946020913b783e342dd08c819b5b452076c21dc075e0991a4a183c3b19d7a750a68058c8379643a487b408d0523762d062b422e0b2d47fc0ac224a46231a5dca3b6069a4390000768a5433e07e0000da410b00003102090604000a010a1f88080000080d030b0c310304001300040113030203141f0c0001000232030b0801010a010007110002020208010605020401010119010b0304070203070506000210070d110100150b0a0504051d050002020b05000c0402003d0e1500260200020108040b03090500060204000d0602010100180501000001030f04 else 0xe0a0512830933085c048e216509713746026a02ec09cb040548400000268f701103ac254729fc29e8096145a39ab47552144806e00019612b7b4491ea44bc1)
def hashdeadl11 (i : Nat) : Nat := 0x5b144463e05aea749a36008e0000f05f008fc82400000000057a08357304bb42c02b0000807cd1701823000007095811411b96631031e07218223334c77b980e8010305dd000180820521064ca3ef0420000409b626cd483a833f03ac022e048a008f80a513f0000db73410f3393ca38834018881012b081c465a02c6142704300002631809700000000715300007115b00dd054b2886014000054161b183099000000000129f0870000a24110110427972915960000477d5b457113518aa01a00007134a023d08a1053002d678ef06b604a6076520f5468b025698fe62d5060c1370000e07eb793c95be02a510198285417000000000000000000005b72220ea00f9098e036e09602120000503908396112556c56084a3a211d0342f0784635707b4293308d0624205556235211962a72516903a0190235010e7765e07d5784f16feb3c248834149073d088b0134091f720f0803275f0052809446ed494b01b1b0305939136b20cf495111aba390000db890950e9807026e609a0205015880ba66b8778d4967988f077f007110cd289d0160000e278401d0000000000000000f032027400000000a08c6209804c4030102eb368a33f3b1d798e0000538a70215061a44e228300000000000000000000d01710838075e4517067406f00000000609a00003253a089a4002093b00a8125000090790000c0599583180c00000000c0411830f1160047224900000000906992725046700b000050511a67544b00000407c35bb06d0000504d3821ca470002762e0000cb1760948827b10a603b4009e06552019464444f9688a0286169097ab82524185057db2feb3d000e6303670ac01e70822426b090d664c05cf764008be03c365d6a2549347068706a71244461f086277c5780380d698dd120b27c20626037d807f403502fe1110000ea6e5071301cb0388044704f411c809595011003b20deb1a98372208b0561092820a91190049704bb03ec070670890335001a03f64504063613c50294b430832441aba46e146c8120193598c103df8314066401fd460e0745084044c100c7760b24b824f4006205b0000563070507a7c9058000000006a440000506e3040e97d006cd027646a6207807fb0450138e56fa018704e8482e0356085662f762c5b3be05eb81f1004f836000000000000000046203a6ac89692730000b034807a613d00008145702433536a79b0407805012a04e80082c50a0c0e782286421a0e4c00400004833a1491a02243880c0851202004211c6408c1835c192e081800c39681005000c04e408002001860c34c8040000000400008087400400100892c38005148410524200800478080001438126000000020022
def hashdeadl10 (i : Nat) : Nat := 0x1c05302000382d2ecf474c3a08f618409ea54931a0a2272b385214e934380040192451090d15cc0564307983441ce005970002c06068f08a82680cc070001a2c5d4a1440400018207150002808001022205d856c41e1700072d518800084a2900000a334a12801820030b1a27
def hashdeadl9 (i : Nat) : Nat := 0x202e0
def deadd8 (i : Nat) : Nat := 0xa24b7baf6624ad253281df927589c4d52540d02
def deadl8 : Packing := (2,6,7,0,4,3,0,deadd8)
def deadd9 (i : Nat) : Nat := 0x17a6100d01602e1f830400f202c200003405840f980801c0010720e8006a183c001d000f8007c00200001509fc5a0b0071b79b2bc5ba99429c459e8d258238d84a14078280a00a7becc495a4a6503c6fdb66689a4d50287fcbc661a544d029ef9c6aed1840d02bed9c626d3540d02ff49184d52540d02ff489c4d52540d02d7f11826d1540d02ffc1184951340d029f6cbc4a1354950195fdc7aed2564d01ff49384d52540901ff61384951540901ef4935496aa40d02df49b54951340d02f7493549503a6502bf62cc4951540901ef6125456aa40901f7612545502a6501fb61284612545600fbc1284612344e009dd9c7aed258ce009ee9c6aed1888a009df1c7aed2584600ff42558ce2284600
def deadl9 : Packing := (25,5,7,1,4,9,0,deadd9)
def deadd10 (i : Nat) : Nat := (if i<1 then 0x2693540b3fecd1349aa055ff26d1a4d502cffb30d2a26815ffabb4610340bfec8c26a81a05ff626d3540d02ffd23092a06817ff1184550340abff5da6b4ca059ff4d5a1a65029ff9569426a80cffdb8aa9354067fed95549aa03fdb4a13549501affb7092b2680e7fda849593407bf69424ac9a035ffaed2564d01cffab15532680e7fd25aa993406bfedc26ac92035ffaed3564901cffab0d1b2480e7fd38aa9924073fe9ad54c92037fe6e13540901fef2b09aa0480ffd9384d502406ffd5da6a81203ffa4e12540901ffe2708aa0480f7f95864d02406bff5da714ca03df74e135a6501affd769ad3280d7febb49699407bbe9aa4b4ca035ff6e123a6501efda5091d3280d7fdb548e99406bff5da474ca039ef495a4a65038ffb63553308167f9b0aa998408bff5dd54cc2053bf6daaa461028ffb6a4d2268157fabb6610340bbf4cc24a81a055fe26d1540d02cff33155206816fd935aa90340b7f492d5481a057f66d51340d02ff924a89a06816fdaaa44d0340b3fcd42074ca05df64d503a6502efd24a81d328157fabb40e9940bbec89a074ca059fd461a1a65029bfb6f5524a80c7febb6a1934063fedc554c9a031ff6d6aa64d01cf7b695532680c7fdb2aa9934073fcd8554c9a031ffaeda8649018ffb6ad1b2480c7febb68d92406ff55da4a81203fda4d52540901fee34a8aa0480f7e92564d02406bfd5db2681203bfa496aa40901dfe22b5520480e7f993aa902407bf492a054ca03dfc45502a65019ff36755251004ff9b1aa928802ff55da5092c01efa4a11849600dfd2515524b007f692849515803fb88c24a8ac017deaed2545600def55492a2b004ffabb6a123802ff55da5091c01efa4a11848e00dfd25155247004ffabb6a1138027fc55a5089c01afe6a12844e00bfe5768c227007bf128461138027fd5db4a89c01bde6952544e00dfe23155227004ff9b8aa9138027fcdad5489c013fe6caaa44e00ff925091a27007fd11848d13802fed5da4689c01bf6aa92344e00bfb57692c67005fdabb45633803fac92a2b19c013feaeda844a009ff370d2a25004ffabb695128027fcdc346894013fe6d5a344a009ff576d1a25006ff1a844d12802ff95da2689401bf66963344a00dfe22755225006fda33aa912802ff55da71114017faaed1888a00bfd3709ac45007fc9384d622802ff55da6b114017fa6e11388a00ffc23089c45007bea8844e22802ff4daa27114017faaed1388a00bfe5769c423007fd1384d611802ff95da6b08c017fcaed2584600fee26a92c23005ff1b848e11803ff09424708c017fc6d52384600bfe57691c23007fd1588ce11803fe89446708c01ff44963384600ffc27111423007fe13588a11803fa49aa4a81a05fd849515409019bf36f5524b007bd2888ce11803df14444508c01ff08ce2284600 else 0x4000888405e986c113905805080340b02e1f06087905c2003f080d05c2010004400c0288128f50060048004020800804100127c503a3f6c170230c990618643002074409038882341900e30020304004060800870140c00228180045c08224a09086c45817020801a183810008ad48702001100108e2b0c1c0800456383810230b0200117dff6de0be2c10281f00a20021f8a108140c707c503e3f8bed83901520010dd505020c988c1183426000e000e00086905c20a40d058002020340034003c1834002fd2040bdb798060306e1b00c84f01a5f8a10bc3024202bf0c090605c00880505210010fc506e1cc0693effc5f6de600097e28190cc11092183f1414080603412860a40cc6004380038003800340034003c003c0020e00107000f000801c0020e00100f78ee2192287800ec3041c003c00361820e001f8a1e001e001e00100000b0411ef1dc4377ae886cc5917b60fc50f000d8e083e2840000016a420f6c1b1c100000b521002c30416383f1420003e284000100c4aca220cd523db61a02c91b20b40600a0dbf169c61a02c9f6de60578fe2fb6f303f8bedbcc0fe2fb6f303d0acfaceacb9c93c83c68c63c53c38c1dc02bd1bb6b9bb96b70b4ab24b09aeeac8aada92a77a5ca41a31a169fb9eb9e69e19d19b69a698b97096094593591a8ff8c38a889887284c81b80b7f07bf7af79f78f7747597497397297197096f96de6b867c64b62560a5ef5df5ae5725415315164fb4d54c54b54a549548547546545545044043b42b41b4164114013fc3ec3e73cc3a639639138137136135c34c33c32c31c30c3073022fd2f82e82cd2b229728727726725725224223d23823322e2292192142041f41ef1ea1e51e01d01cb1c61b61b11a119118c18718217216d16810009807204c026000affd7692d3281defdb6)
def deadl10 : Packing := (156,4,7,5,4,12,0,deadd10)
def deadd11 (i : Nat) : Nat := (if i<1 then 0x86120d08111f407ad1db072b1c206d11ab867718d8613174859115b85231388497118042910183c50e603570c082b709d822b07a8195055010902a80410003ffd1849503fff6692540fffd2546503fff4613540bffd9a4d502fff2693540bffd1a4d502fff4619340bffd3546502fff4d69940bffd9a4e101fff6a135407ffd284d501fff4a935407ffd9a4d501fffaa935407ffd3849501fff4e925407ffd9a49501fff56123407ffd9a48d01fff56193407ffd2864d01fff49593407ffd5864901fff4e192407ffd3564901bff6a11940f7fd9846503dff6551940effeaa46503dff4a51940f7fd25a6503bffaa99840b7fd1a66102dffaa99840b7fd9a46102bffaa91840bbfd9846102dff6619340affda564d02dff6559340affeaa64d02bff6951340bfdd9344d02ffe6a10340bff99840d02ffe4610340bff9a540d02ffe6550340bff91540d02ffe4690340affda846502dff6611940affda346502dff64d1940bff90346502dff6629940b7fd93a6502ffe40e9940b7fd18a6502dff4d69940b7fd13a6502dff66935406ffeaa4d501dff66925406ffeaa49501fdf4d525406ffda864d01dff66193406ffeaa64d01dff561934077fda864d01dff4a1934077fda564d01dff495934077fd2a64d01dffaa993406ffda864901dff66192406ffda564901dff65592406ffda364901dff64d924077fd3864901dff6a1924077fd3564901dff68d92407ff95840901ffe4e102407ff9a840901ffe66102407ff93540901ffe69502407ff99540901ffe68d02407ff99340901dff4e2994077fd35a6501dff496994077fd23a6501ffe4e928803ff91a4a200ffeaa928803ff9a849600ffe46125803ff93a49600ffe46925803ff92845600ffe4e915803ff92a45600ffe6a123803ff91848e00ffe69523803ff91548e00ffe46923803ff9a844e00ffe4a113803ff9a544e00ffe49513803ff92a44e00ffeaa913803ff95844a00ffe4e112803ff9a844a00ffe4d512803ff9a544a00ffe68d128027feaa661029ff2693540a7fc9a44d02dfe6610340bfd93540d02ffa4950340affaaa40d02ff644d0340a7fda8a6502dfe40e9940a7fda3a65029ff6869940a7fda864d019ffaa9934067fda8649019ff68d924067feaa64901ffa49502407ff11540901dfe64d02406ffaaa40901dfe40a99406ffaaa4a200ffa4a125802ffaaa49600bfeaa915803f792545600bfe6a123803fe92848e00bfeaa923802ff9a844e00ffc46113802ff9a544e00bfeaa913803fd92344e00ff649633803fd9158ce00bfe6a112802ff9a544a00bfe68d12803ff11344a00ff68cd12802ffaaa44a00ffa4e222803fe91888a00ffa4d622803fe91388a00ffc4e211803ff13584600ffc49611803ff123846009ef6929940fbea8888a00ff48ce11803fe22284600 else (if i<2 then 0x6718d1b071686b63b38c6ac837ab208143ea5f4a804c20460a84911c7405186a093027a82ae19d57d066c694fa70dcc0ac4ea478ce31a1ecaeaf303c8c241ac2f19b38c69c83fbee47302190238ea2305424c6856399d2085637d12388c0c16cbeff1d208076416c80b40c0049e29d5208144b23f46802b201800c183275231bc58d5919c2ba9ed854030806003067bf9c352078df64634afd056e600c20020b418eaf319c182b832c8683382f1c2de703e3ac80ac412003efc19433aad06707f7f38754282036168bdf159a0ce09fa590158824f17a919786904bef86bc33ab209458f7dd8e39c8904deff5232b9120958e0b701b7e8611b1e288d8776dd9609e2b1c2f1582105b80098e0b90124824976d090cd009250909820be81c002d484d8f144c3068ea08444c12222609117812260911961224208de83785dd4e900b63480dfc5edb981b80c307224fbfd4f301f09477d2a0d202e2010188cddb353cc69017202256222f7fb60add5a80164f6c116903054660bb98d200c6e0e18f8afa73037818602100ed9a0d20beff8bdb752d00186f7fc5ea78e6e01e33bfe2f534770c056718d202388c2401066f7fc5ea68ee1b388131a6862ef8df646718d182bf7fa963ac8ce31a3fbfe2f6dd4f31c70187010d8f7c2b7561a05a04ce121581816fbfdb3530d74005590a1982b682c8ce0be2f6dcc0184f14410307c705b875e98d59067d2d5c686717058176d8d1b06f7c92f17b6e602d3634e457030b7007d2a0b20be2be9500fdf0b7b6c68d029b1803bfe2d415c1bc57d2a01fbfc3600ead415c1bdf363c5c6a8eae0d8d3915c0fdfe0b00ed9a9a81c83fbfc3600ead40dc1ba9e3b0e77f1ab22b839c4d4e356457053ab00682c8ae0bdb341640fdfea700682c8ae0dd49c58d1bc4ea782c02c87d1a03753c751d873bf64634dc23dfe0a86c03b6755a03fbfd4e0164340dc1a82ea786c03c57d1a03fbfc36015c3aad01bdfe3a8ec3ab86a71a7211eff5380570d03906f7fc5edba9e1b82040ec751d87590fa7538d71ddc2586a198ec1bdff16b8ea71ae195efb915c7ab8d74068ed23878d423198bda2f18b3a2a189fa24788e221f881a1e387521a785ea14384820fd83ba0cb82a2071816203f8099ff97ee1f8b7d29f137b21e9179b9e377829ddd76c1d8d7581d3373c9cb17239c6170f9bfd6f41ba36e01b536c99af96b31a9f69c9a4568619f5665990f63618ab610981f5f517935dc17435c0969959b163558495c7566954f54b14f552f949151914374f393a14ce130b4b2929349c124347e11cb46c9185456112143a90a941c9063415103b4088ff53f70fc33ea8f9b3e30f7d3d68f4b3cc8f233c50f053bd8edd3b38eb53a70e8339d0e5b3930e3d37a0da73570d2f3368c7b3160c0d2f30b952d50b132af8a3727d89ab2580901226 else 0x6c244e0445e2e80648bc5050262048e47300a0565ed8f60346f5d8ae98260a0c0068580a0c27015b807c906026158e08c030604c2b2a82103cee10cc378bc503c5a1a381a3a2d03cb121b082409e29104f14d80b00b29b02601632490481068e0401093981802127303093987200a0aca00c1820060c1003060ba9e62b81ec8b40d15c753cc0a26ae1d5e606624740ac47cc0483c9bdf72398ae02b28b1eff6cec705e2c44719c65bd0520ccbd4b702a0c67030651f4282f8a37f6c0f90083dbc507c95c01a2901847d2a015c7efbab500764fd1d5a800524460a84613d40171bdf12bb67568e07cc1703e060df4d22a00b883dd40220c2777c2ed22a06e0defe90110884fd1d5a800526915008831e748a802e219d5c0560f91f4ea40c1509ef89ad00884fd0566800c25702b3400611df1500c10c813b1c0f00a44001e0b8625494a83ec3b7532876c0fa40c07c018307cf7fb66a40f0d782d231a682c8a82a1e8185ce3c519b1a206a008183e7be5a8cd9c5ab50287af14281809827bfc7))
def deadl11 : Packing := (183,3,7,8,4,14,0,deadd11)
def deadd12 (i : Nat) : Nat := 0x226c48bbfb654c3991828d28cddfe2ea731865c0891b87a0bb538ea405a3487b1d9bfa906e3a90b8064694310477f6ca947523051a4f7f6c2ed4a3a91828d23bfa90b0351c15a42e0191a577f8ab8d4e631c0c3f7e91b6d4c6b1c0c3811c4dfe2ea51d869c41234a020c7bed54772271048d2408d8efaa71cc89c4123490277f528e4932271048d27e9c5d4a830c011d1fe8c8d4907400c377f8bb6d4e1b04223bd3538ea46e23461177f6da950523047efedb538ea4608191a477f8ba94761a711a3f7f538e644e0191a3f7f5398d032019383963e9c516e8018413c39e9a98d63991b83b6205dfdb2a635a0646093df6ac6b41c816ae0f00efedb52a0493230488077f8ba95061970704f7f531ac732112b842091d02eff176da98d61b04a4140bbec8db6a6358ec1250d06eff1571a98d6830c994a8fd8b08517fb7ae74f70b6c76686125bc5665224e74a34684243d739334f30b2c728322d1e919c15810b0ac056000ffe92a07ffd1940fffb30817ff46102ffe9aa05ffd9340bffa26817ff46502fff4ca05ffd38407ffa6a80fff49501ffe91a03ffd93407ffb2480dffa6503bfecc205ff90340affd32815ff64d01bfec9203ff902406ffd3280ffe4a200ffc92c01ff915803ff247007fe44e00ffc89401fda33803fd445007fc84600
def deadl12 : Packing := (32,2,7,8,4,12,0,deadd12)
def deadd13 (i : Nat) : Nat := 0x22dfc5b6a90e86821a4efdb54c724410d1f7f16a63a18e01069005bf8b6d52351d0d049cf924d00ffd03ffd02ffd01ffa00
def deadl13 : Packing := (4,1,7,5,4,8,0,deadd13)
def deadd14 (i : Nat) : Nat := 0x17e2b6526070604013ff
def deadl14 : Packing := (1,0,7,2,4,0,0,deadd14)
def deadsamples : Array (Bits × Bits) := #[(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadcolumns : IndexTree ColumnInfo := (.fork 63 (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (.fork 4 (.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (.fork 8 (.fork 4 (.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (.fork 4 (.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (.fork 4 (.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (.fork 8 (.fork 4 (.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (.fork 4 (.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (.fork 31 (.fork 15 (.fork 7 (.fork 3 (.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (.fork 4 (.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (.fork 8 (.fork 4 (.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (.fork 4 (.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (.fork 16 (.fork 8 (.fork 4 (.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (.fork 4 (.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (.fork 8 (.fork 4 (.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (.fork 4 (.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def deadautos : Array (List Nat) := #[[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def deadlevels : Nat → Packing
  | 8 => deadl8
  | 9 => deadl9
  | 10 => deadl10
  | 11 => deadl11
  | 12 => deadl12
  | 13 => deadl13
  | 14 => deadl14
  | _ => emptyPacking
def deadindex : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 1 3 0 9 1 4 (hashdeadl9)
  | 10 => lookupWord 17 61 5 13 5 4 (hashdeadl10)
  | 11 => lookupWord 124 434 7 16 8 4 (hashdeadl11)
  | 12 => lookupWord 137 475 8 16 8 4 (hashdeadl12)
  | 13 => lookupWord 26 148 3 13 5 4 (hashdeadl13)
  | 14 => lookupWord 7 47 1 10 2 4 (hashdeadl14)
  | _ => fun _ => none
def dead : Forest := ⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,deadlevels,deadindex⟩
set_option maxHeartbeats 0 in
theorem geomdead : graphValid dead (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead8_0 : block dead 8 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead8 : block dead 8 0 2=true := sdead8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_0 : block dead 9 0 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_12 : block dead 9 12 13=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead9 : block dead 9 0 25=true := (@block_merge dead 9 0 12 13 sdead9_0 sdead9_12)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_0 : block dead 10 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_6 : block dead 10 6 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_42 : block dead 10 42 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_78 : block dead 10 78 35=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_113 : block dead 10 113 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_149 : block dead 10 149 7=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead10 : block dead 10 0 156=true := (@block_merge dead 10 0 149 7 (@block_merge dead 10 0 113 36 (@block_merge dead 10 0 78 35 (@block_merge dead 10 0 42 36 (@block_merge dead 10 0 6 36 sdead10_0 sdead10_6) sdead10_42) sdead10_78) sdead10_113) sdead10_149)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_0 : block dead 11 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_4 : block dead 11 4 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_40 : block dead 11 40 15=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_55 : block dead 11 55 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_91 : block dead 11 91 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_127 : block dead 11 127 29=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_156 : block dead 11 156 27=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead11 : block dead 11 0 183=true := (@block_merge dead 11 0 156 27 (@block_merge dead 11 0 127 29 (@block_merge dead 11 0 91 36 (@block_merge dead 11 0 55 36 (@block_merge dead 11 0 40 15 (@block_merge dead 11 0 4 36 sdead11_0 sdead11_4) sdead11_40) sdead11_55) sdead11_91) sdead11_127) sdead11_156)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_0 : block dead 12 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_3 : block dead 12 3 14=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_17 : block dead 12 17 15=true := by
  apply cellsBlock (ar:=11) (rows:=1) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead12 : block dead 12 0 32=true := (@block_merge dead 12 0 17 15 (@block_merge dead 12 0 3 14 sdead12_0 sdead12_3) sdead12_17)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_0 : block dead 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_1 : block dead 13 1 3=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead13 : block dead 13 0 4=true := (@block_merge dead 13 0 1 3 sdead13_0 sdead13_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead14_0 : block dead 14 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead14 : block dead 14 0 1=true := sdead14_0
theorem tablesdead : checkedTables dead 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block dead 0 0 0 = true)
  · exact (rfl : block dead 1 0 0 = true)
  · exact (rfl : block dead 2 0 0 = true)
  · exact (rfl : block dead 3 0 0 = true)
  · exact (rfl : block dead 4 0 0 = true)
  · exact (rfl : block dead 5 0 0 = true)
  · exact (rfl : block dead 6 0 0 = true)
  · exact (rfl : block dead 7 0 0 = true)
  · exact alldead8
  · exact alldead9
  · exact alldead10
  · exact alldead11
  · exact alldead12
  · exact alldead13
  · exact alldead14
def hashlivel14 (i : Nat) : Nat := 0x10e82a01d31c8764db22f821488c05f28481b6936ec771800141e0001051038000000000283048e0004048002082c494004b910964406a18ba4000000d701d2c000000508482c0017442008000001c0d201281c000000026292800140300050115d600008228d045001040081000003
def hashlivel13 (i : Nat) : Nat := (if i<1 then 0x4000000015e2c829c000000019d9addbc8188000000000001c3c80000000088cf41a66834020440ad6a56c2d89dbbc2b740e7e9ade82fc23bc32c00000000000109af8271caa0c3200000e9f8290c00000001503400000003c1edc3c40003df98c0459d6082b909fc81e00001409800000001caf8000142c0013acb69822400000003836880ca9c31ca80000381759ce0000000001e0a8bc8ab0a2ba06a37400cc336aa1382780003490400020338a9dc00014935494f03b800611c59038800004394c1acc03b1d640002c22c0003ab114018417c000301455e42c377cb3c298403d602fd492d40934983c2980001095cde06dc7f41d6828383618a18e98c000000030929c9220990de311fd28233c9540003019cc9270088df300000000000000a240000000248c40002693ec958e9e6e9b2c3d009c4425e001e28d40073c1da09d25da6c1600003a85b5604c0f3eb99a966282389f783aa69b4a9cc82b10111c810dd7e003000008999089c0a029cc1c9a2c2cbc0c528e0837fc8dc01c900aac3a7ddaa284c41911e8e82f64127899ddc5c0001c9fb5f96836c89f28008000002140000c1a00001209f8b624b5c00006890eaae431c000000009cf94a4be9f60ac2df1200de5cf080e84297881d42fa81400010c0d51cc84223c35e4aaa02a300b68898000000000002031441680002eb4000001ceda89fc1c5c18f69146b2b697c000000038106810800008b3182e40000000083bca9d800019dc000000129824d4bbca8468a11813643080000023f0a08425489534942815bc1b228bf9ec9ca1c0002c80e5e80c103424100b80001cacc0003c2aae850000000000001438c0000027c0001c34e0262432a0014000329ee03af012c00000000000208421f68000142ec085b022828e429c9019b0a5de901c2cc00020966c3cd00042607eabd4997c14c000180b2829381840000000042180000000000000000c081c2654097a8e8037149ec00030818415fc853c0ecc11b811dc87b035800038834c2740003a85ec9a800000002c86c0001589ddf21a9a8c85e820c0000412182580001dcdb007c00025eff9f1d43800000000000000000aaa9414bc0640000c862493c000000034181890e5e4c00000800c0e0001000400000040000100c010280400c010541000434010020040001800014040080200400000110080001c18020020040f01c1c0000600806028000000a0280500409008010000000000060040000400c0802c000200001834000030141403000010000000a0101102c010400300002054090080001008020030080f0140001c0d0000000c0903803024000000800003060000041703001028000140800402014090100201000008000240000800000010280101002038020000102c000000101803010010000e02802000000040302400 else 0x2a6d8035031bab27013c000040f65c841ed7cb2e6acc433c00011c13016c00028b080002c03c000281f501bcc04d68700000000329371cddaa8fc06f2a4d43a15d69c3452bd00001ead041fc0608019400004a8cea318b114b380002c0db29c00003493ac34800008353020bc8b4dcf400000002c24583b0ce0a9f739f2edc286848023702d7c379421c41558053d09c405c0000c1b7deac49d95f5fa9e000000000000182dd28fe08e241abc1d043300000692980574b98430e1e555e5c000041f80002ab6b4213084fa036c2e10075008c0115839043b708d4000000000000000100a0000000000003083142ac42c7e96bc28c00035f421c0d8284a812c2d06912df0e41300000cbd2a8de1dac000342008a3101cc00038040000000025d4c00002a0e82be02e8000000000000000000000000c24800000000000343400001c07a68394020000240240000000280cc000000000000000000025d345d8040e39ec08b229c99c084817803980e04dd564b07c1e9404901e4c60781521d7b0ad6435400010afd038401bb1d32d837aab3809c030068f6406ac1dec3c10a4fdd77c2a46918826881f25c2400000000e94b410f80ff426fc0c25e1dc310000000020365ab6da8040250d60ac2f38bc11ec44173c05800000000000000035d1040d308c00001c164c02ee96c000000036b7b48571d920ad30000000148864ab800000000c1c2cb9503244968c288000000019d3c000000024a154abca98b0028000108f9439c00011dc6c8d00003692588cb40f9c30540be697000000000000240a)
def hashlivel12 (i : Nat) : Nat := (if i<6 then (if i<3 then (if i<1 then 0x240060010004000000001803400600700280000000040040000036000007806400602000000040000010020000012001003801c0040000008004012000001805c02c00800080200000140018020002002001000001600400380080160020010000002000000801400400300880180020000018008000002000000c02000100080200060010000004008000001000c0100000010004006000000001000a00400b00000000030010010006004000000800c009001801400e00c0000028002001000804c07a0000018004004005000000c000000009000001a01500c000400000200d8000012001002000c000001003803c0000000038000000002000000800400600100580000000008000010000000000400000000000000020050008020036000003800000000d00580440060100078018002000009800c014000000001801800100480f4010007000002000e0510020004000000002006801c01300a001000001700000040440030018010000000001004800000d000000800000100200240040000000048004004000000400c0010100024018003001001001800a000000c004000003800000600000580000020030000010000001001000000e0010008000002000003000400200000300280000080040000018000000000400000100080000000040088000002003002002c00400d00080000120100000000002000004801801800300180340100120008008022003002804402600200000080460020008000000002008000c00e00a000800000c000002800000400200300080020080008020004003002801400001000100140240040000028008003005000001400c000000000200400000080000050000000004009001001800000000200100000110000004002002008001800000100280000020130018028024005000800c000000005800c00e0000000000002002000000002600000300080040050020010010002000800400200e001000400400900200000000010000000006001003800800600000280100160010008000000008000000c006008000001c00a00000280340100000030000000001000000800000300000140100010030004012011001000c00200100000000060010000000002006003800000e002003000400201300000000000000008004000001000800000c0010020020000000001007400000000000040040020020004000001001800400a00a0008008002003001001800000800080040000020018004000005006001801c004001800c00400a005800c008001000800000a001001004401400100080000120000000030002001001000c00800000200280020020000018016000000800c0000020020000006000000800000000000400140040010000000004002001000001200000080200000010060000002004 else (if i<2 then 0xb11d3aa00a6800003e95a1807030267a01cc0000081af00000349af289c595bbc0c62000000000751ee706db4109368998000000000c124300b279051a7b254e0248238481f2901eee064800001554100000aee25c019e54adb061b80d2c49b580000606c3ae86c0000000008013000003011880299e202dae9fe82d2b949b2ab0d753eb0113f847887152cf710820c602a792686149c242c1751798a9fb503f3c8ee18531029ea55020408618130906d3e07a743283029b277ea00002c16a094dcd783c00000401b80000204b20000000000000040c60d50fc894e30326ba04f645058144e022e00000000038059800000000104730829d1034cb25c58074789c3e81a8a08f44195988a1582d8c06d8e11d30898c0093007fdc12bcc19080000a02f8000016904d8514525ca4019a82dfb0335928d60000140f0c5389c7843017a4427300000e0beef53dc00000011200001b47bc2ae559292fa18f44704821a1ba6c10a3f0451bc202f3c2dd276b4002c00000000000000817e4000000606020800001a019001000003c000000800000400400000440000530048000002002004802400a0120028004000006004802400a000004001002400400300240020120088020004002004004c02200a001001c014001002801805e0000030018002010013800401a007000000c02000000100ac00001b001000000e00100c000402a033004801801e016004002c00800900000000060010050010010015001003c018003000800c0100000020004002001000000001a006003007c00c0020000000028010020008c00001f00000040040030000008012015000800800800200d800000e0020000008022002001801400400200d802000e002003009802a028000000400c0000000000002003006800c004007003000800c002001804c00000600300080020080018028022019000000805c0020028004002009001801c000005004802800400b00000000320030000000000000005003c00e000002000400a006002004400000f000800800c009004000400000500180040a000200b8008016016002801801a00c0050000000000000001000000a0128000004017000000000000000c0000000004000002c01600000a801c0020000050004026001003000000a00300080dc0000240000010004014000001001c0030000044018014000001c03a02100d00040000010008020000002001802c0020000000004032005000804c00a00000180100020030078000002003000003c00e007000802400000300000100000050000038004000004000000a000002802800e00400380000100000060004006002000000000601a010801401c0060008030004000000000001800100c000000000600b802400000000000000000020040030012012001801801a001004806 else 0xbd42f73fb4096c000000000c05b4a08fc487a012f9000018123702197d1f1b04ae81103eab8c80ec80960208644a505d2e0000012166c000000000d0c48000029cfba05a4878bd6e06b09e380000000016599600ba200ee77aac000039e6fe84f5528540f2f80000000000000000000000058635d7836af3e00000304250000120d459dc7e80e700000752800000304ef902880000182428000000000000000000405b000001c09c949a080000e71bf218e8000000000e0aebe126800000000000000611e4422d0000020aa3755ce08ec782c9000011555ec87bc84b220258000034ae8f548657c138018c000018315d7ac6e52400000000003230f809e8000053dc7c081a0000041c820381704fba0eb8de22001dc509b3014b5c2f3000000000084c96800d780d7500aa000022957f835800000000006845e116eca88bb402ac94d00000eaa73005674a389126100000d4901c03100000009c240cca69c7e04f710aade0098000000000c094781944000000000701a2000000000753620000000001c8ed985d800000000000000000000005ba1238000063abc70b6321532415748252e0bd6a196ac20541138a099180c101e1c80000000000000000000000072789e0a94000000000a091f8ea88802780000807b0000021e1a85215803f26ef869d2ca3c52b78750032e82d580000ba389e0deac197e5276200dee02788a1f80000da10c000021c724850d808a6401080000604a000001049b3014a98060504e60000000000823ee002a0000000006024b1244780407cad8315c54040c0000268980000000000000000000584018063401825414f9839d01010b4820a97d38590fa051806c5c08bb81036084400001c1f2600a2000000000000000d64910647ae358000011302428d9816b940af502d950221955640000790f800000015a2c15d58035600a20000000007d106000000000101fb8000000000a08800000603a00000000000e9ef1907f7035cf54c9aab6d85f40000000003c0798000000000eec03c0dd000005080dc0d8c000000000f0c15a0ddc0000000000000000001de21800000000000002082800000000000000249dd0000007954c03185ddb5054000000000031cf4b033100000000030297000000000001585c1cbe91eaa01b4b4bd080cf8000040a1f01720482539171300d7e54fa41ae0925b00000eed130239f0076000012ef6800b03d574c23eb41605431ea829d301004078108a043b1a6aa8b600c009530000000000e08a2de1e580a4a033c00002820180000074a4eef9800000000000001c023580da600cd77304000000577105c3922b3a55c501d7dd12ffa4eff422a8326bd02c176d821907e84150547f25638e395031c2554e3a435e11780000000000000000000000000000f04d80000000001535e0000000003c)) else (if i<4 then 0x1c1010000000000aa3f2d5125c852680ed00000000036ae6290a610a37ce71c00000000090ade60c0982c9000009077a00002818fb04cd00000050f601873d4050068e000021dedc864c500b2000021cf25961400001c0a3680fd304b500001f453c000010517f711c00003421b41154c077280058eb22b95110000000003c00080000e092c0000049e1d828ea0be660294c1f4800004001a000000000452d20000000000c897800007238d8572a5f3508223d2214e0eb4811d2816e271ce351a800000000000000c157000001152800000000026896b517cc024e0000081ec88044d754a00003032b80000f0092000000000000000000120e178234584801a7bf807891e0ae816ca251800002817000000000000108c41f4714120000040cebc0297d344000005433400004d14b00000402980000582f400000000008a93000005268400000818f49479ea3f4e0e730311991309088400003c06f00000e200ec0d9d0121bbc23e2031e02a081ee083e5000014eeed1d1d582fecacd5b51f50a3f70214000000000381fc0000000000641b40000105f050abc2160c000000000f05fa00000419b18275ba49c200f942fab0308fa75ce115d004ae0625526e6a169bc174c5363ea482147b2c19628184a70604112d005ba9340000004e2700000091de2712c84510014e7d1f28a28c80fb64284c06181204d40e86c00e615bce799c0000041f1a55228037e0040a5ddf484bdf73216ef3149a7081a440603802da5cabd042cc067a0045a40f3ebb606ab8a2324c421c084920000000000000000000923462e7b86a89ed4b0000015519248ae782e7000000000081888000000000c0bd40000792590000000000a8ac2129d7731c240f48020352fb00000006d400004141aa26bfd412609e3000000000060793cae7d3da9f0800000008219e1420e221a00003885b80000504f295300c0aef809bfac9e000000000480e4902c7808cc00007b8dc000002efd000001853f0000100cf0000010484e742e00000000000000301f1606c1885a8818a00000e44f91e6a9bbfc9729b4e3746aa78000070ca9c008bc1858000000000404f65d9f611e04005095100680580000704350e28800000000040582a088bc0c3151fbe704804ba96938c81891087c00caf28aa2056c2032c14d87c108cd3e4b012dc071ccad46148ad04a60e7bf81c4e1487271e76ea44289a3058ff0b35a053d0ac9f554be08abc83f4c1ea1038ab0651200b84a4f800005ab4b8054400000000060504618bac0e42512ee0619c573b026fa020f00001c4d14431a411b2ba3e1c574800004bc16b069a0000189db0000050887d4a2dca760046f20129251bf021ff800fc0117c1523deb4601cefa2f4000000000704fc50804a087341e7e852b2a823406570025f80baea4078efca03293 else (if i<5 then 0xeef0d000000000000001af2940000000008705e4e7d528ba0000000000c08d74319092a9f05d4806f4000033da1020a6000000000000000000021713c0ce80000e07ea000021d2a0000000000000000000000000000000f275e60005d900001409a682f0b834550070ceeccca7513cf99279a000000000000004a045b44a58975c8292d0796000008b1e000002082fe162d8092815c81a7da00001aa8200000d0c32947cc000000000a056c000000000000000000100c700000402db62b3a00000000028477e0b78000025ca8f92e3000006469c00005904e00000415df012723b82b07cfe0bc749ed9526c27bb61582d01db00000b03daa44ac00000000000000aeff400006b90bba87781810803895289805ae000029ddc391d4a01b7351445d567bcee30b73747008a0e902154702d5487868778112c00001e033b4a39385ce00b8a44b39081b80000301caae7fe8321000000000140ad6894c71111f079875334000029594b2badee381de55ed12420223f44a14306f012d9a1d76198302ac9815322b41e4d2a40d07d5d7807f540bd942ccb8267f0c228012102941862707571f478200569806c30a3c000039cf2800000000060e45821dc85a83076ef51bb80e968639fa654c55cca940f94bec78af8f07cc324a8562077c6602c21ea1c05894a4cd73878000048187e15df6eacc0000000003a7d1002700aa6154f3fa58bc0f3400005021b00771e0756813b0ba03c09d5e4eef820b0000000001804fa89738000000001217940000292330000040551089a139f1d096df488ac1e73027100001c4e1382dc305329782600000000028141511f800001e9084ba7ea7a90452a901d9201da5062fc121fc0ab63d3460787aef62c30a184c48a431c0d4b899e3822da07f8c174440299031d02aa70ef67412a0d10e4a19de16c92a27494c4e766eaef5000004ba6520a40000005df8f540bf070d804ecdc6d00000ea69e0000102a730324ea9dbc4ef800000000002772846280000702f770094000000000203db000000000000003008c479620000000004b9d3000000000308c42d2a98049200001019a0000000000000021e70800006283000001823b492e4600cf4129a4a7e5bcacb09db60c8b82bec839490546013e00000000000000000001c0a77838f70a048e26ec13a285c7f259400002c8032ba27d03440e02ac850d034ee0c665556328a2d82d6ea196003ea9ee62040780aece019589e168640fa8e600001401dbbc2fba3f1e4d180000481cc70775c45418044800003784400000c15015374e229304f2c0000000000000000003c89ef110ca03f6000011df1495018061e0000000002d2e3d0a480000000006bc63978a8c1675695fe94880000000003c012755dd0000080e0fc207c39d70000160e38000000000000010056c00003d2a3 else 0x488122984454aa6884be8a913d95d91795c6048ac05c5010eb0bb5816aa0144082b110c9d409acc277484c140691206ac4167a80bf0000060e7a01a3303c4609628ef3a0b05480cfd0756e118bc30bed2aa72429c1274c0d0a91d2c064120dc1885e00000a752e751359df9a8284a78052e3881ddfad1128034b04bf58290b3991ba2ab44122427dc80aa5a8d04090a40e54007500000011630011894280000040814000041296f032800003807780000920ae756a85cd511389000000000000001837d2ab12000000000001738078be4ba400007024100001d55428801884650000000001ab258000052170c0753492a3057997b68b44f58075c824f703a1c12fc0000784f0170660000000001012942a822450dc2dda858a00001e152740148000090bb8e46b80000000006a247d5404885d605ddf245d0062fe9079bd95809a8a58ec00000852727555641351ea60000022964014cc000000000a050254f800000000000000175757dc6ab82ef000002e3dc00000000000001407d1025c8000010028cee1000001058700001408365d4ce00af00928614ef9cfe53a6820a54cf0c7aad100000000000000140b900000000000104800001832d500fc00001c1e3000008a2342eecbdd4680000707e2000004285d131ef278baf033ca0ca85cb304002153fa855780bb4079000000000048360b05538131c00006850580186014c11de04819700000a00f082ad202dc5050f5403f0068000e8803fb8177c00004baa0aaa07443d648b6712fb00001d5750c2e600000c234da1654000000000a7324015a98085000000000000000000000000e0a9620d054a7ba02fc528520000168350000000001af0914abc5805400000000000000000000000000001010b58318225a09411be82600000e0817ae8dc6907702d200001cf55d40e4c10990000000002000d8000010209403ee2853550a4f04cb013fa485cf805e82b74c05ec00003394e6a7e180eef814b3146db09940000302cb000002a5e7a157f0239082cee05d9a197640a380000b026e254cdc334984e2902018177a9d0d000000000114f6b00c6c021d902278117e089e411df0000000000000048598f7476000000000000000ab24207d58ab2f1256fa4990070bc10c00000000015471400000000087936ae3e140bf000009058c000039e9700000021fa60216c94f2d441aa2339593800000ba00e0554000008122584f10000000002c2324b890601b0744f0833500000322de00000000060518579b600000e89ae817652c62612202b2300000e217a00000a91d80000a0cd7944740000184470065c2141a69721b9eb80aaf80dec00005059f22a7120b4e5e2c681996025174495eabd7050ca7a268f510000000375e23dbb469c00002045427556a09fa0233e528760898340448ab3a3c5910bf))) else (if i<9 then (if i<7 then 0x64ab9671714af51959f1dd90f66787e20e980000684e80a255753bd02ea00000d0888000000000514af000007512aaa2feb81d200aeb46f400005d2c1d07f705079c0fb180a9000006e6b82898d106e000019561c82f528182870d200000000000000b01900000041e3db8a63246820adcc1f04048af06e6cefdd02a1d026e1044d00df90a61d8538f74dbc12e85dfc401772099961187423f712c9d0c425523a88607832a3271e451b8c1c9003eeea387b433388dd6854db71d060f424aaa71381303308ef4d8065494ab40458409bdca10d037430a7200003c2556806e92793e133a68446d5300000125070885f00000671d200000000068313d25de00000c179000000000000000000000000a0a78000009d5dd02255a4240000042c2a960100000a4efc0000500e9000017423000005918bda96420dae027fa84e77094ac549d4020914c800000e14714aa388020ca1e5e10d5aa230000000001c48fc0000054d0000010f5675ce4552170000000001c333a10a30000000003ca12c81584754f20bad9ca439216905218e16f802fe5544a0ae02f45182cbc804c202d640b02aac25d20b000018ecd400000000060c0b60d50407e39152f0140743f9aacb00000c0716c0a61825d80000aa878412a08a81ad552b0cbc0000101400399a90861ce9b8dd588846380476415940ad3abc5ad09c60000000003056002a6d209760976095497704ce0fc11c0db04d1b20402183841435061c12b24e0a51c272d01dd0000080e2209204bbf6fa3aa01988000010616001b2343bb8825f02d15097874e874254f85f2d22e6b584b40b6e024a1a3dbe4960828ed04fa0a7d9e027e80011949ee00b58191dc07b1011520ab1145335d3d103a32a812416dc0000305a2904b561255a8a0a3d3eb099fa52b06a7cf82fa27b0600000c181d02b097779e07df696c000002097c940fe1c176800e874ebc5494000000000f79ba0000381cd80000a284c202d5dcfa2d03700000000000000681499278180c9ca833c04810000160d0c000079580f2318ceaeb007a5860000000ceec140ae00000c06afc068cc11e4841182b5e74460c15d93cf5a095b805bfc3327805cc07df00ae31cc7983ffc010960d9a4022a853e0000000000000000000000010175c00000000000001416711c6b800003a3ce348100000655c8006e3205c6282880000d003160fb38008fbaa1d0c4400000000000000e021e452c0000005546b246a54b6e8018d3dacc0c6c000035e27a02f0000000000000007906beaa2b642db1c6828645708d3401ec81df49532103f800001414780000b2b05441100000000000000160238000013abee0310810e5caba185f6eab66000011d20f0510a0b1da030042f1d02cb0000000003c245b0090a0760441e541b44948f42b62000011e2da054100001214 else (if i<8 then 0x4a25010300310000078376605680000000006059e0000000000000000000909e6a0ed4819f692aa3a02063247417df826ac74c9e06dc0000000002055fc0e5400004825e0000164e4480bad001e67b9b6f458000000000a0064cf57c020aa39ed00000000030a58c02290ab2e4109a4126239adf75014efba28ab995728069f0eac04a5af80c94a8158e5da414898353c786d61391496f80000908ea5421c00005007f608bbd4094297f03dab07841a15efdc7300000177f4000000000000007259a00003c19dc80f2a236000000021e0815a00000c59a9409500000d2070340e88ae580000507a66160388266800c503202080789742813190c7e60023a919a11cd000010041748349d54ad02fba4bfbc26b4024db0af98076c8189585a00000000000000038519000000000181d4b82b200001818400017800000000020ca4000018157d031e00000000000000c72fac07a9408c23a04424da00003e9f18000000000ee969c94980000008cd803824316ed648c298400002832e7866300000f51ad9cff380e23083a2f27800004814c57ba1408240000750ea9070401788000030170fa9c4000000000000000a285805fe02dedd20d501fa0000000001513280473ce0c800006b9d40000000000681e5012f00001007162933800008a2ba0000049a248181604ade48dc4ae480000107620000329ec005b6fa23d150415eb5651a8874302025eca5e3556180a84a0e340000204f900000f4ff8000000000b0b4e9501b8802f84dbd016314a0c29f4a8420b229180266013d80497f0b6800003ded1a1371377a00000000003823d120b48129d48cd05140674b8000000000000002a2f7d4e12020e6803aba9bd2f0a92908a80ac206018e942df18d04dd2285c649b9018800000000000000302f8800007a8d380450c0f4000000000000000000018410000018041e9dd4800000000000003c225403bc00000ee8fbc89d280b930c3f61792dc358000050c04003d740019bb45d01b98046d9d31f043a604ff949174142800009a1d8c135c80d3682c822a6241918000000000000000000000000bce2603f00477468bf0000062879609b41cc99125e000014ef04000040213d0892000000000000000000000002c11200000203e6000031e71c861b0000000001e844f13bc3a7cbeeade1e780000000001e05e6880c984b842131a498800007913bf294bc10f400c1800002a889e084ac11c7808f77a152072e28786844640a00c09854897085716764e146a5c09c790bb00000000025ed800000d0ccde5482c23df82b3705ab64ec14236681685a1db5595e6b2d4861da08b3815d1c165081191231241447406978483424620000101eb3d3dbfab1400002e952601210089c40633ea1c88588705a000003c03b805370000064c1bc13208378309962083129 else 0x648bc000000000e00d3c17fa41e14d3e75a7d6c12ce2a795802567360a474400000000077ba6af2c0aad35d44b1058ae536dc2b58b8d1c20c4e17a341c00009220c1700d56a961000008252a008a80000000007006da021928bbe02e5824be80fe4407f3018020ad2017eae9a2d037f00001a069dab2cd046a80a0f60b34000000000e05bba0ce1c03cd8140f07550e236824e2bd660000160a8ac32fc041e52b556142b8003800005a216f4c984015a8552124aa000000000290c2476940000000000000000000a05414a60b849e377bc0000000006019b00001402f88a118000000000000000000000000000000000000000000f0af00000000002811e329bcc07b2dce9755a8a095c000025e78c14a330c96000000000000000a437809c24237403169a50c14eb2c1ac8bb1e103c680bb69e5999002b225a40e4c00004d3030000104c88000008526204d0000030a74891da200f40000180d5000e190b74000029c4fb13cab01d4ae4244103c512000000000001c018000000000c0064000000000daa46000029e19bbd2160bfb803e400001d1e30000141362c1f900000a218c4e54c00005b8d837339af995c19980000125dc00003c12c0000000001813080000000002708a00000000000000f74fa00000000000000701bbc02bb42b2000000000100988403e000005038db4050415e085af2259000000c329800009077e000000000654f4e04f80000000006125ae006800001c095e5448829dba051a2a26015c450749411598102382e6e20fdc009d016fd064f309b88f0f90060950f17003a00002dc47f8142174d5c128602f3e042b00000c0b304a9fb02a60000080e6583092564a00000640c80000750cf5a29d8e553828a80000000000000000000000000001a158c000000000000001599400001863c00001a0b78000051555000000e9cc00000860c00001201389dfca3b46d0bf0000000000305ac323977562c00d60b9c9f2b5800000802c0000080516e11204120000000000000002084a800004760cc4a47c1b76831970c88a03c0000000000d0744008af1c50000001226d00982c92bfbb730083304ed0dc8713c14d08ffcea3b68820820b2a0c000002c09a000000000194b1000006833f12470c46bc4928611373093e00000c25a403a5f2752000039c4f0000040629610b40000793c1000007503f1ecc103fd0ab8c852356880581e6f71b2a05e0c907395cce025ca15cd022df9609fa21e652b8a98f0386e20179e181f82a860232b2b5d80bbac929982a4c06c8a4bb48a7b0000000a46540d9483e80000e01fea00fe4309b862600000654139d011ba7cd000ab4eb741e0f841a00001217b4000000000000000000141c3a80a1000018106cc12e2918d001a70509f2889800007085e40b8f0117d042e7a14e814f7e8de65)) else (if i<10 then 0x3a8ba8381c0aaac2428928e73902122a818039ba945101b9e04a2408d048e7a133b308a3b440d1c7d6035b00001808dc29f7e540cea4dae07bb41627012060a53956ecea038000000000ae36ec879a11510000000000000065346f71f6000022961cbc47923de4ea3fca817811cda2740000080efa829700000c199400000000000000000000000200b2000002102581d380000000000000108cd80000e049184ab00280d01671013a24976c03ee8088c2a3e60f0202edf864800000000018a9a000001a15e00001826180000000016141240a9283eab03ca00d280000605fb823b380f87c174784e0e018400000a8ad0960c8096ee1987e89f000917241b551c58009c0450570bba0840c289b11454061464787c28d00193b253764577c23050306b0cb26522cc2499054542034000019c1d3821e22216ae9c800006bd990000000001003a038e35292b40fd901ab6bbbd977ab018a1c226b941f7217e000020063f3ca0f757b145fc00006d26ea035ac4a7d8260301ef0000104f7a02f65d081871bc00b90000000000000008042e02eaa03d7e008e6097fc2c880000e084200002827b5864370b1a558f4000000236c7c780f75d4183f80f130b800000180a2d0594d0795c07c10a098000080b8de156ca893582e160827018b0802ea3c562a23fe12630252000008021000003293a45437406ca61820000000000a037800001c01c80000d7a8f04788e97620169029458f6929c544804630b42c0aa229f505569575532103941e90d2ab901a8f4a122820910c5f769e200480015785256703cf575a005a139afc03ad41574ea286865b6a8cdc5232c2a9c119cf06f800001006b784c50000000000000000000105840000000000000000001444cf091d80000c017a34babc17cb05558242a217340000485350000140d100000000000000000003ca4e4952f8ab7800003419bbbd385713a55290c2f70020360bf940d680000705ca170474483282d69142b70507d4b2101d4203dd00000256d95d5fa828ce0366243049d9c4bdca624d2a07628301d0655500d4c0da800e0f85a3305f0e00100004cd10dda16022bc102139047cf029020fd1033400000309e8000038a11301b2677919460ddd5cb02bf5073ecf0e2dc70f10c3702c3603315e796820a5a22b00f88c27963a79524e6c12ac01c638637e2a91e1805e8f450021a0a45e0f7b8041820fce75300000000000000020334213f7097300000503a614ab0c229202ff00001e057d84098000000ba04419a82e4b94d512b72610a0000000000e0734004ffc1e8d12267a40ce0f7c82358000000000010aa42d4c858c2020cc18af090980000622ec000015ee4480a35291c0000000004396a1a699951ed8030954af00000c0b1fdccdf5642a795ec136ac24dfd2b2000012134a40000bc5c0 else (if i<11 then 0x800000000000001007c5c0b2e025502224a4a5d015cc38f92a300a0ed2a87fe85369023454ab8000011470c0a8ccf37a0110dba5b00353a425cc1b10000047a2f240292a33b54bdd04f00000240368000090afc0000041bc80000200b740c161ec280000b7128d44e400007bd180000000003828b13db27a451840cc009b7d5380249e41758000008010103760000042d980000000008140c0000213afca2b37478aa9b8c035d4083f44c2ac96e5d64100001e4d364a898000000001406fb9dfdf9478000000000242bf891d0e02d5cf14e0093250830000000002008fc82c3c0a89018816880902bd82b5a00000000068277000004e35000005820e32913e075e484d391c77206c000000000000000000084a5042e789417d0b82a091980a53803de0637853015e9bd81eb2072d41961281a9be207070800001c1558d11c5a56db40ca8946a81d9820f580d4000003000a000008f48a431deba40b000c2472a41ed4140c80bc12528528829029ec2606a070ec24100000a74020000340923813967b5a80434c2c9a1290202f40414ac062b064a405e6244e4019cd8330d23ad4007d40a5c3e0c02c1a20ecc0000590c40086fc0c240000752ada20ba000029cf32856e1a204418540000492300000000000000000000000004063a0a122bcea0000085910000000000a24c12143ac1509014d101c72037c107f5d24d00001c4edf406a804ac1a57d9513c0000201c4f7be0000016a4e800000000044ef7023ec0566000012117040e7800009a7520000000004063e00000000000000000001010e411b5810bc0340777a4c0e6381af80000f0aa8000000000701b8c2ab7a10a7c220805d27030ab4a17c3078000072253ee52b0034302acc00f00000000007004320ba6a029fa82c401320000000001c2e173849a705b8113c4649285b5b009b1482a4ad33835ef0bdfc18a95e2100000c752de4612c84e00000c04cd85754000078431e055a75631810fd90960a432640c000000000000000000000000184d3606854ec6c0000101cd70c520000000000000000001456440000000000000000000000000000e0279402af026af0135ba2774014000000bbdd00000000020aaf201fe604c6e1619c2b3d11ee124596050c6814d0056000012e52d803900000000011441d5cc0855b9222649449c00000000000000140cf00c8c83490000184c386aa880000906dfaf840000000000d2556418be69c1a84e9870c440eb15ee3281c00000061610828400000603380000068bc35470000016e94400000000000000004240276184d00000000003430d000000000000002c9e410202e09326f0662a70616176002eb42b600417d11b5246c000b200457d114f0b7c604eade1dc82080057c942a441287bbb15a7ac0000000002829a30a94000029c4c003d500000 else 0x9036d647c5014508325aa08a0000000002114700000e14bc00000d03400000410324118501ff00000000000000152786013400000000000000102472e72fa8346950a5098d6122400001016600000a12180000000001a56b213ad003238572f2859747d94a75a8155e712b204771e43022ef0099281379c1f9c83eb5a81aa11c60248800000a9216102181f368247e2297e15e8de2add2d5ba4de2128adcab795a9e0ada0579f4296352077a024a0dc95e2ed848c627b9e4c026a3600000c0c3c4ea04000000000c2acc4474c0000102e20000040a4ce95400000000000000000001bbd700001a105100ef75280474f734fb))))
def hashlivel11 (i : Nat) : Nat := (if i<3 then (if i<1 then 0x80041a0062c2168aab780e860d48c185000038001000025dab000000000000000000000000000000000000000019d4ff043ae9d2b06a30986a0c96aa4900000000060cf40000d09dc000052874000020cac000000000000057873c00300000000000000000010b04000000001dd51001f103790a7640000bad34000067ae98a2700002c0300000180220000000000000000000000000009098800004a8f3ab5b00000000010df00000000000000000000000705da1d49e244a035a0000269cc0000000000a210000000001c286674f40000e0523013cd01d0821c00000000000100200100000201a00300300000d00c01200500100300502000401100900d00401800a00200e00000000800c02100001d00300600600300000c00600303d01200900500801e00400100100400400d00100400300600500000002d00203d01000100000300500200000e00301100500d00000000000100300701e00e03201b00d00400000205500600000200501700400c00200a00500101a00300300300100700100a00500c00f00400000101f00100301f00f00000000a00000000400d00302000200700100400000300000100000100100a00c00001e00a00000200100800001500800700000100a00b00500100301300400700100500200100000200c00001901d00300502600101203901100202801800c00400700700300900100300000200100004401200000002200400900100b00900000600a00f00500400d01303700001300000000601600100101600300000c00100c01800200800400200b00000300200000000b00000000900e00100301200000000200300300200001300000600000000600b00701200600000000200100301700400000500300000400800700101000100000000200100000600200400000100800001400000000000100600000300400100000001300f00c01d00101900000500000000800900200100000500400100000000000000000200000400600000100401500600000000d00000a01400000800300b00300a00200400800000100000000002c00200000400800200000101700100000100000100000000000100200500100700000000200000600000000300100400400a00001300700200300200000100001500900000700800000000100b01000000500000000000000000200000300500300301100000200100000000100600200000000600e00000e00000c00500600500300100000000300000100000000300100100101800300400000900100300000000200100200500700300000000300200400100100000100500000000100200000600000000000100200c00400000300000201000a00000700000100000100400100200600000000000000200000100600100400200000d00300000100000100900100000100e001 else (if i<2 then 0x3600f8000010ce841bf00003e8e11097f40e1c78a5e9d8d0dac0000179170994b0d60424bc2138028100534000032c14000012465029c378031f5f0229a411a1094d80240085c49167a158c380aa34802f740c5c4130609b2c015809a56a334035fc381776358093425045cac000269c2db0cf2dddeaad192acef0ccc9cb3da0e2c2d9f03ae88af903901e520a344486d174ee8210c0716e8e4a0dd4827660410412cf03356ab43051b6840ba70ec364606f400008abbb830c8047f6b38fa49a8034927f39deb6084c4298e099782ecc0c8400000000000009026800000000201aa0000002280000000006ad4801658058b02dba20a80000f02944a89e06d800000000300cf00002028d10e4fdd02305581d3e506340000e036b8125e77290a6b000000000804d40000b02e80000b04428ac6c2568000000001695600001c22192d5bdc4a00000c0d880164c04c8097a439b600ac00009023e42df0000000000000000001a5340000000000000e0b31c17100003c0ea97c140000ba0bbdd5c0000000000000183a2000000000d081c0000000000000000000000000034abd000035dc8000000000000000000c0828c1ef428064351209ae4247005e80000d2a0bab4cf089c43a1b74c182c8502d8000000000000032217804400000000030db49de5c09b80000307b3c343e096502b600000834c0795d81d600001c12100000000000000000010ddd5d59f7856ded0c0bab434a1a4a400008207edeb84abb3414130354834d605a800006a2d44a03f07fea928902dc5d4550d6c8b1aa218f1dc7408cf41d96a983e89ff03de0316077a682064007c0000576500000aa97400000029e0913d0bf9020c00000c31f0051c000000001032e00000000000000000040c4729ef000012b60204916b44a0072c3899a131417d00a240000c00b4036ef289829ed5096c498c50af09d35f04c74232828080000408fc82cae04e2eb470000000000042000000095cea47f2a5080cad03480000107f11e56309ecdd3caa2d00270b0c1d9f37526640000aad7ddccff0d1c0000c0b1e9e01572a9288c5098400000a2ce811b826570932325a181830000269d767c4a9c53a0a9781df7ad5280506a9910083f26d500fa00003c34847be1c38a8003b8251000030243804540000b007980be40c640000000000000f2870000090cf981167001f40e5ca7cc0000b0d500000e0a76c07af0c61de03a031f82ef703bc0374b0d548887e022b405e0000003230718c429a10d16834620b0983766a8e80000000039ecf309341da487962007600000000050dcc0000d0c2a021ff77b01e54700234334ca72b00b120d8602d840a67003b62617003d40bda40c9a77440aca22343436af010982a8e780ac1987011ceab0a07e56a42aa1fa828bb0b255e26e7357c2a497a05c820501b else 0x7d42e7c25120224003784a2a32c7c0000677db0092207ad83423080b002f10827c229701f408a5c246000000000180bbd079c000000000df36a0345ca06200b8286337c468177e062d08adbac252a1ad0a8340db92c780000503a440e630081410b1ab5a413edacf828a9709c900694020b1df7628bec3901099d00e0b19ebc81ed0273c2586a3880000502630b5e0058ea9aa9074e48d6a0242cb57e7782c1e1000009e227019c0000702f40000e0a5ac129202990396376c188a79a19c000000b02027eb0aa8000000000000010cfe020f8ad680000000000000008e0410d47081c21b476e1c02770b69c1f2e74c708760000381640107bc0a200003c13a80d3fdd6cb04ac0000000038a74d0a3be8d600000829e678800000a09fc00516035a42687062068a2922222a1910554e9556716dddda804742a18b2639a862a0d96804fe206200d937166a89ba03fa017b00001814bc0c15a922508a801ddea6a442228ad5b012a8069a294b600765ddf000016a2670c9e02c4778af4ac08259480966a6a35e3f6053a294e303e54142b06071efef0dfdc9fb8756a806a9751942d430012691c300298987208c6dd5e421f2e9b700000de9430acc000000003c0435083b1e2f200a000a02a494020b67afc0b5d502440215f0dbc0000700e8000050e820102027e7a83d62d6400000000388820084800002734400006717a02141220ccb5fe05a1cafc702a14819405a480a4d7687dd43609c5ca07901c340ed60e18aaf0102e0c112b0e369e5a92019c278922cd003880d5b033052a0500f21056bc1ac62190c0cba21194ab4402b8000000003804620cbc0000604e6024800003898d20e228371000000000e2610000000000000000740000050b88425af0ab65f1e00001035f0040cc17c806b40000000000000000021c48401f80000d050c000067059c2d20000142bd000008350b0ab848960000140ab000009c739009800000000000000000201ca0000241940000248bae08f6e836b282280b3906c80000000010200808b74220628a400008a0cc00008a1e34a00f0265aa46d784a0145000024914000000000000020844c04c9000b0038c000000000000000003017400000a8e3000019e10c0c73c15f80b40ab8b07bdb2a2792b25c1933ad78422bca75a8275000000000f02c0000020931016d00000000000001813d4266c41b400001834020bba41f700001c2e88a2f79e13906776b4ab03ee831ae02bcc0631015841a9400c8a9b800ccb02bb50907818c707491d8ed7902683560e7b1f5d7237fc370d70a0000f50e699c54375fc000030afc0000000000000a0ba7ea4a000000000f761c0000000000000e7698c1513266b001ac0a6c6a4820da09ded0794c1ebbd09e54230175ab8314e02780aba179360226b0991089e5a76a4aa49098fa87)) else (if i<4 then 0x20373258011221b00000f04b703849034c0000000000000023540061a05000000779640000378ddc359c03d8c0147a55f82c5c049c0000b07340000a29b8000000002debc70adc418fa06bc00008041d41bea0c3fc862704b80000000000000229a6015d0000342c650a3e838b60b38000090e5f6a306264ac312f0322ab4300003429500001438c804980000200ff8255d0ae40000000005f040000000001a35781bc0000000006a8c400000000201f800371c0b53a707c1dcea0fac889122da0045d092b023600000c11e426dc0000d26440000e01eec13700b3729c2f08f9c0b96061800000018882500abe8000000003010a0000281720000000000000000007769481d1207065c4ef01c7034e000016b3fba4ac0000c21a602018779faa13da8f502fa000038237805ad432a57af9c2e03017c081cf0d700000cabad41b7000021eb90000000000a912805200000e9cd000000000e0ca00000807cd29a390cb3c36220878a9bab0be741a7426b3409530b9241fb7a771a92717906c9fd6a750c2927785381db50b2f0915705fa836610b73ab086a2e46a4c30206418040066c0001a12d896450d7782f2e20132a29e012002b8e078e48b162093c22f400b0830880cd7d4cd679715d48000000000f2826c31ee07b9dc2c60e700302f08e7a896d213c0000c779b082390d250ada80b3cdefd60bff82f482ad42a17604501e1b20c25dead000024a24000000054d0a7c9d90000020a7600000000000000000000000000000001c1a030097e9233068ec1f4000028b1d009f6a8b1a00dc000000001a9a7f091000000000341b900000429420ac80000809e800006a28c000060a9cab4e00002c2545ad7289ad0097402d1c0d06c24e000d6812840173a8410000143571022409f6201dd4a8d00002823b6259c000020042c9b8000010152205324326871884378406c241849045ca8b6f04cc0000f7648006c60948000000002c234077a05e044a5314075129aa1de47a1d6687d7057942fce09bfeb04002840000000028197000000000f0303c2839ac14000010be242deb0c180000d76dcc245000015e2e000000000c0e46419a67646c1e960a47c679c0e4a8012d03d76b156075c0000627dc0000c06e00000000021e5160c92c1f132b16817300000000000003c0ffc0998e94af7897805a80aa708d3809582a4b20a5d80d400003eb49000000000000000000000000000571aa288820ca400000000000003080c000000002010c00003ea35e24100000a004edd5d8206e41f000000cab9107ea48d1504880000d76b041c3d7358491a00001c2116a76f408cc063a0ad07065b00c1106731c514262569c510014000000002eb57e206a42f0771840000f75a40000000000000801e0000000000000010ab000001073f016fd0cdcc111608f00000502 else (if i<5 then 0x8440000000000000000039f5e203f000000000000001aaaaca9590defeb39000019c5f3258cc101307880000807100000d0da428b8527fd5dcf804fe821ae08d79daf0a0a0427c9a0fe6ada121ae4aa3808b3c0f400003c065000000000d0d4c0006000000000f76f0000000000406d000036920c265dc871329dc01d5aac4d6a2d62aa3c2d5d0608c094a25980000027e3082b00000000000000000000002e9be008940000b0e5000005056400003ad740000707fa2a43fa8a141e60000000000000241f5005b000000000000000a1e9e8818208a00e2000000000904d8898f3053ec97b47700019202660c084d2d800000102a80000ea74c00c25a6e4015b60c401ea9e06268a8bb26e8c37e00000438710414000000003682fe00e71c81d2a8800003073101a1f05fc9f35aad08c8b4b7c84000010b5ceaea277ab031ba04bd019532adc00008051209fe509834339a0c36405800000828270a89c0c5c00d80000b0b978153000000000506d5c809e05280000b71f64031c06e8000000002ddff5037d425ce02220246d041b8199d757c00006015402e1c0c380000e01e5c2ed000000000000000000c0338c338d0377692100000c01bb754c0191677e0000000000426dc0ac3811900003c249000015e16402b0000080a2340f1e0aac68a000000c36c000000000979740000974e6e91f40a2b000ce02f01e950000000002a0d0000082d540000000000000000015da2c0b8c00006052701e82a88c000090c88000000002dc27000038175a0a14008600000df6000001419f80ceec2a37039f9da0e282c0000000020b0400000000080e6082b4d072000008a6d0000027939283900000000010bed5e5b000039dfe204700000904d34678972d0000012500a88de0c00000000e7c0000000000000000000000302c8000000000000000000000000002c15ca2094000000001439d00001aa200044d01ab0000000006768c00000093e2924e06c55dd0d282a42ba0000242be00003898b90c1329af0000081bb500f0dd6b000021de3ca8bcc0bf00000c2eb7a8b0000060c054320403e3c30bda8d80000ea4c4831d9777541616281648cff0708c32d0000369bd00002a8e5578e8819ea0bcd486700001dc46a04eec05de01025dd520238e9c6629c08118d0697407fb75415d33e008c02b5b763e8080d066d1dba20a416aafb245e004b0026d1c491033141a400000c35eaa9980000001ae005bb00ab826af7b1342082a702a8cfc0a300000f031340d0478e341a20000242af00002438f0000280a9d0b5a000d222861de25751ec2740000141f650e3981090000142fd979540000200ce4990b0deb68422059b417900003e855d08618344d0a9941d8c781781ea303ba428050e642aed00003a9330a7d5c3635711c0000a05b8000000001415720cc5c1 else 0x5e8c00003c933901cb4021b0c5400000005a5d93b0795486657550290a00000000000003a83c000000000000000000000018057b7c7c8886709cf5dbf2ac2800000000141873ac1a81da00001836010c4c824000002e91e000000000da2a2c931c073ba88bc265b008df021589bbf0782821da7885c372907181de1000004154a08e982f5f24ff00b4b0815ddb6d01cc40975021ec383b75b5eb48e2a206819506415e5030b764068e27eac1c73234ac9c030bc40000672c400006226f81b3e05c2de27ba24c40adc022c0934f06b94053000028845f2bd94293000001c508205a9c4f37149818ada4bbc80090810000020e55c8f7a2c702ba0b005ceb558040380c37a8d1c15040d2ee8abe043d42c30000201233088c0000f0a84000000000000090b980000000000000305814336e7168c21900e0ac20de0df700296756d0060c0703c0a3007f64242e7617aaff000006a3bba0dc0000da7139e4a00001aa65c072680ec00000406f574e80000922131eb0f03f41e4f00000000072076c8c57a72c00000a97c0000476180000a059c2b4100000000000000000090d9f804aca7d140c6000020a8a0000080f300001aacb00a1c0000000000000d0560c22e000020002c07500000e019a9db16a7b800008754be95830b4d409d4012601e4f20a2c064b05e3098a40c0c00000000380f000001888092b0e5cd2807780000b0139c1cb5262042b18013400000000341ed60a126af100002838547)))
def hashlivel10 (i : Nat) : Nat := 0x2d4d1295600a82e753ca2480002c2898300000ef1c82bed3d878c6eef4890000101e00000005101f013a016c118000300c756f817c00e477400000002055d0b02032c08183d706dae96e8f8000102600024026011c0560000000285250934070c019808706b213c000785650bc00002a4800000003520000654f9242e10cc29800000002e7748fb021929921325db701a8a5c0000818d14bb77c405a1dbc0120000a0e5de0d807b044e47101e083fca3ca134000000000000001c22c3c04077805e2a63048226f8e7f00ea91b506804e4aa15d2c0000c11f8058000d03024e20100d4300640000c2dc042320600000000000405a00000000000000101040002033000080a800000003095a0b000000009028c0e1883f11eb015051240cd02660b3e07e825d522728a007a0226d4b50ba0000000700d3003609241d0000173c0000c9b305a306e00000000000504e94200005846a04a00000000000d09da00141700000000a0a742048500a180002c14681b000141500003d50d07d04fb80a9d2d0200000d01041300000b00000001051009170d0e00050300140101000900041f02000a020101080100000205000905010a0002070f
def hashlivel9 (i : Nat) : Nat := 0x804006a3c30008200000e000010
def lived8 (i : Nat) : Nat := 0x1e807d100f41e744c09e2e5fadd54984601605927cb17eb75525051058164de0e5497d16d84601605937a31524745b6118058164
def livel8 : Packing := (4,7,7,0,4,6,0,lived8)
def lived9 (i : Nat) : Nat := (if i<1 then 0x202c007f6fd9f8bec7b4f21e1bbe772ed1d1390716de5b3b626bad2d9cb34644c7585b065e8bbd6ead858cb055e2b754aa81472894ee9c93025b4ac945262474848f50f1ff3f47a0f19de3b2750e11b033c664ca18f2fa5e0b31612b855ca293325c4a4921052003ec748e41be3686a8d01962483304705008c0f01902803c050050018bf5812f151629205921bf99a852f7552a4b2735b5492a5ec5a60164e7b2a92548d8b4c02c90dfdbdb310a1e9525920ff99acab17552e0b241ff2b58caed2065d6483fe56a795daa2c92c907fcad632bb5c192592aeb97ab9aa6a9320b24ddb335536095264164c2fe3e158c5aa4c82c95e5cbd5cd53549605927cd99aa9b04a92c0b2617f6457c2ad8088964c6dea0af855b01112c9a57d525f05a669805934eeaa48e0b4cd300b261df6455caed8a5c164c79ea0ab95db14b82c9bbd15c6053160130593ead330baaa4b8240b27f4a611755497048164fab4c9aeaa92e0902c9fc69635d5525c120593ead322baaa4b8240b27f4a505755497048164faf0cc2e290ae0902c9fda1845c5215c120593ebc326b8a42b8240b27f3858d714857048164fea43e2a6a9260902c97f491d54d524c1205930bfb30be576ad240b2636f6117caed5a48164c2fec9af95dab4902c98cfd635f2bb569205930bfb22be576ad240b2636f5057caed5a48164fbb0c9aa4a8a40882c9fe61635495148110593fac0faa92a290220b241ffb74ac62d2065d6483ff6e958ada62c92c907fedd2b18b5c1925920ffdba56316a8324b241ffb74ac5ed506496483ff6e958bda20c92c9bc79731717b6016059378f2a4be0b6c02c0b26f965493c16d8058164df38a92382db00b02c945fd8d6417baa9525928bfa7ac82f7552a4b2517f475905eeaa54964a2ff6eb20bdd54a92c9ccbd845817baa95259389fb26b02f7552a4b2713f645605eeaa54964e65ea0ac0bdd54a92c9ccf9805817baa95259399f220b02f7552a4b2533f4f5605eeaa54964c2fec859855aa53bac98cfd60b30ab54a77593f4b2e6a9b0ac02c0b27f985c9525451058164fe383eaa4a8a20b02c9fa39755498460160593f552e4a9308c02c0b25eae5f5526118058164fc5c3eaa4c2300b02c97abadd5498460160593f472a42db08c02c0b25eae4b45b6118058164bd5cae856c2300b02c9fea1725494144160592fd62faa9282882c0b27f2c1f5525051058164bf596eaa4a0a20b02c905fcbd5f2aa669525920bfb7b663343d2a4b25e964f45b6158058164bd1c2eaf6c2300b02c978b97d16d8460160592f5525a2db08c02c0b25eac4745b6118058164fc1d3bcaac2300b02c9f8aa778898460160593f454ab11308c02c0b2762e9debb6118058164ed1d2ad76c2300b02c9daaa22aed8460160593f944ef11282882c0b27f88956225051058164 else 0xfa103c8400002640103d04003f0815820000ec20670800f41001502002f0400410800821000007a08004c1000ec2001f84000000007901846203d016c4003d04000000f4179006e34100017400800f41000007d081f4200000f407d100005e080000001a4003ee08c0684c3a819c0683c1180d04067c11880000)
def livel9 : Packing := (95,6,7,2,4,11,0,lived9)
def lived10 (i : Nat) : Nat := (if i<6 then (if i<3 then (if i<1 then 0xb5ed8c6427788964b5ed5c6427788964b5ed3c6427788964b5ed1c6427788964b5eecc6427788964f4ed955827788964fcad845827788964f4ed935827788964f4ed915827788964fcad415827788964fce9805827788964fce9105827788964bced3c5827788964bceecc5827788964b76d8c6425588964b76d3c6425588964b76d1c6425588964b76cac6425588964b76cbc6425588964b76ecc6425588964fe2d845825588964f66d935825588964f66d915825588964fe2d415825588964fe69805825588964fe69105825588964be6d3c5825588964be6ecc5825588964f56d909de5588964fc6d609de5588964fad98260d6380164bedacc60d6380164fed1214c56380164bedacc4c56380164f37a556568880164f3ea2264a8880164fcd98358e7780164fcd93158e7780164bcfacc58e7780164f1f995a227780164f1f992a227780164f1f991a227780164f9b941a227780164b778bc6625580164b778bc64e5580164fe598358e5580164fe593158e5580164be7acc58e5580164b778bc64a5580164f76a2264a5580164f37992a225580164f37991a225580164fb3941a225580164f579989de5580164fd39849de5580164f579939de5580164fc79639de5580164f579929de5580164f579919de5580164fd39419de5580164f97a889de5580164b7e8bc6622280164b7e8bc6562280164f76a556562280164b7e8bc64e2280164fec98358e2280164fec93158e2280164beeacc58e2280164f3e997a222280164f3e995a222280164f3e991a222280164fba941a222280164f5e9989de2280164f5e9959de2280164fda9849de2280164f5e9939de2280164fce9639de2280164f5e9919de2280164fda9419de2280164f9ea889de2280164f769989562280164ff29849562280164f769939562280164fe69639562280164f769919562280164ff29419562280164fb6a889562280164fd6a779562280164fdca778ce2280164ff4a558ce2280164f7e22264a1180164f5f1939de1180164fcf1639de1180164f5f1929de1180164fbd2888ce1180164fdd2778ce1180164f7e19888a1180164f7e19788a1180164f7e19588a1180164ffa18488a1180164f7e19388a1180164fee16388a1180164fbe28888a1180164fde27788a1180164ff625588a1180164ffc23388a1180164fab9756118058164fab9726118058164fab9526118058164fab8526118058164fab97b6118058164fab95b6118058164fab85b6118058164fab92b6118058164fab82b6118058164faba556118058164faba226118058164fababb6118058164feb1725051058164feb1525051058164feb0525051058164feb2225051058164f8ba776118058164fa3a556118058164faaa226118058164dababb6118058164fcb2775051058164fea2225051058164 else (if i<2 then 0xff6152545204416487fcac62d2065d6487fcacaed2065d6487fcac5ed516496487fcacaed516496487fcac5ed316496487fcac56d316496487fcacaed3164964f7c5324c5216496487fcacaed806496487fcac62d706496487fcac62d506496487fcac5ed506496487fcacaed506496487fcac5ed1064964c5fd9b2ad529dd648dfcac56d209dd648fecac5ed31889649ded7c2ad8088964a7f8ac66d518016487fcbc9558a6416487fcbc8898a6416487fcbc8895a6416487fcbc8893a6416487fcbc9552a6416496fcbc9559358164baf98c1498058164be785c5ed8058164bcf97c16d8058164bed93c16d8058164bee92c16d8058164bef11c16d8058164bef11c1491058164bd6d7c2ae558896497f8bc955988016497f8bc889988016497f8bc61d958016497f8bc61d938016497f8bc609938016497f8bc955938016497f8bc8899380164a5fd0c6687a54964e5fa006687a54964a5fecc6687a54964c5fd925eeaa54964c5fd905eeaa54964ccfd605eeaa54964cdee225eeaa54964cdfa005eeaa5496487fd8c2ad2065d64c3fe882ad2065d64c77d522ad516496487fd3c2ad5164964c5fe772ad5164964c7de332ad5164964c7ee222ad516496487fd5c2ad3164964c5fe772ad3164964c77e552ad316496487fd5c2ad8064964c5fe772ad8064964c77e552ad8064964c7ee222ad806496487fd8c2ad706496487fd5c2ad706496487fd1c2ad7064964c3fe882ad7064964c77e552ad7064964c7f6112ad7064964c77d522ae556496487fd1c2ae556496487fd0c2ae5564964c7ee222ae5564964c7f6112ae5564964c7fa002ae5564964c5fd902ad529dd64ccfd602ad529dd64c5fd9c2ad529dd64cdfa002ad529dd648dfecc2ad529dd64ebb6888454a14964e76e5556a2264964c77d5256eaa64964fa79536158058164fa785b6158058164fa7a556158058164bafacc6158058164daf985aed8058164fe71525451058164fe72555451058164bef2cc545105816495fd5caed929dd64f8f985601609dd64bcfacc601609dd64fcf151441609dd6497ed1c2ad958896497ed0c2ad958896497eecc2ad9588964d76cab955958896497ecac56d9188964d76e5556d918896497ecac4ed918896497ed8c2ad918896497ed5c2ad918896497ed3c2ad9188964bfa6cc4c5418896497ecac62d908896497ecac56d9088964d76e5556d908896497ecac4ed9088964d6ed632ad908896497ed8c2ad908896497ed5c2ad908896497ed3c2ad9088964f66e556556088964fae9856016088964beeacc6016088964fee1514416088964b5eecc6567788964b5ed5c6467788964b5ed3c6467788964b5eecc6467788964fcad635067788964fda5315067788964fda5105067788964bdaecc5067788964f4ed636427788964f5ad416427788964 else 0xe7ed725493a64164a7fd7c5493a64164e5fc7c5493a64164a7fecc5493a64164e7ed725491a64164a7fd7c5491a64164e5fc7c5491a64164a7fecc5491a64164e77d7554aaa64164e7ed7254aaa64164a7fd7c54aaa64164e5fc7c54aaa64164a7fecc54aaa64164fe3d755498458164fead725498458164bebd7c5498458164fcbc7c5498458164bebecc5498458164f67d755499358164f6ed725499358164b6fd7c5499358164f4fc7c5499358164b6fecc5499358164f67d755499158164f6ed725499158164b6fd7c5499158164f4fc7c5499158164b6fecc5499158164fead725494158164bebd7c5494158164fcbc7c5494158164bebecc5494158164befacc5cd8058164fed97354d8058164bef97c54d8058164befacc54d8058164fcf9735c98058164fe79755498058164fe79535498058164fee9725498058164bef97c5498058164fcf87c5498058164befacc5498058164bef93c1498058164fed9734c98058164bef97c4c98058164bef95c4c98058164befacc4c98058164fcf9735ed8058164fe795216d8058164bef93c16d8058164bef92c16d8058164bef95c0ad8058164bef93c0ad8058164befacc5cd1058164fed97354d1058164bef97c54d1058164befacc54d1058164fcf9735c91058164fe79755491058164fe79535491058164fee9725491058164bef97c5491058164fcf87c5491058164befacc5491058164bef93c1491058164fed9734c91058164bef97c4c91058164bef95c4c91058164befacc4c91058164eeed725493a58164aefd7c5493a58164ecfc7c5493a58164aefecc5493a58164e5fd106687a54964cdfd805eeaa54964cdfd505eeaa54964cdfd305eeaa54964cdfd205eeaa54964cdfd105eeaa54964c7fd732ad5164964c7fd322ad5164964c7fd752ad3164964c7fe552ad3164964c7fd852ad7064964c7fd312ae5564964c7fd212ae5564964c7fd202ae5564964c7fd102ae5564964faf9736158058164faf9536158058164faf9726158058164faf9526158058164faf9326158058164faf82b6158058164faf97c6158058164faf93c6158058164faf92c6158058164faf82c6158058164fafa226158058164fafacc6158058164fef1735451058164fef1535451058164fef1725451058164fef1525451058164fef1325451058164fef17c5451058164fef13c5451058164fef12c5451058164fef22254510581648dfd7c2ad31601648dfd7c2ad31481648dfd7c2ad8088964a5fd7caa99a54964a77c5c5e99a60164a5fd7c1699a60164a7ed2c1699a60164a7f51c1699a601648f7d5caed8a5c164bf711c16d805416487fcbc65eaa54164fbd1814c5804c164fd69755497048164fde1714857048164ff49535493048164ffc1314853048164c5fd9b1ed5a481648dfd7caed5a48164)) else (if i<4 then 0x97fecc56d3164164f7d5324c52164164b7f57c4c52164164d7f57156d216416497fd7c56d2164164d5fc7c56d216416497fecc56d216416497fd7c4ed216416497fd5c4ed216416497fecc4ed21641649efd5caed87581649efd3caed87581649efd2caed87581649efd7caed85581649efd3caed85581649efd2caed85581649efecc62d7558164f8fd8561d73581649efecc62d73581649efd8caed73581649efd5caed73581649efd2caed73581649efd1caed7358164fa7d876155358164fcdd875cd5358164fe5d855cd5358164bedd8c5cd53581649efecc62d5358164dcfd875ed53581649efd8c5ed53581649efecc5ed53581649efd8caed53581649efd7caed53581649efd2caed53581649efd1caed5358164f8fd7561d8258164f8fd7361d8258164fadd5360d8258164bafd7c60d82581649efd7caed82581649efd5caed82581649efd3caed8258164fcdd535cd7258164dcfd7362d72581649efecc62d7258164fc7d875d55258164fe5d8354d5258164fe5d7354d5258164be7d7c54d5258164fe6c2c54d5258164faed876095258164fe6d756095258164faed836095258164fe6d536095258164fe6c5c6095258164fced735c95258164fe6d535c95258164beed8c5c95258164dafd8762d5258164de7d5362d5258164dcfc7c62d52581649efecc62d52581649efd8c5ed52581649efecc5ed5258164fc7d531ed5258164fced821ed5258164dcfd8b1ed5258164dcfd3b1ed5258164dcfd1b1ed5258164dcfebb1ed52581649efd8caed52581649efd7caed5258164dcfd7caed52581649efd3caed52581649efd1caed5258164dafd8362c5258164debd4c62c52581649efecc62c5258164dedd834ec5258164dedd314ec52581649efd8c4ec52581649efecc4ec5258164def53146c52581649efd3c46c5258164fcdd875cd3258164faed876093258164fecd7360932581649efecc62d32581649efd8c5ed32581649efecc5ed3258164dedd7356d3258164deed8256d32581649efd8c56d32581649efd7c56d3258164dcfc7c56d32581649efecc56d32581649efd8caed32581649efd7caed32581649efd5caed32581649efd1caed3258164fced525c97158164fe6d725495158164fc7c7c5495158164fcf5725c55158164fe75525c55158164de7d525ed51581649efecc5ed5158164dcfd725ed3158164dedd325ed3158164deec2c5ed31581649efecc5ed3158164de7d5256d31581649efd7c56d31581649efecc56d3158164fed5324c52158164bef57c4c52158164def57156d21581649efd7c56d2158164dcfc7c56d21581649efecc56d21581649efd7c4ed21581649efd5c4ed21581649efecc4ed2158164e77d755498a64164e7ed725498a64164a7fd7c5498a64164e5fc7c5498a64164a7fecc5498a64164 else (if i<5 then 0x8ffd8caed2a441648ffd5caed2a441648ffd3caed2a44164c7fcac62d2065d6497fecc62d2065d6497fd8caed2065d6497fd1caed2065d6497fecc4ad1065d6497fd3caed516496497fd0caed5164964c7fcac56d316496497fecc56d316496497fd5caed806496497fd8caed706496497fd1caed7064964f775715455064964f3f9856015064964f779515c15064964c7fcac62d506496497fecc62d5064964f775525451064964f7f151481106496497fecc56d1064964c7fd5b2ad8764164a7fd5c2ad876416497fd5caed876416497fd3caed876416497fd2caed8764164e3fcac61d8564164e5fcac61d7564164c7fcac62d756416497fecc62d7564164f1fd8561d7364164c7fcac62d736416497fecc62d736416497fd8caed736416497fd5caed736416497fd2caed736416497fd1caed7364164f37d876155364164f5dd875cd5364164f75d855cd5364164b7dd8c5cd536416497fecc62d5364164d5fd875ed536416497fd8c5ed536416497fecc5ed536416497fd8caed536416497fd7caed536416497fd2caed536416497fd1caed5364164f1fd7561d8264164f1fd7361d8264164f3dd5360d8264164b3fd7c60d826416497fd7caed826416497fd5caed826416497fd3caed8264164f5dd535cd7264164d5fd7362d726416497fecc62d7264164f57d875d55264164f75d8354d5264164f75d7354d5264164b77d7c54d5264164f76c2c54d5264164f3ed876095264164f76d756095264164f3ed836095264164f76d536095264164f76c5c6095264164f5ed735c95264164f76d535c95264164b7ed8c5c95264164d3fd8762d5264164d77d5362d5264164d5fc7c62d5264164c7fcac62d526416497fecc62d526416497fd8c5ed526416497fecc5ed5264164f57d531ed5264164f5ed821ed5264164d5fd8b1ed5264164d5fd3b1ed5264164d5fd1b1ed5264164d5febb1ed526416497fd8caed526416497fd7caed5264164d5fd7caed526416497fd3caed526416497fd1caed5264164d3fd8362c5264164d7dd834ec5264164d7dd314ec526416497fd8c4ec5264164d6fd6c4ec526416497fecc4ec5264164d7f53146c526416497fd3c46c5264164f5dd875cd3264164f3ed876093264164f7cd73609326416497fecc62d326416497fd8c5ed326416497fecc5ed3264164d7dd7356d3264164d7ed8256d326416497fd8c56d326416497fd7c56d3264164d5fc7c56d326416497fecc56d326416497fd8caed326416497fd7caed326416497fd5caed326416497fd1caed3264164f5ed525c97164164f76d725495164164f57c7c5495164164f5f5725c55164164f775525c55164164d77d525ed5164164d5fd725ed3164164d7dd325ed3164164d7ec2c5ed316416497fecc5ed3164164d77d5256d316416497fd7c56d3164164 else 0xebf9816010a14964efd9314c10a14964aff98c4c10a14964aff98c4410a14964aff93c4410a14964cff93062d0a149648ffecc62d0a14964cff9804ed0a149648ffecc4ed0a149648ffd3c46d0a149648ffecc46d0a14964e77d521699a60164a7fd2c1699a60164a7fd5c0a99a60164c7fd915eeaa60164cfbd415eeaa60164cf7d5256eaa60164c7fd9156eaa60164cfbd4156eaa60164c7fd914aeaa60164cfbd414aeaa601648ffd1caed8a5c164c7fd9562eaa5c164cfbd4162eaa5c164cf7d5356eaa5c164cfbd4156eaa5c1648ffd8c56eaa5c1648ffd8c4eeaa5c1648ffd5c4eeaa5c164cfbd414aeaa5c1648ffd8c4aeaa5c1648ffd3c4aeaa5c164c7fd9546eaa5c1648ffd8c46eaa5c1648ffd5c46eaa5c1648ffd3c46eaa5c1648ffd2c46eaa5c164fb79516158054164c7fc2b66d8a54164c7fd9caed8a541648ffd2caed8a541648ffd1caed8a54164c7fd91aed7a54164cfbd41aed7a541648ffd8caed7a541648ffd3caed7a541648ffd1caed7a54164ffd1214c5804c1648ffd1caed7a4c164fd6d875d55248164fd6d531ed5248164fd6d511ed5248164dded8b1ed5248164dded1b1ed5248164fde5875c52148164fde57a5c52148164ffc53a4c52148164bfe57c4c52148164ffe10c4c52148164ff69535497048164ff69515497048164fde9754857048164fde9734857048164ffe1314857048164ff69755493048164ffc9535493048164ff69515493048164fde87c5493048164ffc9524c53048164ffd1814c53048164ffd1214c53048164ffc9534853048164ffe1714853048164dfe9215ed3048164ef6d755498a48164ef6d515498a48164ef6c5b5498a48164edec7c5498a48164afecbc5498a48164efd9534c18a48164efe9524c18a48164ebf9814c18a48164efd9314c18a48164c7fd9caed8a481648ffd5caed8a481648ffd1caed8a48164ef6d535497a48164ef6d515497a481648ffd8caed7a481648ffd3caed7a481648ffd1caed7a48164ef75815455a48164ef75715455a48164ef79515c15a48164cdfc7c62d5a481648ffecc62d5a48164ed7d511ed5a48164cdfd8b1ed5a48164cdfd3b1ed5a48164cdfd1b1ed5a48164cdfebb1ed5a48164c7fd9caed5a481648ffd8caed5a48164cdfd7caed5a481648ffd3caed5a481648ffd1caed5a48164efd5814c53a48164efd5214c53a48164cdfc7c56d3a481648ffecc56d3a481648ffd8caed3a481648ffd5caed3a481648ffd1caed3a48164cff58146eaa48164ff69755492044164ff69535492044164fde87c5492044164ff71525452044164ffe12c54520441648ffd3caed7a44164efe9524813a441648ffecc62d3a441648ffecc62d2a44164cdfc7c56d2a441648ffecc56d2a441648ffd8c4ed2a441648ffd5c4ed2a441648ffecc4ed2a44164))) else (if i<9 then (if i<7 then 0x8ffcbc5453a48164aefd6c16d3a481648ffcbc9553a481648ffcbc61eaa481648ffcbc546aa481648ffcbc956aa48164bff11c16d2044164afec2c5ed3a441648ffcbc61d2a441648ffcbc9552a44164a7fcac62d2065d64a7fcac4ed5164964a7fcac56d3164964a7fcac5ed8064964a7fcac56d8064964b7ed2c16d806496497fcbc5457064964a7fcac62d5064964a7fcac5ed506496497fcbc602556496497fcbc61d536416497fcbc5cd826416497fcbc61d326416497fcbc4ca55641649efcbc61573581649efcbc61d53581649efcbc5cd82581649efcbc61d32581649efcbc61532581649efcbc4ca55581649efcbc6162258164d5fd905eeaa54964dcfd605eeaa54964dded205eeaa54964cdfd0a5eeaa54964c7fd912ad5260164cfbd412ad52601648ffd1c2ad52601648ffd2c2ad3160164d77d9216d7a60164d77d9116d7a60164dd7d7116d7a60164df3d4116d7a60164df793016d7a60164cf7d2a16d7a60164cf7d1a16d7a60164cf7eaa16d7a60164d5fd925ec5a60164dd7d525ec5a60164d5fd915ec5a60164ddbd415ec5a60164ddf9305ec5a60164cdfd2a5ec5a60164cdfd1a5ec5a60164d7ed914ac5a60164dfad414ac5a60164dfe9304ac5a60164cfed1a4ac5a60164d7ed9c4ac5a60164d7f59346c5a60164def56346c5a60164d7f59246c5a60164df755246c5a60164dff13046c5a60164cff53a46c5a60164cff52a46c5a60164d7f59c46c5a60164dbf58c46c5a60164dfb54c46c5a60164cff5ac46c5a60164c7fd982ad525c164cfbd842ad525c164c7fd932ad525c164cefd632ad525c164cf7d532ad525c164cfbd412ad525c1648ffd8c2ad525c1648ffd3c2ad525c1648ffd1c2ad525c1648ffd8c2ad315c1648ffd5c2ad315c1648ffd2c2ad315c164c7fd952ad8748164cefd632ad87481648ffd5c2ad87481648ffd3c2ad87481648ffd1c2ad8748164cefd632ad85481648ffd3c2ad85481648ffd1c2ad8548164cdfd872ad73481648ffd8c2ad73481648ffd5c2ad73481648ffd1c2ad73481648ffd1c2ad5348164c7fd952ad5148164c7fd932ad5148164cefd632ad5148164cff9302ad51481648ffd3c2ad5148164cfed522ad3148164cff5812ad31481648ffd8c2ad31481648ffd5c2ad3148164def9305ac5a48164cefd3a5ac5a48164c7fd982ad5188964c7fd952ad5188964cfbd842ad5188964c7fd932ad5188964cefd632ad51889648ffd8c2ad51889648ffd3c2ad51889648ffd0c2ad51889648ffecc2ad51889648ffd8c2ad31889648ffd5c2ad3188964c7fd912ad8088964cfbd412ad8088964cff9302ad80889648ffd5c2ad80889648ffd1c2ad8088964c7fd902ae5588964cefd602ae5588964adfd8c4287a54964adfd3c4287a54964adfd1c4287a54964adfecc4287a54964 else (if i<8 then 0xc441668289048a08040de8149020a030403e8008ff29fc83f6e7e68fbe9f603e9e7cc8f8a9ef83dce7b58f5c9e9c3cfe7988f229e343c467848efa9dd83b8e76d8ed29d883ad67568ea49d383a4e7488e8e9d183a0e73a8e6c9cbc39567268e449c7838e671b8e349c4c385e7078e009bf037a66ed8dcc9b8837066dc8db09b4436666c58d829af435c66b48d669ac835866ac8d4a9a8434ce6958d229a3434466848cfa99e4338e66d8ccc998832d66568c9298f031a662d8c52989430ee61c8c30985c30966118c209830303e6008bf897ec2fb65f58be297c02f465e78bcc97882eee5d98ba497202dee5b68b5896882cbe58d8b0095fc2b8e5648ab4953429fe5388a5c9490289e50989f893bc270e4d4898e930025c64ab89429244240647388cc918822ee45988aa9144224e43f886a90b8213641f881e90081fbe3f087cc8f701e8e3d087988f201e1e3bf87768edc1d963a887488e681c7e38586fc8de81bae36b86ce8d8c1ac635486a08d301a0e33a86668ca4192632086388c48183e2fd85f28bd417862ec85c48b6c16b62d2859c8b3416462c485868af015be2b385588a88150629c85308a50147e28b850e8a0c13f627d84f289d4138626c84d6899c131625e84b48958128e250849889201236242847c88e811ae231845a88a4113e2238444887810e621b842e885810a6213841e882c104e208840e8818102620083f887e00f9e1f283e287c00f5e1ea83d287a00f361e583c8878c0ef61da83ac87540e9e1d2839c87340e5e1c7838686fc0dd61b6836a86d00d7e1ab835486a40d3e1a6834486840cfe19b832e86580ca6193832486440c6618b830e86180c0e18082fe85ec0bce17882ee85d80ba617082d885ac0b4e16882ce858c0b0e16082b8856c0ab615582a285400a7614a829285140a1e13f827c84f409de13a827284e0099e132826284c0097612d825884a009361228242848008f611d8226840c077e0e281a4831405a60a78134823403ce06f80c48154023e03a8060809800de0148014800097fcbc6557a601649f7d5caed7a601649ff90caed7a60164d7f59146c5a60164dfb54146c5a60164ef6d521692a601649f7d5caed7a541649dfd7caed2a541649ff90caed1a541649fed2caed7a481649dfd7caed5a4816497fcbc8899a601648ffcbc546aa60164af7d5c0aeaa601648ffcbc956aa601648ffcbc88aaa60164adfcac545735c1648ffcbc5458a5c16497fcbc61d9a5416497fcbc6099a5416497fcbc8899a541648ffcbc8898a541648ffcbc61eaa54164bfd93c16d804c1648ffcbc5457a4c164bfd93c169304816497fcbc61d9a481648ffdbc5498a481648ffcbc5458a48164af7c5c5ed8a481648ffcbc9558a481648ffcbc5457a481648ffcbc61d5a48164adfd7caed5a481648ffcbc61d3a48164 else 0x8e1dc74810470ee3823877143bc11c208e1de08e10474c8a97cd2dca5674a5a948d280a4c7494a920d224a42747da8ecd1bca33f463a8b2d148a26f449a884d0eca19f42ca856d09ca0e7415a81cd01c9fff3f5a7d6cf909ee73d8a7a2cf289e173b8a762cea89d1739ba72ece4c9c5f387a706cdf09b8f36da6d2cd889abf34da68cccfc99d7330a646cc7098bf313a61ecc1497ef2f9a5e4cbac971f2dca5aacb38961f2bca56acab8951f299a524ca2c941f279a4e4c9ac931f259a49ec9209207236a45ec89490d7213a41ec8208fef1f6a3d8c7888ed71d3a398c7088dbf1ada34cc6648c77184a2fac5d88b77167a2c0c5588a5f144a27ac4d88977127a246c470888f10aa206c3e487770e4a1c0c36486a70d0a192c30885ef0b6a15ec2ac851f09ca130c244844f082a0f6c1d08367065a0b6c168829704ba088c10081c7031a054c08c80df017a020c03080270009ff2bfc87f56fe39fb8bf607e86fc99f84bef87db6faf9f56be907ccef929f1cbe287c2ef819ef4bdcc7b5ef679ec0bd647a8ef4a9e86bcf079a6f309e5ebcb87936f1f9e30bc507866f059dfcbbdc777eeee9dd4bba47726ee09db8bb607686ec99d8abb0475e6ebb9d68bac07576ea79d4cba947506e9c9d2aba507496e919d20ba3c746ee899d04b9f873e6e7b9ceeb9d87376e679cc0b97072a6e4d9c8cb90871eee399c64b8a0711ee1c9c2ab838701edff9bf0b7c46f4ede29bb6b7506e66dc29b76b6d06d66da59b48b6806cf6d979b2cb63c6c3ed7d9aecb5bc6b26d5d9aa6b5306a26d3d9a6cb4d4696ed269a3eb460689ed0c9a16b41067e6cf899e2b3a86746ce199c0b364668ecca9986b30865eecb6995eb2a0651ec9f993cb25c6496c919914b20c63dec7498dab1b06356c6998cab17862cec529896b11061e6c35985cb0b4615ec2a984cb07c60bec10981eb02c601ebff97fcaff45fc6bf497e6afc85f6ebec97d6af9c5f2ebe197baaf645ea6bd39798af145deebb69764aeac5d1eb9c972aae385c36b7f96f0adc45b4eb6596b6ad505a7eb48967cacdc5996b319660aca4590eb1a962cac485856b0395f8abd4576eae695beab60569ead2959cab285646ac49580aaf055a6aad9552aa7c54bea909518aa1453eea7694dea9a05306a5994aaa938524ea45947ca8e85196a2e944ea88c50f6a1a942ca848506ea099404a7ec4f9e9ef93d6a79c4f169de93aea74c4e769ca9386a6fc4dd69b3935ea6ac4d1e99f9330a6504c669889308a6004bde97792e6a5bc4b5696392bea56c4ab694f9296a51c4a1693b926ea4cc497692a924ca48848ee919922aa43848368ff91f0a3c447668e591bca36846ae8d1919aa318460e8bd9172a2c845568a69144a27844b6892911ca228442e88190f4a1d8438e86a90cca17c42be853909ea120420683c9070a)) else (if i<10 then 0x7a083d041e8207a105d07a101e84f5427aa1058056102b02c8b0dc1e840ac1058056102c82b080ab0dc40ac1c41056162082b0b0df10440ac10560e2082b0b104158588386e265d07a162032e881e820f4107a0e9032e8b4819745a401d200e90078681785c340bc2e1a0f0d0786820bc10001046102305b14118608c1e84846105b0a118416c200000cd08c4cba0462823082dc118a08c3c80846207a05b1211e3a8819c204230c118408c16c50461c418231211841782846105e08000423081182f0a08c20bd04628230ba9879003c801e4009a0816081e82c640f42f400fa000e8bd0029b20ae2e400824c1cc1082911ea60e608604490940c8200302a1720044c820020582003d0400b610039003c80105be4012118410ea1003d0400f40b620001e820b610320e208128b10436409461b20cfe80306d05215e403202b8c1241bc15c60b20de0ae305906f057183e80d86cfa01004b24460ae0f440678230411772021fa006c8c0ec17836410481b206be80846404142310258358290c06c367d0062b21b20860f50825423277459183202181302b9003d1dc32415c801e0e40980f444774230d9052202482923ba11900581e4402a0a42e4004603b073221186c93b8c127d7790108c9dca0c8006cee192846542313205707a223b86ca11c2f10148219210c90864840b020540e6202a3c803f1a3a9e401f8c01c1e440560f422324771011a3a83c03e81a1790016f1d40d098ea0ce0683c75034163a83381a0d1dc19c0d060468ee068300160508c22ea117508ba840b02846104b06b0521816040741e814860b80da0a4307a8d9052183d3a0083242e34104a2770731c2484148209e4460f230570910860e43ea602a0f43839821141cc108a08c12c1e870ea106d0c3a841289dc1cc78bd0460f4306a82303d193a84364209a102a0d11cea8388c0b015c41b2123908160414a61052080367d00507810d80b64036880cf9021dc600320c3a040cc30ee1032081a044dc20b61002d84028350c100708001c226410070c1e040282014100038401c20007080984504228210140899045d0201380801282001a004000390051782000000b1a09a005c80363410001680100000000068017200d8d040005a0040074008ba0608c20821823080044612230800003a00400223091184000000e80103a0040e801001d00200000022309118400001d002003a0040e80100af0400740081d002074008000000088210000000110420441080000411c3b83e8e9001f5f221de08cacba0ce0f40fb0ef046687507d82303423e403ed2041181a16901f2208c0d090e80ce0fb0460685a4007d82303423e4411c3b83392901f2208c0d080640cf4810eef9104668750670341c3b82dc1182f119761de08e10480bd0ef04607a487705b82303d2520411c3b8e902 else (if i<11 then 0xe880c0074406807a203d0c1903e88ddc307807a2523081b80d8848c1d45246036201b941105680d8815820b20d8206c0591320c3389d002eba0782867034101a0590413040a607ec82303d03b103985d0021b210340fa00398bd001cc5e800f2203f0fa000e8bd0007446720682073a41103d01a0a9041e4548203a207a0801e8003a203d03b131181d880ec20e60f42f40079101e81d8a08c1a4407607a20311841c341641082f04178308204c20c901e10348436421b21006482f083242007a0321001046103d08130208800000003d50fa000e880d42001118400f4086203d03b10ea86c883643e800e62079026101e81d8890421b210d90fa000e883240dc07464bc1f4001d100efa009904074419206003a3030083983d080c007440f204c203d03b112081e888f0098403be8020c901dc23183483e881e810c407607a237724110108c2003f03c1031041e440790462a7701bc23180ed3b8b104074419206e03a301dc41102e80ee208c07688c58820e6207a043103c8130818920a82e4007d10650028a924150403a1c3903d1030841e440d82ce20ca081e80288364978400d925e1000069d45082016200b041161c81e8810ea107a1d910323108b1d472440f6107b0829d41e852ba106108e48818c73843b20f421ce1c9132081e880004ea870841e84cea104107a161083d084d41e8409e26a2041135101eb20880002e4041045e040d80f4217806410188434ea392235d0800b90113508004ea1000d74209d50bae8588420f41053a83d081041e843b00f42059621133a859041e840b40f4264107a10ec83d099d41e840a439221d907a1020b10880f402c44ea0e226750b1c81e89e0c1b81c4404e1027041111c81e89e0e9040b846ba100003f08440838422c211c913ae859d4208208c204107a102d03d0b0841e8404e082204f027102083d080f402c42bc1002b861042005708af04578207a0a42c2103d100f0407b1041e878420f4222113c10af0510415c58820f42c4107a161c83d0b1040f4588208c2a2103d103d079031d45c801e400e3af200b90034ea0f429530f2053a8b90020f41e40081e87900324019200ceac900a9d41e84ce80f42e40083d041e83c801e40081eb2088d4c26a613200f202e40b90020f41e40078119005c803c814ea2353091183d08c802b900f4207a0f20041e83c80107a0a1904d4c3c801e409d513a985c803c801a7507a1720041e82e40167407a1720041e820f4107a083d0790020f41e40081e8588e0c840fac8020788321111c19080f40d05c80103ae40101e81a080f426a61e400a90079029d45c801e400ba9859d01e840bbc80207a083d041e82075c802027083d040f432a61e40083d02f080f4207a107a05e103d040f4178407a0bc203d081e840f01e840780f4207a081e840f41784ea61 else 0x223033103e83d00d8d8681f44c470ce068303d03410036438640362432086487d00074470c107a01b103d00d880dc06c406e03a2c23086c81a0388f0c81185a801386081b80e880dc06c40668462c230341035003e8159003a303401917a000e8810c1e840680322037f40b5d1fa03ae80e8f08c09c406806e2740082183d080741d4407a03a20c903701d180f01e8b1040f454ee118204307a12248488420d284224750a3a841c459c41b20af84632750a118459c1c4426a0574ea39c8178a211e108138a8841e85c801135033a75180df204e45119006c09c404e107a0f2006d763641e866ba0f420d90fa000e881c619c4e800e2264103d104a80e8919c1184c468ce0683641034131181a0806d88c5e81aba036307d64101b1a3380d8a19c1c443aa0f426238670341b1181a080cd88c5e80086207d6410331b11c3381a0d88c0d04066c46207d6410331c338388988c9de19c6c464ee0e63867071103d040cd88c40fbe800663f400431311c3381a0c0d00f419c607a0682241033146c83e081d5d001f471b206f9aa3cd5037e531a6a86c880e40f41c51789e801b00fa3f400d80691b2081e8b10409458820f420ca01d12bac0f081a55d409c7e81aba0f43027069104601e8809d88c40e204e208c071103a87d001f45e8019c0f4364103d104601e894e588d1046a7204e04a35390270251b118409c1a441b215770e208128b1041e8403c1043b401003a9c8a0f02aef07825390261013041cfd0040f204c20ad01b100e81e881cfd005e800f2200d03f12bb81e81f8c1e800f4203f03d146c83d081e83e8003a201df4011a080))))
def livel10 : Packing := (931,5,7,7,4,15,0,lived10)
def lived11 (i : Nat) : Nat := (if i<11 then (if i<5 then (if i<2 then (if i<1 then 0x95600593fbcb8cab002c9fde4c65580164fef2432ac00b27f782b95600593fbd114ab002c9ff65ca3380164ffb2a519c00b27fd8528ce00593fecc0c67002c9ff65c63380164ffb2a319c00b27fd9218ce00593fed11467002c9ffa61e2280164ffd30b11400b27fe97588a00593ff4c1c45002c9ffa5ce2280164ffd2a711400b27fe98188a00593ff4b8c45002c9ffa5462280164ffd26311400b27fe85b88a00593ff52ac45002c9ffc60e1180164ffe2e708c00b27ff18284600593ff8b9423002c9ffc54a1180164ffe0a508c00b27ff13284600593ff911423002c997f6687a549649bfaf7552a4b247fcab481975923fe55aa2c92c91ff2ad31649648ff956c0324b247fcab5c1925923fe55caac92c937f2ad529dd64afdb362d444b26fb611528525933f6ad444c92c91ff56eaa64964cefcaaad320b267ee224a990593b3f2ab2ab02c9ebe6158058164bdf576c02c0b27ef15144160592afeadb253bac957faed929dd64abfb16c84eeb255fd5b64277592afe9db213bac957f4ad909dd64abfa36c84eeb255febb64277593a7ecaac13bac9f2f611609dd64e9fb26b04eeb274fd9158277593e5ea0ac13bac9f3e601609dd64f9f220b04eeb25cfd3b58277592e7f5dac13bac95fb2ad9588964eedcaacac44b257eebb65622592bf6adb23112c95fb4ed9188964afd956c8c44b257eebb64622593f56b1a83112c9fe94c54188964ff4a20a0c44b25faebb50622593b76b1b21112c9deb5059088964afdb16c8444b257ed5b64222592bf69db21112c95fb46d9088964afd956c8444b257eebb64222593b76caac1112c9fab6116088964eddb26b0444b276ed9158222593f56a0ac1112c9fba6016088964fdd220b0444b25eed3b58222592f775dac1112c9d7b6567788964ebdb233bc44b27dad419de22593af6c84ef112c9f3b5827788964eedb212ac44b27e6d6095622593eb73bcab112c9dde9559580164fdb306b1c00b27ed93158e00592f7d5dac7002c9dfa8899280164e7f32b44400b273f992a22005939fcc8d11002c9eee5068880164ebf3313bc00b275f9959de00593edcc24ef002c9d7e64e7780164f9f2c73bc00b275f9929de00593afcc8cef002c9f6e5067780164f3f5113bc00b277799895600593f9cc24ab002c9dde64e5580164fcf2c72ac00b277799295600593bbcc8cab002c9fce5065580164f6f5112ac00b27d7a7795600593eed3bc67002c9dfa6622280164efd32f11400b277e99588a00593fd4c2445002c9dfa64e2280164fdd2c711400b277e99188a00593fd4a0c45002c9efaa222280164fbd4ef11400b27f6a5588a00593fe519c45002c9dfc65e1180164efe32708c00b27ef16384600593bf8c9423002c9f7c9de1180164ffa46708c00b27fe22284600593d5cc2300b02c9fac5051058164 else 0xc9dfb9559188964ff5b0ea0c44b27fad8550622593fd6baa83112c9feb60d4188964ff5ae6a0c44b27fad5350622593fd6c0283112c9feb5c14188964ff5aa0a0c44b27fac5a50622593fd72aa83112c9dfb61d9088964efdb0ac8444b277ed7564222593bf6c1b21112c9dfb5cd9088964efdaa6c8444b277ed7164222593bf6a8b21112c9dfb4c59088964efd8b4c8444b277ee5564222593f76c3ac1112c9fbb6156088964fddaeab0444b27eed8358222593f76b9ac1112c9fbb54d6088964fddae2b0444b27eed5158222593f7698ac1112c9fbb1696088964fddcaab0444b27ded519de22593ef698cef112c9f7b6027788964fbdaa13bc44b27ded309de22593ef6884ef112c9fdb6025588964fedae12ac44b27f6d3095622593fb6884ab112c9fdb2ae5588964eff2eacc400b277f97266200593bfca9331002c9dfe1499880164eff2e2cc400b277f95166200593bfc90b31002c9dfe9559880164eff444cc400b277f98265e00593bfca8b2f002c9dfe4859780164eff30ecac00b277f98565600593bfcc132b002c9dfe5c99580164eff2a4cac00b277f97165600593bfca8b2b002c9dfe4859580164eff444cac00b27fb97561200593fdcb9309002c9fee5498480164ff70a4c2400b27fb97161200593fdca8b09002c9fee4858480164ff74aac2400b27fba2261200593bfcc3b27002c9dfe6159380164eff2eac9c00b277f98264e00593bfcb9327002c9dfe5499380164eff0a4c9c00b277f97164e00593bfca8b27002c9dfe4859380164eff4aac9c00b277fa2264e00593f7cc3ac7002c9fbe6156380164fdf2eab1c00b27ef98258e00593f7cb92c7002c9fbe5496380164fdf0a4b1c00b27ef97158e00593f7ca8ac7002c9fbe4856380164fdf0b6b1c00b27ef82b58e00593f7d2aac7002c9fbe8896380164eff30ec9400b277f98564a00593bfcbab25002c9dfe6099280164eff2a4c9400b277f97164a00593bfca8b25002c9dfe4859280164eff4aac9400b277f98764600593bfcc2b23002c9dfe5d59180164eff304c8c00b277f97264600593bfca9323002c9dfe1499180164eff4aac8c00b277fa2264600593fdcc3a83002c9fee6154180164ff72eaa0c00b27fb98250600593fdcb9283002c9fee5494180164ff70a4a0c00b27fba5550600593fdd11283002c9efe5d68880164f7f2e544400b27bf952a2200593dfc29511002c9efe5c68880164f7f2a344400b27bf931a2200593dfc90d11002c9efe9568880164f7f44544400b27df9859de00593efcc1cef002c9f7e54e7780164fbf3053bc00b27df9529de00593efc994ef002c9f7e6067780164fbf2a33bc00b27df9319de00593efc90cef002c9fde61e5580164fef3072ac00b27f797395600593fbcc14ab002c9fde5ca5580164fef2652ac00b27f7981) else (if i<3 then 0x3690c00b25ff98b48600592ffcbda43002c97fe56d2180164bff27690c00b25ffabb48600593fbcc2cab002c9fde54e5580164fef2a52ac00b27f795195600593ff4c1445002c9ffa54a2280164ffd26511400b27fe92188a005937dec0a94292c9dfb5462264964efda6311324b277ed8088992593bf6a8444c92c9dfb4422264964efd8b511324b277ee55889925933febad54c92c99ff54aaa64964cffcab55324b267fd75629905933feb9314c82c99ff5498a64164cff8a4c5320b267fe55629905933ff11314c82c99ff5c95a64164cffaa4ad320b267fe22569905933feb9274c82c99ff5493a64164cff8a49d320b267fe224e9905933febaa54c82c99ff5492a64164cffcaa95320b267fd72469905933fea9234c82c99ff1491a64164cffc448d320b267fd75aa9905933feb9554c82c99ff54aaa64164cff8a555320b267fe55aa9905933ff11554c82c9dbf5c99558164edfaa4caac0b276fe2265560593f5ebab08b02c9faf5c98458164fd7aa4c22c0b27ebc5261160593f5f2ab08b02c9faf8898458164edfaeac9ac0b276fd7264d60593b7ea9326b02c9dbf1499358164edfcaac9ac0b276fe2264d60593b7ebab22b02c9dbf5c99158164edfaa4c8ac0b276fc5264560593b7f2ab22b02c9dbf8899158164fd7ae4a0ac0b27ebd5250560593f5e29282b02c9faf8894158164fdf2eac02c0b27ef97360160593f7ca9b00b02c9fbe5c98058164fdf2a4c02c0b27ef85260160593f7c99300b02c9fbe5ed8058164fdf2b6c02c0b27ef85b60160593f7c9db00b02c9fbe4ad8058164fdf056c02c0b27efa5560160593f7d11300b02c9fbeaed8058164fdf2ea882c0b27ef97344160593f7ca9a20b02c9fbe5c91058164fdf2a4882c0b27ef85244160593f7c99220b02c9fbe9551058164fdf444882c0b26efd724e96059377ea9274b02c9bbf1493a58164ddfc449d2c0b26efd75aa96059377eb9d54b02c9bbf54eaa58164ddfae5552c0b26efd52aa96059377e29554b02c9bbf4caaa58164ddfcab552c0b26efe22aa960593afea8b253bac9d7f4c5929dd64ebfb00c94eeb275fd5064a77593afe883253bac9d7f615909dd64ebfb06c84eeb275fd5364277593afec13213bac9d7f549909dd64ebfa64c84eeb275fd5164277593afe98b213bac9d7f485909dd64f9fb0ab04eeb27cfd8358277593e7ea9ac13bac9f3f609609dd64f9faa4b04eeb27cfd3258277593e7ea8ac13bac9f3f4c5609dd64f9fa42b04eeb277ed7165622593bf6a8b2b112c9dfb4c59588964efdb00cac44b277ed7065622593bf6a832b112c9dfb4419588964efd956cac44b277ed8764622593bf6c2b23112c9dfb5d59188964efdb06c8c44b277ed7364622593bf6a9b23112c9dfb6019188964efdae0c8c44b277ed5064622593bf62d323112 else (if i<4 then 0x592f7e8d8a4b02c9fb75cd3258164fddb04992c0b25efd8b4c960592f7ebda64b02c97bf56d3258164bdfd76992c0b27cfd725c560592f7f5dae2b02c9f9f5495158164fdeae2a8ac0b25efd7b54560592f7f5daa2b02c9fb74c93158164bdfaf698ac0b25efd5b4c560592f7f5da62b02c9fbd5c52158164fdea6290ac0b25efd7b48560592f7eada42b02c97bf4ed2158164bdfd7690ac0b27e7d8595560593f3ea9caab02c9f9f54a5558164fcfaa32aac0b27eed8288960593f76a9444b02c9fbb4ca2258164fdda43112c0b275fd9b54a775936fe55aa53bac977faed529dd64ebfb36c04eeb25dfebb60277593efcc02a13bac9d7f66d509dd64bbfb16a84eeb25dfebb54277593efcc02613bac9f7b549209dd64fbda42904eeb27df93048277593afecda413bac977f62d209dd64bbfab6904eeb25dfd3b48277592eff5da413bac9f7e481109dd64bbfa76884eeb25dfd2b44277593ff2b8aa3112c9dfb66d5188964bfdaf6a8c44b25fecab54622592ff75daa3112c9dfb66d3188964bfdaf698c44b25fed5b4c622592ff655a63112c97fbaed3188964efdb36c0444b25fecab60222592ff75db01112c9f7b5d57088964fbdae6b8444b27ded715c222592ff6c5ae1112c97fbaed7088964fedaa2a8444b27fe98054222593ff4b82a1112c9dfb66d5088964bfdb16a8444b25fed7b54222592ff655aa1112c97fbaed5088964ff9aa698444b27fcd314c222593ff4c0261112c97fb5ed3088964bfdab698444b27fe55144222592ff6c5a21112c97fb5ed1088964bfdab688444b25fed3b44222593fb6a88b5112c97fb46c5a88964bfda162d444b27f6d5195622593fb6a84ab112c97fb2ae5588964bff576c3c00b27bf98761600593bfccdb0b002c97feaed8580164fbf30ebac00b25ff98b5d600592ffd5db07002c9f7e61d7380164bff316b9c00b25ffabb5ce00593fbcc2aa7002c9ff660d5380164ffb2e6a9c00b25ff98b54e00592ffcbdaa7002c97feaed5380164f7f30ec1400b27bf98360a00593bfccdb05002c97feaed8280164fbf2e6b9400b25ff98b5ca00593fbcbaaa5002c9fde54d5280164ffd304a9400b27fe97254a00593bfccdaa5002c97fe62d5280164bff2f6a9400b27df87b54a00592ffd5daa5002c97fe62c5280164bff27629400b25ff91b14a00593fecb9a65002c9ffa6093280164bff31699400b25ff97b4ca00592ffcada65002c97feaed3280164f7f304c0c00b27df9875c600593efcb92e3002c97fe62d7180164bff576b8c00b27f795254600593ff8c0aa3002c9ffc5c55180164eff336a8c00b25ff98b54600592ffcbdaa3002c97feaed5180164ffb26498c00b27ff1814c600592ffcc5a63002c97fe5ed3180164bff2b698c00b25ffabb4c600593ff8b8a43002c9ffc4c52180164eff3 else 0xf66d2a441649ffb1695220b24ffd7b4a9105927feada54882c93ff4ed2a441649ffd7695220b27f6d5154a22593bf6cdaa5112c9fdb9555288964ffca6290c44b25fed5b48622592ff69da43112c9ffa4c12088964ffd22090444b277ed9b48222592ff6c5a41112c97fb56d2088964bfda7690444b25fed1b48222592bfec5a40cbac95ffaed2065d64eff2408832eb257fd2b44197592bff5daa4c92c9ddf5495164964efeae2a8b24b257fd7b54592592bff5daa2c92c95ff5ed3164964affab698b24b257febb4c592593bf699242c92c9dfd4c52164964affab690b24b257fd3b48592592bff5db00c92c9d7f5d57064964ebfae2b8324b257fd8b5c192592bff5dae0c92c9ddf5455064964eff300a8324b277f97054192592bfec5aa0c92c95ff5ed5064964affd76a8324b277ed8248192593bf6a9240c92c9dfb4852064964affb1690324b257fd5b48192592bff5da40c92c9dfd5451064964eff24088324b257fd7b44192592bfeada20c92c95ff4ad1064964eefaa42d324b2777d5295592593bbea8caac92c9ddf5425564964aff9572ab24b267fcab61d90592bff5db0ec82c9cff61d8564164affd76c2b20b275fd875d590592bfec5aeac82c95ffaed8364164ebfb0eb9b20b257fd8b5cd90592bff5dae6c82c9ddf6155364164efbb06a9b20b277dd7354d90592bfec5aa6c82c95ff5ed5364164affd76a9b20b273fd87609905939fec1b04c82c95ffaed8264164ebfae6b9320b257fd8b5c990593bbebaaa4c82c9ddf54d5264164efdb04a9320b277ed7254990592bfec5aa4c82c95ff5ed5264164ebf8f6a9320b267fdab54990592bff5daa4c82c95ff62c5264164affa7629320b257fd1b14990593beeb9a64c82c9dfb6093264164affb1699320b257fd7b4c990592bfeada64c82c95ffaed3264164ebfae4b8b20b257febb5c590593bbea92a2c82c9dfd5c55164164affaf6a8b20b257febb54590593bee99262c82c95ff5ed3164164affab698b20b257febb4c590593bfab8a42c82c9dfd4c52164164affaf690b20b257fd5b48590592bfe9da42c82c95ffaed2164164eefb0b2ab20b2777d5395590593bbea94aac82c9ddf5465564164efdb0511320b277ed5288990593bf699444c82c9dfb4862264164bdfd76c3ac0b27afd8761560592f7f5db0ab02c9f3f61d7558164bdfb16baac0b25efebb60d60593e7ec3ae6b02c97bf62d7358164bdfd76b9ac0b27e7d8554d60593f6ec1aa6b02c9fb75cd5358164bdfb16a9ac0b25efd7b54d60592f7f5daa6b02c9ebf61d8258164f5fb06c12c0b25efebb60960593e7eb9ae4b02c97bf62d7258164fcfaeaa92c0b27e7d5354960593f76c12a4b02c9fbb5c95258164bdfb16a92c0b25efd7b54960593e7e3daa4b02c97bfaed5258164bdfb16292c0b25efd3b1496))) else (if i<8 then (if i<6 then 0x2e0b24ffcab4c5705927fe55b0e902c93ff2ad85481649ff956b9a40b24ffcab54d205927fe55aa2902c93ff2ad3148164defab42d240b25efd6b169205927fe55aa3112c93ff2ad31889649ff956c0444b24ffcab95622593bf6b9334a92c99ff5e99a54964cffa14cd2a4b275fc7b669525933ff55334a92c95ffaed9a549649ffd76bd2a4b275fd9a1e9525936fe850f4a92c9b7faa87a54964dfdae5552a4b24ffd7baa9525936febdd54a92c93ff42eaa54964dff300850a4b26ff930428525937fc88214292c93ff62d0a149649ffa76850a4b24ffd1b428525933febd334c02c99ff5699a60164cff8b4cd300b267fd2a669805933fe15334c02c99ffaa99a601649ffaf755300b24ffd5baa9805927fe95d54c02c93ff46eaa60164fafaa4baae0b26dfd75629705936feb8b14b82c9bdf16d8a5c1649ffd76c52e0b267fd95aa9705936febad54b82c9b7f5ceaa5c164dbfae3552e0b24ffd8baa9705927feadd54b82c93ff4eeaa5c1649ffa57552e0b24ffd1baa9705937bf2ad54b82c9efe6158054164eff336c02a0b27f785b60150592ffd5db00a82c9f7e5cd7054164fbf2e2b82a0b25ff98b5c150592ffd5dae0a82c9dfe6019a54164eff2e0cd2a0b267fd8a669505933febd334a82c99ff4a99a54164cffa34cd2a0b267fd9b629505927ff5db14a82c93ff62d7a541649ffd76bd2a0b267fd97aa9505937fcc0554a82c9bfe5c2aa54164f7f30ac0260b27bf98160130593fec98b00982c97feaed804c1649ffd76bd260b27f6d7554920593fb6a9aa4902c9fdb5455248164fed8b4a9240b277ed9b54920593ef63daa4902c97fbaed5248164ffcae290a40b27fe53148520593bf6cda42902c97fbaed2148164fbf2eab8240b27df9735c120593ff4a92e0902c9f7e5c57048164ffd242b8240b25ffabb5c120593feca9a60902c9ffa5493048164ffb26298240b27fe9214c120592ffcbda60902c9dfb5499a48164efda42cd240b277f970669205933fec5334902c99ff5e99a48164cffab4cd240b267fc5a669205933fe8d334902c99ffaa99a48164dfdaa4c5240b26ff930629205933fecdb14902c93ffaed8a48164dbfae6bd240b26fed525e9205936feb8af4902c93ff62d7a481649ffd76bd240b26f7d51569205937fcb82b4902c99ff66d5a481649ffb16ad240b24ffd7b569205936fe3dab4902c93ffaed5a48164dfba629d240b24ffd7b4e9205927feada74902c93ffaed3a48164dfdaa555240b26fed21aa9205937fcb8554902c9bfe4c2aa481649ffb1755240b24ffd7baa9205927feadd54902c93ff4eeaa481649ffa3755240b27fe95248110593ff8a8a40882c9dfe66d2044164bff57690220b26ff9205e9105927ff5daf4882c9bfe4813a441649ffb169d220b24ffd7b4e9105927ff5da74882c99f else (if i<7 then 0xbfec2a64c82c9dff5d53264164effb0499320b277fd524c990593bfec5a64c82c9dff5ed3264164effab699320b277fc5b4c990593bfe8da64c82c9dffaed3264164effaa6b8b20b277fd525c590593bfe992e2c82c9dff4ed7164164effae6a8b20b277fd5354590593bfeb92a2c82c9dff5495164164effa64a8b20b277fd3b54590593bfe95aa2c82c9dff5d53164164effae498b20b277fd524c590593bfe29262c82c9dff5ed3164164effab698b20b277fd2b4c590593bfebaa42c82c9dff5cd2164164effaa690b20b277fd5248590593bfe99242c82c9dff56d2164164effa7690b20b277fd8395590593bfec14aac82c9dff4ca5564164effa632ab20b277fd2195590593bfec2c44c82c9dff60e2264164effaa711320b277fd5188990593bfe98c44c82c9dff9562264164fdfab6c3ac0b27efd3b61d60593f7e95b0eb02c9fbfaed8758164fdfaf6c2ac0b27efd3b61560593f7e95b0ab02c9fbf0ad8558164fdfd76c2ac0b27efd7560d60593f7ebdb06b02c9fbf56d8358164fdfa56c1ac0b27efd855cd60593f7ec5ae6b02c9fbf56d7358164fdfa56b9ac0b27efd1b5cd60593f7f5dae6b02c9fbf61d5358164fdfb0aa9ac0b27efd8b54d60593f7ebdaa6b02c9fbf4ad5358164fdf856a9ac0b27efd1b54d60593f7f5daa6b02c9fbf5d58258164fdfae6c12c0b27efd5360960593f7ebdb04b02c9fbf56d8258164fdf8b6c12c0b27efd3b60960593f7f5db04b02c9fbf6157258164fdfb06b92c0b27efd535c960593f7ec3aa4b02c9fbf6155258164fdfb06a92c0b27efd7354960593f7ea9aa4b02c9fbf6095258164fdfb16a92c0b27efd7b54960593f7e9daa4b02c9fbf46d5258164fdfd76a92c0b27efd8314960593f7ec3a64b02c9fbf6153258164fdfaea992c0b27efd824c960593f7ea9264b02c9fbf62d3258164fdfaf6992c0b27efd5b4c960593f7e2da64b02c9fbf46d3258164fdfd76992c0b27efd535c560593f7ea92e2b02c9fbf4c97158164fdfab6b8ac0b27efd3b5c560593f7eb9aa2b02c9fbf54d5158164fdfae4a8ac0b27efd5254560593f7e992a2b02c9fbf5ed5158164fdfa76a8ac0b27efd2b54560593f7ebaa62b02c9fbf5c93158164fdfaa498ac0b27efc524c560593f7ebda62b02c9fbf56d3158164fdfa5698ac0b27efd7548560593f7eb9a42b02c9fbf54d2158164fdfaa490ac0b27efd3248560593f7eada42b02c9fbf4ed2158164fdfb072aac0b27efd8295560593f7e994aab02c9fbf4c65558164fdfa432aac0b27efd8588960593f7ec1c44b02c9fbf54e2258164fdfaa3112c0b27efd3188960593f7f2ac44b02c977f5eeaa549649ff956a9300b24ffcab4c580592fbe2daf4c02c9bdf5685a60164bbfaf62d300b25fed2b16980592ffa8d8b4c02c9bfb4a82a601649ff956a9 else 0x3a48164dffb0f55240b26ffd85aa9205937febad54902c9bff60eaa48164dffae755240b26ffd53aa9205937fec1554902c9bff54aaa48164dffa6555240b26ffd81aa9205937feb8d54902c9bff546aa48164dffa6355240b26ffd21aa9205937fe2dd54902c9bff956aa48164fff30e90220b27ff98548110593ffcbaa40882c9ffe60d2044164fff2e690220b27ff95348110593ffcc1240882c9ffe5492044164fff26490220b27ff98b48110593ffcbda40882c9ffe56d2044164fff0b690220b27ff93b48110593ffd2aa40882c9ffeaed2044164dffb06bd220b26ffd825e9105937fe992f4882c9bff61d3a44164dffb0a9d220b26ffd754e9105937fec1274882c9bff5c93a44164dffaa49d220b26ffc524e9105937fec5a74882c9bff5ed3a44164dffab69d220b26ffd2b4e9105937ff2aa74882c9bff8893a44164dffb0e95220b26ffd854a9105937febaa54882c9bff60d2a44164dffae695220b26ffd534a9105937fec1254882c9bff5492a44164dffa6495220b26ffd8b4a9105937febda54882c9bff56d2a44164dff8b695220b26ffd3b4a9105937ff2aa54882c9bffaed2a44164effb169032eb277fd1b48197593bff5da40cbac9dff5cd5164964effaa6a8b24b277fd5254592593bfebdaa2c92c9dff4ed5164964effa56a8b24b277fd0b54592593bff5daa2c92c9dff5d53164964effab698b24b277fd5348592593bfebab00c92c9dff5498064964effaf6c0324b277fd5b60192593bfe2db00c92c9dff4ad8064964effd76c0324b277fd515c192593bfec3aa0c92c9dff6155064964effaa4a8324b277fd7154192593bfea8aa0c92c9dff4855064964effb16a8324b277fd7b54192593bfe95aa0c92c9dff46d5064964effb0a90324b277fd5148192593bfebaa20c92c9dff5491064964effa632ab24b277fd2195592593bfec04aac92c9dff4825564964effa212ab24b277fd5b61d90593bfe9db0ec82c9dff4ad8764164effd76c3b20b277fd7b61590593bfe9db0ac82c9dff4ad8564164effaeac1b20b277fd7b60d90593bfeadb06c82c9dff4ad8364164effb0ab9b20b277fd8b5cd90593bfeadae6c82c9dff4ad7364164effa36b9b20b277febb5cd90593bfec3aa6c82c9dff6155364164effb16a9b20b277fd7b54d90593bfe95aa6c82c9dff0ad5364164effa36a9b20b277febb54d90593bfebab04c82c9dff5cd8264164effaa6c1320b277fd7b60990593bfeadb04c82c9dff16d8264164effa76c1320b277febb60990593bfec2ae4c82c9dff60d7264164effaa6b9320b277fd8754990593bfec2aa4c82c9dff60d5264164effae6a9320b277fd5354990593bfec12a4c82c9dff62d5264164effaf6a9320b277fd3b54990593bfe8daa4c82c9dffaed5264164effb0629320b277fd874c990593)) else (if i<9 then 0x26ffc2b629505937fe8db14a82c9bff8898a54164dffd76c52a0b26ffd835e9505937fec12f4a82c9bff4c97a54164dffb02bd2a0b26ffd315e9505937fe90af4a82c9bff61eaa54164dffb07552a0b26ffd73aa9505937fec1554a82c9bff5caaa54164dffa65552a0b26ffd81aa9505937feb8d54a82c9bff4c6aa54164dffa43552a0b26ffe22aa950593ffcbab00982c9ffe5c9804c164fff2a4c0260b27ff85260130593ffcb8b00982c9ffe545804c164fff242c0260b27ff97b60130593ffcadb00982c9ffe16d804c164fff256c0260b27ff82b60130593ffc8db00982c9ffe955804c164fff444c0260b27ffabb601305937fec0af4982c9bff5457a4c164dffa42bd260b27fed8754920593ff6c2aa4902c9ffb60d5248164ffdae6a9240b27fed5354920593ff6c0aa4902c9ffb5c55248164ffdaa2a9240b27fed3154920593ff6c52a4902c9ffb5e95248164ffda74a9240b27fed1a54920593ff6c5aa4902c9ffb5ed5248164ffda76a9240b27fed1b54920593ff7552a4902c9ffbaed5248164ffdb0e90a40b27fed8548520593ff6baa42902c9ffb60d2148164ffdae690a40b27fed5348520593ff6c5242902c9ffb5e92148164ffdab490a40b27fec5a48520593ff69d242902c9ffb62d2148164ffdab690a40b27fed3b48520593ff72aa42902c9ffbaa92148164fff30ab8240b27ff9835c120593ffca9ae0902c9ffe6057048164fff2a2b8240b27ff9315c120593ffcc52e0902c9ffe5697048164fff274b8240b27ff91a5c120593ffd552e0902c9ffe61d3048164fff30a98240b27ff9754c120593ffcc1260902c9ffe5493048164fff30298240b27ff9714c120593ffca8a60902c9ffe4853048164fff31498240b27ff97a4c120593ffcad260902c9ffe1693048164fff23498240b27ffa554c120593ffd55260902c9dff61d9a48164effb0acd240b26ffd75629205937fea9314902c9bff5c58a48164dffaa2c5240b26ffd31629205937fe90b14902c9bff5ed8a48164dffab6c5240b26ffc5b629205937fe8db14902c9bff9558a48164dffd76c5240b26ffd855e9205937fec1af4902c9bff54d7a48164dffb02bd240b26ffd515e9205937fe98af4902c9bff61d5a48164dffb0aad240b26ffd83569205937feb9ab4902c9bff54d5a48164dffb04ad240b26ffd32569205937fec0ab4902c9bff5c55a48164dffaa2ad240b26ffd31569205937fe90ab4902c9bff62d5a48164dffaf6ad240b26ffd3b569205937fe8dab4902c9bffaed5a48164dffb0e9d240b26ffd854e9205937febaa74902c9bff6093a48164dffaa49d240b26ffd814e9205937feb8a74902c9bff5453a48164dffa429d240b26ffd8b4e9205937febda74902c9bff56d3a48164dff8b69d240b26ffd1b4e9205937ff2aa74902c9bffaed else (if i<10 then 0x9242902c9eff6058a48164bffd76c5240b27dfd735e920593efeb8af4902c9bff6297a48164bffb16bd240b25ffebb5e920593fbea8ab4902c9bff6295a48164dffaf4ad240b25ffd8b56920592ffebdab4902c9f7f1ed5a48164bffd76ad240b26ffd8a16920592ffec58b4902c97ff4ec5a48164bffa362d240b27fdd314e9205937fec5274902c9bff5e93a48164dffab49d240b26ffc5a4e920592ffebda74902c97ff56d3a48164bffd769d240b26ffd8a469205937febd234902c9bff5691a48164dff8b48d240b26ffd3a46920592ffec5a34902c97ff5ed1a48164bffab68d240b25ffd3b46920592fff5da34902c9bff62aaa48164dffaf555240b26ffd5aaa9205937fe9d554902c9bff46aaa48164dffb56c1a20b25ffebb60d105937fed5b04882c9bff6ad5244164dffb5699220b26ffcab54622593ff698ae4a92c9ffb6017254964ffda60b92a4b27fed105c952593ff68d2e4a92c9ffb4297254964effa20cd2a4b26ffd805e9525937fe982f4a92c9bff4417a54964fbfb003d2a4b27dfd301e952593efe880f4a92c9f7f4287a54964dffb01552a4b26ffd50aa9525937fe98554a92c9bff482aa54964dffa21552a4b26ffd83428525937fec0a14292c9bff4c50a14964effae4cd300b277fd5266980593bff11334c02c9bff5d6aa60164dffae555300b26ffd52aa9805937fe29554c02c9bff5c6aa60164dffaa355300b26ffd31aa9805937fe90d54c02c9bff16eaa60164dff85755300b26ffe55aa9805937ff11554c02c9f7f60d755c164fbfb04baae0b27dfd325d570593efec0aeab82c9f7f4c5755c164fbfa42baae0b27dfd815cd70593efea8ae6b82c9f7f485735c164fbfb06b8ae0b27dfd825c570593efe992e2b82c9bff5458a5c164dffa62c52e0b26ffd21629705937fec2d54b82c9bff60eaa5c164dffaa7552e0b26ffd82aa9705937fe99554b82c9bff606aa5c164dffaa3552e0b26ffd31aa9705937fe90d54b82c9bff62eaa5c164dffa77552e0b26ffd1baa970593ffcb9b00a82c9ffe54d8054164fff2e4c02a0b27ff95260150593ffc99300a82c9ffe5c58054164fff2a2c02a0b27ff93160150593ffc90b00a82c9ffe5e98054164fff274c02a0b27ff92a60150593ffc8d300a82c9ffe5ed8054164fff276c02a0b27ff92b60150593ffc15b00a82c9ffe46d8054164fff444c02a0b27ffabb60150593ffcc1ae0a82c9ffe6097054164fff264b82a0b27ff9815c150593ffc98ae0a82c9ffe4857054164fff314b82a0b27ff93a5c150593ffc952e0a82c9ffe4697054164effb0ecd2a0b277fd8266950593bfeb9334a82c9dff4859a54164effc44cd2a0b26ffd72629505937fea9314a82c9bff5c58a54164dffaa2c52a0b26ffd31629505937fe90b14a82c9bff5ed8a54164dffa56c52a0b else 0x51c051bea1bc41bb41b991b7e1b631b3d1b171afc1ae11abb1aa01a851a6a1a4f1a341a1919fe19e319c819ad19921977195c19411926190b18f018d518ba189f18841869184e1833181817fd17d717bc17a11786176b17501735171a16ff16e416c916ae16931678165d16421627160c15f115cb15b01595157a1554152e151314f8147a142813e1139a135e130c12c512681237120611d511af115d112c10f010bf10831068102c0ff00fca0fa40f730f4d0f110eeb0ec50e940e6e0e480e220e070dec0dd10dab0d900d5f0d180ce70cb60c900c750c4f0c290c0e0bf30bd80bb20b810b5b0b350b0f0ae90ace0aa80a820a5c0a360a1009f509da09bf0999097e092c08e508ca0878085d081607fb07e007990773074d073206eb06c5069f0684065e062d05f105d6059a057f0538051d050204d104a0047a043e042303e703cc03b1038b0365034a031902dd02ac02910255023a021f01f901c801ad0187016c013000ff00d900b30098007d006200310000dffb14852a4b26ffd7a429525937fe9d214a92c9bff4690a54964fbf8f6852a4b25ffebb429525937fe85554a92c9bff6ad5260164bffb5629300b277fd955e980593efebaaf4c02c9fdf16d7a60164bffd76bd300b26ffd7a56980592ffebdab4c02c97ffaed5a60164fefaa42d300b277fd9116980593fdea08b4c02c97ff4ac5a60164bffa362d300b27fed524a9805937febd254c02c9bff5692a60164dff8b495300b25ffd7b4a980592ffeada54c02c97ffaed2a60164effb2215300b27fbd410a9805937fead054c02c97ff56c2a60164bffa3615300b26ffd7a469805937fead234c02c9bff1691a60164dffa748d300b26ffd2a469805937fe15234c02c97ff4ed1a60164bffd768d300b277fd91aa980593fdea0d54c02c9bff5eaaa60164dffab555300b26ffd2aaa9805937fe8d554c02c9f7f5ed315c164dffb5698ae0b25ffcab4c570593bfec8ab4b82c9fef5055a5c164ff7a83552e0b25ffd8baa970592ffe9dd54b82c97ff46eaa5c164dff956c3aa0b25ffebb615505937fed5a62a82c97ffaed8a54164effb22bd2a0b27f7d515e950593fdea0af4a82c9bff6297a54164bffb16bd2a0b25ffebb5e9505937fec5274a82c9bff5e93a54164bffaf69d2a0b25ffebb4e9505937fec5254a82c9bff5e92a54164dffa74952a0b25ffd7b4a950593efe3da54a82c97ff4ed2a54164bffd76952a0b277fd97469505937fec5234a82c9bff5e91a54164dffa748d2a0b26ffd2a46950592ffebda34a82c97ff4ed1a54164bffa568d2a0b25ffebb469505937fed5aa4982c9bff6ad214c164dff956c3a40b26ffdab61520593ff6c12a4902c9ffb5493248164bffd7699240b26ffcab54520593ffc85a62902c9bff6ad3148164ffdb0490a40b27fed5248520593ff69)))) else (if i<16 then (if i<13 then (if i<12 then 0x661bf616d611b60ea60b96067602b5fe45fa85f775f465eff5ead5e505df35dc25d5a5d1e5ce25cb15c755c445bfd5bb65b645b075ae15aa55a8a5a595a3359f759c6597f5959590758d658b0588a5859583357f757dc57c1579b57805765573f5724570956cd569c566b563a55fe55c25586554a550354dd54b754865455541953dd53b753915360533a52fe52d852bd52975266522a51ee51a75160512450dd50a15070504a50194fdd4fa14f654f3f4f034ee84ec24e914e554e2f4df34dcd4d864d604d3a4d144ce34cbd4c814c714c564c3b4c204c104bf54be54bd54bc54bb54b8f4b7f4b644b544b444b294b0e4af34ae34ad34ac34aa84a8d4a724a574a3c4a2c4a1149f649e649cb49b04995497a496a494f4934491948fe48ee48d348b848a84898488848624847483748274817480747ec47d147b6479b478b47704755473a471f470f46f446d946be46a346934678465d464d463d4622460745f745e745cc45bc45a145864576455b454045304515450544ea44cf44b444a444944479445e444e443344234413440343f343d843b243974387436c4351432b4310430042f042d542ba42944279426942594249422e4213420341f341e341d341b8419d41824167414c4131410b40f040d540c540b540a5408a406f4049402e40133ff83fdd3fb73f9c3f813f5b3f403f253ee93ece3ea83e983e7d3e623e523e423e063dbf3d783d3c3d0b3cda3ca93c6d3c313c003bc43b933b623b313af53ac43a7d3a3639fa39c9399839673936390538d438a338723836380537c937823746371536e436b33677363b35ff35ce359d356c353b350a34ce349d346c343b33ff33b8337c3356333032ff32ce32b33261321a31e931a23171313530ee30b23076304530092fe32fa72f602f2f2f142ecd2e9c2e762e452e142de32da72d6b2d3a2d092ccd2c912c812c712c612c512c362c102c002be52bd52bba2b9f2b8f2b742b592b3e2b232b082aed2ac72aac2a912a602a452a352a1a29ff29ef29df29cf29b4298e297e296329532938291d290228f228d728c728ac28912876285b2840282527f427d927be27a32788277827682758273d272d271d26f726e726d726c726b7269c26812666264b2630261525fa25df25b9259e258325732563255325382528250d24fd24e224bc24a124912481247124612451244124312421240623f623e623cb23b02395236f2349232e231322f822dd22c222b22297227c226c225c22412226220021e521d521ba219f218f217f2164213e212e2113210320e820d820bd20a220872077205c203620101ff51fda1fbf1fa41f891f791f691f591f3e1f2e1f131eed1edd1ecd1ebd1ead1e9d1e8d1e721e571e3c1e211e111deb1dd01daa1d9a1d7f1d641d491d2e1d131cf81cd21cac1c861c601c501c401c301c1 else 0x8b92db907b8d6b8bbb895b86fb833b802b7d1b7a0b77ab749b723b6f2b6c1b690b675b65ab63fb624b5f3b5c2b591b56bb52fb4feb4c2b49cb481b45bb440b425b40ab3e4b3beb3a3b37db341b326b30bb2dab2a9b283b25db242b227b201b1e6b1b5b184b15eb12db0fcb0b5b08fb074b04eb033b002afdcafa0af7aaf54af23af08aed7aebcaea1ae7bae60ae2fadfeadcdad91ad60ad3aad09aceeacc8acadac87ac6cac3bac15abfaabc9aba3ab7dab62ab47ab0baae5aacaaaafaa89aa58aa32aa17a9fca9e1a9bba995a97aa949a923a8fda8d7a8bca88ba865a84aa819a7f3a7cda7a7a776a745a709a6e3a6b2a676a645a61fa5f9a5d3a5a2a571a540a50fa4e9a4cea4a8a48da472a44ca426a40ba3daa3a9a383a35da337a306a2eba2c5a29fa279a25ea238a1fca1cba179a148a122a0f1a0cba0a5a07fa059a033a0189ff29fd79f909f549f239edc9eab9e6f9e339df79dc69d8a9d599d499d399d299d039cf39ce39cc89cad9c879c619c3b9c209c059bea9bda9bca9bba9b9f9b849b699b4e9b339b239b089ae29ad29aac9a919a819a669a569a3b9a159a0599d499b99993996d9952992c98fb98eb98ba9889986e985e98439828980297d197b697a6978b9770975597459735971a96ff96ef96d496ae969396789668964d9627960c95f195cb95a595959585956a9539950894c1949b94809465944a942f941493ee93c893b8939d938d935c9336931b92ea92c492a992789247922191f091d591af9173914290f090eb90c5909f90799074902d90078fb58f798f3d8f018eba8e738e6e8e3d8df68dc58d898d588d278cf68cba8c948c638c328c0c8be68b9f8b6e8b5e8b228adb8a9f8a638a328a0189ba897e8937890688bf888e885d882c87f087bf8778873186f586c486888657861085d48598858885788568851684da84a9846d8431841683e583a9838e837e8342830682ca82ba8289824d821181d581998152812180c480888057801b800b7ffb7fd57faf7f7e7f637f3d7f017edb7eaa7ea57e747e387e287e027ddc7dab7d9b7d6a7d2e7cfd7ccc7ca67c967c657c3f7c247c097bd87b9c7b6b7b2f7afe7ac27a7b7a3f7a0e79c77975795a791e78b67890785f784477fd77c17790775f772376bb767f762d75ba759f756e753274f674e674d674c674b6746f742873d6739a735e732d72f172b572a57274724e721271e171a571697143710770e1708470486ff66fe66fd66fbb6fab6f856f6a6f5a6f4a6f2f6f146eee6ed36eb86e926e4b6e0f6dd36da26d716d356d046cb26c766c2f6be86bc26b866b3f6af86ab16a756a446a0869cc6985693e690268bb688a684e682867f767c6678a674e671266d6669a6674662d65f165cb65bb65a065856554653964f264b66459642863e16384633d630162a462736242620) else (if i<14 then 0x9d008904ac37444646e8d01118fba3404825611195a02231774ebad0120a232a41446267088c4dd2197401b5d865d007d021188ac94b6e888c9dd1a015e446564bdd1a014b44646e888c4567ba34029688cad01118920a23134048288c761b0d374e804095d0048c8acf401f4044627aad74af2232ee505a52d1197722232ee1046d5511977195e882244710444f220892065d0ee08c99743b8230824fc2dfbfcfbcbfb9afb74fb2dfafcfad6fab0fa7ffa4efa1df9e1f9b0f98af943f928f902f8dcf8abf87af849f818f7f2f7c1f790f75ff718f6f2f6ccf6a6f675f65af629f60ef5ddf5b7f591f576f550f52af4f9f4d3f4a2f471f440f41af3fff3cef3b3f398f388f36df33cf316f2f0f2caf299f273f237f21cf201f1f1f1cbf1b0f17ff164f149f12ef108f0d7f0b1f08bf070f055f02feff3efd8efbdefa2ef87ef61ef46ef2bef05eedfeeb9ee9eee6dee47ee00ede5edbfed8eed5ded37ed1cecf6ecdbecc0ec84ec69ec4eec28ec02ebdcebc1eb90eb6aeb44eb29eb0eead2eaa1ea65ea3fea19e9f3e9d8e9bde997e97ce961e93be915e8fae8dfe8b9e888e86de852e837e811e7f6e7c5e794e763e727e6f6e6d0e6aae66ee653e62de612e5ece5c6e5a0e585e56ae539e513e4e2e4b1e48be465e43fe424e409e3eee3bde397e371e340e30fe2dee2b8e287e26ce246e22be1fae1bee182e146e115e0efe0b3e082e05ce02be005dfdfdfc4df9edf78df5ddf37df11def6ded0deaade84de48de17dde6dd9fdd58dd27dd01dcdbdcaadc84dc5edc38dc12dbecdbc6dbabdb90db6adb44db1edaf8dad2daacda91da6bda50da2ad9f9d9c8d9add987d961d930d915d8efd8c9d8a3d87dd857d826d800d7cfd79ed778d752d72cd706d6ebd6c5d6aad684d669d62dd5fcd5cbd5b0d57fd559d53ed518d4fdd4e2d4bcd475d444d413d3e2d3b1d380d34fd329d2f8d2c7d296d265d234d203d1d2d1a1d170d14ad12fd109d0d8d0b2d08cd066d040d00fcfe9cfc3cf9dcf82cf5ccf2bcf05cedfceaece88ce57ce3cce16cdfbcde0cdbacd9fcd84cd69cd4ecd1dccf7ccdcccc1cc90cc75cc4fcc29cc03cbddcbc2cba7cb8ccb66cb40cb25cb0acaefcac9caa3ca88ca6dca47ca2cca06c9e0c9bac994c963c93dc90cc8dbc8b5c88fc869c843c828c80dc7f2c7d7c7bcc796c77bc755c73ac71fc704c6e9c6c3c6a8c68dc667c64cc61bc5eac5aec57dc54cc526c4f5c4dac4bfc499c468c44dc41cc3d5c3a4c373c342c311c2ebc2bac289c258c227c1f6c1d0c19fc179c148c117c0f1c0c0c09ac074c04ec028c002bfbbbf8abf64bf33bf18bef2beccbe9bbe80be65be4abe2fbe09bdeebdd3bdadbd7cbd4bbd1abcdebcadbc7cbc4bbc1abbdebbb8bb87bb56bb25baf4bacebaa8ba82ba67ba4cba31ba0bb9dab9bfb9a4b97eb963b94 else (if i<15 then 0xaa0123272326e4c855003d003d003d003d003d003d003d003d006c8ba007a007a00d913d5846279108c4d74acc23193746508c652c9c8816939100c27228468c84e1a1188a48416939115e29222ea16e816e85d44f221188831d5a8032964e4410420309c89c342315400d400953a8022eb502118c2084bb84110410c23a802a8016e85d445a8ba89eac2311750bc884626ba566118c9ba3284632964e440b49c88061391423464270d08c5500350035003500ba8aa004aed40113746508c61042104210428c8348028c8308ea009ae975116a2ea27ab08c4dd020c8e4540195e272205a4e4208c208611a3214412ea28825d45106118a20975115e84626bb106118c9b93c8463847105190e11c412783a801a801a801a805dc4578254ea0089c93c8463a80184750045d7a008baf40135d2ebd0065d519223197748222ee904488d2097719774822e808c84e1ba00911f4017404462e8088c488fa00911f4017404462446904488d208920a2312232bc22b3d005d01118ba02231223e8022b3d005d01118911a411159482248288c488d208911b861386e802e8108c4d77a04231a32846248308c508d208a11a4114234822e8108c4527a00911f401149e802e8088c5d01118ba022312234822292578488d208920a2312234642e808c8488e209771a2388222ef10444e4af09ae93988232724f1118d11c41113c8822ee9c838d3776473562f3400513203d2caef74e41ce38d0d9e807c800302ca77046128c12510c5ec801dc1698248520ee08c0a9424e400dbb20118770ce7c801346ca77046128c0dc6c8714469df2007a3aa81923546474024863aa48cbb92a04a90bd08c932111a7719a9093900156c80ee08ce164eac238ee40b2024e44238ee53ab08c19477264083508c2d8772c1a8ee28460d02d8770825092b56641232ee599048cbb8c2c9232ee3d90b549197720592465dc612f6aac82465dca484a0977197524250474696a9232ee42805dc918d901232ee3a3448cbb8cbb92315402ee22825dc55009197719412ee2a805dc91ac82774e404ca049d5a8060935009197721008bc5dc91902c1232ee30bc50445d49094119402465dc75009188919411121282264048cbb8d9c1412ee48c8160919771f5d2465dc61609197719212825dc6b20a088ba9212823a3448cbb8ca0177246364048cbb8e8d1232ee32ee48c5500bb88a097715402465dc6504bb8bba720e347562f3409907ee97579071a680178c179a00bba5d5e40d022f31a9907634d005dd39031a496165a0198d34010d8e8022b3dd2a04413ab08cc5a01197718410465dc708cbb88acf74a804f0e442333484465dc6d55119771a23482268088d208d20b742b288c9dd1a014b3aa88cadd1118bba3404825651195a02231774baad00af1c8446648288c4ce1118b0d55d6e else 0x423174084626ba1446161c5d4408fa009118411f40135d0a230b740b5d094805822ba08fa00c11f4017400823e802047d0044dfa0223182327826ba18461e8108c5d021188aef408463e8108c45dc25dc310425de208a2095e144109770b5d084109778822047104408e208a2082314232ee28825dc461a20c231c41846288308c4d74288c210425de20881195e115d0471047105118a2093c1223e802e8088c488fa01d51a234822447d00488fa01c81f4044624464f055025485e846ddca8e41e080aa3944234ea146488c490511891b846c8424bd559108e3b94152c8c8108e3a8523686c80f5611c390e260e21621b87c0ae57ab08de4477235d0b108e3b91c347584215c8e182c87d84215ca164364237911dca75611bc88ee4872756108500f4586508de447720588470e43d91ae8588471dc9065194370681eca165194390f64096f54294218ea15cc024e40294651d4291ac302d8eb0842b963ac218821348d763ac2188248eb086208572071843104269210c7588215c91d5e442188246bb1d610c4124758431042b91c30718431042b9438bc88431048f230d1d58471dcb0e6118320687543d1b0d43279108e3b95eac408ef08c8f222047784644bb1023bc2323c88800ca3bc232bc88800ca3bc232832880f223bc232d207ab08e3b92903c88471dc94812ec238ee479108d1947724227908ca3b911952079108e3b970d3d58471dc986a11c7509a4c3497611c7722320bd08e3a83d2a328471042f4750686c34f5611c7507a50bd1de118d2ec7784630bd08e3b83d24237ab1dc1e923b85b10677919012e85b0471dcee183387a0b608e3b982de407911dc89743387a84616e3b981185b8ea0d0819f2005b0471dcaf221185bc811d41a1b204237911d41a143385b0471d41a15e46400460d0908c2de408ea0d0af2033c771e40846f223a83428320cf08f203c88ee68eb0683383424770b624ba1781285b0471dcc08c2f4418ee488217a3b8e11a5d8831dc808c2f477068404616e20c77244184617a3b83428328471042f4772e4079108e3b932025d8471dc88c82dc238ea0d0b9032e8348461a4a16c297430dc297429761b8911c4186e386e18830dc50dc24e42f089c92111750932246228248c45a8ba88b1175114124222825d444dc2cd40185024222824e44ce09c94124244bc4e45500248ea00aa012315400d400d400d402722a8048c9c8ea0049ca5e1338081524222465d441286c898d04a0939113709412ea22d45d44125ea8832921105024222824844c68919412ea409448c450491889bba9114175220bc1a8010bc12ef50055003500350091977185e0d40083c0d4009412ea22d45d44125ea88329751050242228248444e52f08a0939113902a48464dc9908a093215400d400d400923a802a801a8048c550035009c8))) else (if i<19 then (if i<17 then 0x560dc7543b962c81e083c83aee238ee1c50158281d54ee40830cb905c8c349dcc1b83283203c107ae9688ee809c1ece41d58469dcc106eadc88469dcbdd39c5d5b915773b85984680b01ba11a7720500dc08d3b93ba7380b475411943281e0dd75611a773041e70f23ba6770b508ce1079c432cea5783dc23386f0f67203b903e0650ee88480c820e21b901f30d4773f743aa148e422328410f7c82eae1a4ee62bd8682d07a3905e701e82d223261a0ca1613b93ba1d50ac02c2d1c8315d0830cb905c8c349dcf9d42b00b6ba1e81085a0828c439043d67702c1670d35d401d0961e8291320621c357203d0710b214920a4370323909dc3894e40750dc57911940ca7748215c9dd0af05a39008ca16032c214ee40dc0c832dc88469dcddd0283d5cea57a119820f380f45773b85a84670b40c820f38ebb9dc3dc2344412bd1dc7884af47788215cb1063b89ae8410ee15c91de20857181ec431de208572d380431063b91aed380ae61a20c77315e8831dc607a9c4210ad1de208253b5d0821dcaf103b84144638831dcaf0f1095d8ef104815a20c771832c431063b95e286a4ea206288448dc2c9d51a4147220c29d448dc2c9c8181244222788e45756e4623c351dca16f201d50ee4c4617b0d47726403ab8693b92e4623c818693b942105e8465a23b94e41d5c8108d3b96eadc8c818693b96eadc8c839033bc233640c349dc790011a771e403aad4c11902f640c349dc8f2320e40cef08cb9042f677c8108cb901a98771877c8088c788c2de1a8ee4391901118eeae23c818693b943d61a6a63c8088c59030d2771e403aa16da9931185dc818693b943d1680b790720173a6230f416f20b53307a2d172320834c806047900e40324ee50d3907201c80ee88cc08c1905e4ee0d0b900e40236a648479013b8c2de40c349dc8f5720e40cef08cb9042ee40cef08cb9042de40cef08cb8682f4771dd5c478682f4772e1a8ee2082d4c3b8f1185ec351dc988c2f6408ee0d0a48011c771bd54ba61b0d477285ec351dc610a1185ec811dc129b0d1c80ee3c8088c3b8f0d05e8ee3c461770d477205bc351dc610b11e1a0bd1dcb900288c1908ea83212390642c80139190059003900236423643d032e8d918460937e8026e8108c126fd005d009908ba92312d5085e0923084b08c226fd0044dfa00891f40104ae8020bc128248c44dca0882f058000a1740192226fd0044dfa0080507a00c91137e80226fd004057a008ba849bf401137e8023aa124610bc1353d00648c250c911410b740b5d09320937e802e8032444dc990ba01321123093924622ea48c4327a00891f40114109412ee228232444dca088a0923103c0937e80226e4c85d0024c83d006c8811f40135d082c0823e8026e81047d005d02118a1187a04231740846284616e808c4d743d02118ba else (if i<18 then 0xc943b8d9e8088c81341be1ae80364addc1e8211b2904b0dc6c88190735abd008964ba86a0f80d0a08c338a0d04aef4086408c6c94ae83b8641046c940dcd50fbd006c960d062c87c6e80d09dd16c8236a615cae1a2cc236e815caf221186b6a60ecad742c87a84615cae180542308c1043d192c8430e615c83243387a04217aba61ae80807c1f40df401b2506f86ba00d9277444690619259283208320875e8108c708c2097718672ee10411923ac2317401b308c78683d05be80754a0d7a0223185907e1e92090012036e1a0a44c460742df403aa5c3410a81042f0c0f04144630b25dc20852203c09d5087d006c900f0c8e8008c6c94218c8e8036480ec2f0411b24076178208e0d046c835e8008c8367a04231841046208308c4b23a00d90464a05dd2118590a452ee0b820852204bee8d74118572d02066dd0291025f74056d4c1f968135d0b3dd2a0052302d06e1c61185729770561042910067748820ac0f05232591b21083e87a067d00fd0111898730203a10c291464867eba0741a839ae986ba027a00d944633aa0cfa00d920d948220840f83e81be80364c1341be1ae80364a1641f87a4824036d77a00d923020b00743d0522c591921e80e8210fa1780df404e230ee06fa00d92f74c469783d01b591d00f1646481e8641e80e8ce0ef86ba02811a411077e80366119064f740bdd021194648d50efd0211970d0520850d050d041a85e0fa0f7a001e36230ee0f40f7401b264b21e86707707bd000f1c6a87703dd0111959c0d50d00792094ac8d907f10485646c84307a104a9dc230230820d0b068206c2f0d9082406e366208c648250781041197ae8d94ef10480f33bc231b3104b9dc6c423882094a9dc2185418c98bc0d53bc4128681b3104656464e770f41741081d882819317838a2388251922322f01d0e2086209c1e066406640d9103c0937e8017864dfa00891841e04048411137e80226fd02640c91f40113728228469de2c8fba054ceb17a11c5930088ee08c20a59280c8ef08c20a592e400da36429101e02d8ee1489c80168d90ee178bc82208d98ee4e4032416e2309a1523b9c3c83d0bc364291464ba98bc14a11c7736290e30842947704a6c800f0290e2c8154461dc2917200d90bd1063b85234590e390111c770a4600e364366c88471dcddd0ea85e1b308ca9dc2f4231b2435357611a771b25ee917aae8d9846501697a1182d0829dcc36433f5d26408d3b9bba02d6ba364119464807265b2211a7737744bc36611902bf740bc4ca11972051a0a43ee908c1905220594ee1042910360710cf900291664774265900291415f7488207829146c8770ae106119419477046104291611c771b2319201c16c5e8471dcc0b438c77082148a4ca3a85219d5082d47224464c848e4eaa230e244821ec5757905c80b386a3b98ec8 else 0x961088e405a84230cb08447421089ae85a842346f084138e10a41100fb0c09e10929c22188215c91061c95e1c4144257871041e95e1b5d4431042b9220a21143988215c615e20c39182e44310471043d082bc410f43a710e42bc4184258731061095e21866ba0969c439883084f1061c93c84248721481e8e9c4398820f490e40a83d1c3988215c71051095e193c443104657a20c391c4144222bd1041e8e2083d14412d01b93a871442630d10520a750e2588216910c3220256708e41724144262788e52082e24414d41c6c32752c412d0196c32752c4106416ac3221293c07a904171012a39278905109620a413b28c89900390039003902a9c751e400e400a5dc80244790050cb204751bd58479007902119681c23c8028479005902a98b200720072004e46401422aa624eb90059013a8b2007a107a0a5d0f4246e4d6118c3d06114320f437ab900590031d7200b20052ee401223c811d47900361b204740f04b91900572111e401dc8c8088c69772008eae404e838ba5a111e40235309863aa0c91190191c8c809d089772009a9852eb20125d0f42b0d0c83d0f2027586488c8977200b2005eae401640a402391480590039002977200813a3716400d86a4020bd0e6a98f2005e16400bc207a107a17840d21cb53183287220bc1344754194391834c810e461e821e829743d09eae408470e499021185e872430c97412e408470e4c0941ec391c3907a28720f450e41e8b2005e16400bc20799021c8f204380bc3640107a17840f425a219223c80430d0cb200f204321025c8088c1a101e2418643b0d900561911968c80406561b20223203c0680f468e41e02507a4c808c84d77a00d91837085d006c86728c98ef1041292e4623cee1f40d9d5e80707403aa19c6757a006719d5e8019c6009a0df0d4d5e80364d08e20825187b06e3241ed74e80078e3240c81ee801c4a0de647401a108ca3241bf4006b08cb1646483703207a20986483c03c0de20825300139d503c5dc95dc1e834047d002f181b85ee8009480dc3d2c8e8019cbdd012f401b24ee9c69ae85220d902c3603d11ae8580f4c682916a007a0a43a803603d0522049a801e82913a00d81b2303a1e8290d9187a6ee16e647403377647d006c906c87ba0251b1d006c97ba720e71c6ba00d933230ee06fa00d928759901f7a00322cc8065d0091901c85e064504948c1c87d065323a0180dcc80efd009195bb8320360842f14133c86bb08c2b91c31590d55021185730598eb08c2b902190684615c816611bc88ee4a0d104320670ae507c367a0067275dc461e82f7400ce60f40741a85ee8019cd88c6c0674829dcb1770d7401b245aa1f419f401b251aa904bb8d92623aee1f40df401b2606f5d30d7401b25ee8d001a0d944654ba14ba14ba1c461341cb741b386ba01c26837c35d006)) else (if i<20 then 0xb8ba001d135de8007465d7a0223086403a9044a191974008642ea07833878e80074c88c38f401b241921a3a0223222306bd006c9064a236ee9048135208d9183e19290511903ab5de803648757a03740f448ba1a3a0223274019c1506c90eaf404463591d01ba01d22c8e8088c617911b7748240729046ca5e21d50f490461781f24144644bc075208daef4003a36bbd000e8dae81de8036ba9040e8d118d903dd021901d30c96bb08fa01038c23e803192f5611f4027408462591d02118dbbc23482319297a11a412423482203a9044077a0080ef40135d03bd00708fa0080ea411043e808c862480f74084644921d464f40222303c1c7a0112484a03cf542d940f068e8088c8078672230a8403c0d7a022327406e80740f13a02c84640740f140f740446303cddd2083d201e4820f52f102101e07a0d080781f03f446403c0f5208d1181e03a3e801c4218d3bc411277882204710449de2082318c988208c2f122082314414ee28820fc2f0e2082314414ee203710441780dc411a3907a08e209011c41103c06510460f62081e18c90d088e20a772a770f1104649049223882324832412c2388240e308e208c64bd584710481e211c4118c94bd08e2091ae8d984710488e620a32846407b10440f620881ec41103d882204b08e20a32202547910611906485e4ef10481c53bc411949192f562085b28684471053b90648ce88288c2a141aa2388238829dc41780ec411c41446203b10451040e882f44103a388288c218c0ec41123288210c60784643c03b104a0202a080605410ca84615224912705e1b214880b418a21185e05b0e460f42b881683d102d0bd90060f4168ad483d05b0e483261cbd584240221a41e8d9022187804c81b464bd58ea40d41b5640d9c8001cc19dae84618678ea284659e3a8c33e4010012cf08e3a90268571b238644c9aea751b250d44c93a8d64423264305a8e46ca5e202d472205a8f00384121324ea226508c4b2211932182d47224d407803d1a202d03c104059064bd588308c80ca1185e017104a05ad4a3944244723651e0d118710da9d4807899089922348234831d449043da21187b8ea20f7574e4c7522410d41e861b83d09aea410d41e881b9eac751a412d11d461ba3a8832c75107c0dc1c6aec212a4109d08461f21088e842111c8842148673aae9c984240dc1ee108c37421106e0f420f81e84d742d07a1a3726b08469043d089ac320f50849105eac7518650a0884619437221187b8ea26ba90430c7522192f11d46195108803d862f11d489aae42751865b909d4616ae42211a416ba7653a902c86a3aa9d495762c9680dc9d4ad742d22119863aa16910902c8320c27213a95aea410b21e88d74ec07a1b5d0b48846d752087a1d868647643d10372218649d481403db5d84240ca1b838c2120507ab08461 else (if i<21 then 0x64867e801e8832591f4018c908ed047d006c87a1b23e802e80d045d000e886c8750ce1e888c83d0d918d9647d007d011901d1b241b20e7a03412075e810c89190a0b7707a30725041283d23c808c20ce5642b0c33b8610670fa1e9ea921ba750cfd01e415ae8671b3d003d153a8674461c421943385e4ee904819c3d241186707c88d20a7728670789dd20903387a03634ea88c3381b22320861e870dfa03861f404462447d026a8fa04d54463446904432520a231a234821786906118a118d9482319308c2f0d11c412ee31905de208c90bc519288e2085e22d52ee9046c925483e4463252097734a9cba904bba5e19264461d7a00d92068e8088c7d01118d91a230ebd006493a02231923446ddd208c1a04d1b2307c905118d2f04d1923e80324650fa022310ca4822e80364118c190730463047d02ba0fa007a5aa3e815d0118c6c8412ee30825dc4104bb82318412ee2e8006eba0fa05740460c88d77a017506440825dc5d003ead51868e8008c60cba05740fa404619c41f4209771b86e815d070683e8671f40aba08c608fa055d1f401b208eae92ae82308231b3574208232023aba364af13a001baba3e8008ea98fa001baba3036106ae8e1904613748641ac6f2023080643200a3864e1850dcba8c9e80f20a0f16af400f44192178bba4122412ee207c88d20977203c2ee9047d000d89aef4003632ebd00406d208a1bf4070c32ea19c38f4086406cc3243474044644461e3a00c92092447d00649064a236ee90483241f24144644469046495e2259e810c861a219740446419c88fa043222230f1d0219112cf407910c8824911f4086446ee88e1924122590bc90619101f43248288c888c1e241864470dd02190c2dc231475e8108c6d763af4084642ea0ce118e118412ee3846104bb8e118412ee3e80d740dc23274003708c65d419c23181be8108c61a611880d8418463e815d019c2327400d308c708c0d86718c96ef08d2092118d9482384657864a4127401b22e800c83d0fa022310541b2206bd01118d11a41105e1b220f490440fd118b0d032e800749d00ea81d1f40446203a9044323a061a03a403a3604323a022318c803a90472180e81e1c8603a36465de2088bbc4110498822447104bb8d118540bc34471045104bb880ec41105e03b10464e511c41181d88228825dc41780ec411c4144620780d2208e1e01d03c3047d02ae8fa055d0463e81574118d92041046178608c2f0411b240bc1046482327400375747d000dd5d1f4004754c606c2085e184103c2e8108c5d0211882dc2310798462e80b22118c20c2310c9846978610611881323c17408462e8108c4d77a04231832846208308c4a1ba0423184103c2096079ae84625022d40781591248c9e80f543e9564042e800748904649774bc44825dc1a0c1f2234825dc8904b else 0x1575aef406e8074bd006c81d1b04abad77a0123235d0bc074a091aef4003a326e3640f740864074dd011901d1b040bdd000e8c3ef4003630ce1f4ea833207d0f47541992ae87de8006c81d7a055d0fa06ca1f7a001b3aa40fbd000d8c3a8710fa1ea1901b31d50f4244719d3a8c1a277446330c1d7a006720230689053b901907d0f40cc81f7a035d0364065d000d8fa02230869d480c83ef4003642ba1f7a001b207503dd003e87803664469d6338d3b93c44638ebd003d0c197400f419c89053b89ae87d8831dc91063b891187d8831dc81f40dc41187d8831dc71de20883e81b88230fb1063b8d11c674829d489dd118341f406ba19c0d93a02320ce06c9d01c306703640ce9053b8e20c23103c0d31041e9065423124108e207614359745d01ba0c91944e80325118c650c948230ebd006c8c7507a8641c481a62083d18230e30c83381b2a41076207690440ec3d02ae81b1f4003620470ca6a81b27408462e8108c406fa0081af408463abbd01ba01b2740036d747577a02231f400362e8006c45740df4018d90470c80f01b282d0b628825dc406e20880dc41135d03710471040d880dc41115d88206c62b40dc41185e03bd00607620883ad5d193d008977a00731832c34323a037403a6e8108c424ba04231a1907a0e620903484104a08c81a62083d1c412ee20bc076208e20a23103d2ee204619fa007803a5e8088c40ed208ba055d03a3065d000e8c6545e03a30769045577a037403a4e80075ae8c2f74003a3e800745d000e886c823e810c80e94baf4008708c81c7a0374046078a4dc13a23183407a90469041183d1f408462e8108c4d77a04231f40846203bd0041780ef401892e8108c7104bb880ec41105e03b10464e421a23882403b1044076208a2081d105e882074607620884643c03b1049d01ba01e03a41949780f01d235de808c80f01d2a2204e0740f100f03d48230fa1a5208fa04232d19063b940ea41105e482074607520881e03d06831b20fc2f0c6cf409aa3e8154c5d002f0ba00d903a1789d000ed5d184b016504161)))))
def livel11 : Packing := (1644,4,7,10,4,16,0,lived11)
def lived12 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x3ffd8148164fff5c520593ffd5148164fff4c520593ffd2148164fff62920593ffd7a48164fff56920593ffc5a48164fff4e920593ffd1a48164fffaa920593ffd8344164fff5cd10593ffd8244164fff5c910593ffd5244164fff14910593ffd3244164fff54622593ffd3188964fff60222593ffd5088964fff4c222593ffd1088964fff95622593fed7254964dff66952592ffd7a54964f7f1e952592ffeaa54964bff428525937fd9a60164bffaa980593dfd755c164f7f5cd70593dfd715c164bff62970592ffeaa5c164ffe60150593ff97054164dff66950592ffd8a54164bff5e950592ffeaa54164ffe60130592ffd7a4c164ffb54920593fed2148164ffe5c120593ff93048164dff66920592ffd8a48164bff5e920592ffd5a48164bff4e920592ffeaa48164ffe48110592ffd7a44164bff4e910592ffd2a44164ffb54a22593fed2188964ffb482225937fd2065d64dff441975937fd7564964dff549925937fd7164964dff545925937fd3164964dff485925937fd8064964dff5c1925937fd5064964dff481925937fd1064964dff169925937fe5564964dff61d905937fd8564164dff5d5905937fd8364164dff5cd905937fd5364164dff609905937fd7264164dff549905937fc5264164dff4c9905937fd7164164dff545905937fd3164164dff485905937fe5564164dff88990593efd8758164fbf61560593efd7558164fbf60d60593efd7358164fbf54d60593efd8258164fbf5c960593efd5258164fbf14960593efd3258164fbf5c560593efd5158164fbf4c560593efd2158164fbf95560593efe2258164f7f54a77593dfd809dd64f7f54277593dfd309dd64f7f48277593dfd109dd64ffb5d622593fed7188964ffb54622593fed3188964ffb60222593fed7088964ffb54222593fed3088964ffb44222593fec5a88964ffb95622593ff98780164ffe61600593ff97580164ffe60e00593ff97380164ffe54e00593ff98280164ffe5ca00593ff95280164ffe14a00593ff93280164ffe60600593ff97180164ffe54600593ff93180164ffe48600593ffa5580164ffe88a005927fd9a14964bef528525927feaa65d649ff569925937ee22649649ffaa9925927fd8a641649ff5e9905927fd5a641649ff4e9905927fd2a641649ff469905927feaa64164dbf65560593ebd8458164dbf64d605936fd9158164faf50560593ef98058164fbe44160592efd3a58164bbfaa9605935fd929dd64d7f64277593cfd609dd64dfb656225937ed9188964feb506225937ed9088964fbb58222593dee7788964fdb956225937f99880164dfe65e005937f99580164fee612005937f99380164fbe58e005937f99280164dfe64600593fb94180164efea2200593dfa7780164fde95600593fda3380164ffa88a00593ff21180164 else 0xee5d74750844126ba3a84220921a754231dc8204ba3b84644825d08c7724352e8463a88259747708c4124ba11c803b925d08c771049204ba118ee4976231d44126e990634a05aabb9912ea462f2b74c8338b56c85dd1a48e5d50556ad90a02468d2ef29a82812774c8338c69d5502c848d7756418d2802cee89c2462f2829505774e05e48d4036e990670a00b28d2ee91d90a0a92346977b2140504dba3ab906342f191a01c59dd320ce1a9c6ac8d01083065ae882ba0466dd1d5720415657757423420dba28020baabb846754c415d023220c196e8a0083aeaee11a1405757708c8196e8a0082e42ee119f5d5d4231048a02eea984620975d8697488d77d00dba3ab0d44720b91a01e1add35d88e410cb403ee9aec83a00465dd21a88e417234036babbc46209232fc5f68b6b1582285c484884b0ef21aec2f4857b09a2118c1f0834b056a082c0ba80df00e1ff1bfb67eaefb91f42be267bb6f641ea2bcd278faf079de9bb9276b6ec41d67baac74eae921d12b9d07332e499c59b85e6ffeded1ba0b6e26d2ed981b0ab5a26a9ad409a51b44467a2ce699acb30e6586ca09916b1f66392c5f989eb1066176c1497f9afa85ee2bcc176dae865bfeb6816a5acec5942b1595f6aba256aeac59556aa3a53f2a6b94a7a8fa5136a141407a7ba4ede9d09380a6ca4cd698592dba54e4a1a92b9240a42c47c28e811b4a350461e8b1113ca210433a8549079a0a840ba8070fde9f5e3dd67ad0f3e9e323bce7648e8f9cc038d67030ddb9b44357a6978cff99a032d26450c6e986a2fee5eb0bb5972a2dbe5a50b2996122ba255f0a9894f0294a5168a0293c426f24cb897b92ac24d6492090391e4236e46508a99108217a41c8818900e1fd63f207c88f321de23b107418e421c2a37506d38d521a4a33e066a8c8a18ba30985fc8bb816ee2d285848ae6154a291850789e2137e26484b2892e12022350453887a109a20583f487bc0f1e1d8839a86cc0cc618382d285460a0a127022d841007760de819282da055a096011581e0036605f009d80f0014a01b80168000fff5e952593ffd0a54964fffaa952593ffd7560164fff5c980593ffd5260164fff14980593ffd3160164fff5e980593ffd5a60164fff16980593ffd2a60164fff0a980593ffd1a60164fffaa980593ffd525c164fff4c570593ffd8a5c164fff56970593ffd3a5c164fff4a970593ffd1a5c164fffaa970593ffd8754164fff61550593ffd7354164fff5c950593ffd5254164fff4c950593ffd7154164fff4c550593ffd2154164fff62950593ffd7a54164fff4e950593ffd2a54164fff46950593ffd724c164fff54930593ffc524c164fff60530593ffd714c164fff48530593ffd8748164fff61520593ffd7548164fff5cd20593ffd5348164fff60920593ffd5248164fff4c92059) else (if i<3 then 0x11ae96aaef0d68080ddc8dd223904d5868d9d0121e6e9aec4720e80191c75d035dce17408cceab90aeee920e806c84681677488e417561ad00ebbc462f0824dd023178d93234036e820d91a004651677450102d743f5dc5708d21b88511ae9642ef0d68080ddd5dd223178c8868d9d0122c86e2ebabba44720d910d680a10b74906c8d0023306e216e911c820f5910d68099dc2317841206eeaaba2f4ef119b220a0420f025d767708c41386e214ef118bc20997748da9323402e802f09a948d77468c8d00c046e9200bd3b8462c9ed59745e08e591dc41386fba6418d0bd2019111ceeeaa829dd320c683c3667788cc8900525e41200826cc463b8bc70b7204e2407544117a231dd2d4c52088bc290463b9c59c8240106231dc5e3b52350cf640463b984add1d590277320d9178234864eaee920082995913b84696a459dd11a07a4001e773205e08d6190bc3b846209640365d508c7728dc16d0d204473bbaa71055dc81d57221a1dcec30b2350e3903ab0d0ee80df74c8338901c886a7788e417556c30d409064312d1ae8463ba774ce04e755c89dd5d08d0c302420e7037480eacee11a46a0c861107207221a1dd01bee9902bd203ab0d4ef11c82e42d5d0df74c8338900597561a7227788e416833ba2792006f904eee4064916432dd33804a407227708d2eab909c442aeabc2b8ee20a5c8884571dc412b0c1927012eba108ee20a1d58855e1dc412b0c2c883ba6712064120bab3b864b16432107749001586a7788e417217204462ebaae44343b9d86902237561a1dcce448111cef0d3aa6618329025d5a0231dcf20482eab90a9cee119d86906407567708cc1948111b910d0ee67562386a77901c830bb203ab11b913bc3520a0230de4088dc89dc32386520c80e44ee1199c87562354c5e1dc413b0d2006911baa3b88276183290025974231dc414480eac462f0ee20998690623901d59dc32386511c353bc8120b9075dd23354c8d00b6aa462f4baba235a01f7448c5e468d5d00d2ee80918ed548d77468c8d00da00bca08c4917b40754824e802f0c595dd2317938d00cd4aee918bc90271a01da948d77b217446b403baa91aee24a34646807165235dec846b40350da02463d003c50461e680ea8d7748e86d01d52a92eab90bb8470d2e8aee8095ddc808e1a5d340304619680ea90325dd747234008cceab90bbabba0046672177d002322eeea8470d2e9a01823869c8d008acaba192ee11b910d680808dc8d003223aabbe80119023105771a92eab90bb846ae88275ddc808c412064bbb901188255ddd508c41230d11aeeeae8019183288d7786b40720c54990118ee4dd086500d51782330ee118b2311640756c808c7730b3ba6418d0793bc4664480912640b20231dca2ceba118ee408c771646033aa118ee41675d08c77205201390118 else 0x15d363403648ae8f5ba6ba91a826c83a8d680add3200f032d00d930eb118fa2f4e90d680eaa075756239de74869c8d010ac952ae8ea33ebb11cee3d1b33a435a0347588d3c9d0231f5c8d00324d52c3078190ce12eba118ee20a875755c888e771f41b577404b0c3ac343d4473bbab3a037a028231d5d5d006728ea194473b8fae4037a020751e9c8d00672b0c196bb118ee2098321e9c888e77d0067384711cbb3bc35a01b27b565d09577178d908c4141ab1183720ae9a01b273577488c1b90740364fba483a00466c944d3237488c1b907403650bbc46209b2413423dd2239065d86b4036523a8b2e406511aef0d1b2ba1aba02d861d5771e82335574d0032499ce4065ba4826c9aba00469166239dcd586b40720e3d2ee11c346ae80191c920cb74906d5d002338ae1c8b2e42bc192ef119b26a882b6183c094325ded508c4140b21c847aeaef11c642f08295dc1b720235d032d00ee42ee119b2196806721770cb4008ca2c836aeaee11865a01d7706dc808c32104da0391118cd957577d02232865a039111904188d771992eab90bb872ae88311a177754391062328ea2483ceac462f1b2ba43464680b1647508c1e1c6235dec85d21ad01624c462dcee64435a03aa8079d534374178d93234008d20f06bba48364680119ea91d4230ca230743c5d0c886b40584654ee91183a1e434646809aa432dd03c3234008cf11daa11882bb9457124d988c771045e38b21c8460f0681907abbc462f082baa432078255dc5e08c41455211c460e8ee2f082708c320775d88d775d01bd01226893ba3ab118bc0d991a0255d164238681ddd223905d506f40587a11baba003c50cb74d7641d00233046192ef118bc0e88270cb7488c3d17b40078e196802f0463bc82632740756771795d08e41468111baa3bc8250e74017a4122b26ce813baba11c8270e74008c3217a4136813bbaa11c8250f4a9c817750740178f549b21f2703caee91a41a00bca3643219d74469235dec8d013ba23491a8219681641c329df40b21232865a02ee918bca09b74c8286ce31a6a7403651ba6418d1b22f1aa646808122a9dd320ce31ab217748cd91b540149a1bee990634641aa2f1b3a024d9dd320c685e354c8d0101bd0dba6419c6356a9b3a027740dd230f340320323a0c350cfae8ac118ee70dc420f35d8686788e419d34056e911c830d1926ae807354c8dd241d00d908ce6a990bbc466c88260dec82a65d88d775d21a3674050941bdab646e92ec4720c346ce80b0c823106d55d3403065ba046209b26ae80716774500571075d5dc3208d21b879))
def livel12 : Packing := (246,3,7,11,4,15,0,lived12)
def lived13 (i : Nat) : Nat := 0x5d1ab208d17a80c83964bb746ac82711a64501374900f064a9a0320ea94357446743b86a80824dd1aac811904ba1aa0250d7411905aa1a19501174ae90680232aa6e82320b2035403d02ba7711904aa9ba482711aa0320f746ac8191388d174ee2320165629ba482711a20320467748a40d74904e0815d0d1dc46415974461a3b900826ba35641388d322807ba482711a64500d74ae8684641a01a48c3b7eeea9aa3075aaa452fa1b3665747a8ba0ec0ec007ff5c964ffea92c9ffc52593ffb00b27ff5c164ffea82c9ffd30593ffa40b27ff44164fff112c97fd97592ffb24b25ff64164f7eb02c9dfe77593fdc44b27fe80164
def livel13 : Packing := (17,2,7,8,4,11,0,lived13)
def lived14 (i : Nat) : Nat := 0xe8ba407034806ffd64
def livel14 : Packing := (1,1,7,5,4,0,0,lived14)
def livelevels : Nat → Packing
  | 8 => livel8
  | 9 => livel9
  | 10 => livel10
  | 11 => livel11
  | 12 => livel12
  | 13 => livel13
  | 14 => livel14
  | _ => emptyPacking
def liveindex : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 2 10 4 10 2 4 (hashlivel9)
  | 10 => lookupWord 53 206 8 15 7 4 (hashlivel10)
  | 11 => lookupWord 534 2159 12 18 10 4 (hashlivel11)
  | 12 => lookupWord 1024 4145 13 19 11 4 (hashlivel12)
  | 13 => lookupWord 171 693 10 16 8 4 (hashlivel13)
  | 14 => lookupWord 16 62 6 13 5 4 (hashlivel14)
  | _ => fun _ => none
def live : Forest := ⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,livelevels,liveindex⟩
theorem geomlive : graphValid live (boundsBefore known383) = true := geomdead
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive8_0 : block live 8 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alllive8 : block live 8 0 4=true := slive8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive9_0 : block live 9 0 15=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive9_15 : block live 9 15 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive9_51 : block live 9 51 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive9_87 : block live 9 87 8=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alllive9 : block live 9 0 95=true := (@block_merge live 9 0 87 8 (@block_merge live 9 0 51 36 (@block_merge live 9 0 15 36 slive9_0 slive9_15) slive9_51) slive9_87)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_0 : block live 10 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_6 : block live 10 6 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_42 : block live 10 42 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_78 : block live 10 78 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_114 : block live 10 114 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_150 : block live 10 150 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_186 : block live 10 186 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_222 : block live 10 222 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_258 : block live 10 258 16=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_274 : block live 10 274 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_310 : block live 10 310 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_346 : block live 10 346 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_382 : block live 10 382 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_418 : block live 10 418 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_454 : block live 10 454 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_490 : block live 10 490 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_526 : block live 10 526 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_562 : block live 10 562 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_598 : block live 10 598 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_634 : block live 10 634 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_670 : block live 10 670 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_706 : block live 10 706 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_742 : block live 10 742 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_778 : block live 10 778 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_814 : block live 10 814 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_850 : block live 10 850 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_886 : block live 10 886 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive10_922 : block live 10 922 9=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alllive10 : block live 10 0 931=true := (@block_merge live 10 0 922 9 (@block_merge live 10 0 886 36 (@block_merge live 10 0 850 36 (@block_merge live 10 0 814 36 (@block_merge live 10 0 778 36 (@block_merge live 10 0 742 36 (@block_merge live 10 0 706 36 (@block_merge live 10 0 670 36 (@block_merge live 10 0 634 36 (@block_merge live 10 0 598 36 (@block_merge live 10 0 562 36 (@block_merge live 10 0 526 36 (@block_merge live 10 0 490 36 (@block_merge live 10 0 454 36 (@block_merge live 10 0 418 36 (@block_merge live 10 0 382 36 (@block_merge live 10 0 346 36 (@block_merge live 10 0 310 36 (@block_merge live 10 0 274 36 (@block_merge live 10 0 258 16 (@block_merge live 10 0 222 36 (@block_merge live 10 0 186 36 (@block_merge live 10 0 150 36 (@block_merge live 10 0 114 36 (@block_merge live 10 0 78 36 (@block_merge live 10 0 42 36 (@block_merge live 10 0 6 36 slive10_0 slive10_6) slive10_42) slive10_78) slive10_114) slive10_150) slive10_186) slive10_222) slive10_258) slive10_274) slive10_310) slive10_346) slive10_382) slive10_418) slive10_454) slive10_490) slive10_526) slive10_562) slive10_598) slive10_634) slive10_670) slive10_706) slive10_742) slive10_778) slive10_814) slive10_850) slive10_886) slive10_922)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_0 : block live 11 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_2 : block live 11 2 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_38 : block live 11 38 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_74 : block live 11 74 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_110 : block live 11 110 11=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_121 : block live 11 121 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_157 : block live 11 157 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_193 : block live 11 193 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_229 : block live 11 229 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_265 : block live 11 265 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_301 : block live 11 301 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_337 : block live 11 337 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_373 : block live 11 373 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_409 : block live 11 409 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_445 : block live 11 445 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_481 : block live 11 481 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_517 : block live 11 517 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_553 : block live 11 553 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_589 : block live 11 589 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_625 : block live 11 625 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_661 : block live 11 661 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_697 : block live 11 697 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_733 : block live 11 733 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_769 : block live 11 769 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_805 : block live 11 805 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_841 : block live 11 841 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_877 : block live 11 877 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_913 : block live 11 913 24=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_937 : block live 11 937 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_973 : block live 11 973 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_1009 : block live 11 1009 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_1045 : block live 11 1045 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_1081 : block live 11 1081 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_1117 : block live 11 1117 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_1153 : block live 11 1153 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_1189 : block live 11 1189 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_1225 : block live 11 1225 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_1261 : block live 11 1261 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_1297 : block live 11 1297 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_1333 : block live 11 1333 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_1369 : block live 11 1369 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_1405 : block live 11 1405 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_1441 : block live 11 1441 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_1477 : block live 11 1477 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_1513 : block live 11 1513 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_1549 : block live 11 1549 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_1585 : block live 11 1585 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive11_1621 : block live 11 1621 23=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alllive11 : block live 11 0 1644=true := (@block_merge live 11 0 1621 23 (@block_merge live 11 0 1585 36 (@block_merge live 11 0 1549 36 (@block_merge live 11 0 1513 36 (@block_merge live 11 0 1477 36 (@block_merge live 11 0 1441 36 (@block_merge live 11 0 1405 36 (@block_merge live 11 0 1369 36 (@block_merge live 11 0 1333 36 (@block_merge live 11 0 1297 36 (@block_merge live 11 0 1261 36 (@block_merge live 11 0 1225 36 (@block_merge live 11 0 1189 36 (@block_merge live 11 0 1153 36 (@block_merge live 11 0 1117 36 (@block_merge live 11 0 1081 36 (@block_merge live 11 0 1045 36 (@block_merge live 11 0 1009 36 (@block_merge live 11 0 973 36 (@block_merge live 11 0 937 36 (@block_merge live 11 0 913 24 (@block_merge live 11 0 877 36 (@block_merge live 11 0 841 36 (@block_merge live 11 0 805 36 (@block_merge live 11 0 769 36 (@block_merge live 11 0 733 36 (@block_merge live 11 0 697 36 (@block_merge live 11 0 661 36 (@block_merge live 11 0 625 36 (@block_merge live 11 0 589 36 (@block_merge live 11 0 553 36 (@block_merge live 11 0 517 36 (@block_merge live 11 0 481 36 (@block_merge live 11 0 445 36 (@block_merge live 11 0 409 36 (@block_merge live 11 0 373 36 (@block_merge live 11 0 337 36 (@block_merge live 11 0 301 36 (@block_merge live 11 0 265 36 (@block_merge live 11 0 229 36 (@block_merge live 11 0 193 36 (@block_merge live 11 0 157 36 (@block_merge live 11 0 121 36 (@block_merge live 11 0 110 11 (@block_merge live 11 0 74 36 (@block_merge live 11 0 38 36 (@block_merge live 11 0 2 36 slive11_0 slive11_2) slive11_38) slive11_74) slive11_110) slive11_121) slive11_157) slive11_193) slive11_229) slive11_265) slive11_301) slive11_337) slive11_373) slive11_409) slive11_445) slive11_481) slive11_517) slive11_553) slive11_589) slive11_625) slive11_661) slive11_697) slive11_733) slive11_769) slive11_805) slive11_841) slive11_877) slive11_913) slive11_937) slive11_973) slive11_1009) slive11_1045) slive11_1081) slive11_1117) slive11_1153) slive11_1189) slive11_1225) slive11_1261) slive11_1297) slive11_1333) slive11_1369) slive11_1405) slive11_1441) slive11_1477) slive11_1513) slive11_1549) slive11_1585) slive11_1621)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive12_0 : block live 12 0 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive12_36 : block live 12 36 11=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive12_47 : block live 12 47 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive12_83 : block live 12 83 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive12_119 : block live 12 119 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive12_155 : block live 12 155 14=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive12_169 : block live 12 169 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive12_205 : block live 12 205 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive12_241 : block live 12 241 5=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alllive12 : block live 12 0 246=true := (@block_merge live 12 0 241 5 (@block_merge live 12 0 205 36 (@block_merge live 12 0 169 36 (@block_merge live 12 0 155 14 (@block_merge live 12 0 119 36 (@block_merge live 12 0 83 36 (@block_merge live 12 0 47 36 (@block_merge live 12 0 36 11 slive12_0 slive12_36) slive12_47) slive12_83) slive12_119) slive12_155) slive12_169) slive12_205) slive12_241)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive13_0 : block live 13 0 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive13_7 : block live 13 7 10=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alllive13 : block live 13 0 17=true := (@block_merge live 13 0 7 10 slive13_0 slive13_7)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem slive14_0 : block live 14 0 1=true := by
  apply cellsBlock (ar:=10) (rows:=1) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alllive14 : block live 14 0 1=true := slive14_0
theorem tableslive : checkedTables live 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block live 0 0 0 = true)
  · exact (rfl : block live 1 0 0 = true)
  · exact (rfl : block live 2 0 0 = true)
  · exact (rfl : block live 3 0 0 = true)
  · exact (rfl : block live 4 0 0 = true)
  · exact (rfl : block live 5 0 0 = true)
  · exact (rfl : block live 6 0 0 = true)
  · exact (rfl : block live 7 0 0 = true)
  · exact alllive8
  · exact alllive9
  · exact alllive10
  · exact alllive11
  · exact alllive12
  · exact alllive13
  · exact alllive14

theorem completedRoots (deadCase : Impossible graph 14 inputs.toFinset)
    (liveCase : Impossible graph 14 (inputs++[seed]).toFinset) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y 6)) →
      PEqualNP.MetaComplexity.circuitFun 9 C = edge → 16 ≤ C.size := by
  intro C legal first h
  by_contra! small
  obtain ⟨k,t,hk,hdead | hlive⟩ := initial_live C legal first h (by omega)
  · exact deadCase k t hk hdead
  · exact liveCase k t hk hlive

theorem dead_start {prior : Nat → Nat}
    (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid dead prior=true) (checks : checkedTables dead 14) :
    Impossible graph 14 inputs.toFinset := by
  have noRun := root_index (g:=dead) low geometry checks (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf dead=graph := by decide +kernel
  exact tgt ▸ noRun

theorem live_start {prior : Nat → Nat}
    (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid live prior=true) (checks : checkedTables live 14) :
    Impossible graph 14 (inputs++[seed]).toFinset := by
  have noRun := root_index (g:=live) low geometry checks (k:=14) (by decide)
    (i:=0) (ws:=inputs++[seed]) (by decide +kernel)
  have tgt : targetOf live=graph := by decide +kernel
  exact tgt ▸ noRun
end PEqualNP.Outside.L_meta_4445_aux.Parent

namespace PEqualNP.Outside.L_meta_4445_aux.Parent
theorem parentBound : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size :=
  PEqualNP.Outside.L_meta_4445_aux.Parent.completedRoots (PEqualNP.Outside.L_meta_4445_aux.Parent.dead_start (PEqualNP.Outside.L_meta_4445_aux.Parent.before_sound PEqualNP.Outside.L_meta_4445_aux.Parent.known383 PEqualNP.Outside.L_meta_4445_aux.Parent.valid383) PEqualNP.Outside.L_meta_4445_aux.Parent.geomdead PEqualNP.Outside.L_meta_4445_aux.Parent.tablesdead) (PEqualNP.Outside.L_meta_4445_aux.Parent.live_start (PEqualNP.Outside.L_meta_4445_aux.Parent.before_sound PEqualNP.Outside.L_meta_4445_aux.Parent.known383 PEqualNP.Outside.L_meta_4445_aux.Parent.valid383) PEqualNP.Outside.L_meta_4445_aux.Parent.geomlive PEqualNP.Outside.L_meta_4445_aux.Parent.tableslive)

end PEqualNP.Outside.L_meta_4445_aux.Parent

namespace PEqualNP.Outside.L_meta_4445_aux.Header
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def prefixGate : Gate := ⟨GateOp.or,[4,6]⟩
def ports : ℕ → ℕ × ℕ
  | 3 => (0,1) | 5 => (0,2) | 9 => (0,3) | 17 => (0,4)
  | 33 => (0,5) | 65 => (0,6) | 129 => (0,7) | 257 => (0,8)
  | 20 => (2,4) | 36 => (2,5) | 132 => (2,7) | 144 => (4,7)
  | 81 => (9,0) | 84 => (9,2) | 208 => (9,7)
  | _ => (0,0)
def secondGate (m : ℕ) : Gate := ⟨GateOp.or,[(ports m).1,(ports m).2]⟩
def masks : List ℕ := [3,5,9,17,33,65,129,257,20,36,132,144,81,84,208]
def masked (m : ℕ) (x : Fin 9 → Bool) := decide (∃ i : Fin 9, m.testBit i.val=true ∧ x i=true)
def target (x : Fin 9 → Bool) :=
  [1,12,23,34,40,5,16,27,38,57,68,85].any (fun e : ℕ => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
def expanded (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
  (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
def wiresOne (x : Fin 9 → Bool) := List.ofFn x ++ [x 4 || x 6]
def extend (m : ℕ) (x : Fin 9 → Bool) : Fin 11 → Bool := Fin.snoc (Fin.snoc x (x 4 || x 6)) (masked m x)
def readGate (ws : List Bool) (g : Gate) := g.op.eval (g.inputs.map (fun k => ws.getD k false))
def next (ws : List Bool) (g : Gate) := ws ++ [readGate ws g]
def run (gs : List Gate) (ws : List Bool) := gs.foldl next ws

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem masksAgree : ∀ m ∈ masks, ∀ x : Fin 9 → Bool, readGate (wiresOne x) (secondGate m)=masked m x := by
  decide +kernel

theorem targetAgree : ∀ x : Fin 9 → Bool, target x=expanded x := by decide +kernel

theorem keep (gs : List Gate) (ws : List Bool) (i : ℕ) (hi : i<ws.length) :
    (run gs ws).getD i false = ws.getD i false := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (next ws g)).getD i false=_
    rw [ih _ (by simp [next]; omega)]
    exact List.getD_append _ _ _ _ hi

theorem header (m : ℕ) (hm : m ∈ masks) (x : Fin 9 → Bool) :
    next (next (List.ofFn x) prefixGate) (secondGate m) = List.ofFn (extend m x) := by
  have first : next (List.ofFn x) prefixGate = wiresOne x := by
    simp [next,readGate,prefixGate,wiresOne,GateOp.eval]
  rw [first]
  change wiresOne x ++ [readGate (wiresOne x) (secondGate m)] = _
  rw [masksAgree m hm x]
  simp only [extend,List.ofFn_succ_last,Fin.snoc_castSucc,Fin.snoc_last,wiresOne]

theorem lower
    (bound : ∀ C : Circuit, FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y 6)) →
      circuitFun 9 C=expanded → 16≤C.size)
    (m : ℕ) (hm : m ∈ masks) (D : Circuit) (ok : FanInTwo D)
    (spec : ∀ x, circuitFun 11 D (extend m x)=target x) : 14≤D.size := by
  let C : Circuit := ⟨prefixGate::secondGate m::D.gates,D.output⟩
  have legal : FanInTwo C := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl|hg
    · simp [prefixGate]
    rcases List.mem_cons.mp hg with rfl|hg
    · simp [secondGate]
    · exact ok g hg
  have first (x : Fin 9 → Bool) : (C.wires (List.ofFn x)).getD 9 false=(x 4 || x 6) := by
    change (run D.gates (next (next (List.ofFn x) prefixGate) (secondGate m))).getD 9 false=_
    rw [header m hm,keep _ _ _ (by simp)]
    rw [List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
    change extend m x 9 = _
    simp [extend,Fin.snoc]
  have truth : circuitFun 9 C=expanded := by
    funext x
    change (run D.gates (next (next (List.ofFn x) prefixGate) (secondGate m))).getD D.output false=_
    rw [header m hm]
    exact (spec x).trans (targetAgree x)
  have size : C.size=D.size+2 := by simp [C,Circuit.size]
  have count := bound C legal first truth
  omega

end PEqualNP.Outside.L_meta_4445_aux.Header

theorem PEqualNP.Outside.L_meta_4445 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ x2 ∈ [(81 : ℕ), (84 : ℕ), (208 : ℕ)], ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → (∀ (x6 : Fin (9 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x4 (Fin.snoc (Fin.snoc x6 (x6 (4 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)))) (Decidable.decide (∃ (x7 : Fin (9 : ℕ)), x2.testBit ↑x7 = Bool.true ∧ x6 x7 = Bool.true))) = x1 x6) → (14 : ℕ) ≤ x4.size := by
  dsimp only
  intro m hm D ok spec
  have subset : ∀ k ∈ [81, 84, 208], k ∈ PEqualNP.Outside.L_meta_4445_aux.Header.masks := by decide +kernel
  exact PEqualNP.Outside.L_meta_4445_aux.Header.lower PEqualNP.Outside.L_meta_4445_aux.Parent.parentBound m (subset m hm) D ok spec
