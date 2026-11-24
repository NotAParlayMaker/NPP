import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_1673
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
def or_seed : Sig := bin true (inputs.getD 0 zero) (inputs.getD 1 zero)
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
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
abbrev chartGoal := graphGoal
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

-- A column with the extra marker uses the adjacent OR as a free input to the restricted graph.
def seededInputs (m : Nat) : List Sig := vars m ++ [or_seed]
def SeedBound (m bound : Nat) : Prop := Lower (seededInputs m) (graphGoal m) bound

def seedColumn (c : ColumnInfo) : Bool := c.2.1 == 512
def columnRoots (m : Nat) (c : ColumnInfo) : List Sig :=
  if seedColumn c then seededInputs m else vars m
def columnDomain (c : ColumnInfo) : Sig :=
  subcube c.1 (if seedColumn c then 0 else c.2.1)
def columnCheck (m : Nat) (c : ColumnInfo) (plain seeded : Nat → Nat) : Bool :=
  if seedColumn c then
    let (z,_,q,_,bound) := c
    let rows := fixRows z 0
    properB (graphGoal q) &&
      checkMap rows (seededInputs m) (graphGoal m) (seededInputs q) (graphGoal q) &&
      movedWord rows (subcube z 0) == one &&
      decide (bound ≤ seeded q)
  else colCheck m c plain

theorem column_sound {m : Nat} (c : ColumnInfo) (plain seeded : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (plain q))
    (seedValid : ∀ q, SeedBound q (seeded q))
    (checked : columnCheck m c plain seeded = true) :
    Slice (columnRoots m c) (chartGoal m) (columnDomain c) c.2.2.2.2 := by
  cases flag : seedColumn c
  · simpa only [columnRoots,columnDomain,flag,ite_false,Bool.false_eq_true] using
      col_sound c plain valid (by simpa only [columnCheck,flag,Bool.false_eq_true,ite_false] using checked)
  · obtain ⟨z,o,q,s,bound⟩ := c
    simp only [columnCheck,flag,ite_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at checked
    simp only [columnRoots,columnDomain,flag,ite_true]
    apply slice_correct checked.1.1.2 checked.1.2 (proper_of _ checked.1.1.1)
    intro k bank reach available
    exact checked.2.trans (seedValid q k bank reach available)

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


abbrev BoundPool := Sig × Nat × Nat × List Sig
abbrev BoundPool.domain (p : BoundPool) := p.1
abbrev BoundPool.bound (p : BoundPool) := p.2.1
abbrev BoundPool.paid (p : BoundPool) := p.2.2.1
abbrev BoundPool.wires (p : BoundPool) := p.2.2.2

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
def hashSet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0
def packSignals : List Sig → Nat
  | [] => 0
  | a :: xs => a.toNat + (packSignals xs <<< 512)
def keySet (xs : List Sig) := hashSet xs + (packSignals xs <<< 70)

abbrev PreparedPool := BoundPool × List Sig
def preparePool (p : BoundPool) : PreparedPool := (p,p.wires.map (masked p.domain))
def ValidPrepared (raw : List Sig) (T : Sig) (p : PreparedPool) : Prop :=
  ValidPool raw T p.1 ∧ p.2 = p.1.wires.map (masked p.1.domain)
def preparedHas (p : PreparedPool) (a : Sig) : Bool :=
  let m := masked p.1.domain a
  m == zero || m == p.1.domain || p.2.any (fun v => v==m)
theorem prepared_has {p : PreparedPool}
    (eq : p.2 = p.1.wires.map (masked p.1.domain)) (a : Sig) :
    preparedHas p a = availableB p.1.domain p.1.wires a := by
  simp only [preparedHas,availableB,eq]
def preparedCut (p : PreparedPool) (k : Nat) (rest : List Sig) (op : Choice) : Bool :=
  let z := choiceVal op
  let cost := k+p.1.paid
  let budget := p.1.bound + (z::rest).countP (isMaskedConstant p.1.domain)
  (cost < budget) && rest.all (preparedHas p) &&
    (preparedHas p z ||
      ((cost+1 < budget) && preparedHas p op.2.1 && (op.1==2 || preparedHas p op.2.2)))

theorem prepared_cut {p : PreparedPool} {k rest op} (eq : p.2 = p.1.wires.map (masked p.1.domain))
    (h : preparedCut p k rest op = true) : scalarPoolCut p.1 k rest op = true := by
  have fn : preparedHas p = availableB p.1.domain p.1.wires := funext (prepared_has eq)
  simp only [preparedCut,fn,Bool.and_eq_true,decide_eq_true_eq,Bool.or_eq_true] at h
  by_cases present : availableB p.1.domain p.1.wires (choiceVal op) = true
  · simpa only [scalarPoolCut,present,Bool.not_true,Bool.toNat,Bool.cond_false,Nat.add_zero,
      Bool.not_false,Bool.true_or,Bool.and_eq_true,decide_eq_true_eq,and_true] using h.1
  · have absent := Bool.eq_false_iff.mpr present
    have pay := h.2.resolve_left present
    simpa only [scalarPoolCut,absent,Bool.not_false,Bool.toNat,Bool.cond_true,
      Bool.not_true,Bool.false_or,Bool.and_eq_true,decide_eq_true_eq,choiceOK,Bool.or_eq_true] using
      (show _ from ⟨⟨pay.1.1,h.1.2⟩,pay.1.2,pay.2⟩)

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

abbrev CachedPool := PreparedPool × Nat × Nat

def miss (p : PreparedPool) (w : Decor) := !(preparedHas p w.1)
def fixed (p : PreparedPool) (w : Decor) := isMaskedConstant p.1.domain w.1

def cachePool (ws : List Decor) (p : BoundPool) : CachedPool :=
  let pp := preparePool p
  (pp,ws.countP (miss pp),ws.countP (fixed pp))

def ValidCached (raw : List Sig) (T : Sig) (ws : List Decor) (p : CachedPool) : Prop :=
  ValidPrepared raw T p.1 ∧ p.2 = (ws.countP (miss p.1),ws.countP (fixed p.1))

def removal (f : Decor → Bool) (a : Decor) (keep : Bool) : Nat :=
  if keep then 0 else (f a).toNat

theorem countDel (f : Decor → Bool) {ws : List Decor} {a : Decor} (ha : a ∈ ws) (keep : Bool) :
    (delOne ws a keep).countP f = ws.countP f - removal f a keep := by
  cases keep
  · cases h : f a <;> simp [delOne,List.countP_erase,ha,h,removal,Bool.toNat]
  · simp [delOne,removal]

theorem countKeep (f : Decor → Bool) {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    {un : Bool} (ne : un=false → a≠b) (ka kb : Bool) :
    (opKeep un ka kb a b ws).countP f =
      ws.countP f - removal f a ka - removal f b (un || kb) := by
  cases un
  · have hb' : b ∈ delOne ws a ka := by
      cases ka
      · exact (List.mem_erase_of_ne (ne rfl).symm).mpr hb
      · exact hb
    simp only [opKeep,Bool.false_eq_true,ite_false,delTwo,countDel f hb',countDel f ha,Bool.false_or]
  · simp only [opKeep,ite_true,countDel f ha,Bool.true_or,removal,ite_true,Nat.sub_zero]

def cachedCut (p : CachedPool) (k op : Nat) (a b : Decor) (ka kb : Bool) : Bool :=
  let pp := p.1
  let keepB := (op==2) || kb
  let missing := p.2.1 - removal (miss pp) a ka - removal (miss pp) b keepB
  let constants := p.2.2 - removal (fixed pp) a ka - removal (fixed pp) b keepB
  let z := choiceVal (movedChoice op a b)
  let cost := k+pp.1.paid
  let budget := pp.1.bound + constants + (isMaskedConstant pp.1.domain z).toNat
  (cost < budget) && missing==0 &&
    (preparedHas pp z || ((cost+1 < budget) && preparedHas pp a.1 && (op==2 || preparedHas pp b.1)))

theorem cached_cut {raw T ws p k op a b ka kb}
    (valid : ValidCached raw T ws p) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (h : cachedCut p k op a b ka kb=true) :
    preparedCut p.1 k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b) = true := by
  let rest := opKeep (op==2) ka kb a b ws
  have hc := countKeep (fixed p.1) ha hb ne ka kb
  have hm := countKeep (miss p.1) ha hb ne ka kb
  have hc' := congrArg Prod.snd valid.2
  have hm' := congrArg Prod.fst valid.2
  simp only [cachedCut,hc',hm',←hc,←hm,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  have none : rest.countP (miss p.1) = 0 := by simpa [rest] using h.1.2
  have all : (rest.map Prod.fst).all (preparedHas p.1) = true := by
    apply List.all_eq_true.mpr
    intro x hit
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hit
    have step := List.countP_eq_zero.mp none w hw
    cases he : preparedHas p.1 w.1 <;> simp [miss,he] at step ⊢
  simp only [preparedCut,rest,all,Bool.and_eq_true,decide_eq_true_eq,List.countP_cons,
    List.countP_map,Function.comp_def,movedChoice]
  have fn : fixed p.1 = (fun w : Decor => isMaskedConstant p.1.1.domain w.1) := rfl
  simp only [fn] at h
  simpa [rest,movedChoice,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,
    Bool.toNat] using And.intro h.1.1 h.2

def closeChild (pools : List CachedPool) (links : List Sig → List (List Sig))
    (k op : Nat) (a b : Decor) (ka kb : Bool) (ws : List Decor) :=
  let rest := (opKeep (op==2) ka kb a b ws).map Prod.fst
  let child := choiceVal (movedChoice op a b)::rest
  pools.any (fun p => cachedCut p k op a b ka kb) || (links child).any (sameWords child)

theorem closeChild_sound {raw T ws pools links k op a b ka kb}
    (pv : ∀ p ∈ pools, ValidCached raw T ws p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T k (List.toFinset xs))
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : (op==2)=false → a≠b)
    (nd : (choiceVal (movedChoice op a b) :: (opKeep (op==2) ka kb a b ws).map Prod.fst).Nodup)
    (h : closeChild pools links k op a b ka kb ws = true) :
    Impossible T k (choiceVal (movedChoice op a b) :: (opKeep (op==2) ka kb a b ws).map Prod.fst).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨p,hp,ok⟩ | ⟨xs,hx,ok⟩
  · have vp := pv _ hp
    exact scalarPoolCut_sound vp.1.1 nd (prepared_cut vp.1.2 (cached_cut vp ha hb ne ok))
  · rw [sameWords_sound ok]
    exact lv _ _ hx

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List CachedPool × (List Sig → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      closeChild pools links (cap-1) op a b ka kb ws

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidCached raw T ws p)
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
  exact closeChild_sound pv lv ha hb ne nd' test k t hk h


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
    (pv : ∀ p ∈ pools, ValidCached raw T ws p)
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


abbrev IndexTree (α : Type) := Nat × (Nat → α)
def IndexTree.read {α : Type} (tab : IndexTree α) (i : Nat) :=
  if i < tab.1 then some (tab.2 i) else none
def IndexTree.values {α : Type} (tab : IndexTree α) :=
  (List.range tab.1).map tab.2
theorem IndexTree.read_mem {α : Type} (tab : IndexTree α) {i x} (eq : tab.read i=some x) :
    x ∈ tab.values := by
  unfold IndexTree.read at eq
  split at eq
  · rename_i hi
    exact List.mem_map.mpr ⟨i,List.mem_range.mpr hi,Option.some.inj eq⟩
  · contradiction
def columnTable (n entries : Nat) : IndexTree ColumnInfo :=
  (n,fun i =>
    let w := entries >>> (42*i)
    (w &&& 511,(w >>> 9) &&& 1023,(w >>> 19) &&& 511,(w >>> 28) &&& 511,(w >>> 37) &&& 31))

abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × IndexTree ColumnInfo ×
  Array (List Nat) × (Nat → Packing) × (Nat → List Sig → Option (Nat × Nat))
abbrev Forest.mask (g : Forest) := g.1
abbrev Forest.cap (g : Forest) := g.2.1
abbrev Forest.samples (g : Forest) := g.2.2.1
abbrev Forest.cols (g : Forest) := g.2.2.2.1
abbrev Forest.autos (g : Forest) := g.2.2.2.2.1
abbrev Forest.levels (g : Forest) := g.2.2.2.2.2.1
abbrev Forest.index (g : Forest) := g.2.2.2.2.2.2

def wireMask (g : Forest) : Nat := if 512 ≤ g.mask then 511 else g.mask
def wiresOf (g : Forest) :=
  rawDecor (wireMask g) (fun j => (g.samples j).1) (fun j => (g.samples j).2)
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a :=
  raw_faithful (wireMask g) _ _
def targetOf (g : Forest) := chartGoal g.mask
abbrev chartSamples := liftGoal
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
-- A token tree stores a symbol at an even entry and a pair of child indices at an odd entry.
abbrev TokenBook := Nat × Nat
def tokenAt (r : TokenBook) (i : Nat) : Nat :=
  (r.2 >>> (r.1*i)) &&& ((1 <<< r.1)-1)
def decodeTokenAt (r : TokenBook) : Nat → Nat → Nat → Nat × Nat
  | 0, _, w => (0,w)
  | fuel+1, i, w =>
    let code := tokenAt r i
    if code &&& 1 == 0 then (code >>> 1,w)
    else decodeTokenAt r fuel ((code >>> 1)+(w &&& 1)) (w >>> 1)
def decodeToken (r : TokenBook) (w : Nat) : Nat × Nat :=
  decodeTokenAt r 24 0 w
def tokenSequence (r : TokenBook) : Nat → Nat → List Nat × Nat
  | 0, w => ([],w)
  | n+1, w =>
    let (a,w') := decodeToken r w
    let (rest,w'') := tokenSequence r n w'
    (a::rest,w'')
def compressedBooks (p : Nat → Nat) (i : Nat) : TokenBook :=
  (p (5+i),p (9+i))
def skipTokens (r : TokenBook) : Nat → Nat → Nat
  | 0,w => w
  | n+1,w => skipTokens r n (decodeToken r w).2
def decodeOps (r : TokenBook) : Nat → Nat → Nat × Nat
  | 0,w => (0,w)
  | n+1,w =>
    let (op,more) := decodeToken r w
    let (tail,last) := decodeOps r n more
    (op+(tail <<< 10),last)
def compressedHeader (p : Nat → Nat) (d w : Nat) : Nat × Nat × Nat × Nat :=
  let (ops,r) := decodeOps (compressedBooks p 0) (d-1) w
  let (live,s) := decodeToken (compressedBooks p 1) r
  let (num,t) := decodeToken (compressedBooks p 2) s
  (272+(ops <<< 10),live,num,t)
def skipRecord (p : Nat → Nat) (d w : Nat) : Nat :=
  let r := skipTokens (compressedBooks p 0) (d-1) w
  let s := (decodeToken (compressedBooks p 1) r).2
  let (num,t) := decodeToken (compressedBooks p 2) s
  skipTokens (compressedBooks p 3) num t
def skipRecords (p : Nat → Nat) (d : Nat) : Nat → Nat → Nat
  | 0,w => w
  | n+1,w => skipRecords p d n (skipRecord p d w)
def compressedAt (g : Forest) (k i : Nat) : Nat × Nat × Nat × Nat :=
  let (_,d,_,_,_,width,_,p) := g.levels k
  let stride := p 13
  let start := packedAt (fun j => p (100+j)) (i/stride*width) width
  let w := packedAt (fun j => p (1000+j)) start (p 0)
  compressedHeader p d (skipRecords p d (i % stride) w)
def forestRecord (g : Forest) (k i : Nat) : Nat × Nat :=
  if 512 ≤ g.mask then
    let r := compressedAt g k i
    (r.1,r.2.1)
  else
    let (_,depth,_,_,_,_,_,data) := g.levels k
    let len := 10*storedDepth g depth
    let width := len+(wiresOf g).length+depth
    let recp := packedAt data (i*width) width
    (recp &&& ((1 <<< len)-1),recp >>> len)
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,_) := g.levels k
  let (ops,bits) := forestRecord g k i
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive bits bank)
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
    materialize (columnRoots g.mask ci) (chosenSteps bank ops paid d) (columnDomain ci) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (columnRoots g.mask ci) (targetOf g) (columnDomain ci) ci.2.2.2.2)
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

def forestRulePairs (g : Forest) (k i : Nat) : List (Nat × Nat) :=
  let (num,depth,cw,_,_,offw,lw,data) := g.levels k
  if 512 ≤ g.mask then
    let r := compressedAt g k i
    let codes := (tokenSequence (compressedBooks data 3) r.2.2.1 r.2.2.2).1
    codes.map (fun q => (q >>> depth,q &&& ((1 <<< depth)-1)))
  else
    let start := num*(10*storedDepth g depth+(wiresOf g).length+depth)
    let pos := start+num*offw+packedAt data (start+i*offw) offw
    let nr := packedAt data pos 5
    let st := pos+5+lw
    getPairs data cw depth nr st

def forestIndex (g : Forest) (k : Nat) (ws : List Sig) : Option (Nat × Nat) :=
  g.index k ws

def nodeVerified (g : Forest) (k i : Nat) :=
  let (_,depth,_,_,_,_,_,_) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let rules := ((forestRulePairs g k i).filterMap (fun (a,b) => buildRule g ops depth bank a b)).map (cachePool ws)
  let ls := fun tag => ((forestIndex g k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (columnRoots g.mask ci) (targetOf g) (columnDomain ci) ci.2.2.2.2)
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
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hq
    exact ⟨⟨buildRule_sound g cols h,rfl⟩,rfl⟩
  · intro tag xs hx
    have e : ((forestIndex g k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
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
def graphValid (g : Forest) (prior : Nat → Nat) (seeded : Nat → Nat := fun _ => 0) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => columnCheck g.mask c prior seeded) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all_seed (g : Forest) (top : Nat) (prior seeded : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (lowerSeed : ∀ q, SeedBound q (seeded q))
    (geometry : graphValid g prior seeded = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => column_sound _ prior seeded lower lowerSeed (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => column_sound _ prior seeded lower lowerSeed (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset :=
  forest_all_seed g top prior (fun _ => 0) lower (fun _ _ _ _ _ => Nat.zero_le _) geometry rows

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem root_index_seed {g top prior seeded k i ws} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (lowSeed : ∀ q, SeedBound q (seeded q))
    (geom : graphValid g prior seeded = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all_seed g top prior seeded low lowSeed geom blocks _ le i idx.1

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
theorem live_bound_of_available {raw T L k u S} (properT : proper T)
    (run : Live T k u S) (sub : ∀ a ∈ S, a ∈ raw)
    (bound : Lower raw T L) : L ≤ k := by
  have hrun := list_run run S.toList S.nodup_toList (by simp)
  have supplyOld : supply (raw.map observe) (S.toList.map observe) := by
    intro w hw
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
    exact Or.inl (List.mem_map_of_mem (sub a (Finset.mem_toList.mp ha)))
  obtain ⟨j,bank,reach,hit,cost⟩ :=
    contraction (observe_proper properT) hrun _ Reach.start supplyOld
  exact (bound j bank reach hit).trans (by omega)

theorem lower_seeded {m cap hints : Nat}
    (properTarget : properB (graphGoal m) = true)
    (ess : checkEssential (graphGoal m) (seededInputs m) (graphPairs m hints) = true)
    (plain : Lower (vars m) (graphGoal m) (cap+1))
    (useSeed : Impossible (graphGoal m) cap (seededInputs m).toFinset) :
    SeedBound m (cap+1) := by
  intro n bank reach hit
  by_contra! few
  have properT := proper_of _ properTarget
  obtain ⟨k,t,S,small,run,sub⟩ := reach_live properT reach hit
  have all : (vars m).toFinset ⊆ S := by
    intro a ha
    have eq : (graphPairs m hints).map Prod.fst = vars m := by simp [graphPairs,vars,List.map_map]
    have required := essential_ok ess a (eq.symm ▸ ha)
    obtain ⟨r,s,hd,iso⟩ := required
    exact raw_required run _ _ sub r s hd iso
  by_cases seed : or_seed ∈ S
  · have eq : S = (seededInputs m).toFinset := by
      ext a
      refine ⟨fun ha => List.mem_toFinset.mpr (sub a ha),?_⟩
      intro ha
      have hh := List.mem_toFinset.mp ha
      rcases List.mem_append.mp hh with hm | hs
      · exact all (List.mem_toFinset.mpr hm)
      · exact (List.mem_singleton.mp hs).symm ▸ seed
    exact useSeed k t (by omega) (eq ▸ run)
  · have sub' : ∀ a ∈ S, a ∈ vars m := by
      intro a ha
      rcases List.mem_append.mp (sub a ha) with hh | hs
      · exact hh
      · exact (seed ((List.mem_singleton.mp hs) ▸ ha)).elim
    have lo := live_bound_of_available properT run sub' plain
    omega

def KnownSeed (entries : List (Nat × Nat)) : Prop :=
  ∀ e ∈ entries, SeedBound e.1 e.2

theorem knownSeedNil : KnownSeed [] := by simp [KnownSeed]

theorem beforeSeed_sound (entries : List (Nat × Nat)) (valid : KnownSeed entries) (q : Nat) :
    SeedBound q (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have hm := List.mem_of_find?_eq_some h
    have hh : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun (a : Nat × Nat) => a.1==q) h
    have eq : e.1=q := beq_iff_eq.mp hh
    simpa only [Option.map_some,Option.getD_some,eq] using valid e hm

def relabelSeedOK (old rep : Nat) (swaps : List Nat) : Bool :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (seededInputs old) (graphGoal old) (seededInputs rep) (graphGoal rep)

theorem relabelSeed {old rep L swaps} (checked : relabelSeedOK old rep swaps = true)
    (bound : SeedBound rep L) : SeedBound old L := by
  simp only [relabelSeedOK,Bool.and_eq_true] at checked
  exact lower_map checked.2 (proper_of _ checked.1.1) (proper_of _ checked.1.2) bound

theorem extendKnownSeed {old L m relabels} (previous : KnownSeed old)
    (bound : SeedBound m L)
    (checked : relabels.all (fun v => relabelSeedOK v.1 m v.2) = true) :
    KnownSeed (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | hm
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabelSeed (List.all_eq_true.mp checked _ hv) bound
  · exact previous e hm

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

def postMove (c : NodeContext) (i j op : Nat) (ka kb : Bool) : Bool :=
  let a := contextWire c i
  let b := contextWire c j
  let z := movedDecor op a b
  if !properB z.1 || c.2.2.1.any (fun v => v.1==z.1) then true
  else closeChild c.2.2.2.2.1 c.2.2.2.2.2 (c.1-1) op a b ka kb c.2.2.1

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
    onMarks (fun c => postMove c i j op ka kb) mask xs

theorem batchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  let d := len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else postMove xs[q] i j op ka kb := by
    simp only [checkAt,evalMove,budget,arity,len,d,combField,postMove] <;> rfl
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
    · have passed := marked_ok _ _ _ q hq (by
        rw [mark_at _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      rw [eval,if_neg small]
      simpa only [hit,bne_self_eq_false,Bool.false_eq_true,ite_false] using passed
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
  let (_,depth,_,_,_,_,_,_) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let rules := ((forestRulePairs g k i).filterMap (fun (a,b) => buildRule g ops depth bank a b)).map (cachePool ws)
  let ls := fun tag => ((forestIndex g k tag).bind (linkedSet g (k-1))).toList
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
def g15columns : IndexTree ColumnInfo := columnTable 0 0x0
def g15autos : Array (List Nat) := #[[],[33,48]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,fun k ws => g15index k (hashSet ws)⟩
def key31l6 (i : Nat) : Nat := 0x820007028af371d000003180048302e380000000003819155875690d58000003d
def g31d5 (i : Nat) : Nat := 0x84001e90fd02fd01fa00
def g31l5 : Packing := (3,1,3,0,4,4,0,g31d5)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,2,4,0,0,g31d6)
def g31samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : IndexTree ColumnInfo := columnTable 5 0x800078001020002e000208000d8000420003a000088000f00001
def g31autos : Array (List Nat) := #[[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,fun k ws => g31index k (hashSet ws)⟩
def g47samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : IndexTree ColumnInfo := columnTable 1 0x8001380008
def g47autos : Array (List Nat) := #[[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,fun k ws => g47index k (hashSet ws)⟩
def g55samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := columnTable 1 0x8001380010
def g55autos : Array (List Nat) := #[[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,fun k ws => g55index k (hashSet ws)⟩
def g63samples : Array (Bits × Bits) := #[(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := columnTable 1 0xe000f80020
def g63autos : Array (List Nat) := #[[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,fun k ws => g63index k (hashSet ws)⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := #[(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo := columnTable 3 0xa00178004020009c100048003181004
def g111autos : Array (List Nat) := #[[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,fun k ws => g111index k (hashSet ws)⟩
def g119samples : Array (Bits × Bits) := #[(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := columnTable 1 0xa003980004
def g119autos : Array (List Nat) := #[[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat → Packing
  | _ => emptyPacking
def g119index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest := ⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,fun k ws => g119index k (hashSet ws)⟩
def key189l7 (i : Nat) : Nat := 0xa81337040d4b600002948880000590cc33d41450272020001b1
def g189d6 (i : Nat) : Nat := 0x82000f487f40bfa03fa00
def g189l6 : Packing := (3,1,3,0,4,4,0,g189d6)
def g189d7 (i : Nat) : Nat := 0x1f5859bf
def g189l7 : Packing := (1,0,3,2,4,0,0,g189d7)
def g189samples : Array (Bits × Bits) := #[(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : IndexTree ColumnInfo := columnTable 8 0x20003a002808001c8008420013800084800528001820015800044a00568001020016200030a005e00001
def g189autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,fun k ws => g189index k (hashSet ws)⟩
def g127samples : Array (Bits × Bits) := #[(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : IndexTree ColumnInfo := columnTable 1 0x10002f80020
def g127autos : Array (List Nat) := #[[],[101,66,16]]
def g127levels : Nat → Packing
  | _ => emptyPacking
def g127index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest := ⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,fun k ws => g127index k (hashSet ws)⟩
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
def g191columns : IndexTree ColumnInfo := columnTable 38 0x200036400908000d800a420003c102048000f000a128103640080a010f0408038003e00280a001b8008828803640010a001e8008240007e00200800438003828011e000c0a004b800282001380008ca800f0400140013e00080800518101420014c08024800530001928054c08020a04518101038014e00060800560001328214c08004c09530200040015e00040800588000e28414604010a00598000c28016a00028c14518100040016e00020a005c8000638017600010a005e0000340017a00008e005f00001
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
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,fun k ws => g191index k (hashSet ws)⟩
def g251samples : Array (Bits × Bits) := #[(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : IndexTree ColumnInfo := columnTable 1 0xe007980008
def g251autos : Array (List Nat) := #[[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,fun k ws => g251index k (hashSet ws)⟩
def g255samples : Array (Bits × Bits) := #[(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := columnTable 1 0x16005f80040
def g255autos : Array (List Nat) := #[[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat → Packing
  | _ => emptyPacking
def g255index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,fun k ws => g255index k (hashSet ws)⟩
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
def g383columns : IndexTree ColumnInfo := columnTable 59 0xe000f8016028007a20408a001e8014240007e00500a00278013029002e800a0a002f001214000be00480a0431811102800ce00460a1031811042800e600430c600ba00083050c604400c003b8010839a02e800012003f801002c003a20088e009c8004628127001104a009e0004340027a00108e009f0004158027e00100a00a38003828228c08084a02a60023038029c000c4a00a98002c28429800888a00ae00023304a9800881000af000215802be00080b0031810143802c600070a00b3000194002ce00060a20a6002122802d80004ce00b6800124002dc00045600b7800102802e200038800b10000d4002e600030f1431810004802ee00020a409c004052802f00001ce00bd000055802f600010c449c0040130c29800808c00be0000339167001001200be8000238ca9800801200bf00001
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
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,fun k ws => g383index k (hashSet ws)⟩
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
  decide +kernel
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
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true := by
  decide +kernel
theorem bl31_5 : block g31 5 0 3 = true := (@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_6_0 : block g31 6 0 1=true := by
  decide +kernel
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
  decide +kernel
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
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true := by
  decide +kernel
theorem bl189_6 : block g189 6 0 3 = true := (@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_7_0 : block g189 7 0 1=true := by
  decide +kernel
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
  decide +kernel
theorem bl191_6 : block g191 6 0 1 = true := s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_0 : block g191 7 0 13=true := by
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true := by
  decide +kernel
theorem bl191_7 : block g191 7 0 28 = true := (@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_0 : block g191 8 0 7=true := by
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true := by
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true := by
  decide +kernel
theorem bl191_8 : block g191 8 0 100 = true := (@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_0 : block g191 9 0 3=true := by
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true := by
  decide +kernel
theorem bl191_9 : block g191 9 0 12 = true := (@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_10_0 : block g191 10 0 1=true := by
  decide +kernel
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
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : block g383 8 23 2=true := by
  decide +kernel
theorem bl383_8 : block g383 8 0 25 = true := (@block_merge g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_0 : block g383 9 0 9=true := by
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true := by
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : block g383 9 84 7=true := by
  decide +kernel
theorem bl383_9 : block g383 9 0 91 = true := (@block_merge g383 9 0 84 7 (@block_merge g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_0 : block g383 10 0 5=true := by
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : block g383 10 5 16=true := by
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true := by
  decide +kernel
theorem bl383_10 : block g383 10 0 41 = true := (@block_merge g383 10 0 21 20 (@block_merge g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_0 : block g383 11 0 1=true := by
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : block g383 11 1 5=true := by
  decide +kernel
theorem bl383_11 : block g383 11 0 6 = true := (@block_merge g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_12_0 : block g383 12 0 1=true := by
  decide +kernel
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

-- The shared finite search checks graph restrictions and uses the wire liveness recurrence.
-- These lemmas interpret the specified first OR gate before that recurrence starts.
theorem or_seed_nonzero : or_seed ≠ zero := by decide +kernel
theorem or_seed_table : ∀ r : Row, bit r or_seed = (sample r 0 || sample r 1) := by decide +kernel
def or_neighbor (i : Fin 9) : Nat := [1,0,1,2,3,0,1,2,3].getD i.val 0
def or_absentRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< or_neighbor i)
def or_presentRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< or_neighbor i))

theorem or_seed_witness : ∀ i : Fin 9,
    (bit (or_absentRow i) graph != bit (or_presentRow i) graph) &&
    ((inputs++[or_seed]).all fun w => w == inputs.getD i.val zero ||
      bit (or_absentRow i) w == bit (or_presentRow i) w) = true := by decide +kernel

theorem or_all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[or_seed]) :
    S=inputs.toFinset ∨ S=(inputs++[or_seed]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := or_seed_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (or_absentRow i) (or_presentRow i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : or_seed ∈ S
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

theorem or_initial_live (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 1))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t, k ≤ 14 ∧ (Live graph k t inputs.toFinset ∨ Live graph k t (inputs++[or_seed]).toFinset) := by
  have headEq : (execute C.gates inputs).getD 9 zero = or_seed := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (or_seed_table r).symm)
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
    exact False.elim (or_seed_nonzero headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g = or_seed := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = or_seed at headEq
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
    rcases or_all_roots run hs with h | h
    · exact Or.inl (h ▸ run)
    · exact Or.inr (h ▸ run)


def groupsAt (xs : List NodeContext) (arity : Nat) : List NodeContext :=
  xs.filter (fun c => c.2.1 == arity)

def chunkPass (g : Forest) (k start n : Nat) : Bool :=
  let xs := contexts g k start n
  xs.all (fun c => prelim (targetOf g) c && decide (c.2.1 < 16)) &&
  (List.range 16).all (fun arity =>
    let ys := groupsAt xs arity
    ys.isEmpty || runBatch k arity ys)

theorem ctxBudget (g : Forest) (k i : Nat) : (contextOf g k i).1 = k := by
  unfold contextOf
  rfl

theorem ctxArity (g : Forest) (k i : Nat) :
    (contextOf g k i).2.1 = (contextOf g k i).2.2.1.length := by
  unfold contextOf
  rfl

theorem chunkPass_block {g k start n} (pass : chunkPass g k start n = true) :
    block g k start n = true := by
  simp only [chunkPass,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at pass
  apply makeBlock
  intro i lo hi
  let c := contextOf g k i
  let xs := contexts g k start n
  have mem : c ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  have header := pass.1 c mem
  have passes := pass.2 c.2.1 (List.mem_range.mpr header.2)
  let ys := groupsAt xs c.2.1
  have inGroup : c ∈ ys := List.mem_filter.mpr ⟨mem,beq_self_eq_true _⟩
  have ne : ys.isEmpty = false := by
    cases e : ys with
    | nil => rw [e] at inGroup; simp at inGroup
    | cons _ _ => rfl
  have runs : runBatch k c.2.1 ys = true := by
    change (ys.isEmpty || runBatch k c.2.1 ys) = true at passes
    simpa only [ne,Bool.false_or] using passes
  obtain ⟨j,hj,eq⟩ := List.getElem_of_mem inGroup
  have done := runBatch_at hj (by rw [eq]; exact ctxBudget g k i) (by rw [eq])
    (by rw [eq]; exact (ctxArity g k i).symm) runs
  rw [from_context,header.1,Bool.true_and]
  split
  · rfl
  · simpa only [eq] using done

def oneContextPass (c : NodeContext) (wire : Nat) : Bool :=
  batchRow (makeBatch c.1 c.2.1 [c]) [c] wire
    (List.range' (wire+1) (c.2.1-(wire+1)))

theorem ofContextPasses {g k i} (head : prelim (targetOf g) (contextOf g k i) = true)
    (checks : ∀ j : Fin (contextOf g k i).2.1, oneContextPass (contextOf g k i) j.val = true) :
    nodeVerified g k i = true := by
  let c := contextOf g k i
  let b := makeBatch c.1 c.2.1 [c]
  have rows (lo n : Nat) (eq : lo+n=c.2.1) :
      batchRows b [c] (List.range' lo n)=true := by
    induction n generalizing lo with
    | zero => rfl
    | succ n ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have h := checks ⟨lo,by change lo < c.2.1; omega⟩
      simpa only [oneContextPass,b,c,show c.2.1-(lo+1)=n by omega] using h
  have run : runBatch c.1 c.2.1 [c] = true := by
    unfold runBatch
    rw [List.range_eq_range']
    exact rows 0 c.2.1 (by simp)
  have check : testAll c c.2.2.1 = true := by
    apply runBatch_at (q:=0) (by simp) (by rfl) (by rfl) (ctxArity g k i).symm run
  rw [from_context,head,Bool.true_and]
  split
  · rfl
  · exact check
def presentInputs (ws : List Sig) : Nat :=
  (List.range 9).foldl
    (fun m i => if ws.contains (inputs.getD i zero) then m ||| (1 <<< i) else m) 0

def rootAngles (angles : Nat) (ws : List Sig) : List Nat :=
  let m := (angles >>> (12*presentInputs ws)) &&& 4095
  (List.range 12).filter fun i => m.testBit i

def turnSignals (autos : Array (List Nat)) (a : Nat) (ws : List Sig) : List Sig :=
  let perm := (autos[a]?.getD []).map swapRows
  ws.map (movedWord perm.reverse)

def canonicalSignalHash (autos : Array (List Nat)) (angles : Nat) (ws : List Sig) : Nat × Nat :=
  (rootAngles angles ws).foldl (fun best a =>
    let h := hashSet (turnSignals autos a ws)
    if h < best.1 then (h,a) else best) (1 <<< 70,0)

def arcLookup (shape : Forest) (angles composites : Nat) (k : Nat) (ws : List Sig) : Option (Nat × Nat) :=
  let level := k-1
  let (_,_,_,_,_,_,_,p) := shape.levels level
  let (h,a) := canonicalSignalHash shape.autos angles ws
  let b := h % p 1
  let base := packedAt (fun j => p (3000+j)) (b/16 * p 2) (p 2)
  let counts := packedAt (fun j => p (2000+j)) (b/16 * 64) 64
  let lower := counts &&& ((1 <<< (4*(b % 16)))-1)
  let pairs := (lower &&& 0x0f0f0f0f0f0f0f0f) + ((lower >>> 4) &&& 0x0f0f0f0f0f0f0f0f)
  let off := ((pairs * 0x0101010101010101) >>> 56) &&& 255
  let count := (counts >>> (4*(b % 16))) &&& 15
  let width := p 3
  let mask := (1 <<< width)-1
  let finger := (h / p 1 + (h >>> p 4)) &&& mask
  (List.range' (base+off) count).findSome? fun i =>
    let entry := packedAt (fun j => p (4000+j)) ((width+4)*i) (width+4)
    if entry &&& mask != finger then none else
      let e := entry >>> width
      let c := (composites >>> (4*(12*a+e))) &&& 15
      some (i,c)

def seedForest (m cap : Nat) (samples : Array (Bits × Bits)) (cols : IndexTree ColumnInfo)
    (autos : Array (List Nat)) (levels : Nat → Packing) (angles composites : Nat) : Forest :=
  let sc := fun j => samples[j]?.getD (0,0)
  let shape : Forest := ⟨512+m,cap,sc,cols,autos,levels,fun _ _ => none⟩
  ⟨512+m,cap,sc,cols,autos,levels,arcLookup shape angles composites⟩

def repeatSample (period word : Nat) : Bits :=
  BitVec.ofNat 768 (word * ((2^(period*((768+period-1)/period))-1)/(2^period-1)))
def chart167Data5 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x8) else (0x2)) else (if i < 3 then (0x3) else (0x2))) else (if i < 6 then (if i < 5 then (0x7) else (0xb)) else (if i < 7 then (0xc) else (if i < 8 then (0x3) else (0x5))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0xcb99253248002c03803) else (0x94ed4c003)) else (if i < 12 then (0x45c3) else (if i < 13 then (0x801e03) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0xfb70) else (0x3fab28)) else (if i < 3000 then (0x31) else (if i < 4000 then (0x0) else (0x83007)))))
def chart167Data6 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x5) else (0x1)) else (if i < 3 then (0x1) else (0x1))) else (if i < 6 then (if i < 5 then (0x0) else (0x0)) else (if i < 7 then (0xb) else (if i < 8 then (0x3) else (0x4))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0x0) else (0x54e)) else (if i < 12 then (0x6) else (if i < 13 then (0x847c3) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0x0) else (0xd)) else (if i < 3000 then (0x1) else (if i < 4000 then (0x0) else (0x0)))))
def chart167Levels : Nat → Packing
  | 5 => (4,2,0,0,0,4,0,chart167Data5)
  | 6 => (1,1,0,0,0,1,0,chart167Data6)
  | _ => emptyPacking
def angles0 : Nat := 0x3002001003002002002002002002002002002002002002002002002002002002002002002002002002002002002002001001001001003002001003002002002002002002002002002002002002002002002002002002002002002002002002001001001001001001001001002002002002002002002002003002001003002002002002002002002002002002002002001001001001001001001001002002002002002002002002001001001001003002001003002002002002002002002002003002001003002002002002002002002002002002002002002002002002002002002002002002002002002002002002001001001001003002001003002002002002002002002002002002002002002002002002002002002002002002002002001001001001001001001001002002002002002002002002003002001003002002002002002002002002002002002002001001001001001001001001002002002002002002002002001001001001003002001003002002002002002002002002001001001001001001001001003002001003002002002002001001001001001001001001002002002002002002002002001001001001001001001001001001001001003002001003001001001001001001001001002002002002002002002002001001001001001001001001001001001001001001001001001001001001001001001001003002001003002002002002001001001001001001001001001001001001001001001001001001001001001001001001001001001001003002001003001001001001001001001001003002001003002002002002001001001001001001001001002002002002002002002002001001001001001001001001001001001001003002001003001001001001001001001001002002002002002002002002001001001001001001001001001001001001001001001001001001001001001001001001003002001003002002002002001001001001001001001001001001001001001001001001001001001001001001001001001001001001003002001003
def composites0 : Nat := 0x1000000000010
def chart167 : Forest := seedForest 167 6 #[(repeatSample 231 0x3ded9bfde5e4fe7df8b699f575b771f1763aeae6b57f9d10b1965b3b46,repeatSample 231 0x42100402189191a020004304cac9c13204026283a0083c1000bc523902),(repeatSample 231 0x773cb6a9fbcf9f9f776e6fcd4dff7329e0eafd78d39f715ac690a9a87b,repeatSample 231 0x8c24904016068584405ac80110204405908115855170284c400a98070),(repeatSample 231 0x2bfbf5719377fb8fbf7d3e98ddcadeff0533b799cbf2264b2ee7f22699,repeatSample 231 0x540c8082448904201ab2032200c0930120b4a0048ae828400265122609),(repeatSample 231 0x0,repeatSample 231 0x0),(repeatSample 231 0x0,repeatSample 231 0x0),(repeatSample 231 0x4f72ab5fdfbdbd70669fddbe76e5b49f9ef41e46e521dce5df5e26d765,repeatSample 231 0x308941806046024009a2209015103e0840a41c141da0c0c18002204665),(repeatSample 231 0x0,repeatSample 231 0x0),(repeatSample 231 0x77cfdf136fffc16cded5f2dec28cbf6ecfcf71830a71c7eded7ddccda0,repeatSample 231 0x830206d002019960005d409600f4052004200092015071c2d18cc8980),(repeatSample 231 0x0,repeatSample 231 0x0)]
  (columnTable 4 0x20004f0076080043c017820014700570800528015a) #[[],[16,82,131,100]] chart167Levels angles0 composites0
def chart63Data7 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x0) else (0x1)) else (if i < 3 then (0x1) else (0x1))) else (if i < 6 then (if i < 5 then (0x0) else (0x0)) else (if i < 7 then (0xb) else (if i < 8 then (0x2) else (0x0))))) else (if i < 13 then (if i < 11 then (if i < 10 then (0x0) else (0x47e)) else (if i < 12 then (0x2) else (0x0))) else (if i < 2000 then (if i < 100 then (0x1) else (0x0)) else (if i < 3000 then (0x1) else (if i < 4000 then (0x0) else (0x0)))))
def chart63Levels : Nat → Packing
  | 7 => (1,1,0,0,0,1,0,chart63Data7)
  | _ => emptyPacking
def angles1 : Nat := 0x1001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001
def composites1 : Nat := 0x0
def chart63 : Forest := seedForest 63 7 #[(0xbcf7e0ef6b0b57ffe8f77facd8ef7ffa0fe9ff75bdfda265ffe97bfaddb9bbfc679f5736eefdadb43dffbe39775dbede211fc1ffbb948bb92962bf9ef855dd96f54d0fb823df3bdfaf11cbcdddca838d2b6458bffd6ec20500fa51adc525b54e,0x3000b00904002401d082062200080010800808044000019001022100000140022041011040b08c02082000242010c00804000c10030104440028210840004161000100040443000430000c45540008102800104d068c0040040010d40249108),(0xc496bf55fe71efd7f9dbf9738c33d90eb46caed3ef4b29a7cedd4575dacd73fb2a7056e0fe273a3cccf8d07f5ced2fe71e8fbbc17947fe48b1d5e25864fb5ec707b5fb839724da0a8e2a7ea38e1ea2abca5d37ac17d1bee9b6383362bb12f892,0x286b002a0a8d188a00a406844b8002f40036305f18c040449041948205cb298091200642c200431b04580168b41a220e52153132f8c220020079056d401892806c822b851700c02a884029038802036a985932b00503267b861810629b122892),(0xb17fce3d17ff8eebe7ca87321765b88de6f6a9f7d4dacdb65c7ebf575feeade75f62f7e35965da6fe34e64f6de2591579fb22b0447fab0c4b2c7d26fcf6eefea17eafe3eb43795f057e894a96b359436ccb37f484ef16d2cf774aa402a6fc1fd,0x468012c08100610040521109143b900819810800650113b923900020601410306093483c08382c44c203e684000448e101000608032810a03080c0120446415f81005420a0a30590162884806231940140a08d088a78000019e22a00200dc16d),(0x7fea1ff7f7a67ccb1fa6cf4d7ff355c5d8bf9bfafe3cdfba09df8217b4b7f66cfde5ac49cf8fc243d3de2debc1b7e965c5e7160b67a96caf5f3bbd6bbb83a2fb3abb55f7cc1b7c3859d63e1332677e50bf8ac2d17b61d5f2cb4d8dd651fc2aa1,0x8015600038008404102862b040042283042060a0804260429c20e41e10c88101036091015287009321c41002c01a8404b286008018d1021248042188a1018000669928064a58782948d21a41000620d02a1942104001c123420181d641e02880),(0xcf2cffeeb945fff45ae2efe5e5f9af5538f1412cc7c65b1fa2ebeefdaffbec4ca9f48c1b4fb35fba56f60f0927f240fa4ef5f4ce90357d32dcdadcd2c3c75fb9a9dbe57d682ae79c0287257ee1dbee4e324a9e2f221a7cf2ccdf0e1e96934e0f,0x3402001142b050802005140c1a711028535d061309218c80428c1041c52628ea449a2c66a860502488104f8514e062fa4c30892ec20a08a110001c4000b86ae18002413111220694a029053800288e061062b82922123cd0899e0e0096134607),(0xa7c1b76b2398362e9cd7ba9ae96c98779b4d9985257e9f55ddb6b63e4787f348d24f0d3eaa6ccfd0f5fbb315dea0168db809e07f6d0a40837d7d7b879760ab2f70f9aa26acd322c9a0dfdfb77480976e212934f0e43597753da4cef1e0122d74,0xf81a40f14e832c9c42a6da8c15115cc860ba656e2a4ae2a276a519e1b46008d300e1c7aea8c4d719d268dcd1106ac0924125122ac141418103ec10cf22fcf801e26de9c5a4b3464fb8ce572320808b5c61613cd0240034392fa5cef0a0122c74),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
  (columnTable 1 0xe000fc01e0) #[[]] chart63Levels angles1 composites1
def chart159Data7 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x0) else (0x1)) else (if i < 3 then (0x1) else (0x1))) else (if i < 6 then (if i < 5 then (0x0) else (0x0)) else (if i < 7 then (0xb) else (if i < 8 then (0x2) else (0x0))))) else (if i < 13 then (if i < 11 then (if i < 10 then (0x0) else (0x53e)) else (if i < 12 then (0x2) else (0x0))) else (if i < 2000 then (if i < 100 then (0x1) else (0x0)) else (if i < 3000 then (0x1) else (if i < 4000 then (0x0) else (0x0)))))
def chart159Levels : Nat → Packing
  | 7 => (1,1,0,0,0,1,0,chart159Data7)
  | _ => emptyPacking
def chart159 : Forest := seedForest 159 7 #[(0x99ff07be6dc2effe5e99d5a79ab4c9fee7f0defbe2de6d4a49ff16bf9778d5b8ef9fb6d548efd7e1d7fdc4e6dbb7ae1151c3fff321d9d05d063afbfe4867b87d9336875c9e5c7ecf3790d0efd354f9202abe1186ddf6de40c0fed38c1a56b656,0x620058419820614921839a00310a04051004c3149822a0803200522080060a4084051291c04631051414008c7160800025408406040235100e8e1b110419804524000c430010604d6580526493003930280c804a18909a41c040038c10529650),(0x89a6f969ba745ddb3f93fde6fdd8a86ba1fb9692a263b355ce6bd45df7aeb7d5f579b2ac0ae13fe277d8b6f9c5a6fc6dc1f7e741fff642e157675bcd0bfdd6081aaafd405fbb304b173a34c37c3cca2934a5723e11dfe1be96ba7602f603f1a6,0x1455069444030220c478219b40a4f3220a2820002714440ac9580846096994222290a40e0da000920a42ae22820a0d4650273238890408835130644858c65098d0a131804f2b012210082c034c45c00995a06030014645a631ba5402e60061a6),(0x3efd73fb57bff8ed9e6f6bdbd701fed778eebf15effef697ee7debf2f7ef5fcd1f336afdff95197f2c2e3759b0b162eedeb60c9eae86366a7a6b1d7bff9effb63ff57f9ec197af90ebe9df48eaaba14fd4c8cb7d2a39e8f35e702d61a4ff4741,0xc1009100810005100000c0008850004900414048002a01213000400010100101800a010000018520000410100080b21008080084040100600c030a010100224306000a1000008c802b208040a0a200402000840d0028b00102442800003f0441),(0xf310ff5ef399aea9b1c785f5e2eff7ca854de343fcfb18bff659f82eac35f9dbfbf5c91b99fc3816b56edc284efaf30bebcd159c59656dbce19ead56a5ea5f6e4cedaafba4e271f464d674122d8e3fd293d5ad5172eec96e394b033643f079b9,0xcce02013800108021383a221424c034521432304140a2c206b60f40a52c446407205250ee2a7215353a020c035001c6c180a612401089050074415424ea002038ac9483a8c0716454525126080c2b32828461500a0241e2a803033603c07190),(0xf6bffe8dbd217ffe65f5736db27ea7e7678f66ed50636eb93d9fbfe4abfdfa3ad2ecc512e9fbf1d294f54ba69e4c353db7689a675ce99bb69b9fe218bbe5fd5fc3bde2bf21654cf7094764bf8f77d6d14b1f2eb6c548375c395d849f4d0d08ff,0x8000013200dc0e2082400481429118c208a10c42220c0514800180015041111168ca8d0c118100684ac0e810840a38391a1258c082c500220000a02002045f1081012018430c84908028049804d1c0c141130e044548241c111c84014c0d082f),(0x0,0x0),(0x0,0x0),(0xe572b9d565ce0be5c9b9d7cc4d9e4ed1385dcccd0f8eba3d2af66b6ab1e5f6b30537154675a54b0bbddf9bd5f4050ef10c615d2892840d6fcff5d8f1fc1a6dbf24fcc592b4aec673b85fdfd69841d95dca3922e13e5268a5c720cdf1900876ba,0xa1d06330e80e8a3a46d27f60229ae26a4a22331d005a6cec53690974d0602e460f1e0f7758a4a868e18e240015c010347447168538c149832f44124dadf0c1ca936f4e295ae027f945f5f860c41b092861b02e039504b8285a3c5f1900072ba),(0x0,0x0)]
  (columnTable 1 0xe000fc01e0) #[[]] chart159Levels angles1 composites1
def chart187Data6 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x0) else (0x1)) else (if i < 3 then (0x1) else (0x1))) else (if i < 6 then (if i < 5 then (0x0) else (0x0)) else (if i < 7 then (0xb) else (if i < 8 then (0x0) else (0x0))))) else (if i < 13 then (if i < 11 then (if i < 10 then (0x0) else (0x576)) else (if i < 12 then (0x0) else (0x0))) else (if i < 2000 then (if i < 100 then (0x1) else (0x0)) else (if i < 3000 then (0x1) else (if i < 4000 then (0x0) else (0x0)))))
def chart187Levels : Nat → Packing
  | 6 => (1,1,0,0,0,1,0,chart187Data6)
  | _ => emptyPacking
def chart187 : Forest := seedForest 187 6 #[(0xfcbffe7f77b3fe3bfebdf1afb9de10737f7e77bfd6f44e7ef9ddfbb677d7afe5d746ffdb619f519a48881beda98ffdff9dbeef9dff4e2e4eee7d7f15f643f7d676cd4ae4876d8587ced364dfd65692bf03f71b48ffddb3c975f6ca48decd1e35,0x144201040003004100050400142057c80010880020000089040210041003005080412880c020004000004048252c201080002001812820a080b8013048000092580d42c0040084030002501206400085009178002125004825b0484014c01c24),(0x7cb60e2a2c5fc375e1d5c03dad77d36558b31fb5de30987df7b6d3aaf1f3a803ec2aa6b63998f1de1ed2fb14d0e0763fedccf3fdbbcdfc64496ed7148452901d57f9a362a7ec17946acd26b3089d77e396ea1fb61a59bd18a16d1429cd9e935d,0xa3bd6251d808f0a2342ab2c66a480833b94e2055c99f67225100c540edf8570b45a4855b2311c28499c2a8a6ca805e6610c54e9e5210d505314446cca4f8442c05c2a11e83ec1b9c6e192080108d5f72ca4206301a5abd328a0d1429c91e8359),(0x0,0x0),(0x67f762b392ea03f6ffb40fc0d12bbf89e6df0b0d6e5bfb2743efa9ffcf695f1f3ab113bd5c7c19c4b3e7a91ee7f0e3a2eadb86b817d936bdf1e1981f99aafb8bd8b5f71a0ec662a9f95b7198ab2a6e8c3cdef5f741c37e5e0c48735d253a45fc,0x9459b104099048490423403208d343e76d205852842479c6908355c01c0580640048adbf03a4c741e7c08b1200acb074aa1b84b4141180a2509015201816c25ab88d825a10d6840b09503098ab236f040296f1862981ba4c48c87259241844fc),(0xa6dafbbca9ef73719eb3bafdd6b997bb86d5e416ee4bf74f3bb3ffd53b094ec7fef5546c896dd81de3d78d5aef67e30bf67d5dbbd68619b3f7fbe21bf1bc6d6b9fdc3dafc2cac1acb32671a67958e45efd7cdeb9c5964e7f889e7d967b378160,0x48240e30c42094b489c8118820002800904c01a91312862020288002c3d80e81408610002c0b30381802200502514f0b5484084a408450582843a0ca0328250504002d24820840f0922480241098905a5c680239d60240b2000605864b278100),(0x3fc5e3fdfbe75fcf69ef9dfa7e077cf7ff28dbc8b98433acef6e8f1ce42e5b79c10c5bbfde43ef6f3df876fd321f9fe08d4b3a5e85b7df0a19c7e9e7fb770abefdf7ca3b7a133a731fbc8becfee34b66d081207e6afe65f0f66f86f7014ceccb,0x81068290518c2a48402232441c00002008a030100468e14931100d140885b840010c209080162148412b23540901cc2722c00101804091e18415285b41e2800203001291a284000149883a87980cd021000004a4ada34b0d2438695010c4043),(0x0,0x0),(0xdbd4bd3ffb6de4ec23775d165e7cf92474529ecc2f979f96a725dd59e469b4b9b0af54c5be15bf6d3cfbfdf331dfd4bc83457076423dd5b114dbc8f41f76dbf2672ae0517d52bb53f06cda7f24e37b52e9feb21f0428e9709b3d65a39cd1e59a,0xc6a783d070c018500931801b243b5ae9880530ba6028600848c42c242f52843bf44f3c54d62099c91a8441802006a201815390c5220024218284ac7a42215479c20d44d0e4d6ab52e0445047024f3211e9ed30148121c144082c61229cd1a598),(0x0,0x0)]
  (columnTable 0 0x0) #[[]] chart187Levels angles1 composites1
def chart215Data5 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x2) else (0x1)) else (if i < 3 then (0x1) else (0x1))) else (if i < 6 then (if i < 5 then (0x0) else (0xa)) else (if i < 7 then (0xc) else (if i < 8 then (0x3) else (0x4))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0x2c0) else (0xd2c)) else (if i < 12 then (0x4) else (if i < 13 then (0x83) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0x0) else (0x2)) else (if i < 3000 then (0x1) else (if i < 4000 then (0x0) else (0x2)))))
def chart215Data6 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x2) else (0x1)) else (if i < 3 then (0x1) else (0x1))) else (if i < 6 then (if i < 5 then (0x0) else (0x0)) else (if i < 7 then (0xb) else (if i < 8 then (0x3) else (0x3))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0x0) else (0x5ae)) else (if i < 12 then (0x4) else (if i < 13 then (0x23) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0x0) else (0x2)) else (if i < 3000 then (0x1) else (if i < 4000 then (0x0) else (0x0)))))
def chart215Levels : Nat → Packing
  | 5 => (1,2,0,0,0,1,0,chart215Data5)
  | 6 => (1,1,0,0,0,1,0,chart215Data6)
  | _ => emptyPacking
def angles2 : Nat := 0x3002003002001003001003002002002002002002002002002002002002002002002002002002002002002002002002001001001001001001001001003002003002001003001003002002002002002002002002002002002002002002002002003002003002001003001003002002002002002002002002002002002002002002002002002002002002002002002002001001001001001001001001003002003002001003001003002002002002002002002002002002002002002002002002001001001001001001001001001001001001001001001001003002003002001003001003002002002002002002002002001001001001001001001001001001001001001001001001001001001001001001001001003002003002001003001003001001001001001001001001001001001001001001001001003002003002001003001003002002002002002002002002001001001001001001001001001001001001001001001001001001001001001001001001003002003002001003001003003002003002001003001003002002002002002002002002002002002002002002002002002002002002002002002002001001001001001001001001003002003002001003001003002002002002002002002002002002002002002002002002003002003002001003001003002002002002002002002002002002002002002002002002002002002002002002002002001001001001001001001001003002003002001003001003002002002002002002002002002002002002002002002002001001001001001001001001001001001001001001001001003002003002001003001003002002002002002002002002001001001001001001001001001001001001001001001001001001001001001001001001003002003002001003001003001001001001001001001001001001001001001001001001003002003002001003001003002002002002002002002002001001001001001001001001001001001001001001001001001001001001001001001001003002003002001003001003
def composites2 : Nat := 0x1000000000010
def chart215 : Forest := seedForest 215 6 #[(0xe8bfdb7f72cf97ffbb15215a5b1dfefd0e153d5cddd567d376ca8d3ff7a59cfddd1fdc5da6408cdbb5775afd5137903df9eed767df587fc8afb0fb91f79f696deb04efebbc77f65562d72f383957fe30e25a04143f6fb2e90718a47bd2c4edc3,0x6044410046d048000001226a6846000134aa0826220942d143142b2282e11384880404e03900070050122d440c101b4104002e0184a02c085414ccf0d8500020b10eb0c0876508410370a2a20046200e202048c050792012610006ad24421c3),(0xe9dcffeb9ddf7c9cf7f9f7ddbfeeffb5d3cc6e8def79fb7f1ffc6fd1323dff167c6defb75b2a95379edd3dbda24defdeefd7efb27e75ccbbf2a5def7152e578eb3bb379bcafb23017e79cde4be29d7bb3d217be6c744481fbfec5ba506ff5a23,0xb82b08001800810300014000501090420020002980824002c000000011800000200c0881e004440082148c092220900388100c000490000d220610202008120120200401900821036808c080120390311020b0004240400c10640985008a4a20),(0xff7fbf048b28bf6dc5abfce634354397efa3efbbd2aff0eedf7fbbefec622f13f3d1033e7bfd67d5ef97e9ea4ecec7232fbd0f0b89fb9b77d7dec16eeb50f2b6efcf385607555ceaa13fd3ab66b10167c9f5ff697cff0d63e1d723cced62159e,0x46400490648300801854210426c628b488141000292c244100d80150a012382b80026000118098c44400512080c52090228513479920183048c0a2478071c00a0b41b042000314880021133a24f0000e8301464135b90823e90122482560158a),(0x0,0x0),(0x9e8ed23e777f1fdbde06bfe6e53e68580e9b586b10d85cf4fe9ae57b778276f9be57b0489c2b1eed59ff074dd3729605fe7e336439886d552dcfebc8ff9b39791d6ad272770df25de4ca783d53fe7e2b9a9eb273982bf2ab0029e4d21dbaaed0,0xe070ba418a00633848e5e51948739f82e0210d148dc46090c2cc140185c16ec11023aa810c2a1909a0d4c8222a22e64bac0a991d04244d3c502a8320f04ab329440114725709aa58e9c87054505a142f0914d0721a886092104de4900dba8e10),(0x0,0x0),(0x9c417ffa3f1f7c34e067433bf0f2db603c6c3617211a78cfed79e69fdd1c573d182837925ff63a3a775a5773fa332cccc8977f902544f21adc6f97cd07fa7690b93f6b8ac18cf9d89ef448e4b5fc09dc9e8055fee92cd456dd2bfe68b4590271,0x3809325a4e316a888a8aeb82fc50bad839184405374175c0ce07968404835de93a2f37e00380870310a51a6948d24e876064220aa00c4e09c6187dec735e870864f53e2482458c496f53a6ca1e009cc4a8441bca93c1b52890bf668b4510051),(0x5e6b8ebc6975a372ed9eb8affbcfef3ebb22ab37806ed6c9dc4dd8ecb843a05f5fad366f2aff6eecee2fe3126cb35a3a49312a6f84afdf15865a8d9cf87ed0d3ee7d4dbdb5349cef851c5a47fa8c3f6654e584b974db45c6d29f05abfb118b3c,0xb927d90c1320640082a0569089215200436140de449119126322ac8258ed40903f810fae6e4c0630a983a4005b32d448d97a682064940480210210386c8225c0e0980cbcf53c89474590c8411a0c8fa174c680ac40423540108e05a3da118a34),(0x0,0x0)]
  (columnTable 2 0x20010f005e08006302129) #[[],[32,83,116]] chart215Levels angles2 composites2
def chart347Data6 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x5) else (0x1)) else (if i < 3 then (0x2) else (0x2))) else (if i < 6 then (if i < 5 then (0x2) else (0xa)) else (if i < 7 then (0xc) else (if i < 8 then (0x2) else (0x4))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0x328c9807b0003) else (0xab6eb4003)) else (if i < 12 then (0x23) else (if i < 13 then (0x803) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0x950) else (0x18ed)) else (if i < 3000 then (0x3) else (if i < 4000 then (0x0) else (0xa305)))))
def chart347Data7 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x0) else (0x1)) else (if i < 3 then (0x1) else (0x1))) else (if i < 6 then (if i < 5 then (0x0) else (0x0)) else (if i < 7 then (0xb) else (if i < 8 then (0x2) else (0x4))))) else (if i < 13 then (if i < 11 then (if i < 10 then (0x0) else (0x6b6)) else (if i < 12 then (0x2) else (0x8))) else (if i < 2000 then (if i < 100 then (0x1) else (0x0)) else (if i < 3000 then (0x1) else (if i < 4000 then (0x0) else (0x0)))))
def chart347Levels : Nat → Packing
  | 6 => (3,2,0,0,0,4,0,chart347Data6)
  | 7 => (1,1,0,0,0,1,0,chart347Data7)
  | _ => emptyPacking
def angles3 : Nat := 0xf00400800c00a00400800800200600a00400200200a00800600400800400200400800400200600200400200200200200500400800400f00400800c00200400a00400200600a00400400400800400600400800400200400200400200600200400900400800800800400800800200600800800200200800800f00400800c00a00400800800200600a00400200200a00800100400800800900400800800200400800800200600800800500400800400f00400800c00200400a00400200600a00400f00400800c00a00400800800200600a00400200200a00800600400800400200400800400200600200400200200200200500400800400f00400800c00200400a00400200600a00400400400800400600400800400200400200400200600200400900400800800800400800800200600800800200200800800f00400800c00a00400800800200600a00400200200a00800100400800800900400800800200400800800200600800800500400800400f00400800c00200400a00400200600a00400100500900800100500800800300200100f00200200200a00100400900400100400800400200200200600200200200200100500100400100500900800100100100500300200100f00100400100400100400900400200400200400200200200600100100900800100100800800100100100900100100800800100500900800100500800800300200100f00200200200a00100100100100100100900800100100100100100100100900100500100400100500900800100100100500300200100f00100500900800100500800800300200100f00200200200a00100400900400100400800400200200200600200200200200100500100400100500900800100100100500300200100f00100400100400100400900400200400200400200200200600100100900800100100800800100100100900100100800800100500900800100500800800300200100f00200200200a00100100100100100100900800100100100100100100100900100500100400100500900800100100100500300200100f
def composites3 : Nat := 0x123000000001032000000002301000000003210
def chart347 : Forest := seedForest 347 7 #[(0xe9f9eddd758a37ef56c9893edfb29fc3b31e8b2abd36679cfbdbaf7f494cc75efd5ff5fff4035a1d2efd6fb5216b38cf01cfd4d123ccb4afb751f8fb4a74d95f6cb81ebecd0f45bd22c10f248a4b42de5ffcfe39be22ea0937ebb324b45e704d,0x68492028444ca1010a0240002640080406465114641507e06d55000846828603600a121b003040d8a0900be6c13400885000140c004804868244077030157ac4802522409030149024102240249501079d381429a626801202bb12494146048),(0xe6b7e7b50ce5c630d957a3cf6dbf7842e1cccb4faeef47fcabfe55b6b67eefdf7b34dfb15f7dd31d78de9626bbc04b0a142fd777faee93b2be9c3de2ebd6ff187944997271610d893ddbd4fae97693c29316ee9985397f20d6710c432e72c1df,0x10404848321a34c6000958165008923a280318ea0000280151200c005901960e0065089006441b7250c2340002443c506030e60f20c1702405902080d0460840a6100502205808803920701ab09682ca02046418051c174006500c432a620185),(0x0,0x0),(0xbff35f69c5ff8dd3f73dc2366af5e1bf7ceae6e6f1f63cff4472975e77ff359f76a83d5cc88ca1c95f5889caceeecfd4dff4c3bff6bdfa5a34a38555d80d79e7e257f4f912d4f0eb9bbe288ecd9dae15784b258a9331eeff081dd5d9fa104ab0,0xa008a0822a02604c00a2061c840c1001421fe9110ae8c000228110c4804c314008160549828000016081051e084182a094849820d2471503400141671b01014881d24330088150e9d182009049810d107a1b2580980228c900101510b8104ab0),(0xeedcbbe7ee9fbee78de7fa76877d32b976d823367f8fde9bdf5fb84d7dec73e495afb30eb2af5e75d645f4b93fedbce479aa445497b9dfdc285bc11dde7f213b56ff246d54defb77370f2bcfa21128e945856a203b0f8fd7f58262ca928eb7a4,0x1163415811a00103201dc1a118004544890012e830120601102a04226102c48f400150800574c9f005268a4081a83c404018641608a8489006c88a88002400122404244bb61c2006240c2908a034006904040a14650d9606d48042ca028a9504),(0x0,0x0),(0x736fd56fdeb2f91bfc67f6f777f86ff3ccf7995b8649b7613367eaa6f09ffa2fb96faee0b77eb47adb375247709aad2fa5e9bfffbbf7192369fde60e258a073a95c3bb60e8201bf6cf0cd3f97c7bd170c0f613c5e8ccb9bcca337c3611a9c572,0x88b022100141832042c28108047260049248641412a3004602989043824420d00c820509118884040a3983d310a002240a88119082020181e82001430121042e08cbc83549821170460c80c10c611501185213c5a8008839008370141108c472),(0x0,0x0),(0xffac98db3bf3dfdafffade27936eff6f8827fe9890f1e2d486efe3c9a7df37ac4ef3ced499927febcbe7596bf2dfc3bbb3fcacac64be685d53e8326314b466c6ec63cfaf9e20b60cd474ea23b5dfce3c296c55f6f2f4150cbc5e997d49813d0d,0x242452dc40c0893840d00c2710103e02d000060e5002989194604101c02c808e00002a62075105885444800e10c51026170620820b8206413820098a052ba00640424009220860420303a22921e820e0524c032436c1106980088694081310d)]
  (columnTable 3 0x800ac000a72802b200298a00a5c00b4) #[[],[16,82,131,100],[128,49,100],[48,129,82]] chart347Levels angles3 composites3
def chart127Data8 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x0) else (0x1)) else (if i < 3 then (0x1) else (0x1))) else (if i < 6 then (if i < 5 then (0x0) else (0x0)) else (if i < 7 then (0xb) else (if i < 8 then (0x2) else (0x0))))) else (if i < 13 then (if i < 11 then (if i < 10 then (0x0) else (0x4fe)) else (if i < 12 then (0x2) else (0x0))) else (if i < 2000 then (if i < 100 then (0x1) else (0x0)) else (if i < 3000 then (0x1) else (if i < 4000 then (0x0) else (0x0)))))
def chart127Levels : Nat → Packing
  | 8 => (1,1,0,0,0,1,0,chart127Data8)
  | _ => emptyPacking
def chart127 : Forest := seedForest 127 8 #[(0x82a873704bfed9129e8a0be0df5288f923baf85d4a64738667b51116f6e7c37be391def0c03cb1f5e183ca3600ac187c2fd73f085c3354b5b51bfb5a6dc79fec6dbca70c98bf7a23b210d18d0e0832cb664077c4614a13c665e9682436ec7730,0xc2205112445208888c020b028a00801007018c20024013a40ec80002c50110081091860000440134a1214010000010486351120054021090860ae8020a85868064a44404101a1820000047a10800020464000500004a02404521600004e04730),(0xd6cdc495dfbf74e55c58b25f9f6c5fb0d09c43d7515c5f7aca27fbe9a591a9c6facc755e0ec3e422dd1e36d4b972a09b109064da62c05d40d8d414e26234d695d7427d2576e8d69f7c7aa4deed3775297de309c99ef5403397048c4df892a9a8,0x99c0404820020255000140900080a0400c8201480020c0800240104004200442a4051582402e4024002100c7140208200006048020040010814142860005004114031310440448a001880140422443b001320099285402282008c047810a088),(0x7ab3bf2f6503935a1143b98f335d26adfd50aeb4ba3eccbc520faff37fadb66d091c8b8e67a44eaab26f37ba95eb56b43a6a998411c39b5a52baafc2938ba3c7155e43ca4904a99c462f88609397dc44dccd8f8e3420afb1e9b254498598d41f,0x4000a2234411111021e760807445f5e1d43002a036c4c070e0036ae921b43708040828a300840aa8b46927b2002b5434394e0106b1e3115ed22809c09282a1232018404a481ca01446270840819112405e4003a424208b9161b0504981885407),(0x2d1e3ecfb8d23aa82bb76dc43a8bb9477e455620a68b864f18de2f139a6abea61e278c09738cbb9d6b72118d5ed7ef8ac229a06dc14de21a2f3aee3d9899fe82120516fb85041f61c3e53e2779d0e874c1bcc877d206fe4e8c17d79645010bd7,0x8b200080a0820209d0101d1c0202001c21c5100a8908138218ec0002940888a230a58018730821114012100d7a8002ca4420e259400800000512960c001556800024060183001f61804876237800ac948088c8415006744e8c07860604000bd0),(0x356186fec928b619a4f5def12a9e5623e23fa8f8c69f11693df64877c1ba4bf98e2363a518bc37b400ddfea14f526137e0deb223d63d6b0278444d95155a096c2bcfb8535cc3dc401da57a0996cb037b9573e237ee86c04832d83bd3c33d7448,0x340504091b09704423e480e0003150a150182181743728592002c459002643410e42612708a11c8200c4a7a004532035888e01228ab54b02380000917568286d0b4b90524880c00818a700088222014b11723236ae80800032d819d1c31d3008),(0x7880d99db043dd428bbb77f4f4e39ad9e178d0da1f6baa9a87914f22706d88583b1a29cf9210dd4360c1a4dbfd2ffc5fbda329c82fe7a4f75577170dc8710c6803b212bbafb1e2e3c949999146215883baa8d526238c1594f067192fa95792c5,0x848ac85108cf26463c174dc54763ccca8a4425e683e2c1121120dc01044ec424b0a28879a12dc0a100020ccff2fee150c88298828f9a4475855170dd070487a035a82bbc7a14207c1989800e621d08a92aad23f33841594b046192fa91790c5),(0x8d667abab6203fef48faa57359715d33f139cf42593c9a32d71b62bb1690154651f87280df735e5d3fe54dc0b610aee5c29c435efbb21580304e8a210a7ad6118c9f08ef6a586672ffe02cb37a773bc01e6ac9a4c993a51d3765f1510a4a0cf3,0x61b31a506016da0dbd08d6991335117732d6c0593d702782d3527a8e944b8b5193a2804a711a4dbfe52da086189a40c2dc0333e9b0044a34430a848eba8619448e0c88eb1a23407fe42de132553ac00e60c9a46912a51d35657151024a0c73),(0x0,0x0),(0x0,0x0)]
  (columnTable 1 0x10002fc01a0) #[[]] chart127Levels angles1 composites1
def chart223Data8 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x0) else (0x1)) else (if i < 3 then (0x1) else (0x1))) else (if i < 6 then (if i < 5 then (0x0) else (0x0)) else (if i < 7 then (0xb) else (if i < 8 then (0x2) else (0x0))))) else (if i < 13 then (if i < 11 then (if i < 10 then (0x0) else (0x5be)) else (if i < 12 then (0x2) else (0x0))) else (if i < 2000 then (if i < 100 then (0x1) else (0x0)) else (if i < 3000 then (0x1) else (if i < 4000 then (0x0) else (0x0)))))
def chart223Levels : Nat → Packing
  | 8 => (1,1,0,0,0,1,0,chart223Data8)
  | _ => emptyPacking
def angles4 : Nat := 0x3002002002001002003002001003001002001001001003003002002002001002003002001003001002001001001003002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002003002002002001002003002001003001002001001001003003002002002001002003002001003001002001001001003002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001003002002002001002003002001003001002001001001003003002002002001002003002001003001002001001001003001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001003002002002001002003002001003001002001001001003003002002002001002003002001003001002001001001003
def composites4 : Nat := 0x1000000000010
def chart223 : Forest := seedForest 223 8 #[(0xbb1c2e8d94f8df7d68f9065d26a5fa499b2dfeb3fc174dc2472c90966caac18d62aa7d5f851bb7de350765320ba32020bc30b7dec37ba02b030fca7bb5fe3ad99d531c3dab9a38834568d064d064501e91a83f3e31571344b54350007b67f9b1,0x104014893481359d043912cd226118c90adbd767880368c39122600024521500002835d4051132963103611801a220243014c0c4413a2039410fc00330bc36281c06080daa82380645c8f001910c5436d50800261156134090415000536638b1),(0xf4b92ef3b502ce15227d5fbfa6b96f1756a9447bad2155fd1149faa9d86228795761bba888b4bf31cdfcb3f0b452cd89090b44ac4a4096dc9635254ab0f728cf1a65f5695f2da26b7744567dd892cb0aafb18ba8afb9609d76508a65e24510cc,0xa200c862400012428c300010441250200808032005040699900a482180104440002882808400c404108020108509014124000640840080200100800200c12221d56044280248320003244092894808e19a89a489601564108a40a001000c),(0x4d57d12d0bcd48d7d84d48385ada97dee1799b2f83f2391ead83bf7ca7ed7796b08db27427794258f21e18eeb989ba489e1c9864b1a33f054de677e24b18c5596254278622d4d4f4e25e0f8f2dbdfcb7799f44d54862bbb289ed28c916baa02c,0x41140800008040041042040c488020c00110005084ae0a8400003708048320008052206103140500010202083083a009c1c10041183024c410412404008011244540082021080a4800608890c040002611c045208201a82816d208106228000),(0x8aa7f906de97a41f959ab0ca731630abef5b654512ceb637b417a265ce9fffd81d50978057e3fec7ab241b4f6d95ebfe53c2ca913625e923e36bf43d527353e8d28898c610b037040eab7130ee89b563034ee134a446ee4e4c059f1e94c416a3,0x9a4c9c555003311994490c98022438c1820254c003951851b41be00055140dc85410948083423e85a824194f6c95054d23424c106a30200102eb242d107732e89082184430c037020489f100a0099e64000061802446e44c4c009c0c10c416a1),(0x5e90476ad17eb978b5a6e3e0631d96e79ba6ea9f728eb2657a7c842fe87ccde5ab766c7751af1cdf00b9d5a16274db36fdf13b5387fdda26b8488b156709da33858beab6cc07ff102aa3e858565001c932c17c0b980c5461632e57538d0bcf5b,0x45806122816488002386c10010008312412028187468022c4a0009058808c0062b4608235028004800c880a00248c802cca9330384459e02b8001910cf00c9070128a2a20404c040022608da4012000922c01e0188080021232e03538c09c14a),(0x0,0x0),(0xacff5d74202671e66a023f4fdde7645685e9e44b093f761d8be55068380e4d22658f6abd7d0442a9c8c1ab86dfd80ea33f9b53b6a89f61f492f1360d32971c2600f0ea5fd7a5c80f9cf35013100a769dfd2ce836268e15ab92f1b02f44c4cb72,0xc85f14cc048012cf8594304094acb84da7d87003f85430194044413114106f48b1816e957d04420930402b131a6c2ae27c2a43b4a899617432dd3e0d723d9c265050201f9185402709e9481b300c669575086476520615aa92e1302f44c4cb72),(0x7569ea1662ce3097fc9745b1b8e373eec2e2d3b009351c99afe7375d99a3521a86bd1cd468dcd926178b44d83c5e50cd86c4a586f7fa0622aba20ca03af5d4e4a1ba6b9734c04699ee394d96c3b476946cb8eacdf2d7a129f6a8e2d008f82f87,0xf36e3810b1c5201dbebb8494304711c2dee4b58841b117038794308d4ea3490ea2e81cd1008cb92213890cd83c1441c702c3a483c6302423b2b10d252ef5c664a8a27a7ca04a05117e38471643a1f6840ca0ea8d72d7a1297680c25008d82f87),(0x0,0x0)]
  (columnTable 1 0x10004fc0160) #[[],[48,33,133,118]] chart223Levels angles4 composites4
def chart251Data7 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x0) else (0x1)) else (if i < 3 then (0x1) else (0x1))) else (if i < 6 then (if i < 5 then (0x0) else (0x0)) else (if i < 7 then (0xb) else (if i < 8 then (0x2) else (0x0))))) else (if i < 13 then (if i < 11 then (if i < 10 then (0x0) else (0x5f6)) else (if i < 12 then (0x2) else (0x0))) else (if i < 2000 then (if i < 100 then (0x1) else (0x0)) else (if i < 3000 then (0x1) else (if i < 4000 then (0x0) else (0x0)))))
def chart251Levels : Nat → Packing
  | 7 => (1,1,0,0,0,1,0,chart251Data7)
  | _ => emptyPacking
def angles5 : Nat := 0x3003002002002002002002003003002002002002002002003003002002002002002002003003002002002002002002001001003003002002002002001001003003002002002002001001003003002002002002001001003003002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002002001001001001002002002002001001001001002002002002001001001001002002002002001001001001002002002002001001001001002002002002001001001001002002002002001001001001002002002002001001001001002002002002003003002002002002002002003003002002002002002002003003002002002002002002003003002002002002002002001001003003002002002002001001003003002002002002001001003003002002002002001001003003002002002002001001001001003003002002001001001001003003002002001001001001003003002002001001001001003003002002001001001001001001003003001001001001001001003003001001001001001001003003001001001001001001003003001001001001002002002002001001001001002002002002001001001001002002002002001001001001002002002002001001001001002002002002001001001001002002002002001001001001002002002002001001001001002002002002001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001001003003002002001001001001003003002002001001001001003003002002001001001001003003002002001001001001001001003003001001001001001001003003001001001001001001003003001001001001001001003003
def composites5 : Nat := 0x1000000000010
def chart251 : Forest := seedForest 251 7 #[(0xdd03c7deef14b19112bb5b033cf75fab5a355956c21e913b3eb77e94b0a242e2f3b6e2e84f8848fb6e941d880d4d1d59dd28e2967e52d4d406d07dd306fb6413d6f3388fa9659c60f8796f2c929c8eca2b1c2dfee219845ada0ac570c50786be,0x1601203000047100123214440c0c4401302480062160090982a7200210800202021e2088068842180ab005000549154c150892526440500102080981408964004e8134028101082048206e10800c004a03102ceaa0190412ca0a00500102063c),(0x90faa1657b0f1afa49fe168eac3075d6cd6bf32ab721dffd63dee01985b119b1bab09e1d75938414f50f45a3c93a67a213d7d8a99b9307e3f5f4da0c6a89e486c09d1a7daa158c7ed6bf10ffd1d34661b6679a687a67e98062857f5662943cd1,0x40c2080261020e7260410a18a1b2b8020882130002008034001004b88a3001093880980151000400a440a0a38830622202d3408999330340c0e4d20c1400020aa0104a6d28009459909b10e9114042a0b42501105222c88020856f04628428c1),(0x0,0x0),(0x5aedb79140df063bbfc2bdf96f1f6358298e94752ef76c007fc34fae7fecbd2b6b8b1876ebb42119ab50f77572c5f20567fadf40607db5ba48eeb8b5d0aeb995ac81bc74d13a399832e8d2467c16440175d05e402d383625bed567f92b9a0920,0x3e00b6884030a61a57122cd11e515304380c80f220d43e05ea014c8483a4b12a638b38560bc4611828400770218c3007a7425e48605594b040c8b894d902a8852c813617d99a190232e25826801e140114d9b4e229383624be5547700b920920),(0x44ec6e4766ea2f133d7ce17ac66ecd89e3eddd5cee98e48839bc3c355b4fd5524ce6eae3af373953d40ff6fdf270e82d264825537d2b784a0567614eb6705390bce275e0537aa5bc2c01afc23e6de3b27b307300077457198dd6a28df44962c7,0x403e0847278800840008410aa002a8b8c10072099600c02215189121004a40141c60c221a0311463d00df089d020c8800001210011aa2a4a8523000026700312906a40a00620849c050181803a0162a4e8244304064441090180a08df44960c3),(0xbb739dd9f57fc16ee3897a15f3d3d261da1662ed08467786c4255bd72016a28c156bc53d1b4e57ef0ffd8b27ecb7b350c8a2068c544dcdfc9bab17f911570be9832dc97e45c07a0d77f7d0a208e3391e9c89c797c1aa63e6112948a3fb63e929,0x30814800510200a080020120f21062041800910800d48244084b94001620841020803489620561054d8a34c8164000c8a6040810180d849102907c30028ba1912c88681440344930000123008239101829c31441a263c4110140a3e2618101),(0x9c19067218a9dcc6c4a4d7cb92d5b8f7754f9f2ad1617f789a59eb2e0413df75a166b5cfb6dbc6d7f91b1b8eb2ae80f7273f1d31a7cc1bb97209806b6b6fac8409d9238a3203839e3b00531561830963166bfe6c3cdd2bd6a46910378cda5643,0xb21cd6381238c18c12a6b1201a44067ce41984a288fd170bd100d9421003fc74873324cea6526397519a110c328a84dd042c3f30068020bd020908f3eb6fa1e00ca9210210010306230047144285290a424afe6c2cdd2356846810338c5a5602),(0x2ef41a93ebf8667dd932bb4d5710a4e9ff73e98da0de8e84e22769d38e9f305cae5d711e664c3a0ec078516bbff3225f2fd3c41fb0e44879adcf72a04d0e7a6d4586d5b327b4c28545f6da8c42603f7ee8d640a938cac43fc53639401ee86de8,0x3f4800275f281c094f5438c4d904a48dd343ed2e261f0b58b014a00a4e61504aa65d6988660c2a06d030510323613a1f3311892521e640796ecc60804d0c504c06807593a3bd8184c576ba044360444ee00404e13848843bc43639401c886ce8),(0x0,0x0)]
  (columnTable 1 0xe0079c010c) #[[],[81,130,118]] chart251Levels angles5 composites5
def chart415Data8 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x0) else (0x1)) else (if i < 3 then (0x1) else (0x1))) else (if i < 6 then (if i < 5 then (0x0) else (0x0)) else (if i < 7 then (0xb) else (if i < 8 then (0x2) else (0x0))))) else (if i < 13 then (if i < 11 then (if i < 10 then (0x0) else (0x73e)) else (if i < 12 then (0x2) else (0x0))) else (if i < 2000 then (if i < 100 then (0x1) else (0x0)) else (if i < 3000 then (0x1) else (if i < 4000 then (0x0) else (0x0)))))
def chart415Levels : Nat → Packing
  | 8 => (1,1,0,0,0,1,0,chart415Data8)
  | _ => emptyPacking
def chart415 : Forest := seedForest 415 8 #[(0xb76d827afb6ed27abd01dbf8a313b5820a6fb5b786d54193f3123f1a09e356c7e431a67094d3bff9fad08d73b06e4b1e5d95b6de0f9b4922b688feaef7ae44eb68424c6958f2f41cb34293f65cc443c1886a03c8c75c59167d0561002f32fc6e,0x846804084844c23c11050bc8010900788006338a8e004042720640000124030020002640305080215a0008b0a42a41005084bc580eb101028308ec0cb08264482940780130e0841c3202931c40004b04e828024085585816080560000f20a44e),(0xa7825bfff4e9b47d28a0ab7849e9d520bdeae97157950f9fed040badb2af22325318dd96842c3bcf3316d679a081467c15f24433d6880cc8fcd441c65cbfb27ff2171f388a2a9bb1ece38a56bba256230dd706a8fbe587001896197af94254b9,0x6a8441c520b81943a86220314844f3002da84024100c239904500bc7b80bb4380400d99786283ace2130d408004006dc8572002140004c8074940052483c9133861606280a0e12a1cc604043aa83142a058085b4722587001092195af00250b1),(0xaa78adeb065b0ecd9dbb2e88ccf05cdbf3d1e1cfff2a6f7d974982b6f3df4b2d914a7b467a4c8213910af34ed2b88fc91d8ce30da83101fd5b76ddcd0e4129d682bd799fef556b6a6eb32e91e273a4547aba7441088af2a7c258e86a8ddc2215,0x8c0a444300085310040226a00c42120091494802d02688200010068440062840002028448011100a034290b000010804e2002d5180098b02c5800401288408281802c491210220033c800030804068122000088a30854248202009502204),(0x4cb37e5540ccebaa43759eef740f22771e152b79994ad2a04facc7d78650ed3d2a8c2c893b2dce3c4ded95896d39bc62e2f609f07245be1603153c78a031de519782ea37004a209b911d742c8db9fb6e9f0dfa3ff0337d5882bf1e955609c584,0xc00260500830224000050808000880b108020a2010280000710c0b020060a8890088601003010a244104b4816c0918008092093042802100000d10580022445110802010004a00191100412c8501240c900842880001491880171c1406094400),(0x5107c3298be80313fac4e45ecbd6444e3c0d9ea67ccff784ac9f3e853b07fcdfeee583e941b7acfbe88e5e4a0e4784c46b6b97b8195f7e5a509ce320131c858a0c4f87e21ef94f5f007d65e8125e10f992f78d241e0b8cf1670087b7d03238c3,0x413a504880103ca9ad03086321f0256a1c00440d1ad800c9190a1220244468e6481ad488434d88088424a00c4a4c10b690281114e5858149203214b4c8922040f83a20a104bc008552c00124210c103c789261a0284e1670083a3d0121881),(0x0,0x0),(0x0,0x0),(0x217e79482f3f1426f56fcfa505cf598a75a1b1b87424eae155436446d5e24b98037749cdd55a666a8329662dde7da3ef51deea95c2ae57a77caf9011b1f08138407d22b5755d89e4d34a466741c14813f6a960c4821040bf38f6e31f928c4afa,0x1792105012b86307a06682b1985d91996813283096e50f88019035872068a1f81315684f159a06ce8421643d2647b3fe53d118f582aa67a654ac101390d8c539401120b5324c08c0870cc26383c1781392a940a4a210403a38b6c31f928c48fa),(0x52f2f8cea0cfeca345bdf2f3b7af2f67f3c092fb91250fa3c06bf5d0966b310235d092cae9fa554e6cf90bbc0194f0bb9c541c41777dc02b1811c458bd59723495d7c9474f9ec0e3b3ff10d2454a4bd2c5db4237767e846924ab72620a5783fc,0x12281d0980481c3a7e089362a5c6224296ccd499c1030f1d82c0c4c9f4131156b51402c2ecaa550a3ce8431a0090a1bb142434411d6fc0a21ab0c3003ddda220a56f49c5df94d6a280ff30d06048ca5045530837667e846124a86262085683fc)]
  (columnTable 1 0x10004fc0160) #[[]] chart415Levels angles1 composites1
def chart431Data6 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x16) else (0x5)) else (if i < 3 then (0x4) else (0x2))) else (if i < 6 then (if i < 5 then (0x9) else (0xa)) else (if i < 7 then (0xf) else (if i < 8 then (0x0) else (0x0))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0x360d9aa411cea3903f538430ef80dc164c98330bf6263aa29002708c2b07f64d1817d0b90da81303c1b02c3701c03) else (0x1f8433266646a89c008c00fd45acc38006c00bd658c89d895b32c000f0016004c0038003)) else (if i < 12 then (0x0) else (if i < 13 then (0x0) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0xac9b877562503a281500) else (0x58d452167ef6a2a719f0d8dc6acff57909cecfb3e1e71ac5)) else (if i < 3000 then (0x14023) else (if i < 4000 then (0x0) else (0x482813cb287181)))))
def chart431Data7 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x22) else (0x16)) else (if i < 3 then (0x6) else (0x5))) else (if i < 6 then (if i < 5 then (0x0) else (0xb)) else (if i < 7 then (0xe) else (if i < 8 then (0x4) else (0x9))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0x2e46c4d90478e4116cb8b70871061fd522e66e4529320770e65103794e0d6c11753309dc18c2fb746c015cb205b0a6900278670961ec23b4a684d19b803f076a89920336a40dc17b6a54d550139740460ac0f8ea61cd99b701702603d9301b01610c03803) else (0x365cd95be54fc4004f012ff14d968047010e15e9d3803bd93803f00de35c997802fc97803300aee5cad5a7588d68023007e356a97b61e8978017004c01b003e35e002c027001c003)) else (if i < 12 then (0x482b073) else (if i < 13 then (0x1401a0bdc1201c09d402b11880c1c01606c2e302003d80130587c0e03) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0xe337bd9357cd718c02dfb36baa8e8d9f66593e3e8a612809ee755bd695945f96b545414ad15404ec348be2ac9621067154470d82504000) else (0xae139d427adc3b9d41fe8218087ce52b69907c96633009b2ca5d7af8a2a7f82cec7bf26d6f20e67833efce9ae7cbbf5d25c71243762e7ed9d5155156eedaa33a888ae1e7e039995fa1d73b76edabccfc7bf7efd7365df36ceaddeaaef79dcedb426ba6bc70f7b4d49273a1ceacf4550944a8d7e8)) else (if i < 3000 then (0x2312341304100203230118) else (if i < 4000 then (0x740) else (0x2386098643417ce27c269c07e702e838383e1e0c820560d0ecb20e00024961b289a456310e15ca0421b120122c02048ea7d)))))
def chart431Data8 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x27) else (0x3a)) else (if i < 3 then (0x7) else (0x5))) else (if i < 6 then (if i < 5 then (0xd) else (0xb)) else (if i < 7 then (0xd) else (if i < 8 then (0x4) else (0x9))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0xc1132240116d098534454c20c3fc660f61dca70ea5d41bda014a9541ac33d540c61cc2f8870b6cc05230e68c14c27944544ca8238435cc12c1faa49dc0ec1b857066c91a934e694d42880270471100f82b036cb9723261c804c078170160bc03803) else (0x5d7a6bdf16fac6d700df75aeaf5d3aabc06703181ac0bf71eb2f7573e38057029fd33cb9f46f27012c08e04f021816c07fd56fa700dfead95efaa00cc05fe5ed2f00ac04e03b01181cc03fb4ef2b005eeb8013dab003feb9b5e005806c00e003)) else (if i < 12 then (0xa6fb2743) else (if i < 13 then (0xc0071dee160981ccde503599c200a0a060be60a015c80d07014c9e902596c8e63218c2203b904d20138198bd6037158804e70403d1401ba80702e060987c1e23058fc0e03) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0xa5da4aa38a20a0c9f69e29cc9ad99998596e95893b9259138f58d58b48a688587085683c8268137fb7ed7d77c47a278d76f75273b72470e6f96da6c36b069167b66c6586356206015ed5d15c25af59a57f55853b52850d4fa4e54ca4a949848146e45943c4244063eb3d23bd3aa39437f36835333e32230e2f72e42d52b629c28126e25a24b23521b2031ef1d71c41b119b18616f15714212d1181040ef0dc0c80b609a08106e05904202b015000) else (0x1a2133e56ba6dc1a4e9cd08593f4f36773799d8e587c948fb2e56b0b9be53df2d50793640655db55dd075a83fd2fde2ff2f39d2be3830f6d7b993dc3e9f6f553da7262377c4f7df6e8586aa75222f105cd2d65ea66f3465cfb76c27c6d324b3b9c0fe5b6df582dfbf7c9dc02b7b37c8ecb9d88c2af99dd548a5e74ed7d9bcd8e618cde65c0f8f037e27dcf5d8bb8712b2933f3f6c372e2108c09f63e189a684a3d3c373c6aceeae66eba41266f256b1130e7d0f0d8817853b87da84f024d8f71b420c5720cffeb9ef96a7cb2bdade18ea903e9cd75fbacf9bce61a42e6ea35416ab9da16fbf75de78ffa253cd8334e68d54ca6d82becfdae361542fd81507fac07ea870734227ba41b0cbdfe69d23e6f3bec128f95ae44c8bca9362dc5eeb604d7ab0eac5c78c2c28f75535a2b5c7792ebcfac9f62544c8787cff893f5f13f0847afc855eb929f5831fc3e77dbe05f)) else (if i < 3000 then (0x22217151013230313121443321223542513143201220233131001011) else (if i < 4000 then (0xbef4a80) else (0x2883c760b2b15c3e45220fc0c14380042241201504a78068a4be52078ec6e5e0005ccc5710838981f0a080803a139c4083f1c17c9265120443c35290e8080c0e09c3a1c0a89cb0030e00808482385c002e0483ce01b2b83c7e6818890361d0117cae121f8404c340b13424373508c86690b0c872452206c6e100615c0e08181606455)))))
def chart431Data9 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x20) else (0x8)) else (if i < 3 then (0x5) else (0x3))) else (if i < 6 then (if i < 5 then (0x8) else (0xb)) else (if i < 7 then (0xc) else (if i < 8 then (0x4) else (0x8))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0xcb9732e41c80cc17b26648c12330270460ac0fa40148991520170273ba2200f01606c03803) else (0xe5ef4ef5cf5601300f00bb5ef5e007003)) else (if i < 12 then (0x46fac8b73) else (if i < 13 then (0xc98405820702b271802231f481b2f17289c0f38080b130703) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0x9cc7a18fc74b25629d411c0be491c8882000) else (0xee249f7233f5ebb9bb873b061bcb90330b699f735dc304dc77b03ff47fb08a915d70ed633ee83f907772)) else (if i < 3000 then (0x60502210) else (if i < 4000 then (0x0) else (0x23418410086820c005910a28683)))))
def chart431Data10 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x2) else (0x1)) else (if i < 3 then (0x1) else (0x1))) else (if i < 6 then (if i < 5 then (0x0) else (0x0)) else (if i < 7 then (0xb) else (if i < 8 then (0x3) else (0x7))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0x0) else (0x75e)) else (if i < 12 then (0x4) else (if i < 13 then (0x130203) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0x0) else (0x2)) else (if i < 3000 then (0x1) else (if i < 4000 then (0x0) else (0x0)))))
def chart431Levels : Nat → Packing
  | 6 => (10,5,0,0,0,8,0,chart431Data6)
  | 7 => (44,4,0,0,0,10,0,chart431Data7)
  | 8 => (116,3,0,0,0,12,0,chart431Data8)
  | 9 => (16,2,0,0,0,9,0,chart431Data9)
  | 10 => (1,1,0,0,0,1,0,chart431Data10)
  | _ => emptyPacking
def chart431 : Forest := seedForest 431 10 #[(0x765158cff7e51caacba438c2f5d33204c3655e70d5e2b27358b7de975e10b844ce04dfcedcafd7a38b58d04efe574c0004f98b3d9f23b7fd89923192ec02d72130f2603f707c0a212a106cc09f72f19dacc915c7c582cb54817bb0470423bbad,0x46881b91601938200027b00b1102109083155c604052121048d2c29334208864be18a102c81cc703094892821855882108d002bc8b03105c013203d0000bd400304260be402c0101281204c29518d01c2cca14c5c2024b448173a0460023a921),(0x90821288e4e5ff22da363ff7959ebb677fc61e52d5fffc15dbb02109c20e3341d791f60173e94ab0bb80b765ea221dd2c1bf7c61189d031aed87e20742220ba5ec2ea049f2c10ea2968c7ed58591ef1eb30cc9bb5dcdd4761d015b0de6061782,0x807284448da24412e29004700eac4104044022018f8c04a3350025244205040141455c2430a300a492a00525c02214c000257043009c01026c81600753a029a5c425814122c24a6096886b0100842582923468221dc594321c005309c6041682),(0x9c82633b06b2f43134ea72692a97d961d5f69fff01216e38bde622b18d9f20fe7d638da1aeec485a5330e380022c13d5a316af0bf3345524767cd779623250c49252db7ca92ea49deda690bf4e4a0527999acae5c668022c66bc2982eba32c70,0x79886010421010480822420820009020c2990c30000038540820404210080ae0102000094d0049504100020006480100a310890099200c000268175820121450121040088c200410080510240c58000401828004c2280204209c280021a22070),(0x4159babe2ae80dca226dedc9e0edb9a69bc7e55536fdaf6aa2239e337f75c55f6d9964a385482ec8f267c043518fd9957c8612d687e070d8348d00568d7e0de8ee5592cebcaeda6e1848e70a73e29be22ae077e82314771989a093e99ad1a04b,0x210120d14e48484e6542095440e20921d02a04b313b402aa00a9d804b61010c4e5c409010002688122cc4451006e8d558860006021050d8059408028d6008a9cd253284329218224000a30a522293c20c242be801146518092013e98a518009),(0x0,0x0),(0x67364ce4519292eebd7d0314e965e7bc69682225da4f2895775debcc5aeccfad99bc59feba17fd655cca5c390d7020aeedf05914608e9e9306e51d8cb5d5e83a0db8c63373b30f882df99100502516c354452856bdbf08821c5a45f9019cd03c,0x29104024900080889b0044048809c200506020012204280c2008010001000400408648a4020208204000442005202084e60008000000060000050c013560081000b484003b521a88002db0080025028310012812250c00000c0841a1019c501c),(0x0,0x0),(0x3f676fa5a1134295e5977bfe47eadc51c8b7e9af3bff1193594f837daf32f8d8a9faf3927a10b49ee7be35a4a09412af0a2ea259c0d030ff265b0ca4394838be5f033db44085a97743f25d31df28e610d3df1596b897dde26225b01a1a7c8e10,0x84419780216a0b142485395014e2085a0806114e11f30482d1553235aaf0b00f2b50b20010943005a23b398430131e2b182a027d40db30bb6c1200040a0820a6090331b44085a16751d24f10d3002400885c07a00893dde24221901a1a408e00),(0x18fff550790857f51365a75a0e5c0a8f2c9fe118245c1b5f6f0e9d5af2edf7e98d00f50f0d00633624053bbb5bb1f322f149f7f16e6a6c690a2245fe4edf1ec2c28d15e707a8d0633649c6e4348d3c7222a8340c59e1bdc1ba92c62431626c83,0x946a8040430901600021136812500c4580850cb0c0c010d106844048108462418121274a0130411624013a884a89112a0108b7b96d2a28230a2020e4429f8604120841630428e050b6504c8084080c3c2288900410e198c1b292840430222c82)]
  (columnTable 24 0x20001f007c080013c01d828005f0074080051c015c38014f0056080051811542001580054ca04518115040015f00540a0096800d220010e801e0800c600073200318009c8a0843a0070280b18009c0800d40005720035001154b00518105428075001150c2843a005034114604140c22c6002503803580014d600d780050) #[[],[16,82,131,100],[128,49,100],[48,129,82]] chart431Levels angles3 composites3
def chart351Data6 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x17) else (0x2)) else (if i < 3 then (0x3) else (0x2))) else (if i < 6 then (if i < 5 then (0x0) else (0xa)) else (if i < 7 then (0xf) else (if i < 8 then (0x4) else (0xb))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0x166a101f90186dc390e201704f04e080f02c1b01c03) else (0x13ac27524cb49d28002c0038003)) else (if i < 12 then (0x642b73) else (if i < 13 then (0x48030003c784f060002c03803) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0x466078780) else (0x10af337baaed40bc7c78f8ed)) else (if i < 3000 then (0x23) else (if i < 4000 then (0x0) else (0x60451c4)))))
def chart351Data7 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x29) else (0x29)) else (if i < 3 then (0x7) else (0x5))) else (if i < 6 then (if i < 5 then (0x15) else (0xb)) else (if i < 7 then (0xe) else (if i < 8 then (0x4) else (0xa))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0x14ca330c3aa85d1313041762fc5b94258c2bd932825802ac538b3147089ba2646a426c4bb5060c5219408f11624c43c889981fe222422881ec3b8830e6d82bb300a201ac33b7065818c2f86f0b65c9640536d8549b204f09615c2389f086c21b424007651810037066d89431665880ac13b0266007da6023036d99a201350805c0782f0160fc03803) else (0x2e989ada23e8a7809f026fcb4d8d32b4ca78093023c097022e2bc9aebe98aaf008301fc08701efe38fa4a69a01ce63e01be2be01ac077019e6b4d2d362cc8f805f016eeb4015e6aefa43e18e8f004f012f296fa536a498f004300fc04700ec05300de69ef26b43cead002f00aea3eaad802392f8027007f2b68adb23cfac0017004c01b003c033002c063001c003)) else (if i < 12 then (0x462b073) else (if i < 13 then (0x803005b5c2a06a270a005313c6012c5711f408003fdd2789803b0dc785e3e41a02f0ac3309c4308c706001b08268db0132824003c1702c1f01c03) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0x85083a8238017eb7d47bd7a578f77174a72f7187036e96cb6b469e68866c65463f61a6065ef5db5c55a458855f5495345114ee4d94c34ac49147b4594304163fe3e03c93ab39437435534232b3112fd2e22c12a628527025824222b20d1f21dc1c21ad19818016d14a12c1150fe0dc0c50af09708006a04a03401b000) else (0x478d9cca6bf7beb5fa1e42dcc7bd35fd722d28f9707dbefe5fcddf47c24b419a4002604ff2fcabf66a82a02f59681165d73acbf562a82cc47ca529a0b803cdee237bdc4ddf3538345b3370f16495ede85ea4f33d6fb07a34752275adab647566e86ce2bf94d558db874a1cf030d04fb0fc85b38a3df0bc7954ccc7e966f75cdd76fcdf700a5b63fcbf281571165c24c26394a6accf0179f7f37630b29d1abac8f86ada17af7a5ea77d5e3ba178bf97e55b9d89381c5a75a0a5bc7581d9b33e55c44cc4fa0a1352128f9fb579bc355d571100dc17fa3e40794bf4c4ddd5ca6af14c72da4d9e4ed3e8f97c6ab88de219bdf4ed85485b3a83d76d412ae236c4dd8f170c5dfb3fe82e9cb2da940ff7)) else (if i < 3000 then (0x32304113223303220224323003011453111330340) else (if i < 4000 then (0x101080) else (0xc8323c1e01c60231a8e42835130b440241b8484a1b180b06e1d1503c00350b0882e150f8bc402d0403c423b030b870311300056221c8506a0e108bc582f158c04a2c160fc40221b0b46207168281228188bc3c14098fc5e2e1e0d00a32)))))
def chart351Data8 (i : Nat) : Nat := if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then (0x31) else (0xa1)) else (if i < 3 then (0x9) else (if i < 4 then (0x7) else (0x7)))) else (if i < 7 then (if i < 6 then (0xb) else (0xd)) else (if i < 8 then (0x5) else (if i < 9 then (0xa) else (0xa19843306982ec5b95258cd4a660af1562cc53d109109096209f136a092009712628c47ac860821c931426881fe002c00f620c3bac2604d401006f0d698aaa0670c61cc2f88b0b651a1126450814c27b286491982384b086521a003b68c188a2037066c01a12600560bc13b2c04607e993066911100b81364c06c0783f01615c03803))))) else (if i < 1000 then (if i < 12 then (if i < 11 then (0x1cbae5b7ab013e09bf5c6adb53c097049f2f397c08bc5f6af010e08f04181fed7deb6b5d7ad3c78077039eabbd7406f035819e57c07b031fa7b47dc9ef177a9bc6c057029daf009e05b025d8f3d2de1eb5a010c07fe8ee5700dfd6403b019eae805e047015fabbd39e3af55008c03fe3ef4d006c02febc009809c01e00bd5f017c00e003) else (0x21409bc4b31c83)) else (if i < 13 then (0x703803830d90039382ec342dc502ccbf2bcb07e1d0180a028ca727c806011025e0024d5023c906c08b21c9b20cab1fd30480f0500771cc6f0407b1ac30101bc5803c7005f16cc015c2014c4f6806312cb47f1e06e0430fcd00ed340dd000cc470bd70842206d02708df007c1b019f42e0130281703c2b02c6701c03) else (if i < 100 then (0x1) else (0x228189aa25488f621787e21d486f61a68636173856e14b84c611784020f0832a0b5827608481b605780ca0157fc9fda7eddfa17e09f6b7d25f327c5def57b79ec17a89e777985e357821de6773ddb3764dd7d75a1d5074d9d1c741dcec7355cbb7241c737159c427081bff6fb5bd66ed1b946dfdb676d25b296c45afb6b4dab86a41a796979a4668c1a0867a99c966ad996660195a64cd91864018e563418af626587d618184760c981d5fdd7df5f057aa5e317705d257315c6d6f85b8d6cc5add69c5a0d663593162f58515fe57a55d356e55a2562956a553951d540d4eb53514b5528547f519545050bd4114fb53d44ee13a04e153604d293304c2d2eb4b252b34a652834991239488120d47891b8463d17c4555140448110943c10c542b908e41c505640f90234034feb3f54fbd3e94f8a3dc0f593d04f293c34ef23b54ebf3a9ce9139ece5038d4e21382cdef3714dab360cd70354cd30346cd0433b8cce32ccc97320cc67313cc2e3068bfc2f70bb82e84b822dacb4f2cc4b162bfcae82b30ab62a3ca75295ca44289ca1127c49d526f09a22610962250491f24088e223488b72278881219c85220e48241ff07d41ef87a31e387631d1072d1c386f71b606c21a9c69119f0663193463318785fd17a45d216f45a416005691540526141c4e7132c4a71244476118444910d04170fd83da0ef83a80e383760d6033f0ca03170bf82eb0b502a90a442770988245089820e07e01e107301b6067818605a415404f012304180f003680c202a809001d004a007c000)))) else (if i < 2000 then (if i < 1001 then (0x9a5118fd88678f6971f9a38a044c925d1dc11c6b293bd00ef6e2a60efe84fb2d7ab29c037be225ea1def9ffebbf655ceffd499f59d645ee52e717e596f71e30ea7acffc1dfcc150f9f9a15d79607a70f48ee83bc985f0775deb67cad1f09b76cfd2eb063a77fa1635f32dd2dee153da0bd9d7633eb3ec6c64dcdf4d62a3a9799fd41a0ee216a22b6d636a2e96d3f91c8c64c3ef0f6ba672ad659148c7ee5efe5ad77faae77354a3bcc6f85deefc647706bb388be6b261e7ee3c994ed8770199439402e50fb2072e3353ee7c75601da4e187f98972e53b66b80bfe9f7e68c987f890fbabe1b0e2cf4fc69fbb94684521e6e3153e4713f4623ad0bffd121e15e9598f0caaa8752b3ece27ee7045a5e6e498ce6effc5bdc075930afeee5af6d957e75a23d17870f87112b2101b13c02b7d762731e4b6ead56d0c9ba9fd99f3a93f5688fc5efe5186fd76deccde3e9876f82cc99eb331a21abf49df47295b53ccf6a378717dff6eef2e99ec0ea958d97a5ffd4f536bffe85ec4264a4de58df6ae4b4b49e86083e259719cbf772cc34b13db83f6792f18c84f4c38beb8a595379ac66a4eebc7fa23f600ec277d0fb871909ff0f6b0ca4617ef72ce3571a5afba131642ba7fb02bbdd9dcef6e87ebdccebd1142ad7796e4200eb2ae78c99df06f20f5f57a3e8bf16f69875f550cbfa4b3ac1dddd88da2dc54f75c8fb26d959a3223dfcabf31d13f171dc23e8cf6c53285b1336890d22c70db08e7f5274fff4326c65ecc8afbf3d747e2255a378795e423a0ee82f3a535c7bdfc02fbf14cde2e27ee70d2e98df086dc27e7b3748745393ef51afd5b1b9a9216ceb334a54342117e7ec5077a639732677700bde2858a21e792a745b2abaa31fb6e11d4acccd0145b7168060e8f59f18f8f36ba3ebb812e3353ebc1dda2e3e52f8ca706a15f41a38c1df2c03bf05fa33f63fa43b9bf997b9e82104aa719a93e11a0916dd17abfe3375ea6533ff39ea07e57f7b3a93a6b25ed902b8ff45e1c1a8ba5a2689da8469c8d34077b3837017cde9618696e6d10cbfe2d4474fd2c883af2bddcb19f56ccef3d7b99e86fe0af71f0a930dbbf292883b23863517b9579b8d9a7d246e867cecae9aff3f64d39319fdf46ee9b47faaf88e568ec936dcfdeb89f9d805af703ab6bb3293bbf5212c0cf46fdf70aeac34be4aea77d9cc8951205e180e3b6f77e7fb5f69f1b7dbb46ab67abfac9b753bf403b35d5ac679a4c9ed4d8133440b9ac815d9c6dd277770e297db003ef6c1db8ec7d4c8d1bc3b461322e2adc1bcf64c312ce518a21bdc425389fafefa9dee67988cf6dae0cfccfdb8265f9d02329c1b03af26176a4e9afb92928ee95f34726ed1211c786d508bfee6e2396067f1bec99f5b66f4466b210b3584e49e612ef26167e8ff43956740aaef2da39dea3d7f5aee93011ad117) else (0x727d94eeb352645af21288c984d1f92d357af5a56c138b3a69dcba93a6de7fde3f4afc7ff2a819a624ef9c6c8f902df41ed8549d2df3dc0fce377e77edc0bf9ddb7d6c499cc8917d225ce71eefa59b00eacf513d94)) else (if i < 3000 then (0x4131431341271112232122012301311020223235123115014033321651131112334402333340231442001231220101604400114020203203300245022223101101113325031400041432002501420c122) else (if i < 4000 then (0x4fe35026faed20772f1145000) else (0x585f03a1ac2846d0bf0d818c6d8e01062ac570880b03887b0b00c4134088440b4130390181da2bc3f0bf0e43b82a0f61fe0e46686b05a2ac7686712a218220181a214c3902b1c8098370f81a6220288f41e626c3d8ed1183e04d8050e2378250f800c1680a8cd06c14c6580c0a20101e0781101c01e8831402bc628bc1721d84c84505a2187908d01c15c110361341b87109c0b604c648b205a318780ca06a1240909517a3800901c0f037815848058064018121823e47d8d816c190058981b41ac1886e11e2d4050821ec1a03c0b81902785605f01e37c678600b6078520df1a8258620aa1b61640a0e30180ec4e88f0d43307f8051221e4170210f6284488130501c02b8591aa3245804019c0302d06b0fc184458e30822382d89005c050198a91cc16c6f82e03e3c02d885050174270fb0a2010360a90d80105c81e0c00e85108c1d23644b83e1963dc170661c20600b85705e184530af02a2283c07f1fa1a07a027126184200a10e01b8738c116a3a4280f403611c790e112a0687a04d14406c090b30a43885e09a19e02c260d905c3e00f0350ec1c04787c17c0807704507e314460bd1562b0238dc16c1c8388350d2028360bb19822839822)))))
def chart351Data9 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x37) else (0x17)) else (if i < 3 then (0x6) else (0x5))) else (if i < 6 then (if i < 5 then (0x1) else (0xb)) else (if i < 7 then (0xc) else (if i < 8 then (0x5) else (0x9))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0x90a6630480020c3f9266481ec3bb286610899606f0d61cc33b268cc9029905f0b6b014126491014c2785709618c23b080c4a101003f076c01313025880cc17837056b09642c64c008c0fb0650d4422201702606c0782701610c03803) else (0xeaecbeeb6e3e01f01babe017ebae9eebc00f01300bebe007003)) else (if i < 12 then (0x125b42af37320b33ce3) else (if i < 13 then (0x882e341507f3d960f077399bd40f018018046731a40be5b14320e1102814c9f085c37200472192c7e681d95c6e6b19880102b0809c70fc11a01381f0d8bc2ef80e061300f0584c0e03) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0x2df59caeb58294d099c533e4f47a8cd1461d41e7f8f51dcb996eed559cb165d4b2d5327b4b89110d1f83a06c8c115624a4487e0e519e2c04d0830cc0f010000) else (0xa7e4dc4e763e951dc7f58ee2b400119f598777e57ae34d97d8fb68ab9c1fa5f771eb7bbfab02da60b5fb76e4ac9c4f70c0faceef8b3fe43f89f6c353637a3f4d2a99ff42153ed962b7454352d19dfe265532fd62551519cb8c4f637998854546de3fc22d77768d35ff23365fa72ff3532ce312357d739d076a6e764c31455ce780b745ef50d35ddfe42a2733f1af2b160c56bebee55b25cd50e150d184807c394cef3dce5be49fd0e04f89a7de640c4f2bccef5b3070f4fde8f09)) else (if i < 3000 then (0x13212210420063025312240) else (if i < 4000 then (0x880) else (0x3a35138f8600a0a864300d080a0261d1785414130e0bc321e06068360b090c02e380980418051602800070282c1c05188907435)))))
def chart351Data10 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x5) else (0x1)) else (if i < 3 then (0x1) else (0x1))) else (if i < 6 then (if i < 5 then (0x0) else (0x0)) else (if i < 7 then (0xb) else (if i < 8 then (0x3) else (0x7))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0x0) else (0x6be)) else (if i < 12 then (0x6) else (if i < 13 then (0x4cf81c603) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0x0) else (0xd)) else (if i < 3000 then (0x1) else (if i < 4000 then (0x0) else (0x0)))))
def chart351Levels : Nat → Packing
  | 6 => (5,5,0,0,0,7,0,chart351Data6)
  | 7 => (83,4,0,0,0,12,0,chart351Data7)
  | 8 => (323,3,0,0,0,14,0,chart351Data8)
  | 9 => (46,2,0,0,0,11,0,chart351Data9)
  | 10 => (1,1,0,0,0,1,0,chart351Data10)
  | _ => emptyPacking
def angles6 : Nat := 0x3002002002003002002002001002003002001002003002002002002002002002002002002002002002002002002002003002002002003002002002001002003002001002003002002002002002002002002002002002002002002002002002001002001002001002001002001002001002001002001002003002002002003002002002001002003002001002003002001002001002001002001002001002001002001002001002003002002002003002002002001002003002001002003002003002002002003002002002001002003002001002003002002002002002002002002002002002002002002002002002003002002002003002002002001002003002001002003002002002002002002002002002002002002002002002002002001002001002001002001002001002001002001002001002003002002002003002002002001002003002001002003002001002001002001002001002001002001002001002001002003002002002003002002002001002003002001002003002001003001002001003001002001001001003001001001003001002001002001002001002001002001002001002001002001003001002001003001002001001001003001001001003001002001002001002001002001002001002001002001002001001001001001001001001001001001001001001001001001003001002001003001002001001001003001001001003001001001001001001001001001001001001001001001001001003001002001003001002001001001003001001001003001003001002001003001002001001001003001001001003001002001002001002001002001002001002001002001002001003001002001003001002001001001003001001001003001002001002001002001002001002001002001002001002001001001001001001001001001001001001001001001001001003001002001003001002001001001003001001001003001001001001001001001001001001001001001001001001001003001002001003001002001001001003001001001003
def composites6 : Nat := 0x1000000000010
def chart351 : Forest := seedForest 351 10 #[(0x2e250682d5e561d27b030b26a4e64b596f3a49bb75cf5bc6569ec7bcf31667dac4c31f6a99bb7d432a423b82825d6580364ebb11de4c670e715d18bd9a6bebe11d96c5e0a0c0698187c4270d346e43f5c9da3b9b1598c0a3243c60c42f3f9b71,0xc96840833884c4428ab212212f05060839120853a19240205012b31c311c02cad48a462a908878436a402920020126802214d2409e08211a114000c7d008eb003d166660a400284010802721243003f1c9883a1b07904082240c40c42b3f8961),(0xbf28920099058fa89a4aa27be6dfe07cc837fc20e66aa89ae039cb8216e7a31fff858c97667d32a80a4e233b3dc814d74ca2a7b181a0a6e135f7f06f0fb590a3d6c02d12f98bc3686a50874527a1e96ab209cf697846320120d5143fcc953e0e,0x40210100302090800004046804250000025108804288c9d00884000808051002005980101230200000a02013060001c45202414214082400087b0000f810023c0c00910580ac4042a40000400804808222081005840120100d014138480120e),(0x96e91535ed4c2d9742d0a4110b8050e483c5f74c2df49100b5f4eef332bb966e96c57e75dcf802a114903dbc4c8c98735061df870e26bb860e546fdc76d4bd188a3fb2d97d1899382497a5f2075eccb721cf8c1b16e621a0e3e3aa21f33b80e0,0x13d84d090c6c128250b687114890800506006e5061c0710043348586591982be9a6220645a1000a41004113c001d9841920589018a27288686580bd850548a181b21b2c927340130009691d2077a80b201df0c1323a621a0a321aa20733300e0),(0xc03449b7e6dab1ba66dc5eef3a39a59628f72e1728f19fdb3bc734d983dc9fcd8fbfe8feab48e008f799e5465266af662523506c6fb411080c818694580b933ceee35c3ae77e1cd0d5ab703aeacd6e91d726e2408e211e8fcc0e9991104e84cd,0x80200040b18161540a000800222102821818100400100211a0803019a2e01000240944108080e00ae281240210000712052250240480114801010404080a1105e0404002800930c215092021280442010820024000011a03400e0191004c8401),(0x2c5736d60ca010d0b95ded3e70e8e79fcd15638a05bf47fd047f756d7cda0df2fb7833abd597c746793a5ed97d35b0ad2bcc810a30fae4a6c6dd8ba98049604e28cdd9fe1aea90a9c32ef00a3a0ab8852cd25792f0aef43e12f87f403240303a,0x34908e3c043212a07540604c508ac935c60161a81025058c05400062400305100b60b08005120704111ac29d6d34802808c8011a20600c84c4be832805c500080088989d12f0c018c2349808130aa80424124584b82ea43c12f03e001000301a),(0x0,0x0),(0xc3f2b5ec3438ea5f8f324339cd7d192c52f9c7f5d315b4f8495b853a0e25eaa963cba679f484d8bf76f51301a9865488dcff5e22118b287fc6a2811ea1621d0e537c36a5148133d71ee1d89f6510919b77186cb6e51b4378930b068a39e5e542,0xc94002622494b2148a912ba171190aab339a02204895106020630d0012208084009244a0e0849102e61411088884908090ce5228088a29329420041e00321400121c76a0848133d31405511b6900129354145c04258b4168900b02883945a540),(0x0,0x0),(0x62cb7d492eb669a56720d4d85d897d4abe9d965d92455bbd5e5ed03b8dcadd3a4e028a2cfb04ba75a3298aa5966a436dba983cf2c47f189ec2dc21a1fb8f8ed8c139138d5a442e0610690ed0d493bf1ac7e22d754951ad501fb09ed443b24305,0x16035808086a00aa44204018880635400005a41ab16a0080421c42664c1a4c184a64ab08033004250022cab4246a486d2a100cd2c275000442dc12a1e385c2c8012189415a448c0428600c000411ad60834320304850a4100fb09c4442b24204)]
  (columnTable 35 0x80007c01f020002f007a08000dc01e438003f00780a0027c01b020003a20688a020e881a04000bf006808000ba00e820023200398a008f000e128028f002e0800a5000b5200298002cc800a6002b238029c002c4800a3020a928068c082a0800ac000a72802b80028cb000e880a23802ba00288a08a3020a14002bc00284d020e880a030268c08280a080ba00e029002e802a0a00a5c00b4280a9800ac0a00a9c00ac4002b700290a10a6002a2304a9800a81600af800a0) #[[],[128,49,100]] chart351Levels angles6 composites6
def chart191Data5 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0xf) else (0x1)) else (if i < 3 then (0x2) else (0x1))) else (if i < 6 then (if i < 5 then (0x4) else (0xa)) else (if i < 7 then (0x10) else (if i < 8 then (0x0) else (0x0))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0x174903a8a901b05ea2eaa84a080f02c1301c03) else (0xad10)) else (if i < 12 then (0x0) else (if i < 13 then (0x0) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0xf0) else (0x2f39af03)) else (if i < 3000 then (0x2) else (if i < 4000 then (0x0) else (0x43)))))
def chart191Data6 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x1a) else (0xa)) else (if i < 3 then (0x5) else (0x3))) else (if i < 6 then (if i < 5 then (0x24) else (0xb)) else (if i < 7 then (0xf) else (if i < 8 then (0x2) else (0xc))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0x36a2e8da1930570a65094104f09611d20348694cb81f83b2a4a9151037067552bb3527100ac13a84046651c501b324aa1c101702607c0782f01610c03803) else (0x6958d271e4c3ca800370067b4c2caa7158b26800ac013802f0047c4e28bc417a9ab0006c00bc5789a70003f6a800130016007c0038003)) else (if i < 12 then (0x23) else (if i < 13 then (0x8c06c024050002301f0980a801b0170881c83c010000f00b013007003) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0x1ccdce971b75b152a651a813a5acc054238ec5c228b83400) else (0x5ead1b61ad7d127f73daaa88620fc3665ae36ffd7b44510a6dfdfb7fcc712b6a24c0d195014917908f24dfe7b6f9c7cddb3d13a7ec35bfcb4e8c3cd)) else (if i < 3000 then (0x1233014322) else (if i < 4000 then (0x0) else (0xe1c0c68f10384870e1008f0a2800c0420083)))))
def chart191Data7 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x24) else (0x33)) else (if i < 3 then (0x7) else (0x6))) else (if i < 6 then (if i < 5 then (0x4) else (0xb)) else (if i < 7 then (0xe) else (if i < 8 then (0x4) else (0xb))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0x2a04c02bebb2a65d02ac53aa4146d895409b69427c4b893480549a43524c45d0438832494c99207f0f622c3bb262841bc100730d623c33ae0844dd25505f0b65c82b8536d4b9a4404b8ccdb9b3047086cb81f84f077112771445000cc179404840ac13a820460dc0fb646d005eaa2a250804c0781b01618c03803) else (0x3d3091fa55af5400af02af54ad54a13ed4a80a3027c0a7026f532d16a15e94e8093023ed58b56808794f808b020c09701fe55ee56b17ab5c007701ce574e4ead74d46806b019c06f018c07b017f15ac4ea17aa5e8057014f17cf4e3d34a57804b011c04f010c05b00fe93ef56003785fb978b5e003300bed3ab4e3d54009fd70008e56e95eb43aa5f001b005f974004c01f003c02b002c03b001c003)) else (if i < 12 then (0x684f2b073) else (if i < 13 then (0x90800e48c0c92200670c6781221c082816c2b85f0a61ac27b80328b020c0470860020603f0760a1400e02400cc1783705612c1398c6c007c180403301200b81b0262001000f01608c03803) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0x98697295f94d9359148f98e38c08a488a87585f84583081a8037ee7d77bb7a978776f75b74572b7166fe6e66c96b76a668c67064f6316196015e45cc5b759f58a57455f54953351b5034e84d04b94a148947345c44643141a4083ed3d93c23aa38736f35a34232b3163022ea2c62af29828126b25423221b2031ee1d61bb19818115f14913612010a0ed0d30ba0a609007805a04302e018000) else (0x3db11bfdb3471b81cb746291c973c408e4b6ab3ab56e7478bb81f970ac5dd056ecf4efd6aa3c032056437476dd05d77416cbed5db29c703238c603e5de3f875973ffe1ca2bfdfadc8d559879d9eb5da7546fe327f7d7b44ad13f87ca09e814f33a893f3470534e387c29a7e175a7f3a94bded4c25f893c39519fb967e9d7b790bd810f86a138ee4b67b92d2cfa5868efdc7726f6bd455efbe9ff87e1e1acf4a31e74c3cf9144b195a97c8a3db13328656394ebcc98ef76d8e355592fdcfc843f6279fc5bb268fb2b4618f34535769e33feed3e46165295e31809d4c34741db9de6755d87aec4cdbb51276d8dd82aaaca5bd45c1db9d5e5d79c5c42625bf88cec4bd7ba0a6c9ef97fcbe4558c84edcecfaaad4fdf1cda7042725893b12f41e0f9f22aa798ef77c2eb0e54581e3604dec04b867661)) else (if i < 3000 then (0x114211027044216130154013001032112221122122125025116) else (if i < 4000 then (0xc0f5100) else (0x1284c1c4740781d0147116c34154711301e0583504c3f0407b03c2e0f07f1847d0302e190041c0411b461180720a45c0d0220cc781b42a0e4100a0270c02a008550383f1b4731dc521046c0701b14c1c07c1c17c5316c330d460120760f05412c6215846198250847819011020510244b1d8771047a138400dc7e1440e1486e)))))
def chart191Data8 (i : Nat) : Nat := if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then (0x45) else (0xb0)) else (if i < 3 then (0x9) else (if i < 4 then (0x6) else (0x11)))) else (if i < 7 then (if i < 6 then (0xb) else (0xd)) else (if i < 8 then (0x5) else (if i < 9 then (0xa) else (0xd1950284166d49520af15654a110a354429c4fc664c8c904bc884c4d281008f11624c4389b1075519334e4c13ba550770e61ec37b2e888d10a2063080d08a105f0b615d542e648414c278670961ac2387f086b917003b65100195037066a98a012405609e9902f046a01742e269006c0b8135049000781f0160fc03803))))) else (if i < 1000 then (if i < 12 then (if i < 11 then (0x64fb0fc09babe75d32ec097049823e2fdd7cebd022c10fd6ae3d01ffab407bcbe65bbadd95eabd01cc0de077035d5f80ce083031f4eb8fc05bebc015f2f5d2ea9d71baab404f025f47ba6dd66e2f010c07e04701df1dbaac033eae74f38f802f01580dc04fd76eb6007fa7dd72eaf006c02e023009814c01f97e005817c00e003) else (0x320ada2e09bccb11c83)) else (if i < 13 then (0x805e100660f33bc0a3ac14180e3018e737d90580d7041d0442b0980cf32c0e7c0c3900c72fdc0380bb2dcd32ccdb2bc50062906025028e8427c9b880c82c2885d09323c9722ca721c30540831fcab1ed28801b01cc6f08194480c04906718c6b17e704c20c3305714d707804f12ea034043280470fe0831204090370cc3b0bc400ae803c2106823007c2306c17240131c02703c5b02c7701c03) else (if i < 100 then (0x1) else (0x93064ab924e46f915e43b906e4058f4a3b48e6637c8d5e33b8c8630a8bde2de8b122a98a1e25f88f621c87ee1d8870a19185ea15d8522134846a10683b60d683020a5823e078812203480720027fadfc37e9df917dd5f607d1df297c5deff7b95ece7ae5ea17a05e5378f1e1a77c1dd676e9da57635d727575d4174a9d1473c1cdc730dca37221c6f7161c3e7099c0e6fb5bd36ec9b916dfdb6c6d35b306c59af86b95ac76ab5a9369e5a516895a0a67c99da67119ac665998065a195264e991e64258f563618c1629988c61e585560fd82860357f25f697be5ea97935e017525cd571e5c196eb5b496bc5a9167c599164058ad61958155e757255ab564557e557d5365465503538d4cb52c54995209468514d43b50814074f953cc4ea53984e0d36d4d653434ca930f4bc52d14afd2ac4a592774965241489120c47dd1d747051a1461916d455d13a448d0fb43950d342e509c41f1063412d0193fb8fd33ef0fa83e38f6d3d4cf383c88f0d3bd8eda3b08eab3a4ce71396ce373880e003754dc136a0d9235e8d633534d34347cd0b33c8cd63308ca63224c70313cc353080c0a2f78bbe2e84b8b2dd0b5c2d14b2f2c50afc2b6cab42a58a852988a5028b0a1728089e127109ae265097d2584941240c8ec23648c1228488a21a885220dc82220387eb1f287ad1e347731d4073a1c7c7051bc86dc1b206b21a6467e19a864e18e861e18285f617705c616cc59d161056b154853714844fd13804c912cc49311c045710e841b0ff83d20ef03950df83650d1032b0c442f90b882be0aac29209e8263092022e07a41cb06c819905f8169054413104600fa03900c802b009401dc061011c02f0064000)))) else (if i < 2000 then (if i < 1001 then (0xfcd6b9d2465ec7fb4ec6bd783186184113f8c8db4a85ddf629734eb6c207cc0b2f92dabee650fdf28fb8af892deb748813b0b16e8d3875750deb0ad8117f36377dff08a30789aebdf8ebfd8761cf7a6de5247138fe1e32ce3d4efbdf293394db7beafbd36b943d87629734f8600478f394551cdbcfb5950effe05ac17187971f9a68e2f91abe5c6dc6fce44bb197f6c6321141e779acfa66bbcc05e230ee3bf8adf3668bb401f819f513085d75d086723412d036cfe05305ceefb82d3844b1b11a4025634c4344d1514d55756c3d9cd7fbfc8528dd115d5be1a7439eb1303ed6ea96627deadc172de54f1eb5f2736f46879319a089ff526b75938149bac88698bd45a32732e3bc141adb1243449fa6832992c33be5249c67d75fe6b0dbaacec178ceac97a337ea197fb896bc8298ef34f65184bcfa0b7dd8042ca7a106d6fe83ce67339d8b763971cfe56efe59f9f6f456d8b4d06b2f5bbd9fd9cc6982a6de5e48f1c47856ffe4f95e96c80c7f29464fce555b4adbb7d7e52f9caf6a5ae7d4773c5bea4aeab2ede027c3f8d6dcfa92b7c816de4cc0ac4671a62244cfa98d8f0390bd107199e1f7ea1d4941c19c0e14b9b46a52eca7bd33f171ce650eade7c4322d9314b9bf7b39864d50f7a3bac66316be502867890f3a049c7a9d42bc3d1bde5c9b7ffe7ea02704077011855d4f9764b5d5454328547afd998539def8be4b0cefba6d657b0f6dbd8e8a7426ba2f9bcbd717faf932bc4dd71c4adeefe04aff4f7275f639aff605cfd6054fdc4d5c4b859d0122b7e29cd56f196edd8cd497bb2d5fd3c6efb96d6d18370fe0f112d84230047138ff82406bdd7bcfbe38a56f662d63e1c06bd4fd851c3d8ccf052ce6831e2f4f14b36f36246aff9f0243f7caa175829ddf7459bd5dbd2cc4fbc380b187cc5699f288bdd6b79f53bb69a7ee9f18973100db21c65decc047fb313fc4998920a86c18c05b74ec986dc82135fdfd425f525eecaa85d75713a0f424bd195fb8957afa1ce619a7c0f9743a2e36f78e9de7f44a996d39f61367ab94cf21db6ff853bbbbf0146a575f1f94ab11819bd307f6266d3cc62df73da77f17520eba40311ab3e4ea0b7dfef323257baf0677cbaf1e990fea5d66b65c536fa8256f8314e5b7bd8bd912b7dc4ea11ccfabd633c8d3cfde96aaf5efa9d5bd8507b0aec219fae44adfd2ce62f1a730ae7593b7e055f873fa575d90f68cd3fe0abf722eeaaea59599d33bfc5700ef66134aebb3c099aedb027552fba64242895978546f7feac46e112ba97da99dbe19f28c5ac35eaabf9759f612cfb946def616d9e07cc3db3c7e98e83d38be3da9d352c492a17ec9e614c3bf7612ceea98c54e7ad65142e035eb459392cb90fd8bead879de2d9f9ed9efe990881b0aaf681fd8f679158d569cfe5d7f82862f92db3054ddfd4dafe5ca1e) else (0xb0aaf73f4f249dc6bdf59b9791d3364b66a09ef93342bb567a8cec30a6edb9def857e081e769ca339626ab36f24decff3af730c632ffc6dee655cea101d7f2ba3f0d27b8e812070a2b9af04f0abf0f3e8a6eef599323738f923aeebfe9766decc695c31c06be373bf5b295b4dc0d536c0cbec5b60c6fabdfc5371d6a25a7f4f3252311b69d2059f51cbabe459b0af6639dfb9f7ca03bc89e5fc9a5f)) else (if i < 3000 then (0x22400121415630213201411143203451514210630311022131113042221201434050301010124140125121510150204230232321303111323101401140312342332113013220113443516320023114411141223520313131) else (if i < 4000 then (0xb04fa36fb6eb0d4685339244200) else (0x1ec131cc20140611ac411842714c4f1786a1042b1fc0d17c330a4171f06a10062144780982a1705418c511841906031118631287e0d8721e8641a4120302508c2115c751cc0c1545b1fc110c047018170f0671701d1c0550507d0f003104201a86c0c45a0d02912c270ac680704714c6b0f01d19c69120751245800019164170245e180620ac4d18c510387401c7c1e0670200a1906612c081e40b13c1d1947e1106d1cc5303c3a0701d11046140151c07b050061a44e1144b0f0680ac4c0d4610903c11413024151907d0b8171301b0f47a0441803c0b1a85e1fc0a10c420cc081600d1585d070721ec16180770343617441108170b0230ac4001861068701206e0602b0387f150221f03713038180560cc750ec031d47c03c6a078190e029124760f8300047803041080660983f148670d85d0942c1f0471e83c0bc6a1607d1b47f0fc1f1f06419c341e40b1c0641304416064040130680c09c3b0a0590cc030a4091f0661bc361480018c2c11823054070b0521b05a0f4611d46c1cc1b1ac7a00c2d080261c06f10c5b190131ac6f150301a0081340c1787c0fc5001c75078771e04a1a84b0cc4e0dc701346612032090241fc130f832)))))
def chart191Data9 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x37) else (0x17)) else (if i < 3 then (0x6) else (0x4))) else (if i < 6 then (if i < 5 then (0x1f) else (0xb)) else (if i < 7 then (0xc) else (if i < 8 then (0x5) else (0x9))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0x13b97426484420c3fb2a64c1ec3bc44a64a899706f0d61cc339245049020005f0b6ca1922a850814c2785709618c23caa0412217203f076a91312e68cc0cc17837056a015026048408c0f8405c0a997101702606c0782701610c03803) else (0xd5ed6ed76c7e01f01b97e017d7cd3ed7a00f01300bd7e007003)) else (if i < 12 then (0xe333e2a41179bc8a5ece3) else (if i < 13 then (0x3c240e03d9de00730c1be892882009286731a21d0409816cae5f29819004b1419160472193c7ebc1d9ac6e20240bca02b540e0c0230409c3e330db60194009841700f0585c0e03) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0x2c7d68ab150697d179ef34a58c8c8bf0e60cbf97d2f15d6b7a6c0cf9953085a2af54fa7c4a8911152023ca71cd31822ba4ec910fd1aa2b4430680900e00f800) else (0xbf9ebb878be8dc1d0e10a2d2bc43d9e471383ab404dbde19fa6dabb9a0f6eb7ae9f7fdaefa8742ffeb2eebef82f42d59f6eb527313dc78fa86fe71eee1e44e0a85983a885bab32df1f0a7991ba8f64429f0b08f637573869dfc1aca763a8d8f8f847a159bdca5b7d39834b6bd4336cb1a8ccd2f974f91af94b70d96077435e3297f54e3ddc3c12d836bac19937514695e22fc4e35dc3bfc78427bb92fa60e696cafb1bbe87bc863dd1527bc8d050a398fac54bde4490f)) else (if i < 3000 then (0x24023022121431424102303) else (if i < 4000 then (0x840) else (0x4161c0005181a0f05011908160a061a171b0b1f15000c0d1703051e110b08011f0f071503090012131d1916010c)))))
def chart191Data10 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x5) else (0x1)) else (if i < 3 then (0x1) else (0x1))) else (if i < 6 then (if i < 5 then (0x0) else (0x0)) else (if i < 7 then (0xb) else (if i < 8 then (0x3) else (0x8))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0x0) else (0x57e)) else (if i < 12 then (0x6) else (if i < 13 then (0xa05c070403) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0x0) else (0xd)) else (if i < 3000 then (0x1) else (if i < 4000 then (0x0) else (0x0)))))
def chart191Levels : Nat → Packing
  | 5 => (2,6,0,0,0,4,0,chart191Data5)
  | 6 => (21,5,0,0,0,9,0,chart191Data6)
  | 7 => (102,4,0,0,0,12,0,chart191Data7)
  | 8 => (352,3,0,0,0,14,0,chart191Data8)
  | 9 => (46,2,0,0,0,11,0,chart191Data9)
  | 10 => (1,1,0,0,0,1,0,chart191Data10)
  | _ => emptyPacking
def chart191 : Forest := seedForest 191 10 #[(0x96f2c645ff547fcaf15c177c4f48bc4d95263669bed3904b7b1ee1d52ade68a4ec0334f230fa9f24242340a9eebd0a31c23bb79bba2a30ed735a0d394e2f19f45888dc6c9e09a08809a62e88af107ed5a670a82e379240945a03fc879996ac25,0x800400800c8100021080056109c10500213a00200a000802ca6040341048a1b810206010101b442402c000089d0021200c80188822000c40090009620411e40002c8490601000001040000a940100586608826081240904203908300068821),(0x98052246d2f9e585cdd2313a6dec2e991ff00e55f24ccbd8df2d161ac22465e7f72cc8bcc7dca4812c4e13c430160dec0c98bfb9a39e49ca2b6eefe538e3ee907bcc6720b139e9a9f47815a105119937d98317bc54a9be010b39481379783e1a,0x890663321611444c51412d78944224a03c8080648160cf21510014918108250446af818b88c3848908cc024430008d4815533dc4608c4940a942cf6004e1cc1039cc0520b118d1699219958004110d32498b108850a89e01093848007958361a),(0x48e4a9af3ba9c5350d03d885384e8396eb9d4346440d2093a3bf9f5cbea09ffbd22eef0c1fd128e58107fb1a5a43656440408b3d0dbd4c5200b6c0d2e958222fb76192dbed97cb15ac29212f2aede3f0b86f5b4619616c54278c2798626583a1,0x60008800200a08208032d00208840340812904000c0100008214000800f0026990000004140020208121010806c20002400082090401040204240010a80c220c002092014c850e002020002f10a8f24090240a42284160540200271802210121),(0x26017f4f6a0225e645e1ffe122bdfb237cfa73a415f9fbe52cd7cf04fd63f9d6c3dc84706d18704299da3c952b5df46d3dea618458d2082c68b1f70740a150118d96f5eac5ad3f7619d1db14f06fa39004d7bce98e648392ec7342e2528293da,0x2010c4d85423c153010e15a20910a73012c208011c423930c26f74f002158248108610a0281043489638842814c5643cfa2104b812880c401975024021d510881e09e6822221541901cb10a841019002503421042082826c7340e2508292c0),(0xbf4d956a253216caece767e60ee15efb09ce20e8b37357a2e5d16de2f9132b34bbf7bbee9246d08aba49675686da9a999f21c64243c158b72c23fe5cdaa859f01472a51259e855a735d6c61f720c8e6a2a3843a3f3c73f25d05e1d688e00303e,0x7211831a25a21c26ac4800c208d42a5881c400a312e12982000110880980201c0786498302424088914003509640129003014642478027b22c628a0498d802001460241079c8168b04d204691604ce6029084380b3c53d25900c0d088e00201e),(0x79befed8e5350b3833591d0bd71717aef35ddcb31ca63f8c561253370bffd39123146ccffa247f3dc7b91861f3260ad2659629c81003a731f424ea409f8f8617b25439c44a40a0c6db35ddc1d4be442e5dd1ff53e19cf8ef0130e3248faa42c8,0x9a2062c260123a08504d3782901404c2e448052315847c80943007150b62005e44644805c824640141a9112172420ac2459241c000052521a520f9400c02e21b926030045800a095c8339048542e450a10156381210c284d013063248fa002c8),(0x0,0x0),(0x594ca8b067ad54d7224ac807d87bf437ea59d81e4619cf2e7b43da2fd52b27b82a052b55d42546dc52d4c06e2931a2fbeced1872a7fb8f12c453080fd3b19d8ecd650a93ecde5042d31079d20ba3086ed1e8e61946ba956b30e6098b144f5451,0x1c510300fa004c50a00081d012370241a92aa88a04a00086909b0a2340911802289b2c020c9014e0a04c2020131f439aa650c30abda8a1c0853002553b10dc0450008a2a00a5042130869808a00002501c8841846b2952230c60883104e5410),(0x0,0x0)]
  (columnTable 44 0x20002f007a08000dc01e420003c00784e000fc01e020004f00760a0017c01d028006f007208001c801c628007a007088000f041c128043c107010001fc01c020010f005e0a0047c017028012f005a08000d901642001380058ca040d9016040013f00580800530015938014f0056080051811542001580054ca0056801522811460454100057c015020016200538a0059c014c28016a00528800530214928054c085210005bc014828017200518a200d901442801780050ca08530214138017c00504c240d9014030254c08500a800f0414128414604510e005dc014440017a005096005f80140) #[[],[32,83,116]] chart191Levels angles2 composites2
def chart255Data11 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x0) else (0x1)) else (if i < 3 then (0x1) else (0x1))) else (if i < 6 then (if i < 5 then (0x0) else (0x0)) else (if i < 7 then (0xb) else (if i < 8 then (0x2) else (0x0))))) else (if i < 13 then (if i < 11 then (if i < 10 then (0x0) else (0x5fe)) else (if i < 12 then (0x2) else (0x0))) else (if i < 2000 then (if i < 100 then (0x1) else (0x0)) else (if i < 3000 then (0x1) else (if i < 4000 then (0x0) else (0x0)))))
def chart255Levels : Nat → Packing
  | 11 => (1,1,0,0,0,1,0,chart255Data11)
  | _ => emptyPacking
def chart255 : Forest := seedForest 255 11 #[(0xe464d64bd28970004102d0b300682fe1b1633aa2988531745c6285e1015a22d35048e6b5475d3809e10346d07640a707ab54b68f3c9eb2abd7c8f30027592f810309ca7da8041f6c6e17df69d0e6b0016aaa2009bde4c0b0cc0801f1cb371944,0x4440840af081400000021081002027a028a0600280c51300522005e001020281104086354900100c010012c3324280052300a21c34bc02a0c2015120224921210c084a1d00040c6c0402d409d0e280016a8a000804c40010c80001e10a171140),(0x9626ccd6c14082036a104040da1e4e9df95831da3ecc7d8784c5ca26878a7488af36ea68b3c68302e46d080c131ddcb2300d288aa8c50754adb809fd8c6a4045f6ecb3ea6a237080c860029a2e081c33a059fb95d00002958dfd0a4c28d0bc90,0x2224804010000036a014000800e4814510a00d8180864000044000040894440241c600822c04102e4644108001d548200050082084105500c9c085a8c024040b00281c26802400098100200280814328011311590000285057d0a0820008c10),(0x435002cf897c7af273a537328e8486ecea8c464d161f9ae887a8ac9674249936662518111c5056cca881823809705209d5994530731b49e1761634c15b1d008869257400d629800fa7e80dec59210b7d4384c68c489fa802024054316d45e717,0x500353000c20f001843700028004488a802220041212e084a0aa04341490304200009214100a640001801021400208441a5500611a40a10002b48001050008412520001021800b23e019fc41210b014284c280480fa800000050104d446107),(0xc9d0cd24be715124d8912e6da39641a6050bc545cb4b805aea59355cb343f40c20d333486d66427e53e4b72fd69038f9bae4ce1063e02eb6a209572b72e29917309b014f7cdb0b77e4c18c462497d52c3553345e84c7175a6350f8c9003d400a,0xc981840cace15100424100ed800040a4013340444bc1001a63551538830b620800d13348c94540181384130b961128b5bac4821106200a12a201423372e29805000804426c064974c40180022496d42c3553244c84c0071a434008c900390008),(0x12a4fff12f09a5dc813abb1d5d48bc08d4499b7ce428cd5068923c4be8d0563f77ca455d22203e63b76fd570cca46276033e6e0cc463d81c8453da02a533d2d252d691f4d297298717fc71514822a6921021db735872f7643016f794a40a48cd,0x122c71f10304a4558134c8101d089048964c99382428ec410882680340d01426610a400002a82e63a07b4c3048a8420a403b4c00c043d0050c5080800510428042c231a09391008313dc01d4080022920020db335832f0643016f614a4004885),(0x3b7b221018a60dcbe74c66a66323195e816a12392d3304821475718808dd19469c07d1d2453f4432919f6283af2eab831c76dec5d84afc2330320c4a00e52fe371637b13474b4e7a1a2fa162a3dc6a820db243f7af010b0b500b720a732081a7,0x123002100c2429a9624c62224203085a804a9a210802048204107810005d94460c0230ca041f447182994010852c2b8014461d814842a84130920c4a0020488a3063300047eb428093a40162231c2a82052042f7a9010b0200097208712080a7),(0xd254943cc8cc9e80284a21477d3843592e506e24e7e0d6d50a29fa161ac2b32adbd318c7d7afa9d816ab8addc4ad8ca806da216c2f7752866a0177bc8107753584a8768ea9e86ad2264e86732668a946b6c24c606e9bfc2ea1a668e45ae510c1,0xc044843bc8ce5f9400c8b14f6d3193412a506e26a7c282d55a09fa160f44b38bdb830ec7853f88481a8b8a5545e08028001aa16c6722d206604177a010859d310480760c95f8ae8a244a85730660a94436c24c606e9bfc2aa08260e45ae510c1),(0xdaff88853e70edd147c810935ffd29712a400d8a935c7bb53dc3023cba56ba178a4c107c80085981cbe308b4af383e4672b03e8919f4702cc3f2d650296056d0ec84d50a14291355919e6289d52c2c056172520023868497f77076f14911a79,0x410dd8a812c2020410108848b15cb2a500240048a0258111734e0122c9802b813134c121c80000801c6630cb5a03c0640321020a928504128c2d41256c9215658e8845d0a0001114481b26009c42c04010132500023040497f76056700911a58),(0x0,0x0)]
  (columnTable 1 0x16005fc0140) #[[],[32,83,116]] chart255Levels angles2 composites2
def chart479Data11 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x0) else (0x1)) else (if i < 3 then (0x1) else (0x1))) else (if i < 6 then (if i < 5 then (0x0) else (0x0)) else (if i < 7 then (0xb) else (if i < 8 then (0x2) else (0x0))))) else (if i < 13 then (if i < 11 then (if i < 10 then (0x0) else (0x7be)) else (if i < 12 then (0x2) else (0x0))) else (if i < 2000 then (if i < 100 then (0x1) else (0x0)) else (if i < 3000 then (0x1) else (if i < 4000 then (0x0) else (0x0)))))
def chart479Levels : Nat → Packing
  | 11 => (1,1,0,0,0,1,0,chart479Data11)
  | _ => emptyPacking
def chart479 : Forest := seedForest 479 11 #[(0xde0489ce472ec6568c204cf10c56e92cf9a9a6e15156c8df654730a5763848d04023cffee65a3ed3fc2a2c1473001e84a383a7b234d4989cd075007d5a7c955786bc672ef70e98c87310f12b484e265315118af823d14966cf28666a810b682b,0x9c04818040040c10a00100810c04e1a875a806414172c8c324041925660848d200690eeb56de168068603c80430810a5e002229270518816c050002840109113a23c032c77a29ac05000d50b484c265205110af803c14860c928226281032820),(0x61bc0dc9551fe2f65800e2c209009431b05dcb823a459437113044ac9c78ae1aa89e25103e19ce5e131f7514281e76083a1f2119ad70d0a0b702265895f129a5c14e1c9ac455112b894614c02d064592d32bd421f40c078c9e8c498434b38141,0x618200491401c2665000624203000441804149121805141401280488907086089a06a11021214854161e41112c10c6000a1941010c0013a8130000001581280440800410005500008144028021024180d20a94017004038c1680498434008041),(0x2d5cb0a443497128461d221072fa92701174c11dc2852dc0da99d211814ec16dd9cc3a2f84c321412943471688d5747a1922bee742830e36a8512fe06517750c8346dac911f08a651c9e6c7c5f99b1a664f453d700b09e806070a6408c810dc2,0xc4000a483c81000040d00107028813011148400020028404690d010040e200140c802020040200021c024040000307811222ca003800006a8112840280614088362184111088221149ae4645c99300224e04384009084006030a40008810d02),(0x88c5b2385cf54d9af0c434610b25648407ea30bba5384dd3a6b28ffbebf64a0026814a062d80dee123d89aaa5c8ba9130c5ef07682a34173131ad12244af02121811c8905e263572f42c22a4a0324b7c7e43297253830879804282a533749e00,0x4a2104c354912e040804983046080020922bd052a0183a00007e749804e40a40148c42c8096c902209a804c0988010004c044806141700100d12040210002001040a0402610c0e0200000a02243745a012072130008708040022411740200),(0xe008185636ae3bb4ad7a5e3705f47b51f850d8606f1b1638706be34b6aad228146a7819049735124ef93c821b5905dc7955d17a98684a5097dae95c52e80c6a85f81b476aa0884b0367f89926601da89002af70d611e60a22127d5880b4cf6bb,0x40491844208aa2a40d385e3260581a41805491022a01063c116be0180020300103829100012101348597006190b04502151115290684240934aa2cc50e804ea00580a0528849443006dc085406019889002ad505601e20822007d5880a08d49b),(0x0,0x0),(0x12ee6623e35607d72b6b91bef8eba42b2232ac814e013be0a80432a64a8975a221782ec618e4172d20b43beb4a3a08dbe181280a5ffc6ca48f81a684e280daf36f628b7868216222e373413910c41a50ac0c66aa9c4c283071ddbb32d8f1509e,0x1e6ca0024b1601902e6680ada8eaa8022232a0c141000803880022464b086082015800c6188c168920a0b6e2404b08d301a0288a51d060404088a68c600092810c22882840206a22203a093810841a502c0462aa84480830414c9222c8f1509e),(0x69fd80e043373545310622f1dcbd2cc06f11a54c49bd1212b2bb1ae537308e5b977596f9d8f31bad404d2f3ab748973a2280841f80aa7c9357a99224370945fb41e62f757d5a90782d4589a336dac14589da81d986e93ea44c11ae5cb2ac2a1,0x52bf980a04226355534062ad09c772cf84e90a5dc4539329a12f25a61371807cb5365845fd8e15ba4604d2f369748b83a2180001c80a87c815ca5107537180d7300462b246d32d560204189a23648c14581da819986e13ea04c11ae5c32ac2a1),(0xb313637db800b661d3ab6d4cf10143ff8ec62d021a30ea784785ec1a9401533902b0647001379a80502542fdc230b72c61da5a3d341aee5f3aa150c2e7ccda5362b40306798af31c5de147198de1b0490a5099804a75e4d93eb17137660a8834,0xa01340ac9000b6410001260050010175cd440d0202104278476588188401113c02a22430033308041005401d83307628765a17302c029e0b3a61004086ce6850628422073898811819c156010d41a009005099004835e4893eb16111260a8820)]
  (columnTable 1 0x1600afc00a0) #[[],[128,49,100]] chart479Levels angles6 composites6
def chart383Data8 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x1f) else (0x22)) else (if i < 3 then (0x7) else (0x4))) else (if i < 6 then (if i < 5 then (0x7) else (0xb)) else (if i < 7 then (0xf) else (if i < 8 then (0x2) else (0x6))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0xd11c5130aa8dc053c001462ac4fc66aec26c4b893040c01b512670822c43d3268c20c3fb502e41dcba3906801cc37b4a0d6dc9835986c018c2f9626d816c2b8670a61ec2788f096e59a917071810c1fb3064c0ddc403b066509b4364a200ac1382f046d31c301b7289800b81369003c8301f01611c03803) else (0x18aea36d42f6c5b403ac073e2ee9d712af333b00df01b6038c06be6aa94f91bdb26d00cf01979b9b33756aea5d4030c05f80c70176034c05bd0faad718b5a76c00af015759da5734acee554028c04f80a70137997b27b66caadcc024c047c2eee1b5d32b32d00870106022c03f809700f602cc03be6d8e5954bbab5b006f00d78b7ab6c56d6acdc018c02f806700b7d2ab36970bacc74014c027e6ce8dbd9b5a56e00470086012c01f805700772abb35c56cecd6400cc017e4bac4fd29ba57a0027004600ac00fd2f68d759a6a16f00170026006c0078037001601cc0038003)) else (if i < 12 then (0xb) else (if i < 13 then (0x3af83) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0xdf1b6b5e69dd099a324e30c297f6f2dcab6165abcd5aa87496864ed9af2e6504898db14e1bc1c7fef85e4bb1732e09b5353676c717f2e3594abd49a7b4ca92918a1b4047a4e89b43305e8b194c26c4647d8df1822a0470770b60f40f800) else (0xef3cb6be1647feebbf0f2fa77cfb5f1f6483f6edf5c9b38fb5fafe1fb96256bde659074c12878dfb8ae1995bbfa6544eebf0891b5520f5affc81cd343edfd4e1fb15354d6f83a8192994d6f16b9bbf20a07c49b7f767a641e955f5ec936e2ba28bbae7130eb5b46a2473f8a0784497704140ff2110e8fb21deaa5def34ef31dd25a4ae031dee4e7c7efb4f4b5d6342246630fde1950718eb8afd0b37769241ffe390f554597281c87018ef31ff5775cbf455af7928a1d2f903c4920f79a77b90463ad7cfaab5ede3e7daf732443d86b8ae66641f413bae549fb2d74871f6bc21a75af)) else (if i < 3000 then (0x2113035302012221322213331224213123) else (if i < 4000 then (0x105180) else (0x1538292f31132d110d1f131716042a123f2d3a1f381510053e041d113018033f1031203519141d290a2f2a1b3e1d0f3330083311343917121438213b102911340e001a2c)))))
def chart383Data9 (i : Nat) : Nat := if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then (0x52) else (0x9b)) else (if i < 3 then (0x9) else (if i < 4 then (0x6) else (0xe)))) else (if i < 7 then (if i < 6 then (0xb) else (0xe)) else (if i < 8 then (0x5) else (if i < 9 then (0xc) else (0xd49b60c36c82fc980bb64cd88a3330166dc0ba0af1562dc53b0668c9804f9700c425da1093844da84788b6e821c8309b10628c3fb024c41dda01720e61bd804000d6da1a65100c617e330670b61ec2bd5424d4c827b4a6a0d81b914208611c1f8606cc500811620660bca81000560dc1383b04612c0f952690d12bb0170260800781b01614c03803))))) else (if i < 1000 then (if i < 12 then (if i < 11 then (0x367ebbdaedc9bf0147050eaee04fe2fe04eeafabaf0133e3bb6eebbe012f04af2fac9faafe048c127047c137046f2decbf32fe044eafc043f8fcebb32f6cbb8107040c10b03fc11703ef6badb6aaf6cb6b6ce9ae80ef03af6ecbbcbcea99f80e3037c0e7036e6be8b7b4fca9f80d3033e6dad2ea6eedaf00c7030c0cb02fc0d702ec0f302df2badb2b8fabb980af02af47ed3bb4feaaf80a3027c0a7026f4f6bbd36dc8be8093023fcecd9baece8bd8087020c08b01fc09701eeebefba36aab9f007301bf4dab9e8067dbe006b018e6f6b9faebaeba805b015c05f014c077013c0b3012f67cdbaa8fed3e804300feeda9b7b6e6dbd003700cc03b00bc02b9bfbaf8db7aedeab7a6fa007c023006f6f6c3f8017004c027003c047002c0f7001c003) else (0x104c82ae89bcc05ece3)) else (if i < 13 then (0x4414038018c18b18780020018317f00e17c17b17764017416f08016b01e17316719c05c15f5000f404008424815715374014f06014b14726015b14316313f67872000c52013713308c1841e46e012b12712f12310011f1284a023419411711366c0883e062010b10710f1031806006a004c0fb0f74407c07e07000ef0eb0f30e70ff0e311b0df0200db2c00580d37802ec0900cf0cb7b00e41246740c30bf0c70bb4441601988280b30af0041383c00ec0a70a30ab09f0b709b0e00a06c032009308f17844808713008b0830301642f882407b07707f07309706f0d706b13b0674e04f005f1c024001605b0570530c034000030004b16c22422c04303f28004703b04f03701a23c4806805e05c002b0274200984e805401f01b0230174c001302f00f03300b063007003) else (if i < 100 then (0x1) else (0x28119ff27e39eea77f9d827229baa6d09a3a66a992262f987260897965bf968e573955653d949250b93aa4cd92d249891fa45f91264208ffe3e78f2e3ac8e4e3778d1a30c8bae2cc89fe2618926234885a1fb87121818566137843e0f6834e0b1824607d815a038807a0097f91fcf7e69f727d55f387c51ef37b19eac7a4de727969e407885e0b7771da9761dd69751dd2573d1cd172cdc8e71b5c5670e1c1c6fedbdd6f15b9e6e01b4c6cddb1b6be9adb6a89a736929a2a683d9f767719c366b5997659994864cd91663d18d562d589261c583c609180e5fc17db5ee179c5dfd75a5cfd7175c056ea5b256ab59f9669592962a584d5fb57595b9566958055815405499507535d4a651f545350c540f4fb13cd4ea93844d9934e4cdd3104bf12e74b192a34a1125048b921547e11e447011994609169453111c43f10c9426d08041b104c40b500d3fa4fb73e44f783d60f2e3c58efe3b64eab3a3ce71395ce33384cde93708dac363cd713540d273414cec32f0ca6321cc4c30c4c112ff0bdd2ebcb962de8b5b2d0cb242c1caf12b30ab32a4ca69291ca3027ec9cb26cc98b257c94b24d090d23dc8d922d889f2224868214082520287ea1f347ae1dec7611c3c6fb1b906c01a60683197864418645e717485ab15ec55814d050813a04d512cc49a121445010804010f883c30ea438a0db034e0cbc30a0b942b50a6c28609a0245089020c07c41d006a018505b8149047810703800af0254079015c03c0090000)))) else (if i < 2000 then (if i < 1001 then (0x30df2729bec8e5fffa9e45f088fc3c2e756ceeca2fd8bbe63dc03e8ad5d1f7fe7c0ec9158f07f8cedc181a3dea28b79ce5fae38cf71d49fdd5bacb1979fea7786e18d4d451a249fc594d9e3effcf67e9ee0309add07d5df8ee83ee28ddefb11b3d4bf1fa6fe57b0c02e6495fdbf533de693fb36f8940adef9168e5e44dd7af171347e9f4504b34483588bfb3da3f4fb2248722b9a2abd926deb212cbf2ebf752ef820dd1621cb77bea7d77511b3a063d206205563c7eaef4380a8cee8fbed749f31dbcf818bc2dec995c35d7660ca1b9792a1f35dd005cbdd1a44b08a8efc7e9be6d379c9197e3f4f8674e9fd086f76b24e434f29fcc4fecf8157e19bc64783f092c9c8ae1f181a7f268c3c5c395a6866b979eb595a38f42594cbd71b8d4263947d516fc7e0c57a6e15c26c9158178a8ece4db7b88108b56eb0172ceefecf06a2aceb044c735b9ae4baee83e4577ddd43aef997dc63d242dc6fae4750e3aaeb0176113f972e9695cbc8be120a974efc7bfaea6025be679975c7ba7b9a68609bcf9272d7741c4b91fe9dc74a92f74acfd5baf17285cc726f26df787d94d459d944a34fa6bba00b884b1fa7d5ed5f831b124caf06b997e4203721f31dd77ba6e19848170cd379e727241ac783ff747d56f1bcfc37bd598460dee5e01a7c3beeb97ec827f10c8ef09c562ac7cf8de3749f1b3d9d16e806b2bf7e13b998b9ce69b13cf5af632dee5e064be4141c8a47b8eea5d68c3e2722951ebff8af1d9fb678356f3a7d14abaf3fb0afb32e1d0a567e2d4fc7badf51d94be8af62e7bce736b76a28ab4f87c9cbae0b6cbe5d02e77ceeb744eb87785995ea445f8799ebfee8958b8ece6d3119e13bf05b83636efdaa46e123fc2f7c0f727268fd3e8d83f1dfb6719dd36c22b8d28558f4dfdc733514edc7dc47ba4f67e3a07ee8bae33be08c8165eeab8577ee4fc58e66ade9bae72e30a9d134b8b7e389a115b291c3d7ce84500d1a266dc0c2a4fa63ba8ed4e8c4f512e65350f4cd149c0ed97cbb3e4e5d72fb675ce9d8ebd9edc079cbf6cac8ed703cd058fc18193bf1cec6404b4d9e721c0974dd65d70e528918762a9a8468927f16536de3bad7bffa87817b218040a7f67ce40e45ca1c891f3d73b8283f2e63dbd9ea1c0f71408672133d43d78c8bf0824ef3aa9e99a5427d1e096101c2236740cb2e863701fba7c297d15edbfd71f1e9efb10faf3469c819fe7f52c6d97f5764bcdbf945f38a4a834b1d17c89cfcfc4c9fc7a3dd27b6cec7a4169dd1dfa2dd07cef47d7025bd98308b50e3eaebfee83aa950f801d4b88ddefb34b2898dc1b8ce7d12fd190dc2a9f74bb7a6e09422bd8a1cd451dfbe3ba4f8129c7f75ecfc8ff76e8948a472c7bfe068c63a3a273f6e059f29ca383ff3b43d7ce2913424a4fe39a8a3efb8bbe6d9e8d40346a37d5b43e004b34) else (0x1050689fc7b25f1d8bc22ebd9360c20713b696e9d0453678db80c224ecf49d3a7b3fb3d0e5bbdf51db910edc7e1ee85222f35491e80cfa496657975e2e0bbc775cec9e1d9c8347aafebd9f7313e1d019cdb2061f86e06dceadaeeb165937bbe38e837d80d027923fb3e3763f060b2b3f1c390633bc7450f75bd6dd5d2d918f2cb0acb1cbd1601394932aef4a978eb2ff1f7d5d7722631e91e84cf5e30324d3aadd03f9cdcec529bd9567e9ed840c42e3db6345d42335367b471e8458ea5db7ba1c5da66b72f660c20b2995e133f97e1357222f35492f207aaaf3d4ad6556b82b5a0d63c1ff5dc18cf75eff8fb8b60fe559fa2ebcd657ba197395d8e40ce8b2acfd423bc64ea3b7e)) else (if i < 3000 then (0x33131102313202032221131031315110150320523532103213032032052334232131531116113212400123111211231111223323331111534313124312120022224113124422142211343202042) else (if i < 4000 then (0x2450871b193c85329044200) else (0x192348a11041124d63e4421f0ba244bc1bce01e8631d4f91101e2343a2d00433c292481f0347b074791d80339cbb3080324c5f284592fcec06064088642f893068e738c5d228c712caf1947d04009180eb200aa22cf92545f3b86b2b8b5158ff3708f2844e0b8250382917ce5110130406f04c391b45c1ac89128412f4bb3c04702ca62007e1a89e1302f1d84a35c8b04839098700fc5f1e0572f4ef020661e4081786e310e80b0d7230ba12c70024740a01a2b8de2dc851988f0d8ef1586e200300a4722885e144de18ce33d4ce03c91134093d09f374580086a33c6e0cc0c3a844130700d07b23804160d71fcba0e43d2505821071104b91a8dc080f22743e0ec222b0fc100b1120792d0000f86307c4b1942d1204e280c62d4e704c3b1249d1c4de064ef230551e85420c91008ec0684d1444715ca3124421cc541e8ab3a8f525cab0c8ed1e49430c6b374dd114ec3ac31048d02ac0e11847350b903c9a2907a1d0602b03d1481c120c9218641e4f921c7a3a8ee1fc6c0e40c0fcdb384ab298543747e)))))
def chart383Data10 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x62) else (0x5e)) else (if i < 3 then (0x8) else (0x6))) else (if i < 6 then (if i < 5 then (0x13) else (0xb)) else (if i < 7 then (0xd) else (if i < 8 then (0x6) else (0xb))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0x34a204d30310871065403fc22684501810770e61ec3786b60c989a20600c617e880670b6cc09805304015c27a60a64d20a31000860fca9352680d18a10370660ec1784705612c13d546a04180f81b60005e0032624c03e3301301608c03803) else (0x73eadf9ef8d7d018c0bfeece7e59fb1fc057029816c09f6dab77011edf56dee77010c07e04b01dfbb806e033f7f6bf35dc02bf7d009fdf802f011daebdd56f600d805f9fc01397f003edfdafe005807c00e003)) else (if i < 12 then (0xe496694ac09ef8df20c41711b4ca08b18f1c3) else (if i < 13 then (0xcc178a80921283a054ca7bb046052ca39907a8261e813f27650c9b81026655c97b202e86e1202d02462e08f92723645c1600626043d101132164ac83ab00e90407fb301883ec7b8484e03bc050f31d6d813c4141c60a1a01b044836c6b8df1a66006791858031c8020019030c5f8b41002dc120bb16632c578e715640c5394024027d401503808a04b8931201104787011626c43b38800b803c07f0f6038280732f01dc3791c0d620c338e006017c303a066815cb805b0a69808a1101603c0d0047086282183d81280ec1b83f066341024208300ac139e04a008c0f82f0361000b84b02613c0786301628c03803) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0x1d86eb5752ba2dcf8e5d719b897c36e0ceff777fb9fd9eec735e7ad3d49e9df4c1a4ed0967a73919a9cc8653325f8fac6ae303145889c30e0deff97c0bd15e0eecf748b975c36dc56aeb40d992c8d632b0757c2b89570aa754b6a214eaa62524e8f5434a04cf0670936099e4c0e5852a4939c96a48d20a8f646fa32517889cc49e22d0ef862422a0f10448093ffdfd2fc27c13d35e52f0376d3aedd20e5370fb79db8ad9f6bb3531a74d1a67e333192ac7c62db10d7ecbc95d6ae31694b17579ab3d57ea9e53d297544ca024df267d2b4945496241d1dc8a943221490648174001f94f6678a3b29d0ce206f236f1a98d1265f30d97c0bb25a52b014c8a264f526e12f492a46f2128fac79a3a21b70d146202f11658a804be24811b07f83c21b00ce85d42a213308483d41c40c5045818008a000) else (0x1b458f082570ed7a71bd906c6f51fbdb6095b2358e56d0db266ddf97393b4ebf35df7e0f1a3ca3f72a0b13a2c906943b56dcb16ca122e75f7ad439c787583f1d4bb9b3f3d31fbd7a7bc0795ecf46263eb6d4fc6097b8cb049c93bd535fa30fe87266de0c19191d3baf8ca8f5f0557ad7b8927ff5db32d471dc49d25e88dfb9616f3b527ecdda271a83b7af8c6e26532569b768bb296a9737e7128ea21d287cad73e9b4bcca59c07963cabf0b9a0d457c61fbfdb44c95a0e52dca2edd7308f08809435d7a32f17e79705152a87ce13bc00d7b4bcca5fb9cf20b227dde17e5da29b37cd7d89427fac474932a0954ddcd9bb6a2ccb04b443d567bd6f7f03819fab03d7edd3a62f982be1cab5cc21875ab850aa77366edabc1c331063efa15f70c1b21e6987dedcd4fd76bcf8de0e45308349dac5073dfac6fad313a42bcadfa0e52dca2e6370a11a2f0b5cddb7a2a0d7ac75f56ec5b6ce8189aaf2884edf2633847561de7607692e482aebf10a835eb09afaf76ade6587d4c90a4edf5f61e7a36ee8f90697b4f123843020eefd8d7559dd50edb283472c20d3b49dada45ea7faf07f4c74a8a2a397b187ba8964fdfd000f5120a8ad66bc734fb32c695029890afbd6b6fbea40ac3bcc70c5ff7b9cea2bae3b2edf93d75e69abb1f7704bbd8af5e9cd58b4db76740677ede9116e1e3358feda86ce3018d10a85ae6ed8533b661c8adfef79a705a00e19cc23eba9cfeb800d190694fd8ad57994e37537a25debfa7eff94e9876b7e60cfb94e9216a54708415f7aab9faabe0ab774d672e409df5e8cc7b3e773174d7de35bdaa2d4fce36382fe85ae6ed9d13e2376c35d41b8cb04bdc99a405fdea8e00914f9ff01e1ea276bfa46db8023a5cf5afbd6fd7095739ea55bf5789182e1dcf95a8af1b6ccf83afe91b6a415424e906dbc9b66c3315b78a045cf5afbd6f573abb4bfd19f0bf90695d99515fa2399f0d920fa67f7adb63bd3bb7ff48c80dbafb4e92e24b727b8b9471b22c2094388abd6328ba4e3d2f3fdf2c2e7de5257c277515b1f2858b89f5443c948f5e9dd5ac4bc104220f9066baedcaada1b4176773e5d22eeff70bad9f7704bcd19f04a7897cf8220a11f564787732da9bd776ffe5b655ea7fd6cb13a25e423adc247eff2327660c73e281f9a6b354c2841a4edb0eff7bcd383b44a36e03e365a77314f5044edddb3ee58abce3d9367a3fbd75a39e9761511fababcd06bd63d3a7e3b2197013aa26e2c0c6a151afc04abfc79a9b4b54e7b26a623ffc7c766dce32b65e90545e906dc7b04b7adf4fba7e5ee58abcd9e137dca83b94535e80401e32cbe)) else (if i < 3000 then (0x1332332020532321322032012233114222212121403121001222423212221021714122413620631130321162213011) else (if i < 4000 then (0x9d8163491c00) else (0x993f03b2a816128753aca421c3d06c060b40a02c7704051288e6218161f444020a811c6b38cad2c4461c8431c47c158ac0ac921440d010730e89d2ccc9114a925826120072503d0644104c1f1847c054952046c118860a48315c9201c42298400b4d137089048502703318ca71047520835274b71b8741209c0444b1702d3ac5b3c84b1ecd41c83e2c8bc27c4c2e07c1c060038bd38cb6108721f04913c8e0c44712c5b2b8060bc02158f12e8460247f1202c134bc15c3e204a704cb11e0071e82f0243e134ae2a0420f4a712052158f00f87f2e079170a83c47913076160783845d1d46a2f0422ec403c82b)))))
def chart383Data11 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x3e) else (0x9)) else (if i < 3 then (0x5) else (0x4))) else (if i < 6 then (if i < 5 then (0xd) else (0xb)) else (if i < 7 then (0xc) else (if i < 8 then (0x6) else (0xa))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0x49a992600c00ac13b0620cc008001f03608c0bc008cc0819300f01604c03803) else (0xefceee00fefa00bafeefe007003)) else (if i < 12 then (0x1441638449f6e35cc28818f2d31c3) else (if i < 13 then (0x1280a00218c5f2405b440084c1701805313d182e04b11c5c10c570fcd804037080c00c0330bd980e0278202b08c3b07d40160174e08c04c640500f02c1b01c03) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0xa024f8d9f87459e5fd534cd123a8d9290851ac430c000) else (0x6041453a25b833ebc4d7de7f293e4fe706b67b7fdb2f025ed953e31733ebeea5d1ba9e5357e14c9f06d1d1f57f6347cc836e9605df45e6a4d2df74b03af9a947a2a35293e629d1b1a3b068e0fca7f27e96047)) else (if i < 3000 then (0x400600800) else (if i < 4000 then (0x0) else (0x3c171d0429101d1a161b00210a0d0412180f)))))
def chart383Data12 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x8) else (0x1)) else (if i < 3 then (0x1) else (0x1))) else (if i < 6 then (if i < 5 then (0x0) else (0x0)) else (if i < 7 then (0xb) else (if i < 8 then (0x4) else (0x7))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0x0) else (0x6fe)) else (if i < 12 then (0x8) else (if i < 13 then (0x11182c102c383) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0x0) else (0xd8)) else (if i < 3000 then (0x1) else (if i < 4000 then (0x0) else (0x0)))))
def chart383Levels : Nat → Packing
  | 8 => (68,5,0,0,0,11,0,chart383Data8)
  | 9 => (311,4,0,0,0,14,0,chart383Data9)
  | 10 => (189,3,0,0,0,13,0,chart383Data10)
  | 11 => (18,2,0,0,0,10,0,chart383Data11)
  | 12 => (1,1,0,0,0,1,0,chart383Data12)
  | _ => emptyPacking
def chart383 : Forest := seedForest 383 12 #[(0x24d06220d8c0ef7cd2130b3880011fc8040111c24d5c6e468f229076351835c283e320e5eaa6365e62e5a4d060e744cdf603a606615414854514acb7dcca989f3a78cc4e2849acef65481d312c3418c21c4a2dcb0e52879a22a1751a0249e016,0xc040601800e0780008080000811cc04001110210584c408500108804101502014228008a2030064000004800606081d220a60260910000410084839c40988b1a38804c0c01800e60400c210430104004422d830252861002a1541a0008c004),(0x7d118c98a143b5a258af6b1e5a38296592bce06f6038843914844a75a186a5390cd416fbf11b9e01808da64213272a71cee15cdc1e20a8b105f9998893934315f094cfb813f63510b015a3cb9660c638bf91c100198770a02c38006b50ce29f1,0x25108498a02a110210a74198581c01049010402c6000802910140074210200010c1c10c97103060180012013110308600cc040941628a280146d280001900054a4044d01110c2010000500428200c6309b10c000088570802008000150c22871),(0xd1c8942624550f504310fa3740d1eaa706d673ec1a6687eb16c5ed079fe01898db22c6388cf830e6e77851cdae98b7b0d2363ee0c0930459cc93960826222320c8cb38f8f490f8fa9b1521193465218b40901800e737a3344f90e99cec04dea5,0xd84a502656550e544b101e262080e8a3038221c000260b4241a19c02d6e018188120823086b0000a267851e82e98a591c22e1c60c8810453c190920826260b2040c830d8ec10c0aa190a21197065018a40801800a73281344f90e99cac049284),(0x10ad2452ac3a6211a0c594d0933fc21ea1ebbe3a58b07818b0d120c6ca313e26501794d239e9c0230d21f845c5dc9c822fc4432196be60826a43e74664e9a46d0fd13014c6064a8b622048a0cf1be2414906cf1fc0e94a44804e80c4061acf14,0x20006488808700220858010002902100068962998807018000020c4001027065003244a3849000119018001c006080020c08200064c6000280320c40049b0550d11000002010a00602040a00c12e0410906c30b40410240800e004002184d10),(0x656c0de6c5c60a2d2bf222879b1c8d29351733d0008161635ab7bd8254ebcaed893570454007acb1ac6c6f342d09076c55d14511b82894e31e8c5b0768755f420ba44bf3008660f77eae35b0f31e01300028d27517acc1bc355337a4d5d71043,0x652c181045c60a04097262879b148129051420500104002652bb891270ef08a8882451040404cca0a0667c342f09076c05114114882095b316a45b006334450080805bb3019660c10f0e2140f00c01300028107415ac41ac355023a4d5c71043),(0x6730ff0eda4ccad28da0a1f714b0159a8bd00858e786227ee24e25411273ce0167589d1f1e618fddcc734094dd245908a10bb9f4456414dca0f8737d017701f6e0de1235c238fd6107e1fa0b29c079d7892fa2088539158242c48a258bb631e3,0xe7343f0ac2cc0a828c86b1dd0830a00b81f00c60c306a21e02462c410022c201421c851d244089d92c73401665041900014b11cc026450d82070213400076170c0c4303342187d610b00720e29406997890d82088529018200448a258bb621a3),(0xdd6b28cb1d05fad8492811202d4824c3d8a49ec7aa4b47dc8143226a4ce7f462dc2346029d5809e13b02072e01148867813d26fb0a51af75b23193fecc0c78a9012447ba3f65d669197a32eeb912b5b427c312e4344a00179705e875330cc78a,0xd84328421510e2584c0898200100342308a49fc38a0816c68042200a48cdf674c00146020c0800e039120f2c041c0107812b266928541555401293de400cf9005108023a6e615461197852a42912318424c31244144a00169605e864230cc78a),(0x0,0x0),(0xe25a5995072c656a35e50645e5e708d66858ac10a27b1b81792a851814d2588be168db04059275849bd361685a502bee099c5b4295a1eb48b6cc0c50119c820a272304cdbb03438cc8c7c236e885432492643cb22050f841f91c4e1aeda11048,0x840b40022052001300600a4c448c460006010207109017928011014000880016018000196740682802040020162780014080051810a00968c04002180060a222285849102008880838410c085022012202cb02010f8016910041a44011040)]
  (columnTable 68 0x20002f007a08000f001e138003f0078080013c01d828005f007408001c801c640007f007008000e881a24000bf00680800318119428049c10640a0431811902800e700630c003bc018820007220618a002f041814800ff006008000ba00e828025a0034880098800ce28802e803208009c004c528067001310a009e000c328127001304c059c004c0200298002cc800a6002b238029c002c4800ac000a72802b80028ce00ae800a24002bc00284e00b1c009c2002c202269000b3c00982c00c604250a00b60009328829800a48e00b6800924002dc00244800b10208d2802cc08224c00be000834802fc00204e09b30208028202e80380a400ba00a82840c604610e009c800c658027f00300a02a6002b04002b700290a10a6002a2304a9800a81600afc00a05802df00240a00b88088a4002e700230f1431810804802ef00220a409c0048531067001211000bc800863802f400215600bdc008438ca9800a01a00bf80080) #[[],[16,82,131,100],[128,49,100],[48,129,82]] chart383Levels angles3 composites3
def chart495Data8 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x29) else (0x20)) else (if i < 3 then (0x7) else (0x5))) else (if i < 6 then (if i < 5 then (0xd) else (0xb)) else (if i < 7 then (0xf) else (if i < 8 then (0x3) else (0xc))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0x36a284d11c21921862fdc70c71762dd52174a20e30950af1562cc53b8666027ebb09b48028c4b9726c46512108f116659cb36e28820c3f8870f6d19c114a6801cc379046145a9b60670c61ac2f8770b6d91c836069814c278a484411e5504b08615c1fb2a6a40dca95986a00be220330560ec13b0421407d515547014c9b301702606c0782301624c03803) else (0x7b90bf2167738ce435e017602fc05bcbc6fb21257b3e800af01578f529ea4b1ed730028c04f80a7013602cc04bcfcaaeb12d7b4e3008f01176f531ec475cafa0020c03f808700f76f125ec69cc96ac01cc037e2dc97b99e621e7006700c601ac02f807700b6024c02bc2dec39db6629ae004f00974f331ee4b5a97a8010c01f804700772f327cc5b8ec6b800cc017f790a5bc00ac013803700471f3a36f63cca79c006c00bef9087b8004c007801f0016014c0038003)) else (if i < 12 then (0x283b) else (if i < 13 then (0xd004340f003603b03703a0331f8ac007043c02b02707830002301f02f01b90034003e4b801300f01e00b017007003) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0x72ce25bdb6e6c5d4ba2f38e56c7d89701dedba36cacbd7dacb51e9350d9df3565ac958f317e2242c814fb9ea3bb732dedaab36638bed6fac1552a353625146a869001e53906b4c2167280494850ef19e2c04b07c0be10c0e000) else (0x676c3e18ea58c7de4018a9b5ba1a857431573dc172f7d90d3f2743cd5d987450186bf07434f7d6af665b74382ffdf3e8e6ad1a1b7f7cc11b80d8fddf337bd5e24e0ecf686a5874215b356bf9ddac43b3ed742b847e1af61fb18527710e4d580628215a71b56dfce6aa9f98623f107f3aa93cf0967b4316f90f8a57de696cc3b9e8c460bca61f3285e93552b00cf899ab45fef743c553cc3d9142f5cbd03ce9852fdf307aad72c3d527fc7ab4f7957dc3dcbfdf2d8edf58b66bdbab9cd6dba32eceaa6003359549c64ee3ae7a69ab5378642f42de7b82f79ab5caeb200cdacbf7c950abb1cd794a0e61)) else (if i < 3000 then (0x31012311334115224102124033120243) else (if i < 4000 then (0x105000) else (0x1c27898ea7d0f9bcf639071ac606f39938de453b994ee6f2b048f8030c008087f17184100c271847e262b9c4343d309a49a66388303c7906900b87707834de02348b886370a1e0b25c)))))
def chart495Data9 (i : Nat) : Nat := if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then (0x56) else (0xe8)) else (if i < 3 then (0x9) else (if i < 4 then (0x8) else (0x5)))) else (if i < 7 then (if i < 6 then (0xb) else (0xe)) else (if i < 8 then (0x5) else (if i < 9 then (0xc) else (0x3446a0dc0a20cf19631d9812a2a4a885f8c317642aaa0b34802dc57b60148dd0980a36e429c4f9726dcc284bb4e2e05a847b4611621db115069420c3f8930f626c3bb52680d903786ba64588b23020c617da632a0b75d82b8670a61cc278ab096c1211510086529b32426d80ec1bc440660fc1790424809cba14268407db532403608c0bcaa54804c0782b01611c03803))))) else (if i < 1000 then (if i < 12 then (if i < 11 then (0x37d8cf5bbd2e77018f062ebd6061efd8ee6817fcf7018305efbd4af70173af7af56dd72f98f75816b059eddccb7abcc8f3815f056c163055e6debb737dac73814f052ff96af1bf908f7014304fc14704ec15304df3de04cc16f04bc17704af55edb7af9cf658123047f7dcbf3339c9f38117044c11b043e7d6df4bf9abf28107040eddac77235ef6700fb03dc0ff03cc10b03bf5dcbb6af5cbf180e7038fdd2de72adebf580db035c0df034c0eb033f5dadf5af9ade680c7030fd9acf380bf02eefdaef600b3cf680b702bc0cb02aeb9eef7339ebf700a3027eed6ee7bfd8025c0939f7335eff4008f022c09b021c0a7020c12701fff92ff500779f7afd2ef5b9d601bc06baf68073019ef5aad7bdd49f6805f016eedebf3bdd8bd78053013c057012e75edf50043fe5399ee76803f00ec04700dc06300ce9defe62bceee5802b009f7ceb57bb9c007c01bbf531de005c023004c00f8f7802f002c07b001c003) else (0x3a8ada2e09bccb11c83)) else (if i < 13 then (0x1a0407208e01ab0803400c01a71a31af19f8808002c06c01971936706a04605e018b18718f18324c4e066402017b1774207a025890016f16b17316717f1632146e00f88c015b1576008207e886014f14b1531476402301e070013f13b14313715f1331902e02f07e412b1274c02240e024411f11b1231177800ec12084010f10b6607601033a01070ff1130fb12f0f76500f402c03c0ef0eb1806200e70e31603601c00db0df0d70f30d319b0cf32002825c0c70c34800786480bb2a02202547c01880b30af3000ab0b70a70bf0a36802002284a009b09700020c09308f1a008b2407e002496008307f06406807703807b07308706f09f06b0cb06703007001605f52021c8a006c26044005304f05704b05b04756054003f3800fc0a003b03704303306000e0347401e450002702320401f01b3e028001701301e02b00f02f00b063007003) else (if i < 100 then (0x1) else (0x3de5f70bda5f5ffd63f507d23f3d7cdef2ebc9bf1e7c4ff0afbefef2bbb1ee53b74ed47b37ec63affeb77abeea77a7ce97ba38e8439f1e75f9bbe68b989e54b92fe3d38d9e2f388ae17383ee06f7f7df637b5de6b776dd5773adc376eedb3b6b6da53676d94b635d86f5fbd7875c7d6a7587d5c354ad46b4ffd3334a8d20b459d0e341acfbb3cbce8335ccce3318cbf32ddcb0729bc9ef259c903224c8271eec7471a9c63f169c543126c3cb0c4c26f083c1ab04ac09b005bf92fc3be66f70bd3ef2dbc32eedbb52ebaba0ee68b932e2fb852df7b74edbab65ed6eb4e2d0fb3cacd7b2f2c99b20ac64b09ec02afaebc9aeaeb8dadd2b53acdeb15abfaacfaab2a94a9d2a5ca90aa28a81e9eba71a9aea646979a552938a44e8f0a34e8a9a21686ca126828a02a7e79f327979d9a7449cae7079ba26ca9aa268999b663c987a601978a5c896ba58a955e53594664ff93624b6924e473912a41a8fce3c78e4e3708d5a32b8c3a2f38a7626e892a225880a1e6870e19585c6141847e10183aa0ca826e07081320297f75fbe7e79f817d65f367c61ef77b39ea87a09e627905e2a7811de67729dae75f5d617519d1f7411cde7301ca7720dc677105c266fd9bd56e8db866d9db436c75af16b3dab66a51a766961a3368359f1672d9b06631964650d91863d18ca628d87b617983260657f35f657a15e057685d197295c0d6d85aed6a35a19669591562d58415f457715bd568d57f556553854514f853714ba527d47451314294fed3d14ec138e4d913474ca130e4bb92d44ad129749d925c4901227483d1e146f919c45f115b44d911843d90c5428507c413d0304044fef3f00f963d90f413c70ef23ac0e8d39c4e5138c4e0d37ccdd336c8d9635e8d5f34d4d1633c0cce32c8c8f31b4c4f30c4c012f8cbc12e68b752d18b2e2c34af02b38aa62a28a6c2918a2728089e626fc9a52604964252492f24288ea22f089121d485820f08241ffc7dd1ef07a31e0c75a1ce871e1be86e11aec69e1a0c663190862518045e7173c5a4162056114f852013f04e313004a9120c468111c4290fec3d10ed438c0db834b0cbc3130ba02cf0ac028008d021007d01d506b418c05cc15a04e411803fc0e3031009c01b00500094000)))) else (if i < 2000 then (if i < 1001 then (0x6380fd5c3720eb9cfd6964d831e7322c1be94212dfec93aafc1768321a6b865fa9ad2ccfeb05d8e11a57744db17a7fed1fef017575047fcffda68d55cfd2ab0fa5a96e91a77f9de931d4d148ced9c70a6f5031340bf455c8a90ad02efd345e6f7d62c3d83ef222d8f9f4a3510564b9503e1b976105f7d3f1ecd5d4f8a764d8dab423597bff71dbaf6664bba7d31ae9a7c1717859b5bfabbc9c91f5782b2a3b5887def50e933e79f7a29af895e63f3485873ed6e766ef842f02edae42d56c008557af9ab51feae7dfc61a1d485205d0ec306d87cc79d10be7b6bbdcd6f06ed3fcedc556cb5f393ccdaf411fbb768beaffdaed063e96ef8762593fe2abd166d6fe9fbfdfc5f4eda9ad4dce3ea79f6feecc89d6f305f027f5c1737aae16187f570ceae193ec50079be3c7c5d0e7af657dc1e4d3f0721360cf9fb7435fbdfe4312c4fe8f5d317438944460f2c7c31c1d05ba0318379dc588503576f9ac636c6079e478f3907835d411feb7d16609b9abdd9c7e36ed234aedc06ef78cbbc55ab636eae53ccd6bbc2e268c6f97d1f7cdd6ae9fa58217312aef8363cebeb00696452357a96cfd7aa1706c4ac5af347fce67dbfae991abc17f3528a3f04321fd5e8379ad4b9e8f060be4f7d5c591de65df3663bf06ed0321b5d5cbe47d7cd3663cc26ff2b401c95645c312175e5891689b642903bb6d77b5c61b7affe7e10b68313025cb116d4b2b5daa497604eb583cdcd5a72e9bf6f0306f4ecf3b75e59a7f504eb5ef65cfd5a19b7d4e3d4976146dd2e478bdac46fc3a3ff68f763ff79ea0de7748b7179c369c0b9f9b31c2d81f9b16be90b93fdbababfa8b6b0c4ea89a8a475bb47416dc15fdf34281f391fa7b9c75b9e1f84f7753ec0c7c222a523ad3adf4c6d7c5f79e56c2b78035609b6154f2ee52b2a5cad4f9719ff9dd3cc1e2a883e20f5e6daea397a08bf721b2d5db05ffb20bcd135149bf4b6a6cc5b1e708bb4af2ef9f871e733827cb9f1eb9a268bef9ead45775f7f7e7a04feadfff1f0b8318505b89ea08d97788e2db06af5e2c6331b5e008fabc7e68ffa7fa68c26f887e80632a4b713988cbec6bbd35c36f0ba131150335a669b5a57dcfe9752d98e65718fae1c825bff7acc74419d4b977df88b6bd2bf21ce84f701b5f07bf8c1dfeaef8a5a697e00f8c4f7ec3f54b993141656fa63766972e6cf4e777a08bf9fd7ff3efb91ebc91df5e18367a8505bafd93d594c758ffd9cb9063c79d17eee3ce66b5e6b52d3a3f192e3179bff7f47f169d433904bc1f34bf87276822156fdff33d22c971182454ec4a7af9e9abe3d35a75b33b0d93eee2d1d6467ef4d8f1d096fc3b0e933b46d6217c5bc42e6b77c33b1e6d7cc8f83f316c523da40e77971d683b41cae1f0ef41a26ab0bfdb12bbac889bec703f51652c6d9fcf23c7e342f86c9f774dda37eedc) else (0x8a50072726fd5bc1f0d3fd9bd871df9894c7c55dc2e3ab9dda0c4f2c3e198d95e1e6262a4e48fab8a36b42d9ce40442b92c976b107b2126eea81e69c88c59dbbf39caba9125db13ad2608a95746b6a2797d1f18dd4c0fd90d024811fefed5f18b2a3f7bbf7c616e87ee1cadf9191dbb3fbe82d9b2ddac313696c71fa05dd43b74f48ae90bfd2172a0346753d35707ecb1457b18990d794be56c7b46d65373ce67c4455bef8f4d6909ccf66da562de1b2ee7c6d7304b52cab3a797e7b1c8ede32ef84ee7a31466ef8e7f4d1a1b14b3b6d831e9a42f9ff5062a5733ad99ec7722575cee46f5dcfc24f5fcc54b3d6c7a6b4d95040e3ecd13a4cbbe7e0abfd6d2bb37caec87f3e1a303f596ae3a63b060fc49e8c20d1fa7f9a43786e825bce41a31d397722e36edc1c812245397721863c3d06d62366d91191f538ddd2ecda55e98daf758e1625ba26d8a34ccbb94665c5e2cf234a7396113ee567a82367ca6b9173788c8fc60aefc907635a2cb9a1cb5d11e137f99edee464307c107ec4d320df7e6eebcd2cf3be8a14c33a9f57b24031b515dc40fd8fa97f6d623643360b8dbf6f88fd574e1aa05d5428af3cb3f85d437e6f5190e09188dfb2071e0f3edfdf0c45417d749de9af5a228eab65e060e1457b967a7e2ef8bce84f6a0639324173fbe8274de6558a4778dcfd8da6d88e3cb383f372a05abd1705220c1a29537305ca0c1cf93c3281a22440d8e0dfbba0e2c64dfc8e7578c3bea2ab0964f6b372b7dff2b6bf71321fde62f8bede9afa9fb75284b3df4694eaac4e7e195583769625b73fe8a305b4236762f3b7d1a28c4cf80fd89a8d6195d9e3ce6451d681bc47e6452963ec33158fb83687c91df5e286ce60116ff4b203ff55f5f17ba23c8e7a281e3ce67512e306ddd3c7a78c4a13f8df91306454b129fcca819141060af48e8bb977e7a0454ab78eae1acd8a175e5dfca88dae0315fc6340c28cd9bb305cb1b5fe6b7cdb579a57144ded36c87dcb3af73d8adfe59f2ba69ffbfdaaf5616854a4da3ca205db900d5cf074d2fdd1dc1d82e8d382b92b1efa636cf6ca8045d3e98df0d8f3a2fc3cd5906f20818c8a836ad77bb75b59e133e5d49f4fea25d9fd5e68bea0edd9e0c13d00fdf1e81b96f9fbe3cee57aa2b9a63ffd678ccde5e62dca7084d02ec943868fabbfebb55b41a53d67a9525ba4592c0fd5d56bbe384689cecc13faba08ec065ead989b43c0c2e671763b10488c5b2b42c8dbb4325db8baa9f7f9f1e733a24e4dfaba490b6b6fd5c275adfdf2fc797198db0c428ce05b99d455a6ff17452e40fe9ce372f4ec4a7b59c33aa5ffba3f564bbad00e4d8b0868fab4b33)) else (if i < 3000 then (0x1333232010212123022231133312151314341002110211332242210202122321223263113001101122233124311331124222302341200201202210241541102035234441133542410321414231261235313242312252121212122230053021075334031331322010301101241332032031130152) else (if i < 4000 then (0x7034d84b4d225d0d7b3394c7c2f0d83c00) else (0x29b2b900f3721621fd0472752e031825e0cd3f51f82110ad25a3123403731d405e0e60f11cb2fe3283a43e126e00d2832bc0fe22536c3b82bd30103331034f1d40000011b33873d904f0cb33124f36834c05b0170743243663813303fa3863290f10250581513f92e13413530ea31a3aa3e80810b206b34f1a936a3072422fb0d31cb3fc0893f71f505c0fd2c109f11b1921422fb1a00411f61e330d3081371082cf0462651ee26e3b314c39b0861532e42c338a21e17f1b22d83970d118c1f93172410d30431c60ce03435a1121903001a73d30bd38029838c3c032f3b129c3fa11c1080fe3590910742a00d434337a29e32f22335e07339c20b34c1a420209a06f0c40c032b1bb3cc0ec17709311236b3590f23fc3511ce2392b107502718f17b32a0b00653891b339e10e03a1010381d33033791eb2963951a63ab3542cf3dc39b33031c0a50db0191011d22132ca2211720e921a16503f3fe3bf03213a00e1521530431f607534e3d202632d2783031472273921ef0ef2f230915110a3433062be3722d20952f60b439d2aa3371c11410580b81af23f2d309a0e515a1b036116e3300f50233ff1b43c035a20c00d1342422a224f0592cd20f2c20093b20d82b32802c42891021513782a62ff1d93213ae0e63922b723632c11c32429401a28905e3ed1a00063422b526e3b621328610534c0010aa10e2e21ca0bc00a16302e10c0ae1df07832816119b1f63320f83ab1d00801b51503a63be0721a12041d12633791821ad0d83c81df2c339537720d1360023be1a420e1620202df3041ff3192390763080283b63d60ec10026c3ac12a29b30f24f08e02e3942d50ee3860b93232ed37034339617c37a00a13330213b0433a80c60480a115835c3d503b1130002251780c417a3980800c306f11d09211020a3461f91e30491c71de24e2f522138c3693752532191243e73b32d23511411a53c208923b22a)))))
def chart495Data10 (i : Nat) : Nat := if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then (0x67) else (0x97)) else (if i < 3 then (0x9) else (if i < 4 then (0x7) else (0x2)))) else (if i < 7 then (if i < 6 then (0xb) else (0xd)) else (if i < 8 then (0x6) else (if i < 9 then (0xb) else (0xd19a708b68049043883a641fd850a4604528a20732081dc3787b0d6caaaa063a2019c2fb4c2845402b853254d41a104f0972a823c4454410c1f85b07642921033548d1098352056549a502384409c0f82f036c112033064804c078170160dc03803))))) else (if i < 1000 then (if i < 12 then (if i < 11 then (0x5f6bfb007bdcf4f780ee073bef7f780df9deded775a79d7d6fce018c0bfd9efcb5f3bbb8057029816c09e067025ff6808f6de9ee00feebdfd2eed00ec06ff9abee00cc05ffdc015810c04e06b011ff5bf3dbdcfea005f7addde009806c01fbde005807c00e003) else (0xe41609261a72b9ef8df5336ca5c43133c818b1c3)) else (if i < 13 then (0xe40820062d6f011044008058caf9402b659cab8502e8201d814b6003c0a39430e80289f94f27654c9ba90660c80978c02184ac939332464215047024046c8bb386a00508010f21644c839a02060e07f81c4803ec7b9902605e0070ef1d639c0c0b0560460e80df1b638c6b9147e033c880d31963cc6391f186c12082701762dde23343002cc5783c68029c940ab1465401045062026c4b89f1260d03008f1161f0960871061e0683280f6490640736481dc378300d7282182e05a018c2fa60920800f80570a616c278e0096b01f00a03c010c1fbf87e80ec1ba509600bc0803305611c1397036008c0f8c42c005ce001b02619c0787f0162fc03803) else (if i < 100 then (0x1) else (0xcbff2e3cb2b29ec9bf243c89b1f9c74f1b0c633140c3e70bec22705fc0e6ff9bf42f81bcdaf1bbb8eea4ba16e60b89adfcb766d81b592d48b496cf8b32ec9cb1f6c41b05ebfbaf36ba4ade2b3eac4eadfaaf2a9da9e6a50a8829f6a7629b0a65a961a4ce8f9a312888a156831a0467f29f627b99e0e7689cf271a9b726b79a12659988e60097865a5961256694a64fa93124a1921e444908e3f38f123a48daa3408c5e2d08ada28a897e22587621b9862e15884e211d83e60db82be09081620027f75fa17dcdf517cb5ef27b29ea579dde467855de576f5da275e1d407409cdf72d1c88718dc3b7041bea6f2dbb16e15b676cf9b1e6bf1ab06a29a5f688d9e266dd99565d994d644d8f963218a8623586f60797eb5f2579c5dc17475ca16f75b256a65a1565058c960c57315a6562d54d54a54f053454a3519142b4fb93bd4d713444c792f24af129a49c924448a51f6476518444750f843710bd42150514050ff63f60fa83df0f5c3c88ef13b48ea139c8e5138e8e1537dcdce36a0d8e357cd2f3440cdf32e8c9c31c0c4b30acbf52ee8b892d3cb342c58af02b1caa329f0a5c28a8a0c27b49c0263496224f892323c48c42284881217083020407ca1e7877e1d8c7471c686fd1b1868a19a463418145d416ec59615e4554149c4ec13404ae123c464107c3fa0f6c3bc0e183610c702f30ae829009cc25b089c20507801b2061c168053411303980b5018804800a8000)))) else (if i < 2000 then (if i < 1001 then (0xa2616d4e2930b09a517f73e61d9bc25f2ba6339e41afddc058d6131f728ab1cb419109dbf375bd95cb2da037e75ee636bb94de2d198dafb0cabf0f6401243cdd3003153b98b46debd69ee6e41a7365f2e4d27f90ebbb25d4495dfc86cd5644c74b1bb77c94eb70fc1f41991bd4faa8eee02c6b7750be58d6bcffd24c5eff1897cb49e2c73733c9fcb1061eac8937f838cecc97640f6b6f53cab135c8ebfc93257f92a35039d7a908cd6fdc53b6fd5ad2b6f4ff2b5a58dbc08963718617954a4e038ae7f195e6bc5f00d674b462f9bac995282947d7cf9dc1d4a8b3970b0e2cfe9f733cd2d599fda9dfc4dc9f1b913bba03ecfc87c711e43abd48073c37be5ca8255014c494317c1ea584bf5712c86d36fc565f27bafcea7fa74839b99efa663cacef392f8f015231bd64ad370931fd27e61efa13cd1bc33a6e8ad27e057505d24ff95546bc53daa23cb5b1ed3dc7ca4aefe4366aba322be6eba769cdc2a24cf1c60cb1cd8ce627e5527d1916984ff950eab45d9de1b3d5f6240acd775a6ccfdecd21cfcf413149a1e7a77ed3e46ea5e79194a4e86c9d4d12ac438ac9b2089f1f556f769623513b48adf015d2c0a83bcacd5178fc7d97db9c5d7ede5378b4685dffab979f6da188d2b88f68c835cce56409a6dfb8e1f508e8ab009ed6062d1358bec9ee8e2dda733d259f13ce2277514553df2f8903f27aaa07e219db8a6c3227c5f61ac9842ee5e02c1934a0f76d6fef646d787ace6a4be79a0a605f4fc875d20a686f9bd3beb47b1d2f349c33e45e9fe4a2c7d7ce738cf0268acec5658be74d31203cbe5f2e2ab965b6a1e97535b0a2f0eca687618215513ac1d8e6e7599d7c67efef43e435afbe991c5c78c43fd24da9ff3320f17d77e93a41e9ac39d7b209fef73bdafc4f06e7e77854e94b1fb946eab60b09dd4af7fb07baffd324729acd2f7f9901ddb97f9fda37d405ac885b4712ac42f2db4a7beed27ad84ee1b221de02ce1f3be998a54729bc5a378affcbcc3b1de592ac80d77bbbfd83783c150e0941c95938f66f8add39b35d9c7bbf906c1cb096d81188c8677d31c9939ac236f6ecf1a4b4567578b25b88ef698b3a591840baf781b2f3831fdef20be8df78d06534493b51e6f5ac49a0dae8fd293946602862ee42f3d36cd36ff5e3f1f65f6dcbcca84095762b6ee64d5b61f74b017d3d6ecae596d919d56757f7a8a07f37698f5ee8dae378afc4c008ade83e27d6070cd78be819e93743790e80397a6e5419589361ae39257fe906eb70c429b7cc7fd7cdd74a48bcf365461e958f08426a36be3d320cff58d92753550b43bb697f12baf3de334deae7c3ff9e7d285234a49f78cf835fce5ff2a93c898a1b72596d1758e6a75dc9eebc40dadfa3f4a4e570c384b9df5850c0a84095604811ab769b178c70799adbbfd830137d3d78ccdfff5f57) else (0x5178909aef7fa9a3db771a4b7c4f079f1c1a47b27c7a7ecf5afdbf9b5bdc3bc5758b4604ffdd42f9635c78c3177612d355d3e4a2d26a077d3548466bc2cc5488ea394e9ef5821568a3871dcfbcd61cebd9d62ee791cda9f4676624b1af772b9eadc41c573ed5bf825b6513573c8e5439d58e1ef4d3dd9182c1d2f146ac527cbbe15677e21eeb60dce8bcff950eabe539ff4e89b33e892c6b1afe590eb15b2f40ab7cafce74a82571f78248b6a3c90d78fe2d73b780be9e87eff60f79e092d2f787e5527c3a2188c8677d78cdfab1bbfdb0b1cd84e76d4c7525255ab033caf82fd58cf977712f1fbc7afda05370eec324c72c232efd5a2b322d1952f31a753b623f7e116ec3a4933ffd5901ae6eb4eb887b3d84753893edb7a7fc6dfac8f3650942c408bfe356bff4831b770dc164feff53437cf19fbe09f8f5546b853ed6087cd62e338369f7279f8331c606c2723f5ba8d60892c2a71313abe65530cabe21f27370569d730e40baf30b1cd44fbbf9a20b09dcaada7a8fd9d6236bf3feaff244d5c83ec1a7cf7b3977a0f5c6e2e5abe4ff3cf920d96e02f9ea8506280584e0aa50f0ba1d1c05648a803678e75ef7bd6e46493bd7f18524527391faa8835971b92b7e49bf65fa43a677cd82b4d26cddf1dda2c1e1ea81f7d0dc53b95c35a50fa394de2d1a96af215b9f07febcb1af9cf7aff8d21a35bd4c08757ebf678a8c00b18a39181d92a8ea7563dc15c0bc3283efa2bf7807be5e0f3fb9ec9cdc7a0a6dae84fbb08eaa4a4bcf6b8affd135d39c97c79656ae55389892dfd3f8b8f0f9f1a91b56449ae63322d39e9f99afdffc34f858cd93f83345fb2ee894124fb5d9047538aa7b5ee)) else (if i < 3000 then (0x3332012424314111260452113242211222011422301203322421111211510331211244102021324211103141210511511212421021300444212432231114400005211721000325251414132) else (if i < 4000 then (0x240f76caf53a82321084400) else (0xb91241f05a43784b088594208543b8118cf8183fa1bc2002739c7c4e59c11d8018bb1ca2bc660109630be0bc3398b33a14c319e23626d0c89b50803ac170ef0d4418d203e146088028992ce624ef88e0e22442c1fd3123a03195121440c28113078038041c22ee7f8f28d30a263c97861274174378143ce33838073044138091fc0ac064279f00884c4aa9090ec4e0249b900a344010423a2070d90120602e0f79bd146384768081783449d94d0c6108898690121949e87c15a0d81d8df0160b07718e02c06c3300f0dc014e70113083cca69101ec254da9c80ea6243b9a20040a0569010f41a8c38790205e04688036a1640f19415e39c0f8780105ecf99c11a0034ff94a05416c1d0580667b4cf0a304c2b00704931c62c240760f61c8f38350c6118689bb3e00d4e191d04c0e4651310dc1b4220690f6654111d31201ac7603c0b6080c89180e26002194f0346a03307913e6483b0083ca78cc68073684403006f05e2c4c38720822d4829981ac008001f33b4310e5036040014e39d93ba09c041cd3160b02f8b005e484298db03c124f8129358190c01f005c0800e1e1)))))
def chart495Data11 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x33) else (0xe)) else (if i < 3 then (0x5) else (0x5))) else (if i < 6 then (if i < 5 then (0x12) else (0xb)) else (if i < 7 then (0xc) else (if i < 8 then (0x5) else (0x9))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0x304844a912004f0964118124226010c1f84707649299033544caa5502f0560dc13b306491128801f0362918510a25404c0781701608c03803) else (0xfd6dde017fdafdcf9e01300fbde00bfde007003)) else (if i < 12 then (0x467d0edd0d355df092ce3) else (if i < 13 then (0x243c1c84018cbff82d95c605306020d0e0d012c8e43460fd704f1da10c0a00c0bf3038740084e230e0ac3e330d8dc2f901e251100f0584c0e03) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0xfe7d2e9384da341c3ee6b42a39c2548be06791bc6596950515390c0264721744b0ac00) else (0x1e1d5c7879df11b15733fa5f625947614fe78f6920e0f6baea0e8ab44c3cd597bfe37602b534620a8f226f9f1720c9ef85d7532f77d8b0307c697d8854e2f35257c05e175fc7bc62d7cbfca35cf8b917a7d71bbe20576cd62e70ac6b6def160663eb995af3f2e35113eea635787d5eb4b990bcffca1858786ee9ae882e6e3aea7ebec2)) else (if i < 3000 then (0x1103100322f000) else (if i < 4000 then (0x0) else (0x900c1a0f091d026713301c0a6f2d144e63c0903c10140b0303e05080743015)))))
def chart495Data12 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0xc) else (0x1)) else (if i < 3 then (0x1) else (0x1))) else (if i < 6 then (if i < 5 then (0x0) else (0x0)) else (if i < 7 then (0xb) else (if i < 8 then (0x4) else (0x7))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0x0) else (0x7de)) else (if i < 12 then (0xa) else (if i < 13 then (0x1c883c240902c383) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0x0) else (0x63b)) else (if i < 3000 then (0x1) else (if i < 4000 then (0x0) else (0x0)))))
def chart495Levels : Nat → Packing
  | 8 => (65,5,0,0,0,11,0,chart495Data8)
  | 9 => (465,4,0,0,0,14,0,chart495Data9)
  | 10 => (302,3,0,0,0,14,0,chart495Data10)
  | 11 => (28,2,0,0,0,10,0,chart495Data11)
  | 12 => (1,1,0,0,0,1,0,chart495Data12)
  | _ => emptyPacking
def angles7 : Nat := 0xf00c00800800200200a00800300f00800800200200200a00f00c00800800200200a00800300f00800800200200200a00400400c00c00600400800800400400c00c00200600200800400400c00c00600400800800400400c00c00200600200800600400800800200200200200200600800800200200200200600400800800200200200200200600800800200200200200400400400400600400200200400400400400200600200200400400400400600400200200400400400400200600200200900800800800200200800800100900800800200200800800900800800800200200800800100900800800200200800800400400800800600400800800400400800800200600800800400400800800600400800800400400800800200600800800f00c00800800200200a00800300f00800800200200200a00f00c00800800200200a00800300f00800800200200200a00400400c00c00600400800800400400c00c00200600200800400400c00c00600400800800400400c00c00200600200800100100900800300300200800100100100900300300200200100100900800300300200800100100100900300300200200500400400400100400f00c00100500100400100100300f00500400400400100400f00c00100500100400100100300f00100100900800200200200200100100100900200200200200100100900800200200200200100100100900200200200200400400400400400400600400400400400400400400200600400400400400400400600400400400400400400400200600100100900800100100800800100100100900100100800800100100900800100100800800100100100900100100800800100100100100100100900800100100100100100100100900100100100100100100900800100100100100100100100900100100900800300300200800100100100900300300200200100100900800300300200800100100100900300300200200500400400400100400f00c00100500100400100100300f00500400400400100400f00c00100500100400100100300f
def composites7 : Nat := 0x123000000001032000000002301000000003210
def chart495 : Forest := seedForest 495 12 #[(0x26ab080334eebe8e6c717b9536bd844e8d4938ace0a998aa056d91032354763b1324c650e8259bffadf4631e132a4513b1baa4908dc401052c8a7a608173ef041f25e3241c027320d71aa766af5591244c423e0c7814007ccb3a0cda76d6c89a,0x4890a00144e288448004b0126bd050e85097a0a89f99c4a196091030210742f13808080a8219a5908442118021a0192b09e84188de10411a88878409031ab00112183200c007021c61427200f55812400423e0c3814007c483a0cda4694c01a),(0xb8e35e04aa0ca4c354897805b0522374e8f805242385cc4047e4e8d25ad2ad05434f26e4b16002a65247425de53996c82302c619d5a59624be10f8fcaca1ce61011e855308666d6390a296706c3781c8b28033040634625042d6070a3eab9c5,0xb0225644020c048b54c9480110020314a04001062040204041a088821040b80402422624104002014205c25c001086802200841401811404000030840ca00c2a01068150106029c19480806008230088a2001104061460000056020a14a3985),(0x5e50de42b29ae80259324624c9b29be8467217b081b3c027db73b4e024741063280849dc2c3bf684400fce9a84b88b12bc035c984265a0ef25aeba932ead24bb1862cc933e2c38638e25c3d0654c86722433c927b320653124828d03d6182658,0x5010ca020280190200b200056c008b08141000a08012402ac8202160043010212800401c24021084400e028a0118830294030018116500ab098208912621243910080408164818028604814070488432241388249200002104828d0116000648),(0x4f6204fca82c04716c8de9b252e9ec50e31fcb6935855e4d4b956a1aa60284628d7c25b2364d7d40156eebf820cc406bd744510c4a081a15733bd4545c5c9b9e28d2949048935335d623683bce9a7045e1844f5f2908a2da52e10285402cbd9e,0xa630590a80804210e0d999212ad2040a38bc3413585165501150a10e003a4420779a081020d6d501770e86460c4406141085840488808146030c5045808908428e29086489201357023680b84905045c184431b2908a25a12610284402cb996),(0x0,0x0),(0xb20c6d99827816c2827f20be6b12a53231d1a5aca4432330c426e376509281cb8bca320be3c42831f8508069230665117bc303f360942c729140e57e0c2a81780f084aacb7cf85ac59523ddaa1a041aad68fe1a21ac1da499b50400d10414f03,0x3a0404980a2116000377a0244902a22010d085a5240002004004620001820140a848000b42c42400a038000001046400030110e2401028204100812a0a0000190a884484304b088c1902105820a0408a540cc12202414a019340000510400f00),(0xe0e302ba7d0d6f34005860414c16d6ab048d4d828a3b3451293d48d89a29da656dd9198b26b3cb5102d290134ba51ee4419bf4a73d07da8b62b28c4a7524fcdccea495601ae90d87b29892b19931ca89055ad0240f9ea22003f4bdb74920d076,0xf061829a3b490eb1082268004c9e868201a14c82083b345309256050100b5041399911892091ab5102d2a0d203a03480401a36901d058a8322b284631404dc141ca0846050c10d03268140b999314a81051ac0240b9ea02003f01d974020c072),(0xf052b398e14a24317808125e880b701d223e32004ece83d293929aa0dad09f03a1a2ade541808bb49e81e052566652464c4cce03a8fab19cb6ede7cc119b3b13017828f30d5a77046a746a8f4b361745839010d0a6a7a90c78725672a51f0316,0x1421100a44820117808131a100950118a2e3200584410d512929881da48ca0a41928dc0900903781681f450d6620004486cce01a4829014b67d6644519a9902403008728900671020f06a860b161345838010d024a6a10c68305272a11f0016),(0x1ed74371595e979f6878e43a569619dde00cccdde04e928f48018559a325684094b0c7c98e4036706c7152038db24a87e1f814d803b9ee9b4117010b1505362e1963b69c23198da81f899003a9ea1a31845bcd8845c14866405db84af840021,0x19838250494e140e0800249a000491c4c0030188200c9289400000502300a0400000c749820102600041400181280003c04010d002214489405301001c10362c10528098220104080588504020ea12008413cc0840014846404c000af800001)]
  (columnTable 76 0x20001f007c080027001b12000c700670a0033c01982000c604650800318019420009c10644a01270419020010f005e0a0047c017020014700570800528015a38014f00560800518115428015c0054500057c015020018c004e4800528811a2001582044c800560011328025a00348a00a3c00b8200298002cc800a6002b238029c002c4e00b1c009c2002c202269000b3c00982802d80024ca08b0808922c009c10245000b70009120010e801e0800c600073200318009c8a0843a0070280b18009c0a2043a00582003500015c800d4004552c014604150a01d40045428831800948c05d400450200294400d4a00a590034280398000cc800f00001f29010e800e0a80270411130019f004c0a0071811144001cf00460e007700111280297002d0a02a6002b0280ac202261600b7c00903803580014d600d7c005038038f000e0a00e600232300b98008c1000e7000312a02c202068c82b0808182803c80006d000f3000195803cf00060a40d4004153803d400054e8ab0808104003d80004ce22e6002105803dc00045a00f780010) #[[],[81,130,118],[48,33,133,118],[48,129,82]] chart495Levels angles7 composites7
def chart511Data8 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x19) else (0x1)) else (if i < 3 then (0x2) else (0x2))) else (if i < 6 then (if i < 5 then (0x5) else (0xb)) else (if i < 7 then (0x11) else (if i < 8 then (0x0) else (0x0))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0x5545486d15302f056901c430279008c0f827036e3993013798982bb00f01605c03803) else (0x1435ea16f0001ef6480003)) else (if i < 12 then (0x0) else (if i < 13 then (0x0) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0x30640) else (0x159bcdd05f9888ef67)) else (if i < 3000 then (0x3) else (if i < 4000 then (0x0) else (0x6463)))))
def chart511Data9 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x32) else (0x34)) else (if i < 3 then (0x7) else (0x5))) else (if i < 6 then (if i < 5 then (0x12) else (0xb)) else (if i < 7 then (0x10) else (if i < 8 then (0x4) else (0xe))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0x1526c86e06b8d3484eb067b6a196a8acc0c71862fd203a4694c01b90b71676e8578ab80155053942146dd1b338e74c26c4bb5068c24c47b0a364990db08710622c3fb680f6d49c34227181cc3786b4c45d2550670c61dc2f89f0b62ec2ba60aec6d1db30409611d98043a2013c1fb8875ce101b83354cc18ca02b750c9a220270460bc0f83b036c0a990138cca900781701614c03803) else (0xeb98e9d8ebc8e7980143013fe5d8e7c8dbb09fb401370133013b012fd7b0dbe0bbb0f3e001270123cbd69bd6a3decbb8011b0117011f0113012b010fafb4eba8e9b8ed9801070103c35eedc8bf90fda000fb00f700ff00f3d3f8eda8ef889af800eb00e7f9b0c37eebe0b7b000df00db00e300d700ef00d3010b00cfafa8cdb8c7b8bb6c00c700c3ef909bb6c2feab7400bb00b700bf00b3ab6ce5b8eba4cfd000ab00a7b768ab96009ffbe000a3009b00af009783fea2feebb0bfb0008f008bedb0fba0f7a0afd00083007f0087007b0093007700cb0073fba4efa0cfb0e7b0006b0067ebd0e7d0afb0005ff1e8f3a4bf34f3b000570053005b004f0063004b9b3c9b66e7a8dfa00043003ff9e09b74a9d69b6c00370033003b002fedd0efc0af74cf9800270023cdd89b7ca37ec3de001b0017001f0013002b000f0047000b006f00070003)) else (if i < 12 then (0x462b073) else (if i < 13 then (0x5000dc0c688a0003f00ed4f06db2b827f9003300bc03700ae27ca2f00232c00078860001f006c027005d7007c00680003c00b00c0013001c003) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0xd2ad0ccf1cd5cb4c8dc6ec49c2ec0fbf3bcfbadb7bb55b39b1eb02adeab2a86a62a3fa1d9f99de9c49a19839669419198f78d38b489687985b83c81d7ff7e27c87a678976874b7267036de6c469b6726426216035d95ad59157455653751a4ef4d24b949447845743a41c3fe3e33c339e37734a32530a2e62c62a728926b24922d20c1f21d41b018c16a14c12c10d0ec0d10b609a07f05f03a01d000) else (0x1a9199afe4954f3955ccd78610977d0494cbb1b2a9c23e6495553ce88201588ba51f9af15ec951c2aa25dfcbceb022dcbceb0054b8739f53f45ae82cc23e7b2bf0d730e12efacbf9ae2e4a23fce6d3b44e1117c9b1fc69fdaa5e758217224e344144bceb00b8a79531e7e0d99aec6426bfd45ee98720e0e75f039b3adf2179f1e77a0bdc538701d6ab8f414a127ddffa01cebbf41b3af7d190d7f5b2a79dda5f86b9fa839d7df53675d7d721af63fe6bfb2543fcf3ce89771f9eb2a3f73d65d9373a23fcf5d25c65d917aa23fcee704bb3d9ed74e8a6e4e91e2ed173269cb296271d2756290e747f5cef612a925639935512f29b1e1977768f86bdb41bfae6cc0e75cd5ebfafacc6d3bc79559b21aeef84d7da5a50cbb8b304bbf3658bf9d99be1af4c1c86be26ebfae67565dece3d7f5c99a3cb1166c7da62e2b647e931854ca1b911fe774212ee0ed9d32ee4e5e52eff72fc35de9cdfd7ba7aff5cedec95e7db954d75b9eb2a39abf9af4a3afebcd75a6b148dbdc1605f5bdc1816d6a6feb2aae54f3eb2f5fd724d30cbbe26fcd745012ee54f99af0d425df2df085dd2a4e0620b63f5fd7072e66b)) else (if i < 3000 then (0x1412113110111331273622126302021132320321313502022122) else (if i < 4000 then (0xc0f4e80) else (0x5c9b57329bb2420310bdd5a76f04b0395b279858158932a3a5a09320285483251295f8e15529972bc5f9064ab85dafeda7f91c965ca6b9c4647008985e02f99a022dcfb7f9aa46926d4f540a65f30d4771914aa43471dae6672793b81c6fc4ca828f3bb2124769e7112afd7db4cf961297cc52d4a3)))))
def chart511Data10 (i : Nat) : Nat := if i < 12 then (if i < 6 then (if i < 3 then (if i < 1 then (0x77) else (if i < 2 then (0x1c8) else (0xa))) else (if i < 4 then (0x8) else (if i < 5 then (0x1e) else (0xb)))) else (if i < 9 then (if i < 7 then (0xf) else (if i < 8 then (0x5) else (0xe))) else (if i < 10 then (0x509982a41f6982cc340684e5077aa01d639dc70e36a09086f8f31b63dc6b9526c833d950cb4c431eaa3866142fcba384600651b40b71662ec578c315634c53b8a844e084f89b64c589a2362126e4847b9011699043b242e4da83f8830f625c3bd768001cc378a30d6d81cb3800c6d49c605f0b6c102baa68cc14c27b0695411e2237268ce201faa207610c1b84b066dd0c919605609da5023a64dc1b301b6054400b81f0269000782f01619c03803) else (if i < 11 then (0x1f7c3dd769f697f40e2c1c3fbb6bfb1dfa2ff8037f06f60e0c1bbf9f4d7f1a7f37ec036f06d60dcc1b3d3fcff612ff01af836306b767ebbd86faeb7dc0d4c1a7db7cb3ddaf63af6034706860d2c19fcbd6c6fdb6e30ff03370667e7c39e77fe4db740cac193832f06460cec18fe3fc0637bea2deb6fd0ef5c0c4c187d79e9f712dda7b7030706060c2c17feb7cabf55bbbcf402f705e7aff31f76df4f7480bac17382ef05c60bec16ff5bcfb4daddadee02d705a7c7bafbe5fe8f7c40b2c16382cf0587af3a9bf5df8df540aec15bcfecd7717ec3dfc02af05560acc15382bf05460b6c14f831705373ddb37f5b6ea7ec0a4c147e7dce7b9a7bbff4028705060a2c13fd7da96dddeb3df3027704e7fe839fb6f9ad7bc09ac133826f04c609ec12fd7bab7d5dedabf9025704a76ddaaef6ddae7e4092c123824f0487bf22beb73bae7d408ec11bedd8cf71c7ea7eb022f045608cc113823f0446096c10febd6cfb14efb5f3021704276dfbdd87bf29f74082c103820f0407be635dd4ffac7ec07ec0fbfbe0fb7807cc0f781ff03d77ed27fb51fef74c078c0efcfdeff4dcfe27ec01d703a6076c0e781e70396086c0e3829703860d5c0dfe9fef3cdf6e2dde01b7036767db7d957eab7bc06ac0d381af0347afabbf263faef68066c0cbd7becf7927fb3f6018f0316064c0c3819f030767f297f75f4ff5005ec0bbcfeef37db7e277e016f02d605cc0b3efd2ff58057ebef4efeaff4056c0ab816302a605fc0a7dff49ef9eeb35db014702879fe32fe4bdedfd004ec09b813f0267eee35f97becb7d804ac093f9f88ffc048c08f812f0236052c08bc7fcb7ec043edfa010b87fd4feb7f8010397fdafd2dfc00ff01f6041c07b811301e606ec077cffcd7edef931ef00e701c7efc37dc00df01b74f7b5f653fe01a6035c067cb7cd6dc031f3fa67bae778030c05fefb49fe99f6b5ee00b7016602ec057d6feef71f793eda00a70147e7b3ed66ff4a7dc026c04b809f012602ac047f5f8f7e9bec27ee008701072dfadf3007f00f7ffc39fa5bfcffc001cc037807700d6022c03380cb00c7aef23fd4ff8efe0016c02b805397ed6edadf96fe40097eed0023ffb400871bfbcde7be8007600fc01b804f0067fe938fe5fb897dc00ac013dff8e7d9f7a2bfc001f0036008c00be3fe002600bc007805f001603ac0038003) else (0x1477d9b522e6981eb21c43))))) else (if i < 1002 then (if i < 101 then (if i < 13 then (0x1002b001883f004470260e34481044310fe18010ec43736f044b10cc4b00211000391042b109c83861011004b0041f106c423105c02c520061c185040f102c1802f00a705c004030ffc4070fec4130fdcd9470d1c1c10003ef0fad69c291120019003e30f7c3e70f6cf802a003a418103d30f3e3c0ab000b473103c70f0c3cb0efc3d70eec3f30edc42f0ece34036108c024003ab0e9c1b818b039f02e03a30e6c03044f03970e4c38f01003af0e2df8004c03830d0037f0a0037b00600380ddc034c800a4c001036f0dac63c0d9de00bd0014000a035f0d6c0601ae035300203570d3c3630d2dec003003433400d9c3d002000cec33f0cdc3470ccc3730cbc3870cad1f837103230c001c0004031f0c6c8805d102400e003130c3d30029a06485cf03070c0c30b0bfc440a20248088002f70bccdc8069113432002eb0b9c2ef0b8c2fb0b7ca6447c1cc851602d70b4c64653b098044a02cb0b1c2cf0b0d5c24f812401f002bb0adc1a8420120239002af0aac2b30a9c2bf0a8c2db0a7f2c000822801d002970a4d7041210c40224028b0a1c28f0a0d4cca5031405a0027b09dd4440631cd0250026f09ac273099c27f098c6c03600dc0980025b095c39c5f017f0620024f092c253091e08051b10c07c0023f08ede4036b14fc446023308bc23708ac243089c25f088c29b087c317086d4f470f1bc00420213083d210048081c4e00207080c20b07fc0c402001b444e01f707ce3806b01440bb001eb079c1ef078c1fb077eb006d001246c001d7074c1846a00a5c10201cb071c1cf070e4c0ba03040cc001bb06dcfec4822dc05a501af06ac1b3069c1bf068c1db067ee00c4011e806f0197064ce487a003b00e1018b061c18f060f080449017b064063402b017705cc17f05bd1ec3f117344470167058d1042c01f40234015b055c15f054c16b053c19b052db80ad008c8041014304fdd8020b1738770013704cc13b04bcfccb3015a06400127048ca404430cc0445011b045c11f044c12b043d10815003b40280107040cf00517009c8b000fb03dc0ff03cc4c029d158820d00eb039e440280050018e00df036c0e3035c0ef034c10b033c147032c217031c3c023103983f500bf02ec2c0180168423800b302bc0b702add40600060c63000a3027c38c0eb0097460009b024c0a7023cc00068112c1200087020c0b05c700949e0007b01dc07f01cc08b01bd50006605803940067018d1405600d8c295005b015c05f014cb80660004b5000db41910047010c04f00fc06b00ecb401e00033170002f00016003b01640009c1b00142900970001f006c023005c02b004c037003c0c3002c327001c003) else (if i < 100 then (0x1) else (0x4fce4fa64f8b4f6b4f464f224ef84ed44eb34e894e6a4e404e0a4de44dc34d9c4d6e4d324d144ce34cb94c8c4c5d4c3f4c214bff4bdf4bba4b7e4b5b4b324b0c4adb4ab34a884a684a4049fd49c649984971494d492148f148d248a548874865483f481547e947bf47964767474a472a46f446d546b646944677465b463c461a45e345b8457a455b4536451244f644d844a944814456442e440a43d743ae436d4343431e42fb42d142914273424a4220420141e241b541934168414a412c410c40ea40c940a240864067403d40123fdd3fbc3f823f483f0c3ee93ec03ea03e813e5f3e303ddf3db63d953d753d563d2a3d093cc13c813c573c273c073bde3bc13ba13b7c3b553b273ae33ac23a773a4b3a2339fc39d939a939813957392738fc38d938bc387a385a3838381a37e437ac378437653734370e36db36bb369736783659361e35f535d535b5359535673547351434f234cc34ae3480345f3437340f33e933c433993368334b331932fb32d232aa328c325e323e321731fa31cc319f317731543131311230ef30ce30a1307f305b303230142fed2fcf2f9f2f802f622f3d2f0b2ee72eb42e832e5b2e302e112de92dae2d772d592d352d142cd92cb42c962c6f2c4a2c132be32bbb2b8f2b722b412b212ae52ac12a942a672a392a1829e129bd299c297729592939291b28ff28d428a8287b2851282c27fb27d927b72797277b274b272c270a26da26b4268f266e2644261025f225c4259325652536251324e424b62497246b2444241d23fe23d923b8239c2370234c2329230622e122bf229f2277224f2222220221e121c0219921752151212e210c20d420a7208820612043202320011fe41fa91f871f591f341ef61ed71eb01e8f1e561e371e011ddf1dbe1d921d611d3a1d161ce71cc51c9a1c6a1c461c241c041be51bc11b9e1b7f1b531b331b091aea1ac91aab1a5c1a2c1a0b19e419c1199b1976194b1923190318e218b9189b186a1823180417e317c117901754172c16f116ce16a5167a16571633160615d715b31594157615591531150914dd14b8149b14651446142213ff13d713b51392137613531334130512dd12a41283125e1232121411f511d311b21189116a11441128110110de10a91089105f103f10020fe20fb60f880f5d0f0d0ed90eb30e880e5a0e370e120df40dcd0da50d890d5a0d3c0d1b0ce60ca90c880c550c380c140bf20bd30ba60b5d0b330b0f0ae60acb0a810a400a1e09fb09d109a6098009560937091908ee08b1088d086b084b082707fc07de07a707860763072306fc06c106980679065b0639061505ed05bf059605660536050d04f104bf04a0047a04590438041703e603b8038c035d0337031102f002c902910273024c021501ea01ce01ae017e015d012400fa00da00b3008a0066003f001d0000))) else (if i < 1000 then (0x8f448f278f058ee18eb78e828e568e2a8e0c8dea8dc58d9d8d798d568d2c8cfc8cdf8ca68c878c5c8c3d8c1d8be08bbd8b918b5b8b1a8af88acf8aa18a758a568a2f8a0489dc89b6898f89738948891c88ea88c188838861883e881d87fd87d287af878f876a872f86de86c386a28668863c861885fc85cd85ac858385578538851784ef84c284a284828463843b83fa83d283b2839383728352832982fb82d282a88282825c823b821881e081bd818c8161812a81078093806a804d802e7fec7fcc7fa37f837f627f447f1b7ef27ed37eae7e767e567e2f7e0d7ddc7db57d987d757d567d2d7d0f7cef7cc87ca87c8a7c5c7c377c137bf47bbc7b997b737b387af17ac37aa17a7f7a587a357a1479ef79b779917975794f7927790878dc78bf789e785b7828780977cd77b0778b775f7739770476d976b2768a7660763275fb75e175b8759c7573754e752a750b74ec74c974a67482745b7431741073ea73c773a673837366732e731272f372c7729772777259722d720171d771ad71807152712c711070f270c770837059703070076fdf6fb06f906f646f436f216efe6ec46e8c6e5d6e316e106de46db76d876d576d356d116ce86cbc6c906c5e6c356c086bde6bba6b846b5c6b3c6b006ade6ab76a956a6d6a496a1d69f369cb699369696942691768ea68a8688b686f684b681c67fb67c5679e67626743671166e666c466986671663165ef65ce65af6589655d6542652164fe64c4649f647f6461643c641463e363bf638a6369633a631562f262cb629f62816257623461eb61cb61ae618b616c614c6122610460d460a36076604860195fe95fc05f9f5f7f5f4e5f2a5efd5ed45eb75e935e755e375e165df25dd45db65d9a5d235d045cd75cb75c8d5c6b5c1f5be25bc45ba25b705b4e5b2e5b095ad95aad5a8b5a675a465a1859f759d35995596d5949591d58e658c758a858865858583c581b57ef57c357a3577f57605739571b56f356c1569d566f563a561e55ea55c655975579554a551754f854d354b55477544b541a53e153c3539f53805361532252fb52dd52b95296526c524d521551ef51cc519d517a5154512a510d50e650c850a85089506a504750215005) else (if i < 1001 then (0xf4ab6fc0bc4217c7d5878ba751d200e4c2d0bb7a386aefb33b5ee2b585a533b23df9dce5be79df2135e1f6ad1a28996ab4ce56296fba541a30cb48016cdd9f787112e7de145d5fe51041e3ecced55f473b757f46684ea6d370098cadcf1ab09e075cb6d6ff82a43227715ae5b502263b565a8f93ef0df7f4431c9e6e0afd1d1e3c1daf98109703787275c3ef3f927090f08db735bbf764e107e2115e7a9a3dcd65a6abdc70f729e7cc22896c216b9a7387344b03766a82995963555153f023a07bb077c34fb9347404c503dca56e3ead08dede826e7de3ed6ebc2f0f0ea6690ff6afe004c49a08aadbd7cb738fec88573fbb78fa1534429bb51d6dff04651d1f7e161651b7eab3697609b1c606351e59ff5e270077c339b12b0372cfe5e9a26b96f968c1eaed0f8b3449a3c5254119ee53c18cbdca209a6eb7e31013d14ced589a8ae827e3c148798e8fe54357cfe5eae13c3e1bf8f9fd9da2efa745c26efc76d58ad72db027ee727ce08dfbe2f18c2e68a676bedab84f3c27eae117bf9c5bfb9b0cd12d1b9bb870bc2a768bdbf3ca49bf3409c52d57369bf210121d6f39f6ef95a8676472726b8da7c2dbfe4abbb309a155383718c1958a5b1757ab2d1390cff787102dbde568103485f6b75f04e3eee947471a42781bfe349a7162010dee43af8e296a91afe1dd9763a9ee780528afec2ded1d7ff828e8967b87a6f1ac1df3cb612df0a4affc1ee510413ff643c57dab1784cd479b561a7e7e472b14b7e273e3695ee1b9c7397c0de0348b8fb77edb4516a3cb10ddee99dac2e683fdf0c37396cbe1f7a546a7c7c84d743c7b7ef9f560a6553b7b57e73e1adbd109e7ef5371ddfbb78fe6ea7a7652fef95af20d3c8779eb63aff29c564d217cfe8b7f7e71f396ab8dba4f36cf1b97339c5f31c26a5c1a2bc2ebe86adf74876eb631c9da200af3d90539d3f909fe395478b46b1a3f28bc3a8fc2734533ba4573d9053cc6cdb9e51cd84ddb7db3c6e5c7fc4087eeb73c368a6514ef10ee5368fbf983548553ff643b76a5a9fbb43b4547a18d796f86ef74cef764e307e1a7878228bc7bc7d99def0caa6c5c3185cd12c156943b4dcf0a1f5db9e1e3c2fe9f46d03be4a0195f1d19abb985cd12ddef52c5b7abb4e3ebfef9e7fd59a14716f728b6a8d3542d513f731fc356abf0373891f5bcacf87f57d6c747e51b8c27b0035b6b8065753a3c693002628daefdcc7f6af565b184d479c9f35cbf0242532cb73cd6ff6a009730ea6c796fb395bbeced3c29399494d3cc9c0afc57a386ccd676de67177b53a273b90fbc4068cf96f8fa73aab6786fbfd7fb278a1c8e396a3ebe0f02ea37f2972a3f6663fbc32a007d2c3b6f3919125badef0a9f4cd285a481eff43a4f184023feaff382bea745f6b7f08b0bed6ebe06c4a28d72cf1aa4f84b38e99542d95abfb3e1) else (0xcd8fcff29e94e2dbce60669ba43a43b4fdbfadc44796352f6e07b6cc749e634f0d01e328252acccaf7d8357ced4b6af86e3ea68f709a54f399de93b084e32de1a57b877a84d6ebc2d47a086ecc3eb35b4687069b6f00645c05f71f8f660ef87ddbdfd380c071272942adfa0c9f0b7f788553ff65869ddf4daaa6df94c5e59e20d9f74ceeb9d2daf9d55383627d19e68fce91995e943335a59f569e2df7a63b4a709b36e7bfab27aaa47af53d161e666fca7e685c69d91ba3fbd4a8f18f4c4b1d45b6f835425f749c86f729c9b3c395a2abba822ab6b748be77276f2115e7b21f7145c7aa43ef20ca1295751309cd12c3b79b5a35f3bf60eccaebe406c42f100df1f56042eb2492d98e5bf2c36256ef52aa22df940b533f05635ae1995b284b3d8b9a25cfb9ced36ca0906fabea7bec3f21fbe0ed423937bafa91e58d5ef564acd95e2a5ea79a65d93d5c241a8a281bacc720a2a2671cb675daa340eb96de7d5cf68588043c121f83d5f50f3a6274bf7ee8a1bb50a480ddd4e8bed59e11652a190572dba8cda077c368aea3a4f89d404f4533baebe4090be09b775e17425688b7e763a91d7d7db0aef837f3d4434a163510ce296ff925cf32a1351f07da79f309c51127cee4d1eac4be9fab6a2d9bda6d909b2541a3482bc79943d95dda873129269e6af7b56c62f72e576fbff7bcd105425ecbfbe56202c558d7af44b7c9137ce2df9a1fdf90965ca3542b1a95511f94f6d5c3f0241a11be31d074a4b986e415c7a8e8f4a5d46a8505f61aecac520a2fe6db9a68fbf0774b7d1ced5eada8241beaf547e221ed5dac7b010a631258ec3dca790de3a359caece79a673976a3f92de9d96396f9575cd51d1f817ea50ae9f0a1a89d9b12b6ff9cbfa5b9c72dfd0e96d542b1af850bb7f1e1a1c875334a7aa81bf3f9c54ae83efffd57ea79e27120aed8d6d4709b0bc16999bd751d2042e7153e16df4c9a8ee97efd05a1f6fc4cd380b1e57f290550f69426eec796cfcd06abd1fa0bfe4251542df9fc970be7d3db7e56259efab34a3aae2f80dcd195d3f64f37e685c72c6efad30f6fc6b76eb7c5bdbc26c4afa9a751d278fbf983b579106be562534fd5a9195c0df94703a56df2c5f6b00e06f109166396cc084bb3de145d5dbf3f342d5963563bb4d979ccf5d5f1cb45ef5d4c749ea40898ed50abf25fa546acb7e62d1271f2df0de61cb38db468f624d1e4104ffd905174cbb2d519b4c5c336e5654e25c378b9cf347be5225b7f18b553936358119521ec655216e715356414d4a70077c371f5346a2890f34860ad4f68c3d3a9b4d8fca81a28a891082b1abf0b6babea5dc622a99a53b2fb27a9f6fa2df9fbbec9e6fcdb735a3c50a6b6e7818bd69f7959cd5b4f0d3c394f13eeff5f260cd7cd6b59f83cd8f6eacd3cacc9c4b56fd827068eaebcad8fa4e41589)))) else (if i < 2000 then (if i < 1003 then (0xe0ac6b8ad6f765b1e0d5d4e8eb7fbe00dcc7330b85d7cd3c37b3c766d57ca0363f9b6aa9a35e349a28e92be720a796cc2422f09ab34efe3cd8feb90dcf26577be747ef829b1f15cc3f3de41bf2664b8cc6784fe7a659fbe30aedfde72a834a161a64f4520a7f2d706a7e685e733bdd86e5c22968ae6cf87aa31fafca00aa6fbba43a4fdfb2b9ea1ee5c1a328a6c3a9954d1efbdba8828a44b6cf35658e93d4e23603a09f8fb68a65c52d86ee1c2f8fd2fee06fa2b9ec9f214b2a6ea6dcd45f00d8e0425d9b60e34b8dc4474db47b652c7276998aa81a78faca9ba9a3d13ef85cd12cfdfde76650eafe1be1e6b765dab7266e5cef51f0cfb51d5d7c1a8b183344b8bbbc910409b9e790d14e8f81dba5be7c1cd394424598e4f9c15cf90a4c8bd78e8ef06eb0f1cb7e0a7c969a2ea6a6c4b67b9c4c135c268b7bef443f39478d77dd2c36b497eacd0efe4daea6df73a5eaf90a444b04dcf3aec3c58340b6f05701b1d43ec72dff389aa425b8d87b62c74cef54ef53ea68f18b448f3c1df2c6e9df695ee009eaa0650d6a2fd5c27554e121e2b29af962797adc4474ec8deec4dce8e73a5b4d8e03c1b6f9a22e535f0b0d895ebc730d452d8b7a1bed3e10c6a633495b7e0906fabb41cb98d47963dc91c33329c0783057cd950f9ae1178d3ab63f0bf0da3dfe2f6d3cd45f01212b6a7f29ce959df153527f90b615865bf9ee47ef85bd77b42d12df222ae96f813c8834a6afe0fb099020ae5b6b121be7460beef9f6fc36fcbe0b4f4acdbde68c7da8563dabe393c4f83584d74a88af5f6e4df812e405769d1e434346556202e0635f3aac560fb70fe7f549c16bfe5382b81217e0eb36df47bec82aafd9bea37ec4fdf5fe46a81604b79c2220d0f8774b55c8783edbf25750656bf31d27a8ef2361748749f14de61e09088c479c9f1612f71cb7ca172f9a3cb1a84d6ebc2b0fe685c721f728aa1f942bafe142ca9389c65f734af716829b26d77ec63f9ef5bcc749e6bbf6172a3ca245c27699745bf80ed9c32ca9ba9b7c532bb7f3937abf1272865fecb6429eaaf7918629bdca30c80b5cc6a721e78c2afd53bd4fb21e21d6e6b8a8dad0cd2d80de781035f392ae798486c194977df5ffaab96f9fd57ebf0d3ee4d1ef151090f44b47e73aacb7c44b58e5b3af12773075cb6ba9b838a5be9bec805a6c70bd7fefa2defbe41dbdfdf31c1a34f3b05c1b0d0e396cac4b3df56647e0bf15fc786872aa9c250cb983ae5b74ce6159a9b0e6b70cad9e79a060ade8c8ec6dfa4c7b14b7fb20abbf66f79c3423787ce7564f37e1cdb9d1eea8832ca04c7f8129e06b44a39c9b12c0de648d479fa3e0afe3a3e7d3348725d9c50a8787195e7de6497e28543cf3eb35f3f068ca1ec71cb7c34f0f034611cf57f9f9b6bab47bfc969b34cab2d52122cc733bc766c71d36fb4ef2) else (if i < 1004 then (0x651d1f73b51d1366fef07da7c5d3dca772673ef3ffc3f7c3e3b127b1aab18e9d7e53bd26a90ca8120d346b62d94977db3d743514b4608867b46560690edf85dfeb63a7f943611b3b239f7a20a144b58e4f9c15db9c506df74878beeb28e8f7ea20652daea5057cfede6884d5eecb46874b6aa863570a176fde1a78681d8f1da51d13ff3f2f9b8a5aa0527cc1a2f9fd0cedbcc9f016cd8e99decd9142a814ed0e2b682a08d9d7591a2b9ec87869f7268fa6c8b06e71f0b90f729a6783eca5b1d282be59f9fd74dc25be3ddeabda79c564d28626eaccef2480cafce8fb543461ecc1888f2c4f94881a724bbb328bca97a4cf1b828e8be09b6c5e174a2b6a6df91b06cd37344b61bce2ff7cf59218090eb296171f657836256efdc968d6e03cadc3f9621c2ebe646c1a05b7f36dcd34785fadd785f1ff518b8433d54fcbad7c3ab7e78651f9c9bdc38561ef52bfc54be2b5cb68906fab671579c69c8757c72d8fc1ead9cd32e85e9469e1cb145d072f2df2650df569e5acb2f3befc8ae7b2c435917016d340dc25be15dee90f15e40b41a75f27c84f597ebfae535f3c081a5357e7278b500a77268f4cb151f65fbf7c4cdb9e7e547e4377ec070ac6afb09e941adaf95aced151fe685ab2c6e47d5eb8a5aa2cb946acbbd50e0bce43cf220d21edd59bf0e4a1d50abf1fab3cab4eeb07fbe2115e7b2c6ed8577c1b3c7f8a9bb20a200af3d9622b2b28e393f7390ccfbc28cacee976ae7de686a15c35ff286ee1c2e84efb7697fbc07b4850ac42e3030dcacc96ea562f9cb33b0edf467112ffbc6bf6d21d27c4322439c876d07929f07b1adccb3014382f95c35edf86dfb9ca38681c56b96d2917e28551c5b37b4d03b17f249d61edfddeec4dcfc7977ed8e1805efcd0b7536f9500c69c842f100df1f567cadb5c4b6b7298cb73c3f97a969d927f94ad43d5b50650b74bbf5672bda7864b31208086f30f0363b68a6514828ffec07951aa0d9f74cef3eea37bc1c52dfba3fbd0563d2866559a85ef5b977538c17d7f3edfdcbbbbbb8980d7077cf3eb34a7d595ca1abbeccef200a7fec82add49a80d8c4fbe17344b3db8b0e95ddf0f2f3fa6b5af2df357bb278e09a54977ddbca7d794ffc8700241a6c4cdec8037bc409a0e0ef94a459af74874878b0b1dcdbf3fde2c8e426c4aed1e432d9e200f0e0ef8ff15376676bc693487575d04e271f4bd4f39fc07b9ac749ead0d63a4f3725550657ca440c2af1d2d0d4058021a094f98ed4d8f2dfebab1d278d28bdf74874813c58453a3d983111e677cd3c37b7626f30e56c4c7189431ad6256afd5c27b543469b2aad1d66f9a7dc9a352ca4b2f490cab818e8f8774bb5708883539a856ba57057f9d13834b7bc17eb75e59c7b2bfb5125206698077cfbdcc6a3cb1aa19121ce4fdde6656ceb96d252047b00ef97cb97d) else (0xfdca3765bef3e7c00aa9dcaf786f30f04e369011ff26e4a4382e15596f1d4d4d897edd89b0b413f1fe8716fc2bfe0dcf28eb9403623285ba5deba7d0e93cde29cd0d2aa58b6f57d475f453625ff7f1510be1717badc9c02f7fc0818e8e2b5b975a71f71796f9e7c104e29957548131dbf94377ba6775a32853d93d4b7bb46e7872de4ddaf6bda4ba733d7b0fc37df09ab178565270db4340efdf2808e83f29de93fb7026b7f08f0c281383cb7c2bbe426b5162010d048613515f05a78654d8a122cc6157e54029c733bad912fb7eae114da299452d8e721765bb51d68fe885d93ccf907d5bf34cab2ed5e2c353a2f228f29f8f2b395fa9e71e0fabe04834a69c7f6ff7dc001b47bd48ff1c95e2d8ddb5fe53cf98362a9dcadb0b497daff43a401d65372e3f51b9195daa1f721521bd8a8faef729d97d976ae90195e8e89ecb6f05bfbff92d45128e2db9e68dbc616dbbdebad8e93c79d26d347fad5b4f3c3ba4f55c6c48777aa655f8e1931c17e51ef5bcacd874ce727abb2fb2d51c40bb6f0a6576cf100579ec878ab09e06f6b6edd1a8f3fdea77a9f64140c2d6390f102e83cb7ce4abead8f56f1a2062debbdcb68077cd0b51e7e397dd9da97edc5d8f82d77bf3b1063765c10115e60b4420eddb19cf78be5b6fbe3c7236e7de4a9d48eb6ffcf98363c5b5c0d0bca97a4ce46))) else (if i < 4000 then (if i < 3000 then (0x350311110430521503332142233132103005323121321212311211430232412224222310120102604132021215111311237231331213232533541141201014413220122001320232234122223024311223231231613420300005421332023133121212412310001213221313210131113122221301513042403120050100112332223400511122232010221123112211240042041422131131411202321031441123624012324232323121314102215100131120242124641121133423521310442234310240520141303502321003422004423234630121123250222314311131127431) else (0x382d733cc7afeb8ebda527b9723b865fa785c76a1905d9594f1173d0dc2cc8b1ac4b09800)) else (if i < 4001 then (0x87d91357e7739735b619c067767f80e7a731c5e359b5125095f65756b97d878272d9b496232e5345ff1507eb11296f50ca8b2697a81781584638e762736c5108767b219f72a04e9317560aa0523152977ee4f8920aa61ce5ae2aa9e19fe5192354fb9745268a87717766a117f71377044579e23f773733b26b9414e020889224330373a054e16f297143082c00a23d15882a1854ee7fb91a4f17ae93977478c06677d26087e3b78617d839f97d9fc76b6628a956a74d5cc1bc5b87058a39875d944f00f7b459d24a7a71832f87bc88053711459b57d03823471c61b59f083b743995625031527696249ca5082cc2675c60f49ab26e5df7819427649fe8c6b2f78090a51672a24e56b1187cc2f989971219b8897902207458749307c938042098e59aaf79414052091a440575f682bcd0a87816f53f00be03565d44a5671c97db82485b5b372498954539d82812596647e62a4028ef5689bf9dc7ef8847d19dd93f6bc05d80e2852746e598b46757d6bb9ee84f8cb5e23f34e22e84f7537bda5df6e20f073954b51299351f59d2495f27bfb1248d30d82d8b3822b8749d4a226e4fc7a420971d7955715a78067d72c637a48789d5825d6274bda2681c171073462f9a590d29b1620c594728a6c49da11f5457db56a90050953180b64574825e5ee58787f34991782d9353127165fc7eb03a29f1ca98a8433cf84996f9d23245a37885c39137dc1852165977913cd77f90c91a0151fe97b81182778362a936bcc7cb6ed8209338658d78c21ecb6a7f45e4ab39279229240019888f950aaea8fe03b94e77b5710aa91a5c6123184b715ef5306a38eb814ae17432802e289b91751d88073580d6229769a39d875c80c96fa6f7a994c4a5b405cd233abd4ea70176a0a45191bc2c178c6ce1ac7fa9620475c99191bf65d93e77199c82555e8c752d6ae88d8e15b15a852088d6f0b885463c73d667270c59f599b3caea53c61aba087115d7ca52d7f68b086c61673eaaf98252870e97b5e46889c63b93e36556219f086296f5483d3367beb8155d370100d19f25a52c5a479d76974e71883453180754f66757b8e29495897ed56fb3d5e89c927763054971a49b2725810477d721c5574c798f71584857f5f79bd59a25b51e76279094b3823237b07b85155fd09b08d3296177ff9dc84c8019862d802a8292926ef6179f69fe9e842b931b0f51f43f5398ddbac7859a05ab5f67995aa50187f8102528c1bea91373f5852de813908b51411705699a52b0d8d49355342762c025b7761ef78e1e858d9249c752e599143a4178e56d73b9280f9573288b569be8259ca5c28b75a0b7cbf457f5306510a4b995625489672247477e79ca5085594e35457ac6567f611b7118801278525493bdb13783b478447cf9729105238b34ef7995527a4b4e72590e7dd1c77d180893a) else (0x81e6927097a8bfe75660642b962ba6b9e7b64f7a1672c3c677589a45f7c27de6ecb2695a1d77820791f41df2ee9fb96a97f70939d5f50249428b41780a177501046f2c18eb72293e1075987fb48b9117bd7347469b798c5ec5a11bf5a524039eb454127d43f18d98f90a5b157948e81484248a452e8f22cb493964b6b9256685709499348ae5146ec5202c26466f55b9b407185ea8c1baf00b9ce97d3241f09392d794c9bda9667e87177e957531413b856da79cbf87f97289bc8dc7952cd17f528aa87809427275c38437f073b8335490d55ba30b2c76f22615e41ba98064cb4d5b219235a0ff14b23028b9fe02b2bd8697e99717345e59b09e85f118b91b7688142c5788a8dabc7404987e27665fc7c91447c6be79057b255007b65e871a0568c5008666cf56d5a5060470bc87468809623e498d74176b592b253cb8187fb4845f26649c37337a252b7d8253ba51514d258e519392bc0b9a7)))))
def chart511Data11 (i : Nat) : Nat := if i < 101 then (if i < 7 then (if i < 3 then (if i < 1 then (0x81) else (if i < 2 then (0x2b9) else (0xb))) else (if i < 5 then (if i < 4 then (0x9) else (0x14)) else (if i < 6 then (0xb) else (0xe)))) else (if i < 11 then (if i < 9 then (if i < 8 then (0x6) else (0xd)) else (if i < 10 then (0x3004842fd822626602dd930bb166d91b00ab284d2853a60146c918509ba6427c4b8af127441a82a4116549a13661061fd515760f621c3bb7468ca825506f0d619e000730c623c2fb402e815d8105354d089a2172096dc8238434c813c1fa40076589b7368066d8817b5205711013b068cc08c0fb706d4ca80b813aa806c0783701616c03803) else (0x2beeffa018bd7fb9fcf7f8187060c17f9ffb3fcf7b8177afdbbee05cc17b05bc16beffa3feffb2ffc058fff6f7f39feefd3fbc055c15b054c15f053c167052f7eeefe39f6fefbfeaf6f813f04effee04dc14304cc12ffff3fb4ffcbbe6cfb8127048efeef7d011beef011f045ebfc044fbf6043c12b042fbf0f79bfe4040f7be03feff603ec0f7dff00f3ffe00efdff810703ac147039fbecff9bff0febb7fa036c0df035c0d3ffd3df6eefbfb6dfd80cb031effe030c0cf02fefd8cfda6febfd00b702cedfeefcafdedf780ab029c0af028ffbabeebdfae7b809b025f7ecc7fb5fcdef008f022c093021c09f020f3debfeb9f4ef7807b01defb8efa2bdeafe806f01ac073019ffb0fe9805ffee3bfa9fe805b015c063014c07f013e3def7b3facdfd0047010efdacfebdbc9f7803b00dc03f00cfbb6f7e002bbfe37f89ff0027008c02f007c04b006ebfe005c0bb004f3feeff000f002c0e3001c003))) else (if i < 13 then (if i < 12 then (0xc084cd04966276a301f52b6d738a4ef3c620b1c3) else (0x1101dc080431015acacf300186158cabe8000e60200aae55b2a980308303582a5951c04054f2a18101ca053b29c16000c0537299a3d020052f295a2325c0f60291949ca3e1404b06782f885172898710a1e6cc2858c70a0e51b28194fc9ff6606b01a014584f7279b0003c04eb2e013bc9ce94006e11206104df26d938c9aea005640e003b84cf2659d00ec04c35ca131c97e4d325d80500904b37062e81110528b0012ac94e05425192bc93e4b724d8f0171049336a2d2080848b5181fa30c0487241ae008fe47b5cc123c8ee4732d04c213608806e011ac8cf9409401ca145045f22d918c8af4609a01c1024844f225d680a80860bf2110c87e44721d914c86e1d4219df207089a0b6010ac84e780a8019031c041f20d908c82e8e8a90103c720f809d0102c80e413201a8921007a06900fec7ee8987605f80e903ef1f58fcc7ce3ff1f190bc7be46f1ed925c7ae4fb1e987407114e03e00f2c78e3c315032002404801dd94d076e3bf1d98ebc30000054033913002401d18e9c73e1302f02f830803971c9ab0071e39b1c5cc105808f03620e0c6fe1284421fb2f803771b98dec6dea6c05014f13c03671b18dac6be3871ad8eac6ae8ec6a05e803b034f1a5ac811280881a18d1c67f1e006a14b066e0081998cec65e6a02805d829003271919c804919e49c00c6c62e31f189834061f6801400c1c6084503f20c0c5fe4e02902e401882f71798bec5de30b175c6805ce32b1718d4c5be3cf16d8171d002d30e40b3ce28b8c0d00b2c58eac44500afd7088f815d8b0c56e0c80262e708c02af155806054e2b31518c616003e07240a6c52ebe429805804c028f1458a4c50f0c01419c3154064456809ec4ef3c011009cc4de0e018a09ac4ce27f131a9d0a4825b620095d13825f1298a7c49f360ae05882140247121a102f015e05f408ec46e23f119807045e22b100089d7800d81119b7043e56020628e2808e201a8084c41e6009605a83380207101882c3ff3205342b829401f70f9d08084186436c07ac3ce1ef0f187ec3bee440ed82103ae2170e980400b01cf0e5886c38ee140283f001201bf0dd9980e310e0c0006cc35f6c49504d415c41a70d186ac33e8e09001071c001970c9cf81e01310250062c30e18f0c1866c2ff9206f06202c801770b9dc823813a818805ac2ce16f0b1afc20c0c20c60056c2af560032408080014f0a5854c28e15f0a185ec27f9a053004dcca0ca453e04cc25e9004122d0168812709184ac23fa0051a3821fc0117089b4019c0a20260042c20e10f081846c1fe13b07d90501ee1b7079a791c3882023403ac1ce4085a623f06980df06d838c1aeb68cf455022000cf065c480fe89a8cb2030c17e0c705d834c16f00040802bd6c8f2075002ac14e7444720c014f009f04d828c12e0b3049a240d90250170022c10e3a07302900c9007f03d820c0ef9446506401f4006f0359b80640e18a60018c0be06702d81cc0ae08f029b810088244222012c08eb60060390101003f01d810c06ec60490299134802f015a7c01980230e0009c03e03300d813c02e0ef009870c01e24b0058b5c00e003)) else (if i < 100 then (0x1) else (0xc92a6445320f98fbcc74c6367319f18c54c59e62ab314318974c46a620830eb18698c2ec61553095183f0c1a260a8303e18138c0085fb82fb997c90bdf25ece2f49979c4bc745e0e2ef0976a4baec5d522e9497340b95c5c7d2e2b97044b7845b812da596c60b5ba5a992d29168bcb3fe59db2cd69661cb2ac591f2c7d16300b11c58642c1d15fc0af7e57992bbf95d5cae5656f92b6695988ac78560c2ae815624aa8055102a6e1520ca88253dc29d714da8a5d852c3294e149e8a470520e28f8946e8a31e5154288c143c0a194509f2837941349fe84fd927d593da89e844f12277493ad49cce4e3126da1361c9aaa4d16264f931e0989a4c2a25f912ee8971a4b72259892bdc958c4a9825279285093ca49bc24ab924b491ec48b224461214c904a47ef23da11e108eb44725237811b4c8d30466e2310917b08b6c458a22b4915088a0644d22254111dc889e441921e690e6c86d64344218f90bd0857242852132108b8840841de20d71061082a84122207b1035c816a406d201e900687fe23fc01fcc8fc647dc03ec41f528f9cc7c743df11ed80f6047aae3d1c1e778f30878f63c5b1e118efd0775c3b781da78ec2475c63ab21d3f8e92874403a011cdb8e60472ae39171c770e30c70c838261bf60df0c6f1c37681b930dbd46d8c36911b0d8d7386b4e35751a930d3b469a234911a300d0d4680633d219d60cd10662832d7194d8c994646431dc18d70c61862c2312a187c0c27c60a8300917e90beb05efa2f4617890bb445cc42e1f16f08b6bc5b002d3516720b2c859102c6316160afc0577c2b7f15a98ac6455ce2abb15480a958542429e114da0a50c524e28ef14670a27450d6282c13f409e2c4ea6271b136f09ad04d242664131e0978c4af4254612930935c49402457120f88fb04776239111ba88d34462822cf11470898c443621e410c708550426620ed10598820440a820260fea07eb03e801f1c0f7b87b503d581e830f1f078683bec1dcb0ecb875a03a8c1d050e6b871fc38961c0e0df206efc372c1b4b0d9006bc435721a5f0d1e86888340019bf0cca865b4326e18e50c4b061b0304c18070bec85e142e9417280b7d05a582cbc161c0af3856782aca150d0a628528828e8142509fe04f442740137a09ad04ca0260c12de095b04a5024c61243090d847ec239c11a908af0445c21c210bb083784100202a0fb507c403d8c1e5e0eff076783ac41d0a0e540712837c81b7a0d7e06a18340819b80c950635830f817bc0bb005be82d38161c0ac2054a02908141209b804c9825e4129a0910046d022bc10f40828040281f640f40076c039a81c440dc406950332018dc0bfe05bc02cb815340a3004f502650125c08a6041e01f900f5007480365019d00c5405d802a90128008bc03d6019c00bc0042c01c000ba004980170007a0000))))) else (if i < 1006 then (if i < 1002 then (if i < 1000 then (if i < 102 then (0x3f631ebd8ee0c747638c31bb98d56c6766321318498bb2c5a362a8b14958a04c4b56240b110d87f4c3d161c7b0db5866cc300616530aa98500c2586109b07518332c1596098304158190c089602cb008d7fb8bfa65fa32fc297dbebeae5f442f9697c32bde45ed9af6057ab0bd375e82af3597940bc6f5e27af08177b6bbaf5dc32ece97610bad55d53ae9257412b9aa5cc1ae57d726eb9025c6c2e28d70e6b84a5c12ae0016fb2b7905babadc8d6dccb6945b192d7d96b20b54e5a712d26968b2b42c59ffacf1d672cb3665983acb91653ab2495902ac779636cb18558a92c48561f8b0d3584fac1356022aff157e6abe5d5eb4aeeb57592ba515cbcae2656ec2b6b55af6ad4756932b3955914ac64561d2b02957beabc555cb2adb55676ab09556daaa995508aa5b55142a6e1531ea95854972a2dd5102a849540ea9fad4f7ea78b539fa9bfd4daaa6af5343a98e94c16a5b052b72949d4a06a4bf524a291bd486ca3e651daa8df5468aa30a517228acd4464a20650f1286d942eaa137508aa836d4152a07f5028280493fca9fb04fb827c9d3dce9eae4f3d279393c1c9ddc4edb275593a6a9ce54e5a271d138b49c134de4a6ea536f69b384d8aa6b7d35529a7d4d19a66d932d6993f4c8926391318a98704c21a60352f9897a94bc0a5d892e6096fd4b6725aa52cf296384af9257312b24955f4a95253e929a294a14a3fa50fd282293ec49de24e3126b893394980a4b612552925a4919248212390918048afa44cd220490d94852a416520628ff647dea3e411ebc8f36478a23b291d208e4d4710237f51bb28d9846bba353d19f08cd646532320918648bdc45d622cfd16388af5456522a7514f88a48450c22731134a89714493223a511688883442d220f9102287c543caa1dbd0e5a8701436aa1a790ce886274300217790b76858d42b4214dd0a1484e3425da1239089a842041efa0e7d06de832d4186a0b81053282554111207ed0388818e40aba048901fc80db4055a01e900ae80073fdb9fdecfe787f063f6d9fa60fc7e7e0a3ed41f5f4fa987d193e779f2fcf8e07c4c3e0f1efe4f79a7ba43db81eca8f60e7aeb3d539e9e4f48a7a1c3cf19e6b0f2ec79533c781e2e8f0fe78613c179e008ef6477653ba11db84ed6076843b2b9d878ebe475cb3ac81d574ea5674d43a541d1c0e888740c39e41ce60e6de7334396e9ca90e4f6725439189c820e3cc71c038d11c5d8e25870f938619c278e0c4701137ee9bee4df306f7137a61bcc4ddf46ecb374f1b9c0dc846e1436f11b6ecdb146d5236989b448d9926c9236299b0ccd8086bd835c61ad7cd64c6af635661aa88d5026a3e35041a76cd35c697e349e1a440d1b668a7343e1a174d07267f333ec99eb4cee86752339499c20cd88669e333699844cbd065bb32c21956cca7265153276192f4) else (0x47bfa3d971ea08f30c79123c2d1df08ee1475d23a971d298e76472de39211c608e0ac6fa2378b1b9f8dbfc6d3a36591b058d6ac6a9634df1a488d144677a333719768c98c643e31d118c58c3e4613a305517f98bd145dda2e9917268b7b45b2e2d2b166a8b1a457c62b8f159a8abac549229bf14b18a41c50e2280113dd89d4c4e2e26c7132c897644b12250b12478916c47ce2385118c88a5c444a21db10cf885a441b6206f101687f3c3ee61f0b0f658794c3c361de10eb8874ac39421c1b0dd086d7c36121a730d09866b4327e18f10c5c8612c2fee17970b7a85a6c2c5615d90aa7853ac28ee143b09bb84c8c25ba129d09308471c22fa114b087884294209e0fef07cc83c041c620dc906a7832dc18ce0c1905e882df416520acd05358282413a2095d047482224102207450357818bc0b52055702688110c07f2038b01a380bb4055201fd00ad804440152004affd97fd73fe0dfe7efef77f68bf9f9fca2fe2c7efb3f71dfb3cfd697ea43f3f1f992fca37e3c3f149f862fbec7dd0bede5f68efb127d6c3ea99f4ccfa2b7cf6be709f2e2f9207c793e331f116f8577c1bbe049efbcf7ae7bb83dd1dee2af6ca7b4cbd995ec7af6037ae43d675eaf6f54d7a953d3c1e944f4707a193d025e7b8f3a879a7bcca5e5f8f2c27946bc9cde49cf20878ec3c625e2c2f142788abc361e166f0867821bc035dfa0ef9f77b23bd09de22eea7773e3b91ddc1cede276de3b5b9da7ced0a7671bb2ddd928ec7876263b085d7a2eba975be3ad31d628ead2754b3a9bdd492ea1a74f73a6f9d338e965749dba455d18ee89e742eba0d1d024e7dd73d639e01ce70e709736339a6dcce4e649730eb9725cb50e56a72a439471c9dae4a47238b9129c852e3ec71e1b8e61c6dce334717a38a95c516e25a710a387a9c338e17e70a9b8445c1c0e0af7038b8129c006dfd26fc937cc1bdd4dead6f40b7971bc60ddf96ee8b7671bad2dd3d6e82b7345b94cdc666e1eb703db7d4dba26dbab6d4db662dab56d3eb684db3dad9b86cc9365c1b226d8e76c54361bdb078d8116be235dedaeb0d6f96b60b5a55acbcd62b6b063574dab2ed5656a9eb543da9aed4986a36b50cda802d3c969cf34d89a664d2fc6969b4a95a4e0d241690bb47a5a370d18b68a4b44a5a1fad0cf68273405d9fd2cfb967be33ca99df0cec46743b39599c0ccddf66da336199a7ecd1566583323998d0cc4a6601b2f35975ccb8865b5b2d099612caa665363293193ccc9b664c9325a59276c90c6461321b9908cc8156)) else (if i < 1001 then (0xfb78aa44921cd5fb407418d0abbad9dc41b955724ca51807b2bf5a31c11fd30caf529f8c64e1017da969e8f75382e28b06c387b0e66d654ce3a69867fb1bdec86fa5ec7527917533dcf8615a2f0dd505880f4ebade33146faa81eb0db6d5b1ffd92fcd7ffd88f3c20dd5444f5733542b455b766c0214ebf7c03fa49d1053c420e45ca077bd77657f268ffe677f536d37793dd7f97a31747192a7b30fb1f7735f92b6d77d20dd410eff185eb3fb0e4a0de4529819a6785aab74981a7b918d2d6f19bbe3058d51359eb06bc6ae77d9531cb2662f3353aa638fbf8ec0d2b7c7eff606b28fb1517ee18e5ff117ea6ee61a71b75c60915110abdf77f69c44634ab10c85654e3adea08cd7d65682f1e419dfc656b8a0757746fbca6fc8a9bd541620acf997fdef316072ff88aecd6401e3caaf9019cc7f7a4f605f15f5bbad6140f351473bf4c296c4576fbed0b6f0537fa64ee36063755ca7b8818fd977f3195dc2923e37f220bbf1da2c9bea3c72e08407b75a611fc37ee72ff88bf5af6253864edc614bca868ac4e0868fb9f956cddbee8144c1a76887975a5c3fc82eb2be28dc73865b01f45357f7c32731a7c637197b244c175930c6f03370a2a6cc81f26dec86347fecf9e8c0bd6df646e377f0780257bec79356dcee8ed280e66e59814bf200c5c751dcf5fbdc7e08dddb303e5f5020f9b880590e7eff5475a9d51d0e83a838cc0b81b3a7f7932d4e350fbf86bf42b107ef2a08a5ebe50332b1270b3da38df4ce98faf432bdd9372b83217bf55c736f64be786ef4ebb9e706798ac24bf5c2276d3b673ef75caa00e66a5058ec6d642fc7f90bafe0fca3e5e11ce75feffe819246bff4d26c740576f3fbee5a0432dc53164170b85f67a581ca932a88bc4aac10aecd7401c767bcc3cabf0cf6bf43f5b04fd82fa420afef32205d7fa3e81f034ef425aeab91aa891e332ba216ade1b78812ef7d7448d7cb586cabe6ebd5807d247e5d6f7fcab17af92132dbef278d26074ddb6c4d5c8de3996fe4aebd68518e2b082c685cfb0d5bee0be35f5e69f41c6afef61e976045e8f5721adea96f51ab92696cae409c3a3da887b55cfc10fbb09fe4921b7642fe24344b694aee6e05675b35dcb56d4adbf9799fbfdd658e92673fb1520fc3fb5953d98108fb3ed204cab16cdceee01bd5c05f300dbc6ae89fcefd67d2e89b9629e8114eab920567124e5a64d6aa96ab5c714b6061d5cbf49ab984c34e57392771fbd406f0659c6f6f75e9401ec9bb1c18e249982d726943d2d375bad65ac48728c2957aa5bf9aab96489a2cd26d99cc05b746eaabe77d946aa5be4fd0f9e4ba2eaf30c0fe848064a2599b0d123c6ff733926ea0592249c7f378858fc41103c4b5450817821d135d6ca5d3d3f2462ecddba68144fa539a34f7ef226cee0835b10db953d1d5eda1862d5f54) else (0x4ffd1ffb4473e49e97ebd90ff63049bf1debd373c21db1877361a6061f81df01ec154a9d69b206e4cd22e9caf0dd417f69f1be2c529d5aab58b4d33b7f25760ab922338c14fb4859633d3d2db11335ac9bb7185237461dc1f6e36b956be968f8405fb813aa9cfd3831cd9af9deaef4c03d09f1838bccf01b885abfd99c85a83073fb53e2e9f3591bf1db8004feae3ee8ef8f60b417108ca6af9d20adca5adf2e7f4d62f32b41a78e3c09e9e6a28f9effcef707ae56581d922c78e87d6db8a662dab1acbc682e3c557739b894c1c6a9ad637ee9102f4bcec34dad5721fdb287126d5595d517ab97742aee31a1c14234ce445181b0a8ca0464aa215bc43edbfd562eefee5a52196d0ff4497ea3b9fee59b1782ffb53cbb359a07f0c9ad55133c7ae1f0ba6fcdfdfa7169b6d68165ad787fd43c3fdcce5d9eadde9e10c9e4296ffcaedf7dda56f063b5f6cc4f296cadc4df34d8c27c7043c5de20a49c5b781d9eb2f193b49b214c18fcd028434a300f7d334eac40bf2d007cb5c829afdff124c674b857509eb3bcfd2ed4ba6bd26bfd5fee672feea09a28c9c731f4acc44afabe2e20d147e54e0ee0c5060cae454c2ecebcc5f8266d6282678202a7170100b2fa717c79aaafb7b3bd4fe581ed6577c128a5d3e32f0238ff302c683ff8761cd7d831febd24a9307fe453fcbd3c908c303d3f0715c8d54ef9adea0ef7d6f77f6be2954ecb11bbad79016e32f711901ca9f27d3491f2c1d32cda6f49a0172b5bf8504dfd02e6cac48fc0e3f5073f5dd3249112df4c01bf8556a70dd40e781f628a4a95fecb295f3f706d9e9619c7bea742bd62c61c315f7cf7dca46e395e49a011dbef105273179e6192870c3dc6c3e95c5ea4c7cd6f762c468d636aabebbe015b857b0062125fae10b27f8831271aab737faea2ec1f0d94edff147c3b1600faf780c5eae4fea6f73eb5454c7a87c3632fd9b9e01b1b00dcf18b3bc1077dcb9505e9ed3c3e7bd3bdbcfcf2d4f8c883d3bdff2072fba35fd35d6c134c3077428a7d22bcba5a5071893f23d705ee7994d3b9d7a7820fdbf84f0f12094a4af1b798ab8756372b3ebc8a890e2121f62b4e5ca7f1bd99a972d682b198aa6022624ff8aef68d04373a3ba49fef81071b34e32e0449691e3694e8fd7efb08f49079c34ad3e5731661b812ef80913970d0098305b35d4da45c6b9db73c078c1c64d06316cdf93cfdc3a9102f32baae7ba9745616433fae706d813a173cfad5e62f5c99a42ad23c75f02e479362f217209b3f3d18bca5dd61f6499abf04d78feed5eaa4e2edee7c0d6d375c49adecf7b4e0ebd58069fff7ff37fa132205b907c6fb97278f29c345d41493e1d4d07cbb44cd7b99dd5587271c3011b0dc64cfe2187f2d6f870c5af7440c59a97b131f5b5d326a0717ab63fadb123c7c53397a89d0d8cf6342aec7c4))) else (if i < 1004 then (if i < 1003 then (0xceac4ac08968d7406c5b9dba64ee37017dffc53f03202a90d6e8ef3d9e6d9f77d8dc53464ef9412d3c1e37751736abd47dd55b47f945ab589b98f4c71a7accd2521604d1826d2991fc81f1d187b4b57d3e94fa45dc72a13cb23e3783ae1f1ee83c569cd54fe8f6e324c43a995e240cf72e9f19628802bba8f488de79bbd799102de7f7be19687c449abf93b6ae52ac42801b5e360339ecf00d8955cff106cdfccd1460bd77c1cbfba8b1f92b880e6301f177dfec1044a7c64d362efdd13755f3dcf3a4fea2e46bbed64c1d6f4e628d9d7a59fc2dce1e5a6bec64d6747b7ae49f0747485a7d75c6245b5d83c1ae9ac913519a4eb29c343b71ba61e1f42169c85d4eeb5544cf1eb813cdbea3e7ed303a7085fe313cd98a7a5754fdcfc0c2b91d1fa8adeabf3df77451887f02e902f20def898cb5aa5bf9a15c170f84a298074833ad4eabee86f73bafc95f099b9661e558c2694e8ec4601ff00b27faed55b8f217bf155f9b858c3903b41542de6bca19b9caeba883d1ac95fd1353855378b48890c19a8dfd6b9277060e6eff88aff5d7ab80b9ccc75a933ebf9c8fbc8cbefec34d5702194ab603af52daa9c3eeba79adc7026fe61bfe365625b1d7f1b7cef9a632be38c3b9baa1cfffb037f18526709755cf75915a4e3baa0b0da5aa4af97bfd3d9213cdfa45ffb3552d5474e35c93bae409dc76f146636a690c8f521522522e00a94cc0d433a63ebd0c671075449a355a97dfef86df0a9c45c6fcc82017a4b3d3d327f0bb40f68e3152f357801af02683194fe8931f72814bac51a1432ecf86f0172aae4a1f4fa51807bb6b55e6b8e0cd94cb13b6bc32fd9addc6c373a63152642c07cbff92f286bfa6bcb038c98e9dbd110bf876d2770f6ee7887fb5f46121da7cc5c19f6902b93f45c68d25ca3d630fdc45c9e8003b6e5ae637ec7beac58dd174f5e7d702581d2b63a9fad9d809fc522ca9c6e0ebd8e6063c5ead11be40d86f440c66fbf8e591a1ae17d54392031ed0e779b56ca57d1e1dace71ec124cd6f5c9af004b6bc046d9377b376fba1f13dcba462e38d7f0a7d3809d0a38d7825124b197996cf98d636b2a64060f5e996073f7ad865cc53ab69447d2c1e95fdec447eb5ea4d904f723a73489b32d8fb05fb5ba885e68b925563e8b8caf7cca7482a5114af9724868a09afedac17ee409fcf34c30dc63fff75dc4543abf04cd86b39bde94d57933a4433e3c493f00c0fce240670e00da1578deaa018b8ecbdd186db754fb4550bbbbd0f66ee26f94f383c8b5d16fff2d29021a12476e14f8a67e7cf970f8f0e7a67abafbd28b4ad8e8960fae6de06bebb9ebf7047c958f3633f9ad685b7d47ca7d0a5c4ff6d79b62478f8a66b92773f85bb7b669e2d95fa5d0ebff6c23ec997820c9b7046e201bbf905e23afe587e331ed9c05fa361a7da4cc465193) else (0x848ffff7f27c3f8828c91f71a0eab977f60814bd80d57b29d9724868a0d6fec3b23648af8999a335673ad73f7f14b3fc1b70844bf0f9803a5dea1f54137d76342b95b48ded95a74ccf6efe456f57d677c3acad9155f1c6f217f87d24f83330ee32579ed33d5d4f7dc6d99cc08a0e66dfe702a6dd39451196d4a9c758acd3d72e38959ebaf191e2a74f840fd4d5f7d3811d621d8a981cdfeffc8193acde97a7b4d90a73893880dfcae7b828e6b3d75e3266f3b40f68e317ed916fb21f141015ab28b56b7b2a4dfa755202e9deb5ff1b2b6087edc6578a67b9e9e1a3ac8e5d333d962e37b331f4d6827a3a306fb71b553734cb16e32faef9e09a3163cdc3c17dc46ee8ffff7dbbe1fc47c6157620b1abde2e2b48232dec857ac3cb239020bfae572cd7ce042e4ef4cf7471454faafc6fbbd65fc4046f0eb3e6358dac95a950fbfdb5ede57bee453196e880bd5de49e4b182ca06b65ecb9cab954ab142f4bd0e712f8b85320b735ede7dda15b139268bad889263e4a94f95338fd1e4d18f927bb5be28855d7baa0626b3cd8918b4e91af863794f69fa82d3eb8dfbc5b9ddc6fcc0d47d7301ace7773103aa0ed69a8ab41338f42ff9bfbb50cd3b4e22a74f840efb49d341463b5f6cca6b0dae95b0d5bee0bd3a16f8b321a3fadfca0f10cb6a50e367b53940f124b2b789671e24986327fb6e6d651bd323069bea1511e41bfbd5e5cfd50e65fd1edeabab98ce327716e94f8413c7f6f5c95c52950bdfd125fa9193fef34beb8fe8379e6c23b3eb59ce97de2c8d64ef544d261b9e7259af193fe4e991d12b6521eff4b5b88ab29c243b4f875d12ffabbc958fedc1de29db8c3c630a7547c9968a14c0d1e42f7e132e4eea8aee0a022be5dd9834ed50a74e97d6a3bb709e0f3682ebbe09e3215dd79db71c454ca1ab87f66c01d5d17afbec82ff89ab93be950fdc92ce2d007dcbf063db85d433f2707fee6dfb896cfed6fdf404d5637b294868535ec20b10637bb53af35aa9eef49fe16e20a0c7c19d3cbeb57bb9ec90e213754f1831d9e9e6a7e62dcdb320be306591e3498ef89dc6ac2615cfcad0b6f734c0ffd8b94eadd5acfbc7797ed45571c6de33dc4f92a53e54d41e6b4fcb53e251cf75c6416e92cf7cae6f3a5dcec0eb426ae61aafc1a4790bb20cfdd23f786af9be8f3cff2a7fc28a7d22bcb4af3f096c0ef884b78c3e294aee365edd29f085339c5c4c42a8a32e7fbd58bd7a48fcfef7df22f7b242e2ef2c828c2c44d352df4f2d4dd9473dc219013b949aa76f2b31077196dfce49f1fbe0771a9e365b00bb771b7f94f252bbe19789674fb49b31efa81c5d498e9f6ab60133e9d577f708b5a8fded6c63cdb28701be5f5df3c101d296c6007d7a4bbe141c65280659d5fd1d9e943cbf67bcf6a5abf0d2fc7482ff1bb4a5e6abf0b6bb115f2df722b4914)) else (if i < 1005 then (0x1ab97f63380fd3c1adfb737de51fb3d5d4d6c844820ff88ebee95fa21c9c514aeb7437fcb405b06464da5c7a9e3cb577a523c835b93bcfea72a0543659588776b5e24b0626bfb8812bf8f764c07c8bb7de424cd5699a3783e625bf5c5defa90888f21fc909fc1d6e702e8609d7a83db54fd69818bb0d87ab90f168109ef18277b6549d7517a9fa60e324423b3de61e53da60745c6e15ee03fb50ce324e2e81fea1e0d8a7bf4ef47e8e34f6dcc9f41c6adcf1422768aadb1807ec07d03bb6b93d7a7161c85e7dd30758875d61125a05cdc36b3f5dff892faa0a3de61afd5217259af19296db85662bbbbf4791508a043a9abf156b2a7c7a10a00aedeac03e767d63aeaeabf303f4cc789df7620ff3953964dc9f06f587dc44b22e9d9dd7a292c0e629e91fa62fd4b6fbcba2284a7089da7c01703edff37f0b71e27e0f22ffd1dc0c0891db84df19a8ab259f5a9b3859bf9cd9102f723a02c5f96b905c9d333dd604ee97134944e6774a16495f606f03108c1b2db6e8dbf5370eb6615e35c90f6f1a6a145bf57b879567fe305880ddee479362a42fcb05b810a3ff2a12bc6eea7d253664c76ecd65a78e3a6727721f2e46fb7b9487c5f7f1ddc68447bfcd6f291d248175fe8f207c331d652fb871bacbbbf99a4e2f3de03f9e4fecb905f732cff8767a50f34c9296a4a2dca9f772a03abb7df77f6e63235fb9349d8e17a8e2434f3ffff6b6578ddd59dda9d4ab55fb1d8e1e7c0b9c796948656855a7c2f81199096ccdd7ab7eb63c73044ddc6ec8deba1a74dd573755ace3bae7c36262129e9daad61d6568bc002bffdd7afbadff8f6e3278c94d98b1930e09bc2b4e43ea39bfb771096f18cc5fa47ed0c76ecfd2ede69a3f4873536e841c5d73f472047fbbb6ad63436ab3d3cd6d889b5fe929abfe45fee6097c1792590ed25fb7dd0a10df3e917bc39cdb546bf3af30e24be9f7cd22921e3a03589272d620e5d3b3b1fd8d0a2707edf78ce49c14a83e7c1de297aad08f61fa36f31dba3ddc6e579ef032eb4d4dd765adfbc879dc10dff875745c469ab675fb5baf45a6c87fa46f547777f62b463ed05e23b7f287e284a7091927c27afdd7fde2dcf19bbaf57017c18ffde645fe3b3d287917f416a6eb43e6d6f2a13d3b5f18cbb1398f1778d889209e6fba2de9b49d2f145a7fb5699dcd1f4ff20bc48edc51f173cc947f4257ce42234a55ee525f3cafe8ccc3bd837ced0e34a46ec70ad0f42bb7ad6e228f4a112f54e5a994745d799013669b781d9b15c74ecbebbe78203784c2e8d471b0d33fed4bdab4dc8f26c021718f747ff7a07569685d255f3cb6fbec1e3837b40d172a43f9e8bfae57f57ec8adf438efec22573e8ad4f7a6a90d9ae38d3126359fe08209ec4bfedc95ad25e32a09559a3506bdf398cd427392be5dbc1198c6855dff85c0c3e28c038d) else (0xf5032d771bd26cbfea820fb895a0a6069f862d11641f77af34f532aaae67ba61a71b75a747124cc46b93b0334fb49d1257f87d2a7276625b59f5ee00f72ffd8ac419ffbd2d9eba185b9d9d6cc7f969ff1c25b05df14cfe218172e507fc96bbc9a4d5f6637f71b795fc1f495ccd1f2ce1e699b6dc2798b9d2fbd192d6bfcbbdba3ab87742b666d93c71d309b3f031bfa35e351f6ab4aa171fbb93dfaa1e55ee1b60f6e25734dc8f6680cab8c6d1188428745ca1acd6eb7c2e4fe0f2a772d70278de87ed61e266eae9130299c5de9da28f4b3dda2b0867df139fa760dd3bab031a950fbfdace1b2abf10bdffdb2b510e5707e1e223db9c3dc5deee0a299ee554ff156ad80d9d9c245dddfb1ab1e7bbe32b4a796cb510dff47fdd295310834f82cd1460bfcff0443dba60c1dc644a98c6f0a1ab71e89a744ae5bbfa03795982c6cc33a147f901b01a5810a7cd9af28600b837fcbeb7ef68766776d5aa771039fb8bc97eb58a415b051f586835a3f8b66774fa76b2295e727a5352dfb1263ebd0caf4f2ccb09927277f23a02c0cb5c4775e50a72fedfba741d0b977f8ba2cd753729bc242ff45f8a309c399b961fb295e25117e5fe07ff55c9c0657de1856d52adecab7d271464b3f327cff1bdaf12aace71f33f7d075d585594cb13b59c01b74e8f18adffbd83a4ee75eba821dda0a4f6a126f8188d544b725ae2053abb237c60e325e2e1be3e8a3264a462e54d7f7f6f892dd6b7bfef10af9107f433c217021d135d6c7b84da6568b50fec436d25611fb42db1f93f79ffbad68b2d4fb1079170106f4235ba5697b134de53cc113411379531e6b7a8a377ff39b781b5a3039342649ca300ea501439994b16fede6881be931f35afe7a77ef95fa653952c56abf051e9426fa134c0de320cda7257144432269481f8df55aa1ddff2067e95ca200f666929230275dea1f54167d76fdbeeaa14d5fe30c9e7f6d6bc4aa9f344761dc77f905fe3940f5c99626219a8773fa78c8ea016361acefedf8c07fec6cff74ddae9e76dff13d5dbda602b4e7f8b50908b058db1db78d819ff2e481f3d74c24bf5c2164a7089afe6a5ab196590226f96b47fe8fb8167562317af0639340a10728c03b9d82d013439bb7dd1b889ff8dbaef16a48b1f977ab1fcb904ce42d5f409fe75ddf8f70b0df6fc8f2bbb71253cdfcadfe4146794e22fabe28d537f4d53e0698abb26fbe5a5bd14908a7d39e8c51adb6301ef18277b52d6b53f2ee5783e03dbef1fc4cc45594e113127d3b3c8a251f96b7679b76c6deacf7cc111db892b9c3dba53e10a613d70d0276ef19a55ee60afe74686768e11d5cd3553f7f7ffffa1beec3ec8917a5ec0bcecbb86ed1e02b71aff34c31d08e152365837fccd2c8bde8256fd88d83af08ae8b8715a4d9abf6b75a088b76624a46e7122bdfcab0ad146fdff)))) else (if i < 3000 then (if i < 1008 then (if i < 1007 then (0x95b564eabd77a5920d541edb2a77fdcc8c5bd14e4f579bc8181dc3c9310dd45f0893f27b24adb75af41fbda7e6d51f37652ff408f9ecbf8828de9dbc97f41d3cf71ffbedc93d8b1ab5360d6d66cf8af89ee8bc5a00fc6b9222194aa063afeba08eba8a55c8c479a2f5ecef87cf38d87556abbfa931d3eddf666f3d27567f82cdfc13fe3d05fb38bdd6dd7eec52725121a7c29bd90675fb7dd5e3190341442d0b48397f45d1aed35d59d77b4682133cbdd2735fee60f09fb878b99ce8ede271f0c69fec97b642baaf541123e6e29959be5c9c8cdab3a7d0cf3e17678bd17455e1f71faa4664301bb8d7f956c66e54e5eac0df092fd709193fe96e2993b45d65a9e4f9acf2e41464ee4e8092d0733732eca2f037e70f395d8a370c47230dc88a300fd33526e1aae0ad2696c9fc2dce1f34b293923fa4db362e5687f0c31a40f8f609266a997271bf27b316a1102f06b28b5c9300f95b1de8fd31c66a13d877de9cfdff1b28670075b6c40116949d0c73d30cff6398366ee377cab4389bb89ba29d3a2a1da7d719dec17b6b790870b24c7daaae37ba74c7d7a186eef49c20bd5183e97b6743bb8d99a4a44c2dc38441d53365fd14fbd809d6e30ee0b42bb8c7b0fa24b8bc3a582c4df22eaea1f4853674efe10c514aebc81f64cb4c838b73a6641ac7f513a1b2b10cb526735f08274fdbfeee7ae4d355c3c55986bf4ae99f3f4bebb378c5b3c6c08900dd41ed3f35d6b8fbbe89a95e384060d06a77f4ce980c989cffe0d21a86ae7020ea6af3f555cfef0a7e34514c0cf87f37933dcdd1e7f2b7afa97b545fcedd043eafe333efb5abdfc6f661a7755cdd54d3bcd3e9864ff2a2af73d907c51d55b89aca9d3fb71908673fa618ceb26ea707663fbdd59fb5e5a5ede9384163457bd63ad2570fa539a35610db42b654c78c9cc46394dee8ddd4dd382d77ea2f06664539094c0fe6b3c0e62269ffba1bd90dec58aec2d30453851f4ed980d6cf4b6c4866b5adeae263c734966bc64c257fc6ae5ad8c746d89066eb4694f8b5b7f5be403ccf6620c557f011e6aa7fe1ece9d4d5b91ecd0ae55f97d79f6aabf1f8e9aab556abf70eb43895d160de2191fbc31bcdcb3cd891d62ebee3e16bbee2ac292cea756583a1e70269b1ad539c148d6225d0b833daf11fab3917607eca0791531ce520103e4fdc57210c6672ebd0bf5b287b4cf59a9fd2d3ec80ba316c4e49b7de3c52782fcd45ad0f87f6f79ee147736727edaf824fa11dfdd7cef84484694abd78d47d40d550c6f7476f143e224e7ce0413a14452e15684734fd1727493b5bac3dacdb3158543b6a8cfc60dbf9c95c3709a1424236aa254ca1e97bb4dd6d6d6c76e0b60c8689533da9b86c0c6e559c9abfe61dbcb1339669aac7228e831864e7029032deaf957ab8a2d720a1060e531c561058d0bef0e15b3a7d) else (0xb0af7557f72d3ea7658b917d7fed84ede149f9c620bfc3209537d53dcdd11fdbef58d3eb553c7754031e27f7422fba53cf69f57921fcf71f77371333f91e654fcfe174df9bfef4c9d2cd9d3ba54ba89c0d7e9f7cd3492137b529f27b39730402e72fabde8dd77cdd29f082b296fdadd1d11953b8fd3ee9bd2e1e311775842773700ef85ff7315dd4587369398481181a7d7a7b494ad07e4ea2b4f175fbedee9a1728cd2dfd9679a2e16cefbe4e790bf9ffcb190fe200fc12fa4adc8ada55b555d4fdd23f7dc9a4ee3429bf034fdc3f9460bd1a1577fe171307c5181b166657a3a188cb6fbc9319fc02e7953b96a28c79ecbf8d141f2671897f58d3eb55585281ff120091f359eba18edcf8d7072f9d42742e11efdf1394dad441e1ac9450132d94bee1c6eb27ed02db112ab9d33bb27ab912c0e01bfd3bbe381c7eb6d97ae4e996cb51ac6d649e1b1d3f03b43e13e30d0f271347c81fd2ede087c6036aacdb1b06ce300b166f7f97c0cb55c58226ee26e8de937f750aed15727131fef430dc29f6cf739211b9340e848bbebb6e0b39f40e8ba2cd7cab25d7efc11e297ebafb09d9aa2dad1183ca79ee371838d4f7ca5dd2b5263be23fb3afb8e6ff9b497451ed656bce9bfb650e984feff16e32d5e2217fcd6f3798d3817b829da1881fcdb8d7068396e4fd60dbef250c7a89d0d95bd02bb56f3337e9aadecc6fb712aa6e62005703d7afd0073d9e09aea9fdc5559b6cc6c19bb56de17cc4fc841f3b2fd3e81ddb49c5f282667256cc5eb15a933eb570f1d98b0ea09bdd9896d77d8d803fdefadade57c464c72c9d19d5c88e84512d1ae80cc3a9d889033a4c13af4f2d53bef82feea98e3729e9d3df32b72e8a1b18a4f11c63d6dd5a130f4f84d15237781537432940656ce7eb746dd7fd9a9373c70a67e91fb26193b8cc0ccac2ae47416433b78f6c09d6f8cb0f2c6b1b5cb5ad67dd98ad8a5ed0cba31f30878d5d5a6a2ad5533f055a9f675fd0935b8982115844ae7d6a67cf6d7e6f2511fd377a4acf71f8396e21ef197210c9e95e8401ef0ffcf21050519233e0634a4ce48da962fdcb6263ec6f2ac27ae1a08c9de9ad4b551a7c7aaf96ceb76820cfc16dd9ebbe813a65bad7040eaf740b851e94f9faa654c74edcc6e9fa7038a3c93b9a52a9f1a7f512a3e4cb79094c0d24df609ca6770facb50b6bf995bb9fd17b9e9d6abe9b3af4b7d02665a93e5b7deaec1afc192bcf8b9565fc31377a4fa719a76ee26601e28d8daae7b10cfc6279fbad4ea8e86f6476e9cb14674543b5d6b8cfdce15df771aa3cf7f4592cae2961f341751fd4981ab34f77fa0bdf7b81ff9caafdd11153e4d5fd3c769161d8a731bdb89baad8f53189a72d4fbdd72514ee0a64868b5eb7f62aca659192cea4bffb26273d869ebcfaf625300f1d31f755c798ee37ff98a5e786f3)) else (if i < 2000 then (0x17b18b3a7f7be1968dc65c8547826ef4e692cd0c76e3fabf94d46debab6d3f35ee73192a7c12bec69f5a856502762255718c0f7808efeea047d4fc0c7fef322f1fdb8c9431df9a8b5aaebbfb8dc4efcac8a513d95de60a9de07d7afca07bad673f8d05d63f24f82e4ed20a6064e3ef1ab66e7f49a2f54377437ca72a58beab92d2748851967fbc68bc674c06bc99ffc68d62495b1f7e3b7d88f901f88fbe395624edc3c5115f7fcfc997a32a581e30397feee35fe53de64fa6193aa88ff6ada95635ac5e1bc66d0ce55d9747168ce21e9e2194e1612bfdca5f4f9ad4b5e6a9f0c06fba9c453cedc91d1df1a14b7f2f9b0de31cf24871e1ba20177a4d2d97d026f5378c037b92718b8eeefa445bf6747f1cc82fc44daff67e7a53e42fc4a540c5cae47d1bbd8c43058dcad9c2191355207867b5e2554f8f4b8b3e9f295ea227bfbbc08faafcd1024da818bdd56cecb4efb99369d7790ea4e5175e12766c1f3417b4921bb8540d17ae0eebf6fba0434cf73e12448bca735aae06b3c7482f08652ad08e7f5dc310abba8b9db4fc1f4be62f4f39b35f3bd5652c0f7ab6a075756a77f34c0f7d1d186fdb8d9537151e6a2826efbd5fd970a4c36933ed005c9c6eab8ddae30d818daab38c53fe82b6998ca28a94d05ebaa5e00f6fbee5cba2ca5a6bec64daf5f34be486eef2e0cf42b5f3e9b23474d20b66d312d0a260d3b7034abb2d517ae99dd631494221b48a6ffa2e6eb435adeb05b8a0430f600f1a5bdbdddf14e70ef3e1d8b80fd29abe7482b6b49fdb106fcd35a933eb570296e23cbf3bfc583e34384497d06abfc3f1ead50e5fb9ac779aac09cd309670eda4ea4d9056a1fc70e64961de9aafef88fe9eda35aef77d8d89c40ff977be1fc468537b9f5a8152287e5162d5267aca4fb114afbeeae5d9fab85341725412f3c7c3f662191a5d0fcc07b4d37b4319033b004aa8f9ec1acd730343bdfe6f153e8cdf9c09a6fb9bed4be4c9c1d8d30e7220ef197250d6db180cf9a6078c9b269e38f0f192bbe3d3f1b8a64eddf0dda52c2d572296fdad90211b5eeacfb6c4172969d8aa2f927b32b0a1b3237132ba6be99d2b8f90078e2ceb60b1b17670ff82ddf087bee5caf8892668bc131ed3f9a6fe37362f45e7dfc78c96872a13e325f187fdfa92d6fa92ffed0edcf624841116948f5294c5e9cff7bc58d843399588ded812d5f1193fb6700fd1132dfe594b2d5a109acc4dbea8443ae1873595fa73a5dce833bed5bf5ad8e1dba3ddc6c373df2fda9ab3f21063eecc973fa7a7c957cbfba8ba2e09c337eedf5996659ce1f6fe1c10212fbf3b326d2c0f5e7e6afe9fbd953e42a6c16e3021b557f839767bfbb91f5c7249fcc3c8ee90e8e4267c9497b72a619befe892058ff9761e7b9243da4c0ecd5) else (0x332142032242202134102083331333313123521211100231126032321222125332131502102211023521043542511433030224120211225111052030333021345213232303111222141001201230432333034213041141012134202001534530342142101012100001111210022321213030613244321025111012010301211521121323124111333103210032131312512323111222110540212133111214111034254335141054571112524120034423120302012114711120313356200052312140212342412432213300220301311044123413122420212401122371262122244111108232201300410712304232111100101002111101132621103121242011252341013120431112323123535462213023420103630201030044422204104122112010115321133131415111132424210461431441210211322162354513102324320131230311235121011011134440444102333224220220))) else (if i < 4001 then (if i < 4000 then (0xac34f68b4fa9af2de494788a10ee0b3fc7acf29d5b8f6e6d659bb195eeb2154a8a4d091112a093c06f8d41912e6558949101dc3485708a0bc0fc10000) else (0xe3f8e9d8f4ae05e44e6b22db65e412d492e04aae65c1f474c8eb43e415dbe797647b91c967f95950c6e45af60d951345852b8a7ad95ae9755a97be54ae7f2233b614d2fea5f1bd2160a4a40c0cf249e2d8d755470e7ea4af7f404e828cf207980790ffc0e0484990667d12b7e598c4634c6a0a33a064a700c65695d5db0e9d75f387d95241885716f25230fa8de898ccd21651f6a998c10c061483d2c82c4771f73be4264f3171f3a99c667ed92bb10923ae320cd0e2cbef019aef4991db65034aa382ded65d98b495c9eb30cd7de3c20b82024989bbc9cb72eb7c680959a646c79243804c4189925bdb9fae89966abe216f8bc22e7bb04d233c51dca6f5154fe9654bf5188f55f6683658002fad7a9c4e199d25641d46fce22b247e4d5f07c875d7718fa1dae10c73b8234a28e4d2800849e113d97a0bc25ce7595660800d6be3fc2e29825f271e8450ab381dee641fc06f1f9a63905b4c24ad50857fd1e9d046a362bdbd722c4a3867714fc90a9fc861c331ba314a8653ff8e38e0d87406a44c6fc07f34081f2a6056e3ac29d051b53a74c088feeb6bfe4b55c26e7346611f219c54d6b88dc9d82c3d9be37c83a33c809b43edf1333e7370d4de44800441059c1de9e601a323482ce517ddc3f1dda5fb6d0cbfa74a5332c93b2cabcfce157b87db4e73f5e74e90fbc426218ba21c0336e91938a8842fdf7373970b8806878f85102311f40413ce5b1a9b720597524349b094732b59c831b911840c7ceefb70eb49005932c2663431fec3672484641700eff4c90cc591ace177cc4e1c625118212dbc1d33099a0bb217b476b7f88ec1bf0c68b033ca653c2f743f10b24ecc598300555fb4e343e394f5f1ea7b02d947213f197741176e11236b28892ec91c8bb6a4513263af3f7d3a8f9cc2c407fa3e6896680b1b686b9a34f30288bb6d87ce299273801e861750ed8191c131ae9c407f6034837205165dcc654984594a8680d7b1ba5af9960c9a194c411fe867c119bad5e3cf39202842470d362993bb0102ce5c201bbe0b4cfd62c42509656e947bbc66df486ba70095b0224e857a6c2f66104da5c2ce256143597ad9a6df56ef36d33e75e06b397453b6e606c8493305302948a126d4386394bbf2a42090004b884bfb8b98f490969792800c04a54e83b2194cdd466c42e1d2c45877729ca0f52b323b05908623c86070fd1ffc94b6fc92b81672487c429ce5152302f4cffdf70e5e73c3b8297cf712dfc6ae1f731781db17c310f236d23eada5a94f5a44af6158eae0b8b7f09ed1021512394870f524a138ca5f697e29c8556190475403928c780ea17763bc9d7ce3f70039a4366ec813e57645ecacd77f546127b22013fd2eeb4c0d19612c0c192872189127a208f4493eca69d96e237c4897503c1e09cc415d4305942b90ce560cac17bb2149d4e918)) else (if i < 4002 then (0x7291af71c693ec9a03e1535e101975c68db3a4a5a043aa1ff839c8dc3870752f0e7eb9a055207e296097f920858a1be20647273311e7cc8463c9595abaeb5ed49be9c134a2354b6f2abbcf87da4298653b9081480514a51ed4527ef4723c2deeaf7812e830a27ad2e7d1907d1965da19113d5c1854f773396dd8638678033d5c4ae792f6abe96c2e71284956894cbf877089d09a7318397bda03f2e66829ce21e161b04e9027102a95d6b64874dcc6352ce850821cf652f60f762f8c077998fa1138e197663bd8344e607e09d065852fd00226364f2e4719fbba5c58e5685f01adca71ab3efc5b2492fa03bd47ee14a59474acbe59aafaeb0cadd896817593a90c8b6f3541a241c5b68e4b1c4b309ea652d2fbce59db459871c27b18f82353411950e706d3536bdb5eef52b0d707f87544ea8511611cd506473a017ec2b23b1cd9ee4a8c3df6dc81f432b26c20d3b45d60f421d8000c3e69197c117f279ccb428bd748d9aca836925c5f1ad5005785de1b82576081acd54a4a101d97dae4a5c672c3ec1cce4807cd49b9786f239adb5ae08d32f9422ab1cc824e1b323e1c78d2074c898a13a8ae28d4218c4d3cb9602b513fe11e17502d87755f51a4b985e0534fb6abcd4514e227a9cd75c16b0c680baf90921a1785a2090828ab43f4d6aaac3290538f4256f1b73ed16191cafe75d6175c8be5e30918f6df212956b02f454d437816938ed4ce36d0793e1861c3c51a8bfe8684e8d008be1afc2fbe127b91e528eda8914795dce7474e488252e12570be0195d6600a789c23453491296199f9ec4d178bdcb42628fe974c23adeb6f44614a0688109d763d1034540cdf9a503e5c6a5cd9488fd971a28a17b3ffde1ad8e01e8d9954eee951a1585fb26a527e5cacbc28dd863aea835b3e30a3bba5ffe82d22c39e9f2d3b09a78e567ae1ff6b1be2eeeaf47103bdb5f9f34e7d03715e1c0c63a7474dd15212783449a6eeaa7306a1a9fb62c761029e084775296ba6de1a41da78122e1fd0f10759b5e1ef33a972d3d7494653057908a6686e177ccb88a3fb36d3f7a3dd2a6e3474635b62cc522b23c8248f247472c2471816fd9a72b9356408b609a13ea1b080f2a9a752b62c73647bed25a03cb7b6901dde6f562a1cc817d863a3c7a6dd070dd82bb1588062888678a2824ec104706966823859d19a4611c824580ba4b4da58495ab93f09d616ed2f0bbfd2020079c1142c8d73d44b73e1875cecd747b251a36f3797d00245193a2501c57a4857c16113338fe20be704b7e9fb6fdf7218039fee54a5e0330015601671e2219b5b2536a3b8ec2800f3686279665ae451249581ebeba2800c324a9649703d3f60b8c6f194ac8a53708ca341bc702b379c2e0b79589074e21c3da57b0b4a742b5d10070456e34f05f640d244c03c9a4200677e3fe545d38a1890de) else (0x4a64a4ed294430b6d8c615a073c622e88fb43514398e8c4231f83e613dce8169f12fddbea6d207165415e9857ab3ad18e35dc287cace608cb829e8965cd2a815a43869136ff38dc8cb9a530490318f22380e4521b41e84c2e28734a842670e99726812112c260159c365ef22a473291c0ab433225ebefd234e3178acf0dc78fe854c38e5f0cd799b6c959ed4e0f7b03b104e90a37f8936e3d4f8690edac015ef772f691349ac9de2651cb5992afd741b455b2a0028b6cc8cae855b7e23f69c84cf52ba30cd1c8fe19494e793e2edb70ea5187e22c69689f7de3cc0)))))
def chart511Data12 (i : Nat) : Nat := if i < 10 then (if i < 5 then (if i < 2 then (if i < 1 then (0x80) else (0x88)) else (if i < 3 then (0x9) else (if i < 4 then (0x6) else (0xc)))) else (if i < 7 then (if i < 6 then (0xb) else (0xd)) else (if i < 8 then (0x6) else (if i < 9 then (0xc) else (0x2a295421da53041074c98007f0f7089a11520e6d183786baa8a92220670c61dc2faa04c815e0005348016c27a424c544153047086d00a1344076ca81b83f066cc23302b64c0bc13b0a60407d83260036d49a832402605c0782301612c03803))))) else (if i < 1000 then (if i < 12 then (if i < 11 then (0x1ffaff37fe00cffbeffa018c0be05bffb6fb37e99feefb014c09fbf6025ffb808e057021dffa7fc03f01dfff806f7fcef77edb7f002f015ffb37dc027011f7f3f7801beff007c02e013dfe7ff001e00bdff00cc00e003) else (0x144a019acd8bd6af79d031e89c6c85df4ce28f2e31c3)) else (if i < 13 then (0x3038827770827306c26f5ccbe040426706826347425f36c26b25b53418c253478c009e06b07c024b2474702433a449015070023b2374406404303b022f22b23322723f2231804b056432821b2176741a421320f090720ca09d020720320b1ff21f1fb1f70ec24f1f32571ef2006a01e71c00047e01e31dfcf00101d70401db1d36e04443641cb0001c75901c30081bf1bb00c1cf1b79800e85600241af1ab2080e41a71a31b319f5c05f00605b01971930d01604a018418b18738418318f17f3f4bd04080a017717316f62029070c16722016b16317b15f29402c15b15719b1531eb14f5d0a809845e01471435504c0c2098813b13713f133bf08c0a7068012b1274505b49a08f011f11b12311712f11306410f29810b1077046309c06001100ff0fb8505f8be4bc00f30ef0f70eb0445147401280e30df0e70db1b05207701f00d30cf72447c0485800c70c30cb0bf0d70bb1c86501a03d00b30af3c04486901e00a70a30ab09f6702405684d009709309b08f0b708b44c0871030833f020c2e032007b077b302b01245f406f06b0730670e0b0005f86006305b4f03a00535c805704f7b05382d00475c404304b03f07f03b22828003354012002002f02b0280270c00238d020401f01b4001a801329c01700f03700b14b007003) else (if i < 100 then (0x1) else (0x9b8735ca69b4cf0994131366084bb096fd2d4e57ccaa994eb28f650549ae92db23ba453c84190131e7a3a7c7118dc71ae6337c64d8c1716fe2b8451089b3121220ec3d0871d0cfa17942b184df08a20e14173827103e6051c05a800cff31fc53f587de0fa6df2bbe017b50f531e77bcb878bcf0a5de7bb857652ead9d393a22737ae5adc8438b1710ae119bfc37926eccdcbdb6ab68b6c7cd7ddad0b55069f4d289a3bb40c6790cdc1983b2c6650ac94590eb1ec6362c55987c3090609cc0257da2f755e54bb9d7552e7b5ca8b8196daad855a66b30563d2c50582eaf595c92b4755e0aa5951e29e15344a509479a8b15098a06d3eba7a44e9e9c8136ca6714c6e97bd2d3a5734a4c93c9264a49e489090311e5a37b466e8b89141a23b43ac86ad0aaa12d419081dd0121fdf3f327d84f8a1eaf3d067884efe1dc13aca745ce631c4c37fa6ebcdc51b3d35f06a38d2619f7334e6558c8418b830da60a0beb97922e5a5c1cb67968f2ca85894aea959b2a4453cca5c146a286a50289f0139e26c44bfc95f928d247247dc8d9915f2220430484010421fe43ec47bd0f261dba39cc7188dd91b4c35e86968d0819ae32a46148be317102cdc5750ab114a827c44d7893d1220239044788400ff61ee03b8872f0d98197030285b20aee14a826f048d08be10541e0034805cc0a5c1298222039c06800aa01120196021c0190000)))) else (if i < 2000 then (if i < 1001 then (0x8ba39ecca256f57b3577eadd4b952926251becf28bd707f6d9b13149e5795063ae5d7c863d53445c729ea54df941e8bca94e9fc331cd73c44053b7adf9152bb17ca21a876e61972f972f43eb136decf66a76f3b65af0c019dbe2ffd2ce4840c6fe806dadff187c1fb989bfc26debf7449ed2d21432b2a98c57ef58fbda1df68af95a6316c3c7085ee9a9fac207835f56e4674e7a8ee9db33209af347b33f599ed7cbe8bf04cb668acecac86a43c43fddd9d248ba33b80fac3aa4e6f425774b7fe7d1d441f0b343f5e9483e4863fcc3dc7c3a17456431fe986e8769d64e3d91d045f5ec16cfae45c4578c26bba9db6fdf6d87109bd41fb4ae66b4a521f6d04df188fd7eaaf87c309beedb96caba1e549a8a33d7c72bd941ec4fbba9bf29580ca22a4d7b626d2ca22dec656ef1b71ca27997b0b899e5780edcc337e310ea931956f8b71ab94320cbe5ef7336791526a2bec94c268feab83b6b3d08bce51157b61b1284d07ece963d5caf9ccc26bf113cabf27b5e037ed86fb36a7614bca0e302c72291f7f0c9030f0872e8e405afc9a76b15ade88ab28d16a56f573d79c3bcf723c026baa9d646d219d132a18d0d64f28d31c63fde3a01768fa135e389db5f5d2f1847ffab6fa72e8c043e0c135e5bda4e405eaa99528bc15b9a9aa66297c7e48dc6395a0f5bcf2b21f0de5fdc85f1571b1c1e3fb3916f1c527115707d1bf643a9695ff2155fb0b8e1eef60406db97355c72726ff30f719dbe2e8ae2517aea81f258e8a44a54be8ff84d55e6ffe9c8ba44143c06fd945b1c7536ae7f7ebf81db1099c8b90e325fe7d8a8d974a9fac2ae33622a4c7e7cb19cba7c73f45ca571d2b6c2d55e863de9f542ac6dbf44adeae65ae1341f3bef67f2bb845c81f3f66ab0a87eeaa3be4fde5df49cc697b74d0f21316d1d3be928ee9ea764822255799d2564a5d85e03e36bb33e86254a2f04ab6f0ffd5e5a448c0c9ff09a06fd36fa7eba4cc3ede5a56f5dc46a7bcc8cfde3b63f533eb1467d91fc738edfb3dadacf83a56ae507070c60e26b4fe2c87f4b2b3fc2d91ad1ef0661364dd7d837ce8eed3ca97a845f09bd6d2b9d74a7bc8f467c2709f0afb67610e3893996f109526a2bd50f873d2012f4911d2a5f46f5f642682aeb29d70a12ed0ff09be9ee9d2655d2cc1af3f76fe01e294388b9085f72024275938b08e83efff74ce3964f922229a5f47e6db974fb465554614ade9d773d7de76aa76cf470985c6f578fb3b6bf2d877b6ee931d3b09935c7d4c91ad31b514ed8babd547323b7f2e676f7b6b9fbaf9ffb1772d225b241134aa3f9a49174b88be5115701bf6c72ba83f63bee06d91e51a6fc63f8a7402f55756a84606f4317c8233ab053e1745cd57d75fab95b7bce311e1812d1f2c8b2e5f88e8026f7c591cda41bca0fb9966d393af2d68f056f16f2b4608) else (if i < 1002 then (0xe6d5c23a6a6f1787c137dce45baaa0a3ab962a376c946f5e136c8757cf695de46aeaa98cd19dee639b972bf46c43d5b2acc72e8f00c9e184d52ee996dff7f3fe117ef7facd695cb9ba6802fa21d46beccc0fc8b74c85ff9fa3fe46fdfcdf4e5d24d43c0613ae888a355ac30df3a59ee91dd395a1ec0bc0e45cb4a217ee35f17559e5ec4f4966bce66f1e22742e9e4f32fa399797aaf33a08ba442254b25a8af5d1dcaf076e2ecd425a1e135dc3b7276da70c62bff4ca57890e05fff426e66bbeef6db9df408d4cc260fe19f08e4f68cc4f95e3ca19977d2a7b318f12e59ecd7c823ffe93cabae6e9a4c509f5bf28323605e389db5f2a5e64123ec9db6676ba5c797952b4cebfa1af553d3b963cf00652f006dfe3cd4b92a35350c5bd8beddd7ffb674b49358f8e4dc041f0eba294284d7978f07a76eaf95cdf603e7db625a5da5285cf26bf106abf1c8b90a7e984de3cf05ca7ebc60d2a2d6f632c794addf9fbffe8e65e48fe3f343974934433b8b15b7abca73f9a73a8a30285ce40521bd780c338df9d9e3bf17b8835db93b7137ecd4eb179526a28d771727890becd4458bffebafd5edef3811f600ce85ed3c746b932bb707a3fbaf19db8adbeef3932abe210fecf86f84eb413803a26e43fd3775e0fd8f2c8acaa6fb73b62eb74737772df4ca98da8b99b3a6dcfbe39688fa10abb5fc59d2d1c831f28cb7500edcc7d72f94458c862cd9da6e48b82be4ed1e4ce8dacf209ac47bb3392af7dce2137a80db5b9cba1c9794ad4c26933f252b084d073664edcc5685a98c26938db7777dba0df216f4437eca3bc52dea74add4541d8e1cc7dbd9b776ce9795767d16a1354814ce46fadbf5bbc45fff04df701b6b7385ba326bf315be588a935ed2c4ca284462d8fae42ef7d7e426d51b6e05cdfcc2299095ea343974a00be15d36afe82cfe5356604fa362fb7abe59d88fe9211e2d1aef606952eedadfde1f1b55df4a9594cdc4ffbbdbff3879af36b149eb1e54be8809da732d95e144fb39b65afb9019db5e295ce48183030a1cb6203f316e1357ddb7f531d29a89a22a3ba5aa0cf3bc3e797f38a85baa8866534bab460203abadd5286299fac9f2f8add572b47a8945f6653c66b8964d8f9045f5d57f89b1e55cdd3216413406db97016e1d840d4f83edb72fed0be4fdeb053e3b47c728a32a52f46e63be5101235eca10f72f97e3d83d1507375bc5cadaed0f055d686db72616f00c26f95b21d49457ca21a876e6197888a0fa30b90bb2fa87f46d507dfcb6f7e302015bd6cf67753c5bfb516f021db913293314b9c22991eaf484d6dfac0f490f9d0bee6a8cedf6ceccce7f9a2d52fdf1b9dbf592e77db92156d7dc64ed7984dc0296dfaecaff652ee0f6ff1065a854be9a38bf6d7bb12dff9f3da77f093dcb4f27e0ea0d137deef99c45bc93089ed3a4e) else (0xb388dc2d3b32af109bf246e31cadb3d6f3cae1fb41131af88335df8607ce43638962bc0fb32fea5309c72d17217cbb04cd67cb2b21ab9e254155394cf5b8d3faf6d4cdd34cb56650b8bbc705a7adf9419e64df1cad19407d3a3b62ef5dcd723fbb4ff202768ed92674b4f8f819bd2c2ad1cc4135e075921ea861b9781c8b8445f2cc866fefd393be2d139c42e36abc0eb2394879379e8b75c227cc12f95db8b3a58453003313b37c9994f6bffd16a2836632a93c216e352142bca56a61346c18e7807ffdecca67329b6bb338dfdf2882a090eba2cf526abc1f08b63a3b154b2599bf283ecbc7571436e6f1b5c33f9e285bbabcdb1103aca11184deadadcdba1bc325a37e23f687f77aad0dabf655ed0fddd5e779e8570ee623f2c6ed748ee9297f9d4fb46c8eb5b43d19f0a013827c41d9445784d0299c8cedadde52dc6f94550faadb3d6f2e59907b3a4d922e8f764a945ebb45a9aba78a5ca4110ed393a49174a765f214755fb45865fa160dfb21d69ed572bef38837e23f68e56533d11ecdaaf539d9594dfde37e518cbd8c9db76709f76cbfd71414589bdddafb69e53d86abd8fe63edecdbba7ee5f757e07c36b6465743f6d19dee3d046366231da6e71645))) else (if i < 3000 then (0x4154613220204201103111203041024330421052204232532011217342210020828031421211312222801120212423212120723021212310231050103201312051320230) else (if i < 4000 then (0xf67130134732b0d03800) else (0x98c06600af675ec0100f074ba9566525c9f7b834115086d8226dd8972c8a70e61af9f11e9e0345cc00048815ec7fc8c7cd37669e16c4a7250a43105d0b807298b04644979da52109f0ee05029c9a35061e023190800bcad259760e0f8770872f82076e6f0b888249736842b77094895e004d139140753db2118825b40661df608c1f28075485db9bc6972c196518c0a1e3739e881c1340c7066183260dd7989b08c594d0822743a72cb500ded7b81a74d04084a27f9947612d82c2c60e75451a16918173137075f12dc0e978900a8920458472ddb2d48094e7e3306c2007e62d8706c4e785f31b890228261f01278479978527f43602dd04dcb05c98f78c9a0891f130b414851240bd49022059dd744ac6f409700bc584372d5f07609db39d74289d1b93c7ddf89e8b447c3d02819034609848e2e9e2898aa61dd6799af740090806947c302cdff97c4b28961772601347487c8e)))))
def chart511Data13 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x51) else (0xb)) else (if i < 3 then (0x5) else (0x3))) else (if i < 6 then (if i < 5 then (0x8) else (0xb)) else (if i < 7 then (0xc) else (if i < 8 then (0x6) else (0xb))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0x100193324a640cc17a6060809d2002b046a918030688806c0ba648cc03d5001301607c03803) else (0xffcbfcff6fee01300fbfe00b007ffe003)) else (if i < 12 then (0x1481749368f61640b1c3) else (if i < 13 then (0x13a0701905601ec3bb800e61c03786b5c8530da0670c77c26005b060a60300570a60808804b38013c23a380863408003b0280fc1b85f0661d0a40101887400020004609c0f82b0360d17000444804c078170160bc03803) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0x268c8c8c30b9fabb36f2cd1782b24ee8e5071d132a5a8980f91821c022800) else (0x46fb8b7c279db2e9f6a2f609e6ae7b8d0bdf1ab4d2fabec30cc9f7d18635ef0c1324e8df2a30f7c6ad935b7c53e2f957efca8da7db4b81184496d4fb5d3c7f61e655504f8c3c83f98d5ab9bfadbecca19be3237cae9ef8e2cea2f7d8207917db472c5e05e9f594e8dfd05b7d8124630f7c6ad249186227b3d4bacc61bf61ef00d36ec37a61ef8d5b768df7d1462f3d86a093f3187bc034828e8da2de084940d2fd)) else (if i < 3000 then (0x2431301161) else (if i < 4000 then (0x0) else (0x38a74f8a816c44a04000de230424a920c9c816)))))
def chart511Data14 (i : Nat) : Nat := if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then (0x1e) else (0x1)) else (if i < 3 then (0x2) else (0x1))) else (if i < 6 then (if i < 5 then (0x1) else (0x0)) else (if i < 7 then (0xb) else (if i < 8 then (0x5) else (0x9))))) else (if i < 100 then (if i < 11 then (if i < 10 then (0x0) else (0x1ff9ff003)) else (if i < 12 then (0x12) else (if i < 13 then (0xd83007ee0a41c06c2e1804002200f0584c0e03) else (0x1)))) else (if i < 2000 then (if i < 1000 then (0x3c0) else (0x51d387bdd3941ee)) else (if i < 3000 then (0x2) else (if i < 4000 then (0x0) else (0x1)))))
def chart511Levels : Nat → Packing
  | 8 => (3,7,0,0,0,6,0,chart511Data8)
  | 9 => (104,6,0,0,0,12,0,chart511Data9)
  | 10 => (913,5,0,0,0,16,0,chart511Data10)
  | 11 => (1395,4,0,0,0,17,0,chart511Data11)
  | 12 => (272,3,0,0,0,15,0,chart511Data12)
  | 13 => (22,2,0,0,0,11,0,chart511Data13)
  | 14 => (2,1,0,0,0,5,0,chart511Data14)
  | _ => emptyPacking
def angles8 : Nat := 0xfff2808200a0102300802820014294030020104100102120168280020020100100120020014294020020100100100120408208c0028050a200800a0000c008c3c28000430c1023000080080280281080081000200080080280281001081001004920808200800020820020820100900100800120100020020f00800200a010208002002001009003002001001003002040048040008040240000208041008041008000249200208240808002008050a0800200a0010080030080010090030020a05200800a0010220080080000420480420000400480480030c20082020010030010030000420400420010410010010040820080020050a200800a0000420080420000420480420000820800820010820010020000c00800c20000430c100300c03280800800002002802800014294800800002002002802fff2808200a0102300802820014294030020104100102120400400c00c00402400800800400400c00c00002402002800408208c0028050a200800a0000c008c3c28000430c1023000410c08610800033c30028200500400100f0014014012030040040060020140140020020040040040060140140100020401408400480001408c03c000410480410c000500c003fff0480080400080080081680280400480400400400081401680410808610800020820020820100100100900100100120100400c00600800400c00200200500400100f00100100100304004004004804004004024004104004100800104100024920400c00400800400c00600800400400400c00500400100f0001201801800001201800800005004001a05004004004804041200861200100300100300004004004204004004104100001201001200001201801800001001001201005004001a0500800800820800800810820000c00800c00800400c00430c0010018018000030030028000010010018010030030020020410c08610800033c30028200500400100f0014014012030401400400400001400c03c00001401001400001001003c03401408400480001408c03c000410480410c000500c003fff
def composites8 : Nat := 0x123456789ab1032547698ba2406183a5b79426081a3b5973517092b4a68537190b2a486684a2b09173586a4b2907153795b3a18062497b5a3816042ab8967452301ba9876543210
def chart511 : Forest := seedForest 511 14 #[(0x409a48e9685802218b2746350bf6179534886263c79100a12841e80a4430f80f01b1034990b29d3d5189c08b0478e2766d0ecc3258729c8e1b3a05402a884346e8684844229b264d225e74152b0801c9eb0153025c0441e00556b56048383e89,0x401008c5614812210822003109c209050480424205010020a841c00a0800f80900b1021180b281291009028424486246440288210c528882102801202a8842066808480402910241225a3015210801c0aa015102480400e00512a520168a0110),(0x7dcaff138520749c00350f2716f50e2a71780a18103c153c447400738424808a6f785c2e34ce40a78af2b1335253edd34414914850698716e7287990bd0318009610a3c3970037d20780c80a881335197843f80481ba0b1ec0c54180c386010f,0x398224100424609800048a08063106227178081000ac181000300261842000a2c7084828344800048242300340169c9100941080100804140700708215021800961002438500259205804802081334095040a80081a8091ec0454080407512e7),(0xc215111e2a15e5a88d07481b9090b8c4cd6aecd650eaed02f8a32381713045448c4de54014a80aa6e834c70259163195b30ce188fa488c1a0f62588653545170aa9888a50e20936381891b4334492141cce4630e406262229098e02a44031f6,0x4215021c2401e4280902401180a08800886a645240206800a0a240033104040084611040202828a28800830080061081b004a188424880280f6040c2035451700a8808850e20024201081b4134402100c8a4630640222002908840099886d10),(0x45c0008a320f00a46dca785ecd90e6128e4aa0562261e24db413906e0ae38a201f30c0a157ab4c417661a22171d230ac1c92ba0421946389644933509e2862d2a8076e214930e8d0d6820511a4d24443063c30930aa014af6220609a0267c1f8,0x414000081007002439424144c0d1261204404012000060452401c10a48e3000206314200412164015071a201709010240490800000906189600911409c0822c0a8036821081068d052820401a4124041021410010aa014af0020600a026200e1),(0x1e07936054734f3e4e92828054269081e306f129e0fa92bb1b1eeef40bbe16f84c2c5d42f361ca818b40610a8d209810080f56e66b22265c8751ee0841ad3e20007413b9bd0b840fac53828242e57a12416823bde888c100b8ac52f14807fe00,0x42697208430691a429088801424c080b1063129e0de921a03942e74031806f008083d4632400a800b04490a09008c10880956d66324066487146e0041251c2000741398b50a840e8c01828242e53a12416822bca008c100b88c12d16805fe04),(0xafb3bd191e15c153e1dcf1a124982291899735b34041b1124a10a525620c2d03a0ca29040a10711a98ed9924ca231ca431c521d9d42c232c3ac294cb805339f893e7021c8090100001a5c7e216f91ac00202884516a9fd4b3d0aa00480780000,0xfa195001c054102831cf140a0300212085124a16042a10000102024630c0402000a09040200700008c080301a23102010440118c02c032ca0c1d40a8001315893e70218800010000084c56016f11a000002800514817d0b3808000081758646),(0x115d1aa4ed8261c453226543ba42ad6026225e079c5ac345076780dbfa9e5fc83225920322d596027155d6a07aaf2b40e601c06f892dfa35d006582cc8cd905b6cbc3130143c5a6580943a2cc46622e4a0a2c01d2f5156b48cb0844b13800000,0xd18a0e900004753026543e84229000682540114528005060788986acf4c18303592028ab104027915c6203aa120607640c86f0934e2a18082040cc8cd005a68ac2130103c5a658014322c846002e420a2401d2e1156a00ca0804b13800000),(0x73092ed069960911647408040488b43d5e2d4dd89528484a428c3357138ab475b6afea780cbc0894032440c6cc8cc69ea6b383293a5890c052900273434a8c842d980537a1494cf1082b3203fd10eb6731743d2023358845445c2b1524000000,0x900c2a90219a0019646208040480944d57284908802848484085135b808290b5b4a1e2da0cad0810032e604cc48c8692a4939023381250c153000070434a88802c10052721094cd1082b3203e800e167317439000334804444542b1524000000),(0xa036f08714c898f2b5a8aad82814c162653d96290ecf7624e11d168124c8e1c1944930e174062678b3020f8f078cc9c1875872a486925972160c98bd1214c82d701254ca6347c082610928e5482d8522c8d8086a014a30c8db1516ad38000000,0xa012400700e8129004a00a880004c064610c8308028d0220c12816010400a1c0804020e910060330820209ce050449828100328026021412122408b10210c825001014c26343800221090880480c8502c8480862014a0040c31516a42c002900)]
  (columnTable 209 0x8000dc01e438003f007808001c801c620003c10704a010f041c040007f007010002fc01a02000c604650800270419128049c106408001c8818628087220610a002f041814800ff006008000d90164200036005908004e0016340013f00580e0053c01582001460455080056001532811460454100057c015020016200538a0059c014c20014c085250005bc014838017c0050480063021292001382048ca024e0812128218c08484e006f001212801c700470800528811a2001582044ca00568811220016220438a005a8810a2801cc08424a005c881062801782040c8000ba00e8200262023288009c004c528067001310a049c004c1302a6202300c059c004c0200298002cc800a6002b238029c002c4800ac000a72802b400295000af000a12002c400274e00b1c009c2002c202268a08b0808924002dc00244800b10208d2002c400234a00bc000873002f80020d200bf0008120010e801e0800c600073200318009c8a02c60027028012e801a08008c9006638033a00188a2043a00582003500015c800d40045528075001150a20c600252308b1800940a00d88004e2803700011c800a51003528038c080a4800ac100272802b440094800f00001f2003c00803ca20ac1000728202e80380a400ba00a82840c604610a800f0414128414604510e005dc014440017a204090005e8014248097a204016005fc014029010e800e0a80270411130258c08480c0067c013031012e800a0e006bc01283200bc10404e812f041004801bf00480a0071811144001cf00460e0077001113041c604410e0079c010c39812e80020e1471811004801ef004210007dc010440017a004098007fc0100380272003196009fc00c0280a9800ac0a00a9c00ac4002b640091000adc00a428429800a88c12a6002a05802bf00280a02b0808985802df00240a00b88088a4002e700230f1431810804802ef00220a409c0048531067001211000bc800863802f400215220ad900045802f700210c24ac1000338ca9800a01a00bfc008028431800988c12c60026048033f00180e00d60005358035f00140a80988084a28037001115000dc8004630c31800909000de000434c017a20009600de8004254097a20001a00dfc004038038f000e0a00e600232300b98008c1000e7000314003af000a0800ac000274002b600090c10e6002223803b80008cf802f04001384b98008811812f040006003bf00080a80b08081a2803c400074c82b0808182803c80802ca00f20001b4003cc08025000f3000194807cc08021600f3c001829035001054e00f5000153a2ac202041000f600013388b9800841600f7000115027cc08001a00f7c00102003c00003cc80b88080a3803e200038f1071810043a0ae202021200f9c000c4003ea00029000f3000094451c604001800fbc000831037001014e00fc000073a22e202008e41dc004044803f200019000fd00005422ae202001800fdc000438c39800809200fe0000341177001001800fe8000240cb9800801800ff00001) #[[],[81,130,118],[16,82,131,100],[80,16,33,50,116,131,100],[16,32,48,128,100,80,116],[80,129,50,116],[32,83,116],[128,81,32,49,100,116],[32,49,128,81,116,100],[128,49,100],[48,33,133,118],[48,129,82]] chart511Levels angles8 composites8

theorem blocksByChunks (g : Forest) (k start piece chunks : Nat)
    (checks : ∀ i : Fin chunks, chunkPass g k (start+piece*i.val) piece = true) :
    block g k start (piece*chunks) = true := by
  induction chunks generalizing start with
  | zero => rfl
  | succ n ih =>
    have head : block g k start piece = true := by
      apply chunkPass_block
      simpa using checks ⟨0, by omega⟩
    have tail := ih (start+piece) (fun i => by
      have h := checks i.succ
      change chunkPass g k (start+piece*(i.val+1)) piece = true at h
      rwa [Nat.mul_succ,Nat.add_comm (piece*i.val) piece,←Nat.add_assoc] at h)
    rw [Nat.mul_succ,Nat.add_comm (piece*n) piece]
    exact block_merge head tail

theorem seededFinish (g : Forest) (m cap hints : Nat) {prior seeded : Nat → Nat}
    (plain : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (seedProof : ∀ q, SeedBound q (seeded q))
    (geometry : graphValid g prior seeded = true)
    (tables : checkedTables g cap)
    (data : prior m = cap+1 ∧ properB (graphGoal m) = true ∧
      checkEssential (graphGoal m) (seededInputs m) (graphPairs m hints) = true ∧
      targetOf g = graphGoal m ∧ indexedRoot g cap 0 (seededInputs m) = true) :
    SeedBound m (cap+1) := by
  obtain ⟨count,properT,essential,target,start⟩ := data
  have excluded := root_index_seed (g:=g) (top:=cap) (prior:=prior) (seeded:=seeded)
    (k:=cap) (i:=0) (ws:=seededInputs m) plain seedProof geometry tables (Nat.le_refl cap) start
  rw [target] at excluded
  exact lower_seeded (m:=m) (cap:=cap) (hints:=hints) properT essential (count ▸ plain m) excluded

theorem seededByCount (m cap hints : Nat) {prior : Nat → Nat}
    (plain : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (data : prior m = cap+1 ∧ properB (graphGoal m) = true ∧
      checkEssential (graphGoal m) (seededInputs m) (graphPairs m hints) = true ∧
      cap+1 < (seededInputs m).toFinset.card) : SeedBound m (cap+1) := by
  obtain ⟨size,properT,essential,need⟩ := data
  apply lower_seeded (m:=m) (cap:=cap) (hints:=hints) properT essential (size ▸ plain m)
  intro k t budget run
  have enough := (live_size run).2
  omega

def registered0 : List (Nat × Nat) := []
theorem registered0Valid : KnownSeed registered0 := knownSeedNil

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem seedBound15 : SeedBound 15 4 :=
  seededByCount 15 3 8449 (before_sound known383 valid383) (by decide +kernel)

def chart15Relabels : List (Nat × List Nat) := [(163,[115,50,98,83,66,16]),(135,[115,99,83,67]),(15,[]),(27,[66,16])]
def registered15 := extendKnown registered0 4 chart15Relabels
theorem registered15Valid : KnownSeed registered15 :=
  extendKnownSeed registered0Valid seedBound15 (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem seedBound23 : SeedBound 23 4 :=
  seededByCount 23 3 257 (before_sound known383 valid383) (by decide +kernel)

def chart23Relabels : List (Nat × List Nat) := [(99,[66,100,82,50]),(39,[84]),(23,[])]
def registered23 := extendKnown registered15 4 chart23Relabels
theorem registered23Valid : KnownSeed registered23 :=
  extendKnownSeed registered15Valid seedBound23 (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem seedBound47 : SeedBound 47 5 :=
  seededByCount 47 4 8449 (before_sound known383 valid383) (by decide +kernel)

def chart47Relabels : List (Nat × List Nat) := [(227,[83,82,114,99,66,16]),(47,[]),(339,[131,50,114,82,99,66]),(151,[115,99,83,67])]
def registered47 := extendKnown registered23 5 chart47Relabels
theorem registered47Valid : KnownSeed registered47 :=
  extendKnownSeed registered23Valid seedBound47 (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem seedBound55 : SeedBound 55 5 :=
  seededByCount 55 4 257 (before_sound known383 valid383) (by decide +kernel)

def chart55Relabels : List (Nat × List Nat) := [(103,[82,98,66,16]),(115,[98,50]),(55,[])]
def registered55 := extendKnown registered47 5 chart55Relabels
theorem registered55Valid : KnownSeed registered55 :=
  extendKnownSeed registered47Valid seedBound55 (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem seedBound79 : SeedBound 79 5 :=
  seededByCount 79 4 16785665 (before_sound known383 valid383) (by decide +kernel)

def chart79Relabels : List (Nat × List Nat) := [(327,[131,115,83,67,98]),(79,[]),(179,[115,50,98,83,66,16])]
def registered79 := extendKnown registered55 5 chart79Relabels
theorem registered79Valid : KnownSeed registered79 :=
  extendKnownSeed registered55Valid seedBound79 (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem seedBound143 : SeedBound 143 5 :=
  seededByCount 143 4 536879361 (before_sound known383 valid383) (by decide +kernel)

def chart143Relabels : List (Nat × List Nat) := [(143,[])]
def registered143 := extendKnown registered79 5 chart143Relabels
theorem registered143Valid : KnownSeed registered143 :=
  extendKnownSeed registered79Valid seedBound143 (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem seedBound331 : SeedBound 331 5 :=
  seededByCount 331 4 12901711873 (before_sound known383 valid383) (by decide +kernel)

def chart331Relabels : List (Nat × List Nat) := [(331,[])]
def registered331 := extendKnown registered143 5 chart331Relabels
theorem registered331Valid : KnownSeed registered331 :=
  extendKnownSeed registered143Valid seedBound331 (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem geometry167 :
    graphValid chart167 (boundsBefore known383) (boundsBefore registered331) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks167_5_0 : chunkPass chart167 5 0 4 = true := by decide +kernel

theorem verified167_5 : block chart167 5 0 4 = true :=
  (chunkPass_block checks167_5_0)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem chart167Root0 : nodeVerified chart167 6 0 = true := by
  apply ofContextPasses (by decide +kernel)
  change ∀ w : Fin 6, oneContextPass (contextOf chart167 6 0) w.val = true
  intro w
  fin_cases w <;> decide +kernel

theorem verified167_6 : block chart167 6 0 1 = true := by
  simp only [block,Nat.reduceAdd,Bool.and_eq_true,chart167Root0,true_and,and_true]

theorem verifiedChart167 : checkedTables chart167 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact verified167_5
  · exact verified167_6

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem seedBound167 : SeedBound 167 7 :=
  seededFinish chart167 167 6 536871169
    (before_sound known383 valid383) (beforeSeed_sound registered331 registered331Valid)
    geometry167 verifiedChart167 (by decide +kernel)

def chart167Relabels : List (Nat × List Nat) := [(355,[135,98,66,50]),(31,[100,67,84,115]),(167,[])]
def registered167 := extendKnown registered331 7 chart167Relabels
theorem registered167Valid : KnownSeed registered167 :=
  extendKnownSeed registered331Valid seedBound167 (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem geometry63 :
    graphValid chart63 (boundsBefore known383) (boundsBefore registered167) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem chart63Root0 : nodeVerified chart63 7 0 = true := by
  apply ofContextPasses (by decide +kernel)
  change ∀ w : Fin 7, oneContextPass (contextOf chart63 7 0) w.val = true
  intro w
  fin_cases w <;> decide +kernel

theorem verified63_7 : block chart63 7 0 1 = true := by
  simp only [block,Nat.reduceAdd,Bool.and_eq_true,chart63Root0,true_and,and_true]

theorem verifiedChart63 : checkedTables chart63 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact verified63_7

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem seedBound63 : SeedBound 63 8 :=
  seededFinish chart63 63 7 8449
    (before_sound known383 valid383) (beforeSeed_sound registered167 registered167Valid)
    geometry63 verifiedChart63 (by decide +kernel)

def chart63Relabels : List (Nat × List Nat) := [(231,[83,82,114,99,66,16]),(359,[131,67,116,99,82,16]),(371,[131,84,115,98]),(183,[115,84,99]),(63,[]),(95,[101,66,16])]
def registered63 := extendKnown registered167 8 chart63Relabels
theorem registered63Valid : KnownSeed registered63 :=
  extendKnownSeed registered167Valid seedBound63 (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem seedBound119 : SeedBound 119 6 :=
  seededByCount 119 5 16777473 (before_sound known383 valid383) (by decide +kernel)

def chart119Relabels : List (Nat × List Nat) := [(119,[])]
def registered119 := extendKnown registered63 6 chart119Relabels
theorem registered119Valid : KnownSeed registered119 :=
  extendKnownSeed registered63Valid seedBound119 (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem geometry159 :
    graphValid chart159 (boundsBefore known383) (boundsBefore registered119) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem chart159Root0 : nodeVerified chart159 7 0 = true := by
  apply ofContextPasses (by decide +kernel)
  change ∀ w : Fin 7, oneContextPass (contextOf chart159 7 0) w.val = true
  intro w
  fin_cases w <;> decide +kernel

theorem verified159_7 : block chart159 7 0 1 = true := by
  simp only [block,Nat.reduceAdd,Bool.and_eq_true,chart159Root0,true_and,and_true]

theorem verifiedChart159 : checkedTables chart159 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact verified159_7

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem seedBound159 : SeedBound 159 8 :=
  seededFinish chart159 159 7 536879361
    (before_sound known383 valid383) (beforeSeed_sound registered119 registered119Valid)
    geometry159 verifiedChart159 (by decide +kernel)

def chart159Relabels : List (Nat × List Nat) := [(175,[84,115]),(159,[])]
def registered159 := extendKnown registered119 8 chart159Relabels
theorem registered159Valid : KnownSeed registered159 :=
  extendKnownSeed registered119Valid seedBound159 (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem geometry187 :
    graphValid chart187 (boundsBefore known383) (boundsBefore registered159) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem chart187Root0 : nodeVerified chart187 6 0 = true := by
  apply ofContextPasses (by decide +kernel)
  change ∀ w : Fin 7, oneContextPass (contextOf chart187 6 0) w.val = true
  intro w
  fin_cases w <;> decide +kernel

theorem verified187_6 : block chart187 6 0 1 = true := by
  simp only [block,Nat.reduceAdd,Bool.and_eq_true,chart187Root0,true_and,and_true]

theorem verifiedChart187 : checkedTables chart187 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact verified187_6

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem seedBound187 : SeedBound 187 7 :=
  seededFinish chart187 187 6 1342193665
    (before_sound known383 valid383) (beforeSeed_sound registered159 registered159Valid)
    geometry187 verifiedChart187 (by decide +kernel)

def chart187Relabels : List (Nat × List Nat) := [(455,[115,83,133,99,50,66,16]),(187,[])]
def registered187 := extendKnown registered159 7 chart187Relabels
theorem registered187Valid : KnownSeed registered187 :=
  extendKnownSeed registered159Valid seedBound187 (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem seedBound207 : SeedBound 207 6 :=
  seededByCount 207 5 553656577 (before_sound known383 valid383) (by decide +kernel)

def chart207Relabels : List (Nat × List Nat) := [(207,[])]
def registered207 := extendKnown registered187 6 chart207Relabels
theorem registered207Valid : KnownSeed registered207 :=
  extendKnownSeed registered187Valid seedBound207 (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem geometry215 :
    graphValid chart215 (boundsBefore known383) (boundsBefore registered207) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks215_5_0 : chunkPass chart215 5 0 1 = true := by decide +kernel

theorem verified215_5 : block chart215 5 0 1 = true :=
  (chunkPass_block checks215_5_0)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem chart215Root0 : nodeVerified chart215 6 0 = true := by
  apply ofContextPasses (by decide +kernel)
  change ∀ w : Fin 7, oneContextPass (contextOf chart215 6 0) w.val = true
  intro w
  fin_cases w <;> decide +kernel

theorem verified215_6 : block chart215 6 0 1 = true := by
  simp only [block,Nat.reduceAdd,Bool.and_eq_true,chart215Root0,true_and,and_true]

theorem verifiedChart215 : checkedTables chart215 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact verified215_5
  · exact verified215_6

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem seedBound215 : SeedBound 215 7 :=
  seededFinish chart215 215 6 553648385
    (before_sound known383 valid383) (beforeSeed_sound registered207 registered207Valid)
    geometry215 verifiedChart215 (by decide +kernel)

def chart215Relabels : List (Nat × List Nat) := [(243,[100,82,50,16]),(215,[])]
def registered215 := extendKnown registered207 7 chart215Relabels
theorem registered215Valid : KnownSeed registered215 :=
  extendKnownSeed registered207Valid seedBound215 (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem geometry347 :
    graphValid chart347 (boundsBefore known383) (boundsBefore registered215) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks347_6_0 : chunkPass chart347 6 0 3 = true := by decide +kernel

theorem verified347_6 : block chart347 6 0 3 = true :=
  (chunkPass_block checks347_6_0)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem chart347Root0 : nodeVerified chart347 7 0 = true := by
  apply ofContextPasses (by decide +kernel)
  change ∀ w : Fin 7, oneContextPass (contextOf chart347 7 0) w.val = true
  intro w
  fin_cases w <;> decide +kernel

theorem verified347_7 : block chart347 7 0 1 = true := by
  simp only [block,Nat.reduceAdd,Bool.and_eq_true,chart347Root0,true_and,and_true]

theorem verifiedChart347 : checkedTables chart347 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact verified347_6
  · exact verified347_7

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem seedBound347 : SeedBound 347 8 :=
  seededFinish chart347 347 7 12901695489
    (before_sound known383 valid383) (beforeSeed_sound registered215 registered215Valid)
    geometry347 verifiedChart347 (by decide +kernel)

def chart347Relabels : List (Nat × List Nat) := [(347,[])]
def registered347 := extendKnown registered215 8 chart347Relabels
theorem registered347Valid : KnownSeed registered347 :=
  extendKnownSeed registered215Valid seedBound347 (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem geometry127 :
    graphValid chart127 (boundsBefore known383) (boundsBefore registered347) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem chart127Root0 : nodeVerified chart127 8 0 = true := by
  apply ofContextPasses (by decide +kernel)
  change ∀ w : Fin 8, oneContextPass (contextOf chart127 8 0) w.val = true
  intro w
  fin_cases w <;> decide +kernel

theorem verified127_8 : block chart127 8 0 1 = true := by
  simp only [block,Nat.reduceAdd,Bool.and_eq_true,chart127Root0,true_and,and_true]

theorem verifiedChart127 : checkedTables chart127 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact verified127_8

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem seedBound127 : SeedBound 127 9 :=
  seededFinish chart127 127 8 16785665
    (before_sound known383 valid383) (beforeSeed_sound registered347 registered347Valid)
    geometry127 verifiedChart127 (by decide +kernel)

def chart127Relabels : List (Nat × List Nat) := [(127,[]),(247,[84,115]),(375,[131,84,115,98])]
def registered127 := extendKnown registered347 9 chart127Relabels
theorem registered127Valid : KnownSeed registered127 :=
  extendKnownSeed registered347Valid seedBound127 (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem geometry223 :
    graphValid chart223 (boundsBefore known383) (boundsBefore registered127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem chart223Root0 : nodeVerified chart223 8 0 = true := by
  apply ofContextPasses (by decide +kernel)
  change ∀ w : Fin 8, oneContextPass (contextOf chart223 8 0) w.val = true
  intro w
  fin_cases w <;> decide +kernel

theorem verified223_8 : block chart223 8 0 1 = true := by
  simp only [block,Nat.reduceAdd,Bool.and_eq_true,chart223Root0,true_and,and_true]

theorem verifiedChart223 : checkedTables chart223 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact verified223_8

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem seedBound223 : SeedBound 223 9 :=
  seededFinish chart223 223 8 553656577
    (before_sound known383 valid383) (beforeSeed_sound registered127 registered127Valid)
    geometry223 verifiedChart223 (by decide +kernel)

def chart223Relabels : List (Nat × List Nat) := [(223,[]),(499,[100,131,82,16])]
def registered223 := extendKnown registered127 9 chart223Relabels
theorem registered223Valid : KnownSeed registered223 :=
  extendKnownSeed registered127Valid seedBound223 (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem geometry251 :
    graphValid chart251 (boundsBefore known383) (boundsBefore registered223) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem chart251Root0 : nodeVerified chart251 7 0 = true := by
  apply ofContextPasses (by decide +kernel)
  change ∀ w : Fin 8, oneContextPass (contextOf chart251 7 0) w.val = true
  intro w
  fin_cases w <;> decide +kernel

theorem verified251_7 : block chart251 7 0 1 = true := by
  simp only [block,Nat.reduceAdd,Bool.and_eq_true,chart251Root0,true_and,and_true]

theorem verifiedChart251 : checkedTables chart251 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact verified251_7

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem seedBound251 : SeedBound 251 8 :=
  seededFinish chart251 251 7 1358970881
    (before_sound known383 valid383) (beforeSeed_sound registered223 registered223Valid)
    geometry251 verifiedChart251 (by decide +kernel)

def chart251Relabels : List (Nat × List Nat) := [(471,[115,83,133,99,50,66,16]),(251,[])]
def registered251 := extendKnown registered223 8 chart251Relabels
theorem registered251Valid : KnownSeed registered251 :=
  extendKnownSeed registered223Valid seedBound251 (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem geometry415 :
    graphValid chart415 (boundsBefore known383) (boundsBefore registered251) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem chart415Root0 : nodeVerified chart415 8 0 = true := by
  apply ofContextPasses (by decide +kernel)
  change ∀ w : Fin 8, oneContextPass (contextOf chart415 8 0) w.val = true
  intro w
  fin_cases w <;> decide +kernel

theorem verified415_8 : block chart415 8 0 1 = true := by
  simp only [block,Nat.reduceAdd,Bool.and_eq_true,chart415Root0,true_and,and_true]

theorem verifiedChart415 : checkedTables chart415 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact verified415_8

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem seedBound415 : SeedBound 415 9 :=
  seededFinish chart415 415 8 13421781249
    (before_sound known383 valid383) (beforeSeed_sound registered251 registered251Valid)
    geometry415 verifiedChart415 (by decide +kernel)

def chart415Relabels : List (Nat × List Nat) := [(415,[])]
def registered415 := extendKnown registered251 9 chart415Relabels
theorem registered415Valid : KnownSeed registered415 :=
  extendKnownSeed registered251Valid seedBound415 (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem geometry431 :
    graphValid chart431 (boundsBefore known383) (boundsBefore registered415) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks431_6_0 : chunkPass chart431 6 0 10 = true := by decide +kernel

theorem verified431_6 : block chart431 6 0 10 = true :=
  (chunkPass_block checks431_6_0)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks431_7_0 : ∀ i : Fin 2, chunkPass chart431 7 (0+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks431_7_1 : chunkPass chart431 7 32 12 = true := by decide +kernel

theorem verified431_7 : block chart431 7 0 44 = true :=
  (@block_merge chart431 7 0 32 12 (blocksByChunks chart431 7 0 16 2 checks431_7_0) (chunkPass_block checks431_7_1))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks431_8_0 : ∀ i : Fin 5, chunkPass chart431 8 (0+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks431_8_1 : ∀ i : Fin 2, chunkPass chart431 8 (80+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks431_8_2 : chunkPass chart431 8 112 4 = true := by decide +kernel

theorem verified431_8 : block chart431 8 0 116 = true :=
  (@block_merge chart431 8 0 80 36 (blocksByChunks chart431 8 0 16 5 checks431_8_0) (@block_merge chart431 8 80 32 4 (blocksByChunks chart431 8 80 16 2 checks431_8_1) (chunkPass_block checks431_8_2)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks431_9_0 : ∀ i : Fin 1, chunkPass chart431 9 (0+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

theorem verified431_9 : block chart431 9 0 16 = true :=
  (blocksByChunks chart431 9 0 16 1 checks431_9_0)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem chart431Root0 : nodeVerified chart431 10 0 = true := by
  apply ofContextPasses (by decide +kernel)
  change ∀ w : Fin 8, oneContextPass (contextOf chart431 10 0) w.val = true
  intro w
  fin_cases w <;> decide +kernel

theorem verified431_10 : block chart431 10 0 1 = true := by
  simp only [block,Nat.reduceAdd,Bool.and_eq_true,chart431Root0,true_and,and_true]

theorem verifiedChart431 : checkedTables chart431 10 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact verified431_6
  · exact verified431_7
  · exact verified431_8
  · exact verified431_9
  · exact verified431_10

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem seedBound431 : SeedBound 431 11 :=
  seededFinish chart431 431 10 13421781249
    (before_sound known383 valid383) (beforeSeed_sound registered415 registered415Valid)
    geometry431 verifiedChart431 (by decide +kernel)

def chart431Relabels : List (Nat × List Nat) := [(431,[])]
def registered431 := extendKnown registered415 11 chart431Relabels
theorem registered431Valid : KnownSeed registered431 :=
  extendKnownSeed registered415Valid seedBound431 (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem geometry351 :
    graphValid chart351 (boundsBefore known383) (boundsBefore registered431) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks351_6_0 : chunkPass chart351 6 0 5 = true := by decide +kernel

theorem verified351_6 : block chart351 6 0 5 = true :=
  (chunkPass_block checks351_6_0)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks351_7_0 : ∀ i : Fin 5, chunkPass chart351 7 (0+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks351_7_1 : chunkPass chart351 7 80 3 = true := by decide +kernel

theorem verified351_7 : block chart351 7 0 83 = true :=
  (@block_merge chart351 7 0 80 3 (blocksByChunks chart351 7 0 16 5 checks351_7_0) (chunkPass_block checks351_7_1))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks351_8_0 : ∀ i : Fin 5, chunkPass chart351 8 (0+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks351_8_1 : ∀ i : Fin 5, chunkPass chart351 8 (80+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks351_8_2 : ∀ i : Fin 5, chunkPass chart351 8 (160+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks351_8_3 : ∀ i : Fin 5, chunkPass chart351 8 (240+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks351_8_4 : chunkPass chart351 8 320 3 = true := by decide +kernel

theorem verified351_8 : block chart351 8 0 323 = true :=
  (@block_merge chart351 8 0 160 163 (@block_merge chart351 8 0 80 80 (blocksByChunks chart351 8 0 16 5 checks351_8_0) (blocksByChunks chart351 8 80 16 5 checks351_8_1)) (@block_merge chart351 8 160 80 83 (blocksByChunks chart351 8 160 16 5 checks351_8_2) (@block_merge chart351 8 240 80 3 (blocksByChunks chart351 8 240 16 5 checks351_8_3) (chunkPass_block checks351_8_4))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks351_9_0 : ∀ i : Fin 2, chunkPass chart351 9 (0+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks351_9_1 : chunkPass chart351 9 32 14 = true := by decide +kernel

theorem verified351_9 : block chart351 9 0 46 = true :=
  (@block_merge chart351 9 0 32 14 (blocksByChunks chart351 9 0 16 2 checks351_9_0) (chunkPass_block checks351_9_1))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem chart351Root0 : nodeVerified chart351 10 0 = true := by
  apply ofContextPasses (by decide +kernel)
  change ∀ w : Fin 8, oneContextPass (contextOf chart351 10 0) w.val = true
  intro w
  fin_cases w <;> decide +kernel

theorem verified351_10 : block chart351 10 0 1 = true := by
  simp only [block,Nat.reduceAdd,Bool.and_eq_true,chart351Root0,true_and,and_true]

theorem verifiedChart351 : checkedTables chart351 10 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact verified351_6
  · exact verified351_7
  · exact verified351_8
  · exact verified351_9
  · exact verified351_10

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem seedBound351 : SeedBound 351 11 :=
  seededFinish chart351 351 10 12901687553
    (before_sound known383 valid383) (beforeSeed_sound registered431 registered431Valid)
    geometry351 verifiedChart351 (by decide +kernel)

def chart351Relabels : List (Nat × List Nat) := [(367,[84,131,98]),(351,[]),(379,[100,131,82,16]),(319,[101,66,16])]
def registered351 := extendKnown registered431 11 chart351Relabels
theorem registered351Valid : KnownSeed registered351 :=
  extendKnownSeed registered431Valid seedBound351 (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem geometry191 :
    graphValid chart191 (boundsBefore known383) (boundsBefore registered351) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks191_5_0 : chunkPass chart191 5 0 2 = true := by decide +kernel

theorem verified191_5 : block chart191 5 0 2 = true :=
  (chunkPass_block checks191_5_0)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks191_6_0 : ∀ i : Fin 1, chunkPass chart191 6 (0+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks191_6_1 : chunkPass chart191 6 16 5 = true := by decide +kernel

theorem verified191_6 : block chart191 6 0 21 = true :=
  (@block_merge chart191 6 0 16 5 (blocksByChunks chart191 6 0 16 1 checks191_6_0) (chunkPass_block checks191_6_1))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks191_7_0 : ∀ i : Fin 5, chunkPass chart191 7 (0+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks191_7_1 : ∀ i : Fin 1, chunkPass chart191 7 (80+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks191_7_2 : chunkPass chart191 7 96 6 = true := by decide +kernel

theorem verified191_7 : block chart191 7 0 102 = true :=
  (@block_merge chart191 7 0 80 22 (blocksByChunks chart191 7 0 16 5 checks191_7_0) (@block_merge chart191 7 80 16 6 (blocksByChunks chart191 7 80 16 1 checks191_7_1) (chunkPass_block checks191_7_2)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks191_8_0 : ∀ i : Fin 5, chunkPass chart191 8 (0+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks191_8_1 : ∀ i : Fin 5, chunkPass chart191 8 (80+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks191_8_2 : ∀ i : Fin 5, chunkPass chart191 8 (160+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks191_8_3 : ∀ i : Fin 5, chunkPass chart191 8 (240+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks191_8_4 : ∀ i : Fin 2, chunkPass chart191 8 (320+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

theorem verified191_8 : block chart191 8 0 352 = true :=
  (@block_merge chart191 8 0 160 192 (@block_merge chart191 8 0 80 80 (blocksByChunks chart191 8 0 16 5 checks191_8_0) (blocksByChunks chart191 8 80 16 5 checks191_8_1)) (@block_merge chart191 8 160 80 112 (blocksByChunks chart191 8 160 16 5 checks191_8_2) (@block_merge chart191 8 240 80 32 (blocksByChunks chart191 8 240 16 5 checks191_8_3) (blocksByChunks chart191 8 320 16 2 checks191_8_4))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks191_9_0 : ∀ i : Fin 2, chunkPass chart191 9 (0+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks191_9_1 : chunkPass chart191 9 32 14 = true := by decide +kernel

theorem verified191_9 : block chart191 9 0 46 = true :=
  (@block_merge chart191 9 0 32 14 (blocksByChunks chart191 9 0 16 2 checks191_9_0) (chunkPass_block checks191_9_1))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem chart191Root0 : nodeVerified chart191 10 0 = true := by
  apply ofContextPasses (by decide +kernel)
  change ∀ w : Fin 8, oneContextPass (contextOf chart191 10 0) w.val = true
  intro w
  fin_cases w <;> decide +kernel

theorem verified191_10 : block chart191 10 0 1 = true := by
  simp only [block,Nat.reduceAdd,Bool.and_eq_true,chart191Root0,true_and,and_true]

theorem verifiedChart191 : checkedTables chart191 10 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact verified191_5
  · exact verified191_6
  · exact verified191_7
  · exact verified191_8
  · exact verified191_9
  · exact verified191_10

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem seedBound191 : SeedBound 191 11 :=
  seededFinish chart191 191 10 536879361
    (before_sound known383 valid383) (beforeSeed_sound registered351 registered351Valid)
    geometry191 verifiedChart191 (by decide +kernel)

def chart191Relabels : List (Nat × List Nat) := [(487,[115,83,82,130,99,66,16]),(191,[])]
def registered191 := extendKnown registered351 11 chart191Relabels
theorem registered191Valid : KnownSeed registered191 :=
  extendKnownSeed registered351Valid seedBound191 (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem geometry255 :
    graphValid chart255 (boundsBefore known383) (boundsBefore registered191) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem chart255Root0 : nodeVerified chart255 11 0 = true := by
  apply ofContextPasses (by decide +kernel)
  change ∀ w : Fin 9, oneContextPass (contextOf chart255 11 0) w.val = true
  intro w
  fin_cases w <;> decide +kernel

theorem verified255_11 : block chart255 11 0 1 = true := by
  simp only [block,Nat.reduceAdd,Bool.and_eq_true,chart255Root0,true_and,and_true]

theorem verifiedChart255 : checkedTables chart255 11 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact verified255_11

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem seedBound255 : SeedBound 255 12 :=
  seededFinish chart255 255 11 553656577
    (before_sound known383 valid383) (beforeSeed_sound registered191 registered191Valid)
    geometry255 verifiedChart255 (by decide +kernel)

def chart255Relabels : List (Nat × List Nat) := [(255,[]),(503,[115,82,98,131,66,16])]
def registered255 := extendKnown registered191 12 chart255Relabels
theorem registered255Valid : KnownSeed registered255 :=
  extendKnownSeed registered191Valid seedBound255 (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem geometry479 :
    graphValid chart479 (boundsBefore known383) (boundsBefore registered255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem chart479Root0 : nodeVerified chart479 11 0 = true := by
  apply ofContextPasses (by decide +kernel)
  change ∀ w : Fin 9, oneContextPass (contextOf chart479 11 0) w.val = true
  intro w
  fin_cases w <;> decide +kernel

theorem verified479_11 : block chart479 11 0 1 = true := by
  simp only [block,Nat.reduceAdd,Bool.and_eq_true,chart479Root0,true_and,and_true]

theorem verifiedChart479 : checkedTables chart479 11 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact verified479_11

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem seedBound479 : SeedBound 479 12 :=
  seededFinish chart479 479 11 13438558465
    (before_sound known383 valid383) (beforeSeed_sound registered255 registered255Valid)
    geometry479 verifiedChart479 (by decide +kernel)

def chart479Relabels : List (Nat × List Nat) := [(507,[100,131,82,16]),(479,[])]
def registered479 := extendKnown registered255 12 chart479Relabels
theorem registered479Valid : KnownSeed registered479 :=
  extendKnownSeed registered255Valid seedBound479 (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem geometry383 :
    graphValid chart383 (boundsBefore known383) (boundsBefore registered479) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks383_8_0 : ∀ i : Fin 4, chunkPass chart383 8 (0+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks383_8_1 : chunkPass chart383 8 64 4 = true := by decide +kernel

theorem verified383_8 : block chart383 8 0 68 = true :=
  (@block_merge chart383 8 0 64 4 (blocksByChunks chart383 8 0 16 4 checks383_8_0) (chunkPass_block checks383_8_1))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks383_9_0 : ∀ i : Fin 5, chunkPass chart383 9 (0+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks383_9_1 : ∀ i : Fin 5, chunkPass chart383 9 (80+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks383_9_2 : ∀ i : Fin 5, chunkPass chart383 9 (160+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks383_9_3 : ∀ i : Fin 4, chunkPass chart383 9 (240+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks383_9_4 : chunkPass chart383 9 304 7 = true := by decide +kernel

theorem verified383_9 : block chart383 9 0 311 = true :=
  (@block_merge chart383 9 0 160 151 (@block_merge chart383 9 0 80 80 (blocksByChunks chart383 9 0 16 5 checks383_9_0) (blocksByChunks chart383 9 80 16 5 checks383_9_1)) (@block_merge chart383 9 160 80 71 (blocksByChunks chart383 9 160 16 5 checks383_9_2) (@block_merge chart383 9 240 64 7 (blocksByChunks chart383 9 240 16 4 checks383_9_3) (chunkPass_block checks383_9_4))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks383_10_0 : ∀ i : Fin 5, chunkPass chart383 10 (0+12*i.val) 12 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks383_10_1 : ∀ i : Fin 5, chunkPass chart383 10 (60+12*i.val) 12 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks383_10_2 : ∀ i : Fin 5, chunkPass chart383 10 (120+12*i.val) 12 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks383_10_3 : chunkPass chart383 10 180 9 = true := by decide +kernel

theorem verified383_10 : block chart383 10 0 189 = true :=
  (@block_merge chart383 10 0 120 69 (@block_merge chart383 10 0 60 60 (blocksByChunks chart383 10 0 12 5 checks383_10_0) (blocksByChunks chart383 10 60 12 5 checks383_10_1)) (@block_merge chart383 10 120 60 9 (blocksByChunks chart383 10 120 12 5 checks383_10_2) (chunkPass_block checks383_10_3)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks383_11_0 : ∀ i : Fin 2, chunkPass chart383 11 (0+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks383_11_1 : chunkPass chart383 11 16 2 = true := by decide +kernel

theorem verified383_11 : block chart383 11 0 18 = true :=
  (@block_merge chart383 11 0 16 2 (blocksByChunks chart383 11 0 8 2 checks383_11_0) (chunkPass_block checks383_11_1))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem chart383Root0 : nodeVerified chart383 12 0 = true := by
  apply ofContextPasses (by decide +kernel)
  change ∀ w : Fin 9, oneContextPass (contextOf chart383 12 0) w.val = true
  intro w
  fin_cases w <;> decide +kernel

theorem verified383_12 : block chart383 12 0 1 = true := by
  simp only [block,Nat.reduceAdd,Bool.and_eq_true,chart383Root0,true_and,and_true]

theorem verifiedChart383 : checkedTables chart383 12 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact verified383_8
  · exact verified383_9
  · exact verified383_10
  · exact verified383_11
  · exact verified383_12

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem seedBound383 : SeedBound 383 13 :=
  seededFinish chart383 383 12 12901687553
    (before_sound known383 valid383) (beforeSeed_sound registered479 registered479Valid)
    geometry383 verifiedChart383 (by decide +kernel)

def chart383Relabels : List (Nat × List Nat) := [(383,[])]
def registered383 := extendKnown registered479 13 chart383Relabels
theorem registered383Valid : KnownSeed registered383 :=
  extendKnownSeed registered479Valid seedBound383 (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem geometry495 :
    graphValid chart495 (boundsBefore known383) (boundsBefore registered383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks495_8_0 : ∀ i : Fin 4, chunkPass chart495 8 (0+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks495_8_1 : chunkPass chart495 8 64 1 = true := by decide +kernel

theorem verified495_8 : block chart495 8 0 65 = true :=
  (@block_merge chart495 8 0 64 1 (blocksByChunks chart495 8 0 16 4 checks495_8_0) (chunkPass_block checks495_8_1))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks495_9_0 : ∀ i : Fin 5, chunkPass chart495 9 (0+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks495_9_1 : ∀ i : Fin 5, chunkPass chart495 9 (80+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks495_9_2 : ∀ i : Fin 5, chunkPass chart495 9 (160+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks495_9_3 : ∀ i : Fin 5, chunkPass chart495 9 (240+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks495_9_4 : ∀ i : Fin 5, chunkPass chart495 9 (320+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks495_9_5 : ∀ i : Fin 4, chunkPass chart495 9 (400+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks495_9_6 : chunkPass chart495 9 464 1 = true := by decide +kernel

theorem verified495_9 : block chart495 9 0 465 = true :=
  (@block_merge chart495 9 0 240 225 (@block_merge chart495 9 0 80 160 (blocksByChunks chart495 9 0 16 5 checks495_9_0) (@block_merge chart495 9 80 80 80 (blocksByChunks chart495 9 80 16 5 checks495_9_1) (blocksByChunks chart495 9 160 16 5 checks495_9_2))) (@block_merge chart495 9 240 160 65 (@block_merge chart495 9 240 80 80 (blocksByChunks chart495 9 240 16 5 checks495_9_3) (blocksByChunks chart495 9 320 16 5 checks495_9_4)) (@block_merge chart495 9 400 64 1 (blocksByChunks chart495 9 400 16 4 checks495_9_5) (chunkPass_block checks495_9_6))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks495_10_0 : ∀ i : Fin 5, chunkPass chart495 10 (0+12*i.val) 12 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks495_10_1 : ∀ i : Fin 5, chunkPass chart495 10 (60+12*i.val) 12 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks495_10_2 : ∀ i : Fin 5, chunkPass chart495 10 (120+12*i.val) 12 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks495_10_3 : ∀ i : Fin 5, chunkPass chart495 10 (180+12*i.val) 12 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks495_10_4 : ∀ i : Fin 5, chunkPass chart495 10 (240+12*i.val) 12 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks495_10_5 : chunkPass chart495 10 300 2 = true := by decide +kernel

theorem verified495_10 : block chart495 10 0 302 = true :=
  (@block_merge chart495 10 0 180 122 (@block_merge chart495 10 0 60 120 (blocksByChunks chart495 10 0 12 5 checks495_10_0) (@block_merge chart495 10 60 60 60 (blocksByChunks chart495 10 60 12 5 checks495_10_1) (blocksByChunks chart495 10 120 12 5 checks495_10_2))) (@block_merge chart495 10 180 60 62 (blocksByChunks chart495 10 180 12 5 checks495_10_3) (@block_merge chart495 10 240 60 2 (blocksByChunks chart495 10 240 12 5 checks495_10_4) (chunkPass_block checks495_10_5))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks495_11_0 : ∀ i : Fin 3, chunkPass chart495 11 (0+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks495_11_1 : chunkPass chart495 11 24 4 = true := by decide +kernel

theorem verified495_11 : block chart495 11 0 28 = true :=
  (@block_merge chart495 11 0 24 4 (blocksByChunks chart495 11 0 8 3 checks495_11_0) (chunkPass_block checks495_11_1))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem chart495Root0 : nodeVerified chart495 12 0 = true := by
  apply ofContextPasses (by decide +kernel)
  change ∀ w : Fin 9, oneContextPass (contextOf chart495 12 0) w.val = true
  intro w
  fin_cases w <;> decide +kernel

theorem verified495_12 : block chart495 12 0 1 = true := by
  simp only [block,Nat.reduceAdd,Bool.and_eq_true,chart495Root0,true_and,and_true]

theorem verifiedChart495 : checkedTables chart495 12 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact verified495_8
  · exact verified495_9
  · exact verified495_10
  · exact verified495_11
  · exact verified495_12

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem seedBound495 : SeedBound 495 13 :=
  seededFinish chart495 495 12 13438558465
    (before_sound known383 valid383) (beforeSeed_sound registered383 registered383Valid)
    geometry495 verifiedChart495 (by decide +kernel)

def chart495Relabels : List (Nat × List Nat) := [(447,[100,131,82,16]),(495,[])]
def registered495 := extendKnown registered383 13 chart495Relabels
theorem registered495Valid : KnownSeed registered495 :=
  extendKnownSeed registered383Valid seedBound495 (by decide +kernel)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem geometry511 :
    graphValid chart511 (boundsBefore known383) (boundsBefore registered495) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,by decide +kernel⟩
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_8_0 : chunkPass chart511 8 0 3 = true := by decide +kernel

theorem verified511_8 : block chart511 8 0 3 = true :=
  (chunkPass_block checks511_8_0)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_9_0 : ∀ i : Fin 5, chunkPass chart511 9 (0+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_9_1 : ∀ i : Fin 1, chunkPass chart511 9 (80+16*i.val) 16 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_9_2 : chunkPass chart511 9 96 8 = true := by decide +kernel

theorem verified511_9 : block chart511 9 0 104 = true :=
  (@block_merge chart511 9 0 80 24 (blocksByChunks chart511 9 0 16 5 checks511_9_0) (@block_merge chart511 9 80 16 8 (blocksByChunks chart511 9 80 16 1 checks511_9_1) (chunkPass_block checks511_9_2)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_10_0 : ∀ i : Fin 5, chunkPass chart511 10 (0+12*i.val) 12 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_10_1 : ∀ i : Fin 5, chunkPass chart511 10 (60+12*i.val) 12 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_10_2 : ∀ i : Fin 5, chunkPass chart511 10 (120+12*i.val) 12 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_10_3 : ∀ i : Fin 5, chunkPass chart511 10 (180+12*i.val) 12 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_10_4 : ∀ i : Fin 5, chunkPass chart511 10 (240+12*i.val) 12 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_10_5 : ∀ i : Fin 5, chunkPass chart511 10 (300+12*i.val) 12 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_10_6 : ∀ i : Fin 5, chunkPass chart511 10 (360+12*i.val) 12 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_10_7 : ∀ i : Fin 5, chunkPass chart511 10 (420+12*i.val) 12 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_10_8 : ∀ i : Fin 5, chunkPass chart511 10 (480+12*i.val) 12 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_10_9 : ∀ i : Fin 5, chunkPass chart511 10 (540+12*i.val) 12 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_10_10 : ∀ i : Fin 5, chunkPass chart511 10 (600+12*i.val) 12 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_10_11 : ∀ i : Fin 5, chunkPass chart511 10 (660+12*i.val) 12 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_10_12 : ∀ i : Fin 5, chunkPass chart511 10 (720+12*i.val) 12 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_10_13 : ∀ i : Fin 5, chunkPass chart511 10 (780+12*i.val) 12 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_10_14 : ∀ i : Fin 5, chunkPass chart511 10 (840+12*i.val) 12 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_10_15 : ∀ i : Fin 1, chunkPass chart511 10 (900+12*i.val) 12 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_10_16 : chunkPass chart511 10 912 1 = true := by decide +kernel

theorem verified511_10 : block chart511 10 0 913 = true :=
  (@block_merge chart511 10 0 480 433 (@block_merge chart511 10 0 240 240 (@block_merge chart511 10 0 120 120 (@block_merge chart511 10 0 60 60 (blocksByChunks chart511 10 0 12 5 checks511_10_0) (blocksByChunks chart511 10 60 12 5 checks511_10_1)) (@block_merge chart511 10 120 60 60 (blocksByChunks chart511 10 120 12 5 checks511_10_2) (blocksByChunks chart511 10 180 12 5 checks511_10_3))) (@block_merge chart511 10 240 120 120 (@block_merge chart511 10 240 60 60 (blocksByChunks chart511 10 240 12 5 checks511_10_4) (blocksByChunks chart511 10 300 12 5 checks511_10_5)) (@block_merge chart511 10 360 60 60 (blocksByChunks chart511 10 360 12 5 checks511_10_6) (blocksByChunks chart511 10 420 12 5 checks511_10_7)))) (@block_merge chart511 10 480 240 193 (@block_merge chart511 10 480 120 120 (@block_merge chart511 10 480 60 60 (blocksByChunks chart511 10 480 12 5 checks511_10_8) (blocksByChunks chart511 10 540 12 5 checks511_10_9)) (@block_merge chart511 10 600 60 60 (blocksByChunks chart511 10 600 12 5 checks511_10_10) (blocksByChunks chart511 10 660 12 5 checks511_10_11))) (@block_merge chart511 10 720 120 73 (@block_merge chart511 10 720 60 60 (blocksByChunks chart511 10 720 12 5 checks511_10_12) (blocksByChunks chart511 10 780 12 5 checks511_10_13)) (@block_merge chart511 10 840 60 13 (blocksByChunks chart511 10 840 12 5 checks511_10_14) (@block_merge chart511 10 900 12 1 (blocksByChunks chart511 10 900 12 1 checks511_10_15) (chunkPass_block checks511_10_16))))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_0 : ∀ i : Fin 5, chunkPass chart511 11 (0+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_1 : ∀ i : Fin 5, chunkPass chart511 11 (40+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_2 : ∀ i : Fin 5, chunkPass chart511 11 (80+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_3 : ∀ i : Fin 5, chunkPass chart511 11 (120+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_4 : ∀ i : Fin 5, chunkPass chart511 11 (160+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_5 : ∀ i : Fin 5, chunkPass chart511 11 (200+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_6 : ∀ i : Fin 5, chunkPass chart511 11 (240+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_7 : ∀ i : Fin 5, chunkPass chart511 11 (280+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_8 : ∀ i : Fin 5, chunkPass chart511 11 (320+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_9 : ∀ i : Fin 5, chunkPass chart511 11 (360+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_10 : ∀ i : Fin 5, chunkPass chart511 11 (400+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_11 : ∀ i : Fin 5, chunkPass chart511 11 (440+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_12 : ∀ i : Fin 5, chunkPass chart511 11 (480+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_13 : ∀ i : Fin 5, chunkPass chart511 11 (520+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_14 : ∀ i : Fin 5, chunkPass chart511 11 (560+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_15 : ∀ i : Fin 5, chunkPass chart511 11 (600+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_16 : ∀ i : Fin 5, chunkPass chart511 11 (640+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_17 : ∀ i : Fin 5, chunkPass chart511 11 (680+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_18 : ∀ i : Fin 5, chunkPass chart511 11 (720+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_19 : ∀ i : Fin 5, chunkPass chart511 11 (760+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_20 : ∀ i : Fin 5, chunkPass chart511 11 (800+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_21 : ∀ i : Fin 5, chunkPass chart511 11 (840+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_22 : ∀ i : Fin 5, chunkPass chart511 11 (880+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_23 : ∀ i : Fin 5, chunkPass chart511 11 (920+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_24 : ∀ i : Fin 5, chunkPass chart511 11 (960+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_25 : ∀ i : Fin 5, chunkPass chart511 11 (1000+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_26 : ∀ i : Fin 5, chunkPass chart511 11 (1040+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_27 : ∀ i : Fin 5, chunkPass chart511 11 (1080+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_28 : ∀ i : Fin 5, chunkPass chart511 11 (1120+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_29 : ∀ i : Fin 5, chunkPass chart511 11 (1160+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_30 : ∀ i : Fin 5, chunkPass chart511 11 (1200+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_31 : ∀ i : Fin 5, chunkPass chart511 11 (1240+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_32 : ∀ i : Fin 5, chunkPass chart511 11 (1280+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_33 : ∀ i : Fin 5, chunkPass chart511 11 (1320+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_34 : ∀ i : Fin 4, chunkPass chart511 11 (1360+8*i.val) 8 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_11_35 : chunkPass chart511 11 1392 3 = true := by decide +kernel

theorem verified511_11 : block chart511 11 0 1395 = true :=
  (@block_merge chart511 11 0 720 675 (@block_merge chart511 11 0 360 360 (@block_merge chart511 11 0 160 200 (@block_merge chart511 11 0 80 80 (@block_merge chart511 11 0 40 40 (blocksByChunks chart511 11 0 8 5 checks511_11_0) (blocksByChunks chart511 11 40 8 5 checks511_11_1)) (@block_merge chart511 11 80 40 40 (blocksByChunks chart511 11 80 8 5 checks511_11_2) (blocksByChunks chart511 11 120 8 5 checks511_11_3))) (@block_merge chart511 11 160 80 120 (@block_merge chart511 11 160 40 40 (blocksByChunks chart511 11 160 8 5 checks511_11_4) (blocksByChunks chart511 11 200 8 5 checks511_11_5)) (@block_merge chart511 11 240 40 80 (blocksByChunks chart511 11 240 8 5 checks511_11_6) (@block_merge chart511 11 280 40 40 (blocksByChunks chart511 11 280 8 5 checks511_11_7) (blocksByChunks chart511 11 320 8 5 checks511_11_8))))) (@block_merge chart511 11 360 160 200 (@block_merge chart511 11 360 80 80 (@block_merge chart511 11 360 40 40 (blocksByChunks chart511 11 360 8 5 checks511_11_9) (blocksByChunks chart511 11 400 8 5 checks511_11_10)) (@block_merge chart511 11 440 40 40 (blocksByChunks chart511 11 440 8 5 checks511_11_11) (blocksByChunks chart511 11 480 8 5 checks511_11_12))) (@block_merge chart511 11 520 80 120 (@block_merge chart511 11 520 40 40 (blocksByChunks chart511 11 520 8 5 checks511_11_13) (blocksByChunks chart511 11 560 8 5 checks511_11_14)) (@block_merge chart511 11 600 40 80 (blocksByChunks chart511 11 600 8 5 checks511_11_15) (@block_merge chart511 11 640 40 40 (blocksByChunks chart511 11 640 8 5 checks511_11_16) (blocksByChunks chart511 11 680 8 5 checks511_11_17)))))) (@block_merge chart511 11 720 360 315 (@block_merge chart511 11 720 160 200 (@block_merge chart511 11 720 80 80 (@block_merge chart511 11 720 40 40 (blocksByChunks chart511 11 720 8 5 checks511_11_18) (blocksByChunks chart511 11 760 8 5 checks511_11_19)) (@block_merge chart511 11 800 40 40 (blocksByChunks chart511 11 800 8 5 checks511_11_20) (blocksByChunks chart511 11 840 8 5 checks511_11_21))) (@block_merge chart511 11 880 80 120 (@block_merge chart511 11 880 40 40 (blocksByChunks chart511 11 880 8 5 checks511_11_22) (blocksByChunks chart511 11 920 8 5 checks511_11_23)) (@block_merge chart511 11 960 40 80 (blocksByChunks chart511 11 960 8 5 checks511_11_24) (@block_merge chart511 11 1000 40 40 (blocksByChunks chart511 11 1000 8 5 checks511_11_25) (blocksByChunks chart511 11 1040 8 5 checks511_11_26))))) (@block_merge chart511 11 1080 160 155 (@block_merge chart511 11 1080 80 80 (@block_merge chart511 11 1080 40 40 (blocksByChunks chart511 11 1080 8 5 checks511_11_27) (blocksByChunks chart511 11 1120 8 5 checks511_11_28)) (@block_merge chart511 11 1160 40 40 (blocksByChunks chart511 11 1160 8 5 checks511_11_29) (blocksByChunks chart511 11 1200 8 5 checks511_11_30))) (@block_merge chart511 11 1240 80 75 (@block_merge chart511 11 1240 40 40 (blocksByChunks chart511 11 1240 8 5 checks511_11_31) (blocksByChunks chart511 11 1280 8 5 checks511_11_32)) (@block_merge chart511 11 1320 40 35 (blocksByChunks chart511 11 1320 8 5 checks511_11_33) (@block_merge chart511 11 1360 32 3 (blocksByChunks chart511 11 1360 8 4 checks511_11_34) (chunkPass_block checks511_11_35)))))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_12_0 : ∀ i : Fin 5, chunkPass chart511 12 (0+4*i.val) 4 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_12_1 : ∀ i : Fin 5, chunkPass chart511 12 (20+4*i.val) 4 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_12_2 : ∀ i : Fin 5, chunkPass chart511 12 (40+4*i.val) 4 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_12_3 : ∀ i : Fin 5, chunkPass chart511 12 (60+4*i.val) 4 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_12_4 : ∀ i : Fin 5, chunkPass chart511 12 (80+4*i.val) 4 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_12_5 : ∀ i : Fin 5, chunkPass chart511 12 (100+4*i.val) 4 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_12_6 : ∀ i : Fin 5, chunkPass chart511 12 (120+4*i.val) 4 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_12_7 : ∀ i : Fin 5, chunkPass chart511 12 (140+4*i.val) 4 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_12_8 : ∀ i : Fin 5, chunkPass chart511 12 (160+4*i.val) 4 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_12_9 : ∀ i : Fin 5, chunkPass chart511 12 (180+4*i.val) 4 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_12_10 : ∀ i : Fin 5, chunkPass chart511 12 (200+4*i.val) 4 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_12_11 : ∀ i : Fin 5, chunkPass chart511 12 (220+4*i.val) 4 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_12_12 : ∀ i : Fin 5, chunkPass chart511 12 (240+4*i.val) 4 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_12_13 : ∀ i : Fin 3, chunkPass chart511 12 (260+4*i.val) 4 = true := by
  intro i
  fin_cases i <;> decide +kernel

theorem verified511_12 : block chart511 12 0 272 = true :=
  (@block_merge chart511 12 0 140 132 (@block_merge chart511 12 0 60 80 (@block_merge chart511 12 0 20 40 (blocksByChunks chart511 12 0 4 5 checks511_12_0) (@block_merge chart511 12 20 20 20 (blocksByChunks chart511 12 20 4 5 checks511_12_1) (blocksByChunks chart511 12 40 4 5 checks511_12_2))) (@block_merge chart511 12 60 40 40 (@block_merge chart511 12 60 20 20 (blocksByChunks chart511 12 60 4 5 checks511_12_3) (blocksByChunks chart511 12 80 4 5 checks511_12_4)) (@block_merge chart511 12 100 20 20 (blocksByChunks chart511 12 100 4 5 checks511_12_5) (blocksByChunks chart511 12 120 4 5 checks511_12_6)))) (@block_merge chart511 12 140 60 72 (@block_merge chart511 12 140 20 40 (blocksByChunks chart511 12 140 4 5 checks511_12_7) (@block_merge chart511 12 160 20 20 (blocksByChunks chart511 12 160 4 5 checks511_12_8) (blocksByChunks chart511 12 180 4 5 checks511_12_9))) (@block_merge chart511 12 200 40 32 (@block_merge chart511 12 200 20 20 (blocksByChunks chart511 12 200 4 5 checks511_12_10) (blocksByChunks chart511 12 220 4 5 checks511_12_11)) (@block_merge chart511 12 240 20 12 (blocksByChunks chart511 12 240 4 5 checks511_12_12) (blocksByChunks chart511 12 260 4 3 checks511_12_13)))))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_13_0 : ∀ i : Fin 5, chunkPass chart511 13 (0+3*i.val) 3 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_13_1 : ∀ i : Fin 2, chunkPass chart511 13 (15+3*i.val) 3 = true := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem checks511_13_2 : chunkPass chart511 13 21 1 = true := by decide +kernel

theorem verified511_13 : block chart511 13 0 22 = true :=
  (@block_merge chart511 13 0 15 7 (blocksByChunks chart511 13 0 3 5 checks511_13_0) (@block_merge chart511 13 15 6 1 (blocksByChunks chart511 13 15 3 2 checks511_13_1) (chunkPass_block checks511_13_2)))

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem chart511Root0 : nodeVerified chart511 14 0 = true := by
  apply ofContextPasses (by decide +kernel)
  change ∀ w : Fin 9, oneContextPass (contextOf chart511 14 0) w.val = true
  intro w
  fin_cases w <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem chart511Root1 : nodeVerified chart511 14 1 = true := by
  apply ofContextPasses (by decide +kernel)
  change ∀ w : Fin 10, oneContextPass (contextOf chart511 14 1) w.val = true
  intro w
  fin_cases w <;> decide +kernel

theorem verified511_14 : block chart511 14 0 2 = true := by
  simp only [block,Nat.reduceAdd,Bool.and_eq_true,chart511Root0,chart511Root1,true_and,and_true]

theorem verifiedChart511 : checkedTables chart511 14 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact verified511_8
  · exact verified511_9
  · exact verified511_10
  · exact verified511_11
  · exact verified511_12
  · exact verified511_13
  · exact verified511_14

theorem plainStart : indexedRoot chart511 14 0 inputs = true := by decide +kernel
theorem seededStart : indexedRoot chart511 14 1 (inputs++[or_seed]) = true := by decide +kernel

end PEqualNP.Outside.L_meta_1673

open PEqualNP.Outside.L_meta_1673

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_1673 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 1)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro C fan first computes
  by_contra! small
  have same : targetOf chart511 = graph := by decide +kernel
  have without := root_index_seed (g:=chart511) (top:=14) (k:=14)
    (before_sound known383 valid383) (beforeSeed_sound registered495 registered495Valid)
    geometry511 verifiedChart511 (Nat.le_refl 14) plainStart
  have withOr := root_index_seed (g:=chart511) (top:=14) (k:=14)
    (before_sound known383 valid383) (beforeSeed_sound registered495 registered495Valid)
    geometry511 verifiedChart511 (Nat.le_refl 14) seededStart
  rw [same] at without withOr
  obtain ⟨k,t,budget, h | h⟩ := or_initial_live C fan first computes (by omega)
  · exact without k t budget h
  · exact withOr k t budget h
