import PEqualNP.Defs

-- The live-wire framework and induced-subgraph lower bounds build on the checked
-- L-meta-1667 and L-meta-1920 proofs, including PressF10’s work in PR 4332 (Apache-2.0).
namespace PEqualNP.Outside.L_meta_1677
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
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
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
def vertex (m j : Nat) := if m.testBit j then (if m.testBit 9 && j == 4 then neg (inputs.getD 4 zero) else inputs.getD j zero) else zero
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

def supportPairs (baseRow mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,Fin.ofNat 512 baseRow,Fin.ofNat 512 (baseRow ^^^ (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  let base := if m.testBit 9 && m.testBit 4 then 16 else 0
  (selected m).map fun (i,a) =>
    let r := base ^^^ (1 <<< ((hints >>> (4*i)) &&& 15))
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ^^^ (1 <<< i)))

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
def colFree (m z o : Nat) := (m &&& 511) ^^^ ((m &&& 511) &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let baseRow := if m.testBit 9 && free.testBit 4 then 16 else 0
  let xs := supportPairs baseRow s
  let count := (xs.map Prod.fst).toFinset.card
  let drop := colFree free q 0
  let lz := if m.testBit 9 && drop.testBit 4 then drop &&& (511 ^^^ 16) else drop
  let lo := if m.testBit 9 && drop.testBit 4 then 16 else 0
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows lz lo) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let baseRow := if m.testBit 9 && free.testBit 4 then 16 else 0
  let xs := supportPairs baseRow s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) _ hh.1 p bank hr ha)
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
  let x := fun j => if m.testBit j then (if m.testBit 9 && j == 4 then ~~~(v 4) else v j) else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then (if m.testBit 9 && j.val == 4 then ~~~(v 4) else v j.val) else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · by_cases hf : (m.testBit 9 && j.val == 4) = true
    · have hj4 : j.val = 4 := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hf; exact hf.2
      simp only [vertex, hh, hf, ite_true, bit_neg, BitVec.getLsbD_not, i.isLt, decide_true, Bool.true_and]
      exact congrArg Bool.not (asRow_bit v i ⟨4, by decide⟩)
    · simpa [vertex, hh, hf] using asRow_bit v i j
  · simp [vertex, hh, bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then (if m.testBit 9 && j == 4 then ~~~(v 4) else v j) else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
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

abbrev ExtraCut := Nat → List Sig → Bool
abbrev ChildLinks := (Nat → List (List Sig)) × ExtraCut

def closeChild (pools : List BoundPool) (links : ChildLinks) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links.1 (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op) || links.2 k ws

theorem closeChild_sound {raw T pools} {links : ChildLinks} {k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links.1 tag → Impossible T k (List.toFinset xs))
    (cutValid : ∀ ws : List Sig, ws.Nodup → links.2 k ws = true → Impossible T k ws.toFinset)
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with (⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩) | cutProof
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok
  · exact cutValid _ nd cutProof

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

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × ChildLinks
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
theorem evalMove_sound {raw T r s ws pools} {links : ChildLinks} {cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links.1 tag → Impossible T (cap-1) (List.toFinset xs))
    (cv : ∀ words : List Sig, words.Nodup → links.2 (cap-1) words = true → Impossible T (cap-1) words.toFinset)
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
  exact closeChild_sound pv lv cv nd' test k t hk h


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

theorem node_sound {raw T r s ws pools} {links : ChildLinks} {cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links.1 tag → Impossible T (cap-1) (List.toFinset xs))
    (cv : ∀ words : List Sig, words.Nodup → links.2 (cap-1) words = true → Impossible T (cap-1) words.toFinset)
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
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv cv pro fresh (all_unary checks ha keep)
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
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv cv
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
  cut : ExtraCut := fun _ _ => false
  cut_sound : ∀ k (ws : List Sig), ws.Nodup → cut k ws = true → Impossible (chartGoal mask) k ws.toFinset := by
    intros
    contradiction

  recipes3095 : Option (Nat → Nat → Nat × Nat) := none
  rules3095 : Option (Nat → Nat → List (Nat × Nat)) := none

def wiresOf (g : Forest) :=
  rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
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
  let packet := match g.recipes3095 with
    | some reader => reader k i
    | none =>
      let recp := packedAt data (i*width) width
      (recp &&& ((1 <<< len)-1),recp >>> len)
  let ops := packet.1
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive packet.2 bank)

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
  let entries := match g.rules3095 with
    | some reader => reader k i
    | none => getPairs data cw depth nr st
  let rules := entries.filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls,g.cut) ws)

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
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (g.cut_sound _) (by simpa only [h0,if_false] using checked.2)
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
def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let entries := match g.rules3095 with
    | some reader => reader k i
    | none => getPairs data cw depth nr st
  let rules := entries.filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls,g.cut)


def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
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
def deadsamples : Array (Bits × Bits) := #[(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadautos : Array (List Nat) := #[[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]

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
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index,fun _ _ => false, by simp,none,none⟩
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
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index,fun _ _ => false, by simp,none,none⟩
def g47 : Forest := ⟨47,4,fun _ => (0,0),.leaf [],#[],fun _ => emptyPacking,fun _ _ => none,fun _ _ => false,by simp,none,none⟩
def g55 : Forest := ⟨55,4,fun _ => (0,0),.leaf [],#[],fun _ => emptyPacking,fun _ _ => none,fun _ _ => false,by simp,none,none⟩
def g63 : Forest := ⟨63,7,fun _ => (0,0),.leaf [],#[],fun _ => emptyPacking,fun _ _ => none,fun _ _ => false,by simp,none,none⟩
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
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index,fun _ _ => false, by simp,none,none⟩
def g119 : Forest := ⟨119,5,fun _ => (0,0),.leaf [],#[],fun _ => emptyPacking,fun _ _ => none,fun _ _ => false,by simp,none,none⟩
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
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index,fun _ _ => false, by simp,none,none⟩
def g127 : Forest := ⟨127,8,fun _ => (0,0),.leaf [],#[],fun _ => emptyPacking,fun _ _ => none,fun _ _ => false,by simp,none,none⟩
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
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index,fun _ _ => false, by simp,none,none⟩
def g251 : Forest := ⟨251,7,fun _ => (0,0),.leaf [],#[],fun _ => emptyPacking,fun _ _ => none,fun _ _ => false,by simp,none,none⟩
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
theorem s31_5_0 : block g31 5 0 1=true := by
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true := by
  decide +kernel
theorem bl31_5 : block g31 5 0 3 = true := (@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
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
theorem s189_6_0 : block g189 6 0 1=true := by
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true := by
  decide +kernel
theorem bl189_6 : block g189 6 0 3 = true := (@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
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
theorem s191_6_0 : block g191 6 0 1=true := by
  decide +kernel
theorem bl191_6 : block g191 6 0 1 = true := s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem s191_7_0 : block g191 7 0 13=true := by
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true := by
  decide +kernel
theorem bl191_7 : block g191 7 0 28 = true := (@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
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
theorem s191_9_0 : block g191 9 0 3=true := by
  decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true := by
  decide +kernel
theorem bl191_9 : block g191 9 0 12 = true := (@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
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

end PEqualNP.Outside.L_meta_1677

namespace PEqualNP.Outside.L_meta_1677.RankBase

-- The branch-group argument and circuit simplifier are adapted from L_meta_1549.
-- The simplifier tracks the number of non-NOT gates independently of length.

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def isNotGate (op : GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false


def nonNotCount (gs : List Gate) : ℕ :=
  gs.countP (fun g => !(isNotGate g.op))

end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g

theorem CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h

theorem CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk

theorem getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp


theorem split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩


end CircuitProof

namespace CircuitProof

open PEqualNP.CircuitLowerBounds

def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false

theorem vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩

theorem vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm

theorem vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h

end CircuitProof

namespace PetersenCutTrace

open PEqualNP.CircuitLowerBounds
open CircuitProof

def avoid {W : Type} (edge : W → W → Prop) (cut : W) (a b : W) : Prop :=
  edge a b ∧ a ≠ cut ∧ b ≠ cut

theorem difference_traces {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut : W) (x y : W → Bool)
    (order : ∀ a b, edge a b → rank a < rank b)
    (localStep : ∀ b, ¬ input b → x b ≠ y b → ∃ a, edge a b ∧ x a ≠ y a)
    (sameCut : x cut = y cut) {out : W} (different : x out ≠ y out) :
    ∃ a, input a ∧ x a ≠ y a ∧ Relation.ReflTransGen (avoid edge cut) a out := by
  classical
  have track : ∀ k b, rank b = k → x b ≠ y b →
      ∃ a, input a ∧ x a ≠ y a ∧ Relation.ReflTransGen (avoid edge cut) a b := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro b hb diff
      by_cases hInput : input b
      · exact ⟨b, hInput, diff, Relation.ReflTransGen.refl⟩
      · obtain ⟨p, hp, dp⟩ := localStep b hInput diff
        have earlier : rank p < k := (order p b hp).trans_eq hb
        obtain ⟨a, ha, da, path⟩ := ih (rank p) earlier p rfl dp
        have pOff : p ≠ cut := by rintro rfl; exact dp sameCut
        have bOff : b ≠ cut := by rintro rfl; exact diff sameCut
        exact ⟨a, ha, da, path.tail ⟨hp, pOff, bOff⟩⟩
  exact track (rank out) out rfl different

theorem cut_agreement {W : Type} (rank : W → Nat) (input : W → Prop)
    (edge : W → W → Prop) (cut out : W) (x y : W → Bool)
    (order : ∀ a b, edge a b → rank a < rank b)
    (localStep : ∀ b, ¬ input b → x b ≠ y b → ∃ a, edge a b ∧ x a ≠ y a)
    (sameCut : x cut = y cut)
    (blocked : ∀ a, input a → x a ≠ y a →
      ¬ Relation.ReflTransGen (avoid edge cut) a out) : x out = y out := by
  by_contra different
  obtain ⟨a, ha, da, reaches⟩ := difference_traces rank input edge cut x y
    order localStep sameCut different
  exact blocked a ha da reaches

theorem unary_factor {A : Type} (w f : A → Bool)
    (h : ∀ x y, w x = w y → f x = f y) :
    ∃ outer : Bool → Bool, ∀ x, outer (w x) = f x := by
  classical
  let outer (b : Bool) := if hb : ∃ a, w a = b then f (Classical.choose hb) else false
  refine ⟨outer, fun x => ?_⟩
  have hx : ∃ a, w a = w x := ⟨x, rfl⟩
  unfold outer
  rw [dite_eq_left hx]
  exact h _ _ (Classical.choose_spec hx)

def inputWire {n : Nat} (gs : List Gate) (v : Fin n) : Fin (n + gs.length) :=
  v.castLE (Nat.le_add_right n gs.length)

def readEdge {n : Nat} (gs : List Gate) (a b : Fin (n + gs.length)) : Prop :=
  ∃ (p : Nat) (g : Gate), gs[p]? = some g ∧ b.val = n + p ∧ a.val ∈ g.inputs

theorem read_order {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    {a b : Fin (n + gs.length)} (edge : readEdge gs a b) : a.val < b.val := by
  obtain ⟨p, g, hpg, hb, ha⟩ := edge
  rw [hb]
  exact (hcl p g hpg).lt _ ha

private theorem gate_difference {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (x y : Fin n → Bool) (b : Fin (n + gs.length)) (notInput : ¬ b.val < n)
    (diff : vl gs x b.val ≠ vl gs y b.val) :
    ∃ a : Fin (n + gs.length), readEdge gs a b ∧ vl gs x a.val ≠ vl gs y a.val := by
  let p := b.val - n
  have hb : b.val = n + p := by dsimp [p]; omega
  have hp : p < gs.length := by have := b.isLt; omega
  let g := gs[p]
  have hpg : gs[p]? = some g := List.getElem?_eq_getElem hp
  have differingRead : ∃ a ∈ g.inputs, vl gs x a ≠ vl gs y a := by
    classical
    by_contra none
    apply diff
    rw [hb]
    exact vl_congr gs hcl x y p g hpg (fun a ha => by
      by_contra da
      exact none ⟨a, ha, da⟩)
  obtain ⟨a, ha, da⟩ := differingRead
  have ha' := (hcl p g hpg).lt a ha
  refine ⟨⟨a, by have := b.isLt; omega⟩, ⟨p, g, hpg, hb, ha⟩, da⟩

theorem circuit_cut_agreement {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (x y : Fin n → Bool)
    (sameCut : vl gs x cut.val = vl gs y cut.val)
    (blocked : ∀ i : Fin n, x i ≠ y i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    vl gs x out.val = vl gs y out.val := by
  apply cut_agreement Fin.val (fun v => v.val < n) (readEdge gs) cut out
    (fun v => vl gs x v.val) (fun v => vl gs y v.val)
  · exact fun _ _ e => read_order hcl e
  · exact gate_difference hcl x y
  · exact sameCut
  · intro a ha diff
    let i : Fin n := ⟨a.val, ha⟩
    have sameWire : inputWire gs i = a := Fin.ext rfl
    have di : x i ≠ y i := by
      rw [vl_input gs x a.val ha, vl_input gs y a.val ha] at diff
      exact diff
    rw [← sameWire]
    exact blocked i di

theorem circuit_cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (blocked : ∀ i : Fin n, group i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    ∃ outer : Bool → Bool, ∀ x : Fin n → Bool, (∀ i, ¬ group i → x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val := by
  let Fiber := {x : Fin n → Bool // ∀ i, ¬ group i → x i = base i}
  obtain ⟨outer, ho⟩ := unary_factor
    (fun x : Fiber => vl gs x.val cut.val) (fun x : Fiber => vl gs x.val out.val) (by
      intro x y sameCut
      apply circuit_cut_agreement hcl cut out x.val y.val sameCut
      intro i diff
      apply blocked i
      by_contra notGroup
      exact diff ((x.property i notGroup).trans (y.property i notGroup).symm))
  exact ⟨outer, fun x agrees => ho ⟨x, agrees⟩⟩

end PetersenCutTrace

namespace CircuitProof.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitProof

def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs

end CircuitProof.Readers

namespace PetersenCutTrace

open PEqualNP.CircuitLowerBounds
open CircuitProof CircuitProof.Readers

def predecessors {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) : List (Fin (n + gs.length)) :=
  if gate : n ≤ b.val then
    let slot := b.val - n
    have hs : slot < gs.length := by have := b.isLt; omega
    let g := gs[slot]'hs
    g.inputs.attach.map fun a => ⟨a.val, by
      have atSlot : gs[slot]? = some g := List.getElem?_eq_getElem hs
      have before := (clean slot g atSlot).lt a.val a.property
      omega⟩
  else []

theorem predecessors_values {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (internal : n ≤ b.val) :
    (predecessors clean b).map Fin.val =
      (gs[b.val - n]'(by have := b.isLt; omega)).inputs := by
  simp [predecessors, internal, List.map_map, Function.comp_def]

theorem predecessors_nil_input {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) (primary : b.val < n) : predecessors clean b = [] := by
  simp [predecessors, show ¬ n ≤ b.val by omega]

theorem predecessors_val_gate {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (b : Fin (n + gs.length)) {p : Nat} {g : Gate} (atSlot : gs[p]? = some g) (bWire : b.val = n + p) :
    (predecessors clean b).map Fin.val = g.inputs := by
  have isGate : n ≤ b.val := by omega
  have which : b.val - n = p := by omega
  have located := (List.getElem?_eq_some_iff.mp atSlot).2
  simpa [which, located] using predecessors_values clean b isGate

theorem predecessors_mem {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (a b : Fin (n + gs.length)) : a ∈ predecessors clean b ↔ readEdge gs a b := by
  by_cases internal : n ≤ b.val
  · let slot := b.val - n
    have hs : slot < gs.length := by have := b.isLt; dsimp [slot]; omega
    let g := gs[slot]'hs
    have wire : b.val = n + slot := by dsimp [slot]; omega
    have atSlot : gs[slot]? = some g := List.getElem?_eq_getElem hs
    have valList : (predecessors clean b).map Fin.val = g.inputs :=
      predecessors_values clean b internal
    constructor
    · intro mem
      refine ⟨slot, g, atSlot, wire, ?_⟩
      rw [← valList]
      exact List.mem_map.mpr ⟨a, mem, rfl⟩
    · rintro ⟨q, h, atQ, wireQ, inside⟩
      have same : q = slot := by omega
      subst q
      have gateSame : h = g := Option.some.inj (atQ.symm.trans atSlot)
      subst h
      rw [← valList] at inside
      obtain ⟨a', mem, equal⟩ := List.mem_map.mp inside
      exact (Fin.ext equal : a' = a) ▸ mem
  · have empty : predecessors clean b = [] := by simp [predecessors, internal]
    rw [empty]
    constructor
    · simp
    · rintro ⟨slot, g, _, wire, _⟩
      omega

end PetersenCutTrace

namespace PetersenScratch

open PEqualNP.MetaComplexity

def occurrences {n : ℕ} (i : Fin n) : DMFormula n → ℕ
  | .lit k _ => if k = i then 1 else 0
  | .and p q => occurrences i p + occurrences i q
  | .or p q => occurrences i p + occurrences i q

def hasPair {n : ℕ} (i j : Fin n) (p : DMFormula n) : Prop :=
  0 < occurrences i p ∨ 0 < occurrences j p

def pairInput {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (a b : Bool) (k : Fin n) : Bool :=
  if k = i then a else if k = j then b else base k

def pairValue {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n) :
    Bool → Bool → Bool :=
  fun a b => p.eval (pairInput i j base a b)

def binOp (conj : Bool) (a b : Bool) : Bool :=
  if conj then a && b else a || b

noncomputable def combine {n : ℕ} (conj : Bool) (i j : Fin n) (p q : DMFormula n)
    (P Q : Bool → Bool → Bool) : Bool → Bool → Bool := by
  classical
  exact if hasPair i j p then
    if hasPair i j q then fun a b => binOp conj (P a b) (Q a b) else P
    else Q

noncomputable def pairKernel {n : ℕ} (i j : Fin n) : DMFormula n → Bool → Bool → Bool
  | .lit k sign => fun a b =>
    let bit := if k = i then a else if k = j then b else false
    if sign then bit else !bit
  | .and p q => combine true i j p q (pairKernel i j p) (pairKernel i j q)
  | .or p q => combine false i j p q (pairKernel i j p) (pairKernel i j q)

private theorem eval_agree {n : ℕ} (p : DMFormula n) {x y : Fin n → Bool}
    (h : ∀ k, 0 < occurrences k p → x k = y k) : p.eval x = p.eval y := by
  induction p with
  | lit k s =>
    have e := h k (by simp [occurrences])
    simp [DMFormula.eval, e]
  | and p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [occurrences]; omega)),
      ihq (fun k hk => h k (by simp only [occurrences]; omega))]
  | or p q ihp ihq =>
    simp only [DMFormula.eval]
    rw [ihp (fun k hk => h k (by simp only [occurrences]; omega)),
      ihq (fun k hk => h k (by simp only [occurrences]; omega))]

private theorem absent_left {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : occurrences i p = 0) (a a' b : Bool) :
    pairValue i j base p a b = pairValue i j base p a' b := by
  apply eval_agree
  intro k hk
  have ne : k ≠ i := by rintro rfl; omega
  simp [pairInput, ne]

private theorem absent_right {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : occurrences j p = 0) (a b b' : Bool) :
    pairValue i j base p a b = pairValue i j base p a b' := by
  apply eval_agree
  intro k hk
  have ne : k ≠ j := by rintro rfl; omega
  simp [pairInput, ne]

def changes (f : Bool → Bool → Bool) : Prop :=
  ∃ b, f false b ≠ f true b

private theorem changes_left {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b => op (P a b) (Q a b))
    (hQ : ∀ b, Q false b = Q true b) : changes P := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun hp => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hp, hQ])⟩

private theorem changes_right {op : Bool → Bool → Bool} {P Q : Bool → Bool → Bool}
    (h : changes fun a b => op (P a b) (Q a b))
    (hP : ∀ b, P false b = P true b) : changes Q := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun hq => hb (by
    change op (P false b) (Q false b) = op (P true b) (Q true b)
    rw [hq, hP])⟩

private theorem constant_pair {n : ℕ} {i j : Fin n} {base : Fin n → Bool} {p : DMFormula n}
    (h : ¬ hasPair i j p) (a b : Bool) :
    pairValue i j base p a b = pairValue i j base p false false := by
  have hi : occurrences i p = 0 := by
    by_contra e
    exact h (Or.inl (by omega))
  have hj : occurrences j p = 0 := by
    by_contra e
    exact h (Or.inr (by omega))
  exact (absent_left hi a false b).trans (absent_right hj false b false)

private theorem neutral_right (conj c : Bool) (P : Bool → Bool → Bool)
    (h : ∃ a b a' b', binOp conj (P a b) c ≠ binOp conj (P a' b') c) :
    ∀ a b, binOp conj (P a b) c = P a b := by
  cases conj <;> cases c <;> simp [binOp] at h ⊢

private theorem bin_comm (conj a b : Bool) : binOp conj a b = binOp conj b a := by
  cases conj <;> cases a <;> cases b <;> rfl

private theorem combine_stable {n : ℕ} (i j : Fin n) (base : Fin n → Bool)
    (conj : Bool) (p q : DMFormula n)
    (hi : occurrences i p + occurrences i q ≤ 1)
    (hj : occurrences j p + occurrences j q ≤ 1)
    (present : hasPair i j p ∨ hasPair i j q)
    (dep_i : 0 < occurrences i p + occurrences i q →
      changes fun a b => binOp conj (pairValue i j base p a b) (pairValue i j base q a b))
    (dep_j : 0 < occurrences j p + occurrences j q →
      changes fun b a => binOp conj (pairValue i j base p a b) (pairValue i j base q a b))
    (ihp : occurrences i p ≤ 1 → occurrences j p ≤ 1 → hasPair i j p →
      (0 < occurrences i p → changes (pairValue i j base p)) →
      (0 < occurrences j p → changes fun b a => pairValue i j base p a b) →
      ∀ a b, pairValue i j base p a b = pairKernel i j p a b)
    (ihq : occurrences i q ≤ 1 → occurrences j q ≤ 1 → hasPair i j q →
      (0 < occurrences i q → changes (pairValue i j base q)) →
      (0 < occurrences j q → changes fun b a => pairValue i j base q a b) →
      ∀ a b, pairValue i j base q a b = pairKernel i j q a b)
    (a b : Bool) :
    binOp conj (pairValue i j base p a b) (pairValue i j base q a b) =
      combine conj i j p q (pairKernel i j p) (pairKernel i j q) a b := by
  classical
  have pl : hasPair i j p → ∀ a b, pairValue i j base p a b = pairKernel i j p a b := by
    intro hp
    apply ihp (by omega) (by omega) hp
    · intro h
      exact changes_left (dep_i (by omega)) (fun b => absent_left (by omega) false true b)
    · intro h
      exact changes_left (dep_j (by omega)) (fun a => absent_right (by omega) a false true)
  have ql : hasPair i j q → ∀ a b, pairValue i j base q a b = pairKernel i j q a b := by
    intro hq
    apply ihq (by omega) (by omega) hq
    · intro h
      exact changes_right (dep_i (by omega)) (fun b => absent_left (by omega) false true b)
    · intro h
      exact changes_right (dep_j (by omega)) (fun a => absent_right (by omega) a false true)
  have nonconst : ∃ a b a' b',
      binOp conj (pairValue i j base p a b) (pairValue i j base q a b) ≠
        binOp conj (pairValue i j base p a' b') (pairValue i j base q a' b') := by
    unfold hasPair at present
    rcases present with (h | h) | (h | h)
    · obtain ⟨b, h⟩ := dep_i (by omega)
      exact ⟨false, b, true, b, h⟩
    · obtain ⟨a, h⟩ := dep_j (by omega)
      exact ⟨a, false, a, true, h⟩
    · obtain ⟨b, h⟩ := dep_i (by omega)
      exact ⟨false, b, true, b, h⟩
    · obtain ⟨a, h⟩ := dep_j (by omega)
      exact ⟨a, false, a, true, h⟩
  by_cases hp : hasPair i j p
  · by_cases hq : hasPair i j q
    · simp [combine, hp, hq, pl hp, ql hq]
    · rw [constant_pair hq a b]
      have hn := nonconst
      simp_rw [constant_pair hq] at hn
      rw [neutral_right conj _ _ hn a b, pl hp]
      simp [combine, hp, hq]
  · have hq := present.resolve_left hp
    rw [constant_pair hp a b, bin_comm]
    have hn := nonconst
    simp_rw [constant_pair hp, bin_comm conj (pairValue i j base p false false)] at hn
    rw [neutral_right conj _ _ hn a b, ql hq]
    simp [combine, hp]

private theorem stable_pair {n : ℕ} (i j : Fin n) (base : Fin n → Bool) (p : DMFormula n)
    (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1) (present : hasPair i j p)
    (dep_i : 0 < occurrences i p → changes (pairValue i j base p))
    (dep_j : 0 < occurrences j p → changes fun b a => pairValue i j base p a b) :
    ∀ a b, pairValue i j base p a b = pairKernel i j p a b := by
  induction p with
  | lit k s =>
    intro a b
    by_cases hki : k = i
    · simp [pairValue, pairKernel, DMFormula.eval, pairInput, hki]
    · have hkj : k = j := by
        by_contra h
        simp [hasPair, occurrences, hki, h] at present
      simp [pairValue, pairKernel, DMFormula.eval, pairInput, hkj]
  | and p q ihp ihq =>
    have present' : hasPair i j p ∨ hasPair i j q := by
      unfold hasPair at *
      simp only [occurrences] at present
      omega
    exact combine_stable i j base true p q hi hj present' dep_i dep_j ihp ihq
  | or p q ihp ihq =>
    have present' : hasPair i j p ∨ hasPair i j q := by
      unfold hasPair at *
      simp only [occurrences] at present
      omega
    exact combine_stable i j base false p q hi hj present' dep_i dep_j ihp ihq

theorem fixed_pair_invariant {n : ℕ} (i j : Fin n) (p : DMFormula n)
    (hi : occurrences i p ≤ 1) (hj : occurrences j p ≤ 1)
    (baseA baseO : Fin n → Bool) (outerA outerO : Bool → Bool)
    (hA : ∀ a b, outerA (pairValue i j baseA p a b) = (a && b))
    (hO : ∀ a b, outerO (pairValue i j baseO p a b) = (a || b)) : False := by
  have depAi : changes (pairValue i j baseA p) := by
    refine ⟨true, fun h => ?_⟩
    have e := congrArg outerA h
    rw [hA, hA] at e
    cases e
  have depAj : changes fun b a => pairValue i j baseA p a b := by
    refine ⟨true, fun h => ?_⟩
    have e := congrArg outerA h
    rw [hA, hA] at e
    cases e
  have depOi : changes (pairValue i j baseO p) := by
    refine ⟨false, fun h => ?_⟩
    have e := congrArg outerO h
    rw [hO, hO] at e
    cases e
  have depOj : changes fun b a => pairValue i j baseO p a b := by
    refine ⟨false, fun h => ?_⟩
    have e := congrArg outerO h
    rw [hO, hO] at e
    cases e
  have present : hasPair i j p := by
    left
    by_contra! h
    obtain ⟨b, hb⟩ := depAi
    exact hb (absent_left (by omega) false true b)
  have stableA := stable_pair i j baseA p hi hj present (fun _ => depAi) (fun _ => depAj)
  have stableO := stable_pair i j baseO p hi hj present (fun _ => depOi) (fun _ => depOj)
  simp_rw [stableA] at hA
  simp_rw [stableO] at hO
  have ne : pairKernel i j p false false ≠ pairKernel i j p false true := by
    intro e
    have f := congrArg outerO e
    rw [hO, hO] at f
    cases f
  have zeros := hA false false
  have other := hA false true
  have one := hA true true
  cases hk : pairKernel i j p false false <;>
    cases hl : pairKernel i j p false true <;>
    cases hm : pairKernel i j p true true <;>
    simp_all

end PetersenScratch

namespace PetersenCutFormula

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open CircuitProof
open PetersenScratch

def negFormula {n : Nat} : DMFormula n → DMFormula n
  | .lit i sign => .lit i (!sign)
  | .and a b => .or (negFormula a) (negFormula b)
  | .or a b => .and (negFormula a) (negFormula b)

theorem negFormula_eval {n : Nat} (p : DMFormula n) (x : Fin n → Bool) :
    (negFormula p).eval x = !(p.eval x) := by
  induction p with
  | lit i s =>
    cases s <;> cases e : x i <;> simp [negFormula, DMFormula.eval, e]
  | and a b iha ihb =>
    simp only [negFormula, DMFormula.eval, iha, ihb]
    cases a.eval x <;> cases b.eval x <;> rfl
  | or a b iha ihb =>
    simp only [negFormula, DMFormula.eval, iha, ihb]
    cases a.eval x <;> cases b.eval x <;> rfl

theorem negFormula_occurrences {n : Nat} (i : Fin n) (p : DMFormula n) :
    occurrences i (negFormula p) = occurrences i p := by
  induction p with
  | lit i s => rfl
  | and a b iha ihb => simp [negFormula, occurrences, iha, ihb]
  | or a b iha ihb => simp [negFormula, occurrences, iha, ihb]

def wireFormula {n : Nat} (fallback : Fin n) (gs : List Gate) (w : Nat) : DMFormula n :=
  if hw : w < n then
    .lit ⟨w, hw⟩ true
  else
    match gs[w - n]? with
    | none => .lit fallback true
    | some g =>
      match g.op, g.inputs with
      | .not, [a] =>
        if _ha : a < w then negFormula (wireFormula fallback gs a) else .lit fallback true
      | .and, [a, b] =>
        if _ha : a < w then
          if _hb : b < w then .and (wireFormula fallback gs a) (wireFormula fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | .or, [a, b] =>
        if _ha : a < w then
          if _hb : b < w then .or (wireFormula fallback gs a) (wireFormula fallback gs b)
          else .lit fallback true
        else .lit fallback true
      | _, _ => .lit fallback true
termination_by w
decreasing_by all_goals assumption

theorem wireFormula_input {n : Nat} (fallback : Fin n) (gs : List Gate) (i : Fin n) :
    wireFormula fallback gs i.val = .lit i true := by
  rw [wireFormula]
  simp [i.isLt]

private theorem wireFormula_not {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .not)
    (inputs : g.inputs = [a]) (ha : a < n + p) :
    wireFormula fallback gs (n + p) = negFormula (wireFormula fallback gs a) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha]

private theorem wireFormula_and {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .and)
    (inputs : g.inputs = [a, b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .and (wireFormula fallback gs a) (wireFormula fallback gs b) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha, hb]

private theorem wireFormula_or {n : Nat} (fallback : Fin n) {gs : List Gate}
    {p a b : Nat} {g : Gate} (hg : gs[p]? = some g) (op : g.op = .or)
    (inputs : g.inputs = [a, b]) (ha : a < n + p) (hb : b < n + p) :
    wireFormula fallback gs (n + p) = .or (wireFormula fallback gs a) (wireFormula fallback gs b) := by
  have hn : ¬ n + p < n := by omega
  have hp : n + p - n = p := by omega
  conv_lhs => rw [wireFormula]
  simp [hn, hp, hg, op, inputs, ha, hb]

theorem wireFormula_eval {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (x : Fin n → Bool) (w : Nat) (hw : w < n + gs.length) :
    (wireFormula fallback gs w).eval x = vl gs x w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hi : w < n
    · rw [wireFormula_input fallback gs ⟨w, hi⟩, vl_input gs x w hi]
      rfl
    · obtain ⟨p, rfl⟩ : ∃ p, w = n + p := ⟨w - n, by omega⟩
      have hp : p < gs.length := by omega
      let g := gs[p]
      have hg : gs[p]? = some g := List.getElem?_eq_getElem hp
      rcases hcl p g hg with ⟨op, a, ha, inputs⟩ | ⟨op | op, a, b, ha, hb, inputs⟩
      · rw [wireFormula_not fallback hg op inputs ha, negFormula_eval, ih a ha (by omega),
          vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]
      · rw [wireFormula_and fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega), ih b hb (by omega), vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]
      · rw [wireFormula_or fallback hg op inputs ha hb]
        simp only [DMFormula.eval]
        rw [ih a ha (by omega), ih b hb (by omega), vl_gate gs hcl x p g hg]
        simp [op, inputs, GateOp.eval]

theorem wireFormula_count_input {n : Nat} (fallback : Fin n) (gs : List Gate) (chosen i : Fin n) :
    occurrences chosen (wireFormula fallback gs i.val) = if i = chosen then 1 else 0 := by
  rw [wireFormula_input]
  rfl

theorem wireFormula_count_gate {n : Nat} (fallback : Fin n) {gs : List Gate} (hcl : CleanL n gs)
    (chosen : Fin n) {p : Nat} {g : Gate} (hg : gs[p]? = some g) :
    occurrences chosen (wireFormula fallback gs (n + p)) =
      (g.inputs.map fun a => occurrences chosen (wireFormula fallback gs a)).sum := by
  rcases hcl p g hg with ⟨op, a, ha, inputs⟩ | ⟨op | op, a, b, ha, hb, inputs⟩
  · simp [wireFormula_not fallback hg op inputs ha, inputs, negFormula_occurrences]
  · simp [wireFormula_and fallback hg op inputs ha hb, inputs, occurrences]
  · simp [wireFormula_or fallback hg op inputs ha hb, inputs, occurrences]

theorem wireFormula_count_gate_fin {n : Nat} (fallback chosen : Fin n) {gs : List Gate}
    (hcl : CleanL n gs) {p : Nat} {g : Gate} (hg : gs[p]? = some g)
    {b : Fin (n + gs.length)} (hb : b.val = n + p)
    (parents : List (Fin (n + gs.length))) (parentsVal : parents.map Fin.val = g.inputs) :
    occurrences chosen (wireFormula fallback gs b.val) =
      (parents.map fun a => occurrences chosen (wireFormula fallback gs a.val)).sum := by
  rw [hb, wireFormula_count_gate fallback hcl chosen hg, ← parentsVal, List.map_map]
  rfl

end PetersenCutFormula

namespace PetersenCutIndependent

open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutFormula PetersenCutTrace PetersenScratch

theorem wireFormula_count_input_fin {n : Nat} {gs : List Gate} (fallback chosen : Fin n)
    (a : Fin (n + gs.length)) (ha : a.val < n) :
    occurrences chosen (wireFormula fallback gs a.val) =
      if a = inputWire gs chosen then 1 else 0 := by
  let i : Fin n := ⟨a.val, ha⟩
  have e : i = chosen ↔ a = inputWire gs chosen := by
    constructor
    · intro h
      exact Fin.ext (congrArg (fun k : Fin n => k.val) h)
    · intro h
      exact Fin.ext (congrArg (fun k : Fin (n + gs.length) => k.val) h)
  change occurrences chosen (wireFormula fallback gs i.val) = _
  simp only [wireFormula_count_input, e]

theorem cut_factors {n : Nat} {gs : List Gate} (hcl : CleanL n gs)
    (cut out : Fin (n + gs.length)) (group : Fin n → Prop) (base : Fin n → Bool)
    (controlled : cut = out ∨ ∀ i : Fin n, group i →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs i) out) :
    ∃ outer : Bool → Bool, ∀ x : Fin n → Bool, (∀ i, ¬ group i → x i = base i) →
      outer (vl gs x cut.val) = vl gs x out.val := by
  rcases controlled with rfl | blocked
  · exact ⟨id, fun _ _ => rfl⟩
  · exact circuit_cut_factors hcl cut out group base blocked

end PetersenCutIndependent

namespace FirstBranchRoute

open Relation

variable {m : Nat} (reads : Fin m → Fin m → Prop) (output : Fin m)

def Branches (v : Fin m) : Prop := ∃ a b, reads v a ∧ reads v b ∧ a ≠ b

def Terminal (v : Fin m) : Prop := v = output ∨ Branches reads v

def Follow (v w : Fin m) : Prop := reads v w ∧ ¬ Terminal reads output v

lemma follow_unique {v a b : Fin m} (first : Follow reads output v a) (next : Follow reads output v b) :
    a = b := by
  by_contra separate
  exact first.2 (Or.inr ⟨a, b, first.1, next.1, separate⟩)

variable (forward : ∀ {v w : Fin m}, reads v w → v < w)
variable (live : ∀ v : Fin m, v ≠ output → ∃ w, reads v w)

include forward live in
theorem exists_boundary (v : Fin m) :
    ∃ root : Fin m, Terminal reads output root ∧ ReflTransGen (Follow reads output) v root := by
  let distance (w : Fin m) := m - w.val
  induction v using (measure distance).wf.induction with
  | h v ih =>
    by_cases terminal : Terminal reads output v
    · exact ⟨v, terminal, ReflTransGen.refl⟩
    obtain ⟨next, edge⟩ := live v (fun e => terminal (Or.inl e))
    have increase := forward edge
    have closer : distance next < distance v := by
      dsimp [distance]
      have bounds := next.isLt
      change v.val < next.val at increase
      omega
    obtain ⟨root, stopped, route⟩ := ih next closer
    exact ⟨root, stopped, route.head ⟨edge, terminal⟩⟩

include forward in
theorem boundary_unique {v a b : Fin m} (terminalA : Terminal reads output a)
    (terminalB : Terminal reads output b) (routeA : ReflTransGen (Follow reads output) v a)
    (routeB : ReflTransGen (Follow reads output) v b) : a = b := by
  let distance (w : Fin m) := m - w.val
  induction v using (measure distance).wf.induction generalizing a b with
  | h v ih =>
    rcases routeA.cases_head with h | ⟨next, edge, tailA⟩
    · subst a
      rcases routeB.cases_head with h | ⟨_, edgeB, _⟩
      · exact h
      · exact (edgeB.2 terminalA).elim
    · rcases routeB.cases_head with h | ⟨nextB, edgeB, tailB⟩
      · subst b
        exact (edge.2 terminalB).elim
      have equal := follow_unique reads output edge edgeB
      subst nextB
      have increase := forward edge.1
      have closer : distance next < distance v := by
        dsimp [distance]
        have bounds := next.isLt
        change v.val < next.val at increase
        omega
      exact ih next closer terminalA terminalB tailA tailB

noncomputable def first (v : Fin m) : Fin m :=
  Classical.choose (exists_boundary reads output forward live v)

theorem first_stops (v : Fin m) : Terminal reads output (first reads output forward live v) :=
  (Classical.choose_spec (exists_boundary reads output forward live v)).1

theorem first_path (v : Fin m) : ReflTransGen (Follow reads output) v (first reads output forward live v) :=
  (Classical.choose_spec (exists_boundary reads output forward live v)).2

theorem first_of_terminal {v : Fin m} (stopped : Terminal reads output v) :
    first reads output forward live v = v :=
  boundary_unique reads output forward (first_stops reads output forward live v) stopped
    (first_path reads output forward live v) ReflTransGen.refl

theorem first_of_follows {v w : Fin m} (step : Follow reads output v w) :
    first reads output forward live v = first reads output forward live w :=
  boundary_unique reads output forward (first_stops reads output forward live v)
    (first_stops reads output forward live w) (first_path reads output forward live v)
    ((first_path reads output forward live w).head step)

include forward in
theorem path_forward {v w : Fin m} (route : ReflTransGen reads v w) : v ≤ w := by
  induction route with
  | refl => exact le_rfl
  | tail _ edge ih => exact le_trans ih (le_of_lt (forward edge))

lemma follows_is_read_path {v w : Fin m} (route : ReflTransGen (Follow reads output) v w) :
    ReflTransGen reads v w := by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1

theorem first_forward (v : Fin m) : v ≤ first reads output forward live v :=
  path_forward reads forward (follows_is_read_path reads output (first_path reads output forward live v))

theorem read_before {v w : Fin m} (route : ReflTransGen reads v w)
    (before : w ≤ first reads output forward live v) :
    ReflTransGen (Follow reads output) v w ∧ first reads output forward live w = first reads output forward live v := by
  induction route with
  | refl => exact ⟨ReflTransGen.refl, rfl⟩
  | tail _ edge ih =>
    have predecessorBefore := lt_of_lt_of_le (forward edge) before
    obtain ⟨tracked, label⟩ := ih (le_of_lt predecessorBefore)
    have step : Follow reads output _ _ := ⟨edge, fun stopped => by
      have self := first_of_terminal reads output forward live stopped
      rw [self] at label
      exact (ne_of_lt predecessorBefore) label⟩
    exact ⟨tracked.tail step, (first_of_follows reads output forward live step).symm.trans label⟩

theorem ancestor_first_le {v w : Fin m} (route : ReflTransGen reads v w)
    (stopped : Terminal reads output w) : first reads output forward live v ≤ w := by
  by_contra tooLate
  have earlier := lt_of_not_ge tooLate
  have same := (read_before reads output forward live route (le_of_lt earlier)).2
  rw [first_of_terminal reads output forward live stopped] at same
  exact (ne_of_lt earlier) same

theorem edge_before {v a b : Fin m} (route : ReflTransGen reads v a) (edge : reads a b)
    (bound : b ≤ first reads output forward live v) : Follow reads output a b := by
  have earlier := lt_of_lt_of_le (forward edge) bound
  have same := (read_before reads output forward live route (le_of_lt earlier)).2
  refine ⟨edge, fun stopped => ?_⟩
  rw [first_of_terminal reads output forward live stopped] at same
  exact (ne_of_lt earlier) same

def Avoid (cut v w : Fin m) : Prop := reads v w ∧ v ≠ cut

lemma avoiding_is_read_path (cut : Fin m) {v w : Fin m} (route : ReflTransGen (Avoid reads cut) v w) :
    ReflTransGen reads v w := by
  induction route with
  | refl => exact ReflTransGen.refl
  | tail _ edge ih => exact ih.tail edge.1

theorem avoiding_stays_before {v w : Fin m}
    (route : ReflTransGen (Avoid reads (first reads output forward live v)) v w) :
    w ≤ first reads output forward live v := by
  induction route with
  | refl => exact first_forward reads output forward live v
  | tail prior edge ih =>
    have label := (read_before reads output forward live (avoiding_is_read_path reads _ prior) ih).2
    have earlier := lt_of_le_of_ne ih edge.2
    have following : Follow reads output _ _ := ⟨edge.1, fun terminal => by
      rw [first_of_terminal reads output forward live terminal] at label
      exact (ne_of_lt earlier) label⟩
    have same := (first_of_follows reads output forward live following).symm.trans label
    rw [← same]
    exact first_forward reads output forward live _

theorem no_avoiding_after {v w : Fin m} (after : first reads output forward live v < w) :
    ¬ ReflTransGen (Avoid reads (first reads output forward live v)) v w :=
  fun route => (not_lt_of_ge (avoiding_stays_before reads output forward live route)) after

include forward in
theorem unique_follow_predecessor {source a b goal : Fin m}
    (routeA : ReflTransGen (Follow reads output) source a) (edgeA : Follow reads output a goal)
    (routeB : ReflTransGen (Follow reads output) source b) (edgeB : Follow reads output b goal) : a = b := by
  let distance (w : Fin m) := m - w.val
  induction source using (measure distance).wf.induction generalizing a b with
  | h source ih =>
    rcases routeA.cases_head with aHere | ⟨nextA, stepA, laterA⟩
    · subst a
      rcases routeB.cases_head with bHere | ⟨next, stepB, later⟩
      · exact bHere
      have equal : next = goal := follow_unique reads output stepB edgeA
      subst next
      have increasing := path_forward reads forward (follows_is_read_path reads output later)
      exact (not_lt_of_ge increasing (forward edgeB.1)).elim
    · rcases routeB.cases_head with bHere | ⟨nextB, stepB, laterB⟩
      · subst b
        have equal : nextA = goal := follow_unique reads output stepA edgeB
        subst nextA
        have increasing := path_forward reads forward (follows_is_read_path reads output laterA)
        exact (not_lt_of_ge increasing (forward edgeA.1)).elim
      have equal := follow_unique reads output stepA stepB
      subst nextB
      have increase := forward stepA.1
      have closer : distance nextA < distance source := by
        dsimp [distance]
        have bounds := nextA.isLt
        change source.val < nextA.val at increase
        omega
      exact ih nextA closer laterA edgeA laterB edgeB

theorem unique_predecessor_before {source a b goal : Fin m}
    (bound : goal ≤ first reads output forward live source)
    (routeA : ReflTransGen reads source a) (edgeA : reads a goal)
    (routeB : ReflTransGen reads source b) (edgeB : reads b goal) : a = b := by
  have aBound := le_trans (le_of_lt (forward edgeA)) bound
  have bBound := le_trans (le_of_lt (forward edgeB)) bound
  exact unique_follow_predecessor reads output forward
    (read_before reads output forward live routeA aBound).1
    (edge_before reads output forward live routeA edgeA bound)
    (read_before reads output forward live routeB bBound).1
    (edge_before reads output forward live routeB edgeB bound)

lemma witness_of_positive_sum {α : Type*} (weight : α → Nat) (xs : List α)
    (positive : 0 < (xs.map weight).sum) : ∃ a ∈ xs, 0 < weight a := by
  induction xs with
  | nil => simp at positive
  | cons a rest ih =>
    by_cases h : 0 < weight a
    · exact ⟨a, by simp, h⟩
    have hr : 0 < (rest.map weight).sum := by
      simp only [List.map_cons, List.sum_cons] at positive
      omega
    obtain ⟨b, hb, hbPos⟩ := ih hr
    exact ⟨b, by simp [hb], hbPos⟩

lemma sum_le_one_of_unique_positive {α : Type*} (weight : α → Nat) (xs : List α)
    (distinct : xs.Nodup) (small : ∀ a ∈ xs, weight a ≤ 1)
    (unique : ∀ a ∈ xs, ∀ b ∈ xs, 0 < weight a → 0 < weight b → a = b) :
    (xs.map weight).sum ≤ 1 := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    simp only [List.nodup_cons] at distinct
    simp only [List.map_cons, List.sum_cons]
    by_cases h : weight a = 0
    · rw [h, Nat.zero_add]
      exact ih distinct.2 (fun b hb => small b (by simp [hb]))
        (fun b hb c hc => unique b (by simp [hb]) c (by simp [hc]))
    have restZero : (rest.map weight).sum = 0 := by
      by_contra some
      obtain ⟨b, hb, hbPos⟩ := witness_of_positive_sum weight rest (by omega)
      have equal := unique a (by simp) b (by simp [hb]) (by omega) hbPos
      exact distinct.1 (by simpa [equal] using hb)
    rw [restZero, Nat.add_zero]
    exact small a (by simp)

section Count

variable (parents : Fin m → List (Fin m))
variable (reads_parent : ∀ a b : Fin m, reads a b ↔ a ∈ parents b)
variable (weight : Fin m → Nat) (source : Fin m)
variable (other_weight : ∀ v : Fin m, v ≠ source → weight v = ((parents v).map weight).sum)

include forward reads_parent other_weight in
theorem weight_positive_path {v : Fin m} (positive : 0 < weight v) : ReflTransGen reads source v := by
  revert positive
  induction v using (measure (fun w : Fin m => w.val)).wf.induction with
  | h v ih =>
    intro positive
    by_cases isSource : v = source
    · subst v
      exact ReflTransGen.refl
    rw [other_weight v isSource] at positive
    obtain ⟨a, member, hp⟩ := witness_of_positive_sum weight (parents v) positive
    have edge := (reads_parent a v).mpr member
    have earlier := forward edge
    exact (ih a earlier hp).tail edge

include reads_parent other_weight in
theorem weight_before_le_one (rootWeight : weight source = 1) (distinct : ∀ v, (parents v).Nodup)
    {v : Fin m} (bound : v ≤ first reads output forward live source) : weight v ≤ 1 := by
  revert bound
  induction v using (measure (fun w : Fin m => w.val)).wf.induction with
  | h v ih =>
    intro bound
    by_cases isSource : v = source
    · subst v
      exact le_of_eq rootWeight
    rw [other_weight v isSource]
    apply sum_le_one_of_unique_positive weight (parents v) (distinct v)
    · intro a member
      have earlier := forward ((reads_parent a v).mpr member)
      exact ih a earlier (le_trans (le_of_lt earlier) bound)
    · intro a ma b mb ha hb
      exact unique_predecessor_before reads output forward live bound
        (weight_positive_path reads forward parents reads_parent weight source other_weight ha)
        ((reads_parent a v).mpr ma)
        (weight_positive_path reads forward parents reads_parent weight source other_weight hb)
        ((reads_parent b v).mpr mb)

end Count

end FirstBranchRoute

namespace PetersenFirstGroup

open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutFormula PetersenCutIndependent PetersenCutTrace PetersenScratch

noncomputable def firstInputBoundary {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (i : Fin n) : Fin (n + gs.length) :=
  FirstBranchRoute.first (readEdge gs) out (read_order clean) live (inputWire gs i)

noncomputable def firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) : Finset (Fin n) :=
  Finset.univ.filter fun i => firstInputBoundary clean out live i = cut

theorem mem_firstInputGroup {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) (i : Fin n) :
    i ∈ firstInputGroup clean out live cut ↔ firstInputBoundary clean out live i = cut := by
  simp [firstInputGroup]

theorem wire_le_output {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (w : Fin (n + gs.length)) : w ≤ out := by
  let last : Fin (n + gs.length) := ⟨n + gs.length - 1, by have := out.isLt; omega⟩
  have top (v : Fin (n + gs.length)) : v ≤ last := by
    change v.val ≤ n + gs.length - 1
    have := v.isLt
    omega
  have lastOut : last = out := by
    by_contra notOutput
    obtain ⟨v, e⟩ := live last notOutput
    exact (not_lt_of_ge (top v)) (read_order clean e)
  exact lastOut ▸ top w

theorem firstInputBoundary_occurrences_le_one {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (fallback chosen : Fin n) :
    occurrences chosen (wireFormula fallback gs (firstInputBoundary clean out live chosen).val)
      ≤ 1 := by
  let weight (a : Fin (n + gs.length)) := occurrences chosen (wireFormula fallback gs a.val)
  have sourcePrimary : (inputWire gs chosen).val < n := chosen.isLt
  have atSource : weight (inputWire gs chosen) = 1 := by
    dsimp [weight]
    rw [wireFormula_count_input_fin fallback chosen _ sourcePrimary, ite_eq_left rfl]
  have otherWeight : ∀ w : Fin (n + gs.length), w ≠ inputWire gs chosen →
      weight w = ((predecessors clean w).map weight).sum := by
    intro w other
    by_cases primary : w.val < n
    · simp [weight, wireFormula_count_input_fin fallback chosen w primary, other,
        predecessors_nil_input clean w primary]
    · let p := w.val - n
      have hp : p < gs.length := by have := w.isLt; dsimp [p]; omega
      have hw : w.val = n + p := by dsimp [p]; omega
      let g := gs[p]
      have atSlot : gs[p]? = some g := List.getElem?_eq_getElem hp
      exact wireFormula_count_gate_fin fallback chosen clean atSlot hw _
        (predecessors_val_gate clean w atSlot hw)
  exact FirstBranchRoute.weight_before_le_one (readEdge gs) out (read_order clean) live
    (predecessors clean) (fun a b => (predecessors_mem clean a b).symm) weight
    (inputWire gs chosen) otherWeight atSource distinct le_rfl

theorem firstInputGroup_controlled {n : Nat} {gs : List Gate}
    (clean : CleanL n gs) (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (cut : Fin (n + gs.length)) :
    cut = out ∨ ∀ k : Fin n, k ∈ firstInputGroup clean out live cut →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out := by
  by_cases terminal : cut = out
  · exact Or.inl terminal
  right
  intro k member path
  have before : cut < out := lt_of_le_of_ne (wire_le_output clean out live cut) terminal
  have firstHere := (mem_firstInputGroup clean out live cut k).mp member
  have after : firstInputBoundary clean out live k < out := by rwa [firstHere]
  have blocked := FirstBranchRoute.no_avoiding_after (readEdge gs) out
    (read_order clean) live after
  apply blocked
  change Relation.ReflTransGen (FirstBranchRoute.Avoid (readEdge gs)
    (firstInputBoundary clean out live k)) (inputWire gs k) out
  rw [firstHere]
  exact Relation.ReflTransGen.mono (fun _ _ e => ⟨e.1, e.2.1⟩) _ _ path

end PetersenFirstGroup

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open scoped BigOperators

def operands (gs : List Gate) : List Nat := gs.flatMap Gate.inputs


def notGateCount (gs : List Gate) : Nat := (gs.filter fun g => isNotGate g.op).length

theorem operand_mem_of_read {gs : List Gate} {slot wire : Nat} (read : Reads gs slot wire) :
    wire ∈ operands gs := by
  obtain ⟨g, gAt, before⟩ := read
  exact List.mem_flatMap.mpr ⟨g, List.mem_iff_getElem?.mpr ⟨slot, gAt⟩, before⟩

theorem two_readers_operand_count {gs : List Gate} {wire p q : Nat}
    (neq : p ≠ q) (first : Reads gs p wire) (second : Reads gs q wire) :
    2 ≤ (operands gs).count wire := by
  induction gs generalizing p q with
  | nil =>
    rcases first with ⟨g, atGate, _⟩
    simp at atGate
  | cons a rest ih =>
    simp only [operands, List.flatMap_cons, List.count_append]
    cases p with
    | zero =>
      cases q with
      | zero => exact (neq rfl).elim
      | succ q =>
        have atA : wire ∈ a.inputs := by simpa [Reads] using first
        have later : Reads rest q wire := by simpa [Reads] using second
        have aPos : 0 < a.inputs.count wire := List.count_pos_iff.mpr atA
        have restPos : 0 < (operands rest).count wire := List.count_pos_iff.mpr (operand_mem_of_read later)
        simp only [operands] at restPos
        omega
    | succ p =>
      cases q with
      | zero =>
        have atA : wire ∈ a.inputs := by simpa [Reads] using second
        have later : Reads rest p wire := by simpa [Reads] using first
        have aPos : 0 < a.inputs.count wire := List.count_pos_iff.mpr atA
        have restPos : 0 < (operands rest).count wire := List.count_pos_iff.mpr (operand_mem_of_read later)
        simp only [operands] at restPos
        omega
      | succ q =>
        have early : Reads rest p wire := by simpa [Reads] using first
        have late : Reads rest q wire := by simpa [Reads] using second
        have different : p ≠ q := fun eq => neq (congrArg Nat.succ eq)
        have count := ih different early late
        simp only [operands] at count
        omega

theorem operands_count_length (gs : List Gate)
    (arity : ∀ g ∈ gs, g.inputs.length + (if isNotGate g.op then 1 else 0) = 2) :
    (operands gs).length + notGateCount gs = 2 * gs.length := by
  induction gs with
  | nil => simp [operands, notGateCount]
  | cons g gs ih =>
    have gArity := arity g (by simp)
    have rest := ih (fun q hq => arity q (List.mem_cons_of_mem _ hq))
    cases h : isNotGate g.op
    · simp [h] at gArity
      simp [operands, notGateCount, h] at rest ⊢
      omega
    · simp [h] at gArity
      simp [operands, notGateCount, h] at rest ⊢
      omega

theorem clean_gate_arity {n : Nat} {gs : List Gate} (h : CleanL n gs) :
    ∀ g ∈ gs, g.inputs.length + (if isNotGate g.op then 1 else 0) = 2 := by
  intro g gMem
  obtain ⟨p, atGate⟩ := List.mem_iff_getElem?.mp gMem
  rcases h p g atGate with ⟨op, a, _, args⟩ | ⟨ops, a, b, _, _, args⟩
  · simp [op, args, isNotGate]
  · rcases ops with op | op <;> simp [op, args, isNotGate]

theorem branch_card_add_wire_card_le_operands (gs : List Gate) (branches : Finset Nat)
    (twice : ∀ w ∈ branches, 2 ≤ (operands gs).count w) :
    branches.card + (operands gs).toFinset.card ≤ (operands gs).length := by
  classical
  let W := (operands gs).toFinset
  have subset : branches ⊆ W := by
    intro w wm
    have t := twice w wm
    exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by omega))
  have aux : (∑ w ∈ W, if w ∈ branches then (1 : Nat) else 0) = branches.card := by
    have same : (∑ w ∈ W, if w ∈ branches then (1 : Nat) else 0) =
        ∑ w ∈ branches, if w ∈ branches then (1 : Nat) else 0 := by
      symm
      apply Finset.sum_subset subset
      intro w _ notBranch
      simp [notBranch]
    rw [same]
    simp
  have total : (∑ w ∈ W, (operands gs).count w) = (operands gs).length :=
    List.sum_toFinset_count_eq_length _
  have bound : (∑ w ∈ W, ((if w ∈ branches then (1 : Nat) else 0) + 1)) ≤
      ∑ w ∈ W, (operands gs).count w := by
    apply Finset.sum_le_sum
    intro w wIn
    by_cases b : w ∈ branches
    · simpa [b] using twice w b
    · have pos : 0 < (operands gs).count w := List.count_pos_iff.mpr (List.mem_toFinset.mp wIn)
      simpa [b] using pos
  rw [Finset.sum_add_distrib, aux, total] at bound
  simpa [W] using bound

theorem branching_budget {n out : Nat} {gs : List Gate} (clean : CleanL n gs)
    (outValid : out < n + gs.length)
    (everyNonoutputUsed : ∀ w < n + gs.length, w ≠ out → ∃ p, Reads gs p w)
    (branches : Finset Nat)
    (twoReaders : ∀ w ∈ branches, ∃ p q, p ≠ q ∧ Reads gs p w ∧ Reads gs q w) :
    branches.card + (n + gs.length - 1) + notGateCount gs ≤ 2 * gs.length := by
  let W := (operands gs).toFinset
  let required := (Finset.range (n + gs.length)).erase out
  have requiredUsed : required ⊆ W := by
    intro w inSet
    have spec := Finset.mem_erase.mp inSet
    obtain ⟨p, read⟩ := everyNonoutputUsed w (Finset.mem_range.mp spec.2) spec.1
    exact List.mem_toFinset.mpr (operand_mem_of_read read)
  have numRequired : required.card = n + gs.length - 1 := by
    change ((Finset.range (n + gs.length)).erase out).card = _
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr outValid), Finset.card_range]
  have twice : ∀ w ∈ branches, 2 ≤ (operands gs).count w := by
    intro w mem
    obtain ⟨p, q, different, pReads, qReads⟩ := twoReaders w mem
    exact two_readers_operand_count different pReads qReads
  have up := branch_card_add_wire_card_le_operands gs branches twice
  have used := Finset.card_le_card requiredUsed
  rw [numRequired] at used
  have total := operands_count_length gs (clean_gate_arity clean)
  change n + gs.length - 1 ≤ (operands gs).toFinset.card at used
  omega


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open PetersenCutTrace

theorem branch_slots_of_read_edges {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)}
    (fork : FirstBranchRoute.Branches (readEdge gs) w) :
    ∃ p q, p ≠ q ∧ Reads gs p w.val ∧ Reads gs q w.val := by
  obtain ⟨first, next, pRead, qRead, separate⟩ := fork
  obtain ⟨p, g, atP, src, ap⟩ := pRead
  obtain ⟨q, h, atQ, dst, aq⟩ := qRead
  refine ⟨p, q, ?_, ⟨g, atP, ap⟩, ⟨h, atQ, aq⟩⟩
  intro same
  subst q
  exact separate (Fin.ext (src.trans dst.symm))

noncomputable def circuitBranchWires {n : Nat} (gs : List Gate) : Finset (Fin (n + gs.length)) := by
  classical
  exact (Finset.univ).filter fun w => FirstBranchRoute.Branches (readEdge gs) w

theorem in_circuit_branches {n : Nat} {gs : List Gate} {w : Fin (n + gs.length)} :
    w ∈ circuitBranchWires gs ↔ FirstBranchRoute.Branches (readEdge gs) w := by
  classical
  simp [circuitBranchWires]


namespace PetersenCutTrace

open PEqualNP.CircuitLowerBounds CircuitProof
open Relation

theorem agree_on_input_ancestors {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (x y : Fin n → Bool) (w : Fin (n + gs.length))
    (agrees : ∀ i, ReflTransGen (readEdge gs) (inputWire gs i) w → x i = y i) :
    vl gs x w.val = vl gs y w.val := by
  revert agrees
  induction w using (measure (fun a : Fin (n + gs.length) => a.val)).wf.induction with
  | h w earlier =>
    intro agree
    by_cases input : w.val < n
    · let i : Fin n := ⟨w.val, input⟩
      have name : inputWire gs i = w := Fin.ext rfl
      have atInput : ReflTransGen (readEdge gs) (inputWire gs i) w := by
        simpa only [name] using (ReflTransGen.refl : ReflTransGen (readEdge gs) w w)
      have a := agree i atInput
      simpa only [vl_input gs x w.val input, vl_input gs y w.val input] using a
    · let p := w.val - n
      have pLt : p < gs.length := by have := w.isLt; dsimp [p]; omega
      have gateWire : w.val = n + p := by dsimp [p]; omega
      let g := gs[p]'pLt
      have atGate : gs[p]? = some g := List.getElem?_eq_getElem pLt
      rw [gateWire]
      apply vl_congr gs clean x y p g atGate
      intro a inGate
      have readBefore := (clean p g atGate).lt a inGate
      let wire : Fin (n + gs.length) := ⟨a, by have := w.isLt; omega⟩
      have read : readEdge gs wire w := ⟨p, g, atGate, gateWire, inGate⟩
      apply earlier wire (show wire.val < w.val by change a < w.val; omega)
      intro i path
      exact agree i (path.tail read)

end PetersenCutTrace

open PEqualNP.CircuitLowerBounds
open CircuitProof
open PetersenCutTrace Relation

open PEqualNP.CircuitLowerBounds CircuitProof
open PetersenCutTrace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers
open PetersenCutTrace PetersenFirstGroup

lemma nonNotCount_add_notCount (gs : List Gate) :
    nonNotCount gs + (gs.filter (fun g => isNotGate g.op)).length = gs.length := by
  rw [← List.countP_eq_length_filter]
  induction gs with
  | nil => simp [nonNotCount]
  | cons g gs ih =>
    simp only [nonNotCount, List.countP_cons, List.length_cons] at ih ⊢
    cases h : isNotGate g.op <;> simp [h] <;> omega


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CircuitProof CircuitProof.Readers PetersenCutTrace PetersenFirstGroup
open PetersenCutFormula PetersenCutIndependent PetersenScratch
def Forbid {n : Nat} (F : (Fin n → Bool) → Bool) (i j : Fin n) : Prop :=
  ∀ a o, (∀ u v, F (pairInput i j a u v) = (u && v)) →
    (∀ u v, F (pairInput i j o u v) = (u || v)) → False
theorem forkBudget {n r : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (budget : nonNotCount gs + 1 ≤ n + r) : (circuitBranchWires (n := n) gs).card ≤ r := by
  classical
  let branches := circuitBranchWires (n := n) gs
  have h := branching_budget clean out.isLt (fun w hw hne => by
      let wire : Fin (n + gs.length) := ⟨w, hw⟩
      obtain ⟨v,p,g,hg,_,hw'⟩ := live wire (fun e => hne (congrArg Fin.val e))
      exact ⟨p,g,hg,hw'⟩)
    (branches.image Fin.val) (fun w hw => by
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      exact branch_slots_of_read_edges (in_circuit_branches.mp hv))
  rw [Finset.card_image_of_injective _ Fin.val_injective] at h
  have count := nonNotCount_add_notCount gs
  change nonNotCount gs + notGateCount gs = gs.length at count
  change branches.card ≤ r
  omega

theorem rankCuts {n r : ℕ} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (hcard : (circuitBranchWires (n := n) gs).card ≤ r) :
    ∃ label : Fin n → Fin (r+1),
      (∀ i j, label i = label j ↔ firstInputBoundary clean out live i = firstInputBoundary clean out live j) ∧
      (∀ k : Fin (r+1), ∃ code : (Fin n → Bool) → Bool,
        (∀ x y, (∀ i, label i ≤ k → x i = y i) → code x = code y) ∧
        (∀ x y, (∀ i, label i ≠ k → x i = y i) → code x = code y → vl gs x out.val = vl gs y out.val)) := by
  classical
  let branches := circuitBranchWires (n := n) gs
  change branches.card ≤ r at hcard
  let cuts := insert out branches
  have small : cuts.card ≤ r+1 := (Finset.card_insert_le ..).trans (by omega)
  let boundary := firstInputBoundary clean out live
  have mem (i : Fin n) : boundary i ∈ cuts := by
    rcases FirstBranchRoute.first_stops (readEdge gs) out (read_order clean) live (inputWire gs i)
      with ho | hb
    · exact Finset.mem_insert.mpr (Or.inl ho)
    · exact Finset.mem_insert.mpr (Or.inr (in_circuit_branches.mpr hb))
  let embed := (cuts.orderIsoOfFin rfl).symm
  let rank (c : cuts) : Fin (r+1) :=
    ⟨r+1 - cuts.card + (embed c).val, by have := (embed c).isLt; omega⟩
  have strict : StrictMono rank := by
    intro c d hcd
    have he := embed.strictMono hcd
    change (embed c).val < (embed d).val at he
    change r+1 - cuts.card + (embed c).val < r+1 - cuts.card + (embed d).val
    omega
  let loc (i : Fin n) : cuts := ⟨boundary i, mem i⟩
  let label (i : Fin n) := rank (loc i)
  have eqv (i j : Fin n) : label i = label j ↔ boundary i = boundary j := by
    change rank (loc i) = rank (loc j) ↔ (loc i).val = (loc j).val
    rw [strict.injective.eq_iff, Subtype.ext_iff]
  refine ⟨label, eqv, ?_⟩
  intro k
  by_cases used : ∃ z, label z = k
  · obtain ⟨z, rfl⟩ := used
    let c := boundary z
    have term : FirstBranchRoute.Terminal (readEdge gs) out c :=
      FirstBranchRoute.first_stops (readEdge gs) out (read_order clean) live (inputWire gs z)
    refine ⟨fun x => vl gs x c.val, ?_, ?_⟩
    · intro x y hxy
      apply agree_on_input_ancestors clean
      intro i path
      apply hxy i
      exact strict.monotone (show loc i ≤ loc z from
        FirstBranchRoute.ancestor_first_le (readEdge gs) out (read_order clean) live path term)
    · intro x y hxy heq
      have blocked := firstInputGroup_controlled clean out live c
      rcases blocked with atOut | apart
      · simpa only [atOut] using heq
      · apply circuit_cut_agreement clean c out x y heq
        intro i hi
        apply apart i
        apply (mem_firstInputGroup clean out live c i).mpr
        exact (eqv i z).mp (by_contra fun ne => hi (hxy i ne))
  · refine ⟨fun _ => false, fun _ _ _ => rfl, ?_⟩
    intro x y hxy _
    have : x = y := funext (fun i => hxy i (fun h => used ⟨i,h⟩))
    rw [this]


theorem generalConflict {n : Nat} {gs : List Gate} (clean : CleanL n gs)
    (out : Fin (n + gs.length))
    (live : ∀ w : Fin (n + gs.length), w ≠ out → ∃ v, readEdge gs w v)
    (distinct : ∀ w, (predecessors clean w).Nodup)
    (e : Fin n × Fin n)
    (same : firstInputBoundary clean out live e.1 = firstInputBoundary clean out live e.2) :
    Forbid (fun x => vl gs x out.val) e.1 e.2 := by
  intro ctxA ctxO hand hor
  let cut := firstInputBoundary clean out live e.1
  have hi := firstInputBoundary_occurrences_le_one clean out live distinct e.1 e.1
  have hj := firstInputBoundary_occurrences_le_one clean out live distinct e.1 e.2
  rw [← same] at hj
  have controlled : cut = out ∨ ∀ k : Fin n, (k = e.1 ∨ k = e.2) →
      ¬ Relation.ReflTransGen (avoid (readEdge gs) cut) (inputWire gs k) out := by
    rcases firstInputGroup_controlled clean out live cut with h | h
    · exact Or.inl h
    · apply Or.inr
      intro k hk
      apply h
      apply (mem_firstInputGroup clean out live cut k).mpr
      rcases hk with hk | hk
      · rw [hk]
      · rw [hk]
        exact same.symm
  have factor (base : Fin n → Bool) : ∃ outer : Bool → Bool, ∀ a b,
      outer (pairValue e.1 e.2 base (wireFormula e.1 gs cut.val) a b) =
        vl gs (pairInput e.1 e.2 base a b) out.val := by
    obtain ⟨outer, ho⟩ := cut_factors clean cut out (fun k => k = e.1 ∨ k = e.2) base controlled
    refine ⟨outer, fun a b => ?_⟩
    unfold pairValue
    rw [wireFormula_eval e.1 clean _ cut.val cut.isLt]
    apply ho
    intro k hk
    simp [pairInput, show k ≠ e.1 from fun h => hk (Or.inl h),
      show k ≠ e.2 from fun h => hk (Or.inr h)]
  obtain ⟨fa, ha⟩ := factor ctxA
  obtain ⟨fo, ho⟩ := factor ctxO
  apply fixed_pair_invariant e.1 e.2 (wireFormula e.1 gs cut.val) hi hj _ _ fa fo
  · intro a b; exact (ha a b).trans (hand a b)
  · intro a b; exact (ho a b).trans (hor a b)

structure Grouping {n : Nat} (r : Nat) (F : (Fin n → Bool) → Bool) where
  label : Fin n → Fin (r+1)
  pair : ∀ i j, label i = label j → Forbid F i j
  cut : ∀ k, ∃ code : (Fin n → Bool) → Bool,
    (∀ x y, (∀ i, label i ≤ k → x i = y i) → code x = code y) ∧
    (∀ x y, (∀ i, label i ≠ k → x i = y i) → code x = code y → F x = F y)

namespace RankRules

inductive Rule (n : Nat)
  | square (i j : Fin n) (a o : Nat)
  | cube (i j k : Fin n) (a b c : Nat) (bit sign : Bool)

def row {n : Nat} (m : Nat) : Fin n → Bool := fun i => m.testBit i.val

def accepts {n r : Nat} (label : Fin n → Fin r) : Rule n → Bool
  | .square i j _ _ => label i != label j
  | .cube i j k _ _ _ _ _ => (label i != label j) || decide (label k ≤ label i)

end RankRules
end PEqualNP.Outside.L_meta_1677.RankBase

namespace PEqualNP.Outside.L_meta_1677.FrontRanks

abbrev Word := BitVec 512

def fits (mono desired ground sample : Bool) : Bool :=
  if mono then if desired then !ground || sample else !sample || ground else ground == sample

def pinMask (mono desired sample : Bool) (w : Word) : Word :=
  if fits mono desired false sample then
    if fits mono desired true sample then BitVec.allOnes 512 else ~~~w
  else if fits mono desired true sample then w else 0

def mask (mono desired : Bool) : (ws : List Word) → (Fin ws.length → Bool) → Word
  | [], _ => BitVec.allOnes 512
  | w :: ws, x => pinMask mono desired (x 0) w &&& mask mono desired ws (fun i => x i.succ)

def forced (target : Word) (mono desired : Bool) (ws : List Word) (x : Fin ws.length → Bool) : Bool :=
  decide ((mask mono desired ws x &&& (if desired then target else ~~~target)) ≠ (0 : Word))

theorem mask_spec (mono b) (p : Fin 512) (ws : List Word) (x : Fin ws.length → Bool) :
    (mask mono b ws x).getLsbD p.val = true ↔
      ∀ i, fits mono b ((ws.get i).getLsbD p.val) (x i) = true := by
  induction ws with
  | nil =>
    change (BitVec.allOnes 512).getLsbD p.val = true ↔ _
    simp only [BitVec.getLsbD_allOnes, p.isLt, decide_true, true_iff]
    intro i
    exact Fin.elim0 i
  | cons w ws ih =>
    have pin : (pinMask mono b (x 0) w).getLsbD p.val =
        fits mono b (w.getLsbD p.val) (x 0) := by
      cases mono <;> cases b <;> cases q : x 0 <;>
        simp only [pinMask, fits, q, Bool.not_false, Bool.not_true, Bool.false_or,
          Bool.true_or, Bool.or_false, Bool.or_true, Bool.false_eq_true, Bool.true_eq_false,
          ite_false, ite_true, beq_false, beq_true, BitVec.getLsbD_allOnes, BitVec.getLsbD_not,
          BitVec.getLsbD_zero, p.isLt, decide_true, Bool.true_and]
    simp only [mask,BitVec.getLsbD_and,Bool.and_eq_true,ih,pin]
    constructor
    · intro ⟨h0,hs⟩ i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact h0
      · exact hs j
    · intro h
      exact ⟨h 0, fun i => h i.succ⟩

theorem forced_sound {ws : List Word} {target : Word} {mono : Bool}
    (F : (Fin ws.length → Bool) → Bool)
    (agree : ∀ p : Fin 512, F (fun i => (ws.get i).getLsbD p.val) = target.getLsbD p.val)
    (mon : mono = true → Monotone F) (b : Bool) (x) (h : forced target mono b ws x = true) :
    F x = b := by
  let bits := mask mono b ws x &&& (if b then target else ~~~target)
  have nzero : bits ≠ 0 := of_decide_eq_true h
  obtain ⟨p,hp⟩ : ∃ p : Fin 512, bits.getLsbD p.val = true := by
    by_contra! hbad
    apply nzero
    apply BitVec.eq_of_getElem_eq
    intro i hi
    have hh := hbad ⟨i,hi⟩
    simpa [BitVec.getLsbD_eq_getElem hi] using hh
  change (mask mono b ws x &&& (if b then target else ~~~target)).getLsbD p.val = true at hp
  simp only [BitVec.getLsbD_and, Bool.and_eq_true] at hp
  have fh := (mask_spec mono b p ws x).mp hp.1
  have ground : F (fun i => (ws.get i).getLsbD p.val) = b := by
    rw [agree]; cases b <;> simpa [p.isLt] using hp.2
  cases hm : mono with
  | false =>
    have eq : (fun i => (ws.get i).getLsbD p.val) = x := by
      funext i; simpa [fits,hm] using fh i
    rwa [eq] at ground
  | true =>
    cases b with
    | false =>
      have le : x ≤ fun i => (ws.get i).getLsbD p.val := by
        intro i
        have hi := fh i
        cases q : x i <;> cases v : (ws.get i).getLsbD p.val <;> simp_all [fits]
      have bound := mon hm le
      rw [ground] at bound
      cases e : F x <;> simp_all
      exact (by decide : ¬ true ≤ false) bound
    | true =>
      have le : (fun i => (ws.get i).getLsbD p.val) ≤ x := by
        intro i
        have hi := fh i
        cases q : x i <;> cases v : (ws.get i).getLsbD p.val <;> simp_all [fits]
      have bound := mon hm le
      rw [ground] at bound
      cases e : F x <;> simp_all
      exact (by decide : ¬ true ≤ false) bound
end PEqualNP.Outside.L_meta_1677.FrontRanks

namespace PEqualNP.Outside.L_meta_1677.FrontRanks
open RankBase RankBase.RankRules RankBase.PetersenScratch

def checksRule (target : Word) (mono : Bool) (ws : List Word) : Rule ws.length → Bool :=
  let checkValue := fun x b => forced target mono b ws x
  fun
  | .square i j a o =>
      [false,true].all fun u => [false,true].all fun v =>
        checkValue (pairInput i j (row a) u v) (u && v) &&
        checkValue (pairInput i j (row o) u v) (u || v)
  | .cube i j k a b c bit sign =>
      let hi m := Function.update (row m) k bit
      ((List.finRange ws.length).all fun v => v == i || v == j ||
        (row a v == row b v && row b v == row c v)) &&
      checkValue (row a) false &&
      checkValue (row b) true &&
      checkValue (hi a) sign &&
      checkValue (hi b) sign &&
      checkValue (hi c) (!sign)

theorem checksRule_sound {target : Word} {mono : Bool} {ws : List Word} {r : Nat}
    (F : (Fin ws.length → Bool) → Bool)
    (agree : ∀ p : Fin 512, F (fun i => (ws.get i).getLsbD p.val) = target.getLsbD p.val)
    (mon : mono = true → Monotone F) (group : Grouping r F) {rule : Rule ws.length}
    (h : checksRule target mono ws rule = true) : accepts group.label rule = true := by
  have evaluation {x b} (e : forced target mono b ws x = true) : F x = b :=
    forced_sound F agree mon b x e
  cases rule with
  | square i j a o =>
    apply bne_iff_ne.mpr
    intro eq
    have all (u v : Bool) := List.all_eq_true.mp
      (List.all_eq_true.mp h u (by cases u <;> decide)) v (by cases v <;> decide)
    exact group.pair i j eq (row a) (row o)
      (fun u v => by
        have both := all u v
        simp only [Bool.and_eq_true] at both
        exact evaluation both.1)
      (fun u v => by
        have both := all u v
        simp only [Bool.and_eq_true] at both
        exact evaluation both.2)
  | cube i j k a b c bit sign =>
    simp only [accepts, Bool.or_eq_true, bne_iff_ne, decide_eq_true_eq]
    by_cases eq : group.label i = group.label j
    · right
      by_contra nl
      have high := lt_of_not_ge nl
      simp only [checksRule, Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨⟨same,va⟩,vb⟩,vha⟩,vhb⟩,vhc⟩ := h
      obtain ⟨code,lower,upper⟩ := group.cut (group.label i)
      let upd (m : Nat) := Function.update (row m) k bit
      have noChange (m : Nat) : code (upd m) = code (row m) := by
        apply lower
        intro u hu
        apply Function.update_of_ne
        intro e
        subst u
        exact (not_le_of_gt high) hu
      have share {u} (hu : group.label u ≠ group.label i) :
          row a u = row b u ∧ row b u = row c u := by
        have s := List.all_eq_true.mp same u (List.mem_finRange u)
        have ei : u ≠ i := fun e => hu (e ▸ rfl)
        have ej : u ≠ j := fun e => hu (e ▸ eq.symm)
        simpa [ei,ej] using s
      have ab : code (row a) ≠ code (row b) := by
        intro e
        have bad := upper _ _ (fun _ hu => (share hu).1) e
        rw [evaluation va,evaluation vb] at bad
        contradiction
      have lift {p q : Nat} (off : ∀ u, group.label u ≠ group.label i → row p u = row q u) :
          ∀ u, group.label u ≠ group.label i → upd p u = upd q u := by
        intro u hu
        by_cases e : u = k
        · subst u; simp [upd]
        · simpa only [upd,Function.update_of_ne e] using off u hu
      have ac : code (row a) ≠ code (row c) := by
        intro e
        have bad := upper _ _ (lift fun _ hu => (share hu).1.trans (share hu).2)
          ((noChange a).trans (e.trans (noChange c).symm))
        change F (Function.update (row a) k bit) = F (Function.update (row c) k bit) at bad
        rw [evaluation vha,evaluation vhc] at bad
        cases sign <;> cases bad
      have bc : code (row b) ≠ code (row c) := by
        intro e
        have bad := upper _ _ (lift fun _ hu => (share hu).2)
          ((noChange b).trans (e.trans (noChange c).symm))
        change F (Function.update (row b) k bit) = F (Function.update (row c) k bit) at bad
        rw [evaluation vhb,evaluation vhc] at bad
        cases sign <;> cases bad
      cases ha : code (row a) <;> cases hb : code (row b) <;> cases hc : code (row c) <;> simp_all
    · exact Or.inl eq
def readFin (n x : Nat) : Option (Fin n) :=
  if h : x < n then some ⟨x,h⟩ else none

def ruleCode (n w : Nat) : Option (Rule n) := do
  let i ← readFin n (w &&& 15)
  let j ← readFin n ((w >>> 4) &&& 15)
  let k := (w >>> 8) &&& 15
  let pay := w >>> 12
  let raw := pay &&& 4095
  if k == 15 then
    return .square i j raw (pay >>> 12)
  else
    let pivot ← readFin n k
    let corner (m : Nat) := raw ||| ((m &&& 1) <<< i.val) ||| (((m >>> 1) &&& 1) <<< j.val)
    return .cube i j pivot (corner (pay >>> 12)) (corner (pay >>> 14))
      (corner (pay >>> 16)) (!(raw.testBit k)) (pay.testBit 18)

def readRules (n : Nat) : Nat → Nat → List (Rule n)
  | 0, _ => []
  | c+1, w =>
    (ruleCode n (w &&& 0xfffffffff)).toList ++ readRules n c (w >>> 36)

namespace ColorBits

def span (w : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => span w f n ||| (f n <<< (n*w))

def Bounded (a w : Nat) := ∀ j, w ≤ j → a.testBit j = false

theorem span_out {w f} (hf : ∀ d, Bounded (f d) w) (n : Nat) : Bounded (span w f n) (n*w) := by
  induction n with
  | zero => simp [Bounded,span]
  | succ n ih =>
    intro j hj
    simp only [span,Nat.testBit_or,Nat.testBit_shiftLeft]
    rw [Nat.succ_mul] at hj
    rw [ih j (by omega),hf n _ (by omega)]
    simp

theorem span_at {w f} (hf : ∀ d, Bounded (f d) w) {d j} (hj : j < w) :
    ∀ n, d < n → (span w f n).testBit (d*w+j) = (f d).testBit j := by
  intro n
  induction n with
  | zero => omega
  | succ n ih =>
    intro hd
    simp only [span,Nat.testBit_or,Nat.testBit_shiftLeft]
    by_cases same : d = n
    · subst d
      rw [span_out hf n _ (by omega)]
      simp
    · have lt : d < n := by omega
      have lim := Nat.mul_le_mul_right w (show d+1 ≤ n by omega)
      rw [Nat.succ_mul] at lim
      rw [ih lt]
      simp [show ¬n*w ≤ d*w+j by omega]

def full (w : Nat) := (1 <<< w)-1
theorem full_bit (w j : Nat) : (full w).testBit j = decide (j < w) := by
  simp [full,Nat.shiftLeft_eq]

def plane (r bit : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, i =>
    let w := r^n
    if i == n then span w (fun d => if d.testBit bit then full w else 0) r
    else let v := plane r bit n i; span w (fun _ => v) r

theorem digit_out (w bit d : Nat) : Bounded (if d.testBit bit then full w else 0) w := by
  intro j hj
  split <;> simp [full_bit,show ¬j<w by omega]

theorem plane_out (r bit n i : Nat) : Bounded (plane r bit n i) (r^n) := by
  induction n with
  | zero => simp [Bounded,plane]
  | succ n ih =>
    rw [plane,Nat.pow_succ']
    split
    · exact span_out (digit_out _ _) r
    · exact span_out (fun _ => ih) r

def index (r : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => f n * r^n + index r f n

theorem index_lt {r f n} (hf : ∀ i < n, f i < r) : index r f n < r^n := by
  induction n with
  | zero => simp [index]
  | succ n ih =>
    have sm := ih (fun i hi => hf i (by omega))
    have lim := Nat.mul_le_mul_right (r^n) (show f n + 1 ≤ r from hf n (by omega))
    rw [Nat.succ_mul] at lim
    rw [index,Nat.pow_succ']
    omega

theorem plane_at {r f n i} (bit : Nat) (hf : ∀ j < n, f j < r) (hi : i < n) :
    (plane r bit n i).testBit (index r f n) = (f i).testBit bit := by
  induction n with
  | zero => omega
  | succ n ih =>
    have prior (j) (hj : j < n) := hf j (by omega)
    have ix := index_lt prior
    have ln := hf n (by omega)
    rw [plane,index]
    by_cases eq : i = n
    · subst i
      simp only [beq_self_eq_true,ite_true]
      rw [span_at (digit_out _ _) ix _ ln]
      cases z : (f n).testBit bit <;> simp [full_bit,ix]
    · simp only [beq_iff_eq,eq,ite_false]
      rw [span_at (fun _ => plane_out r bit n i) ix _ ln]
      exact ih prior (by omega)

def allowed {n} (all : Nat) (cols : List (Nat × Nat × Nat)) : Rule n → Nat
  | .square i j .. =>
    let a := cols.getD i (0,0,0); let b := cols.getD j (0,0,0)
    (a.1 ^^^ b.1) ||| (a.2.1 ^^^ b.2.1) ||| (a.2.2 ^^^ b.2.2)
  | .cube i j k .. =>
    let a := cols.getD i (0,0,0); let b := cols.getD j (0,0,0); let c := cols.getD k (0,0,0)
    let diff := (a.1 ^^^ b.1) ||| (a.2.1 ^^^ b.2.1) ||| (a.2.2 ^^^ b.2.2)
    let lo := (a.2.1 &&& (all ^^^ c.2.1)) ||| ((all ^^^ (a.2.1 ^^^ c.2.1)) &&& (a.1 ||| (all ^^^ c.1)))
    let le := (a.2.2 &&& (all ^^^ c.2.2)) ||| ((all ^^^ (a.2.2 ^^^ c.2.2)) &&& lo)
    diff ||| le

def fast {n} (r : Nat) (rs : List (Rule n)) : Bool :=
  if 1 ≤ r && r ≤ 5 && n ≤ 12 then
    let all := full (r^n)
    let cols := (List.range n).map (fun (i : Nat) => (plane r 0 n i,plane r 1 n i,plane r 2 n i))
    rs.foldl (fun a q => a &&& allowed all cols q) all != 0
  else true

theorem binary_diff : ∀ a b : Fin 5, ((a.val.testBit 0 ^^ b.val.testBit 0) ||
    (a.val.testBit 1 ^^ b.val.testBit 1) || (a.val.testBit 2 ^^ b.val.testBit 2)) = (a != b) := by decide +kernel

theorem binary_le : ∀ a c : Fin 5,
    ((a.val.testBit 2 && !c.val.testBit 2) || (!(a.val.testBit 2 ^^ c.val.testBit 2) &&
    ((a.val.testBit 1 && !c.val.testBit 1) ||
    (!(a.val.testBit 1 ^^ c.val.testBit 1) && (a.val.testBit 0 || !c.val.testBit 0))))) = decide (c ≤ a) := by decide +kernel

theorem fold_bit {α} (ok : α → Nat) (j : Nat) (rs : List α)
    (h : ∀ q ∈ rs, (ok q).testBit j = true) (a : Nat) (ha : a.testBit j = true) :
    (rs.foldl (fun z q => z &&& ok q) a).testBit j = true := by
  induction rs generalizing a with
  | nil => exact ha
  | cons q qs ih =>
    apply ih (fun u hu => h u (List.mem_cons_of_mem _ hu))
    simp [Nat.testBit_and,ha,h q List.mem_cons_self]

theorem sound {n r} {label : Fin n → Fin r} {rules : List (Rule n)}
    (good : ∀ q ∈ rules, accepts label q = true) : fast r rules = true := by
  unfold fast
  split
  next bound =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at bound
    let f (i : Nat) := if h : i < n then (label ⟨i,h⟩).val else 0
    have hf (i) (hi : i < n) : f i < r := by simp only [f,dite_eq_left hi]; exact (label _).isLt
    let ix := index r f n
    let all := full (r^n)
    let cols := (List.range n).map (fun (i : Nat) => (plane r 0 n i,plane r 1 n i,plane r 2 n i))
    have ha : all.testBit ix = true := by simp [all,full_bit,ix,index_lt hf]
    have lookup (i : Fin n) : cols.getD i (0,0,0) = (plane r 0 n i,plane r 1 n i,plane r 2 n i) := by
      simp [cols,List.getD_eq_getElem?_getD,i.isLt]
    have val (i : Fin n) (bit) : (plane r bit n i).testBit ix = (label i).val.testBit bit := by
      simp only [ix,plane_at bit hf i.isLt,f,dite_eq_left i.isLt]
    let v (i : Fin n) : Fin 5 := ⟨(label i).val,by have := (label i).isLt; omega⟩
    have hq (q : Rule n) (hq : q ∈ rules) : (allowed all cols q).testBit ix = true := by
      have g := good q hq
      cases q with
      | square i j a o =>
        simp only [allowed,lookup,Nat.testBit_or,Nat.testBit_xor,val]
        rw [binary_diff (v i) (v j)]
        exact g
      | cube i j k a b c bit sign =>
        simp only [allowed,lookup,Nat.testBit_or,Nat.testBit_and,Nat.testBit_xor,val,ha,Bool.true_xor]
        rw [binary_diff (v i) (v j),binary_le (v i) (v k)]
        exact g
    have ok := fold_bit (allowed all cols) ix rules hq all ha
    change (rules.foldl _ all != 0) = true
    apply bne_iff_ne.mpr
    intro zero
    rw [zero] at ok
    simp at ok
  next => rfl
end ColorBits

namespace PackedRows

def lane : Nat := (1 <<< 512)-1
def matrix : List Word → Nat
  | [] => 0
  | w::ws => w.toNat ||| (matrix ws <<< 512)

def stride (gap : Nat) := ((1 <<< (16*gap))-1)/((1 <<< gap)-1)
def spread (x : Nat) := ((x*stride 511) &&& stride 512)*lane
def collapse (x : Nat) :=
  let a := x ||| (x >>> 4096)
  let b := a ||| (a >>> 2048)
  let c := b ||| (b >>> 1024)
  (c ||| (c >>> 512)) &&& lane

def force (g active T x : Nat) (mono b : Bool) :=
  let s := spread (x &&& active)
  let bad := if mono then
      if b then g ^^^ (g &&& s) else s ^^^ (g &&& s)
    else g ^^^ s
  let want := if b then T else lane ^^^ T
  (want &&& (lane ^^^ collapse bad)) != 0

def edit (m i : Nat) (b : Bool) :=
  if m.testBit i == b then m else m ^^^ (1 <<< i)

def check {n : Nat} (g active T : Nat) (mono : Bool) : Rule n → Bool
  | .square i j a o =>
    [false,true].all fun u => [false,true].all fun v =>
      force g active T (edit (edit a j v) i u) mono (u && v) &&
      force g active T (edit (edit o j v) i u) mono (u || v)
  | .cube i j k a b c bit sign =>
    let except := (1 <<< i.val) ||| (1 <<< j.val)
    let dif := ((a ^^^ b) ||| (b ^^^ c)) &&& active
    ((dif &&& except)==dif) &&
      force g active T a mono false && force g active T b mono true &&
      force g active T (edit a k bit) mono sign && force g active T (edit b k bit) mono sign &&
      force g active T (edit c k bit) mono (!sign)


theorem matrix_bit (ws : List Word) (i j : Nat) (hj : j < 512) :
 (matrix ws).testBit (i*512+j) = ((ws[i]?).getD 0).getLsbD j := by
 induction ws generalizing i with
 | nil => simp [matrix]
 | cons w ws ih =>
   cases i with
   | zero =>
     simp [matrix,Nat.testBit_or,Nat.testBit_shiftLeft,show ¬512≤j by omega,BitVec.getLsbD]
   | succ i =>
     rw [Nat.succ_mul]
     simp only [matrix,Nat.testBit_or,Nat.testBit_shiftLeft]
     have upper : w.toNat.testBit (i*512+512+j) = false := by
       apply Nat.testBit_lt_two_pow
       exact lt_of_lt_of_le w.isLt (Nat.pow_le_pow_right (by decide) (by omega))
     rw [upper]
     simp [show 512 ≤ i*512+512+j by omega, show i*512+512+j-512 = i*512+j by omega,ih]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem collapse_false (z j : Nat) (hj : j<512) :
 (collapse z).testBit j = false ↔ ∀ i : Fin 16, z.testBit (i.val*512+j) = false := by
 simp [collapse,lane,Nat.testBit_and,Nat.testBit_or,Nat.testBit_shiftRight,Nat.shiftLeft_eq,hj,Fin.forall_fin_succ,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
 simp only [and_assoc,and_left_comm,and_comm]

def slowSpread (x : Nat) := ColorBits.span 512 (fun d => if x.testBit d then lane else 0) 16
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem spread_correct : ∀ x : Fin 4096, spread x.val = slowSpread x.val := by decide +kernel

theorem force_sound (ws : List Word) (hn : ws.length ≤ 12) (T : Word) (mono b : Bool) (x : Nat)
 (h : force (matrix ws) (ColorBits.full ws.length) T.toNat x mono b = true) :
 forced T mono b ws (RankBase.RankRules.row x) = true := by
 let y := x &&& ColorBits.full ws.length
 let s := spread y
 let g := matrix ws
 let bad := if mono then if b then g ^^^ (g &&& s) else s ^^^ (g &&& s) else g ^^^ s
 let want := if b then T.toNat else lane ^^^ T.toNat
 change (want &&& (lane ^^^ collapse bad) != 0) = true at h
 obtain ⟨j,hj⟩ := Nat.exists_testBit_of_ne_zero (bne_iff_ne.mp h)
 rw [Nat.testBit_and,Bool.and_eq_true] at hj
 have lim : j<512 := by
   by_contra! large
   have t := Nat.testBit_lt_two_pow (x:=T.toNat) (i:=j) (lt_of_lt_of_le T.isLt (Nat.pow_le_pow_right (by decide) large))
   have z := hj.1
   cases b <;> simp [want,lane,Nat.testBit_xor,Nat.shiftLeft_eq,t,show ¬j<512 by omega] at z
 have clear := hj.2
 simp only [Nat.testBit_xor,show lane.testBit j = true by simpa [lane,Nat.shiftLeft_eq] using lim,Bool.true_xor,Bool.not_eq_true'] at clear
 have bits := (collapse_false bad j lim).mp clear
 have small : y < 4096 := by
   apply lt_of_le_of_lt (Nat.and_le_right ..)
   have pow := Nat.pow_le_pow_right (n:=2) (by decide) hn
   simp [ColorBits.full,Nat.shiftLeft_eq]
   omega
 have matchRows : ∀ i : Fin ws.length, fits mono b ((ws.get i).getLsbD j) (x.testBit i.val) = true := by
   intro i
   have r := bits ⟨i.val,by omega⟩
   have slice : s.testBit (i.val*512+j) = x.testBit i.val := by
     have eq := spread_correct (⟨y,small⟩ : Fin 4096)
     change (spread y).testBit _ = _
     rw [eq,slowSpread,ColorBits.span_at (w:=512) (f:=fun d => if y.testBit d then lane else 0) (fun d => by
       intro l hl
       split <;> simp [lane,Nat.shiftLeft_eq,show ¬l<512 by omega]) lim 16 (by omega)]
     cases e : x.testBit i.val <;> simp [e,y,Nat.testBit_and,ColorBits.full_bit,i.isLt,lane,Nat.shiftLeft_eq,lim]
   have wire : g.testBit (i.val*512+j) = (ws.get i).getLsbD j := by simpa [g,i.isLt] using matrix_bit ws i.val j lim
   change bad.testBit (i.val*512+j) = false at r
   cases mono <;> cases b <;> simp [bad,Nat.testBit_xor,Nat.testBit_and,wire,slice,fits] at r ⊢ <;> grind
 have gate := (mask_spec mono b ⟨j,lim⟩ ws (RankBase.RankRules.row x)).mpr matchRows
 simp only [forced,decide_eq_true_eq]
 intro zero
 have z := congrArg (fun w : Word => w.getLsbD j) zero
 have t := hj.1
 change (_ &&& _ : Word).getLsbD j = (0 : Word).getLsbD j at z
 rw [BitVec.getLsbD_and,gate] at z
 cases b
 · simp [want,lane,Nat.testBit_xor,Nat.shiftLeft_eq,lim] at t
   change T.getLsbD j = false at t
   simp only [Bool.false_eq_true,ite_false,BitVec.getLsbD_not,lim,decide_true,Bool.true_and,t,Bool.not_false,BitVec.getLsbD_zero] at z
   simpa [BitVec.getLsbD] using z
 · simp [want] at t
   change T.getLsbD j = true at t
   simp [t] at z

theorem row_edit {n} (m : Nat) (i : Fin n) (b : Bool) :
    row (edit m i.val b) = Function.update (row m) i b := by
  funext j
  by_cases h : j = i
  · subst j
    simp only [Function.update_self,row,edit]
    split
    next eq => exact beq_iff_eq.mp eq
    next ne =>
      simp [Nat.testBit_xor,Nat.shiftLeft_eq,Nat.testBit_two_pow]
      cases q : m.testBit i.val <;> cases b <;> simp_all
  · have hij : i.val ≠ j.val := fun e => h (Fin.ext e.symm)
    rw [Function.update_of_ne h]
    simp only [row,edit]
    split
    · rfl
    · simp [Nat.testBit_xor,Nat.shiftLeft_eq,Nat.testBit_two_pow,hij]

theorem edit_pair {n} (m : Nat) (i j : Fin n) (a b : Bool) :
    row (edit (edit m j.val b) i.val a) = pairInput i j (row m) a b := by
  rw [row_edit,row_edit]
  funext k
  by_cases hi : k = i <;> by_cases hj : k = j <;> simp [pairInput,hi,hj,Function.update]

theorem check_sound (T : Word) (mono : Bool) (ws : List Word) (hn : ws.length ≤ 12) (q : Rule ws.length)
 (h : check (matrix ws) (ColorBits.full ws.length) T.toNat mono q = true) : checksRule T mono ws q = true := by
 have F := force_sound ws hn T mono
 cases q with
 | square i j a o =>
   simp only [check,List.all_eq_true,Bool.and_eq_true] at h
   simp only [checksRule,List.all_eq_true,Bool.and_eq_true]
   intro u hu v hv
   obtain ⟨ha,ho⟩ := h u hu v hv
   exact ⟨edit_pair a i j u v ▸ F _ _ ha,edit_pair o i j u v ▸ F _ _ ho⟩
 | cube i j k a b c bit sign =>
   simp only [check,Bool.and_eq_true,beq_iff_eq] at h
   obtain ⟨⟨⟨⟨⟨dif,fa⟩,fb⟩,fak⟩,fbk⟩,fck⟩ := h
   simp only [checksRule,Bool.and_eq_true,List.all_eq_true]
   refine ⟨⟨⟨⟨⟨?_,F _ _ fa⟩,F _ _ fb⟩,row_edit a k bit ▸ F _ _ fak⟩,row_edit b k bit ▸ F _ _ fbk⟩,row_edit c k bit ▸ F _ _ fck⟩
   intro v hv
   by_cases vi : v = i
   · simp [vi]
   by_cases vj : v = j
   · simp [vj]
   have ni : i.val ≠ v.val := fun e => vi (Fin.ext e.symm)
   have nj : j.val ≠ v.val := fun e => vj (Fin.ext e.symm)
   have e := congrArg (fun z : Nat => z.testBit v.val) dif
   simp [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,Nat.shiftLeft_eq,Nat.testBit_two_pow,ni,nj,ColorBits.full_bit,v.isLt] at e
   simp [vi,vj,row]
   grind

end PackedRows

def rankCheck (target : Word) (mono : Bool) (ws : List Word) (r : Nat) (rules : List (Rule ws.length)) : Bool :=
  (ws.length ≤ 12) && rules.all (PackedRows.check (PackedRows.matrix ws) (ColorBits.full ws.length) target.toNat mono) && !(ColorBits.fast (r+1) rules)

theorem rankCheck_sound {target : Word} {mono : Bool} {ws : List Word} {r : Nat} {rules : List (Rule ws.length)}
    (F : (Fin ws.length → Bool) → Bool)
    (agree : ∀ p : Fin 512, F (fun i => (ws.get i).getLsbD p.val) = target.getLsbD p.val)
    (mon : mono = true → Monotone F) (group : Grouping r F)
    (h : rankCheck target mono ws r rules = true) : False := by
  have pass : (ws.length ≤ 12 ∧ rules.all (PackedRows.check (PackedRows.matrix ws) (ColorBits.full ws.length) target.toNat mono) = true) ∧ ColorBits.fast (r+1) rules = false := by
    simpa only [rankCheck, Bool.and_eq_true, Bool.not_eq_true',decide_eq_true_eq] using h
  have accept (claim : Rule ws.length) (hc : claim ∈ rules) : accepts group.label claim = true :=
    checksRule_sound F agree mon group (PackedRows.check_sound target mono ws pass.1.1 claim (List.all_eq_true.mp pass.1.2 _ hc))
  have found : ColorBits.fast (r+1) rules = true :=
    ColorBits.sound (r:=r+1) (label:=group.label) accept
  rw [pass.2] at found
  contradiction

end PEqualNP.Outside.L_meta_1677.FrontRanks

namespace PEqualNP.Outside.L_meta_1677.FrontRanks
open RankBase RankBase.RankRules

def readPrefixField (format : Nat → Nat × (Nat → Nat)) (read : Nat → Nat → Nat)
    (kind p raw : Nat) : Nat × Nat :=
  let t := format kind
  let ent := t.2 (read p t.1)
  let value := ent &&& 8191
  let next := p+(ent >>> 13)
  if value == 4096 then (read next raw,next+raw) else (value,next)

def insertZeroAt (x i : Nat) : Nat :=
  (x &&& ((1 <<< i)-1)) ||| ((x >>> i) <<< (i+1))

def expandRow (x h : Nat) : Nat :=
  let i := h &&& 15
  let j := (h >>> 4) &&& 15
  insertZeroAt (insertZeroAt x (min i j)) (max i j)

def readDirect (n : Nat) (f : Nat → Nat × (Nat → Nat)) (read : Nat → Nat → Nat) :
    Nat → Nat → List (Rule n)
  | 0, _ => []
  | count+1, p =>
    let item := if read p 1 == 1 then
        ((f 4).2 (read (p+1) 10),p+11)
      else
        let hdr := readPrefixField f read 0 (p+1) 12
        let base := readPrefixField f read 1 hdr.2 (n-2)
        let square := hdr.1 >>> 8 == 15
        let tail := readPrefixField f read (if square then 3 else 2) base.2 (if square then n-2 else 7)
        let z := if square then expandRow tail.1 hdr.1 else tail.1
        (hdr.1 ||| (expandRow base.1 hdr.1 <<< 12) ||| (z <<< 24),tail.2)
    (ruleCode n item.1).toList ++ readDirect n f read count item.2

def rankHuffCheck (target : Word) (mono : Bool) (ws : List Word) (r : Nat)
    (format : Nat → Nat × (Nat → Nat)) (read : Nat → Nat → Nat) (tag p : Nat) : Bool :=
  if tag == 0 then false else if tag == 1 then
    forced target mono false ws (row (read p ws.length)) &&
      forced target mono true ws (row (read p ws.length))
  else
    rankCheck target mono ws r (readDirect ws.length format read (tag-2) p)

theorem rankHuffCheck_sound {target : Word} {mono : Bool} {ws : List Word} {r tag p : Nat}
    {format : Nat → Nat × (Nat → Nat)} {read : Nat → Nat → Nat}
    (F : (Fin ws.length → Bool) → Bool)
    (agree : ∀ p : Fin 512, F (fun i => (ws.get i).getLsbD p.val) = target.getLsbD p.val)
    (mon : mono = true → Monotone F) (group : Grouping r F)
    (h : rankHuffCheck target mono ws r format read tag p = true) : False := by
  unfold rankHuffCheck at h
  split at h
  · contradiction
  split at h
  · simp only [Bool.and_eq_true] at h
    have no := forced_sound F agree mon false _ h.1
    have yes := forced_sound F agree mon true _ h.2
    rw [no] at yes
    contradiction
  · exact rankCheck_sound F agree mon group h

end PEqualNP.Outside.L_meta_1677.FrontRanks

namespace PEqualNP.Outside.L_meta_1677

open PEqualNP.CircuitLowerBounds

open PEqualNP.CircuitLowerBounds

namespace FromFrontier

def good (n : Nat) (g : Gate) : Prop :=
  (g.op = .not ∧ ∃ i<n, g.inputs=[i]) ∨
    ((g.op = .or ∨ g.op = .and) ∧ ∃ i<n, ∃ j<n, i≠j ∧ g.inputs=[i,j])

def wasRead (gs : List Gate) (i : Nat) : Prop := ∃ g∈gs, i∈g.inputs

def isNeg : GateOp → Bool
  | .not => true
  | _ => false

def realization (w : List Sig) (used : Nat → Prop) (T : Sig) (k t : Nat) : Prop :=
  ∃ (gs : List Gate) (o : Nat), gs.length=k ∧
    gs.countP (fun g => isNeg g.op)=t ∧ o<w.length+gs.length ∧
    (execute gs w).getD o zero=T ∧
    (∀ p g, gs[p]?=some g → good (w.length+p) g) ∧
    ∀ i<w.length+gs.length, i≠o → used i ∨ wasRead gs i

def bank (w : List Sig) (used : Nat → Prop) (S : Finset Sig) (ix : Sig → Nat) : Prop :=
  (∀ s∈S, ix s<w.length ∧ w.getD (ix s) zero=s) ∧
    ∀ i<w.length, used i ∨ ∃ s∈S, ix s=i

theorem forward {w : List Sig} {used : Nat → Prop} {T : Sig} {k t : Nat}
    {g : Gate} {z : Sig} (eq : gv w g=z) (ok : good w.length g)
    (next : realization (w++[z]) (fun i => used i ∨ i∈g.inputs) T k t) :
    realization w used T (k+1) (t+(if isNeg g.op then 1 else 0)) := by
  obtain ⟨gs,o,hl,ht,hb,he,hg,hr⟩ := next
  refine ⟨g::gs,o,by simp [hl],?_,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb,?_,?_,?_⟩
  · cases n : isNeg g.op <;> simp [List.countP_cons,ht,n,Nat.add_comm]
  · change (execute gs (w++[gv w g])).getD o zero=T
    rwa [eq]
  · intro p h hit
    cases p with
    | zero =>
      change some g=some h at hit
      exact Option.some.inj hit ▸ ok
    | succ p =>
      have sub : gs[p]?=some h := hit
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hg p h sub
  · intro i hi ne
    have bounds : i<(w++[z]).length+gs.length := by
      simp only [List.length_cons] at hi
      simp only [List.length_append,List.length_singleton]; omega
    rcases hr i bounds ne with (prior|atGate)|⟨h,hh,hi⟩
    · exact .inl prior
    · exact .inr ⟨g,by simp,atGate⟩
    · exact .inr ⟨h,List.mem_cons_of_mem _ hh,hi⟩

theorem extendBank {w : List Sig} {used : Nat → Prop} {S U : Finset Sig}
    {ix : Sig → Nat} {z : Sig} {g : Gate} (b : bank w used S ix)
    (fresh : z∉U) (subset : U⊆S) (reads : ∀ s∈S, s∈U ∨ ix s∈g.inputs) :
    bank (w++[z]) (fun i => used i ∨ i∈g.inputs) (insert z U)
      (fun s => if s=z then w.length else ix s) := by
  constructor
  · intro s hs
    rcases Finset.mem_insert.mp hs with rfl|hu
    · simp
    · have ne : s≠z := fun h => fresh (h ▸ hu)
      obtain ⟨bound,val⟩ := b.1 s (subset hu)
      simp only [ne,ite_false,List.length_append,List.length_singleton]
      refine ⟨by omega,?_⟩
      simpa only [List.getD_eq_getElem?_getD,List.getElem?_append_left bound] using val
  · intro i hi
    simp only [List.length_append,List.length_singleton] at hi
    by_cases lt : i<w.length
    · rcases b.2 i lt with already|⟨s,hs,hi⟩
      · exact .inl (.inl already)
      rcases reads s hs with hu|read
      · have ne : s≠z := fun h => fresh (h ▸ hu)
        exact .inr ⟨s,Finset.mem_insert_of_mem hu,by simpa [ne] using hi⟩
      · exact .inl (.inr (hi ▸ read))
    · have h : i=w.length := by omega
      exact .inr ⟨z,by simp,by simp [h]⟩

theorem build {T : Sig} {k t : Nat} {S : Finset Sig} (h : Live T k t S) :
    ∀ (w : List Sig) (used : Nat → Prop) (ix : Sig → Nat),
      bank w used S ix → realization w used T k t := by
  induction h with
  | stop hp =>
    intro w used ix b
    obtain ⟨bound,val⟩ := b.1 T (by simp)
    refine ⟨[],ix T,rfl,rfl,by simpa using bound,val,?_,?_⟩
    · intro i g hit; simp at hit
    · intro i hi ne
      rcases b.2 i (by simpa using hi) with hu|⟨s,hs,hit⟩
      · exact Or.inl hu
      simp only [Finset.mem_singleton] at hs
      exact (ne (hs ▸ hit.symm)).elim
  | @unary k t U a proper fresh tail ih =>
    intro w used ix b
    obtain ⟨bound,val⟩ := b.1 a (by simp)
    let g : Gate := ⟨.not,[ix a]⟩
    have hv : gv w g = neg a := by
      change neg (w.getD (ix a) zero)=neg a
      rw [val]
    have well : good w.length g := Or.inl ⟨rfl,ix a,bound,rfl⟩
    apply forward hv well
    apply ih
    apply extendBank b (fun hz => fresh (Finset.mem_insert_of_mem hz)) (fun _ hy => Finset.mem_insert_of_mem hy)
    intro s hs
    rcases Finset.mem_insert.mp hs with rfl|hu
    · right; simp [g]
    · exact .inl hu
  | @binary k t U a c d pa pc diff fresh tail ih =>
    intro w used ix b
    obtain ⟨ba,va⟩ := b.1 a (by simp)
    obtain ⟨bc,vc⟩ := b.1 c (by simp)
    have unique : ix a ≠ ix c := fun eq => diff (va.symm.trans (eq ▸ vc))
    let g : Gate := ⟨if d then .or else .and,[ix a,ix c]⟩
    have hv : gv w g = bin d a c := by
      cases d with
      | false =>
        change bin false (w.getD (ix a) zero) (bin false (w.getD (ix c) zero) one)=bin false a c
        rw [va,vc]
        simp only [bin,Bool.false_eq_true,ite_false,one,BitVec.and_allOnes]
      | true =>
        change bin true (w.getD (ix a) zero) (bin true (w.getD (ix c) zero) zero)=bin true a c
        rw [va,vc]
        simp [bin,zero]
    have well : good w.length g := by
      apply Or.inr
      exact ⟨by cases d <;> simp [g],ix a,ba,ix c,bc,unique,rfl⟩
    have notCount : isNeg g.op=false := by cases d <;> rfl
    have rel : realization w used T (k+1) (t+(if isNeg g.op then 1 else 0)) := by
      apply forward hv well
      apply ih
      apply extendBank b (fun hz => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)))
        (fun _ hy => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy))
      intro s hs
      rcases Finset.mem_insert.mp hs with rfl|hrest
      · right; simp [g]
      rcases Finset.mem_insert.mp hrest with rfl|hu
      · right; simp [g]
      · exact .inl hu
    simpa [notCount] using rel

theorem realize {T : Sig} {k t : Nat} (ws : List Sig) (hn : ws.Nodup)
    (h : Live T k t ws.toFinset) : realization ws (fun _ => False) T k t := by
  apply build h ws (fun _ => False) (fun x => ws.idxOf x)
  constructor
  · intro s hs
    have mem := List.mem_toFinset.mp hs
    have lt := List.idxOf_lt_length_of_mem mem
    exact ⟨lt,by rw [List.getD_eq_getElem _ _ lt, List.getElem_idxOf]⟩
  · intro i hi
    refine .inr ⟨ws[i],List.mem_toFinset.mpr (List.getElem_mem hi),?_⟩
    have idx := List.idxOf_lt_length_of_mem (List.getElem_mem hi : ws[i]∈ws)
    have eq : (⟨ws.idxOf ws[i],idx⟩ : Fin ws.length) = ⟨i,hi⟩ :=
      (List.nodup_iff_injective_get.mp hn) (List.getElem_idxOf idx)
    exact congrArg Fin.val eq

end FromFrontier

open PEqualNP.CircuitLowerBounds
open RankBase.CircuitProof RankBase.PetersenCutTrace

namespace FromFrontier

theorem realizeRank {T : Sig} {k t : Nat} (ws : List Sig) (hn : ws.Nodup)
    (h : Live T k t ws.toFinset) :
    ∃ (gs : List Gate) (out : Fin (ws.length + gs.length)) (cl : CleanL ws.length gs),
      nonNotCount gs=k-t ∧ gs.length=k ∧
      (∀ w, w≠out → ∃ v, readEdge gs w v) ∧
      (∀ w, (predecessors cl w).Nodup) ∧
      (∀ x : Fin 512, vl gs (fun i => (ws.get i).getLsbD x.val) out.val =
        T.getLsbD x.val) := by
  obtain ⟨gs,o,hl,ht,ho,val,well,reads⟩ := realize ws hn h
  have clean : CleanL ws.length gs := by
    intro p g hg
    rcases well p g hg with hnot|⟨op,i,bi,j,bj,_,pins⟩
    · exact .inl hnot
    · exact .inr ⟨op.symm,i,j,bi,bj,pins⟩
  refine ⟨gs,⟨o,ho⟩,clean,?_,hl,?_,?_,?_⟩
  · have eq : isNotGate = isNeg := by funext op; cases op <;> rfl
    have total := RankBase.nonNotCount_add_notCount gs
    rw [← List.countP_eq_length_filter,eq] at total
    omega
  · intro w ne
    rcases reads w.val w.isLt (fun eq => ne (Fin.ext eq)) with impossible|⟨g,hg,pin⟩
    · exact impossible.elim
    obtain ⟨i,hi,hgi⟩ := List.getElem_of_mem hg
    exact ⟨⟨ws.length+i,by omega⟩,i,g,by simp [List.getElem?_eq_getElem hi,hgi],rfl,pin⟩
  · intro w
    by_cases internal : ws.length≤w.val
    · apply List.Nodup.of_map Fin.val
      rw [predecessors_values clean w internal]
      have lo : w.val-ws.length < gs.length := by have := w.isLt; omega
      have hw := well _ _ (List.getElem?_eq_getElem lo : gs[w.val-ws.length]?=some _)
      rcases hw with ⟨_,i,_,pins⟩|⟨_,i,_,j,_,ne,pins⟩
      · simp [pins]
      · simp [pins,ne]
    · rw [predecessors_nil_input clean w (by omega)]; simp
  · intro x
    have legal (g : Gate) (hg : g∈gs) : g.op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) := by
      obtain ⟨i,hi,hgi⟩ := List.getElem_of_mem hg
      have got : gs[i]?=some g := by simp [List.getElem?_eq_getElem hi,hgi]
      exact ((clean i g got).nok).1.1
    have init : List.ofFn (fun i : Fin ws.length => bit x (ws.get i))=ws.map (bit x) := by
      apply List.ext_getElem <;> simp
    change (wiresFrom gs (List.ofFn fun i : Fin ws.length => bit x (ws.get i))).getD o false=bit x T
    rw [init]
    change (gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (ws.map (bit x))).getD o false=bit x T
    rw [←execute_bits gs x ws legal,b_read,val]

end FromFrontier

namespace FromFrontier

private theorem increasingRun (gs : List Gate)
    (pos : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) (a b : List Bool)
    (sz : a.length=b.length) (h : ∀ i, a.getD i false ≤ b.getD i false) :
    ∀ i, (wiresFrom gs a).getD i false ≤ (wiresFrom gs b).getD i false := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    apply ih (fun v hv => pos v (by simp [hv]))
    · simp [sz]
    · intro j
      by_cases eq : j=a.length
      · subst j
        rw [getD_snoc_len _ _ _ _ rfl, getD_snoc_len b _ _ _ sz.symm]
        apply Bool.le_iff_imp.mpr
        rcases pos g (by simp) with op|op
        · simp only [op, GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
          intro yes p hp
          exact Bool.le_iff_imp.mp (h p) (yes p hp)
        · simp only [op, GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
          rintro ⟨p,hp,yes⟩
          exact ⟨p,hp,Bool.le_iff_imp.mp (h p) yes⟩
      · rw [getD_snoc_ne _ _ _ _ eq,getD_snoc_ne _ _ _ _ (by omega)]
        exact h j

theorem groupFromLive {T : Sig} {k t r : Nat} (ws : List Sig) (hn : ws.Nodup)
    (budget : k-t+1≤ws.length+r) (run : Live T k t ws.toFinset) :
    ∃ (F : (Fin ws.length → Bool) → Bool), Nonempty (RankBase.Grouping r F) ∧
      (∀ x : Fin 512, F (fun i => (ws.get i).getLsbD x.val) = T.getLsbD x.val) ∧
      (t=0 → Monotone F) := by
  obtain ⟨gs,out,cl,cnt,sz,live,distinct,ok⟩ := realizeRank ws hn run
  let F := fun x : Fin ws.length → Bool => vl gs x out.val
  have limit := RankBase.forkBudget cl out live (cnt ▸ budget)
  obtain ⟨label,loc,codes⟩ := RankBase.rankCuts cl out live limit
  refine ⟨F,⟨⟨label,fun i j h => RankBase.generalConflict cl out live distinct (i,j) ((loc i j).mp h),codes⟩⟩,ok,?_⟩
  intro tz x y xy
  have total := RankBase.nonNotCount_add_notCount gs
  have zero : gs.countP (fun g => isNotGate g.op)=0 := by
    rw [←List.countP_eq_length_filter] at total
    omega
  have pos (g : Gate) (hg : g∈gs) : g.op=.and ∨ g.op=.or := by
    have neg := List.countP_eq_zero.mp zero g hg
    obtain ⟨i,hi,eq⟩ := List.getElem_of_mem hg
    have atSlot : gs[i]?=some g := by simp [List.getElem?_eq_getElem hi,eq]
    rcases cl i g atSlot with ⟨op,_⟩|⟨op,_⟩
    · simp [op,isNotGate] at neg
    · exact op
  apply increasingRun gs pos _ _ (by simp)
  intro i
  by_cases hi : i<ws.length
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem,hi] using xy ⟨i,hi⟩
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]

end FromFrontier

private theorem signed_bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

private lemma signed_live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma signed_live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
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


def Limited (T : Sig) (cap budget : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → t ≤ budget → ¬Live T k t S

def remainder (budget op : Nat) := budget - (if op=2 then 1 else 0)

theorem enum_signed {T : Sig} {cap budget : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : 0 < budget → ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Limited T (cap-1) (budget-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Limited T (cap-1) budget (childTwo ws a b d ka kb).toFinset) :
    Limited T cap budget ws.toFinset := by
  classical
  intro k t hk hnots h
  generalize he : ws.toFinset = S at h
  cases h with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := signed_live_proper tail _ (Finset.mem_insert_self _ _)
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
    have sc := (signed_live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep (by omega) a am keep fresh hz len k t (by omega) (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := signed_live_proper tail _ (Finset.mem_insert_self _ _)
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
    have sc := (signed_live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) hnots (eq.symm ▸ tail)

abbrev SignedLinks :=
  (Nat → Nat → List (List Sig)) × ExtraCut × (Nat → List Sig → Bool)

def closeSigned (pools : List BoundPool) (links : SignedLinks) (k budget : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op :: rest
  pools.any (fun p => scalarPoolCut p k rest op) ||
    (links.1 budget (keySet ws)).any (sameWords ws) ||
    links.2.1 k ws || links.2.2 budget ws

theorem closeSigned_sound {raw T pools} {links : SignedLinks} {k budget rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links.1 budget tag → Limited T k budget (List.toFinset xs))
    (cutValid : ∀ ws : List Sig, ws.Nodup → links.2.1 k ws = true → Impossible T k ws.toFinset)
    (orientValid : ∀ ws : List Sig, links.2.2 budget ws = true → Limited T k budget ws.toFinset)
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeSigned pools links k budget rest op = true) :
    Limited T k budget (choiceVal op :: rest).toFinset := by
  simp only [closeSigned,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ((⟨p,hp,ok⟩ | ⟨xs,hx,ok⟩) | cut) | orient
  · intro m t hm _
    exact scalarPoolCut_sound (pValid _ hp) nd ok m t hm
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · intro m t hm _
    exact cutValid _ nd cut m t hm
  · exact orientValid _ orient

abbrev SignedContext := Nat × Nat × Nat × List Decor × CovPair × List BoundPool × SignedLinks
def evalSigned (c : SignedContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,budget,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if (op==2 && budget==0) || decide (len>cap) then true else
    let d := (len==cap) || (remainder budget op==0)
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeSigned pools links (cap-1) (remainder budget op) rest (movedChoice op a b)

theorem evalSigned_sound {raw T r s ws pools} {links : SignedLinks} {cap budget a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (allows : op=2 → 0<budget)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links.1 (remainder budget op) tag →
      Limited T (cap-1) (remainder budget op) (List.toFinset xs))
    (cv : ∀ words : List Sig, words.Nodup → links.2.1 (cap-1) words = true → Impossible T (cap-1) words.toFinset)
    (ov : ∀ words : List Sig, links.2.2 (remainder budget op) words = true →
       Limited T (cap-1) (remainder budget op) words.toFinset)
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalSigned (cap,budget,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    Limited T (cap-1) (remainder budget op) (moveFront ws op a b ka kb).toFinset := by
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
  intro k t hk nt h
  have hsz := (signed_live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalSigned at test
  have validMove : (op==2 && budget==0) = false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    simp only [Bool.and_eq_true,beq_iff_eq] at yes
    exact (Nat.ne_of_gt (allows yes.1)) yes.2
  change (if (op==2 && budget==0) || decide (1+(ws.length-_ - _) > cap) then true else _) = true at test
  rw [leq,validMove] at test
  simp only [Bool.false_or, decide_eq_false (show ¬ child.length > cap by omega), Bool.false_eq_true, ite_false] at test
  let d := (child.length==cap) || (remainder budget op==0)
  have sep := cover_sound h rfl (pair_sep pairs) d (by
    intro hd
    change (child.length==cap || remainder budget op==0) = true at hd
    simp only [Bool.or_eq_true,beq_iff_eq] at hd
    rcases hd with equal | exhausted <;> omega)
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
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
  exact closeSigned_sound pv lv cv ov nd' test k t hk nt h


def signedPair (ctx : SignedContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalSigned ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def signedRow (ctx : SignedContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  evalSigned ctx 2 a a z false false && evalSigned ctx 2 a a z true true &&
    bs.all (fun b => signedPair ctx a b false && signedPair ctx a b true)
def signedAll (ctx : SignedContext) : List Decor → Bool
  | [] => true
  | a::bs => signedRow ctx a bs && signedAll ctx bs

theorem signed_unary {ctx ws} (h : signedAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalSigned ctx 2 a a (movedDecor 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [signedAll,Bool.and_eq_true,signedRow] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem signed_binary {ctx ws} (h : signedAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : signedPair ctx a b d=true ∨ signedPair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [signedAll,Bool.and_eq_true,signedRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail

theorem signedPair_at {ctx a b d} (h : signedPair ctx a b d = true) (ka kb : Bool) :
    evalSigned ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [signedPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem nodeSigned_sound {raw T r s ws pools} {links : SignedLinks} {cap budget}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ b tag xs, xs ∈ links.1 b tag → Limited T (cap-1) b (List.toFinset xs))
    (cv : ∀ words : List Sig, words.Nodup → links.2.1 (cap-1) words = true → Impossible T (cap-1) words.toFinset)
    (ov : ∀ b words, links.2.2 b words = true → Limited T (cap-1) b words.toFinset)
    (checks : signedAll (cap,budget,ws.length,ws,preCov ws,pools,links) ws = true) :
    Limited T cap budget (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk _ h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    cases h
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_signed nd out
  · intro hb v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact evalSigned_sound (op:=2) pairs faith nd ha ha (by simp) hc' (fun _ => hb) pv
      (lv _) cv (ov _) pro fresh (signed_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : signedPair (cap,budget,ws.length,ws,preCov ws,pools,links) a b d = true) :
        Limited T (cap-1) budget (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      have hstay : remainder budget (if d then 1 else 0) = budget := by cases d <;> simp [remainder]
      rw [← hstay]
      exact evalSigned_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc'
        (by cases d <;> simp) pv (lv _) cv (ov _) (eq ▸ pr) (eq ▸ fr) (signedPair_at test ka kb)
    rcases signed_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (signed_bin_comm d a.1 b.1 ▸ pro)
        (signed_bin_comm d a.1 b.1 ▸ fresh) hh

theorem rotateLimited {T n budget} {ws : List Sig} (hi : Limited T n budget ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Limited T n budget (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk ht h
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
  exact hi k t hk ht run

structure SignedForest where
  base : Forest
  budget : Nat → Nat → Nat
  orientedPairs : List (Row × Row)

def signedLinked (g : SignedForest) (k budget : Nat) (p : Nat × Nat) : Option (List Sig) :=
  if g.budget k p.1 = budget then linkedSet g.base k p else none

theorem signedLinked_sound (g : SignedForest) (k budget : Nat)
    (names : ∀ x ∈ g.base.autos.toList, autoOK (targetOf g.base) (x.map swapRows) = true)
    (earlier : ∀ i < (g.base.levels k).1,
      Limited (targetOf g.base) k (g.budget k i) (stateSet g.base k i).toFinset)
    {p out} (h : signedLinked g k budget p = some out) :
    Limited (targetOf g.base) k budget out.toFinset := by
  unfold signedLinked at h
  split at h
  next sb =>
    unfold linkedSet at h
    split at h
    · contradiction
    next valid =>
      cases ep : g.base.autos[p.2]? with
      | none => simp [ep] at h
      | some perm =>
        simp only [ep, Option.map_some, Option.some.injEq] at h
        subst out
        rw [← sb]
        exact rotateLimited (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? ep))
  next _ => contradiction

def orientedPairsOK (g : SignedForest) :=
  g.orientedPairs.all fun (p,n) => bit p (targetOf g.base) && !(bit n (targetOf g.base))

def orientedExcluded (g : SignedForest) (budget : Nat) (ws : List Sig) :=
  (budget == 0) && g.orientedPairs.any fun (p,n) =>
    ws.all fun sig => !(bit p sig) || bit n sig

theorem orientedExcluded_sound (g : SignedForest) (good : orientedPairsOK g = true)
    {cap budget ws} (he : orientedExcluded g budget ws = true) :
    Limited (targetOf g.base) cap budget ws.toFinset := by
  simp only [orientedExcluded, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at he
  obtain ⟨zeroBudget,⟨⟨p,n⟩,mem,bad⟩⟩ := he
  intro k t hk ht live
  have pair := List.all_eq_true.mp good (p,n) mem
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at pair
  obtain ⟨sig,has,yes,no⟩ := mono_row_difference live (by omega) pair.1 pair.2
  have h := List.all_eq_true.mp bad sig (List.mem_toFinset.mp has)
  simp [yes,no] at h

def stateSigned (g : SignedForest) (k i : Nat) : SignedContext :=
  let c := contextOf g.base k i
  let ref := fun budget tag =>
    ((g.base.index k (2*tag+budget)).bind (signedLinked g (k-1) budget)).toList
  (k,g.budget k i,c.2.2.1.length,c.2.2.1,preCov c.2.2.1,c.2.2.2.2.1,ref,g.base.cut,orientedExcluded g)

def nodeSignedVerified (g : SignedForest) (k i : Nat) :=
  prelim (targetOf g.base) (contextOf g.base k i) &&
    (if k=0 then true else signedAll (stateSigned g k i) (contextOf g.base k i).2.2.1)

theorem nodeSignedVerified_sound (g : SignedForest) (k i : Nat)
    (samples : properPairs (targetOf g.base) (asRow fun j => (g.base.samples j).1)
      (asRow fun j => (g.base.samples j).2))
    (cols : ∀ ci ∈ g.base.cols.values,
      Slice (vars g.base.mask) (targetOf g.base) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.base.autos.toList, autoOK (targetOf g.base) (x.map swapRows) = true)
    (pairs : orientedPairsOK g = true)
    (prior : k>0 → ∀ j < (g.base.levels (k-1)).1,
      Limited (targetOf g.base) (k-1) (g.budget (k-1) j) (stateSet g.base (k-1) j).toFinset)
    (checked : nodeSignedVerified g k i = true) :
    Limited (targetOf g.base) k (g.budget k i) (stateSet g.base k i).toFinset := by
  simp only [nodeSignedVerified, prelim, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g.base ∉ stateSet g.base k i := of_decide_eq_false checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t b ht _ h
    have hb : t=0 := by omega
    subst t
    generalize he : (stateSet g.base 0 i).toFinset = S at h
    cases h
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  apply nodeSigned_sound (raw:=vars g.base.mask) samples _ hN hT _ _
    (g.base.cut_sound _) (fun _ _ h => orientedExcluded_sound g pairs h)
    (by
      have good := checked.2
      rw [ite_eq_right h0] at good
      exact good)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g.base) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g.base cols h
  · intro budget tag xs hx
    have e : ((g.base.index k (2*tag+budget)).bind (signedLinked g (k-1) budget))=some xs := by
      simpa using hx
    obtain ⟨p,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact signedLinked_sound g _ _ names (prior (by omega)) h



abbrev FrontierTest := Sig → Bool → List Sig → Nat → Nat → Nat → Bool

def frontierTestOK (test : FrontierTest) : Prop :=
  ∀ T mono ws r k i (F : (Fin ws.length → Bool) → Bool),
    (∀ x : Fin 512, F (fun j => (ws.get j).getLsbD x.val) = T.getLsbD x.val) →
    (mono=true → Monotone F) → RankBase.Grouping r F → test T mono ws r k i=true → False

def rankNode (test : FrontierTest) (g : SignedForest) (k i : Nat) : Bool :=
  let ws := stateSet g.base k i
  let T := targetOf g.base
  decide ws.Nodup && decide (g.budget k i ≤ 1) &&
    test T true ws (k+1-ws.length) k i &&
    (g.budget k i == 0 || decide (k<ws.length) || test T false ws (k-ws.length) k i)

theorem rankNode_sound (test : FrontierTest) (ok : frontierTestOK test)
    (g : SignedForest) (k i : Nat) (checked : rankNode test g k i=true) :
    Limited (targetOf g.base) k (g.budget k i) (stateSet g.base k i).toFinset := by
  let ws := stateSet g.base k i
  simp only [rankNode,Bool.and_eq_true,decide_eq_true_eq,Bool.or_eq_true,beq_iff_eq] at checked
  obtain ⟨⟨⟨unique,one⟩,monoOK⟩,signedOK⟩ := checked
  intro a t ak tb run
  have ht := (signed_live_size run).1
  have size := (signed_live_size run).2
  rw [List.toFinset_card_of_nodup unique] at size
  change ws.length + t ≤ a+1 at size
  by_cases noNot : t=0
  · obtain ⟨F,⟨gr⟩,ag,mon⟩ := FromFrontier.groupFromLive ws unique
      (r:=k+1-ws.length) (by omega : a-t+1≤ws.length+(k+1-ws.length)) run
    exact ok _ true _ _ _ _ F ag (fun _ => mon noNot) gr monoOK
  · obtain (zero|tooLarge)|okSigned := signedOK
    · omega
    · change k<ws.length at tooLarge
      omega
    · obtain ⟨F,⟨gr⟩,ag,mon⟩ := FromFrontier.groupFromLive ws unique
        (r:=k-ws.length) (by omega : a-t+1≤ws.length+(k-ws.length)) run
      exact ok _ false _ _ _ _ F ag (by simp) gr okSigned

def hybridNode (test : FrontierTest) (count : Nat → Nat) (g : SignedForest) (k i : Nat) :=
  if i<count k then rankNode test g k i else nodeSignedVerified g k i
def hybridBlock (test : FrontierTest) (count : Nat → Nat) (g : SignedForest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => hybridNode test count g k (start+n) && hybridBlock test count g k start n

theorem hybridBlock_at {test count g k start n} (h : hybridBlock test count g k start n = true) (j : Nat)
    (lo : start ≤ j) (hi : j < start+n) : hybridNode test count g k j = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [hybridBlock, Bool.and_eq_true] at h
    by_cases eq : j = start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem hybridBlock_merge {test count g k start a b} (h : hybridBlock test count g k start a = true)
    (h' : hybridBlock test count g k (start+a) b = true) : hybridBlock test count g k start (a+b) = true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [hybridBlock, Bool.and_eq_true] at h'
    simp only [Nat.add_succ, hybridBlock, Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1, ih h'.2⟩


def hybridTables (test : FrontierTest) (count : Nat → Nat) (g : SignedForest) (top : Nat) :=
  ∀ k ≤ top, hybridBlock test count g k 0 (g.base.levels k).1 = true

theorem hybridForest_all (test : FrontierTest) (sound : frontierTestOK test) (count : Nat → Nat)
    (g : SignedForest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g.base prior = true) (pairs : orientedPairsOK g = true)
    (rows : hybridTables test count g top) :
    ∀ k ≤ top, ∀ i < (g.base.levels k).1,
      Limited (targetOf g.base) k (g.budget k i) (stateSet g.base k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk i hi
    have checked := hybridBlock_at (rows k hk) i (by omega) (by omega)
    unfold hybridNode at checked
    split at checked
    · exact rankNode_sound test sound g k i checked
    · apply nodeSignedVerified_sound g k i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 pairs _ checked
      intro pos
      exact ih (k-1) (by omega) (by omega)

private lemma cutLiveSize {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
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

private lemma cutBitBin (i : Row) (d : Bool) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]
private lemma cutBitNeg (i : Row) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
def Sensitive (T : Sig) (S : Finset Sig) (r : Row) (v : Sig) : Prop :=
  ∃ s, bit r T ≠ bit s T ∧ ∀ u ∈ S, u ≠ v → bit r u = bit s u

def Pivot (T : Sig) (S : Finset Sig) (r s : Row) (v : Sig) : Prop :=
  Sensitive T S r v ∧ Sensitive T S s v

private theorem sensitive_mem (l : Live T k t S) (h : Sensitive T S r v) : v∈S := by
  rcases h with ⟨s,d,h⟩
  obtain ⟨u,hu,hd⟩ := live_row_difference l d
  by_contra z
  exact hd (h _ hu (fun e => z (e ▸ hu)))

private theorem sensitive_unary (az : a∉U) (h : Sensitive T (insert a U) r v) :
    Sensitive T (insert (neg a) U) r (if v=a then neg a else v) := by
  rcases h with ⟨s,hd,hn⟩
  refine ⟨s,hd,?_⟩
  intro u hu ne
  rcases Finset.mem_insert.mp hu with rfl|hu
  · by_cases eq : v=a
    · simp [eq] at ne
    · rw [cutBitNeg,cutBitNeg,hn _ (by simp) (Ne.symm eq)]
  · apply hn _ (Finset.mem_insert_of_mem hu)
    intro e
    subst u
    by_cases eq : v=a
    · exact az (eq ▸ hu)
    · simp [eq] at ne

private theorem sensitive_binary (az : a∉U) (bz : b∉U)
    (h : Sensitive T (insert a (insert b U)) r v) :
    Sensitive T (insert (bin d a b) U) r (if v=a ∨ v=b then bin d a b else v) := by
  rcases h with ⟨s,hd,hn⟩
  refine ⟨s,hd,?_⟩
  intro u hu ne
  rcases Finset.mem_insert.mp hu with rfl|hu
  · by_cases eq : v=a ∨ v=b
    · simp [eq] at ne
    · rw [cutBitBin,cutBitBin,hn a (by simp) (fun e => eq (.inl e.symm)),
        hn b (by simp) (fun e => eq (.inr e.symm))]
  · apply hn _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu))
    intro e
    subst u
    by_cases eq : v=a ∨ v=b
    · rcases eq with e|e
      · exact az (e ▸ hu)
      · exact bz (e ▸ hu)
    · simp [eq] at ne

private theorem sensitive_pass {g a b : Sig} {d : Bool} (az : a∉U) (ab : a≠b)
    (law : ∀ r, bit r g = (if d then bit r a || bit r b else bit r a && bit r b))
    (l : Live T k t (insert g U)) (h : Sensitive T (insert a (insert b U)) r a) :
    bit r b = !d ∧ bit r g = bit r a := by
  rcases h with ⟨s,hd,hn⟩
  obtain ⟨u,hu,uh⟩ := live_row_difference l hd
  rcases Finset.mem_insert.mp hu with rfl | hu
  · have eq := hn b (by simp) ab.symm
    rw [law,law] at uh
    rw [law,←eq] at *
    all_goals cases d <;> cases a' : bit r a <;> cases b' : bit r b <;>
      cases c' : bit s a <;> simp_all
  · exact (uh (hn _ (by simp [hu]) (fun e => az (e ▸ hu)))).elim

private theorem two_split {U : Finset Sig} {i j a b : Sig} {d : Bool}
    (az : a∉U) (bz : b∉U) (ab : a≠b) (hf : bin d a b ∉ insert a (insert b U)) (l : Live T k t (insert (bin d a b) U))
    (p : Pivot T (insert a (insert b U)) r s i)
    (q : Pivot T (insert a (insert b U)) r s j)
    (hi : bit r i ≠ bit s i) (hj : bit r j ≠ bit s j) (ne : i≠j) :
    ∃ i' j', Pivot T (insert (bin d a b) U) r s i' ∧ Pivot T (insert (bin d a b) U) r s j' ∧
      bit r i' ≠ bit s i' ∧ bit r j' ≠ bit s j' ∧ i'≠j' := by
  let f (v : Sig) := if v=a ∨ v=b then bin d a b else v
  have lift {v} (pv : Pivot T (insert a (insert b U)) r s v) :
       Pivot T (insert (bin d a b) U) r s (f v) :=
    ⟨sensitive_binary az bz pv.1,sensitive_binary az bz pv.2⟩
  have passA {row} (pv : Sensitive T (insert a (insert b U)) row a) :=
    sensitive_pass az ab (d:=d) (fun i => cutBitBin i d a b) l pv
  have passB {row} (pv : Sensitive T (insert a (insert b U)) row b) :
      bit row a = !d ∧ bit row (bin d a b) = bit row b := by
    apply sensitive_pass bz ab.symm (d:=d) (fun i => ?_) l
    · simpa [Finset.insert_comm] using pv
    · rw [cutBitBin]; cases d <;> simp [Bool.and_comm,Bool.or_comm]
  have val {v} (pv : Pivot T (insert a (insert b U)) r s v) :
      bit r (f v)=bit r v ∧ bit s (f v)=bit s v := by
    by_cases eq : v=a ∨ v=b
    · simp only [f,ite_eq_left eq]
      rcases eq with rfl|rfl
      · exact ⟨(passA pv.1).2,(passA pv.2).2⟩
      · exact ⟨(passB pv.1).2,(passB pv.2).2⟩
    · simp [f,eq]
  have fresh {v} (pv : Pivot T (insert a (insert b U)) r s v) (h : ¬(v=a ∨ v=b))
      (fv : v=bin d a b) (hf : bin d a b ∉ insert a (insert b U)) : False := by
    subst v
    obtain ⟨row,hd,ex⟩ := pv.1
    obtain ⟨u,hu,uh⟩ := live_row_difference l hd
    rcases Finset.mem_insert.mp hu with rfl | hu
    · rw [cutBitBin,cutBitBin,ex a (by simp) (fun e => h (.inl e.symm)),
        ex b (by simp) (fun e => h (.inr e.symm))] at uh
      exact uh rfl
    · exact uh (ex _ (by simp [hu]) (fun e => hf (e ▸ (by simp [hu]))))
  refine ⟨f i,f j,lift p,lift q,by rwa [(val p).1,(val p).2],by rwa [(val q).1,(val q).2],?_⟩
  by_cases ei : i=a ∨ i=b <;> by_cases ej : j=a ∨ j=b
  · rcases ei with rfl|rfl <;> rcases ej with rfl|rfl
    · contradiction
    · exact (hj ((passA p.1).1.trans (passA p.2).1.symm)).elim
    · exact (hj ((passB p.1).1.trans (passB p.2).1.symm)).elim
    · contradiction
  · simp only [f,ite_eq_left ei,ite_eq_right ej]
    intro e
    exact fresh q ej e.symm hf
  · simp only [f,ite_eq_right ei,ite_eq_left ej]
    intro e
    exact fresh p ei e hf
  · simpa [f,ei,ej] using ne

theorem tight_no_conflict {T k t S} (l : Live T k t S) (tight : k+1≤S.card+t)
    {r s i j} (p : Pivot T S r s i) (q : Pivot T S r s j)
    (hi : bit r i ≠ bit s i) (hj : bit r j ≠ bit s j) (ne : i≠j) : False := by
  induction l generalizing i j with
  | stop hp =>
    have mem := sensitive_mem (Live.stop hp) p.1
    have mem' := sensitive_mem (Live.stop hp) q.1
    simp only [Finset.mem_singleton] at mem mem'
    exact ne (mem.trans mem'.symm)
  | @unary k t U a ha hf tail ih =>
    have hfU : neg a ∉ U := fun h => hf (by simp [h])
    have size := (cutLiveSize tail).2
    rw [Finset.card_insert_of_notMem hfU] at size
    have az : a ∉ U := by
      intro hal
      rw [Finset.insert_eq_of_mem hal] at tight
      omega
    rw [Finset.card_insert_of_notMem az] at tight
    have next : k+1 ≤ (insert (neg a) U).card+t := by
      rw [Finset.card_insert_of_notMem hfU]; omega
    let f (v : Sig) := if v=a then neg a else v
    have lift {v} (pv : Pivot T (insert a U) r s v) :
        Pivot T (insert (neg a) U) r s (f v) := ⟨sensitive_unary az pv.1,sensitive_unary az pv.2⟩
    have dv {v} (dd : bit r v ≠ bit s v) : bit r (f v) ≠ bit s (f v) := by
      by_cases e : v=a
      · subst v; simpa [f,cutBitNeg] using dd
      · simpa [f,e] using dd
    apply ih next (lift p) (lift q) (dv hi) (dv hj)
    have mi := sensitive_mem (.unary ha hf tail) p.1
    have mj := sensitive_mem (.unary ha hf tail) q.1
    by_cases ei : i=a <;> by_cases ej : j=a
    · exact (ne (ei.trans ej.symm)).elim
    · simp only [f,ite_eq_left ei,ite_eq_right ej]
      exact fun e => hf (e ▸ mj)
    · simp only [f,ite_eq_right ei,ite_eq_left ej]
      exact fun e => hf (e ▸ mi)
    · simpa [f,ei,ej] using ne
  | @binary k t U a b d ha hb ab hf tail ih =>
    have hfU : bin d a b ∉ U := fun h => hf (by simp [h])
    have size := (cutLiveSize tail).2
    rw [Finset.card_insert_of_notMem hfU] at size
    have lim := Finset.card_insert_le (a:=a) (s:=insert b U)
    have bl := Finset.card_insert_le (a:=b) (s:=U)
    have bz : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight lim
      omega
    have az : a∉insert b U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight
      omega
    rw [Finset.card_insert_of_notMem az,Finset.card_insert_of_notMem bz] at tight
    have next : k+1 ≤ (insert (bin d a b) U).card+t := by
      rw [Finset.card_insert_of_notMem hfU]; omega
    obtain ⟨i',j',pi,pj,ii,jj,z⟩ := two_split (fun hm => az (by simp [hm])) bz ab hf tail p q hi hj ne
    exact ih next pi pj ii jj z

theorem tight_no_binate {T k t S} (l : Live T k t S) (tight : k+1≤S.card+t)
    {r s i} (p : Pivot T S r s i) (hi : bit r i = bit s i) (goal : bit r T ≠ bit s T) : False := by
  induction l generalizing i with
  | stop hp =>
    have mi := sensitive_mem (Live.stop hp) p.1
    simp only [Finset.mem_singleton] at mi
    exact goal (mi ▸ hi)
  | @unary k t U a ha hf tail ih =>
    have hfU : neg a ∉ U := fun h => hf (by simp [h])
    have size := (cutLiveSize tail).2
    rw [Finset.card_insert_of_notMem hfU] at size
    have az : a ∉ U := by
      intro hal
      rw [Finset.insert_eq_of_mem hal] at tight
      omega
    rw [Finset.card_insert_of_notMem az] at tight
    have next : k+1 ≤ (insert (neg a) U).card+t := by
      rw [Finset.card_insert_of_notMem hfU]; omega
    let f (v : Sig) := if v=a then neg a else v
    have lift {v} (pv : Pivot T (insert a U) r s v) :
        Pivot T (insert (neg a) U) r s (f v) := ⟨sensitive_unary az pv.1,sensitive_unary az pv.2⟩
    have dv {v} (dd : bit r v = bit s v) : bit r (f v) = bit s (f v) := by
      by_cases e : v=a
      · subst v; simpa [f,cutBitNeg] using dd
      · simpa [f,e] using dd
    exact ih next (lift p) (dv hi)
  | @binary k t U a b d ha hb ab hf tail ih =>
    have hfU : bin d a b ∉ U := fun h => hf (by simp [h])
    have size := (cutLiveSize tail).2
    rw [Finset.card_insert_of_notMem hfU] at size
    have lim := Finset.card_insert_le (a:=a) (s:=insert b U)
    have bl := Finset.card_insert_le (a:=b) (s:=U)
    have bz : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight lim
      omega
    have az : a∉insert b U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight
      omega
    rw [Finset.card_insert_of_notMem az,Finset.card_insert_of_notMem bz] at tight
    have next : k+1 ≤ (insert (bin d a b) U).card+t := by
      rw [Finset.card_insert_of_notMem hfU]; omega
    have nz : a∉U := fun h => az (Finset.mem_insert_of_mem h)
    let f (v : Sig) := if v=a ∨ v=b then bin d a b else v
    have lift : Pivot T (insert (bin d a b) U) r s (f i) :=
      ⟨sensitive_binary nz bz p.1,sensitive_binary nz bz p.2⟩
    apply ih next lift
    by_cases eq : i=a ∨ i=b
    · simp only [f,ite_eq_left eq]
      rcases eq with e|e
      · subst i
        have pick {row} (pv : Sensitive T (insert a (insert b U)) row a) :=
          (sensitive_pass nz ab (d:=d) (fun j => cutBitBin j d a b) tail pv).2
        exact (pick p.1).trans (hi.trans (pick p.2).symm)
      · subst i
        have law (row : Row) : bit row (bin d a b) =
            (if d then bit row b || bit row a else bit row b && bit row a) := by
          rw [cutBitBin]; cases d <;> simp [Bool.and_comm,Bool.or_comm]
        have pick {row} (pv : Sensitive T (insert a (insert b U)) row b) :=
          (sensitive_pass bz ab.symm law tail (by simpa [Finset.insert_comm] using pv)).2
        exact (pick p.1).trans (hi.trans (pick p.2).symm)
    · simpa [f,eq] using hi

namespace RootFloor

def rootRules9 : Nat × Nat := (0x4e00468704e00458704d04028708a090f8604d00487604e00257604e10027604d0201760d0014f85114050f7504e00186504d00276504e08016504e00168404e00138404d04008404e00857404d02037404e00127404d00407404e00186404d00236404e00816404d10006404e00875404d08035404e0080540d0082f8304e01057304d02047304e01027304d00286304d00246304e01016304d00185304e01075304d08045304d00125304e0040531810c0f4304d04078204e08068204e00258204e00238204d020182068110f7204e08086204d10076204e00816204e00285204d00175204d00135204d10015204e00805204d00174204d00134204e080042192060f3204e00168104e00458104e00138104d02028104d00808104d02067104e04057104e001271181090f6104e00485104e04075104d08065104d10025104e00405104d00864104e04034104e00404104e00183104d01063104e04043104e00123104d100031181110f2104e01068004e00258004d04048004e00238004d00818004e00257004d00447004e01027004e01086004d10046004e010160192048f5008a180f4004e00283004d00453004e00243004e02023004d10013004e01072004d00852004d08042004e02032004d008120114180f10,105)
def rootRules10 : Nat × Nat := (0x4e20568704e00458704d24028704e20138604d20587604e3012762d0014f85305250f7504e20186504e20168404d02038404d24008404e00857404d02037404e20127404d24407404e20186404e00875404d08035404e2480542d0281f8304e01057304d02047304e01027304e20586304e00485304e01075304d08045304d20125304e2440533812c0f4304d24078204e28168204e00258204e00238204d020182268301f7204e28186204d30176204e00285204e00275204d20135204d10015204e24805204d20174204e00234204e2c0042381260f3204e20168104e00458104e20138104d02028104e24057104d02027104e20186104e00485104e24075104d10025104e24005104e24034104e24004104e20183104e24043104d010231381110f2104d24058004d24048004d24457004d24447004e2502702d0248f502682c0f4004d24453004d24443004e26023004e25072004d24852004d2c042004e26032004d24051004d240410,81)

end RootFloor

namespace RootFloor

def augmented := inputs ++ [bin true (inputs.getD 0 zero) (inputs.getD 6 zero)]

theorem rawInputsNoDup : inputs.Nodup := by decide +kernel
theorem augmentedNoDup : augmented.Nodup := by decide +kernel
theorem rawInputsLength : inputs.length = 9 := by decide +kernel
theorem augmentedLength : augmented.length = 10 := by decide +kernel

open FrontRanks

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem rootRules9Checked : rankCheck graph false inputs 4 (readRules inputs.length rootRules9.2 rootRules9.1) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem rootRules10Checked : rankCheck graph false augmented 3 (readRules augmented.length rootRules10.2 rootRules10.1) = true := by decide +kernel

theorem signedAtMostOneBare {k t} (budget : k ≤ 14) (run : Live graph k t inputs.toFinset) : t ≤ 1 := by
  by_contra! excess
  have ranks : k-t+1 ≤ inputs.length+4 := by rw [rawInputsLength]; omega
  obtain ⟨F,⟨g⟩,agree,_⟩ := FromFrontier.groupFromLive inputs rawInputsNoDup ranks run
  exact rankCheck_sound F agree (by intro h; cases h) g rootRules9Checked

theorem signedAtMostOneSeeded {k t} (budget : k ≤ 14) (run : Live graph k t augmented.toFinset) : t ≤ 1 := by
  by_contra! excess
  have ranks : k-t+1 ≤ augmented.length+3 := by rw [augmentedLength]; omega
  obtain ⟨F,⟨g⟩,agree,_⟩ := FromFrontier.groupFromLive augmented augmentedNoDup ranks run
  exact rankCheck_sound F agree (by intro h; cases h) g rootRules10Checked

end RootFloor

namespace O1677

structure Six3640 where
  p : Row
  n : Row
  ni : Row
  pi : Row
  nj : Row
  pj : Row

def invRows3640 : List (Row × Row) := [(320,257),(264,257),(132,129),(416,385),(176,400),(17,80),(82,50),(273,274),(160,192),(448,386),(404,402),(304,276),(44,100),(152,400),(197,201),(160,136),(28,52),(120,116),(131,386),(76,104),(6,10),(14,42),(168,138),(12,72),(262,261),(152,146),(292,261),(304,274),(304,50),(132,384)]
def sixRows3640 : List Six3640 := [⟨85,104,69,120,84,105⟩,⟨148,50,144,54,20,178⟩,⟨308,69,52,325,276,101⟩,⟨154,385,146,393,138,401⟩,⟨232,69,200,101,104,197⟩,⟨278,208,276,210,274,212⟩,⟨265,69,257,77,9,325⟩,⟨306,208,50,464,274,240⟩,⟨120,69,112,77,104,85⟩,⟨194,385,192,387,130,449⟩,⟨38,104,36,106,34,108⟩,⟨389,104,385,108,261,232⟩,⟨262,385,260,387,258,389⟩,⟨101,208,100,209,69,240⟩,⟨13,385,9,389,5,393⟩,⟨321,42,257,106,65,298⟩,⟨44,50,40,54,36,58⟩,⟨290,138,34,394,258,170⟩,⟨259,276,258,277,257,278⟩,⟨266,50,258,58,10,306⟩,⟨133,34,129,38,5,162⟩,⟨176,276,144,308,48,404⟩,⟨37,276,36,277,5,308⟩,⟨387,208,386,209,385,210⟩,⟨66,276,64,278,2,340⟩,⟨21,40,5,56,20,41⟩,⟨98,260,96,262,34,324⟩]

def inversion3640 (ws : List Sig) (rn : Row × Row) : Bool :=
  ws.all fun w => !bit rn.1 w || bit rn.2 w

def deviates3640 (p n r s : Row) (w : Sig) : Bool :=
  (bit p w != bit r w) || (bit n w != bit s w)

def pick3640 (ws : List Sig) (p n r s : Row) : Option Sig :=
  match ws.filter (deviates3640 p n r s) with
  | [w] => if (bit p w != bit r w) && (bit n w != bit s w) then some w else none
  | _ => none

def pairCut3640 (p n : Row) (a b : Option Sig) : Bool :=
  match a,b with
  | some u,some v => (bit p u == bit n u) || (bit p v == bit n v) || (u != v)
  | some u,none => bit p u == bit n u
  | none,some v => bit p v == bit n v
  | none,none => false

def sixCut3640 (ws : List Sig) (s : Six3640) : Bool :=
  pairCut3640 s.p s.n (pick3640 ws s.p s.n s.ni s.pi) (pick3640 ws s.p s.n s.nj s.pj)

def shapeCut3640 (k : Nat) (ws : List Sig) : Bool :=
  (k+1 ≤ ws.length || (k == ws.length && invRows3640.any (inversion3640 ws))) &&
    sixRows3640.any (sixCut3640 ws)

def sixValid3640 (T : Sig) (s : Six3640) : Bool :=
  (bit s.p T != bit s.n T) && (bit s.p T != bit s.ni T) &&
  (bit s.n T != bit s.pi T) && (bit s.p T != bit s.nj T) && (bit s.n T != bit s.pj T)

theorem sixRows3640_valid :
    sixRows3640.all (sixValid3640 (chartGoal 511)) = true := by decide +kernel

theorem invRows3640_valid :
    invRows3640.all (fun rn => bit rn.1 (chartGoal 511) && !bit rn.2 (chartGoal 511)) = true := by
  decide +kernel


private theorem pick_single3640 {ws p n r s v}
    (h : pick3640 ws p n r s = some v) : ws.filter (deviates3640 p n r s) = [v] := by
  unfold pick3640 at h
  split at h
  next w eq =>
    split at h
    · cases h
      exact eq
    · contradiction
  next => contradiction

private theorem pick_pivot3640 {ws p n r s v T}
    (h : pick3640 ws p n r s = some v) (dr : bit p T ≠ bit r T) (ds : bit n T ≠ bit s T) :
    Pivot T ws.toFinset p n v := by
  have good := pick_single3640 h
  have agree (u : Sig) (hu : u ∈ ws.toFinset) (ne : u ≠ v) :
      bit p u = bit r u ∧ bit n u = bit s u := by
    have hd : deviates3640 p n r s u = false := by
      cases e : deviates3640 p n r s u with
      | false => rfl
      | true =>
        have a := List.mem_filter.mpr ⟨List.mem_toFinset.mp hu,e⟩
        rw [good] at a
        exact False.elim (ne (List.mem_singleton.mp a))
    simpa [deviates3640] using hd
  exact ⟨⟨r,dr,fun u hu ne => (agree u hu ne).1⟩,
    ⟨s,ds,fun u hu ne => (agree u hu ne).2⟩⟩

private theorem six_impossible3640 {ws k t T s} (run : Live T k t ws.toFinset)
    (tight : k+1 ≤ ws.toFinset.card+t) (valid : sixValid3640 T s = true)
    (cut : sixCut3640 ws s = true) : False := by
  simp [sixValid3640,and_assoc] at valid
  obtain ⟨diff,dr,ds,er,es⟩ := valid
  let pi := pick3640 ws s.p s.n s.ni s.pi
  let pj := pick3640 ws s.p s.n s.nj s.pj
  change pairCut3640 s.p s.n pi pj = true at cut
  cases hi : pi with
  | none =>
    cases hj : pj with
    | none => simp [pairCut3640,hi,hj] at cut
    | some v =>
      have pv := pick_pivot3640 (v:=v) (show pick3640 ws s.p s.n s.nj s.pj = some v from hj) er es
      exact tight_no_binate run tight pv (by simpa [pairCut3640,hi,hj] using cut) diff
  | some u =>
    have pu := pick_pivot3640 (v:=u) (show pick3640 ws s.p s.n s.ni s.pi = some u from hi) dr ds
    by_cases eu : bit s.p u = bit s.n u
    · exact tight_no_binate run tight pu eu diff
    cases hj : pj with
    | none => simp [pairCut3640,hi,hj,eu] at cut
    | some v =>
      have pv := pick_pivot3640 (v:=v) (show pick3640 ws s.p s.n s.nj s.pj = some v from hj) er es
      by_cases ev : bit s.p v = bit s.n v
      · exact tight_no_binate run tight pv ev diff
      exact tight_no_conflict run tight pu pv eu ev (by simpa [pairCut3640,hi,hj,eu,ev] using cut)

theorem shapeCut3640_sound (k : Nat) (ws : List Sig) (nd : ws.Nodup)
    (cut : shapeCut3640 k ws = true) : Impossible (chartGoal 511) k ws.toFinset := by
  intro j t budget run
  simp only [shapeCut3640, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    beq_iff_eq, List.any_eq_true] at cut
  obtain ⟨room,s,hs,why⟩ := cut
  have tight : j+1 ≤ ws.toFinset.card+t := by
    rw [List.toFinset_card_of_nodup nd]
    rcases room with room|⟨eq,p,hp,inv⟩
    · omega
    · have test := List.all_eq_true.mp invRows3640_valid p hp
      have sign : bit p.1 (chartGoal 511) = true ∧ bit p.2 (chartGoal 511) = false := by simpa using test
      have need : t ≠ 0 := by
        intro zeroNot
        obtain ⟨w,hw,h1,h0⟩ := mono_row_difference run zeroNot sign.1 sign.2
        have wi := List.all_eq_true.mp inv w (List.mem_toFinset.mp hw)
        simp [h1,h0] at wi
      omega
  exact six_impossible3640 run tight (List.all_eq_true.mp sixRows3640_valid s hs) why

def ruleSym3095 (word : Nat → Nat) (tbl tb input : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0,_,_ => (0,0)
  | m+1,base,shift =>
    let pick := (input >>> shift) &&& 3
    let x := packedAt word (tbl+(base*4+pick)*tb) tb
    let advance := x &&& 3
    let val := (x >>> 2)-1
    if advance == 0 then ruleSym3095 word tbl tb input m val (shift+2)
    else (val,shift+advance)

def ruleList3095 (word : Nat → Nat) (tbl tb : Nat) (pos : Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | n+1 =>
    let x := ruleSym3095 word tbl tb (packedAt word pos 20) 10 0 0
    (x.1 &&& 255,x.1 >>> 8)::ruleList3095 word tbl tb (pos+x.2) n

def fixedRules3095 (word : Nat → Nat) (cw pos : Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | n+1 =>
    let z := packedAt word pos cw
    (z &&& 255,z >>> 8)::fixedRules3095 word cw (pos+cw) n

def ruleRead3095 (word : Nat → Nat) (base start a off b tbl tb pi pb cw i : Nat) : List (Nat × Nat) :=
  let pos := packedAt word (start+i / 16 * a) a + packedAt word (off+i*b) b
  let x := ruleSym3095 word tbl tb (packedAt word pos 20) 10 0 0
  if x.1 < base+32 then ruleList3095 word tbl tb (pos+x.2) (x.1-base) else
    let pp := packedAt word (pi+(x.1-base-32)*pb) pb
    fixedRules3095 word cw (pp+5) (packedAt word pp 5)
def signedColumns : IndexTree ColumnInfo := (.fork 58 ((.fork 29 ((.fork 14 ((.fork 7 ((.fork 3 (.leaf [(3,0,508,0,9),(2,1,460,48,7),(5,0,506,0,8)]) ((.fork 2 (.leaf [(6,0,505,0,9),(7,0,504,0,7)]) (.leaf [(5,2,440,64,6),(9,0,486,0,8)]))))) ((.fork 3 (.leaf [(10,0,501,0,8),(12,0,499,0,9),(8,4,369,130,7)]) ((.fork 2 (.leaf [(4,8,227,272,7),(14,0,497,0,7)]) (.leaf [(10,4,369,128,6),(0,16,486,9,10)]))))))) ((.fork 7 ((.fork 3 (.leaf [(17,0,494,0,11),(19,0,492,0,8),(21,2,424,64,5)]) ((.fork 2 (.leaf [(24,0,487,0,11),(8,16,486,1,9)]) (.leaf [(25,0,486,0,8),(9,16,486,0,8)]))))) ((.fork 4 ((.fork 2 (.leaf [(26,4,353,128,5),(32,1,460,18,7)]) (.leaf [(1,32,94,384,7),(35,0,476,0,7)]))) ((.fork 2 (.leaf [(34,1,460,16,6),(36,0,347,0,8)]) (.leaf [(39,0,344,0,4),(40,0,471,0,8)]))))))))) ((.fork 14 ((.fork 7 ((.fork 3 (.leaf [(49,0,462,0,8),(50,1,460,0,5),(56,0,455,0,7)]) ((.fork 2 (.leaf [(0,64,189,258,10),(66,0,445,0,11)]) (.leaf [(2,64,189,256,9),(67,0,444,0,8)]))))) ((.fork 3 (.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5)]) ((.fork 2 (.leaf [(74,4,305,128,5),(80,0,431,0,11)]) (.leaf [(83,0,428,0,7),(96,0,415,0,9)]))))))) ((.fork 7 ((.fork 3 (.leaf [(96,1,396,18,6),(98,1,396,16,5),(132,0,379,0,11)]) ((.fork 2 (.leaf [(4,128,347,32,9),(133,0,378,0,7)]) (.leaf [(134,0,377,0,8),(132,2,312,65,6)]))))) ((.fork 4 ((.fork 2 (.leaf [(133,2,312,64,5),(136,0,375,0,9)]) (.leaf [(140,0,371,0,8),(132,8,99,272,6)]))) ((.fork 2 (.leaf [(144,0,367,0,11),(152,4,353,2,5)]) (.leaf [(160,0,351,0,11),(160,1,332,18,6)]))))))))))) ((.fork 29 ((.fork 14 ((.fork 7 ((.fork 3 (.leaf [(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) ((.fork 2 (.leaf [(172,0,339,0,5),(176,1,332,2,5)]) (.leaf [(192,0,319,0,11),(198,0,313,0,7)]))))) ((.fork 3 (.leaf [(260,0,251,0,8),(264,0,247,0,9),(256,8,227,20,7)]) ((.fork 2 (.leaf [(8,256,151,96,7),(268,0,243,0,7)]) (.leaf [(273,0,238,0,7),(280,0,231,0,8)]))))))) ((.fork 7 ((.fork 3 (.leaf [(276,8,227,0,5),(288,0,223,0,9),(256,32,94,129,7)]) ((.fork 2 (.leaf [(32,256,151,72,7),(257,32,94,128,6)]) (.leaf [(296,0,215,0,7),(40,256,151,64,6)]))))) ((.fork 4 ((.fork 2 (.leaf [(273,32,78,128,5),(56,256,135,64,5)]) (.leaf [(320,0,191,0,11),(256,64,189,2,9)]))) ((.fork 2 (.leaf [(322,0,189,0,8),(258,64,189,0,8)]) (.leaf [(324,0,187,0,7),(324,8,163,16,5)]))))))))) ((.fork 14 ((.fork 7 ((.fork 3 (.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5)]) ((.fork 2 (.leaf [(224,256,23,8,5),(5,16,482,8,6)]) (.leaf [(33,16,454,8,6),(10,64,181,256,6)]))))) ((.fork 3 (.leaf [(80,2,424,5,6),(97,0,414,0,6),(129,0,382,0,9)]) ((.fork 2 (.leaf [(156,0,355,0,7),(129,32,94,256,6)]) (.leaf [(161,0,350,0,8),(40,128,339,4,6)]))))))) ((.fork 7 ((.fork 3 (.leaf [(177,0,334,0,7),(193,0,318,0,7),(257,16,230,8,6)]) ((.fork 2 (.leaf [(289,0,222,0,7),(257,64,188,2,6)]) (.leaf [(321,0,190,0,7),(260,64,185,2,6)]))))) ((.fork 4 ((.fork 2 (.leaf [(72,256,151,32,6),(328,0,183,0,8)]) (.leaf [(336,0,175,0,8),(344,0,167,0,7)]))) ((.fork 2 (.leaf [(384,32,94,1,6),(416,0,95,0,8)]) (.leaf [(448,0,63,0,8),(480,0,31,0,7)]))))))))))))
def rulesWord9 (i : Nat) : Nat := 0x314001600150005934
def spentSigned9 (i : Nat) : Nat := 0x0
def rulesWord10 (i : Nat) : Nat := 0x8062315280623152229a9972229a9972023a0342023a03421112012211120122a1527292a1527292a172002aa172002a21e200ea21e200ea11e200ca11e200ca8b9281528b928152223a0032223a00321b92314a1b92314ad9caa112d9caa112c12230aac12230aa00aa412200aa412240f202aa40f202aae112b112e112b112031a20aa031a20aa80aad11280aad112012ab972012ab97240aa020a40aa020a99ba001499ba028c01a801a00198019001880180017801700168016001580150014801400138010cf11400b402bcf2949292026a9292026a5174c0ad004c034cc07a008ac07a008a02d40a740074d07c914cc2acd97432041a1c01f4024c0a3422ac42ad0014013d003c3292036c329200e401c4d17401d4b07cc9ccd9bc91549204017408dc005c0304212402349114215410ac02dcf204013001280120011800c5001a0145001a0110e07cf07c3114010802c2e97402c2010000f800f000e800e000d800d000c800c000b800b000a8028400fc016400a0016d003200990032009000880080007800700068006000580050004800400039002d002400300029000c002000180010913d18896331084801b6d1626bd3c8d3ddc4c95626904591984c01bed4e12bf2f8d421d4ce56a48fe5b1d08001becd5e2ad3a8cc01c6cd5b268ee5e18080013073a80e8490a048200e06028100602008001e0e06830160a048200e06028100602008001e0e06830160a048200e06028100602008001e0e06830160a048200e06028100602008001e0e06830160a048200e06028100602008001e0e06830160a048200e06028100602008001e0e06830160a048200e06028100602008001e0e06830160a048200e06028100602008001e0e06830160a048200e0602810060200801f6b07c314a6400700c014020030040040000f20d2c75a51853a518e91030a40a3007a5494593d2ac8154f8c9537ed48fc1aebea249f837d44e2a4c73298ea28f227366e55e0a7485871e165a89435ae30e132f8d444b059f6e110d4c370b343152825f38e482aa86d549668836aa4b344d2b3421c02c19555530094950358e10602042300d857003fb8c4ae2a59a2518441927e8ae5ebec31cb96f439cb96f438cabb14fb8cbbd5d0e1e5ed2c393d1ee91a7bb34ece916ec574bb3a26d318994e902dd36399d255d3b064ee911de83bedc5242a28e85ed0e3b477605cb6c936fcf6d6bcdcacab65a73245bb2d0959e6a2cd196c4a6a33232d884de42871a8dc1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def spentSigned10 (i : Nat) : Nat := 0xba31361680088000e14bf04005e040e00008001c000e0000
def linksSigned10 (i : Nat) : Nat := 0xa0800284000004000000c1400c040000000
def rulesWord11 (i : Nat) : Nat := (if i<2 then (if i<1 then 0xb40d7ff71f8065ba3875bb4668c7cbd47c763c05caa3b23e51c3fb4519b8fa45bf4dc9c0f231e89fa1a6f812f8f963e9faa868fdb47473fed51e9d6d51dcd39fb5b3973ff0a3d3ff7d26be95e78b74e3ed6ce56473e868fa69702816747e71f931f47d348e2c7e5a5247171fef73cb93774f8fcfc72ffb5dcdf9f8f9bad7f0100cb6f75ba8fb29db445aeefbceeddcd9788eeebe2d446d7bf3b1f0f775f3ba5cf73659dcbddc7b9b9e5dadd9db7f5fcd46118b6daed6f9d8f4694eebd6f8fce08fe1cbd7a8f6d37a2edcd786dfeb6f9d8fa61fbb377416a5ebbc5e9ddd7dae7af7778ba32f76f76aeedf8ba2f797afb5bb774f7369cbdc3efbb735deda6fa71ebddddbf17cf2f9aed476bfafdb5ee5717b7754e70f61d35eea292938dcfbcd3af167a692bac685fe73ee4da9bffdc6bca3d5a2eb3d3496342ff39f2f736e5ffb4d25fe5f2fe7fb797dcf153637e4bf574e7838a9a4b5f1a17f9cfb936a6fff71aad47ab4678a0e9a4bee37e42f9fb7fe28393f90bb68fbab0dbf7d3ef0f7dd6e9af322c24d5aef34c526afad779975e0e2c24d5aef34ebcc8b0aa4ebbcd35687edfef6f3cc30ffbedede7af267c2655c73aee6de78a4c35eae39d7736eef149afc7356ceb870714986bf1af9aae6debc59e4c2655c73aee4db8364df3ffb99d6d7e21ae4da4fff6abca3d5a24fff6aeb51ead127ffb575a8f568fb9e292ae6efaba7ee78a4ab9bbeae9fb9e292ae6efaba61f1869fe876f686da21f4fb76fa63e2abf7ce1f69e987ddd8b16a1943f795dbb0e667930ab9d7c4bdcdbcf255af8e7ea5ee61c1e7930ab8e75cbdcdb999e4c2ae39d72f736e6ee0ebadd32f90f5d6e92ffd930ff2f96efd65f93ebfcbd148782aeb74cb8baaeb74cf14c930fb573c6bdbcf77e2afbcc375d39e0e4c3ed5cf1af0f3c5324c3ed5cf1af6fcecbaddbe9b78bbceb74fb9f16649871ae5f0f3c9af8fa97cbf60f173c9871ae5f0fee2e799261c6b97c3c430869dba7c19bf5a77079ec1ab6c9834edcb6b2de38fd079f05b63c3647eb459dfe9d41d3ae2e5a6f64ac7d3a9e1f0554fcaec8f4e8a72ba775b79d3b1c7eb6f3ebc1541d2765a569e9e7fdbcbaf3fedd39ff6f2e7fdbcbfc5c749e78b68ff90628393cf16e9ff171d278e6da3fcc9593cf16d1fe293c73d6da20ffcac9e78b68ff3220c9e39b68f03607179fa3b40d3a23dd481a7e9db97af01baa7eda7970eeb4edd32e0edde822d4072d5845cfee9e5ab08b9fdd3cb858fad3d2c74fadba400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0xa0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040091ca1c67939b7d5d2534e3cb4b6d1fb84d10f003b00e803900e003700d803500d003300c803100c002f00b802d00b002b00a802900a0027009802500900230088021008001f007801d007001b00680190060017005801500500130048011004000f003800d003000b0028009002000700180050010003000800100000dd416b97bf3720b7beaee9e8ff3fb65a6f96fd2f869bffb9dfda52795a806416a01f7f2b5e161e9bf7f2f7fdfb3947fdf40e56ff7a412ff7ddf29bb5a56174d0b21782e5d8f8f977682ceffda537cb81602e033ed3f8df192fb6f1e74feb4f1d7a77d9f1f1495f5fd855c73afb8d3eb8e1f50dcf38c9dfbd98f8e3ec68a7c96c75c7e786b1fa86963cf98cbe98ecd2adb39f8c74b7e18fd4bda78fad3e09bf3fa377323f00e78) else (if i<3 then 0xee1a1c06480a3184a01c400a90aaa03d42aa80f5a729ce569ca7394c72c03131cb00c40dab889036ae2240e50082010c045806b016e5204b128079016a031404b98292cde00cce40825ea4b9097a92e5c5d400d317500348549155215245540d28114034a0440086053a02100418082010001f803e0056807d015a01f428cb8e60a32c2e802a852200aa027a00e8092803a03d0078402e6114a22a00c815580320554454b94a115203b0074402a016c143807200e001b8036201280b1804a02c406a00d00198032006200c0017802e005a00b0015802a005200a00138026000b208a429c255908101410b9405040b0b44902c2d12442b303d3894c0f6008994a802282980d70094012002300440084010001f003c0074015401c0036006800c80180481005c00b00150028004c0090011002040160078253801c0034111402684a508a6804400c001600280048008000e001800280040006400500110014a4224550d000a32729463f875fc769be675754ccf631c8e19000d1efdb3a9b9be45861e96d9794e8e12e0790fc00abe8c9b64c825eb7058f5a147448e42c4770f400f73a2dc731bb6bc9d228769985610e3008c0ac00edb57c6ec3a32708b1cd6413a404d72b8700fc00f8fb2dff35bb2a79760c6b1744ed023108612000e675ac02b69c626771b462d5846cf23288210c00cdf0eb969f9ba27785b86114a460e02dc680b400bcaaaa427095a3c819c66415b4a0f22e8700e0003b4ae1fc500b40a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0a0240801c060140400c020040003c0e0340c02c0 else 0x200488f5801223d4084802102120084006811d001a0474826914d209a453526ea05549ba815601a84dd806a13740ba816502ea059541ea955507aa55425c81bd097206f48de9055237a41550e0a8a54382a294c528cb9314a32e4a5c884d297221350c49199431246640cc8171033205c407c858901f21625880a0156202805409e8035027a00d522489b9489226e403aa05100ea8144878803121e200c40ce80d9033a036447880f511e203d4e5c8129397204a5a6e904169ba41040e881c103a2070505ea031417a80c4828801920a200658a481c5629207140888131022204c48468195211a065527290c549ca431481e84c9207a1324044801d01120074022817d008a05f54a5108a311405380c704f559cc13d409c88910272224408c80590232016402e815d00ba0575054b4b94152d2e5c24a0917092824405080bd014202f40d0019c03300651c1ea8b9707aa2e407ea14901fa852565c8cdd597233740c8018c031006100c0017c02f005d00b8016c02d005900b0015c02b005500a8014c029005100a0013c027004d0098012c02500490090011c0230018800514e6026c1398625284a39bc0498a25))
def spentSigned11 (i : Nat) : Nat := 0x2e2e200048f0118207800e00001e0000004015031074e6010b0407c000ff5eee00c4403fa1a0120830f9190804400088003013f3800bff8b6b8b08100100100000fa400400004021204400010804080010000390802014000080c000000820190000100010800000403ca0000000081000000000000000104804080020080000c000801008005000000000
def linksSigned11 (i : Nat) : Nat := 0x520f0a31000018126843c00d9006a040113cd0420000085c000000002021b055000000000000480e684ff817e05c8d5fe81c80003802080ca029c009182d08326819b0012815f1455232043df02e54040833b84c001fd85130281256c03e400509d4e82bb849e81930545022905e70629215182890df802600006857d25ef863c83de02ac00ed00f181c481400000000202080000000000020df0000204f0813b8462036d80ae246c851c830781ae04100000000515d00000000703b083c0000000028030000000000000000403a0000183b800040447833444db05b8000404a8000381ed05fe80c40531841c000633e301700000000553e404900002038284b781f304bb85f79020000305d0000000040188000320f80005860000060565a145a567852b84e0000382d9858b35d6055801280000000000000000000681bf0082801f811800020dd00000000401b683ce03eb84cf05a42a68000684d331d5046b81e203518099824e8364844e8398000404090244037805aa82ea000a859082c902fe01d200a28431830a006681a385d80000000184500005835800000000000000000004004b023c02c0000384a00001003b0102815702f0000784d8000300bf060800000004838f8538000382140470000785080002232e052185830599210253f000050070000683180000000000000000000000000000000000068348000000000000048800018278000000078428000180280004011003a800d205b000000000000681d80000810800000007dd480000000000000001a2e2231a8167808a0611031000590620861d016c056e33d80005022582940483a14e013402010232045883f8814993f5818202b100fd25c74bd00003a2d7c4e000028270000000000000000000b000045de923d3147a0501a548032c8bf9cd49233186372303047804ee8be483708577839403d202a702548346825a007800000000d0b084841e0c581325851600140000a3c00c300860006102800428101005c02b1a302030a10282000050308000800000283000408614241070000004000000204000030000002
def rulesWord12 (i : Nat) : Nat := (if i<2 then (if i<1 then 0x8577fb3bcb99cf1b257ba730f130561abdfb6f1eec3f28989835fab9bd8caf75bfca25eadd57b5e30784ad0e1cd0fbee72f9a4596f5d343ab398705af8eb1daba57ceafcf1e4bfb4c46176dc4b9f0d2df6ac7edff4c1ad12e78223fa0d6d3d5a7920ecff06b4a587689cea5fd66be26bbc7d58ee7e61ef2f0ebd1d907fe26d5efe9f1e4bfbf3088bb6e251373a47ef3bdad576c9cbbedcffd239a0c15b1e229f0959158f2e96f1e0cd07fadc9e7eeef35690f61ff64d076effed90ffeb41c3b53e10fe3d36ed8372e2b63cf973ef586ca1c6b41869cfcd226b2dcfc7adf9c441cfbdfdbbf16175ffc9ef8785d3062e8dee4e737c3e26d71abaffdebf3fd577de69bdb5f79a6f6cbe7ae96cbc7d3062daae3fef4fce8f2f1a75bba1c9ebd3ab7627995ed20fffde989ef4f8f041d26ff85de9e0e7eaad32b6e0bae3396fcf053598c67d6555defc3eb85938d59a0bb53dd9b0b8c757ac176c3c2e26e558f5bba37c3c2e3adbfb9b7afe60e995b2df655aef184f7f7f7ba2b2bbb7ce4eda7d333fc82d26ee16d3e1e3bea4c1a2de582f15b1efe4e18dbb1e5bb5afa9f9fbafe583d165f718f6efeff17a0c1c1f76615768d3bf0e4f3c5e7675aedcf4efbb1333d313a4ddc2dafc21fc7a3d3a2dd278cb056c7bf32c2c7a3836e6cb056c6267e741d38dba5585def89cfdd7f2fee2ad10f6718f6efe4c1d3dd668c2ae83bf089c65fdb232e6baefbeec4fbbd498364adde8aeeee60cba77c2ae26ebcebc4fa56d3f137e6bd23b7b4adc3b17e4dc6aeba1afbb371d7575d0d7c26f41e4b63ff60e73c6737f57a560f1de3fef9bd0765f7abdfb661dd8fad1defde7b3b3bb1a7bebdcd9dd2beb3fcde9583d78d7e279bdfbaf1aceda7e7f6f41db1fcdefdc4d7567aebf5284ffde1e3f3b987b65e773c5b2e3fcc7786d8f8fcdcfddb1f9f9dcf5b63f33c9e9c8b1791f2ada7f4f25cac591722dafb4ed8cf731ec519ee47ef37d25e90fbee5e64f0db2fd391efa4bfbcfda7a9e594bd7307655b2ebaee9ff0fbfacfd1475871f7f58f1da6f2e3f79a6f2f1bcd37979f820b53b63f3f3b17083fef5f6ffbf2effdfd62ccaff04dbfab707fde5f31fb7733f160d378fe7456ee67d762e983fef5fa9e5d16e6bffbc3cbceffbc3cbfbc96ee6bebff7975d07fef2ef32786d979fc75f379a6dafd723dfc36c7c8f4ded979f9dae0ffbfac78df7253c91da5bfdeb91766de5dbfbc77979dbdc67378f8fd86ee3bc7e7e75bbbc77f51d36f6cbc5bb35bbc7ebeb6ef2f178ded97cc74d6cbcf7262e922e45beb3dcf6000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0x800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e01802804006008008008c65df262a14593c08ba6235065a0f383100c002f00b802d00b002b00a802900a0027009802500900230088021008001f007801d007001b00680190060017005801500500130048011004000f003800d003000b0028009002000700180050010003000800100000e5116f3fdd6cd2730ecff938e2b56683b4144d34a94e4792d9acc941da25f9c463e139fd8f6c709c9641ff5a0ed6961cf8f63cbfde39bf3fddad13b648fef61efdac2ab7fc2ef9f3f6f1a78b268b4d9456e592bbc72776a87091edafcfbf4a94f1f49a0f6dede7cbae0f6ebff7afeba74de863f2f1e2d7a7ac95feeef139cbf962e26d59b543ae26164d1058f6f58589dbdedd1ebefad614d6e27a37b70e0d5aaca682df396a2d44e136f7f5e5cfb26e7af655fc6257f2df5905eb86892b1bbcfcd7f2d9c5878ac7cd5f44cfd7f2c65e2a2bd2bbc2e193c6ef272ebb39b359f37682bf8f3f3c58bb6ba1f57d05416f5e76e0f0c70f3f05d357d26b1e673b759de7a3bfd9f1ab1d1ad1de95b7dd863) else (if i<3 then 0x11a04e81be00381a622e81d213d409d13d409d02b41b902b41b902144dd02144dd80e40b180e40b1005510100551010134449013444904d013004b012804901200470118011905601d80fe03a803a27081c2464a03e06180c2253414125341410450110043010804109be04009d203f00f803d00f005780a22738952073408d073408d06241010624101052406d052406d60f40ec60f40e801f807a808a01a80c883e80980f66128901039090132e515632e484a024408a02440e0640888912e888903700d803500d042260154226015033202a03218ba51240c451240c002f14e542a94e522998e501498e50584955058495542e802600f8cde026a012537819a053602d053602d80740b880740b402c00ac02a00a4028009c026009402401ae023114a03b408803b48aa0210156020007c01e007402a807001b00680190060652903e017005801500500130c4a01200566228044010003c00e0034339894a00c14ba00b002800900200070018005001000320050022005a2931a183d7708c813f2223d4700b811d1d62e0360009b11fa14bb36b8ca96da6a3f66aca90f815020c1d0009d323e2f40c766d497ea9c4b27ccc91521f82a028000804f21c5b6a694c1d4aa534286dcb51291c426831000a2333232423788d8187ad14c2850e11582142e42080062ab655027347c84cf09b12da4ec800bd12414c11800562a0d2c22d3be66cbc956264458788cb11c1a41b8004ae8cd091e33545e0a292420e374600860c81040e8004d491d111e9378668b494f2363e06b0a90f81281480013a1f02d85103a04c0480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c0160280480800e018028040060080080001e0380680c016028048 else 0x32a80520500841f85105268134159813415913c458913c458946b518546b5185814510581451050334069033406902d405d02d405d26e488526e488523148bd23148bd0544031054403100d400500d4005063446d063446d2434539243453962941b162941b11724521172452103540490354049004417900441792414059241405906a41b506a41b502e604102e604180d509180d509102f40f102f40f11396086139413804150510415051215819e41288e60298))
def spentSigned12 (i : Nat) : Nat := 0x2000200000000128bf02000010000000a108100410020f02024000482002200810400804ff410200802008080900801080800881080000202001000100082040008811002ae81a404222f1080111040488048fe50080808804090400802100160108020108880084040400000408107a40000
def linksSigned12 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0x180464417ca8051902c700f6ac08700000000016aa1b0015e80a1506492ce83c200700c1d201ac0e64a49e800005473a2094c0007203a3d93f956a7300df40002c08ad610f800000000000001801e00000583d80350f000ec00006217f0000000000000075bc900001a0a5a412eb01f090268681d140c880000c081e80b68d22a5bae09022a0000380db2a91bc075f40a0800002214d00000000000000000000000000001820b00000507e00000281a54a227e06c6468f8000000000c05f400000000000000b049fe0c2cc0d79c456c037e000010156b8225100d880eb641c6e82850000000003c11860053e020200000c20480000b04160000000000034e20358a0e380000680e0201c3e03a1154b981868058aa028980064834500001e4eb8402d18445a18710099500d68020700001e0737c0f0e01b22060cc0a5180770817ce72ee206f401b9d845ad01b7c8e0c0000448ee8004a2817081aad3ab2002040000000000000000000000000000400b740748000000000381692076560efe021b583c800001605224815983e7d20076009c40f1983f10089c00002a4b5fca721081580da500dd8820d90400684fd01cf8042bb06dbc2e2101d4d84070472c000004459480a500000284580000003b400001909209cf8c8008204ad210c00000401f1304f0e00d5edc4e215300001e08b1401f203c06418d200abc1a9f42422048b0c2ef85d73c9004021960a4dc109901671770c0000290a8ddabf80754607240000202d500000000000000000000000040aa4000000000c07000e44c00000000000000808d140ad80000d02c0a00e800000803f0000000003405c8000000041801e1800012000801e197020c4c7001a1c2800c264000402e8206300800808d073800000081008904005800844a040000a054205201000030002001002630088280018004001003e1cc8c0c2408116000080e00680001400e1809507000050d040c5002e0069f2c0028900109830201f803430100020060b02243800008404140830706100800000a850200201700058002019803e002800214000061c180321000a140000002001804000b000600186180400a020840000001800c005802c00100040c5001a082002c00480220c10022001810228a800a0000106286802400180022408300089810e00b000234500020029538042000a00000100010004144800a10100100060000002800e04080000cc030e081070e0c0001a040000008701000c5030600303025c1950200780020038000082801800100000028000006800000680080078000381801c00500160028006002001e0008000003021a00200020018000240020a044000a005800000481060000104007000e04381242c28d16002800c01901000c504040439822000010408a80040000708001060c01300 else (if i < 2 then 0xc0c42ed5f0000000000209a681e780000800ae00002005a649206a31800000992428197c02a860036c1de453e4003aa946680000082615049842468406182c604027d20b0c00002218400000000000000000000000000003a440a01b729015c07df80f4b03d0000000000000006022b00000000000000000000000140edc000000000403b200003400b0810b400e40000181407810000000008f000000000000001a85240000400ce00001c049400001006bf010a00000000078325000008039d58c948288c92452051b020f00000d052340568808c00000e04cc8047d0060001c380850a0cfb9d52303fc300de000000000080612116da0cdfc09af83ea4875a00000000058244000006e040821e700b500001a0c7000000000000000a2e75c4598000000000c105511cba846100000aaae94188902760000100cf0c9d5d02e5c04da8105c0000583e10000184e19409900000605efc409fed19b01f940677003af012a48279548462ce7bc46390161942ce6e8d500bfd02b36a72ee08a40218f80633087a228ca24b07029df072c00000803e9b17c5083a6a23b448dd004650766000024146603c4105e4000000000683eb0000000001401358043d046a40fe40000000006061f810e8000002442005da0062280426c8f4a04cfc405c0000000000000120b6000007830e0000000000418400000f0339e48ef29d2cb92700000004dae49c30440003a18117cc1670000000000200ce01a7b094300001a0263cc2f00000000014f0c9008780087c087600000411d00000403fde11248071200cd803c800000c4b7100706003c68c6a0034e82e920398000000000241920000180ade402800000f021000000000060bc7552f000000000068060402c52111281ac88193000002c9cd40f39044a7474e0000201bec8397000000000000004801fa045b605cdc1f280000b47fc00ffcc219e00d1100fe60749c09e7bb85946f680c75800c00000902ada06e8c0b694244d008ba007000001004f2025000000000000000407eac04fc0041701dcc00500000245d669b882604400000000000000907354083064b1bbaa200001e054dece2e809fc013a000000000280f7807c94092e29c4e01bc50362a00249d1b603dda073600000c0f7800003124b76af0000000000f05ac0014800006018e606c8c062b40a8800007074c0000000000216ac088600425810300000e04fe407f1816430332000000000000000000000001c4df800004a17600001c0c16410700000d02bee808100d738322e001720068000000000a013400000020900000788a8000000000080c2904b6009b8013a800003045ec07bb109a80000742ea6094440f2800004884aa0c800000000004028060874c082b02abf077dc016f4231d83e6607d00090d41ff504233470d802000000300dc0 else 0x901fb00000600ec8049800004830000000a11608930b03460000080b93c05e421501032130a44420680000d07c0c0e521d34b3a3f1175364f8000e0180d7302aba1193c195208af103a82100880b8181a7018a9c07b6823178038e12c2401500000403df106915671801db582fce464720d88c0c1480ca44302a0ef40000000000031a00000000063b280000000003c144801c89948a81157414abc91dd07aba087c011fa82d43074a503e40000080970000000003cc3f80000e02aee0d028197a82e16461f409ebc011a84324009a00074000028006807021403a40180000000000c114f01e1f81d744565800485c5c984135462d2edf341484026421247e0a35c227d804900000c0b7b5c44a03a700833a040e80bcd0441706020000099d641b96a771d831050000881e6903d6c068941cf28414f07c48057a8052008b0b055db087c00000000000000000000000000003007800000000000000600caee46201e6e03950249d031801d355004c7039562583c00a13b2710561406a5c0fb00000e06d1c05ef59c4082dd504c5a1174000038426300dbc0c1c0000102ec5019000001021230352f05c4c00808045801270000000003810a800312045c0000000a28000000000601d465bd8000000000c0840000018241406ca00001c1bb00000f72f400001e49e0000000001e0de8c19b00000802b36eea000000000000000809d180fc182489021442303594f20367d067562ed40000000000000060f2a41ec80000505a32ea8c00000000000001809be00cdc831a00001e0db1017a882cf2a84d485bdc4937017100000000021c907a39000000000000027000000000040a8c00000000000001c001000007033f70370000010054700904068e000008179b393b505cde012c0000000000000060fc800000840b000000000059c9e00f6f074210663ddd57822ab01c8000000000608dd0000000003611e80000f061b4001f80a813aa10000000001413400000407a5e034800000000000000a041cd2158013b507ae00002410d80000600fda047700ef9017e2051f2076da48fe0379e8487d245018d8bd9483020996e4441c20000010667a0a4882161012900001c048380a70bb2a506bc00003413d8000048472ec90b817f000000000100ba9946038446eb720e00540000000000000160fdc000058c27000000000240112045e40844e106b5c55b092776853eea820009f83efc0573a0b1200f968408f011400002c056800002013980dac0000689781028600000000010144a06b60000280a0882231034a00001812538247a11ac0000280ce8845200000000018077d81e80000000cd681dde00e630103802ff247fd81876026620d9bc14c71397a066100d3380c4b816c707638094b80e1081b9301d8c6222808a502e8301dbb2408c0028000000000)) else (if i < 4 then 0x49825ab05480045a81382844c80350000024112282ca5588e0088081b8f836e7054e00001803c80000000008107fc05d100d4c30e640dd701ce80000f05a04033d00ae103cca0170808a3403dd8358128902f124000018250e739d00d35c929400425202da0f040000201ce0000000000415a80442d036bac8e7c1ab3811b0051d6028081c508165d0297802b0000000106c05f720b6e011c2c389d017d684200065d020492702a860e51d0f02815044c20cae6221b1018e079700b05991e8825f00000c016000004834b000000000100388803200001809f59c7f480e9500220065800000000000000a0850000000000301ba000005921a81cbc648900e20a61cf01660770440c0c00000000000000000000000000000000080aec00007c14300000e0cf4000028317b274ae90ab006281260b081840b2440fa5814c2040580e828055402b10000160230818d901d6000018492c00000000000000002f61839601cfa02380000181be00000000000000340cfd0420c92a16083d4054b04270000100279420ddb90ec63f6eedec0000000000000000dd000005030c000000000341108000000001800e4000050326d059b961768185202d73723e0000150b9000000075840173c1bb800000000000003c0c2800000000000002c20e00000000000000000000000000000000000000302ff00001002afd8fd0028bf0106a0340c1d1580f3f042e80cb7402a80000000012f0d400007424a000000000310a50806a4b55800001816cb821e2043980e08000040421b04fc00000000008331000000000304a44002c000008c614807c0000000001e0041007f90059305d60000141d720319604ee40776cc48800000000000000003e0000000000a034d0000000007022600000000000000b0080e0da80000180de5a7be2b10541e76027c7a37a40c6040cc800000000020e1b41f6302f810668c096681b96812ba0318e10de41a080077308b30249001938000000000811408cf86212c703020000000006924f20659810a9ad5ec012ad0672804e300c598460600bfe0909418ad0349a27ce00003c216ca310306288000c00000000040083404c4000048064075a3c07cc00000000000000000000000581f52065c2038c5c648000000000000000000281b0000018c53a5888000000085ca053e4033381a6f06de000000159508d9e00ba402ec00006816ec032800003008960096778b680924c01e8000000001c08c7c17000000291e7b4f80c09780000907d2000000000682ef4038860d80c9ef80000b05e2c06540000082aa000006497c0000483ba00001a04880202a81aa0000000000adc400000400880000000000000044842e0d70c0f600000607180000104bf2893a90198000031a11000000000000000007e682c0d0569e0f50acd3b80c4203b4f70a else (if i < 5 then 0x4026c000000000d004283098000031250f05dd08c5c00007817a705ec6035ac098000000000160ee4000000000f7646000000000100360000000f79c1fa00000b01240000000001037b00000000000000480f9000000000000000000000001c0120000000000c064200001c1fd0000000001481c7420c3842f5078c000011d4fe824e5034760aa381a25d386300dc40dc28039e825ca0249ee86a892f0031f2232d2eeb3404a000000000100b3181c4800000000120d7ec16e0000000001202d81dd3783130000040fbb41b0c812d40324000000000404250000000003640050239c18b2e0ea0c0ff89890b04114031a4007cb945101fae0900c11de818300000000000000703f8712a8000000000002d2a06fc00003010b41380902e8000000000380e5401b00000001418db8f0000024012c053200fa10605a00a541fd80000702fa4ce4844c06808600001005aa014d9d1a06053e2e4b98063b1426592733111e401bf03c2d070b4082b8203303f300001809b2011bc023d00000e04b840bb000ae2744424f3dc14d0000000000022ff0173e82fdd07ac62ec00000001d1e03d4606ac81658000000000e0bd3113e3019a8067154e47c0bac01b358343440a9020723944e026e80956c21c28219b03c5c6ab0000078378000002047a021a001de000002e5a1518a90024263fbc00b80000480fec00e900863c201fb8efb04e4a0ff400004009900000a080790a9000000000140c7800001a31400000a088b006ce028a00001606808169d01210000048424c2149214b60111c116d01f680000e988d4101180a100000990d3e0760017180000e04c000001c926d0158b05854024f41f1d937ce0036a0686813890383706a2803c641e9a82460674200002481600000f7298c02bd990fe02a02014ec254b002b0b1459078a4095d1d94b04355038fa0b1ac2008b87c8028ec037c00001a42d4089000d08400b8000000001c046ac191bdac5d1151e019d81a8702a5771e1e0a134088e83dba0162a012b8184e843f942e1c0a994113d03b500000000000000402af8011f4c7fb0182780a3a755920bc2c22bb844dd038d4036b0135c9be40000000000c467c8203b0368630dc000000000841f4000000000700f27056c0078141ad382b8107a22104220bef018fa01d522577c0a54019e4005ec8f366a18e922100000a0d5e80e9800004012a000008102b8299d06fe44e5840d200000e075600000000040387f0730000d2c1ee7925c00001606600000483b8808a920d778064e8211824b100227c08ba84510000000002c0239418200000e05acc1639020900001c0707c208d00d5f911bc112c0000000003a6f8e0c48000050123300c5206108086f814de71fa00003010900000801eae409b0016d045cb088e00001c0b200000c04c6c0e2d061 else 0x150110000000b7f412c000004b2dc00002ddcbaa22620652001a3a9d480000000000000000004c3885003200001c1aa080fb00001604b3c1ce0000000001e89f40000000000000160d0e003d000)))
def rulesWord13 (i : Nat) : Nat := 0x37b0190dec0643820d10e0834413218904c86243221990c8866404a1ad01286b604a064812818020d02102940840b805802a02fa03b02980ec0a41ec8a50e9229606a05581a815497210225c8219202050480839807a14a01e81291ca089472822417404c024011117300545cc016064849049212414c4de817010007814e81d405807003401800b08944e64a52228050024010007107c0aa0ab006002801000600236bd4b15b668d95e357d9b45e13c414d0240460031ebdab2a02688d5fb6c9784bce728c8b154240027190613785b9649694c50d370ad2004d0c8180004b118410f0370c82d0a023078190500f0280500326ae90a0003abf7e24dcdc10052bc5fe4a7c441d4be2ff37bf2b14d6a7dfc96ae086ec27840f26aefe378851bc3d042ad5a9ff25bc9d257a9e3aa8af9abe597eb531ff9bf65f8a6bb540e7e7f35166b33f24d0e378e455a9f14be993a353e2fb7c7bb7e26bbbd5025ec13e9be5884cf6ed7135ff8b08e1b981aeab47f37cb380e65cef116b0ee717f434edbe383617b3f1d2422d0f400d3acff7c34845a785fd70d3b635a9f17f922ec1bbcf0857149bf9d56f7a232f67e5b3cb6ba761098eb3f23c76db6de10dcca3ae23fd6fde106d8e00994fc8ef7cf0376dad31f257d732b17b79ac59e47785a58fe96e7c4d6d43fcb30535b163fa59b481b0623be789ac3fa5588b672c77ac45ac5f7a50dd184230f5d3189ac5dfd2ede20d9c71defec4d6c58e32fe26b62f07f47b481b7c038037749c0da0e004a5294a5294a5294a529
def spentSigned13 (i : Nat) : Nat := 0x4000000010000882
def linksSigned13 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x5a4ec07c000000000a07fb40a400348000000003d4f7000000000000000000f0c25005b89100c16f3037f40dc00000c04900002416ab0679817002dee8369000018333a061090b690e1d433d300640000d082841e5767f40000a0e30423dd065b401f000001c08300d6c082403e48028c17afd339ca848c178a0d1c000000c6c000000000c2bc80c88000050a53822b70089820800001117df0762806c00003889a60d8c0000000000000000000000c034480040000000000000021b2000000000a0a80000010270000050caf9370c09c202b850092c2f500000426b000039e6e00002408480e2442b1b0e100000e080fc0210000182df00000000050e06824a707fd5cba000008112705540000306d08157000000000009400000000008273b95b2c28a00164c2bab3351677f002ff00cee0b7200fa6018e0259906329c0ad0378434520708023b000000000600e80000d08b25f55e07ab01aad0c2fc31800000000000003828200002c455000000000901c800010000181cad081a0161f1c900000000000000000000000000000000b04bf82f2604edc2d2393cf43ab00002022f4005c0000406f3c05d80298db00e05a642660000282791677841ddc091dc14e5089c0000972efc0230000000004006add2ae072d81f8000011c1450a9b6b954078800000000108aa00002806400002407300000000006bf28015106232cdec2df00000402840000000000000e01fbc37c00003c0cd206b980d3d026d2f3690e98c0760041f021e0000268ea00003c2b450c2aa372000035f3d60b16a5a80096901a200000c29700002c36c40ddd80c2f095800006036d4371b01d5811460a2742eb101e29f77000010088d0a588006104aa00620075a022a40639437984dd9425200000000000000000000000c2688049400002b44982b600000000000000104000050a1200b80060168c0404100a0181062830a0018089871a0049dc0000001200e800400c801800001060000506000011e000000214f00020000306000000200b810a003830604180200000a1c04a0014046000c00307040010602008010a009000600980280010094002000600180040c58a02004001e180070a0028e001c10200000021e04e800e0400004103800000201100c08000047801e0018000002000200181600c803020000000002002c00200000ce012c001802c081002e0410034582152800a000a096000a001801404d000000507120400008102800000200040060108040000e00000006800000001011c1890322080010c082800000001020000f02000040c0c1800c8c18000000800a006811a00d8012001000601a001a002820200780021000e043c48024000800c2c28902004020001f01184c380260428304081800e1cb00120400008281000c00100760008008000832c01585 else 0x8762a01404731a0cd6c13a604c8000000002c276000000000e02ce9334605b000008049cc32500002834bf0dfc000090404000000000c35ea047b60c220d40a2558aea000000000042f11038c0000000010103000004237000000000000000000f0d11435b300f40000901fc0000d08089f260000000004639c00a9000038251608cec1e4c0d93423590128c13de09b9d2bad03ce81b3a044c00d7f0e0ac38368dff818f60d98ee60000000000803d0dac200000801c411055356b01aa9b56c04c0000000000000070049c1f430c91826c00000029800000c027000026380e0d700000b0d4740c620e9d834e00000c39900003c319a25dc0000000034218000000000d0e7e41150000282e9404580000307340000101469a68e0278000010635c03e1903240b5106900000000019c034038642e4b03a280a0b076d03038066801dce0a480000646e40000302040000a0133c0cc70268016270b39c11110a15411f2051d01ab60cfd02f3000018086606736555a08f00000c09ec0000000000000902e842100000360f730d03808c10cde8108007248329db5e60002d053c417cf05f5e1cf10d3d82a790172c2c831dc38220f0733815e20063c03740b46e8d6d00ad802500661832c0000100fc00db880a5f0410c37bb03560354600f204a579006c13fd0b58000070dbfc374000014258000000000a02f6436500003c0900000141d23718c0000806c70058a83cc000080b6443070000000000000000000000083af4042d0228000020e2909cb880fd083c8c0f5206d740bb0000182a551c8ec0b700001c2480000310a857242004500001677ac8de4812612e5400000070441190000000009073d829be22df80d8f01f541bdb0a20000046205033a000011d54c0cd2429f083c40000b08118065915fc000060833827d45e71c1f1b01b6c1e1f0b53c11800000000050e01428710540e4b2302440000c0b880000000000000509e1008b00002009700002e09d00003446600001dc64f03bc428fd971580b1402bf813c00000c27700000811c9724501afb5e010066d09e9c21b309a801b700000000050d68c22e00003c06b5055a8016b0a1382cc21e81832100002836000001411a0000003acb0db6414dc0c1980d0d0aec02e7421c64275e0503a33210ab202c076bf4000090369443430d488c2c708c140dd201eb402c104b40000606740000104ac0000003cac18b207bc837620d080000d0c580000e06c8c51700000000000000000000001c109641880000d096f40b9508c40000303c000004028b81a70000000003089600a800001c39860a56816090e22a43f00000035700003c17370267024c64c7c00000000243230071a031e7011a00ff20ea140472028c408e0000000009016800000b8e8826200391c38ee074400003579b8269e6d5400009) else (if i < 3 then 0x90b60000050b6f40ad20d2ac0360000364fdc0c47c071e8963406954151008a908528b7d00001004f10c215d322058c000000001e0b7a6be8000076541c02e0071ec46e602610b52e07ea02c3000000000109700000306480000b0937c2feb0d240000f02f000c7403839afe60798000090553c378a0aa3025700003426500002497610e2ec36b0073a41f00000001a32097dc0f79928b1a44d077981e7204d400000000000004656b1cef6864dc26dc8e5000000000305e721160806010df80000d0aa801360000380aea0608000020b291f56009854a337928e814ce755e825ed065640a76020180838585a82f8305dce0f090e5da728b0eb400e9005d20183d0024000070315112d10834818115369835d10510000000002410a00000815db04dec2f490755c2830895e6f83000001cf09076bc191807b0c15380eb8dc6e00002c0b0d010c000000000000019d21004b30b8c000000001c11b6057cc0ec67c820291db452c10580e52c2fce0028000064d484370b0e7a82a3d113d0216200b6ab5f490148229c0519c301000000000d0d60000010440000000002010e0000382fa0000140f1302d0c03f000011f98808e000003050d1944008e541230000202cda0982c20e0000081bfa0c4a41d9604764193c04bb01f2d0aa400003021fdf66b09030315011a3034130bc00102e09c9d85860d9f81b90000042ff00000000000001400e00002c1a9000000a34c8944000000001402f109bfef82000000000101000000f07a64056a067c000000002636f401340000c07cdc05270bb40000d77700000e078c000000000000070a8980d9b03940000607da82ea76e600000605ffc04e30491431720d65cc840052dc31cd0b09c234200d14094000028732e0e76c29d70e90029a80a0102bde07d5e03a407de03a1d0bbd813800780000000000dc4c30a70000020dcc000066de40000283db021950d8980f60000000009045c00000000380eec075c000000d340000d06c000009924b40293077ec28c00000838a7082d42ae60044c25dc093f42dd90b068057000000000000000000b0cc40000a08740000000018e10605d6c32fc090b808500000cba65039c0000808e8000010950000080c12012020e88000000002c180e0d325c3d00003c0920017c0000d83d5e493006400000204c4c755a0ca902cb000c7a535000008314200ec80c400002815ca0b1cc10ca0076417b102240000a0d1a01c0a03ef197a0000082869066e94ee00003d8d230b82024e70516cb55ca9640000d024c000050717253680a35437a50740832d0000000000000382be700a8022370108958e30a40812c80254434810a8701861039ac100106b4410df06678798b0c175c3e304d145eab0cec000010358000000000420f106ef010f30e15021c903f94179644bcc0b200b27 else (if i < 4 then 0x6e39810c0ac32e70082028e8072082b75081e039260389c09fb0ca341a5e0154000028d540000a08b76c7710855c2af20ccb01fce000281b67018783399056782bfb45e3c2d0d727c0000000000000000006d78000038267000000000000000000a01dd41eb365fcc30e6023c0000000002259000024171000000000b04a0000030d0c00000000080449065e4005000000000800980000c0598000060e68c23670e8101ba0000000000000000009b8734a3054cd80000000000000000000000640f0c37d60cd94226503500000000024033f25e40000e0990000090e6d438dd015280ac00001c16700003c2c6f027502f76061ec24b50acf1130000000000000000000607f4000000000000020e5b23a2000000000c0868000000910000000000000030a4c000047df00000e05db03270000302d5705afae9990687c32010c4f0053e1dbc000000000000000a64000072cac000000001407b0000344b400000000040e3d633100001c0075070d43a5b03b64375a05b480b600001c2460000000000000081ed317a540ab1098c00002b08c0000c0904000030cf0000040be69989301d2800800000000040b7800008b45c0000e75fc0000c084b043a000004353701bf80320000342b9000000000c0300dcf940b9b19a50000280cf4050600c1d00c3414287df65da3f0ad6c08d9061400000000000000062a42e5f03256d186475483a3006a2c3aa604a4000000000000020527046f10d8681d40000301d370bb3c224609f3831d000008249b0c332f7bc08fe4310f00e7c15b90e4dc2d3f0c68c1a694e5e0133a0d58252bb082740cbc7ce400000000103917032000008b4572979501780000b084c81c47ae080014205a1dcfa00cf80000409fc00006896e0221ab26881fb00002c3a939e0c0000a04e5c0c382d5000002693c000000000000020e1b05ec20ba0000000002446d000016d13901a0831f000000000d0ac8000080bf4000070258000071441c2170000000003048ac3260000282ad30c03c0aac0a049a34106e141a000544000000001416e0000145f01945482550000282d700ac00000e0e42000f70804c8b600003015a728bd80ea000000000506500000f08f98245e05fa8205d0aac0000917b4000000003e76700000000087e5c0000a0cc1c0ca000022252644b3839540bb8844aa1e67c003a0da981218002ed959707b981060000282da70040c07040032035f000000338000000000c03e0001e000000000f0bd882cfd913400002094f97a540b1242fb00003428b001e45d31507e5c038304f800000019e296931d58404160847e4fc009fa0152c0c3f02a4503ac815800003414a150c780be00000000000000c0b8000000355000018232000000000000000000c83bc000000002c21f2088a430db06b3829e509d2c368c004f806e else 0xb07a0000027cd0579e999c941bec25e9d82ae0dc9839c9090cc2e1625d40172a06240000200340000e052240484080000009006f027109168a76da0590c17ae059)))
def rulesWord14 (i : Nat) : Nat := 0x2e80f822a0982945242945243784060a840439412439412405004003002230261e8bd99dca0f7b5
def spentSigned14 (i : Nat) : Nat := 0x0
def linksSigned14 (i : Nat) : Nat := 0xd00000000000823309ac01000000040b0000b0e0000801400010448215076e22e0540000001413109c032000000fb05dd9f8b7c000a06e16200000000003221898a8a10000000000051f000102570ff62d37800000031c0060ebc1ca060000204242fa0f6c1600028300000000f28b831a0f302e704bee26088c2900031a0102406050d4000a02f1a2c78843ec0e50060003c08a08340a2a89004038800010ac000000000000006f0a00eea0f06b82ab064828107c85f401f837e0d8ca0400a9df0001c14c09040e40ec00020b400050d00000000062f488000e07b43301bda130030504905000100214d20
def signedLevels : Nat → Packing
  | 9 => (3,6,0,0,0,0,0,fun _ => 0)
  | 10 => (200,5,0,0,0,0,0,fun _ => 0)
  | 11 => (1125,4,0,0,0,0,0,fun _ => 0)
  | 12 => (944,3,0,0,0,0,0,fun _ => 0)
  | 13 => (64,2,0,0,0,0,0,fun _ => 0)
  | 14 => (2,1,0,0,0,0,0,fun _ => 0)
  | _ => emptyPacking
def signedIndices : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 1 15 0 10 2 4 linksSigned10
  | 11 => lookupWord 81 349 7 16 8 4 linksSigned11
  | 12 => lookupWord 476 2013 7 19 11 4 linksSigned12
  | 13 => lookupWord 402 1693 7 18 10 4 linksSigned13
  | 14 => lookupWord 29 127 4 14 6 4 linksSigned14
  | _ => fun _ => none
def signedBudgetData : Nat → Nat → Nat
  | 9 => spentSigned9
  | 10 => spentSigned10
  | 11 => spentSigned11
  | 12 => spentSigned12
  | 13 => spentSigned13
  | 14 => spentSigned14
  | _ => fun _ => 0
def signedRules : Nat → Nat → List (Nat × Nat)
  | 9 => ruleRead3095 rulesWord9 16384 6 0 6 2 12 17 80 0 14
  | 10 => ruleRead3095 rulesWord10 8192 2182 11 2325 9 4125 16 7517 0 13
  | 11 => ruleRead3095 rulesWord11 4096 9526 14 10520 10 21770 15 28010 0 12
  | 12 => ruleRead3095 rulesWord12 2048 10358 14 11184 11 21568 14 26007 15 11
  | 13 => ruleRead3095 rulesWord13 1024 2522 11 2566 10 3206 13 4506 0 10
  | 14 => ruleRead3095 rulesWord14 512 66 0 66 6 78 12 318 0 9
  | _ => fun _ => []
def rawRecipe9 (i : Nat) : Nat := 0x17ad88d5b1534c120583c7a314c0a62982408054ee5749b6114160160
def getRecipe9 (i : Nat) : Nat × Nat := let a := packedAt rawRecipe9 (i * 75) 75; (a &&& 1152921504606846975,a >>> 60)
def rawRecipe10 (i : Nat) : Nat := (if i < 1 then 0xa7bd4caa9814c10096fd6caed8148100a7f51caa98148100e7d98a4c53048100f7d1814c53048100f769535492044100f7e1c25452044100ae7ecc6cda521960ae7dc22cda521960ae7ecc6c9a521960ce7db36c9a521960ae7d3c2c9a521960aedecc6d5a321960aeddc22d5a321960aedecc6c9a321960aedecc6c1a32196087fecc6c8a961560ae7dc521aaa54d60aeddc321aaa54d60aef5c121aaa54d60aafc8c5a8a254d60aafc8c5a9a154d60ae7dc5219a214d60aeddc3219a214d60aef5c1219a214d60d6decc6cc8664960d6ddc56cc8664960d6dcc56cc8664960d6ddc26cc8664960d6ddc06cc866496096fdcb2195364960b6ddc32195364960b6f5c1219536496087fdc12ad5364960b2fc8c5ad5364960b6ddc32185364960b6f5c12185364960b6ddc321a3364960de5dc56cc8654960ae7dc521aaa54960aebdc421aaa54960aeddc321aaa54960aef5c121aaa549609e7dcb2195354960be3dc42195354960be5dc32195354960be75c12195354960ba7c8c5ad5354960ae7dc52193a1496087fecc56c9a5096087fdca2e5874c960ce7dca6d4864c96087fdca2e5854c960ae7dc52195a4c960aebdc42195a4c960aef5c12195a4c960ae7dc521aaa4c960aeddc321aaa4c960aef5c121aaa4c960a6fdc2269635056087fdbc2698250560a7edc22698250560c6fd656c89a4c560bb78c569d8460160be78c569d6460160fab9a76116460160fab8a56116460160fab9756116460160af78c569da360160bd78c569d7360160b778c569d9360160be78c569d6360160cef9a72ad6360160fab984591a260160fab9845917260160fab9845915260160fab9845922260160af78c569da160160bb78c569d8160160be78c569d6160160fab9845516160160d3f8c962d5160160fb71526055160160dbf15b6053160160fbd1326053160160b67dc52199254160b6ddc32199254160b6f5c12199254160ce7dca6d4864c160ae7dc52195a4c160aef5c12195a4c160ae7dc521aaa4c160aeddc321aaa4c160aef5c121aaa4c160be5dc5219534c160b67dc5219924c160b6ddc3219924c160b6f5c1219924c160ce7dca6d48648160de6dc26d48648160ceddca6cc8648160ded9c06cc8648160ae7dc52195a48160aeddc32195a48160aef5c12195a48160ae7dc52193a48160aeddc32193a48160aef5c12193a48160ae7dc521aaa48160aebdc421aaa48160aeddc321aaa48160be6dc52195248160beadc42195248160becdc32195248160bee5c12195248160be79c52193048160bed9c32193048160bef1c12193048160ff49535493048160ee75655e95144160def16b6d15144160fe716b5495144160fe71635495144160feb1645c94144160feb1645494144160cbb8ab6115460160b3f0c96053160160d6f09b5ad5144160 else 0xbf78c569d3160160de7dc36d48648160deddc56cc86481609efdcb2195348160bef5c12195348160bafc8c5ad5348160fed96354d3048160fed96c54d304816087fd1caed8a48100e3f98a605304810095fd7caed524410087fecc62d3a4410087fecc62d2a4410087fd5c4ed2a4410087fecc4ed2a44100e7e9524e92044100ceddb56c1a321960cafc8b5e96a54d60aafc8c5aaaa54d60aebdc421aaa54d60aafc8c5a9a454d60aafc8c5a9a254d60aafc8c5a9a054d6087fecc6d4a96096087fdcb2a55360960a77dc52a55360960b67dc521a3364960b6f5c121a3364960ceddca6cc865496087fecc6cc9a549608dfdcb1eaaa5496087fdca2e5835496087fdbc2698354960aebdc42193a1496087fd8c56c9a4c96087fecc56c9a4c960aeddc32195a4c960aebdc421aaa4c960fabaaa6116460160fab9a56116460160faba556116460160fab984590a260160fab9845905260160bd78c569d7160160fc75655c5515c160ceddca6cc8654160de5dc36d4864c160aeddc32195a4c1609eddcb219534c160bed5c1219534c160badc8c5ad534c160aebdc42195a48160aef5c121aaa48160baf88c5ad5344160fe71645495144160feb1641494144160feb1648894144160f749535493048100f761525452044100ae3d4c2c9a521960ae3dc52194a14960d3b89b6114160160c7fd5b6293148100f7f1835452044100de7dc06d4864c960deddc26cc8654160be7dc52193254160beddc32193254160bef5c12193254160be7dc52195348160beddc32195348160fb798554d8048160)
def getRecipe10 (i : Nat) : Nat × Nat := let a := packedAt rawRecipe10 (i * 64) 64; (a &&& 1125899906842623,a >>> 50)
def rawRecipe11 (i : Nat) : Nat := (if i < 4 then (if i < 2 then (if i < 1 then 0x481105837fcbd240882c1bfe4e92044160ffe2a290220b05ffabb61110582ffcc5ae8882c1fbe5d56444160fdf4aab2220b05ff98b55110583f7cb2aa8882c1fee6115444160f7f308c1a20b07df9875cd10583f7cb2ae6882c1fbe5917344160fdf2eab1a20b07efa5558d10583f7cba2c6882c1fbe5516344160fdf2e6b1a20b05ff98b54d10582ffcbdaa6882c1fbe5ad5344160bff576a9a20b07f798554d10583f7cb2aa6882c1fbe5915344160fef2a8a9a20b07fd98354d10583fecb9aa6882c1fbe58d5344160bff316a1a20b05ff95b50d10583fdcc2286882c1fbe5917244160fdf2c6b9220b077f97564910583bfd2ab24882c1dfe5d19244160eff2a8c9220b077f97364910583bfca9b24882c1dfe14d9244160eff286c9220b05ff98b54910582ffcbdaa4882c1f7e1ed5244160bff576a9220b07f797554910583f7cb2aa4882c1fbe5915244160fef2a6a9220b07fe98254910583ff4b92a4882c1dfe6495244160fdf2c829220b07ef96314910583f7cb2a84882c17fe62d4244160bff2b6a1220b07fb95450910583f7cb1a84882c1dfe6494244160fdf2c899220b05ff95b4c910583f7cb1a64882c1dfe6493244160fdf2c911220b07ef963889105837fca9b14882c1bfe5498a44160fdf2c6bd220b077f9925e910583f7cb1ab4882c1dfe6495a44160bff2b69d220b07ef9634e910583bfcc9274882c1fbe58d2a44160bff2b695220b07ff18754510583ff8c5aa2882c1ffc5ed5144160ffe576a8a20b07ff18554510583ff8ba2a2882c1ffc6d15144160ffe2a8a8a20b07ff18354510583ff8b9aa2882c1ffc6cd5144160ffe166a8a20b07ff15354510583ff8a1aa2882c1ffc8cd5144160ffe304a8a20b07ff17254510583ff8d92a2882c1ffc2c95144160ffe2a4a8a20b07ff14254510583ff8992a2882c1ffc0c95144160ffe444a8a20b07ff18a54510583ff8bd2a2882c1ffc5695144160ffe274a8a20b07ff12a54510583ff8c1a82882c1ffc5cd4144160ffe304a0a20b07ff17250510583ff8a9282882c1ffc1494144160ffe264a0a20b07ff222505105823fe5d262902011ffaed3a44100ddb964d190cb047fdb52a57358337e4d2d4a9ac19fd28ca164960cbf8f4cd2a4b05eddb321852582f7ad890c292c179f6d4860c960bdbb6643064b05ef5b121832583d7ac1302b0ac11ff6cc9a505608ffb644d282b067bc9a50941582bfa5cb0298ac1cfd625814c560cdfac64d242b05ef8ab59580582dfcc5aa8c02c1ebe6156360160f6f30aa9b00b07af98458580582bfc4da82c02c13bf2e965481609df974b1a40b07e756554510583bf84daa2882c1fbc5955144160efe324a8a20b07f7152545105837f8c52a2882c1dfc6494144160ff6284a0a20b053f8b960580583d78c0ac2c02c1f9c5955144160 else 0xc1dfea65804c160f7f30ac0260b077f99560130583f7cb2b00982c1bfe569804c160dff554c0260b07ef96360130583feca9b00982c1dfe649804c160f7f302c0260b077f99160130583f7cb0b00982c1ff64c5804c160fdf2c6b8260b077f9925c130583efcb8ae0982c1fbe585704c160ffb262b8260b076fd8959520583b7ec4ac6902c15ff66d5348160bdfad6a9a40b04ffcba54d2058377eb2b14902c1bbf58d8a481609ffb16bd240b06efd655e92058377eb1af4902c19ff54d9a48160cff8a6cd240b067fe336692058377e432b4902c1bbf5955a48160ddfac6ad240b06efc864e92058377eb2a74902c19ff66d3a481609ffab69d240b06efd634e92058377e43554902c1bbf596aa48160ddfac755240b057febb64920583b7eb1b24902c19ff4e99248160cffd54c9240b077ed8954920583bf74caa4902c1fbb2195248160fbd8f6a9240b077ed9b54920583fb6baaa4902c1dfb6555248160fddacaa9240b077ed9354920583f76b1aa4902c1bfb6295248160dfdaf4a9240b057fd9b4c9205836febd2e2902c1dfb5499148160ddfb14b0a40b07eed5258520582f7eb5aa2902c1ddf6555148160fcfacaa8a40b07f6d5254520582f7eb5a62902c1df764d3148160fdbac698a40b07eed6548520583f76b1a42902c17fb56d2148160eff2f2c0240b07bf98560120583bfccab00902c1fbe5958048160eff326c0240b07ef963601205837fcad300902c1bfe4e98048160dff554c0240b07fe95260120583dfcc0b00902c1dfe6458048160fdf2c2c0240b07fe92160120583bfcc4ae0902c1dfea657048160fbf2eab8240b07df9735c120583bfcc9ae0902c1fbe58d7048160dff314b8240b06ff93a5c120583ff4a92e0902c1f7e5c57048160eff322b8240b07ef9615c120583ff490ae0902c1dfe6253048160eff2f298240b07ef8864c120583bfccaa60902c1fbe5953048160bff31698240b05ff97b4c120583bfcc9a60902c1bfe6293048160dff2f498240b077f9924c120583ff4a9260902c1dfe6453048160fdf2c298240b07fd9314c120583ff490a60902c13ff62d7a44160ddfacabd220b067fd925e91058377eb2a74882c13ff62d3a441609ffaf69d220b04ffd5b4e91058377eb1a74882c1bbf5952a44160ddfac695220b06ff97a601105837fc9d300882c1bfe4a98044160bff316b8220b07ef9655c110583bfcc92e0882c1bfe6297044160dff274b8220b06ff92a5c110583f7cb2a60882c17fe56d3044160fdf2c698220b07fd9534c1105837fcc5260882c1bfe5e93044160dff25498220b077f98948110583bfcbca40882c1dfe6552044160fdf2ca90220b077f99348110583f7cb1a40882c17fe62d2044160bff2f690220b05ff95b48110582ffc9da40882c17feaed2044160ffd2a490220b06ff98a) else (if i < 3 then 0x26a9300b07ef96354980583fbca9aa4c02c1ffa6895260160ffd2e4a9300b07bf98414980583f7cb18a4c02c1fbe5954260160bff2b6a1300b07ef96350980583fdca1a84c02c1fbe5953260160bff2b699300b07ef9650c980583f7cb2c44c02c1efe6122260160fdf2c711300b06ff9a768580583dfcc2342c02c1efeaa98160160f7f34ec0b00b07bf9a560580583dfc52b02c02c1efe5d58160160f7f4aac0b00b07bf9a460580583dfcba302c02c1efe5518160160f7f346c0b00b07bf8a360580583dfcb9b02c02c1efe54d8160160f7f0a6c0b00b07bf94360580583dfd19b02c02c1efe6898160160f7f144c0b00b07bf97260580583dfca9302c02c1efe1498160160f7f284c0b00b07bf93260580583dfc19302c02c1efe8898160160bff356b8b00b05ffabb5c580583dfcc2ae2c02c1efe6117160160fbf2e4b8b00b07ef9a758580583f7ca9ac2c02c1fbe5496160160bff2f6a8b00b07bf98454580583fbca92a2c02c1ffc5c55160160bff2f6a0b00b07fb94250580583dfcc2a62c02c1efe6113160160bff35698b00b05ff97b4c580582ffcada62c02c17fe52d3160160bff57698b00b07fd9324c580583ff8a0a62c02c1efe6112160160bff2f690b00b05ff95b48580582ffc9da42c02c1ffc4c52160160cffd54c92e0b057febb64970583afeb9b24b82c1dbf58d925c160efe962c92e0b07cfd635c570583afec92e2b82c1bbf629615c160edfb24b0ae0b05efd6b54570583efab8aa2b82c177f5ed315c160bdfad698ae0b07edd634c570582f7ed990ca82c13ff62d7a54160ddfb14b1aa0b057fd8b64950583b7e43324a82c19ff6299254160cffaf4c92a0b076fd6564950583b7eb1b24a82c1dfd2c59254160affb36a92a0b067fd9a4c950582bfecda64a82c19ff6683254160cffb35112a0b076fd9258550582f7eb5aa2a82c1fb758d3154160affb3690aa0b077f99260150582bff5daf2982c17bf6cc864c160edfb12b2a60b06efd65629305827fec5af4982c1bbf5957a4c160ddf90cad260b04ffd8b569305827febdab4982c1bbf21aaa4c160ddfacb55260b06efd7a58d30583beec4aa6982c1df7a65534c160efb936a9a60b07f5d8554d305837eec52a6982c1bf75e9534c160affb16c9260b057fd7b64930583b7e43324982c1dbf595924c160cffb14c9260b067fd7a649305833fead324982c1dbf58d924c160efbaa6c9260b077f4b164930582bfecdaa4982c19ff669524c160febaa6a9260b067fd9a14930582bfecda64982c19ff66a224c160ebfaf2b8a60b057fd7b64530583beea9b22982c1fb754d614c160edfb24b0a60b05efd6b54530583bbecaaa2982c1f9f595514c160bdfad698a60b077dd794c530583beecaa62982c1fb7595314c160bfbab698a60b07fd5814c530582bfecda42982 else 0x1583f3eb1aa4a8ac1fdb6095254560ddfad4a12a2b06efd6a4c95158377eb5064a8ac1bbf5aa2254560f7eb04c0aa2b067fc9a60d415833fe4d2e6a0ac19ff6697250560cff934b9282b06efd6a5c941583bdeca2e4a0ac1faf5917250560cffaf4c9282b067fd9a549415833fe4d2a4a0ac1def6515250560fd7ac8a9282b067fd9a149415833fe4d0a4a0ac1def6505250560fd7ac829282b077bd7950941583f5eb2a84a0ac19ff2693250560cffb3511282b067fc9a8894158377eb5444a0ac1def6522250560fd7ac911282b04ffd8b5e9315827ff5daf498ac19ff6257a4c560cff972bd262b067fe995e9315833fecaaf498ac19ff6517a4c560ddfac8bd262b06fecb25e931583b7eb293498ac19ff61c9a4c560ddfae8b5262b06efd545a9315827febdab498ac1bbf5915a4c560ddfacaa5262b06efd65aa9315836febd2e498ac19ff5e9924c560cffab4c9262b067fd9a5493158377eb52a498ac1bdf569524c560ddfad4a1262b077dd794c931583f6eb2a6498ac1dfd269814c560dfeab4c0a62b07bf58260531583fea9930298ac1bbf5957a48560ddfac6bd242b067fd74669215833fea9b3490ac19ff14d9a48560cffa86cd242b067fe33669215833fea993490ac13ff62d5a48560ddfac8ad242b06efd635692158377eb2a9490ac1bbf5953a485609ffaf69d242b04ffd5b4e92158377eb1d5490ac1fbd5953148560dfeb1498a42b07afd8558d80583dbec2aa6c02c19ffaa99260160e7fb0ac9300b07bf5814c580582ffd5db4ec02c1fde2d5a760160dff34ed2b00b07bf9a761580582ffcd5aeac02c1f7e69d7560160eff34ecab00b07efaaa59580583f7cd3acac02c1fbe6956560160fdf2cad2300b07bfaaa61180583dfcd3b08c02c1efe6958460160f7f14ac2300b07bf97561180582ffcd5ae8c02c1fbe5957460160fdf34eb2300b06ff9a768d80583f7cb2b46c02c1fbe594a360160bff356b9b00b07df9a75cd80583bfccaae6c02c1fbe5957360160fbf2e8b9b00b07ef9645cd80583bfcd3b26c02c1fbeaa96360160fdf34eb1b00b07ef9a558d80583f7c52ac6c02c1fbe5d56360160fdf4aab1b00b07ef9a458d80583f7cba2c6c02c1fbe5516360160fdf346b1b00b05ff9ab54d80582ffcbdaa6c02c1dfe66d5360160fdf2d6a9b00b05ffabb54d80583dfcc2aa6c02c1fbe5915360160ffb346a9b00b07fd97354d80583f7cb2a86c02c17fe56d4360160fdf2cb19b00b06ff9a768980583f7cb2b44c02c1efe611a260160fdf2c6d1300b07ef96528980583dfcc2144c02c1fbe58ca260160bff356b9300b07ef9655c980583dfcc22e4c02c1fbe58d7260160bff356a9300b05ff97b54980583efc3daa4c02c17feaed5260160fef14aa9300b07bf98554980583fbcbaaa4c02c1fbe5915260160eff3)) else (if i < 6 then (if i < 5 then 0xf1eaaa54960ddf90d552a4b057fcb961152582bfec5b28a92c15ffaed9454960ebf8f4ca2a4b06efd8a5915258377ebd2c8a92c1f3f1e96454960ddfd54b22a4b07e7d75591525836fe3d348a92c15ff2e58354960cff934c1aa4b075fc7a64d52583bde5a326a92c1dbf5919354960ddfaf4b1aa4b06efeaa58d525836fe3d346a92c1b7f1e8a354960eefb12a9aa4b0777e9954d52583f3e432a6a92c1ddf66d5354960eef936a9aa4b07e7d6b54d525837bec52a6a92c1f5f1e95354960eefb34a9aa4b0777d9454d52583f3eb22a6a92c1fd760d5354960feb946a9aa4b07f6cb254d52582bfecda86a92c17bf5ad4354960cff93519aa4b057fcb960952583bf6dcb04a92c1dfb2e58254960efdd32c12a4b07dec7a60952583bf6cd304a92c1fdb2d58254960fedaeac12a4b077ed9460952583f76b2304a92c1efb60d8254960fedaa6c12a4b07eed645c952583f76b1ae4a92c1fdb54d7254960dbf8f4d0aa4b06dfc7a68152582bfea5d32292c15ff4ee9914960bdfb66430a4b057fd8b65052583bde5a326292c1dbf5919314960affb36a18a4b05efd6b50c525833febcb14a12c19ffa658a50960ddfacabd284b067fd75669425833ff2ab34a12c1bbf596aa509609ffb1755284b04ffd7baa9425827feadd54a12c13ff46eaa50960fd7acaba284b057fcb961d32582bfeadd32992c15ff4ee994c960affa574ca64b05efdb521932582f7ed990c992c15ff2e5854c960cffaeacd264b067fd74669325833fec2934992c1bbf2195a4c9609ffb16ad264b06efd64569325837f6ad304992c13ff6e9524c960affab74c864b05efdb521832582f7eda90d112c17bf6cc8688960aff972c2c44b057fd8b65222583f5ec22c9112c1def2d19388960edfb28b1c44b057fd9b54e22582f7eb5aa7112c15ff66d4388960bdfad6a1c44b073fd895cd81583df6c12a4c0ac1cff6254260560ddfd54b2ae2b075fd7950d71583afebcc66b8ac19ffaa97564560ebfb0eb9b22b067feaa5cd915833ff552a6c8ac1df760d5364560cffd5429b22b067fd7a50d915833febd466c8ac19ffaa97264560cffd54a9322b075fc7b54991583bbea9aa4c8ac1dfb6095264560cffd5429322b057fd8b509915833ff55264c8ac19ffaa83264560fd7b08aa2c2b07cfd875cd6158377ed5aa6b0ac1fb760d5358560bdfd76c12c2b07afd8360961582f7ec5ae4b0ac1dbf5d19258560edfaa6c92c2b076fc5364961583b7ea1b24b0ac1dbf8cd9258560bdfb16a92c2b07cfc7b54961583f3ea9aa4b0ac1fbb6095258560bdfb16a12c2b05efd8b4c961583f76c1264b0ac1bbf5a974545609ff974b9aa2b06efd6a5cd5158377eb5286a8ac1bbf5aa33545609ff974c12a2b067fc9a6095158377eb52e4a8ac1f5f1ed5254560fcfac8a92a2b0777d935495 else 0xa408057fd3b68520403bfcb2a6090201dfe62d3048100eff2b6982408077f98a4c120403bfcad26090201dfeaa93048100eff302982408077f9514c120403bfcd8a6090201dfe6853048100affd76b9a208075fd875cd10402bff5db04882015ffaed5244100efdb04a92208057fd8b4e9104033fec2a74882019ff62d3a44100cffab69d2208067febb4e9104033fec1274882019ff5493a44100cffb649d2208067fd834a9104033fea9a54882019ff62d2a44100cffa76952208067fd83aa9104033feb9d54882019ff60aaa44100cffaa5552208067fd32aa910403bfcc2a4088201dfe60d2044100eff2a6902208077f98b48110403bfcada4088201dfe4ed2044100eff314902208077f95a48110403bfc9d24088201bbf6cda521960ddfb64d290cb06efdb568c8658377ed9346432c1bbf6c1a321960affab74cb0ab057fd4ba6585582bfe9dd32c2ac15ff4ae9961560affa974caeab057fd3ba6575582bfe95d32baac17bf6cc8695560cffb14bab28b067fd8a95594583f5ebab08b22c15ff5ee9960d60affab74cb06b057fd3ba6583582bfe95d32c1ac19ff2a57560d60affab74cae6b057fd3ba6573582bfe95d32b9ac19ff2a5855cd60affab74caa6b057fd3ba6553582bfe95d32a9ac17bf6e88654d60bdfb6a432a6b05efdb321953583d7e45ad4a9ac1dbf6256a54d60edf972b52a6b06efd8a5a95358377ebd2d4a9ac1bbf2696a54d60ddfad5552a6b06efc86aa953583f3eb530aa9ac1bbf6296454d60ddfaf4b22a6b06efeaa59153583f3ec2ac8a9ac1bbf5a9a454d60efbb72c1aa6b077de9960d53583beecd306a9ac1fb75a98354d60efbb28c1aa6b07edd6460d5358377eb5344a9ac1bbf5a8a254d60ddfad4d0aa6b06efd6a68153582bfe95d3229ac15ffaed7950d60bdfb6a43466b057fd5ba6582582bfea5d32c12c15ff4ee9960960affa574cb04b067fca95d5825833fe54caac12c19ff2a553609609ff956a9b04b057fc9b54d82583deec1aa6c12c15ff56e995c960affa974cae4b057fd8b65172582bff5db28b92c1faf611645c960aff972c1ae4b077bcb464d72583b7eb2326b92c1dbf651635c960affb36a1ae4b05efd6b50d725833fec52e8c92c19ffaa97464960edfae8b1b24b067fd8a54d925833ff552a6c92c1dbf2195364960affb16a9b24b067fdab54d92582bfe55aa6c92c1dbf5ad5364960affd76a9b24b077dd8354d925833fec50a6c92c1dbf2185364960cffb14a1b24b076fd6550d925833fec5466c92c1dbf21a3364960efeae850b24b077f55328592583bfa29942c92c1dfd50ca164960efec6650b24b057fd5ba6552582bfea5d32a92c15ff4ee9954960affa574caa4b05efdb521952583afec48f4a92c1d7fa647a54960dbfb143d2a4b06dfc7a66952583afe3d334a92c1b7) else (if i < 7 then 0xbf6caa42902c17fe62d7048160fdf2cab8240b077fa994c120583f7cb1a60902c1ff654d3048160eff466c9220b07ef96354910583ff8c22a2882c11ff2e953481008ffd76c52408047fd8baa9204023fe9dd54902011ff46eaa48100efb2a6982408067f98a4c120403bf4a926090201df64c530481008ffb169d2208047fd8b4a9104023fe9da54882011ffaed2a44100efd2a4902208067f93a48110403bf8a8a40882011ff4eeaa5e560dcfd76d290cb06e7db36948658373e59b4a432c1b9f6c9a521960dcf964d290cb06e7db06948658376f5db46432c1bb76d5a321960ddb96ad190cb06eddb268c8658376ed8346432c11ff6cca9615608ffb6454b0ab05e7db521a55582f5eda10d2aac17b76cc8695560bdeb62434aab047fdb52a5835823fed9152c1ac13bf6e88654d60bcfb6a432a6b05ebdb421953582f6ed990ca9ac17bd6c48654d60b5f916b52a6b05e7db521853582f6ed990c29ac17bd6c48614d60bcfb6a43466b05eddb321a33582f7ad890d19ac11ff6d4a9609608ffb6654b04b056fdb3219925823fe55aa6c92c179f6d48654960bd7b68432a4b05eddb321952582f7ad890ca92c11ff62c9a549608ffb664d2a4b05e7db521852582f5eda10c292c11ff62c9a509608ffab64d284b05e7db521932582f5eda10c992c17b76cc864c960bdeb6243264b047fd8b269325823fead934992c179f6d48688960bd7b6843444b05eddb321a22582f7ad890d112c19bf2a5655c560cdf934b1a82b066fd6526931582fbc5ab4ec02c1eee6115460160bdf156b1b00b05bf98b54580583df8c0aa2c02c16fe62d4160160f77308a0b00b07bf1814c580582f3eda90ca82c17af6d08654160bdbb66432a0b05ef5b121950582f3eda90c982c17b76cc864c160bdeb6243260b05e7db521920582f5eda10c902c17b76cc8648160bdeb6243240b07ef16b54510583f78b22a2882c1fbc58d5144160fde2c6a0a20b047bd4baa930402b6ed990cc92c15bd6c48664960f57308b2300b07eb16450510583bfea9b0488201dff60d5244100dffb14992e0b07dfd835c570583bfec4a64a82c1dffa653254160fdf90c992a0b06ffeaa4c950583f7eb2a64a82c17ffaed3254160fdfac6992a0b077fd924c950583f7e992c2a82c1ffe4c98054160ffbaa699260b077fd8954d20583bff4caa6902c17ffaed5348160fefb0aa9a40b07fdd8354d205837fea9af4902c1bff54eaa48160fdfaa6b0a40b07fed5348520583ffcc1ae0902c1ffe60d7044160fff264a8220b067feaa60530402bff5dae2982019ffaa9714c100affb16d0a608057febb58d204033fed8b14902015ff56d3a48100cffac7552408067fd53aa920402bff5db02902019ff6e98148100e7fb14c0a408067feaa605204033ff5526290201dfe6c13148100affb16d0 else 0x1dff549814c100effaa6c0a408077fd7454d92583ffcd3a62c02c1bff629315c160fdf90ca9a40b07efd6b54d20583f7eb2aa6902c1fbf58d5348160effaa6c9240b07ff95360120583ffca9ae0902c1ffe54d3048160fff2a690220b075fd875c5304033ff5db14902019ff6293148100cffd54bab28b07ebe5561164582bfe9dd32b92c17bf6cc8654960fd7b08b22a4b07cfc7a58d52582bff5db28292c1faf6116414960cffcaa4d284b067fe5526932583b7eb2327112c19ff2698250560dbfb0ebd262b06efd655e931583dfd2ab08c02c1efe6115260160fbf34eb8b00b067fd8a649705836fec52e2b82c1f3f595715c160bdfb6a43260b07edc8654d30583f6eb5aa6982c17bf6d48648160bdfb6643240b07f6d5354920583)))
def getRecipe11 (i : Nat) : Nat × Nat := let a := packedAt rawRecipe11 (i * 53) 53; (a &&& 1099511627775,a >>> 40)
def rawRecipe12 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x2ffd7a54560dff669515837fc9a54560fbf5a951582ffeaa54560dff65151583efd6454560dff64d51583efd6354560fdf54951583ff58154560bff5e9415837fd9250560dff625315837fd794c560dffa65315837fd954c560dff65131583efd644c560bff629315837fd9a4c560dff26931583efd6a4c560bff56931582ffd4a4c560bffaa9315837fd924c560ff74c9315837fd8948560dff5e5215837fe9948560dff65521583efd6548560dff65121583efd6448560dff64d21582ffd8a48560bff5e9215837fd9a48560bff56921582ffd4a48560bff4e921582ffeaa48560ffd4c521582ffeaa60160dffa6580583bfd8560160dff65580583efd6560160dff64d80583efd6360160eff605805837fd9160160fbf58580583ffaaa60160ffe69580583ff8a560160ffe5d580583ff89560160ffe95580583ff9a460160ffe5d180583ff95460160ffe68d80583ff8a360160ffe5cd80583ff89360160ffe14d80583ff94360160ffe8cd80583ff9a260160ffe28980583ff97260160ffe24980583ff85260160ffe50980583ff93260160ffe0c980583ffa2260160ffe68580583ff95160160ffe50580583ff92160160dffa6570583efd635c160fbf585705837fd8954160dffa6550583efc8654160bff62950582ffd7a54160bffaa9505837fd9554160fbf595505837fd9354160fbf58d505837fd9254160dff64550583efd6154160fdf54550583ff98054160dff625305837fd794c160dffa65305837fd954c160bff62930582ffd7a4c160bff56930582ffeaa4c160dff64d305837fd924c160dff64530583efd614c160ff74c5305837fd8948160dff5e5205837fe9948160dff655205837fd9348160bff62920582ffd7a48160fbf1a920582ffd5a48160bff4e920582ffeaa48160dff64520583efd6148160ffb485205837fd8944160dff5e5105837fd9544160fbf595105837fd9344160fbf58d105837fd9244160bff62910582ffd7a44160bff56910582ffd3a44160bff4a910583ff55144160ffe60110583ff97044160ffe54110583ff93044160ffe61d10583ff98544160ffe5d510583ffa5544160ffe5d110583ff95444160ffe60d10583ff97344160ffe14d10583ff94344160ffe8cd10583ff98244160ffe5c910583ff85244160ffe50910583ff93244160ffe0c910583ffa2244160ffe62910583ff97a44160ffe56910583ff93a44160ffe4a9105827feaa625609ff62a995827fd1aa65609ffaa9955827fca9611609ffaa993583ef8a058d609ff269535827feaa649609ff2a5815833fd89605609ff2a5715827fd8a64560fbd605615827fd9a545609ff269515827fd9a4c5609ff26931582efd6a4c5609ff26921583bf98560160dfe65580583ef96460160dfe64d80583ef96160160fbe59510582ff98a44160 else 0xfff5c910583ffd5244160fff14910583ffd3244160fff0c910583ffe2244160dff685304037fd8a48100dff4e9204037feaa48100dff685204037fd7344100dff609104037fd5244100dff4c9104037fd3a44100dff4a9104037fca562560dff28d895837fca262560bffaa9855837fda961560dffa65855837fd895d560dffa65755837fca265560dff62655583efc8695560dffa65845837fd895d160dffa65745837fd955d160fbf595745837fd8565160dff5d594583efd8559160fbf5d564583efe5559160bffaa9835837fda960d60dffa65835837fd9460d60fbf591835837fe995cd60fbf591735837fd7464d60dff289935837fd7924d60fbf59493583efca258d60dff625535837fe9954d60bff62953582ffd7a54d60dff669535837fc9a54d60bffaa953583f7d8554d60dff651535837fd8914d60dffa6453583efc8614d60dff625435837fd7950d60dffa6543582ffd7a50d60dff626335837fd798cd60fbf21a33582ffeaa60960dff6a5825837fca960960dff5e5825837fe9960960dff65182583efd6460960eff60d825837fd895c960dffa65725837fd955c960fbf595725837fd945c960fbf591725837fd935c960fbf58d725837fd8364960dff28d925837fc5364960dff50d925837fe3364960fbf59492583efd6324960dff625525837fe9954960bff62952582ffd7a54960dff66952582ffeaa54960fdf5d5525837fd9454960dff64d52583fed7254960dff624525837fe9914960fbf218525837fd9414960fbf590525837fd9314960fbf58c525837fd8950960dff5e5425837fe9950960dff65542582ffd7a50960bffaa942583fbd7450960dff625325837fd794c960dffa6532583efc864c960dff65532583efd654c960dff65132583efd644c960bff629325837fd9a4c960bff56932582ffeaa4c960ffb609325837fd890c960dffa6432583efc860c960dff65432583efd650c960dff62622583efc8688960dff65622583efd6588960fbf592225837fd9388960fbf58e22583bfd8260560bff62971582ffeaa5c560dff625715837fe995c560dff655715837fd945c560fbf591715837fd935c560fbf58d715837fd8764560dff615915837fd7564560dff955915837fd8464560dff5d1915837fd8364560dff5cd915837fd5364560dff14d915837fd4364560dff8cd915837fd8264560dff5c9915837fd5264560dff149915837fd4264560dff4c9915837fc3264560dff88991583efd8758560fbf61561583efd7558560fbf95561583efd8458560fbf5d161583efd5458560fbf60d61583efd7358560fbf54d61583efc5358560fbf50d61583efe3358560fbf5c961583efd5258560fbf14961583efd4258560fbf4c961583efc3258560fbf889615837fd8954560dff5e5515837fe9954560bff6295158) else (if i < 3 then 0x83ffd8554560fff5d151583ffda454560fff60d51583ffd7354560fff68d51583ffca354560fff54d51583ffd4354560fff8cd51583ffd7254560fff68951583ffca254560fff54951583ffd4254560fff4c951583ffc3254560fff88951583ffda054560fff60d41583ffd7350560fff5c941583ffd5250560fff14941583ffd3250560fff88941583ffd854c560fff5d531583ffe554c560fff61131583ffd744c560fff55131583ffd8a4c560fff5e931583ffd5a4c560fff16931583ffd4a4c560fffaa931583ffd834c560fff54d31583ffd824c560fff5c931583ffd524c560fff14931583ffd424c560fff68931583ffca24c560fff4c931583ffe224c560fff68131583ffd8748560fff61521583ffd7548560fff95521583ffd8448560fff5d121583ffd5448560fff60d21583ffd7348560fff14d21583ffd4348560fff8cd21583ffd8a48560fff56921583ffd4a48560fff4e921583ffd8248560fff54921583ffd3248560fff68121583ffda760160fff69580583ffd7560160fff95580583ffda360160fff5cd80583ffc5360160fff8cd80583ffda260160fff5c980583ffd5260160fff14980583ffd3260160fff0c980583ffe2260160fff68580583ffd5160160fff48580583ffd935c160fff8cd70583ffd825c160fff68970583ffd925c160fff4c970583ffd815c160fff68570583ffd515c160fff48570583ffd8754160fff62550583ffd7954160fff62950583ffd8554160fff65550583ffd6554160fff60d50583ffd7354160fff64d50583ffd6354160fff68d50583ffd5354160fff8cd50583ffd8254160fff5c950583ffd9254160fff58950583ffda254160fff54950583ffc3254160fff88950583ffd8154160fff5c550583ffda154160fff54550583ffd3154160fff48550583ffd894c160fff5e530583ffd854c160fff5d530583ffd954c160fff59530583ffe554c160fff62930583ffd7a4c160fff56930583ffd834c160fff5cd30583ffd934c160fff58d30583ffd824c160fff5c930583ffd924c160fff58930583ffd524c160fff14930583ffda24c160fff4c930583ffe224c160fff60530583ffd714c160fff54530583ffda14c160fff4c530583ffd214c160fff62520583ffd7948160fff61520583ffd7548160fff65520583ffd6548160fff95520583ffd8348160fff5cd20583ffd9348160fff58d20583ffc5348160fff8cd20583ffd8a48160fff5e920583ffd5a48160fff16920583ffd3a48160fff0e920583ffeaa48160fff60920583ffd9248160fff58920583ffd5248160fff4c920583ffd8148160fff5c520583ffd5148160fff4c520583ffda148160fff48520583ffd8744160fff61510583ffd7544160fff95510583ffd8344160fff5cd10583ffc5344160fff8cd10583ffd824416 else (if i < 4 then 0x60fff69d83583ffda560d60fff5d583583ffc9560d60fff95583583ffd7460d60fff68983583ffda160d60fff68183583ffda95cd60fff2a573583ffe995cd60fff61573583ffda55cd60fff65573583ffd945cd60fff5d193583ffd7364d60fff61493583ffd8954d60fff5e553583ffe9954d60fff62953583ffd7a54d60fff66953583ffc9a54d60fff5a953583ffeaa54d60fff61553583ffd9554d60fff65153583ffda454d60fff60d53583ffd9354d60fff68953583ffca254d60fff68553583ffda054d60fffa6453583ffd8950d60fff5e543583ffd8550d60fff5d543583ffd9550d60fff95543583ffd798cd60fff61633583ffeaa60960fff69d82583ffca960960fff69582583ffca560960fff5d582583ffc9560960fff95582583ffda460960fff5d182583ffda360960fff28d82583ffc9360960fff14d82583ffd4360960fff8cd82583ffda160960fff68182583ffe995c960fff61572583ffd845c960fff65172583ffd835c960fff54d72583ffd435c960fff5d192583ffd7364960fff54d92583ffd4364960fff61492583ffd8324960fff54c92583ffd5358960fff14d62583ffe3358960fff62552583ffd7954960fffa6552583ffd8a54960fff5e952583ffd9a54960fff26952583ffd6a54960fffaa952583ffd8554960fff65552583ffd7454960fff65152583ffda454960fff64d52583ffc9354960fff68d52583ffca354960fff54d52583ffd4354960fff8cd52583ffd9254960fff68552583ffda054960fffa6452583ffd8414960fff65052583ffd8314960fff58c52583ffd4314960fff62542583ffd7950960fff5d542583ffd9550960fff95542583ffc5a50960fff64d42583ffd9250960fff61d32583ffd894c960fff5e532583ffe994c960fff61532583ffd754c960fff65532583ffc954c960fff59532583ffe554c960fff5d132583ffd944c960fff62932583ffd7a4c960fff66932583ffc9a4c960fff5a932583ffd5a4c960fff16932583ffd4a4c960fffaa932583ffd834c960fff64d32583ffd534c960fff60932583ffd924c960fff54932583ffda14c960fff68132583ffe990c960fff61432583ffd650c960fff61622583ffd6588960fff61222583ffd9488960fff60e22583ffd6388960fff54e22583ffd4388960fff5d581583ffe5560560fff5d181583ffd7360560fff54d81583ffc5360560fff50d81583ffe3360560fff5c981583ffd5260560fff14981583ffd4260560fff4c981583ffc3260560fff88981583ffd8a5c560fff61571583ffda55c560fff61171583ffda45c560fff60d71583ffda35c560fff54d71583ffd435c560fff8cd71583ffd525c560fff50971583ffda05c560fff5cd91583ffd5364560fff54991583ffd3264560fff62951583ffd7a54560fffaa9515 else 0xfff5d153583ffd5360960fff61152583ffd8354960fff58d52583ffd8254960fff61d42583ffd8454560fff60951583ffd8250560fff61d31583ffd5348560fff54d80583ffd7160160fff4c580583ffd315c160fff4c950583ffd874c160fff54d30583ffd8748160fff54d20583ffd5344160dff605304037fd714c100dff58d204037fd5348100dff605204037fd3148100dff60d104037fca35e560dff95594583efd7458d60fbf21953583efd6a54d60fbf59153583fdd8354d60dff5d1925837fd5364960fbf21952583dfc7a54960fbf59152583efd6354960fdf54d52583fed8254960fbf59542582ffd8a50960dff65222583dfd875c560fbf59571583efd8258560dff64d41583efd6350560fef50941583efd654c560bff5e931583ff5814c560fbf58d215837fd9260160ffe69d80583ff95360160ffe54980583ff97160160ffe4c5805837fd925c160f7f5c570583efc864c160fbf59530583efd634c160ff754d30583ff9804c160ffe5c130583efc8648160fbf59520583efd6348160dff64920583fed5248160ffe60120583ff97048160ffe4c120583ff92044160ffe61110583ff95344160ffe549105827feaa58100dbf595604036fd63581009ffaa9304027fd8a481009ffaa9204037f930481009ff4e9104027fd2a441009ffaa9104037f920441009ffaa9795827fd7aa65609ff56a995827fd4aa65609ff4ea995827fd2aa6560bbf69486582efda3219609ff2a585583ef8a0595609ff629945827fd7a651609ffaa994583ebd84591609ff2a5835827fca95cd609ff5e9935837bca464d60dbf591935827fd9a50d60bbf5a9435827fca9609609ff629925836fc8664960dbf58d925837f4a1649609ff269525827fd9a509609ff269425827fd9a4c9609ff269325835fd795c5609ff5e9915827feaa64560dbf64961582efd6a545609ff669415827fc9a50560def65141583ebd64505609ff66921583ef96560160efe61180583ef96360160efe605805827fd9a541609ff669305827fd9a48160fbe59110583ef96344160dfe64910583ff15144160ffc50510582e7da521960baf69086582edda321960bbd68486583ffda461560fff68d85583ffda261560fff68585583ffda061560fffa6575583ffd7561160fff95584583ffd895d160fff61574583ffd955d160fff5d594583ffe55651)))
def getRecipe12 (i : Nat) : Nat × Nat := let a := packedAt rawRecipe12 (i * 42) 42; (a &&& 1073741823,a >>> 30)
def rawRecipe13 (i : Nat) : Nat := 0xffebcac1ffe99583ffb0ab07ff59560ffec22c1ffd74583ffb28b07ff60d60ffeb9ac1ffd63583ffaa6b07ff50d60ffec12c1ffd62583ffaa4b07ff50960ffe992c1ffd81583ffae2b07ff54560ffea0ac1ffd31583ffa42b07ff60160ffeb82c1ffd50583ffa60b07ff48160ffe882c17fd60402ffa60805ff48100bfe882017fd89582ffaf2b05ffa6560f7e432c17fd95583dfacab05ff65160f7eb22c17fd93583dfac6b05ff64960bfec8ac1efd61583ff300b07fe44160ffec4ac1ffd75583ffb2ab07ff25560fff2aac1ffd93583ff926b07ff14d60fff19ac1ffd72583ffb24b07ff24960ffe292c1ffc32583ffc44b07ff64560
def getRecipe13 (i : Nat) : Nat × Nat := let a := packedAt rawRecipe13 (i * 31) 31; (a &&& 1048575,a >>> 20)
def rawRecipe14 (i : Nat) : Nat := 0xffd607fd00
def getRecipe14 (i : Nat) : Nat × Nat := let a := packedAt rawRecipe14 (i * 20) 20; (a &&& 1023,a >>> 10)
def opsAndMask : Nat → Nat → Nat × Nat
  | 9 => getRecipe9
  | 10 => getRecipe10
  | 11 => getRecipe11
  | 12 => getRecipe12
  | 13 => getRecipe13
  | 14 => getRecipe14
  | _ => fun _ => (0,0)
def requestedBudget (k i : Nat) : Nat := 1 - packedAt (signedBudgetData k) i 1
def signedBase : Forest := ⟨511,14,fun j => deadsamples[j]?.getD (0,0),signedColumns,deadautos,
  signedLevels,signedIndices,shapeCut3640,shapeCut3640_sound,some opsAndMask,some signedRules⟩
def signedCertificate : SignedForest := ⟨signedBase,requestedBudget,[(17,272)]⟩

def rankDictionary (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x1752049201742224000f83049c10231046201271011000f61424000f83209400f85a09800f85049c80453046680042046601274049601253049080453090000f32282200f50049240480046504943114100f93049420384049304430705400f43046402342046280042046810273a48800f21e28600f40046802752046c04853e05800f43046804853046804587046610270046620230049010362632620f32049220281049410362046004853049604430024000f83412000f32e68a40f40049601853022000f62c24c00f83046e08054c24000f83f81e01f3204d200410046610720046402852046004581049204470046202852046002852046102396046140391046282842505400f65046210270781601f32722600f72682080f28282080f28046e20320f01800f43046120640c12800f32046248054304000f74e90a00f50668240f40088200f82305000f43049504560722700f72046208054a05000f75822000f72432420f32046210720268240f40548100f94609000f21209200f21049240084482400f50780600f32049420473046401641702000f324d0440f50049700762046604687046640751049110192430400f83409400f21049700241049140420049a80420a09000f85046508054049480354222000f62409000f21046010753224000f73305200f65205000f43046c02342046410653046601381301200f61046008162046410573609400f211a8080f40605400f75ad0240f50a41800f85049680420046608054046404587046002752605000f437c0700f21049604470049204074701600f61049280420049601742702400f64046404853205000f75830800f83468440f40750500f50049700142049640084382000f54e05c00f430468023422d0240f50046410273109000f75682600f50302000f64222000f72411400f61046001231a90200f50822800f7204960858040a000f86049020473628600f40641600f84046110260605000f75d80c00f32046004643046410563046408462049020374030000f8360a400f86e05000f43150100f50528500f40728300f40046004587501400f61009000f21e68240f40e44c00f83e05800f75049820384528100f40c22000f72105000f6504942037440a400f86424400f83305000f650a8080f40a68240f40c24800f83728100f40101000f61612600f32046402752212000f32049720271a28200f40812800f32e05000f75046010573228200f40702000f64049020384209000f21212200f32046008574422000f72609400f85209000f85690600f50609000f85c32c20f32046010273628200f40422400f72049e04430550500f50e09800f85704400f74412400f32c12c00f32e28200f40e09000f85290200f50704000f74a90a00f50012000f32022000f72e28a00f40 else 0x1009400f85222200f72432402f83314100f306a8480f84582000f32046102496609200f21046104943049408587046601865309000f75505000f65046102392405400f18049380142049380241630600f80705500f65049408120046684843412400f72181000f53046101374046210263049201752046002582190080f30018000f68049104064388080f40c22c00f726d0240f50049688081660600f100c0100fa3750300f50049701352049701342224200f73622200f62722200f7204da00410e05c00f75350100f50641600f48049301642521500f79304000f63890800f32e09000f21046648052049700251049641382049604830049300031049300251046640341682200f50049440243046708052622000f62049700742049040342018000f72046180150109000f21c88400f8504664805404d400675405000f75108080f6a205400f43490400f32504400f61030000f73524400f10702400f32090000f500460016811a2100fa2514500f39105000f4300a000f40005000f75182000f3221a210fa2211000f61a05000f4304964048004944048004610293004902017204960457004e600572049440782049640287046008754049620172124000f10046004576705400f65046301731605400f43424400f7304641075330a400f70222200f62580000f64049010231a05800f43824800f83e09c00f8504ee00850668440f40046402582046404687046601684046402382046240751645404f85350300f50550100f50612400f32622400f8620a200f864e80a0f84505000f436c0600f2169a608f08005000f43049100251049001853049080354049204430014000f100b0080f90312300f32046204041214200f10290080f30049c20182382000f32321300f7469a090f280460a0820046001384049208580094080f30f81880f43534120f39046002382682400f50046c04587046604053228600f400461400420494048760466203200466101600494027650496403820496013520493007620492027650490202710492080810466408720466086540494203640495044300464801650460403410490081200460023420a4000f10c22800f72046408754134120f39168120f49148100f49046448984049304064728500f40244000f83645601f8304970456020a200f28682600f08305200f43328100f40328300f40128100f40624400f83705600f65514100f93046a80042049c20384d04800f75049e4038204651026004640186504940a968049604074049608520046440751049640782046700276046404643049040243046004851046680682046101264409000f85049480453046708054690200f50488600f82049608081046502496046602830049620671046140931046408162049700631046004541e45c04f850496) else (if i < 3 then 0x6080520464048510464405710460106530496013424d0601f32514100f39046202582049001752049320671046201478046201741046201468046602570541500f4904624034160a000f8640a000f40414000f10294080f30612200f320493080710491a02a1494080f83049020261728200f62422000f6204970453060a600f28046502392309200f2104620275204620123104962027104d200132241200f84049202863046601468641200f84534120f93282200f080490400840462028420462084620460016410462040810490a0310104000f75301000f61046208654112000f62209800f85580400f32046640831622600f72490400f50014000f51628a00f40228a00f40046410720490440f50049008587046010263128300f40049500570609600f21014000f61046601681430000f73509000f752c0200f32046202652046404051028000f4004601016004910015204600265210a100f7034a308f07e68e01f72432410f786686c0f40205400f75548500f49046a04041049a04430812000f32046802382e81800f2104668016504920278504920278304640168404942067104648086204d600410049402364046605863049602765046010853049104479046640381049080651049300130622000f72049604530049602483046604843049604730046601231508000f2140a400f40414400f1004644018504970027604670027304d600132049204530309000f21390080f30e90e00f50049e012530464016816d0440f50049240782046640431028000f72428400f40590500f90049610231241000f85049220182360100fa1750700f50046201274049701253302000f32418400f72534522f3904900174204930015204d400186046244053409400f85628400f40548500f9460a600f78644400f83628200f72046700720694080f38046604051049c20382c8a402f85ed0240f50c30c00f83ac0800f85049a08580b01800f43049810231c28800f72e41800f85049644470049108570488400f8504640127404951029104950869104960818004e60038604940246304912017604e600380282240f50049680651049501352049608871024000f7330a200fa2750100f5004944008450a200f70405100f7310a400f70094080f8304932027160a600f80049101642309200f75424000f73624000f73411000f61046502942384000f6420a200f40009000f85046422342046284843325301f7a3e0380fa1568120f49605600f83f01c00f436d0640f50e48400f21c30400f83e44400f83049880354824000f83046408164046440341046601831550500f32049102963046008462046601271046604841049502963049204570046240431046202830046004463049402863046640571046310260046610120482000f5004620138 else (if i < 4 then 0x3104944457004964457004922036404942028104661086004950025104950076204910232904924084004910236904902017604604075104e20038604920818004930027604921036204601498104930024104d100310788080f400493022a304922017204620a780046001541046610653390300f50049208821694210f81049404476049700672619408f610496040186a0080f380490202430490844601c2140f32046202342668640f40a41000f85e90600f50049c08587022800f72781480f4304950125304654004204640a89028a280f80046410263604000f730461202300461249430460c004204624057128a202fa5046340042301000f43684400f81049220374046610580701200f61181000f4304920185304640243060a200f86105200f65114500f93046282830046201641148100f9460a600f40602000f62049410231049301652710600f50701400f6124a202f7a534522f93405300f73514500f93049010273046602576049410273046408642509000f210464848430462a083130a300f7004908153108a080f60105100f73046660230e81c00f21e48c00f21e90200f50046a40341046802582046a40431046c02382046301264450500f10049620281049508496046120460168120f9404620183104942016804950015204912232904960407804e50064904d00487604604805420a240f40049010160046604863668401f720496803540490815320492402874a8480f40568524f9404d40808760a200f40644200f8304978024104950134240a400f92509400f75701000f75322200f72049780541049780142505400f91648600f21305200fa1782480f5420a200f80311000f5100a000f86085000f64389300f65083000f32390100f52114000f69046380150ed0880f83ad0880f8320a200f7820a201f86088000f85505400f4368a680f80488200f82708200f21614600f10412000f72711000f51320000f74083000f54049e04470c88c00f85a05800f75046c02852049900152046e04053046c02582482440f50046310620428440f4004640138404940858004644043104942038204928004104e010163049001342049320176046608162405000f4350a500f92005400f43005400f75082000f50501000f75046540931405400f91322300f724c8080f8440a400f78046410160609600f853c0300f21524000f10430000f83046401231790600f63105400f670490a0318046704071049304530046204051390080f5204608815004e280043049304560185100f59ed0a40f50d14810f75ad0810f85e45804f8521a202f6a402280f283a2180f06194080f3004ee00043a28a00f40046a20430e68c20f21e05a40f75d80400f32a50800f83046202572046408574049401742046010680046500561049288081046 else 0x4620168404621016304628016504620468704950852004630034104910456004648068204641068004641086004940447004620458168a401f86046408654046500341046004751049644430046204851046404581046604081046700163046010163046080165049220473049040782049040287046308054046204843a09000f21046504053046040051046604851534102f30622200f78584080f30422400f86241600f85049420182682000f50484400f65701400f43424402f83148100f40284000f100466040710462040716b0600f10024400f8360a600f86046700561328200f62645204f8560a600f82405600f43602000f5204650065160a400f783a2300fa2392300f6a668204f40049104430046204587610000f72046408072609402f854a8080f48780400f32694480f38212000f620a8080f48046204643694280f38611000f61784300f10704400f1004904048000a200f86049002863046008164046040431046002476049201342046008542046004543011000f511a2180f92243000f53050000f10046102492302100f52185000f54112100f620d0080f502a8280f48790090f30612000f325c1480f913a2180fa21a2180fa26a8480f485a0500f90142040f27046082630e45601f83668201f7204640138104e2005860466808620494408510494045300497001300492201760460016840494302)))
def prefixTable0 (i : Nat) : Nat := 0x28002be0d9ea0ef5428002bdc9cae0cf74280023c859ec8ef702800389c600a28f10280033dcd5e64e7532800389cdc240af43280023c859ec2af4028002bdd5c6848f1028002be0e10a6ef8628002bdc9c2c4cf51280023c860e84e1522800391819ec48f10280038c815e64ef52280033e158860af43280023c85c082af4028002bdd5de608f1028002be0d9ea0ef9228002bdca1f02cf74280023c859ec8e372280038581c4628f10280033dcd5e64ef6928004060a00a4af43280023c859ec2af4028002bdd5c7048f1028002be0ddec6e58028002bdc9c0a8cf51280023c8608a6e26128003898d9ec48f10280039d495e64e641280033e158860af43280023c861f00af4028002bdd600868f1028002be0d9ea0ef5428002bdc9cae0cf74280023c859ec8ef702800389c600e88f10280033dcd5e64e7532800389cdc240af43280023c859ec2af4028002bdd5c6848f1028002be0e08e0ef8628002bdc9c2c4cf51280023c860c62e1522800391819ec48f10280038c815e64ef52280033e158860af43280023c85c082af4028002bdd5de608f1028002be0d9ea0ef9228002bdca1f26cf74280023c859ec8e372280038581c4628f10280033dcd5e64ef6928004190a0708af43280023c859ec2af4028002bdd5c7048f1028002be0ddec6e58028002bdc9c0a8cf51280023c861ecae26128003898d9ec48f10280039d495e64e641280033e158860af43280023c860840af4028002bdd60ca48f10
def prefixTable1 (i : Nat) : Nat := 0x60a030604c000c0a060e01c00141806100404030240c000818070009c00182206100502030408c000e0c270809c001c0206100404038104c000818070041c00181046100802838120c000c06060841c00141806100404030010c000818060421c00181026100502030410c000c00271001c00183046100404030080c000818060441c001c182610060a030604c000c0a060e01c00141806100404030240c000818080221c00182206100502030408c000e0e081801c001c3106100404038108c000818070c81c00181046100709040310c000c06060841c00141806100404030010c000818060421c00181026100502030410c000c00270d01c00183046100404030080c000818060441c001c308610060a030604c000c0a060e01c00141806100404030240c000818070009c00182206100502030408c000e0c270809c001c0206100404038104c000818070041c0018104610080a438120c000c06060841c00141806100404030010c000818060421c00181026100502030410c000c00271001c00183046100404030080c000818060441c001c182610060a030604c000c0a060e01c00141806100404030240c000818080181c00182206100502030408c000e0e080a09c001c3106100404038108c000818070c81c00181046100709040340c000c06060841c00141806100404030010c000818060421c00181026100502030410c000c00270d01c00183046100404030080c000818060441c001c3086100
def prefixTable2 (i : Nat) : Nat := 0x202488119009a2046202488118c09c204620248811920002046202488118c09c2046
def prefixTable3 (i : Nat) : Nat := 0x1800307086000c0451800287046000a1a11800303086000c1611800206146000c18a1800306486000a1141800307806000a1941800304146000c0c11800206146000a0851800302846000c1c51800287046000a1a11800303846000c1121800206146000c0611800303146000a1141800302506000a1941800305146000c1891800206146000a085
def rankFormat : Nat → Nat × (Nat → Nat)
  | 0 => (8,prefixTable0)
  | 1 => (8,prefixTable1)
  | 2 => (4,prefixTable2)
  | 3 => (6,prefixTable3)
  | _ => (0,fun _ => 0)
def rankHeader9 (i : Nat) : Nat := 0x9a6a9511805
def rankPayload9 (i : Nat) : Nat := 0x66b8533562912e09b2e7c3e8fa0831b578370f34fbb6
def rankMode9 (i mode : Nat) : Nat × Nat := let v := packedAt rankHeader9 ((2*i+mode)*11) 11; (v &&& 7,v >>> 3)
def rankHeader10 (i : Nat) : Nat := 0xdc80b7153dc54b6fb3dbecb6e63db98b6d63db58b6bd3daf4b6ab3daacb6943da50b6763d9d8b65d3d974b6453000035dd70000358070000351f7d420f4ba5d290f4545d124f3bc8ce80f3495000032e27cb2cf2677000032007c7d4f1a58c628f12c7000030c17c2a4f069700002ff9700002fa1700002f50700002ee8700002e84700002e327b89cedd57b6fced588b534ecfc7b3c4ecae7b28cec5c700002be77af70eb608ad44eaee7ab78ea8c7a9f0ea0d7a808e9b68a668e9337a474e8bf8a2d0e87d7a19ce7ee89f70e77779db0e72d7000026c479a9ce60e8000025a670000256750000250d7000024af79290e45489100e3e858f44e35d78d24e2c488ac0e23688894e1bc700002178785b4e11f78430e0a578238e044780c4dfdc77f10df8557db8df13700001ea6700001e42700001df677790dd7f775b0dd2977464dcc6772ecdc747718cdbf676facdb9976de4db1476bd0da7b76994d9e376748d984765ccd900863a0d89d76248d8297607c581516000d79b75e10d70f75c10d67b8000015db85720d586755a0d52c55468d4aa85270d45855104d43715098d3eb54f38d37f54d90d31454c00d29274a1cd22c74868d1b274660d13274460d0bd7429cd04e700000ff8700000fb3700000f7273d68cef373b7cce6973978ce00737b4cd80735d4cd2b73438cc97731eccc1373004cb7482da4cb1f72c50cab672a7cca44728a0c9d0726ecc9637253cc8f570000089370000083d5000007ed71f64c75e71d28c70751bb0c6757195cc5e27171cc5368146cc47f811b4c3e180f08c32680c0cc2ac50a84c246708a0c1ac70684c12080408c0ab50234c036500b440241006c40121002440001
def rankPayload10 (i : Nat) : Nat := (if i < 1 then 0xb60712f3a65def839ce49979d445eb0cb4dab67b18eff865bf57494abd8525c2126eb109a75b1cfc8625d40535612b6601b5e096ff879faa72c16b08eff83965aa1074405152f32a6e1560c99722637d5c6fa0cb909e58c90eb4ef25d40d7822a9125d44e90b408768ed98bfa8cd22c1cf315d0355ff05b68450386704185740c276ab0972bda51d02cd89bf39e5dff82c285a5e57fc16642281c8bd0ac72effc1605df41c856395ff05b245085978a0738dcf5d972e3d44d07864a18b395ff05be3b1d166810ef6166825db15ed66954d01c11b16cd7ae126d0988373378bda65b90a4abd92efca0cd2c57b5b554741e0c744b7fb0672bda46bd954511e3cfa342f178dfebca906586634c60797678e0b29ee795837c749d64f22af1bfd603c067c295c76862c725305bcaef1d9f3e5b1b050c5bd44d27bb2b3e5b1586d1be2667565cbc21be05c72ec2b599a5078196e7b0632d691235c24bf432d6984f831d196b4244aa112682cec596acacb9f2d8e73e5760362e6d4442de03579854835c967056f3ee3a079b95173ee38e87e1f0f45122b1bf8bea2e7d9f5974caa8d3a39feb3aa34eb92f984cbdac9bd62ff94ef0b1ab17fd9637c2c36a63d68b351255ec6abd831c6f8658dab1b429ac9bfb46063b59839fd63625ceb1ac29ac9bac235ed6d662c0e25e758db366cf631dff0cb7eae9295ac11b5a49bac78feb3996f4d79faafe8db4ebe5392659e380496fd436f6be859a4907386b36be85ba79a5fd2764eac70564b725f30f171a382253c75f59dd2effd872f1d2f614a859e12ce65dd5b0a241cf171870550c7bf0d57b065be655b3cc52ea1b4c18e373e4fac75a86bf93ea2bfb8e69321c848df1507da352efc455e630c947705d88550b596a1d82431c5830783c291b7c841d65a86c737265a8d7b5d36c0e4dd6196dfd59faafeb2dff10d7784abe61969b513192db3fc8eef146cf64f1c4b0a3af32ae9acb7a1b0ac258bda2a0ac2d75255f31d2ec2ef053ac31efc74958bd8c7bf0cbba92af60d45e1186142042c4b7a08dad446cd612b9f67d15b3f97c36de7ea8cfe39c852eb1c1b308d7f93e62bfdc7706cc79157cd2a43993661936601237ace5abc646face86bfcbee0bfdc72d5e03148e26927d950fe5f77855f326b0c6591db3fc5f6cff2fb937d676b0a476b164b17ca966cb8c342251dc9beb3bc37d4f162c9ef0df53c5cd676e0a4c71a14a8ed8e7e4738ea0e5bea78428d5338ea1b82031cd9701b8225f159f318e525b79746d87cfbb6e0b386f2bfd837a5fe93b82a2bd0731dfee3b82ff41c85cfa3e9737ed6a05b3e0fbd802f8eac3cbb7936b2e998b2bfa2eb2e9f26d865429a2b6ae7b808db7190317175617fa3e3991db573f4ede4d862ff91d45be8390ba7d2738f6f71de31bd5b6477e61a7bfe4d9a0d0613098244 else 0x9383fc9f7261610161c7f5ada3f538eff8e4dfed590ff6adf0f59d21a43473c198dc332e87b22fb9e5a1c396b824a786b6e4944cce7403beae4e78456ca92d670613a54bf9be88e7d9f705ceba3998e8bcc2546f27d8dcfabeea671d305d4e8e3793e492032d9981be199a865b6783e386f16d031bc5f64ccf76c93bed18ebeb1822a15e61134e962f852c5f0a49df68d4ba832d648c464efb46f2fac608a85b308973a4f7614b270b093516cc24f793bed183428e6b285b31e5f58d45acf61c06ac8c4327c82f1c21e3af855f68cd550ba8ebe0536ae29bed1a2b6601b7e0b12dfe107d483ea2afb46ac8c4357f2f80cc228a5fc8adb841bca49d583aface46d6a0af9884d3af61c861b749720bc72878ea720ad44c7ad135c82c0a36fa3e44958316f97bd1c974548dbcd235ed1a1122e4086d93616660a4fa9f527561975065b49188bfb7f5eba8ea720a69d6789890216c0b3c429ed798df68c83ea68f9314b7f8d4bfe0b5898cf62728538284065842894f0911286f2f84bbf0d55a234c2a5ff0590ba96baa62fed1a339cfe0535aea5aeae854216f0e7e0b5892c258d4bbf084752f448447f8894aad4dc7909e262f58ef4b1e642390c839ca33b546615c5aa3309f39b72240a7ac387b0f60c67b82913ae91913a464436f2440c9b6be428a8244c41bca7225df818d58a88d30a97bc3d75601c0b805328530cd4531ab0f3f5545c9865bfe352f78c6e7e0b2c141062c280de1d3058dcfc1639283ca25065b27563cbeb391b5a82d9884bce832f3a88e563c7390a5d616ba86dd25c82f1ce4cbba82af44477b436c9ae4127bb0a58493d964e3516cc272b8c888deb392afeada2a37cb631e4e5cf148e312932d8dcbc7846618dce5c57187044219cba608b188e0b48ef8196e2b8c72b8c38224e9d241df81335c68e0a70c4b098b581a5470c592d05b31e5f59cc5ac5ca9dc4afa11d7afa0534976a7a94fe115ee08ed172cc9bfb46063b3cc1cfeb1b12e75154ee27a915ee01490dfd75162e599375846bdae9)
def rankMode10 (i mode : Nat) : Nat × Nat := let v := packedAt rankHeader10 ((2*i+mode)*18) 18; (v &&& 15,v >>> 4)
def rankHeader11 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0xa736590cd8de736320cd8487360c8cd7c4735e70cd724735c38cd6a0735a28cd61c735818cd58e7355e0cd4e2735330cd4547350f8cd3ba734e50cd31a734c10cd24e834898cd1607344d0cd0c6734298cd006733fc0ccefa733b60cce487338c8ccdb4733618ccd007333a8ccc74733120ccbbc732e98ccb20732bd0cca2c832820cc97c732598cc890832190cc796831e00cc6f8731b48cc650731890cc5ac7000000c5127313a8cc416731000cc392730df0cc2c8830ac8cc2447308a0cc18e7000000c11a730410cc0967301a8cbfe25000000bf5c52fd18cbec672fac0cbdee82f6f0cbce472f298cbbd072eea0cbae872eb48cba2282e830cb99252e5f0cb8ba7000000b80072df10cb6fc72db38cb61e72d820cb57272d510cb4d672d2a0cb43472d078cb3628000000b2d272cab0cb1b682c680cb0c882c2c8caf8692bd20cae9072b940cad7082b4f8cac5882b108cab4c82acd8caac872aa68caa1a72a788ca8c482a258ca82c529fb8ca71c729c18ca6507000000a5be729658ca4f2729318ca40e728f88ca348728c70ca222828830ca17a728590ca0ea728350ca0547280b8c9fa8727d98c9ee270000009e5c7278d0c9da0727628c9cf0727368c9c765270d8c9b3c826c80c9a66826928c999a7265d0c989c726218c981c525f78c9702825bb0c95f6825780c95447254b8c947e725158c9374724d78c92bc724a58c91ca7246d0c9142524470c90a8724248c8fc2823eb0c8ef470000008e8250000008db0823648c8cee723360c8c18722fb0c8b1a822c10c8a64722938c8994822598c88dc7222c0c88427220b0c87a6721de0c86bc721a70c85928215f0c85047213a0c84547210c8c8374720d10c82ac700000081e2720718c812c7203f8c804e7200d0c7f7481fd78c7ecc71fa90c7e1671f7b0c7d3471f478c7c8c71f190c7ba871ee48c7ae671eaa0c79ba800000078e871e330c77d281de48c770271dbb0c761e81d808c751681d400c748a71d170c736481cd38c725081c888c71667000000704681c088c6f7871bd68c6ebe71ba88c6dba81b638c6cce71b288c6c0671afc0c6b5c71acc8c6a6871a8d8c691e81a3d8c683e71a030c6746719c70c6670719900c653c70000006460718f69c6292f00000060dd118171c5f0ec17a39c5d17017179c5c4a116e69c59c4f16381c5718f15a49c54a4f15081c5295014781c5046c13eb9c4e48c136f1c4b75112a29c47e7211d71c45f51114ca04422c10db1c415501018203e5700f659c3add20e8e1c388d00dfa9c35f120d5020332af0c981c306ec0bea9c2ccd30b051c297510a2520263b10951202530109291c2490108e89c2194d08279c208a107fa9c1dbb0073f1c1a5d406671c16df305839c13c3104bc1c116ec04199c0dcf0036f040daa102cf480713a010ac800019 else (if i < 2 then 0x4aa759250d6426758ff8d6360758d08d62c2758a48d61da7586b8d613a758420d6088758198d5ff8757f28d5f5c70000015ee6757b40d5e12757798d5d607574c0d5c0a856f98d5b68756ce8d5ab470000015a1a7567d0d59807565a8d58c47562b8d5834756048d57a4755e00d5706755b78d5670755940d55e27556a0d553a700000154ba7000001544c7550d8d5396854d60d52c2700000151fa754780d5116754400d50865541c0d4fc6753eb0d4ed0753ae8d4e34753810d4d96753600d4cf8753388d4c56753100d4bd2752ef0d4b4e752cb8d4ab4752a10d4a007527a8d48f6752358d4824752000d4792751df0d46e6851b40d45d08516b0d4536751418d448670000014404750f50d4324750bf0d42847509b8d4194750550d4066750140d3fa474fde8d3ef274fb00d3e0674f720d3cea74f350d3c5084f060d3b5474ecb0d3a6874e8d8d395874e508d388874e120d374c74dcd8d36c87000001360474d718d352c74d458d348274d1b0d33ba74ce90d332c700000132b474ca78d321074c7e8d314674c4c0d307474c138d2f9074bda0d2ed674ba98d2df074b6c8d2cfe74b388d2c1484aff8d2b5274ac98d2a7874a930d299274a5c0d289674a200d27b2849e70d269e8499f8d2610749798d253e8494a0d24aa749210d23d4848ea8d22b6948a50d2226748840d21748484e8d20808481a8d1fe6847f40d1f4670000011ed8747ab0d1e3e747840d1d967475d0d1cb2847270d1c2e747060d1b88746da0d1afa746b60d1a6a746950d19d070000011958700000118c470000011846700000117d0745e80d16de845af0d164e700000115ce7456a0d14ac800000113fc744f78d1342744c58d1266744900d1198744608d110e5443a0d1040744060d0f6e743d20d0e70743968d0d2e9433f8d0c5c743118d0b66742d40d0acc742a70d0a26742800d0932742470d088c742138d0780741d58d06d8741b08d060c741738d04e2741288d0412540ff0d0386740d20d02807409a8d01967405e0d0066840118cff4283fcb0cfe7673f940cfd9683f600cfd1053f3e8cfc1e83f020cfb8273edb0cfab283ea00cf9aa83e650cf91c73e418cf88a7000000f81473df88cf71e73dc20cf69853da08cf5b483d678cf4f283d2d0cf3dc73cec0cf2a29000000f1b483c678cf0fe73c300cf00273bf70cef4873bca0cedfa93b738ced4a73b4d0cecae73b1f0cec3453afd8ceb2483ac38cea1083a7e8ce97673a530ce90453a2e8ce83a73a090ce7a4739e38ce6d2839ab0ce61c739818ce536839480ce4a2739230ce40e738fe0ce380738d48ce2e4738a68ce22c738858ce190738578ce038838088cdfaa737e50cdede737b20cde4a537880cdd7c537598cdcf8737340cdc5a737110cdbca736e98cdb1e736bf8cda907369b0cd9fe7367a0cd97 else 0xdebb077add8dea7c77a998de9f877a788de95077a4b0de8ae77a228de81c779fc0de782779db0de6fe7000001e6907799e8de5b6879680de52a7793b0de44c779088de394878db8de300778b70de26e778960de1ea778750de1667000001e0da7782a0ddfd0777ee8ddf10777bb0dde4a7778d0ddd5e7000001dcf0777310ddc2a777008ddb227000001daa0776a28dda0e7767e0dd98a7765d0dd9067763c0dd8827761b0dd7d0775ee8dd7287000001d6867759c0dd5f47756e8dd53e7754a0dd47e7000001d3dc774eb0dd2f2774b70dd2447748b8dd1827745b0dd0948741f8dd010773fe8dcf4c773c80dce627738b0dcda67735d8dccb6773248dcc16773000dcb64772cf0dca44872818dc930872408dc85e872070dc732771c08dc5e68716f0dc5207000001c474771178dc3c8770e78dc2e0770b28dc220770828dc1687000001c0c2770260dc00476ff20dbf4e76fc78dbe8676f988dbdc476f680dbd2476f438dbca076f228dbbf876ef30dbb367000001bac876ea80db9fc76e788db90086e310db7f076df00db69c86da18db59c86d5c8db4d87000001b44c76d0d8db3b876ce48db31e76cbf0db24276c848db16686c4e0db0bc76c298db02c76c000daf6676bce8dae9c86ba18dae1276b7f0dacc686b280dac1476aff8dab9076ada0daafa76ab28daa207000001a99876a608da8fa76a338da85656a0a0da730869c18da60c869780da5267693e8da45a769110da38a868d30da276768918da174768578da0e47682d0da01a768010d9f2e867c10d9e80767948d9d927675f0d9c9a7671b8d9bd0866e98d9b2e766c18d9a80700000199e4700000199407000001989e766220d980a765fa0d9728700000196d6565ab0d96545658b0d95d45656b0d95565654b8d94ec500000194845651a0d93ce764ec8d9336564c80d9276764928d9188764580d90da764310d9082564148d8fb8763e88d8f60563d28d8e8e70000018e36563838d8d4a7634d0d8cf2563330d8c8a563190d8c22562fe8d8bb8562e88d8aea762ae8d8a68562900d89ee500000189865625c0d890270000018870762168d87e2561e80d86bc861a98d85dc8616b0d84c8861280d83c2860eb0d832a760c50d82a6760a40d81fc760758d8140760490d80607600c0d7f9e75fe20d7eb475fa78d7d5895f4c0d7c9475f1a8d7bfc75ef38d7b2c85ec58d7a7a85e990d79f67000001798875e540d786075e108d777c75dd98d76a285d9b0d75e875d6f8d752e85d420d749a75d1a8d736e700000172ee7000001728075c950d719875c608d70d685c2c0d701a75bfd8d6f1285bbf0d6e8475b9b8d6dbc75b698d6cfe75b370d6c5285b050d6b3a75ac70d6a7c75a940d69b685a680d68bc75a298d67fe859f68d676c759d40d66a47599e8d66007597a8d65567594a8d6)) else (if i < 4 then 0x70e735289cc90e729679c9a8e71c279c650e708689c1c0e6f5a89bd10e6f2e19bbd0e6ede19bac0e6e3879b7e8e6d6870000026cea79b350e6c4879b070e6b5c79acb0e6a667000002699e79a5b8e68b679a238e67dc799e88e678c199d68e667a799928e6582799540e6412998f58e627a998990e616a8984b0e603e798030e5f2a797c50e5e32797870e5d9c797618e5d1870000025c7670000025bf8796f88e5b5e796cc0e5ac2796a30e59c8796688e59167963a0e587a796190e57e0795ed0e572470000025692795970e55e4795708e553e700000254c27000002542e700000253b270000025314700000252a6700000252247947e8e50e68942f8e504c70000024fb470000024f3670000024eb2793a70e4dfe8937a0e4d7a793550e4cd07932a8e4c14792fb8e4b70792d68e4aec792b00e4a527928a0e49ba792640e4922792400e4840792068e47ac70000024726791c40e4698700000245fe70000024576700000244c27000002444c700000243208000002423e700000241827000002410c7000002408e7000002400270000023f5278fc50e3e6c78f8c8e3d9c78f578e3ce270000023c5678f058e3b4870000023a54700000239de78e6d8e38d28000002383e700000237aa78ddb0e36ae7000002362078d7f8e3586700000234fe70000023486700000233f278cf70e331678cb30e31f678c768e31207000002309278c158e2fba70000022f2c70000022ebe78ba50e2de878b748e2ce478b338e2c2288afc8e2ad880000022a6278a8d0e297678a580e28f278a370e282a789ff8e2716889ba8e26587898d8e2590700000224fe7893a0e246c7890e8e2380788d28e224c888888e219a788610e20e0788328e205c7880f0e1f62887d30e1ec4787ab8e1e40787848e1d4c7874d8e1cae70000021c24787038e1ba0786e28e1af6886b80e1a62786890e1976786538e189e786180e17cc785e58e167a9858f8e15a67855e0e14ea885300e14527850f0e13be7000002132e784bd0e1208784790e1144784470e106e784128e0fdc783f18e0f26783c08e0e94783998e0daa7835a8e0d145833a0e0c7a783110e0bd4782ef8e0b30782bf8e0a46782888e09cc5826d8e09487824c8e08c4782270e07d2781ea0e0752581ca8e06647818f0e052c881458e04a87000002040a70000020364700000202c470000020206700000201625804f8e00d0700000200627800b0dff9277fda8dfeac7000001fe0c77f780dfd4877f470dfc9677f200dfc0677ef68dfb2a77ec08dfa3477e838df97077e568df8da77e310df84477e0b8df7c077de50df6a487d9d8df6087000001f58677d568df4b477d278df43077d010df35087cc60df2aa77ca18df20877c788df12a77c450df07487c110def8077bda8dee8c77b980ded8e77b590decba77b1f8 else (if i < 5 then 0x2f44a7000002f3c27bce40ef2dc7bcb18ef2407bc878ef1b07bc668ef1008bc3a8ef0727bc128eefd27bbe60eef2a7bbc50eee707000002edb47bb610eecb88bb288eec2a7bb050eeb887badc8eeac87000002ea407ba818ee9068000002e88c7000002e81e7b9fd0ee6e88b9b20ee65a7b98c0ee5a47b9610ee5167b93d8ee4887000002e4007b8fa8ee3507b8c98ee2a07b8a00ee20a7b87a8ee1747b8578ee0f07b8368ee06c7b8158edfe87000002df5a7000002deb47000002de347000002dda67000002dd1c7b73d0edc488b7028edb647b6d18eda2a8b6818ed9907b65c8ed8c88b62c8ed82c7b5ff0ed7767b5d60ed6ca7b5ad0ed6287b5848ed5728b5570ed4ee7b5348ed4428b50b0ed3907b4da8ed2fc7000002d2687000002d1cc7000002d1567000002d0d87000002d02c7000002cfbe7000002cf1c7000002ce807b3978ecde07000002cd527b34b8ecc547000002cbaa7000002cb0c7000002ca807000002c9fe7b27a0ec97a7000002c8f87000002c8647000002c7c07b1ea8ec73c7000002c69a7000002c61c7000002c58c8b15d8ec4de8b1308ec4328b1058ec3828b0d68ec2528b08a8ec1a07b0628ec0ea7b0350ec03c8b0098ebf6c8afd00ebeba7000002be247000002bdb67af620ebc888af1c8ebc047aefb8ebb707000002bae27aea90eb9bc7ae680eb8fa8ae390eb8507000002b7b47ade30eb6e67adad0eb5b08ad600eb4aa7ad1b0eb3867acdc0eb2ec7acb58eb25e7ac920eb17e8ac588eb0c28000002b03e7000002afba7000002af1a7000002ae9a7000002ae287000002adba7000002ad4c7ab4d8eacc87000002ac327ab058eab967aade8eab067aabc0eaa707aa918ea8f29000002a85e7000002a7ec7a9ef8ea74c7000002a6ce7a9a40ea5728a9528ea4d27a9298ea3e67a8ea0ea2ca7a8a80ea1be7a8678ea1307a83c8ea0727a8118e9fa670000029f2e7a7bf0e9e0c8a77d8e9d7870000029cf87a7388e9c488a7040e9ba27a6df0e9af47a6b78e9a5c7a68b8e997a800000298f07a6300e97f47a5f18e97487a5cc8e96c47a5a68e96247a57e8e958c700000295007000002946e7a5100e937c8a4d98e92668a4940e919e7a45f8e90ca7000002900270000028f8270000028efe70000028e9070000028e0c7a37d8e8d887a35c8e8cbc70000028bde7a2f20e8b4a7a2cd0e8ac67a2a78e89ec7000002895a700000288ce7a22a8e880e7a1fc0e8778700000286e07a1a88e86047a17b8e85707a14c8e84947a1158e8366700000282b27a0a18e819e7a05c8e81047a0378e805c7a0118e7fb879fe20e7ec079fa38e7d9089f548e7c7079f0e0e7bb070000027b3079ec10e7a9679ea00e7a1279e798e79427000002787479e130e77ac89de30e76ca79dab8e760c79d780e74fc89d358e743279d0 else 0xc0268b005c3c0170b00323c00c8b000a3c0028afff43bffd0affcc3000002ffac3bfeb0aff8e3000002ff5e3bfd78aff323000002ff1c3bfc70afef63bfbd8afece3bfb38afe9e3bfa78afe703bf9c0afe4a3bf928afe183000002fdec3000002fdd63bf758afd943bf650afd523bf548afd2c3000002fd163bf458afcdc3bf370afc983bf260afc5e3bf178afc343bf0d0afc043000002fb7a7000002faca7000002fa5c7be8d0ef9b47000002f91c7be3f8ef8907be1e8ef80c7000002f7927000002f7087000002f67e7bd948ef5de7bd720ef50080)))
def rankPayload11 (i : Nat) : Nat := (if i < 6 then (if i < 3 then (if i < 1 then 0x348f99b062cc87818ecc063cb38169975e5e007babe631d7d236541eeacdf390c82ad94b67dc741eea2ad959bd67fb8e88e61599cbc48ff09b92ff298a721b1c4318521f79147c729038e4a43208b3e39283a334818df484fd8d5358d8d6d77aea812752cca4d1253c0e701745453b431be896c66900741977a17186b05b9708740bc2af8b54766ae38e120990d7f368eb6b8ce0a9eeb3d5c56eb0a38af440b7dc5bfb07abaa8339ff8f348e8abfc1684e7c5bfc176819f3cce38a250f9b0e1b13b20f398ee79a07744a18f32d14b4dec1bcf0eb6aa8e816bbec198a9ef063a89d61942175d922571d99a98ec912b0ec48d7050855b1d8fddb43d42b239ca9fcaec3e592561e5a0311581c184e63a4ac08c3860c2150c33153c861d779071d852756d9af99ecfeb195741922561d891ae320d18e5fd085d74e532df8f8b9c04491cb650b911499d72513b0e32df8512782d1a7c751e6564cf218b68c3f76d39733142d711b86664838358c486c85bab78a169fb71bf09b78a06de2859ce10778c60339a40e0d731a0f7f9119d46fc263c9d30c482dbf5456487ca57e851379c15bef18c2a5cb663c1e1de015800ba5be34e3541eac3980dacc316b3539f59ce7cfa4ee0df41dc1be838a7f59cb69f98c857f48c657f49cc77dc98b59b598ece553329239672859937d31b9062c0afb3b7c9f66ecfc1f10885030bf1900be3ab0973cd75e0cf8289c83642885f73cea1b3185f20ff07dec38c51911cd2dc2831d621407560f56395c3a46d94624aaececbc840e788c5b67f27cda934601f6890bef271edaa7ab11b657b2a06fcd206e41b4495f35b89b80e7f562f4b9f59d0f64ac1b164758eb3cab4e22b03b2844af90ac8e87b2561257f59de45436288718afeb1b715876ecd3196707b005f735b1d6166973d658dcca24a291d9dbcf0f564fbf2fa91e15d42560c4c15f31e9320b188c38609d070c33ed9f4d1782de59c73d5807f78d45a759bf00f5f53c8db2a37e7a2655236cad364cc365d45a74d9e27afa9efc530d937001fd162906ec922f27dd9cf83e32d98e7815f2092bef63a86688de4fb720cfbcb0bee8e7c1f73c0afbc84e41bcb886382ad8cb661a232222a43a0f5821109b8ca78ceb1c1023e38ae3ba49d4378b9d0da6688e0b2ecc20565b822311914cae4a5ce9ff64a9159eb0a16094aa831ae58ab0abdf2919d67bf5418865b22950b1d24a7b30a0c70c341c73a4e88c3078cea191448b831329e2250a38451b262dd28b174cc6499704af94c492070cc51f6e311c380c3080cb0cc5036ab9e919cdcf38dde743d998b8632506398e83bd0219a416e1b0485f41c30a10b032871c66ff38c712037675419c23ed12843d2aff48dc38fe1f766503b4ce87b718867a467584c6e390be83bb3172c86ff37d99a38ee1b05b826598c6e863a0 else (if i < 2 then 0x2152b2b030c184aa945d05c0c306dba5656a8189bea62e819dadde93137d5e2db3ef92551296056570867cfd145a152929afe7e9a80f1853b2b142560c33c4c4df40b2a4a04da5274fe11b5c1e326bf9fa7369f846c50958376b6416769fe433137d1094942820da566dddbff28d227846d2b367e9cdf501e72a0a5c317dc8321792ccedef28cc90c628eef4bb5e9589b4acaf5c8c6293a8531b0365a56159451f142862def93460594855492b9d28bdba51dde976b42bc6dde8acae247a495ceb84d977284ac184aa936a15d7298da4f90dd812906293c85429669727451f0c1633137d14afe11935e9fc237dff946d3fc867d0e1b50a6317dc8302741a5661a255c87581b212aa0595aa0d36442aab9ce81656959f7fa656431b541a562e871c5f720dab0207137d76bc344a63e2c5095836ac081f7c9a765f7fa69585653616c2ca986626fa84fdacd1a7468d3a19fc236db658c3618346b4f59d697d4f342ff38dcdfa82930cc9ac6f7e0e721b657429e118c5a75b6d0db2bb5da7acebb5da20ea6b2864f08d8ffce318b4e9b0817650177d18b4ea4a0d2fa9ed7398c327846685fe719215061b49f21ba1ffce36a82c50740589433f846cc765c0a437e075cbda733ca61d035e2c664c6483ebcf41d403d8f15caa24e1a35eca9fd34eb2aa60b9c18e5dee70619cce036b040e097d9daa8536ae85f10ba8e40978e0335742f9e3863db949e3684c85d4d542983338612e8b6e002ae7de261bb2cc15de322934b99c06ec7d8703a8909649be296a27328ded05b6ac41db9205f31814d20b324d6ca03dd459d437a41cf39ab9e351d743fcc5d30d05de05a0429a4169c21d681b6090f798c5cdeed90df949dccd2a6dcecc5c3331266371cd7f7175e6d868bfd2e9268a54db9e3c849bc45e327aea4ebe539053bfa245241bb3094c14de40b4c721bf2913ab314a6f1cb1e18547aea14d58f29c8b15302f8c9300cf1c0339429c16b2efa65db272c48b4842854f78cd4b4f9cdb61d275613ed24620c75088d3a31d418da4f3c242146c9a234eb2452c193ea4eac524621782530c6ac0534ea85393d753c812f1c864ea853978e58f7e5278da533d750c6ac053c0a14c335118eb49946232e2c540c329b02853c852286f4ca0ebbfb5fd22d38b0c96f1cb0e3b10e0cd44a1bf23b539f94c6d3382cce5e0f266449eb527bf11977893d6907f84c39d240b74c114ff29a808512286dc480de3352c14502dc283c14539b670ca4f1508019d2efa006b9496a67ccf27a26653be9c50c17afa0dea1c14ae597e0cd41dc6fa8d64c14f6b2a061d63ac1a865c850af3c3deb1c3199281a8df491b7027782ce05acbad8d2027786c5ecf2eae9291b7098a9e3476cd9187133a0eef726f132c7b21e3c93bc2e592365398b1e2cc8d206386308646d8246d8218c2185 else 0x48d564dd4327b3ea8dfc3b7af3b8470116d8de1c69a2378e34e7d5876a4d4b61515c9ea7b7143a3ab0b9fd4f09365c82a63af16fe53330c672536e247d2624eca316eaf851af85da4f3a1ed3f8705a0e7dce72d9614f05a0e7dc785dae72ad55a9423d9f346fe1dc5b2fb0ca3429ac7ff48ce2bb5f8131608c24c3001a8f151aec73e91bbea83e2930c0be8b18a25083b716f50ad50730b59e0507c52758771706eaf28d1a14b65efb229da9b18bd1bbdbc0ac2a7f4ef64fe08b02ad8ef1de3f0de071f7179cc730bb1e898944ec15ba11f06fc3a3005e8f20d2bec27d3e65e73ee7c3d67779b230a74c6b1b112dd050a0c75e3c12d8e839b01c71fcdc36c84e818f68e79678137caadface9147ace616f96476ab059e0e66f7946c27f078345e0d3f4d78b8615c90eba4fac3e2a7da7e840d16c1e5f721ca82e4ef29bec7ec84e81b5e2e19c24e83bc3781e2d0f02af0d79b63e25be1228d43740af6f6c662df53db6dd8ac6c653ea37b0c6374451478c5bea7bc53ed1937559368dfc299ffce3362ff48d4cbfce32b5ff468d9cc4eea29e9180a89d88b8cbf9c6c220dc04a2a928191a66b9613bc3fca6243977b456e99ae6568a3543374d8470128edb3bfc38b44e72ef681a61fe535e1cd732bf0c6350de1368d8cbf9c66d063b0794275257613b61a27d157940244fe1188783ca01244445d0b7c302f44128a9ba08b02a07f088953746e77fce3777f3346694e38648f0c151a6c1aa1202459a89978b351271e242c669ef30a4e127b0ca36151271eef53eab27a0e787337bce370e8c7053146de25fe719d894676431aaacb2bfc345aaacc1e4361c4555559a76555679b90877e886d948cdd119ba6323ce3742fc088f229e91b3a9937559328dfc299ffce3532ff38d64739f424851bbac2a198375d48713a8e4dd862c59762d58761516df104ae85000dddb262e2a20f42383c31178b843cf91e361351382954e3b09c41d6b042cbae1ea795aab5428cb856a08c326ec119ba3cff4989ea8893d6466e944de0f4ca37f07a670f67df1da89fc116bcc0ab6356aad456a1465ddd5a250839937600dc1bbcff49bb99146ac4ff479379c9ecf9c97d59c7b8e3c631b112dd698d636092cf982f4e01162520768e10350722207f3a14e1c8a7c26c65f4d54fb1937609bdc57f8eda82a838e574c3586911c27d2601249f47b04d8f395d76dc7850363d149bf35ee51019fff3eac04a503215fb42fbdbce68dd5e62b7b6a0aa0e15b7ef04b3707424fa3c8cbe9f3b584fa4c026aba8c84e639ccdc39370c1e371df093986edb104be88251cd1ba4464a06748a3f988635059280bb95e6258c524a54f08c9af89beba5ece8a4ee69798863215885740cd3b200959590c6637ff28d250147f312c6a0a9af89beba5c9d7123d7284ac1a6282cad506a82e43ad5)) else (if i < 4 then 0x6ac855232d7e1257f58da5d5e0e0d1e53bc1f463828163435558fa1622f7ec60fe8c383ffc2f62718272724e2c487822350f4445e17b3ed8bb94837acd4b271ee730de0740ab94e2324bd187037ceff6301ffe1fd933895c62e2f1057db6ea1b6dd032b915ba0c4dd9722240f6ec81b89b5e65f4e6ec21881db99d1d8343ce9b3a1555637109110866b128d498852716243c27182727225fe2a81989931a46b465c0dea1e938f812c241f9c4e3e2ba2d03f0f7e35861a8e6b538d098f58d55f53cdc6a5ef4f6c2284718a249e223a3843d46f914f94cf8ca33c37994a8d3dfe4d8344fe719389cb51271c246acef9992432d2472f843534844f0dd5a6173044955de979d2a340139e5425aaaaeaaaeac5c31ed06c58f6471bc50d6a70b542843d0af7a36320605458f505c80273faf3d8433ed8a8dd36742abad558dc61b692394f1de0a9876a150e6def4fa17b064e8e1cf62f758b378df66b1893ce34c047a6f4f0f0bc6493c538b8b4eaaac6e35d795c92f49c52c0afc3963110863259d80962210fe1cb0568ad6c72c0f546e494736f6db537e9888bd50923b602acef06f8a3e3724a3b0b87aa30ab639603706fd28d00ab11dc6326578095e7d28d1758c9d07a012ccc6cb6be26ee0a34a58150862c771c92f49ca3404b3b62210c648096760df4d1db311e6ce856c29f43bd1795c98857d042d5b50063165086193a0f4025998d96d62b7d6ae985693232e21ecf9e9bc7aa9d43216199f39ce2d3a84c7ac6aafa9e8873e718658cb03a66cba915ba0a2dc2f6d9e84578480943d8251960d7f2547428031426c4d98e8d18f15c810505621c0982d53ed06c84703a37c09f7f0260ac168571b23d7fc9db4c7c361547ab69063465ece9b121680ab1c68b855c36adfed7a82ec85e8f322626c1b97d206bcecbbd725e26c2190339ecec97833222f0ff90a8aa716662612b02d2d1e04e20273eb0d0125b54444889116cc4bd5b3a4b59f6b688197f497ad975e7794818095eb7973e2819ad1c75275868ae8a93ac1317667d58736a8857bd06e8bdeded8c0ad5757bf1449d617ec56f86f03c776d41aa782a51ed5a611f43b542a61da3e02968ad95b0bb00a8370120245e89bc33b0bb213ee542b51bb60e3bb5b3b06e05588e0342231becbec418082f404e7b76ea9864815622b0bb30ba5137c56335c9476176d5098bb30af8a3e3e6da06e0246023b754d9ec568e950addb352c3950f78a1adbc2857bd0fe4eb9604ae39de93631bba4030d7ab8b479d2bd8680913b944076ec85e8dd104a857bd176a979e796c6024151a11f62470edfb0d584d95838f19d84d944556d8b4ef441d0c961f10c88e7902a44515ba1110123918f0bdf1c206ea36218090862c4acadb62501d15959d64b565e51160249fc22247c0aaf3786d8e84b8be3551ffc3c7f67d6 else (if i < 5 then 0x2fb8dd6a9089cb855a02712f7161d219935595dcaa5f7041ef3882c1c2f6b47eab77b56b25e75a88f6ac648f5ac58bdaf2786e39f91f1f86c2aac5e8f9088e4422d5e153bc0c35692fef3ae2b13497f79d854430d4e0bbc6870b2cffc5963e30b30b0bbc76152859e12ce792b91cb687036e93983de761ff8e0fc8e7050ace31efa9e626b0e8dfe4732a638a6e2510e45c1281d24c01317f90c26f61ab0ff29ba5efe8b3d7227828d469d00cd9097d9be973a3c2f642b087837c51f188db17b03d5109d6166c81bd7dbb239abcc898f3137b0d473c56f57d28056eedf18a8678e162b5a26ee854c3a6ac3c592ff87f674b9d295128e9bc0acbe14078de85ecea09a873bb2256ca256ca06ec69095b297a930c78ab110add00095ac0995070fa286e97bf6ade2e6ac226ea84ac382c56b6940e68c39cd9034fd73a4aaead28004809a95fa7c3fb3a82e4163f0ac635a30ee85ec6def4ce57a27c5631e9b62f658af45ac2a760451553a695fdab66854c3bed8eb44daa9d20906ac9a79fb231ef69528f71c54dd5bae87c8ed011444aed87c6572849d471362379d0e1666782b71b1578ca91df89aa61026756191f03434094dd8039ee883728c83143dc267a6c4826e9b87f197a572b46d7b2f1861df84a3bf2a02ab3ef06ee8d19666c09933433bad04ccdfb075d12fb1e12f45d58b3b651c82503b745de9f1253ce2c4985a07c60f89525da29f40522e43dd9904e32d2b9b964d310188ed56ef7477e3b05ad1b43d9062b068ce93134649a3364da8c659a099d56e15664b7756ecfc2ab690e284d0f7104dd319f2248d0e1e4128a1bcecfbc03a0ac2b8d902786c9abb60ab31f0dab7f1d0422117c3a55166a22a913119054c4f1084d40691c8c881b928792c55df8575767aa3e7b340de26a9b74f8ca8cea3ef344abf04a41446e92ed42d3732c482b0af4e4469d1a70a9de3c9ec876085b164f39254b9215872234a3b06d116ad21238c85f73ad5ad9ee4f1e753235134af7242fb9fd85a372374d030e46e9725ca0d0251da3ac7784242c0b35172374d03083409c8dd2e7b9217e46a2f9ee485f91a8b73e8c9a330af4d03015ab8e7053aa683409d1bf0dca50ca37861a1f62705149e1f321d9d271be7b962257a6135e321cf8a4f6ab587d70c1a3e8b70d10ed56bb8a8f5c3e8714d04a1674389581c8df092b6a65a8f5efa4a83ed237459d821ae252374b92e5868f28cdd4566e9876c2bdc3aa3f1d6fca352351695a435fd9f70b396db2472e154477b3327eda3404d0aa3c566e9b050264cab89b71cbbbd6b4a23dab1975036d47b89a7430a364d16c1fa2dc0d44848f6acc7fa2c1570da05c33aaec2dc6b77bd636c93b5780d752cd1db207bceaee322a65da5d5188f6add2f6da932d5ab9fd63217f0c7c2c2fe53be0a249c4e14b697516532e2f4 else 0x8bd702d039f0fa3b16fa9ef464186045437d04063bb7a84961b1fd21768684c028c5b194f82c0254a146a316ead2baf8c36316eab4ab7e07ed844c1b87f7ae40fe1d6d3171d1259da1207243dee83e9b48e7af65c819cf40e27dc0e7f34a4844fac72221ac4ca33b16fa9e127138a97f817065b897fc16f8794e05f5b60b388a98605f5588f90cd8548b62436b4ae2dd4fa1071536fee7814289089396c68dbe8bda6ce02f53b240cbf38755f0fdada3ae26c89837d26b5f53c912832cb5f53c54bfc41385d46bfe0b2928d0b920b0b4dce273aabf4d0fa1f0ff43ff63166e996a278610d445cc3786fa9468ceb4188fa11cf30f5a3af0cfac3d6986fbf85a51521562da5157121a98fa093b0a253cbdd47ccb5efe6541f547f122e70a41e159ba6862a3d47f7251e5ee1f547c2a3deb6ae1099c477b616c23e8095ab7f43870d16cc2988c7ad60b59528fa1cb5116a24622e786100b7a4aa0dfdad1a6c60f23f57b68c09d77233a4d188f6ad874c7961f47b4baa3c8711dbeca44428f4e594324b580746c82b00a15f6ac71d072111866d8453b487f07fd882c9c4b3e04d034f36cc4a76899f9bf7d18f6d3e680ac82a92ed0d985a8746582b11a09d0ed636e14ed68ce59aed23ac6dc42348468ced232924662dac194c3d689d97055492bb1957958efcd0595f28be0131bb22ebb820413a00ae73a1fc47de0595f63757ca0ba0f1941b662da18eb39ecf827f3e30e64028f2c6dc19e2a606a937895484542a963d9266826e98cf871aa7f78cc294cb6bf2a7be12390ce0f39de4b904c0f177da0595f298df0098ddad71947369512940c39e4454947c172e0a2d1b905bc9d125ed25fab02a96f41370bda1ead0d60448e38a9b4b5d58748404040c59f6804c158d903b0bced90f3b1a59ea0901011506e0ed1ea0c59fbdd26c40260ac168571b3b8e517a03a364158130ae3bd9a926e22e941af7d9eb5d08aba70d951fab00c8aca18aa811697f7bced5677791430c3286351f51245ac1645e240c5251f79daacd3281d25679d2435fe0b732f0793f2710bbc2123d672e1cad8cb1b269dddc81cb0feab3a82672cfc9a7622116923de761f437a4a7821c15a06845f953ae03caf922e377128550aaddfcdf795db68b412b0de1cb548da1961208710e45c15c2f85a095bd8251b25c61793622bfd1ea0bf22f0b7a9828b0d855a47a2c9abb67938f5396e45d1549f459d9356d25fdeb1d7859d695fa1d7832af2987ba94fb45f21e46ee2522fe662791b146d2ff73b105f97d09a3797d218b139aa3746fed58a35169b1223b8f38eb30417dd0a0651175f23743ce929e08e5348f95142c4f369f9e101e2a7b532ec97dc21f2bb0fae3128d9a9da04a075e4e9d8e0bfd16d25fdeb28aec3e711e383f45aa762c2ff45b897f6adaca62ceca874cb99770fed71))) else (if i < 9 then (if i < 7 then 0xb1cfc268fbea7d2beb2fee5970f46d8a86f4afafd4c27582a3405fdc7d6a8d047d6c0e38b1a02c6808194b6ce10f15a416ce40ecde0bedf09f52c825076fb047ac3c0b3522a1bd3e2804ac1f3e9922241ed58f31bfe8977d9b38e54e8066c9dbf14030e844eb0c50228a1c76a5d43629b1ec0ba059a0a1ffe8b538b790dd09038e31dce82f280c10a820c43bfa349a0d3038ee25ff059c2b8492076d8a8612a83a13ac3140e1607399a28d50cdebea465b11390dc09c419e81393a2f6b26e023a52c21c2b587809c48eab9d038702dd80b01c7399e82a1692a6e06fee5ddd14ac2f4b0e0d02ae47c8c3436e5c5c61ae43a07d2f9f9ed291e6bb7c7646f6553ecb14350a863e990e81f3d622c088c5728185e9d7866f85c2be957247538e1c1cf71e740cd42874ce3fa1854f018eb487de8bfe134ce5cc383c50d2b97d3823341af520652db38437330a136cec819cf086e5b9d0d884ccbfc4e27091e57a213e484acc879c0e9923a9c48ea96e0a2bc3a5878161123e0b412ff138f337bc09111860914e17839e380e58e7f4271d2d30383a3c09c620ce0a760dbf833ef15e8ba5ff4210a9879a9081ddd0618470733ff9ccbfcd4610f95ce977d334e69fda1712ff236c7bfb281d079df43bd7221b020f3a931f21ad4fdff478ae7404888437ac64b5a9a4c7c86aab117d291e6bb7c7646f4cbbba2c50d42a18fa643a07cee17c57a238c418e1306a57a8b815cd377005e89b5ebb6c98b8a46d36089bb0d45c02b48aa0ec3150de8c0ec02846a188a98e716fa9e565c1ccffe7a7c3815cc7dddfccbfca4ce0043207b76452c4dc2758773986a4efa5f3e29c5018aed0332cdcf13a16fe9554e80c57d4582a4c50789d1806166e58a8d111066f0d93701117c2b76054dc1f41150e52b3c6965106a4f7acc50d7c3d80ede13ff8e0e15b2a99ffc70676de1c81097f8b8c9afc39052726ab8ec50d133ff876d4ac1831346c5babc764a56295984ffe12aff05bbdf55856cab453e130bd52b2f5eac09962dd4b7f49ffe13695c0a4367872069621c334425ac5c6a4693f7b3b75ceff99bde17052b2c64856caeaa4d571be552276d40cd0265b5f281d4cffe383bd64cffe39df42819f0a01cefa3e22071d93a53449aae37cae67a09ab837cae67a1c1935a4ef0e404d571be55237aed2f4aef1a9a4c6dc942d5ceff949cedd8a1a316ea26ae0d69f298a1a3b74cffe0f339e26c5e9131e73f41b9d737aa8a7ca6e7704bfc5c6448f82df8effc26f45ff09a9491f14954165dbb94859c1dcaf44e0f050c7cbde42ee08a0160573d283fb85f731dae2e1b85cc33ce0856b0856b01bb49f6ea35f281c142831ce0c6ea8490a3db83a4f69e158f3c32f8d7af3b23ebb56fe1d963cd43b4b40712ff1424851edc18dd42b2931f41b03a0d7ca8721584d2d575ea137b6c else (if i < 8 then 0xa6a29e69d086a21d2898bf88cd2151be843a524740430524443d9e629e15233587c90c14d447a1861e5080cd61f243a514aa10030d2ea1fff5d3efb5a77d0fbc70b48cbe851de0d4bc859da70f52d4552d44c64c1944552980aa311e939a40f821698601544b1918668bec696c944b82267ec4d89fb143dca5b5013bf81f0ae0afd782764e1132b2a0f5e888193742548a22620c87f3186e1313be544598717b2015474431a1aef87721c8bfd4622e0614289a041c49053bbebe2881f8c6ef347a84174685a8e65a16e2fc77309a7dba7e3babf416e2620498a7f2304e119de55184e7a3d81ef5b091734680936b59e8552924120240b91c7996e08a7f78dabc2a30413f9c6d082c5af028162df24682f8492031cfe719c9cf0599539e476ce4bf001eea6673a60a733494e18ca68a06139007546e8a141483e530d2310322816e5243571c653dab6329ed5ba173a91efa9e0163adf66cba66b5d6868259e831166cd43097c919dd19aa6c43e87182952689b818cdc8e989dbfa771829e50d45a5264747187b062094248e3d3adfc82d2d1b26e6ccce905a04e19a41b24440830216c6057ad1b20742b813c029b2e3ef1b451ef1877fc972bd34b7950d9bc7d8a15bd17bd23b6e0d121367a0c5aeed3443700c84d5868f50c93703a366288130afeb40982b1b20742be9b2dfa354479dd251639ff8ec2914300aa1eb1c7c69a34162de7fead3d02cacd83387a1eea516b290b96e866145429da6ba12555ac7247d36d1eb9a8b160a98701f3ba0a6ccafdda7cd14976b89020dffb1c85a8ad95a48f84c63dd48ad9581486c4841cf5fc8c1032b5909f4e29c44ba00d6265199111328cc35ac7222e0d178990d68cdc192f13652c359cf0868bc35dcbfa2ee08a119a2f223d2ffa227401ac21c2b27dc32d3a08198a1ac003837d60fee3830d7ea7c5b0245ea435beb7060fee033c9720cae57038e06721d009b4c15218a3511394c03a5ede019fdb906581038e73fe845e0cc0518b1137af628d40cc19e3cd239a577837be3b20668bc89a8492076dd909b067e8fff099638f3b2e73d7989b70a23b0ec08a09d458af440cfc5f1a067e2fe8bd4fe0450b02620ce68942993a07c3f3b4f0c8eb96df44a341f811411d2c620de2e514874121d006b7d2f9d71e2b54132605a073e113766fe1468a853837fd02b730dbdea3c09a3e176b71c7e136a23e1310f2610a12823fe7040ec6dcb817391f7d3be7c503c2ed763bff09a131f23ba22071db6321953a019fd1659dd010a840dd8bfe13330a1d36294153c06187466a1b113a0f9da42429e1dcecc11865a7438a8d13ee6003d4bebf5383b3c57681fdc557c66a5d43427583ebe8895c77a9eafea7c7e8455d807dc715daf53ea40fb983b1c576bc7e8f151ac118327417f73001aaf8cc3a8c47d5f07658b7e3 else 0xa5f99ec874102164723221cac3f4bb511eb4e87e1aa6fb250d7c34f91cfc715a2915106de74bd9587e9737bf5ee843c374160686918eacc57bf3af2bafddb753f83951eedb4fe50944a0c7aa553ddb390993a9ec0e0a671de1f72ad99a9c66e649739dbe41908593786e82092d1f28e7904d14f5f412d3fcc1df19476c2a419b788d48334ff8eb7f45881cb0d0f051bd843bc1a7c15b171a128d00d0d05741f052d0da1e46e94fe74124121372870e74bd7d2e75fae3482a1a8d2fd5ce0a0495d84cda5cb0957fbb61dec6bb483e5697945f21907b0c0f7ad4abc46ca71cf9d6b6ab443be0b55a255e07e3727d0eb62e34251a01a1a0afb2e155c68a9718053529a94c5c162f53180d6bc1406e5c6e074fe12ed7fc29a90ff0445b150b23366092ab2bf09339eb2ad0a364db1ba1caffecf8c0ac97eba0a077c180354f1fe4b904112520d8891a86085129e656cc631d24682033e04265bf30e678b9e94ba2ae8f2c8c46a2549999934541b8755ea9951e3bf4fc89829ecc5fd227441dfccc2436042da60c989b106064c190e880ff330900e475a27445ee98bfa0515211a05154622e094443a2cc53d0cb99a95d130228fd01181115152eaf5cb4c55cf3163d64c6bb4e2e58553a70ef6adf651e2e58e22172df765b9e4a55fecfbc34d54bca4538fc715ade6dd74651d0a332b015c113756ea1855ee1dbde1d717e3160a789aa1ec3b54bca45398bf1d04a7626abdb167418110e8292ee0b402cb1f47cb8826e9b917b9206451ef19674059d2d43dca425468302133897a411ecd339209180b07269cdc92d1d60bc78a8311e3ad89a20b30c333683020b3266e5a7ed194ba832d6a3a8912ccc19378b9632de35daf172cf365f113172b0fbce1810aff89173c5c45e5c4fda36a446452b29b3e0c9b4b086f5f44896a2eb0e68914162b45938fc5c51a0b79e6a1a267af6561b5d12028e2e5c2a09b47d099df0321cc30ccd0334181351b1ee690419054c4fa0e329f45bdfc2d253e936323e8b6a4a8f48f5a9a6b0d9386946fa2752006b9443a5043a5351be9517f318e350e31f56663babf3c6975e7eb1c6a37d13053c1ede7b972067439bef147336a5d624277843221548db843ce84108ae6f6acd1d7fd234eba9b84f5e70c149e13439ae31308015fd2d8ef844e19c327ba79ca7b21031ce71852336e646fc31910a21e548439ff8bfda3a334e8ba8592061b4bb97500a015e7977006b9613bc261e774186864428d8246a841168fec0669d3475fe8cdb9b68eda950235baa684ef021abd1cb319a75e8e59cabcc7c8565f21128ef2265814b8b1720a5adf85e83338855d0297f0472814bf889b9402dc413a117e0ce830c6854b9052f70197b8447a5413b17b2c5ed85829f47b11ffdab032e74a7fa0130563648281d37600c439b900b9af81012ec86)) else (if i < 11 then (if i < 10 then 0x8c053f80372ecc479e522afeed88b38e0f321ce06aecf87785cb19098b72265bbdc8cabd8ccbdcd971f79deff242a3deb5063e87008d16f9ecea7909a2a2a045e75700be0c2de87682efb124bd64d310cfa11426cff54ea30fa3c57bea31470c9f032f12f23a2a97e5c30c0021d618511e4f79c350722ff219c5cb2c2964e366127b2c24d4744808c20761215218606c5430c01e502cf48148655ecf2809a2b8deda22e04f0225c6f6d3c0a737ab84b0b954660a11049d0917349620b09ecb08c327b2c9cdc921e6cc26a321f6c22ab2f90c301803002732d9121861f0130fef3a2a8c01e49f23e1ecfb4eb1628f71c4d2c39f354e669e7743c353e8b365196765418a151e2ca20d50d05d0d0461a9e55881663afc20057e1263bdcec8571f78c12406a99d063af4eab38638c22f6701dd870ce1b22feb0e5075ae7f27b228d1050a80288a70d818ed5691d0de0b0a8605683300c700f60b15816150c0ad040f609eac18c0c723a1bc2d5aae286bbc0c8a7384a4f617d842a01aad5c9f23a071056d7a34f6ac606a3f2e5a31886a0dee554ff0af76a22083d8e86f1a0d51a20b0d778b9fe4742a01669f82e84a4877cff2387d8aa1ee39a37b97d8bc6f0c356e8a141159481a877f91c44a1dbd84a6e8d3e9333483b711a9d6d6dafbbe55fe4764949ee84a4873b290d5ab7ecfaa51ecfb0d778a66a2f9fe47543dc759a7e0acd1a0909f05bc30d2c8a731e083d6d6837b969f810ca22083cd4ff0af763bc998ef59c4d524f609999f41e4cc77ea912306f368070c096ce7e057539e96c61b8138f25bc4485d5115483ac27894f7215c368f32eb363f41a61f41819e06e0987d1ec85da44e8889b810ed08d06648841bada0b23cc368570261ced1abd0271e6851728c4f82310063e2233a9f0e5031a0f6ee467ae8af70e7410a818e9b1213da74641b20877457b806238c8eb194ae0949102879b88b9663dc00ab0634ab34623ac02ad359e854b58a0eb03fa8c3e80291ff6aacc2baa29ebd082b03e3ae99a75bda406fa081232cfe6a610f76244bd13e44e37d0b923ae2ed78280dfa0e8cb91d0a76412e58cd3723723a1501b92a41220847c72213767604d4267c570708cf84d09b6b43acd53bec4d1043b8b10c7a05011d91394e3d497f09c31e1c6a4e44e56916338cfec969100669fd44ae700a1ad934c4062adc76b3f7bb83b6c0260ac0e8571b2c386c1db4b55bbdd67fa39aee694db72c5941f2db43561f10e28074158571b204d8e183091096bbe98ea399a1875197c935f0e3e3a1e1d8f7104dd37d59a6d9561d31c7abc9eb52b22e51154b802dc0236cff95142c4f3112450de8b847c8414982450212dff0327d1e64dfc093e834c9f479a3c908ce6e4df82678abeaca8fff452d44a5e640691f2a47d8a9311905512d89a9799c413ac4f04728 else 0x49f8494831df8961351d0da0623d509bdff6463c6747cfc244a99c902cc51b3526735df9f927c80a10216360502c50814f022546fed6f5a434855e951c3aa5f3aabdf7bb3dcb3aa977e6fbdc74051b33d91aa87ee384bb0e6c2e5b457f71c63d67c9ecfbeac0e312c249dfc7814e42253c7420a0700787e5e23ac027903d0797d58208c3295a8b0252398d4603088eb2daf927e08224a41a95b318c42144a3853acf24682e65b8278792701b89105fd065b0d7f82da69dee3bbc4a3b16ae5895b3029d668a3dc718167ae22012598e8c90399312a2b8040669098172112d4243c125c8538270826fd581c77b450c8851ea1941330119cfc03a04dc68490974d5070c42784cc22d33920af9186d5fd45a62a99b937918ca0723f0f53fb7d4fd47e0fb77234cc7bc83722affa8a7f5ce0154486b06247752a2a97014bf80a403313a9fdcf90b693d582e401bd5890c66cf59ebac31e693a8ae7b8ff66bec82840638e37b0be741b30a632cd18fa3da48d054cd074661a8b4bf7a8b283d9b8d12212f51c7d30012efb986e1b7d9ae71d6e34311e533ffd06d4bb0e20b9e7413396f15fdc75c9ecfbe7b541d943ad73bcf0f6f5f4d5a6422ae23cec113bc1a3723117072adfc8ec25c1f0f91d228f79cd1bfa44e8958a7aa0c7c8ea8c7ac0e89228f79d848016281058eeafcf1a5d8571f78d7a424da3d57188b9d4ec203d801587dc4b890dc2bfa171b89fd9c8885d388a94cf5396ac902a2fab064f5493c0a7b1a8ed28ea3757454350669fd8cb6f116d2422d4c44a556a5e887fa11f0f309a22f0b4158d920b76bd08103763ae7c14ba2bc48255453d07bd5a07f994c41e5112b3620dd4bd13df09a0a7497684387b2934ec7322e45e8881caa478764d3bccc65a49d7e5b73664467b89457422834518755d2bdf07fd84648006ea068c046fc54544598713be4c589a0a1271207465e75364ce6b926e22636e5aadeadfc9681af1c2aa5e479814c5fdfacd93ccaa66163d4abe551af82f7cc437bf295ec255f2bcbc087ba9868d7854bfb221d2af9435e043dd50cdd2a9fc8a1eb446ff05e0e012699afd49518540247db950722fe825e1112212425a0b097c8bfaf6e244a80c09337b2d7c2699f51f4c822a91734fc4b47ff4a3e8dfda10ecaaa45c856fbb6297f628f51eaf740205b1db04cccfa0f2663bf54b536e2d911157f76cf3cadd273803c863a34ed3f1d008addd9af8e84d70a5ee227400582065a274092bb01897e0d130d7085105abff6e86a35a34241603ba7951f76dba599721678854db884f72a97d010a8a8112bdd976f78cc8db9ef54bd0e19f3dc9e5dbd9f38af61534e9c57f71ce2bfb3e635ed28a9ef1b64b96750a45ce83c6fed7cfecf951a74e2bd8e2bfb8e635ed39698884ccfa0fda60c739a424aec5ce0c4758283a88863d0875) else (if i < 12 then 0xff85840bc1102e307ab6799c9032f42863311e685ab6493960f061960e5cac2b6e012f0b97ed5b85cbfa3dc1c33e3e151ef1b06d5f94eec3402670b4f3c2cb689c0a25e464935a986f27acc5c00ae85b291517130dc6fb3376a270fae17c8dd22e1e7494f0dcd4ed22f9f885a8ee8bb06a7b3f79e138a129b8dc8b8913ce82d8df712f2a5484fefe52e836420de527fc0fd967a91681c8be66a4f979d7ddb78af8466b1e84bcbe2bf71a89c8ffeaafdae450a43348b6798a7928df5ecf33cb31705b12139a930a6d6530819f23c601381e91bbf82b0b3a2753f7432e45de1e773224505917b3bb92820259642c6ce8bd1923674be9b5815667f01d485f4055998876d7c4d0970162324218152964bd604ae3864b3b172e121cc3fa4662470cc5e1436501eb4bd7c04ffc39679142dbe5e0565b928b3b86443d9d7c6d83821c43b132d07a15f900925e0241b8875092bb6f5b2a619651240423a086c2e553ddb686a9b5ea218e791e1ba1f810986d3fd7416ff4d644945dc12e91632bf7d0f469c347b0ec0814f6980c776046a1b7b90ef82225020a30c3ca979a79ac2014398b806cd3bc5f8889405088769334e4291280a11b2d2669c8503a0f44dca6afe1a953a98b80d4e1198bd26de2cd610611138446c41249d0225014221da4cd3b86850909dd5fe27092f3b29ae276fe9dc60a7910e1e6698c341612443d359a630d058494ff06a35e5443aca66e4443729a8a794ce83443a8d07654c1f876be0d46ae0cece87f025f9542796be137294cfe1cb29c91329d1173ce03413aae561f48cf8ca77db113f9ce5e6a346a27425261b5d6436e4a9e705fe89fce779059d877a603451a056898b1f288a340af944c2e8e5ddbaa601344c48e60341a88a369b2bd00a9279ce8864469ce174c2e84440a9279cea7232579bf776ae7a218d448f3bd0431f143fd2ac7909a60547b5f7b21351cfd5813690fd587940ff4aa135baa8111eac39700be0ce4e892f562b752df86e99db38379b40386531427906f36b4ecf501c334ea13c0273d481e9fa66ba2a6085311279f8038604b8379b42469884b122c66cfc93cfca67304113428c64257441559a9a22a93959bf04923c52a5d4368f34bb0ca100ac910627823d679731ca82172ce2bfdc708f59114088751c3516939a44861804430d45aa62218615214e7a086196c698b91a63a75c8cf544d0a1c300a9fd44ae70d74c64440a90f89537916dc7b3a622182812c43050a912220a8a3e7b300a9fd44ae700a1ad070c09653b2bb9e8e7c874c258ddb73773d18c95229884b27bbe902684909ac4c7fe8c904e16d581376ac6263fcf284abf5604dfab07a8ff7bfec50d2d44ec8c434b5138b5810a28c428a8122620cd2d45f5627b8ebcf310ed24fed2d451a53fb99416620c1c58984909a270b46483fcc0b9089 else 0x150e805ea85b91c2c204))))
def rankMode11 (i mode : Nat) : Nat × Nat := let v := packedAt rankHeader11 ((2*i+mode)*22) 22; (v &&& 31,v >>> 5)
def rankHeader12 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x733368f00000033059232ef4732bed032a4c7324e933240c7320b5231fd8731c5540000003196123180c731608c31504731255031164730db1630cb8730a14f308c873061913050c7302a50301c872fed132fdc472faf102f9a472f758f2f61872f35512f26472effd00000002ed3d22ebc072e73520000002e49900000002e1b102e02072dc7902db9072d8f112d81472d54102d45872d14912d05472cd3902cbc472c878d2c79c72c4b112c39c72c04900000002bce102bc0472b7e552b70872b43902b35c72afe522aee472ac4100000002a87132a78072a48122a23c829ef9029dc47299fd3298f07295c9029490829171128ff4828bb9328adc72881d2286fc72843d228360728089200000027d65027c287277e932770c72744d2272b4826d35526bdc72691d226840726581226424726175026054725c5d425b2c72576940000002544902532872502d024f3c724b4d3249cc7246f90245a0724339000000024015023ec4723b7d123a6472370902362c72329d200000022e95122d74722a4d122954722718f22600722341200000021fbd121ea0721ae55219f87216b1221558721289121164720e69020d60720a1922092c72059952049072018501ffe871fc0501fb1471f7b521f6d871f4e8c1f33071f06500000001ee40c1ed4c71eb44d1ea2c71e874c1e73871e45911e35471e0b4f0000001ddb501dcd871da88f1d98071d78cc1d67871d3d8f1d29471cf50f1cde871ca8cc1c87c81c4b541c2d481c05900000001bc7921bafc71b85901b70871b43521b2ec71b02d11ae9871ab6931a9fc71a9d011a8d471a674f1a56871a318f0000001a0b1019fa0719c55319b687197e51196dc719358f1927c719040f18f30718c61018b847189bcc188e071861101850871821d218128717e31017d00717a88f179ac7177250176187173a10172b0717074f16f6c716d20f16c187169b101686c7164c51163e8716109015ff8715c71115b947156e951560c715348e1526c714e55314cf071491d3147fc7144e4f000000141e50140b8713d99213c5c713a0cc138e8713539113400713158f1305c712d4d112c70712939200000012581212460711f29511e4c711b48f11a6c71175d11160c71117d211058710ce1210be47109090000000105454103f07101b0d1007470fdb900fc8070f7d540f6a470f3b520f29070ef2930000000e74e30000000e10990000000da35c0000000d331e0cf3d20c971f0000000c49d90c05910c03010bd6100b809e0000000b1c5e0ae8910a8e9e0a571009f29e09cacf096f1d093ad108e99e08b00f082d6007e7d107959e07774d072e1806fb5006ac5e0690cc064399061b0c05d61805aa110562d8051f9104a3de045b5103ee5e03ad5003271e02dd13026a9f022bd00173270134d000a36200619300001d else 0x4a505e39875e02d05df1475dc3500000005d8c515d75c75d49d25d3a875d10505cf7885cca915cb8c75c7e910000005c52cf5c33885be7d35bc6c85b9c105b8e475b62500000005b25545b15c75ae6905ad7875aaf905a9e475a73900000005a44515a33c75a06d200000059cb130000005996900000005963510000005947cc5936875901d258ee4758bd9058aa475879d20000005844955830c75804d057f54757a7d6578f47573b555728c757054d00000056da0f56c7075694d25685c7564f51563d47560d5155fb0755bc5355a5875570935562c75531d1551cc754f25054e48754bd4f54ac87548150547087543e120000005417905409c753e1d053d40753acd05399c7536cd1000000534ccc5336c8531a4c53060752da1252c28752a48c0000005277d0526207522fcc521c4751e51251cd87519ed051828751375251298750fd9000000050c09450b2c75086505072075043d05032874ff60f4fe0874faf524f9ec74f77904f5f074f30914f1a874eecd10000004eb6d04e9b884e7d8c4e65c74e420f0000004e21cc4e07874dc4104db3874d86904d74074d584c0000004d378c4d29c74cfa504ce6874cb6114ca8474c66d34c57074c308f4c21474bdb144bc9474b9c124b8a074b4e944b3d074b204c0000004af6904ada074a87544a77c74a584c0000004a25104a174749e8d049ce0849a64f499607496b50000000494090000000490cd000000048f04c00000048b290000000485c56000000482bd100000047fa5147e0c747a710479647476e9000000047508c473d47470e5000000046de4f46ce47469c4f4689c7465a9046450746288c46130745dc5045c6c7459b90458d074558514549c745141445020744d411000000449a5344840744510f443d4744095143f74743c81243b507438050435fc84333514324c742f8d242e50742ab95000000427f10426cc74238114227c741f90f41e88741c6cd41b907418d12417907414d50413d47410b5440fd8740d4510000004095d4408807404a514037073fec953fdc873f89550000003f53903f3e073efb903ee7473eb4103e9f073e7b4c3e6d873e20153e0b473dcbd33dba483d67563d55473d1dd33d0f073ccb150000003c95103c86473c47d43c37473c07503bf9873bc2133baa073b73d13b65073b45cc3b38073b06d30000003abc143aa7873a7a503a68473a33d100000039fd9039ea0739ce8c39bd07399f0c398f473958523945473915d039068738c952000000389092387b4738495138348737fd9037e38837a4533794c7376292374fc737031236ee0736af9036a087366cd2365707362d0d361f4735f49035e30735b590000000358350356dc735431035344735069034f8c734bdd034ae87348810347387343bd4342c0733f45233e10733add1339c07336f11335d) else (if i < 3 then 0x72d10772c98372b9c772b70372a108729e43728e870000007279c77272437261c7725f037251477249c3723c077237437227877224c37217077213837203c700000071ea0771e74371d4c771cd8371bfc771bd0371af4771ac83719ec7000000718b47718883716a097167437159877156c37142c77140037129087121c3711087710dc371000770f8c370e78770e4c370d70770d44370c68770c3c370b2c770b003709fc7709d03708f47708c83707ec7707c03706e47706b83705dc7705b03704d47704a837033887030c3701e47701b837009477006836ff8c76ff6036fde090000006fcdc76fcb036fb7486fb4836fa3c76fa1036f90076f88836f78876f71036f63476f60836f52c76f4f436f41870000006f30476f29036f16c76f14036f06476f03836ef5c76ef3036ee5476ee2836ecf486ecc836ebc876eb9c36eac076ea9436e9b876e98c36e88476e85836e74876e71c36e64076e61436e4dc70000006e40076e3d436e2f876e28036e1a476e17836e09c76e07036df8c76df5036dde096ddb436dcd876dcac36dbd076dba436da6c86da4036d96476d93836d85c76d83036d72876d6b436d4c086d49436d3b876d34036d26476d23836d0fc70000006cfd076cf7436ce6076ce3436cd5876cd2c36cc4076cc1436cb3876cb0c36ca3076ca0436c8e076c8b436c7d876c7ac36c6d076c67436c4d486c4a836c36476c33836c25c76c23036c09c80000006bfa476bf7836be0886bddc36bc8c76bc6036bb8476bb0c36b93886b90c36b83070000006b73076b70436b62876b5fc36b4f486b47836b37086b34436b26876b23c36b13486b10836b02c70000006aecc76aea036ad9886ad6c36ac9076ac6436ab8876ab5c36aa8076aa5436a97876a94c36a7ec76a79036a6b476a68836a54476a51836a41076a3e436a30876a2dc36a1d486a1a836a08476a058369f7c769f50369e44700000069d14769ce8369bd8769bac3699d48699a83698cc7000000697a876977c36967486964836950c7694e03694047693d83692fc7692d03691c876919c3690b8700000068f6c768e90768bd5068a288687152685c87682a1200000067efd367e14767b311679e07677d8c676d08672b95671b0766e65166d88766aa90669747666d51665b0766301166210765f85065e94765c28f65b387658ad0000000655f8f65498765109400000064de5064d087649d50000000646d9064578764229100000063ee1100000063b610000000638490636ec763405000000062ff5462eb0762b311629f47626310625107620c5461fa4761bfd561ae07617d1061648761239100000060e5d000000060ca4c60b98760845200000060445260310860118c6003c75fd4900000005f9a915f7e885f48915f2c875f088c5ef4475ec8515eb7075e84935e72475e else (if i < 4 then 0x837fbbc77fb4437fa6877fa3c37f95077f92437f79487f76837f68c70000007f56477f53837f41077f3e437f30877f2dc37f20070000007f10877f0dc37f00077ef8837eeac77ee7437ed9877ed6c37ec0487ebd837eafc77ead037e9a877e97c37e85477e7fc37e6a487e67837e59c70000007e3f087e39837e2bc77e29037e1b477e18837e09877e06c37df9077df6437de6477de3837dd3870000007dbc877db9c37da1887d9ec37d91077d8e437d7c077d77037d64877d61c37d44c80000007d35077d32437d24877d21c37d14077d0c437cfe877cfbc37cee077ceb437cdd877cdac37ccd077cca437cbc877cb4c37ca4487ca1837c93c77c91037c83470000007c73477c70837c62c77c5b037c4d477c4a837c32897c2fc37c21077c1e437c0e477c0b837bf9477bf6837be8c77be6037bd5880000007bc0877bbd037bae877ba7037b99470000007b8b870000007b73070000007b65470000007b4cc70000007b3b070000007b26070000007b13880000007b03477afd837aefc70000007adf077adc437acc477ac9837ab5087ab2437a9f887a9cc37a8f077a8a037a7a070000007a68877a65c37a58077a55437a47877a44c37a37077a34437a23877a20c37a0d077a078379f90700000079e98779e1c379d40779d14379bf0779bc4379ae8779abc3798c08798943797b877978c3796987796203795447795183793a887937c3792a07000000791c47791983790bc779090378fb4778f88378eac778e80378d60778ce8378bb0878b84378aa8778a7c3789a077892837884c7788203787207000000785cc7785a03784b877848c37836c77834037824077821437810c8780e0377fd4777f5c377e80777e54377d78777d4c377c44877c18377b3c700000077a087779dc3778f077787837779c77777037768877765c37758077750837738487735837727c777250377160700000076ffc776fd0376ef4776ec8376dec776dc0376c68776c3c376b2c776ab43769a877697c3768a07768743767987000000766247765f83764f08764943763b870000007625877622c3761507760d8375fcc775fa0375e64775e38375d30775d04375c28775bac375aa4875a7837599c77597037584870000007571c7756f03756147755e83754e087546437537877534c37525c775230375050975024374f48774f1c374e14774de8374c90774c64374b88774b5c374a8070000007494077491437480c7747e03747047746d83745d877458837448870000007436c77434037426477423837413877410c373fe8773fbc373ecc773ea0373dc4773d98373cbc773c90373bb4700000073ab4773a883739ac77393437385877382c37375077372437364877361c3734f47734c83733ec7733c03732e47732b83731dc7731b03730b4773088372f14772ec8372dec7 else 0x887e838870c7886d43885f87885cc3884f07884c43883e87883bc3882c07000000881187880ec387f88800000087e64787dec387cec787cc0387be4787bb8387ab0787a6c38796c7000000878107877983876148875e83874e07874b43872e48872b838718c80000008706c787040386f1c786ef0386dcc786da0386c94786c68386b8c786b60386a4c786a203869207000000867747867483866408865c83864b47864583863347863083862087861dc3860a878606c385f48785f1c385e40785e14385ce4885cb8385bb08000000859d88859ac38589888586c38573c8857103856088855dc3854d48854a83853a080000008524888521c3851148850e8384fe0884f84384e7c884e50384d48884d10384c08884bdc384ac0884a4c3849148848dc3847d48847a838467088464438445c90000008436478433838425c78423038415478412838404c784020383f18783eec383dec700000083cf0700000083ba0700000083a547000000839347838c03837e47837b83836cc7836a038344c9834203833088832dc3832007831d43830a8800000082fb4782f88382dc8882d9c382bec882bc0382ac0782a6838297c78295038286478283838274c7826f43825c47000000824e87824bc3823947823683822608000000821187820ec382010781fe4381eb8881e8c381d8c781d60381c58881c2c381af4881ac83819bc78199038188878185c38173c7816dc3815b088158438144c78142038134478131838123c7812103811088810a8380f7c880f1c380e40700000080d40780d14380c38780c0c380b30700000080a34780a0838092c7809003808247807f838071c7806f03806147805e838050c7000000803f47803c83802e07802b43801d87801ac38008c78003037ff3077ff0437fe2877fdc837fcc477fc9)))
def rankPayload12 (i : Nat) : Nat := (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then 0xe1463c8a4ae98108926d29cff9a418a46cd4bd11824953c95d25a6653b913848e38d2281c453e56e27c3d2fec77c2c4dca1bf13a474bb805be200e7bb590de334bd821f9e1bc66b19c6319632286be25ee7bdbdcc250fc10e62ea33482ef40c02e30292fa89d6710032252d31825bc26c98d3821431d9124f27e814ea171fc066a8f9e6906291b352f44609254f2574969994ee44e1238e348a2e54f95b89f0f4bfb1d0de0a4df89d23a0157286f2ee5ec14d454be08401d456b297dcc9d343f0438c0acc520c0158c9c3003f9bac709a542cc379eb957897763325139848cffcb537e7c914b639246e9907cd61b92510e8501ea1d50883192881759fa1342d0d77cb887f83d8f3e4d4deff9805bff4d48b14cffcb00740cb3906ed297c10cc3506a14bbbcf2b2014378b979eb94bb805986bc544803d638d67106042d0fc1086f50a97f181540ea2b1996612cc5d22fdc557b1d8f79720cc842cf8e41cf0cd905088c373cce399072cb7d7186b1c39bc35cbb5c7b3ea84bfc45e4d56fe98d9f798a38703898e1b4fff2e4180a9e030e164dd3501dc55144a1f1c163c5e0e788940e641cb7660e3919b3398619b2730b0b7ce1d507098520b4450d62679250c7ba8430d96fa31321eb8edf09b944d03a33b7884627f94c21f2dff3aa0738e762741517f84d407b9e9b40e23081aa183640c8521b4459f7f244c81fcc17a285864986c9a57e9b3ea0d6c5bf0d89059b1217078e076c73f09bc751bb738f57cce7c79654f8be35d42253cc5bf073f4757cce7c067b17fc26e2bb5ea49aa16ddf86ea1b7693072d9c7c8430bb73a84515f70b9066ce241730c4d14b778a073cb2c153cd88586e81b43087dcf2b8ef63b2ea87e754724eb9b072d3b24e199720d6ef705031bd4a2462d62f1ccd43644e83830fae0bfaf6540c582cbb0d58346bb16451973632f6085db3b54077efc9d3681d3f48c2066cc58649a290da7d9bd42840f4a87c4e831c81fc13f82d8b7e0e5ed9f1929e6c485de42281c0cca9b62416dc531cb8e72ec73f098b541b3486cc5bf1d67ad91457c1850e9848a10f1cbdc241c72ce9b70a8f21032c5ff0999480c4c90b8bc99316452c4c9038b4a89920b3c450da2d01e761db9067cb8f5c5c301f71e700337906189909f2af398ee1720dc57a23849a1843efc561df90c99b6b2109462a7ec418dddcb54717cf8f622c6e8ac2704eb150777739a45aa09a296f6214626a85b0c90f3331698ca33096da54d71b2110c63848cc51864a7b5d5937b1163745c12855070a1418e796c2d78563715fe0e5203591ccbfce31c153c83c16eea08e1f22859cdf95553fa7a27c41961c0e9a3c4ad4c4a3c019f345a1346d1d268c4513e25acd2668e32fa625f850f03f855c18b46d3476d434df8c182d125aa09f0e5f7c9df64f54384aae1ea1d1d142 else 0xb1161fe3fba517b9dfebbc3fe4222220951efc8ac2bcbc4fdc33c911ea0a5cf6a1a4ec0a3ce5d6e8d425283b24ca71490cec8269724da7015202ffce6f6ff1c217a0dfb7e37f6802707ed8ff58bbc3cf322e75ff213215e622dd2e431bb10dde9690183f6c06f7940489dca2c5430673685ba3f1869d905cd8377c30209420cf5ff2108b786444e1a69c0e4c582dda627b9c32e5de5ed059e7959a1f765c7ee706180eec50f2ff46056b507b1bc0c703d405b88195c71c62c98ad642641480968d418828260e98a618d3cf4cccd537c3d334b33956668e781630869e6d0e691999ba673e4133517a8e99e48d6dee3d90e71be817a5003bb134e8c0ad53a62e8148224b1ee489c5f92a87e0b740adfcd2271a629060a2053c53d0a1051549ebea4bcf486f36816e215cfc09b9407a9bc1932475ca71baa60520ad52063e9671dc26c99cfcb5ac89fa6284ae781416ff0c4aa38f63f0d534c1b5f862180961f489203bb38382dd030a128c9289c83099d5a00c3ecbf35a1ad2282a8a73340c8c432b8e11eb940294fd68a182e6708cd8ccad784e81a59067886282dc8332d64f4d4597ff4fd2ce38aff63ecef3c7086b0078bd72cf5d6a5aa5f3dc595b24b6f41ea04573274c53fe6a692270a15cc928905b8870c26e518cc973bd7d6394283d314e6e819cd9036b038e39a5e3061c0bbd0dbc477836d73467dc1ba9aae30882be5dfb28292b27a5c2e3386c5ed2fab306612c0286b24d25dc14aef0de1a18b66432eeca5ef03959faa23e44f63ec2a2417cf7fa612d65f070cae391a8031e2016dee8c2ed826e504cdbf06ae9b82c56dc02dc40de916a389d73e45de1afe8a8514bf8285a812c32b8ef9e7a6a28e1dd35408bf3352c3c56583b00b6f661a835caa2733c83eb191865e398a618bb86f2c421b59c47a65fab300b6f66195f5caa2733c942a5f2da5ac70bc467898ccb3093d58f3c64502187e9a74494f13de91388758218b3d125d1ab0d85c92520dc922448cb0e0b917291ca2d03b8192506d018a7f3c2839c2c39a70ed9339ab63e53f50821f64274316626e53cf888c32e016764083c8b3d921d42cbf2b3e9281cf561770de97c10cf779e01401d034be1bc6340e50af3cd586dda4f4a692eeacf31745b4be6821830216a8a08401a89d6714c35e2b958cc802e61223e4564044963b7f7b0e943963edbc5167599ab173a26a5a0f9679a418a46cd4bd11824953c95d25a6653b913848e38d228b953e56e27c3d2fec77c2c4dca1bf8b2475c285634e578309bc7e5c8e5b25015ac2d51cf232ed4e7575bbbf99ca22654f1e179490d61f215393e4b4a85080c714fa8b54644814f69a32ed9fe47328c3bacf9495c5914b265f2129898c960a615acbbf90a6239786498059289cb1974444a51384a714961f1c322d0388c32ed437cc75a293aa6) else (if i < 3 then 0xaa82508efc4d53341bd3e28c7981a9a7ed2a58874a16a249a9a0bc3d8a5ff287cb3e47b06821ce3825196bec43c59efee24d5acd11e0ec15acb0d8458701790535b164439ab1965708a7da0252ea5dc6fbfd41b216c2381d74eaed1599b8f65d4658dd2b843760b4baf7ff6a424728471765d5cb8cf1b20ac1082d37706fcd08705ae24128dd20a0944381305ae9c37bfd408f1ed50abb376094d7c1bf34a862db1bc8ee5c6e82f11e32c0e8f159666c098871c382d6118987ad6236560b58c3d6af2e23654923811889c84181daa3da5f771e8764defb38ecf260c19d15222b7c199eb306b7f4a87993c648c3dd4990b4a8a91106ec9b8019809056e86fc66a8c85a4447261c33c37c4f18dfbfd6439f419cebfe782c0add245b26e0223dbc198e139affc808e117b926d38bc9d7284a50703329219df5ef2932bb637e5225380ae416fba8eedef5497adf06e3240480906f308654a345be3f65d7e9f901228e3988fbece3a8aa2988b91419eb8c06c598cee1830d11675c6f74fa285e38407f215d5234067c2853b7de4391c09859842538585263a22833a92d8f450a8aeb414ef1968d89140ce757c24e8bc381ddbf3c83388ae9c70ab0a4c726188b9141991278c52dd19d41daad1782dc3622d49fc379c6940fe015116ff5e1d09fe429d653843cc84c3083becaf377a43763de90047c15ba13bdbf2ab7aa470321674a7dbfdd3078d70684bc38dffc853ad8bf7b27647e556f55e2df023f797b79bf23ef860e7f6f5daa5c8edaf2dc23848a352df44fa544fea248d3bdf943d928338e893619c5ce4370a34ee12895d5d49d2acb22df685c027ee93fa3c5bc3f0e2d261ef778588d5234c8742615b212e901a37c7f27f3f9084fadf067784a5ba0332768cbf9ce88a0add16fa2513fc3466a9d49eb91b9f69fadfd2a0244fbff74bae301bec80b0ce9d6bae879a5e16cb25c15bef0e9e89fd381f0c0e982c43129c522d3845d0b23e20e4588250bd7373ac09e6e450b1cfd6e89d14911261194ed4061c8971715a804381a34ee1830d8bd2c58a065c8edba11c0f583761fa8301a87f4280c5a3ce22273488bc5452c349d83329d237517f49d5040fe67d6fa444b6ab45e0b30d27742514de544e4ee228332768cbf9ce88a0add16fa2513fc3466a9d49eb91b9f69feb23b66153a0e2760df6fd3dd0c439f0c541bcbd810bb6f4c3ce5daac9469da8bfa4e27673c058677504ce381b88251ed44fe89234e4c20de9ef0b27f0ba406a1f1fdd2fd9162f8634310ed2001bfdb108253b6461b9f58793b706b5c28d38dff5f7fe4ec4fc8d1c2b7d12b0dcc621da54b6a845ec3511f02abaf60d3c395fdbcbeed9264a0ce3da33556af850a770974a12d6037e27ee18dfda4d11c2e9e6884b58f9d071011daadc60dc0ac430120add3efb509dca23e2520750 else 0xecdbc9e5d2e5b3e72988269cb9e4b5223de76dcbb6d0dd36bb2eacc499cd9d1e26435ac75e9c223528d35c9118571bc4c86b5e9c623bf7a82e4f9f5211858eb7c3d4847d0d94d646ebc67971a9da8de00d258cd05621f494f34bca2f409735d12072bf5c68fca8f6d27128a123e567d3543ea5c7d2503812a87a9da80b4ef61d26de208ec65317001d9626fd070c38e47c474e47c168795f247f12b82ed47be2a92c72db9c6e92443bfd4a17e6801b7b14a33415aa110e5c6178130072cd0dee3945e88fa0097514431593eaa1cb8d552be24c1282723f0bdd7fa6a804c9382d26d079be3a80b4158571b204e01b7919ec93b665a0b047177e3a86ee3593053c0e73258bbd42908ba93a9267372775070caa686c4394d04a00c8b8a119a7cc43c6f35f93a55469d80369247d0ded3f6853443825c4a45d03410e0963797149671f0d61f24910e55d1c15a8535c176850931c3e621d9d435f93a55469d9574692375c83702ab7778e0b45545dcd0bbeda1bbac578483ef05b824a78aa882a930178f993c4bdcd5e075d50ad44b8a9b84ed971531ea72dfce95b5786923deb1d7542b5116476d608fa2cfc9ab72b925ebefee492a06651029ef888c865ccff826c58f098ace5568787725d1bea7e266b415a0b15ff60c986594340dc912a92842c79d88cbd1f94942164c71e3790da9da5a292cd79c32163642c8256f2e640561f1b9d4282d05a7aa0b22d039049db1bf1227c572dc17ba19724d9636fd17c917eb8d63291842c7a679c7675086b82ed2d14966bd17c2160ac2c8d96f38de49e93f7858a0a8e15fae3eec6f38e5c5d7a4b0b282d1b9aff0ba8d045c43e3704b42fcd33ef307fd91ed919af1e204f40b961ba0ef888cf1ca21f23a4b0ae0add7ee3925e81287b651029ef448e0f8aa1026294e3acdd02e5b468dd2c7c47167009e47fdb04a1ede382d0efc37c1253df053418034221c50dd8bb196074159bb1b204f81b7919e7bcf38e1c177e3a821d9f78cfb429a0940e8250ae21e76c036f233cf79e708e2efc750f4afd2c3e868a95f0665d5539b92f6a84d099b64670ca6b99857eb815eb2c63c95547a8a818178cb11e6b60090b387dd0cb81285910eddc998ef0fa4f602ab779923bed1bc24d17dcf07aa7bb28fb68ee785dae6c589abb6c924d567df07aad1d781d786ab4a058f07068f29daba97324e73658a83a58b2e279cc3c88ed82288713a9241089d35a6bc228bfb8615c4382ba2e32c67821e57eb854724c6597760d152bf276c6c4528bf59fc3c1a87908b930c786597759e116429bb04271d0a1485042114dd8cf2e20ac6cb1308ada66cb437b6c4e8c84558639c70090b420946dabb65833658188113a09443c93f7952ca3086922fe61e95b6ff33c49db914221c1289dcf6e9c618551eaeb5a197c9040cc71ea39ddb119d0)) else (if i < 6 then (if i < 5 then 0x3cc5ee99429238e789492db9142c75ce6934a0e1078b820cd2ef6e3b66858215b8495db0433d93ae296c44a13a6764e19d04ea39d4e2e2881af52118764f2820dcde8e11321ac8895773620ca086b5aec3c4c9072ab7044f9bd88a68c70fe4106d72721079ccc29942222ced9574ccb906086e82751ce12576c724ebbec603fe2c503677206522d199082ca82642118717084c2f49e14c92492d93539d8e5adc8895773620ca086b5aec3c4c9072ab7044f9bd88a68c70be30d68ced3ac72aee6c419410d6b5d8789920e556e089f37b114d18e1c9f0d9d29054300deb5b804f0aac4001ba23243c2f6089bdb643f301ceb9133b2d12396d9341bd073dbf810bb6dbb23da3918f09b06e24e5b7d7227a18871cd8131bd7994b7aa81e8debf37a58d073cd03b1cf9551573a2df4c1b835ad72e66438d195561eeacb9c86b8258d064f13e6f42ce47433d8345f772483b72aa703b648f5f3bf4f34b9ff61a825acd0b004377a44bdd48e106e20c60c78c91504c9344b151b391169625ea12d63d71e638622f95544540f865eb8f3d3691d50db418ec3196c85099d4d3681d65e8683168c385b9944925b0c18dc76f94d3444f90713ee06dd8c1826942c73e68be380f8647997274c4859247258889ebc9a9cec7261e60c8188373668e8de933ae4444dd972260ddc7aa77327c165da26a5b8ad53d1a128615ac809d0b650910afd4fed39fa11e5a0bf431c80d34133b86dfa18ed19aa619bf8d21ad5fc216f4239e8f3a3953775cae59f996d82ea3aa8fd0c73f33361f4ba9b184c8fc8781d4286133f1e4ee783d68c0289d197f4518a59b3e2774684f8a452143131c01587c6c569a0b3ea0141baa62713e8afd07820133b3a863364a2a91309d530a52a12ba6d8575b0a906c4f0e6e1a3e2442d62313d0c713300a42d60ed266014778f57bbc5c98099651dbc66cea926aed89ec24b58e7c65a3100bed4848e508e2ec02b9719e3641582105a15e59fe1499844865a1d4563642385b17e2946381d30e235288f730a014d7827d1352db0f90b90fa53053c784cd8a5016128d086640e57eef80ad8490054bf24f45fae117c0b294c65a515cd03ae28211d0c7a00bb349ea8ce78afce1890a8be2f900ab05ec8c6800b1a46346f68a19ec80547a67fedc486623a2126682438a317214e4d923fa3a5493f7952e15fae0c2d4d1d0c7a3dafb4a2afd05859d2379e4cc4f23e262a3cb4173f41d6bf431da2d81a443f09290647a676238edf84897b2935e8f50e2d07e88cbda7ed05fd4b4c6f8bec65e8d0bd8a4946a697935e294a3a861a27dc468c72710aba7d12ea32ccd8594a632d28ae681d71410b99802ecd27aa339e2bf3860aba1c35f25d783844ccaa88bacd9dca286b07f2d1099ffb7120fe7bc89ec13326aed8768ef7bbc89249ed0dd3133a56ef79da else 0xee3dc19203a58465813196449120d41e09f53a4249e30f630c43e8ea923c48e3259b653a850c871d3d398a0d6da5426ef356d980500981d1966ec6c8bb22aa9cb08f734233c14a8de9f41143e10e11fc79023aa154e04f610c1766efedd532c2074438299b7eb7f0e0128bb14e6bc43ad308e02c6f8d13626140e99b02607d2895919a1be5897b04ee855d8f705624d7ea3122a0140180ea86bc10a3b6c653461eea61eeaa35f0435e110fd5e22f289c8851db11c877b018f704d8310638349d092e944502cee11f509a15fa56587c16d5da2b37604c0e82922b2c4cdec2497ec4927076103a455c9f8f201346bae2818250c00aacca5acf428e8b697f7d1e39c9e2325b43cae1d2a7b4251d84810238df1cb2f980e4acc0282d296b159b234360154ac92b0045f915362ec4e7c9b3dfa1c65dc500a0b54ac56601518c79266fd0c7479fca4ccdab2658639eacf9110238048c402d21aa200c438cd52b001afb10ea5668749a9258b12e576d5473eca3a1ec9b39e295d696f0aad0cbe49e28c7bf2fe3f1955258f2fd8981a36ac9bf2a18e116f33a1562cc6b71c8d5d2b77cae3a88ba54b704d4b45935608571c96372a78ea26dacbe8c41ca911f2b8439758b292410acb3e68dea8ae576c21c179ad077715d9e87362c79d88cb0a6a20aa5d66c96017a518f31ab262ebe9354d53eace8d337366850c0a6a20aa58044cf60d6c3520713640f7c9f0e471ed1c8c78c272dbc708e7d9730a4966977b51986b58fa9192c7e4d2ba3d4694c3a60b0ae4c3409cfef54eb8997ae1fc35b7d90898bd7c2386d3be30d66f57a7119ac7482e771c97083d82d9082d114c189937a1ad1986b7c6b1ed3e7722625247433dfe5931edca240b261c8c783fa07133115b986b1366f545ba8358e19fa385f1b7367504ce190d7114de9557567470c65b207d3240c90826250375e722cd9ca1e20e73c4a1101b56e8e03e49b4642944b6696b1d7b4879ded1e65f9c622c58bc7650ad7987f8de52c21cfd37ab1c1be4fdc76f94d707556f5298990343674af50865b148b462265c21309b66940c7676d9328e8a3512180fb056393c2879bd7d55bd482a180fef5c79e8a352c727856a34a6812d9f2887f541521f92fb20622676511edb242b0864bf1db0b1a0c9368cf871704184a11d9d4283c754e6963406f4e7af3c7240eabe4fd7ff828184fac76e64d283ba7957d26852471a36fa4d28583589f133114c1b0fd7fa5fd82820d66eabfc38b582c90a07b37decb841e4824190e015448666940cc5c744967684e74be4618bf3965eab86bb37afd1995773620ca086b5aec3c4c9072ab7044f9bd88a68c70d070d6492392d1144c95773620ca086b5aec3c4c9072ab7044f9bd88a68c70d9b13e6f67ee4f13e1fe04b673b27e49e1488ca0e392433f6cd9037026f619911136) else (if i < 7 then 0x893fca1f517e56129b0c3aea8e27702d0383c948b26fe23a18f11b249db73a85116e6085cec5b23e08597da5141687c6fd075bb0d1cb0355868bea2e2353d19ba67be8e47aebd1fe95444a3dbde13424e85d768527a3da3469c9a0b96e5518642341c6e791d14d47e7d28f297a447bd6c0f79da1ba6138439e4f1b9e8b6bbe7e4e47e325825acc653427213308659b237c0c73871c3e65510f5af34e6323466163da9d4096b115b2bf0e014c392eed349d49159a1d1253c34cba8a52c233d5dfa509338292ee07689022637c9a75e9b4eb68f1b013c7eb1c60d131be5c3603eb253c53a80f63490d4db60345f8d90f13a9761a89d6020ad678d1abb45f39c537c679b270cb6554e31f531f1182f1b127ff48b652e8d120477797f83267da7ec3caa504b3011f1c699e5da4ea8cf27a53ba372548d194ad8ea421ecc53cf67217d638942270c43e63e240bfd737c67cc04eef290b577d638b6415ce71a24086022766e9bf264e1bd80a5d3f79ec12f779109d1b40e290c3bf7fed692a540ccc71ea7f42eb77d147bc60ba3d54ccc758a3f0e59f93463fa3ef05b25e170e876dcf796ae4053f7f7124dc168b957e0ac828136b68ac8a99b1be786afb7b04ac05054d0fa48e1aee24efed54a0943cacf932b64fda536b864d21605d5d3ea4084ba6c9c37695e209582e7348052bc57292d4cf99e41bc1ee9ce197503e065e048cd21317f2ad83240658a5b16b66ae6a4dc4aa255cb089ff276cc4c48e31559b1063cb3542685db5a77c3ac5d835b6816f8ea7ad14b8bc9282d027124a79c5543a210f05703e684a491a764ed42270c2e416b4d0b6094f084714ba210f2a10de04c168b90ae66c578273665e4529873eeb6c5d9bb3e295c251a70a90600a32f39b8806ea9bf5b019c6ef586b0fbf5ad986b9f053ed1f042cc06058d1f58e206939c12b90a05ccde822e6f11efaeb5786af0f578884443ce7712f8260f79c35d442a0ac90723b6fe249d95c996f1369c4643dd0952288a48310f2584390f16bc6565ea310e99e93cfd8c3d4186d81555c74ba82ef3b9364bebdd43784ff9e4e8cb92670d2e8cb18678c18de72041c30f381876dfa6e393dd44f2c66cc9f127dabf7d9be24a1424a694174ec2de3d22a54812393a44e116323e25cbd27c9184ea9887a2f832e73c372045c9b8febdd3e246cc80c8f9f8489073266b0c309337b2065108816bf3547cff83ae33feca41ce70cf1cdd2c5016a78c61a5d38779d4ad2d10ee2d5f90d4b3727c2fdd1ef9eea3fb6a148b1e1de0645187373f411dffb887c99df84897fae83993d81df60c51a990abe170d77078c43f8a4ecb83c979bce3dee491b25c74169671babf3c64083f69774bb8a7ad24632c5388703a66c17acb19611c1d9ad11f20c1c8c702648c6582969a1ec1a9af3ba66cf89152c661cd98393 else (if i < 8 then 0x7b470c399431caf7c5a038b5f626dc5d267f5ca0769c20e218c062ef2382c6176cec59387430f445e43e5605125989b700cae92e6f399a5d3787576bd39b0f5cb75d8b7bce3654ca5cfe933f9014844a64d9d4bd28c78b00829a89c844c182eb452c0242ad1b454f78d501072bb60b782dc2d0bbcc4a791ff41290e7bd24817429a8ba0cd388a9f98a3cd5b457045ec451f41532fcf4ca618feee181eb3053cb3a96bdd329067b7f0e2232a2e8334e22a7b6395db78b46bde82ca88480876c7b1a8083d58a85d72aa6fda1874310b782c855a314781c8ffda147481290e7b6d5db3f7d7be26a99a1763dfbdea5c7a85d0e371e28494468be89fb818791171457f78d25114ce810bd3e54434a11f395ec79f2fefedc9e5c5206b0dcd72a1c510eaf65447f8125552e3ffca086a26ecd07795d148c2690243180d7a406a8b274239e7686382de0fef18bbc0e0c21164a205d6544c4db828c3ebf3f4b44a181f7d562c9f2db01d422ff3f4cabcc6a582eaf1905d58b45d9514cb52eaf54cde90ba1ce65b2a267c47f7c5a3d8a0be4b43a1ed87f6bafb7128898836ff63564df6e251e8e499fc85e32e84a9374ca9edc0ff8a498100c95168a83fe5f9f214714c3ea8f1e220710af125eea5c4b47c8c15932641acf8bca0862a3d4102b6185b70e11478ed87b727c4e13db8a616ffaa8f52e0354d4281da70e3964df5f91828d74a9b7b683c5187d7e7e96894303efaac593e5b603a845fe7e995798d4b05d5e32fa089db3751479ab6898a402b822d0c65b4650b2638ee1e85182405af6898ed8f1abb6146f6dbaa9b9961c4eff9f2bde1843aabd9963b602da391f3d11796a341ea6d7b8a3f2ba5ee1f650d6114727c78c0fbebbfd06875112bc641747ff4147e16f25af4ee6c2862ed0c778ca9fcc2e7ea148b9e0402de49489bc9ec9783d874a3c8ee24892a94c1021608b6dd67c0bff287d0d4d9386043576e4cdf416117b8909db6e70ff3845415431efe36dd8dc5b08b928c7b24d937b148e1ed30f2521877f1b9d85fedc91a18b6f064c56863cccd0598e18355ba6bc7f5a9520c2a0b52f6ce89b84f5a6ae95b8a02d81a364d585705a33c5daa108e084bae6adb10ef1dfc4212644a43ac689bdd21d50207c15827b6e754b122e4a2f9c3d288e863cfb7466e9bd784f8e032cf4a721410aa50f36dfa0a2f870c22e6a1b227e8c4c41173174087e6a693878cd23e7a8973274d0ff181598484ea1f473fee25d2f67c7ae9f919a8a09d05ecb5f7ea25a229e8e542473cd843f0e5b50a071b783de840d0d2bf10e094ee84a3407398292c3e30e7c41a94c14f0a52b23dd9584a4d8a0c52dd5c938737f39c5faffe91f6c351f042cb67fc19349954ab3d2989d52bd07c6262c4237e872a1b361f4440c98fea1fd19ba61dffeba473d07fd9cb75040abde3d7d else 0xb533bfac4b9df20f1dff51addf47947c623e8f20d345fe9478d44a447d2e5960bd78903bdb5a7de2749be29ada46e28e2491b4d1d66cd4091c50d3072b6c57c9775e5d5508dd1d64142b8933420ac5daa29e8bc8d157e2345ac5fb6ff86a9b89225c961bdc79478bf125df5ee88586c15d278e5c0aa9080187ab1c38d73865ca17d9e3d86691be934c25c7c2bdb3c9364c116dbdcbf5e11b256dcdd94baa686febdd6a03aed1a39ec67a88f5dc4ae3c57b925df51c7d1e39b1405ac5b49e30e67a1004715c8ffc193295b923a18f7ef98205ddf98a3fa0a5437e87f9ba67de1cef78a37e65b607ca390b703ee59e39b1434b3bd493afc3c7eb352c6ccbd64a792edc7ee520d51e6081b230c15cd9e921a8ae5f230c37e8621ea7f6839dad2fce203416d1c8611f3febad8babdfbe8d466b7bf1d8ebeba449045c9863c9dc728eb5b6f441b27237d0c9b511e6a54f3a6aa3aaf8a41148ab2e83afae821d4a71597464ae7e9da79e1d237e477ee913b85b24a365e893b2a1a876f9b829a0b04514238c75a77056875e88d1ffa0e183701c969e489222521314c64b18c72199691bcff60c99f1229d4927c7ba9a30f2518f29757ff41143ef8712858705cc5944dc079f854833e38ca7a2a5c3664d4a4ea5502962f261971a9d2f6088d8f8dbd0292ef21d8fa41d22e770230f8a5434a5a03293fb064dc4d13707af2ee2e59395089c33fb13ad6ff0c88f93e380562e4f0b7b3524954be27a9b124ae89d2d88c6de982ec76851222d038d38e3c9463c0d908c326515ee08d9d58b69e7511e277c4f174a150c58854d0fb046e342a876ccba24737e314e2b7f947e69071925cf653d3be0461974c4e8745cb2e811628c5d8b256e27f5d37e0848e845a2a0d4bd8eb17223cbb91865c095fd9138c11b81c62e74eb2e815c9c0095bf9a952f14e02fb338e49f556dc91f217762cdce533a683a31fc8d9cf7244b0e13b2186e9d6685234c76fed4efa2490189efe328e062c9b4d55ecce3b4c6352ffdff7c8465acb0760bc78887c7632c892c6de87be9c579064c44e0a703d16de206c8c648b40e05328d498e3be7434dde3adb570d8f9381c9bd1224b4e284e129773e32f089bb7f60a475e3b8bb1641a95b0fa5ec758b911fd74df82123a5dc22d15cd5bd08f90876290e3fb217a3aa24135344fe0f2127011f251a21ee1a091c7268adfd88723e45b115358d9a122a8acbc8c757f89c5d9f530a394d485710f0149c01ef56829c76feff487ba1a0a5c786fc9723d49a9f173fef59f211c733d27ee5d8b79fddaa80ad5de2c5db0c3aaa439c962dfca458f397ff2425bcfcbb1aba507b45d7281cca18efea0c61313aa3f5d9d8ba4566e9b8520f7222e79b0822a3f863e6c2f1463cca8822ae912ad18739511caedb2b01303102ba405e4f6cec08a7966cb2a27f30)))) else (if i < 13 then (if i < 11 then (if i < 10 then 0xde333313091e736284d89134eb69970079cc108eabec019198eec06affaf088aa433e66c9c30cd6ce37e83f62c42eb63c9e5112fdffbebdc42c0d6c52de8e47c8750c37bfe42a8da5366985c821d350f486fb0bb1c5a0b23240021dc9ad34b2d7063a13d17aa3cb4f1d067e552baee2e7a0f80bfec2ec3e27bfec7168f2963a17c842c6c8593c61b4fd89581dc16749f2c848e09171ab0a3353876cdee58b9c32ea27a3aa45f20414f11f133ef0bb49f245f0369006a23d4370b309e30a4f3f771c14962246ade88521cdeca1f1bbc6fcac85f29543a84148471b20745281303e0ac75fa15453d093503ba4a45ec68e088bb1bc46929a9d044c1849510ba0ec3172c4463d8222d49400a3b6ec5d849de08cdb8851c7092a692351190f51121e0dd5371910eaa68b97105621cfa8935a64674684e2fdb5166a13c29065987c0096e7d067e57e70db18449da12321e4fdc2720004ae44a80dfa0e8cf86d6dafca58ec3a53a6c18550ebf2d08b3f6efecd0154ba196d5395e7993d8f62442731d5b93576d8ce24152650448791f10c2900098a84e347274a73902169ebb9961b2925bfba7b9f46d28640c9df43f46504a109b3d3becc7468c7a88a1901017fa886032e22053de44a5593390a7161e92ba60a21e6eaa93ea1b48028bda16bf246f09dc5fb7237f10e467fd7487cefb77032261c77276cf116c6036aba3344778ebd4432c18e6a67d8a4193c0a79bba7aa4cff9ef2c1ff66b3c8e21d9fe8afc0981d10e07c1580b342617f0c8528bf18e7d52c9615a6449021c68e964faa9ac6df14b468e78a5d5317918e4881020b89f530a3948ca13c10f01480093bcde3b83b6c26d019e2ec2382b1b215c0edc3f1d40264b45794dc832575b66cc138c52ba6e41686f2c32c4cc502fa08d8333b7a0b5751737887c547becd836fdfb063da76941f4db2528310345b7be0f4f4e6aeac3a61ce1fb9a93773e0d2165e031c00f2ac8758c0487c751da53148cf77924319b21d60036038fd99a0b2ef98246b2015343e097c3c48b9f201d10c32988ed25ee83751875147a6a4de8218f8a97a3fd2ad250ba5bcf2af19143581d506dcb4c10216817cc102b9125d02d0db316a8da1ce180d1863ace786ea966021fb0b23e4398df8a80c931d468ecbe4840b5f99a39fc4d533032625447c8190c25c6628e5627955449d9f2dce3afe4bb8a111f1421147a852f734d8457bbb564c765cc77e1ac25b601ab1edd22e5962ccf990030d27cc5f3e24ecfb7904fe3a112c2287119054c4f4acd4b68cd537424a61b466c9b57e8e544c7468c79a2ac5d32986fe7a35469b2db0315c764b42e26f173de4f74297b91a7a08e876d81831c1754dfd9cb0e783c2394186287cf91f9901338827774d5262d55a7728ce991b22c5d3881c71e0569a93ed7545ff9b15537b98a83d74d else 0x23e68fb9fa0d1bb1fa18eab3f951c9ffd0437e128ed5792639fe3fbaa6bd97c440c98408e7fca6742a97d5831d44dc497478effa4575cef9181f4b8d17faf5eb3b0309d44f62e9bf15a5462d6830e5a7da3996c58526434a38f08f7e0eab462d7172c8c23216a8c22517c65b7f8ae0c580032f69ff818eb8ac628d92726e6534b9c18e12225097790509683a317e94ec824f618be32ee5fb046a98d9221271d68b7f74e0c4a7631994ab9eda64821f71a7a6c4b4c659336be5f2533439b31cafe775e82190c86176ca3be0a010b3413af64fe2b1e055191f3664f196280b5d471f44e26061db17572cdfd66fb93f678e3086d3cf0f5cb90d63bc493c2e1473565a8b3fa08143e7e12a4683f1103262f920b61cccef04d4b0eda5afbe0794926eb99ba59dea6c482c503c728ebf319bedfbb71d6c9b24b4e3bb5c18e72e4e21e360014ec25df0a416d68b30e63e66a8ed4234cd4ce861b9ad0ca49110fb290be48bab1666311c7cae30fa2a113866b62e7979c54570b48bb5bd4283ced08b882b6f692637abf17336c5cf2f6b60941c306237fff95c8f4ce1ec1492d0160c96ad073e2475c5143ab8c3e88dcdb91e0a7d9083d92d6b63ad497681c8b929f411fb8c3e9d0b5be5e2e45cba1d4243d1748a9dd4a26f743dc12b7b1bf0b482e928d35b3ee2bcbca575a699c968275766e66dd991b232c7c819432da439819f0e39dedcd51028ec7cffb89819310c2ba4a8dad58a334b78553ca225fbff7d7b88581ad8a5bd1c8f90ea186f7e6a1b154e5547436865c35197a26e76100031c214417717ecc92ca512f3a9ee4d33698a1385a7d7eb934951914ca8024a9fe8f3493f8ea1376614e01d08e33c6c8a5026a8700a05717632f71c92f4a8df09ba9d4563642385b17e2946381d30e07d288f730a04cd7827e549f58c92422f832f4b025065c53c224002709c9e745049d3f1dc1a97bf4300ffcea247009447a57502314e3754cbf4ee849e551858db9a3433398e6be6de4f083de774452e18b1b70cff12f20a42536a29f21899aa9e5724bd79938658a14b54a86d86a5fc80396da16b864c5e7fc0c75cec3866e18f2d9f642ce8a9b121944c8cb81419d2a1394850d8729fa71670de73a28800368598ef2763091b27893d6d0ca887233745c39ab7f43a0d1f45b868876ab5dc547999c87233744f4e61ff127ad87a9bdf09af018e70f8b093d8b390d6dc028f3caa2d47548dce77797712366515c8cc0babac0478803b6e23d34f61d3fa302adeefa4de0c9a00d33698ab66bbc25b5c1860274c4ad6424574a0d1461d477cbd216b3189472d5a4b8d5090c0296f58a175f9d4f14741b7287997538732ebb88c39f176c78e4d8cdcfb28ef72c0437a4d0063f641b479b091de5d6956ee52d59a9c71f147863450a2e47228b1757e639e0f13450e1faa48a3) else (if i < 12 then 0x83f54e4f1cd058b55f8c30ec93564a490b7d2d97a17753180d4df8fc8b6e1ce1932ef2a450391107c4b2618f4c1a62e7d514f3d1f2e4b5429438e8d2b55a84f078efcd543efbffd0433a0810b3f8aff717d040a19ab57f0a438d36b74b4fd029d2f6088f0f60905251f1137011865c38d49d8b6cc80a48b40e4cec66f9a969fa913940a4a84162de8a674f3a85b3221fc5264e81794efffc1492d35331f1187c047ee7e3559eb64fdbed2effe50f8f1b992f61642dfeb9be296aeb0691de6cd21cac0437e2a00a067c38e77b735440a3b1f3fee26064c430ae92a34971aa0a3ac2de17679fb231ee2ffd59431cdb09c743da54d90cb16f97a51d632ac382ee55f6e45116911f13a3b4ad0e9b147523eba287ec83694816d330b0d418e7c154d4a9170d34c5d55b9bee70c9b122717cdd6b40f7d27cfc7e46862c3872896c405ad22571cf5605757e04c158d905a07c529f108e314a7acd3ea784cc91fb8649f8eb3ff068d5f1265248c39f5d10eb81581f5766842b827f5e5891818a3022120e608145248a13aecf74ec50c917f27d448e4858ea47c369d3b436e44eb9f26f762c47c25ef762ce7c9ace287e0cffdefa409659c8321576cc64e193fe98c09d0520990a593397b9b7e9422ee0a4b18a5275210e5d4251a0b0810b65840ae66f11de410cbd151a7a12960cd4f4242db49e20b051a432e692da3cdb5265cd459dce1cc09d924aa0c48d4a6e25e4506dcad975dc63a1b447fd8a0f242a18b295ff287dfb7f7c994a6b3e3086d9be277db923a91f552016db8f3caa3aa46e73bbcbb891b328ae46605d5d6023c401db711e9a7b0e9fd18156f77d26f064d00699b4c55b35de12dae0c3013a6256b2122ba43aa11f7ccbc3cbd216b3189470c571cb156ad25c6a80bafcc0296fa9e28cf9b0147e0e3717c468d1238a15f54e1d9fb8c24001b52782b23224d07c173c8fcc7c4c6a34ca40b48a5136693cc2e062880036e9b15b923e0c4a82d8b9103a6e5070cc4ed7e5f0db4571534e4f6a2ec3a518ffe451d8ed365999b14a15e288af54357cf0813f5e2340e8d1292461c69b970bb238a18e186426f3898a81dd893dc982f07a84e22cb19611775929e6269b8a39eee520c964b64618754850cc84120811465a2b36631d5bee6253d95ec6e994834d76baa6ec1dcd1dbabe6384563654c6854097b5fa5dc6882712609446bb1461121962d59d8069a836000f137e57148c9b24c7c453a9a82e5817b18a19715c43b1995aff33e8924065cfab2875f51b5eb9feab9926332913ac31ad15acaa983986c9987c173fccfa2470c7c4c00803546d08d9ce5505b8efa7dd9e87ce8a1eec7c432dd8b918a71b4e2f514566fc2d987791837d92c392c74cd7ead1d3e8d4b1405acdd46119230891f79368acf9ae576cd7e421d26da16315a1d80115c8c87303 else 0xcf7432e96250f0dcb2329a8be3991227bc1da4d22e0940561f39945f0489e7d46821a924d78878a2e0a296c7cfeead1ffc94478c662891387c52f5e5c468be2589c1d82f10e3c5658cb38e0ef505cb0bf48bf749a630597f194707dc233ec1930d37a24b443ba723e46a45da9dc75b68dddc3456dc1bb7a232c7197610ce7520f9064d437cb2698c31fe0244a433d22887a6a0945fe2723e450843087c9d238f70d068d5535334dd3fe78b0df9a04b21735fbc10f534f085b363a448a8f77c495fd3b90a21ce38df52f86fcd025bbed0dd887a9a6b43e9b1d2223d41be2432e9ddc3410e71c1da970664dc0295900eb38a00c60c4903f1747594f43f844a48c410a8100a47c5c95900a700762de5903306c89dc71a4327a400ca79a91723349195900cb90f4dc9d481ce3a15024b41c9a98927145c8f10063ac478134ae7755f8292ee4c424ce0c8c324906a43322b6ebee918c5633890cec1a472810e87abb21592dc5a76ba29b3b5f20f3fba48eba3374d37c9048ee73c4a15bdb67a7c09e8ca484f052e244e2b869a62eb460553387f95554db700a3cf3e8417640f53db91598057163cdae0c743b1d0c7a491e72d0da248f1ccdb392a9a5cce0769f73831d4cda62a60d5ba6224519d882f0414f044984ea9b5483754c4497e1aa6333f92afa23ade880b0388e849829e00ad6d2e9b230c0f501887d30e23cb665f92a2c7b4c983812be84e808772bc1352c1575ced3095d10313660a78e3654de9463c84d7a726bb3503ae0a149eba2bdc5b101c33eea32986571c7bd26c5dc5e43631fc117fa9d844d43d0798e863d0ec2ec8f7e0555184369f108a15c1ea38b1e7edc8f89359c698a41814552f8709d053bd608c9b457b3c4e038638d54344e7485750a11683c6548baee0dd8f31c0a7b5150311c50ea96a23d42600d9e62f25c59945bd3a1b4c228f366731de22e5984bdb08bf41197c5ded5030b37fe2e8494c37fa88651154bfbbb431cb3a0c2769845066542b237fa0e502d29680d930cbb454b806c851a176a5ffbf60c9b8989681cf2cbae8c184fc8c19a7714244a5b09206c821d26e0cf9483641a69e68a83680c28415b8f502a9c8fc446cb881f03a09df19ee561348598a0a8554dd654472bb6606b80452ac7998a290b5d5cd0ccc4c255e845613b2edef19950ee4c4db81149bc1e626dc6662426117c9ba6caf6018c1ee0e10c68f7a1630bb67b961d430e39fbb8886c5683c5fd918f7c24494b96423271131067dee42260c12844ccf640cb2f65e4bb8354ce4b4148274ae43d80b09000390eb066e7cc9afc9f1c59f6038b956a561f1199be12481153605feb0061273332dc8986d31758b955b102214c432b8eeba548251548a55d314ea4df03ac04f9c8759375939bf223200e43ac6031d6628cd6bf21da490cb79310bb2f40c9475)) else (if i < 15 then (if i < 14 then 0x9ecdc1f85f32617c1f9f7f1048e78a28bf952cdc4ab285a5168770ee52482d88de16041a21de53d9975e0ff83cb64b70ee65fe056a995c15ed3502d20af0b02599056caf12f02b445aab4b4b3707e5a43b81b07e64c54eaa033cb8d990563655695588c97e05f953f0e404c1c38e05724a51b2cba4a934232c158bb37617c2faad2d2cde5485f9526560bca72d217c6c96b3267dd6994750c1dd16969e16040560fcb3d6500605c1e867aceee43280d82b59494991680b52b286525247e17817497f02b75594b3ced25205c32bb9e63d409e0b3b99da4a5fea00d0cfb241e8852ce00c4281707a19f85e10840ce1940689510a59c4292902e19433887baa90f15800c43e294c528ca543cbfe56d650b40e07a19c1e80d006214018cd48621c01b29af3f02870c4c1307aa7e52825312095dc9710cb2dc42bb901b0541ef316f705412b044380f79ac10986ae0cb3b9e10554e1045039d7f2596c4370bc438250073b714f02b410a2540683d0ce0344a83d323c20b9383cb601769357e129aca52c4f87f35755c0ae465d043ca543692e1782535f59494c2f7fa892e769292ce4a44280d07a19c0699101b8bc9488704a254c4a0250a581283d2ce05c2783d31e96eb380d3761945da5bf87f35f02873434565680b51042d80ca32c0bb49be0cb7c52410b7459c0b9690ca63d2d8cb196194b4be297082473c8216c00d10b18d92fc3fe21c0b88531b18ccb583df02b0afbe294286e0514be056eab183d01a13c1e98f19fcae904818d76fc208dd37102957082473c21ca682537621c5d8cf4b6194c7892ca16907a05c2783d31e96c068850f603555dd33ffc4f044504296902eaaee99ff1966eef88cb06a6b40688509e03555dd33fe21c6782510e1ee47b25f824b28f0c35a2d085d87731f04c1ea830ee96c1e80d0f60f647cdb07a0943d87735a0d4e486331f04cb487707a18cc684f31e034658879232ca0b7e084b0f878fc3f9a04a2eeb29bb49632d042dd1691972465940c621c67a085b021c068b72ce034b483d31e96c12a5b07ab2c1298f0ee32eb18dd2eb965c0a831c17c108bf0be5d4658cb02f744baa1d410b740a65f80349fa92f407a21cc6b814c44fc74e03131943e0e18e05148cb832d58dc0a831c32c4382d04a5dcbae0dad22d76a194496503b87d35aa0c4783d0ee1dc9f87b70298b83d5b32cbb58261dc3198b76aed44382d04a5dcba83d45a0f4069896048701284774e0b443e03014cbf00b85fc1b5a296214d04a86c4382d1bbf3d7340ef9ae9f88db93c9db04704b4d51b82d5f2201288fbce549f432cb8e92a81a44f07d65543bfaade756510b99e434a190e05645d25a0b2e3ca93e98a4709651f78097321973b3123f7498df5652a3ce1899fa9d2cabf4177174482592baea818aea2b5fa457ff9e10b7a910426803fe42 else 0x8338a7025e04f32e4ff2c85f84646c0f8eb5026ec1180f77a4fc749c11820b42782d32f1749ff40ad519745b836b4b749b94921d207d6e93fc1b842696e969bb680cda8eb22a6afaeb2e83ac34cab01e46cb4addc6b042d2e8969610b75037b01143e45b08c0784f5632ac8d937b326f75ab4d0c0dc1b5a1d2e41218e77a09681692d32ad018015ba0b4169dd08ee845cc21cc3d02b75f871d465f914610e59ec356cb324fce0e1d8213462c9ff0824276a355dac592ee5d45c829256abc9598b1f662614dd014cbf0dbe0dad025881a4e294f24a3142f80fc6b7785ac079a702e01d497a00d2566e1cec0450f86b84705a6260e8b9c6b042d04bbbb04a24d842dd05f83a17e44cb118121c3122e7658b902ec216c41f8a203cd38972d714789e048a19924a53c078c50be29dd082d0162e4238b90025afa81240612e037a0979292f400f7642382d08e0b45cecb02e17c2f80f18a6649294fa97022284ac0f83f245602c9b90512e094dee8498693402850c80c6abbbd1087807f5023804ae841680b17211c6bb7b45a0958121c2564ac05b084ea9ba092e89580f26e8add08b903e02c5380b01e69c0696b6109d530258857403801256c216c12b01a1be0fdf725a0e44b8cb2f214452e251a01333632da4df020807196d26f86dd92fc0220f54abd07d8d74b707443dd703a0a5009bbc1a1a69e0a6bda012d383435894690742880bfc3208306cdb8d70831460c897ac632c0e9bb05221c098d709e044438fb03ad3cb4cefc1a1a0ca0f43b80b1aa0e427f0bc0908d3c6a8652d20441e82907ad3cb481107ad3c278fb07a0441e80b1aa0e7a81240625a724b48410ee18c0d8fb01613cc68fb0820f4b48fb07ad3c0880524b581dc02a3173e015502571de80aa03292924b58496b04a8cb46265c0283fd9219cff997e97c0af01fc172c35819cffa632862a692d6196865b2de5f437acf23887006496b03bee9473df02b552a44af4be05786543b83f73e8816173107e6543b8a982f076084d39f0ee0fc5499524b59acf23887006496b01e995323acc1e895d54043961ac00791f59b815063a54e8b4269357e525ac3566ac1efc0a352c0ee2cd35821301092915232e5483d3220ec1e89507e0355780d31a6d431bb595224b29bf129ecbb5e43bd3773ff02b55b56e65b6ac5cb4a50ef18c3dca701a0fc3bc63e104859265b40343d80dcb6637e0561196865b2f995f8720260cb0c67845be9196503bc639525df2e80da6b04260cbd232ca3b536a18ddabb50ee0941a98b196234028cb4626141687722bf02b5401416cb782bc4c14376cdc0285f0beab427b3700a47c028cb23ee7d1885f0beab4b4b3700a5a48f8052d29cdd782d07e2a4c699705a98d94d63286e0514b2d99706581682de260a04fe16046560b59482d1b271dd02571c17c2faad0) else (if i < 16 then 0x834346ece0dc30466340d8110023a7a59c5027f43050c698f4061a46597902607ccdf0bc21206340d81101e3a75681f2925ab4d0d990465176ac90f388446187481101ea740884f77a707da81b0ef38fa8104262d366400f502084c1dc0dd99393094e0969cc604411877036044008e912a09624ef07eabebd80319a90c198b9a73482200192b1f72a4bbbd5865d588a907e00fe38b95108c958ba1017c40a5435c5c83f006abc7d83d09e0f4dbf042587caec7d8bbe084b0f87d9bb0cbda4e67882e4bafd8431a7a7336f59cdb98f27306cb48fb64bf01ea957a7e02287c5bd86d27302381d9b60a4438fb19e63c7d84f07b5fecc83d37ba1f736c6b81f12f20c68abf2e60040396de161002e03403f0b0800d00215cb8bfa2ab40496519cb905b4349b1210cb7882d4a9b89468afc3480f00e05d5fc2f2e601f858400b801c523c513445234a289a204703ab34b9e251a304438c212ba60ca03fe097900d12ecabf055ce3afa24c5d8250ae25c0680715603400857e278222802c5581701e5b6288971571440796d01a01c5580d0025b40680b57e0940f85701a02c5580d01e5b789e088a00f4065ac0d8ab02e29c05abf04a07c2b80d12e2ac068012da24b28afe7185700e21c4381d02fb2c23d71a417a00e2ac068012da1a45fb88448639453638946803ce483d03e02c1f90d107a00403905e161001a1a7858408d80f0378a478034058ab01a03cb680d00280cb581b1560349cb913bc5b9717f524b41eac3224a4dfbd59766a5d4084d5aedc20d6b00e47d7e97533716d8221c0bec212b9ea175621759620b5d0847d9b19685d5a1c678044713053d0e2b1cbec80aa25882dfa04901b8982864cb582732617c628d32bba8ea81686f96211f898298d6ef020bbb00e3aeede65e81584cad589c14c68b500b07777126b4145dbb0712e1076ad20f1430a2304ae8c538b0a6e8104d5c59173034d59058537465707e14dd1838b9776b767080752356516eb07072b744b9050a24fe55add0823a4d5c59173034d59051ae4adddc0d6f6c216e895ecb60e8110e42997a12b787fb01c90581baa800b83e01eedd6d04b4348e048a66116e6dc1c8eb2ea6cc7584151088c317543a104759b727287610e8929ed1352d836b465ac1eba3f065940525dc14c190c66d428841c59941b3ba6df1ae04bc0839860cc5116e14474ecb243ca214e13f0835ac7d98b1f706d57e619c33bd6ebb5272b746aadd76a62c31829cc20a5daa67316b756e83536a3ecbbdf9d9a50f14a193ea32fcc3b04268c9c9736634c4c57070c76a1dc0d93f3263a5df82731a034c9aafc53812f02f9ab1d6084e2a1d383836b49cd0ee6364bf34894a8d0ab152a0a5698b666cba8ebb832119bbc1b5ab8315091b11690be5a706d6b2c9970d26649f82d32e30407c2360ea0514ab19b5 else (if i < 17 then 0x2aa1154b6492ba0f2d84c1c487526815e01d2ea6dd57e89021752ea0cd57d1594e5d7e3bb52ea97d40a6224681936937c02eafe3282997e00d157b358cf0088d13842104baad01e2afe111c7902354c4a4558e9022c216a1290d2a211386322a11390632c9d700712a1a4f0b7b57ea26890347b93071842d4d924ac08d7d51089c355540225c4a869e824bafc3225603c058b9156046a1cb61c11d24ac95aad007b2eebecf272f0767801ea357e4513bbebe2881f6a23cd55a0dc5fd3d2ca351abf19cb901a48f9b31a69e4b280ffa3a02f3a8d5f84e5e08d501ff47ff3a88f09cf83080d5003b3c9cbc1d9e007a88f012c8996205712b9243409714a6cd7838a50c9f51abf08fa311d64a4028212e6e2112ade66ca281300249c00b3940a3f656b29672e4165160810b6f80a6d14c1e5b02f80f2ca66460a797ab034d6f1fae211202203c74823002ce5028fd95aca49380f2ca66460a7923e17c60c4933253c2f80fd04878c2bcd1fa8743538c119bf23e17c9299901e08c00b3940a3f656b29c3adb4ce656a05002ca47eb2940a045949c128a005eac05a03c6094f892714b98016520b7c791028fde0f842622d1d2517c416a01101ef5601f05a314ae9c524a17ccc8c1023c1e5b0e080f0460042f811e844e2f1048e78a2f40ad509504b127783f55eca4b681325605c0180dbb204e0a85701a4a48f9bfbaa4a6ec91f610b5009aa185e25594e291e5d902e04c9492b01acabf3648113774678044465a260a07720e1989468cdd8121c74f5b40394b1063a88465f0f404c12e1941cddd25a1dc1c80b10e0fc8968770cbd0eaca665dab172ce057230250a3bd01540cb07e402cd6acb19621c28bb7ad6104658070a2a26880bd418cbad61067083dbba433212e0f7d01128ef814380f7329ab572dacd4ea904ea3900f430cf4043980512d9c908202c1e83f2fc32787fb01c8870164b41f929d07202c4383f225a21c1c80b10e0fc896bc3fd98b38adb80514423212e01e70865bba4b41e87707202fe09298625a0f4788770faa0c4783d9dedc5fd14b409cb902dc65b9f1ba04ccd8cb842967309c75a63670686abf9391f6636b6c31be34d8c6774e3ad31b2044289b3082da2b83860d32ca3ed042dd0b7cb23ec089bb410b612da0104a6eefc943ea32fc327b3714a7394641b118e64c69e291a0bf01a2dc4380dc9356d6291a0054624a4028211d621ccbab11520fc01851082594cc8c14f3f1fb48bd0639b117e58c20e291a76917a00b072b6c1492d0ef0c6f93bc03ce124f0974684f026ef43bdc3d1a6ec09bbd023755b027e4b84a1de129c109f98c088230ee06c0880f1d208c3b81b022004749271965e40980f33608c3b81b02203c7494b40bca1d0d4e379a08c65dc18e7ccd8130ee1dc0d81300266d4ee0d0d5c1846c46efdae1d6da77b else 0x12a454ab195265c2fbd582a55883f32e17eb4a732db05cca83fad3d74759ab04217c02a732daacc92d6005672e4095650a4cbf012d06e29e8199752720cd4429ca)))))
def rankMode12 (i mode : Nat) : Nat × Nat := let v := packedAt rankHeader12 ((2*i+mode)*24) 24; (v &&& 63,v >>> 6)
def rankHeader13 (i : Nat) : Nat := 0xcc3a188a66f72859a9eacea149c6681a7cc298000011a97a1a283f51978820e1365aa483155900000b366d574625d1e455a07b260e7e6190992e2984c86483278c359000001b28020e800019
def rankPayload13 (i : Nat) : Nat := 0x1b4401bbf00a32c43e675069260883b17e1f4788bf18e6c4f898719e3340188704215c658d115e2ecbc8d312609c4682b462017d90432b3f6a46d188eb43ba4912067ec1029b450056c1021626eaec2d8a543b92c758055026f7444a48c6aa8471269e4b19b3066074c3acdd10eb81381f3e20ac8fc434768bbf00a0b46590b1333fb046a98e3c116a12b9e17e16d985b094467a31176b6c688e1c05a32cfb82718e58c02a5f15e2fc468211b25e4159bbbe20cc019779ee0152fe4b4863341086f1e33def886ffc450c5eff0c8668054be0848d8352ba314d397724a00ccc81f1d6a04990a596daa1366128d08695b75e84128d306a775248c715eb348599b3ee95cbc8a5026fa1932bf10e43328078b38d27ef369f9a2bf1ec1291f899853892e5ff924a6188f97177e00c4382704aafd7d88d0ae344579a1b865e6a68a51762fcb19f718eb6c6686ff24948311f2eff871eca2194397b2be01453ab397fe9aa0250062e4058291d60141c97725a46c1aa5f5028c41097b38a4946295d34e33437a1d4be3c72580548a8546a5810e8929e8a22e65fa9f0de00c018b90160a4758050725dc9691b06a97d40a310425ece292518a574d38cd0de6ec239b305e2bcd89f154e2ecc38a525a3656d82703bc2a41865ad32c695cdc9792ea33ff0e01ab4d91e1ec65829261122464f4098d93ba0a46e87b1960e569e8d91e0d496e8172c66c5f96319ff6c84b68a14a7c533e472ca6c4192cce0d524ed3f34efcfc70d9c14d05982e2ce03d82591fb446583511a58cf882736261c52acd1a26b45f8cb60d0bcafb10e1ed2c8931c38094bb97b24629c9e829fbe32ff0e01a80317202c148eb00a0e4bb92d2360d52fa81462084bd9c524a314ae9a719a1bf49225f87048c5393d3763ac1a82991e00c5c80b0523ac028392ee4b48d8354bea05188212f6714928c52ba69c6686f0f64f45cea25e469c7892306bab49844b5227102914e3353386f0522e40592d91f17717925d5a1eccc94fd6732c00c1a9a70431241920729e751d5047367ba6a85741688d3d22bfd085b5faebcaf86f96258449c9750316dcb8d304eaec6897523e0af8c9b119666fef82110e6b5944e41982ed164eefe2cc5910e09c128cb2ea234bb8d115e0d7d2845e4cd8212f62fcb19f718eb6cb0e06f
def rankMode13 (i mode : Nat) : Nat × Nat := let v := packedAt rankHeader13 ((2*i+mode)*19) 19; (v &&& 63,v >>> 6)
def rankHeader14 (i : Nat) : Nat := 0
def rankPayload14 (i : Nat) : Nat := 0
def rankMode14 (i mode : Nat) : Nat × Nat := let v := packedAt rankHeader14 ((2*i+mode)*2) 2; (v &&& 1,v >>> 1)
def rankModeData : Nat → Nat → Nat → Nat × Nat
  | 9 => rankMode9
  | 10 => rankMode10
  | 11 => rankMode11
  | 12 => rankMode12
  | 13 => rankMode13
  | 14 => rankMode14
  | _ => fun _ _ => (0,0)
def rankWords : Nat → Nat → Nat
  | 9 => rankPayload9
  | 10 => rankPayload10
  | 11 => rankPayload11
  | 12 => rankPayload12
  | 13 => rankPayload13
  | 14 => rankPayload14
  | _ => fun _ => 0
def rankCount : Nat → Nat
  | 9 => 2
  | 10 => 138
  | 11 => 970
  | 12 => 793
  | 13 => 16
  | 14 => 0
  | _ => 0

def testPacked : FrontierTest := fun T mono ws r k i =>
  let chunk := rankModeData k i (if mono then 0 else 1)
  FrontRanks.rankHuffCheck T mono ws r (fun kind => if kind == 4 then (10, fun j => packedAt rankDictionary (36*j) 36) else let f := rankFormat kind; (f.1, fun j => packedAt f.2 (17*j) 17))
    (packedAt (rankWords k)) chunk.1 chunk.2

theorem testPackedOK : frontierTestOK testPacked := by
  intro T mono ws r k i F agree mon group checked
  exact FrontRanks.rankHuffCheck_sound F agree mon group checked

namespace Margin
def easy (c : SignedContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,budget,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if (op==2 && budget==0) || decide (len>cap) then true else
    let d := (len==cap) || (remainder budget op==0)
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    !properB z.1 || ws.any (fun v => v.1==z.1)

def hint (b : Nat) : Nat × Nat :=
 if b &&& 1 == 0 then (5,b >>> 1)
 else if b &&& 3 == 1 then
  (match (b >>> 2) &&& 3 with | 0 => 6 | 1 => 1 | 2 => 2 | _ => 7,b >>> 4)
 else (8+((b >>> 2) &&& 15),b >>> 6)
def claim (h : Nat) (pools : List BoundPool) (links : SignedLinks) (k budget : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op :: rest
  if h == 1 then (links.1 budget (keySet ws)).any (sameWords ws)
  else if h == 2 then links.2.1 k ws
  else (pools[h-5]?).any (fun p => scalarPoolCut p k rest op)
def step (c : SignedContext) (op : Nat) (a b z : Decor) (ka kb : Bool) (bits : Nat) : Option Nat :=
 if easy c op a b z ka kb then some bits else
  let (cap,budget,_,ws,_,pools,links) := c
  let rest := (opKeep (op==2) ka kb a b ws).map Prod.fst
  let h := (hint bits).1
  if claim h pools links (cap-1) (remainder budget op) rest (movedChoice op a b)
   then some (hint bits).2 else none
def pair (ctx : SignedContext) (a b : Decor) (op bits : Nat) : Option Nat := do
 let go := step ctx op a b (movedDecor op a b)
 let x ← go false false bits
 let x ← go false true x
 let x ← go true false x
 go true true x
def pairs (ctx : SignedContext) (a : Decor) : List Decor → Nat → Option Nat
 | [], bits => some bits
 | b::bs, bits => do
   let x ← pair ctx a b 0 bits
   let x ← pair ctx a b 1 x
   pairs ctx a bs x
def allMoves (ctx : SignedContext) : List Decor → Nat → Option Nat
 | [], bits => some bits
 | a::bs, bits => do
   let go := step ctx 2 a a (movedDecor 2 a a)
   let x ← go false false bits
   let x ← go true true x
   let x ← pairs ctx a bs x
   allMoves ctx bs x
def node (g : SignedForest) (k i bits : Nat) :=
 prelim (targetOf g.base) (contextOf g.base k i) &&
   (if k=0 then true else (allMoves (stateSigned g k i) (contextOf g.base k i).2.2.1 bits).isSome)
theorem claim_ok {h ps ls k b r op} (H : claim h ps ls k b r op = true) :
    closeSigned ps ls k b r op = true := by
  simp only [closeSigned, Bool.or_eq_true]
  unfold claim at H
  split at H
  · exact Or.inl (Or.inl (Or.inr H))
  split at H
  · exact Or.inl (Or.inr H)
  · cases q : ps[h-5]? with
    | none => simp [q] at H
    | some p =>
      apply Or.inl (Or.inl (Or.inl _))
      exact List.any_eq_true.mpr ⟨p,List.mem_of_getElem? q,by simpa [q] using H⟩

theorem threeGuards {f g h s : Bool}
  (yes : (if f then true else if g then true else h) = true ∨ s=true) :
    (if f then true else if g then true else if h then true else s)=true := by
  cases f <;> cases g <;> cases h <;> simp_all

theorem step_ok {c op a b z ka kb x y} (H : step c op a b z ka kb x = some y) :
    evalSigned c op a b z ka kb = true := by
  rcases c with ⟨cap,bud,n,ws,cov,ps,ls⟩
  let rest := (opKeep (op==2) ka kb a b ws).map Prod.fst
  let tight := claim (hint x).1 ps ls (cap-1) (remainder bud op) rest (movedChoice op a b)
  change (if easy _ op a b z ka kb then some x else if tight then some _ else none) = some y at H
  have dis : easy (cap,bud,n,ws,cov,ps,ls) op a b z ka kb = true ∨ tight = true := by
    by_cases h : easy (cap,bud,n,ws,cov,ps,ls) op a b z ka kb = true
    · exact Or.inl h
    · right
      by_contra hn
      simp [h,hn] at H
  have forward : easy (cap,bud,n,ws,cov,ps,ls) op a b z ka kb = true ∨
      closeSigned ps ls (cap-1) (remainder bud op) rest (movedChoice op a b) = true :=
    dis.imp id claim_ok
  exact threeGuards forward

theorem bindSome {o : Option Nat} {f : Nat → Option Nat} {v} :
    (o >>= f) = some v ↔ ∃ z, o = some z ∧ f z = some v := Option.bind_eq_some_iff

theorem pair_ok {c a b d x y} (H : pair c a b (if d then 1 else 0) x = some y) :
    signedPair c a b d = true := by
  simp only [pair,bindSome] at H
  obtain ⟨j,h1,k,h2,l,h3,h4⟩ := H
  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨step_ok h1,step_ok h3⟩,
    step_ok h2⟩,step_ok h4⟩

theorem pairs_ok {c a bs x y} (H : pairs c a bs x = some y) :
    bs.all (fun b => signedPair c a b false && signedPair c a b true) = true := by
  induction bs generalizing x with
  | nil => rfl
  | cons b bs ih =>
    simp only [pairs, bindSome] at H
    obtain ⟨j,h1,k,h2,h3⟩ := H
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨pair_ok (d:=false) h1,pair_ok (d:=true) h2⟩,ih h3⟩

theorem all_ok {c ws x y} (H : allMoves c ws x = some y) : signedAll c ws = true := by
  induction ws generalizing x with
  | nil => rfl
  | cons a bs ih =>
    simp only [allMoves, bindSome] at H
    obtain ⟨j,h1,k,h2,l,h3,h4⟩ := H
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨step_ok h1,step_ok h2⟩,pairs_ok h3⟩,ih h4⟩

theorem node_ok {g k i bits} (H : node g k i bits = true) : nodeSignedVerified g k i = true := by
  unfold node at H
  unfold nodeSignedVerified
  obtain ⟨h1,h2⟩ := Bool.and_eq_true_iff.mp H
  apply Bool.and_eq_true_iff.mpr ⟨h1,?_⟩
  split <;> rename_i h
  · rfl
  · rw [if_neg h] at h2
    obtain ⟨x,hx⟩ := Option.isSome_iff_exists.mp h2
    exact all_ok hx
def bank12 (i : Nat) : Nat := (if i<893 then (if i<868 then (if i<855 then (if i<849 then (if i<846 then (if i<844 then 0x4f023bba1111c22279e0e8e88e238a9658d0e2cb0aa27b447155152caa27ab447155152caaa18603d060c300c1899ba1c9a82940c else (if i<845 then 0x681510003aea88000035d5115451110a2288000000000 else 0x681510003aea88000baa214300ebaa22a8a18000000000)) else (if i<847 then 0x18d5d0003a86ba04000888882200ea1ae8aa1088000000000 else (if i<848 then 0x681510051110000035d5114401aea88a22a8000000000 else 0x1a220002222200000d744411008888822088000000000))) else (if i<852 then (if i<850 then 0x20044400038220885044111740000208822088880c44113757411 else (if i<851 then 0xc01a86a19e2222222200286a1a962217bbbbba226eea86aa1a8e2228fba3844444441511d1111000a680 else 0x702a20035774400001a86a22e80544445114400000000)) else (if i<853 then 0x135553cf3c444444430c0c22a965a962218bdd34234551c751c44328fa1c444442221110c2030184d08d1a10 else (if i<854 then 0x55552cb2d4fdd5dd111111111551c751c7d111c00006187a2218606abbabbba22ba07ba222222220222200050 else 0x2c0aa1aa86188888888aeae87a23aa3a8ea188ae8e0000002802222222222a20155d5d5d11dd5d0a151d)))) else (if i<861 then (if i<858 then (if i<856 then 0x351c71111110d3dd1f444353cf51c4574000352cb51c45754b01111111104435dd5d11dd5d174440000 else (if i<857 then 0xaba2222223bbbbba23aaa597ba23ba580015471f7447754707088888a88222aa187aba23baa18a1888600140 else 0x71aba04712c406a187aa214000001abbbaa2ba005454445441440000)) else (if i<859 then 0x8001a007d1c00444440c03d0c3110c06eae8887ba0000008088888888881 else (if i<860 then 0x1a0000410111002222200310c744b0018863a2a38e0000008088888e8e881 else 0x40888004443d00000888fa2860111dd1745d000000000))) else (if i<864 then (if i<862 then 0x256546e8088a577655ad950c353e5a9d0c440444224b53a3a862a1e540948a92564b96a7643154a8f2996aa574350c41863ca430c44044420845545084 else (if i<863 then 0x256546e8088a577655ad950c396a7431153c0444224b52ba1862a0e540948a9525a95d950c5418e18e1e564b96aa764314a87291e4440444208545084 else 0x5400059a047510c344300001d4570d190da9000345054530151916a44a11d44f1ad190c99246400014140)) else (if i<866 then (if i<865 then 0x5400186000c15d1ca2838a89651491100001514c29222250800000ae9e51491e44a51240184e9624a889dd00001400 else 0x1715c568b65696594a251cba38e512865d0e430c3a2dd91f56fdd08caae49a7503c208f108440232511d6e46465455427842189743d2e430c39d9508a44328a29f926d504aa54) else (if i<867 then 0x1008000a8a8e2a38a8e38e000000044544545b9128a111110c4310c310606111152c54b155d351ca29443196ee9bbbba0d51d0c7774544544544f9128a111191d511 else 0x200a80010002ba2bba2ba68000111516c544a2c4a11110c43110c183106111151c5657151c9d29443196e8edd1d33749510c319dd1511513c544a2c4a1111919511))))) else (if i<880 then (if i<874 then (if i<871 then (if i<869 then 0xb7774516cb6ca4ca225128ce221a9431621c88622191158c440e4a0c42a1507435bad6e80ca4a2bc8c872a22ad48a828791e1d45120774a2511dd02894 else (if i<870 then 0x52b775bbba111088888888888888894d949e842a0b162c5e842050d72867ee888a8a8307ba22221a832c1861870e38e1c3e84238030638d08840a1965961c else 0x446657595008aa6186222dca888a888ecaee8ec8e8accac9e21c8cec800025471c18e1ca8cea8e0e3a2ba1c8eecae89dd1519511112c4646449519511028a02814)) else (if i<872 then 0x6b4f98d4a11116abe1dbb59774bbba19430d3873a1945858f2a2c11042084354f2cb61e764350a7432863ce861ca8452187aa2b44f4b8a252a04444a25102888894 else (if i<873 then 0xd41102222108dddd0474a506a19e08ee86140002941a8e5823baa1920208eeca862471c280000001340500 else 0x10080022a18ae8a86d800000022b8a88a8c894508e8888e38e3a3a2d34222dd0dba1a73a5152a3a38e8a862ba2a1c96091d19d2c54454444f9128a1111951911))) else (if i<877 then (if i<875 then 0x802a0000a800054315d4c5434c0c00008ce2a2f8a8c65062508e888e238e38e88ed68b4222dd2cdd2c9d2a547471d152c5757152db24324746764544544f1513ca0c4a1111951911 else (if i<876 then 0x2dddd145755ca1ca225128c622194328872218a88471157c440c72831508541d1ad6eb5ba68321ca29c8c87222ad48a828b91e2d41207774a2511dd35a2894 else 0x84000404453282a223a50764745472821c8cec801e0000a28a011ca0a87233b32091512822588c8c88548880a2800514)) else (if i<878 then 0x6b471e37ca111168b6ece5dd2eee8650c32873a194181972a0c110422208435470e5cec872a110fad9475ca5cec872148f3aa2b43f498a255204444a2510421112894 else (if i<879 then 0x35008888423777411d2941a867823ba184c0000a5011dd950c0e0351cb2847764324790a00000004d000a0 else 0x4021004301d15d29a000a888a65244a100000a9e25945d2a449111c544a4882248880030140500a05028a0)))) else (if i<886 then (if i<883 then (if i<881 then 0xa11108894a3c651c71c2222222211111111128b29f90a8546b5add0e840b2b94b6d4715115156a42186186222221b41861947a9e50e38542a0906a1744442251a5d0e94 else (if i<882 then 0x256564f900186004aeeae86800302564b99054e899511910a9112232202441222232b23cc84e933232a32005002814 else 0x151515c406e8002a20080d002a29888284740ca88e2385688911e544f1906889191e4b510c430d512464390c300005014)) else (if i<884 then 0x2947818f0444108222eeaaf20c2d0841104414a28ba50a38f20c2a9d15071cb29c8350a745452e4799506116ae8b74b9d9dd2861ca830aa745450e4390e743 else (if i<885 then 0xa51e06a58f04441082228e3c830870a96104411028a2a0e50bbb20c2a9d151776541a8452ba2add1f774b29c830a4711479d9d92861ca830aa4315039d9d90c3 else 0x14108882220e3afa22211110888884444444444a1d54a2b542a150a2c2cd508540ba9974bbba2a22a32969430ca183d0c44446529d0ca3ca3542a1502a4))) else (if i<889 then (if i<887 then 0xe1c54038062a2182038e006c545f284408d1d1d6844111078aae9922247464470c303124746430c0580000005440a888e8ae8ee81 else (if i<888 then 0x1504c0540001512c044a89612322471d048ceeca886061232187a180046464644400a015406a547448ceeececa88d else 0x2050a0050086030300000ac84c90c48f0e8d2744ee80349d04eeee94220b2a449191951102252a443a4471951111)) else (if i<891 then (if i<890 then 0x569738f58ca5ddd557a221151108442214b7f545ce8888a8b36187aa0e7444552187aa0e7444552186186526a9945c8541694a81c38e3b421cd6b4a147ca8541191e901c else 0x6a0982a80012bba0d95dd3437744a88848c88804ece9e2192a19609d9d91950e400e0050280a544448c888ca8c881) else (if i<892 then 0x200220141110a06221149dd0001108a4873a548888410444421110293bba4e888e800002001400014 else 0x2088000a111081088b404431116808c872004101a0088eeee8d1168108c8732d6ec8000354000200014)))))) else (if i<918 then (if i<905 then (if i<899 then (if i<896 then (if i<894 then 0x11044011110822221b4110c002227b41190c1c008020d04774dd1a2225b41190c91dadd900006a80040000 else (if i<895 then 0x6a038e001c04aee815b2a19e027665444048c88ca86580a9d9991900dd95d9195dd000a0012a220848c888c8c881 else 0x1aa0182ea0000007431104044311aa2202222235474c344319193574f06a8e8c8cee802c006a0280b54440a888888e23881)) else (if i<897 then 0x40202c0e0000600457151025011d1d1a091d12c54709824676454444f02502323222000c0501415d1d0d48eecec88d else (if i<898 then 0x13f545f0180004313545b05c86062074411d1d515c6ce81a8cee880000a8a6043104644546440238811c4474411 else 0x59f0d444444686bba23a0422222221b0d4b5c46745464071c000130000035dd11dd119d0680c350cf119d15190c13a180400014))) else (if i<902 then (if i<900 then 0x2232b86a0112cb1117c351115111d0d7745bd91d0d775ba5ca8eee8014505430d434c43919d9d28311c547911f6744a8638a886a2222788c8ca8952322200500014 else (if i<901 then 0x2422220d4a5165044214aeb5432da2ad1084088dd52b42e9491c386a1c53a2a68f32590d498aa74545d91e643061a8f154e8a8bb21c861ca80a411074a54 else 0x1b2cb14a51e50a2a31442b278642502be349ecab6522bab5bab2ad954a8cab77422b2a1950a8ca46444a18395072910d53b3b22181520e18e954aa54)) else (if i<903 then 0x12dca85c6592b89e5428d95dd57db2d28e1e43ae8e5194c44a3291911950c3061ccaa765430c43697655abbba3c8cee952a0792954a5520466544655232223232a32a1 else (if i<904 then 0x6e92a088ee8d272bbbadd4a861a9fa9d0f55a9d1d431c4404454213552a597aa9d90e547117ad4ae86a18618e290c32a543529515290111105421021114 else 0x4a2212aa9f2db2888a4ca4c220e0c1c111ed0782225dd956c875374444a5aca9790ea2ecec8888884542111111111112861ca83906a2ecec86221888ad29a19a90aa54)))) else (if i<911 then (if i<908 then (if i<906 then 0x425261861870e38e089bbbbbbbad28a818dd0f150f0618d01515165b4c31dba55cf4889350c71dbba596b9e92cb11150444444422111088888425061da094a844 else (if i<907 then 0x25453e55b52ca854695dd3fbb2d14f2cb15a2eecab74bbb2a225c464a219511288caa544a223a2232a38f21f43caea8c88f2a145aa648a94a52a4a861c9741ce8632a2a1ca83 else 0x13602a50545f1001045704a0a965c882a596000a14151c7912854751c1c1818821861830618650544f53c4415191244351169a2d3774ddddd51d)) else (if i<909 then 0xd0888835694d94110852ba1c350e21c42155c088d1f4a1c20e5375a1ab4553a2a2eecea435262a91c451e76674186a3c5218a81cec861ca80a4110b2a54 else (if i<910 then 0x9503062238e2072a222224aee8ec8e81d951ddd001800028a009592c47919d95d0912a2222232322091100280014 else 0x1427a9e12d65447d54a1151a5dd1d96b4a68d8a0c448a0872a95dd0f430692ca8a9729d2eca439289444457148865232220f250e5260952a54))) else (if i<914 then (if i<912 then 0x51509498e38e0c18618618226eeeeeb4a2a0e0cd0f150f0e38d0f0545498e186ddd2cb5cb16222beda6a386dd2ae7a4b911150444444422110888884250e0da0952844 else (if i<913 then 0x688d0081113c5444747747468a8e23c8ee8e00680014003443150e4776430060454444b11d1910a91100280014 else 0xd1604545700068880000000c574391057400e2ba9c883a121811513c44110a919100000)) else (if i<916 then (if i<915 then 0x204100006810440b41810443743084440dd0c30da04110ddddddd0810442044444444400000 else 0x26b2aaa26b9775bb2a1872a0f743dd1add692a79f2a3f74f0f4788810888408221111111d0a88865430e541eae861e9431088659668b05a821160e39a1cd0e043a838e) else (if i<917 then 0x14aaa6d75294f3d351e7b77775bbba1111108888894b2d3516a5ee88960c183061b420c0c35506187ba2221861836b75a16a81b74084a21084184443aa07550e3b7421c06386a6e84 else 0x52aa9b4d3288aa845bbbbad11d088888884444444a79f2a3c477444f060c18316841852cb951623ba22a5862dad1d685aa06d03871c71116844a3851c380c1886dd08301a9ba1c))))) else (if i<931 then (if i<924 then (if i<921 then (if i<919 then 0x2565556574d65654f3e54f3cf11044115430d5430cf0c4196585a82cdd374d1a69bbbbaba22dd6b5a222222211112d43a111950c3950c350c41865b5ba2a218e383821c1a3ea811d4 else (if i<920 then 0x52a69a36db2eeb5bbba1860c1861ee86d54dbbad1751e53cfdd0c3d1e221088888888844458bdd066e9610183683062861101c3870fa0c68e1070704422221888844444b08888e1 else 0x52a71976d72a6a2ca5965b5baa0618306186187a1830e1c3871c6860884222222221110888444422238444775addddddd6ee8444741830cdd0c1c210dba0f1e52c7818111116e8)) else (if i<922 then 0x13595553cf4d73d44444657765774474444444444444444654b2e54b2c44bd112c00000e38e3888fa223a8e0795dd95dd151dd115d07dd0c30c31110f4444350c0c31d430f43005400050 else (if i<923 then 0x25aa090c020a4b94a4794921816a53201294ccccca5202d2544a41909528 else 0x53c3599553e5465f955196d65390d539d5d9d9551916d432e4b550091e475959d5d990d523232baa8aa555))) else (if i<927 then (if i<925 then 0x127eab69af27ecefa6f812186186000127cececcc8888888cccccccc963b4b2d2323c8f23ccc8ea88699 else (if i<926 then 0x12dd010d5394c70e265b948725ca4b99511c9d24b990680544a49504cca439548ca4f9904c859 else 0x4872a7eaf21cab7ad8123e8fa0004873b3b332222222223278f9999192e4b92e521ca729ccc8ca88e1199)) else (if i<929 then (if i<928 then 0xb32bb29acca8caf32a3adac8f23a8f3b21cec8c8b6b3b3b2a0125c972b21a872919193d664555 else 0x487aadcb721d404424b52d43aa2203a824398e532012bc9532594e7643203e44a54a492b2) else (if i<930 then 0x4e86a7c9f211011011113aab882204ecc8a44024b1084333218a40385494a829212a90 else 0x2858d04d05a08451ad104222001042232487641c3200c48a088a102108)))) else (if i<937 then (if i<934 then (if i<932 then 0x50b03859a681a0e52070d00a08842292a4994ca407294c8a0a404952a4 else (if i<933 then 0x9995d94e4393c6570e5475664390e5b9d92e7527849725ccc8c8c8f3323c8f3333b21aea4253232332a else 0x26656434e4036c254032a2102204af2183994eceb52582e448f238791901e26576752)) else (if i<935 then 0x94e804402284291e4290049990853a0420cec8522909332048085 else (if i<936 then 0x243959959093c25413b3ad90b2c018e071232214ccca653ad486b202ca4645325 else 0x13a596da69c844044044521c8620089a1884216960783b23c8e291999991480c801505))) else (if i<940 then (if i<938 then 0x4ae3e61b77ca63ffadf69af5e873c888880111111119de4791e6640264398e439993c33c33d33b3b2fccc97a5e88b9 else (if i<939 then 0x911111190c757cf50c76e4b5e444444002222222259e9c9699d9d9d9999991e6641a8024a490e4391e66653b3a329 else 0x125e451b094c00444442022042c5885a7eb43238790c830610800d6e7432)) else (if i<942 then (if i<941 then 0x9d95917e4795d151e579959090e4396e4301a7c9f3325c8c8ccc8c8c967564390e4b323c8f29cccec9699 else 0x2532fb9cf396cb51cf56cfac799e7777646466f9100989e327802a731c9725cccccaf2becc8f23cbf332188621ea839) else (if i<943 then 0x4c8accac8e5a732a3ca896b213b3b3b294c01953e4f4c8721c873321961c966645767522b323c8f2dcccaf2299 else 0x42244217953e4f9149725808795d1c2400442322511486a1c88a76764249)))))))
def bank13 (i : Nat) : Nat := (if i<40 then (if i<28 then (if i<22 then (if i<19 then (if i<17 then 0x88955ad5697430444222b4baa18a9414a2945697543152aa955aa5d50c4aaa5550444208545084 else (if i<18 then 0x1402050c430300154554a50ca55d1d2974a5dd551551432955755545450c555d555551112944a515151511 else 0x88843ad1697431569754352852941569754355528b54baa1aaa9554111508408404554a50a504)) else (if i<20 then 0xa2a5c455aa3a210549a8ae894a2d4a141516a2ba255528a87515d12aa95544180c060c52850a50 else (if i<21 then 0xa5262eeab4568aa7a974a1a94454a215112a96a5d286aaa2aadd6aea8aee941a8e28a5294aa29442a222a2a2aa1 else 0xe78e13280c1a832a954a1a944a2a515116eaaa97577474a555286aaa2baa5058a52954a045554a2a222a2a2aa1))) else (if i<25 then (if i<23 then 0xa52e2eeab468aa9a975aa51153d4a25151152eb5430c432a96a5d6aaa8a86a50e2852954a2a9442a222a2a2a1 else (if i<24 then 0x88843ad16974b1569754b50445421055aa5d51d4710e2d2ea96aa251d4a34a514a50110d4183018314 else 0xa2a6f4543ae8fad054baea8fa510810549a8a8ea944422a3d7547d2a89454a2f4a1452940c180c0830)) else (if i<26 then 0x196183ca34baad6eaaab774a21528a88954aa5d5d51529554babaa2aaa5038a55294a045554a2a222a2a2aa1 else (if i<27 then 0x29478bbaad1a56eb74a22a510a88954b52e835d5152a8ea5d06baa2aaa5062855294a2a9442a222a2a2a1 else 0x22111684745454584775438a81687054545847755472888b508eeaa8e555062a0316830183021116942940c)))) else (if i<34 then (if i<31 then (if i<29 then 0x515ca3aa20c4228a6a2ba22835285144f515d12aa8a25a8ae89554aa50e250a14a6a9428528 else (if i<30 then 0x294984203144f5089444bbaa1d6a8e954b508e0d45754a23a844222a2a225060a85294a2875aa3babaa2ad else 0x1450c3d066b4554f4a19754a23a510a88954fd2865d555152a97a50daaaa2aaa50e5285294a69442a222a2a2a1)) else (if i<32 then 0x5551e7aa8350c36b75a2a8751c70f4384221022a8b52d43d28e22d541a86187a50c4a187ad1aa0b5a084d0810a822 else (if i<33 then 0x55550c30c444444557743d11d552cb50c4574b0002a8e3a8622baa3838888888a8811155dd5d11dd5d17454740802814 else 0x7aaa96596abbabbaaa2258a622aa38ea38faa2380000c30f4310d4301aaeeaeeea8ae81eeaa88a8a888a881a8a889400050))) else (if i<37 then (if i<35 then 0x51108eeb44744221ea5c477454b83062d03061ea4c477454a9864cf51623ba252c32965870e2d070e070e08b4110c060c1c else (if i<36 then 0x810a140ca145dd008050a286ba528000050a286ba52a8a50a286ba2a8aaa0100500142804a014280 else 0xaaa5aa838e5550c355061aaeeaab57754b15b0cb38aaabaaa350d7554a22042210422aaa6aa7d435d552a89555a1d77754aba225dd550a3d4a2942954150a8222054094)) else (if i<38 then 0x1aaa7aa9a5955747550e3aae86aa0d430d4f3631ca18abafaaa751d435528882210884108aad16babaaa55d116aaeaeaa6d4750d4aa25d5550a4d4a2942a94150a822210811514 else (if i<39 then 0xaa96aa08e55510d541862a27aa854454b0670ca78aa10ea222aa11d1a1d09a1d1545f5546a1a8aa9474aaa2baa9b50d454a3a555550a4d4a2954294d50a83a69ad14 else 0xd403555432d574b2c000001a86daae86a1945062222222222104222aa1aeaba9a96514a188aaa863aae8ea381431151c755ddd5d3d74a2974457577454401511111511511511))))) else (if i<52 then (if i<46 then (if i<43 then (if i<41 then 0x16a2222089444211550c31d41888622088844552e71d518a8a862a5dd1ad1d69ad154b7c753622a18a9574aaa5ae3a931150c4aba555550a3c54a2942940755a11d56b5baadd5695ad else (if i<42 then 0x15dd55054aaa3baa7f4544bd50a888e9a0c45512f54daea8ea9554293528a515447d526baa3aa5552eaea85444474a2a511061d0a818301a80caa2a940c5429540c else 0x1544554552aa888a9b1551c7150ea2388aa82d115553152ea2a38a9554283528a5054541a8a862a2a50c306aaa58a8f5151c4aaa550d5addd1569ad146ea8aa2a94dd50aa534)) else (if i<44 then 0xa142850328517742801428a1ae94a14280a050a28a894a204a1450d7455294540000a005000014 else (if i<45 then 0x1544554552aa888a9b155dd156a8e88aa820c415156a8ee8a8ab554293528a51554f1526a2ba2a5d52aaa8e2a2d45744abaa555060c541a818d03062a8aa5030d5429450d4 else 0xd50c37d4d52aae861aa30c443508a8888821111574b0d45a862222a2d54293508a5157570d49a86222a52d4baba786ad5d15112ea97743b471c3021c3a81daa2a8aa1504542941c))) else (if i<49 then (if i<47 then 0x50a0505069a03c014058ba14a0114428894038ba155454a00ca5d1554555400145050294294a212888a8a881 else (if i<48 then 0xaaa5aaaa6baaaaa861aa86186abbaabbabbaa588862b188aaa9eaaafa86baaa2aaa2a8a536a515471d4355d55151c70eabbaabbbaa2baaadd1f5544554454544545454aa2a22aa2a940a852954 else 0x1517c546d4a2a596aa2cb150c35506a1863a6b741555d551a96a1ea942ddd10a821505453550a8a8ea944542aa0d430c3d286d2a8862a147a94528a5282383a8707471a21c714)) else (if i<50 then 0xaaa5aaabe7aaaaa861aa86186abbab1a9fbabbaa588862b388aa8e3a863aeaa88eaa2a8a536a5155535555d435d551551d4aabbaabbabaa3ba3a97755445544545445455454a2a22aa2a940a852a954 else (if i<51 then 0x5058001a34d001f0d9ba140813440e2217099ba154715018f1bad28638a861800000008b1a212888a8a881 else 0x2aeeaaab6abaa0550c3d50c32830005555f5553143295544754445129445554fd552ca50ca55515d50c30186154351550c355ddd5d1ca5d297545757755444288511151515511)))) else (if i<58 then (if i<55 then (if i<53 then 0x5ca02a51544b2ca2a88ea38e0ca0621862251545b52d470d4540a000000145514d4b51c3155285282a27a8a88a8a88288b4d51d11ddd11ad11511 else (if i<54 then 0x2aa96aaadaaaaaa861aa86186abbaabbabbaa5aa88862af88aaeeaaeeeaa8eaa8aa294ba954551c7550d57554747d1c3aaa9eaaa9a86baa2abaa51d5544554454544545454a2a22aa2a940a8552954 else 0x282c000d1a680103e1b3740a8102088111103971ba128e22384c1e6e81551151d4000000018b1ba128622a1a8603)) else (if i<56 then 0x1555f6d5574d55554b2d54b2cb028002a8e3aa8e3a8e0a1d5445544544a2944554f3d4b052a8e789eaa186aa186a194286a2aa186abbaabbaba14baa2babbaaa22aa250511151515511 else (if i<57 then 0x288aa9f28a8e8550e2a38fa1c2ddd34455362aabe9471529418a8528a505468a8a2a55055262aa7ea94712aa94aaa11512c4a22a51529445541ee94369430ca50d5443 else 0x408210208860040822a184a07000204115d0974d081045431545d5000000040000))) else (if i<61 then (if i<59 then 0x6ca02a5154534c0030310c128aa27a9e06a278001428aa25a96506a2a585945511d4703151ca51c7282a2ba882a2a228a88b4d516877744d1d11511 else (if i<60 then 0xd5d2f543d4a2211d51c72d43888e22088844d53e72d5188a8e2a56830c3074d156a9abaf96ad1515d152eeab754f6cb52e22a389574babaa149894528a529a18218a83044301e8314 else 0x282c000d1a6801069f1ba16810208811110d85c1f40ae88a84c1e0fa057445554000000018b03e84ba22a1a8603)) else (if i<62 then 0xa22aa6ca2a21828f150a041861818150188515155a2bba1942a56aa971554c32854aa5d5551e2aa5865094baaaaaa11511c4a1529454544555a1a86a534add5d5d551d else (if i<63 then 0x42010822030010822ba100000084115d09540210457455154000000d08000 else 0x1ad3400381cdd038102688511058537428ea2a03019ba286a2a1860000001a212888a8a881))))))
def bank14 (i : Nat) : Nat := (if i<1 then 0xb5dd2c571151c7d511d498f28a1aea8a861835ddd515d52eea8a888a8a9454454a5285294 else 0x2aaa86186abbabba18ae88aaaa6a1aeaa8aaa8a51ea51554b50d75545554aaaa3a86baa2aaa5555511515115151528a88aa940a852954)
def hintAt : Nat → Nat → Option Nat
 | 12, i => if i ≥ 843 && i ≤ 943 then some (bank12 i) else none
 | 13, i => if i ≥ 16 && i ≤ 63 then some (bank13 i) else none
 | 14, i => if i ≥ 0 && i ≤ 1 then some (bank14 i) else none
 | _, _ => none

def fastNode (k i : Nat) := if i < rankCount k then rankNode testPacked signedCertificate k i
 else match hintAt k i with
 | some bits => node signedCertificate k i bits
 | none => nodeSignedVerified signedCertificate k i
theorem fastNode_ok {k i} (h : fastNode k i=true) :
    hybridNode testPacked rankCount signedCertificate k i=true := by
 unfold fastNode at h
 unfold hybridNode
 split <;> rename_i he
 · simpa only [if_pos he] using h
 · rw [if_neg he] at h
   split at h
   · exact node_ok h
   · exact h
def fastBlock (k start : Nat) : Nat → Bool
 | 0 => true
 | n+1 => fastNode k (start+n) && fastBlock k start n
theorem block_ok {k start n} (h : fastBlock k start n=true) :
    hybridBlock testPacked rankCount signedCertificate k start n=true := by
 induction n with
 | zero => rfl
 | succ n ih =>
   obtain ⟨child,rest⟩ := Bool.and_eq_true_iff.mp h
   exact Bool.and_eq_true_iff.mpr ⟨fastNode_ok child,ih rest⟩
end Margin
abbrev auditBlock := hybridBlock testPacked rankCount signedCertificate

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem joinBlock (k start a b : Nat)
    (left : auditBlock k start a = true) (right : auditBlock k (start+a) b = true) :
    auditBlock k start (a+b) = true :=
  @hybridBlock_merge testPacked rankCount signedCertificate k start a b left right



set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem blk9_2 : auditBlock 9 2 1=true := by exact Margin.block_ok (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem level9 : auditBlock 9 0 3=true :=
  (joinBlock 9 0 2 1 (by exact Margin.block_ok (by decide +kernel)) blk9_2)



set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem blk10_47 : auditBlock 10 47 44=true := by exact Margin.block_ok (by decide +kernel)



set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem blk10_138 : auditBlock 10 138 5=true := by exact Margin.block_ok (by decide +kernel)



set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem blk10_192 : auditBlock 10 192 8=true := by exact Margin.block_ok (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem level10 : auditBlock 10 0 200=true :=
  (joinBlock 10 0 128 72 (joinBlock 10 0 47 81 (joinBlock 10 0 3 44 (by exact Margin.block_ok (by decide +kernel)) (by exact Margin.block_ok (by decide +kernel))) (joinBlock 10 47 44 37 blk10_47 (by exact Margin.block_ok (by decide +kernel)))) (joinBlock 10 128 15 57 (joinBlock 10 128 10 5 (by exact Margin.block_ok (by decide +kernel)) blk10_138) (joinBlock 10 143 44 13 (by exact Margin.block_ok (by decide +kernel)) (joinBlock 10 187 5 8 (by exact Margin.block_ok (by decide +kernel)) blk10_192))))



set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem blk11_38 : auditBlock 11 38 44=true := by exact Margin.block_ok (by decide +kernel)



set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem blk11_170 : auditBlock 11 170 44=true := by exact Margin.block_ok (by decide +kernel)



set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem blk11_302 : auditBlock 11 302 44=true := by exact Margin.block_ok (by decide +kernel)



set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem blk11_434 : auditBlock 11 434 44=true := by exact Margin.block_ok (by decide +kernel)



set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem blk11_566 : auditBlock 11 566 44=true := by exact Margin.block_ok (by decide +kernel)



set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem blk11_698 : auditBlock 11 698 44=true := by exact Margin.block_ok (by decide +kernel)



set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem blk11_830 : auditBlock 11 830 44=true := by exact Margin.block_ok (by decide +kernel)



set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem blk11_943 : auditBlock 11 943 27=true := by exact Margin.block_ok (by decide +kernel)



set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem blk11_1019 : auditBlock 11 1019 44=true := by exact Margin.block_ok (by decide +kernel)



set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem blk11_1111 : auditBlock 11 1111 14=true := by exact Margin.block_ok (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem level11 : auditBlock 11 0 1125=true :=
  (joinBlock 11 0 610 515 (joinBlock 11 0 258 352 (joinBlock 11 0 82 176 (joinBlock 11 0 3 79 (by exact Margin.block_ok (by decide +kernel)) (joinBlock 11 3 35 44 (by exact Margin.block_ok (by decide +kernel)) blk11_38)) (joinBlock 11 82 88 88 (joinBlock 11 82 44 44 (by exact Margin.block_ok (by decide +kernel)) (by exact Margin.block_ok (by decide +kernel))) (joinBlock 11 170 44 44 blk11_170 (by exact Margin.block_ok (by decide +kernel))))) (joinBlock 11 258 176 176 (joinBlock 11 258 88 88 (joinBlock 11 258 44 44 (by exact Margin.block_ok (by decide +kernel)) blk11_302) (joinBlock 11 346 44 44 (by exact Margin.block_ok (by decide +kernel)) (by exact Margin.block_ok (by decide +kernel)))) (joinBlock 11 434 88 88 (joinBlock 11 434 44 44 blk11_434 (by exact Margin.block_ok (by decide +kernel))) (joinBlock 11 522 44 44 (by exact Margin.block_ok (by decide +kernel)) blk11_566)))) (joinBlock 11 610 308 207 (joinBlock 11 610 132 176 (joinBlock 11 610 44 88 (by exact Margin.block_ok (by decide +kernel)) (joinBlock 11 654 44 44 (by exact Margin.block_ok (by decide +kernel)) blk11_698)) (joinBlock 11 742 88 88 (joinBlock 11 742 44 44 (by exact Margin.block_ok (by decide +kernel)) (by exact Margin.block_ok (by decide +kernel))) (joinBlock 11 830 44 44 blk11_830 (by exact Margin.block_ok (by decide +kernel))))) (joinBlock 11 918 101 106 (joinBlock 11 918 52 49 (joinBlock 11 918 25 27 (by exact Margin.block_ok (by decide +kernel)) blk11_943) (joinBlock 11 970 5 44 (by exact Margin.block_ok (by decide +kernel)) (by exact Margin.block_ok (by decide +kernel)))) (joinBlock 11 1019 54 52 (joinBlock 11 1019 44 10 blk11_1019 (by exact Margin.block_ok (by decide +kernel))) (joinBlock 11 1073 38 14 (by exact Margin.block_ok (by decide +kernel)) blk11_1111)))))



set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem blk12_71 : auditBlock 12 71 44=true := by exact Margin.block_ok (by decide +kernel)



set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem blk12_203 : auditBlock 12 203 44=true := by exact Margin.block_ok (by decide +kernel)



set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem blk12_335 : auditBlock 12 335 44=true := by exact Margin.block_ok (by decide +kernel)



set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem blk12_428 : auditBlock 12 428 44=true := by exact Margin.block_ok (by decide +kernel)



set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem blk12_560 : auditBlock 12 560 44=true := by exact Margin.block_ok (by decide +kernel)



set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem blk12_692 : auditBlock 12 692 44=true := by exact Margin.block_ok (by decide +kernel)



set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem blk12_793 : auditBlock 12 793 4=true := by exact Margin.block_ok (by decide +kernel)



set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem blk12_861 : auditBlock 12 861 44=true := by exact Margin.block_ok (by decide +kernel)



set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem level12 : auditBlock 12 0 944=true :=
  (joinBlock 12 0 516 428 (joinBlock 12 0 247 269 (joinBlock 12 0 115 132 (joinBlock 12 0 27 88 (by exact Margin.block_ok (by decide +kernel)) (joinBlock 12 27 44 44 (by exact Margin.block_ok (by decide +kernel)) blk12_71)) (joinBlock 12 115 44 88 (by exact Margin.block_ok (by decide +kernel)) (joinBlock 12 159 44 44 (by exact Margin.block_ok (by decide +kernel)) blk12_203))) (joinBlock 12 247 132 137 (joinBlock 12 247 44 88 (by exact Margin.block_ok (by decide +kernel)) (joinBlock 12 291 44 44 (by exact Margin.block_ok (by decide +kernel)) blk12_335)) (joinBlock 12 379 49 88 (joinBlock 12 379 5 44 (by exact Margin.block_ok (by decide +kernel)) (by exact Margin.block_ok (by decide +kernel))) (joinBlock 12 428 44 44 blk12_428 (by exact Margin.block_ok (by decide +kernel)))))) (joinBlock 12 516 264 164 (joinBlock 12 516 132 132 (joinBlock 12 516 44 88 (by exact Margin.block_ok (by decide +kernel)) (joinBlock 12 560 44 44 blk12_560 (by exact Margin.block_ok (by decide +kernel)))) (joinBlock 12 648 44 88 (by exact Margin.block_ok (by decide +kernel)) (joinBlock 12 692 44 44 blk12_692 (by exact Margin.block_ok (by decide +kernel))))) (joinBlock 12 780 61 103 (joinBlock 12 780 13 48 (by exact Margin.block_ok (by decide +kernel)) (joinBlock 12 793 4 44 blk12_793 (by exact Margin.block_ok (by decide +kernel)))) (joinBlock 12 841 64 39 (joinBlock 12 841 20 44 (by exact Margin.block_ok (by decide +kernel)) blk12_861) (joinBlock 12 905 17 22 (by exact Margin.block_ok (by decide +kernel)) (by exact Margin.block_ok (by decide +kernel)))))))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem blk13_0 : auditBlock 13 0 16=true := by exact Margin.block_ok (by decide +kernel)



set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem level13 : auditBlock 13 0 64=true :=
  (joinBlock 13 0 16 48 blk13_0 (joinBlock 13 16 19 29 (by exact Margin.block_ok (by decide +kernel)) (by exact Margin.block_ok (by decide +kernel))))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem blk14_0 : auditBlock 14 0 1=true := by exact Margin.block_ok (by decide +kernel)


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem level14 : auditBlock 14 0 2=true :=
  (joinBlock 14 0 1 1 blk14_0 (by exact Margin.block_ok (by decide +kernel)))

theorem tables : hybridTables testPacked rankCount signedCertificate 14 := by
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
  · exact level9
  · exact level10
  · exact level11
  · exact level12
  · exact level13
  · exact level14

theorem geometry : graphValid signedBase (boundsBefore known251) = true := by decide +kernel
theorem pairChecks : orientedPairsOK signedCertificate = true := by decide +kernel

theorem checkedRoots :
    Limited graph 14 1 (inputs ++ [bin true (inputs.getD 0 zero) (inputs.getD 6 zero)]).toFinset ∧
      Limited graph 14 1 inputs.toFinset := by
  let g := signedCertificate
  have checked := hybridForest_all testPacked testPackedOK rankCount g 14 (boundsBefore known251) (before_sound known251 valid251) geometry pairChecks tables
  have tgt : targetOf g.base = graph := by decide +kernel
  constructor
  · have h := checked 14 (by decide) 1 (by decide)
    have budget : g.budget 14 1 = 1 := by decide +kernel
    have eq : sameWords (stateSet g.base 14 1)
        (inputs ++ [bin true (inputs.getD 0 zero) (inputs.getD 6 zero)]) = true := by decide +kernel
    rwa [tgt,budget,sameWords_sound eq] at h
  · have h := checked 14 (by decide) 0 (by decide)
    have budget : g.budget 14 0 = 1 := by decide +kernel
    have eq : sameWords (stateSet g.base 14 0) inputs = true := by decide +kernel
    rwa [tgt,budget,sameWords_sound eq] at h

end O1677

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev targetFn := edge

def firstOr : Sig := bin true (inputs.getD 0 zero) (inputs.getD 6 zero)
def augmentedInputs : List Sig := inputs ++ [firstOr]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem rowSemantics :
    ∀ r : Row, augmentedInputs.map (bit r) =
      List.ofFn (sample r) ++ [sample r 0 || sample r 6] ∧
      bit r graph = targetFn (sample r) := by decide +kernel

def essentialRow (i : Fin 9) : Row :=
  Fin.ofNat 512 (([96, 1, 2, 4, 1, 1, 257, 4, 8] : List Nat).getD i.val 0)

def toggleEssentialRow (i : Fin 9) : Row :=
  Fin.ofNat 512 ((essentialRow i).val ||| (1 <<< i.val))

set_option maxHeartbeats 0 in
theorem essentialRaw :
    ∀ i : Fin 9, (bit (essentialRow i) graph != bit (toggleEssentialRow i) graph) &&
      (augmentedInputs.all fun w => w == inputs.getD i.val zero ||
        bit (essentialRow i) w == bit (toggleEssentialRow i) w) = true := by decide +kernel

theorem noTail (C : Circuit) (fan : FanInTwo C) (small : C.size ≤ 14)
    (correct : ∀ x : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [x 0 || x 6]) = targetFn x) : False := by
  have outputTable : (execute C.gates augmentedInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let r : Row := ⟨i,hi⟩
    change bit r _ = bit r graph
    rw [← b_read, execute_bits _ _ _ (fun g hg => (fan g hg).1),
      (rowSemantics r).1, (rowSemantics r).2]
    exact correct (sample r)
  have supported := get_rep (execute C.gates augmentedInputs) C.output
  rw [outputTable] at supported
  obtain ⟨k,t,S,le,run,sub⟩ := extract C.gates augmentedInputs fan graph_proper
    (supported.resolve_right (fun h => h graph_proper))
  have bound : k ≤ 14 := le.trans small
  have allRaw : inputs.toFinset ⊆ S := by
    intro w hw
    rw [List.mem_toFinset, ← input_list, List.mem_ofFn] at hw
    obtain ⟨i, rfl⟩ := hw
    have h := essentialRaw i
    simp only [Bool.and_eq_true, bne_iff_ne, List.all_eq_true, Bool.or_eq_true,
      beq_iff_eq, decide_eq_true_eq] at h
    exact raw_required run _ _ sub _ _ h.1 (fun v hv ne => (h.2 v hv).resolve_left ne)
  by_cases h : firstOr ∈ S
  · have eq : S = augmentedInputs.toFinset := by
      apply Finset.Subset.antisymm (fun w hw => List.mem_toFinset.mpr (sub w hw))
      intro w hw
      rcases List.mem_append.mp (List.mem_toFinset.mp hw) with hr | he
      · exact allRaw (List.mem_toFinset.mpr hr)
      · exact List.mem_singleton.mp he ▸ h
    exact O1677.checkedRoots.1 k t bound (RootFloor.signedAtMostOneSeeded bound (eq ▸ run)) (eq ▸ run)
  · have eq : S = inputs.toFinset := by
      apply Finset.Subset.antisymm _ allRaw
      intro w hw
      rcases List.mem_append.mp (sub w hw) with hr | he
      · exact List.mem_toFinset.mpr hr
      · exact (h (List.mem_singleton.mp he ▸ hw)).elim
    exact O1677.checkedRoots.2 k t bound (RootFloor.signedAtMostOneBare bound (eq ▸ run)) (eq ▸ run)

theorem firstOrLower (C : Circuit) (fan : FanInTwo C)
    (head : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 6))
    (correct : circuitFun 9 C = targetFn) : 16 ≤ C.size := by
  let step (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have preserved (gs : List Gate) (w : List Bool) (h : 9 < w.length) :
      (gs.foldl step w).getD 9 false = w.getD 9 false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      · exact List.getD_append _ _ _ _ h
      · simp [step]
        omega
  obtain ⟨gs, out⟩ := C
  cases gs with
  | nil =>
    have impossible := head (fun _ => true)
    change (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = true at impossible
    simp at impossible
  | cons g tail =>
    by_contra! short
    let D : Circuit := ⟨tail, out⟩
    apply noTail D
    · exact fun g hg => fan g (List.mem_cons_of_mem _ hg)
    · change tail.length ≤ 14
      change (g :: tail).length < 16 at short
      simp only [List.length_cons] at short
      omega
    · intro x
      have fst := head x
      let value := g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)
      change (tail.foldl step (List.ofFn x ++ [value])).getD 9 false = _ at fst
      rw [preserved _ _ (by simp), List.getD_append_right _ _ _ _ (by simp), List.length_ofFn] at fst
      change value = (x 0 || x 6) at fst
      have eval := congrFun correct x
      change D.eval (List.ofFn x ++ [value]) = targetFn x at eval
      rwa [fst] at eval

end PEqualNP.Outside.L_meta_1677

theorem PEqualNP.Outside.L_meta_1677 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size :=
  PEqualNP.Outside.L_meta_1677.firstOrLower
