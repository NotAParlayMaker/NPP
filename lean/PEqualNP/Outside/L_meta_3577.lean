import Mathlib
import PEqualNP.Defs

-- The graph and block proofs adapt kunalb541's contribution in pull request 7479
-- to open-goat/pequalnp-proofs, under the Apache License 2.0.
-- The parameters and the theorem on unbounded multiplicative loss are separate.
namespace PEqualNP.Outside.L_meta_3577_aux

-- Store the modulus and number of sites with an offset of two.
-- This makes the lower bounds available to the standard arithmetic instances.
abbrev Params := {t : ℕ × ℕ × ℕ //
  (t.1+2).Prime ∧ (t.2.1+2)^2 ≤ t.1+2 ∧ t.1+2 ≤ 2^t.2.2}

abbrev Params.q (p : Params) := p.val.1 + 2
abbrev Params.u (p : Params) := p.val.2.1 + 2
abbrev Params.b (p : Params) := p.val.2.2
theorem Params.prime (p : Params) : p.q.Prime := p.property.1
theorem Params.u2 (p : Params) : 2 ≤ p.u := Nat.le_add_left 2 _
theorem Params.leadBound (p : Params) : p.u^2 ≤ p.q := p.property.2.1
theorem Params.sites (p : Params) : 2*p.u ≤ p.q := by
  have hu := p.u2
  nlinarith [p.leadBound, Nat.mul_le_mul_right p.u hu]
theorem Params.bits (p : Params) : p.q ≤ 2^p.b := p.property.2.2

abbrev F (p : Params) := ZMod p.q
abbrev Ix (p : Params) := Fin p.u
abbrev Left (p : Params) := F p × F p × Fin (p.u^2)
abbrev Right (p : Params) := (Ix p × (Ix p)) × (F p × (F p))
abbrev Vertex (p : Params) := Sum (Left p) (Right p)

def coordA (p : Params) (i : Ix p) : F p := (i.val : F p)
def coordB (p : Params) (j : Ix p) : F p := ((p.u + j.val : Nat) : F p)

def val (p : Params) (u : Left p) (x : F p) : F p := u.1 + u.2.1*x + (u.2.2.val : F p)*x^2
def atPair (p : Params) (u : Left p) (ij : Ix p × (Ix p)) : F p × (F p) :=
  (val p u (coordA p ij.1), (val p) u (coordB p ij.2))
def inc (p : Params) (u : Left p) (w : Right p) : Prop := atPair p u w.1 = w.2

def graph (p : Params) : SimpleGraph (Vertex p) :=
  { Adj := fun a b => match a, b with
      | .inl u, .inr w => (inc p) u w
      | .inr w, .inl u => (inc p) u w
      | _, _ => False
    symm := ⟨by rintro (_|_) (_|_) h <;> exact h⟩
    loopless := ⟨by rintro (_|_) <;> simp⟩ }

noncomputable def edgeCount (p : Params) : ℕ := by
  classical
  exact (graph p).edgeFinset.card

private theorem cast_inj (p : Params) {a b : Nat} (ha : a < p.q) (hb : b < p.q)
    (h : (a : F p) = (b : F p)) : a = b := by
  have e := congrArg ZMod.val h
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using e

theorem coordA_inj (p : Params) : Function.Injective (coordA p) := by
  have hsites := p.sites
  intro i j h
  exact Fin.ext (cast_inj p (by have := i.isLt; omega) (by have := j.isLt; omega) h)

theorem coordB_inj (p : Params) : Function.Injective (coordB p) := by
  have hsites := p.sites
  intro i j h
  have e := cast_inj p (a := p.u+i.val) (b := p.u+j.val) (by have := i.isLt; omega) (by have := j.isLt; omega) h
  exact Fin.ext (by omega)

theorem coord_disjoint (p : Params) (i j : Ix p) : (coordA p) i ≠ (coordB p) j := by
  have hsites := p.sites
  intro h
  have e := cast_inj p (a := i.val) (b := p.u+j.val) (by have := i.isLt; omega) (by have := j.isLt; omega) h
  have il := i.isLt
  omega

private theorem three_points (p : Params) {u v : Left p} {a b c : F p}
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (ea : (val p) u a = (val p) v a) (eb : (val p) u b = (val p) v b) (ec : (val p) u c = (val p) v c) : u = v := by
  let : Fact p.q.Prime := ⟨p.prime⟩
  dsimp only [val] at ea eb ec
  have ab0 : (b-a)*((u.2.1-v.2.1)+((u.2.2.val : F p)-(v.2.2.val : F p))*(a+b)) = 0 := by linear_combination eb - ea
  have ac0 : (c-a)*((u.2.1-v.2.1)+((u.2.2.val : F p)-(v.2.2.val : F p))*(a+c)) = 0 := by linear_combination ec - ea
  have ab1 := (mul_eq_zero.mp ab0).resolve_left (sub_ne_zero.mpr ab.symm)
  have ac1 := (mul_eq_zero.mp ac0).resolve_left (sub_ne_zero.mpr ac.symm)
  have bc0 : (b-c)*((u.2.2.val : F p)-(v.2.2.val : F p)) = 0 := by linear_combination ab1 - ac1
  have uc := sub_eq_zero.mp ((mul_eq_zero.mp bc0).resolve_left (sub_ne_zero.mpr bc))
  rw [uc,sub_self,zero_mul,add_zero] at ab1
  have ub := sub_eq_zero.mp ab1
  rw [uc,ub] at ea
  exact Prod.ext (by linear_combination ea) (Prod.ext ub (Fin.ext (cast_inj p (u.2.2.isLt.trans_le p.leadBound) (v.2.2.isLt.trans_le p.leadBound) uc)))

theorem no_rectangle (p : Params) {u v : Left p} {w z : Right p}
    (huw : (inc p) u w) (hvw : (inc p) v w) (huz : (inc p) u z) (hvz : (inc p) v z) : u = v ∨ w = z := by
  have e₁ := congrArg Prod.fst (huw.trans hvw.symm)
  have e₂ := congrArg Prod.snd (huw.trans hvw.symm)
  have e₃ := congrArg Prod.fst (huz.trans hvz.symm)
  have e₄ := congrArg Prod.snd (huz.trans hvz.symm)
  by_cases a : w.1.1 = z.1.1
  · by_cases b : w.1.2 = z.1.2
    · right
      have ij : w.1 = z.1 := Prod.ext a b
      exact Prod.ext ij (huw.symm.trans ((congrArg (atPair p u) ij).trans huz))
    · left
      exact three_points p (coord_disjoint p _ _) (coord_disjoint p _ _) ((coordB_inj p).ne b) e₁ e₂ e₄
  · left
    exact three_points p (coord_disjoint p _ _) ((coordA_inj p).ne a) (coord_disjoint p _ _).symm e₁ e₂ e₃

theorem no_four (p : Params) (a b c d : Vertex p) (ac : a ≠ c) (bd : b ≠ d) :
    ¬ ((graph p).Adj a b ∧ (graph p).Adj b c ∧ (graph p).Adj c d ∧ (graph p).Adj d a) := by
  rintro ⟨h₁,h₂,h₃,h₄⟩
  rcases a with a|a <;> rcases b with b|b <;> rcases c with c|c <;> rcases d with d|d <;>
    try contradiction
  · rcases (no_rectangle p) h₁ h₂ h₄ h₃ with h|h
    · exact ac (congrArg Sum.inl h)
    · exact bd (congrArg Sum.inr h)
  · rcases (no_rectangle p) h₁ h₄ h₂ h₃ with h|h
    · exact bd (congrArg Sum.inl h)
    · exact ac (congrArg Sum.inr h)

section EdgeCount
variable {L R I : Type} [Fintype L] [Fintype I]
theorem edge_lower (mk : L → I → R) (proj : R → I) (hp : ∀ l i, proj (mk l i) = i)
    (G : SimpleGraph (L ⊕ R)) [Fintype G.edgeSet]
    (edges : ∀ l i, G.Adj (.inl l) (.inr (mk l i))) :
    ∀ k : Nat, Fintype.card I = k → Fintype.card L * k ≤ G.edgeFinset.card := by
  rintro _ rfl
  let emit (p : L × I) : G.edgeSet := ⟨s(.inl p.1,.inr (mk p.1 p.2)), edges p.1 p.2⟩
  have inject : Function.Injective emit := by
    rintro ⟨u,i⟩ ⟨v,j⟩ h
    have he : s((Sum.inl u : L ⊕ R),Sum.inr (mk u i)) =
              s((Sum.inl v : L ⊕ R),Sum.inr (mk v j)) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp he with ⟨hu,hm⟩ | ⟨bad,_⟩
    · exact Prod.ext (Sum.inl.inj hu) (by simpa only [hp] using congrArg proj (Sum.inr.inj hm))
    · cases bad
  calc
    Fintype.card L * Fintype.card I = Fintype.card (L × I) := (Fintype.card_prod L I).symm
    _ ≤ Fintype.card G.edgeSet := Fintype.card_le_of_injective emit inject
    _ = G.edgeFinset.card := G.card_edgeSet
end EdgeCount

private theorem pairCard (m : Nat) : Fintype.card (Fin m × Fin m) = m^2 := by
  simp [Fintype.card_prod,pow_two]

theorem count_edges (p : Params) : Fintype.card (Left p) * p.u^2 ≤ edgeCount p := by
  classical
  exact edge_lower (I := Ix p × (Ix p)) (fun u ij => (ij, (atPair p) u ij))
    Prod.fst (fun _ _ => rfl) (graph p) (fun _ _ => rfl) (p.u^2) (pairCard p.u)

abbrev Label (p : Params) := Bool ⊕ (Bool × (Ix p) × Fin p.b × Bool)

def symbolBit (p : Params) (x : F p) (j : Fin p.b) : Bool := x.val.testBit j.val

theorem separate_symbols (p : Params) {x y : F p} (ne : x ≠ y) : ∃ j : Fin p.b, (symbolBit p) x j ≠ (symbolBit p) y j := by
  classical
  by_contra! h
  apply ne
  apply ZMod.val_injective p.q
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < p.b
  · exact h ⟨j,hj⟩
  · have hp : 2^p.b ≤ 2^j := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
    have xs := ZMod.val_lt x
    have ys := ZMod.val_lt y
    have qbits := p.bits
    rw [Nat.testBit_lt_two_pow (by omega : x.val < 2^j), Nat.testBit_lt_two_pow (by omega : y.val < 2^j)]

def wordSymbol (p : Params) (u : Left p) (half : Bool) (i : Ix p) : F p :=
  if half then (val p) u (coordB p i) else (val p) u (coordA p i)

def rightCoord (p : Params) (r : Right p) (half : Bool) : Ix p := if half then r.1.2 else r.1.1

def rightSymbol (p : Params) (r : Right p) (half : Bool) : F p := if half then r.2.2 else r.2.1

theorem inc_symbols (p : Params) (u : Left p) (r : Right p) : (inc p) u r ↔ ∀ half,
    (wordSymbol p) u half (rightCoord p r half) = (rightSymbol p) r half := by
  constructor
  · intro h half
    cases half
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  · intro h
    exact Prod.ext (h false) (h true)

def inBlock (p : Params) : Label p → (Vertex p) → Prop
  | .inl side, .inl _ => side = false
  | .inl side, .inr _ => side = true
  | .inr (h,i,j,pol), .inl u => (symbolBit p) (wordSymbol p u h i) j = pol
  | .inr (h,i,j,pol), .inr r => (rightCoord p) r h = i ∧ (symbolBit p) (rightSymbol p r h) j ≠ pol

noncomputable def blocks (p : Params) (j : Label p) : Finset (Vertex p) := by
  classical
  exact Finset.univ.filter (inBlock p j)

theorem mem_blocks (p : Params) (j : Label p) (v : Vertex p) : v ∈ (blocks p) j ↔ (inBlock p) j v := by
  classical
  simp only [blocks,Finset.mem_filter,Finset.mem_univ,true_and]

private theorem cross_independent (p : Params) (j : Label p) {u : Left p} {r : Right p}
    (hu : (inBlock p) j (.inl u)) (hr : (inBlock p) j (.inr r)) : ¬ (inc p) u r := by
  rcases j with h | ⟨h,i,bit,pol⟩
  · change h = false at hu
    change h = true at hr
    simp [hu] at hr
  · change (symbolBit p) (wordSymbol p u h i) bit = pol at hu
    change (rightCoord p) r h = i ∧ (symbolBit p) (rightSymbol p r h) bit ≠ pol at hr
    intro adj
    have eq := (inc_symbols p u r).mp adj h
    rw [hr.1] at eq
    exact hr.2 ((congrArg (fun s => (symbolBit p) s bit) eq).symm.trans hu)

section AbstractBlocks

private theorem abstract_independent (p : Params) (B : Label p → Finset (Vertex p)) (memB : ∀ j v, v ∈ B j ↔ (inBlock p) j v)
    (j : Label p) (a : Vertex p) (ha : a ∈ B j) (b : Vertex p) (hb : b ∈ B j) :
    ¬ (graph p).Adj a b := by
  rw [memB] at ha hb
  cases a with
  | inl u => cases b with
             | inl u' => exact id
             | inr r => exact cross_independent p j ha hb
  | inr r => cases b with
             | inl u => exact cross_independent p j hb ha
             | inr r' => exact id

private theorem abstract_cover (p : Params) (B : Label p → Finset (Vertex p)) (memB : ∀ j v, v ∈ B j ↔ (inBlock p) j v)
    (v : Vertex p) : ∃ j : Label p, v ∈ B j := by
  cases v with
  | inl u => exact ⟨.inl false,(memB _ _).mpr rfl⟩
  | inr r => exact ⟨.inl true,(memB _ _).mpr rfl⟩

private theorem abstract_cocover (p : Params) (B : Label p → Finset (Vertex p)) (memB : ∀ j v, v ∈ B j ↔ (inBlock p) j v)
    (v : Vertex p) : ∃ j : Label p, v ∉ B j := by
  cases v with
  | inl u => exact ⟨.inl true, fun h => Bool.noConfusion ((memB _ _).mp h)⟩
  | inr r => exact ⟨.inl false, fun h => Bool.noConfusion ((memB _ _).mp h)⟩

private theorem cross_nonedge (p : Params) (B : Label p → Finset (Vertex p)) (memB : ∀ j v, v ∈ B j ↔ (inBlock p) j v)
    (u : Left p) (r : Right p) (h : ¬ (inc p) u r) :
    ∃ j : Label p, Sum.inl u ∈ B j ∧ Sum.inr r ∈ B j := by
  classical
  rw [(inc_symbols p)] at h
  push Not at h
  obtain ⟨half,ne⟩ := h
  obtain ⟨j,bitne⟩ := separate_symbols p ne
  let i := rightCoord p r half
  let pol := symbolBit p (wordSymbol p u half i) j
  refine ⟨Sum.inr (half,i,j,pol),(memB _ _).mpr rfl,(memB _ _).mpr ?_⟩
  exact ⟨rfl, Ne.symm bitne⟩

private theorem abstract_nonedges (p : Params) (B : Label p → Finset (Vertex p)) (memB : ∀ j v, v ∈ B j ↔ (inBlock p) j v)
    (a b : Vertex p) (_ne : a ≠ b) (h : ¬ (graph p).Adj a b) :
    ∃ j : Label p, a ∈ B j ∧ b ∈ B j := by
  cases a with
  | inl u => cases b with
             | inl u' => exact ⟨.inl false, (memB _ _).mpr rfl, (memB _ _).mpr rfl⟩
             | inr r => exact cross_nonedge p B memB u r h
  | inr r => cases b with
             | inr r' => exact ⟨.inl true, (memB _ _).mpr rfl, (memB _ _).mpr rfl⟩
             | inl u =>
                 obtain ⟨j,hj,hk⟩ := cross_nonedge p B memB u r h
                 exact ⟨j,hk,hj⟩

private def extraRight (p : Params) (i : Ix p) (s : F p) : Right p := ((i,i),(0,s))
private def extraLeft (p : Params) (s : F p) : Left p := (s,0,0)
private theorem differentRight (p : Params) (i : Ix p) : (Sum.inr (extraRight p i 0) : Vertex p) ≠ Sum.inr (extraRight p i 1) := by
  let : Fact p.q.Prime := ⟨p.prime⟩
  exact fun h => zero_ne_one (congrArg (fun x : Right p => x.2.2) (Sum.inr.inj h))
private theorem differentLeft (p : Params) : (Sum.inl (extraLeft p 0) : Vertex p) ≠ Sum.inl (extraLeft p 1) := by
  let : Fact p.q.Prime := ⟨p.prime⟩
  exact fun h => zero_ne_one (congrArg (fun x : Left p => x.1) (Sum.inl.inj h))

private theorem missesPair (p : Params) (B : Label p → Finset (Vertex p)) (memB : ∀ j v, v ∈ B j ↔ (inBlock p) j v)
    (j : Label p) : ∃ a b : Vertex p, a ≠ b ∧ a ∉ B j ∧ b ∉ B j := by
  rcases j with (_ | _) | ⟨h,i,bit,pol⟩
  · exact ⟨.inr (extraRight p 0 0), .inr (extraRight p 0 1), (differentRight p) 0,
      fun x => Bool.noConfusion ((memB _ _).mp x), fun x => Bool.noConfusion ((memB _ _).mp x)⟩
  · exact ⟨.inl (extraLeft p 0), .inl (extraLeft p 1), (differentLeft p),
      fun x => Bool.noConfusion ((memB _ _).mp x), fun x => Bool.noConfusion ((memB _ _).mp x)⟩
  · let other : Ix p := if i = 0 then 1 else 0
    have diff : other ≠ i := by
      by_cases hi : i = 0
      · subst i; simp only [other, ite_true]; intro he; have heq := congrArg Fin.val he; have hu := p.u2; simp [Nat.mod_eq_of_lt (by omega : 1 < p.u)] at heq
      · simpa [other,hi] using Ne.symm hi
    have omitted (s : F p) : Sum.inr (extraRight p other s) ∉ B (Sum.inr (h,i,bit,pol)) := by
      intro hn
      have hin := ((memB _ _).mp hn).1
      cases h <;> exact diff hin
    exact ⟨.inr (extraRight p other 0), .inr (extraRight p other 1), (differentRight p) other,omitted _,omitted _⟩

private theorem card_bound_two_missing {α : Type} [Fintype α] (s : Finset α) (a b : α)
    (ne : a ≠ b) (ha : a ∉ s) (hb : b ∉ s) : s.card + 2 ≤ Fintype.card α := by
  classical
  have sa : a ∈ Finset.univ \ s := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,ha⟩
  have sb : b ∈ Finset.univ \ s := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hb⟩
  have ss : ({a,b} : Finset α) ⊆ Finset.univ \ s :=
    Finset.insert_subset sa (Finset.singleton_subset_iff.mpr sb)
  have le := Finset.card_le_card ss
  rw [Finset.card_pair ne] at le
  have eq := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ s)
  rw [Finset.card_univ] at eq
  omega

private theorem abstract_miss_two (p : Params) (B : Label p → Finset (Vertex p)) (memB : ∀ j v, v ∈ B j ↔ (inBlock p) j v)
    (j : Label p) : (B j).card + 2 ≤ Fintype.card (Vertex p) := by
  obtain ⟨a,b,ne,ha,hb⟩ := missesPair p B memB j
  exact card_bound_two_missing (B j) a b ne ha hb

end AbstractBlocks

def IsIndependentFamily (p : Params) (B : Label p → Finset (Vertex p)) : Prop :=
  ∀ j : Label p, ∀ a ∈ B j, ∀ b ∈ B j, ¬ (graph p).Adj a b

theorem blocks_independent (p : Params) : (IsIndependentFamily p) (blocks p) := abstract_independent p (blocks p) (mem_blocks p)

theorem blocks_cover (p : Params) (v : Vertex p) : ∃ j : Label p, v ∈ (blocks p) j := abstract_cover p (blocks p) (mem_blocks p) v

theorem blocks_cocover (p : Params) (v : Vertex p) : ∃ j : Label p, v ∉ (blocks p) j := abstract_cocover p (blocks p) (mem_blocks p) v

theorem blocks_nonedges (p : Params) (a b : Vertex p) (ne : a ≠ b) (h : ¬ (graph p).Adj a b) :
    ∃ j : Label p, a ∈ (blocks p) j ∧ b ∈ (blocks p) j := abstract_nonedges p (blocks p) (mem_blocks p) a b ne h

theorem blocks_miss_two (p : Params) (j : Label p) : (blocks p j).card + 2 ≤ Fintype.card (Vertex p) :=
  (abstract_miss_two p) (blocks p) (mem_blocks p) j

theorem label_count (p : Params) : Fintype.card (Label p) = 4*p.u*p.b+2 := by
  simp [Label,Ix,Fintype.card_prod,Fintype.card_sum]
  ring

theorem left_count (p : Params) : Fintype.card (Left p) = p.q^2*p.u^2 := by
  simp [Left,F,Fintype.card_prod, ZMod.card]
  ring

theorem vertex_count (p : Params) : Fintype.card (Vertex p) = 2*(p.q^2*p.u^2) := by
  rw [show Fintype.card (Vertex p) = Fintype.card (Left p) + Fintype.card (Right p) from Fintype.card_sum]
  rw [left_count]
  simp [Right,Ix,F,Fintype.card_prod,ZMod.card]
  ring

private theorem square_le_pow {s : ℕ} (hs : 4 ≤ s) : s^2 ≤ 2^s := by
  induction s, hs using Nat.le_induction with
  | base => decide
  | succ s hs ih =>
    rw [pow_succ 2 s]
    nlinarith [Nat.mul_le_mul_right s hs]

-- The seventh powers express a bound with the seventh root of the vertex count.
private theorem seventh_gap (p : Params) (C : ℕ) (qhi : p.q ≤ 2*p.u^2)
    (wide : 8*(2*C*(4*p.b+2))^7 < p.u) :
    (C*(Fintype.card (Label p)*Fintype.card (Vertex p)))^7 * Fintype.card (Vertex p) <
      (edgeCount p)^7 := by
  let L := p.q^2*p.u^2
  have posL : 0 < L := by dsimp [L]; have := p.prime.pos; have := p.u2; positivity
  have posU : 0 < p.u := by have := p.u2; omega
  have pos : 0 < L^7*p.u^13 := by positivity
  have vertices : Fintype.card (Vertex p) ≤ 8*p.u^6 := by
    rw [vertex_count]
    calc 2*(p.q^2*p.u^2) ≤ 2*((2*p.u^2)^2*p.u^2) := by gcongr
         _ = 8*p.u^6 := by ring
  have labels : Fintype.card (Label p) ≤ p.u*(4*p.b+2) := by
    rw [label_count]
    nlinarith [p.u2]
  have base : C*(Fintype.card (Label p)*Fintype.card (Vertex p))
      ≤ C*((p.u*(4*p.b+2))*(2*L)) := by
    rw [vertex_count]
    gcongr
  calc (C*(Fintype.card (Label p)*Fintype.card (Vertex p)))^7 * Fintype.card (Vertex p)
      ≤ (C*((p.u*(4*p.b+2))*(2*L)))^7 * (8*p.u^6) := by gcongr
    _ = (L^7*p.u^13)*(8*(2*C*(4*p.b+2))^7) := by
      exact (show ∀ l x y z : ℕ, (z*((x*y)*(2*l)))^7*(8*x^6) = (l^7*x^13)*(8*(2*z*y)^7) by
        intro l x y z; ring) L p.u (4*p.b+2) C
    _ < (L^7*p.u^13)*p.u := Nat.mul_lt_mul_of_pos_left wide pos
    _ = (Fintype.card (Left p)*p.u^2)^7 := by rw [left_count]; dsimp [L]; ring
    _ ≤ (edgeCount p)^7 := Nat.pow_le_pow_left (count_edges p) 7

theorem polynomial_parameters (C : ℕ) :
    ∃ p : Params,
      (C*(Fintype.card (Label p)*Fintype.card (Vertex p)))^7 * Fintype.card (Vertex p) <
        (edgeCount p)^7 := by
  let s := 512*(C+1)
  let u := (2^s)^8
  let b := 16*s+1
  have hs : 8 ≤ s := by dsimp [s]; omega
  have hpow : s^16 ≤ u := by
    rw [show (16 : ℕ) = 2*8 by decide, pow_mul]
    exact Nat.pow_le_pow_left (square_le_pow (by omega)) 8
  have hu : 2 ≤ u := by
    have h := Nat.pow_le_pow_left hs 16
    omega
  obtain ⟨q,prime,lo,hi⟩ := Nat.exists_prime_lt_and_le_two_mul (u^2) (by positivity)
  have bits : q ≤ 2^b := by
    calc q ≤ 2*u^2 := hi
         _ = 2^(16*s+1) := by
           dsimp only [u]
           rw [← pow_mul, ← pow_mul, pow_succ 2 (16*s)]
           rw [show s*(8*2) = 16*s by omega, Nat.mul_comm]
  have small : 2*C*(4*b+2) ≤ s^2 := by dsimp [b,s]; nlinarith
  have wide : 8*(2*C*(4*b+2))^7 < u := by
    calc 8*(2*C*(4*b+2))^7 ≤ 8*(s^2)^7 := by gcongr
         _ < (s^2)*(s^2)^7 := by
           apply Nat.mul_lt_mul_of_pos_right
           · nlinarith [Nat.mul_self_le_mul_self hs]
           · positivity
         _ = s^16 := by ring
         _ ≤ u := hpow
  have eqQ : q-2+2 = q := by have := prime.two_le; omega
  have eqU : u-2+2 = u := by omega
  let p : Params := ⟨(q-2,u-2,b), by
    dsimp only
    rw [eqQ,eqU]
    exact ⟨prime,lo.le,bits⟩⟩
  refine ⟨p, seventh_gap p C ?_ ?_⟩
  · change q-2+2 ≤ 2*(u-2+2)^2
    simpa only [eqU,eqQ] using hi
  · change 8*(2*C*(4*b+2))^7 < u-2+2
    simpa only [eqU] using wide

-- For a right vertex, each permitted leading coefficient gives one neighbor.
noncomputable def through (p : Params) (r : Right p) (t : Fin (p.u^2)) : Left p := by
  let : Fact p.q.Prime := ⟨p.prime⟩
  let x := coordA p r.1.1
  let y := coordB p r.1.2
  let c : F p := t.val
  let slope := ((r.2.2-c*y^2)-(r.2.1-c*x^2))/(y-x)
  exact (r.2.1-slope*x-c*x^2, slope, t)

private theorem through_inc (p : Params) (r : Right p) (t : Fin (p.u^2)) :
    inc p (through p r t) r := by
  let : Fact p.q.Prime := ⟨p.prime⟩
  have ne := sub_ne_zero.mpr (coord_disjoint p r.1.1 r.1.2).symm
  apply Prod.ext
  · dsimp [through,atPair,val]
    ring
  · dsimp [through,atPair,val]
    field_simp [ne]
    ring

private theorem unique_with_lead (p : Params) {u v : Left p} {r : Right p}
    (hu : inc p u r) (hv : inc p v r) (h : u.2.2 = v.2.2) : u = v := by
  let : Fact p.q.Prime := ⟨p.prime⟩
  have ha := congrArg Prod.fst (hu.trans hv.symm)
  have hb := congrArg Prod.snd (hu.trans hv.symm)
  dsimp [atPair,val] at ha hb
  rw [h] at ha hb
  have prod : (coordB p r.1.2 - coordA p r.1.1) * (u.2.1-v.2.1) = 0 := by
    linear_combination hb - ha
  have slope := sub_eq_zero.mp ((mul_eq_zero.mp prod).resolve_left
    (sub_ne_zero.mpr (coord_disjoint p r.1.1 r.1.2).symm))
  rw [slope] at ha
  exact Prod.ext (by linear_combination ha) (Prod.ext slope h)

theorem regular_degree (p : Params) (v : Vertex p) :
    ((graph p).neighborSet v).ncard = p.u^2 := by
  classical
  rw [← Set.fintypeCard_eq_ncard]
  cases v with
  | inl l =>
    let pack (ij : Ix p × Ix p) : (graph p).neighborSet (.inl l) :=
      ⟨.inr (ij,atPair p l ij),rfl⟩
    have inj : Function.Injective pack := by
      intro a b h
      exact congrArg Prod.fst (Sum.inr.inj (congrArg Subtype.val h))
    have surj : Function.Surjective pack := by
      rintro ⟨v,h⟩
      cases v with
      | inl v => exact False.elim h
      | inr r =>
        refine ⟨r.1, Subtype.ext (congrArg Sum.inr ?_)⟩
        exact Prod.ext rfl h
    exact (Fintype.card_congr (Equiv.ofBijective pack ⟨inj,surj⟩)).symm.trans (pairCard p.u)
  | inr r =>
    let pack (t : Fin (p.u^2)) : (graph p).neighborSet (.inr r) :=
      ⟨.inl (through p r t),through_inc p r t⟩
    have inj : Function.Injective pack := by
      intro a b h
      exact congrArg (fun x : Left p => x.2.2) (Sum.inl.inj (congrArg Subtype.val h))
    have surj : Function.Surjective pack := by
      rintro ⟨v,h⟩
      cases v with
      | inr v => exact False.elim h
      | inl l =>
        refine ⟨l.2.2, Subtype.ext (congrArg Sum.inl ?_)⟩
        exact unique_with_lead p (through_inc p r l.2.2) h rfl
    exact (Fintype.card_congr (Equiv.ofBijective pack ⟨inj,surj⟩)).symm.trans (Fintype.card_fin _)

theorem transfer (C : ℕ) {V K : Type*} [Fintype V] [Fintype K] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (side : V → Bool) (I : K → Finset V)
    (reg : ∃ d, ∀ v, (G.neighborSet v).ncard = d)
    (part : ∀ a b, G.Adj a b → side a ≠ side b)
    (square : ∀ a b c d : V, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hk : 2 ≤ Fintype.card K)
    (ind : ∀ j, ∀ a ∈ I j, ∀ b ∈ I j, ¬ G.Adj a b)
    (inside : ∀ v, ∃ j, v ∈ I j)
    (outside : ∀ v, ∃ j, v ∉ I j)
    (miss : ∀ j, (I j).card + 2 ≤ Fintype.card V)
    (nonedge : ∀ a b, a ≠ b → ¬ G.Adj a b → ∃ j, a ∈ I j ∧ b ∈ I j)
    (large : (C*(Fintype.card K * Fintype.card V))^7 * Fintype.card V < G.edgeFinset.card^7) :
    ¬ (∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (side : Fin n → Bool) (I : Fin k → Finset (Fin n)), (∃ d, ∀ v, (G.neighborSet v).ncard = d) → (∀ a b : Fin n, G.Adj a b → side a ≠ side b) → (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → 2 ≤ k → (∀ j : Fin k, ∀ a ∈ I j, ∀ b ∈ I j, ¬ G.Adj a b) → (∀ v : Fin n, ∃ j : Fin k, v ∈ I j) → (∀ v : Fin n, ∃ j : Fin k, v ∉ I j) → (∀ j : Fin k, (I j).card + 2 ≤ n) → (∀ a b : Fin n, a ≠ b → ¬ G.Adj a b → ∃ j : Fin k, a ∈ I j ∧ b ∈ I j) → ∃ T : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) ∧ (G.edgeFinset.card + T.card + 1)^7 ≤ (C * ∑ j : Fin k, (n - (I j).card))^7 * n) := by
  classical
  intro hall
  let e := Fintype.equivFin V
  let f := Fintype.equivFin K
  let H := G.comap e.symm
  let J := fun j : Fin (Fintype.card K) => (I (f.symm j)).map e.toEmbedding
  have mem (j v) : v ∈ J j ↔ e.symm v ∈ I (f.symm j) := by
    simp [J]
  have regularH : ∃ d, ∀ v, (H.neighborSet v).ncard = d := by
    obtain ⟨d,hd⟩ := reg
    refine ⟨d, fun v => ?_⟩
    calc (H.neighborSet v).ncard = (G.neighborSet (e.symm v)).ncard := by
           simp only [← Set.fintypeCard_eq_ncard]
           exact Fintype.card_congr ((SimpleGraph.Iso.comap e.symm G).mapNeighborSet v)
         _ = d := hd _
  obtain ⟨T,_,bound⟩ := hall _ _ H (fun v => side (e.symm v)) J regularH
    (fun a b => part _ _) (fun a b c d ha hb =>
      square _ _ _ _ (e.symm.injective.ne ha) (e.symm.injective.ne hb)) hk
    (fun j a ha b hb => ind _ _ ((mem j a).1 ha) _ ((mem j b).1 hb))
    (by intro v; obtain ⟨j,h⟩ := inside (e.symm v)
        exact ⟨f j,(mem _ _).2 (by simpa using h)⟩)
    (by intro v; obtain ⟨j,h⟩ := outside (e.symm v)
        exact ⟨f j,fun hm => h (by simpa using (mem _ _).1 hm)⟩)
    (fun j => by simpa only [J, Finset.card_map] using miss (f.symm j))
    (by intro a b hab hn
        obtain ⟨j,ha,hb⟩ := nonedge (e.symm a) (e.symm b) (e.symm.injective.ne hab) hn
        exact ⟨f j,(mem _ _).2 (by simpa using ha),(mem _ _).2 (by simpa using hb)⟩)
  have ee : H.edgeFinset.card = G.edgeFinset.card :=
    (SimpleGraph.Iso.comap e.symm G).card_edgeFinset_eq
  have upper : (∑ j : Fin (Fintype.card K), (Fintype.card V - (J j).card)) ≤
      Fintype.card K * Fintype.card V := by
    calc _ ≤ ∑ _j : Fin (Fintype.card K), Fintype.card V :=
            Finset.sum_le_sum (fun _ _ => Nat.sub_le _ _)
         _ = _ := by simp
  have scaled := Nat.mul_le_mul_left C upper
  have scaledPow := Nat.mul_le_mul_right (Fintype.card V) (Nat.pow_le_pow_left scaled 7)
  have below := Nat.pow_le_pow_left (show H.edgeFinset.card ≤ H.edgeFinset.card + T.card + 1 by omega) 7
  rw [ee] at below bound
  omega

-- Even multiplying the total cost by a fixed constant and the seventh root of n fails.
theorem regular_seventh_power_obstruction (C : ℕ) :
    ¬ (∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (side : Fin n → Bool) (I : Fin k → Finset (Fin n)), (∃ d, ∀ v, (G.neighborSet v).ncard = d) → (∀ a b : Fin n, G.Adj a b → side a ≠ side b) → (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → 2 ≤ k → (∀ j : Fin k, ∀ a ∈ I j, ∀ b ∈ I j, ¬ G.Adj a b) → (∀ v : Fin n, ∃ j : Fin k, v ∈ I j) → (∀ v : Fin n, ∃ j : Fin k, v ∉ I j) → (∀ j : Fin k, (I j).card + 2 ≤ n) → (∀ a b : Fin n, a ≠ b → ¬ G.Adj a b → ∃ j : Fin k, a ∈ I j ∧ b ∈ I j) → ∃ T : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) ∧ (G.edgeFinset.card + T.card + 1)^7 ≤ (C * ∑ j : Fin k, (n - (I j).card))^7 * n) := by
  classical
  obtain ⟨p,large⟩ := polynomial_parameters C
  apply transfer C (graph p) (fun v => match v with | .inl _ => false | .inr _ => true) (blocks p)
  · exact ⟨p.u^2, regular_degree p⟩
  · rintro (a|a) (b|b) h <;> first | exact h.elim | exact Bool.false_ne_true | exact Ne.symm Bool.false_ne_true
  · exact no_four p
  · rw [label_count]; omega
  · exact blocks_independent p
  · exact blocks_cover p
  · exact blocks_cocover p
  · exact blocks_miss_two p
  · exact blocks_nonedges p
  · exact large

end PEqualNP.Outside.L_meta_3577_aux

theorem PEqualNP.Outside.L_meta_3577 : ¬ (∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (side : Fin n → Bool) (I : Fin k → Finset (Fin n)), (∀ a b : Fin n, G.Adj a b → side a ≠ side b) → (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → 2 ≤ k → (∀ j : Fin k, ∀ a ∈ I j, ∀ b ∈ I j, ¬ G.Adj a b) → (∀ v : Fin n, ∃ j : Fin k, v ∈ I j) → (∀ v : Fin n, ∃ j : Fin k, v ∉ I j) → (∀ j : Fin k, (I j).card + 2 ≤ n) → (∀ a b : Fin n, a ≠ b → ¬ G.Adj a b → ∃ j : Fin k, a ∈ I j ∧ b ∈ I j) → ∃ T : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) ∧ G.edgeFinset.card + T.card + 1 ≤ ∑ j : Fin k, (n - (I j).card)) := by
  intro assertion
  apply PEqualNP.Outside.L_meta_3577_aux.regular_seventh_power_obstruction 1
  intro n k G dec side I _regular part square hk ind inside outside miss nonedge
  obtain ⟨T,cover,bound⟩ := assertion n k G side I part square hk ind inside outside miss nonedge
  refine ⟨T,cover,?_⟩
  rw [one_mul]
  have hn := miss ⟨0,by omega⟩
  exact (Nat.pow_le_pow_left bound 7).trans (Nat.le_mul_of_pos_right _ (by omega))
