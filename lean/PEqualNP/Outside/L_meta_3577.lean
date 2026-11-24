import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3577_aux

abbrev F := ZMod 65537
abbrev Ix := Fin 128
abbrev Left := F × F × F
abbrev Right := (Ix × Ix) × (F × F)
abbrev V := Sum Left Right

instance : Fact (Nat.Prime 65537) := ⟨by norm_num⟩

def coordA (i : Ix) : F := (i.val : F)
def coordB (j : Ix) : F := ((128 + j.val : Nat) : F)

def val (u : Left) (x : F) : F := u.1 + u.2.1*x + u.2.2*x^2
def atPair (u : Left) (ij : Ix × Ix) : F × F :=
  (val u (coordA ij.1), val u (coordB ij.2))
def inc (u : Left) (w : Right) : Prop := atPair u w.1 = w.2
instance (u : Left) (w : Right) : Decidable (inc u w) := inferInstanceAs (Decidable (_ = _))

def graph : SimpleGraph V :=
  { Adj := fun a b => match a, b with
      | .inl u, .inr w => inc u w
      | .inr w, .inl u => inc u w
      | _, _ => False
    symm := ⟨by rintro (_|_) (_|_) h <;> exact h⟩
    loopless := ⟨by rintro (_|_) <;> simp⟩ }

instance : DecidableRel graph.Adj := fun a b => by
  rcases a with u|w <;> rcases b with v|z <;> first | exact inferInstanceAs (Decidable (inc _ _)) | exact isFalse id

private theorem cast_inj {a b : Nat} (ha : a < 65537) (hb : b < 65537)
    (h : (a : F) = (b : F)) : a = b := by
  have e := congrArg ZMod.val h
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using e

theorem coordA_inj : Function.Injective coordA := by
  intro i j h
  exact Fin.ext (cast_inj (by have := i.isLt; omega) (by have := j.isLt; omega) h)

theorem coordB_inj : Function.Injective coordB := by
  intro i j h
  have e := cast_inj (a := 128+i.val) (b := 128+j.val) (by have := i.isLt; omega) (by have := j.isLt; omega) h
  exact Fin.ext (by omega)

theorem coord_disjoint (i j : Ix) : coordA i ≠ coordB j := by
  intro h
  have e := cast_inj (a := i.val) (b := 128+j.val) (by have := i.isLt; omega) (by have := j.isLt; omega) h
  have il := i.isLt
  omega

private theorem three_points {u v : Left} {a b c : F}
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (ea : val u a = val v a) (eb : val u b = val v b) (ec : val u c = val v c) : u = v := by
  dsimp only [val] at ea eb ec
  have ab0 : (b-a)*((u.2.1-v.2.1)+(u.2.2-v.2.2)*(a+b)) = 0 := by linear_combination eb - ea
  have ac0 : (c-a)*((u.2.1-v.2.1)+(u.2.2-v.2.2)*(a+c)) = 0 := by linear_combination ec - ea
  have ab1 := (mul_eq_zero.mp ab0).resolve_left (sub_ne_zero.mpr ab.symm)
  have ac1 := (mul_eq_zero.mp ac0).resolve_left (sub_ne_zero.mpr ac.symm)
  have bc0 : (b-c)*(u.2.2-v.2.2) = 0 := by linear_combination ab1 - ac1
  have uc := sub_eq_zero.mp ((mul_eq_zero.mp bc0).resolve_left (sub_ne_zero.mpr bc))
  rw [uc,sub_self,zero_mul,add_zero] at ab1
  have ub := sub_eq_zero.mp ab1
  rw [uc,ub] at ea
  exact Prod.ext (by linear_combination ea) (Prod.ext ub uc)

theorem no_rectangle {u v : Left} {w z : Right}
    (huw : inc u w) (hvw : inc v w) (huz : inc u z) (hvz : inc v z) : u = v ∨ w = z := by
  have e₁ := congrArg Prod.fst (huw.trans hvw.symm)
  have e₂ := congrArg Prod.snd (huw.trans hvw.symm)
  have e₃ := congrArg Prod.fst (huz.trans hvz.symm)
  have e₄ := congrArg Prod.snd (huz.trans hvz.symm)
  by_cases a : w.1.1 = z.1.1
  · by_cases b : w.1.2 = z.1.2
    · right
      have ij : w.1 = z.1 := Prod.ext a b
      exact Prod.ext ij (huw.symm.trans ((congrArg (atPair u) ij).trans huz))
    · left
      exact three_points (coord_disjoint _ _) (coord_disjoint _ _) (coordB_inj.ne b) e₁ e₂ e₄
  · left
    exact three_points (coord_disjoint _ _) (coordA_inj.ne a) (coord_disjoint _ _).symm e₁ e₂ e₃

theorem no_four (a b c d : V) (ac : a ≠ c) (bd : b ≠ d) :
    ¬ (graph.Adj a b ∧ graph.Adj b c ∧ graph.Adj c d ∧ graph.Adj d a) := by
  rintro ⟨h₁,h₂,h₃,h₄⟩
  rcases a with a|a <;> rcases b with b|b <;> rcases c with c|c <;> rcases d with d|d <;>
    try contradiction
  · rcases no_rectangle h₁ h₂ h₄ h₃ with h|h
    · exact ac (congrArg Sum.inl h)
    · exact bd (congrArg Sum.inr h)
  · rcases no_rectangle h₁ h₄ h₂ h₃ with h|h
    · exact bd (congrArg Sum.inl h)
    · exact ac (congrArg Sum.inr h)


end PEqualNP.Outside.L_meta_3577_aux

namespace PEqualNP.Outside.L_meta_3577_aux
section
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
end

private theorem pairCard (m : Nat) : Fintype.card (Fin m × Fin m) = m^2 := by
  simp [Fintype.card_prod,pow_two]

theorem count_edges : Fintype.card Left * 128^2 ≤ graph.edgeFinset.card := by
  exact edge_lower (I := Ix × Ix) (fun u ij => (ij, atPair u ij))
    Prod.fst (fun _ _ => rfl) graph (fun _ _ => rfl) (128^2) (pairCard 128)

end PEqualNP.Outside.L_meta_3577_aux

namespace PEqualNP.Outside.L_meta_3577_aux

abbrev Label := Bool ⊕ (Bool × Ix × Fin 17 × Bool)

def symbolBit (x : F) (j : Fin 17) : Bool := x.val.testBit j.val

theorem separate_symbols {x y : F} (ne : x ≠ y) : ∃ j : Fin 17, symbolBit x j ≠ symbolBit y j := by
  classical
  by_contra! h
  apply ne
  apply ZMod.val_injective 65537
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 17
  · exact h ⟨j,hj⟩
  · have hp : 2^17 ≤ 2^j := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
    have xs := ZMod.val_lt x
    have ys := ZMod.val_lt y
    norm_num at hp
    rw [Nat.testBit_lt_two_pow (by omega : x.val < 2^j), Nat.testBit_lt_two_pow (by omega : y.val < 2^j)]

def wordSymbol (u : Left) (half : Bool) (i : Ix) : F :=
  if half then val u (coordB i) else val u (coordA i)

def rightCoord (r : Right) (half : Bool) : Ix := if half then r.1.2 else r.1.1

def rightSymbol (r : Right) (half : Bool) : F := if half then r.2.2 else r.2.1

theorem inc_symbols (u : Left) (r : Right) : inc u r ↔ ∀ half,
    wordSymbol u half (rightCoord r half) = rightSymbol r half := by
  constructor
  · intro h half
    cases half
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  · intro h
    exact Prod.ext (h false) (h true)

def inBlock : Label → V → Prop
  | .inl side, .inl _ => side = false
  | .inl side, .inr _ => side = true
  | .inr (h,i,j,pol), .inl u => symbolBit (wordSymbol u h i) j = pol
  | .inr (h,i,j,pol), .inr r => rightCoord r h = i ∧ symbolBit (rightSymbol r h) j ≠ pol

noncomputable def blocks (j : Label) : Finset V := by
  classical
  exact Finset.univ.filter (inBlock j)

theorem mem_blocks (j : Label) (v : V) : v ∈ blocks j ↔ inBlock j v := by
  classical
  simp only [blocks,Finset.mem_filter,Finset.mem_univ,true_and]

private theorem cross_independent (j : Label) {u : Left} {r : Right}
    (hu : inBlock j (.inl u)) (hr : inBlock j (.inr r)) : ¬ inc u r := by
  rcases j with h | ⟨h,i,bit,pol⟩
  · change h = false at hu
    change h = true at hr
    simp [hu] at hr
  · change symbolBit (wordSymbol u h i) bit = pol at hu
    change rightCoord r h = i ∧ symbolBit (rightSymbol r h) bit ≠ pol at hr
    intro adj
    have eq := (inc_symbols u r).mp adj h
    rw [hr.1] at eq
    exact hr.2 ((congrArg (fun s => symbolBit s bit) eq).symm.trans hu)

section AbstractBlocks

private theorem abstract_independent (B : Label → Finset V) (memB : ∀ j v, v ∈ B j ↔ inBlock j v)
    (j : Label) (a : V) (ha : a ∈ B j) (b : V) (hb : b ∈ B j) :
    ¬ graph.Adj a b := by
  rw [memB] at ha hb
  cases a with
  | inl u => cases b with
             | inl u' => exact id
             | inr r => exact cross_independent j ha hb
  | inr r => cases b with
             | inl u => exact cross_independent j hb ha
             | inr r' => exact id

private theorem abstract_cover (B : Label → Finset V) (memB : ∀ j v, v ∈ B j ↔ inBlock j v)
    (v : V) : ∃ j : Label, v ∈ B j := by
  cases v with
  | inl u => exact ⟨.inl false,(memB _ _).mpr rfl⟩
  | inr r => exact ⟨.inl true,(memB _ _).mpr rfl⟩

private theorem abstract_cocover (B : Label → Finset V) (memB : ∀ j v, v ∈ B j ↔ inBlock j v)
    (v : V) : ∃ j : Label, v ∉ B j := by
  cases v with
  | inl u => exact ⟨.inl true, fun h => Bool.noConfusion ((memB _ _).mp h)⟩
  | inr r => exact ⟨.inl false, fun h => Bool.noConfusion ((memB _ _).mp h)⟩

private theorem cross_nonedge (B : Label → Finset V) (memB : ∀ j v, v ∈ B j ↔ inBlock j v)
    (u : Left) (r : Right) (h : ¬ inc u r) :
    ∃ j : Label, Sum.inl u ∈ B j ∧ Sum.inr r ∈ B j := by
  classical
  rw [inc_symbols] at h
  push Not at h
  obtain ⟨half,ne⟩ := h
  obtain ⟨j,bitne⟩ := separate_symbols ne
  let i := rightCoord r half
  let pol := symbolBit (wordSymbol u half i) j
  refine ⟨Sum.inr (half,i,j,pol),(memB _ _).mpr rfl,(memB _ _).mpr ?_⟩
  exact ⟨rfl, Ne.symm bitne⟩

private theorem abstract_nonedges (B : Label → Finset V) (memB : ∀ j v, v ∈ B j ↔ inBlock j v)
    (a b : V) (_ne : a ≠ b) (h : ¬ graph.Adj a b) :
    ∃ j : Label, a ∈ B j ∧ b ∈ B j := by
  cases a with
  | inl u => cases b with
             | inl u' => exact ⟨.inl false, (memB _ _).mpr rfl, (memB _ _).mpr rfl⟩
             | inr r => exact cross_nonedge B memB u r h
  | inr r => cases b with
             | inr r' => exact ⟨.inl true, (memB _ _).mpr rfl, (memB _ _).mpr rfl⟩
             | inl u =>
                 obtain ⟨j,hj,hk⟩ := cross_nonedge B memB u r h
                 exact ⟨j,hk,hj⟩

private def extraRight (i : Ix) (s : F) : Right := ((i,i),(0,s))
private def extraLeft (s : F) : Left := (0,0,s)
private theorem differentRight (i : Ix) : (Sum.inr (extraRight i 0) : V) ≠ Sum.inr (extraRight i 1) :=
  fun h => zero_ne_one (congrArg (fun x : Right => x.2.2) (Sum.inr.inj h))
private theorem differentLeft : (Sum.inl (extraLeft 0) : V) ≠ Sum.inl (extraLeft 1) :=
  fun h => zero_ne_one (congrArg (fun x : Left => x.2.2) (Sum.inl.inj h))

private theorem missesPair (B : Label → Finset V) (memB : ∀ j v, v ∈ B j ↔ inBlock j v)
    (j : Label) : ∃ a b : V, a ≠ b ∧ a ∉ B j ∧ b ∉ B j := by
  rcases j with (_ | _) | ⟨h,i,bit,pol⟩
  · exact ⟨.inr (extraRight 0 0), .inr (extraRight 0 1), differentRight 0,
      fun x => Bool.noConfusion ((memB _ _).mp x), fun x => Bool.noConfusion ((memB _ _).mp x)⟩
  · exact ⟨.inl (extraLeft 0), .inl (extraLeft 1), differentLeft,
      fun x => Bool.noConfusion ((memB _ _).mp x), fun x => Bool.noConfusion ((memB _ _).mp x)⟩
  · let other : Ix := if i = 0 then 1 else 0
    have diff : other ≠ i := by
      by_cases hi : i = 0
      · subst i; decide +revert
      · simpa [other,hi] using Ne.symm hi
    have omitted (s : F) : Sum.inr (extraRight other s) ∉ B (Sum.inr (h,i,bit,pol)) := by
      intro hn
      have hin := ((memB _ _).mp hn).1
      cases h <;> exact diff hin
    exact ⟨.inr (extraRight other 0), .inr (extraRight other 1), differentRight other,omitted _,omitted _⟩

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

private theorem abstract_miss_two (B : Label → Finset V) (memB : ∀ j v, v ∈ B j ↔ inBlock j v)
    (j : Label) : (B j).card + 2 ≤ Fintype.card V := by
  obtain ⟨a,b,ne,ha,hb⟩ := missesPair B memB j
  exact card_bound_two_missing (B j) a b ne ha hb

end AbstractBlocks

def IsIndependentFamily (B : Label → Finset V) : Prop :=
  ∀ j : Label, ∀ a ∈ B j, ∀ b ∈ B j, ¬ graph.Adj a b

theorem blocks_independent : IsIndependentFamily blocks := abstract_independent blocks mem_blocks

theorem blocks_cover (v : V) : ∃ j : Label, v ∈ blocks j := abstract_cover blocks mem_blocks v

theorem blocks_cocover (v : V) : ∃ j : Label, v ∉ blocks j := abstract_cocover blocks mem_blocks v

theorem blocks_nonedges (a b : V) (ne : a ≠ b) (h : ¬ graph.Adj a b) :
    ∃ j : Label, a ∈ blocks j ∧ b ∈ blocks j := abstract_nonedges blocks mem_blocks a b ne h

theorem blocks_miss_two (j : Label) : (blocks j).card + 2 ≤ Fintype.card V :=
  abstract_miss_two blocks mem_blocks j

theorem label_count : Fintype.card Label = 8706 := by norm_num [Label,Ix,Fintype.card_prod,Fintype.card_sum]

theorem blocks_cosize : (∑ j : Label, (Fintype.card V - (blocks j).card)) ≤ 8706 * Fintype.card V := by
  calc
    _ ≤ ∑ _j : Label, Fintype.card V := Finset.sum_le_sum (fun _ _ => Nat.sub_le _ _)
    _ = _ := by simp

end PEqualNP.Outside.L_meta_3577_aux

namespace PEqualNP.Outside.L_meta_3577_aux

theorem vertex_number :
    8706 * Fintype.card V < Fintype.card Left * 128^2 := by
  rw [show Fintype.card V = Fintype.card Left + Fintype.card Right from Fintype.card_sum]
  have hl : Fintype.card Left = 65537 * (65537 * 65537) := by
    rw [Fintype.card_prod (α := F) (β := F × F), Fintype.card_prod (α := F) (β := F), ZMod.card]
  have hr : Fintype.card Right = (128 * 128) * (65537 * 65537) := by
    rw [Fintype.card_prod (α := Ix × Ix) (β := F × F), Fintype.card_prod (α := Ix) (β := Ix),
      Fintype.card_prod (α := F) (β := F), Fintype.card_fin, ZMod.card]
  rw [hl,hr]
  decide

theorem gapArithmetic {K : Type*} [Fintype K] (count : Fintype.card K = 8706) :
    Fintype.card K * Fintype.card V < graph.edgeFinset.card := by
  rw [count]
  exact vertex_number.trans_le count_edges

end PEqualNP.Outside.L_meta_3577_aux

namespace PEqualNP.Outside.L_meta_3577_aux

theorem transfer {V K : Type*} [Fintype V] [Fintype K] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (side : V → Bool) (I : K → Finset V)
    (part : ∀ a b, G.Adj a b → side a ≠ side b)
    (square : ∀ a b c d : V, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (hk : 2 ≤ Fintype.card K)
    (ind : ∀ j, ∀ a ∈ I j, ∀ b ∈ I j, ¬ G.Adj a b)
    (inside : ∀ v, ∃ j, v ∈ I j)
    (outside : ∀ v, ∃ j, v ∉ I j)
    (miss : ∀ j, (I j).card + 2 ≤ Fintype.card V)
    (nonedge : ∀ a b, a ≠ b → ¬ G.Adj a b → ∃ j, a ∈ I j ∧ b ∈ I j)
    (large : Fintype.card K * Fintype.card V < G.edgeFinset.card) :
    ¬ (∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (side : Fin n → Bool) (I : Fin k → Finset (Fin n)), (∀ a b : Fin n, G.Adj a b → side a ≠ side b) → (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → 2 ≤ k → (∀ j : Fin k, ∀ a ∈ I j, ∀ b ∈ I j, ¬ G.Adj a b) → (∀ v : Fin n, ∃ j : Fin k, v ∈ I j) → (∀ v : Fin n, ∃ j : Fin k, v ∉ I j) → (∀ j : Fin k, (I j).card + 2 ≤ n) → (∀ a b : Fin n, a ≠ b → ¬ G.Adj a b → ∃ j : Fin k, a ∈ I j ∧ b ∈ I j) → ∃ T : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) ∧ G.edgeFinset.card + T.card + 1 ≤ ∑ j : Fin k, (n - (I j).card)) := by
  classical
  intro hall
  let e := Fintype.equivFin V
  let f := Fintype.equivFin K
  let H := G.comap e.symm
  let J := fun j : Fin (Fintype.card K) => (I (f.symm j)).map e.toEmbedding
  have mem (j v) : v ∈ J j ↔ e.symm v ∈ I (f.symm j) := by
    simp [J]
  obtain ⟨T,_,bound⟩ := hall _ _ H (fun v => side (e.symm v)) J
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
  omega

end PEqualNP.Outside.L_meta_3577_aux

open PEqualNP.Outside.L_meta_3577_aux

theorem PEqualNP.Outside.L_meta_3577 : ¬ (∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (side : Fin n → Bool) (I : Fin k → Finset (Fin n)), (∀ a b : Fin n, G.Adj a b → side a ≠ side b) → (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → 2 ≤ k → (∀ j : Fin k, ∀ a ∈ I j, ∀ b ∈ I j, ¬ G.Adj a b) → (∀ v : Fin n, ∃ j : Fin k, v ∈ I j) → (∀ v : Fin n, ∃ j : Fin k, v ∉ I j) → (∀ j : Fin k, (I j).card + 2 ≤ n) → (∀ a b : Fin n, a ≠ b → ¬ G.Adj a b → ∃ j : Fin k, a ∈ I j ∧ b ∈ I j) → ∃ T : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → a ∈ T ∨ b ∈ T) ∧ G.edgeFinset.card + T.card + 1 ≤ ∑ j : Fin k, (n - (I j).card)) := by
  classical
  let side : V → Bool := Sum.elim (fun _ => false) (fun _ => true)
  apply transfer graph side blocks _ no_four (by rw [label_count]; decide)
    blocks_independent blocks_cover blocks_cocover blocks_miss_two
    blocks_nonedges (gapArithmetic label_count)
  rintro (a | a) (b | b) h <;> first | exact h.elim | exact Bool.false_ne_true | exact Ne.symm Bool.false_ne_true
