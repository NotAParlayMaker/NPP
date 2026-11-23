import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_252_aux

namespace FormulaRectangleBound

open PEqualNP.MetaComplexity

def Positive {n : ℕ} : DMFormula n → Prop
  | .lit _ b => b = true
  | .and f g | .or f g => Positive f ∧ Positive g

end FormulaRectangleBound

-- Route each positive and negative input pair to a leaf. Its variable separates the two inputs.
namespace FormulaKWPartition

open PEqualNP.MetaComplexity FormulaRectangleBound

def label {n : ℕ} : (f : DMFormula n) → Fin f.leaves → Fin n
  | .lit i _ => fun _ => i
  | .and f g => Fin.addCases (label f) (label g)
  | .or f g => Fin.addCases (label f) (label g)

def rowPath {n : ℕ} : (f : DMFormula n) → (Fin n → Bool) → Fin f.leaves → Prop
  | .lit _ _, _ => fun _ => True
  | .and f g, x => Fin.addCases (rowPath f x) (rowPath g x)
  | .or f g, x => Fin.addCases
      (fun i => f.eval x = true ∧ rowPath f x i)
      (fun i => f.eval x = false ∧ rowPath g x i)

def colPath {n : ℕ} : (f : DMFormula n) → (Fin n → Bool) → Fin f.leaves → Prop
  | .lit _ _, _ => fun _ => True
  | .and f g, y => Fin.addCases
      (fun i => f.eval y = false ∧ colPath f y i)
      (fun i => f.eval y = true ∧ colPath g y i)
  | .or f g, y => Fin.addCases (colPath f y) (colPath g y)

def route {n : ℕ} : (f : DMFormula n) → (Fin n → Bool) → (Fin n → Bool) → Fin f.leaves
  | .lit _ _, _, _ => (0 : Fin 1)
  | .and f g, x, y => if f.eval y then Fin.natAdd _ (route g x y)
      else Fin.castAdd _ (route f x y)
  | .or f g, x, y => if f.eval x then Fin.castAdd _ (route f x y)
      else Fin.natAdd _ (route g x y)

private theorem cast_same {m n : ℕ} (a b : Fin m) :
    Fin.castAdd n a = Fin.castAdd n b ↔ a = b := by simp [Fin.ext_iff]

private theorem nat_same {m n : ℕ} (a b : Fin n) :
    Fin.natAdd m a = Fin.natAdd m b ↔ a = b := by simp [Fin.ext_iff]

private theorem separate {m n : ℕ} (a : Fin m) (b : Fin n) :
    Fin.castAdd n a ≠ Fin.natAdd m b := by
  simp only [ne_eq,Fin.ext_iff,Fin.val_castAdd,Fin.val_natAdd]
  omega

theorem reaches_iff {n : ℕ} (f : DMFormula n) (x y : Fin n → Bool) (i : Fin f.leaves) :
    rowPath f x i ∧ colPath f y i ↔ i = route f x y := by
  induction f with
  | lit j p =>
    exact ⟨fun _ => Subsingleton.elim (α := Fin 1) _ _, fun _ => ⟨trivial,trivial⟩⟩
  | and f g left right =>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · cases h : f.eval y <;> simp [rowPath,colPath,route,h,left]
      all_goals first | exact (cast_same _ _).symm | exact separate _ _
    · cases h : f.eval y <;> simp [rowPath,colPath,route,h,right]
      all_goals first | exact (nat_same _ _).symm | exact Ne.symm (separate _ _)
  | or f g left right =>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · cases h : f.eval x <;> simp [rowPath,colPath,route,h,left]
      all_goals first | exact (cast_same _ _).symm | exact separate _ _
    · cases h : f.eval x <;> simp [rowPath,colPath,route,h,right]
      all_goals first | exact (nat_same _ _).symm | exact Ne.symm (separate _ _)

theorem row_label {n : ℕ} (f : DMFormula n) (hf : Positive f)
    (x : Fin n → Bool) (hx : f.eval x = true) (i : Fin f.leaves) :
    rowPath f x i → x (label f i) = true := by
  induction f with
  | lit j p =>
    obtain rfl : p = true := hf
    simpa [rowPath,label,DMFormula.eval] using hx
  | and f g left right =>
    obtain ⟨h₁,h₂⟩ := Bool.and_eq_true_iff.mp hx
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [rowPath,label] using left hf.1 h₁ j
    · simpa [rowPath,label] using right hf.2 h₂ j
  | or f g left right =>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [rowPath,label,Fin.addCases_left]
      rintro ⟨he,hp⟩
      exact left hf.1 he j hp
    · simp only [rowPath,label,Fin.addCases_right]
      rintro ⟨he,hp⟩
      exact right hf.2 (by simpa [DMFormula.eval,he] using hx) j hp

theorem col_label {n : ℕ} (f : DMFormula n) (hf : Positive f)
    (y : Fin n → Bool) (hy : f.eval y = false) (i : Fin f.leaves) :
    colPath f y i → y (label f i) = false := by
  induction f with
  | lit j p =>
    obtain rfl : p = true := hf
    simpa [colPath,label,DMFormula.eval] using hy
  | and f g left right =>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [colPath,label,Fin.addCases_left]
      rintro ⟨he,hp⟩
      exact left hf.1 he j hp
    · simp only [colPath,label,Fin.addCases_right]
      rintro ⟨he,hp⟩
      exact right hf.2 (by simpa [DMFormula.eval,he] using hy) j hp
  | or f g left right =>
    obtain ⟨h₁,h₂⟩ := Bool.or_eq_false_iff.mp hy
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [colPath,label] using left hf.1 h₁ j
    · simpa [colPath,label] using right hf.2 h₂ j

end FormulaKWPartition

-- Two private vertices of a triangle need at least three leaf occurrences between them.
namespace PendantPrivate

open FormulaKWPartition FormulaRectangleBound PEqualNP.MetaComplexity

variable {n : ℕ}

def pair (a b : Fin n) (i : Fin n) : Bool := decide (i = a ∨ i = b)

def single (a : Fin n) (i : Fin n) : Bool := decide (i = a)

def occurrences (f : DMFormula n) (a : Fin n) : Finset (Fin f.leaves) :=
  Finset.univ.filter fun i => label f i = a

def reached (f : DMFormula n) (a : Fin n) (x y : Fin n → Bool) : Prop :=
  label f (route f x y) = a

def Computes (f : DMFormula n) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ x : Fin n → Bool, f.eval x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

private theorem pairTrue {G : SimpleGraph (Fin n)} {f : DMFormula n} (he : Computes f G)
    {a b : Fin n} (hab : G.Adj a b) : f.eval (pair a b) = true :=
  (he _).mpr ⟨a, b, hab, by simp [pair], by simp [pair]⟩

private theorem singleFalse {G : SimpleGraph (Fin n)} {f : DMFormula n} (he : Computes f G)
    (v : Fin n) : f.eval (single v) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨i, j, hip, hi, hj⟩ := (he _).mp h
  simp only [single, decide_eq_true_eq] at hi hj
  exact hip.ne (hi.trans hj.symm)

theorem forced {G : SimpleGraph (Fin n)} {f : DMFormula n} (hf : Positive f)
    (he : Computes f G) {a b : Fin n} (hab : G.Adj a b)
    (y : Fin n → Bool) (hneg : f.eval y = false) (hb : y b = true) :
    reached f a (pair a b) y := by
  let i := route f (pair a b) y
  obtain ⟨hr, hc⟩ := (reaches_iff f (pair a b) y i).mpr rfl
  have hx := row_label f hf _ (pairTrue he hab) i hr
  have hy := col_label f hf _ hneg i hc
  rcases (show label f i = a ∨ label f i = b from of_decide_eq_true hx) with h | h
  · exact h
  · rw [h, hb] at hy
    contradiction

theorem occursOnEdge {G : SimpleGraph (Fin n)} {f : DMFormula n} (hf : Positive f)
    (he : Computes f G) {a b : Fin n} (hab : G.Adj a b) : (occurrences f a).Nonempty := by
  have h := forced hf he hab (single b) (singleFalse he b) (by simp [single])
  exact ⟨route f (pair a b) (single b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

private theorem transfer {f : DMFormula n} {a : Fin n} (h : (occurrences f a).card ≤ 1)
    {x x' y y' : Fin n → Bool} (hxy : reached f a x y) (hxy' : reached f a x' y') :
    reached f a x' y := by
  let i := route f x y
  let j := route f x' y'
  have hi : i ∈ occurrences f a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩
  have hj : j ∈ occurrences f a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy'⟩
  have ij : i = j := Finset.card_le_one.mp h i hi j hj
  have hcol := ((reaches_iff f x y i).mpr rfl).2
  have hrow := ((reaches_iff f x' y' j).mpr rfl).1
  have hroute := (reaches_iff f x' y i).mp ⟨ij ▸ hrow, hcol⟩
  exact (congrArg (label f) hroute).symm.trans hxy

theorem identicalRows {G : SimpleGraph (Fin n)} {f : DMFormula n} (hf : Positive f)
    (he : Computes f G) {a b c : Fin n} (hab : G.Adj a b) (hac : G.Adj a c)
    (ha : (occurrences f a).card ≤ 1) (y : Fin n → Bool) :
    reached f a (pair a b) y ↔ reached f a (pair a c) y := by
  have hb := forced hf he hab (single b) (singleFalse he b) (by simp [single])
  have hc := forced hf he hac (single c) (singleFalse he c) (by simp [single])
  exact ⟨fun h => transfer ha h hc, fun h => transfer ha h hb⟩

theorem incompatiblePrivate {G : SimpleGraph (Fin n)} {f : DMFormula n} (hf : Positive f)
    (he : Computes f G) {a b c : Fin n} (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    ¬ ((occurrences f a).card ≤ 1 ∧ (occurrences f b).card ≤ 1) := by
  rintro ⟨onceA, onceB⟩
  let y := single c
  have neg := singleFalse he c
  have sel : y c = true := by simp [y, single]
  have hA := (identicalRows hf he hab hac onceA y).mpr (forced hf he hac y neg sel)
  have hB := (identicalRows hf he hab.symm hbc onceB y).mpr (forced hf he hbc y neg sel)
  have same : pair b a = pair a b := by funext i; simp [pair, or_comm]
  rw [same] at hB
  exact hab.ne (hA.symm.trans hB)

theorem threePrivate {G : SimpleGraph (Fin n)} {f : DMFormula n} (hf : Positive f)
    (he : Computes f G) {a b c : Fin n} (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    3 ≤ (occurrences f a).card + (occurrences f b).card := by
  have ha := Finset.card_pos.mpr (occursOnEdge hf he hab)
  have hb := Finset.card_pos.mpr (occursOnEdge hf he hab.symm)
  have h := incompatiblePrivate hf he hab hac hbc
  omega

theorem forcedTaggedRow {G : SimpleGraph (Fin n)} {f : DMFormula n} (hf : Positive f)
    (he : Computes f G) {a b c : Fin n} (hab : G.Adj a b) (hac : G.Adj a c)
    (ha : (occurrences f a).card ≤ 1) (y : Fin n → Bool) (hneg : f.eval y = false)
    (hb : y b = true) : reached f a (pair a c) y :=
  (identicalRows hf he hab hac ha y).mp (forced hf he hab y hneg hb)

end PendantPrivate

namespace PendantCover

variable {V I : Type} [Fintype I] [DecidableEq V]

def centers (apex : I → V) : Finset V := Finset.univ.image apex

def triangleEdge (c a b x y : V) : Prop :=
  s(x,y) = s(c,a) ∨ s(x,y) = s(c,b) ∨ s(x,y) = s(a,b)

def Covers (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ x y, G.Adj x y → x ∈ S ∨ y ∈ S

def CoversUnmarked (H : SimpleGraph V) (apex : I → V) (U : Finset V) : Prop :=
  ∀ x y, H.Adj x y → x ∉ centers apex → y ∉ centers apex → x ∈ U ∨ y ∈ U

theorem coverFromCore (G H : SimpleGraph V) (apex a b : I → V) (U : Finset V)
    (decomp : ∀ x y, G.Adj x y → H.Adj x y ∨ ∃ i, triangleEdge (apex i) (a i) (b i) x y)
    (hU : CoversUnmarked H apex U) :
    ∃ S : Finset V, Covers G S ∧ S.card ≤ Fintype.card I + (centers apex).card + U.card := by
  classical
  let privateA : Finset V := Finset.univ.image a
  let S := (privateA ∪ centers apex) ∪ U
  have cen (i : I) : apex i ∈ S := by simp [S,centers]
  have prv (i : I) : a i ∈ S := by simp [S,privateA]
  have lift (y : V) (hy : y ∈ centers apex ∨ y ∈ U) : y ∈ S := by
    simpa [S,or_assoc] using (show y ∈ privateA ∨ y ∈ centers apex ∨ y ∈ U from Or.inr hy)
  refine ⟨S, ?_, ?_⟩
  · intro x y hxy
    rcases decomp x y hxy with core | ⟨i, h⟩
    · by_cases hx : x ∈ centers apex
      · exact Or.inl (lift x (Or.inl hx))
      by_cases hy : y ∈ centers apex
      · exact Or.inr (lift y (Or.inl hy))
      exact (hU x y core hx hy).imp (fun h => lift _ (Or.inr h)) (fun h => lift _ (Or.inr h))
    · rcases h with h | h | h <;> rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
        first | exact Or.inl (cen i) | exact Or.inr (cen i) | exact Or.inl (prv i) | exact Or.inr (prv i)
  · have hp : privateA.card ≤ Fintype.card I :=
      (Finset.card_image_le.trans_eq (Finset.card_univ (α := I)))
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right hp _)) _)

end PendantCover

namespace PendantDecomposition

structure Data {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] where
  t : ℕ
  H : SimpleGraph (Fin n)
  hdec : DecidableRel H.Adj
  apex : Fin t → Fin n
  p : Fin t × Bool → Fin n
  inj : Function.Injective p
  apart : ∀ z, p z ∉ PendantCover.centers apex
  coreAdj : ∀ x y, H.Adj x y → G.Adj x y
  privateOffCore : ∀ x y, H.Adj x y → ∀ z, x ≠ p z
  spoke : ∀ i b, G.Adj (apex i) (p (i,b))
  base : ∀ i, G.Adj (p (i,false)) (p (i,true))
  neighbors : ∀ i b v, G.Adj (p (i,b)) v ↔ v = apex i ∨ v = p (i,!b)
  decomp : ∀ x y, G.Adj x y → H.Adj x y ∨
    ∃ i, PendantCover.triangleEdge (apex i) (p (i,false)) (p (i,true)) x y
  triFree : ∀ a b c, H.Adj a b → H.Adj b c → H.Adj c a → False
  square : ∀ a b c d, a ≠ c → b ≠ d → H.Adj a b → H.Adj b c → H.Adj c d → ¬ H.Adj d a
  edgeCount : letI := hdec; G.edgeFinset.card = H.edgeFinset.card + 3 * t



end PendantDecomposition

local instance coreDecidable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (D : PendantDecomposition.Data G) : DecidableRel D.H.Adj := D.hdec

namespace CubicStarCapacity

variable {V : Type} [Fintype V] [DecidableEq V]

def negativeSet (G : SimpleGraph V) (g : Sym2 V) (i : V) : Prop :=
  i ∉ g ∧ ∃ j ∈ g, G.Adj i j

private theorem edgeAdj (G : SimpleGraph V) (e : Sym2 V) :
    e ∈ G.edgeSet → ∀ i j : V, i ∈ e → j ∈ e → i ≠ j → G.Adj i j := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    intro he i j hi hj hne
    change G.Adj a b at he
    rcases Sym2.mem_iff.mp hi with rfl | rfl <;> rcases Sym2.mem_iff.mp hj with rfl | rfl
    all_goals first | exact (hne rfl).elim | exact he | exact he.symm

theorem negativeIndependent (G : SimpleGraph V)
    (triangle : ∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a)
    (square : ∀ a b c d, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬G.Adj d a)
    (g : Sym2 V) (hg : g ∈ G.edgeSet) (x y : V)
    (hx : negativeSet G g x) (hy : negativeSet G g y) : ¬G.Adj x y := by
  intro xy
  obtain ⟨xout, p, hp, xp⟩ := hx
  obtain ⟨yout, q, hq, yq⟩ := hy
  by_cases same : p = q
  · subst q
    exact triangle x y p xy yq xp.symm
  · exact square p x y q (fun h => yout (h ▸ hp)) (fun h => xout (h ▸ hq))
      xp.symm xy yq (edgeAdj G g hg p q hp hq same).symm

end CubicStarCapacity

-- Add the local bounds. Each core edge has a single owner, and its owners cover the unmarked core.
namespace PendantCount

open PEqualNP.MetaComplexity FormulaRectangleBound PendantPrivate

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

def bad (D : PendantDecomposition.Data G) (f : DMFormula n) : Finset (Fin D.t) :=
  Finset.univ.filter fun i => (occurrences f (D.p (i,false))).card + (occurrences f (D.p (i,true))).card = 3

def tag (D : PendantDecomposition.Data G) (f : DMFormula n) (i : Fin D.t) : Bool :=
  decide ((occurrences f (D.p (i,false))).card = 1)

theorem badOnce (D : PendantDecomposition.Data G) (f : DMFormula n) (hf : Positive f) (ev : Computes f G)
    {i : Fin D.t} (hi : i ∈ bad D f) : (occurrences f (D.p (i,!(tag D f i)))).card ≤ 1 := by
  have hb := (Finset.mem_filter.mp hi).2
  have h := Finset.card_pos.mpr (occursOnEdge hf ev (D.base i))
  by_cases one : (occurrences f (D.p (i,false))).card = 1
  · simp [tag,one]
  · simp [tag,one]
    omega

theorem aggregate (D : PendantDecomposition.Data G) (f : DMFormula n) (hf : Positive f)
    (ev : Computes f G) (owner : Sym2 (Fin n) → Fin n)
    (owns : ∀ e ∈ D.H.edgeFinset, owner e ∈ e)
    (loc : ∀ v : Fin n, (∀ z, v ≠ D.p z) →
      D.H.degree v + (if v ∈ (PendantCover.centers D.apex ∪ D.H.edgeFinset.image owner) then 1 else 0) +
        ((bad D f).filter (fun i => D.apex i = v)).card ≤
      (occurrences f v).card + (D.H.edgeFinset.filter (fun e => owner e = v)).card)
    (k : ℕ) (mincov : ∀ S, PendantCover.Covers G S → k ≤ S.card) :
    G.edgeFinset.card + k ≤ f.leaves := by
  classical
  let priv := Finset.univ.image D.p
  let pay := PendantCover.centers D.apex ∪ D.H.edgeFinset.image owner
  let U := D.H.edgeFinset.image owner \ PendantCover.centers D.apex
  have hcov : PendantCover.CoversUnmarked D.H D.apex U := by
    intro x y h nx ny
    have hin : s(x,y) ∈ D.H.edgeFinset := D.H.mem_edgeFinset.mpr h
    have ho := Finset.mem_image_of_mem owner hin
    rcases Sym2.mem_iff.mp (owns _ hin) with hx | hy
    · exact Or.inl (Finset.mem_sdiff.mpr ⟨hx ▸ ho,nx⟩)
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨hy ▸ ho,ny⟩)
  obtain ⟨S,hs,hsc⟩ := PendantCover.coverFromCore G D.H D.apex (fun i => D.p (i,false))
    (fun i => D.p (i,true)) U D.decomp hcov
  have union : PendantCover.centers D.apex ∪ U = pay := by
    ext v
    simp [U,pay]
  have disj : Disjoint (PendantCover.centers D.apex) U := Finset.disjoint_sdiff
  have cp := Finset.card_union_of_disjoint disj
  rw [union] at cp
  have kc := mincov S hs
  rw [Fintype.card_fin] at hsc
  have hpriv (v : Fin n) : v ∈ priv ↔ ∃ z, D.p z = v := by simp [priv]
  have degZero (z) : D.H.degree (D.p z) = 0 := by
    rw [← D.H.card_neighborFinset_eq_degree, Finset.card_eq_zero]
    exact Finset.eq_empty_iff_forall_notMem.mpr fun w hw =>
      D.privateOffCore _ _ ((D.H.mem_neighborFinset _ _).mp hw) z rfl
  have miss (z) : D.p z ∉ pay := by
    intro h
    rcases Finset.mem_union.mp h with center | him
    · exact D.apart z center
    · obtain ⟨e,he,eq⟩ := Finset.mem_image.mp him
      have hv : D.p z ∈ e := eq ▸ owns e he
      have ne : (D.H.incidenceFinset (D.p z)).Nonempty :=
        ⟨e,D.H.mem_incidenceFinset.mpr ⟨D.H.mem_edgeFinset.mp he,hv⟩⟩
      simpa [SimpleGraph.card_incidenceFinset_eq_degree,degZero] using Finset.card_pos.mpr ne
  let remainder (v : Fin n) := if v ∈ priv then 0 else (occurrences f v).card
  have localAll (v : Fin n) :
      D.H.degree v + (if v ∈ pay then 1 else 0) + ((bad D f).filter (fun i => D.apex i = v)).card ≤
        remainder v + (D.H.edgeFinset.filter (fun e => owner e = v)).card := by
    by_cases hp : v ∈ priv
    · obtain ⟨z,rfl⟩ := (hpriv v).mp hp
      have empt : ((bad D f).filter (fun i => D.apex i = D.p z)) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        exact D.apart z ((Finset.mem_filter.mp hi).2 ▸ (Finset.mem_image_of_mem D.apex (Finset.mem_univ i)))
      simp [degZero,miss,empt]
    · simpa [remainder,hp,pay] using loc v (fun z h => hp ((hpriv _).mpr ⟨z,h.symm⟩))
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun v _ => localAll v)
  simp only [Finset.sum_add_distrib,D.H.sum_degrees_eq_twice_card_edges,
    Finset.sum_card_fiberwise_eq_card_filter] at total
  simp [← Finset.sum_filter] at total
  have prv (i : Fin D.t) :
      4 ≤ (occurrences f (D.p (i,false))).card + (occurrences f (D.p (i,true))).card +
        (if i ∈ bad D f then 1 else 0) := by
    have lb := threePrivate hf ev (D.base i) (D.spoke i false).symm (D.spoke i true).symm
    by_cases e : (occurrences f (D.p (i,false))).card + (occurrences f (D.p (i,true))).card = 3 <;>
      simp [bad,e] <;> omega
  have privateTotal := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => prv i)
  simp only [Finset.sum_add_distrib] at privateTotal
  simp [← Finset.sum_filter] at privateTotal
  have split : (∑ v, remainder v) + (∑ i : Fin D.t, (occurrences f (D.p (i,false))).card) +
      (∑ i : Fin D.t, (occurrences f (D.p (i,true))).card) = f.leaves := by
    have eqpriv : (∑ v ∈ priv, (occurrences f v).card) =
        (∑ i : Fin D.t, (occurrences f (D.p (i,false))).card) +
        ∑ i : Fin D.t, (occurrences f (D.p (i,true))).card := by
      unfold priv
      rw [Finset.sum_image (fun _ _ _ _ e => D.inj e), Fintype.sum_prod_type]
      simp [Fintype.sum_bool, Finset.sum_add_distrib,add_comm]
    rw [add_assoc, ← eqpriv]
    have split' := Finset.sum_add_sum_compl priv (fun v => (occurrences f v).card)
    simp only [remainder,ite_not]
    have hrem : (∑ v : Fin n, if v ∈ priv then 0 else (occurrences f v).card) =
        ∑ v ∈ privᶜ, (occurrences f v).card := by
      have hh := Finset.sum_filter (s := (Finset.univ : Finset (Fin n))) (p := fun v => v ∉ priv) (f := fun v => (occurrences f v).card)
      simpa [Finset.compl_eq_univ_sdiff, Finset.sdiff_eq_filter] using hh.symm
    rw [hrem,add_comm,split']
    simp [occurrences, Finset.sum_card_fiberwise_eq_card_filter]
  have edges := D.edgeCount
  omega

end PendantCount

-- Build independent sets in the original graph by choosing one private vertex per marked triangle.
namespace PendantColumns

open PendantDecomposition CubicStarCapacity

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

noncomputable def bits (S : Set (Fin n)) (v : Fin n) : Bool := by
  classical exact decide (v ∈ S)

theorem bits_true (S : Set (Fin n)) (v) : bits S v = true ↔ v ∈ S := by
  classical simp [bits]

theorem bits_false (S : Set (Fin n)) (v) : bits S v = false ↔ v ∉ S := by
  classical simp [bits]

def Independent (G : SimpleGraph (Fin n)) (S : Set (Fin n)) : Prop :=
  ∀ x y, x ∈ S → y ∈ S → ¬ G.Adj x y

private def extend (D : Data G) (tag : Fin D.t → Bool)
    (base : Set (Fin n)) (mark : Fin n → Prop) : Set (Fin n) :=
  {x | x ∈ base ∨ ∃ i, mark (D.apex i) ∧ D.p (i, tag i) = x}

def edgeCol (D : Data G) (tag : Fin D.t → Bool) (g : Sym2 (Fin n)) : Set (Fin n) :=
  extend D tag {v | negativeSet D.H g v} (· ∈ g)

def refCol (D : Data G) (tag : Fin D.t → Bool) (c : Fin n) : Set (Fin n) :=
  extend D tag {v | D.H.Adj c v} (· = c)

def swapTag {m : ℕ} (tag : Fin m → Bool) (k i : Fin m) : Bool :=
  if i = k then !tag i else tag i

def switchCol (D : Data G) (tag : Fin D.t → Bool) (c : Fin n) (k : Fin D.t) : Set (Fin n) :=
  refCol D (swapTag tag k) c

theorem apexNonprivate (D : Data G) (i : Fin D.t) (z : Fin D.t × Bool) : D.apex i ≠ D.p z := by
  intro h
  apply D.apart z
  rw [← h]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ i)

private theorem extendCore (D : Data G) (tag : Fin D.t → Bool) (base : Set (Fin n))
    (mark : Fin n → Prop) (v : Fin n) (hnp : ∀ z, v ≠ D.p z) :
    v ∈ extend D tag base mark ↔ v ∈ base := by
  constructor
  · rintro (h | ⟨i, _, h⟩)
    · exact h
    · exact (hnp (i, tag i) h.symm).elim
  · exact Or.inl

private theorem extendPrivate (D : Data G) (tag : Fin D.t → Bool) (base : Set (Fin n))
    (mark : Fin n → Prop) (off : ∀ z, D.p z ∉ base) (i : Fin D.t) (t : Bool) :
    D.p (i,t) ∈ extend D tag base mark ↔ mark (D.apex i) ∧ t = tag i := by
  constructor
  · rintro (h | ⟨j, hj, h⟩)
    · exact (off _ h).elim
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (D.inj h)
      exact ⟨hj, rfl⟩
  · rintro ⟨hi,rfl⟩
    exact Or.inr ⟨i,hi,rfl⟩

private theorem edgeBaseOff (D : Data G) (g : Sym2 (Fin n)) (z) :
    ¬negativeSet D.H g (D.p z) := by
  rintro ⟨_, j, _, h⟩
  exact D.privateOffCore _ _ h z rfl

private theorem refBaseOff (D : Data G) (c : Fin n) (z) : ¬D.H.Adj c (D.p z) := by
  intro h
  exact D.privateOffCore _ _ h.symm z rfl

theorem edgeCore (D : Data G) (tag : Fin D.t → Bool) (g : Sym2 (Fin n)) (v)
    (hnp : ∀ z, v ≠ D.p z) : v ∈ edgeCol D tag g ↔ negativeSet D.H g v :=
  extendCore D tag {u | negativeSet D.H g u} (· ∈ g) v hnp

theorem refCore (D : Data G) (tag : Fin D.t → Bool) (c v)
    (hnp : ∀ z, v ≠ D.p z) : v ∈ refCol D tag c ↔ D.H.Adj c v :=
  extendCore D tag {u | D.H.Adj c u} (· = c) v hnp

theorem switchCore (D : Data G) (tag : Fin D.t → Bool) (c) (k : Fin D.t) (v)
    (hnp : ∀ z, v ≠ D.p z) : v ∈ switchCol D tag c k ↔ D.H.Adj c v :=
  refCore D _ c v hnp

theorem edgePrivate (D : Data G) (tag : Fin D.t → Bool) (g : Sym2 (Fin n)) (i) (t) :
    D.p (i,t) ∈ edgeCol D tag g ↔ D.apex i ∈ g ∧ t = tag i :=
  extendPrivate D tag _ _ (edgeBaseOff D g) i t

theorem refPrivate (D : Data G) (tag : Fin D.t → Bool) (c) (i) (t) :
    D.p (i,t) ∈ refCol D tag c ↔ D.apex i = c ∧ t = tag i :=
  extendPrivate D tag _ _ (refBaseOff D c) i t

theorem switchPrivate (D : Data G) (tag : Fin D.t → Bool) (c) (k i : Fin D.t) (t) :
    D.p (i,t) ∈ switchCol D tag c k ↔ D.apex i = c ∧ t = (if i = k then !tag i else tag i) :=
  refPrivate D _ c i t

private theorem extendIndependent (D : Data G) (tag : Fin D.t → Bool) (base : Set (Fin n))
    (mark : Fin n → Prop) (hbase : Independent D.H base) (off : ∀ z, D.p z ∉ base)
    (away : ∀ c, mark c → c ∉ base) : Independent G (extend D tag base mark) := by
  have alone (i : Fin D.t) (hmark : mark (D.apex i)) (v : Fin n) (hv : v ∈ base) :
      ¬G.Adj (D.p (i,tag i)) v := by
    intro h
    rcases (D.neighbors _ _ _).mp h with rfl | rfl
    · exact away _ hmark hv
    · exact off _ hv
  intro x y hx hy hxy
  rcases hx with hx | ⟨i, hi, rfl⟩ <;> rcases hy with hy | ⟨j, hj, rfl⟩
  · rcases D.decomp _ _ hxy with hc | ⟨i, ht⟩
    · exact hbase _ _ hx hy hc
    · rcases ht with h | h | h <;> rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      all_goals first | exact off _ hx | exact off _ hy
  · exact alone j hj x hx hxy.symm
  · exact alone i hi y hy hxy
  · rcases (D.neighbors _ _ _).mp hxy with h | h
    · exact apexNonprivate D i _ h.symm
    · obtain ⟨rfl,hb⟩ := Prod.mk.inj (D.inj h)
      cases ht : tag j <;> simp [ht] at hb

theorem edgeIndependent (D : Data G) (tag : Fin D.t → Bool) (g : Sym2 (Fin n)) (hg : g ∈ D.H.edgeSet) :
    Independent G (edgeCol D tag g) := by
  apply extendIndependent D tag {v | negativeSet D.H g v} (· ∈ g)
    (negativeIndependent D.H D.triFree D.square g hg) (edgeBaseOff D g)
  exact fun _ hmem hbad => hbad.1 hmem

theorem refIndependent (D : Data G) (tag : Fin D.t → Bool) (c : Fin n) :
    Independent G (refCol D tag c) := by
  refine extendIndependent D tag {v | D.H.Adj c v} (· = c) ?_ (refBaseOff D c) ?_
  · intro x y hx hy hxy
    exact D.triFree c x y hx hxy hy.symm
  · intro v hv
    rw [hv]
    exact D.H.irrefl

theorem switchIndependent (D : Data G) (tag : Fin D.t → Bool) (c : Fin n) (k : Fin D.t) :
    Independent G (switchCol D tag c k) := refIndependent D (swapTag tag k) c

theorem evalFalse {f : PEqualNP.MetaComplexity.DMFormula n} (he : PendantPrivate.Computes f G)
    (S : Set (Fin n)) (h : Independent G S) : f.eval (bits S) = false := by
  apply Bool.eq_false_iff.mpr
  intro htrue
  obtain ⟨x, y, hxy, hx, hy⟩ := (he _).mp htrue
  exact h x y ((bits_true _ _).mp hx) ((bits_true _ _).mp hy) hxy

end PendantColumns

-- At a triangle apex, switching the private choice gives an independent column difference.
namespace PendantHubRank

variable {I J B : Type} [Fintype I] [Fintype J] [Fintype B] [DecidableEq I] [DecidableEq J]

theorem rank (M : Matrix (Sum I (Option J)) B ℚ) (base : B) (edge : I → B) (flip : J → B)
    (baseCore : ∀ i, M (.inl i) base = 1)
    (baseTag : ∀ j, M (.inr (some j)) base = 0)
    (baseMark : M (.inr none) base = 1)
    (edgeCore : ∀ i k, M (.inl i) (edge k) = if i = k then 0 else 1)
    (edgeTag : ∀ j k, M (.inr (some j)) (edge k) = 0)
    (edgeMark : ∀ k, M (.inr none) (edge k) = 1)
    (flipCore : ∀ i k, M (.inl i) (flip k) = 1)
    (flipTag : ∀ j k, M (.inr (some j)) (flip k) = if j = k then 1 else 0) :
    Fintype.card I + Fintype.card J + 1 ≤ M.rank := by
  classical
  have inj : Function.Injective M.transpose.mulVecLin := by
    apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    have eqn (b : B) := congrFun hx b
    have expand (b : B) :
        (∑ i : I, M (.inl i) b * x (.inl i)) + M (.inr none) b * x (.inr none) +
          ∑ j : J, M (.inr (some j)) b * x (.inr (some j)) = 0 := by
      have he : (∑ u, M u b * x u) = 0 := eqn b
      simpa only [
        Fintype.sum_sum_type, Fintype.sum_option, add_assoc, add_left_comm, add_comm] using he
    have hb := expand base
    simp only [baseCore,baseMark,baseTag,one_mul,zero_mul,Finset.sum_const_zero,add_zero] at hb
    have hcore (k : I) : x (.inl k) = 0 := by
      have h := expand (edge k)
      simp only [edgeCore,edgeMark,edgeTag,one_mul,zero_mul,Finset.sum_const_zero,add_zero] at h
      have sub (i : I) : (if i = k then (0 : ℚ) else 1) * x (.inl i) =
            x (.inl i) - if i = k then x (.inl i) else 0 := by
        split <;> simp_all
      simp_rw [sub] at h
      rw [Finset.sum_sub_distrib] at h
      simp at h
      linarith
    simp [hcore] at hb
    have htag (k : J) : x (.inr (some k)) = 0 := by
      have h := expand (flip k)
      simpa [hcore, hb, flipTag, ite_mul] using h
    funext a
    rcases a with i | (_ | j)
    · exact hcore i
    · exact hb
    · exact htag j
  have eq : M.transpose.rank = Fintype.card (Sum I (Option J)) := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj inj, Module.finrank_fintype_fun_eq_card]
  rw [Matrix.rank_transpose] at eq
  simp only [Fintype.card_sum, Fintype.card_option] at eq
  omega

end PendantHubRank

namespace PartialDiagonalRank

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def mat (P : Finset ι) : Matrix ι ι ℚ :=
  fun i j => 1 - if i = j ∧ i ∉ P then 1 else 0

theorem applyVec (P : Finset ι) (x : ι → ℚ) (i : ι) :
    (mat P).mulVec x i = ∑ j, x j - (if i ∈ P then 0 else x i) := by
  by_cases hi : i ∈ P <;> simp [Matrix.mulVec, dotProduct, mat, hi, sub_mul,
    Finset.sum_sub_distrib, ite_mul]

private theorem fullRank (P : Finset ι)
    (h : ∀ x : ι → ℚ, (mat P).mulVec x = 0 → x = 0) :
    (mat P).rank = Fintype.card ι := by
  have inj : Function.Injective (mat P).mulVecLin := (injective_iff_map_eq_zero _).mpr h
  rw [Matrix.rank, LinearMap.finrank_range_of_inj inj, Module.finrank_fintype_fun_eq_card]

theorem singletonRank (p : ι) : (mat {p}).rank = Fintype.card ι := by
  apply fullRank
  intro x hx
  have ht : ∑ i, x i = 0 := by simpa [applyVec] using congrFun hx p
  have ho (j : ι) (hj : j ≠ p) : x j = 0 := by
    simpa [applyVec, hj, ht] using congrFun hx j
  have hp : x p = 0 := by
    rwa [Finset.sum_eq_single p (fun i _ hin => ho i hin) (by simp)] at ht
  ext i
  by_cases h : i = p
  · rwa [h]
  · exact ho i h

theorem ownedRank (P : Finset ι) (hP : P.Nonempty) :
    Fintype.card ι - P.card + 1 ≤ (mat P).rank := by
  obtain ⟨p, hp⟩ := hP
  let S := insert p (Finset.univ \ P)
  let r : S := ⟨p, Finset.mem_insert_self _ _⟩
  have localMat : (mat P).submatrix (fun i : S => i.val) (fun i : S => i.val) = mat {r} := by
    ext i j
    have owned : i.val ∈ P ↔ i = r := by
      constructor
      · intro h
        rcases Finset.mem_insert.mp i.prop with eq | miss
        · exact Subtype.ext eq
        · exact ((Finset.mem_sdiff.mp miss).2 h).elim
      · rintro rfl
        exact hp
    simp [Matrix.submatrix, mat, owned]
  have bound := (mat P).rank_submatrix_le (fun i : S => i.val) (fun i : S => i.val)
  rw [localMat, singletonRank, Fintype.card_coe] at bound
  simpa [S, hp, Finset.card_sdiff_of_subset] using bound

def extended (P : Finset ι) : Matrix ι (Option ι) ℚ := fun i j =>
  match j with
  | none => 1
  | some k => mat P i k

private theorem extendedEmpty : (extended (∅ : Finset ι)).rank = Fintype.card ι := by
  have surj : Function.Surjective (extended (∅ : Finset ι)).mulVecLin := by
    intro y
    let x : Option ι → ℚ := fun j => match j with
      | none => ∑ k, y k
      | some k => -y k
    use x
    ext i
    change (∑ j : Option ι, extended ∅ i j * x j) = y i
    rw [Fintype.sum_option]
    change 1 * (∑ k, y k) + (mat ∅).mulVec (fun k => -y k) i = y i
    rw [applyVec]
    simp
  rw [Matrix.rank, LinearMap.range_eq_top.mpr surj]
  simp

theorem extendedRank (P : Finset ι) :
    Fintype.card ι - P.card + (if P.Nonempty then 1 else 0) ≤ (extended P).rank := by
  by_cases h : P.Nonempty
  · simp only [if_pos h]
    exact (ownedRank P h).trans ((extended P).rank_submatrix_le id some)
  · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp h
    simp [extendedEmpty]

theorem rectanglesRank {α β L : Type} [Fintype β]
    (M : Matrix α β ℚ) (T : Finset L) (hitR : L → α → Bool) (hitC : L → β → Bool)
    (entries : ∀ i j, M i j = ∑ l ∈ T, if hitR l i && hitC l j then 1 else 0) :
    M.rank ≤ T.card := by
  classical
  let R : Matrix α T ℚ := fun i l => if hitR l.val i then 1 else 0
  let C : Matrix T β ℚ := fun l j => if hitC l.val j then 1 else 0
  have eq : M = R * C := by
    ext i j
    rw [entries, Matrix.mul_apply, ← Finset.sum_attach]
    change (∑ l ∈ T.attach, _) = ∑ l ∈ T.attach, _
    apply Finset.sum_congr rfl
    intro l _
    cases hr : hitR l.val i <;> cases hc : hitC l.val j <;> simp [R, C, hr, hc]
  rw [eq]
  simpa using ((Matrix.rank_mul_le_left R C).trans (Matrix.rank_le_card_width R))

end PartialDiagonalRank

-- Bound the rank for each variable by the number of leaves carrying its label.
namespace PendantLocal

open PEqualNP.MetaComplexity FormulaRectangleBound FormulaKWPartition PendantPrivate

variable {n : ℕ} {G : SimpleGraph (Fin n)} {f : DMFormula n} {c : Fin n}

structure CoreColumns (G : SimpleGraph (Fin n)) (f : DMFormula n) (c : Fin n) (I : Type) where
  tip : I → Fin n
  base : Fin n → Bool
  edge : I → Fin n → Bool
  adj : ∀ i, G.Adj c (tip i)
  baseNeg : f.eval base = false
  edgeNeg : ∀ i, f.eval (edge i) = false
  baseOn : ∀ i, base (tip i) = true
  edgeOff : ∀ i k, i ≠ k → edge k (tip i) = true

structure MarkedColumns {I : Type} (C : CoreColumns G f c I) (J : Type) where
  a : J → Fin n
  b : J → Fin n
  extra : Fin n
  flip : J → Fin n → Bool
  ac : ∀ j, G.Adj (a j) c
  ab : ∀ j, G.Adj (a j) (b j)
  one : ∀ j, (occurrences f (a j)).card ≤ 1
  extraAdj : G.Adj c extra
  baseB : ∀ j, C.base (b j) = true
  edgeB : ∀ k j, C.edge k (b j) = true
  baseExtra : C.base extra = true
  edgeExtra : ∀ k, C.edge k extra = true
  flipNeg : ∀ k, f.eval (flip k) = false
  flipCore : ∀ k i, flip k (C.tip i) = true
  flipA : ∀ k, flip k (a k) = true
  flipOther : ∀ j k, j ≠ k → flip k (b j) = true

noncomputable def value (f : DMFormula n) (c : Fin n) (x y : Fin n → Bool) : ℚ :=
  if label f (route f x y) = c then 1 else 0

private theorem value_one {x y : Fin n → Bool} (h : reached f c x y) :
    value f c x y = 1 := ite_eq_left h

private theorem value_zero {x y : Fin n → Bool} (h : ¬ reached f c x y) :
    value f c x y = 0 := ite_eq_right h

theorem rank_le {R B : Type} [Fintype B] (f : DMFormula n) (c : Fin n)
    (x : R → Fin n → Bool) (y : B → Fin n → Bool) :
    Matrix.rank (fun r b => value f c (x r) (y b)) ≤ (occurrences f c).card := by
  classical
  apply PartialDiagonalRank.rectanglesRank _ _
    (fun l r => decide (rowPath f (x r) l)) (fun l b => decide (colPath f (y b) l))
  intro r b
  simp only [occurrences,value,Bool.and_eq_true,decide_eq_true_eq,reaches_iff]
  simp

theorem unmarked {I : Type} [Fintype I] [DecidableEq I] (hf : Positive f)
    (he : Computes f G) (C : CoreColumns G f c I) (P : Finset I)
    (owner : ∀ i, reached f c (pair c (C.tip i)) (C.edge i) ↔ i ∈ P) :
    Fintype.card I - P.card + (if P.Nonempty then 1 else 0) ≤ (occurrences f c).card := by
  classical
  let x (i : I) := pair c (C.tip i)
  let y : Option I → Fin n → Bool := fun k => k.elim C.base C.edge
  have same : PartialDiagonalRank.extended P = (fun i k => value f c (x i) (y k)) := by
    ext i k
    cases k with
    | none =>
      exact (value_one (forced hf he (C.adj i) C.base C.baseNeg (C.baseOn i))).symm
    | some k =>
      by_cases eq : i = k
      · subst k
        by_cases h : i ∈ P
        · simpa [PartialDiagonalRank.extended,PartialDiagonalRank.mat,h,x,y] using
            (value_one ((owner i).mpr h)).symm
        · simpa [PartialDiagonalRank.extended,PartialDiagonalRank.mat,h,x,y] using
            (value_zero (fun h' => h ((owner i).mp h'))).symm
      · have force := forced hf he (C.adj i) _ (C.edgeNeg k) (C.edgeOff i k eq)
        simpa [PartialDiagonalRank.extended,PartialDiagonalRank.mat,eq,x,y] using
          (value_one force).symm
  have h := PartialDiagonalRank.extendedRank P
  rw [same] at h
  exact h.trans (rank_le f c x y)

theorem marked {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (hf : Positive f) (he : Computes f G) (C : CoreColumns G f c I) (D : MarkedColumns C J)
    (P : Finset I) (owner : ∀ i, reached f c (pair c (C.tip i)) (C.edge i) ↔ i ∈ P) :
    Fintype.card I - P.card + Fintype.card J + 1 ≤ (occurrences f c).card := by
  classical
  let U := Finset.univ \ P
  let row : Sum (↥U) (Option J) → Fin n → Bool :=
    fun r => r.elim (fun i => pair c (C.tip i.val))
      (fun t => t.elim (pair c D.extra) fun j => pair c (D.a j))
  let col : Option (Sum (↥U) J) → Fin n → Bool :=
    fun k => k.elim C.base fun s => s.elim (fun i => C.edge i.val) D.flip
  let M : Matrix (Sum (↥U) (Option J)) (Option (Sum (↥U) J)) ℚ :=
    fun r k => value f c (row r) (col k)
  have tagged (j : J) (y : Fin n → Bool) (hn : f.eval y = false) (hb : y (D.b j) = true) :
      value f c (pair c (D.a j)) y = 0 := by
    have rev : pair (D.a j) c = pair c (D.a j) := by funext i; simp [pair, or_comm]
    have claim := forcedTaggedRow hf he (D.ab j) (D.ac j) (D.one j) y hn hb
    rw [rev] at claim
    exact value_zero (fun h => (D.ac j).ne (claim.symm.trans h))
  have bound := PendantHubRank.rank M none (fun i => some (.inl i)) (fun j => some (.inr j))
    (fun i => value_one (forced hf he (C.adj i.val) _ C.baseNeg (C.baseOn i.val)))
    (fun j => tagged j _ C.baseNeg (D.baseB j))
    (value_one (forced hf he D.extraAdj _ C.baseNeg D.baseExtra))
    (fun i k => by
      by_cases h : i = k
      · subst k
        rw [ite_eq_left rfl]
        exact value_zero fun hc => (Finset.mem_sdiff.mp i.prop).2 ((owner i.val).mp hc)
      · rw [ite_eq_right h]
        exact value_one (forced hf he (C.adj i.val) _ (C.edgeNeg k.val)
          (C.edgeOff i.val k.val (fun hv => h (Subtype.ext hv)))))
    (fun j k => tagged j _ (C.edgeNeg k.val) (D.edgeB k.val j))
    (fun k => value_one (forced hf he D.extraAdj _ (C.edgeNeg k.val) (D.edgeExtra k.val)))
    (fun i k => value_one (forced hf he (C.adj i.val) _ (D.flipNeg k) (D.flipCore k i.val)))
    (fun j k => by
      by_cases h : j = k
      · subst k
        rw [ite_eq_left rfl]
        exact value_one (forced hf he (D.ac j).symm _ (D.flipNeg j) (D.flipA j))
      · rw [ite_eq_right h]
        exact tagged j _ (D.flipNeg k) (D.flipOther j k h))
  have h := bound.trans (rank_le f c row col)
  simpa [U,Finset.card_sdiff_of_subset (Finset.subset_univ P)] using h

end PendantLocal

namespace PendantLocalGraph

open PendantColumns PendantDecomposition PendantPrivate PendantLocal
open FormulaKWPartition FormulaRectangleBound PEqualNP.MetaComplexity

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {f : DMFormula n}

abbrev Star (D : Data G) (c : Fin n) := ↥(D.H.incidenceFinset c)

theorem center_mem (D : Data G) (c : Fin n) (k : Star D c) : c ∈ k.val :=
  (D.H.mem_incidenceFinset.mp k.prop).2

theorem coreEdge (D : Data G) (c : Fin n) (k : Star D c) : k.val ∈ D.H.edgeSet :=
  (D.H.mem_incidenceFinset.mp k.prop).1

noncomputable def tip (D : Data G) (c : Fin n) (k : Star D c) : Fin n :=
  Sym2.Mem.other (center_mem D c k)

theorem tipPair (D : Data G) (c : Fin n) (k : Star D c) : s(c,tip D c k) = k.val :=
  Sym2.other_spec (center_mem D c k)

theorem tip_adj (D : Data G) (c : Fin n) (k : Star D c) : D.H.Adj c (tip D c k) := by
  change s(c,tip D c k) ∈ D.H.edgeSet
  rw [tipPair]
  exact coreEdge D c k

theorem tip_nonprivate (D : Data G) (c : Fin n) (k : Star D c) :
    ∀ z, tip D c k ≠ D.p z := D.privateOffCore _ _ (tip_adj D c k).symm

noncomputable def core (D : Data G) (tag : Fin D.t → Bool)
    (he : Computes f G) (c : Fin n) : CoreColumns G f c (Star D c) where
  tip := tip D c
  base := bits (refCol D tag c)
  edge k := bits (edgeCol D tag k.val)
  adj k := D.coreAdj _ _ (tip_adj D c k)
  baseNeg := evalFalse he _ (refIndependent D tag c)
  edgeNeg k := evalFalse he _ (edgeIndependent D tag k.val (coreEdge D c k))
  baseOn k := (bits_true _ _).mpr ((refCore D tag c _ (tip_nonprivate D c k)).mpr (tip_adj D c k))
  edgeOff i k h := by
    apply (bits_true _ _).mpr
    apply (edgeCore D tag k.val _ (tip_nonprivate D c i)).mpr
    refine ⟨?_, c, center_mem D c k, (tip_adj D c i).symm⟩
    rw [← tipPair D c k, Sym2.mem_iff]
    rintro (hc | ht)
    · exact (tip_adj D c i).ne hc.symm
    · apply h
      apply Subtype.ext
      rw [← tipPair D c i, ← tipPair D c k, ht]

def edgeInput (e : Sym2 (Fin n)) (i : Fin n) := decide (i ∈ e)

theorem edgeInput_pair (c x : Fin n) : edgeInput s(c,x) = pair c x := by
  funext i
  simp [edgeInput, pair, Sym2.mem_iff]

noncomputable def owner (D : Data G) (tag : Fin D.t → Bool) (f : DMFormula n)
    (g : Sym2 (Fin n)) : Fin n :=
  label f (route f (edgeInput g) (bits (edgeCol D tag g)))

noncomputable def owned (D : Data G) (tag : Fin D.t → Bool) (f : DMFormula n)
    (c : Fin n) : Finset (Sym2 (Fin n)) := D.H.edgeFinset.filter (fun e => owner D tag f e = c)

theorem owner_mem (D : Data G) (tag : Fin D.t → Bool) (hf : Positive f) (he : Computes f G)
    (g : Sym2 (Fin n)) (hg : g ∈ D.H.edgeFinset) : owner D tag f g ∈ g := by
  have htrue : f.eval (edgeInput g) = true := by
    induction g using Sym2.inductionOn with
    | _ a b =>
      have h := D.coreAdj a b (D.H.mem_edgeFinset.mp hg)
      exact (he _).mpr ⟨a,b,h,by simp [edgeInput],by simp [edgeInput]⟩
  let k := route f (edgeInput g) (bits (edgeCol D tag g))
  have hrow := ((reaches_iff f (edgeInput g) (bits (edgeCol D tag g)) k).mpr rfl).1
  exact of_decide_eq_true (row_label f hf _ htrue k hrow)

noncomputable def ownersInStar (D : Data G) (tag : Fin D.t → Bool) (f : DMFormula n) (c : Fin n) :
    Finset (Star D c) := Finset.univ.filter (fun e => owner D tag f e.val = c)

theorem reaches_owner (D : Data G) (tag : Fin D.t → Bool) (he : Computes f G) (c : Fin n)
    (e : Star D c) : reached f c (pair c ((core D tag he c).tip e)) ((core D tag he c).edge e) ↔
      e ∈ ownersInStar D tag f c := by
  simp only [ownersInStar, Finset.mem_filter, Finset.mem_univ, true_and]
  change label f (route f (pair c (tip D c e)) _) = c ↔ label f (route f (edgeInput e.val) _) = c
  rw [← edgeInput_pair, tipPair]
  rfl

theorem ownedCard (D : Data G) (tag : Fin D.t → Bool) (hf : Positive f)
    (he : Computes f G) (c : Fin n) :
    (ownersInStar D tag f c).card = (owned D tag f c).card := by
  classical
  let P := ownersInStar D tag f c
  let emb : Star D c ↪ Sym2 (Fin n) := Function.Embedding.subtype _
  have eq : P.map emb = owned D tag f c := by
    ext g
    constructor
    · intro hg
      obtain ⟨e, hp, rfl⟩ := Finset.mem_map.mp hg
      exact Finset.mem_filter.mpr ⟨D.H.mem_edgeFinset.mpr (coreEdge D c e),
        (Finset.mem_filter.mp hp).2⟩
    · intro hg
      obtain ⟨hE, howner⟩ := Finset.mem_filter.mp hg
      have inc : g ∈ D.H.incidenceFinset c := D.H.mem_incidenceFinset.mpr
        ⟨D.H.mem_edgeFinset.mp hE, howner ▸ owner_mem D tag hf he g hE⟩
      exact Finset.mem_map.mpr ⟨⟨g,inc⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,howner⟩,rfl⟩
  rw [← eq, Finset.card_map]

theorem unmarkedLower (D : Data G) (tag : Fin D.t → Bool) (hf : Positive f) (he : Computes f G)
    (c : Fin n) : D.H.degree c - (owned D tag f c).card +
      (if (owned D tag f c).Nonempty then 1 else 0) ≤ (occurrences f c).card := by
  have h := unmarked hf he (core D tag he c) _ (reaches_owner D tag he c)
  have ne : (ownersInStar D tag f c).Nonempty ↔ (owned D tag f c).Nonempty := by
    simp only [← Finset.card_pos, ownedCard D tag hf he c]
  simpa [ne, Star, SimpleGraph.card_incidenceFinset_eq_degree, ownedCard D tag hf he c] using h

end PendantLocalGraph

namespace PendantLocalGraph

open PendantColumns PendantDecomposition PendantPrivate PendantLocal
open PEqualNP.MetaComplexity

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {f : DMFormula n}

noncomputable def markedData (D : Data G) (tag : Fin D.t → Bool) (he : Computes f G)
    (c : Fin n) (hc : c ∈ PendantCover.centers D.apex) (F : Finset (Fin D.t))
    (hF : ∀ i ∈ F, D.apex i = c ∧ (occurrences f (D.p (i,!tag i))).card ≤ 1) :
    MarkedColumns (core D tag he c) F := by
  classical
  have ex : ∃ i, D.apex i = c := by simpa [PendantCover.centers] using hc
  let j0 := Classical.choose ex
  have hj0 : D.apex j0 = c := Classical.choose_spec ex
  have atC (j : ↥F) : D.apex j.val = c := (hF j.val j.prop).1
  have ref (i : Fin D.t) (hi : D.apex i = c) :
      bits (refCol D tag c) (D.p (i,tag i)) = true :=
    (bits_true _ _).mpr ((refPrivate D tag c i _).mpr ⟨hi,rfl⟩)
  have onEdge (k : Star D c) (i : Fin D.t) (hi : D.apex i = c) :
      bits (edgeCol D tag k.val) (D.p (i,tag i)) = true :=
    (bits_true _ _).mpr ((edgePrivate D tag k.val i _).mpr ⟨hi ▸ center_mem D c k,rfl⟩)
  refine {
    a := fun j => D.p (j.val,!tag j.val)
    b := fun j => D.p (j.val,tag j.val)
    extra := D.p (j0,tag j0)
    flip := fun j => bits (switchCol D tag c j.val)
    ac := fun j => ?_
    ab := fun j => ?_
    one := fun j => (hF _ j.prop).2
    extraAdj := hj0 ▸ D.spoke j0 (tag j0)
    baseB := fun j => ref j.val (atC j)
    edgeB := fun k j => onEdge k j.val (atC j)
    baseExtra := ref j0 hj0
    edgeExtra := fun k => onEdge k j0 hj0
    flipNeg := fun j => evalFalse he _ (switchIndependent D tag c j.val)
    flipCore := fun k i => (bits_true _ _).mpr
      ((switchCore D tag c k.val _ (tip_nonprivate D c i)).mpr (tip_adj D c i))
    flipA := fun k => (bits_true _ _).mpr ((switchPrivate D tag c k.val k.val _).mpr
      ⟨atC k, by simp⟩)
    flipOther := fun j k neq => (bits_true _ _).mpr ((switchPrivate D tag c k.val j.val _).mpr
      ⟨atC j, by simp [show j.val ≠ k.val from fun h => neq (Subtype.ext h)]⟩)
  }
  · rw [← atC j]
    exact (D.spoke j.val (!tag j.val)).symm
  · cases h : tag j.val
    · simpa using (D.base j.val).symm
    · simpa using D.base j.val

end PendantLocalGraph

namespace PendantLocalGraph

open PendantColumns PendantDecomposition PendantPrivate PendantLocal
open FormulaKWPartition FormulaRectangleBound PEqualNP.MetaComplexity

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {f : DMFormula n}

theorem markedLower (D : Data G) (tag : Fin D.t → Bool) (hf : Positive f) (he : Computes f G)
    (c : Fin n) (hc : c ∈ PendantCover.centers D.apex) (F : Finset (Fin D.t))
    (hF : ∀ i ∈ F, D.apex i = c ∧ (occurrences f (D.p (i,!tag i))).card ≤ 1) :
    D.H.degree c - (owned D tag f c).card + F.card + 1 ≤ (occurrences f c).card := by
  have h := marked hf he (core D tag he c) (markedData D tag he c hc F hF) _
    (reaches_owner D tag he c)
  simpa [Star, SimpleGraph.card_incidenceFinset_eq_degree, ownedCard D tag hf he c] using h

end PendantLocalGraph

namespace PendantDecomposition

theorem countEdges {n t : ℕ} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (apex : Fin t → Fin n) (p : Fin t × Bool → Fin n)
    (inj : Function.Injective p) (apart : ∀ z, p z ∉ PendantCover.centers apex)
    (coreAdj : ∀ x y, H.Adj x y → G.Adj x y)
    (privateOffCore : ∀ x y, H.Adj x y → ∀ z, x ≠ p z)
    (spoke : ∀ i b, G.Adj (apex i) (p (i,b)))
    (base : ∀ i, G.Adj (p (i,false)) (p (i,true)))
    (decomp : ∀ x y, G.Adj x y → H.Adj x y ∨
      ∃ i, PendantCover.triangleEdge (apex i) (p (i,false)) (p (i,true)) x y) :
    G.edgeFinset.card = H.edgeFinset.card + 3*t := by
  classical
  let spokeEdge (z : Fin t × Bool) := s(apex z.1,p z)
  let baseEdge (i : Fin t) := s(p (i,false),p (i,true))
  let edge : (Fin t × Bool) ⊕ Fin t → Sym2 (Fin n) := Sum.elim spokeEdge baseEdge
  have diff (i : Fin t) (z : Fin t × Bool) : apex i ≠ p z := by
    intro eq
    exact apart z (eq ▸ (show apex i ∈ PendantCover.centers apex by simp [PendantCover.centers]))
  have edgeInj : Function.Injective edge := by
    apply Function.Injective.sumElim
    · intro z w h
      rcases Sym2.eq_iff.mp h with ⟨_,eq⟩|⟨eq,_⟩
      · exact inj eq
      · exact (diff _ _ eq).elim
    · intro i j h
      rcases Sym2.eq_iff.mp h with ⟨eq,_⟩|⟨eq,_⟩ <;> exact congrArg Prod.fst (inj eq)
    · intro z i h
      rcases Sym2.eq_iff.mp h with ⟨eq,_⟩|⟨eq,_⟩ <;> exact diff _ _ eq
  let F := Finset.univ.image edge
  have valid (z) : edge z ∈ G.edgeFinset := by
    cases z with
    | inl z => exact G.mem_edgeFinset.mpr (spoke z.1 z.2)
    | inr i => exact G.mem_edgeFinset.mpr (base i)
  have separated (z) : edge z ∉ H.edgeFinset := by
    intro h
    cases z with
    | inl z =>
        have a : H.Adj (apex z.1) (p z) := H.mem_edgeFinset.mp h
        exact privateOffCore _ _ a.symm z rfl
    | inr i =>
        have a : H.Adj (p (i,false)) (p (i,true)) := H.mem_edgeFinset.mp h
        exact privateOffCore _ _ a (i,false) rfl
  have disj : Disjoint H.edgeFinset F := by
    apply Finset.disjoint_left.mpr
    rintro e he hf
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hf
    exact separated z he
  have allEdges : G.edgeFinset = H.edgeFinset ∪ F := by
    ext e
    induction e using Sym2.inductionOn with
    | _ a b =>
      constructor
      · intro h
        rcases decomp a b (G.mem_edgeFinset.mp h) with core | ⟨i,h⟩
        · exact Finset.mem_union_left _ (H.mem_edgeFinset.mpr core)
        · apply Finset.mem_union_right
          rcases h with h|h|h
          · exact Finset.mem_image.mpr ⟨Sum.inl (i,false),Finset.mem_univ _,h.symm⟩
          · exact Finset.mem_image.mpr ⟨Sum.inl (i,true),Finset.mem_univ _,h.symm⟩
          · exact Finset.mem_image.mpr ⟨Sum.inr i,Finset.mem_univ _,h.symm⟩
      · intro h
        rcases Finset.mem_union.mp h with core | tri
        · exact G.mem_edgeFinset.mpr (coreAdj a b (H.mem_edgeFinset.mp core))
        · obtain ⟨z,_,hz⟩ := Finset.mem_image.mp tri
          exact hz ▸ valid z
  rw [allEdges, Finset.card_union_of_disjoint disj]
  have cardF : F.card = 3*t := by
    rw [show F.card = Finset.univ.card from Finset.card_image_of_injective _ edgeInj]
    simp
    omega
  rw [cardF]

end PendantDecomposition

-- Remove a pair of degree-two vertices from each triangle. The remaining core is triangle-free.
namespace PendantDecomposition

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

private abbrev Vertex := Fin n

private def IsTri (s : Finset (Fin n)) : Prop :=
  s.card = 3 ∧ ∀ a ∈ s, ∀ b ∈ s, a ≠ b → G.Adj a b

private theorem makeTri (a b c : Fin n) (ab : G.Adj a b) (bc : G.Adj b c)
    (ca : G.Adj c a) : IsTri G {a,b,c} := by
  refine ⟨by simp [ab.ne,bc.ne,ca.ne.symm], ?_⟩
  intro x hx y hy hn
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl <;> first
    | exact (hn rfl).elim | assumption | exact ab.symm | exact bc.symm | exact ca.symm

private structure Pick (s : Finset (Fin n)) where
  c : Fin n
  a : Fin n
  b : Fin n
  mem : s = {c,a,b}
  ca : G.Adj c a
  cb : G.Adj c b
  ab : G.Adj a b
  da : (Finset.univ.filter (G.Adj a)).card = 2
  db : (Finset.univ.filter (G.Adj b)).card = 2

abbrev TriangleHyp : Prop := ∀ a b c : Fin n, G.Adj a b → G.Adj b c → G.Adj a c →
  ((Finset.univ.filter (G.Adj a)).card = 2 ∧ (Finset.univ.filter (G.Adj b)).card = 2) ∨
  ((Finset.univ.filter (G.Adj a)).card = 2 ∧ (Finset.univ.filter (G.Adj c)).card = 2) ∨
  ((Finset.univ.filter (G.Adj b)).card = 2 ∧ (Finset.univ.filter (G.Adj c)).card = 2)

private theorem pickExists (h : TriangleHyp G) (s : Finset (Fin n)) (hs : IsTri G s) :
    Nonempty (Pick G s) := by
  obtain ⟨x,y,z,hxy,hxz,hyz,hS⟩ := Finset.card_eq_three.mp hs.1
  have xy := hs.2 x (by simp [hS]) y (by simp [hS]) hxy
  have xz := hs.2 x (by simp [hS]) z (by simp [hS]) hxz
  have yz := hs.2 y (by simp [hS]) z (by simp [hS]) hyz
  rcases h x y z xy yz xz with ⟨hx,hy⟩|⟨hx,hz⟩|⟨hy,hz⟩
  · exact ⟨⟨z,x,y,by rw [hS]; ext; simp; tauto,xz.symm,yz.symm,xy,hx,hy⟩⟩
  · exact ⟨⟨y,x,z,by rw [hS]; ext; simp; tauto,xy.symm,yz,xz,hx,hz⟩⟩
  · exact ⟨⟨x,y,z,hS,xy,xz,yz,hy,hz⟩⟩

private theorem degreeTwo {a b c : Fin n} (hab : G.Adj a b) (hac : G.Adj a c) (hbc : b ≠ c)
    (d : (Finset.univ.filter (G.Adj a)).card = 2) (v : Fin n) :
    G.Adj a v ↔ v = b ∨ v = c := by
  have sub : ({b,c} : Finset (Fin n)) ⊆ Finset.univ.filter (G.Adj a) := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl <;> simpa
  have eq := Finset.eq_of_subset_of_card_le sub (by simp [d,hbc])
  have hv := Finset.ext_iff.mp eq v
  simpa using hv.symm

private theorem privateTriangle {s t : Finset (Fin n)} (x : Fin n) (hs : IsTri G s)
    (ht : IsTri G t) (xs : x ∈ s) (xt : x ∈ t) (d : (Finset.univ.filter (G.Adj x)).card = 2) :
    s = t := by
  let ns := insert x (Finset.univ.filter (G.Adj x))
  have card : ns.card = 3 := by simp [ns,d]
  have eqOf (K : Finset (Fin n)) (hk : IsTri G K) (hx : x ∈ K) : K = ns := by
    refine Finset.eq_of_subset_of_card_le ?_ (by rw [card,hk.1])
    intro y hy
    by_cases h : y = x
    · simp [ns,h]
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hk.2 _ hx _ hy (Ne.symm h)⟩)
  exact (eqOf s hs xs).trans (eqOf t ht xt).symm

abbrev SquareHyp : Prop := ∀ a b c d : Fin n,
  a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
  G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a

theorem extract (sq : SquareHyp G) (tri : TriangleHyp G) : Nonempty (Data G) := by
  classical
  let Tr := {s : Finset (Fin n) // IsTri G s}
  letI : Fintype Tr := Fintype.ofFinite _
  let t := Fintype.card Tr
  let enum : Fin t ≃ Tr := (Fintype.equivFin Tr).symm
  let Q (i : Fin t) := Classical.choice (pickExists G tri (enum i).val (enum i).prop)
  let apex (i : Fin t) := (Q i).c
  let p : Fin t × Bool → Fin n := fun z => if z.2 then (Q z.1).b else (Q z.1).a
  have apmem (i : Fin t) : apex i ∈ (enum i).val := by simp [apex,(Q i).mem]
  have pmem (i : Fin t) (b : Bool) : p (i,b) ∈ (enum i).val := by cases b <;> simp [p,(Q i).mem]
  have pd (i : Fin t) (b : Bool) : (Finset.univ.filter (G.Adj (p (i,b)))).card = 2 := by
    cases b
    · exact (Q i).da
    · exact (Q i).db
  have only (i j : Fin t) (b : Bool) (h : p (i,b) ∈ (enum j).val) : i = j :=
    enum.injective (Subtype.ext (privateTriangle G (p (i,b))
      (enum i).prop (enum j).prop (pmem i b) h (pd i b)))
  have spoke (i : Fin t) (b : Bool) : G.Adj (apex i) (p (i,b)) := by
    cases b
    · exact (Q i).ca
    · exact (Q i).cb
  have base (i : Fin t) : G.Adj (p (i,false)) (p (i,true)) := (Q i).ab
  have neigh (i : Fin t) (b : Bool) (v : Fin n) :
      G.Adj (p (i,b)) v ↔ v = apex i ∨ v = p (i,!b) := by
    apply degreeTwo G (spoke i b).symm _ (spoke i (!b)).ne (pd i b)
    cases b
    · exact base i
    · exact (base i).symm
  have inj : Function.Injective p := by
    rintro ⟨i,b⟩ ⟨j,c⟩ h
    obtain rfl : i = j := only i j b (h ▸ pmem j c)
    cases b <;> cases c
    · rfl
    · exact ((base i).ne h).elim
    · exact ((base i).ne h.symm).elim
    · rfl
  have apart (z : Fin t × Bool) : p z ∉ PendantCover.centers apex := by
    rintro h
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp h
    obtain ⟨i,b⟩ := z
    obtain rfl : i = j := only i j b (hj ▸ apmem j)
    exact (spoke i b).ne hj
  let free (v : Fin n) := ∀ z, v ≠ p z
  let H : SimpleGraph (Fin n) := {
    Adj := fun x y => G.Adj x y ∧ free x ∧ free y
    symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
    loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩ }
  have core (x y : Fin n) (xy : H.Adj x y) : G.Adj x y := xy.1
  have off (x y : Fin n) (xy : H.Adj x y) : ∀ z, x ≠ p z := xy.2.1
  have triEdge (i : Fin t) (b : Bool) (y : Fin n) (h : G.Adj (p (i,b)) y) :
      PendantCover.triangleEdge (apex i) (p (i,false)) (p (i,true)) (p (i,b)) y := by
    rcases (neigh i b y).mp h with rfl|rfl <;> cases b <;>
      simp [PendantCover.triangleEdge,Sym2.eq_iff]
  have decomp (x y : Fin n) (h : G.Adj x y) : H.Adj x y ∨ ∃ i,
      PendantCover.triangleEdge (apex i) (p (i,false)) (p (i,true)) x y := by
    by_cases hx : free x
    · by_cases hy : free y
      · exact Or.inl ⟨h,hx,hy⟩
      obtain ⟨⟨i,b⟩,rfl⟩ := not_forall_not.mp hy
      exact Or.inr ⟨i,by simpa only [PendantCover.triangleEdge, @Sym2.eq_swap _ x (p (i,b))] using triEdge i b x h.symm⟩
    · obtain ⟨⟨i,b⟩,rfl⟩ := not_forall_not.mp hx
      exact Or.inr ⟨i,triEdge i b y h⟩
  have tf (x y z : Fin n) (xy : H.Adj x y) (yz : H.Adj y z) (zx : H.Adj z x) : False := by
    let tr : Tr := ⟨{x,y,z},makeTri G x y z xy.1 yz.1 zx.1⟩
    obtain ⟨i,hi⟩ := enum.surjective tr
    have hp := pmem i false
    rw [hi] at hp
    change p (i,false) ∈ ({x,y,z} : Finset _) at hp
    simp only [Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with h|h|h
    · exact off x y xy _ h.symm
    · exact off y z yz _ h.symm
    · exact off z x zx _ h.symm
  have sf (a b c d : Fin n) (ac : a ≠ c) (bd : b ≠ d) (ab : H.Adj a b) (bc : H.Adj b c)
      (cd : H.Adj c d) (da : H.Adj d a) : False :=
    sq a b c d ab.ne ac da.symm.ne bc.ne bd cd.ne ab.1 bc.1 cd.1 da.1
  exact ⟨⟨t,H,inferInstance,apex,p,inj,apart,core,off,spoke,base,neigh,decomp,tf,sf,
    countEdges G H apex p inj apart core off spoke base decomp⟩⟩

end PendantDecomposition

-- Assign edges to a minimum vertex cover and join the resulting stars to attain the lower bound.
namespace GirthFiveUpper

open PEqualNP.MetaComplexity FormulaRectangleBound

private theorem orSum {α : Type} {n : ℕ} (S : Finset α) (hs : S.Nonempty)
    (k : α → ℕ) (P : α → (Fin n → Bool) → Prop)
    (given : ∀ a ∈ S, ∃ f : DMFormula n, Positive f ∧ f.leaves = k a ∧
      ∀ x, f.eval x = true ↔ P a x) :
    ∃ f : DMFormula n, Positive f ∧ f.leaves = ∑ a ∈ S, k a ∧
      ∀ x, f.eval x = true ↔ ∃ a ∈ S, P a x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp at hs
  | @insert a t ha ih =>
    obtain ⟨f, hf, lf, ef⟩ := given a (Finset.mem_insert_self ..)
    by_cases ht : t.Nonempty
    · obtain ⟨g, hg, lg, eg⟩ := ih ht (fun b hb => given b (Finset.mem_insert_of_mem hb))
      refine ⟨.or f g, ⟨hf,hg⟩, ?_, ?_⟩
      · simp [DMFormula.leaves,lf,lg,ha]
      · intro x
        simp [DMFormula.eval,ef,eg]
    · rw [Finset.not_nonempty_iff_eq_empty.mp ht]
      exact ⟨f,hf,by simpa using lf,by simpa using ef⟩

theorem upper {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (edge : ∃ a b, G.Adj a b) (C : Finset (Fin n))
    (cover : ∀ a b, G.Adj a b → a ∈ C ∨ b ∈ C) :
    ∃ f : DMFormula n, Positive f ∧ f.leaves ≤ G.edgeFinset.card + C.card ∧
      ∀ x : Fin n → Bool, f.eval x = true ↔ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
  classical
  let E := ↥G.edgeFinset
  have ends (e : E) : ∃ a b, a ∈ C ∧ G.Adj a b ∧ e.val = s(a,b) := by
    obtain ⟨e, he⟩ := e
    induction e using Sym2.inductionOn with
    | hf a b =>
      have hab : G.Adj a b := by simpa using he
      rcases cover a b hab with ha | hb
      · exact ⟨a,b,ha,hab,rfl⟩
      · exact ⟨b,a,hb,hab.symm,Sym2.eq_swap⟩
  choose center other hc hadj heq using ends
  let centers := Finset.univ.image center
  let fiber (v : Fin n) := Finset.univ.filter (fun e : E => center e = v)
  have center_mem (e : E) : center e ∈ centers := Finset.mem_image_of_mem _ (Finset.mem_univ e)
  have hcs : centers ⊆ C := by
    intro v hv
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hv
    exact hc e
  obtain ⟨a,b,hab⟩ := edge
  let witness : E := ⟨s(a,b),by simpa using hab⟩
  have star (v : Fin n) (hv : v ∈ centers) : ∃ f : DMFormula n, Positive f ∧
      f.leaves = 1 + (fiber v).card ∧
      ∀ x, f.eval x = true ↔ x v = true ∧ ∃ e ∈ fiber v, x (other e) = true := by
    obtain ⟨e,_,he⟩ := Finset.mem_image.mp hv
    have nonempty : (fiber v).Nonempty := ⟨e,by simp [fiber,he]⟩
    obtain ⟨g,hg,lg,eg⟩ := orSum (fiber v) nonempty (fun _ => 1)
      (fun j x => x (other j) = true)
      (fun j _ => ⟨.lit (other j) true,rfl,rfl,by simp [DMFormula.eval]⟩)
    refine ⟨.and (.lit v true) g,⟨rfl,hg⟩,?_,?_⟩
    · simpa [DMFormula.leaves] using lg
    · intro x
      simp [DMFormula.eval,eg]
  obtain ⟨f,hf,lf,ef⟩ := orSum centers ⟨_,center_mem witness⟩
    (fun v => 1 + (fiber v).card)
    (fun v x => x v = true ∧ ∃ e ∈ fiber v, x (other e) = true) star
  have counts : ∑ v ∈ centers, (fiber v).card = G.edgeFinset.card := by
    rw [show (∑ v ∈ centers, (fiber v).card) =
        (Finset.univ.filter (fun e : E => center e ∈ centers)).card from
      Finset.sum_card_fiberwise_eq_card_filter _ _ _]
    simp [center_mem,E]
  refine ⟨f,hf,?_,?_⟩
  · rw [lf,Finset.sum_add_distrib, counts]
    simpa [Nat.add_comm] using Nat.add_le_add_right (Finset.card_le_card hcs) G.edgeFinset.card
  · intro x
    rw [ef]
    constructor
    · rintro ⟨v,_,hv,e,he,ho⟩
      have hcv : center e = v := (Finset.mem_filter.mp he).2
      exact ⟨center e,other e,hadj e,hcv.symm ▸ hv,ho⟩
    · rintro ⟨u,v,huv,xu,xv⟩
      let e : E := ⟨s(u,v),by simpa using huv⟩
      have hh : u = center e ∧ v = other e ∨ u = other e ∧ v = center e := Sym2.eq_iff.mp (heq e)
      refine ⟨center e,center_mem e,?_,e,by simp [fiber],?_⟩ <;> rcases hh with h|h <;> simp_all

end GirthFiveUpper

namespace PendantFormula

open PEqualNP.MetaComplexity FormulaRectangleBound PendantPrivate

theorem lower {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (D : PendantDecomposition.Data G) (f : DMFormula n) (hf : Positive f)
    (ev : Computes f G) (k : ℕ) (minimum : ∀ S, PendantCover.Covers G S → k ≤ S.card) :
    G.edgeFinset.card + k ≤ f.leaves := by
  classical
  let tag := PendantCount.tag D f
  let own := PendantLocalGraph.owner D tag f
  refine PendantCount.aggregate D f hf ev own (fun e he => PendantLocalGraph.owner_mem D tag hf ev e he) ?_ k minimum
  intro v _
  let F := (PendantCount.bad D f).filter (fun i => D.apex i = v)
  by_cases marked : v ∈ PendantCover.centers D.apex
  · have hb (i) (hi : i ∈ F) : D.apex i = v ∧ (occurrences f (D.p (i,!tag i))).card ≤ 1 :=
      ⟨(Finset.mem_filter.mp hi).2, PendantCount.badOnce D f hf ev (Finset.mem_filter.mp hi).1⟩
    have bound := PendantLocalGraph.markedLower D tag hf ev v marked F hb
    have pay : v ∈ PendantCover.centers D.apex ∪ D.H.edgeFinset.image own := Finset.mem_union_left _ marked
    simp only [if_pos pay]
    change D.H.degree v + 1 + F.card ≤ (occurrences f v).card + (PendantLocalGraph.owned D tag f v).card
    omega
  · have emp : F = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact marked ((Finset.mem_filter.mp hi).2 ▸ Finset.mem_image_of_mem D.apex (Finset.mem_univ i))
    have pay : v ∈ PendantCover.centers D.apex ∪ D.H.edgeFinset.image own ↔
        (PendantLocalGraph.owned D tag f v).Nonempty := by
      simp [marked,PendantLocalGraph.owned,own,Finset.filter_nonempty_iff]
    have bound := PendantLocalGraph.unmarkedLower D tag hf ev v
    change D.H.degree v + (if v ∈ PendantCover.centers D.apex ∪ D.H.edgeFinset.image own then 1 else 0) +
        F.card ≤ (occurrences f v).card + (PendantLocalGraph.owned D tag f v).card
    simp only [pay,emp,Finset.card_empty,add_zero]
    omega

def RecPositive {n : ℕ} := DMFormula.rec (motive := fun _ : DMFormula n => Prop)
  (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q)

theorem recPositive {n : ℕ} (f : DMFormula n) : RecPositive f ↔ Positive f := by
  induction f with
  | lit => rfl
  | and f g h k => exact and_congr h k
  | or f g h k => exact and_congr h k

end PendantFormula

end PEqualNP.Outside.L_meta_252_aux

open PEqualNP.Outside.L_meta_252_aux

theorem PEqualNP.Outside.L_meta_252 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (t s : ℕ), (∃ u v : Fin n, G.Adj u v) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∀ a b c : Fin n, G.Adj a b → G.Adj b c → G.Adj a c → ((Finset.univ.filter (G.Adj a)).card = 2 ∧ (Finset.univ.filter (G.Adj b)).card = 2) ∨ ((Finset.univ.filter (G.Adj a)).card = 2 ∧ (Finset.univ.filter (G.Adj c)).card = 2) ∨ ((Finset.univ.filter (G.Adj b)).card = 2 ∧ (Finset.univ.filter (G.Adj c)).card = 2)) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → ((∃ φ : PEqualNP.MetaComplexity.DMFormula n, φ.leaves ≤ s ∧ PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ : PEqualNP.MetaComplexity.DMFormula n => Prop) (fun (_ : Fin n) (c : Bool) => c = true) (fun _ _ p q => p ∧ q) (fun _ _ p q => p ∧ q) φ ∧ ∀ x : Fin n → Bool, (φ.eval x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) ↔ G.edgeFinset.card + t ≤ s) := by
  intro n G _ t s edge sq tri hasCov minimum
  classical
  constructor
  · rintro ⟨f,lf,p,ev⟩
    obtain ⟨D⟩ := PendantDecomposition.extract G sq tri
    exact (PendantFormula.lower D f ((PendantFormula.recPositive f).mp p) ev t minimum).trans lf
  · intro h
    obtain ⟨C,cover,card⟩ := hasCov
    obtain ⟨f,p,lf,ev⟩ := GirthFiveUpper.upper G edge C cover
    exact ⟨f,by omega,(PendantFormula.recPositive f).mpr p,ev⟩
