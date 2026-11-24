import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.LowerPart
import PEqualNP.MetaComplexity.Helpers.LowerPart2

/-
The two witnesses outside each partner's neighbourhood force a mixed-colour OR
below the dirty AND. Remove the input of the first such OR that carries only
the opposite colour. The certificate uses the project's one-dirty-AND
structure and the fold-program redirection theorem.
-/
namespace PEqualNP.Outside.L_meta_4741
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.MetaComplexity.LowerPart PEqualNP.MetaComplexity.FoldProg PEqualNP.TopForm
  PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership PEqualNP.SplitCount

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g : ℕ}
def One (C : Circuit) (w : ℕ) (y : Fin n) := wireVal n C w (unitInput y) = true
def Mixed (C : Circuit) (s : Fin n → Bool) (w : ℕ) :=
  ∃ a b : Fin n, One C w a ∧ One C w b ∧ s a ≠ s b
def Partner (C : Circuit) (g : ℕ) (z : Fin n) :=
  ∃ k < C.gates.length, (gateAt C k).op = GateOp.and ∧ PZ C g k z
def Sides (G : SimpleGraph (Fin n)) (C : Circuit) (g : ℕ) :=
  ∀ z, Partner C g z → ∀ b : Fin 2, ∃ y, One C (opnd C g b) y ∧ ¬ G.Adj y z

theorem oneLow (H : OneDirty G C g) {v : Fin n} (hot : gateVal n C g (unitInput v) = true)
    {w : ℕ} (hw : w < n+C.gates.length) (hl : Low G C w) : ∃ y : Fin n, One C w y := by
  rcases (val_low H w hw hl _).mp (ones_val C H.ao w hw) with ⟨y,_,hy⟩|⟨r,_⟩
  · exact ⟨y,hy⟩
  · exact ⟨v,(reach_le C H.ao g w hw r).2 _ hot⟩

theorem anyPartner (H : OneDirty G C g) {v : Fin n} (hot : gateVal n C g (unitInput v) = true) :
    ∃ z : Fin n, Partner C g z := by
  obtain ⟨k,hk,op,b,hr⟩ := above_and H g H.hg H.dirty
  have lt := opnd_lt C H.ao k hk (1-b)
  obtain ⟨z,hz⟩ := oneLow H hot (by omega : opnd C k (1-b)<n+C.gates.length)
    (low_opnd H k hk _ (Or.inr op))
  exact ⟨z,k,hk,op,(pz_iff C g k z).mpr ⟨b,hr,hz⟩⟩

theorem partnerAdj (H : OneDirty G C g) {z v : Fin n} (hz : Partner C g z)
    (hot : gateVal n C g (unitInput v) = true) : G.Adj v z := by
  obtain ⟨k,hk,op,hp⟩ := hz
  have up := mono C H.ao _ _ (unit_le v (pairInput v z) (by simp [pairInput])) (n+g) (by have := H.hg; omega) hot
  exact pair_adj G v z (pz_F H k hk op z hp _ up (by simp [pairInput]))

theorem partnerOutside (H : OneDirty G C g) (sides : Sides G C g) {z : Fin n} (hz : Partner C g z)
    (b : Fin 2) : ¬ One C (opnd C g b) z := by
  intro h
  obtain ⟨y,hy,ne⟩ := sides z hz (1-b)
  obtain ⟨k,hk,op,hp⟩ := hz
  exact ne (pz_opnd H k hk op z hp y b h hy).symm

theorem differentSides (H : OneDirty G C g) (s : Fin n → Bool) (col : ∀ u v, G.Adj u v → s u ≠ s v)
    {z a b : Fin n} (hz : Partner C g z) (ha : One C (opnd C g 0) a)
    (hb : One C (opnd C g 1) b) (az : ¬ G.Adj a z) (bz : ¬ G.Adj b z) : s a ≠ s b := by
  obtain ⟨k,hk,op,hp⟩ := hz
  let x := fun j : Fin n => decide (j=a ∨ j=b ∨ j=z)
  have ax : x a = true := decide_eq_true (Or.inl rfl)
  have bx : x b = true := decide_eq_true (Or.inr (Or.inl rfl))
  have zx : x z = true := decide_eq_true (Or.inr (Or.inr rfl))
  have gate := (val_and C H.ao g H.hg H.gand x).mpr
    ⟨(opnd_val H 0 x).mpr ⟨a,ax,ha⟩,(opnd_val H 1 x).mpr ⟨b,bx,hb⟩⟩
  obtain ⟨i,j,ij,hi,hj⟩ := (graphFun_empty G x).mp (pz_F H k hk op z hp x gate zx)
  change decide (_ ∨ _ ∨ _) = true at hi hj
  rcases of_decide_eq_true hi with rfl|rfl|rfl <;> rcases of_decide_eq_true hj with rfl|rfl|rfl <;>
    first | exact col _ _ ij | exact (col _ _ ij).symm | exact (G.irrefl ij).elim |
      exact (az ij).elim | exact (az ij.symm).elim | exact (bz ij).elim | exact (bz ij.symm).elim

theorem mixedLow {s : Fin n → Bool} {w} (h : Mixed C s w) : Low G C w := by
  rintro hb
  obtain ⟨a,_,ha,_,_⟩ := h
  have hf := hb _ ha
  rw [unit_false] at hf
  contradiction

theorem rawNotMixed (s : Fin n → Bool) (w : ℕ) (hw : w < n) : ¬ Mixed C s w := by
  rintro ⟨a,b,ha,hb,d⟩
  unfold One at ha hb
  rw [wireVal_lt C w hw] at ha hb
  simp only [unitInput,decide_eq_true_eq] at ha hb
  exact d (congrArg s (ha.symm.trans hb))

theorem cleanNotReach (H : OneDirty G C g) {v : Fin n} (hot : gateVal n C g (unitInput v)=true)
    (s : Fin n → Bool) (col : ∀ u v, G.Adj u v → s u ≠ s v)
    {q} (mixed : Mixed C s (n+q)) {k} (hk : k < C.gates.length) (op : (gateAt C k).op = GateOp.and)
    (kg : k ≠ g) (b : Fin 2) : ¬ OrReaches n C (opnd C k b) q := by
  intro reach
  obtain ⟨a,c,ha,hc,ac⟩ := mixed
  have lt := opnd_lt C H.ao k hk b
  have ol := opnd_lt C H.ao k hk (1-b)
  obtain ⟨z,hz⟩ := oneLow H hot (by omega : opnd C k (1-b)<n+C.gates.length) (low_opnd H k hk _ (Or.inr op))
  have raw := (reach_le C H.ao q (opnd C k b) (by omega) reach).2
  have az := col a z (and_pair' H k hk op kg b a z (raw _ ha) hz)
  have cz := col c z (and_pair' H k hk op kg b c z (raw _ hc) hz)
  cases a' : s a <;> cases c' : s c <;> cases z' : s z <;> simp_all

structure Cut (C : Circuit) (g : ℕ) (s : Fin n → Bool) (v : Fin n) (q : ℕ) (b : Fin 2) : Prop where
  prior : q < g
  op : (gateAt C q).op = GateOp.or
  mixed : Mixed C s (n+q)
  wrong : ∀ y, One C (opnd C q b) y → s y ≠ s v
  feeds : ∃ d : Fin 2, OrReaches n C (opnd C g d) q

theorem findCut (H : OneDirty G C g) (s : Fin n → Bool) (col : ∀ u v, G.Adj u v → s u ≠ s v)
    (v : Fin n) (hot : gateVal n C g (unitInput v)=true) (sides : Sides G C g) :
    ∃ q b, Cut C g s v q b := by
  classical
  obtain ⟨z,hz⟩ := anyPartner H hot
  obtain ⟨a,ha,az⟩ := sides z hz 0
  obtain ⟨b,hb,bz⟩ := sides z hz 1
  have diff := differentSides H s col hz ha hb az bz
  have hboth := (val_and C H.ao g H.hg H.gand _).mp hot
  obtain ⟨d,hd⟩ : ∃ d : Fin 2, Mixed C s (opnd C g d) := by
    by_cases av : s a = s v
    · exact ⟨1,v,b,hboth.2,hb,fun eq => diff (av.trans eq)⟩
    · exact ⟨0,a,v,ha,hboth.1,av⟩
  have ex : ∃ q : ℕ, q < g ∧ Mixed C s (n+q) := by
    have lt := opnd_lt C H.ao g H.hg d
    have ge : n ≤ opnd C g d := by by_contra! small; exact rawNotMixed s _ small hd
    refine ⟨opnd C g d - n,by omega,?_⟩
    rwa [show n+(opnd C g d-n) = opnd C g d by omega]
  let q := Nat.find ex
  obtain ⟨qg,qm⟩ : q < g ∧ Mixed C s (n+q) := Nat.find_spec ex
  have ql := qg.trans H.hg
  have qlow := mixedLow (G:=G) qm
  have qo : (gateAt C q).op = .or := by
    rcases LeafBound.ao_op H.ao ql with op|op
    · exact (qg.ne (low_and H q ql op qlow)).elim
    · exact op
  have pure (c : Fin 2) : ¬ Mixed C s (opnd C q c) := by
    intro mm
    have lt := opnd_lt C H.ao q ql c
    have ge : n ≤ opnd C q c := by by_contra! small; exact rawNotMixed s _ small mm
    have eq : n+(opnd C q c-n)=opnd C q c := by omega
    exact (Nat.find_min ex (show opnd C q c-n < q by omega)) ⟨by omega,by rwa [eq]⟩
  obtain ⟨w,ws,wh⟩ : ∃ w, s w ≠ s v ∧ One C (n+q) w := by
    obtain ⟨u,w,hu,hw,ne⟩ := qm
    by_cases uv : s u = s v
    · exact ⟨w,fun h => ne (uv.trans h.symm),hw⟩
    · exact ⟨u,uv,hu⟩
  obtain ⟨c,hc⟩ : ∃ c : Fin 2, One C (opnd C q c) w := by
    rcases (val_or C H.ao q ql qo _).mp wh with h|h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
  obtain ⟨k,hk,op,e,re⟩ := above_and H q ql qlow
  have kg : k=g := by by_contra ne; exact cleanNotReach H hot s col qm hk op ne e re
  subst k
  refine ⟨q,c,qg,qo,qm,?_,e,re⟩
  intro y hy h
  exact pure c ⟨w,y,hc,hy,fun eq => ws (eq.trans h)⟩

end PEqualNP.Outside.L_meta_4741

namespace PEqualNP.Outside.L_meta_4741
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.MetaComplexity.LowerPart PEqualNP.MetaComplexity.FoldProg PEqualNP.TopForm
  PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership PEqualNP.SplitCount

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g : ℕ}

private theorem sameBool {x y z : Bool} (hx : x ≠ z) (hy : y ≠ z) : x=y := by
  cases x <;> cases y <;> cases z <;> simp_all

theorem noPartnerOnEdge (H : OneDirty G C g) (s : Fin n → Bool) (col : ∀ u v, G.Adj u v → s u ≠ s v)
    (v : Fin n) (hot : gateVal n C g (unitInput v) = true) (sides : Sides G C g)
    {q d} (cut : Cut C g s v q d) (p r : Fin n) (pr : G.Adj p r)
    (fired : wireVal n C (opnd C q d) (pairInput p r) = true) :
    ∀ z, pairInput p r z = true → ¬ Partner C g z := by
  have ql := cut.prior.trans H.hg
  have wh := opnd_lt C H.ao q ql d
  have low := low_opnd H q ql d (Or.inl (mixedLow cut.mixed))
  obtain ⟨y,on,src⟩ : ∃ y : Fin n, pairInput p r y = true ∧ One C (opnd C q d) y := by
    rcases (val_low H _ (by omega) low _).mp fired with h|⟨rw,_⟩
    · exact h
    · have := (reach_le C H.ao g _ (by omega) rw).1
      have := cut.prior
      omega
  have wrong := cut.wrong y src
  have rawY := (val_or' C H.ao q ql cut.op (unitInput y)).mpr ⟨d,src⟩
  obtain ⟨b,reach⟩ := cut.feeds
  have bl := opnd_lt C H.ao g H.hg b
  have yb : One C (opnd C g b) y := (reach_le C H.ao q _ (by have := H.hg; omega) reach).2 _ rawY
  intro z onz part
  have same := sameBool wrong (col z v (partnerAdj H part hot).symm)
  have yz : y=z := by
    change decide (y=p ∨ y=r) = true at on
    change decide (z=p ∨ z=r) = true at onz
    rcases of_decide_eq_true on with h|h <;> rcases of_decide_eq_true onz with k|k
    · exact h.trans k.symm
    · exact ((col p r pr) (h ▸ k ▸ same)).elim
    · exact ((col r p pr.symm) (h ▸ k ▸ same)).elim
    · exact h.trans k.symm
  subst z
  exact partnerOutside H sides part b yb

private def masked (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (q g w : ℕ) :=
  Low G C w ∧ (OrReaches n C w q ∨ OrReaches n C w g)

private theorem src_unmasked (q g w : ℕ) (x : Fin n → Bool) (hm : ¬ masked G C q g w) :
    open Classical in
    srcAt x (fun j => if masked G C q g (n+j) then false else gateVal n C j x) (srcOf n w) =
    wireVal n C w x := by
  classical
  rcases srcOf_cases (n:=n) w with ⟨i,rfl⟩|⟨j,rfl⟩
  · rw [srcOf_input,wireVal_lt C _ i.isLt]; rfl
  · rw [srcOf_gate]; change (if masked G C q g (n+j) then false else gateVal n C j x) = _
    rw [ite_eq_right hm]; rfl

private theorem safeOperands (H : OneDirty G C g) (s : Fin n → Bool) (col : ∀ u v, G.Adj u v → s u ≠ s v)
    (v : Fin n) (hot : gateVal n C g (unitInput v) = true)
    {q d} (cut : Cut C g s v q d) {p r : Fin n}
    (absent : ∀ z, pairInput p r z = true → ¬ Partner C g z)
    {k} (hk : k < C.gates.length) (safe : ¬masked G C q g (n+k))
    (active : gateVal n C k (pairInput p r) = true) (b : Fin 2) :
    ¬ masked G C q g (opnd C k b) := by
  rintro ⟨lo,reachPath⟩
  rcases LeafBound.ao_op H.ao hk with op|op
  · have notg : k≠g := by
      rintro rfl
      exact safe ⟨H.dirty,Or.inr (reach_self C H.ao k hk)⟩
    rcases reachPath with rq|rg
    · exact cleanNotReach H hot s col cut.mixed hk op notg b rq
    · have notother := not_both' H k hk op b rg
      have other := ((val_and' C H.ao k hk op _ b).mp active).2
      obtain ⟨z,hz,one⟩ := (pure_val H k hk op (1-b) notother _).mp other
      exact absent z hz ⟨k,hk,op,(pz_iff C g k z).mpr ⟨b,rg,one⟩⟩
  · have low : Low G C (n+k) := by
      intro bel
      exact lo (below_or H.ao k hk op bel b)
    apply safe
    refine ⟨low,?_⟩
    exact reachPath.imp
      (fun hr => (reach_gate C H.ao k q hk).mpr (Or.inr ⟨op,b,hr⟩))
      (fun hr => (reach_gate C H.ao k g hk).mpr (Or.inr ⟨op,b,hr⟩))

theorem removePort (H : OneDirty G C g) (s : Fin n → Bool) (col : ∀ u v, G.Adj u v → s u ≠ s v)
    (v : Fin n) (hot : gateVal n C g (unitInput v) = true) (sides : Sides G C g)
    {q d} (cut : Cut C g s v q d) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  classical
  let K := Finset.range C.gates.length
  let src (k : ℕ) (b : Fin 2) : Src n ℕ := if k=q ∧ b=d then none else srcOf n (opnd C k b)
  let root := srcOf n C.output
  have hK (k : ℕ) (hk : k ∈ K) : k < C.gates.length := Finset.mem_range.mp hk
  have ql := cut.prior.trans H.hg
  obtain ⟨o,ol,oe,ob⟩ := out_gate H
  have valid := adj_of_AO G C H.ao H.comp (by omega)
  have origOut (x) : srcAt x (fun j => gateVal n C j x) root = graphFun G ∅ x := by
    rw [srcAt_srcOf,← H.comp]; rfl
  refine redirect_lt G C K hK src ?_ root ?_ valid ?_ ?_ ?_
  · intro k hk b j hj
    dsimp only [src] at hj
    split at hj
    · contradiction
    · have := srcOf_inr _ _ hj
      have kl := hK k hk
      have := opnd_lt C H.ao k kl b
      exact ⟨Finset.mem_range.mpr (by omega),by omega⟩
  · intro j hj
    have := srcOf_inr _ _ hj
    exact Finset.mem_range.mpr (by omega)
  · intro x hx
    refine ⟨fun j => gateVal n C j x,super_of_le C H.ao K hK src x ?_,(origOut x).trans hx⟩
    intro k hk b h
    dsimp only [src] at h
    split at h
    · cases h
    · rwa [srcAt_srcOf] at h
  · intro p r pr
    let x := pairInput p r
    have pos : graphFun G ∅ x = true := (graphFun_empty G x).mpr
      ⟨p,r,pr,by simp [x,pairInput],by simp [x,pairInput]⟩
    by_cases fired : wireVal n C (opnd C q d) x = true
    · have absent := noPartnerOnEdge H s col v hot sides cut p r pr fired
      let t := fun j => if masked G C q g (n+j) then false else gateVal n C j x
      have sroot : ¬masked G C q g C.output := by
        rw [oe]
        exact fun h => h.1 ob
      refine ⟨t,?_,?_⟩
      · intro k hk active
        have kl := hK k hk
        by_cases bad : masked G C q g (n+k)
        · simp [t,bad] at active
        have og : gateVal n C k x=true := by simpa only [t,ite_eq_right bad] using active
        have ne : k≠q := by
          rintro rfl
          exact bad ⟨mixedLow cut.mixed,Or.inl (reach_self C H.ao k kl)⟩
        have same (b : Fin 2) : srcAt x t (src k b) = wireVal n C (opnd C k b) x := by
          rw [show src k b = srcOf n (opnd C k b) by simp [src,ne]]
          exact src_unmasked _ _ _ _ (safeOperands H s col v hot cut absent kl bad og b)
        change opv (isA (gateAt C k).op) (srcAt x t (src k 0)) (srcAt x t (src k 1)) = true
        rw [same,same,← gate_eq C H.ao k kl]
        exact og
      · change srcAt x t (srcOf n C.output) = true
        rw [show srcAt x t (srcOf n C.output) = wireVal n C C.output x from src_unmasked _ _ _ _ sroot]
        exact (congrFun H.comp x).trans pos
    · refine ⟨fun j => gateVal n C j x,?_,(origOut x).trans pos⟩
      intro k hk active
      have same (b : Fin 2) : srcAt x (fun j => gateVal n C j x) (src k b) = wireVal n C (opnd C k b) x := by
        dsimp only [src]
        split
        · rename_i hit
          obtain ⟨rfl,rfl⟩ := hit
          exact (Bool.eq_false_iff.mpr fired).symm
        · exact srcAt_srcOf C _ x
      change opv (isA (gateAt C k).op) (srcAt x _ (src k 0)) (srcAt x _ (src k 1)) = true
      rw [same,same,← gate_eq C H.ao k (hK k hk)]
      exact active
  · exact ⟨q,ql,Or.inr ⟨d,by simp [src]⟩⟩

end PEqualNP.Outside.L_meta_4741


open PEqualNP.MetaComplexity.LowerPart PEqualNP.Outside.L_meta_4741 in
theorem PEqualNP.Outside.L_meta_4741 :
∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (g : ℕ) (v : Fin n), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → g < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬ PEqualNP.TopForm.BelowF G C g → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → k ≠ g → PEqualNP.TopForm.BelowF G C k) → PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.SplitCount.unitInput v) = true → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ z : Fin n, (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 0) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 1) (PEqualNP.SplitCount.unitInput z) = true) ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k 1) g ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C k 0) (PEqualNP.SplitCount.unitInput z) = true) → (∃ y : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 0) (PEqualNP.SplitCount.unitInput y) = true ∧ ¬ G.Adj y z) ∧ (∃ y : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 1) (PEqualNP.SplitCount.unitInput y) = true ∧ ¬ G.Adj y z)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  intro n G _ C s g v bip _ ao correct lift operands cone hg gand dirty others hot partners
  let H : OneDirty G C g := ⟨ao,correct,lift,operands,cone,hg,gand,dirty,others⟩
  have sides : Sides G C g := by
    rintro z ⟨k,hk,op,hz⟩ b
    have both := partners k hk op z hz
    fin_cases b
    · exact both.1
    · exact both.2
  obtain ⟨q,b,cut⟩ := findCut H s bip v hot sides
  exact removePort H s bip v hot sides cut
