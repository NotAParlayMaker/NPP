import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_150

-- The wire-index lemmas adapt the input relabeling proof in L-meta-567.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m


def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩


def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩


def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]


def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]



def legal (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def isAnd : GateOp → Bool
  | .and => true
  | _ => false

def fired (b : ℕ → Bool) (g : Gate) : Bool := isAnd g.op && g.inputs.any b

def reduced (b : ℕ → Bool) (g : Gate) : Gate :=
  if fired b g then ⟨.or,g.inputs.filter fun i => !(b i)⟩ else g

def rd (w : List Bool) (i : ℕ) := w.getD i false

def reduceList : List Bool → List Gate → List Gate
  | _, [] => []
  | w, g::gs => reduced (rd w) g :: reduceList (step w g) gs

theorem reduced_legal (b : ℕ → Bool) (g : Gate) (hg : legal g) : legal (reduced b g) := by
  unfold reduced
  split
  · exact ⟨Or.inr rfl,(List.length_filter_le ..).trans hg.2⟩
  · exact hg

theorem reduceList_legal (w : List Bool) (gs : List Gate) (hg : ∀ g ∈ gs, legal g) :
    ∀ g ∈ reduceList w gs, legal g := by
  induction gs generalizing w with
  | nil => simp [reduceList]
  | cons g gs ih =>
    intro k hk
    rcases List.mem_cons.mp hk with rfl|ht
    · exact reduced_legal _ _ (hg _ (by simp))
    · exact ih _ (fun t ht => hg t (by simp [ht])) k ht

theorem a_fired {b : ℕ → Bool} {g : Gate} (h : fired b g = true) : g.op = GateOp.and := by
  have eq := (Bool.and_eq_true_iff.mp h).1
  cases h' : g.op <;> simp_all [isAnd]

theorem gate_mix (b y z : ℕ → Bool) (hz : ∀ i, z i = (b i || y i)) (g : Gate) (hg : legal g) :
    g.op.eval (g.inputs.map z) = (g.op.eval (g.inputs.map b) ||
      (reduced b g).op.eval ((reduced b g).inputs.map y)) := by
  rcases g with ⟨op,pins⟩
  rcases hg with ⟨hop,hlen⟩
  change op = .and ∨ op = .or at hop
  change pins.length ≤ 2 at hlen
  cases pins with
  | nil =>
    rcases hop with rfl|rfl <;> rfl
  | cons i pins =>
    cases pins with
    | nil =>
      rcases hop with rfl|rfl <;> cases eb : b i <;> cases ey : y i <;>
        simp [reduced,fired,isAnd,GateOp.eval,hz,eb,ey]
    | cons j pins =>
      cases pins with
      | nil =>
        rcases hop with rfl|rfl <;> cases eb : b i <;> cases ec : b j <;>
          cases ey : y i <;> cases ez : y j <;> simp [reduced,fired,isAnd,GateOp.eval,hz,eb,ec,ey,ez]
      | cons k ks => simp at hlen

def Mix (b y z : List Bool) : Prop :=
  b.length=y.length ∧ b.length=z.length ∧ ∀ i, rd z i = (rd b i || rd y i)

theorem mix_step (b y z : List Bool) (h : Mix b y z) (g : Gate) (hg : legal g) :
    Mix (step b g) (step y (reduced (rd b) g)) (step z g) := by
  obtain ⟨hy,hz,h⟩ := h
  refine ⟨by simp [step,hy],by simp [step,hz],?_⟩
  intro i
  rcases Nat.lt_trichotomy i b.length with lo|mid|hi
  · simp only [rd,step,List.getD_append _ _ _ _ lo,List.getD_append _ _ _ _ (hy ▸ lo),
      List.getD_append _ _ _ _ (hz ▸ lo)]
    exact h i
  · have iy := mid.trans hy
    have iz := mid.trans hz
    have lastread (L : List Bool) (v : Bool) (j : ℕ) (e : j=L.length) :
        (L++[v]).getD j false = v := by rw [e,getD_snoc_eq]
    simp only [rd,step]
    rw [lastread z _ i iz,lastread b _ i mid,lastread y _ i iy]
    exact gate_mix (rd b) (rd y) (rd z) h g hg
  · unfold rd step
    rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    rfl

theorem mix_run (gs : List Gate) (b y z : List Bool) (hg : ∀ g ∈ gs, legal g) (h : Mix b y z) :
    Mix (gs.foldl step b) ((reduceList b gs).foldl step y) (gs.foldl step z) := by
  induction gs generalizing b y z with
  | nil => exact h
  | cons g gs ih =>
    exact ih _ _ _ (fun t ht => hg t (by simp [ht])) (mix_step _ _ _ h g (hg g (by simp)))

theorem mix_inputs {n : ℕ} (b y : Fin n → Bool) :
    Mix (List.ofFn b) (List.ofFn y) (List.ofFn fun i => b i || y i) := by
  refine ⟨by simp,by simp,?_⟩
  intro j
  by_cases hj : j < n
  · simp [rd,hj]
  · simp [rd,hj]

theorem eval_or {n : ℕ} (C : Circuit) (b x : Fin n → Bool) (hg : ∀ g ∈ C.gates, legal g) :
    C.eval (List.ofFn fun i => b i || x i) = (C.eval (List.ofFn b) ||
      (⟨reduceList (List.ofFn b) C.gates,C.output⟩ : Circuit).eval (List.ofFn x)) :=
  (mix_run _ _ _ _ hg (mix_inputs b x)).2.2 C.output

theorem still_and (b : List Bool) (gs : List Gate) (j : ℕ) (g : Gate)
    (atj : (reduceList b gs)[j]? = some g) (op : g.op = GateOp.and) :
    gs[j]? = some g := by
  induction gs generalizing b j with
  | nil => simp [reduceList] at atj
  | cons z zs ih =>
    cases j with
    | zero =>
      have eq : reduced (rd b) z = g := Option.some.inj atj
      by_cases fire : fired (rd b) z = true
      · rw [show reduced (rd b) z = ⟨.or,_⟩ from ite_eq_left fire] at eq
        rw [← eq] at op
        contradiction
      · simpa [reduced,fire] using congrArg some eq
    | succ j => exact ih (step b z) j atj

theorem same_or_dropped (b : List Bool) (gs : List Gate) :
    reduceList b gs = gs ∨ ∃ (j : ℕ) (a k : Gate), gs[j]? = some a ∧
      (reduceList b gs)[j]? = some k ∧ a.op = GateOp.and ∧ k.op = GateOp.or := by
  induction gs generalizing b with
  | nil => exact Or.inl rfl
  | cons a gs ih =>
    by_cases fire : fired (rd b) a = true
    · right
      refine ⟨0,a,reduced (rd b) a,rfl,rfl,a_fired fire,?_⟩
      simp [reduced,fire]
    · rcases ih (step b a) with eq|⟨j,g,k,old,new,yes,no⟩
      · left
        simp [reduceList,reduced,fire,eq]
      · exact Or.inr ⟨j+1,g,k,old,new,yes,no⟩

def maskPin {n : ℕ} (keep : Fin n → Bool) (i : Fin n) : Fin (n+1) :=
  if keep i then i.castSucc else Fin.last n

def masked {n : ℕ} (keep : Fin n → Bool) (C : Circuit) : Circuit :=
  let R := relabel n (n+1) (maskPin keep) C
  ⟨⟨.or,[]⟩::R.gates,R.output⟩

theorem mask_eval {n : ℕ} (keep x : Fin n → Bool) (C : Circuit) :
    (masked keep C).eval (List.ofFn x) = C.eval (List.ofFn fun i => keep i && x i) := by
  let y : Fin (n+1) → Bool := Fin.snoc x false
  have cast (i : Fin n) : y (maskPin keep i) = (keep i && x i) := by
    cases h : keep i <;> simp [maskPin,h,y]
  have ys : List.ofFn y = List.ofFn x ++ [false] := by
    rw [List.ofFn_succ']
    simp [y,Fin.snoc_castSucc,Fin.snoc_last,Function.comp_def]
  have init : step (List.ofFn x) ⟨.or,[]⟩ = List.ofFn y := by rw [ys]; rfl
  have ev := (rel_fold n (n+1) (maskPin keep) C.gates _ _ (rel_init _ _ _ y)).2.2 C.output
  have eq : y ∘ maskPin keep = (fun i => keep i && x i) := funext cast
  rw [eq] at ev
  change ((C.gates.map (relGate n (n+1) (maskPin keep))).foldl step
    (step (List.ofFn x) ⟨.or,[]⟩)).getD _ false = _
  rw [init]
  exact ev

theorem mask_legal {n : ℕ} (keep : Fin n → Bool) (C : Circuit) (h : ∀ g ∈ C.gates, legal g) :
    ∀ g ∈ (masked keep C).gates, legal g := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl|hm
  · exact ⟨Or.inr rfl,by decide⟩
  · obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hm
    exact ⟨(h k hk).1,by simpa [relGate] using (h k hk).2⟩

theorem mask_count {n : ℕ} (keep : Fin n → Bool) (C : Circuit) (A : Finset ℕ)
    (cert : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and → j ∈ A) :
    ∀ j g, (masked keep C).gates[j]? = some g → g.op = GateOp.and → j ∈ A.image Nat.succ := by
  intro j g atj op
  cases j with
  | zero =>
    have eq : (⟨.or,[]⟩ : Gate) = g := Option.some.inj atj
    rw [←eq] at op
    contradiction
  | succ j =>
    change ((C.gates.map (relGate n (n+1) (maskPin keep)))[j]?) = some g at atj
    rw [List.getElem?_map] at atj
    obtain ⟨src,old,rfl⟩ := Option.map_eq_some_iff.mp atj
    exact Finset.mem_image.mpr ⟨j,cert _ _ old op,rfl⟩

def point {n : ℕ} (r i : Fin n) : Bool := decide (i=r)

def outside {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r i : Fin n) : Bool :=
  decide (i ≠ r ∧ ¬ G.Adj r i)

theorem edge_mask {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (r : Fin n) (x : Fin n → Bool) :
    (∃ u v, G.Adj u v ∧ (point r u || (outside G r u && x u)) = true ∧
      (point r v || (outside G r v && x v)) = true) ↔
    ∃ u v, G.Adj u v ∧ u ≠ r ∧ v ≠ r ∧ ¬ G.Adj r u ∧ ¬ G.Adj r v ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨u,v,edge,hu,hv⟩
    have nu : u ≠ r := by
      rintro rfl
      simp [point,outside,edge.ne.symm,edge] at hv
    have nv : v ≠ r := by
      rintro rfl
      simp [point,outside,edge.ne,edge.symm] at hu
    have ux : ¬ G.Adj r u ∧ x u = true := by simpa [point,outside,nu] using hu
    have vx : ¬ G.Adj r v ∧ x v = true := by simpa [point,outside,nv] using hv
    exact ⟨u,v,edge,nu,nv,ux.1,vx.1,ux.2,vx.2⟩
  · rintro ⟨u,v,edge,nu,nv,ou,ov,hu,hv⟩
    exact ⟨u,v,edge,by simp [point,outside,nu,ou,hu],by simp [point,outside,nv,ov,hv]⟩

end PEqualNP.Outside.L_meta_150

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_150 in
theorem PEqualNP.Outside.L_meta_150 : ∀ (n a : ℕ) (G : SimpleGraph (Fin n)) (r : Fin n), (∃ w : Fin n, G.Adj r w) → (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ a + 1 ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) ∧ ∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ (∃ A : Finset ℕ, A.card ≤ a ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → j ∈ A) ∧ ∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ u ≠ r ∧ v ≠ r ∧ ¬ G.Adj r u ∧ ¬ G.Adj r v ∧ x u = true ∧ x v = true) := by
  classical
  rintro n a G r ⟨w,edge⟩ ⟨C,mono,⟨A,count,cert⟩,correct⟩
  have legalC : ∀ g ∈ C.gates, legal g := fun g hg => mono g hg
  have single (i : Fin n) : C.eval (List.ofFn (point i)) = false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    obtain ⟨u,v,e,hu,hv⟩ := (correct _).mp yes
    have eu : u=i := by simpa [point] using hu
    have ev : v=i := by simpa [point] using hv
    exact e.ne (eu.trans ev.symm)
  have both : C.eval (List.ofFn fun i => point r i || point w i) = true :=
    (correct _).mpr ⟨r,w,edge,by simp [point],by simp [point]⟩
  let B := List.ofFn (point r)
  let D : Circuit := ⟨reduceList B C.gates,C.output⟩
  have changed : reduceList B C.gates ≠ C.gates := by
    intro eq
    have mix := eval_or C (point r) (point w) legalC
    change C.eval _ = (C.eval _ || (⟨reduceList B C.gates,C.output⟩ : Circuit).eval _) at mix
    rw [eq,both,single r] at mix
    change true = (false || C.eval (List.ofFn (point w))) at mix
    rw [single w] at mix
    contradiction
  obtain ⟨j,g,k,old,new,yes,no⟩ := (same_or_dropped B C.gates).resolve_left changed
  have hj : j ∈ A := cert _ _ old yes
  have dcert : ∀ u v, D.gates[u]? = some v → v.op = GateOp.and → u ∈ A.erase j := by
    intro u v huv hv
    apply Finset.mem_erase.mpr
    refine ⟨?_,cert _ _ (still_and B C.gates u v huv hv) hv⟩
    rintro rfl
    have eq : v = k := Option.some.inj (huv.symm.trans new)
    rw [eq,no] at hv
    contradiction
  let keep := outside G r
  refine ⟨masked keep D,mask_legal keep D (reduceList_legal B C.gates legalC),?_,?_⟩
  · refine ⟨(A.erase j).image Nat.succ,?_,mask_count keep D (A.erase j) dcert⟩
    have hi := Finset.card_image_le (s := A.erase j) (f := Nat.succ)
    have he := Finset.card_erase_of_mem hj
    omega
  · intro x
    rw [mask_eval]
    have mix := eval_or C (point r) (fun i => keep i && x i) legalC
    rw [single r,Bool.false_or] at mix
    change D.eval (List.ofFn (fun i => keep i && x i)) = true ↔ _
    rw [← mix,correct]
    exact edge_mask G r x
