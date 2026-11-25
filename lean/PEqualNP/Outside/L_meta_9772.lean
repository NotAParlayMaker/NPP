import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9772_aux
namespace DagTools
open Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def gop : Bool→ Bool→ Bool→ Bool
  | true,a,b=>a && b
  | false,a,b=>a || b
@[simp] theorem gop_true (a b : Bool) : gop true a b = (a && b):=rfl
@[simp] theorem gop_false (a b : Bool) : gop false a b = (a || b):=rfl
abbrev Dag:=List (Bool×ℕ×ℕ)
def tag (D : Dag) (j : ℕ) : Bool:=(D.getD j (false,0,0)).1
def opA (D : Dag) (j : ℕ) : ℕ:=(D.getD j (false,0,0)).2.1
def opB (D : Dag) (j : ℕ) : ℕ:=(D.getD j (false,0,0)).2.2
def vg (w : List Bool) (g : Bool×ℕ×ℕ) : List Bool:=
  w ++ [gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]
def wl (D : Dag) (w : List Bool) : List Bool:=D.foldl vg w
def val (D : Dag) {n : ℕ} (x : Fin n→ Bool) (w : ℕ) : Bool:=
  (wl D (List.ofFn x)).getD w false
def za (n : ℕ) (D : Dag) : Prop:=
  ∀ j,j < D.length→ opA D j < n + j∧opB D j < n + j∧opA D j≠opB D j
def zq (D : Dag) (w : ℕ) : Finset ℕ:=
  (Finset.range D.length).filter (fun j=>opA D j = w∨opB D j = w)
def zd (D : Dag) (w : ℕ) : ℕ:=(zq D w).card
def Live (n : ℕ) (D : Dag) : Prop:=∀ w,w + 1 < n + D.length→ 1≤ zd D w
def z0 (n : ℕ) (D : Dag) : Prop:=za n D∧Live n D∧D≠[]
def qc (n : ℕ) (D : Dag) : ℕ:=n + D.length - 1
def single {n : ℕ} (v : Fin n) : Fin n→ Bool:=fun i=>decide (i = v)
def supp (n : ℕ) (D : Dag) (w : ℕ) : Finset (Fin n):=
  Finset.univ.filter (fun v=>val D (single v) w = true)
def zw (D : Dag) (K : Finset ℕ) : ℕ:=∑ w∈K,(zd D w - 1)
def inner (n : ℕ) (D : Dag) : Finset ℕ:=Finset.range (n + D.length - 1)
def vl (n : ℕ) (D : Dag) : ℕ:=zw D (inner n D)
def zu (n : ℕ) (D : Dag) : ℕ:=
  zw D ((inner n D).filter (fun w=>(supp n D w).Nonempty))
def qd (n : ℕ) (D : Dag) : ℕ:=
  zw D ((inner n D).filter (fun w=>¬ (supp n D w).Nonempty))
def branchW (n : ℕ) (D : Dag) : Finset ℕ:=
  (Finset.range (n + D.length)).filter (fun w=>2≤ zd D w)
def z6 (n : ℕ) (D : Dag) : Finset (Fin n):=(branchW n D).biUnion (supp n D)
def z1 (n : ℕ) (D : Dag) : Finset (Fin n):=Finset.univ \ z6 n D
def units (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ,ℕ):=
  (inner n D).sigma (fun w=>Finset.range (zd D w - 1))
def wo (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ,ℕ):=
  (units n D).filter (fun u=>(supp n D u.1).Nonempty)
def arcs (D : Dag) : Finset (ℕ×Bool):=Finset.range D.length×ˢ Finset.univ
def src (D : Dag) (e : ℕ×Bool) : ℕ:=if e.2 = true then opB D e.1 else opA D e.1
def zk (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (ℕ×Bool):=
  (arcs D).filter (fun e=>src D e∈K∧n + e.1∉K)
def merges (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset ℕ:=
  (Finset.range D.length).filter (fun j=>n + j∈K∧opA D j∈K∧opB D j∈K)
def sources (n : ℕ) (K : Finset ℕ) : Finset ℕ:=K.filter (fun w=>w < n)
def zb (n : ℕ) (D : Dag) (T : Finset (Fin n)) : Finset ℕ:=
  (Finset.range (n + D.length)).filter (fun w=>(supp n D w∩T).Nonempty)
def zx (n : ℕ) (D : Dag) (x y : Fin n) : Finset ℕ:=
  (Finset.range (n + D.length)).filter (fun w=>x∈supp n D w∧y∉supp n D w)
def qe (n : ℕ) (D : Dag) (b : Fin n→ ℕ) : Prop:=
  ∀ v∈z6 n D,2≤ zd D (b v)∧supp n D (b v) = {v}
def reservedUnits (n : ℕ) (D : Dag) (b : Fin n→ ℕ) : Finset (Σ _ : ℕ,ℕ):=
  (z6 n D).image (fun v=>(⟨b v,0⟩ : Σ _ : ℕ,ℕ))
def z5 (n : ℕ) (D : Dag) (b : Fin n→ ℕ) : Finset (Σ _ : ℕ,ℕ):=
  wo n D \ reservedUnits n D b
theorem tag_eq (D : Dag) (j : ℕ) (h : j < D.length) : tag D j = (D[j]).1:=by
  simp [tag,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]
theorem opA_eq (D : Dag) (j : ℕ) (h : j < D.length) : opA D j = (D[j]).2.1:=by
  simp [opA,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]
theorem opB_eq (D : Dag) (j : ℕ) (h : j < D.length) : opB D j = (D[j]).2.2:=by
  simp [opB,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h]
theorem z4y (g : Bool×ℕ×ℕ) (D : Dag) (w : List Bool) :
    wl (g :: D) w = wl D (vg w g):=rfl
theorem z0j (D E : Dag) (w : List Bool) : wl (D ++ E) w = wl E (wl D w):=by
  simp [wl,List.foldl_append]
theorem z0w (w : List Bool) (g : Bool×ℕ×ℕ) : (vg w g).length = w.length + 1:=by
  simp [vg]
theorem z0i (D : Dag) : ∀ w : List Bool,(wl D w).length = w.length + D.length:=by
  induction D with
  | nil=>intro w;simp [wl]
  | cons g D ih=>intro w;rw [z4y,ih,z0w];simp;omega
theorem z27 (w : List Bool) (g : Bool×ℕ×ℕ) (i : ℕ) (h : i < w.length) :
    (vg w g).getD i false = w.getD i false:=by
  simp [vg,List.getD_eq_getElem?_getD,List.getElem?_append_left h]
theorem z2d (D : Dag) : ∀ (w : List Bool) (i : ℕ),i < w.length→
    (wl D w).getD i false = w.getD i false:=by
  induction D with
  | nil=>intro w i _;rfl
  | cons g D ih=>
    intro w i h;rw [z4y,ih _ _ (by rw [z0w];omega),z27 _ _ _ h]
theorem getD_ge (w : List Bool) (i : ℕ) (h : w.length≤ i) : w.getD i false = false:=by
  simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none h]
theorem z1d (w : List Bool) (g : Bool×ℕ×ℕ) :
    (vg w g).getD w.length false = gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false):=by
  simp [vg,List.getD_eq_getElem?_getD]
theorem z4x (D : Dag) (w : List Bool) (j : ℕ) (hj : j < D.length) :
    (wl D w).getD (w.length + j) false =
      gop (tag D j) ((wl (D.take j) w).getD (opA D j) false)
        ((wl (D.take j) w).getD (opB D j) false):=by
  have hsplit : D = D.take j ++ D[j] :: D.drop (j + 1):=by simp
  have hlen : (wl (D.take j) w).length = w.length + j:=by
    rw [z0i,List.length_take];omega
  rw [tag_eq D j hj,opA_eq D j hj,opB_eq D j hj]
  conv_lhs=>rw [hsplit,z0j,z4y]
  rw [z2d _ _ _ (by rw [z0w,hlen];omega),← hlen,z1d]
theorem z0x (D : Dag) (w : List Bool) (j i : ℕ) (hi : i < w.length + j)
    (hj : j≤ D.length) :
    (wl (D.take j) w).getD i false = (wl D w).getD i false:=by
  have hsplit : D = D.take j ++ D.drop j:=by simp
  have hlen : (wl (D.take j) w).length = w.length + j:=by
    rw [z0i,List.length_take];omega
  conv_rhs=>rw [hsplit,z0j]
  rw [z2d (D.drop j) (wl (D.take j) w) i (by rw [hlen];exact hi)]
theorem val_input (D : Dag) {n : ℕ} (x : Fin n→ Bool) (i : ℕ) (h : i < n) :
    val D x i = x ⟨i,h⟩:=by
  unfold val;rw [z2d _ _ _ (by simpa using h)];simp [List.getD_eq_getElem?_getD,h]
theorem val_ge (D : Dag) {n : ℕ} (x : Fin n→ Bool) (w : ℕ) (h : n + D.length≤ w) :
    val D x w = false:=by
  unfold val;exact getD_ge _ _ (by rw [z0i];simpa using h)
theorem val_take (D : Dag) {n : ℕ} (x : Fin n→ Bool) (k w : ℕ) (hw : w < n + k)
    (hk : k≤ D.length) : val (D.take k) x w = val D x w:=by
  unfold val;exact z0x D _ k w (by simpa using hw) hk
theorem val_gate {n : ℕ} {D : Dag} (hS : za n D) (x : Fin n→ Bool) (j : ℕ)
    (hj : j < D.length) :
    val D x (n + j) = gop (tag D j) (val D x (opA D j)) (val D x (opB D j)):=by
  obtain ⟨ha,hb,-⟩:=hS j hj;have h:=z4x D (List.ofFn x) j hj;simp only [List.length_ofFn] at h;unfold val;rw [h,z0x D _ j _ (by simpa using ha) hj.le,
    z0x D _ j _ (by simpa using hb) hj.le]
theorem val_unique {n : ℕ} {D : Dag} (hS : za n D) (x : Fin n→ Bool) (f : ℕ→ Bool)
    (hin : ∀ i (h : i < n),f i = x ⟨i,h⟩)
    (hg : ∀ j,j < D.length→ f (n + j) = gop (tag D j) (f (opA D j)) (f (opB D j))) :
    ∀ w,w < n + D.length→ val D x w = f w:=by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih=>
    intro hw
    by_cases hn : w < n
    · rw [val_input D x w hn,hin w hn]
    · obtain ⟨j,rfl⟩ : ∃ j,w = n + j:=⟨w - n,by omega⟩
      have hj : j < D.length:=by omega
      obtain ⟨ha,hb,-⟩:=hS j hj;rw [val_gate hS x j hj,hg j hj,ih _ ha (by omega),ih _ hb (by omega)]
abbrev Ref:=Bool ⊕ ℕ
def refVal (W : List Bool) : Ref→ Bool
  | Sum.inl b=>b
  | Sum.inr k=>W.getD k false
def z8 (m : List Ref) (i : ℕ) : Ref:=m.getD i (Sum.inl false)
def zy (t : Bool) : Ref→ Ref→ Ref ⊕ (ℕ×ℕ)
  | Sum.inl a,r=>Sum.inl (if a = t then r else Sum.inl a)
  | Sum.inr i,Sum.inl b=>Sum.inl (if b = t then Sum.inr i else Sum.inl b)
  | Sum.inr i,Sum.inr j=>if i = j then Sum.inl (Sum.inr i) else Sum.inr (i,j)
def x2 : GateOp→ Bool
  | GateOp.and=>true
  | _=>false
def y2 (n : ℕ) (st : List Ref×Dag) (g : Gate) : List Ref×Dag:=
  match g.inputs with
  | []=>(st.1 ++ [Sum.inl (x2 g.op)],st.2)
  | [a]=>(st.1 ++ [z8 st.1 a],st.2)
  | a :: b :: _=>
    match zy (x2 g.op) (z8 st.1 a) (z8 st.1 b) with
    | Sum.inl r=>(st.1 ++ [r],st.2)
    | Sum.inr p=>(st.1 ++ [Sum.inr (n + st.2.length)],st.2 ++ [(x2 g.op,p.1,p.2)])
def wb (B : ℕ) : Ref→ Prop
  | Sum.inl _=>True
  | Sum.inr k=>k < B
def z24 (n : ℕ) (st : List Ref×Dag) : Prop:=
  za n st.2∧∀ r∈st.1,wb (n + st.2.length) r
theorem z47 {B B' : ℕ} (h : B≤ B') (r : Ref) (hr : wb B r) : wb B' r:=by
  rcases r with b | k
  · trivial
  · exact lt_of_lt_of_le hr h
theorem vd (W : List Bool) (m : List Ref) (i : ℕ) :
    refVal W (z8 m i) = (m.map (refVal W)).getD i false:=by
  simp only [z8,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases m[i]? <;> rfl
theorem yw (B : ℕ) (m : List Ref) (hm : ∀ r∈m,wb B r) (i : ℕ) :
    wb B (z8 m i):=by
  simp only [z8,List.getD_eq_getElem?_getD]
  rcases h : m[i]? with _ | r
  · trivial
  · exact hm r (List.mem_of_getElem? h)
theorem z1i (W : List Bool) (g : Bool×ℕ×ℕ) (r : Ref) (hr : wb W.length r) :
    refVal (vg W g) r = refVal W r:=by
  rcases r with b | k
  · rfl
  · exact z27 W g k hr
theorem z3h (t : Bool) (W : List Bool) (a b r : Ref) (h : zy t a b = Sum.inl r) :
    refVal W r = gop t (refVal W a) (refVal W b):=by
  rcases a with a | i
  · simp only [zy,Sum.inl.injEq] at h
    subst h
    cases t <;> cases a <;> simp [refVal]
  · rcases b with b | j
    · simp only [zy,Sum.inl.injEq] at h
      subst h
      cases t <;> cases b <;> simp [refVal]
    · simp only [zy] at h
      split_ifs at h with hij
      simp only [Sum.inl.injEq] at h;subst h;subst hij
      cases t <;> simp [refVal]
theorem z4a (B : ℕ) (t : Bool) (a b r : Ref) (ha : wb B a) (hb : wb B b)
    (h : zy t a b = Sum.inl r) : wb B r:=by
  rcases a with a | i
  · simp only [zy,Sum.inl.injEq] at h
    subst h;split_ifs
    · exact hb
    · trivial
  · rcases b with b | j
    · simp only [zy,Sum.inl.injEq] at h
      subst h;split_ifs
      · exact ha
      · trivial
    · simp only [zy] at h
      split_ifs at h
      simp only [Sum.inl.injEq] at h;subst h;exact ha
theorem z08 (t : Bool) (a b : Ref) (p : ℕ×ℕ) (h : zy t a b = Sum.inr p) :
    a = Sum.inr p.1∧b = Sum.inr p.2∧p.1≠p.2:=by
  rcases a with a | i
  · simp [zy] at h
  · rcases b with b | j
    · simp [zy] at h
    · simp only [zy] at h
      split_ifs at h with hij
      cases h
      exact ⟨rfl,rfl,hij⟩
theorem z6g (op : GateOp) (hop : op∈({GateOp.and,GateOp.or} : Set GateOp)) :
    op.eval [] = x2 op:=by
  rcases hop with rfl | rfl <;> rfl
theorem z6f (op : GateOp) (hop : op∈({GateOp.and,GateOp.or} : Set GateOp)) (u : Bool) :
    op.eval [u] = u:=by
  rcases hop with rfl | rfl <;> simp [GateOp.eval]
theorem z5i (op : GateOp) (hop : op∈({GateOp.and,GateOp.or} : Set GateOp))
    (u v : Bool) : op.eval [u,v] = gop (x2 op) u v:=by
  rcases hop with rfl | rfl <;> simp [GateOp.eval,x2]
theorem z07 (D E : Dag) (k : ℕ) (h : k < D.length) :
    (D ++ E).getD k (false,0,0) = D.getD k (false,0,0):=by
  simp [List.getD_eq_getElem?_getD,List.getElem?_append_left h]
theorem z2z (D : Dag) (g : Bool×ℕ×ℕ) :
    (D ++ [g]).getD D.length (false,0,0) = g:=by
  simp [List.getD_eq_getElem?_getD]
theorem z1w {n : ℕ} {D : Dag} (hS : za n D) (t : Bool) (i j : ℕ)
    (hi : i < n + D.length) (hj : j < n + D.length) (hij : i≠j) :
    za n (D ++ [(t,i,j)]):=by
  intro k hk;simp only [List.length_append,List.length_singleton] at hk
  by_cases hk' : k < D.length
  · simp only [opA,opB,z07 D _ k hk']
    exact hS k hk'
  · have hkD : k = D.length:=by omega
    subst hkD;simp only [opA,opB,z2z];exact ⟨hi,hj,hij⟩
theorem z1v {n : ℕ} {D : Dag} (hS : za n D) (k : ℕ) : za n (D.take k):=by
  intro j hj;simp only [List.length_take] at hj;have hj1 : j < k:=by omega
  have hj2 : j < D.length:=by omega
  have e : (D.take k).getD j (false,0,0) = D.getD j (false,0,0):=by
    simp [List.getD_eq_getElem?_getD,hj1]
  simp only [opA,opB,e];exact hS j hj2
theorem z58 (n : ℕ) (st : List Ref×Dag) (g : Gate)
    (hg : g.op∈({GateOp.and,GateOp.or} : Set GateOp)∧g.inputs.length≤ 2)
    (h : z24 n st) :
    z24 n (y2 n st g)∧(y2 n st g).2.length≤ st.2.length + 1∧
    ∀ (x : Fin n→ Bool) (w : List Bool),st.1.map (refVal (wl st.2 (List.ofFn x))) = w→
      (y2 n st g).1.map (refVal (wl (y2 n st g).2 (List.ofFn x))) =
        w ++ [g.op.eval (g.inputs.map fun i=>w.getD i false)]:=by
  obtain ⟨m,D⟩:=st;obtain ⟨op,ins⟩:=g;obtain ⟨hop,hlen⟩:=hg;obtain ⟨hS,hok⟩:=h;dsimp only at hS hok hop hlen ⊢
  rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,rest⟩⟩⟩
  · refine ⟨⟨hS,?_⟩,by simp [y2],fun x w hw=>?_⟩
    · intro r hr
      simp only [y2,List.mem_append,List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hok r hr
      · trivial
    · subst hw
      simp only [y2,List.map_append,List.map_cons,List.map_nil,refVal,z6g op hop]
  · refine ⟨⟨hS,?_⟩,by simp [y2],fun x w hw=>?_⟩
    · intro r hr
      simp only [y2,List.mem_append,List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hok r hr
      · exact yw _ m hok a
    · subst hw
      simp only [y2,List.map_append,List.map_cons,List.map_nil,z6f op hop,
        vd]
  · have hla:=yw _ m hok a
    have hlb:=yw _ m hok b
    rcases hc : zy (x2 op) (z8 m a) (z8 m b) with r | p
    · refine ⟨⟨by simpa only [y2,hc] using hS,?_⟩,by simp [y2,hc],
        fun x w hw=>?_⟩
      · intro r' hr
        simp only [y2,hc,List.mem_append,List.mem_singleton] at hr ⊢
        rcases hr with hr | rfl
        · exact hok r' hr
        · exact z4a _ _ _ _ _ hla hlb hc
      · subst hw
        simp only [y2,hc,List.map_append,List.map_cons,List.map_nil,z5i op hop,
          z3h _ (wl D (List.ofFn x)) _ _ _ hc,vd]
    · obtain ⟨ea,eb,hne⟩:=z08 _ _ _ _ hc
      rw [ea] at hla;rw [eb] at hlb;have hS':=z1w hS (x2 op) p.1 p.2 hla hlb hne
      refine ⟨⟨by simpa only [y2,hc] using hS',?_⟩,by simp [y2,hc],
        fun x w hw=>?_⟩
      · intro r' hr
        simp only [y2,hc,List.mem_append,List.mem_singleton,List.length_append,
          List.length_singleton] at hr ⊢
        rcases hr with hr | rfl
        · exact z47 (by omega) r' (hok r' hr)
        · show n + D.length < n + (D.length + 1)
          omega
      · subst hw
        have hWlen : (wl D (List.ofFn x)).length = n + D.length:=by
          rw [z0i,List.length_ofFn]
        have hW' : wl (D ++ [(x2 op,p.1,p.2)]) (List.ofFn x) =
            vg (wl D (List.ofFn x)) (x2 op,p.1,p.2):=by
          rw [z0j];rfl
        have h1 : m.map (refVal (vg (wl D (List.ofFn x)) (x2 op,p.1,p.2))) =
            m.map (refVal (wl D (List.ofFn x))):=
          List.map_congr_left (fun r hr=>z1i _ _ r (by rw [hWlen];exact hok r hr))
        have h2 : (vg (wl D (List.ofFn x)) (x2 op,p.1,p.2)).getD (n + D.length) false =
            gop (x2 op) ((m.map (refVal (wl D (List.ofFn x)))).getD a false)
              ((m.map (refVal (wl D (List.ofFn x)))).getD b false):=by
          rw [← hWlen,z1d,← vd,← vd,ea,eb];rfl
        simp only [y2,hc,hW',List.map_append,List.map_cons,List.map_nil,h1,refVal,
          h2,z5i op hop]
  · simp at hlen
theorem z59 (n : ℕ) (gs : List Gate)
    (hgs : ∀ g∈gs,g.op∈({GateOp.and,GateOp.or} : Set GateOp)∧g.inputs.length≤ 2) :
    ∀ st : List Ref×Dag,z24 n st→
      z24 n (gs.foldl (y2 n) st)∧
      (gs.foldl (y2 n) st).2.length≤ st.2.length + gs.length∧
      ∀ (x : Fin n→ Bool) (w : List Bool),st.1.map (refVal (wl st.2 (List.ofFn x))) = w→
        (gs.foldl (y2 n) st).1.map
            (refVal (wl (gs.foldl (y2 n) st).2 (List.ofFn x))) =
          gs.foldl (fun w g=>w ++ [g.op.eval (g.inputs.map fun i=>w.getD i false)]) w:=by
  induction gs with
  | nil=>intro st h;exact ⟨h,by simp,fun x w hw=>hw⟩
  | cons g gs ih=>
    intro st h;obtain ⟨h1,h2,h3⟩:=z58 n st g (hgs g (by simp)) h;obtain ⟨i1,i2,i3⟩:=ih (fun g' hg'=>hgs g' (by simp [hg'])) _ h1
    refine ⟨i1,?_,fun x w hw=>?_⟩
    · simp only [List.foldl_cons,List.length_cons];omega
    · simp only [List.foldl_cons];exact i3 x _ (h3 x w hw)
theorem z6p (n : ℕ) (x : Fin n→ Bool) :
    ((List.range n).map Sum.inr).map (refVal (wl ([] : Dag) (List.ofFn x))) = List.ofFn x:=by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map,List.length_range] at h1;simp [refVal,wl,List.getD_eq_getElem?_getD,h1]
theorem exists_strict_of_monotone2 {n : ℕ} (C : Circuit) (hmono : Monotone2 C) :
    (∃ b : Bool,∀ x : Fin n→ Bool,C.eval (List.ofFn x) = b)∨
    (∃ i : Fin n,∀ x : Fin n→ Bool,C.eval (List.ofFn x) = x i)∨
    (∃ D : Dag,za n D∧D≠[]∧D.length≤ C.size∧
      ∀ x : Fin n→ Bool,val D x (qc n D) = C.eval (List.ofFn x)):=by
  have h0 : z24 n ((List.range n).map Sum.inr,([] : Dag)):=by
    refine ⟨fun j hj=>absurd hj (by simp),fun r hr=>?_⟩
    simp only [List.mem_map,List.mem_range] at hr;obtain ⟨k,hk,rfl⟩:=hr
    simpa [wb] using hk
  obtain ⟨⟨hS,hok⟩,hlen,hsem⟩:=z59 n C.gates hmono _ h0
  generalize C.gates.foldl (y2 n) ((List.range n).map Sum.inr,([] : Dag)) = st
    at hS hok hlen hsem
  obtain ⟨m,D⟩:=st;dsimp only at hS hok hlen hsem;have hev : ∀ x : Fin n→ Bool,
      C.eval (List.ofFn x) = refVal (wl D (List.ofFn x)) (z8 m C.output):=by
    intro x;rw [vd,hsem x (List.ofFn x) (z6p n x)];rfl
  have hk:=yw _ m hok C.output
  rcases hr : z8 m C.output with b | k
  · exact Or.inl ⟨b,fun x=>by rw [hev x,hr];rfl⟩
  · rw [hr] at hk
    have hk' : k < n + D.length:=hk
    by_cases hkn : k < n
    · exact Or.inr (Or.inl ⟨⟨k,hkn⟩,fun x=>by rw [hev x,hr];exact val_input D x k hkn⟩)
    · have hl : (D.take (k - n + 1)).length = k - n + 1:=by
        rw [List.length_take];omega
      refine Or.inr (Or.inr ⟨D.take (k - n + 1),z1v hS _,?_,?_,fun x=>?_⟩)
      · intro h
        rw [h] at hl;simp at hl
      · rw [hl]
        simp only [List.length_nil,Nat.zero_add] at hlen;unfold Circuit.size;omega
      · have ho : qc n (D.take (k - n + 1)) = k:=by unfold qc;rw [hl];omega
        rw [ho,val_take D x (k - n + 1) k (by omega) (by omega),hev x,hr];rfl
theorem z18 {D : Dag} {w : ℕ} (h : zd D w = 0) (j : ℕ) (hj : j < D.length) :
    opA D j≠w∧opB D j≠w:=by
  unfold zd zq at h;rw [card_eq_zero,Finset.filter_eq_empty_iff] at h
  have:=h (Finset.mem_range.mpr hj)
  tauto
def z2y (c a : ℕ) : ℕ:=if c < a then a - 1 else a
def zs (c w : ℕ) : ℕ:=if w < c then w else w + 1
def wm (n j : ℕ) (D : Dag) : Dag:=
  (D.eraseIdx j).map (fun g=>(g.1,z2y (n + j) g.2.1,z2y (n + j) g.2.2))
theorem wc (n j : ℕ) (D : Dag) (hj : j < D.length) :
    (wm n j D).length = D.length - 1:=by
  simp [wm,List.length_eraseIdx,hj]
theorem z49 (n j : ℕ) (D : Dag) (k : ℕ) (hk : zs j k < D.length) :
    tag (wm n j D) k = tag D (zs j k)∧
    opA (wm n j D) k = z2y (n + j) (opA D (zs j k))∧
    opB (wm n j D) k = z2y (n + j) (opB D (zs j k)):=by
  have e : (wm n j D).getD k (false,0,0) =
      ((D.getD (zs j k) (false,0,0)).1,z2y (n + j) (D.getD (zs j k) (false,0,0)).2.1,
        z2y (n + j) (D.getD (zs j k) (false,0,0)).2.2):=by
    simp only [wm,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eraseIdx];unfold zs at hk ⊢
    split_ifs at hk ⊢ <;> simp [List.getElem?_eq_getElem hk]
  unfold tag opA opB;rw [e];exact ⟨rfl,rfl,rfl⟩
theorem z0d {n : ℕ} {D : Dag} (hS : za n D) (j : ℕ) (hj : j < D.length)
    (hf : zd D (n + j) = 0) : za n (wm n j D):=by
  intro k hk;rw [wc n j D hj] at hk;have hk' : zs j k < D.length:=by unfold zs;split_ifs <;> omega
  have hk2 : (k < j∧zs j k = k)∨(j≤ k∧zs j k = k + 1):=by
    unfold zs;split_ifs <;> omega
  obtain ⟨ha,hb,hab⟩:=hS _ hk';obtain ⟨ra,rb⟩:=z18 hf _ hk';obtain ⟨-,ea,eb⟩:=z49 n j D k hk';rw [ea,eb]
  generalize zs j k = k' at *
  generalize opA D k' = a at *
  generalize opB D k' = b at *
  refine ⟨?_,?_,?_⟩ <;> unfold z2y <;> split_ifs <;> omega
theorem z48 {n : ℕ} {D : Dag} (hS : za n D) (j : ℕ) (hj : j < D.length)
    (hf : zd D (n + j) = 0) (x : Fin n→ Bool) (w : ℕ) (hw : w < n + (D.length - 1)) :
    val (wm n j D) x w = val D x (zs (n + j) w):=by
  refine val_unique (z0d hS j hj hf) x (fun u=>val D x (zs (n + j) u))
    (fun i hi=>?_) (fun k hk=>?_) w (by rw [wc n j D hj];exact hw)
  · have e : zs (n + j) i = i:=by unfold zs;split_ifs <;> omega
    show val D x (zs (n + j) i) = x ⟨i,hi⟩
    rw [e];exact val_input D x i hi
  · rw [wc n j D hj] at hk
    have hk' : zs j k < D.length:=by unfold zs;split_ifs <;> omega
    obtain ⟨et,ea,eb⟩:=z49 n j D k hk';obtain ⟨ra,rb⟩:=z18 hf _ hk';have e1 : zs (n + j) (n + k) = n + zs j k:=by unfold zs;split_ifs <;> omega
    have e2 : ∀ a,a≠n + j→ zs (n + j) (z2y (n + j) a) = a:=by
      intro a ha;unfold zs z2y;split_ifs <;> omega
    show val D x (zs (n + j) (n + k)) = gop (tag (wm n j D) k)
      (val D x (zs (n + j) (opA (wm n j D) k)))
      (val D x (zs (n + j) (opB (wm n j D) k)))
    rw [e1,et,ea,eb,e2 _ ra,e2 _ rb];exact val_gate hS x _ hk'
theorem z5h {n : ℕ} (F : (Fin n→ Bool)→ Bool)
    (hess : ∀ i : Fin n,∃ x y : Fin n→ Bool,(∀ k,k≠i→ x k = y k)∧F x≠F y) :
    ∀ (s : ℕ) (D : Dag),D.length = s→ za n D→ D≠[]→
      (∀ x : Fin n→ Bool,val D x (qc n D) = F x)→
      ∃ D' : Dag,z0 n D'∧D'.length≤ s∧
        ∀ x : Fin n→ Bool,val D' x (qc n D') = F x:=by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih=>
    intro D hlen hS hne hD;have hpos : 0 < D.length:=List.length_pos_iff.mpr hne
    by_cases hL : Live n D
    · exact ⟨D,⟨hS,hL,hne⟩,hlen.le,hD⟩
    · obtain ⟨w,hw,hf0⟩ : ∃ w,w + 1 < n + D.length∧zd D w = 0:=by
        by_contra hcon
        exact hL (fun w hw=>by
          by_contra h0
          exact hcon ⟨w,hw,by omega⟩)
      by_cases hwn : w < n
      · exfalso
        obtain ⟨x,y,hxy,hFne⟩:=hess ⟨w,hwn⟩
        apply hFne
        rw [← hD x,← hD y];have hout : qc n D≠w:=by unfold qc;omega
        have key:=val_unique hS y (fun u=>if u = w then y ⟨w,hwn⟩ else val D x u)
          (fun i hi=>by
            by_cases hiw : i = w
            · subst hiw;simp
            · simp only [hiw,ite_false]
              rw [val_input D x i hi];exact hxy ⟨i,hi⟩ (fun h=>hiw (congrArg Fin.val h)))
          (fun j hj=>by
            obtain ⟨ha,hb⟩:=z18 hf0 j hj;have hnj : n + j≠w:=by omega
            simp only [hnj,ha,hb,ite_false];exact val_gate hS x j hj)
          (qc n D) (by unfold qc;omega)
        simp only [hout,ite_false] at key;exact key.symm
      · obtain ⟨j,rfl⟩ : ∃ j,w = n + j:=⟨w - n,by omega⟩
        have hj : j < D.length:=by omega
        have hl:=wc n j D hj;obtain ⟨D',h1,h2,h3⟩:=ih (D.length - 1) (by omega) (wm n j D) hl
          (z0d hS j hj hf0)
          (fun h=>by rw [h] at hl;simp at hl;omega)
          (fun x=>by
            have ho : qc n (wm n j D) = n + (D.length - 1) - 1:=by unfold qc;rw [hl]
            have hu : zs (n + j) (n + (D.length - 1) - 1) = qc n D:=by
              unfold zs qc;split_ifs <;> omega
            rw [ho,z48 hS j hj hf0 x _ (by omega),hu];exact hD x)
        exact ⟨D',h1,by omega,h3⟩
theorem exists_strictLive_of_strict {n : ℕ} (F : (Fin n→ Bool)→ Bool)
    (hess : ∀ i : Fin n,∃ x y : Fin n→ Bool,(∀ k,k≠i→ x k = y k)∧F x≠F y)
    (D : Dag) (hS : za n D) (hne : D≠[])
    (hD : ∀ x : Fin n→ Bool,val D x (qc n D) = F x) :
    ∃ D' : Dag,z0 n D'∧D'.length≤ D.length∧
      ∀ x : Fin n→ Bool,val D' x (qc n D') = F x:=
  z5h F hess D.length D rfl hS hne hD
theorem z1u {n : ℕ} (C : Circuit) (hmono : Monotone2 C)
    (hnc : ∀ b : Bool,∃ x : Fin n→ Bool,C.eval (List.ofFn x)≠b)
    (hnp : ∀ i : Fin n,∃ x : Fin n→ Bool,C.eval (List.ofFn x)≠x i)
    (hess : ∀ i : Fin n,∃ x y : Fin n→ Bool,(∀ k,k≠i→ x k = y k)∧
      C.eval (List.ofFn x)≠C.eval (List.ofFn y)) :
    ∃ D : Dag,z0 n D∧D.length≤ C.size∧
      ∀ x : Fin n→ Bool,val D x (qc n D) = C.eval (List.ofFn x):=by
  rcases exists_strict_of_monotone2 (n:=n) C hmono with
    ⟨b,hb⟩ | ⟨i,hi⟩ | ⟨D,hS,hne,hlen,hD⟩
  · obtain ⟨x,hx⟩:=hnc b
    exact absurd (hb x) hx
  · obtain ⟨x,hx⟩:=hnp i
    exact absurd (hi x) hx
  · obtain ⟨D',h1,h2,h3⟩:=
      exists_strictLive_of_strict (fun x=>C.eval (List.ofFn x)) hess D hS hne hD
    exact ⟨D',h1,by omega,h3⟩
section SurplusFlow
variable {n : ℕ} {D : Dag}
theorem qm {w : ℕ} : w∈inner n D↔w + 1 < n + D.length:=by
  unfold inner;rw [Finset.mem_range];omega
theorem qw (j : ℕ) : src D (j,false) = opA D j:=by simp [src]
theorem y5 (j : ℕ) : src D (j,true) = opB D j:=by simp [src]
theorem yv (hS : za n D) (w : ℕ) (h : n + D.length≤ w + 1) :
    zd D w = 0:=by
  unfold zd zq;rw [card_eq_zero,Finset.filter_eq_empty_iff];intro j hj;have hj2:=Finset.mem_range.mp hj
  have:=hS j hj2
  omega
theorem lt_of_fanout_pos (hS : za n D) {w : ℕ} (h : 1≤ zd D w) :
    w + 1 < n + D.length:=by
  by_contra hc
  have:=yv hS w (by omega)
  omega
theorem vi (P : ℕ×Bool→ Prop) [DecidablePred P] :
    ((arcs D).filter P).card = ∑ j∈Finset.range D.length,
      ((if P (j,false) then 1 else 0) + (if P (j,true) then 1 else 0)):=by
  rw [Finset.card_filter,arcs,Finset.sum_product]
  refine sum_congr rfl (fun j _=>?_)
  rw [Fintype.sum_bool,add_comm]
theorem z56 : (arcs D).card = 2 * D.length:=by
  simp [arcs,Finset.card_product,Nat.mul_comm]
theorem z68 (hS : za n D) (e : ℕ×Bool) (he : e∈arcs D) :
    src D e + 1 < n + D.length:=by
  obtain ⟨j,c⟩:=e;have hj : j < D.length:=by simpa [arcs] using he
  have:=hS j hj
  cases c
  · rw [qw];omega
  · rw [y5];omega
theorem z46 (hS : za n D) (w : ℕ) :
    zd D w = ((arcs D).filter (fun e=>src D e = w)).card:=by
  rw [vi,zd,zq,Finset.card_filter]
  refine sum_congr rfl (fun j hj=>?_)
  have:=(hS j (Finset.mem_range.mp hj)).2.2
  rw [qw,y5]
  split_ifs <;> omega
theorem z0p (hS : za n D) (K : Finset ℕ) :
    ∑ w∈K,zd D w = ((arcs D).filter (fun e=>src D e∈K)).card:=by
  rw [Finset.card_eq_sum_card_fiberwise (f:=src D)
    (s:=(arcs D).filter (fun e=>src D e∈K)) (t:=K)
    (fun e he=>Finset.mem_coe.mpr (mem_filter.mp (Finset.mem_coe.mp he)).2)]
  refine sum_congr rfl (fun w hw=>?_)
  rw [z46 hS,Finset.filter_filter]
  congr 1
  ext e
  simp only [mem_filter]
  constructor
  · rintro ⟨he,rfl⟩;exact ⟨he,hw,rfl⟩
  · rintro ⟨he,-,h⟩;exact ⟨he,h⟩
theorem vh {K : Finset ℕ} (hL : ∀ w∈K,1≤ zd D w) :
    zw D K + K.card = ∑ w∈K,zd D w:=by
  rw [zw,Finset.card_eq_sum_ones,← Finset.sum_add_distrib];exact sum_congr rfl (fun w hw=>Nat.sub_add_cancel (hL w hw))
theorem xo (h : z0 n D) : vl n D + n = D.length + 1:=by
  obtain ⟨hS,hL,hne⟩:=h;have hpos : 0 < D.length:=List.length_pos_iff.mpr hne;have h1 : zw D (inner n D) + (inner n D).card = ∑ w∈inner n D,zd D w:=
    vh (fun w hw=>hL w (qm.mp hw))
  have h2 : ∑ w∈inner n D,zd D w = 2 * D.length:=by
    rw [z0p hS,Finset.filter_true_of_mem,z56];intro e he;exact qm.mpr (z68 hS e he)
  have h3 : (inner n D).card = n + D.length - 1:=Finset.card_range _;unfold vl;omega
theorem x6 (n : ℕ) (D : Dag) : vl n D = zu n D + qd n D:=by
  unfold vl zu qd zw;exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
theorem live_reaches_out (h : z0 n D) (w : ℕ) (hw : w < n + D.length) :
    Relation.ReflTransGen (fun a b=>b < n + D.length∧n≤ b∧
      (opA D (b - n) = a∨opB D (b - n) = a)) w (qc n D):=by
  obtain ⟨hS,hL,-⟩:=h
  generalize hk : n + D.length - w = k
  induction k using Nat.strong_induction_on generalizing w with
  | _ k ih=>
    by_cases hlast : w + 1 = n + D.length
    · have hw2 : w = qc n D:=by unfold qc;omega
      rw [hw2]
    · obtain ⟨j,hj⟩:=card_pos.mp (hL w (by omega))
      simp only [zq,mem_filter,Finset.mem_range] at hj;have hs:=hS j hj.1
      refine Relation.ReflTransGen.head (b:=n + j) ⟨by omega,by omega,?_⟩
        (ih (n + D.length - (n + j)) (by omega) (n + j) (by omega) rfl)
      simpa using hj.2
theorem mem_supp {v : Fin n} {w : ℕ} : v∈supp n D w↔val D (single v) w = true:=by
  simp [supp]
theorem val_mono (hS : za n D) (x y : Fin n→ Bool) (hxy : ∀ i,x i = true→ y i = true)
    (w : ℕ) : val D x w = true→ val D y w = true:=by
  induction w using Nat.strong_induction_on with
  | _ w ih=>
    by_cases hn : w < n
    · rw [val_input D x w hn,val_input D y w hn];exact hxy _
    · by_cases hw : w < n + D.length
      · obtain ⟨j,rfl⟩ : ∃ j,w = n + j:=⟨w - n,by omega⟩
        have hj : j < D.length:=by omega
        obtain ⟨ha,hb,-⟩:=hS j hj;rw [val_gate hS x j hj,val_gate hS y j hj];have h1:=ih _ ha;have h2:=ih _ hb
        cases tag D j <;>
          simp only [gop_true,gop_false,Bool.and_eq_true,Bool.or_eq_true] <;> tauto
      · rw [val_ge D x w (by omega)];simp
theorem supp_input (D : Dag) (i : Fin n) : supp n D i.val = {i}:=by
  ext v
  rw [mem_supp,val_input D (single v) i.val i.isLt];simp [single,eq_comm]
theorem supp_ge (D : Dag) (w : ℕ) (h : n + D.length≤ w) : supp n D w = ∅:=by
  ext v
  simp [mem_supp,val_ge D (single v) w h]
theorem supp_gate (hS : za n D) (j : ℕ) (hj : j < D.length) :
    supp n D (n + j) = if tag D j = true then supp n D (opA D j)∩supp n D (opB D j)
      else supp n D (opA D j)∪supp n D (opB D j):=by
  ext v
  rw [mem_supp,val_gate hS _ j hj]
  cases tag D j <;> simp [mem_supp]
theorem z32 (h : z0 n D) (K : Finset ℕ) (hK : K⊆inner n D)
    (hpred : ∀ j,j < D.length→ n + j∈K→ opA D j∈K∨opB D j∈K) :
    (zk n D K).card + (merges n D K).card = (sources n K).card + zw D K:=by
  obtain ⟨hS,hL,-⟩:=h;have hKlt : ∀ w∈K,w + 1 < n + D.length:=fun w hw=>qm.mp (hK hw);have h1 : zw D K + K.card = ((arcs D).filter (fun e=>src D e∈K)).card:=by
    rw [← z0p hS,vh (fun w hw=>hL w (hKlt w hw))]
  have h2:=Finset.card_filter_add_card_filter_not
    (s:=(arcs D).filter (fun e=>src D e∈K)) (fun e : ℕ×Bool=>n + e.1∈K)
  rw [Finset.filter_filter,Finset.filter_filter] at h2;have h3 : ((arcs D).filter (fun e=>src D e∈K∧n + e.1∈K)).card =
      ((Finset.range D.length).filter (fun j=>n + j∈K)).card + (merges n D K).card:=by
    rw [vi,merges,Finset.card_filter,Finset.card_filter,
      ← Finset.sum_add_distrib]
    refine sum_congr rfl (fun j hj=>?_)
    have:=hpred j (Finset.mem_range.mp hj)
    rw [qw,y5]
    by_cases hj2 : n + j∈K <;> by_cases ha : opA D j∈K <;> by_cases hb : opB D j∈K <;>
      simp_all
  have h4 : K.card = (sources n K).card +
      ((Finset.range D.length).filter (fun j=>n + j∈K)).card:=by
    rw [← Finset.card_filter_add_card_filter_not (s:=K) (fun w=>w < n),sources]
    congr 1
    have himg : K.filter (fun w=>¬ w < n) =
        ((Finset.range D.length).filter (fun j=>n + j∈K)).image (fun j=>n + j):=by
      ext w
      simp only [mem_filter,mem_image,Finset.mem_range]
      constructor
      · rintro ⟨hw,hn⟩
        have:=hKlt w hw
        exact ⟨w - n,⟨by omega,by rwa [Nat.add_sub_cancel' (by omega)]⟩,by omega⟩
      · rintro ⟨j,⟨-,hj⟩,rfl⟩
        exact ⟨hj,by omega⟩
    rw [himg,card_image_of_injective _ (add_right_injective n)]
  unfold zk;omega
theorem z3q (T : Finset (Fin n))
    (hout : supp n D (qc n D)∩T = ∅) : zb n D T⊆inner n D:=by
  intro w hw;simp only [zb,mem_filter,Finset.mem_range] at hw;rw [qm]
  by_contra hc
  have hw2 : w = qc n D:=by unfold qc;omega
  rw [hw2,hout] at hw;exact not_nonempty_empty hw.2
theorem z26 (D : Dag) (T : Finset (Fin n)) :
    (sources n (zb n D T)).card = T.card:=by
  have himg : sources n (zb n D T) = T.image (fun v : Fin n=>v.val):=by
    ext w
    simp only [sources,zb,mem_filter,Finset.mem_range,mem_image]
    constructor
    · rintro ⟨⟨-,v,hv⟩,hw⟩
      have hs : supp n D w = {⟨w,hw⟩}:=supp_input D ⟨w,hw⟩;rw [hs,mem_inter,mem_singleton] at hv;exact ⟨v,hv.2,by rw [hv.1]⟩
    · rintro ⟨v,hv,rfl⟩
      refine ⟨⟨by have:=v.isLt;omega,v,?_⟩,v.isLt⟩
      rw [supp_input];simp [hv]
  rw [himg,card_image_of_injective _ Fin.val_injective]
theorem ym (h : z0 n D) (T : Finset (Fin n))
    (hout : supp n D (qc n D)∩T = ∅) :
    (zk n D (zb n D T)).card + (merges n D (zb n D T)).card =
      T.card + zw D (zb n D T):=by
  rw [← z26 D T]
  refine z32 h _ (z3q T hout) (fun j hj hK=>?_)
  obtain ⟨ha,hb,-⟩:=h.1 j hj;simp only [zb,mem_filter,Finset.mem_range] at hK ⊢;obtain ⟨v,hv⟩:=hK.2;rw [mem_inter,supp_gate h.1 j hj] at hv
  split_ifs at hv with ht
  · rw [mem_inter] at hv
    exact Or.inl ⟨by omega,v,mem_inter.mpr ⟨hv.1.1,hv.2⟩⟩
  · rw [mem_union] at hv
    rcases hv.1 with h1 | h1
    · exact Or.inl ⟨by omega,v,mem_inter.mpr ⟨h1,hv.2⟩⟩
    · exact Or.inr ⟨by omega,v,mem_inter.mpr ⟨h1,hv.2⟩⟩
theorem z31 (h : z0 n D) (x y : Fin n) (hxy : x≠y)
    (hout : x∉supp n D (qc n D)) :
    (zk n D (zx n D x y)).card + (merges n D (zx n D x y)).card =
      1 + zw D (zx n D x y):=by
  have hsub : zx n D x y⊆inner n D:=by
    intro w hw;simp only [zx,mem_filter,Finset.mem_range] at hw;rw [qm]
    by_contra hc
    have hw2 : w = qc n D:=by unfold qc;omega
    rw [hw2] at hw;exact hout hw.2.1
  have hsrc : sources n (zx n D x y) = {x.val}:=by
    ext w
    simp only [sources,zx,mem_filter,Finset.mem_range,mem_singleton]
    constructor
    · rintro ⟨⟨-,hx,-⟩,hw⟩
      have hs : supp n D w = {⟨w,hw⟩}:=supp_input D ⟨w,hw⟩;rw [hs,mem_singleton] at hx;rw [hx]
    · rintro rfl
      refine ⟨⟨by have:=x.isLt;omega,?_,?_⟩,x.isLt⟩
      · rw [supp_input];exact mem_singleton_self x
      · rw [supp_input,mem_singleton];exact fun hc=>hxy hc.symm
  have hfl:=z32 h _ hsub (fun j hj hK=>?_)
  · rw [hsrc,card_singleton] at hfl;exact hfl
  · obtain ⟨ha,hb,-⟩:=h.1 j hj
    simp only [zx,mem_filter,Finset.mem_range] at hK ⊢;obtain ⟨-,hx,hy⟩:=hK;rw [supp_gate h.1 j hj] at hx hy
    split_ifs at hx hy with ht
    · rw [mem_inter] at hx hy
      by_cases hya : y∈supp n D (opA D j)
      · exact Or.inr ⟨by omega,hx.2,fun hc=>hy ⟨hya,hc⟩⟩
      · exact Or.inl ⟨by omega,hx.1,hya⟩
    · rw [mem_union] at hx hy
      rcases hx with h1 | h1
      · exact Or.inl ⟨by omega,h1,fun hc=>hy (Or.inl hc)⟩
      · exact Or.inr ⟨by omega,h1,fun hc=>hy (Or.inr hc)⟩
theorem mem_units {u : Σ _ : ℕ,ℕ} :
    u∈units n D↔u.1∈inner n D∧u.2 + 1 < zd D u.1:=by
  rw [units,Finset.mem_sigma,Finset.mem_range]
  constructor <;> rintro ⟨h1,h2⟩ <;> exact ⟨h1,by omega⟩
theorem xm (n : ℕ) (D : Dag) (p : ℕ→ Prop) [DecidablePred p] :
    ((units n D).filter (fun u=>p u.1)).card = zw D ((inner n D).filter p):=by
  have hs : (units n D).filter (fun u=>p u.1) =
      ((inner n D).filter p).sigma (fun w=>Finset.range (zd D w - 1)):=by
    ext u;simp only [units,mem_filter,Finset.mem_sigma];tauto
  rw [hs,Finset.card_sigma,zw]
  simp
theorem card_unitsPlus (n : ℕ) (D : Dag) : (wo n D).card = zu n D:=by
  unfold wo zu;exact xm n D (fun w=>(supp n D w).Nonempty)
theorem mem_eligSet {v : Fin n} :
    v∈z6 n D↔∃ w,2≤ zd D w∧v∈supp n D w:=by
  simp only [z6,branchW,mem_biUnion,mem_filter,Finset.mem_range]
  constructor
  · rintro ⟨w,⟨-,h2⟩,hv⟩;exact ⟨w,h2,hv⟩
  · rintro ⟨w,h2,hv⟩
    refine ⟨w,⟨?_,h2⟩,hv⟩
    by_contra hc
    rw [supp_ge D w (by omega)] at hv;exact notMem_empty v hv
theorem mem_ineligSet {v : Fin n} :
    v∈z1 n D↔∀ w,v∈supp n D w→ zd D w≤ 1:=by
  rw [z1,mem_sdiff,mem_eligSet]
  constructor
  · rintro ⟨-,h⟩ w hw
    by_contra hc
    exact h ⟨w,by omega,hw⟩
  · intro h
    refine ⟨mem_univ v,?_⟩
    rintro ⟨w,hw,hv⟩
    have:=h w hv
    omega
theorem xi {v : Fin n} {T : Finset (Fin n)} :
    (({v} : Finset (Fin n))∩T).Nonempty↔v∈T:=by
  constructor
  · rintro ⟨u,hu⟩
    rw [mem_inter,mem_singleton] at hu;exact hu.1▸hu.2
  · intro h
    exact ⟨v,mem_inter.mpr ⟨mem_singleton_self v,h⟩⟩
theorem z1h (b : Fin n→ ℕ) (hb : qe n D b) :
    Set.InjOn (fun v=>(⟨b v,0⟩ : Σ _ : ℕ,ℕ)) (z6 n D : Set (Fin n)):=by
  intro v hv v2 hv2 he;have hbv : b v = b v2:=congrArg Sigma.fst he;have h1:=(hb v hv).2;rw [hbv,(hb v2 hv2).2] at h1;exact (singleton_injective h1).symm
theorem reserved_subset (hS : za n D) (b : Fin n→ ℕ) (hb : qe n D b) :
    reservedUnits n D b⊆wo n D:=by
  intro u hu;obtain ⟨v,hv,rfl⟩:=mem_image.mp hu;obtain ⟨h2,hs⟩:=hb v hv;have h1 : 1≤ zd D (b v):=by omega
  rw [wo,mem_filter,mem_units]
  refine ⟨⟨qm.mpr (lt_of_fanout_pos hS h1),?_⟩,?_⟩
  · show 0 + 1 < zd D (b v)
    omega
  · show (supp n D (b v)).Nonempty
    rw [hs];exact Finset.singleton_nonempty v
theorem card_reserved (b : Fin n→ ℕ) (hb : qe n D b) :
    (reservedUnits n D b).card = (z6 n D).card:=
  card_image_of_injOn (z1h b hb)
theorem z0g (hS : za n D) (b : Fin n→ ℕ) (hb : qe n D b) :
    (z6 n D).card≤ zu n D:=by
  rw [← card_reserved b hb,← card_unitsPlus];exact card_le_card (reserved_subset hS b hb)
theorem card_residual (hS : za n D) (b : Fin n→ ℕ) (hb : qe n D b) :
    (z5 n D b).card + (z6 n D).card = zu n D:=by
  rw [← card_reserved b hb,← card_unitsPlus];exact Finset.card_sdiff_add_card_eq_card (reserved_subset hS b hb)
theorem w6 (hS : za n D) (b : Fin n→ ℕ) (hb : qe n D b)
    (T : Finset (Fin n)) :
    zw D (zb n D T) = (T∩z6 n D).card +
      ((z5 n D b).filter (fun u=>(supp n D u.1∩T).Nonempty)).card:=by
  have h1 : zw D (zb n D T) =
      ((units n D).filter (fun u=>(supp n D u.1∩T).Nonempty)).card:=by
    rw [xm n D (fun w=>(supp n D w∩T).Nonempty)]
    symm
    refine Finset.sum_subset (fun w hw=>?_) (fun w hw hnot=>?_)
    · rw [mem_filter] at hw
      have:=qm.mp hw.1
      exact mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hw.2⟩
    · rw [zb,mem_filter] at hw
      have hni : w∉inner n D:=fun hc=>hnot (mem_filter.mpr ⟨hc,hw.2⟩);rw [qm] at hni;simp [yv hS w (by omega)]
  have h2 : (units n D).filter (fun u=>(supp n D u.1∩T).Nonempty) =
      (reservedUnits n D b).filter (fun u=>(supp n D u.1∩T).Nonempty)∪
        (z5 n D b).filter (fun u=>(supp n D u.1∩T).Nonempty):=by
    ext u
    have hsub:=reserved_subset hS b hb;simp only [z5,wo,mem_union,mem_filter,mem_sdiff]
    constructor
    · intro hu
      by_cases hr : u∈reservedUnits n D b
      · exact Or.inl ⟨hr,hu.2⟩
      · exact Or.inr ⟨⟨⟨hu.1,hu.2.mono inter_subset_left⟩,hr⟩,hu.2⟩
    · rintro (hu | hu)
      · exact ⟨(mem_filter.mp (hsub hu.1)).1,hu.2⟩
      · exact ⟨hu.1.1.1,hu.2⟩
  have h3 : Disjoint ((reservedUnits n D b).filter (fun u=>(supp n D u.1∩T).Nonempty))
      ((z5 n D b).filter (fun u=>(supp n D u.1∩T).Nonempty)):=
    Finset.disjoint_filter_filter Finset.disjoint_sdiff
  have h4 : (reservedUnits n D b).filter (fun u=>(supp n D u.1∩T).Nonempty) =
      (T∩z6 n D).image (fun v=>(⟨b v,0⟩ : Σ _ : ℕ,ℕ)):=by
    rw [reservedUnits,Finset.filter_image]
    congr 1
    ext v
    simp only [mem_filter,mem_inter]
    constructor
    · rintro ⟨hv,hne⟩
      rw [(hb v hv).2,xi] at hne;exact ⟨hne,hv⟩
    · rintro ⟨hT,hv⟩
      refine ⟨hv,?_⟩
      rw [(hb v hv).2,xi];exact hT
  rw [h1,h2,card_union_of_disjoint h3,h4,
    card_image_of_injOn ((z1h b hb).mono
      (Finset.coe_subset.mpr inter_subset_right))]
theorem w5 (hS : za n D) (b : Fin n→ ℕ) (hb : qe n D b)
    (T : Finset (Fin n)) :
    zw D (zb n D T) + (z6 n D).card≤
      (T∩z6 n D).card + zu n D:=by
  have h1:=w6 hS b hb T;have h2:=card_residual hS b hb;have h3:=card_filter_le (z5 n D b)
    (fun u=>(supp n D u.1∩T).Nonempty)
  omega
end SurplusFlow
def y3 {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : ℕ:=
  if h : w < n then (σ ⟨w,h⟩).val else w
def z7 {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) : Dag:=
  D.map (fun g=>(g.1,y3 σ g.2.1,y3 σ g.2.2))
theorem z01 {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : w < n) :
    y3 σ w = (σ ⟨w,h⟩).val:=by
  simp [y3,h]
theorem x4 {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : n≤ w) : y3 σ w = w:=by
  simp [y3,Nat.not_lt.mpr h]
theorem y4 {n : ℕ} (σ : Equiv.Perm (Fin n)) {m : ℕ} (hm : n≤ m) (w : ℕ) :
    y3 σ w < m↔w < m:=by
  by_cases h : w < n
  · rw [z01 σ h]
    have:=(σ ⟨w,h⟩).isLt
    constructor <;> intro <;> omega
  · rw [x4 σ (Nat.not_lt.mp h)]
theorem vt {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : y3 σ⁻¹ (y3 σ w) = w:=by
  by_cases h : w < n
  · rw [z01 σ h,z01 σ⁻¹ (σ ⟨w,h⟩).isLt];simp
  · rw [x4 σ (Nat.not_lt.mp h),x4 σ⁻¹ (Nat.not_lt.mp h)]
theorem tr_liftP_inv' {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : y3 σ (y3 σ⁻¹ w) = w:=by
  simpa using vt σ⁻¹ w
theorem z0y {n : ℕ} (σ : Equiv.Perm (Fin n)) {a b : ℕ} :
    y3 σ a = y3 σ b↔a = b:=by
  refine ⟨fun h=>?_,congrArg _⟩
  have:=congrArg (y3 σ⁻¹) h
  rwa [vt,vt] at this
theorem q8 {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) :
    (z7 σ D).length = D.length:=by
  simp [z7]
theorem tr_tag {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    tag (z7 σ D) j = tag D j:=by
  rw [tag_eq _ j (by rw [q8];exact hj),tag_eq D j hj];simp [z7]
theorem z50 {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opA (z7 σ D) j = y3 σ (opA D j):=by
  rw [opA_eq _ j (by rw [q8];exact hj),opA_eq D j hj];simp [z7]
theorem z4z {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opB (z7 σ D) j = y3 σ (opB D j):=by
  rw [opB_eq _ j (by rw [q8];exact hj),opB_eq D j hj];simp [z7]
theorem z1t {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : za n D) :
    za n (z7 σ D):=by
  intro j hj;rw [q8] at hj;obtain ⟨ha,hb,hab⟩:=hS j hj;rw [z50 σ D j hj,z4z σ D j hj];exact ⟨(y4 σ (Nat.le_add_right n j) _).mpr ha,
    (y4 σ (Nat.le_add_right n j) _).mpr hb,fun h=>hab ((z0y σ).mp h)⟩
theorem z3g {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : za n D)
    (x : Fin n→ Bool) (w : ℕ) :
    val (z7 σ D) x (y3 σ w) = val D (fun i=>x (σ i)) w:=by
  by_cases hw : w < n + D.length
  · refine (val_unique (z1t σ hS) x
      (fun w'=>val D (fun i=>x (σ i)) (y3 σ⁻¹ w')) ?_ ?_ (y3 σ w) ?_).trans ?_
    · intro i hi
      show val D (fun i=>x (σ i)) (y3 σ⁻¹ i) = x ⟨i,hi⟩
      rw [z01 σ⁻¹ hi,val_input D _ _ (σ⁻¹ ⟨i,hi⟩).isLt]
      simp
    · intro j hj
      rw [q8] at hj
      show val D (fun i=>x (σ i)) (y3 σ⁻¹ (n + j)) =
        gop (tag (z7 σ D) j) (val D (fun i=>x (σ i)) (y3 σ⁻¹ (opA (z7 σ D) j)))
          (val D (fun i=>x (σ i)) (y3 σ⁻¹ (opB (z7 σ D) j)))
      rw [x4 σ⁻¹ (Nat.le_add_right n j),tr_tag σ D j hj,z50 σ D j hj,
        z4z σ D j hj,vt,vt,val_gate hS _ j hj]
    · rw [q8];exact (y4 σ (Nat.le_add_right _ _) w).mpr hw
    · show val D (fun i=>x (σ i)) (y3 σ⁻¹ (y3 σ w)) = _
      rw [vt]
  · have hw':=Nat.not_lt.mp hw
    rw [x4 σ (le_trans (Nat.le_add_right _ _) hw'),
      val_ge _ _ _ (by rw [q8];exact hw'),val_ge _ _ _ hw']
theorem xn {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (w : ℕ) :
    zd (z7 σ D) (y3 σ w) = zd D w:=by
  unfold zd zq;rw [q8]
  congr 1
  apply Finset.filter_congr
  intro j hj;have hj':=Finset.mem_range.mp hj;rw [z50 σ D j hj',z4z σ D j hj',z0y,z0y]
theorem z57 {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hL : Live n D) :
    Live n (z7 σ D):=by
  rcases eq_or_ne D [] with rfl | hne
  · exact hL
  · intro w' hw'
    rw [q8] at hw';have hpos:=List.length_pos_iff.mpr hne;rw [← tr_liftP_inv' σ w',xn]
    apply hL
    by_cases h : w' < n
    · have:=(y4 σ⁻¹ le_rfl w').mpr h
      omega
    · rw [x4 σ⁻¹ (Nat.not_lt.mp h)];exact hw'
theorem z2l {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (h : z0 n D) :
    z0 n (z7 σ D):=
  ⟨z1t σ h.1,z57 σ h.2.1,by simpa [z7] using h.2.2⟩
theorem z5d {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : za n D) (hne : D≠[])
    (x : Fin n→ Bool) :
    val (z7 σ D) x (qc n (z7 σ D)) = val D (fun i=>x (σ i)) (qc n D):=by
  have hpos:=List.length_pos_iff.mpr hne;have e : qc n (z7 σ D) = y3 σ (qc n D):=by
    rw [x4 σ (by unfold qc;omega)];simp [qc,q8]
  rw [e,z3g σ hS]
theorem z3w {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    (fun i=>single v (σ i)) = single (σ⁻¹ v):=by
  funext i
  simp only [single,decide_eq_decide]
  constructor
  · intro h;rw [← h];simp
  · intro h;rw [h];simp
theorem y7 {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : za n D) (w : ℕ) :
    supp n (z7 σ D) (y3 σ w) = (supp n D w).image σ:=by
  ext v
  simp only [supp,mem_filter,mem_univ,true_and,mem_image];rw [z3g σ hS,z3w]
  constructor
  · intro h;exact ⟨σ⁻¹ v,h,by simp⟩
  · rintro ⟨a,ha,rfl⟩;simpa using ha
theorem wg {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : za n D) :
    z6 n (z7 σ D) = (z6 n D).image σ:=by
  ext v
  simp only [z6,mem_biUnion,mem_image,branchW,mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨w',⟨hw',hf⟩,hv⟩
    obtain ⟨w,rfl⟩ : ∃ w,w' = y3 σ w:=⟨y3 σ⁻¹ w',(tr_liftP_inv' σ w').symm⟩;rw [y7 σ hS,mem_image] at hv;obtain ⟨a,ha,rfl⟩:=hv;rw [xn] at hf;rw [q8,y4 σ (Nat.le_add_right _ _)] at hw';exact ⟨a,⟨w,⟨hw',hf⟩,ha⟩,rfl⟩
  · rintro ⟨a,⟨w,⟨hw,hf⟩,ha⟩,rfl⟩
    refine ⟨y3 σ w,⟨?_,?_⟩,?_⟩
    · rw [q8];exact (y4 σ (Nat.le_add_right _ _) w).mpr hw
    · rw [xn];exact hf
    · rw [y7 σ hS];exact Finset.mem_image_of_mem _ ha
theorem z2v {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : za n D) :
    z1 n (z7 σ D) = (z1 n D).image σ:=by
  ext v
  simp only [z1,wg σ hS,mem_sdiff,mem_univ,true_and,
    mem_image]
  constructor
  · intro h
    exact ⟨σ⁻¹ v,fun hm=>h ⟨σ⁻¹ v,hm,by simp⟩,by simp⟩
  · rintro ⟨a,ha,rfl⟩ ⟨b,hb,hab⟩
    exact ha (σ.injective hab▸hb)
theorem zm (n : ℕ) (D : Dag) : (z1 n D).card + (z6 n D).card = n:=by
  have h:=Finset.card_sdiff_add_card_eq_card (subset_univ (z6 n D));rw [card_univ,Fintype.card_fin] at h;exact h
def qi {n : ℕ} (G : Fin n→ Fin n→ Prop) (x : Fin n→ Bool) : Prop:=
  ∃ u v : Fin n,G u v∧x u = true∧x v = true
def z3 (n : ℕ) (G : Fin n→ Fin n→ Prop) (D : Dag) : Prop:=
  ∀ x : Fin n→ Bool,val D x (qc n D) = true↔qi G x
def zc {n : ℕ} (G : Fin n→ Fin n→ Prop) (Good : Fin n→ Prop) : Prop:=
  (∀ u v,G u v→ G v u)∧(∀ u,¬ G u u)∧
    (∀ v,Good v→ ∀ w,v≠w→ ∃ z,G v z∧¬ G w z)∧
    (∀ u,∃ a,G u a)
def qy (n : ℕ) (D : Dag) (a b : ℕ) : Prop:=
  b < n + D.length∧n≤ b∧(opA D (b - n) = a∨opB D (b - n) = a)
def qv {n : ℕ} (u z : Fin n) : Fin n→ Bool:=fun i=>decide (i = u) || decide (i = z)
def q9 {n : ℕ} (v : Fin n) (x : Fin n→ Bool) : Fin n→ Bool:=fun i=>decide (i = v) || x i
def qa {n : ℕ} (A : Finset (Fin n)) : Fin n→ Bool:=fun i=>decide (i∈A)
theorem z13 {α : Type} {r p : α→ α→ Prop} (h : ∀ a b,r a b→ p a b) {a b : α}
    (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b:=by
  induction hab with
  | refl=>exact Relation.ReflTransGen.refl
  | tail _ hbc ih=>exact Relation.ReflTransGen.tail ih (h _ _ hbc)
section SemCore
variable {n : ℕ} {G : Fin n→ Fin n→ Prop} {Good : Fin n→ Prop} {D : Dag}
theorem w9 (v : Fin n) (x : Fin n→ Bool) : ∀ k,k≠v→ x k = q9 v x k:=by
  intro k hk;simp [q9,hk]
theorem xq (v : Fin n) (x : Fin n→ Bool) : q9 v x v = true:=by simp [q9]
theorem z2i (v : Fin n) (x : Fin n→ Bool) : ∀ i,x i = true→ q9 v x i = true:=by
  intro i hi;simp [q9,hi]
theorem z4k {x : Fin n→ Bool} {u : Fin n} (hu : x u = true) :
    ∀ i,single u i = true→ x i = true:=by
  intro i hi;simp only [single,decide_eq_true_eq] at hi;rw [hi];exact hu
theorem x8 (hS : za n D) {u : Fin n} {w : ℕ} (hu : u∈supp n D w)
    {x : Fin n→ Bool} (hx : x u = true) : val D x w = true:=
  val_mono hS (single u) x (z4k hx) w (mem_supp.mp hu)
theorem yf {v : Fin n} {w : ℕ} (hv : v∈supp n D w) : w < n + D.length:=by
  by_contra hc
  rw [supp_ge D w (by omega)] at hv;exact notMem_empty v hv
theorem yr (hS : za n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true) :
    supp n D (n + j) = supp n D (opA D j)∩supp n D (opB D j):=by
  rw [supp_gate hS j hj];simp [ht]
theorem yq (hS : za n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = false) :
    supp n D (n + j) = supp n D (opA D j)∪supp n D (opB D j):=by
  rw [supp_gate hS j hj];simp [ht]
theorem qg (hS : za n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true)
    (s : Bool) : supp n D (n + j)⊆supp n D (src D (j,s)):=by
  rw [yr hS hj ht]
  cases s
  · rw [qw];exact inter_subset_left
  · rw [y5];exact inter_subset_right
theorem z12 (hS : za n D) {j : ℕ} (hj : j < D.length) (s : Bool) :
    src D (j,s) < n + j:=by
  obtain ⟨ha,hb,-⟩:=hS j hj
  cases s
  · rw [qw];exact ha
  · rw [y5];exact hb
theorem z5t (hS : za n D) {j : ℕ} (hj : j < D.length) (s : Bool) :
    src D (j,s)≠src D (j,!s):=by
  obtain ⟨-,-,hne⟩:=hS j hj
  cases s
  · simpa [src] using hne
  · simpa [src] using hne.symm
theorem vm {j : ℕ} (hj : j < D.length) (s : Bool) :
    qy n D (src D (j,s)) (n + j):=by
  refine ⟨by omega,by omega,?_⟩
  rw [Nat.add_sub_cancel_left]
  cases s
  · exact Or.inl (qw j).symm
  · exact Or.inr (y5 j).symm
theorem z54 {a b : ℕ} : qy n D a b↔
    ∃ j s,j < D.length∧b = n + j∧src D (j,s) = a:=by
  constructor
  · rintro ⟨h1,h2,h3 | h3⟩
    · exact ⟨b - n,false,by omega,by omega,by rw [qw];exact h3⟩
    · exact ⟨b - n,true,by omega,by omega,by rw [y5];exact h3⟩
  · rintro ⟨j,s,hj,rfl,rfl⟩
    refine ⟨by omega,by omega,?_⟩
    rw [Nat.add_sub_cancel_left]
    cases s
    · exact Or.inl (qw j).symm
    · exact Or.inr (y5 j).symm
theorem z1o (hS : za n D) {a b : ℕ} (h : qy n D a b) : a < b:=by
  obtain ⟨h1,h2,h3⟩:=h
  have:=hS (b - n) (by omega)
  omega
theorem ve {a c : ℕ} (h : qy n D a c) : c - n∈zq D a:=by
  unfold zq;rw [mem_filter,Finset.mem_range];exact ⟨by have:=h.1;have:=h.2.1;omega,h.2.2⟩
theorem z1f {a c : ℕ} (h : qy n D a c) : 1≤ zd D a:=
  card_pos.mpr ⟨_,ve h⟩
theorem x9 {a c c' : ℕ} (h1 : qy n D a c) (h2 : qy n D a c')
    (hf : zd D a = 1) : c = c':=by
  have m1:=ve h1;have m2:=ve h2;obtain ⟨r,hr⟩:=card_eq_one.mp (show (zq D a).card = 1 from hf);rw [hr,mem_singleton] at m1 m2
  have:=h1.2.1
  have:=h2.2.1
  omega
theorem v9 (hS : za n D) (x y : Fin n→ Bool) (v : Fin n)
    (hxy : ∀ k,k≠v→ x k = y k) (w : ℕ) (hw : val D x w≠val D y w) :
    Relation.ReflTransGen (fun a b=>qy n D a b∧val D x b≠val D y b) v.val w:=by
  induction w using Nat.strong_induction_on with
  | _ w ih=>
    by_cases hn : w < n
    · rw [val_input D x w hn,val_input D y w hn] at hw
      have hwv : (⟨w,hn⟩ : Fin n) = v:=by
        by_contra hc;exact hw (hxy _ hc)
      rw [← hwv]
    · by_cases hlt : w < n + D.length
      · obtain ⟨j,rfl⟩ : ∃ j,w = n + j:=⟨w - n,by omega⟩
        have hj : j < D.length:=by omega
        obtain ⟨ha,hb,-⟩:=hS j hj;have hg:=hw;rw [val_gate hS x j hj,val_gate hS y j hj] at hg
        by_cases h1 : val D x (opA D j) = val D y (opA D j)
        · have h2 : val D x (opB D j)≠val D y (opB D j):=by
            intro h2;apply hg;rw [h1,h2]
          exact Relation.ReflTransGen.tail (ih _ hb h2)
            ⟨⟨hlt,by omega,Or.inr (by rw [Nat.add_sub_cancel_left])⟩,hw⟩
        · exact Relation.ReflTransGen.tail (ih _ ha h1)
            ⟨⟨hlt,by omega,Or.inl (by rw [Nat.add_sub_cancel_left])⟩,hw⟩
      · exfalso;apply hw;rw [val_ge D x w (by omega),val_ge D y w (by omega)]
def z23 (n : ℕ) (D : Dag) (b v : ℕ) : Prop:=
  b = v∨¬ Relation.ReflTransGen (fun a c=>qy n D a c∧c≠b) v (qc n D)
theorem z43 (hS : za n D) (x y : Fin n→ Bool) (v : Fin n)
    (hxy : ∀ k,k≠v→ x k = y k) (b : ℕ) (hdom : z23 n D b v.val)
    (hb : val D x b = val D y b) : val D x (qc n D) = val D y (qc n D):=by
  by_contra hne
  rcases hdom with rfl | hdom
  · rw [val_input D x _ v.isLt,val_input D y _ v.isLt] at hb
    have hxy2 : x = y:=by
      funext k
      by_cases hk : k = v
      · rw [hk];exact hb
      · exact hxy k hk
    exact hne (by rw [hxy2])
  · exact hdom (z13
      (fun a c h=>⟨h.1,fun hc=>h.2 (by rw [hc];exact hb)⟩)
      (v9 hS x y v hxy _ hne))
def zn (n : ℕ) (D : Dag) (a b : ℕ) : Prop:=
  Relation.ReflTransGen (fun a c=>qy n D a c∧zd D a = 1) a b
theorem qk (hS : za n D) {v b : ℕ} (h : zn n D v b) :
    z23 n D b v:=by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl=>exact Or.inl rfl
  | @head a c hstep _ ih=>
    by_cases hba : b = a
    · exact Or.inl hba
    · right
      intro hp
      rcases Relation.ReflTransGen.cases_head hp with heq | ⟨c',hs,hrest⟩
      · have h0:=yv hS a (by rw [heq];unfold qc;omega)
        have h1:=hstep.2;omega
      · have hcc : c = c':=x9 hstep.1 hs.1 hstep.2
        subst hcc
        rcases ih with rfl | ih
        · exact hs.2 rfl
        · exact ih hrest
theorem z03 (hS : za n D) (v : Fin n) : ∀ w,v∈supp n D w→
    (∀ u,u < w→ v∈supp n D u→ zd D u≤ 1)→ zn n D v.val w:=by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih=>
    intro hv hlow
    by_cases hn : w < n
    · have hs : supp n D w = {⟨w,hn⟩}:=supp_input D ⟨w,hn⟩
      rw [hs,mem_singleton] at hv;rw [hv];exact Relation.ReflTransGen.refl
    · have hlt:=yf hv
      obtain ⟨j,rfl⟩ : ∃ j,w = n + j:=⟨w - n,by omega⟩;have hj : j < D.length:=by omega
      have key : ∀ s : Bool,v∈supp n D (src D (j,s))→ zn n D v.val (n + j):=by
        intro s hva;have hstep : qy n D (src D (j,s)) (n + j):=vm hj s;have hlt':=z12 hS hj s;have h1:=z1f hstep;have h2:=hlow _ hlt' hva;exact Relation.ReflTransGen.tail (ih _ hlt' hva (fun u hu=>hlow u (by omega)))
          ⟨hstep,by omega⟩
      rw [supp_gate hS j hj] at hv
      split_ifs at hv with ht
      · exact key false (by rw [qw];exact (mem_inter.mp hv).1)
      · rcases mem_union.mp hv with h1 | h1
        · exact key false (by rw [qw];exact h1)
        · exact key true (by rw [y5];exact h1)
theorem qr (hG : zc G Good) (v : Fin n) : ¬ qi G (single v):=by
  rintro ⟨a,c,hac,ha,hc⟩
  simp only [single,decide_eq_true_eq] at ha hc;rw [ha,hc] at hac;exact hG.2.1 _ hac
theorem wq {u v : Fin n} (huv : G u v) : qi G (qv u v):=
  ⟨u,v,huv,by simp [qv],by simp [qv]⟩
theorem ye (hG : zc G Good) (hC : z3 n G D) : supp n D (qc n D) = ∅:=
  Finset.eq_empty_iff_forall_notMem.2
    (fun v hv=>qr hG v ((hC _).1 (mem_supp.1 hv)))
theorem z1s (hG : zc G Good) (hS : za n D) (hC : z3 n G D) (v : Fin n)
    (S : Finset (Fin n)) (hsep : ∀ u,u∉S→ ∃ z,G v z∧¬ G u z)
    (b : ℕ) (hdom : z23 n D b v.val) : supp n D b⊆S:=by
  intro u hu
  by_contra huv
  obtain ⟨hsym,hirr,-,-⟩:=hG;obtain ⟨z,hvz,huz⟩:=hsep u huv;have hxb : val D (qv u z) b = true:=x8 hS hu (by simp [qv]);have hyb : val D (q9 v (qv u z)) b = true:=
    x8 hS hu (by simp [q9,qv])
  have hout:=z43 hS _ _ v (w9 v (qv u z)) b hdom (by rw [hxb,hyb]);have h1 : ¬ qi G (qv u z):=by
    rintro ⟨a,c,hac,ha,hc⟩
    simp only [qv,Bool.or_eq_true,decide_eq_true_eq] at ha hc
    rcases ha with ha | ha <;> rcases hc with hc | hc <;> rw [ha,hc] at hac
    · exact hirr _ hac
    · exact huz hac
    · exact huz (hsym _ _ hac)
    · exact hirr _ hac
  have h2 : qi G (q9 v (qv u z)):=
    ⟨v,z,hvz,xq v _,by simp [q9,qv]⟩
  have h3:=(hC _).mpr h2;rw [← hout] at h3;exact h1 ((hC _).mp h3)
theorem ys (hG : zc G Good) (hS : za n D) (hC : z3 n G D) (v : Fin n)
    (hvG : Good v) (b : ℕ) (hdom : z23 n D b v.val) : supp n D b⊆{v}:=
  z1s hG hS hC v {v} (fun u hu=>hG.2.2.1 v hvG u (fun e=>hu (by simp [e]))) b hdom
theorem z36 (hG : zc G Good) (hS : za n D) (hC : z3 n G D) (v : Fin n)
    (hvG : Good v) (hv : v∈z6 n D) :
    ∃ b,2≤ zd D b∧supp n D b = {v}∧zn n D v.val b:=by
  classical
  have hex : ∃ w,2≤ zd D w∧v∈supp n D w:=mem_eligSet.mp hv;obtain ⟨h1,h2⟩:=Nat.find_spec hex;have hch : zn n D v.val (Nat.find hex):=
    z03 hS v _ h2 (fun u hu huv=>by
      have:=Nat.find_min hex hu
      by_contra hc
      exact this ⟨by omega,huv⟩)
  exact ⟨Nat.find hex,h1,Finset.Subset.antisymm
    (ys hG hS hC v hvG _ (qk hS hch)) (singleton_subset_iff.mpr h2),hch⟩
def z1g (n : ℕ) (D : Dag) (b : Fin n→ ℕ) : Prop:=
  ∀ v∈z6 n D,2≤ zd D (b v)∧supp n D (b v) = {v}∧zn n D v.val (b v)
theorem z16 (hG : zc G Good) (hS : za n D) (hC : z3 n G D)
    (hEl : ∀ v∈z6 n D,Good v) :
    ∃ b : Fin n→ ℕ,z1g n D b:=by
  classical
  have h : ∀ v : Fin n,∃ b,v∈z6 n D→
      2≤ zd D b∧supp n D b = {v}∧zn n D v.val b:=by
    intro v
    by_cases hv : v∈z6 n D
    · obtain ⟨b,hb⟩:=z36 hG hS hC v (hEl v hv) hv
      exact ⟨b,fun _=>hb⟩
    · exact ⟨0,fun h=>absurd h hv⟩
  choose b hb using h
  exact ⟨b,fun v hv=>hb v hv⟩
theorem z1q {b : Fin n→ ℕ} (hb : z1g n D b) : qe n D b:=
  fun v hv=>⟨(hb v hv).1,(hb v hv).2.1⟩
theorem zz (hG : zc G Good) (hS : za n D) (hC : z3 n G D)
    (hEl : ∀ v∈z6 n D,Good v) :
    ∃ b : Fin n→ ℕ,qe n D b:=by
  obtain ⟨b,hb⟩:=z16 hG hS hC hEl;exact ⟨b,z1q hb⟩
theorem qt {v : Fin n} : v∈z1 n D↔v∉z6 n D:=by
  simp [z1]
theorem z35 (hS : za n D) {v : Fin n} (hv : v∈z1 n D) {w : ℕ}
    (hw : v∈supp n D w) : zn n D v.val w:=
  z03 hS v w hw (fun u _ hu=>mem_ineligSet.mp hv u hu)
theorem we (hG : zc G Good) (hS : za n D) (hC : z3 n G D) {v : Fin n}
    (hvG : Good v) (hv : v∈z1 n D) {w : ℕ} (hw : v∈supp n D w) : supp n D w = {v}:=
  Finset.Subset.antisymm (ys hG hS hC v hvG w (qk hS (z35 hS hv hw)))
    (singleton_subset_iff.mpr hw)
theorem z0m {v : Fin n} {w : ℕ} : w∈zb n D {v}↔v∈supp n D w:=by
  simp only [zb,mem_filter,Finset.mem_range]
  constructor
  · rintro ⟨-,u,hu⟩
    rw [mem_inter,mem_singleton] at hu;exact hu.2▸hu.1
  · intro h
    exact ⟨yf h,v,mem_inter.mpr ⟨h,mem_singleton_self v⟩⟩
theorem xf {v : Fin n} {e : ℕ×Bool} : e∈zk n D (zb n D {v})↔
    e.1 < D.length∧v∈supp n D (src D e)∧v∉supp n D (n + e.1):=by
  simp only [zk,arcs,mem_filter,Finset.mem_product,Finset.mem_range,
    mem_univ,and_true,z0m]
theorem z2j {v : Fin n} (hv : v∈z1 n D) :
    zw D (zb n D {v}) = 0:=by
  unfold zw
  refine Finset.sum_eq_zero (fun w hw=>?_)
  have:=mem_ineligSet.mp hv w (z0m.mp hw)
  omega
theorem ws (hG : zc G Good) (hS : za n D) (hC : z3 n G D)
    {u v : Fin n} (huv : G u v) :
    ∃ j,j < D.length∧tag D j = true∧val D (qv u v) (n + j) = true∧
      u∉supp n D (n + j)∧v∉supp n D (n + j)∧
      ∃ s : Bool,u∈supp n D (src D (j,s))∧v∉supp n D (src D (j,s))∧
        v∈supp n D (src D (j,!s))∧u∉supp n D (src D (j,!s)):=by
  classical
  have hex : ∃ w,val D (qv u v) w = true∧u∉supp n D w∧v∉supp n D w:=
    ⟨qc n D,(hC _).2 (wq huv),by rw [ye hG hC];simp,
      by rw [ye hG hC];simp⟩
  obtain ⟨hw1,hw2,hw3⟩:=Nat.find_spec hex;have hmin : ∀ a,a < Nat.find hex→ val D (qv u v) a = true→
      u∈supp n D a∨v∈supp n D a:=by
    intro a ha hva
    by_contra hc
    rw [not_or] at hc;exact Nat.find_min hex ha ⟨hva,hc.1,hc.2⟩
  generalize Nat.find hex = w at hw1 hw2 hw3 hmin
  have hlt : w < n + D.length:=by
    by_contra hc
    rw [val_ge D _ w (by omega)] at hw1;exact Bool.false_ne_true hw1
  have hn : n≤ w:=by
    by_contra hc
    have hc' : w < n:=by omega
    rw [val_input D _ w hc'] at hw1;have hs : supp n D w = {⟨w,hc'⟩}:=supp_input D ⟨w,hc'⟩;rw [hs,mem_singleton] at hw2 hw3;simp only [qv,Bool.or_eq_true,decide_eq_true_eq] at hw1
    rcases hw1 with h | h
    · exact hw2 h.symm
    · exact hw3 h.symm
  obtain ⟨j,rfl⟩ : ∃ j,w = n + j:=⟨w - n,by omega⟩;have hj : j < D.length:=by omega
  obtain ⟨ha,hb,-⟩:=hS j hj;have hval:=hw1;rw [val_gate hS _ j hj] at hw1;rw [supp_gate hS j hj] at hw2 hw3
  cases ht : tag D j
  · exfalso
    rw [ht] at hw1 hw2 hw3;simp only [gop_false,Bool.or_eq_true] at hw1;simp only [Bool.false_eq_true,ite_false,mem_union,not_or] at hw2 hw3
    rcases hw1 with h | h
    · rcases hmin _ ha h with h' | h'
      · exact hw2.1 h'
      · exact hw3.1 h'
    · rcases hmin _ hb h with h' | h'
      · exact hw2.2 h'
      · exact hw3.2 h'
  · rw [ht] at hw1 hw2 hw3
    simp only [gop_true,Bool.and_eq_true] at hw1;simp only [ite_true,mem_inter,not_and] at hw2 hw3;have hsupp : u∉supp n D (n + j)∧v∉supp n D (n + j):=by
      rw [yr hS hj ht];simp only [mem_inter,not_and];exact ⟨hw2,hw3⟩
    refine ⟨j,hj,ht,hval,hsupp.1,hsupp.2,?_⟩
    rcases hmin _ ha hw1.1 with hA | hA
    · have hB : u∉supp n D (opB D j):=hw2 hA
      have hBv : v∈supp n D (opB D j):=(hmin _ hb hw1.2).resolve_left hB;exact ⟨false,by simpa [src] using hA,by simpa [src] using fun h=>hw3 h hBv,
        by simpa [src] using hBv,by simpa [src] using hB⟩
    · have hB : v∉supp n D (opB D j):=hw3 hA
      have hBu : u∈supp n D (opB D j):=(hmin _ hb hw1.2).resolve_right hB;exact ⟨true,by simpa [src] using hBu,by simpa [src] using hB,
        by simpa [src] using hA,by simpa [src] using fun h=>hw2 h hBu⟩
theorem wa (hG : zc G Good) (h : z0 n D) (hC : z3 n G D)
    {v : Fin n} (hv : v∈z1 n D) :
    ∃ e : ℕ×Bool,e.1 < D.length∧tag D e.1 = true∧v∈supp n D (src D e)∧
      v∉supp n D (n + e.1)∧(∀ a,G v a→ a∈supp n D (src D (e.1,!e.2)))∧
      zk n D (zb n D {v}) = {e}∧merges n D (zb n D {v}) = ∅:=by
  have hS:=h.1;have hfl:=ym h {v} (by rw [ye hG hC];simp);rw [z2j hv,card_singleton] at hfl;have hmeet : ∀ a,G v a→ ∃ j s,j < D.length∧tag D j = true∧
      (j,s)∈zk n D (zb n D {v})∧a∈supp n D (src D (j,!s)):=by
    intro a hva;obtain ⟨j,hj,ht,-,hju,-,s,h1,-,h3,-⟩:=ws hG hS hC hva;exact ⟨j,s,hj,ht,xf.mpr ⟨hj,h1,hju⟩,h3⟩
  obtain ⟨a0,ha0⟩:=hG.2.2.2 v;obtain ⟨j0,s0,hj0,ht0,hm0,-⟩:=hmeet a0 ha0;have hcard : (zk n D (zb n D {v})).card = 1:=by
    have:=card_pos.mpr ⟨_,hm0⟩
    omega
  have hmer : merges n D (zb n D {v}) = ∅:=card_eq_zero.mp (by omega);obtain ⟨e,he⟩:=card_eq_one.mp hcard;rw [he,mem_singleton] at hm0;subst hm0;have hmem:=xf.mp (by rw [he];exact mem_singleton_self _)
  refine ⟨(j0,s0),hj0,ht0,hmem.2.1,hmem.2.2,?_,he,hmer⟩
  intro a hva;obtain ⟨j,s,-,-,hm,ha⟩:=hmeet a hva;rw [he,mem_singleton] at hm;rw [Prod.mk.injEq] at hm;obtain ⟨rfl,rfl⟩:=hm;exact ha
theorem ql (hG : zc G Good) (h : z0 n D) (hC : z3 n G D)
    {v : Fin n} (hvG : Good v) (hv : v∈z1 n D) :
    ∃ e : ℕ×Bool,e.1 < D.length∧tag D e.1 = true∧supp n D (src D e) = {v}∧
      supp n D (n + e.1) = ∅∧(∀ a,G v a→ a∈supp n D (src D (e.1,!e.2)))∧
      zk n D (zb n D {v}) = {e}∧merges n D (zb n D {v}) = ∅:=by
  obtain ⟨e,h1,h2,h3,h4,h5,h6,h7⟩:=wa hG h hC hv;have hsrc : supp n D (src D e) = {v}:=we hG h.1 hC hvG hv h3
  refine ⟨e,h1,h2,hsrc,?_,h5,h6,h7⟩
  refine eq_empty_of_forall_notMem (fun x hx=>?_)
  have hx2:=qg h.1 h1 h2 e.2 hx;rw [hsrc,mem_singleton] at hx2;exact h4 (hx2▸hx)
theorem wu (hG : zc G Good) (h : z0 n D) (hC : z3 n G D)
    {u v : Fin n} (huG : Good u) (hvG : Good v) (huv : G u v) (hdeg : ∃ a,G u a∧a≠v) :
    u∈z6 n D∨v∈z6 n D:=by
  by_contra hc
  rw [not_or] at hc;obtain ⟨eu,-,-,-,-,hnu,hxu,-⟩:=ql hG h hC huG (qt.mpr hc.1);obtain ⟨ev,-,-,hsv,-,-,hxv,-⟩:=ql hG h hC hvG (qt.mpr hc.2);obtain ⟨j,hj,-,-,hju,hjv,s,h1,-,h3,-⟩:=ws hG h.1 hC huv
  have m1 : (j,s)∈zk n D (zb n D {u}):=xf.mpr ⟨hj,h1,hju⟩;have m2 : (j,!s)∈zk n D (zb n D {v}):=xf.mpr ⟨hj,h3,hjv⟩;rw [hxu,mem_singleton] at m1;rw [hxv,mem_singleton] at m2;subst m1;subst m2;obtain ⟨a,hua,hav⟩:=hdeg;have h5 : a∈supp n D (src D (j,!s)):=hnu a hua
  rw [hsv,mem_singleton] at h5;exact hav h5
theorem z3o {A : Finset (Fin n)} (hA : ∀ a∈A,∀ b∈A,¬ G a b) :
    ¬ qi G (qa A):=by
  rintro ⟨a,c,hac,ha,hc⟩
  simp only [qa,decide_eq_true_eq] at ha hc;exact hA a ha c hc hac
theorem x7 (hG : zc G Good) (hS : za n D) (hC : z3 n G D)
    (A : Finset (Fin n)) (hA : ∀ a∈A,∀ b∈A,¬ G a b) (x : Fin n)
    (hnb : ∃ a∈A,G x a) :
    ∃ j s,j < D.length∧tag D j = true∧x∈supp n D (src D (j,s))∧
      x∉supp n D (n + j)∧Disjoint (supp n D (src D (j,s))) A:=by
  by_contra hcon
  have hmask : ∀ j s,j < D.length→ tag D j = true→ x∈supp n D (src D (j,s))→
      x∉supp n D (n + j)→ val D (qa A) (src D (j,s)) = true∧
        val D (q9 x (qa A)) (src D (j,s)) = true:=by
    intro j s hj ht h1 h2;have hnd : ¬ Disjoint (supp n D (src D (j,s))) A:=
      fun hd=>hcon ⟨j,s,hj,ht,h1,h2,hd⟩
    rw [Finset.not_disjoint_iff] at hnd;obtain ⟨a,ha1,ha2⟩:=hnd;exact ⟨x8 hS ha1 (by simp [qa,ha2]),
      x8 hS ha1 (by simp [q9,qa,ha2])⟩
  have key : ∀ w,x∉supp n D w→ val D (qa A) w = val D (q9 x (qa A)) w:=by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih=>
      intro hw
      by_cases hn : w < n
      · rw [val_input D _ w hn,val_input D _ w hn]
        have hs : supp n D w = {⟨w,hn⟩}:=supp_input D ⟨w,hn⟩;rw [hs,mem_singleton] at hw;exact w9 x _ _ (fun hc=>hw hc.symm)
      · by_cases hlt : w < n + D.length
        · obtain ⟨j,rfl⟩ : ∃ j,w = n + j:=⟨w - n,by omega⟩
          have hj : j < D.length:=by omega
          obtain ⟨ha,hb,-⟩:=hS j hj;rw [val_gate hS _ j hj,val_gate hS _ j hj]
          cases ht : tag D j
          · rw [yq hS hj ht,mem_union,not_or] at hw
            rw [ih _ ha hw.1,ih _ hb hw.2]
          · have hw2:=hw
            rw [yr hS hj ht,mem_inter,not_and] at hw2
            by_cases hxa : x∈supp n D (opA D j)
            · have h1:=hmask j false hj ht (by rw [qw];exact hxa) hw
              rw [qw] at h1;rw [ih _ hb (hw2 hxa),h1.1,h1.2]
            · by_cases hxb : x∈supp n D (opB D j)
              · have h1:=hmask j true hj ht (by rw [y5];exact hxb) hw
                rw [y5] at h1;rw [ih _ ha hxa,h1.1,h1.2]
              · rw [ih _ ha hxa,ih _ hb hxb]
        · rw [val_ge D _ w (by omega),val_ge D _ w (by omega)]
  have hout:=key (qc n D) (by rw [ye hG hC];exact notMem_empty x);obtain ⟨a,ha,hxa⟩:=hnb;have h2 : qi G (q9 x (qa A)):=
    ⟨x,a,hxa,xq x _,by simp [q9,qa,ha]⟩
  have h3:=(hC _).mpr h2;rw [← hout] at h3;exact z3o hA ((hC _).mp h3)
theorem wt (hS : za n D) (T M : Finset (Fin n)) (hM : 2≤ M.card) (w : ℕ)
    (hw : supp n D w∩T = M) :
    ∃ j,j < D.length∧n + j≤ w∧supp n D (n + j)∩T = M∧
      j∈merges n D (zb n D T)∧(∀ u,u < n + j→ supp n D u∩T≠M)∧
      ((tag D j = true∧M ⊂ supp n D (opA D j)∩T∧M ⊂ supp n D (opB D j)∩T)∨
        (tag D j = false∧supp n D (opA D j)∩T ⊂ M∧supp n D (opB D j)∩T ⊂ M∧
          (supp n D (opA D j)∩T)∪(supp n D (opB D j)∩T) = M∧
          (supp n D (opA D j)∩T).Nonempty∧(supp n D (opB D j)∩T).Nonempty)):=by
  classical
  have hex : ∃ u,supp n D u∩T = M:=⟨w,hw⟩;have hle : Nat.find hex≤ w:=Nat.find_min' hex hw;have hmin : ∀ u,u < Nat.find hex→ supp n D u∩T≠M:=fun u hu=>Nat.find_min hex hu;have hspec:=Nat.find_spec hex
  generalize Nat.find hex = f at hle hmin hspec
  have hMne : M.Nonempty:=card_pos.mp (by omega);have hmem : ∀ {u : ℕ},(supp n D u∩T).Nonempty→ u∈zb n D T:=by
    intro u hu;obtain ⟨v,hv⟩:=hu;exact mem_filter.mpr ⟨Finset.mem_range.mpr
      (yf (mem_inter.mp hv).1),v,hv⟩
  have hflt : f < n + D.length:=by
    obtain ⟨v,hv⟩:=hMne;rw [← hspec] at hv;exact yf (mem_inter.mp hv).1
  have hfn : n≤ f:=by
    by_contra hc
    have hc' : f < n:=by omega
    have hs : supp n D f = {⟨f,hc'⟩}:=supp_input D ⟨f,hc'⟩;have h1 : M.card≤ 1:=by
      rw [← hspec,hs];exact (card_le_card inter_subset_left).trans (by simp)
    omega
  obtain ⟨j,rfl⟩ : ∃ j,f = n + j:=⟨f - n,by omega⟩;have hj : j < D.length:=by omega
  obtain ⟨ha,hb,-⟩:=hS j hj;have hna:=hmin _ ha;have hnb:=hmin _ hb
  refine ⟨j,hj,hle,hspec,?_,hmin,?_⟩
  · have hAB : (supp n D (opA D j)∩T).Nonempty∧(supp n D (opB D j)∩T).Nonempty:=by
      cases ht : tag D j
      · rw [yq hS hj ht,Finset.union_inter_distrib_right] at hspec
        constructor
        · rw [nonempty_iff_ne_empty]
          intro he;rw [he,Finset.empty_union] at hspec;exact hnb hspec
        · rw [nonempty_iff_ne_empty]
          intro he;rw [he,Finset.union_empty] at hspec;exact hna hspec
      · rw [yr hS hj ht] at hspec
        obtain ⟨v,hv⟩:=hMne;rw [← hspec] at hv;simp only [mem_inter] at hv;exact ⟨⟨v,mem_inter.mpr ⟨hv.1.1,hv.2⟩⟩,⟨v,mem_inter.mpr ⟨hv.1.2,hv.2⟩⟩⟩
    rw [merges,mem_filter,Finset.mem_range];exact ⟨hj,hmem (by rw [hspec];exact hMne),hmem hAB.1,hmem hAB.2⟩
  · cases ht : tag D j
    · right
      rw [yq hS hj ht,Finset.union_inter_distrib_right] at hspec;have hsa : supp n D (opA D j)∩T⊆M:=by rw [← hspec];exact Finset.subset_union_left
      have hsb : supp n D (opB D j)∩T⊆M:=by rw [← hspec];exact Finset.subset_union_right
      refine ⟨rfl,Finset.ssubset_iff_subset_ne.mpr ⟨hsa,hna⟩,
        Finset.ssubset_iff_subset_ne.mpr ⟨hsb,hnb⟩,hspec,?_,?_⟩
      · rw [nonempty_iff_ne_empty]
        intro he;rw [he,Finset.empty_union] at hspec;exact hnb hspec
      · rw [nonempty_iff_ne_empty]
        intro he;rw [he,Finset.union_empty] at hspec;exact hna hspec
    · left
      rw [yr hS hj ht] at hspec;have hsa : M⊆supp n D (opA D j)∩T:=by
        rw [← hspec];intro v hv;simp only [mem_inter] at hv ⊢;exact ⟨hv.1.1,hv.2⟩
      have hsb : M⊆supp n D (opB D j)∩T:=by
        rw [← hspec];intro v hv;simp only [mem_inter] at hv ⊢;exact ⟨hv.1.2,hv.2⟩
      exact ⟨rfl,Finset.ssubset_iff_subset_ne.mpr ⟨hsa,Ne.symm hna⟩,
        Finset.ssubset_iff_subset_ne.mpr ⟨hsb,Ne.symm hnb⟩⟩
end SemCore
def yl (n : ℕ) (D : Dag) (x : Fin n) : Finset (ℕ×Bool):=zk n D (zb n D {x})
def z04 (e : ℕ×Bool) : ℕ×Bool:=(e.1,!e.2)
section SemCodes
variable {n : ℕ} {G : Fin n→ Fin n→ Prop} {Good : Fin n→ Prop} {D : Dag}
theorem qj {x : Fin n} {e : ℕ×Bool} : e∈yl n D x↔
    e.1 < D.length∧x∈supp n D (src D e)∧x∉supp n D (n + e.1):=xf
theorem z5c (e : ℕ×Bool) : z04 (z04 e) = e:=by simp [z04]
theorem z67 (hS : za n D) {x : Fin n} {e : ℕ×Bool} (he : e∈yl n D x) :
    tag D e.1 = true:=by
  obtain ⟨hj,h1,h2⟩:=qj.mp he
  by_contra ht
  rw [Bool.not_eq_true] at ht
  apply h2
  rw [yq hS hj ht,mem_union];obtain ⟨j,s⟩:=e
  cases s
  · left;simpa [src] using h1
  · right;simpa [src] using h1
theorem z66 (hG : zc G Good) (h : z0 n D) (hC : z3 n G D) (x : Fin n) :
    (yl n D x).card + (merges n D (zb n D {x})).card =
      1 + zw D (zb n D {x}):=by
  have h1:=ym h {x} (by rw [ye hG hC];simp)
  rwa [card_singleton] at h1
theorem z1r (hG : zc G Good) (hS : za n D) (hC : z3 n G D) {x y : Fin n}
    (hxy : G x y) : ∃ e,e∈yl n D x∧z04 e∈yl n D y∧
      y∉supp n D (src D e)∧x∉supp n D (src D (z04 e))∧
      val D (qv x y) (n + e.1) = true:=by
  obtain ⟨j,hj,-,hval,hju,hjv,s,h1,h2,h3,h4⟩:=ws hG hS hC hxy;exact ⟨(j,s),qj.mpr ⟨hj,h1,hju⟩,qj.mpr ⟨hj,h3,hjv⟩,h2,h4,hval⟩
theorem z44 (hG : zc G Good) (hS : za n D) (hC : z3 n G D)
    {x a b y : Fin n} (hab : ¬ G a b) (hxy : G x y) (hya : ¬ G y a) (hyb : ¬ G y b) :
    ∃ e,e∈yl n D x∧a∉supp n D (src D e)∧b∉supp n D (src D e):=by
  have hsym:=hG.1;have hirr:=hG.2.1;have hA : ∀ u∈({a,b,y} : Finset (Fin n)),∀ v∈({a,b,y} : Finset (Fin n)),
      ¬ G u v:=by
    intro u hu v hv;simp only [mem_insert,mem_singleton] at hu hv
    rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;> rw [hu,hv]
    · exact hirr a
    · exact hab
    · exact fun h=>hya (hsym _ _ h)
    · exact fun h=>hab (hsym _ _ h)
    · exact hirr b
    · exact fun h=>hyb (hsym _ _ h)
    · exact hya
    · exact hyb
    · exact hirr y
  obtain ⟨j,s,hj,-,h1,h2,hd⟩:=x7 hG hS hC {a,b,y} hA x ⟨y,by simp,hxy⟩;exact ⟨(j,s),qj.mpr ⟨hj,h1,h2⟩,fun h=>disjoint_left.mp hd h (by simp),
    fun h=>disjoint_left.mp hd h (by simp)⟩
end SemCodes
section SemArms
variable {n : ℕ} {G : Fin n→ Fin n→ Prop} {Good : Fin n→ Prop} {D : Dag}
theorem z14 (hS : za n D) {R : ℕ→ ℕ→ Prop} (hR : ∀ a b,R a b→ qy n D a b)
    {a b : ℕ} (h : Relation.ReflTransGen R a b) : a≤ b:=by
  induction h with
  | refl=>exact le_refl _
  | tail _ hbc ih=>exact le_trans ih (le_of_lt (z1o hS (hR _ _ hbc)))
theorem vx (hG : zc G Good) (h : z0 n D) (hC : z3 n G D)
    (b : Fin n→ ℕ) (hb : qe n D b) (x : Fin n) :
    (yl n D x).card + (merges n D (zb n D {x})).card =
      1 + (({x} : Finset (Fin n))∩z6 n D).card +
        ((z5 n D b).filter (fun u=>x∈supp n D u.1)).card:=by
  have h1:=z66 hG h hC x;have h2:=w6 h.1 b hb {x};have h3 : (z5 n D b).filter (fun u=>(supp n D u.1∩{x}).Nonempty) =
      (z5 n D b).filter (fun u=>x∈supp n D u.1):=by
    refine Finset.filter_congr (fun u _=>?_)
    constructor
    · rintro ⟨y,hy⟩
      rw [mem_inter,mem_singleton] at hy;exact hy.2▸hy.1
    · intro hx
      exact ⟨x,mem_inter.mpr ⟨hx,mem_singleton_self x⟩⟩
  rw [h3] at h2;omega
end SemArms
section SemPaths
variable {n : ℕ} {G : Fin n→ Fin n→ Prop} {Good : Fin n→ Prop} {D : Dag}
theorem vw (a : Fin n) : qa ({a} : Finset (Fin n)) = single a:=by
  funext k;simp [qa,single]
theorem v7 (hS : za n D) (x : Fin n→ Bool) {j : ℕ} (hj : j < D.length)
    (s : Bool) : val D x (n + j) =
      gop (tag D j) (val D x (src D (j,s))) (val D x (src D (j,!s))):=by
  rw [val_gate hS x j hj]
  cases s
  · simp [src]
  · cases tag D j <;> simp [src,Bool.and_comm,Bool.or_comm]
theorem z0n (hG : zc G Good) {i : Fin n} {S : Finset (Fin n)}
    (h : qi G (q9 i (qa S))) :
    (∃ a∈S,G i a)∨∃ a∈S,∃ b∈S,G a b:=by
  obtain ⟨u,v,huv,hu,hv⟩:=h;simp only [q9,qa,Bool.or_eq_true,decide_eq_true_eq] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · rw [hu,hv] at huv;exact absurd huv (hG.2.1 i)
  · rw [hu] at huv;exact Or.inl ⟨v,hv,huv⟩
  · rw [hv] at huv;exact Or.inl ⟨u,hu,hG.1 _ _ huv⟩
  · exact Or.inr ⟨u,hu,v,hv,huv⟩
theorem z37 (hS : za n D) {v b t : ℕ} (h : zn n D v b) (hbt : b≤ t) :
    b = v∨¬ Relation.ReflTransGen (fun a c=>qy n D a c∧c≠b) v t:=by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl=>exact Or.inl rfl
  | @head a c hstep hrest ih=>
    by_cases hba : b = a
    · exact Or.inl hba
    · right
      intro hp
      rcases Relation.ReflTransGen.cases_head hp with heq | ⟨c',hs,hrest'⟩
      · have h1:=z1o hS hstep.1
        have h2:=z14 hS (fun _ _ hab=>hab.1) hrest;omega
      · have hcc : c = c':=x9 hstep.1 hs.1 hstep.2
        subst hcc
        rcases ih with rfl | ih
        · exact hs.2 rfl
        · exact ih hrest'
theorem z4l (hS : za n D) (x y : Fin n→ Bool) (v : Fin n)
    (hxy : ∀ k,k≠v→ x k = y k) (b t : ℕ)
    (hdom : b = v.val∨¬ Relation.ReflTransGen (fun a c=>qy n D a c∧c≠b) v.val t)
    (hb : val D x b = val D y b) : val D x t = val D y t:=by
  by_contra hne
  rcases hdom with rfl | hdom
  · rw [val_input D x _ v.isLt,val_input D y _ v.isLt] at hb
    have hxy2 : x = y:=by
      funext k
      by_cases hk : k = v
      · rw [hk];exact hb
      · exact hxy k hk
    exact hne (by rw [hxy2])
  · exact hdom (z13
      (fun a c h=>⟨h.1,fun hc=>h.2 (by rw [hc];exact hb)⟩)
      (v9 hS x y v hxy _ hne))
theorem z45 (hS : za n D) {a c q : ℕ} (hc : zn n D a c)
    (hq : Relation.ReflTransGen (qy n D) a q) :
    Relation.ReflTransGen (qy n D) c q∨(zn n D q c∧q≠c):=by
  revert hq
  induction hc using Relation.ReflTransGen.head_induction_on with
  | refl=>exact fun hq=>Or.inl hq
  | @head a a' hstep hrest ih=>
    intro hq
    rcases Relation.ReflTransGen.cases_head hq with heq | ⟨a'',hs,hrest'⟩
    · right
      have h1:=z1o hS hstep.1;have h2:=z14 hS (fun _ _ hab=>hab.1) hrest
      refine ⟨?_,by omega⟩
      rw [← heq];exact Relation.ReflTransGen.head hstep hrest
    · have hcc : a' = a'':=x9 hstep.1 hs hstep.2
      subst hcc;exact ih hrest'
theorem z2s (hS : za n D) (v : Fin n) {j : ℕ} (hj : j < D.length) (s : Bool)
    (hch : zn n D v.val (src D (j,!s))) (hf : zd D (src D (j,!s)) = 1)
    (x y : Fin n→ Bool) (hxy : ∀ k,k≠v→ x k = y k) :
    val D x (src D (j,s)) = val D y (src D (j,s)):=by
  by_contra hne
  have hp : Relation.ReflTransGen (qy n D) v.val (src D (j,s)):=
    z13 (fun _ _ h=>h.1) (v9 hS x y v hxy _ hne)
  have hstepc : qy n D (src D (j,!s)) (n + j):=vm hj (!s);have hstepq : qy n D (src D (j,s)) (n + j):=vm hj s;have hlt1:=z12 hS hj s;have hlt2:=z12 hS hj (!s)
  rcases z45 hS hch hp with h1 | ⟨h1,h2⟩
  · rcases Relation.ReflTransGen.cases_head h1 with heq | ⟨c',hs,hrest⟩
    · exact z5t hS hj s heq.symm
    · have hcc : n + j = c':=x9 hstepc hs hf
      subst hcc
      have:=z14 hS (fun _ _ h=>h) hrest
      omega
  · rcases Relation.ReflTransGen.cases_head h1 with heq | ⟨q',hs,hrest⟩
    · exact h2 heq
    · have hcc : n + j = q':=x9 hstepq hs.1 hs.2
      subst hcc
      have:=z14 hS (fun _ _ h=>h.1) hrest
      omega
theorem z29 (hS : za n D) (hC : z3 n G D) (x : Fin n→ Bool) (v : Fin n)
    (b : ℕ) (hdom : z23 n D b v.val) (h0 : ¬ qi G x) (h1 : qi G (q9 v x)) :
    val D x b = false∧val D (q9 v x) b = true:=by
  have hne : val D x b≠val D (q9 v x) b:=by
    intro heq;have h2:=z43 hS x _ v (w9 v x) b hdom heq;exact h0 ((hC x).mp (by rw [h2];exact (hC _).mpr h1))
  have hmono:=val_mono hS x (q9 v x) (z2i v x) b
  cases hx : val D x b
  · refine ⟨rfl,?_⟩
    cases hy : val D (q9 v x) b
    · exact absurd (hx.trans hy.symm) hne
    · rfl
  · exact absurd (hx.trans (hmono hx).symm) hne
theorem z5u (hS : za n D) (i : Fin n) (w : ℕ) (hch : zn n D i.val w)
    (Bs N : Finset (Fin n)) (hN : N⊆Bs)
    (h0 : val D (q9 i (qa (Bs \ N))) w = false)
    (h1 : ∀ a∈N,val D (q9 i (qa {a})) w = true)
    (hz : ∀ a∈N,val D (qa {a}) w = false) :
    ∃ j s,j < D.length∧tag D j = true∧n + j≤ w∧
      zn n D i.val (src D (j,!s))∧supp n D (src D (j,s))∩Bs = N:=by
  have hJ : ∀ c,zn n D i.val c→ (val D (q9 i (qa (Bs \ N))) c = true∨
      ∃ j s,j < D.length∧tag D j = true∧n + j≤ c∧zn n D i.val (src D (j,!s))∧
        zd D (src D (j,!s)) = 1∧val D (qa (Bs \ N)) (src D (j,s)) = false):=by
    intro c hc
    induction hc with
    | refl=>left;rw [val_input D _ _ i.isLt];exact xq i _
    | tail hab hbc ih=>
      obtain ⟨j,s,hj,rfl,rfl⟩:=z54.mp hbc.1;have hlt:=z12 hS hj s
      rcases ih with hy | ⟨j',s',hj',ht',hle,hc',hf',hv'⟩
      · cases ht : tag D j
        · left
          rw [v7 hS _ hj s,ht,gop_false,hy];rfl
        · by_cases hq : val D (q9 i (qa (Bs \ N))) (src D (j,!s)) = true
          · left
            rw [v7 hS _ hj s,ht,gop_true,hy,hq];rfl
          · right
            refine ⟨j,!s,hj,ht,le_refl _,by rw [Bool.not_not];exact hab,
              by rw [Bool.not_not];exact hbc.2,?_⟩
            by_contra hc2
            rw [Bool.not_eq_false] at hc2;exact hq (val_mono hS _ _ (z2i i _) _ hc2)
      · right
        exact ⟨j',s',hj',ht',by omega,hc',hf',hv'⟩
  rcases hJ w hch with hy | ⟨j,s,hj,ht,hle,hc,hf,hv⟩
  · rw [h0] at hy
    exact absurd hy Bool.false_ne_true
  · refine ⟨j,s,hj,ht,hle,hc,?_⟩
    have hchg : zn n D i.val (n + j):=
      Relation.ReflTransGen.tail hc ⟨vm hj (!s),hf⟩
    ext a
    rw [mem_inter]
    constructor
    · rintro ⟨ha1,ha2⟩
      by_contra haN
      have:=x8 hS ha1 (x:=qa (Bs \ N))
        (by simp [qa,ha2,haN])
      rw [hv] at this;exact Bool.false_ne_true this
    · intro haN
      refine ⟨?_,hN haN⟩
      have hgne : val D (qa {a}) (n + j)≠val D (q9 i (qa {a})) (n + j):=by
        intro heq;have h2:=z4l hS _ _ i (w9 i (qa {a})) (n + j) w
          (z37 hS hchg hle) heq
        rw [hz a haN,h1 a haN] at h2;exact Bool.false_ne_true h2
      have hgy : val D (q9 i (qa {a})) (n + j) = true:=by
        by_contra hc2
        rw [Bool.not_eq_true] at hc2
        apply hgne
        rw [hc2]
        by_contra hc3
        rw [Bool.not_eq_false] at hc3;rw [val_mono hS _ _ (z2i i _) _ hc3] at hc2;exact Bool.noConfusion hc2
      rw [v7 hS _ hj s,ht,gop_true,Bool.and_eq_true] at hgy;have hind:=z2s hS i hj s hc hf _ _ (w9 i (qa {a}));rw [hgy.1,vw] at hind;exact mem_supp.mpr hind
theorem z2t (hS : za n D) (i : Fin n) (w : ℕ) (hch : zn n D i.val w)
    (Bs : Finset (Fin n))
    (h0 : ∀ S : Finset (Fin n),S⊆Bs→ (∀ a∈S,¬ G i a)→
      val D (q9 i (qa S)) w = false)
    (h1 : ∀ a∈Bs,G i a→
      val D (q9 i (qa {a})) w = true∧val D (qa {a}) w = false) :
    ∃ j s,j < D.length∧tag D j = true∧n + j≤ w∧
      zn n D i.val (src D (j,!s))∧
      ∀ a∈Bs,(a∈supp n D (src D (j,s))↔G i a):=by
  classical
  obtain ⟨j,s,hj,ht,hle,hc,hsupp⟩:=z5u hS i w hch Bs (Bs.filter (fun a=>G i a))
    (filter_subset _ _)
    (h0 _ sdiff_subset (fun a ha hia=>by
      rw [mem_sdiff,mem_filter] at ha;exact ha.2 ⟨ha.1,hia⟩))
    (fun a ha=>(h1 a (mem_filter.mp ha).1 (mem_filter.mp ha).2).1)
    (fun a ha=>(h1 a (mem_filter.mp ha).1 (mem_filter.mp ha).2).2)
  refine ⟨j,s,hj,ht,hle,hc,fun a ha=>?_⟩
  constructor
  · intro has
    have : a∈supp n D (src D (j,s))∩Bs:=mem_inter.mpr ⟨has,ha⟩;rw [hsupp,mem_filter] at this;exact this.2
  · intro hia
    have : a∈Bs.filter (fun a=>G i a):=mem_filter.mpr ⟨ha,hia⟩;rw [← hsupp] at this;exact (mem_inter.mp this).1
theorem z0o (hG : zc G Good) (hS : za n D) (hC : z3 n G D) {i : Fin n}
    (hiG : Good i) (hi : i∈z1 n D) {b : ℕ} (hch : zn n D i.val b) (hf : 2≤ zd D b) :
    supp n D b = ∅:=by
  have hsub:=ys hG hS hC i hiG b (qk hS hch)
  refine eq_empty_of_forall_notMem (fun x hx=>?_)
  have h1:=hsub hx;rw [mem_singleton] at h1;have h2:=mem_ineligSet.mp hi b (h1▸hx);omega
theorem z1p {a t : ℕ} (hp : Relation.ReflTransGen (qy n D) a t) :
    zn n D a t∨∃ b,zn n D a b∧2≤ zd D b:=by
  induction hp using Relation.ReflTransGen.head_induction_on with
  | refl=>exact Or.inl Relation.ReflTransGen.refl
  | @head a a' hstep _ ih=>
    by_cases hf : zd D a = 1
    · rcases ih with h1 | ⟨b,h1,h2⟩
      · exact Or.inl (Relation.ReflTransGen.head ⟨hstep,hf⟩ h1)
      · exact Or.inr ⟨b,Relation.ReflTransGen.head ⟨hstep,hf⟩ h1,h2⟩
    · have:=z1f hstep
      exact Or.inr ⟨a,Relation.ReflTransGen.refl,by omega⟩
theorem v8 (hG : zc G Good) (h : z0 n D) (hC : z3 n G D)
    {i : Fin n} (hiG : Good i) (hi : i∈z1 n D) :
    zn n D i.val (qc n D)∨
      ∃ b,zn n D i.val b∧2≤ zd D b∧supp n D b = ∅:=by
  have hlt : i.val < n + D.length:=by have:=i.isLt;omega
  have hp : Relation.ReflTransGen (qy n D) i.val (qc n D):=live_reaches_out h i.val hlt
  rcases z1p hp with h1 | ⟨b,h1,h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨b,h1,h2,z0o hG h.1 hC hiG hi h1 h2⟩
theorem z0b (hS : za n D) {b : ℕ} (hf : 2≤ zd D b) (he : supp n D b = ∅) :
    b∈(inner n D).filter (fun w=>¬ (supp n D w).Nonempty):=
  mem_filter.mpr ⟨qm.mpr (lt_of_fanout_pos hS (w:=b) (by omega)),
    by rw [he];exact not_nonempty_empty⟩
theorem z39 (hS : za n D) (hB0 : qd n D = 0) {b : ℕ} (hf : 2≤ zd D b) :
    (supp n D b).Nonempty:=by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne;have h1 : zd D b - 1≤ ∑ w∈(inner n D).filter (fun w=>¬ (supp n D w).Nonempty),
      (zd D w - 1):=
    Finset.single_le_sum (f:=fun w=>zd D w - 1) (fun _ _=>Nat.zero_le _)
      (z0b hS hf hne)
  unfold qd zw at hB0;omega
theorem z38 (hS : za n D) (hB0 : qd n D≤ 1) {b b' : ℕ}
    (hf : 2≤ zd D b) (he : supp n D b = ∅) (hf' : 2≤ zd D b')
    (he' : supp n D b' = ∅) : b = b':=by
  by_contra hne
  have hsub : ({b,b'} : Finset ℕ)⊆(inner n D).filter (fun w=>¬ (supp n D w).Nonempty):=by
    intro c hc;rw [mem_insert,mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact z0b hS hf he
    · exact z0b hS hf' he'
  have h1:=sum_le_sum_of_subset (f:=fun w=>zd D w - 1) hsub;rw [Finset.sum_pair hne] at h1;unfold qd zw at hB0;omega
theorem z2h (hG : zc G Good) (h : z0 n D) (hC : z3 n G D)
    (hB0 : qd n D = 0) {i : Fin n} (hiG : Good i) (hi : i∈z1 n D) {w : ℕ}
    (hp : Relation.ReflTransGen (qy n D) i.val w) : zn n D i.val w:=by
  rcases z1p hp with h1 | ⟨b,h1,h2⟩
  · exact h1
  · have h3:=z39 h.1 hB0 h2
    rw [z0o hG h.1 hC hiG hi h1 h2] at h3;exact absurd h3 not_nonempty_empty
theorem xg (hG : zc G Good) (h : z0 n D) (hC : z3 n G D)
    (hB0 : qd n D = 0) {i : Fin n} (hiG : Good i) (hi : i∈z1 n D) :
    zn n D i.val (qc n D):=
  z2h hG h hC hB0 hiG hi
    (live_reaches_out h i.val (by have:=i.isLt;omega))
theorem x1 (hG : zc G Good) (hS : za n D) (hC : z3 n G D)
    (Bs : Finset (Fin n)) (hBs : ∀ a∈Bs,∀ b∈Bs,¬ G a b) {i : Fin n}
    (hch : zn n D i.val (qc n D)) :
    ∃ j s,j < D.length∧tag D j = true∧zn n D i.val (src D (j,!s))∧
      ∀ a∈Bs,(a∈supp n D (src D (j,s))↔G i a):=by
  obtain ⟨j,s,hj,ht,-,hc,hsupp⟩:=z2t (G:=G) hS i (qc n D) hch Bs
    (fun S hS1 hS2=>by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      rcases z0n hG ((hC _).mp hc) with ⟨a,ha,hia⟩ | ⟨a,ha,b,hb,hab⟩
      · exact hS2 a ha hia
      · exact hBs a (hS1 ha) b (hS1 hb) hab)
    (fun a _ hia=>by
      constructor
      · exact (hC _).mpr ⟨i,a,hia,xq i _,by simp [q9,qa]⟩
      · by_contra hc
        rw [Bool.not_eq_false,vw] at hc;exact qr hG a ((hC _).mp hc))
  exact ⟨j,s,hj,ht,hc,hsupp⟩
theorem z0k (hG : zc G Good) (hS : za n D) (hC : z3 n G D)
    (Bs : Finset (Fin n)) (hBs : ∀ a∈Bs,∀ b∈Bs,¬ G a b) {i j : Fin n} {w : ℕ}
    (hch : zn n D i.val w) (hdj : z23 n D w j.val)
    (hnsub : ∃ a∈Bs,G j a∧¬ G i a) :
    ∃ k s,k < D.length∧tag D k = true∧n + k≤ w∧
      zn n D i.val (src D (k,!s))∧
      ∀ a∈Bs,(a∈supp n D (src D (k,s))↔G i a):=by
  classical
  have hX0 : ¬ qi G (q9 i (qa (Bs.filter (fun a=>¬ G i a)))):=by
    intro hc
    rcases z0n hG hc with ⟨a,ha,hia⟩ | ⟨a,ha,b,hb,hab⟩
    · exact (mem_filter.mp ha).2 hia
    · exact hBs a (mem_filter.mp ha).1 b (mem_filter.mp hb).1 hab
  obtain ⟨a0,ha0,hja0,hia0⟩:=hnsub;have hX1 : qi G (q9 j (q9 i (qa (Bs.filter (fun a=>¬ G i a))))):=
    ⟨j,a0,hja0,xq j _,by simp [q9,qa,ha0,hia0]⟩
  have hwX:=(z29 hS hC _ j w hdj hX0 hX1).1
  refine z2t hS i w hch Bs (fun S hS1 hS2=>?_) (fun a _ hia=>?_)
  · by_contra hc
    rw [Bool.not_eq_false] at hc;have hmono:=val_mono hS (q9 i (qa S))
      (q9 i (qa (Bs.filter (fun a=>¬ G i a)))) (fun k hk=>by
        simp only [q9,qa,Bool.or_eq_true,decide_eq_true_eq] at hk ⊢
        rcases hk with hk | hk
        · exact Or.inl hk
        · exact Or.inr (mem_filter.mpr ⟨hS1 hk,hS2 k hk⟩)) w hc
    rw [hwX] at hmono;exact Bool.false_ne_true hmono
  · have h2:=z29 hS hC (qa {a}) i w (qk hS hch)
      (by rw [vw];exact qr hG a)
      ⟨i,a,hia,xq i _,by simp [q9,qa]⟩
    exact ⟨h2.2,h2.1⟩
theorem z0l (hG : zc G Good) (h : z0 n D) (hC : z3 n G D)
    (hB0 : qd n D≤ 1) (Bs : Finset (Fin n)) (hBs : ∀ a∈Bs,∀ b∈Bs,¬ G a b)
    {i j : Fin n} (hiG : Good i) (hjG : Good j) (hi : i∈z1 n D) (hj : j∈z1 n D)
    (hji : ∃ a∈Bs,G j a∧¬ G i a) :
    (∃ k s,k < D.length∧tag D k = true∧zn n D i.val (src D (k,!s))∧
        ∀ a∈Bs,(a∈supp n D (src D (k,s))↔G i a))∨
      (∃ k s,k < D.length∧tag D k = true∧zn n D j.val (src D (k,!s))∧
        ∀ a∈Bs,(a∈supp n D (src D (k,s))↔G j a)):=by
  have hS:=h.1
  rcases v8 hG h hC hiG hi with h1 | ⟨b,hb1,hb2,hb3⟩
  · exact Or.inl (x1 hG hS hC Bs hBs h1)
  · rcases v8 hG h hC hjG hj with h1 | ⟨b',hb1',hb2',hb3'⟩
    · exact Or.inr (x1 hG hS hC Bs hBs h1)
    · have hbb : b' = b:=z38 hS hB0 hb2' hb3' hb2 hb3
      rw [hbb] at hb1';obtain ⟨k,s,hk,ht,-,hc,hsupp⟩:=z0k hG hS hC Bs hBs hb1
        (qk hS hb1') hji
      exact Or.inl ⟨k,s,hk,ht,hc,hsupp⟩
end SemPaths
section SemDiff
variable {n : ℕ} {G : Fin n→ Fin n→ Prop} {Good : Fin n→ Prop} {D : Dag}
theorem z15 {x y : Fin n} {w : ℕ} :
    w∈zx n D x y↔x∈supp n D w∧y∉supp n D w:=by
  simp only [zx,mem_filter,Finset.mem_range];exact ⟨fun h=>h.2,fun h=>⟨yf h.1,h⟩⟩
theorem wr {x y : Fin n} {e : ℕ×Bool} :
    e∈zk n D (zx n D x y)↔e.1 < D.length∧
      (x∈supp n D (src D e)∧y∉supp n D (src D e))∧
      ¬ (x∈supp n D (n + e.1)∧y∉supp n D (n + e.1)):=by
  simp only [zk,arcs,mem_filter,Finset.mem_product,Finset.mem_range,
    mem_univ,and_true,z15]
theorem z34 (hS : za n D) (b : Fin n→ ℕ) (hb : qe n D b)
    {x y : Fin n} (hxy : x≠y) (hx : x∈z6 n D) :
    zw D (zx n D x y) = 1 + ((z5 n D b).filter
      (fun u=>x∈supp n D u.1∧y∉supp n D u.1)).card:=by
  have h1 : zw D (zx n D x y) =
      ((units n D).filter (fun u=>x∈supp n D u.1∧y∉supp n D u.1)).card:=by
    rw [xm n D (fun w=>x∈supp n D w∧y∉supp n D w)]
    symm
    refine Finset.sum_subset (fun w hw=>?_) (fun w hw hnot=>?_)
    · rw [mem_filter] at hw
      exact z15.mpr hw.2
    · have hni : w∉inner n D:=fun hc=>hnot (mem_filter.mpr ⟨hc,z15.mp hw⟩)
      rw [qm] at hni;simp [yv hS w (by omega)]
  have h2 : (units n D).filter (fun u=>x∈supp n D u.1∧y∉supp n D u.1) =
      {(⟨b x,0⟩ : Σ _ : ℕ,ℕ)}∪(z5 n D b).filter
        (fun u=>x∈supp n D u.1∧y∉supp n D u.1):=by
    ext u
    have hsub:=reserved_subset hS b hb;simp only [z5,wo,mem_union,mem_filter,mem_sdiff,
      mem_singleton]
    constructor
    · intro hu
      by_cases hr : u∈reservedUnits n D b
      · left
        obtain ⟨v,hv,rfl⟩:=mem_image.mp hr;have hxv:=hu.2.1;rw [(hb v hv).2,mem_singleton] at hxv;rw [hxv]
      · exact Or.inr ⟨⟨⟨hu.1,⟨x,hu.2.1⟩⟩,hr⟩,hu.2⟩
    · rintro (rfl | hu)
      · have hbx:=hb x hx
        refine ⟨(mem_filter.mp (hsub (mem_image.mpr ⟨x,hx,rfl⟩))).1,?_,?_⟩
        · rw [hbx.2];exact mem_singleton_self x
        · rw [hbx.2,mem_singleton];exact fun hc=>hxy hc.symm
      · exact ⟨hu.1.1.1,hu.2⟩
  have h3 : (⟨b x,0⟩ : Σ _ : ℕ,ℕ)∉(z5 n D b).filter
      (fun u=>x∈supp n D u.1∧y∉supp n D u.1):=by
    intro hc;exact (mem_sdiff.mp (mem_filter.mp hc).1).2 (mem_image.mpr ⟨x,hx,rfl⟩)
  rw [h1,h2,Finset.singleton_union,Finset.card_insert_of_notMem h3];omega
theorem z3p (hS : za n D) {x y : Fin n} (hxy : x≠y) {w : ℕ}
    (hw : x∈supp n D w∧y∈supp n D w) :
    ∃ j s,j < D.length∧tag D j = false∧x∈supp n D (n + j)∧y∈supp n D (n + j)∧
      x∈supp n D (src D (j,s))∧y∉supp n D (src D (j,s))∧
      y∈supp n D (src D (j,!s))∧x∉supp n D (src D (j,!s)):=by
  classical
  have hex : ∃ u,x∈supp n D u∧y∈supp n D u:=⟨w,hw⟩;obtain ⟨h1,h2⟩:=Nat.find_spec hex;have hmin : ∀ u,u < Nat.find hex→ ¬ (x∈supp n D u∧y∈supp n D u):=
    fun u hu=>Nat.find_min hex hu
  generalize Nat.find hex = f at h1 h2 hmin
  have hlt:=yf h1;have hn : n≤ f:=by
    by_contra hc
    have hs : supp n D f = {⟨f,by omega⟩}:=supp_input D ⟨f,by omega⟩;rw [hs,mem_singleton] at h1 h2;exact hxy (h1.trans h2.symm)
  obtain ⟨j,rfl⟩ : ∃ j,f = n + j:=⟨f - n,by omega⟩;have hj : j < D.length:=by omega
  obtain ⟨ha,hb,-⟩:=hS j hj;have hna:=hmin _ ha;have hnb:=hmin _ hb
  cases ht : tag D j
  · have h1':=h1
    have h2':=h2;rw [yq hS hj ht,mem_union] at h1' h2'
    refine ⟨j,?_⟩
    rcases h1' with hxa | hxb
    · have hya : y∉supp n D (opA D j):=fun hc=>hna ⟨hxa,hc⟩
      have hyb : y∈supp n D (opB D j):=h2'.resolve_left hya;exact ⟨false,hj,ht,h1,h2,by simpa [src] using hxa,by simpa [src] using hya,
        by simpa [src] using hyb,by simpa [src] using fun hc=>hnb ⟨hc,hyb⟩⟩
    · have hyb : y∉supp n D (opB D j):=fun hc=>hnb ⟨hxb,hc⟩
      have hya : y∈supp n D (opA D j):=h2'.resolve_right hyb;exact ⟨true,hj,ht,h1,h2,by simpa [src] using hxb,by simpa [src] using hyb,
        by simpa [src] using hya,by simpa [src] using fun hc=>hna ⟨hc,hya⟩⟩
  · exfalso
    rw [yr hS hj ht,mem_inter] at h1 h2;exact hna ⟨h1.1,h2.1⟩
theorem z2k (hG : zc G Good) (h : z0 n D) (hC : z3 n G D)
    (b : Fin n→ ℕ) (hb : qe n D b) {x c z : Fin n} (hxc : x≠c)
    (hx : x∈z6 n D)
    (hres : ∀ u∈z5 n D b,x∈supp n D u.1→ c∈supp n D u.1)
    {w : ℕ} (hw : x∈supp n D w∧c∈supp n D w) (hxz : G x z) (hcz : ¬ G c z) :
    zw D (zx n D x c) = 1∧merges n D (zx n D x c) = ∅∧
      (zk n D (zx n D x c)).card = 2∧
      ∃ e∈zk n D (zx n D x c),tag D e.1 = false∧c∈supp n D (n + e.1):=by
  have hS:=h.1;have hsur : zw D (zx n D x c) = 1:=by
    rw [z34 hS b hb hxc hx,Finset.filter_eq_empty_iff.mpr
      (fun u hu hc=>hc.2 (hres u hu hc.1)),card_empty]
  have hfl:=z31 h x c hxc
    (by rw [ye hG hC];exact notMem_empty x)
  rw [hsur] at hfl;obtain ⟨j1,s1,hj1,ht1,hx1,hc1,hxs1,hcs1,-,-⟩:=z3p hS hxc hw;have he1 : (j1,s1)∈zk n D (zx n D x c):=
    wr.mpr ⟨hj1,⟨hxs1,hcs1⟩,fun hc=>hc.2 hc1⟩
  have hA : ∀ u∈({c,z} : Finset (Fin n)),∀ v∈({c,z} : Finset (Fin n)),¬ G u v:=by
    intro u hu v hv;simp only [mem_insert,mem_singleton] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv <;> rw [hu,hv]
    · exact hG.2.1 c
    · exact hcz
    · exact fun hc=>hcz (hG.1 _ _ hc)
    · exact hG.2.1 z
  obtain ⟨j2,s2,hj2,-,hx2,hn2,hd2⟩:=x7 hG hS hC {c,z} hA x ⟨z,by simp,hxz⟩;have he2 : (j2,s2)∈zk n D (zx n D x c):=
    wr.mpr ⟨hj2,⟨hx2,fun hc=>disjoint_left.mp hd2 hc (by simp)⟩,
      fun hc=>hn2 hc.1⟩
  have hne : (j1,s1)≠(j2,s2):=by
    intro heq;rw [Prod.mk.injEq] at heq;exact hn2 (heq.1▸hx1)
  have h2 : 2≤ (zk n D (zx n D x c)).card:=
    one_lt_card.mpr ⟨_,he1,_,he2,hne⟩
  exact ⟨hsur,card_eq_zero.mp (by omega),by omega,(j1,s1),he1,ht1,hc1⟩
end SemDiff
def qq (n : ℕ) (D : Dag) (P M : Finset (Fin n)) : Prop:=∃ w,supp n D w∩P = M
def z11 (n : ℕ) (D : Dag) (P : Finset (Fin n)) : Finset ℕ:=
  (merges n D (zb n D P)).filter (fun j=>2≤ (supp n D (n + j)∩P).card)
def xh (n : ℕ) (D : Dag) (P U : Finset (Fin n)) (f : Fin n) (e : ℕ×Bool) : Prop:=
  e.1 < D.length∧tag D e.1 = true∧f∈P∧f∈supp n D (src D e)∧
    f∉supp n D (n + e.1)∧supp n D (src D e)∩P⊆U∧(supp n D (src D e)∩P).card≤ 2
def qx (n : ℕ) (D : Dag) (P : Finset (Fin n)) (e : ℕ×Bool) : (ℕ×Bool) ⊕ ℕ:=
  if supp n D (n + e.1)∩P = ∅ then Sum.inl e else Sum.inr e.1
def z42 (n : ℕ) (D : Dag) (P : Finset (Fin n)) (c : (ℕ×Bool) ⊕ ℕ) : Prop:=
  Sum.elim (fun e=>e∈zk n D (zb n D P)∧(supp n D (src D e)∩P).card≤ 2)
    (fun j=>j∈merges n D (zb n D P)∧(supp n D (n + j)∩P).card = 1) c
section SupMask
variable {n : ℕ} {D : Dag}
theorem z0z (P : Finset (Fin n)) (w : ℕ) : qq n D P (supp n D w∩P):=⟨w,rfl⟩
theorem z1n {P M : Finset (Fin n)} (h : qq n D P M) : M⊆P:=by
  obtain ⟨w,rfl⟩:=h;exact inter_subset_right
theorem y9 {P : Finset (Fin n)} {w : ℕ} :
    w∈zb n D P↔(supp n D w∩P).Nonempty:=by
  simp only [zb,mem_filter,Finset.mem_range]
  constructor
  · exact fun h=>h.2
  · intro h
    obtain ⟨v,hv⟩:=h;exact ⟨yf (mem_inter.mp hv).1,v,hv⟩
theorem z5a (hS : za n D) {P M : Finset (Fin n)} (hM : 2≤ M.card)
    (h : qq n D P M) : ∃ j∈z11 n D P,supp n D (n + j)∩P = M:=by
  obtain ⟨w,hw⟩:=h;obtain ⟨j,-,-,hj,hmer,-,-⟩:=wt hS P M hM w hw;exact ⟨j,mem_filter.mpr ⟨hmer,by rw [hj];exact hM⟩,hj⟩
theorem z3n (hS : za n D) (P : Finset (Fin n)) (F : Finset (Finset (Fin n)))
    (hF : ∀ M∈F,2≤ M.card∧qq n D P M) : F.card≤ (z11 n D P).card:=by
  have hsub : F⊆(z11 n D P).image (fun j=>supp n D (n + j)∩P):=by
    intro M hM;obtain ⟨j,hj,hjM⟩:=z5a hS (hF M hM).1 (hF M hM).2;exact mem_image.mpr ⟨j,hj,hjM⟩
  exact (card_le_card hsub).trans Finset.card_image_le
theorem z2q (hS : za n D) {P T : Finset (Fin n)} (hP : P.card≤ 7)
    (hT : T.card = 3) (h : qq n D P T) :
    (∃ A,qq n D P A∧A.card = 2∧A⊆T)∨
      (∃ A,qq n D P A∧A.card = 4∧T⊆A)∨
      (∃ A B,A≠B∧qq n D P A∧qq n D P B∧A.card = 5∧B.card = 5∧
        T⊆A∧T⊆B∧A∩B = T):=by
  obtain ⟨w,hw⟩:=h;obtain ⟨j,hj,-,hjT,-,-,hpar⟩:=wt hS P T (by omega) w hw;have hoA : qq n D P (supp n D (opA D j)∩P):=z0z P _;have hoB : qq n D P (supp n D (opB D j)∩P):=z0z P _
  rcases hpar with ⟨ht,hA,hB⟩ | ⟨-,hA,hB,hun,-,-⟩
  · have hAB : (supp n D (opA D j)∩P)∩(supp n D (opB D j)∩P) = T:=by
      rw [← hjT,yr hS hj ht]
      ext v
      simp only [mem_inter];tauto
    generalize supp n D (opA D j)∩P = A at hoA hA hAB
    generalize supp n D (opB D j)∩P = B at hoB hB hAB
    have hcA:=card_lt_card hA;have hcB:=card_lt_card hB;have hu : (A∪B).card≤ 7:=
      (card_le_card (union_subset (z1n hoA) (z1n hoB))).trans hP
    have hie:=Finset.card_union_add_card_inter A B;rw [hAB] at hie
    by_cases h4 : A.card = 4
    · exact Or.inr (Or.inl ⟨A,hoA,h4,hA.subset⟩)
    by_cases h4' : B.card = 4
    · exact Or.inr (Or.inl ⟨B,hoB,h4',hB.subset⟩)
    refine Or.inr (Or.inr ⟨A,B,?_,hoA,hoB,by omega,by omega,hA.subset,hB.subset,hAB⟩)
    intro hEq;rw [hEq,inter_self] at hAB;rw [hAB] at hcB;omega
  · generalize supp n D (opA D j)∩P = A at hoA hA hun
    generalize supp n D (opB D j)∩P = B at hoB hB hun
    have hcA:=card_lt_card hA;have hcB:=card_lt_card hB;have hc:=Finset.card_union_le A B;rw [hun] at hc
    by_cases h2 : A.card = 2
    · exact Or.inl ⟨A,hoA,h2,hA.subset⟩
    · exact Or.inl ⟨B,hoB,by omega,hB.subset⟩
theorem z3l {T T' A : Finset (Fin n)} (hA : A.card = 2) (h1 : A⊆T)
    (h2 : A⊆T') (hint : T≠T'→ (T∩T').card≤ 1) : T = T':=by
  by_contra hne
  have h3:=card_le_card (Finset.subset_inter h1 h2);have h4:=hint hne;omega
theorem z3m {T T' A : Finset (Fin n)} (hT : T.card = 3) (hT' : T'.card = 3)
    (hA : A.card = 4) (h1 : T⊆A) (h2 : T'⊆A) (hint : T≠T'→ (T∩T').card≤ 1) :
    T = T':=by
  by_contra hne
  have h3:=card_le_card (union_subset h1 h2);have h4:=Finset.card_union_add_card_inter T T';have h5:=hint hne;omega
theorem z52 {T1 T2 T3 A : Finset (Fin n)} (h1 : T1.card = 3) (h2 : T2.card = 3)
    (h3 : T3.card = 3) (hA : A.card≤ 5) (s1 : T1⊆A) (s2 : T2⊆A) (s3 : T3⊆A)
    (i12 : (T1∩T2).card≤ 1) (i13 : (T1∩T3).card≤ 1) (i23 : (T2∩T3).card≤ 1) :
    False:=by
  have hu:=card_le_card (union_subset (union_subset s1 s2) s3);have e1:=Finset.card_union_add_card_inter T1 T2;have e2:=Finset.card_union_add_card_inter (T1∪T2) T3;have e3 : ((T1∪T2)∩T3).card≤ (T1∩T3).card + (T2∩T3).card:=by
    rw [Finset.union_inter_distrib_right];exact Finset.card_union_le _ _
  omega
theorem z41 (hS : za n D) {P : Finset (Fin n)} (hP : P.card≤ 7)
    (L : Finset (Finset (Fin n))) (h3 : ∀ T∈L,T.card = 3∧qq n D P T)
    (hint : ∀ T∈L,∀ T'∈L,T≠T'→ (T∩T').card≤ 1) :
    ∃ Aux : Finset (Finset (Fin n)),L.card≤ Aux.card∧∀ A∈Aux,qq n D P A∧
      ((A.card = 2∧∃ T∈L,A⊆T)∨A.card = 4∨A.card = 5):=by
  classical
  refine ⟨P.powerset.filter (fun A=>qq n D P A∧
      ((A.card = 2∧∃ T∈L,A⊆T)∨A.card = 4∨A.card = 5)),?_,
    fun A hA=>(mem_filter.mp hA).2⟩
  generalize hAux : P.powerset.filter (fun A=>qq n D P A∧
      ((A.card = 2∧∃ T∈L,A⊆T)∨A.card = 4∨A.card = 5)) = Aux
  have hmem : ∀ A,qq n D P A→
      ((A.card = 2∧∃ T∈L,A⊆T)∨A.card = 4∨A.card = 5)→ A∈Aux:=by
    intro A h1 h2;rw [← hAux];exact mem_filter.mpr ⟨Finset.mem_powerset.mpr (z1n h1),h1,h2⟩
  have hprop : ∀ A∈Aux,(A.card = 2∧∃ T∈L,A⊆T)∨A.card = 4∨A.card = 5:=by
    intro A hA;rw [← hAux] at hA;exact (mem_filter.mp hA).2.2
  have hrow : ∀ T∈L,2≤ ∑ A∈Aux,
      (if A.card = 5 then (if T⊆A then 1 else 0) else (if A⊆T∨T⊆A then 2 else 0)):=by
    intro T hT
    rcases z2q hS hP (h3 T hT).1 (h3 T hT).2 with
      ⟨A,ho,hc,hs⟩ | ⟨A,ho,hc,hs⟩ | ⟨A,B,hne,hoA,hoB,hcA,hcB,hsA,hsB,-⟩
    · refine le_trans ?_ (Finset.single_le_sum (fun _ _=>Nat.zero_le _)
        (hmem A ho (Or.inl ⟨hc,T,hT,hs⟩)))
      simp [hc,hs]
    · refine le_trans ?_ (Finset.single_le_sum (fun _ _=>Nat.zero_le _)
        (hmem A ho (Or.inr (Or.inl hc))))
      simp [hc,hs]
    · have hsub : ({A,B} : Finset (Finset (Fin n)))⊆Aux:=by
        intro x hx;rw [mem_insert,mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hmem _ hoA (Or.inr (Or.inr hcA))
        · exact hmem _ hoB (Or.inr (Or.inr hcB))
      refine le_trans ?_ (sum_le_sum_of_subset hsub)
      rw [Finset.sum_pair hne];simp [hcA,hcB,hsA,hsB]
  have hcol : ∀ A∈Aux,∑ T∈L,
      (if A.card = 5 then (if T⊆A then 1 else 0) else (if A⊆T∨T⊆A then 2 else 0))≤ 2:=by
    intro A hA
    by_cases h5 : A.card = 5
    · have hsum : ∑ T∈L,(if A.card = 5 then (if T⊆A then 1 else 0)
          else (if A⊆T∨T⊆A then 2 else 0)) = (L.filter (fun T=>T⊆A)).card:=by
        rw [Finset.card_filter];exact sum_congr rfl (fun T _=>by simp [h5])
      rw [hsum]
      by_contra hgt
      obtain ⟨T1,T2,T3,m1,m2,m3,n12,n13,n23⟩:=
        Finset.two_lt_card_iff.mp (show 2 < (L.filter (fun T=>T⊆A)).card by omega)
      rw [mem_filter] at m1 m2 m3;exact z52 (h3 _ m1.1).1 (h3 _ m2.1).1 (h3 _ m3.1).1 h5.le m1.2 m2.2 m3.2
        (hint _ m1.1 _ m2.1 n12) (hint _ m1.1 _ m3.1 n13) (hint _ m2.1 _ m3.1 n23)
    · have hsum : ∑ T∈L,(if A.card = 5 then (if T⊆A then 1 else 0)
          else (if A⊆T∨T⊆A then 2 else 0)) =
          2 * (L.filter (fun T=>A⊆T∨T⊆A)).card:=by
        rw [Finset.card_filter,Finset.mul_sum];exact sum_congr rfl (fun T _=>by simp [h5])
      rw [hsum];have hle : (L.filter (fun T=>A⊆T∨T⊆A)).card≤ 1:=by
        rw [Finset.card_le_one];intro T hT T' hT';rw [mem_filter] at hT hT';have c3:=(h3 T hT.1).1;have c3':=(h3 T' hT'.1).1
        rcases hprop A hA with ⟨h2,-⟩ | h4 | h5'
        · have e1 : A⊆T:=hT.2.resolve_right (fun h=>by
            have:=card_le_card h;omega)
          have e2 : A⊆T':=hT'.2.resolve_right (fun h=>by
            have:=card_le_card h;omega)
          exact z3l h2 e1 e2 (hint T hT.1 T' hT'.1)
        · have e1 : T⊆A:=hT.2.resolve_left (fun h=>by
            have:=card_le_card h;omega)
          have e2 : T'⊆A:=hT'.2.resolve_left (fun h=>by
            have:=card_le_card h;omega)
          exact z3m c3 c3' h4 e1 e2 (hint T hT.1 T' hT'.1)
        · exact absurd h5' h5
      omega
  have h1:=Finset.card_nsmul_le_sum L _ 2 hrow;have h2:=Finset.sum_le_card_nsmul Aux _ 2 hcol;rw [Finset.sum_comm] at h1;simp only [smul_eq_mul] at h1 h2;omega
theorem z40 (hS : za n D) {P : Finset (Fin n)} (hP : P.card≤ 7)
    (L : Finset (Finset (Fin n))) (h3 : ∀ T∈L,T.card = 3∧qq n D P T)
    (hint : ∀ T∈L,∀ T'∈L,T≠T'→ (T∩T').card≤ 1)
    (X : Finset (Finset (Fin n)))
    (hX : ∀ M∈X,qq n D P M∧2≤ M.card∧M∉L∧M.card≠4∧M.card≠5∧
      (M.card = 2→ ∀ T∈L,¬ M⊆T)) :
    2 * L.card + X.card≤ (z11 n D P).card:=by
  classical
  obtain ⟨Aux,hcard,hAux⟩:=z41 hS hP L h3 hint;have hd1 : Disjoint L Aux:=by
    rw [disjoint_left];intro T hT hTA
    have:=(h3 T hT).1
    rcases (hAux T hTA).2 with ⟨h,-⟩ | h | h <;> omega
  have hd2 : Disjoint (L∪Aux) X:=by
    rw [disjoint_left];intro M hM hMX;obtain ⟨-,-,hnL,hn4,hn5,hno⟩:=hX M hMX
    rcases mem_union.mp hM with h | h
    · exact hnL h
    · rcases (hAux M h).2 with ⟨h2,T,hT,hs⟩ | h4 | h5
      · exact hno h2 T hT hs
      · exact hn4 h4
      · exact hn5 h5
  have hle:=z3n hS P ((L∪Aux)∪X) (by
    intro M hM
    rcases mem_union.mp hM with h | h
    · rcases mem_union.mp h with h | h
      · exact ⟨by have:=(h3 M h).1;omega,(h3 M h).2⟩
      · refine ⟨?_,(hAux M h).1⟩
        rcases (hAux M h).2 with ⟨h,-⟩ | h | h <;> omega
    · exact ⟨(hX M h).2.1,(hX M h).1⟩)
  rw [card_union_of_disjoint hd2,card_union_of_disjoint hd1] at hle;omega
theorem z3z {G : Fin n→ Fin n→ Prop} {Good : Fin n→ Prop} (hG : zc G Good) (hS : za n D)
    (hC : z3 n G D) {P U X : Finset (Fin n)} (hUP : U⊆P)
    (hU : U.card≤ 2∨(U.card = 3∧¬ qq n D P U))
    (hX : ∀ a∈X,∀ b∈X,¬ G a b) (hPX : P \ U⊆X) {f : Fin n} (hf : f∈U)
    (hnb : ∃ a∈X,G f a) : ∃ e,xh n D P U f e:=by
  obtain ⟨j,s,hj,ht,h1,h2,hd⟩:=x7 hG hS hC X hX f hnb;have hsub : supp n D (src D (j,s))∩P⊆U:=by
    intro v hv;rw [mem_inter] at hv
    by_contra hvU
    exact disjoint_left.mp hd hv.1 (hPX (mem_sdiff.mpr ⟨hv.2,hvU⟩))
  refine ⟨(j,s),hj,ht,hUP hf,h1,h2,hsub,?_⟩
  rcases hU with hU | ⟨hU3,hmiss⟩
  · exact (card_le_card hsub).trans hU
  · have hne : supp n D (src D (j,s))∩P≠U:=fun h=>hmiss ⟨_,h⟩
    have:=card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,hne⟩)
    omega
theorem z02 (hS : za n D) {P U : Finset (Fin n)} {f : Fin n} {e : ℕ×Bool}
    (h : xh n D P U f e) :
    supp n D (n + e.1)∩P⊆(supp n D (src D e)∩P).erase f:=by
  obtain ⟨hj,ht,-,-,h2,-,-⟩:=h;intro v hv;rw [mem_inter] at hv;rw [mem_erase,mem_inter];exact ⟨fun hvf=>h2 (hvf▸hv.1),qg hS hj ht e.2 hv.1,hv.2⟩
theorem z3y {P U : Finset (Fin n)} {f : Fin n} {e : ℕ×Bool}
    (h : xh n D P U f e)
    (hno : ∀ M,M⊆U→ M.card = 2→ f∈M→ ¬ qq n D P M) :
    supp n D (src D e)∩P = {f}:=by
  obtain ⟨-,-,hfP,h1,-,hsub,hc⟩:=h;have hfm : f∈supp n D (src D e)∩P:=mem_inter.mpr ⟨h1,hfP⟩;have hc2 : (supp n D (src D e)∩P).card≠2:=
    fun h2=>hno _ hsub h2 hfm (z0z P _)
  exact (Finset.eq_of_subset_of_card_le (singleton_subset_iff.mpr hfm)
    (by rw [card_singleton];omega)).symm
theorem z10 {P : Finset (Fin n)} {e e0 : ℕ×Bool}
    (h : qx n D P e = Sum.inl e0) : e = e0∧supp n D (n + e.1)∩P = ∅:=by
  unfold qx at h
  split_ifs at h with h0
  exact ⟨Sum.inl.inj h,h0⟩
theorem z2r {P : Finset (Fin n)} {e : ℕ×Bool} {j : ℕ}
    (h : qx n D P e = Sum.inr j) : e.1 = j∧(supp n D (n + e.1)∩P).Nonempty:=by
  unfold qx at h
  split_ifs at h with h0
  exact ⟨Sum.inr.inj h,nonempty_iff_ne_empty.mpr h0⟩
theorem z5b (hS : za n D) {P U : Finset (Fin n)} {f : Fin n} {e : ℕ×Bool}
    (h : xh n D P U f e) : z42 n D P (qx n D P e):=by
  have hout:=z02 hS h;obtain ⟨hj,ht,hfP,h1,-,-,hc⟩:=h;have hfm : f∈supp n D (src D e)∩P:=mem_inter.mpr ⟨h1,hfP⟩;unfold qx
  split_ifs with h0
  · show e∈zk n D (zb n D P)∧(supp n D (src D e)∩P).card≤ 2
    refine ⟨?_,hc⟩
    rw [zk,mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj,mem_univ _⟩,
      y9.mpr ⟨f,hfm⟩,?_⟩
    rw [y9,h0];exact not_nonempty_empty
  · show e.1∈merges n D (zb n D P)∧(supp n D (n + e.1)∩P).card = 1
    have hne : (supp n D (n + e.1)∩P).Nonempty:=nonempty_iff_ne_empty.mpr h0;have hle:=card_le_card hout;rw [Finset.card_erase_of_mem hfm] at hle;have hpos:=card_pos.mpr hne
    refine ⟨?_,by omega⟩
    obtain ⟨v,hv⟩:=hne;rw [mem_inter] at hv;have hA:=qg hS hj ht false hv.1;have hB:=qg hS hj ht true hv.1;rw [qw] at hA;rw [y5] at hB;rw [merges,mem_filter,Finset.mem_range];exact ⟨hj,y9.mpr ⟨v,mem_inter.mpr hv⟩,
      y9.mpr ⟨v,mem_inter.mpr ⟨hA,hv.2⟩⟩,
      y9.mpr ⟨v,mem_inter.mpr ⟨hB,hv.2⟩⟩⟩
theorem z33 (hS : za n D) {P U U' : Finset (Fin n)} {f f' : Fin n}
    {e : ℕ×Bool} (h : xh n D P U f e) (h' : xh n D P U' f' e)
    (hne : (supp n D (n + e.1)∩P).Nonempty) : f = f':=by
  by_contra hff
  obtain ⟨q,hq⟩:=hne;have h1:=z02 hS h hq;have h2:=z02 hS h' hq;rw [mem_erase] at h1 h2;have hsub : ({q,f,f'} : Finset (Fin n))⊆supp n D (src D e)∩P:=by
    intro x hx;simp only [mem_insert,mem_singleton] at hx
    rcases hx with hx | hx | hx <;> rw [hx]
    · exact h1.2
    · exact mem_inter.mpr ⟨h.2.2.2.1,h.2.2.1⟩
    · exact mem_inter.mpr ⟨h'.2.2.2.1,h'.2.2.1⟩
  have hc:=card_le_card hsub;have h3 : ({q,f,f'} : Finset (Fin n)).card = 3:=by
    rw [Finset.card_insert_of_notMem,Finset.card_pair hff];simp only [mem_insert,mem_singleton,not_or];exact ⟨h1.1,h2.1⟩
  have:=h.2.2.2.2.2.2
  omega
theorem v6 (hS : za n D) {P U U' : Finset (Fin n)} {f f' : Fin n}
    {e e' : ℕ×Bool} (h : xh n D P U f e) (h' : xh n D P U' f' e')
    (hs : supp n D (src D e)∩P = {f}) (hff : f≠f') :
    qx n D P e≠qx n D P e':=by
  intro heq;have h0 : supp n D (n + e.1)∩P = ∅:=by
    have hout:=z02 hS h;rw [hs,Finset.erase_singleton] at hout;exact Finset.subset_empty.mp hout
  have hc : qx n D P e = Sum.inl e:=by simp [qx,h0]
  rw [hc] at heq;have he:=(z10 heq.symm).1;subst he;have hm : f'∈supp n D (src D e')∩P:=mem_inter.mpr ⟨h'.2.2.2.1,h'.2.2.1⟩;rw [hs,mem_singleton] at hm;exact hff hm.symm
theorem z53 (hS : za n D) {P : Finset (Fin n)} (Lab : Finset (Fin n))
    (U : Fin n→ Finset (Fin n)) (wit : Fin n→ ℕ×Bool)
    (hwit : ∀ f∈Lab,xh n D P (U f) f (wit f)) (c : (ℕ×Bool) ⊕ ℕ) :
    (Lab.filter (fun f=>qx n D P (wit f) = c)).card≤ 2:=by
  rcases c with e0 | j0
  · by_cases hne : (Lab.filter (fun f=>qx n D P (wit f) = Sum.inl e0)).Nonempty
    · obtain ⟨f0,hf0⟩:=hne
      rw [mem_filter] at hf0;have hcard:=(hwit f0 hf0.1).2.2.2.2.2.2;rw [(z10 hf0.2).1] at hcard
      refine le_trans (card_le_card ?_) hcard
      intro f hf;rw [mem_filter] at hf;have hw:=hwit f hf.1;rw [(z10 hf.2).1] at hw;exact mem_inter.mpr ⟨hw.2.2.2.1,hw.2.2.1⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      simp
  · have hinj : Set.InjOn (fun f=>(wit f).2)
        (Lab.filter (fun f=>qx n D P (wit f) = Sum.inr j0) : Set (Fin n)):=by
      intro f hf f' hf' hs;rw [Finset.mem_coe,mem_filter] at hf hf';obtain ⟨h1,hn1⟩:=z2r hf.2;obtain ⟨h1',-⟩:=z2r hf'.2;have hee : wit f = wit f':=Prod.ext (h1.trans h1'.symm) hs;have hw':=hwit f' hf'.1;rw [← hee] at hw';exact z33 hS (hwit f hf.1) hw' hn1
    have hle:=Finset.card_le_card_of_injOn (t:=(Finset.univ : Finset Bool))
      (fun f=>(wit f).2) (fun _ _=>mem_univ _) hinj
    simpa using hle
theorem z51 (hS : za n D) {P : Finset (Fin n)} (Lab : Finset (Fin n))
    (U : Fin n→ Finset (Fin n)) (wit : Fin n→ ℕ×Bool)
    (hwit : ∀ f∈Lab,xh n D P (U f) f (wit f)) :
    Lab.card≤ 2 * (Lab.image (fun f=>qx n D P (wit f))).card:=
  Finset.card_le_mul_card_image Lab 2 (fun c _=>z53 hS Lab U wit hwit c)
theorem z25 (hS : za n D) {P : Finset (Fin n)} (Lab S : Finset (Fin n))
    (U : Fin n→ Finset (Fin n)) (wit : Fin n→ ℕ×Bool)
    (hwit : ∀ f∈Lab,xh n D P (U f) f (wit f)) (hSL : S⊆Lab)
    (hsing : ∀ f∈S,supp n D (src D (wit f))∩P = {f}) :
    2 * S.card + (Lab \ S).card≤
      2 * (Lab.image (fun f=>qx n D P (wit f))).card:=by
  have h1 : (S.image (fun f=>qx n D P (wit f))).card = S.card:=
    card_image_of_injOn (fun f hf f' hf' heq=>by
      by_contra hne
      exact v6 hS (hwit f (hSL hf)) (hwit f' (hSL hf')) (hsing f hf) hne heq)
  have h2:=z51 hS (Lab \ S) U wit (fun f hf=>hwit f (mem_sdiff.mp hf).1);have hd : Disjoint (S.image (fun f=>qx n D P (wit f)))
      ((Lab \ S).image (fun f=>qx n D P (wit f))):=by
    rw [disjoint_left];intro c hc1 hc2;obtain ⟨f,hf,rfl⟩:=mem_image.mp hc1;obtain ⟨f',hf',heq⟩:=mem_image.mp hc2;rw [mem_sdiff] at hf';exact v6 hS (hwit f (hSL hf)) (hwit f' hf'.1) (hsing f hf)
      (fun h=>hf'.2 (h▸hf)) heq.symm
  have h3 : (S.image (fun f=>qx n D P (wit f))∪
      (Lab \ S).image (fun f=>qx n D P (wit f))).card≤
      (Lab.image (fun f=>qx n D P (wit f))).card:=
    card_le_card (union_subset (Finset.image_subset_image hSL)
      (Finset.image_subset_image sdiff_subset))
  rw [card_union_of_disjoint hd,h1] at h3;omega
theorem z5s (P : Finset (Fin n)) (E : Finset (ℕ×Bool))
    (hE : ∀ e∈E,e∈zk n D (zb n D P)∧3≤ (supp n D (src D e)∩P).card)
    (C : Finset ((ℕ×Bool) ⊕ ℕ)) (hC : ∀ c∈C,z42 n D P c) :
    (z11 n D P).card + E.card + C.card≤
      (zk n D (zb n D P)).card + (merges n D (zb n D P)).card:=by
  have hl : ∀ e∈C.toLeft,e∈zk n D (zb n D P)∧
      (supp n D (src D e)∩P).card≤ 2:=fun e he=>hC _ (Finset.mem_toLeft.mp he)
  have hr : ∀ j∈C.toRight,j∈merges n D (zb n D P)∧
      (supp n D (n + j)∩P).card = 1:=fun j hj=>hC _ (Finset.mem_toRight.mp hj)
  have h1 : E.card + C.toLeft.card≤ (zk n D (zb n D P)).card:=by
    rw [← card_union_of_disjoint]
    · refine card_le_card (fun e he=>?_)
      rcases mem_union.mp he with h | h
      · exact (hE e h).1
      · exact (hl e h).1
    · rw [disjoint_left]
      intro e h1 h2;have a:=(hE e h1).2;have b:=(hl e h2).2;omega
  have h2 : (z11 n D P).card + C.toRight.card≤ (merges n D (zb n D P)).card:=by
    rw [← card_union_of_disjoint]
    · refine card_le_card (fun j hj=>?_)
      rcases mem_union.mp hj with h | h
      · exact (mem_filter.mp h).1
      · exact (hr j h).1
    · rw [disjoint_left]
      intro j h1 h2;have a:=(mem_filter.mp h1).2;have b:=(hr j h2).2;omega
  have h3:=Finset.card_toLeft_add_card_toRight (u:=C);omega
theorem z64 (hS : za n D) (P : Finset (Fin n)) (E : Finset (ℕ×Bool))
    (hE : ∀ e∈E,e∈zk n D (zb n D P)∧3≤ (supp n D (src D e)∩P).card)
    (Lab S : Finset (Fin n)) (U : Fin n→ Finset (Fin n)) (wit : Fin n→ ℕ×Bool)
    (hwit : ∀ f∈Lab,xh n D P (U f) f (wit f)) (hSL : S⊆Lab)
    (hsing : ∀ f∈S,supp n D (src D (wit f))∩P = {f}) :
    2 * ((z11 n D P).card + E.card) + 2 * S.card + (Lab \ S).card≤
      2 * ((zk n D (zb n D P)).card + (merges n D (zb n D P)).card):=by
  have h1:=z25 hS Lab S U wit hwit hSL hsing;have h2:=z5s P E hE (Lab.image (fun f=>qx n D P (wit f))) (by
    intro c hc;obtain ⟨f,hf,rfl⟩:=mem_image.mp hc;exact z5b hS (hwit f hf))
  omega
theorem z2f {G : Fin n→ Fin n→ Prop} {Good : Fin n→ Prop} (hG : zc G Good) (h : z0 n D)
    (hC : z3 n G D) (P I : Finset (Fin n))
    (hI : ∀ i∈I,i∈z1 n D∧Good i∧
      ∃ N : Finset (Fin n),N⊆P∧3≤ N.card∧∀ a∈N,G i a) :
    ∃ E : Finset (ℕ×Bool),E.card = I.card∧∀ e∈E,
      e∈zk n D (zb n D P)∧3≤ (supp n D (src D e)∩P).card:=by
  classical
  have hex : ∀ i : Fin n,∃ e : ℕ×Bool,i∈I→ e.1 < D.length∧
      supp n D (src D e) = {i}∧supp n D (n + e.1) = ∅∧
      ∀ a,G i a→ a∈supp n D (src D (e.1,!e.2)):=by
    intro i
    by_cases hi : i∈I
    · obtain ⟨e,h1,-,h3,h4,h5,-,-⟩:=ql hG h hC (hI i hi).2.1 (hI i hi).1
      exact ⟨e,fun _=>⟨h1,h3,h4,h5⟩⟩
    · exact ⟨(0,false),fun hc=>absurd hc hi⟩
  choose g hg using hex
  refine ⟨I.image (fun i=>((g i).1,!(g i).2)),?_,?_⟩
  · refine card_image_of_injOn (fun i hi i' hi' heq=>?_)
    rw [Prod.mk.injEq,Bool.not_inj_iff] at heq;have he : g i = g i':=Prod.ext heq.1 heq.2;have h1:=(hg i hi).2.1;rw [he,(hg i' hi').2.1] at h1;exact (singleton_injective h1).symm
  · intro e he
    obtain ⟨i,hi,rfl⟩:=mem_image.mp he;obtain ⟨hj,-,hout,hnb⟩:=hg i hi;obtain ⟨N,hNP,hN3,hNG⟩:=(hI i hi).2.2;have hsub : N⊆supp n D (src D ((g i).1,!(g i).2))∩P:=
      fun a ha=>mem_inter.mpr ⟨hnb a (hNG a ha),hNP ha⟩
    have hc:=card_le_card hsub
    refine ⟨?_,by omega⟩
    rw [zk,mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj,mem_univ _⟩,
      y9.mpr (card_pos.mp (by omega)),?_⟩
    rw [y9,hout,empty_inter];exact not_nonempty_empty
end SupMask
section K4Generic
variable {n : ℕ} {G : Fin n→ Fin n→ Prop} {Good : Fin n→ Prop} {D : Dag}
theorem z4e {T : Finset (Fin n)} {w : ℕ} :
    w∈zb n D T↔(supp n D w∩T).Nonempty:=by
  simp only [zb,mem_filter,Finset.mem_range,and_iff_right_iff_imp]
  rintro ⟨v,hv⟩
  exact yf (mem_inter.mp hv).1
theorem z1y {T : Finset (Fin n)} {e : ℕ×Bool} : e∈zk n D (zb n D T)↔
    e.1 < D.length∧(supp n D (src D e)∩T).Nonempty∧
      ¬ (supp n D (n + e.1)∩T).Nonempty:=by
  simp only [zk,arcs,mem_filter,Finset.mem_product,Finset.mem_range,
    mem_univ,and_true,z4e]
def z3u (n : ℕ) (G : Fin n→ Fin n→ Prop) (Good : Fin n→ Prop) (D : Dag) (pos : Fin n→ ℕ×Bool) : Prop:=
  (∀ i∈z1 n D,Good i→ (pos i).1 < D.length∧supp n D (n + (pos i).1) = ∅∧
    (∀ a,G i a→ a∈supp n D (src D (pos i)))∧
    supp n D (src D ((pos i).1,!(pos i).2)) = {i})∧
  ∀ i∈z1 n D,Good i→ ∀ i'∈z1 n D,Good i'→ pos i = pos i'→ i = i'
theorem z3j (hG : zc G Good) (h : z0 n D) (hC : z3 n G D) :
    ∃ pos : Fin n→ ℕ×Bool,z3u n G Good D pos:=by
  classical
  have hex : ∀ i : Fin n,∃ e : ℕ×Bool,i∈z1 n D→ Good i→ (e.1 < D.length∧
      supp n D (n + e.1) = ∅∧(∀ a,G i a→ a∈supp n D (src D e))∧
      supp n D (src D (e.1,!e.2)) = {i}):=by
    intro i
    by_cases hi : i∈z1 n D∧Good i
    · obtain ⟨e,h1,-,h3,h4,h5,-,-⟩:=ql hG h hC hi.2 hi.1
      exact ⟨(e.1,!e.2),fun _ _=>⟨h1,h4,h5,by simpa using h3⟩⟩
    · exact ⟨(0,false),fun h1 h2=>absurd ⟨h1,h2⟩ hi⟩
  choose pos hpos using hex
  refine ⟨pos,hpos,fun i hi hiG i' hi' hi'G he=>?_⟩
  have h1:=(hpos i hi hiG).2.2.2;rw [he,(hpos i' hi' hi'G).2.2.2] at h1;exact (singleton_injective h1).symm
theorem z3i {pos : Fin n→ ℕ×Bool} (hpos : z3u n G Good D pos) {i a : Fin n}
    {T : Finset (Fin n)} (hi : i∈z1 n D) (hiG : Good i) (hia : G i a) (haT : a∈T) :
    pos i∈zk n D (zb n D T):=by
  obtain ⟨h1,h2,h3,-⟩:=hpos.1 i hi hiG;rw [z1y]
  refine ⟨h1,⟨a,mem_inter.mpr ⟨h3 a hia,haT⟩⟩,?_⟩
  rw [h2,empty_inter];exact not_nonempty_empty
theorem z5m {pos : Fin n→ ℕ×Bool} (hpos : z3u n G Good D pos) (T J : Finset (Fin n))
    (hJ : ∀ i∈J,i∈z1 n D∧Good i∧∃ a∈T,G i a) :
    J.image pos⊆zk n D (zb n D T)∧(J.image pos).card = J.card:=by
  refine ⟨fun e he=>?_,card_image_of_injOn (fun i hi i' hi' h=>
    hpos.2 i (hJ i hi).1 (hJ i hi).2.1 i' (hJ i' hi').1 (hJ i' hi').2.1 h)⟩
  obtain ⟨i,hi,rfl⟩:=mem_image.mp he;obtain ⟨a,haT,hia⟩:=(hJ i hi).2.2;exact z3i hpos (hJ i hi).1 (hJ i hi).2.1 hia haT
theorem vn (hS : za n D) (T : Finset (Fin n)) (w : ℕ)
    (h2 : 2≤ (supp n D w∩T).card) :
    ∃ j∈merges n D (zb n D T),supp n D (n + j)∩T = supp n D w∩T:=by
  obtain ⟨j,-,-,h3,h4,-,-⟩:=wt hS T _ h2 w rfl;exact ⟨j,h4,h3⟩
theorem z4d (hS : za n D) {T : Finset (Fin n)} (hT : T.card = 3)
    {a b c : Fin n} (ha : a∈T) (hb : b∈T) (hc : c∈T) (hab : a≠b) (hac : a≠c)
    (hbc : b≠c) {w1 w2 : ℕ} (h1a : a∈supp n D w1) (h1b : b∈supp n D w1)
    (h2a : a∈supp n D w2) (h2c : c∈supp n D w2) :
    2≤ (merges n D (zb n D T)).card:=by
  have m1a : a∈supp n D w1∩T:=mem_inter.mpr ⟨h1a,ha⟩;have m1b : b∈supp n D w1∩T:=mem_inter.mpr ⟨h1b,hb⟩;have m2a : a∈supp n D w2∩T:=mem_inter.mpr ⟨h2a,ha⟩;have m2c : c∈supp n D w2∩T:=mem_inter.mpr ⟨h2c,hc⟩;have c1 : 2≤ (supp n D w1∩T).card:=one_lt_card.mpr ⟨a,m1a,b,m1b,hab⟩
  have c2 : 2≤ (supp n D w2∩T).card:=one_lt_card.mpr ⟨a,m2a,c,m2c,hac⟩;obtain ⟨j1,hj1,e1⟩:=vn hS T w1 c1
  by_cases heq : supp n D w1∩T = supp n D w2∩T
  · have hfull : supp n D w1∩T = T:=by
      refine Finset.eq_of_subset_of_card_le inter_subset_right ?_
      rw [hT];exact two_lt_card.mpr
        ⟨a,m1a,b,m1b,c,by rw [heq];exact m2c,hab,hac,hbc⟩
    obtain ⟨j,-,-,h3,h4,-,hcase⟩:=wt hS T T (by omega) w1 hfull
    rcases hcase with ⟨-,hA,-⟩ | ⟨-,hA,hB,hU,-,-⟩
    · exact absurd rfl (Finset.ssubset_of_ssubset_of_subset hA inter_subset_right).ne
    · have hcard : 3≤ (supp n D (opA D j)∩T).card + (supp n D (opB D j)∩T).card:=by
        have:=Finset.card_union_le (supp n D (opA D j)∩T) (supp n D (opB D j)∩T)
        rw [hU,hT] at this;exact this
      have key : ∀ w,supp n D w∩T ⊂ T→ 2≤ (supp n D w∩T).card→
          2≤ (merges n D (zb n D T)).card:=by
        intro w hss hc2;obtain ⟨j',hj',e'⟩:=vn hS T w hc2
        refine one_lt_card.mpr ⟨j,h4,j',hj',fun hjj=>?_⟩
        rw [hjj,e'] at h3;exact hss.ne h3
      by_cases hc2 : 2≤ (supp n D (opA D j)∩T).card
      · exact key _ hA hc2
      · exact key _ hB (by omega)
  · obtain ⟨j2,hj2,e2⟩:=vn hS T w2 c2
    exact one_lt_card.mpr ⟨j1,hj1,j2,hj2,fun hjj=>heq (by rw [← e1,← e2,hjj])⟩
end K4Generic
section L3Gen
variable {n : ℕ} {G : Fin n→ Fin n→ Prop} {Good : Fin n→ Prop} {D : Dag}
theorem z6l (hS : za n D) {P : Finset (Fin n)} (hP : P.card≤ 7)
    (L : Finset (Finset (Fin n))) (h3 : ∀ T∈L,T.card = 3∧qq n D P T)
    (hint : ∀ T∈L,∀ T'∈L,T≠T'→ (T∩T').card≤ 1) (E : Finset (ℕ×Bool))
    (hE : ∀ e∈E,e∈zk n D (zb n D P)∧3≤ (supp n D (src D e)∩P).card)
    (Lab : Finset (Fin n)) (U : Fin n→ Finset (Fin n))
    (hw : ∀ f∈Lab,∃ e,xh n D P (U f) f e)
    (hUL : ∀ f∈Lab,∀ T∈L,(U f∩T).card≤ 1) :
    2 * L.card + E.card + Lab.card≤
      (zk n D (zb n D P)).card + (merges n D (zb n D P)).card:=by
  classical
  choose! wit hwit using hw
  let S:=Lab.filter (fun f=>∀ M,M⊆U f→ M.card = 2→ f∈M→ ¬ qq n D P M)
  have hSL : S⊆Lab:=filter_subset _ _;have hno : ∀ f∈Lab \ S,∃ M,M⊆U f∧M.card = 2∧f∈M∧qq n D P M:=by
    intro f hf;rw [mem_sdiff,mem_filter] at hf
    by_contra hc
    exact hf.2 ⟨hf.1,fun M h1 h2 h4 h5=>hc ⟨M,h1,h2,h4,h5⟩⟩
  choose! pr hpr using hno
  have hX:=z40 hS hP L h3 hint ((Lab \ S).image pr) (by
    intro M hM;obtain ⟨f,hf,rfl⟩:=mem_image.1 hM;obtain ⟨h1,h2,-,h4⟩:=hpr f hf
    refine ⟨h4,by omega,fun hL=>by have:=(h3 _ hL).1;omega,by omega,by omega,
      fun _ T hT hsub=>?_⟩
    have:=card_le_card (Finset.subset_inter h1 hsub)
    have:=hUL f (mem_sdiff.1 hf).1 T hT
    omega)
  have hcnt:=z64 hS P E hE Lab S U wit hwit hSL (fun f hf=>
    z3y (hwit f (hSL hf)) (mem_filter.1 hf).2)
  have hfib : (Lab \ S).card≤ 2 * ((Lab \ S).image pr).card:=by
    refine Finset.card_le_mul_card_image _ 2 (fun M _=>?_)
    by_cases hne : ((Lab \ S).filter (fun f=>pr f = M)).Nonempty
    · obtain ⟨g,hg⟩:=hne
      rw [mem_filter] at hg;have hM2 : M.card = 2:=hg.2▸(hpr g hg.1).2.1;rw [← hM2]
      refine card_le_card (fun f hf=>?_)
      rw [mem_filter] at hf;exact hf.2▸(hpr f hf.1).2.2.1
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne];simp
  have:=Finset.card_sdiff_add_card_eq_card hSL
  omega
theorem z63 (hG : zc G Good) (hS : za n D) (hC : z3 n G D)
    {pos : Fin n→ ℕ×Bool} (hpos : z3u n G Good D pos) (T J : Finset (Fin n))
    (A : Fin n→ Finset (Fin n))
    (hJ : ∀ i∈J,i∈z1 n D∧Good i∧(∃ a∈T,G i a)∧∀ f∈T,∃ a∈A f,G i a)
    (hA : ∀ f∈T,(∀ a∈A f,∀ b∈A f,¬ G a b)∧T.erase f⊆A f∧∃ a∈A f,G f a) :
    J.card + T.card≤ (zk n D (zb n D T)).card:=by
  classical
  obtain ⟨hsub,hcard⟩:=z5m hpos T J (fun i hi=>⟨(hJ i hi).1,(hJ i hi).2.1,(hJ i hi).2.2.1⟩);have hex : ∀ f∈T,∃ e : ℕ×Bool,e.1 < D.length∧tag D e.1 = true∧
      f∈supp n D (src D e)∧f∉supp n D (n + e.1)∧Disjoint (supp n D (src D e)) (A f):=by
    intro f hf;obtain ⟨j,s,h1,h2,h4,h5,h6⟩:=x7 hG hS hC (A f) (hA f hf).1 f (hA f hf).2.2;exact ⟨(j,s),h1,h2,h4,h5,h6⟩
  choose! w hw using hex
  have hinj : Set.InjOn w T:=by
    intro f hf g hg hfg
    by_contra hne
    exact disjoint_left.1 (hw f hf).2.2.2.2 (hfg▸(hw g hg).2.2.1)
      ((hA f hf).2.1 (mem_erase.2 ⟨fun h=>hne h.symm,hg⟩))
  have hdis : Disjoint (J.image pos) (T.image w):=by
    rw [disjoint_left];intro e he1 he2;obtain ⟨i,hi,rfl⟩:=mem_image.1 he1;obtain ⟨f,hf,hfe⟩:=mem_image.1 he2;obtain ⟨a,ha,hia⟩:=(hJ i hi).2.2.2 f hf;exact disjoint_left.1 (hw f hf).2.2.2.2
      (hfe▸(hpos.1 i (hJ i hi).1 (hJ i hi).2.1).2.2.1 a hia) ha
  have hsub2 : T.image w⊆zk n D (zb n D T):=by
    intro e he;obtain ⟨f,hf,rfl⟩:=mem_image.1 he;obtain ⟨h1,h2,h4,h5,h6⟩:=hw f hf
    refine z1y.2 ⟨h1,⟨f,mem_inter.2 ⟨h4,hf⟩⟩,?_⟩
    rintro ⟨g,hg⟩
    rw [mem_inter] at hg;have hgs : g∈supp n D (src D (w f)):=qg hS h1 h2 (w f).2 hg.1;exact disjoint_left.1 h6 hgs
      ((hA f hf).2.1 (mem_erase.2 ⟨fun h=>h5 (h▸hg.1),hg.2⟩))
  have:=card_le_card (union_subset hsub hsub2)
  rw [card_union_of_disjoint hdis,hcard,card_image_of_injOn hinj] at this;exact this
end L3Gen
section L3bGen
variable {n : ℕ} {G : Fin n→ Fin n→ Prop} {Good : Fin n→ Prop} {D : Dag}
theorem z6d (hG : zc G Good) (h : z0 n D) (hC : z3 n G D) (b : Fin n→ ℕ)
    (hb : qe n D b) {x c : Fin n} (hxG : Good x) (hxc : x≠c) (hx : x∈z6 n D)
    (hres : ∀ u∈z5 n D b,x∈supp n D u.1→ c∈supp n D u.1) {w : ℕ}
    (hw : x∈supp n D w∧c∈supp n D w) :
    ∃ e0,∀ e∈yl n D x,e≠e0→ c∈supp n D (src D e):=by
  classical
  obtain ⟨z,hxz,hcz⟩:=hG.2.2.1 x hxG c hxc;obtain ⟨-,-,h2,e1,he1,ht1,-⟩:=z2k hG h hC b hb hxc hx hres hw hxz hcz;have hc1 : ((zk n D (zx n D x c)).erase e1).card = 1:=by
    rw [Finset.card_erase_of_mem he1,h2]
  obtain ⟨e0,he0⟩:=card_eq_one.1 hc1
  refine ⟨e0,fun e he hne=>?_⟩
  by_contra hce
  obtain ⟨h1,h4,h5⟩:=qj.1 he;have hm : e∈(zk n D (zx n D x c)).erase e1:=
    mem_erase.2 ⟨fun heq=>by
      have:=z67 h.1 he
      rw [heq,ht1] at this;exact Bool.false_ne_true this,wr.2 ⟨h1,⟨h4,hce⟩,fun hc=>h5 hc.1⟩⟩
  rw [he0,mem_singleton] at hm;exact hne hm
end L3bGen
section ExtraHelpers
variable {n : ℕ} {G : Fin n→ Fin n→ Prop} {Good : Fin n→ Prop} {D : Dag}
theorem z2x (hG : zc G Good) (hS : za n D) (hC : z3 n G D)
    (pos : Fin n→ ℕ×Bool) (T J Q : Finset (Fin n)) (qsub : Q⊆T)
    (A : Fin n→ Finset (Fin n))
    (hposJ : (∀ i∈J,pos i∈zk n D (zb n D T)∧∀ a,G i a→ a∈supp n D (src D (pos i)))∧
      Set.InjOn pos (J : Set (Fin n)))
    (hJ : ∀ i∈J,∀ f∈Q,∃ a∈A f,G i a)
    (hA : ∀ f∈Q,(∀ a∈A f,∀ b∈A f,¬ G a b)∧T.erase f⊆A f∧∃ a∈A f,G f a) :
    J.card + Q.card≤ (zk n D (zb n D T)).card:=by
  classical
  have hsub : J.image pos⊆zk n D (zb n D T):=by
    intro e he;obtain ⟨i,hi,rfl⟩:=mem_image.1 he;exact (hposJ.1 i hi).1
  have hcard : (J.image pos).card = J.card:=card_image_of_injOn hposJ.2;have hex : ∀ f∈Q,∃ e : ℕ×Bool,e.1 < D.length∧tag D e.1 = true∧
      f∈supp n D (src D e)∧f∉supp n D (n + e.1)∧Disjoint (supp n D (src D e)) (A f):=by
    intro f hf;obtain ⟨j,s,h1,h2,h4,h5,h6⟩:=x7 hG hS hC (A f) (hA f hf).1 f (hA f hf).2.2;exact ⟨(j,s),h1,h2,h4,h5,h6⟩
  choose! w hw using hex
  have hinj : Set.InjOn w Q:=by
    intro f hf g hg hfg
    by_contra hne
    exact disjoint_left.1 (hw f hf).2.2.2.2 (hfg▸(hw g hg).2.2.1)
      ((hA f hf).2.1 (mem_erase.2 ⟨fun h=>hne h.symm,qsub hg⟩))
  have hdis : Disjoint (J.image pos) (Q.image w):=by
    rw [disjoint_left];intro e he1 he2;obtain ⟨i,hi,rfl⟩:=mem_image.1 he1;obtain ⟨f,hf,hfe⟩:=mem_image.1 he2;obtain ⟨a,ha,hia⟩:=hJ i hi f hf;exact disjoint_left.1 (hw f hf).2.2.2.2
      (hfe▸(hposJ.1 i hi).2 a hia) ha
  have hsub2 : Q.image w⊆zk n D (zb n D T):=by
    intro e he;obtain ⟨f,hf,rfl⟩:=mem_image.1 he;obtain ⟨h1,h2,h4,h5,h6⟩:=hw f hf
    refine z1y.2 ⟨h1,⟨f,mem_inter.2 ⟨h4,qsub hf⟩⟩,?_⟩
    rintro ⟨g,hg⟩
    rw [mem_inter] at hg;have hgs : g∈supp n D (src D (w f)):=qg hS h1 h2 (w f).2 hg.1;exact disjoint_left.1 h6 hgs
      ((hA f hf).2.1 (mem_erase.2 ⟨fun h=>h5 (h▸hg.1),hg.2⟩))
  have:=card_le_card (union_subset hsub hsub2)
  rw [card_union_of_disjoint hdis,hcard,card_image_of_injOn hinj] at this;exact this
theorem y6 (hS : za n D) (b : Fin n→ ℕ) (hb : qe n D b)
    {w : ℕ} (hf : 2≤ zd D w) (hc : 2≤ (supp n D w).card) :
    (⟨w,0⟩ : Σ _ : ℕ,ℕ)∈z5 n D b:=by
  simp only [z5,mem_sdiff,wo,mem_filter,mem_units]
  refine ⟨⟨⟨qm.mpr (lt_of_fanout_pos hS (by omega)),by omega⟩,card_pos.mp (by omega)⟩,?_⟩
  intro hmem;obtain ⟨v,hv,heq⟩:=mem_image.mp hmem;have hw : b v = w:=congrArg Sigma.fst heq;have hs:=(hb v hv).2;rw [hw] at hs;rw [hs,card_singleton] at hc;omega
theorem w4 (hS : za n D) (b : Fin n→ ℕ) (hb : qe n D b)
    {w : ℕ} (hf : 2≤ zd D w) (hc : 2≤ (supp n D w).card)
    (T : Finset (Fin n)) (hdis : Disjoint (supp n D w) T) :
    zw D (zb n D T) + (z6 n D).card + 1≤
      (T∩z6 n D).card + zu n D:=by
  have h1:=w6 hS b hb T;have h2:=card_residual hS b hb
  let u0 : Σ _ : ℕ,ℕ:=⟨w,0⟩
  have hu0 : u0∈z5 n D b:=y6 hS b hb hf hc;have hnot : u0∉(z5 n D b).filter (fun u=>(supp n D u.1∩T).Nonempty):=by
    intro hm;obtain ⟨a,ha⟩:=(mem_filter.mp hm).2;rw [mem_inter] at ha;exact disjoint_left.mp hdis ha.1 ha.2
  have hss : (z5 n D b).filter (fun u=>(supp n D u.1∩T).Nonempty) ⊂ z5 n D b:=
    Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset _ _,fun heq=>hnot (heq.symm▸hu0)⟩
  have h3:=card_lt_card hss;omega
theorem vz (hG : zc G Good) (h : z0 n D) (hC : z3 n G D)
    {t : ℕ} (hB0 : qd n D≤ t) (P I : Finset (Fin n))
    (hP : ∀ a∈P,∀ b∈P,¬ G a b)
    (hI : ∀ i∈I,i∈z1 n D∧Good i)
    (hsep : ∀ i∈I,∀ j∈I,i≠j→ ∃ a∈P,G j a∧¬ G i a) :
    ∃ Bad : Finset (Fin n),Bad⊆I∧Bad.card≤ t∧
      ∀ i∈I \ Bad,∀ x∈P,G i x→
        ∃ e∈yl n D x,∀ a∈P,a∈supp n D (src D e)↔G i a:=by
  classical
  let HasEx (i : Fin n) : Prop:=∀ x∈P,G i x→
    ∃ e∈yl n D x,∀ a∈P,a∈supp n D (src D e)↔G i a
  let Bad:=I.filter (fun i=>¬ HasEx i)
  have hBadSub : Bad⊆I:=filter_subset _ _;have from_chain : ∀ {i : Fin n},i∈I→ ∀ {j s},j < D.length→ tag D j = true→
      zn n D i.val (src D (j,!s))→
      (∀ a∈P,a∈supp n D (src D (j,s))↔G i a)→ HasEx i:=by
    intro i hi j s hj ht hch hex x hxP hix
    refine ⟨(j,s),qj.mpr ⟨hj,(hex x hxP).2 hix,?_⟩,hex⟩
    intro hx2;have hp:=ys hG h.1 hC i (hI i hi).2 _ (qk h.1 hch);have eq:=mem_singleton.mp (hp (qg h.1 hj ht (!s) hx2));exact hG.2.1 i (eq▸hix)
  have hreach : ∀ i∈Bad,∃ b,zn n D i.val b∧2≤ zd D b∧supp n D b = ∅:=by
    intro i hi;have hiI : i∈I:=hBadSub hi;have hno : ¬ HasEx i:=(mem_filter.mp hi).2
    rcases v8 hG h hC (hI i hiI).2 (hI i hiI).1 with h1 | h2
    · obtain ⟨j,s,hj,ht,hch,hex⟩:=x1 hG h.1 hC P hP h1
      exact absurd (from_chain hiI hj ht hch hex) hno
    · exact h2
  choose! bw hbw using hreach
  have hinj : Set.InjOn bw (Bad : Set (Fin n)):=by
    intro i hi j hj heq
    by_contra hne
    have hiI : i∈I:=hBadSub hi;have hjI : j∈I:=hBadSub hj;obtain ⟨hch1,-,-⟩:=hbw i hi;obtain ⟨hch2,-,-⟩:=hbw j hj;rw [← heq] at hch2;obtain ⟨k,s,hk,ht,-,hch,hex⟩:=
      z0k hG h.1 hC P hP hch1 (qk h.1 hch2) (hsep i hiI j hjI hne)
    exact (mem_filter.mp hi).2 (from_chain hiI hk ht hch hex)
  have hsubE : Bad.image bw⊆(inner n D).filter (fun w=>¬ (supp n D w).Nonempty):=by
    intro w hw;obtain ⟨i,hi,rfl⟩:=mem_image.mp hw;obtain ⟨-,hf,hemp⟩:=hbw i hi;exact mem_filter.mpr ⟨qm.mpr (lt_of_fanout_pos h.1 (by omega)),by simp [hemp]⟩
  have hle1 : Bad.card≤ ∑ w∈Bad.image bw,(zd D w - 1):=by
    rw [← card_image_of_injOn hinj]
    calc (Bad.image bw).card = ∑ _w∈Bad.image bw,1:=by simp
      _≤ ∑ w∈Bad.image bw,(zd D w - 1):=by
        refine sum_le_sum (fun w hw=>?_)
        obtain ⟨i,hi,rfl⟩:=mem_image.mp hw
        have:=(hbw i hi).2.1
        omega
  have hle2 : ∑ w∈Bad.image bw,(zd D w - 1)≤ qd n D:=by
    unfold qd zw;exact sum_le_sum_of_subset hsubE
  refine ⟨Bad,hBadSub,by omega,fun i hi=>?_⟩
  rw [mem_sdiff] at hi
  by_contra hno
  exact hi.2 (mem_filter.mpr ⟨hi.1,hno⟩)
end ExtraHelpers
end DagTools
namespace Resolution
abbrev Lit:=Nat×Bool
abbrev Clause:=List Lit
def neg (l : Lit) : Lit:=(l.1,!l.2)
def Yes (v : Nat→ Bool) (l : Lit):=v l.1 = l.2
def Holds (v : Nat→ Bool) (c : Clause):=∃ l∈c,Yes v l
theorem yn (v : Nat→ Bool) (l : Lit) : Yes v (neg l)↔¬ Yes v l:=by
  simp only [Yes,neg]
  cases v l.1 <;> cases l.2 <;> decide
def key (l : Lit) : Nat:=2 * l.1 + l.2.toNat
theorem z4q : Function.Injective key:=by
  rintro ⟨n,b⟩ ⟨m,c⟩ eq
  cases b <;> cases c <;> simp [key,Bool.toNat] at eq ⊢ <;> omega
def z0s (a : Nat) (l : Lit):=a ||| (2 ^ key l)
def initial : Clause→ Nat
  | []=>0
  | l :: ls=>z0s (initial ls) (neg l)
theorem z4f (a : Nat) (p x : Lit) :
    (z0s a p).testBit (key x) = true↔a.testBit (key x) = true∨p = x:=by
  simp [z0s,Nat.testBit_two_pow,z4q.eq_iff]
theorem z5p {c : Clause} {x : Lit} (h : (initial c).testBit (key x) = true) :
    ∃ l∈c,neg l = x:=by
  induction c with
  | nil=>simp [initial] at h
  | cons l ls ih=>
    rcases (z4f _ _ _).mp h with h | e
    · obtain ⟨t,ht,eq⟩:=ih h;exact ⟨t,List.mem_cons_of_mem _ ht,eq⟩
    · exact ⟨l,List.mem_cons_self,e⟩
def allowed (a : Nat) (p : Option Lit) (c : Clause) : Bool:=
  c.all fun l=>some l == p || a.testBit (key (neg l))
theorem z2p {v a p c} (sat : Holds v c) (forced : ∀ l,a.testBit (key l) = true→ Yes v l)
    (ok : allowed a p c = true) : ∃ l,some l = p∧Yes v l:=by
  obtain ⟨l,hl,hv⟩:=sat;have bound:=(List.all_eq_true.mp ok) l hl;simp only [Bool.or_eq_true,beq_iff_eq] at bound
  rcases bound with eq | deny
  · exact ⟨l,eq,hv⟩
  · exact ((yn v l).mp (forced _ deny) hv).elim
def digits (width : Nat) : Nat→ Nat→ List Nat
  | 0,_=>[]
  | count + 1,n=>(n % (2 ^ width)) :: digits width count (n >>> width)
def z5r (width len bits : Nat) : Clause:=
  (digits width len bits).map (fun n=>(n / 2,n % 2 == 1))
def z6b (a : Nat) (c : Clause) : Option Lit:=
  c.find? fun l=>!(a.testBit (key (neg l)))
def qf (v : Nat→ Bool) (book : Nat→ Clause) (n : Nat):=
  ∀ i,i < n→ Holds v (book i)
def zf (book : Nat→ Clause) (n last : Nat) : List Nat→ Nat→ Bool
  | [],a=>decide (last < n) && allowed a none (book last)
  | i :: rest,a=>decide (i < n) &&
      match z6b a (book i) with
      | none=>allowed a none (book i)
      | some p=>allowed a (some p) (book i) && zf book n last rest (z0s a p)
theorem z2b {v book n} (sat : qf v book n)
    (last : Nat) (units : List Nat) (a : Nat)
    (forced : ∀ l,a.testBit (key l) = true→ Yes v l)
    (ok : zf book n last units a = true) : False:=by
  induction units generalizing a with
  | nil=>
    simp only [zf,Bool.and_eq_true,decide_eq_true_eq] at ok;obtain ⟨_,e,_⟩:=z2p (sat _ ok.1) forced ok.2
    contradiction
  | cons i us ih=>
    simp only [zf,Bool.and_eq_true,decide_eq_true_eq] at ok;obtain ⟨hi,rest⟩:=ok
    split at rest
    · obtain ⟨_,e,_⟩:=z2p (sat _ hi) forced rest
      contradiction
    · rename_i p _
      rw [Bool.and_eq_true] at rest;obtain ⟨l,e,hv⟩:=z2p (sat _ hi) forced rest.1;have eq:=Option.some.inj e;subst l
      apply ih (z0s a p) _ rest.2
      intro t ht
      rcases (z4f _ _ _).1 ht with old | rfl
      · exact forced t old
      · exact hv
def zo (book : Nat→ Clause) (width : Nat) : Nat→ List Nat→ Bool
  | _,[]=>true
  | i,u :: us=>zf book i ((u >>> 9) % (2 ^ width))
      (digits width (u % 512) (u >>> (9 + width))) (initial (book i)) && zo book width (i + 1) us
theorem z17 {v book width i} (sat : qf v book i) (rows : List Nat)
    (ok : zo book width i rows = true) : qf v book (i + rows.length):=by
  induction rows generalizing i with
  | nil=>simpa using sat
  | cons u us ih=>
    simp only [zo,Bool.and_eq_true] at ok;have holds : Holds v (book i):=by
      by_contra no
      apply z2b sat _ _ _ _ ok.1
      intro x hx;obtain ⟨y,hy,rfl⟩:=z5p hx;exact (yn v y).2 (fun yes=>no ⟨y,hy,yes⟩)
    have step : qf v book (i + 1):=by
      intro j hj
      by_cases lt : j < i
      · exact sat j lt
      · have eq : j = i:=by omega
        exact eq▸holds
    have rest:=ih step ok.2
    simpa [Nat.add_assoc,Nat.add_comm 1 us.length] using rest
theorem z4h {v book n} (sat : qf v book n) (last : Nat) (units : List Nat)
    (ok : zf book n last units 0 = true) : False:=
  z2b sat last units 0 (by simp) ok
def z4c (ts : Array (List Nat)) (i : Nat) : Nat:=
  (ts.getD (i / 16) []).getD (i % 16) 0
end Resolution
namespace Compact
open Finset
open DagTools Resolution
abbrev Slot:=ℕ×Bool
def flip (s : Bool) (e : Slot) : Slot:=if s then z04 e else e
theorem z0t (s : Bool) : Function.Injective (flip s):=by
  intro a b
  cases s with
  | false=>exact id
  | true=>
    intro eq;have h:=congrArg z04 eq
    simpa only [flip,ite_true,z5c] using h
def mask {n : ℕ} (m : Nat) : Finset (Fin n):=Finset.univ.filter (fun v=>m.testBit v.val)
def z4 (neigh : List Nat) {n : ℕ} (u v : Fin n) : Prop:=
  (neigh.getD u.val 0).testBit v.val = true
instance (neigh : List Nat) {n : ℕ} (u v : Fin n) : Decidable (z4 neigh u v):=
  inferInstanceAs (Decidable ((neigh.getD u.val 0).testBit v.val = true))
def x0 (neigh : List Nat) {n : ℕ} (T : Finset (Fin n)) : Prop:=
  ∀ a∈T,∀ b∈T,¬ z4 neigh a b
instance (neigh : List Nat) {n : ℕ} (T : Finset (Fin n)) : Decidable (x0 neigh T):=
  inferInstanceAs (Decidable (∀ a∈T,∀ b∈T,¬ z4 neigh a b))
def zh (n : ℕ) [NeZero n] (edges : List (Nat×Nat)) (s : Bool) (e : Nat) : Fin n:=
  let ab:=edges.getD e (0,0)
  Fin.ofNat n (if s then ab.2 else ab.1)
def z1c {n m : ℕ} [NeZero n] (edges : List (Nat×Nat)) (D : Dag) (P : Fin m→ Slot) : Prop:=
  ∀ s (e : Fin m),flip s (P e)∈yl n D (zh n edges s e.val)
theorem xx {n m : ℕ} [NeZero n] {neigh : List Nat} {edges : List (Nat×Nat)}
    {Good : Fin n→ Prop} {D : Dag}
    (hG : zc (z4 neigh) Good) (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (adjE : ∀ e : Fin m,z4 neigh (zh n edges false e.val) (zh n edges true e.val)) :
    ∃ P : Fin m→ Slot,z1c (n:=n) edges D P:=by
  have both (e : Fin m) : ∃ p : Slot,
      p∈yl n D (zh n edges false e.val)∧
      z04 p∈yl n D (zh n edges true e.val):=by
    obtain ⟨p,hl,hr,_⟩:=z1r hG h.1 hc (adjE e);exact ⟨p,hl,hr⟩
  choose P hp using both
  exact ⟨P,fun s e=>by cases s;exact (hp e).1;exact (hp e).2⟩
def vu (n : Nat) (neigh : List Nat) (M : Nat) : Bool:=
  (List.range n).all fun u=>!M.testBit u || (M &&& neigh.getD u 0) == 0
theorem yu {n : ℕ} {neigh : List Nat} {M : Nat} (h : vu n neigh M = true) :
    x0 neigh (mask M : Finset (Fin n)):=by
  intro u hu v hv huv;simp only [mask,mem_filter,mem_univ,true_and] at hu hv;have h1:=List.all_eq_true.mp h u.val (List.mem_range.mpr u.isLt);simp only [hu,Bool.not_true,Bool.false_or,beq_iff_eq] at h1;have hb:=congrArg (fun z : Nat=>z.testBit v.val) h1;rw [Nat.testBit_and,Nat.zero_testBit,hv,huv] at hb
  exact Bool.false_ne_true hb.symm
def qn (n : ℕ) (D : Dag) (x : Fin n):=(yl n D x).card
def cap {n : ℕ} (k I : Nat) (x : Fin n):=if I.testBit x.val then 1 else 2 + k
def z0u (n : ℕ) (D : Dag) (x c : Fin n):=∃ w,x∈supp n D w∧c∈supp n D w
theorem z4j (n : ℕ) (D : Dag) (x c : Fin n) : z0u n D x c↔z0u n D c x:=by
  simp only [z0u,and_comm]
def x3 (n : ℕ) (D : Dag) (p : Slot) (x : Fin n):=x∈supp n D (src D p)
structure Layout (n m : ℕ) [NeZero n] (edges : List (Nat×Nat)) (D : Dag) (k I w0 : Nat) where
  wire : Fin n→ Nat→ Slot
  edge : Fin m→ Slot
  reader : Bool→ Fin m→ Nat
  branch : Fin n→ Nat
  order : Fin k≃↥(z5 n D branch)
  pure : qe n D branch
  limit : ∀ x,qn n D x≤ cap k I x
  member : ∀ x j,wire x j∈yl n D x
  inject : ∀ x j l,j < qn n D x→ l < qn n D x→ wire x j = wire x l→ j = l
  covers : ∀ x e,e∈yl n D x→ ∃ j < qn n D x,wire x j = e
  reader_live : ∀ s e,reader s e < qn n D (zh n edges s e.val)
  read : ∀ s e,wire (zh n edges s e.val) (reader s e) = flip s (edge e)
  res0_ok : w0≠0→ ∃ h0 : 0 < k,∀ x : Fin n,x∈supp n D (order ⟨0,h0⟩).val.1↔x∈(mask w0 : Finset (Fin n))
theorem z6h {n k w0 : ℕ} {D : Dag} {b : Fin n→ ℕ}
    (hS : za n D) (hb : qe n D b) (hrc : (z5 n D b).card = k)
    (hw0 : w0≠0→ ∃ w : ℕ,2≤ zd D w∧supp n D w = (mask w0 : Finset (Fin n))∧2≤ (supp n D w).card) :
    ∃ f : Fin k≃↥(z5 n D b),
      w0≠0→ ∃ h0 : 0 < k,∀ x : Fin n,x∈supp n D (f ⟨0,h0⟩).val.1↔x∈(mask w0 : Finset (Fin n)):=by
  classical
  have count : Fintype.card ↥(z5 n D b) = k:=by rw [Fintype.card_coe];exact hrc
  by_cases hz : w0 = 0
  · exact ⟨(Fintype.equivFinOfCardEq count).symm,fun hne=>absurd hz hne⟩
  · obtain ⟨w,hfw,hsw,hcw⟩:=hw0 hz
    let u0 : ↥(z5 n D b):=⟨⟨w,0⟩,y6 hS b hb hfw hcw⟩
    have hkpos : 0 < k:=by
      have hpos : 0 < (z5 n D b).card:=card_pos.mpr ⟨u0.val,u0.property⟩;omega
    let f0 : Fin k≃↥(z5 n D b):=(Fintype.equivFinOfCardEq count).symm
    let idx0 : Fin k:=f0.symm u0
    let f : Fin k≃↥(z5 n D b):=(Equiv.swap ⟨0,hkpos⟩ idx0).trans f0
    refine ⟨f,fun _=>⟨hkpos,fun x=>?_⟩⟩
    have hf0 : f ⟨0,hkpos⟩ = u0:=by
      dsimp only [f,Equiv.trans_apply];rw [Equiv.swap_apply_left,Equiv.apply_symm_apply]
    rw [hf0];change x∈supp n D w↔_;rw [hsw]
theorem z6q {n : ℕ} (D : Dag) (x : Fin n) :
    ∃ _ : Fin (qn n D x)≃↥(yl n D x),True:=by
  classical
  exact ⟨(Fintype.equivFinOfCardEq (by simp [qn])).symm,trivial⟩
theorem vb {n m : ℕ} [NeZero n] {neigh : List Nat} {edges : List (Nat×Nat)}
    {Good : Fin n→ Prop} {k I w0 bpVal : Nat} {D : Dag}
    (hG : zc (z4 neigh) Good) (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (adjE : ∀ e : Fin m,z4 neigh (zh n edges false e.val) (zh n edges true e.val))
    (hEl : ∀ v∈z6 n D,Good v)
    (bp : zu n D = bpVal) (eq : (mask I : Finset (Fin n)) = z1 n D)
    (sizeK : k + (n - (mask I : Finset (Fin n)).card) = bpVal)
    (hw0 : w0≠0→ ∃ w : ℕ,2≤ zd D w∧supp n D w = (mask w0 : Finset (Fin n))∧2≤ (supp n D w).card) :
    Nonempty (Layout n m edges D k I w0):=by
  obtain ⟨b,hb⟩:=zz hG h.1 hc hEl;have el:=zm n D;have diff:=card_residual h.1 b hb;rw [← eq] at el;have hel : n - (mask I : Finset (Fin n)).card = (z6 n D).card:=Nat.sub_eq_of_eq_add' el.symm;rw [hel] at sizeK;have hrc : (z5 n D b).card = k:=by omega
  obtain ⟨f,hf0⟩:=z6h h.1 hb hrc hw0;have lim (x : Fin n) : qn n D x≤ cap k I x:=by
    unfold cap qn
    by_cases hx : I.testBit x.val = true
    · rw [if_pos hx]
      have hxm : x∈(mask I : Finset (Fin n)):=by simp [mask,hx]
      obtain ⟨p,_,_,_,_,_,sw,_⟩:=wa hG h hc (eq▸hxm);change yl n D x = {p} at sw;rw [sw,card_singleton]
    · rw [if_neg hx]
      have one:=card_le_card (inter_subset_left : ({x} : Finset (Fin n))∩z6 n D⊆{x});have two:=card_filter_le (z5 n D b) (fun u=>x∈supp n D u.1);have cc:=vx hG h hc b hb x;simp only [card_singleton] at one;omega
  have has (x : Fin n) : 0 < qn n D x:=by
    obtain ⟨y,xy⟩:=hG.2.2.2 x;obtain ⟨p,hp,_⟩:=z1r hG h.1 hc xy;exact card_pos.mpr ⟨p,hp⟩
  let enum (x : Fin n) : Fin (qn n D x)≃↥(yl n D x):=(z6q D x).choose
  let atIdx (x : Fin n) (j : Nat) : Fin (qn n D x):=
    if hj : j < qn n D x then ⟨j,hj⟩ else ⟨0,has x⟩
  let wfn (x : Fin n) (j : Nat):=((enum x) (atIdx x j)).val
  have onto (x : Fin n) (e) (he : e∈yl n D x) : ∃ j < qn n D x,wfn x j = e:=by
    obtain ⟨i,hf⟩:=(enum x).surjective ⟨e,he⟩;exact ⟨i.val,i.isLt,by simpa [wfn,atIdx,i.isLt] using congrArg Subtype.val hf⟩
  obtain ⟨P,hp⟩:=xx (m:=m) hG h hc adjE
  let readAt (s : Bool) (e : Fin m) : Nat:=(onto (zh n edges s e.val) _ (hp s e)).choose
  have spec (s : Bool) (e : Fin m):=(onto (zh n edges s e.val) _ (hp s e)).choose_spec
  refine ⟨⟨wfn,P,readAt,b,f,hb,lim,fun x j=>((enum x) (atIdx x j)).property,?_,onto,
    fun s e=>(spec s e).1,fun s e=>(spec s e).2,hf0⟩⟩
  intro x j l hj hl same;have e:=(enum x).injective (Subtype.ext same)
  simpa [atIdx,hj,hl] using congrArg Fin.val e
inductive Fact (n m : ℕ) where
  | live (x : Fin n) (j : Nat)
  | lab (x : Fin n) (j : Nat) (c : Fin n)
  | res (t : Nat) (x : Fin n)
  | common (x c : Fin n)
  | gate (e f : Fin m)
  | reader (s : Bool) (e : Fin m) (j : Nat)
  | es (s : Bool) (e : Fin m) (c : Fin n)
  | avoid (x : Fin n) (a j : Nat)
  | see (x i : Fin n) (p j : Nat)
  | diff (t : Nat) (x c : Fin n)
  deriving DecidableEq
instance {n m : ℕ} [NeZero n] : Inhabited (Fact n m):=⟨.live (Fin.ofNat n 0) 0⟩
inductive Scheme (n m : ℕ) where
  | self (x : Fin n) (j : Nat)
  | earlier (x : Fin n) (j : Nat)
  | labCommon (x c : Fin n) (j : Nat)
  | someRes (x : Fin n)
  | allRes (x : Fin n) (t : Nat)
  | exposure (x : Fin n) (a : Nat)
  | exactAt (x i : Fin n) (p : Nat)
  | avoidLive (x : Fin n) (a j : Nat)
  | seeLive (x i : Fin n) (p j : Nat)
  | avoidNot (x c : Fin n) (a j : Nat)
  | seeLab (x i c : Fin n) (p j : Nat)
  | diffX (t : Nat) (x c : Fin n)
  | diffC (t : Nat) (x c : Fin n)
  | adjacentCommon (x c i : Fin n)
  | resCommon (x c : Fin n) (t : Nat)
  | residual (x c : Fin n) (j l : Nat)
  | readerAny (s : Bool) (e : Fin m)
  | readerLive (s : Bool) (e : Fin m) (j : Nat)
  | readerLab (s : Bool) (e : Fin m) (j : Nat) (c : Fin n) (forward : Bool)
  | eqLab (s : Bool) (e f : Fin m) (c : Fin n) (forward : Bool)
  | gateEq (s : Bool) (e f : Fin m) (j : Nat)
  | ineligPure (x c : Fin n)
  | fixedRes (x : Fin n) (dir : Bool)
  | exactPair (x i y j : Fin n) (p : Nat)
instance {n m : ℕ} [NeZero n] : Inhabited (Scheme n m):=⟨.self (Fin.ofNat n 0) 0⟩
def rAt {n m : ℕ} [NeZero n] {edges : List (Nat×Nat)} {D : Dag} {k I w0 : Nat}
    (Z : Layout n m edges D k I w0) (s : Nat) (x : Fin n) : Prop:=
  ∃ t : Fin k,t.val = s∧x∈supp n D (Z.order t).val.1
def qb {n m : ℕ} [NeZero n] {neigh : List Nat} {edges : List (Nat×Nat)} {D : Dag} {k I w0 : Nat}
    (Z : Layout n m edges D k I w0) : Fact n m→ Prop
  | .live x j=>j < qn n D x
  | .lab x j c=>x3 n D (Z.wire x j) c
  | .res t x=>rAt Z t x
  | .common x c=>z0u n D x c
  | .gate i j=>Z.edge i = Z.edge j
  | .reader s e j=>Z.reader s e = j
  | .es s e c=>x3 n D (flip s (Z.edge e)) c
  | .avoid x a j=>j < qn n D x∧∀ c∈(mask a : Finset (Fin n)),¬ x3 n D (Z.wire x j) c
  | .see x i p j=>j < qn n D x∧∀ c∈(mask p : Finset (Fin n)),x3 n D (Z.wire x j) c↔z4 neigh i c
  | .diff t x c=>rAt Z t x∧¬ rAt Z t c
abbrev FactClause (n m : ℕ):=List (Fact n m×Bool)
def qh {n m : ℕ} [NeZero n] {neigh : List Nat} {edges : List (Nat×Nat)} {D : Dag} {k I w0 : Nat}
    (Z : Layout n m edges D k I w0) (c : FactClause n m) : Prop:=
  ∃ e∈c,if e.2 then qb (neigh:=neigh) Z e.1 else ¬ qb (neigh:=neigh) Z e.1
def pos {n m : ℕ} (a : Fact n m) : Fact n m×Bool:=(a,true)
def vf {n m : ℕ} (a : Fact n m) : Fact n m×Bool:=(a,false)
def v4 {n m : ℕ} (cnt : Nat) (p : Nat→ Fact n m) : FactClause n m:=
  (List.range cnt).map (fun j=>pos (p j))
def z1a {n m : ℕ} (x c : Fin n) : Fact n m:=.common (min x c) (max x c)
def enabled {n m : ℕ} [NeZero n] (neigh : List Nat) (edges : List (Nat×Nat))
    (goodB : Fin n→ Bool) (c2 : Bool) (bz0 : Bool) (w0 k I : Nat) : Scheme n m→ Bool
  | .allRes _ t=>decide (t < k)
  | .exposure x a=>vu n neigh a && (List.range n).any (fun v=>a.testBit v && (neigh.getD x.val 0).testBit v)
  | .exactAt x i p=>bz0 && vu n neigh p && I.testBit i.val && goodB i && p.testBit x.val && (neigh.getD i.val 0).testBit x.val
  | .avoidNot _ c a _=>a.testBit c.val
  | .seeLab _ _ c p _=>p.testBit c.val
  | .adjacentCommon x c i=>I.testBit i.val && goodB i && (neigh.getD i.val 0).testBit x.val && (neigh.getD i.val 0).testBit c.val
  | .residual x c j l=>(x.val != c.val) && !I.testBit x.val && goodB x && decide (j < l)
  | .gateEq s e f _=>zh n edges s e.val == zh n edges s f.val
  | .ineligPure x c=>I.testBit x.val && (x.val != c.val) &&
      (goodB x || (c2 && (x.val == 0) && (((c.val != 4) && (c.val != 5)) || (I.testBit c.val && goodB c))))
  | .fixedRes x dir=>(w0 != 0) && if dir then w0.testBit x.val else !w0.testBit x.val
  | .exactPair x i y j p=>vu n neigh p &&
      I.testBit i.val && I.testBit j.val && goodB i && goodB j &&
      (i.val != j.val) && p.testBit x.val && p.testBit y.val &&
      (neigh.getD i.val 0).testBit x.val && (neigh.getD j.val 0).testBit y.val &&
      (List.range n).any (fun a=>p.testBit a && (neigh.getD j.val 0).testBit a && !(neigh.getD i.val 0).testBit a)
  | _=>true
def expand {n m : ℕ} [NeZero n] (neigh : List Nat) (edges : List (Nat×Nat)) (k I : Nat) :
    Scheme n m→ FactClause n m
  | .self x j=>[pos (.lab x j x)]
  | .earlier x j=>[vf (.live x (j + 1)),pos (.live x j)]
  | .labCommon x c j=>[vf (.live x j),vf (.lab x j c),pos (z1a x c)]
  | .someRes x=>vf (.live x 2) :: v4 k (fun t=>.res t x)
  | .allRes x t=>[vf (.live x (1 + k)),pos (.res t x)]
  | .exposure x a=>v4 (cap k I x) (fun j=>.avoid x a j)
  | .exactAt x i p=>v4 (cap k I x) (fun j=>.see x i p j)
  | .avoidLive x a j=>[vf (.avoid x a j),pos (.live x j)]
  | .seeLive x i p j=>[vf (.see x i p j),pos (.live x j)]
  | .avoidNot x c a j=>[vf (.avoid x a j),vf (.lab x j c)]
  | .seeLab x i c p j=>if z4 neigh i c then [vf (.see x i p j),pos (.lab x j c)] else [vf (.see x i p j),vf (.lab x j c)]
  | .diffX t x c=>[vf (.diff t x c),pos (.res t x)]
  | .diffC t x c=>[vf (.diff t x c),vf (.res t c)]
  | .adjacentCommon x c _=>[pos (z1a x c)]
  | .resCommon x c t=>[vf (.res t x),vf (.res t c),pos (z1a x c)]
  | .residual x c j l=>vf (z1a x c) :: vf (.live x l) :: pos (.lab x j c) :: pos (.lab x l c) :: v4 k (fun t=>.diff t x c)
  | .readerAny s e=>v4 (cap k I (zh n edges s e.val)) (fun j=>.reader s e j)
  | .readerLive s e j=>[vf (.reader s e j),pos (.live (zh n edges s e.val) j)]
  | .readerLab s e j c dir=>[(Fact.reader s e j,false),(.lab (zh n edges s e.val) j c,!dir),(.es s e c,dir)]
  | .eqLab s e f c dir=>[(Fact.gate e f,false),(.es s e c,!dir),(.es s f c,dir)]
  | .gateEq s e f j=>[vf (.reader s e j),vf (.reader s f j),pos (.gate e f)]
  | .ineligPure x c=>[vf (.lab x 0 c)]
  | .fixedRes x dir=>[(.res 0 x,dir)]
  | .exactPair x i y j p=>v4 (cap k I x) (fun s=>.see x i p s) ++ v4 (cap k I y) (fun s=>.see y j p s)
theorem z62 {n m : ℕ} [NeZero n] {neigh : List Nat} {edges : List (Nat×Nat)} {D : Dag} {k I w0 : Nat}
    (Z : Layout n m edges D k I w0) (a : Fact n m) (b : Bool) (c : FactClause n m) :
    qh (neigh:=neigh) Z ((a,b) :: c)↔(if b then qb (neigh:=neigh) Z a else ¬ qb (neigh:=neigh) Z a)∨qh (neigh:=neigh) Z c:=by
  simp [qh,List.mem_cons,exists_or,or_and_right]
theorem xv {n m : ℕ} [NeZero n] {neigh : List Nat} {edges : List (Nat×Nat)} {D : Dag} {k I w0 : Nat}
    (Z : Layout n m edges D k I w0) (a : Fact n m) (c : FactClause n m) :
    qh (neigh:=neigh) Z (pos a :: c)↔qb (neigh:=neigh) Z a∨qh (neigh:=neigh) Z c:=by
  simp [qh,pos,List.mem_cons,exists_or,or_and_right]
theorem yn {n m : ℕ} [NeZero n] {neigh : List Nat} {edges : List (Nat×Nat)} {D : Dag} {k I w0 : Nat}
    (Z : Layout n m edges D k I w0) (a : Fact n m) (c : FactClause n m) :
    qh (neigh:=neigh) Z (vf a :: c)↔¬ qb (neigh:=neigh) Z a∨qh (neigh:=neigh) Z c:=by
  simp [qh,vf,List.mem_cons,exists_or,or_and_right]
theorem y8 {n m : ℕ} [NeZero n] {neigh : List Nat} {edges : List (Nat×Nat)} {D : Dag} {k I w0 : Nat}
    (Z : Layout n m edges D k I w0) : ¬ qh (neigh:=neigh) Z []:=by simp [qh]
theorem vq {n m : ℕ} [NeZero n] {neigh : List Nat} {edges : List (Nat×Nat)} {D : Dag} {k I w0 : Nat}
    (Z : Layout n m edges D k I w0) (cnt : Nat) (p : Nat→ Fact n m) :
    qh (neigh:=neigh) Z (v4 cnt p)↔∃ j < cnt,qb (neigh:=neigh) Z (p j):=by
  simp [qh,v4,pos]
theorem z60 {n m : ℕ} [NeZero n] {neigh : List Nat} {edges : List (Nat×Nat)} {D : Dag} {k I w0 : Nat}
    (Z : Layout n m edges D k I w0) (c1 c2 : FactClause n m) :
    qh (neigh:=neigh) Z (c1 ++ c2)↔qh (neigh:=neigh) Z c1∨qh (neigh:=neigh) Z c2:=by
  simp [qh,List.mem_append,exists_or,or_and_right]
theorem z0a {n m : ℕ} [NeZero n] {neigh : List Nat} {edges : List (Nat×Nat)} {D : Dag} {k I w0 : Nat}
    (Z : Layout n m edges D k I w0) (x c : Fin n) :
    qb (neigh:=neigh) Z (z1a x c)↔z0u n D x c:=by
  rcases le_total x c with le | le
  · simp [z1a,min_eq_left le,max_eq_right le,qb]
  · simp [z1a,min_eq_right le,max_eq_left le,qb,z4j n D c x]
theorem z4v {n m : ℕ} [NeZero n] {edges : List (Nat×Nat)} {D : Dag} {k I w0 : Nat}
    (Z : Layout n m edges D k I w0) (t : Fin k) (x : Fin n) :
    rAt Z t.val x↔x∈supp n D (Z.order t).val.1:=by
  constructor
  · rintro ⟨s,e,h⟩;exact (Fin.ext e : s = t)▸h
  · exact fun h=>⟨t,rfl,h⟩
set_option maxHeartbeats 400000 in
set_option maxRecDepth 200000 in
theorem z55 {n m : ℕ} [NeZero n] {neigh : List Nat} {edges : List (Nat×Nat)}
    {goodB : Fin n→ Bool} {c2 bz0 : Bool} {w0 k I : Nat} {D : Dag}
    (Z : Layout n m edges D k I w0)
    (hG : zc (z4 neigh) (fun v=>goodB v = true))
    (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (hz1 : qd n D≤ 1) (hz0 : bz0 = true→ qd n D = 0)
    (eq : (mask I : Finset (Fin n)) = z1 n D)
    (hc2 : c2 = true→ ∀ (x : Fin n),x.val = 0→ ∀ w,x∈supp n D w→
      ∀ c : Fin n,c∈supp n D w→ c.val = 0∨c.val = 4∨c.val = 5)
    (q : Scheme n m) (en : enabled neigh edges goodB c2 bz0 w0 k I q = true) :
    qh (neigh:=neigh) Z (expand neigh edges k I q):=by
  classical
  have size_code (x : Fin n) : qn n D x≤ 2 + (Finset.univ.filter (fun t : Fin k=>x∈supp n D (Z.order t).val.1)).card:=by
    have image : (Finset.univ.filter (fun t : Fin k=>x∈supp n D (Z.order t).val.1)).image (fun t=>(Z.order t).val) =
        (z5 n D Z.branch).filter (fun u=>x∈supp n D u.1):=by
      ext u
      constructor
      · intro hu;obtain ⟨t,ht,rfl⟩:=mem_image.mp hu
        exact mem_filter.mpr ⟨(Z.order t).property,(mem_filter.mp ht).2⟩
      · intro hu
        obtain ⟨base,sp⟩:=mem_filter.mp hu;obtain ⟨t,e⟩:=Z.order.surjective ⟨u,base⟩;exact mem_image.mpr ⟨t,mem_filter.mpr ⟨mem_univ _,by simpa [e] using sp⟩,congrArg Subtype.val e⟩
    have cc:=vx hG h hc Z.branch Z.pure x;have one:=card_le_card (inter_subset_left : ({x} : Finset (Fin n))∩z6 n D⊆{x});simp only [card_singleton] at one;rw [← image,card_image_of_injective _ (fun _ _ e=>Z.order.injective (Subtype.ext e))] at cc;unfold qn;omega
  cases q with
  | self x j=>
    simpa only [expand,xv,y8,or_false,qb,x3] using (qj.mp (Z.member x j)).2.1
  | earlier x j=>
    simp only [expand,yn,xv,y8,or_false,qb];omega
  | labCommon x c j=>
    simp only [expand,yn,xv,y8,or_false];rw [z0a];simp only [qb];have hself:=(qj.mp (Z.member x j)).2.1
    by_cases h1 : j < qn n D x
    · by_cases h2 : x3 n D (Z.wire x j) c
      · exact Or.inr (Or.inr ⟨_,hself,h2⟩)
      · exact Or.inr (Or.inl h2)
    · exact Or.inl h1
  | someRes x=>
    simp only [expand,yn,vq,qb]
    by_cases active : 2 < qn n D x
    · have sz:=size_code x
      obtain ⟨t,ht⟩:=card_pos.mp (show 0 < (Finset.univ.filter (fun t : Fin k=>x∈supp n D (Z.order t).val.1)).card by omega)
      exact Or.inr ⟨t.val,t.isLt,(z4v Z t x).2 (mem_filter.mp ht).2⟩
    · exact Or.inl active
  | allRes x t=>
    simp only [enabled,decide_eq_true_eq] at en;simp only [expand,yn,xv,y8,or_false,qb]
    by_cases active : 1 + k < qn n D x
    · have sz:=size_code x
      have hfull : Finset.univ.filter (fun s : Fin k=>x∈supp n D (Z.order s).val.1) = Finset.univ:=
        eq_univ_of_card _ (by
          have hle:=card_le_univ (Finset.univ.filter (fun s : Fin k=>x∈supp n D (Z.order s).val.1));simp at hle ⊢;omega)
      let i : Fin k:=⟨t,en⟩
      have hmem : i∈Finset.univ.filter (fun s : Fin k=>x∈supp n D (Z.order s).val.1):=hfull.symm▸mem_univ i;exact Or.inr ((z4v Z i x).2 (mem_filter.mp hmem).2)
    · exact Or.inl active
  | exposure x a=>
    simp only [enabled,Bool.and_eq_true,List.any_eq_true,List.mem_range] at en
    rcases en with ⟨hind,v,hv,hav,hxv⟩
    obtain ⟨g,s,hl,_,xl,no,dis⟩:=x7 hG h.1 hc (mask a) (yu hind) x ⟨⟨v,hv⟩,by simp [mask,hav],hxv⟩;obtain ⟨j,live,eqw⟩:=Z.covers x (g,s) (qj.mpr ⟨hl,xl,no⟩);exact (vq Z _ _).2 ⟨j,lt_of_lt_of_le live (Z.limit x),live,fun c cin (hh : x3 n D (Z.wire x j) c)=>
      disjoint_left.mp dis (eqw▸hh) cin⟩
  | exactAt x i p=>
    simp only [enabled,Bool.and_eq_true] at en
    rcases en with ⟨⟨⟨⟨⟨hbz,hind⟩,hiI⟩,hiG⟩,hxP⟩,hix⟩
    have hiIm : i∈(mask I : Finset (Fin n)):=by simp [mask,hiI]
    have hxPm : x∈(mask p : Finset (Fin n)):=by simp [mask,hxP]
    obtain ⟨j,s,hj,ht,ch,ex⟩:=x1 hG h.1 hc (mask p) (yu hind)
      (xg hG h hc (hz0 hbz) hiG (eq▸hiIm))
    have heW : (j,s)∈yl n D x:=by
      refine qj.mpr ⟨hj,(ex _ hxPm).2 hix,?_⟩
      intro hx2;have hp:=ys hG h.1 hc i hiG _ (qk h.1 ch);have heq:=mem_singleton.mp (hp (qg h.1 hj ht (!s) hx2));exact hG.2.1 i (heq▸hix)
    obtain ⟨l,live,same⟩:=Z.covers x (j,s) heW;exact (vq Z _ _).2 ⟨l,lt_of_lt_of_le live (Z.limit x),live,fun c inc=>by simpa [x3,same] using ex c inc⟩
  | avoidLive x a j=>
    simp only [expand,yn,xv,y8,or_false,qb]
    by_cases v : j < qn n D x∧∀ c∈(mask a : Finset (Fin n)),¬ x3 n D (Z.wire x j) c
    · exact Or.inr v.1
    · exact Or.inl v
  | seeLive x i p j=>
    simp only [expand,yn,xv,y8,or_false,qb]
    by_cases v : j < qn n D x∧∀ c∈(mask p : Finset (Fin n)),x3 n D (Z.wire x j) c↔z4 neigh i c
    · exact Or.inr v.1
    · exact Or.inl v
  | avoidNot x c a j=>
    simp only [enabled] at en;have hcm : c∈(mask a : Finset (Fin n)):=by simp [mask,en]
    simp only [expand,yn,y8,or_false,qb]
    by_cases v : j < qn n D x∧∀ c'∈(mask a : Finset (Fin n)),¬ x3 n D (Z.wire x j) c'
    · exact Or.inr (v.2 c hcm)
    · exact Or.inl v
  | seeLab x i c p j=>
    simp only [enabled] at en;have hcm : c∈(mask p : Finset (Fin n)):=by simp [mask,en]
    by_cases a : z4 neigh i c <;> simp only [expand,a,ite_true,ite_false,yn,xv,y8,or_false,qb]
    · by_cases v : j < qn n D x∧∀ c'∈(mask p : Finset (Fin n)),x3 n D (Z.wire x j) c'↔z4 neigh i c'
      · exact Or.inr ((v.2 c hcm).2 a)
      · exact Or.inl v
    · by_cases v : j < qn n D x∧∀ c'∈(mask p : Finset (Fin n)),x3 n D (Z.wire x j) c'↔z4 neigh i c'
      · exact Or.inr (fun u=>a ((v.2 c hcm).1 u))
      · exact Or.inl v
  | diffX t x c=>simp only [expand,yn,xv,y8,or_false,qb];tauto
  | diffC t x c=>simp only [expand,yn,y8,or_false,qb];tauto
  | adjacentCommon x c i=>
    simp only [enabled,Bool.and_eq_true] at en
    rcases en with ⟨⟨⟨hiI,hiG⟩,hix⟩,hic⟩
    have hiIm : i∈(mask I : Finset (Fin n)):=by simp [mask,hiI]
    simp only [expand,xv,y8,or_false,z0a];obtain ⟨e,_,_,_,_,hn,_⟩:=ql hG h hc hiG (eq▸hiIm);exact ⟨_,hn x hix,hn c hic⟩
  | resCommon x c t=>
    simp only [expand,yn,xv,y8,or_false];rw [z0a];simp only [qb]
    by_cases rx : rAt Z t x <;> by_cases rc : rAt Z t c
    · obtain ⟨i,eqi,hx⟩:=rx;obtain ⟨j,eqj,hcc⟩:=rc
      have same : i = j:=Fin.ext (eqi.trans eqj.symm);exact Or.inr (Or.inr ⟨_,hx,same▸hcc⟩)
    all_goals tauto
  | residual x c j l=>
    simp only [enabled,Bool.and_eq_true,bne_iff_ne,ne_eq,Bool.not_eq_true',decide_eq_true_eq] at en
    rcases en with ⟨⟨⟨hxc,hnxI⟩,hxG⟩,hjl⟩
    simp only [expand,yn,xv,vq];rw [z0a];simp only [qb]
    by_cases com : z0u n D x c
    · right
      by_cases active : l < qn n D x
      · right
        by_contra! bad
        obtain ⟨mj,ml,rest⟩:=bad;have hj : j < qn n D x:=lt_trans hjl active;have elig : x∈z6 n D:=by
          by_contra no
          have hm : x∈(mask I : Finset (Fin n)):=eq▸qt.mpr no;simp [mask,hnxI] at hm
        have hres : ∀ u∈z5 n D Z.branch,x∈supp n D u.1→ c∈supp n D u.1:=by
          intro u hu xu;obtain ⟨t,ht⟩:=Z.order.surjective ⟨u,hu⟩;have hrt:=rest t.val t.isLt ((z4v Z t x).2 (by simpa [ht] using xu))
          simpa [ht] using (z4v Z t c).1 hrt
        obtain ⟨w,xw,cw⟩:=com;obtain ⟨e0,other⟩:=z6d hG h hc Z.branch Z.pure hxG (fun e=>hxc (congrArg Fin.val e)) elig hres ⟨xw,cw⟩;have hne : Z.wire x j≠Z.wire x l:=fun heq=>(Nat.ne_of_lt hjl) (Z.inject x j l hj active heq)
        by_cases ep : Z.wire x j = e0
        · exact ml (other (Z.wire x l) (Z.member x l) (fun heq=>hne (ep.trans heq.symm)))
        · exact mj (other (Z.wire x j) (Z.member x j) ep)
      · exact Or.inl active
    · exact Or.inl com
  | readerAny s e=>
    exact (vq Z _ _).2 ⟨_,lt_of_lt_of_le (Z.reader_live s e) (Z.limit _),rfl⟩
  | readerLive s e j=>
    simp only [expand,yn,xv,y8,or_false,qb]
    by_cases r : Z.reader s e = j
    · exact Or.inr (r▸Z.reader_live s e)
    · exact Or.inl r
  | readerLab s e j c dir=>
    simp only [expand,z62,y8,or_false,qb]
    by_cases r : Z.reader s e = j
    · right
      have hrl : x3 n D (Z.wire (zh n edges s e.val) j) c↔x3 n D (flip s (Z.edge e)) c:=by
        rw [← r,Z.read]
      cases dir
      · simp only [Bool.not_false,Bool.false_eq_true,ite_true,ite_false]
        by_cases h1 : x3 n D (flip s (Z.edge e)) c
        · exact Or.inl (hrl.2 h1)
        · exact Or.inr h1
      · simp only [Bool.not_true,Bool.false_eq_true,ite_true,ite_false]
        by_cases h1 : x3 n D (flip s (Z.edge e)) c
        · exact Or.inr h1
        · exact Or.inl (fun h2=>h1 (hrl.1 h2))
    · exact Or.inl r
  | eqLab s e f c dir=>
    simp only [expand,z62,y8,or_false,qb]
    by_cases r : Z.edge e = Z.edge f
    · right
      rw [r]
      cases dir
      · simp only [Bool.not_false,Bool.false_eq_true,ite_true,ite_false]
        exact em _
      · simp only [Bool.not_true,Bool.false_eq_true,ite_true,ite_false]
        exact (em _).symm
    · exact Or.inl r
  | gateEq s e f j=>
    simp only [enabled,beq_iff_eq] at en;simp only [expand,yn,xv,y8,or_false,qb]
    by_cases r1 : Z.reader s e = j
    · by_cases r2 : Z.reader s f = j
      · exact Or.inr (Or.inr (z0t s (by rw [← Z.read,← Z.read,r1,r2,en])))
      · exact Or.inr (Or.inl r2)
    · exact Or.inl r1
  | ineligPure x c=>
    simp only [enabled,Bool.and_eq_true,Bool.or_eq_true,bne_iff_ne,ne_eq,beq_iff_eq] at en;simp only [expand,yn,y8,or_false,qb,x3]
    rcases en with ⟨⟨hxI,hxcv⟩,hcase⟩
    have hxc : x≠c:=fun e=>hxcv (congrArg Fin.val e);have hxIm : x∈(mask I : Finset (Fin n)):=by simp [mask,hxI]
    have hself:=(qj.mp (Z.member x 0)).2.1;intro hmem
    rcases hcase with hxG | ⟨⟨hc2t,hx0⟩,h45 | ⟨hcI,hcG⟩⟩
    · have hp:=we hG h.1 hc hxG (eq▸hxIm) hself
      rw [hp,mem_singleton] at hmem;exact hxc hmem.symm
    · have hsub:=hc2 hc2t x hx0 _ hself c hmem
      rcases hsub with h0 | h4 | h5
      · exact hxc (Fin.ext (hx0.trans h0.symm))
      · exact h45.1 h4
      · exact h45.2 h5
    · have hcIm : c∈(mask I : Finset (Fin n)):=by simp [mask,hcI]
      have hp:=we hG h.1 hc hcG (eq▸hcIm) hmem;rw [hp,mem_singleton] at hself;exact hxc hself
  | fixedRes x dir=>
    simp only [enabled,Bool.and_eq_true,bne_iff_ne,ne_eq] at en;obtain ⟨hw0,hmem⟩:=en;obtain ⟨h0,hres0⟩:=Z.res0_ok hw0
    cases dir
    · simp only [expand,qh,List.mem_singleton,exists_eq_left,Bool.false_eq_true,ite_false,qb]
      intro hr;have hx:=(z4v Z ⟨0,h0⟩ x).1 hr;simp only [Bool.false_eq_true,ite_false,Bool.not_eq_true'] at hmem;have hm:=(hres0 x).1 hx;simp [mask,hmem] at hm
    · simp only [expand,qh,List.mem_singleton,exists_eq_left,ite_true,qb]
      simp only [ite_true] at hmem;exact (z4v Z ⟨0,h0⟩ x).2 ((hres0 x).2 (by simp [mask,hmem]))
  | exactPair x i y j p=>
    simp only [enabled,Bool.and_eq_true,bne_iff_ne,ne_eq,List.any_eq_true,List.mem_range,Bool.not_eq_true'] at en
    rcases en with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hind,hiI⟩,hjI⟩,hiG⟩,hjG⟩,_⟩,hxP⟩,hyP⟩,hix⟩,hjy⟩,a,ha,⟨hpA,hja⟩,hnia⟩
    have hiIm : i∈(mask I : Finset (Fin n)):=by simp [mask,hiI]
    have hjIm : j∈(mask I : Finset (Fin n)):=by simp [mask,hjI]
    have hxPm : x∈(mask p : Finset (Fin n)):=by simp [mask,hxP]
    have hyPm : y∈(mask p : Finset (Fin n)):=by simp [mask,hyP]
    have hji : ∃ a∈(mask p : Finset (Fin n)),z4 neigh j a∧¬ z4 neigh i a:=
      ⟨⟨a,ha⟩,by simp [mask,hpA],hja,fun hbad=>Bool.false_ne_true (hnia▸hbad)⟩
    simp only [expand,z60,vq,qb]
    rcases z0l hG h hc hz1 (mask p) (yu hind) hiG hjG (eq▸hiIm) (eq▸hjIm) hji with
      ⟨g,s,hg,ht,ch,ex⟩ | ⟨g,s,hg,ht,ch,ex⟩
    · left
      have heW : (g,s)∈yl n D x:=by
        refine qj.mpr ⟨hg,(ex _ hxPm).2 hix,?_⟩
        intro hx2;have hp:=ys hG h.1 hc i hiG _ (qk h.1 ch);have heq:=mem_singleton.mp (hp (qg h.1 hg ht (!s) hx2));exact hG.2.1 i (heq▸hix)
      obtain ⟨l,live,same⟩:=Z.covers x (g,s) heW;exact ⟨l,lt_of_lt_of_le live (Z.limit x),live,fun c inc=>by simpa [x3,same] using ex c inc⟩
    · right
      have heW : (g,s)∈yl n D y:=by
        refine qj.mpr ⟨hg,(ex _ hyPm).2 hjy,?_⟩
        intro hy2;have hp:=ys hG h.1 hc j hjG _ (qk h.1 ch);have heq:=mem_singleton.mp (hp (qg h.1 hg ht (!s) hy2));exact hG.2.1 j (heq▸hjy)
      obtain ⟨l,live,same⟩:=Z.covers y (g,s) heW;exact ⟨l,lt_of_lt_of_le live (Z.limit y),live,fun c inc=>by simpa [x3,same] using ex c inc⟩
def bits (v pos w : Nat) : Nat:=(v >>> pos) &&& ((1 <<< w) - 1)
def yy (v : Nat) : Nat:=
  match v &&& 15 with
  | 0=>12 | 1=>16 | 2=>12 | 3=>12 | 4=>14
  | 5=>14 | 6=>14 | 7=>18 | 8=>22 | _=>16
def w7 (v : Nat) : Nat:=
  match v &&& 31 with
  | 0=>13 | 1=>13 | 2=>17 | 3=>9 | 4=>13 | 5=>15
  | 6=>19 | 7=>19 | 8=>23 | 9=>23 | 10=>27 | 11=>17
  | 12=>17 | 13=>17 | 14=>17 | 15=>21 | 16=>11 | 17=>15
  | 18=>20 | 19=>21 | 20=>20 | 21=>13 | 22=>10 | _=>27
def z5e (n m : ℕ) [NeZero n] [NeZero m] (maskBook : List Nat) (v : Nat) : Fact n m:=
  match v &&& 15 with
  | 0=>.live (Fin.ofNat n (bits v 4 4)) (bits v 8 4)
  | 1=>.lab (Fin.ofNat n (bits v 4 4)) (bits v 8 4) (Fin.ofNat n (bits v 12 4))
  | 2=>.res (bits v 4 4) (Fin.ofNat n (bits v 8 4))
  | 3=>.common (Fin.ofNat n (bits v 4 4)) (Fin.ofNat n (bits v 8 4))
  | 4=>.gate (Fin.ofNat m (bits v 4 5)) (Fin.ofNat m (bits v 9 5))
  | 5=>.reader (bits v 4 1 == 1) (Fin.ofNat m (bits v 5 5)) (bits v 10 4)
  | 6=>.es (bits v 4 1 == 1) (Fin.ofNat m (bits v 5 5)) (Fin.ofNat n (bits v 10 4))
  | 7=>.avoid (Fin.ofNat n (bits v 4 4)) (maskBook.getD (bits v 8 6) 0) (bits v 14 4)
  | 8=>.see (Fin.ofNat n (bits v 4 4)) (Fin.ofNat n (bits v 8 4)) (maskBook.getD (bits v 12 6) 0) (bits v 18 4)
  | 9=>.diff (bits v 4 4) (Fin.ofNat n (bits v 8 4)) (Fin.ofNat n (bits v 12 4))
  | _=>default
def z5w (n m : ℕ) [NeZero n] [NeZero m] (maskBook : List Nat) (v : Nat) : Scheme n m:=
  match v &&& 31 with
  | 0=>.self (Fin.ofNat n (bits v 5 4)) (bits v 9 4)
  | 1=>.earlier (Fin.ofNat n (bits v 5 4)) (bits v 9 4)
  | 2=>.labCommon (Fin.ofNat n (bits v 5 4)) (Fin.ofNat n (bits v 9 4)) (bits v 13 4)
  | 3=>.someRes (Fin.ofNat n (bits v 5 4))
  | 4=>.allRes (Fin.ofNat n (bits v 5 4)) (bits v 9 4)
  | 5=>.exposure (Fin.ofNat n (bits v 5 4)) (maskBook.getD (bits v 9 6) 0)
  | 6=>.exactAt (Fin.ofNat n (bits v 5 4)) (Fin.ofNat n (bits v 9 4)) (maskBook.getD (bits v 13 6) 0)
  | 7=>.avoidLive (Fin.ofNat n (bits v 5 4)) (maskBook.getD (bits v 9 6) 0) (bits v 15 4)
  | 8=>.seeLive (Fin.ofNat n (bits v 5 4)) (Fin.ofNat n (bits v 9 4)) (maskBook.getD (bits v 13 6) 0) (bits v 19 4)
  | 9=>.avoidNot (Fin.ofNat n (bits v 5 4)) (Fin.ofNat n (bits v 9 4)) (maskBook.getD (bits v 13 6) 0) (bits v 19 4)
  | 10=>.seeLab (Fin.ofNat n (bits v 5 4)) (Fin.ofNat n (bits v 9 4)) (Fin.ofNat n (bits v 13 4)) (maskBook.getD (bits v 17 6) 0) (bits v 23 4)
  | 11=>.diffX (bits v 5 4) (Fin.ofNat n (bits v 9 4)) (Fin.ofNat n (bits v 13 4))
  | 12=>.diffC (bits v 5 4) (Fin.ofNat n (bits v 9 4)) (Fin.ofNat n (bits v 13 4))
  | 13=>.adjacentCommon (Fin.ofNat n (bits v 5 4)) (Fin.ofNat n (bits v 9 4)) (Fin.ofNat n (bits v 13 4))
  | 14=>.resCommon (Fin.ofNat n (bits v 5 4)) (Fin.ofNat n (bits v 9 4)) (bits v 13 4)
  | 15=>.residual (Fin.ofNat n (bits v 5 4)) (Fin.ofNat n (bits v 9 4)) (bits v 13 4) (bits v 17 4)
  | 16=>.readerAny (bits v 5 1 == 1) (Fin.ofNat m (bits v 6 5))
  | 17=>.readerLive (bits v 5 1 == 1) (Fin.ofNat m (bits v 6 5)) (bits v 11 4)
  | 18=>.readerLab (bits v 5 1 == 1) (Fin.ofNat m (bits v 6 5)) (bits v 11 4) (Fin.ofNat n (bits v 15 4)) (bits v 19 1 == 1)
  | 19=>.eqLab (bits v 5 1 == 1) (Fin.ofNat m (bits v 6 5)) (Fin.ofNat m (bits v 11 5)) (Fin.ofNat n (bits v 16 4)) (bits v 20 1 == 1)
  | 20=>.gateEq (bits v 5 1 == 1) (Fin.ofNat m (bits v 6 5)) (Fin.ofNat m (bits v 11 5)) (bits v 16 4)
  | 21=>.ineligPure (Fin.ofNat n (bits v 5 4)) (Fin.ofNat n (bits v 9 4))
  | 22=>.fixedRes (Fin.ofNat n (bits v 5 4)) (bits v 9 1 == 1)
  | 23=>.exactPair (Fin.ofNat n (bits v 5 4)) (Fin.ofNat n (bits v 9 4)) (Fin.ofNat n (bits v 13 4)) (Fin.ofNat n (bits v 17 4)) (maskBook.getD (bits v 21 6) 0)
  | _=>default
def atLit (n m : ℕ) [NeZero n] [NeZero m] (mb : List Nat) (atbl : Array (List Nat)) (l : Lit) : Fact n m×Bool:=
  (z5e n m mb (z4c atbl l.1),l.2)
def z2m {n m : ℕ} [NeZero n] [NeZero m] (neigh : List Nat) (edges : List (Nat×Nat))
    (goodB : Fin n→ Bool) (c2 bz0 : Bool) (w0 k I : Nat) (mb : List Nat)
    (atbl : Array (List Nat)) (r : Scheme n m) (c : Clause) : Bool:=
  enabled neigh edges goodB c2 bz0 w0 k I r &&
  let cl:=c.map (atLit n m mb atbl)
  (expand neigh edges k I r).all (fun p=>cl.contains p)
def ze {n m : ℕ} [NeZero n] [NeZero m] (neigh : List Nat) (edges : List (Nat×Nat))
    (goodB : Fin n→ Bool) (c2 bz0 : Bool) (w0 k I : Nat) (mb : List Nat)
    (atbl : Array (List Nat)) (book : Nat→ Clause) : Nat→ List Nat→ Bool
  | _,[]=>true
  | pos,sc :: scs=>
    z2m neigh edges goodB c2 bz0 w0 k I mb atbl (z5w n m mb sc) (book pos) &&
    ze (n:=n) (m:=m) neigh edges goodB c2 bz0 w0 k I mb atbl book (pos + 1) scs
noncomputable def z1e {n m : ℕ} [NeZero n] [NeZero m] {neigh : List Nat} {edges : List (Nat×Nat)}
    {D : Dag} {k I w0 : Nat} (Z : Layout n m edges D k I w0) (mb : List Nat) (atbl : Array (List Nat)) (idx : Nat) : Bool:=
  @decide (qb (neigh:=neigh) Z (z5e n m mb (z4c atbl idx))) (Classical.propDecidable _)
theorem wp {n m : ℕ} [NeZero n] [NeZero m] {neigh : List Nat} {edges : List (Nat×Nat)}
    {goodB : Fin n→ Bool} {c2 bz0 : Bool} {w0 k I : Nat} {D : Dag}
    (Z : Layout n m edges D k I w0)
    (hG : zc (z4 neigh) (fun v=>goodB v = true))
    (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (hz1 : qd n D≤ 1) (hz0 : bz0 = true→ qd n D = 0)
    (eq : (mask I : Finset (Fin n)) = z1 n D)
    (hc2 : c2 = true→ ∀ (x : Fin n),x.val = 0→ ∀ w,x∈supp n D w→
      ∀ c : Fin n,c∈supp n D w→ c.val = 0∨c.val = 4∨c.val = 5)
    (mb : List Nat) (atbl : Array (List Nat)) (book : Nat→ Clause) {pos : Nat}
    (prev : qf (z1e (neigh:=neigh) Z mb atbl) book pos)
    (R : List Nat)
    (ok : ze (n:=n) (m:=m) neigh edges goodB c2 bz0 w0 k I mb atbl book pos R = true) :
    qf (z1e (neigh:=neigh) Z mb atbl) book (pos + R.length):=by
  have localSound (r : Scheme n m) (c : Clause)
      (lok : z2m neigh edges goodB c2 bz0 w0 k I mb atbl r c = true) :
      Holds (z1e (neigh:=neigh) Z mb atbl) c:=by
    simp only [z2m,Bool.and_eq_true] at lok;obtain ⟨p,hm,hval⟩:=z55 Z hG h hc hz1 hz0 eq hc2 r lok.1;have mem:=List.contains_iff_mem.mp (List.all_eq_true.mp lok.2 p hm);obtain ⟨l,hl,eqp⟩:=List.mem_map.mp mem;subst p
    refine ⟨l,hl,?_⟩
    rcases l with ⟨i,b⟩
    cases b <;> simp [z1e,Yes,atLit] at hval ⊢ <;> exact hval
  induction R generalizing pos with
  | nil=>simpa using prev
  | cons sc scs ih=>
    simp only [ze,Bool.and_eq_true] at ok;have hnext : qf (z1e (neigh:=neigh) Z mb atbl) book (pos + 1):=by
      intro i hi
      by_cases hlt : i < pos
      · exact prev i hlt
      · have heq : i = pos:=by omega
        subst heq;exact localSound _ _ ok.1
    have hres:=ih hnext ok.2
    simpa [Nat.add_assoc,Nat.add_comm 1] using hres
theorem z2e {v : Nat→ Bool} {book : Nat→ Clause} : qf v book 0:=
  fun _ hi=>absurd hi (Nat.not_lt_zero _)
def zr (litW : Nat) (tbl : Array (List Nat)) (i : Nat) : Clause:=
  let x:=z4c tbl i
  z5r litW (x % 64) (x >>> 6)
theorem xj {n m : ℕ} [NeZero n] [NeZero m] {neigh : List Nat} {edges : List (Nat×Nat)}
    {goodB : Fin n→ Bool} {c2 bz0 : Bool} {w0 k I litW cidW orig tot lc : Nat}
    {mb : List Nat} {atbl tbl : Array (List Nat)} {sc0 rs0 lu : List Nat} {D : Dag}
    (bpVal : Nat)
    (hG : zc (z4 neigh) (fun v=>goodB v = true))
    (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (adjE : ∀ e : Fin m,z4 neigh (zh n edges false e.val) (zh n edges true e.val))
    (hEl : ∀ v∈z6 n D,goodB v = true)
    (hz1 : qd n D≤ 1) (hz0 : bz0 = true→ qd n D = 0)
    (bp : zu n D = bpVal) (eq : (mask I : Finset (Fin n)) = z1 n D)
    (hcard : k + (n - (mask I : Finset (Fin n)).card) = bpVal)
    (hw0 : w0≠0→ ∃ w,2≤ zd D w∧supp n D w = (mask w0 : Finset (Fin n))∧2≤ (supp n D w).card)
    (hc2 : c2 = true→ ∀ (x : Fin n),x.val = 0→ ∀ w,x∈supp n D w→
      ∀ c : Fin n,c∈supp n D w→ c.val = 0∨c.val = 4∨c.val = 5)
    (h0 : sc0.length = orig) (ht : orig + rs0.length = tot)
    (hic0 : ze (n:=n) (m:=m) neigh edges goodB c2 bz0 w0 k I mb atbl (zr litW tbl) 0 sc0 = true)
    (hro0 : zo (zr litW tbl) cidW orig rs0 = true)
    (hcf : zf (zr litW tbl) tot lc lu 0 = true) : False:=by
  obtain ⟨Z⟩:=vb (m:=m) (k:=k) (I:=I) (w0:=w0) (bpVal:=bpVal) hG h hc adjE hEl bp eq hcard hw0;have hb : qf (z1e (neigh:=neigh) Z mb atbl) (zr litW tbl) orig:=
    (by omega : 0 + sc0.length = orig)▸wp Z hG h hc hz1 hz0 eq hc2 mb atbl (zr litW tbl) z2e sc0 hic0
  exact z4h (ht▸z17 hb rs0 hro0) _ _ hcf
theorem z5v {n m : ℕ} [NeZero n] [NeZero m] {neigh : List Nat} {edges : List (Nat×Nat)}
    {goodB : Fin n→ Bool} {c2 bz0 : Bool} {w0 k I litW cidW m1 orig tot lc : Nat}
    {mb : List Nat} {atbl tbl : Array (List Nat)} {sc0 sc1 rs0 lu : List Nat} {D : Dag}
    (bpVal : Nat)
    (hG : zc (z4 neigh) (fun v=>goodB v = true))
    (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (adjE : ∀ e : Fin m,z4 neigh (zh n edges false e.val) (zh n edges true e.val))
    (hEl : ∀ v∈z6 n D,goodB v = true)
    (hz1 : qd n D≤ 1) (hz0 : bz0 = true→ qd n D = 0)
    (bp : zu n D = bpVal) (eq : (mask I : Finset (Fin n)) = z1 n D)
    (hcard : k + (n - (mask I : Finset (Fin n)).card) = bpVal)
    (hw0 : w0≠0→ ∃ w,2≤ zd D w∧supp n D w = (mask w0 : Finset (Fin n))∧2≤ (supp n D w).card)
    (hc2 : c2 = true→ ∀ (x : Fin n),x.val = 0→ ∀ w,x∈supp n D w→
      ∀ c : Fin n,c∈supp n D w→ c.val = 0∨c.val = 4∨c.val = 5)
    (h0 : sc0.length = m1) (h1 : m1 + sc1.length = orig) (ht : orig + rs0.length = tot)
    (hic0 : ze (n:=n) (m:=m) neigh edges goodB c2 bz0 w0 k I mb atbl (zr litW tbl) 0 sc0 = true)
    (hic1 : ze (n:=n) (m:=m) neigh edges goodB c2 bz0 w0 k I mb atbl (zr litW tbl) m1 sc1 = true)
    (hro0 : zo (zr litW tbl) cidW orig rs0 = true)
    (hcf : zf (zr litW tbl) tot lc lu 0 = true) : False:=by
  obtain ⟨Z⟩:=vb (m:=m) (k:=k) (I:=I) (w0:=w0) (bpVal:=bpVal) hG h hc adjE hEl bp eq hcard hw0;have ha : qf (z1e (neigh:=neigh) Z mb atbl) (zr litW tbl) m1:=
    (by omega : 0 + sc0.length = m1)▸wp Z hG h hc hz1 hz0 eq hc2 mb atbl (zr litW tbl) z2e sc0 hic0
  have hb : qf (z1e (neigh:=neigh) Z mb atbl) (zr litW tbl) orig:=
    h1▸wp Z hG h hc hz1 hz0 eq hc2 mb atbl (zr litW tbl) ha sc1 hic1
  exact z4h (ht▸z17 hb rs0 hro0) _ _ hcf
theorem runS32 {n m : ℕ} [NeZero n] [NeZero m] {neigh : List Nat} {edges : List (Nat×Nat)}
    {goodB : Fin n→ Bool} {c2 bz0 : Bool} {w0 k I litW cidW m1 m2 orig mid tot lc : Nat}
    {mb : List Nat} {atbl tbl : Array (List Nat)} {sc0 sc1 sc2 rs0 rs1 lu : List Nat} {D : Dag}
    (bpVal : Nat)
    (hG : zc (z4 neigh) (fun v=>goodB v = true))
    (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (adjE : ∀ e : Fin m,z4 neigh (zh n edges false e.val) (zh n edges true e.val))
    (hEl : ∀ v∈z6 n D,goodB v = true)
    (hz1 : qd n D≤ 1) (hz0 : bz0 = true→ qd n D = 0)
    (bp : zu n D = bpVal) (eq : (mask I : Finset (Fin n)) = z1 n D)
    (hcard : k + (n - (mask I : Finset (Fin n)).card) = bpVal)
    (hw0 : w0≠0→ ∃ w,2≤ zd D w∧supp n D w = (mask w0 : Finset (Fin n))∧2≤ (supp n D w).card)
    (hc2 : c2 = true→ ∀ (x : Fin n),x.val = 0→ ∀ w,x∈supp n D w→
      ∀ c : Fin n,c∈supp n D w→ c.val = 0∨c.val = 4∨c.val = 5)
    (h0 : sc0.length = m1) (h1 : m1 + sc1.length = m2) (h2 : m2 + sc2.length = orig)
    (hm : orig + rs0.length = mid) (ht : mid + rs1.length = tot)
    (hic0 : ze (n:=n) (m:=m) neigh edges goodB c2 bz0 w0 k I mb atbl (zr litW tbl) 0 sc0 = true)
    (hic1 : ze (n:=n) (m:=m) neigh edges goodB c2 bz0 w0 k I mb atbl (zr litW tbl) m1 sc1 = true)
    (hic2 : ze (n:=n) (m:=m) neigh edges goodB c2 bz0 w0 k I mb atbl (zr litW tbl) m2 sc2 = true)
    (hro0 : zo (zr litW tbl) cidW orig rs0 = true)
    (hro1 : zo (zr litW tbl) cidW mid rs1 = true)
    (hcf : zf (zr litW tbl) tot lc lu 0 = true) : False:=by
  obtain ⟨Z⟩:=vb (m:=m) (k:=k) (I:=I) (w0:=w0) (bpVal:=bpVal) hG h hc adjE hEl bp eq hcard hw0;have ha : qf (z1e (neigh:=neigh) Z mb atbl) (zr litW tbl) m1:=
    (by omega : 0 + sc0.length = m1)▸wp Z hG h hc hz1 hz0 eq hc2 mb atbl (zr litW tbl) z2e sc0 hic0
  have hb : qf (z1e (neigh:=neigh) Z mb atbl) (zr litW tbl) m2:=
    h1▸wp Z hG h hc hz1 hz0 eq hc2 mb atbl (zr litW tbl) ha sc1 hic1
  have hc' : qf (z1e (neigh:=neigh) Z mb atbl) (zr litW tbl) orig:=
    h2▸wp Z hG h hc hz1 hz0 eq hc2 mb atbl (zr litW tbl) hb sc2 hic2
  have hr : qf (z1e (neigh:=neigh) Z mb atbl) (zr litW tbl) mid:=
    hm▸z17 hc' rs0 hro0
  exact z4h (ht▸z17 hr rs1 hro1) _ _ hcf
end Compact
namespace GraphTools
open Finset
open DagTools Compact
theorem z3c {n : ℕ} (x : Fin n→ Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i:=by
  simp [List.getD_eq_getElem?_getD,i.isLt]
set_option maxHeartbeats 400000 in
theorem repr (n : ℕ) (I : Finset (Fin n)) : ∃ m : Fin (2 ^ n),(mask m.val : Finset (Fin n)) = I:=by
  let bs:=List.ofFn (fun i : Fin n=>decide (i∈I))
  let B:=BitVec.ofBoolListLE bs
  have hl : bs.length = n:=List.length_ofFn;have lt : B.toNat < 2 ^ n:=by have h:=B.isLt;change _ < 2 ^ bs.length at h;simpa [hl] using h
  refine ⟨⟨B.toNat,lt⟩,?_⟩
  ext i
  simp only [mask,mem_filter,mem_univ,true_and];change B.getLsbD i.val = true↔i∈I;rw [BitVec.getLsbD_ofBoolListLE];have g:=z3c (fun i : Fin n=>decide (i∈I)) i;simp only [bs,g,decide_eq_true_eq]
theorem z5j {n : ℕ} (k m : Nat) (e : k &&& m = k) :
    (mask k : Finset (Fin n))⊆mask m:=by
  intro v hv;simp only [mask,mem_filter,mem_univ,true_and] at *
  have h:=congrArg (fun z : Nat=>z.testBit v.val) e;change (k &&& m).testBit v.val = k.testBit v.val at h
  simpa only [Nat.testBit_and,hv,Bool.true_and] using h
theorem z5k {n : ℕ} (k m : Nat) (hk : k < 2 ^ n)
    (hsub : (mask k : Finset (Fin n))⊆mask m) : k &&& m = k:=by
  apply Nat.eq_of_testBit_eq
  intro i;rw [Nat.testBit_and]
  by_cases hi : i < n
  · by_cases hb : k.testBit i = true
    · have hm : (⟨i,hi⟩ : Fin n)∈(mask m : Finset (Fin n)):=
        hsub (by simp [mask,hb])
      simp only [mask,mem_filter,mem_univ,true_and] at hm;rw [hb,hm];rfl
    · simp only [Bool.not_eq_true] at hb
      rw [hb];rfl
  · have h0 : k.testBit i = false:=Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hk (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [h0];rfl
theorem z4p {n : ℕ} (k m : Nat) (hk : k < 2 ^ n)
    (hdis : Disjoint (mask k : Finset (Fin n)) (mask m)) : m &&& k = 0:=by
  apply Nat.eq_of_testBit_eq
  intro i;rw [Nat.testBit_and,Nat.zero_testBit]
  by_cases hi : i < n
  · by_cases hb : k.testBit i = true
    · have hnot : (⟨i,hi⟩ : Fin n)∉(mask m : Finset (Fin n)):=
        disjoint_left.mp hdis (by simp [mask,hb])
      simp only [mask,mem_filter,mem_univ,true_and,Bool.not_eq_true] at hnot;rw [hnot,hb];rfl
    · simp only [Bool.not_eq_true] at hb
      rw [hb,Bool.and_false]
  · have h0 : k.testBit i = false:=Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hk (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [h0,Bool.and_false]
def clean (edges : List (Nat×Nat)) (m : Nat) : Bool:=
  edges.all (fun e=>!(m.testBit e.1 && m.testBit e.2))
def z0r (n : ℕ) (edges : List (Nat×Nat)) (weights : List (Nat×Nat))
    (mustHave mustNot baseK cap m : Nat) : Bool:=
  clean edges m &&
  ((m &&& mustHave) == mustHave) &&
  ((m &&& mustNot) == 0) &&
  (let c:=(mask m : Finset (Fin n)).card
   decide (n + baseK≤ c + cap) &&
   weights.all (fun r=>(r.1 &&& m != r.1) || decide (n + r.2≤ c + cap)))
theorem z05 {n : ℕ} {neigh : List Nat} {edges : List (Nat×Nat)}
    {weights : List (Nat×Nat)} {mustHave mustNot baseK cap m : Nat} {D : Dag}
    (hcover : ∀ u v : Fin n,z4 neigh u v→ u∈z6 n D∨v∈z6 n D)
    (hEdges : ∀ q∈edges,∃ hu : q.1 < n,∃ hv : q.2 < n,z4 neigh ⟨q.1,hu⟩ ⟨q.2,hv⟩)
    (hMHlt : mustHave < 2 ^ n) (hMNlt : mustNot < 2 ^ n)
    (hMH : (mask mustHave : Finset (Fin n))⊆z1 n D)
    (hMN : Disjoint (mask mustNot : Finset (Fin n)) (z1 n D))
    (hBase : (z6 n D).card + baseK≤ zu n D)
    (hWeights : ∀ r∈weights,(mask r.1 : Finset (Fin n))⊆z1 n D→ (z6 n D).card + r.2≤ zu n D)
    (enc : (mask m : Finset (Fin n)) = z1 n D) (lim : zu n D≤ cap) :
    z0r n edges weights mustHave mustNot baseK cap m = true:=by
  have p:=zm n D;rw [← enc] at p;have cleanM : clean edges m = true:=by
    rw [clean,List.all_eq_true]
    rintro ⟨u,v⟩ e
    obtain ⟨hu,hv,hadj⟩:=hEdges (u,v) e;have a:=hcover ⟨u,hu⟩ ⟨v,hv⟩ hadj
    by_contra! fail
    have both : m.testBit u = true∧m.testBit v = true:=by simpa using fail
    have add (x : Fin n) (hx : m.testBit x.val = true) : x∉z6 n D:=by
      apply qt.mp
      rw [← enc];simpa [mask] using hx
    exact a.elim (add _ both.1) (add _ both.2)
  have mhEq : (m &&& mustHave) = mustHave:=by
    rw [Nat.and_comm];exact z5k mustHave m hMHlt (enc▸hMH)
  have mnEq : (m &&& mustNot) = 0:=z4p mustNot m hMNlt (enc▸hMN);simp only [z0r,cleanM,mhEq,mnEq,beq_self_eq_true,Bool.true_and,Bool.and_eq_true,
    decide_eq_true_eq,List.all_eq_true]
  refine ⟨by omega,?_⟩
  intro r hr
  by_cases eq : r.1 &&& m = r.1
  · have sub : (mask r.1 : Finset (Fin n))⊆z1 n D:=enc▸z5j _ _ eq
    have w:=hWeights r hr sub;have enough : n + r.2≤ (mask m : Finset (Fin n)).card + cap:=by omega
    simp [eq,enough]
  · simp [eq]
def vo {n : ℕ} (neigh : List Nat) (T J : Finset (Fin n)) (A : Fin n→ Finset (Fin n)) : Prop:=
  (∀ i∈J,(∃ a∈T,z4 neigh i a)∧∀ f∈T,∃ a∈A f,z4 neigh i a)∧
  (∀ f∈T,x0 neigh (A f)∧T.erase f⊆A f∧∃ a∈A f,z4 neigh f a)
instance {n : ℕ} (neigh : List Nat) (T J : Finset (Fin n)) (A : Fin n→ Finset (Fin n)) :
    Decidable (vo neigh T J A):=by unfold vo;infer_instance
def cost (n : ℕ) (D : Dag) (T : Finset (Fin n)):=(merges n D (zb n D T)).card
theorem share {n : ℕ} {neigh : List Nat} {Good : Fin n→ Prop} {D : Dag}
    (hG : zc (z4 neigh) Good) (h : z0 n D) (hc : z3 n (z4 neigh) D)
    {i x y : Fin n} (hiG : Good i) (hi : i∈z1 n D)
    (hx : z4 neigh i x) (hy : z4 neigh i y) :
    ∃ w : Nat,x∈supp n D w∧y∈supp n D w:=by
  obtain ⟨e,_,_,_,_,hn,_⟩:=ql hG h hc hiG hi;exact ⟨_,hn x hx,hn y hy⟩
theorem z6k {n : ℕ} {neigh : List Nat} {Good : Fin n→ Prop} {D : Dag}
    (hG : zc (z4 neigh) Good) (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (T : Finset (Fin n)) (i x y : Fin n) (hiG : Good i) (hi : i∈z1 n D)
    (geom : z4 neigh i x∧z4 neigh i y∧x∈T∧y∈T∧x≠y) :
    1≤ cost n D T:=by
  obtain ⟨w,hx,hy⟩:=share hG h hc hiG hi geom.1 geom.2.1;obtain ⟨j,hj,_⟩:=vn h.1 T w (one_lt_card.mpr
    ⟨x,mem_inter.mpr ⟨hx,geom.2.2.1⟩,y,mem_inter.mpr ⟨hy,geom.2.2.2.1⟩,geom.2.2.2.2⟩)
  exact card_pos.mpr ⟨j,hj⟩
theorem z6j {n : ℕ} {neigh : List Nat} {Good : Fin n→ Prop} {D : Dag}
    (hG : zc (z4 neigh) Good) (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (T : Finset (Fin n)) (i j x y z : Fin n) (hiG : Good i) (hjG : Good j)
    (hi : i∈z1 n D) (hj : j∈z1 n D)
    (geom : z4 neigh i x∧z4 neigh i y∧z4 neigh j x∧z4 neigh j z∧
      T.card = 3∧x∈T∧y∈T∧z∈T∧x≠y∧x≠z∧y≠z) :
    2≤ cost n D T:=by
  rcases geom with ⟨ix,iy,jx,jz,t3,xt,yt,zt,xy,xz,yz⟩
  obtain ⟨w,hx,hy⟩:=share hG h hc hiG hi ix iy;obtain ⟨v,hx',hz⟩:=share hG h hc hjG hj jx jz;exact z4d h.1 t3 xt yt zt xy xz yz hx hy hx' hz
theorem z4g {n : ℕ} {neigh : List Nat} {Good : Fin n→ Prop} {D : Dag}
    (hG : zc (z4 neigh) Good) (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (hEl : ∀ v∈z6 n D,Good v)
    {w0 : Nat} (hw0 : w0≠0→ ∃ w,2≤ zd D w∧supp n D w = (mask w0 : Finset (Fin n))∧2≤ (supp n D w).card)
    (T J : Finset (Fin n)) (A : Fin n→ Finset (Fin n))
    (valid : vo neigh T J A) (hJ : J⊆z1 n D) (hJG : ∀ i∈J,Good i)
    (m k : Nat) (hm : m≤ cost n D T)
    (hk : k + T.card≤ J.card + m + (if w0≠0∧Disjoint (mask w0 : Finset (Fin n)) T then 1 else 0)) :
    (z6 n D).card + k≤ zu n D:=by
  obtain ⟨b,hb⟩:=zz hG h.1 hc hEl;obtain ⟨pos,hpos⟩:=z3j hG h hc;have ex:=z63 hG h.1 hc hpos T J A
    (fun i hi=>⟨hJ hi,hJG i hi,(valid.1 i hi).1,(valid.1 i hi).2⟩) valid.2
  have fl:=ym h T (by rw [ye hG hc,empty_inter]);have hle:=card_le_card (inter_subset_left : T∩z6 n D⊆T);unfold cost at hm
  by_cases hbon : w0≠0∧Disjoint (mask w0 : Finset (Fin n)) T
  · rw [if_pos hbon] at hk
    obtain ⟨w,hfw,hsw,hcw⟩:=hw0 hbon.1;have sup:=w4 h.1 b hb hfw hcw T (hsw▸hbon.2);omega
  · rw [if_neg hbon] at hk
    have sup:=w5 h.1 b hb T;omega
abbrev wn:=Nat×Nat×Nat×Nat×Nat×Nat×Nat
def vp (r : wn):=(r.1,r.2.2.2.1)
def z28 (n a : Nat) (v : Fin n) : Finset (Fin n):=
  mask ((a >>> (n * v.val)) &&& ((1 <<< n) - 1))
def point (n p j : Nat) [NeZero n] : Fin n:=Fin.ofNat n ((p >>> (4 * j)) &&& 15)
def vv (n : ℕ) [NeZero n] (neigh : List Nat) (K T : Finset (Fin n)) (m p : Nat) : Prop:=
  let i:=point n p 0
  let j:=point n p 1
  let x:=point n p 2
  let y:=point n p 3
  let z:=point n p 4
  m = 0∨(m = 1∧i∈K∧z4 neigh i x∧z4 neigh i y∧x∈T∧y∈T∧x≠y)∨
    (m = 2∧i∈K∧j∈K∧z4 neigh i x∧z4 neigh i y∧z4 neigh j x∧z4 neigh j z∧
      T.card = 3∧x∈T∧y∈T∧z∈T∧x≠y∧x≠z∧y≠z)
instance (n : ℕ) [NeZero n] (neigh : List Nat) (K T : Finset (Fin n)) (m p : Nat) :
    Decidable (vv n neigh K T m p):=by unfold vv;infer_instance
def vc (n : ℕ) [NeZero n] (neigh : List Nat) (goodB : Fin n→ Bool) (w0 : Nat) (r : wn) : Bool:=
  let (K,T,J,k,m,p,a):=r
  decide (vo neigh (mask T : Finset (Fin n)) (mask J) (z28 n a)∧
    (∀ i∈(mask K : Finset (Fin n)),goodB i = true)∧
    (mask J : Finset (Fin n))⊆mask K∧
    k + (mask T : Finset (Fin n)).card≤ (mask J : Finset (Fin n)).card + m +
      (if w0≠0∧Disjoint (mask w0 : Finset (Fin n)) (mask T) then 1 else 0)∧
    vv n neigh (mask K) (mask T) m p)
theorem v3 {n : ℕ} [NeZero n] {neigh : List Nat} {goodB : Fin n→ Bool} {w0 : Nat} {D : Dag}
    (hG : zc (z4 neigh) (fun v=>goodB v = true)) (h : z0 n D)
    (hc : z3 n (z4 neigh) D) (hEl : ∀ v∈z6 n D,goodB v = true)
    (hw0 : w0≠0→ ∃ w,2≤ zd D w∧supp n D w = (mask w0 : Finset (Fin n))∧2≤ (supp n D w).card)
    (r : wn) (ok : vc n neigh goodB w0 r = true)
    (sub : (mask (vp r).1 : Finset (Fin n))⊆z1 n D) :
    (z6 n D).card + (vp r).2≤ zu n D:=by
  rcases r with ⟨K,T,J,k,m,p,a⟩
  obtain ⟨valid,hKG,small,size,geom⟩:=of_decide_eq_true ok;have hmc : m≤ cost n D (mask T):=by
    rcases geom with rfl | ⟨rfl,iK,rest⟩ | ⟨rfl,iK,jK,rest⟩
    · exact Nat.zero_le _
    · exact z6k hG h hc (mask T) (point n p 0) (point n p 2) (point n p 3) (hKG _ iK) (sub iK) rest
    · exact z6j hG h hc (mask T) (point n p 0) (point n p 1) (point n p 2) (point n p 3) (point n p 4)
        (hKG _ iK) (hKG _ jK) (sub iK) (sub jK) rest
  exact z4g hG h hc hEl hw0 (mask T) (mask J) (z28 n a) valid
    (small.trans sub) (fun i hi=>hKG i (small hi)) m k hmc size
def z9 {n : ℕ} (neigh : List Nat) (P : Finset (Fin n)) (i : Fin n):=P.filter (z4 neigh i)
def wide {n : ℕ} (neigh : List Nat) (P : Finset (Fin n)):=
  Finset.univ.filter fun i : Fin n=>(z9 neigh P i).card = 3
def labels {n : ℕ} (neigh : List Nat) (P O : Finset (Fin n)):=
  (Finset.univ \ O).biUnion (z9 neigh P)
theorem xb {n : ℕ} (neigh : List Nat) (P : Finset (Fin n)) (i a : Fin n) :
    a∈z9 neigh P i↔a∈P∧z4 neigh i a:=mem_filter
theorem z6m {n : ℕ} (neigh : List Nat)
    (deg : ∀ j : Fin n,(z9 neigh Finset.univ j).card≤ 3) (P : Finset (Fin n)) (i : Fin n) :
    (z9 neigh P i).card≤ 3:=
  le_trans (card_le_card (fun a ha=>
    (xb _ _ _ a).2 ⟨mem_univ _,((xb _ _ _ a).1 ha).2⟩)) (deg i)
theorem z0q {n : ℕ} (neigh : List Nat)
    (ff : ∀ i j : Fin n,i≠j→ (z9 neigh Finset.univ i∩z9 neigh Finset.univ j).card≤ 1)
    (P : Finset (Fin n)) {i j : Fin n} (ne : i≠j) :
    (z9 neigh P i∩z9 neigh P j).card≤ 1:=by
  apply le_trans (card_le_card _) (ff _ _ ne)
  intro a ha
  rcases mem_inter.mp ha with ⟨ai,aj⟩
  exact mem_inter.mpr ⟨(xb _ _ _ _).2 ⟨mem_univ _,((xb _ _ _ _).1 ai).2⟩,
    (xb _ _ _ _).2 ⟨mem_univ _,((xb _ _ _ _).1 aj).2⟩⟩
noncomputable def marks {n : ℕ} (neigh : List Nat) (D : Dag) (P : Finset (Fin n)) : Finset (Fin n):=by
  classical
  exact (wide neigh P).filter (fun i=>qq n D P (z9 neigh P i))
theorem z1x {n : ℕ} {neigh : List Nat} {D : Dag} {P : Finset (Fin n)} {i : Fin n} :
    i∈marks neigh D P↔(z9 neigh P i).card = 3∧qq n D P (z9 neigh P i):=by
  classical
  simp [marks,wide]
theorem z3r {n : ℕ} {neigh : List Nat} {Good : Fin n→ Prop} {D : Dag}
    (hG : zc (z4 neigh) Good) (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (hEl : ∀ v∈z6 n D,Good v)
    (deg : ∀ j : Fin n,(z9 neigh Finset.univ j).card≤ 3)
    (ff : ∀ i j : Fin n,i≠j→ (z9 neigh Finset.univ i∩z9 neigh Finset.univ j).card≤ 1)
    (P : Finset (Fin n)) (hind : x0 neigh P) (p7 : P.card≤ 7)
    (hwideG : ∀ i∈wide neigh P,Good i) :
    2 * (marks neigh D P).card + (z1 n D∩wide neigh P).card +
      (labels neigh P (marks neigh D P)).card + (z6 n D).card≤
    P.card + (P∩z6 n D).card + zu n D:=by
  classical
  let O:=marks neigh D P
  let W:=z1 n D∩wide neigh P
  obtain ⟨b,hb⟩:=zz hG h.1 hc hEl;obtain ⟨E,ne,he⟩:=z2f hG h hc P W (fun i hi=>by
    rcases mem_inter.mp hi with ⟨hin,wi⟩
    have three : (z9 neigh P i).card = 3:=by simpa [wide] using wi
    exact ⟨hin,hwideG i wi,z9 neigh P i,filter_subset _ _,by omega,
      fun a ha=>((xb _ _ _ a).1 ha).2⟩)
  have each : ∀ f∈labels neigh P O,∃ c,c∉O∧f∈z9 neigh P c:=by
    intro f hf;obtain ⟨c,hc2,hf⟩:=mem_biUnion.mp hf;exact ⟨c,(mem_sdiff.mp hc2).2,hf⟩
  choose! c chooseC using each
  have src (f) (hf : f∈labels neigh P O) : ∃ e,xh n D P (z9 neigh P (c f)) f e:=by
    let v:=c f
    let U:=z9 neigh P v
    have inside : U⊆P:=filter_subset _ _;have cov : U.card≤ 2∨U.card = 3∧¬ qq n D P U:=by
      have small : U.card≤ 3:=z6m neigh deg P v
      by_cases t : U.card = 3
      · exact Or.inr ⟨t,fun occ=>(chooseC _ hf).1 (z1x.2 ⟨t,occ⟩)⟩
      · exact Or.inl (by omega)
    let X:=insert v (P \ U)
    refine z3z hG h.1 hc (X:=X) inside cov ?_ (fun a ha=>mem_insert_of_mem ha)
      (chooseC _ hf).2 ⟨v,mem_insert_self _ _,hG.1 _ _ ((xb _ _ _ _).1 (chooseC _ hf).2).2⟩
    have no (a) (ha : a∈P \ U) : ¬ z4 neigh v a:=
      fun ev=>(mem_sdiff.mp ha).2 ((xb neigh P v a).2 ⟨(mem_sdiff.mp ha).1,ev⟩)
    intro i hi j hj
    rcases mem_insert.mp hi with rfl | hi <;> rcases mem_insert.mp hj with rfl | hj
    · exact hG.2.1 _
    · exact no _ hj
    · exact fun a=>no _ hi (hG.1 _ _ a)
    · exact hind _ (mem_sdiff.mp hi).1 _ (mem_sdiff.mp hj).1
  have main:=z6l h.1 p7 (O.image (z9 neigh P)) (fun T ht=>by
    obtain ⟨i,hi,rfl⟩:=mem_image.mp ht;exact z1x.mp hi)
    (fun T ht U hu neq=>by
      obtain ⟨i,hi,rfl⟩:=mem_image.mp ht;obtain ⟨j,hj,rfl⟩:=mem_image.mp hu;exact z0q neigh ff P (fun e=>neq (congrArg (z9 neigh P) e)))
    E he (labels neigh P O) (fun f=>z9 neigh P (c f)) src (fun f hf T ht=>by
      obtain ⟨i,hi,rfl⟩:=mem_image.mp ht;exact z0q neigh ff P (fun eq=>(chooseC _ hf).1 (eq▸hi)))
  have inj : Set.InjOn (z9 neigh P) O:=by
    intro u hu v hv eq
    by_contra bad
    have small:=z0q neigh ff P bad;rw [eq,inter_self] at small;have full:=(z1x.mp hv).1;omega
  rw [card_image_of_injOn inj,ne] at main;have fl:=ym h P (by rw [ye hG hc];simp);have sup:=w5 h.1 b hb P;change 2 * O.card + W.card + (labels neigh P O).card + (z6 n D).card≤
    P.card + (P∩z6 n D).card + zu n D
  omega
theorem z5q {n : ℕ} {neigh : List Nat} {Good : Fin n→ Prop} {D : Dag}
    (hG : zc (z4 neigh) Good) (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (ff : ∀ i j : Fin n,i≠j→ (z9 neigh Finset.univ i∩z9 neigh Finset.univ j).card≤ 1)
    (z : qd n D≤ 1) (P : Finset (Fin n)) (ind : x0 neigh P)
    {i j : Fin n} (hiG : Good i) (hjG : Good j) (hi : i∈z1 n D) (hj : j∈z1 n D)
    (ne : i≠j) (wi : i∈wide neigh P) (wj : j∈wide neigh P) :
    i∈marks neigh D P∨j∈marks neigh D P:=by
  have ci : (z9 neigh P i).card = 3:=by simpa [wide] using wi
  have cj : (z9 neigh P j).card = 3:=by simpa [wide] using wj
  have miss : ¬ z9 neigh P j⊆z9 neigh P i:=by
    intro e;have small:=z0q neigh ff P ne.symm;rw [inter_eq_left.mpr e,cj] at small;omega
  obtain ⟨a,aj,ai⟩:=not_subset.mp miss;obtain ⟨ap,ja⟩:=(xb _ _ _ _).mp aj;have no : ¬ z4 neigh i a:=fun ia=>ai ((xb _ _ _ _).2 ⟨ap,ia⟩);have asOcc {k : Fin n} {w : Nat} (ex : ∀ a∈P,a∈supp n D w↔z4 neigh k a) :
      qq n D P (z9 neigh P k):=by
    refine ⟨w,?_⟩;ext a
    simp only [mem_inter,xb]
    constructor
    · rintro ⟨a1,a2⟩;exact ⟨a2,(ex a a2).1 a1⟩
    · rintro ⟨a1,a2⟩;exact ⟨(ex a a1).2 a2,a1⟩
  rcases z0l hG h hc z P ind hiG hjG hi hj ⟨a,ap,ja,no⟩ with
    ⟨k,s,_,_,_,ex⟩ | ⟨k,s,_,_,_,ex⟩
  · exact Or.inl (z1x.2 ⟨ci,asOcc ex⟩)
  · exact Or.inr (z1x.2 ⟨cj,asOcc ex⟩)
theorem yc {n : ℕ} {neigh : List Nat} {Good : Fin n→ Prop} {D : Dag}
    (hG : zc (z4 neigh) Good) (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (hEl : ∀ v∈z6 n D,Good v)
    (deg : ∀ j : Fin n,(z9 neigh Finset.univ j).card≤ 3)
    (ff : ∀ i j : Fin n,i≠j→ (z9 neigh Finset.univ i∩z9 neigh Finset.univ j).card≤ 1)
    (z : qd n D≤ 1) (P I : Finset (Fin n)) (target : Nat) (e : Fin n)
    (ind : x0 neigh P) (p7 : P.card≤ 7) (hwideG : ∀ i∈wide neigh P,Good i)
    (hwsub : wide neigh P⊆insert e (I∩wide neigh P))
    (geo : let IW:=I∩wide neigh P
      let ok (O : Finset (Fin n)):=target + P.card + (P \ I).card≤ 2 * O.card + IW.card + (labels neigh P O).card + (n - I.card)
      ok IW∧ok (insert e IW)∧∀ k∈IW,ok (IW.erase k)∧ok (insert e (IW.erase k)))
    (eq : I = z1 n D) : target≤ zu n D:=by
  classical
  have eqI:=zm n D;have bound:=z3r hG h hc hEl deg ff P ind p7 hwideG;have seteq : P \ I = P∩z6 n D:=by ext x;simp [eq,qt]
  let O:=marks neigh D P
  let IW:=I∩wide neigh P
  have hOsub : O⊆insert e IW:=(filter_subset _ _).trans hwsub;have hg : target + P.card + (P \ I).card≤ 2 * O.card + IW.card + (labels neigh P O).card + (n - I.card):=by
    by_cases all : IW⊆O
    · by_cases he : e∈O
      · have hO : O = insert e IW:=by
          ext x;constructor
          · exact fun hx=>hOsub hx
          · intro hx;rcases mem_insert.mp hx with rfl | hx;exact he;exact all hx
        simpa [hO] using geo.2.1
      · have hO : O = IW:=by
          ext x;constructor
          · intro hx;rcases mem_insert.mp (hOsub hx) with rfl | hx;exact absurd hx he;exact hx
          · exact fun hx=>all hx
        simpa [hO] using geo.1
    · obtain ⟨k,hk,miss⟩:=not_subset.mp all
      have her : IW.erase k⊆O:=fun i hi=>by
        obtain ⟨ne,wi⟩:=mem_erase.mp hi;have hk':=mem_inter.mp hk;have wi':=mem_inter.mp wi;exact (z5q hG h hc ff z P ind (hwideG i wi'.2) (hwideG k hk'.2)
          (eq▸wi'.1) (eq▸hk'.1) ne wi'.2 hk'.2).resolve_right miss
      by_cases he : e∈O
      · have hO : O = insert e (IW.erase k):=by
          ext x;constructor
          · intro hx;rcases mem_insert.mp (hOsub hx) with rfl | hx'
            · exact mem_insert_self _ _
            · exact mem_insert_of_mem (mem_erase.mpr ⟨fun hxk=>miss (hxk▸hx),hx'⟩)
          · intro hx;rcases mem_insert.mp hx with rfl | hx';exact he;exact her hx'
        simpa [hO] using (geo.2.2 k hk).2
      · have hO : O = IW.erase k:=by
          ext x;constructor
          · intro hx;rcases mem_insert.mp (hOsub hx) with rfl | hx'
            · exact absurd hx he
            · exact mem_erase.mpr ⟨fun hxk=>miss (hxk▸hx),hx'⟩
          · exact fun hx=>her hx
        simpa [hO] using (geo.2.2 k hk).1
  dsimp only [O,IW] at hg;rw [← eq] at bound eqI;rw [← seteq] at bound;omega
theorem occurs {n : ℕ} {neigh : List Nat} {Good : Fin n→ Prop} {D : Dag}
    (hG : zc (z4 neigh) Good) (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (hz : qd n D = 0) (P : Finset (Fin n)) (hind : x0 neigh P)
    (i : Fin n) (hiG : Good i) (hi : i∈z1 n D) :
    qq n D P (z9 neigh P i):=by
  obtain ⟨j,s,_,_,_,ex⟩:=x1 hG h.1 hc P hind (xg hG h hc hz hiG hi)
  refine ⟨src D (j,s),?_⟩
  ext a
  simp only [mem_inter,z9,mem_filter]
  constructor
  · rintro ⟨ha,hin⟩;exact ⟨hin,(ex a hin).1 ha⟩
  · rintro ⟨hin,ha⟩;exact ⟨(ex a hin).2 ha,hin⟩
theorem z5l {n : ℕ} {neigh : List Nat} {Good : Fin n→ Prop} {D : Dag}
    (hG : zc (z4 neigh) Good) (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (ff : ∀ i j : Fin n,i≠j→ (z9 neigh Finset.univ i∩z9 neigh Finset.univ j).card≤ 1)
    (zero : qd n D = 0) (P I U W : Finset (Fin n)) (ind : x0 neigh P) (p7 : P.card≤ 7)
    (sub : I⊆z1 n D)
    (u : ∀ i∈U,i∈I∧Good i∧(z9 neigh P i).card = 3)
    (w : ∀ i∈W,i∈I∧Good i∧(z9 neigh P i).card = 2) :
    2 * U.card + W.card≤ (merges n D (zb n D P)).card:=by
  let f:=z9 neigh P
  have sep {i j : Fin n} (ne : i≠j) : (f i∩f j).card≤ 1:=z0q neigh ff P ne;have inj {T : Finset (Fin n)} (hi : ∀ i∈T,2≤ (f i).card) : Set.InjOn f T:=by
    intro i iT j _ eq
    by_contra ne
    have le:=sep ne;rw [← eq,inter_self] at le
    have:=hi i iT
    omega
  have uinj : Set.InjOn f U:=inj (fun i hi=>by have:=(u i hi).2.2;change 2≤ (z9 neigh P i).card;omega);have winj : Set.InjOn f W:=inj (fun i hi=>(w i hi).2.2.ge);have m:=z40 h.1 p7 (U.image f) (fun T ht=>by
    obtain ⟨i,hi,rfl⟩:=mem_image.mp ht;exact ⟨(u _ hi).2.2,occurs hG h hc zero P ind i (u _ hi).2.1 (sub (u _ hi).1)⟩)
    (fun T ht M hm diff=>by
      obtain ⟨i,hi,rfl⟩:=mem_image.mp ht;obtain ⟨j,hj,rfl⟩:=mem_image.mp hm;exact sep (fun e=>diff (congrArg f e)))
    (W.image f) (fun M hm=>by
      obtain ⟨i,hi,rfl⟩:=mem_image.mp hm;have c : (f i).card = 2:=(w i hi).2.2;have separate : ∀ j∈U,¬ f i⊆f j:=by
        intro j hj incl;have cj : (f j).card = 3:=(u j hj).2.2;have distinct : i≠j:=by rintro rfl;omega
        have v:=sep distinct;rw [inter_eq_left.mpr incl,c] at v;omega
      refine ⟨occurs hG h hc zero P ind i (w _ hi).2.1 (sub (w _ hi).1),by omega,?_,by omega,by omega,?_⟩
      · intro mem
        obtain ⟨j,hj,eq⟩:=mem_image.mp mem;exact separate j hj (by rw [eq])
      · intro _ T ht
        obtain ⟨j,hj,rfl⟩:=mem_image.mp ht;exact separate j hj)
  rw [card_image_of_injOn uinj,card_image_of_injOn winj] at m;exact m.trans (card_le_card (filter_subset _ _))
theorem z2w {n : ℕ} {neigh : List Nat} {Good : Fin n→ Prop} {D : Dag}
    (hG : zc (z4 neigh) Good) (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (hEl : ∀ v∈z6 n D,Good v)
    (ff : ∀ i j : Fin n,i≠j→ (z9 neigh Finset.univ i∩z9 neigh Finset.univ j).card≤ 1)
    {w0 : Nat} (hw0 : w0≠0→ ∃ w,2≤ zd D w∧supp n D w = (mask w0 : Finset (Fin n))∧2≤ (supp n D w).card)
    (zero : qd n D = 0) (P I U W J Q : Finset (Fin n)) (A : Fin n→ Finset (Fin n))
    (eq : I = z1 n D) (ind : x0 neigh P) (p7 : P.card≤ 7) (qs : Q⊆P)
    (u : ∀ i∈U,i∈I∧Good i∧(z9 neigh P i).card = 3)
    (w : ∀ i∈W,i∈I∧Good i∧(z9 neigh P i).card = 2)
    (j : ∀ i∈J,i∈I∧Good i∧(∃ a∈P,z4 neigh i a)∧∀ f∈Q,∃ a∈A f,z4 neigh i a)
    (free : ∀ f∈Q,x0 neigh (A f)∧P.erase f⊆A f∧∃ a∈A f,z4 neigh f a) :
    J.card + Q.card + 2 * U.card + W.card + (n - I.card) +
      (if w0≠0∧∀ x∈(mask w0 : Finset (Fin n)),x∉P then 1 else 0)≤
    P.card + (P \ I).card + zu n D:=by
  obtain ⟨b,hb⟩:=zz hG h.1 hc hEl;obtain ⟨pos,hpos⟩:=z3j hG h hc;have lo:=z5l hG h hc ff zero P I U W ind p7 (eq▸Finset.Subset.rfl) u w;have exits:=z2x hG h.1 hc pos P J Q qs A
    ⟨fun i hi=>⟨by
        obtain ⟨a,haP,hia⟩:=(j i hi).2.2.1;exact z3i hpos (eq▸(j i hi).1) (j i hi).2.1 hia haP,
      (hpos.1 i (eq▸(j i hi).1) (j i hi).2.1).2.2.1⟩,
     fun i hi i' hi' heq=>hpos.2 i (eq▸(j i hi).1) (j i hi).2.1 i' (eq▸(j i' hi').1) (j i' hi').2.1 heq⟩
    (fun i hi f hf=>(j i hi).2.2.2 f hf) free
  have fl:=ym h P (by rw [ye hG hc];simp);have card:=zm n D;have seteq : P \ I = P∩z6 n D:=by ext x;simp [eq,qt]
  rw [seteq,eq]
  by_cases hbon : w0≠0∧∀ x∈(mask w0 : Finset (Fin n)),x∉P
  · rw [if_pos hbon]
    obtain ⟨ww,hfw,hsw,hcw⟩:=hw0 hbon.1;have hdisj : Disjoint (mask w0 : Finset (Fin n)) P:=disjoint_left.mpr hbon.2;have sup:=w4 h.1 b hb hfw hcw P (hsw▸hdisj);omega
  · rw [if_neg hbon]
    have sup:=w5 h.1 b hb P;omega
theorem x5 {n : ℕ} {neigh : List Nat} {Good : Fin n→ Prop} {D : Dag}
    (hG : zc (z4 neigh) Good) (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (hEl : ∀ v∈z6 n D,Good v)
    (tight : zu n D≤ (z6 n D).card) : ∀ x : Fin n,(yl n D x).card≤ 2:=by
  obtain ⟨b,hb⟩:=zz hG h.1 hc hEl;have zero : z5 n D b = ∅:=by
    have:=card_residual h.1 b hb
    exact card_eq_zero.mp (by omega)
  intro x;have count:=vx hG h hc b hb x;have one:=card_le_card (inter_subset_left : ({x} : Finset (Fin n))∩z6 n D⊆{x});rw [zero] at count;simp only [filter_empty,card_empty,card_singleton] at count one;omega
theorem z6c {n m : ℕ} [NeZero n] {neigh : List Nat} {edges : List (Nat×Nat)}
    {Good : Fin n→ Prop} {D : Dag} {P : Fin m→ Slot}
    (hG : zc (z4 neigh) Good) (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (hp : z1c (n:=n) edges D P) (s : Bool) (a b : Fin m)
    (same : zh n edges s a.val = zh n edges s b.val)
    (hiG : Good (zh n edges s a.val)) (hi : zh n edges s a.val∈z1 n D) :
    P a = P b:=by
  obtain ⟨e,_,_,_,_,_,hw,_⟩:=ql hG h hc hiG hi;change yl n D (zh n edges s a.val) = {e} at hw;have ha:=hp s a;have hb:=hp s b;rw [← same] at hb;exact z0t s ((mem_singleton.mp (hw▸ha)).trans (mem_singleton.mp (hw▸hb)).symm)
theorem z69 {n m : ℕ} [NeZero n] {neigh : List Nat} {edges : List (Nat×Nat)}
    {Good : Fin n→ Prop} {D : Dag} {P : Fin m→ Slot}
    (hG : zc (z4 neigh) Good) (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (hp : z1c (n:=n) edges D P) (s : Bool) (a b : Fin m)
    (diff : zh n edges s a.val≠zh n edges s b.val)
    (hiG : Good (zh n edges s a.val)) (hi : zh n edges s a.val∈z1 n D) :
    P a≠P b:=by
  intro eq;have ha:=(qj.mp (hp s a)).2.1;have hb:=(qj.mp (hp s b)).2.1;rw [← eq] at hb;rw [we hG h.1 hc hiG hi ha,mem_singleton] at hb;exact diff hb.symm
theorem z5g {n m : ℕ} [NeZero n] {neigh : List Nat} {edges : List (Nat×Nat)}
    {Good : Fin n→ Prop} {D : Dag} {P : Fin m→ Slot} {v0 : Fin n}
    (hG : zc (z4 neigh) Good) (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (hp : z1c (n:=n) edges D P) (hv : v0∈z1 n D)
    (s : Bool) (a b : Fin m)
    (g : zh n edges s a.val = zh n edges s b.val∧
      Good (zh n edges s a.val)∧zh n edges s a.val = v0) :
    P a = P b:=z6c hG h hc hp s a b g.1 g.2.1 (g.2.2.symm▸hv)
theorem z5f {n m : ℕ} [NeZero n] {neigh : List Nat} {edges : List (Nat×Nat)}
    {Good : Fin n→ Prop} {D : Dag} {P : Fin m→ Slot} {v0 : Fin n}
    (hG : zc (z4 neigh) Good) (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (hp : z1c (n:=n) edges D P) (hv : v0∈z1 n D)
    (s : Bool) (a b : Fin m)
    (g : zh n edges s a.val≠zh n edges s b.val∧
      Good (zh n edges s a.val)∧zh n edges s a.val = v0) :
    P a≠P b:=z69 hG h hc hp s a b g.1 g.2.1 (g.2.2.symm▸hv)
theorem couple {n m : ℕ} [NeZero n] {edges : List (Nat×Nat)} {D : Dag} {P : Fin m→ Slot}
    (hp : z1c (n:=n) edges D P) (lim : ∀ x : Fin n,(yl n D x).card≤ 2)
    (s : Bool) (a b c : Fin m)
    (same : zh n edges s a.val = zh n edges s b.val∧
      zh n edges s a.val = zh n edges s c.val) :
    P a = P b∨P b = P c∨P a = P c:=by
  by_contra! ne
  have hb:=hp s b;have hc:=hp s c;rw [← same.1] at hb;rw [← same.2] at hc;have card:=two_lt_card.mpr ⟨_,hp s a,_,hb,_,hc,fun e=>ne.1 (z0t s e),
    fun e=>ne.2.2 (z0t s e),fun e=>ne.2.1 (z0t s e)⟩
  exact (Nat.not_lt_of_ge (lim _)) card
theorem yg {n m : ℕ} [NeZero n] {neigh : List Nat} {edges : List (Nat×Nat)}
    {Good : Fin n→ Prop} {D : Dag} {P : Fin m→ Slot}
    (hG : zc (z4 neigh) Good) (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (hp : z1c (n:=n) edges D P) (lim : ∀ x : Fin n,(yl n D x).card≤ 2)
    (s : Bool) (a b i j : Fin m) (q : Fin n)
    (geom : zh n edges s a.val = zh n edges s b.val∧
      ¬ z4 neigh (zh n edges s i.val) (zh n edges s j.val)∧
      z4 neigh (zh n edges s a.val) q∧
      ¬ z4 neigh q (zh n edges s i.val)∧
      ¬ z4 neigh q (zh n edges s j.val)) :
    P a = P b∨P a≠P i∨P b≠P j:=by
  by_contra! bad
  obtain ⟨sw,na,hq,ni,nj⟩:=geom;obtain ⟨e,he,no1,no2⟩:=z44 hG h.1 hc na hq ni nj;have mb:=hp s b;rw [← sw] at mb;have yi:=(qj.mp (hp s i)).2.1;have yj:=(qj.mp (hp s j)).2.1;rw [← bad.2.1] at yi;rw [← bad.2.2] at yj;have ne1 : flip s (P a)≠e:=fun eq=>no1 (eq▸yi)
  have ne2 : flip s (P b)≠e:=fun eq=>no2 (eq▸yj);have card:=two_lt_card.mpr ⟨_,hp s a,_,mb,e,he,fun eq=>bad.1 (z0t s eq),ne1,ne2⟩;exact (Nat.not_lt_of_ge (lim _)) card
def xd {n : ℕ} (neigh : List Nat) (D : Dag) (P : Finset (Fin n)) (i : Fin n) : Prop:=
  ∀ x∈P,z4 neigh i x→ ∃ e∈yl n D x,∀ a∈P,a∈supp n D (src D e)↔z4 neigh i a
theorem wy {n : ℕ} {neigh : List Nat} {Good : Fin n→ Prop} {D : Dag}
    (hG : zc (z4 neigh) Good) (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (z : qd n D = 0) (P : Finset (Fin n)) (ind : x0 neigh P)
    (i : Fin n) (hiG : Good i) (hi : i∈z1 n D) : xd neigh D P i:=by
  intro x xin ix;obtain ⟨j,s,hj,ht,ch,ex⟩:=x1 hG h.1 hc P ind (xg hG h hc z hiG hi)
  refine ⟨(j,s),qj.mpr ⟨hj,(ex _ xin).2 ix,?_⟩,ex⟩
  intro hx;have pure:=ys hG h.1 hc i hiG _ (qk h.1 ch);have eq:=mem_singleton.mp (pure (qg h.1 hj ht (!s) hx));exact hG.2.1 i (eq▸ix)
def z00 {n : ℕ} (D : Dag) (x c : Fin n) : Prop:=
  ∃ e∈yl n D x,∃ f∈yl n D x,e≠f∧c∉supp n D (src D e)∧c∉supp n D (src D f)
theorem z3v {n : ℕ} {neigh : List Nat} {D : Dag}
    (P : Finset (Fin n)) (i j x c y : Fin n)
    (hi : xd neigh D P i) (hj : xd neigh D P j)
    (g : x∈P∧c∈P∧y∈P∧z4 neigh i x∧z4 neigh j x∧
      ¬ z4 neigh i c∧¬ z4 neigh j c∧z4 neigh i y∧¬ z4 neigh j y) :
    z00 D x c:=by
  rcases g with ⟨xp,cp,yp,ix,jx,ic,jc,iy,jy⟩
  obtain ⟨e,he,E⟩:=hi x xp ix;obtain ⟨f,hf,F⟩:=hj x xp jx
  refine ⟨e,he,f,hf,?_,fun q=>ic ((E _ cp).1 q),fun q=>jc ((F _ cp).1 q)⟩
  rintro rfl;exact jy ((F _ yp).1 ((E _ yp).2 iy))
theorem z2o {n : ℕ} {neigh : List Nat} {Good : Fin n→ Prop} {D : Dag}
    (hG : zc (z4 neigh) Good) (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (P A : Finset (Fin n)) (indA : x0 neigh A) (i x c : Fin n)
    (hi : xd neigh D P i)
    (g : x∈P∧c∈P∧c∈A∧z4 neigh i x∧¬ z4 neigh i c∧
      (∃ a∈A,z4 neigh x a)∧∃ y∈P,y∈A∧z4 neigh i y) :
    z00 D x c:=by
  rcases g with ⟨xp,cp,ca,ix,ic,xa,y,yp,ya,iy⟩
  obtain ⟨e,he,E⟩:=hi x xp ix;obtain ⟨j,s,js,_,xs,no,free⟩:=x7 hG h.1 hc A indA x xa
  refine ⟨e,he,(j,s),qj.mpr ⟨js,xs,no⟩,?_,
    fun q=>ic ((E _ cp).1 q),fun q=>disjoint_left.mp free q ca⟩
  rintro rfl;exact disjoint_left.mp free ((E _ yp).2 iy) ya
def code {n k : ℕ} {D : Dag} {b : Fin n→ Nat}
    (f : Fin k≃↥(z5 n D b)) (x : Fin n) : Finset (Fin k):=
  Finset.univ.filter (fun t=>x∈supp n D (f t).val.1)
theorem z4u {n k : ℕ} {neigh : List Nat} {Good : Fin n→ Prop} {D : Dag}
    (hG : zc (z4 neigh) Good) (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (b : Fin n→ Nat) (hb : qe n D b) (f : Fin k≃↥(z5 n D b)) (x c : Fin n)
    (hxG : Good x) (ne : x≠c) (elig : x∈z6 n D) (miss : z00 D x c)
    (together : ∃ w,x∈supp n D w∧c∈supp n D w) : ¬ code f x⊆code f c:=by
  intro sub;obtain ⟨w,xw,cw⟩:=together;have incl (u) (hu : u∈z5 n D b) (xu : x∈supp n D u.1) : c∈supp n D u.1:=by
    obtain ⟨t,eq⟩:=f.surjective ⟨u,hu⟩;have xt : t∈code f x:=mem_filter.mpr ⟨mem_univ _,by simpa [eq] using xu⟩
    simpa [eq] using (mem_filter.mp (sub xt)).2
  obtain ⟨e0,other⟩:=z6d hG h hc b hb hxG ne elig incl (w:=w) ⟨xw,cw⟩;obtain ⟨p,hp,q,hq,pq,mp,mq⟩:=miss
  by_cases ep : p = e0
  · exact mq (other q hq (by rintro rfl;exact pq ep))
  · exact mp (other p hp ep)
theorem z4s {n k : ℕ} {neigh : List Nat} {Good : Fin n→ Prop} {D : Dag}
    (hG : zc (z4 neigh) Good) (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (b : Fin n→ Nat) (hb : qe n D b) (f : Fin k≃↥(z5 n D b)) (x c : Fin n)
    (hxG : Good x) (ne : x≠c) (elig : x∈z6 n D) (miss : z00 D x c) :
    code f x = ∅∨¬ code f x⊆code f c:=by
  by_cases empty : code f x = ∅
  · exact Or.inl empty
  · right;intro sub
    obtain ⟨t,xt⟩:=nonempty_iff_ne_empty.mpr empty;exact z4u hG h hc b hb f x c hxG ne elig miss
      ⟨_,(mem_filter.mp xt).2,(mem_filter.mp (sub xt)).2⟩ sub
theorem z4r {n k : ℕ} {D : Dag} {b : Fin n→ Nat}
    (hS : za n D) (hb : qe n D b) (hrc : (z5 n D b).card = k)
    {w : ℕ} {S : Finset (Fin n)} (hfw : 2≤ zd D w) (hsw : supp n D w = S) (hcw : 2≤ S.card) :
    ∃ (h0 : 0 < k) (f : Fin k≃↥(z5 n D b)),
      ∀ x : Fin n,⟨0,h0⟩∈code f x↔x∈S:=by
  classical
  let u0 : ↥(z5 n D b):=⟨⟨w,0⟩,y6 hS b hb hfw (hsw▸hcw)⟩
  have h0 : 0 < k:=by
    have hp : 0 < (z5 n D b).card:=card_pos.mpr ⟨u0.val,u0.property⟩;omega
  have count : Fintype.card ↥(z5 n D b) = k:=by rw [Fintype.card_coe];exact hrc
  let f0 : Fin k≃↥(z5 n D b):=(Fintype.equivFinOfCardEq count).symm
  let idx0 : Fin k:=f0.symm u0
  let f : Fin k≃↥(z5 n D b):=(Equiv.swap ⟨0,h0⟩ idx0).trans f0
  refine ⟨h0,f,fun x=>?_⟩
  simp only [code,mem_filter,mem_univ,true_and];have hf0 : f ⟨0,h0⟩ = u0:=by
    dsimp only [f,Equiv.trans_apply];rw [Equiv.swap_apply_left,Equiv.apply_symm_apply]
  rw [hf0];change x∈supp n D w↔x∈S;rw [hsw]
noncomputable def qz {n k : ℕ} {D : Dag} {b : Fin n→ Nat}
    (f : Fin k≃↥(z5 n D b)) (v : Fin n) : Fin (2 ^ k):=
  (repr k (code f v)).choose
theorem mask_codeMask {n k : ℕ} {D : Dag} {b : Fin n→ Nat}
    (f : Fin k≃↥(z5 n D b)) (v : Fin n) :
    (mask (qz f v).val : Finset (Fin k)) = code f v:=
  (repr k (code f v)).choose_spec
theorem z30 {n k : ℕ} {D : Dag} {b : Fin n→ Nat}
    (f : Fin k≃↥(z5 n D b)) {x c : Fin n}
    (h : ¬ code f x⊆code f c) :
    ((qz f x).val &&& (qz f c).val)≠(qz f x).val:=by
  intro heq;apply h;rw [← mask_codeMask f x,← mask_codeMask f c];exact z5j _ _ heq
theorem z4t {n k : ℕ} {D : Dag} {b : Fin n→ Nat}
    (f : Fin k≃↥(z5 n D b)) {x c : Fin n}
    (h : code f x = ∅∨¬ code f x⊆code f c) :
    (qz f x).val = 0∨((qz f x).val &&& (qz f c).val)≠(qz f x).val:=by
  rcases h with hemp | hns
  · left;by_contra hne
    have hlt:=(qz f x).2;have hne' : (mask (qz f x).val : Finset (Fin k))≠∅:=by
      intro he;apply hne;apply Nat.eq_of_testBit_eq;intro i;simp only [Nat.zero_testBit]
      by_cases hi : i < k
      · have hmem : (⟨i,hi⟩ : Fin k)∉(mask (qz f x).val : Finset (Fin k)):=by rw [he];simp
        simpa [mask] using hmem
      · exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega)))
    exact hne' ((mask_codeMask f x).trans hemp)
  · right;exact z30 f hns
theorem z2c {n k : ℕ} {D : Dag} {b : Fin n→ Nat}
    (f : Fin (k + 1)≃↥(z5 n D b)) (v : Fin n) :
    (qz f v).val.testBit 0 = true↔(0 : Fin (k + 1))∈code f v:=by
  rw [← mask_codeMask f v];simp [mask]
theorem z3d {k : ℕ} (m : Fin (2 ^ (k + 1))) (b : Bool) (hb : m.val.testBit 0 = b) :
    2 * (m.val / 2) + (if b then 1 else 0) = m.val:=by
  rw [Nat.testBit_zero] at hb
  cases b <;> simp at hb ⊢ <;> omega
theorem z3e {n : ℕ} {D : Dag} {I : Nat} {x : Fin n}
    (eq : (mask I : Finset (Fin n)) = z1 n D) (hx : x∉(mask I : Finset (Fin n))) :
    x∈z6 n D:=by
  by_contra hne;exact hx (eq▸qt.mpr hne)
def z1m (wf : Nat→ Nat) : Nat→ Nat→ List Nat→ List Nat
  | 0,_,acc=>acc.reverse
  | n + 1,x,acc=>
    let w:=wf x
    z1m wf n (x >>> w) ((x &&& ((1 <<< w) - 1)) :: acc)
def zg (wf : Nat→ Nat) (cs : List Nat) : List Nat:=
  cs.flatMap (fun x=>z1m wf (x &&& 63) (x >>> 6) [])
def zj (wf : Nat→ Nat) (cs : List Nat) : Array (List Nat):=
  (cs.map (fun x=>z1m wf (x &&& 63) (x >>> 6) [])).toArray
abbrev xe:=Nat×Nat×Nat×Nat×Nat×Nat×Nat×Nat×Nat
def z5y (n : Nat) (neigh : List Nat) (M : Nat) : Bool:=
  (List.range n).all fun u=>!M.testBit u ||
    (List.range n).all fun v=>!M.testBit v || !(neigh.getD u 0).testBit v
theorem z1j {n : Nat} {neigh : List Nat} {M : Nat} (h : z5y n neigh M = true) :
    x0 neigh (mask M : Finset (Fin n)):=by
  intro u hu v hv huv;simp only [mask,mem_filter,mem_univ,true_and] at hu hv;have h1:=List.all_eq_true.mp h u.val (List.mem_range.mpr u.isLt);simp only [hu,Bool.not_true,Bool.false_or] at h1;have h2:=List.all_eq_true.mp h1 v.val (List.mem_range.mpr v.isLt)
  simp only [hv,Bool.not_true,Bool.false_or,Bool.not_eq_true'] at h2;unfold z4 at huv;rw [h2] at huv;exact Bool.false_ne_true huv
def yh (n : Nat) (neigh : List Nat) (goodMask I drop : Nat) (vars : List Nat) (s : xe) : Bool:=
  let (kind,P,A,i,j,x,c,y,si):=s
  let adjB (u v : Nat):=(neigh.getD u 0).testBit v
  i < n && j < n && x < n && c < n && y < n && si < n &&
  x != c && goodMask.testBit x && !I.testBit x && vars.contains x && vars.contains c &&
  z5y n neigh P && goodMask.testBit i && I.testBit i &&
  (drop == 0 || (P == 63 && !drop.testBit i)) &&
  (if kind < 2 then
    z5y n neigh A && P.testBit x && P.testBit c && A.testBit c &&
    adjB i x && !adjB i c &&
    (List.range n).any (fun a=>A.testBit a && adjB x a) &&
    (List.range n).any (fun y0=>P.testBit y0 && A.testBit y0 && adjB i y0)
   else
    goodMask.testBit j && I.testBit j &&
    (drop == 0 || (P == 63 && !drop.testBit j)) &&
    P.testBit x && P.testBit c && P.testBit y &&
    adjB i x && adjB j x && !adjB i c && !adjB j c && adjB i y && !adjB j y) &&
  (if kind == 0 || kind == 2 then
    goodMask.testBit si && I.testBit si && adjB si x && adjB si c
   else true)
def yx (env : Nat→ Nat) (s : xe) : Bool:=
  let (kind,_,_,_,_,x,c,_,_):=s
  let ax:=env x
  let ac:=env c
  if kind == 0 || kind == 2 then (ax &&& ac) != ax
  else (ax == 0) || ((ax &&& ac) != ax)
def yk (dom w0 : Nat) : List Nat→ (Nat→ Nat)→ List xe→ Bool
  | [],env,steps=>!(steps.all fun s=>yx env s)
  | v :: vs,env,steps=>
    (List.range dom).all fun t=>
      let mv:=if w0 == 0 then t else 2 * t + (if w0.testBit v then 1 else 0)
      yk dom w0 vs (fun u=>if u == v then mv else env u) steps
theorem z1k {dom w0 : Nat} (vars : List Nat) (env0 real : Nat→ Nat) (steps : List xe)
    (hOk : yk dom w0 vars env0 steps = true)
    (hReal : ∀ v∈vars,∃ t < dom,real v = if w0 == 0 then t else 2 * t + (if w0.testBit v then 1 else 0))
    (hExt : ∀ v,v∉vars→ env0 v = real v)
    (hSteps : ∀ s∈steps,yx real s = true) : False:=by
  induction vars generalizing env0 with
  | nil=>
    have heq : env0 = real:=funext fun v=>hExt v (by simp);have hall : steps.all (fun s=>yx env0 s) = true:=
      List.all_eq_true.mpr (fun s hs=>by rw [heq];exact hSteps s hs)
    simp [yk,hall] at hOk
  | cons v vs ih=>
    obtain ⟨t,ht,hrt⟩:=hReal v List.mem_cons_self;have hOk':=List.all_eq_true.mp hOk t (List.mem_range.mpr ht)
    refine ih _ hOk' (fun u hu=>hReal u (List.mem_cons_of_mem _ hu)) (fun u hu=>?_)
    by_cases huv : u = v
    · subst huv;simp [hrt]
    · simp only [beq_iff_eq,huv,ite_false]
      exact hExt u (by simp [huv,hu])
theorem z21 {n k : ℕ} {neigh : List Nat} {Good : Fin n→ Prop} {D : Dag}
    (hG : zc (z4 neigh) Good) (h : z0 n D) (hc : z3 n (z4 neigh) D)
    {b : Fin n→ Nat} (hb : qe n D b) (f : Fin k≃↥(z5 n D b))
    {goodMask I drop : Nat} (hGood : ∀ v : Fin n,goodMask.testBit v.val = true→ Good v)
    (eq : (mask I : Finset (Fin n)) = z1 n D)
    (hEx : ∀ P : Nat,x0 neigh (mask P : Finset (Fin n))→ ∀ i : Fin n,i∈(mask I : Finset (Fin n))→
      goodMask.testBit i.val = true→ (drop == 0 || (P == 63 && !drop.testBit i.val)) = true→ xd neigh D (mask P) i)
    (vars : List Nat) (s : xe) (hGeo : yh n neigh goodMask I drop vars s = true) :
    yx (fun v=>if hv : v < n then (qz f ⟨v,hv⟩).val else 0) s = true:=by
  rcases s with ⟨kind,P,A,i,j,x,c,y,si⟩
  simp only [yh,Bool.and_eq_true,bne_iff_ne,ne_eq,decide_eq_true_eq,
    Bool.not_eq_true',List.contains_iff_mem] at hGeo
  rcases hGeo with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hi,hj⟩,hx⟩,hc'⟩,hy⟩,hsi⟩,hxc⟩,hgx⟩,hnxI⟩,_⟩,_⟩,hPind⟩,hgi⟩,hiI⟩,hdropi⟩,hmiss⟩,hsh⟩
  let fi : Fin n:=⟨i,hi⟩;let fj : Fin n:=⟨j,hj⟩;let fx : Fin n:=⟨x,hx⟩
  let fc : Fin n:=⟨c,hc'⟩;let fy : Fin n:=⟨y,hy⟩;let fsi : Fin n:=⟨si,hsi⟩
  have hPi : x0 neigh (mask P : Finset (Fin n)):=z1j hPind;have hexI : xd neigh D (mask P) fi:=hEx P hPi fi (by simp [mask,fi,hiI]) hgi hdropi;have hM : z00 D fx fc:=by
    by_cases hk : kind < 2
    · simp only [hk,ite_true,Bool.and_eq_true,Bool.not_eq_true',List.any_eq_true,List.mem_range] at hmiss
      rcases hmiss with ⟨⟨⟨⟨⟨⟨⟨hAind,hPx⟩,hPc⟩,hAc⟩,hix⟩,hnic⟩,⟨a,ha,hAa,hxa⟩⟩,⟨y0,hy0,⟨hPy0,hAy0⟩,hiy0⟩⟩
      exact z2o hG h hc (mask P) (mask A) (z1j hAind) fi fx fc hexI
        ⟨by simp [mask,fx,hPx],by simp [mask,fc,hPc],by simp [mask,fc,hAc],
         hix,fun hbad=>Bool.false_ne_true (hnic▸hbad),
         ⟨⟨a,ha⟩,by simp [mask,hAa],hxa⟩,⟨⟨y0,hy0⟩,by simp [mask,hPy0],by simp [mask,hAy0],hiy0⟩⟩
    · simp only [hk,ite_false,Bool.and_eq_true,Bool.not_eq_true'] at hmiss
      rcases hmiss with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hgj,hjI⟩,hdropj⟩,hPx⟩,hPc⟩,hPy⟩,hix⟩,hjx⟩,hnic⟩,hnjc⟩,hiy⟩,hnjy⟩
      have hexJ : xd neigh D (mask P) fj:=hEx P hPi fj (by simp [mask,fj,hjI]) hgj hdropj;exact z3v (mask P) fi fj fx fc fy hexI hexJ
        ⟨by simp [mask,fx,hPx],by simp [mask,fc,hPc],by simp [mask,fy,hPy],hix,hjx,
         fun hbad=>Bool.false_ne_true (hnic▸hbad),fun hbad=>Bool.false_ne_true (hnjc▸hbad),
         hiy,fun hbad=>Bool.false_ne_true (hnjy▸hbad)⟩
  have hElx : fx∈z6 n D:=z3e eq (by simp [mask,fx,hnxI]);have hfxc : fx≠fc:=fun e=>hxc (congrArg Fin.val e);simp only [yx,dif_pos hx,dif_pos hc']
  by_cases htg : (kind == 0 || kind == 2) = true
  · simp only [htg,ite_true,Bool.and_eq_true] at hsh ⊢
    rcases hsh with ⟨⟨⟨hgsi,hsiI⟩,hsix⟩,hsic⟩
    have hsub:=z30 f (z4u hG h hc b hb f fx fc (hGood fx hgx) hfxc hElx hM
      (share hG h hc (hGood fsi hgsi) (eq▸by simp [mask,fsi,hsiI]) hsix hsic))
    simpa [bne_iff_ne] using hsub
  · simp only [htg,Bool.false_eq_true,ite_false,Bool.or_eq_true,beq_iff_eq,bne_iff_ne]
    exact z4t f (z4s hG h hc b hb f fx fc (hGood fx hgx) hfxc hElx hM)
theorem xc {n k w0 goodMask I drop bpVal : ℕ} {neigh : List Nat} {Good : Fin n→ Prop} {D : Dag}
    (hG : zc (z4 neigh) Good) (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (hEl : ∀ v∈z6 n D,Good v)
    (hGood : ∀ v : Fin n,goodMask.testBit v.val = true→ Good v)
    (bp : zu n D = bpVal) (eq : (mask I : Finset (Fin n)) = z1 n D)
    (hcard : (mask I : Finset (Fin n)).card + bpVal = n + k)
    (hw0 : w0≠0→ ∃ w,2≤ zd D w∧supp n D w = (mask w0 : Finset (Fin n))∧2≤ (supp n D w).card)
    (hEx : ∀ P : Nat,x0 neigh (mask P : Finset (Fin n))→ ∀ i : Fin n,i∈(mask I : Finset (Fin n))→
      goodMask.testBit i.val = true→ (drop == 0 || (P == 63 && !drop.testBit i.val)) = true→ xd neigh D (mask P) i)
    (vars : List Nat) (steps : List xe)
    (hAll : vars.all (fun v=>decide (v < n)) = true∧
      steps.all (yh n neigh goodMask I drop vars) = true∧
      yk (if w0 == 0 then 2 ^ k else 2 ^ (k - 1)) w0 vars (fun _=>0) steps = true) :
    False:=by
  obtain ⟨b,hb⟩:=zz hG h.1 hc hEl;have hcr:=card_residual h.1 b hb;have hel:=zm n D;rw [← eq] at hel;have hrc : (z5 n D b).card = k:=by omega
  have hVarsLt : ∀ v∈vars,v < n:=fun v hv=>decide_eq_true_eq.mp (List.all_eq_true.mp hAll.1 v hv);have hStepVars : ∀ s∈steps,s.2.2.2.2.2.1∈vars∧s.2.2.2.2.2.2.1∈vars:=by
    intro s hs;have hg:=List.all_eq_true.mp hAll.2.1 s hs
    rcases s with ⟨kind,P,A,i,j,x,c,y,si⟩
    simp only [yh,Bool.and_eq_true,List.contains_iff_mem] at hg;exact ⟨hg.1.1.1.1.1.1.1.2,hg.1.1.1.1.1.1.2⟩
  by_cases hw : w0 = 0
  · subst hw
    let f : Fin k≃↥(z5 n D b):=
      (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe];exact hrc)).symm
    let real (v : Nat) : Nat:=if hv : v < n then (qz f ⟨v,hv⟩).val else 0
    let real' (v : Nat) : Nat:=if v∈vars then real v else 0
    have hOk:=hAll.2.2;simp only [beq_self_eq_true,ite_true] at hOk
    refine z1k vars (fun _=>0) real' steps hOk (fun v hv=>?_) (fun v hv=>by simp [real',hv]) (fun s hs=>?_)
    · have hvn:=hVarsLt v hv
      refine ⟨(qz f ⟨v,hvn⟩).val,(qz f ⟨v,hvn⟩).2,?_⟩
      simp [real',real,hv,hvn]
    · have hst:=z21 hG h hc hb f hGood eq hEx vars s (List.all_eq_true.mp hAll.2.1 s hs)
      obtain ⟨hx,hc'⟩:=hStepVars s hs
      rcases s with ⟨kind,P,A,i,j,x,c,y,si⟩
      simp only [yx,real',if_pos hx,if_pos hc'];exact hst
  · obtain ⟨w,hfw,hsw,hcw⟩:=hw0 hw
    obtain ⟨h0,f,hf0⟩:=z4r h.1 hb hrc hfw hsw (hsw▸hcw);obtain ⟨k',rfl⟩ : ∃ k',k = k' + 1:=⟨k - 1,by omega⟩
    let real (v : Nat) : Nat:=if hv : v < n then (qz f ⟨v,hv⟩).val else 0
    let real' (v : Nat) : Nat:=if v∈vars then real v else 0
    have hOk:=hAll.2.2;have hwnz : (w0 == 0) = false:=beq_false_of_ne hw;simp only [hwnz,Bool.false_eq_true,ite_false,Nat.add_sub_cancel] at hOk
    refine z1k vars (fun _=>0) real' steps hOk (fun v hv=>?_) (fun v hv=>by simp [real',hv]) (fun s hs=>?_)
    · have hvn:=hVarsLt v hv
      let fv : Fin n:=⟨v,hvn⟩
      refine ⟨(qz f fv).val / 2,by have:=(qz f fv).2;omega,?_⟩
      simp only [real',real,hv,hvn,ite_true,dif_pos,hwnz,Bool.false_eq_true,ite_false];have hbit : (qz f fv).val.testBit 0 = w0.testBit v:=by
        cases htb : w0.testBit v
        · exact Bool.eq_false_iff.mpr fun ht=>by
            have hm:=(hf0 fv).mp ((z2c f fv).mp ht);simp only [mask,mem_filter,mem_univ,true_and,fv,htb] at hm;exact Bool.false_ne_true hm
        · exact (z2c f fv).mpr ((hf0 fv).mpr (by simp [mask,fv,htb]))
      exact (z3d (qz f fv) (w0.testBit v) hbit).symm
    · have hst:=z21 hG h hc hb f hGood eq hEx vars s (List.all_eq_true.mp hAll.2.1 s hs)
      obtain ⟨hx,hc'⟩:=hStepVars s hs
      rcases s with ⟨kind,P,A,i,j,x,c,y,si⟩
      simp only [yx,real',if_pos hx,if_pos hc'];exact hst
theorem zp {n : ℕ} (σ : Equiv.Perm (Fin n)) (m1 m2 : Nat)
    (h : ∀ i : Fin n,m1.testBit i.val = m2.testBit (σ i).val) :
    (mask m1 : Finset (Fin n)).image σ = mask m2:=by
  ext y
  simp only [mem_image,mask,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨x,hx,rfl⟩;rwa [← h x]
  · intro hy;exact ⟨σ⁻¹ y,by rw [h];simpa using hy,by simp⟩
def auto {n : ℕ} (neigh : List Nat) (σ : Equiv.Perm (Fin n)) : Prop:=
  ∀ i j : Fin n,z4 neigh (σ i) (σ j)↔z4 neigh i j
theorem z3a {n : ℕ} {neigh : List Nat} {D : Dag} (h : z0 n D)
    (σ : Equiv.Perm (Fin n)) (ha : auto neigh σ) {P : Finset (Fin n)} (hP : P.image σ = P)
    {i : Fin n} (hex : xd neigh D P (σ⁻¹ i)) :
    xd neigh (z7 σ D) P i:=by
  intro x hxP hix;have hx1 : σ⁻¹ x∈P:=by
    have:=hP.symm▸hxP
    obtain ⟨u,hu,hu2⟩:=mem_image.mp this;have : u = σ⁻¹ x:=by rw [← hu2];simp
    exact this▸hu
  obtain ⟨e,he,hE⟩:=hex (σ⁻¹ x) hx1 ((ha (σ⁻¹ i) (σ⁻¹ x)).1 (by simpa using hix));obtain ⟨he1,he2,he3⟩:=qj.mp he;have hsrc : src (z7 σ D) e = y3 σ (src D e):=by
    rcases e with ⟨j,s⟩;cases s <;> simp [src,z50 σ D j he1,z4z σ D j he1]
  have hgate : n + e.1 = y3 σ (n + e.1):=(x4 σ (by omega)).symm;have heW : e∈yl n (z7 σ D) x:=by
    refine qj.mpr ⟨by rw [q8];exact he1,
      by rw [hsrc,y7 σ h.1];exact mem_image.mpr ⟨σ⁻¹ x,he2,by simp⟩,?_⟩
    intro hbad;rw [hgate,y7 σ h.1,mem_image] at hbad;obtain ⟨u,hu,hu2⟩:=hbad;have huq : u = σ⁻¹ x:=by rw [← hu2];simp
    exact he3 (huq▸hu)
  refine ⟨e,heW,fun a haP=>?_⟩
  have ha1 : σ⁻¹ a∈P:=by
    have:=hP.symm▸haP
    obtain ⟨u,hu,hu2⟩:=mem_image.mp this;have : u = σ⁻¹ a:=by rw [← hu2];simp
    exact this▸hu
  rw [hsrc,y7 σ h.1,mem_image]
  constructor
  · rintro ⟨u,hu,rfl⟩;have:=(ha (σ⁻¹ i) u).2 ((hE u (by simpa using ha1)).1 hu);simpa using this
  · intro hia;exact ⟨σ⁻¹ a,(hE _ ha1).2 ((ha (σ⁻¹ i) (σ⁻¹ a)).1 (by simpa using hia)),by simp⟩
theorem rename {n : ℕ} {neigh : List Nat} {D : Dag}
    (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (σ : Equiv.Perm (Fin n)) (a : auto neigh σ) :
    z3 n (z4 neigh) (z7 σ D):=by
  intro x;rw [z5d σ h.1 h.2.2,hc]
  constructor
  · rintro ⟨u,v,uv,hu,hv⟩;exact ⟨σ u,σ v,(a _ _).2 uv,hu,hv⟩
  · rintro ⟨u,v,uv,hu,hv⟩
    refine ⟨σ.symm u,σ.symm v,(a _ _).1 (by simpa using uv),by simpa using hu,by simpa using hv⟩
theorem wv {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : za n D) (hne : D≠[])
    (P : Finset (Fin n)→ Prop) [DecidablePred P] (hP : ∀ S : Finset (Fin n),P (S.image σ)↔P S) :
    zw (z7 σ D) ((inner n (z7 σ D)).filter (fun w=>P (supp n (z7 σ D) w))) =
    zw D ((inner n D).filter (fun w=>P (supp n D w))):=by
  have hpos : 0 < D.length:=List.length_pos_iff.mpr hne;have hle : n≤ n + D.length - 1:=by omega
  unfold zw
  refine Finset.sum_nbij' (y3 σ⁻¹) (y3 σ) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    simp only [mem_filter,qm,q8] at hw ⊢
    refine ⟨by have:=(y4 σ⁻¹ hle w).mpr (by omega);omega,?_⟩
    have hs:=y7 σ hS (y3 σ⁻¹ w);rw [tr_liftP_inv' σ w] at hs;exact (hP _).mp (hs▸hw.2)
  · intro w hw
    simp only [mem_filter,qm,q8] at hw ⊢
    refine ⟨by have:=(y4 σ hle w).mpr (by omega);omega,?_⟩
    rw [y7 σ hS w];exact (hP _).mpr hw.2
  · intro w _;exact tr_liftP_inv' σ w
  · intro w _;simpa using tr_liftP_inv' σ⁻¹ w
  · intro w _
    have:=xn σ D (y3 σ⁻¹ w)
    rw [tr_liftP_inv' σ w] at this;rw [this]
theorem z4o {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : za n D) (hne : D≠[]) :
    zu n (z7 σ D) = zu n D:=by
  classical
  exact wv σ hS hne (fun S=>S.Nonempty) (fun S=>image_nonempty)
theorem z4n {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : za n D) (hne : D≠[]) :
    qd n (z7 σ D) = qd n D:=by
  classical
  exact wv σ hS hne (fun S=>¬ S.Nonempty) (fun S=>by simp [image_nonempty])
def mkPerm {n : ℕ} [NeZero n] (f g : List Nat)
    (hl : ∀ x : Fin n,Fin.ofNat n (g.getD (Fin.ofNat n (f.getD x.val 0)).val 0) = x)
    (hr : ∀ x : Fin n,Fin.ofNat n (f.getD (Fin.ofNat n (g.getD x.val 0)).val 0) = x) :
    Equiv.Perm (Fin n) where
  toFun x:=Fin.ofNat n (f.getD x.val 0)
  invFun x:=Fin.ofNat n (g.getD x.val 0)
  left_inv:=hl
  right_inv:=hr
def wd (n : Nat) (neigh : List Nat) (fg : List Nat×List Nat) : Bool:=
  let (f,g):=fg
  (List.range n).all (fun x=>
    decide (f.getD x 0 < n) && decide (g.getD x 0 < n) &&
    g.getD (f.getD x 0) 0 == x && f.getD (g.getD x 0) 0 == x) &&
  (List.range n).all (fun i=>(List.range n).all fun j=>
    (neigh.getD (f.getD i 0) 0).testBit (f.getD j 0) == (neigh.getD i 0).testBit j)
theorem wk {α : Type} {p : α→ Bool} {l : List α} {d : α}
    (h : l.all p = true) (hne : l≠[]) (k : Nat) : p (l.getD k (l.getD 0 d)) = true:=by
  have h0 : 0 < l.length:=List.length_pos_iff.mpr hne
  by_cases hk : k < l.length
  · rw [List.getD_eq_getElem _ _ hk];exact List.all_eq_true.mp h _ (List.getElem_mem hk)
  · rw [List.getD_eq_getElem?_getD,List.getElem?_eq_none (Nat.le_of_not_lt hk),Option.getD_none,
        List.getD_eq_getElem _ _ h0];exact List.all_eq_true.mp h _ (List.getElem_mem h0)
def z3b {n : ℕ} [NeZero n] {neigh : List Nat} (fg : List Nat×List Nat)
    (h : wd n neigh fg = true) : Equiv.Perm (Fin n):=
  mkPerm fg.1 fg.2
    (fun x=>by
      have hx:=List.all_eq_true.mp (Bool.and_eq_true _ _ |>.mp h).1 x.val (List.mem_range.mpr x.isLt);simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at hx
      apply Fin.ext;simp only [Fin.val_ofNat,Nat.mod_eq_of_lt hx.1.1.1,hx.1.2,Nat.mod_eq_of_lt x.isLt])
    (fun x=>by
      have hx:=List.all_eq_true.mp (Bool.and_eq_true _ _ |>.mp h).1 x.val (List.mem_range.mpr x.isLt);simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at hx
      apply Fin.ext;simp only [Fin.val_ofNat,Nat.mod_eq_of_lt hx.1.1.2,hx.2,Nat.mod_eq_of_lt x.isLt])
theorem z0e {n : ℕ} [NeZero n] {neigh : List Nat} (fg : List Nat×List Nat)
    (h : wd n neigh fg = true) (i : Fin n) : (z3b fg h i).val = fg.1.getD i.val 0:=by
  have hi:=List.all_eq_true.mp (Bool.and_eq_true _ _ |>.mp h).1 i.val (List.mem_range.mpr i.isLt);simp only [Bool.and_eq_true,decide_eq_true_eq] at hi;change (Fin.ofNat n (fg.1.getD i.val 0)).val = _;simp only [Fin.val_ofNat,Nat.mod_eq_of_lt hi.1.1.1]
theorem z4b {n : ℕ} [NeZero n] {neigh : List Nat} (fg : List Nat×List Nat)
    (h : wd n neigh fg = true) : auto neigh (z3b fg h):=by
  intro i j;have hij:=List.all_eq_true.mp (List.all_eq_true.mp (Bool.and_eq_true _ _ |>.mp h).2 i.val (List.mem_range.mpr i.isLt)) j.val (List.mem_range.mpr j.isLt);simp only [z4,z0e fg h i,z0e fg h j,beq_iff_eq.mp hij]
def va {n : ℕ} [NeZero n] {neigh : List Nat} (ps : List (List Nat×List Nat))
    (hps : ps.all (wd n neigh) = true) (hne : ps≠[]) (k : Nat) : Equiv.Perm (Fin n):=
  z3b (ps.getD k (ps.getD 0 ([],[]))) (wk hps hne k)
theorem z1b {n : ℕ} [NeZero n] {neigh : List Nat} (ps : List (List Nat×List Nat))
    (hps : ps.all (wd n neigh) = true) (hne : ps≠[]) (k : Nat) :
    auto neigh (va ps hps hne k):=
  z4b _ _
theorem z06 {n : ℕ} [NeZero n] {neigh : List Nat} (ps : List (List Nat×List Nat))
    (hps : ps.all (wd n neigh) = true) (hne : ps≠[]) (k : Nat) (i : Fin n) :
    (va ps hps hne k i).val = (ps.getD k (ps.getD 0 ([],[]))).1.getD i.val 0:=
  z0e _ _ i
theorem qu {n : ℕ} {neigh : List Nat} {D : Dag}
    (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (σ : Equiv.Perm (Fin n)) (a : auto neigh σ) :
    z0 n (z7 σ D)∧z3 n (z4 neigh) (z7 σ D)∧
      (z7 σ D).length = D.length∧
      zu n (z7 σ D) = zu n D∧qd n (z7 σ D) = qd n D∧
      z1 n (z7 σ D) = (z1 n D).image σ:=
  ⟨z2l σ h,rename h hc σ a,q8 σ D,
    z4o σ h.1 h.2.2,z4n σ h.1 h.2.2,z2v σ h.1⟩
def z3s (n M : Nat) : Nat:=((List.range n).filter fun i=>M.testBit i).length
theorem xk {n : Nat} (p : Nat→ Bool) :
    (Finset.univ.filter fun v : Fin n=>p v.val = true).card =
    ((List.range n).filter p).length:=by
  have hmap : (List.finRange n).map Fin.val = List.range n:=
    List.ext_getElem (by simp) (fun i h1 h2=>by simp)
  have h1 : Finset.univ.filter (fun v : Fin n=>p v.val = true) =
      ((List.finRange n).filter (fun v : Fin n=>p v.val)).toFinset:=by
    ext v;simp [List.mem_filter]
  rw [h1,List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _),← hmap,List.filter_map,List.length_map];rfl
theorem qo {n M : Nat} : (mask M : Finset (Fin n)).card = z3s n M:=
  xk (fun i=>M.testBit i)
theorem z3t {n P I : Nat} :
    ((mask P : Finset (Fin n)) \ mask I).card =
    ((List.range n).filter fun i=>P.testBit i && !I.testBit i).length:=by
  have h : (mask P : Finset (Fin n)) \ mask I =
      Finset.univ.filter (fun v : Fin n=>(P.testBit v.val && !I.testBit v.val) = true):=by
    ext v;simp [mask,Bool.and_eq_true]
  rw [h];exact xk (fun i=>P.testBit i && !I.testBit i)
theorem vk {n P : Nat} {neigh : List Nat} (i : Fin n) :
    (z9 neigh (mask P) i).card = z3s n (P &&& neigh.getD i.val 0):=by
  have h : z9 neigh (mask P) i = mask (P &&& neigh.getD i.val 0):=by
    ext a;simp [z9,mask,z4,Nat.testBit_and,Bool.and_eq_true]
  rw [h];exact qo
abbrev z0v:=Nat×Nat×Nat×Nat×Nat×Nat×List Nat
def vr (n : Nat) (neigh : List Nat) (goodMask w0 target : Nat) (s : z0v) : Bool:=
  let (I,P,U,W,J,Q,al):=s
  let nb (i : Nat):=neigh.getD i 0
  vu n neigh P &&
  decide (z3s n P≤ 7) &&
  (List.range n).all (fun x=>!Q.testBit x || P.testBit x) &&
  (List.range n).all (fun i=>!U.testBit i || (I.testBit i && goodMask.testBit i && z3s n (P &&& nb i) == 3)) &&
  (List.range n).all (fun i=>!W.testBit i || (I.testBit i && goodMask.testBit i && z3s n (P &&& nb i) == 2)) &&
  (List.range n).all (fun i=>!J.testBit i || (I.testBit i && goodMask.testBit i &&
    (List.range n).any (fun a=>P.testBit a && (nb i).testBit a) &&
    (List.range n).all (fun f=>!Q.testBit f || (List.range n).any (fun a=>(al.getD f 0).testBit a && (nb i).testBit a)))) &&
  (List.range n).all (fun f=>!Q.testBit f ||
    (let Af:=al.getD f 0
     vu n neigh Af &&
     (List.range n).all (fun a=>!(a != f && P.testBit a) || Af.testBit a) &&
     (List.range n).any (fun a=>Af.testBit a && (nb f).testBit a))) &&
  decide (target + z3s n P + ((List.range n).filter fun v=>P.testBit v && !I.testBit v).length≤
    z3s n J + z3s n Q + 2 * z3s n U + z3s n W + (n - z3s n I) +
    (if w0 != 0 && (List.range n).all (fun x=>!w0.testBit x || !P.testBit x) then 1 else 0))
theorem wh {n w0 goodMask target : ℕ} {neigh : List Nat} {Good : Fin n→ Prop} {D : Dag}
    (hG : zc (z4 neigh) Good) (h : z0 n D) (hc : z3 n (z4 neigh) D)
    (hEl : ∀ v∈z6 n D,Good v)
    (hGood : ∀ v : Fin n,goodMask.testBit v.val = true→ Good v)
    (ff : ∀ i j : Fin n,i≠j→ (z9 neigh Finset.univ i∩z9 neigh Finset.univ j).card≤ 1)
    (hw0 : w0≠0→ ∃ w,2≤ zd D w∧supp n D w = (mask w0 : Finset (Fin n))∧2≤ (supp n D w).card)
    (z : qd n D = 0) (s : z0v)
    (eq : (mask s.1 : Finset (Fin n)) = z1 n D)
    (ok : vr n neigh goodMask w0 target s = true) :
    target≤ zu n D:=by
  rcases s with ⟨I,P,U,W,J,Q,al⟩
  simp only [vr,Bool.and_eq_true,decide_eq_true_eq] at ok
  rcases ok with ⟨⟨⟨⟨⟨⟨⟨hPind,hP7⟩,hQP⟩,hU⟩,hW⟩,hJ⟩,hFree⟩,hIneq⟩
  have hpb:=z2w (w0:=w0) hG h hc hEl ff hw0 z
    (mask P) (mask I) (mask U) (mask W) (mask J) (mask Q)
    (fun f : Fin n=>mask (al.getD f.val 0)) eq (yu hPind)
    (by rw [qo];exact hP7)
    (fun x hx=>by
      simp only [mask,mem_filter,mem_univ,true_and] at hx ⊢
      have:=List.all_eq_true.mp hQP x.val (List.mem_range.mpr x.isLt)
      simpa [hx] using this)
    (fun i hi=>by
      simp only [mask,mem_filter,mem_univ,true_and] at hi
      have:=List.all_eq_true.mp hU i.val (List.mem_range.mpr i.isLt)
      simp only [hi,Bool.not_true,Bool.false_or,Bool.and_eq_true,beq_iff_eq] at this;exact ⟨by simp [mask,this.1.1],hGood i this.1.2,by rw [vk];exact this.2⟩)
    (fun i hi=>by
      simp only [mask,mem_filter,mem_univ,true_and] at hi
      have:=List.all_eq_true.mp hW i.val (List.mem_range.mpr i.isLt)
      simp only [hi,Bool.not_true,Bool.false_or,Bool.and_eq_true,beq_iff_eq] at this;exact ⟨by simp [mask,this.1.1],hGood i this.1.2,by rw [vk];exact this.2⟩)
    (fun i hi=>by
      simp only [mask,mem_filter,mem_univ,true_and] at hi
      have:=List.all_eq_true.mp hJ i.val (List.mem_range.mpr i.isLt)
      simp only [hi,Bool.not_true,Bool.false_or,Bool.and_eq_true,List.any_eq_true,List.mem_range] at this;obtain ⟨⟨⟨hiI,hiG⟩,⟨a,ha,haP,hia⟩⟩,hAf⟩:=this
      refine ⟨by simp [mask,hiI],hGood i hiG,⟨⟨a,ha⟩,by simp only [mask,mem_filter,mem_univ,true_and];exact haP,hia⟩,fun f hf=>?_⟩
      simp only [mask,mem_filter,mem_univ,true_and] at hf;have hf':=List.all_eq_true.mp hAf f.val (List.mem_range.mpr f.isLt);simp only [hf,Bool.not_true,Bool.false_or,List.any_eq_true,List.mem_range,Bool.and_eq_true] at hf';obtain ⟨b,hb,hbA,hib⟩:=hf'
      exact ⟨⟨b,hb⟩,by simp only [mask,mem_filter,mem_univ,true_and];exact hbA,hib⟩)
    (fun f hf=>by
      simp only [mask,mem_filter,mem_univ,true_and] at hf;have hf':=List.all_eq_true.mp hFree f.val (List.mem_range.mpr f.isLt);simp only [hf,Bool.not_true,Bool.false_or,Bool.and_eq_true,List.any_eq_true,List.mem_range] at hf';obtain ⟨⟨hAind,hEr⟩,⟨a,ha,haA,hfa⟩⟩:=hf'
      refine ⟨yu hAind,fun x hx=>?_,⟨⟨a,ha⟩,by simp only [mask,mem_filter,mem_univ,true_and];exact haA,hfa⟩⟩
      simp only [mem_erase,mask,mem_filter,mem_univ,true_and] at hx ⊢;have hx':=List.all_eq_true.mp hEr x.val (List.mem_range.mpr x.isLt);have hne : x.val≠f.val:=fun e=>hx.1 (Fin.ext e)
      simpa [bne_iff_ne,hne,hx.2] using hx')
  rw [qo,qo,qo,qo,
      qo,qo,z3t] at hpb
  have hbon : (if (w0 != 0) = true∧((List.range n).all fun x=>!w0.testBit x || !P.testBit x) = true then 1 else 0)≤
      (if w0≠0∧∀ x∈(mask w0 : Finset (Fin n)),x∉(mask P : Finset (Fin n)) then 1 else 0):=by
    split_ifs with h1 h2
    · exact le_refl 1
    · exfalso;apply h2
      simp only [bne_iff_ne,ne_eq] at h1
      refine ⟨h1.1,fun x hx hxP=>?_⟩
      simp only [mask,mem_filter,mem_univ,true_and] at hx hxP
      have:=List.all_eq_true.mp h1.2 x.val (List.mem_range.mpr x.isLt)
      simp [hx,hxP] at this
    · exact Nat.zero_le _
    · exact le_refl 0
  omega
end GraphTools
namespace Reduction
open Finset
open DagTools Compact GraphTools
def z6o : List Nat:=[1024,8832,12544,6272,11264,5632,2816,10,68,98,49,88,44,22]
def z6n : List Nat:=[4416,6272,3136,5632,2816,1408,5,34,49,24,44,22,11]
def z6e : List Nat:=[2368,3200,1600,2560,1280,896,5,34,49,44,22,11]
abbrev v5:=z4 z6o (n:=14)
abbrev z22:=z4 z6n (n:=13)
abbrev z0h:=z4 z6e (n:=12)
def z6i (v : Fin 14) : Bool:=v.val != 0
theorem z6a : zc v5 (fun v=>z6i v = true):=by unfold zc;decide +kernel
theorem grGp : zc z22 (fun _=>True):=by unfold zc;decide +kernel
theorem z5o : zc z0h (fun _=>True):=by unfold zc;decide +kernel
def z09 (i : Fin 13) : Fin 14:=⟨i.val + 1,by omega⟩
def y1 (x : Fin 13→ Bool) : Fin 14→ Bool:=
  fun v=>if h : v.val = 0 then false else x ⟨v.val - 1,by omega⟩
def wz (i : Fin 12) : Fin 14:=
  if h : i.val < 9 then ⟨i.val + 1,by omega⟩ else ⟨i.val + 2,by omega⟩
def yo (x : Fin 12→ Bool) : Fin 14→ Bool:=
  fun v=>if v.val = 0 then true else if v.val = 10 then false
    else if h : v.val < 10 then x ⟨v.val - 1,by omega⟩ else x ⟨v.val - 2,by omega⟩
theorem z4w : ∀ u v : Fin 13,z22 u v↔v5 (z09 u) (z09 v):=by decide +kernel
theorem z4i : ∀ u v : Fin 12,z0h u v↔v5 (wz u) (wz v):=by decide +kernel
theorem hneGp : ∃ u v : Fin 13,z22 u v:=⟨0,6,by decide⟩
theorem z5z : ∃ u v : Fin 12,z0h u v:=⟨0,6,by decide⟩
theorem z5n : ∀ u : Fin 14,u∉({0,4,5} : Finset (Fin 14))→
    ∃ z,v5 0 z∧¬ v5 u z:=by decide +kernel
theorem z2n (x : Fin 13→ Bool) : qi v5 (y1 x)↔qi z22 x:=by
  constructor
  · rintro ⟨u,v,huv,hu,hv⟩
    have hu0 : u.val≠0:=by intro h0;simp [y1,h0] at hu
    have hv0 : v.val≠0:=by intro h0;simp [y1,h0] at hv
    refine ⟨⟨u.val - 1,by omega⟩,⟨v.val - 1,by omega⟩,(z4w _ _).2 ?_,?_,?_⟩
    · have e1 : z09 ⟨u.val - 1,by omega⟩ = u:=Fin.ext (by simp [z09];omega)
      have e2 : z09 ⟨v.val - 1,by omega⟩ = v:=Fin.ext (by simp [z09];omega);rw [e1,e2];exact huv
    · simpa [y1,hu0] using hu
    · simpa [y1,hv0] using hv
  · rintro ⟨u,v,huv,hu,hv⟩
    refine ⟨z09 u,z09 v,(z4w u v).1 huv,?_,?_⟩
    · simpa [y1,z09] using hu
    · simpa [y1,z09] using hv
theorem z20 (x : Fin 12→ Bool) : qi v5 (yo x)↔qi z0h x:=by
  have h0n : ∀ v : Fin 14,v5 ⟨0,by omega⟩ v→ v.val = 10:=by decide +kernel
  have h0n' : ∀ u : Fin 14,v5 u ⟨0,by omega⟩→ u.val = 10:=by decide +kernel
  constructor
  · rintro ⟨u,v,huv,hu,hv⟩
    have hu10 : u.val≠10:=by intro h10;simp [yo,h10] at hu
    have hv10 : v.val≠10:=by intro h10;simp [yo,h10] at hv
    have hu0 : u.val≠0:=by
      intro h0;have eu : u = ⟨0,by omega⟩:=Fin.ext h0;exact hv10 (h0n v (eu▸huv))
    have hv0 : v.val≠0:=by
      intro h0;have ev : v = ⟨0,by omega⟩:=Fin.ext h0;exact hu10 (h0n' u (ev▸huv))
    let u' : Fin 12:=if h : u.val < 10 then ⟨u.val - 1,by omega⟩ else ⟨u.val - 2,by omega⟩
    let v' : Fin 12:=if h : v.val < 10 then ⟨v.val - 1,by omega⟩ else ⟨v.val - 2,by omega⟩
    have eu : wz u' = u:=by
      apply Fin.ext
      by_cases h1 : u.val < 10
      · simp [u',wz,h1,show u.val - 1 < 9 by omega];omega
      · simp [u',wz,h1,show ¬ u.val - 2 < 9 by omega];omega
    have ev : wz v' = v:=by
      apply Fin.ext
      by_cases h1 : v.val < 10
      · simp [v',wz,h1,show v.val - 1 < 9 by omega];omega
      · simp [v',wz,h1,show ¬ v.val - 2 < 9 by omega];omega
    refine ⟨u',v',(z4i u' v').2 (by rw [eu,ev];exact huv),?_,?_⟩
    · simp only [u'];split_ifs with hlt <;> simpa [yo,hu0,hu10,hlt] using hu
    · simp only [v'];split_ifs with hlt <;> simpa [yo,hv0,hv10,hlt] using hv
  · rintro ⟨u,v,huv,hu,hv⟩
    refine ⟨wz u,wz v,(z4i u v).1 huv,?_,?_⟩
    · by_cases h9 : u.val < 9
      · simp [yo,wz,h9,show u.val + 1≠10 by omega,show u.val + 1 < 10 by omega,hu]
      · simp [yo,wz,h9,show u.val + 2≠10 by omega,show ¬ u.val + 2 < 10 by omega,hu]
    · by_cases h9 : v.val < 9
      · simp [yo,wz,h9,show v.val + 1≠10 by omega,show v.val + 1 < 10 by omega,hv]
      · simp [yo,wz,h9,show v.val + 2≠10 by omega,show ¬ v.val + 2 < 10 by omega,hv]
def xr (n' : ℕ) (st : List Ref×Dag) (g : Bool×ℕ×ℕ) : List Ref×Dag:=
  match zy g.1 (z8 st.1 g.2.1) (z8 st.1 g.2.2) with
  | Sum.inl r=>(st.1 ++ [r],st.2)
  | Sum.inr p=>(st.1 ++ [Sum.inr (n' + st.2.length)],st.2 ++ [(g.1,p.1,p.2)])
def z2 (n' : ℕ) (m0 : List Ref) (D : Dag) : ℕ→ List Ref×Dag
  | 0=>(m0,[])
  | k + 1=>xr n' (z2 n' m0 D k) (D.getD k (false,0,0))
theorem z0c (n' : ℕ) (m0 : List Ref) (D : Dag) (k : ℕ) :
    (z2 n' m0 D k).1.length = m0.length + k:=by
  induction k with
  | zero=>simp [z2]
  | succ k ih=>
    simp only [z2,xr]
    cases zy _ _ _ <;> simp [ih,Nat.add_assoc]
theorem wx (n' : ℕ) (m0 : List Ref) (hm0 : ∀ r∈m0,wb n' r) (D : Dag) (k : ℕ) :
    z24 n' (z2 n' m0 D k):=by
  induction k with
  | zero=>
    exact ⟨fun j hj=>by simp [z2] at hj,fun r hr=>by simpa [z2] using hm0 r hr⟩
  | succ k ih=>
    obtain ⟨hS,hok⟩:=ih;simp only [z2,xr]
    set g:=D.getD k (false,0,0)
    have ha:=yw _ _ hok g.2.1;have hb:=yw _ _ hok g.2.2
    rcases hc : zy g.1 (z8 (z2 n' m0 D k).1 g.2.1) (z8 (z2 n' m0 D k).1 g.2.2) with r | p
    · refine ⟨hS,fun x hx=>?_⟩
      rcases List.mem_append.mp hx with h1 | h2
      · exact hok x h1
      · rw [List.mem_singleton.mp h2];exact z4a _ _ _ _ _ ha hb hc
    · obtain ⟨ea,eb,hne⟩:=z08 _ _ _ _ hc
      rw [ea] at ha;rw [eb] at hb
      refine ⟨z1w hS g.1 p.1 p.2 ha hb hne,fun x hx=>?_⟩
      simp only [List.length_append,List.length_singleton]
      rcases List.mem_append.mp hx with h1 | h2
      · exact z47 (by omega) x (hok x h1)
      · rw [List.mem_singleton.mp h2];show n' + (z2 n' m0 D k).2.length < n' + ((z2 n' m0 D k).2.length + 1);omega
theorem zi (n' : ℕ) (m0 : List Ref) (D : Dag) {j k w : ℕ}
    (hjk : j≤ k) (hw : w < m0.length + j) :
    z8 (z2 n' m0 D k).1 w = z8 (z2 n' m0 D j).1 w:=by
  induction k with
  | zero=>
    have hj0 : j = 0:=by omega
    subst hj0;rfl
  | succ k ih=>
    by_cases hle : j≤ k
    · rw [← ih hle]
      have hlen:=z0c n' m0 D k;have hw' : w < (z2 n' m0 D k).1.length:=by omega
      simp only [z2,xr,z8,List.getD_eq_getElem?_getD]
      cases zy _ _ _ <;> simp [List.getElem?_append_left hw']
    · have hje : j = k + 1:=by omega
      subst hje;rfl
theorem vj (n' : ℕ) (m0 : List Ref) (D : Dag) (k : ℕ) :
    z8 (z2 n' m0 D (k + 1)).1 (m0.length + k) =
      match zy (tag D k) (z8 (z2 n' m0 D k).1 (opA D k))
          (z8 (z2 n' m0 D k).1 (opB D k)) with
      | Sum.inl r=>r
      | Sum.inr _=>Sum.inr (n' + (z2 n' m0 D k).2.length):=by
  have hlen:=z0c n' m0 D k;simp only [z2,xr,tag,opA,opB,z8,List.getD_eq_getElem?_getD]
  cases zy _ _ _ <;> simp [List.getElem?_append_right (by omega : (z2 n' m0 D k).1.length≤ m0.length + k),hlen]
theorem z61 (g : Bool×ℕ×ℕ) (w : List Bool) : wl [g] w = vg w g:=rfl
theorem z3k (w : List Bool) (g : Bool×ℕ×ℕ) :
    (vg w g).getD w.length false = gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false):=by
  simp [vg,List.getD_eq_getElem?_getD]
theorem z2a {n n' : ℕ} (m0 : List Ref) (hm0len : m0.length = n)
    (hm0ok : ∀ r∈m0,wb n' r) {D : Dag} (hS : za n D)
    (x' : Fin n'→ Bool) (x : Fin n→ Bool)
    (hinit : ∀ i : Fin n,refVal (List.ofFn x') (z8 m0 i.val) = x i) :
    ∀ k≤ D.length,∀ w < n + k,
      refVal (wl (z2 n' m0 D k).2 (List.ofFn x')) (z8 (z2 n' m0 D k).1 w) = val D x w:=by
  intro k
  induction k with
  | zero=>
    intro _ w hw;have hwl : wl (z2 n' m0 D 0).2 (List.ofFn x') = List.ofFn x':=by simp [z2,wl]
    rw [hwl,val_input D x w hw];exact hinit ⟨w,hw⟩
  | succ k ih=>
    intro hk w hw;have hk' : k < D.length:=by omega
    obtain ⟨hSk,hokk⟩:=wx n' m0 hm0ok D k;have hlenk:=z0c n' m0 D k;have hwl_len : (wl (z2 n' m0 D k).2 (List.ofFn x')).length = n' + (z2 n' m0 D k).2.length:=by
      rw [z0i,List.length_ofFn]
    by_cases hlt : w < n + k
    · have hst:=zi n' m0 D (Nat.le_succ k) (by omega : w < m0.length + k)
      rw [hst];have hokw : wb (n' + (z2 n' m0 D k).2.length) (z8 (z2 n' m0 D k).1 w):=
        yw _ _ hokk w
      simp only [z2,xr]
      cases hc : zy _ _ _
      · exact ih (by omega) w hlt
      · rename_i p
        rw [z0j,z61,z1i _ _ _ (by rw [hwl_len];exact hokw)];exact ih (by omega) w hlt
    · have hweq : w = n + k:=by omega
      subst hweq;rw [val_gate hS x k hk'];obtain ⟨ha,hb,_⟩:=hS k hk';have eva:=ih (by omega) (opA D k) ha;have evb:=ih (by omega) (opB D k) hb;have hstep:=vj n' m0 D k;rw [hm0len] at hstep;rw [hstep]
      set g:=D.getD k (false,0,0)
      rcases hc : zy (tag D k) (z8 (z2 n' m0 D k).1 (opA D k))
          (z8 (z2 n' m0 D k).1 (opB D k)) with r | p
      · have hd : (z2 n' m0 D (k + 1)).2 = (z2 n' m0 D k).2:=by
          simp only [z2,xr,tag,opA,opB] at hc ⊢;rw [hc]
        rw [hd,z3h _ _ _ _ _ hc,eva,evb]
      · have hd : (z2 n' m0 D (k + 1)).2 = (z2 n' m0 D k).2 ++ [(tag D k,p.1,p.2)]:=by
          simp only [z2,xr,tag,opA,opB] at hc ⊢;rw [hc]
        obtain ⟨ea,eb,_⟩:=z08 _ _ _ _ hc;rw [hd,z0j,z61];change (vg (wl (z2 n' m0 D k).2 (List.ofFn x')) (tag D k,p.1,p.2)).getD
          (n' + (z2 n' m0 D k).2.length) false = _
        rw [← hwl_len,z3k];rw [ea] at eva;rw [eb] at evb;exact congrArg₂ (gop (tag D k)) eva evb
def qp (n' : ℕ) (m0 : List Ref) (D : Dag) (j : ℕ) : Bool:=
  (zy (tag D j)
    (z8 (z2 n' m0 D D.length).1 (opA D j))
    (z8 (z2 n' m0 D D.length).1 (opB D j))).isLeft
theorem w8 {n n' : ℕ} (m0 : List Ref) (hm0len : m0.length = n)
    {D : Dag} (hS : za n D) :
    ∀ k≤ D.length,
      (z2 n' m0 D k).2.length + ((Finset.range k).filter (fun j=>qp n' m0 D j = true)).card = k:=by
  intro k
  induction k with
  | zero=>simp [z2]
  | succ k ih=>
    intro hk;have hk' : k < D.length:=by omega
    obtain ⟨ha,hb,_⟩:=hS k hk';have hA:=zi n' m0 D (show k≤ D.length by omega) (by omega : opA D k < m0.length + k)
    have hB:=zi n' m0 D (show k≤ D.length by omega) (by omega : opB D k < m0.length + k)
    rw [Finset.range_add_one,Finset.filter_insert];have hnot : k∉(Finset.range k).filter (fun j=>qp n' m0 D j = true):=by simp
    have hih:=ih (by omega)
    rcases hc : zy (tag D k) (z8 (z2 n' m0 D k).1 (opA D k))
        (z8 (z2 n' m0 D k).1 (opB D k)) with r | p
    · have hd : (z2 n' m0 D (k + 1)).2 = (z2 n' m0 D k).2:=by
        simp only [z2,xr,tag,opA,opB] at hc ⊢;rw [hc]
      have hdropk : qp n' m0 D k = true:=by simp only [qp,hA,hB,hc,Sum.isLeft_inl]
      rw [hd,if_pos hdropk,Finset.card_insert_of_notMem hnot];omega
    · have hd : (z2 n' m0 D (k + 1)).2 = (z2 n' m0 D k).2 ++ [(tag D k,p.1,p.2)]:=by
        simp only [z2,xr,tag,opA,opB] at hc ⊢;rw [hc]
      have hdropk : qp n' m0 D k = false:=by simp only [qp,hA,hB,hc,Sum.isLeft_inr]
      rw [hd,if_neg (by simp [hdropk]),List.length_append,List.length_singleton];omega
theorem yd {n n' : ℕ} (m0 : List Ref) (hm0len : m0.length = n)
    {D : Dag} (hS : za n D) {j : ℕ} (hj : j < D.length) :
    z8 (z2 n' m0 D D.length).1 (n + j) =
      match zy (tag D j) (z8 (z2 n' m0 D D.length).1 (opA D j))
          (z8 (z2 n' m0 D D.length).1 (opB D j)) with
      | Sum.inl r=>r
      | Sum.inr _=>Sum.inr (n' + (z2 n' m0 D j).2.length):=by
  obtain ⟨ha,hb,_⟩:=hS j hj;have h1:=zi n' m0 D (show j + 1≤ D.length by omega) (by omega : n + j < m0.length + (j + 1))
  have hA:=zi n' m0 D (show j≤ D.length by omega) (by omega : opA D j < m0.length + j)
  have hB:=zi n' m0 D (show j≤ D.length by omega) (by omega : opB D j < m0.length + j)
  rw [h1,hA,hB,← hm0len];exact vj n' m0 D j
theorem z1z {n' : ℕ} {m0 : List Ref} {D : Dag} {j : ℕ} {b : Bool}
    (h : z8 (z2 n' m0 D D.length).1 (opA D j) = Sum.inl b) :
    qp n' m0 D j = true:=by
  simp [qp,h,zy]
theorem z1l {n' : ℕ} {m0 : List Ref} {D : Dag} {j : ℕ} {b : Bool}
    (h : z8 (z2 n' m0 D D.length).1 (opB D j) = Sum.inl b) :
    qp n' m0 D j = true:=by
  simp only [qp,h]
  cases z8 (z2 n' m0 D D.length).1 (opA D j) <;> simp [zy]
theorem zv {n' : ℕ} {m0 : List Ref} {D : Dag} {v j : ℕ} {b : Bool}
    (hj : j∈zq D v) (hv : z8 (z2 n' m0 D D.length).1 v = Sum.inl b) :
    qp n' m0 D j = true:=by
  simp only [zq,mem_filter,Finset.mem_range] at hj
  rcases hj.2 with h1 | h1
  · exact z1z (h1▸hv)
  · exact z1l (h1▸hv)
theorem gate_const_of_both {n n' : ℕ} {m0 : List Ref} (hm0len : m0.length = n)
    {D : Dag} (hS : za n D) {j : ℕ} (hj : j < D.length) {a b : Bool}
    (ha : z8 (z2 n' m0 D D.length).1 (opA D j) = Sum.inl a)
    (hb : z8 (z2 n' m0 D D.length).1 (opB D j) = Sum.inl b) :
    ∃ c : Bool,z8 (z2 n' m0 D D.length).1 (n + j) = Sum.inl c:=by
  rw [yd m0 hm0len hS hj,ha,hb];simp only [zy]
  split_ifs
  · exact ⟨b,rfl⟩
  · exact ⟨a,rfl⟩
theorem gate_const_of_absorb {n n' : ℕ} {m0 : List Ref} (hm0len : m0.length = n)
    {D : Dag} (hS : za n D) {v j : ℕ} (hj : j∈zq D v) {a : Bool}
    (hv : z8 (z2 n' m0 D D.length).1 v = Sum.inl a) (ht : a≠tag D j) :
    z8 (z2 n' m0 D D.length).1 (n + j) = Sum.inl a:=by
  simp only [zq,mem_filter,Finset.mem_range] at hj;rw [yd m0 hm0len hS hj.1]
  rcases hj.2 with h1 | h1
  · rw [h1,hv];simp [zy,ht]
  · rw [h1,hv]
    cases hr : z8 (z2 n' m0 D D.length).1 (opA D j) with
    | inl b=>
      simp only [zy]
      split_ifs with hbt
      · rfl
      · cases a <;> cases b <;> cases tag D j <;> simp_all
    | inr i=>simp [zy,ht]
theorem w3 {n n' : ℕ} {G' : Fin n'→ Fin n'→ Prop} {Good' : Fin n'→ Prop}
    (hG' : zc G' Good') (hne_G' : ∃ u v : Fin n',G' u v)
    (m0 : List Ref) (hm0len : m0.length = n) (hm0ok : ∀ r∈m0,wb n' r)
    {D : Dag} (h : z0 n D)
    (ext : (Fin n'→ Bool)→ (Fin n→ Bool))
    (hinit : ∀ (x' : Fin n'→ Bool) (i : Fin n),refVal (List.ofFn x') (z8 m0 i.val) = ext x' i)
    (hcomp : ∀ x' : Fin n'→ Bool,val D (ext x') (qc n D) = true↔qi G' x') :
    ∃ k,n'≤ k∧k < n' + (z2 n' m0 D D.length).2.length∧
      z8 (z2 n' m0 D D.length).1 (qc n D) = Sum.inr k∧
      ∃ E : Dag,z0 n' E∧E.length≤ k - n' + 1∧z3 n' G' E:=by
  set st:=z2 n' m0 D D.length
  obtain ⟨hS,hL,hne⟩:=h;have hpos : 0 < D.length:=List.length_pos_iff.mpr hne;obtain ⟨hSE,hokE⟩:=wx n' m0 hm0ok D D.length;have hout_lt : qc n D < n + D.length:=by unfold qc;omega
  have hev : ∀ x' : Fin n'→ Bool,
      refVal (wl st.2 (List.ofFn x')) (z8 st.1 (qc n D)) = val D (ext x') (qc n D):=
    fun x'=>z2a m0 hm0len hm0ok hS x' (ext x') (hinit x') D.length le_rfl (qc n D) hout_lt
  have hok_out:=yw _ _ hokE (qc n D)
  rcases hr : z8 st.1 (qc n D) with b | k
  · exfalso
    cases b
    · obtain ⟨u,v,huv⟩:=hne_G'
      have h1:=(hcomp (qv u v)).2 (wq huv);have h2:=hev (qv u v);rw [hr] at h2;simp [refVal] at h2;rw [h2] at h1;contradiction
    · have h1 : ¬ qi G' (fun _=>false):=by rintro ⟨_,_,_,h1,_⟩;contradiction
      have h2:=hev (fun _=>false);rw [hr] at h2;simp [refVal] at h2;exact h1 ((hcomp _).1 h2)
  · rw [hr] at hok_out
    have hklt : k < n' + st.2.length:=hok_out;have hkn : n'≤ k:=by
      by_contra hlt
      have hlt' : k < n':=by omega
      let v0 : Fin n':=⟨k,hlt'⟩
      have h2:=hev (single v0);rw [hr] at h2;change val st.2 (single v0) k = _ at h2;rw [val_input st.2 (single v0) k hlt'] at h2;have h3 : single v0 ⟨k,hlt'⟩ = true:=by simp [single,v0]
      rw [h3] at h2;exact qr hG' v0 ((hcomp (single v0)).1 h2.symm)
    refine ⟨k,hkn,hklt,rfl,?_⟩
    let E0:=st.2.take (k - n' + 1)
    have hlenE0 : E0.length = k - n' + 1:=by simp only [E0,List.length_take];omega
    have hneE0 : E0≠[]:=by intro heq;rw [heq] at hlenE0;simp at hlenE0
    let F : (Fin n'→ Bool)→ Bool:=fun x'=>val D (ext x') (qc n D)
    have hess : ∀ i : Fin n',∃ x y : Fin n'→ Bool,(∀ j,j≠i→ x j = y j)∧F x≠F y:=by
      intro i;obtain ⟨j,hij⟩:=hG'.2.2.2 i
      refine ⟨single j,qv i j,fun t ht=>by simp [single,qv,ht],?_⟩
      intro heq;have h1 : F (single j) = false:=by
        by_contra htf;rw [Bool.not_eq_false] at htf
        exact qr hG' j ((hcomp _).1 htf)
      have h2 : F (qv i j) = true:=(hcomp _).2 (wq hij);rw [h1,h2] at heq;contradiction
    have hE0val : ∀ x' : Fin n'→ Bool,val E0 x' (qc n' E0) = F x':=by
      intro x';have ho : qc n' E0 = k:=by unfold qc;rw [hlenE0];omega
      rw [ho,val_take st.2 x' (k - n' + 1) k (by omega) (by omega)];have h2:=hev x';rw [hr] at h2;exact h2
    obtain ⟨E,hEL,hElen,hEval⟩:=exists_strictLive_of_strict F hess E0 (z1v hSE _) hneE0 hE0val
    refine ⟨E,hEL,by omega,fun x'=>by rw [hEval x'];exact hcomp x'⟩
theorem not_const_out_of_red {n n' : ℕ} {G' : Fin n'→ Fin n'→ Prop} {Good' : Fin n'→ Prop}
    (hG' : zc G' Good') (hne_G' : ∃ u v : Fin n',G' u v)
    (m0 : List Ref) (hm0len : m0.length = n) (hm0ok : ∀ r∈m0,wb n' r)
    {D : Dag} (h : z0 n D)
    (ext : (Fin n'→ Bool)→ (Fin n→ Bool))
    (hinit : ∀ (x' : Fin n'→ Bool) (i : Fin n),refVal (List.ofFn x') (z8 m0 i.val) = ext x' i)
    (hcomp : ∀ x' : Fin n'→ Bool,val D (ext x') (qc n D) = true↔qi G' x')
    {v : ℕ} {b : Bool} (hv : z8 (z2 n' m0 D D.length).1 v = Sum.inl b) :
    v≠qc n D:=by
  intro heq;obtain ⟨k,_,_,hnr,_⟩:=w3 hG' hne_G' m0 hm0len hm0ok h ext hinit hcomp;rw [heq] at hv;rw [hv] at hnr
  cases hnr
def z0f : List Ref:=
  Sum.inl false :: (List.range 13).map Sum.inr
theorem z3f {D : Dag} (h : z0 14 D) (hc : z3 14 v5 D) (hdrop :
    2≤ ((Finset.range D.length).filter (fun j=>qp 13 z0f D j = true)).card)
    (hlen : D.length≤ 24) :
    ∃ E : Dag,z0 13 E∧E.length≤ 22∧z3 13 z22 E:=by
  have hm0len : z0f.length = 14:=by decide
  have hm0ok : ∀ r∈z0f,wb 13 r:=by
    intro r hr;simp only [z0f,List.mem_cons,List.mem_map,List.mem_range] at hr
    rcases hr with rfl | ⟨i,hi,rfl⟩
    · trivial
    · exact hi
  have hinit : ∀ (x' : Fin 13→ Bool) (i : Fin 14),refVal (List.ofFn x') (z8 z0f i.val) = y1 x' i:=by
    intro x' i
    rcases i with ⟨v,hv⟩
    cases v with
    | zero=>simp [z0f,z8,refVal,y1]
    | succ v=>
      have hv13 : v < 13:=by omega
      simp only [z0f,z8,List.getD_eq_getElem?_getD,List.getElem?_cons_succ,
        List.getElem?_map,List.getElem?_range hv13,Option.map_some,Option.getD_some,
        refVal,y1,Nat.succ_ne_zero,dite_false,Nat.add_sub_cancel]
      exact z3c x' ⟨v,hv13⟩
  have hcomp : ∀ x' : Fin 13→ Bool,val D (y1 x') (qc 14 D) = true↔qi z22 x':=
    fun x'=>(hc (y1 x')).trans (z2n x')
  obtain ⟨k,hkn,hklt,_,E,hEL,hElen,hEcomp⟩:=
    w3 grGp hneGp z0f hm0len hm0ok h y1 hinit hcomp
  have hdc:=w8 (n':=13) z0f hm0len h.1 D.length le_rfl;exact ⟨E,hEL,by omega,hEcomp⟩
def zl : List Ref:=
  [Sum.inl true,Sum.inr 0,Sum.inr 1,Sum.inr 2,Sum.inr 3,Sum.inr 4,Sum.inr 5,
   Sum.inr 6,Sum.inr 7,Sum.inr 8,Sum.inl false,Sum.inr 9,Sum.inr 10,Sum.inr 11]
theorem vy : ∀ r∈zl,wb 12 r:=by
  intro r hr;simp only [zl,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [wb]
theorem z19 (x'' : Fin 12→ Bool) (i : Fin 14) :
    refVal (List.ofFn x'') (z8 zl i.val) = yo x'' i:=by
  fin_cases i <;> simp [zl,z8,refVal,yo,List.getD_eq_getElem?_getD]
theorem z4m {D : Dag} (h : z0 14 D) (hc : z3 14 v5 D) (hdrop :
    4≤ ((Finset.range D.length).filter (fun j=>qp 12 zl D j = true)).card)
    (hlen : D.length≤ 24) :
    ∃ E : Dag,z0 12 E∧E.length≤ 20∧z3 12 z0h E:=by
  have hm0len : zl.length = 14:=rfl;have hcomp : ∀ x'' : Fin 12→ Bool,val D (yo x'') (qc 14 D) = true↔qi z0h x'':=
    fun x''=>(hc (yo x'')).trans (z20 x'')
  obtain ⟨k,hkn,hklt,_,E,hEL,hElen,hEcomp⟩:=
    w3 z5o z5z zl hm0len vy h yo z19 hcomp
  have hdc:=w8 (n':=12) zl hm0len h.1 D.length le_rfl;exact ⟨E,hEL,by omega,hEcomp⟩
theorem z2u {D : Dag} (h : z0 14 D) (hc : z3 14 v5 D)
    (hlen : D.length≤ 24)
    (hdrop3 : 3≤ ((Finset.range D.length).filter (fun j=>qp 12 zl D j = true)).card)
    {jw g : ℕ} (hjw : jw < D.length) (hg : g < D.length)
    (hnd : qp 12 zl D jw = false)
    (hfan : zd D (14 + jw) = 1) (hgread : g∈zq D (14 + jw))
    (hgconst : z8 (z2 12 zl D D.length).1 (14 + g) = Sum.inl true) :
    ∃ E : Dag,z0 12 E∧E.length≤ 20∧z3 12 z0h E:=by
  have hm0len : zl.length = 14:=rfl;have hcomp : ∀ x'' : Fin 12→ Bool,val D (yo x'') (qc 14 D) = true↔qi z0h x'':=
    fun x''=>(hc (yo x'')).trans (z20 x'')
  obtain ⟨k,hkn,hklt,hlookOut,E1,hE1L,hE1len,hE1comp⟩:=
    w3 z5o z5z zl hm0len vy h yo z19 hcomp
  set st:=z2 12 zl D D.length
  have hdc : st.2.length + ((Finset.range D.length).filter (fun j=>qp 12 zl D j = true)).card = D.length:=
    w8 (n':=12) zl hm0len h.1 D.length le_rfl
  have hst_len : st.2.length≤ 21:=by omega
  by_cases hksmall : k + 1 < 12 + st.2.length
  · exact ⟨E1,hE1L,by omega,hE1comp⟩
  · have hkeq : k = qc 12 st.2:=by unfold qc;omega
    let idx:=(z2 12 zl D jw).2.length
    have hejw : z8 st.1 (14 + jw) = Sum.inr (12 + idx):=by
      have hl:=yd (n':=12) zl hm0len h.1 hjw;have hnd' : (zy (tag D jw) (z8 st.1 (opA D jw)) (z8 st.1 (opB D jw))).isLeft = false:=hnd
      cases hc2 : zy (tag D jw) (z8 st.1 (opA D jw)) (z8 st.1 (opB D jw)) with
      | inl r=>rw [hc2] at hnd';simp at hnd'
      | inr p=>rw [hl,hc2]
    have hmono : ∀ a b,a≤ b→ (z2 12 zl D a).2.length≤ (z2 12 zl D b).2.length:=by
      intro a b hab
      induction b with
      | zero=>
        have ha0 : a = 0:=by omega
        subst ha0;exact le_rfl
      | succ b ih=>
        by_cases hle : a≤ b
        · refine le_trans (ih hle) ?_
          simp only [z2,xr]
          cases zy _ _ _ <;> simp
        · have hab1 : a = b + 1:=by omega
          subst hab1;exact le_rfl
    have hstep_jw : (z2 12 zl D (jw + 1)).2.length = idx + 1:=by
      have hA:=zi 12 zl D (show jw≤ D.length by omega) (by have:=(h.1 jw hjw).1;rw [hm0len];omega)
      have hB:=zi 12 zl D (show jw≤ D.length by omega) (by have:=(h.1 jw hjw).2.1;rw [hm0len];omega)
      have hnd' : (zy (tag D jw) (z8 (z2 12 zl D jw).1 (opA D jw))
          (z8 (z2 12 zl D jw).1 (opB D jw))).isLeft = false:=by
        simpa only [qp,hA,hB] using hnd
      simp only [z2,xr,idx];change (match zy (tag D jw) (z8 (z2 12 zl D jw).1 (opA D jw))
          (z8 (z2 12 zl D jw).1 (opB D jw)) with
          | Sum.inl r=>((z2 12 zl D jw).1 ++ [r],(z2 12 zl D jw).2)
          | Sum.inr p=>((z2 12 zl D jw).1 ++ [Sum.inr (12 + (z2 12 zl D jw).2.length)],
              (z2 12 zl D jw).2 ++ [(tag D jw,p.1,p.2)])).2.length = _
      cases hc2 : zy (tag D jw) (z8 (z2 12 zl D jw).1 (opA D jw))
          (z8 (z2 12 zl D jw).1 (opB D jw)) with
      | inl r=>simp [hc2] at hnd'
      | inr p=>simp
    have hidx_lt : idx < st.2.length:=by
      have h1:=hmono (jw + 1) D.length (by omega);change (z2 12 zl D (jw + 1)).2.length≤ st.2.length at h1;omega
    have hno_alias : ∀ v < 14 + D.length,v≠14 + jw→ z8 st.1 v≠Sum.inr (12 + idx):=by
      intro v
      induction v using Nat.strong_induction_on with
      | _ v ih=>
        intro hv hne
        by_cases hv14 : v < 14
        · have hst:=zi 12 zl D (Nat.zero_le D.length) (by rw [hm0len];omega)
          have hok0:=yw 12 zl vy v;change z8 st.1 v = z8 zl v at hst;rw [hst]
          cases hl : z8 zl v with
          | inl _=>simp
          | inr a=>rw [hl] at hok0;intro heq;injection heq with ha;dsimp [wb] at hok0;omega
        · obtain ⟨q,rfl⟩ : ∃ q,v = 14 + q:=⟨v - 14,by omega⟩
          have hq : q < D.length:=by omega
          by_cases hql : q < jw
          · have hst:=zi 12 zl D (show q + 1≤ D.length by omega) (show 14 + q < zl.length + (q + 1) by rw [hm0len];omega)
            have hokq:=yw _ _ (wx 12 zl vy D (q + 1)).2 (14 + q);have hle : (z2 12 zl D (q + 1)).2.length≤ idx:=hmono (q + 1) jw (by omega);rw [hst]
            cases hl : z8 (z2 12 zl D (q + 1)).1 (14 + q) with
            | inl _=>simp
            | inr a=>rw [hl] at hokq;intro heq;injection heq with ha;dsimp [wb] at hokq;omega
          · have hqgt : jw < q:=by omega
            by_cases hqg : q = g
            · subst hqg;rw [hgconst];simp
            · rw [yd zl hm0len h.1 hq]
              obtain ⟨ha,hb,_⟩:=h.1 q hq;have hnot_read : opA D q≠14 + jw∧opB D q≠14 + jw:=by
                have hcard : (zq D (14 + jw)).card = 1:=hfan;obtain ⟨g0,hg0⟩:=card_eq_one.mp hcard;have hgg0 : g = g0:=mem_singleton.mp (hg0▸hgread);subst hgg0
                constructor <;> intro hread
                · have hqm : q∈zq D (14 + jw):=mem_filter.mpr ⟨Finset.mem_range.mpr hq,Or.inl hread⟩
                  exact hqg (mem_singleton.mp (hg0▸hqm))
                · have hqm : q∈zq D (14 + jw):=mem_filter.mpr ⟨Finset.mem_range.mpr hq,Or.inr hread⟩
                  exact hqg (mem_singleton.mp (hg0▸hqm))
              have hna : z8 st.1 (opA D q)≠Sum.inr (12 + idx):=ih (opA D q) ha (by omega) hnot_read.1;have hnb : z8 st.1 (opB D q)≠Sum.inr (12 + idx):=ih (opB D q) hb (by omega) hnot_read.2
              cases hc2 : zy (tag D q) (z8 st.1 (opA D q)) (z8 st.1 (opB D q)) with
              | inl r=>
                rcases ha' : z8 st.1 (opA D q) with ba | ia <;>
                rcases hb' : z8 st.1 (opB D q) with bb | ib <;>
                  simp only [ha',hb',zy] at hc2
                · split_ifs at hc2 <;> cases hc2 <;> simp
                · split_ifs at hc2 <;> cases hc2
                  · exact hb'▸hnb
                  · simp
                · split_ifs at hc2 <;> cases hc2
                  · exact ha'▸hna
                  · simp
                · split_ifs at hc2
                  cases hc2;exact ha'▸hna
              | inr p=>
                have hge:=hmono (jw + 1) q (by omega);intro heq;injection heq with h';omega
    have hjw_ne_out : 14 + jw≠qc 14 D:=by
      have hg_gt : 14 + jw < 14 + g:=by
        simp only [zq,mem_filter,Finset.mem_range] at hgread;obtain ⟨ha,hb,_⟩:=h.1 g hg
        rcases hgread.2 with e | e <;> omega
      unfold qc;omega
    have hidx_ne_last : 12 + idx≠qc 12 st.2:=by
      intro heq;have hbad:=hno_alias (qc 14 D) (by unfold qc;have:=List.length_pos_iff.mpr h.2.2;omega) hjw_ne_out.symm;rw [hlookOut,hkeq,← heq] at hbad;exact hbad rfl
    have hidx_lt_sub : idx + 1 < st.2.length:=by unfold qc at hidx_ne_last;omega
    have hemit_ne : ∀ t≤ D.length,∀ r < (z2 12 zl D t).2.length,
        opA (z2 12 zl D t).2 r≠12 + idx∧opB (z2 12 zl D t).2 r≠12 + idx:=by
      intro t
      induction t with
      | zero=>intro _ r hr;simp [z2] at hr
      | succ t ih=>
        intro ht r hr;have ht' : t < D.length:=by omega
        obtain ⟨ha,hb,_⟩:=h.1 t ht';have hA:=zi 12 zl D (show t≤ D.length by omega) (w:=opA D t) (by rw [hm0len];omega)
        have hB:=zi 12 zl D (show t≤ D.length by omega) (w:=opB D t) (by rw [hm0len];omega)
        simp only [z2,xr] at hr ⊢
        rcases hc2 : zy (D.getD t (false,0,0)).1 (z8 (z2 12 zl D t).1 (D.getD t (false,0,0)).2.1)
            (z8 (z2 12 zl D t).1 (D.getD t (false,0,0)).2.2) with r0 | p
        · simp only [hc2] at hr ⊢
          exact ih (by omega) r hr
        · simp only [hc2,List.length_append,List.length_singleton] at hr ⊢
          by_cases hlt : r < (z2 12 zl D t).2.length
          · simp only [opA,opB,z07 _ _ r hlt]
            exact ih (by omega) r hlt
          · have hreq : r = (z2 12 zl D t).2.length:=by omega
            subst hreq;simp only [opA,opB,z2z];obtain ⟨ea,eb,_⟩:=z08 _ _ _ _ hc2;change p.1≠12 + idx∧p.2≠12 + idx;have htg : t≠g:=by
              intro hteq;subst t;have hgl:=yd (n':=12) zl hm0len h.1 hg;rw [hgconst] at hgl;change zy (tag D g) (z8 (z2 12 zl D g).1 (opA D g))
                (z8 (z2 12 zl D g).1 (opB D g)) = Sum.inr p at hc2
              rw [← hA,← hB] at hc2;rw [hc2] at hgl;cases hgl
            have hnot_read : opA D t≠14 + jw∧opB D t≠14 + jw:=by
              obtain ⟨g0,hg0⟩:=card_eq_one.mp hfan;have hgg0 : g = g0:=mem_singleton.mp (hg0▸hgread);subst hgg0
              constructor <;> intro hread
              · exact htg (mem_singleton.mp (hg0▸(mem_filter.mpr ⟨Finset.mem_range.mpr ht',Or.inl hread⟩)))
              · exact htg (mem_singleton.mp (hg0▸(mem_filter.mpr ⟨Finset.mem_range.mpr ht',Or.inr hread⟩)))
            have hna:=hno_alias (opA D t) (by omega) hnot_read.1;have hnb:=hno_alias (opB D t) (by omega) hnot_read.2;rw [hA] at hna;rw [hB] at hnb;change z8 (z2 12 zl D t).1 (opA D t) = Sum.inr p.1 at ea;change z8 (z2 12 zl D t).1 (opB D t) = Sum.inr p.2 at eb
            exact ⟨fun e=>hna (ea.trans (congrArg Sum.inr e)),fun e=>hnb (eb.trans (congrArg Sum.inr e))⟩
    have hfan0 : zd st.2 (12 + idx) = 0:=by
      unfold zd zq;rw [card_eq_zero,Finset.filter_eq_empty_iff];intro r hr;have hr':=Finset.mem_range.mp hr;have hne:=hemit_ne D.length le_rfl r hr';tauto
    have hSE : za 12 st.2:=(wx 12 zl vy D D.length).1
    let E0:=wm 12 idx st.2
    have hE0len : E0.length = st.2.length - 1:=wc 12 idx st.2 hidx_lt;have hE0ne : E0≠[]:=by intro heq;rw [heq] at hE0len;simp at hE0len;omega
    let F : (Fin 12→ Bool)→ Bool:=fun x''=>val D (yo x'') (qc 14 D)
    have hess : ∀ i : Fin 12,∃ x y : Fin 12→ Bool,(∀ j,j≠i→ x j = y j)∧F x≠F y:=by
      intro i;obtain ⟨j,hij⟩:=z5o.2.2.2 i
      refine ⟨single j,qv i j,fun t ht=>by simp [single,qv,ht],?_⟩
      intro heq;have h1 : F (single j) = false:=by
        by_contra htf;rw [Bool.not_eq_false] at htf
        exact qr z5o j ((hcomp _).1 htf)
      have h2 : F (qv i j) = true:=(hcomp _).2 (wq hij);rw [h1,h2] at heq;contradiction
    have hE0val : ∀ x'' : Fin 12→ Bool,val E0 x'' (qc 12 E0) = F x'':=by
      intro x'';have ho : qc 12 E0 = 12 + (st.2.length - 1) - 1:=by unfold qc;rw [hE0len]
      have hu : zs (12 + idx) (12 + (st.2.length - 1) - 1) = qc 12 st.2:=by
        unfold zs qc;split_ifs <;> omega
      rw [ho,z48 hSE idx hidx_lt hfan0 x'' _ (by omega),hu,← hkeq];have hv:=z2a zl hm0len vy h.1 x'' (yo x'') (z19 x'') D.length le_rfl (qc 14 D)
        (by unfold qc;have:=List.length_pos_iff.mpr h.2.2;omega)
      rw [hlookOut] at hv;exact hv
    obtain ⟨E,hEL,hElen,hEval⟩:=exists_strictLive_of_strict F hess E0 (z0d hSE idx hidx_lt hfan0) hE0ne hE0val;exact ⟨E,hEL,by omega,fun x''=>by rw [hEval x''];exact hcomp x''⟩
def yb (g w v : ℕ) : ℕ:=
  if v = 14 + g then w - 1
  else if 14 + g < v then v - 2
  else v - 1
def unsp (g v' : ℕ) : ℕ:=
  if v' < 13 + g then v' + 1 else v' + 2
def z2g (g w : ℕ) (D : Dag) : Dag:=
  (D.eraseIdx g).map (fun x=>(x.1,yb g w x.2.1,yb g w x.2.2))
theorem z65 {D : Dag} (h : z0 14 D) (hc : z3 14 v5 D) (hlen : D.length≤ 24)
    {g hgt w u : ℕ} (hg : g < D.length) (hh : hgt < D.length) (hgh : g < hgt)
    (hf0 : zd D 0 = 1) (hg0 : g∈zq D 0)
    (hgt_tag : tag D g = false) (hg_in : (opA D g = 0∧opB D g = w)∨(opA D g = w∧opB D g = 0))
    (hfg : zd D (14 + g) = 1) (hhg : hgt∈zq D (14 + g))
    (hh_in : (opA D hgt = 14 + g∧opB D hgt = u)∨(opA D hgt = u∧opB D hgt = 14 + g))
    (hsw : supp 14 D w = {⟨4,by omega⟩,⟨5,by omega⟩})
    (hsu : supp 14 D u = {⟨10,by omega⟩})
    (hfw : 2≤ zd D w) (h10 : (⟨10,by omega⟩ : Fin 14)∈z1 14 D) :
    ∃ D' : Dag,z0 13 D'∧D'.length≤ 23∧z3 13 z22 D'∧
      (⟨9,by omega⟩ : Fin 13)∈z1 13 D'∧
      ∃ w' : ℕ,2≤ zd D' w'∧supp 13 D' w' = {⟨3,by omega⟩,⟨4,by omega⟩}:=by
  have hw_lt : w < 14 + g:=by
    obtain ⟨ha,hb,_⟩:=h.1 g hg
    rcases hg_in with ⟨_,e⟩ | ⟨e,_⟩ <;> omega
  have hw_ge14 : 14≤ w:=by
    by_contra hlt
    have hs:=supp_input (n:=14) D ⟨w,by omega⟩;rw [hsw] at hs;have h4 : (⟨4,by omega⟩ : Fin 14)∈({⟨w,by omega⟩} : Finset (Fin 14)):=hs▸(by simp);have h5 : (⟨5,by omega⟩ : Fin 14)∈({⟨w,by omega⟩} : Finset (Fin 14)):=hs▸(by simp);simp only [mem_singleton,Fin.mk.injEq] at h4 h5;omega
  have huw : u≠w:=by
    intro heq;rw [heq,hsw] at hsu;have h10m : (⟨10,by omega⟩ : Fin 14)∈({⟨4,by omega⟩,⟨5,by omega⟩} : Finset (Fin 14)):=hsu▸(by simp);simp at h10m
  let D':=z2g g w D
  have hD'len : D'.length = D.length - 1:=by simp [D',z2g,List.length_eraseIdx,hg]
  have hD'ne : D'≠[]:=by intro heq;rw [heq] at hD'len;simp at hD'len;omega
  have hops : ∀ k,zs g k < D.length→
      tag D' k = tag D (zs g k)∧
      opA D' k = yb g w (opA D (zs g k))∧
      opB D' k = yb g w (opB D (zs g k)):=by
    intro k hk;have e : D'.getD k (false,0,0) =
        ((D.getD (zs g k) (false,0,0)).1,
          yb g w (D.getD (zs g k) (false,0,0)).2.1,
          yb g w (D.getD (zs g k) (false,0,0)).2.2):=by
      simp only [D',z2g,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eraseIdx];unfold zs at hk ⊢
      split_ifs at hk ⊢ <;> simp [List.getElem?_eq_getElem hk]
    unfold tag opA opB;rw [e];exact ⟨rfl,rfl,rfl⟩
  have hno0 : ∀ k,k < D.length→ k≠g→ opA D k≠0∧opB D k≠0:=by
    intro k hk hne;obtain ⟨g0,hg0eq⟩:=card_eq_one.mp hf0;have e : g = g0:=mem_singleton.mp (hg0eq▸hg0);subst e
    constructor <;> intro h0
    · exact hne (mem_singleton.mp (hg0eq▸mem_filter.mpr ⟨Finset.mem_range.mpr hk,Or.inl h0⟩))
    · exact hne (mem_singleton.mp (hg0eq▸mem_filter.mpr ⟨Finset.mem_range.mpr hk,Or.inr h0⟩))
  have hno_g : ∀ k,k < D.length→ k≠hgt→ opA D k≠14 + g∧opB D k≠14 + g:=by
    intro k hk hne;obtain ⟨h0,hh0⟩:=card_eq_one.mp hfg;have e : hgt = h0:=mem_singleton.mp (hh0▸hhg);subst e
    constructor <;> intro h0
    · exact hne (mem_singleton.mp (hh0▸mem_filter.mpr ⟨Finset.mem_range.mpr hk,Or.inl h0⟩))
    · exact hne (mem_singleton.mp (hh0▸mem_filter.mpr ⟨Finset.mem_range.mpr hk,Or.inr h0⟩))
  have hS' : za 13 D':=by
    intro k hk;rw [hD'len] at hk;have hk' : zs g k < D.length:=by unfold zs;split_ifs <;> omega
    have hne_g : zs g k≠g:=by unfold zs;split_ifs <;> omega
    obtain ⟨-,ea,eb⟩:=hops k hk';obtain ⟨ha,hb,hab⟩:=h.1 _ hk';obtain ⟨ha0,hb0⟩:=hno0 _ hk' hne_g;rw [ea,eb];have hlt_k : ∀ a,a≠0→ a < 14 + zs g k→ yb g w a < 13 + k:=by
      intro a ha0' halt;unfold yb;unfold zs at halt;split_ifs at halt ⊢ <;> omega
    refine ⟨hlt_k _ ha0 ha,hlt_k _ hb0 hb,?_⟩
    intro heq
    by_cases hkh : zs g k = hgt
    · rw [hkh] at hab heq
      rcases hh_in with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rw [h1,h2] at heq <;>
        (unfold yb at heq;split_ifs at heq <;> omega)
    · obtain ⟨hag,hbg⟩:=hno_g _ hk' hkh
      unfold yb at heq;split_ifs at heq <;> omega
  have hval' : ∀ (x' : Fin 13→ Bool) (v' : ℕ),v' < 13 + D'.length→
      val D' x' v' = val D (y1 x') (unsp g v'):=by
    intro x' v' hv'
    refine val_unique hS' x' (fun u'=>val D (y1 x') (unsp g u')) (fun i hi=>?_) (fun k hk=>?_) v' hv'
    · have e : unsp g i = i + 1:=by unfold unsp;split_ifs <;> omega
      show val D (y1 x') (unsp g i) = x' ⟨i,hi⟩
      rw [e,val_input D (y1 x') (i + 1) (by omega)];simp [y1]
    · rw [hD'len] at hk
      have hk' : zs g k < D.length:=by unfold zs;split_ifs <;> omega
      have hne_g : zs g k≠g:=by unfold zs;split_ifs <;> omega
      obtain ⟨et,ea,eb⟩:=hops k hk';obtain ⟨ha0,hb0⟩:=hno0 _ hk' hne_g;have he1 : unsp g (13 + k) = 14 + zs g k:=by unfold unsp zs;split_ifs <;> omega
      have hvg : val D (y1 x') (14 + g) = val D (y1 x') w:=by
        rw [val_gate h.1 (y1 x') g hg,hgt_tag]
        rcases hg_in with ⟨h1,h2⟩ | ⟨h1,h2⟩
        · rw [h1,h2,val_input D (y1 x') 0 (by omega)];simp [y1,gop]
        · rw [h1,h2,val_input D (y1 x') 0 (by omega)];simp [y1,gop]
      have hstep : ∀ a,a≠0→ val D (y1 x') (unsp g (yb g w a)) = val D (y1 x') a:=by
        intro a ha0'
        by_cases hag : a = 14 + g
        · subst hag
          have e2 : unsp g (yb g w (14 + g)) = w:=by unfold yb unsp;split_ifs <;> omega
          rw [e2,hvg]
        · have e2 : unsp g (yb g w a) = a:=by unfold yb unsp;split_ifs <;> omega
          rw [e2]
      show val D (y1 x') (unsp g (13 + k)) = gop (tag D' k)
        (val D (y1 x') (unsp g (opA D' k))) (val D (y1 x') (unsp g (opB D' k)))
      rw [he1,et,ea,eb,hstep _ ha0,hstep _ hb0];exact val_gate h.1 (y1 x') _ hk'
  have hfan' : ∀ v' < 13 + D'.length,zd D' v' = zd D (unsp g v'):=by
    intro v' hv';rw [hD'len] at hv'
    by_cases hvw : v' = w - 1
    · subst hvw
      have huw' : unsp g (w - 1) = w:=by unfold unsp;split_ifs <;> omega
      rw [huw'];have hcard_eq : (zq D' (w - 1)).card = (insert hgt ((zq D w).erase g)).card:=by
        refine Finset.card_nbij' (zs g) (fun j=>if j < g then j else j - 1) ?_ ?_ ?_ ?_
        · intro k hk
          simp only [Finset.mem_coe,zq,mem_filter,Finset.mem_range,hD'len] at hk;have hk' : zs g k < D.length:=by unfold zs;split_ifs <;> omega
          have hne_g : zs g k≠g:=by unfold zs;split_ifs <;> omega
          obtain ⟨-,ea,eb⟩:=hops k hk';obtain ⟨ha0,hb0⟩:=hno0 _ hk' hne_g;have hsp_eq : ∀ a,a≠0→ yb g w a = w - 1→ a = w∨a = 14 + g:=by
            intro a ha0' heq;unfold yb at heq;split_ifs at heq <;> omega
          simp only [Finset.mem_coe,mem_insert,mem_erase,zq,mem_filter,Finset.mem_range]
          rcases hk.2 with h1 | h1
          · rw [ea] at h1
            rcases hsp_eq _ ha0 h1 with h2 | h2
            · exact Or.inr ⟨hne_g,hk',Or.inl h2⟩
            · left;by_contra hnh;exact (hno_g _ hk' hnh).1 h2
          · rw [eb] at h1
            rcases hsp_eq _ hb0 h1 with h2 | h2
            · exact Or.inr ⟨hne_g,hk',Or.inr h2⟩
            · left;by_contra hnh;exact (hno_g _ hk' hnh).2 h2
        · intro j hj
          simp only [Finset.mem_coe,mem_insert,mem_erase,zq,mem_filter,Finset.mem_range] at hj ⊢;have hj_lt : j < D.length∧j≠g:=by
            rcases hj with rfl | ⟨hne,hjl,_⟩
            · exact ⟨hh,by omega⟩
            · exact ⟨hjl,hne⟩
          have hk_lt : (if j < g then j else j - 1) < D.length - 1:=by split_ifs <;> omega
          have hup : zs g (if j < g then j else j - 1) = j:=by unfold zs;split_ifs <;> omega
          obtain ⟨-,ea,eb⟩:=hops (if j < g then j else j - 1) (by rw [hup];exact hj_lt.1);rw [hD'len,ea,eb,hup]
          refine ⟨hk_lt,?_⟩
          rcases hj with rfl | ⟨_,_,h2 | h2⟩
          · rcases hh_in with ⟨h1,_⟩ | ⟨_,h1⟩
            · left;rw [h1];simp [yb]
            · right;rw [h1];simp [yb]
          · left;rw [h2];unfold yb;split_ifs <;> omega
          · right;rw [h2];unfold yb;split_ifs <;> omega
        · intro k _;by_cases hkg : k < g
          · simp [zs,hkg]
          · simp [zs,hkg,show ¬ k + 1 < g by omega]
        · intro j hj
          simp only [Finset.mem_coe,mem_insert,mem_erase] at hj;have hne : j≠g:=by rcases hj with rfl | ⟨h1,_⟩ <;> omega
          by_cases hjg : j < g
          · simp [zs,hjg]
          · simp [zs,hjg,show ¬ j - 1 < g by omega];omega
      have hgw : g∈zq D w:=by
        simp only [zq,mem_filter,Finset.mem_range]
        rcases hg_in with ⟨_,e⟩ | ⟨e,_⟩ <;> exact ⟨hg,by tauto⟩
      have hhw : hgt∉(zq D w).erase g:=by
        simp only [mem_erase,zq,mem_filter,Finset.mem_range,not_and];intro _ _ h2
        rcases hh_in with ⟨h1,h3⟩ | ⟨h3,h1⟩ <;> rcases h2 with h4 | h4 <;> omega
      unfold zd;rw [hcard_eq,Finset.card_insert_of_notMem hhw,Finset.card_erase_of_mem hgw];have hpos : 1≤ (zq D w).card:=by unfold zd at hfw;omega
      omega
    · unfold zd
      refine Finset.card_nbij' (zs g) (fun j=>if j < g then j else j - 1) ?_ ?_ ?_ ?_
      · intro k hk
        simp only [Finset.mem_coe,zq,mem_filter,Finset.mem_range,hD'len] at hk ⊢;have hk' : zs g k < D.length:=by unfold zs;split_ifs <;> omega
        have hne_g : zs g k≠g:=by unfold zs;split_ifs <;> omega
        obtain ⟨-,ea,eb⟩:=hops k hk';obtain ⟨ha0,hb0⟩:=hno0 _ hk' hne_g;have hsp : ∀ a,a≠0→ yb g w a = v'→ a = unsp g v':=by
          intro a ha0' heq;unfold yb at heq;unfold unsp;split_ifs at heq ⊢ <;> omega
        refine ⟨hk',?_⟩
        rcases hk.2 with h1 | h1
        · exact Or.inl (hsp _ ha0 (ea▸h1))
        · exact Or.inr (hsp _ hb0 (eb▸h1))
      · intro j hj
        simp only [Finset.mem_coe,zq,mem_filter,Finset.mem_range,hD'len] at hj ⊢;have hne_g : j≠g:=by
          intro heq;subst heq
          rcases hg_in with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rcases hj.2 with h3 | h3 <;>
            (unfold unsp at h3;split_ifs at h3 <;> omega)
        have hk_lt : (if j < g then j else j - 1) < D.length - 1:=by split_ifs <;> omega
        have hup : zs g (if j < g then j else j - 1) = j:=by unfold zs;split_ifs <;> omega
        obtain ⟨-,ea,eb⟩:=hops (if j < g then j else j - 1) (by rw [hup];exact hj.1);rw [ea,eb,hup];have hsp2 : yb g w (unsp g v') = v':=by unfold yb unsp;split_ifs <;> omega
        refine ⟨hk_lt,?_⟩
        rcases hj.2 with h1 | h1
        · exact Or.inl (by rw [h1,hsp2])
        · exact Or.inr (by rw [h1,hsp2])
      · intro k _;by_cases hkg : k < g
        · simp [zs,hkg]
        · simp [zs,hkg,show ¬ k + 1 < g by omega]
      · intro j hj
        simp only [Finset.mem_coe,zq,mem_filter,Finset.mem_range] at hj;have hne_g : j≠g:=by
          intro heq;subst heq
          rcases hg_in with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rcases hj.2 with h3 | h3 <;>
            (unfold unsp at h3;split_ifs at h3 <;> omega)
        by_cases hjg : j < g
        · simp [zs,hjg]
        · simp [zs,hjg,show ¬ j - 1 < g by omega];omega
  have hL' : Live 13 D':=by
    intro v' hv';rw [hfan' v' (by omega)]
    apply h.2.1 (unsp g v')
    rw [hD'len] at hv';unfold unsp;split_ifs <;> omega
  have hcomp' : z3 13 z22 D':=by
    intro x';have ho : unsp g (qc 13 D') = qc 14 D:=by
      unfold qc unsp;rw [hD'len];split_ifs <;> omega
    rw [hval' x' (qc 13 D') (by unfold qc;omega),ho,hc (y1 x'),z2n x']
  have hsupp' : ∀ v' < 13 + D'.length,∀ i : Fin 13,
      i∈supp 13 D' v'↔z09 i∈supp 14 D (unsp g v'):=by
    intro v' hv' i;have hsing : y1 (single i) = single (z09 i):=by
      funext v;simp only [y1,single,z09];split_ifs with h0 <;> simp [Fin.ext_iff] <;> omega
    simp only [mem_supp,hval' (single i) v' hv',hsing]
  have h9 : (⟨9,by omega⟩ : Fin 13)∈z1 13 D':=by
    rw [mem_ineligSet];intro v' hv9;have hv' : v' < 13 + D'.length:=yf hv9;rw [hfan' v' hv'];have h10m : (⟨10,by omega⟩ : Fin 14)∈supp 14 D (unsp g v'):=(hsupp' v' hv' ⟨9,by omega⟩).1 hv9;exact mem_ineligSet.mp h10 (unsp g v') h10m
  refine ⟨D',⟨hS',hL',hD'ne⟩,by omega,hcomp',h9,w - 1,?_,?_⟩
  · have hlt : w - 1 < 13 + D'.length:=by omega
    rw [hfan' (w - 1) hlt];have hu : unsp g (w - 1) = w:=by unfold unsp;split_ifs <;> omega
    rw [hu];exact hfw
  · ext i
    have hlt : w - 1 < 13 + D'.length:=by omega
    have hu : unsp g (w - 1) = w:=by unfold unsp;split_ifs <;> omega
    rw [hsupp' (w - 1) hlt i,hu,hsw];simp only [mem_insert,mem_singleton,z09,Fin.ext_iff];omega
theorem z3x {D : Dag} (hS : za 14 D) {g hgt u : ℕ}
    (hg_lt : g < D.length) (hh_lt : hgt < D.length) (hgh : g < hgt)
    (hg_eq : zq D 0 = {g}) (hh_eq : zq D (14 + g) = {hgt})
    (hht_true : tag D hgt = true)
    (hh_in : (opA D hgt = 14 + g∧opB D hgt = u)∨(opA D hgt = u∧opB D hgt = 14 + g)) :
    ∀ v,(0 : Fin 14)∈supp 14 D v→ v = 0∨v = 14 + g:=by
  have hno0 : ∀ j < D.length,j≠g→ opA D j≠0∧opB D j≠0:=by
    intro j hj hne
    constructor <;> intro e
    · exact hne (mem_singleton.mp (hg_eq▸mem_filter.mpr ⟨Finset.mem_range.mpr hj,Or.inl e⟩))
    · exact hne (mem_singleton.mp (hg_eq▸mem_filter.mpr ⟨Finset.mem_range.mpr hj,Or.inr e⟩))
  have hnog : ∀ j < D.length,j≠hgt→ opA D j≠14 + g∧opB D j≠14 + g:=by
    intro j hj hne
    constructor <;> intro e
    · exact hne (mem_singleton.mp (hh_eq▸mem_filter.mpr ⟨Finset.mem_range.mpr hj,Or.inl e⟩))
    · exact hne (mem_singleton.mp (hh_eq▸mem_filter.mpr ⟨Finset.mem_range.mpr hj,Or.inr e⟩))
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih=>
    intro hv
    by_cases hv14 : v < 14
    · have hs:=supp_input (n:=14) D ⟨v,hv14⟩
      rw [hs,mem_singleton] at hv;exact Or.inl (congrArg Fin.val hv).symm
    · have hvl:=yf hv
      obtain ⟨j,rfl⟩ : ∃ j,v = 14 + j:=⟨v - 14,by omega⟩;have hj : j < D.length:=by omega
      by_cases hjg : j = g
      · exact Or.inr (by omega)
      · exfalso
        by_cases hjh : j = hgt
        · subst j
          rw [yr hS hh_lt hht_true,mem_inter] at hv;have h0u : (0 : Fin 14)∈supp 14 D u:=by
            rcases hh_in with ⟨_,e⟩ | ⟨e,_⟩ <;> rw [← e];exact hv.2;exact hv.1
          have hult : u < 14 + hgt:=by
            obtain ⟨ha,hb,_⟩:=hS hgt hh_lt
            rcases hh_in with ⟨_,e⟩ | ⟨e,_⟩ <;> omega
          rcases ih u hult h0u with rfl | rfl
          · have hbad:=hno0 hgt hh_lt (by omega)
            rcases hh_in with ⟨_,e⟩ | ⟨e,_⟩
            · exact hbad.2 e
            · exact hbad.1 e
          · obtain ⟨_,_,hab⟩:=hS hgt hh_lt
            rcases hh_in with ⟨e1,e2⟩ | ⟨e1,e2⟩ <;> omega
        · obtain ⟨ha0,hb0⟩:=hno0 j hj hjg
          obtain ⟨hag,hbg⟩:=hnog j hj hjh;obtain ⟨ha,hb,_⟩:=hS j hj;rw [supp_gate hS j hj] at hv
          split_ifs at hv
          · rcases ih (opA D j) ha (mem_inter.mp hv).1 with e | e <;> tauto
          · rcases mem_union.mp hv with h1 | h1
            · rcases ih (opA D j) ha h1 with e | e <;> tauto
            · rcases ih (opB D j) hb h1 with e | e <;> tauto
set_option maxHeartbeats 400000 in
theorem z5x
    (hGp : ¬ ∃ D' : Dag,z0 13 D'∧D'.length≤ 22∧z3 13 z22 D')
    (hGpp : ¬ ∃ D'' : Dag,z0 12 D''∧D''.length≤ 20∧z3 12 z0h D'')
    (hC1 : ¬ ∃ D' : Dag,z0 13 D'∧D'.length≤ 23∧z3 13 z22 D'∧
      (⟨9,by omega⟩ : Fin 13)∈z1 13 D'∧
      ∃ w' : ℕ,2≤ zd D' w'∧supp 13 D' w' = {⟨3,by omega⟩,⟨4,by omega⟩})
    (hC2 : ¬ ∃ D : Dag,z0 14 D∧D.length≤ 24∧z3 14 v5 D∧
      (⟨0,by omega⟩ : Fin 14)∈z1 14 D∧
      (⟨10,by omega⟩ : Fin 14)∈z6 14 D∧
      (∀ w,(⟨0,by omega⟩ : Fin 14)∈supp 14 D w→
        ∀ c∈supp 14 D w,c.val = 0∨c.val = 4∨c.val = 5)) :
    ¬ ∃ D : Dag,z0 14 D∧D.length≤ 24∧z3 14 v5 D:=by
  rintro ⟨D,h,hlen,hc⟩
  have hpos : 0 < D.length:=List.length_pos_iff.mpr h.2.2;have hsupp0 : supp 14 D 0 = {0}:=supp_input (n:=14) D 0;have hsupp10 : supp 14 D 10 = {10}:=supp_input (n:=14) D 10;have hm0Gp_len : z0f.length = 14:=rfl;have hm0Gpp_len : zl.length = 14:=rfl
  have h0Gp : z8 (z2 13 z0f D D.length).1 0 = Sum.inl false:=by
    rw [zi 13 z0f D (Nat.zero_le D.length) (by omega)];rfl
  have h0Gpp : z8 (z2 12 zl D D.length).1 0 = Sum.inl true:=by
    rw [zi 12 zl D (Nat.zero_le D.length) (by omega)];rfl
  have h10Gpp : z8 (z2 12 zl D D.length).1 10 = Sum.inl false:=by
    rw [zi 12 zl D (Nat.zero_le D.length) (by omega)];rfl
  have hcompGpp : ∀ x'' : Fin 12→ Bool,val D (yo x'') (qc 14 D) = true↔qi z0h x'':=
    fun x''=>(hc (yo x'')).trans (z20 x'')
  have hnot_out_gpp : ∀ {v : ℕ} {b : Bool},
      z8 (z2 12 zl D D.length).1 v = Sum.inl b→ v≠qc 14 D:=
    fun hv=>not_const_out_of_red z5o z5z zl hm0Gpp_len vy h yo z19 hcompGpp hv
  have hcard4 : ∀ a b c d : ℕ,a < D.length→ b < D.length→ c < D.length→ d < D.length→
      a≠b→ a≠c→ a≠d→ b≠c→ b≠d→ c≠d→
      qp 12 zl D a = true→ qp 12 zl D b = true→
      qp 12 zl D c = true→ qp 12 zl D d = true→ False:=by
    intro a b c d ha hb hc2 hd hab hac had hbc hbd hcd da db dc dd
    let S : Finset ℕ:={a,b,c,d}
    have hSsub : S⊆(Finset.range D.length).filter (fun j=>qp 12 zl D j = true):=by
      intro x hx;simp only [S,mem_insert,mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> exact mem_filter.mpr ⟨Finset.mem_range.mpr ‹_›,‹_›⟩
    have hScard : S.card = 4:=by
      simp only [S,Finset.card_insert_of_notMem,mem_insert,mem_singleton,
        card_singleton,not_or,hab,hac,had,hbc,hbd,hcd,not_false_eq_true,and_self]
    exact hGpp (z4m h hc (by have:=card_le_card hSsub;omega) hlen)
  have hf0_pos : 1≤ zd D 0:=h.2.1 0 (by omega)
  by_cases hf0_ge2 : 2≤ zd D 0
  · apply hGp
    apply z3f h hc _ hlen
    have hsub : zq D 0⊆(Finset.range D.length).filter (fun j=>qp 13 z0f D j = true):=by
      intro j hj;exact mem_filter.mpr ⟨Finset.mem_range.mpr (Finset.mem_range.mp (mem_filter.mp hj).1),
        zv hj h0Gp⟩
    exact le_trans hf0_ge2 (card_le_card hsub)
  have hf0 : zd D 0 = 1:=by omega
  obtain ⟨g,hg_eq⟩:=card_eq_one.mp hf0;have hg_mem : g∈zq D 0:=hg_eq▸mem_singleton_self g;have hg_lt : g < D.length:=Finset.mem_range.mp (mem_filter.mp hg_mem).1
  by_cases htg : tag D g = true
  · apply hGp
    have hg_const : z8 (z2 13 z0f D D.length).1 (14 + g) = Sum.inl false:=
      gate_const_of_absorb hm0Gp_len h.1 hg_mem h0Gp (by rw [htg];decide)
    have hcompGp : ∀ x' : Fin 13→ Bool,val D (y1 x') (qc 14 D) = true↔qi z22 x':=
      fun x'=>(hc (y1 x')).trans (z2n x')
    have hm0okGp : ∀ r∈z0f,wb 13 r:=by
      intro r hr;simp only [z0f,List.mem_cons,List.mem_map,List.mem_range] at hr
      rcases hr with rfl | ⟨i,hi,rfl⟩
      · trivial
      · exact hi
    have hinitGp : ∀ (x' : Fin 13→ Bool) (i : Fin 14),refVal (List.ofFn x') (z8 z0f i.val) = y1 x' i:=by
      intro x' ⟨v,hv⟩
      cases v with
      | zero=>simp [z0f,z8,refVal,y1]
      | succ v=>
        have hv13 : v < 13:=by omega
        simp only [z0f,z8,List.getD_eq_getElem?_getD,List.getElem?_cons_succ,
          List.getElem?_map,List.getElem?_range hv13,Option.map_some,Option.getD_some,
          refVal,y1,Nat.succ_ne_zero,dite_false,Nat.add_sub_cancel]
        exact z3c x' ⟨v,hv13⟩
    have hne_out : 14 + g≠qc 14 D:=
      not_const_out_of_red grGp hneGp z0f hm0Gp_len hm0okGp h y1 hinitGp hcompGp hg_const
    obtain ⟨h1,hh1⟩:=card_pos.mp (h.2.1 (14 + g) (by unfold qc at hne_out;omega));have hh1_lt : h1 < D.length:=Finset.mem_range.mp (mem_filter.mp hh1).1;have hgh1 : g < h1:=by
      obtain ⟨ha,hb,_⟩:=h.1 h1 hh1_lt
      rcases (mem_filter.mp hh1).2 with e | e <;> omega
    have hsub : ({g,h1} : Finset ℕ)⊆(Finset.range D.length).filter (fun j=>qp 13 z0f D j = true):=by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx2
      · exact mem_filter.mpr ⟨Finset.mem_range.mpr hg_lt,zv hg_mem h0Gp⟩
      · rw [mem_singleton.mp hx2]
        exact mem_filter.mpr ⟨Finset.mem_range.mpr hh1_lt,zv hh1 hg_const⟩
    have hc2 : ({g,h1} : Finset ℕ).card = 2:=by rw [Finset.card_pair (by omega)]
    exact z3f h hc (by have:=card_le_card hsub;omega) hlen
  have hgt_false : tag D g = false:=Bool.eq_false_iff.mpr htg;have hg_in : ∃ w,(opA D g = 0∧opB D g = w)∨(opA D g = w∧opB D g = 0):=by
    rcases (mem_filter.mp hg_mem).2 with e | e
    · exact ⟨opB D g,Or.inl ⟨e,rfl⟩⟩
    · exact ⟨opA D g,Or.inr ⟨rfl,e⟩⟩
  obtain ⟨w,hg_in⟩:=hg_in;have hch0g : zn 14 D 0 (14 + g):=by
    refine Relation.ReflTransGen.single ⟨⟨by omega,by omega,?_⟩,hf0⟩
    rw [Nat.add_sub_cancel_left];exact (mem_filter.mp hg_mem).2
  have hsub_g : supp 14 D (14 + g)⊆({0,4,5} : Finset (Fin 14)):=
    z1s z6a h.1 hc 0 _ z5n (14 + g) (qk h.1 hch0g)
  have h0_in_g : (0 : Fin 14)∈supp 14 D (14 + g):=by
    rw [yq h.1 hg_lt hgt_false,mem_union]
    rcases hg_in with ⟨h1,_⟩ | ⟨_,h1⟩
    · left;rw [h1,hsupp0];simp
    · right;rw [h1,hsupp0];simp
  have hw_ne10 : w≠10:=by
    intro heq;have h10m : (10 : Fin 14)∈supp 14 D (14 + g):=by
      rw [yq h.1 hg_lt hgt_false,mem_union]
      rcases hg_in with ⟨_,h2⟩ | ⟨h2,_⟩
      · right;rw [h2,heq,hsupp10];simp
      · left;rw [h2,heq,hsupp10];simp
    have h10s:=hsub_g h10m;simp at h10s
  have hg_const_gpp : z8 (z2 12 zl D D.length).1 (14 + g) = Sum.inl true:=
    gate_const_of_absorb hm0Gpp_len h.1 hg_mem h0Gpp (by rw [hgt_false];decide)
  have hg_drop_gpp : qp 12 zl D g = true:=zv hg_mem h0Gpp;have hg_ne_out : 14 + g≠qc 14 D:=hnot_out_gpp hg_const_gpp;have hfg_pos : 1≤ zd D (14 + g):=h.2.1 (14 + g) (by unfold qc at hg_ne_out;omega);obtain ⟨k10,hk10⟩:=card_pos.mp (h.2.1 10 (by omega))
  have hk10_lt : k10 < D.length:=Finset.mem_range.mp (mem_filter.mp hk10).1;have hk10_drop : qp 12 zl D k10 = true:=zv hk10 h10Gpp;have hk10_ne_g : k10≠g:=by
    intro heq;subst heq
    rcases (mem_filter.mp hk10).2 with h1 | h1 <;> rcases hg_in with ⟨h2,h3⟩ | ⟨h2,h3⟩ <;> omega
  have two_const_reader : ∀ j v1 v2 b1 b2,j < D.length→ v1≠v2→
      j∈zq D v1→ j∈zq D v2→
      z8 (z2 12 zl D D.length).1 v1 = Sum.inl b1→
      z8 (z2 12 zl D D.length).1 v2 = Sum.inl b2→
      ∃ r c,r < D.length∧j < r∧r∈zq D (14 + j)∧
        z8 (z2 12 zl D D.length).1 (14 + j) = Sum.inl c∧
        qp 12 zl D r = true:=by
    intro j v1 v2 b1 b2 hj hne hr1 hr2 hv1 hv2;have hboth : ∃ c,z8 (z2 12 zl D D.length).1 (14 + j) = Sum.inl c:=by
      rcases (mem_filter.mp hr1).2 with e1 | e1 <;> rcases (mem_filter.mp hr2).2 with e2 | e2
      · exact absurd (e1.symm.trans e2) hne
      · exact gate_const_of_both hm0Gpp_len h.1 hj (e1▸hv1) (e2▸hv2)
      · exact gate_const_of_both hm0Gpp_len h.1 hj (e2▸hv2) (e1▸hv1)
      · exact absurd (e1.symm.trans e2) hne
    obtain ⟨c,hc2⟩:=hboth;have hne_out:=hnot_out_gpp hc2;obtain ⟨r,hr⟩:=card_pos.mp (h.2.1 (14 + j) (by unfold qc at hne_out;omega));have hr_lt : r < D.length:=Finset.mem_range.mp (mem_filter.mp hr).1;have hjr : j < r:=by
      obtain ⟨ha,hb,_⟩:=h.1 r hr_lt
      rcases (mem_filter.mp hr).2 with e | e <;> omega
    exact ⟨r,c,hr_lt,hjr,hr,hc2,zv hr hc2⟩
  by_cases hfg_ge2 : 2≤ zd D (14 + g)
  · obtain ⟨h1,hh1,h2,hh2,h12⟩:=one_lt_card.mp (show 1 < (zq D (14 + g)).card from hfg_ge2)
    have hh1_lt : h1 < D.length:=Finset.mem_range.mp (mem_filter.mp hh1).1;have hh2_lt : h2 < D.length:=Finset.mem_range.mp (mem_filter.mp hh2).1;have hgh1 : g < h1:=by
      obtain ⟨ha,hb,_⟩:=h.1 h1 hh1_lt;rcases (mem_filter.mp hh1).2 with e | e <;> omega
    have hgh2 : g < h2:=by
      obtain ⟨ha,hb,_⟩:=h.1 h2 hh2_lt;rcases (mem_filter.mp hh2).2 with e | e <;> omega
    have hd1 : qp 12 zl D h1 = true:=zv hh1 hg_const_gpp;have hd2 : qp 12 zl D h2 = true:=zv hh2 hg_const_gpp
    by_cases hk1 : k10 = h1
    · subst hk1
      obtain ⟨r,cr,hr_lt,h1r,hr_mem,h1c,hdr⟩:=
        two_const_reader k10 (14 + g) 10 true false hh1_lt (by omega) hh1 hk10 hg_const_gpp h10Gpp
      by_cases hr2 : r = h2
      · subst hr2
        obtain ⟨r',_,hr'_lt,h2r',_,_,hdr'⟩:=
          two_const_reader r (14 + g) (14 + k10) true cr hh2_lt (by omega) hh2 hr_mem hg_const_gpp h1c
        exact hcard4 g k10 r r' hg_lt hh1_lt hh2_lt hr'_lt (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          hg_drop_gpp hd1 hd2 hdr'
      · exact hcard4 g k10 h2 r hg_lt hh1_lt hh2_lt hr_lt (by omega) (by omega) (by omega) h12 (by omega) (Ne.symm hr2)
          hg_drop_gpp hd1 hd2 hdr
    · by_cases hk2 : k10 = h2
      · subst hk2
        obtain ⟨r,cr,hr_lt,h2r,hr_mem,h2c,hdr⟩:=
          two_const_reader k10 (14 + g) 10 true false hh2_lt (by omega) hh2 hk10 hg_const_gpp h10Gpp
        by_cases hr1 : r = h1
        · subst hr1
          obtain ⟨r',_,hr'_lt,h1r',_,_,hdr'⟩:=
            two_const_reader r (14 + g) (14 + k10) true cr hh1_lt (by omega) hh1 hr_mem hg_const_gpp h2c
          exact hcard4 g k10 r r' hg_lt hh2_lt hh1_lt hr'_lt (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            hg_drop_gpp hd2 hd1 hdr'
        · exact hcard4 g h1 k10 r hg_lt hh1_lt hh2_lt hr_lt (by omega) (by omega) (by omega) h12 (Ne.symm hr1) (by omega)
            hg_drop_gpp hd1 hd2 hdr
      · exact hcard4 g h1 h2 k10 hg_lt hh1_lt hh2_lt hk10_lt (by omega) (by omega) hk10_ne_g.symm h12 (Ne.symm hk1) (Ne.symm hk2)
          hg_drop_gpp hd1 hd2 hk10_drop
  have hfg : zd D (14 + g) = 1:=by omega
  obtain ⟨hgt,hh_eq⟩:=card_eq_one.mp hfg;have hh_mem : hgt∈zq D (14 + g):=hh_eq▸mem_singleton_self hgt;have hh_lt : hgt < D.length:=Finset.mem_range.mp (mem_filter.mp hh_mem).1;have hgh : g < hgt:=by
    obtain ⟨ha,hb,_⟩:=h.1 hgt hh_lt;rcases (mem_filter.mp hh_mem).2 with e | e <;> omega
  have hh_drop : qp 12 zl D hgt = true:=zv hh_mem hg_const_gpp
  by_cases hth : tag D hgt = false
  · have hh_const : z8 (z2 12 zl D D.length).1 (14 + hgt) = Sum.inl true:=
      gate_const_of_absorb hm0Gpp_len h.1 hh_mem hg_const_gpp (by rw [hth];decide)
    have hh_ne_out:=hnot_out_gpp hh_const;obtain ⟨r,hr⟩:=card_pos.mp (h.2.1 (14 + hgt) (by unfold qc at hh_ne_out;omega));have hr_lt : r < D.length:=Finset.mem_range.mp (mem_filter.mp hr).1;have hhr : hgt < r:=by
      obtain ⟨ha,hb,_⟩:=h.1 r hr_lt;rcases (mem_filter.mp hr).2 with e | e <;> omega
    have hr_drop : qp 12 zl D r = true:=zv hr hh_const;have hch0h : zn 14 D 0 (14 + hgt):=by
      refine Relation.ReflTransGen.tail hch0g ⟨⟨by omega,by omega,?_⟩,hfg⟩
      rw [Nat.add_sub_cancel_left];exact (mem_filter.mp hh_mem).2
    have hsub_h : supp 14 D (14 + hgt)⊆({0,4,5} : Finset (Fin 14)):=
      z1s z6a h.1 hc 0 _ z5n (14 + hgt) (qk h.1 hch0h)
    have hk10_ne_h : k10≠hgt:=by
      intro heq;subst heq;have h10m : (10 : Fin 14)∈supp 14 D (14 + k10):=by
        rw [yq h.1 hh_lt hth,mem_union]
        rcases (mem_filter.mp hk10).2 with e | e
        · left;rw [e,hsupp10];simp
        · right;rw [e,hsupp10];simp
      have h10s:=hsub_h h10m;simp at h10s
    by_cases hkr : k10 = r
    · subst hkr
      obtain ⟨r',_,hr'_lt,hrr',_,_,hdr'⟩:=
        two_const_reader k10 (14 + hgt) 10 true false hr_lt (by omega) hr hk10 hh_const h10Gpp
      exact hcard4 g hgt k10 r' hg_lt hh_lt hr_lt hr'_lt (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        hg_drop_gpp hh_drop hr_drop hdr'
    · exact hcard4 g hgt r k10 hg_lt hh_lt hr_lt hk10_lt (by omega) (by omega) hk10_ne_g.symm (by omega) hk10_ne_h.symm (Ne.symm hkr)
        hg_drop_gpp hh_drop hr_drop hk10_drop
  have hht_true : tag D hgt = true:=Bool.eq_true_of_not_eq_false hth;have hh_in : ∃ u,(opA D hgt = 14 + g∧opB D hgt = u)∨(opA D hgt = u∧opB D hgt = 14 + g):=by
    rcases (mem_filter.mp hh_mem).2 with e | e
    · exact ⟨opB D hgt,Or.inl ⟨e,rfl⟩⟩
    · exact ⟨opA D hgt,Or.inr ⟨rfl,e⟩⟩
  obtain ⟨u,hh_in⟩:=hh_in;have h0_only : ∀ v,(0 : Fin 14)∈supp 14 D v→ v = 0∨v = 14 + g:=
    z3x h.1 hg_lt hh_lt hgh hg_eq hh_eq hht_true hh_in
  have h0_inelig : (0 : Fin 14)∈z1 14 D:=by
    rw [mem_ineligSet];intro v hv
    rcases h0_only v hv with rfl | rfl <;> omega
  have h0_sub : ∀ v,(0 : Fin 14)∈supp 14 D v→
      ∀ c∈supp 14 D v,c.val = 0∨c.val = 4∨c.val = 5:=by
    intro v hv c hc0
    rcases h0_only v hv with rfl | rfl
    · rw [hsupp0,mem_singleton] at hc0
      left;exact congrArg Fin.val hc0
    · have hm:=hsub_g hc0
      simp only [mem_insert,mem_singleton,Fin.ext_iff] at hm;exact hm
  by_cases h10e : (10 : Fin 14)∈z6 14 D
  · exact hC2 ⟨D,h,hlen,hc,h0_inelig,h10e,h0_sub⟩
  have h10i : (10 : Fin 14)∈z1 14 D:=qt.mpr h10e;obtain ⟨e10,he10_lt,he10_tag,he10_src,he10_emp,he10_nbhd,he10_exit,_⟩:=
    ql z6a h hc (by decide : z6i 10 = true) h10i
  have h0_in_other : (0 : Fin 14)∈supp 14 D (src D (e10.1,!e10.2)):=
    he10_nbhd 0 (by decide)
  have he10_eq_h : e10.1 = hgt∧src D (e10.1,!e10.2) = 14 + g∧src D e10 = u:=by
    have hsrc_g : src D (e10.1,!e10.2) = 14 + g:=by
      rcases h0_only _ h0_in_other with h0eq | hgeq
      · exfalso
        have h4m : (4 : Fin 14)∈supp 14 D (src D (e10.1,!e10.2)):=
          he10_nbhd 4 (by decide)
        rw [h0eq,hsupp0,mem_singleton] at h4m;exact absurd (congrArg Fin.val h4m) (by omega)
      · exact hgeq
    have hmem_h : e10.1∈zq D (14 + g):=by
      simp only [zq,mem_filter,Finset.mem_range]
      refine ⟨he10_lt,?_⟩
      cases hs : e10.2
      · rw [hs] at hsrc_g;exact Or.inr (by simpa [src] using hsrc_g)
      · rw [hs] at hsrc_g;exact Or.inl (by simpa [src] using hsrc_g)
    have hgate : e10.1 = hgt:=mem_singleton.mp (hh_eq▸hmem_h);have hu_eq : src D e10 = u:=by
      rcases hh_in with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · cases hs : e10.2
        · exfalso;rw [hs,hgate] at hsrc_g;simp only [Bool.not_false,src,ite_true] at hsrc_g
          have:=(h.1 hgt hh_lt).2.2;omega
        · unfold src;rw [hs,hgate];simp only [ite_true];exact h2
      · cases hs : e10.2
        · unfold src;rw [hs,hgate];simp only [Bool.false_eq_true,ite_false];exact h1
        · exfalso;rw [hs,hgate] at hsrc_g;simp only [Bool.not_true,src,Bool.false_eq_true,ite_false] at hsrc_g
          have:=(h.1 hgt hh_lt).2.2;omega
    exact ⟨hgate,hsrc_g,hu_eq⟩
  have hsu : supp 14 D u = {10}:=he10_eq_h.2.2▸he10_src;have h4_in_g : (4 : Fin 14)∈supp 14 D (14 + g):=
    he10_eq_h.2.1▸he10_nbhd 4 (by decide)
  have h5_in_g : (5 : Fin 14)∈supp 14 D (14 + g):=
    he10_eq_h.2.1▸he10_nbhd 5 (by decide)
  have h0_not_w : (0 : Fin 14)∉supp 14 D w:=by
    intro h0w
    rcases h0_only w h0w with rfl | rfl
    · obtain ⟨_,_,hab⟩:=h.1 g hg_lt;rcases hg_in with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega
    · obtain ⟨ha,hb,_⟩:=h.1 g hg_lt;rcases hg_in with ⟨_,h2⟩ | ⟨h2,_⟩ <;> omega
  have hsw : supp 14 D w = {4,5}:=by
    have hor:=yq h.1 hg_lt hgt_false;have hor2 : supp 14 D (14 + g) = {0}∪supp 14 D w:=by
      rcases hg_in with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · rw [hor,h1,h2,hsupp0]
      · rw [hor,h1,h2,Finset.union_comm,hsupp0]
    ext x
    constructor
    · intro hx
      have hxg : x∈supp 14 D (14 + g):=by rw [hor2];exact Finset.mem_union_right _ hx
      have hxs:=hsub_g hxg;simp only [mem_insert,mem_singleton] at hxs ⊢
      rcases hxs with rfl | h45
      · exact absurd hx h0_not_w
      · exact h45
    · intro hx
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl | rfl
      · rw [hor2,mem_union,mem_singleton] at h4_in_g
        exact h4_in_g.resolve_left (by decide)
      · rw [hor2,mem_union,mem_singleton] at h5_in_g
        exact h5_in_g.resolve_left (by decide)
  by_cases hfw : 2≤ zd D w
  · exact hC1 (z65 h hc hlen hg_lt hh_lt hgh hf0 hg_mem hgt_false hg_in hfg hh_mem hh_in hsw hsu hfw h10i)
  · have hw_ge14 : 14≤ w:=by
      by_contra hlt
      have hs:=supp_input (n:=14) D ⟨w,by omega⟩;rw [hsw] at hs;have h4 : (4 : Fin 14)∈({⟨w,by omega⟩} : Finset (Fin 14)):=hs▸(by simp);have h5 : (5 : Fin 14)∈({⟨w,by omega⟩} : Finset (Fin 14)):=hs▸(by simp);simp only [mem_singleton,Fin.ext_iff] at h4 h5;omega
    have hw_lt_g : w < 14 + g:=by
      obtain ⟨ha,hb,_⟩:=h.1 g hg_lt;rcases hg_in with ⟨_,e⟩ | ⟨e,_⟩ <;> omega
    obtain ⟨jw,rfl⟩ : ∃ jw,w = 14 + jw:=⟨w - 14,by omega⟩;have hjw_lt : jw < D.length:=by omega
    have hfan_jw : zd D (14 + jw) = 1:=by
      have hpos_jw:=h.2.1 (14 + jw) (by omega);omega
    have hg_read_jw : g∈zq D (14 + jw):=by
      simp only [zq,mem_filter,Finset.mem_range]
      rcases hg_in with ⟨_,e⟩ | ⟨e,_⟩ <;> exact ⟨hg_lt,by tauto⟩
    have hjw_ne_k10 : jw≠k10:=by
      intro heq;subst heq;have h10_not : (10 : Fin 14)∉supp 14 D (14 + jw):=by rw [hsw];decide
      have h10_in : ∃ s : Bool,src D (jw,s) = 10:=by
        rcases (mem_filter.mp hk10).2 with e | e
        · exact ⟨false,by simpa [src] using e⟩
        · exact ⟨true,by simpa [src] using e⟩
      obtain ⟨s,hs⟩:=h10_in;have hexit : (jw,s)∈zk 14 D (zb 14 D {10}):=
        xf.mpr ⟨hjw_lt,by rw [hs,hsupp10];simp,h10_not⟩
      rw [he10_exit,mem_singleton] at hexit;have h1:=congrArg Prod.fst hexit;rw [he10_eq_h.1] at h1;omega
    have hthird : ∃ d3,d3 < D.length∧d3≠g∧d3≠hgt∧d3≠jw∧qp 12 zl D d3 = true:=by
      by_cases hkh : k10 = hgt
      · subst hkh
        obtain ⟨r,_,hr_lt,hhr,_,_,hdr⟩:=
          two_const_reader k10 (14 + g) 10 true false hh_lt (by omega) hh_mem hk10 hg_const_gpp h10Gpp
        exact ⟨r,hr_lt,by omega,by omega,by omega,hdr⟩
      · exact ⟨k10,hk10_lt,hk10_ne_g,hkh,hjw_ne_k10.symm,hk10_drop⟩
    obtain ⟨d3,hd3_lt,hd3g,hd3h,hd3jw,hd3_drop⟩:=hthird
    by_cases hjd : qp 12 zl D jw = true
    · exact hcard4 g hgt d3 jw hg_lt hh_lt hd3_lt hjw_lt (by omega) hd3g.symm (by omega) hd3h.symm (by omega) hd3jw
        hg_drop_gpp hh_drop hd3_drop hjd
    · have hnd : qp 12 zl D jw = false:=Bool.eq_false_iff.mpr hjd
      have hdrop3 : 3≤ ((Finset.range D.length).filter (fun j=>qp 12 zl D j = true)).card:=by
        let S : Finset ℕ:={g,hgt,d3}
        have hSsub : S⊆(Finset.range D.length).filter (fun j=>qp 12 zl D j = true):=by
          intro x hx;simp only [S,mem_insert,mem_singleton] at hx
          rcases hx with rfl | rfl | rfl <;> exact mem_filter.mpr ⟨Finset.mem_range.mpr ‹_›,‹_›⟩
        have hScard : S.card = 3:=by
          simp only [S,Finset.card_insert_of_notMem,mem_insert,mem_singleton,
            card_singleton,not_or,hd3g.symm,hd3h.symm,show g≠hgt by omega,not_false_eq_true,and_self]
        have:=card_le_card hSsub;omega
      exact hGpp (z2u h hc hlen hdrop3 hjw_lt hg_lt hnd hfan_jw hg_read_jw hg_const_gpp)
end Reduction
namespace G_Gp
open DagTools Resolution Compact GraphTools Reduction
def neigh:List Nat:=[4416,6272,3136,5632,2816,1408,5,34,49,24,44,22,11]
def edges:List (Nat×Nat):=[(0,6),(0,8),(0,12),(1,7),(1,11),(1,12),(2,6),(2,10),(2,11),(3,9),(3,10),(3,12),(4,8),(4,9),(4,11),(5,7),(5,8),(5,10)]
def goodB:Fin 13→Bool:=(fun _:Fin 13=>true)
def mBook:List Nat:=[63,122,157,216,270,330,396,551,610,645,774,1043,1106,1169,1539,1858,2089,2152,2185,2504,2593,3713,4148,4208,4244,4644,4996,5328,6752,8128]
theorem gr:zc (z4 neigh) (fun v=>goodB v=true):=by unfold zc;decide +kernel
theorem edgesOk:∀ q∈edges,∃ hu:q.1<13,∃ hv:q.2<13,z4 neigh ⟨q.1,hu⟩ ⟨q.2,hv⟩:=by decide +kernel
theorem adjE:∀ e:Fin 18,z4 neigh (zh 13 edges false e.val) (zh 13 edges true e.val):=by decide +kernel
theorem deg3:∀ j:Fin 13,(z9 neigh Finset.univ j).card≤3:=by decide +kernel
theorem girth6:∀ i j:Fin 13,i≠j→(z9 neigh Finset.univ i∩z9 neigh Finset.univ j).card≤1:=by decide +kernel
theorem hdeg2:∀ u v:Fin 13,z4 neigh u v→∃ a,z4 neigh u a∧a≠v:=by decide +kernel
theorem cover {D:Dag} (h:z0 13 D) (hc:z3 13 (z4 neigh) D):∀ u v:Fin 13,z4 neigh u v→u∈z6 13 D∨v∈z6 13 D:=fun u v huv=>wu gr h hc rfl rfl huv (hdeg2 u v huv)
def permLists:List (List Nat×List Nat):=[([0,1,2,3,4,5,6,7,8,9,10,11,12],[0,1,2,3,4,5,6,7,8,9,10,11,12]),([2,1,0,4,3,5,6,7,10,9,8,12,11],[2,1,0,4,3,5,6,7,10,9,8,12,11]),([2,5,0,3,4,1,6,7,11,9,12,8,10],[2,5,0,3,4,1,6,7,11,9,12,8,10]),([0,5,2,4,3,1,6,7,12,9,11,10,8],[0,5,2,4,3,1,6,7,12,9,11,10,8]),([0,3,2,1,5,4,6,9,8,7,11,10,12],[0,3,2,1,5,4,6,9,8,7,11,10,12]),([2,4,0,1,5,3,6,9,10,7,12,8,11],[2,3,0,5,1,4,6,9,11,7,8,12,10]),([2,3,0,5,1,4,6,9,11,7,8,12,10],[2,4,0,1,5,3,6,9,10,7,12,8,11]),([5,2,1,3,4,0,7,6,8,9,12,11,10],[5,2,1,3,4,0,7,6,8,9,12,11,10]),([5,0,1,4,3,2,7,6,10,9,11,12,8],[1,2,5,4,3,0,7,6,12,9,8,10,11]),([1,0,5,3,4,2,7,6,11,9,10,8,12],[1,0,5,3,4,2,7,6,11,9,10,8,12]),([1,2,5,4,3,0,7,6,12,9,8,10,11],[5,0,1,4,3,2,7,6,10,9,11,12,8]),([5,3,1,2,0,4,7,9,8,6,11,12,10],[4,2,3,1,5,0,9,6,8,7,12,10,11]),([5,4,1,0,2,3,7,9,10,6,12,11,8],[3,2,4,5,1,0,9,6,12,7,8,11,10]),([1,3,5,0,2,4,7,9,11,6,8,10,12],[3,0,4,1,5,2,9,6,10,7,11,8,12]),([1,4,5,2,0,3,7,9,12,6,10,8,11],[4,0,3,5,1,2,9,6,11,7,10,12,8]),([4,2,3,1,5,0,9,6,8,7,12,10,11],[5,3,1,2,0,4,7,9,8,6,11,12,10]),([3,0,4,1,5,2,9,6,10,7,11,8,12],[1,3,5,0,2,4,7,9,11,6,8,10,12]),([4,1,3,2,0,5,9,7,8,6,10,12,11],[4,1,3,2,0,5,9,7,8,6,10,12,11])]
theorem autsOk:permLists.all (wd 13 neigh)=true:=by decide +kernel
def permOf (k:Nat):Equiv.Perm (Fin 13):=va (neigh:=neigh) permLists autsOk (by decide) k
theorem autoOf (k:Nat):auto neigh (permOf k):=z1b (neigh:=neigh) permLists autsOk (by decide) k
theorem permVal (k:Nat) (i:Fin 13):(permOf k i).val=(permLists.getD k (permLists.getD 0 ([],[]))).1.getD i.val 0:=z06 (neigh:=neigh) permLists autsOk (by decide) k i
def wSpecs:List wn:=[(7,6144,7,2,1,51969,1102087<<<147),(56,1280,56,2,1,43013,51942262275<<<104),(1856,44,1856,3,2,340650,86311696762921<<<26),(320,1,320,1,0,0,4148),(1152,32,1152,1,0,0,135<<<66),(2560,16,2560,1,0,0,135<<<53),(9,4096,9,1,0,0,305<<<157),(18,2048,18,1,0,0,99<<<145),(36,1024,36,1,0,0,27<<<133),(2496,22,2496,3,2,270779,0x227000104e068000),(3712,22,3712,3,2,270779,0x10e00001ea068000),(4160,1,4160,1,0,0,270),(384,32,384,1,0,0,1043<<<65),(1536,8,1536,1,0,0,1037<<<41),(4736,10,4736,2,1,12556,573395330998272),(20,2048,20,1,0,0,165<<<144),(1216,36,1216,2,1,21002,0x870000000829<<<26),(2112,4,2112,1,0,0,1043<<<26),(2624,20,2624,2,1,16907,18119394323<<<26),(3328,20,3328,2,1,16907,18488492093<<<27),(4864,9,4864,2,1,12300,573395313885306),(6,2048,6,1,0,0,27<<<146),(13,5120,13,2,1,51715,4638900487<<<134),(33,256,33,1,0,0,27<<<107),(42,5120,42,2,1,51715,19612566565<<<132),(896,48,896,2,1,21512,8546345<<<52),(4480,3,4480,2,1,4108,17113210),(4992,11,4992,3,2,200908,573395330998394),(5184,5,5184,2,1,8198,140190417166),(5312,11,5312,3,2,200908,302915470565646),(6144,2,6144,1,0,0,1286144),(6720,11,6720,3,2,200908,573395315171598),(19,2304,19,2,1,47108,27212912787725<<<107),(52,1280,52,2,1,43013,22145926659<<<104),(6208,3,6208,2,1,4108,1286414),(7424,11,7424,3,2,200908,302915454738554),(3,4096,3,1,0,0,27<<<159),(10,4096,10,1,0,0,645<<<156),(12,1024,12,1,0,0,305<<<131),(14,3072,14,2,1,47618,9579041<<<130),(17,256,17,1,0,0,305<<<105),(40,1024,40,1,0,0,645<<<130),(48,256,48,1,0,0,645<<<104),(768,16,768,1,0,0,2089<<<52),(1088,4,1088,1,0,0,2089<<<26),(1280,32,1280,1,0,0,157<<<65),(2176,2,2176,1,0,0,33980416),(3200,6,3200,2,1,8459,8221261824),(3584,12,3584,2,1,12810,16990269<<<27),(4224,2,4224,1,0,0,17113088),(4608,8,4608,1,0,0,1043<<<39),(21,2304,21,2,1,47108,22677427323149<<<107),(25,4352,25,2,1,51200,0xc18000000000489<<<106),(26,6144,26,2,1,51969,5311625<<<145),(28,3072,28,2,1,47618,12610081<<<130),(35,4352,35,2,1,51200,0x630000000000425<<<106),(37,1280,37,2,1,43013,11072963113<<<105),(38,3072,38,2,1,47618,9578633<<<130),(41,1280,41,2,1,43013,25971130921<<<105),(50,2304,50,2,1,47108,0xc60000000889<<<104),(448,33,448,2,1,20488,0x8260000000000001034),(832,17,832,2,1,16392,0x8290000000001034),(1344,5,1344,2,1,8198,140190421044),(1600,12,1600,2,1,12810,33982505<<<26),(1664,40,1664,2,1,21258,4529849357<<<41),(1792,24,1792,2,1,17161,4279309<<<41),(2240,6,2240,2,1,8459,70028525568),(2304,16,2304,1,0,0,551<<<52),(2368,5,2368,2,1,8198,69994549300),(2432,18,2432,2,1,16651,0x2270000002068000),(2688,18,2688,2,1,16651,0x10e0000002068000),(3072,4,3072,1,0,0,61<<<27),(4288,3,4288,2,1,4108,17113358),(4352,1,4352,1,0,0,122),(4672,9,4672,2,1,12300,573395313885454),(5120,8,5120,1,0,0,551<<<39),(5248,10,5248,2,1,12556,302915470565376),(6656,10,6656,2,1,12556,573395315171328)]
def wts:=wSpecs.map vp
theorem wRows:wSpecs.all (vc 13 neigh goodB 0)=true:=by decide +kernel
def poss (c m:Nat):=z0r 13 edges wts 0 0 0 c m
def orbsCap:List Nat:=[31,63,88,122,200,216,330,704,4032,7616,8128]
def orbsM1:List Nat:=[63,216,8128]
def mapCap:List (Nat×Nat×Nat):=[(31,0,31),(47,4,31),(55,6,31),(59,9,31),(61,2,31),(62,7,31),(63,0,63),(88,0,88),(98,4,88),(122,0,122),(133,15,88),(152,7,88),(157,7,122),(200,0,200),(208,1,200),(216,0,216),(330,0,330),(396,7,330),(517,17,88),(546,11,88),(551,11,122),(578,4,200),(608,5,200),(610,4,216),(641,16,200),(644,15,200),(645,15,216),(704,0,704),(774,11,330),(1106,1,330),(1169,10,330),(1539,13,330),(2152,2,330),(2185,9,330),(2593,14,330),(4032,0,4032),(4208,3,330),(4244,8,330),(4644,12,330),(6080,1,4032),(7104,2,4032),(7616,0,7616),(7872,3,4032),(8000,4,7616),(8064,15,7616),(8128,0,8128)]
def mapM1:List (Nat×Nat×Nat):=[(63,0,63),(216,0,216),(610,4,216),(645,15,216),(8128,0,8128)]
def survCap:=mapCap.map Prod.fst
def survM1:=mapM1.map Prod.fst
theorem mapCapOk:mapCap.all (fun t=>(List.finRange 13).all (fun i=>t.1.testBit i.val==t.2.2.testBit ((permLists.getD t.2.1 (permLists.getD 0 ([],[]))).1.getD i.val 0)))=true:=by decide +kernel
theorem survCapCov:survCap.all (fun m=>mapCap.any (fun t=>t.1==m&&orbsCap.contains t.2.2))=true:=by decide +kernel
theorem mapM1Ok:mapM1.all (fun t=>(List.finRange 13).all (fun i=>t.1.testBit i.val==t.2.2.testBit ((permLists.getD t.2.1 (permLists.getD 0 ([],[]))).1.getD i.val 0)))=true:=by decide +kernel
theorem survM1Cov:survM1.all (fun m=>mapM1.any (fun t=>t.1==m&&orbsM1.contains t.2.2))=true:=by decide +kernel
def survTest (m:Nat):=!(poss 10 m)||survCap.contains m
theorem sc0:∀ j:Fin 2048,survTest (0+j.val)=true:=by decide +kernel
theorem sc1:∀ j:Fin 2048,survTest (2048+j.val)=true:=by decide +kernel
theorem sc2:∀ j:Fin 2048,survTest (4096+j.val)=true:=by decide +kernel
theorem sc3:∀ j:Fin 2048,survTest (6144+j.val)=true:=by decide +kernel
theorem allSurv (m:Fin 8192):survTest m.val=true:=by
  let j:Fin 2048:=⟨m.val%2048,Nat.mod_lt _ (by decide)⟩
  by_cases q0:m.val/2048=0
  · have e:m.val=0+j.val:=by dsimp [j];omega
    rw [e];exact sc0 j
  by_cases q1:m.val/2048=1
  · have e:m.val=2048+j.val:=by dsimp [j];omega
    rw [e];exact sc1 j
  by_cases q2:m.val/2048=2
  · have e:m.val=4096+j.val:=by dsimp [j];omega
    rw [e];exact sc2 j
  by_cases q3:m.val/2048=3
  · have e:m.val=6144+j.val:=by dsimp [j];omega
    rw [e];exact sc3 j
  omega
theorem m1List:survCap.all (fun m=>!(poss 9 m)||survM1.contains m)=true:=by decide +kernel
theorem m2List:survCap.all (fun m=>!(poss 8 m))=true:=by decide +kernel
theorem poss_of {D:Dag} (h:z0 13 D) (hc:z3 13 (z4 neigh) D) (c m:Nat) (enc:(mask m:Finset (Fin 13))=z1 13 D) (lim:zu 13 D≤c):poss c m=true:=by
  obtain ⟨b,hb⟩:=zz gr h.1 hc (fun _ _=>rfl);have hbase:=z0g h.1 b hb
  exact z05 (cover h hc) edgesOk (by decide) (by decide) (by simp [mask]) (by simp [mask]) (by omega) (fun r hr sub=>by rw [wts,List.mem_map] at hr;obtain ⟨s,hs,rfl⟩:=hr;exact v3 gr h hc (fun _ _=>rfl) (fun h=>absurd rfl h) s (List.all_eq_true.mp wRows _ hs) sub) enc lim
theorem noTwo_0 {D:Dag} (h:z0 13 D) (hc:z3 13 (z4 neigh) D) (tight:zu 13 D≤(z6 13 D).card) (hv:(0:Fin 13)∈z1 13 D):False:=by
  have w2:=x5 gr h hc (fun _ _=>rfl) tight;obtain ⟨P,hp⟩:=xx (m:=18) gr h hc adjE
  let ae:=z5g gr h hc hp hv;let ps:=z5f gr h hc hp hv;let cp:=couple hp w2;let ex:=yg gr h hc hp w2
  have c0:=ae false 0 2 (by decide)
  have c1:=ps false 0 5 (by decide)
  have c2:=ps false 0 11 (by decide)
  have c3:=cp false 9 10 11 (by decide)
  have c4:=cp true 7 10 17 (by decide)
  have c5:=cp true 4 8 14 (by decide)
  have c6:=cp true 2 5 11 (by decide)
  have c7:=ex false 4 5 14 11 7 (by decide)
  have c8:=ex false 7 8 17 4 6 (by decide)
  have c9:=ex false 7 8 17 14 6 (by decide)
  have c10:=ex false 10 11 7 5 9 (by decide)
  have c11:=ex false 10 11 17 5 9 (by decide)
  have c12:=ex true 7 10 8 9 5 (by decide)
  have c13:=ex true 2 5 0 4 3 (by decide)
  have c14:=ex true 2 11 0 9 1 (by decide)
  have c15:=ex true 2 11 0 10 1 (by decide)
  clear h hc hp w2 tight hv ae ps cp ex;grind (splits:=0) only
theorem noTwo_6 {D:Dag} (h:z0 13 D) (hc:z3 13 (z4 neigh) D) (tight:zu 13 D≤(z6 13 D).card) (hv:(6:Fin 13)∈z1 13 D):False:=by
  have w2:=x5 gr h hc (fun _ _=>rfl) tight;obtain ⟨P,hp⟩:=xx (m:=18) gr h hc adjE
  let ae:=z5g gr h hc hp hv;let ps:=z5f gr h hc hp hv;let cp:=couple hp w2;let ex:=yg gr h hc hp w2
  have c0:=ae true 0 6 (by decide)
  have c1:=ps true 0 8 (by decide)
  have c2:=ps true 0 11 (by decide)
  have c3:=ps true 0 16 (by decide)
  have c4:=ps true 0 17 (by decide)
  have c5:=cp false 6 7 8 (by decide)
  have c6:=cp false 15 16 17 (by decide)
  have c7:=cp true 1 12 16 (by decide)
  have c8:=cp true 7 10 17 (by decide)
  have c9:=cp true 4 8 14 (by decide)
  have c10:=cp true 2 5 11 (by decide)
  have c11:=ex false 0 2 6 5 8 (by decide)
  have c12:=ex false 1 2 16 5 6 (by decide)
  have c13:=ex false 4 5 14 2 7 (by decide)
  have c14:=ex false 6 7 0 10 11 (by decide)
  have c15:=ex false 6 7 0 17 11 (by decide)
  have c16:=ex false 6 8 0 4 10 (by decide)
  have c17:=ex false 7 8 10 14 6 (by decide)
  have c18:=ex false 10 11 7 2 9 (by decide)
  have c19:=ex false 10 11 7 5 9 (by decide)
  have c20:=ex false 12 14 1 4 9 (by decide)
  have c21:=ex false 12 14 1 8 9 (by decide)
  have c22:=ex false 12 14 16 4 9 (by decide)
  have c23:=ex false 16 17 1 10 7 (by decide)
  have c24:=ex false 16 17 12 10 7 (by decide)
  have c25:=ex true 12 16 14 15 0 (by decide)
  have c26:=ex true 7 17 6 15 3 (by decide)
  have c27:=ex true 7 17 6 16 3 (by decide)
  have c28:=ex true 7 17 8 15 3 (by decide)
  have c29:=ex true 7 17 8 16 3 (by decide)
  clear h hc hp w2 tight hv ae ps cp ex;rcases c5 with h1|h1|h1
  · rcases c7 with h2|h2|h2
    · rcases c8 with h3|h3|h3 <;> grind (splits:=0) only
    · grind (splits:=0) only
    · grind (splits:=0) only
  · grind (splits:=0) only
  · grind (splits:=0) only
theorem side_63 {D:Dag} (h:z0 13 D) (hc:z3 13 (z4 neigh) D) (z:qd 13 D≤1) (eq:(mask 63:Finset (Fin 13))=z1 13 D):11≤zu 13 D:=yc gr h hc (fun _ _=>rfl) deg3 girth6 z (mask 8128) (mask 63) 11 (0:Fin 13) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) eq
theorem side_8128 {D:Dag} (h:z0 13 D) (hc:z3 13 (z4 neigh) D) (z:qd 13 D≤1) (eq:(mask 8128:Finset (Fin 13))=z1 13 D):10≤zu 13 D:=yc gr h hc (fun _ _=>rfl) deg3 girth6 z (mask 63) (mask 8128) 10 (8:Fin 13) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) eq
def privList:List z0v:=[(31,6400,0,19,19,6400,[0,0,0,0,0,0,0,0,6752,0,0,4996,2504]),(4032,53,256,3136,3392,49,[4148,0,0,0,551,157,0,0,0,0,0,0,0]),(7616,15,4096,3136,7232,11,[270,157,0,551,0,0,0,0,0,0,0,0,0]),(8128,31,6144,1856,8128,0,[0,0,0,0,0,0,0,0,0,0,0,0,0])]
theorem privsOk:privList.all (vr 13 neigh 8191 0 11)=true:=by decide +kernel
theorem pv {D:Dag} (h:z0 13 D) (hc:z3 13 (z4 neigh) D) (z:qd 13 D=0) (I idx:Nat) (hidx:idx<privList.length) (hI:(privList[idx]'hidx).1=I) (eq:(mask I:Finset (Fin 13))=z1 13 D):11≤zu 13 D:=wh (w0:=0) (goodMask:=8191) (target:=11) gr h hc (fun _ _=>rfl) (fun _ _=>rfl) girth6 (fun h=>absurd rfl h) z (privList[idx]'hidx) (hI.symm ▸ eq) (List.all_eq_true.mp privsOk _ (List.getElem_mem hidx))
theorem cd0 {D:Dag} (h:z0 13 D) (hc:z3 13 (z4 neigh) D) (z:qd 13 D=0) (bp:zu 13 D=10) (I k:Nat) (eq:(mask I:Finset (Fin 13))=z1 13 D) (vars:List Nat) (steps:List xe) (hcard:(mask I:Finset (Fin 13)).card+10=13+k) (hAll:vars.all (fun v=>decide (v<13))=true∧steps.all (yh 13 neigh 8191 I 0 vars)=true∧yk (if 0==0 then 2^k else 2^(k-1)) 0 vars (fun _=>0) steps=true):False:=xc (k:=k) (w0:=0) (goodMask:=8191) (I:=I) (drop:=0) (bpVal:=10) gr h hc (fun _ _=>rfl) (fun _ _=>rfl) bp eq hcard (fun h=>absurd rfl h) (fun P hP i hi hg _=>wy gr h hc z (mask P) hP i ((fun _ _=>rfl) i hg) (eq ▸ hi)) vars steps hAll
def sa0:Array (List Nat):=zj yy [0x14944940541454541454104010480c48088808884848480840804040400050,0x2c2c680a8a84a80682868682864a4646464246008a00602c18681854090,0x2420482040787225112512115c854445444457205110510115ec08ac2cac6c6c50,0x13ade46c682c40eb790b122d5c4b570151005102d5e4a048a0487879181218111e1d0,0x1292200a488201d6040758001d62ca864a8494a7b1a191a11529ec286428414a723ade86c50,0x4250098025ba0928092509ba38235232552e0554b80552e0953a8154ea0153a82292210,0x28f603d48e513940e5239acd603568d603144c5231403510d483520950,0x93514d653604d41252454515b45a9160454105141490523d44f5b3d90,0x605581820608141951654995561818506189551556556055414525190,0x20c4525147441d1064399201460502151854a152814c]
def st0:Array (List Nat):=zj (fun x=>6+9*(x&&&63)) [0x2204421c083e086c38106410b8214042408401078302058209040e08141018201050,0x251202239102218241047e08f47010ec11b8e021a8233046208bc116822b140427140424050,0x381c82251b02371b0233984b619a8cc11a0cc1190c01188c01178b41170b411549e490cb05408ac5408a44e08a04e089848090,0x4a24024924021ca402472282462282442102432102419fcf21915041200fc11f0fc11e8f011d8f011d4e66d0c3a7408a072090,0x32a7823127822fa7022e27024da652e196134115d3410753411493011453011c130106d3011312c112d2c11b92c124516850d0,0xad55aa4322ab02402a823eaa823d2a023baa0253a95461a514c124d4c123948123548122144121d4412853e9d0cd6a008d0a0090,0xbd002e835ca551eb21c0ab94aa25643815728f448d96429197012dcd263580a055b9a4bab0140ab7319756026141cb6096a5929ab8382ad4b24d5707055a94c9aae0d0a0e5a04b31e118358838541abc1c200d0,0xdf1937036db65ae1b5414da0c1ada09aa086c06d503358368822568348311b419c1b2596cd0c1ac80986c56386296104c15faec35e811801af404be0d0,0xf705eaf37686f1213d0322bd0278901e41a05dcf20de23e76067b763b8373ba5d61835cc1395c6dd0dbe3a72063972048f7038836f8d1c41a25b8e00d0,0x37c62341c4e2b170c53120a1e08561d100c270e86070b84c1431cc28246c1a101a1e09060e06084605000dfefd7c86fb183f837d8b9f81bec58f80d0,0x96b29b01cb598d60e36bc95072b62490395b1a4c1c3579280e52c48a072963458391c964e18a64414863f190e3a1e90061d90051d0c478338c6a3c1c742d180d0,0x2231c9b07378a49039bc5a4c1c1df5340e6af68107016a4c8399b8a101ccdb9040dc2f09806ef6f4c0398b61d01cc5acea0da6f097072f653a0397b31d41b3dbd2c0d0,0xa16eb03098c58d074298834298b6d92e81172385923845c8e164a5480a7f5591436eccdc03911be0bc413aa6cdc1c4d872395892361cae2c22f417d831d050,0x118179914248a9d101b5411cccc20702b5570713420716aae4c080e1404b7580a0c221853e5c0cb]
def sr0_0:List Nat:=zg w7 [0x4a4d2494a38a97491526920a5d24149a49d6523ace2755a44e9b481d56903a6d25a948b538962a912c152058aa40b0548f0521e6124394244798488e50901e6120394244529084a92105522212a4441548084a9010553632b00d802c01442a00d046801402900c80240104180db569aa0a42500a845400a054a82548ea4322009000804001000003f,0x1223a447464274a40748d82c0d9280d919023221c083885081052808528005221ba7905d3c42e9f740c2128790143c40a1e500c212579012bc4095e4a0c0ba704138149caa598954b40ab496a15652d40ad25a81594b52a746256ce944ac9d2855b3a50ab274a056ce940ac9d28a483115290a2289214254a4284a2485015290a028921403a988027551002eaa201d502013aa84017550800eaa101d500013aa80017550000eaa528a4a5d27f,0x6549cc149524a3a62a3e80a3e8b41f3d20f98a0ea020ea2d06cc5065010651473662732807329080531807408074830298b03a0303a4302863042a5048a08d46090060954209002093302662c40a0c4800c495812b148ab2482b2520205249c3249cb229cb209c928230d92322463b1464a1465b0464a04648409089f0d11f223e2b13e5a13e4b03e5a03e4743f,0x160c4c60cd020cd03]
theorem sic0_0:ze (n:=13) (m:=18) neigh edges goodB false true 0 1 216 mBook sa0 (zr 9 st0) 0 sr0_0=true:=by decide +kernel
def srs0_0:List Nat:=zg (fun x=>9+8*(1+(x&&&511))) [0xb07edcd996c43431ad7528d7af2a0fb00f355f385b3488b6cd8e068c5e37d5c75c079daca02a1d2a815f5ede814100df80c812e75330171916f9b780d77307b8d831fab2a7613222464651f43424bd3d4600e0cceadc4a69d7363d2c2250b101132b311a5249281c80919198851d19109410a0989ed4d05251a2c2ce2422a40c27522c502a69d04ecf4d0495a916261328814b1a0a845a8980a5c96648a5f434b3f8b469062840c767eb1b487b3b0cc7877867c7579100fc7c6af09595759d83f3c3bdae3e33c8807bb03565b54ce8e5032958f16012b2daae7e7ca805335f385e375a02a04b1e4cc15cde42ddcc419ee0cac79c83e1205fc645c5a140d1b17123a38371c06304b32412d4602ba53d4df554f5fcdcd61e04e0484615583dd29ea2f6aafe6e6b0b02702422b01ae2e0de040200e406929190151413930352515006858552819b]
theorem sro0_0:zo (zr 9 st0) 8 192 srs0_0=true:=by decide +kernel
theorem scf0:zf (zr 9 st0) 219 201 (digits 8 11 0x5d368ab6d9cd1e06dad5c7) 0=true:=by decide +kernel
def sa1:Array (List Nat):=zj yy [0x42b770b100b100adec08ac06c2c6c6c2c64a4646464246c20642050089010,0x1080488049607200410121011581c40100048004160772b102b120addc6c406c50,0x951b81546e0151b82486e0521b80486e08060810182000608266df06c459b791b1c0b1066de42c50,0x16949a5b658195965818516149850b094009002b034032706e05c1b80706e10,0x1cd47311ac427545d5b75a5d607541c517149c526d45b596d81b506950]
def st1:Array (List Nat):=zj (fun x=>6+8*(x&&&63)) [0xa090226240888782201e08706021a18085c5021314084410f043410b0424106041010300090,0x135250c3154c092920246480911082404208ecccac33e3a08f0e82393a08d8c82343208c4c822e2a08b0a82251f190d0,0x8d702205c08696825957550c996022056087550253514f0cf94823d5208e5482365008d5402315008b93822d4e090,0x1b4fcdd98e056d3f2f663815b4dcbcc1985026c09adb02696a160d9c16563610c559024b620919882456009018025f5d5b0ca5782265e090,0x62828987830e1432203850a860e14220837d7f810c05f0279041de1e830578760dc5cdd43017009bc9c85a05056f271b681415bc846da04856a6e090,0x24e127839f7e8c0e7e023837b949c0e75ca3039d748e0dde126839b727e0e6dd20039997910c566029510960d1e4a583950e900d06424838b8d8f0d0,0x6815e04541994d620e767c29d9f740d06651e48499950a1416d05b54826d3a09b53826d3b4e0ce]
def sr1_0:List Nat:=zg w7 [0x10203c4101e800c40058583a101ae0d989c1b40b9836a17246d40e60da81c91b52a366255c6d44a80da85571b50aa036a05406d490d989201b50a4036a049c6d4030188046051004c0a2018102023028402605080c08001181400130299b2933671672d22ccda419cb4833369580a4b20249620492c071590122b1024560382c8090588121594827b4904169109ed22105a4027b48041690b20d846c01602900c8024171598aa0ff,0xcb9b98b9aa039aa2dcccc5cc501cc512d6662d6280d628ec09d8ec5d9245d96c1d9241d93902722dc324dcb22dcb20dc9a81351660b066490664c409889085bc802de2016f0b0610a03e1]
theorem sic1_0:ze (n:=13) (m:=18) neigh edges goodB false true 0 1 330 mBook sa1 (zr 8 st1) 0 sr1_0=true:=by decide +kernel
def srs1_0:List Nat:=zg (fun x=>9+7*(1+(x&&&511))) [0x386c35eb9d406425d8a5bb35e4200f182a1c2750078976c586bc8401a72f9fd26ee346799c6a8f55b9ecb20167095f35a4fdc3b1f3366b96402ce0d9542c5b8b3e4c40165e46d0072e49174234254f935c059791ad65c9200de0753a35805529070d58093664b0a101ce031228f522344a31e2c2e4c82ca927efb1274ae4c82143f4d84c172ce52020c16c085cbe029526648a140e5e81ce]
theorem sro1_0:zo (zr 8 st1) 7 96 srs1_0=true:=by decide +kernel
theorem scf1:zf (zr 8 st1) 110 41 (digits 7 17 0xb584150c563a0c2750048877b75e4) 0=true:=by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem no_dag:¬∃ D:Dag,z0 13 D∧D.length≤22∧z3 13 (z4 neigh) D:=by
  rintro ⟨D,h,hlen,hc⟩
  have hsur:=xo h;have hsp:=x6 13 D;obtain ⟨m,enc⟩:=repr 13 (z1 13 D)
  have hok:poss 10 m.val=true:=poss_of h hc 10 m.val enc (by omega)
  have hmem:m.val∈survCap:=by have:=allSurv m;simpa [survTest,hok] using this
  have hge:9≤zu 13 D:=by by_contra hlt;have hp:=poss_of h hc 8 m.val enc (by omega);have:=List.all_eq_true.mp m2List _ hmem;simp [hp] at this
  by_cases hbpm1:zu 13 D=9
  · have hp1:=poss_of h hc 9 m.val enc hbpm1.le
    have hm1:=List.all_eq_true.mp m1List _ hmem;simp only [hp1,Bool.not_true,Bool.false_or,List.contains_iff_mem] at hm1
    obtain ⟨⟨mv,ai,rep⟩,htm,htb⟩:=List.any_eq_true.mp (List.all_eq_true.mp survM1Cov _ hm1)
    simp only [Bool.and_eq_true,beq_iff_eq,List.contains_iff_mem] at htb;rcases htb with ⟨hmveq,hrep⟩
    have hmv:(mask mv:Finset (Fin 13)).image (permOf ai)=mask rep:=zp _ _ _ (fun i=>by rw [permVal ai i];exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp mapM1Ok _ htm) i (List.mem_finRange i)))
    obtain ⟨h1,h2,_,h4,h5,h6⟩:=qu h hc (permOf ai) (autoOf ai)
    have eq':(mask rep:Finset (Fin 13))=z1 13 (z7 (permOf ai) D):=by rw [h6,←enc,←hmveq,hmv]
    simp only [orbsM1,List.mem_cons,List.not_mem_nil,or_false] at hrep
    rcases hrep with rfl|rfl|rfl
    · have:=side_63 h1 h2 (by omega) eq';omega
    · obtain ⟨j1,j2,_,j4,_,j6⟩:=qu h1 h2 (permOf 11) (autoOf 11)
      have el:=zm 13 (z7 (permOf 11) (z7 (permOf ai) D))
      have hci:(z1 13 (z7 (permOf 11) (z7 (permOf ai) D))).card=4:=by rw [j6,Finset.card_image_of_injective _ (permOf 11).injective,←eq'];decide +kernel
      exact noTwo_0 j1 j2 (by omega) (by rw [j6,←eq'];exact Finset.mem_image.mpr ⟨(4:Fin 13),by decide,Fin.ext (by rw [permVal 11];decide)⟩)
    · have:=side_8128 h1 h2 (by omega) eq';omega
  have hbp:zu 13 D=10:=by omega
  have hbz0:qd 13 D=0:=by omega
  obtain ⟨⟨mv,ai,rep⟩,htm,htb⟩:=List.any_eq_true.mp (List.all_eq_true.mp survCapCov _ hmem)
  simp only [Bool.and_eq_true,beq_iff_eq,List.contains_iff_mem] at htb;rcases htb with ⟨hmveq,hrep⟩
  have hmv:(mask mv:Finset (Fin 13)).image (permOf ai)=mask rep:=zp _ _ _ (fun i=>by rw [permVal ai i];exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp mapCapOk _ htm) i (List.mem_finRange i)))
  obtain ⟨h1,h2,_,h4,h5,h6⟩:=qu h hc (permOf ai) (autoOf ai)
  have eq':(mask rep:Finset (Fin 13))=z1 13 (z7 (permOf ai) D):=by rw [h6,←enc,←hmveq,hmv]
  simp only [orbsCap,List.mem_cons,List.not_mem_nil,or_false] at hrep
  rcases hrep with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · have:=pv h1 h2 (by omega) 31 0 (by decide) rfl eq';omega
  · have:=side_63 h1 h2 (by omega) eq';omega
  · obtain ⟨j1,j2,_,j4,_,j6⟩:=qu h1 h2 (permOf 11) (autoOf 11)
    have el:=zm 13 (z7 (permOf 11) (z7 (permOf ai) D))
    have hci:(z1 13 (z7 (permOf 11) (z7 (permOf ai) D))).card=3:=by rw [j6,Finset.card_image_of_injective _ (permOf 11).injective,←eq'];decide +kernel
    exact noTwo_0 j1 j2 (by omega) (by rw [j6,←eq'];exact Finset.mem_image.mpr ⟨(4:Fin 13),by decide,Fin.ext (by rw [permVal 11];decide)⟩)
  · exact cd0 h1 h2 (by omega) (by omega) 122 2 eq' [8,10,11] [(0,2504,2185,5,0,8,11,0,4),(0,1858,774,3,0,10,8,0,5),(0,2504,396,1,0,11,8,0,4),(3,3713,0,1,4,11,10,7,0)] (by decide +kernel) (by decide +kernel)
  · obtain ⟨j1,j2,_,j4,_,j6⟩:=qu h1 h2 (permOf 12) (autoOf 12)
    have el:=zm 13 (z7 (permOf 12) (z7 (permOf ai) D))
    have hci:(z1 13 (z7 (permOf 12) (z7 (permOf ai) D))).card=3:=by rw [j6,Finset.card_image_of_injective _ (permOf 12).injective,←eq'];decide +kernel
    exact noTwo_0 j1 j2 (by omega) (by rw [j6,←eq'];exact Finset.mem_image.mpr ⟨(3:Fin 13),by decide,Fin.ext (by rw [permVal 12];decide)⟩)
  · exact xj 10 gr h1 h2 adjE (fun _ _=>rfl) (by omega) (fun _=>by omega) (by omega) eq' (by decide +kernel) (fun h=>absurd rfl h) (fun h=>by cases h) (by decide) (by decide) sic0_0 sro0_0 scf0
  · exact xj 10 gr h1 h2 adjE (fun _ _=>rfl) (by omega) (fun _=>by omega) (by omega) eq' (by decide +kernel) (fun h=>absurd rfl h) (fun h=>by cases h) (by decide) (by decide) sic1_0 sro1_0 scf1
  · have el:=zm 13 (z7 (permOf ai) D);have c:(mask 704:Finset (Fin 13)).card=3:=by decide +kernel
    rw [←eq'] at el;exact noTwo_6 h1 h2 (by omega) (eq' ▸ (by decide:(6:Fin 13)∈mask 704))
  · have:=pv h1 h2 (by omega) 4032 1 (by decide) rfl eq';omega
  · have:=pv h1 h2 (by omega) 7616 2 (by decide) rfl eq';omega
  · have:=pv h1 h2 (by omega) 8128 3 (by decide) rfl eq';omega
end G_Gp
namespace G_Gpp
open DagTools Resolution Compact GraphTools Reduction
def neigh:List Nat:=[2368,3200,1600,2560,1280,896,5,34,49,44,22,11]
def edges:List (Nat×Nat):=[(0,6),(0,8),(0,11),(1,7),(1,10),(1,11),(2,6),(2,9),(2,10),(3,9),(3,11),(4,8),(4,10),(5,7),(5,8),(5,9)]
def goodB:Fin 12→Bool:=(fun _:Fin 12=>true)
def mBook:List Nat:=[63,122,157,216,270,330,396,531,594,657,834,1065,1128,1161,1480,1665,2100,2160,2196,2436,2768,3168,4032]
theorem gr:zc (z4 neigh) (fun v=>goodB v=true):=by unfold zc;decide +kernel
theorem edgesOk:∀ q∈edges,∃ hu:q.1<12,∃ hv:q.2<12,z4 neigh ⟨q.1,hu⟩ ⟨q.2,hv⟩:=by decide +kernel
theorem adjE:∀ e:Fin 16,z4 neigh (zh 12 edges false e.val) (zh 12 edges true e.val):=by decide +kernel
theorem deg3:∀ j:Fin 12,(z9 neigh Finset.univ j).card≤3:=by decide +kernel
theorem girth6:∀ i j:Fin 12,i≠j→(z9 neigh Finset.univ i∩z9 neigh Finset.univ j).card≤1:=by decide +kernel
theorem hdeg2:∀ u v:Fin 12,z4 neigh u v→∃ a,z4 neigh u a∧a≠v:=by decide +kernel
theorem cover {D:Dag} (h:z0 12 D) (hc:z3 12 (z4 neigh) D):∀ u v:Fin 12,z4 neigh u v→u∈z6 12 D∨v∈z6 12 D:=fun u v huv=>wu gr h hc rfl rfl huv (hdeg2 u v huv)
def permLists:List (List Nat×List Nat):=[([0,1,2,3,4,5,6,7,8,9,10,11],[0,1,2,3,4,5,6,7,8,9,10,11]),([2,5,0,3,4,1,6,7,10,11,8,9],[2,5,0,3,4,1,6,7,10,11,8,9]),([1,0,5,3,4,2,7,6,10,9,8,11],[1,0,5,3,4,2,7,6,10,9,8,11]),([5,2,1,3,4,0,7,6,8,11,10,9],[5,2,1,3,4,0,7,6,8,11,10,9]),([0,5,2,4,3,1,6,7,11,10,9,8],[0,5,2,4,3,1,6,7,11,10,9,8]),([2,1,0,4,3,5,6,7,9,8,11,10],[2,1,0,4,3,5,6,7,9,8,11,10]),([1,2,5,4,3,0,7,6,11,8,9,10],[5,0,1,4,3,2,7,6,9,10,11,8]),([5,0,1,4,3,2,7,6,9,10,11,8],[1,2,5,4,3,0,7,6,11,8,9,10]),([9,10,11,6,7,8,3,4,5,0,1,2],[9,10,11,6,7,8,3,4,5,0,1,2]),([11,8,9,6,7,10,3,4,1,2,5,0],[11,8,9,6,7,10,3,4,1,2,5,0]),([8,11,10,6,7,9,4,3,5,2,1,0],[11,10,9,7,6,8,3,4,0,5,2,1]),([9,8,11,7,6,10,3,4,2,1,0,5],[10,9,8,6,7,11,4,3,1,0,5,2]),([11,10,9,7,6,8,3,4,0,5,2,1],[8,11,10,6,7,9,4,3,5,2,1,0])]
theorem autsOk:permLists.all (wd 12 neigh)=true:=by decide +kernel
def permOf (k:Nat):Equiv.Perm (Fin 12):=va (neigh:=neigh) permLists autsOk (by decide) k
theorem autoOf (k:Nat):auto neigh (permOf k):=z1b (neigh:=neigh) permLists autsOk (by decide) k
theorem permVal (k:Nat) (i:Fin 12):(permOf k i).val=(permLists.getD k (permLists.getD 0 ([],[]))).1.getD i.val 0:=z06 (neigh:=neigh) permLists autsOk (by decide) k i
def wSpecs:List wn:=[(13,2560,13,2,1,47363,622854279<<<112),(448,33,448,2,1,20488,0x213000000000000834),(50,1280,50,2,1,43012,6643778697<<<96),(2624,5,2624,2,1,8198,17867735310),(10,2048,10,1,0,0,657<<<132),(17,256,17,1,0,0,141<<<99),(1088,4,1088,1,0,0,531<<<24),(2176,2,2176,1,0,0,4362240),(1664,6,1664,2,1,8458,2055421952),(12,512,12,1,0,0,135<<<112),(48,256,48,1,0,0,1161<<<96),(576,4,576,1,0,0,1065<<<24),(6,1024,6,1,0,0,27<<<123),(9,2048,9,1,0,0,297<<<133),(384,32,384,1,0,0,531<<<60),(2304,1,2304,1,0,0,122),(14,1536,14,2,1,43266,84195<<<113),(19,1280,19,2,1,43012,830472333<<<99),(33,256,33,1,0,0,27<<<99),(41,768,41,2,1,38917,4989225<<<97),(52,768,52,2,1,38917,1353345<<<96),(1344,5,1344,2,1,8198,8908703796),(1536,4,1536,1,0,0,61<<<25),(2432,3,2432,2,1,4107,4362362),(18,1024,18,1,0,0,99<<<122),(20,1024,20,1,0,0,165<<<121),(40,512,40,1,0,0,549<<<110),(320,1,320,1,0,0,2100),(640,32,640,1,0,0,135<<<61),(1152,2,1152,1,0,0,8601600),(1216,6,1216,2,1,8458,8917303296),(2112,1,2112,1,0,0,270),(3,2048,3,1,0,0,27<<<135),(7,3072,7,2,1,47617,288903<<<124),(21,1280,21,2,1,43012,692060301<<<99),(25,2304,25,2,1,47104,1791001362531<<<101),(26,3072,26,2,1,47617,1705569<<<122),(28,1536,28,2,1,43266,106851<<<113),(36,512,36,1,0,0,27<<<111),(42,2560,42,2,1,47363,2755658277<<<110),(56,768,56,2,1,38917,9979521<<<96),(704,36,704,2,1,21001,18554258719785<<<24),(768,32,768,1,0,0,157<<<60),(832,5,832,2,1,8198,17867737140),(1408,34,1408,2,1,20743,0x213000000000834000),(1792,36,1792,2,1,21001,5394478923837<<<25),(2240,3,2240,2,1,4107,4362510),(2688,34,2688,2,1,20743,0x10e000000000429000),(3072,2,3072,1,0,0,643072),(3136,3,3136,2,1,4107,643342)]
def wts:=wSpecs.map vp
theorem wRows:wSpecs.all (vc 12 neigh goodB 0)=true:=by decide +kernel
def poss (c m:Nat):=z0r 12 edges wts 0 0 0 c m
def orbsCap:List Nat:=[31,47,63,88,98,122,216,330]
def orbsM1:List Nat:=[63,216]
def mapCap:List (Nat×Nat×Nat):=[(31,0,31),(47,0,47),(55,4,47),(59,2,31),(61,1,31),(62,3,31),(63,0,63),(88,0,88),(98,0,98),(122,0,122),(133,2,98),(152,2,88),(157,2,122),(200,8,88),(208,11,88),(216,0,216),(330,0,330),(396,3,330),(594,5,330),(657,6,330),(1128,1,330),(1161,2,330),(1288,8,98),(1480,8,122),(1984,11,31),(2160,4,330),(2196,7,330),(2576,11,98),(2768,11,122),(3008,9,31),(3520,12,31),(3776,8,31),(3904,8,47),(3968,10,47),(4032,8,63)]
def mapM1:List (Nat×Nat×Nat):=[(63,0,63),(216,0,216),(4032,8,63)]
def survCap:=mapCap.map Prod.fst
def survM1:=mapM1.map Prod.fst
theorem mapCapOk:mapCap.all (fun t=>(List.finRange 12).all (fun i=>t.1.testBit i.val==t.2.2.testBit ((permLists.getD t.2.1 (permLists.getD 0 ([],[]))).1.getD i.val 0)))=true:=by decide +kernel
theorem survCapCov:survCap.all (fun m=>mapCap.any (fun t=>t.1==m&&orbsCap.contains t.2.2))=true:=by decide +kernel
theorem mapM1Ok:mapM1.all (fun t=>(List.finRange 12).all (fun i=>t.1.testBit i.val==t.2.2.testBit ((permLists.getD t.2.1 (permLists.getD 0 ([],[]))).1.getD i.val 0)))=true:=by decide +kernel
theorem survM1Cov:survM1.all (fun m=>mapM1.any (fun t=>t.1==m&&orbsM1.contains t.2.2))=true:=by decide +kernel
def survTest (m:Nat):=!(poss 9 m)||survCap.contains m
theorem sc0:∀ j:Fin 2048,survTest (0+j.val)=true:=by decide +kernel
theorem sc1:∀ j:Fin 2048,survTest (2048+j.val)=true:=by decide +kernel
theorem allSurv (m:Fin 4096):survTest m.val=true:=by
  let j:Fin 2048:=⟨m.val%2048,Nat.mod_lt _ (by decide)⟩
  by_cases q0:m.val/2048=0
  · have e:m.val=0+j.val:=by dsimp [j];omega
    rw [e];exact sc0 j
  by_cases q1:m.val/2048=1
  · have e:m.val=2048+j.val:=by dsimp [j];omega
    rw [e];exact sc1 j
  omega
theorem m1List:survCap.all (fun m=>!(poss 8 m)||survM1.contains m)=true:=by decide +kernel
theorem m2List:survCap.all (fun m=>!(poss 7 m))=true:=by decide +kernel
theorem poss_of {D:Dag} (h:z0 12 D) (hc:z3 12 (z4 neigh) D) (c m:Nat) (enc:(mask m:Finset (Fin 12))=z1 12 D) (lim:zu 12 D≤c):poss c m=true:=by
  obtain ⟨b,hb⟩:=zz gr h.1 hc (fun _ _=>rfl);have hbase:=z0g h.1 b hb
  exact z05 (cover h hc) edgesOk (by decide) (by decide) (by simp [mask]) (by simp [mask]) (by omega) (fun r hr sub=>by rw [wts,List.mem_map] at hr;obtain ⟨s,hs,rfl⟩:=hr;exact v3 gr h hc (fun _ _=>rfl) (fun h=>absurd rfl h) s (List.all_eq_true.mp wRows _ hs) sub) enc lim
theorem noTwo_0 {D:Dag} (h:z0 12 D) (hc:z3 12 (z4 neigh) D) (tight:zu 12 D≤(z6 12 D).card) (hv:(0:Fin 12)∈z1 12 D):False:=by
  have w2:=x5 gr h hc (fun _ _=>rfl) tight;obtain ⟨P,hp⟩:=xx (m:=16) gr h hc adjE
  let ae:=z5g gr h hc hp hv;let ps:=z5f gr h hc hp hv;let cp:=couple hp w2;let ex:=yg gr h hc hp w2
  have c0:=ae false 0 1 (by decide)
  have c1:=ae false 0 2 (by decide)
  have c2:=ps false 0 11 (by decide)
  have c3:=ps false 0 14 (by decide)
  have c4:=cp false 3 4 5 (by decide)
  have c5:=cp false 6 7 8 (by decide)
  have c6:=cp false 13 14 15 (by decide)
  have c7:=cp true 1 11 14 (by decide)
  have c8:=cp true 7 9 15 (by decide)
  have c9:=cp true 4 8 12 (by decide)
  have c10:=ex false 4 5 12 2 7 (by decide)
  have c11:=ex false 7 8 9 4 6 (by decide)
  have c12:=ex false 7 8 9 12 6 (by decide)
  have c13:=ex false 14 15 11 7 7 (by decide)
  have c14:=ex false 14 15 11 9 7 (by decide)
  have c15:=ex true 1 14 2 13 4 (by decide)
  have c16:=ex true 1 14 2 15 4 (by decide)
  have c17:=ex true 7 15 6 13 3 (by decide)
  have c18:=ex true 7 15 8 13 3 (by decide)
  have c19:=ex true 4 8 3 6 4 (by decide)
  have c20:=ex true 4 8 5 6 4 (by decide)
  have c21:=ex true 2 5 1 3 3 (by decide)
  clear h hc hp w2 tight hv ae ps cp ex;grind (splits:=0) only
theorem noTwo_3 {D:Dag} (h:z0 12 D) (hc:z3 12 (z4 neigh) D) (tight:zu 12 D≤(z6 12 D).card) (hv:(3:Fin 12)∈z1 12 D):False:=by
  have w2:=x5 gr h hc (fun _ _=>rfl) tight;obtain ⟨P,hp⟩:=xx (m:=16) gr h hc adjE
  let ae:=z5g gr h hc hp hv;let ps:=z5f gr h hc hp hv;let cp:=couple hp w2;let ex:=yg gr h hc hp w2
  have c0:=ae false 9 10 (by decide)
  have c1:=ps false 9 7 (by decide)
  have c2:=ps false 9 15 (by decide)
  have c3:=cp false 6 7 8 (by decide)
  have c4:=cp false 13 14 15 (by decide)
  have c5:=cp true 1 11 14 (by decide)
  have c6:=cp true 7 9 15 (by decide)
  have c7:=cp true 4 8 12 (by decide)
  have c8:=cp true 2 5 10 (by decide)
  have c9:=ex false 1 2 11 10 6 (by decide)
  have c10:=ex false 4 5 12 2 7 (by decide)
  have c11:=ex false 4 5 12 10 7 (by decide)
  have c12:=ex false 7 8 15 4 6 (by decide)
  have c13:=ex false 7 8 15 12 6 (by decide)
  have c14:=ex false 14 15 1 7 7 (by decide)
  have c15:=ex false 14 15 11 7 7 (by decide)
  have c16:=ex true 1 14 2 13 4 (by decide)
  have c17:=ex true 7 9 6 10 5 (by decide)
  have c18:=ex true 7 9 8 10 5 (by decide)
  have c19:=ex true 9 15 10 13 2 (by decide)
  have c20:=ex true 9 15 10 14 2 (by decide)
  have c21:=ex true 4 8 5 6 4 (by decide)
  clear h hc hp w2 tight hv ae ps cp ex;grind (splits:=0) only
theorem side_63 {D:Dag} (h:z0 12 D) (hc:z3 12 (z4 neigh) D) (z:qd 12 D≤1) (eq:(mask 63:Finset (Fin 12))=z1 12 D):9≤zu 12 D:=yc gr h hc (fun _ _=>rfl) deg3 girth6 z (mask 4032) (mask 63) 9 (0:Fin 12) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) eq
def privList:List z0v:=[(31,3328,0,19,19,3328,[0,0,0,0,0,0,0,0,3168,0,2436,1480]),(47,2816,0,41,41,2816,[0,0,0,0,0,0,0,0,2768,2436,0,834]),(63,3840,0,63,63,0,[0,0,0,0,0,0,0,0,0,0,0,0])]
theorem privsOk:privList.all (vr 12 neigh 4095 0 10)=true:=by decide +kernel
theorem pv {D:Dag} (h:z0 12 D) (hc:z3 12 (z4 neigh) D) (z:qd 12 D=0) (I idx:Nat) (hidx:idx<privList.length) (hI:(privList[idx]'hidx).1=I) (eq:(mask I:Finset (Fin 12))=z1 12 D):10≤zu 12 D:=wh (w0:=0) (goodMask:=4095) (target:=10) gr h hc (fun _ _=>rfl) (fun _ _=>rfl) girth6 (fun h=>absurd rfl h) z (privList[idx]'hidx) (hI.symm ▸ eq) (List.all_eq_true.mp privsOk _ (List.getElem_mem hidx))
theorem cd0 {D:Dag} (h:z0 12 D) (hc:z3 12 (z4 neigh) D) (z:qd 12 D=0) (bp:zu 12 D=9) (I k:Nat) (eq:(mask I:Finset (Fin 12))=z1 12 D) (vars:List Nat) (steps:List xe) (hcard:(mask I:Finset (Fin 12)).card+9=12+k) (hAll:vars.all (fun v=>decide (v<12))=true∧steps.all (yh 12 neigh 4095 I 0 vars)=true∧yk (if 0==0 then 2^k else 2^(k-1)) 0 vars (fun _=>0) steps=true):False:=xc (k:=k) (w0:=0) (goodMask:=4095) (I:=I) (drop:=0) (bpVal:=9) gr h hc (fun _ _=>rfl) (fun _ _=>rfl) bp eq hcard (fun h=>absurd rfl h) (fun P hP i hi hg _=>wy gr h hc z (mask P) hP i ((fun _ _=>rfl) i hg) (eq ▸ hi)) vars steps hAll
def sa0:Array (List Nat):=zj yy [0x1448444848808485408548c408484c48008080848404084844444440450,0x1494485445409414544140814541448104410540c480c48094884488488850,0x8727012111c9c072700212115c454444570115c4146808a80680a424094090,0x501120110405c08848b2712c9c0b2792a122a9e0a8646844aa781a190a102a9e02850,0x2592a0564a80592a080758101d60007582018a0406280018a1484488449017511121111405c4410,0x8851214486021407521944655198866019668249425482448248426a4d0,0x9051414906141810503d44f523d48e513954e623980e5125409522550,0x1a506545952654986061458604d453524d55260494926045451524550,0x1274611104468d01f517d49f527945e557981e506d49a516955a626990,0x7a5188479d03]
def st0:Array (List Nat):=zj (fun x=>6+9*(x&&&63)) [0x4e1a082a1a1206110d08831082150707830883838183c34106410a8302c184418120c1a0e0816081c1010141018201050,0x3227044c27044b2404472404432204411c043f042a3a1e063b1c0437042a34190631045c08b01150228050,0x351a02331a023218823018822f96cb2186cbc1070b41170b4103cb41048b01158b01154a24f0c725408785008a450087650090,0x43208242208240a0823f1e823e1e823b9d4e61890ec11e0ec106cec1078e81170e81058e41158e411bcd2630ce06e08d86e090,0x26a50249a451e18912411e524106d24107920107120117520103d2010591c10491c115d1c1225067b0d1888091488081288090,0x284844a0c2a262006110309834fa753619c13c11b53c11a938119d3811913411853412652e950c729808789608a696087696086494090,0x559c4caa0240aab3599540461484aa09523d1985074289950129c4a1f0a0685538942e140d0aa70f85c1c141480a6084ea6094a1d098401c289d48128d168508020551a2cfa10040aa3429f50010144ca2090,0x1258012fd7ab90d76045f06bb012f035d801701adc15aacd5a1a3560b40d5e8a5a06095a0487582c8357a11641a056411fd58b00d5e7c5606ab389ad4048150,0x6dbc136c30dc0c3ad86e06db05358309b59b01b45a6d50c8ad0099ecd638625653383648819c186d9c107d94cc0d9218660617633283648298c1b058ac30d0,0x6afe09f2fb7e86497c04f5045ef47b062d7a3c8376bbde21915d813a4115ba1d418a5d0e60dc2e37286497004df6eb5c36d881bc188db0de0d0,0x1015746038cada101c4e2b170c8b120a230f85870d1f4403868da1c1c34610a0e120c1e0aff0c73060a063682063d8041031dc102818c1fc18cdfd000d0,0x1eeda910723713e8391b91f81b2e19200e42d28a07216a458373b223c1c7da4ee0e3ed47806f35d47038eb11f41c7584fc0db2ba8d071b6238838db09c81ac605180d0,0x8682cf64851186841404283a08283a28060f054e1407061453838e42244e6a7070505539cc2892101ca70a1cc341718be930786eb86490392bba281c95e1160d0,0x4804906e089065088a0c4ddad40c200c1e001401fc10404e129420932c08af082c04c22c15e1051ab050828cfa82115e26582d046482ca050,0xde05f40aec17d309741ae9f4df0dbed80972bb087]
def sr0_0:List Nat:=zg w7 [0xa04291404e0828a410214964522d4924581248b23896a4912c09205a9240b024954522a6924545244a9a489514902a69205452472290e4711c492238124472380e24901c092229484538884a91105522229c042548082a90a20d0646a3250092885422a00251028092a29553a91d4864a42212111005484224212089001484024202081000484201100083f,0x8911288912881121e0340a434a44348868944694846908d1280d2900d2219a7904d3c4269f340c10257928308549e40a4f10527a903148162024f12059090bc8085e2042f2106054b8149c042e5928c4b4a5289684a50ad294a15a12940b4a5281684a500ea6201d502013aa8401755080ea80009d54000baa80623100ac4a20018944031204056250802c4a10018942031200056250002c4a00018948094905149204292404e2828a7f,0x15e74c5e7d01e7d2493a6293e8093e91611316134061348a0898a09a0209a15a34e4d1a60d1e8fc09f8bd0a93d2a8bd2a83d26e0d409a8d45a9085a90b51a83521035206a2cc0998b1010312083124e049c528141290812923024628424484824848908c85090450948109041091f023e2740a474a447488e8944e9484e9140e9480e91302262443f,0x2bd298bd3a03d3a49884c588d0188d06]
theorem sic0_0:ze (n:=12) (m:=16) neigh edges goodB false true 0 1 216 mBook sa0 (zr 9 st0) 0 sr0_0=true:=by decide +kernel
def srs0_0:List Nat:=zg (fun x=>9+8*(1+(x&&&511))) [0x2cacef60242fed036467ada764dfe6e6a3f683397937e704c4a5033016cff35c7c9bf38256a09e0007b0159ca485f06dfc7c9cdc8f16fed4e0986588423a32fefa52c602d6dace4dfe6e6b877e704c482012482b171a0c140b93b524077d7c02017e022e382c1797192fb696ab8d8eeeef6e2d83dc1717db55d686c7774c4c371641858b864b25eb662dcdebeda363a39b8ac0f99adb8bb8adbb9bcc29695ac9889d1d0cf971110c00a4cd6dbdd5ce15e4b4ae8e867cb88886083e9286c356bf6694697abb5f329de85852982147454db1983005a09fcc1501a732a4149415eb25953207e4a2831399510989725240c828086767ec2eae8e6f3a8c1a4c60d4140433cd3727162039f1eb0808f8ed8d8975080d81dde1d90c179c190c028785888284070b05ccc90e05668cd500a0e042012200953502c2956041e55245423512017cb4f04aab6278f8f122a118d35b3b3646564a983d4151b069ad9d994b208887255418965413860339373a354a48c6c76a0426a5a72534221a19b4820dcdb11a1193b14e80e74d4709a98966c06393669683a022215a72393928164]
theorem sro0_0:zo (zr 9 st0) 8 195 srs0_0=true:=by decide +kernel
theorem scf0:zf (zr 9 st0) 231 146 (digits 8 26 0x8e8cbfbd94b280b3b4e19eb69d937f9b9ae6e5e4df9c13120804) 0=true:=by decide +kernel
def sa1:Array (List Nat):=zj yy [0x1c6c449b790b1026ddc2c4ac2c09008901050501040088000804040400050,0x2c405040484045007100b001400120010401c8b47014112d1d41040b47226de46c50,0x4212080808102020008082018204060800182095471551d4506c1041547b201420122012401d0,0x40980260096c0250026c0d00c943b8150ee0143b82486e0521b80486e090848b1411421210,0x161405d49650598565b59916605940352094425b098c]
def st1:Array (List Nat):=zj (fun x=>6+8*(x&&&63)) [0xa8a022624088c74643152208807021e1c08686021618084c502110e083410b042418205040c101050,0x1313824a480904e4bc3464009110024240081d0023e3808f0e023a3808dce02342e08c8b82302e08b4a49430f2c090,0x9d7825d5b590c1d7023d5a08c16025755530d115824356081d5823c5408ed502375408c9482315209453d2430f50090,0x1cc1716f6d0c55c02216e0879b821b6c0859b026b69670c55a821f68085d98265615f0c3d902626009358024a5e090,0xf5fa0837d02820cde08281347a0ccde9f837d007a0de51cfdd0185794735740615e4fcd4d9d05127809dd14f5c8185774533720615dcf4ccd9c8510760825d827508120d0,0x25e1a50395064e3e2430f92098e323838b0c8e0cae423834b888c0e2c2a2038706160dec38146840d15fa1037d04840c1e102813e820d0,0x1dce027753380dd1e43c38c2d658e11d1e5fa044817974358415f9d1e604e057e7479817a15e5d1fa05005938b09f4109050574c038d80960dfe2a583917c960d0,0x15048dc47837705dd5827740085]
def sr1_0:List Nat:=zg w7 [0x28766250ed02a49da85473b5029276a051ced490d98921b40a4e36a049c6d484218908440a1708a1416114085c22810584501006202010202402800280500c0620118144013028806040808c0a10098142030200046050004c0a550a4aa1c5554482b689400a485824904049204092400e285824504048a04091400e085824104048204092d0a45a1c4b044816a8926ca44d9c499b4892f690266d204bda42c8831400200064001000003f,0x1b585322c29c1614c161d1782d025a2b15a5415a4015a4b05a5405a41c0286c82910829408291051d8852208528085210a3b00a4400a5000a44360f20b0788583ec0184280f2040788203d0018800b0b07420364]
theorem sic1_0:ze (n:=12) (m:=16) neigh edges goodB false true 0 1 330 mBook sa1 (zr 8 st1) 0 sr1_0=true:=by decide +kernel
def srs1_0:List Nat:=zg (fun x=>9+7*(1+(x&&&511))) [0x16f86b910d5c36e6f5b8c780c12f86bb14e80a9922a444c91de3c37bf860b3b1386f529df9303a34d114453668cbf540987b8b957e8c0aa53aa4a5cb3f8a073ed10b03d62eecc5af0e6bf719a0217ab31098e1ebecb4c0cafdbcb7ab1106509b575143b9f4698e09a946400aa51ab3f4182f240e60a9d279e5cc8e07a1324c8a670d99aa08b55c284ba04a53a5020202a81899686992a4548b1ad4e660837e741e5d71d564960152]
theorem sro1_0:zo (zr 8 st1) 7 99 srs1_0=true:=by decide +kernel
theorem scf1:zf (zr 8 st1) 117 109 (digits 7 8 0x8d0030785d3964) 0=true:=by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem no_dag:¬∃ D:Dag,z0 12 D∧D.length≤20∧z3 12 (z4 neigh) D:=by
  rintro ⟨D,h,hlen,hc⟩
  have hsur:=xo h;have hsp:=x6 12 D;obtain ⟨m,enc⟩:=repr 12 (z1 12 D)
  have hok:poss 9 m.val=true:=poss_of h hc 9 m.val enc (by omega)
  have hmem:m.val∈survCap:=by have:=allSurv m;simpa [survTest,hok] using this
  have hge:8≤zu 12 D:=by by_contra hlt;have hp:=poss_of h hc 7 m.val enc (by omega);have:=List.all_eq_true.mp m2List _ hmem;simp [hp] at this
  by_cases hbpm1:zu 12 D=8
  · have hp1:=poss_of h hc 8 m.val enc hbpm1.le
    have hm1:=List.all_eq_true.mp m1List _ hmem;simp only [hp1,Bool.not_true,Bool.false_or,List.contains_iff_mem] at hm1
    obtain ⟨⟨mv,ai,rep⟩,htm,htb⟩:=List.any_eq_true.mp (List.all_eq_true.mp survM1Cov _ hm1)
    simp only [Bool.and_eq_true,beq_iff_eq,List.contains_iff_mem] at htb;rcases htb with ⟨hmveq,hrep⟩
    have hmv:(mask mv:Finset (Fin 12)).image (permOf ai)=mask rep:=zp _ _ _ (fun i=>by rw [permVal ai i];exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp mapM1Ok _ htm) i (List.mem_finRange i)))
    obtain ⟨h1,h2,_,h4,h5,h6⟩:=qu h hc (permOf ai) (autoOf ai)
    have eq':(mask rep:Finset (Fin 12))=z1 12 (z7 (permOf ai) D):=by rw [h6,←enc,←hmveq,hmv]
    simp only [orbsM1,List.mem_cons,List.not_mem_nil,or_false] at hrep
    rcases hrep with rfl|rfl
    · have:=side_63 h1 h2 (by omega) eq';omega
    · have el:=zm 12 (z7 (permOf ai) D);have c:(mask 216:Finset (Fin 12)).card=4:=by decide +kernel
      rw [←eq'] at el;exact noTwo_3 h1 h2 (by omega) (eq' ▸ (by decide:(3:Fin 12)∈mask 216))
  have hbp:zu 12 D=9:=by omega
  have hbz0:qd 12 D=0:=by omega
  obtain ⟨⟨mv,ai,rep⟩,htm,htb⟩:=List.any_eq_true.mp (List.all_eq_true.mp survCapCov _ hmem)
  simp only [Bool.and_eq_true,beq_iff_eq,List.contains_iff_mem] at htb;rcases htb with ⟨hmveq,hrep⟩
  have hmv:(mask mv:Finset (Fin 12)).image (permOf ai)=mask rep:=zp _ _ _ (fun i=>by rw [permVal ai i];exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp mapCapOk _ htm) i (List.mem_finRange i)))
  obtain ⟨h1,h2,_,h4,h5,h6⟩:=qu h hc (permOf ai) (autoOf ai)
  have eq':(mask rep:Finset (Fin 12))=z1 12 (z7 (permOf ai) D):=by rw [h6,←enc,←hmveq,hmv]
  simp only [orbsCap,List.mem_cons,List.not_mem_nil,or_false] at hrep
  rcases hrep with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · have:=pv h1 h2 (by omega) 31 0 (by decide) rfl eq';omega
  · have:=pv h1 h2 (by omega) 47 1 (by decide) rfl eq';omega
  · have:=pv h1 h2 (by omega) 63 2 (by decide) rfl eq';omega
  · have el:=zm 12 (z7 (permOf ai) D);have c:(mask 88:Finset (Fin 12)).card=3:=by decide +kernel
    rw [←eq'] at el;exact noTwo_3 h1 h2 (by omega) (eq' ▸ (by decide:(3:Fin 12)∈mask 88))
  · obtain ⟨j1,j2,_,j4,_,j6⟩:=qu h1 h2 (permOf 2) (autoOf 2)
    have el:=zm 12 (z7 (permOf 2) (z7 (permOf ai) D))
    have hci:(z1 12 (z7 (permOf 2) (z7 (permOf ai) D))).card=3:=by rw [j6,Finset.card_image_of_injective _ (permOf 2).injective,←eq'];decide +kernel
    exact noTwo_0 j1 j2 (by omega) (by rw [j6,←eq'];exact Finset.mem_image.mpr ⟨(1:Fin 12),by decide,Fin.ext (by rw [permVal 2];decide)⟩)
  · exact cd0 h1 h2 (by omega) (by omega) 122 2 eq' [8,9,10] [(0,1480,1161,5,0,8,10,0,4),(0,4032,2436,3,0,9,8,0,5),(0,1480,396,1,0,10,8,0,4),(3,1665,0,1,4,10,9,7,0)] (by decide +kernel) (by decide +kernel)
  · exact xj 9 gr h1 h2 adjE (fun _ _=>rfl) (by omega) (fun _=>by omega) (by omega) eq' (by decide +kernel) (fun h=>absurd rfl h) (fun h=>by cases h) (by decide) (by decide) sic0_0 sro0_0 scf0
  · exact xj 9 gr h1 h2 adjE (fun _ _=>rfl) (by omega) (fun _=>by omega) (by omega) eq' (by decide +kernel) (fun h=>absurd rfl h) (fun h=>by cases h) (by decide) (by decide) sic1_0 sro1_0 scf1
end G_Gpp
namespace G_C1
open DagTools Resolution Compact GraphTools Reduction
def neigh:List Nat:=[4416,6272,3136,5632,2816,1408,5,34,49,24,44,22,11]
def edges:List (Nat×Nat):=[(0,6),(0,8),(0,12),(1,7),(1,11),(1,12),(2,6),(2,10),(2,11),(3,9),(3,10),(3,12),(4,8),(4,9),(4,11),(5,7),(5,8),(5,10)]
def goodB:Fin 13→Bool:=(fun _:Fin 13=>true)
def mBook:List Nat:=[63,122,157,216,270,330,396,551,610,645,774,1043,1106,1169,1539,1858,2089,2152,2185,2504,2593,3713,4148,4208,4244,4644,4996,5328,6752,8128]
theorem gr:zc (z4 neigh) (fun v=>goodB v=true):=by unfold zc;decide +kernel
theorem edgesOk:∀ q∈edges,∃ hu:q.1<13,∃ hv:q.2<13,z4 neigh ⟨q.1,hu⟩ ⟨q.2,hv⟩:=by decide +kernel
theorem adjE:∀ e:Fin 18,z4 neigh (zh 13 edges false e.val) (zh 13 edges true e.val):=by decide +kernel
theorem deg3:∀ j:Fin 13,(z9 neigh Finset.univ j).card≤3:=by decide +kernel
theorem girth6:∀ i j:Fin 13,i≠j→(z9 neigh Finset.univ i∩z9 neigh Finset.univ j).card≤1:=by decide +kernel
theorem hdeg2:∀ u v:Fin 13,z4 neigh u v→∃ a,z4 neigh u a∧a≠v:=by decide +kernel
theorem cover {D:Dag} (h:z0 13 D) (hc:z3 13 (z4 neigh) D):∀ u v:Fin 13,z4 neigh u v→u∈z6 13 D∨v∈z6 13 D:=fun u v huv=>wu gr h hc rfl rfl huv (hdeg2 u v huv)
def permLists:List (List Nat×List Nat):=[([0,1,2,3,4,5,6,7,8,9,10,11,12],[0,1,2,3,4,5,6,7,8,9,10,11,12]),([2,1,0,4,3,5,6,7,10,9,8,12,11],[2,1,0,4,3,5,6,7,10,9,8,12,11]),([2,5,0,3,4,1,6,7,11,9,12,8,10],[2,5,0,3,4,1,6,7,11,9,12,8,10]),([0,5,2,4,3,1,6,7,12,9,11,10,8],[0,5,2,4,3,1,6,7,12,9,11,10,8]),([5,2,1,3,4,0,7,6,8,9,12,11,10],[5,2,1,3,4,0,7,6,8,9,12,11,10]),([5,0,1,4,3,2,7,6,10,9,11,12,8],[1,2,5,4,3,0,7,6,12,9,8,10,11]),([1,0,5,3,4,2,7,6,11,9,10,8,12],[1,0,5,3,4,2,7,6,11,9,10,8,12]),([1,2,5,4,3,0,7,6,12,9,8,10,11],[5,0,1,4,3,2,7,6,10,9,11,12,8])]
theorem autsOk:permLists.all (wd 13 neigh)=true:=by decide +kernel
def permOf (k:Nat):Equiv.Perm (Fin 13):=va (neigh:=neigh) permLists autsOk (by decide) k
theorem autoOf (k:Nat):auto neigh (permOf k):=z1b (neigh:=neigh) permLists autsOk (by decide) k
theorem permVal (k:Nat) (i:Fin 13):(permOf k i).val=(permLists.getD k (permLists.getD 0 ([],[]))).1.getD i.val 0:=z06 (neigh:=neigh) permLists autsOk (by decide) k i
theorem aut24Ok:permLists.all (fun fg=>(List.range 13).all fun i=>(24:Nat).testBit i==(24:Nat).testBit (fg.1.getD i 0))=true:=by decide +kernel
theorem perm24 (k:Nat):(mask 24:Finset (Fin 13)).image (permOf k)=mask 24:=zp _ _ _ (fun i=>by rw [permVal k i];exact beq_iff_eq.mp (List.all_eq_true.mp (wk aut24Ok (by decide) k) i.val (List.mem_range.mpr i.isLt)))
def wSpecs:List wn:=[(1344,5,1344,3,1,8198,140190421044),(3200,6,3200,3,1,8459,8221261824),(4480,3,4480,3,1,4108,17113210),(6208,3,6208,3,1,4108,1286414),(320,1,320,2,0,0,4148),(384,32,384,2,0,0,1043<<<65),(1088,4,1088,2,0,0,2089<<<26),(2176,2,2176,2,0,0,33980416),(3,4096,3,2,0,0,27<<<159),(6,2048,6,2,0,0,27<<<146),(7,6144,7,3,1,51969,1102087<<<147),(33,256,33,2,0,0,27<<<107),(36,1024,36,2,0,0,27<<<133),(448,33,448,3,1,20488,0x8260000000000001034),(1152,32,1152,2,0,0,135<<<66),(1216,36,1216,3,1,21002,0x870000000829<<<26),(1792,24,1792,2,1,17161,4279309<<<41),(2112,4,2112,2,0,0,1043<<<26),(3072,4,3072,2,0,0,61<<<27),(3328,36,3328,3,1,21002,43155831390269<<<27),(4160,1,4160,2,0,0,270),(4224,2,4224,2,0,0,17113088),(4352,1,4352,2,0,0,122),(6144,2,6144,2,0,0,1286144),(35,4352,35,3,1,51200,0x630000000000425<<<106),(37,1280,37,3,1,43013,11072963113<<<105),(38,3072,38,3,1,47618,9578633<<<130),(2240,6,2240,3,1,8459,70028525568),(2368,5,2368,3,1,8198,69994549300),(2432,34,2432,3,1,20743,0x8260000000002068000),(4288,3,4288,3,1,4108,17113358),(5184,5,5184,3,1,8198,140190417166),(5248,34,5248,3,1,20743,0x21c0000000001052000),(5376,33,5376,3,1,20488,0x13a000000000000007a),(6400,3,6400,3,1,4108,1286266),(7168,6,7168,3,1,8459,8188567552)]
def wts:=wSpecs.map vp
theorem wRows:wSpecs.all (vc 13 neigh goodB 24)=true:=by decide +kernel
def poss (c m:Nat):=z0r 13 edges wts 512 0 1 c m
def orbsCap:List Nat:=[517,551,578,610,704,770,774,834,1794,1858,1920,1984,2816,3008,3904,4032,7936,8000,8128]
def orbsM1:List Nat:=[610,4032,8000,8128]
def mapCap:List (Nat×Nat×Nat):=[(517,0,517),(546,4,517),(551,0,551),(578,0,578),(608,2,578),(610,0,610),(641,6,578),(644,4,578),(645,4,610),(704,0,704),(770,0,770),(772,4,770),(774,0,774),(834,0,834),(900,4,834),(1537,7,770),(1538,1,770),(1539,1,774),(1602,1,834),(1665,7,834),(1794,0,1794),(1858,0,1858),(1920,0,1920),(1984,0,1984),(2561,6,770),(2592,2,770),(2593,2,774),(2656,2,834),(2689,6,834),(2816,0,2816),(3008,0,3008),(3585,6,1794),(3648,6,1920),(3713,6,1858),(3776,6,1984),(3904,0,3904),(3968,6,3904),(4032,0,4032),(4612,5,770),(4640,3,770),(4644,3,774),(4704,3,834),(4740,5,834),(4868,4,1794),(4928,4,1920),(4996,4,1858),(5056,4,1984),(5632,1,2816),(5824,1,3008),(5952,1,3904),(6016,5,3904),(6080,1,4032),(6688,2,1794),(6752,2,1858),(6784,2,1920),(6848,2,1984),(6976,2,3904),(7040,4,3904),(7104,2,4032),(7744,3,3904),(7808,7,3904),(7872,3,4032),(7936,0,7936),(8000,0,8000),(8064,4,8000),(8128,0,8128)]
def mapM1:List (Nat×Nat×Nat):=[(610,0,610),(645,4,610),(4032,0,4032),(6080,1,4032),(7104,2,4032),(7872,3,4032),(8000,0,8000),(8064,4,8000),(8128,0,8128)]
def survCap:=mapCap.map Prod.fst
def survM1:=mapM1.map Prod.fst
theorem mapCapOk:mapCap.all (fun t=>(List.finRange 13).all (fun i=>t.1.testBit i.val==t.2.2.testBit ((permLists.getD t.2.1 (permLists.getD 0 ([],[]))).1.getD i.val 0)))=true:=by decide +kernel
theorem survCapCov:survCap.all (fun m=>mapCap.any (fun t=>t.1==m&&orbsCap.contains t.2.2))=true:=by decide +kernel
theorem mapM1Ok:mapM1.all (fun t=>(List.finRange 13).all (fun i=>t.1.testBit i.val==t.2.2.testBit ((permLists.getD t.2.1 (permLists.getD 0 ([],[]))).1.getD i.val 0)))=true:=by decide +kernel
theorem survM1Cov:survM1.all (fun m=>mapM1.any (fun t=>t.1==m&&orbsM1.contains t.2.2))=true:=by decide +kernel
def survTest (m:Nat):=!(poss 11 m)||survCap.contains m
theorem sc0:∀ j:Fin 2048,survTest (0+j.val)=true:=by decide +kernel
theorem sc1:∀ j:Fin 2048,survTest (2048+j.val)=true:=by decide +kernel
theorem sc2:∀ j:Fin 2048,survTest (4096+j.val)=true:=by decide +kernel
theorem sc3:∀ j:Fin 2048,survTest (6144+j.val)=true:=by decide +kernel
theorem allSurv (m:Fin 8192):survTest m.val=true:=by
  let j:Fin 2048:=⟨m.val%2048,Nat.mod_lt _ (by decide)⟩
  by_cases q0:m.val/2048=0
  · have e:m.val=0+j.val:=by dsimp [j];omega
    rw [e];exact sc0 j
  by_cases q1:m.val/2048=1
  · have e:m.val=2048+j.val:=by dsimp [j];omega
    rw [e];exact sc1 j
  by_cases q2:m.val/2048=2
  · have e:m.val=4096+j.val:=by dsimp [j];omega
    rw [e];exact sc2 j
  by_cases q3:m.val/2048=3
  · have e:m.val=6144+j.val:=by dsimp [j];omega
    rw [e];exact sc3 j
  omega
theorem m1List:survCap.all (fun m=>!(poss 10 m)||survM1.contains m)=true:=by decide +kernel
theorem m2List:survCap.all (fun m=>!(poss 9 m)||m==8128)=true:=by decide +kernel
theorem m3List:survCap.all (fun m=>!(poss 8 m))=true:=by decide +kernel
theorem poss_of {D:Dag} (h:z0 13 D) (hc:z3 13 (z4 neigh) D) (h9:(9:Fin 13)∈z1 13 D) (hw0:∃ w,2≤zd D w∧supp 13 D w=(mask 24:Finset (Fin 13))∧2≤(supp 13 D w).card) (c m:Nat) (enc:(mask m:Finset (Fin 13))=z1 13 D) (lim:zu 13 D≤c):poss c m=true:=by
  obtain ⟨b,hb⟩:=zz gr h.1 hc (fun _ _=>rfl);obtain ⟨w,hfw,hsw,hcw⟩:=hw0
  have hres_pos:0<(z5 13 D b).card:=Finset.card_pos.mpr ⟨⟨w,0⟩,y6 h.1 b hb hfw hcw⟩
  have hcr:=card_residual h.1 b hb
  exact z05 (cover h hc) edgesOk (by decide) (by decide) (fun x hx=>by have hx9:x=9:=(by revert x hx;decide +kernel);exact hx9 ▸ h9) (by simp [mask]) (by omega) (fun r hr sub=>by rw [wts,List.mem_map] at hr;obtain ⟨s,hs,rfl⟩:=hr;exact v3 gr h hc (fun _ _=>rfl) (fun _=>⟨w,hfw,hsw,hcw⟩) s (List.all_eq_true.mp wRows _ hs) sub) enc lim
theorem side_8000 {D:Dag} (h:z0 13 D) (hc:z3 13 (z4 neigh) D) (z:qd 13 D≤1) (eq:(mask 8000:Finset (Fin 13))=z1 13 D):11≤zu 13 D:=yc gr h hc (fun _ _=>rfl) deg3 girth6 z (mask 63) (mask 8000) 11 (8:Fin 13) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) eq
def privList:List z0v:=[(1794,56,0,1792,1792,56,[0,0,0,4148,2089,157,0,0,0,0,0,0,0]),(1858,37,0,1344,1344,37,[4148,0,2089,0,0,157,0,0,0,0,0,0,0]),(1920,56,0,1792,1792,56,[0,0,0,4148,2089,157,0,0,0,0,0,0,0]),(1984,37,0,1344,1344,37,[4148,0,2089,0,0,157,0,0,0,0,0,0,0]),(3904,37,0,1344,1344,37,[4148,0,2089,0,0,157,0,0,0,0,0,0,0]),(7936,27,4096,2816,6912,11,[122,157,0,1043,0,0,0,0,0,0,0,0,0]),(8000,31,6144,1856,8000,2,[0,157,0,0,0,0,0,0,0,0,0,0,0]),(8128,63,7424,704,8128,0,[0,0,0,0,0,0,0,0,0,0,0,0,0])]
theorem privsOk:privList.all (vr 13 neigh 8191 24 12)=true:=by decide +kernel
theorem pv {D:Dag} (h:z0 13 D) (hc:z3 13 (z4 neigh) D) (z:qd 13 D=0) (hw0:∃ w,2≤zd D w∧supp 13 D w=(mask 24:Finset (Fin 13))∧2≤(supp 13 D w).card) (I idx:Nat) (hidx:idx<privList.length) (hI:(privList[idx]'hidx).1=I) (eq:(mask I:Finset (Fin 13))=z1 13 D):12≤zu 13 D:=wh (w0:=24) (goodMask:=8191) (target:=12) gr h hc (fun _ _=>rfl) (fun _ _=>rfl) girth6 (fun _=>hw0) z (privList[idx]'hidx) (hI.symm ▸ eq) (List.all_eq_true.mp privsOk _ (List.getElem_mem hidx))
theorem cd0 {D:Dag} (h:z0 13 D) (hc:z3 13 (z4 neigh) D) (z:qd 13 D=0) (bp:zu 13 D=11) (hw0:∃ w,2≤zd D w∧supp 13 D w=(mask 24:Finset (Fin 13))∧2≤(supp 13 D w).card) (I k:Nat) (eq:(mask I:Finset (Fin 13))=z1 13 D) (vars:List Nat) (steps:List xe) (hcard:(mask I:Finset (Fin 13)).card+11=13+k) (hAll:vars.all (fun v=>decide (v<13))=true∧steps.all (yh 13 neigh 8191 I 0 vars)=true∧yk (if 24==0 then 2^k else 2^(k-1)) 24 vars (fun _=>0) steps=true):False:=xc (k:=k) (w0:=24) (goodMask:=8191) (I:=I) (drop:=0) (bpVal:=11) gr h hc (fun _ _=>rfl) (fun _ _=>rfl) bp eq hcard (fun _=>hw0) (fun P hP i hi hg _=>wy gr h hc z (mask P) hP i ((fun _ _=>rfl) i hg) (eq ▸ hi)) vars steps hAll
theorem cdD {D:Dag} (h:z0 13 D) (hc:z3 13 (z4 neigh) D) (bpVal I k drop:Nat) (bp:zu 13 D=bpVal) (hw0:∃ w,2≤zd D w∧supp 13 D w=(mask 24:Finset (Fin 13))∧2≤(supp 13 D w).card) (eq:(mask I:Finset (Fin 13))=z1 13 D) (hex:∀ i∈(mask I:Finset (Fin 13))\mask drop,xd neigh D (mask 63) i) (vars:List Nat) (steps:List xe) (hdrop:drop≠0) (hcard:(mask I:Finset (Fin 13)).card+bpVal=13+k) (hAll:vars.all (fun v=>decide (v<13))=true∧steps.all (yh 13 neigh 8191 I drop vars)=true∧yk (if 24==0 then 2^k else 2^(k-1)) 24 vars (fun _=>0) steps=true):False:=xc (k:=k) (w0:=24) (goodMask:=8191) (I:=I) (drop:=drop) (bpVal:=bpVal) gr h hc (fun _ _=>rfl) (fun _ _=>rfl) bp eq hcard (fun _=>hw0) (fun P _ i hi _ hcond=>by simp only [beq_false_of_ne hdrop,Bool.false_or,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at hcond;rcases hcond with ⟨rfl,hnd⟩;exact hex i (Finset.mem_sdiff.mpr ⟨hi,by simp [mask,hnd]⟩)) vars steps hAll
theorem shiftC1 {D:Dag} (h:z0 13 D) (hc:z3 13 (z4 neigh) D) (hw0:∃ w,2≤zd D w∧supp 13 D w=(mask 24:Finset (Fin 13))∧2≤(supp 13 D w).card) (σ:Equiv.Perm (Fin 13)) (ha:auto neigh σ) (h24:(mask 24:Finset (Fin 13)).image σ=mask 24):z0 13 (z7 σ D)∧z3 13 (z4 neigh) (z7 σ D)∧zu 13 (z7 σ D)=zu 13 D∧qd 13 (z7 σ D)=qd 13 D∧z1 13 (z7 σ D)=(z1 13 D).image σ∧(∃ w,2≤zd (z7 σ D) w∧supp 13 (z7 σ D) w=(mask 24:Finset (Fin 13))∧2≤(supp 13 (z7 σ D) w).card):=by
  obtain ⟨h1,h2,_,h4,h5,h6⟩:=qu h hc σ ha;obtain ⟨w,hfw,hsw,hcw⟩:=hw0
  refine ⟨h1,h2,h4,h5,h6,y3 σ w,by rw [xn];exact hfw,by rw [y7 σ h.1 w,hsw,h24],by rw [y7 σ h.1 w,hsw,h24];decide +kernel⟩
def pMapOk (di m1 m2:Nat):Bool:=(List.range 13).all fun i=>m1.testBit i==m2.testBit ((permLists.getD di (permLists.getD 0 ([],[]))).1.getD i 0)
theorem pMapSound (di m1 m2:Nat) (h:pMapOk di m1 m2=true):(mask m1:Finset (Fin 13)).image (permOf di)=mask m2:=zp _ _ _ (fun i=>by rw [permVal di i];exact beq_iff_eq.mp (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)))
def c1Drops:List (Nat×Nat×Nat×Nat×List Nat×List xe):=[(4032,10,64,3,[0,1,2],[(0,63,4148,8,0,0,2,0,6),(3,63,0,7,11,1,0,5,0),(0,63,4148,7,0,1,2,0,11),(0,63,122,10,0,2,1,0,11)]),(4032,10,256,3,[0,1,5],[(0,63,4148,6,0,0,5,0,8),(3,63,0,7,11,1,0,5,0),(0,63,4148,11,0,1,5,0,7),(0,63,270,10,0,5,1,0,7)]),(4032,10,512,3,[0,1,2],[(0,63,4148,8,0,0,2,0,6),(3,63,0,7,11,1,0,5,0),(0,63,4148,7,0,1,2,0,11),(2,63,0,6,10,2,1,0,11)]),(4032,10,1024,3,[0,1,2],[(0,63,4148,8,0,0,2,0,6),(3,63,0,7,11,1,0,5,0),(0,63,4148,7,0,1,2,0,11),(0,63,1043,6,0,2,1,0,11)]),(8128,10,64,4,[0,1,2,5],[(2,63,0,8,12,0,2,4,6),(0,63,122,12,0,0,5,0,8),(2,63,0,7,11,1,0,5,12),(2,63,0,11,12,1,5,2,7),(0,63,122,10,0,2,1,0,11),(0,63,122,11,0,2,5,0,10),(2,63,0,7,10,5,0,1,8),(2,63,0,8,10,5,1,0,7),(2,63,0,7,8,5,2,1,10)]),(8128,10,256,4,[0,1,2,5],[(0,63,270,12,0,0,2,0,6),(2,63,0,6,12,0,5,2,8),(2,63,0,7,11,1,0,5,12),(2,63,0,11,12,1,5,2,7),(2,63,0,6,10,2,1,0,11),(2,63,0,6,11,2,5,0,10),(2,63,0,7,10,5,0,1,8),(0,63,270,10,0,5,1,0,7),(0,63,270,7,0,5,2,0,10)]),(8128,10,512,4,[0,1,2,5],[(2,63,0,8,12,0,2,4,6),(2,63,0,6,12,0,5,2,8),(2,63,0,7,11,1,0,5,12),(2,63,0,11,12,1,5,2,7),(2,63,0,6,10,2,1,0,11),(2,63,0,6,11,2,5,0,10),(2,63,0,7,10,5,0,1,8),(2,63,0,8,10,5,1,0,7),(2,63,0,7,8,5,2,1,10)]),(8128,9,192,3,[0,1,2],[(2,63,0,8,12,0,2,4,6),(0,63,157,11,0,1,0,0,12),(0,63,122,10,0,2,1,0,11)]),(8128,9,320,3,[0,1,2],[(0,63,270,12,0,0,2,0,6),(2,63,0,7,11,1,0,5,12),(0,63,122,10,0,2,1,0,11)]),(8128,9,576,3,[0,1,2],[(2,63,0,8,12,0,2,4,6),(2,63,0,7,11,1,0,5,12),(0,63,122,10,0,2,1,0,11)]),(8128,9,768,3,[0,1,2],[(0,63,270,12,0,0,2,0,6),(2,63,0,7,11,1,0,5,12),(2,63,0,6,10,2,1,0,11)]),(8128,9,1280,3,[0,1,2],[(0,63,270,12,0,0,2,0,6),(2,63,0,7,11,1,0,5,12),(0,63,1043,6,0,2,1,0,11)]),(8128,9,2304,3,[0,1,2],[(0,63,270,12,0,0,2,0,6),(0,63,2089,7,0,1,0,0,12),(2,63,0,6,10,2,1,0,11)])]
theorem c1DropsOk:c1Drops.all (fun t=>let (M,bp,dm,k,vs,st):=t;dm != 0&&decide (z3s 13 M+bp=13+k)&&vs.all (fun v=>decide (v<13))&&st.all (yh 13 neigh 8191 M dm vs)&&yk (2^(k-1)) 24 vs (fun _=>0) st)=true:=by decide +kernel
def c1Map:List (Nat×Nat×Nat×Nat×Nat):=[(4032,10,64,0,0),(4032,10,128,6,0),(4032,10,256,0,1),(4032,10,512,0,2),(4032,10,1024,0,3),(4032,10,2048,6,1),(8128,10,64,0,4),(8128,10,128,4,4),(8128,10,256,0,5),(8128,10,512,0,6),(8128,10,1024,1,5),(8128,10,2048,2,5),(8128,10,4096,3,5),(8128,9,192,0,7),(8128,9,320,0,8),(8128,9,576,0,9),(8128,9,1088,1,8),(8128,9,2112,2,8),(8128,9,4160,3,8),(8128,9,384,4,8),(8128,9,640,4,9),(8128,9,1152,7,8),(8128,9,2176,6,8),(8128,9,4224,5,8),(8128,9,768,0,10),(8128,9,1280,0,11),(8128,9,2304,0,12),(8128,9,4352,4,11),(8128,9,1536,1,10),(8128,9,2560,2,10),(8128,9,4608,3,10),(8128,9,3072,6,11),(8128,9,5120,1,12),(8128,9,6144,2,11)]
theorem c1MapOk:c1Map.all (fun t=>let (M,bp,sm,di,idx):=t;match c1Drops[idx]? with | none=>false | some (M',bp',dm,_,_,_)=>M'==M&&bp'==bp&&pMapOk di 63 63&&pMapOk di M M&&pMapOk di sm dm)=true:=by decide +kernel
theorem c1Cov1:∀ M∈([4032,8128]:List Nat),∀ d:Fin 13,M.testBit d.val=true→c1Map.any (fun t=>t.1==M&&t.2.1==10&&t.2.2.1==(1<<<d.val))=true:=by decide +kernel
theorem c1Cov2:∀ d1 d2:Fin 13,(8128:Nat).testBit d1.val=true→(8128:Nat).testBit d2.val=true→d1.val<d2.val→c1Map.any (fun t=>t.1==8128&&t.2.1==9&&t.2.2.1==((1<<<d1.val)|||(1<<<d2.val)))=true:=by decide +kernel
theorem movC1 {D:Dag} {M bp sm:Nat} (h:z0 13 D) (hc:z3 13 (z4 neigh) D) (hbp:zu 13 D=bp) (hw0:∃ w,2≤zd D w∧supp 13 D w=(mask 24:Finset (Fin 13))∧2≤(supp 13 D w).card) (eq:(mask M:Finset (Fin 13))=z1 13 D) (hhex:∀ i∈(mask M:Finset (Fin 13))\mask sm,xd neigh D (mask 63) i) (hcov:c1Map.any (fun t=>t.1==M&&t.2.1==bp&&t.2.2.1==sm)=true):False:=by
  obtain ⟨⟨M0,bp0,sm0,di,idx⟩,hm,hmt⟩:=List.any_eq_true.mp hcov
  simp only [Bool.and_eq_true,beq_iff_eq] at hmt;rcases hmt with ⟨⟨rfl,rfl⟩,rfl⟩
  have hmo:=List.all_eq_true.mp c1MapOk _ hm
  cases hget:c1Drops[idx]? with
  | none=>simp [hget] at hmo
  | some d=>
    rcases d with ⟨M',bp',dm,k,vs,st⟩;simp only [hget,Bool.and_eq_true,beq_iff_eq] at hmo
    rcases hmo with ⟨⟨⟨⟨rfl,rfl⟩,h63b⟩,hMb⟩,hsmb⟩
    have hdo:=List.all_eq_true.mp c1DropsOk _ (List.mem_of_getElem? hget)
    simp only [Bool.and_eq_true,bne_iff_ne,ne_eq,decide_eq_true_eq] at hdo
    rcases hdo with ⟨⟨⟨⟨hdm,hcard⟩,hvs⟩,hst⟩,hfail⟩
    have h63:=pMapSound di 63 63 h63b;have hM:=pMapSound di M' M' hMb;have hST:=pMapSound di sm0 dm hsmb
    obtain ⟨h1,h2,h4,_,h6,hw0'⟩:=shiftC1 h hc hw0 (permOf di) (autoOf di) (perm24 di)
    refine cdD h1 h2 bp' M' k dm (h4.trans hbp) hw0' (by rw [h6,←eq,hM]) (fun i hi=>z3a h (permOf di) (autoOf di) h63 (hhex ((permOf di)⁻¹ i) ?_)) vs st hdm (by rw [qo];exact hcard) ⟨hvs,hst,hfail⟩
    rw [Finset.mem_sdiff] at hi ⊢
    have hmem:(permOf di)⁻¹ i∈(mask M':Finset (Fin 13)):=by have:=hM.symm ▸ hi.1;obtain ⟨u,hu,hu2⟩:=Finset.mem_image.mp this;have huq:u=(permOf di)⁻¹ i:=(by rw [←hu2];simp);exact huq ▸ hu
    exact ⟨hmem,fun hS=>hi.2 (hST ▸ Finset.mem_image.mpr ⟨(permOf di)⁻¹ i,hS,by simp⟩)⟩
theorem kill_b1 {D:Dag} {M:Nat} (hM:M∈([4032,8128]:List Nat)) (hsep:∀ i∈(mask M:Finset (Fin 13)),∀ j∈(mask M:Finset (Fin 13)),i≠j→∃ a∈(mask 63:Finset (Fin 13)),z4 neigh j a∧¬z4 neigh i a) (h6:6∈(mask M:Finset (Fin 13))) (h:z0 13 D) (hc:z3 13 (z4 neigh) D) (hz:qd 13 D≤1) (bp:zu 13 D=10) (hw0:∃ w,2≤zd D w∧supp 13 D w=(mask 24:Finset (Fin 13))∧2≤(supp 13 D w).card) (eq:(mask M:Finset (Fin 13))=z1 13 D):False:=by
  obtain ⟨Bad,hBsub,hBcard,hBex⟩:=vz gr h hc hz (mask 63) (mask M) (by decide +kernel) (fun i hi=>⟨eq ▸ hi,rfl⟩) hsep
  have hcov:∃ d∈(mask M:Finset (Fin 13)),Bad⊆mask (1<<<d.val):=by
    by_cases hemp:Bad=∅
    · exact ⟨6,h6,by simp [hemp]⟩
    · have hc1:Bad.card=1:=(by have:=Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hemp);omega)
      obtain ⟨d,hd⟩:=Finset.card_eq_one.mp hc1;refine ⟨d,hBsub (hd ▸ Finset.mem_singleton_self d),fun x hx=>?_⟩
      rw [hd,Finset.mem_singleton] at hx;subst hx;simp [mask,Nat.testBit_shiftLeft]
  obtain ⟨d,hdM,hBd⟩:=hcov
  have hdM':M.testBit d.val=true:=by simpa [mask] using hdM
  exact movC1 h hc bp hw0 eq (fun i hi=>hBex i (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hi).1,fun hB=>(Finset.mem_sdiff.mp hi).2 (hBd hB)⟩)) (c1Cov1 M hM d hdM')
theorem kill_b2_8128 {D:Dag} (h:z0 13 D) (hc:z3 13 (z4 neigh) D) (hz:qd 13 D≤2) (bp:zu 13 D=9) (hw0:∃ w,2≤zd D w∧supp 13 D w=(mask 24:Finset (Fin 13))∧2≤(supp 13 D w).card) (eq:(mask 8128:Finset (Fin 13))=z1 13 D):False:=by
  have hge6:∀ x:Fin 13,x∈(mask 8128:Finset (Fin 13))→6≤x.val:=by decide +kernel
  have hlt6:∀ x:Fin 13,6≤x.val→(8128:Nat).testBit x.val=true:=by decide +kernel
  obtain ⟨Bad,hBsub,hBcard,hBex⟩:=vz gr h hc hz (mask 63) (mask 8128) (by decide +kernel) (fun i hi=>⟨eq ▸ hi,rfl⟩) (by decide +kernel)
  have hcov:∃ d1 d2:Fin 13,6≤d1.val∧d1.val<d2.val∧Bad⊆{d1,d2}:=by
    by_cases h0:Bad.card=0
    · exact ⟨6,7,by decide,by decide,by simp [Finset.card_eq_zero.mp h0]⟩
    · by_cases h1:Bad.card=1
      · obtain ⟨a,ha⟩:=Finset.card_eq_one.mp h1;have ha6:=hge6 a (hBsub (ha ▸ Finset.mem_singleton_self a))
        by_cases ha12:a.val=12
        · exact ⟨6,a,by decide,by omega,by intro x hx;rw [ha,Finset.mem_singleton] at hx;simp [hx]⟩
        · exact ⟨a,12,ha6,by omega,by intro x hx;rw [ha,Finset.mem_singleton] at hx;simp [hx]⟩
      · have hc2:Bad.card=2:=(by omega);obtain ⟨a,b,hne,hab⟩:=Finset.card_eq_two.mp hc2
        have ha6:=hge6 a (hBsub (hab ▸ Finset.mem_insert_self a {b}));have hb6:=hge6 b (hBsub (hab ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)))
        by_cases hlt:a.val<b.val
        · exact ⟨a,b,ha6,hlt,by simp [hab]⟩
        · exact ⟨b,a,hb6,by omega,by intro x hx;rw [hab] at hx;simp at hx ⊢;tauto⟩
  obtain ⟨d1,d2,hd1,hd12,hBd⟩:=hcov
  have hsub:Bad⊆mask ((1<<<d1.val)|||(1<<<d2.val)):=fun x hx=>by rcases Finset.mem_insert.mp (hBd hx) with rfl|hx2;simp [mask,Nat.testBit_or,Nat.testBit_shiftLeft];rw [Finset.mem_singleton] at hx2;subst hx2;simp [mask,Nat.testBit_or,Nat.testBit_shiftLeft]
  exact movC1 h hc bp hw0 eq (fun i hi=>hBex i (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hi).1,fun hB=>(Finset.mem_sdiff.mp hi).2 (hsub hB)⟩)) (c1Cov2 d1 d2 (hlt6 d1 hd1) (hlt6 d2 (by omega)) hd12)
def sa0:Array (List Nat):=zj yy [0x2c6c6c2c6c185090505050104808880888484848085004480440804040400050,0x8522180152014405001800522c9d048404844b27402102c9c0086c08ac10,0x2d162414505441890604140d5b3588c513140c60314495025489542190,0x7211064711104430101d517549d527145c547181c524545150454f]
def st0:Array (List Nat):=zj (fun x=>6+7*(x&&&63)) [0x468023e09d04d026412e0950499008782341160880430214106081050,0x3f044be801877cf03760b96ecc36a11c06d41360da80641b1569c322c025ca8258a82509824898244092050,0x5f39803bb6ea875c75c0c8dc097d8b41d7196835352c075c5540e9826e9500e7cd921919c12d953034b225070e3c50d0c2090,0xf31b807e62720ded6ec1f78d883ef130072da740fabaa41efe3cc343b82dbaf387a4c6c0f496d41e929983cb8f086872057cf620d0,0x2203a41f7602f762d06d41ae0d9d1f03fb8b807f70720e8def41fb99683f722a07074780cd]
def sr0_0:List Nat:=zg w7 [0x389a09044c504d0104d20602606068ec09d8b90a1392a0b92a039246048c7628cb608c90848909121120a1290a122021290212360b03646408c8804c9000c913022624408044840448180108101280812800122c8a4591c4b42489604902d0920581257615ac63600b05b5490028004010c88024002020d486a4001000003f,0x4721317234072345a0d98a0ca020ca11c44c5c4d08]
theorem sic0_0:ze (n:=13) (m:=18) neigh edges goodB false false 24 1 610 mBook sa0 (zr 7 st0) 0 sr0_0=true:=by decide +kernel
def srs0_0:List Nat:=zg (fun x=>9+7*(1+(x&&&511))) [0x23438ac1c327cedbb180f531e3a3c74b8e9cf9118101ca0cb568cc58a12d80c5d1934aa60ae5890b3a10e64c8384139409124a5dd242c55c88570a4273841103cd19300808036065aa94070c1570186]
theorem sro0_0:zo (zr 7 st0) 7 71 srs0_0=true:=by decide +kernel
theorem scf0:zf (zr 7 st0) 77 74 (digits 7 28 0x87197c464e1e3f42dd8a080f531e3a3e64b8e9cf911a30203) 0=true:=by decide +kernel
def sa1:Array (List Nat):=zj yy [0x61b170b100edd82c7008b030b0707070306c08ac1c9c5c5c5c1c44088410,0x4cae097b7c1b115edf02c417b721b1e070446c771c180c170c101b1c83b771b110edd0,0x88521d447571d8075019446521949c2b8170ae01c2b82683205a0c8068320932b814cae10,0x83422d44b5c2d9cb602d40a512948a52254495c259c96025408512150,2755824898]
def st1:Array (List Nat):=zj (fun x=>6+8*(x&&&63)) [0x888021e200870682181a085810c040811714084c111043c10d0a0824107041410300090,0x70f82193e08f4e4d430b3c08e8e021e3808d8d02183408ccbc9c3153208c0b822c2e08a898228260894846c30b24090,0x13d352c30b4e08e93021f4c08d9282194a09251d143154808c51822c4608ad1022844090d04fc30b4208890021f40090,0x1bdc5cc3016e09b5ad9430b6c08eda1a8323666a0cdd91a031d64660d7d858c3015e09756d5c359085c0d64196835904560d454d5430150090,0x1a5e20838360700e0d89c837758800e0549c038154720d9d61f837f52600dfd518837d7b750de449f03157c09e441e832d767a0de439d032974760d0,0x6804e8159059e0d60381837f54107017604b013604a017904b]
def sr1_0:List Nat:=zg w7 [0x4544981131609323893260132381322204444785c8795c4795c0790d021a2e15989c2b40b9856a1718ad40e615a81c62b5341862683102d406285a70c5035018a069c31499598932b40a6e56a14d8ad409b95a81362b52f6525ece2be5a4576b482f96905dad2361486c388d189119f12034624067c4876520ece21bda4436b4806f6900dad2cb2ec1b60cb003800c058c9c02e007008ff,0x1852662522805229728f3128d4028d4b90798906a0106a170e117222e3c12e4712e5c02e4702e45411]
theorem sic1_0:ze (n:=13) (m:=18) neigh edges goodB false true 24 1 517 mBook sa1 (zr 8 st1) 0 sr1_0=true:=by decide +kernel
def srs1_0:List Nat:=zg (fun x=>9+7*(1+(x&&&511))) [0xf423b736690a780730bceae381169b14a812d19b206080b503377f225b17cd985601324d413341cfdbbe6c023ca13381039191444021f1a29002630885029d117100e4d4975058426282d2824d2f3ab8e04566452c0495525d416109090b4e098b0e0870c163018b]
theorem sro1_0:zo (zr 8 st1) 7 80 srs1_0=true:=by decide +kernel
theorem scf1:zf (zr 8 st1) 91 30 (digits 7 19 0x31191423dd3d715de22213c25ab15680a) 0=true:=by decide +kernel
def sa2:Array (List Nat):=zj yy [0x4db771b1a0b1036ddc2c6c08ac2c6c6c2c68a8686868286c18681848088810,0xa3d80f513940e52396cd603568d613140c52314951b81546e0151b8236de86c50,0x41d106439909151456d160456916141410524148f513d4d]
def st2:Array (List Nat):=zj (fun x=>6+7*(x&&&63)) [0x13441203c11c3c11a301163011404102549044411e08d045822410c08404180090,0x3f150037e21e06dddb90c0b6099821d9340c2b2601ab5eb4302a82529d2864d4048130475304692045d2048cf990d0,0x6b3ab075d7480ebac8c1b17d503aab9d07556380e9d19a193a414f21403432a8073c74c0cdcc941c5931c3031028705e86fc6420d0,0x1401400d7b2157b32037e0cb7d603b2ea40765c460c8]
def sr2_0:List Nat:=zg w7 [0xd20f98a0ea020ea2d06cc50650106514736627328073288c0918ec519285196c1192811921024227c3447cb427cb407c8e811d1360b0364a03646408c8aa3662546d02ad0da85571b502b436a055c6d46d948db389b569135ed206d5a40d7b4aec2b58c6c01602a00d002816d5a6a90f3]
theorem sic2_0:ze (n:=13) (m:=18) neigh edges goodB false true 24 1 578 mBook sa2 (zr 7 st2) 0 sr2_0=true:=by decide +kernel
def srs2_0:List Nat:=zg (fun x=>9+6*(1+(x&&&511))) [0x17e53b536c3e6d85a828b59054f21438a4412c3b6e11c4e2e058ce84839b75841d61c5ec640bb1cdb241a81b03ef0a20708185]
theorem sro2_0:zo (zr 7 st2) 6 51 srs2_0=true:=by decide +kernel
theorem scf2:zf (zr 7 st2) 56 19 (digits 6 22 0x356412324cb5be5a6854f688df36ca182) 0=true:=by decide +kernel
def sa3:Array (List Nat):=zj yy [0x210130010101c8007008b00c8c4c4c4c0c44088400088000804040400050,0x1c6080608101820006082405d4444c44450170111501130110405c0044840731011101d0,0x8b522944a532980a60294055115485521144453118046011480718101c610,0x16545890a2405d457525d49651594d6605940b512d4c]
def st3:Array (List Nat):=zj (fun x=>6+7*(x&&&63)) [0x224011e4011c3411834116046022012e5022609104782345042430414106081050,0x3d76e430ef0244e823ee8238e0232e026ec54862db04d1804c9804b9804b1404a9404994049509b0c3a4090,0x159c14d971438e126061e6048e44a0e3829419d892038e022070e0bf0c5c209ac00994009740096be0953e0933e090,0x1ce9620f6efe2195d816bd3943ce4b5079c8680f38ec81dfc38c32b782bb6ea862ee04cec5a0d7d6b41aba96034f52b073e8d30d0,0xac0d67c132079f5ee1f3ebdf808881ce0c706ce6ec1f7c1b83ef8b807273740fad0dc1f5a5c03af1b907ce8600d0,2416558146]
def sr3_0:List Nat:=zg w7 [0x17812f15a1325a5315a5305a45c08b895022a2312a4012a4302a4002a42c0858890810922122311250112430125001240389880714080ae2a100dc5420038a80057150006e2a0001c5403018806040806c0a1009814001b02800260520252404e2828a4503148a00290414520818a41001488052100e22182444204808609010812cb06c0b60c8c026003008c064001000003f,0x3595315974059741ac498ac5a02c5a40a24c4a2d00a2d09]
theorem sic3_0:ze (n:=13) (m:=18) neigh edges goodB false true 24 1 704 mBook sa3 (zr 7 st3) 0 sr3_0=true:=by decide +kernel
def srs3_0:List Nat:=zg (fun x=>9+7*(1+(x&&&511))) [0x5c0d5a9a1284ac038e3e44f10066c68938096265b1766951a76a98c049c2890399996cd4c146211120145416513994c602242c2910258388719f3d6ebc44b16fc16e18375e2214517001030f913c4019d1e24d025dba721c30578065aa940202017018a]
theorem sro3_0:zo (zr 7 st3) 7 72 srs3_0=true:=by decide +kernel
theorem scf3:zf (zr 7 st3) 82 37 (digits 7 22 0xba732849b26cd23cc6a98c4482128cf9b2640a) 0=true:=by decide +kernel
def sa4:Array (List Nat):=zj yy [0xc8c888488048084848084c04400440080480c04800c000804040400050,0x1c9c5c5c5c1c4c1448144c48cc0ccc4c8c4c4c4c0c4c808088488c84c8850,0x300b048f00b0070280a84a8e84e83068728ca8068286868285cdc50,0x1c704870442c770c120c100b1cc2a772a102a120a9dc684068442a770a100a100a9d0,0xc9a72269c49a70269cc4072101cc4044407210130010101c8004c2c772c122c120b1d0,0xcdc72371e87044dc7a0c10371ccb37423122cdc08c504c404c44b374031003102cdd0,0x1820d8a7c2a12629c58a7c0a10629cd02702212409cc4845027012130210409c00850,0x181c83356a08d5a81356a00d5a83024e0809381024e0009383018a0806281018a000628301820806081018210,0x2190209c23a0320336d6a09b5a816d6a01b5a836c7209b1c816c7201b1c8360720981c81607210,0xc552154c45211444531180460114b064b0272867282428642824c864c8250,0x4b532d48b572d80b532980a50298c7521d447571d8075019405511550,0x9451514d46051814513d40f533d48f533948e51394ce623980e603950,0x97515d697605d4d65259456535981660594d552554555a55815535150,0x16a489d094651d165428d1624289063508d4e3528d4e260894a2635d50,567553]
def st4:Array (List Nat):=zj (fun x=>6+9*(x&&&63)) [0x944e1a0c46087c34200c3a086434105c10a82120420083c0c10341e080c1608240c10141018201050,0x12c8c4c0c8e48088a090c120823f047a08ec11c0236046a32086208bc116822b044e28090,0x1a8cc11a0cc1190c01188c0117812a0226041c097cb41174be580cb25a08ae5808aa4e08a65524065104924e090,0x1188a09108a090e813d9d442da1824220024120022ca0023f1e823e1e823c1d023b1d02399b4ce61109e7208e06c08dc6c08926c090,0x160ae0958ae0954a60950a60948a00944a0093e9d4da64427a7823827023426823126024ba55228b100e96081294092490091c90090,0x40cc099ccc0836cc0994c8098cc80988c20980c2097ebd5cad442daf822caf025d2e023f2e025b2d023c2d0259abd4ea11066b2090,0xee40812e20924e0091ee00918de0912de09bad96bb4c427b7026d36023836022635823535826a348232348268b3592c31052d0090,0x162f20958f20956f00950f0094aee0944ee09daeb74b9c414bb02103a8267ba820dba82653a0263ba0262398260b98272b8dc2df110,0x1050208b30208ff0008f90008f2fe08ecfe09fafb7cbdc427bf0238be82373e8235be02343e0232bd82313d827abcde2ef1066f4090,0x8ac4e230f109f1409b51208e31208991008d71009a90e08cb0e0a1b0b84c1c42dc3022cc2823fc2025b418282c0e02ff10b704090b02090,0x5592052390885961e0d0d23908858a1e0d0d2390b2d8a180f0c3491042790051f8eb3d8f160d0d1f8eb3d83160d0d1f8eb1d83160c0c0c8f04278e044b2917038d890b8187c48340e320c290717050,0x46cc2681ccc01300e5f2d419f634581a5f2d419de34581a5f2d3e9de345618492e08bf2c0a57296d93494481a57296db5494481a572926b548c4a18b92a08ab280a4f25379a630481a4f253798e30481a4f253498e3046181926090,0x53e9b4ba38949205383a48fa981d24794a0e923aa30745067f3da0d0c42dcf822ccf029dce66f3112660a9d06079d0533024e0304ce0249cd26c1ccc05360d0,0x2ca1cb50763675a830dda8265d9ad01d942d680ec6c6b406c5b05983b2852c01d8d81600ebb5bafd5c42dd7022cd6823cd5ab01d4c109d4aa81846a5500d0,0x181bfdf6ee25ec61800c67800af62ebf06adbc5f83bd8b2f81aa6f17c0ef62abb06a3bb5e03b8dbeeb73109f7008936e0adb6bb4d844b288ad818a6d81086cd6a0d0,0xb7cc6683cbe57278d132230cb0633cb059117650356e3b281e4459920d538ec9079115630351e331c1e2f1387c1898528628327e28224e202c29130c1e1485820d0,0x31f32d907b3a06703d9d0b301d4665b00f6340af07b1a15583d5ea75fad109faa0893a80b4a08e749a60c6fa4d107a1cfe7732216f4011673c12ef359c0d0,0x37f7cc907bfbb6303d1d93781ef6e9ae0f7b72d60767bd6e03ddd93701de6c5b80f7374c307b9b96083aae436c1edebd9c0f6f56cc0759a46d03dad12a41cd721b20d0,0x9a02424ab8d181ccc1bd834907220e270a1606f61536921149b648899705d3deb801e8f75c00f8386d707c1c16b03cde137c1efefd940d0,0x1aeddd9032402488884486b934324190223445a648108d11241344699b02d99642061202234624e6d7b0b1893920d824624e487d09182449dee6c16b79f9eecc4cfcf76756110,0x5e2ef81dfe5f1aa91f7ef5cbacef1761942b37abbd50296010d82583d89032c091001ee41dceb8265b16d766110658818904dd82cd75b10366bad941960eeff120965050,0x1820b081cd039a3d0434043d236206c373b283dfda82dfe5f02f559de0659bd77f81cbde1503acef1bfc0e5eeeee1cb]
def sr4_0:List Nat:=zg w7 [0x84090b0a6161c827c490458920b0e213e24422c4804f89008b121514c2a3904f492082924151c427a4884149009e920105259655856058309832c08e04289433a0150472843411a00500dc04e01700380d6a4b513219808c02600300110866402321110048224002018d406a0040198008024001000003f,0x80926a10024d400249a800093500c46301890401b128800625100c48100d89420031280036250000c4a0180c603020806040806c0a1009814001b02800260531453628e4c6524987a48b1949161e920c6524187a4a0453408e4819249002492047140c9228012410324820049370a66e1c8dc389b589135f1206d6240d7c4966532cce45a1a48b03489686912c0d205a1a40b03493453268e44bd24490a4812149100a6201c8403888609110812021827f,0xc0e18d81c4130e38a26087144c0e205871c50b0438a061c7140c10e28d5a319ab48235d6944682d284d75a509a0b4a035d6940682d28093318126820124d440049a95]
theorem sic4_0:ze (n:=13) (m:=18) neigh edges goodB false true 24 2 610 mBook sa4 (zr 9 st4) 0 sr4_0=true:=by decide +kernel
def sr4_1:List Nat:=zg w7 [0xc0a9000a90f0b98f2b90f2b88f2b80f21a02c0c5890b1121031246246042488488c449404490c0494004910963c80b1e2058f2c161602c8729e4194f10ca7e50b328164214f200a788053c2858140b2132790193c40c9e642c320590813c8009e2004f02160102c729c384e13270d039881adad18db5a41378b4a26dd6942de2d285b75a50378b4a06dd694d8e18db1c413638816dc7140dd0e2bf,0x3589382c498ac5a02c5a40a24c4a2d00a2d2381c7128e31406114841149781af125e2a15e4a05e4b4266b48d68cc969009694c569005694c169001692b0d1ab235624ac742acb40ac9484cd491a91992920129298a9200a9298292002923e067c48f89d0919d233a2323a5223a5023a447446274a4274a027486074a4074a00748b8197122e2702e4543f,0x4e2a4e515263156811569a5ab325a9415a9405a94944e98c4fa044fa0d474e4a3a7051d3151f4051f41aca98acba02cba5ca3cc0a3515]
theorem sic4_1:ze (n:=13) (m:=18) neigh edges goodB false true 24 2 610 mBook sa4 (zr 9 st4) 147 sr4_1=true:=by decide +kernel
def srs4_0:List Nat:=zg (fun x=>9+9*(1+(x&&&511))) [0xb65e53aa14c0597c40c13705a942159a652e54a0148a0c2146d299c71802d4ea52f90bf1da802844252e16c8566e0b8d3c94a102d166b156a652e913e964a940291429c4aff2c40ca91446b5924d3458d87b128ac09aa912b8f222d180b511c561c896af2b69328114c9514c445581961fe5249a2d2e928125922574a2360295471584a38a64002c772fab15b555103c16aa55d2c5342061dcbeaeaa2a8e45aa58a686092f1e4c27830040e85c149d812592daa152de8c549f8ed401402aab532b00b43a14bcee5f06c41c0609b82e34aa52842994ba44b254a0148a0c22726a04a27e273ac94ef7b43ea0e9a7cde9d5196d30fa1277bf9d6fa7b1f89481a6c3ea137a71f2992d8f841defe75be89c512653ded0f25cdcf67aa64b63e107c4821eef9bba6992d7f0209a81289f89cfa7f3e29b0f3d12a6f1e73d325a7d0893d02513e130fe0547a291abd5d8e06e9151d2974b9138981e2415d2c529209d0e851a6e9d4bb489651811411b0d47a3c13d24568b04514763a4800dccf58dc8a130879b96491d8241de4e41051e89408305a7d170abd5cd238e3cdcb248ebc9c82082512813e8305a2c1171841b8d914b840a8a462f17a9151ae44eba130ad240b733d6372284c21e6e592c767f07793904105824642f409f4b20c168b860b679309e0c01039168527304964f2613c18020742e0a4e20947a3178bb48a8d72275d098482b49031c4df6db601c0c05025c6087ab9a471c79b964b1d793904105824667d2c8305c2d1609991369a9ecf008b59bade209d97a7cc61f4f015313a9cad047369d878552a158a04c173199d6cb85aa904d37884bcd0055a08c45360f4a8562a141a42a344d0ce713a11878c42d150bc14264e4dcce66881a65e683281446229ccda542b150a24c134ca756cb85aa904d37884bd3c055a08c4536950ac54284f8513eb64d194c86933c996aa4134de212f02a78d09c9b0796823110c8612a158a850990ec05a8c79880c582f58a1508899acd2668819a855e2311079602a1a0485c3316ac55e2341a08543404ac95f32188a9040523114904759ac95e2343a18544905a11108759abc4632188a9120964c0e17146b45604d564431a2d013cc00f2d9534856088685206c989c2a2b0264431a2d013cb654d2158200f0e088f8e0443690582c65fcb9886f21b08dc42019a8204038110de43031ac7e28360258ac3602f80802008018c0894051dc02938699a027ebedf2f70984822147f021e8f1780843a1c7a819d8ea7404c2411778199ccc6586c321867819329b4f2dd70235a2d5482a4f82b5]
theorem sro4_0:zo (zr 9 st4) 9 294 srs4_0=true:=by decide +kernel
theorem scf4:zf (zr 9 st4) 347 97 (digits 9 41 0x5e2e2a5b8da71b5d4d1802d4ea52f90bf1da802844252e1300566f1a79294215aacd62ad4ca5d227d2c952805228) 0=true:=by decide +kernel
def sa5:Array (List Nat):=zj yy [0xac06c2c6c6c2c4d818098489818d85898585858185048d009005010,0x62b142b120eddc6c586c506c443b770b160b100edd02c4c0ac0ac48ec2cac50,0x28586c1841567a0613411cc90409049047314101411411cc1041047004130eddcac50,0x41611309a00c2684061302520809481025200094830212080848102120008483559c9567b1611559d0,0x12c24d064d026d0d0ced8cd31b824c6e0531b804c6e0d12b8244ae0512b8044ae0cc2682309a10,0xb45991604551160414cd523544d5b3598d643580d50315ac65ac252c650,0x1064345491514544]
def st5:Array (List Nat):=zj (fun x=>6+8*(x&&&63)) [0xa41272208949c7831f22088411d1e086c11904545821315100c3c10d042c109041c1020102090,0x111182433b332d108d082403a08f8e823c3a087ce82383208d8c8234320874c82302c08b8b022a2c0898114050,0x19d95856c417660845902626009798025c5a096168257514b47101558254500949402035009392824c4a08052824846090,0x1e1e82777573711015d825574080dd024c720925c026f6d6b691015b82546c094db02036c0939a824d6a0921a024568090,0x7e402398e08da382318c08ba3028b898785108e2821f8808de1822f840a0e05f5ec4178208460025f7c09f9f02597a090,0x2867cf4ae60786a19f352b981c181a802279e0a766d553e580869d9b554996021a766d3d2658006079c08a26829906240e5c195064e463e344239209064023e90090,0x5ed02ad0cb20c46c8263aeb00eb42ac037faab00d76a2b83ad08a80de6a2a83a706968cfcde50786a5a33f2f941e1a968cdcbe5070612a4089e882a19f3d35981e190,0x31e9ad83c5c3c1bb108f102bf20c20cfef30833db8c20ee4f3083bf1ac00cdef3003b934c00efc62e832fbabc0ee4aae83b706d6cec6a44ad0eb40d0,0xec11e320870dcf0bc4aeaa6581b0141c1776f9d574b15ddb5be7518577576f9d4b5519b5bdddd51859d576c0cec7c2ad061cec7c3afbec60ef6b3183abb8c60d0,0x3001b106c6e82b9044]
def sr5_0:List Nat:=zg w7 [0x943181288200e514404a20400945000728a0210c604220803845100108a202110201c228400845000708a0002114ab14d56392ac7156d922ad32415b6482b4c9410a6821c903449200892410e281a24500448a087040d120802243b29876720ded241b5a4834b49076710ded221b5a4434b48876700ded201b5a4034b4aec6b4ec164b19584ac03611b00580188c336013005800c01420a07f,0x68c7648c8c48c8848ca848cb628c8c28ca828cb608c8c08ca808c9081b0b19b233636236446c5626cac26c8826c9606cac06c8806c8c810b5bc81ade20d6f6b163582c852de4096f104b7a58b12c164268f20347881a3cd056680c1b474a1b4ad9a98d98d31b4126e36a24d86d4498da05371b50a6c36a04dc6d409b0da912b31a2568244ad028b15a81162b5184c63309904613204ca26509884ca0328994062132bf,0x5a0d9d906cc88366083288c05]
theorem sic5_0:ze (n:=13) (m:=18) neigh edges goodB false true 24 2 774 mBook sa5 (zr 8 st5) 0 sr5_0=true:=by decide +kernel
def srs5_0:List Nat:=zg (fun x=>9+8*(1+(x&&&511))) [0x219683313225a9a6bbc128c040a93c0e0d8cbfb08704c94847c239332a08884607cad14bcfca99da5c5b50cb41989912d4e0935e1ddf9460205f549bd10b9e8706c6865fd84381e46423e11c999504440250860568a5e7e54ced2e2da865a0cc4ca9aa696e8a30102a4de885d04383632fec21c0eeb211f08e4cca8222010842b73765f60567b0d817d5d1b1a197f5c0e8b8f847266117e0b15a2979f9533b4b8c636a196c041033b3c313f323da829a6c6a63a2faf0a09892b0f40bea90eb7a21706c7052ebfb0ae0703c2c5c239332a088804a10ecad14bcfca99da5c631b50cb6020819cdd589f995ed414d2e35dd798205f549bd10b9593975fd8570381c34605c58562e11c99950444021086e568a5e7e54ced2e3190104f2f8da865afc0ce8eec502c6fade885cfec21c0e1708e4cca822208426402f45442e2c41076c6a10290598992c919110c5431e9b93abac00aa879c042249a1a20a0086600707660af0e403eaa1eb20b33315b5a24288757863c550f3806191f1c1c98100f9d01ca08d68956d5cd8d4d1543c801628a63c9a2e8ea43b069e18980b706e6b680504030271040c298f2589a32529248ea7a406270351]
theorem sro5_0:zo (zr 8 st5) 8 131 srs5_0=true:=by decide +kernel
theorem scf5:zf (zr 8 st5) 148 140 (digits 8 36 0x432d0662654d534b8274757e5180817d527a1c1b1a197f610e9392908f84726654111008) 0=true:=by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem no_dag:¬∃ D:Dag,z0 13 D∧D.length≤23∧z3 13 (z4 neigh) D∧(9:Fin 13)∈z1 13 D∧∃ w',2≤zd D w'∧supp 13 D w'={3,4}:=by
  rintro ⟨D,h,hlen,hc,h9,w',hfw',hsw'⟩
  have hw0:∃ w,2≤zd D w∧supp 13 D w=(mask 24:Finset (Fin 13))∧2≤(supp 13 D w).card:=⟨w',hfw',by rw [hsw'];decide +kernel,by rw [hsw'];decide +kernel⟩
  have hsur:=xo h;have hsp:=x6 13 D;obtain ⟨m,enc⟩:=repr 13 (z1 13 D)
  have hok:poss 11 m.val=true:=poss_of h hc h9 hw0 11 m.val enc (by omega)
  have hmem:m.val∈survCap:=by have:=allSurv m;simpa [survTest,hok] using this
  have hge9:9≤zu 13 D:=by by_contra hlt;have hp8:=poss_of h hc h9 hw0 8 m.val enc (by omega);have:=List.all_eq_true.mp m3List _ hmem;simp [hp8] at this
  by_cases hbp9:zu 13 D=9
  · have hp9:=poss_of h hc h9 hw0 9 m.val enc hbp9.le
    have hm8:=List.all_eq_true.mp m2List _ hmem;simp only [hp9,Bool.not_true,Bool.false_or,beq_iff_eq] at hm8
    exact kill_b2_8128 h hc (by omega) hbp9 hw0 (hm8 ▸ enc)
  by_cases hbp10:zu 13 D=10
  · have hp10:=poss_of h hc h9 hw0 10 m.val enc hbp10.le
    have hm1:=List.all_eq_true.mp m1List _ hmem;simp only [hp10,Bool.not_true,Bool.false_or,List.contains_iff_mem] at hm1
    obtain ⟨⟨mv,ai,rep⟩,htm,htb⟩:=List.any_eq_true.mp (List.all_eq_true.mp survM1Cov _ hm1)
    simp only [Bool.and_eq_true,beq_iff_eq,List.contains_iff_mem] at htb;rcases htb with ⟨hmveq,hrep⟩
    have hmv:(mask mv:Finset (Fin 13)).image (permOf ai)=mask rep:=zp _ _ _ (fun i=>by rw [permVal ai i];exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp mapM1Ok _ htm) i (List.mem_finRange i)))
    obtain ⟨h1,h2,h4,h5,h6,hw'⟩:=shiftC1 h hc hw0 (permOf ai) (autoOf ai) (perm24 ai)
    have eq':(mask rep:Finset (Fin 13))=z1 13 (z7 (permOf ai) D):=by rw [h6,←enc,←hmveq,hmv]
    simp only [orbsM1,List.mem_cons,List.not_mem_nil,or_false] at hrep
    rcases hrep with rfl|rfl|rfl|rfl
    · exact xj 10 gr h1 h2 adjE (fun _ _=>rfl) (by omega) (fun h=>by cases h) (by omega) eq' (by decide +kernel) (fun _=>hw') (fun h=>by cases h) (by decide) (by decide) sic0_0 sro0_0 scf0
    · exact kill_b1 (M:=4032) (by decide) (by decide +kernel) (by decide) h1 h2 (by omega) (by omega) hw' eq'
    · have:=side_8000 h1 h2 (by omega) eq';omega
    · exact kill_b1 (M:=8128) (by decide) (by decide +kernel) (by decide) h1 h2 (by omega) (by omega) hw' eq'
  have hbp11:zu 13 D=11:=by omega
  have hbz0:qd 13 D=0:=by omega
  obtain ⟨⟨mv,ai,rep⟩,htm,htb⟩:=List.any_eq_true.mp (List.all_eq_true.mp survCapCov _ hmem)
  simp only [Bool.and_eq_true,beq_iff_eq,List.contains_iff_mem] at htb;rcases htb with ⟨hmveq,hrep⟩
  have hmv:(mask mv:Finset (Fin 13)).image (permOf ai)=mask rep:=zp _ _ _ (fun i=>by rw [permVal ai i];exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp mapCapOk _ htm) i (List.mem_finRange i)))
  obtain ⟨h1,h2,h4,h5,h6,hw'⟩:=shiftC1 h hc hw0 (permOf ai) (autoOf ai) (perm24 ai)
  have eq':(mask rep:Finset (Fin 13))=z1 13 (z7 (permOf ai) D):=by rw [h6,←enc,←hmveq,hmv]
  simp only [orbsCap,List.mem_cons,List.not_mem_nil,or_false] at hrep
  rcases hrep with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact xj 11 gr h1 h2 adjE (fun _ _=>rfl) (by omega) (fun _=>by omega) (by omega) eq' (by decide +kernel) (fun _=>hw') (fun h=>by cases h) (by decide) (by decide) sic1_0 sro1_0 scf1
  · exact cd0 h1 h2 (by omega) (by omega) hw' 551 3 eq' [8,10,11] [(0,1858,1106,0,0,8,10,0,5),(0,3713,2185,5,0,10,11,0,2),(3,2504,0,1,2,11,8,7,0),(0,3713,1169,1,0,11,10,0,2)] (by decide +kernel) (by decide +kernel)
  · exact xj 11 gr h1 h2 adjE (fun _ _=>rfl) (by omega) (fun _=>by omega) (by omega) eq' (by decide +kernel) (fun _=>hw') (fun h=>by cases h) (by decide) (by decide) sic2_0 sro2_0 scf2
  · exact z5v 11 gr h1 h2 adjE (fun _ _=>rfl) (by omega) (fun _=>by omega) (by omega) eq' (by decide +kernel) (fun _=>hw') (fun h=>by cases h) (by decide) (by decide) (by decide) sic4_0 sic4_1 sro4_0 scf4
  · exact xj 11 gr h1 h2 adjE (fun _ _=>rfl) (by omega) (fun _=>by omega) (by omega) eq' (by decide +kernel) (fun _=>hw') (fun h=>by cases h) (by decide) (by decide) sic3_0 sro3_0 scf3
  · exact cd0 h1 h2 (by omega) (by omega) hw' 770 1 eq' [3,4] [(0,63,2089,8,0,4,3,0,9)] (by decide +kernel) (by decide +kernel)
  · exact xj 11 gr h1 h2 adjE (fun _ _=>rfl) (by omega) (fun _=>by omega) (by omega) eq' (by decide +kernel) (fun _=>hw') (fun h=>by cases h) (by decide) (by decide) sic5_0 sro5_0 scf5
  · exact cd0 h1 h2 (by omega) (by omega) hw' 834 2 eq' [0,3,4] [(0,63,4148,6,0,0,4,0,8),(0,63,2089,8,0,4,3,0,9)] (by decide +kernel) (by decide +kernel)
  · have:=pv h1 h2 (by omega) hw' 1794 0 (by decide) rfl eq';omega
  · have:=pv h1 h2 (by omega) hw' 1858 1 (by decide) rfl eq';omega
  · have:=pv h1 h2 (by omega) hw' 1920 2 (by decide) rfl eq';omega
  · have:=pv h1 h2 (by omega) hw' 1984 3 (by decide) rfl eq';omega
  · exact cd0 h1 h2 (by omega) (by omega) hw' 2816 1 eq' [3,4] [(2,63,0,8,11,4,3,0,9)] (by decide +kernel) (by decide +kernel)
  · exact cd0 h1 h2 (by omega) (by omega) hw' 3008 3 eq' [0,1,2] [(0,63,4148,8,0,0,2,0,6),(3,63,0,7,11,1,0,5,0),(0,63,4148,7,0,1,2,0,11),(0,63,1043,6,0,2,1,0,11)] (by decide +kernel) (by decide +kernel)
  · have:=pv h1 h2 (by omega) hw' 3904 4 (by decide) rfl eq';omega
  · exact cd0 h1 h2 (by omega) (by omega) hw' 4032 4 eq' [0,1,2,5] [(0,63,4148,8,0,0,2,0,6),(0,63,4148,6,0,0,5,0,8),(3,63,0,7,11,1,0,5,0),(0,63,4148,11,0,1,5,0,7),(2,63,0,6,10,2,1,0,11),(2,63,0,6,11,2,5,0,10),(2,63,0,7,10,5,0,1,8),(2,63,0,8,10,5,1,0,7),(2,63,0,7,8,5,2,1,10)] (by decide +kernel) (by decide +kernel)
  · have:=pv h1 h2 (by omega) hw' 7936 5 (by decide) rfl eq';omega
  · have:=pv h1 h2 (by omega) hw' 8000 6 (by decide) rfl eq';omega
  · have:=pv h1 h2 (by omega) hw' 8128 7 (by decide) rfl eq';omega
end G_C1
namespace G_C2
open DagTools Resolution Compact GraphTools Reduction
def neigh:List Nat:=[1024,8832,12544,6272,11264,5632,2816,10,68,98,49,88,44,22]
def edges:List (Nat×Nat):=[(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
def goodB:Fin 14→Bool:=(fun v:Fin 14=>v.val != 0)
def mBook:List Nat:=[127,245,315,433,541,661,793,1102,1220,1290,1548,2087,2213,2339,2693,3078,3716,4179,4305,4371,5009,5186,6403,7426,8297,8417,8489,8969,9288,9992,10657,12481,13504,15233,16256]
theorem gr:zc (z4 neigh) (fun v=>goodB v=true):=by unfold zc;decide +kernel
theorem edgesOk:∀ q∈edges,∃ hu:q.1<14,∃ hv:q.2<14,z4 neigh ⟨q.1,hu⟩ ⟨q.2,hv⟩:=by decide +kernel
theorem adjE:∀ e:Fin 19,z4 neigh (zh 14 edges false e.val) (zh 14 edges true e.val):=by decide +kernel
theorem deg3:∀ j:Fin 14,(z9 neigh Finset.univ j).card≤3:=by decide +kernel
theorem girth6:∀ i j:Fin 14,i≠j→(z9 neigh Finset.univ i∩z9 neigh Finset.univ j).card≤1:=by decide +kernel
theorem hGoodM:∀ v:Fin 14,(16382:Nat).testBit v.val=true→ goodB v=true:=by decide +kernel
theorem hcov_aux:∀ u v:Fin 14,z4 neigh u v→(goodB u=true∧goodB v=true∧∃ a,z4 neigh u a∧a≠v)∨u=10∨v=10:=by decide +kernel
theorem cover {D:Dag} (h:z0 14 D) (hc:z3 14 (z4 neigh) D) (h10:(10:Fin 14)∈z6 14 D):∀ u v:Fin 14,z4 neigh u v→u∈z6 14 D∨v∈z6 14 D:=by
  intro u v huv;rcases hcov_aux u v huv with ⟨huG,hvG,hd⟩|rfl|rfl
  · exact wu gr h hc huG hvG huv hd
  · exact Or.inl h10
  · exact Or.inr h10
def permLists:List (List Nat×List Nat):=[([0,1,2,3,4,5,6,7,8,9,10,11,12,13],[0,1,2,3,4,5,6,7,8,9,10,11,12,13]),([0,1,6,3,5,4,2,7,8,13,10,12,11,9],[0,1,6,3,5,4,2,7,8,13,10,12,11,9]),([0,3,2,1,5,4,6,7,8,11,10,9,13,12],[0,3,2,1,5,4,6,7,8,11,10,9,13,12]),([0,3,6,1,4,5,2,7,8,12,10,13,9,11],[0,3,6,1,4,5,2,7,8,12,10,13,9,11]),([0,2,1,6,4,5,3,8,7,12,10,11,9,13],[0,2,1,6,4,5,3,8,7,12,10,11,9,13]),([0,2,3,6,5,4,1,8,7,13,10,9,11,12],[0,6,1,2,5,4,3,8,7,11,10,12,13,9]),([0,6,1,2,5,4,3,8,7,11,10,12,13,9],[0,2,3,6,5,4,1,8,7,13,10,9,11,12]),([0,6,3,2,4,5,1,8,7,9,10,13,12,11],[0,6,3,2,4,5,1,8,7,9,10,13,12,11])]
theorem autsOk:permLists.all (wd 14 neigh)=true:=by decide +kernel
def permOf (k:Nat):Equiv.Perm (Fin 14):=va (neigh:=neigh) permLists autsOk (by decide) k
theorem autoOf (k:Nat):auto neigh (permOf k):=z1b (neigh:=neigh) permLists autsOk (by decide) k
theorem permVal (k:Nat) (i:Fin 14):(permOf k i).val=(permLists.getD k (permLists.getD 0 ([],[]))).1.getD i.val 0:=z06 (neigh:=neigh) permLists autsOk (by decide) k i
theorem autC2Ok:permLists.all (fun fg=>fg.1.getD 0 0==0&&(List.range 14).all fun c=>!(c==0||c==4||c==5)||(let y:=fg.1.getD c 0;y==0||y==4||y==5))=true:=by decide +kernel
theorem perm0 (k:Nat):permOf k 0=0:=Fin.ext (by rw [permVal k 0];exact beq_iff_eq.mp ((Bool.and_eq_true _ _).mp (wk (d:=([],[])) autC2Ok (by decide) k)).1)
theorem perm45 (k:Nat):∀ c:Fin 14,c.val=0∨c.val=4∨c.val=5→(permOf k c).val=0∨(permOf k c).val=4∨(permOf k c).val=5:=fun c hc=>by rw [permVal k c];have h1:=List.all_eq_true.mp ((Bool.and_eq_true _ _).mp (wk (d:=([],[])) autC2Ok (by decide) k)).2 c.val (List.mem_range.mpr c.isLt);rcases hc with h|h|h <;> simp [h,Bool.or_eq_true,beq_iff_eq] at h1 ⊢ <;> tauto
def wSpecs:List wn:=[(14,12288,14,2,1,56322,70541537<<<168),(18,8192,18,1,0,0,305<<<184),(24,2048,24,1,0,0,305<<<156),(34,512,34,1,0,0,305<<<128),(36,4096,36,1,0,0,793<<<168),(58,5632,58,3,2,829781,0xe840003b81d3<<<132),(640,2,640,1,0,0,135938048),(4224,8,4224,1,0,0,2087<<<42),(4992,44,4992,3,2,340684,4846647289438313<<<28),(8448,4,8448,1,0,0,4179<<<28),(48,1024,48,1,0,0,2693<<<140),(82,2560,82,2,1,47366,415538088101<<<126),(96,512,96,1,0,0,645<<<127),(100,4608,100,2,1,51461,0xc640000001113<<<126),(116,5632,116,3,2,829781,0x4e100007702e81<<<127),(768,64,768,1,0,0,2087<<<84),(896,66,896,2,1,24841,0x8270000000000000081a4000),(4480,12,4480,2,1,12812,34201705<<<28),(10624,22,10624,3,2,270813,0x44e00010530874000),(20,8192,20,1,0,0,645<<<183),(28,6144,28,2,1,51971,19163681<<<155),(40,4096,40,1,0,0,661<<<168),(42,4608,42,2,1,51461,0xa5400000010d1<<<126),(80,2048,80,1,0,0,645<<<155),(2176,8,2176,1,0,0,4179<<<42),(2304,64,2304,1,0,0,541<<<84),(4352,4,4352,1,0,0,8297<<<28),(8320,2,8320,1,0,0,8863744),(14848,22,14848,3,2,270813,0x44e000013b03d4000),(6,8192,6,1,0,0,433<<<182),(12,4096,12,1,0,0,433<<<168),(26,10240,26,2,1,56068,594047672545<<<154),(38,4608,38,2,1,51461,0xc6400000010d1<<<126),(50,1536,50,2,1,43269,11030833<<<128),(52,5120,52,2,1,51717,346281744643<<<140),(56,3072,56,2,1,47620,19991173<<<140),(66,512,66,1,0,0,433<<<126),(72,2048,72,1,0,0,433<<<154),(84,10240,84,2,1,56068,627870540073<<<154),(104,2560,104,2,1,47366,88717919747<<<127),(112,1536,112,2,1,43269,22061701<<<127),(2432,72,2432,2,1,25355,0x8740000001053<<<42),(2560,64,2560,1,0,0,315<<<84),(2688,10,2688,2,1,12551,0x414c00081a4000),(4608,32,4608,1,0,0,551<<<71),(4736,10,4736,2,1,12551,9178723204612096),(4864,36,4864,2,1,21004,4846647255244905<<<28),(6144,8,6144,1,0,0,245<<<42),(6400,12,6400,2,1,12812,4022377<<<28),(8576,6,8576,2,1,8461,1121800634368),(8704,2,8704,1,0,0,4014080),(8960,6,8960,2,1,8461,1121795784704),(10240,16,10240,1,0,0,551<<<57),(10368,10,10368,2,1,12551,0x414c0000874000),(10496,20,10496,2,1,16909,295815876691<<<28),(12288,4,12288,1,0,0,315<<<28),(12416,6,12416,2,1,8461,84566032384),(54,5632,54,3,2,829781,686645015445971<<<132),(60,11264,60,3,2,899652,0x7408000d303b81<<<140),(70,8704,70,2,1,55553,0x31900000000002129<<<126),(74,2560,74,2,1,47366,177435838629<<<126),(76,6144,76,2,1,51971,38326547<<<154),(114,11264,114,3,2,899652,0x3a100009c23b81<<<140),(120,5632,120,3,2,829781,8171570542423681<<<127),(6656,40,6656,2,1,21260,295815872757<<<42),(6784,98,6784,3,2,414105,0x13b1138000000000081a4000),(6912,44,6912,3,2,340684,4846647259258985<<<28),(10752,18,10752,2,1,16653,0x44e000000003d4000),(10880,88,10880,3,2,410555,0x4ec0001139053<<<42),(11008,22,11008,3,2,270813,0x44e000105303d4000),(12800,6,12800,2,1,8461,84561182720),(12928,44,12928,3,2,340684,4846647289430331<<<28),(13056,98,13056,3,2,414105,0x8271138000000000003d4000),(14336,12,14336,2,1,12812,4014395<<<28),(14464,22,14464,3,2,270813,0x44e000013b0874000),(14592,88,14592,3,2,410555,0x87400011380f5<<<42)]
def wts:=wSpecs.map vp
theorem wRows:wSpecs.all (vc 14 neigh goodB 0)=true:=by decide +kernel
def poss (c m:Nat):=z0r 14 edges wts 1 1024 0 c m
def orbsCap:List Nat:=[11,23,31,63,79,95,127,133,145,149,177,181,197,213,245,385,401,433,517,525,529,533,541,645,657,661,913,2565,2693,2817,2945,4625,4753,5009,7041,14977,15233]
def orbsM1:List Nat:=[95,127,197,401,433,661,15233]
def mapCap:List (Nat×Nat×Nat):=[(11,0,11),(23,0,23),(31,0,31),(45,2,23),(47,2,31),(63,0,63),(69,4,11),(79,0,79),(87,4,31),(89,3,23),(91,3,31),(93,7,31),(95,0,95),(99,1,23),(103,5,31),(107,1,31),(109,6,31),(111,1,95),(119,4,63),(123,1,63),(125,6,63),(127,0,127),(133,0,133),(145,0,145),(149,0,149),(161,1,145),(165,2,149),(177,0,177),(181,0,181),(193,1,133),(197,0,197),(209,3,149),(213,0,213),(225,1,149),(229,1,213),(241,1,181),(245,0,245),(259,4,133),(265,6,133),(267,4,197),(273,4,145),(275,4,149),(281,7,149),(283,4,213),(289,5,145),(291,5,149),(297,6,149),(299,5,213),(305,4,177),(307,4,181),(313,6,181),(315,4,245),(385,0,385),(401,0,401),(417,1,401),(433,0,433),(517,0,517),(521,7,517),(525,0,525),(529,0,529),(533,0,533),(537,7,533),(541,0,541),(645,0,645),(657,0,657),(661,0,661),(777,7,645),(785,7,657),(793,7,661),(913,0,913),(2051,5,517),(2053,2,517),(2055,2,525),(2081,2,529),(2083,5,533),(2085,2,533),(2087,2,541),(2181,2,645),(2209,2,657),(2213,2,661),(2307,5,645),(2337,5,657),(2339,5,661),(2465,2,913),(2565,0,2565),(2693,0,2693),(2817,0,2817),(2945,0,2945),(4099,4,517),(4113,3,529),(4115,4,533),(4161,3,517),(4163,3,525),(4177,3,533),(4179,3,541),(4241,3,657),(4289,3,645),(4305,3,661),(4355,4,645),(4369,4,657),(4371,4,661),(4497,3,913),(4625,0,4625),(4753,0,4753),(4881,4,4753),(5009,0,5009),(6147,4,2565),(6273,4,2817),(6403,4,2693),(6529,4,2945),(7041,0,7041),(8201,6,517),(8225,1,529),(8233,6,533),(8257,1,517),(8265,1,525),(8289,1,533),(8297,1,541),(8353,1,657),(8385,1,645),(8417,1,661),(8457,6,645),(8481,6,657),(8489,6,661),(8609,1,913),(8713,6,2565),(8833,6,2817),(8969,6,2693),(9089,6,2945),(10273,1,4625),(10401,1,4753),(10529,5,4753),(10657,1,5009),(11137,2,7041),(12353,1,2565),(12481,1,2693),(12545,1,2817),(12673,1,2945),(13185,3,7041),(14721,1,7041),(14977,0,14977),(15105,4,14977),(15233,0,15233)]
def mapM1:List (Nat×Nat×Nat):=[(95,0,95),(111,1,95),(127,0,127),(197,0,197),(267,4,197),(401,0,401),(417,1,401),(433,0,433),(661,0,661),(793,7,661),(2213,2,661),(2339,5,661),(4305,3,661),(4371,4,661),(8417,1,661),(8489,6,661),(15233,0,15233)]
def survCap:=mapCap.map Prod.fst
def survM1:=mapM1.map Prod.fst
theorem mapCapOk:mapCap.all (fun t=>(List.finRange 14).all (fun i=>t.1.testBit i.val==t.2.2.testBit ((permLists.getD t.2.1 (permLists.getD 0 ([],[]))).1.getD i.val 0)))=true:=by decide +kernel
theorem survCapCov:survCap.all (fun m=>mapCap.any (fun t=>t.1==m&&orbsCap.contains t.2.2))=true:=by decide +kernel
theorem mapM1Ok:mapM1.all (fun t=>(List.finRange 14).all (fun i=>t.1.testBit i.val==t.2.2.testBit ((permLists.getD t.2.1 (permLists.getD 0 ([],[]))).1.getD i.val 0)))=true:=by decide +kernel
theorem survM1Cov:survM1.all (fun m=>mapM1.any (fun t=>t.1==m&&orbsM1.contains t.2.2))=true:=by decide +kernel
def survTest (m:Nat):=!(poss 11 m)||survCap.contains m
theorem sc0:∀ j:Fin 2048,survTest (0+j.val)=true:=by decide +kernel
theorem sc1:∀ j:Fin 2048,survTest (2048+j.val)=true:=by decide +kernel
theorem sc2:∀ j:Fin 2048,survTest (4096+j.val)=true:=by decide +kernel
theorem sc3:∀ j:Fin 2048,survTest (6144+j.val)=true:=by decide +kernel
theorem sc4:∀ j:Fin 2048,survTest (8192+j.val)=true:=by decide +kernel
theorem sc5:∀ j:Fin 2048,survTest (10240+j.val)=true:=by decide +kernel
theorem sc6:∀ j:Fin 2048,survTest (12288+j.val)=true:=by decide +kernel
theorem sc7:∀ j:Fin 2048,survTest (14336+j.val)=true:=by decide +kernel
theorem allSurv (m:Fin 16384):survTest m.val=true:=by
  let j:Fin 2048:=⟨m.val%2048,Nat.mod_lt _ (by decide)⟩
  by_cases q0:m.val/2048=0
  · have e:m.val=0+j.val:=by dsimp [j];omega
    rw [e];exact sc0 j
  by_cases q1:m.val/2048=1
  · have e:m.val=2048+j.val:=by dsimp [j];omega
    rw [e];exact sc1 j
  by_cases q2:m.val/2048=2
  · have e:m.val=4096+j.val:=by dsimp [j];omega
    rw [e];exact sc2 j
  by_cases q3:m.val/2048=3
  · have e:m.val=6144+j.val:=by dsimp [j];omega
    rw [e];exact sc3 j
  by_cases q4:m.val/2048=4
  · have e:m.val=8192+j.val:=by dsimp [j];omega
    rw [e];exact sc4 j
  by_cases q5:m.val/2048=5
  · have e:m.val=10240+j.val:=by dsimp [j];omega
    rw [e];exact sc5 j
  by_cases q6:m.val/2048=6
  · have e:m.val=12288+j.val:=by dsimp [j];omega
    rw [e];exact sc6 j
  by_cases q7:m.val/2048=7
  · have e:m.val=14336+j.val:=by dsimp [j];omega
    rw [e];exact sc7 j
  omega
theorem m1List:survCap.all (fun m=>!(poss 10 m)||survM1.contains m)=true:=by decide +kernel
theorem m2List:survCap.all (fun m=>!(poss 9 m))=true:=by decide +kernel
theorem poss_of {D:Dag} (h:z0 14 D) (hc:z3 14 (z4 neigh) D) (h0:(0:Fin 14)∈z1 14 D) (h10:(10:Fin 14)∈z6 14 D) (c m:Nat) (enc:(mask m:Finset (Fin 14))=z1 14 D) (lim:zu 14 D≤c):poss c m=true:=by
  have hEl:∀ v∈z6 14 D,goodB v=true:=fun v hv=>by by_contra hn;have hv0:v=0:=(by clear hv;revert v hn;decide +kernel);subst hv0;exact (qt.mp h0) hv
  obtain ⟨b,hb⟩:=zz gr h.1 hc hEl;have hbase:=z0g h.1 b hb
  exact z05 (cover h hc h10) edgesOk (by decide) (by decide) (fun x hx=>by have hx0:x=0:=(by revert x hx;decide +kernel);exact hx0 ▸ h0) (by rw [Finset.disjoint_left];intro x hx hin;have hx10:x=10:=(by clear hin;revert x hx;decide +kernel);subst hx10;exact (qt.mp hin) h10) (by omega) (fun r hr sub=>by rw [wts,List.mem_map] at hr;obtain ⟨s,hs,rfl⟩:=hr;exact v3 gr h hc hEl (fun h=>absurd rfl h) s (List.all_eq_true.mp wRows _ hs) sub) enc lim
theorem noTwo_1 {D:Dag} (h:z0 14 D) (hc:z3 14 (z4 neigh) D) (hEl:∀ v∈z6 14 D,goodB v=true) (tight:zu 14 D≤(z6 14 D).card) (hv:(1:Fin 14)∈z1 14 D):False:=by
  have w2:=x5 gr h hc hEl tight;obtain ⟨P,hp⟩:=xx (m:=19) gr h hc adjE
  let ae:=z5g gr h hc hp hv;let ps:=z5f gr h hc hp hv;let cp:=couple hp w2;let ex:=yg gr h hc hp w2
  have c0:=ae false 1 3 (by decide)
  have c1:=ps false 1 6 (by decide)
  have c2:=ps false 1 12 (by decide)
  have c3:=cp false 10 11 12 (by decide)
  have c4:=cp true 8 11 18 (by decide)
  have c5:=cp true 5 9 15 (by decide)
  have c6:=cp true 3 6 12 (by decide)
  have c7:=ex false 5 6 15 12 8 (by decide)
  have c8:=ex false 8 9 18 5 7 (by decide)
  have c9:=ex false 8 9 18 15 7 (by decide)
  have c10:=ex false 11 12 8 6 10 (by decide)
  have c11:=ex false 11 12 18 6 10 (by decide)
  have c12:=ex true 8 11 9 10 6 (by decide)
  have c13:=ex true 3 6 1 5 4 (by decide)
  have c14:=ex true 3 12 1 10 2 (by decide)
  have c15:=ex true 3 12 1 11 2 (by decide)
  clear h hc hp w2 tight hv ae ps cp ex hEl;grind (splits:=0) only
theorem noTwo_4 {D:Dag} (h:z0 14 D) (hc:z3 14 (z4 neigh) D) (hEl:∀ v∈z6 14 D,goodB v=true) (tight:zu 14 D≤(z6 14 D).card) (hv:(4:Fin 14)∈z1 14 D):False:=by
  have w2:=x5 gr h hc hEl tight;obtain ⟨P,hp⟩:=xx (m:=19) gr h hc adjE
  let ae:=z5g gr h hc hp hv;let ps:=z5f gr h hc hp hv;let cp:=couple hp w2;let ex:=yg gr h hc hp w2
  have c0:=ae false 10 12 (by decide)
  have c1:=ps false 10 3 (by decide)
  have c2:=ps false 10 6 (by decide)
  have c3:=cp false 4 5 6 (by decide)
  have c4:=cp true 2 13 17 (by decide)
  have c5:=cp true 5 9 15 (by decide)
  have c6:=cp true 3 6 12 (by decide)
  have c7:=ex false 2 3 17 6 7 (by decide)
  have c8:=ex false 5 6 9 3 8 (by decide)
  have c9:=ex false 5 6 15 3 8 (by decide)
  have c10:=ex false 13 15 2 9 10 (by decide)
  have c11:=ex false 13 15 17 9 10 (by decide)
  have c12:=ex true 5 15 4 13 3 (by decide)
  have c13:=ex true 3 12 2 10 2 (by decide)
  have c14:=ex true 6 12 4 10 1 (by decide)
  have c15:=ex true 6 12 5 10 1 (by decide)
  clear h hc hp w2 tight hv ae ps cp ex hEl;grind (splits:=0) only
theorem noTwo_7 {D:Dag} (h:z0 14 D) (hc:z3 14 (z4 neigh) D) (hEl:∀ v∈z6 14 D,goodB v=true) (tight:zu 14 D≤(z6 14 D).card) (hv:(7:Fin 14)∈z1 14 D):False:=by
  have w2:=x5 gr h hc hEl tight;obtain ⟨P,hp⟩:=xx (m:=19) gr h hc adjE
  let ae:=z5g gr h hc hp hv;let ps:=z5f gr h hc hp hv;let cp:=couple hp w2;let ex:=yg gr h hc hp w2
  have c0:=ae true 1 7 (by decide)
  have c1:=ps true 1 9 (by decide)
  have c2:=ps true 1 12 (by decide)
  have c3:=ps true 1 17 (by decide)
  have c4:=ps true 1 18 (by decide)
  have c5:=cp false 7 8 9 (by decide)
  have c6:=cp false 16 17 18 (by decide)
  have c7:=cp true 2 13 17 (by decide)
  have c8:=cp true 8 11 18 (by decide)
  have c9:=cp true 5 9 15 (by decide)
  have c10:=cp true 3 6 12 (by decide)
  have c11:=ex false 1 3 7 6 9 (by decide)
  have c12:=ex false 2 3 17 6 7 (by decide)
  have c13:=ex false 5 6 15 3 8 (by decide)
  have c14:=ex false 7 8 1 11 12 (by decide)
  have c15:=ex false 7 8 1 18 12 (by decide)
  have c16:=ex false 7 9 1 5 11 (by decide)
  have c17:=ex false 8 9 11 15 7 (by decide)
  have c18:=ex false 11 12 8 3 10 (by decide)
  have c19:=ex false 11 12 8 6 10 (by decide)
  have c20:=ex false 13 15 2 5 10 (by decide)
  have c21:=ex false 13 15 2 9 10 (by decide)
  have c22:=ex false 13 15 17 5 10 (by decide)
  have c23:=ex false 17 18 2 11 8 (by decide)
  have c24:=ex false 17 18 13 11 8 (by decide)
  have c25:=ex true 13 17 15 16 1 (by decide)
  have c26:=ex true 8 18 7 16 4 (by decide)
  have c27:=ex true 8 18 7 17 4 (by decide)
  have c28:=ex true 8 18 9 16 4 (by decide)
  have c29:=ex true 8 18 9 17 4 (by decide)
  clear h hc hp w2 tight hv ae ps cp ex hEl;rcases c5 with h1|h1|h1
  · rcases c7 with h2|h2|h2
    · rcases c8 with h3|h3|h3 <;> grind (splits:=0) only
    · grind (splits:=0) only
    · grind (splits:=0) only
  · grind (splits:=0) only
  · grind (splits:=0) only
theorem noTwo_9 {D:Dag} (h:z0 14 D) (hc:z3 14 (z4 neigh) D) (hEl:∀ v∈z6 14 D,goodB v=true) (tight:zu 14 D≤(z6 14 D).card) (hv:(9:Fin 14)∈z1 14 D):False:=by
  have w2:=x5 gr h hc hEl tight;obtain ⟨P,hp⟩:=xx (m:=19) gr h hc adjE
  let ae:=z5g gr h hc hp hv;let ps:=z5f gr h hc hp hv;let cp:=couple hp w2;let ex:=yg gr h hc hp w2
  have c0:=ae true 2 17 (by decide)
  have c1:=ps true 2 16 (by decide)
  have c2:=ps true 2 18 (by decide)
  have c3:=cp false 10 11 12 (by decide)
  have c4:=cp false 16 17 18 (by decide)
  have c5:=cp true 8 11 18 (by decide)
  have c6:=cp true 3 6 12 (by decide)
  have c7:=ex false 2 3 17 6 7 (by decide)
  have c8:=ex false 11 12 8 3 10 (by decide)
  have c9:=ex false 11 12 8 6 10 (by decide)
  have c10:=ex false 17 18 2 8 8 (by decide)
  have c11:=ex false 17 18 2 11 8 (by decide)
  have c12:=ex true 11 18 10 16 3 (by decide)
  have c13:=ex true 11 18 12 16 3 (by decide)
  have c14:=ex true 3 12 2 10 2 (by decide)
  clear h hc hp w2 tight hv ae ps cp ex hEl;grind (splits:=0) only
theorem side_95 {D:Dag} (h:z0 14 D) (hc:z3 14 (z4 neigh) D) (hEl:∀ v∈z6 14 D,goodB v=true) (z:qd 14 D≤1) (eq:(mask 95:Finset (Fin 14))=z1 14 D):12≤zu 14 D:=yc gr h hc hEl deg3 girth6 z (mask 16256) (mask 95) 12 (5:Fin 14) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) eq
theorem side_127 {D:Dag} (h:z0 14 D) (hc:z3 14 (z4 neigh) D) (hEl:∀ v∈z6 14 D,goodB v=true) (z:qd 14 D≤1) (eq:(mask 127:Finset (Fin 14))=z1 14 D):12≤zu 14 D:=yc gr h hc hEl deg3 girth6 z (mask 16256) (mask 127) 12 (1:Fin 14) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) eq
theorem side_15233 {D:Dag} (h:z0 14 D) (hc:z3 14 (z4 neigh) D) (hEl:∀ v∈z6 14 D,goodB v=true) (z:qd 14 D≤1) (eq:(mask 15233:Finset (Fin 14))=z1 14 D):11≤zu 14 D:=yc gr h hc hEl deg3 girth6 z (mask 126) (mask 15233) 11 (9:Fin 14) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) eq
def privList:List z0v:=[(31,14336,0,28,28,14336,[0,0,0,0,0,0,0,0,0,0,0,12481,10657,6403]),(63,13824,32,22,54,5632,[0,0,0,0,0,0,0,0,0,13504,15233,0,9992,0]),(181,13312,0,52,52,13312,[0,0,0,0,0,0,0,0,0,0,12481,0,9288,5186]),(541,14336,0,28,28,14336,[0,0,0,0,0,0,0,0,0,0,0,12481,10657,6403]),(2693,74,0,2688,2688,74,[0,8297,0,4179,0,0,315,0,0,0,0,0,0,0]),(2945,74,0,2688,2688,74,[0,8297,0,4179,0,0,315,0,0,0,0,0,0,0]),(4753,42,0,4736,4736,42,[0,8297,0,2087,0,1102,0,0,0,0,0,0,0,0]),(7041,106,512,6272,6784,98,[0,8297,0,0,0,1102,315,0,0,0,0,0,0,0]),(14977,30,8192,6272,14464,22,[0,541,315,0,1102,0,0,0,0,0,0,0,0,0]),(15233,94,10240,4992,15232,16,[0,0,0,0,1102,0,0,0,0,0,0,0,0,0])]
theorem privsOk:privList.all (vr 14 neigh 16382 0 12)=true:=by decide +kernel
theorem pv {D:Dag} (h:z0 14 D) (hc:z3 14 (z4 neigh) D) (z:qd 14 D=0) (hEl:∀ v∈z6 14 D,goodB v=true) (I idx:Nat) (hidx:idx<privList.length) (hI:(privList[idx]'hidx).1=I) (eq:(mask I:Finset (Fin 14))=z1 14 D):12≤zu 14 D:=wh (w0:=0) (goodMask:=16382) (target:=12) gr h hc hEl hGoodM girth6 (fun h=>absurd rfl h) z (privList[idx]'hidx) (hI.symm ▸ eq) (List.all_eq_true.mp privsOk _ (List.getElem_mem hidx))
theorem cd0 {D:Dag} (h:z0 14 D) (hc:z3 14 (z4 neigh) D) (z:qd 14 D=0) (bp:zu 14 D=11) (hEl:∀ v∈z6 14 D,goodB v=true) (I k:Nat) (eq:(mask I:Finset (Fin 14))=z1 14 D) (vars:List Nat) (steps:List xe) (hcard:(mask I:Finset (Fin 14)).card+11=14+k) (hAll:vars.all (fun v=>decide (v<14))=true∧steps.all (yh 14 neigh 16382 I 0 vars)=true∧yk (if 0==0 then 2^k else 2^(k-1)) 0 vars (fun _=>0) steps=true):False:=xc (k:=k) (w0:=0) (goodMask:=16382) (I:=I) (drop:=0) (bpVal:=11) gr h hc hEl hGoodM bp eq hcard (fun h=>absurd rfl h) (fun P hP i hi hg _=>wy gr h hc z (mask P) hP i (hGoodM i hg) (eq ▸ hi)) vars steps hAll
def sa0:Array (List Nat):=zj yy [0x246464246c206420580898189858585818581450144014581040105010400050,0x307070304ac2c0acac6c6c6c2c68098a85868698ca80682408a424a450,0x24a848ea791a113a9e42840ea7b2a122e9ec6844ba7b0a102e9f4b47474743470b050,0x58a7d0a10629c9697c191b19115a5f0246c24416972469f068451a7c0a160a10469d0,0x1412a0104a827e9f0a845fa707e9c9bb7d1b116ede46c742c642c41bb7d2a12629f46850,0x1ae8266825a826a4ee8ca05a81816a0205a82812a0604a80812a0905a81416a0105a82412a10,0x97515d757605d41656598155155495545181450518015105481500150,0x5d527551c607141c626d45b5c6d81b506959a62654595d65819506150,0x23508946252896e160856616081460528149f517d71f607d41e507550,0x1ca470114042954655b95a6560954a451915a460914a3518d6e3698d90,0x25149412304689a2d47b524b462d08]
def st0:Array (List Nat):=zj (fun x=>6+9*(x&&&63)) [0x8410f821d0434086010b8502098211041e08301050208040c08101018201050,0x12890111c1228243048208fc11e82391d0437046a08cc1188a02158a05c18ac4c2c0c4e28084a22090,0x6b339843171a823419821619823218023118022e964aa1948b81178b81138b01168b01128a81158a811449a490ca450089c4c090,0x462382452182442182419fcf61a110410b9041200fc10b0fc11f0f41188f411e4e66d0c467808ec7208e87208e06c08dc6c090,0x2da9022528822ba88229a8022f280227a7822d278225a7022b27024da5d2a1a613410b12c118928124d1e870c769209208e090,0x132b2085cb208d2b00858b008caae08c4ae090aac085cac0902aa0858aa08faa808c4a8094ea551a853e9d18a4a608bea6089ca4090,0x5e94c9eb4140abd2992d6828157a4f258996828e17812ecbe5b5b0a055d97caeb6140abb2d95d6c261448ba09722f168a8502ae45e63150a055c8b4c62a130a165c042b0b0c035b82b50566b157ab556a9190,0x38416fb75b218edbc1245b4dc0d16d86d06d7040ed66a06cf68b4c314b3826582cd01328302b29901b0d8ac70c52c209820afc00c00d0,0x2060bf5ff010c52fc09f2082df0fa0c12f87b06f579bbc311bd023bbc1e419c5dcf00dda0835d8ea0dd2e77186e5233a0372911cc1b9484e20d0,0x239304759149039087a4819be3d220e421c8f07198dc7430ac6028a821b8a45830cc52241c361f110c2b0c0a1709828707204283838fa101c1c79040d0,0x9db11a01ced8cd20e73379887351b4e031dce029a8d26c1a3665360e6a32980689984c8397cb6521cac252e0c2b2e0a561096072b074a0393c963e1c8441260d0,0x28ef292074777478378c1a881d15d9020dab2aa107436e4d83a1b62601b6dc9400e82d67006fb664f839fb41fc1cfda5000deebe9e073d623f839eb1a001b257d3a0d0,0xa4167b0e00197450bd2988e5064734a70733905383a4caa9c1d3e352c0e9f1c9407179a5303a6c3a581d3621280e2720a5074b874683a5c42381bae91460d0,0x107063f47913c046285810b18820b0b42a7cb42a1c8419cb7d27321126df994c048fc8429a827b4aac556af0b0caf58aac2c2d165608bc5a160e532b090,0x760aed7a12ed7a530d76bd2786bd51054f046]
def sr0_0:List Nat:=zg w7 [0xdeda41b9b4b1452636924c352458da48b0d490636920c352569292d2715b2522b5ca416c9482d729468a48b52451ca48a2d4904729208b524ea291d74923a692275d244e9a481d74903a6925d148bba489774902ee925a01d00680b003800c00590ac03600b005109a842d421a0c8ca403200905c5662ac32600b00180cb545a82d592a0950400003f,0x12f168af2682f25a0605a4ac0958a90a02920029206040c4084000910dd3c82e9e2174fba0610cd3c8269e2134f9a0610b53c81a9e20d4f6a06053396a5a974d81692ae5062d28a065a50c18b4a18196941062d282065a5141a94a2819294306a5286064a5041a94a081929482d255c90b5a51212b4a142d694284ad2810b5a50212b4a242d294484a52850b4a50a1294a042d294084a529fa293f94917da920fb525bb29376716f6d22dcda7f,0xf6a8692d3192f4092f46b1798316a51ca4c5cad01cad20e0262e0680e069050131503405034961b296452c7632c9232cb612c9212ca4858a491491b0c92b04928e1928e451c5631cb231c9611cb211ca281451860b086490865040a08bf0e13f2e0bf2e03f27a0ec09d8b9020392003926e04dc582dc980dc9a8181a9330e9332e8b32e8332620bc3f,0xb9473cca399a514c651502515172866328281282898c3318c1408c14345a98c5ba045ba31edccf]
theorem sic0_0:ze (n:=14) (m:=19) neigh edges goodB true false 0 1 433 mBook sa0 (zr 9 st0) 0 sr0_0=true:=by decide +kernel
def srs0_0:List Nat:=zg (fun x=>9+8*(1+(x&&&511))) [0xcaab7d41d9e0d80324a5b4b524118f9491291410a8131008f0f1f167b1298551d25a9ad45409f85bf3531873d894c1c8e96d2d69e4a5248daa45023c2de959ec4c2a61226286d6e23114e4dcf6129054acd62e46d4cca6361854bcb6ecc0605eceae084a4a46406c68664c0c6b0c65133d7f433f1068620a555b372b3c2f5e583a2e665c56382c121164dbdccf600aae2b6dad219b6a0195d74e4b4f0bd690cd8a994e8b84c4593473f50252b35898f8d874d2f2d493329b3ab3018178411d60d9b01213d9fbf54dd5c5dd6dbbcebe63fbd01e91f045f902e50ae2ecf6dde69f4b31fde80df01f413a1e1d4204acaaa8171615ad032a2facb3229d9d231e221c0908b269e7b0041819579604c4593473d5013a00f4402671464cf630252d1848453011cde2cad63adacec33a2e29d5d1c235ddca31d9c41410080402b832f0e769636d67611714eae8e118ece20a080402015e1424266e6f612902c140c00f0e8e41819a]
theorem sro0_0:zo (zr 9 st0) 8 204 srs0_0=true:=by decide +kernel
theorem scf0:zf (zr 9 st0) 230 51 (digits 8 28 0x358730899cbede88341068e46cc0bd18c9cbbc84e5e0dfd5d28f8506) 0=true:=by decide +kernel
def sa1:Array (List Nat):=zj yy [0x2045c41170045d4046808a8149454545414541040104408840440400400050,0xc4444a170285e884588448817a1111205d84468044081760112105c44170105cc0450,0x2605c58170605c494409449157250115101511455c54041440144115732112285d0,0x284d84d44cc4c8791811e4600791821dc604771801dc608091810246000918201c6040718001c610,0x155155495555181450518015105481510180050018542684258424c4250,0x1ca4701140407545d527549c517155c617181c60714c]
def st1:Array (List Nat):=zj (fun x=>6+8*(x&&&63)) [0x808821f1d1b0c1c782051c08606821714084c111043c10c042810906082418205060808101050,0xc8f023e3c0814f022c3a0880e8235312b0ce0d023634081cd02323008b8c022c2a08a0a822725230c1c9820524090,0xf9702285a0881682554d450d615025654094d502504c09393024b4c092110246440904f4ec3384009090020740090,0xfdb82056e08b1b02286c0885b026b6967656361181da8205680865982076408fd882056208858025f5d5b0c1d7822e5c090,0x1e41777573716f6d18e1d823776081dd82327408bdd023e7408b1c8229720881c823870090dc02077008c9b822e6e090,0x224022838759517a52161d6525e94858751497a4a14221828539337e061614e4b5f818585332d047e145a102832f29047c1426082813f21047814260027f08160df417b050,0x29c42a03a550a80d3e8aa034ba80a9c3a803a548a00d1e828839b9d9f0c566829704365a6030b96940e3e464c3158e0a2c1038a8c0d0,0x2de72b83b79eb00e3692d03a388b40ed642b83b592b00e5622c83b3909c0ece4a783adafb10c56b02aba9a10e9c4aa83a558aa0d5e8aa8353aa090,0x29c109045813f811f6b6521197dbdb5ddc4f86835f6e0c9d7e0db0485717e0dc615f8e843571776d321615c5f818485717e06321615c5f818e8516700a15f819c0499a6b60d0,0x9e06d0149540a8a96a83a2a5a80c5]
def sr1_0:List Nat:=zg w7 [0x23b8a007a71500ece2a01cdc54048b8dc8091408122800164544038a0403715080e28000dc54c09498138b0c29160c520c30a418314a2a52445524882a491538a22a914415228a9c111548220a9284a4550a48a3149142712a8522518a44a13815429028c52409488a14910c292204e2450a4486148114290218522094841388827010c520894811388227005453432500a80140a9504a80904622110a8003f,0x2e027070131703407034828098a81a0281a3b02762e42a4e4a24e4804e489c8d45c9445c9005c90b91a839288392003925604ac548141490014903020620402004a000488455e402af101578a8308685e4142f10a17d08304185ec20b103179882c285d2c2d9516b98b479171b90f522a21da45443c8a047a91508ed22a11ce45403d48a807691500e722a21e9c54439b8a88771408f4e2a11d9c54239b8abf,0x15ca4c5cad01cad03]
theorem sic1_0:ze (n:=14) (m:=19) neigh edges goodB true false 0 1 661 mBook sa1 (zr 8 st1) 0 sr1_0=true:=by decide +kernel
def srs1_0:List Nat:=zg (fun x=>9+8*(1+(x&&&511))) [0x18dd9ddf9d589e6002995917e4e3e359984181401ec28504c592448d4d2e92320faf8b6c0bf1ca002c200b8145b2b298e505d0292942e952f2db938b847281602caca4b095709d6db9b5b239417818e6ded612100ee806304e32452d8c8b8a894b42393631110d55530349099827192296c645c544a59c9b188886aaa981a9442bc1248582ce838e030d550cd3cdc125c9c64905e8c052e2f56403f3e5132039808190916879e1da8ab0245538691cf450fd607c78748d2c805e1e15242216741c706818b10c96726c2e1a76670638366e12134e1a4a411646031fa48f0a918d26910ca39e8a2d2c424181270446138691cf45164888e0d29047c59301c269c3494822c9a32b0b2760438368c0e0481574252020f8e2d2c90a2219181d4]
theorem sro1_0:zo (zr 8 st1) 8 129 srs1_0=true:=by decide +kernel
theorem scf1:zf (zr 8 st1) 149 122 (digits 8 23 0x6376787f6875676279800a65645f94938f8d6661060500) 0=true:=by decide +kernel
def sa2:Array (List Nat):=zj yy [0x50d10075cb40743008b030b0707070306808a824a46464642454089410,0x1b1e03060b4483d720b5e074442d780d100b5dcb454b4481d771d151d11075dc3450,0x91a113a9ec2840ea790a1a2d12275e874449d7a0d10275c86c791c111b1e070643050,0x904a81412a0104a825a9f068456a7c0a105a9f0b4492d7c1d114b5f034412d723a9ec6850,0x1f1d8274b605d2d8074b609a2d8168b601a2d8264760591d8064760974a815d2a0174a8250b20542c8050b210,0x5d09d02d53da3dc3288b60622d8088b60a12d8184b60212d827cb605f2d807cb609f1d817c7610,0x5d5c7581d597585c507149c526d45b596d81b506945a526973426b4250,0x1ee47b51cd427d45f5c7da5f607d41e517949e52754c]
def st2:Array (List Nat):=zj (fun x=>6+8*(x&&&63)) [0xa8a0226220890882201c0878702191a085c50213044410f043428209041c105040c0020300090,0xc128249453f0c5520246440909102403e08f0f823a3808dcccbc32a3608d0c82243208c0b821e2e08a48c7432c28090,0x99a02196809999022064098d756430b6209817025e5c09696025658094d3d2c3545208e9482504e08d13824c4a090,0x2df82617c0979f025b7a0959e827975710c2de0276740981d0272700969c026d69650db9b022c6c086db026a68090,0x92382218c087a3028b89870c2e282768809862027286096e1828583810c561024682090e082408008f60027f7d7b0d0,0x152702509a08d66824c9808c66029795930cee5822a9608d6502249408c64821e920a463e3432d90086e402278e090,0xc6a82a9a7a50c6ea026ba6089a98267a40882902a3a19f0dba8822da2086e8826aa0089e802669e08867829d9b990d0,0x2fcac96e8685bf2b1fba1a16fc947ee860502be0aec0af03b906dc1b5b3b10ceed0250b208d6c824cb008c6c02afadab0ceeb8235ac090,0x7482d1cfcb0f3423403cd06ce0f3413283c5c7c90c07102c36f6bb61a170dbd9ed8685c36b67b618145b082bdc20b055546e0685c1554db81a17054536e06050cc0090,0x3c7bfa43ed12f00c57c02ed10ee0d1fabb83ed0ee80d07a3a83e3e5e70c07882e1dfdb0c2f80277dcde0d7f6378373dadc0d5f6b603d3d7d50d0,0x6c1a71b0b0c1c36b0b0d942c3656b0f0dadb03ddecf60fdf5b903f7d4e60faf33d03f5c6e40fd723983d9ccf20fcf1b583f3c8d40d0,0x17d5f87604637f560d453f043ea07b41adb3c13b13702c2798b760e44e4083028c098dfd7834607341400747342251f020d0,0x107041c14f08ec19702080a5023bc10b06c82d7f7f301109]
def sr2_0:List Nat:=zg w7 [0x285a5285094a5021694a0425294b51496a38ad94915ae920b652416ba4a5a524b352493ea492d38a59a9149f522969c12cd4824fa93a8a4751c4eba489d34903ae92074d249d29135a922635224d6a4498d48135a9026352361486c388d38911a312034e24068c49071a90b4a412ea4428d4884ba900a352012ea41d2902fa920575220bea4415d4802fa90057523a1c19600700180a1948064012005228ff,0x20baf5d0606ab9369a5b8d88b4c51416a862a2d50c505aa08a8b5411416aa12d314305aa1860b5410c16a9f2d313e5a817f0b542fb96a81fc2d503ee5aa7c74c4fe0ea89f71d513e3a817f07542fb8ea81fc1d503ee3aa74b4c4ed16a85da2d50bb05aa0768b540ec16a9a2d313505aa2694b542d416a85a52d503505aa0694b54c8e989971d51323a8165c7542ca8ea81971d5032a3aa5d28c4ba52057c4a50af694a05f12940bda52942c31285881524b142a416281492c5029058a4128c482523f,0xc7bb317b9407b94cbdb98bdaa03daa65cdcc5cd501cd51f8709f913f1e0bf248bf2e03f2483f27a04f45d813b160bb248bb2603b2483b27204e45b8649b9645b9641b935026a2439af20cd78866bf34199a0b21ad79056bc42b5f5a0c215d7902ebeb]
theorem sic2_0:ze (n:=14) (m:=19) neigh edges goodB true true 0 1 23 mBook sa2 (zr 8 st2) 0 sr2_0=true:=by decide +kernel
def srs2_0:List Nat:=zg (fun x=>9+8*(1+(x&&&511))) [0x22a62869f028aa2fefad6e654fca81602965e271ef2eece8c2eb8bf0306ba4442158cf55ec00b60825b201f255e23bdc5af7a5f06454c50d3e051545fdf5adcca9f954bc48280406252e12cde5dd9d186858504dfac15551ed6a11f30ebeb45c1c2efe24f62b6108f8aead5f5a2c0c25821f2174737078ba77c1af7a240690bb3ade80e2a62829a42965e3e26f2ce901727232c0229402b3b263e0292c0920541d7bd1001c267e166e66d2cab674113d3934100e0d3e06222481821f746f78720a7771af7a25071ba61d241b494b4a5c4aa59ca4830d530e928e11c0a161e1cfafea09ef6a61508f96d5f5a220f117e0d7b0cb0847c4e4dafad0f0613a0159e941e014651879147426151072b5041562091a021b461e451d0985421aad43054645818147011ec2a11f2beb5f40c9c68a660a0d8d75ca262580a5034532d4e6a696e6d51312f05b3b2b430b216965655bcc382829ba19a8b6adb1e5b410d10ecc66646268c86154f2c40b6765686263862f2e34a97988059998bcc400e0]
theorem sro2_0:zo (zr 8 st2) 8 169 srs2_0=true:=by decide +kernel
theorem scf2:zf (zr 8 st2) 201 17 (digits 8 18 0xb0d107e7f52587b7cb7c4011884c8c5afad) 0=true:=by decide +kernel
def sa3:Array (List Nat):=zj yy [0x30d100b5cb40742c08ac18985858581858104c1048c0c08c8c4c4c4c0c50,0x180c411371031b2d12375ec7444dd7b0d10375e0b44cb4482d781d131d110b5e03450,0x9e4d81793601e4d8278b605e2d8078b609a2d8168b601a2d8201ce040738001ce091376131144dc44c50,0x65981653598515045491524145056418d060416f424f42740b4cf6cd0,0x92d24845a106550954a552914645691824515d417525d4d]
def st3:Array (List Nat):=zj (fun x=>6+8*(x&&&63)) [0xa8a0226220890882201c0878702191a085c50213044410f043010a041c20205040c101050,0x11d0cf4309460911082404208f8f023a3c08dcccbc3383608b0d821b3608d0c82263208c0b82202e08a48c7432c28090,0xc15022154094d453c32d5208a94821b52089d402245008853821e4e09352d243094c0911282414a08f92023b48090,0x19c947d886050666098c1990361057d756c31b5e08d5702265c08c5682205a09655d543385808b56021b5808d15822756090,0x1d5e5dc3157409cdc5ac36d04720c25c82456e700db409c033f6a6e0db401a83693935601a15a4e4c58068569353160181459a026568099cac9588685672b1f621a150,0x25de24839776900dedb25039578840e55da0838f93910c563828d8b870e244a30389108a0e243a1838185830c560027d0435f1f830b7c7a0d0,0x14cdd6836904cd5c6c3693509a4c026935360cbd54d0375958f819716563e065de058905c5b428b8909fe226039984920e660a4036f88960d0,0x14814e04241093e087c941833d49090db411b048]
def sr3_0:List Nat:=zg w7 [0x1e83034dc9b6d7934c4f26a05eb4d50bd09aa07ad3540f426a9e2d313d65aa27a0b544f16a05eb2d50bd05aa07acb540f416a9a2d313505aa268cb544d16a05a82d50b465aa06a0b540d196a80733100e681019cd4200b9a80067350002e6a44ca4899c516348a22690458d20889a4dd291b7a923635246e9c4dbd489b1a9036f5206c6a42d29051a9208f522146a4423d48051a9008f523a1b193005800c064a9a540c84601300183f,0x1a4b4c64bd024bd0d2426324681246935a1315a3405a3496052c64858a4958649582492f025e2b40c0b4860b49181231421324244844c284a62848c084a6084886f5e417af10bd7de832f416427af203d7881ebe5]
theorem sic3_0:ze (n:=14) (m:=19) neigh edges goodB true true 0 1 149 mBook sa3 (zr 8 st3) 0 sr3_0=true:=by decide +kernel
def srs3_0:List Nat:=zg (fun x=>9+7*(1+(x&&&511))) [0x1a2e0c07af880384b15f5e1b888388c01af5f0ce60e1274dd786e1e0e3494fa33b2a6c8c1a2cd39c26ed087d25a43dc735209b9006909be4027a2a13ee1b9f818e253e90f2202e50324045583970ef7ba545b68254995a4d3b76c500e49a9968622ed625766b78b81849a996459701453b88df5b978e80ed19356050cead2bc9bc8c0b3059e4601976a658956605a96adde9f8e8e70b9a96205d4b58e8dcbf9a905c209c81eb00a64704026812bd5101ac0114]
theorem sro3_0:zo (zr 8 st3) 7 100 srs3_0=true:=by decide +kernel
theorem scf3:zf (zr 8 st3) 120 17 (digits 7 18 0x78b1d05fa950f5f2d062a177edd786e) 0=true:=by decide +kernel
def sa4:Array (List Nat):=zj yy [0xb0a110a102e9ca80682408a4189858585818581444144840408444440450,0xc04494a71529c14a792a123a9e46844ea703a9e4286ca844a848ba7b1a111a112e9d0,0x416a0904a81412a0104a823d2a04f4a803d2a080718101c60007182605d84445817311160110605d0,0x2154845111584611180459a091a09a02a13a932896a0625a80896a0905a81416a10,0x1a2418d423528d4a251895a2608945b506d49b566981a5169845501550,9349662978]
def st4:Array (List Nat):=zj (fun x=>6+8*(x&&&63)) [0xa898228260890802222008786821c1a085c6021512084410f043410a042010506080c101050,0x1090023e4008f4ece43363c0864f02323a08b0e0235312f0ca8d0236340864d02243008c8c021e2e08b0b8227211b0d0,0xa1582195608955022254087d4821c5209453d34307500921382454e09093023f4c092d1d043074a09211824446090,0x91982336608b590263615f0c65882336008797825d5b590cad702365c0895682325a087d6022c58095d554c32b56090,0x1dc01d037337336a1815ccdcb5a860573332d6a161451c826f7209c4a48db060571291d6c1815c48c75b0585047009b411b836b05a59d9432a6808dda021968090,0x25e564439310960e4c3a503930c900e2e3e343138a0a1c10b86880c261a1037f83810c4df827d7b750c1df0249787a0ddc09e834374780d0,0xbd7c6433d73655310f54dcc619856553190e4c18992a20e8e3a703a38c9a0de64a803a1829c0e860268385769e0e7e0a3839f808c0e66766c31398090,0x150156041c17d770a867c2a19f9c0df50d25e044b51420c748c103190464b827305ccf422f53190dccf4783733d1837110]
def sr4_0:List Nat:=zg w7 [0xc52b4a08a569482d18905a40a12b4a042d6948251890b4a5121294a142d294284a52810b4a5021294a3d28c47da5288f14a511e94813ed294278a5280fb4a501e294a01c4c4038a04067150806e2a0019c54001b8a9812930271618522c18a418614830629528a4a4d2494a38a934905269275148eba491d34923a8e275d244e9a481d74903a6925d148bba491634912ee92258d240bba48163491a0c8c9802c006032d456a0241100083f,0x68b5318b7408b74344498c45a0445a45a24c5a2d01a2d23814718a1628a5618a5608a4dc09b8b50303520835216042c448109130892888923009288092219a7904d3c4269f340c9a05908d3c8069e2034f1a06050b96a5b12d18a2b5a51452b4a289690315ad2ac]
theorem sic4_0:ze (n:=14) (m:=19) neigh edges goodB true true 0 1 177 mBook sa4 (zr 8 st4) 0 sr4_0=true:=by decide +kernel
def srs4_0:List Nat:=zg (fun x=>9+7*(1+(x&&&511))) [0x849151630dee0a52d59f7b741c0e14324498b1878294c17fdedd08038f29469d0f9cfef27cf15e9a845aec834812a33c080a804ad6f2e8c382d55112f558f413a6bb38c236eb5aaa234cbd563374d7642620750a55004814a34a7d3016289951bb748e0673cb7f5560456f4911d8042ee0c3222d09cd9c70df388dc1a51c186c5b87222f773357c5a834a3130b8aad02b26b30a1330d8b7013bdc9288e01c64d4d9d10e815d1878eca9302b4673091130516b160d8b42830f689d911c04c93830d8bcd606589d5ad0d137efa23308ad86c602e7e05bd76e070c16f8195]
theorem sro4_0:zo (zr 8 st4) 7 107 srs4_0=true:=by decide +kernel
theorem scf4:zf (zr 8 st4) 128 16 (digits 7 18 0x60e171e42b5516331042657ffdf7b74) 0=true:=by decide +kernel
def sa5:Array (List Nat):=zj yy [0xc08c8c504c50cc4c08c0c4c4c0c5008440844084844840440444440450,0x3408b40742c086c0ac2c6c6c2c6c1c50184c1850089010905050501050,0x82d781d131d110b5e0344c34402d782b112b120ade06c446c442b780b100adc42c50,0x114111d1cc10441040747421132112105d04444417311140110105cc0460b44cb450,0x144dc44c500c41137b2d12375ec7444dd7b0d10375c8b3712cdc0b37103121d1cc5050,0x9e2d8178b601e2d8268b605a2d8068b608d6b8135ae00d6b8201ce040738001ce080718101c6000718244dd0,0x119806500d482510944260096f424f4246c250c2504276cf4cec4d04d0,0x4e523944e603944d503548d543180c5131847501d4875219446541990,0x965159516635981652454515b45811524145054418d0604140f5b3d90,0xa55491824539189951656d9606549851615186161818515d417525d50,0x24b462d2484b5d968441d186460d0c3438506550954c]
def st5:Array (List Nat):=zj (fun x=>6+9*(x&&&63)) [0x1282230442087c28107410c85834185c28104c108820e0418082c0c10241028182018201050,0x3526044a23044823043723044421044021043f1e043b1e04391a04371a0433046208b8116022a045226090,0x391c02039c02371b02351b023419823219822f964a61988bc1180bc1170b01168b01158a41150a411348e430ca04c089c4c090,0x9248045c48048e46045646048b44a1c30aa2820ba202422182419f4ee189d041200f811f8f811e8ec11e0ec11c4da670ce870090,0x39a98203a98237290235a90234288232a88250a7d3218554010693c12713c1269301211301255228d0d2c9408c494087a94090,0x28ac82272c821aac8225ac02242c021bac0222ab82202b8256aad52185558127554105d54126950121550129d4aa30ce8a6090,0xbf5eaec34b2f8231af821eaf82492f022eaf02472e822bae825cadd6a198d7011817011756c11696c115d6811516812cd62af0d0,0x19e5b2ab107428799c13349e49610d056693c82c21a0acd2490584361414cc09961b4d85830287d941324ea6f600185649d4d2c0030ac9379a408c01450c8098e381f06c50f0f8361828701b0414280d0,0x3b90237b81c41b7c04e20cd2dc7006df0037036d82d96bb4c36a821b01b5404d60daa006906d14ba4d8c3c15a29747b18782b45268f630e851c340267984b6c41e0acf30955883c150,0x26e09080e0e10820703045f028006fd7fbe430abf0242be1f41bcdeef50c7af209de083ddcf00c1aee7606e775ba431eb98272b8dba1b7c10e40d0,0x47e3b170e36248f06278f051b11470340c62381c6c41160cf7168c071589c3c31ac502888ca241c44610e0e1b0b8287070e43030ac3020dc22141c1c250a0d0,0x13b045b3a9e062b9d4e039bcd66218f66c124e65340d1f3099072f96c9c3958925c189e5c14ac452c0cff2896072b1049833cc9a501c864b230c6b20090,0x101885303a6bfa141bc6554a0e96f69a074b7a4c0370caa901ca5bd480e92ea9a0749744c0376b7a8c1d1dd4f60e8ee87a06fb6a5103a2b6a041cfe87410c6b3e090,0x1aa08dc19ec6aac1d5e49420eaf22a00733a85503aac72581d562d260e7306a90753895083a9c3a801d46214e0e131aa70719835383a7c4a481d3e1d220d0,0xe2a734071b04788f468e04a7d5c6a1d3e7f5790c3858ac4420b82df06560a2d5a170e8ef7758f4472b7c275d266a3d1142ad4d071d8d8507050,0x6136990f883d041434099ac21a124466b086842104f28998d441ed2421ed25ee1a557e920c0c28099206601c44603240c71348b288c5544e2556312f9420e2c33800e1381ca070d0,0x18c148a4c22998824aa5c25b98c21a821e043c53099ec429ad84a6c203e194caa1e0cb]
def sr5_0:List Nat:=zg w7 [0x9b1a9036f5206c6a4b329166712cce0589a474290e8711cd12238a240734480e289104a4220a484314908271110522218a4044148086290b4a4146a4823d48851a9108f520146a4023d4856520a2d2410da482b38851691086d22159c028b48043690d20e842c83611b00582dea8d536aa0c90028004018c8c0286213089800c085512a80908402211100083f,0x108dbc806de2036f1b060821bd0c164282f204178820bd04181b6e0d37058b8105cf16989eb2d513d05aa278b502f596a85e82d503d65aa07a0b54d16989a82d513465aa16a0b542d196a81a82d503465aa35acc46c35a88d16b511ad681361ad4268b5a84d6b401b0d6a0345ad403998807340802e6a101cd000239a800173500e262011c54401b8a8807140808e2a100dc5400238a80037152265244ce28a1a4511348228690444d26e948dbd491b1a92374e26dea7f,0x198133158b3258332621426244c4682c4822c4a80c4820c497812f15a1425a44b4682b4862b4a80b4860b49181231d8a32d82324213242448448284a628488084a60848f82c0f91d023a2103a46c08d899020192081921e043c4684486910d1208d2888d2200d2880d20e01422414a2214a2014886f5e417af10bd7de83084f5e407af103d79e833f,0x524b4c64bd024bd36c5e62c5a80c5a9392131923409234dad1991684e6b4262b4680b468b41f3141d4230c98b0da030da11834e2c1a62c1e80c1e9130d3130f4030f489c2981c3a4b02963240812486124a1]
theorem sic5_0:ze (n:=14) (m:=19) neigh edges goodB true true 0 1 197 mBook sa5 (zr 9 st5) 0 sr5_0=true:=by decide +kernel
def srs5_0:List Nat:=zg (fun x=>9+9*(1+(x&&&511))) [0xd24237bdcd7091f1cd04640b8660c6d82bf908101e909068539a082e190c415fc4305a0cdef7351b84c734141c52170c860822882bf8d2111e8fd088539a082e1982bf8860a21a147c6b351bcd2ed1e188e6823385c326d33415fc4209b4d9eec753757c9c53c11dcbf4e84c25010718cca7f40188e42411864307e81bf8ce0d128a102663299e047230864fd007f0a41a2713204c8637f0a40cff4c82936a1672913ee261a8934562430818e96fa293a440a0944e7f401c832183f3f85209249e49078063a48e061f1bc86691eae578ba7d3f420047b3c592ca7bbe5766c203a1ce6a0b960be7c10880445b0ebf1f6713d05cc00d0f180445e10160fafb3db78b80a2f16cb27c3d86c34de30021b4d26a3b1d4dd5f29dc0ee5f849e60c663159ac64aa51f09603015d0e77183178e565b358c984aa5176977439d2c0602b201e3c3790cd63f34014964d3b1dc9e3017bd4e0043a144162d280c5de2b7a1dc0c2a288c49a2d3a9400476250246eb21aae156d957bc96cad1b0c816375a0cd70a96c0d00c8f780045451189345a8e48a31de4e17128162c288c4962b26015c20e56008843f4220ce6190c208860858b05a2d6543adaebd602c14e11702fdb60e6e35562d75eb41c0bf08b0412a65285428a80215874097300dc803480096eb55983c1a0e5c01870571d950725202a61269749310088d458040091022f126bb4931c08462b924a6452a8155caa078355e0451a813c0b0401d48064421d0c030080112060d980445d0f96838162c822d]
theorem sro5_0:zo (zr 9 st5) 9 222 srs5_0=true:=by decide +kernel
theorem scf5:zf (zr 9 st5) 267 62 (digits 9 11 0x1aa126f7b9a0dc2483c20830a) 0=true:=by decide +kernel
def sa6:Array (List Nat):=zj yy [0x2c2c74207020701c6c1c4c088c080c4c8c4c00c08088808884848480850,0x340b4b44b4074347474347008b030b0707070306c0acac4ac06c2c6c50,0x87d7a1d131d111f5e8344c34407d7a2b122b121ede86c486c447b7a0b120b101edd0,0x912761211449c480112760212231123122cdc84c444c44b3702cdc40c68b44cb450,0x2609c582731210609cc08495d7c1d11575f034415d7c2b1256df06c455b7c0b1056dd0,0x8f4b813d2e00f4b82020a0408280020a080738101ce00073827b1f4706c7045ec7d0c1b0c107b1d0,0xc8272cf4cec8ca04d8181360204d82753605d4d80753609c4d81713601c4d825d2e0574b805d2e10,0x30b602d48a512948a60297496025709612140852214f4272c24ac248c250,0xf5b3d80e513948e523544d5d35b0d603540c513148c522d44b5d2d90,0x3136b4d8135249452504949262454515c45ad1604545050414905c3d90,0x4a1127441d12543150c44291093514d49]
def st6:Array (List Nat):=zj (fun x=>6+9*(x&&&63)) [0x46240842087c10e021a0430085810a84820a84820684820782820182c1810240c10141018201050,0x1288c11208c11108011088010fc7410fc7410f411c8e821b8235046630085e08b41158229120427050,0x99b82361a02351a020819823219822f964a61988bc1180bc1170b01168b010e4b01158a41150a411348e410ca04c089c4c090,0x8942a04345220228220212a2024321022521024120022220023f9ecee181cfc11f0f411e4f411d0ec11bcd2670ce46e08e06e090,0x5228025128024fa7532181d3c11f13812693811d1301259301255228d0cc49408769409249008b890087290091c8c08ac8c090,0x3cad823aad024b2d0259ac55e19c96411c564104d6411b16011ad6010356010415c11955c12b54ea10c62ac0954a60950a6090,0x43308225b08241300222b0025faf57619457c11397c112d78112178108d7811157411097412e56eb50c0eb808fab60934b6090,0x576904d167b3433034022d33822bb30265b258e198d94118194117590116990115d8c11518c131586c10d14c408a2c4084ac4090,0x384e66d070485709cc220e090ae1368441c0c1410e009be9b4b9e01c2825bc137450320db6141f06d9040a0307820281b5daad30cc6d60876d60924d408bad4091cd2090,0xebc1e4186de0ee0dd2ed7586077404e73096db43a15ce612ab68742b9cb6556d0e050a398272a2d0edc120ae545a0db82415ca8741889b828c9c8138c9e496c09057193c86d8120ae32490db0221410e2090,0x8f86438383c2616181e0c141606fd0dfe2e8206318204ab8040837f8b2041a95f9000dfe2a7e06fb7cbd437b811f4181df413dc04f80dee007a06f1050,0x12b104b8341ca2581cac3d280e472792861391051f04331e9006178f47038bc6636184e2c1456270d0e223c8a063b8a05111b448349c3a241c44690c0d0,0x515d4f40e87419d873f17508318d0829f8b2801aa679400e7e2a9d06a39d4f039ccde6a184e7011b665360c233499073197ca439589a60189660121e592e0d0,0x23b2aa6074d8c4983a6c6a481ccded4a0e9702a0074b7e4e8380c42901c3dfd480e92f88407497a428379c428c1bbe1d460e8eec84074775428377bfa881d15d8f80d0,0x111042008416411fd3eb96f838f83091068b19086f59840304048259b841c12080a0859052d9f54039ecaaa01d464d360ea3249a07219f5383a7c626c1d3e35340d0,0x2c810a0e821d39db45311ceda1d1604298e9ceda6596460a238246b9da6da1070e76d0e9925b19a6e76d250473b687459630ae97dc1e1e23ee0f0f7608ff060aff09f70a7643dfc29bd666c0d0,0x13ca5c155b00a00c240404246c38d78209010be0e9207089a245e8204123617ae3248a8160a18395821205ee0a258a860e532b0a873f0a0efb74d2447dba6930a110,0x25808901a1c155b009a0a241904dc113951424fc196c927c1a258a820c8]
def sr6_0:List Nat:=zg w7 [0x12b969256ad24ad9c55cb48ab5690572d20ad5a5122922471458922891c11624966522c8d24589a48b3389646912c4d20591a40b1348fa521eb52439ea447ad488e7a911f4e03d6a4073d48f6521ead24395a447ab488e56901ead20395a4349a32d00e847401a0c196007001800b215806c23600b06c5722b8f5b7a8190c626102310184864401200103f,0x13a69aa174d3540ed26a9c4d313949aa270d3542e526a85c34d503949aa070d354ba59897c4b512f496a25d2d02be25a857a4b502f896a05e92d47a5988fa4b511e496a13e92d427925a84f4b401f496a03c92d40411880824080d04a100e094204120006825000704a01ccc40139a8801735100e681009cd4200b9a8407340004e6a0005cd4f6149ec38bdb8917af120f6e241ebc4b0452608e2c312458324830c49060c92ae9495ad492ba71573522ad6a455d382b9a9056b52ad97f,0x4204844f8300f92c0f91d023a26c3a46c88d8f44d9304d9740d9300d919023225c3845c88b8b44b9704b9340b9700b91509115222a3212a5202a44c1a04c9804c8881111213d7901ebc40f5e7a0c21cb79065bc432df960c212b79015bc40ade560c212379011bc408de460c103279902c32dc1a6e0b270193a04d314149aa28135030626a860a4d504189aa0829354ea69bf,0x189467b4a3314a1404a14624f98a4ea024ea2d07cc5075010752492a6292e8092e8d3173e18b9898aa018aa34c4cd862662622806228c293312914029144e1c24e449c7829c9629cb809c9609c928125110a5210252461b246448c5828cb628c9808cb608caa]
theorem sic6_0:ze (n:=14) (m:=19) neigh edges goodB true true 0 1 401 mBook sa6 (zr 9 st6) 0 sr6_0=true:=by decide +kernel
def srs6_0:List Nat:=zg (fun x=>9+9*(1+(x&&&511))) [0x5f3022104609c0791661820a6a9272b190da6743dcae45e375b8b762b858f156cc2d98aa293c006157137d8cbb5b0bd72b8874520aff77c4a0f065d02812511694d524e56321b4ce87b95c6bc6f2ddc0dc7137d76b65cae188ee8941e0d055d02812510f1b4729775c4d121107a52100988410e43e4a8120414668096ec76eb89c6df632d972b87341e0cba05025c2101d1cc7e6d1c9b80a535394158ca6d93c0c2032428d70d43845210c49024401c0fa4d226833998440849c290e2108a40d469338215aa34e404066932a483a1c1107a128748044d60b35a44d20f499900a3d398fcde3b38816060d5e808808523a0888b15aabdeab3419155aa34e3e9fc03043a4fe14522894202008014a061c1cc7e6f1d9b00ac25f8401cc30232d921309338089d52b4daed4573453cf5803cd400b67835a4d06aa95a29e4fb5818f377a80169d069010a474111162b557bd5668322ab5469c7d3f8060873964fe153e9f0f69a4c89046fd4426036183f03052fb153f0f2047c09c4c253b811367a143d854760290d0a474191434887ca6100414082d347a11bd8542614be1088342a04ee432111dee78089e0e89b4c9e8082811a6d32763d3d84e8142a10f21823114540f1409134753a0a80aa55733da4d54eb453c9f7a361e6ef5003016d7083555c9f78bcddea00634c10f20a2ac04a85304c24ac02295a2d64f361400b6801c565c191605c5402ad164b00c85c2cb503128684d1b924665e2e98cc2ec311306c054500c08e92b0bcb8ea2abb51619250d09a37248ccbc5d31985d805311306c044500c0ce72ca2c2a602f98cbc48199346e4b1aa2c149608a5112031697064551615c0a2b2e0c8b02e18a351ce84301c0c8c739501c32478b4b0572e1545831040b8588f4721860074616cb4591902f1]
theorem sro6_0:zo (zr 9 st6) 9 231 srs6_0=true:=by decide +kernel
theorem scf6:zf (zr 9 st6) 280 224 (digits 9 21 0xb763b79c8bc7139a22df632ed6cb95c45e2507832e81409) 0=true:=by decide +kernel
def sa7:Array (List Nat):=zj yy [0x10610099ec08ac180b058718c9805818585818509050505010580c500c50,0x101841367b2c182c12371cb02c70607044dc71c0b0c180c10371c826741611099d0,0xcb3258b20562c8058b20919681465a0119682025a0409680025a309844984936714d9c458701850,0x5d457525d49651595166059411514549156418105441af02718270090,0x92d24845a102551954a55291464569192460914b]
def st7:Array (List Nat):=zj (fun x=>6+8*(x&&&63)) [0xa098225211d0c44902222008787021b18085c402130e140c3c4020d042c109041c1050408100050,0x1291824846084518214440909102403c08f8f021e3c08dcbc9c33a3608e0d82353608c8b82302e08b4b822a26090,0xa56025755530d2958249560845582145408895024354083d5024052087d482514f4d0c45402434e08f930247453d0d0,0x699026164098d2c5448405634b411210158c5504384856062084c598035f05756d6433a5c08e5702355c08c9682315a08b56822a58090,0x2142a0033f80820dedf5fc3197a09e5ddcc37508780dd419d837504720db5bdc43196c09a4103686a0c05a1983653b335e341594ecad78d0565332b5e2c150,0x20dd2503957c8c0e55fa3836b84920e4dba30393708e0d9dd2403916e7c0e45c1f838b8d8f0c662828987810c46202850c860c8e0a1830f86090,0x401823c0850182860838544037505e5d423d1408f5045035604f54c5033d534a0d94165580994b82655c090,0x93064e38282043]
def sr7_0:List Nat:=zg w7 [0x5e02c8719e418cf10c67e3030319c796d58b0c4b596289682c512c58815acb142b41628562c402d658a05a0b148cb1891c96512232ca24659028e4b285149650a232ca14659008e4b28111965012c6202590200cb2800496526c524f192498b2493638a78c914c59209e324134648262c9370a46de248d8c491b87136f1226c6244dc381b789036312131482638848c9008593630620e3085822c0060120050008063aa1d7f,0x2925a6325e8125e869213192340923422d098ad1a02d1a4b02963240a48d8649106490c91b0492204925e04bc5685096950569501692302462840c08488084886f1e4178f10bc7de0321]
theorem sic7_0:ze (n:=14) (m:=19) neigh edges goodB true true 0 1 525 mBook sa7 (zr 8 st7) 0 sr7_0=true:=by decide +kernel
def srs7_0:List Nat:=zg (fun x=>9+7*(1+(x&&&511))) [0x479b6ef56ab3230ab37dfc3e3c35630116b84e3cd991ae8ab37dfc3b5c35638a02c0410a29c6ea20a68ceecddbd20303edd602a69ea2e9c97619319b6eb05ae30ab4664a051ba071816957291946866d60c4c69ebb74e5f09c79013a424a0149900c14b0267ca9804f039f3ae903e398c4024d1c78f5cba3c25f2d58af1a0069e5c8151c580536b902d3ea00a58a1721019b16f8b0e071081858a171f8582f710410de032c04c91170c010409c18455b3568e0b8253]
theorem sro7_0:zo (zr 8 st7) 7 96 srs7_0=true:=by decide +kernel
theorem scf7:zf (zr 8 st7) 115 84 (digits 7 11 0x14a7dca71396f8a18281) 0=true:=by decide +kernel
def sa8:Array (List Nat):=zj yy [0x20344740b42808a81409494494054145454145410401074004400400050,0x5157015110510455c01468b460b4489d7a1d11275e0746834409d720b5c42d700b5d0,0x8095810256000958d251025126d5f45445b57d05106d5c95d71575f034415d72455c45450,0x14006ad09d509d02d53da3280b60602d8080b609d2d8174b601d2d8268b605a2d8068b610,0x5c5d7195c607181c51554155255554605141461054015205740610190,0x1ca4701140417541d527549c517188]
def st8:Array (List Nat):=zj (fun x=>6+8*(x&&&63)) [0x948c8431b2408748821e2008746821916085440213043c4020d042c10804181040408101050,0x1191022844090cfce4311420900f823c3e08e8e02363808c4b49c3343008c8c021b3008b8b022a2c08a09821e26090,0x7d8025f5d5b0c45782415c08ed682365a09554534358540959502525008f14024e4c08d93024b49450cd12822e48090,0x1cc1716f6d0cd1c022e6e091db026b69670cd1a82336a086da822e6808ada022866087d9826563610c6d9021d62090,0x216261c3178409fc1057e820c0dfa0037d007e0decd4bdc86857b3529721a15ecbca5c8705187a09dde82795953741015e5653dd040579534f0e7415d9e027514760d0,0x26c4a8835798a20c468829d529e0e6c32783a1409e0cf6627830f9e0a753a5839b0a960cde5a6039195930c5e4028d042632383078c8a0d0,0x26c18f9aae0ebe52a03af92a60e0e72b0381a0ac0e65f2b03ad88a80eb61a9838b7caa0eae22503ab86920e96a69c317a40a8e7e5c39d58a20d0,0x1ec1316b2e0eb45c21a7b0869eca0327672e0c69ed10376ac0a6275e441d2586989d1079749e1a86604439185a5ad121696b6504291a6d7b10741a143a39840150]
def sr8_0:List Nat:=zg w7 [0x405a62828b5430516a820c2d53a5a62768b544ec16a89d2d40bb45aa1760b540ed16a81d82d5345a6268b502d16a01a82d5012a6202550200caa800195500012aa6d4a4deaa49b0548b7aa916c1520deaa41b054aba5256b522ad6a415cd482b5a9454a48a9c511548a20a90445520882a49d29135a922635244e9c49ad48931a9026b5204c6a42d2905a710b4e0146a47434305212805422a00502a5412ba1510a8003f,0x15ca4c5cad01cad1ae02617013838098b81a0381a41404c540d0140d1d813b1721d272552724027244e47a2e4aa2e4a22e4802e485c8f41c9541c9001c92b02562a40a0a4800a48181031020d00241002500024435af20ad78856beb4195a0b21d57906abc4355faa0c0d5726d370]
theorem sic8_0:ze (n:=14) (m:=19) neigh edges goodB true true 0 1 533 mBook sa8 (zr 8 st8) 0 sr8_0=true:=by decide +kernel
def srs8_0:List Nat:=zg (fun x=>9+7*(1+(x&&&511))) [0x93a2ed08c7fcdca7ce2fda83083a2ed89b302e2a73ba00d0218f23cfbe2fd102093a2ee4b49f4d08bf6a0a2ae8bb626e00bc8f9e76034c922434f82f61edde009ebab5e997325419a0808052184ca2143461ebd5520848a21444b72cd85208b277099aaad52e59c2ead38681b3f1e4d99aa6ea342573df482039a0340467e3cbb736ea34256fa534203019c1ef1ec791c5fbe030c643d88e60345af0418c276d1baa05bf6eb080c1708191]
theorem sro8_0:zo (zr 8 st8) 7 111 srs8_0=true:=by decide +kernel
theorem scf8:zf (zr 8 st8) 128 125 (digits 7 5 2937168639) 0=true:=by decide +kernel
def sa9:Array (List Nat):=zj yy [0x1d5c4147008b0140894145454144c8c4c4c4c0c54084c0844088404410,0x18173011c21162112485f044584445217c01160110485c8757315111d5c4544c1450,0x202560409580025608091810246000918201c6040718001c614844c844981751111605cc44540450,0x525349812512d40b522d54a60294ca6c1095109c13513246460519180464610,0x7a51e5449501f517d49f527945e55798de6079413514d49352494f]
def st9:Array (List Nat):=zj (fun x=>6+8*(x&&&63)) [0x54a0226240888902201e08707821b18085c50213044410f043410b042010604140820102090,0x12514fc34c4809292020348091910242440900f823c3e08dcc4ac33a3608e0d82343008c8c022e2a08b0a8229251f0d0,0x8d702205a08756825957550c0d602475609055023c54094d453c34c52092d48203520919402435009013823d4e090,0x1ad3505980856b474100661459a82056a09a4106836705958d8433a6408e5902346208cd8822e6008b58025f5d5b0c55782265c090,0x20e161c319820a05fdec37d0e800df431f837d0a7a0dd5e5dc3197409c410970720c1dc1b836d3b35680215b4ecbda00856d352f00681469b026b4d476602150,0x276125039d86960dce326839b78940e6dda5836f7c980e65e21039976860e4e565c319920a463e24315900a344a383278a8e0e344220321888a0d0,0x76046816d68600db5a19036b05ad182464c09da4e10544295f200e463427d04d4c46830305254d1838b7c9c0cf]
def sr9_0:List Nat:=zg w7 [0x828bd4418a20b0c174a8b51913123922a245a45428e48a8516915023922a045a45404a988095408072aa1006554001caa800195501226202450202c8a8005915000722a01c4c402b8a8803715100e281015c54201b8a80057150006e2a604a4c28a498314930271614522c18a418514830629484a4960a4926148a58291498520960a4126148ea521d4e239aa44715480e6a901c55383518a8014046013001814aa6550120887f,0x137a5317a7407a742bca98bcba03cba0d254c525d0125d1f813f17a04f46a2f4862f4aa0f4860f493812714a1324a5314a5304a45c08b8950281521815221c179060bc4305f820c215179028be2]
theorem sic9_0:ze (n:=14) (m:=19) neigh edges goodB true true 0 1 645 mBook sa9 (zr 8 st9) 0 sr9_0=true:=by decide +kernel
def srs9_0:List Nat:=zg (fun x=>9+7*(1+(x&&&511))) [0x4fad384d814f6d45dbab247059c1c4db3573af63b790756305142d0a19100d19e22e09284a2432ae1be22e08349cfa132f931e01034bac4881a7539f4265fe8466f13a4a0b4c7b08085b220c0752ab4305faf6eee5cd1aa311f923835a161ac882e18bc0b4e8880f5409325ca0c1424d0316251213b02020e22e09447d39940a542c55855a438681a6139f466d0014e]
theorem sro9_0:zo (zr 8 st9) 7 97 srs9_0=true:=by decide +kernel
theorem scf9:zf (zr 8 st9) 111 45 (digits 7 37 0xb644180ea556860bd5ee4fbb672e6935188fad3a40914f6d468bbb6eac91c182) 0=true:=by decide +kernel
def sa10:Array (List Nat):=zj yy [0x30b0707070306c0acac4ac06c2c6c6c2c701c6c1c4c088c04088404410,0x605f0ac495b7c1b1156de86c702c415b7a2b112b121edc46c447b7a0b110b101edd0,0x574b805d2e08091810246000918201c6040718001c614844c8449817511131111605d4044c0450,0x2d1604545050414905c3d80f5b3d84e503948e51b093109b1331325d2e10,0x4a1127441d093514d713604d452504949252454515c458d]
def st10:Array (List Nat):=zj (fun x=>6+8*(x&&&63)) [0x908022220087c11d046c11914086450217044c50211043c10c04281090608140820102090,0x119102423e0900f823b37310cf0e822c3a0854e82383608d0d8232300890c02223008ac9c8432e2a08b0a822826090,0x13d6824c5a080d68249580919602435609015825553510c0d502475209054024b453f0d392824c4a080d2824844090,0x19d1d040188508660994106036305857d7432f6008b1802156008e1782355e08a1782135e08c9702255c08897025b59570d0,0x1fc42083337c800dfc39f03777b790c1dd82730435c9d030b72700dadbdb43076a09a4b4a590505692d23641415a4a48d904850468099d351d88085674d416202150,0x25dba283976c880dc5fa503956e7a0e55b1e0393918d0e3c7a4838f1c900e3c6a303878b890c1e18285837d0cf6021037f16840c561023980820d0,0x201f57c8c4807d23241201f4c454497990a5e662837f064e3c203052d6d1836702099c095c36700574c12063a603997a8a0e65e2203758e960d0,0x60063c1315d150e01f42807d5f0c5]
def sr10_0:List Nat:=zg w7 [0x620c0b17398b574b312f496a25c52d44ba5a057c4b50af496a15c52d42ba5a017c4b502f496a05c52d404898805915100722a202450202c8a8403915000b22a000e45403898807140806e2a000dc54c094985149306292604e2c28a458314830a29060c52ad9495cb492a369256ce2ae5a455ab482b969056ad20a8da47b290f56921c6d2238da407ab480e3692c00e00300164b195806c23600b063d6dea630120887f,0x1894662942809428c49f3149d4049d45a0f98a0ea020ea270e1272e0a72e02724a0494518309196c919123160a32d8a3260232d82324204844f8300f92c0f91d023a24236f201b7880dbc6c184262f203178818be5]
theorem sic10_0:ze (n:=14) (m:=19) neigh edges goodB true true 0 1 657 mBook sa10 (zr 8 st10) 0 sr10_0=true:=by decide +kernel
def srs10_0:List Nat:=zg (fun x=>9+7*(1+(x&&&511))) [0x7108915ec224240ba72e341306e91b6404d8e3b7064b81619c7a6c4d3a35281784ddb35680786828128a4de9212e9ced7708a0e62077e820108825cb87709901dda1e8288118711e890f0b6812a3f4130698a872899a0058f32f61ad565c604faee691af503d12ae04a647971813ebb9a45fc5ab44a076c1f4a7cd10182d40358ae305da0220609149d4aa13675a9d0ac061e609159f5405447cf407ea94e500f120297a4607559f8107200788c167503f58ad82e44f120251]
theorem sro10_0:zo (zr 8 st10) 7 100 srs10_0=true:=by decide +kernel
theorem scf10:zf (zr 8 st10) 117 26 (digits 7 24 0x8a71e9714d9af276ccb4ee38f642c0064f4e7a2504) 0=true:=by decide +kernel
def sa11:Array (List Nat):=zj yy [0x99cb4340b4b47474743474245c245c9c5c5c5c1c58089805804088410,0x62d12475f0745874451d71d0c0d160d10475cc9844984826711611099cc18441850,0x102da000b682025a0409680025a09367416114d9d0184136724b5c52d771d104b5dc3470b450,0x825cd096d0946091609d63643613dc327cb605f2d807cb6091b68146da011b68202da10,0x75019446521974560155c560114445211483510d5c3600d402510950,0x1890614105087511d747671d87]
def st11:Array (List Nat):=zj (fun x=>6+8*(x&&&63)) [0x1ca0226240888782201e086c70219045c1150448110043c10d042c1090608141820300090,0xe9202464808c9102424408f4dcbc3403c08f8f021d3c08e8d82383608d4d82322e08c0b8229251f0cb0a022a28090,0x817025b59570c1d6822758093958221560955453432a54081d5025250089940205500939302204c092d251431d4a090,0xd5a8233680909a023068099d958c32a66081d98253640881882615f5d0cb58022a60081d802265e093d702235c090,0x25e02772b27700615dcac85c018577272170041409d8275081a0dcc17105bc16d6b690d05b023e6c0875b023b6a0919a82386a090,0x46524838d8f910c063028b89850e1c3a283870c880e1c2a1037f81830c05f827d3b336e34146df027b3f39741c15ecfcc5d07057b393174341421e8279534f7204150,0x2ae02683ab829c0e4e1aa03a9808e0ea60a403a7a59f0e8c629831da60a8c5a90347a0a40e8c52783439ea00e666e74301980a5411394960d0,0x22e1c23d6d740cc5d0d833d6d300ddc1775409dc9827721280c957c803775008241795b500e5e8ab03ad8e9a0eb642703a186aa0d0,0x21c11c0471b021c6a0870d82a305f5b52e9e80d86ada9ab0eb6a6ae404a7a308a]
def sr11_0:List Nat:=zg w7 [0x3f85aa07dcb540fb16a91b6312236ca246d9028a5b28111b65016c6200ed94400db2880b6408036ca0012d94001db28001b65012c6202590200cb2800496500032ca4d8a498b2493638a68c914c59229b1c134648262c94b4a4969c52cd48a4fa904b352093ea51d29239a9245b5248e9c51cd48a2da91474e08e6a4116d484c5208d92410b2482638842c9008d92010b243485a01d0068366af352700b801c0c316088ff,0x3462cc4625006252e30e6230a8030a97107311054010541e1d21e443c7a23c8e23cba03c8e03c86810d1160d016470164240848870b9072b8872b80720a041444335f9a0b216d79036bc41b5eda0c10467a302c8459e402cf101678b030359d6c8d961696e35f2d313f85aa27d8b544f96a05fc2d50bee5aa17d8b542f96a35]
theorem sic11_0:ze (n:=14) (m:=19) neigh edges goodB true true 0 1 2565 mBook sa11 (zr 8 st11) 0 sr11_0=true:=by decide +kernel
def srs11_0:List Nat:=zg (fun x=>9+8*(1+(x&&&511))) [0x7f055b0129bf1e25232885c343ba8c8294c6d2869442e151511d44c143226a8a494a2170a807eea360b443c54524a42510b171615754606400534809999078f485187509585c551da818b0c6d8e4bcc4baae009702f6dc0c63586257004b6b717b6f04b3b28484350116964100d7008807e8c7c2836faa2f8eaa40a5116157552020ba30d9e09a101404b930a888b0a5e9e5d920b416f2504e909c04343336300d127877320e484d058807a42680c44d848bc30d40a7472766e70984c4a48909c0a2c362e312a23222974332d274f023207172816131292249581d6]
theorem sro11_0:zo (zr 8 st11) 8 116 srs11_0=true:=by decide +kernel
theorem scf11:zf (zr 8 st11) 138 28 (digits 8 32 0x64216a1f664241463e141b8355704a827e6d6843201873605f89888475610706) 0=true:=by decide +kernel
def sa12:Array (List Nat):=zj yy [0xb01808980581408941494545454144c088c0c8c4c4c4c0c48088810,0x8b675161216112d9c4584818441840b67204dd44c4413741315031004dd00c70090,0xc4858085408418273021426124d9f058505845367c061406104d9d4984898449850,0x2025a0409680025a0c9848086831611021a0c184008682020a0408280020a09827612151211609d0,0x623246da051b68046da0919681465a0119682065a0419680065a080b68102da000b68202ce040b38002ce10,0x4944b502d48b522944a55298ca6029718255824d824982718d8cd94d0,0x1e5449501f517d49f527945e557981e514d413524d4925149552634990,500993]
def st12:Array (List Nat):=zj (fun x=>6+8*(x&&&63)) [0xb0a82282a0898902222408847821d1a08646821714084c111043c10d0a0824107041410300090,0xd93024a460921182324608fce4c43443e0908f82403e086cf823c3808e8e02363808d0c02323008bcac9430b2e090,0x175a025a680959a026761590c05982646009898025e6009716025a580959602534d470d51482405209413024e4c090,0x101d821b7608f1c824e7209d1c823b7208d9c82486e09c1b82356e08c9b826d6b690c05b02656a0989a825e6a090,0x1fdf5ec3787e0909f82417e086df82747c08e9f02377c09c1e82347a08cde8277736f0d11d82547609e1d824376090,0xd23028b89870d56282408a093e2023a8808da202498608d218232860a160e0430b8408b20822982089a0022380090,0x102702509a093e682369a092a602499808ca6029795930d06582509408de5024a9208ce482918f8d0d164023a8e090,0x2ad14f68068516aa0aa5e5d688685a97971a21a16a5d5c6886050ca80a9d0cee78685a743359e1a169cecd67860502a60a9470803a3068419f06766e643559c090,0x304231830bc608b70b103c106c40c9efb083c104be0ee6f6ec31fb80aded6bc301b6098ecad035fb0b40d6ebac8357aeb00eb5452c6290520ac090,0x2cf43783dfbcd80f7eeb683b1c0dc0f76f3303ddbaca0f5f676c31fd60b574f3c3d112d40c57502d110d20f443b383c9cdcb0c7f202c7c5bf0d0,0x15edd7ec04676d560f1f0425b63b7b2119db5883676d5a0c9cb71f0842f852c0cbe14983d5d1092d448031b04fddcc83c3d0e00f8733603e1cada0d0,0xdd0774d02dd7c0b74f82a7069ce82a73e0b441c104c813199760f5f877f26e7746e1dfc9b9ddd818d]
def sr12_0:List Nat:=zg w7 [0x1010c81016194202432840386508050ca1006194002432800386500050ca00061940411880824080d04a1016094201c128006825000b04a000e094c11498238b0c491614922c192418624830a49060c929b14934649262c914f19229a324531648278c904d192098b24b62916ac922c992458b248b63896ac912c992258b240b2648162c904ca4099c415348828690054d200a1a7060c4160a8c9402a005018c8c026003010ff,0x109b3c80d9e206cf360610933c8099e204cf26060633ad8db2cad8626a36c62452d94488db2851cb650a296ca1446d9408e5b28114b6502236ca4658c488cb2851c9650a232ca0472594088cb281963102b2ca104a5940094b280b6310096ca2006d942025b28402b6508036ca0012d940015b28001b6501666202cd0202d9a8404b35000b66a0012cd404b1880396510052ca2006594404b2040396508052ca1006594001cb2800296500032ca0218c402c32880486510070ca200a194400c32bf,0x57a5317a7407a742bca98bcba03cba0d254c525d0125d1f813f17a1527a44f46a2f4aa0f493812714a1324a44944a294a62948a094a60948b811712a04544a254862548a0548605484319f8c0c21567ab0325]
theorem sic12_0:ze (n:=14) (m:=19) neigh edges goodB true true 0 1 2817 mBook sa12 (zr 8 st12) 0 sr12_0=true:=by decide +kernel
def srs12_0:List Nat:=zg (fun x=>9+8*(1+(x&&&511))) [0x9891880ba2a5a921a8a7248e54101d6b0458717a5e6d7d5a3c3b3a9f44acabaa6f5c3f2286332b4e4c004f364576babbb5b3a474b8b11ad14c48c45485d453d2c72a080f37021238bd10353e2d9c1bcfaf225655d537ae1f911d431995a7260a80278dbb5cdd2ba309dc5ad23a588dac6a6624622a29c2e39504295ac1199c5e9a1c1f59d0904fd127cdab2aea84e18ccac6c01b0e451d98ee52922e2d6ce91d2886331231017454b523d514e491ca8204608baf4bcf6ae6e6c893eb2723f595754cc94910c6656d09e0080ce98ecc68a123231716b6748e96236481b4f134d77794509b7b672b3a414072689a78da2db248ad9d2393c02d3de531146462ce91c924134c0f2c02ad038f01139a16181457ce58d14c48c454cf85d6d453d65755d552c72a0843199590820053123d3b4a91bdbc042eb223afbf2f3427b13fb02d32a430b3a61e9d9d1c8d0c8c2251d904b4ab1a8e0939d23a39179389cd0b0c0a2be72c68aa67eb6a29eb2baaeaa39504218ccae6246201002982de9da5695f1dc21911d19f9a13dfd9521b8585451c46dc0659d30250d090500fe91d1cdc8bc8713253b413361360689929ea19a02414243808a8d0b0b494c80b19140403200485838701139a16189497814a8d0b0b898c80b1b1720020c5511530f5002872a88a886a9016524c18165c090214130148ea0513441b3914484f45a34b3e1736060aa20d9a891d015a]
theorem sro12_0:zo (zr 8 st12) 8 163 srs12_0=true:=by decide +kernel
theorem scf12:zf (zr 8 st12) 189 47 (digits 8 16 0x27342c3028afae86332b009c76bcb8b4) 0=true:=by decide +kernel
def sa13:Array (List Nat):=zj yy [0x1d5f40b4b45474754cb4074347474347430603060a06060602048088810,0x22f5ec7444bd7b0d150d102f5c8944494487572502151115111d5c540814441450,0x9e4d81793601e4d82025604095800256090571415c10572375c4dd781d10375e0346cb454b450,0xb582d80a512948a522544958258095021448522157424942540948d0,0xc543110a4423544d5d35a0d603540c513148c5d2d8c]
def st13:Array (List Nat):=zj (fun x=>6+8*(x&&&63)) [0x94982221e08807821d1408745021b045c486031314084410f043010a0424107041410300090,0x121282384609111823f3b350d08f82403e08f0e82183a08e0d02363408bc9c7c3322e08c0b822d2e08a89822826090,0xc9602315808b56022a5608a5582255608895022154094d453c3325208b54822a5008893824d4b470c553023c4a090,0x194ac8d809050264098d90217621c0d8415f5d5b0d0d782405e08557823d5c0921702185c08e5682445a08d96825957550d0,0x35fa0030b7e7c0ddde5ec3017609d5cdbc37108740dc419c8371046e0da5adb430168099d0464585056741371614159c64dc5848562660994ccad80b05653323602c150,0x22dc2503956a840e55b21837d70920e4da9e03936c7a0e463e2438d1a900c564028d108e0d262a3838d0e880d16222838385870c060827f050,0xed74d838d06565db0319123b1411c41918d0994165580994882652b2e0d9550265232e0d95482818c960e5de2103977a860d0,0x168195045011418084]
def sr13_0:List Nat:=zg w7 [0x4a0c250586abb149af26989eb4d513ca9aa2793502f5a6a85e84d50bca9aa07ad3540f426a81e54d5012a6200a554400caa88095408052aa1006554204aa000295500032aa414a4812a490538a04a90409526e948dd389b7a913635206dea40d8d497a522ef5245aea44bbd4896ba902ef5205aea475290e4a921c55243a9c4725488e2a911d4e0392a4071548693465a015d10e847401a0dcac654a0030008010ff,0x1a62e6262a8062a9831331311403114c14998948a0148a1b0e91b22363d136481365d0364803646408c897068172401722a0454498608996049960099110222242baf205d7882ebd7418424af202578812be4]
theorem sic13_0:ze (n:=14) (m:=19) neigh edges goodB true true 0 1 4625 mBook sa13 (zr 8 st13) 0 sr13_0=true:=by decide +kernel
def srs13_0:List Nat:=zg (fun x=>9+7*(1+(x&&&511))) [0x1551593d4efd742cd972e3acf8366d2b77a3d1991b680b989f4f9dbb4d00a135e00ab1710e2b684f0cbd19b3808d2e81c5dd1c706a24213bde8868634b3071b74718967205d42ac00a94da332d00b8fa75dd7a6804c20e2c6a1c584f1e8bd270132a4c806080cb0356a81c359022c54c3467caedf81f3af5aee00117ad60ac815cc913e3528c73b820e2849dc101911e5720d52a1dbf041424ee000c9b02ab08a91d060264aed70311]
theorem sro13_0:zo (zr 8 st13) 7 99 srs13_0=true:=by decide +kernel
theorem scf13:zf (zr 8 st13) 116 29 (digits 7 16 0xa68aca0aad9ababf5dba1e7cb8eb) 0=true:=by decide +kernel
def sa14:Array (List Nat):=zj yy [0x28a86868682854d45494545454144cc0c088c0c48c8c4c4c4c0c54084c0850,0x74347474344f0300b048b02c0ac48ec2cac4ac06c2c6c6c2c68e850,0xc74447d730d101f5cc7b7a2b121edcc6c447b730b101edf44b408f434b44b410,0xa0d180d10275cc9b7226de86c606c449b7a0b180b1026dcc7d7a2d132d121f5e87450,0x1375ec3440dd732cdc8b37513112cdc44c540c40b3710313275e0b4489d781d11275d0,0x3074455d7c0d10575cd3b7c2b182b124edf06c453b7c0b104edccdd7b2d12375ec7450,0x346c45ab706adcd8b732b1262dc58b7d0b1062dcd7d725f5c57d705f5cd5d7c2d12575d0,0x259ae0566b8059ae0cd6b8235ae04d6b8035ae0c0738201ce040738001ce34ec60ec4dab7d2b126add0,0x9e6b8179ae01e6b8374b609d2d8174b601d2d83713609c4d81713601c4d835d2e0974b815d2e0174b8359ae10,0xa12d8184b60212d8381360a04d8181360204d8380b60a02d8180b60202d837cb609f2d817cb601f2d8379ae10,0x3b193b09cb3d33b33db3dc3388b60a22d8188b60222d83852e0a14b81852e0214b8384b610,0xb532d48b552980a5329b34673426f466f424f464f4276c676c272c672c250,0x9551556956055414514d413534d493534949251495526349812512d50,0x595d65a9960654d960614d75a5d897515d7576b5d8d7605d416535550,0x16a47a51e5449505f507d4df527d4de527945e557981e53654995b6590,6631598338]
def st14:Array (List Nat):=zj (fun x=>6+9*(x&&&63)) [0x42087c10e821b0432085c10a8213041610081e1008160f060609040e08141010200050,0x8244088608fc8010f411d82351c04371c04351b8c83178b02188b02178c45018a45810ac1138a02128223050,0x1b0d411a4c65d2c88453404663104643104602e045e2e045a2c04572993c9620b4ac1150a411409c113094112488111c8811248e400d0,0x22a2023321024321023221023020024120022f20023f1e823e1e822d1e823c9dce26b105a7808527608e87008e47008dc6a090,0x53a8d3e9b108aa60948a2090ca209409e09049e09389a08f89a09329749a34408a60206a5824a248248248247230245230244a15027b110,0x22b10261300233300220b0025f2f02302f025d2e023f2e025bac55aa9105ab60968b00964b0095cac08e4ac0954a808d8a8090,0x6f37023937026836823636822636826cb55a6cf105ad809acd408a0d209a0ce099acb64b1c422b3023332825032025d318262b057ab9110,0xe6f408daf209e2ef76bac408bc0206bb824a3b0248bb02473a8245ba8272b85badb11d0e409cce4085ae409c4e00964e009ace0090,0x530608eb0408e50408df0208d9020a02ff7ebec416c0025a3f8259bf82573f0239bf02553e8236be827cbddeaf3105af80852f6090,0xc11409071408bd1408fd1208fb1208b5120a230f86c2c422c40233c38232438230c3022f43023fc2822d428284c1e0b03105b08090,0x177220a431f8ec6c474480273c80216c80271478259c7826f470239c70268468236c6828cc5e2b13108b1808cd16090f1608c916090,0xcf36088336097d3408c33409753208ff320a632f96cac422cc02334b82304b025dca823f4a8294c9e4b23108b28088326097f24090,0x5b48096946095d4408d9420a833f9ecec422d002524f8243cf82504f0241cf021fcf024e4e823ece829ccde6b33108b38098536090,0x1d5c08635c0ab62e1a0759051203ab8285c1d6c60360eb20e230757070c03aa835306a34fa6d2c422d4023353823053023ed282a4d1e8b43110,0x9166085f66088d640863640ac7615aabeb4281ac7615aaaeb4281ac76157aac4d5a186962085f62086d600863600abf5d6b946ac281abf5d6b936ac281abf5d28936ac2618155e085f5e090,0x5d6e08936e08616c0ad7693297eb0401ad7693296eb0401ad7692f96eb03e18156a08936a081d68088f680acf6574b8ea82c1acf6574b7ea82c1acf6571b7ea8281acf6574b46a82c1acf6571b46a8281acf656fb444d54190,0x17dbde06fe20e6f810cef415dc101ddaf01806ed740ee77161afea4401ae77161aeea4401ae7715faeea43e186972089372086d70088f700adf6d52a86a8401adf6d52a76a8401adf6d50a76a83e190,0x33620d0079b0f6783cd873381e6c35980f2e0e471f95c98839c80433c7058dc5e27062047181614118a0c1b8a092b86c4078503620347e0b0c1e1409820d0,0x16f71b60f6e5adc07b50767afd6e94416ec82d48ab5c195761ae0f4ed6d706dfd56b03d4893581e9ca1ac0da3a4d507a9116903d3933481e8c1d0e7f3b99110,0x1c90a7283e484b8c1f1787bfdc8845e205bd21708333eeb8419976dc20f6e64e107bd1e6f8350f037c198775be0cbfb6df07b72f6f831fef82de8eb7019ff71ba0d0,0x3bf96d10787e47703eee53ac1f7725d40ef3c8ed07dbc07583eddfba81dd709d80fb380ca07d9bf6483e9f47afd51073d20867d00b9fcde5f1c4e48639c1f242dcc0d0,0x19b0461011458d6ead1b0e3080adec6287e8d87b1d86b4285bab5fc38a2c75a7ec06c2af1ee7715db1572401b67a90b8bbd0b57bcf107c1d47883d3edbc41edf4de20fc7a2da07bbcd7803f0e5b681ec735de0d0,0x596cee16e89658fd9e3ada14820f241a0902daa7b78aa7b6902df3e154e40b6dbe782b1673292089399bca64ebc1602fb8dd9eca2b75c367b2b7c58dd9ecae31202fb8dd9eca731acb6770b8c41482793bc260e72150,0x1017dd8ec2b7ad3f47a4d8ec35a7d0b63ad58693477d0d8d78a670c0d16e2c59cdcc462ae67333610ac59cdc6e6bb14615f269441c2f4fa391c7df6f7d9ee91d9bedef238feef5874ca5de2ef4a0a4832da4be0a14615f26b5c1c2e370a159eca159ecae10d0,0x235afa7d1c8e3efb7b2b8babad972ece631944c458bc5dc99562b8babad972eab660ad3922e055774ed9d56cf5e4d24af5faed5b4fae191351a7a14c0291a336b449941c369dc2e5d56cf5e4c1c8c65b596c1c28b89b5d28828598c678b1144caf6c3a24f71989980598cae23c58ca276db921127b8cc4cbc2cc65711db717730b1e23b6dcf161667185d4980d856e34190,0x1b7076fbe08880dbc8a1577662f0caed972ecebb5fe9def238fbef44d248b4cc5131988f1772a95db2e5d9d76bfd3bde471f7de89a78a48b4ee74e96dcd248b482b84315db2e5d56cebb5fd383890757ebba76ceab67af2693015bd8c6c20c41235afa7d1c8e3efb7b2b8babad972ecd8b3188f163289dcaa8942c662e6014e]
def sr14_0:List Nat:=zg w7 [0x44d6a4898d49127a9126b5224c6a4493d48135a9026352049ea49b299367226ce24d5a4498b48135690262d23e94c7d390f5a921cf5223d6a4473d480e7a91eca63d9c87ab488e76901ced23a40d268cb425a01d08e803403840c260c6c8164b19584ac03611b00580e805401a00500d404a015002804c80643191804c006052a9957f,0xe66301cd04039a04057350802e6a0015cd4000b9a9ab29b5b6936a2d26d59c9adb4935169268ed22d6da45a8b4835b6906a2d20d1da58b29b167260ed22c1da418db4afa535f4e4bd6a457bd482f9a9574a6ae9c95cd492b5a92574e2ae6a455ad482b9a9056b529d94d3b392796924e2d229e5a4538b482796904e2d26e94cdd391b7a923635226dea44d8d481b7a90363525994cb339166712d4d22589a40b534816269274a64e9ff,0x379ad04f6b5a89e86b50bdad6a17a1ad40f6b5a81e86b53a5a6374b504ed16a89d82d513a65aa1768b542ec16a85d32d503b45aa0760b540e996a9c4d31b89a827293544e1a6a85ca4d50b869aa07293540e1a6a974b31ae96825d2d02bd25a85784b502f496a05e12d4b3598d66b412d8d6a25a1ad42b635a85686b502d8d6a05a1ad46b598cd6b411ad681361ad406c35aae]
theorem sic14_0:ze (n:=14) (m:=19) neigh edges goodB true true 0 2 213 mBook sa14 (zr 9 st14) 0 sr14_0=true:=by decide +kernel
def sr14_1:List Nat:=zg w7 [0x4196f10cb7e58b32c57960ccb05909dbc80ede2076f3b161d8acec18760b1cb70e9b86cdc196e0d37059b936da5b8d88b4c7116a0a2a2d50c545aa08a0b550a598e14b4143896a18712d410c25aa12d31c25a8286cb5450c16a861b2d50c305aa184b5010d96a82182d5409a638135050626a8a0a4d51409a8183135430526a820c4d504149aa80b4c7016a0a0a2d50c145aa0830b5410516a9f2d31be5a827cb502fe16a81fc2d53cd6637b5ad46f435abf,0x512f2992f268af2d8af298af2682f2d82f2982f25a0ac346acb44acb42acb40ac94827034e249c5281a519925224a2514a5314a4504a5304a45c0cb891712a0502a4302a4439af20cd78866bf34599a2bcd066682c86f5e417af10bd7de8b2f4577a0c213d7901ebc40f5e7a2c3d159e830f41665b6f31db790edbcc36de41b6f10db7ed8b36c57b60cdb0590e5bff,0xd62f3db1798d8bce6c5e60c5a9a62b306294d2d5982d4a15e94c5e9d01e9d0af2a62f2e80f2e83495314974049747e06fc49f8bd0a9bd2a93d2a8bd2a83d26606cc7a4cc944cc864cca64ccba2cc962cc942cc862cca62cc8598f4199281990c1994c1993105e06bc764bcae]
theorem sic14_1:ze (n:=14) (m:=19) neigh edges goodB true true 0 2 213 mBook sa14 (zr 9 st14) 172 sr14_1=true:=by decide +kernel
def srs14_0:List Nat:=zg (fun x=>9+9*(1+(x&&&511))) [0x174e85228a93f1f7517cb72716dafcb6362c07b92587091627298c6c58725250519a586a9299cd178b9e4a480929576bd92b0a140ad97b816f94ebbd22e5163e1180f8e975530d835a2707130c8d0e310d0c55e0958bdcf182b851a60be3fa24661c2082be0441a77d4b012b67a24e6692b09ae21d0ad46a70a72b782cecb6db2c35f96c86370c003e894b49c24e7a999aa572152502587951c7d7e5b1bc30446ea42027c769b0298cc5819b185273d5aad27386aa6380b7ca75dcc948115c9df163e11ae356ab81aa70a76d66b18ab64b6430c0019450e4961c24589c6e31c2dbb0c94146a921a258e39299dc2dbc3d84cc0b13ca44624a838dc94f94586bf218d8941a376a901a43b6881534367e621b2f7b6e0c0f273b4b0d72237815b2f7b6bec061270b6ec2e2020e94840510f92e994ae1534921b4bf089e070f548404f8ed42051d29080a01e4e67b34c1a707093c12781a3d521013a39508152d3d4ccd52ab65cd496f51c0d7e5b1b9c83a693a4a54933514bd7e5b1b9e828aa5175ba4a48642dfefc126eba2c25706d72b68ab094c08eabea12c2ce02341d2cc0921107616681c867d239e085118bc4eeb143d914f20c2eb08c0bd2dc26f4bb2cde5ad6d5f830b4c230300bcbc02af575072c3003b5a845b5acc205049b0dfb0b88090f8d5269945a5c2eec01b64328e0ba352a354b85d36d90c00c3c12413e91cf4443b815b8f9b6bf006d86fd85c6038ac4a20040180a2e0678d90e5706bd854c0656aad5ca67829cde6e5504adf62b0b5de80e532b1e4753a1cced6e552a2c5656bab81aad44abacca5419b4d8d77902582b22f87ed004a0d027f3e058281208a1020964d8040490c461b2c3b69b535c9e0c2492e03022632590d7278209a498140094c763315ae4f04af566c257ae8b2583059d7cb12e2c018bb59b0960bc2d9695e073b3c8e8ad562ad5ca8b2aa8e46eb258dae6d079d4e67636bc025616bbd010ad55ab9527154589e7616bbd4146d37bc9e87456ab156ae55588e2874529d0ad73b044ea733b1b4def179d85aef5048c92235458bcfc823fd8120811a23d00330a2382030488d51a31460163f1e8ec701e0e0683240082a945d6e94304abada7315c125775141088345570a75b6d398aa0b2bba8a888439440a8a74a2024eb42014b65e83c203ad63001a55269184c22109601a773798878381b9e81bf,0x1f49c1c4ba613d6e3e72c05be53aef48a1c621b720c458f8468301af7448cc39bf037b06732edc9cad1256b8b9c2eef7fbfaa41d8566a78c15197c7e2da8e72db6c86003375f96c6f0640140adf5746e3e40b7ca75de91438c436e4188b1f08d06035ee89198737e06f60ce65db9395a24ad711539c2eef9abfdfd52cd304be2da8c2a6732cddb2bf2d8dc30002e1dbb5de21115c408fd6513b256db5815b8f902df29d77a45ca2c7c2301b2b2eaa61b06b44e0e26198a1c621a18abc1ab17b9e30570a34c17c7e2d81bd84220a24661ced0cd4ae393449ccd25613076a353853b9cee00bc86db6cafcb6370c003e88e969ea666a95c82887d8149ad30d52aa546a797afcb6431b9c854502b153eae93599cf5b8f9cb016f94ebbd22e5163e1180d95a9556ae1da8d4e1558b6db2bf2d90c6e1800170987]
theorem sro14_0:zo (zr 9 st14) 9 344 srs14_0=true:=by decide +kernel
theorem scf14:zf (zr 9 st14) 414 313 (digits 9 26 0x12d3d4ccd52b8b698fb0293982d2a5869e35170a34c0fea39dcdd7e5b1b) 0=true:=by decide +kernel
def sa15:Array (List Nat):=zj yy [0x88c4c8cc8c48c04c0c4c4c0c4c808088488c848884880480848480850,0x28282864e464a46464642474207020701c6c1c4c1448144cc0c48c08ccc50,0x2cac6c6c6c2c680a84a8e84e828a84c6868cc8684a82868688c82846810,0x34344f0300b04b0f074b070b074704b030707430770c7003030306cec50,0xc4a732a12129e468444a790a130a10129f44b408f434f474b44b4074347450,0xc7c7a2c121f1c47c701f1cc4c792c12131c8b064704870444c790c120c10131e4e850,0x22a122e9ec6844ba702e9c8cc44cc4cb37123122cdc84c444c44b37203102cdc40c50,0x33cde88c48f37a13113cde80c40f3733a9eca864a848ea713a9ec2840ea7b3a132e9d0,0xa0210549d8084d0c72431c50c70431ccfc7b2c123f1ec7044fc7a1c1b0c103f1e83050,0x30b468b4495d7c1d1a1d11575f034415d7a0d13549e888495276221a1211549d84850,0x1aa73609c98271609cc48418273021c3a135a9f0a8496a7c1a115a9f028416a73575d0,0x3731c9cc71731c1cc7d3a136e9f4a849ba716e9f42841ba733a136a9c9aa716a9f46850,0xc773821dce04773801dce0c0738201ce040738001ce0e1a72869c61a70869cddc72771c5dc70771d0,0xd04a82412a0504a80412a0ca5a82296a04a5a80296a0c88282220a0488280220a0c782821e0a04782801e0a10,0x2752a05d4a80752a0dc4d82713605c4d8071360d74a825d2a0574a805d2a0d05a82416a0505a80416a08e850,0x368ee8ce24a82892a0624a80892a0e05a8381360a04d8181360204d83756a09d5a81756a01d5a83752a10,0x2e82668666824e864e824a864a8268c668c248c648c268866882708f28ea4d0,0xc2580851214c85221734673426b066b024b064b0276867682728672826e8650,0xcc52314cb522d44b5d2db0b602d4ca522944a532988a6029749602550,0xd0524170f603d6cf613940e533948e533548d513574d603540c513150,0x313604d6d3634949251494d26249812534549151456d16045450504150,0x35d6c75a9d697581d527581c536d49b516d65b606d41a534d493514d50,0xc442910df527d45f5c7da9f697d89f607d4de607949e637549d517550,0x1ee47b51cd47a5128449d107479512543150a]
def st15:Array (List Nat):=zj (fun x=>6+10*(x&&&63)) [0x8c26082508c180c21041d0601e0c1b04170602054104c103410080f04020340f018302c102410140608030401050,0x10448084704450f8420c3f10020f410ec10e410dc10d410c810c010b810b010a810a0109426090,0x6d04691906a0c65198218c1184117c1174116c115c520859148215c5912031541124520851044d1004e0c451004a0d0,0x24890088f22822348a088904870483210220411fc11e47c087b1f021e47b1b831dc11a46e1d031cc11a4661c0319c6e090,0xb22c022b8b008ac2a022a8a808a62882290a2089f26c9724442809e085327822709a0849268226096084e2582128960841258225090090,0x273402078cc08ce3302064cc08ca3182320c608173182310c208c030822fcbb2e4b7107d2f822f0ba08aa2e02290b608b52c4a928c41f4b4090,0x983a02128e808e63902250e408423902384dd364d710e2380214ce008de3702124dc08da3602128d808423582344cd31cc310d43402348d0090,0xce3e82064fa08f83d82328f608c83d823d0f208c43c82300f208f13ace93944280f008533c023b8ea08ec3a82378ea08493a82368e8090,0x10645022b114090444824011208a644824450d42503107d44024390c08bc4302429080906420241102090040823fcfb3dcf310273f823f0fa090,0x834d024c930092e4c024b52948d1d10114b024a92809264a0249122092048824791c091a47024651745513107d46024391608bc458242914090,0xe2538214d4e094c52823b94a084952825214608da51825114208e650825053b4d531108b50024f93a093c4e822153a09384d024d934090,0x925a8259d6558d5f1168598214d66089c590258162089257825755b565551011570201d5a0920560255958091a550254954094f52d4750c45414e090,0xbc5f021c17a09065e821a97809005e025d5715bd6b11765d0214d7409725c023b17008495c025816e08985b821396e096c5a822516a090,0xec63021258c094862823698a089862825118808e6620261d8560d81107d61821d184090660822b1820900600229980097f5f57b5e441f57e090,0xc1660265d9564d9110d4658234d96082765820799408cf65020659408ca648232592081764823119008c1640263d8d62d89105363825318c090,0x127690201da409246882485a209566882479a0091b6802549a0099f6759b664409d9e08fc670233d9c081967023e19a08c966823d198090,0x496d02265b2084e6c82129b208416c82255b008926c02109b009af6b5ab6a44045ae092a6b02491aa091b6a0269da568da1101169824a9a4090,0xec6f02379bc08496f0236dba08986e82129ba08e76e02251b808426e026ddb56cdb110a16d825a1b608536d823b5b4089c6d02379b4090,0x497382521cc08db7302511ca08e77282725c7715c310537202379c608497182265c408e670826fdbd6edb910e36f82701be08536f823bdbc090,0x9c7782585dc084e7702251da08927682765d7755d3108b7602215d6088375024bdd209d173dcd72c4541d008e3740214dd0094c73823bdce090,0xa17a025a1e808537a025c9e608ed7982581e408997902139e4096c7882255e208927882785df775db117778025a1e0085378023b1de090,0x537e823b1f809487d82261f608e77d0214df209f17bded7ac422df0093e7b824f5ee08857b824e1ec09377b024c9ea092f7a827a5e7795e3110,0xd820216206080f81821342415838140c1e031140c15830740c09031342216038140e1e831140e16030740e088380c180417fc17f417edf97ddf5110,0x21183cf93d416130615a10085883828360b354cb070261a0d82c1f32c1c06068360b354c5070261a0d82c1f3141c06068360b32cc507016180c83020960c080e828208e0a0a0981d2b494440186826074ad1f110061a0981d2547c04110615a08090,0x21985c4f24c4c1006092180857860208a160859858285613704df110521a1584dc112c4414868561337c4b110481a1584dc110c4414868561337c43110481a1584c4b10c441006032140857850203a120a1183cfd3e44c06068460f3f4f513018190,0x22588d495144080861e224085789021ea22085988828861f36ce7101fc185788021661e0a1d86c9925600100615e1c08598682866175a49d130521a1985d6913c4c1486866172744f130481a1985d6924c4c1486866172749313048190,0xc8b021e62c080e8a821ee2a0a2989d73585fe12068a6275cd6d7f8481a2989d615b4407f8623a2808578a022322608598982896235454d808521a2588d515260214868962353549808481a2588d51516021486896235354580848190,0x2358cd3f4cc6821068d6334e5331a08218788d0223e34087a8c82236320a318bcbd41e021b868c62f2f5018086e1a318bd0740602198615a3008798c021622e087b8b828b62b2bcab8106e1a2d8acaf296041b868b62b2aca581066190,0x93e4d92e45124702a4e0c11938291c08930301e4c09579224a0e4700a4a0d53912480e47002440e410433902420c319023e0e398de3b8f440463808078d828d6334fd391a084190,0x22e6c0a6721a6a0e67202680e671fa640e5f9766198c40465e0807970296e5995e51107d96821d654960394c7296031be580871952560e531b2560c6b942540e5318a500d0,0x28da2e89a144a1c60a303a1c5ea283a1c5ca203a1c5aa1039fe7da0e8110279f820667c0a79042f9e27a0c2d9e2760e719be759cc409e7008199b829b66b9a66512672226c0d0,0x43e9aa8831bea20a9f1b2a00d0ba6aa00c67a802a7c62a7034169ca683a6697a568f1293082980c27a602a4c1aa583066960a93052940ccba42940e9304a8e0cc5a3a900d0,0xafd6cad83516b6af03aec3cad83256b6ae0310eb6ad03acc1ac6afab6a912ab0eab00eab0e2ae0eab0daac0eab0d2a80ea706a5a8ea1a744a7c76a9031f6a40a9f1caa20d0,0xb16c3b06b712bb152c40c53b1025cebeb083afd72b083536bcb083aec50b0833b6b8b08337eb4b083126c20949af2c00ebb11ac00c99ae2c00eb9262c00c4bad2c00d6dadabe0d0,0xb5472b6032f6d2b6032ced0b603b3caeb6031bed80ad51b2d60d07b4ad60cadb42d60ecf2aad60ed518acc0d01b32d20ca7b32d00ecf292cc0ec9042bb22ca0c29b22c60d0,0x249a4ae20e9191ae20ee3962a20ee395aa00ee39429c0e5599ae00ee192a600ee1912620e4399ade0edf8ea600edf8f2620e3f94adc0edd8ea4a0edd8f2440edbb66d7b3441f6da090,0x2eda8ad80eeda82d60eeda72cc0e9ba1aea0eeba0a940eeba028e0e7ba7ae80ee99d2940ee99ca8e0e77a1ae60ee79d2820ee79ca800ec791ae40ee5962d80ee595ad60ee5942cc0d0,0x7761985db325c4c270777ddd86617131b36d452221985c4c6cdb5149da1d6757de176c9c156b76de3866171304e1d6f5addb774ec16bdb52f20ed3aeaf20ed1ae2f20eb5b3af20ef3acac80ed1aaaf00ef1a9ac80eb9aaaee0eefa9ab20ecba4aec0d0,0x145536c512e2d810bf8ac6eb60a96e5308f13a5bf6ec94145716423c4eb6fdbd260527c9b6ddb5248582607110064b5af6b51f207a8b4af1b8ab038665d95344cd3fcfb8460f67d9d130b344cd3fcfb8460f67d9d13192294d12223745cf894610418661713052121985c4e0c976cc490e1713a1913092150,0x29304f16fc98124493e4708d133597654ca16a5a8eedb6ed996e59b96e326edb96dbb665b966e3a80831697a64cba405344cd65d95310593e4591c3834ff82c1c65058359782c1c33051ec0c12c98516c55346e2145536c5b06bc144b260b58b6041ba2bb6ed9b00a8b60419a2bb3cb5b6ed9b40b12acf2d6d0b6ed92c4aa1d0,0x2605677861985c9f6dc4c1e17090520c0c03826fe1584c4210e9395b36c4de161584c4b111bc161584dbf12846fdbb6cce91085032136f83344cd65d9505c50620d65e0b3441c1a0b8341807848341c82d97654d01a0d0720b335961647050,0xb6ed5094f50dcb7454814e53c5bf6e4ec16b7b04490eab06dbb66d50ea5b8e5bb6e591bc60901882c0c11b73c5bf1284544525147c120f8444c0e1183c4c060483e111301867058460f130cc121183c161319d3c8683c1813211674fd190,0x781ba2bb66cf0306b8c6f0ae1b7e4d8de621410066d99c21f0152623895ce114988e257404526238954e107c52021f14f51dd0107c7354e0d4f12223895d152067ed8f3b14811d188e251214a158b63dfb7dcec150,0xba6eb9be7db9e8e1a8da26870ecf1e80e1ba2db606826071100610e53adc770c53160981c440192b160981c440192815cb88e256284765f18cd411a23519414c5f17ad3814848d4688cd414c5331c847c4688ce354c06765417c6331a2352147765d77c6338d4687bd3021414c5f17ac8516dfb84070d0,0x2238958a0c06158580ee2064d56e48680484422160306006085859de18649f6dc221c18018560c1815a060e9006428360b0703159677861727db70907a7c1a8e9f0a8da1c2a6e979f66fba686190,0x287069a8c62f952d216d2966548be3145ed61e54a6a2f8c6d99606a6ad98c62f616a01a2fa6a548c6d2b606a6a599510d8be315f6a021ca520060ecf018560c06148214eb4728363dfbb154f746c152071ea2d03acf114f63dd188e25154f89623745cb520663d4f74623895ca190,0x26706d2998520e66b485614848b81ad1b73c5bfad851a654098f7ed4f745bf3c5e9b15f35d6278a4c8a6276fcf17a6c55d6c11209af9bf3c5e9796b61ac1b14488a6275d56fafc87a62989c485b857ed8f7a6275d4f16fe29b0098cc6823c3952591a431216189d755be291abf5d6278a6b6150,0xd06b40654065415821a0590818158580e9b0642aec1b001b02540ad2121489522814b]
def sr15_0:List Nat:=zg w7 [0x3a40d21e80b403a11d00680708184c19e00b7045801dc10e047001b820c08600ec05601b00580688144a19d00a8254013a10950868234002a105042807202900c80241b15c8ae3d6dea6b525a89900c863330111888c026113001804880442199008802411200103f,0x9f46913c8d22789a40fa3481e46903c4d27514ce9a499d4723ae92474d248e2a491d4713ae92274d244e2a481d74903a692071524ba299774932e8e4595248ba389774912ca92059524b3299646932c4d26599c8b23491626922cce2591a44b1348966702c8d20589a47c298f8721eb12239624072c489853130e424e24842c4889389110b12024e24042c489453126926251c843a490947112692221d24442a488947012692021d27f,0x1b547268e922d6d241a3a4b0453608e4c11c586248b06490618920c19256a29ad94935ae926b51c96ca492d74925a8e2b652456ba482d94905ae92ae94d5d392b9a9256b524ae9c55cd48ab5a91574e0ae6a415ad4aa453548e4ad124956248ab4491558920ad12415624a1853430e485e2490ac48a1789142b12284e2410bc48215890427127e14cfc391f78923eb1227de244fac481f78903eb127994cf3391f46923c4d24799ff,0xdba3937b4926e6924dd1c5bda48b734916ce920ded241b9a48367496a8a6d1d24c]
theorem sic15_0:ze (n:=14) (m:=19) neigh edges goodB true true 0 2 433 mBook sa15 (zr 10 st15) 0 sr15_0=true:=by decide +kernel
def sr15_1:List Nat:=zg w7 [0x11046322090445412848a825010d04a1e08c63c12087a82510ed04a21e09023d412847682508e704a01ea09403b41280738250ee6631dcd043d39a887173510ee6811e9cd4238b9a807a73500e2e6a01ccc60139a8c01735180e682009cd4400b9a8807340804e6a1005cd42039a00027350002e6a868a70d1ca1ca49433492868e30e52461ba48c334908729210dd25dc29bb872777122ed6245d9c483b589076712e614dcc39395891737122e56241cdc48395896e8a6ded27f,0x3b2b4a074d694ea518ddd4a51ba694a3752904eca5289d34a50bba94a174d2940eca5281d34a5389a63713504e26a05c4d403949aa5d28c6be2528d7b4a51ae94825f12944bda528974a40af894a15ed2940be252817b4a520b463416904812d28905a40a12b4a042d69482518d0b4a51a0494a341290485a5289094a5120494a241290285a5285094a50a0494a042d294084a5281024a514b4632a5694651ad28ca5a41152b4a228d6944512d288a5a40952b4a128d6942512d284a5a40152b4a028d6940512d2bf,0x2054f2a16150aca8184346f20a378851be8c59460c312379091bcc08de4046f10237918b08c56460c230590d13c8289e2144fa216510ae8819440b1a370e138689c264e0a3706138289c064e5ca6ad4b5369a974d8928c712520a294a50c5894a18a5294115a528e05a4409a638135050626a8a0a4d51409a8183135430526a820c4d504149aa7568c6ecad28dd35a51bab4827756944ecad285dd5a50bb2b4a174d6940eead2bf,0xc0e9e4074f103a79d0b0e856740c3a0599153cc4a9e4254f302a790153cc]
theorem sic15_1:ze (n:=14) (m:=19) neigh edges goodB true true 0 2 433 mBook sa15 (zr 10 st15) 201 sr15_1=true:=by decide +kernel
def sr15_2:List Nat:=zg w7 [0x3805c8a848ca919519115222a2312a5212a4302a5202a44c1a04c9804c88819112222439af20cd78866bf34599a2bcd066682c86b1e4158f10ac7d60b2b057580cac0590963c80b1e2058f2c16160acb018580b21da7906d3c4369fb42cda15ed03368166594f31ca790e53cc329e4194f10ca7e50b32857940cca05885d3ee857740b109a7cd0ae68166474f313a7909d3ff,0xe83b2603b2d03b2483b2103b2720dc326dcb24dcb22dcb20dc9a8270e1a7234e3c24e4b24e449c7829c9629c8538f01392c13925099a5234a3324a44946629484294a6094840949186cd196c9196c5196c11921034224844f8300f92c0f91d033a24744d874cd919b1e91b2e89b2e81b232066448c897032e2d22e5c22e445c5a25cb825c9a05cbf,0x17a7407a74da5198a50a0250a3127cc5275012751683e6283a8083a9279532797417974079741a4a9c9254c925d0525d0125d1a62e6262a8062a8d31331311403114614998948a0148a3f037e3c27e4a27e4927e5227e44fc782fc942fc922fca42fcb80fc940fc920fca40fc9e80c1e9081e93b0d1bb23762d2765d2764c2765a276492764227644ec582ecb42ec922ecb22ec842ec9a0ecbf,0xc7bb3d3dd9e5eecc4f7660f72997b7307b54cb9b9839aa4de94c9e9d0b]
theorem sic15_2:ze (n:=14) (m:=19) neigh edges goodB true true 0 2 433 mBook sa15 (zr 10 st15) 402 sr15_2=true:=by decide +kernel
def srs15_0:List Nat:=zg (fun x=>9+10*(1+(x&&&511))) [0x758beb4aef47d08051b5241dd1f1cd124590a9b51a4306e46418ce33c1b06eb2342053cce81f8f63ac8117e94a4a8f99c147bafe788fa3d90440521489ec40d260551e780387a1f5806047f204f53d28f208127bafe788fa3d90440521489e8051ec408ba2e51e78040f75fcef3d87a1e28f3c80e781e47b300c0d1e7b819685b28e505132f047a358c6380f0426c0621e22b252e2765cb1f314c93502663638275b006b32d4c2d174450cc2305324d8091a06608d88a28701950e4711b492890741ca21174206b18e641a8283b22c3ba203922a054791d620048a8ee8b0da852328c2488f2203930d43cc28d21837084104c83b051151dd161d1124811f491174206b1d816320ce31b12c530eb50d213b0891a44908d40d15cee188e5164e3028b62c2f6bcd073a8c4069e27ca0a81028ea1780c5e010721cebd2f8308be770185816c605e97c3b4ec3ac620439c024fa027d5f37c5f70340b024087e0108e8e33580a77001c7010ae770c4738b671815d88c63b936039ea4103462ec49d1e480047c9f07e0042d1dc311c82c1cc05731c900c0173c083e0f2bdaf23f9d4749d041020e73917b5e4e91785d170ee04455134b339ce537c602a8a0b5caad7b581b06b11414178591884e0e86a1f0144f11b64d889d38cad2bcaa1842309445054620e1363114623129b09c22803897188a3138991201453149b26c4548b22e95a588461487e0e86a599562f88a0a0c81e1582aeaba4e806417858ec01874490774606c4800acd0ee928d89532e934d693a3a38a52908ea12b32cb330ca84cb1ac3320e0171b5241dd1b1bd19028888b0928487e870149541c9c410985c49a0097240c12d935ab3808f75fcf11f45a164821887815ce33ba663c01a7bafe778f42b904310f62d1cc729e40b4b12e681a25913502a162083f3080d3b2e5422f58f64c1f64a6208e5c054c12f8420fcc29ea1a21b2008101161251311d0f1142342810a2a765fcb603101161251311e5e4fd111190a04a8a5fb26c8a84a24bb2d81d14429914f13b4580a5d2885f27e5da7c050fc46121916514f5394d5414b969484f4c210c4907992a2194a018ca1817f,0x28c5a260952a4d0d88a129aced6c59555371140827840974089c3e8969a505401064049bae6baab0fc070de950ee948ea93014962609bae5725ceac2700e7d1fab92e67fa024d1335620409aa52daa0dd3713502940ac94cab948e056ca956b5a566a982ca3564a6550a15580a5337c52074df94205551576f9bf5443a2789d56410a91424fd6253564aaa705137c09551375653a545362789d6f810502b2532aa512a60570dcf8da398d1db9baad769cd709d7711d972dc1056acaa9c68c82913c46d9362274e32a460284a6b5860d7d554dc4502462118c20175dd4aaa9902c6737386e7b9ae13aee246b1c5595538c0ac680e01807a3004ef3baee0761c870f0818ab2c4a94b5354b0a8aa59faa2a76719e0d837a9a64592a10926297ac8d100d344c96468c065815cb23460329d352c52f2aea3a959c67aa40d8374b8aa4ac1c58b4854338cf52c1b06e9a264b215a0b4d5a44b19c67933a58360dcb02bcae5913106a6ad02565414e58d4297154b22620a574dda80049815a564ca03365603895e37d5b02c5e19534022b1352c52e2a930028e0920ee8f8e68e0161d8582387c070440f0340a0d0320c02f048222a8982f0b231024872844310456ff5013fc44090233d82e5]
theorem sro15_0:zo (zr 10 st15) 10 602 srs15_0=true:=by decide +kernel
def srs15_1:List Nat:=zg (fun x=>9+10*(1+(x&&&511))) [0x145acd4bb053630690a263a80b6bddd584ad2c4751bcaae2cc97cdf179ddf11414e302cc28710a1dd161c10e4b66b4d51e440724c61786a1fbaed587532485131d659bba9f96230956f2bceefaaa228286c112b09c94ade87add06ad333974da50eabead29a9924270990570ead3b3a13d5d755ef66d6e1cb7af5962f6956ea6daecbce2282af405dc61ab50cf5d36943aafab4a6a64909c26415c3ad5cd2b361359add8556cb2e955f97d0380b24bccfa3d0f15bf61bce0a5800987a19834240881bbca1f03d7802adf3a338b75a53633b6b95098cad4f26b08db09752f0ac3a99242899c2570eb2cddd09d614fcb1294750a46f574612aca2e2de20f5df66d554dc4505408e302cb30d5f47a1e20396ca56cb5f99db499cb78356d5bdadd584e4a50f5ba5f5a6696e9bc27e8561d57d5a53532484e1320ae1d659bba13a7e5894aae926309565179a14baaefbb2dfb36c3aaa9b88a0a811e707814b0082fa3d0f101cb652b65afacdda4cf06adddbc991c2575c6bf36d57492f35dd75350d3ddf765bf66d86f38296008aab0f1e00104f76805f47a1e2b780e8e96cac2958decb5f649799c509ad65f9b6bb2dfb0de771816052c00d2143ba2c3821c96cd69aa3c880e498c2f0d43f75dab08cad6bd611bc7555dd4efdc61f3514bcb374c3aafab4a6a6490a2670990570eb4fcd8d284cddc612ab8ada367554450538c0b0d83a46c6f4391644a0ca765245d081ae5182e9b82a049b420eb55d7159a19812e7b827ea72e8b914903180a8194a618f0e43f73a9570dcd72a8c0c4606c52e0c5425251e518429b82a04a74186098cd54310dca50fca3702c54dc15021940d51d4c6a5ab524c430e645895004a96a3295504db70cfcae2366d98637c27294a34dc15022a01256139295bc0fab702ba2e985c1885a1855cebd9b553b00a304c76a5ab991623280c6398a65181061892935328c1f4dcc905408b13540fb042b7b804dc9a24299c453a665906ec44b204636e924443ff3ddb921ca15746100bae6811310c416d5013fac80902366d551119e2533ccc6e1d1231d8252413348fab9d73409390e208a6cdaaa8088964044d10b9a6489b04a1a84745046c62fcc9b01db72a1ad184026b927284a710bad1eba966d554dcff11408b2024dc084d5244d8250d222e248c64e95090aba3035c9394253885fcb36aaa6e7f88a04590126e436db9a24299c453a6423b0fcc7701db32149e6790e18402eb9a044c87284431045d15d9b555013fc44b202408996236dcd120ccc229d1219d875cd0225fc8f1fbb36aa590cd08d7802adf3a338b75a53633b6bc2656cad6a52f291636ac3aafa6490a267095c3a94f574ab289556b25895d9b4dc4505408b309ebc0156db4c356b99eb4932384ae66eaeb5ace5c2cd5a8221304f67009281ca1787e0e96611a7e974946d8c2558752144c754b12baaa2282abb0b2585441d0fcb30c53f294612aca3515554dc45054094f0462788e686c44e9c6bd0c254aba301425359dadb36aaa6e22812310a1c06f1c46d33f5c55368da1322c93282d35a8d2e4bc07519c4cf9b367a5895cc8b21bc0967eb8376645912c02accb5578b82dc02815c82e1cf2d5ca3f0fb40acc72cfe2dacab19cd404b78fa3fab2809fcb20b3945c39e59b90e696e7c9f1561680a5f568a54055e00ab7d30072e964adca0a265e08f3631a13d90b3041686328e0158a072ed622828997823b16132ccba80ab557963ae0b2846c503976b114144cbc11d8b099755b96d5941b3e4f0fb1d62fbe8740b947cf209a167c9e2759d8eb2045fa3d7804b1cb651c02b083280005013fafd068178590181abe0a5ec013c8f549125bf15fc8cfb3d2f1bcb2602747bcf2203de47a9e978e4792a8f9140ef6bd615050f7813d]
theorem sro15_1:zo (zr 10 st15) 10 702 srs15_1=true:=by decide +kernel
theorem scf15:zf (zr 10 st15) 763 81 (digits 10 44 0x1284c13db16ca2d8b2af5adac0d59cb499d4c8e12bad7bbab095256961af8de3aab85094e55716fabe6f8bceefb36aaa6e2282a0471816) 0=true:=by decide +kernel
def sa16:Array (List Nat):=zj yy [0x354c540141414541040104408448c408404418004001400540c00050,0x28a84468684ca8068286868284d414494094d4549474544941454741450,0x50a110a10029f40b4494b44f414744b41434474034284a80a8e84e810,0x10b5e034402d753d13035c4b4480d711d11035c434400d73029d4a8480a751a11029d0,0x7d731d5c875711d5c0757105101c1cc3d720f5c43d700f5e0f44c2d782d120b5e07450,0xb1a112e9ec2840ba73275e8b4489d7a1d11275c09d7a3d113d131f5c87d711f5e83450,0x60510455c0144cbd7b2d122f5ec7444bd7b0d102f5ece844e84cba7b2a112a122e9d0,0x14844c8449817d111511131111605f40454044181730113455c915761511455c05450,0x3024608091810246000918301c6080718101c60007183715f494589449c571715c1c573605f48450,0xd74a825d2a0574a805d2a0cf4a823d2a04f4a803d2a0c291820a4604291800a460c0958202560409580025610,0xdd4d82753605d4d8075360dd2d8274b605d2d8074b60da2d8268b605a2d8068b60d8958262560589580625610,0x1942414641427446744254465442694f44d94d44f68cde4d82793605e4d80793610,0x5018005001ab466b425746574247464742568656824686468275467542594650,0x155551814505180553114845111744651180451054015305481560190,0x15a60694d952654595a65959616581950614d552554555a55955615590,0x5d50754dd52754dc527141c617159c657181c506d4da526945a5d6990,0x72918a46891c0450105]
def st16:Array (List Nat):=zj (fun x=>6+10*(x&&&63)) [0x1f070260c1d090208c107c1a080306c1c0819041604140411038204c0e081104c0c0c0d038202c0c08080403018040c01050,0x1244a08471002114400847114380c43043910020fc10ec360f030dc3808350433042f0c020b430082f0b4240c2b0429050,0x6c1a821a4651845b10411a0219864086218020f060085e16821705a085714821645208571644e0c1f138540c4f148207c4a140312c4e081f1204c0d0,0x5420821d08208801f821407e08701f821f07a084c1e821b07a08771cc6f1ac41e07608531d821507208741c821406e08701b821306a090,0xc49c08252682074980894258224c101c92089123c8d22c414c90085423821408c087c228221c831fc7b108821821e0860853218221082090,0x4f2c822c0ae08802b821c0ae08a02b021f0ac086c2b0229ca528c9f10aa29822a0a6085329821d0a4087028822809e086c27822749b26497110,0xc230020e4c008be2f02188bc083c2f022e8b8085e2e02170b808b72ccaf2b442a8b608882d822a0b608532d822d0b208842c821d0b2090,0xe03882378dc08da3702364d5344cd10533602358d408743502348d008703402338cc086c330231cc12f4b910ca3182320c608413182310c0090,0x1033ecf33b4403d0209003e823f8fa08fc3e82034fa08f83c823d8f208f43c823c0ec08ee3b023a8ec08e939ce337440c4e808253982390e2090,0xfe45023f514080d45023d91208f544823b91008eb440243d0941d051031438243108090a42020950808264182391060820410237904090,0x1274952348440c5260825490238122081d488237d200895480247d1d46d19100f47820351c08f746823d11a08ef46023a918091745513444403d16090,0x1374d5334c4432d3608c84d821053608c54d023093408394d022fd32083c4c822ed30085c4c024bd2d4ad29100f4b823fd2c08f44a823bd28090,0x4c520251d4550d411031518243144090b51020954408265082395420820500237d40093f4f53b4e4432d3e08414f823093c083c4e8217138090,0xb455022155408b054822055208a054021f550094f5354b52442254e0878538214d4e088553021514c084f53022054a085052821f548090,0x54590234d62088058821416208cf58021f160084c580257d5d56d591053578213d5c08b156822015a08a156021f158095755553544414d56090,0x4d72081f0b8560d710b8460d6f040560c3b040460c1f0b0580d710b0440d6f048580c3b048440d6d056b0569056759563584414d6608d7590221164090,0x17d5ece136c0207060bd7c082d5e825e577404f95b80c19795dd013c56e03065e5773e4f10296e18565e020457808585d8204d7609755ccff3dd6a03065d5733fcef5a80c19755ccf73bc0a5a860b97408115d020b172090,0x18961cc31743a0e06625870f45d0e8361810620211d880812618211586098560d0d09c1e0906615834342107824198560c270841c078615984082f610216182082d60826057f394df0716c182f60020b57e090,0x19163c711b56e128604190085764020498e085963826358b19c635c038198d62c6717d700e066358b18c5f5c036182e630211d8c082c62821158a098961cc930c3a1006625873243d0e840198961cc30f43a0e06625873245d0e840190,0x44658216596099564c791541e1486655931e45107852199564c551441e1386655931e44d07852199564c551341e1386655931444d0784a182e650215d94082c64826458f2a4755b852199163ca91c56e14866458f1d4715b84e199163ca91b56e14866458f1d46d5b84e190,0x1af3e1b00cf76b1b00daf3c1aa0cef6a9ac0da568da969c4105a40839688267410259c68030159c678366c006703665972d4b15a04e199965cb5285681386665972c4a15a04a1846660215d98090,0x30dc072030e5c809c50d1c60dc3189c60c3d701c60dc50c9be0dc3179be0c5d6f9c00dbb04176e9bc0c156e9b80db705b56cdb16ac403db409af401b20cff6b1b20d0,0xb5751d80c55749d80c75741d80dd11d1d80cb1751d60c51749d60dd11c1d60ca1739d40c4d739d20dd11b1ce0dcd05cb725c76fc4714427283105ca09c50f9c80dc3199c80d0,0x7bcde7a837b4187a837a4179de578ddd11df0a9e60c31798277c287903095e40827781e20ddf089e20c21771e00ddf061dc0ddb765d773c42add47683744a8768314dda090,0x1f366a020e036a1fe0e03699fc0db966a000e016a1c60e01699be0dfb7e5ff7f44105fa08397e027ddf57c5eb11ed0a9f60c317d827b4287d03095f409ed089f00ce17c9f00d0,0x77c147d1d4bd2940cf4184f04b72cd5f5747c15bd7b2080e09719fe0e096f9fc0dd5712060dd370a060dc1742060e076e9cc0de16ba040dad77a040e056d9e80da17ba020d9f7b2020d0,0x5fd8149d253a4e75f41c5ec0237cb2dd5765d5166452749b49d2507452859755d51664571415158507909071830c476141e60c1c4250f50071183862c3618c691842e2157665972c846659755d512b857d5ed09f97ee0972dc968da580c8825a572dc968e037f877d5f77b43034147d1d4bd033ecf4190,0x10048c70e0b90f462e412040c70e03d4dc76bd6e5dc1111af2dd570e15104c631cbd4dd3317050e1890e98731d370f472dd570e1af5445919af158130db56bd6e5e57740db11d6e5e5776bdb540db13c48826030e430842779de57805111890e0c74dcb9048731cb94dd313085625872e43831c3a17475fd8149d255f41c5ece939df77d602310,0x5d57340d173dc55d57345cec11f77b4255d972dd99115707c2f0b4455daf0e0b711890e03a11446bd570e0b704456bc1116030e1af55cb70ec56bc3855cb70ec111957284b72b59965c60e1576bcb754450e18961c3a2e05040380483b10100483831cb9150,0x1f55c25d413085829cb7645db744121c1f55c2c0dc070cc76357062c3872081a5c072dc36357062c380f5c929c070d8d62d700e0c72e5c8244d1445576dd21537701cb4fcc70e46304c74dd350f0529cb76456e63ddb744729d915b98f745ce19db2dd915b98f744ad73c86456e63dd176dcf2c870f5c972c5d70055cc11090,0x1d25555759d65758631c6972c386357062c3d70c97441744b709d12dddb0d8560c310dd12dc570dd12dc590dd12dc130d8560c31430464c5709936548753c4c147b21d4f52454158560c310944744b704059101f050,0x2dc160d4e08b776d4f0cb776d4f15c460d4f21832dd9159d8f53ddb21c5720b716421584455d6763c7721cd976d4f31d3772c386346904d155d9159d8f1dc87365db53d6e748b53d4959d6114051cc7720cd53648776d6753dd21b0b1ec8753d6758c5419915b98f3648755ddb59d4f748752cd]
def sr16_0:List Nat:=zg w7 [0x1043a910a352212ea4421d48051a9009752010ea40d2980ba93034e402ea4801d4880ba9100752002ea4001d481453028e402d24405a4880349001692000d247481a4d192e88b422ba21d082e883423440a250ce805412a008d086823400a00a90148a3350128075442a115006a881420a054a8254448024119084442c1505010003f,0x220a92f4a65e9c8bbd49163a912ef52258ea40bbd48163a92e8a65dd24cb1a49974722ee92458d248ba389774912d692258d240bba4816b4902c6924e94c9ad49931a932475264e9c89ad49131a922475244e9c49ad48931a912475204d6a4098d48123a91f4a63d6a4c71d498fa721c752238ea407ad480e3a91d4a63a9c875388ea701c5523814070387a530f4e41aea4435d48071a90b4a6146a4c25d4985a720a352412ea7f,0x19e94823ed294478a5288f4a409f694a13c529407da5280f14a50522630a450412c8a8423915004b22a0254c604aa08095408012aa1025500034aa8001955012263024504048a0405915080722a0016454001c8a80713180e282015c54401b8a880714080ae2a100dc54002b8a800371538a53714e4e6aa49c654938a71735522e32a41cd54838ca9604a6c09c98d14930a29260c524c09c58d148b0a29160c520c68a418514830629454a68a9c91538a2ca914415208b2a7f,0x6c4aa098d955130d2aa2625502c6caa8586955031b2aa061a554ba518d7b4a51ae94825c52942b8a5281714a51e94633ed294678a5291]
theorem sic16_0:ze (n:=14) (m:=19) neigh edges goodB true true 0 2 661 mBook sa16 (zr 10 st16) 0 sr16_0=true:=by decide +kernel
def sr16_1:List Nat:=zg w7 [0x43a2f20d178868bf4459a22bd1066882c8545e40a2f10517a88b14456a20c51058eab8695c3a2e1a1706ab8295c1a2e0a174b2b6545a9b4d7934c6f26a09eb4d513d09aa27953542f5a6a85e84d50bca9aa07ad3540f426a81e54d53a9a63753504ea6a05da4d50bb09aa07693540ec26a9d2d31ba5a82768b544ec16a85da2d50bb05aa0768b540ec16a9a2d31b505aa3694b546d16a09a82d5134a5aa268b502d416a85a52d503505aa0694b54c4a9bf,0x1818312062040c0048a004a0004886b5e415af10ad7d68b2b4575a0cad05992ebcc575e42baf305d7902ebc4175eba2c5d15ae830c875e623af211d7980ebc8075e203af1d160e8ac74183a0b215a7902d3c4169eb42c5a15ad03168166434f311a7908d3cc069e4034f101a78d0b06856340c1a0590eabc8355e21aafd5166a8af5419aa0b10657b28ad9416200af05158282ff,0x140d1d81bb12762e42a6e48dc8d49c91391a8b9200b92b0392a83926e0d42a6d48da8d49a9135168b52a8b5268352a8352660a3665136646cc544cc8a4cc824cca24cc942cc8a2cca22cc940cc8a0cca20cc9882b0d1ab23563a256552564125644ac742acaa2ac822acb40acaa0ac820ac94814149001490b01206247a4248a424ba2248a224ba0248a024bf,0x2b9498b95a0395a698aceac566162b306294eb44995a24c1a2d0ce02657013838098b81a0381a41404c540d11]
theorem sic16_1:ze (n:=14) (m:=19) neigh edges goodB true true 0 2 661 mBook sa16 (zr 10 st16) 206 sr16_1=true:=by decide +kernel
def srs16_0:List Nat:=zg (fun x=>9+9*(1+(x&&&511))) [0xac592894d66c8280bd6fa22e051d2546fb057cd805b759ed573019b57e745a9a3a3d6af2e4dcb8051a97e745b9ad6c05b4db25f302cf4c43d4cedcc1258b414ca99897cc04395b36af3b65ab9481d6cb5cc8bc5ccc19f2bd2d5e76cb57b9836df69cc4cb2a62306af3b65abdcc1758add9004a182279188b47a7111cee7a811d0103e85ea9a082850e9a47c0d3e8c01f3a0ba17aa6c189c4fc0e089901a1509a17aa8415a20860c045a6db6b5dc40230580c26248a4123399c8e3c0e17063b1be3ee04c2731f2b29b5da033360f05ec34badc15e15a8127612f4ae4113f255688c3825108684efb57aa0258a35e12f0e31b0f6e28340e24ff925a8eb6db5c8e1f1b66125b9af63bae12f0e31a0eeec13c25e1c4391c0f507885a6db6a7d1be1f1f8a05d0ecc25bd02c1f42f8024fe801cdc169f7c16db6b8bc3e202df1079f712825a0e36db4f7e181743bd06d08ce21d3bd33a5e0330580c26248a4123399c8e3c0e17063bbd8dbe20fbcdcb1428bd5e2fd74b75b47e3c17351a2400b7bbec38025eaf3766fd89d030b73585e3b1bdfc8c1b220eaf5791d8def9ee077decf751d8d8700a8646a22150ca753f6f93a923807928401f3fa1bed511e135f9a975b18feed6e6bdd3ed78710e4683b3fd75023bb802e856c16382fce8b5342ec0ab5344782f21d901574b75b47e3c6a346cdeebc38872381ea0c6f5db80bcf84b9d5f8590c8d4442a194ea7e4f6f52473f0079284c180c05d0e7efb5447859128c86542a353c9d350d92db6873f7daa23c1e8fa6226a70ac9d451a03c942f439fbed510a0fc458a9587af52435a403ddeeb7c011c17e745b9ae43b25aec636f75d82cdabf3a2e8deb8029d23c6f0bc7cd6053fe19077f3f6bc0346c8e3f2147a292b4b4825808018009c3d06ac402be24aa7b1f41067d669b4e5b021315e5055935520570d09be21a1e75e8dd03d8ec35dad06c32160ad9010988ba4992c8676a59a974882531174831d8c93028a45928953f64e2e03375b744a1b78c461cebd1c20970d11b85e2ee75e8df03e1423a20152ec98dcce331355a2e8c1157a4003160dc652ec955a2e3b3557a4020018a05e06fc0d0561808885423d44844ca8537a059a9d408e53275140452845608fcf21d0a04bdde6ed74088401a0abe02118855928d68a858a910e8f0496dd06772175a4d968671ced631b99a65f11b8c205e7419dc45a72817f,0x3a6c911a83f688f27338f24d66e130a7aa2c27b87e3f5fb8a087ede0ceb40343c1c8fe793a9ecd66e130a7aa2c4313b61aed6f0110243a6c911a83f688f27338f24d66e130a7e3d5148b087edf9f0675a0178af7bd52c09fde6b1479107ca259689f3b0207b3da8d19d4f679359b84c29ea8b09c8441f03642158ae6ef50b7358abb7eecbfd1f0fdef0702f0293f5e2b6261af0e22df54903a139fe5a6b14e6380f635caf944b4013fb6cb57ced905db38dbdfea1cebd8986bc388b64d1c0f5072dccb83c9c0d63d9046b959f4ac4c25f6e76cb57e1084522c944aab964ac6ed6e6b1576fdcf992c4fd5970a7d32d027e4bb2b160bf780ba1f6d96ae2e10b49e6d977b53b1f375b40ec3a181f088373b8ec632ff91e47c3310fc33aed0d355e6d976345e0056abcdb2e967f63e2ee691e07a323e1106e751c0bde012683cfc6ef75011b8f370ba5b767b45cfdef16f1e8807c22660ee3b3a8e32b32985b757edced96aeed0eb69baeab5bcf30eccadab5765abb8419dbcb657db65abf680d66b65a6633499cba58f8e877a010209853d5148b5c84c27cc198c863cafb35765abdcc3c542894e693199cbba1002b84ee5eacc4b1f116b8dc22995f3fa7d7e8d5d96ae580e5b2cd699a4c666562af765dd08004fd52c7c45a29e7f4fa2e6154ab3930c949b1d23198c79bc4cd4bf81960eb8157ce259689f3bdd03a559c9864a4d8e918cc63cde266a5c2713807422de112f833acb0b2559c9864a4d8e918cc63cde266a5e2a148a40bc3de02f8342cb0b6abc4cc4b7801c0522b6492d1233508f389cf91ac48208866c27f0675a0122036488d11e4efc6cf1cf833ad5058f5b2446a0fda405d6ab89eca56a509de0d5022e0557e4ba562612e77aa085aadd74be9048a4673391c781c28ef0637c7dc653680cda83c179bd86b79b82bc2b5024ec25e95c822784a210d88c3828fa7f0984ee0c955bbf7daa026aebf1bd62b9bbd42dcd62aed76dfa1c0bf5ec4c35e1c45b240ee5e7f96ec733ab7031955f12c12d025a27ef081fd02938883fcb10e5449dcced96af6419286089e4622d1e9c4473b9ea0473fc0cf5d0a6820f8967540429164a2555cb256376b7358abb5db7c8702fd7b130d787116c983d97a0e5bb1ccea882e0632abf25c220fcfa562612f4043957d0920125ced96ae2e1a1a6c1d99480e2]
theorem sro16_0:zo (zr 10 st16) 9 412 srs16_0=true:=by decide +kernel
theorem scf16:zf (zr 10 st16) 509 47 (digits 9 34 0x6f311b0d0652e7c4b275399c743bde4804d6053709853d5f88a459b02613994c86310ff3c19d) 0=true:=by decide +kernel
def sa17:Array (List Nat):=zj yy [0x980581448d4140949454545414541040104408c40840440400400050,0xa2612259e858449671161a06110610259ce8284a808a80681809848d810,0x8f67126113d9c0f6732d9d498489848b67516112d9c8585418481840b67a3613259d0,0x428416a73455c494409449157250115101511455c540414401441157136133d9d0,0xc8449817611131111605d80441817301135a9eca844a8496a7b1a111a115a9ec2850,0x3021a0808681021a000868301c6080718101c600071833113705c9c171705c1c1763113605d88450,0xcf4a823d2a04f4a803d2a0c796821e5a04796801e5a0c786821e1a04786801e1a0c09682025a0409680025a10,0x158655824546454258465842444a98e84d94d84d44cd89682625a0589680625a10,0xd5525555460514146005441530548151018005001868646826986698250,0x1ca4701140407545d537549d537149c517155c617181c5071815515550]
def st17:Array (List Nat):=zj (fun x=>6+9*(x&&&63)) [0x128802118943c187c4010743c106c30105c3010541098211041c08301058202038202028182010201050,0x482204462204322204411e8e46221088010848010f87810e87010d87010d06010c86010b45c10ac5c10b456280c4e28084620090,0x3118021098021f17822917822e17821d16821a16022316021916022b9449a4510425608a85008a450083e50089c4c08944c090,0x5288090c8209088209007c08fc7c08f6753699440c9e823c1d023b1d02399d02381b02371b02359b023419023319023097cb659110,0x128a609469d4ba4c452288204a8825027024f270203a7024d25824c258202a5824a248248248247a25067d105e8e091888091488090,0x16eb559ac44522d8257ad8204ad82502d024fad0203ad024d2c824cac8202ac824a2c0248ac0256aad52a7115cac0940aa0934a8090,0x64c8098ec561b04410b1820fb10227b08219b0025faf576b91042be08a8bc08a6bc08b8bc083ebc089cba0896ba0890b8088eb8090,0x1aed569b44421358231b58210b5821f35022eb5021d34821bb4821a340219b40267b3596c91042ce08a6cc08b8cc0874ca088ec8090,0x7582e905cee571b84410b9822ab9020fb90227b88224b8026fb75b6d9105ede091adc0914dc090eda0908da0902d808fcd8090,0x177c04f77aa9542ea040cf77aa9536ea040cf77aa8536ea030cf77aa952aea040cf77aa852aea030cf77aa6d2a04750c227b04f37b04247a040b7a04f1110b0377bc8581bc4482a0dde0a1506ed050,0x4702085500084b0009fefd2a93dd81e19fefd2a925d81e19fefd27925d81c1834fe0846fe082cfc084afc09f6f93c9c5d07219f6f93c9a5d07219f6f9389a5d06a19e4fa0836fa0814f8090,0x42c101c2a181c24010a0e0f0545a15dc281a0f05459fddc281a0f05429fddc2619e506085b060815040857040a0701218ede0201a07011f8ede01e1a0701218d5e0201a07011f8d5e01e1a07011d8d438f0185902090,0x12b094b03949c25819be492c0cd72c0a561093072934498333c9a481c7e3b2191882f8f04298e0519041f188d060d8c458388c3e2715105f1008530e090,0x86ca2781c96113c0e7b129b073d8a4e038bc22741cee25200e771491073599cde7220be6810a66414c65f2d93881998052b0a4b83949e25c19de492e0ce72e090,0x19eef551a5d363019eef55ba58530b5d9e3a11a6d767b2cb02a8d2eb35b81c551a5d66b7500aa34bacd6e9415aad38197c385978404881c04bef02c881ac3964bed569c0c38f080884947c1e0aee6f8a066fc1e0aee141f0683bba0adf440b1b954f839fc826c1cfe45380d0,0x1faff24af0426aec9018b414280e632f9586221f87a022c14400af57ee77293052895d7ebd270af57b84f57bacc37abdd669411eaf75b06f57ba5837abdc121bddeab75aa5857abdc0c09110,0x178fa08300cc65614c64efb7c9eccb3c1e48f93d995f729960f3599c76230f8f9edf6f99314fb7c9a4e824a5f6f934cb8594bedf269960b3599c76230f8fcfe7a44fe1f1f8ec467b381c56f21406d52c97da61c120a877286027fbf5781bf5fe4e0d0,0x1e043c230a7a0a16861e9e041e5ebe030f2f5f4187a78bc0e78fb93be44924a43cbc930a1e6a97df726110cbd0f853d0f17daa24143cd52f888582bca7a2b0ce]
def sr17_0:List Nat:=zg w7 [0x2b5d24561a482d7490586928a94d1539222a924415248a9c511548a20a91454e088aa4110549ec533c59267b1c8fa6491e4c923c59227d3240fa6481e4c903c5925b14cb63916ac922c99245b1c4b5648964c902d5920593240b16492c532699264b1c89a648934c912459204d324091648d10289431a08b10188c32608b045480a42500a80140a9504a809084222110a8003f,0x18e32ca31e59043d4b2887196508f52ca11c659403d4b280719650f0c631e190439432887186508f50ca01ca194038c32809631812c8202590202cb28001965010c6302190402c32880286510030ca202190202c328402865000b0ca000a19403898c067151806e2a301c5040338a8803715100e281019c54201b8a840714000ce2a000dc54e094dc314938c291718520e30a58129b0c293604e4c30a498314930271618522c18a45813830c29060c52b514d6a392d7492586924b51ff,0x4234f201a7880d3c6858342b1a060d02cc699e434cf30a6790533c4299f4c2ca615d3032981642acf20567882b3d5858ac2b56062b02c8455e402af101578a8b054562a0c15059930bcc585e42c2f306179030bc4185ec22c6115b0831841634ce1a1705338285d2cad9616ca8b589631b12c826165944c4b20585965030b2ca3d28c67a5208fb4a511e294a13ed294278a5280fb4a501e294a1e58c63d4b2bf,0x15ca4c5cad01cad02e027070131703407034828098a81a0281a3b037624ec5c81b91a9392893920139227235172511724017242e46a0e4a20e4800e49581ab12562a40a0a4800a4818183120620402004a0004a6]
theorem sic17_0:ze (n:=14) (m:=19) neigh edges goodB true true 0 2 913 mBook sa17 (zr 9 st17) 0 sr17_0=true:=by decide +kernel
def srs17_0:List Nat:=zg (fun x=>9+9*(1+(x&&&511))) [0x7b16bed5b1b4b255ee988d472220b3d8b56892574412ef776a58f874174681caf7d448230686b598cc06bb1d82d4623f4290e62819c40f1a8cc750918b2993166fb7a31195f2f473175fa3802008728c2a2034898c21f122a9590054261e4950229cd025062813e907d1882c2034898c21f122a9590053259ee97549a04a0c51285f4903105550f780a554ea04fc5a2adf6f2f97b0f5f804009808c220e328637da8395f4397e016a82c6a331d4253ea780aa2282c3d0c4730f3319594c98723946146b31980fd5035d8ec14a851ee3988a621d0a07874dc2635be5f08c369a04a8a36089f46a0705e061c0c8a42cb458a495caf882612eed7b9f0e82e0d0312cfa3c05c2ee80e0a42c1958bed5a9676bdcf8741706818984a2c1f4780ac1a1ad763b05acc6603518813824398a067103d4cf780a5d52a250a580e2034898c21f55400ce240629d528b451a04a0a05c09f49031055f8096980874a51bb49a2d06ac2dbede5f2f57e8e008006a101c0d87434673351ca5038d4663a848c594c96fb7a0ce2622f97acb03b157e8e0300400a30b0e06c8e5200da4d04729006ce66239460361321bae16db6186bd828158abf003641adb6132186bd6e3818abf02801b40b4310926b95b04c24e503a61d0f7492b92caf0309044260fa211af944c0600a754a30d0250502df4905604e006732241580412089f0ff7f1a04a6310be920ab0599cc8905580c4669131a04a610fbe8cc0848a1884125bae028e503b3d960803b5408b43e1d05c94583e9da074b2601e107b810c28d34a24c421102200e1e34898c62130015de9d01961e4f37b23c9a084d134069b793cde8f547ba8124d2dba4bef37a3c8aa8f4f0249e512826d3c9d29178ba5c4794c165e01a75e44847bb80c582b115d64e7896492f02e1311e990617d32572411c8c8f2a81dd4e92c3bddc5c2623d34082726496024e23c8a062d95538574c9208e464797c12763a9fce67a160ac60ec3c9c4546f061e8ea7f381d850273901c885f27164925402910be4e2d92ca8052517c9c55229680a1b0c06566b159054ee76069fdcee60e03460b5179f8fa2a028a8ee303f9f05cb10321100835e2e87c3d21845c6e44382d088240aed74111e0ed0e08412010abc5d904803f43823b]
theorem sro17_0:zo (zr 9 st17) 9 227 srs17_0=true:=by decide +kernel
theorem scf17:zf (zr 9 st17) 286 275 (digits 9 2 51485) 0=true:=by decide +kernel
theorem shiftC2 {D:Dag} (h:z0 14 D) (hc:z3 14 (z4 neigh) D) (h0:(0:Fin 14)∈z1 14 D) (hc2:∀ w,(0:Fin 14)∈supp 14 D w→∀ c∈supp 14 D w,c.val=0∨c.val=4∨c.val=5) (ai:Nat):z0 14 (z7 (permOf ai) D)∧z3 14 (z4 neigh) (z7 (permOf ai) D)∧zu 14 (z7 (permOf ai) D)=zu 14 D∧qd 14 (z7 (permOf ai) D)=qd 14 D∧z1 14 (z7 (permOf ai) D)=(z1 14 D).image (permOf ai)∧(∀ v∈z6 14 (z7 (permOf ai) D),goodB v=true)∧(∀ (x:Fin 14),x.val=0→∀ w,x∈supp 14 (z7 (permOf ai) D) w→∀ c∈supp 14 (z7 (permOf ai) D) w,c.val=0∨c.val=4∨c.val=5):=by
  obtain ⟨h1,h2,_,h4,h5,h6⟩:=qu h hc (permOf ai) (autoOf ai)
  refine ⟨h1,h2,h4,h5,h6,?_,?_⟩
  · intro v hv;rw [wg (permOf ai) h.1,Finset.mem_image] at hv;obtain ⟨u,hu,rfl⟩:=hv
    have hu0:u≠0:=fun e=>by subst e;exact (qt.mp h0) hu
    have hne0:permOf ai u≠0:=fun e=>hu0 ((permOf ai).injective (e.trans (perm0 ai).symm))
    simp only [goodB,bne_iff_ne,ne_eq];exact fun e=>hne0 (Fin.ext e)
  · intro x hx0 w hxw c hcw;have hx:x=0:=Fin.ext hx0;subst hx
    have hsw:=y7 (permOf ai) h.1 (y3 (permOf ai)⁻¹ w);rw [tr_liftP_inv' (permOf ai) w] at hsw
    rw [hsw,Finset.mem_image] at hxw hcw;obtain ⟨u,hu,hu0⟩:=hxw;obtain ⟨v,hv,rfl⟩:=hcw
    have hueq:u=0:=(permOf ai).injective (hu0.trans (perm0 ai).symm);subst hueq
    exact perm45 ai v (hc2 _ hu v hv)
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem no_dag:¬∃ D:Dag,z0 14 D∧D.length≤24∧z3 14 (z4 neigh) D∧(0:Fin 14)∈z1 14 D∧(10:Fin 14)∈z6 14 D∧(∀ w,(0:Fin 14)∈supp 14 D w→∀ c∈supp 14 D w,c.val=0∨c.val=4∨c.val=5):=by
  rintro ⟨D,h,hlen,hc,h0,h10,hc2⟩
  have hsur:=xo h;have hsp:=x6 14 D;obtain ⟨m,enc⟩:=repr 14 (z1 14 D)
  have hok:poss 11 m.val=true:=poss_of h hc h0 h10 11 m.val enc (by omega)
  have hmem:m.val∈survCap:=by have:=allSurv m;simpa [survTest,hok] using this
  have hge10:10≤zu 14 D:=by by_contra hlt;have hp9:=poss_of h hc h0 h10 9 m.val enc (by omega);have:=List.all_eq_true.mp m2List _ hmem;simp [hp9] at this
  by_cases hbp10:zu 14 D=10
  · have hp10:=poss_of h hc h0 h10 10 m.val enc hbp10.le
    have hm1:=List.all_eq_true.mp m1List _ hmem;simp only [hp10,Bool.not_true,Bool.false_or,List.contains_iff_mem] at hm1
    obtain ⟨⟨mv,ai,rep⟩,htm,htb⟩:=List.any_eq_true.mp (List.all_eq_true.mp survM1Cov _ hm1)
    simp only [Bool.and_eq_true,beq_iff_eq,List.contains_iff_mem] at htb;rcases htb with ⟨hmveq,hrep⟩
    have hmv:(mask mv:Finset (Fin 14)).image (permOf ai)=mask rep:=zp _ _ _ (fun i=>by rw [permVal ai i];exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp mapM1Ok _ htm) i (List.mem_finRange i)))
    obtain ⟨h1,h2,h4,h5,h6,hEl',hc2'⟩:=shiftC2 h hc h0 hc2 ai
    have eq':(mask rep:Finset (Fin 14))=z1 14 (z7 (permOf ai) D):=by rw [h6,←enc,←hmveq,hmv]
    simp only [orbsM1,List.mem_cons,List.not_mem_nil,or_false] at hrep
    rcases hrep with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · have:=side_95 h1 h2 hEl' (by omega) eq';omega
    · have:=side_127 h1 h2 hEl' (by omega) eq';omega
    · obtain ⟨j1,j2,_,j4,_,j6⟩:=qu h1 h2 (permOf 4) (autoOf 4)
      have el:=zm 14 (z7 (permOf 4) (z7 (permOf ai) D))
      have hci:(z1 14 (z7 (permOf 4) (z7 (permOf ai) D))).card=4:=by rw [j6,Finset.card_image_of_injective _ (permOf 4).injective,←eq'];decide +kernel
      have hEl'':∀ x∈z6 14 (z7 (permOf 4) (z7 (permOf ai) D)),goodB x=true:=by intro x hx;rw [wg (permOf 4) h1.1,Finset.mem_image] at hx;obtain ⟨u,hu,rfl⟩:=hx;have hu0:u≠0:=fun e=>(by have:=hEl' u hu;simp [e,goodB] at this);have hne0:permOf 4 u≠0:=fun e=>hu0 ((permOf 4).injective (e.trans (perm0 4).symm));simp only [goodB,bne_iff_ne,ne_eq];exact fun e=>hne0 (Fin.ext e)
      exact noTwo_1 j1 j2 hEl'' (by omega) (by rw [j6,←eq'];exact Finset.mem_image.mpr ⟨(2:Fin 14),by decide,Fin.ext (by rw [permVal 4];decide)⟩)
    · have el:=zm 14 (z7 (permOf ai) D);have c:(mask 401:Finset (Fin 14)).card=4:=by decide +kernel
      rw [←eq'] at el;exact noTwo_4 h1 h2 hEl' (by omega) (eq' ▸ (by decide:(4:Fin 14)∈mask 401))
    · exact xj 10 gr h1 h2 adjE hEl' (by omega) (fun h=>by cases h) (by omega) eq' (by decide +kernel) (fun h=>absurd rfl h) (fun _=>hc2') (by decide) (by decide) sic0_0 sro0_0 scf0
    · exact xj 10 gr h1 h2 adjE hEl' (by omega) (fun h=>by cases h) (by omega) eq' (by decide +kernel) (fun h=>absurd rfl h) (fun _=>hc2') (by decide) (by decide) sic1_0 sro1_0 scf1
    · have:=side_15233 h1 h2 hEl' (by omega) eq';omega
  have hbp11:zu 14 D=11:=by omega
  have hbz0:qd 14 D=0:=by omega
  obtain ⟨⟨mv,ai,rep⟩,htm,htb⟩:=List.any_eq_true.mp (List.all_eq_true.mp survCapCov _ hmem)
  simp only [Bool.and_eq_true,beq_iff_eq,List.contains_iff_mem] at htb;rcases htb with ⟨hmveq,hrep⟩
  have hmv:(mask mv:Finset (Fin 14)).image (permOf ai)=mask rep:=zp _ _ _ (fun i=>by rw [permVal ai i];exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp mapCapOk _ htm) i (List.mem_finRange i)))
  obtain ⟨h1,h2,h4,h5,h6,hEl',hc2'⟩:=shiftC2 h hc h0 hc2 ai
  have eq':(mask rep:Finset (Fin 14))=z1 14 (z7 (permOf ai) D):=by rw [h6,←enc,←hmveq,hmv]
  simp only [orbsCap,List.mem_cons,List.not_mem_nil,or_false] at hrep
  rcases hrep with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · have el:=zm 14 (z7 (permOf ai) D);have c:(mask 11:Finset (Fin 14)).card=3:=by decide +kernel
    rw [←eq'] at el;exact noTwo_1 h1 h2 hEl' (by omega) (eq' ▸ (by decide:(1:Fin 14)∈mask 11))
  · exact xj 11 gr h1 h2 adjE hEl' (by omega) (fun _=>by omega) (by omega) eq' (by decide +kernel) (fun h=>absurd rfl h) (fun _=>hc2') (by decide) (by decide) sic2_0 sro2_0 scf2
  · have:=pv h1 h2 (by omega) hEl' 31 0 (by decide) rfl eq';omega
  · have:=pv h1 h2 (by omega) hEl' 63 1 (by decide) rfl eq';omega
  · exact cd0 h1 h2 (by omega) (by omega) hEl' 79 2 eq' [9,11,12] [(0,2693,2213,1,0,9,11,0,6),(0,6403,4371,6,0,11,12,0,3),(3,5009,0,2,3,12,9,8,0),(0,6403,2339,2,0,12,11,0,3)] (by decide +kernel) (by decide +kernel)
  · have:=side_95 h1 h2 hEl' (by omega) eq';omega
  · have:=side_127 h1 h2 hEl' (by omega) eq';omega
  · obtain ⟨j1,j2,_,j4,_,j6⟩:=qu h1 h2 (permOf 4) (autoOf 4)
    have el:=zm 14 (z7 (permOf 4) (z7 (permOf ai) D))
    have hci:(z1 14 (z7 (permOf 4) (z7 (permOf ai) D))).card=3:=by rw [j6,Finset.card_image_of_injective _ (permOf 4).injective,←eq'];decide +kernel
    have hEl'':∀ x∈z6 14 (z7 (permOf 4) (z7 (permOf ai) D)),goodB x=true:=by intro x hx;rw [wg (permOf 4) h1.1,Finset.mem_image] at hx;obtain ⟨u,hu,rfl⟩:=hx;have hu0:u≠0:=fun e=>(by have:=hEl' u hu;simp [e,goodB] at this);have hne0:permOf 4 u≠0:=fun e=>hu0 ((permOf 4).injective (e.trans (perm0 4).symm));simp only [goodB,bne_iff_ne,ne_eq];exact fun e=>hne0 (Fin.ext e)
    exact noTwo_1 j1 j2 hEl'' (by omega) (by rw [j6,←eq'];exact Finset.mem_image.mpr ⟨(2:Fin 14),by decide,Fin.ext (by rw [permVal 4];decide)⟩)
  · have el:=zm 14 (z7 (permOf ai) D);have c:(mask 145:Finset (Fin 14)).card=3:=by decide +kernel
    rw [←eq'] at el;exact noTwo_4 h1 h2 hEl' (by omega) (eq' ▸ (by decide:(4:Fin 14)∈mask 145))
  · exact xj 11 gr h1 h2 adjE hEl' (by omega) (fun _=>by omega) (by omega) eq' (by decide +kernel) (fun h=>absurd rfl h) (fun _=>hc2') (by decide) (by decide) sic3_0 sro3_0 scf3
  · exact xj 11 gr h1 h2 adjE hEl' (by omega) (fun _=>by omega) (by omega) eq' (by decide +kernel) (fun h=>absurd rfl h) (fun _=>hc2') (by decide) (by decide) sic4_0 sro4_0 scf4
  · have:=pv h1 h2 (by omega) hEl' 181 2 (by decide) rfl eq';omega
  · exact xj 11 gr h1 h2 adjE hEl' (by omega) (fun _=>by omega) (by omega) eq' (by decide +kernel) (fun h=>absurd rfl h) (fun _=>hc2') (by decide) (by decide) sic5_0 sro5_0 scf5
  · exact z5v 11 gr h1 h2 adjE hEl' (by omega) (fun _=>by omega) (by omega) eq' (by decide +kernel) (fun h=>absurd rfl h) (fun _=>hc2') (by decide) (by decide) (by decide) sic14_0 sic14_1 sro14_0 scf14
  · exact cd0 h1 h2 (by omega) (by omega) hEl' 245 3 eq' [9,10,11,12] [(0,3716,3078,5,0,9,11,0,6),(0,5009,4371,6,0,9,12,0,5),(0,3716,2693,4,0,10,9,0,5),(0,7426,6403,4,0,10,12,0,5),(0,3716,1548,6,0,11,10,0,4),(3,6403,0,6,4,11,12,8,0),(0,5009,793,2,0,12,9,0,5),(0,7426,1290,2,0,12,10,0,5),(3,6403,0,2,5,12,11,8,0)] (by decide +kernel) (by decide +kernel)
  · have el:=zm 14 (z7 (permOf ai) D);have c:(mask 385:Finset (Fin 14)).card=3:=by decide +kernel
    rw [←eq'] at el;exact noTwo_7 h1 h2 hEl' (by omega) (eq' ▸ (by decide:(7:Fin 14)∈mask 385))
  · exact xj 11 gr h1 h2 adjE hEl' (by omega) (fun _=>by omega) (by omega) eq' (by decide +kernel) (fun h=>absurd rfl h) (fun _=>hc2') (by decide) (by decide) sic6_0 sro6_0 scf6
  · exact runS32 11 gr h1 h2 adjE hEl' (by omega) (fun _=>by omega) (by omega) eq' (by decide +kernel) (fun h=>absurd rfl h) (fun _=>hc2') (by decide) (by decide) (by decide) (by decide) (by decide) sic15_0 sic15_1 sic15_2 sro15_0 sro15_1 scf15
  · have el:=zm 14 (z7 (permOf ai) D);have c:(mask 517:Finset (Fin 14)).card=3:=by decide +kernel
    rw [←eq'] at el;exact noTwo_9 h1 h2 hEl' (by omega) (eq' ▸ (by decide:(9:Fin 14)∈mask 517))
  · exact xj 11 gr h1 h2 adjE hEl' (by omega) (fun _=>by omega) (by omega) eq' (by decide +kernel) (fun h=>absurd rfl h) (fun _=>hc2') (by decide) (by decide) sic7_0 sro7_0 scf7
  · have el:=zm 14 (z7 (permOf ai) D);have c:(mask 529:Finset (Fin 14)).card=3:=by decide +kernel
    rw [←eq'] at el;exact noTwo_9 h1 h2 hEl' (by omega) (eq' ▸ (by decide:(9:Fin 14)∈mask 529))
  · exact xj 11 gr h1 h2 adjE hEl' (by omega) (fun _=>by omega) (by omega) eq' (by decide +kernel) (fun h=>absurd rfl h) (fun _=>hc2') (by decide) (by decide) sic8_0 sro8_0 scf8
  · have:=pv h1 h2 (by omega) hEl' 541 3 (by decide) rfl eq';omega
  · exact xj 11 gr h1 h2 adjE hEl' (by omega) (fun _=>by omega) (by omega) eq' (by decide +kernel) (fun h=>absurd rfl h) (fun _=>hc2') (by decide) (by decide) sic9_0 sro9_0 scf9
  · exact xj 11 gr h1 h2 adjE hEl' (by omega) (fun _=>by omega) (by omega) eq' (by decide +kernel) (fun h=>absurd rfl h) (fun _=>hc2') (by decide) (by decide) sic10_0 sro10_0 scf10
  · exact z5v 11 gr h1 h2 adjE hEl' (by omega) (fun _=>by omega) (by omega) eq' (by decide +kernel) (fun h=>absurd rfl h) (fun _=>hc2') (by decide) (by decide) (by decide) sic16_0 sic16_1 sro16_0 scf16
  · exact xj 11 gr h1 h2 adjE hEl' (by omega) (fun _=>by omega) (by omega) eq' (by decide +kernel) (fun h=>absurd rfl h) (fun _=>hc2') (by decide) (by decide) sic17_0 sro17_0 scf17
  · exact xj 11 gr h1 h2 adjE hEl' (by omega) (fun _=>by omega) (by omega) eq' (by decide +kernel) (fun h=>absurd rfl h) (fun _=>hc2') (by decide) (by decide) sic11_0 sro11_0 scf11
  · have:=pv h1 h2 (by omega) hEl' 2693 4 (by decide) rfl eq';omega
  · exact xj 11 gr h1 h2 adjE hEl' (by omega) (fun _=>by omega) (by omega) eq' (by decide +kernel) (fun h=>absurd rfl h) (fun _=>hc2') (by decide) (by decide) sic12_0 sro12_0 scf12
  · have:=pv h1 h2 (by omega) hEl' 2945 5 (by decide) rfl eq';omega
  · exact xj 11 gr h1 h2 adjE hEl' (by omega) (fun _=>by omega) (by omega) eq' (by decide +kernel) (fun h=>absurd rfl h) (fun _=>hc2') (by decide) (by decide) sic13_0 sro13_0 scf13
  · have:=pv h1 h2 (by omega) hEl' 4753 6 (by decide) rfl eq';omega
  · exact cd0 h1 h2 (by omega) (by omega) hEl' 5009 3 eq' [1,2,3,5] [(0,127,8297,9,0,1,3,0,7),(0,127,8297,7,0,1,5,0,9),(3,127,0,8,12,2,1,6,0),(0,127,8297,8,0,2,5,0,12),(0,127,2087,7,0,3,2,0,12),(0,127,2087,7,0,3,5,0,12),(0,127,1102,12,0,5,1,0,9),(0,127,1102,9,0,5,2,0,12),(0,127,1102,9,0,5,3,0,12)] (by decide +kernel) (by decide +kernel)
  · have:=pv h1 h2 (by omega) hEl' 7041 7 (by decide) rfl eq';omega
  · have:=pv h1 h2 (by omega) hEl' 14977 8 (by decide) rfl eq';omega
  · have:=pv h1 h2 (by omega) hEl' 15233 9 (by decide) rfl eq';omega
end G_C2
section FinalBridge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity DagTools Compact GraphTools Reduction
def edges14:List (ℕ×ℕ):=[(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
def hit14 (x:Fin 14→Bool):=∃ u v:Fin 14,(u.val,v.val)∈edges14∧x u=true∧x v=true
theorem graph_edges14:∀ u v:Fin 14,v5 u v↔(u.val,v.val)∈edges14∨(v.val,u.val)∈edges14:=by decide +kernel
theorem agrees14 (x:Fin 14→Bool):hit14 x↔qi v5 x:=by
  constructor
  · rintro ⟨u,v,e,hu,hv⟩;exact ⟨u,v,(graph_edges14 u v).2 (Or.inl e),hu,hv⟩
  · rintro ⟨u,v,a,hu,hv⟩;rcases (graph_edges14 u v).1 a with e|e
    · exact ⟨u,v,e,hu,hv⟩
    · exact ⟨v,u,e,hv,hu⟩
theorem normalized14 (C:Circuit) (hm:Monotone2 C) (hc:∀ x:Fin 14→Bool,C.eval (List.ofFn x)=true↔hit14 x):
    ∃ D:Dag,z0 14 D∧D.length≤C.size∧z3 14 v5 D:=by
  obtain ⟨D,hd,le,ev⟩:=z1u (n:=14) C hm (by
    intro b;cases b
    · refine ⟨fun _=>true,?_⟩;rw [Ne,Bool.not_eq_false];exact (hc _).2 ⟨0,10,by decide,rfl,rfl⟩
    · exact ⟨fun _=>false,fun h=>by rcases (hc _).1 h with ⟨_,_,_,h1,_⟩;contradiction⟩) (by
    intro i;exact ⟨single i,fun h=>qr z6a i ((agrees14 _).1 ((hc _).1 (by rw [h];simp [single])))⟩) (by
    intro i;obtain ⟨j,ij⟩:=z6a.2.2.2 i
    refine ⟨single j,qv i j,fun k hki=>by simp [qv,single,hki],fun h=>qr z6a j ((agrees14 _).1 ((hc _).1 (h.trans ((hc _).2 ((agrees14 _).2 (wq ij))))))⟩)
  exact ⟨D,hd,le,fun x=>by rw [ev,hc];exact agrees14 x⟩
theorem no_dag14:¬∃ D:Dag,z0 14 D∧D.length≤24∧z3 14 v5 D:=z5x G_Gp.no_dag G_Gpp.no_dag G_C1.no_dag G_C2.no_dag
end FinalBridge
end PEqualNP.Outside.L_meta_9772_aux

theorem PEqualNP.Outside.L_meta_9772 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 24 ∧ (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) := by
  rintro ⟨C,mono,len,comp⟩
  obtain ⟨D,h,short,hc⟩:=PEqualNP.Outside.L_meta_9772_aux.normalized14 C mono comp
  exact PEqualNP.Outside.L_meta_9772_aux.no_dag14 ⟨D,h,short.trans len,hc⟩
