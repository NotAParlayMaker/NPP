import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_3539_aux
abbrev I := Fin 14
abbrev X := I → Bool
def edgeRows : List Nat := [1408,8832,12544,6272,11264,5632,2816]

def inputRows : List Nat := [95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752]

def F (x : X) := decide (∃ i j : I, (edgeRows.getD i.val 0).testBit j.val=true ∧ x i=true ∧ x j=true)

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  rw [List.getD_eq_getElem _ _ (by simp;omega),List.getD_eq_getElem _ _ h,List.getElem_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  rw [List.getD_eq_getElem _ _ (by simp),List.getElem_append_right (by omega)]
  simp

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hw),List.getD_eq_getElem _ _ (by simpa using hw),List.getElem_ofFn,List.getElem_ofFn]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

/- A wire true at `x` is true at every input above `x`. -/
theorem up (gates : List Gate) (g : ℕ)
    (hleg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    {N : ℕ} (x y : Fin N → Bool) (hxy : ∀ v, x v = true → y v = true)
    (h : Circuit.eval ⟨gates, g⟩ (List.ofFn x) = true) :
    Circuit.eval ⟨gates, g⟩ (List.ofFn y) = true := by
  rw [eval_eq] at h ⊢
  exact mono2 gates hleg _ _ (by simp) (ofFn_mono N x y hxy) g h

/- For each of the 128 assignments to the left side, this table selects a dominating
   maximal independent set from the 37 negative samples. -/
def negIndex : Array Nat := #[36,35,24,23,16,14,15,11,30,28,9,0,10,4,7,0,21,20,19,17,5,4,0,0,6,4,2,0,4,4,0,0,32,31,13,11,12,11,11,11,27,25,2,0,0,0,0,0,3,0,2,0,1,0,0,0,2,0,2,0,0,0,0,0,34,33,22,17,8,0,7,0,29,25,7,0,7,0,7,0,18,17,17,17,1,0,0,0,0,0,0,0,0,0,0,0,26,25,0,0,1,0,0,0,25,25,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0]
def sample (r : Nat) (i : I) := (inputRows.getD i.val 0).testBit r
def leftMap (x : X) : Fin 7 → Bool := fun i => x ⟨i.val,by omega⟩
def leftCode (x : X) : Fin 128 :=
  ⟨(BitVec.ofBoolListLE (List.ofFn (leftMap x))).toNat,by
    have h := (BitVec.ofBoolListLE (List.ofFn (leftMap x))).isLt; simpa using h⟩
lemma left_bit (x : X) (u : Fin 7) : (leftCode x).val.testBit u.val=x ⟨u.val,by omega⟩ := by
  change (BitVec.ofBoolListLE (List.ofFn (leftMap x))).getLsbD u.val=_
  rw [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem _ _ (by simp),List.getElem_ofFn]
  rfl
def side (l : Fin 128) (i : I) := if i.val<7 then l.val.testBit i.val else
  decide (∀ a : Fin 7, l.val.testBit a.val=true → (edgeRows.getD a.val 0).testBit i.val=false)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem negativeRows : ∀ l : Fin 128,
    (negIndex.getD (l.val) 0)<37 ∧ ∀ i : I, side l i=true →
      sample (21+(negIndex.getD (l.val) 0)) i=true := by decide +kernel
set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem positiveRows : ∀ i j : I, (edgeRows.getD i.val 0).testBit j.val=true →
    ∃ r : Fin 21, ∀ u : I, sample r.val u=true → u=i ∨ u=j := by decide +kernel
lemma dom (x : X) (hF : F x=false) (u : I) (h : x u=true) : side (leftCode x) u=true := by
  by_cases hu : u.val<7
  · simpa [side,hu,left_bit x ⟨u.val,hu⟩] using h
  · simp only [side,hu,ite_false,decide_eq_true_eq]
    intro a ha
    cases he : (edgeRows.getD a.val 0).testBit u.val with
    | false => rfl
    | true =>
      have hx : x ⟨a.val,by omega⟩=true := (left_bit x a).symm.trans ha
      exact False.elim (Bool.noConfusion ((show F x=true by exact decide_eq_true ⟨⟨a.val,by omega⟩,u,he,hx,h⟩).symm.trans hF))
/- Every true assignment contains an edge, and every false assignment is dominated by
   a negative sample. Monotonicity therefore extends the 58 sample values to all inputs. -/
lemma complete (H : X → Bool) (hmono : ∀ x y : X, (∀ i, x i=true →y i=true) → H x=true →H y=true)
    (hr : ∀ r<58, H (sample r)=decide (r<21)) : ∀ x : X, H x=F x := by
  intro x
  cases e : F x with
  | true =>
    obtain ⟨a,b,hab,ha,hb⟩ := of_decide_eq_true e
    obtain ⟨r,hh⟩ := positiveRows a b hab
    apply hmono (sample r.val) x (fun i hi => ?_) (by simpa [r.isLt] using hr r.val (by have:=r.isLt;omega))
    rcases hh i hi with h|h <;> subst i <;> assumption
  | false =>
    obtain ⟨hn,hd⟩ := negativeRows (leftCode x)
    let r := 21+(negIndex.getD ((leftCode x).val) 0)
    have h0 : H (sample r)=false := by simpa [r] using hr r (by dsimp [r]; omega)
    by_contra! hx
    have hy := hmono x (sample r) (fun i hi => hd i (dom x e i hi)) (by simpa using hx)
    simp [h0] at hy
def gate (t : Nat) : Gate := ⟨if t<4096 then .and else .or,[t % 64,(t/64) % 64]⟩
def step (w : List Nat) (t : Nat) := w++[if t<4096 then w.getD (t % 64) 0 &&& w.getD ((t/64) % 64) 0
  else w.getD (t % 64) 0 ||| w.getD ((t/64) % 64) 0]
def machine (p : List Nat) : Circuit := ⟨p.map gate,13+p.length⟩
lemma legitimate (p : List Nat) : Monotone2 (machine p) := by
  intro g hg
  obtain ⟨t,_,rfl⟩ := List.mem_map.mp hg
  by_cases h : t<4096 <;> simp [gate,h]
lemma read_bits (w : List Nat) (i r : Nat) :
    (w.map (fun n => n.testBit r)).getD i false=(w.getD i 0).testBit r := by
  simpa using (List.getD_map w (0:Nat) (n:=i) (fun n => n.testBit r))
/- Each bit position evaluates one assignment through the entire circuit. -/
lemma circuit_bits (p : List Nat) (w : List Nat) (r : Nat) :
    (p.foldl step w).map (fun n => n.testBit r)=wf (p.map gate) (w.map (fun n => n.testBit r)) := by
  induction p generalizing w with
  | nil => rfl
  | cons t p ih =>
    change (p.foldl step (step w t)).map _=wf (p.map gate) (_ ++ [_])
    rw [ih]
    congr 1
    by_cases h : t<4096 <;> simp only [step,gate,h,ite_true,ite_false,List.map_append,List.map_cons,List.map_nil,Nat.testBit_and,Nat.testBit_or,GateOp.eval,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,read_bits,Bool.and_true,Bool.or_false]
lemma init_samples (r : Nat) : inputRows.map (fun n => n.testBit r)=List.ofFn (sample r) := by
  apply List.ext_getElem
  · simp [inputRows]
  · intro i hi hi'
    have h : i < inputRows.length := by simpa using hi
    simp only [sample,List.getElem_map,List.getElem_ofFn,List.getD_eq_getElem _ _ h]
theorem sample_target : ∀ r : Fin 58, (2097151 : Nat).testBit r.val=decide (r.val<21) := by decide +kernel
theorem decoded (p : List Nat) (h : (p.foldl step inputRows).getD (13+p.length) 0=2097151) :
    ∀ x : X, (machine p).eval (List.ofFn x)=F x := by
  apply complete
  · intro x y xy
    apply up _ _ _ x y xy
    exact fun g hg => by simpa using legitimate p g hg
  · intro r hr
    have e := congrArg (fun n : Nat => n.testBit r) h
    rw [←read_bits,circuit_bits,init_samples,sample_target ⟨r,hr⟩] at e
    exact e
end PEqualNP.Outside.L_meta_3539_aux

open PEqualNP.Outside.L_meta_3539_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem PEqualNP.Outside.L_meta_3539 :
  let w := ([95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752] : List ℕ)
  let step := fun (w : List ℕ) (t : ℕ) => w++[if t<4096 then w.getD (t % 64) 0 &&& w.getD ((t/64) % 64) 0 else w.getD (t % 64) 0 ||| w.getD ((t/64) % 64) 0]
  let gate := fun t : ℕ => (⟨if t<4096 then GateOp.and else GateOp.or,[t % 64,(t/64) % 64]⟩ : Gate)
  let F := fun x : Fin 14 → Bool => decide (∃ a b : Fin 14, (([1408,8832,12544,6272,11264,5632,2816] : List ℕ).getD a.val 0).testBit b.val=true ∧ x a=true ∧ x b=true)
  ∀ P : List ℕ, (P.foldl step w).getD (13+P.length) 0=2097151 →
    ∀ x : Fin 14 → Bool, (Circuit.mk (P.map gate) (13+P.length)).eval (List.ofFn x)=F x := by
  dsimp only
  exact decoded
